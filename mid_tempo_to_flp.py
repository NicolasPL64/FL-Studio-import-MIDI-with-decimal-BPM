#!/usr/bin/env python3
"""
mid_tempo_to_flp.py

Add fractional-BPM tempo automation to an FL Studio project (.flp) by reading a
MIDI file's tempo map and generating a master-tempo automation clip.

Why this exists: FL Studio rounds fractional BPM to the nearest integer when
importing a MIDI file with tempo changes. This script restores the exact
fractional tempo map as a "Hold"-mode tempo automation clip, byte-exact against
the format FL Studio 26.1.7 produces.

Usage:
    python mid_tempo_to_flp.py --mid song.mid --flp project.flp [--out out.flp]

The output .flp is written next to the input (suffixed with the MIDI stem) by
default; the original is left untouched.
"""

import argparse
import os
import shutil
import struct
import sys

# ---------------------------------------------------------------------------
# FLP event encoding constants
# ---------------------------------------------------------------------------
BYTE = 0
WORD = 64
DWORD = 128
TEXT = 192

MIN_BPM = 10.0
MAX_BPM = 522.0

# Event IDs
EV_NEW = 64
EV_TYPE = 21
EV_AUTOMATION = 234
EV_ARRANGEMENT_NEW = 99
EV_PLAYLIST = 233
EV_INIT_CONTROL = 227

# FL 26 playlist record size (60-byte base + 28-byte FL21+ extension).
# Only 233 payloads whose length is a multiple of this are real playlists;
# FL also emits short 233 blobs inside note/controller data which must
# never be touched (patching them corrupts the file).
PLAYLIST_RECORD_SIZE = 88

# ---------------------------------------------------------------------------
# Byte templates extracted from an FL Studio 26.1.7 generated reference.
# ---------------------------------------------------------------------------

# "Name" event payload = UTF-16LE "Tempo\0"
TEMPO_NAME_UTF16 = "540065006d0070006f000000"

# Automation channel event template. `None` payloads are filled at runtime
# (IID and the automation point data). Everything else is copied verbatim.
AUTOMATION_CHANNEL_TEMPLATE = [
    (EV_NEW, None),  # channel IID (u16) -> filled
    (EV_TYPE, "05"),  # 5 = automation
    (201, "0000"),  # internal name (empty)
    (212, "0000000000000000ffffffff00000000510000000500000000000000000000000000000053030000800000000000000000000000"),
    (203, TEMPO_NAME_UTF16),  # channel name "Tempo"
    (155, "00000000"),
    (128, "8e736000"),
    (41, "01"),
    (0, "01"),
    (209, "0000000000190000000000000400000090000000"),
    (138, "80008000"),
    (139, "00000100"),
    (89, "0000"),
    (97, "8000"),
    (48, "00"),
    (69, "8000"),
    (86, "0001"),
    (71, "0004"),
    (83, "0000"),
    (74, "0000"),
    (75, "0000"),
    (76, "0000"),
    (85, "0008"),
    (131, "00008000"),
    (70, "0000"),
    (104, "0000"),
    (50, "01"),
    (219, "000000000032000000000000000100000000000000000000"),  # Levels: Min=0, Max=12800
    (229, "0000000000320000000000000000000000000000"),
    (221, "01000000f401000000"),
    (215, "ffffffff0000000001000000ffffffff3c0000000000803f0000803f0000803f0000803f0000803f0000000001000000ffffffff000400003000000000000100a7050000000000000001000000000000000000000000000000000000010000000000000000000000000000000000000002000000feffffffffffffff000000000000000000000000000000000000f03f0000000000000000ffffffff01010000000000000000e03f"),
    (132, "00000000"),
    (144, "00000000"),
    (145, "00000000"),
    (EV_AUTOMATION, None),  # points -> filled
    (32, "00"),
    (228, "64000000000000000000000000000000"),
    (228, "3c000000000000000000000000000000"),
    (218, "000000000000000064000000204e0000204e00003075000032000000204e00000000000064000000204e000000000000b680000000000000000000000000000000000000"),
    (218, "040000000000000064000000204e0000204e00003075000032000000204e00000000000064000000204e000000000000b68000000000000000000000000000009bffffff"),
    (218, "000000000000000064000000204e0000204e00003075000032000000204e00000000000064000000204e000000000000b680000000000000000000000000000000000000"),
    (218, "000000000000000064000000204e0000204e00003075000032000000204e00000000000064000000204e000000000000b680000000000000000000000000000000000000"),
    (218, "000000000000000064000000204e0000204e00003075000032000000204e00000000000064000000204e000000000000b680000000000000000000000000000000000000"),
    (143, "03000000"),
    (20, "00"),
    (170, "ffffffff"),
    (51, "00"),
]

# Fixed 115-byte tail of the Automation (234) event (clip settings / LFO).
AUTOMATION_TAIL = (
    "01000000ffffffffffffffffffffffffffffffff80000000800000000000000080000000"
    "0500000003000000010000000000000000000000000000000000000000f03f00000000"
    "000000000100000000000000fffffffffffffffffffffffffbb200000000000000000000"
    "0000000000000000"
)

# Initialised-control event (227): links the master tempo to the automation
# channel. Byte index 2 carries the automation channel IID.
INIT_CONTROL_PREFIX = "0000"
INIT_CONTROL_SUFFIX = "00000000000500004008000000d5010000"


# ---------------------------------------------------------------------------
# MIDI parsing (raw, tolerates sysex that breaks `mido`)
# ---------------------------------------------------------------------------
def _read_midi_varint(data, i):
    value = 0
    while True:
        b = data[i]
        i += 1
        value = (value << 7) | (b & 0x7F)
        if not (b & 0x80):
            return value, i


def read_midi_tempo_map(path):
    """Return (ticks_per_beat, [(tick, bpm), ...]) from a MIDI file."""
    data = open(path, "rb").read()
    if data[:4] != b"MThd":
        raise ValueError(f"{path}: not a MIDI file")

    i = 4
    header_len = struct.unpack_from(">I", data, i)[0]
    i += 4
    fmt = struct.unpack_from(">H", data, i)[0]
    i += 2
    ntrks = struct.unpack_from(">H", data, i)[0]
    i += 2
    division = struct.unpack_from(">H", data, i)[0]
    i += 2

    if division & 0x8000:
        raise ValueError("SMPTE time division not supported")

    tempos = []
    for _ in range(ntrks):
        if data[i : i + 4] != b"MTrk":
            break
        i += 4
        tlen = struct.unpack_from(">I", data, i)[0]
        i += 4
        end = i + tlen
        tick = 0
        running = 0
        while i < end:
            dt, i = _read_midi_varint(data, i)
            tick += dt
            b = data[i]
            if b & 0x80:
                status = data[i]
                i += 1
                running = status
            else:
                status = running
                i += 1

            if status == 0xFF:
                mtype = data[i]
                i += 1
                ln, i = _read_midi_varint(data, i)
                payload = data[i : i + ln]
                i += ln
                if mtype == 0x51 and ln == 3:
                    us = (payload[0] << 16) | (payload[1] << 8) | payload[2]
                    tempos.append((tick, 60000000.0 / us))
            elif status in (0xF0, 0xF7):
                ln, i = _read_midi_varint(data, i)
                i += ln
            elif status & 0xF0 in (0xC0, 0xD0):
                i += 1
            elif status & 0xF0 in (0x80, 0x90, 0xA0, 0xB0, 0xE0):
                i += 2
            else:
                # running status byte already consumed; nothing more to skip
                pass

    if not tempos:
        tempos = [(0, 120.0)]

    # Ensure a first point at tick 0 (MIDI default tempo if none at 0).
    if tempos[0][0] != 0:
        tempos.insert(0, (0, 120.0))

    return division, tempos


# ---------------------------------------------------------------------------
# FLP parsing / encoding
# ---------------------------------------------------------------------------
def parse_flp(data):
    """Parse an FLP into (header_dict, [(event_id, payload_bytes), ...], spans).

    spans[i] = (start, end) byte offsets of the complete original encoding of
    events[i] (id + length prefix + payload), used for byte-exact passthrough
    of untouched events.
    """
    if data[:4] != b"FLhd":
        raise ValueError("not an FLP file (missing 'FLhd' magic)")
    fmt = struct.unpack_from("<h", data, 8)[0]
    num_channels = struct.unpack_from("<H", data, 10)[0]
    ppq = struct.unpack_from("<H", data, 12)[0]
    if data[14:18] != b"FLdt":
        raise ValueError("missing 'FLdt' data chunk")

    events = []
    spans = []
    i = 22
    n = len(data)
    while i < n:
        start = i
        eid = data[i]
        i += 1
        if eid < 64:
            size = 1
        elif eid < 128:
            size = 2
        elif eid < 192:
            size = 4
        else:
            size, i = _read_flp_varint(data, i)
        payload = data[i : i + size]
        i += size
        events.append((eid, payload))
        spans.append((start, i))

    return {"format": fmt, "num_channels": num_channels, "ppq": ppq}, events, spans


def _read_flp_varint(data, i):
    result = 0
    shift = 0
    while True:
        b = data[i]
        i += 1
        result |= (b & 0x7F) << shift
        if not (b & 0x80):
            return result, i
        shift += 7


def encode_event(eid, payload):
    if eid < 64:
        return bytes([eid]) + payload
    if eid < 128:
        return bytes([eid]) + payload
    if eid < 192:
        return bytes([eid]) + payload
    # length-prefixed (varint) DATA event
    n = len(payload)
    length = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            length.append(b | 0x80)
        else:
            length.append(b)
            break
    return bytes([eid]) + bytes(length) + payload


# ---------------------------------------------------------------------------
# Automation generation
# ---------------------------------------------------------------------------
def _bpm_to_value(bpm):
    v = (bpm - MIN_BPM) / (MAX_BPM - MIN_BPM)
    if v < 0.0:
        v = 0.0
    if v > 1.0:
        v = 1.0
    return v


def build_automation_event(points):
    """Build the Automation (234) event payload.

    points: list of (position_ppq: float, bpm: float), positions absolute and
    sorted ascending.
    """
    header = struct.pack("<I", 1)  # _u1
    header += struct.pack("<i", 64)  # lfo.amount
    header += b"\x00"  # _u2
    header += b"\x04\x00"  # _u3
    header += b"\x00\x00"  # _u4
    header += struct.pack("<I", 3)  # _u5

    body = header + struct.pack("<I", len(points))
    prev = 0.0
    for idx, (pos, bpm) in enumerate(points):
        offset = pos - prev
        prev = pos
        body += struct.pack("<d", offset)
        body += struct.pack("<d", _bpm_to_value(bpm))
        body += struct.pack("<f", 0.0)  # tension
        if idx == 0:
            body += b"\x00\x00\x00\x00"  # first point: no curve
        else:
            body += b"\x02\x00\x00\x00"  # Hold mode
    body += bytes.fromhex(AUTOMATION_TAIL)
    return body


def build_init_control(iid):
    """Build the initialised-control (227) event payload."""
    return bytes.fromhex(INIT_CONTROL_PREFIX) + bytes([iid]) + bytes.fromhex(INIT_CONTROL_SUFFIX)


def build_playlist_item(iid, length_ppq, clip_id, track_rvidx=498):
    item = struct.pack("<I", 0)  # position
    item += struct.pack("<H", 20480)  # pattern_base
    item += struct.pack("<H", iid)  # item_index -> automation channel IID
    item += struct.pack("<I", length_ppq)  # length
    item += struct.pack("<h", track_rvidx)  # track (reversed index)
    item += struct.pack("<H", 0)  # group
    item += struct.pack("<H", 120)  # _u1
    item += struct.pack("<H", 0x40)  # item_flags
    item += b"\x40\x64\x80\x80"  # _u2
    item += struct.pack("<f", -1.0)  # start offset (full)
    item += struct.pack("<f", -1.0)  # end offset (full)
    item += struct.pack("<I", clip_id)
    item += b"\x00" * 28  # reserved
    item += struct.pack("<d", 1.0)  # scale
    item += b"\x00\x00\x00\x00"
    item += b"\xff\xff\xff\xff"
    item += b"\x00\x00\x00\x00"
    item += b"\x00\x00\x00\x00"
    return item


def _decode_playlist_items(payload, record_size=88):
    items = []
    for i in range(0, len(payload), record_size):
        rec = payload[i : i + record_size]
        items.append(rec)
    return items


def _playlist_item_index(record):
    return struct.unpack_from("<H", record, 6)[0]


def _playlist_item_clip_id(record):
    return struct.unpack_from("<I", record, 32)[0]


def _playlist_item_length(record):
    return struct.unpack_from("<I", record, 8)[0]


def verify_output(data, events, spans, first_channel_idx,
                  playlist_idx, item, out):
    """Re-parse the serialized output and assert only intended changes exist.

    Raises ValueError on any unexpected difference. Returns a summary dict.
    """
    header, new_events, _ = parse_flp(out)
    n_new_channel_events = len(AUTOMATION_CHANNEL_TEMPLATE)

    # 1. event count: +channel block, +1 init control
    if len(new_events) != len(events) + n_new_channel_events + 1:
        raise ValueError(
            f"verify: event count {len(new_events)} != {len(events)} + "
            f"{n_new_channel_events + 1}"
        )

    # 2. exact event-id sequence with insertions at the expected spots
    # (init control, then channel block, both before the first channel)
    old_ids = [e[0] for e in events]
    new_ids = [e[0] for e in new_events]
    template_ids = [eid for eid, _ in AUTOMATION_CHANNEL_TEMPLATE]
    expected_ids = (
        old_ids[:first_channel_idx]
        + [EV_INIT_CONTROL]
        + template_ids
        + old_ids[first_channel_idx:]
    )
    if new_ids != expected_ids:
        raise ValueError("verify: event id sequence differs from expected splice")

    def new_index(i):
        return i + n_new_channel_events + 1 if i >= first_channel_idx else i

    # 3. every pre-existing event byte-identical except the patched playlist
    for i in range(len(events)):
        if i == playlist_idx:
            continue
        if new_events[new_index(i)] != events[i]:
            raise ValueError(f"verify: pre-existing event {i} changed unexpectedly")

    # 4. patched playlist = old payload + appended item
    if new_events[new_index(playlist_idx)][1] != events[playlist_idx][1] + item:
        raise ValueError("verify: playlist patch mismatch")

    # 5. non-playlist 233 blobs (short payloads in note/controller data) must
    # be byte-identical; the patched target stays record-aligned by
    # construction (aligned old payload + one 88-byte record)
    old_short = [pl for eid, pl in events
                 if eid == EV_PLAYLIST and len(pl) % PLAYLIST_RECORD_SIZE != 0]
    new_short = [pl for eid, pl in new_events
                 if eid == EV_PLAYLIST and len(pl) % PLAYLIST_RECORD_SIZE != 0]
    if old_short != new_short:
        raise ValueError("verify: short 233 blob changed unexpectedly")

    # 6. channel IIDs unique across (New, Type) pairs
    iids = [
        struct.unpack("<H", pl)[0]
        for (eid, pl), nxt in zip(new_events, new_events[1:] + [(None, b"")])
        if eid == EV_NEW and nxt[0] == EV_TYPE
    ]
    if len(iids) != len(set(iids)):
        raise ValueError(f"verify: duplicate channel IIDs {iids}")

    # 7. header consistency
    if struct.unpack_from("<H", out, 10)[0] != len(iids):
        raise ValueError("verify: header channel count mismatch")
    if struct.unpack_from("<I", out, 18)[0] != len(out) - 22:
        raise ValueError("verify: header FLdt size mismatch")

    return {
        "records_in_playlist": len(new_events[new_index(playlist_idx)][1])
        // PLAYLIST_RECORD_SIZE,
        "channel_iids": iids,
    }


# ---------------------------------------------------------------------------
# Main logic
# ---------------------------------------------------------------------------
def add_tempo_automation(flp_path, mid_path, out_path):
    with open(flp_path, "rb") as f:
        data = f.read()

    header, events, spans = parse_flp(data)
    ppq = header["ppq"]
    division, tempos = read_midi_tempo_map(mid_path)

    # Automation channel IID = current channel count (0-indexed next slot).
    auto_iid = header["num_channels"]

    # Convert MIDI ticks -> beats (automation point X is in beats, not PPQ).
    points = [(tick / float(division), bpm) for tick, bpm in tempos]

    # --- Locate insertion points -------------------------------------------
    # Everything new goes right before the channel rack: x.flp itself keeps
    # its controller events (226) immediately before the first channel, so
    # the 227 init and the automation channel block join that cluster.
    # (Inserting the block earlier, before the first e99, corrupts the file.)
    first_channel_idx = None

    for idx in range(len(events) - 1):
        eid = events[idx][0]
        nxt = events[idx + 1][0]
        if first_channel_idx is None and eid == EV_NEW and nxt == EV_TYPE:
            first_channel_idx = idx

    # The arrangement playlist: only record-aligned 233 payloads are real
    # playlists (short 233 blobs inside note/controller data must not be
    # touched). Use the LAST aligned one, for both reading and writing.
    playlist_candidates = [
        idx
        for idx, (eid, payload) in enumerate(events)
        if eid == EV_PLAYLIST and len(payload) % PLAYLIST_RECORD_SIZE == 0
    ]
    playlist_idx = playlist_candidates[-1] if playlist_candidates else None

    if first_channel_idx is None:
        raise ValueError("could not locate channel rack section")
    if playlist_idx is None:
        raise ValueError("no record-aligned playlist event found; refusing to patch")

    # --- Determine song length and clip id from the target playlist ---------
    song_length = 0
    max_clip_id = 0
    payload = events[playlist_idx][1]
    for rec in _decode_playlist_items(payload):
        iidx = _playlist_item_index(rec)
        cid = _playlist_item_clip_id(rec)
        ln = _playlist_item_length(rec)
        if iidx >= 20480:  # pattern clip
            song_length = max(song_length, ln)
        max_clip_id = max(max_clip_id, cid)

    last_point_beats = points[-1][0] if points else 0.0
    clip_length = int(max(song_length, last_point_beats * ppq + 1))
    clip_id = max_clip_id + 1

    # --- Build the new events ----------------------------------------------
    channel_events = []
    for eid, payload_hex in AUTOMATION_CHANNEL_TEMPLATE:
        if eid == EV_NEW:
            payload = struct.pack("<H", auto_iid)
        elif eid == EV_AUTOMATION:
            payload = build_automation_event(points)
        else:
            payload = bytes.fromhex(payload_hex)
        channel_events.append((eid, payload))

    init_control = (EV_INIT_CONTROL, build_init_control(auto_iid))

    # --- Splice into the event list ----------------------------------------
    # Init control first, then the automation channel block, both right
    # before the first existing channel (joining the controller cluster).
    # Untouched events keep their original raw bytes (span) for byte-exact
    # passthrough.
    new_events = []
    new_spans = []  # (start, end) into original data, or None for new/modified
    for idx, ev in enumerate(events):
        if idx == first_channel_idx:
            new_events.append(init_control)
            new_spans.append(None)
            for cev in channel_events:
                new_events.append(cev)
                new_spans.append(None)
        new_events.append(ev)
        new_spans.append(spans[idx])

    # Append the automation clip item to the target playlist (FL appends new
    # clips at the end). Re-locate it: still the last aligned one, since the
    # inserted events contain no 233.
    aligned = [
        i
        for i, (eid, pl) in enumerate(new_events)
        if eid == EV_PLAYLIST and len(pl) % PLAYLIST_RECORD_SIZE == 0
    ]
    target = aligned[-1]
    item = build_playlist_item(auto_iid, clip_length, clip_id)
    new_events[target] = (EV_PLAYLIST, new_events[target][1] + item)
    new_spans[target] = None

    # --- Serialize ---------------------------------------------------------
    buf = bytearray()
    buf += data[:22]  # header placeholder (fixed 22 bytes)
    for (eid, payload), span in zip(new_events, new_spans):
        if span is not None:
            buf += data[span[0] : span[1]]
        else:
            buf += encode_event(eid, payload)

    struct.pack_into("<H", buf, 10, header["num_channels"] + 1)
    struct.pack_into("<I", buf, 18, len(buf) - 22)

    # --- Verify before writing ---------------------------------------------
    check = verify_output(
        data, events, spans, first_channel_idx,
        playlist_idx, item, bytes(buf),
    )

    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(buf)

    return {
        "auto_iid": auto_iid,
        "num_points": len(points),
        "clip_length": clip_length,
        "clip_id": clip_id,
        "ppq": ppq,
        "division": division,
        "playlist_records": check["records_in_playlist"],
        "channel_iids": check["channel_iids"],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="mid_tempo_to_flp",
        description="Add fractional-BPM tempo automation from a MIDI file into an FLP.",
    )
    parser.add_argument("--mid", required=True, help="input MIDI file (tempo source)")
    parser.add_argument("--flp", required=True, help="input FL Studio project (.flp)")
    parser.add_argument("--out", help="output .flp path (default: <flp> + '-' + <mid stem>)")
    args = parser.parse_args(argv)

    if args.out:
        out = args.out
    else:
        stem = os.path.splitext(os.path.basename(args.mid))[0]
        out = f"{os.path.splitext(args.flp)[0]}-{stem}.flp"

    info = add_tempo_automation(args.flp, args.mid, out)

    print(f"wrote {out}")
    print(
        f"  automation channel IID: {info['auto_iid']} | points: {info['num_points']} "
        f"| clip length: {info['clip_length']} PPQ | clip id: {info['clip_id']}"
    )
    print(f"  ppq={info['ppq']} midi division={info['division']}")


if __name__ == "__main__":
    main()
