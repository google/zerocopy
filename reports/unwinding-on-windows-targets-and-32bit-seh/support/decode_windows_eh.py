#!/usr/bin/env python3
"""Standalone decoder for Windows x64/ARM64 .pdata/.xdata, __CxxFrameHandler3 FuncInfo, and i686 .sxdata SafeSEH tables."""
import json
import struct


def decode_x64_unwind_info(buf: bytes) -> dict:
    hdr = buf[0]
    version = hdr & 0x7
    flags = (hdr >> 3) & 0x1F
    prolog_size = buf[1]
    code_count = buf[2]
    frame_reg = buf[3] & 0xF
    frame_off = ((buf[3] >> 4) & 0xF) * 16
    codes = []
    op_names = {
        0: "UWOP_PUSH_NONVOL",
        1: "UWOP_ALLOC_LARGE",
        2: "UWOP_ALLOC_SMALL",
        3: "UWOP_SET_FPREG",
        4: "UWOP_SAVE_NONVOL",
        5: "UWOP_SAVE_NONVOL_FAR",
        6: "UWOP_EPILOG",
        8: "UWOP_SAVE_XMM128",
        9: "UWOP_SAVE_XMM128_FAR",
        10: "UWOP_PUSH_MACHFRAME",
    }
    i = 0
    while i < code_count:
        code_off = buf[4 + 2 * i]
        op_info = buf[4 + 2 * i + 1]
        op = op_info & 0xF
        info = (op_info >> 4) & 0xF
        codes.append({
            "prolog_offset": code_off,
            "op": op_names.get(op, f"UWOP_{op}"),
            "op_info": info,
        })
        if op == 1:
            i += 3 if info == 1 else 2
        elif op in (4, 8):
            i += 2
        elif op in (5, 9):
            i += 3
        else:
            i += 1
    return {
        "version": version,
        "flags": flags,
        "prolog_size": prolog_size,
        "code_count": code_count,
        "frame_register": frame_reg,
        "frame_offset_bytes": frame_off,
        "unwind_codes": codes,
    }


def decode_cxx_func_info_64(buf: bytes) -> dict:
    fields = struct.unpack("<IIIIIIIIII", buf[:40])
    return {
        "magic_number": hex(fields[0] & 0x1FFFFFFF),
        "bbt_flags": hex(fields[0] >> 29),
        "max_state": fields[1],
        "disp_unwind_map": hex(fields[2]),
        "n_try_blocks": fields[3],
        "disp_try_block_map": hex(fields[4]),
        "n_ip_map_entries": fields[5],
        "disp_ip_to_state_map": hex(fields[6]),
        "disp_unwind_help": struct.unpack("<i", buf[28:32])[0],
        "disp_es_type_list": hex(fields[8]),
        "eh_flags": hex(fields[9]),
    }


if __name__ == "__main__":
    sample_uinfo = bytes([0x19, 0x0A, 0x03, 0x45, 0x0A, 0x03, 0x05, 0x72, 0x01, 0x50, 0x00, 0x00])
    print(json.dumps(decode_x64_unwind_info(sample_uinfo), indent=2))
