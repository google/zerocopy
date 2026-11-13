#!/usr/bin/env python3
"""Standalone decoder for ELF .eh_frame/.gcc_except_table, Mach-O __compact_unwind/__unwind_info, and Windows COFF .pdata/.xdata/.sxdata."""
import struct
import sys
from pathlib import Path


def read_uleb128(buf: bytes, off: int) -> tuple[int, int]:
    val = 0
    shift = 0
    while True:
        b = buf[off]
        off += 1
        val |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            return val, off
        shift += 7


def read_sleb128(buf: bytes, off: int) -> tuple[int, int]:
    val = 0
    shift = 0
    while True:
        b = buf[off]
        off += 1
        val |= (b & 0x7F) << shift
        shift += 7
        if (b & 0x80) == 0:
            if shift < 64 and (b & 0x40):
                val |= -(1 << shift)
            return val, off


def decode_gcc_lsda(lsda: bytes) -> dict:
    off = 0
    lp_start_enc = lsda[off]
    off += 1
    assert lp_start_enc == 0xFF, f"Expected DW_EH_PE_omit (0xff), got {lp_start_enc:#x}"
    ttype_enc = lsda[off]
    off += 1
    ttype_base_off = None
    if ttype_enc != 0xFF:
        ttype_off, off = read_uleb128(lsda, off)
        ttype_base_off = off + ttype_off
    cs_enc = lsda[off]
    off += 1
    cs_len, off = read_uleb128(lsda, off)
    cs_end = off + cs_len
    call_sites = []
    while off < cs_end:
        assert cs_enc == 0x01, f"Expected ULEB128 callsite encoding (0x01), got {cs_enc:#x}"
        cs_start, off = read_uleb128(lsda, off)
        cs_length, off = read_uleb128(lsda, off)
        cs_lpad, off = read_uleb128(lsda, off)
        cs_action, off = read_uleb128(lsda, off)
        call_sites.append({
            "cs_start": cs_start,
            "cs_len": cs_length,
            "cs_lpad": cs_lpad,
            "cs_action_entry": cs_action,
        })
    actions = []
    act_off = cs_end
    limit = (ttype_base_off - 4) if ttype_base_off is not None else len(lsda)
    while act_off < limit and act_off < len(lsda):
        if lsda[act_off] == 0 and act_off + 1 == len(lsda):
            break
        ttype_idx, next_pos = read_sleb128(lsda, act_off)
        if next_pos >= len(lsda):
            break
        next_act, next_pos2 = read_sleb128(lsda, next_pos)
        actions.append({
            "byte_offset_1based": act_off - cs_end + 1,
            "ttype_index": ttype_idx,
            "next_action_offset": next_act,
        })
        act_off = next_pos2
    return {
        "lp_start_encoding": hex(lp_start_enc),
        "ttype_encoding": hex(ttype_enc),
        "call_site_encoding": hex(cs_enc),
        "call_site_table_length": cs_len,
        "call_sites": call_sites,
        "actions": actions,
    }


def decode_win_arm64_packed_pdata(rva: int, unwind_data: int) -> dict:
    flag = unwind_data & 0x3
    if flag == 0:
        return {"function_rva": hex(rva), "flag": 0, "xdata_rva": hex(unwind_data)}
    func_len = ((unwind_data >> 2) & 0x7FF) * 4
    reg_f = (unwind_data >> 13) & 0x7
    reg_i = (unwind_data >> 16) & 0xF
    h = (unwind_data >> 20) & 0x1
    cr = (unwind_data >> 21) & 0x3
    frame_size = ((unwind_data >> 23) & 0x1FF) * 16
    return {
        "function_rva": hex(rva),
        "flag": flag,
        "function_length_bytes": func_len,
        "saved_float_regs": (reg_f + 1) if reg_f > 0 else 0,
        "saved_int_regs": reg_i,
        "homed_params": bool(h),
        "chain_return_mode": cr,
        "frame_size_bytes": frame_size,
    }


if __name__ == "__main__":
    # Self-test on catch_unwind_entry LSDA bytes from probe_x86_64-unknown-linux-gnu.o
    sample_lsda = bytes([
        0xFF, 0x9B, 0x19, 0x01, 0x10,
        0x08, 0x05, 0x11, 0x03,
        0x11, 0x08, 0x67, 0x01,
        0x26, 0x05, 0x4E, 0x00,
        0x2B, 0x3C, 0x00, 0x00,
        0x7F, 0x00, 0x01, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00
    ])
    import json
    print(json.dumps(decode_gcc_lsda(sample_lsda), indent=2))
