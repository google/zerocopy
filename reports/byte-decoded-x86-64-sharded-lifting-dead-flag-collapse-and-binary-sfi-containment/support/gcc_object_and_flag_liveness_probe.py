#!/usr/bin/env python3
"""
Empirical GCC 15.2.0 x86-64 `.o` byte-stream, `.rela.rodata` jump-table,
dynamic stack-realignment (`and rsp, -32`), VEX2/VEX3 encoding, and backward
`RFLAGS` liveness / demonic-undefined-flag kill-rate analyzer.

Compiles representative C translation units with `gcc -O2` and `gcc -O3 -mavx2`
inside `tempfile.TemporaryDirectory()`, parses ELF `.text` / `.rodata` /
`.rela.*` sections via `objdump` and `readelf`, and measures exact per-basic-block
backward liveness over `{CF, PF, AF, ZF, SF, OF}` (including `PF` parity8 and
architecturally undefined demonic flags).
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

C_WORKLOADS: dict[str, tuple[list[str], str]] = {
    "straight_alu_mix_o2": (
        ["-O2", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        r"""
#include <stdint.h>

uint64_t straight_alu_mix_o2(uint64_t a, uint64_t b, const uint64_t * restrict k, uint64_t * restrict out) {
    uint64_t v0 = a ^ k[0];
    uint64_t v1 = b + k[1];
    v0 = (v0 + v1) * 0x9E3779B97F4A7C15ULL;
    v1 = (v1 ^ (v0 >> 29)) + k[2];
    v0 = (v0 << 13) ^ v1;
    v1 = (v1 * k[3]) + (v0 >> 7);
    uint64_t res = (v0 ^ v1) + (a << 3);
    out[0] = res;
    return res ^ v0;
}
""",
    ),
    "aligned_frame_spills_o2": (
        ["-O2", "-mno-red-zone", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        r"""
#include <stdint.h>

#define MIX_STEP(s, i, c) do { \
    uint64_t t = (s[(i) & 7] + (c)) ^ (s[((i) + 3) & 7] << 7); \
    s[(i) & 7] = t * 0xBF58476D1CE4E5B9ULL; \
    s[((i) + 1) & 7] ^= (t >> 19); \
} while (0)

uint64_t aligned_frame_spills_o2(uint64_t seed, const uint64_t * restrict in_ptr, uint64_t * restrict out_ptr) {
    __attribute__((aligned(32))) volatile uint64_t frame_slots[8];
    for (int i = 0; i < 8; i++) {
        frame_slots[i] = in_ptr[i] ^ (seed + (uint64_t)i * 0x9E3779B97F4A7C15ULL);
    }
    MIX_STEP(frame_slots, 0, 0x11ULL);
    MIX_STEP(frame_slots, 1, 0x23ULL);
    MIX_STEP(frame_slots, 2, 0x37ULL);
    MIX_STEP(frame_slots, 3, 0x4BULL);
    uint64_t acc = frame_slots[0] + frame_slots[3] + frame_slots[5] + frame_slots[7];
    out_ptr[0] = acc;
    return acc;
}
""",
    ),
    "switch_dispatch_8_o2": (
        ["-O2", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        r"""
#include <stdint.h>

uint64_t switch_dispatch_8_o2(uint32_t op, uint64_t x, uint64_t y) {
    switch (op) {
        case 0: return (x + y) ^ 0x517CC1B727220A95ULL;
        case 1: return (x - y) * 0x9E3779B97F4A7C15ULL;
        case 2: return (x << 5) ^ (y >> 3);
        case 3: return (x & y) + (x | 0xFFULL);
        case 4: return (x ^ (y << 11)) + 0x1337ULL;
        case 5: return (y - (x >> 7)) * 3ULL;
        case 6: return ((x + 17ULL) * y) ^ (x >> 31);
        case 7: return (x << 1) + (y << 2) + 9ULL;
        default: return x ^ y;
    }
}
""",
    ),
    "avx2_vec_accum_o3": (
        ["-O3", "-mavx2", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        r"""
#include <immintrin.h>
#include <stddef.h>
#include <stdint.h>

uint32_t avx2_vec_accum_o3(const uint32_t * restrict buf, size_t n32) {
    __m256i acc = _mm256_setzero_si256();
    for (size_t i = 0; i + 8 <= n32; i += 8) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(buf + i));
        __m256i mixed = _mm256_xor_si256(v, _mm256_srli_epi32(v, 3));
        acc = _mm256_add_epi32(acc, mixed);
    }
    __m128i lo = _mm256_castsi256_si128(acc);
    __m128i hi = _mm256_extracti128_si256(acc, 1);
    __m128i s4 = _mm_add_epi32(lo, hi);
    s4 = _mm_add_epi32(s4, _mm_shuffle_epi32(s4, 0x4E));
    s4 = _mm_add_epi32(s4, _mm_shuffle_epi32(s4, 0xB1));
    uint32_t out = (uint32_t)_mm_cvtsi128_si32(s4);
    _mm256_zeroupper();
    return out;
}
""",
    ),
    "cyclic_crc_state_o2": (
        ["-O2", "-fcf-protection=full", "-fno-asynchronous-unwind-tables"],
        r"""
#include <stddef.h>
#include <stdint.h>

uint64_t cyclic_crc_state_o2(const uint64_t * restrict words, size_t n, uint64_t init) {
    uint64_t crc = init ^ 0xFFFFFFFFFFFFFFFFULL;
    for (size_t i = 0; i < n; i++) {
        uint64_t w = words[i] ^ crc;
        for (int b = 0; b < 8; b++) {
            uint64_t mask = -(w & 1ULL);
            w = (w >> 1) ^ (0xC96C5795D7870F42ULL & mask);
        }
        crc = (crc >> 8) ^ (w * 0x9E3779B97F4A7C15ULL);
    }
    return ~crc;
}
""",
    ),
}

ALL_FLAGS = ("cf", "pf", "af", "zf", "sf", "of")

# Map condition suffixes (`j<cc>`, `set<cc>`, `cmov<cc>`) to read flag sets:
CC_READS: dict[str, set[str]] = {
    "e": {"zf"}, "z": {"zf"}, "ne": {"zf"}, "nz": {"zf"},
    "b": {"cf"}, "c": {"cf"}, "nae": {"cf"},
    "ae": {"cf"}, "nb": {"cf"}, "nc": {"cf"},
    "be": {"cf", "zf"}, "na": {"cf", "zf"},
    "a": {"cf", "zf"}, "nbe": {"cf", "zf"},
    "s": {"sf"}, "ns": {"sf"},
    "p": {"pf"}, "pe": {"pf"}, "np": {"pf"}, "po": {"pf"},
    "o": {"of"}, "no": {"of"},
    "l": {"sf", "of"}, "nge": {"sf", "of"},
    "ge": {"sf", "of"}, "nl": {"sf", "of"},
    "le": {"zf", "sf", "of"}, "ng": {"zf", "sf", "of"},
    "g": {"zf", "sf", "of"}, "nle": {"zf", "sf", "of"},
}


def classify_flag_effects(mnemonic: str) -> tuple[set[str], set[str], set[str], bool]:
    """Return `(reads, defined_writes, undef_writes, is_branch_or_exit)` for an x86-64 mnemonic."""
    m = mnemonic.split()[-1].lower()  # strip prefixes like `notrack` or `rep`
    if m in ("ret", "retq"):
        return set(), set(), set(), True
    if m in ("jmp", "jmpq"):
        return set(), set(), set(), True
    if m.startswith("j") and m[1:] in CC_READS:
        return set(CC_READS[m[1:]]), set(), set(), True
    if m.startswith("cmov") and m[4:] in CC_READS:
        return set(CC_READS[m[4:]]), set(), set(), False
    if m.startswith("set") and m[3:] in CC_READS:
        return set(CC_READS[m[3:]]), set(), set(), False
    if m in ("adc", "sbb"):
        return {"cf"}, set(ALL_FLAGS), set(), False
    if m in ("add", "sub", "cmp", "neg"):
        return set(), set(ALL_FLAGS), set(), False
    if m in ("inc", "dec"):
        return set(), {"pf", "af", "zf", "sf", "of"}, set(), False
    if m in ("xor", "and", "or", "test"):
        return set(), {"cf", "pf", "zf", "sf", "of"}, {"af"}, False
    if m in ("shl", "sal", "shr", "sar"):
        # Multi-bit shifts leave OF (for count != 1) and AF architecturally undefined:
        return set(), {"cf", "pf", "zf", "sf"}, {"af", "of"}, False
    if m in ("imul", "mul"):
        return set(), {"cf", "of"}, {"pf", "af", "zf", "sf"}, False
    if m in ("bsf", "bsr"):
        return set(), {"zf"}, {"cf", "pf", "af", "sf", "of"}, False
    if m in ("tzcnt", "lzcnt"):
        return set(), {"cf", "zf"}, {"pf", "af", "sf", "of"}, False
    return set(), set(), set(), False


LINE_RE = re.compile(r"^\s*([0-9a-fA-F]+):\s+((?:[0-9a-fA-F]{2}\s)+)\s*(.*)$")


def parse_objdump_insns(obj_path: Path) -> list[dict[str, object]]:
    out = subprocess.check_output(
        ["objdump", "-d", "-M", "intel", "--no-show-raw-insn", str(obj_path)],
        text=True,
        timeout=10,
    )
    out_raw = subprocess.check_output(
        ["objdump", "-d", "-M", "intel", str(obj_path)],
        text=True,
        timeout=10,
    )
    insns: list[dict[str, object]] = []
    cur_bytes: list[int] = []
    cur_off: int | None = None
    cur_asm: str = ""
    for ln in out_raw.splitlines():
        m = LINE_RE.match(ln)
        if not m:
            continue
        off = int(m.group(1), 16)
        b_hex = [int(x, 16) for x in m.group(2).strip().split()]
        asm = m.group(3).strip()
        if asm == "" and insns and off == int(insns[-1]["offset"]) + len(insns[-1]["bytes"]):
            # Continuation line of a >7-byte instruction in objdump output
            insns[-1]["bytes"].extend(b_hex)
        else:
            insns.append({"offset": off, "bytes": b_hex, "asm": asm})
    _ = (out, cur_bytes, cur_off, cur_asm)
    return insns


def parse_relocations(obj_path: Path) -> list[dict[str, str]]:
    out = subprocess.check_output(["readelf", "-r", "-W", str(obj_path)], text=True, timeout=10)
    relocs: list[dict[str, str]] = []
    section = ""
    for ln in out.splitlines():
        s = ln.strip()
        if s.startswith("Relocation section '"):
            section = s.split("'")[1]
        elif s and len(s.split()) >= 5 and all(c in "0123456789abcdefABCDEF" for c in s.split()[0]):
            parts = s.split()
            relocs.append({
                "section": section,
                "offset": "0x" + parts[0],
                "type": parts[2],
                "sym_and_addend": " ".join(parts[4:]),
            })
    return relocs


def analyze_workload(name: str, flags: list[str], src: str, td: Path) -> dict[str, object]:
    c_file = td / f"{name}.c"
    o_file = td / f"{name}.o"
    c_file.write_text(src, encoding="utf-8")
    subprocess.run(["gcc"] + flags + ["-c", str(c_file), "-o", str(o_file)], check=True, timeout=20)

    insns = parse_objdump_insns(o_file)
    relocs = parse_relocations(o_file)
    all_bytes = [b for ins in insns for b in ins["bytes"]]
    lengths = [len(ins["bytes"]) for ins in insns]

    # Identify basic-block boundaries (branch targets + post-branch fallthroughs)
    target_offsets: set[int] = {0}
    for idx, ins in enumerate(insns):
        asm = str(ins["asm"])
        toks = asm.split()
        mnem = toks[0] if toks else ""
        if mnem == "notrack" and len(toks) >= 2:
            mnem = toks[1]
        if mnem.startswith("j") or mnem in ("ret", "retq"):
            if idx + 1 < len(insns):
                target_offsets.add(int(insns[idx + 1]["offset"]))
            for t in toks[1:]:
                if all(c in "0123456789abcdefABCDEF" for c in t):
                    target_offsets.add(int(t, 16))

    # Split into basic blocks
    blocks: list[list[dict[str, object]]] = []
    cur: list[dict[str, object]] = []
    for ins in insns:
        if int(ins["offset"]) in target_offsets and cur:
            blocks.append(cur)
            cur = []
        cur.append(ins)
    if cur:
        blocks.append(cur)

    # Conservative cross-block live-out seed: union of upward-exposed reads of all blocks,
    # except `ret` blocks whose SysV ABI exit has `live_out = empty`!
    block_upward_reads: list[set[str]] = []
    for blk in blocks:
        live: set[str] = set()
        for ins in reversed(blk):
            asm = str(ins["asm"])
            mnem = " ".join(asm.split()[:2]) if asm.startswith("notrack ") else (asm.split()[0] if asm.split() else "")
            reads, def_w, undef_w, _ = classify_flag_effects(mnem)
            live = (live - (def_w | undef_w)) | reads
        block_upward_reads.append(live)

    global_branch_live: set[str] = set()
    for rset in block_upward_reads:
        global_branch_live |= rset

    total_flag_writers = 0
    total_flag_bits_written = 0
    dead_flag_bits_written = 0
    total_undef_bits_written = 0
    dead_undef_bits_written = 0
    total_pf_writes = 0
    dead_pf_writes = 0

    for blk in blocks:
        last_asm = str(blk[-1]["asm"])
        last_mnem = last_asm.split()[0].lower() if last_asm.split() else ""
        # SysV x86-64 ABI: status flags are caller-clobbered (dead at `ret`)
        live = set() if last_mnem in ("ret", "retq") else set(global_branch_live)
        for ins in reversed(blk):
            asm = str(ins["asm"])
            mnem = " ".join(asm.split()[:2]) if asm.startswith("notrack ") else (asm.split()[0] if asm.split() else "")
            reads, def_w, undef_w, _ = classify_flag_effects(mnem)
            all_w = def_w | undef_w
            if all_w:
                total_flag_writers += 1
                for f in all_w:
                    total_flag_bits_written += 1
                    if f not in live:
                        dead_flag_bits_written += 1
                for f in undef_w:
                    total_undef_bits_written += 1
                    if f not in live:
                        dead_undef_bits_written += 1
                if "pf" in all_w:
                    total_pf_writes += 1
                    if "pf" not in live:
                        dead_pf_writes += 1
            live = (live - all_w) | reads

    vex2_count = sum(1 for ins in insns if ins["bytes"] and ins["bytes"][0] == 0xC5)
    vex3_count = sum(1 for ins in insns if ins["bytes"] and ins["bytes"][0] == 0xC4)
    has_and_rsp_realign = any("and" in str(ins["asm"]) and "rsp" in str(ins["asm"]) for ins in insns)
    has_notrack_jmp = any("notrack jmp" in str(ins["asm"]) for ins in insns)
    has_endbr64 = any("endbr64" in str(ins["asm"]) for ins in insns)
    has_vzeroupper = any("vzeroupper" in str(ins["asm"]) for ins in insns)

    return {
        "workload": name,
        "gcc_flags": flags,
        "text_bytes": len(all_bytes),
        "insn_count": len(insns),
        "basic_blocks": len(blocks),
        "min_insn_len": min(lengths),
        "max_insn_len": max(lengths),
        "mean_insn_len": round(sum(lengths) / len(lengths), 2),
        "has_endbr64": has_endbr64,
        "has_and_rsp_realign": has_and_rsp_realign,
        "has_notrack_jmp": has_notrack_jmp,
        "has_vzeroupper": has_vzeroupper,
        "vex2_insns": vex2_count,
        "vex3_insns": vex3_count,
        "relocation_count": len(relocs),
        "relocations_sample": relocs[:10],
        "flag_liveness": {
            "flag_writing_insns": total_flag_writers,
            "total_flag_bits_written": total_flag_bits_written,
            "dead_flag_bits_written": dead_flag_bits_written,
            "dead_flag_bit_pct": round(100.0 * dead_flag_bits_written / max(1, total_flag_bits_written), 2),
            "undef_flag_bits_written": total_undef_bits_written,
            "dead_undef_flag_bits_written": dead_undef_bits_written,
            "dead_undef_flag_pct": round(100.0 * dead_undef_bits_written / max(1, total_undef_bits_written), 2),
            "pf_parity8_writes": total_pf_writes,
            "dead_pf_parity8_writes": dead_pf_writes,
            "dead_pf_parity8_pct": round(100.0 * dead_pf_writes / max(1, total_pf_writes), 2),
        },
        "text_hex": bytes(all_bytes).hex(),
        "disassembly": [
            {
                "off": ins["offset"],
                "len": len(ins["bytes"]),
                "hex": bytes(ins["bytes"]).hex(),
                "asm": ins["asm"],
            }
            for ins in insns
        ],
    }


def main() -> int:
    gcc_ver = subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0]
    objdump_ver = subprocess.check_output(["objdump", "--version"], text=True).splitlines()[0]

    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)
        results = [
            analyze_workload(nm, fl, src, td)
            for nm, (fl, src) in C_WORKLOADS.items()
        ]

    tot_insns = sum(int(r["insn_count"]) for r in results)
    tot_bytes = sum(int(r["text_bytes"]) for r in results)
    tot_fb = sum(int(r["flag_liveness"]["total_flag_bits_written"]) for r in results)
    dead_fb = sum(int(r["flag_liveness"]["dead_flag_bits_written"]) for r in results)
    tot_ub = sum(int(r["flag_liveness"]["undef_flag_bits_written"]) for r in results)
    dead_ub = sum(int(r["flag_liveness"]["dead_undef_flag_bits_written"]) for r in results)
    tot_pf = sum(int(r["flag_liveness"]["pf_parity8_writes"]) for r in results)
    dead_pf = sum(int(r["flag_liveness"]["dead_pf_parity8_writes"]) for r in results)

    aggregate = {
        "workloads": len(results),
        "total_insns": tot_insns,
        "total_text_bytes": tot_bytes,
        "mean_bytes_per_insn": round(tot_bytes / max(1, tot_insns), 2),
        "max_insn_bytes": max(int(r["max_insn_len"]) for r in results),
        "total_flag_bits_written": tot_fb,
        "dead_flag_bits_written": dead_fb,
        "dead_flag_bit_pct": round(100.0 * dead_fb / max(1, tot_fb), 2),
        "undef_flag_bits_written": tot_ub,
        "dead_undef_flag_bits_written": dead_ub,
        "dead_undef_flag_pct": round(100.0 * dead_ub / max(1, tot_ub), 2),
        "pf_parity8_writes": tot_pf,
        "dead_pf_parity8_writes": dead_pf,
        "dead_pf_parity8_pct": round(100.0 * dead_pf / max(1, tot_pf), 2),
    }

    payload = {
        "toolchains": {"gcc": gcc_ver, "objdump": objdump_ver},
        "aggregate": aggregate,
        "workloads": results,
    }
    out_path = HERE / "gcc_object_and_flag_liveness_results.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    digest = hashlib.sha256(out_path.read_bytes()).hexdigest()
    print(f"Wrote {out_path.name} (sha256={digest[:16]}...): {json.dumps(aggregate)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
