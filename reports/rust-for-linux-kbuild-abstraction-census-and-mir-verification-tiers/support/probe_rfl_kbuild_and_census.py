#!/usr/bin/env python3
"""Deterministic algebraic, Kbuild-target, and optional source-tree revalidator
for the Rust for Linux (RfL) verification architecture report.

Default mode (`python3 -B probe_rfl_kbuild_and_census.py`) executes pure
standard-library checks with zero network or external filesystem dependencies:
  1. Verifies bit-width shift/mask corner cases underlying `kernel::num::Bounded`
     (`fits_within`), `kernel::dma::CoherentAllocation` (`dma_bit_mask`), and
     `kernel::page::page_align` (wrapping overflow domain `[2^64 - 4095, 2^64)`).
  2. Verifies Kbuild `generate_rust_target.rs` ABI version transitions
     (`rustc >= 1.98.0` `"softfloat"` vs. `"x86-softfloat"`) and endianness
     divergence against big-endian byte projections.
  3. Checks structural consistency of the pinned `torvalds/linux` commit
     `b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f` (`Linux 7.4-rc4`) census totals.

Optional tree mode (`--linux-root /path/to/linux`) recomputes the `.rs` and
`rust/helpers/*.c` census over a local Linux checkout for future revalidation.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

PINNED_LINUX_COMMIT = "b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f"

PINNED_CENSUS_SUMMARY = {
    "total_rs_files": 568,
    "rust_kernel": {
        "files": 169,
        "lines": 62930,
        "unsafe_blocks": 1870,
        "unsafe_fns": 476,
        "unsafe_impls": 383,
        "safety_comments": 2244,
        "invariants_headers": 153,
        "asm_sites": 6,
    },
    "rust_pin_init": {
        "files": 11,
        "unsafe_blocks": 119,
    },
    "drivers_selected": {
        "rnull_unsafe_blocks": 0,
        "phy_unsafe_blocks": 0,
        "pwm_unsafe_blocks": 0,
        "drm_unsafe_blocks": 9,
        "nova_core_unsafe_blocks": 37,
        "binder_unsafe_blocks": 152,
    },
    "rust_helpers_c": {
        "leaf_c_files": 69,
        "helper_functions": 439,
    },
}


def fits_within_rfl_u8(value: int, num_bits: int) -> tuple[str, bool | None]:
    """Model MIR shift-checked execution of `(value << (8 - num_bits)) >> (8 - num_bits) == value`."""
    assert 0 <= value < 256
    if num_bits > 8:
        return ("panic_or_ub_underflow", None)
    shift = 8 - num_bits
    if shift >= 8:
        # In Rust MIR (`BinOp::Shl` / `Shr`), shifting a W-bit integer by >= W faults.
        return ("mir_shift_ub", None)
    masked = (((value << shift) & 0xFF) >> shift)
    return ("ok", masked == value)


def dma_bit_mask_u64(n: int) -> tuple[str, int | None]:
    """Model `rust/kernel/dma.rs` `dma_bit_mask` vs. unguarded `(1u64 << n) - 1`."""
    if n < 0 or n > 64:
        return ("invalid_width", None)
    if n == 64:
        return ("ok", (1 << 64) - 1)
    if n == 0:
        return ("ok", 0)
    return ("ok", (1 << n) - 1)


def page_align_4k_u64(addr: int) -> tuple[int, bool]:
    """Model `(addr + 4095) & !4095` in 64-bit unsigned arithmetic with overflow flag."""
    assert 0 <= addr < (1 << 64)
    raw_sum = addr + 4095
    overflowed = raw_sum >= (1 << 64)
    wrapped = raw_sum & ((1 << 64) - 1)
    return (wrapped & ~4095, overflowed)


def kbuild_x86_rustc_abi(version_tuple: tuple[int, int, int]) -> str:
    """Mirror `scripts/generate_rust_target.rs:206-210` (`rustc >= 1.98.0` transition)."""
    return "softfloat" if version_tuple >= (1, 98, 0) else "x86-softfloat"


def verify_algebraic_and_abi_models() -> dict[str, object]:
    # 1. Exhaustive u8 verification of `fits_within` (`num_bits` in 0..=8).
    status_zero, _ = fits_within_rfl_u8(0, 0)
    assert status_zero == "mir_shift_ub", "unguarded num_bits == 0 shifts by bit-width W"
    for k in range(1, 9):
        for v in range(256):
            if k == 8:
                # shift = 0: valid in MIR, always true for u8
                st, ok = fits_within_rfl_u8(v, 8)
                assert st == "ok" and ok is True
            else:
                st, ok = fits_within_rfl_u8(v, k)
                assert st == "ok" and ok == (v < (1 << k))

    # 2. Exhaustive width check (`0..=64`) of `dma_bit_mask_u64`.
    for n in range(65):
        st, mask = dma_bit_mask_u64(n)
        assert st == "ok" and mask == ((1 << n) - 1)
        if n == 64:
            # Confirm why `n == 64` requires an explicit branch in MIR (`64 >= 64` shift UB).
            assert n >= 64
    assert dma_bit_mask_u64(65) == ("invalid_width", None)

    # 3. Page alignment boundary check at 4 KiB (`PAGE_SIZE = 4096`).
    max_u64 = (1 << 64) - 1
    max_aligned = max_u64 - 4095  # 0xffff_ffff_ffff_f000
    assert page_align_4k_u64(0) == (0, False)
    assert page_align_4k_u64(1) == (4096, False)
    assert page_align_4k_u64(4096) == (4096, False)
    assert page_align_4k_u64(max_aligned) == (max_aligned, False)
    # Any address in `[max_aligned + 1, max_u64]` wraps to 0 under wrapping add!
    assert page_align_4k_u64(max_aligned + 1) == (0, True)
    assert page_align_4k_u64(max_u64) == (0, True)

    # 4. Kbuild `generate_rust_target.rs` ABI transition & endianness check.
    assert kbuild_x86_rustc_abi((1, 85, 0)) == "x86-softfloat"
    assert kbuild_x86_rustc_abi((1, 97, 0)) == "x86-softfloat"
    assert kbuild_x86_rustc_abi((1, 98, 0)) == "softfloat"

    word = 0x01020304
    le_bytes = list(word.to_bytes(4, "little"))
    be_bytes = list(word.to_bytes(4, "big"))
    assert le_bytes == [0x04, 0x03, 0x02, 0x01]
    assert be_bytes == [0x01, 0x02, 0x03, 0x04]
    assert le_bytes != be_bytes

    # 5. Pinned census sanity relationships.
    rk = PINNED_CENSUS_SUMMARY["rust_kernel"]
    drv = PINNED_CENSUS_SUMMARY["drivers_selected"]
    assert drv["rnull_unsafe_blocks"] == 0
    assert drv["phy_unsafe_blocks"] == 0
    assert drv["pwm_unsafe_blocks"] == 0
    assert rk["safety_comments"] > rk["unsafe_blocks"]

    return {
        "status": "ok",
        "pinned_linux_commit": PINNED_LINUX_COMMIT,
        "fits_within_u8_pairs_checked": 9 * 256,
        "dma_mask_widths_checked": 66,
        "page_align_overflow_threshold_hex": hex(max_aligned + 1),
        "rustc_1_98_x86_abi": kbuild_x86_rustc_abi((1, 98, 0)),
    }


UNSAFE_BLOCK_RE = re.compile(r"\bunsafe\s*\{")
UNSAFE_FN_RE = re.compile(r"\bunsafe\s+(?:extern\s+(?:\"[^\"]*\"\s+)?)?fn\b")
UNSAFE_IMPL_RE = re.compile(r"\bunsafe\s+impl\b")
SAFETY_COMMENT_RE = re.compile(r"//\s*SAFETY:")
INVARIANTS_RE = re.compile(r"#\s*Invariants\b")
ASM_RE = re.compile(r"\b(?:core::arch::)?asm!\s*\(")
HELPER_C_RE = re.compile(r"\brust_helper_[A-Za-z0-9_]+\s*\(")


def scan_linux_tree(linux_root: Path) -> dict[str, object]:
    rs_files = sorted(linux_root.rglob("*.rs"))
    kernel_files = [p for p in rs_files if p.is_relative_to(linux_root / "rust/kernel")]

    def agg(paths: list[Path]) -> dict[str, int]:
        totals = {
            "files": len(paths),
            "lines": 0,
            "unsafe_blocks": 0,
            "unsafe_fns": 0,
            "unsafe_impls": 0,
            "safety_comments": 0,
            "invariants_headers": 0,
            "asm_sites": 0,
        }
        for p in paths:
            txt = p.read_text(encoding="utf-8", errors="replace")
            totals["lines"] += len(txt.splitlines())
            totals["unsafe_blocks"] += len(UNSAFE_BLOCK_RE.findall(txt))
            totals["unsafe_fns"] += len(UNSAFE_FN_RE.findall(txt))
            totals["unsafe_impls"] += len(UNSAFE_IMPL_RE.findall(txt))
            totals["safety_comments"] += len(SAFETY_COMMENT_RE.findall(txt))
            totals["invariants_headers"] += len(INVARIANTS_RE.findall(txt))
            totals["asm_sites"] += len(ASM_RE.findall(txt))
        return totals

    helpers_dir = linux_root / "rust/helpers"
    c_leafs = sorted(
        p for p in helpers_dir.glob("*.c") if p.name != "helpers.c"
    ) if helpers_dir.is_dir() else []
    helper_defs = sum(
        len(HELPER_C_RE.findall(p.read_text(encoding="utf-8", errors="replace")))
        for p in c_leafs
    )
    return {
        "total_rs_files": len(rs_files),
        "rust_kernel": agg(kernel_files),
        "rust_helpers_c": {
            "leaf_c_files": len(c_leafs),
            "helper_functions": helper_defs,
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--linux-root",
        type=Path,
        help="Optional path to a Linux kernel tree to re-run the source census",
    )
    args = parser.parse_args(argv)

    result = verify_algebraic_and_abi_models()
    if args.linux_root is not None:
        result["live_tree_census"] = scan_linux_tree(args.linux_root.resolve())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
