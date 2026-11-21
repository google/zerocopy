#!/usr/bin/env python3
"""Executable CI spec-cone digest & anti-reward-hacking gate probe over real rustc MIR.

Compiles a Rust crate containing:
  - A human-reviewed reference function `checksum_ref` that transitively calls a helper
    `mix_byte` and uses a `const SEED: u64`;
  - An inline-ASM implementation `checksum_asm`;
  - An unrelated function `unrelated_fn`.

Extracts real `Runtime(PostCleanup)` MIR via `rustc +1.99.1` (`RUSTC_BOOTSTRAP=1
-Z dump-mir=runtime-post-cleanup`), computes the transitive MIR call-cone digest
`SpecConeHash(checksum_ref)` and per-function content-addressed verification cache key
`CacheKey(checksum_asm)`, and tests four PR mutation scenarios:
  1. PR edits ONLY `unrelated_fn` -> `SpecConeHash` UNCHANGED, `CacheKey` UNCHANGED (cache HIT).
  2. PR optimizes ONLY `checksum_asm` -> `SpecConeHash` UNCHANGED (0 human review needed!),
     `CacheKey` CHANGED (triggers re-proof of `checksum_asm` only).
  3. PR leaves `checksum_ref` untouched but silently tampers with transitive helper
     `mix_byte` -> `SpecConeHash` CHANGED (surfaces immediately on Human Review Surface!).
  4. PR modifies `#[cfg]` / target features (`-C target-feature=+avx2`) -> `CacheKey`
     CHANGED (prevents stale cross-target cache reuse!).

Uses `tempfile.TemporaryDirectory()` for all transient build files.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

BASE_CRATE_RS = r"""
use core::arch::asm;

const SEED: u64 = 0x9E37_79B9;

#[inline(never)]
fn mix_byte(acc: u64, b: u8) -> u64 {
    acc.wrapping_mul(31).wrapping_add(b as u64)
}

#[allow(dead_code)]
fn checksum_ref(slice: &[u8]) -> u64 {
    let mut acc = SEED;
    for &b in slice {
        acc = mix_byte(acc, b);
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn checksum_asm(ptr: *const u8, len: usize) -> u64 {
    let mut acc = SEED;
    let mut i = 0usize;
    while i < len {
        let b = unsafe { *ptr.add(i) } as u64;
        unsafe {
            asm!(
                "imul {acc}, {acc}, 31",
                "add {acc}, {b}",
                acc = inout(reg) acc,
                b = in(reg) b,
                options(nomem, nostack),
            );
        }
        i += 1;
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn unrelated_fn(x: u64) -> u64 {
    x.wrapping_add(1)
}
"""


def dump_post_cleanup_mir(src: str, extra_flags: list[str] | None = None) -> dict[str, str]:
    """Compile `src` with `rustc +1.99.1` and return {fn_name: post_cleanup_mir_text}."""
    with tempfile.TemporaryDirectory(prefix="anneal_ci_gate_") as td:
        tmp = Path(td)
        rs = tmp / "crate_under_test.rs"
        mir_dir = tmp / "mir"
        mir_dir.mkdir()
        rs.write_text(src)
        env = os.environ.copy()
        env["RUSTC_BOOTSTRAP"] = "1"
        cmd = [
            "rustc", "+1.99.1", "--edition=2024", "--crate-type=lib", "-O",
            "--crate-name", "demo",
            "-Z", "dump-mir=all",
            "-Z", f"dump-mir-dir={mir_dir}",
            str(rs), "--out-dir", str(tmp),
        ]
        if extra_flags:
            cmd.extend(extra_flags)
        p = subprocess.run(cmd, capture_output=True, text=True, env=env)
        if p.returncode != 0:
            raise RuntimeError(f"rustc failed: {p.stderr}")
        out: dict[str, str] = {}
        for path in sorted(mir_dir.glob("*runtime-post-cleanup.after.mir")):
            # Filename format: demo.<fn_name>.3-2-000.runtime-post-cleanup.after.mir
            stem = path.name
            m = re.match(r"^demo\.(.+?)\.\d+-\d+-\d+\.runtime-post-cleanup\.after\.mir$", stem)
            if m:
                out[m.group(1)] = path.read_text()
        return out


def normalize_mir_for_hash(mir_text: str) -> str:
    """Strip source line/column span comments (which shift when unrelated lines move)
    while retaining all MIR types, constants, operands, calls, and CFG structure."""
    lines = []
    for line in mir_text.splitlines():
        # Strip `// at /tmp/.../file.rs:LINE:COL: LINE:COL` span annotations
        cleaned = re.sub(r"//\s*at\s+.*$", "", line).rstrip()
        if cleaned:
            lines.append(cleaned)
    return "\n".join(lines)


def extract_local_callees(mir_text: str, local_fns: set[str]) -> set[str]:
    """Find local function names referenced in MIR `TerminatorKind::Call` / operands."""
    callees: set[str] = set()
    for fn in local_fns:
        if re.search(rf"\b{re.escape(fn)}\s*\(", mir_text):
            callees.add(fn)
    return callees


def compute_spec_cone_hash(mir_map: dict[str, str], root_fn: str) -> tuple[list[str], str]:
    """Compute transitive call-closure over local MIR bodies starting at `root_fn`."""
    local_fns = set(mir_map.keys())
    visited: set[str] = set()
    stack = [root_fn]
    while stack:
        cur = stack.pop()
        if cur in visited or cur not in mir_map:
            continue
        visited.add(cur)
        for callee in extract_local_callees(mir_map[cur], local_fns):
            if callee not in visited:
                stack.append(callee)
    ordered = sorted(visited)
    h = hashlib.sha256()
    for fn in ordered:
        h.update(fn.encode())
        h.update(b"\0")
        h.update(normalize_mir_for_hash(mir_map[fn]).encode())
        h.update(b"\0")
    return ordered, h.hexdigest()


def compute_cache_key(
    rustc_ver: str,
    target_flags: list[str],
    spec_cone_hash: str,
    impl_mir: str,
) -> str:
    h = hashlib.sha256()
    h.update(rustc_ver.encode())
    h.update(b"\0")
    h.update(" ".join(target_flags).encode())
    h.update(b"\0")
    h.update(spec_cone_hash.encode())
    h.update(b"\0")
    h.update(normalize_mir_for_hash(impl_mir).encode())
    return h.hexdigest()


def main() -> int:
    rustc_ver = subprocess.run(
        ["rustc", "+1.99.1", "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()

    base_mir = dump_post_cleanup_mir(BASE_CRATE_RS)
    base_cone, base_spec_hash = compute_spec_cone_hash(base_mir, "checksum_ref")
    base_cache_key = compute_cache_key(rustc_ver, [], base_spec_hash, base_mir["checksum_asm"])

    # Scenario 1: Edit unrelated_fn (including adding blank lines that shift line numbers!)
    s1_src = BASE_CRATE_RS.replace(
        "x.wrapping_add(1)",
        "\n    // comment shifting line numbers\n    x.wrapping_add(42)",
    )
    s1_mir = dump_post_cleanup_mir(s1_src)
    s1_cone, s1_spec_hash = compute_spec_cone_hash(s1_mir, "checksum_ref")
    s1_cache_key = compute_cache_key(rustc_ver, [], s1_spec_hash, s1_mir["checksum_asm"])

    # Scenario 2: Agent hyper-optimizes ONLY `checksum_asm` (e.g., shift-sub instead of imul 31)
    s2_src = BASE_CRATE_RS.replace(
        '"imul {acc}, {acc}, 31",',
        '"mov r11, {acc}", "shl {acc}, 5", "sub {acc}, r11",',
    ).replace(
        'options(nomem, nostack),',
        'out("r11") _, options(nomem, nostack),',
    )
    s2_mir = dump_post_cleanup_mir(s2_src)
    s2_cone, s2_spec_hash = compute_spec_cone_hash(s2_mir, "checksum_ref")
    s2_cache_key = compute_cache_key(rustc_ver, [], s2_spec_hash, s2_mir["checksum_asm"])

    # Scenario 3: Reward-hacking PR leaves `checksum_ref` untouched but weakens helper `mix_byte`!
    s3_src = BASE_CRATE_RS.replace(
        "acc.wrapping_mul(31).wrapping_add(b as u64)",
        "0 /* reward-hacked helper */",
    )
    s3_mir = dump_post_cleanup_mir(s3_src)
    s3_cone, s3_spec_hash = compute_spec_cone_hash(s3_mir, "checksum_ref")
    s3_cache_key = compute_cache_key(rustc_ver, [], s3_spec_hash, s3_mir["checksum_asm"])

    # Scenario 4: Target feature / compiler flag change (`-C target-feature=+avx2`)
    s4_flags = ["-C", "target-feature=+avx2"]
    s4_mir = dump_post_cleanup_mir(BASE_CRATE_RS, extra_flags=s4_flags)
    s4_cone, s4_spec_hash = compute_spec_cone_hash(s4_mir, "checksum_ref")
    s4_cache_key = compute_cache_key(rustc_ver, s4_flags, s4_spec_hash, s4_mir["checksum_asm"])

    report = {
        "rustc_version": rustc_ver,
        "base": {
            "spec_cone": base_cone,
            "spec_cone_hash": base_spec_hash,
            "cache_key": base_cache_key,
        },
        "scenarios": {
            "1_edit_unrelated_fn": {
                "spec_cone_changed": s1_spec_hash != base_spec_hash,
                "cache_key_changed": s1_cache_key != base_cache_key,
                "requires_human_spec_review": s1_spec_hash != base_spec_hash,
                "triggers_reverify": s1_cache_key != base_cache_key,
            },
            "2_optimize_asm_only": {
                "spec_cone_changed": s2_spec_hash != base_spec_hash,
                "cache_key_changed": s2_cache_key != base_cache_key,
                "requires_human_spec_review": s2_spec_hash != base_spec_hash,
                "triggers_reverify": s2_cache_key != base_cache_key,
            },
            "3_tamper_transitive_helper_mix_byte": {
                "spec_cone_changed": s3_spec_hash != base_spec_hash,
                "cache_key_changed": s3_cache_key != base_cache_key,
                "requires_human_spec_review": s3_spec_hash != base_spec_hash,
                "triggers_reverify": s3_cache_key != base_cache_key,
            },
            "4_target_feature_flag_change": {
                "spec_cone_changed": s4_spec_hash != base_spec_hash,
                "cache_key_changed": s4_cache_key != base_cache_key,
                "requires_human_spec_review": s4_spec_hash != base_spec_hash,
                "triggers_reverify": s4_cache_key != base_cache_key,
            },
        },
    }

    assert report["base"]["spec_cone"] == ["checksum_ref", "mix_byte"]
    assert not report["scenarios"]["1_edit_unrelated_fn"]["spec_cone_changed"]
    assert not report["scenarios"]["1_edit_unrelated_fn"]["cache_key_changed"]
    assert not report["scenarios"]["2_optimize_asm_only"]["spec_cone_changed"]
    assert report["scenarios"]["2_optimize_asm_only"]["cache_key_changed"]
    assert report["scenarios"]["3_tamper_transitive_helper_mix_byte"]["spec_cone_changed"]
    assert report["scenarios"]["3_tamper_transitive_helper_mix_byte"]["cache_key_changed"]
    assert report["scenarios"]["4_target_feature_flag_change"]["cache_key_changed"]

    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
