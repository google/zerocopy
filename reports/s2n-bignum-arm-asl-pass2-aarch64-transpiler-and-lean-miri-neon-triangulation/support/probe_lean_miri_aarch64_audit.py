#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Audit proofs-rs/lean-miri@c92d1d97 AArch64 intrinsic coverage across stdarch
and 12 production Rust SIMD crates, verify IntrinsicAarch64Ext.lean under Lean
v4.34.1 standalone private kernel replay, and differentially cross-check FIPS-197
AES-128, FIPS-180-4 SHA-512, and NEON reductions/shifts/PMULL on live
rustc + qemu-aarch64 -cpu max.

All temporary compilations and QEMU runs execute inside
tempfile.TemporaryDirectory().
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

PRODUCTION_CRATES = [
    "zlib-rs-0.6.8",
    "memchr-2.8.3",
    "simdutf8-0.1.5",
    "crc32fast-1.5.5",
    "simd-adler32-0.3.10",
    "blake3-1.8.7",
    "aho-corasick-1.1.5",
    "bytecount-0.6.9",
    "hashbrown-0.17.1",
    "sha2-0.11.1",
    "chacha20-0.10.2",
    "aes-0.9.4",
]


def strip_lean_comments(text: str) -> str:
    out = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        if depth == 0 and not in_str and text[i : i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if not in_str and text[i : i + 2] == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0 and text[i : i + 2] == "-/":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            if text[i] == '"' and (i == 0 or text[i - 1] != "\\"):
                in_str = not in_str
            out.append(text[i])
        i += 1
    return "".join(out)


def scan_lean_file(path: Path) -> dict:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    clean = strip_lean_comments(text)
    constructs = {
        "axiom": len(re.findall(r"\baxiom\b", clean)),
        "opaque": len(re.findall(r"\bopaque\b", clean)),
        "partial": len(re.findall(r"\bpartial\b", clean)),
        "unsafe": len(re.findall(r"\bunsafe\b", clean)),
        "sorry": len(re.findall(r"\bsorry\b", clean)),
        "admit": len(re.findall(r"\badmit\b", clean)),
        "bv_decide": len(re.findall(r"\bbv_decide\b", clean)),
        "native_decide": len(re.findall(r"\bnative_decide\b", clean)),
        "extern_attr": len(re.findall(r"@\[[^\]]*\bextern\b", clean)),
        "implemented_by_attr": len(re.findall(r"@\[[^\]]*\bimplemented_by\b", clean)),
        "csimp_attr": len(re.findall(r"@\[[^\]]*\bcsimp\b", clean)),
        "set_option": len(re.findall(r"\bset_option\b", clean)),
        "by_tactic_blocks": len(re.findall(r":=\s*by\b|\bby\s+decide\b", clean)),
    }
    decls = len(
        re.findall(
            r"^\s*(?:private\s+|protected\s+)?(?:def|abbrev|structure|inductive|theorem)\s+",
            clean,
            re.M,
        )
    )
    return {
        "lines": len(text.splitlines()),
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "top_level_decls": decls,
        "constructs": constructs,
    }


def is_base_lean_miri_supported(lnk: str) -> bool:
    if lnk == "llvm.prefetch.p0" or lnk.startswith("llvm.ctpop.v"):
        return True
    if not lnk.startswith("llvm.aarch64."):
        return False
    suf = lnk[len("llvm.aarch64.") :]
    if suf == "neon.umaxp.v16i8":
        return True
    if (
        suf.startswith("neon.addp.")
        or suf.startswith("neon.uaddlp.")
        or suf.startswith("neon.sqdmulh.")
    ):
        return True
    if suf in {
        "neon.tbl1.v8i8",
        "neon.tbl1.v16i8",
        "neon.tbl2.v8i8",
        "neon.tbl2.v16i8",
        "neon.tbl3.v8i8",
        "neon.tbl3.v16i8",
        "neon.tbl4.v8i8",
        "neon.tbl4.v16i8",
    }:
        return True
    if suf in {
        "crc32b",
        "crc32h",
        "crc32w",
        "crc32x",
        "crc32cb",
        "crc32ch",
        "crc32cw",
        "crc32cx",
    }:
        return True
    if suf == "neon.pmull64":
        return True
    if suf in {
        "crypto.sha256h",
        "crypto.sha256h2",
        "crypto.sha256su0",
        "crypto.sha256su1",
    }:
        return True
    return False


def extract_ext_supported_names(ext_lean: Path) -> set[str]:
    txt = ext_lean.read_text(encoding="utf-8")
    return set(re.findall(r'"(llvm\.aarch64\.[a-z0-9.]+)"', txt))


def audit_stdarch_and_12crates(
    toolchain: str, vendor_dir: Path, ext_names: set[str]
) -> dict:
    sysroot = subprocess.check_output(
        ["rustc", f"+{toolchain}", "--print", "sysroot"], text=True
    ).strip()
    core_arch = (
        Path(sysroot) / "lib/rustlib/src/rust/library/stdarch/crates/core_arch/src"
    )
    sample_files = sorted((core_arch / "arm_shared").rglob("*.rs")) + sorted(
        (core_arch / "aarch64").rglob("*.rs")
    )

    mod_externs: dict[tuple[str, str], set[str]] = {}
    global_externs: dict[str, set[str]] = {}
    all_aarch64_links: set[str] = set()
    all_nonsve_links: set[str] = set()
    pub_fns: dict[str, list[tuple[str, str]]] = {}

    for fp in sample_files:
        rel = str(fp.relative_to(core_arch))
        txt = fp.read_text(errors="ignore")
        for m in re.finditer(
            r"((?:#\[[^\]]*\]\s*)+)(?:pub\s+)?(?:safe\s+|unsafe\s+)?fn\s+([a-zA-Z0-9_]+)\s*\(",
            txt,
        ):
            attrs, fname = m.group(1), m.group(2)
            for lm in re.finditer(r'link_name\s*=\s*"(llvm\.[^"]+)"', attrs):
                lnk = lm.group(1)
                if lnk.startswith("llvm.arm."):
                    continue
                if lnk.startswith("llvm.aarch64."):
                    all_aarch64_links.add(lnk)
                    if ".sve." not in lnk and "sve" not in rel:
                        all_nonsve_links.add(lnk)
                mod_externs.setdefault((rel, fname), set()).add(lnk)
                global_externs.setdefault(fname, set()).add(lnk)

        txt_notest = re.split(r"#\[cfg\(test\)\]\s*mod\s+", txt)[0]
        lines = txt_notest.splitlines()
        i = 0
        while i < len(lines):
            m = re.search(
                r"^\s*pub\s+(?:const\s+)?(?:unsafe\s+)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)",
                lines[i],
            )
            if (
                not m
                and i + 1 < len(lines)
                and re.match(r"^\s*pub\s+(?:const\s+)?(?:unsafe\s+)?$", lines[i])
            ):
                m = re.search(r"^\s*fn\s+([a-zA-Z_][a-zA-Z0-9_]*)", lines[i + 1])
            if m:
                name = m.group(1)
                buf = []
                depth = 0
                started = False
                j = i
                while j < len(lines):
                    line = lines[j]
                    buf.append(line)
                    if "{" in line:
                        started = True
                        depth += line.count("{") - line.count("}")
                        if depth <= 0:
                            break
                    elif started:
                        depth += line.count("{") - line.count("}")
                        if depth <= 0:
                            break
                    j += 1
                pub_fns.setdefault(name, []).append(("\n".join(buf), rel))
                i = j + 1
            else:
                i += 1

    simd_txt = (vendor_dir / "Miri/Interpreter/IntrinsicSimd.lean").read_text(
        encoding="utf-8"
    )
    portable_simd_set = set(re.findall(r'"(simd_[a-z0-9_]+)"', simd_txt))

    def classify_fn(name: str, seen: set[str] | None = None) -> tuple[set[str], set[str]]:
        if seen is None:
            seen = set()
        if name in seen or name not in pub_fns:
            return set(), set()
        seen.add(name)
        s_ops: set[str] = set()
        l_ops: set[str] = set()
        entries = pub_fns[name]
        aarch64_entries = [e for e in entries if e[1].startswith("aarch64/")]
        chosen = aarch64_entries if aarch64_entries else entries
        for body, rel in chosen:
            for lm in re.finditer(r'link_name\s*=\s*"(llvm\.[^"]+)"', body):
                lnk = lm.group(1)
                if not lnk.startswith("llvm.arm."):
                    l_ops.add(lnk)
            body_nc = re.sub(r"//.*", "", body)
            body_nc = body_nc[body_nc.index("{") :] if "{" in body_nc else body_nc
            for s in re.findall(r"\b(simd_[a-z0-9_]+)\b", body_nc):
                s_ops.add(s)
            for tok in re.findall(
                r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:::<[^>]*>)?\s*\(", body_nc
            ):
                if (rel, tok) in mod_externs:
                    l_ops |= mod_externs[(rel, tok)]
                elif tok in global_externs and not tok.startswith("v"):
                    l_ops |= global_externs[tok]
                elif tok in pub_fns and tok != name:
                    s2, l2 = classify_fn(tok, seen)
                    s_ops |= s2
                    l_ops |= l2
        return s_ops, l_ops

    cargo_reg = Path.home() / ".cargo" / "registry" / "src"
    per_crate: dict[str, dict] = {}
    total_calls: dict[str, int] = {}

    for c in PRODUCTION_CRATES:
        matches = glob.glob(str(cargo_reg / "*" / c))
        if not matches:
            continue
        p = Path(matches[0])
        rs_files = [
            Path(r) / f
            for r, _, fs in os.walk(p)
            for f in sorted(fs)
            if f.endswith(".rs")
        ]
        c_calls: dict[str, int] = {}
        for rf in rs_files:
            txt_nc = re.sub(r"//.*", "", rf.read_text(errors="ignore"))
            for tok in re.findall(
                r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:::<[^>]*>)?\s*\(", txt_nc
            ):
                if tok in pub_fns:
                    c_calls[tok] = c_calls.get(tok, 0) + 1
                    total_calls[tok] = total_calls.get(tok, 0) + 1

        c_tot = sum(c_calls.values())
        c_before = 0
        c_after = 0
        for fn_name, cnt in c_calls.items():
            s_ops, l_ops = classify_fn(fn_name)
            miss_s = s_ops - portable_simd_set
            miss_before = [l for l in l_ops if not is_base_lean_miri_supported(l)]
            miss_after = [
                l
                for l in l_ops
                if not (is_base_lean_miri_supported(l) or l in ext_names)
            ]
            if not miss_s and not miss_before:
                c_before += cnt
            if not miss_s and not miss_after:
                c_after += cnt
        per_crate[c] = {
            "total_sites": c_tot,
            "distinct_intrinsics": len(c_calls),
            "covered_before": c_before,
            "covered_after": c_after,
        }

    covered_before = 0
    covered_after = 0
    pure_portable_simd_sites = 0
    previously_unsupported_breakdown = []
    remaining_after_ext = []

    for fn_name, cnt in sorted(total_calls.items()):
        s_ops, l_ops = classify_fn(fn_name)
        miss_s = sorted(s_ops - portable_simd_set)
        miss_before = sorted(l for l in l_ops if not is_base_lean_miri_supported(l))
        miss_after = sorted(
            l
            for l in l_ops
            if not (is_base_lean_miri_supported(l) or l in ext_names)
        )
        if not l_ops and not miss_s:
            pure_portable_simd_sites += cnt
        if not miss_s and not miss_before:
            covered_before += cnt
        else:
            previously_unsupported_breakdown.append(
                {
                    "intrinsic": fn_name,
                    "sites": cnt,
                    "llvm_links": miss_before,
                    "closed_by_ext": len(miss_after) == 0,
                }
            )
        if not miss_s and not miss_after:
            covered_after += cnt
        else:
            remaining_after_ext.append(
                {"intrinsic": fn_name, "sites": cnt, "missing_llvm": miss_after}
            )

    tot = sum(total_calls.values())
    base_nonsve = sorted(l for l in all_nonsve_links if is_base_lean_miri_supported(l))
    after_nonsve = sorted(
        l
        for l in all_nonsve_links
        if is_base_lean_miri_supported(l) or l in ext_names
    )

    return {
        "toolchain": toolchain,
        "stdarch_pub_fn_count": len(pub_fns),
        "stdarch_distinct_llvm_aarch64_all": len(all_aarch64_links),
        "stdarch_distinct_llvm_aarch64_non_sve": len(all_nonsve_links),
        "stdarch_non_sve_supported_before": len(base_nonsve),
        "stdarch_non_sve_supported_after_ext": len(after_nonsve),
        "ext_supported_llvm_aarch64_count": len(ext_names),
        "crate_benchmark": {
            "crate_count": len(per_crate),
            "total_aarch64_sites": tot,
            "distinct_called_intrinsics": len(total_calls),
            "pure_portable_simd_sites": pure_portable_simd_sites,
            "covered_before_sites": covered_before,
            "covered_before_pct": round(100.0 * covered_before / max(1, tot), 2),
            "unsupported_before_sites": tot - covered_before,
            "unsupported_before_pct": round(
                100.0 * (tot - covered_before) / max(1, tot), 2
            ),
            "covered_after_ext_sites": covered_after,
            "covered_after_ext_pct": round(100.0 * covered_after / max(1, tot), 2),
            "remaining_after_ext": remaining_after_ext,
            "previously_unsupported_breakdown": previously_unsupported_breakdown,
            "per_crate": per_crate,
        },
    }


REPLAY_EXT_DRIVER = r"""import Lean
import Lean.Replay

open Lean

def renderArr (xs : Array String) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map fun s => s!"\"{s}\"") ++ "]"

def collectAxioms (env : Environment) (roots : Array Name) : Array String := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut work := roots.toList
  let mut axs : Std.HashSet String := {}
  while !work.isEmpty do
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if !visited.contains c then
        visited := visited.insert c
        if let some ci := env.find? c then
          match ci with
          | .axiomInfo _ => axs := axs.insert c.toString
          | _ =>
            for dep in ci.getUsedConstantsAsSet do
              if !visited.contains dep then
                work := dep :: work
  return axs.toArray.qsort (· < ·)

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let forbiddenConsts : Array Name := #[
    `sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler
  ]
  let baseInit ← importModules #[
    { module := `Init.Core, importAll := true },
    { module := `Init.Data.BitVec.Basic, importAll := true },
    { module := `Init.Data.BitVec.Lemmas, importAll := true },
    { module := `Init.Data.List.Basic, importAll := true },
    { module := `Init.Data.Nat.Basic, importAll := true }
  ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

  let tLoad0 ← IO.monoMsNow
  let envExt ← importModules #[
    { module := `IntrinsicAarch64Ext, importAll := true }
  ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let loadMs := (← IO.monoMsNow) - tLoad0

  let mut unsafeConsts : Array String := #[]
  let mut partialConsts : Array String := #[]
  let mut axiomConsts : Array String := #[]
  let mut opaqueConsts : Array String := #[]
  let mut forbiddenRefs : Array String := #[]
  let mut delta : Std.HashMap Name ConstantInfo := {}

  for (cname, cinfo) in envExt.constants.toList do
    if !baseInit.constants.contains cname then
      delta := delta.insert cname cinfo
      if cinfo.isUnsafe then unsafeConsts := unsafeConsts.push cname.toString
      if cinfo.isPartial then partialConsts := partialConsts.push cname.toString
      match cinfo with
      | .axiomInfo _ => axiomConsts := axiomConsts.push cname.toString
      | .opaqueInfo _ => opaqueConsts := opaqueConsts.push cname.toString
      | _ => pure ()
      let used := cinfo.getUsedConstantsAsSet
      for fc in forbiddenConsts do
        if used.contains fc then
          forbiddenRefs := forbiddenRefs.push s!"{cname}->{fc}"

  let tRep0 ← IO.monoMsNow
  let _ ← baseInit.toKernelEnv.replay delta
  let replayMs := (← IO.monoMsNow) - tRep0

  let axs := collectAxioms envExt #[
    `IntrinsicAarch64Ext.evalAarch64Ext,
    `IntrinsicAarch64Ext.fips197_arm_round1_matches_x86_vaesenc,
    `IntrinsicAarch64Ext.fips180_4_sha512h2_abc_round01_matches_qemu,
    `IntrinsicAarch64Ext.neon_uaddlv_v16i8_max_sum_4080,
    `IntrinsicAarch64Ext.neon_ushl_v16i8_negative_shifts_right_and_saturates,
    `IntrinsicAarch64Ext.neon_pmull_v8i16_gf2_specimen
  ]
  IO.println "{"
  IO.println s!"  \"load_private_ms\": {loadMs},"
  IO.println s!"  \"delta_consts\": {delta.size},"
  IO.println s!"  \"replay_ms\": {replayMs},"
  IO.println s!"  \"unsafe_consts\": {renderArr unsafeConsts},"
  IO.println s!"  \"partial_consts\": {renderArr partialConsts},"
  IO.println s!"  \"axiom_consts\": {renderArr axiomConsts},"
  IO.println s!"  \"opaque_consts\": {renderArr opaqueConsts},"
  IO.println s!"  \"forbidden_refs\": {renderArr forbiddenRefs},"
  IO.println s!"  \"transitive_axioms\": {renderArr axs}"
  IO.println "}"
  return 0
"""


def compile_and_replay_ext(
    ext_lean: Path, lean_bin: str, lean_wrapper: str | None
) -> dict:
    prefix = [lean_wrapper, "--"] if lean_wrapper else []
    with tempfile.TemporaryDirectory() as tmp:
        tmp_p = Path(tmp)
        local_lean = tmp_p / "IntrinsicAarch64Ext.lean"
        local_lean.write_bytes(ext_lean.read_bytes())
        olean = tmp_p / "IntrinsicAarch64Ext.olean"

        t0 = time.monotonic()
        r = subprocess.run(
            [
                *prefix,
                lean_bin,
                "-R",
                str(tmp_p),
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-o",
                str(olean),
                str(local_lean),
            ],
            cwd=tmp,
            capture_output=True,
            text=True,
            check=True,
        )
        compile_ms = round((time.monotonic() - t0) * 1000.0, 2)

        drv = tmp_p / "ReplayExt.lean"
        drv.write_text(REPLAY_EXT_DRIVER, encoding="utf-8")
        env = os.environ.copy()
        lean_resolved = Path(lean_bin).resolve()
        env["LEAN_PATH"] = str(tmp_p)
        env["LEAN_SYSROOT"] = str(lean_resolved.parent.parent)
        env["PATH"] = f"{lean_resolved.parent}:{env.get('PATH', '')}"
        r_rep = subprocess.run(
            [*prefix, lean_bin, "--run", str(drv)],
            cwd=tmp,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        rep_json = json.loads(r_rep.stdout)
        return {
            "compile_ms": compile_ms,
            "olean_bytes": olean.stat().st_size,
            "zero_warnings_and_errors": (r.stdout.strip() == "" and r.stderr.strip() == ""),
            "private_kernel_replay": rep_json,
        }


QEMU_FIPS_RUST_HARNESS = r"""#![no_std]
#![no_main]
#![allow(suspicious_runtime_symbol_definitions)]
use core::arch::aarch64::*;
use core::arch::asm;
use core::mem::transmute;

#[unsafe(no_mangle)]
pub extern "C" fn rust_eh_personality() {}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe {
        sys_write(b"PANIC\n");
        asm!("mov x8, #94\n svc #0", in("x0") 101usize, options(noreturn));
    }
}

unsafe fn sys_write(buf: &[u8]) {
    asm!(
        "mov x8, #64\n svc #0",
        in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(),
        lateout("x0") _, out("x8") _, options(nostack)
    );
}

unsafe fn print_u128(label: &[u8], val: u128) {
    sys_write(label);
    let mut out = [0u8; 35];
    out[0] = b'0'; out[1] = b'x';
    let hex = b"0123456789abcdef";
    let mut i = 0;
    while i < 32 {
        out[2 + i] = hex[((val >> ((31 - i) * 4)) & 0xf) as usize];
        i += 1;
    }
    out[34] = b'\n';
    sys_write(&out);
}

#[target_feature(enable = "neon,aes,sha3")]
unsafe fn run_checks() {
    // 1. Full 10-round NIST FIPS-197 Appendix B AES-128 Encryption & Decryption
    const RCON: [u32; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];
    let key0: u128 = 0x3c4fcf098815f7aba6d2ae2816157e2b;
    let mut cols = [0u32; 44];
    cols[0] = (key0 & 0xffff_ffff) as u32;
    cols[1] = ((key0 >> 32) & 0xffff_ffff) as u32;
    cols[2] = ((key0 >> 64) & 0xffff_ffff) as u32;
    cols[3] = ((key0 >> 96) & 0xffff_ffff) as u32;
    let mut wi = 4usize;
    while wi < 44 {
        let mut w = cols[wi - 1];
        if wi % 4 == 0 {
            let sub = vgetq_lane_u32::<0>(vreinterpretq_u32_u8(vaeseq_u8(
                vreinterpretq_u8_u32(vdupq_n_u32(w)),
                vdupq_n_u8(0),
            )));
            w = sub.rotate_right(8) ^ RCON[wi / 4 - 1];
        }
        cols[wi] = cols[wi - 4] ^ w;
        wi += 1;
    }
    let mut rks = [0u128; 11];
    let mut ri = 0usize;
    while ri < 11 {
        rks[ri] = (cols[4 * ri] as u128)
            | ((cols[4 * ri + 1] as u128) << 32)
            | ((cols[4 * ri + 2] as u128) << 64)
            | ((cols[4 * ri + 3] as u128) << 96);
        ri += 1;
    }
    let pt: u128 = 0x340737e0a29831318d305a88a8f64332;
    let mut b: uint8x16_t = transmute(pt);
    let mut r = 0;
    while r < 9 {
        b = vaesmcq_u8(vaeseq_u8(b, transmute(rks[r])));
        r += 1;
    }
    b = veorq_u8(vaeseq_u8(b, transmute(rks[9])), transmute(rks[10]));
    let ct: u128 = transmute(b);
    // Expected FIPS-197 Appendix B ciphertext: 39 25 84 1d 02 dc 09 fb dc 1185 97 19 6a 0b 32
    assert_eq!(ct, 0x320b6a19978511dcfb09dc021d842539u128);

    // Equivalent Inverse Cipher round keys via vaesimcq_u8
    let mut dec_b: uint8x16_t = b;
    dec_b = vaesimcq_u8(vaesdq_u8(dec_b, transmute(rks[10])));
    let mut dr = 9;
    while dr >= 2 {
        let eq_key = vaesimcq_u8(transmute(rks[dr]));
        dec_b = vaesimcq_u8(vaesdq_u8(dec_b, eq_key));
        dr -= 1;
    }
    dec_b = veorq_u8(vaesdq_u8(dec_b, vaesimcq_u8(transmute(rks[1]))), transmute(rks[0]));
    let recovered_pt: u128 = transmute(dec_b);
    assert_eq!(recovered_pt, pt);
    print_u128(b"fips197_aes128_ct=", ct);
    print_u128(b"fips197_aes128_recovered_pt=", recovered_pt);

    // 2. Full 80-round NIST FIPS-180-4 SHA-512("abc") via vsha512{h,h2,su0,su1}q_u64
    const K512: [u64; 80] = [
        0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
        0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
        0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
        0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
        0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
        0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
        0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
        0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
        0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
        0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
        0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
        0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
        0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
        0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
        0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
        0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
        0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
        0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
        0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
        0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
    ];
    let ab0: uint64x2_t = transmute([0x6a09e667f3bcc908u64, 0xbb67ae8584caa73b]);
    let cd0: uint64x2_t = transmute([0x3c6ef372fe94f82bu64, 0xa54ff53a5f1d36f1]);
    let ef0: uint64x2_t = transmute([0x510e527fade682d1u64, 0x9b05688c2b3e6c1f]);
    let gh0: uint64x2_t = transmute([0x1f83d9abfb41bd6bu64, 0x5be0cd19137e2179]);
    let (mut ab, mut cd, mut ef, mut gh) = (ab0, cd0, ef0, gh0);

    let mut s: [uint64x2_t; 8] = [transmute([0u64, 0u64]); 8];
    s[0] = transmute([0x6162638000000000u64, 0]);
    s[7] = transmute([0u64, 24]);

    let rk_pair = |idx: usize| -> uint64x2_t { unsafe { transmute([K512[idx], K512[idx + 1]]) } };

    let mut t = 0usize;
    while t < 80 {
        if t >= 16 {
            let idx = (t / 2) % 8;
            let s_next = s[(idx + 1) % 8];
            let s_prev = s[(idx + 7) % 8];
            let s_mid = vextq_u64::<1>(s[(idx + 4) % 8], s[(idx + 5) % 8]);
            s[idx] = vsha512su1q_u64(vsha512su0q_u64(s[idx], s_next), s_prev, s_mid);
        }
        let w_pair = s[(t / 2) % 8];
        let init_sum = vaddq_u64(w_pair, rk_pair(t));
        match (t / 2) % 4 {
            0 => {
                let sum = vaddq_u64(vextq_u64::<1>(init_sum, init_sum), gh);
                let inter = vsha512hq_u64(sum, vextq_u64::<1>(ef, gh), vextq_u64::<1>(cd, ef));
                gh = vsha512h2q_u64(inter, cd, ab);
                cd = vaddq_u64(cd, inter);
            }
            1 => {
                let sum = vaddq_u64(vextq_u64::<1>(init_sum, init_sum), ef);
                let inter = vsha512hq_u64(sum, vextq_u64::<1>(cd, ef), vextq_u64::<1>(ab, cd));
                ef = vsha512h2q_u64(inter, ab, gh);
                ab = vaddq_u64(ab, inter);
            }
            2 => {
                let sum = vaddq_u64(vextq_u64::<1>(init_sum, init_sum), cd);
                let inter = vsha512hq_u64(sum, vextq_u64::<1>(ab, cd), vextq_u64::<1>(gh, ab));
                cd = vsha512h2q_u64(inter, gh, ef);
                gh = vaddq_u64(gh, inter);
            }
            _ => {
                let sum = vaddq_u64(vextq_u64::<1>(init_sum, init_sum), ab);
                let inter = vsha512hq_u64(sum, vextq_u64::<1>(gh, ab), vextq_u64::<1>(ef, gh));
                ab = vsha512h2q_u64(inter, ef, cd);
                ef = vaddq_u64(ef, inter);
            }
        }
        t += 2;
    }
    ab = vaddq_u64(ab, ab0);
    cd = vaddq_u64(cd, cd0);
    ef = vaddq_u64(ef, ef0);
    gh = vaddq_u64(gh, gh0);

    let ab_words: [u64; 2] = transmute(ab);
    let cd_words: [u64; 2] = transmute(cd);
    let ef_words: [u64; 2] = transmute(ef);
    let gh_words: [u64; 2] = transmute(gh);
    // NIST FIPS-180-4 SHA-512("abc") = ddaf35a193617aba cc417349ae204131 12e6fa4e89a97ea2 0a9eeee64b55d39a 2192992a274fc1a8 36ba3c23a3feebbd 454d4423643ce80e 2a9ac94fa54ca49f
    assert_eq!(ab_words[0], 0xddaf35a193617abau64);
    assert_eq!(ab_words[1], 0xcc417349ae204131u64);
    assert_eq!(cd_words[0], 0x12e6fa4e89a97ea2u64);
    assert_eq!(cd_words[1], 0x0a9eeee64b55d39au64);
    assert_eq!(ef_words[0], 0x2192992a274fc1a8u64);
    assert_eq!(ef_words[1], 0x36ba3c23a3feebbdu64);
    assert_eq!(gh_words[0], 0x454d4423643ce80eu64);
    assert_eq!(gh_words[1], 0x2a9ac94fa54ca49fu64);
    print_u128(b"fips180_4_sha512_abc_ab=", transmute(ab));
    print_u128(b"fips180_4_sha512_abc_gh=", transmute(gh));

    // 3. NEON uaddlv, ushl, sshl, pmull checks matching IntrinsicAarch64Ext theorems
    let all_ff: uint8x16_t = vdupq_n_u8(0xff);
    assert_eq!(vaddlvq_u8(all_ff), 4080u16);
    let mut sh_a = [0u8; 16]; sh_a[0] = 0x84; sh_a[1] = 0x84;
    let mut sh_b = [0i8; 16]; sh_b[0] = -2;   sh_b[1] = 8;
    let u_out: [u8; 16] = transmute(vshlq_u8(transmute(sh_a), transmute(sh_b)));
    assert_eq!(u_out[0], 0x21);
    assert_eq!(u_out[1], 0x00);
    sh_b[1] = -128;
    let s_out: [u8; 16] = transmute(vshlq_s8(transmute(sh_a), transmute(sh_b)));
    assert_eq!(s_out[0], 0xe1);
    assert_eq!(s_out[1], 0xff);
    let p_in: [u8; 8] = [0x83, 0, 0, 0, 0, 0, 0, 0];
    let p_out: [u16; 8] = transmute(vmull_p8(transmute(p_in), transmute(p_in)));
    assert_eq!(p_out[0], 0x4005u16);
    print_u128(b"neon_ext_assertions_passed=", 1);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    run_checks();
    asm!("mov x8, #93\n svc #0", in("x0") 0usize, options(noreturn));
}
"""


def run_qemu_crypto_neon_crosscheck(toolchain: str, qemu_bin: str) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        rs = Path(tmp) / "fips_check.rs"
        exe = Path(tmp) / "fips_check"
        rs.write_text(QEMU_FIPS_RUST_HARNESS, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                f"+{toolchain}",
                "--target=aarch64-unknown-linux-gnu",
                "-Clinker-flavor=ld.lld",
                "-Clinker=rust-lld",
                "-Crelocation-model=static",
                "-Cpanic=abort",
                "-O",
                str(rs),
                "-o",
                str(exe),
            ],
            check=True,
        )
        r = subprocess.run(
            [qemu_bin, "-cpu", "max", str(exe)],
            capture_output=True,
            text=True,
            timeout=20,
            check=True,
        )
        kv = {}
        for line in r.stdout.strip().splitlines():
            if "=" in line:
                k, v = line.split("=", 1)
                kv[k.strip()] = v.strip()
        return {"qemu_returncode": r.returncode, "vectors": kv}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vendor-dir", type=Path, required=True)
    parser.add_argument(
        "--ext-lean",
        type=Path,
        default=Path(__file__).resolve().with_name("IntrinsicAarch64Ext.lean"),
    )
    parser.add_argument("--rustc-toolchain", default="1.99.1")
    parser.add_argument("--lean-bin", default="lean")
    parser.add_argument("--lean-wrapper", default=None)
    parser.add_argument("--qemu-bin", default="qemu-aarch64")
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path(__file__)
        .resolve()
        .with_name("probe_lean_miri_aarch64_audit_results.json"),
    )
    args = parser.parse_args()

    pin_json = json.loads(
        (args.vendor_dir / "UPSTREAM_PIN.json").read_text(encoding="utf-8")
    )
    vendor_scans = {
        "Miri/Interpreter/IntrinsicSimd.lean": scan_lean_file(
            args.vendor_dir / "Miri/Interpreter/IntrinsicSimd.lean"
        ),
        "Miri/Interpreter/IntrinsicCrypto.lean": scan_lean_file(
            args.vendor_dir / "Miri/Interpreter/IntrinsicCrypto.lean"
        ),
        "Miri/Interpreter/IntrinsicArchitecture.lean": scan_lean_file(
            args.vendor_dir / "Miri/Interpreter/IntrinsicArchitecture.lean"
        ),
        "support/IntrinsicAarch64Ext.lean": scan_lean_file(args.ext_lean),
    }

    ext_names = extract_ext_supported_names(args.ext_lean)
    cov = audit_stdarch_and_12crates(args.rustc_toolchain, args.vendor_dir, ext_names)
    lean_audit = compile_and_replay_ext(
        args.ext_lean, args.lean_bin, args.lean_wrapper
    )
    qemu_check = run_qemu_crypto_neon_crosscheck(args.rustc_toolchain, args.qemu_bin)

    out = {
        "upstream_pin": {
            "repository": pin_json.get("repository", "proofs-rs/lean-miri"),
            "commit": pin_json.get("commit"),
            "lean_toolchain": pin_json.get("lean_toolchain"),
            "pinned_module_count": len(pin_json.get("modules", [])),
        },
        "source_scans": vendor_scans,
        "coverage_audit": cov,
        "intrinsic_aarch64_ext_lean_audit": lean_audit,
        "qemu_aarch64_fips_and_neon_crosscheck": qemu_check,
    }
    args.out_json.write_text(
        json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(out["coverage_audit"]["crate_benchmark"], indent=2))
    print(json.dumps(out["intrinsic_aarch64_ext_lean_audit"], indent=2))
    print(json.dumps(out["qemu_aarch64_fips_and_neon_crosscheck"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
