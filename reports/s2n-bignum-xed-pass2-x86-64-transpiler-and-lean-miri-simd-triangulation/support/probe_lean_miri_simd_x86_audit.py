#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Source, coverage, compilation, and standalone kernel-replay audit of
proofs-rs/lean-miri IntrinsicSimd and IntrinsicX86 under Lean v4.34.1.

All temporary builds and kernel-replay harnesses execute inside
tempfile.TemporaryDirectory() and invoke Lean strictly through the configured
cgroup/slot wrapper when provided.
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import shutil
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

TARGET_MODULES = [
    "Miri.Interpreter.IntrinsicSimd",
    "Miri.Interpreter.IntrinsicCrypto",
    "Miri.Interpreter.IntrinsicArchitecture",
    "Miri.Interpreter.IntrinsicX86.Basic",
    "Miri.Interpreter.IntrinsicX86.Float",
    "Miri.Interpreter.IntrinsicX86.Integer",
    "Miri.Interpreter.IntrinsicX86.Chunks",
    "Miri.Interpreter.IntrinsicX86.Strings",
    "Miri.Interpreter.IntrinsicX86.Aes",
    "Miri.Interpreter.IntrinsicX86.Crypto",
    "Miri.Interpreter.IntrinsicX86.Extras",
    "Miri.Interpreter.IntrinsicX86.DispatchFloat",
    "Miri.Interpreter.IntrinsicX86.DispatchVector",
    "Miri.Interpreter.IntrinsicX86",
    "Miri.Interpreter.Math.Bindings",
    "Miri.Interpreter.IntrinsicVectorMachine",
]


def strip_lean_comments(text: str) -> str:
    # Remove nested /- ... -/ and line -- ... comments for token scanning
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
        "by_tactic_blocks": len(re.findall(r":=\s*by\b", clean)),
    }
    defs = len(re.findall(r"^\s*(?:private\s+|protected\s+)?(?:def|abbrev|structure|inductive|theorem)\s+", clean, re.M))
    return {
        "lines": len(text.splitlines()),
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "top_level_decls": defs,
        "constructs": constructs,
    }


def extract_lean_miri_supported_names(vendor_dir: Path) -> dict:
    simd_txt = (vendor_dir / "Miri/Interpreter/IntrinsicSimd.lean").read_text()
    portable_simd = sorted(set(re.findall(r'"(simd_[a-z0-9_]+)"', simd_txt)))

    # Collect exact llvm.x86.* names recognized across IntrinsicX86/*.lean and IntrinsicX86.lean
    x86_names: set[str] = set()
    # From IntrinsicX86.lean
    for s in ["addcarry.32", "addcarry.64", "subborrow.32", "subborrow.64", "sse2.pause",
              "pclmulqdq", "pclmulqdq.256", "pclmulqdq.512"]:
        x86_names.add(f"llvm.x86.{s}")
    # From Extras.lean bmi
    for op in ["bextr", "bzhi", "pext", "pdep"]:
        for w in ["32", "64"]:
            x86_names.add(f"llvm.x86.bmi.{op}.{w}")
    # From Crypto.lean gfni, sha, aesni
    for s in ["vgf2p8affineqb.128", "vgf2p8affineqb.256", "vgf2p8affineqb.512",
              "vgf2p8affineinvqb.128", "vgf2p8affineinvqb.256", "vgf2p8affineinvqb.512",
              "vgf2p8mulb.128", "vgf2p8mulb.256", "vgf2p8mulb.512"]:
        x86_names.add(f"llvm.x86.{s}")
    for s in ["256rnds2", "256msg1", "256msg2"]:
        x86_names.add(f"llvm.x86.sha{s}")
    for s in ["aesimc", "aeskeygenassist", "aesdec", "aesdec.256", "aesdec.512",
              "aesdeclast", "aesdeclast.256", "aesdeclast.512",
              "aesenc", "aesenc.256", "aesenc.512",
              "aesenclast", "aesenclast.256", "aesenclast.512"]:
        x86_names.add(f"llvm.x86.aesni.{s}")
    # From Strings.lean + IntrinsicX86.lean sse42
    str_txt = (vendor_dir / "Miri/Interpreter/IntrinsicX86/Strings.lean").read_text()
    for s in re.findall(r'"(pcmp[ie]str[a-z0-9]+)"', str_txt):
        x86_names.add(f"llvm.x86.sse42.{s}")
    for s in ["crc32.32.8", "crc32.32.16", "crc32.32.32", "crc32.64.64"]:
        x86_names.add(f"llvm.x86.sse42.{s}")
    # From DispatchFloat.lean
    df_txt = (vendor_dir / "Miri/Interpreter/IntrinsicX86/DispatchFloat.lean").read_text()
    for s in re.findall(r'"((?:sse|sse2|sse41|avx)\.[a-z0-9.]+)"', df_txt):
        if s not in ("sse2.", "sse.min", "sse2.min", "avx.min", "sse.rsqrt", "avx.rsqrt",
                     "sse2.cvtt", "avx.cvtt", "sse.cvtt"):
            x86_names.add(f"llvm.x86.{s}")
    # From DispatchVector.lean
    dv_txt = (vendor_dir / "Miri/Interpreter/IntrinsicX86/DispatchVector.lean").read_text()
    for m in re.finditer(r'\|\s*"([a-z0-9.]+)"\s*=>\s*some', dv_txt):
        x86_names.add(f"llvm.x86.{m.group(1)}")

    return {
        "portable_simd_count": len(portable_simd),
        "portable_simd_names": portable_simd,
        "llvm_x86_count": len(x86_names),
        "llvm_x86_names": sorted(x86_names),
        "llvm_generic_names": ["llvm.prefetch.p0", "llvm.ctpop.v*"],
    }


def parse_stdarch_and_check_coverage(toolchain: str, supported: dict) -> dict:
    sysroot = subprocess.check_output(
        ["rustup", "run", toolchain, "rustc", "--print", "sysroot"], text=True
    ).strip()
    x86_dir = Path(sysroot) / "lib/rustlib/src/rust/library/stdarch/crates/core_arch/src/x86"
    llvm_links: dict[str, str] = {}
    fn_bodies: dict[str, str] = {}

    for root, _, files in os.walk(x86_dir):
        for f in sorted(files):
            if not f.endswith(".rs"):
                continue
            txt = (Path(root) / f).read_text(errors="ignore")
            for m in re.finditer(
                r'#\[link_name\s*=\s*"(llvm\.[^"]+)"\]\s*(?:pub\s+)?fn\s+([a-zA-Z0-9_]+)',
                txt,
            ):
                llvm_links[m.group(2)] = m.group(1)
            lines = txt.splitlines()
            i = 0
            while i < len(lines):
                m = re.search(
                    r"\bpub\s+(?:const\s+)?(?:unsafe\s+)?fn\s+(_mm(?:256|512)?_[a-zA-Z0-9_]+)",
                    lines[i],
                )
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
                    fn_bodies[name] = "\n".join(buf)
                    i = j + 1
                else:
                    i += 1

    def classify(name: str, seen: set[str] | None = None) -> tuple[set[str], set[str]]:
        if seen is None:
            seen = set()
        if name in seen or name not in fn_bodies:
            return set(), set()
        seen.add(name)
        body = re.sub(r"//.*", "", fn_bodies[name])
        body = body[body.index("{") :] if "{" in body else body
        s_ops = set(re.findall(r"\b(simd_[a-z0-9_]+)\b", body))
        l_ops = set()
        for tok in re.findall(r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:::<[^>]*>)?\s*\(", body):
            if tok in llvm_links:
                l_ops.add(llvm_links[tok])
            elif tok.startswith("_mm") and tok != name:
                s2, l2 = classify(tok, seen)
                s_ops |= s2
                l_ops |= l2
        return s_ops, l_ops

    simd_set = set(supported["portable_simd_names"])
    x86_set = set(supported["llvm_x86_names"])

    def is_llvm_supported(op: str) -> bool:
        if op == "llvm.prefetch.p0" or op.startswith("llvm.ctpop.v"):
            return True
        return op in x86_set

    distinct_stdarch_links = sorted(set(llvm_links.values()))
    supported_stdarch_links = [op for op in distinct_stdarch_links if is_llvm_supported(op)]

    # Scan the 12 crates if present in ~/.cargo/registry/src
    cargo_reg = Path.home() / ".cargo" / "registry" / "src"
    total_calls: dict[str, int] = {}
    for c in PRODUCTION_CRATES:
        matches = glob.glob(str(cargo_reg / "*" / c))
        if not matches:
            continue
        p = Path(matches[0])
        rs_files = [Path(r) / f for r, _, fs in os.walk(p) for f in fs if f.endswith(".rs")]
        local_defs = set()
        for rf in rs_files:
            txt_nc = re.sub(r"//.*", "", rf.read_text(errors="ignore"))
            for d in re.findall(r"\bfn\s+(_mm(?:256|512)?_[a-z0-9_]+)\b", txt_nc):
                local_defs.add(d)
        for rf in rs_files:
            txt_nc = re.sub(r"//.*", "", rf.read_text(errors="ignore"))
            for m in re.findall(r"\b(_mm(?:256|512)?_[a-z0-9_]+)\s*(?:::<[^>]*>)?\s*\(", txt_nc):
                if m not in local_defs:
                    total_calls[m] = total_calls.get(m, 0) + 1

    covered_sites = 0
    uncovered_details = []
    covered_with_closure_only = 0
    for fn_name, cnt in sorted(total_calls.items()):
        s_ops, l_ops = classify(fn_name)
        missing_s = sorted(s_ops - simd_set)
        missing_l = sorted(op for op in l_ops if not is_llvm_supported(op))
        if not missing_s and not missing_l:
            covered_sites += cnt
            # Without IntrinsicX86 wired in, only pure MIR + portable simd_* + prefetch/ctpop work:
            if all(op == "llvm.prefetch.p0" or op.startswith("llvm.ctpop.v") for op in l_ops):
                covered_with_closure_only += cnt
        else:
            uncovered_details.append({
                "fn": fn_name,
                "sites": cnt,
                "missing_simd": missing_s,
                "missing_llvm": missing_l,
            })

    total_sites = sum(total_calls.values())
    return {
        "toolchain": toolchain,
        "stdarch_fn_count": len(fn_bodies),
        "stdarch_distinct_llvm_links": len(distinct_stdarch_links),
        "stdarch_supported_llvm_links": len(supported_stdarch_links),
        "stdarch_supported_llvm_pct": round(100.0 * len(supported_stdarch_links) / max(1, len(distinct_stdarch_links)), 2),
        "crate_corpus_total_sites": total_sites,
        "crate_corpus_covered_by_160_closure_only": covered_with_closure_only,
        "crate_corpus_covered_by_160_closure_pct": round(100.0 * covered_with_closure_only / max(1, total_sites), 2),
        "crate_corpus_covered_with_intrinsic_x86": covered_sites,
        "crate_corpus_covered_with_intrinsic_x86_pct": round(100.0 * covered_sites / max(1, total_sites), 2),
        "crate_corpus_uncovered": uncovered_details,
    }


def get_topological_closure(vendor_dir: Path, roots: list[str]) -> list[str]:
    visited: list[str] = []
    seen: set[str] = set()

    def get_imports(mod: str) -> list[str]:
        p = vendor_dir / (mod.replace(".", "/") + ".lean")
        if not p.exists():
            return []
        res = []
        for line in p.read_text().splitlines():
            m = re.match(r"^\s*import\s+(Miri[A-Za-z0-9_.]*)", line)
            if m:
                res.append(m.group(1))
        return res

    def dfs(mod: str) -> None:
        if mod in seen:
            return
        seen.add(mod)
        for dep in get_imports(mod):
            dfs(dep)
        visited.append(mod)

    for r in roots:
        dfs(r)
    return visited


EDGE_CASE_THEOREMS_LEAN = r"""import Miri.Interpreter.IntegerOps
import Miri.Interpreter.IntrinsicSimd
import Miri.Interpreter.IntrinsicCrypto
import Miri.Interpreter.IntrinsicX86.Aes
import Miri.Interpreter.IntrinsicX86.Integer

/-! ## Kernel-checked semantic edge-case theorems on actual `lean-miri` definitions -/

namespace EdgeCaseProofs
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- 1. NIST FIPS-197 Appendix B cipher round 1 vector against `Miri.Interpreter.IntrinsicX86.Aes.round`:
    Input block `32 43 f6 a8 88 5a 30 8d 31 31 98 a2 e0 37 07 34` XORed with cipher round 0 key
    `2b 7e 15 16 28 ae d2 a6 ab f7 15 88 09 cf 4f 3c` =
    `19 3d e3 be a0 f4 e2 2b 9a c6 8d 2a e9 f8 48 08` (little-endian `U128`:
    `0x0848f8e92a8dc69a2be2f4a0bee33d19`), cipher round 1 key
    `a0 fa fe 17 88 54 2c b1 23 a3 39 39 2a 6c 76 05` (little-endian `U128`:
    `0x05766c2a3939a323b12c548817fefaa0`), expected cipher round 1 output
    `a4 9c 7f f2 68 9f 35 2b 6b 5b ea 43 02 6a 50 49` (little-endian `U128`:
    `0x49506a0243ea5b6b2b359f68f27f9ca4`). -/
theorem aes_round_fips197_round1 :
    IntrinsicX86.Aes.round false
      (BitVec.ofNat 128 0x0848f8e92a8dc69a2be2f4a0bee33d19)
      (BitVec.ofNat 128 0x05766c2a3939a323b12c548817fefaa0) =
    BitVec.ofNat 128 0x49506a0243ea5b6b2b359f68f27f9ca4 := rfl

/-- 2. `aesimc` (`mixColumns true`) inverts `mixColumns false` on FIPS-197 state. -/
theorem aes_invMixColumns_roundtrip :
    IntrinsicX86.Aes.mixColumns true
      (IntrinsicX86.Aes.mixColumns false (BitVec.ofNat 128 0x0848f8e92a8dc69a2be2f4a0bee33d19)) =
    BitVec.ofNat 128 0x0848f8e92a8dc69a2be2f4a0bee33d19 := rfl

/-- 3. Portable `simd_shl` delegates to `IntegerOps.binary .ShlUnchecked`: shifting a 32-bit
    lane by `32` returns immediate Undefined Behavior (`shiftOverflow`). -/
theorem mir_simd_shl_ub_at_width_32 :
    let ty : Miri.Interpreter.IntegerType := ⟨Size.ofBytes 4, .u32⟩
    let lhs : Miri.Interpreter.IntegerValue := ⟨ScalarInt.ofUInt32 0x12345678, ty⟩
    let rhs : Miri.Interpreter.IntegerValue := ⟨ScalarInt.ofUInt32 32, ty⟩
    IntegerOps.binary .ShlUnchecked lhs rhs =
      .error (.undefinedBehavior (.shiftOverflow .ShlUnchecked 32 false)) := rfl

/-- 4. By contrast, `llvm.x86.{sse2,avx2}.psll.d` / `psllv.d` calls `IntrinsicX86.shiftScalar`:
    shifting a 32-bit lane by `32` (or `200`) succeeds without UB and saturates to `0`. -/
theorem x86_pslld_saturates_to_zero_at_32 :
    (IntrinsicX86.shiftScalar (P := CtfeProvenance) (S := Unit)
      (.fromScalarInt (.ofUInt32 0x12345678)) (Size.ofBytes 4) 32 .left).run () =
    .ok (.fromScalarInt (.ofUInt32 0)) () := rfl

theorem x86_psrad_clamps_sign_bit_at_32 :
    (IntrinsicX86.shiftScalar (P := CtfeProvenance) (S := Unit)
      (.fromScalarInt (.ofUInt32 0x80000000)) (Size.ofBytes 4) 32 .arithmeticRight).run () =
    .ok (.fromScalarInt (.ofUInt32 0xFFFFFFFF)) () := rfl

/-- 5. `carryless64` polynomial multiplication in GF(2)[x] (`pclmulqdq`). -/
theorem carryless64_crc_fold_specimen :
    IntrinsicCrypto.carryless64 0x8000000000000001 0x8000000000000001 =
    (BitVec.ofNat 128 0x40000000000000000000000000000001) := rfl

end EdgeCaseProofs
"""

REPLAY_DRIVER_LEAN = r"""import Lean.Elab.Import
import Lean.Replay

open Lean

def targetModules : Array Name := #[
  `Miri.Interpreter.IntrinsicSimd,
  `Miri.Interpreter.IntrinsicCrypto,
  `Miri.Interpreter.IntrinsicArchitecture,
  `Miri.Interpreter.IntrinsicX86.Basic,
  `Miri.Interpreter.IntrinsicX86.Float,
  `Miri.Interpreter.IntrinsicX86.Integer,
  `Miri.Interpreter.IntrinsicX86.Chunks,
  `Miri.Interpreter.IntrinsicX86.Strings,
  `Miri.Interpreter.IntrinsicX86.Aes,
  `Miri.Interpreter.IntrinsicX86.Crypto,
  `Miri.Interpreter.IntrinsicX86.Extras,
  `Miri.Interpreter.IntrinsicX86.DispatchFloat,
  `Miri.Interpreter.IntrinsicX86.DispatchVector,
  `Miri.Interpreter.IntrinsicX86,
  `Miri.Interpreter.Math.Bindings,
  `Miri.Interpreter.IntrinsicVectorMachine,
  `EdgeCaseTheorems
]

def forbiddenConsts : List Name := [
  ``sorryAx,
  `Lean.ofReduceBool,
  `Lean.ofReduceNat,
  `Lean.trustCompiler,
  `Lean.reduceBool,
  `Lean.reduceNat
]

def readVmHwmKb : IO Nat := do
  let txt ← IO.FS.readFile "/proc/self/status"
  for line in txt.splitOn "\n" do
    if line.startsWith "VmHWM:" then
      let parts := (line.drop 6).trimAscii.toString.splitOn " "
      for p in parts do
        if let some n := p.trimAscii.toString.toNat? then
          return n
  return 0

def renderArr (xs : Array String) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map fun s => s!"\"{s}\"") ++ "]"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot) [System.FilePath.mk "."]
  let mode := args.headD "x86"
  if mode == "simd" then
    let t0 ← IO.monoMsNow
    let basePreSimd ← importModules #[
      { module := `Miri.Interpreter.Cast, importAll := true },
      { module := `Miri.Interpreter.IntrinsicFloat, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let envSimdArch ← importModules #[
      { module := `Miri.Interpreter.IntrinsicArchitecture, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadSimdMs := (← IO.monoMsNow) - t0

    let mut simdDelta : Std.HashMap Name ConstantInfo := {}
    for (cname, cinfo) in envSimdArch.constants.toList do
      if !basePreSimd.constants.contains cname && !cinfo.isUnsafe && !cinfo.isPartial then
        simdDelta := simdDelta.insert cname cinfo
    let tRep1 ← IO.monoMsNow
    let _ ← basePreSimd.toKernelEnv.replay simdDelta
    let replaySimdMs := (← IO.monoMsNow) - tRep1
    let hwmKb ← readVmHwmKb
    IO.println "{"
    IO.println s!"  \"load_simd_private_ms\": {loadSimdMs},"
    IO.println s!"  \"replay_simd_arch_consts\": {simdDelta.size},"
    IO.println s!"  \"replay_simd_arch_ms\": {replaySimdMs},"
    IO.println s!"  \"replay_simd_vmhwm_kb\": {hwmKb}"
    IO.println "}"
    return 0
  else
    let tLoad0 ← IO.monoMsNow
    let env ← importModules #[
      { module := `Miri.Interpreter.IntrinsicVectorMachine, importAll := true },
      { module := `EdgeCaseTheorems, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let loadMs := (← IO.monoMsNow) - tLoad0

    let basePreX86 ← importModules #[
      { module := `Miri.Interpreter.IntrinsicArchitecture, importAll := true },
      { module := `Miri.Interpreter.PointerPlaceMachine, importAll := true },
      { module := `Miri.Interpreter.Math.Dispatch, importAll := true },
      { module := `Miri.Interpreter.Intrinsics, importAll := true }
    ] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

    let targetSet : Std.HashSet Name := Std.HashSet.ofArray targetModules
    let mut perModCounts : Std.HashMap Name Nat := {}
    let mut unsafeConsts : Array String := #[]
    let mut partialConsts : Array String := #[]
    let mut axiomConsts : Array String := #[]
    let mut opaqueConsts : Array String := #[]
    let mut forbiddenRefs : Array String := #[]

    for (cname, cinfo) in env.constants.toList do
      match env.getModuleIdxFor? cname with
      | some idx =>
        let mname := env.header.moduleNames[idx.toNat]!
        if targetSet.contains mname then
          perModCounts := perModCounts.insert mname ((perModCounts.getD mname 0) + 1)
          if cinfo.isUnsafe then unsafeConsts := unsafeConsts.push cname.toString
          if cinfo.isPartial then partialConsts := partialConsts.push cname.toString
          match cinfo with
          | .axiomInfo _ => axiomConsts := axiomConsts.push cname.toString
          | .opaqueInfo _ => opaqueConsts := opaqueConsts.push cname.toString
          | _ => pure ()
          let used := cinfo.getUsedConstantsAsSet
          for fc in forbiddenConsts do
            if used.contains fc then
              forbiddenRefs := forbiddenRefs.push s!"{mname}:{cname}->{fc}"
      | none => pure ()

    let collectAxioms (roots : Array Name) : IO (Array String) := do
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

    let simdAxioms ← collectAxioms #[`Miri.Interpreter.IntrinsicSimd.eval]
    let x86Axioms ← collectAxioms #[`Miri.Interpreter.IntrinsicX86.eval, `Miri.Interpreter.IntrinsicVectorMachine.bindX86]

    let mut x86Delta : Std.HashMap Name ConstantInfo := {}
    for (cname, cinfo) in env.constants.toList do
      if !basePreX86.constants.contains cname && !cinfo.isUnsafe && !cinfo.isPartial then
        x86Delta := x86Delta.insert cname cinfo
    let tRep2 ← IO.monoMsNow
    let _ ← basePreX86.toKernelEnv.replay x86Delta
    let replayX86Ms := (← IO.monoMsNow) - tRep2
    let hwmKb ← readVmHwmKb

    let mut modCountPairs : Array String := #[]
    for m in targetModules do
      let c := perModCounts.getD m 0
      modCountPairs := modCountPairs.push s!"\"{m}\": {c}"

    IO.println "{"
    IO.println s!"  \"load_private_ms\": {loadMs},"
    IO.println s!"  \"replay_x86_vm_consts\": {x86Delta.size},"
    IO.println s!"  \"replay_x86_vm_ms\": {replayX86Ms},"
    IO.println s!"  \"replay_x86_vmhwm_kb\": {hwmKb},"
    IO.println s!"  \"unsafe_consts\": {renderArr unsafeConsts},"
    IO.println s!"  \"partial_consts\": {renderArr partialConsts},"
    IO.println s!"  \"axiom_consts\": {renderArr axiomConsts},"
    IO.println s!"  \"opaque_consts\": {renderArr opaqueConsts},"
    IO.println s!"  \"forbidden_refs\": {renderArr forbiddenRefs},"
    IO.println s!"  \"simd_eval_transitive_axioms\": {renderArr simdAxioms},"
    IO.println s!"  \"x86_eval_transitive_axioms\": {renderArr x86Axioms},"
    IO.println ("  \"per_module_kernel_consts\": {" ++ String.intercalate ", " modCountPairs.toList ++ "}")
    IO.println "}"
    return 0
"""


def compile_and_replay_miri_closure(
    vendor_dir: Path, lean_bin: str, lean_wrapper: str | None
) -> dict:
    pin = json.loads((vendor_dir / "UPSTREAM_PIN.json").read_text())
    pin_oleans = {
        entry["module"]: entry["olean_sha256"]
        for entry in pin["execution_machine_closure"]
    }
    topo = get_topological_closure(vendor_dir, ["Miri.Interpreter.IntrinsicVectorMachine"])

    def run_lean(args: list[str], cwd: Path, env: dict[str, str]) -> subprocess.CompletedProcess:
        cmd = ([lean_wrapper] if lean_wrapper else []) + [lean_bin] + args
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
        if p.returncode != 0:
            raise RuntimeError(f"lean failed ({p.returncode}) on {args[-1]}:\nSTDOUT:\n{p.stdout}\nSTDERR:\n{p.stderr}")
        return p

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src_root = td_path / "src" / "vendor-miri"
        out_root = td_path / "out"
        src_root.mkdir(parents=True, exist_ok=True)
        out_root.mkdir(parents=True, exist_ok=True)
        # Copy required Miri sources into isolated temp directory matching anneal-audit layout
        for mod in topo:
            rel = Path(mod.replace(".", "/") + ".lean")
            dst = src_root / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(vendor_dir / rel, dst)

        env_build = os.environ.copy()
        lean_bin_resolved = Path(lean_bin).resolve()
        env_build["LEAN_PATH"] = str(out_root)
        env_build["LEAN_SYSROOT"] = str(lean_bin_resolved.parent.parent)
        env_build["PATH"] = f"{lean_bin_resolved.parent}:{env_build.get('PATH', '')}"

        per_target_compile: dict[str, dict] = {}
        pin_sha_matches = 0
        pin_sha_checked = 0
        t_total0 = time.monotonic()

        for mod in topo:
            rel_lean = mod.replace(".", "/") + ".lean"
            rel_olean = mod.replace(".", "/") + ".olean"
            (out_root / rel_olean).parent.mkdir(parents=True, exist_ok=True)
            t0 = time.monotonic()
            run_lean(
                [
                    "-j1",
                    "-M4096",
                    "-t0",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-R",
                    "src/vendor-miri",
                    "-o",
                    f"out/{rel_olean}",
                    f"src/vendor-miri/{rel_lean}",
                ],
                cwd=td_path,
                env=env_build,
            )
            dt_ms = round((time.monotonic() - t0) * 1000.0, 2)
            olean_bytes = (out_root / rel_olean).read_bytes()
            olean_sha = hashlib.sha256(olean_bytes).hexdigest()
            if mod in pin_oleans:
                pin_sha_checked += 1
                if olean_sha == pin_oleans[mod]:
                    pin_sha_matches += 1
            if mod in TARGET_MODULES:
                priv_p = out_root / (mod.replace(".", "/") + ".olean.private")
                srv_p = out_root / (mod.replace(".", "/") + ".olean.server")
                total_olean = (
                    len(olean_bytes)
                    + (priv_p.stat().st_size if priv_p.exists() else 0)
                    + (srv_p.stat().st_size if srv_p.exists() else 0)
                )
                per_target_compile[mod] = {
                    "compile_wall_ms": dt_ms,
                    "olean_bytes": len(olean_bytes),
                    "olean_all_parts_bytes": total_olean,
                    "olean_sha256": olean_sha,
                    "in_upstream_pin_closure": mod in pin_oleans,
                    "matches_upstream_pin_olean": (
                        olean_sha == pin_oleans[mod] if mod in pin_oleans else None
                    ),
                }

        total_compile_s = round(time.monotonic() - t_total0, 3)

        # 1. Compile 6 edge-case theorems directly against compiled Miri modules
        edge_src = src_root / "EdgeCaseTheorems.lean"
        edge_src.write_text(EDGE_CASE_THEOREMS_LEAN)
        run_lean(
            [
                "-j1",
                "-M4096",
                "-t0",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-R",
                "src/vendor-miri",
                "-o",
                "out/EdgeCaseTheorems.olean",
                "src/vendor-miri/EdgeCaseTheorems.lean",
            ],
            cwd=td_path,
            env=env_build,
        )

        # 2. Run isolated out-of-process kernel replay driver (separate processes per delta for clean RSS)
        driver_path = out_root / "ReplayDriver.lean"
        driver_path.write_text(REPLAY_DRIVER_LEAN)
        proc_simd = run_lean(
            [
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-j1",
                "-M16384",
                f"-R{out_root}",
                "--run",
                str(driver_path),
                "simd",
            ],
            cwd=out_root,
            env=env_build,
        )
        proc_x86 = run_lean(
            [
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-j1",
                "-M16384",
                f"-R{out_root}",
                "--run",
                str(driver_path),
                "x86",
            ],
            cwd=out_root,
            env=env_build,
        )
        replay_report = json.loads(proc_x86.stdout)
        replay_report.update(json.loads(proc_simd.stdout))

    return {
        "closure_modules_compiled": len(topo),
        "closure_total_compile_wall_s": total_compile_s,
        "upstream_pin_shared_modules": pin_sha_checked,
        "upstream_pin_olean_bit_identical_matches": pin_sha_matches,
        "target_modules_compile": per_target_compile,
        "kernel_replay_and_audit": replay_report,
        "edge_case_theorems_kernel_checked": [
            "aes_round_fips197_round1",
            "aes_invMixColumns_roundtrip",
            "mir_simd_shl_ub_at_width_32",
            "x86_pslld_saturates_to_zero_at_32",
            "x86_psrad_clamps_sign_bit_at_32",
            "carryless64_crc_fold_specimen",
        ],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--vendor-miri-dir", required=True, type=Path)
    ap.add_argument("--lean-bin", default=shutil.which("lean") or "lean")
    ap.add_argument("--lean-wrapper", default=None)
    ap.add_argument("--out-json", required=True, type=Path)
    args = ap.parse_args()

    vendor_dir: Path = args.vendor_miri_dir
    pin = json.loads((vendor_dir / "UPSTREAM_PIN.json").read_text())
    in_closure = {e["module"] for e in pin["execution_machine_closure"]}

    source_inventory = {}
    for mod in TARGET_MODULES:
        rel = mod.replace(".", "/") + ".lean"
        info = scan_lean_file(vendor_dir / rel)
        info["path"] = rel
        info["in_160_execution_machine_closure"] = mod in in_closure
        source_inventory[mod] = info

    supported = extract_lean_miri_supported_names(vendor_dir)
    cov_199 = parse_stdarch_and_check_coverage("1.99.1", supported)
    cov_nightly = parse_stdarch_and_check_coverage("nightly-2026-11-12", supported)
    replay = compile_and_replay_miri_closure(vendor_dir, args.lean_bin, args.lean_wrapper)

    result = {
        "miri_repository": pin["repository"],
        "miri_commit": pin["commit"],
        "upstream_pins": pin["upstream_pins"],
        "build_lean_toolchain": pin["build_lean_toolchain"],
        "upstream_lean_toolchain": pin["upstream_lean_toolchain"],
        "source_inventory": source_inventory,
        "supported_intrinsics": supported,
        "stdarch_and_crate_coverage": {
            "rustc_1_99_1": cov_199,
            "rustc_1_102_0_nightly": cov_nightly,
        },
        "build_and_kernel_replay": replay,
    }
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Wrote {args.out_json}")


if __name__ == "__main__":
    main()
