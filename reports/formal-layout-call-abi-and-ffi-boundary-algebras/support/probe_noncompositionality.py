#!/usr/bin/env python3
"""
Standalone reproducible probe verifying:
1. Lean 4.34.1 `prelude` + `Init.*` kernel check, axiom closure, and data-vs-proof WHNF latency.
2. Live `g++` Itanium ABI `dsize` tail-padding non-congruence (when C++ compiler is present).
3. Live `rustc` `UnsafeCell` niche suppression and `repr(C)` vs `repr(transparent)` i128 ABI divergence (when rustc is present).
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def find_lean():
    if env_bin := os.environ.get("LEAN_BIN"):
        return env_bin
    if on_path := shutil.which("lean"):
        return on_path
    return "lean"


def run_cmd(cmd, cwd=None):
    t0 = time.monotonic()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    dt_ms = (time.monotonic() - t0) * 1000.0
    return proc.returncode, proc.stdout, proc.stderr, round(dt_ms, 2)


def run_lean_cmd(lean_bin, args):
    if anneal_run := shutil.which("anneal-lean-run"):
        cmd = [anneal_run, "--mode", "file", "--", lean_bin, *args]
    else:
        cmd = [lean_bin, *args]
    return run_cmd(cmd)


def main():
    here = Path(__file__).resolve().parent
    lean_src = here / "LayoutCallAbiAlgebra.lean"
    lean_bin = find_lean()

    rc_ver, ver_out, _, _ = run_cmd([lean_bin, "--version"])
    lean_version = ver_out.strip() if rc_ver == 0 else "unknown"

    rc, out, err, lean_ms = run_lean_cmd(lean_bin, ["-DwarningAsError=true", str(lean_src)])
    if rc != 0:
        print(out + err, file=sys.stderr)
        sys.exit(rc)

    text = lean_src.read_text()
    banned_tokens = [
        "sorry", "admit", "omega", "bv_decide", "native_decide",
        "_unsafe_rec", "noncomputable", "Classical.choice", "Quot.sound",
    ]
    code_lines = []
    in_doc = False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("/-"):
            in_doc = True
        if not in_doc and not s.startswith("--"):
            code_lines.append(line)
        if "-/" in s:
            in_doc = False
    code_only = "\n".join(code_lines)
    hygiene_hits = {
        tok: len(re.findall(r"\b" + re.escape(tok) + r"\b", code_only))
        for tok in banned_tokens
    }

    decls = re.findall(r"^(?:theorem|def)\s+([A-Za-z0-9_'?]+)", text, flags=re.M)
    axiom_map = {}
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        audit_file = td_path / "AuditAxioms.lean"
        prints = "\n".join(f"#print axioms FormalLayoutAbiAlgebra.{name}" for name in decls)
        audit_file.write_text(text + "\n" + prints + "\n")
        arc, aout, aerr, _ = run_lean_cmd(lean_bin, [str(audit_file)])
        if arc != 0:
            print(aout + aerr, file=sys.stderr)
            sys.exit(arc)
        for line in (aout + "\n" + aerr).splitlines():
            m = re.match(r"^'FormalLayoutAbiAlgebra\.([^']+)' depends on axioms: \[(.*)\]$", line.strip())
            if m:
                axs = [x.strip() for x in m.group(2).split(",") if x.strip()] if m.group(2).strip() else []
                axiom_map[m.group(1)] = axs
            m2 = re.match(r"^'FormalLayoutAbiAlgebra\.([^']+)' does not depend on any axioms$", line.strip())
            if m2:
                axiom_map[m2.group(1)] = []

        # Data/proof split vs dependent sigma chain microbenchmark (120 chained updates)
        bench_unbundled = td_path / "BenchUnbundled.lean"
        bench_bundled = td_path / "BenchBundled.lean"
        base_header = "\n".join([
            "prelude",
            "import Init.Core",
            "import Init.Data.Nat.Basic",
            "structure G where",
            "  data : Nat",
            "  total : Nat",
            "  align : Nat",
            "def ValidG (g : G) : Prop := 0 < g.align ∧ g.data ≤ g.total",
        ])
        bench_unbundled.write_text(base_header + """
def stepG (g : G) : G := { g with data := g.data + 1, total := g.total + 1 }
theorem stepG_valid (g : G) (h : ValidG g) : ValidG (stepG g) :=
  ⟨h.1, Nat.succ_le_succ h.2⟩
def loopG (k : Nat) (g : G) : G := @Nat.rec (fun _ => G) g (fun _ acc => stepG acc) k
theorem loopG_valid (k : Nat) (g : G) (h : ValidG g) : ValidG (loopG k g) := by
  induction k with
  | zero => exact h
  | succ _ ih => exact stepG_valid _ ih
theorem canaryU : (loopG 120 { data := 1, total := 4, align := 4 }).total = 124 := rfl
""")
        bench_bundled.write_text(base_header + """
structure BG where
  g : G
  valid : ValidG g
def stepBG (b : BG) : BG :=
  { g := { b.g with data := b.g.data + 1, total := b.g.total + 1 }
    valid := ⟨b.valid.1, Nat.succ_le_succ b.valid.2⟩ }
def loopBG (k : Nat) (b : BG) : BG := @Nat.rec (fun _ => BG) b (fun _ acc => stepBG acc) k
theorem canaryB : (loopBG 120 { g := { data := 1, total := 4, align := 4 }, valid := ⟨Nat.zero_lt_succ 3, Nat.le_of_lt (Nat.lt_succ_of_le (Nat.le_refl 3))⟩ }).g.total = 124 := rfl
""")
        _, _, _, ms_u = run_lean_cmd(lean_bin, [str(bench_unbundled)])
        _, _, _, ms_b = run_lean_cmd(lean_bin, [str(bench_bundled)])

        cpp_res = None
        for cxx in ("g++", "clang++"):
            if shutil.which(cxx):
                cpp_src = td_path / "itanium_dsize.cpp"
                cpp_bin = td_path / "itanium_dsize"
                cpp_src.write_text("""
#include <cstddef>
#include <cstdint>
#include <cstdio>
struct UserDtor { int32_t a; uint8_t b; ~UserDtor() {} };
struct PodEqual { int32_t a; uint8_t b; uint8_t pad[3]; };
struct DerivedNonPod : UserDtor { uint8_t d; };
struct DerivedPod : PodEqual { uint8_t d; };
struct MemberNonPod { UserDtor u; uint8_t d; };
struct NoUniqueMember { [[no_unique_address]] UserDtor u; uint8_t d; };
int main() {
  std::printf("{\\"UserDtor\\": [%zu, %zu], \\"PodEqual\\": [%zu, %zu], \\"DerivedNonPod\\": [%zu, %zu, %zu], \\"DerivedPod\\": [%zu, %zu, %zu], \\"MemberNonPod\\": [%zu, %zu, %zu], \\"NoUniqueMember\\": [%zu, %zu, %zu]}\\n",
    sizeof(UserDtor), alignof(UserDtor), sizeof(PodEqual), alignof(PodEqual),
    sizeof(DerivedNonPod), alignof(DerivedNonPod), offsetof(DerivedNonPod, d),
    sizeof(DerivedPod), alignof(DerivedPod), offsetof(DerivedPod, d),
    sizeof(MemberNonPod), alignof(MemberNonPod), offsetof(MemberNonPod, d),
    sizeof(NoUniqueMember), alignof(NoUniqueMember), offsetof(NoUniqueMember, d));
}
""")
                rc1, _, _, _ = run_cmd([cxx, "-std=c++20", "-O2", str(cpp_src), "-o", str(cpp_bin)])
                if rc1 == 0:
                    rc2, out2, _, _ = run_cmd([str(cpp_bin)])
                    if rc2 == 0:
                        _, ver2, _, _ = run_cmd([cxx, "--version"])
                        cpp_res = {
                            "compiler": cxx,
                            "version": ver2.splitlines()[0] if ver2 else "",
                            "measurements": json.loads(out2.strip()),
                        }
                break

        rust_res = None
        if shutil.which("rustc"):
            rs_src = td_path / "rust_noncomp.rs"
            rs_ll = td_path / "rust_noncomp.ll"
            rs_src.write_text("""
#![crate_type = "lib"]
use core::cell::UnsafeCell;
use core::mem::size_of;
#[repr(C)] pub struct WrapCell(pub UnsafeCell<bool>);
#[repr(C)] pub struct PlainBool(pub bool);
#[repr(C)] pub struct I128C(pub u128);
#[repr(transparent)] pub struct I128T(pub u128);
#[unsafe(no_mangle)] pub extern "C" fn take_c(x: I128C) -> u64 { x.0 as u64 }
#[unsafe(no_mangle)] pub extern "C" fn take_t(x: I128T) -> u64 { x.0 as u64 }
pub fn sizes() -> [usize; 6] {
    [size_of::<bool>(), size_of::<Option<bool>>(), size_of::<Option<PlainBool>>(), size_of::<Option<WrapCell>>(), size_of::<I128C>(), size_of::<I128T>()]
}
""")
            _, rver, _, _ = run_cmd(["rustc", "--version"])
            rc_ir, _, _, _ = run_cmd(["rustc", "--edition=2024", "-O", "--emit=llvm-ir", "-o", str(rs_ll), str(rs_src)])
            rc_sz, out_sz, err_sz, _ = run_cmd(["rustc", "--edition=2024", "-O", "-Zprint-type-sizes", str(rs_src)])
            ll_txt = rs_ll.read_text() if rc_ir == 0 else ""
            sigs = [ln for ln in ll_txt.splitlines() if "define " in ln and ("take_c" in ln or "take_t" in ln)]
            ts_lines = [ln for ln in (out_sz + "\n" + err_sz).splitlines() if "print-type-size type:" in ln]
            rust_res = {"version": rver.strip(), "llvm_sigs": sigs, "type_sizes": ts_lines}

    distinct_axioms = sorted({ax for axs in axiom_map.values() for ax in axs})
    summary = {
        "lean_version": lean_version,
        "lean_file": lean_src.name,
        "lean_check_ms": lean_ms,
        "decl_count": len(axiom_map),
        "hygiene_hits": hygiene_hits,
        "distinct_axioms": distinct_axioms,
        "bench_unbundled_ms": ms_u,
        "bench_bundled_ms": ms_b,
        "cpp_probe": cpp_res,
        "rust_probe": rust_res,
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
