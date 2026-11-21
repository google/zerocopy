#!/usr/bin/env python3
"""F2-Linear / Bilinear GMP Unit-Basis vs. CDCL SAT/LRAT Crossover Benchmark.

Measures exact AIG/CNF size, CaDiCaL 2.1.2 solve time, trimmed LRAT RUP step count, and Lean v4.34.1
kernel replay time across carryless multiply (`pclmulqdq`) widths w in {8, 12, 16, 20, 24, 32, 64},
constant-polynomial CRC-64-ECMA folding (w=64), and 128-bit 16-lane `vpshufb` GF(2^8) multiply.
"""
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

TC_DIR = os.environ.get(
    "LEAN_V4341_SYSROOT",
    os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.34.1"),
)
LEAN_BIN = os.path.join(TC_DIR, "bin", "lean")
CADICAL_BIN = os.path.join(TC_DIR, "bin", "cadical")
LEAN_RUN = os.environ.get(
    "ANNEAL_LEAN_RUN",
    os.path.expanduser("~/.local/bin/anneal-lean-run"),
)
HERE = os.path.dirname(os.path.abspath(__file__))


def parse_tstat(stderr_txt):
    m = re.search(r"TSTAT wall=([0-9.]+) user=([0-9.]+) sys=([0-9.]+) rss=(\d+)", stderr_txt)
    if not m:
        return {}
    return {
        "wall_s": float(m.group(1)),
        "user_s": float(m.group(2)),
        "sys_s": float(m.group(3)),
        "rss_mb": round(int(m.group(4)) / 1024.0, 2),
    }


SAT_CLMUL_PROBE_LEAN = r"""import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Lean.Meta.Tactic.BVDecide

def bvZeroExt (wIn wOut : Nat) (e : BVExpr wIn) : BVExpr wOut :=
  .extract 0 wOut (.append (.const (0#wOut)) e rfl)

def bvShlConst (w : Nat) (e : BVExpr w) (k : Nat) : BVExpr w :=
  .shiftLeft e (.const (BitVec.ofNat w k))

/-- Build bit-blasted schoolbook carryless multiply `clmul w wOut x y` in upstream `Std.Tactic.BVDecide.BVExpr`. -/
def bvClmul (w wOut : Nat) (x y : BVExpr w) : BVExpr wOut := Id.run do
  let mut acc : BVExpr wOut := .const (0#wOut)
  let xExt : BVExpr wOut := bvZeroExt w wOut x
  for i in [0:w] do
    let yiBit : BVExpr 1 := .extract i 1 y
    let mask : BVExpr wOut := .replicate wOut yiBit (by simp)
    let shifted : BVExpr wOut := bvShlConst wOut xExt i
    let term : BVExpr wOut := .bin shifted .and mask
    acc := .bin acc .xor term
  return acc

def bvClmulKaratsuba (half : Nat) (x y : BVExpr (2 * half)) : BVExpr (4 * half) :=
  let wOut := 4 * half
  let xLo : BVExpr half := .extract 0 half x
  let xHi : BVExpr half := .extract half half x
  let yLo : BVExpr half := .extract 0 half y
  let yHi : BVExpr half := .extract half half y
  let z0  : BVExpr wOut := bvZeroExt (2 * half) wOut (bvClmul half (2 * half) xLo yLo)
  let z2Raw : BVExpr wOut := bvZeroExt (2 * half) wOut (bvClmul half (2 * half) xHi yHi)
  let z2  : BVExpr wOut := bvShlConst wOut z2Raw (2 * half)
  let zMid : BVExpr wOut := bvZeroExt (2 * half) wOut (bvClmul half (2 * half) (.bin xLo .xor xHi) (.bin yLo .xor yHi))
  let z1Raw : BVExpr wOut := .bin (.bin zMid .xor z0) .xor z2Raw
  let z1  : BVExpr wOut := bvShlConst wOut z1Raw half
  .bin (.bin z0 .xor z1) .xor z2

def runSatCrossover (timeoutSec : Nat) : Lean.CoreM Unit := do
  let cadicalPath := (← IO.appPath).parent.get! / "cadical"
  let mut rows : Array String := #[]
  let mut seenTimeout := false
  for half in [4, 6, 8, 10, 12, 16, 32] do
    let w := 2 * half
    let wOut := 4 * half
    let x : BVExpr w := .var 0
    let y : BVExpr w := .var 1
    let lhs := bvClmulKaratsuba half x y
    let rhs := bvClmul w wOut x y
    let vc : BVLogicalExpr := .not (.literal (.bin lhs .eq rhs))
    let t0 ← IO.monoMsNow
    let entry := vc.bitblast
    let aigGates := entry.aig.decls.size
    let (relab, _) := entry.relabelNat'
    let cnf := AIG.toCNF relab
    let nClauses := cnf.clauses.size
    let tBlast ← IO.monoMsNow
    if half ≥ 12 && seenTimeout then
      rows := rows.push s!"\{\"width\": {w}, \"aig_gates\": {aigGates}, \"cnf_clauses\": {nClauses}, \"bitblast_ms\": {tBlast - t0}, \"status\": \"SKIPPED_AFTER_SMALLER_TIMEOUT\"}"
    else
      let ts0 ← IO.monoMsNow
      let (row, timedOut) ← try
        IO.FS.withTempFile fun h cnfPath => do
          IO.FS.withTempFile fun _ lratPath => do
            h.putStr cnf.dimacs
            h.flush
            let res ← External.satQuery cadicalPath cnfPath lratPath timeoutSec true .proof
            let ts1 ← IO.monoMsNow
            match res with
            | .sat _ =>
              return (s!"\{\"width\": {w}, \"aig_gates\": {aigGates}, \"cnf_clauses\": {nClauses}, \"status\": \"UNEXPECTED_SAT\"}", false)
            | .unsat =>
              let acts ← LratCert.load lratPath true
              let ts2 ← IO.monoMsNow
              let mut nRup := 0
              for a in acts do
                match a with
                | .addRup .. => nRup := nRup + 1
                | _ => pure ()
              return (s!"\{\"width\": {w}, \"aig_gates\": {aigGates}, \"cnf_clauses\": {nClauses}, \"bitblast_ms\": {tBlast - t0}, \"cadical_ms\": {ts1 - ts0}, \"trim_ms\": {ts2 - ts1}, \"lrat_total_actions\": {acts.size}, \"lrat_rup_steps\": {nRup}, \"status\": \"UNSAT\"}", false)
      catch _ =>
        let ts1 ← IO.monoMsNow
        pure (s!"\{\"width\": {w}, \"aig_gates\": {aigGates}, \"cnf_clauses\": {nClauses}, \"bitblast_ms\": {tBlast - t0}, \"cadical_ms\": {ts1 - ts0}, \"status\": \"TIMEOUT\"}", true)
      if timedOut then seenTimeout := true
      rows := rows.push row

  -- Also measure Unary CRC-64-ECMA constant-polynomial `clmulKaratsuba 32 x K == clmul 64 128 x K` in SAT!
  let x64 : BVExpr 64 := .var 0
  let k64 : BVExpr 64 := .const (0x42f0e1eba9ea3693#64)
  let vcCrc : BVLogicalExpr := .not (.literal (.bin (bvClmulKaratsuba 32 x64 k64) .eq (bvClmul 64 128 x64 k64)))
  let eCrc := vcCrc.bitblast
  let (rCrc, _) := eCrc.relabelNat'
  let cnfCrc := AIG.toCNF rCrc
  let tsCrc0 ← IO.monoMsNow
  let crcRow ← try
    IO.FS.withTempFile fun h cnfPath => do
      IO.FS.withTempFile fun _ lratPath => do
        h.putStr cnfCrc.dimacs
        h.flush
        let res ← External.satQuery cadicalPath cnfPath lratPath timeoutSec true .proof
        let ts1 ← IO.monoMsNow
        match res with
        | .sat _ => return "{\"task\": \"crc64_const_clmul\", \"status\": \"SAT\"}"
        | .unsat =>
          let acts ← LratCert.load lratPath true
          let mut nRup := 0
          for a in acts do
            match a with | .addRup .. => nRup := nRup + 1 | _ => pure ()
          return s!"\{\"task\": \"crc64_const_clmul\", \"aig_gates\": {eCrc.aig.decls.size}, \"cnf_clauses\": {cnfCrc.clauses.size}, \"cadical_ms\": {ts1 - tsCrc0}, \"lrat_rup_steps\": {nRup}, \"status\": \"UNSAT\"}"
  catch _ =>
    let ts1 ← IO.monoMsNow
    pure s!"\{\"task\": \"crc64_const_clmul\", \"aig_gates\": {eCrc.aig.decls.size}, \"cnf_clauses\": {cnfCrc.clauses.size}, \"cadical_ms\": {ts1 - tsCrc0}, \"status\": \"TIMEOUT\"}"
  rows := rows.push crcRow
  IO.println ("[\n  " ++ String.intercalate ",\n  " rows.toList ++ "\n]")

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (System.FilePath.mk args[0]!) [System.FilePath.mk "."]
  let env ← Lean.importModules #[{ module := `Lean.Elab.Tactic.BVDecide }, { module := `Std.Tactic.BVDecide }] {}
  let ctx : Lean.Core.Context := { fileName := "<sat_crossover>", fileMap := default }
  let st : Lean.Core.State := { env }
  let _ ← (runSatCrossover 20).toIO ctx st
"""


def main():
    with tempfile.TemporaryDirectory() as tmp:
        shutil.copyfile(os.path.join(HERE, "F2BasisSimd.lean"), os.path.join(tmp, "F2BasisSimd.lean"))
        # Also compile a minimal F2BasisCore (without the 55s top-level theorems) so per-width timings are clean!
        with open(os.path.join(HERE, "F2BasisSimd.lean")) as f:
            f2_text = f.read()
        f2_core = f2_text.split("/-- Full 64x64 -> 128-bit `pclmulqdq` Karatsuba")[0] + "\nend F2SimdCert\n"
        with open(os.path.join(tmp, "F2Core.lean"), "w") as f:
            f.write(f2_core)
        rc0 = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
             "-o", "F2Core.olean", "F2Core.lean"],
            cwd=tmp, capture_output=True, text=True
        )
        assert rc0.returncode == 0, rc0.stdout + rc0.stderr

        env = os.environ.copy()
        env["LEAN_PATH"] = tmp

        # 1. Run SAT crossover probe across widths 8..64 (timeout = 20s per width in CaDiCaL)
        with open(os.path.join(tmp, "SatProbe.lean"), "w") as f:
            f.write(SAT_CLMUL_PROBE_LEAN)
        rsat = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "SatProbe.lean", TC_DIR],
            cwd=tmp, env=env, capture_output=True, text=True
        )
        assert rsat.returncode == 0, rsat.stdout + rsat.stderr
        sat_rows = json.loads(rsat.stdout)

        # 2. Measure F2-Bilinear GMP basis across widths 8, 12, 16, 20, 24, 32, 64 + Unary F2-Linear on CRC-64 & VPSHUFB-128!
        f2_rows = []
        for half in [4, 6, 8, 10, 12, 16, 32]:
            w = 2 * half
            wOut = 4 * half
            mod = f"F2W{w}"
            lean_w = f"""prelude
import F2Core
namespace Run{w}
open F2SimdCert
def clmulKara{w} (x y : BitVec {w}) : BitVec {wOut} :=
  let xLo := BitVec.extractLsb' 0 {half} x
  let xHi := BitVec.extractLsb' {half} {half} x
  let yLo := BitVec.extractLsb' 0 {half} y
  let yHi := BitVec.extractLsb' {half} {half} y
  let z0 := (clmul {half} {w} xLo yLo).zeroExtend {wOut}
  let z2 := ((clmul {half} {w} xHi yHi).zeroExtend {wOut}) <<< {w}
  let zMid := (clmul {half} {w} (xLo ^^^ xHi) (yLo ^^^ yHi)).zeroExtend {wOut}
  let z1 := (zMid ^^^ z0 ^^^ (clmul {half} {w} xHi yHi).zeroExtend {wOut}) <<< {half}
  z0 ^^^ z1 ^^^ z2

theorem eq_{w} : checkF2Bilinear clmulKara{w} (clmul {w} {wOut}) = true := by decide +kernel
end Run{w}
"""
            with open(os.path.join(tmp, f"{mod}.lean"), "w") as f:
                f.write(lean_w)
            res = subprocess.run(
                [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
                 LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
                 "-o", f"{mod}.olean", f"{mod}.lean"],
                cwd=tmp, env=env, capture_output=True, text=True
            )
            assert res.returncode == 0, res.stdout + res.stderr
            f2_rows.append({
                "width": w,
                "basis_evals": w * w,
                "compile": parse_tstat(res.stderr),
                "olean_bytes": os.path.getsize(os.path.join(tmp, f"{mod}.olean")),
            })

        # Also measure standalone Unary F2-Linear (`checkF2Linear1`) on 64-bit CRC-64-ECMA & 128-bit VPSHUFB GF(2^8)!
        f2_tail = "prelude\nimport F2Core\nnamespace F2SimdCert\n/-- Extract byte" + f2_text.split("/-- Extract byte")[1]
        f2_vpshufb_defs = f2_tail.split("/-- End-to-end 128-bit SIMD theorem:")[0] + "\nend F2SimdCert\n"
        with open(os.path.join(tmp, "F2SimdDefs.lean"), "w") as f:
            f.write(f2_vpshufb_defs)
        rd = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
             "-o", "F2SimdDefs.olean", "F2SimdDefs.lean"],
            cwd=tmp, env=env, capture_output=True, text=True
        )
        assert rd.returncode == 0, rd.stdout + rd.stderr

        unary_cases = {
            "crc64_const_clmul_64": """prelude
import F2SimdDefs
namespace UnaryBench
open F2SimdCert
theorem crc64_eq : ∀ x : BitVec 64, clmulKaratsuba64 x 0x42f0e1eba9ea3693#64 = clmul 64 128 x 0x42f0e1eba9ea3693#64 :=
  checkF2Linear1_sound
    ⟨clmulKaratsuba64_isBilinear.zero_left _, fun a1 a2 => clmulKaratsuba64_isBilinear.xor_left a1 a2 _⟩
    ⟨(clmul_isBilinear 64 128).zero_left _, fun a1 a2 => (clmul_isBilinear 64 128).xor_left a1 a2 _⟩
    (by decide +kernel)
end UnaryBench
""",
            "vpshufb128_gf256_mul_0x9d": """prelude
import F2SimdDefs
namespace UnaryBench2
open F2SimdCert
theorem vpshufb_eq : ∀ v : BitVec 128,
    gf256SimdVpshufb128 (mkGf256LutLo 0x9d#8) (mkGf256LutHi 0x9d#8) v = gf256MulConstSimd128 0x9d#8 v :=
  checkF2Linear1_sound
    (gf256SimdVpshufb128_isLinear (by decide +kernel) (by decide +kernel))
    (gf256MulConstSimd128_isLinear 0x9d#8)
    (by decide +kernel)
end UnaryBench2
"""
        }
        unary_results = {}
        for name, code in unary_cases.items():
            mod = f"U_{name}"
            with open(os.path.join(tmp, f"{mod}.lean"), "w") as f:
                f.write(code)
            ru = subprocess.run(
                [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
                 LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
                 "-o", f"{mod}.olean", f"{mod}.lean"],
                cwd=tmp, env=env, capture_output=True, text=True
            )
            assert ru.returncode == 0, ru.stdout + ru.stderr
            unary_results[name] = {
                "compile": parse_tstat(ru.stderr),
                "olean_bytes": os.path.getsize(os.path.join(tmp, f"{mod}.olean")),
            }

        out = {
            "sat_cdcl_crossover": sat_rows,
            "f2_bilinear_gmp_basis": f2_rows,
            "f2_unary_linear_gmp_basis": unary_results,
        }
        with open(os.path.join(HERE, "f2_vs_sat_crossover.json"), "w") as f:
            json.dump(out, f, indent=2)
        print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
