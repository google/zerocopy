-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import DaemonSpec

/-!
# Resident Pre-Warmed Lean 4 Kernel Audit Daemon (`AnnealKernelDaemon.lean`)

Loads `Init` and `DaemonSpec` (`Layer0..Layer3` checker definitions) once into a resident
`Lean.Environment` (`env_base`), bypassing per-request `.olean` `mmap` initialization (`~180 ms`),
ASCII `.lean` parsing, and `Lean.Elab` elaboration.
For each incoming function or cone verification packet `(reqId, chunks250, seed)`:
1. Constructs the kernel `Declaration.thmDecl` directly in memory using `mkNatLit chunks250`
   and `mkNatLit seed`:
   `theorem cert_<reqId> : DaemonSpec.checkStepsN <chunks250> <seed> = true := Eq.refl true`
2. Audits the proof and type expressions for forbidden constants (`sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`);
3. Invokes `env_base.addDeclCore 0 200000 decl none` (the C++ `lean::environment::add` kernel
   typechecker) and drops the returned ephemeral `Environment`, leaving `env_base` untouched.
-/

open Lean

/-- Read current process VmRSS in kilobytes from `/proc/self/statm` on Linux. -/
def getVmRssKb : IO UInt64 := do
  try
    let content ← IO.FS.readFile "/proc/self/statm"
    let parts := content.trimAscii.toString.splitOn " "
    match parts[1]? with
    | some rssPagesStr =>
        match rssPagesStr.toNat? with
        | some pages => return (pages * 4).toUInt64
        | none => return 0
    | none => return 0
  catch _ =>
    return 0

/-- Fast recursive expression scan ensuring no `sorryAx`, `Lean.ofReduceBool`, or
`Lean.trustCompiler` constant occurs anywhere in the submitted kernel declaration. -/
partial def hasForbiddenConst : Expr → Bool
  | .const n _ =>
      n == ``sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler
  | .app f a => hasForbiddenConst f || hasForbiddenConst a
  | .lam _ t b _ => hasForbiddenConst t || hasForbiddenConst b
  | .forallE _ t b _ => hasForbiddenConst t || hasForbiddenConst b
  | .letE _ t v b _ => hasForbiddenConst t || hasForbiddenConst v || hasForbiddenConst b
  | .mdata _ e => hasForbiddenConst e
  | .proj _ _ e => hasForbiddenConst e
  | _ => false

/-- Construct a kernel `Declaration.thmDecl` directly from binary `Nat` parameters `(chunks250, seed)`
without invoking the Lean parser or elaborator. -/
def mkShardThmDecl (reqId chunks250 seed : Nat) (expectedBool : Name := ``Bool.true)
    (customProof? : Option Expr := none) : Declaration :=
  let declName := Name.mkSimple s!"_anneal_ephemeral_cert_{reqId}"
  let lhs := mkApp2 (mkConst ``DaemonSpec.checkStepsN) (mkNatLit chunks250) (mkNatLit seed)
  let rhs := mkConst expectedBool
  let propType := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs
  let proofVal := customProof?.getD (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) rhs)
  Declaration.thmDecl {
    name        := declName
    levelParams := []
    type        := propType
    value       := proofVal
  }

/-- Verify a single ephemeral declaration against the immutable resident `envBase`
using `Environment.addDeclCore`, returning `(accepted, latencyUs)`. -/
def checkCertInResidentKernel (envBase : Environment) (decl : Declaration) : IO (Bool × Float) := do
  let t0 ← IO.monoNanosNow
  let ok ← match decl with
    | .thmDecl tv =>
        if hasForbiddenConst tv.type || hasForbiddenConst tv.value then
          pure false
        else
          match envBase.addDeclCore 0 200000 decl none true with
          | .ok _ephemeralEnv =>
              -- `_ephemeralEnv` goes out of scope immediately here; `envBase` is untouched!
              pure true
          | .error _ =>
              pure false
    | _ => pure false
  let t1 ← IO.monoNanosNow
  let us := (t1 - t0).toFloat / 1000.0
  return (ok, us)

/-- Benchmark `iters` sequential kernel checks on `envBase` and return `(p50_ms, p95_ms, p99_ms)`. -/
def benchScenario (envBase : Environment) (iters : Nat) (chunks250 : Nat) : IO (Float × Float × Float) := do
  let mut timesMs : Array Float := Array.mkEmpty iters
  for i in [0:iters] do
    let decl := mkShardThmDecl i chunks250 (i + 1)
    let (ok, us) ← checkCertInResidentKernel envBase decl
    if !ok then
      throw <| IO.userError s!"Resident kernel rejected valid certificate at iter {i}"
    timesMs := timesMs.push (us / 1000.0)
  let sorted := timesMs.qsort (fun a b => a < b)
  let p50 := sorted.getD (iters / 2) 0.0
  let p95 := sorted.getD ((iters * 95) / 100) 0.0
  let p99 := sorted.getD ((iters * 99) / 100) 0.0
  return (p50, p95, p99)

def main : IO Unit := do
  let tBoot0 ← IO.monoNanosNow
  initSearchPath (← findSysroot) [System.FilePath.mk ".lake/build/lib/lean"]
  let envBase ← importModules #[{ module := `DaemonSpec }] {} 0
  let tBoot1 ← IO.monoNanosNow
  let warmBootMs := (tBoot1 - tBoot0).toFloat / 1000000.0
  let baseConstCount := envBase.constants.map₁.size

  -- 1. Measure incremental scenarios:
  -- S2: 1 function (245 steps -> 1 chunk of 250 steps)
  let (s2P50, s2P95, s2P99) ← benchScenario envBase 200 1
  -- S4: 1 function body edit (310 steps -> 2 chunks = 500 steps)
  let (s4P50, s4P95, s4P99) ← benchScenario envBase 200 2
  -- 10-fn batch (2,450 steps -> 10 chunks = 2,500 steps)
  let (m10P50, m10P95, m10P99) ← benchScenario envBase 100 10
  -- S3 sharded across 8 resident workers (51,840 / 8 = 6,480 steps -> 26 chunks per worker)
  let (s3ShardedP50, s3ShardedP95, s3ShardedP99) ← benchScenario envBase 60 26
  -- S3 single-worker sequential (112-function hot inline cone, 51,840 steps -> 208 chunks)
  let (s3P50, s3P95, s3P99) ← benchScenario envBase 30 208

  -- 2. Negative tamper-rejection tests in the live C++ kernel:
  -- (a) Corrupted NatBinarySplit certificate (claiming `checkStepsN 1 42 = false` by `rfl`)
  let badDeclCorrupt := mkShardThmDecl 900001 1 42 ``Bool.false
  let (okCorrupt, usCorrupt) ← checkCertInResidentKernel envBase badDeclCorrupt
  -- (b) Injected `sorryAx` proof term
  let sorryProof := mkApp2 (mkConst ``sorryAx [Level.zero]) (mkConst ``True) (mkConst ``Bool.false)
  let badDeclSorry := mkShardThmDecl 900002 1 42 ``Bool.true (some sorryProof)
  let (okSorry, usSorry) ← checkCertInResidentKernel envBase badDeclSorry
  -- (c) Injected `Lean.ofReduceBool` term
  let reduceBoolProof := mkConst `Lean.ofReduceBool
  let badDeclReduce := mkShardThmDecl 900003 1 42 ``Bool.true (some reduceBoolProof)
  let (okReduce, usReduce) ← checkCertInResidentKernel envBase badDeclReduce
  -- (d) Verify `envBase` is 100% untainted after all 3 negative tamper attempts:
  let postTamperDecl := mkShardThmDecl 900004 1 777
  let (okPostTamper, usPostTamper) ← checkCertInResidentKernel envBase postTamperDecl

  -- 3. 10,000-request continuous stress test measuring RSS stability & zero declaration leakage
  let rssBefore ← getVmRssKb
  let mut rssAt100 : UInt64 := 0
  let mut rssAt1000 : UInt64 := 0
  let mut rssAt5000 : UInt64 := 0
  let tStress0 ← IO.monoNanosNow
  for reqIdx in [1:10001] do
    let decl := mkShardThmDecl (100000 + reqIdx) 1 reqIdx
    let (ok, _) ← checkCertInResidentKernel envBase decl
    if !ok then
      throw <| IO.userError s!"Stress test failed at request {reqIdx}"
    if reqIdx == 100 then rssAt100 ← getVmRssKb
    if reqIdx == 1000 then rssAt1000 ← getVmRssKb
    if reqIdx == 5000 then rssAt5000 ← getVmRssKb
  let tStress1 ← IO.monoNanosNow
  let rssAt10000 ← getVmRssKb
  let stressTotalMs := (tStress1 - tStress0).toFloat / 1000000.0
  let postStressConstCount := envBase.constants.map₁.size
  let leakedDecls := postStressConstCount - baseConstCount

  IO.println s!"\{\"daemon_init_ms\": {warmBootMs},"
  IO.println s!" \"base_const_count\": {baseConstCount},"
  IO.println s!" \"post_stress_const_count\": {postStressConstCount},"
  IO.println s!" \"leaked_decls\": {leakedDecls},"
  IO.println s!" \"scenarios_lean_kernel_ms\": \{"
  IO.println s!"   \"S2_245_steps\": \{\"p50_ms\": {s2P50}, \"p95_ms\": {s2P95}, \"p99_ms\": {s2P99}},"
  IO.println s!"   \"S4_310_steps\": \{\"p50_ms\": {s4P50}, \"p95_ms\": {s4P95}, \"p99_ms\": {s4P99}},"
  IO.println s!"   \"batch10_2450_steps\": \{\"p50_ms\": {m10P50}, \"p95_ms\": {m10P95}, \"p99_ms\": {m10P99}},"
  IO.println s!"   \"S3_51840_steps_8worker_sharded\": \{\"p50_ms\": {s3ShardedP50}, \"p95_ms\": {s3ShardedP95}, \"p99_ms\": {s3ShardedP99}},"
  IO.println s!"   \"S3_51840_steps_1worker_seq\": \{\"p50_ms\": {s3P50}, \"p95_ms\": {s3P95}, \"p99_ms\": {s3P99}}"
  IO.println s!" },"
  IO.println s!" \"tamper_tests\": \{"
  IO.println s!"   \"corrupted_packet_accepted\": {okCorrupt}, \"corrupted_reject_us\": {usCorrupt},"
  IO.println s!"   \"sorryAx_accepted\": {okSorry}, \"sorryAx_reject_us\": {usSorry},"
  IO.println s!"   \"ofReduceBool_accepted\": {okReduce}, \"ofReduceBool_reject_us\": {usReduce},"
  IO.println s!"   \"post_tamper_valid_accepted\": {okPostTamper}, \"post_tamper_valid_us\": {usPostTamper}"
  IO.println s!" },"
  IO.println s!" \"stress_10000_requests\": \{"
  IO.println s!"   \"total_ms\": {stressTotalMs},"
  IO.println s!"   \"mean_us_per_req\": {(stressTotalMs * 1000.0) / 10000.0},"
  IO.println s!"   \"rss_kb_before\": {rssBefore},"
  IO.println s!"   \"rss_kb_req_100\": {rssAt100},"
  IO.println s!"   \"rss_kb_req_1000\": {rssAt1000},"
  IO.println s!"   \"rss_kb_req_5000\": {rssAt5000},"
  IO.println s!"   \"rss_kb_req_10000\": {rssAt10000}"
  IO.println s!" }}"
