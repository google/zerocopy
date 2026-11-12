-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

open Lean Meta

namespace MetaHasFVarCachingProbe

/--
Build a depth-`d` shared state-transition DAG where each step updates a `Bool`
control/status component via `Bool.or cur.1 cur.1` while forwarding a payload
component `cur.2`.
- When `payload` is a closed constant (`0 : Nat`), `cur.hasFVar == false` at
  every layer, so `useWHNFCache` (`src/Lean/Meta/WHNF.lean`) caches the first
  branch of `Bool.or cur.1 cur.1` in `whnfDefault` and hits the cache in `O(1)`
  on the second branch (`O(d)` total time).
- When `payload` is a free variable (`symVar : Nat`), `cur.hasFVar == true` at
  every layer—even though `.1` projects only the `Bool` component! Because
  `(Prod.fst cur).hasFVar == true`, `useWHNFCache` returns `false` and `whnf`
  re-evaluates both branches of `Bool.or cur.1 cur.1` at every layer (`O(2^d)`
  total time).
-/
def buildCoupledStateDag (d : Nat) (payload : Expr) : Expr := Id.run do
  let u0 := Level.zero
  let boolTy := mkConst ``Bool
  let natTy := mkConst ``Nat
  let mut cur := mkApp4 (mkConst ``Prod.mk [u0, u0]) boolTy natTy (mkConst ``Bool.false) payload
  for _ in [:d] do
    let fst := mkProj ``Prod 0 cur
    let snd := mkProj ``Prod 1 cur
    let orFst := mkApp2 (mkConst ``Bool.or) fst fst
    cur := mkApp4 (mkConst ``Prod.mk [u0, u0]) boolTy natTy orFst snd
  return mkProj ``Prod 0 cur

/--
Decoupled state representation: keep the reducible control/tag DAG separate from
the `FVar`-carrying symbolic payload tuple until the top level, so the inner
reducible DAG has `hasFVar == false` and hits `useWHNFCache`.
-/
def buildDecoupledStateDag (d : Nat) (payload : Expr) : Expr := Id.run do
  let u0 := Level.zero
  let boolTy := mkConst ``Bool
  let natTy := mkConst ``Nat
  let mut ctrl := mkConst ``Bool.false
  for _ in [:d] do
    ctrl := mkApp2 (mkConst ``Bool.or) ctrl ctrl
  let topPair := mkApp4 (mkConst ``Prod.mk [u0, u0]) boolTy natTy ctrl payload
  return mkProj ``Prod 0 topPair

def runBench : MetaM Unit := do
  IO.println s!"LEAN_VERSION={Lean.versionString}"
  let natTy := mkConst ``Nat
  let closedPayload := mkNatLit 0
  let simpTheorems ← getSimpTheorems
  let simprocs ← Simp.getSimprocs
  let simpCtx ← Simp.mkContext (simpTheorems := #[simpTheorems])
  withLocalDeclD `symVar natTy fun fvarPayload => do
    for d in [10, 12, 14, 16, 18, 20] do
      let closedExpr := buildCoupledStateDag d closedPayload
      let fvarCoupled := buildCoupledStateDag d fvarPayload
      let fvarDecoupled := buildDecoupledStateDag d fvarPayload

      -- 1. `Meta.whnf` on closed DAG (`hasFVar = false`, `useWHNFCache = true`)
      modifyThe Meta.State (fun s => { s with cache := {} })
      let t0 ← IO.monoNanosNow
      let rClosed ← whnf closedExpr
      let t1 ← IO.monoNanosNow
      let msClosed := (t1 - t0).toFloat / 1000000.0

      -- 2. `Meta.whnf` on coupled FVar-carrying DAG (`hasFVar = true`, `useWHNFCache = false`)
      modifyThe Meta.State (fun s => { s with cache := {} })
      let t2 ← IO.monoNanosNow
      let rFVar ← whnf fvarCoupled
      let t3 ← IO.monoNanosNow
      let msFVar := (t3 - t2).toFloat / 1000000.0

      -- 3. `Meta.dsimp` on coupled FVar-carrying DAG (`ExprMap` memoizes even when `hasFVar = true`)
      let t4 ← IO.monoNanosNow
      let (rDsimp, _) ← dsimp fvarCoupled simpCtx (simprocs := #[simprocs])
      let t5 ← IO.monoNanosNow
      let msDsimp := (t5 - t4).toFloat / 1000000.0

      -- 4. `Meta.whnf` on decoupled FVar-carrying DAG (inner control DAG has `hasFVar = false`)
      modifyThe Meta.State (fun s => { s with cache := {} })
      let t6 ← IO.monoNanosNow
      let rDecoupled ← whnf fvarDecoupled
      let t7 ← IO.monoNanosNow
      let msDecoupled := (t7 - t6).toFloat / 1000000.0

      IO.println s!"DEPTH={d} whnf_closed_ms={msClosed} whnf_fvar_coupled_ms={msFVar} dsimp_fvar_coupled_ms={msDsimp} whnf_fvar_decoupled_ms={msDecoupled} speedup_dsimp={msFVar / msDsimp} speedup_decoupled={msFVar / msDecoupled} all_false={rClosed == mkConst ``Bool.false && rFVar == mkConst ``Bool.false && rDsimp == mkConst ``Bool.false && rDecoupled == mkConst ``Bool.false}"

    -- Test `BuiltinSimprocs.BitVec` (`BitVec.fromExpr?` / `Nat.fromExpr?`) on concrete vs FVar expressions
    let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
    withLocalDeclD `x bv64 fun xFVar => do
      let bvLit42 := toExpr (42#64)
      let idxLit3 := toExpr (3 : Nat)
      let concreteGetLsb := mkApp3 (mkConst ``BitVec.getLsbD) (toExpr (64 : Nat)) bvLit42 idxLit3
      let symbolicGetLsb := mkApp3 (mkConst ``BitVec.getLsbD) (toExpr (64 : Nat)) xFVar idxLit3
      let (rConc, _) ← simp concreteGetLsb simpCtx (simprocs := #[simprocs])
      let (rSym, _) ← simp symbolicGetLsb simpCtx (simprocs := #[simprocs])
      IO.println s!"SIMPROC concrete_reduced={rConc.expr != concreteGetLsb} symbolic_reduced={rSym.expr != symbolicGetLsb} concrete_out={rConc.expr} symbolic_out={rSym.expr}"

unsafe def main (args : List String) : IO Unit := do
  let sysroot := args[0]!
  initSearchPath (System.FilePath.mk sysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<probe>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  discard <| (runBench.run' {}).toIO ctx state

end MetaHasFVarCachingProbe

unsafe def main (args : List String) : IO Unit :=
  MetaHasFVarCachingProbe.main args
