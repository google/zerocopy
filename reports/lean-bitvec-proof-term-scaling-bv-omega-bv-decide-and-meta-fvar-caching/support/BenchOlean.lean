-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay

open Lean

partial def exprStats (e : Expr) : IO (Nat × Nat × Nat) := do
  let memo ← IO.mkRef ({} : Std.HashMap UInt64 (Nat × Nat))
  let rec go (x : Expr) : IO (Nat × Nat) := do
    let addr := unsafe (ptrAddrUnsafe x).toUInt64
    if let some res := (← memo.get)[addr]? then
      return res
    let res ← match x with
      | .app f a =>
        let (tf, df) ← go f
        let (ta, da) ← go a
        pure (1 + tf + ta, 1 + Nat.max df da)
      | .lam _ t b _ | .forallE _ t b _ =>
        let (tt, dt) ← go t
        let (tb, db) ← go b
        pure (1 + tt + tb, 1 + Nat.max dt db)
      | .letE _ t v b _ =>
        let (tt, dt) ← go t
        let (tv, dv) ← go v
        let (tb, db) ← go b
        pure (1 + tt + tv + tb, 1 + Nat.max dt (Nat.max dv db))
      | .mdata _ b | .proj _ _ b =>
        let (tb, db) ← go b
        pure (1 + tb, 1 + db)
      | _ => pure (1, 1)
    memo.modify (·.insert addr res)
    return res
  let (tree, depth) ← go e
  let dag := (← memo.get).size
  return (dag, tree, depth)

partial def collectAxiomsTransitive (env : Environment) (roots : Array Name) : IO (Array Name) := do
  let visited ← IO.mkRef ({} : Std.HashSet Name)
  let axioms ← IO.mkRef ({} : Std.HashSet Name)
  let rec visit (n : Name) : IO Unit := do
    if (← visited.get).contains n then return
    visited.modify (·.insert n)
    if let some cinfo := env.find? n then
      if cinfo matches .axiomInfo _ then
        axioms.modify (·.insert n)
      for dep in cinfo.getUsedConstantsAsSet do
        visit dep
  for r in roots do
    visit r
  return (← axioms.get).toArray

unsafe def main (args : List String) : IO Unit := do
  let modNameStr := args[0]!
  let sysroot := args[1]!
  let modName := modNameStr.toName
  initSearchPath (System.FilePath.mk sysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0) (loadExts := true)
  let some modIdx := env.getModuleIdx? modName | throw (IO.userError s!"Module {modName} not found")
  let modData := env.header.moduleData[modIdx.toNat]!

  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut roots : Array Name := #[]
  let mut totalDag := 0
  let mut totalTree := 0
  let mut maxDepth := 0

  IO.println s!"MODULE={modName}"
  IO.println s!"NUM_CONSTANTS={modData.constants.size}"
  IO.println s!"NUM_EXTRA_CONSTS={modData.extraConstNames.size}"

  for cinfo in modData.constants do
    newConsts := newConsts.insert cinfo.name cinfo
    roots := roots.push cinfo.name
    let (tdag, ttree, tdepth) ← exprStats cinfo.type
    let (vdag, vtree, vdepth) ← match cinfo.value? (allowOpaque := true) with
      | some v => exprStats v
      | none => pure (0, 0, 0)
    totalDag := totalDag + tdag + vdag
    totalTree := totalTree + ttree + vtree
    maxDepth := Nat.max maxDepth (Nat.max tdepth vdepth)
    IO.println s!"CONST {cinfo.name} type_dag={tdag} val_dag={vdag} val_tree={vtree} depth={vdepth}"

  let allAxioms ← collectAxiomsTransitive env roots
  let importNames := modData.imports
  let baseEnv ← importModules importNames {} (trustLevel := 0) (loadExts := false)
  let mut replayTimesMs : Array Float := #[]
  for _ in [:5] do
    let t0 ← IO.monoNanosNow
    discard <| baseEnv.toKernelEnv.replay newConsts
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0).toFloat / 1000000.0
    replayTimesMs := replayTimesMs.push ms

  let sortedReplay := replayTimesMs.qsort (· < ·)
  let minReplay := sortedReplay[0]!
  let medReplay := sortedReplay[2]!
  let axList := allAxioms.map toString |>.qsort (· < ·)
  IO.println s!"SUMMARY total_dag={totalDag} total_tree={totalTree} max_depth={maxDepth} replay_min_ms={minReplay} replay_med_ms={medReplay} axioms={axList}"
