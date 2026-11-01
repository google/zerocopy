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

unsafe def countExprNodes (e : Expr)
    (memoRef : IO.Ref (Std.HashMap USize Nat)) : IO Nat := do
  let ptr := ptrAddrUnsafe e
  let memo ← memoRef.get
  if let some tCount := memo.get? ptr then
    return tCount
  let childTree ← match e with
    | .app f a =>
      let tf ← countExprNodes f memoRef
      let ta ← countExprNodes a memoRef
      pure (tf + ta)
    | .lam _ t b _ =>
      let tt ← countExprNodes t memoRef
      let tb ← countExprNodes b memoRef
      pure (tt + tb)
    | .forallE _ t b _ =>
      let tt ← countExprNodes t memoRef
      let tb ← countExprNodes b memoRef
      pure (tt + tb)
    | .letE _ t val b _ =>
      let tt ← countExprNodes t memoRef
      let tv ← countExprNodes val memoRef
      let tb ← countExprNodes b memoRef
      pure (tt + tv + tb)
    | .mdata _ b =>
      countExprNodes b memoRef
    | .proj _ _ b =>
      countExprNodes b memoRef
    | _ =>
      pure 0
  let myTree := 1 + childTree
  memoRef.modify (·.insert ptr myTree)
  return myTree

unsafe def measureTarget (baseEnv : Environment) (targetModStr : String) : IO Unit := do
  let targetMod := targetModStr.toName
  let targetEnv ← importModules #[{ module := targetMod }] {}
  let mut baseModSet : NameSet := {}
  for m in baseEnv.header.modules do
    baseModSet := baseModSet.insert m.module
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let memoAll ← IO.mkRef (Std.HashMap.emptyWithCapacity 4096 : Std.HashMap USize Nat)
  let memoMod ← IO.mkRef (Std.HashMap.emptyWithCapacity 2048 : Std.HashMap USize Nat)
  let mut totalTree : Nat := 0
  let mut modTree : Nat := 0
  let mut modDecls : Nat := 0
  let mut replayedMods : Array Name := #[]
  for m in targetEnv.header.modules, data in targetEnv.header.moduleData do
    if !baseModSet.contains m.module then
      replayedMods := replayedMods.push m.module
      for cinfo in data.constants do
        newConsts := newConsts.insert cinfo.name cinfo
        let tT ← countExprNodes cinfo.type memoAll
        totalTree := totalTree + tT
        if let some val := cinfo.value? (allowOpaque := true) then
          let tV ← countExprNodes val memoAll
          totalTree := totalTree + tV
        if m.module == targetMod then
          modDecls := modDecls + 1
          let mT ← countExprNodes cinfo.type memoMod
          modTree := modTree + mT
          if let some val := cinfo.value? (allowOpaque := true) then
            let mV ← countExprNodes val memoMod
            modTree := modTree + mV
  let totalDag := (← memoAll.get).size
  let modDag := (← memoMod.get).size
  let mut timesNs : Array Nat := #[]
  for _ in [0:7] do
    let t0 ← IO.monoNanosNow
    let _ ← (baseEnv.toKernelEnv.replay newConsts).toIO
      (fun err => IO.userError s!"Kernel replay error in {targetMod}: {err}")
    let t1 ← IO.monoNanosNow
    timesNs := timesNs.push (t1 - t0)
  let sorted := timesNs.qsort (· < ·)
  let medNs := sorted[3]!
  let medUs := medNs / 1000
  let medMsInt := medUs / 1000
  let medMsFrac := medUs % 1000
  let fracStr :=
    if medMsFrac < 10 then s!"00{medMsFrac}"
    else if medMsFrac < 100 then s!"0{medMsFrac}"
    else s!"{medMsFrac}"
  IO.println s!"MOD={targetModStr} REPLAY_US={medUs} REPLAY_MS={medMsInt}.{fracStr} DECLS={newConsts.size} DAG_NODES={totalDag} TREE_NODES={totalTree} MOD_DECLS={modDecls} MOD_DAG_NODES={modDag} MOD_TREE_NODES={modTree} REPLAYED_MODS={replayedMods.size}"

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot) ["."]
  match args with
  | baseModStr :: targetMods =>
    let baseEnv ← importModules #[{ module := baseModStr.toName }] {}
    for tMod in targetMods do
      measureTarget baseEnv tMod
  | [] =>
    IO.eprintln "Usage: MeasureKernel <BaseModule> <TargetModule1> ..."
    IO.Process.exit 1
