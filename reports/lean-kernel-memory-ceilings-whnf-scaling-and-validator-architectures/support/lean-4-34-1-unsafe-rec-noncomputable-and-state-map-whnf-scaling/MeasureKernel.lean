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

def exprDagNodes (e : Expr) : IO Nat := do
  let (_, st) ← StateT.run (go e) (Std.HashSet.emptyWithCapacity 256)
  return st.size
where
  go (e : Expr) : StateT (Std.HashSet UInt64) IO Unit := do
    let h := e.hash
    if (← get).contains h then
      return ()
    modify (·.insert h)
    match e with
    | .app f a => go f; go a
    | .lam _ d b _ => go d; go b
    | .forallE _ d b _ => go d; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => return ()

unsafe def measureModule (baseEnv : Environment) (modNameStr : String) :
    IO Unit := do
  let modName := modNameStr.toName
  let env ← importModules #[{ module := modName }] {}
  let some modIdx := env.getModuleIdx? modName | do
    IO.eprintln s!"Module {modName} not found"
    return ()
  let decls := env.header.moduleData[modIdx.toNat]!.constants
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut totalDag : Nat := 0
  for ci in decls do
    newConsts := newConsts.insert ci.name ci
    let tyNodes ← exprDagNodes ci.type
    let valNodes ← match ci.value? (allowOpaque := true) with
      | some v => exprDagNodes v
      | none => pure 0
    totalDag := totalDag + tyNodes + valNodes
  let mut times : Array Float := #[]
  for _ in [0:5] do
    let t0 ← IO.monoNanosNow
    let _ ← (baseEnv.toKernelEnv.replay newConsts).toIO
      (fun err => IO.userError s!"Kernel replay error in {modName}: {err}")
    let t1 ← IO.monoNanosNow
    times := times.push ((t1 - t0).toFloat / 1000000.0)
  let sorted := times.qsort (· < ·)
  let medianMs := sorted[2]!
  IO.println s!"{modNameStr}\tREPLAY_MS={medianMs}\tDAG_NODES={totalDag}\tDECLS={decls.size}"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | searchPathStr :: modNames =>
    initSearchPath (← findSysroot) [System.FilePath.mk searchPathStr]
    let baseEnv ← importModules #[{ module := `BenchCommon }] {}
    for m in modNames do
      measureModule baseEnv m
    return 0
  | [] =>
    IO.eprintln "Usage: MeasureKernel <SearchPath> <Mod1> <Mod2> ..."
    return 1
