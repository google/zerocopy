-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

open Lean

def allowedAxioms : List Name :=
  [``Classical.choice, ``Quot.sound, ``propext]

def main : IO UInt32 := do
  let sysroot : System.FilePath :=
    "/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1"
  initSearchPath sysroot
    ["/usr/local/google/home/joshlf/.gemini/jetski/brain/4b1fe580-2cc4-422a-bacb-323a44926709/scratch/r2_loops_and_join_vcgen/build"]
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := `LoopAndJoinVCGenProbe }] {} (trustLevel := 0)
  let t1 ← IO.monoMsNow
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut probeDecls : Nat := 0
  let mut probeTheorems : Nat := 0
  let mut usedAxioms : NameSet := {}
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    let modData := env.header.moduleData[idx]!
    let isFoundation := modName == `Init || (`Init).isPrefixOf modName
    if !isFoundation then
      for ci in modData.constants do
        if ci.isUnsafe then
          throw <| IO.userError s!"REJECTED: unsafe declaration {ci.name} in {modName}"
        if ci.isPartial then
          throw <| IO.userError s!"REJECTED: partial declaration {ci.name} in {modName}"
        if ci.isAxiom then
          throw <| IO.userError s!"REJECTED: custom axiom {ci.name} in {modName}"
        locals := locals.insert ci.name ci
        if modName == `LoopAndJoinVCGenProbe then
          probeDecls := probeDecls + 1
          match ci with
          | .thmInfo _ => probeTheorems := probeTheorems + 1
          | _ => pure ()
  -- Check transitive axiom closure of all declarations in LoopAndJoinVCGenProbe
  let mut visited : NameSet := {}
  let mut worklist : Array Name := #[]
  for (n, _) in locals do
    worklist := worklist.push n
  while !worklist.isEmpty do
    let n := worklist.back!
    worklist := worklist.pop
    if !visited.contains n then
      visited := visited.insert n
      let some ci := env.checked.get.find? n
        | throw <| IO.userError s!"missing constant {n}"
      if ci.isAxiom then
        if !allowedAxioms.contains n then
          throw <| IO.userError s!"REJECTED: disallowed axiom {n} (e.g. sorryAx)"
        usedAxioms := usedAxioms.insert n
      for dep in ci.type.getUsedConstants do
        if !visited.contains dep then worklist := worklist.push dep
      if let some val := ci.value? (allowOpaque := true) then
        for dep in val.getUsedConstants do
          if !visited.contains dep then worklist := worklist.push dep
  -- Build foundation-only environment and replay all non-foundation constants
  -- in the kernel
  let mut foundationImports : Array Import := #[]
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modName == `Init || (`Init).isPrefixOf modName then
      foundationImports := foundationImports.push { module := modName }
  let mut prefixLocals : Std.HashMap Name ConstantInfo := {}
  let mut probeOnlyLocals : Std.HashMap Name ConstantInfo := {}
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    let modData := env.header.moduleData[idx]!
    let isFoundation := modName == `Init || (`Init).isPrefixOf modName
    if !isFoundation then
      for ci in modData.constants do
        if modName == `LoopAndJoinVCGenProbe then
          probeOnlyLocals := probeOnlyLocals.insert ci.name ci
        else
          prefixLocals := prefixLocals.insert ci.name ci
  let t2 ← IO.monoMsNow
  let base ← importModules foundationImports {} (trustLevel := 0)
  let t3 ← IO.monoMsNow
  let kenvPrefix ← base.toKernelEnv.replay prefixLocals
  let t4 ← IO.monoMsNow
  let _ ← kenvPrefix.replay probeOnlyLocals
  let t5 ← IO.monoMsNow
  let base2 ← importModules foundationImports {} (trustLevel := 0)
  let t6 ← IO.monoMsNow
  let _ ← base2.toKernelEnv.replay locals
  let t7 ← IO.monoMsNow
  IO.println s!"PASS: LoopAndJoinVCGenProbe kernel & boundary audit succeeded"
  IO.println s!"  LoopAndJoinVCGenProbe decls     : {probeDecls} ({probeTheorems} theorems/lemmas)"
  IO.println s!"  Prefix (Trusted+Anneal) decls   : {prefixLocals.size}"
  IO.println s!"  Total non-foundation replayed   : {locals.size} declarations"
  IO.println s!"  Total reachable constants       : {visited.size}"
  IO.println s!"  Axioms used                     : {usedAxioms.toList}"
  IO.println s!"  Zero isUnsafe/isPartial/isAxiom : true"
  IO.println s!"  Import env time                 : {t1 - t0} ms"
  IO.println s!"  Foundation base import time     : {t3 - t2} ms"
  IO.println s!"  Prefix (Trusted+Anneal) replay  : {t4 - t3} ms"
  IO.println s!"  LoopAndJoinVCGenProbe replay    : {t5 - t4} ms"
  IO.println s!"  Full combined replay time       : {t7 - t6} ms"
  return 0
