-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr

open Lean

def main (args : List String) : IO UInt32 := do
  let [sysrootStr, oleanPath, modNameStr] := args
    | IO.eprintln "usage: ProbeRawModuleDataOverrides <sysroot> <olean-path> <mod-name>"; return 2
  Lean.initSearchPath (System.FilePath.mk sysrootStr) [System.FilePath.mk oleanPath |>.parent.getD (System.FilePath.mk ".")]
  let modName := modNameStr.toName

  -- 1. Read raw ModuleData directly from the .olean file without importing any Environment
  let t0 ← IO.monoNanosNow
  let (rawModData, _region) ← readModuleData (System.FilePath.mk oleanPath)
  let t1 ← IO.monoNanosNow
  IO.println s!"[1] readModuleData took {(t1 - t0).toFloat / 1000000.0} ms"
  IO.println s!"    rawModData.constNames = {rawModData.constNames}"
  IO.println s!"    rawModData.extraConstNames = {rawModData.extraConstNames}"
  for (extName, ents) in rawModData.entries do
    IO.println s!"    rawModData.entries: ext={extName}, size={ents.size}"

  -- 2. Import environment with loadExts := false and NO enableInitializersExecution
  let t2 ← IO.monoNanosNow
  let envFalse ← importModules #[{ module := modName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let t3 ← IO.monoNanosNow
  IO.println s!"[2] importModules (loadExts := false) took {(t3 - t2).toFloat / 1000000.0} ms"

  let some modIdx := envFalse.getModuleIdx? modName
    | throw <| IO.userError s!"module {modName} not found in envFalse"
  let hdrData := envFalse.header.moduleData[modIdx]!
  for (extName, ents) in hdrData.entries do
    IO.println s!"    envFalse.header.moduleData[{modIdx}].entries: ext={extName}, size={ents.size}"

  let implEntries := Compiler.implementedByAttr.ext.getModuleEntries envFalse modIdx
  let extEntries := externAttr.ext.getModuleEntries envFalse modIdx
  let csimpEntries := Compiler.CSimp.ext.ext.getModuleEntries envFalse modIdx
  IO.println s!"    envFalse getModuleEntries: implementedBy={implEntries.size}, extern={extEntries.size}, csimp={csimpEntries.size}"
  for (declName, targetName) in implEntries do
    IO.println s!"      implementedBy entry (loadExts := false): {declName} -> {targetName}"
  for (declName, extData) in extEntries do
    IO.println s!"      extern entry (loadExts := false): {declName} -> {extData.entries.length} entries"
  for scopedEntry in csimpEntries do
    match scopedEntry with
    | .global e =>
      IO.println s!"      csimp global entry (loadExts := false): {e.fromDeclName} -> {e.toDeclName} via {e.thmName}"
    | .scoped ns e =>
      IO.println s!"      csimp scoped entry ({ns}) (loadExts := false): {e.fromDeclName} -> {e.toDeclName} via {e.thmName}"

  -- Also check whether Compiler.getImplementedBy? and getExternAttrData? work directly on envFalse!
  for cname in rawModData.constNames do
    IO.println s!"    envFalse query on {cname}: getImplementedBy?={Compiler.getImplementedBy? envFalse cname}, isExtern={isExtern envFalse cname}"

  return 0
