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
unsafe def main (args : List String) : IO Unit := do
  let modName := args[0]!.toName
  initSearchPath (System.FilePath.mk args[1]!)
  enableInitializersExecution
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0) (loadExts := true)
  let modIdx := env.getModuleIdx? modName |>.get!
  let modData := env.header.moduleData[modIdx.toNat]!
  let baseWithAll := env.toKernelEnv
  for cinfo in modData.constants do
    if cinfo matches .thmInfo _ then
      let t0 ← IO.monoNanosNow
      match baseWithAll.addDecl {} (.thmDecl {
        name := cinfo.name ++ `_bench_copy
        levelParams := cinfo.levelParams
        type := cinfo.type
        value := cinfo.value! (allowOpaque := true)
      }) with
      | .ok _ =>
        let t1 ← IO.monoNanosNow
        let ms := (t1 - t0).toFloat / 1000000.0
        if true then
          IO.println s!"{ms}ms: {cinfo.name}"
      | .error _ => IO.println s!"ERR: {cinfo.name}"
