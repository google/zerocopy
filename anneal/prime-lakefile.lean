/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lake

open Lake DSL

namespace Anneal

open System

private structure TraceUpdate where
  path : FilePath
  metadata : BuildMetadata

private def TraceUpdate.tempPath (self : TraceUpdate) : FilePath :=
  FilePath.mk <| self.path.toString ++ ".anneal-tmp"

private def getBuildStore : JobM BuildStore :=
  JobM.ofFn fun _ _ _ store _ state => do
    return .ok (← store.get) state

private def verifyArtifactHash (artifact : Artifact) : JobM PUnit := do
  let actualHash ← computeFileHash artifact.path
  unless actualHash == artifact.hash do
    IO.eprintln s!"Lake returned a stale hash for {artifact.path}: expected {artifact.hash}, got {actualHash}"
    error s!"Lake returned a stale hash for {artifact.path}"

private def verifyArtifactHashes (artifacts : ModuleOutputArtifacts) : JobM PUnit := do
  verifyArtifactHash artifacts.olean
  artifacts.oleanServer?.forM verifyArtifactHash
  artifacts.oleanPrivate?.forM verifyArtifactHash
  verifyArtifactHash artifacts.ilean
  artifacts.ir?.forM verifyArtifactHash
  verifyArtifactHash artifacts.c
  artifacts.bc?.forM verifyArtifactHash
  artifacts.ltar?.forM verifyArtifactHash

set_option linter.deprecated false in
private def collectTraceUpdates (ws : Workspace) (store : BuildStore) : JobM (Array TraceUpdate) := do
  let mut updates := #[]
  for ⟨key, familyJob⟩ in store do
    match key with
    | .packageModuleFacet packageName moduleName facet =>
      if h : facet = Module.leanArtsFacet then
        have ofData := by unfold BuildData; simp [h]
        let job : Job ModuleOutputArtifacts := cast ofData familyJob
        let some artifacts ← job.wait? | continue
        let some pkg := ws.findPackageByKey? packageName | continue
        let some mod := pkg.findModule? moduleName | continue
        -- Artifact hashes are checked before publishing the replacement trace.
        verifyArtifactHashes artifacts
        let savedTrace ← readTraceFile mod.traceFile
        let log := match savedTrace with
          | .ok metadata => metadata.log
          | .missing | .invalid => {}
        let metadata := BuildMetadata.ofBuild job.getTrace artifacts.descrs log
        let needsUpdate := match savedTrace with
          | .ok saved => saved.toJson != metadata.toJson
          | .missing | .invalid => true
        if needsUpdate then
          updates := updates.push {path := mod.traceFile, metadata}
    | _ => pure ()
  return updates

private def writeTraceUpdates (updates : Array TraceUpdate) : IO Unit := do
  -- Serialize every replacement before publishing any of them, so a staging
  -- error cannot leave a half-refreshed trace set.
  for update in updates do
    update.metadata.writeFile update.tempPath
  for update in updates do
    IO.FS.rename update.tempPath update.path

/--
Set up one Lean file using Lake's old-mode fallback, then promote the exact
current dependency traces for every module visited by the successful build.

Writes are deliberately deferred until the root build has completed. Updating
a child trace earlier would advance its mtime and could make an old-mode parent
appear older than its inputs before Lake reaches it.
-/
script refreshLakeTraces (args) do
  let ws ← getWorkspace
  let fileName ← match args with
    | [fileName] => pure fileName
    | _ => throw <| IO.userError "expected exactly one Lean file"
  let some path ← resolvePath? fileName
    | throw <| IO.userError s!"file not found: {fileName}"
  let updates ← ws.runBuild (cfg := {oldMode := true, trustHash := false}) do
    (← setupServerModule fileName path none).mapM fun _ => do
      collectTraceUpdates ws (← getBuildStore)
  writeTraceUpdates updates
  IO.println s!"refreshed {updates.size} Lake module traces in one build"
  return 0

end Anneal

require aeneas from "@AENEAS_ROOT@"

package anneal_verification

@[default_target]
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[`Generated]
