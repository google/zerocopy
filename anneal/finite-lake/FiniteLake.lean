-- Copyright 2026 The Fuchsia Authors
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.

-- Internal finite preparation only. The parent owns workspace/SDK admission,
-- saved generation, exclusive writer lease, cancellation and process cleanup.
-- Public setup-file and the language server continue using stock Lake.
import Lake
import Lake.Load.Workspace
import Lake.Build.Module
import Lake.Build.Run
import Lake.CLI.Build
import Lake.CLI.Serve
import Lake.Load.Lean.Elab
import Lake.Util.IO

open Lean Lake System

namespace Anneal.FiniteLake

structure SetupRequest where
  fileName : String
  path : String
  header : Option ModuleHeader
  deriving FromJson, Inhabited

structure RootRequest where
  requestId : String
  targets : Array String
  setup : Option SetupRequest
  deriving FromJson, Inhabited

structure Plan where
  protocol : Nat
  opId : String
  configText : String
  manifestText : String
  initialTargets : Array String
  requests : Array RootRequest
  deriving FromJson

def validIdentity (s : String) : Bool :=
  !s.isEmpty && decide (s.utf8ByteSize ≤ 64) && s.toList.all fun c =>
    decide (c.toNat < 128) && (c.isAlphanum || c == '_' || c == '-')

def exactFields (value : Json) (names : List String) : IO Unit := do
  let fields ← IO.ofExcept value.getObj?
  unless fields.size == names.length && fields.toList.all (fun entry => names.contains entry.1) do
    throw <| IO.userError "Unexpected or missing finite protocol fields"

def validatePlan (value : Json) : IO Plan := do
  exactFields value ["protocol", "opId", "configText", "manifestText", "initialTargets", "requests"]
  let roots ← IO.ofExcept (value.getObjVal? "requests" >>= Json.getArr?)
  for root in roots do
    exactFields root ["requestId", "targets", "setup"]
    let setup ← IO.ofExcept (root.getObjVal? "setup")
    if setup != Json.null then exactFields setup ["fileName", "path", "header"]
  let plan : Plan ← IO.ofExcept (fromJson? value)
  unless plan.protocol == 1 && validIdentity plan.opId do
    throw <| IO.userError "Unsupported finite protocol or operation identity"
  if plan.requests.size > 32 || plan.initialTargets.size > 8 then
    throw <| IO.userError "Finite plan exceeds 32 roots or 8 initial targets"
  let mut seen : Array String := #[]
  for request in plan.requests do
    unless validIdentity request.requestId && !seen.contains request.requestId do
      throw <| IO.userError "Invalid or duplicate finite root identity"
    if request.targets.size > 8 then throw <| IO.userError "Finite root exceeds 8 targets"
    seen := seen.push request.requestId
  return plan

def readPlan : IO Json := do
  let input ← IO.getStdin
  let mut bytes := ByteArray.empty
  repeat
    let chunk ← input.read (min 65536 (1048577 - bytes.size)).toUSize
    bytes := bytes ++ chunk
    if bytes.size > 1048576 then throw <| IO.userError "Finite plan exceeds 1MiB encoded input"
    if chunk.isEmpty then break
  let some text := String.fromUTF8? bytes
    | throw <| IO.userError "Finite plan is not UTF-8"
  IO.ofExcept (Json.parse text)

-- Bound the complete summary, including its explicit truncation notice, by
-- UTF-8 bytes. JSON's worst six-byte escaping stays below the 64KiB wire cap.
def errorSummary (text : String) : String × Bool := Id.run do
  if text.utf8ByteSize ≤ 8192 then return (if text.isEmpty then "Unknown Lake failure" else text, false)
  let notice := " [truncated; full error on stderr]"
  let mut fragment := ""
  for c in text.toList do
    if fragment.utf8ByteSize + c.utf8Size > 8192 - notice.utf8ByteSize then break
    fragment := fragment.push c
  return (fragment ++ notice, true)

def emit (opId event : String) (fields : List (String × Json)) : IO Unit := do
  let value := Json.mkObj ([("protocol", toJson (1 : Nat)), ("opId", toJson opId),
    ("event", toJson event)] ++ fields)
  let encoded := value.compress ++ "\n"
  if encoded.utf8ByteSize > 65536 then throw <| IO.userError "Finite status record exceeds 64KiB"
  let out ← IO.getStdout
  out.putStr encoded
  out.flush

def errorFields (err : IO.Error) : IO (List (String × Json)) := do
  let text := err.toString
  IO.eprintln text
  let (summary, truncated) := errorSummary text
  return [("error", toJson summary), ("errorTruncated", toJson truncated)]

def buildTargets (ws : Workspace) (targets : Array String) : IO Unit := do
  unless targets.isEmpty do
    let specs ← (parseTargetSpecs ws targets.toList).toIO (fun err => IO.userError err.toString)
    for spec in specs do
      unless spec.buildable do
        throw <| IO.userError s!"Nonbuildable target: {spec.info.key.toSimpleString}"
    -- Each root group gets a fresh context, job store, queue and monitor.
    ws.runBuild (buildSpecs specs)

def runPlan (workspace : String) (plan : Plan) : IO UInt32 := do
  let root ← Lake.resolvePath (FilePath.mk workspace)
  -- Exact parent-rendered config and existing empty manifest precede all Lake
  -- configuration loading. Never repair/materialize dependencies or toolchains.
  let manifestText ← IO.FS.readFile (root / "lake-manifest.json")
  let manifest ← IO.ofExcept (Json.parse manifestText)
  let packages ← IO.ofExcept (manifest.getObjVal? "packages" >>= Json.getArr?)
  let version ← IO.ofExcept (manifest.getObjVal? "version" >>= Json.getStr?)
  unless packages.isEmpty && version == "1.2.0" && manifestText == plan.manifestText do
    throw <| IO.userError "Generated empty manifest admission failed"
  unless (← IO.FS.readFile (root / "lakefile.lean")) == plan.configText do
    throw <| IO.userError "Generated configuration admission failed"
  let some sysroot ← IO.getEnv "LEAN_SYSROOT"
    | throw <| IO.userError "Admitted LEAN_SYSROOT is required"
  let lean ← LeanInstall.get (FilePath.mk sysroot) (collocated := true)
  let lake := LakeInstall.ofLean lean
  let env ← match ← (Env.compute lake lean none (some true)).toBaseIO with
    | .ok env => pure env
    | .error err => throw <| IO.userError err
  let cfg : LoadConfig := {
    lakeEnv := env, wsDir := root, lakeArgs? := none,
    reconfigure := false, updateDeps := false, updateToolchain := false
  }
  if let some err ← IO.getEnv invalidConfigEnvVar then throw <| IO.userError err
  let configFile ← realConfigFile cfg.configFile
  let some ws ← (loadWorkspace cfg).toBaseIO
    | throw <| IO.userError "Failed to load generated Lake workspace; see stderr"
  unless ws.root.depConfigs.isEmpty do
    throw <| IO.userError "Generated configuration unexpectedly has dependencies"
  emit plan.opId "load" [("outcome", toJson "loaded")]
  let mut failed := false
  if !plan.initialTargets.isEmpty then
    try
      buildTargets ws plan.initialTargets
      emit plan.opId "initial" [("outcome", toJson "built")]
    catch err =>
      failed := true
      emit plan.opId "initial" ([("outcome", toJson "buildFailed")] ++ (← errorFields err))
  for index in [:plan.requests.size] do
    let request := plan.requests[index]!
    let identity := [("index", toJson index), ("requestId", toJson request.requestId)]
    -- Catch build and setup separately: the parent retains each root's exact
    -- disposition and the independent next root gets fresh ws.runBuild state.
    let built ← try
      buildTargets ws request.targets
      pure true
    catch err =>
      failed := true
      emit plan.opId "root" (identity ++ [("outcome", toJson "buildFailed")] ++ (← errorFields err))
      pure false
    if built then
      if let some setup := request.setup then
        try
          let path ← Lake.resolvePath (FilePath.mk setup.path)
          -- Preserve stock setup-file's admitted config-module special case.
          -- Ordinary roots await typed setup success without serializing it.
          let _ : ModuleSetup ← if path == configFile then
            pure { name := configModuleName, plugins := #[env.lake.sharedLib] }
          else ws.runBuild (setupServerModule setup.fileName path setup.header)
          emit plan.opId "root" (identity ++ [("outcome", toJson "prepared")])
        catch err =>
          failed := true
          emit plan.opId "root" (identity ++ [("outcome", toJson "setupFailed")] ++ (← errorFields err))
      else emit plan.opId "root" (identity ++ [("outcome", toJson "buildOnly")])
  emit plan.opId "complete" [("count", toJson plan.requests.size), ("failed", toJson failed)]
  return if failed then (1 : UInt32) else (0 : UInt32)

end Anneal.FiniteLake

def main (args : List String) : IO UInt32 := do
  let mut opId := "invalid"
  try
    let value ← Anneal.FiniteLake.readPlan
    if let .ok identity := value.getObjVal? "opId" >>= Json.getStr? then
      if Anneal.FiniteLake.validIdentity identity then opId := identity
    let plan ← Anneal.FiniteLake.validatePlan value
    match args with
    | [workspace] => Anneal.FiniteLake.runPlan workspace plan
    | _ => throw <| IO.userError "anneal-finite-lake WORKSPACE_ROOT requires one argument"
  catch err =>
    Anneal.FiniteLake.emit opId "fatal" (← Anneal.FiniteLake.errorFields err)
    return (2 : UInt32)
