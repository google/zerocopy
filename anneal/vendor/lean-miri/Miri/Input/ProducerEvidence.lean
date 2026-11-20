import Miri.Input.Decoder

/-! Explicit MIR producer settings and consumed-artifact identities. Source:
Miri lib.rs::MIRI_DEFAULT_ARGS (190-211), bin/miri.rs driver setup; exporter
producer.rs records actual compiler session settings and hashes the consumed
crate artifacts. Comparison to a reference is conditional on that reference's
provenance; it does not certify Rust behavior or establish UB freedom. -/
namespace Miri.Input.ProducerEvidence
open Lean
abbrev Result := Except String
structure Artifact where
  path : String
  crateName : String
  kind : String
  sha256 : String
  sizeBytes : Nat
  withinSysroot : Bool
  sysrootRelativePath : Option String
structure Settings where
  sysrootPath : String
  sysrootManifestSha256 : String
  loadedArtifactsManifestSha256 : String
  requestedCfgMiri : Bool
  miriDefaultArgs : Array String
  rustcArgs : Array String
  effectivePanicStrategy : String
  requestedMirOptLevel : Option Nat
  mirEnablePasses : Array (String × Bool)
  mirPreserveUb : Bool
  extraConstUbChecks : Bool
  alwaysEncodeMir : Bool
  deduplicateDiagnostics : Bool
  artifacts : Array Artifact
  originalPayload : Json

private def field (j : Json) (key : String) : Result Json := j.getObjVal? key
private def string (j : Json) (key : String) : Result String := do (← field j key).getStr?
private def boolean (j : Json) (key : String) : Result Bool := do (← field j key).getBool?
private def natural (j : Json) (key : String) : Result Nat := do (← field j key).getNat?
private def strings (j : Json) (key : String) : Result (Array String) := do
  (← (← field j key).getArr?).mapM Json.getStr?
private def optionalString (j : Json) (key : String) : Result (Option String) := do
  match ← field j key with
  | .null => pure none
  | value => value.getStr?.map some
private def digest (j : Json) (key : String) : Result String := do
  let value ← string j key
  unless value.length == 64 && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do
    throw s!"invalid SHA256 evidence in {key}"
  pure value
private def artifact (j : Json) : Result Artifact := do
  unless (← string j "status") == "supported" do throw "consumed-artifact hash evidence is incomplete"
  pure {
    path := ← string j "path", crateName := ← string j "crate_name", kind := ← string j "kind"
    sha256 := ← digest j "sha256", sizeBytes := ← natural j "size_bytes"
    withinSysroot := ← boolean j "within_sysroot"
    sysrootRelativePath := ← optionalString j "sysroot_relative_path" }

def ofDocument (document : ImportDocumentCore) : Result Settings := do
  let value ← field (← field document.raw "producer") "input_settings"
  unless (← string value "status") == "supported" do throw "producer settings/artifact identity evidence is incomplete"
  unless (← string value "hash_algorithm") == "sha256" do throw "unrecognized producer fingerprint algorithm"
  let level ← match ← field value "mir_opt_level" with
    | .null => pure none
    | value => value.getNat?.map some
  let passes ← (← (← field value "mir_enable_passes").getArr?).mapM fun entry => do
    let values ← entry.getArr?
    unless values.size == 2 do throw "invalid MIR pass setting evidence"
    let some name := values[0]? | throw "MIR pass name missing"
    let some enabled := values[1]? | throw "MIR pass setting missing"
    pure (← name.getStr?,← enabled.getBool?)
  pure {
    sysrootPath := ← string value "sysroot_path"
    sysrootManifestSha256 := ← digest value "sysroot_manifest_sha256"
    loadedArtifactsManifestSha256 := ← digest value "loaded_artifacts_manifest_sha256"
    requestedCfgMiri := ← boolean value "requested_cfg_miri"
    miriDefaultArgs := ← strings value "miri_default_args", rustcArgs := ← strings value "rustc_args"
    effectivePanicStrategy := ← string value "effective_panic_strategy", requestedMirOptLevel := level
    mirEnablePasses := passes, mirPreserveUb := ← boolean value "mir_preserve_ub"
    extraConstUbChecks := ← boolean value "extra_const_ub_checks", alwaysEncodeMir := ← boolean value "always_encode_mir"
    deduplicateDiagnostics := ← boolean value "deduplicate_diagnostics"
    artifacts := ← (← (← field value "artifacts").getArr?).mapM artifact
    originalPayload := value }

def pinnedMiriDefaultArgs : Array String := #[
  "--cfg=miri", "-Zalways-encode-mir", "-Zextra-const-ub-checks", "-Zmir-preserve-ub",
  "-Zmir-opt-level=0", "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
  "-Zmir-enable-passes=-ReferencePropagation,-GVN", "-Zdeduplicate-diagnostics=no"]

/-- Retain every explicit cfg argument in its original compiler syntax.
This does not infer built-in target cfgs from a target triple. -/
def requestedCfgs (settings : Settings) : Array String := Id.run do
  let mut values := #[]
  let mut pending := false
  for arg in settings.rustcArgs do
    if pending then values := values.push arg; pending := false
    else if arg == "--cfg" then pending := true
    else if arg.startsWith "--cfg=" then values := values.push (arg.drop 6).toString
  return values

/-- Compare actual producer inputs to an independently pinned reference.
Reference trust and source-to-MIR correctness remain explicit external
assumptions. Both sysroot and non-sysroot consumed artifacts must match. -/
def compareReferenceInputs (actual reference : Settings) : Result Unit := do
  unless actual.miriDefaultArgs == pinnedMiriDefaultArgs && reference.miriDefaultArgs == pinnedMiriDefaultArgs do
    throw "producer does not record the pinned Miri default arguments"
  unless actual.requestedCfgMiri && reference.requestedCfgMiri do throw "cfg(miri) was not requested for both producers"
  unless requestedCfgs actual == requestedCfgs reference do throw "producer cfg inputs differ"
  unless actual.requestedMirOptLevel == some 0 && reference.requestedMirOptLevel == some 0 do
    throw "producer MIR optimization settings do not match supported pinned configuration"
  unless actual.mirPreserveUb && actual.extraConstUbChecks && actual.alwaysEncodeMir && !actual.deduplicateDiagnostics do
    throw "actual producer does not preserve required Miri MIR settings"
  unless reference.mirPreserveUb && reference.extraConstUbChecks && reference.alwaysEncodeMir && !reference.deduplicateDiagnostics do
    throw "reference does not preserve required Miri MIR settings"
  unless actual.mirEnablePasses == reference.mirEnablePasses do throw "producer MIR pass overrides differ"
  unless actual.effectivePanicStrategy == reference.effectivePanicStrategy do throw "producer panic strategies differ"
  unless actual.sysrootManifestSha256 == reference.sysrootManifestSha256 do throw "producer sysroot artifact manifests differ"
  unless actual.loadedArtifactsManifestSha256 == reference.loadedArtifactsManifestSha256 do throw "producer consumed dependency artifacts differ"

end Miri.Input.ProducerEvidence
