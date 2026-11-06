import AnnealResearch.Post96Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.Post96NativeConsumer

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.PR86AuditRepairs
open AnnealResearch.Post96Consumer
open AnnealResearch.StatefulGenericLibraryH3H7

/-- Native records have separate provenance from every retained Linux family. The producer
    reports compiler completion; an outer manifest/process owner must establish freshness. -/
inductive NativeTypeKind where
  | unit | bool | u32 | usize | scalarPair | rawPtrU32
  deriving DecidableEq, Repr

structure NativeTypeRecord where
  key : String
  kind : NativeTypeKind
  defPathHash : Option (Nat × Nat)
  fieldKeys : List String
  sizeBytes : Nat
  alignBytes : Nat
  fieldOffsets : List Nat
  isSized : Bool
  reprC : Bool
  packedAlignment : Option Nat
  explicitAlignment : Option Nat
  deriving DecidableEq, Repr

structure NativeBodyKey where
  key : String
  defPathHash : Nat × Nat
  handle : Nat
  localKeys : List String
  deriving DecidableEq, Repr

structure NativeSourceClaim where
  reportedPath : String
  reportedByteCount : Nat
  deriving DecidableEq, Repr

structure NativeContext where
  crateName : String
  targetTriple : List Nat
  svh : Nat × Nat
  pointerWidth : Nat
  sources : List NativeSourceClaim
  deriving DecidableEq, Repr

inductive NativeSubjectKind where
  | nativeScalar | nativePointer
  deriving DecidableEq, Repr

structure NativeEnvelope where
  kind : NativeSubjectKind
  schemaVersion : Nat
  rawSha256 : String
  context : NativeContext
  compilerCompletedReported : Bool
  entryKey : String
  entryHandle : Nat
  typeRecords : List NativeTypeRecord
  bodyKeys : List NativeBodyKey
  bodies : List WireBody
  deriving DecidableEq, Repr

structure ExpectedNative where
  kind : NativeSubjectKind
  rawSha256 : String
  context : NativeContext
  entryKey : String
  deriving DecidableEq, Repr

def carrierType : NativeTypeKind → MirTypeTag
  | .unit => .unit
  | .bool => .bool
  | .u32 => .u32
  | .usize => .usize
  | .scalarPair => .effectLog
  | .rawPtrU32 => .rawPtrU32

/-- `.effectLog` is only the existing two-scalar carrier for this bounded adapter, not a
    claim that the native nominal struct is EffectLog. Full native keys remain above. -/
def findNativeType (types : List NativeTypeRecord) (key : String) : Option NativeTypeRecord :=
  types.find? (fun t => t.key == key)

def nativeDefinitionKey (fp : Nat × Nat) : String :=
  s!"DefPathHash(Fingerprint({fp.1}, {fp.2}))"

def checkNativeType (types : List NativeTypeRecord) (t : NativeTypeRecord) : Bool :=
  t.isSized &&
  match t.kind with
  | .unit => (t.key == "unit") && (t.sizeBytes == 0) && (t.alignBytes == 1) && t.fieldKeys.isEmpty && t.fieldOffsets.isEmpty
  | .bool => (t.key == "bool") && (t.sizeBytes == 1) && (t.alignBytes == 1) && t.fieldKeys.isEmpty && t.fieldOffsets.isEmpty
  | .u32 => (t.key == "u32") && (t.sizeBytes == 4) && (t.alignBytes == 4) && t.fieldKeys.isEmpty && t.fieldOffsets.isEmpty
  | .usize => (t.key == "usize") && (t.sizeBytes == 8) && (t.alignBytes == 8) && t.fieldKeys.isEmpty && t.fieldOffsets.isEmpty
  | .rawPtrU32 => (t.key == "raw:Not:u32") && (t.sizeBytes == 8) && (t.alignBytes == 8) && t.fieldKeys.isEmpty && t.fieldOffsets.isEmpty
  | .scalarPair =>
      (match t.defPathHash with
       | none => false
       | some fp => t.key == "adt:" ++ nativeDefinitionKey fp) && t.reprC && (t.packedAlignment == none) && (t.explicitAlignment == none) &&
      (t.fieldKeys == ["u32", "u32"]) &&
      match findNativeType types "u32" with
      | none => false
      | some u =>
          match accumReprCFields none [(u.sizeBytes, u.alignBytes), (u.sizeBytes, u.alignBytes)] [] 0 1 with
          | none => false
          | some (offsets, endOff, align) =>
              (t.fieldOffsets == offsets) && (t.alignBytes == align) &&
              (t.sizeBytes == alignUpTo endOff align)

def checkNativeTypes (e : NativeEnvelope) : Bool :=
  (e.context.pointerWidth == 64) && !e.typeRecords.isEmpty &&
  (e.typeRecords.map (·.key)).eraseDups.length == e.typeRecords.length &&
  e.typeRecords.all (checkNativeType e.typeRecords) &&
  (match e.kind with
   | .nativeScalar => !(e.typeRecords.any (fun t => t.kind == .rawPtrU32))
   | .nativePointer => e.typeRecords.any (fun t => t.kind == .rawPtrU32))

def checkNativeBodyKey (e : NativeEnvelope) (k : NativeBodyKey) (b : WireBody) : Bool :=
  (k.key == nativeDefinitionKey k.defPathHash) &&
  Nat.ble 128 k.handle && Nat.ble k.handle 159 && (b.bodyId == k.handle) && (b.symId == k.handle) &&
  (b.originKind == .localOwner) && (b.mirPhase == .runtimePostCleanup) &&
  (k.localKeys.length == b.localTypes.length) &&
  (k.localKeys.mapM (fun key => (findNativeType e.typeRecords key).map (fun t => carrierType t.kind)) == some b.localTypes)

def checkNativeKeys (e : NativeEnvelope) : Bool :=
  (e.bodyKeys.length == e.bodies.length) &&
  (e.bodyKeys.map (·.key)).eraseDups.length == e.bodyKeys.length &&
  (e.bodyKeys.map (·.handle)).eraseDups.length == e.bodyKeys.length &&
  ((e.bodyKeys.zip e.bodies).all (fun kb => checkNativeBodyKey e kb.1 kb.2)) &&
  e.bodyKeys.any (fun k => (k.key == e.entryKey) && (k.handle == e.entryHandle))

/-- Consumer-created AMIR bridge. Its flags express only this adapter's closed selected
    graph. The native producer did not emit AMIR or report preserved-UB/UB-check settings. -/
def bridgeBytes (e : NativeEnvelope) : List Nat :=
  let fp := computeCargoPayloadFp16 (asciiCrateBytes e.context.crateName)
    (specEncodeBodiesCons e.bodies)
  specEncodePackage { version := 3, defaultPhase := .runtimePostCleanup, monoComplete := true, preserveUb := false, ubChecks := false, fpHi := fp.1, fpLo := fp.2, bodies := e.bodies }

def checkNativeIdentity (expected : ExpectedNative) (e : NativeEnvelope) : Bool :=
  (e.schemaVersion == 1) && (e.kind == expected.kind) && (e.rawSha256 == expected.rawSha256) &&
  (e.context == expected.context) && (e.entryKey == expected.entryKey) &&
  checkAsciiCrateName e.context.crateName && e.compilerCompletedReported

def checkNative (expected : ExpectedNative) (e : NativeEnvelope) : Bool :=
  checkNativeIdentity expected e && checkNativeTypes e && checkNativeKeys e &&
  isAdmittedPackageBytes (bridgeBytes e) &&
  (decodePackageBodies (bridgeBytes e) == e.bodies) && checkRuntimeClosedBodies e.bodies

structure AcceptedNative where
  envelope : NativeEnvelope
  bodies : List WireBody
  deriving DecidableEq, Repr

def acceptNative (expected : ExpectedNative) (e : NativeEnvelope) : Option AcceptedNative :=
  bif checkNative expected e then some { envelope := e, bodies := e.bodies } else none

theorem checkNative_sound (expected : ExpectedNative) (e : NativeEnvelope)
    (h : checkNative expected e = true) :
    checkNativeIdentity expected e = true ∧ checkNativeTypes e = true ∧
    checkNativeKeys e = true ∧ isAdmittedPackageBytes (bridgeBytes e) = true ∧
    decodePackageBodies (bridgeBytes e) = e.bodies ∧ checkRuntimeClosedBodies e.bodies = true := by
  unfold checkNative at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hi, ht⟩, hk⟩, ha⟩, hd⟩, hc⟩
  exact ⟨hi, ht, hk, ha, beq_iff_eq.mp hd, hc⟩

theorem acceptNative_sound (expected : ExpectedNative) (e : NativeEnvelope) (a : AcceptedNative)
    (h : acceptNative expected e = some a) :
    a.envelope = e ∧ a.bodies = e.bodies ∧
    checkNativeIdentity expected e = true ∧ checkNativeTypes e = true ∧
    checkNativeKeys e = true ∧ isAdmittedPackageBytes (bridgeBytes e) = true ∧
    decodePackageBodies (bridgeBytes e) = e.bodies ∧ checkRuntimeClosedBodies e.bodies = true := by
  unfold acceptNative at h
  cases hc : checkNative expected e with
  | false => rw [hc] at h; contradiction
  | true =>
      rw [hc] at h
      injection h with hh
      subst a
      exact ⟨rfl, rfl, checkNative_sound expected e hc⟩

#print axioms acceptNative_sound

end AnnealResearch.Post96NativeConsumer
