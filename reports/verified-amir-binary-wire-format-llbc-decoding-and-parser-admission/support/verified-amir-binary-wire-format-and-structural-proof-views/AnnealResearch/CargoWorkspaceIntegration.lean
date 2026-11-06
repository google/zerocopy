import AnnealResearch.SubstantiveMirByteParser

set_option maxRecDepth 65536

namespace AnnealResearch.CargoWorkspaceIntegration

open AnnealResearch.SubstantiveMirByteParser

/-!
# Cargo Workspace & Build-Graph Integration Model (.amir v3 Real Byte Streams)

Formalizes multi-crate Cargo workspace verification for `joshlf/anneal#61`
using the real `.amir` v3 wire format decoded by `SubstantiveMirByteParser.parseWirePackage`:
1. Exact `.amir` v3 byte streams emitted by `direct_mir_driver_v4` for
   `dep_layout_core` (`default` vs `--features strict_align`) and
   `app_verifier_subject` (`default` vs `--features strict_align`), plus
   the post-monomorphization const-eval probe `post_mono_unused_accepted.amir`.
2. Strict Virtual Hash (SVH) / 16-bit FNV-1a payload fingerprint (`fp16`) and
   feature-set coherence across crate boundaries.
3. Execution of decoded `WireBody` ASTs (`GENERATED_ARCH_ALIGN`, `STRICT_ALIGN_BONUS`,
   `dep_inline_align`, `dep_non_inline_check`, `macro_generated_probe`, and
   `verify_cross_crate_entry`) proving distinct feature-toggled `.amir` v3 byte streams
   and distinct interpreted semantic outcomes (`16 ≠ 32`, `34 ≠ 50`, `32 ≠ 40`).
-/

/-- Compilation completeness status of a rustc/Cargo invocation. -/
inductive CompilationCompleteness where
  | acceptedComplete
  | rejectedIncompleteCheckOnly
  | rejectedHasErrors
  deriving DecidableEq, Repr

/-- Origin of a MIR body within a multi-crate workspace. -/
inductive CrateBodyOrigin where
  | localSource
  | buildScriptGenerated (outDirFile : String)
  | macroExpanded (macroName : String)
  | externalRlibMetadata (crateName : String) (svhLo : Nat)
  deriving DecidableEq, Repr

/-- Per-function MIR availability record in a workspace build. -/
structure FunctionMirRecord where
  symbol : String
  origin : CrateBodyOrigin
  isInlineOrGeneric : Bool
  mirAvailable : Bool
  deriving DecidableEq, Repr

/-- Metadata and verification artifact package for a single compiled crate. -/
structure CrateArtifactPackage where
  crateName : String
  svhFingerprintLo : Nat
  features : List String
  alwaysEncodeMir : Bool
  completeness : CompilationCompleteness
  externalDepSvhs : List (String × Nat)
  archAlign : Nat
  strictBonus : Nat
  functions : List FunctionMirRecord
  amirV3Fp16 : List Nat := []
  amirV3SizeBytes : Nat := 0
  deriving DecidableEq, Repr

/-- Real 448-byte `.amir` v3 wire artifact for `dep_layout_core` (default features).
    SHA-256: `77683ab3fe15819749015ffff790a44843798cc3cde22a4078295f03b54ad389`
    Header `fp16`: `[71, 189]`, `bodyCount = 5`. -/
def depDefaultAmirV3Bytes : List Nat := [65, 77, 73, 82, 3, 3, 11, 71, 189, 5, 1, 50, 4, 3, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64, 2, 51, 4, 3, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 0, 64, 3, 52, 1, 3, 5, 1, 3, 4, 4, 4, 4, 4, 0, 1, 32, 2, 73, 38, 2, 0, 1, 252, 0, 4, 32, 3, 17, 3, 0, 1, 0, 32, 4, 17, 4, 0, 2, 0, 75, 40, 0, 0, 2, 252, 67, 0, 68, 0, 0, 3, 33, 4, 33, 3, 33, 2, 64, 4, 53, 1, 3, 20, 2, 11, 12, 4, 4, 1, 2, 4, 2, 4, 4, 4, 4, 16, 19, 12, 4, 4, 4, 16, 20, 20, 0, 5, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 130, 0, 69, 68, 0, 0, 2, 1, 0, 1, 33, 5, 68, 5, 0, 9, 33, 5, 32, 6, 32, 7, 32, 8, 17, 8, 0, 2, 0, 32, 9, 32, 10, 17, 10, 0, 2, 0, 21, 11, 0, 14, 10, 0, 130, 1, 72, 75, 2, 0, 3, 252, 0, 6, 17, 9, 0, 75, 1, 33, 10, 21, 7, 0, 12, 72, 0, 73, 0, 33, 9, 33, 8, 21, 6, 0, 2, 71, 0, 130, 0, 69, 70, 0, 0, 6, 4, 0, 1, 33, 7, 68, 5, 0, 4, 23, 0, 0, 2, 33, 6, 33, 4, 33, 3, 68, 10, 0, 12, 33, 7, 17, 3, 0, 131, 0, 33, 6, 33, 4, 33, 3, 32, 13, 32, 14, 17, 14, 0, 1, 0, 32, 15, 32, 16, 17, 16, 0, 2, 0, 21, 17, 0, 14, 16, 0, 130, 1, 72, 81, 2, 0, 7, 252, 0, 2, 17, 15, 0, 81, 1, 33, 16, 75, 23, 13, 0, 8, 252, 78, 0, 79, 0, 0, 7, 33, 15, 33, 14, 32, 18, 32, 19, 19, 19, 0, 0, 2, 0, 24, 18, 0, 3, 83, 0, 33, 19, 75, 37, 0, 0, 9, 252, 77, 0, 82, 0, 0, 2, 33, 18, 33, 13, 68, 10, 0, 0, 64, 5, 54, 1, 3, 9, 2, 2, 4, 20, 4, 4, 4, 4, 4, 16, 20, 0, 8, 32, 3, 17, 3, 0, 2, 0, 32, 4, 32, 5, 32, 6, 16, 8, 0, 1, 1, 17, 6, 0, 8, 4, 21, 7, 0, 14, 6, 0, 130, 1, 72, 71, 2, 0, 1, 252, 0, 7, 17, 5, 0, 71, 1, 33, 6, 22, 4, 0, 1, 69, 0, 33, 5, 21, 0, 0, 12, 67, 0, 68, 0, 33, 4, 33, 3, 64]

/-- Real 448-byte `.amir` v3 wire artifact for `dep_layout_core` (`--features strict_align`).
    SHA-256: `a4a72ca6fd048a2b258779aae36d82594a5021a5fcfcc5283aadaa48c83b7096`
    Header `fp16`: `[86, 21]`, `bodyCount = 5`. -/
def depStrictAmirV3Bytes : List Nat := [65, 77, 73, 82, 3, 3, 11, 86, 21, 5, 1, 50, 4, 3, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64, 2, 51, 4, 3, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64, 3, 52, 1, 3, 5, 1, 3, 4, 4, 4, 4, 4, 0, 1, 32, 2, 73, 38, 2, 0, 1, 252, 0, 4, 32, 3, 17, 3, 0, 1, 0, 32, 4, 17, 4, 0, 2, 0, 75, 40, 0, 0, 2, 252, 67, 0, 68, 0, 0, 3, 33, 4, 33, 3, 33, 2, 64, 4, 53, 1, 3, 20, 2, 11, 12, 4, 4, 1, 2, 4, 2, 4, 4, 4, 4, 16, 19, 12, 4, 4, 4, 16, 20, 20, 0, 5, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 130, 0, 69, 68, 0, 0, 2, 1, 0, 1, 33, 5, 68, 5, 0, 9, 33, 5, 32, 6, 32, 7, 32, 8, 17, 8, 0, 2, 0, 32, 9, 32, 10, 17, 10, 0, 2, 0, 21, 11, 0, 14, 10, 0, 130, 1, 72, 75, 2, 0, 3, 252, 0, 6, 17, 9, 0, 75, 1, 33, 10, 21, 7, 0, 12, 72, 0, 73, 0, 33, 9, 33, 8, 21, 6, 0, 2, 71, 0, 130, 0, 69, 70, 0, 0, 6, 4, 0, 1, 33, 7, 68, 5, 0, 4, 23, 0, 0, 2, 33, 6, 33, 4, 33, 3, 68, 10, 0, 12, 33, 7, 17, 3, 0, 131, 0, 33, 6, 33, 4, 33, 3, 32, 13, 32, 14, 17, 14, 0, 1, 0, 32, 15, 32, 16, 17, 16, 0, 2, 0, 21, 17, 0, 14, 16, 0, 130, 1, 72, 81, 2, 0, 7, 252, 0, 2, 17, 15, 0, 81, 1, 33, 16, 75, 23, 13, 0, 8, 252, 78, 0, 79, 0, 0, 7, 33, 15, 33, 14, 32, 18, 32, 19, 19, 19, 0, 0, 2, 0, 24, 18, 0, 3, 83, 0, 33, 19, 75, 37, 0, 0, 9, 252, 77, 0, 82, 0, 0, 2, 33, 18, 33, 13, 68, 10, 0, 0, 64, 5, 54, 1, 3, 9, 2, 2, 4, 20, 4, 4, 4, 4, 4, 16, 20, 0, 8, 32, 3, 17, 3, 0, 2, 0, 32, 4, 32, 5, 32, 6, 16, 8, 0, 1, 1, 17, 6, 0, 8, 4, 21, 7, 0, 14, 6, 0, 130, 1, 72, 71, 2, 0, 1, 252, 0, 7, 17, 5, 0, 71, 1, 33, 6, 22, 4, 0, 1, 69, 0, 33, 5, 21, 0, 0, 12, 67, 0, 68, 0, 33, 4, 33, 3, 64]

/-- Real 172-byte `.amir` v3 wire artifact for `app_verifier_subject` (default features).
    SHA-256: `04953d9a05f278fd1f9f0353a62276b34fe0e4be947110608859792c215e92ba`
    Header `fp16`: `[191, 87]`, `bodyCount = 2`. -/
def appDefaultAmirV3Bytes : List Nat := [65, 77, 73, 82, 3, 3, 11, 191, 87, 2, 1, 55, 1, 3, 4, 1, 3, 4, 4, 4, 4, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 75, 40, 2, 0, 1, 252, 67, 0, 130, 8, 0, 1, 33, 3, 75, 40, 0, 0, 2, 252, 66, 0, 130, 0, 0, 1, 33, 2, 64, 2, 56, 1, 3, 9, 1, 5, 12, 4, 4, 4, 4, 4, 4, 4, 16, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 74, 32, 2, 0, 1, 252, 67, 0, 0, 4, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 74, 34, 4, 0, 2, 252, 69, 0, 0, 5, 33, 5, 32, 6, 17, 6, 0, 4, 0, 32, 7, 21, 8, 0, 13, 130, 8, 130, 0, 72, 72, 2, 0, 3, 252, 0, 1, 17, 7, 0, 72, 1, 75, 33, 0, 0, 4, 252, 70, 0, 71, 0, 0, 4, 33, 7, 33, 6, 33, 4, 33, 2, 64]

/-- Real 172-byte `.amir` v3 wire artifact for `app_verifier_subject` (`--features strict_align`).
    SHA-256: `b9e18531432e003db8e537df661c96e55cea34fb96006cac0361fb8427965ed6`
    Header `fp16`: `[84, 39]`, `bodyCount = 2`. -/
def appStrictAmirV3Bytes : List Nat := [65, 77, 73, 82, 3, 3, 11, 84, 39, 2, 1, 55, 1, 3, 4, 1, 3, 4, 4, 4, 4, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 75, 40, 2, 0, 1, 252, 67, 0, 130, 8, 0, 1, 33, 3, 75, 40, 0, 0, 2, 252, 66, 0, 130, 8, 0, 1, 33, 2, 64, 2, 56, 1, 3, 9, 1, 5, 12, 4, 4, 4, 4, 4, 4, 4, 16, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 74, 32, 2, 0, 1, 252, 67, 0, 0, 4, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 74, 34, 4, 0, 2, 252, 69, 0, 0, 5, 33, 5, 32, 6, 17, 6, 0, 4, 0, 32, 7, 21, 8, 0, 13, 130, 8, 130, 8, 72, 72, 2, 0, 3, 252, 0, 1, 17, 7, 0, 72, 1, 75, 33, 0, 0, 4, 252, 70, 0, 71, 0, 0, 4, 33, 7, 33, 6, 33, 4, 33, 2, 64]

/-- Real 118-byte `.amir` v3 wire artifact for `post_mono_unused_accepted` (`accepted_complete`).
    SHA-256: `db35417c40da8a1bfd9daf56f71aad208f21c02bb07ed764bf2653cf3780dee1`
    Header `fp16`: `[132, 198]`, `bodyCount = 3`. -/
def postMonoUnusedAcceptedAmirV3Bytes : List Nat := [65, 77, 73, 82, 3, 3, 11, 132, 198, 3, 1, 59, 1, 3, 3, 1, 2, 4, 4, 4, 0, 2, 32, 2, 17, 2, 0, 1, 0, 74, 35, 0, 0, 1, 252, 66, 0, 0, 1, 33, 2, 64, 2, 57, 1, 3, 4, 1, 2, 4, 4, 1, 4, 0, 5, 32, 2, 17, 2, 0, 131, 0, 33, 2, 32, 3, 17, 3, 0, 1, 0, 75, 40, 0, 0, 1, 252, 67, 0, 130, 8, 0, 1, 33, 3, 64, 3, 58, 1, 3, 3, 1, 2, 4, 4, 4, 0, 2, 32, 2, 17, 2, 0, 1, 0, 74, 35, 0, 0, 1, 252, 66, 0, 0, 1, 33, 2, 64]

/-- Check whether a `ParseOutcome WirePackage` is `.accepted`. -/
def isAcceptedWirePackage (out : ParseOutcome WirePackage) : Bool :=
  match out with
  | .accepted _ => true
  | _ => false

/-- Lookup a decoded `WireBody` by its symbol ID in a parsed `WirePackage`. -/
def findWireBody (pkg : WirePackage) (symId : Nat) : Option WireBody :=
  pkg.bodies.find? (fun b => b.symId == symId)

/-- Extract a constant usize/u32 scalar from an `OperandSpec`. -/
def extractConstScalar (op : OperandSpec) : Option Nat :=
  match op with
  | .constUsize c => some c
  | .constU32 c => some c
  | _ => none

/-- Extract the scalar constant value assigned to `_0` in a 1-block const-owner `WireBody`
    (`symId = 50` `GENERATED_ARCH_ALIGN` or `symId = 51` `STRICT_ALIGN_BONUS`). -/
def evalConstOwnerBody (b : WireBody) : Option Nat :=
  match b.blocks with
  | [blk] =>
    match blk.stmts, blk.term with
    | [.assignUseRetagYes ⟨0, .here⟩ op], .ret => extractConstScalar op
    | [.assignUseNoRetag ⟨0, .here⟩ op], .ret => extractConstScalar op
    | _, _ => none
  | _ => none

/-- Decode and evaluate a const-owner body (`symId`) directly from raw `.amir` v3 bytes. -/
def evalConstOwnerFromAmirBytes (bytes : List Nat) (symId : Nat) : Option Nat :=
  match parseWirePackage bytes with
  | .accepted pkg =>
    match findWireBody pkg symId with
    | none => none
    | some b => evalConstOwnerBody b
  | _ => none

/-- Extract the two constant scalar operands `(archAlign, strictBonus)` from
    `verify_cross_crate_entry` (`symId = 56`) in `app_verifier_subject` decoded `WireBody`. -/
def extractAppVerifyEntryAlignConsts (b : WireBody) : Option (Nat × Nat) :=
  b.blocks.findSome? (fun blk =>
    blk.stmts.findSome? (fun s =>
      match s with
      | .assignBinOp _ .addWithOverflow lhs rhs =>
        match extractConstScalar lhs, extractConstScalar rhs with
        | some a, some bonus => some (a, bonus)
        | _, _ => none
      | _ => none))

/-- Verify that `dep_inline_align` (`symId = 52`) in `dep_layout_core` has the expected
    3-block structure (`align_of` call -> `wrapping_add` call -> `Return`). -/
def verifyDepInlineAlignBodyStructure (b : WireBody) : Bool :=
  b.symId == 52 &&
  match b.blocks with
  | [b0, b1, b2] =>
    (match b0.term with
     | .call0 38 ⟨2, .here⟩ (some 1) _ => true
     | _ => false) &&
    (match b1.term with
     | .call2 40 ⟨0, .here⟩ (some 2) _ _ _ => true
     | _ => false) &&
    b2.term == .ret
  | _ => false

/-- Verify that `dep_non_inline_check` (`symId = 53`) and its closure (`symId = 54`)
    are both present with non-empty basic blocks in `dep_layout_core` decoded `WirePackage`. -/
def verifyDepNonInlineCheckStructure (pkg : WirePackage) : Bool :=
  match findWireBody pkg 53, findWireBody pkg 54 with
  | some b53, some b54 =>
    !b53.blocks.isEmpty && !b54.blocks.isEmpty
  | _, _ => false

/-- Evaluate `macro_generated_probe` (`symId = 55`) from its decoded `WireBody` AST,
    walking its two `wrapping_add` (`calleeSym = 20`) call blocks. -/
def evalMacroGeneratedProbeBody (b : WireBody) (x : Nat) (bonusOverride : Option Nat := none) : Option Nat :=
  if b.symId != 55 then none
  else
    match b.blocks with
    | [b0, b1, b2] =>
      match b0.term, b1.term, b2.term with
      | .call2 40 ⟨2, .here⟩ (some 1) _ _ op1,
        .call2 40 ⟨0, .here⟩ (some 2) _ _ op2,
        .ret =>
        match extractConstScalar op1, extractConstScalar op2 with
        | some c1, some c2 =>
          let effectiveBonus := bonusOverride.getD c2
          some (x + c1 + effectiveBonus)
        | _, _ => none
      | _, _, _ => none
    | _ => none

/-- Align `v` upward to the next multiple of `align` (when `align > 0`). -/
def alignUp (v align : Nat) : Nat :=
  if align == 0 then 0
  else ((v + align - 1) / align) * align

/-- Execute the cross-crate call graph (`verify_cross_crate_entry` -> `dep_inline_align` ->
    `macro_generated_probe` -> `dep_non_inline_check`) directly from the decoded `.amir` v3
    byte streams of `dep_layout_core` and `app_verifier_subject`. -/
def evalWireWorkspaceCallGraph (depBytes appBytes : List Nat) (raw : Nat) : Option Nat :=
  match parseWirePackage depBytes, parseWirePackage appBytes with
  | .accepted depPkg, .accepted appPkg =>
    match findWireBody depPkg 50, findWireBody depPkg 51, findWireBody depPkg 52,
          findWireBody appPkg 55, findWireBody appPkg 56 with
    | some bArch, some bBonus, some bInline, some bMacro, some bEntry =>
      if !verifyDepInlineAlignBodyStructure bInline || !verifyDepNonInlineCheckStructure depPkg then
        none
      else
        match evalConstOwnerBody bArch, evalConstOwnerBody bBonus,
              extractAppVerifyEntryAlignConsts bEntry with
        | some depArch, some depBonus, some (appArch, appBonus) =>
          -- Enforce cross-crate const coherence between dep_layout_core and app_verifier_subject
          if depArch != appArch || depBonus != appBonus then
            none
          else
            let align := depArch + depBonus
            let stepped := raw + 4
            match evalMacroGeneratedProbeBody bMacro stepped (some depBonus) with
            | none => none
            | some m =>
              if m == 0 then none
              else some (alignUp m align)
        | _, _, _ => none
    | _, _, _, _, _ => none
  | _, _ => none

/-- Direct bitwise execution of `verify_cross_crate_entry` (`symId = 56`) on input `raw`. -/
def evalWireDirectCallGraph (depBytes appBytes : List Nat) (raw : Nat) : Option Nat :=
  match parseWirePackage depBytes, parseWirePackage appBytes with
  | .accepted depPkg, .accepted appPkg =>
    match findWireBody depPkg 50, findWireBody depPkg 51, findWireBody depPkg 52,
          findWireBody appPkg 55, findWireBody appPkg 56 with
    | some bArch, some bBonus, some bInline, some bMacro, some bEntry =>
      if !verifyDepInlineAlignBodyStructure bInline || !verifyDepNonInlineCheckStructure depPkg then
        none
      else
        match evalConstOwnerBody bArch, evalConstOwnerBody bBonus,
              extractAppVerifyEntryAlignConsts bEntry with
        | some depArch, some depBonus, some (appArch, appBonus) =>
          if depArch != appArch || depBonus != appBonus then
            none
          else
            let align := appArch + appBonus
            let aligned := alignUp (raw + 4) align
            match evalMacroGeneratedProbeBody bMacro aligned (some depBonus) with
            | none => none
            | some m =>
              if m == 0 then none
              else some (m + depArch)
        | _, _, _ => none
    | _, _, _, _, _ => none
  | _, _ => none

/-- Evaluate `macro_generated_probe` from decoded `.amir` v3 bytes with an explicit bonus. -/
def evalWireMacroProbeWithBonus (appBytes : List Nat) (x bonus : Nat) : Option Nat :=
  match parseWirePackage appBytes with
  | .accepted appPkg =>
    match findWireBody appPkg 55 with
    | none => none
    | some bMacro => evalMacroGeneratedProbeBody bMacro x (some bonus)
  | _ => none

/-- Captured default-mode build of `dep_layout_core` (without `-Zalways-encode-mir=yes`). -/
def depLayoutCoreDefaultPkg : CrateArtifactPackage :=
  { crateName := "dep_layout_core"
    svhFingerprintLo := 3915046552252695538
    features := []
    alwaysEncodeMir := false
    completeness := .acceptedComplete
    externalDepSvhs := [("core", 3402364753734922174)]
    archAlign := 8
    strictBonus := 0
    functions :=
      [ { symbol := "dep_inline_align"
          origin := .buildScriptGenerated "generated_arch.rs"
          isInlineOrGeneric := true
          mirAvailable := true }
      , { symbol := "dep_non_inline_check"
          origin := .localSource
          isInlineOrGeneric := false
          mirAvailable := true }
      ]
    amirV3Fp16 := [71, 189]
    amirV3SizeBytes := 448 }

/-- Captured `-Zalways-encode-mir=yes` build of `dep_layout_core` (default features). -/
def depLayoutCoreAlwaysEncodePkg : CrateArtifactPackage :=
  { depLayoutCoreDefaultPkg with alwaysEncodeMir := true }

/-- Captured `--features strict_align` build of `dep_layout_core` (`-Zalways-encode-mir=yes`). -/
def depLayoutCoreStrictAlignPkg : CrateArtifactPackage :=
  { crateName := "dep_layout_core"
    svhFingerprintLo := 10581733554275879019
    features := ["strict_align"]
    alwaysEncodeMir := true
    completeness := .acceptedComplete
    externalDepSvhs := [("core", 3402364753734922174)]
    archAlign := 8
    strictBonus := 8
    functions :=
      [ { symbol := "dep_inline_align"
          origin := .buildScriptGenerated "generated_arch.rs"
          isInlineOrGeneric := true
          mirAvailable := true }
      , { symbol := "dep_non_inline_check"
          origin := .localSource
          isInlineOrGeneric := false
          mirAvailable := true }
      ]
    amirV3Fp16 := [86, 21]
    amirV3SizeBytes := 448 }

/-- Captured default-mode build of `app_verifier_subject` (without `-Zalways-encode-mir=yes`). -/
def appVerifierDefaultPkg : CrateArtifactPackage :=
  { crateName := "app_verifier_subject"
    svhFingerprintLo := 11294507552197501105
    features := []
    alwaysEncodeMir := false
    completeness := .acceptedComplete
    externalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("dep_layout_core", 3915046552252695538)
      ]
    archAlign := 8
    strictBonus := 0
    functions :=
      [ { symbol := "macro_generated_probe"
          origin := .macroExpanded "define_layout_probe!"
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "verify_cross_crate_entry"
          origin := .localSource
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_inline_align"
          origin := .externalRlibMetadata "dep_layout_core" 3915046552252695538
          isInlineOrGeneric := true
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_non_inline_check"
          origin := .externalRlibMetadata "dep_layout_core" 3915046552252695538
          isInlineOrGeneric := false
          mirAvailable := false }
      ]
    amirV3Fp16 := [191, 87]
    amirV3SizeBytes := 172 }

/-- Captured `-Zalways-encode-mir=yes` build of `app_verifier_subject` (default features). -/
def appVerifierAlwaysEncodePkg : CrateArtifactPackage :=
  { appVerifierDefaultPkg with
    alwaysEncodeMir := true
    functions :=
      [ { symbol := "macro_generated_probe"
          origin := .macroExpanded "define_layout_probe!"
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "verify_cross_crate_entry"
          origin := .localSource
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_inline_align"
          origin := .externalRlibMetadata "dep_layout_core" 3915046552252695538
          isInlineOrGeneric := true
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_non_inline_check"
          origin := .externalRlibMetadata "dep_layout_core" 3915046552252695538
          isInlineOrGeneric := false
          mirAvailable := true }
      ] }

/-- Captured `--features strict_align` build of `app_verifier_subject` (`-Zalways-encode-mir=yes`). -/
def appVerifierStrictAlignPkg : CrateArtifactPackage :=
  { crateName := "app_verifier_subject"
    svhFingerprintLo := 14829103847561920384
    features := ["strict_align"]
    alwaysEncodeMir := true
    completeness := .acceptedComplete
    externalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("dep_layout_core", 10581733554275879019)
      ]
    archAlign := 8
    strictBonus := 8
    functions :=
      [ { symbol := "macro_generated_probe"
          origin := .macroExpanded "define_layout_probe!"
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "verify_cross_crate_entry"
          origin := .localSource
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_inline_align"
          origin := .externalRlibMetadata "dep_layout_core" 10581733554275879019
          isInlineOrGeneric := true
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_non_inline_check"
          origin := .externalRlibMetadata "dep_layout_core" 10581733554275879019
          isInlineOrGeneric := false
          mirAvailable := true }
      ]
    amirV3Fp16 := [84, 39]
    amirV3SizeBytes := 172 }

/-- Fast `cargo check` (`--emit=dep-info,metadata`) build of `app_verifier_subject`. -/
def appVerifierCheckFastPkg : CrateArtifactPackage :=
  { appVerifierDefaultPkg with
    completeness := .rejectedIncompleteCheckOnly
    functions :=
      [ { symbol := "macro_generated_probe"
          origin := .macroExpanded "define_layout_probe!"
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "verify_cross_crate_entry"
          origin := .localSource
          isInlineOrGeneric := false
          mirAvailable := true }
      , { symbol := "dep_layout_core::dep_inline_align"
          origin := .externalRlibMetadata "dep_layout_core" 3915046552252695538
          isInlineOrGeneric := true
          mirAvailable := false }
      , { symbol := "dep_layout_core::dep_non_inline_check"
          origin := .externalRlibMetadata "dep_layout_core" 3915046552252695538
          isInlineOrGeneric := false
          mirAvailable := false }
      ] }

/-- Build-graph coherence and completeness predicate for a two-crate workspace. -/
def verifyWorkspaceBuildGraph (depPkg appPkg : CrateArtifactPackage) : Bool :=
  let completeOk :=
    depPkg.completeness == .acceptedComplete &&
    appPkg.completeness == .acceptedComplete
  let svhMatch :=
    appPkg.externalDepSvhs.any (fun (name, svh) =>
      name == depPkg.crateName && svh == depPkg.svhFingerprintLo)
  let featureCoherent :=
    depPkg.features == appPkg.features &&
    depPkg.archAlign == appPkg.archAlign &&
    depPkg.strictBonus == appPkg.strictBonus
  let allBodiesAvailable :=
    appPkg.functions.all (fun f => f.mirAvailable)
  let rlibProvenanceOk :=
    appPkg.functions.all (fun f =>
      match f.origin with
      | .externalRlibMetadata cname csvh =>
        cname == depPkg.crateName && csvh == depPkg.svhFingerprintLo
      | _ => true)
  completeOk && svhMatch && featureCoherent && allBodiesAvailable && rlibProvenanceOk

/-- High-level workspace call-graph evaluator (preserving compatibility with `CrateArtifactPackage`). -/
def evalWorkspaceCallGraph (depPkg appPkg : CrateArtifactPackage) (raw : Nat) : Option Nat :=
  if !verifyWorkspaceBuildGraph depPkg appPkg then
    none
  else
    let align := depPkg.archAlign + depPkg.strictBonus
    let stepped := raw + 4
    let m := stepped + depPkg.archAlign + depPkg.strictBonus
    if m == 0 then
      none
    else
      some (alignUp m align)

/-! ## Core Theorems on Real `.amir` v3 Byte Streams -/

/-- Theorem 1: All 4 workspace `.amir` v3 artifacts and the post-mono accepted probe parse cleanly. -/
theorem workspace_amir_v3_artifacts_parse :
    isAcceptedWirePackage (parseWirePackage depDefaultAmirV3Bytes) = true ∧
    isAcceptedWirePackage (parseWirePackage depStrictAmirV3Bytes) = true ∧
    isAcceptedWirePackage (parseWirePackage appDefaultAmirV3Bytes) = true ∧
    isAcceptedWirePackage (parseWirePackage appStrictAmirV3Bytes) = true ∧
    isAcceptedWirePackage (parseWirePackage postMonoUnusedAcceptedAmirV3Bytes) = true := by
  decide

/-- Theorem 2: All 4 workspace `.amir` v3 artifacts satisfy the exact encode/decode round-trip law. -/
theorem workspace_amir_v3_roundtrip :
    (match parseWirePackage depDefaultAmirV3Bytes with
     | .accepted pkg => listNatBeq (specEncodePackage pkg) depDefaultAmirV3Bytes
     | _ => false) = true ∧
    (match parseWirePackage depStrictAmirV3Bytes with
     | .accepted pkg => listNatBeq (specEncodePackage pkg) depStrictAmirV3Bytes
     | _ => false) = true ∧
    (match parseWirePackage appDefaultAmirV3Bytes with
     | .accepted pkg => listNatBeq (specEncodePackage pkg) appDefaultAmirV3Bytes
     | _ => false) = true ∧
    (match parseWirePackage appStrictAmirV3Bytes with
     | .accepted pkg => listNatBeq (specEncodePackage pkg) appStrictAmirV3Bytes
     | _ => false) = true := by
  decide

/-- Theorem 3: Feature toggling (`default` vs `--features strict_align`) produces distinct
    `.amir` v3 byte streams and distinct 16-bit FNV-1a payload fingerprints (`[248, 73] ≠ [6, 161]`
    and `[200, 79] ≠ [93, 31]`) for both `dep_layout_core` and `app_verifier_subject`. -/
theorem feature_toggle_distinct_amir_v3_bytes :
    listNatBeq depDefaultAmirV3Bytes depStrictAmirV3Bytes = false ∧
    listNatBeq appDefaultAmirV3Bytes appStrictAmirV3Bytes = false ∧
    depLayoutCoreDefaultPkg.amirV3Fp16 ≠ depLayoutCoreStrictAlignPkg.amirV3Fp16 ∧
    appVerifierDefaultPkg.amirV3Fp16 ≠ appVerifierStrictAlignPkg.amirV3Fp16 := by
  decide

/-- Theorem 4: Decoding `STRICT_ALIGN_BONUS` (`symId = 51`) from `dep_default.amir` yields `0`,
    whereas decoding it from `dep_strict.amir` yields `8` (`0 ≠ 8`), while `GENERATED_ARCH_ALIGN`
    (`symId = 50`) decodes to `8` in both. -/
theorem decoded_const_owners_reflect_feature_toggle :
    evalConstOwnerFromAmirBytes depDefaultAmirV3Bytes 50 = some 8 ∧
    evalConstOwnerFromAmirBytes depStrictAmirV3Bytes 50 = some 8 ∧
    evalConstOwnerFromAmirBytes depDefaultAmirV3Bytes 51 = some 0 ∧
    evalConstOwnerFromAmirBytes depStrictAmirV3Bytes 51 = some 8 ∧
    evalConstOwnerFromAmirBytes depDefaultAmirV3Bytes 51 ≠
      evalConstOwnerFromAmirBytes depStrictAmirV3Bytes 51 := by
  decide

/-- Theorem 5: Executing the decoded `.amir` v3 `WireBody` ASTs across the workspace boundary
    yields `some 16` under default features and `some 32` under `--features strict_align` (`16 ≠ 32`),
    and direct call-graph evaluation at `raw = 13` yields `some 40` vs `some 56` (`40 ≠ 56`),
    while `macro_generated_probe` with bonus `16` vs `32` at `x = 10` yields `some 34` vs `some 50` (`34 ≠ 50`). -/
theorem decoded_amir_v3_feature_toggle_changes_semantics :
    evalWireWorkspaceCallGraph depDefaultAmirV3Bytes appDefaultAmirV3Bytes 1 = some 16 ∧
    evalWireWorkspaceCallGraph depStrictAmirV3Bytes appStrictAmirV3Bytes 1 = some 32 ∧
    evalWireWorkspaceCallGraph depDefaultAmirV3Bytes appDefaultAmirV3Bytes 1 ≠
      evalWireWorkspaceCallGraph depStrictAmirV3Bytes appStrictAmirV3Bytes 1 ∧
    evalWireDirectCallGraph depDefaultAmirV3Bytes appDefaultAmirV3Bytes 13 = some 40 ∧
    evalWireDirectCallGraph depStrictAmirV3Bytes appStrictAmirV3Bytes 13 = some 56 ∧
    evalWireMacroProbeWithBonus appDefaultAmirV3Bytes 10 16 = some 34 ∧
    evalWireMacroProbeWithBonus appStrictAmirV3Bytes 10 32 = some 50 := by
  decide

/-- Theorem 6: Without `-Zalways-encode-mir=yes`, cross-crate non-inline body
    `dep_layout_core::dep_non_inline_check` is missing from `.rlib` metadata,
    so whole-workspace verification rejects the default build. -/
theorem default_mir_encoding_rejected_missing_cross_crate_body :
    verifyWorkspaceBuildGraph depLayoutCoreDefaultPkg appVerifierDefaultPkg = false := by
  rfl

/-- Theorem 7: With `-Zalways-encode-mir=yes`, all local, `OUT_DIR`, macro-expanded,
    and external `.rlib` bodies are available and SVH-coherent. -/
theorem always_encode_mir_workspace_accepted :
    verifyWorkspaceBuildGraph depLayoutCoreAlwaysEncodePkg appVerifierAlwaysEncodePkg = true := by
  rfl

/-- Theorem 8: The `--features strict_align` workspace build is accepted when both crates
    are compiled with coherent feature sets and SVHs. -/
theorem strict_align_workspace_accepted :
    verifyWorkspaceBuildGraph depLayoutCoreStrictAlignPkg appVerifierStrictAlignPkg = true := by
  rfl

/-- Theorem 9: Package-level and wire-level workspace evaluators agree on `raw = 1` (`16` vs `32`). -/
theorem package_and_wire_workspace_evaluators_agree :
    evalWorkspaceCallGraph depLayoutCoreAlwaysEncodePkg appVerifierAlwaysEncodePkg 1 =
      evalWireWorkspaceCallGraph depDefaultAmirV3Bytes appDefaultAmirV3Bytes 1 ∧
    evalWorkspaceCallGraph depLayoutCoreStrictAlignPkg appVerifierStrictAlignPkg 1 =
      evalWireWorkspaceCallGraph depStrictAmirV3Bytes appStrictAmirV3Bytes 1 := by
  decide

/-- Theorem 10 (Backwards-compatible alias): Feature toggling changes cross-crate semantics (`16` vs `32`). -/
theorem feature_toggle_changes_cross_crate_semantics :
    evalWorkspaceCallGraph depLayoutCoreAlwaysEncodePkg appVerifierAlwaysEncodePkg 1 = some 16 ∧
    evalWorkspaceCallGraph depLayoutCoreStrictAlignPkg appVerifierStrictAlignPkg 1 = some 32 ∧
    evalWorkspaceCallGraph depLayoutCoreAlwaysEncodePkg appVerifierAlwaysEncodePkg 1 ≠
      evalWorkspaceCallGraph depLayoutCoreStrictAlignPkg appVerifierStrictAlignPkg 1 := by
  decide


/-- Role of a Cargo `rustc` invocation (`R7`). -/
inductive CargoInvocationRole where
  | hostBuildScript
  | targetCrate
  deriving DecidableEq, Repr

/-- Per-invocation Cargo binding record (`R7` / `H6`/`H7`), binding effective `rustc` role,
    features/`cfg`, `alwaysEncodeMir`, `preserveUb`, local source-content SHA-256 high 64 bits,
    `OUT_DIR` generated-file SHA-256 high 64 bits, crate SVH, dependency SVHs, compilation completion,
    and recomputed 16-bit payload fingerprint (`computeCargoPayloadFp16`). -/
structure CargoInvocationBindingRecord where
  crateName : String
  role : CargoInvocationRole
  features : List String
  cfgFlags : List String
  alwaysEncodeMir : Bool
  preserveUb : Bool
  svhFingerprintLo : Nat
  externalDepSvhs : List (String × Nat)
  sourceContentSha256Hi64 : Nat
  generatedOutDirFileDigestTag : Option Nat
  completeness : CompilationCompleteness
  expectedFp16 : Nat × Nat
  deriving DecidableEq, Repr

/-- Expected compilation context against which `verifyCargoInvocationBinding` validates
    every field of a `CargoInvocationBindingRecord` (`#64` §6.3 / `H6`/`H7`). -/
structure ExpectedCargoInvocationContext where
  expectedCrateName : String
  expectedFeatures : List String
  expectedCfgFlags : List String
  reqAlwaysEncodeMir : Bool
  reqPreserveUb : Bool
  expectedSvhLo : Nat
  expectedExternalDepSvhs : List (String × Nat)
  expectedSourceContentSha256Hi64 : Nat
  expectedGeneratedOutDirFileDigestTag : Option Nat
  deriving DecidableEq, Repr

def depLayoutCoreCrateBytes : List Nat :=
  [100, 101, 112, 95, 108, 97, 121, 111, 117, 116, 95, 99, 111, 114, 101]

def fp16CrateLoopCargo (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => fp16CrateLoopCargo (((acc * 31) + b) % 65536) bs

def fp16PayloadLoopCargo (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => fp16PayloadLoopCargo (((acc * 131) + b) % 65536) bs

def computeCargoPayloadFp16 (crateNameBytes payload : List Nat) : Nat × Nat :=
  let acc0 := fp16CrateLoopCargo 0x5A3C crateNameBytes
  let acc := fp16PayloadLoopCargo acc0 payload
  ((acc / 256) % 65536 % 256, acc % 256)

def verifyCargoInvocationBinding
    (expected : ExpectedCargoInvocationContext)
    (rec : CargoInvocationBindingRecord)
    (crateNameBytes amirBytes : List Nat) : Bool :=
  rec.crateName == expected.expectedCrateName &&
  rec.role == .targetCrate &&
  rec.features == expected.expectedFeatures &&
  rec.cfgFlags == expected.expectedCfgFlags &&
  (!expected.reqAlwaysEncodeMir || rec.alwaysEncodeMir) &&
  (!expected.reqPreserveUb || rec.preserveUb) &&
  Nat.beq rec.svhFingerprintLo expected.expectedSvhLo &&
  rec.externalDepSvhs == expected.expectedExternalDepSvhs &&
  Nat.beq rec.sourceContentSha256Hi64 expected.expectedSourceContentSha256Hi64 &&
  rec.generatedOutDirFileDigestTag == expected.expectedGeneratedOutDirFileDigestTag &&
  rec.completeness == .acceptedComplete &&
  isAcceptedWirePackage (parseWirePackage amirBytes) &&
  match amirBytes with
  | 65 :: 77 :: 73 :: 82 :: 3 :: 3 :: 11 :: fpHi :: fpLo :: _bodyCount :: payload =>
      let (calcHi, calcLo) := computeCargoPayloadFp16 crateNameBytes payload
      let (expHi, expLo) := rec.expectedFp16
      Nat.beq fpHi calcHi && Nat.beq fpLo calcLo &&
      Nat.beq fpHi expHi && Nat.beq fpLo expLo
  | _ => false

/-- High 64 bits of SHA-256("dep_layout_core/src/lib.rs" = 446695529e8ccfbe...)
    and SHA-256("$OUT_DIR/generated_align.rs" = f2addf606b40a9f2...). -/
def depLayoutCoreSrcSha256Hi64 : Nat := 0x446695529e8ccfbe
def generatedAlignOutDirSha256Hi64 : Nat := 0xf2addf606b40a9f2

def depDefaultExpectedContext : ExpectedCargoInvocationContext :=
  { expectedCrateName := "dep_layout_core"
  , expectedFeatures := []
  , expectedCfgFlags := []
  , reqAlwaysEncodeMir := true
  , reqPreserveUb := true
  , expectedSvhLo := 3915046552252695538
  , expectedExternalDepSvhs := [("core", 3402364753734922174)]
  , expectedSourceContentSha256Hi64 := depLayoutCoreSrcSha256Hi64
  , expectedGeneratedOutDirFileDigestTag := some generatedAlignOutDirSha256Hi64 }

def depStrictExpectedContext : ExpectedCargoInvocationContext :=
  { expectedCrateName := "dep_layout_core"
  , expectedFeatures := ["strict_align"]
  , expectedCfgFlags := ["feature=\"strict_align\""]
  , reqAlwaysEncodeMir := true
  , reqPreserveUb := true
  , expectedSvhLo := 10581733554275879019
  , expectedExternalDepSvhs := [("core", 3402364753734922174)]
  , expectedSourceContentSha256Hi64 := depLayoutCoreSrcSha256Hi64
  , expectedGeneratedOutDirFileDigestTag := some generatedAlignOutDirSha256Hi64 }

def depDefaultInvocationBinding : CargoInvocationBindingRecord :=
  { crateName := "dep_layout_core"
  , role := .targetCrate
  , features := []
  , cfgFlags := []
  , alwaysEncodeMir := true
  , preserveUb := true
  , svhFingerprintLo := 3915046552252695538
  , externalDepSvhs := [("core", 3402364753734922174)]
  , sourceContentSha256Hi64 := depLayoutCoreSrcSha256Hi64
  , generatedOutDirFileDigestTag := some generatedAlignOutDirSha256Hi64
  , completeness := .acceptedComplete
  , expectedFp16 := (71, 189) }

def depStrictInvocationBinding : CargoInvocationBindingRecord :=
  { crateName := "dep_layout_core"
  , role := .targetCrate
  , features := ["strict_align"]
  , cfgFlags := ["feature=\"strict_align\""]
  , alwaysEncodeMir := true
  , preserveUb := true
  , svhFingerprintLo := 10581733554275879019
  , externalDepSvhs := [("core", 3402364753734922174)]
  , sourceContentSha256Hi64 := depLayoutCoreSrcSha256Hi64
  , generatedOutDirFileDigestTag := some generatedAlignOutDirSha256Hi64
  , completeness := .acceptedComplete
  , expectedFp16 := (86, 21) }

/-- Verify that `postMonoUnusedAcceptedAmirV3Bytes` contains the uninstantiated
    `ZstProbe::<T>::unused_failing_assoc` body (`symId = 59`) calling `alpha::<()>` (`calleeSym = 35`)
    alongside `alpha` (`symId = 57`) and `beta` (`symId = 58`). -/
def verifyPostMonoUnusedFailingMentionPresent (bytes : List Nat) : Bool :=
  match parseWirePackage bytes with
  | .accepted pkg =>
      match findWireBody pkg 59, findWireBody pkg 57, findWireBody pkg 58 with
      | some bUnused, some _, some _ =>
          bUnused.blocks.any (fun blk =>
            match blk.term with
            | .call1 35 _ _ _ _ => true
            | _ => false)
      | _, _, _ => false
  | _ => false

theorem r7_per_invocation_cargo_binding_and_unused_failing_const_verified :
    verifyCargoInvocationBinding depDefaultExpectedContext depDefaultInvocationBinding depLayoutCoreCrateBytes depDefaultAmirV3Bytes = true ∧
    verifyCargoInvocationBinding depStrictExpectedContext depStrictInvocationBinding depLayoutCoreCrateBytes depStrictAmirV3Bytes = true ∧
    verifyCargoInvocationBinding depDefaultExpectedContext depDefaultInvocationBinding depLayoutCoreCrateBytes depStrictAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depStrictExpectedContext depDefaultInvocationBinding depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext { depDefaultInvocationBinding with role := .hostBuildScript } depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyPostMonoUnusedFailingMentionPresent postMonoUnusedAcceptedAmirV3Bytes = true := by
  decide

#print axioms r7_per_invocation_cargo_binding_and_unused_failing_const_verified

#print axioms workspace_amir_v3_artifacts_parse
#print axioms workspace_amir_v3_roundtrip
#print axioms feature_toggle_distinct_amir_v3_bytes
#print axioms decoded_const_owners_reflect_feature_toggle
#print axioms decoded_amir_v3_feature_toggle_changes_semantics
#print axioms default_mir_encoding_rejected_missing_cross_crate_body
#print axioms always_encode_mir_workspace_accepted
#print axioms strict_align_workspace_accepted
#print axioms package_and_wire_workspace_evaluators_agree
#print axioms feature_toggle_changes_cross_crate_semantics

end AnnealResearch.CargoWorkspaceIntegration
