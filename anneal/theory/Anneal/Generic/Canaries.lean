-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Generic.Syntax
public import Anneal.Generic.TypeSpec
public import Anneal.Generic.OpenSemantics
public import Anneal.Generic.Erasure

public section

namespace Anneal.Generic

open Trusted.MirAst Trusted.MirSemantics

/-!
# Open-Generics Canaries (`Anneal.Generic.Canaries`)

Kernel-checked positive and negative verification canaries exercising:
1. `hash_block<H: Sha256Like>(h: H, block: &[u8], offset: u64) -> Hash`:
   parametric-only verification across all well-formed `TypeLayoutSpec`
   instantiations via `ParametricBodyVerified` and assume-guarantee
   `.traitCall`;
2. `verify_aligned<B: ByteSource<Out = u64>>(src: &B, offset: u64) -> B::Out`:
   parametric-only verification with an associated-type projection
   (`assocProj`), `WhereClause.typeEq`, and concrete `TraitRegistry`
   normalization (`(MemSlice as ByteSource)::Out`);
3. Negative coherence canary: duplicate `ImplKey` in `TraitRegistry` fails
   `TraitRegistryWf` statically (`false`);
4. Negative missing-bound canary: omitting the trait bound from
   `sig.whereClauses` causes `.traitCall` to fail closed with
   `.fault .unsupported`, refuting `ParametricBodyVerified`;
5. `generic_id<T>(x: T) -> T`: parametric verification plus concrete
   closed-instantiation transfer (`bool` and `u64`) via
   `ClosedOpenInstantiationTransfer` and `ClosedInstantiationTransfer` to
   genuine Day-1 `BodyVerified` (zero caller-supplied `wellFormedTransfer`
   escape hatches);
6. Negative `.typeEq` canary (`canary_i64_u64_share_typeLayoutSpec` and
   `canary_typeEq_rejects_distinct_same_layout`): `i64` and `u64` share
   `intTypeLayoutSpec .i64`, yet `WhereClauseSem` rejects
   `.typeEq (.int .i64 true) (.int .i64 false)` via normalized `OpenMirTy.beq`;
7. Negative malformed-body canary
   (`canary_malformed_body_unsat_where_rejected`): hoisting
   `OpenBodyStructureValid` rejects `pointerWidthBits = 32` even when
   `sig.whereClauses` is unsatisfiable;
8. Erasure Canary 3 (`canary_day1_erasure_unsafe_noop_u64`): erases
   `unsafe_noop<T>` at `u64` to Day-1 `BodyVerified`, discharging an
   `OpenExecEnv`-dependent `safetyPre` alongside an uncalled
   non-Day-1-erasable sibling body;
9. Closed-reference / empty-tuple fail-closed canaries
   (`canary_tuple_nil_not_admitted`, `canary_checkOpenVal_closed_ref_inhabited`,
   `canary_closed_ref_self_impl_refused`,
   `canary_closed_ref_body_not_parametric_verified`, and
   `canary_closed_ref_subst_not_well_formed`): closed `.tuple []` is rejected by
   `evalNormOpenTySpec`, `checkOpenVal` validates closed pointers via
   `checkOpenValOnSpec`, and `openClosedTySupported` refuses closed
   Day-1-convertible reference and raw-pointer (`&u64`, `*const bool`) bodies,
   impls, and substitutions in `OpenBodyStaticAdmitted`, `SatisfiesTraitSem`,
   `AllWhereDischarged`, `ParametricBodyVerified`, and
   `AllSubstTypesWellFormed`;
10. Anti-vacuity and by-value trait-satisfaction witness canaries
    (`canary_generic_id_u64_open_nonvacuous`,
    `canary_erased_generic_id_u64_nonvacuous`,
    `canary_verify_aligned_memSlice_admitted_and_inhabited`,
    `canary_by_val_trait_impl_satisfies_sem`, and
    `canary_day1_erasure_trait_bounded_id_u64`): concrete non-trivial runtime
    argument and terminal-return witnesses (`42_u64`) for open and erased Day-1
    `BodyVerified` bodies, plus a positive by-value-receiver scalar trait `impl`
    witness proving `SatisfiesTraitSem`, `AllWhereDischarged`, and end-to-end
    trait-bounded `ClosedInstantiationTransfer` to Day-1 `BodyVerified`;
11. Open/concrete trait-call boundary and admission regression canaries
    (`canary_openClosedTySupported_boundary`,
    `canary_assume_guarantee_out_of_range_param_refused`, and
    `canary_concrete_trait_call_dst_mismatch_refused`): pins the exact
    `openClosedTySupported` Day-1 vs. non-Day-1 pointee boundary, proves
    `AssumeGuaranteeTraitCall` refuses out-of-range `.param` indices in
    `retTy`, `argTys`, and `whereClauses` (with a matching in-bounds positive
    control), and proves `concreteTraitCallStep` rejects destination return-type
    mismatches (`.param 0` and `u64` against an `i64` callee), projected
    destinations, and out-of-bounds destination locals (with a matching `i64`
    positive control).
-/

private theorem canary_step_ne_fault {α β : Type} {s : α} {k : FaultKind}
    {P : Prop} (h : StepResult.step s = (@StepResult.fault α β k)) : P := by
  cases h

private theorem canary_done_ne_fault {α β : Type} {out : β} {k : FaultKind}
    {P : Prop} (h : (@StepResult.done α β out) = .fault k) : P := by
  cases h

private theorem canary_done_ne_step {α β : Type} {out : β} {s : α} {P : Prop}
    (h : (@StepResult.done α β out) = .step s) : P := by
  cases h

private theorem canary_bool_false_ne_true {P : Prop} (h : false = true) : P := by
  cases h

private theorem canary_if_false {α : Type} {a b : α} :
    (if false = true then a else b) = b :=
  rfl

private theorem canary_ite_false {α : Type} {c : Bool} {a b : α}
    (h : c = false) : (if c = true then a else b) = b := by
  subst h
  rfl

private theorem canary_nat_zero_ne_succ {n : Nat} {P : Prop}
    (h : 0 = n + 1) : P := by
  cases h

private theorem canary_nat_succ_ne_zero {n : Nat} {P : Prop}
    (h : n + 1 = 0) : P := by
  cases h

private theorem canary_except_ok_inj {ε α : Type} {a b : α}
    (h : (@Except.ok ε α a) = .ok b) : a = b := by
  cases h
  rfl

/-- Canonical trait id for `Sha256Like`. -/
@[expose] noncomputable def traitSha256LikeId : TraitDefId := 0

/-- Canonical trait id for `ByteSource`. -/
@[expose] noncomputable def traitByteSourceId : TraitDefId := 1

/-- Canonical nominal ADT id for 32-byte `Hash`. -/
@[expose] noncomputable def hashAdtId : AdtDefId := 0

/-- Canonical nominal ADT id for concrete `MemSlice`. -/
@[expose] noncomputable def memSliceAdtId : AdtDefId := 1

/-- Empty `OpenExecEnv` rejecting unknown trait contracts and ADTs. -/
@[expose] noncomputable def emptyOpenExecEnv : OpenExecEnv :=
  { traitContracts := fun _ => none }

/-- Layout spec for a 32-byte `Hash` digest. -/
@[expose] noncomputable def hashTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 0
  , sizeForMeta := fun m => match m with | .none => some 32 | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with
      | .none => some (repeatItem (.valueByte .anyByte) 32)
      | _ => none }

/-- Layout spec for concrete `MemSlice` (pointer-sized handle). -/
@[expose] noncomputable def memSliceTypeLayoutSpec : TypeLayoutSpec :=
  { isSized := true
  , alignLog2 := 3
  , sizeForMeta := fun m => match m with | .none => some 16 | _ => none
  , inhabited := true
  , hasUnsafeCell := false
  , rolesForMeta := fun m =>
      match m with
      | .none => some (repeatItem (.valueByte .anyByte) 16)
      | _ => none }

/-- Proof that `hashTypeLayoutSpec` is well-formed. -/
theorem wellFormed_hashTypeLayoutSpec :
    WellFormedTypeLayoutSpec hashTypeLayoutSpec := by
  refine ⟨fun _ => ⟨32, repeatItem (.valueByte .anyByte) 32, rfl, rfl,
      length_repeatItem _ 32⟩, ?_, ?_, by decide,
    fun _ => ⟨fun _ => ⟨repeatItem (.init 0 none) 32, by
      unfold LangValid LangValidBool hashTypeLayoutSpec
      rfl⟩, fun h => by cases h⟩⟩
  · intro m sz h
    cases m with
    | none =>
        cases h
        exact ⟨le_isizeMax_of_le_32 (by decide),
          repeatItem (.valueByte .anyByte) 32, rfl, length_repeatItem _ 32⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs h
    cases m with
    | none => cases h; exact ⟨32, rfl, length_repeatItem _ 32⟩
    | sliceLen _ | vtable _ => cases h

/-- Proof that `memSliceTypeLayoutSpec` is well-formed. -/
theorem wellFormed_memSliceTypeLayoutSpec :
    WellFormedTypeLayoutSpec memSliceTypeLayoutSpec := by
  refine ⟨fun _ => ⟨16, repeatItem (.valueByte .anyByte) 16, rfl, rfl,
      length_repeatItem _ 16⟩, ?_, ?_, by decide,
    fun _ => ⟨fun _ => ⟨repeatItem (.init 0 none) 16, by
      unfold LangValid LangValidBool memSliceTypeLayoutSpec
      rfl⟩, fun h => by cases h⟩⟩
  · intro m sz h
    cases m with
    | none =>
        cases h
        exact ⟨le_isizeMax_of_le_32 (by decide),
          repeatItem (.valueByte .anyByte) 16, rfl, length_repeatItem _ 16⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs h
    cases m with
    | none => cases h; exact ⟨16, rfl, length_repeatItem _ 16⟩
    | sliceLen _ | vtable _ => cases h

/-- `Sha256Like::hash_step(self, block: &[u8], offset: u64) -> Hash` contract.
-/
@[expose] noncomputable def sha256MethodSpec : TraitMethodSpec :=
  { sig :=
      { methodIdx := 0
      , argTys :=
          [.param 0, .ref .shared (.slice (.int .i8 false)), .int .i64 false]
      , retTy := .adt hashAdtId []
      , whereClauses := []
      , isUnsafe := false }
  , pre := fun _ _ argVals _ => Nat.beq argVals.length 3 = true
  , post := fun _ _ _ cm out =>
      ∃ digest : List AllocByte,
        digest.length = 32 ∧
        LangValidBool hashTypeLayoutSpec .none digest = true ∧
        out = .returned ⟨.bytes digest, cm⟩ }

/-- `Sha256Like` trait contract. -/
@[expose] noncomputable def sha256Contract : TraitContract :=
  { traitId := traitSha256LikeId
  , tyParamCount := 0
  , assocTypeCount := 0
  , methodSpecs := [sha256MethodSpec] }

/-- `ByteSource::read_aligned(&self, offset: u64) -> Self::Out` contract. -/
@[expose] noncomputable def byteSourceMethodSpec : TraitMethodSpec :=
  { sig :=
      { methodIdx := 0
      , argTys := [.ref .shared (.param 0), .int .i64 false]
      , retTy := .assocProj (.param 0) traitByteSourceId [] 0
      , whereClauses := []
      , isUnsafe := false }
  , pre := fun _ _ argVals _ => Nat.beq argVals.length 2 = true
  , post := fun _ assocSpecs _ cm out =>
      match assocSpecs with
      | [outSpec] =>
          ∃ v : Val,
            checkOpenValOnSpec v (some outSpec) = true ∧
            out = .returned ⟨v, cm⟩
      | _ => False }

/-- `ByteSource` trait contract with 1 associated type (`Out`). -/
@[expose] noncomputable def byteSourceContract : TraitContract :=
  { traitId := traitByteSourceId
  , tyParamCount := 0
  , assocTypeCount := 1
  , methodSpecs := [byteSourceMethodSpec] }

/-- Canonical ADT layout map covering `Hash` (`0`) and `MemSlice` (`1`). -/
@[expose] noncomputable def canaryAdtSpecs (id : AdtDefId)
    (args : List TypeLayoutSpec) : Option TypeLayoutSpec :=
  match id, args with
  | 0, [] => some hashTypeLayoutSpec
  | 1, [] => some memSliceTypeLayoutSpec
  | _, _ => none

/-- Open generic body modeling
`hash_block<H: Sha256Like>(h: H, block: &[u8], offset: u64) -> Hash`. -/
@[expose] noncomputable def hashBlockBody : OpenBody :=
  { sig :=
      { tyParamCount := 1
      , argTys :=
          [.param 0, .ref .shared (.slice (.int .i8 false)), .int .i64 false]
      , retTy := .adt hashAdtId []
      , whereClauses :=
          [ .traitBound (.param 0) traitSha256LikeId []
          , .isSized (.param 0) ] }
  , argumentCount := 3
  , locals :=
      [ .adt hashAdtId []
      , .param 0
      , .ref .shared (.slice (.int .i8 false))
      , .int .i64 false ]
  , basicBlocks :=
      [ { statements := []
        , terminator :=
            .traitCall (.param 0) traitSha256LikeId [] 0
              [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]
              ⟨0, []⟩ (some 1) .continue_ }
      , { statements := [], terminator := .return_ } ]
  , isUnsafe := false
  , identity := "canary::hash_block" }

/-- Open generic body modeling
`verify_aligned<B: ByteSource<Out = u64>>(src: &B, offset: u64) -> B::Out`. -/
@[expose] noncomputable def verifyAlignedBody : OpenBody :=
  { sig :=
      { tyParamCount := 1
      , argTys := [.ref .shared (.param 0), .int .i64 false]
      , retTy := .assocProj (.param 0) traitByteSourceId [] 0
      , whereClauses :=
          [ .traitBound (.param 0) traitByteSourceId []
          , .typeEq (.assocProj (.param 0) traitByteSourceId [] 0)
              (.int .i64 false) ] }
  , argumentCount := 2
  , locals :=
      [ .assocProj (.param 0) traitByteSourceId [] 0
      , .ref .shared (.param 0)
      , .int .i64 false ]
  , basicBlocks :=
      [ { statements := []
        , terminator :=
            .traitCall (.param 0) traitByteSourceId [] 0
              [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
              ⟨0, []⟩ (some 1) .continue_ }
      , { statements := [], terminator := .return_ } ]
  , isUnsafe := false
  , identity := "canary::verify_aligned" }

/-- Open generic body with a missing trait bound in `sig.whereClauses`
(negative soundness canary). -/
@[expose] noncomputable def missingBoundBody : OpenBody :=
  { hashBlockBody with
    sig := { hashBlockBody.sig with whereClauses := [.isSized (.param 0)] }
    identity := "canary::missing_bound" }

/-- Day-1-erasable open generic identity body `generic_id<T>(x: T) -> T`. -/
@[expose] noncomputable def genericIdBody : OpenBody :=
  { sig :=
      { tyParamCount := 1
      , argTys := [.param 0]
      , retTy := .param 0
      , whereClauses := [.isSized (.param 0)] }
  , argumentCount := 1
  , locals := [.param 0, .param 0]
  , basicBlocks :=
      [ { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        , terminator := .return_ } ]
  , isUnsafe := false
  , identity := "canary::generic_id" }

/-- Concrete well-formed `TraitRegistry` containing a valid `MemSlice` impl of
`ByteSource` (`type Out = u64`). -/
@[expose] noncomputable def canaryTraitRegistry : TraitRegistry :=
  [ ( ⟨.adt memSliceAdtId [], traitByteSourceId, []⟩
    , { implTyParamCount := 0
      , whereClauses := []
      , assocTypes := [{ assocIdx := 0, rhsTy := .int .i64 false }]
      , methodDefIds := [] } ) ]

/-- Execution environment for the `Sha256Like` and `ByteSource` canaries. -/
@[expose] noncomputable def canaryExecEnv : OpenExecEnv :=
  { traitContracts := fun tid =>
      if Nat.beq tid traitSha256LikeId then some sha256Contract
      else if Nat.beq tid traitByteSourceId then some byteSourceContract
      else none
  , typeSpecs :=
      { adtSpecs := canaryAdtSpecs
      , assocSpecs := fun selfTy tr args idx =>
          match selfTy, tr, args, idx with
          | .param 0, 1, [], 0 => some (intTypeLayoutSpec .i64)
          | _, _, _, _ => none
      , paramSpecs := []
      , paramInvs := [] } }

/-- Open program for `hash_block<H: Sha256Like>`. -/
@[expose] noncomputable def hashBlockProgram : OpenProgram :=
  { bodies := [hashBlockBody]
  , entryDefId := 0
  , traitRegistry := canaryTraitRegistry
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Open program for `verify_aligned<B: ByteSource>`. -/
@[expose] noncomputable def verifyAlignedProgram : OpenProgram :=
  { bodies := [verifyAlignedBody]
  , entryDefId := 0
  , traitRegistry := canaryTraitRegistry
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Open program for negative missing-bound canary. -/
@[expose] noncomputable def missingBoundProgram : OpenProgram :=
  { bodies := [missingBoundBody]
  , entryDefId := 0
  , traitRegistry := canaryTraitRegistry
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Open program for `generic_id<T>(x: T) -> T`. -/
@[expose] noncomputable def genericIdProgram : OpenProgram :=
  { bodies := [genericIdBody]
  , entryDefId := 0
  , traitRegistry := []
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Duplicate-impl registry violating coherence (two conflicting `u64` impls for
`Sha256Like`). -/
@[expose] noncomputable def badDuplicateRegistry : TraitRegistry :=
  [ ( ⟨.int .i64 false, traitSha256LikeId, []⟩
    , { methodDefIds := [(0, 10)] } )
  , ( ⟨.int .i64 false, traitSha256LikeId, []⟩
    , { methodDefIds := [(0, 11)] } ) ]

/-- Negative Canary 3: `TraitRegistryWf` rejects overlapping `ImplKey`s, closing
dictionary spoofing statically. -/
theorem canary_rejects_duplicate_impl :
    TraitRegistryWf badDuplicateRegistry = false := by
  rfl

/-- Positive Associated-Type Normalization Canary:
`(MemSlice as ByteSource)::Out` normalizes to `u64` under
`canaryTraitRegistry`. -/
theorem canary_verify_aligned_assoc_norm :
    normalizeOpenTy canaryTraitRegistry normFuel
      (.assocProj (.adt memSliceAdtId []) traitByteSourceId [] 0) =
    .int .i64 false := by
  rfl

private theorem checkOpenArgsMatch_three_shape (prog : OpenProgram)
    (env : OpenExecEnv) (t1 t2 t3 : OpenMirTy) (args : List Val)
    (h : checkOpenArgsMatch prog env args [t1, t2, t3] = true) :
    ∃ v1 v2 v3 : Val,
      args = [v1, v2, v3] ∧
      checkOpenVal prog env v1 t1 = true ∧
      checkOpenVal prog env v2 t2 = true ∧
      checkOpenVal prog env v3 t3 = true := by
  cases args with
  | nil => cases h
  | cons v1 r1 =>
      cases r1 with
      | nil =>
          unfold checkOpenArgsMatch at h
          exact canary_bool_false_ne_true (bool_and_right h)
      | cons v2 r2 =>
          cases r2 with
          | nil =>
              unfold checkOpenArgsMatch at h
              exact canary_bool_false_ne_true (bool_and_right (bool_and_right h))
          | cons v3 r3 =>
              cases r3 with
              | cons _ _ =>
                  unfold checkOpenArgsMatch at h
                  exact canary_bool_false_ne_true
                    (bool_and_right (bool_and_right (bool_and_right h)))
              | nil =>
                  unfold checkOpenArgsMatch at h
                  have h1 := bool_and_left h
                  have h23 := bool_and_right h
                  have h2 := bool_and_left h23
                  have h3 := bool_and_left (bool_and_right h23)
                  exact ⟨v1, v2, v3, rfl, h1, h2, h3⟩

private theorem checkOpenArgsMatch_two_shape (prog : OpenProgram)
    (env : OpenExecEnv) (t1 t2 : OpenMirTy) (args : List Val)
    (h : checkOpenArgsMatch prog env args [t1, t2] = true) :
    ∃ v1 v2 : Val,
      args = [v1, v2] ∧
      checkOpenVal prog env v1 t1 = true ∧
      checkOpenVal prog env v2 t2 = true := by
  cases args with
  | nil => cases h
  | cons v1 r1 =>
      cases r1 with
      | nil =>
          unfold checkOpenArgsMatch at h
          exact canary_bool_false_ne_true (bool_and_right h)
      | cons v2 r2 =>
          cases r2 with
          | cons _ _ =>
              unfold checkOpenArgsMatch at h
              exact canary_bool_false_ne_true (bool_and_right (bool_and_right h))
          | nil =>
              unfold checkOpenArgsMatch at h
              have h1 := bool_and_left h
              have h2 := bool_and_left (bool_and_right h)
              exact ⟨v1, v2, rfl, h1, h2⟩

private theorem checkOpenArgsMatch_one_shape (prog : OpenProgram)
    (env : OpenExecEnv) (t1 : OpenMirTy) (args : List Val)
    (h : checkOpenArgsMatch prog env args [t1] = true) :
    ∃ v1 : Val,
      args = [v1] ∧
      checkOpenVal prog env v1 t1 = true := by
  cases args with
  | nil => cases h
  | cons v1 r1 =>
      cases r1 with
      | cons _ _ =>
          unfold checkOpenArgsMatch at h
          exact canary_bool_false_ne_true (bool_and_right h)
      | nil =>
          unfold checkOpenArgsMatch at h
          exact ⟨v1, rfl, bool_and_left h⟩

/-- Reachable state invariant for `hash_block<H: Sha256Like>`. -/
def hashBlockInv (v1 v2 v3 : Val) (s : OpenState) : Prop :=
  (s.frames =
      [{ defId := 0
       , blockIdx := 0
       , stmtIdx := 0
       , locals :=
           [.immediate none, .immediate (some v1), .immediate (some v2),
             .immediate (some v3)]
       , retDst := none }] ∧
    s.callerMem = ⟨[]⟩) ∨
  (∃ digest : List AllocByte, ∃ cm : CallerMemory,
    s.frames =
      [{ defId := 0
       , blockIdx := 1
       , stmtIdx := 0
       , locals :=
           [.immediate (some (.bytes digest)), .immediate (some v1),
             .immediate (some v2), .immediate (some v3)]
       , retDst := none }] ∧
    s.callerMem = cm)

private theorem hashBlock_openStep_unfold (env' : OpenExecEnv)
    (s : OpenState) (res : StepResult OpenState TerminalOut) :
    OpenStep (entryOpenProgForBody hashBlockProgram 0) env'
        hashBlockBody.sig.whereClauses s res ↔
      OpenStep hashBlockProgram env' hashBlockBody.sig.whereClauses s res :=
  Iff.rfl

private theorem hashBlock_openStep_eq (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 v2 v3 : Val) (mem : MemoryState)
    (res : StepResult OpenState TerminalOut)
    (hArgsOk :
      checkOpenArgsMatch hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
          .int .i64 false] = true) :
    OpenStep hashBlockProgram
      { canaryExecEnv with
        typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
      hashBlockBody.sig.whereClauses
      { frames :=
          [{ defId := 0, blockIdx := 0, stmtIdx := 0
           , locals := [.immediate none, .immediate (some v1),
               .immediate (some v2), .immediate (some v3)]
           , retDst := none }]
      , callerMem := ⟨[]⟩
      , mem := mem }
      res ↔
      ∃ digest,
        digest.length = 32 ∧
        LangValidBool hashTypeLayoutSpec .none digest = true ∧
        res = .step
          { frames :=
              [{ defId := 0, blockIdx := 1, stmtIdx := 0
               , locals := [.immediate (some (.bytes digest)),
                   .immediate (some v1), .immediate (some v2),
                   .immediate (some v3)]
               , retDst := none }]
          , callerMem := ⟨[]⟩
          , mem := mem } := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  have hArgsOk' :
      checkOpenArgsMatch hashBlockProgram env' [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
          .int .i64 false] = true :=
    hArgsOk
  have hStepEq :
      OpenStep hashBlockProgram env' hashBlockBody.sig.whereClauses
        { frames :=
            [{ defId := 0, blockIdx := 0, stmtIdx := 0
             , locals := [.immediate none, .immediate (some v1),
                 .immediate (some v2), .immediate (some v3)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := mem }
        res ↔
        (¬ (([v1, v2, v3] : List Val).length.beq 3 = true) ∧
            res = .fault .undefined) ∨
          (([v1, v2, v3] : List Val).length.beq 3 = true ∧
            ∃ out : TerminalOut,
              (∃ digest, digest.length = 32 ∧
                LangValidBool hashTypeLayoutSpec .none digest = true ∧
                out = .returned ⟨.bytes digest, ⟨[]⟩⟩) ∧
              match out with
              | .returned ⟨retVal, cm'⟩ =>
                  if !checkOpenVal hashBlockProgram env' retVal
                        (.adt hashAdtId []) then
                    res = .fault .undefined
                  else
                    match writeOpenPlace hashBlockProgram env' hashBlockBody
                        { defId := 0, blockIdx := 0, stmtIdx := 0
                        , locals := [.immediate none, .immediate (some v1),
                            .immediate (some v2), .immediate (some v3)]
                        , retDst := none }
                        ⟨0, []⟩ retVal with
                    | .error k => res = .fault k
                    | .ok frame₂ =>
                        res = .step
                          { frames :=
                              [{ frame₂ with blockIdx := 1, stmtIdx := 0 }]
                          , callerMem := cm'
                          , mem := mem }
              | .unwound cm' =>
                  res = openUnwindWith
                    { frames :=
                        [{ defId := 0, blockIdx := 0, stmtIdx := 0
                         , locals := [.immediate none, .immediate (some v1),
                             .immediate (some v2), .immediate (some v3)]
                         , retDst := none }]
                    , callerMem := ⟨[]⟩
                    , mem := mem }
                    cm' [] .continue_
                    (some
                      { defId := 0, blockIdx := 0, stmtIdx := 0
                      , locals := [.immediate none, .immediate (some v1),
                          .immediate (some v2), .immediate (some v3)]
                      , retDst := none })) := by
    unfold OpenStep OpenStepOnFrames OpenStepOnBodyOpt OpenStepOnBlockOpt
      OpenStepOnStmtEnd OpenStepOnTerm
    dsimp only
    rw [show openListGet? hashBlockProgram.bodies 0 = some hashBlockBody from rfl]
    dsimp only
    rw [show openListGet? hashBlockBody.basicBlocks 0 =
        some
          { statements := []
          , terminator :=
              .traitCall (.param 0) traitSha256LikeId [] 0
                [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]
                ⟨0, []⟩ (some 1) .continue_ } from rfl]
    dsimp only [Trusted.MirSemantics.getElem?, List.length, Nat.beq]
    rw [canary_ite_false]
    unfold AssumeGuaranteeTraitCall
    rw [canary_ite_false]
    rw [show env'.traitContracts traitSha256LikeId = some sha256Contract from rfl]
    dsimp only
    rw [canary_ite_false]
    rw [show lookupMethodSpec sha256Contract.methodSpecs 0 =
        some sha256MethodSpec from rfl]
    dsimp only
    rw [canary_ite_false]
    rw [show openListGet? hashBlockBody.locals 0 =
        some (.adt hashAdtId []) from rfl]
    dsimp only
    rw [canary_ite_false]
    rw [show evalOpenTySpec hashBlockProgram.traitRegistry normFuel env'.typeSpecs
        (normalizeOpenTy hashBlockProgram.traitRegistry normFuel (.param 0)) =
        some sp0 from rfl]
    rw [show evalNormOpenTySpecList env'.typeSpecs
        (List.map (normalizeOpenTy hashBlockProgram.traitRegistry normFuel) []) =
        some [] from rfl]
    rw [show resolveTraitAssocSpecs hashBlockProgram env'
        (normalizeOpenTy hashBlockProgram.traitRegistry normFuel (.param 0))
        traitSha256LikeId
        (List.map (normalizeOpenTy hashBlockProgram.traitRegistry normFuel) [])
        sha256Contract.assocTypeCount = some [] from rfl]
    dsimp only
    rw [show evalOpenOperands hashBlockProgram env' hashBlockBody
        { defId := 0, blockIdx := 0, stmtIdx := 0
        , locals := [.immediate none, .immediate (some v1),
            .immediate (some v2), .immediate (some v3)]
        , retDst := none }
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩] =
        .ok ([v1, v2, v3],
          { defId := 0, blockIdx := 0, stmtIdx := 0
          , locals := [.immediate none, .immediate (some v1),
              .immediate (some v2), .immediate (some v3)]
          , retDst := none }) from rfl]
    dsimp only
    rw [show sha256MethodSpec.sig.argTys.map
        (OpenMirTy.substAndNormalize hashBlockProgram.traitRegistry normFuel
          (normalizeOpenTy hashBlockProgram.traitRegistry normFuel (.param 0) ::
            List.map (normalizeOpenTy hashBlockProgram.traitRegistry normFuel) [])) =
        [.param 0, .ref .shared (.slice (.int .i8 false)), .int .i64 false]
      from rfl]
    rw [hArgsOk', Bool.not_true, canary_if_false]
    rw [show OpenMirTy.substAndNormalize hashBlockProgram.traitRegistry normFuel
        (normalizeOpenTy hashBlockProgram.traitRegistry normFuel (.param 0) ::
          List.map (normalizeOpenTy hashBlockProgram.traitRegistry normFuel) [])
        sha256MethodSpec.sig.retTy = .adt hashAdtId [] from rfl]
    dsimp only [sha256MethodSpec]
    exact Iff.rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hStepEq]
  have hWrOfValid :
      ∀ digest : List AllocByte,
        LangValidBool hashTypeLayoutSpec .none digest = true →
        checkOpenVal hashBlockProgram env' (.bytes digest) (.adt hashAdtId []) =
          true ∧
        writeOpenPlace hashBlockProgram env' hashBlockBody
          { defId := 0, blockIdx := 0, stmtIdx := 0
          , locals := [.immediate none, .immediate (some v1),
              .immediate (some v2), .immediate (some v3)]
          , retDst := none }
          ⟨0, []⟩ (.bytes digest) =
          .ok
            { defId := 0, blockIdx := 0, stmtIdx := 0
            , locals := [.immediate (some (.bytes digest)),
                .immediate (some v1), .immediate (some v2),
                .immediate (some v3)]
            , retDst := none } := by
    intro digest hValid
    have hChk :
        checkOpenVal hashBlockProgram env' (.bytes digest) (.adt hashAdtId []) =
          true := by
      unfold checkOpenVal evalOpenTySpec checkOpenValOnSpec
      change LangValidBool hashTypeLayoutSpec .none digest = true
      exact hValid
    refine ⟨hChk, ?_⟩
    unfold writeOpenPlace
    dsimp only [hashBlockBody, openListGet?, Trusted.MirSemantics.getElem?,
      setElem?, List.isEmpty]
    simp only [Bool.not_true, canary_if_false, hChk]
  constructor
  · intro h
    cases h with
    | inl hNot => exact False.elim (hNot.1 rfl)
    | inr hOk =>
        let ⟨_, out, ⟨digest, hLen, hValid, hOutEq⟩, hOut⟩ := hOk
        subst hOutEq
        let ⟨hChk, hWr⟩ := hWrOfValid digest hValid
        dsimp only at hOut
        rw [hChk, Bool.not_true, canary_if_false, hWr] at hOut
        exact ⟨digest, hLen, hValid, hOut⟩
  · intro ⟨digest, hLen, hValid, hRes⟩
    subst hRes
    let ⟨hChk, hWr⟩ := hWrOfValid digest hValid
    refine .inr ⟨rfl, .returned ⟨.bytes digest, ⟨[]⟩⟩,
      ⟨digest, hLen, hValid, rfl⟩, ?_⟩
    dsimp only
    rw [hChk, Bool.not_true, canary_if_false, hWr]

private theorem hashBlock_step_preserves (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 v2 v3 : Val)
    (hArgsOk :
      checkOpenArgsMatch hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
          .int .i64 false] = true)
    (s₁ s₂ : OpenState)
    (hInv : hashBlockInv v1 v2 v3 s₁)
    (hStep :
      OpenStep hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        hashBlockBody.sig.whereClauses s₁ (.step s₂)) :
    hashBlockInv v1 v2 v3 s₂ := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s₁ with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          rw [hashBlock_openStep_eq sp0 paramInvs assocSpecs v1 v2 v3 mem
            (.step s₂) hArgsOk] at hStep
          let ⟨digest, _, _, hEq⟩ := hStep
          cases hEq
          exact .inr ⟨digest, ⟨[]⟩, rfl, rfl⟩
  | inr h1 =>
      let ⟨digest, cm', hF, hCm⟩ := h1
      cases s₁ with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF
          rw [hCm] at hStep
          change StepResult.step s₂ = openEvalDetStep hashBlockProgram env' _ at hStep
          have hDone : openEvalDetStep hashBlockProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 1, stmtIdx := 0
                   , locals := [.immediate (some (.bytes digest)),
                       .immediate (some v1), .immediate (some v2),
                       .immediate (some v3)]
                   , retDst := none }]
              , callerMem := cm'
              , mem := mem } =
              .done (.returned ⟨.bytes digest, cm'⟩) := by
            unfold openEvalDetStep openEvalDetStepAux OpenProgram.toDay1?
            rfl
          rw [hDone] at hStep
          exact canary_done_ne_step hStep.symm

private theorem hashBlock_inv_progress (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 v2 v3 : Val)
    (hArgsOk :
      checkOpenArgsMatch hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
          .int .i64 false] = true)
    (s : OpenState)
    (hInv : hashBlockInv v1 v2 v3 s) :
    ∃ res : StepResult OpenState TerminalOut,
      OpenStep hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        hashBlockBody.sig.whereClauses s res := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          let digest : List AllocByte := repeatItem (.init 0 none) 32
          have hValid : LangValidBool hashTypeLayoutSpec .none digest = true := by
            unfold LangValidBool hashTypeLayoutSpec
            rfl
          let nextS : OpenState :=
            { frames :=
                [{ defId := 0, blockIdx := 1, stmtIdx := 0
                 , locals := [.immediate (some (.bytes digest)),
                     .immediate (some v1), .immediate (some v2),
                     .immediate (some v3)]
                 , retDst := none }]
            , callerMem := ⟨[]⟩
            , mem := mem }
          refine ⟨.step nextS, ?_⟩
          rw [hashBlock_openStep_eq sp0 paramInvs assocSpecs v1 v2 v3 mem
            (.step nextS) hArgsOk]
          exact ⟨digest, length_repeatItem _ 32, hValid, rfl⟩
  | inr h1 =>
      let ⟨digest, cm', hF, hCm⟩ := h1
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF
          exact ⟨openEvalDetStep hashBlockProgram env' _, rfl⟩

private theorem hashBlock_inv_no_fault (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 v2 v3 : Val)
    (hArgsOk :
      checkOpenArgsMatch hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
          .int .i64 false] = true)
    (s : OpenState) (k : FaultKind)
    (hInv : hashBlockInv v1 v2 v3 s)
    (hFault :
      OpenStep hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        hashBlockBody.sig.whereClauses s (.fault k)) :
    False := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          rw [hashBlock_openStep_eq sp0 paramInvs assocSpecs v1 v2 v3 mem
            (.fault k) hArgsOk] at hFault
          let ⟨_, _, _, hEq⟩ := hFault
          exact canary_step_ne_fault hEq.symm
  | inr h1 =>
      let ⟨digest, cm', hF, hCm⟩ := h1
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF
          rw [hCm] at hFault
          change StepResult.fault k = openEvalDetStep hashBlockProgram env' _ at hFault
          have hDone : openEvalDetStep hashBlockProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 1, stmtIdx := 0
                   , locals := [.immediate (some (.bytes digest)),
                       .immediate (some v1), .immediate (some v2),
                       .immediate (some v3)]
                   , retDst := none }]
              , callerMem := cm'
              , mem := mem } =
              .done (.returned ⟨.bytes digest, cm'⟩) := by
            unfold openEvalDetStep openEvalDetStepAux OpenProgram.toDay1?
            rfl
          rw [hDone] at hFault
          exact canary_done_ne_fault hFault.symm

private theorem hashBlock_reaches_inv (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 v2 v3 : Val)
    (hArgsOk :
      checkOpenArgsMatch hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
          .int .i64 false] = true) :
    ∀ s₀ s : OpenState,
      OpenReaches hashBlockProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        hashBlockBody.sig.whereClauses s₀ s →
      hashBlockInv v1 v2 v3 s₀ →
      hashBlockInv v1 v2 v3 s
  | _, _, .refl _, h0 => h0
  | s₀, s, .step hStep hRest, h0 =>
      hashBlock_reaches_inv sp0 paramInvs assocSpecs v1 v2 v3 hArgsOk _ s hRest
        (hashBlock_step_preserves sp0 paramInvs assocSpecs v1 v2 v3 hArgsOk s₀ _
          h0 hStep)

private theorem openInitState_hashBlock (env' : OpenExecEnv) (v1 v2 v3 : Val)
    (hCheck :
      checkOpenArgsMatch hashBlockProgram env' [v1, v2, v3]
        [.param 0, .ref .shared (.slice (.int .i8 false)),
         .int .i64 false] = true) :
    openInitState hashBlockProgram env' { args := [v1, v2, v3] } =
      .ok
        { frames :=
            [{ defId := 0
             , blockIdx := 0
             , stmtIdx := 0
             , locals :=
                 [.immediate none, .immediate (some v1),
                   .immediate (some v2), .immediate (some v3)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := MemoryState.empty } := by
  unfold openInitState openInitStateAux
  rw [show OpenProgram.toDay1? hashBlockProgram = none from rfl]
  dsimp only
  rw [canary_ite_false]
  rw [show openListGet? hashBlockProgram.bodies hashBlockProgram.entryDefId =
      some hashBlockBody from rfl]
  dsimp only
  rw [canary_ite_false]
  unfold initOpenLocals
  dsimp only
  rw [show (hashBlockBody.locals.drop 1).take hashBlockBody.argumentCount =
      [.param 0, .ref .shared (.slice (.int .i8 false)), .int .i64 false]
    from rfl]
  rw [hCheck]
  rw [canary_ite_false]
  rw [show initOpenLocalsBuild hashBlockProgram hashBlockBody 0
      hashBlockBody.locals [v1, v2, v3] =
      some [.immediate none, .immediate (some v1), .immediate (some v2),
        .immediate (some v3)] from rfl]
  rfl
  · rfl
  · rfl
  · rfl

private theorem hashBlock_single_inst (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hWf0 : WellFormedTypeLayoutSpec sp0)
    (hSized : sp0.isSized = true) :
    let env' : OpenExecEnv :=
      { canaryExecEnv with
        typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
    OpenBodyStaticAdmitted hashBlockProgram env' hashBlockBody ∧
    ∀ args : List Val,
      ValidOpenEntryArgs hashBlockProgram env' hashBlockBody args →
      (hashBlockBody.isUnsafe = true → True) →
      OpenWellFormed (entryOpenProgForBody hashBlockProgram 0) env'
        hashBlockBody.sig.whereClauses { args := args } := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  let sliceU8Spec : TypeLayoutSpec :=
    { isSized := false
    , alignLog2 := 0
    , sizeForMeta := fun m => match m with
        | .sliceLen len =>
            if 1 * len ≤ isizeMax then some (1 * len) else none
        | _ => none
    , inhabited := true
    , hasUnsafeCell := false
    , rolesForMeta := fun m => match m with
        | .sliceLen len =>
            if 1 * len ≤ isizeMax then
              some (repeatConcat [.valueByte .anyByte] len)
            else none
        | _ => none }
  have hAdmitted : OpenBodyStaticAdmitted hashBlockProgram env' hashBlockBody := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    refine ⟨⟨hashTypeLayoutSpec, rfl, rfl, wellFormed_hashTypeLayoutSpec, rfl⟩,
      ⟨sp0, rfl, rfl, hWf0, hSized⟩,
      ⟨pointerTypeLayoutSpec sliceU8Spec true, rfl, rfl,
        wellFormed_pointerTypeLayoutSpec sliceU8Spec true (by decide), rfl⟩,
      ⟨intTypeLayoutSpec .i64, rfl, rfl, wellFormed_intTypeLayoutSpec .i64, rfl⟩,
      True.intro⟩
  refine ⟨hAdmitted, fun args hArgs _ => ?_⟩
  let ⟨v1, v2, v3, hArgsEq, hV1, hV2, hV3⟩ :=
    checkOpenArgsMatch_three_shape hashBlockProgram env'
      (.param 0) (.ref .shared (.slice (.int .i8 false)))
      (.int .i64 false) args hArgs.1
  subst hArgsEq
  let sInit : OpenState :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals :=
             [.immediate none, .immediate (some v1), .immediate (some v2),
               .immediate (some v3)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  have hCheck : checkOpenArgsMatch hashBlockProgram env' [v1, v2, v3]
      [.param 0, .ref .shared (.slice (.int .i8 false)), .int .i64 false] =
      true :=
    bool_and_eq_true hV1 (bool_and_eq_true hV2 (bool_and_eq_true hV3 rfl))
  have hInit := openInitState_hashBlock env' v1 v2 v3 hCheck
  refine ⟨⟨sInit, hInit, fun s hReach => ?_⟩, fun s₀ hS0 s k hReach hFault => ?_⟩
  · have hInv := hashBlock_reaches_inv sp0 paramInvs assocSpecs v1 v2 v3 hCheck
      sInit s hReach (Or.inl ⟨rfl, rfl⟩)
    exact hashBlock_inv_progress sp0 paramInvs assocSpecs v1 v2 v3 hCheck s hInv
  · have hEqS0 := canary_except_ok_inj (hInit.symm.trans hS0)
    have hInv := hashBlock_reaches_inv sp0 paramInvs assocSpecs v1 v2 v3 hCheck
      s₀ s hReach (hEqS0 ▸ Or.inl ⟨rfl, rfl⟩)
    exact hashBlock_inv_no_fault sp0 paramInvs assocSpecs v1 v2 v3 hCheck s k
      hInv hFault

/-- Canary 1
(`hash_block<H: Sha256Like>(h: H, block: &[u8], offset: u64) -> Hash`):
kernel-checked parametric fault-freedom across all well-formed `TypeLayoutSpec`
instantiations of `H`. -/
theorem canary_hash_block_parametric_verified :
    ParametricBodyVerified hashBlockProgram canaryExecEnv 0 hashBlockBody
      (fun _ _ => True) := by
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun paramSpecs paramInvs assocSpecs hLen hWf _ hWhere => ?_⟩
  cases paramSpecs with
  | nil => exact canary_nat_zero_ne_succ hLen
  | cons sp0 rest =>
      cases rest with
      | cons _ _ => exact canary_nat_succ_ne_zero (Nat.succ.inj hLen)
      | nil =>
          let ⟨spS, hEvS, _, hSized⟩ := hWhere.2.1
          cases hEvS
          exact hashBlock_single_inst sp0 paramInvs assocSpecs hWf.1 hSized

/-- Reachable state invariant for `verify_aligned<B: ByteSource<Out = u64>>`. -/
def verifyAlignedInv (v1 v2 : Val) (s : OpenState) : Prop :=
  (s.frames =
      [{ defId := 0
       , blockIdx := 0
       , stmtIdx := 0
       , locals :=
           [.immediate none, .immediate (some v1), .immediate (some v2)]
       , retDst := none }] ∧
    s.callerMem = ⟨[]⟩) ∨
  (∃ retVal : Val, ∃ cm : CallerMemory,
    s.frames =
      [{ defId := 0
       , blockIdx := 1
       , stmtIdx := 0
       , locals :=
           [.immediate (some retVal), .immediate (some v1),
             .immediate (some v2)]
       , retDst := none }] ∧
    s.callerMem = cm)

private theorem verifyAligned_openStep_eq (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hOutEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
      some (intTypeLayoutSpec .i64))
    (v1 v2 : Val) (mem : MemoryState)
    (res : StepResult OpenState TerminalOut)
    (hArgsOk :
      checkOpenArgsMatch verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true) :
    OpenStep verifyAlignedProgram
      { canaryExecEnv with
        typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
      verifyAlignedBody.sig.whereClauses
      { frames :=
          [{ defId := 0, blockIdx := 0, stmtIdx := 0
           , locals := [.immediate none, .immediate (some v1),
               .immediate (some v2)]
           , retDst := none }]
      , callerMem := ⟨[]⟩
      , mem := mem }
      res ↔
      ∃ retVal : Val,
        checkOpenValOnSpec retVal (some (intTypeLayoutSpec .i64)) = true ∧
        res = .step
          { frames :=
              [{ defId := 0, blockIdx := 1, stmtIdx := 0
               , locals := [.immediate (some retVal), .immediate (some v1),
                   .immediate (some v2)]
               , retDst := none }]
          , callerMem := ⟨[]⟩
          , mem := mem } := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  have hArgsOk' :
      checkOpenArgsMatch verifyAlignedProgram env' [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true :=
    hArgsOk
  have hAssoc :
      resolveTraitAssocSpecs verifyAlignedProgram env'
        (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel (.param 0))
        traitByteSourceId
        (List.map (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel) [])
        byteSourceContract.assocTypeCount =
      some [intTypeLayoutSpec .i64] := by
    unfold resolveTraitAssocSpecs
    dsimp only [byteSourceContract]
    unfold resolveTraitAssocSpecsAux evalOpenTySpec
    rw [show normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel (.param 0) =
        .param 0 from rfl]
    rw [show List.map (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel)
        ([] : List OpenMirTy) = [] from rfl]
    rw [show normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel
        (.assocProj (.param 0) traitByteSourceId [] 0) =
        .assocProj (.param 0) traitByteSourceId [] 0 from rfl]
    rw [show resolveTraitAssocSpecsAux verifyAlignedProgram env' (.param 0)
        traitByteSourceId [] (0 + 1) 0 = some [] from rfl]
    dsimp only [evalNormOpenTySpec]
    change
      (match assocSpecs (.param 0) traitByteSourceId [] 0,
          (some [] : Option (List TypeLayoutSpec)) with
      | some sp, some rest => some (sp :: rest)
      | _, _ => none) = some [intTypeLayoutSpec .i64]
    rw [hOutEq]
  have hStepEq :
      OpenStep verifyAlignedProgram env' verifyAlignedBody.sig.whereClauses
        { frames :=
            [{ defId := 0, blockIdx := 0, stmtIdx := 0
             , locals := [.immediate none, .immediate (some v1),
                 .immediate (some v2)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := mem }
        res ↔
        (¬ (([v1, v2] : List Val).length.beq 2 = true) ∧
            res = .fault .undefined) ∨
          (([v1, v2] : List Val).length.beq 2 = true ∧
            ∃ out : TerminalOut,
              (∃ v,
                checkOpenValOnSpec v (some (intTypeLayoutSpec .i64)) = true ∧
                out = .returned ⟨v, ⟨[]⟩⟩) ∧
              match out with
              | .returned ⟨retVal, cm'⟩ =>
                  if !checkOpenVal verifyAlignedProgram env' retVal
                        (.assocProj (.param 0) traitByteSourceId [] 0) then
                    res = .fault .undefined
                  else
                    match writeOpenPlace verifyAlignedProgram env'
                        verifyAlignedBody
                        { defId := 0, blockIdx := 0, stmtIdx := 0
                        , locals := [.immediate none, .immediate (some v1),
                            .immediate (some v2)]
                        , retDst := none }
                        ⟨0, []⟩ retVal with
                    | .error k => res = .fault k
                    | .ok frame₂ =>
                        res = .step
                          { frames :=
                              [{ frame₂ with blockIdx := 1, stmtIdx := 0 }]
                          , callerMem := cm'
                          , mem := mem }
              | .unwound cm' =>
                  res = openUnwindWith
                    { frames :=
                        [{ defId := 0, blockIdx := 0, stmtIdx := 0
                         , locals := [.immediate none, .immediate (some v1),
                             .immediate (some v2)]
                         , retDst := none }]
                    , callerMem := ⟨[]⟩
                    , mem := mem }
                    cm' [] .continue_
                    (some
                      { defId := 0, blockIdx := 0, stmtIdx := 0
                      , locals := [.immediate none, .immediate (some v1),
                          .immediate (some v2)]
                      , retDst := none })) := by
    unfold OpenStep OpenStepOnFrames OpenStepOnBodyOpt OpenStepOnBlockOpt
      OpenStepOnStmtEnd OpenStepOnTerm
    dsimp only
    rw [show openListGet? verifyAlignedProgram.bodies 0 =
        some verifyAlignedBody from rfl]
    dsimp only
    rw [show openListGet? verifyAlignedBody.basicBlocks 0 =
        some
          { statements := []
          , terminator :=
              .traitCall (.param 0) traitByteSourceId [] 0
                [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
                ⟨0, []⟩ (some 1) .continue_ } from rfl]
    dsimp only [Trusted.MirSemantics.getElem?, List.length, Nat.beq]
    rw [canary_ite_false]
    unfold AssumeGuaranteeTraitCall
    rw [canary_ite_false]
    rw [show env'.traitContracts traitByteSourceId =
        some byteSourceContract from rfl]
    dsimp only
    rw [canary_ite_false]
    rw [show lookupMethodSpec byteSourceContract.methodSpecs 0 =
        some byteSourceMethodSpec from rfl]
    dsimp only
    rw [canary_ite_false]
    rw [show openListGet? verifyAlignedBody.locals 0 =
        some (.assocProj (.param 0) traitByteSourceId [] 0) from rfl]
    dsimp only
    rw [canary_ite_false]
    rw [show evalOpenTySpec verifyAlignedProgram.traitRegistry normFuel
        env'.typeSpecs
        (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel (.param 0)) =
        some sp0 from rfl]
    rw [show evalNormOpenTySpecList env'.typeSpecs
        (List.map (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel) []) =
        some [] from rfl]
    rw [hAssoc]
    dsimp only
    rw [show evalOpenOperands verifyAlignedProgram env' verifyAlignedBody
        { defId := 0, blockIdx := 0, stmtIdx := 0
        , locals := [.immediate none, .immediate (some v1),
            .immediate (some v2)]
        , retDst := none }
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩] =
        .ok ([v1, v2],
          { defId := 0, blockIdx := 0, stmtIdx := 0
          , locals := [.immediate none, .immediate (some v1),
              .immediate (some v2)]
          , retDst := none }) from rfl]
    dsimp only
    rw [show byteSourceMethodSpec.sig.argTys.map
        (OpenMirTy.substAndNormalize verifyAlignedProgram.traitRegistry normFuel
          (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel (.param 0) ::
            List.map (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel) [])) =
        [.ref .shared (.param 0), .int .i64 false] from rfl]
    rw [hArgsOk', Bool.not_true, canary_if_false]
    rw [show OpenMirTy.substAndNormalize verifyAlignedProgram.traitRegistry normFuel
        (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel (.param 0) ::
          List.map (normalizeOpenTy verifyAlignedProgram.traitRegistry normFuel) [])
        byteSourceMethodSpec.sig.retTy =
        .assocProj (.param 0) traitByteSourceId [] 0 from rfl]
    dsimp only [byteSourceMethodSpec]
    exact Iff.rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hStepEq]
  have hWrOfValid :
      ∀ retVal : Val,
        checkOpenValOnSpec retVal (some (intTypeLayoutSpec .i64)) = true →
        checkOpenVal verifyAlignedProgram env' retVal
          (.assocProj (.param 0) traitByteSourceId [] 0) = true ∧
        writeOpenPlace verifyAlignedProgram env' verifyAlignedBody
          { defId := 0, blockIdx := 0, stmtIdx := 0
          , locals := [.immediate none, .immediate (some v1),
              .immediate (some v2)]
          , retDst := none }
          ⟨0, []⟩ retVal =
          .ok
            { defId := 0, blockIdx := 0, stmtIdx := 0
            , locals := [.immediate (some retVal), .immediate (some v1),
                .immediate (some v2)]
            , retDst := none } := by
    intro retVal hChkSpec
    have hChk :
        checkOpenVal verifyAlignedProgram env' retVal
          (.assocProj (.param 0) traitByteSourceId [] 0) = true := by
      unfold checkOpenVal evalOpenTySpec normalizeOpenTy evalNormOpenTySpec
      change checkOpenValOnSpec retVal
        (assocSpecs (.param 0) traitByteSourceId [] 0) = true
      rw [hOutEq]
      exact hChkSpec
    refine ⟨hChk, ?_⟩
    unfold writeOpenPlace
    dsimp only [verifyAlignedBody, openListGet?, Trusted.MirSemantics.getElem?,
      setElem?, List.isEmpty]
    simp only [Bool.not_true, canary_if_false, hChk]
  constructor
  · intro h
    cases h with
    | inl hNot => exact False.elim (hNot.1 rfl)
    | inr hOk =>
        let ⟨_, out, ⟨retVal, hChkSpec, hOutEqVal⟩, hOut⟩ := hOk
        subst hOutEqVal
        let ⟨hChk, hWr⟩ := hWrOfValid retVal hChkSpec
        dsimp only at hOut
        rw [hChk, Bool.not_true, canary_if_false, hWr] at hOut
        exact ⟨retVal, hChkSpec, hOut⟩
  · intro ⟨retVal, hChkSpec, hRes⟩
    subst hRes
    let ⟨hChk, hWr⟩ := hWrOfValid retVal hChkSpec
    refine .inr ⟨rfl, .returned ⟨retVal, ⟨[]⟩⟩,
      ⟨retVal, hChkSpec, rfl⟩, ?_⟩
    dsimp only
    rw [hChk, Bool.not_true, canary_if_false, hWr]

private theorem verifyAligned_step_preserves (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hOutEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
      some (intTypeLayoutSpec .i64))
    (v1 v2 : Val)
    (hArgsOk :
      checkOpenArgsMatch verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true)
    (s₁ s₂ : OpenState)
    (hInv : verifyAlignedInv v1 v2 s₁)
    (hStep :
      OpenStep verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        verifyAlignedBody.sig.whereClauses s₁ (.step s₂)) :
    verifyAlignedInv v1 v2 s₂ := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s₁ with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          rw [verifyAligned_openStep_eq sp0 paramInvs assocSpecs hOutEq v1 v2 mem
            (.step s₂) hArgsOk] at hStep
          let ⟨retVal, _, hEq⟩ := hStep
          cases hEq
          exact .inr ⟨retVal, ⟨[]⟩, rfl, rfl⟩
  | inr h1 =>
      let ⟨retVal, cm', hF, hCm⟩ := h1
      cases s₁ with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF
          rw [hCm] at hStep
          change StepResult.step s₂ = openEvalDetStep verifyAlignedProgram env' _ at hStep
          have hDone : openEvalDetStep verifyAlignedProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 1, stmtIdx := 0
                   , locals := [.immediate (some retVal),
                       .immediate (some v1), .immediate (some v2)]
                   , retDst := none }]
              , callerMem := cm'
              , mem := mem } =
              .done (.returned ⟨retVal, cm'⟩) := by
            unfold openEvalDetStep openEvalDetStepAux OpenProgram.toDay1?
            rfl
          rw [hDone] at hStep
          exact canary_done_ne_step hStep.symm

private theorem verifyAligned_inv_progress (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hOutEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
      some (intTypeLayoutSpec .i64))
    (v1 v2 : Val)
    (hArgsOk :
      checkOpenArgsMatch verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true)
    (s : OpenState)
    (hInv : verifyAlignedInv v1 v2 s) :
    ∃ res : StepResult OpenState TerminalOut,
      OpenStep verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        verifyAlignedBody.sig.whereClauses s res := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          let retVal : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 0⟩
          have hChkSpec : checkOpenValOnSpec retVal (some (intTypeLayoutSpec .i64)) =
              true := by
            rfl
          let nextS : OpenState :=
            { frames :=
                [{ defId := 0, blockIdx := 1, stmtIdx := 0
                 , locals := [.immediate (some retVal), .immediate (some v1),
                     .immediate (some v2)]
                 , retDst := none }]
            , callerMem := ⟨[]⟩
            , mem := mem }
          refine ⟨.step nextS, ?_⟩
          rw [verifyAligned_openStep_eq sp0 paramInvs assocSpecs hOutEq v1 v2 mem
            (.step nextS) hArgsOk]
          exact ⟨retVal, hChkSpec, rfl⟩
  | inr h1 =>
      let ⟨retVal, cm', hF, hCm⟩ := h1
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF
          exact ⟨openEvalDetStep verifyAlignedProgram env' _, rfl⟩

private theorem verifyAligned_inv_no_fault (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hOutEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
      some (intTypeLayoutSpec .i64))
    (v1 v2 : Val)
    (hArgsOk :
      checkOpenArgsMatch verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true)
    (s : OpenState) (k : FaultKind)
    (hInv : verifyAlignedInv v1 v2 s)
    (hFault :
      OpenStep verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        verifyAlignedBody.sig.whereClauses s (.fault k)) :
    False := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          rw [verifyAligned_openStep_eq sp0 paramInvs assocSpecs hOutEq v1 v2 mem
            (.fault k) hArgsOk] at hFault
          let ⟨_, _, hEq⟩ := hFault
          exact canary_step_ne_fault hEq.symm
  | inr h1 =>
      let ⟨retVal, cm', hF, hCm⟩ := h1
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF
          rw [hCm] at hFault
          change StepResult.fault k = openEvalDetStep verifyAlignedProgram env' _ at hFault
          have hDone : openEvalDetStep verifyAlignedProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 1, stmtIdx := 0
                   , locals := [.immediate (some retVal),
                       .immediate (some v1), .immediate (some v2)]
                   , retDst := none }]
              , callerMem := cm'
              , mem := mem } =
              .done (.returned ⟨retVal, cm'⟩) := by
            unfold openEvalDetStep openEvalDetStepAux OpenProgram.toDay1?
            rfl
          rw [hDone] at hFault
          exact canary_done_ne_fault hFault.symm

private theorem verifyAligned_reaches_inv (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hOutEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
      some (intTypeLayoutSpec .i64))
    (v1 v2 : Val)
    (hArgsOk :
      checkOpenArgsMatch verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true) :
    ∀ s₀ s : OpenState,
      OpenReaches verifyAlignedProgram
        { canaryExecEnv with
          typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        verifyAlignedBody.sig.whereClauses s₀ s →
      verifyAlignedInv v1 v2 s₀ →
      verifyAlignedInv v1 v2 s
  | _, _, .refl _, h0 => h0
  | s₀, s, .step hStep hRest, h0 =>
      verifyAligned_reaches_inv sp0 paramInvs assocSpecs hOutEq v1 v2 hArgsOk _ s
        hRest
        (verifyAligned_step_preserves sp0 paramInvs assocSpecs hOutEq v1 v2
          hArgsOk s₀ _ h0 hStep)

private theorem openInitState_verifyAligned (env' : OpenExecEnv) (v1 v2 : Val)
    (hCheck :
      checkOpenArgsMatch verifyAlignedProgram env' [v1, v2]
        [.ref .shared (.param 0), .int .i64 false] = true) :
    openInitState verifyAlignedProgram env' { args := [v1, v2] } =
      .ok
        { frames :=
            [{ defId := 0
             , blockIdx := 0
             , stmtIdx := 0
             , locals :=
                 [.immediate none, .immediate (some v1), .immediate (some v2)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := MemoryState.empty } := by
  unfold openInitState openInitStateAux
  rw [show OpenProgram.toDay1? verifyAlignedProgram = none from rfl]
  dsimp only
  rw [canary_ite_false]
  rw [show openListGet? verifyAlignedProgram.bodies
      verifyAlignedProgram.entryDefId = some verifyAlignedBody from rfl]
  dsimp only
  rw [canary_ite_false]
  unfold initOpenLocals
  dsimp only
  rw [show (verifyAlignedBody.locals.drop 1).take
      verifyAlignedBody.argumentCount =
      [.ref .shared (.param 0), .int .i64 false] from rfl]
  rw [hCheck]
  rw [canary_ite_false]
  rw [show initOpenLocalsBuild verifyAlignedProgram verifyAlignedBody 0
      verifyAlignedBody.locals [v1, v2] =
      some [.immediate none, .immediate (some v1), .immediate (some v2)]
    from rfl]
  rfl
  · rfl
  · rfl
  · rfl

private theorem verifyAligned_single_inst (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hWf0 : WellFormedTypeLayoutSpec sp0)
    (hOutEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
      some (intTypeLayoutSpec .i64)) :
    let env' : OpenExecEnv :=
      { canaryExecEnv with
        typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
    OpenBodyStaticAdmitted verifyAlignedProgram env' verifyAlignedBody ∧
    ∀ args : List Val,
      ValidOpenEntryArgs verifyAlignedProgram env' verifyAlignedBody args →
      (verifyAlignedBody.isUnsafe = true → True) →
      OpenWellFormed (entryOpenProgForBody verifyAlignedProgram 0) env'
        verifyAlignedBody.sig.whereClauses { args := args } := by
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  have hAdmitted :
      OpenBodyStaticAdmitted verifyAlignedProgram env' verifyAlignedBody := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    refine ⟨⟨intTypeLayoutSpec .i64, rfl, ?_, wellFormed_intTypeLayoutSpec .i64,
        rfl⟩,
      ⟨pointerTypeLayoutSpec sp0 true, rfl, rfl,
        wellFormed_pointerTypeLayoutSpec sp0 true hWf0.2.2.2.1, rfl⟩,
      ⟨intTypeLayoutSpec .i64, rfl, rfl, wellFormed_intTypeLayoutSpec .i64, rfl⟩,
      True.intro⟩
    unfold evalOpenTySpec normalizeOpenTy evalNormOpenTySpec
    dsimp only [verifyAlignedProgram, traitByteSourceId]
    exact hOutEq
  refine ⟨hAdmitted, fun args hArgs _ => ?_⟩
  let ⟨v1, v2, hArgsEq, hV1, hV2⟩ :=
    checkOpenArgsMatch_two_shape verifyAlignedProgram env'
      (.ref .shared (.param 0)) (.int .i64 false) args hArgs.1
  subst hArgsEq
  let sInit : OpenState :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals :=
             [.immediate none, .immediate (some v1), .immediate (some v2)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  have hCheck : checkOpenArgsMatch verifyAlignedProgram env' [v1, v2]
      [.ref .shared (.param 0), .int .i64 false] = true :=
    bool_and_eq_true hV1 (bool_and_eq_true hV2 rfl)
  have hInit := openInitState_verifyAligned env' v1 v2 hCheck
  refine ⟨⟨sInit, hInit, fun s hReach => ?_⟩, fun s₀ hS0 s k hReach hFault => ?_⟩
  · have hInv := verifyAligned_reaches_inv sp0 paramInvs assocSpecs hOutEq v1 v2
      hCheck sInit s hReach (Or.inl ⟨rfl, rfl⟩)
    exact verifyAligned_inv_progress sp0 paramInvs assocSpecs hOutEq v1 v2
      hCheck s hInv
  · have hEqS0 := canary_except_ok_inj (hInit.symm.trans hS0)
    have hInv := verifyAligned_reaches_inv sp0 paramInvs assocSpecs hOutEq v1 v2
      hCheck s₀ s hReach (hEqS0 ▸ Or.inl ⟨rfl, rfl⟩)
    exact verifyAligned_inv_no_fault sp0 paramInvs assocSpecs hOutEq v1 v2
      hCheck s k hInv hFault

/-- Canary 2 (`verify_aligned<B: ByteSource<Out = u64>>` taking `&B` and `u64`
and returning `B::Out`): kernel-checked parametric fault-freedom with an
associated-type projection and equality constraint. -/
theorem canary_verify_aligned_parametric_verified :
    ParametricBodyVerified verifyAlignedProgram canaryExecEnv 0
      verifyAlignedBody (fun _ _ => True) := by
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun paramSpecs paramInvs assocSpecs hLen hWf _ hWhere => ?_⟩
  cases paramSpecs with
  | nil => exact canary_nat_zero_ne_succ hLen
  | cons sp0 rest =>
      cases rest with
      | cons _ _ => exact canary_nat_succ_ne_zero (Nat.succ.inj hLen)
      | nil =>
          have hEq : assocSpecs (.param 0) traitByteSourceId [] 0 =
              some (intTypeLayoutSpec .i64) := by
            let ⟨sp, hLhs, hRhs, _⟩ := hWhere.2.1
            have hLhs' : assocSpecs (.param 0) traitByteSourceId [] 0 =
                some sp := by
              unfold evalOpenTySpec at hLhs
              rw [show normalizeOpenTy verifyAlignedProgram.traitRegistry
                  normFuel (.assocProj (.param 0) traitByteSourceId [] 0) =
                  .assocProj (.param 0) traitByteSourceId [] 0 from rfl] at hLhs
              exact hLhs
            have hRhs' : some (intTypeLayoutSpec .i64) = some sp := by
              unfold evalOpenTySpec at hRhs
              rw [show normalizeOpenTy verifyAlignedProgram.traitRegistry
                  normFuel (.int .i64 false) = .int .i64 false from rfl] at hRhs
              exact hRhs
            cases hRhs'
            exact hLhs'
          exact verifyAligned_single_inst sp0 paramInvs assocSpecs hWf.1 hEq

/-- Negative Canary 4: omitting the `H: Sha256Like` `WhereClause` causes
`.traitCall` to fail closed with `.fault .unsupported`, refuting
`ParametricBodyVerified`. -/
theorem canary_missing_bound_not_parametric_verified :
    ¬ ParametricBodyVerified missingBoundProgram canaryExecEnv 0
        missingBoundBody (fun _ _ => True) := by
  intro hVer
  let env' : OpenExecEnv :=
    { canaryExecEnv with
      typeSpecs := substTypeSpecEnv canaryExecEnv.typeSpecs
        [intTypeLayoutSpec .i64] [fun _ => True] (fun _ _ _ _ => none) }
  have hWf64 := wellFormed_intTypeLayoutSpec .i64
  have hInvsWf : AllParamInvsWf [intTypeLayoutSpec .i64] [fun _ => True] :=
    ⟨fun _ _ => ⟨repeatItem (.init 0 none) 8, int_zero_bytes_valid .i64,
      True.intro⟩, True.intro⟩
  have hWhere : AllWhereParamsSem missingBoundProgram env'
      missingBoundBody.sig.whereClauses :=
    ⟨⟨intTypeLayoutSpec .i64, rfl, hWf64, rfl⟩, True.intro⟩
  have hInst := hVer.2.2.2 [intTypeLayoutSpec .i64] [fun _ => True]
    (fun _ _ _ _ => none) rfl ⟨hWf64, True.intro⟩ hInvsWf hWhere
  let v1 : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 0⟩
  let v2 : Val := .ptr ⟨some 1, (0 : UInt64), .isize⟩
  let v3 : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 0⟩
  have hArgs : ValidOpenEntryArgs missingBoundProgram env' missingBoundBody
      [v1, v2, v3] := ⟨by rfl, True.intro, True.intro, True.intro, True.intro⟩
  have hWf := hInst.2 [v1, v2, v3] hArgs (fun _ => True.intro)
  let sInit : OpenState :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals :=
             [.immediate none, .immediate (some v1), .immediate (some v2),
               .immediate (some v3)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  exact hWf.2 sInit rfl sInit .unsupported (OpenReaches.refl sInit) (by
    unfold OpenStep OpenStepOnFrames OpenStepOnBodyOpt OpenStepOnBlockOpt
      OpenStepOnStmtEnd OpenStepOnTerm AssumeGuaranteeTraitCall
    rfl)

/-- Reachable state invariant for `generic_id<T>(x: T) -> T`. -/
def genericIdInv (v1 : Val) (s : OpenState) : Prop :=
  (s.frames =
      [{ defId := 0
       , blockIdx := 0
       , stmtIdx := 0
       , locals := [.immediate none, .immediate (some v1)]
       , retDst := none }] ∧
    s.callerMem = ⟨[]⟩) ∨
  (s.frames =
      [{ defId := 0
       , blockIdx := 0
       , stmtIdx := 1
       , locals := [.immediate (some v1), .immediate (some v1)]
       , retDst := none }] ∧
    s.callerMem = ⟨[]⟩)

private theorem genericId_step_preserves (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 : Val)
    (hChk : checkOpenVal genericIdProgram
      { emptyOpenExecEnv with
        typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
      v1 (.param 0) = true)
    (s₁ s₂ : OpenState)
    (hInv : genericIdInv v1 s₁)
    (hStep :
      OpenStep genericIdProgram
        { emptyOpenExecEnv with
          typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        genericIdBody.sig.whereClauses s₁ (.step s₂)) :
    genericIdInv v1 s₂ := by
  let env' : OpenExecEnv :=
    { emptyOpenExecEnv with
      typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s₁ with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          change StepResult.step s₂ = openEvalDetStep genericIdProgram env' _ at hStep
          have hDet : openEvalDetStep genericIdProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 0, stmtIdx := 0
                   , locals := [.immediate none, .immediate (some v1)]
                   , retDst := none }]
              , callerMem := ⟨[]⟩
              , mem := mem } =
          .step
            { frames :=
                [{ defId := 0, blockIdx := 0, stmtIdx := 1
                 , locals := [.immediate (some v1), .immediate (some v1)]
                 , retDst := none }]
            , callerMem := ⟨[]⟩
            , mem := mem } := by
            unfold openEvalDetStep openEvalDetStepAux
            rw [show OpenProgram.toDay1? genericIdProgram = none from rfl]
            have hOp : evalOpenOperand genericIdProgram env' genericIdBody
                { defId := 0, blockIdx := 0, stmtIdx := 0
                , locals := [.immediate none, .immediate (some v1)]
                , retDst := none }
                (.copy ⟨1, []⟩) =
                .ok (v1, .param 0,
                  { defId := 0, blockIdx := 0, stmtIdx := 0
                  , locals := [.immediate none, .immediate (some v1)]
                  , retDst := none }) := by
              unfold evalOpenOperand
              dsimp only [genericIdProgram, genericIdBody, openListGet?,
                Trusted.MirSemantics.getElem?, List.isEmpty]
              rfl
            have hWr : writeOpenPlace genericIdProgram env' genericIdBody
                { defId := 0, blockIdx := 0, stmtIdx := 0
                , locals := [.immediate none, .immediate (some v1)]
                , retDst := none }
                ⟨0, []⟩ v1 =
                .ok
                  { defId := 0, blockIdx := 0, stmtIdx := 0
                  , locals := [.immediate (some v1), .immediate (some v1)]
                  , retDst := none } := by
              unfold writeOpenPlace
              dsimp only [genericIdBody, openListGet?,
                Trusted.MirSemantics.getElem?, setElem?, List.isEmpty]
              simp only [Bool.not_true, canary_if_false]
              rw [hChk]
              simp only [Bool.not_true, canary_if_false]
            dsimp only
            rw [show openListGet? genericIdProgram.bodies 0 = some genericIdBody
              from rfl]
            dsimp only
            rw [show openListGet? genericIdBody.basicBlocks 0 =
                some
                  { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
                  , terminator := .return_ } from rfl]
            dsimp only [openListGet?, Trusted.MirSemantics.getElem?, List.length,
              List.isEmpty, Nat.beq]
            simp only [Bool.not_true, canary_if_false]
            rw [hOp]
            dsimp only
            rw [show openListGet? genericIdBody.locals 0 = some (.param 0) from rfl]
            dsimp only
            rw [show OpenMirTy.beq
                (normalizeOpenTy genericIdProgram.traitRegistry normFuel (.param 0))
                (normalizeOpenTy genericIdProgram.traitRegistry normFuel (.param 0)) =
                true from rfl]
            simp only [Bool.not_true, canary_if_false]
            rw [hWr]
          rw [hDet] at hStep
          have hS2 := StepResult.step.inj hStep
          exact .inr ⟨hS2 ▸ rfl, hS2 ▸ rfl⟩
  | inr h1 =>
      let ⟨hF, hCm⟩ := h1
      cases s₁ with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          change StepResult.step s₂ = openEvalDetStep genericIdProgram env' _ at hStep
          have hDet : openEvalDetStep genericIdProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 0, stmtIdx := 1
                   , locals := [.immediate (some v1), .immediate (some v1)]
                   , retDst := none }]
              , callerMem := ⟨[]⟩
              , mem := mem } =
              .done (.returned ⟨v1, ⟨[]⟩⟩) := by
            unfold openEvalDetStep openEvalDetStepAux OpenProgram.toDay1?
            rfl
          rw [hDet] at hStep
          exact canary_done_ne_step hStep.symm

private theorem genericId_inv_progress (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 : Val) (s : OpenState)
    (hInv : genericIdInv v1 s) :
    ∃ res : StepResult OpenState TerminalOut,
      OpenStep genericIdProgram
        { emptyOpenExecEnv with
          typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        genericIdBody.sig.whereClauses s res := by
  let env' : OpenExecEnv :=
    { emptyOpenExecEnv with
      typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          exact ⟨openEvalDetStep genericIdProgram env' _, rfl⟩
  | inr h1 =>
      let ⟨hF, hCm⟩ := h1
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          exact ⟨openEvalDetStep genericIdProgram env' _, rfl⟩

private theorem genericId_inv_no_fault (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 : Val)
    (hChk : checkOpenVal genericIdProgram
      { emptyOpenExecEnv with
        typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
      v1 (.param 0) = true)
    (s : OpenState) (k : FaultKind)
    (hInv : genericIdInv v1 s)
    (hFault :
      OpenStep genericIdProgram
        { emptyOpenExecEnv with
          typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        genericIdBody.sig.whereClauses s (.fault k)) :
    False := by
  let env' : OpenExecEnv :=
    { emptyOpenExecEnv with
      typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  cases hInv with
  | inl h0 =>
      let ⟨hF, hCm⟩ := h0
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          change StepResult.fault k = openEvalDetStep genericIdProgram env' _ at hFault
          have hDet : openEvalDetStep genericIdProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 0, stmtIdx := 0
                   , locals := [.immediate none, .immediate (some v1)]
                   , retDst := none }]
              , callerMem := ⟨[]⟩
              , mem := mem } =
          .step
            { frames :=
                [{ defId := 0, blockIdx := 0, stmtIdx := 1
                 , locals := [.immediate (some v1), .immediate (some v1)]
                 , retDst := none }]
            , callerMem := ⟨[]⟩
            , mem := mem } := by
            unfold openEvalDetStep openEvalDetStepAux
            rw [show OpenProgram.toDay1? genericIdProgram = none from rfl]
            have hOp : evalOpenOperand genericIdProgram env' genericIdBody
                { defId := 0, blockIdx := 0, stmtIdx := 0
                , locals := [.immediate none, .immediate (some v1)]
                , retDst := none }
                (.copy ⟨1, []⟩) =
                .ok (v1, .param 0,
                  { defId := 0, blockIdx := 0, stmtIdx := 0
                  , locals := [.immediate none, .immediate (some v1)]
                  , retDst := none }) := by
              unfold evalOpenOperand
              dsimp only [genericIdProgram, genericIdBody, openListGet?,
                Trusted.MirSemantics.getElem?, List.isEmpty]
              rfl
            have hWr : writeOpenPlace genericIdProgram env' genericIdBody
                { defId := 0, blockIdx := 0, stmtIdx := 0
                , locals := [.immediate none, .immediate (some v1)]
                , retDst := none }
                ⟨0, []⟩ v1 =
                .ok
                  { defId := 0, blockIdx := 0, stmtIdx := 0
                  , locals := [.immediate (some v1), .immediate (some v1)]
                  , retDst := none } := by
              unfold writeOpenPlace
              dsimp only [genericIdBody, openListGet?,
                Trusted.MirSemantics.getElem?, setElem?, List.isEmpty]
              simp only [Bool.not_true, canary_if_false]
              rw [hChk]
              simp only [Bool.not_true, canary_if_false]
            dsimp only
            rw [show openListGet? genericIdProgram.bodies 0 = some genericIdBody
              from rfl]
            dsimp only
            rw [show openListGet? genericIdBody.basicBlocks 0 =
                some
                  { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
                  , terminator := .return_ } from rfl]
            dsimp only [openListGet?, Trusted.MirSemantics.getElem?, List.length,
              List.isEmpty, Nat.beq]
            simp only [Bool.not_true, canary_if_false]
            rw [hOp]
            dsimp only
            rw [show openListGet? genericIdBody.locals 0 = some (.param 0) from rfl]
            dsimp only
            rw [show OpenMirTy.beq
                (normalizeOpenTy genericIdProgram.traitRegistry normFuel (.param 0))
                (normalizeOpenTy genericIdProgram.traitRegistry normFuel (.param 0)) =
                true from rfl]
            simp only [Bool.not_true, canary_if_false]
            rw [hWr]
          rw [hDet] at hFault
          exact canary_step_ne_fault hFault.symm
  | inr h1 =>
      let ⟨hF, hCm⟩ := h1
      cases s with
      | mk frames callerMem mem =>
          dsimp only at hF hCm
          subst hF hCm
          change StepResult.fault k = openEvalDetStep genericIdProgram env' _ at hFault
          have hDet : openEvalDetStep genericIdProgram env'
              { frames :=
                  [{ defId := 0, blockIdx := 0, stmtIdx := 1
                   , locals := [.immediate (some v1), .immediate (some v1)]
                   , retDst := none }]
              , callerMem := ⟨[]⟩
              , mem := mem } =
              .done (.returned ⟨v1, ⟨[]⟩⟩) := by
            unfold openEvalDetStep openEvalDetStepAux OpenProgram.toDay1?
            rfl
          rw [hDet] at hFault
          exact canary_done_ne_fault hFault.symm

private theorem genericId_reaches_inv (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (v1 : Val)
    (hChk : checkOpenVal genericIdProgram
      { emptyOpenExecEnv with
        typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
      v1 (.param 0) = true) :
    ∀ s₀ s : OpenState,
      OpenReaches genericIdProgram
        { emptyOpenExecEnv with
          typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
            [sp0] paramInvs assocSpecs }
        genericIdBody.sig.whereClauses s₀ s →
      genericIdInv v1 s₀ →
      genericIdInv v1 s
  | _, _, .refl _, h0 => h0
  | s₀, s, .step hStep hRest, h0 =>
      genericId_reaches_inv sp0 paramInvs assocSpecs v1 hChk _ s hRest
        (genericId_step_preserves sp0 paramInvs assocSpecs v1 hChk s₀ _ h0 hStep)

private theorem openInitState_genericId (env' : OpenExecEnv) (v1 : Val)
    (hCheck :
      checkOpenArgsMatch genericIdProgram env' [v1] [.param 0] = true) :
    openInitState genericIdProgram env' { args := [v1] } =
      .ok
        { frames :=
            [{ defId := 0
             , blockIdx := 0
             , stmtIdx := 0
             , locals := [.immediate none, .immediate (some v1)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := MemoryState.empty } := by
  unfold openInitState openInitStateAux
  rw [show OpenProgram.toDay1? genericIdProgram = none from rfl]
  dsimp only
  rw [canary_ite_false]
  rw [show openListGet? genericIdProgram.bodies genericIdProgram.entryDefId =
      some genericIdBody from rfl]
  dsimp only
  rw [canary_ite_false]
  unfold initOpenLocals
  dsimp only
  rw [show (genericIdBody.locals.drop 1).take genericIdBody.argumentCount =
      [.param 0] from rfl]
  rw [hCheck]
  rw [canary_ite_false]
  rw [show initOpenLocalsBuild genericIdProgram genericIdBody 0
      genericIdBody.locals [v1] =
      some [.immediate none, .immediate (some v1)] from rfl]
  rfl
  · rfl
  · rfl
  · rfl

private theorem genericId_single_inst (sp0 : TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec)
    (hWf0 : WellFormedTypeLayoutSpec sp0)
    (hSized : sp0.isSized = true) :
    let env' : OpenExecEnv :=
      { emptyOpenExecEnv with
        typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
          [sp0] paramInvs assocSpecs }
    OpenBodyStaticAdmitted genericIdProgram env' genericIdBody ∧
    ∀ args : List Val,
      ValidOpenEntryArgs genericIdProgram env' genericIdBody args →
      (genericIdBody.isUnsafe = true → True) →
      OpenWellFormed (entryOpenProgForBody genericIdProgram 0) env'
        genericIdBody.sig.whereClauses { args := args } := by
  let env' : OpenExecEnv :=
    { emptyOpenExecEnv with
      typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
        [sp0] paramInvs assocSpecs }
  have hAdmitted :
      OpenBodyStaticAdmitted genericIdProgram env' genericIdBody :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨⟨sp0, rfl, rfl, hWf0, hSized⟩, ⟨sp0, rfl, rfl, hWf0, hSized⟩, True.intro⟩⟩
  refine ⟨hAdmitted, fun args hArgs _ => ?_⟩
  let ⟨v1, hArgsEq, hV1⟩ :=
    checkOpenArgsMatch_one_shape genericIdProgram env' (.param 0) args hArgs.1
  subst hArgsEq
  let sInit : OpenState :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals := [.immediate none, .immediate (some v1)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  have hCheck : checkOpenArgsMatch genericIdProgram env' [v1] [.param 0] =
      true :=
    bool_and_eq_true hV1 rfl
  have hInit := openInitState_genericId env' v1 hCheck
  refine ⟨⟨sInit, hInit, fun s hReach => ?_⟩, fun s₀ hS0 s k hReach hFault => ?_⟩
  · have hInv := genericId_reaches_inv sp0 paramInvs assocSpecs v1 hV1 sInit s
      hReach (Or.inl ⟨rfl, rfl⟩)
    exact genericId_inv_progress sp0 paramInvs assocSpecs v1 s hInv
  · have hEqS0 := canary_except_ok_inj (hInit.symm.trans hS0)
    have hInv := genericId_reaches_inv sp0 paramInvs assocSpecs v1 hV1 s₀ s
      hReach (hEqS0 ▸ Or.inl ⟨rfl, rfl⟩)
    exact genericId_inv_no_fault sp0 paramInvs assocSpecs v1 hV1 s k hInv hFault

/-- Canary 5 (`generic_id<T>(x: T) -> T`): kernel-checked parametric
fault-freedom for a Day-1-erasable generic identity function. -/
theorem canary_generic_id_parametric_verified :
    ParametricBodyVerified genericIdProgram emptyOpenExecEnv 0 genericIdBody
      (fun _ _ => True) := by
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun paramSpecs paramInvs assocSpecs hLen hWf _ hWhere => ?_⟩
  cases paramSpecs with
  | nil => exact canary_nat_zero_ne_succ hLen
  | cons sp0 rest =>
      cases rest with
      | cons _ _ => exact canary_nat_succ_ne_zero (Nat.succ.inj hLen)
      | nil =>
          let ⟨spS, hEvS, _, hSized⟩ := hWhere.1
          cases hEvS
          exact genericId_single_inst sp0 paramInvs assocSpecs hWf.1 hSized

/-- Concrete Open-Instantiation Canary: instantiating `generic_id<T>` at `bool`
via `ClosedOpenInstantiationTransfer` yields `OpenWellFormed`. -/
theorem canary_open_inst_generic_id_bool :
    ∃ paramSpecs : List TypeLayoutSpec,
      ∃ paramInvs : List (List AllocByte → Prop),
      let env' : OpenExecEnv :=
        { emptyOpenExecEnv with
          typeSpecs := substTypeSpecEnv emptyOpenExecEnv.typeSpecs
            paramSpecs paramInvs
            (instAssocSpecs genericIdProgram.traitRegistry
              emptyOpenExecEnv.typeSpecs [.bool]) }
      paramSpecs.length = genericIdBody.sig.tyParamCount ∧
      AllParamSpecsWf paramSpecs ∧
      AllParamInvsWf paramSpecs paramInvs ∧
      AllWhereParamsSem genericIdProgram env' genericIdBody.sig.whereClauses ∧
      OpenBodyStaticAdmitted genericIdProgram env' genericIdBody ∧
      ∀ args : List Val,
        ValidOpenEntryArgs genericIdProgram env' genericIdBody args →
        (genericIdBody.isUnsafe = true → True) →
        OpenWellFormed (entryOpenProgForBody genericIdProgram 0) env'
          genericIdBody.sig.whereClauses { args := args } := by
  have hWf : AllSubstTypesWellFormed genericIdProgram emptyOpenExecEnv [.bool] := by
    intro ty hMem
    cases hMem with
    | head =>
        exact ⟨rfl, rfl, boolTypeLayoutSpec, rfl, wellFormed_boolTypeLayoutSpec⟩
    | tail _ h => cases h
  have hWhere : AllWhereDischarged genericIdProgram emptyOpenExecEnv [.bool]
      genericIdBody.sig.whereClauses := by
    intro wc hMem
    cases hMem with
    | head =>
        exact ⟨rfl, boolTypeLayoutSpec, rfl, wellFormed_boolTypeLayoutSpec, rfl⟩
    | tail _ h => cases h
  exact ClosedOpenInstantiationTransfer genericIdProgram emptyOpenExecEnv
    0 genericIdBody [.bool] (fun _ _ => True)
    canary_generic_id_parametric_verified rfl hWf hWhere rfl

/-- Concrete Erasure Canary 1: instantiating `generic_id<T>` at `bool` via
`ClosedInstantiationTransfer` yields genuine Day-1 `BodyVerified` without
caller-supplied transfer axioms. -/
theorem canary_day1_erasure_generic_id_bool :
    BodyVerified
      (eraseOpenProgram [.bool] genericIdProgram) 0
      (eraseOpenBody [] [.bool] genericIdBody)
      (fun _ => True) := by
  have hWf : AllSubstTypesWellFormed genericIdProgram emptyOpenExecEnv [.bool] := by
    intro ty hMem
    cases hMem with
    | head =>
        exact ⟨rfl, rfl, boolTypeLayoutSpec, rfl, wellFormed_boolTypeLayoutSpec⟩
    | tail _ h => cases h
  have hWhere : AllWhereDischarged genericIdProgram emptyOpenExecEnv [.bool]
      genericIdBody.sig.whereClauses := by
    intro wc hMem
    cases hMem with
    | head =>
        exact ⟨rfl, boolTypeLayoutSpec, rfl, wellFormed_boolTypeLayoutSpec, rfl⟩
    | tail _ h => cases h
  exact ClosedInstantiationTransfer genericIdProgram emptyOpenExecEnv 0
    genericIdBody [.bool] (fun _ _ => True) (fun _ => True)
    canary_generic_id_parametric_verified rfl hWf hWhere rfl rfl rfl
    rfl rfl (fun h => by cases h)

/-- Concrete Erasure Canary 2: instantiating `generic_id<T>` at `u64` via
`ClosedInstantiationTransfer` yields genuine Day-1 `BodyVerified` without
caller-supplied transfer axioms. -/
theorem canary_day1_erasure_generic_id_u64 :
    BodyVerified
      (eraseOpenProgram [.int .i64 false] genericIdProgram) 0
      (eraseOpenBody [] [.int .i64 false] genericIdBody)
      (fun _ => True) := by
  have hWf : AllSubstTypesWellFormed genericIdProgram emptyOpenExecEnv
      [.int .i64 false] := by
    intro ty hMem
    cases hMem with
    | head =>
        exact ⟨rfl, rfl, intTypeLayoutSpec .i64, rfl,
          wellFormed_intTypeLayoutSpec .i64⟩
    | tail _ h => cases h
  have hWhere : AllWhereDischarged genericIdProgram emptyOpenExecEnv
      [.int .i64 false] genericIdBody.sig.whereClauses := by
    intro wc hMem
    cases hMem with
    | head =>
        exact ⟨rfl, intTypeLayoutSpec .i64, rfl,
          wellFormed_intTypeLayoutSpec .i64, rfl⟩
    | tail _ h => cases h
  exact ClosedInstantiationTransfer genericIdProgram emptyOpenExecEnv 0
    genericIdBody [.int .i64 false] (fun _ _ => True) (fun _ => True)
    canary_generic_id_parametric_verified rfl hWf hWhere rfl rfl rfl
    rfl rfl (fun h => by cases h)

/-- Companion witness for Negative Canary 6: `i64` and `u64` evaluate to the
same well-formed `TypeLayoutSpec` (`intTypeLayoutSpec .i64`), confirming that
normalized `OpenMirTy.beq`—not layout mismatch—is what rejects `.typeEq`. -/
theorem canary_i64_u64_share_typeLayoutSpec :
    ∃ sp : TypeLayoutSpec,
      evalOpenTySpec genericIdProgram.traitRegistry normFuel
        emptyOpenExecEnv.typeSpecs (.int .i64 true) = some sp ∧
      evalOpenTySpec genericIdProgram.traitRegistry normFuel
        emptyOpenExecEnv.typeSpecs (.int .i64 false) = some sp ∧
      WellFormedTypeLayoutSpec sp :=
  ⟨intTypeLayoutSpec .i64, rfl, rfl, wellFormed_intTypeLayoutSpec .i64⟩

/-- Negative Canary 6: `WhereClauseSem` rejects `.typeEq` between distinct Rust
types that share a `TypeLayoutSpec` (`i64` vs. `u64`). -/
theorem canary_typeEq_rejects_distinct_same_layout :
    ¬ WhereClauseSem genericIdProgram emptyOpenExecEnv
        (.typeEq (.int .i64 true) (.int .i64 false)) := by
  intro hSem
  exact canary_bool_false_ne_true hSem.2.1

/-- Malformed 32-bit `OpenProgram` carrying an unsatisfiable trait bound so
`AllWhereParamsSem` is vacuous under `emptyOpenExecEnv`. -/
noncomputable def malformedUnsatWhereBody : OpenBody :=
  { genericIdBody with
    sig :=
      { genericIdBody.sig with
        whereClauses := [.traitBound (.param 0) 999 []] } }

/-- Program wrapper with invalid `pointerWidthBits = 32` for
`malformedUnsatWhereBody`. -/
noncomputable def malformedUnsatWhereProgram : OpenProgram :=
  { bodies := [malformedUnsatWhereBody]
  , traitRegistry := []
  , entryDefId := 0
  , pointerWidthBits := 32
  , mirProfileVersion := 1
  , scope := .unit }

/-- Negative Canary 7: hoisting `OpenBodyStructureValid` ensures a malformed
body (`pointerWidthBits = 32`) is rejected by `ParametricBodyVerified` even when
its `whereClauses` are unsatisfiable. -/
theorem canary_malformed_body_unsat_where_rejected :
    ¬ ParametricBodyVerified malformedUnsatWhereProgram emptyOpenExecEnv 0
        malformedUnsatWhereBody (fun _ _ => True) := by
  intro hVer
  cases hVer.2.2.1.1

/-- Minimal `unsafe` generic body (`unsafe fn unsafe_noop<T>()`) whose safety
precondition inspects `env'.typeSpecs.paramSpecs`. -/
noncomputable def unsafeNoopBody : OpenBody :=
  { sig :=
      { tyParamCount := 1
      , argTys := []
      , retTy := .unit
      , whereClauses := [.isSized (.param 0)] }
  , argumentCount := 0
  , locals := [.unit]
  , basicBlocks :=
      [{ statements := []
       , terminator := .return_
       , cleanup := false }]
  , isUnsafe := true
  , identity := "canary::unsafe_noop" }

/-- Program pairing `unsafeNoopBody` with an uncalled open `.traitCall` sibling
body (`missingBoundBody`), exercising both `OpenExecEnv`-dependent `safetyPre`
and sibling-body independence in `OpenInstantiationErasureClaim`. -/
noncomputable def unsafeNoopProgram : OpenProgram :=
  { bodies := [unsafeNoopBody, missingBoundBody]
  , traitRegistry := []
  , entryDefId := 0
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Parametric verification of `unsafeNoopBody` with an `OpenExecEnv`-dependent
safety precondition (`env'.typeSpecs.paramSpecs.length = 1`, which is false on
`emptyOpenExecEnv`). -/
theorem canary_unsafe_noop_parametric_verified :
    ParametricBodyVerified unsafeNoopProgram emptyOpenExecEnv 0
      unsafeNoopBody
      (fun env' _ => env'.typeSpecs.paramSpecs.length = 1) := by
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun paramSpecs paramInvs assocSpecs hLen _ _ _ => ?_⟩
  cases paramSpecs with
  | nil => exact canary_nat_zero_ne_succ hLen
  | cons sp0 rest =>
      cases rest with
      | cons _ _ => exact canary_nat_succ_ne_zero (Nat.succ.inj hLen)
      | nil =>
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            ⟨⟨unitTypeLayoutSpec, rfl, rfl, wellFormed_unitTypeLayoutSpec, rfl⟩,
              True.intro⟩⟩,
            fun args hValid _ => ?_⟩
          cases args with
          | cons _ _ => exact canary_bool_false_ne_true hValid.1
          | nil =>
              let sInit : OpenState :=
                { frames :=
                    [{ defId := 0
                     , blockIdx := 0
                     , stmtIdx := 0
                     , locals := [.immediate (some .unit)]
                     , retDst := none }]
                , callerMem := ⟨[]⟩
                , mem := MemoryState.empty }
              refine ⟨⟨sInit, rfl, fun s hReach => ?_⟩,
                fun s₀ hS0 s k hReach hFault => ?_⟩
              · cases hReach with
                | refl => exact ⟨.done (.returned ⟨.unit, ⟨[]⟩⟩), rfl⟩
                | step hStep _ => cases hStep
              · have hEq := canary_except_ok_inj hS0
                subst hEq
                cases hReach with
                | refl => cases hFault
                | step hStep _ => cases hStep

/-- Concrete Erasure Canary 3: instantiating `unsafeNoopBody` at `u64` via
`ClosedInstantiationTransfer` discharges an `OpenExecEnv`-dependent `safetyPre`
at the `σ`-instantiated environment even when `prog.bodies` contains an uncalled
non-Day-1-erasable sibling body. -/
theorem canary_day1_erasure_unsafe_noop_u64 :
    BodyVerified
      (eraseOpenProgram [.int .i64 false] unsafeNoopProgram) 0
      (eraseOpenBody [] [.int .i64 false] unsafeNoopBody)
      (fun _ => True) := by
  have hWf : AllSubstTypesWellFormed unsafeNoopProgram emptyOpenExecEnv
      [.int .i64 false] := by
    intro ty hMem
    cases hMem with
    | head =>
        exact ⟨rfl, rfl, intTypeLayoutSpec .i64, rfl,
          wellFormed_intTypeLayoutSpec .i64⟩
    | tail _ h => cases h
  have hWhere : AllWhereDischarged unsafeNoopProgram emptyOpenExecEnv
      [.int .i64 false] unsafeNoopBody.sig.whereClauses := by
    intro wc hMem
    cases hMem with
    | head =>
        exact ⟨rfl, intTypeLayoutSpec .i64, rfl,
          wellFormed_intTypeLayoutSpec .i64, rfl⟩
    | tail _ h => cases h
  exact ClosedInstantiationTransfer unsafeNoopProgram emptyOpenExecEnv 0
    unsafeNoopBody [.int .i64 false]
    (fun env' _ => env'.typeSpecs.paramSpecs.length = 1) (fun _ => True)
    canary_unsafe_noop_parametric_verified rfl hWf hWhere rfl rfl rfl
    rfl rfl (fun _ _ paramSpecs hEv _ _ => by cases hEv; rfl)

/-- Negative Canary 9a: closed `.tuple []` is rejected by `evalOpenTySpec`
(Rust `()` uses `OpenMirTy.unit`). -/
theorem canary_tuple_nil_not_admitted :
    evalOpenTySpec genericIdProgram.traitRegistry normFuel
      emptyOpenExecEnv.typeSpecs (.tuple []) = none :=
  rfl

/-- Canary 9b: `checkOpenVal` guards `checkVal` on `isSupportedScalarOrUnitTy`
so closed reference types evaluate against `pointerTypeLayoutSpec` rather than
vacuously returning `false` on all values. -/
theorem canary_checkOpenVal_closed_ref_inhabited :
    checkOpenVal verifyAlignedProgram canaryExecEnv
      (.ptr ⟨some 1, (0 : UInt64), .isize⟩)
      (.ref .shared (.int .i64 false)) = true :=
  rfl

/-- Closed-reference `&self` method body for a candidate
`impl ByteSource for u64`. -/
noncomputable def closedRefSelfImplBody : OpenBody :=
  { sig :=
      { tyParamCount := 0
      , argTys := [.ref .shared (.int .i64 false), .int .i64 false]
      , retTy := .int .i64 false
      , whereClauses := [] }
  , argumentCount := 2
  , locals :=
      [.int .i64 false, .ref .shared (.int .i64 false), .int .i64 false]
  , basicBlocks :=
      [{ statements :=
           [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
       , terminator := .return_
       , cleanup := false }]
  , isUnsafe := false
  , identity := "canary::u64_closed_ref_self_read_aligned" }

/-- Program pairing `verifyAlignedBody` with `closedRefSelfImplBody` registered
as `impl ByteSource for u64`. -/
noncomputable def closedRefSelfProgram : OpenProgram :=
  { bodies := [verifyAlignedBody, closedRefSelfImplBody]
  , entryDefId := 0
  , traitRegistry :=
      [ ( ⟨.int .i64 false, traitByteSourceId, []⟩
        , { implTyParamCount := 0
          , whereClauses := []
          , assocTypes := [{ assocIdx := 0, rhsTy := .int .i64 false }]
          , methodDefIds := [(0, 1)] } ) ]
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Negative Canary 9c: closed Day-1-convertible `&self` impls
(`impl ByteSource for u64`) are refused by `OpenBodyStaticAdmitted`,
`SatisfiesTraitSem`, and `AllWhereDischarged` (blocking closed-instantiation
transfer). -/
theorem canary_closed_ref_self_impl_refused :
    ¬ OpenBodyStaticAdmitted closedRefSelfProgram canaryExecEnv
        closedRefSelfImplBody ∧
    ¬ SatisfiesTraitSem closedRefSelfProgram canaryExecEnv (.int .i64 false)
        traitByteSourceId [] byteSourceContract ∧
    ¬ AllWhereDischarged closedRefSelfProgram canaryExecEnv [.int .i64 false]
        verifyAlignedBody.sig.whereClauses := by
  have hNotAdm :
      ∀ envC : OpenExecEnv,
        ¬ OpenBodyStaticAdmitted closedRefSelfProgram envC
            closedRefSelfImplBody := by
    intro envC hAdm
    let ⟨_, hSupp, _⟩ := hAdm.2.2.2.2.2.2.2.2.2.2.1
    exact canary_bool_false_ne_true hSupp
  have hNotSat :
      ∀ envC : OpenExecEnv,
        envC.traitContracts traitByteSourceId = some byteSourceContract →
        ¬ SatisfiesTraitSem closedRefSelfProgram envC (.int .i64 false)
            traitByteSourceId [] byteSourceContract := by
    intro envC _ hSat
    unfold SatisfiesTraitSem at hSat
    rw [traitCheckDepth] at hSat
    unfold SatisfiesTraitSemDepth at hSat
    let ⟨_, _, _, _, _, _, _, binding, hBind, _, _, _, _, _, _, _, _, _, _,
      hMethods⟩ := hSat
    cases hBind
    let ⟨calleeId, calleeBody, hLook, hGet, _, _, _, hCalAdm, _⟩ :=
      hMethods byteSourceMethodSpec (List.Mem.head [])
    cases hLook
    cases hGet
    exact hNotAdm _ hCalAdm
  refine ⟨hNotAdm canaryExecEnv, hNotSat canaryExecEnv rfl, ?_⟩
  intro hDisch
  have hTr :=
    hDisch (.traitBound (.param 0) traitByteSourceId []) (List.Mem.head _)
  dsimp only [WhereClause.substAndNormalize, WhereClauseSem] at hTr
  let ⟨contract, hCon, hSat⟩ := hTr
  cases hCon
  exact hNotSat _ rfl hSat

/-- Negative Canary 9d: a body taking a closed Day-1 reference parameter
(`&u64`) is rejected unconditionally by `ParametricBodyVerified` via
`OpenBodyStructureValid`. -/
theorem canary_closed_ref_body_not_parametric_verified :
    ¬ ParametricBodyVerified closedRefSelfProgram canaryExecEnv 1
        closedRefSelfImplBody (fun _ _ => True) := by
  intro hVer
  exact canary_bool_false_ne_true hVer.2.2.1.2.2.2.2.2.2.2.2.2

/-- Negative Canary 9e: closed Day-1 reference substitutions (`σ = [&u64]`) are
rejected by `AllSubstTypesWellFormed`. -/
theorem canary_closed_ref_subst_not_well_formed :
    ¬ AllSubstTypesWellFormed genericIdProgram emptyOpenExecEnv
        [.ref .shared (.int .i64 false)] := by
  intro hWf
  exact canary_bool_false_ne_true
    (hWf (.ref .shared (.int .i64 false)) (List.Mem.head [])).2.1

/-- Non-trivial `u64` scalar witness (`42_u64`) for anti-vacuity canaries. -/
noncomputable def canaryVal42U64 : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 42⟩

/-- Anti-Vacuity Canary 10a: `genericIdBody` instantiated at `u64` in
`OpenSemantics` is admitted (`OpenBodyStaticAdmitted`), inhabited by the
non-trivial entry witness `[42_u64]` (`ValidOpenEntryArgs`), and executes to
`.returned ⟨42_u64, ⟨[]⟩⟩` (`OpenBehavior`). -/
theorem canary_generic_id_u64_open_nonvacuous :
    let env' := instOpenExecEnv genericIdProgram emptyOpenExecEnv
      [.int .i64 false] [intTypeLayoutSpec .i64]
    OpenBodyStaticAdmitted genericIdProgram env' genericIdBody ∧
    ValidOpenEntryArgs genericIdProgram env' genericIdBody [canaryVal42U64] ∧
    OpenBehavior (entryOpenProgForBody genericIdProgram 0) env'
      genericIdBody.sig.whereClauses { args := [canaryVal42U64] }
      (.returned ⟨canaryVal42U64, ⟨[]⟩⟩) := by
  let env' := instOpenExecEnv genericIdProgram emptyOpenExecEnv
    [.int .i64 false] [intTypeLayoutSpec .i64]
  have hWf64 := wellFormed_intTypeLayoutSpec .i64
  have hAdm : OpenBodyStaticAdmitted genericIdProgram env' genericIdBody :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨⟨intTypeLayoutSpec .i64, rfl, rfl, hWf64, rfl⟩,
       ⟨intTypeLayoutSpec .i64, rfl, rfl, hWf64, rfl⟩, True.intro⟩⟩
  have hValid :
      ValidOpenEntryArgs genericIdProgram env' genericIdBody [canaryVal42U64] :=
    ⟨rfl, True.intro, True.intro⟩
  let s0 : OpenState :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals := [.immediate none, .immediate (some canaryVal42U64)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  let s1 : OpenState :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 1
         , locals :=
             [.immediate (some canaryVal42U64),
              .immediate (some canaryVal42U64)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  have hStep0 :
      OpenStep (entryOpenProgForBody genericIdProgram 0) env'
        genericIdBody.sig.whereClauses s0 (.step s1) := rfl
  have hStep1 :
      OpenStep (entryOpenProgForBody genericIdProgram 0) env'
        genericIdBody.sig.whereClauses s1
        (.done (.returned ⟨canaryVal42U64, ⟨[]⟩⟩)) := rfl
  exact ⟨hAdm, hValid, ⟨s0, s1, rfl, .step hStep0 (.refl s1), hStep1⟩⟩

/-- Anti-Vacuity Canary 10b: the Day-1 erased `generic_id<u64>` body (proven
`BodyVerified` by `canary_day1_erasure_generic_id_u64`) satisfies
`BodyStaticAdmitted = true`, admits the non-trivial entry witness `[42_u64]`
under `ValidEntryArgs`, and terminates with `.returned ⟨42_u64, ⟨[]⟩⟩` under
`Trusted.MirSemantics.Behavior`. -/
theorem canary_erased_generic_id_u64_nonvacuous :
    let erasedProg := eraseOpenProgram [.int .i64 false] genericIdProgram
    let erasedBody := eraseOpenBody [] [.int .i64 false] genericIdBody
    BodyStaticAdmitted erasedProg erasedBody = true ∧
    ValidEntryArgs erasedBody [canaryVal42U64] ∧
    Behavior (entryProgForBody erasedProg 0) { args := [canaryVal42U64] }
      (.returned ⟨canaryVal42U64, ⟨[]⟩⟩) := by
  let erasedProg := eraseOpenProgram [.int .i64 false] genericIdProgram
  let erasedBody := eraseOpenBody [] [.int .i64 false] genericIdBody
  let ds0 : State :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals := [.immediate none, .immediate (some canaryVal42U64)] }]
    , callerMem := ⟨[]⟩
    , mem := entryMemory }
  let ds1 : State :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 1
         , locals :=
             [.immediate (some canaryVal42U64),
              .immediate (some canaryVal42U64)] }]
    , callerMem := ⟨[]⟩
    , mem := entryMemory }
  have hStep0 : Step (entryProgForBody erasedProg 0) ds0 (.step ds1) :=
    ⟨0, rfl, rfl⟩
  exact ⟨rfl, rfl, ⟨ds1, .tail (.refl ds0) hStep0, 0, rfl, rfl⟩⟩

/-- Anti-Vacuity Canary 10c: `verifyAlignedBody` instantiated at `MemSlice`
(`src: &MemSlice`) is statically admitted (`OpenBodyStaticAdmitted`) and admits
the non-trivial entry witness `[.ptr ⟨some 1, 0, .isize⟩, 42_u64]`. -/
theorem canary_verify_aligned_memSlice_admitted_and_inhabited :
    let env' :=
      { canaryExecEnv with
        typeSpecs :=
          substTypeSpecEnv canaryExecEnv.typeSpecs [memSliceTypeLayoutSpec]
            [fun _ => True] canaryExecEnv.typeSpecs.assocSpecs }
    OpenBodyStaticAdmitted verifyAlignedProgram env' verifyAlignedBody ∧
    ValidOpenEntryArgs verifyAlignedProgram env' verifyAlignedBody
      [.ptr ⟨some 1, (0 : UInt64), .isize⟩, canaryVal42U64] :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨⟨intTypeLayoutSpec .i64, rfl, rfl, wellFormed_intTypeLayoutSpec .i64, rfl⟩,
     ⟨pointerTypeLayoutSpec memSliceTypeLayoutSpec true, rfl, rfl,
       wellFormed_pointerTypeLayoutSpec memSliceTypeLayoutSpec true (by decide),
       rfl⟩,
     ⟨intTypeLayoutSpec .i64, rfl, rfl, wellFormed_intTypeLayoutSpec .i64, rfl⟩,
     True.intro⟩⟩,
   ⟨rfl, True.intro, True.intro, True.intro⟩⟩

/-- Canonical trait id for a by-value-receiver scalar trait `ByValId`. -/
@[expose] noncomputable def traitByValId : TraitDefId := 2

/-- Method contract for `fn id_val(self) -> Self` (`methodIdx = 0`), requiring
the returned value to equal the single by-value `self` argument with empty
`CallerMemory`. -/
@[expose] noncomputable def byValIdMethodSpec : TraitMethodSpec :=
  { sig :=
      { methodIdx := 0
      , argTys := [.param 0]
      , retTy := .param 0
      , whereClauses := []
      , isUnsafe := false }
  , pre := fun _ _ _ _ => True
  , post := fun _ _ argVals _ out =>
      match out, argVals with
      | .returned ⟨rv, ⟨[]⟩⟩, [v] => rv = v
      | _, _ => False }

/-- Trait contract for `ByValId` (`0` type params, `0` assoc types, 1 by-value
method). -/
@[expose] noncomputable def byValIdContract : TraitContract :=
  { traitId := traitByValId
  , tyParamCount := 0
  , assocTypeCount := 0
  , methodSpecs := [byValIdMethodSpec] }

/-- Semantic environment mapping `traitByValId` (`2`) to `byValIdContract`. -/
@[expose] noncomputable def byValTraitExecEnv : OpenExecEnv :=
  { traitContracts := fun id =>
      if Nat.beq id traitByValId then some byValIdContract else none }

/-- Trait-bounded generic identity body
`fn trait_bounded_id<T: ByValId>(x: T) -> T` (`defId = 0`), Day-1-erasable at
closed scalar instantiations. -/
@[expose] noncomputable def traitBoundedIdBody : OpenBody :=
  { sig :=
      { tyParamCount := 1
      , argTys := [.param 0]
      , retTy := .param 0
      , whereClauses :=
          [ .traitBound (.param 0) traitByValId []
          , .isSized (.param 0) ] }
  , argumentCount := 1
  , locals := [.param 0, .param 0]
  , basicBlocks :=
      [{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
       , terminator := .return_
       , cleanup := false }]
  , isUnsafe := false
  , identity := "canary::trait_bounded_id" }

/-- Concrete by-value-receiver trait method body `fn id_val(self: u64) -> u64`
(`defId = 1`) implementing `ByValId` for `u64`. -/
@[expose] noncomputable def u64ByValIdImplBody : OpenBody :=
  { sig :=
      { tyParamCount := 0
      , argTys := [.int .i64 false]
      , retTy := .int .i64 false
      , whereClauses := [] }
  , argumentCount := 1
  , locals := [.int .i64 false, .int .i64 false]
  , basicBlocks :=
      [{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
       , terminator := .return_
       , cleanup := false }]
  , isUnsafe := false
  , identity := "canary::u64_by_val_id" }

/-- Program pairing `traitBoundedIdBody` (`0`) with `u64ByValIdImplBody` (`1`)
registered as `impl ByValId for u64`. -/
@[expose] noncomputable def byValTraitProgram : OpenProgram :=
  { bodies := [traitBoundedIdBody, u64ByValIdImplBody]
  , entryDefId := 0
  , traitRegistry :=
      [ ( ⟨.int .i64 false, traitByValId, []⟩
        , { implTyParamCount := 0
          , whereClauses := []
          , assocTypes := []
          , methodDefIds := [(0, 1)] } ) ]
  , pointerWidthBits := 64
  , mirProfileVersion := 1
  , scope := .unit }

/-- Reachable 2-state invariant for a 1-argument copy-and-return body `did`. -/
private def byValCopyInv (did : DefId) (v1 : Val) (s : OpenState) : Prop :=
  (s.frames =
      [{ defId := did
       , blockIdx := 0
       , stmtIdx := 0
       , locals := [.immediate none, .immediate (some v1)]
       , retDst := none }] ∧
    s.callerMem = ⟨[]⟩) ∨
  (s.frames =
      [{ defId := did
       , blockIdx := 0
       , stmtIdx := 1
       , locals := [.immediate (some v1), .immediate (some v1)]
       , retDst := none }] ∧
    s.callerMem = ⟨[]⟩)

private theorem byValCopy_det0 (prog : OpenProgram) (env : OpenExecEnv)
    (did : DefId) (ob : OpenBody) (ty : OpenMirTy) (v1 : Val)
    (mem : MemoryState)
    (hDay1 : OpenProgram.toDay1? prog = none)
    (hBody : openListGet? prog.bodies did = some ob)
    (hBb : openListGet? ob.basicBlocks 0 =
      some
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        , terminator := .return_
        , cleanup := false })
    (hL0 : openListGet? ob.locals 0 = some ty)
    (hL1 : openListGet? ob.locals 1 = some ty)
    (hBeq : OpenMirTy.beq (normalizeOpenTy prog.traitRegistry normFuel ty)
      (normalizeOpenTy prog.traitRegistry normFuel ty) = true)
    (hChk : checkOpenVal prog env v1 ty = true) :
    openEvalDetStep prog env
      { frames :=
          [{ defId := did, blockIdx := 0, stmtIdx := 0
           , locals := [.immediate none, .immediate (some v1)]
           , retDst := none }]
      , callerMem := ⟨[]⟩
      , mem := mem } =
    .step
      { frames :=
          [{ defId := did, blockIdx := 0, stmtIdx := 1
           , locals := [.immediate (some v1), .immediate (some v1)]
           , retDst := none }]
      , callerMem := ⟨[]⟩
      , mem := mem } := by
  have hOp : evalOpenOperand prog env ob
      { defId := did, blockIdx := 0, stmtIdx := 0
      , locals := [.immediate none, .immediate (some v1)]
      , retDst := none }
      (.copy ⟨1, []⟩) =
      .ok (v1, ty,
        { defId := did, blockIdx := 0, stmtIdx := 0
        , locals := [.immediate none, .immediate (some v1)]
        , retDst := none }) := by
    unfold evalOpenOperand
    dsimp only [List.isEmpty, Trusted.MirSemantics.getElem?]
    rw [hL1]
    rfl
  have hWr : writeOpenPlace prog env ob
      { defId := did, blockIdx := 0, stmtIdx := 0
      , locals := [.immediate none, .immediate (some v1)]
      , retDst := none }
      ⟨0, []⟩ v1 =
      .ok
        { defId := did, blockIdx := 0, stmtIdx := 0
        , locals := [.immediate (some v1), .immediate (some v1)]
        , retDst := none } := by
    unfold writeOpenPlace
    dsimp only [List.isEmpty]
    simp only [Bool.not_true, canary_if_false]
    rw [hL0]
    dsimp only
    rw [hChk]
    simp only [Bool.not_true, canary_if_false]
    rfl
  unfold openEvalDetStep openEvalDetStepAux
  rw [hDay1]
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [show openListGet?
      [OpenStatementKind.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))] 0 =
      some (.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))) from rfl]
  dsimp only [List.isEmpty]
  simp only [Bool.not_true, canary_if_false]
  rw [hL0]
  dsimp only
  rw [hOp]
  dsimp only
  rw [hBeq]
  simp only [Bool.not_true, canary_if_false]
  rw [hWr]

private theorem byValCopy_det1 (prog : OpenProgram) (env : OpenExecEnv)
    (did : DefId) (ob : OpenBody) (v1 : Val) (mem : MemoryState)
    (hDay1 : OpenProgram.toDay1? prog = none)
    (hBody : openListGet? prog.bodies did = some ob)
    (hBb : openListGet? ob.basicBlocks 0 =
      some
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        , terminator := .return_
        , cleanup := false }) :
    openEvalDetStep prog env
      { frames :=
          [{ defId := did, blockIdx := 0, stmtIdx := 1
           , locals := [.immediate (some v1), .immediate (some v1)]
           , retDst := none }]
      , callerMem := ⟨[]⟩
      , mem := mem } =
    .done (.returned ⟨v1, ⟨[]⟩⟩) := by
  unfold openEvalDetStep openEvalDetStepAux
  rw [hDay1]
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [show openListGet?
      [OpenStatementKind.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))] 1 =
      none from rfl]
  rfl

private theorem byValCopy_openStep_eq (prog : OpenProgram) (env : OpenExecEnv)
    (wcs : List WhereClause) (did : DefId) (ob : OpenBody)
    (s : OpenState) (res : StepResult OpenState TerminalOut)
    (stmtIdx : Nat) (locs : List LocalSlot)
    (hF : s.frames =
      [{ defId := did, blockIdx := 0, stmtIdx := stmtIdx
       , locals := locs, retDst := none }])
    (hBody : openListGet? prog.bodies did = some ob)
    (hBb : openListGet? ob.basicBlocks 0 =
      some
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        , terminator := .return_
        , cleanup := false })
    (hIdx : stmtIdx = 0 ∨ stmtIdx = 1) :
    OpenStep prog env wcs s res ↔ res = openEvalDetStep prog env s := by
  unfold OpenStep
  rw [hF]
  unfold OpenStepOnFrames
  dsimp only
  rw [hBody]
  unfold OpenStepOnBodyOpt
  dsimp only
  rw [hBb]
  cases hIdx with
  | inl h0 => subst h0; rfl
  | inr h1 => subst h1; rfl

private theorem byValCopy_reaches_inv (prog : OpenProgram) (env : OpenExecEnv)
    (wcs : List WhereClause) (did : DefId) (ob : OpenBody) (ty : OpenMirTy)
    (v1 : Val)
    (hDay1 : OpenProgram.toDay1? prog = none)
    (hBody : openListGet? prog.bodies did = some ob)
    (hBb : openListGet? ob.basicBlocks 0 =
      some
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        , terminator := .return_
        , cleanup := false })
    (hL0 : openListGet? ob.locals 0 = some ty)
    (hL1 : openListGet? ob.locals 1 = some ty)
    (hBeq : OpenMirTy.beq (normalizeOpenTy prog.traitRegistry normFuel ty)
      (normalizeOpenTy prog.traitRegistry normFuel ty) = true)
    (hChk : checkOpenVal prog env v1 ty = true) :
    ∀ s₀ s : OpenState,
      OpenReaches prog env wcs s₀ s →
      byValCopyInv did v1 s₀ →
      byValCopyInv did v1 s
  | _, _, .refl _, h0 => h0
  | s₀, s, .step (s₂ := s₂) hStep hRest, h0 =>
      have hNext : byValCopyInv did v1 s₂ := by
        cases h0 with
        | inl hS0 =>
            let ⟨hF, hCm⟩ := hS0
            cases s₀ with
            | mk frames callerMem mem =>
                dsimp only at hF hCm
                subst hF hCm
                have hEq := (byValCopy_openStep_eq prog env wcs did ob _
                  (.step s₂) 0 _ rfl hBody hBb (.inl rfl)).1 hStep
                rw [byValCopy_det0 prog env did ob ty v1 mem hDay1 hBody hBb
                  hL0 hL1 hBeq hChk] at hEq
                have hInj := StepResult.step.inj hEq
                exact .inr ⟨hInj ▸ rfl, hInj ▸ rfl⟩
        | inr hS1 =>
            let ⟨hF, hCm⟩ := hS1
            cases s₀ with
            | mk frames callerMem mem =>
                dsimp only at hF hCm
                subst hF hCm
                have hEq := (byValCopy_openStep_eq prog env wcs did ob _
                  (.step s₂) 1 _ rfl hBody hBb (.inr rfl)).1 hStep
                rw [byValCopy_det1 prog env did ob v1 mem hDay1 hBody hBb]
                  at hEq
                exact canary_done_ne_step hEq.symm
      byValCopy_reaches_inv prog env wcs did ob ty v1 hDay1 hBody hBb hL0 hL1
        hBeq hChk s₂ s hRest hNext

private theorem byValCopy_wf_and_behavior (prog : OpenProgram)
    (env : OpenExecEnv) (wcs : List WhereClause) (did : DefId) (ob : OpenBody)
    (ty : OpenMirTy) (v1 : Val)
    (hDay1 : OpenProgram.toDay1? prog = none)
    (hEntry : prog.entryDefId = did)
    (hBody : openListGet? prog.bodies did = some ob)
    (hBb : openListGet? ob.basicBlocks 0 =
      some
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
        , terminator := .return_
        , cleanup := false })
    (hL0 : openListGet? ob.locals 0 = some ty)
    (hL1 : openListGet? ob.locals 1 = some ty)
    (hBeq : OpenMirTy.beq (normalizeOpenTy prog.traitRegistry normFuel ty)
      (normalizeOpenTy prog.traitRegistry normFuel ty) = true)
    (hChk : checkOpenVal prog env v1 ty = true)
    (hInit : openInitState prog env { args := [v1] } =
      .ok
        { frames :=
            [{ defId := did
             , blockIdx := 0
             , stmtIdx := 0
             , locals := [.immediate none, .immediate (some v1)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := MemoryState.empty }) :
    OpenWellFormed prog env wcs { args := [v1] } ∧
    ∀ out : TerminalOut,
      OpenBehavior prog env wcs { args := [v1] } out →
      out = .returned ⟨v1, ⟨[]⟩⟩ := by
  let _ := hEntry
  let sInit : OpenState :=
    { frames :=
        [{ defId := did
         , blockIdx := 0
         , stmtIdx := 0
         , locals := [.immediate none, .immediate (some v1)]
         , retDst := none }]
    , callerMem := ⟨[]⟩
    , mem := MemoryState.empty }
  refine ⟨⟨⟨sInit, hInit, fun s hReach => ?_⟩,
    fun s₀ hS0 s k hReach hFault => ?_⟩, fun out hBeh => ?_⟩
  · have hInv := byValCopy_reaches_inv prog env wcs did ob ty v1 hDay1 hBody
      hBb hL0 hL1 hBeq hChk sInit s hReach (.inl ⟨rfl, rfl⟩)
    cases hInv with
    | inl h0 =>
        exact ⟨openEvalDetStep prog env s,
          (byValCopy_openStep_eq prog env wcs did ob s _ 0 _ h0.1 hBody hBb
            (.inl rfl)).2 rfl⟩
    | inr h1 =>
        exact ⟨openEvalDetStep prog env s,
          (byValCopy_openStep_eq prog env wcs did ob s _ 1 _ h1.1 hBody hBb
            (.inr rfl)).2 rfl⟩
  · have hEqS0 := canary_except_ok_inj (hInit.symm.trans hS0)
    have hInv := byValCopy_reaches_inv prog env wcs did ob ty v1 hDay1 hBody
      hBb hL0 hL1 hBeq hChk s₀ s hReach (hEqS0 ▸ .inl ⟨rfl, rfl⟩)
    cases hInv with
    | inl h0 =>
        let ⟨hF, hCm⟩ := h0
        cases s with
        | mk frames callerMem mem =>
            dsimp only at hF hCm
            subst hF hCm
            have hEq := (byValCopy_openStep_eq prog env wcs did ob _ (.fault k)
              0 _ rfl hBody hBb (.inl rfl)).1 hFault
            rw [byValCopy_det0 prog env did ob ty v1 mem hDay1 hBody hBb hL0
              hL1 hBeq hChk] at hEq
            exact canary_step_ne_fault hEq.symm
    | inr h1 =>
        let ⟨hF, hCm⟩ := h1
        cases s with
        | mk frames callerMem mem =>
            dsimp only at hF hCm
            subst hF hCm
            have hEq := (byValCopy_openStep_eq prog env wcs did ob _ (.fault k)
              1 _ rfl hBody hBb (.inr rfl)).1 hFault
            rw [byValCopy_det1 prog env did ob v1 mem hDay1 hBody hBb] at hEq
            exact canary_done_ne_fault hEq.symm
  · let ⟨s₀, s, hS0, hReach, hDone⟩ := hBeh
    have hEqS0 := canary_except_ok_inj (hInit.symm.trans hS0)
    have hInv := byValCopy_reaches_inv prog env wcs did ob ty v1 hDay1 hBody
      hBb hL0 hL1 hBeq hChk s₀ s hReach (hEqS0 ▸ .inl ⟨rfl, rfl⟩)
    cases hInv with
    | inl h0 =>
        let ⟨hF, hCm⟩ := h0
        cases s with
        | mk frames callerMem mem =>
            dsimp only at hF hCm
            subst hF hCm
            have hEq := (byValCopy_openStep_eq prog env wcs did ob _ (.done out)
              0 _ rfl hBody hBb (.inl rfl)).1 hDone
            rw [byValCopy_det0 prog env did ob ty v1 mem hDay1 hBody hBb hL0
              hL1 hBeq hChk] at hEq
            exact canary_done_ne_step hEq
    | inr h1 =>
        let ⟨hF, hCm⟩ := h1
        cases s with
        | mk frames callerMem mem =>
            dsimp only at hF hCm
            subst hF hCm
            have hEq := (byValCopy_openStep_eq prog env wcs did ob _ (.done out)
              1 _ rfl hBody hBb (.inr rfl)).1 hDone
            rw [byValCopy_det1 prog env did ob v1 mem hDay1 hBody hBb] at hEq
            exact StepResult.done.inj hEq

/-- `normalizeOpenTy` at any fuel leaves a `normalizeOpenTyStep` fixed point
unchanged. Rewriting with this avoids elaborator `whnf` of the 16-deep
`normalizeOpenTyStep` chain at `normFuel`, which re-evaluates the
call-by-name argument at every level and costs `O(2^normFuel)`. -/
private theorem canary_normalizeOpenTy_of_step_fixed (reg : TraitRegistry)
    (ty : OpenMirTy) (h : normalizeOpenTyStep reg ty = ty) :
    ∀ n, normalizeOpenTy reg n ty = ty
  | 0 => rfl
  | n + 1 => by
      unfold normalizeOpenTy
      rw [h]
      exact canary_normalizeOpenTy_of_step_fixed reg ty h n

private theorem openInitState_byValImpl (envC : OpenExecEnv) (v1 : Val)
    (hCheck :
      checkOpenArgsMatch byValTraitProgram envC [v1] [.int .i64 false] =
        true) :
    openInitState (entryOpenProgForBody byValTraitProgram 1) envC
      { args := [v1] } =
      .ok
        { frames :=
            [{ defId := 1
             , blockIdx := 0
             , stmtIdx := 0
             , locals := [.immediate none, .immediate (some v1)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := MemoryState.empty } := by
  let p1 := entryOpenProgForBody byValTraitProgram 1
  unfold openInitState openInitStateAux
  rw [show OpenProgram.toDay1? p1 = none from rfl]
  dsimp only
  rw [canary_ite_false]
  rw [show openListGet? p1.bodies p1.entryDefId = some u64ByValIdImplBody
      from rfl]
  dsimp only
  rw [canary_ite_false]
  unfold initOpenLocals
  dsimp only
  rw [show (u64ByValIdImplBody.locals.drop 1).take
      u64ByValIdImplBody.argumentCount = [.int .i64 false] from rfl]
  have hCheck' : checkOpenArgsMatch p1 envC [v1] [.int .i64 false] = true :=
    hCheck
  rw [hCheck']
  rw [canary_ite_false]
  have hSlot : openLiveUninitSlot p1 (.int .i64 false) = .immediate none := by
    unfold openLiveUninitSlot
    rw [canary_normalizeOpenTy_of_step_fixed _ _ rfl]
    rfl
  rw [show initOpenLocalsBuild p1 u64ByValIdImplBody 0
      u64ByValIdImplBody.locals [v1] =
      some [openLiveUninitSlot p1 (.int .i64 false), .immediate (some v1)]
      from rfl, hSlot]
  rfl
  · rfl
  · rfl
  · rfl

/-- Positive Canary 10d: a by-value-receiver scalar trait `impl`
(`impl ByValId for u64`) satisfies `SatisfiesTraitSem` and discharges
`AllWhereDischarged` at `σ = [u64]`, witnessing that trait-bounded
closed-instantiation transfer is inhabited for supported scalar receiver types.
-/
theorem canary_by_val_trait_impl_satisfies_sem :
    SatisfiesTraitSem byValTraitProgram byValTraitExecEnv (.int .i64 false)
      traitByValId [] byValIdContract ∧
    AllWhereDischarged byValTraitProgram byValTraitExecEnv [.int .i64 false]
      traitBoundedIdBody.sig.whereClauses := by
  have hWf64 := wellFormed_intTypeLayoutSpec .i64
  have hSat :
      SatisfiesTraitSem byValTraitProgram byValTraitExecEnv (.int .i64 false)
        traitByValId [] byValIdContract := by
    unfold SatisfiesTraitSem
    rw [traitCheckDepth]
    unfold SatisfiesTraitSemDepth
    let envClosed : OpenExecEnv :=
      { byValTraitExecEnv with
        typeSpecs :=
          { byValTraitExecEnv.typeSpecs with
            paramSpecs := [], paramInvs := [] } }
    have hAdmImpl :
        OpenBodyStaticAdmitted byValTraitProgram envClosed
          u64ByValIdImplBody :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ⟨⟨intTypeLayoutSpec .i64, rfl, rfl, hWf64, rfl⟩,
         ⟨intTypeLayoutSpec .i64, rfl, rfl, hWf64, rfl⟩, True.intro⟩⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, (fun _ h => by cases h),
      ⟨intTypeLayoutSpec .i64, rfl, hWf64, fun _ _ _ => True.intro⟩,
      { implTyParamCount := 0
      , whereClauses := []
      , assocTypes := []
      , methodDefIds := [(0, 1)] },
      rfl, rfl, (fun _ h => by cases h),
      ⟨[], rfl, True.intro, (fun _ h => by cases h),
        ⟨intTypeLayoutSpec .i64, [], rfl, rfl, fun mspec hMem => ?_⟩⟩⟩
    cases hMem with
    | tail _ h => cases h
    | head =>
        refine ⟨1, u64ByValIdImplBody, rfl, rfl, rfl, rfl, rfl, hAdmImpl,
          rfl, rfl, rfl, fun argVals hMatch _ => ?_⟩
        have hMatch' :
            checkOpenArgsMatch byValTraitProgram envClosed argVals
              [.int .i64 false] = true := hMatch
        let ⟨v1, hArgsEq, hV1⟩ :=
          checkOpenArgsMatch_one_shape byValTraitProgram envClosed
            (.int .i64 false) argVals hMatch'
        subst hArgsEq
        have hInit := openInitState_byValImpl envClosed v1 hMatch'
        have hMain := byValCopy_wf_and_behavior
          (entryOpenProgForBody byValTraitProgram 1) envClosed [] 1
          u64ByValIdImplBody (.int .i64 false) v1 rfl rfl rfl rfl rfl rfl rfl
          hV1 hInit
        refine ⟨hMain.1, fun out hBeh => ?_⟩
        have hOut := hMain.2 out hBeh
        subst hOut
        rfl
  refine ⟨hSat, ?_⟩
  intro wc hMem
  cases hMem with
  | head =>
      exact ⟨byValIdContract, rfl, hSat⟩
  | tail _ hMem2 =>
      cases hMem2 with
      | head =>
          exact ⟨rfl, intTypeLayoutSpec .i64, rfl, hWf64, rfl⟩
      | tail _ h => cases h

private theorem openInitState_traitBoundedId (env' : OpenExecEnv) (v1 : Val)
    (hCheck :
      checkOpenArgsMatch byValTraitProgram env' [v1] [.param 0] = true) :
    openInitState (entryOpenProgForBody byValTraitProgram 0) env'
      { args := [v1] } =
      .ok
        { frames :=
            [{ defId := 0
             , blockIdx := 0
             , stmtIdx := 0
             , locals := [.immediate none, .immediate (some v1)]
             , retDst := none }]
        , callerMem := ⟨[]⟩
        , mem := MemoryState.empty } := by
  let p0 := entryOpenProgForBody byValTraitProgram 0
  unfold openInitState openInitStateAux
  rw [show OpenProgram.toDay1? p0 = none from rfl]
  dsimp only
  rw [canary_ite_false]
  rw [show openListGet? p0.bodies p0.entryDefId = some traitBoundedIdBody
      from rfl]
  dsimp only
  rw [canary_ite_false]
  unfold initOpenLocals
  dsimp only
  rw [show (traitBoundedIdBody.locals.drop 1).take
      traitBoundedIdBody.argumentCount = [.param 0] from rfl]
  have hCheck' : checkOpenArgsMatch p0 env' [v1] [.param 0] = true := hCheck
  rw [hCheck']
  rw [canary_ite_false]
  have hSlot : openLiveUninitSlot p0 (.param 0) = .immediate none := by
    unfold openLiveUninitSlot
    rw [canary_normalizeOpenTy_of_step_fixed _ _ rfl]
    rfl
  rw [show initOpenLocalsBuild p0 traitBoundedIdBody 0
      traitBoundedIdBody.locals [v1] =
      some [openLiveUninitSlot p0 (.param 0), .immediate (some v1)]
      from rfl, hSlot]
  rfl
  · rfl
  · rfl
  · rfl

/-- Parametric verification of `trait_bounded_id<T: ByValId>(x: T) -> T`. -/
theorem canary_trait_bounded_id_parametric_verified :
    ParametricBodyVerified byValTraitProgram byValTraitExecEnv 0
      traitBoundedIdBody (fun _ _ => True) := by
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun paramSpecs paramInvs assocSpecs hLen hWf _ hWhere => ?_⟩
  cases paramSpecs with
  | nil => exact canary_nat_zero_ne_succ hLen
  | cons sp0 rest =>
      cases rest with
      | cons _ _ => exact canary_nat_succ_ne_zero (Nat.succ.inj hLen)
      | nil =>
          let ⟨spS, hEvS, _, hSized⟩ := hWhere.2.1
          cases hEvS
          let env' : OpenExecEnv :=
            { byValTraitExecEnv with
              typeSpecs := substTypeSpecEnv byValTraitExecEnv.typeSpecs
                [sp0] paramInvs assocSpecs }
          have hAdm :
              OpenBodyStaticAdmitted byValTraitProgram env'
                traitBoundedIdBody :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              ⟨⟨sp0, rfl, rfl, hWf.1, hSized⟩,
               ⟨sp0, rfl, rfl, hWf.1, hSized⟩, True.intro⟩⟩
          refine ⟨hAdm, fun args hArgs _ => ?_⟩
          let ⟨v1, hArgsEq, hV1⟩ :=
            checkOpenArgsMatch_one_shape byValTraitProgram env' (.param 0) args
              hArgs.1
          subst hArgsEq
          have hCheck :
              checkOpenArgsMatch byValTraitProgram env' [v1] [.param 0] =
                true :=
            bool_and_eq_true hV1 rfl
          have hInit := openInitState_traitBoundedId env' v1 hCheck
          exact (byValCopy_wf_and_behavior
            (entryOpenProgForBody byValTraitProgram 0) env'
            traitBoundedIdBody.sig.whereClauses 0 traitBoundedIdBody (.param 0)
            v1 rfl rfl rfl rfl rfl rfl rfl hV1 hInit).1

/-- Positive Canary 10e: end-to-end trait-bounded `ClosedInstantiationTransfer`
for `trait_bounded_id<T: ByValId>(x: T) -> T` instantiated at `u64` yields
Day-1 `BodyVerified` and executes on `[42_u64]` to `.returned ⟨42_u64, ⟨[]⟩⟩`.
-/
theorem canary_day1_erasure_trait_bounded_id_u64 :
    let erasedProg := eraseOpenProgram [.int .i64 false] byValTraitProgram
    let erasedBody := eraseOpenBody byValTraitProgram.traitRegistry
      [.int .i64 false] traitBoundedIdBody
    BodyVerified erasedProg 0 erasedBody (fun _ => True) ∧
    ValidEntryArgs erasedBody [canaryVal42U64] ∧
    Behavior (entryProgForBody erasedProg 0) { args := [canaryVal42U64] }
      (.returned ⟨canaryVal42U64, ⟨[]⟩⟩) := by
  have hWf : AllSubstTypesWellFormed byValTraitProgram byValTraitExecEnv
      [.int .i64 false] := by
    intro ty hMem
    cases hMem with
    | head =>
        exact ⟨rfl, rfl, intTypeLayoutSpec .i64, rfl,
          wellFormed_intTypeLayoutSpec .i64⟩
    | tail _ h => cases h
  have hVer : BodyVerified
      (eraseOpenProgram [.int .i64 false] byValTraitProgram) 0
      (eraseOpenBody byValTraitProgram.traitRegistry [.int .i64 false]
        traitBoundedIdBody)
      (fun _ => True) :=
    ClosedInstantiationTransfer byValTraitProgram byValTraitExecEnv 0
      traitBoundedIdBody [.int .i64 false] (fun _ _ => True) (fun _ => True)
      canary_trait_bounded_id_parametric_verified rfl hWf
      canary_by_val_trait_impl_satisfies_sem.2 rfl rfl rfl rfl rfl
      (fun h => by cases h)
  let erasedProg := eraseOpenProgram [.int .i64 false] byValTraitProgram
  let ds0 : State :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 0
         , locals := [.immediate none, .immediate (some canaryVal42U64)] }]
    , callerMem := ⟨[]⟩
    , mem := entryMemory }
  let ds1 : State :=
    { frames :=
        [{ defId := 0
         , blockIdx := 0
         , stmtIdx := 1
         , locals :=
             [.immediate (some canaryVal42U64),
              .immediate (some canaryVal42U64)] }]
    , callerMem := ⟨[]⟩
    , mem := entryMemory }
  have hStep0 : Step (entryProgForBody erasedProg 0) ds0 (.step ds1) :=
    ⟨0, rfl, rfl⟩
  exact ⟨hVer, rfl, ⟨ds1, .tail (.refl ds0) hStep0, 0, rfl, rfl⟩⟩

/-- Canary 11a: characterizes the exact `openClosedTySupported` boundary:
closed Day-1-convertible references, raw pointers, and non-overflow tuples are
refused, whereas closed references to non-Day-1 pointees (`&[u8]`, `&MemSlice`)
yield `toClosedMirTy? = none` and remain admitted (as documented in Gap #7). -/
theorem canary_openClosedTySupported_boundary :
    openClosedTySupported [] (.ref .shared (.int .i64 false)) = false ∧
    openClosedTySupported [] (.rawPtr .shared .bool) = false ∧
    openClosedTySupported [] (.tuple [.int .i64 false, .int .i64 false]) =
      false ∧
    openClosedTySupported [] (.ref .shared (.slice (.int .i8 false))) = true ∧
    openClosedTySupported [] (.ref .shared (.adt memSliceAdtId [])) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Trait id for Canary 11b testing out-of-range `.param` rejection in
`AssumeGuaranteeTraitCall`. -/
@[expose] noncomputable def traitParamBoundId : TraitDefId := 3

/-- Helper constructing a 0-param `TraitContract` (`Self = .param 0` only)
whose single method (`methodIdx = 0`) uses the supplied `argTys`, `retTy`, and
`whereClauses`. -/
noncomputable def paramBoundContract (argTys : List OpenMirTy)
    (retTy : OpenMirTy) (wcs : List WhereClause) : TraitContract :=
  { traitId := traitParamBoundId
  , tyParamCount := 0
  , assocTypeCount := 0
  , methodSpecs :=
      [{ sig :=
           { methodIdx := 0
           , argTys := argTys
           , retTy := retTy
           , whereClauses := wcs
           , isUnsafe := false }
       , pre := fun _ _ _ _ => True
       , post := fun _ _ argVals _ out =>
           match out, argVals with
           | .returned ⟨rv, ⟨[]⟩⟩, v :: _ => rv = v
           | _, _ => False }] }

/-- Two-parameter caller body `fn foo<A: T, B>(a: A, b: B) -> retTy` invoking
`<A as T>::m(a)` into local `_0 : retTy`. -/
noncomputable def twoParamCallerBody (retTy : OpenMirTy) : OpenBody :=
  { sig :=
      { tyParamCount := 2
      , argTys := [.param 0, .param 1]
      , retTy := retTy
      , whereClauses :=
          [ .traitBound (.param 0) traitParamBoundId []
          , .isSized (.param 0)
          , .isSized (.param 1) ] }
  , argumentCount := 2
  , locals := [retTy, .param 0, .param 1]
  , basicBlocks :=
      [{ statements := []
       , terminator :=
           .traitCall (.param 0) traitParamBoundId [] 0
             [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_ }
       , { statements := [], terminator := .return_ }]
  , isUnsafe := false
  , identity := "canary::two_param_caller" }

/-- Negative Canary 11b (with non-vacuous positive control): in a 2-parameter
caller (`A = .param 0`, `B = .param 1`) calling a 0-parameter trait (`Self`
only), `AssumeGuaranteeTraitCall` fails closed (`.fault .unsupported`) whenever
`mspec.sig.{retTy, argTys, whereClauses}` contains out-of-range `.param 1`,
while stepping normally on the matching in-bounds `.param 0` signature. -/
theorem canary_assume_guarantee_out_of_range_param_refused :
    let mkProg (retTy : OpenMirTy) : OpenProgram :=
      { bodies := [twoParamCallerBody retTy]
      , entryDefId := 0
      , traitRegistry := []
      , pointerWidthBits := 64
      , mirProfileVersion := 1
      , scope := .unit }
    let mkEnv (c : TraitContract) : OpenExecEnv :=
      { typeSpecs :=
          { paramSpecs := [intTypeLayoutSpec .i64, intTypeLayoutSpec .i64]
          , paramInvs := [fun _ => True, fun _ => True]
          , adtSpecs := fun _ _ => none
          , assocSpecs := fun _ _ _ _ => none }
      , traitContracts := fun tr =>
          if Nat.beq tr traitParamBoundId then some c else none }
    let frame : OpenFrameState :=
      { defId := 0
      , blockIdx := 0
      , stmtIdx := 0
      , locals :=
          [ .immediate none
          , .immediate (some canaryVal42U64)
          , .immediate (some canaryVal42U64) ]
      , retDst := none }
    let s : OpenState :=
      { frames := [frame], callerMem := ⟨[]⟩, mem := MemoryState.empty }
    let wcs := (twoParamCallerBody (.param 1)).sig.whereClauses
    (∀ res,
      AssumeGuaranteeTraitCall (mkProg (.param 1))
        (mkEnv (paramBoundContract [.param 0] (.param 1) [])) wcs s
        (twoParamCallerBody (.param 1)) frame [] (.param 0) traitParamBoundId
        [] 0 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_ res →
      res = .fault .unsupported) ∧
    (∀ res,
      AssumeGuaranteeTraitCall (mkProg (.param 0))
        (mkEnv (paramBoundContract [.param 1] (.param 0) [])) wcs s
        (twoParamCallerBody (.param 0)) frame [] (.param 0) traitParamBoundId
        [] 0 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_ res →
      res = .fault .unsupported) ∧
    (∀ res,
      AssumeGuaranteeTraitCall (mkProg (.param 0))
        (mkEnv (paramBoundContract [.param 0] (.param 0) [.isSized (.param 1)]))
        wcs s (twoParamCallerBody (.param 0)) frame [] (.param 0)
        traitParamBoundId [] 0 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_
        res →
      res = .fault .unsupported) ∧
    (∃ s',
      AssumeGuaranteeTraitCall (mkProg (.param 0))
        (mkEnv (paramBoundContract [.param 0] (.param 0) [])) wcs s
        (twoParamCallerBody (.param 0)) frame [] (.param 0) traitParamBoundId
        [] 0 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_ (.step s')) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro res hStep
    unfold AssumeGuaranteeTraitCall at hStep
    exact hStep
  · intro res hStep
    unfold AssumeGuaranteeTraitCall at hStep
    exact hStep
  · intro res hStep
    unfold AssumeGuaranteeTraitCall at hStep
    exact hStep
  · refine ⟨{ frames :=
                [{ defId := 0
                 , blockIdx := 1
                 , stmtIdx := 0
                 , locals :=
                     [ .immediate (some canaryVal42U64)
                     , .immediate (some canaryVal42U64)
                     , .immediate (some canaryVal42U64) ]
                 , retDst := none }]
            , callerMem := ⟨[]⟩
            , mem := MemoryState.empty }, ?_⟩
    unfold AssumeGuaranteeTraitCall
    exact Or.inr
      ⟨True.intro, .returned ⟨canaryVal42U64, ⟨[]⟩⟩, rfl, rfl⟩

/-- Signed `i64` scalar literal `42_i64` for Canary 11c. -/
noncomputable def canaryVal42I64 : Val := .scalar ⟨.i64, true, 42⟩

/-- Monomorphic `i64 -> i64` callee body returning its argument. -/
noncomputable def i64CalleeBody : OpenBody :=
  { sig :=
      { tyParamCount := 0
      , argTys := [.int .i64 true]
      , retTy := .int .i64 true
      , whereClauses := [] }
  , argumentCount := 1
  , locals := [.int .i64 true, .int .i64 true]
  , basicBlocks :=
      [{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
       , terminator := .return_
       , cleanup := false }]
  , isUnsafe := false
  , identity := "canary::i64_callee_id" }

/-- Caller body with configurable destination local `_0 : dstTy` and single
argument `_1 : i64` for `concreteTraitCallStep` regression checks. -/
noncomputable def concreteCallerBody (dstTy : OpenMirTy) : OpenBody :=
  { sig :=
      { tyParamCount := 1
      , argTys := [.int .i64 true]
      , retTy := dstTy
      , whereClauses := [] }
  , argumentCount := 1
  , locals := [dstTy, .int .i64 true]
  , basicBlocks := [{ statements := [], terminator := .return_ }]
  , isUnsafe := false
  , identity := "canary::concrete_caller" }

/-- Negative Canary 11c (with non-vacuous positive control):
`concreteTraitCallStep` refuses destination return-type mismatches against an
`i64`-returning callee (`.param 0` instantiated at `u64` and closed `u64`, both
sharing `intTypeLayoutSpec .i64`), non-empty destination projections, and
out-of-bounds destination locals, while stepping normally on unprojected
`⟨0, []⟩` of matching type `i64`. -/
theorem canary_concrete_trait_call_dst_mismatch_refused :
    let mkProg (dstTy : OpenMirTy) : OpenProgram :=
      { bodies := [concreteCallerBody dstTy, i64CalleeBody]
      , entryDefId := 0
      , traitRegistry :=
          [ ( ⟨.int .i64 true, traitByValId, []⟩
            , { implTyParamCount := 0
              , whereClauses := []
              , assocTypes := []
              , methodDefIds := [(0, 1)] } ) ]
      , pointerWidthBits := 64
      , mirProfileVersion := 1
      , scope := .unit }
    let env : OpenExecEnv :=
      { typeSpecs :=
          { paramSpecs := [intTypeLayoutSpec .i64]
          , paramInvs := [fun _ => True]
          , adtSpecs := fun _ _ => none
          , assocSpecs := fun _ _ _ _ => none }
      , traitContracts := fun _ => none }
    let frame : OpenFrameState :=
      { defId := 0
      , blockIdx := 0
      , stmtIdx := 0
      , locals := [.immediate none, .immediate (some canaryVal42I64)]
      , retDst := none }
    let s : OpenState :=
      { frames := [frame], callerMem := ⟨[]⟩, mem := MemoryState.empty }
    let callWith (dstTy : OpenMirTy) (dst : OpenPlace) :=
      concreteTraitCallStep (mkProg dstTy) env s (concreteCallerBody dstTy)
        frame [] (.int .i64 true) traitByValId [] 0 [.copy ⟨1, []⟩] dst
        (some 0) .continue_
    callWith (.param 0) ⟨0, []⟩ = .fault .unsupported ∧
    callWith (.int .i64 false) ⟨0, []⟩ = .fault .unsupported ∧
    callWith (.int .i64 true) ⟨0, [.deref]⟩ = .fault .unsupported ∧
    callWith (.int .i64 true) ⟨99, []⟩ = .fault .unsupported ∧
    ∃ s', callWith (.int .i64 true) ⟨0, []⟩ = .step s' :=
  ⟨rfl, rfl, rfl, rfl, ⟨_, rfl⟩⟩

end Anneal.Generic

end
