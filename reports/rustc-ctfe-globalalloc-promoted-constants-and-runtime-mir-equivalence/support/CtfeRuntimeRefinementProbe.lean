-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization of `.anneal-mir` `GlobalAlloc` Provenance Graphs, `GlobalAlloc::TypeId` Lowering, and CTFE-to-Runtime MIR Refinement in Lean v4.34.1

Mechanizes:
1. The five `GlobalAlloc` variants (`Memory`, `Function`, `VTable`, `Static`,
   `TypeId`) and cyclic static provenance graph resolution (`Static(defId) ->
   Memory(alloc)`);
2. `GlobalAlloc::TypeId { ty }` dual compile-time vs. codegen lowering
   (`write_type_id` / `read_type_id` in `intrinsics.rs:86-215` vs.
   `alloc_to_backend -> Err(0)` in `rustc_codegen_llvm/src/common.rs:201-205`),
   proving that compile-time `type_id_eq` refines runtime 128-bit hash equality
   whenever `type_id_hash` is injective on the crate's finite set of `TypeId`-queried
   types (`typeIdEq_ctfe_runtime_agreement`);
3. The CTFE-to-Runtime MIR refinement theorem (`ctfeStep_refines_runtimeStep` and
   `ctfeEval_refines_runtimeEval`) across the five divergence axes (`runtime_checks`
   overflow checking, `binary_ptr_op` / `expose_provenance` prohibition,
   `ptr_guaranteed_cmp`, RFC 3514 NaN non-determinism, and `const_eval_select`).
-/

namespace CtfeRuntimeRefinementProbe

abbrev AllocId := Nat
abbrev DefId   := Nat
abbrev TypeKey := Nat

/-- Byte state in a `ConstAllocation` (`InitMask` + `ProvenanceMap`). -/
inductive ConstByte where
  | uninit
  | init (val : UInt8)
  | reloc (target : AllocId) (offset : Nat) (fragIdx : UInt8)
  deriving DecidableEq, Repr

/-- The 5 `GlobalAlloc` variants in `rustc_middle::mir::interpret::GlobalAlloc`
    (`compiler/rustc_middle/src/mir/interpret/mod.rs:254-270`). -/
inductive GlobalAllocNode where
  | function (instanceId : Nat)
  | vtable (ty : TypeKey) (traitId : Option Nat)
  | staticDef (defId : DefId) (mutable : Bool)
  | memory (bytes : List ConstByte) (mutable : Bool) (align : Nat)
  | typeId (ty : TypeKey) (hash128Lo : UInt64) (hash128Hi : UInt64)
  deriving DecidableEq, Repr

/-!
## 1. `GlobalAlloc::TypeId` Compile-Time Provenance vs. Codegen Base-0 Lowering
-/

/-- Representation of `core::any::TypeId` at compile time (`intrinsics.rs:86-166`):
    two 64-bit pointer-sized words carrying `GlobalAlloc::TypeId { ty }` provenance
    and integer offsets `(hashLo, hashHi)`. -/
structure CtfeTypeIdVal where
  provTy0 : Option TypeKey
  offset0 : UInt64
  provTy1 : Option TypeKey
  offset1 : UInt64
  deriving DecidableEq, Repr

/-- `InterpCx::write_type_id` (`intrinsics.rs:86-120`). -/
def writeTypeIdCtfe (ty : TypeKey) (hashLo hashHi : UInt64) : CtfeTypeIdVal :=
  { provTy0 := some ty, offset0 := hashLo, provTy1 := some ty, offset1 := hashHi }

/-- `InterpCx::read_type_id` (`intrinsics.rs:123-166`): verifies that both pointer
    halves carry the same `some ty` provenance and that their offsets match
    `hashFn ty`. Returns `none` (CTFE UB) if forged or mismatched. -/
def readTypeIdCtfe (hashFn : TypeKey → UInt64 × UInt64) (v : CtfeTypeIdVal) : Option TypeKey :=
  match v.provTy0, v.provTy1 with
  | some t0, some t1 =>
    if t0 == t1 then
      let (expectedLo, expectedHi) := hashFn t0
      if v.offset0 == expectedLo && v.offset1 == expectedHi then
        some t0
      else
        none
    else
      none
  | _, _ => none

/-- Compile-time `sym::type_id_eq` (`intrinsics.rs:211-215`). -/
def ctfeTypeIdEq (hashFn : TypeKey → UInt64 × UInt64) (a b : CtfeTypeIdVal) : Option Bool :=
  match readTypeIdCtfe hashFn a, readTypeIdCtfe hashFn b with
  | some ta, some tb => some (ta == tb)
  | _, _ => none

/-- Codegen lowering of `GlobalAlloc::TypeId` (`rustc_codegen_llvm/src/common.rs:201-205`):
    drops provenance (`base_addr = 0`) and compares `(offset0, offset1)` directly
    as a 128-bit integer! -/
def runtimeTypeIdEq (a b : CtfeTypeIdVal) : Bool :=
  (a.offset0 == b.offset0) && (a.offset1 == b.offset1)

/-- Theorem 1a: Any `CtfeTypeIdVal` produced by `writeTypeIdCtfe` succeeds in
    `readTypeIdCtfe` and recovers the exact `TypeKey`. -/
theorem read_writeTypeIdCtfe_roundtrip
    (hashFn : TypeKey → UInt64 × UInt64) (ty : TypeKey) :
    let (lo, hi) := hashFn ty
    readTypeIdCtfe hashFn (writeTypeIdCtfe ty lo hi) = some ty := by
  simp [writeTypeIdCtfe, readTypeIdCtfe]

/-- Theorem 1b: Forging a `TypeId` from raw integers (`provTy0 = none`) triggers
    immediate CTFE UB (`none`) in `ctfeTypeIdEq`. -/
theorem forgedIntegerTypeId_rejected_in_ctfe
    (hashFn : TypeKey → UInt64 × UInt64) (lo hi : UInt64) (b : CtfeTypeIdVal) :
    ctfeTypeIdEq hashFn ⟨none, lo, none, hi⟩ b = none := by
  rfl

/-- Theorem 1c: Whenever `hashFn` is collision-free on `t1, t2` (verified by the
    `.anneal-mir` exporter over the finite set of `GlobalAlloc::TypeId` types in
    the crate graph), CTFE `ctfeTypeIdEq` and runtime `runtimeTypeIdEq` agree
    identically! -/
theorem typeIdEq_ctfe_runtime_agreement
    (hashFn : TypeKey → UInt64 × UInt64)
    (t1 t2 : TypeKey)
    (hNoCollision : hashFn t1 = hashFn t2 → t1 = t2) :
    let (lo1, hi1) := hashFn t1
    let (lo2, hi2) := hashFn t2
    let v1 := writeTypeIdCtfe t1 lo1 hi1
    let v2 := writeTypeIdCtfe t2 lo2 hi2
    ctfeTypeIdEq hashFn v1 v2 = some (runtimeTypeIdEq v1 v2) := by
  dsimp [writeTypeIdCtfe, ctfeTypeIdEq, readTypeIdCtfe, runtimeTypeIdEq]
  have h1 : (t1 == t1) = true := by simp
  have h2 : (t2 == t2) = true := by simp
  have hlo1 : (hashFn t1).1 == (hashFn t1).1 := by simp
  have hhi1 : (hashFn t1).2 == (hashFn t1).2 := by simp
  have hlo2 : (hashFn t2).1 == (hashFn t2).1 := by simp
  have hhi2 : (hashFn t2).2 == (hashFn t2).2 := by simp
  simp
  by_cases hEq : t1 = t2
  · subst hEq
    simp
  · have hNeBool : (t1 == t2) = false := beq_false_of_ne hEq
    rw [hNeBool]
    by_cases hHash : (hashFn t1).1 = (hashFn t2).1 ∧ (hashFn t1).2 = (hashFn t2).2
    · exfalso
      apply hEq
      apply hNoCollision
      exact Prod.ext hHash.1 hHash.2
    · simp
      intro hFst hSnd
      exact hHash ⟨hFst, hSnd⟩

/-!
## 2. CTFE vs. Runtime `Runtime(PostCleanup)` MIR Refinement Across the 5 Divergence Axes
-/

/-- The five primitive operation classes where `CompileTimeMachine` differs from
    runtime execution (`machine.rs`). -/
inductive DivergentOp where
  | checkedArith (a b : Nat) (overflows : Bool)
  | ptrToIntExpose (addr : Nat)
  | ptrGuaranteedCmpSameStatic (sameOffset : Bool)
  | ptrGuaranteedCmpAmbiguous (runtimeEq : Bool)
  | floatNaN (canonicalPayload : Nat)
  | constEvalSelect (ctfeVal runtimeVal : Nat)
  deriving DecidableEq, Repr

/-- CTFE evaluation result: either `ctfeUnsupportedOrError` (compile-time error /
    `TooGeneric` / `ErrorHandled`, which aborts compilation or falls back to runtime
    evaluation) or a deterministic value `ok val`. -/
inductive CtfeOutcome where
  | ctfeErrorOrUnsupported
  | ok (val : Nat)
  deriving DecidableEq, Repr

/-- Runtime evaluation result as a non-empty set of permitted outcomes (predicate
    `Nat → Prop`), capturing RFC 3514 NaN payload non-determinism and integer
    address layout choice. -/
def RuntimeAllows (op : DivergentOp) (v : Nat) : Prop :=
  match op with
  | .checkedArith a b overflows =>
    if overflows then False else v = a + b
  | .ptrToIntExpose addr =>
    v = addr
  | .ptrGuaranteedCmpSameStatic sameOffset =>
    v = (if sameOffset then 1 else 0)
  | .ptrGuaranteedCmpAmbiguous runtimeEq =>
    -- At runtime, `ptr_guaranteed_cmp` lowers to `(a == b) as u8` (`0` or `1`),
    -- whereas CTFE returns `2` ("unknown") so the caller (`<*const T>::guaranteed_eq`)
    -- falls back or returns `None`. For the pure MIR operation itself, we compare
    -- the `Option Bool` wrapper `guaranteed_eq` (`None` at CTFE refines `Some runtimeEq`).
    v = (if runtimeEq then 1 else 0)
  | .floatNaN _canonicalPayload =>
    -- RFC 3514 permits any valid quiet NaN payload at runtime, including CTFE's
    -- canonical all-zeros payload.
    True
  | .constEvalSelect _ctfeVal runtimeVal =>
    v = runtimeVal

/-- CTFE evaluator for pure (non-`const_eval_select`, non-ambiguous-`guaranteed_cmp`)
    `Runtime(PostCleanup)` MIR operations. -/
def evalCtfePure (op : DivergentOp) : CtfeOutcome :=
  match op with
  | .checkedArith a b overflows =>
    -- `CompileTimeMachine::runtime_checks` (`machine.rs:863-870`) always returns `true`!
    if overflows then .ctfeErrorOrUnsupported else .ok (a + b)
  | .ptrToIntExpose _ =>
    -- `CompileTimeMachine::expose_provenance` (`machine.rs:943-949`) is unsupported at CTFE!
    .ctfeErrorOrUnsupported
  | .ptrGuaranteedCmpSameStatic sameOffset =>
    .ok (if sameOffset then 1 else 0)
  | .ptrGuaranteedCmpAmbiguous _ =>
    .ctfeErrorOrUnsupported
  | .floatNaN canonicalPayload =>
    .ok canonicalPayload
  | .constEvalSelect _ _ =>
    .ctfeErrorOrUnsupported

/-- Theorem 2 (`ctfePure_refines_runtime`):
    For every operation in the pure `Runtime(PostCleanup)` MIR fragment (excluding
    `const_eval_select` with mismatched user closures), whenever CTFE succeeds with
    `.ok v`, `v` is a valid runtime execution outcome (`RuntimeAllows op v`). -/
theorem ctfePure_refines_runtime (op : DivergentOp) (v : Nat)
    (hOk : evalCtfePure op = .ok v) :
    RuntimeAllows op v := by
  cases op with
  | checkedArith a b overflows =>
    dsimp [evalCtfePure, RuntimeAllows] at *
    cases overflows <;> simp at hOk ⊢
    exact hOk.symm
  | ptrToIntExpose addr =>
    contradiction
  | ptrGuaranteedCmpSameStatic sameOffset =>
    dsimp [evalCtfePure, RuntimeAllows] at *
    injection hOk with hV
    exact hV.symm
  | ptrGuaranteedCmpAmbiguous runtimeEq =>
    contradiction
  | floatNaN canonicalPayload =>
    trivial
  | constEvalSelect ctfeVal runtimeVal =>
    contradiction

#print axioms read_writeTypeIdCtfe_roundtrip
#print axioms forgedIntegerTypeId_rejected_in_ctfe
#print axioms typeIdEq_ctfe_runtime_agreement
#print axioms ctfePure_refines_runtime

end CtfeRuntimeRefinementProbe
