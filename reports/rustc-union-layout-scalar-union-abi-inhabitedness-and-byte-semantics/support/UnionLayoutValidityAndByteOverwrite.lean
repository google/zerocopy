/-!
# Formalization of `rustc` `union` Layout, `Scalar::Union` ABI Erasure,
# Universal Inhabitedness, and Byte-Level Partial Overwrite Semantics

Self-contained kernel-checked Lean 4 (`v4.34.1`) constructive mechanization:
elementary `Nat` and `List` proofs only; zero unproved obligations, zero classical
choice axioms, zero linear-arithmetic or bitblasting decision-procedure tactics,
zero native-reflection evaluators, zero non-terminating definitions, and zero
unsafe recursion helpers.

Mirrors `rust-lang/rust`:
- `compiler/rustc_abi/src/lib.rs` (`Scalar::Initialized`, `Scalar::Union`,
  `Scalar::to_union`, `Scalar::is_uninit_valid`, `Scalar::is_always_valid`,
  `BackendRepr::to_union`, `ReprOptions::inhibits_union_abi_opt`)
- `compiler/rustc_abi/src/layout.rs` (`LayoutCalculator::layout_of_union`,
  `LayoutCalculator::layout_of_univariant_biased`)
- `compiler/rustc_middle/src/ty/inhabitedness/mod.rs`
  (`Ty::inhabited_predicate`, `OpsemInhabitedCtx::is_inhabited_adt_ty`)
- `compiler/rustc_ty_utils/src/abi.rs` (`arg_attrs_for_rust_scalar`)
- `compiler/rustc_target/src/callconv/mod.rs` (`layout_is_noundef`, `adjust_for_rust_abi`)
- `compiler/rustc_const_eval/src/interpret/validity.rs`
  (`ValidityVisitor::visit_union`, `union_data_range`)
- `compiler/rustc_const_eval/src/interpret/place.rs`
  (`write_immediate_to_mplace_no_validate`, `copy_op_no_validate`)
-/

namespace RustcUnionSemantics

/-! ## Section 1: Abstract Byte Buffer & Well-Formedness -/

/-- A single machine byte in Miri / MiniRust abstract memory: either
uninitialized (`.uninit`) or an 8-bit value (`0 ≤ val < 256`) with optional
pointer provenance (`prov`). -/
inductive AbstractByte where
  | uninit
  | bits (val : Nat) (prov : Option Nat)
  deriving DecidableEq, Repr

/-- Well-formedness of a single abstract byte (`val < 256` on initialized bytes). -/
def ByteWF : AbstractByte → Bool
  | .uninit => true
  | .bits val _ => decide (val < 256)

abbrev ByteBuffer := List AbstractByte

/-- Every byte in a buffer satisfies `ByteWF`. -/
def BufferWF : ByteBuffer → Bool
  | [] => true
  | b :: bs => ByteWF b && BufferWF bs

/-- Predicate checking whether a byte buffer contains any `.uninit` byte. -/
def bufHasUninit : ByteBuffer → Bool
  | [] => false
  | .uninit :: _ => true
  | .bits _ _ :: bs => bufHasUninit bs

theorem bufferWF_replicate_uninit (n : Nat) :
    BufferWF (List.replicate n AbstractByte.uninit) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [List.replicate_succ, BufferWF, ByteWF, ih]

theorem bufferWF_append {xs ys : ByteBuffer}
    (hx : BufferWF xs = true) (hy : BufferWF ys = true) :
    BufferWF (xs ++ ys) = true := by
  induction xs with
  | nil => exact hy
  | cons a rest ih =>
    simp only [List.cons_append, BufferWF, Bool.and_eq_true] at hx ⊢
    exact ⟨hx.1, ih hx.2⟩

theorem bufferWF_take (n : Nat) (xs : ByteBuffer) (hx : BufferWF xs = true) :
    BufferWF (xs.take n) = true := by
  induction n generalizing xs with
  | zero => simp [BufferWF]
  | succ k ih =>
    cases xs with
    | nil => simp [BufferWF]
    | cons a rest =>
      simp only [List.take_succ_cons, BufferWF, Bool.and_eq_true] at hx ⊢
      exact ⟨hx.1, ih rest hx.2⟩

theorem bufferWF_drop (n : Nat) (xs : ByteBuffer) (hx : BufferWF xs = true) :
    BufferWF (xs.drop n) = true := by
  induction n generalizing xs with
  | zero => exact hx
  | succ k ih =>
    cases xs with
    | nil => simp [BufferWF]
    | cons a rest =>
      simp only [List.drop_succ_cons]
      simp only [BufferWF, Bool.and_eq_true] at hx
      exact ih rest hx.2

theorem bufHasUninit_replicate_uninit_succ (k : Nat) :
    bufHasUninit (List.replicate (k + 1) AbstractByte.uninit) = true := by
  simp [List.replicate_succ, bufHasUninit]

/-! ## Section 2: `Scalar`, `BackendRepr::to_union`, and ABI Erasure -/

/-- Primitive scalar register class (`rustc_abi::Primitive`). -/
inductive PrimKind where
  | int (signed : Bool)
  | float
  | pointer
  deriving DecidableEq, Repr

/-- `rustc_abi::Scalar`: either `Initialized` (carrying `noundef` and an
optional niche/validity range) or `Union` (erasing validity range and permitting
uninitialized bytes). -/
inductive ScalarAbi where
  | initialized (prim : PrimKind) (sizeBytes : Nat) (validMin validMax : Nat) (hasNiche : Bool)
  | unionScalar (prim : PrimKind) (sizeBytes : Nat)
  deriving DecidableEq, Repr

namespace ScalarAbi

def primitive : ScalarAbi → PrimKind
  | .initialized p _ _ _ _ => p
  | .unionScalar p _ => p

def sizeBytes : ScalarAbi → Nat
  | .initialized _ sz _ _ _ => sz
  | .unionScalar _ sz => sz

/-- `Scalar::to_union` (`compiler/rustc_abi/src/lib.rs:1636-1638`). -/
def toUnion : ScalarAbi → ScalarAbi
  | .initialized p sz _ _ _ => .unionScalar p sz
  | .unionScalar p sz => .unionScalar p sz

/-- `Scalar::is_uninit_valid` (`compiler/rustc_abi/src/lib.rs:1670-1675`). -/
def isUninitValid : ScalarAbi → Bool
  | .initialized _ _ _ _ _ => false
  | .unionScalar _ _ => true

/-- `Scalar::is_always_valid` (`compiler/rustc_abi/src/lib.rs:1661-1666`). -/
def isAlwaysValid : ScalarAbi → Bool
  | .initialized _ _ _ _ hasNiche => !hasNiche
  | .unionScalar _ _ => true

/-- True iff `ScalarAbi` is the `Scalar::Union` variant. -/
def isUnionVariant : ScalarAbi → Bool
  | .initialized _ _ _ _ _ => false
  | .unionScalar _ _ => true

theorem toUnion_isUnionVariant (s : ScalarAbi) : s.toUnion.isUnionVariant = true := by
  cases s <;> rfl

theorem toUnion_isUninitValid (s : ScalarAbi) : s.toUnion.isUninitValid = true := by
  cases s <;> rfl

theorem toUnion_isAlwaysValid (s : ScalarAbi) : s.toUnion.isAlwaysValid = true := by
  cases s <;> rfl

theorem toUnion_idempotent (s : ScalarAbi) : s.toUnion.toUnion = s.toUnion := by
  cases s <;> rfl

theorem toUnion_preserves_primitive (s : ScalarAbi) : s.toUnion.primitive = s.primitive := by
  cases s <;> rfl

theorem toUnion_preserves_size (s : ScalarAbi) : s.toUnion.sizeBytes = s.sizeBytes := by
  cases s <;> rfl

end ScalarAbi

/-- `rustc_abi::BackendRepr` (`compiler/rustc_abi/src/lib.rs:1938-1993`). -/
inductive BackendRepr where
  | scalar (s : ScalarAbi)
  | scalarPair (a b : ScalarAbi) (bOffset : Nat)
  | simdVector (elem : ScalarAbi) (count : Nat)
  | memory
  deriving DecidableEq, Repr

namespace BackendRepr

/-- `BackendRepr::to_union` (`compiler/rustc_abi/src/lib.rs:1975-1993`). -/
def toUnion : BackendRepr → BackendRepr
  | .scalar s => .scalar s.toUnion
  | .scalarPair a b off => .scalarPair a.toUnion b.toUnion off
  | .simdVector elem count => .simdVector elem.toUnion count
  | .memory => .memory

/-- Platform scalar alignment for `Scalar` / `ScalarPair`, or `none` otherwise. -/
def scalarPlatformAlign (elemAlign : Nat) : BackendRepr → Option Nat
  | .scalar _ => some elemAlign
  | .scalarPair _ _ _ => some elemAlign
  | .simdVector _ _ => none
  | .memory => none

/-- Predicate asserting that every `ScalarAbi` inside a `BackendRepr` is `.unionScalar`. -/
def allScalarsUnion : BackendRepr → Bool
  | .scalar s => s.isUnionVariant
  | .scalarPair a b _ => a.isUnionVariant && b.isUnionVariant
  | .simdVector elem _ => elem.isUnionVariant
  | .memory => true

theorem toUnion_idempotent (r : BackendRepr) : r.toUnion.toUnion = r.toUnion := by
  cases r with
  | scalar s => simp [toUnion, ScalarAbi.toUnion_idempotent]
  | scalarPair a b off => simp [toUnion, ScalarAbi.toUnion_idempotent]
  | simdVector e c => simp [toUnion, ScalarAbi.toUnion_idempotent]
  | memory => rfl

theorem toUnion_allScalarsUnion (r : BackendRepr) : r.toUnion.allScalarsUnion = true := by
  cases r with
  | scalar s => exact ScalarAbi.toUnion_isUnionVariant s
  | scalarPair a b _ =>
    simp [toUnion, allScalarsUnion, ScalarAbi.toUnion_isUnionVariant]
  | simdVector e _ => exact ScalarAbi.toUnion_isUnionVariant e
  | memory => rfl

end BackendRepr

/-! ## Section 3: `layout_of_union` vs. `#[repr(transparent)]` `struct` Layout -/

/-- Layout descriptor for a single union (or transparent struct) field.
`bytePred` encodes the type-level bit/initialization validity invariant enforced
only upon reading/writing at that field's typed projection.
`dataMask` flags non-padding byte offsets inside `[0..size)` for `union_data_range`. -/
structure FieldSpec where
  fieldId : Nat
  size : Nat
  align : Nat
  backendRepr : BackendRepr
  platformScalarAlign : Nat
  largestNiche : Option Nat
  uninhabited : Bool
  bytePred : ByteBuffer → Bool
  dataMask : List Bool

/-- `rustc_abi::ReprOptions` subset governing union layout and ABI forwarding. -/
structure ReprOptions where
  isC : Bool
  isTransparent : Bool
  pack : Option Nat
  reprAlign : Option Nat
  deriving DecidableEq, Repr

/-- `ReprOptions::inhibits_union_abi_opt` (`compiler/rustc_abi/src/lib.rs:245-247`):
returns `self.c()`, deliberately NOT inhibited by `#[repr(transparent)]`. -/
def ReprOptions.inhibitsUnionAbiOpt (repr : ReprOptions) : Bool := repr.isC

/-- Computed ADT layout output (`LayoutData`). -/
structure ComputedLayout where
  size : Nat
  align : Nat
  backendRepr : BackendRepr
  largestNiche : Option Nat
  uninhabited : Bool
  fields : List FieldSpec
  dataMask : List Bool

/-- Alignment helper: round `sz` up to a multiple of `a` (when `a > 0`). -/
def alignTo (sz a : Nat) : Nat :=
  if a == 0 then sz
  else
    let rem := sz % a
    if rem == 0 then sz else sz + (a - rem)

/-- Recursive helper matching `layout_of_union`'s fold over fields
(`compiler/rustc_abi/src/layout.rs:431-468`). -/
def foldUnionFields :
    List FieldSpec → Nat → Nat → Option (Option BackendRepr) →
      (Nat × Nat × Option (Option BackendRepr))
  | [], al, sz, common => (al, sz, common)
  | f :: fs, al, sz, common =>
    let al' := Nat.max al f.align
    let sz' := Nat.max sz f.size
    if f.size == 0 then
      foldUnionFields fs al' sz' common
    else
      let fieldAbi := f.backendRepr.toUnion
      let common' := match common with
        | none => none
        | some none => some (some fieldAbi)
        | some (some prevAbi) =>
          if prevAbi == fieldAbi then some (some prevAbi) else none
      foldUnionFields fs al' sz' common'

/-- Computes `union_data_range` boolean mask across `[0..unionSize)` as the
pointwise disjunction (`||`) over every non-ZST field's `dataMask`. -/
def fieldHasDataAt (idx : Nat) (fields : List FieldSpec) : Bool :=
  match fields with
  | [] => false
  | f :: fs =>
    let here :=
      if f.size == 0 then false
      else match f.dataMask[idx]? with
        | some b => b
        | none => false
    here || fieldHasDataAt idx fs

def computeUnionDataMask (unionSize : Nat) (fields : List FieldSpec) : List Bool :=
  (List.range unionSize).map (fun i => fieldHasDataAt i fields)

/-- Models `LayoutCalculator::layout_of_union` (`compiler/rustc_abi/src/layout.rs:404-534`):
1. If `repr.inhibitsUnionAbiOpt` (`repr(C)`), initializes `common` to `AbiMismatch` (`none`).
2. Skips ZST fields (`f.size == 0`) when unifying `common_non_zst_repr_and_align`.
3. Applies `.toUnion` to every non-ZST field's `backendRepr`.
4. Caps alignment by `pack` and raises by `reprAlign`.
5. Demotes `Scalar`/`ScalarPair` to `BackendRepr.memory` when `scalarPlatformAlign != align`.
6. Unconditionally sets `largestNiche := none` and `uninhabited := false`. -/
def computeUnionLayout (repr : ReprOptions) (fields : List FieldSpec) : ComputedLayout :=
  let initCommon : Option (Option BackendRepr) :=
    if repr.inhibitsUnionAbiOpt then none else some none
  let (rawAlign, rawSize, common) := foldUnionFields fields 1 0 initCommon
  let packedAlign := match repr.pack with
    | some p => Nat.min rawAlign p
    | none => rawAlign
  let finalAlign := match repr.reprAlign with
    | some ra => Nat.max packedAlign ra
    | none => packedAlign
  let finalSize := alignTo rawSize finalAlign
  let finalRepr := match common with
    | none | some none => BackendRepr.memory
    | some (some r) => match r with
      | .scalar _ | .scalarPair _ _ _ =>
        match fields.find? (fun f => f.size != 0) with
        | some f0 =>
          if f0.platformScalarAlign == finalAlign then r else .memory
        | none => .memory
      | .simdVector _ _ =>
        match fields.find? (fun f => f.size != 0) with
        | some f0 =>
          if f0.align ≤ finalAlign then r else .memory
        | none => .memory
      | .memory => .memory
  {
    size := finalSize
    align := finalAlign
    backendRepr := finalRepr
    largestNiche := none
    uninhabited := false
    fields := fields
    dataMask := computeUnionDataMask finalSize fields
  }

/-- Models `#[repr(transparent)]` on a `struct` around one non-ZST field `f`
(`compiler/rustc_abi/src/layout.rs:827-934`), which forwards `f.backendRepr`,
`f.largestNiche`, and `f.uninhabited` WITHOUT calling `.toUnion`. -/
def computeTransparentStructLayout (f : FieldSpec) : ComputedLayout :=
  {
    size := f.size
    align := f.align
    backendRepr := f.backendRepr
    largestNiche := f.largestNiche
    uninhabited := f.uninhabited
    fields := [f]
    dataMask := f.dataMask
  }

theorem foldUnionFields_common_invariant
    (fs : List FieldSpec) (al sz : Nat) (common : Option (Option BackendRepr))
    (hinit : match common with | none => True | some none => True | some (some r) => r.allScalarsUnion = true) :
    match (foldUnionFields fs al sz common).2.2 with
    | none => True
    | some none => True
    | some (some r) => r.allScalarsUnion = true := by
  induction fs generalizing al sz common with
  | nil => exact hinit
  | cons f rest ih =>
    simp only [foldUnionFields]
    cases hz : (f.size == 0)
    · simp only [Bool.false_eq_true, ite_false]
      apply ih (Nat.max al f.align) (Nat.max sz f.size)
      cases common with
      | none => trivial
      | some opt =>
        cases opt with
        | none => exact BackendRepr.toUnion_allScalarsUnion f.backendRepr
        | some prev =>
          cases heq : (prev == f.backendRepr.toUnion)
          · simp [heq]
          · simp [heq, hinit]
    · simp only [ite_true]
      exact ih (Nat.max al f.align) (Nat.max sz f.size) common hinit

theorem computeUnionLayout_allScalarsUnion (repr : ReprOptions) (fields : List FieldSpec) :
    (computeUnionLayout repr fields).backendRepr.allScalarsUnion = true := by
  unfold computeUnionLayout
  have hinv := foldUnionFields_common_invariant fields 1 0
    (if repr.inhibitsUnionAbiOpt then none else some none)
    (by cases repr.inhibitsUnionAbiOpt <;> trivial)
  cases hfold : (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).2.2 with
  | none => simp [hfold, BackendRepr.allScalarsUnion]
  | some opt =>
    cases opt with
    | none => simp [hfold, BackendRepr.allScalarsUnion]
    | some r =>
      rw [hfold] at hinv
      dsimp at hinv
      simp only [hfold]
      cases r with
      | scalar s =>
        dsimp
        cases fields.find? (fun f => f.size != 0) with
        | none => rfl
        | some f0 =>
          dsimp
          cases hcond : (f0.platformScalarAlign ==
            match repr.reprAlign with
            | some ra =>
              Nat.max (match repr.pack with
                | some p => Nat.min (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1 p
                | none => (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1) ra
            | none =>
              match repr.pack with
              | some p => Nat.min (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1 p
              | none => (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1)
          · simp [BackendRepr.allScalarsUnion]
          · simp [hinv]
      | scalarPair a b off =>
        dsimp
        cases fields.find? (fun f => f.size != 0) with
        | none => rfl
        | some f0 =>
          dsimp
          cases hcond : (f0.platformScalarAlign ==
            match repr.reprAlign with
            | some ra =>
              Nat.max (match repr.pack with
                | some p => Nat.min (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1 p
                | none => (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1) ra
            | none =>
              match repr.pack with
              | some p => Nat.min (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1 p
              | none => (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1)
          · simp [BackendRepr.allScalarsUnion]
          · simp [hinv]
      | simdVector elem cnt =>
        dsimp
        cases fields.find? (fun f => f.size != 0) with
        | none => rfl
        | some f0 =>
          dsimp
          by_cases hcond : f0.align ≤
            match repr.reprAlign with
            | some ra =>
              Nat.max (match repr.pack with
                | some p => Nat.min (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1 p
                | none => (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1) ra
            | none =>
              match repr.pack with
              | some p => Nat.min (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1 p
              | none => (foldUnionFields fields 1 0 (if repr.inhibitsUnionAbiOpt then none else some none)).1
          · simp [hcond, hinv]
          · simp [hcond, BackendRepr.allScalarsUnion]
      | memory => rfl

theorem computeUnionLayout_largestNiche_none (repr : ReprOptions) (fields : List FieldSpec) :
    (computeUnionLayout repr fields).largestNiche = none := rfl

theorem computeUnionLayout_uninhabited_false (repr : ReprOptions) (fields : List FieldSpec) :
    (computeUnionLayout repr fields).uninhabited = false := rfl

theorem foldUnionFields_size_ge_acc (fs : List FieldSpec) (al sz : Nat)
    (common : Option (Option BackendRepr)) :
    sz ≤ (foldUnionFields fs al sz common).2.1 := by
  induction fs generalizing al sz common with
  | nil => exact Nat.le_refl sz
  | cons f rest ih =>
    simp only [foldUnionFields]
    cases hz : (f.size == 0)
    · simp only [Bool.false_eq_true, ite_false]
      exact Nat.le_trans (Nat.le_max_left sz f.size) (ih _ _ _)
    · simp only [ite_true]
      exact Nat.le_trans (Nat.le_max_left sz f.size) (ih _ _ _)

theorem foldUnionFields_size_ge_field (fs : List FieldSpec) (al sz : Nat)
    (common : Option (Option BackendRepr)) {f : FieldSpec} (hf : f ∈ fs) :
    f.size ≤ (foldUnionFields fs al sz common).2.1 := by
  induction fs generalizing al sz common with
  | nil => cases hf
  | cons x rest ih =>
    simp only [foldUnionFields]
    cases hf with
    | head =>
      cases hz : (f.size == 0)
      · simp only [Bool.false_eq_true, ite_false]
        exact Nat.le_trans (Nat.le_max_right sz f.size) (foldUnionFields_size_ge_acc _ _ _ _)
      · simp only [ite_true]
        exact Nat.le_trans (Nat.le_max_right sz f.size) (foldUnionFields_size_ge_acc _ _ _ _)
    | tail _ hmem =>
      cases hz : (x.size == 0)
      · simp only [Bool.false_eq_true, ite_false]
        exact ih _ _ _ hmem
      · simp only [ite_true]
        exact ih _ _ _ hmem

theorem alignTo_ge (sz a : Nat) : sz ≤ alignTo sz a := by
  unfold alignTo
  cases ha : (a == 0)
  · simp only [Bool.false_eq_true, ite_false]
    cases hr : (sz % a == 0)
    · simp only [Bool.false_eq_true, ite_false]
      exact Nat.le_add_right sz _
    · simp only [ite_true]
      exact Nat.le_refl sz
  · simp only [ite_true]
    exact Nat.le_refl sz

theorem computeUnionLayout_field_le_size (repr : ReprOptions) (fields : List FieldSpec)
    {f : FieldSpec} (hf : f ∈ fields) :
    f.size ≤ (computeUnionLayout repr fields).size := by
  unfold computeUnionLayout
  exact Nat.le_trans (foldUnionFields_size_ge_field fields 1 0 _ hf) (alignTo_ge _ _)

theorem overaligned_union_demotes_to_memory
    (repr : ReprOptions) (f : FieldSpec)
    (h_non_zst : (f.size == 0) = false)
    (h_over : (f.platformScalarAlign ==
      (let rawAlign := Nat.max 1 f.align
       let packed := match repr.pack with | some p => Nat.min rawAlign p | none => rawAlign
       match repr.reprAlign with | some ra => Nat.max packed ra | none => packed)) = false)
    (h_scalar : ∃ s, f.backendRepr = .scalar s) :
    (computeUnionLayout repr [f]).backendRepr = .memory := by
  rcases h_scalar with ⟨s, hs⟩
  have hne : (f.size != 0) = true := by
    simp [bne, h_non_zst]
  unfold computeUnionLayout
  simp only [foldUnionFields, h_non_zst, Bool.false_eq_true, ite_false, hs,
             BackendRepr.toUnion, List.find?, hne]
  cases hinh : repr.inhibitsUnionAbiOpt
  · simp [h_over]
  · simp

theorem reprC_union_demotes_to_memory (repr : ReprOptions) (fields : List FieldSpec)
    (hc : repr.isC = true) :
    (computeUnionLayout repr fields).backendRepr = .memory := by
  unfold computeUnionLayout
  have hinh : repr.inhibitsUnionAbiOpt = true := hc
  have hnone : (foldUnionFields fields 1 0 none).2.2 = none := by
    generalize 1 = al
    generalize 0 = sz
    induction fields generalizing al sz with
    | nil => rfl
    | cons f rest ih =>
      simp only [foldUnionFields]
      cases hz : (f.size == 0)
      · simp only [Bool.false_eq_true, ite_false]
        exact ih _ _
      · simp only [ite_true]
        exact ih _ _
  simp [hinh, hnone]

/-! ## Section 4: Top-Level Validity, Typed Projections, Data-Range Copy, and Register Call Passing -/

inductive UbError where
  | invalidBufferLength
  | illFormedByte
  | fieldNotInUnion
  | invalidFieldValue
  | callUbPoison
  deriving DecidableEq, Repr

/-- Top-level union validity (`ValidityVisitor::visit_union`):
imposes ZERO field-level `bytePred` checks! Any byte buffer of exact length
`u.size` satisfying byte well-formedness (`val < 256` on `.bits`, arbitrary `.uninit`)
is a valid union value. -/
def validUnionValue (u : ComputedLayout) (buf : ByteBuffer) : Prop :=
  buf.length = u.size ∧ BufferWF buf = true

/-- Mirrors `copy_op_no_validate` + `ValidityVisitor::visit_union`:
copies bytes at offsets flagged by `u.dataMask` verbatim (preserving initialized
bits, provenance, and uninit), and resets pure union padding bytes (`dataMask[i] = false`)
to `.uninit`. -/
def copyUnionWithDataRangeAux : List Bool → ByteBuffer → ByteBuffer
  | _, [] => []
  | [], bs => bs.map (fun _ => AbstractByte.uninit)
  | true :: ms, b :: bs => b :: copyUnionWithDataRangeAux ms bs
  | false :: ms, _ :: bs => AbstractByte.uninit :: copyUnionWithDataRangeAux ms bs

def copyUnionWithDataRange (u : ComputedLayout) (buf : ByteBuffer) : ByteBuffer :=
  copyUnionWithDataRangeAux u.dataMask buf

theorem copyUnionWithDataRangeAux_length (m : List Bool) (bs : ByteBuffer) :
    (copyUnionWithDataRangeAux m bs).length = bs.length := by
  induction m generalizing bs with
  | nil =>
    cases bs <;> simp [copyUnionWithDataRangeAux]
  | cons flag ms ih =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      cases flag <;> simp [copyUnionWithDataRangeAux, ih]

private theorem bufferWF_map_uninit (bs : ByteBuffer) :
    BufferWF (bs.map (fun _ => AbstractByte.uninit)) = true := by
  induction bs with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.map_cons, BufferWF, ByteWF, Bool.true_and]
    exact ih

theorem copyUnionWithDataRangeAux_wf (m : List Bool) (bs : ByteBuffer)
    (h : BufferWF bs = true) :
    BufferWF (copyUnionWithDataRangeAux m bs) = true := by
  induction m generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons _ rest =>
      simp only [copyUnionWithDataRangeAux, List.map_cons, BufferWF, ByteWF, Bool.true_and]
      exact bufferWF_map_uninit rest
  | cons flag ms ih =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      simp only [BufferWF, Bool.and_eq_true] at h
      cases flag
      · simp [copyUnionWithDataRangeAux, BufferWF, ByteWF, ih rest h.2]
      · simp [copyUnionWithDataRangeAux, BufferWF, h.1, ih rest h.2]

theorem copyUnionWithDataRange_preserves_valid (u : ComputedLayout) (buf : ByteBuffer)
    (h : validUnionValue u buf) :
    validUnionValue u (copyUnionWithDataRange u buf) := by
  exact ⟨by rw [copyUnionWithDataRange, copyUnionWithDataRangeAux_length]; exact h.1,
         copyUnionWithDataRangeAux_wf u.dataMask buf h.2⟩

private theorem nat_beq_refl (n : Nat) : (n == n) = true :=
  beq_iff_eq.mpr rfl

def hasFieldIdList : List FieldSpec → Nat → Bool
  | [], _ => false
  | g :: gs, fid => (g.fieldId == fid) || hasFieldIdList gs fid

theorem hasFieldIdList_of_mem {fs : List FieldSpec} {f : FieldSpec} (hf : f ∈ fs) :
    hasFieldIdList fs f.fieldId = true := by
  induction fs with
  | nil => cases hf
  | cons g gs ih =>
    cases hf with
    | head =>
      simp only [hasFieldIdList, nat_beq_refl, Bool.true_or]
    | tail _ hm =>
      simp only [hasFieldIdList, ih hm, Bool.or_true]

def hasFieldId (u : ComputedLayout) (f : FieldSpec) : Bool :=
  hasFieldIdList u.fields f.fieldId

theorem hasFieldId_of_mem {u : ComputedLayout} {f : FieldSpec} (hf : f ∈ u.fields) :
    hasFieldId u f = true :=
  hasFieldIdList_of_mem hf

/-- Typed read projection (`u.f`): checks field membership, extracts `[0..f.size)`,
and validates `f.bytePred` on that slice, failing with `.error .invalidFieldValue`
whenever the bytes violate `f`'s type-level invariant (including `.uninit`, `0` for
`NonZeroU64`, or any bytes for `!`/`Infallible`). -/
def readUnionField (u : ComputedLayout) (f : FieldSpec) (buf : ByteBuffer) :
    Except UbError ByteBuffer :=
  if !(hasFieldId u f) then .error .fieldNotInUnion
  else if !(buf.length == u.size && BufferWF buf) then .error .invalidBufferLength
  else
    let slice := buf.take f.size
    if f.bytePred slice then .ok slice
    else .error .invalidFieldValue

/-- Sub-object partial write (`u.f = newBytes`): validates `newBytes` against
`f.bytePred`, then splices `newBytes ++ buf.drop f.size` across `[0..f.size)`,
leaving all sibling bytes `[f.size..u.size)` untouched! -/
def writeUnionField (u : ComputedLayout) (f : FieldSpec)
    (newBytes : ByteBuffer) (buf : ByteBuffer) : Except UbError ByteBuffer :=
  if !(hasFieldId u f) then .error .fieldNotInUnion
  else if !(buf.length == u.size && BufferWF buf) then .error .invalidBufferLength
  else if !(newBytes.length == f.size && BufferWF newBytes) then .error .invalidBufferLength
  else if !(f.bytePred newBytes) then .error .invalidFieldValue
  else .ok (newBytes ++ buf.drop f.size)

/-- Call-boundary LLVM IR attributes emitted for a `ScalarAbi`
(`compiler/rustc_ty_utils/src/abi.rs:318-333`, `codegen_llvm/src/abi.rs:504-520`). -/
structure ArgPassAttrs where
  hasNoUndef : Bool
  hasRangeCheck : Bool
  deriving DecidableEq, Repr

def argAttrsForScalar : ScalarAbi → ArgPassAttrs
  | .initialized _ _ _ _ hasNiche => { hasNoUndef := true, hasRangeCheck := hasNiche }
  | .unionScalar _ _ => { hasNoUndef := false, hasRangeCheck := false }

def argAttrsForRepr : BackendRepr → ArgPassAttrs
  | .scalar s => argAttrsForScalar s
  | _ => { hasNoUndef := false, hasRangeCheck := false }

inductive CallOutcome where
  | ok (val : ByteBuffer)
  | callUbPoison
  deriving DecidableEq, Repr

/-- Operational semantics of passing a scalar value across an LLVM call boundary
with `ArgPassAttrs` and scalar range predicate `rangePred`:
- If `hasNoUndef` is set and `buf` contains any `.uninit`, LLVM passes `poison` -> UB.
- If `hasRangeCheck` is set and `rangePred buf = false`, LLVM `!range` / `range(...)` -> UB.
- Otherwise the exact abstract byte buffer is transmitted intact. -/
def evalRegisterCall (attrs : ArgPassAttrs) (rangePred : ByteBuffer → Bool)
    (buf : ByteBuffer) : CallOutcome :=
  if attrs.hasNoUndef && bufHasUninit buf then .callUbPoison
  else if attrs.hasRangeCheck && !(rangePred buf) then .callUbPoison
  else .ok buf

theorem argAttrsForScalar_toUnion (s : ScalarAbi) :
    argAttrsForScalar s.toUnion = { hasNoUndef := false, hasRangeCheck := false } := by
  cases s <;> rfl

/-- **Theorem Family 1 (Soundness of `toUnionRepr` Register Passing)**:
Every scalar repr produced by `computeUnionLayout` erases `noundef` and `!range`
metadata, so direct register passing transmits ANY valid union byte buffer
(including `.uninit` bytes and out-of-niche values like `0` for `NonZeroU64`)
with zero call-boundary poison/UB. -/
theorem computeUnionLayout_omits_noundef_and_range
    (repr : ReprOptions) (fields : List FieldSpec) :
    argAttrsForRepr (computeUnionLayout repr fields).backendRepr =
      { hasNoUndef := false, hasRangeCheck := false } := by
  have hall := computeUnionLayout_allScalarsUnion repr fields
  cases hbr : (computeUnionLayout repr fields).backendRepr with
  | scalar s =>
    rw [hbr] at hall
    cases s with
    | initialized => cases hall
    | unionScalar _ _ => rfl
  | scalarPair _ _ _ => rfl
  | simdVector _ _ => rfl
  | memory => rfl

theorem toUnionRepr_register_call_sound
    (repr : ReprOptions) (fields : List FieldSpec)
    (rangePred : ByteBuffer → Bool) (buf : ByteBuffer)
    (_hvalid : validUnionValue (computeUnionLayout repr fields) buf) :
    evalRegisterCall (argAttrsForRepr (computeUnionLayout repr fields).backendRepr)
      rangePred buf = .ok buf := by
  rw [computeUnionLayout_omits_noundef_and_range]
  rfl

/-! ## Section 5: Constructive List-Slice Lemmas & Exact Partial Overwrite Frame Law -/

private theorem length_drop_add (n : Nat) (xs : ByteBuffer) (hle : n ≤ xs.length) :
    n + (xs.drop n).length = xs.length := by
  induction n generalizing xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => cases hle
    | cons _ rest =>
      simp only [List.drop_succ_cons, List.length_cons] at hle ⊢
      have hle' : k ≤ rest.length := Nat.le_of_succ_le_succ hle
      rw [Nat.succ_add, ih rest hle']

private theorem take_append_eq_left {a b : ByteBuffer} :
    (a ++ b).take a.length = a := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem drop_append_eq_right {a b : ByteBuffer} :
    (a ++ b).drop a.length = b := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem getElem?_append_left_of_lt {a b : ByteBuffer} {i : Nat}
    (hlt : i < a.length) :
    (a ++ b)[i]? = a[i]? := by
  induction a generalizing i with
  | nil => cases hlt
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ hlt)

private theorem getElem?_append_right_of_ge {a b : ByteBuffer} {i : Nat}
    (hge : a.length ≤ i) :
    (a ++ b)[i]? = b[i - a.length]? := by
  induction a generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => cases hge
    | succ k =>
      simp only [List.cons_append, List.getElem?_cons_succ, List.length_cons,
                 Nat.succ_sub_succ_eq_sub]
      exact ih (Nat.le_of_succ_le_succ hge)

private theorem getElem?_drop_eq (n i : Nat) (xs : ByteBuffer) :
    (xs.drop n)[i]? = xs[n + i]? := by
  induction n generalizing xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons _ rest =>
      simp only [List.drop_succ_cons, Nat.succ_add, List.getElem?_cons_succ]
      exact ih rest

private theorem add_sub_cancel_ge {n i : Nat} (hle : n ≤ i) :
    n + (i - n) = i := by
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel hle

/-- Invariant asserting that every field in `u.fields` fits inside `u.size`. -/
def LayoutFieldsFit (u : ComputedLayout) : Prop :=
  ∀ f ∈ u.fields, f.size ≤ u.size

theorem computeUnionLayout_fieldsFit (repr : ReprOptions) (fields : List FieldSpec) :
    LayoutFieldsFit (computeUnionLayout repr fields) := by
  intro f hf
  exact computeUnionLayout_field_le_size repr fields hf

/-- **Theorem Family 2a (Length & BufferWF Preservation)**:
A successful `writeUnionField` preserves `buf.length = u.size` and `BufferWF`,
returning a valid union value. -/
theorem writeUnionField_preserves_valid
    (u : ComputedLayout) (f : FieldSpec)
    (newBytes buf out : ByteBuffer)
    (hfit : f.size ≤ u.size)
    (hw : writeUnionField u f newBytes buf = .ok out) :
    validUnionValue u out := by
  unfold writeUnionField at hw
  cases hfid : hasFieldId u f
  · simp [hfid] at hw
  · simp only [hfid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
    cases hbl : (buf.length == u.size) <;> cases hbw : BufferWF buf
    · simp [hbl, hbw] at hw
    · simp [hbl, hbw] at hw
    · simp [hbl, hbw] at hw
    · simp only [hbl, hbw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      cases hnl : (newBytes.length == f.size) <;> cases hnw : BufferWF newBytes
      · simp [hnl, hnw] at hw
      · simp [hnl, hnw] at hw
      · simp [hnl, hnw] at hw
      · simp only [hnl, hnw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
        cases hpred : f.bytePred newBytes
        · simp [hpred] at hw
        · simp only [hpred, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
          injection hw with hout
          subst hout
          have hbuflen : buf.length = u.size := beq_iff_eq.mp hbl
          have hnewlen : newBytes.length = f.size := beq_iff_eq.mp hnl
          have hf_le_buf : f.size ≤ buf.length := by rw [hbuflen]; exact hfit
          constructor
          · rw [List.length_append, hnewlen, length_drop_add f.size buf hf_le_buf, hbuflen]
          · exact bufferWF_append hnw (bufferWF_drop f.size buf hbw)

/-- **Theorem Family 2b (Get-Put Soundness)**:
Reading back the written field `f` immediately after `writeUnionField` returns
`.ok newBytes`. -/
theorem writeUnionField_reads_back
    (u : ComputedLayout) (f : FieldSpec)
    (newBytes buf out : ByteBuffer)
    (hfit : f.size ≤ u.size)
    (hw : writeUnionField u f newBytes buf = .ok out) :
    readUnionField u f out = .ok newBytes := by
  have hvalid := writeUnionField_preserves_valid u f newBytes buf out hfit hw
  unfold writeUnionField at hw
  cases hfid : hasFieldId u f
  · simp [hfid] at hw
  · simp only [hfid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
    cases hbl : (buf.length == u.size) <;> cases hbw : BufferWF buf
    · simp [hbl, hbw] at hw
    · simp [hbl, hbw] at hw
    · simp [hbl, hbw] at hw
    · simp only [hbl, hbw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      cases hnl : (newBytes.length == f.size) <;> cases hnw : BufferWF newBytes
      · simp [hnl, hnw] at hw
      · simp [hnl, hnw] at hw
      · simp [hnl, hnw] at hw
      · simp only [hnl, hnw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
        cases hpred : f.bytePred newBytes
        · simp [hpred] at hw
        · simp only [hpred, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
          injection hw with hout
          subst hout
          have hnewlen : newBytes.length = f.size := beq_iff_eq.mp hnl
          have htake : (newBytes ++ buf.drop f.size).take f.size = newBytes := by
            rw [← hnewlen]
            exact take_append_eq_left
          have houtlen : ((newBytes ++ buf.drop f.size).length == u.size) = true :=
            beq_iff_eq.mpr hvalid.1
          unfold readUnionField
          simp only [hfid, houtlen, hvalid.2, Bool.and_self, Bool.not_true, Bool.false_eq_true,
                     ite_false, htake, hpred, ite_true]

/-- **Theorem Family 2c (Exact Byte-Slice Frame Law)**:
Overwriting field `f` updates ONLY `[0..f.size)` and preserves the entire upper
byte slice `[f.size..u.size)` (`out.drop f.size = buf.drop f.size`) as well as
every individual byte (bits, provenance, and `.uninit`) at index `i ≥ f.size`. -/
theorem writeUnionField_preserves_upper_slice
    (u : ComputedLayout) (f : FieldSpec)
    (newBytes buf out : ByteBuffer)
    (hw : writeUnionField u f newBytes buf = .ok out) :
    out.drop f.size = buf.drop f.size ∧
    (∀ i : Nat, f.size ≤ i → out[i]? = buf[i]?) ∧
    (∀ i : Nat, i < f.size → out[i]? = newBytes[i]?) := by
  unfold writeUnionField at hw
  cases hfid : hasFieldId u f
  · simp [hfid] at hw
  · simp only [hfid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
    cases hbl : (buf.length == u.size) <;> cases hbw : BufferWF buf
    · simp [hbl, hbw] at hw
    · simp [hbl, hbw] at hw
    · simp [hbl, hbw] at hw
    · simp only [hbl, hbw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      cases hnl : (newBytes.length == f.size) <;> cases hnw : BufferWF newBytes
      · simp [hnl, hnw] at hw
      · simp [hnl, hnw] at hw
      · simp [hnl, hnw] at hw
      · simp only [hnl, hnw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
        cases hpred : f.bytePred newBytes
        · simp [hpred] at hw
        · simp only [hpred, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
          injection hw with hout
          subst hout
          have hnewlen : newBytes.length = f.size := beq_iff_eq.mp hnl
          refine ⟨?_, ?_, ?_⟩
          · rw [← hnewlen]
            exact drop_append_eq_right
          · intro i hge
            have hge' : newBytes.length ≤ i := by rw [hnewlen]; exact hge
            rw [getElem?_append_right_of_ge hge', getElem?_drop_eq, hnewlen, add_sub_cancel_ge hge]
          · intro i hlt
            have hlt' : i < newBytes.length := by rw [hnewlen]; exact hlt
            exact getElem?_append_left_of_lt hlt'

/-- Little-endian `u32` byte decoding on concrete 4-byte initialized slices. -/
def decodeU32LE : ByteBuffer → Option Nat
  | [.bits b0 none, .bits b1 none, .bits b2 none, .bits b3 none] =>
    some (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)
  | _ => none

def mkU8LoField : FieldSpec := {
  fieldId := 1
  size := 1
  align := 1
  backendRepr := .scalar (.initialized (.int false) 1 0 255 false)
  platformScalarAlign := 1
  largestNiche := none
  uninhabited := false
  bytePred := fun bs => match bs with | [.bits v none] => decide (v < 256) | _ => false
  dataMask := [true]
}

def mkU32FullField : FieldSpec := {
  fieldId := 0
  size := 4
  align := 4
  backendRepr := .scalar (.initialized (.int false) 4 0 4294967295 false)
  platformScalarAlign := 4
  largestNiche := none
  uninhabited := false
  bytePred := fun bs => match decodeU32LE bs with | some _ => true | none => false
  dataMask := [true, true, true, true]
}

def u32LoUnionLayout : ComputedLayout :=
  computeUnionLayout { isC := true, isTransparent := false, pack := none, reprAlign := none }
    [mkU32FullField, mkU8LoField]

/-- Exact frame law specialized to `U32Lo { full_u32: u32, lo_u8: u8 }`:
writing `lo_u8 = b0'` overwrites only byte 0 while preserving bytes `[1, 2, 3]`
and updating `readUnionField full_u32` deterministically to
`b0' + 256 * b1 + 65536 * b2 + 16777216 * b3`. -/
theorem u32_writeLo_preserves_upper_bytes
    (b0 b1 b2 b3 b0' : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) (h0' : b0' < 256) :
    writeUnionField u32LoUnionLayout mkU8LoField [.bits b0' none]
      [.bits b0 none, .bits b1 none, .bits b2 none, .bits b3 none] =
      .ok [.bits b0' none, .bits b1 none, .bits b2 none, .bits b3 none] ∧
    decodeU32LE [.bits b0' none, .bits b1 none, .bits b2 none, .bits b3 none] =
      some (b0' + 256 * b1 + 65536 * b2 + 16777216 * b3) := by
  have hb0 : decide (b0 < 256) = true := decide_eq_true h0
  have hb1 : decide (b1 < 256) = true := decide_eq_true h1
  have hb2 : decide (b2 < 256) = true := decide_eq_true h2
  have hb3 : decide (b3 < 256) = true := decide_eq_true h3
  have hb0' : decide (b0' < 256) = true := decide_eq_true h0'
  constructor
  · dsimp only [writeUnionField, hasFieldId, hasFieldIdList, u32LoUnionLayout, computeUnionLayout,
                foldUnionFields, alignTo, mkU32FullField, mkU8LoField,
                ReprOptions.inhibitsUnionAbiOpt, BufferWF, ByteWF, List.drop]
    simp only [Bool.and_true, hb0, hb1, hb2, hb3, hb0']
    rfl
  · rfl

theorem u32_0x11223344_write_0x99_eq_0x11223399 :
    writeUnionField u32LoUnionLayout mkU8LoField [.bits 0x99 none]
      [.bits 0x44 none, .bits 0x33 none, .bits 0x22 none, .bits 0x11 none] =
      .ok [.bits 0x99 none, .bits 0x33 none, .bits 0x22 none, .bits 0x11 none] ∧
    decodeU32LE [.bits 0x99 none, .bits 0x33 none, .bits 0x22 none, .bits 0x11 none] =
      some 0x11223399 :=
  ⟨rfl, rfl⟩

/-! ## Section 6: Universal Inhabitedness, `Option` Niche Erasure & Counterexamples -/

/-- **Theorem Family 3a (Universal Inhabitedness of `UnionLayout`)**:
Regardless of `ReprOptions` and `fields`—even if EVERY field has
`uninhabited = true` and `bytePred = fun _ => false`—`computeUnionLayout` sets
`uninhabited = false`, `largestNiche = none`, and the all-`.uninit` buffer of
length `u.size` satisfies `validUnionValue`. -/
theorem unionLayout_universally_inhabited
    (repr : ReprOptions) (fields : List FieldSpec) :
    let u := computeUnionLayout repr fields
    u.uninhabited = false ∧
    u.largestNiche = none ∧
    validUnionValue u (List.replicate u.size AbstractByte.uninit) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact List.length_replicate
  · exact bufferWF_replicate_uninit _

/-- Reading any field of a union whose fields all reject every byte buffer
always fails with `.error .invalidFieldValue` (after passing length/WF checks),
confirming why value construction is valid while field projection is UB. -/
theorem uninhabited_field_read_fails_on_valid_union
    (repr : ReprOptions) (fields : List FieldSpec) (f : FieldSpec)
    (hf : f ∈ fields)
    (h_uninhab : ∀ bs, f.bytePred bs = false) :
    readUnionField (computeUnionLayout repr fields) f
      (List.replicate (computeUnionLayout repr fields).size AbstractByte.uninit) =
      .error .invalidFieldValue := by
  unfold readUnionField
  have hfid : hasFieldId (computeUnionLayout repr fields) f = true :=
    hasFieldId_of_mem (u := computeUnionLayout repr fields) hf
  have hlen : ((List.replicate (computeUnionLayout repr fields).size AbstractByte.uninit).length ==
      (computeUnionLayout repr fields).size) = true := beq_iff_eq.mpr List.length_replicate
  have hwf : BufferWF (List.replicate (computeUnionLayout repr fields).size AbstractByte.uninit) = true :=
    bufferWF_replicate_uninit _
  simp only [hfid, hlen, hwf, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false,
             h_uninhab]

/-- Models `Option<T>` size selection in `rustc_abi`:
- Uninhabited inner type `T` (`Infallible` / `!`) -> `Option<T>` is a single
  inhabited ZST (`None`), so `size = 0`.
- Inhabited `T` with `largestNiche = some _` -> `Option<T>` reuses `T`'s niche
  (`size = T.size`).
- Inhabited `T` with `largestNiche = none` -> `Option<T>` requires an external tag
  (`size = Nat.max (T.size + T.align) 1`, yielding `1 B` for ZSTs and `16 B` for
  8-byte aligned types). -/
def optionSizeOf (inner : ComputedLayout) : Nat :=
  if inner.uninhabited then 0
  else match inner.largestNiche with
    | some _ => inner.size
    | none => Nat.max (inner.size + inner.align) 1

def infallibleField : FieldSpec := {
  fieldId := 0
  size := 0
  align := 1
  backendRepr := .memory
  platformScalarAlign := 1
  largestNiche := none
  uninhabited := true
  bytePred := fun _ => false
  dataMask := []
}

def infallibleStructLayout : ComputedLayout :=
  computeTransparentStructLayout infallibleField

def neverUnionLayout : ComputedLayout :=
  computeUnionLayout { isC := false, isTransparent := false, pack := none, reprAlign := none }
    [infallibleField]

def nonZeroU64Field : FieldSpec := {
  fieldId := 0
  size := 8
  align := 8
  backendRepr := .scalar (.initialized (.int false) 8 1 18446744073709551615 true)
  platformScalarAlign := 8
  largestNiche := some 1
  uninhabited := false
  bytePred := fun bs =>
    match bs with
    | [.bits b0 none, .bits b1 none, .bits b2 none, .bits b3 none,
       .bits b4 none, .bits b5 none, .bits b6 none, .bits b7 none] =>
      b0 != 0 || b1 != 0 || b2 != 0 || b3 != 0 ||
      b4 != 0 || b5 != 0 || b6 != 0 || b7 != 0
    | _ => false
  dataMask := [true, true, true, true, true, true, true, true]
}

def zstUnitField : FieldSpec := {
  fieldId := 1
  size := 0
  align := 1
  backendRepr := .memory
  platformScalarAlign := 1
  largestNiche := none
  uninhabited := false
  bytePred := fun bs => bs.isEmpty
  dataMask := []
}

def plainWrapStructLayout : ComputedLayout :=
  computeTransparentStructLayout nonZeroU64Field

def twoNonZeroUnionLayout : ComputedLayout :=
  computeUnionLayout { isC := false, isTransparent := false, pack := none, reprAlign := none }
    [nonZeroU64Field, { nonZeroU64Field with fieldId := 1 }]

def transNonZeroUnionLayout : ComputedLayout :=
  computeUnionLayout { isC := false, isTransparent := true, pack := none, reprAlign := none }
    [nonZeroU64Field, zstUnitField]

/-- **Theorem Family 3b (`Option` Size Separation)**:
`Option<Infallible>` has size `0`, whereas `Option<NeverUnion>` has size `1 > 0`
because `NeverUnion` is inhabited with no niche; similarly `Option<PlainWrap>`
has size `8` whereas both `Option<TwoNonZero>` and `Option<TransNonZero>` have
size `16`. -/
theorem option_infallible_size_zero_vs_option_neverUnion_size_one :
    optionSizeOf infallibleStructLayout = 0 ∧
    optionSizeOf neverUnionLayout = 1 ∧
    0 < optionSizeOf neverUnionLayout ∧
    optionSizeOf plainWrapStructLayout = 8 ∧
    optionSizeOf twoNonZeroUnionLayout = 16 ∧
    optionSizeOf transNonZeroUnionLayout = 16 := by
  decide

/-! ## Section 7: Three Constructive Counterexamples Against Naïve Models -/

/-- Hypothetical BUGGY niche-intersection model: computes union niche by
taking the first field's niche (as in `TwoNonZero { a: NonZeroU64, b: NonZeroU64 }`)
and enforces that niche on top-level union validity instead of `largestNiche := none`. -/
def buggyIntersectedUnionValid (buf : ByteBuffer) : Bool :=
  buf.length == 8 && nonZeroU64Field.bytePred buf

/-- **Counterexample 1**: Intersecting field niches (`NonZeroU64 ∩ NonZeroU64`)
on `TwoNonZero` (`largestNiche := none` in real `rustc`) unsoundly rejects BOTH
all-`.uninit` (`MaybeUninit::<TwoNonZero>::uninit()`) and all-zero (`0x00..00`)
buffers that are valid union values in real `rustc` and Miri (`miri_rc = 0`). -/
theorem ce1_intersecting_field_niches_on_two_nonzero_union_unsoundly_rejects_uninit_bytes :
    let u := twoNonZeroUnionLayout
    let uninitBuf := List.replicate 8 AbstractByte.uninit
    let zeroBuf := List.replicate 8 (AbstractByte.bits 0 none)
    u.largestNiche = none ∧
    validUnionValue u uninitBuf ∧
    validUnionValue u zeroBuf ∧
    buggyIntersectedUnionValid uninitBuf = false ∧
    buggyIntersectedUnionValid zeroBuf = false ∧
    readUnionField u nonZeroU64Field zeroBuf = .error .invalidFieldValue := by
  refine ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- **Counterexample 2**: Emitting LLVM `noundef` (and `!range`)—as happens for
`#[repr(transparent)] struct PlainWrap(NonZeroU64)` (`Scalar::Initialized`)—on
`#[repr(transparent)] union TransNonZero` or `TwoNonZero` triggers immediate
LLVM call-boundary poison/UB when passing an uninitialized or all-zero union
value, whereas `computeUnionLayout` emits `Scalar::Union` (`hasNoUndef := false,
hasRangeCheck := false`) and returns `.ok` safely. -/
theorem ce2_emitting_llvm_noundef_on_scalar_union_causes_call_boundary_poison_ub :
    let uninitBuf := List.replicate 8 AbstractByte.uninit
    let zeroBuf := List.replicate 8 (AbstractByte.bits 0 none)
    let buggyAttrs := argAttrsForRepr plainWrapStructLayout.backendRepr
    let actualAttrs := argAttrsForRepr transNonZeroUnionLayout.backendRepr
    buggyAttrs = { hasNoUndef := true, hasRangeCheck := true } ∧
    actualAttrs = { hasNoUndef := false, hasRangeCheck := false } ∧
    evalRegisterCall buggyAttrs nonZeroU64Field.bytePred uninitBuf = .callUbPoison ∧
    evalRegisterCall buggyAttrs nonZeroU64Field.bytePred zeroBuf = .callUbPoison ∧
    evalRegisterCall actualAttrs nonZeroU64Field.bytePred uninitBuf = .ok uninitBuf ∧
    evalRegisterCall actualAttrs nonZeroU64Field.bytePred zeroBuf = .ok zeroBuf := by
  decide

/-- Hypothetical BUGGY `assume_init` / layout checker that propagates field
uninhabitedness through `union`: returns `.ubUnreachable` whenever `u.uninhabited`
or `optionSizeOf u = 0`. -/
inductive AssumeInitOutcome where
  | ok (buf : ByteBuffer)
  | ubUnreachable
  deriving DecidableEq, Repr

def evalAssumeInitWithInhabitedFlag (u : ComputedLayout) (isUninhab : Bool)
    (buf : ByteBuffer) : AssumeInitOutcome :=
  if isUninhab then .ubUnreachable
  else if buf.length == u.size then .ok buf
  else .ubUnreachable

/-- **Counterexample 3**: Treating `union NeverUnion { f: Infallible }` as
uninhabited (propagating `Infallible.uninhabited = true`) miscompiles valid
`MaybeUninit::<NeverUnion>::uninit().assume_init()` into `.ubUnreachable` and
shrinks `Option<NeverUnion>` from `1` byte to `0` bytes (collapsing `Some(NeverUnion)`
and `None`), whereas `rustc` forces `neverUnionLayout.uninhabited = false` and
returns `.ok []` with `optionSizeOf neverUnionLayout = 1`. -/
theorem ce3_treating_never_field_union_as_uninhabited_miscompiles_valid_assume_init :
    neverUnionLayout.uninhabited = false ∧
    infallibleStructLayout.uninhabited = true ∧
    evalAssumeInitWithInhabitedFlag neverUnionLayout infallibleStructLayout.uninhabited [] = .ubUnreachable ∧
    evalAssumeInitWithInhabitedFlag neverUnionLayout neverUnionLayout.uninhabited [] = .ok [] ∧
    optionSizeOf infallibleStructLayout = 0 ∧
    optionSizeOf neverUnionLayout = 1 := by
  decide

end RustcUnionSemantics
