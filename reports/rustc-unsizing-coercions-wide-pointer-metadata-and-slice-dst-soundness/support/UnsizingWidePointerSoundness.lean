/-
  UnsizingWidePointerSoundness.lean

  Standalone Lean v4.34.1 mechanization of `rustc` unsizing coercions
  (`PointerCoercion::Unsize`, structural tail `Unsize`, `CoerceUnsized` wrapper
  projection), wide pointer metadata (`PtrMetadata`, slice lengths, and `dyn`
  vtable headers), MIR peephole / GVN metadata folding, and dynamic
  `size_of_val_raw` / `align_of_val_raw` layout soundness within `isize::MAX`.

  Discipline:
  - 0 `sorry`
  - 0 `Classical.choice`
  - 0 `omega`
  - 0 `bv_decide`
  - 0 `native_decide`
  - 0 `partial def`
  - 0 `._unsafe_rec` (every term-level definition is marked `noncomputable` and
    uses primitive structural recursion plus primitive `Bool` `match` elimination,
    preventing the Lean code generator from synthesizing partial `._unsafe_rec`
    helpers while preserving kernel definitional reduction).
-/

namespace UnsizingWidePointerSoundness

/-! ## 1. Pointer Metadata, Wide Pointers, and VTable Headers -/

/-- Runtime pointer metadata carried by a Rust reference or raw pointer:
    - `.thin` models unit metadata `()` on pointers to `Sized` (or `extern`) types.
    - `.sliceLen n` models element-count metadata `n : usize` on `[T]` / `str` tails.
    - `.vtable vtId` models `DynMetadata<dyn Trait>` pointing to compiler vtable `vtId`. -/
inductive PtrMeta where
  | thin
  | sliceLen (n : Nat)
  | vtable (vtId : Nat)

/-- Explicit structural equality on `PtrMeta` (avoiding `deriving` codegen helpers). -/
noncomputable def PtrMeta.beq : PtrMeta → PtrMeta → Bool
  | .thin, .thin => true
  | .sliceLen a, .sliceLen b => Nat.beq a b
  | .vtable a, .vtable b => Nat.beq a b
  | _, _ => false

theorem PtrMeta.beq_refl (m : PtrMeta) : PtrMeta.beq m m = true := by
  cases m with
  | thin => rfl
  | sliceLen _ => exact Nat.beq_refl _
  | vtable _ => exact Nat.beq_refl _

/-- A runtime pointer value pairing a byte address, allocation provenance ID,
    and thin/wide pointer metadata (`BackendRepr::Scalar` vs `ScalarPair`). -/
structure PtrVal where
  addr : Nat
  prov : Nat
  metadata : PtrMeta

/-- Compiler-emitted read-only vtable header (`COMMON_VTABLE_ENTRIES` slots 1 and 2,
    tagged with the erased existential trait identity `traitId` and concrete `implTyId`). -/
structure VTableHeader where
  size : Nat
  align : Nat
  traitId : Nat
  implTyId : Nat

/-- Read-only global vtable environment mapping `vtId` to its header. -/
abbrev VtEnv := Nat → Option VTableHeader

/-- Byte span `[base, base + bytes)` inside live allocation `prov`. -/
structure LiveAlloc where
  prov : Nat
  base : Nat
  bytes : Nat

/-- Whether byte range `[addr, addr + span)` lies within `alloc`. -/
noncomputable def SpanInBounds (alloc : LiveAlloc) (prov addr span : Nat) : Prop :=
  prov = alloc.prov ∧ alloc.base ≤ addr ∧ addr + span ≤ alloc.base + alloc.bytes

/-! ## 2. Alignment Rounding & Checked `isize::MAX` Arithmetic -/

/-- Pure `Bool` maximum via primitive `Bool.casesOn` (`match`) rather than `@ite`
    over `Decidable`. -/
noncomputable def fastMax (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => b
  | false => a

/-- Round `offset` up to the next multiple of `align` (matching `Size::align_to`). -/
noncomputable def alignUp (offset align : Nat) : Nat :=
  match Nat.beq align 0 with
  | true => offset
  | false =>
    let rem := offset % align
    match Nat.beq rem 0 with
    | true => offset
    | false => offset + (align - rem)

theorem le_alignUp (offset align : Nat) : offset ≤ alignUp offset align := by
  unfold alignUp
  cases Nat.beq align 0 with
  | true => exact Nat.le_refl offset
  | false =>
    dsimp only []
    cases Nat.beq (offset % align) 0 with
    | true => exact Nat.le_refl offset
    | false => exact Nat.le_add_right offset (align - offset % align)

/-- Checked multiplication bounded by `bound` (`isize::MAX`). -/
noncomputable def checkedMulLe (a b bound : Nat) : Option Nat :=
  let prod := a * b
  match Nat.ble prod bound with
  | true => some prod
  | false => none

/-- Checked addition bounded by `bound` (`isize::MAX`). -/
noncomputable def checkedAddLe (a b bound : Nat) : Option Nat :=
  let sum := a + b
  match Nat.ble sum bound with
  | true => some sum
  | false => none

theorem checkedMulLe_sound {a b bound res : Nat}
    (h : checkedMulLe a b bound = some res) :
    res = a * b ∧ res ≤ bound := by
  unfold checkedMulLe at h
  dsimp only [] at h
  cases hble : Nat.ble (a * b) bound with
  | false =>
    rw [hble] at h
    cases h
  | true =>
    rw [hble] at h
    injection h with hres
    exact ⟨hres.symm, hres ▸ Nat.le_of_ble_eq_true hble⟩

theorem checkedAddLe_sound {a b bound res : Nat}
    (h : checkedAddLe a b bound = some res) :
    res = a + b ∧ res ≤ bound := by
  unfold checkedAddLe at h
  dsimp only [] at h
  cases hble : Nat.ble (a + b) bound with
  | false =>
    rw [hble] at h
    cases h
  | true =>
    rw [hble] at h
    injection h with hres
    exact ⟨hres.symm, hres ▸ Nat.le_of_ble_eq_true hble⟩

/-! ## 3. Sized & Unsized Pointee Types and `StructKind::MaybeUnsized` Layout -/

/-- Statically `Sized` non-tail prefix field layout specification `(size, align)`
    (`compiler/rustc_abi/src/layout.rs:1265-1274` rejects any unsized non-tail field
    with `LayoutCalculatorError::UnexpectedUnsized`). -/
structure FieldSpec where
  size : Nat
  align : Nat

noncomputable def FieldSpec.abiAlign (f : FieldSpec) : Nat :=
  fastMax 1 f.align

noncomputable def FieldSpec.abiSize (f : FieldSpec) : Nat :=
  alignUp f.size f.abiAlign

/-- Indexed field entry `(declIdx, size, align)` used during `repr(Rust)` field sorting. -/
structure IndexedFieldLayout where
  declIdx : Nat
  size : Nat
  align : Nat

/-- Insert a field into a list sorted by descending alignment, preserving declaration
    order on alignment ties (mirroring `univariant_biased` `cmp::Reverse(alignment_group_key)`). -/
noncomputable def insertByDescAlign (x : IndexedFieldLayout) :
    List IndexedFieldLayout → List IndexedFieldLayout
  | [] => [x]
  | y :: ys =>
    match Nat.ble x.align y.align with
    | true => y :: insertByDescAlign x ys
    | false => x :: y :: ys

/-- Stable insertion sort of indexed field layouts by descending alignment. -/
noncomputable def sortFieldsDescAlign : List IndexedFieldLayout → List IndexedFieldLayout
  | [] => []
  | x :: xs => insertByDescAlign x (sortFieldsDescAlign xs)

/-- Assign sequential aligned byte offsets in memory order, returning
    `(placedPairs, endOffset, maxAlign)` where `placedPairs` maps `(declIdx, byteOffset)`. -/
noncomputable def placeOrderedFields :
    List IndexedFieldLayout → Nat → Nat → (List (Nat × Nat) × Nat × Nat)
  | [], curOff, curAlign => ([], curOff, curAlign)
  | f :: fs, curOff, curAlign =>
    let fOff := alignUp curOff f.align
    let nextOff := fOff + f.size
    let nextAlign := fastMax curAlign f.align
    let (rest, finalOff, finalAlign) := placeOrderedFields fs nextOff nextAlign
    ((f.declIdx, fOff) :: rest, finalOff, finalAlign)

/-- Look up the byte offset assigned to declaration field index `idx`. -/
noncomputable def lookupOffset (idx : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (k, v) :: rest =>
    match Nat.beq idx k with
    | true => some v
    | false => lookupOffset idx rest

/-- Build indexed layouts for `prefixFields` starting at declaration index `idx`. -/
noncomputable def indexFieldSpecs : Nat → List FieldSpec → List IndexedFieldLayout
  | _, [] => []
  | idx, f :: fs =>
    { declIdx := idx, size := f.abiSize, align := f.abiAlign } ::
      indexFieldSpecs (idx + 1) fs

/-- Computed prefix layout of the non-tail fields `0 .. fields.length - 2` under
    `StructKind::MaybeUnsized` (`compiler/rustc_abi/src/layout.rs:1112`:
    `let end = if let StructKind::MaybeUnsized = kind { fields.len() - 1 } else { fields.len() }`). -/
structure PrefixLayout where
  offsets : List (Nat × Nat)
  endOffset : Nat
  maxAlign : Nat

/-- Compute the `StructKind::MaybeUnsized` prefix layout strictly from `prefixFields`. -/
noncomputable def computePrefixLayout (prefixFields : List FieldSpec) : PrefixLayout :=
  let indexed := indexFieldSpecs 0 prefixFields
  let sorted := sortFieldsDescAlign indexed
  let (offs, endOff, maxAl) := placeOrderedFields sorted 0 1
  { offsets := offs, endOffset := endOff, maxAlign := maxAl }

/-- Combined alignment of a struct with `prefixFields` and tail alignment `tailAlign`. -/
noncomputable def structFullAlign (prefixFields : List FieldSpec) (tailAlign : Nat) : Nat :=
  fastMax (computePrefixLayout prefixFields).maxAlign tailAlign

/-- Combined byte size of a struct with `prefixFields`, `tailSize`, and `tailAlign`. -/
noncomputable def structFullSize (prefixFields : List FieldSpec)
    (tailSize tailAlign : Nat) : Nat :=
  let p := computePrefixLayout prefixFields
  let fullAlign := fastMax p.maxAlign tailAlign
  alignUp (alignUp p.endOffset tailAlign + tailSize) fullAlign

/-- First-order recursive pointee type algebra covering sized scalars, fixed-length arrays,
    unsized slices `[T]`, trait objects `dyn Trait`, and arbitrarily nested structs
    `struct S { prefixFields..., tail }` (`OuterWrap<DstWrap<[u32; 3]>>`, etc.). -/
inductive DstTy where
  | scalar (size : Nat) (align : Nat)
  | array (elem : DstTy) (len : Nat)
  | slice (elem : DstTy)
  | dynTrait (traitId : Nat)
  | structTy (adtId : Nat) (prefixFields : List FieldSpec) (tail : DstTy)

/-- Whether a `DstTy` is statically `Sized`. -/
noncomputable def isSized : DstTy → Bool
  | .scalar _ _ => true
  | .array elem _ => isSized elem
  | .slice _ => false
  | .dynTrait _ => false
  | .structTy _ _ tail => isSized tail

/-- Static ABI alignment of a `DstTy` (note `dynTrait` has static placeholder
    alignment `1` in `LayoutData::unit(cx, false)`, `rustc_ty_utils/src/layout.rs:516-518`). -/
noncomputable def staticAlign : DstTy → Nat
  | .scalar _ align => fastMax 1 align
  | .array elem _ => staticAlign elem
  | .slice elem => staticAlign elem
  | .dynTrait _ => 1
  | .structTy _ prefixFields tail => structFullAlign prefixFields (staticAlign tail)

/-- Static byte size of a `DstTy` (meaningful as total object size when `isSized ty = true`;
    for unsized types `slice` / `dynTrait`, static size is `0`, matching `LayoutData`). -/
noncomputable def staticSize : DstTy → Nat
  | .scalar size align => alignUp size (fastMax 1 align)
  | .array elem len => staticSize elem * len
  | .slice _ => 0
  | .dynTrait _ => 0
  | .structTy _ prefixFields tail =>
    structFullSize prefixFields (staticSize tail) (staticAlign tail)

/-- Field offset table of `structTy adtId prefixFields tail` under `StructKind::MaybeUnsized`:
    prefix fields `0 .. prefixFields.length - 1` use `computePrefixLayout prefixFields`,
    and the tail field at index `prefixFields.length` sits at
    `alignUp p.endOffset (staticAlign tail)`. -/
noncomputable def maybeUnsizedFieldOffset (prefixFields : List FieldSpec) (tail : DstTy)
    (fieldIdx : Nat) : Option Nat :=
  let p := computePrefixLayout prefixFields
  match Nat.blt fieldIdx prefixFields.length with
  | true => lookupOffset fieldIdx p.offsets
  | false =>
    match Nat.beq fieldIdx prefixFields.length with
    | true => some (alignUp p.endOffset (staticAlign tail))
    | false => none

/-- Counterfactual `StructKind::AlwaysSized` field offset table (`SizedWrap<T>` without `?Sized`),
    which sorts ALL fields including the last field `tail` (`end = fields.len()`). -/
noncomputable def alwaysSizedFieldOffset (prefixFields : List FieldSpec) (tail : DstTy)
    (fieldIdx : Nat) : Option Nat :=
  let tailSpec : FieldSpec := { size := staticSize tail, align := staticAlign tail }
  let allFields := indexFieldSpecs 0 (prefixFields ++ [tailSpec])
  let sorted := sortFieldsDescAlign allFields
  let (offs, _, _) := placeOrderedFields sorted 0 1
  lookupOffset fieldIdx offs

/-! ## 4. Theorem 1: Prefix-Field Offset & Address Invariance Under Tail Unsizing -/

/-- **Theorem 1a (Prefix-Field Offset Invariance Under `StructKind::MaybeUnsized`):**
    For any prefix field list `prefixFields`, any declaration index `i < prefixFields.length`,
    and ANY pair of tail types `tailSrc` and `tailDst` (whether `[T; N] -> [T]`,
    `Concrete -> dyn Trait`, or nested custom DSTs), `maybeUnsizedFieldOffset` assigns
    the exact same byte offset to field `i` before and after unsizing, even though
    `prefixFields` themselves undergo `repr(Rust)` alignment-descending reordering. -/
theorem prefix_field_offset_invariant_under_tail_unsizing
    (prefixFields : List FieldSpec) (tailSrc tailDst : DstTy) (i : Nat)
    (hi : i < prefixFields.length) :
    maybeUnsizedFieldOffset prefixFields tailSrc i =
      maybeUnsizedFieldOffset prefixFields tailDst i := by
  unfold maybeUnsizedFieldOffset
  have hblt : Nat.blt i prefixFields.length = true := Nat.blt_eq.mpr hi
  rw [hblt]

/-- Unsize a runtime pointer by replacing only its metadata (`unsize_into_ptr` / `unsize_ptr`),
    preserving both raw byte address `addr` and provenance `prov`. -/
noncomputable def unsizePtr (p : PtrVal) (newMeta : PtrMeta) : PtrVal :=
  { addr := p.addr, prov := p.prov, metadata := newMeta }

/-- Project a prefix field `(addr + off, prov, .thin)` off a struct pointer `p`. -/
noncomputable def projectPrefixField (prefixFields : List FieldSpec) (tail : DstTy)
    (p : PtrVal) (i : Nat) : Option PtrVal :=
  match maybeUnsizedFieldOffset prefixFields tail i with
  | some off => some { addr := p.addr + off, prov := p.prov, metadata := .thin }
  | none => none

/-- **Theorem 1b (Prefix-Field Pointer Projection Invariance Across `PointerCoercion::Unsize`):**
    Projecting any prefix field `i < prefixFields.length` through `unsizePtr p newMeta`
    at unsized type `structTy adtId prefixFields tailDst` yields the exact same thin
    pointer `(addr, prov, .thin)` as projecting field `i` from `p` at `tailSrc`. -/
theorem prefix_field_projection_commutes_with_unsize
    (prefixFields : List FieldSpec) (tailSrc tailDst : DstTy)
    (p : PtrVal) (newMeta : PtrMeta) (i : Nat) (hi : i < prefixFields.length) :
    projectPrefixField prefixFields tailDst (unsizePtr p newMeta) i =
      projectPrefixField prefixFields tailSrc p i := by
  unfold projectPrefixField unsizePtr
  dsimp only []
  rw [prefix_field_offset_invariant_under_tail_unsizing prefixFields tailDst tailSrc i hi]

/-- Path of nested tail steps followed by a prefix field index at that nesting depth. -/
inductive NestedPrefixPath where
  | herePrefix (fieldIdx : Nat)
  | intoTail (rest : NestedPrefixPath)

/-- Resolve a nested prefix field offset through arbitrarily nested `structTy` tails. -/
noncomputable def resolveNestedPrefixOffset : DstTy → NestedPrefixPath → Option Nat
  | .structTy _ prefixFields tail, .herePrefix i =>
    match Nat.blt i prefixFields.length with
    | true => maybeUnsizedFieldOffset prefixFields tail i
    | false => none
  | .structTy _ prefixFields tail, .intoTail rest =>
    let p := computePrefixLayout prefixFields
    match resolveNestedPrefixOffset tail rest with
    | some innerOff => some (alignUp p.endOffset (staticAlign tail) + innerOff)
    | none => none
  | _, _ => none

/-- Two-level nested slice-tail prefix invariance (`OuterWrap<DstWrap<[T; N]>>` vs
    `OuterWrap<DstWrap<[T]>>`): every prefix field at BOTH the outer and inner struct
    levels sits at the exact same byte offset from the outer pointer base! -/
theorem nested_slice_tail_prefix_offsets_invariant
    (outerId innerId : Nat) (outerPrefix innerPrefix : List FieldSpec)
    (elem : DstTy) (len : Nat) (path : NestedPrefixPath) :
    resolveNestedPrefixOffset
        (.structTy outerId outerPrefix (.structTy innerId innerPrefix (.array elem len))) path =
      resolveNestedPrefixOffset
        (.structTy outerId outerPrefix (.structTy innerId innerPrefix (.slice elem))) path := by
  cases path with
  | herePrefix i =>
    unfold resolveNestedPrefixOffset
    cases hblt : Nat.blt i outerPrefix.length with
    | false => rfl
    | true =>
      have hi : i < outerPrefix.length := Nat.blt_eq.mp hblt
      exact prefix_field_offset_invariant_under_tail_unsizing outerPrefix _ _ i hi
  | intoTail rest =>
    cases rest with
    | herePrefix j =>
      simp only [resolveNestedPrefixOffset, staticAlign]
      cases hblt : Nat.blt j innerPrefix.length with
      | false => rfl
      | true =>
        have hj : j < innerPrefix.length := Nat.blt_eq.mp hblt
        rw [prefix_field_offset_invariant_under_tail_unsizing innerPrefix _ _ j hj]
    | intoTail deeper =>
      cases deeper <;> rfl

/-! ## 5. `UnOp::PtrMetadata` Evaluation & MIR Peephole / GVN Folding Equivalence -/

/-- Runtime evaluation of `Rvalue::UnaryOp(UnOp::PtrMetadata, p)`
    (`compiler/rustc_const_eval/src/interpret/operator.rs:487-501`). -/
noncomputable def evalPtrMetadata (p : PtrVal) : PtrMeta :=
  p.metadata

/-- Lockstep tail peeling across nested structs (`TyCtxt::struct_lockstep_tails_raw`,
    `compiler/rustc_middle/src/ty/util.rs:341-373`). -/
noncomputable def structLockstepTails : DstTy → DstTy → (DstTy × DstTy)
  | .structTy idA prefA tailA => fun dst =>
    match dst with
    | .structTy idB prefB tailB =>
      match Nat.beq idA idB && Nat.beq prefA.length prefB.length with
      | true => structLockstepTails tailA tailB
      | false => (.structTy idA prefA tailA, .structTy idB prefB tailB)
    | _ => (.structTy idA prefA tailA, dst)
  | src => fun dst => (src, dst)

/-- Compute the metadata produced by `PointerCoercion::Unsize` from `srcTy` to `dstTy`
    given source metadata `oldMeta` and concrete vtable witness `vtWitness`
    (`compiler/rustc_codegen_ssa/src/base.rs:161-220` & `interpret/cast.rs:365-459`). -/
noncomputable def computeUnsizedMeta (srcTy dstTy : DstTy) (oldMeta : PtrMeta)
    (vtWitness : Option Nat) : Option PtrMeta :=
  match structLockstepTails srcTy dstTy with
  | (.array elemSrc len, .slice _) =>
    match isSized elemSrc with
    | true => some (.sliceLen len)
    | false => none
  | (leafSrc, .dynTrait _) =>
    match isSized leafSrc with
    | true =>
      match vtWitness with
      | some vtId => some (.vtable vtId)
      | none => none
    | false =>
      match leafSrc, oldMeta, vtWitness with
      | .dynTrait _, .vtable _, some newVtId => some (.vtable newVtId)
      | _, _, _ => none
  | _ => none

/-- MIR pointer expression tree covering `AggregateKind::RawPtr`, `PointerCoercion::Unsize`,
    metadata-preserving `CastKind::PtrToPtr`, and `&*p` / `&raw *p` reborrows. -/
inductive MirPtrExpr where
  | localPtr (val : PtrVal)
  | rawPtrAggregate (addr : Nat) (prov : Nat) (ptrMeta : PtrMeta)
  | reborrowDeref (inner : MirPtrExpr)
  | ptrToPtrSameMeta (inner : MirPtrExpr) (newAddr : Nat)
  | unsizeArrayToSlice (inner : MirPtrExpr) (elem : DstTy) (len : Nat)
  | unsizeLockstepStructSlice (inner : MirPtrExpr) (srcTy dstTy : DstTy)

/-- Big-step runtime evaluation of a `MirPtrExpr` to an optional `PtrVal`. -/
noncomputable def evalMirPtrExpr : MirPtrExpr → Option PtrVal
  | .localPtr v => some v
  | .rawPtrAggregate addr prov ptrMeta =>
    some { addr := addr, prov := prov, metadata := ptrMeta }
  | .reborrowDeref inner => evalMirPtrExpr inner
  | .ptrToPtrSameMeta inner newAddr =>
    match evalMirPtrExpr inner with
    | some p => some { addr := newAddr, prov := p.prov, metadata := p.metadata }
    | none => none
  | .unsizeArrayToSlice inner elem len =>
    match isSized elem with
    | true =>
      match evalMirPtrExpr inner with
      | some p => some (unsizePtr p (.sliceLen len))
      | none => none
    | false => none
  | .unsizeLockstepStructSlice inner srcTy dstTy =>
    match evalMirPtrExpr inner, computeUnsizedMeta srcTy dstTy .thin none with
    | some p, some m => some (unsizePtr p m)
    | _, _ => none

/-- Static MIR peephole / GVN folder for `UnOp::PtrMetadata(e)`:
    models both stock `GVN::simplify_unary` (`compiler/rustc_mir_transform/src/gvn.rs:1303-1371`,
    which peels `PtrToPtr` and `Deref` reborrows, folds `RawPtr { metadata } -> metadata`,
    and folds `[T; N] -> [T]` `Unsize` to `const N`) AND the generalized lockstep-tail
    rule for nested custom slice DSTs (`DstWrap<[T; N]> -> DstWrap<[T]>`). -/
noncomputable def foldPtrMetadataStatic : MirPtrExpr → Option PtrMeta
  | .localPtr _ => none
  | .rawPtrAggregate _ _ ptrMeta => some ptrMeta
  | .reborrowDeref inner => foldPtrMetadataStatic inner
  | .ptrToPtrSameMeta inner _ => foldPtrMetadataStatic inner
  | .unsizeArrayToSlice _ elem len =>
    match isSized elem with
    | true => some (.sliceLen len)
    | false => none
  | .unsizeLockstepStructSlice _ srcTy dstTy =>
    computeUnsizedMeta srcTy dstTy .thin none

/-- **Theorem 2 (`PtrMetadata` Peephole & GVN Folding Soundness):**
    Whenever `foldPtrMetadataStatic e = some foldedMeta` and `evalMirPtrExpr e = some runtimePtr`,
    runtime evaluation `evalPtrMetadata runtimePtr` produces the exact same metadata
    `foldedMeta` without reading memory or dereferencing `runtimePtr`. -/
theorem ptrMetadata_peephole_folding_sound :
    ∀ (e : MirPtrExpr) (foldedMeta : PtrMeta) (runtimePtr : PtrVal),
      foldPtrMetadataStatic e = some foldedMeta →
      evalMirPtrExpr e = some runtimePtr →
      evalPtrMetadata runtimePtr = foldedMeta := by
  intro e
  induction e with
  | localPtr _ =>
    intro foldedMeta runtimePtr hFold _
    cases hFold
  | rawPtrAggregate _ _ _ =>
    intro foldedMeta runtimePtr hFold hEval
    injection hFold with hMeta
    injection hEval with hPtr
    rw [← hPtr, ← hMeta]
    rfl
  | reborrowDeref inner ih =>
    intro foldedMeta runtimePtr hFold hEval
    exact ih foldedMeta runtimePtr hFold hEval
  | ptrToPtrSameMeta inner _ ih =>
    intro foldedMeta runtimePtr hFold hEval
    unfold foldPtrMetadataStatic at hFold
    unfold evalMirPtrExpr at hEval
    cases hInner : evalMirPtrExpr inner with
    | none =>
      rw [hInner] at hEval
      cases hEval
    | some p =>
      rw [hInner] at hEval
      injection hEval with hPtr
      have hSub := ih foldedMeta p hFold hInner
      rw [← hPtr]
      exact hSub
  | unsizeArrayToSlice inner elem _ _ =>
    intro foldedMeta runtimePtr hFold hEval
    unfold foldPtrMetadataStatic at hFold
    unfold evalMirPtrExpr at hEval
    cases hSz : isSized elem with
    | false =>
      rw [hSz] at hFold
      cases hFold
    | true =>
      rw [hSz] at hFold hEval
      cases hInner : evalMirPtrExpr inner with
      | none =>
        rw [hInner] at hEval
        cases hEval
      | some p =>
        rw [hInner] at hEval
        injection hFold with hMeta
        injection hEval with hPtr
        rw [← hPtr, ← hMeta]
        rfl
  | unsizeLockstepStructSlice inner _ _ _ =>
    intro foldedMeta runtimePtr hFold hEval
    unfold foldPtrMetadataStatic at hFold
    unfold evalMirPtrExpr at hEval
    rw [hFold] at hEval
    cases hInner : evalMirPtrExpr inner with
    | none =>
      rw [hInner] at hEval
      cases hEval
    | some p =>
      rw [hInner] at hEval
      injection hEval with hPtr
      rw [← hPtr]
      rfl

/-! ## 6. Dynamic `size_of_val_raw` / `align_of_val_raw` & In-Bounds Unsizing Soundness -/

/-- Dynamic layout computation matching `rustc_const_eval::interpret::EvalContext::size_and_align_from_meta`
    (`compiler/rustc_const_eval/src/interpret/eval_context.rs:432-518`):
    enforces slice multiplication overflow bounds (`InvalidMeta::SliceTooBig`),
    vtable trait/size validity, and whole-struct prefix + tail + alignment-padding
    `<= isizeMax` bounds (`InvalidMeta::TooBig`). -/
noncomputable def sizeAndAlignChecked (vtEnv : VtEnv) (isizeMax : Nat) :
    DstTy → PtrMeta → Option (Nat × Nat)
  | .scalar size align => fun ptrMeta =>
    match ptrMeta with
    | .thin =>
      let al := fastMax 1 align
      let sz := alignUp size al
      match Nat.ble sz isizeMax with
      | true => some (sz, al)
      | false => none
    | _ => none
  | .array elem len => fun ptrMeta =>
    match ptrMeta with
    | .thin =>
      match isSized elem with
      | true =>
        match checkedMulLe (staticSize elem) len isizeMax with
        | some sz => some (sz, staticAlign elem)
        | none => none
      | false => none
    | _ => none
  | .slice elem => fun ptrMeta =>
    match ptrMeta with
    | .sliceLen len =>
      match isSized elem with
      | true =>
        match checkedMulLe (staticSize elem) len isizeMax with
        | some sz => some (sz, staticAlign elem)
        | none => none
      | false => none
    | _ => none
  | .dynTrait expectedTrait => fun ptrMeta =>
    match ptrMeta with
    | .vtable vtId =>
      match vtEnv vtId with
      | some vt =>
        match Nat.beq vt.traitId expectedTrait && Nat.ble vt.size isizeMax with
        | true => some (vt.size, vt.align)
        | false => none
      | none => none
    | _ => none
  | .structTy adtId prefixFields tail => fun ptrMeta =>
    match isSized tail with
    | true =>
      match ptrMeta with
      | .thin =>
        let sz := staticSize (.structTy adtId prefixFields tail)
        let al := staticAlign (.structTy adtId prefixFields tail)
        match Nat.ble sz isizeMax with
        | true => some (sz, al)
        | false => none
      | _ => none
    | false =>
      match sizeAndAlignChecked vtEnv isizeMax tail ptrMeta with
      | some (tailSize, tailAlign) =>
        let p := computePrefixLayout prefixFields
        let fullAlign := fastMax p.maxAlign tailAlign
        let tailOffAdjusted := alignUp p.endOffset tailAlign
        match checkedAddLe tailOffAdjusted tailSize isizeMax with
        | some unpaddedEnd =>
          let fullSize := alignUp unpaddedEnd fullAlign
          match Nat.ble fullSize isizeMax with
          | true => some (fullSize, fullAlign)
          | false => none
        | none => none
      | none => none

noncomputable def sizeOfValChecked (vtEnv : VtEnv) (isizeMax : Nat)
    (ty : DstTy) (ptrMeta : PtrMeta) : Option Nat :=
  match sizeAndAlignChecked vtEnv isizeMax ty ptrMeta with
  | some (sz, _) => some sz
  | none => none

noncomputable def alignOfValChecked (vtEnv : VtEnv) (isizeMax : Nat)
    (ty : DstTy) (ptrMeta : PtrMeta) : Option Nat :=
  match sizeAndAlignChecked vtEnv isizeMax ty ptrMeta with
  | some (_, al) => some al
  | none => none

/-- Every successful `sizeOfValChecked` evaluation guarantees `sz ≤ isizeMax`. -/
theorem sizeOfValChecked_le_isizeMax (vtEnv : VtEnv) (isizeMax : Nat)
    (ty : DstTy) (ptrMeta : PtrMeta) (sz : Nat)
    (h : sizeOfValChecked vtEnv isizeMax ty ptrMeta = some sz) :
    sz ≤ isizeMax := by
  unfold sizeOfValChecked at h
  cases hsa : sizeAndAlignChecked vtEnv isizeMax ty ptrMeta with
  | none =>
    rw [hsa] at h
    cases h
  | some pair =>
    rw [hsa] at h
    injection h with hsz
    subst hsz
    cases ty with
    | scalar size align =>
      cases ptrMeta with
      | thin =>
        unfold sizeAndAlignChecked at hsa
        dsimp only [] at hsa
        cases hble : Nat.ble (alignUp size (fastMax 1 align)) isizeMax with
        | false => rw [hble] at hsa; cases hsa
        | true =>
          rw [hble] at hsa
          injection hsa with hp
          rw [← hp]
          exact Nat.le_of_ble_eq_true hble
      | sliceLen _ => cases hsa
      | vtable _ => cases hsa
    | array elem len =>
      cases ptrMeta with
      | thin =>
        unfold sizeAndAlignChecked at hsa
        dsimp only [] at hsa
        cases hszElem : isSized elem with
        | false => rw [hszElem] at hsa; cases hsa
        | true =>
          rw [hszElem] at hsa
          dsimp only [] at hsa
          cases hmul : checkedMulLe (staticSize elem) len isizeMax with
          | none => rw [hmul] at hsa; cases hsa
          | some prod =>
            rw [hmul] at hsa
            injection hsa with hp
            rw [← hp]
            exact (checkedMulLe_sound hmul).2
      | sliceLen _ => cases hsa
      | vtable _ => cases hsa
    | slice elem =>
      cases ptrMeta with
      | thin => cases hsa
      | vtable _ => cases hsa
      | sliceLen len =>
        unfold sizeAndAlignChecked at hsa
        dsimp only [] at hsa
        cases hszElem : isSized elem with
        | false => rw [hszElem] at hsa; cases hsa
        | true =>
          rw [hszElem] at hsa
          dsimp only [] at hsa
          cases hmul : checkedMulLe (staticSize elem) len isizeMax with
          | none => rw [hmul] at hsa; cases hsa
          | some prod =>
            rw [hmul] at hsa
            injection hsa with hp
            rw [← hp]
            exact (checkedMulLe_sound hmul).2
    | dynTrait expectedTrait =>
      cases ptrMeta with
      | thin => cases hsa
      | sliceLen _ => cases hsa
      | vtable vtId =>
        unfold sizeAndAlignChecked at hsa
        dsimp only [] at hsa
        cases hvt : vtEnv vtId with
        | none => rw [hvt] at hsa; cases hsa
        | some vt =>
          rw [hvt] at hsa
          dsimp only [] at hsa
          cases htr : Nat.beq vt.traitId expectedTrait with
          | false => rw [htr] at hsa; cases hsa
          | true =>
            rw [htr] at hsa
            cases hble : Nat.ble vt.size isizeMax with
            | false => rw [hble] at hsa; cases hsa
            | true =>
              rw [hble] at hsa
              injection hsa with hp
              rw [← hp]
              exact Nat.le_of_ble_eq_true hble
    | structTy adtId prefixFields tail =>
      unfold sizeAndAlignChecked at hsa
      dsimp only [] at hsa
      cases hszTail : isSized tail with
      | true =>
        rw [hszTail] at hsa
        dsimp only [] at hsa
        cases ptrMeta with
        | sliceLen _ => cases hsa
        | vtable _ => cases hsa
        | thin =>
          dsimp only [] at hsa
          cases hble : Nat.ble (staticSize (.structTy adtId prefixFields tail)) isizeMax with
          | false => rw [hble] at hsa; cases hsa
          | true =>
            rw [hble] at hsa
            injection hsa with hp
            rw [← hp]
            exact Nat.le_of_ble_eq_true hble
      | false =>
        rw [hszTail] at hsa
        dsimp only [] at hsa
        cases hRec : sizeAndAlignChecked vtEnv isizeMax tail ptrMeta with
        | none => rw [hRec] at hsa; cases hsa
        | some tailPair =>
          rw [hRec] at hsa
          dsimp only [] at hsa
          cases hAdd :
              checkedAddLe
                (alignUp (computePrefixLayout prefixFields).endOffset tailPair.2)
                tailPair.1
                isizeMax with
          | none => rw [hAdd] at hsa; cases hsa
          | some unpaddedEnd =>
            rw [hAdd] at hsa
            dsimp only [] at hsa
            cases hble :
                Nat.ble
                  (alignUp unpaddedEnd (fastMax (computePrefixLayout prefixFields).maxAlign tailPair.2))
                  isizeMax with
            | false => rw [hble] at hsa; cases hsa
            | true =>
              rw [hble] at hsa
              injection hsa with hp
              rw [← hp]
              exact Nat.le_of_ble_eq_true hble

/-- Inductive typing derivation for `PointerCoercion::Unsize` from a statically
    `Sized` source type `srcTy` (or `dyn` trait upcast) to an unsized destination
    type `dstTy`, tracking exact layout preservation `(erasedSize, erasedAlign)`. -/
inductive ValidUnsize (vtEnv : VtEnv) :
    DstTy → PtrMeta → DstTy → PtrMeta → Nat → Nat → Prop where
  /-- `&[T; N] -> &[T]` (including ZST slices such as `&[(); usize::MAX]`). -/
  | arrayToSlice (elem : DstTy) (len : Nat)
      (hElemSized : isSized elem = true) :
      ValidUnsize vtEnv
        (.array elem len) .thin
        (.slice elem) (.sliceLen len)
        (staticSize elem * len) (staticAlign elem)
  /-- `&Concrete -> &dyn Trait` when `vtId` is the compiler-generated vtable for `Concrete`. -/
  | sizedToDyn (src : DstTy) (traitId vtId : Nat) (vt : VTableHeader)
      (hSrcSized : isSized src = true)
      (hVt : vtEnv vtId = some vt)
      (hTrait : Nat.beq vt.traitId traitId = true)
      (hSz : vt.size = staticSize src)
      (hAl : vt.align = staticAlign src) :
      ValidUnsize vtEnv
        src .thin
        (.dynTrait traitId) (.vtable vtId)
        (staticSize src) (staticAlign src)
  /-- `&dyn SubTrait -> &dyn SuperTrait` trait upcasting between vtables of the same concrete type. -/
  | dynUpcast (subTrait superTrait vtSub vtSuper : Nat) (hSub hSuper : VTableHeader)
      (hVtSub : vtEnv vtSub = some hSub)
      (hVtSuper : vtEnv vtSuper = some hSuper)
      (hSubTrait : Nat.beq hSub.traitId subTrait = true)
      (hSuperTrait : Nat.beq hSuper.traitId superTrait = true)
      (hSameImpl : hSub.implTyId = hSuper.implTyId)
      (hSameSz : hSuper.size = hSub.size)
      (hSameAl : hSuper.align = hSub.align) :
      ValidUnsize vtEnv
        (.dynTrait subTrait) (.vtable vtSub)
        (.dynTrait superTrait) (.vtable vtSuper)
        hSub.size hSub.align
  /-- Structural tail unsizing `Struct<T> -> Struct<U>` (supports arbitrary nesting depth
      `Outer<Inner<[T; N]>> -> Outer<Inner<[T]>>` and `Outer<Concrete> -> Outer<dyn Trait>`). -/
  | structTail (adtId : Nat) (prefixFields : List FieldSpec)
      (tailSrc tailDst : DstTy) (metaIn metaOut : PtrMeta)
      (tailSz tailAl : Nat)
      (hDstUnsized : isSized tailDst = false)
      (hTail : ValidUnsize vtEnv tailSrc metaIn tailDst metaOut tailSz tailAl) :
      ValidUnsize vtEnv
        (.structTy adtId prefixFields tailSrc) metaIn
        (.structTy adtId prefixFields tailDst) metaOut
        (structFullSize prefixFields tailSz tailAl)
        (structFullAlign prefixFields tailAl)

/-- Every thin-source `ValidUnsize` derivation preserves exact `staticSize` and `staticAlign`
    of the concrete sized source type `srcTy` across arbitrary struct-tail nesting! -/
theorem validUnsize_thin_matches_static_layout
    {vtEnv : VtEnv} {srcTy dstTy : DstTy} {metaOut : PtrMeta} {sz al : Nat}
    (h : ValidUnsize vtEnv srcTy .thin dstTy metaOut sz al) :
    sz = staticSize srcTy ∧ al = staticAlign srcTy := by
  generalize hMetaIn : PtrMeta.thin = metaIn at h
  induction h with
  | arrayToSlice _ _ _ =>
    exact ⟨rfl, rfl⟩
  | sizedToDyn _ _ _ _ _ _ _ _ _ =>
    exact ⟨rfl, rfl⟩
  | dynUpcast _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases hMetaIn
  | structTail _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hSzEq, hAlEq⟩ := ih hMetaIn
    subst hSzEq
    subst hAlEq
    exact ⟨rfl, rfl⟩

/-- **Theorem 3a (Exact Dynamic Layout Evaluation Under `ValidUnsize`):**
    For EVERY `ValidUnsize` coercion (array-to-slice, ZST slice, concrete-to-`dyn`,
    `dyn` supertrait upcast, and arbitrarily nested custom DST tails) whose source
    size is bounded by `isizeMax`, `sizeAndAlignChecked` on the unsized destination
    succeeds (`≠ none`) and recovers the exact `(erasedSize, erasedAlign)`. -/
theorem validUnsize_sizeAndAlignChecked_eq
    {vtEnv : VtEnv} {isizeMax : Nat}
    {srcTy : DstTy} {metaIn : PtrMeta} {dstTy : DstTy} {metaOut : PtrMeta}
    {sz al : Nat}
    (hUnsize : ValidUnsize vtEnv srcTy metaIn dstTy metaOut sz al)
    (hBound : sz ≤ isizeMax) :
    sizeAndAlignChecked vtEnv isizeMax dstTy metaOut = some (sz, al) := by
  induction hUnsize with
  | arrayToSlice elem len hElemSized =>
    unfold sizeAndAlignChecked
    dsimp only []
    rw [hElemSized]
    dsimp only []
    unfold checkedMulLe
    dsimp only []
    have hble : Nat.ble (staticSize elem * len) isizeMax = true :=
      Nat.ble_eq.mpr hBound
    rw [hble]
  | sizedToDyn src _ _ _ _ hVt hTrait hSz hAl =>
    unfold sizeAndAlignChecked
    dsimp only []
    rw [hVt]
    dsimp only []
    rw [hTrait]
    rw [hSz, hAl]
    have hble : Nat.ble (staticSize src) isizeMax = true :=
      Nat.ble_eq.mpr hBound
    rw [hble]
    rfl
  | dynUpcast _ _ _ _ hSub _ _ hVtSuper _ hSuperTrait _ hSameSz hSameAl =>
    unfold sizeAndAlignChecked
    dsimp only []
    rw [hVtSuper]
    dsimp only []
    rw [hSuperTrait]
    rw [hSameSz, hSameAl]
    have hble : Nat.ble hSub.size isizeMax = true :=
      Nat.ble_eq.mpr hBound
    rw [hble]
    rfl
  | structTail _ prefixFields _ _ _ _ tailSz tailAl hDstUnsized _ ih =>
    unfold structFullSize at hBound
    unfold structFullSize structFullAlign
    let p := computePrefixLayout prefixFields
    let fullAlign := fastMax p.maxAlign tailAl
    let unpaddedEnd := alignUp p.endOffset tailAl + tailSz
    let fullSize := alignUp unpaddedEnd fullAlign
    have hUnpaddedLeFull : unpaddedEnd ≤ fullSize := le_alignUp unpaddedEnd fullAlign
    have hUnpaddedLeMax : unpaddedEnd ≤ isizeMax :=
      Nat.le_trans hUnpaddedLeFull hBound
    have hTailLeUnpadded : tailSz ≤ unpaddedEnd :=
      Nat.le_add_left tailSz (alignUp p.endOffset tailAl)
    have hTailLeMax : tailSz ≤ isizeMax :=
      Nat.le_trans hTailLeUnpadded hUnpaddedLeMax
    have hRec := ih hTailLeMax
    unfold sizeAndAlignChecked
    dsimp only []
    rw [hDstUnsized]
    dsimp only []
    rw [hRec]
    dsimp only []
    unfold checkedAddLe
    dsimp only []
    have hBleUnpadded : Nat.ble unpaddedEnd isizeMax = true :=
      Nat.ble_eq.mpr hUnpaddedLeMax
    rw [hBleUnpadded]
    dsimp only []
    have hBleFull : Nat.ble fullSize isizeMax = true :=
      Nat.ble_eq.mpr hBound
    rw [hBleFull]

/-- **Theorem 3b (In-Bounds Allocation Span Containment of Slice & Nested-DST Unsizing):**
    If a thin pointer `p` to a sized source type `srcTy` (`staticSize srcTy ≤ isizeMax`)
    is in-bounds of live allocation `alloc` (`SpanInBounds alloc p.prov p.addr (staticSize srcTy)`),
    and `srcTy` unsizes to `dstTy` with metadata `metaOut` via `ValidUnsize`, then:
    1. `sizeOfValChecked vtEnv isizeMax dstTy (unsizePtr p metaOut).metadata = some (staticSize srcTy)`,
    2. `alignOfValChecked vtEnv isizeMax dstTy (unsizePtr p metaOut).metadata = some (staticAlign srcTy)`,
    3. `(unsizePtr p metaOut)` is in-bounds of `alloc` over its entire dynamic byte span! -/
theorem unsized_span_contained_in_source_allocation
    {vtEnv : VtEnv} {isizeMax : Nat} {alloc : LiveAlloc}
    {srcTy dstTy : DstTy} {metaOut : PtrMeta} {sz al : Nat}
    (p : PtrVal)
    (hUnsize : ValidUnsize vtEnv srcTy .thin dstTy metaOut sz al)
    (hMax : staticSize srcTy ≤ isizeMax)
    (hInBounds : SpanInBounds alloc p.prov p.addr (staticSize srcTy)) :
    let pWide := unsizePtr p metaOut
    sizeOfValChecked vtEnv isizeMax dstTy pWide.metadata = some (staticSize srcTy) ∧
    alignOfValChecked vtEnv isizeMax dstTy pWide.metadata = some (staticAlign srcTy) ∧
    SpanInBounds alloc pWide.prov pWide.addr (staticSize srcTy) := by
  obtain ⟨hSzEq, hAlEq⟩ := validUnsize_thin_matches_static_layout hUnsize
  have hBound : sz ≤ isizeMax := by
    rw [hSzEq]
    exact hMax
  have hChecked := validUnsize_sizeAndAlignChecked_eq hUnsize hBound
  unfold sizeOfValChecked alignOfValChecked unsizePtr
  dsimp only []
  rw [hChecked, hSzEq, hAlEq]
  exact ⟨rfl, rfl, hInBounds⟩

/-! ## 7. Sharpness Counterexamples (Kernel-Checked Negative Witnesses) -/

/-- Unchecked 64-bit wrapping byte-size calculation `(head + len * elemSize) % 2^64`
    (modeling what happens if `size_of_val_raw` / slice bounds checking omits
    `isize::MAX` / overflow guards). -/
noncomputable def uncheckedWrappingByteSize64 (headSize len elemSize : Nat) : Nat :=
  (headSize + len * elemSize) % (Nat.pow 2 64)

/-- **Counterexample 1 (`ce1_unchecked_slice_byte_size_overflow_unsound`):**
    Consider `[u32]` (`elemSize = 4`, `headSize = 0`) with forged raw-slice length
    `len = 2^62 + 1` pointing to a small 8-byte `[u32; 2]` buffer (`allocBytes = 8`)
    on a 64-bit target (`isizeMax = 2^63 - 1`):
    1. Unchecked 64-bit modular arithmetic wraps `(0 + (2^62 + 1) * 4) % 2^64 = 4 ≤ 8`,
       falsely certifying that the slice fits inside the 8-byte buffer!
    2. Yet valid slice index `idx = 2 < len` addresses byte offset `2 * 4 = 8`
       (span `[8, 12)`), reading strictly out-of-bounds past `allocBytes = 8`!
    3. `sizeOfValChecked` rejects `(slice u32, sliceLen (2^62 + 1))` (`= none`),
       matching Miri `InvalidMeta(SliceTooBig)` (`m07_ub_slice_size_of_val_raw_u64_wrap_boundary`). -/
theorem ce1_unchecked_slice_byte_size_overflow_unsound :
    let u32Ty := DstTy.scalar 4 4
    let forgedLen := Nat.pow 2 62 + 1
    let allocBytes := 8
    let isizeMax64 := Nat.pow 2 63 - 1
    let victimIdx := 2
    uncheckedWrappingByteSize64 0 forgedLen 4 = 4 ∧
    uncheckedWrappingByteSize64 0 forgedLen 4 ≤ allocBytes ∧
    victimIdx < forgedLen ∧
    allocBytes < victimIdx * 4 + 4 ∧
    sizeOfValChecked (fun _ => none) isizeMax64 (.slice u32Ty) (.sliceLen forgedLen) = none := by
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · exact Nat.le_of_ble_eq_true rfl
  · exact Nat.le_of_ble_eq_true rfl
  · exact Nat.le_of_ble_eq_true rfl

/-- **Counterexample 2 (`ce2_non_tail_field_reordering_breaks_coerce_unsized`):**
    Consider `struct Wrap<T> { tag: u8, header: u16, tail: T }` (fields `0: u8`, `1: u16`, `2: T`),
    matching our empirical probe `SizedWrap<u64>` vs `DstWrap<u64>`!
    1. If the compiler allowed independent full-struct field reordering (`alwaysSizedFieldOffset`,
       sorting `prefixFields ++ [tail]`), then in `Wrap<u64>` (`tail` align `8 > 2 > 1`),
       `tail` is hoisted to offset `0`, shifting `header: u16` (field `1`) to offset `8`
       and `tag: u8` (field `0`) to offset `10`; whereas in `Wrap<dyn Trait>` (where static
       `dyn Trait` has placeholder align `1`), `header: u16` sits at offset `0` and
       `tag: u8` sits at offset `2`! Thus `PointerCoercion::Unsize` (`&Wrap<u64> -> &Wrap<dyn Trait>`)
       corrupts every prefix field read (`offset 8 != offset 0`, `offset 10 != offset 2`)!
    2. Under `StructKind::MaybeUnsized` (`maybeUnsizedFieldOffset`), `header` stays at offset `0`
       and `tag` stays at offset `2` across BOTH `Wrap<u64>` and `Wrap<dyn Trait>`. -/
theorem ce2_non_tail_field_reordering_breaks_coerce_unsized :
    let u8Spec : FieldSpec := { size := 1, align := 1 }
    let u16Spec : FieldSpec := { size := 2, align := 2 }
    let u64Ty := DstTy.scalar 8 8
    let dynTy := DstTy.dynTrait 0
    let pref := [u8Spec, u16Spec]
    alwaysSizedFieldOffset pref u64Ty 1 = some 8 ∧
    alwaysSizedFieldOffset pref dynTy 1 = some 0 ∧
    alwaysSizedFieldOffset pref u64Ty 0 = some 10 ∧
    alwaysSizedFieldOffset pref dynTy 0 = some 2 ∧
    alwaysSizedFieldOffset pref u64Ty 1 ≠ alwaysSizedFieldOffset pref dynTy 1 ∧
    maybeUnsizedFieldOffset pref u64Ty 1 = some 0 ∧
    maybeUnsizedFieldOffset pref dynTy 1 = some 0 ∧
    maybeUnsizedFieldOffset pref u64Ty 0 = some 2 ∧
    maybeUnsizedFieldOffset pref dynTy 0 = some 2 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro hEq
  injection hEq with hNum
  cases hNum

/-- **Counterexample 3 (`ce3_prefix_plus_valid_slice_overflows_isizeMax`):**
    Sharpness witness for Miri case `m08_ub_struct_tail_prefix_pushes_over_isize_max`:
    For `DstWrap<[u8]>` (`tag: u8, header: u16, tail: [u8]`, prefix end `3`, align `2`)
    at `len = isizeMax64 - 1`:
    1. `[u8]` alone with `len = isizeMax64 - 1` IS valid (`sizeOfValChecked = some (isizeMax64 - 1)`),
    2. Yet embedding that exact slice tail inside `DstWrap<[u8]>` pushes total byte size
       `alignUp (3 + (isizeMax64 - 1)) 2` past `isizeMax64`, so `sizeOfValChecked` on
       `DstWrap<[u8]>` MUST reject it (`= none`)! Checking only the slice tail without
       adding the prefix offset and struct-alignment tail padding is unsound. -/
theorem ce3_prefix_plus_valid_slice_overflows_isizeMax :
    let u8Spec : FieldSpec := { size := 1, align := 1 }
    let u16Spec : FieldSpec := { size := 2, align := 2 }
    let u8Ty := DstTy.scalar 1 1
    let isizeMax64 := 9223372036854775807
    let edgeLen := 9223372036854775806
    isizeMax64 = Nat.pow 2 63 - 1 ∧
    edgeLen = isizeMax64 - 1 ∧
    sizeOfValChecked (fun _ => none) isizeMax64 (.slice u8Ty) (.sliceLen edgeLen) =
      some edgeLen ∧
    sizeOfValChecked (fun _ => none) isizeMax64
      (.structTy 1 [u8Spec, u16Spec] (.slice u8Ty)) (.sliceLen edgeLen) = none := by
  have hSlice :
      sizeAndAlignChecked (fun _ => none) 9223372036854775807
        (.slice (.scalar 1 1)) (.sliceLen 9223372036854775806) =
      some (9223372036854775806, 1) := by
    unfold sizeAndAlignChecked checkedMulLe
    have hSz : staticSize (.scalar 1 1) = 1 := rfl
    have hAl : staticAlign (.scalar 1 1) = 1 := rfl
    have hSzB : isSized (.scalar 1 1) = true := rfl
    rw [hSzB, hSz, hAl]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold sizeOfValChecked
    rw [hSlice]
  · unfold sizeOfValChecked sizeAndAlignChecked
    have hUnsz : isSized (.slice (.scalar 1 1)) = false := rfl
    rw [hUnsz]
    dsimp only []
    rw [hSlice]
    dsimp only []
    have hPrefOff :
        alignUp (computePrefixLayout [{ size := 1, align := 1 }, { size := 2, align := 2 }]).endOffset 1 = 3 := rfl
    rw [hPrefOff]
    unfold checkedAddLe
    rfl

/-- Concrete kernel-reduced sanity check matching our empirical `DstWrap` & `OuterWrap` specimens:
    - `ZST` slice `&[(); usize::MAX]` (`2^64 - 1`) has checked size `0` and align `1`.
    - `DstWrap<[u32; 4]>` unsized to `DstWrap<[u32]>` has checked size `20` and align `4`.
    - `OuterWrap<DstWrap<[u32; 3]>>` unsized to `OuterWrap<DstWrap<[u32]>>` has checked size `32`
      and align `8`, matching native execution `s04_nested = [3, 32, 8, ...]`. -/
theorem concrete_specimens_kernel_verified :
    let unitTy := DstTy.scalar 0 1
    let u8Spec : FieldSpec := { size := 1, align := 1 }
    let u16Spec : FieldSpec := { size := 2, align := 2 }
    let u64Spec : FieldSpec := { size := 8, align := 8 }
    let u32Ty := DstTy.scalar 4 4
    let usizeMax64 := Nat.pow 2 64 - 1
    let isizeMax64 := Nat.pow 2 63 - 1
    let innerDst := DstTy.structTy 1 [u8Spec, u16Spec] (.slice u32Ty)
    let outerDst := DstTy.structTy 2 [u8Spec, u64Spec] innerDst
    sizeAndAlignChecked (fun _ => none) isizeMax64 (.slice unitTy) (.sliceLen usizeMax64) =
      some (0, 1) ∧
    sizeAndAlignChecked (fun _ => none) isizeMax64 innerDst (.sliceLen 4) =
      some (20, 4) ∧
    sizeAndAlignChecked (fun _ => none) isizeMax64 outerDst (.sliceLen 3) =
      some (32, 8) := by
  exact ⟨rfl, rfl, rfl⟩

end UnsizingWidePointerSoundness
