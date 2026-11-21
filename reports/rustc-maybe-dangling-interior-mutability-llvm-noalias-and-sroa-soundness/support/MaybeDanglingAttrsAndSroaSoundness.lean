/-!
# `MaybeDangling`-like wrappers: parameter-attribute lowering, validity levels, niches and SROA

A self-contained finite model (Lean core only, no imports) of four things that
`rustc` does with references and with the wrappers `MaybeDangling<T>`,
`ManuallyDrop<T>`, coroutine state and `MaybeUninit<T>`:

The "later" compiler revision is `rust-lang/rust`
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (rustc 1.102.0-nightly, LLVM 23) and the
"earlier" one is `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (rustc 1.98.0-nightly, LLVM 22).

* **Lowering.**  `pointeeInfoAt`, `argAttrs` and `lowerPost`/`lowerPre` transcribe
  `ty_and_layout_pointee_info_at` (`compiler/rustc_middle/src/ty/layout.rs`),
  `arg_attrs_for_rust_scalar` (`compiler/rustc_ty_utils/src/abi.rs`) and `get_attrs`
  (`compiler/rustc_codegen_llvm/src/abi.rs`).  `lowerPost` is the compiler revision that
  has `ArgAttribute::NoFree` and the LLVM-version gate on `dereferenceable`;
  `lowerPre` is the earlier revision without either.
* **Validity.**  `validSlot` transcribes the reference checks of
  `ValidityVisitor::check_safe_pointer` together with the sticky `may_dangle` flag
  (`compiler/rustc_const_eval/src/interpret/validity.rs`): inside a maybe-dangling-like
  type a reference must still be non-null and aligned, but need not be dereferenceable.
* **Call-time aliasing.**  `step`/`run` is a small state machine for one pointee during
  one call: liveness, the stored value and the strongest permission held by pointers
  that are *not* derived from the argument.  A read through the argument freezes an
  active exclusive alias (the "foreign read" rule), which is the reason `rustc` gives
  for withholding `dereferenceable` from `&!Freeze` and `&mut !Unpin`.
* **SROA.**  `sroaStmt` rewrites a whole-value typed copy at a wrapper type into a typed
  copy at the wrapped type, which is what `ScalarReplacementOfAggregates` does to a
  local it flattens.

What is and is not claimed.  The lowering functions are transcriptions restricted to the
type family `Ty` below (references to three 8-byte, 8-aligned pointees under any nesting
of five one-field wrappers) and to arguments at default unstable flags; `Box`, wide
pointers, return positions, `-Zbox-noalias`, `-Zmutable-noalias` and `-Zllvm-writable` are
not modelled.  `captures(address, read_provenance)` is carried
through the lowering but has no semantics here.  The aliasing machine is an abstraction
written for this file; it is not Stacked Borrows or Tree Borrows.  The theorems relate
these definitions to each other; they do not mention `rustc` or LLVM binaries.
-/

namespace MaybeDanglingModel

/-! ## Boolean and numeric helpers

Kept explicit so that proofs reduce by `cases` and `rfl`. -/

def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

def gtOne : Nat → Bool
  | 0 => false
  | 1 => false
  | _ + 2 => true

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a
  · exact Bool.noConfusion h
  · rfl

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a
  · exact Bool.noConfusion h
  · exact h

theorem and_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  subst ha
  subst hb
  rfl

theorem and_true_eq (b : Bool) : (b && true) = b := by
  cases b <;> rfl

theorem or_true_eq (b : Bool) : (b || true) = true := by
  cases b <;> rfl

theorem or_false_eq (b : Bool) : (b || false) = b := by
  cases b <;> rfl

/-! ## Types -/

/-- Pointee types.  All three are 8 bytes, 8-aligned. -/
inductive Pointee
  /-- `u64`: `Freeze` and `Unpin`. -/
  | u64
  /-- `UnsafeCell<u64>`: `!Freeze`, `Unpin`. -/
  | unsafeCellU64
  /-- `struct { v: u64, _pin: PhantomPinned }`: `Freeze`, `!Unpin`. -/
  | pinnedU64
  deriving DecidableEq, Repr

def Pointee.freeze : Pointee → Bool
  | .u64 => true
  | .unsafeCellU64 => false
  | .pinnedU64 => true

def Pointee.unpin : Pointee → Bool
  | .u64 => true
  | .unsafeCellU64 => true
  | .pinnedU64 => false

inductive Mutbl
  | shared
  | mut
  deriving DecidableEq, Repr

/-- One-field wrappers around a pointer-sized value. -/
inductive Wrapper
  /-- A user `#[repr(transparent)] struct W<T>(T)` that is not a lang item. -/
  | plain
  /-- `ManuallyDrop<T>` (`AdtFlags::IS_MANUALLY_DROP`). -/
  | manuallyDrop
  /-- `MaybeDangling<T>` (`AdtFlags::IS_MAYBE_DANGLING`). -/
  | maybeDangling
  /-- Coroutine state (`ty::Coroutine(..)`), abstracted to one saved field. -/
  | coroutine
  /-- `union MaybeUninit<T>`. -/
  | maybeUninit
  deriving DecidableEq, Repr

/-- `Ty::is_like_maybe_dangling` restricted to `Wrapper`. -/
def Wrapper.isLikeMaybeDangling : Wrapper → Bool
  | .manuallyDrop => true
  | .maybeDangling => true
  | .coroutine => true
  | .plain => false
  | .maybeUninit => false

def Wrapper.isUnion : Wrapper → Bool
  | .maybeUninit => true
  | .plain => false
  | .manuallyDrop => false
  | .maybeDangling => false
  | .coroutine => false

inductive Ty
  | ref (m : Mutbl) (t : Pointee)
  | wrap (w : Wrapper) (inner : Ty)

/-! ## Lowering: `PointeeInfo`, `ArgAttributes`, LLVM parameter attributes -/

inductive PointerKind
  | sharedRef (frozen : Bool)
  | mutableRef (unpin : Bool)
  deriving DecidableEq, Repr

structure PointeeInfo where
  safe : Option PointerKind
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

/-- "Patch result if we are a MaybeDangling-like type": mark the pointer as raw, assert no
dereferenceability, keep the alignment. -/
def patchMaybeDangling : Option PointeeInfo → Option PointeeInfo
  | none => none
  | some info => some { safe := none, size := 0, align := info.align }

/-- `ty_and_layout_pointee_info_at` at offset 0.  `optimize` is
`sess.opts.optimize != OptLevel::No`. -/
noncomputable def pointeeInfoAt (optimize : Bool) : Ty → Option PointeeInfo
  | .ref .shared t =>
      some { safe := some (.sharedRef (optimize && t.freeze))
             size := match optimize && t.freeze with
               | true => 8
               | false => 0
             align := 8 }
  | .ref .mut t =>
      some { safe := some (.mutableRef (optimize && t.unpin))
             size := match optimize && t.unpin with
               | true => 8
               | false => 0
             align := 8 }
  | .wrap w inner =>
      match w.isUnion, w.isLikeMaybeDangling with
      | true, _ => none
      | false, true => patchMaybeDangling (pointeeInfoAt optimize inner)
      | false, false => pointeeInfoAt optimize inner

/-- The two facts about the ABI scalar that the lowering reads. -/
structure Scalar where
  /-- `Scalar::is_uninit_valid()`: true for the scalar of a union. -/
  uninitValid : Bool
  /-- `!valid_range.contains(0)`. -/
  rangeExcludesZero : Bool
  deriving DecidableEq, Repr

noncomputable def scalarOf : Ty → Scalar
  | .ref _ _ => { uninitValid := false, rangeExcludesZero := true }
  | .wrap w inner =>
      match w.isUnion with
      | true => { uninitValid := true, rangeExcludesZero := false }
      | false => scalarOf inner

structure ArgAttrs where
  noUndef : Bool
  nonNull : Bool
  noAlias : Bool
  noFree : Bool
  readOnly : Bool
  capturesReadOnly : Bool
  pointeeSize : Nat
  pointeeAlign : Option Nat
  deriving DecidableEq, Repr

def emptyArgAttrs : ArgAttrs :=
  { noUndef := false, nonNull := false, noAlias := false, noFree := false, readOnly := false
    capturesReadOnly := false, pointeeSize := 0, pointeeAlign := none }

def strongKind : Option PointerKind → Bool
  | some (.sharedRef frozen) => frozen
  | some (.mutableRef unpin) => unpin
  | none => false

def frozenSharedKind : Option PointerKind → Bool
  | some (.sharedRef frozen) => frozen
  | some (.mutableRef _) => false
  | none => false

/-- `pointee_align` is recorded only when it exceeds 1. -/
def alignAttr (a : Nat) : Option Nat :=
  match gtOne a with
  | true => some a
  | false => none

theorem alignAttr_eq_some {a n : Nat} (h : alignAttr a = some n) : a = n := by
  unfold alignAttr at h
  cases hg : gtOne a with
  | false =>
    rw [hg] at h
    cases h
  | true =>
    rw [hg] at h
    exact Option.some.inj h

/-- `arg_attrs_for_rust_scalar` for an argument (not a return value). -/
noncomputable def argAttrs (optimize : Bool) (ty : Ty) : ArgAttrs :=
  match (scalarOf ty).uninitValid, pointeeInfoAt optimize ty with
  | true, _ => emptyArgAttrs
  | false, none =>
      { noUndef := true, nonNull := (scalarOf ty).rangeExcludesZero, noAlias := false
        noFree := false, readOnly := false, capturesReadOnly := false, pointeeSize := 0
        pointeeAlign := none }
  | false, some info =>
      { noUndef := true
        nonNull := (scalarOf ty).rangeExcludesZero
        noAlias := strongKind info.safe
        noFree := strongKind info.safe
        readOnly := frozenSharedKind info.safe
        capturesReadOnly := frozenSharedKind info.safe
        pointeeSize := info.size
        pointeeAlign := alignAttr info.align }

structure LlvmAttrs where
  noalias : Bool
  nofree : Bool
  noundef : Bool
  readonly : Bool
  nonnull : Bool
  capturesAddressReadProvenance : Bool
  align : Option Nat
  dereferenceable : Option Nat
  dereferenceableOrNull : Option Nat
  deriving DecidableEq, Repr

def unoptimizedAttrs (a : ArgAttrs) : LlvmAttrs :=
  { noalias := false, nofree := false, noundef := false, readonly := false, nonnull := false
    capturesAddressReadProvenance := false, align := a.pointeeAlign, dereferenceable := none
    dereferenceableOrNull := none }

def optimizedAttrs (emitDeref nofree : Bool) (a : ArgAttrs) : LlvmAttrs :=
  { noalias := a.noAlias
    nofree := nofree
    noundef := a.noUndef
    readonly := a.readOnly
    nonnull := a.nonNull && !emitDeref
    capturesAddressReadProvenance := a.capturesReadOnly
    align := a.pointeeAlign
    dereferenceable := match emitDeref, a.nonNull with
      | true, true => some a.pointeeSize
      | true, false => none
      | false, _ => none
    dereferenceableOrNull := match emitDeref, a.nonNull with
      | true, false => some a.pointeeSize
      | true, true => none
      | false, _ => none }

/-- `get_attrs` at the later compiler revision: `dereferenceable` is emitted when the
pointee size is non-zero and (`LLVM >= 23` or `NoFree` is set). -/
def lowerPost (optimize llvmGe23 : Bool) (a : ArgAttrs) : LlvmAttrs :=
  match optimize with
  | false => unoptimizedAttrs a
  | true => optimizedAttrs (!(isZero a.pointeeSize) && (llvmGe23 || a.noFree)) a.noFree a

/-- `get_attrs` at the earlier compiler revision: no `NoFree`, `dereferenceable` is emitted
whenever the pointee size is non-zero. -/
def lowerPre (optimize : Bool) (a : ArgAttrs) : LlvmAttrs :=
  match optimize with
  | false => unoptimizedAttrs a
  | true => optimizedAttrs (!(isZero a.pointeeSize)) false a

noncomputable def llvmParamAttrs (optimize llvmGe23 : Bool) (ty : Ty) : LlvmAttrs :=
  lowerPost optimize llvmGe23 (argAttrs optimize ty)

noncomputable def llvmParamAttrsPre (optimize : Bool) (ty : Ty) : LlvmAttrs :=
  lowerPre optimize (argAttrs optimize ty)

/-! ### The nine rows -/

/-- `&u64` -/
def row1 : Ty := .ref .shared .u64
/-- `&mut u64` -/
def row2 : Ty := .ref .mut .u64
/-- `&UnsafeCell<u64>` -/
def row3 : Ty := .ref .shared .unsafeCellU64
/-- `&mut UnsafeCell<u64>` -/
def row4 : Ty := .ref .mut .unsafeCellU64
/-- `&mut PinnedU64` -/
def row5 : Ty := .ref .mut .pinnedU64
/-- `PlainWrap<&u64>` -/
def row6 : Ty := .wrap .plain row1
/-- `ManuallyDrop<&u64>` -/
def row7 : Ty := .wrap .manuallyDrop row1
/-- `MaybeDangling<&u64>` -/
def row8 : Ty := .wrap .maybeDangling row1
/-- `MaybeUninit<&u64>` -/
def row9 : Ty := .wrap .maybeUninit row1

def rows : List Ty := [row1, row2, row3, row4, row5, row6, row7, row8, row9]

/-- `ptr noalias nofree noundef readonly align 8 captures(address, read_provenance)
dereferenceable(8)` -/
def attrsFrozenShared : LlvmAttrs :=
  { noalias := true, nofree := true, noundef := true, readonly := true, nonnull := false
    capturesAddressReadProvenance := true, align := some 8, dereferenceable := some 8
    dereferenceableOrNull := none }

/-- `ptr noalias nofree noundef align 8 dereferenceable(8)` -/
def attrsUniqueMut : LlvmAttrs :=
  { noalias := true, nofree := true, noundef := true, readonly := false, nonnull := false
    capturesAddressReadProvenance := false, align := some 8, dereferenceable := some 8
    dereferenceableOrNull := none }

/-- `ptr noundef nonnull align 8` -/
def attrsAlignedNonNull : LlvmAttrs :=
  { noalias := false, nofree := false, noundef := true, readonly := false, nonnull := true
    capturesAddressReadProvenance := false, align := some 8, dereferenceable := none
    dereferenceableOrNull := none }

/-- `ptr` -/
def attrsBare : LlvmAttrs :=
  { noalias := false, nofree := false, noundef := false, readonly := false, nonnull := false
    capturesAddressReadProvenance := false, align := none, dereferenceable := none
    dereferenceableOrNull := none }

/-- `ptr align 8` -/
def attrsAlignOnly : LlvmAttrs := { attrsBare with align := some 8 }

def eraseNoFree (a : LlvmAttrs) : LlvmAttrs := { a with nofree := false }

/-- Later revision, LLVM 23, `-C opt-level=2`. -/
theorem matrix_post_llvm23_opt2 :
    rows.map (llvmParamAttrs true true) =
      [attrsFrozenShared, attrsUniqueMut, attrsAlignedNonNull, attrsUniqueMut,
       attrsAlignedNonNull, attrsFrozenShared, attrsAlignedNonNull, attrsAlignedNonNull,
       attrsBare] := by
  decide

/-- Later revision on an LLVM older than 23: the nine rows are unchanged, because every
row with a non-zero pointee size also has `NoFree`. -/
theorem matrix_post_llvm22_opt2 :
    rows.map (llvmParamAttrs true false) = rows.map (llvmParamAttrs true true) := by
  decide

/-- Earlier revision, `-C opt-level=2`: the same rows without `nofree`. -/
theorem matrix_pre_opt2 :
    rows.map (llvmParamAttrsPre true) =
      [eraseNoFree attrsFrozenShared, eraseNoFree attrsUniqueMut, attrsAlignedNonNull,
       eraseNoFree attrsUniqueMut, attrsAlignedNonNull, eraseNoFree attrsFrozenShared,
       attrsAlignedNonNull, attrsAlignedNonNull, attrsBare] := by
  decide

/-- `-C opt-level=0`, either revision, either LLVM. -/
theorem matrix_opt0 (llvmGe23 : Bool) :
    rows.map (llvmParamAttrs false llvmGe23) =
        [attrsAlignOnly, attrsAlignOnly, attrsAlignOnly, attrsAlignOnly, attrsAlignOnly,
         attrsAlignOnly, attrsAlignOnly, attrsAlignOnly, attrsBare] ∧
      rows.map (llvmParamAttrsPre false) = rows.map (llvmParamAttrs false llvmGe23) := by
  cases llvmGe23 <;> decide

/-- On LLVM 23 the two `get_attrs` revisions differ exactly in `nofree`, for every
`ArgAttrs` value and hence for every type. -/
theorem pre_eq_post_erase_nofree (a : ArgAttrs) :
    lowerPre true a = eraseNoFree (lowerPost true true a) := by
  cases a with
  | mk noUndef nonNull noAlias noFree readOnly capturesReadOnly pointeeSize pointeeAlign =>
    cases pointeeSize <;> rfl

theorem llvmParamAttrsPre_eq (ty : Ty) :
    llvmParamAttrsPre true ty = eraseNoFree (llvmParamAttrs true true ty) :=
  pre_eq_post_erase_nofree (argAttrs true ty)

/-- Exactly three wrapper families are maybe-dangling-like. -/
theorem isLikeMaybeDangling_iff (w : Wrapper) :
    w.isLikeMaybeDangling = true ↔
      w = .manuallyDrop ∨ w = .maybeDangling ∨ w = .coroutine := by
  cases w <;> decide


/-! ## HeapState, pointers and the validity invariant -/

inductive AllocState
  | live
  | freed
  deriving DecidableEq, Repr

structure Alloc where
  base : Nat
  size : Nat
  state : AllocState
  deriving DecidableEq, Repr

abbrev HeapState := List Alloc

structure Ptr where
  addr : Nat
  /-- Provenance: index of the allocation this pointer was derived from, if any. -/
  alloc : Option Nat
  deriving DecidableEq, Repr

/-- The contents of one pointer-sized location. -/
inductive Slot
  | uninit
  | ptr (p : Ptr)
  deriving DecidableEq, Repr

def nonNull (p : Ptr) : Bool := !(isZero p.addr)

def aligned (a : Nat) (p : Ptr) : Bool := isZero (p.addr % a)

def inBounds (a : Alloc) (p : Ptr) (n : Nat) : Bool :=
  match a.state with
  | .freed => false
  | .live => Nat.ble a.base p.addr && Nat.ble (p.addr + n) (a.base + a.size)

/-- `n` bytes at `p` lie inside a live allocation that `p` has provenance for. -/
def derefable (h : HeapState) (p : Ptr) (n : Nat) : Bool :=
  match p.alloc with
  | none => false
  | some i =>
      match h[i]? with
      | none => false
      | some a => inBounds a p n

/-- The validity invariant of a pointer-sized value of type `ty`, as checked by
`check_safe_pointer`.  `mayDangle` is the visitor's sticky `may_dangle` flag: it is set
on entering a maybe-dangling-like type and switches off only the dereferenceability
check.  A union accepts every bit pattern. -/
noncomputable def validSlot (h : HeapState) : Bool → Ty → Slot → Bool
  | _, .ref _ _, .uninit => false
  | mayDangle, .ref _ _, .ptr p =>
      nonNull p && aligned 8 p && (mayDangle || derefable h p 8)
  | mayDangle, .wrap w inner, s =>
      match w.isUnion with
      | true => true
      | false => validSlot h (mayDangle || w.isLikeMaybeDangling) inner s

/-- Entering a maybe-dangling context only ever admits more values. -/
theorem validSlot_mono (h : HeapState) : ∀ (ty : Ty) (s : Slot),
    validSlot h false ty s = true → validSlot h true ty s = true := by
  intro ty
  induction ty with
  | ref m t =>
    intro s hv
    cases s with
    | uninit => exact Bool.noConfusion hv
    | ptr p => exact and_intro (and_left hv) rfl
  | wrap w inner ih =>
    intro s hv
    cases w with
    | maybeUninit => rfl
    | plain => exact ih s hv
    | manuallyDrop => exact hv
    | maybeDangling => exact hv
    | coroutine => exact hv

/-! ### The four validity levels -/

/-- `fullRef < mayDangleAlignedNonNull < rawAligned < uninitOrArbitrary`. -/
inductive Level
  /-- Non-null, aligned and dereferenceable; the flags record `Freeze`/`Unpin` of the
  pointee and matter only for the call-time aliasing contract. -/
  | fullRef (frozen unpin : Bool)
  /-- Non-null and aligned; may point to freed or never-allocated memory. -/
  | mayDangleAlignedNonNull (align : Nat)
  /-- Aligned; may be null. -/
  | rawAligned (align : Nat)
  /-- Any bit pattern, including uninitialized. -/
  | uninitOrArbitrary
  deriving DecidableEq, Repr

def Level.rank : Level → Nat
  | .fullRef _ _ => 0
  | .mayDangleAlignedNonNull _ => 1
  | .rawAligned _ => 2
  | .uninitOrArbitrary => 3

def Level.admits (h : HeapState) : Level → Slot → Bool
  | .fullRef _ _, .uninit => false
  | .fullRef _ _, .ptr p => nonNull p && aligned 8 p && derefable h p 8
  | .mayDangleAlignedNonNull _, .uninit => false
  | .mayDangleAlignedNonNull a, .ptr p => nonNull p && aligned a p
  | .rawAligned _, .uninit => false
  | .rawAligned a, .ptr p => aligned a p
  | .uninitOrArbitrary, _ => true

/-- The effect of a maybe-dangling context on a level. -/
def Level.weaken : Bool → Level → Level
  | false, l => l
  | true, .fullRef _ _ => .mayDangleAlignedNonNull 8
  | true, .mayDangleAlignedNonNull a => .mayDangleAlignedNonNull a
  | true, .rawAligned a => .rawAligned a
  | true, .uninitOrArbitrary => .uninitOrArbitrary

noncomputable def levelOf : Ty → Level
  | .ref _ t => .fullRef t.freeze t.unpin
  | .wrap w inner =>
      match w.isUnion, w.isLikeMaybeDangling with
      | true, _ => .uninitOrArbitrary
      | false, true => (levelOf inner).weaken true
      | false, false => levelOf inner

theorem weaken_weaken (md : Bool) (l : Level) :
    (l.weaken true).weaken md = l.weaken true := by
  cases md <;> cases l <;> rfl

theorem weaken_union (md : Bool) : Level.uninitOrArbitrary.weaken md = .uninitOrArbitrary := by
  cases md <;> rfl

/-- `levelOf` characterises validity exactly, in and out of a maybe-dangling context. -/
theorem validSlot_eq_level (h : HeapState) : ∀ (ty : Ty) (md : Bool) (s : Slot),
    validSlot h md ty s = ((levelOf ty).weaken md).admits h s := by
  intro ty
  induction ty with
  | ref m t =>
    intro md s
    cases s with
    | uninit => cases md <;> rfl
    | ptr p =>
      cases md with
      | false => rfl
      | true => exact and_true_eq (nonNull p && aligned 8 p)
  | wrap w inner ih =>
    intro md s
    cases w with
    | maybeUninit =>
      show true = ((Level.uninitOrArbitrary).weaken md).admits h s
      rw [weaken_union]
      rfl
    | plain =>
      show validSlot h (md || false) inner s = ((levelOf inner).weaken md).admits h s
      rw [or_false_eq]
      exact ih md s
    | manuallyDrop =>
      show validSlot h (md || true) inner s = (((levelOf inner).weaken true).weaken md).admits h s
      rw [or_true_eq, weaken_weaken]
      exact ih true s
    | maybeDangling =>
      show validSlot h (md || true) inner s = (((levelOf inner).weaken true).weaken md).admits h s
      rw [or_true_eq, weaken_weaken]
      exact ih true s
    | coroutine =>
      show validSlot h (md || true) inner s = (((levelOf inner).weaken true).weaken md).admits h s
      rw [or_true_eq, weaken_weaken]
      exact ih true s

/-- The levels of the nine rows. -/
theorem levels_of_rows :
    rows.map levelOf =
      [.fullRef true true, .fullRef true true, .fullRef false true, .fullRef false true,
       .fullRef true false, .fullRef true true, .mayDangleAlignedNonNull 8,
       .mayDangleAlignedNonNull 8, .uninitOrArbitrary] := by
  decide

/-- The four levels form a chain: each admits everything the previous one admits. -/
theorem level_chain (h : HeapState) (frozen unpin : Bool) (s : Slot) :
    ((Level.fullRef frozen unpin).admits h s = true →
        (Level.mayDangleAlignedNonNull 8).admits h s = true) ∧
      ((Level.mayDangleAlignedNonNull 8).admits h s = true →
        (Level.rawAligned 8).admits h s = true) ∧
      ((Level.rawAligned 8).admits h s = true → Level.uninitOrArbitrary.admits h s = true) := by
  cases s with
  | uninit => exact ⟨fun hv => hv, fun hv => hv, fun _ => rfl⟩
  | ptr p => exact ⟨fun hv => and_left hv, fun hv => and_right hv, fun _ => rfl⟩

/-- The chain is strict: a freed allocation, the null pointer and an uninitialized slot
separate the four levels. -/
theorem level_chain_strict :
    let freedHeap : HeapState := [{ base := 8, size := 8, state := .freed }]
    let dangling : Slot := .ptr { addr := 8, alloc := some 0 }
    let null : Slot := .ptr { addr := 0, alloc := none }
    ((Level.mayDangleAlignedNonNull 8).admits freedHeap dangling = true ∧
        (Level.fullRef true true).admits freedHeap dangling = false) ∧
      ((Level.rawAligned 8).admits freedHeap null = true ∧
        (Level.mayDangleAlignedNonNull 8).admits freedHeap null = false) ∧
      (Level.uninitOrArbitrary.admits freedHeap .uninit = true ∧
        (Level.rawAligned 8).admits freedHeap .uninit = false) := by
  decide

/-! ## Theorem 1a: every emitted value-level attribute is true of every valid value -/

/-- What the attributes assert about the argument value at function entry.  Every
asserted fact must hold (a conservative reading: LLVM makes some violations poison
rather than immediate undefined behaviour). -/
def alignHolds (p : Ptr) : Option Nat → Bool
  | none => true
  | some n => aligned n p

def derefHolds (h : HeapState) (p : Ptr) : Option Nat → Bool
  | none => true
  | some n => nonNull p && derefable h p n

def derefOrNullHolds (h : HeapState) (p : Ptr) : Option Nat → Bool
  | none => true
  | some n => !(nonNull p) || derefable h p n

def attrsHold (h : HeapState) (a : LlvmAttrs) : Slot → Bool
  | .uninit =>
      !a.noundef && !a.nonnull && a.align.isNone && a.dereferenceable.isNone &&
        a.dereferenceableOrNull.isNone
  | .ptr p =>
      (!a.nonnull || nonNull p) && alignHolds p a.align &&
        derefHolds h p a.dereferenceable && derefOrNullHolds h p a.dereferenceableOrNull

/-- A valid value of a type whose scalar forbids uninitialized bytes is a non-null
pointer. -/
theorem valid_ptr_of_init (h : HeapState) : ∀ (ty : Ty) (md : Bool) (s : Slot),
    validSlot h md ty s = true → (scalarOf ty).uninitValid = false →
      ∃ p, s = .ptr p ∧ nonNull p = true := by
  intro ty
  induction ty with
  | ref m t =>
    intro md s hv _
    cases s with
    | uninit => exact Bool.noConfusion hv
    | ptr p => exact ⟨p, rfl, and_left (and_left hv)⟩
  | wrap w inner ih =>
    intro md s hv hu
    cases w with
    | maybeUninit => exact Bool.noConfusion hu
    | plain => exact ih (md || false) s hv hu
    | manuallyDrop => exact ih (md || true) s hv hu
    | maybeDangling => exact ih (md || true) s hv hu
    | coroutine => exact ih (md || true) s hv hu

/-- What `PointeeInfo` promises, stated for a value valid in context `md`. -/
def PointeeFacts (h : HeapState) (md : Bool) (s : Slot) : Option PointeeInfo → Prop
  | none => True
  | some info =>
      ∃ p, s = .ptr p ∧ aligned info.align p = true ∧
        (md = false → isZero info.size = false → derefable h p info.size = true)

theorem pointeeFacts_ref (h : HeapState) (opt md : Bool) (m : Mutbl) (t : Pointee) (p : Ptr)
    (hv : validSlot h md (.ref m t) (.ptr p) = true) :
    PointeeFacts h md (.ptr p) (pointeeInfoAt opt (.ref m t)) := by
  have hal : aligned 8 p = true := and_right (and_left hv)
  have hd : (md || derefable h p 8) = true := and_right hv
  cases m <;> cases t <;> cases opt <;>
    exact ⟨p, rfl, hal, fun hmd hz => by
      first
        | exact Bool.noConfusion hz
        | (subst hmd; exact hd)⟩

/-- Under a non-union wrapper that is maybe-dangling-like, the patched `PointeeInfo`
keeps only the alignment. -/
theorem pointeeFacts_patch (h : HeapState) (md : Bool) (s : Slot) :
    ∀ (o : Option PointeeInfo), PointeeFacts h true s o →
      PointeeFacts h md s (patchMaybeDangling o)
  | none, _ => True.intro
  | some _, ⟨p, hp⟩ => ⟨p, hp.1, hp.2.1, fun _ hz => Bool.noConfusion hz⟩

theorem valid_pointee_facts (h : HeapState) (opt : Bool) : ∀ (ty : Ty) (md : Bool) (s : Slot),
    validSlot h md ty s = true → PointeeFacts h md s (pointeeInfoAt opt ty) := by
  intro ty
  induction ty with
  | ref m t =>
    intro md s hv
    cases s with
    | uninit => exact Bool.noConfusion hv
    | ptr p => exact pointeeFacts_ref h opt md m t p hv
  | wrap w inner ih =>
    intro md s hv
    cases w with
    | maybeUninit => exact True.intro
    | plain =>
      have hi := ih (md || false) s hv
      rw [or_false_eq] at hi
      exact hi
    | manuallyDrop =>
      have hi := ih (md || true) s hv
      rw [or_true_eq] at hi
      exact pointeeFacts_patch h md s (pointeeInfoAt opt inner) hi
    | maybeDangling =>
      have hi := ih (md || true) s hv
      rw [or_true_eq] at hi
      exact pointeeFacts_patch h md s (pointeeInfoAt opt inner) hi
    | coroutine =>
      have hi := ih (md || true) s hv
      rw [or_true_eq] at hi
      exact pointeeFacts_patch h md s (pointeeInfoAt opt inner) hi

/-- Entry facts for a non-null pointer, from the alignment and size recorded in
`ArgAttrs`.  Covers both `get_attrs` revisions. -/
theorem lower_sound_ptr (h : HeapState) (p : Ptr) (hnn : nonNull p = true) (opt ge23 : Bool) :
    ∀ (a : ArgAttrs), (∀ n, a.pointeeAlign = some n → aligned n p = true) →
      (isZero a.pointeeSize = false → derefable h p a.pointeeSize = true) →
      attrsHold h (lowerPost opt ge23 a) (.ptr p) = true ∧
        attrsHold h (lowerPre opt a) (.ptr p) = true := by
  intro a
  cases a with
  | mk noUndef nonNull' noAlias noFree readOnly capturesReadOnly pointeeSize pointeeAlign =>
    intro hal hd
    have hal' : alignHolds p pointeeAlign = true := by
      cases pointeeAlign with
      | none => rfl
      | some n => exact hal n rfl
    cases hz : isZero pointeeSize with
    | true =>
      cases opt <;> cases ge23 <;> cases nonNull' <;> cases noFree <;>
        simp [attrsHold, lowerPost, lowerPre, optimizedAttrs, unoptimizedAttrs, derefHolds,
          derefOrNullHolds, hz, hnn, hal']
    | false =>
      have hd' : derefable h p pointeeSize = true := hd hz
      cases opt <;> cases ge23 <;> cases nonNull' <;> cases noFree <;>
        simp [attrsHold, lowerPost, lowerPre, optimizedAttrs, unoptimizedAttrs, derefHolds,
          derefOrNullHolds, hz, hnn, hal', hd']

theorem lower_sound_empty (h : HeapState) (s : Slot) (opt ge23 : Bool) :
    attrsHold h (lowerPost opt ge23 emptyArgAttrs) s = true ∧
      attrsHold h (lowerPre opt emptyArgAttrs) s = true := by
  cases s <;> cases opt <;> cases ge23 <;> exact ⟨rfl, rfl⟩

/-- **Theorem 1a.**  For every type in the family, every heap, both optimisation levels,
both LLVM generations and both compiler revisions: every value that satisfies the
validity invariant of the type satisfies every value-level fact asserted by the emitted
parameter attributes (`noundef`, `nonnull`, `align`, `dereferenceable`,
`dereferenceable_or_null`). -/
theorem lowering_sound_entry (h : HeapState) (opt ge23 : Bool) (ty : Ty) (s : Slot)
    (hv : validSlot h false ty s = true) :
    attrsHold h (llvmParamAttrs opt ge23 ty) s = true ∧
      attrsHold h (llvmParamAttrsPre opt ty) s = true := by
  unfold llvmParamAttrs llvmParamAttrsPre argAttrs
  cases hu : (scalarOf ty).uninitValid with
  | true => exact lower_sound_empty h s opt ge23
  | false =>
    cases valid_ptr_of_init h ty false s hv hu with
    | intro p hp =>
      have hs : s = .ptr p := hp.1
      subst hs
      have hpf := valid_pointee_facts h opt ty false (.ptr p) hv
      cases hpi : pointeeInfoAt opt ty with
      | none =>
        exact lower_sound_ptr h p hp.2 opt ge23 _ (fun n hn => by cases hn)
          (fun hz => Bool.noConfusion hz)
      | some info =>
        rw [hpi] at hpf
        cases hpf with
        | intro q hq =>
          have hqp : p = q := Slot.ptr.inj hq.1
          subst hqp
          refine lower_sound_ptr h p hp.2 opt ge23 _ ?_ (fun hz => hq.2.2 rfl hz)
          intro n hn
          have hn' : alignAttr info.align = some n := hn
          have hn'' : info.align = n := alignAttr_eq_some hn'
          subst hn''
          exact hq.2.1

/-! ## Theorem 2: the `Option` niche -/

/-- Null is outside the valid range and uninitialized bytes are not allowed, so null is
available as a niche. -/
noncomputable def hasNullNiche (ty : Ty) : Bool :=
  !(scalarOf ty).uninitValid && (scalarOf ty).rangeExcludesZero

/-- `size_of::<Option<T>>()` for the pointer-sized `T` of this family. -/
noncomputable def optionSize (ty : Ty) : Nat :=
  match hasNullNiche ty with
  | true => 8
  | false => 16

theorem option_sizes_of_rows : rows.map optionSize = [8, 8, 8, 8, 8, 8, 8, 8, 16] := by
  decide

/-- No non-union wrapper changes the niche: `MaybeDangling`, `ManuallyDrop`, coroutine
state and plain wrappers all keep `Option` at 8 bytes when the wrapped type has it. -/
theorem niche_preserved (w : Wrapper) (inner : Ty) (hw : w.isUnion = false) :
    optionSize (.wrap w inner) = optionSize inner := by
  cases w with
  | maybeUninit => exact Bool.noConfusion hw
  | plain => rfl
  | manuallyDrop => rfl
  | maybeDangling => rfl
  | coroutine => rfl

/-- A union wrapper removes the niche whatever it wraps. -/
theorem niche_lost_under_union (inner : Ty) : optionSize (.wrap .maybeUninit inner) = 16 :=
  rfl

/-- Semantic side of the niche: when the lowering reports a null niche, the null pointer
is not a valid value, in or out of a maybe-dangling context, on any heap. -/
theorem null_not_valid_of_niche (h : HeapState) : ∀ (ty : Ty) (md : Bool) (prov : Option Nat),
    hasNullNiche ty = true → validSlot h md ty (.ptr { addr := 0, alloc := prov }) = false := by
  intro ty
  induction ty with
  | ref m t =>
    intro md prov _
    rfl
  | wrap w inner ih =>
    intro md prov hn
    cases w with
    | maybeUninit => exact Bool.noConfusion hn
    | plain => exact ih (md || false) prov hn
    | manuallyDrop => exact ih (md || true) prov hn
    | maybeDangling => exact ih (md || true) prov hn
    | coroutine => exact ih (md || true) prov hn

/-- Niche encoding of `Option<T>`: `None` is the null pointer. -/
def encodeOption : Option Slot → Slot
  | none => .ptr { addr := 0, alloc := none }
  | some s => s

def decodeOption : Slot → Option Slot
  | .uninit => some .uninit
  | .ptr p =>
      match isZero p.addr with
      | true => none
      | false => some (.ptr p)

/-- With a null niche the 8-byte encoding is lossless on valid values. -/
theorem niche_roundtrip (h : HeapState) (ty : Ty) (md : Bool) (s : Slot)
    (hn : hasNullNiche ty = true) (hv : validSlot h md ty s = true) :
    decodeOption (encodeOption (some s)) = some s := by
  cases s with
  | uninit => rfl
  | ptr p =>
    cases p with
    | mk addr prov =>
      cases addr with
      | zero =>
        have hfalse := null_not_valid_of_niche h ty md prov hn
        rw [hfalse] at hv
        exact Bool.noConfusion hv
      | succ n => rfl

/-- Without the niche it is not: null is a valid `MaybeUninit<&u64>` and collides with
`None`, so `Option<MaybeUninit<&u64>>` needs a separate tag (16 bytes). -/
theorem niche_ambiguous_for_maybe_uninit (h : HeapState) (md : Bool) :
    validSlot h md row9 (.ptr { addr := 0, alloc := none }) = true ∧
      decodeOption (encodeOption (some (.ptr { addr := 0, alloc := none }))) = none ∧
      optionSize row9 = 16 ∧ optionSize row8 = 8 ∧ optionSize row7 = 8 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `Option<MaybeDangling<&u64>>` sits exactly at the `rawAligned` level: null (`None`)
or a non-null aligned pointer that may dangle. -/
theorem option_maybe_dangling_is_rawAligned (h : HeapState) (p : Ptr) :
    (isZero p.addr || validSlot h false row8 (.ptr p)) = (Level.rawAligned 8).admits h (.ptr p) := by
  cases p with
  | mk addr prov =>
    cases addr with
    | zero => rfl
    | succ n => exact and_true_eq (aligned 8 { addr := n + 1, alloc := prov })


/-! ## Theorem 1b: the call-time contract

One pointee, one call.  The state records whether the pointee is still allocated, its
current value, and the strongest permission held by pointers that are *not* derived from
the argument.  Undefined behaviour is `none`. -/

/-- The semantic kind of the pointer argument, read off the type alone. -/
inductive RefKind
  /-- `&T` with `T: Freeze`. -/
  | frozenShared
  /-- `&mut T` with `T: Unpin`. -/
  | uniqueMut
  /-- `&T` with `T: !Freeze`. -/
  | interiorMutShared
  /-- `&mut T` with `T: !Unpin`. -/
  | pinnedMut
  /-- Anything under a maybe-dangling-like wrapper or a union. -/
  | mayDangle
  deriving DecidableEq, Repr

noncomputable def kindOf : Ty → RefKind
  | .ref .shared t =>
      match t.freeze with
      | true => .frozenShared
      | false => .interiorMutShared
  | .ref .mut t =>
      match t.unpin with
      | true => .uniqueMut
      | false => .pinnedMut
  | .wrap w inner =>
      match w.isUnion, w.isLikeMaybeDangling with
      | true, _ => .mayDangle
      | false, true => .mayDangle
      | false, false => kindOf inner

def isStrong : RefKind → Bool
  | .frozenShared => true
  | .uniqueMut => true
  | .interiorMutShared => false
  | .pinnedMut => false
  | .mayDangle => false

def RefKind.isFrozenShared : RefKind → Bool
  | .frozenShared => true
  | .uniqueMut => false
  | .interiorMutShared => false
  | .pinnedMut => false
  | .mayDangle => false

/-- The callee may write through every kind of argument except `&Freeze`. -/
def RefKind.calleeMayWrite : RefKind → Bool
  | .frozenShared => false
  | .uniqueMut => true
  | .interiorMutShared => true
  | .pinnedMut => true
  | .mayDangle => true

/-- Strongest permission held on the pointee by pointers not derived from the argument. -/
inductive OtherPerm
  /-- No such pointer. -/
  | none
  /-- Shared read-only aliases. -/
  | readOnly
  /-- Shared read-write aliases (interior mutability); their owner may also free. -/
  | cell
  /-- An exclusive alias that is being written through; its owner may also free. -/
  | uniqueActive
  /-- That exclusive alias after a read through another pointer: no longer writable. -/
  | uniqueFrozen
  deriving DecidableEq, Repr

structure CallState where
  live : Bool
  other : OtherPerm
  val : Nat
  deriving DecidableEq, Repr

inductive Ev
  /-- Read through the argument (or a pointer derived from it). -/
  | calleeRead
  /-- Write through the argument. -/
  | calleeWrite (v : Nat)
  /-- Read through a pointer not derived from the argument. -/
  | otherRead
  /-- Write through a pointer not derived from the argument. -/
  | otherWrite (v : Nat)
  /-- Deallocation through a pointer not derived from the argument. -/
  | otherFree
  deriving DecidableEq, Repr

def Ev.isForeignWrite : Ev → Bool
  | .otherWrite _ => true
  | .calleeRead => false
  | .calleeWrite _ => false
  | .otherRead => false
  | .otherFree => false

def Ev.isFree : Ev → Bool
  | .otherFree => true
  | .calleeRead => false
  | .calleeWrite _ => false
  | .otherRead => false
  | .otherWrite _ => false

def Ev.isCalleeWrite : Ev → Bool
  | .calleeWrite _ => true
  | .calleeRead => false
  | .otherRead => false
  | .otherWrite _ => false
  | .otherFree => false

/-- A read through the argument is a foreign read for an exclusive alias and freezes it. -/
def afterCalleeRead : OtherPerm → OtherPerm
  | .uniqueActive => .uniqueFrozen
  | .none => .none
  | .readOnly => .readOnly
  | .cell => .cell
  | .uniqueFrozen => .uniqueFrozen

/-- A write through the argument disables every alias except interior-mutable ones. -/
def afterCalleeWrite : OtherPerm → OtherPerm
  | .cell => .cell
  | .none => .none
  | .readOnly => .none
  | .uniqueActive => .none
  | .uniqueFrozen => .none

def otherMayRead : OtherPerm → Bool
  | .none => false
  | .readOnly => true
  | .cell => true
  | .uniqueActive => true
  | .uniqueFrozen => true

def otherMayWriteOrFree : OtherPerm → Bool
  | .cell => true
  | .uniqueActive => true
  | .none => false
  | .readOnly => false
  | .uniqueFrozen => false

def guardState (b : Bool) (s : CallState) : Option CallState :=
  match b with
  | true => some s
  | false => none

def step (k : RefKind) (s : CallState) : Ev → Option CallState
  | .calleeRead => guardState s.live { s with other := afterCalleeRead s.other }
  | .calleeWrite v =>
      guardState (s.live && k.calleeMayWrite) { s with val := v, other := afterCalleeWrite s.other }
  | .otherRead => guardState (s.live && otherMayRead s.other) s
  | .otherWrite v => guardState (s.live && otherMayWriteOrFree s.other) { s with val := v }
  | .otherFree => guardState (s.live && otherMayWriteOrFree s.other) { s with live := false }

noncomputable def run (k : RefKind) : CallState → List Ev → Option CallState
  | s, [] => some s
  | s, e :: rest => (step k s e).bind (fun s' => run k s' rest)

/-- States in which a call may start, by kind.  `&Freeze`: live, other pointers at most
read-only.  `&mut Unpin`: live, no other pointer.  `&!Freeze` and `&mut !Unpin`: live,
with any alias configuration.  Maybe-dangling: anything, including already freed. -/
def admissibleInit : RefKind → CallState → Bool
  | .frozenShared, s =>
      s.live && (match s.other with
        | .none => true
        | .readOnly => true
        | .cell => false
        | .uniqueActive => false
        | .uniqueFrozen => false)
  | .uniqueMut, s =>
      s.live && (match s.other with
        | .none => true
        | .readOnly => false
        | .cell => false
        | .uniqueActive => false
        | .uniqueFrozen => false)
  | .interiorMutShared, s => s.live
  | .pinnedMut, s => s.live
  | .mayDangle, _ => true

theorem or_false_split {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first
    | exact ⟨rfl, rfl⟩
    | exact Bool.noConfusion h

theorem or_false_intro {a b : Bool} (ha : a = false) (hb : b = false) : (a || b) = false := by
  subst ha
  subst hb
  rfl

/-- For the two strong kinds every defined step keeps the state admissible, is neither a
foreign write nor a free, is not a callee write when the argument is `&Freeze`, and
leaves the value alone unless it is a callee write. -/
theorem step_strong (k : RefKind) (hk : isStrong k = true) (s s' : CallState) (e : Ev)
    (hs : admissibleInit k s = true) (hstep : step k s e = some s') :
    admissibleInit k s' = true ∧ e.isForeignWrite = false ∧ e.isFree = false ∧
      (k.isFrozenShared = true → e.isCalleeWrite = false) ∧
      (e.isCalleeWrite = false → s'.val = s.val) := by
  cases s with
  | mk live other val =>
    cases k <;> first
      | exact Bool.noConfusion hk
      | (cases live <;> cases other <;> first
          | exact Bool.noConfusion hs
          | (cases e <;> first
              | (cases hstep; exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩)
              | (cases hstep; exact ⟨rfl, rfl, rfl, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩)
              | cases hstep))

theorem strong_live (k : RefKind) (hk : isStrong k = true) (s : CallState)
    (hs : admissibleInit k s = true) : s.live = true := by
  cases k <;> first
    | exact Bool.noConfusion hk
    | exact and_left hs

/-- Along every defined execution of a strong kind: no write through foreign pointers,
no deallocation, the pointee is live at the end, `&Freeze` is never written through, and
the value changes only by callee writes. -/
theorem run_strong (k : RefKind) (hk : isStrong k = true) : ∀ (tr : List Ev) (s s' : CallState),
    admissibleInit k s = true → run k s tr = some s' →
      tr.any Ev.isForeignWrite = false ∧ tr.any Ev.isFree = false ∧ s'.live = true ∧
        (k.isFrozenShared = true → tr.any Ev.isCalleeWrite = false) ∧
        (tr.any Ev.isCalleeWrite = false → s'.val = s.val) := by
  intro tr
  induction tr with
  | nil =>
    intro s s' hs hrun
    cases hrun
    exact ⟨rfl, rfl, strong_live k hk s hs, fun _ => rfl, fun _ => rfl⟩
  | cons e rest ih =>
    intro s s' hs hrun
    have hrun' : (step k s e).bind (fun s1 => run k s1 rest) = some s' := hrun
    cases hst : step k s e with
    | none =>
      rw [hst] at hrun'
      cases hrun'
    | some s1 =>
      rw [hst] at hrun'
      have hstep := step_strong k hk s s1 e hs hst
      have hrest := ih s1 s' hstep.1 hrun'
      refine ⟨or_false_intro hstep.2.1 hrest.1, or_false_intro hstep.2.2.1 hrest.2.1,
        hrest.2.2.1, fun hf => or_false_intro (hstep.2.2.2.1 hf) (hrest.2.2.2.1 hf), ?_⟩
      intro hcw
      have hsplit := or_false_split hcw
      exact (hrest.2.2.2.2 hsplit.2).trans (hstep.2.2.2.2 hsplit.1)

/-- For a strong kind a speculative read at function entry is unobservable: the
execution with the extra read has exactly the same outcome. -/
theorem spurious_read_sound (k : RefKind) (hk : isStrong k = true) (s : CallState)
    (hs : admissibleInit k s = true) (tr : List Ev) :
    run k s (.calleeRead :: tr) = run k s tr := by
  cases s with
  | mk live other val =>
    cases k <;> first
      | exact Bool.noConfusion hk
      | (cases live <;> cases other <;> first
          | exact Bool.noConfusion hs
          | rfl)

/-! ### The lowering assigns the strong attributes only to the strong kinds -/

def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | true, false => false
  | false, true => false

theorem boolEq_right {a b : Bool} (h : boolEq a b = true) (ha : a = true) : b = true := by
  subst ha
  cases b
  · exact Bool.noConfusion h
  · rfl

theorem or_resolve {a b : Bool} (h : (a || b) = true) (hb : b = false) : a = true := by
  subst hb
  cases a
  · exact Bool.noConfusion h
  · rfl

/-- Agreement between the `PointeeInfo` computed by the lowering and the kind read off
the type: `noalias`-capable exactly for the strong kinds, read-only exactly for
`&Freeze`, and a zero size for every other kind. -/
def infoAgrees : Option PointeeInfo → RefKind → Bool
  | none, _ => true
  | some info, k =>
      boolEq (strongKind info.safe) (isStrong k) &&
        boolEq (frozenSharedKind info.safe) k.isFrozenShared &&
        (isStrong k || isZero info.size)

theorem infoAgrees_patch : ∀ (o : Option PointeeInfo),
    infoAgrees (patchMaybeDangling o) .mayDangle = true
  | none => rfl
  | some _ => rfl

theorem info_agrees : ∀ (ty : Ty), infoAgrees (pointeeInfoAt true ty) (kindOf ty) = true := by
  intro ty
  induction ty with
  | ref m t => cases m <;> cases t <;> rfl
  | wrap w inner ih =>
    cases w with
    | maybeUninit => rfl
    | plain => exact ih
    | manuallyDrop => exact infoAgrees_patch (pointeeInfoAt true inner)
    | maybeDangling => exact infoAgrees_patch (pointeeInfoAt true inner)
    | coroutine => exact infoAgrees_patch (pointeeInfoAt true inner)

theorem argAttrs_kind (ty : Ty) :
    ((argAttrs true ty).noAlias = true → isStrong (kindOf ty) = true) ∧
      ((argAttrs true ty).noFree = true → isStrong (kindOf ty) = true) ∧
      (isZero (argAttrs true ty).pointeeSize = false → isStrong (kindOf ty) = true) ∧
      ((argAttrs true ty).readOnly = true → (kindOf ty).isFrozenShared = true) := by
  have hag := info_agrees ty
  unfold argAttrs
  cases hu : (scalarOf ty).uninitValid with
  | true =>
    exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
      fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | false =>
    cases hpi : pointeeInfoAt true ty with
    | none =>
      exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
        fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
    | some info =>
      rw [hpi] at hag
      have h1 : boolEq (strongKind info.safe) (isStrong (kindOf ty)) = true :=
        and_left (and_left hag)
      have h2 : boolEq (frozenSharedKind info.safe) (kindOf ty).isFrozenShared = true :=
        and_right (and_left hag)
      have h3 : (isStrong (kindOf ty) || isZero info.size) = true := and_right hag
      exact ⟨fun h => boolEq_right h1 h, fun h => boolEq_right h1 h,
        fun hz => or_resolve h3 hz, fun h => boolEq_right h2 h⟩

theorem lowerPost_strong (ge23 sk : Bool) : ∀ (a : ArgAttrs),
    (a.noAlias = true → sk = true) → (a.noFree = true → sk = true) →
      (isZero a.pointeeSize = false → sk = true) →
      ((lowerPost true ge23 a).noalias = true → sk = true) ∧
        ((lowerPost true ge23 a).nofree = true → sk = true) ∧
        ((lowerPost true ge23 a).dereferenceable.isSome = true → sk = true) ∧
        ((lowerPost true ge23 a).dereferenceableOrNull.isSome = true → sk = true) := by
  intro a
  cases a with
  | mk noUndef nonNull' noAlias noFree readOnly capturesReadOnly pointeeSize pointeeAlign =>
    intro h1 h2 h3
    refine ⟨h1, h2, ?_, ?_⟩
    · cases hz : isZero pointeeSize with
      | false => exact fun _ => h3 hz
      | true =>
        cases ge23 <;> cases noFree <;> cases nonNull' <;>
          simp [lowerPost, optimizedAttrs, hz]
    · cases hz : isZero pointeeSize with
      | false => exact fun _ => h3 hz
      | true =>
        cases ge23 <;> cases noFree <;> cases nonNull' <;>
          simp [lowerPost, optimizedAttrs, hz]

theorem isFrozenShared_eq (k : RefKind) (h : k.isFrozenShared = true) : k = .frozenShared := by
  cases k <;> first
    | rfl
    | exact Bool.noConfusion h

/-- `noalias`, `nofree`, `dereferenceable` and `dereferenceable_or_null` are emitted only
for the strong kinds, and `readonly` only for `&Freeze`; for every type in the family. -/
theorem attrs_only_for_strong_kinds (ge23 : Bool) (ty : Ty) :
    ((llvmParamAttrs true ge23 ty).noalias = true → isStrong (kindOf ty) = true) ∧
      ((llvmParamAttrs true ge23 ty).nofree = true → isStrong (kindOf ty) = true) ∧
      ((llvmParamAttrs true ge23 ty).dereferenceable.isSome = true →
        isStrong (kindOf ty) = true) ∧
      ((llvmParamAttrs true ge23 ty).dereferenceableOrNull.isSome = true →
        isStrong (kindOf ty) = true) ∧
      ((llvmParamAttrs true ge23 ty).readonly = true → kindOf ty = .frozenShared) := by
  have hk := argAttrs_kind ty
  have hl := lowerPost_strong ge23 (isStrong (kindOf ty)) (argAttrs true ty) hk.1 hk.2.1 hk.2.2.1
  exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, fun h => isFrozenShared_eq _ (hk.2.2.2 h)⟩

/-- **Theorem 1b.**  For every type in the family, every state in which a call on an
argument of that type may start, and every sequence of events:

* if the lowering emits `dereferenceable`, a speculative read at entry does not change
  the outcome;
* if it emits `noalias` or `nofree`, then along a defined execution no foreign pointer
  writes or frees the pointee, and the pointee is live at the end;
* if it emits `readonly`, a defined execution contains no write through the argument,
  and so the value at the end is the value at entry. -/
theorem lowering_sound_call (ge23 : Bool) (ty : Ty) (s : CallState)
    (hs : admissibleInit (kindOf ty) s = true) (tr : List Ev) :
    ((llvmParamAttrs true ge23 ty).dereferenceable.isSome = true →
        run (kindOf ty) s (.calleeRead :: tr) = run (kindOf ty) s tr) ∧
      (((llvmParamAttrs true ge23 ty).noalias = true ∨
          (llvmParamAttrs true ge23 ty).nofree = true) →
        ∀ s', run (kindOf ty) s tr = some s' →
          tr.any Ev.isForeignWrite = false ∧ tr.any Ev.isFree = false ∧ s'.live = true) ∧
      ((llvmParamAttrs true ge23 ty).readonly = true →
        ∀ s', run (kindOf ty) s tr = some s' →
          tr.any Ev.isCalleeWrite = false ∧ s'.val = s.val) := by
  have ha := attrs_only_for_strong_kinds ge23 ty
  refine ⟨fun hd => spurious_read_sound _ (ha.2.2.1 hd) s hs tr, ?_, ?_⟩
  · intro hor s' hrun
    have hstrong : isStrong (kindOf ty) = true := by
      cases hor with
      | inl h => exact ha.1 h
      | inr h => exact ha.2.1 h
    have hr := run_strong _ hstrong tr s s' hs hrun
    exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
  · intro hro s' hrun
    have hfs : kindOf ty = .frozenShared := ha.2.2.2.2 hro
    have hstrong : isStrong (kindOf ty) = true := by
      rw [hfs]
      rfl
    have hr := run_strong _ hstrong tr s s' hs hrun
    have hfs' : (kindOf ty).isFrozenShared = true := by
      rw [hfs]
      rfl
    exact ⟨hr.2.2.2.1 hfs', hr.2.2.2.2 (hr.2.2.2.1 hfs')⟩

/-! ## Theorem 3: SROA -/

inductive Stmt
  /-- Deallocate allocation `alloc`. -/
  | free (alloc : Nat)
  /-- A whole-value typed copy of the observed value at type `ty`; defined iff the value
  satisfies the validity invariant of `ty` in the current heap. -/
  | copyAt (ty : Ty)

noncomputable def freeAt : HeapState → Nat → HeapState
  | [], _ => []
  | a :: rest, 0 => { a with state := .freed } :: rest
  | a :: rest, i + 1 => a :: freeAt rest i

def guardHeap (b : Bool) (k : Option HeapState) : Option HeapState :=
  match b with
  | true => k
  | false => none

/-- Run a statement list on one observed value; `none` is undefined behaviour. -/
noncomputable def exec (s : Slot) : HeapState → List Stmt → Option HeapState
  | h, [] => some h
  | h, .free i :: rest => exec s (freeAt h i) rest
  | h, .copyAt ty :: rest => guardHeap (validSlot h false ty s) (exec s h rest)

/-- What flattening a wrapper-typed local does to a whole-value copy of it: the copy is
re-expressed at the type of the wrapped field, unless the wrapper is excluded. -/
def sroaStmt (excluded : Wrapper → Bool) : Stmt → Stmt
  | .free i => .free i
  | .copyAt (.ref m t) => .copyAt (.ref m t)
  | .copyAt (.wrap w inner) =>
      match excluded w with
      | true => .copyAt (.wrap w inner)
      | false => .copyAt inner

/-- `is_excluded_ty` at the later revision, restricted to `Wrapper`:
`ty.is_union() || ty.is_like_maybe_dangling()`. -/
def sroaExcludedPost (w : Wrapper) : Bool := w.isUnion || w.isLikeMaybeDangling

/-- `is_excluded_ty` at the earlier revision, restricted to `Wrapper`: `ty.is_union()`. -/
def sroaExcludedPre (w : Wrapper) : Bool := w.isUnion

/-- Peeling wrapper `w` off a typed copy never turns a defined copy into an undefined
one. -/
def sroaValid (w : Wrapper) : Prop :=
  ∀ (h : HeapState) (inner : Ty) (s : Slot),
    validSlot h false (.wrap w inner) s = true → validSlot h false inner s = true

def freedHeap : HeapState := [{ base := 8, size := 8, state := .freed }]

def danglingSlot : Slot := .ptr { addr := 8, alloc := some 0 }

theorem peel_unsound_of_dangling (w : Wrapper)
    (hw : validSlot freedHeap false (.wrap w row1) danglingSlot = true) : ¬ sroaValid w :=
  fun hp => Bool.noConfusion (hp freedHeap row1 danglingSlot hw)

/-- **Theorem 3 (conditional soundness).**  Peeling is sound exactly for the wrappers the
later exclusion predicate does not exclude. -/
theorem sroaValid_iff (w : Wrapper) : sroaValid w ↔ sroaExcludedPost w = false := by
  cases w with
  | plain => exact ⟨fun _ => rfl, fun _ _ _ _ hv => hv⟩
  | manuallyDrop =>
    exact ⟨fun hp => absurd hp (peel_unsound_of_dangling _ rfl), fun h => Bool.noConfusion h⟩
  | maybeDangling =>
    exact ⟨fun hp => absurd hp (peel_unsound_of_dangling _ rfl), fun h => Bool.noConfusion h⟩
  | coroutine =>
    exact ⟨fun hp => absurd hp (peel_unsound_of_dangling _ rfl), fun h => Bool.noConfusion h⟩
  | maybeUninit =>
    exact ⟨fun hp => Bool.noConfusion (hp [] row1 .uninit rfl), fun h => Bool.noConfusion h⟩

/-- The earlier predicate admits an unsound peel for each of the three
maybe-dangling-like families. -/
theorem pre_predicate_admits_unsound_peel (w : Wrapper) (hw : w.isLikeMaybeDangling = true) :
    sroaExcludedPre w = false ∧ ¬ sroaValid w := by
  cases w with
  | plain => exact Bool.noConfusion hw
  | maybeUninit => exact Bool.noConfusion hw
  | manuallyDrop => exact ⟨rfl, peel_unsound_of_dangling _ rfl⟩
  | maybeDangling => exact ⟨rfl, peel_unsound_of_dangling _ rfl⟩
  | coroutine => exact ⟨rfl, peel_unsound_of_dangling _ rfl⟩

/-- With the later predicate the rewrite preserves every defined execution. -/
theorem sroa_post_preserves (s : Slot) : ∀ (prog : List Stmt) (h h' : HeapState),
    exec s h prog = some h' → exec s h (prog.map (sroaStmt sroaExcludedPost)) = some h' := by
  intro prog
  induction prog with
  | nil =>
    intro h h' hx
    exact hx
  | cons st rest ih =>
    intro h h' hx
    cases st with
    | free i => exact ih (freeAt h i) h' hx
    | copyAt ty =>
      have hx' : guardHeap (validSlot h false ty s) (exec s h rest) = some h' := hx
      cases hv : validSlot h false ty s with
      | false =>
        rw [hv] at hx'
        cases hx'
      | true =>
        rw [hv] at hx'
        have hrest := ih h h' hx'
        cases ty with
        | ref m t =>
          show guardHeap (validSlot h false (.ref m t) s)
            (exec s h (rest.map (sroaStmt sroaExcludedPost))) = some h'
          rw [hv]
          exact hrest
        | wrap w inner =>
          cases w with
          | plain =>
            have hv' : validSlot h false inner s = true := hv
            show guardHeap (validSlot h false inner s)
              (exec s h (rest.map (sroaStmt sroaExcludedPost))) = some h'
            rw [hv']
            exact hrest
          | manuallyDrop =>
            show guardHeap (validSlot h false (.wrap .manuallyDrop inner) s)
              (exec s h (rest.map (sroaStmt sroaExcludedPost))) = some h'
            rw [hv]
            exact hrest
          | maybeDangling =>
            show guardHeap (validSlot h false (.wrap .maybeDangling inner) s)
              (exec s h (rest.map (sroaStmt sroaExcludedPost))) = some h'
            rw [hv]
            exact hrest
          | coroutine =>
            show guardHeap (validSlot h false (.wrap .coroutine inner) s)
              (exec s h (rest.map (sroaStmt sroaExcludedPost))) = some h'
            rw [hv]
            exact hrest
          | maybeUninit =>
            show guardHeap (validSlot h false (.wrap .maybeUninit inner) s)
              (exec s h (rest.map (sroaStmt sroaExcludedPost))) = some h'
            rw [hv]
            exact hrest

/-! ## Sharpness: three constructive counterexamples -/

def ce1Heap : HeapState := [{ base := 8, size := 8, state := .live }]

def ce1Slot : Slot := .ptr { addr := 8, alloc := some 0 }

/-- Copy the wrapper while its target is live, free the target, copy the wrapper again. -/
def ce1Prog (w : Wrapper) : List Stmt :=
  [.copyAt (.wrap w row1), .free 0, .copyAt (.wrap w row1)]

/-- **Counterexample 1.**  For `MaybeDangling`, `ManuallyDrop` and coroutine state: the
program is defined; flattening under the earlier exclusion predicate makes it undefined
(the second copy now has type `&u64` and its target is freed); the later predicate
leaves the program unchanged.  The hoisted `&u64` would moreover be lowered with
`dereferenceable(8)`, whose entry fact is false on the freed heap, while the attributes
of the wrapped type remain true. -/
theorem ce1_sroa_flattening_maybe_dangling_introduces_dangling_ref_ub :
    ((exec ce1Slot ce1Heap (ce1Prog .maybeDangling)).isSome = true ∧
        exec ce1Slot ce1Heap ((ce1Prog .maybeDangling).map (sroaStmt sroaExcludedPre)) = none ∧
        (ce1Prog .maybeDangling).map (sroaStmt sroaExcludedPost) = ce1Prog .maybeDangling) ∧
      ((exec ce1Slot ce1Heap (ce1Prog .manuallyDrop)).isSome = true ∧
        exec ce1Slot ce1Heap ((ce1Prog .manuallyDrop).map (sroaStmt sroaExcludedPre)) = none ∧
        (ce1Prog .manuallyDrop).map (sroaStmt sroaExcludedPost) = ce1Prog .manuallyDrop) ∧
      ((exec ce1Slot ce1Heap (ce1Prog .coroutine)).isSome = true ∧
        exec ce1Slot ce1Heap ((ce1Prog .coroutine).map (sroaStmt sroaExcludedPre)) = none ∧
        (ce1Prog .coroutine).map (sroaStmt sroaExcludedPost) = ce1Prog .coroutine) ∧
      ((llvmParamAttrs true true row1).dereferenceable = some 8 ∧
        attrsHold (freeAt ce1Heap 0) (llvmParamAttrs true true row1) ce1Slot = false ∧
        attrsHold (freeAt ce1Heap 0) (llvmParamAttrs true true row8) ce1Slot = true) := by
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

def ce2Exclusive : CallState := { live := true, other := .uniqueActive, val := 0 }

def ce2Cell : CallState := { live := true, other := .cell, val := 0 }

/-- **Counterexample 2.**  For `&UnsafeCell<u64>` and `&mut PinnedU64` the lowering emits
none of `noalias`, `nofree`, `readonly`, `dereferenceable`, and each of them would be
unsound for the kind: a speculative entry read turns a defined execution into an
undefined one; a defined execution frees the pointee during the call; and a defined
execution has a foreign write between two reads through the argument. -/
theorem ce2_dereferenceable_on_shared_unsafecell_or_pinned_mut_unsound (k : RefKind)
    (hk : k = .interiorMutShared ∨ k = .pinnedMut) :
    (llvmParamAttrs true true row3 = attrsAlignedNonNull ∧
        llvmParamAttrs true true row5 = attrsAlignedNonNull ∧
        kindOf row3 = .interiorMutShared ∧ kindOf row5 = .pinnedMut) ∧
      (admissibleInit k ce2Exclusive = true ∧
        (run k ce2Exclusive [.otherWrite 1]).isSome = true ∧
        run k ce2Exclusive [.calleeRead, .otherWrite 1] = none) ∧
      (admissibleInit k ce2Cell = true ∧
        (run k ce2Cell [.calleeRead, .otherFree]).map (fun s => s.live) = some false) ∧
      ((run k ce2Cell [.calleeRead, .otherWrite 1, .calleeRead]).map (fun s => s.val) = some 1 ∧
        ([Ev.calleeRead, Ev.otherWrite 1, Ev.calleeRead].any Ev.isCalleeWrite) = false) := by
  cases hk with
  | inl h =>
    subst h
    decide
  | inr h =>
    subst h
    decide

/-- The same for a maybe-dangling argument whose target is already freed at entry: the
empty execution is defined, the speculative read is not. -/
theorem ce2_maybe_dangling_spurious_read_unsound :
    admissibleInit (kindOf row8) { live := false, other := .none, val := 0 } = true ∧
      (run (kindOf row8) { live := false, other := .none, val := 0 } []).isSome = true ∧
      run (kindOf row8) { live := false, other := .none, val := 0 } [.calleeRead] = none := by
  decide

/-- **Counterexample 3.**  Inside `MaybeDangling` (and `ManuallyDrop`) the scalar
validity is retained: on every heap, in or out of a maybe-dangling context, the null
pointer and a misaligned pointer are invalid, and they falsify the `nonnull` and
`align 8` attributes the lowering still emits.  An aligned non-null pointer with no
allocation behind it is valid. -/
theorem ce3_null_or_unaligned_inside_maybe_dangling_violates_retained_scalar_validity
    (h : HeapState) (md : Bool) (prov : Option Nat) :
    (validSlot h md row8 (.ptr { addr := 0, alloc := prov }) = false ∧
        validSlot h md row8 (.ptr { addr := 1, alloc := prov }) = false ∧
        validSlot h md row7 (.ptr { addr := 0, alloc := prov }) = false ∧
        validSlot h md row7 (.ptr { addr := 1, alloc := prov }) = false) ∧
      ((llvmParamAttrs true true row8).nonnull = true ∧
        (llvmParamAttrs true true row8).align = some 8 ∧
        attrsHold h (llvmParamAttrs true true row8) (.ptr { addr := 0, alloc := prov }) = false ∧
        attrsHold h (llvmParamAttrs true true row8) (.ptr { addr := 1, alloc := prov }) = false) ∧
      validSlot [] false row8 (.ptr { addr := 8, alloc := none }) = true :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## Axiom audit

Each command prints the axioms the named theorem depends on. -/

#print axioms matrix_post_llvm23_opt2
#print axioms matrix_post_llvm22_opt2
#print axioms matrix_pre_opt2
#print axioms matrix_opt0
#print axioms pre_eq_post_erase_nofree
#print axioms llvmParamAttrsPre_eq
#print axioms isLikeMaybeDangling_iff
#print axioms validSlot_mono
#print axioms validSlot_eq_level
#print axioms levels_of_rows
#print axioms level_chain
#print axioms level_chain_strict
#print axioms lowering_sound_entry
#print axioms option_sizes_of_rows
#print axioms niche_preserved
#print axioms niche_lost_under_union
#print axioms null_not_valid_of_niche
#print axioms niche_roundtrip
#print axioms niche_ambiguous_for_maybe_uninit
#print axioms option_maybe_dangling_is_rawAligned
#print axioms run_strong
#print axioms spurious_read_sound
#print axioms info_agrees
#print axioms attrs_only_for_strong_kinds
#print axioms lowering_sound_call
#print axioms sroaValid_iff
#print axioms pre_predicate_admits_unsound_peel
#print axioms sroa_post_preserves
#print axioms ce1_sroa_flattening_maybe_dangling_introduces_dangling_ref_ub
#print axioms ce2_dereferenceable_on_shared_unsafecell_or_pinned_mut_unsound
#print axioms ce2_maybe_dangling_spurious_read_unsound
#print axioms ce3_null_or_unaligned_inside_maybe_dangling_violates_retained_scalar_validity

end MaybeDanglingModel
