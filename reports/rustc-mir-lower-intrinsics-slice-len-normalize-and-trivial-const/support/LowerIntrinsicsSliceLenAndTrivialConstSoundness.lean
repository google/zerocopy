/-!
# Soundness Mechanization of `rustc` MIR `LowerIntrinsics`, `LowerSliceLenCalls`,
# `PostAnalysisNormalize`, and `trivial_const`

Standalone Lean 4 (`v4.34.1`) formalization establishing kernel-checked theorems
and refutation counterexamples for four `rustc_mir_transform` components audited
across `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`)
and `137d1d49458b73b7b85d2c1599d8730886d65e47` (HEAD):

1. `LowerIntrinsics` (`lower_intrinsics.rs`, 14 explicit match arms / 29 `sym::*` intrinsics):
   - Uninhabited `read_via_copy` and `transmute`/`transmute_unchecked` statement-before-
     `Unreachable` fault-kind preservation (`lowerIntrinsics_uninhabited_preserves_pre_ub`),
     plus counterexample refuting statement omission (`naive_uninhabited_drop_stmt_misclassifies_ub`).
   - Wide-pointer `aggregate_raw_ptr` <-> `UnOp::PtrMetadata` bijection
     (`aggregateRawPtr_ptrMetadata_bijection`) and `deref_pointer` validity boundaries
     for dangling `&[T]` references and invalid `dyn Trait` vtables.
   - `copy_nonoverlapping` and `assume` destination unit-write semantics (`137d1d49458b`
     fix over `14210df0e27c` omitted destination assignment).
   - `slice_get_unchecked` 4-way `*const`/`*mut`/`&`/`&mut` lowering soundness,
     pre-`Derefer` `!place.is_indirect()` and constant-index ICE preconditions, plus the
     `pair.0` non-indirect field-projection and `discriminant_value` broken-MIR
     counterexamples.
   - Complete block-level semantic soundness across all 14 arms (`lowerIntrinsics_sound_all_arms`).
2. `LowerSliceLenCalls` (`lower_slice_len.rs`):
   - Call-to-`UnOp::PtrMetadata` refinement (`lowerSliceLenCalls_refines_call`),
     opt-level / `FnPtr` / `CallSource` / diverging gates, and the `as_mut_preserves_cfg()`
     dropped-cleanup-edge CFG-cache counterexample.
3. `PostAnalysisNormalize` (`post_analysis_normalize.rs`) & `CleanupPostBorrowck`:
   - `OpaqueCast` projection elimination, hidden-type revelation soundness,
     `try_normalize` fallback under impossible clauses, and `user_type_annotations`
     clearing ordering.
4. `trivial_const` (`trivial_const.rs` + `lib.rs`):
   - Chained zero-pipeline constant evaluation equivalence to full CTFE
     (`trivialConst_eval_equiv_ctfe`).
   - Load-bearing soundness counterexamples for omitting `has_impossible_clauses`
     (`trivialConst_without_impossibleClauses_unsound_counterexample`), omitting
     `opaque_types_defined_by` / `body.has_opaque_types()`, omitting `!args.is_empty()`,
     and omitting `AnonConstKind::NonTypeSystemInline`.

Purity discipline: zero `sorry`, zero `Classical.choice`, zero `omega`,
zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `deriving`
(ensuring zero `._unsafe_rec` constants), compiling cleanly under
`-DwarningAsError=true`.
-/

namespace RustcMirLowerIntrinsicsSoundness

/-! ## Section 1: Core Identifiers, Types, Values, Memory, and Typed Faults -/

abbrev LocalId := Nat
abbrev BlockId := Nat
abbrev AllocId := Nat
abbrev VtableId := Nat
abbrev DefId := Nat
abbrev FieldIdx := Nat
abbrev OpaqueId := Nat

/-- Pointer kind for pointer/reference types (`*const`, `*mut`, `&`, `&mut`). -/
inductive PtrKind where
  | rawConst
  | rawMut
  | refShared
  | refMut

/-- Pointee unsizedness classification matching `rustc` pointer metadata kinds. -/
inductive PointeeKind where
  | sized (byteSize : Nat)
  | slice (elemSize : Nat)
  | dynTrait (expectedTrait : Nat)

/-- Pointer metadata payload matching `MemPlaceMeta`. -/
inductive PtrMeta where
  | none
  | sliceLen (len : Nat)
  | vtable (vid : VtableId)

/-- Minimal MIR type system capturing inhabitedness, byte sizes, pointers,
references, opaque types, and enums needed for the four passes. -/
inductive MirTy where
  | unit
  | bool
  | u32
  | usize
  | voidTy
  | uninhabitedSized (byteSize : Nat)
  | ptr (kind : PtrKind) (pointee : PointeeKind)
  | tupleU32Bool
  | ordering
  | enumTag
  | opaque (oid : OpaqueId)
  | structPair

def MirTy.byteSize : MirTy → Nat
  | .unit => 0
  | .bool => 1
  | .u32 => 4
  | .usize => 8
  | .voidTy => 0
  | .uninhabitedSized sz => sz
  | .ptr _ (.sized _) => 8
  | .ptr _ (.slice _) => 16
  | .ptr _ (.dynTrait _) => 16
  | .tupleU32Bool => 8
  | .ordering => 1
  | .enumTag => 1
  | .opaque _ => 8
  | .structPair => 12

def MirTy.isInhabited : MirTy → Bool
  | .voidTy => false
  | .uninhabitedSized _ => false
  | .tupleU32Bool => true
  | _ => true

def MirTy.hasOpaque : MirTy → Bool
  | .opaque _ => true
  | .tupleU32Bool => false
  | _ => false

/-- Exact operational fault taxonomy distinguishing memory-access UB, validity UB,
unreachable UB, `assume(false)` UB, unchecked-op overflow UB, transmute size
mismatch UB, uninitialized local UB, and compiler-internal ICE preconditions. -/
inductive FaultKind where
  | memAccessUb
  | invalidValueUb
  | unreachableUb
  | assumeFalseUb
  | overflowUb
  | sizeMismatchUb
  | icePrecondition
  | uninitLocalUb
  | unsupportedOp

/-- Concrete pointer representation with provenance/allocation tag, byte offset,
alignment witness, and optional wide metadata. -/
structure PtrVal where
  alloc : Option AllocId
  offset : Nat
  aligned : Bool
  ptrMeta : PtrMeta

/-- Runtime value domain for MIR evaluation. -/
inductive Val where
  | unit
  | bool (b : Bool)
  | int (n : Nat)
  | ptr (p : PtrVal)
  | pair (a b : Val)
  | tag (discr : Nat)
  | structPair (f0 f1 : Nat)
  | uninit

/-- Memory and runtime-check environment. -/
structure Mem where
  allocSize : AllocId → Option Nat
  vtableTrait : VtableId → Option Nat
  storeVal : AllocId → Nat → Val
  runtimeUbChecks : Bool
  runtimeOverflowChecks : Bool
  runtimeContractChecks : Bool

def Mem.writeAt (m : Mem) (aid : AllocId) (off : Nat) (v : Val) : Mem :=
  { m with
    storeVal := fun a o =>
      if Nat.beq a aid && Nat.beq o off then v else m.storeVal a o }

/-- Check whether a pointer supports a memory access of `accessSize` bytes.
Matches `check_ptr_access` / `check_and_deref_ptr` in `rustc_const_eval`:
zero-byte accesses short-circuit cleanly; non-zero accesses require a live
allocation with `offset + accessSize ≤ allocLen` and alignment. -/
def Mem.checkAccess (m : Mem) (p : PtrVal) (accessSize : Nat) : Except FaultKind Unit :=
  match accessSize with
  | 0 => .ok ()
  | _ + 1 =>
    match p.alloc with
    | none => .error .memAccessUb
    | some aid =>
      match m.allocSize aid with
      | none => .error .memAccessUb
      | some len =>
        if Nat.ble (p.offset + accessSize) len && p.aligned then
          .ok ()
        else
          .error .memAccessUb

/-- Validate a pointer value according to `InterpCx::deref_pointer`
(`compiler/rustc_const_eval/src/interpret/place.rs:468-538`).
- References (`&T`, `&mut T`): require live allocation, alignment, full pointee
  dereferenceability (`elemSize * len` for slices), and valid vtable for `dyn Trait`.
- Raw pointers (`*const T`, `*mut T`): for sized and slice pointees, data address
  validity is NOT checked; for `dyn Trait`, vtable validity IS checked. -/
def Mem.derefPointerCheck (m : Mem) (pk : PtrKind) (pt : PointeeKind) (p : PtrVal) :
    Except FaultKind Unit :=
  match pk with
  | .refShared | .refMut =>
    match p.alloc with
    | none => .error .invalidValueUb
    | some aid =>
      match m.allocSize aid with
      | none => .error .invalidValueUb
      | some len =>
        if !p.aligned then
          .error .invalidValueUb
        else
          match pt with
          | .sized sz =>
            if Nat.ble (p.offset + sz) len then .ok () else .error .invalidValueUb
          | .slice elemSz =>
            match p.ptrMeta with
            | .sliceLen n =>
              if Nat.ble (p.offset + elemSz * n) len then .ok () else .error .invalidValueUb
            | _ => .error .invalidValueUb
          | .dynTrait expectedTrait =>
            match p.ptrMeta with
            | .vtable vid =>
              match m.vtableTrait vid with
              | some tid =>
                if Nat.beq tid expectedTrait then .ok () else .error .invalidValueUb
              | none => .error .invalidValueUb
            | _ => .error .invalidValueUb
  | .rawConst | .rawMut =>
    match pt with
    | .sized _ => .ok ()
    | .slice _ =>
      match p.ptrMeta with
      | .sliceLen _ => .ok ()
      | _ => .error .invalidValueUb
    | .dynTrait expectedTrait =>
      match p.ptrMeta with
      | .vtable vid =>
        match m.vtableTrait vid with
        | some tid =>
          if Nat.beq tid expectedTrait then .ok () else .error .invalidValueUb
        | none => .error .invalidValueUb
      | _ => .error .invalidValueUb

/-- Type-validity check when producing a value of type `ty`
(`rust-lang/reference` `r[undefined.invalid]`). Producing any value of an
uninhabited type (`Void`, `UninhabitedSized`) is always `invalidValueUb`. -/
def checkValueValidity (ty : MirTy) (v : Val) : Except FaultKind Val :=
  match ty with
  | .voidTy => .error .invalidValueUb
  | .uninhabitedSized _ => .error .invalidValueUb
  | .unit =>
    match v with
    | .unit => .ok .unit
    | _ => .error .invalidValueUb
  | .bool =>
    match v with
    | .bool b => .ok (.bool b)
    | _ => .error .invalidValueUb
  | .u32 | .usize =>
    match v with
    | .int n => .ok (.int n)
    | _ => .error .invalidValueUb
  | .ptr _ _ =>
    match v with
    | .ptr p => .ok (.ptr p)
    | _ => .error .invalidValueUb
  | .tupleU32Bool =>
    match v with
    | .pair (.int n) (.bool b) => .ok (.pair (.int n) (.bool b))
    | _ => .error .invalidValueUb
  | .ordering =>
    match v with
    | .tag d => if Nat.ble d 2 then .ok (.tag d) else .error .invalidValueUb
    | _ => .error .invalidValueUb
  | .enumTag =>
    match v with
    | .tag d => .ok (.tag d)
    | _ => .error .invalidValueUb
  | .opaque _ => .ok v
  | .structPair =>
    match v with
    | .structPair a b => .ok (.structPair a b)
    | _ => .error .invalidValueUb

/-- Reading a value of type `ty` through a raw pointer `p`:
1. Checks memory access of `ty.byteSize` bytes (`memAccessUb` on null/dangling/OOB
   whenever `ty.byteSize > 0`).
2. Loads stored value (or `.unit` for 0-byte types).
3. Validates at `ty` (`invalidValueUb` on uninhabited types even when `byteSize = 0`). -/
def Mem.readViaPtr (m : Mem) (p : PtrVal) (ty : MirTy) : Except FaultKind Val :=
  match m.checkAccess p ty.byteSize with
  | .error e => .error e
  | .ok () =>
    let rawVal :=
      match ty.byteSize with
      | 0 => Val.unit
      | _ + 1 =>
        match p.alloc with
        | some aid => m.storeVal aid p.offset
        | none => Val.uninit
    checkValueValidity ty rawVal

/-- Transmuting value `v` of type `srcTy` into `dstTy`
(`compiler/rustc_const_eval/src/interpret/cast.rs:192-218`):
1. Checks `srcTy.byteSize == dstTy.byteSize` (else `sizeMismatchUb`).
2. Checks validity at `dstTy` (`invalidValueUb` for uninhabited `dstTy`). -/
def evalTransmute (srcTy dstTy : MirTy) (v : Val) : Except FaultKind Val :=
  if !Nat.beq srcTy.byteSize dstTy.byteSize then
    .error .sizeMismatchUb
  else
    checkValueValidity dstTy v

theorem checkValueValidity_uninhabited_always_faults (v : Val) (sz : Nat) :
    checkValueValidity .voidTy v = .error .invalidValueUb ∧
    checkValueValidity (.uninhabitedSized sz) v = .error .invalidValueUb := by
  exact ⟨rfl, rfl⟩

/-! ## Section 2: MIR Places, Projections, and Post-`Derefer` Invariants -/

/-- Projection elements matching `rustc_middle::mir::ProjectionElem`. -/
inductive ProjElem where
  | deref
  | phantomDeref
  | field (idx : FieldIdx)
  | index (idxLocal : LocalId)
  | opaqueCast (hiddenTy : MirTy)

/-- `ProjectionElem::is_indirect` (`compiler/rustc_middle/src/mir/statement.rs:263-275`). -/
def ProjElem.isIndirect : ProjElem → Bool
  | .deref => true
  | .phantomDeref => true
  | .field _ => false
  | .index _ => false
  | .opaqueCast _ => false

/-- MIR place (`local` + projection list). -/
structure Place where
  localId : LocalId
  proj : List ProjElem

def Place.ofLocal (l : LocalId) : Place := { localId := l, proj := [] }

def Place.asLocal (p : Place) : Option LocalId :=
  match p.proj with
  | [] => some p.localId
  | _ :: _ => none

def ProjList.anyIndirect (xs : List ProjElem) : Bool :=
  xs.foldr (fun e ih => e.isIndirect || ih) false

/-- `Place::is_indirect` (`compiler/rustc_middle/src/mir/statement.rs:377-379`). -/
def Place.isIndirect (p : Place) : Bool :=
  ProjList.anyIndirect p.proj

def Place.projectDeeper (p : Place) (extra : List ProjElem) : Place :=
  { localId := p.localId, proj := p.proj ++ extra }

/-- Post-`Derefer` MIR invariant (`compiler/rustc_middle/src/mir/syntax.rs:117-118`,
enforced by `compiler/rustc_mir_transform/src/validate.rs`):
`Deref` / `PhantomDeref` is permitted ONLY as the first projection (`index 0`). -/
def Place.derefOnlyFirst (p : Place) : Bool :=
  match p.proj with
  | [] => true
  | _ :: rest => !ProjList.anyIndirect rest

def ProjList.hasOpaqueCast (xs : List ProjElem) : Bool :=
  xs.foldr (fun e ih => match e with | .opaqueCast _ => true | _ => ih) false

def Place.hasOpaqueCast (p : Place) : Bool :=
  ProjList.hasOpaqueCast p.proj

theorem projList_anyIndirect_append (xs ys : List ProjElem) :
    ProjList.anyIndirect (xs ++ ys) = (ProjList.anyIndirect xs || ProjList.anyIndirect ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold ProjList.anyIndirect at ih ⊢
    simp only [List.cons_append, List.foldr_cons, ih, Bool.or_assoc]

/-- Exact characterization of when `place.project_deeper([.deref, .index idx])`
preserves the post-`Derefer` invariant `derefOnlyFirst`:
it holds IF AND ONLY IF `place` is a plain local (`place.proj = []`). -/
theorem sliceGetUnchecked_preserves_derefOnlyFirst_iff (p : Place) (idx : LocalId) :
    (p.projectDeeper [.deref, .index idx]).derefOnlyFirst = true ↔ p.proj = [] := by
  unfold Place.projectDeeper Place.derefOnlyFirst
  cases h : p.proj with
  | nil =>
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons e es =>
    simp only [List.cons_append, projList_anyIndirect_append]
    have h1 : ProjList.anyIndirect [ProjElem.deref, ProjElem.index idx] = true := rfl
    rw [h1]
    simp only [Bool.or_true, Bool.not_true, Bool.false_eq_true, false_iff]
    intro hne
    cases hne

/-- Necessary & sufficient corollary for plain local arguments:
ordinary Rust MIR building stages call arguments into plain locals,
guaranteeing `derefOnlyFirst = true`. -/
theorem sliceGetUnchecked_plainLocal_preserves_derefOnlyFirst (l idx : LocalId) :
    ((Place.ofLocal l).projectDeeper [.deref, .index idx]).derefOnlyFirst = true := by
  exact (sliceGetUnchecked_preserves_derefOnlyFirst_iff (Place.ofLocal l) idx).mpr rfl

/-- Refutation 1 (indirect place `*pp`): when `Derefer` is bypassed via
`#[custom_mir(dialect = "runtime", phase = "initial")]` and `place = *_1`,
`place.isIndirect = true` (triggering `assert!(!place.is_indirect())` ICE),
and omitting that assertion would emit `(*(*_1))[_2]` violating `derefOnlyFirst`. -/
theorem sliceGetUnchecked_indirect_violates_derefOnlyFirst (l idx : LocalId) :
    let p : Place := { localId := l, proj := [.deref] }
    p.isIndirect = true ∧ (p.projectDeeper [.deref, .index idx]).derefOnlyFirst = false := by
  refine ⟨rfl, rfl⟩

/-- Refutation 2 (Lean-discovered upstream invariant gap in `lower_intrinsics.rs:254`):
`assert!(!place.is_indirect())` is STRICTLY TOO WEAK!
For a non-indirect field projection `pair.0` (`proj = [.field 0]`):
1. `p.isIndirect = false` (so `assert!(!place.is_indirect())` PASSES!),
2. Yet `p.projectDeeper [.deref, .index idx]` yields `(*(_1.0))[_2]` with
   `proj = [.field 0, .deref, .index idx]`, violating `derefOnlyFirst = false`
   and triggering `validate.rs:82:25: broken MIR ... has deref as a later projection`! -/
theorem sliceGetUnchecked_fieldProj_bypasses_isIndirect_yet_violates_derefOnlyFirst
    (l idx : LocalId) :
    let p : Place := { localId := l, proj := [.field 0] }
    p.isIndirect = false ∧
    p.asLocal = none ∧
    (p.projectDeeper [.deref, .index idx]).derefOnlyFirst = false := by
  refine ⟨rfl, rfl, rfl⟩

/-- Refutation 3 (`discriminant_value` missing guard at `lower_intrinsics.rs:216-217`):
calling `mk_place_deref(arg)` without checking `arg.asLocal` emits invalid
`(*(*_1))` for `*pp` and invalid `(*(_1.0))` for `pair.0`, both caught only
downstream by `validate.rs`. -/
theorem discriminantValue_nonlocal_violates_derefOnlyFirst (l : LocalId) :
    let pDeref : Place := { localId := l, proj := [.deref] }
    let pField : Place := { localId := l, proj := [.field 0] }
    (pDeref.projectDeeper [.deref]).derefOnlyFirst = false ∧
    (pField.projectDeeper [.deref]).derefOnlyFirst = false := by
  refine ⟨rfl, rfl⟩

/-! ## Section 3: MIR Operations, All 29 Lowered Intrinsics, Statements, and Semantics -/

/-- Runtime check queries lowered from `ub_checks`/`overflow_checks`/`contract_checks`. -/
inductive RuntimeChecksKind where
  | ubChecks
  | overflowChecks
  | contractChecks

/-- Binary operators lowered by `LowerIntrinsics` (`lower_intrinsics.rs:117-174, 227-243`). -/
inductive BinOp where
  | add
  | sub
  | mul
  | cmp
  | addUnchecked
  | subUnchecked
  | mulUnchecked
  | div
  | rem
  | shlUnchecked
  | shrUnchecked
  | addWithOverflow
  | subWithOverflow
  | mulWithOverflow
  | offset

/-- Unary operators including `UnOp::PtrMetadata`. -/
inductive UnOp where
  | ptrMetadata (pk : PtrKind) (pt : PointeeKind)

/-- Non-diverging intrinsics lowered to `StatementKind::Intrinsic`. -/
inductive NonDivIntrinsic where
  | copyNonOverlapping (src dst count : LocalId)
  | assume (cond : LocalId)

/-- Call source tag matching `rustc_middle::mir::CallSource`. -/
inductive CallSource where
  | normal
  | misc
  | overloadedOperator

/-- Exhaustive enumeration of all 29 `sym::*` Rustc intrinsic names handled across
the 14 explicit match arms of `lower_intrinsics.rs:23-360` (plus wildcard pass-through). -/
inductive IntrinsicSym where
  | sym_unreachable
  | sym_ub_checks
  | sym_overflow_checks
  | sym_contract_checks
  | sym_forget
  | sym_copy_nonoverlapping
  | sym_assume
  | sym_wrapping_add
  | sym_wrapping_sub
  | sym_wrapping_mul
  | sym_three_way_compare
  | sym_unchecked_add
  | sym_unchecked_sub
  | sym_unchecked_mul
  | sym_unchecked_div
  | sym_unchecked_rem
  | sym_unchecked_shl
  | sym_unchecked_shr
  | sym_add_with_overflow
  | sym_sub_with_overflow
  | sym_mul_with_overflow
  | sym_read_via_copy
  | sym_discriminant_value
  | sym_offset
  | sym_slice_get_unchecked
  | sym_transmute
  | sym_transmute_unchecked
  | sym_aggregate_raw_ptr
  | sym_ptr_metadata
  | sym_other (id : Nat)

/-- The 14-arm lowered intrinsic classifier (with wildcard pass-through). -/
inductive RustcIntrinsic where
  | unreachable
  | runtimeCheck (rc : RuntimeChecksKind)
  | forget
  | copyNonOverlapping
  | assume
  | binOpIntrinsic (op : BinOp)
  | readViaCopy (pointeeTy : MirTy)
  | discriminantValue
  | sliceGetUnchecked (retKind : PtrKind) (elemSize : Nat)
  | transmute (srcTy dstTy : MirTy)
  | transmuteUnchecked (srcTy dstTy : MirTy)
  | aggregateRawPtr (retKind : PtrKind) (pt : PointeeKind)
  | ptrMetadata (pk : PtrKind) (pt : PointeeKind)
  | otherUnlowered (id : Nat)

/-- Exact classification mapping every one of the 29 `sym::*` intrinsics in
`lower_intrinsics.rs` to its lowering arm. -/
def IntrinsicSym.classify (srcTy dstTy : MirTy) (pk : PtrKind) (pt : PointeeKind)
    (elemSz : Nat) : IntrinsicSym → RustcIntrinsic
  | .sym_unreachable => .unreachable
  | .sym_ub_checks => .runtimeCheck .ubChecks
  | .sym_overflow_checks => .runtimeCheck .overflowChecks
  | .sym_contract_checks => .runtimeCheck .contractChecks
  | .sym_forget => .forget
  | .sym_copy_nonoverlapping => .copyNonOverlapping
  | .sym_assume => .assume
  | .sym_wrapping_add => .binOpIntrinsic .add
  | .sym_wrapping_sub => .binOpIntrinsic .sub
  | .sym_wrapping_mul => .binOpIntrinsic .mul
  | .sym_three_way_compare => .binOpIntrinsic .cmp
  | .sym_unchecked_add => .binOpIntrinsic .addUnchecked
  | .sym_unchecked_sub => .binOpIntrinsic .subUnchecked
  | .sym_unchecked_mul => .binOpIntrinsic .mulUnchecked
  | .sym_unchecked_div => .binOpIntrinsic .div
  | .sym_unchecked_rem => .binOpIntrinsic .rem
  | .sym_unchecked_shl => .binOpIntrinsic .shlUnchecked
  | .sym_unchecked_shr => .binOpIntrinsic .shrUnchecked
  | .sym_add_with_overflow => .binOpIntrinsic .addWithOverflow
  | .sym_sub_with_overflow => .binOpIntrinsic .subWithOverflow
  | .sym_mul_with_overflow => .binOpIntrinsic .mulWithOverflow
  | .sym_read_via_copy => .readViaCopy dstTy
  | .sym_discriminant_value => .discriminantValue
  | .sym_offset => .binOpIntrinsic .offset
  | .sym_slice_get_unchecked => .sliceGetUnchecked pk elemSz
  | .sym_transmute => .transmute srcTy dstTy
  | .sym_transmute_unchecked => .transmuteUnchecked srcTy dstTy
  | .sym_aggregate_raw_ptr => .aggregateRawPtr pk pt
  | .sym_ptr_metadata => .ptrMetadata pk pt
  | .sym_other id => .otherUnlowered id

def RustcIntrinsic.isLowered : RustcIntrinsic → Bool
  | .otherUnlowered _ => false
  | _ => true

/-- Exact census theorem: all 29 explicit `sym::*` intrinsics in `lower_intrinsics.rs`
classify to a lowered arm (`isLowered = true`), while `.sym_other` stays unlowered. -/
theorem all_29_explicit_syms_are_lowered (srcTy dstTy : MirTy) (pk : PtrKind)
    (pt : PointeeKind) (elemSz : Nat) :
    let syms : List IntrinsicSym :=
      [.sym_unreachable, .sym_ub_checks, .sym_overflow_checks, .sym_contract_checks,
       .sym_forget, .sym_copy_nonoverlapping, .sym_assume, .sym_wrapping_add,
       .sym_wrapping_sub, .sym_wrapping_mul, .sym_three_way_compare,
       .sym_unchecked_add, .sym_unchecked_sub, .sym_unchecked_mul,
       .sym_unchecked_div, .sym_unchecked_rem, .sym_unchecked_shl,
       .sym_unchecked_shr, .sym_add_with_overflow, .sym_sub_with_overflow,
       .sym_mul_with_overflow, .sym_read_via_copy, .sym_discriminant_value,
       .sym_offset, .sym_slice_get_unchecked, .sym_transmute,
       .sym_transmute_unchecked, .sym_aggregate_raw_ptr, .sym_ptr_metadata]
    syms.length = 29 ∧
    syms.all (fun s => (s.classify srcTy dstTy pk pt elemSz).isLowered) = true ∧
    ∀ id, ((IntrinsicSym.sym_other id).classify srcTy dstTy pk pt elemSz).isLowered = false := by
  refine ⟨rfl, rfl, fun _ => rfl⟩

/-- Function callee representation in `TerminatorKind::Call`. -/
inductive Callee where
  | intrinsic (intr : RustcIntrinsic)
  | sliceLenFn (elemSize : Nat)
  | fnPtrSliceLen (elemSize : Nat)
  | normalFn (defId : DefId)

/-- MIR operands (`Copy`, `Move`, `Constant`, `RuntimeChecks`). -/
inductive Operand where
  | copy (p : Place)
  | move (p : Place)
  | constVal (v : Val) (ty : MirTy)
  | constUneval (defId : DefId) (genericArgs : List MirTy) (ty : MirTy)
  | runtimeChecks (rc : RuntimeChecksKind)

/-- MIR rvalues produced by `LowerIntrinsics` and `LowerSliceLenCalls`. -/
inductive Rvalue where
  | use (op : Operand)
  | readViaDeref (ptrLocal : LocalId) (pointeeTy : MirTy)
  | binOp (op : BinOp) (lhs rhs : Operand)
  | unOp (op : UnOp) (arg : Operand)
  | discriminant (ptrPlace : Place)
  | sliceIndexPtr (retKind : PtrKind) (elemSize : Nat) (ptrPlace : Place) (idxLocal : LocalId)
  | castTransmute (srcTy dstTy : MirTy) (arg : Operand)
  | aggregateRawPtr (retKind : PtrKind) (pt : PointeeKind) (data metaOp : Operand)

/-- MIR statements. -/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | intrinsic (intr : NonDivIntrinsic)
  | nop

/-- MIR terminators. -/
inductive Term where
  | goto (target : BlockId)
  | return_
  | unreachable
  | call
      (callee : Callee)
      (args : List Operand)
      (dst : Place)
      (target : Option BlockId)
      (unwind : Option BlockId)
      (callSource : CallSource)

/-- Basic block containing sequential statements and one terminator. -/
structure BasicBlock where
  stmts : List Stmt
  term : Term

/-- Execution state for single-frame evaluation of lowered/unlowered blocks. -/
structure ExecState where
  locals : LocalId → Val
  localTy : LocalId → MirTy
  mem : Mem

def ExecState.setLocal (st : ExecState) (l : LocalId) (v : Val) : ExecState :=
  { st with locals := fun x => if Nat.beq x l then v else st.locals x }

/-- Result of executing a basic block step. -/
inductive BlockOutcome where
  | nextBlock (bb : BlockId) (st : ExecState)
  | returned (v : Val) (st : ExecState)
  | callPending (callee : Callee) (args : List Operand) (st : ExecState)
  | fault (k : FaultKind)

def U32_MOD : Nat := 4294967296

def evalRuntimeChecks (m : Mem) : RuntimeChecksKind → Bool
  | .ubChecks => m.runtimeUbChecks
  | .overflowChecks => m.runtimeOverflowChecks
  | .contractChecks => m.runtimeContractChecks

def evalOperand (st : ExecState) : Operand → Except FaultKind Val
  | .copy p =>
    match p.proj with
    | [] =>
      match st.locals p.localId with
      | .uninit => .error .uninitLocalUb
      | v => .ok v
    | _ => .error .unsupportedOp
  | .move p =>
    match p.proj with
    | [] =>
      match st.locals p.localId with
      | .uninit => .error .uninitLocalUb
      | v => .ok v
    | _ => .error .unsupportedOp
  | .constVal v _ => .ok v
  | .constUneval _ _ _ => .error .unsupportedOp
  | .runtimeChecks rc => .ok (.bool (evalRuntimeChecks st.mem rc))

def evalBinOp (op : BinOp) (lv rv : Val) : Except FaultKind Val :=
  match op, lv, rv with
  | .add, .int a, .int b => .ok (.int ((a + b) % U32_MOD))
  | .sub, .int a, .int b => .ok (.int ((a + U32_MOD - (b % U32_MOD)) % U32_MOD))
  | .mul, .int a, .int b => .ok (.int ((a * b) % U32_MOD))
  | .cmp, .int a, .int b =>
    if Nat.blt a b then .ok (.tag 0)
    else if Nat.beq a b then .ok (.tag 1)
    else .ok (.tag 2)
  | .addUnchecked, .int a, .int b =>
    if Nat.blt (a + b) U32_MOD then .ok (.int (a + b)) else .error .overflowUb
  | .subUnchecked, .int a, .int b =>
    if Nat.ble b a then .ok (.int (a - b)) else .error .overflowUb
  | .mulUnchecked, .int a, .int b =>
    if Nat.blt (a * b) U32_MOD then .ok (.int (a * b)) else .error .overflowUb
  | .div, .int a, .int b =>
    if Nat.beq b 0 then .error .overflowUb else .ok (.int (a / b))
  | .rem, .int a, .int b =>
    if Nat.beq b 0 then .error .overflowUb else .ok (.int (a % b))
  | .shlUnchecked, .int a, .int s =>
    if Nat.blt s 32 then .ok (.int ((a * (Nat.pow 2 s)) % U32_MOD)) else .error .overflowUb
  | .shrUnchecked, .int a, .int s =>
    if Nat.blt s 32 then .ok (.int (a / (Nat.pow 2 s))) else .error .overflowUb
  | .addWithOverflow, .int a, .int b =>
    let ov := !Nat.blt (a + b) U32_MOD
    .ok (.pair (.int ((a + b) % U32_MOD)) (.bool ov))
  | .subWithOverflow, .int a, .int b =>
    let ov := !Nat.ble b a
    .ok (.pair (.int ((a + U32_MOD - (b % U32_MOD)) % U32_MOD)) (.bool ov))
  | .mulWithOverflow, .int a, .int b =>
    let ov := !Nat.blt (a * b) U32_MOD
    .ok (.pair (.int ((a * b) % U32_MOD)) (.bool ov))
  | .offset, .ptr p, .int delta =>
    .ok (.ptr { p with offset := p.offset + delta })
  | _, _, _ => .error .unsupportedOp

/-- Evaluate `UnOp::PtrMetadata` matching `compiler/rustc_const_eval/src/interpret/operator.rs:499-513`:
FIRST executes `derefPointerCheck`, THEN returns metadata (`unit` for thin pointers,
`int len` for slices, `int vid` for `dyn Trait` vtables). -/
def evalUnOp (m : Mem) (op : UnOp) (v : Val) : Except FaultKind Val :=
  match op, v with
  | .ptrMetadata pk pt, .ptr p =>
    match m.derefPointerCheck pk pt p with
    | .error e => .error e
    | .ok () =>
      match p.ptrMeta with
      | .none => .ok .unit
      | .sliceLen n => .ok (.int n)
      | .vtable vid => .ok (.int vid)
  | _, _ => .error .unsupportedOp

/-- Evaluate `Rvalue::Aggregate(AggregateKind::RawPtr(..), [data, meta])`
matching `compiler/rustc_const_eval/src/interpret/step.rs:317-338`. -/
def evalAggregateRawPtr (pt : PointeeKind) (dataVal metaVal : Val) : Except FaultKind Val :=
  match dataVal with
  | .ptr dp =>
    match pt, metaVal with
    | .sized _, .unit => .ok (.ptr { dp with ptrMeta := .none })
    | .slice _, .int n => .ok (.ptr { dp with ptrMeta := .sliceLen n })
    | .dynTrait _, .int vid => .ok (.ptr { dp with ptrMeta := .vtable vid })
    | _, _ => .error .invalidValueUb
  | _ => .error .invalidValueUb

/-- Evaluate `slice_get_unchecked` / `&(*ptr)[idx]` / `&raw (*ptr)[idx]`. -/
def evalSliceIndexPtr (st : ExecState) (retKind : PtrKind) (elemSize : Nat)
    (ptrPlace : Place) (idxLocal : LocalId) : Except FaultKind Val :=
  if ptrPlace.isIndirect then
    .error .icePrecondition
  else
    match ptrPlace.asLocal with
    | none => .error .icePrecondition
    | some pl =>
      match st.locals pl, st.locals idxLocal with
      | .ptr p, .int i =>
        match p.ptrMeta with
        | .sliceLen len =>
          if Nat.blt i len then
            let resPtr : PtrVal :=
              { alloc := p.alloc
                offset := p.offset + elemSize * i
                aligned := p.aligned
                ptrMeta := .none }
            match retKind with
            | .refShared | .refMut =>
              match st.mem.derefPointerCheck retKind (.sized elemSize) resPtr with
              | .ok () => .ok (.ptr resPtr)
              | .error e => .error e
            | .rawConst | .rawMut => .ok (.ptr resPtr)
          else
            .error .memAccessUb
        | _ => .error .invalidValueUb
      | _, _ => .error .uninitLocalUb

/-- Write value to a destination place. -/
def writePlace (st : ExecState) (dst : Place) (v : Val) : Except FaultKind ExecState :=
  match dst.proj with
  | [] => .ok (st.setLocal dst.localId v)
  | [.deref] =>
    match st.locals dst.localId with
    | .ptr p =>
      match st.mem.checkAccess p 1 with
      | .error e => .error e
      | .ok () =>
        match p.alloc with
        | some aid => .ok { st with mem := st.mem.writeAt aid p.offset v }
        | none => .error .memAccessUb
    | _ => .error .uninitLocalUb
  | _ => .error .unsupportedOp

def evalRvalue (st : ExecState) : Rvalue → Except FaultKind Val
  | .use op => evalOperand st op
  | .readViaDeref ptrLocal pointeeTy =>
    match st.locals ptrLocal with
    | .ptr p => st.mem.readViaPtr p pointeeTy
    | .uninit => .error .uninitLocalUb
    | _ => .error .invalidValueUb
  | .binOp op lhs rhs =>
    match evalOperand st lhs with
    | .error e => .error e
    | .ok lv =>
      match evalOperand st rhs with
      | .error e => .error e
      | .ok rv => evalBinOp op lv rv
  | .unOp op arg =>
    match evalOperand st arg with
    | .error e => .error e
    | .ok v => evalUnOp st.mem op v
  | .discriminant ptrPlace =>
    match ptrPlace.asLocal with
    | some pl =>
      match st.locals pl with
      | .ptr p =>
        match st.mem.readViaPtr p .enumTag with
        | .ok (.tag d) => .ok (.int d)
        | .ok _ => .error .invalidValueUb
        | .error e => .error e
      | _ => .error .uninitLocalUb
    | none => .error .icePrecondition
  | .sliceIndexPtr retKind elemSize ptrPlace idxLocal =>
    evalSliceIndexPtr st retKind elemSize ptrPlace idxLocal
  | .castTransmute srcTy dstTy arg =>
    match evalOperand st arg with
    | .error e => .error e
    | .ok v => evalTransmute srcTy dstTy v
  | .aggregateRawPtr _ pt data metaOp =>
    match evalOperand st data with
    | .error e => .error e
    | .ok dv =>
      match evalOperand st metaOp with
      | .error e => .error e
      | .ok mv => evalAggregateRawPtr pt dv mv

def evalNonDivIntrinsic (st : ExecState) : NonDivIntrinsic → Except FaultKind ExecState
  | .assume condLocal =>
    match st.locals condLocal with
    | .bool true => .ok st
    | .bool false => .error .assumeFalseUb
    | .uninit => .error .uninitLocalUb
    | _ => .error .invalidValueUb
  | .copyNonOverlapping srcLocal dstLocal countLocal =>
    match st.locals srcLocal, st.locals dstLocal, st.locals countLocal with
    | .ptr sp, .ptr dp, .int cnt =>
      match st.mem.checkAccess sp cnt with
      | .error e => .error e
      | .ok () =>
        match st.mem.checkAccess dp cnt with
        | .error e => .error e
        | .ok () => .ok st
    | _, _, _ => .error .uninitLocalUb

def evalStmt (st : ExecState) : Stmt → Except FaultKind ExecState
  | .nop => .ok st
  | .intrinsic intr => evalNonDivIntrinsic st intr
  | .assign dst rv =>
    match evalRvalue st rv with
    | .error e => .error e
    | .ok v => writePlace st dst v

def evalStmts (st : ExecState) (stmts : List Stmt) : Except FaultKind ExecState :=
  (stmts.foldr
    (fun s ih => fun cur =>
      match evalStmt cur s with
      | .error e => .error e
      | .ok cur' => ih cur')
    (fun cur => .ok cur)) st

theorem evalStmts_nil (st : ExecState) : evalStmts st [] = .ok st := rfl

theorem evalStmts_cons (st : ExecState) (s : Stmt) (ss : List Stmt) :
    evalStmts st (s :: ss) =
      match evalStmt st s with
      | .error e => .error e
      | .ok st' => evalStmts st' ss := rfl

theorem evalStmts_append (st : ExecState) (xs ys : List Stmt) :
    evalStmts st (xs ++ ys) =
      match evalStmts st xs with
      | .error e => .error e
      | .ok st' => evalStmts st' ys := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, evalStmts_cons, evalStmts_cons]
    cases evalStmt st x with
    | error e => rfl
    | ok st1 => exact ih st1

/-- Helper applying an rvalue evaluation, destination write, and optional target jump. -/
def finishRvalueTarget (st : ExecState) (dst : Place) (rv : Rvalue)
    (target : Option BlockId) : BlockOutcome :=
  match evalRvalue st rv with
  | .error e => .fault e
  | .ok v =>
    match writePlace st dst v with
    | .error e => .fault e
    | .ok st' =>
      match target with
      | none => .fault .unreachableUb
      | some bb => .nextBlock bb st'

/-- Source-level reference operational semantics of intrinsic calls BEFORE
`LowerIntrinsics` runs. -/
def evalIntrinsicCall (st : ExecState) (intr : RustcIntrinsic) (args : List Operand)
    (dst : Place) (target : Option BlockId) : BlockOutcome :=
  match intr, args with
  | .unreachable, [] => .fault .unreachableUb
  | .runtimeCheck rc, [] =>
    match target with
    | none => .fault .icePrecondition
    | some bb => finishRvalueTarget st dst (.use (.runtimeChecks rc)) (some bb)
  | .forget, [_] =>
    match target with
    | none => .fault .icePrecondition
    | some bb => finishRvalueTarget st dst (.use (.constVal .unit .unit)) (some bb)
  | .copyNonOverlapping, [.move sPl, .move dPl, .move cPl] =>
    match target, sPl.asLocal, dPl.asLocal, cPl.asLocal with
    | some bb, some sl, some dl, some cl =>
      match evalNonDivIntrinsic st (.copyNonOverlapping sl dl cl) with
      | .error e => .fault e
      | .ok st1 => finishRvalueTarget st1 dst (.use (.constVal .unit .unit)) (some bb)
    | _, _, _, _ => .fault .icePrecondition
  | .assume, [.move condPl] =>
    match target, condPl.asLocal with
    | some bb, some cl =>
      match evalNonDivIntrinsic st (.assume cl) with
      | .error e => .fault e
      | .ok st1 => finishRvalueTarget st1 dst (.use (.constVal .unit .unit)) (some bb)
    | _, _ => .fault .icePrecondition
  | .binOpIntrinsic op, [lhs, rhs] =>
    match target with
    | none => .fault .icePrecondition
    | some bb => finishRvalueTarget st dst (.binOp op lhs rhs) (some bb)
  | .readViaCopy pointeeTy, [Operand.move pPl] =>
    match pPl.asLocal with
    | none => .fault .icePrecondition
    | some pl => finishRvalueTarget st dst (.readViaDeref pl pointeeTy) target
  | .readViaCopy pointeeTy, [Operand.copy pPl] =>
    match pPl.asLocal with
    | none => .fault .icePrecondition
    | some pl => finishRvalueTarget st dst (.readViaDeref pl pointeeTy) target
  | .discriminantValue, [Operand.move pPl] =>
    match target with
    | none => .fault .icePrecondition
    | some bb => finishRvalueTarget st dst (.discriminant pPl) (some bb)
  | .sliceGetUnchecked retKind elemSize, [Operand.move pPl, Operand.move iPl] =>
    match target, iPl.asLocal with
    | some bb, some il =>
      finishRvalueTarget st dst (.sliceIndexPtr retKind elemSize pPl il) (some bb)
    | _, _ => .fault .icePrecondition
  | .transmute srcTy dstTy, [arg] =>
    finishRvalueTarget st dst (.castTransmute srcTy dstTy arg) target
  | .transmuteUnchecked srcTy dstTy, [arg] =>
    finishRvalueTarget st dst (.castTransmute srcTy dstTy arg) target
  | .aggregateRawPtr retKind pt, [data, metaOp] =>
    match target with
    | none => .fault .icePrecondition
    | some bb => finishRvalueTarget st dst (.aggregateRawPtr retKind pt data metaOp) (some bb)
  | .ptrMetadata pk pt, [ptrOp] =>
    match target with
    | none => .fault .icePrecondition
    | some bb => finishRvalueTarget st dst (.unOp (.ptrMetadata pk pt) ptrOp) (some bb)
  | .otherUnlowered id, _ => .callPending (.intrinsic (.otherUnlowered id)) args st
  | _, _ => .fault .icePrecondition

/-- Evaluate a basic block terminator.
For `Callee.sliceLenFn elemSize`, matches `library/core/src/slice/mod.rs:118-120`:
`pub const fn len(&self) -> usize { ptr::metadata(self) }` (never unwinds;
validates `&[T]` via `deref_pointer` and returns its slice length). -/
def evalTerm (st : ExecState) : Term → BlockOutcome
  | .goto bb => .nextBlock bb st
  | .return_ => .returned (st.locals 0) st
  | .unreachable => .fault .unreachableUb
  | .call callee args dst target _unwind _cs =>
    match callee with
    | .intrinsic intr => evalIntrinsicCall st intr args dst target
    | .sliceLenFn elemSize =>
      match args, target with
      | [arg], some bb =>
        finishRvalueTarget st dst (.unOp (.ptrMetadata .refShared (.slice elemSize)) arg) (some bb)
      | _, _ => .fault .icePrecondition
    | .fnPtrSliceLen elemSize => .callPending (.fnPtrSliceLen elemSize) args st
    | .normalFn fid => .callPending (.normalFn fid) args st

/-- Execute an entire basic block (statements then terminator). -/
def execBlock (st : ExecState) (blk : BasicBlock) : BlockOutcome :=
  match evalStmts st blk.stmts with
  | .error e => .fault e
  | .ok st' => evalTerm st' blk.term

/-- Composition lemma 1: appending an assignment statement followed by `Goto` or
`Unreachable` executes identically to `finishRvalueTarget`. -/
theorem execBlock_append_assign (st : ExecState) (stmts : List Stmt)
    (dst : Place) (rv : Rvalue) (target : Option BlockId) :
    execBlock st
      { stmts := stmts ++ [.assign dst rv]
        term := match target with | none => .unreachable | some bb => .goto bb } =
    match evalStmts st stmts with
    | .error e => .fault e
    | .ok st1 => finishRvalueTarget st1 dst rv target := by
  unfold execBlock
  rw [evalStmts_append]
  cases evalStmts st stmts with
  | error _ => rfl
  | ok st1 =>
    dsimp only
    rw [evalStmts_cons]
    simp only [evalStmt, finishRvalueTarget]
    cases hrv : evalRvalue st1 rv with
    | error _ => rfl
    | ok v =>
      dsimp only
      cases hw : writePlace st1 dst v with
      | error _ => rfl
      | ok st2 =>
        dsimp only
        rw [evalStmts_nil]
        cases target <;> rfl

/-- Composition lemma 2: appending a non-diverging intrinsic + destination unit
assignment + `Goto bb`. -/
theorem execBlock_append_nonDiv_unit (st : ExecState) (stmts : List Stmt)
    (intr : NonDivIntrinsic) (dst : Place) (bb : BlockId) :
    execBlock st
      { stmts := stmts ++ [.intrinsic intr, .assign dst (.use (.constVal .unit .unit))]
        term := .goto bb } =
    match evalStmts st stmts with
    | .error e => .fault e
    | .ok st1 =>
      match evalNonDivIntrinsic st1 intr with
      | .error e => .fault e
      | .ok st2 => finishRvalueTarget st2 dst (.use (.constVal .unit .unit)) (some bb) := by
  unfold execBlock
  rw [evalStmts_append]
  cases evalStmts st stmts with
  | error _ => rfl
  | ok st1 =>
    dsimp only
    rw [evalStmts_cons]
    simp only [evalStmt, finishRvalueTarget, evalRvalue, evalOperand]
    cases hnd : evalNonDivIntrinsic st1 intr with
    | error _ => rfl
    | ok st2 =>
      dsimp only
      rw [evalStmts_cons]
      simp only [evalStmt, evalRvalue, evalOperand]
      cases hw : writePlace st2 dst .unit with
      | error _ => rfl
      | ok st3 =>
        dsimp only
        rw [evalStmts_nil]
        rfl

/-! ## Section 4: `LowerIntrinsics` Pass Model, Uninhabited UB Ordering, and Wide-Pointer Bijection -/

/-- Exact model of `LowerIntrinsics::run_pass` on a single basic block
(`compiler/rustc_mir_transform/src/lower_intrinsics.rs:12-363` at `137d1d49458b`).
`emitUnitDestOnNonDiv = true` matches `137d1d49458b` HEAD (`copy_nonoverlapping`
and `assume` emit `*destination = ()`); `emitUnitDestOnNonDiv = false` matches
`14210df0e27c` (`1.98.0-nightly`). -/
def lowerIntrinsicsBlock (emitUnitDestOnNonDiv : Bool) (blk : BasicBlock) :
    Except FaultKind BasicBlock :=
  match blk.term with
  | .call (.intrinsic intr) args dst target _unwind _cs =>
    match intr, args with
    | .unreachable, [] =>
      .ok { stmts := blk.stmts, term := .unreachable }
    | .runtimeCheck rc, [] =>
      match target with
      | none => .error .icePrecondition
      | some bb =>
        .ok { stmts := blk.stmts ++ [.assign dst (.use (.runtimeChecks rc))]
              term := .goto bb }
    | .forget, [_] =>
      match target with
      | none => .error .icePrecondition
      | some bb =>
        .ok { stmts := blk.stmts ++ [.assign dst (.use (.constVal .unit .unit))]
              term := .goto bb }
    | .copyNonOverlapping, [.move sPl, .move dPl, .move cPl] =>
      match target, sPl.asLocal, dPl.asLocal, cPl.asLocal with
      | some bb, some sl, some dl, some cl =>
        let extra : List Stmt :=
          if emitUnitDestOnNonDiv then
            [.intrinsic (.copyNonOverlapping sl dl cl), .assign dst (.use (.constVal .unit .unit))]
          else
            [.intrinsic (.copyNonOverlapping sl dl cl)]
        .ok { stmts := blk.stmts ++ extra, term := .goto bb }
      | _, _, _, _ => .error .icePrecondition
    | .assume, [.move condPl] =>
      match target, condPl.asLocal with
      | some bb, some cl =>
        let extra : List Stmt :=
          if emitUnitDestOnNonDiv then
            [.intrinsic (.assume cl), .assign dst (.use (.constVal .unit .unit))]
          else
            [.intrinsic (.assume cl)]
        .ok { stmts := blk.stmts ++ extra, term := .goto bb }
      | _, _ => .error .icePrecondition
    | .binOpIntrinsic op, [lhs, rhs] =>
      match target with
      | none => .error .icePrecondition
      | some bb =>
        .ok { stmts := blk.stmts ++ [.assign dst (.binOp op lhs rhs)]
              term := .goto bb }
    | .readViaCopy pointeeTy, [Operand.move pPl] =>
      match pPl.asLocal with
      | none => .error .icePrecondition
      | some pl =>
        .ok { stmts := blk.stmts ++ [.assign dst (.readViaDeref pl pointeeTy)]
              term := match target with | none => .unreachable | some bb => .goto bb }
    | .readViaCopy pointeeTy, [Operand.copy pPl] =>
      match pPl.asLocal with
      | none => .error .icePrecondition
      | some pl =>
        .ok { stmts := blk.stmts ++ [.assign dst (.readViaDeref pl pointeeTy)]
              term := match target with | none => .unreachable | some bb => .goto bb }
    | .discriminantValue, [Operand.move pPl] =>
      match target with
      | none => .error .icePrecondition
      | some bb =>
        .ok { stmts := blk.stmts ++ [.assign dst (.discriminant pPl)]
              term := .goto bb }
    | .sliceGetUnchecked retKind elemSize, [Operand.move pPl, Operand.move iPl] =>
      if pPl.isIndirect then
        .error .icePrecondition
      else
        match target, iPl.asLocal with
        | some bb, some il =>
          .ok { stmts := blk.stmts ++ [.assign dst (.sliceIndexPtr retKind elemSize pPl il)]
                term := .goto bb }
        | _, _ => .error .icePrecondition
    | .transmute srcTy dstTy, [arg] =>
      .ok { stmts := blk.stmts ++ [.assign dst (.castTransmute srcTy dstTy arg)]
            term := match target with | none => .unreachable | some bb => .goto bb }
    | .transmuteUnchecked srcTy dstTy, [arg] =>
      .ok { stmts := blk.stmts ++ [.assign dst (.castTransmute srcTy dstTy arg)]
            term := match target with | none => .unreachable | some bb => .goto bb }
    | .aggregateRawPtr retKind pt, [data, metaOp] =>
      match target with
      | none => .error .icePrecondition
      | some bb =>
        .ok { stmts := blk.stmts ++ [.assign dst (.aggregateRawPtr retKind pt data metaOp)]
              term := .goto bb }
    | .ptrMetadata pk pt, [ptrOp] =>
      match target with
      | none => .error .icePrecondition
      | some bb =>
        .ok { stmts := blk.stmts ++ [.assign dst (.unOp (.ptrMetadata pk pt) ptrOp)]
              term := .goto bb }
    | .otherUnlowered _, _ => .ok blk
    | _, _ => .error .icePrecondition
  | _ => .ok blk

/-- Naive buggy lowering for uninhabited `read_via_copy` / `transmute` (`target = none`)
that omits the read/cast statement and replaces the terminator directly with `Unreachable`. -/
def naiveDropStmtLowerUninhabited (blk : BasicBlock) : BasicBlock :=
  match blk.term with
  | .call (.intrinsic (.readViaCopy _)) _ _ none _ _ =>
    { stmts := blk.stmts, term := .unreachable }
  | .call (.intrinsic (.transmute _ _)) _ _ none _ _ =>
    { stmts := blk.stmts, term := .unreachable }
  | .call (.intrinsic (.transmuteUnchecked _ _)) _ _ none _ _ =>
    { stmts := blk.stmts, term := .unreachable }
  | _ => blk

/-- **Main Theorem 1A (Uninhabited `read_via_copy` & `transmute` Pre-UB Preservation):**
For `read_via_copy` with `target = none` (uninhabited pointee) and for `transmute` /
`transmute_unchecked` with `target = none` (uninhabited destination), `LowerIntrinsics`
emits the read/cast statement BEFORE patching the terminator to `TerminatorKind::Unreachable`
(`lower_intrinsics.rs:191-205, 302-313`), thereby preserving the EXACT fault kind
(`memAccessUb`, `invalidValueUb`, `sizeMismatchUb`, `uninitLocalUb`, or `unreachableUb`)
produced by the source intrinsic call! -/
theorem lowerIntrinsics_uninhabited_preserves_pre_ub
    (st : ExecState) (prefixStmts : List Stmt) (dst : Place) (unwind : Option BlockId)
    (cs : CallSource) :
    (∀ (pointeeTy : MirTy) (pl : LocalId),
      let srcBlk : BasicBlock :=
        { stmts := prefixStmts
          term := .call (.intrinsic (.readViaCopy pointeeTy))
                    [.copy (Place.ofLocal pl)] dst none unwind cs }
      ∃ loweredBlk,
        lowerIntrinsicsBlock true srcBlk = .ok loweredBlk ∧
        execBlock st loweredBlk = execBlock st srcBlk) ∧
    (∀ (srcTy dstTy : MirTy) (arg : Operand),
      let srcBlk : BasicBlock :=
        { stmts := prefixStmts
          term := .call (.intrinsic (.transmute srcTy dstTy))
                    [arg] dst none unwind cs }
      ∃ loweredBlk,
        lowerIntrinsicsBlock true srcBlk = .ok loweredBlk ∧
        execBlock st loweredBlk = execBlock st srcBlk) ∧
    (∀ (srcTy dstTy : MirTy) (arg : Operand),
      let srcBlk : BasicBlock :=
        { stmts := prefixStmts
          term := .call (.intrinsic (.transmuteUnchecked srcTy dstTy))
                    [arg] dst none unwind cs }
      ∃ loweredBlk,
        lowerIntrinsicsBlock true srcBlk = .ok loweredBlk ∧
        execBlock st loweredBlk = execBlock st srcBlk) := by
  refine ⟨?_, ?_, ?_⟩
  · intro pointeeTy pl
    refine ⟨{ stmts := prefixStmts ++ [.assign dst (.readViaDeref pl pointeeTy)]
              term := .unreachable }, rfl, ?_⟩
    have hL := execBlock_append_assign st prefixStmts dst (.readViaDeref pl pointeeTy) none
    exact hL
  · intro srcTy dstTy arg
    refine ⟨{ stmts := prefixStmts ++ [.assign dst (.castTransmute srcTy dstTy arg)]
              term := .unreachable }, rfl, ?_⟩
    exact execBlock_append_assign st prefixStmts dst (.castTransmute srcTy dstTy arg) none
  · intro srcTy dstTy arg
    refine ⟨{ stmts := prefixStmts ++ [.assign dst (.castTransmute srcTy dstTy arg)]
              term := .unreachable }, rfl, ?_⟩
    exact execBlock_append_assign st prefixStmts dst (.castTransmute srcTy dstTy arg) none

/-- Exact Miri fault-ordering witness 1: reading an 8-byte uninhabited struct
`UninhabitedSized(u64, Void)` through a null pointer faults with `memAccessUb`
BEFORE validity checking and BEFORE `Unreachable`! -/
theorem lowerIntrinsics_readViaCopy_sizedUninhabited_null_is_memAccessUb :
    let emptyMem : Mem :=
      { allocSize := fun _ => none
        vtableTrait := fun _ => none
        storeVal := fun _ _ => .uninit
        runtimeUbChecks := true
        runtimeOverflowChecks := true
        runtimeContractChecks := false }
    let nullPtr : PtrVal := { alloc := none, offset := 0, aligned := true, ptrMeta := .none }
    let st : ExecState :=
      { locals := fun l => if Nat.beq l 1 then .ptr nullPtr else .uninit
        localTy := fun l =>
          if Nat.beq l 1 then .ptr .rawConst (.sized 8) else .uninhabitedSized 8
        mem := emptyMem }
    let srcBlk : BasicBlock :=
      { stmts := []
        term := .call (.intrinsic (.readViaCopy (.uninhabitedSized 8)))
                  [.copy (Place.ofLocal 1)] (Place.ofLocal 0) none none .normal }
    match lowerIntrinsicsBlock true srcBlk with
    | .ok loweredBlk =>
      execBlock st loweredBlk = .fault .memAccessUb ∧
      execBlock st srcBlk = .fault .memAccessUb
    | .error _ => False := by
  refine ⟨rfl, rfl⟩

/-- Exact Miri fault-ordering witness 2: reading 0-byte `Void` through a null
pointer short-circuits 0-byte memory access and faults with `invalidValueUb`
BEFORE `Unreachable` (matching live Miri `read_via_copy_void_null`)! -/
theorem lowerIntrinsics_readViaCopy_void_null_is_invalidValueUb :
    let emptyMem : Mem :=
      { allocSize := fun _ => none
        vtableTrait := fun _ => none
        storeVal := fun _ _ => .uninit
        runtimeUbChecks := true
        runtimeOverflowChecks := true
        runtimeContractChecks := false }
    let nullPtr : PtrVal := { alloc := none, offset := 0, aligned := true, ptrMeta := .none }
    let st : ExecState :=
      { locals := fun l => if Nat.beq l 1 then .ptr nullPtr else .uninit
        localTy := fun l => if Nat.beq l 1 then .ptr .rawConst (.sized 0) else .voidTy
        mem := emptyMem }
    let srcBlk : BasicBlock :=
      { stmts := []
        term := .call (.intrinsic (.readViaCopy .voidTy))
                  [.copy (Place.ofLocal 1)] (Place.ofLocal 0) none none .normal }
    match lowerIntrinsicsBlock true srcBlk with
    | .ok loweredBlk =>
      execBlock st loweredBlk = .fault .invalidValueUb ∧
      execBlock st srcBlk = .fault .invalidValueUb
    | .error _ => False := by
  refine ⟨rfl, rfl⟩

/-- Counterexample proving why statement-before-`Unreachable` ordering is load-bearing:
a naive lowering that omits the `Copy(*_2)` statement misclassifies the 8-byte
null-pointer memory access UB (`memAccessUb`) as `unreachableUb`. -/
theorem naive_uninhabited_drop_stmt_misclassifies_ub :
    let emptyMem : Mem :=
      { allocSize := fun _ => none
        vtableTrait := fun _ => none
        storeVal := fun _ _ => .uninit
        runtimeUbChecks := true
        runtimeOverflowChecks := true
        runtimeContractChecks := false }
    let nullPtr : PtrVal := { alloc := none, offset := 0, aligned := true, ptrMeta := .none }
    let st : ExecState :=
      { locals := fun l => if Nat.beq l 1 then .ptr nullPtr else .uninit
        localTy := fun l =>
          if Nat.beq l 1 then .ptr .rawConst (.sized 8) else .uninhabitedSized 8
        mem := emptyMem }
    let srcBlk : BasicBlock :=
      { stmts := []
        term := .call (.intrinsic (.readViaCopy (.uninhabitedSized 8)))
                  [.copy (Place.ofLocal 1)] (Place.ofLocal 0) none none .normal }
    execBlock st srcBlk = .fault .memAccessUb ∧
    execBlock st (naiveDropStmtLowerUninhabited srcBlk) = .fault .unreachableUb ∧
    execBlock st (naiveDropStmtLowerUninhabited srcBlk) ≠ execBlock st srcBlk := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- **Main Theorem 1B (`aggregate_raw_ptr` <-> `UnOp::PtrMetadata` Wide-Pointer Bijection):**
On valid raw pointers (`*const` or `*mut`):
1. Thin raw pointers (`sized`): `PtrMetadata(aggregate_raw_ptr(data, ())) = ok ()`.
2. Slice raw pointers (`slice`): `PtrMetadata(aggregate_raw_ptr(data, len)) = ok (int len)`
   unconditionally even if `data` is null/dangling (`place.rs:527-529`).
3. `dyn Trait` raw pointers with valid vtable (`m.vtableTrait vid = some expectedTrait`):
   `PtrMetadata(aggregate_raw_ptr(data, vid)) = ok (int vid)`.
4. Reconstruction identity: extracting `(data_part, ptr_metadata(sp))` from any slice
   raw pointer `sp` and re-aggregating yields the EXACT original `sp`. -/
theorem aggregateRawPtr_ptrMetadata_bijection (m : Mem) (pk : PtrKind)
    (hRaw : pk = .rawConst ∨ pk = .rawMut) :
    (∀ (dp : PtrVal) (sz : Nat),
      (evalAggregateRawPtr (.sized sz) (.ptr dp) .unit >>=
        evalUnOp m (.ptrMetadata pk (.sized sz))) = .ok .unit) ∧
    (∀ (dp : PtrVal) (elemSz len : Nat),
      (evalAggregateRawPtr (.slice elemSz) (.ptr dp) (.int len) >>=
        evalUnOp m (.ptrMetadata pk (.slice elemSz))) = .ok (.int len)) ∧
    (∀ (dp : PtrVal) (expectedTrait vid : Nat),
      m.vtableTrait vid = some expectedTrait →
      (evalAggregateRawPtr (.dynTrait expectedTrait) (.ptr dp) (.int vid) >>=
        evalUnOp m (.ptrMetadata pk (.dynTrait expectedTrait))) = .ok (.int vid)) ∧
    (∀ (sp : PtrVal) (elemSz len : Nat),
      sp.ptrMeta = .sliceLen len →
      (match evalUnOp m (.ptrMetadata pk (.slice elemSz)) (.ptr sp) with
       | .ok mv => evalAggregateRawPtr (.slice elemSz) (.ptr { sp with ptrMeta := .none }) mv
       | .error e => .error e) = .ok (.ptr sp)) := by
  cases hRaw with
  | inl h =>
    subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro dp sz; rfl
    · intro dp elemSz len; rfl
    · intro dp expectedTrait vid hvt
      simp only [evalAggregateRawPtr, Bind.bind, Except.bind, evalUnOp,
        Mem.derefPointerCheck, hvt, Nat.beq_refl, ↓reduceIte]
    · intro sp elemSz len hmeta
      cases sp with
      | mk alloc off al pm =>
        cases hmeta
        rfl
  | inr h =>
    subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro dp sz; rfl
    · intro dp elemSz len; rfl
    · intro dp expectedTrait vid hvt
      simp only [evalAggregateRawPtr, Bind.bind, Except.bind, evalUnOp,
        Mem.derefPointerCheck, hvt, Nat.beq_refl, ↓reduceIte]
    · intro sp elemSz len hmeta
      cases sp with
      | mk alloc off al pm =>
        cases hmeta
        rfl

/-- Boundary theorem on `operator.rs:501` (`self.deref_pointer(val)?`):
1. For a dangling `&[T]` reference (`alloc = none`), `UnOp::PtrMetadata` faults
   with `invalidValueUb` rather than returning `len`.
2. For a `dyn Trait` raw pointer with an invalid/unregistered vtable, `UnOp::PtrMetadata`
   faults with `invalidValueUb` even on a raw pointer. -/
theorem ptrMetadata_derefPointer_validity_boundaries (m : Mem) (elemSz len expectedTrait vid : Nat)
    (hBadVt : m.vtableTrait vid = none) :
    let danglingRef : PtrVal :=
      { alloc := none, offset := 4, aligned := true, ptrMeta := .sliceLen len }
    let badDynRaw : PtrVal :=
      { alloc := none, offset := 0, aligned := true, ptrMeta := .vtable vid }
    evalUnOp m (.ptrMetadata .refShared (.slice elemSz)) (.ptr danglingRef) =
      .error .invalidValueUb ∧
    evalUnOp m (.ptrMetadata .rawConst (.dynTrait expectedTrait)) (.ptr badDynRaw) =
      .error .invalidValueUb := by
  refine ⟨rfl, ?_⟩
  simp only [evalUnOp, Mem.derefPointerCheck, hBadVt]

/-- Version-divergence counterexample (`14210df0e27c` vs `137d1d49458b` HEAD):
In `14210df0e27c`, `LowerIntrinsics` lowered `assume(b)` and `copy_nonoverlapping`
WITHOUT emitting `*destination = ()`. When `destination` is an uninitialized local `_0`,
omitting the unit assignment leaves `_0 = .uninit`, whereas `137d1d49458b`
(`emitUnitDestOnNonDiv = true`) initializes `_0 = .unit`, matching source `Call`. -/
theorem assume_unit_dest_fix_head_vs_legacy198 :
    let m : Mem :=
      { allocSize := fun _ => none
        vtableTrait := fun _ => none
        storeVal := fun _ _ => .uninit
        runtimeUbChecks := false
        runtimeOverflowChecks := false
        runtimeContractChecks := false }
    let st : ExecState :=
      { locals := fun l => if Nat.beq l 1 then .bool true else .uninit
        localTy := fun l => if Nat.beq l 1 then .bool else .unit
        mem := m }
    let srcBlk : BasicBlock :=
      { stmts := []
        term := .call (.intrinsic .assume)
                  [.move (Place.ofLocal 1)] (Place.ofLocal 0) (some 1) none .normal }
    match lowerIntrinsicsBlock true srcBlk, lowerIntrinsicsBlock false srcBlk with
    | .ok headBlk, .ok legacyBlk =>
      (match execBlock st srcBlk, execBlock st headBlk, execBlock st legacyBlk with
       | .nextBlock 1 stSrc, .nextBlock 1 stHead, .nextBlock 1 stLeg =>
         stSrc.locals 0 = .unit ∧
         stHead.locals 0 = .unit ∧
         stLeg.locals 0 = .uninit
       | _, _, _ => False)
    | _, _ => False := by
  refine ⟨rfl, rfl, rfl⟩

/-- Ordinary-Rust constant-index ICE witness (`lower_intrinsics.rs:259`):
calling `slice_get_unchecked(sp, const 2)` passes `Operand.constVal` as `index`,
causing `index.node.place().unwrap()` to hit `icePrecondition` (`rc = 101`). -/
theorem sliceGetUnchecked_const_index_triggers_ice (spLocal : LocalId) (dst : Place)
    (retKind : PtrKind) (elemSz : Nat) (bb : BlockId) :
    let blk : BasicBlock :=
      { stmts := []
        term := .call (.intrinsic (.sliceGetUnchecked retKind elemSz))
                  [.move (Place.ofLocal spLocal), .constVal (.int 2) .usize]
                  dst (some bb) none .normal }
    lowerIntrinsicsBlock true blk = .error .icePrecondition := by
  rfl

/-- Complete soundness of `LowerIntrinsics` (`137d1d49458b`, `emitUnitDestOnNonDiv = true`)
across ALL 14 lowered arms (covering all 29 `sym::*` intrinsics) plus the wildcard
pass-through arm: whenever `lowerIntrinsicsBlock true blk = .ok blk'`, executing
`blk'` produces the EXACT same `BlockOutcome` as executing `blk` directly! -/
theorem lowerIntrinsics_sound_all_arms (st : ExecState) (blk blk' : BasicBlock)
    (hLower : lowerIntrinsicsBlock true blk = .ok blk') :
    execBlock st blk' = execBlock st blk := by
  unfold lowerIntrinsicsBlock at hLower
  cases hTerm : blk.term with
  | goto bb => rw [hTerm] at hLower; cases hLower; rfl
  | return_ => rw [hTerm] at hLower; cases hLower; rfl
  | unreachable => rw [hTerm] at hLower; cases hLower; rfl
  | call callee args dst target unwind cs =>
    rw [hTerm] at hLower
    cases callee with
    | sliceLenFn _ | fnPtrSliceLen _ | normalFn _ => cases hLower; rfl
    | intrinsic intr =>
      cases intr with
      | otherUnlowered _ => cases hLower; rfl
      | unreachable =>
        cases args with
        | nil =>
          cases hLower; unfold execBlock; rw [hTerm]
          cases evalStmts st blk.stmts <;> rfl
        | cons _ _ => cases hLower
      | runtimeCheck rc =>
        cases args with
        | nil =>
          cases target with
          | none => cases hLower
          | some bb =>
            cases hLower
            have h := execBlock_append_assign st blk.stmts dst (.use (.runtimeChecks rc)) (some bb)
            unfold execBlock at h ⊢
            rw [hTerm]; exact h
        | cons _ _ => cases hLower
      | forget =>
        cases args with
        | nil => cases hLower
        | cons _ rest =>
          cases rest with
          | cons _ _ => cases hLower
          | nil =>
            cases target with
            | none => cases hLower
            | some bb =>
              cases hLower
              have h := execBlock_append_assign st blk.stmts dst (.use (.constVal .unit .unit)) (some bb)
              unfold execBlock at h ⊢
              rw [hTerm]; exact h
      | copyNonOverlapping =>
        cases args with
        | nil => cases hLower
        | cons a0 r0 =>
          cases a0 <;> try (cases hLower)
          cases r0 with
          | nil => cases hLower
          | cons a1 r1 =>
            cases a1 <;> try (cases hLower)
            cases r1 with
            | nil => cases hLower
            | cons a2 r2 =>
              cases a2 <;> try (cases hLower)
              cases r2 with
              | cons _ _ => cases hLower
              | nil =>
                rename_i sPl dPl cPl
                cases target with
                | none => cases hLower
                | some bb =>
                  cases hs : sPl.asLocal with
                  | none => simp only [hs] at hLower; cases hLower
                  | some sl =>
                    cases hd : dPl.asLocal with
                    | none => simp only [hs, hd] at hLower; cases hLower
                    | some dl =>
                      cases hc : cPl.asLocal with
                      | none => simp only [hs, hd, hc] at hLower; cases hLower
                      | some cl =>
                        simp only [hs, hd, hc, ↓reduceIte] at hLower
                        cases hLower
                        have h := execBlock_append_nonDiv_unit st blk.stmts
                          (.copyNonOverlapping sl dl cl) dst bb
                        unfold execBlock at h ⊢
                        rw [hTerm]
                        simpa only [evalTerm, evalIntrinsicCall, hs, hd, hc] using h
      | assume =>
        cases args with
        | nil => cases hLower
        | cons a0 r0 =>
          cases a0 <;> try (cases hLower)
          cases r0 with
          | cons _ _ => cases hLower
          | nil =>
            rename_i condPl
            cases target with
            | none => cases hLower
            | some bb =>
              cases hc : condPl.asLocal with
              | none => simp only [hc] at hLower; cases hLower
              | some cl =>
                simp only [hc, ↓reduceIte] at hLower
                cases hLower
                have h := execBlock_append_nonDiv_unit st blk.stmts (.assume cl) dst bb
                unfold execBlock at h ⊢
                rw [hTerm]
                simpa only [evalTerm, evalIntrinsicCall, hc] using h
      | binOpIntrinsic op =>
        cases args with
        | nil => cases hLower
        | cons lhs r0 =>
          cases r0 with
          | nil => cases hLower
          | cons rhs r1 =>
            cases r1 with
            | cons _ _ => cases hLower
            | nil =>
              cases target with
              | none => cases hLower
              | some bb =>
                cases hLower
                have h := execBlock_append_assign st blk.stmts dst (.binOp op lhs rhs) (some bb)
                unfold execBlock at h ⊢
                rw [hTerm]; exact h
      | readViaCopy pointeeTy =>
        cases args with
        | nil => cases hLower
        | cons a0 r0 =>
          cases r0 with
          | cons _ _ => cases a0 <;> cases hLower
          | nil =>
            cases a0 with
            | copy pPl =>
              cases hp : pPl.asLocal with
              | none => simp only [hp] at hLower; cases hLower
              | some pl =>
                simp only [hp] at hLower; cases hLower
                have h := execBlock_append_assign st blk.stmts dst (.readViaDeref pl pointeeTy) target
                unfold execBlock at h ⊢
                rw [hTerm]
                simpa only [evalTerm, evalIntrinsicCall, hp] using h
            | move pPl =>
              cases hp : pPl.asLocal with
              | none => simp only [hp] at hLower; cases hLower
              | some pl =>
                simp only [hp] at hLower; cases hLower
                have h := execBlock_append_assign st blk.stmts dst (.readViaDeref pl pointeeTy) target
                unfold execBlock at h ⊢
                rw [hTerm]
                simpa only [evalTerm, evalIntrinsicCall, hp] using h
            | constVal _ _ | constUneval _ _ _ | runtimeChecks _ => cases hLower
      | discriminantValue =>
        cases args with
        | nil => cases hLower
        | cons a0 r0 =>
          cases a0 <;> try (cases hLower)
          cases r0 with
          | cons _ _ => cases hLower
          | nil =>
            rename_i pPl
            cases target with
            | none => cases hLower
            | some bb =>
              cases hLower
              have h := execBlock_append_assign st blk.stmts dst (.discriminant pPl) (some bb)
              unfold execBlock at h ⊢
              rw [hTerm]; exact h
      | sliceGetUnchecked retKind elemSize =>
        cases args with
        | nil => cases hLower
        | cons a0 r0 =>
          cases a0 <;> try (cases hLower)
          cases r0 with
          | nil => cases hLower
          | cons a1 r1 =>
            cases a1 <;> try (cases hLower)
            cases r1 with
            | cons _ _ => cases hLower
            | nil =>
              rename_i pPl iPl
              cases hind : pPl.isIndirect with
              | true => simp only [hind, ↓reduceIte] at hLower; cases hLower
              | false =>
                simp only [hind, Bool.false_eq_true, ↓reduceIte] at hLower
                cases target with
                | none => cases hLower
                | some bb =>
                  cases hi : iPl.asLocal with
                  | none => simp only [hi] at hLower; cases hLower
                  | some il =>
                    simp only [hi] at hLower; cases hLower
                    have h := execBlock_append_assign st blk.stmts dst
                      (.sliceIndexPtr retKind elemSize pPl il) (some bb)
                    unfold execBlock at h ⊢
                    rw [hTerm]
                    simpa only [evalTerm, evalIntrinsicCall, hi] using h
      | transmute srcTy dstTy =>
        cases args with
        | nil => cases hLower
        | cons arg r0 =>
          cases r0 with
          | cons _ _ => cases hLower
          | nil =>
            cases hLower
            have h := execBlock_append_assign st blk.stmts dst (.castTransmute srcTy dstTy arg) target
            unfold execBlock at h ⊢
            rw [hTerm]; exact h
      | transmuteUnchecked srcTy dstTy =>
        cases args with
        | nil => cases hLower
        | cons arg r0 =>
          cases r0 with
          | cons _ _ => cases hLower
          | nil =>
            cases hLower
            have h := execBlock_append_assign st blk.stmts dst (.castTransmute srcTy dstTy arg) target
            unfold execBlock at h ⊢
            rw [hTerm]; exact h
      | aggregateRawPtr retKind pt =>
        cases args with
        | nil => cases hLower
        | cons data r0 =>
          cases r0 with
          | nil => cases hLower
          | cons metaOp r1 =>
            cases r1 with
            | cons _ _ => cases hLower
            | nil =>
              cases target with
              | none => cases hLower
              | some bb =>
                cases hLower
                have h := execBlock_append_assign st blk.stmts dst
                  (.aggregateRawPtr retKind pt data metaOp) (some bb)
                unfold execBlock at h ⊢
                rw [hTerm]; exact h
      | ptrMetadata pk pt =>
        cases args with
        | nil => cases hLower
        | cons ptrOp r0 =>
          cases r0 with
          | cons _ _ => cases hLower
          | nil =>
            cases target with
            | none => cases hLower
            | some bb =>
              cases hLower
              have h := execBlock_append_assign st blk.stmts dst
                (.unOp (.ptrMetadata pk pt) ptrOp) (some bb)
              unfold execBlock at h ⊢
              rw [hTerm]; exact h

/-! ## Section 5: `LowerSliceLenCalls` Refinement, Gates, and CFG-Cache Defect -/

/-- Exact model of `LowerSliceLenCalls` (`compiler/rustc_mir_transform/src/lower_slice_len.rs:12-65`).
Fires iff `mirOptLevel >= 1`, `target = some bb`, `callSource = .normal`,
single argument `[arg]`, and `const_fn_def()` matches `slice_len_fn`. -/
def lowerSliceLenBlock (mirOptLevel : Nat) (blk : BasicBlock) : BasicBlock :=
  if Nat.ble 1 mirOptLevel then
    match blk.term with
    | .call (.sliceLenFn elemSize) [arg] dst (some bb) _unwind .normal =>
      { stmts := blk.stmts ++ [.assign dst (.unOp (.ptrMetadata .refShared (.slice elemSize)) arg)]
        term := .goto bb }
    | _ => blk
  else
    blk

/-- **Main Theorem 2 (`LowerSliceLenCalls` Call-to-`PtrMetadata` Refinement):**
For EVERY execution state `st`, EVERY `mirOptLevel`, and EVERY basic block `blk`,
`LowerSliceLenCalls` strictly refines (preserves exact operational equivalence,
including `&[T]` validity checking on dangling/null references) the source
`core::slice::<impl [T]>::len` call! -/
theorem lowerSliceLenCalls_refines_call (st : ExecState) (mirOptLevel : Nat) (blk : BasicBlock) :
    execBlock st (lowerSliceLenBlock mirOptLevel blk) = execBlock st blk := by
  unfold lowerSliceLenBlock
  cases hopt : Nat.ble 1 mirOptLevel with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    cases hTerm : blk.term with
    | goto _ | return_ | unreachable => rfl
    | call callee args dst target unwind cs =>
      cases callee with
      | intrinsic _ | fnPtrSliceLen _ | normalFn _ => rfl
      | sliceLenFn elemSize =>
        cases args with
        | nil => rfl
        | cons arg rest =>
          cases rest with
          | cons _ _ => rfl
          | nil =>
            cases target with
            | none => rfl
            | some bb =>
              cases cs with
              | misc | overloadedOperator => rfl
              | normal =>
                have h := execBlock_append_assign st blk.stmts dst
                  (.unOp (.ptrMetadata .refShared (.slice elemSize)) arg) (some bb)
                unfold execBlock at h ⊢
                rw [hTerm]; exact h

/-- Policy gate: at `-Zmir-opt-level=0`, `LowerSliceLenCalls` is a strict no-op. -/
theorem lowerSliceLenCalls_disabled_at_opt0 (blk : BasicBlock) :
    lowerSliceLenBlock 0 blk = blk := by
  rfl

/-- Indirect `FnPtr` calls (`let f: fn(&[T]) -> usize = <[T]>::len; f(s)`) are
NOT lowered because `func.const_fn_def()` returns `None`. -/
theorem lowerSliceLenCalls_skips_fn_ptr (optLevel elemSize : Nat) (stmts : List Stmt)
    (arg : Operand) (dst : Place) (bb : BlockId) (unwind : Option BlockId) :
    let blk : BasicBlock :=
      { stmts := stmts
        term := .call (.fnPtrSliceLen elemSize) [arg] dst (some bb) unwind .normal }
    lowerSliceLenBlock optLevel blk = blk := by
  unfold lowerSliceLenBlock
  cases Nat.ble 1 optLevel <;> rfl

/-- Non-`Normal` `CallSource` calls are NOT lowered (`lower_slice_len.rs:40`). -/
theorem lowerSliceLenCalls_skips_non_normal_call_source (optLevel elemSize : Nat)
    (stmts : List Stmt) (arg : Operand) (dst : Place) (bb : BlockId)
    (unwind : Option BlockId) :
    let blkMisc : BasicBlock :=
      { stmts := stmts
        term := .call (.sliceLenFn elemSize) [arg] dst (some bb) unwind .misc }
    let blkOp : BasicBlock :=
      { stmts := stmts
        term := .call (.sliceLenFn elemSize) [arg] dst (some bb) unwind .overloadedOperator }
    lowerSliceLenBlock optLevel blkMisc = blkMisc ∧
    lowerSliceLenBlock optLevel blkOp = blkOp := by
  unfold lowerSliceLenBlock
  cases Nat.ble 1 optLevel <;> exact ⟨rfl, rfl⟩

/-- Diverging `slice_len_fn` call (`target = none`) is NOT lowered (`lower_slice_len.rs:39`). -/
theorem lowerSliceLenCalls_skips_diverging_call (optLevel elemSize : Nat)
    (stmts : List Stmt) (arg : Operand) (dst : Place) (unwind : Option BlockId) :
    let blk : BasicBlock :=
      { stmts := stmts
        term := .call (.sliceLenFn elemSize) [arg] dst none unwind .normal }
    lowerSliceLenBlock optLevel blk = blk := by
  unfold lowerSliceLenBlock
  cases Nat.ble 1 optLevel <;> rfl

/-- CFG successor list of a terminator (normal + unwind cleanup targets). -/
def Term.successors : Term → List BlockId
  | .goto bb => [bb]
  | .return_ => []
  | .unreachable => []
  | .call _ _ _ target unwind _ =>
    (match target with | some b => [b] | none => []) ++
    (match unwind with | some u => [u] | none => [])

/-- **CFG-Cache Soundness Refutation for `lower_slice_len.rs:24-25`:**
The upstream comment `// The one successor remains unchanged, so no need to invalidate`
justifying `body.basic_blocks.as_mut_preserves_cfg()` is FALSE whenever the call has
an `UnwindAction::Cleanup(cleanupBb)` edge (empirically reproduced on
`probe_slice_len_sole_unwind_cleanup`, where `bb0 -> bb3 (cleanup)` is orphaned!). -/
theorem lowerSliceLenCalls_drops_cleanup_edge_invalidates_cfg
    (elemSize : Nat) (arg : Operand) (dst : Place) (normalBb cleanupBb : BlockId) :
    let blk : BasicBlock :=
      { stmts := []
        term := .call (.sliceLenFn elemSize) [arg] dst (some normalBb) (some cleanupBb) .normal }
    blk.term.successors = [normalBb, cleanupBb] ∧
    (lowerSliceLenBlock 1 blk).term.successors = [normalBb] ∧
    (lowerSliceLenBlock 1 blk).term.successors ≠ blk.term.successors := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-! ## Section 6: `PostAnalysisNormalize` & `CleanupPostBorrowck` Soundness -/

/-- Hidden-type environment mapping opaque type IDs to their revealed underlying types
(available under `TypingMode::PostAnalysis`, `mir/mod.rs:429-431`).
Returning `none` models an unnormalizable/impossible-clause fallback (`#91745`). -/
abbrev HiddenEnv := OpaqueId → Option MirTy

def normalizeTy (env : HiddenEnv) : MirTy → MirTy
  | .opaque oid =>
    match env oid with
    | some hidden => hidden
    | none => .opaque oid
  | t => t

def stripOpaqueCasts (ps : List ProjElem) : List ProjElem :=
  ps.foldr (fun e ih => match e with | .opaqueCast _ => ih | _ => e :: ih) []

def normalizePlace (useNextSolverGlobally : Bool) (p : Place) : Place :=
  if useNextSolverGlobally then p
  else { localId := p.localId, proj := stripOpaqueCasts p.proj }

/-- Simplified analysis-cleanup body metadata capturing `user_type_annotations`,
local types, and places. -/
structure CleanupBody where
  userTypeAnnotations : List Nat
  localUserTys : List (Option Nat)
  localTys : List MirTy
  places : List Place

/-- `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:79-83`): clears
`user_type_annotations` and all `decl.user_ty` fields BEFORE `PostAnalysisNormalize`. -/
def runCleanupPostBorrowck (b : CleanupBody) : CleanupBody :=
  { b with
    userTypeAnnotations := []
    localUserTys := b.localUserTys.map (fun _ => none) }

/-- `PostAnalysisNormalize` (`post_analysis_normalize.rs:14-98`): reveals opaque
types via `try_normalize_erasing_regions` and strips `ProjectionElem::OpaqueCast`
under the classic trait solver (`!next_trait_solver_globally()`). -/
def runPostAnalysisNormalize (env : HiddenEnv) (useNextSolverGlobally : Bool)
    (b : CleanupBody) : CleanupBody :=
  { b with
    localTys := b.localTys.map (normalizeTy env)
    places := b.places.map (normalizePlace useNextSolverGlobally) }

theorem cleanupPostBorrowck_clears_user_type_annotations (b : CleanupBody) :
    (runCleanupPostBorrowck b).userTypeAnnotations = [] ∧
    (runPostAnalysisNormalize (fun _ => none) false (runCleanupPostBorrowck b)).userTypeAnnotations = [] := by
  exact ⟨rfl, rfl⟩

theorem stripOpaqueCasts_hasOpaqueCast_false (ps : List ProjElem) :
    ProjList.hasOpaqueCast (stripOpaqueCasts ps) = false := by
  induction ps with
  | nil => rfl
  | cons e es ih =>
    unfold stripOpaqueCasts ProjList.hasOpaqueCast at ih ⊢
    cases e with
    | opaqueCast _ => exact ih
    | deref | phantomDeref | field _ | index _ =>
      simp only [List.foldr_cons, ih]

/-- Every place emitted by `PostAnalysisNormalize` (with classic solver) contains
ZERO `ProjectionElem::OpaqueCast` projections (`validate.rs:882-889`). -/
theorem postAnalysisNormalize_eliminates_opaque_cast (p : Place) :
    (normalizePlace false p).hasOpaqueCast = false := by
  exact stripOpaqueCasts_hasOpaqueCast_false p.proj

/-- Evaluates a field/`OpaqueCast` projection chain on a concrete `Val`. -/
def stepProjVal (v : Val) (e : ProjElem) : Option Val :=
  match e with
  | .opaqueCast _ => some v
  | .field 0 =>
    match v with
    | .structPair f0 _ => some (.int f0)
    | _ => none
  | .field 1 =>
    match v with
    | .structPair _ f1 => some (.int f1)
    | _ => none
  | _ => none

def evalProjVal (v : Val) (ps : List ProjElem) : Option Val :=
  (ps.foldr
    (fun e ih => fun cur =>
      match stepProjVal cur e with
      | some next => ih next
      | none => none)
    (fun cur => some cur)) v

theorem evalProjVal_cons (v : Val) (e : ProjElem) (es : List ProjElem) :
    evalProjVal v (e :: es) =
      match stepProjVal v e with
      | some next => evalProjVal next es
      | none => none := rfl

/-- `PostAnalysisNormalize` stripping of `OpaqueCast` strictly preserves runtime
place-projection evaluation for every value `v` and every projection list `ps`! -/
theorem postAnalysisNormalize_preserves_place_eval (v : Val) (ps : List ProjElem) :
    evalProjVal v (stripOpaqueCasts ps) = evalProjVal v ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | opaqueCast hidden =>
      change evalProjVal v (stripOpaqueCasts es) = evalProjVal v (.opaqueCast hidden :: es)
      rw [evalProjVal_cons]
      exact ih v
    | deref | phantomDeref | index _ =>
      change evalProjVal v (_ :: stripOpaqueCasts es) = evalProjVal v (_ :: es)
      rw [evalProjVal_cons, evalProjVal_cons]
      rfl
    | field idx =>
      change evalProjVal v (.field idx :: stripOpaqueCasts es) = evalProjVal v (.field idx :: es)
      rw [evalProjVal_cons, evalProjVal_cons]
      cases stepProjVal v (.field idx) with
      | none => rfl
      | some next => exact ih next

/-- When `env` resolves an opaque ID, `normalizeTy` reveals the hidden type; when
`env oid = none` (impossible where-clause fallback `#91745`), `normalizeTy` leaves
`.opaque oid` intact without panicking. -/
theorem postAnalysisNormalize_reveals_or_preserves_on_impossible (env : HiddenEnv) (oid : OpaqueId) :
    (∀ hTy, env oid = some hTy → normalizeTy env (.opaque oid) = hTy) ∧
    (env oid = none → normalizeTy env (.opaque oid) = .opaque oid) := by
  refine ⟨?_, ?_⟩
  · intro hTy h; simp only [normalizeTy, h]
  · intro h; simp only [normalizeTy, h]

/-! ## Section 7: `trivial_const` Chained Fast-Path Equivalence & Guard Necessity -/

/-- `DefKind` subset relevant to `trivial_const.rs:55-59`. -/
inductive ConstDefKind where
  | constItem
  | assocConst
  | anonConst (isNonTypeSystemInline : Bool)
  | staticItem
  | fnItem

/-- A constant item's `mir_built` body and metadata inspected by `trivial_const`. -/
structure ConstItem where
  defKind : ConstDefKind
  hasImpossibleClauses : Bool
  definesOpaqueTypes : Bool
  bodyHasOpaqueTypes : Bool
  blocks : List BasicBlock
  returnTy : MirTy

abbrev ConstEnv := DefId → Option ConstItem

/-- Whether `DefKind` is admitted by `trivial_const.rs:55-59` (`137d1d49458b`). -/
def ConstDefKind.admittedHead : ConstDefKind → Bool
  | .constItem => true
  | .assocConst => true
  | .anonConst isInline => !isInline
  | .staticItem => false
  | .fnItem => false

/-- Syntactic shape classification of a trivial-const body (`trivial_const.rs:79-112`):
exact 1 BB, exact 1 statement `_0 = Operand::Constant(...)`, `Return` terminator. -/
inductive TrivialBodyShape where
  | literal (v : Val) (ty : MirTy)
  | chainedRef (targetDef : DefId) (args : List MirTy) (ty : MirTy)
  | nonTrivial

def classifyTrivialBody (blocks : List BasicBlock) : TrivialBodyShape :=
  match blocks with
  | [{ stmts := [.assign dst (.use op)], term := .return_ }] =>
    match dst.asLocal with
    | some 0 =>
      match op with
      | .constVal v ty => .literal v ty
      | .constUneval d args ty => .chainedRef d args ty
      | _ => .nonTrivial
    | _ => .nonTrivial
  | _ => .nonTrivial

/-- Guarded `trivial_const` matching `rust-lang/rust` HEAD `137d1d49458b`
(`compiler/rustc_mir_transform/src/trivial_const.rs:46-113`), fuel-indexed over
chained `Const::Unevaluated` hops (`args.is_empty()`). -/
def trivialConst (env : ConstEnv) (fuel : Nat) (defId : DefId) : Option (Val × MirTy) :=
  (Nat.rec (motive := fun _ => DefId → Option (Val × MirTy))
    (fun _ => none)
    (fun _ ih d =>
      match env d with
      | none => none
      | some item =>
        if !item.defKind.admittedHead then none
        else if item.hasImpossibleClauses then none
        else if item.definesOpaqueTypes then none
        else if item.bodyHasOpaqueTypes then none
        else
          match classifyTrivialBody item.blocks with
          | .literal v ty => some (v, ty)
          | .chainedRef nextDef args _ =>
            if args.isEmpty then ih nextDef else none
          | .nonTrivial => none)
    fuel) defId

/-- Unguarded `trivial_const` omitting `has_impossible_clauses` (matching
`14210df0e27c` `1.98.0-nightly`). -/
def trivialConstWithoutImpossibleGuard (env : ConstEnv) (fuel : Nat) (defId : DefId) :
    Option (Val × MirTy) :=
  (Nat.rec (motive := fun _ => DefId → Option (Val × MirTy))
    (fun _ => none)
    (fun _ ih d =>
      match env d with
      | none => none
      | some item =>
        if !item.defKind.admittedHead then none
        else if item.definesOpaqueTypes then none
        else if item.bodyHasOpaqueTypes then none
        else
          match classifyTrivialBody item.blocks with
          | .literal v ty => some (v, ty)
          | .chainedRef nextDef args _ =>
            if args.isEmpty then ih nextDef else none
          | .nonTrivial => none)
    fuel) defId

/-- Unguarded `trivial_const` omitting `!opaque_types_defined_by.is_empty()` and
`body.has_opaque_types()`. -/
def trivialConstWithoutOpaqueGuard (env : ConstEnv) (fuel : Nat) (defId : DefId) :
    Option (Val × MirTy) :=
  (Nat.rec (motive := fun _ => DefId → Option (Val × MirTy))
    (fun _ => none)
    (fun _ ih d =>
      match env d with
      | none => none
      | some item =>
        if !item.defKind.admittedHead then none
        else if item.hasImpossibleClauses then none
        else
          match classifyTrivialBody item.blocks with
          | .literal v ty => some (v, ty)
          | .chainedRef nextDef args _ =>
            if args.isEmpty then ih nextDef else none
          | .nonTrivial => none)
    fuel) defId

/-- Full CTFE pipeline model (`ImpossibleClauses` -> opaque-type borrowck/normalization
-> MIR interpretation) for a constant item. -/
def evalFullCtfe (env : ConstEnv) (fuel : Nat) (defId : DefId) : Except FaultKind (Val × MirTy) :=
  (Nat.rec (motive := fun _ => DefId → Except FaultKind (Val × MirTy))
    (fun _ => .error .unsupportedOp)
    (fun _ ih d =>
      match env d with
      | none => .error .unsupportedOp
      | some item =>
        if item.hasImpossibleClauses then
          .error .unreachableUb
        else if item.definesOpaqueTypes || item.bodyHasOpaqueTypes then
          .error .invalidValueUb
        else
          match classifyTrivialBody item.blocks with
          | .literal v ty => .ok (v, ty)
          | .chainedRef nextDef args _ =>
            if args.isEmpty then
              ih nextDef
            else
              .error .unsupportedOp
          | .nonTrivial => .error .unsupportedOp)
    fuel) defId

theorem trivialConst_zero (env : ConstEnv) (d : DefId) :
    trivialConst env 0 d = none := rfl

theorem trivialConst_succ (env : ConstEnv) (k : Nat) (d : DefId) :
    trivialConst env (k + 1) d =
      match env d with
      | none => none
      | some item =>
        if !item.defKind.admittedHead then none
        else if item.hasImpossibleClauses then none
        else if item.definesOpaqueTypes then none
        else if item.bodyHasOpaqueTypes then none
        else
          match classifyTrivialBody item.blocks with
          | .literal v ty => some (v, ty)
          | .chainedRef nextDef args _ =>
            if args.isEmpty then trivialConst env k nextDef else none
          | .nonTrivial => none := rfl

theorem evalFullCtfe_succ (env : ConstEnv) (k : Nat) (d : DefId) :
    evalFullCtfe env (k + 1) d =
      match env d with
      | none => .error .unsupportedOp
      | some item =>
        if item.hasImpossibleClauses then
          .error .unreachableUb
        else if item.definesOpaqueTypes || item.bodyHasOpaqueTypes then
          .error .invalidValueUb
        else
          match classifyTrivialBody item.blocks with
          | .literal v ty => .ok (v, ty)
          | .chainedRef nextDef args _ =>
            if args.isEmpty then
              evalFullCtfe env k nextDef
            else
              .error .unsupportedOp
          | .nonTrivial => .error .unsupportedOp := rfl

/-- **Main Theorem 3A (`trivial_const` Chained Evaluation Equivalence to Full CTFE):**
For ANY constant environment `env`, ANY chain depth `fuel`, and ANY constant `defId`,
whenever guarded `trivialConst env fuel defId` returns `some (v, ty)`, the full
CTFE pipeline (`ImpossibleClauses` + opaque checks + recursive MIR evaluation)
evaluates `defId` to the EXACT same `.ok (v, ty)`! -/
theorem trivialConst_eval_equiv_ctfe (env : ConstEnv) (fuel : Nat) (defId : DefId)
    (v : Val) (ty : MirTy)
    (hTriv : trivialConst env fuel defId = some (v, ty)) :
    evalFullCtfe env fuel defId = .ok (v, ty) := by
  induction fuel generalizing defId with
  | zero =>
    rw [trivialConst_zero] at hTriv
    cases hTriv
  | succ k ih =>
    rw [trivialConst_succ] at hTriv
    rw [evalFullCtfe_succ]
    cases hEnv : env defId with
    | none =>
      rw [hEnv] at hTriv
      cases hTriv
    | some item =>
      rw [hEnv] at hTriv
      cases hAdm : item.defKind.admittedHead with
      | false =>
        simp only [hAdm, Bool.not_false, ↓reduceIte] at hTriv
        cases hTriv
      | true =>
        simp only [hAdm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTriv
        cases hImp : item.hasImpossibleClauses with
        | true =>
          simp only [hImp, ↓reduceIte] at hTriv
          cases hTriv
        | false =>
          simp only [hImp, Bool.false_eq_true, ↓reduceIte] at hTriv ⊢
          cases hDefOp : item.definesOpaqueTypes with
          | true =>
            simp only [hDefOp, ↓reduceIte] at hTriv
            cases hTriv
          | false =>
            simp only [hDefOp, Bool.false_eq_true, ↓reduceIte, Bool.false_or] at hTriv ⊢
            cases hBodyOp : item.bodyHasOpaqueTypes with
            | true =>
              simp only [hBodyOp, ↓reduceIte] at hTriv
              cases hTriv
            | false =>
              simp only [hBodyOp, Bool.false_eq_true, ↓reduceIte] at hTriv ⊢
              cases hShape : classifyTrivialBody item.blocks with
              | nonTrivial =>
                rw [hShape] at hTriv
                cases hTriv
              | literal v' ty' =>
                rw [hShape] at hTriv
                injection hTriv with hPair
                dsimp only
                rw [hPair]
              | chainedRef nextDef args ty' =>
                rw [hShape] at hTriv
                cases hArgs : args.isEmpty with
                | false =>
                  simp only [hArgs, Bool.false_eq_true, ↓reduceIte] at hTriv
                  cases hTriv
                | true =>
                  simp only [hArgs, ↓reduceIte] at hTriv ⊢
                  exact ih nextDef hTriv

/-- Concrete 3-hop chain witness (`TRIV_A = 42`, `TRIV_B = TRIV_A`,
`TRIV_C_CHAIN2 = TRIV_B`): both `trivialConst` and `evalFullCtfe` resolve all
three to `(Val.int 42, MirTy.usize)`. -/
def chainEnv : ConstEnv
  | 0 =>
    some { defKind := .constItem
           hasImpossibleClauses := false
           definesOpaqueTypes := false
           bodyHasOpaqueTypes := false
           blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constVal (.int 42) .usize))]
                        term := .return_ }]
           returnTy := .usize }
  | 1 =>
    some { defKind := .constItem
           hasImpossibleClauses := false
           definesOpaqueTypes := false
           bodyHasOpaqueTypes := false
           blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constUneval 0 [] .usize))]
                        term := .return_ }]
           returnTy := .usize }
  | 2 =>
    some { defKind := .constItem
           hasImpossibleClauses := false
           definesOpaqueTypes := false
           bodyHasOpaqueTypes := false
           blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constUneval 1 [] .usize))]
                        term := .return_ }]
           returnTy := .usize }
  | _ => none

theorem trivialConst_chain2_resolves_concrete :
    trivialConst chainEnv 4 2 = some (.int 42, .usize) ∧
    evalFullCtfe chainEnv 4 2 = .ok (.int 42, .usize) := by
  refine ⟨rfl, ?_⟩
  exact trivialConst_eval_equiv_ctfe chainEnv 4 2 (.int 42) .usize rfl

/-- **Main Theorem 3B (`has_impossible_clauses` Soundness Guard Necessity Counterexample):**
Constructs `IMPOSSIBLE_CLAUSE_TRIV: usize = 7 where String: Copy` (matching our live
`rustc 1.98.0-nightly` probe where `IMPOSSIBLE_CLAUSE_TRIV` bypassed `ImpossiblePredicates`
and succeeded while `IMPOSSIBLE_CLAUSE_NON_TRIV = 3 + 4` failed with `E0080`):
1. Unguarded `trivialConstWithoutImpossibleGuard` (pre-guard `14210df0e27c`) returns
   `some (.int 7, .usize)`.
2. Full CTFE (`evalFullCtfe`, running `ImpossibleClauses` -> `bb0: { unreachable; }`)
   returns `.error .unreachableUb` — DIRECTLY DISAGREEING with the unguarded fast path!
3. Guarded `trivialConst` (`137d1d49458b`, `trivial_const.rs:65-67`) returns `none`,
   forcing fallback to full CTFE and restoring exact equivalence! -/
theorem trivialConst_without_impossibleClauses_unsound_counterexample :
    let impossibleItem : ConstItem :=
      { defKind := .constItem
        hasImpossibleClauses := true
        definesOpaqueTypes := false
        bodyHasOpaqueTypes := false
        blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constVal (.int 7) .usize))]
                     term := .return_ }]
        returnTy := .usize }
    let env : ConstEnv := fun d => if Nat.beq d 0 then some impossibleItem else none
    trivialConstWithoutImpossibleGuard env 2 0 = some (.int 7, .usize) ∧
    evalFullCtfe env 2 0 = .error .unreachableUb ∧
    trivialConst env 2 0 = none := by
  refine ⟨rfl, rfl, rfl⟩

/-- Counterexample proving necessity of `!tcx.opaque_types_defined_by(def).is_empty()`
and `body.has_opaque_types()` (`trivial_const.rs:69-77`):
without these guards, a constant defining an opaque type (`NON_TRIV_OPAQUE_DEF: HiddenCopy = 99`)
would skip `mir_borrowck` / opaque-type hidden-type definition and silently diverge
from full CTFE. -/
theorem trivialConst_without_opaqueGuard_counterexample :
    let opaqueItem : ConstItem :=
      { defKind := .constItem
        hasImpossibleClauses := false
        definesOpaqueTypes := true
        bodyHasOpaqueTypes := true
        blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constVal (.int 99) (.opaque 0)))]
                     term := .return_ }]
        returnTy := .opaque 0 }
    let env : ConstEnv := fun d => if Nat.beq d 0 then some opaqueItem else none
    trivialConstWithoutOpaqueGuard env 2 0 = some (.int 99, .opaque 0) ∧
    evalFullCtfe env 2 0 = .error .invalidValueUb ∧
    trivialConst env 2 0 = none := by
  refine ⟨rfl, rfl, rfl⟩

/-- Guard theorem (`trivial_const.rs:106-108`): referencing a generic associated
constant (`GenHolder::<u8>::ASSOC_TRIV`, non-empty `args = [.u32]`) is rejected by
`trivial_const`, forcing the full MIR pipeline. -/
theorem trivialConst_rejects_nonempty_generic_args :
    let env : ConstEnv
      | 0 =>
        some { defKind := .assocConst
               hasImpossibleClauses := false
               definesOpaqueTypes := false
               bodyHasOpaqueTypes := false
               blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constVal (.int 7) .usize))]
                            term := .return_ }]
               returnTy := .usize }
      | 1 =>
        some { defKind := .constItem
               hasImpossibleClauses := false
               definesOpaqueTypes := false
               bodyHasOpaqueTypes := false
               blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constUneval 0 [.u32] .usize))]
                            term := .return_ }]
               returnTy := .usize }
      | _ => none
    trivialConst env 3 0 = some (.int 7, .usize) ∧
    trivialConst env 3 1 = none := by
  refine ⟨rfl, rfl⟩

/-- Guard theorem (`trivial_const.rs:57` added in `137d1d49458b`):
`DefKind::AnonConst` with `AnonConstKind::NonTypeSystemInline` (`isInline = true`)
is rejected by `trivial_const`, whereas type-system `AnonConst` (`isInline = false`)
remains admitted. -/
theorem trivialConst_rejects_non_type_system_inline_anon_const :
    let mkAnon (isInline : Bool) : ConstItem :=
      { defKind := .anonConst isInline
        hasImpossibleClauses := false
        definesOpaqueTypes := false
        bodyHasOpaqueTypes := false
        blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constVal (.int 1) .usize))]
                     term := .return_ }]
        returnTy := .usize }
    let env : ConstEnv
      | 0 => some (mkAnon true)
      | 1 => some (mkAnon false)
      | _ => none
    trivialConst env 2 0 = none ∧
    trivialConst env 2 1 = some (.int 1, .usize) := by
  refine ⟨rfl, rfl⟩

/-- Non-trivial arithmetic const (`NON_TRIV_ARITH = 40 + 2`) has `Rvalue::BinaryOp`
and multiple blocks, so `trivialConst` returns `none`. -/
theorem trivialConst_rejects_arithmetic_body :
    let arithItem : ConstItem :=
      { defKind := .constItem
        hasImpossibleClauses := false
        definesOpaqueTypes := false
        bodyHasOpaqueTypes := false
        blocks :=
          [{ stmts := [.assign (Place.ofLocal 1)
                        (.binOp .addWithOverflow (.constVal (.int 40) .usize)
                                                 (.constVal (.int 2) .usize))]
             term := .goto 1 },
           { stmts := [.assign (Place.ofLocal 0) (.use (.copy (Place.ofLocal 1)))]
             term := .return_ }]
        returnTy := .usize }
    let env : ConstEnv := fun d => if Nat.beq d 0 then some arithItem else none
    trivialConst env 2 0 = none := by
  rfl

/-- `DefKind::Static` and `DefKind::Fn` are unconditionally rejected by `trivial_const`
(`trivial_const.rs:55-59`) even when syntactically single-block constant returns. -/
theorem trivialConst_rejects_static_and_fn :
    let mkKind (k : ConstDefKind) : ConstItem :=
      { defKind := k
        hasImpossibleClauses := false
        definesOpaqueTypes := false
        bodyHasOpaqueTypes := false
        blocks := [{ stmts := [.assign (Place.ofLocal 0) (.use (.constVal (.int 5) .usize))]
                     term := .return_ }]
        returnTy := .usize }
    let env : ConstEnv
      | 0 => some (mkKind .staticItem)
      | 1 => some (mkKind .fnItem)
      | _ => none
    trivialConst env 2 0 = none ∧
    trivialConst env 2 1 = none := by
  refine ⟨rfl, rfl⟩

end RustcMirLowerIntrinsicsSoundness
