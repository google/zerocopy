/-
  UnsafeBindersManglingValidityAndScalarizeSoundness.lean

  Self-contained Lean v4.34.1 mechanization of Rust `feature(unsafe_binders)`
  (`unsafe<'a> T`, `Rvalue::WrapUnsafeBinder`, `ProjectionElem::UnwrapUnsafeBinder`):

  1. Type System, `!Copy` Enforcement, `BikeshedGuaranteedNoDrop` Well-Formedness,
     Layout Transparency, and Bound-Region Erasure (`eraseBoundRegions`).
  2. Operational Semantics of `WrapUnsafeBinder` / `UnwrapUnsafeBinder` with
     Recursive Inner-Type Validity & Aliasing-Tag Delegation (fixing `validity.rs:987`)
     and proof that `-Zmiri-disable-validation` (`ValidationMode.no`) disables
     the borrow tracker (`borrow_tracker = None`), hiding aliasing & validity UB.
  3. MIR Execution Semantics (`deinitMovedPlace : Bool`, honoring `deinitMovedPlace = true`),
     Soundness of Algebraic Cancellation `UnwrapUnsafeBinder(WrapUnsafeBinder(v)) = v`,
     GVN opacity diagnosis, and `SROA` Binder-Unwrapping Scalarization simulation.
  4. Total Prefix-Free `v0` Symbol-Mangling Production Extension (`Z [G<n>_] <ty>`)
     for `TyKind::UnsafeBinder(Binder<Ty>)` (eliminating `v0.rs:679`) with a
     constructive round-trip decoder and full injectivity proof (zero collisions
     across RFC 2603 / `v0.rs` type and `FnPtr` productions).

  Purity contract:
  - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
    zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
  - Every `def` is declared `noncomputable def` without `deriving` clauses.
-/

namespace UnsafeBindersFormal

/-! ## Part I: List, Arithmetic, and Region/Type Preliminaries -/

/-- Pure structural `List.get?` avoiding `Init` auxiliaries. -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Pure structural `List.set` avoiding `List.set._unsafe_rec`. -/
noncomputable def listSet {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

theorem listGet?_listSet_eq {α : Type} :
    ∀ (xs : List α) (i : Nat) (old v : α),
      listGet? xs i = some old →
      listGet? (listSet xs i v) i = some v := by
  intro xs
  induction xs with
  | nil =>
      intro i old v h
      cases i <;> simp [listGet?] at h
  | cons x xs ih =>
      intro i old v h
      cases i with
      | zero =>
          simp [listSet, listGet?]
      | succ i' =>
          simp only [listSet, listGet?]
          exact ih i' old v h

theorem listGet?_listSet_ne {α : Type} :
    ∀ (xs : List α) (i j : Nat) (v : α),
      i ≠ j →
      listGet? (listSet xs i v) j = listGet? xs j := by
  intro xs
  induction xs with
  | nil =>
      intro i j v _
      cases i <;> cases j <;> rfl
  | cons x xs ih =>
      intro i j v hne
      cases i with
      | zero =>
          cases j with
          | zero => exact False.elim (hne rfl)
          | succ j' => rfl
      | succ i' =>
          cases j with
          | zero => rfl
          | succ j' =>
              simp only [listSet, listGet?]
              apply ih
              intro heq
              apply hne
              rw [heq]

theorem listSet_listSet_same {α : Type} :
    ∀ (xs : List α) (i : Nat) (v1 v2 : α),
      listSet (listSet xs i v1) i v2 = listSet xs i v2 := by
  intro xs
  induction xs with
  | nil =>
      intro i v1 v2
      cases i <;> rfl
  | cons x xs ih =>
      intro i v1 v2
      cases i with
      | zero => rfl
      | succ i' =>
          simp only [listSet]
          rw [ih i' v1 v2]

/-- Constructive `Nat` equality. -/
noncomputable def natBeq : Nat → Nat → Bool
  | 0, 0 => true
  | m + 1, n + 1 => natBeq m n
  | _, _ => false

theorem natBeq_true_iff : ∀ a b : Nat, natBeq a b = true ↔ a = b := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b with
      | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ _ => exact ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h⟩
  | succ a' ih =>
      intro b
      cases b with
      | zero => exact ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h⟩
      | succ b' =>
          have ih' := ih b'
          exact ⟨fun h => congrArg Nat.succ (ih'.mp h), fun h => ih'.mpr (Nat.succ.inj h)⟩

theorem natBeq_false_iff (a b : Nat) : natBeq a b = false ↔ a ≠ b := by
  constructor
  · intro h heq
    have ht := (natBeq_true_iff a b).mpr heq
    rw [h] at ht
    contradiction
  · intro hne
    cases h : natBeq a b with
    | false => rfl
    | true => exact False.elim (hne ((natBeq_true_iff a b).mp h))

theorem natBeq_refl (a : Nat) : natBeq a a = true :=
  (natBeq_true_iff a a).mpr rfl

/-- Constructive `Nat` strict comparison `a < b`. -/
noncomputable def natBlt : Nat → Nat → Bool
  | _, 0 => false
  | 0, _ + 1 => true
  | m + 1, n + 1 => natBlt m n

theorem natBlt_true_iff : ∀ a b : Nat, natBlt a b = true ↔ a < b := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b with
      | zero => simp [natBlt]
      | succ b' => simp [natBlt, Nat.zero_lt_succ]
  | succ a' ih =>
      intro b
      cases b with
      | zero => simp [natBlt]
      | succ b' =>
          simp only [natBlt, ih b']
          constructor
          · exact Nat.succ_lt_succ
          · exact Nat.lt_of_succ_lt_succ

theorem natBlt_false_iff (a b : Nat) : natBlt a b = false ↔ b ≤ a := by
  constructor
  · intro h
    cases Nat.lt_or_ge a b with
    | inl hlt =>
        have ht := (natBlt_true_iff a b).mpr hlt
        rw [h] at ht
        contradiction
    | inr hle => exact hle
  · intro hle
    cases h : natBlt a b with
    | false => rfl
    | true =>
        have hlt := (natBlt_true_iff a b).mp h
        exact False.elim (Nat.not_lt_of_ge hle hlt)

/-- Constructive `Bool` equality. -/
noncomputable def boolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- De Bruijn region representation matching `rustc_type_ir::Region`. -/
inductive Region where
  | erased
  | bound (debruijn : Nat) (varIdx : Nat)

noncomputable def Region.beq : Region → Region → Bool
  | .erased, .erased => true
  | .bound d1 v1, .bound d2 v2 => natBeq d1 d2 && natBeq v1 v2
  | _, _ => false

theorem Region.beq_true_iff : ∀ r1 r2 : Region, Region.beq r1 r2 = true ↔ r1 = r2 := by
  intro r1 r2
  cases r1 <;> cases r2 <;> simp [Region.beq]
  case bound.bound d1 v1 d2 v2 =>
    constructor
    · intro ⟨hd, hv⟩
      exact ⟨(natBeq_true_iff d1 d2).mp hd, (natBeq_true_iff v1 v2).mp hv⟩
    · intro ⟨hd, hv⟩
      exact ⟨(natBeq_true_iff d1 d2).mpr hd, (natBeq_true_iff v1 v2).mpr hv⟩

/-- Subset of `rustc_type_ir::TyKind` centered on `UnsafeBinder` and its interactions. -/
inductive Ty where
  | bool
  | u32
  | u64
  | unit
  | never
  | ref (mutbl : Bool) (reg : Region) (inner : Ty)
  | rawPtr (mutbl : Bool) (inner : Ty)
  | manuallyDrop (inner : Ty)
  | tuple (fields : List Ty)
  | unsafeBinder (boundLifetimes : Nat) (inner : Ty)

/- Structural equality on `Ty` and `List Ty`. -/
mutual
  noncomputable def Ty.beq : Ty → Ty → Bool
    | .bool, .bool => true
    | .u32, .u32 => true
    | .u64, .u64 => true
    | .unit, .unit => true
    | .never, .never => true
    | .ref m1 r1 t1, .ref m2 r2 t2 =>
        boolBeq m1 m2 && Region.beq r1 r2 && Ty.beq t1 t2
    | .rawPtr m1 t1, .rawPtr m2 t2 =>
        boolBeq m1 m2 && Ty.beq t1 t2
    | .manuallyDrop t1, .manuallyDrop t2 => Ty.beq t1 t2
    | .tuple fs1, .tuple fs2 => Ty.beqList fs1 fs2
    | .unsafeBinder n1 t1, .unsafeBinder n2 t2 =>
        natBeq n1 n2 && Ty.beq t1 t2
    | _, _ => false

  noncomputable def Ty.beqList : List Ty → List Ty → Bool
    | [], [] => true
    | x :: xs, y :: ys => Ty.beq x y && Ty.beqList xs ys
    | _, _ => false
end

/-- Instantiate the outermost `UnsafeBinder` depth `k` with `Region.erased`,
    modeling `TyCtxt::instantiate_bound_regions_with_erased` (`validate.rs:899,1470`,
    `layout.rs:875`, `needs_drop.rs:240`). -/
noncomputable def eraseRegionAt (k : Nat) : Region → Region
  | .erased => .erased
  | .bound d v =>
      if natBeq d k then .erased
      else if natBlt k d then .bound (d - 1) v
      else .bound d v

mutual
  noncomputable def eraseBoundRegions (k : Nat) : Ty → Ty
    | .bool => .bool
    | .u32 => .u32
    | .u64 => .u64
    | .unit => .unit
    | .never => .never
    | .ref m r inner => .ref m (eraseRegionAt k r) (eraseBoundRegions k inner)
    | .rawPtr m inner => .rawPtr m (eraseBoundRegions k inner)
    | .manuallyDrop inner => .manuallyDrop (eraseBoundRegions k inner)
    | .tuple fs => .tuple (eraseBoundRegionsList k fs)
    | .unsafeBinder n inner => .unsafeBinder n (eraseBoundRegions (k + 1) inner)

  noncomputable def eraseBoundRegionsList (k : Nat) : List Ty → List Ty
    | [] => []
    | t :: ts => eraseBoundRegions k t :: eraseBoundRegionsList k ts
end

/-- Outermost binder instantiation (`k = 0`). -/
noncomputable def instantiateBinder (inner : Ty) : Ty :=
  eraseBoundRegions 0 inner

/-- Predicate characterizing types whose bound regions are strictly below `depth`. -/
noncomputable def regionClosed (depth : Nat) : Region → Prop
  | .erased => True
  | .bound d _ => d < depth

/- Structural closedness over `Ty` and `List Ty`. -/
mutual
  noncomputable def tyClosed (depth : Nat) : Ty → Prop
    | .bool => True
    | .u32 => True
    | .u64 => True
    | .unit => True
    | .never => True
    | .ref _ r inner => regionClosed depth r ∧ tyClosed depth inner
    | .rawPtr _ inner => tyClosed depth inner
    | .manuallyDrop inner => tyClosed depth inner
    | .tuple fs => tyListClosed depth fs
    | .unsafeBinder _ inner => tyClosed (depth + 1) inner

  noncomputable def tyListClosed (depth : Nat) : List Ty → Prop
    | [] => True
    | t :: ts => tyClosed depth t ∧ tyListClosed depth ts
end

theorem eraseRegionAt_of_lt (k : Nat) (r : Region) (hc : regionClosed k r) :
    eraseRegionAt k r = r := by
  cases r with
  | erased => rfl
  | bound d v =>
      have hlt : d < k := hc
      have hne : natBeq d k = false := by
        cases h : natBeq d k with
        | false => rfl
        | true =>
            have heq := (natBeq_true_iff d k).mp h
            rw [heq] at hlt
            exact False.elim (Nat.lt_irrefl k hlt)
      have hblt : natBlt k d = false :=
        (natBlt_false_iff k d).mpr (Nat.le_of_lt hlt)
      simp [eraseRegionAt, hne, hblt]

theorem eraseBoundRegions_closed :
    ∀ (t : Ty) (k : Nat), tyClosed k t → eraseBoundRegions k t = t := by
  intro t
  refine Ty.rec
    (motive_1 := fun t => ∀ k, tyClosed k t → eraseBoundRegions k t = t)
    (motive_2 := fun ts => ∀ k, tyListClosed k ts → eraseBoundRegionsList k ts = ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · intro m r inner ih k ⟨hr, hi⟩
    simp only [eraseBoundRegions, eraseRegionAt_of_lt k r hr, ih k hi]
  · intro m inner ih k hi
    simp only [eraseBoundRegions, ih k hi]
  · intro inner ih k hi
    simp only [eraseBoundRegions, ih k hi]
  · intro fs ih k hfs
    simp only [eraseBoundRegions, ih k hfs]
  · intro n inner ih k hi
    simp only [eraseBoundRegions, ih (k + 1) hi]
  · intro _ _; rfl
  · intro hd tl ihd iht k ⟨hh, ht⟩
    simp only [eraseBoundRegionsList, ihd k hh, iht k ht]

theorem eraseRegionAt_reduces_closed (k : Nat) (r : Region) (hc : regionClosed (k + 1) r) :
    regionClosed k (eraseRegionAt k r) := by
  cases r with
  | erased => trivial
  | bound d v =>
      have hlt : d < k + 1 := hc
      cases h : natBeq d k with
      | true =>
          simp [eraseRegionAt, h, regionClosed]
      | false =>
          have hne : d ≠ k := fun heq => by
            have ht := (natBeq_true_iff d k).mpr heq
            rw [h] at ht; contradiction
          have hle : d ≤ k := Nat.le_of_lt_succ hlt
          have hdk : d < k := Nat.lt_of_le_of_ne hle hne
          have hblt : natBlt k d = false := (natBlt_false_iff k d).mpr (Nat.le_of_lt hdk)
          simp [eraseRegionAt, h, hblt, regionClosed, hdk]

theorem eraseBoundRegions_reduces_closed :
    ∀ (t : Ty) (k : Nat), tyClosed (k + 1) t → tyClosed k (eraseBoundRegions k t) := by
  intro t
  refine Ty.rec
    (motive_1 := fun t => ∀ k, tyClosed (k + 1) t → tyClosed k (eraseBoundRegions k t))
    (motive_2 := fun ts => ∀ k, tyListClosed (k + 1) ts → tyListClosed k (eraseBoundRegionsList k ts))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro m r inner ih k ⟨hr, hi⟩
    exact ⟨eraseRegionAt_reduces_closed k r hr, ih k hi⟩
  · intro m inner ih k hi
    exact ih k hi
  · intro inner ih k hi
    exact ih k hi
  · intro fs ih k hfs
    exact ih k hfs
  · intro n inner ih k hi
    exact ih (k + 1) hi
  · intro _ _; trivial
  · intro hd tl ihd iht k ⟨hh, ht⟩
    exact ⟨ihd k hh, iht k ht⟩

/- `rustc_trait_selection/src/traits/select/candidate_assembly.rs:1174-1176`:
   `ty::UnsafeBinder(_)` assembles NO `Copy`/`Clone` builtin candidate. -/
mutual
  noncomputable def tyIsCopy : Ty → Bool
    | .bool => true
    | .u32 => true
    | .u64 => true
    | .unit => true
    | .never => true
    | .ref false _ _ => true
    | .ref true _ _ => false
    | .rawPtr _ _ => true
    | .manuallyDrop _ => false
    | .tuple fs => tyListIsCopy fs
    | .unsafeBinder _ _ => false

  noncomputable def tyListIsCopy : List Ty → Bool
    | [] => true
    | t :: ts => tyIsCopy t && tyListIsCopy ts
end

theorem tyIsCopy_unsafeBinder_false (n : Nat) (inner : Ty) :
    tyIsCopy (.unsafeBinder n inner) = false :=
  rfl

/- `rustc_trait_selection/src/traits/select/confirmation.rs:1190-1250` &
   `rustc_trait_selection/src/traits/wf.rs:978-993`:
   Well-formedness of `unsafe<'a> T` requires `T : BikeshedGuaranteedNoDrop`. -/
mutual
  noncomputable def bikeshedGuaranteedNoDrop : Ty → Bool
    | .ref _ _ _ => true
    | .manuallyDrop _ => true
    | .tuple fs => tyListBikeshed fs
    | t => tyIsCopy t

  noncomputable def tyListBikeshed : List Ty → Bool
    | [] => true
    | t :: ts => bikeshedGuaranteedNoDrop t && tyListBikeshed ts
end

/- Well-formedness judgment matching `wf.rs:978-993`. -/
mutual
  noncomputable def tyWellFormed : Ty → Bool
    | .bool => true
    | .u32 => true
    | .u64 => true
    | .unit => true
    | .never => true
    | .ref _ _ inner => tyWellFormed inner
    | .rawPtr _ inner => tyWellFormed inner
    | .manuallyDrop inner => tyWellFormed inner
    | .tuple fs => tyListWellFormed fs
    | .unsafeBinder _ inner => tyWellFormed inner && bikeshedGuaranteedNoDrop inner

  noncomputable def tyListWellFormed : List Ty → Bool
    | [] => true
    | t :: ts => tyWellFormed t && tyListWellFormed ts
end

theorem wf_accepts_mut_ref_binder (n : Nat) :
    tyWellFormed (.unsafeBinder n (.ref true (.bound 0 0) .u32)) = true :=
  rfl

theorem wf_accepts_manuallyDrop_binder (n : Nat) (inner : Ty) (hwf : tyWellFormed inner = true) :
    tyWellFormed (.unsafeBinder n (.manuallyDrop inner)) = true := by
  simp [tyWellFormed, bikeshedGuaranteedNoDrop, hwf]

theorem wf_rejects_nested_unsafeBinder (n1 n2 : Nat) (inner : Ty) :
    tyWellFormed (.unsafeBinder n1 (.unsafeBinder n2 inner)) = false := by
  simp [tyWellFormed, bikeshedGuaranteedNoDrop, tyIsCopy]

/-- Physical ABI layout descriptor matching `rustc_ty_utils/src/layout.rs:874-877`. -/
structure Layout where
  sizeBytes : Nat
  alignBytes : Nat
  isZst : Bool

noncomputable def maxNat (a b : Nat) : Nat :=
  if natBlt a b then b else a

noncomputable def alignUp (sz al : Nat) : Nat :=
  if natBeq al 0 then sz
  else ((sz + (al - 1)) / al) * al

/- Structural layout computation; invariance under `eraseBoundRegions` is proved below. -/
mutual
  noncomputable def tyLayout : Ty → Layout
    | .bool => { sizeBytes := 1, alignBytes := 1, isZst := false }
    | .u32 => { sizeBytes := 4, alignBytes := 4, isZst := false }
    | .u64 => { sizeBytes := 8, alignBytes := 8, isZst := false }
    | .unit => { sizeBytes := 0, alignBytes := 1, isZst := true }
    | .never => { sizeBytes := 0, alignBytes := 1, isZst := true }
    | .ref _ _ _ => { sizeBytes := 8, alignBytes := 8, isZst := false }
    | .rawPtr _ _ => { sizeBytes := 8, alignBytes := 8, isZst := false }
    | .manuallyDrop inner => tyLayout inner
    | .tuple fs => tyListLayout fs
    | .unsafeBinder _ inner => tyLayout inner

  noncomputable def tyListLayout : List Ty → Layout
    | [] => { sizeBytes := 0, alignBytes := 1, isZst := true }
    | t :: ts =>
        let l1 := tyLayout t
        let l2 := tyListLayout ts
        let al := maxNat l1.alignBytes l2.alignBytes
        { sizeBytes := alignUp (alignUp l1.sizeBytes l2.alignBytes + l2.sizeBytes) al
          alignBytes := al
          isZst := l1.isZst && l2.isZst }
end

theorem tyLayout_eraseBoundRegions :
    ∀ (t : Ty) (k : Nat), tyLayout (eraseBoundRegions k t) = tyLayout t := by
  intro t
  refine Ty.rec
    (motive_1 := fun t => ∀ k, tyLayout (eraseBoundRegions k t) = tyLayout t)
    (motive_2 := fun ts => ∀ k, tyListLayout (eraseBoundRegionsList k ts) = tyListLayout ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · intro _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro m r inner _ _; rfl
  · intro m inner ih k; simp only [eraseBoundRegions, tyLayout]
  · intro inner ih k; simp only [eraseBoundRegions, tyLayout, ih k]
  · intro fs ih k; simp only [eraseBoundRegions, tyLayout, ih k]
  · intro n inner ih k; simp only [eraseBoundRegions, tyLayout, ih (k + 1)]
  · intro _; rfl
  · intro hd tl ihd iht k
    simp only [eraseBoundRegionsList, tyListLayout, ihd k, iht k]

theorem tyLayout_unsafeBinder (n : Nat) (inner : Ty) :
    tyLayout (.unsafeBinder n inner) = tyLayout (instantiateBinder inner) := by
  simp only [tyLayout, instantiateBinder]
  exact (tyLayout_eraseBoundRegions inner 0).symm

/-! ## Part II: Runtime Values, Borrow Tracker, and Miri Validity Fix (`validity.rs:987`) -/

inductive Perm where
  | unique
  | sharedRO
  | sharedRW
  | disabled

structure TagEntry where
  tag : Nat
  perm : Perm

inductive AccessKind where
  | read
  | write

structure AllocBlock where
  size : Nat
  align : Nat
  active : Bool
  cells : List Nat
  nextTag : Nat
  stack : List TagEntry

structure Mem where
  allocs : List AllocBlock

inductive Val where
  | uninit
  | boolVal (b : Nat)
  | u32Val (n : Nat)
  | u64Val (n : Nat)
  | unitVal
  | ptrVal (alloc : Nat) (off : Nat) (tag : Nat)
  | tupleVal (fields : List Val)
  | manuallyDropVal (inner : Val)

inductive ValidityMode where
  | no
  | shallow
  | deep

inductive BorrowTrackerMode where
  | enabled
  | disabled

/-- `src/tools/miri/src/bin/miri.rs:689-692`:
    `if miri_config.validation == ValidationMode::No { miri_config.borrow_tracker = None; }`. -/
noncomputable def effectiveBorrowTracker (vm : ValidityMode) (bt : BorrowTrackerMode) :
    BorrowTrackerMode :=
  match vm with
  | .no => .disabled
  | _ => bt

theorem disable_validation_kills_borrow_tracker (bt : BorrowTrackerMode) :
    effectiveBorrowTracker .no bt = .disabled :=
  rfl

inductive InterpErr where
  | fixmeUnsafeBinder
  | uninitRead
  | invalidBool
  | uninhabitedNever
  | nullOrDanglingPtr
  | misalignedPtr
  | outOfBounds
  | useAfterFree
  | aliasingUB
  | typeMismatch
  | badPlace
  | movedValueRead

inductive InterpRes (α : Type) where
  | ok (val : α)
  | err (e : InterpErr)

/-- Pop stack entries above `targetTag` on conflicting access (`stacked_borrows/mod.rs`). -/
noncomputable def stackFindAndPop (targetTag : Nat) (ak : AccessKind) :
    List TagEntry → Option (List TagEntry)
  | [] => none
  | top :: rest =>
      match natBeq top.tag targetTag with
      | true =>
          match ak, top.perm with
          | .read, .disabled => none
          | .write, .unique => some (top :: rest)
          | .write, .sharedRW => some (top :: rest)
          | .write, .sharedRO => none
          | .write, .disabled => none
          | .read, _ => some (top :: rest)
      | false =>
          match ak with
          | .write => stackFindAndPop targetTag ak rest
          | .read =>
              match top.perm with
              | .unique => stackFindAndPop targetTag ak rest
              | _ =>
                  match stackFindAndPop targetTag ak rest with
                  | none => none
                  | some kept => some (top :: kept)

/-- Perform a reborrow / retag on `alloc`, deriving a fresh `newTag` above `parentTag`. -/
noncomputable def retagAlloc (mem : Mem) (allocId parentTag : Nat) (newPerm : Perm) :
    InterpRes (Nat × Mem) :=
  match listGet? mem.allocs allocId with
  | none => .err .nullOrDanglingPtr
  | some blk =>
      match blk.active with
      | false => .err .useAfterFree
      | true =>
          let ak := match newPerm with | .unique => AccessKind.write | _ => AccessKind.read
          match stackFindAndPop parentTag ak blk.stack with
          | none => .err .aliasingUB
          | some truncated =>
              let fresh := blk.nextTag
              let blk' : AllocBlock :=
                { blk with
                  nextTag := fresh + 1
                  stack := { tag := fresh, perm := newPerm } :: truncated }
              .ok (fresh, { allocs := listSet mem.allocs allocId blk' })

/-- Perform memory write through `(allocId, tag)` updating the stack when borrow tracking is on. -/
noncomputable def writeMemCell (mem : Mem) (vm : ValidityMode) (bt : BorrowTrackerMode)
    (allocId off tag val : Nat) : InterpRes Mem :=
  match listGet? mem.allocs allocId with
  | none => .err .nullOrDanglingPtr
  | some blk =>
      match blk.active with
      | false => .err .useAfterFree
      | true =>
          match natBlt blk.size (off + 1) with
          | true => .err .outOfBounds
          | false =>
              match effectiveBorrowTracker vm bt with
              | .disabled =>
                  let blk' := { blk with cells := listSet blk.cells off val }
                  .ok { allocs := listSet mem.allocs allocId blk' }
              | .enabled =>
                  match stackFindAndPop tag .write blk.stack with
                  | none => .err .aliasingUB
                  | some truncated =>
                      let blk' := { blk with cells := listSet blk.cells off val, stack := truncated }
                      .ok { allocs := listSet mem.allocs allocId blk' }

/-- Read memory cell through `(allocId, tag)` under `effectiveBorrowTracker vm bt`. -/
noncomputable def readMemCell (mem : Mem) (vm : ValidityMode) (bt : BorrowTrackerMode)
    (allocId off tag : Nat) : InterpRes Nat :=
  match listGet? mem.allocs allocId with
  | none => .err .nullOrDanglingPtr
  | some blk =>
      match blk.active with
      | false => .err .useAfterFree
      | true =>
          match natBlt blk.size (off + 1) with
          | true => .err .outOfBounds
          | false =>
              match listGet? blk.cells off with
              | none => .err .outOfBounds
              | some val =>
                  match effectiveBorrowTracker vm bt with
                  | .disabled => .ok val
                  | .enabled =>
                      match stackFindAndPop tag .read blk.stack with
                      | none => .err .aliasingUB
                      | some _ => .ok val

/-- Check basic pointer validity (`validity.rs:561-722`) plus optional retag (`624`). -/
noncomputable def checkSafePtr (mem : Mem) (vm : ValidityMode) (bt : BorrowTrackerMode)
    (mutbl retag : Bool) (alloc off tag : Nat) (pointeeTy : Ty) : InterpRes (Nat × Mem) :=
  let layout := tyLayout pointeeTy
  match listGet? mem.allocs alloc with
  | none => .err .nullOrDanglingPtr
  | some blk =>
      match blk.active with
      | false => .err .useAfterFree
      | true =>
          match natBlt blk.size (off + layout.sizeBytes) with
          | true => .err .outOfBounds
          | false =>
              match natBeq (off % layout.alignBytes) 0 with
              | false => .err .misalignedPtr
              | true =>
                  match retag with
                  | false => .ok (tag, mem)
                  | true =>
                      match effectiveBorrowTracker vm bt with
                      | .disabled => .ok (tag, mem)
                      | .enabled =>
                          let p := if mutbl then Perm.unique else Perm.sharedRO
                          retagAlloc mem alloc tag p

theorem retagAlloc_ne_fixme (mem : Mem) (allocId parentTag : Nat) (newPerm : Perm) :
    retagAlloc mem allocId parentTag newPerm ≠ .err .fixmeUnsafeBinder := by
  unfold retagAlloc
  cases listGet? mem.allocs allocId with
  | none => intro h; cases h
  | some blk =>
      rcases blk with ⟨sz, al, active, cells, nextTag, stack⟩
      cases active with
      | false => intro h; cases h
      | true =>
          dsimp only
          cases stackFindAndPop parentTag (match newPerm with | .unique => .write | _ => .read) stack with
          | none => intro h; dsimp only at h; cases h
          | some _ => intro h; dsimp only at h; cases h

theorem checkSafePtr_ne_fixme (mem : Mem) (vm : ValidityMode) (bt : BorrowTrackerMode)
    (mutbl retag : Bool) (alloc off tag : Nat) (pointeeTy : Ty) :
    checkSafePtr mem vm bt mutbl retag alloc off tag pointeeTy ≠ .err .fixmeUnsafeBinder := by
  unfold checkSafePtr
  cases listGet? mem.allocs alloc with
  | none => intro h; cases h
  | some blk =>
      rcases blk with ⟨sz, al, active, cells, nextTag, stack⟩
      cases active with
      | false => intro h; cases h
      | true =>
          dsimp only
          cases natBlt sz (off + (tyLayout pointeeTy).sizeBytes) with
          | true => intro h; dsimp only at h; cases h
          | false =>
              dsimp only
              cases natBeq (off % (tyLayout pointeeTy).alignBytes) 0 with
              | false => intro h; dsimp only at h; cases h
              | true =>
                  dsimp only
                  cases retag with
                  | false => intro h; cases h
                  | true =>
                      cases effectiveBorrowTracker vm bt with
                      | disabled => intro h; cases h
                      | enabled =>
                          dsimp only
                          exact retagAlloc_ne_fixme mem alloc tag
                            (if mutbl then Perm.unique else Perm.sharedRO)

/-- Pure helper applying a single-element validator across tuple fields without `mutual`. -/
noncomputable def validateListWith
    (step : Mem → Ty → Val → InterpRes (Val × Mem))
    (mem : Mem) : List Ty → List Val → InterpRes (List Val × Mem)
  | [], [] => .ok ([], mem)
  | t :: ts, v :: vs =>
      match step mem t v with
      | .err e => .err e
      | .ok (v', mem') =>
          match validateListWith step mem' ts vs with
          | .err e => .err e
          | .ok (vs', mem'') => .ok (v' :: vs', mem'')
  | _, _ => .err .typeMismatch

theorem validateListWith_ne_fixme
    (step : Mem → Ty → Val → InterpRes (Val × Mem))
    (hstep : ∀ mem t v, step mem t v ≠ .err .fixmeUnsafeBinder) :
    ∀ (ts : List Ty) (vs : List Val) (mem : Mem),
      validateListWith step mem ts vs ≠ .err .fixmeUnsafeBinder := by
  intro ts
  induction ts with
  | nil =>
      intro vs mem
      cases vs <;> intro h <;> cases h
  | cons t ts' ih =>
      intro vs mem
      cases vs with
      | nil => intro h; cases h
      | cons v vs' =>
          simp only [validateListWith]
          cases hs : step mem t v with
          | err e =>
              intro h
              dsimp only at h
              cases h
              exact hstep mem t v hs
          | ok p =>
              rcases p with ⟨v', mem'⟩
              dsimp only
              cases hl : validateListWith step mem' ts' vs' with
              | err e =>
                  intro h
                  dsimp only at h
                  cases h
                  exact ih vs' mem' hl
              | ok _ => intro h; dsimp only at h; cases h

/-- Stock Miri validity (`validity.rs:987` / `994`) vs Fixed recursive delegation.
    When `handleBinder = false`, models upstream `unimplemented!("FIXME(unsafe_binder)")`.
    When `handleBinder = true`, delegates `unsafeBinder` to `instantiateBinder inner`. -/
noncomputable def validateValCore (handleBinder : Bool) (vm : ValidityMode)
    (bt : BorrowTrackerMode) (retag : Bool) :
    Nat → Mem → Ty → Val → InterpRes (Val × Mem)
  | 0, mem, _, v => .ok (v, mem)
  | fuel' + 1, mem, ty, v =>
      match vm with
      | .no => .ok (v, mem)
      | _ =>
          match ty, v with
          | .bool, .boolVal b =>
              match natBlt b 2 with
              | true => .ok (.boolVal b, mem)
              | false => .err .invalidBool
          | .bool, .uninit => .err .uninitRead
          | .bool, _ => .err .typeMismatch
          | .u32, .u32Val n => .ok (.u32Val n, mem)
          | .u32, .uninit => .err .uninitRead
          | .u32, _ => .err .typeMismatch
          | .u64, .u64Val n => .ok (.u64Val n, mem)
          | .u64, .uninit => .err .uninitRead
          | .u64, _ => .err .typeMismatch
          | .unit, .unitVal => .ok (.unitVal, mem)
          | .unit, _ => .err .typeMismatch
          | .never, _ => .err .uninhabitedNever
          | .rawPtr _ _, .ptrVal a o t => .ok (.ptrVal a o t, mem)
          | .rawPtr _ _, _ => .err .typeMismatch
          | .ref m _ inner, .ptrVal a o t =>
              match checkSafePtr mem vm bt m retag a o t inner with
              | .err e => .err e
              | .ok (t', mem') =>
                  match vm with
                  | .deep =>
                      match listGet? mem'.allocs a with
                      | none => .err .nullOrDanglingPtr
                      | some blk =>
                          match listGet? blk.cells o with
                          | none => .err .outOfBounds
                          | some cval =>
                              match validateValCore handleBinder vm bt false fuel' mem' inner (.u32Val cval) with
                              | .err e => .err e
                              | .ok (_, mem'') => .ok (.ptrVal a o t', mem'')
                  | _ => .ok (.ptrVal a o t', mem')
          | .ref _ _ _, _ => .err .typeMismatch
          | .manuallyDrop inner, .manuallyDropVal iv =>
              match validateValCore handleBinder vm bt false fuel' mem inner iv with
              | .err e => .err e
              | .ok (iv', mem') => .ok (.manuallyDropVal iv', mem')
          | .manuallyDrop _, _ => .err .typeMismatch
          | .tuple fs, .tupleVal vs =>
              match validateListWith (validateValCore handleBinder vm bt retag fuel') mem fs vs with
              | .err e => .err e
              | .ok (vs', mem') => .ok (.tupleVal vs', mem')
          | .tuple _, _ => .err .typeMismatch
          | .unsafeBinder _ inner, val =>
              match handleBinder with
              | true => validateValCore true vm bt retag fuel' mem (instantiateBinder inner) val
              | false => .err .fixmeUnsafeBinder

theorem stockMiri_panics_on_unsafeBinder (vm : ValidityMode) (hvm : vm ≠ .no)
    (bt : BorrowTrackerMode) (retag : Bool) (fuel : Nat) (mem : Mem)
    (n : Nat) (inner : Ty) (v : Val) :
    validateValCore false vm bt retag (fuel + 1) mem (.unsafeBinder n inner) v =
      .err .fixmeUnsafeBinder := by
  cases vm with
  | no => exact False.elim (hvm rfl)
  | shallow => rfl
  | deep => rfl

theorem fixedValidity_unsafeBinder_delegates (vm : ValidityMode) (hvm : vm ≠ .no)
    (bt : BorrowTrackerMode) (retag : Bool) (fuel : Nat) (mem : Mem)
    (n : Nat) (inner : Ty) (v : Val) :
    validateValCore true vm bt retag (fuel + 1) mem (.unsafeBinder n inner) v =
      validateValCore true vm bt retag fuel mem (instantiateBinder inner) v := by
  cases vm with
  | no => exact False.elim (hvm rfl)
  | shallow => rfl
  | deep => rfl

theorem fixedValidity_never_fixme :
    ∀ (fuel : Nat) (vm : ValidityMode) (bt : BorrowTrackerMode)
      (retag : Bool) (mem : Mem) (t : Ty) (v : Val),
      validateValCore true vm bt retag fuel mem t v ≠ .err .fixmeUnsafeBinder := by
  intro fuel
  induction fuel with
  | zero =>
      intro vm bt retag mem t v
      intro h; cases h
  | succ fuel' ih =>
      intro vm bt retag mem t v
      cases vm with
      | no => intro h; cases h
      | shallow =>
          cases t with
          | bool =>
              cases v <;> simp only [validateValCore]
              · intro h; cases h
              · rename_i b; cases natBlt b 2 <;> intro h <;> cases h
              all_goals (intro h; cases h)
          | u32 => cases v <;> intro h <;> cases h
          | u64 => cases v <;> intro h <;> cases h
          | unit => cases v <;> intro h <;> cases h
          | never => intro h; cases h
          | rawPtr _ _ => cases v <;> intro h <;> cases h
          | ref m _ inner =>
              cases v with
              | ptrVal a o tag =>
                  simp only [validateValCore]
                  cases hsp : checkSafePtr mem .shallow bt m retag a o tag inner with
                  | err e =>
                      intro h
                      dsimp only at h
                      cases h
                      exact checkSafePtr_ne_fixme mem .shallow bt m retag a o tag inner hsp
                  | ok p => intro h; dsimp only at h; cases h
              | _ => intro h; cases h
          | manuallyDrop inner =>
              cases v with
              | manuallyDropVal iv =>
                  simp only [validateValCore]
                  cases hv : validateValCore true .shallow bt false fuel' mem inner iv with
                  | err e =>
                      intro h
                      dsimp only at h
                      cases h
                      exact ih .shallow bt false mem inner iv hv
                  | ok p => intro h; dsimp only at h; cases h
              | _ => intro h; cases h
          | tuple fs =>
              cases v with
              | tupleVal vs =>
                  simp only [validateValCore]
                  cases hl : validateListWith (validateValCore true .shallow bt retag fuel') mem fs vs with
                  | err e =>
                      intro h
                      dsimp only at h
                      cases h
                      exact validateListWith_ne_fixme
                        (validateValCore true .shallow bt retag fuel')
                        (fun m t' v' => ih .shallow bt retag m t' v')
                        fs vs mem hl
                  | ok p => intro h; dsimp only at h; cases h
              | _ => intro h; cases h
          | unsafeBinder _ inner =>
              simp only [validateValCore]
              exact ih .shallow bt retag mem (instantiateBinder inner) v
      | deep =>
          cases t with
          | bool =>
              cases v <;> simp only [validateValCore]
              · intro h; cases h
              · rename_i b; cases natBlt b 2 <;> intro h <;> cases h
              all_goals (intro h; cases h)
          | u32 => cases v <;> intro h <;> cases h
          | u64 => cases v <;> intro h <;> cases h
          | unit => cases v <;> intro h <;> cases h
          | never => intro h; cases h
          | rawPtr _ _ => cases v <;> intro h <;> cases h
          | ref m _ inner =>
              cases v with
              | ptrVal a o tag =>
                  simp only [validateValCore]
                  cases hsp : checkSafePtr mem .deep bt m retag a o tag inner with
                  | err e =>
                      intro h
                      dsimp only at h
                      cases h
                      exact checkSafePtr_ne_fixme mem .deep bt m retag a o tag inner hsp
                  | ok p =>
                      rcases p with ⟨t', mem'⟩
                      dsimp only
                      cases listGet? mem'.allocs a with
                      | none => intro h; dsimp only at h; cases h
                      | some blk =>
                          dsimp only
                          cases listGet? blk.cells o with
                          | none => intro h; dsimp only at h; cases h
                          | some cval =>
                              dsimp only
                              cases hv : validateValCore true .deep bt false fuel' mem' inner (.u32Val cval) with
                              | err e =>
                                  intro h
                                  dsimp only at h
                                  cases h
                                  exact ih .deep bt false mem' inner (.u32Val cval) hv
                              | ok _ => intro h; dsimp only at h; cases h
              | _ => intro h; cases h
          | manuallyDrop inner =>
              cases v with
              | manuallyDropVal iv =>
                  simp only [validateValCore]
                  cases hv : validateValCore true .deep bt false fuel' mem inner iv with
                  | err e =>
                      intro h
                      dsimp only at h
                      cases h
                      exact ih .deep bt false mem inner iv hv
                  | ok p => intro h; dsimp only at h; cases h
              | _ => intro h; cases h
          | tuple fs =>
              cases v with
              | tupleVal vs =>
                  simp only [validateValCore]
                  cases hl : validateListWith (validateValCore true .deep bt retag fuel') mem fs vs with
                  | err e =>
                      intro h
                      dsimp only at h
                      cases h
                      exact validateListWith_ne_fixme
                        (validateValCore true .deep bt retag fuel')
                        (fun m t' v' => ih .deep bt retag m t' v')
                        fs vs mem hl
                  | ok p => intro h; dsimp only at h; cases h
              | _ => intro h; cases h
          | unsafeBinder _ inner =>
              simp only [validateValCore]
              exact ih .deep bt retag mem (instantiateBinder inner) v

theorem fixedValidity_catches_invalid_bool_in_binder (mem : Mem) (bt : BorrowTrackerMode) :
    validateValCore true .shallow bt false 4 mem (.unsafeBinder 0 .bool) (.boolVal 2) =
      .err .invalidBool :=
  rfl

theorem disable_validation_misses_invalid_bool (mem : Mem) (bt : BorrowTrackerMode) :
    validateValCore true .no bt false 4 mem (.unsafeBinder 0 .bool) (.boolVal 2) =
      .ok (.boolVal 2, mem) :=
  rfl

theorem fixedValidity_catches_dangling_ref_in_binder (bt : BorrowTrackerMode) :
    validateValCore true .shallow bt false 4 { allocs := [] }
      (.unsafeBinder 1 (.ref false (.bound 0 0) .u32)) (.ptrVal 0 0 0) =
      .err .nullOrDanglingPtr :=
  rfl

/-- Model of `dup_mut_via_ptr_read`: two `&mut u32` references `r1` and `r2` unwrapped from
    copies (`ptr::read`) of `unsafe<'a> &'a mut u32`, retagged with `WithRetag::Yes`, followed by
    `*r1 = 10; *r2 = 20; *r1`. -/
noncomputable def runDupMutScenario (vm : ValidityMode) (bt : BorrowTrackerMode) :
    InterpRes (Nat × Nat) :=
  let initMem : Mem :=
    { allocs := [{ size := 4, align := 4, active := true, cells := [0], nextTag := 1,
                   stack := [{ tag := 0, perm := .unique }] }] }
  let binderTy : Ty := .unsafeBinder 1 (.ref true (.bound 0 0) .u32)
  let initPtr : Val := .ptrVal 0 0 0
  match validateValCore true vm bt true 4 initMem binderTy initPtr with
  | .err e => .err e
  | .ok (r1Val, mem1) =>
      match validateValCore true vm bt true 4 mem1 binderTy initPtr with
      | .err e => .err e
      | .ok (r2Val, mem2) =>
          match r1Val, r2Val with
          | .ptrVal a1 o1 t1, .ptrVal a2 o2 t2 =>
              match writeMemCell mem2 vm bt a1 o1 t1 10 with
              | .err e => .err e
              | .ok mem3 =>
                  match writeMemCell mem3 vm bt a2 o2 t2 20 with
                  | .err e => .err e
                  | .ok mem4 =>
                      match readMemCell mem4 vm bt a1 o1 t1 with
                      | .err e => .err e
                      | .ok v1 =>
                          match readMemCell mem4 vm bt a2 o2 t2 with
                          | .err e => .err e
                          | .ok v2 => .ok (v1, v2)
          | _, _ => .err .typeMismatch

theorem fixedValidity_catches_dup_mut_aliasing :
    runDupMutScenario .shallow .enabled = .err .aliasingUB :=
  rfl

theorem disable_validation_hides_dup_mut_aliasing (bt : BorrowTrackerMode) :
    runDupMutScenario .no bt = .ok (20, 20) := by
  cases bt <;> rfl

/-! ## Part III: MIR Semantics (`deinitMovedPlace`), Algebraic Cancellation, GVN Opacity, & SROA -/

inductive ProjElem where
  | deref
  | field (idx : Nat)
  | unwrapUnsafeBinder (ty : Ty)

structure Place where
  localId : Nat
  projs : List ProjElem

inductive Operand where
  | copy (p : Place)
  | move (p : Place)
  | constVal (v : Val)

inductive Rvalue where
  | use (op : Operand) (retag : Bool)
  | aggregateTuple (ops : List Operand)
  | wrapUnsafeBinder (op : Operand) (ty : Ty)
  | addU32 (lhs rhs : Operand)

inductive Stmt where
  | storageLive (localId : Nat)
  | storageDead (localId : Nat)
  | assign (dst : Place) (rv : Rvalue)
  | nop

inductive LocalSlot where
  | dead
  | liveUninit
  | liveInit (v : Val)

structure MirState where
  locals : List LocalSlot
  mem : Mem
  vm : ValidityMode
  bt : BorrowTrackerMode
  deinitMovedPlace : Bool

noncomputable def readValProj (mem : Mem) (vm : ValidityMode) (bt : BorrowTrackerMode) :
    Val → List ProjElem → InterpRes Val
  | v, [] => .ok v
  | v, .unwrapUnsafeBinder _ :: rest => readValProj mem vm bt v rest
  | .tupleVal fs, .field idx :: rest =>
      match listGet? fs idx with
      | none => .err .badPlace
      | some f => readValProj mem vm bt f rest
  | .ptrVal a o t, .deref :: rest =>
      match readMemCell mem vm bt a o t with
      | .err e => .err e
      | .ok n => readValProj mem vm bt (.u32Val n) rest
  | _, _ :: _ => .err .badPlace

noncomputable def updateTupleField (idx : Nat) (newVal : Val) : List Val → Option (List Val)
  | [] => none
  | v :: vs =>
      match idx with
      | 0 => some (newVal :: vs)
      | idx' + 1 =>
          match updateTupleField idx' newVal vs with
          | none => none
          | some vs' => some (v :: vs')

noncomputable def writeValProj : Val → List ProjElem → Val → Option Val
  | _, [], newVal => some newVal
  | base, .unwrapUnsafeBinder _ :: rest, newVal => writeValProj base rest newVal
  | .tupleVal fs, .field idx :: rest, newVal =>
      match listGet? fs idx with
      | none => none
      | some oldF =>
          match writeValProj oldF rest newVal with
          | none => none
          | some newF =>
              match updateTupleField idx newF fs with
              | none => none
              | some fs' => some (.tupleVal fs')
  | _, _, _ => none

noncomputable def evalOperand (st : MirState) : Operand → InterpRes (Val × MirState)
  | .constVal v => .ok (v, st)
  | .copy p =>
      match listGet? st.locals p.localId with
      | some (.liveInit baseVal) =>
          match readValProj st.mem st.vm st.bt baseVal p.projs with
          | .err e => .err e
          | .ok res => .ok (res, st)
      | some .liveUninit => .err .movedValueRead
      | _ => .err .badPlace
  | .move p =>
      match listGet? st.locals p.localId with
      | some (.liveInit baseVal) =>
          match readValProj st.mem st.vm st.bt baseVal p.projs with
          | .err e => .err e
          | .ok res =>
              let locals' :=
                match st.deinitMovedPlace with
                | false => st.locals
                | true =>
                    match p.projs with
                    | [] => listSet st.locals p.localId .liveUninit
                    | _ :: _ => st.locals
              .ok (res, { st with locals := locals' })
      | some .liveUninit => .err .movedValueRead
      | _ => .err .badPlace

noncomputable def evalOperandList (st : MirState) : List Operand → InterpRes (List Val × MirState)
  | [] => .ok ([], st)
  | op :: ops =>
      match evalOperand st op with
      | .err e => .err e
      | .ok (v, st1) =>
          match evalOperandList st1 ops with
          | .err e => .err e
          | .ok (vs, st2) => .ok (v :: vs, st2)

noncomputable def evalRvalue (st : MirState) : Rvalue → InterpRes (Val × MirState)
  | .use op _ => evalOperand st op
  | .wrapUnsafeBinder op _ => evalOperand st op
  | .aggregateTuple ops =>
      match evalOperandList st ops with
      | .err e => .err e
      | .ok (vs, st') => .ok (.tupleVal vs, st')
  | .addU32 lhs rhs =>
      match evalOperand st lhs with
      | .err e => .err e
      | .ok (v1, st1) =>
          match evalOperand st1 rhs with
          | .err e => .err e
          | .ok (v2, st2) =>
              match v1, v2 with
              | .u32Val a, .u32Val b => .ok (.u32Val ((a + b) % 4294967296), st2)
              | _, _ => .err .typeMismatch

noncomputable def writePlace (st : MirState) (dst : Place) (val : Val) : InterpRes MirState :=
  match dst.projs with
  | [] =>
      match listGet? st.locals dst.localId with
      | some .liveUninit | some (.liveInit _) =>
          .ok { st with locals := listSet st.locals dst.localId (.liveInit val) }
      | _ => .err .badPlace
  | _ :: _ =>
      match listGet? st.locals dst.localId with
      | some (.liveInit baseVal) =>
          match writeValProj baseVal dst.projs val with
          | none => .err .badPlace
          | some baseVal' =>
              .ok { st with locals := listSet st.locals dst.localId (.liveInit baseVal') }
      | _ => .err .badPlace

noncomputable def execStmt (st : MirState) : Stmt → InterpRes MirState
  | .nop => .ok st
  | .storageLive l =>
      match listGet? st.locals l with
      | none => .err .badPlace
      | some _ => .ok { st with locals := listSet st.locals l .liveUninit }
  | .storageDead l =>
      match listGet? st.locals l with
      | none => .err .badPlace
      | some _ => .ok { st with locals := listSet st.locals l .dead }
  | .assign dst rv =>
      match evalRvalue st rv with
      | .err e => .err e
      | .ok (v, st1) => writePlace st1 dst v

noncomputable def execBlock (st : MirState) : List Stmt → InterpRes MirState
  | [] => .ok st
  | s :: ss =>
      match execStmt st s with
      | .err e => .err e
      | .ok st' => execBlock st' ss

noncomputable def operandDisjointFrom (op : Operand) (forbidden : Nat) : Prop :=
  match op with
  | .constVal _ => True
  | .copy p => p.localId ≠ forbidden
  | .move p => p.localId ≠ forbidden

noncomputable def localsAgreeExcept (wbIdx : Nat) (l1 l2 : List LocalSlot) : Prop :=
  ∀ i, i ≠ wbIdx → listGet? l1 i = listGet? l2 i

noncomputable def stateAgreeExcept (wbIdx : Nat) (s1 s2 : MirState) : Prop :=
  localsAgreeExcept wbIdx s1.locals s2.locals ∧
  s1.mem = s2.mem ∧ s1.vm = s2.vm ∧ s1.bt = s2.bt ∧
  s1.deinitMovedPlace = s2.deinitMovedPlace

/-- **Theorem (Algebraic Cancellation Soundness)**:
    Wrapping an operand `op` into an unsafe binder temporary `wbIdx` and immediately
    unwrapping `wbIdx` (`UnwrapUnsafeBinder`) before deallocating `wbIdx` produces the
    exact same observable post-state (modulo the dead slot `wbIdx`) as directly evaluating
    `op`—both when `deinitMovedPlace = true` and when `deinitMovedPlace = false`. -/
theorem unwrap_wrap_cancel_sound
    (st : MirState) (wbIdx dstIdx : Nat) (wbSlot dstSlot : LocalSlot)
    (wbTy unwrappedTy : Ty) (op : Operand) (useMove retag : Bool)
    (hwb : listGet? st.locals wbIdx = some wbSlot)
    (hdst : listGet? st.locals dstIdx = some dstSlot)
    (hdstLive : dstSlot = .liveUninit ∨ ∃ v, dstSlot = .liveInit v)
    (hneWbDst : dstIdx ≠ wbIdx)
    (hdisj : operandDisjointFrom op wbIdx) :
    let srcBlock : List Stmt :=
      [ .storageLive wbIdx,
        .assign { localId := wbIdx, projs := [] } (.wrapUnsafeBinder op wbTy),
        .assign { localId := dstIdx, projs := [] }
          (.use (if useMove then
                   .move { localId := wbIdx, projs := [.unwrapUnsafeBinder unwrappedTy] }
                 else
                   .copy { localId := wbIdx, projs := [.unwrapUnsafeBinder unwrappedTy] }) retag),
        .storageDead wbIdx ]
    let optBlock : List Stmt :=
      [ .assign { localId := dstIdx, projs := [] } (.use op retag) ]
    (∀ e, execBlock st srcBlock = .err e ↔ execBlock st optBlock = .err e) ∧
    (∀ s1 s2, execBlock st srcBlock = .ok s1 → execBlock st optBlock = .ok s2 →
      stateAgreeExcept wbIdx s1 s2) := by
  dsimp only
  have hop : ∀ s0 : MirState,
      evalOperand { s0 with locals := listSet s0.locals wbIdx .liveUninit } op =
        match evalOperand s0 op with
        | .err e => .err e
        | .ok (v, s') => .ok (v, { s' with locals := listSet s'.locals wbIdx .liveUninit }) := by
    intro s0
    cases op with
    | constVal c => rfl
    | copy q =>
        have hqne : wbIdx ≠ q.localId := fun heq => hdisj heq.symm
        simp only [evalOperand]
        rw [listGet?_listSet_ne s0.locals wbIdx q.localId .liveUninit hqne]
        cases hq : listGet? s0.locals q.localId with
        | none => rfl
        | some sl =>
            cases sl with
            | dead => rfl
            | liveUninit => rfl
            | liveInit bv =>
                dsimp only
                cases hr : readValProj s0.mem s0.vm s0.bt bv q.projs <;> dsimp only
    | move q =>
        have hqne : wbIdx ≠ q.localId := fun heq => hdisj heq.symm
        simp only [evalOperand]
        rw [listGet?_listSet_ne s0.locals wbIdx q.localId .liveUninit hqne]
        cases hq : listGet? s0.locals q.localId with
        | none => rfl
        | some sl =>
            cases sl with
            | dead => rfl
            | liveUninit => rfl
            | liveInit bv =>
                dsimp only
                cases hr : readValProj s0.mem s0.vm s0.bt bv q.projs with
                | err er => dsimp only
                | ok rv =>
                    cases s0.deinitMovedPlace with
                    | false => dsimp only
                    | true =>
                        cases q.projs with
                        | cons _ _ => rfl
                        | nil =>
                            simp only []
                            have hcomm : ∀ (ls : List LocalSlot) (i j : Nat) (a b : LocalSlot),
                                i ≠ j → listSet (listSet ls i a) j b = listSet (listSet ls j b) i a := by
                              intro ls
                              induction ls with
                              | nil => intro i j a b _; cases i <;> cases j <;> rfl
                              | cons x xs ih =>
                                  intro i j a b hij
                                  cases i with
                                  | zero =>
                                      cases j with
                                      | zero => exact False.elim (hij rfl)
                                      | succ j' => rfl
                                  | succ i' =>
                                      cases j with
                                      | zero => rfl
                                      | succ j' =>
                                          simp only [listSet]
                                          rw [ih i' j' a b (fun heq => hij (congrArg Nat.succ heq))]
                            rw [hcomm s0.locals wbIdx q.localId .liveUninit .liveUninit hqne]
  simp only [execBlock, execStmt, evalRvalue, hwb]
  rw [hop st]
  cases hev : evalOperand st op with
  | err e =>
      dsimp only
      constructor
      · intro e'; rfl
      · intro s1 s2 h1 h2; cases h1
  | ok p =>
      rcases p with ⟨v, st1⟩
      have hwbSt1 : listGet? st1.locals wbIdx = some wbSlot := by
        cases op with
        | constVal _ => simp [evalOperand] at hev; rw [← hev.2]; exact hwb
        | copy _ =>
            simp only [evalOperand] at hev
            cases hq : listGet? st.locals _ <;> rw [hq] at hev
            · dsimp only at hev; cases hev
            · rename_i sl; cases sl <;> dsimp only at hev
              · cases hev
              · cases hev
              · cases hr : readValProj _ _ _ _ _ with
                | err _ => rw [hr] at hev; dsimp only at hev; cases hev
                | ok _ =>
                    rw [hr] at hev; dsimp only at hev
                    injection hev with hp
                    injection hp with _ hst1
                    rw [← hst1]; exact hwb
        | move q =>
            simp only [evalOperand] at hev
            cases hq : listGet? st.locals q.localId <;> rw [hq] at hev
            · dsimp only at hev; cases hev
            · rename_i sl; cases sl <;> dsimp only at hev
              · cases hev
              · cases hev
              · cases hr : readValProj _ _ _ _ _ with
                | err _ => rw [hr] at hev; dsimp only at hev; cases hev
                | ok _ =>
                    rw [hr] at hev; dsimp only at hev
                    injection hev with hp
                    injection hp with _ hst1
                    rw [← hst1]
                    cases st.deinitMovedPlace <;> cases q.projs <;> dsimp only
                    · exact hwb
                    · exact hwb
                    · rw [listGet?_listSet_ne st.locals q.localId wbIdx .liveUninit hdisj]; exact hwb
                    · exact hwb
      have hwb1 : listGet? (listSet st1.locals wbIdx .liveUninit) wbIdx = some .liveUninit :=
        listGet?_listSet_eq st1.locals wbIdx wbSlot .liveUninit hwbSt1
      have hw1 : writePlace { st1 with locals := listSet st1.locals wbIdx .liveUninit }
          { localId := wbIdx, projs := [] } v =
          .ok { st1 with locals := listSet st1.locals wbIdx (.liveInit v) } := by
        simp only [writePlace, hwb1, listSet_listSet_same]
      have hwb2 : listGet? (listSet st1.locals wbIdx (.liveInit v)) wbIdx = some (.liveInit v) :=
        listGet?_listSet_eq st1.locals wbIdx wbSlot (.liveInit v) hwbSt1
      have hdst1 : listGet? st1.locals dstIdx = some dstSlot ∨
          (dstSlot ≠ .dead ∧ listGet? st1.locals dstIdx = some .liveUninit) := by
        cases op with
        | constVal _ => simp [evalOperand] at hev; rw [← hev.2]; exact Or.inl hdst
        | copy _ =>
            simp only [evalOperand] at hev
            cases hq : listGet? st.locals _ <;> rw [hq] at hev
            · dsimp only at hev; cases hev
            · rename_i sl; cases sl <;> dsimp only at hev
              · cases hev
              · cases hev
              · cases hr : readValProj _ _ _ _ _ with
                | err _ => rw [hr] at hev; dsimp only at hev; cases hev
                | ok _ =>
                    rw [hr] at hev; dsimp only at hev
                    injection hev with hp
                    injection hp with _ hst1
                    rw [← hst1]; exact Or.inl hdst
        | move q =>
            simp only [evalOperand] at hev
            cases hq : listGet? st.locals q.localId <;> rw [hq] at hev
            · dsimp only at hev; cases hev
            · rename_i sl; cases sl <;> dsimp only at hev
              · cases hev
              · cases hev
              · cases hr : readValProj _ _ _ _ _ with
                | err _ => rw [hr] at hev; dsimp only at hev; cases hev
                | ok _ =>
                    rw [hr] at hev; dsimp only at hev
                    injection hev with hp
                    injection hp with _ hst1
                    rw [← hst1]
                    cases st.deinitMovedPlace <;> cases q.projs
                    · exact Or.inl hdst
                    · exact Or.inl hdst
                    · dsimp only
                      cases hqd : natBeq q.localId dstIdx with
                      | true =>
                          have heqd := (natBeq_true_iff q.localId dstIdx).mp hqd
                          rw [heqd]
                          have hnd : dstSlot ≠ LocalSlot.dead := by
                            rcases hdstLive with rfl | ⟨_, rfl⟩ <;> intro hc <;> cases hc
                          exact Or.inr ⟨hnd, listGet?_listSet_eq st.locals dstIdx dstSlot LocalSlot.liveUninit hdst⟩
                      | false =>
                          have hneqd := (natBeq_false_iff q.localId dstIdx).mp hqd
                          rw [listGet?_listSet_ne st.locals q.localId dstIdx .liveUninit hneqd]
                          exact Or.inl hdst
                    · exact Or.inl hdst
      have hdstWrite : ∃ oldDst,
          listGet? st1.locals dstIdx = some oldDst ∧
          (oldDst = .liveUninit ∨ ∃ u, oldDst = .liveInit u) := by
        rcases hdst1 with h1 | ⟨_, h1⟩
        · exact ⟨dstSlot, h1, hdstLive⟩
        · exact ⟨.liveUninit, h1, Or.inl rfl⟩
      rcases hdstWrite with ⟨oldDst, holdDst, holdLive⟩
      have hwDst_opt : writePlace st1 { localId := dstIdx, projs := [] } v =
          .ok { st1 with locals := listSet st1.locals dstIdx (.liveInit v) } := by
        rcases holdLive with rfl | ⟨u, rfl⟩ <;> simp [writePlace, holdDst]
      have hdst2 : listGet? (listSet st1.locals wbIdx (.liveInit v)) dstIdx = some oldDst := by
        rw [listGet?_listSet_ne st1.locals wbIdx dstIdx (.liveInit v) (fun heq => hneWbDst heq.symm)]
        exact holdDst
      have hwDst_src : writePlace { st1 with locals := listSet st1.locals wbIdx (.liveInit v) }
          { localId := dstIdx, projs := [] } v =
          .ok { st1 with locals := listSet (listSet st1.locals wbIdx (.liveInit v)) dstIdx (.liveInit v) } := by
        rcases holdLive with rfl | ⟨u, rfl⟩ <;> simp [writePlace, hdst2]
      have hEvalUnwrap : ∀ (um : Bool),
          evalOperand { st1 with locals := listSet st1.locals wbIdx (LocalSlot.liveInit v) }
            (if um then .move { localId := wbIdx, projs := [.unwrapUnsafeBinder unwrappedTy] }
             else .copy { localId := wbIdx, projs := [.unwrapUnsafeBinder unwrappedTy] }) =
          .ok (v, { st1 with locals := listSet st1.locals wbIdx (LocalSlot.liveInit v) }) := by
        intro um
        cases um with
        | false => simp [evalOperand, hwb2, readValProj]
        | true =>
            simp [evalOperand, hwb2, readValProj]
            cases st1.deinitMovedPlace <;> rfl
      have hDeadSlot : listGet? (listSet (listSet st1.locals wbIdx (LocalSlot.liveInit v)) dstIdx (LocalSlot.liveInit v)) wbIdx =
          some (LocalSlot.liveInit v) := by
        rw [listGet?_listSet_ne _ dstIdx wbIdx (LocalSlot.liveInit v) hneWbDst]
        exact hwb2
      dsimp only
      rw [hw1]
      dsimp only
      rw [hEvalUnwrap useMove]
      dsimp only
      rw [hwDst_src]
      simp only [hDeadSlot]
      rw [hwDst_opt]
      dsimp only
      constructor
      · intro e; constructor <;> (intro hc; cases hc)
      · intro s1 s2 h1 h2
        injection h1 with hs1
        injection h2 with hs2
        rw [← hs1, ← hs2]
        refine ⟨?_, rfl, rfl, rfl, rfl⟩
        intro j hj
        have hj' : wbIdx ≠ j := fun heq => hj heq.symm
        dsimp only
        rw [listGet?_listSet_ne _ wbIdx j LocalSlot.dead hj']
        cases hjd : natBeq dstIdx j with
        | true =>
            have heq := (natBeq_true_iff dstIdx j).mp hjd
            rw [← heq]
            rw [listGet?_listSet_eq _ dstIdx oldDst (LocalSlot.liveInit v) hdst2]
            rw [listGet?_listSet_eq st1.locals dstIdx oldDst (LocalSlot.liveInit v) holdDst]
        | false =>
            have hnej := (natBeq_false_iff dstIdx j).mp hjd
            rw [listGet?_listSet_ne _ dstIdx j (LocalSlot.liveInit v) hnej]
            rw [listGet?_listSet_ne _ wbIdx j (LocalSlot.liveInit v) hj']
            rw [listGet?_listSet_ne _ dstIdx j (LocalSlot.liveInit v) hnej]

/-- Diagnosis of GVN opacity (`compiler/rustc_mir_transform/src/gvn.rs:921,1101`):
    `gvn.rs:1101` lowers `WrapUnsafeBinder` to `Cast { kind: Transmute, value }`,
    while `gvn.rs:921` records `ProjectionElem::UnwrapUnsafeBinder(())` without
    simplifying `projUnwrapBinder (castTransmute v)`. -/
inductive GvnValue where
  | opaque (id : Nat)
  | tuple (fields : List GvnValue)
  | castTransmute (inner : GvnValue)
  | projField (idx : Nat) (inner : GvnValue)
  | projUnwrapBinder (inner : GvnValue)

noncomputable def gvnProjectCurrent (proj : ProjElem) (v : GvnValue) : GvnValue :=
  match proj, v with
  | .field idx, .tuple fs =>
      match listGet? fs idx with
      | some f => f
      | none => .projField idx (.tuple fs)
  | .field idx, other => .projField idx other
  | .unwrapUnsafeBinder _, other => .projUnwrapBinder other
  | .deref, other => other

noncomputable def gvnProjectWithCancel (proj : ProjElem) (v : GvnValue) : GvnValue :=
  match proj, v with
  | .field idx, .tuple fs =>
      match listGet? fs idx with
      | some f => f
      | none => .projField idx (.tuple fs)
  | .field idx, other => .projField idx other
  | .unwrapUnsafeBinder _, .castTransmute inner => inner
  | .unwrapUnsafeBinder _, other => .projUnwrapBinder other
  | .deref, other => other

theorem gvn_current_fails_wrap_unwrap_tuple (a b : GvnValue) :
    gvnProjectCurrent (.field 0)
      (gvnProjectCurrent (.unwrapUnsafeBinder (.tuple [.u32, .u64])) (.castTransmute (.tuple [a, b]))) =
      .projField 0 (.projUnwrapBinder (.castTransmute (.tuple [a, b]))) :=
  rfl

theorem gvn_fixed_cancels_wrap_unwrap_tuple (a b : GvnValue) :
    gvnProjectWithCancel (.field 0)
      (gvnProjectWithCancel (.unwrapUnsafeBinder (.tuple [.u32, .u64])) (.castTransmute (.tuple [a, b]))) =
      a :=
  rfl

/-- **Theorem (`SROA` Binder-Unwrapping Scalarization Soundness)**:
    Models the `wrap_unwrap_tuple(a : u32, b : u64) -> u32` kernel (`_3 = (a, b);
    _4 = wrap_binder!(_3); _0 = unwrap_binder!(_4).0`) vs scalarization into field
    locals `(f0, f1)` (`f0 = a; f1 = b; _0 = f0`), proving exact return-place and memory
    preservation across arbitrary `(va, vb)` and both `deinitMovedPlace` modes. -/
theorem sroa_binder_scalarize_sound
    (st : MirState) (va vb : Val)
    (retIdx argAIdx argBIdx tupIdx wbIdx f0Idx f1Idx : Nat)
    (hDistinct :
      retIdx ≠ argAIdx ∧ retIdx ≠ argBIdx ∧ retIdx ≠ tupIdx ∧ retIdx ≠ wbIdx ∧ retIdx ≠ f0Idx ∧ retIdx ≠ f1Idx ∧
      argAIdx ≠ argBIdx ∧ argAIdx ≠ tupIdx ∧ argAIdx ≠ wbIdx ∧ argAIdx ≠ f0Idx ∧ argAIdx ≠ f1Idx ∧
      argBIdx ≠ tupIdx ∧ argBIdx ≠ wbIdx ∧ argBIdx ≠ f0Idx ∧ argBIdx ≠ f1Idx ∧
      tupIdx ≠ wbIdx ∧ tupIdx ≠ f0Idx ∧ tupIdx ≠ f1Idx ∧
      wbIdx ≠ f0Idx ∧ wbIdx ≠ f1Idx ∧ f0Idx ≠ f1Idx)
    (hRet : listGet? st.locals retIdx = some .liveUninit)
    (hArgA : listGet? st.locals argAIdx = some (.liveInit va))
    (hArgB : listGet? st.locals argBIdx = some (.liveInit vb))
    (hTup : ∃ sl, listGet? st.locals tupIdx = some sl)
    (hWb : ∃ sl, listGet? st.locals wbIdx = some sl)
    (hF0 : ∃ sl, listGet? st.locals f0Idx = some sl)
    (hF1 : ∃ sl, listGet? st.locals f1Idx = some sl) :
    let tupleTy : Ty := .tuple [.u32, .u64]
    let binderTy : Ty := .unsafeBinder 0 tupleTy
    let srcBlock : List Stmt :=
      [ .storageLive tupIdx,
        .assign { localId := tupIdx, projs := [] }
          (.aggregateTuple [.copy { localId := argAIdx, projs := [] },
                            .copy { localId := argBIdx, projs := [] }]),
        .storageLive wbIdx,
        .assign { localId := wbIdx, projs := [] }
          (.wrapUnsafeBinder (.copy { localId := tupIdx, projs := [] }) binderTy),
        .assign { localId := retIdx, projs := [] }
          (.use (.copy { localId := wbIdx, projs := [.unwrapUnsafeBinder tupleTy, .field 0] }) false),
        .storageDead wbIdx,
        .storageDead tupIdx ]
    let sroaBlock : List Stmt :=
      [ .storageLive f0Idx,
        .storageLive f1Idx,
        .assign { localId := f0Idx, projs := [] } (.use (.copy { localId := argAIdx, projs := [] }) false),
        .assign { localId := f1Idx, projs := [] } (.use (.copy { localId := argBIdx, projs := [] }) false),
        .assign { localId := retIdx, projs := [] } (.use (.copy { localId := f0Idx, projs := [] }) false),
        .storageDead f1Idx,
        .storageDead f0Idx ]
    ∃ s1 s2,
      execBlock st srcBlock = .ok s1 ∧
      execBlock st sroaBlock = .ok s2 ∧
      listGet? s1.locals retIdx = some (.liveInit va) ∧
      listGet? s2.locals retIdx = some (.liveInit va) ∧
      s1.mem = s2.mem := by
  rcases hDistinct with ⟨hra, hrb, hrt, hrw, hrf0, hrf1,
    hab, hat, haw, haf0, haf1, hbt, hbw, hbf0, hbf1, htw, htf0, htf1, hwf0, hwf1, hf01⟩
  rcases hTup with ⟨slTup, hslTup⟩
  rcases hWb with ⟨slWb, hslWb⟩
  rcases hF0 with ⟨slF0, hslF0⟩
  rcases hF1 with ⟨slF1, hslF1⟩
  dsimp only
  have h1 : listGet? (listSet st.locals tupIdx .liveUninit) argAIdx = some (.liveInit va) := by
    rw [listGet?_listSet_ne _ tupIdx argAIdx _ hat.symm]; exact hArgA
  have h2 : listGet? (listSet st.locals tupIdx .liveUninit) argBIdx = some (.liveInit vb) := by
    rw [listGet?_listSet_ne _ tupIdx argBIdx _ hbt.symm]; exact hArgB
  have h3 : listGet? (listSet st.locals tupIdx .liveUninit) tupIdx = some .liveUninit :=
    listGet?_listSet_eq st.locals tupIdx slTup .liveUninit hslTup
  have h4 : listGet? (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx = some slWb := by
    rw [listGet?_listSet_ne _ tupIdx wbIdx _ htw]; exact hslWb
  have h5 : listGet? (listSet (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx .liveUninit) tupIdx =
      some (.liveInit (.tupleVal [va, vb])) := by
    rw [listGet?_listSet_ne _ wbIdx tupIdx _ htw.symm]
    exact listGet?_listSet_eq st.locals tupIdx slTup (.liveInit (.tupleVal [va, vb])) hslTup
  have h6 : listGet? (listSet (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx .liveUninit) wbIdx =
      some LocalSlot.liveUninit :=
    listGet?_listSet_eq _ wbIdx slWb LocalSlot.liveUninit h4
  have h7 : listGet? (listSet (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx (.liveInit (.tupleVal [va, vb]))) wbIdx =
      some (LocalSlot.liveInit (.tupleVal [va, vb])) :=
    listGet?_listSet_eq _ wbIdx slWb (LocalSlot.liveInit (.tupleVal [va, vb])) h4
  have h8 : listGet? (listSet (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx (.liveInit (.tupleVal [va, vb]))) retIdx =
      some LocalSlot.liveUninit := by
    rw [listGet?_listSet_ne _ wbIdx retIdx _ hrw.symm]
    rw [listGet?_listSet_ne _ tupIdx retIdx _ hrt.symm]
    exact hRet
  have h9 : listGet? (listSet (listSet (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx (.liveInit (.tupleVal [va, vb]))) retIdx (.liveInit va)) wbIdx =
      some (LocalSlot.liveInit (.tupleVal [va, vb])) := by
    rw [listGet?_listSet_ne _ retIdx wbIdx _ hrw]
    exact h7
  have h10 : listGet? (listSet (listSet (listSet (listSet st.locals tupIdx (.liveInit (.tupleVal [va, vb]))) wbIdx (.liveInit (.tupleVal [va, vb]))) retIdx (.liveInit va)) wbIdx .dead) tupIdx =
      some (LocalSlot.liveInit (.tupleVal [va, vb])) := by
    rw [listGet?_listSet_ne _ wbIdx tupIdx _ htw.symm]
    rw [listGet?_listSet_ne _ retIdx tupIdx _ hrt]
    rw [listGet?_listSet_ne _ wbIdx tupIdx _ htw.symm]
    exact listGet?_listSet_eq st.locals tupIdx slTup (LocalSlot.liveInit (.tupleVal [va, vb])) hslTup
  have g1 : listGet? (listSet st.locals f0Idx .liveUninit) f1Idx = some slF1 := by
    rw [listGet?_listSet_ne _ f0Idx f1Idx _ hf01]; exact hslF1
  have g2 : listGet? (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) argAIdx =
      some (LocalSlot.liveInit va) := by
    rw [listGet?_listSet_ne _ f1Idx argAIdx _ haf1.symm]
    rw [listGet?_listSet_ne _ f0Idx argAIdx _ haf0.symm]
    exact hArgA
  have g3 : listGet? (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx =
      some LocalSlot.liveUninit := by
    rw [listGet?_listSet_ne _ f1Idx f0Idx _ hf01.symm]
    exact listGet?_listSet_eq st.locals f0Idx slF0 LocalSlot.liveUninit hslF0
  have g4 : listGet? (listSet (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx (.liveInit va)) argBIdx =
      some (LocalSlot.liveInit vb) := by
    rw [listGet?_listSet_ne _ f0Idx argBIdx _ hbf0.symm]
    rw [listGet?_listSet_ne _ f1Idx argBIdx _ hbf1.symm]
    rw [listGet?_listSet_ne _ f0Idx argBIdx _ hbf0.symm]
    exact hArgB
  have g5 : listGet? (listSet (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx (.liveInit va)) f1Idx =
      some LocalSlot.liveUninit := by
    rw [listGet?_listSet_ne _ f0Idx f1Idx _ hf01]
    exact listGet?_listSet_eq _ f1Idx slF1 LocalSlot.liveUninit g1
  have g6 : listGet? (listSet (listSet (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx (.liveInit va)) f1Idx (.liveInit vb)) f0Idx =
      some (LocalSlot.liveInit va) := by
    rw [listGet?_listSet_ne _ f1Idx f0Idx _ hf01.symm]
    exact listGet?_listSet_eq _ f0Idx LocalSlot.liveUninit (LocalSlot.liveInit va) g3
  have g7 : listGet? (listSet (listSet (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx (.liveInit va)) f1Idx (.liveInit vb)) retIdx =
      some LocalSlot.liveUninit := by
    rw [listGet?_listSet_ne _ f1Idx retIdx _ hrf1.symm]
    rw [listGet?_listSet_ne _ f0Idx retIdx _ hrf0.symm]
    rw [listGet?_listSet_ne _ f1Idx retIdx _ hrf1.symm]
    rw [listGet?_listSet_ne _ f0Idx retIdx _ hrf0.symm]
    exact hRet
  have g8 : listGet? (listSet (listSet (listSet (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx (.liveInit va)) f1Idx (.liveInit vb)) retIdx (.liveInit va)) f1Idx =
      some (LocalSlot.liveInit vb) := by
    rw [listGet?_listSet_ne _ retIdx f1Idx _ hrf1]
    exact listGet?_listSet_eq _ f1Idx LocalSlot.liveUninit (LocalSlot.liveInit vb) g5
  have g9 : listGet? (listSet (listSet (listSet (listSet (listSet (listSet st.locals f0Idx .liveUninit) f1Idx .liveUninit) f0Idx (.liveInit va)) f1Idx (.liveInit vb)) retIdx (.liveInit va)) f1Idx .dead) f0Idx =
      some (LocalSlot.liveInit va) := by
    rw [listGet?_listSet_ne _ f1Idx f0Idx _ hf01.symm]
    rw [listGet?_listSet_ne _ retIdx f0Idx _ hrf0]
    exact g6
  have hPair0 : listGet? [va, vb] 0 = some va := rfl
  let s1 : MirState :=
    { locals := listSet (listSet (listSet (listSet (listSet st.locals tupIdx (LocalSlot.liveInit (.tupleVal [va, vb])))
        wbIdx (LocalSlot.liveInit (.tupleVal [va, vb]))) retIdx (LocalSlot.liveInit va)) wbIdx LocalSlot.dead) tupIdx LocalSlot.dead,
      mem := st.mem, vm := st.vm, bt := st.bt, deinitMovedPlace := st.deinitMovedPlace }
  let s2 : MirState :=
    { locals := listSet (listSet (listSet (listSet (listSet (listSet (listSet st.locals f0Idx LocalSlot.liveUninit)
        f1Idx LocalSlot.liveUninit) f0Idx (LocalSlot.liveInit va)) f1Idx (LocalSlot.liveInit vb)) retIdx (LocalSlot.liveInit va))
        f1Idx LocalSlot.dead) f0Idx LocalSlot.dead,
      mem := st.mem, vm := st.vm, bt := st.bt, deinitMovedPlace := st.deinitMovedPlace }
  refine ⟨s1, s2, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [execBlock, execStmt, evalRvalue, evalOperandList, evalOperand,
      writePlace, readValProj, hslTup, h1, h2, h3, listSet_listSet_same, h4, h5, h6, h7, h8, h9, h10, hPair0, s1]
  · simp only [execBlock, execStmt, evalRvalue, evalOperand, writePlace, readValProj,
      g1, g2, g3, g4, g5, g6, g7, g8, g9, hslF0, s2]
  · dsimp only [s1]
    rw [listGet?_listSet_ne _ tupIdx retIdx _ hrt.symm]
    rw [listGet?_listSet_ne _ wbIdx retIdx _ hrw.symm]
    exact listGet?_listSet_eq _ retIdx LocalSlot.liveUninit (LocalSlot.liveInit va) h8
  · dsimp only [s2]
    rw [listGet?_listSet_ne _ f0Idx retIdx _ hrf0.symm]
    rw [listGet?_listSet_ne _ f1Idx retIdx _ hrf1.symm]
    exact listGet?_listSet_eq _ retIdx LocalSlot.liveUninit (LocalSlot.liveInit va) g7

/-! ## Part IV: Total Prefix-Free `v0` Symbol-Mangling Production for `TyKind::UnsafeBinder` -/

/-- Constructive `Char` equality via `Nat` codepoints. -/
noncomputable def charBeq (a b : Char) : Bool :=
  natBeq a.toNat b.toNat

theorem charBeq_true_iff (a b : Char) : charBeq a b = true ↔ a = b := by
  unfold charBeq
  rw [natBeq_true_iff, Char.toNat_inj]

theorem charBeq_refl (a : Char) : charBeq a a = true :=
  (charBeq_true_iff a a).mpr rfl

/-- RFC 2603 / `v0.rs` base-62 digit encoder (`0..9`, `a..z`, `A..Z`). -/
noncomputable def encodeDigit62 : Nat → Char
  | 0 => '0'  | 1 => '1'  | 2 => '2'  | 3 => '3'  | 4 => '4'
  | 5 => '5'  | 6 => '6'  | 7 => '7'  | 8 => '8'  | 9 => '9'
  | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e'
  | 15 => 'f' | 16 => 'g' | 17 => 'h' | 18 => 'i' | 19 => 'j'
  | 20 => 'k' | 21 => 'l' | 22 => 'm' | 23 => 'n' | 24 => 'o'
  | 25 => 'p' | 26 => 'q' | 27 => 'r' | 28 => 's' | 29 => 't'
  | 30 => 'u' | 31 => 'v' | 32 => 'w' | 33 => 'x' | 34 => 'y'
  | 35 => 'z' | 36 => 'A' | 37 => 'B' | 38 => 'C' | 39 => 'D'
  | 40 => 'E' | 41 => 'F' | 42 => 'G' | 43 => 'H' | 44 => 'I'
  | 45 => 'J' | 46 => 'K' | 47 => 'L' | 48 => 'M' | 49 => 'N'
  | 50 => 'O' | 51 => 'P' | 52 => 'Q' | 53 => 'R' | 54 => 'S'
  | 55 => 'T' | 56 => 'U' | 57 => 'V' | 58 => 'W' | 59 => 'X'
  | 60 => 'Y' | 61 => 'Z' | _ => '0'

/-- RFC 2603 / `v0.rs` base-62 digit decoder. -/
noncomputable def decodeDigit62 : Char → Option Nat
  | '0' => some 0  | '1' => some 1  | '2' => some 2  | '3' => some 3  | '4' => some 4
  | '5' => some 5  | '6' => some 6  | '7' => some 7  | '8' => some 8  | '9' => some 9
  | 'a' => some 10 | 'b' => some 11 | 'c' => some 12 | 'd' => some 13 | 'e' => some 14
  | 'f' => some 15 | 'g' => some 16 | 'h' => some 17 | 'i' => some 18 | 'j' => some 19
  | 'k' => some 20 | 'l' => some 21 | 'm' => some 22 | 'n' => some 23 | 'o' => some 24
  | 'p' => some 25 | 'q' => some 26 | 'r' => some 27 | 's' => some 28 | 't' => some 29
  | 'u' => some 30 | 'v' => some 31 | 'w' => some 32 | 'x' => some 33 | 'y' => some 34
  | 'z' => some 35 | 'A' => some 36 | 'B' => some 37 | 'C' => some 38 | 'D' => some 39
  | 'E' => some 40 | 'F' => some 41 | 'G' => some 42 | 'H' => some 43 | 'I' => some 44
  | 'J' => some 45 | 'K' => some 46 | 'L' => some 47 | 'M' => some 48 | 'N' => some 49
  | 'O' => some 50 | 'P' => some 51 | 'Q' => some 52 | 'R' => some 53 | 'S' => some 54
  | 'T' => some 55 | 'U' => some 56 | 'V' => some 57 | 'W' => some 58 | 'X' => some 59
  | 'Y' => some 60 | 'Z' => some 61 | _ => none

theorem decodeDigit62_underscore : decodeDigit62 '_' = none := rfl

noncomputable def checkDigit62Table : Nat → Bool
  | 0 => true
  | n + 1 =>
      match decodeDigit62 (encodeDigit62 n) with
      | some m => match natBeq n m with | true => checkDigit62Table n | false => false
      | none => false

theorem checkDigit62Table_sound :
    ∀ k : Nat, checkDigit62Table k = true →
      ∀ d : Nat, d < k → decodeDigit62 (encodeDigit62 d) = some d := by
  intro k
  induction k with
  | zero => intro _ d hd; exact False.elim (Nat.not_lt_zero _ hd)
  | succ k' ih =>
      intro hk d hd
      unfold checkDigit62Table at hk
      cases hdec : decodeDigit62 (encodeDigit62 k') with
      | none => rw [hdec] at hk; exact False.elim (Bool.noConfusion hk)
      | some m =>
          rw [hdec] at hk
          dsimp only at hk
          cases hbeq : natBeq k' m with
          | false => rw [hbeq] at hk; exact False.elim (Bool.noConfusion hk)
          | true =>
              rw [hbeq] at hk
              dsimp only at hk
              have hkm : k' = m := (natBeq_true_iff k' m).mp hbeq
              subst hkm
              cases Nat.lt_succ_iff_lt_or_eq.mp hd with
              | inl hlt => exact ih hk d hlt
              | inr heq => subst heq; exact hdec

theorem decodeDigit62_encodeDigit62 (d : Nat) (hd : d < 62) :
    decodeDigit62 (encodeDigit62 d) = some d :=
  checkDigit62Table_sound 62 rfl d hd

theorem encodeDigit62_ne_underscore (d : Nat) (hd : d < 62) :
    encodeDigit62 d ≠ '_' := by
  intro heq
  have h := decodeDigit62_encodeDigit62 d hd
  rw [heq] at h
  cases h

/-- Pure multi-digit step evaluator for big-endian base-62 streams. -/
noncomputable def stepDigits (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
      match decodeDigit62 c with
      | none => none
      | some d => stepDigits (acc * 62 + d) cs

theorem stepDigits_snoc :
    ∀ (cs : List Char) (acc : Nat) (c : Char) (d : Nat),
      decodeDigit62 c = some d →
      stepDigits acc (cs ++ [c]) =
        match stepDigits acc cs with
        | none => none
        | some v => some (v * 62 + d) := by
  intro cs
  induction cs with
  | nil =>
      intro acc c d hc
      simp only [List.nil_append, stepDigits, hc]
  | cons x xs ih =>
      intro acc c d hc
      simp only [List.cons_append, stepDigits]
      cases hx : decodeDigit62 x with
      | none => rfl
      | some dx =>
          dsimp only
          exact ih (acc * 62 + dx) c d hc

theorem div62_lt (n : Nat) (h62 : 62 ≤ n) : n / 62 < n := by
  have hpos : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 61) h62
  have hgt1 : 1 < 62 := Nat.succ_lt_succ (Nat.zero_lt_succ 60)
  exact Nat.div_lt_self hpos hgt1

/-- Constructive fuel-indexed big-endian base-62 digit encoder (zero `_unsafe_rec`). -/
noncomputable def encodePosDigits62 : Nat → Nat → List Char
  | 0, _ => []
  | fuel' + 1, n =>
      match natBlt n 62 with
      | true => [encodeDigit62 n]
      | false => encodePosDigits62 fuel' (n / 62) ++ [encodeDigit62 (n % 62)]

theorem encodePosDigits62_stepDigits :
    ∀ (fuel n : Nat), n < fuel →
      stepDigits 0 (encodePosDigits62 fuel n) = some n := by
  intro fuel
  induction fuel with
  | zero => intro n hn; exact False.elim (Nat.not_lt_zero _ hn)
  | succ fuel' ih =>
      intro n hn
      unfold encodePosDigits62
      have hle : n ≤ fuel' := Nat.le_of_lt_succ hn
      cases hlt : natBlt n 62 with
      | true =>
          dsimp only
          have hn62 : n < 62 := (natBlt_true_iff n 62).mp hlt
          simp only [stepDigits, decodeDigit62_encodeDigit62 n hn62, Nat.zero_mul, Nat.zero_add]
      | false =>
          dsimp only
          have h62 : 62 ≤ n := (natBlt_false_iff n 62).mp hlt
          have hsub : n / 62 < fuel' := Nat.lt_of_lt_of_le (div62_lt n h62) hle
          have ihRec := ih (n / 62) hsub
          have hmod62 : n % 62 < 62 := Nat.mod_lt n (Nat.zero_lt_succ 61)
          have hdecMod := decodeDigit62_encodeDigit62 (n % 62) hmod62
          rw [stepDigits_snoc (encodePosDigits62 fuel' (n / 62)) 0 (encodeDigit62 (n % 62)) (n % 62) hdecMod]
          rw [ihRec]
          dsimp only
          rw [Nat.mul_comm (n / 62) 62, Nat.div_add_mod n 62]

theorem encodePosDigits62_ne_nil (y : Nat) : encodePosDigits62 (y + 1) y ≠ [] := by
  unfold encodePosDigits62
  cases natBlt y 62 with
  | true => intro h; cases h
  | false =>
      dsimp only
      cases encodePosDigits62 y (y / 62) <;> intro h <;> cases h

/-- RFC 2603 / `v0.rs:249-256` `_`-terminated integer encoder:
    `0 ↦ "_"`, `y + 1 ↦ base62(y) ++ "_"`. -/
noncomputable def encodeInteger62 : Nat → List Char
  | 0 => ['_']
  | y + 1 => encodePosDigits62 (y + 1) y ++ ['_']

/-- Structural streaming base-62 accumulator decoder terminating on `'_'`. -/
noncomputable def decodeBase62Acc (acc : Nat) : List Char → Option (Nat × List Char)
  | [] => none
  | c :: cs =>
      match charBeq c '_' with
      | true => some (acc, cs)
      | false =>
          match decodeDigit62 c with
          | none => none
          | some d => decodeBase62Acc (acc * 62 + d) cs

theorem decodeBase62Acc_append_stepDigits :
    ∀ (ds : List Char) (acc v : Nat) (rest : List Char),
      stepDigits acc ds = some v →
      decodeBase62Acc acc (ds ++ '_' :: rest) = some (v, rest) := by
  intro ds
  induction ds with
  | nil =>
      intro acc v rest h
      simp only [stepDigits] at h
      injection h with heq
      rw [heq]
      dsimp only [List.nil_append, decodeBase62Acc]
      rw [charBeq_refl '_']
  | cons x xs ih =>
      intro acc v rest h
      simp only [stepDigits] at h
      cases hx : decodeDigit62 x with
      | none => rw [hx] at h; cases h
      | some dx =>
          rw [hx] at h
          dsimp only at h
          have hne : x ≠ '_' := by
            intro heq
            rw [heq] at hx
            cases hx
          have hbeq : charBeq x '_' = false := by
            cases hb : charBeq x '_' with
            | false => rfl
            | true => exact False.elim (hne ((charBeq_true_iff x '_').mp hb))
          dsimp only [List.cons_append, decodeBase62Acc]
          rw [hbeq]
          dsimp only
          rw [hx]
          exact ih (acc * 62 + dx) v rest h

/-- Inverse of `encodeInteger62`: `decodeInteger62 (encodeInteger62 n ++ rest) = some (n, rest)`. -/
noncomputable def decodeInteger62 : List Char → Option (Nat × List Char)
  | [] => none
  | c :: cs =>
      match charBeq c '_' with
      | true => some (0, cs)
      | false =>
          match decodeDigit62 c with
          | none => none
          | some d =>
              match decodeBase62Acc d cs with
              | none => none
              | some (v, rest) => some (v + 1, rest)

theorem decodeInteger62_encodeInteger62_roundtrip (n : Nat) (rest : List Char) :
    decodeInteger62 (encodeInteger62 n ++ rest) = some (n, rest) := by
  cases n with
  | zero =>
      simp only [encodeInteger62, List.singleton_append, decodeInteger62, charBeq_refl]
  | succ y =>
      have hne := encodePosDigits62_ne_nil y
      have hstep := encodePosDigits62_stepDigits (y + 1) y (Nat.lt_succ_self y)
      cases hds : encodePosDigits62 (y + 1) y with
      | nil => exact False.elim (hne hds)
      | cons c ds' =>
          rw [hds] at hstep
          simp only [stepDigits] at hstep
          cases hc : decodeDigit62 c with
          | none => rw [hc] at hstep; cases hstep
          | some d =>
              rw [hc] at hstep
              dsimp only at hstep
              rw [Nat.zero_mul, Nat.zero_add] at hstep
              have hacc := decodeBase62Acc_append_stepDigits ds' d y rest hstep
              have hcne : c ≠ '_' := by
                intro heq; rw [heq] at hc; cases hc
              have hcbeq : charBeq c '_' = false := by
                cases hb : charBeq c '_' with
                | false => rfl
                | true => exact False.elim (hcne ((charBeq_true_iff c '_').mp hb))
              simp only [encodeInteger62, hds, List.append_assoc, List.cons_append, List.nil_append,
                decodeInteger62, hcbeq, hc, hacc]

/-- RFC 2603 / `v0.rs:262-267` optional `tag`-prefixed integer encoder (`0 ↦ ""`, `x + 1 ↦ tag ++ int(x)`). -/
noncomputable def encodeOptInteger62 (tag : Char) : Nat → List Char
  | 0 => []
  | x + 1 => tag :: encodeInteger62 x

/-- Inverse of `encodeOptInteger62 tag` whenever non-tagged suffixes cannot start with `tag`. -/
noncomputable def decodeOptInteger62 (tag : Char) : List Char → Option (Nat × List Char)
  | [] => some (0, [])
  | c :: cs =>
      match charBeq c tag with
      | true =>
          match decodeInteger62 cs with
          | none => none
          | some (x, rest) => some (x + 1, rest)
      | false => some (0, c :: cs)

theorem decodeOptInteger62_encodeOptInteger62_roundtrip
    (tag : Char) (n : Nat) (rest : List Char)
    (hhead : ∀ c cs, rest = c :: cs → c ≠ tag) :
    decodeOptInteger62 tag (encodeOptInteger62 tag n ++ rest) = some (n, rest) := by
  cases n with
  | zero =>
      cases rest with
      | nil => rfl
      | cons c cs =>
          have hne := hhead c cs rfl
          have hb : charBeq c tag = false := by
            cases hq : charBeq c tag with
            | false => rfl
            | true => exact False.elim (hne ((charBeq_true_iff c tag).mp hq))
          simp only [encodeOptInteger62, List.nil_append, decodeOptInteger62, hb]
  | succ x =>
      simp only [encodeOptInteger62, List.cons_append, decodeOptInteger62, charBeq_refl,
        decodeInteger62_encodeInteger62_roundtrip]

/-- Region representation for RFC 2603 `v0` mangling (`erased` vs `L<idx>_`). -/
inductive MangleRegion where
  | erased
  | bound (idx : Nat)

noncomputable def encodeMangleRegion : MangleRegion → List Char
  | .erased => []
  | .bound idx => 'L' :: encodeInteger62 idx

noncomputable def decodeMangleRegion : List Char → Option (MangleRegion × List Char)
  | [] => some (.erased, [])
  | c :: cs =>
      match charBeq c 'L' with
      | true =>
          match decodeInteger62 cs with
          | none => none
          | some (idx, rest) => some (.bound idx, rest)
      | false => some (.erased, c :: cs)

theorem decodeMangleRegion_encodeMangleRegion_roundtrip
    (r : MangleRegion) (rest : List Char)
    (hhead : ∀ c cs, rest = c :: cs → c ≠ 'L') :
    decodeMangleRegion (encodeMangleRegion r ++ rest) = some (r, rest) := by
  cases r with
  | erased =>
      cases rest with
      | nil => rfl
      | cons c cs =>
          have hne := hhead c cs rfl
          have hb : charBeq c 'L' = false := by
            cases hq : charBeq c 'L' with
            | false => rfl
            | true => exact False.elim (hne ((charBeq_true_iff c 'L').mp hq))
          simp only [encodeMangleRegion, List.nil_append, decodeMangleRegion, hb]
  | bound idx =>
      simp only [encodeMangleRegion, List.cons_append, decodeMangleRegion, charBeq_refl,
        decodeInteger62_encodeInteger62_roundtrip]

/-- Extended RFC 2603 / `v0.rs` type AST adding `.unsafeBinder` under unused prefix tag `'Z'`. -/
inductive MangleTy where
  | bool
  | u32
  | u64
  | unit
  | never
  | ref (mutbl : Bool) (reg : MangleRegion) (inner : MangleTy)
  | rawPtr (mutbl : Bool) (inner : MangleTy)
  | tuple (fields : List MangleTy)
  | fnPtr (boundLifetimes : Nat) (isUnsafe : Bool) (isCAbi : Bool)
          (inputs : List MangleTy) (output : MangleTy)
  | unsafeBinder (boundLifetimes : Nat) (inner : MangleTy)

/- Total `v0` type encoder extending `rustc_symbol_mangling/src/v0.rs:521-692` with `'Z'`
   for `TyKind::UnsafeBinder(Binder<Ty>)` (`Z [G<n>_] <ty>`). -/
mutual
  noncomputable def encodeMangleTy : MangleTy → List Char
    | .bool => ['b']
    | .u32 => ['m']
    | .u64 => ['y']
    | .unit => ['u']
    | .never => ['z']
    | .ref false reg inner => ['R'] ++ encodeMangleRegion reg ++ encodeMangleTy inner
    | .ref true reg inner => ['Q'] ++ encodeMangleRegion reg ++ encodeMangleTy inner
    | .rawPtr false inner => ['P'] ++ encodeMangleTy inner
    | .rawPtr true inner => ['O'] ++ encodeMangleTy inner
    | .tuple fields => ['T'] ++ encodeMangleTyList fields ++ ['E']
    | .fnPtr bl isU isC inputs out =>
        ['F'] ++
        encodeOptInteger62 'G' bl ++
        (match isU with | true => ['U'] | false => []) ++
        (match isC with | true => ['K', 'C'] | false => []) ++
        encodeMangleTyList inputs ++
        ['E'] ++
        encodeMangleTy out
    | .unsafeBinder bl inner =>
        ['Z'] ++ encodeOptInteger62 'G' bl ++ encodeMangleTy inner

  noncomputable def encodeMangleTyList : List MangleTy → List Char
    | [] => []
    | t :: ts => encodeMangleTy t ++ encodeMangleTyList ts
end

noncomputable def mangleTagChars : MangleTy → Char
  | .bool => 'b'
  | .u32 => 'm'
  | .u64 => 'y'
  | .unit => 'u'
  | .never => 'z'
  | .ref false _ _ => 'R'
  | .ref true _ _ => 'Q'
  | .rawPtr false _ => 'P'
  | .rawPtr true _ => 'O'
  | .tuple _ => 'T'
  | .fnPtr _ _ _ _ _ => 'F'
  | .unsafeBinder _ _ => 'Z'

theorem encodeMangleTy_head (t : MangleTy) :
    ∃ tail, encodeMangleTy t = mangleTagChars t :: tail := by
  cases t with
  | bool => exact ⟨[], rfl⟩
  | u32 => exact ⟨[], rfl⟩
  | u64 => exact ⟨[], rfl⟩
  | unit => exact ⟨[], rfl⟩
  | never => exact ⟨[], rfl⟩
  | ref mutbl reg inner =>
      cases mutbl
      · exact ⟨encodeMangleRegion reg ++ encodeMangleTy inner, rfl⟩
      · exact ⟨encodeMangleRegion reg ++ encodeMangleTy inner, rfl⟩
  | rawPtr mutbl inner =>
      cases mutbl
      · exact ⟨encodeMangleTy inner, rfl⟩
      · exact ⟨encodeMangleTy inner, rfl⟩
  | tuple fields => exact ⟨encodeMangleTyList fields ++ ['E'], rfl⟩
  | fnPtr bl isU isC inputs out =>
      exact ⟨encodeOptInteger62 'G' bl ++ (match isU with | true => ['U'] | false => []) ++
        (match isC with | true => ['K', 'C'] | false => []) ++ encodeMangleTyList inputs ++ ['E'] ++ encodeMangleTy out, rfl⟩
  | unsafeBinder bl inner =>
      exact ⟨encodeOptInteger62 'G' bl ++ encodeMangleTy inner, rfl⟩

noncomputable def isAllowedMangleHead : Char → Bool
  | 'b' | 'm' | 'y' | 'u' | 'z' | 'R' | 'Q' | 'P' | 'O' | 'T' | 'F' | 'Z' => true
  | _ => false

theorem isAllowedMangleHead_tag (t : MangleTy) : isAllowedMangleHead (mangleTagChars t) = true := by
  cases t with
  | ref mutbl _ _ => cases mutbl <;> rfl
  | rawPtr mutbl _ => cases mutbl <;> rfl
  | bool => rfl
  | u32 => rfl
  | u64 => rfl
  | unit => rfl
  | never => rfl
  | tuple _ => rfl
  | fnPtr _ _ _ _ _ => rfl
  | unsafeBinder _ _ => rfl

theorem allowedMangleHead_not_ctrl (c : Char) (h : isAllowedMangleHead c = true) :
    c ≠ 'L' ∧ c ≠ 'G' ∧ c ≠ 'U' ∧ c ≠ 'K' ∧ c ≠ 'E' ∧ c ≠ '_' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro heq; rw [heq] at h; exact Bool.noConfusion h)

/-- Every valid `<type>` production begins with a head character disjoint from `v0` binder/modifier
    control markers `'L'`, `'G'`, `'U'`, `'K'`, `'E'`, `'_'`. -/
theorem encodeMangleTy_head_not_ctrl (t : MangleTy) (c : Char) (cs : List Char)
    (h : encodeMangleTy t = c :: cs) :
    c ≠ 'L' ∧ c ≠ 'G' ∧ c ≠ 'U' ∧ c ≠ 'K' ∧ c ≠ 'E' ∧ c ≠ '_' := by
  rcases encodeMangleTy_head t with ⟨tail, ht⟩
  rw [ht] at h
  injection h with hc _
  have ha := isAllowedMangleHead_tag t
  rw [hc] at ha
  exact allowedMangleHead_not_ctrl c ha

theorem encodeMangleTyList_head_not_ctrl (ts : List MangleTy) (rest : List Char)
    (hhead : ∀ c cs, rest = c :: cs → c ≠ 'L' ∧ c ≠ 'G' ∧ c ≠ 'U' ∧ c ≠ 'K') :
    ∀ c cs, encodeMangleTyList ts ++ rest = c :: cs →
      c ≠ 'L' ∧ c ≠ 'G' ∧ c ≠ 'U' ∧ c ≠ 'K' ∧ (ts ≠ [] → c ≠ 'E') := by
  cases ts with
  | nil =>
      intro c cs h
      rw [encodeMangleTyList, List.nil_append] at h
      have h4 := hhead c cs h
      exact ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2, fun hne => False.elim (hne rfl)⟩
  | cons t ts' =>
      intro c cs h
      simp only [encodeMangleTyList, List.append_assoc] at h
      rcases encodeMangleTy_head t with ⟨tail, ht⟩
      rw [ht, List.cons_append] at h
      injection h with hc _
      have ht' : encodeMangleTy t = c :: tail := by rw [← hc]; exact ht
      have hctrl := encodeMangleTy_head_not_ctrl t c tail ht'
      exact ⟨hctrl.1, hctrl.2.1, hctrl.2.2.1, hctrl.2.2.2.1, fun _ => hctrl.2.2.2.2.1⟩

noncomputable def decodeFlagU : List Char → Bool × List Char
  | c :: cs => match charBeq c 'U' with | true => (true, cs) | false => (false, c :: cs)
  | [] => (false, [])

noncomputable def decodeFlagKC : List Char → Bool × List Char
  | c1 :: c2 :: cs =>
      match charBeq c1 'K', charBeq c2 'C' with
      | true, true => (true, cs)
      | _, _ => (false, c1 :: c2 :: cs)
  | xs => (false, xs)

theorem decodeFlagU_roundtrip (isU : Bool) (rest : List Char)
    (hhead : ∀ c cs, rest = c :: cs → c ≠ 'U') :
    decodeFlagU ((match isU with | true => ['U'] | false => []) ++ rest) = (isU, rest) := by
  cases isU with
  | true =>
      dsimp only [List.singleton_append, decodeFlagU]
      rw [charBeq_refl 'U']
  | false =>
      cases rest with
      | nil => rfl
      | cons c cs =>
          have hne := hhead c cs rfl
          have hb : charBeq c 'U' = false := by
            cases hq : charBeq c 'U' with
            | false => rfl
            | true => exact False.elim (hne ((charBeq_true_iff c 'U').mp hq))
          dsimp only [List.nil_append, decodeFlagU]
          rw [hb]

theorem decodeFlagKC_roundtrip (isC : Bool) (rest : List Char)
    (hhead : ∀ c cs, rest = c :: cs → c ≠ 'K') :
    decodeFlagKC ((match isC with | true => ['K', 'C'] | false => []) ++ rest) = (isC, rest) := by
  cases isC with
  | true =>
      dsimp only [List.cons_append, List.nil_append, decodeFlagKC]
      rw [charBeq_refl 'K', charBeq_refl 'C']
  | false =>
      cases rest with
      | nil => rfl
      | cons c1 xs =>
          cases xs with
          | nil => rfl
          | cons c2 cs =>
              have hne := hhead c1 (c2 :: cs) rfl
              have hb1 : charBeq c1 'K' = false := by
                cases hq : charBeq c1 'K' with
                | false => rfl
                | true => exact False.elim (hne ((charBeq_true_iff c1 'K').mp hq))
              dsimp only [List.nil_append, decodeFlagKC]
              rw [hb1]

mutual
  noncomputable def mangleFuel : MangleTy → Nat
    | .bool => 1
    | .u32 => 1
    | .u64 => 1
    | .unit => 1
    | .never => 1
    | .ref _ _ inner => mangleFuel inner + 1
    | .rawPtr _ inner => mangleFuel inner + 1
    | .tuple fs => mangleListFuel fs + 2
    | .fnPtr _ _ _ ins out => mangleListFuel ins + mangleFuel out + 2
    | .unsafeBinder _ inner => mangleFuel inner + 1

  noncomputable def mangleListFuel : List MangleTy → Nat
    | [] => 1
    | t :: ts => mangleFuel t + mangleListFuel ts + 1
end

mutual
  noncomputable def decodeMangleTy : Nat → List Char → Option (MangleTy × List Char)
    | 0, _ => none
    | _ + 1, 'b' :: rest => some (.bool, rest)
    | _ + 1, 'm' :: rest => some (.u32, rest)
    | _ + 1, 'y' :: rest => some (.u64, rest)
    | _ + 1, 'u' :: rest => some (.unit, rest)
    | _ + 1, 'z' :: rest => some (.never, rest)
    | fuel' + 1, 'R' :: rest =>
        match decodeMangleRegion rest with
        | none => none
        | some (reg, rest1) =>
            match decodeMangleTy fuel' rest1 with
            | none => none
            | some (inner, rest2) => some (.ref false reg inner, rest2)
    | fuel' + 1, 'Q' :: rest =>
        match decodeMangleRegion rest with
        | none => none
        | some (reg, rest1) =>
            match decodeMangleTy fuel' rest1 with
            | none => none
            | some (inner, rest2) => some (.ref true reg inner, rest2)
    | fuel' + 1, 'P' :: rest =>
        match decodeMangleTy fuel' rest with
        | none => none
        | some (inner, rest1) => some (.rawPtr false inner, rest1)
    | fuel' + 1, 'O' :: rest =>
        match decodeMangleTy fuel' rest with
        | none => none
        | some (inner, rest1) => some (.rawPtr true inner, rest1)
    | fuel' + 1, 'T' :: rest =>
        match decodeMangleTyArgs fuel' rest with
        | none => none
        | some (fields, rest1) => some (.tuple fields, rest1)
    | fuel' + 1, 'F' :: rest =>
        match decodeOptInteger62 'G' rest with
        | none => none
        | some (bl, rest1) =>
            match decodeFlagU rest1 with
            | (isU, rest2) =>
                match decodeFlagKC rest2 with
                | (isC, rest3) =>
                    match decodeMangleTyArgs fuel' rest3 with
                    | none => none
                    | some (ins, rest4) =>
                        match decodeMangleTy fuel' rest4 with
                        | none => none
                        | some (out, rest5) => some (.fnPtr bl isU isC ins out, rest5)
    | fuel' + 1, 'Z' :: rest =>
        match decodeOptInteger62 'G' rest with
        | none => none
        | some (bl, rest1) =>
            match decodeMangleTy fuel' rest1 with
            | none => none
            | some (inner, rest2) => some (.unsafeBinder bl inner, rest2)
    | _ + 1, _ => none

  noncomputable def decodeMangleTyArgs : Nat → List Char → Option (List MangleTy × List Char)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel' + 1, c :: rest =>
        match charBeq c 'E' with
        | true => some ([], rest)
        | false =>
            match decodeMangleTy fuel' (c :: rest) with
            | none => none
            | some (t, rest1) =>
                match decodeMangleTyArgs fuel' rest1 with
                | none => none
                | some (ts, rest2) => some (t :: ts, rest2)
end

/-- Combined fuel-indexed round-trip correctness theorem proving zero parse ambiguity
    across primitives, references, raw pointers, tuples, `fn` pointers (`F [G] [U] [KC]`),
    and unsafe binders (`Z [G]`). -/
theorem decodeMangleTy_roundtrip_both :
    ∀ (fuel : Nat),
      (∀ (t : MangleTy) (rest : List Char),
        mangleFuel t ≤ fuel →
        decodeMangleTy fuel (encodeMangleTy t ++ rest) = some (t, rest)) ∧
      (∀ (ts : List MangleTy) (rest : List Char),
        mangleListFuel ts ≤ fuel →
        decodeMangleTyArgs fuel (encodeMangleTyList ts ++ 'E' :: rest) = some (ts, rest)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro t rest h
        cases t <;> cases h
      · intro ts rest h
        cases ts <;> cases h
  | succ fuel' ih =>
      rcases ih with ⟨ihTy, ihList⟩
      constructor
      · intro t rest h
        cases t with
        | bool => rfl
        | u32 => rfl
        | u64 => rfl
        | unit => rfl
        | never => rfl
        | ref mutbl reg inner =>
            have hle : mangleFuel inner ≤ fuel' := Nat.le_of_succ_le_succ h
            have hrec := ihTy inner rest hle
            have hreg : decodeMangleRegion (encodeMangleRegion reg ++ (encodeMangleTy inner ++ rest)) =
                some (reg, encodeMangleTy inner ++ rest) := by
              apply decodeMangleRegion_encodeMangleRegion_roundtrip
              intro c cs hc
              rcases encodeMangleTy_head inner with ⟨tail, ht⟩
              rw [ht, List.cons_append] at hc
              injection hc with hcc _
              have ht' : encodeMangleTy inner = c :: tail := by rw [← hcc]; exact ht
              exact (encodeMangleTy_head_not_ctrl inner c tail ht').1
            cases mutbl with
            | false =>
                simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
                rw [hreg]
                dsimp only
                rw [hrec]
            | true =>
                simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
                rw [hreg]
                dsimp only
                rw [hrec]
        | rawPtr mutbl inner =>
            have hle : mangleFuel inner ≤ fuel' := Nat.le_of_succ_le_succ h
            have hrec := ihTy inner rest hle
            cases mutbl with
            | false =>
                simp only [encodeMangleTy, List.cons_append, List.nil_append, decodeMangleTy]
                rw [hrec]
            | true =>
                simp only [encodeMangleTy, List.cons_append, List.nil_append, decodeMangleTy]
                rw [hrec]
        | tuple fields =>
            have hle1 : mangleListFuel fields + 1 ≤ fuel' := Nat.le_of_succ_le_succ h
            have hle : mangleListFuel fields ≤ fuel' := Nat.le_trans (Nat.le_succ _) hle1
            have hrec := ihList fields rest hle
            simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
            rw [hrec]
        | unsafeBinder bl inner =>
            have hle : mangleFuel inner ≤ fuel' := Nat.le_of_succ_le_succ h
            have hrec := ihTy inner rest hle
            have hbl : decodeOptInteger62 'G' (encodeOptInteger62 'G' bl ++ (encodeMangleTy inner ++ rest)) =
                some (bl, encodeMangleTy inner ++ rest) := by
              apply decodeOptInteger62_encodeOptInteger62_roundtrip
              intro c cs hc
              rcases encodeMangleTy_head inner with ⟨tail, ht⟩
              rw [ht, List.cons_append] at hc
              injection hc with hcc _
              have ht' : encodeMangleTy inner = c :: tail := by rw [← hcc]; exact ht
              exact (encodeMangleTy_head_not_ctrl inner c tail ht').2.1
            simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
            rw [hbl]
            dsimp only
            rw [hrec]
        | fnPtr bl isU isC ins out =>
            have hle1 : mangleListFuel ins + mangleFuel out + 1 ≤ fuel' := Nat.le_of_succ_le_succ h
            have hleSum : mangleListFuel ins + mangleFuel out ≤ fuel' := Nat.le_trans (Nat.le_succ _) hle1
            have hleIns : mangleListFuel ins ≤ fuel' := Nat.le_trans (Nat.le_add_right _ _) hleSum
            have hleOut : mangleFuel out ≤ fuel' := Nat.le_trans (Nat.le_add_left _ _) hleSum
            have hrecIns := ihList ins (encodeMangleTy out ++ rest) hleIns
            have hrecOut := ihTy out rest hleOut
            have hArgsCtrl : ∀ c cs, encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest) = c :: cs →
                c ≠ 'L' ∧ c ≠ 'G' ∧ c ≠ 'U' ∧ c ≠ 'K' ∧ (ins ≠ [] → c ≠ 'E') := by
              apply encodeMangleTyList_head_not_ctrl ins ('E' :: (encodeMangleTy out ++ rest))
              intro c cs hc
              injection hc with he _
              rw [← he]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; cases h)
            cases isU with
            | true =>
                cases isC with
                | true =>
                    have hG := decodeOptInteger62_encodeOptInteger62_roundtrip 'G' bl
                      ('U' :: 'K' :: 'C' :: (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest)))
                      (fun c _ hc => by injection hc with hcc _; rw [← hcc]; intro hx; cases hx)
                    simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
                    rw [hG]
                    dsimp only [decodeFlagU]
                    rw [charBeq_refl 'U']
                    dsimp only [decodeFlagKC]
                    rw [charBeq_refl 'K', charBeq_refl 'C']
                    dsimp only
                    rw [hrecIns]
                    dsimp only
                    rw [hrecOut]
                | false =>
                    have hG := decodeOptInteger62_encodeOptInteger62_roundtrip 'G' bl
                      ('U' :: (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest)))
                      (fun c _ hc => by injection hc with hcc _; rw [← hcc]; intro hx; cases hx)
                    have hKC := decodeFlagKC_roundtrip false
                      (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest))
                      (fun c cs hc => (hArgsCtrl c cs hc).2.2.2.1)
                    dsimp only [List.nil_append] at hKC
                    simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
                    rw [hG]
                    dsimp only [decodeFlagU]
                    rw [charBeq_refl 'U']
                    dsimp only
                    rw [hKC]
                    dsimp only
                    rw [hrecIns]
                    dsimp only
                    rw [hrecOut]
            | false =>
                cases isC with
                | true =>
                    have hG := decodeOptInteger62_encodeOptInteger62_roundtrip 'G' bl
                      ('K' :: 'C' :: (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest)))
                      (fun c _ hc => by injection hc with hcc _; rw [← hcc]; intro hx; cases hx)
                    have hU := decodeFlagU_roundtrip false
                      ('K' :: 'C' :: (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest)))
                      (fun c _ hc => by injection hc with hcc _; rw [← hcc]; intro hx; cases hx)
                    dsimp only [List.nil_append] at hU
                    simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
                    rw [hG]
                    dsimp only
                    rw [hU]
                    dsimp only [decodeFlagKC]
                    rw [charBeq_refl 'K', charBeq_refl 'C']
                    dsimp only
                    rw [hrecIns]
                    dsimp only
                    rw [hrecOut]
                | false =>
                    have hG := decodeOptInteger62_encodeOptInteger62_roundtrip 'G' bl
                      (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest))
                      (fun c cs hc => (hArgsCtrl c cs hc).2.1)
                    have hU := decodeFlagU_roundtrip false
                      (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest))
                      (fun c cs hc => (hArgsCtrl c cs hc).2.2.1)
                    have hKC := decodeFlagKC_roundtrip false
                      (encodeMangleTyList ins ++ 'E' :: (encodeMangleTy out ++ rest))
                      (fun c cs hc => (hArgsCtrl c cs hc).2.2.2.1)
                    dsimp only [List.nil_append] at hU hKC
                    simp only [encodeMangleTy, List.append_assoc, List.cons_append, List.nil_append, decodeMangleTy]
                    rw [hG]
                    dsimp only
                    rw [hU]
                    dsimp only
                    rw [hKC]
                    dsimp only
                    rw [hrecIns]
                    dsimp only
                    rw [hrecOut]
      · intro ts rest h
        cases ts with
        | nil =>
            dsimp only [encodeMangleTyList, List.nil_append, decodeMangleTyArgs]
            rw [charBeq_refl 'E']
        | cons t ts' =>
            have hle0 : mangleFuel t + mangleListFuel ts' ≤ fuel' := Nat.le_of_succ_le_succ h
            have hleT : mangleFuel t ≤ fuel' := Nat.le_trans (Nat.le_add_right _ _) hle0
            have hleTs : mangleListFuel ts' ≤ fuel' := Nat.le_trans (Nat.le_add_left _ _) hle0
            have hrecT := ihTy t (encodeMangleTyList ts' ++ 'E' :: rest) hleT
            have hrecTs := ihList ts' rest hleTs
            rcases encodeMangleTy_head t with ⟨tail, ht⟩
            have hcne := (encodeMangleTy_head_not_ctrl t (mangleTagChars t) tail ht).2.2.2.2.1
            have hbeq : charBeq (mangleTagChars t) 'E' = false := by
              cases hq : charBeq (mangleTagChars t) 'E' with
              | false => rfl
              | true => exact False.elim (hcne ((charBeq_true_iff (mangleTagChars t) 'E').mp hq))
            dsimp only [encodeMangleTyList]
            rw [List.append_assoc, ht]
            dsimp only [List.cons_append, decodeMangleTyArgs]
            rw [hbeq]
            dsimp only
            rw [← List.cons_append, ← ht]
            rw [hrecT]
            dsimp only
            rw [hrecTs]

/-- Standalone decoder theorem for any encoded `MangleTy`. -/
theorem decodeMangleTy_encodeMangleTy_roundtrip (t : MangleTy) (rest : List Char) :
    decodeMangleTy (mangleFuel t) (encodeMangleTy t ++ rest) = some (t, rest) :=
  (decodeMangleTy_roundtrip_both (mangleFuel t)).1 t rest (Nat.le_refl _)

/-- **Theorem (Full Prefix-Freeness / Self-Delimitation)**:
    No valid `v0` encoding extended with `'Z'` for `UnsafeBinder` is a strict prefix
    of any other valid encoding. -/
theorem encodeMangleTy_prefix_free (t1 t2 : MangleTy) (s1 s2 : List Char)
    (h : encodeMangleTy t1 ++ s1 = encodeMangleTy t2 ++ s2) :
    t1 = t2 ∧ s1 = s2 := by
  let fuel := mangleFuel t1 + mangleFuel t2
  have h1 := (decodeMangleTy_roundtrip_both fuel).1 t1 s1 (Nat.le_add_right _ _)
  have h2 := (decodeMangleTy_roundtrip_both fuel).1 t2 s2 (Nat.le_add_left _ _)
  rw [h] at h1
  rw [h1] at h2
  injection h2 with hpair
  injection hpair with ht hs
  exact ⟨ht, hs⟩

/-- **Theorem (`v0` Mangling Injectivity)**:
    Two distinct `MangleTy` terms (including `unsafe<'a> T` vs `unsafe<> T`, safe `fn` vs `unsafe fn`,
    bound lifetimes vs erased lifetimes) never map to the same symbol string. -/
theorem encodeMangleTy_injective (t1 t2 : MangleTy)
    (h : encodeMangleTy t1 = encodeMangleTy t2) :
    t1 = t2 := by
  have hpf := encodeMangleTy_prefix_free t1 t2 [] [] (by rw [List.append_nil, List.append_nil, h])
  exact hpf.1

/-! ### Golden Regression Specimens & Collision-Freedom Certificates -/

theorem mangle_unsafeBinder_empty_u32_golden :
    encodeMangleTy (.unsafeBinder 0 .u32) = ['Z', 'm'] := rfl

theorem mangle_unsafeBinder_mut_ref_golden :
    encodeMangleTy (.unsafeBinder 1 (.ref true (.bound 1) .u32)) =
      ['Z', 'G', '_', 'Q', 'L', '0', '_', 'm'] := rfl

theorem mangle_fnPtr_taking_unsafeBinder_vs_unsafeFn_distinct :
    encodeMangleTy (.fnPtr 0 false false [.unsafeBinder 0 .u32] .u32) = ['F', 'Z', 'm', 'E', 'm'] ∧
    encodeMangleTy (.fnPtr 0 true false [.u32] .u32) = ['F', 'U', 'm', 'E', 'm'] ∧
    encodeMangleTy (.fnPtr 0 false false [.unsafeBinder 0 .u32] .u32) ≠
      encodeMangleTy (.fnPtr 0 true false [.u32] .u32) :=
  ⟨rfl, rfl, by intro h; cases h⟩

theorem mangle_unsafeBinder_collides_if_using_U :
    (['F', 'U', 'm', 'E', 'm'] : List Char) =
      encodeMangleTy (.fnPtr 0 true false [.u32] .u32) := rfl

theorem mangle_unsafeBinder_collides_if_using_G :
    (['F', 'G', '_', 'Q', 'L', '0', '_', 'm', 'E', 'm'] : List Char) =
      encodeMangleTy (.fnPtr 1 false false [.ref true (.bound 1) .u32] .u32) := rfl

theorem mangle_unsafeBinder_collides_if_using_K :
    (['F', 'K', 'C', 'E', 'm'] : List Char) =
      encodeMangleTy (.fnPtr 0 false true [] .u32) := rfl

theorem mangle_unsafeBinder_collides_if_using_E :
    (['F', 'E', 'm'] : List Char) =
      encodeMangleTy (.fnPtr 0 false false [] .u32) := rfl

end UnsafeBindersFormal

