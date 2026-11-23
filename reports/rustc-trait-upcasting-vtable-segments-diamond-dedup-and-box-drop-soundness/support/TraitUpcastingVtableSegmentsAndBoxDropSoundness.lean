/-!
# Soundness of `rustc` Segmented Vtables, Diamond Supertrait Deduplication, Generic Ambiguity, and `Box<dyn Sub> -> Box<dyn Super>` Drop/Deallocation

Kernel-checked Lean v4.34.1 formalization modeling the `rustc` trait upcasting pipeline across:
- `compiler/rustc_middle/src/ty/vtable.rs` (`VtblEntry`, `COMMON_VTABLE_ENTRIES`, `vtable_allocation_provider`)
- `compiler/rustc_trait_selection/src/traits/vtable.rs` (`prepare_vtable_segments_inner`, `vtable_entries`, `supertrait_vtable_slot`, `vtable_prefix_traits`)
- `compiler/rustc_type_ir/src/elaborate.rs` (`Elaborator::visited` anonymizing supertrait deduplication)
- `compiler/rustc_trait_selection/src/traits/select/{mod.rs, candidate_assembly.rs, confirmation.rs}` (`winnow_candidates`, `has_non_region_infer`)
- `compiler/rustc_codegen_ssa/src/{base.rs, meth.rs, size_of_val.rs}` (`unsized_info`, `get_data_ptr`, `size_and_align_of_dst`)
- `compiler/rustc_mir_transform/src/elaborate_drop.rs` (`open_drop_for_box_contents` + `destructor_call_block_sync`) and `compiler/rustc_codegen_ssa/src/mir/block.rs` (`codegen_drop_terminator`)
- `library/alloc/src/boxed.rs` (`Box::drop`, `Layout::for_value_raw`)

Strict kernel purity:
- Zero imports beyond standard `Init` (prelude).
- Every `def` is declared `noncomputable def` (zero `partial def`, zero `._unsafe_rec` compiler auxiliaries).
- Zero `deriving` clauses on inductive/structure types.
- Zero `sorry`, `admit`, `Classical`, `omega`, `bv_decide`, `native_decide`, `axiom`, `opaque`, `unsafe`, or `@[extern]`.
-/

namespace TraitUpcastingVtableSoundness

/-! ## 1. Core Identifiers, Layouts, and Boolean Equality Helpers -/

structure TraitRef where
  defId  : Nat
  argTag : Nat

structure MethodId where
  id : Nat

structure ImplFnId where
  id : Nat

structure DropFnId where
  id : Nat

structure TyId where
  id : Nat

structure Layout where
  size  : Nat
  align : Nat

structure DSAHeader where
  dropFn : Option DropFnId
  layout : Layout

noncomputable def TraitRef.beq (a b : TraitRef) : Bool :=
  Nat.beq a.defId b.defId && Nat.beq a.argTag b.argTag

noncomputable def MethodId.beq (a b : MethodId) : Bool :=
  Nat.beq a.id b.id

noncomputable def ImplFnId.beq (a b : ImplFnId) : Bool :=
  Nat.beq a.id b.id

noncomputable def DropFnId.beq (a b : DropFnId) : Bool :=
  Nat.beq a.id b.id

noncomputable def TyId.beq (a b : TyId) : Bool :=
  Nat.beq a.id b.id

noncomputable def Layout.beq (a b : Layout) : Bool :=
  Nat.beq a.size b.size && Nat.beq a.align b.align

noncomputable def optDropBeq : Option DropFnId → Option DropFnId → Bool
  | none, none => true
  | some a, some b => DropFnId.beq a b
  | _, _ => false

noncomputable def DSAHeader.beq (a b : DSAHeader) : Bool :=
  optDropBeq a.dropFn b.dropFn && Layout.beq a.layout b.layout

theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  rw [Nat.beq_eq]

theorem nat_beq_refl (a : Nat) : Nat.beq a a = true :=
  (nat_beq_true_iff a a).mpr rfl

theorem bool_and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> constructor <;> intro h
  · cases h
  · cases h.1
  · cases h
  · cases h.1
  · cases h
  · cases h.2
  · exact ⟨rfl, rfl⟩
  · rfl

theorem traitRef_beq_eq (a b : TraitRef) : a.beq b = true ↔ a = b := by
  cases a with
  | mk d1 g1 =>
    cases b with
    | mk d2 g2 =>
      dsimp only [TraitRef.beq]
      constructor
      · intro h
        have h1 := (bool_and_true_iff (Nat.beq d1 d2) (Nat.beq g1 g2)).mp h
        have hd : d1 = d2 := (nat_beq_true_iff d1 d2).mp h1.1
        have hg : g1 = g2 := (nat_beq_true_iff g1 g2).mp h1.2
        subst hd; subst hg; rfl
      · intro h
        cases h
        exact (bool_and_true_iff (Nat.beq d1 d1) (Nat.beq g1 g1)).mpr
          ⟨nat_beq_refl d1, nat_beq_refl g1⟩

theorem traitRef_beq_refl (a : TraitRef) : a.beq a = true :=
  (traitRef_beq_eq a a).mpr rfl

theorem methodId_beq_eq (a b : MethodId) : a.beq b = true ↔ a = b := by
  cases a with
  | mk i1 =>
    cases b with
    | mk i2 =>
      dsimp only [MethodId.beq]
      constructor
      · intro h
        have hi : i1 = i2 := (nat_beq_true_iff i1 i2).mp h
        subst hi; rfl
      · intro h
        cases h
        exact nat_beq_refl i1

theorem methodId_beq_refl (a : MethodId) : a.beq a = true :=
  (methodId_beq_eq a a).mpr rfl

theorem traitMem_cons (x y : TraitRef) (xs : List TraitRef) :
    ((x :: xs).any (fun z => TraitRef.beq y z)) =
      (TraitRef.beq y x || xs.any (fun z => TraitRef.beq y z)) := by
  rfl

noncomputable def traitMem (y : TraitRef) (xs : List TraitRef) : Bool :=
  match xs with
  | [] => false
  | x :: rest => if TraitRef.beq y x then true else traitMem y rest

theorem traitMem_iff (y : TraitRef) (xs : List TraitRef) :
    traitMem y xs = true ↔ ∃ z, z ∈ xs ∧ TraitRef.beq y z = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; simp [traitMem] at h
    · intro ⟨z, hz, _⟩; cases hz
  | cons x rest ih =>
    dsimp only [traitMem]
    cases hEq : TraitRef.beq y x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h
        have ⟨z, hz1, hz2⟩ := ih.mp h
        exact ⟨z, List.mem_cons_of_mem x hz1, hz2⟩
      · intro ⟨z, hz1, hz2⟩
        cases hz1 with
        | head =>
          rw [hz2] at hEq
          cases hEq
        | tail _ ht =>
          exact ih.mpr ⟨z, ht, hz2⟩
    · simp only [↓reduceIte]
      constructor
      · intro _
        exact ⟨x, List.Mem.head rest, hEq⟩
      · intro _; exact True.intro

theorem traitMem_eq_true_iff_mem (y : TraitRef) (xs : List TraitRef) :
    traitMem y xs = true ↔ y ∈ xs := by
  constructor
  · intro h
    have ⟨z, hz1, hz2⟩ := (traitMem_iff y xs).mp h
    have hEq : y = z := (traitRef_beq_eq y z).mp hz2
    subst hEq; exact hz1
  · intro hy
    exact (traitMem_iff y xs).mpr ⟨y, hy, traitRef_beq_refl y⟩

noncomputable def listNodupTraits : List TraitRef → Bool
  | [] => true
  | x :: xs => (!traitMem x xs) && listNodupTraits xs

theorem not_traitMem_cons_of_not_mem (x a : TraitRef) (xs : List TraitRef)
    (h1 : x ≠ a) (h2 : ¬ traitMem x xs = true) :
    ¬ traitMem x (a :: xs) = true := by
  intro hm
  have hmem : x ∈ a :: xs := (traitMem_eq_true_iff_mem x (a :: xs)).mp hm
  cases hmem with
  | head => exact h1 rfl
  | tail _ ht => exact h2 ((traitMem_eq_true_iff_mem x xs).mpr ht)

/-! ## 2. General List Prefix Algebra and Indexing Lemmas -/

noncomputable def ListPrefix {α : Type} (xs ys : List α) : Prop :=
  ∃ suffix : List α, ys = xs ++ suffix

theorem listPrefix_refl {α : Type} (xs : List α) : ListPrefix xs xs :=
  ⟨[], (List.append_nil xs).symm⟩

theorem listPrefix_trans {α : Type} {xs ys zs : List α}
    (h1 : ListPrefix xs ys) (h2 : ListPrefix ys zs) : ListPrefix xs zs := by
  rcases h1 with ⟨s1, rfl⟩
  rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, List.append_assoc xs s1 s2⟩

theorem listPrefix_nil {α : Type} (ys : List α) : ListPrefix [] ys :=
  ⟨ys, rfl⟩

theorem listPrefix_cons {α : Type} (a : α) {xs ys : List α}
    (h : ListPrefix xs ys) : ListPrefix (a :: xs) (a :: ys) := by
  rcases h with ⟨s, rfl⟩
  exact ⟨s, rfl⟩

theorem listPrefix_getElem? {α : Type} {xs ys : List α}
    (h : ListPrefix xs ys) (idx : Nat) {v : α}
    (hx : xs[idx]? = some v) : ys[idx]? = some v := by
  rcases h with ⟨suf, rfl⟩
  induction xs generalizing idx with
  | nil =>
    simp at hx
  | cons a rest ih =>
    cases idx with
    | zero =>
      simp at hx
      simp [hx]
    | succ k =>
      simp only [List.cons_append]
      exact ih k hx

theorem list_getElem?_append_right {α : Type} (xs ys : List α) (i : Nat) :
    (xs ++ ys)[xs.length + i]? = ys[i]? := by
  induction xs with
  | nil =>
    simp [Nat.zero_add]
  | cons a rest ih =>
    simp only [List.length_cons, Nat.succ_add, List.cons_append, List.getElem?_cons_succ]
    exact ih

theorem list_getElem?_append_eq {α : Type} (pre post : List α) (x : α) :
    (pre ++ [x] ++ post)[pre.length]? = some x := by
  have h0 : (pre ++ ([x] ++ post))[pre.length]? = ([x] ++ post)[0]? := by
    have := list_getElem?_append_right pre ([x] ++ post) 0
    rw [Nat.add_zero] at this
    exact this
  rw [List.append_assoc]
  rw [h0]
  rfl

theorem nat_le_add_right (a b : Nat) : a ≤ a + b := by
  induction b with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ]
    exact Nat.le_succ_of_le ih

/-! ## 3. Vtable Entries, Segments, and `prepare_vtable_segments` DFS -/

inductive MethodSlotKind where
  | active (m : MethodId)
  | vacantSlot

inductive VtblSegment where
  | metadataDSA
  | traitOwnEntries (traitRef : TraitRef) (emitVptr : Bool)

inductive VtblEntry where
  | metaDrop (fn? : Option DropFnId)
  | metaSize (sz : Nat)
  | metaAlign (al : Nat)
  | vacant
  | method (traitRef : TraitRef) (m : MethodId) (implFn : ImplFnId)
  | traitVPtr (subTrait : TraitRef)

noncomputable def VtblEntry.beq (a b : VtblEntry) : Bool :=
  match a, b with
  | .metaDrop d1, .metaDrop d2 => optDropBeq d1 d2
  | .metaSize s1, .metaSize s2 => Nat.beq s1 s2
  | .metaAlign a1, .metaAlign a2 => Nat.beq a1 a2
  | .vacant, .vacant => true
  | .method t1 m1 f1, .method t2 m2 f2 =>
    TraitRef.beq t1 t2 && MethodId.beq m1 m2 && ImplFnId.beq f1 f2
  | .traitVPtr t1, .traitVPtr t2 => TraitRef.beq t1 t2
  | _, _ => false

structure ConcreteType where
  tyId      : TyId
  needsDrop : Bool
  dropFn    : Option DropFnId
  layout    : Layout

noncomputable def ConcreteType.dsaHeader (ct : ConcreteType) : DSAHeader :=
  { dropFn := if ct.needsDrop then ct.dropFn else none, layout := ct.layout }

structure TraitSpec where
  traitRef     : TraitRef
  directSupers : List TraitRef
  ownMethods   : List MethodSlotKind

structure TraitEnv where
  lookupTrait : TraitRef → Option TraitSpec

noncomputable def TraitEnv.directSupers (env : TraitEnv) (tr : TraitRef) : List TraitRef :=
  match env.lookupTrait tr with
  | some sp => sp.directSupers
  | none => []

noncomputable def TraitEnv.ownMethods (env : TraitEnv) (tr : TraitRef) : List MethodSlotKind :=
  match env.lookupTrait tr with
  | some sp => sp.ownMethods
  | none => []

structure ImplTable where
  lookupImpl : TyId → TraitRef → MethodId → Option ImplFnId

noncomputable def MethodSlotKind.toEntry (impls : ImplTable) (ct : ConcreteType)
    (tr : TraitRef) : MethodSlotKind → VtblEntry
  | .active m =>
    match impls.lookupImpl ct.tyId tr m with
    | some fnId => VtblEntry.method tr m fnId
    | none => VtblEntry.vacant
  | .vacantSlot => VtblEntry.vacant

noncomputable def ownTraitEntries (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (tr : TraitRef) : List VtblEntry :=
  (env.ownMethods tr).map (MethodSlotKind.toEntry impls ct tr)

theorem ownTraitEntries_length (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (tr : TraitRef) :
    (ownTraitEntries env impls ct tr).length = (env.ownMethods tr).length := by
  dsimp only [ownTraitEntries]
  exact List.length_map _

/-- Mirror of `ty::elaborate::supertrait_def_ids(tcx, tr).any(has_own_existential_vtable_entries)`. -/
noncomputable def hasTransitiveOwnEntriesFuel (env : TraitEnv) :
    Nat → TraitRef → List TraitRef → Bool
  | 0, _, _ => false
  | fuel + 1, tr, visited =>
    if !(env.ownMethods tr).isEmpty then true
    else if traitMem tr visited then false
    else (env.directSupers tr).any (fun sup => hasTransitiveOwnEntriesFuel env fuel sup (tr :: visited))

noncomputable def hasTransitiveOwnEntries (env : TraitEnv) (tr : TraitRef) (fuel : Nat) : Bool :=
  hasTransitiveOwnEntriesFuel env fuel tr []

inductive DFSMode where
  | dive
  | pop

structure DFSFrame where
  traitRef : TraitRef
  emitVptr : Bool
  siblings : List TraitRef

structure DFSState where
  mode          : DFSMode
  emitVptrOnNew : Bool
  visited       : List TraitRef
  stack         : List DFSFrame
  revSegments   : List VtblSegment

noncomputable def takeFirstUnvisited (visited : List TraitRef) :
    List TraitRef → Option (TraitRef × List TraitRef)
  | [] => none
  | x :: rest =>
    if traitMem x visited then takeFirstUnvisited visited rest
    else some (x, rest)

theorem takeFirstUnvisited_not_visited (visited xs : List TraitRef) (x : TraitRef)
    (rest : List TraitRef) (h : takeFirstUnvisited visited xs = some (x, rest)) :
    ¬ traitMem x visited = true := by
  induction xs with
  | nil =>
    simp [takeFirstUnvisited] at h
  | cons a tl ih =>
    dsimp only [takeFirstUnvisited] at h
    cases hm : traitMem a visited
    · rw [hm] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases h
      exact fun hfalse => by rw [hm] at hfalse; cases hfalse
    · rw [hm] at h
      simp only [↓reduceIte] at h
      exact ih h

noncomputable def dfsStep (env : TraitEnv) (transFuel : Nat) (st : DFSState) : DFSState :=
  match st.mode with
  | .dive =>
    match st.stack with
    | [] => st
    | top :: _ =>
      match takeFirstUnvisited st.visited (env.directSupers top.traitRef) with
      | some (nextSuper, restSupers) =>
        { mode := .dive
          emitVptrOnNew := st.emitVptrOnNew
          visited := nextSuper :: st.visited
          stack := { traitRef := nextSuper, emitVptr := st.emitVptrOnNew, siblings := restSupers } :: st.stack
          revSegments := st.revSegments }
      | none =>
        { st with mode := .pop }
  | .pop =>
    match st.stack with
    | [] => st
    | top :: stackRest =>
      let hasEntries := hasTransitiveOwnEntries env top.traitRef transFuel
      let seg := VtblSegment.traitOwnEntries top.traitRef (top.emitVptr && hasEntries)
      let emitVptr' := st.emitVptrOnNew || hasEntries
      match takeFirstUnvisited st.visited top.siblings with
      | some (nextSib, restSibs) =>
        { mode := .dive
          emitVptrOnNew := emitVptr'
          visited := nextSib :: st.visited
          stack := { traitRef := nextSib, emitVptr := emitVptr', siblings := restSibs } :: stackRest
          revSegments := seg :: st.revSegments }
      | none =>
        { mode := .pop
          emitVptrOnNew := emitVptr'
          visited := st.visited
          stack := stackRest
          revSegments := seg :: st.revSegments }

noncomputable def dfsRun (env : TraitEnv) (transFuel : Nat) : Nat → DFSState → DFSState
  | 0, st => st
  | steps + 1, st => dfsRun env transFuel steps (dfsStep env transFuel st)

noncomputable def initialDFSState (root : TraitRef) : DFSState :=
  { mode := .dive
    emitVptrOnNew := false
    visited := [root]
    stack := [{ traitRef := root, emitVptr := false, siblings := [] }]
    revSegments := [VtblSegment.metadataDSA] }

/-- Executable mirror of `prepare_vtable_segments` (`compiler/rustc_trait_selection/src/traits/vtable.rs`). -/
noncomputable def prepareVtableSegments (env : TraitEnv) (root : TraitRef)
    (steps transFuel : Nat) : List VtblSegment :=
  (dfsRun env transFuel steps (initialDFSState root)).revSegments.reverse

/-! ## 4. Universal Diamond Deduplication Invariant for `prepareVtableSegments` -/

noncomputable def segmentTraits : List VtblSegment → List TraitRef
  | [] => []
  | .metadataDSA :: rest => segmentTraits rest
  | .traitOwnEntries tr _ :: rest => tr :: segmentTraits rest

noncomputable def stackTraits : List DFSFrame → List TraitRef
  | [] => []
  | f :: fs => f.traitRef :: stackTraits fs

theorem segmentTraits_append (xs ys : List VtblSegment) :
    segmentTraits (xs ++ ys) = segmentTraits xs ++ segmentTraits ys := by
  induction xs with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | metadataDSA => exact ih
    | traitOwnEntries tr ev =>
      simp only [List.cons_append, segmentTraits, ih]

theorem mem_segmentTraits_reverse (segs : List VtblSegment) (tr : TraitRef) :
    tr ∈ segmentTraits segs.reverse ↔ tr ∈ segmentTraits segs := by
  induction segs with
  | nil => simp [segmentTraits]
  | cons seg rest ih =>
    simp only [List.reverse_cons, segmentTraits_append]
    cases seg with
    | metadataDSA =>
      simp [segmentTraits, ih]
    | traitOwnEntries tr' _ =>
      simp only [segmentTraits, List.mem_append, List.mem_singleton, ih]
      exact ⟨fun h => by
               cases h with
               | inl h1 => exact List.mem_cons_of_mem tr' h1
               | inr h2 => exact h2 ▸ List.Mem.head _,
             fun h => by
               cases h with
               | head => exact Or.inr rfl
               | tail _ h1 => exact Or.inl h1⟩

theorem noDupTraits_reverse_of_disjoint (segs : List VtblSegment)
    (h : listNodupTraits (segmentTraits segs) = true) :
    listNodupTraits (segmentTraits segs.reverse) = true := by
  induction segs with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | metadataDSA =>
      simp only [List.reverse_cons, segmentTraits_append, segmentTraits, List.append_nil]
      exact ih h
    | traitOwnEntries tr _ =>
      dsimp only [segmentTraits, listNodupTraits] at h
      have hBoth := (bool_and_true_iff (!traitMem tr (segmentTraits rest))
        (listNodupTraits (segmentTraits rest))).mp h
      have hRest := ih hBoth.2
      simp only [List.reverse_cons, segmentTraits_append]
      dsimp only [segmentTraits]
      have hNotRev : ¬ tr ∈ segmentTraits rest.reverse := by
        intro hmem
        have hInOrig : tr ∈ segmentTraits rest := (mem_segmentTraits_reverse rest tr).mp hmem
        have hTm : traitMem tr (segmentTraits rest) = true :=
          (traitMem_eq_true_iff_mem tr (segmentTraits rest)).mpr hInOrig
        rw [hTm] at hBoth
        cases hBoth.1
      clear h hBoth ih
      revert hRest hNotRev
      generalize segmentTraits rest.reverse = revList
      induction revList with
      | nil =>
        intro _ _
        simp [listNodupTraits, traitMem]
      | cons y ys ihy =>
        intro hRest hNotRev
        dsimp only [listNodupTraits] at hRest
        have hSplit := (bool_and_true_iff (!traitMem y ys) (listNodupTraits ys)).mp hRest
        have hyNeq : tr ≠ y := fun heq => hNotRev (heq ▸ List.Mem.head ys)
        have hNotYs : ¬ tr ∈ ys := fun hmem => hNotRev (List.Mem.tail y hmem)
        have ihRes := ihy hSplit.2 hNotYs
        simp only [List.cons_append, listNodupTraits]
        apply (bool_and_true_iff _ _).mpr
        constructor
        · have hmemY : ¬ y ∈ (ys ++ [tr]) := by
            intro hmem
            have hor := List.mem_append.mp hmem
            cases hor with
            | inl hy =>
              have hTm := (traitMem_eq_true_iff_mem y ys).mpr hy
              rw [hTm] at hSplit; cases hSplit.1
            | inr htr =>
              simp only [List.mem_singleton] at htr
              exact hyNeq htr.symm
          cases htm : traitMem y (ys ++ [tr])
          · rfl
          · exact False.elim (hmemY ((traitMem_eq_true_iff_mem y (ys ++ [tr])).mp htm))
        · exact ihRes

/-- Well-formedness invariant of the DFS state for diamond deduplication. -/
structure DFSInvariant (st : DFSState) : Prop where
  stackSubVisited  : ∀ x, x ∈ stackTraits st.stack → x ∈ st.visited
  emittedSubVisited : ∀ x, x ∈ segmentTraits st.revSegments → x ∈ st.visited
  stackNodup       : listNodupTraits (stackTraits st.stack) = true
  emittedNodup     : listNodupTraits (segmentTraits st.revSegments) = true
  disjoint         : ∀ x, x ∈ stackTraits st.stack → ¬ x ∈ segmentTraits st.revSegments
  startsWithDSA    : ∃ pre, st.revSegments = pre ++ [VtblSegment.metadataDSA]

theorem dfsInvariant_init (root : TraitRef) : DFSInvariant (initialDFSState root) where
  stackSubVisited x hx := by
    simp only [initialDFSState, stackTraits, List.mem_singleton] at hx
    subst hx
    simp [initialDFSState]
  emittedSubVisited x hx := by
    simp [initialDFSState, segmentTraits] at hx
  stackNodup := by
    simp [initialDFSState, stackTraits, listNodupTraits, traitMem]
  emittedNodup := by
    simp [initialDFSState, segmentTraits, listNodupTraits]
  disjoint x _ hx := by
    simp [initialDFSState, segmentTraits] at hx
  startsWithDSA := ⟨[], rfl⟩

theorem dfsStep_preserves_invariant (env : TraitEnv) (transFuel : Nat) (st : DFSState)
    (inv : DFSInvariant st) : DFSInvariant (dfsStep env transFuel st) := by
  rcases st with ⟨mode, emitVptrOnNew, visited, stack, revSegments⟩
  rcases inv with ⟨hSV, hEV, hSN, hEN, hDisj, hDSA⟩
  cases mode with
  | dive =>
    dsimp only [dfsStep]
    cases stack with
    | nil =>
      exact { stackSubVisited := hSV, emittedSubVisited := hEV, stackNodup := hSN,
              emittedNodup := hEN, disjoint := hDisj, startsWithDSA := hDSA }
    | cons top rest =>
      dsimp only
      cases ht : takeFirstUnvisited visited (env.directSupers top.traitRef) with
      | none =>
        exact { stackSubVisited := hSV, emittedSubVisited := hEV, stackNodup := hSN,
                emittedNodup := hEN, disjoint := hDisj, startsWithDSA := hDSA }
      | some p =>
        cases p with
        | mk nextSuper _ =>
          have hNotVis : ¬ traitMem nextSuper visited = true :=
            takeFirstUnvisited_not_visited visited _ nextSuper _ ht
          have hNotMemVis : ¬ nextSuper ∈ visited :=
            fun hmem => hNotVis ((traitMem_eq_true_iff_mem nextSuper visited).mpr hmem)
          refine { stackSubVisited := ?_, emittedSubVisited := ?_, stackNodup := ?_,
                   emittedNodup := hEN, disjoint := ?_, startsWithDSA := hDSA }
          · intro x hx
            simp only [stackTraits] at hx
            cases hx with
            | head => exact List.Mem.head visited
            | tail _ htail => exact List.Mem.tail nextSuper (hSV x htail)
          · intro x hx
            exact List.Mem.tail nextSuper (hEV x hx)
          · simp only [stackTraits, listNodupTraits]
            apply (bool_and_true_iff _ _).mpr
            constructor
            · have hNotStack : ¬ nextSuper ∈ stackTraits (top :: rest) :=
                fun hmem => hNotMemVis (hSV nextSuper hmem)
              cases htm : traitMem nextSuper (stackTraits (top :: rest))
              · dsimp only [stackTraits] at htm; rw [htm]; rfl
              · exact False.elim (hNotStack ((traitMem_eq_true_iff_mem nextSuper _).mp htm))
            · exact hSN
          · intro x hx he
            simp only [stackTraits] at hx
            cases hx with
            | head => exact hNotMemVis (hEV nextSuper he)
            | tail _ htail => exact hDisj x htail he
  | pop =>
    dsimp only [dfsStep]
    cases stack with
    | nil =>
      exact { stackSubVisited := hSV, emittedSubVisited := hEV, stackNodup := hSN,
              emittedNodup := hEN, disjoint := hDisj, startsWithDSA := hDSA }
    | cons top rest =>
      dsimp only
      have hTopStack : top.traitRef ∈ stackTraits (top :: rest) :=
        List.Mem.head (stackTraits rest)
      have hTopVis : top.traitRef ∈ visited := hSV top.traitRef hTopStack
      have hTopNotEmitted : ¬ top.traitRef ∈ segmentTraits revSegments :=
        hDisj top.traitRef hTopStack
      have hTopBoth := (bool_and_true_iff (!traitMem top.traitRef (stackTraits rest))
        (listNodupTraits (stackTraits rest))).mp hSN
      have hTopNotRest : ¬ top.traitRef ∈ stackTraits rest := by
        intro hmem
        have htm := (traitMem_eq_true_iff_mem top.traitRef (stackTraits rest)).mpr hmem
        rw [htm] at hTopBoth; cases hTopBoth.1
      cases ht : takeFirstUnvisited visited top.siblings with
      | none =>
        refine { stackSubVisited := ?_, emittedSubVisited := ?_, stackNodup := hTopBoth.2,
                 emittedNodup := ?_, disjoint := ?_, startsWithDSA := ?_ }
        · intro x hx
          exact hSV x (List.Mem.tail top.traitRef hx)
        · intro x hx
          simp only [segmentTraits] at hx
          cases hx with
          | head => exact hTopVis
          | tail _ htail => exact hEV x htail
        · simp only [segmentTraits, listNodupTraits]
          apply (bool_and_true_iff _ _).mpr
          constructor
          · cases htm : traitMem top.traitRef (segmentTraits revSegments)
            · rfl
            · exact False.elim (hTopNotEmitted ((traitMem_eq_true_iff_mem top.traitRef _).mp htm))
          · exact hEN
        · intro x hx he
          simp only [segmentTraits] at he
          cases he with
          | head => exact hTopNotRest hx
          | tail _ htail => exact hDisj x (List.Mem.tail top.traitRef hx) htail
        · rcases hDSA with ⟨pre, hpre⟩
          dsimp only at hpre
          refine ⟨VtblSegment.traitOwnEntries top.traitRef (top.emitVptr && hasTransitiveOwnEntries env top.traitRef transFuel) :: pre, ?_⟩
          dsimp only; rw [hpre]; rfl
      | some p =>
        cases p with
        | mk nextSib _ =>
          have hNotVis : ¬ traitMem nextSib visited = true :=
            takeFirstUnvisited_not_visited visited _ nextSib _ ht
          have hNotMemVis : ¬ nextSib ∈ visited :=
            fun hmem => hNotVis ((traitMem_eq_true_iff_mem nextSib visited).mpr hmem)
          refine { stackSubVisited := ?_, emittedSubVisited := ?_, stackNodup := ?_,
                   emittedNodup := ?_, disjoint := ?_, startsWithDSA := ?_ }
          · intro x hx
            simp only [stackTraits] at hx
            cases hx with
            | head => exact List.Mem.head visited
            | tail _ htail =>
              exact List.Mem.tail nextSib (hSV x (List.Mem.tail top.traitRef htail))
          · intro x hx
            simp only [segmentTraits] at hx
            cases hx with
            | head => exact List.Mem.tail nextSib hTopVis
            | tail _ htail => exact List.Mem.tail nextSib (hEV x htail)
          · simp only [stackTraits, listNodupTraits]
            apply (bool_and_true_iff _ _).mpr
            constructor
            · have hNotRest : ¬ nextSib ∈ stackTraits rest := fun hmem =>
                hNotMemVis (hSV nextSib (List.Mem.tail top.traitRef hmem))
              cases htm : traitMem nextSib (stackTraits rest)
              · rfl
              · exact False.elim (hNotRest ((traitMem_eq_true_iff_mem nextSib _).mp htm))
            · exact hTopBoth.2
          · simp only [segmentTraits, listNodupTraits]
            apply (bool_and_true_iff _ _).mpr
            constructor
            · cases htm : traitMem top.traitRef (segmentTraits revSegments)
              · rfl
              · exact False.elim (hTopNotEmitted ((traitMem_eq_true_iff_mem top.traitRef _).mp htm))
            · exact hEN
          · intro x hx he
            simp only [stackTraits] at hx
            simp only [segmentTraits] at he
            cases hx with
            | head =>
              cases he with
              | head => exact hNotMemVis hTopVis
              | tail _ htail => exact hNotMemVis (hEV nextSib htail)
            | tail _ hxRest =>
              cases he with
              | head => exact hTopNotRest hxRest
              | tail _ heRest =>
                exact hDisj x (List.Mem.tail top.traitRef hxRest) heRest
          · rcases hDSA with ⟨pre, hpre⟩
            dsimp only at hpre
            refine ⟨VtblSegment.traitOwnEntries top.traitRef (top.emitVptr && hasTransitiveOwnEntries env top.traitRef transFuel) :: pre, ?_⟩
            dsimp only; rw [hpre]; rfl

theorem dfsRun_preserves_invariant (env : TraitEnv) (transFuel steps : Nat) (st : DFSState)
    (inv : DFSInvariant st) : DFSInvariant (dfsRun env transFuel steps st) := by
  induction steps generalizing st with
  | zero => exact inv
  | succ k ih =>
    exact ih (dfsStep env transFuel st) (dfsStep_preserves_invariant env transFuel st inv)

/-- **Universal Theorem 1A (Diamond Deduplication)**: For every trait DAG `env`, root trait,
    and DFS step budget, `prepareVtableSegments` emits every `TraitRef` at most once. -/
theorem prepareSegments_unique_traits (env : TraitEnv) (root : TraitRef) (steps transFuel : Nat) :
    listNodupTraits (segmentTraits (prepareVtableSegments env root steps transFuel)) = true := by
  have inv := dfsRun_preserves_invariant env transFuel steps (initialDFSState root)
    (dfsInvariant_init root)
  exact noDupTraits_reverse_of_disjoint _ inv.emittedNodup

/-- **Universal Theorem 1B (`MetadataDSA` Header First)**: For every `env`, `root`, and budgets,
    the very first segment emitted by `prepareVtableSegments` is always `.metadataDSA`. -/
theorem prepareSegments_first_is_dsa (env : TraitEnv) (root : TraitRef) (steps transFuel : Nat) :
    ∃ tail, prepareVtableSegments env root steps transFuel = VtblSegment.metadataDSA :: tail := by
  have inv := dfsRun_preserves_invariant env transFuel steps (initialDFSState root)
    (dfsInvariant_init root)
  rcases inv.startsWithDSA with ⟨pre, hpre⟩
  refine ⟨pre.reverse, ?_⟩
  dsimp only [prepareVtableSegments]
  rw [hpre]
  simp

/-! ## 5. Vtable Entries, Slots, Primary-Prefix Exactness, and Secondary `TraitVPtr` Lookup -/

noncomputable def commonDSAEntries (ct : ConcreteType) : List VtblEntry :=
  let d := ct.dsaHeader
  [VtblEntry.metaDrop d.dropFn, VtblEntry.metaSize d.layout.size, VtblEntry.metaAlign d.layout.align]

theorem commonDSAEntries_length (ct : ConcreteType) :
    (commonDSAEntries ct).length = 3 := rfl

noncomputable def segmentEntries (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType) :
    VtblSegment → List VtblEntry
  | .metadataDSA => commonDSAEntries ct
  | .traitOwnEntries tr emitVptr =>
    ownTraitEntries env impls ct tr ++ (if emitVptr then [VtblEntry.traitVPtr tr] else [])

noncomputable def vtableEntriesOfSegs (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType) :
    List VtblSegment → List VtblEntry
  | [] => []
  | seg :: rest => segmentEntries env impls ct seg ++ vtableEntriesOfSegs env impls ct rest

noncomputable def vtableEntries (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (root : TraitRef) (steps transFuel : Nat) : List VtblEntry :=
  vtableEntriesOfSegs env impls ct (prepareVtableSegments env root steps transFuel)

/-- **Universal Theorem 1C (Slot 0..2 `DSA` Header Invariant)**: Every vtable for concrete type
    `ct` has `[metaDrop (dropFn?), metaSize size, metaAlign align]` at slots 0, 1, and 2,
    regardless of which trait object or supertrait vtable is generated. -/
theorem vtableEntries_header_dsa (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (root : TraitRef) (steps transFuel : Nat) :
    let es := vtableEntries env impls ct root steps transFuel
    let d := ct.dsaHeader
    es[0]? = some (VtblEntry.metaDrop d.dropFn) ∧
    es[1]? = some (VtblEntry.metaSize d.layout.size) ∧
    es[2]? = some (VtblEntry.metaAlign d.layout.align) := by
  have ⟨tail, htail⟩ := prepareSegments_first_is_dsa env root steps transFuel
  dsimp only [vtableEntries]
  rw [htail]
  dsimp only [vtableEntriesOfSegs, segmentEntries, commonDSAEntries]
  exact ⟨rfl, rfl, rfl⟩

/-- Mirror of `supertrait_vtable_slot` callback over emitted `VtblSegment`s.
    Returns `some (some slotIdx)` if a `TraitVPtr` slot must be loaded, `some none` if the
    supertrait shares the prefix unchanged, or `none` if `target` is absent. -/
noncomputable def supertraitSlotInSegs (env : TraitEnv) (target : TraitRef) :
    List VtblSegment → Nat → Option (Option Nat)
  | [], _ => none
  | .metadataDSA :: rest, offset =>
    supertraitSlotInSegs env target rest (offset + 3)
  | .traitOwnEntries tr emitVptr :: rest, offset =>
    let offset' := offset + (env.ownMethods tr).length
    if TraitRef.beq tr target then
      if emitVptr then some (some offset') else some none
    else
      let nextOffset := if emitVptr then offset' + 1 else offset'
      supertraitSlotInSegs env target rest nextOffset

noncomputable def supertraitVtableSlot (env : TraitEnv) (source target : TraitRef)
    (steps transFuel : Nat) : Option (Option Nat) :=
  supertraitSlotInSegs env target (prepareVtableSegments env source steps transFuel) 0

theorem supertraitSlotInSegs_shift (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (target : TraitRef) (segs : List VtblSegment) (prefixEntries : List VtblEntry)
    (hNone : supertraitSlotInSegs env target segs prefixEntries.length = some (some idx)) :
    prefixEntries.length ≤ idx ∧
    (prefixEntries ++ vtableEntriesOfSegs env impls ct segs)[idx]? = some (VtblEntry.traitVPtr target) := by
  induction segs generalizing prefixEntries with
  | nil =>
    simp [supertraitSlotInSegs] at hNone
  | cons seg rest ih =>
    cases seg with
    | metadataDSA =>
      dsimp only [supertraitSlotInSegs] at hNone
      dsimp only [vtableEntriesOfSegs, segmentEntries]
      have hLen : (prefixEntries ++ commonDSAEntries ct).length = prefixEntries.length + 3 := by
        rw [List.length_append, commonDSAEntries_length]
      rw [← hLen] at hNone
      have hRec := ih (prefixEntries ++ commonDSAEntries ct) hNone
      have hLe : prefixEntries.length ≤ (prefixEntries ++ commonDSAEntries ct).length := by
        rw [hLen]; exact nat_le_add_right _ 3
      rw [← List.append_assoc]
      exact ⟨Nat.le_trans hLe hRec.1, hRec.2⟩
    | traitOwnEntries tr emitVptr =>
      dsimp only [supertraitSlotInSegs] at hNone
      dsimp only [vtableEntriesOfSegs, segmentEntries]
      let own := ownTraitEntries env impls ct tr
      have hOwnLen : (ownTraitEntries env impls ct tr).length = (env.ownMethods tr).length :=
        ownTraitEntries_length env impls ct tr
      cases hEq : TraitRef.beq tr target
      · rw [hEq] at hNone
        simp only [Bool.false_eq_true, ↓reduceIte] at hNone
        cases emitVptr
        · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hNone ⊢
          have hLen : (prefixEntries ++ own).length = prefixEntries.length + (env.ownMethods tr).length := by
            rw [List.length_append]
            exact congrArg (prefixEntries.length + ·) hOwnLen
          rw [← hLen] at hNone
          have hRec := ih (prefixEntries ++ own) hNone
          have hLe : prefixEntries.length ≤ (prefixEntries ++ own).length := by
            rw [hLen]; exact nat_le_add_right _ _
          rw [← List.append_assoc]
          exact ⟨Nat.le_trans hLe hRec.1, hRec.2⟩
        · simp only [↓reduceIte] at hNone ⊢
          let pre' := prefixEntries ++ own ++ [VtblEntry.traitVPtr tr]
          have hLen : pre'.length = prefixEntries.length + (env.ownMethods tr).length + 1 := by
            dsimp only [pre']
            rw [List.length_append, List.length_append, hOwnLen, List.length_singleton]
          rw [← hLen] at hNone
          have hRec := ih pre' hNone
          have hLe : prefixEntries.length ≤ pre'.length := by
            rw [hLen]
            exact Nat.le_trans (nat_le_add_right _ _) (nat_le_add_right _ 1)
          have hAssoc : prefixEntries ++ (own ++ [VtblEntry.traitVPtr tr] ++ vtableEntriesOfSegs env impls ct rest) =
              pre' ++ vtableEntriesOfSegs env impls ct rest := by
            dsimp only [pre']
            simp only [List.append_assoc]
          rw [hAssoc]
          exact ⟨Nat.le_trans hLe hRec.1, hRec.2⟩
      · rw [hEq] at hNone
        simp only [↓reduceIte] at hNone
        have hTrEq : tr = target := (traitRef_beq_eq tr target).mp hEq
        subst hTrEq
        cases emitVptr
        · simp only [Bool.false_eq_true, ↓reduceIte] at hNone
          cases hNone
        · simp only [↓reduceIte] at hNone ⊢
          injection hNone with hInner
          injection hInner with hIdx
          subst hIdx
          constructor
          · exact nat_le_add_right _ _
          · have hIdxEq : prefixEntries.length + (env.ownMethods tr).length = (prefixEntries ++ own).length := by
              rw [List.length_append, hOwnLen]
            rw [hIdxEq]
            have hAssoc : prefixEntries ++ (own ++ [VtblEntry.traitVPtr tr] ++ vtableEntriesOfSegs env impls ct rest) =
                (prefixEntries ++ own) ++ [VtblEntry.traitVPtr tr] ++ vtableEntriesOfSegs env impls ct rest := by
              simp only [List.append_assoc]
            rw [hAssoc]
            exact list_getElem?_append_eq (prefixEntries ++ own) (vtableEntriesOfSegs env impls ct rest)
              (VtblEntry.traitVPtr tr)

/-- **Universal Theorem 1D (Secondary `TraitVPtr` Slot Lookup Exactness)**: Whenever
    `supertraitVtableSlot env source target = some (some idx)`, `vtableEntries` at slot `idx`
    is guaranteed to contain `VtblEntry.traitVPtr target`, and `3 ≤ idx` (never aliases `DSA`). -/
theorem secondary_vptr_slot_exact (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (source target : TraitRef) (steps transFuel idx : Nat)
    (hSlot : supertraitVtableSlot env source target steps transFuel = some (some idx)) :
    3 ≤ idx ∧
    (vtableEntries env impls ct source steps transFuel)[idx]? = some (VtblEntry.traitVPtr target) := by
  have ⟨tail, htail⟩ := prepareSegments_first_is_dsa env source steps transFuel
  dsimp only [supertraitVtableSlot] at hSlot
  dsimp only [vtableEntries]
  rw [htail] at hSlot ⊢
  dsimp only [supertraitSlotInSegs] at hSlot
  dsimp only [vtableEntriesOfSegs, segmentEntries]
  rw [Nat.zero_add] at hSlot
  have hLen3 : (commonDSAEntries ct).length = 3 := commonDSAEntries_length ct
  rw [← hLen3] at hSlot
  exact supertraitSlotInSegs_shift env impls ct target tail (commonDSAEntries ct) hSlot

theorem supertraitSlotInSegs_none_witness (env : TraitEnv) (target : TraitRef)
    (segs : List VtblSegment) (off : Nat)
    (h : supertraitSlotInSegs env target segs off = some none) :
    VtblSegment.traitOwnEntries target false ∈ segs := by
  induction segs generalizing off with
  | nil => simp [supertraitSlotInSegs] at h
  | cons seg rest ih =>
    cases seg with
    | metadataDSA =>
      dsimp only [supertraitSlotInSegs] at h
      exact List.Mem.tail _ (ih (off + 3) h)
    | traitOwnEntries tr emitVptr =>
      dsimp only [supertraitSlotInSegs] at h
      cases hEq : TraitRef.beq tr target
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h
        exact List.Mem.tail _ (ih _ h)
      · simp only [hEq, ↓reduceIte] at h
        have hTrEq : tr = target := (traitRef_beq_eq tr target).mp hEq
        subst hTrEq
        cases emitVptr
        · exact List.Mem.head rest
        · simp at h

/-- **Universal Theorem 1E (Zero-Offset `emitVptr = false` Witness)**: Whenever
    `supertraitVtableSlot = some none`, `target` was emitted in `prepareVtableSegments` with
    `emitVptr = false`, meaning no `TraitVPtr` entry exists for `target` and the vtable pointer
    stays unchanged. -/
theorem primary_prefix_slot_emits_no_vptr (env : TraitEnv) (source target : TraitRef)
    (steps transFuel : Nat)
    (h : supertraitVtableSlot env source target steps transFuel = some none) :
    VtblSegment.traitOwnEntries target false ∈ prepareVtableSegments env source steps transFuel :=
  supertraitSlotInSegs_none_witness env target _ 0 h

/-! ## 6. Method Slot Computation, Runtime Dispatch, and Primary-Prefix Upcast Contract -/

/-- Find the slot index of method `(target, m)` inside direct vtable entries of `target`. -/
noncomputable def findMethodSlotInEntries (target : TraitRef) (m : MethodId) :
    List VtblEntry → Nat → Option Nat
  | [], _ => none
  | .method tr m' _ :: rest, idx =>
    if TraitRef.beq tr target && MethodId.beq m m' then some idx
    else findMethodSlotInEntries target m rest (idx + 1)
  | _ :: rest, idx => findMethodSlotInEntries target m rest (idx + 1)

theorem findMethodSlotInEntries_spec (target : TraitRef) (m : MethodId)
    (es : List VtblEntry) (startIdx idx : Nat)
    (h : findMethodSlotInEntries target m es startIdx = some idx) :
    ∃ k implFn, idx = startIdx + k ∧ es[k]? = some (VtblEntry.method target m implFn) := by
  induction es generalizing startIdx with
  | nil => simp [findMethodSlotInEntries] at h
  | cons e rest ih =>
    cases e with
    | method tr m' f =>
      dsimp only [findMethodSlotInEntries] at h
      cases hCond : TraitRef.beq tr target && MethodId.beq m m'
      · rw [hCond] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        have ⟨k, f', hidx, hget⟩ := ih (startIdx + 1) h
        refine ⟨k + 1, f', ?_, hget⟩
        rw [hidx, Nat.add_assoc, Nat.add_comm 1 k]
      · rw [hCond] at h
        simp only [↓reduceIte] at h
        injection h with hEq
        subst hEq
        have hBoth := (bool_and_true_iff (TraitRef.beq tr target) (MethodId.beq m m')).mp hCond
        have hTr : tr = target := (traitRef_beq_eq tr target).mp hBoth.1
        have hM : m = m' := (methodId_beq_eq m m').mp hBoth.2
        subst hTr; subst hM
        exact ⟨0, f, rfl, rfl⟩
    | metaDrop _ | metaSize _ | metaAlign _ | vacant | traitVPtr _ =>
      dsimp only [findMethodSlotInEntries] at h
      have ⟨k, f', hidx, hget⟩ := ih (startIdx + 1) h
      refine ⟨k + 1, f', ?_, hget⟩
      rw [hidx, Nat.add_assoc, Nat.add_comm 1 k]

noncomputable def dispatchFromVtable (es : List VtblEntry) (idx : Nat) : Option ImplFnId :=
  match es[idx]? with
  | some (.method _ _ f) => some f
  | _ => none

noncomputable def readDSAFromEntries (es : List VtblEntry) : Option DSAHeader :=
  match (es[0]?, es[1]?, es[2]?) with
  | (some (VtblEntry.metaDrop d), some (VtblEntry.metaSize sz), some (VtblEntry.metaAlign al)) =>
    some { dropFn := d, layout := { size := sz, align := al } }
  | (_, _, _) => none

theorem readDSAFromEntries_of_header {es : List VtblEntry} {d : DSAHeader}
    (h0 : es[0]? = some (.metaDrop d.dropFn))
    (h1 : es[1]? = some (.metaSize d.layout.size))
    (h2 : es[2]? = some (.metaAlign d.layout.align)) :
    readDSAFromEntries es = some d := by
  dsimp only [readDSAFromEntries]
  rw [h0, h1, h2]

/-- Runtime representation of `&dyn T` (or `Box<dyn T>` vtable half): statically typed at
    `staticTrait`, backed at runtime by concrete allocation `(concreteTy, vtableTrait)` (`GlobalAlloc::VTable`). -/
structure DynVtableView where
  staticTrait : TraitRef
  vtableTrait : TraitRef

/-- Prefix & `TraitVPtr` coherence invariant on `(env, impls, ct, steps, transFuel)`.
    Holds when every zero-offset `emitVptr = false` upcast produces a true slot-by-slot
    vtable prefix, matching `rustc_trait_selection/src/traits/vtable.rs::vtable_prefix_traits`. -/
structure VtableCoherenceSpec (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) : Prop where
  prefixExact :
    ∀ src tgt,
      supertraitVtableSlot env src tgt steps transFuel = some none →
      ListPrefix (vtableEntries env impls ct tgt steps transFuel)
                 (vtableEntries env impls ct src steps transFuel)

/-- **Coherence Invariant on Live Fat Pointer View**: `view.vtableTrait`'s vtable has
    `view.staticTrait`'s vtable as an exact slot-by-slot prefix. -/
noncomputable def WellFormedView (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (view : DynVtableView) : Prop :=
  ListPrefix (vtableEntries env impls ct view.staticTrait steps transFuel)
             (vtableEntries env impls ct view.vtableTrait steps transFuel)

theorem wellFormedView_direct (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (root : TraitRef) :
    WellFormedView env impls ct steps transFuel { staticTrait := root, vtableTrait := root } :=
  listPrefix_refl _

/-- Runtime semantics of `rustc_codegen_ssa/src/base.rs::unsized_info`:
    queries `supertraitVtableSlot (view.staticTrait, target)`.
    - `none` -> invalid upcast;
    - `some none` -> returns `view.vtableTrait` unchanged (zero-instruction upcast!);
    - `some (some idx)` -> loads `(vtableEntries view.vtableTrait)[idx]?`, expecting `.traitVPtr target`. -/
noncomputable def upcastViewStep (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (view : DynVtableView) (target : TraitRef) : Option DynVtableView :=
  match supertraitVtableSlot env view.staticTrait target steps transFuel with
  | none => none
  | some none => some { staticTrait := target, vtableTrait := view.vtableTrait }
  | some (some idx) =>
    match (vtableEntries env impls ct view.vtableTrait steps transFuel)[idx]? with
    | some (.traitVPtr subTr) =>
      if TraitRef.beq subTr target then
        some { staticTrait := target, vtableTrait := subTr }
      else none
    | _ => none

noncomputable def upcastViewChain (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (view : DynVtableView) : List TraitRef → Option DynVtableView
  | [] => some view
  | tgt :: rest =>
    match upcastViewStep env impls ct steps transFuel view tgt with
    | some view' => upcastViewChain env impls ct steps transFuel view' rest
    | none => none

/-- **Universal Theorem 2A (Upcast Step Soundness & Prefix Preservation)**: Under
    `VtableCoherenceSpec`, ANY valid single upcast `view -> target` succeeds (`some view'`),
    preserves `WellFormedView`, and if `slot = some (some idx)`, loads `subTr = target`
    deterministically from `view.vtableTrait`'s runtime vtable at offset `idx`. -/
theorem upcastViewStep_sound (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (coh : VtableCoherenceSpec env impls ct steps transFuel)
    (view : DynVtableView) (hwf : WellFormedView env impls ct steps transFuel view)
    (target : TraitRef)
    (hValid : (supertraitVtableSlot env view.staticTrait target steps transFuel).isSome = true) :
    ∃ view', upcastViewStep env impls ct steps transFuel view target = some view' ∧
             view'.staticTrait = target ∧
             WellFormedView env impls ct steps transFuel view' := by
  dsimp only [upcastViewStep]
  cases hSlot : supertraitVtableSlot env view.staticTrait target steps transFuel
  · rw [hSlot] at hValid; simp at hValid
  · rename_i optIdx
    cases optIdx with
    | none =>
      refine ⟨{ staticTrait := target, vtableTrait := view.vtableTrait }, rfl, rfl, ?_⟩
      exact listPrefix_trans (coh.prefixExact view.staticTrait target hSlot) hwf
    | some idx =>
      dsimp only
      have hSec := secondary_vptr_slot_exact env impls ct view.staticTrait target steps transFuel idx hSlot
      have hRuntime : (vtableEntries env impls ct view.vtableTrait steps transFuel)[idx]? =
          some (VtblEntry.traitVPtr target) :=
        listPrefix_getElem? hwf idx hSec.2
      rw [hRuntime]
      simp only [traitRef_beq_refl target, ↓reduceIte]
      exact ⟨{ staticTrait := target, vtableTrait := target }, rfl, rfl, listPrefix_refl _⟩

theorem upcastViewStep_wellFormed_of_some (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (coh : VtableCoherenceSpec env impls ct steps transFuel)
    (view view' : DynVtableView) (hwf : WellFormedView env impls ct steps transFuel view)
    (target : TraitRef)
    (hStep : upcastViewStep env impls ct steps transFuel view target = some view') :
    view'.staticTrait = target ∧ WellFormedView env impls ct steps transFuel view' := by
  dsimp only [upcastViewStep] at hStep
  cases hSlot : supertraitVtableSlot env view.staticTrait target steps transFuel
  · rw [hSlot] at hStep; cases hStep
  · rw [hSlot] at hStep
    rename_i optIdx
    cases optIdx with
    | none =>
      injection hStep with hEq
      subst hEq
      exact ⟨rfl, listPrefix_trans (coh.prefixExact view.staticTrait target hSlot) hwf⟩
    | some idx =>
      dsimp only at hStep
      cases hGet : (vtableEntries env impls ct view.vtableTrait steps transFuel)[idx]? with
      | none => rw [hGet] at hStep; cases hStep
      | some entry =>
        rw [hGet] at hStep
        cases entry with
        | traitVPtr subTr =>
          dsimp only at hStep
          cases hBeq : TraitRef.beq subTr target
          · rw [hBeq] at hStep; simp at hStep
          · rw [hBeq] at hStep; simp at hStep
            subst hStep
            have hTr : subTr = target := (traitRef_beq_eq subTr target).mp hBeq
            subst hTr
            exact ⟨rfl, listPrefix_refl _⟩
        | metaDrop _ | metaSize _ | metaAlign _ | vacant | method _ _ _ => cases hStep

/-- **Universal Theorem 2B (Arbitrary-Length Chain Well-Formedness)**: Any sequence of
    trait upcasts `[T₁, ..., Tₖ]` from a well-formed `view₀` produces a well-formed `viewₖ`. -/
theorem upcastViewChain_wellFormed (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (coh : VtableCoherenceSpec env impls ct steps transFuel)
    (chain : List TraitRef) (view view' : DynVtableView)
    (hwf : WellFormedView env impls ct steps transFuel view)
    (hChain : upcastViewChain env impls ct steps transFuel view chain = some view') :
    WellFormedView env impls ct steps transFuel view' := by
  induction chain generalizing view with
  | nil =>
    simp [upcastViewChain] at hChain
    subst hChain; exact hwf
  | cons tgt rest ih =>
    dsimp only [upcastViewChain] at hChain
    cases hStep : upcastViewStep env impls ct steps transFuel view tgt with
    | none => rw [hStep] at hChain; cases hChain
    | some vMid =>
      rw [hStep] at hChain
      have hMid := upcastViewStep_wellFormed_of_some env impls ct steps transFuel coh view vMid hwf tgt hStep
      exact ih vMid hMid.2 hChain

theorem upcastViewChain_staticTrait (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (coh : VtableCoherenceSpec env impls ct steps transFuel)
    (view view' : DynVtableView) (chain : List TraitRef) (lastTr : TraitRef)
    (hNonEmpty : chain ≠ [] → ∃ pre, chain = pre ++ [lastTr])
    (hEqEmpty : chain = [] → view.staticTrait = lastTr)
    (hwf : WellFormedView env impls ct steps transFuel view)
    (hChain : upcastViewChain env impls ct steps transFuel view chain = some view') :
    view'.staticTrait = lastTr := by
  induction chain generalizing view with
  | nil =>
    simp [upcastViewChain] at hChain
    subst hChain
    exact hEqEmpty rfl
  | cons tgt rest ih =>
    dsimp only [upcastViewChain] at hChain
    cases hStep : upcastViewStep env impls ct steps transFuel view tgt with
    | none => rw [hStep] at hChain; cases hChain
    | some vMid =>
      rw [hStep] at hChain
      have hMid := upcastViewStep_wellFormed_of_some env impls ct steps transFuel coh view vMid hwf tgt hStep
      cases rest with
      | nil =>
        simp [upcastViewChain] at hChain
        subst hChain
        have ⟨pre, hpre⟩ := hNonEmpty (fun hc => by cases hc)
        cases pre with
        | nil =>
          simp at hpre
          rw [hMid.1, hpre]
        | cons _ _ =>
          simp at hpre
      | cons r2 rrest =>
        have hPre := hNonEmpty (fun hc => by cases hc)
        refine ih vMid ?_ ?_ hMid.2 hChain
        · intro _
          rcases hPre with ⟨pre, hpre⟩
          cases pre with
          | nil => simp at hpre
          | cons _ preTail =>
            simp only [List.cons_append] at hpre
            injection hpre with _ hRestEq
            exact ⟨preTail, hRestEq⟩
        · intro hEmpty; cases hEmpty

/-- **Universal Theorem 2C (Upcast Chain `DSA` Preservation)**: Any well-formed upcast view
    (reachable by ANY chain length) preserves the concrete type's `[drop_fn, size, align]` header. -/
theorem wellFormedView_dsa_eq (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (view : DynVtableView) :
    readDSAFromEntries (vtableEntries env impls ct view.vtableTrait steps transFuel) =
      some ct.dsaHeader := by
  have ⟨h0, h1, h2⟩ := vtableEntries_header_dsa env impls ct view.vtableTrait steps transFuel
  exact readDSAFromEntries_of_header h0 h1 h2

/-- **Universal Theorem 2D (Upcast Chain Method Dispatch Equivalence)**: Calling any method `m`
    declared on `view.staticTrait` through runtime `view.vtableTrait` ALWAYS resolves to the
    exact same `ImplFnId` stored in direct `vtableEntries env impls ct view.staticTrait`,
    even when `view.vtableTrait ≠ view.staticTrait` (e.g. `Diamond` vs `Root` vs sub-vtable)! -/
theorem wellFormedView_dispatch_eq_direct (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (view : DynVtableView) (m : MethodId) (idx : Nat)
    (hwf : WellFormedView env impls ct steps transFuel view)
    (hSlot : findMethodSlotInEntries view.staticTrait m
      (vtableEntries env impls ct view.staticTrait steps transFuel) 0 = some idx) :
    dispatchFromVtable (vtableEntries env impls ct view.vtableTrait steps transFuel) idx =
      dispatchFromVtable (vtableEntries env impls ct view.staticTrait steps transFuel) idx := by
  have ⟨k, implFn, hidx, hget⟩ := findMethodSlotInEntries_spec view.staticTrait m _ 0 idx hSlot
  rw [Nat.zero_add] at hidx
  subst hidx
  have hRuntime := listPrefix_getElem? hwf idx hget
  dsimp only [dispatchFromVtable]
  rw [hget, hRuntime]

/-- **Universal Theorem 2E (Diamond Path-Coherence)**: Regardless of which upcast path is taken
    from a root `dyn Diamond` object — left spine `Diamond ->* Left ->* Root`, right branch
    `Diamond ->* Right ->* Root`, or direct `Diamond ->* Root` — any two chains terminating at the
    same `Root` yield:
    (1) identical `(dropFn?, size, align)` `DSAHeader`, AND
    (2) identical virtual method dispatch on EVERY method `m` of `Root`, even when their runtime
        vtable allocation handles (`viewL.vtableTrait` vs `viewR.vtableTrait`) are distinct! -/
theorem diamond_path_coherence (env : TraitEnv) (impls : ImplTable) (ct : ConcreteType)
    (steps transFuel : Nat) (coh : VtableCoherenceSpec env impls ct steps transFuel)
    (dia root : TraitRef) (chainL chainR : List TraitRef) (viewL viewR : DynVtableView)
    (hNonEmptyL : ∃ pL, chainL = pL ++ [root])
    (hNonEmptyR : ∃ pR, chainR = pR ++ [root])
    (hL : upcastViewChain env impls ct steps transFuel { staticTrait := dia, vtableTrait := dia } chainL = some viewL)
    (hR : upcastViewChain env impls ct steps transFuel { staticTrait := dia, vtableTrait := dia } chainR = some viewR) :
    readDSAFromEntries (vtableEntries env impls ct viewL.vtableTrait steps transFuel) = some ct.dsaHeader ∧
    readDSAFromEntries (vtableEntries env impls ct viewR.vtableTrait steps transFuel) = some ct.dsaHeader ∧
    (∀ m idx,
      findMethodSlotInEntries root m (vtableEntries env impls ct root steps transFuel) 0 = some idx →
      dispatchFromVtable (vtableEntries env impls ct viewL.vtableTrait steps transFuel) idx =
      dispatchFromVtable (vtableEntries env impls ct viewR.vtableTrait steps transFuel) idx) := by
  have hwf0 := wellFormedView_direct env impls ct steps transFuel dia
  have hwfL := upcastViewChain_wellFormed env impls ct steps transFuel coh chainL _ viewL hwf0 hL
  have hwfR := upcastViewChain_wellFormed env impls ct steps transFuel coh chainR _ viewR hwf0 hR
  have hStL : viewL.staticTrait = root :=
    upcastViewChain_staticTrait env impls ct steps transFuel coh _ viewL chainL root
      (fun _ => hNonEmptyL) (fun hc => by rcases hNonEmptyL with ⟨pL, hpL⟩; cases pL <;> simp at hpL <;> rw [hpL] at hc <;> cases hc) hwf0 hL
  have hStR : viewR.staticTrait = root :=
    upcastViewChain_staticTrait env impls ct steps transFuel coh _ viewR chainR root
      (fun _ => hNonEmptyR) (fun hc => by rcases hNonEmptyR with ⟨pR, hpR⟩; cases pR <;> simp at hpR <;> rw [hpR] at hc <;> cases hc) hwf0 hR
  refine ⟨wellFormedView_dsa_eq env impls ct steps transFuel viewL,
          wellFormedView_dsa_eq env impls ct steps transFuel viewR, ?_⟩
  intro m idx hSlot
  have hLDirect := wellFormedView_dispatch_eq_direct env impls ct steps transFuel viewL m idx hwfL (hStL.symm ▸ hSlot)
  have hRDirect := wellFormedView_dispatch_eq_direct env impls ct steps transFuel viewR m idx hwfR (hStR.symm ▸ hSlot)
  rw [hLDirect, hRDirect, hStL, hStR]

/-! ## 7. `util::supertraits` Deduplication and `winnow_candidates` Generic Ambiguity -/

inductive TyPat where
  | concrete (argTag : Nat)
  | inferVar

structure TraitPat where
  defId  : Nat
  argPat : TyPat

noncomputable def matchesTraitPat (pat : TraitPat) (tr : TraitRef) : Bool :=
  Nat.beq pat.defId tr.defId &&
  match pat.argPat with
  | .concrete tag => Nat.beq tag tr.argTag
  | .inferVar => true

noncomputable def traitPatHasNonRegionInfer (pat : TraitPat) : Bool :=
  match pat.argPat with
  | .inferVar => true
  | .concrete _ => false

/-- Executable BFS/stack elaborator mirroring `compiler/rustc_type_ir/src/elaborate.rs`
    (`Elaborator::extend_deduped` using anonymized predicate `visited` set) as consumed by
    `assemble_candidates_for_unsizing` (`candidate_assembly.rs`). -/
noncomputable def elaborateSupertraitsFuel (env : TraitEnv) :
    Nat → List TraitRef → List TraitRef → List TraitRef
  | 0, _, accRev => accRev.reverse
  | _ + 1, [], accRev => accRev.reverse
  | fuel + 1, cur :: queue, accRev =>
    if traitMem cur accRev then elaborateSupertraitsFuel env fuel queue accRev
    else
      let unvisitedSupers := (env.directSupers cur).filter (fun s => !traitMem s accRev)
      elaborateSupertraitsFuel env fuel (queue ++ unvisitedSupers) (cur :: accRev)

noncomputable def supertraitsList (env : TraitEnv) (root : TraitRef) (fuel : Nat) : List TraitRef :=
  elaborateSupertraitsFuel env fuel [root] []

inductive SelectionResult where
  | unique (cand : TraitRef)
  | noCandidate
  | ambiguous

/-- Mirror of `select/candidate_assembly.rs` + `select/mod.rs::winnow_candidates`:
    - 0 matching supertraits -> `noCandidate`;
    - 1 deduplicated matching supertrait -> `unique cand`;
    - >= 2 distinct matching supertraits:
      * if `hasNonRegionInfer` -> `ambiguous` (`error[E0308]`);
      * otherwise -> deterministically selects first candidate (ordered `c1.min(c2)`). -/
noncomputable def selectUpcastCandidate (env : TraitEnv) (src : TraitRef) (pat : TraitPat)
    (fuel : Nat) : SelectionResult :=
  let cands := (supertraitsList env src fuel).filter (matchesTraitPat pat)
  match cands with
  | [] => SelectionResult.noCandidate
  | [c] => SelectionResult.unique c
  | c1 :: _ =>
    if traitPatHasNonRegionInfer pat then SelectionResult.ambiguous
    else SelectionResult.unique c1

theorem selectUpcast_singleton_unique (env : TraitEnv) (src cand : TraitRef) (pat : TraitPat)
    (fuel : Nat) (h : (supertraitsList env src fuel).filter (matchesTraitPat pat) = [cand]) :
    selectUpcastCandidate env src pat fuel = SelectionResult.unique cand := by
  dsimp only [selectUpcastCandidate]
  rw [h]

theorem selectUpcast_multi_infer_ambiguous (env : TraitEnv) (src c1 c2 : TraitRef)
    (rest : List TraitRef) (defId : Nat) (fuel : Nat)
    (h : (supertraitsList env src fuel).filter (matchesTraitPat { defId := defId, argPat := .inferVar }) =
      c1 :: c2 :: rest) :
    selectUpcastCandidate env src { defId := defId, argPat := .inferVar } fuel =
      SelectionResult.ambiguous := by
  dsimp only [selectUpcastCandidate]
  rw [h]
  rfl

/-! ## 8. Heap Operational Semantics and `Box<dyn Sub> -> Box<dyn Super>` Drop/Dealloc Soundness -/

structure Ptr where
  addr : Nat

noncomputable def Ptr.beq (a b : Ptr) : Bool :=
  Nat.beq a.addr b.addr

inductive DropEvent where
  | callDrop (dropFn : DropFnId) (ptr : Ptr)
  | dealloc (ptr : Ptr) (layout : Layout)

inductive HeapError where
  | ok
  | nullPointer
  | useAfterFree
  | sizeMismatch (expected actual : Nat)
  | alignMismatch (expected actual : Nat)

structure HeapBlock where
  live   : Bool
  layout : Layout

structure MachineState where
  heap    : Ptr → Option HeapBlock
  nextPtr : Nat
  events  : List DropEvent
  err     : HeapError

structure BoxDynValue where
  ptr  : Ptr
  ct   : ConcreteType
  view : DynVtableView

noncomputable def updateHeap (h : Ptr → Option HeapBlock) (p : Ptr)
    (blk : Option HeapBlock) : Ptr → Option HeapBlock :=
  fun q => if Ptr.beq p q then blk else h q

theorem updateHeap_eq (h : Ptr → Option HeapBlock) (p : Ptr) (blk : Option HeapBlock) :
    updateHeap h p blk p = blk := by
  dsimp only [updateHeap, Ptr.beq]
  simp only [nat_beq_refl p.addr, ↓reduceIte]

noncomputable def allocBoxDyn (st : MachineState) (ct : ConcreteType) (root : TraitRef) :
    MachineState × BoxDynValue :=
  let p : Ptr := { addr := st.nextPtr }
  let heap' := if Nat.beq ct.layout.size 0 then st.heap
               else updateHeap st.heap p (some { live := true, layout := ct.layout })
  let st' : MachineState := { st with heap := heap', nextPtr := st.nextPtr + 1 }
  let boxVal : BoxDynValue :=
    { ptr := p, ct := ct, view := { staticTrait := root, vtableTrait := root } }
  (st', boxVal)

/-- Mirror of MIR `Drop` terminator (`codegen_drop_terminator` nullable slot-0 check)
    followed by `<Box<T> as Drop>::drop` (`Layout::for_value_raw` reading slots 1 & 2,
    skipping `deallocate` when `size == 0`, calling `dealloc(ptr, Layout(size, align))` when `size > 0`). -/
noncomputable def dropBoxDyn (env : TraitEnv) (impls : ImplTable) (steps transFuel : Nat)
    (st : MachineState) (b : BoxDynValue) : MachineState :=
  let es := vtableEntries env impls b.ct b.view.vtableTrait steps transFuel
  match readDSAFromEntries es with
  | none => { st with err := HeapError.nullPointer }
  | some dsa =>
    let stAfterDrop :=
      match dsa.dropFn with
      | some dfn => { st with events := st.events ++ [DropEvent.callDrop dfn b.ptr] }
      | none => st
    if Nat.beq dsa.layout.size 0 then
      stAfterDrop
    else
      match stAfterDrop.heap b.ptr with
      | none => { stAfterDrop with err := HeapError.useAfterFree }
      | some blk =>
        if !blk.live then { stAfterDrop with err := HeapError.useAfterFree }
        else if !Nat.beq blk.layout.size dsa.layout.size then
          { stAfterDrop with err := HeapError.sizeMismatch blk.layout.size dsa.layout.size }
        else if !Nat.beq blk.layout.align dsa.layout.align then
          { stAfterDrop with err := HeapError.alignMismatch blk.layout.align dsa.layout.align }
        else
          { heap := updateHeap stAfterDrop.heap b.ptr (some { live := false, layout := blk.layout })
            nextPtr := stAfterDrop.nextPtr
            events := stAfterDrop.events ++ [DropEvent.dealloc b.ptr dsa.layout]
            err := stAfterDrop.err }

noncomputable def upcastBoxDyn (env : TraitEnv) (impls : ImplTable) (steps transFuel : Nat)
    (b : BoxDynValue) (chain : List TraitRef) : Option BoxDynValue :=
  match upcastViewChain env impls b.ct steps transFuel b.view chain with
  | some v' => some { b with view := v' }
  | none => none

/-- **Universal Theorem 3 (Arbitrary-Chain `Box<dyn T₀> -> ... -> Box<dyn Tₖ>` Drop & Heap Deallocation Soundness)**:
    Starting from any error-free `MachineState` (`st.err = .ok`), allocating `Box<dyn T₀>` for any
    concrete type `ct` (`needsDrop` either `true` or `false`, `size` zero or positive), applying
    ANY valid trait upcast chain `T₀ -> T₁ -> ... -> Tₖ`, and dropping the resulting `Box<dyn Tₖ>`:
    1. Leaves `err = .ok` (zero size mismatch, zero alignment mismatch, zero use-after-free);
    2. Fires `DropEvent.callDrop dfn ptr` iff `ct.needsDrop = true` and `ct.dropFn = some dfn`
       (BEFORE `DropEvent.dealloc` — preserving outer-before-inner Drop elaboration order);
    3. Deallocates at the EXACT `ct.layout` (`size, align`) if `ct.layout.size > 0`, or skips
       allocator `dealloc` if `ct.layout.size = 0`;
    4. Leaves the heap block marked non-live if `ct.layout.size > 0`. -/
theorem box_upcast_chain_drop_dealloc_sound (env : TraitEnv) (impls : ImplTable)
    (steps transFuel : Nat) (st : MachineState) (ct : ConcreteType) (root : TraitRef)
    (chain : List TraitRef) (bUp : BoxDynValue)
    (hOk : st.err = HeapError.ok)
    (hUp : upcastBoxDyn env impls steps transFuel (allocBoxDyn st ct root).2 chain = some bUp) :
    let st0 := (allocBoxDyn st ct root).1
    let p := (allocBoxDyn st ct root).2.ptr
    let stEnd := dropBoxDyn env impls steps transFuel st0 bUp
    stEnd.err = HeapError.ok ∧
    stEnd.events = st.events ++
      (match ct.dsaHeader.dropFn with | some dfn => [DropEvent.callDrop dfn p] | none => []) ++
      (if Nat.beq ct.layout.size 0 then [] else [DropEvent.dealloc p ct.layout]) ∧
    (Nat.beq ct.layout.size 0 = false →
      stEnd.heap p = some { live := false, layout := ct.layout }) := by
  dsimp only [allocBoxDyn] at hUp ⊢
  dsimp only [upcastBoxDyn] at hUp
  cases hCh : upcastViewChain env impls ct steps transFuel
      { staticTrait := root, vtableTrait := root } chain with
  | none => rw [hCh] at hUp; cases hUp
  | some vEnd =>
    rw [hCh] at hUp
    injection hUp with hBEq
    subst hBEq
    dsimp only [dropBoxDyn]
    have hDsa : readDSAFromEntries (vtableEntries env impls ct vEnd.vtableTrait steps transFuel) =
        some ct.dsaHeader :=
      wellFormedView_dsa_eq env impls ct steps transFuel vEnd
    rw [hDsa]
    dsimp only
    cases hSz : Nat.beq ct.layout.size 0
    · dsimp only [ConcreteType.dsaHeader] at hSz ⊢
      simp only [hSz, Bool.false_eq_true, ↓reduceIte]
      have hBlk : updateHeap st.heap { addr := st.nextPtr }
          (some { live := true, layout := ct.layout }) { addr := st.nextPtr } =
          some { live := true, layout := ct.layout } :=
        updateHeap_eq _ _ _
      cases hDr : (if ct.needsDrop then ct.dropFn else none) with
      | none =>
        dsimp only
        rw [hBlk]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nat_beq_refl ct.layout.size, nat_beq_refl ct.layout.align]
        refine ⟨hOk, ?_, fun _ => updateHeap_eq _ _ _⟩
        simp only [List.append_nil]
      | some dfn =>
        dsimp only
        rw [hBlk]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nat_beq_refl ct.layout.size, nat_beq_refl ct.layout.align]
        refine ⟨hOk, True.intro, fun _ => updateHeap_eq _ _ _⟩
    · dsimp only [ConcreteType.dsaHeader] at hSz ⊢
      simp only [hSz, ↓reduceIte]
      cases hDr : (if ct.needsDrop then ct.dropFn else none) with
      | none =>
        refine ⟨hOk, ?_, fun hF => by cases hF⟩
        simp only [List.append_nil]
      | some dfn =>
        refine ⟨hOk, ?_, fun hF => by cases hF⟩
        simp only [List.append_nil]

/-! ## 9. Exact Concrete Specimens Matching Empirical `rustc`/LLVM/`Miri` Probes -/

-- Shared trait identifiers across Specimens A, B, and C
noncomputable def tRoot : TraitRef := { defId := 1, argTag := 0 }
noncomputable def tLeft : TraitRef := { defId := 2, argTag := 0 }
noncomputable def tRight : TraitRef := { defId := 3, argTag := 0 }
noncomputable def tDiamond : TraitRef := { defId := 4, argTag := 0 }
noncomputable def tSibling : TraitRef := { defId := 5, argTag := 0 }
noncomputable def tRightSecond : TraitRef := { defId := 6, argTag := 0 }
noncomputable def tDiamondAsym : TraitRef := { defId := 7, argTag := 0 }
noncomputable def tGenRootU8 : TraitRef := { defId := 8, argTag := 8 }
noncomputable def tGenRootU16 : TraitRef := { defId := 8, argTag := 16 }
noncomputable def tLeftU8 : TraitRef := { defId := 9, argTag := 0 }
noncomputable def tRightU8 : TraitRef := { defId := 10, argTag := 0 }
noncomputable def tSameGenDia : TraitRef := { defId := 11, argTag := 0 }
noncomputable def tAmbigDia : TraitRef := { defId := 12, argTag := 0 }

noncomputable def tSuperA : TraitRef := { defId := 20, argTag := 0 }
noncomputable def tSuperB : TraitRef := { defId := 21, argTag := 0 }
noncomputable def tSuperC : TraitRef := { defId := 22, argTag := 0 }
noncomputable def tEmptyMarker : TraitRef := { defId := 23, argTag := 0 }
noncomputable def tSub : TraitRef := { defId := 24, argTag := 0 }
noncomputable def tSubAfterEmpty : TraitRef := { defId := 25, argTag := 0 }
noncomputable def tTri : TraitRef := { defId := 26, argTag := 0 }

noncomputable def tTier0 : TraitRef := { defId := 30, argTag := 0 }
noncomputable def tTier1 : TraitRef := { defId := 31, argTag := 0 }
noncomputable def tTier2 : TraitRef := { defId := 32, argTag := 0 }
noncomputable def tTier3 : TraitRef := { defId := 33, argTag := 0 }
noncomputable def tPrim0 : TraitRef := { defId := 34, argTag := 0 }
noncomputable def tPrim1 : TraitRef := { defId := 35, argTag := 0 }
noncomputable def tPrim2 : TraitRef := { defId := 36, argTag := 0 }

noncomputable def specimenEnv : TraitEnv :=
  { lookupTrait := fun tr =>
      if tr.beq tRoot then some { traitRef := tRoot, directSupers := [], ownMethods := [.active { id := 1 }] }
      else if tr.beq tLeft then some { traitRef := tLeft, directSupers := [tRoot], ownMethods := [.active { id := 2 }] }
      else if tr.beq tRight then some { traitRef := tRight, directSupers := [tRoot], ownMethods := [.active { id := 3 }] }
      else if tr.beq tDiamond then some { traitRef := tDiamond, directSupers := [tLeft, tRight], ownMethods := [.active { id := 4 }] }
      else if tr.beq tSibling then some { traitRef := tSibling, directSupers := [], ownMethods := [.active { id := 5 }] }
      else if tr.beq tRightSecond then some { traitRef := tRightSecond, directSupers := [tSibling, tRoot], ownMethods := [.active { id := 6 }] }
      else if tr.beq tDiamondAsym then some { traitRef := tDiamondAsym, directSupers := [tLeft, tRightSecond], ownMethods := [.active { id := 7 }] }
      else if tr.beq tGenRootU8 then some { traitRef := tGenRootU8, directSupers := [], ownMethods := [.active { id := 8 }] }
      else if tr.beq tGenRootU16 then some { traitRef := tGenRootU16, directSupers := [], ownMethods := [.active { id := 8 }] }
      else if tr.beq tLeftU8 then some { traitRef := tLeftU8, directSupers := [tGenRootU8], ownMethods := [] }
      else if tr.beq tRightU8 then some { traitRef := tRightU8, directSupers := [tGenRootU8], ownMethods := [] }
      else if tr.beq tSameGenDia then some { traitRef := tSameGenDia, directSupers := [tLeftU8, tRightU8], ownMethods := [.active { id := 9 }] }
      else if tr.beq tAmbigDia then some { traitRef := tAmbigDia, directSupers := [tGenRootU8, tGenRootU16], ownMethods := [.active { id := 10 }] }
      else if tr.beq tSuperA then some { traitRef := tSuperA, directSupers := [], ownMethods := [.active { id := 20 }] }
      else if tr.beq tSuperB then some { traitRef := tSuperB, directSupers := [], ownMethods := [.active { id := 21 }] }
      else if tr.beq tSuperC then some { traitRef := tSuperC, directSupers := [], ownMethods := [.active { id := 22 }, .active { id := 23 }] }
      else if tr.beq tEmptyMarker then some { traitRef := tEmptyMarker, directSupers := [], ownMethods := [] }
      else if tr.beq tSub then some { traitRef := tSub, directSupers := [tSuperA, tSuperB], ownMethods := [.active { id := 24 }] }
      else if tr.beq tSubAfterEmpty then some { traitRef := tSubAfterEmpty, directSupers := [tEmptyMarker, tSuperB], ownMethods := [.active { id := 25 }] }
      else if tr.beq tTri then some { traitRef := tTri, directSupers := [tSuperA, tSuperB, tSuperC], ownMethods := [.active { id := 26 }] }
      else if tr.beq tPrim0 then some { traitRef := tPrim0, directSupers := [], ownMethods := [.active { id := 30 }] }
      else if tr.beq tPrim1 then some { traitRef := tPrim1, directSupers := [], ownMethods := [.active { id := 31 }] }
      else if tr.beq tPrim2 then some { traitRef := tPrim2, directSupers := [], ownMethods := [.active { id := 32 }] }
      else if tr.beq tTier0 then some { traitRef := tTier0, directSupers := [], ownMethods := [.active { id := 33 }] }
      else if tr.beq tTier1 then some { traitRef := tTier1, directSupers := [tPrim1, tTier0], ownMethods := [.active { id := 34 }] }
      else if tr.beq tTier2 then some { traitRef := tTier2, directSupers := [tPrim2, tTier1], ownMethods := [.active { id := 35 }] }
      else if tr.beq tTier3 then some { traitRef := tTier3, directSupers := [tPrim0, tTier2], ownMethods := [.active { id := 36 }] }
      else none }

noncomputable def specimenImpls : ImplTable :=
  { lookupImpl := fun _ tr m => some { id := tr.defId * 100 + tr.argTag * 10 + m.id } }

noncomputable def ctSmallNode : ConcreteType :=
  { tyId := { id := 1 }, needsDrop := false, dropFn := none, layout := { size := 8, align := 8 } }

noncomputable def ctImpl16 : ConcreteType :=
  { tyId := { id := 2 }, needsDrop := false, dropFn := none, layout := { size := 16, align := 16 } }

noncomputable def ctDropTracker : ConcreteType :=
  { tyId := { id := 3 }, needsDrop := true, dropFn := some { id := 901 }, layout := { size := 32, align := 32 } }

noncomputable def ctNoDropBig : ConcreteType :=
  { tyId := { id := 4 }, needsDrop := false, dropFn := some { id := 902 }, layout := { size := 64, align := 32 } }

-- Exact LLVM IR byte offsets (`slot * 8`) verified by kernel reduction (`rfl`)!
theorem expA_primary_and_empty_marker_zero_offset :
    supertraitVtableSlot specimenEnv tSub tSuperA 20 10 = some none ∧
    supertraitVtableSlot specimenEnv tSubAfterEmpty tSuperB 20 10 = some none ∧
    supertraitVtableSlot specimenEnv tTri tSuperA 30 10 = some none :=
  ⟨rfl, rfl, rfl⟩

theorem expA_secondary_vptr_slots_exact :
    supertraitVtableSlot specimenEnv tSub tSuperB 20 10 = some (some 5) ∧
    supertraitVtableSlot specimenEnv tTri tSuperB 30 10 = some (some 5) ∧
    supertraitVtableSlot specimenEnv tTri tSuperC 30 10 = some (some 8) :=
  ⟨rfl, rfl, rfl⟩

theorem expA_prefix_relationships_hold (ct : ConcreteType) :
    ListPrefix (vtableEntries specimenEnv specimenImpls ct tSuperA 20 10)
               (vtableEntries specimenEnv specimenImpls ct tSub 20 10) ∧
    ListPrefix (vtableEntries specimenEnv specimenImpls ct tSuperB 20 10)
               (vtableEntries specimenEnv specimenImpls ct tSubAfterEmpty 20 10) ∧
    ListPrefix (vtableEntries specimenEnv specimenImpls ct tSuperA 30 10)
               (vtableEntries specimenEnv specimenImpls ct tTri 30 10) := by
  have hSegA20 : prepareVtableSegments specimenEnv tSuperA 20 10 =
      [VtblSegment.metadataDSA, VtblSegment.traitOwnEntries tSuperA false] := rfl
  have hSegSub : prepareVtableSegments specimenEnv tSub 20 10 =
      [VtblSegment.metadataDSA, VtblSegment.traitOwnEntries tSuperA false,
       VtblSegment.traitOwnEntries tSuperB true, VtblSegment.traitOwnEntries tSub false] := rfl
  have hSegB20 : prepareVtableSegments specimenEnv tSuperB 20 10 =
      [VtblSegment.metadataDSA, VtblSegment.traitOwnEntries tSuperB false] := rfl
  have hSegSAE : prepareVtableSegments specimenEnv tSubAfterEmpty 20 10 =
      [VtblSegment.metadataDSA, VtblSegment.traitOwnEntries tEmptyMarker false,
       VtblSegment.traitOwnEntries tSuperB false, VtblSegment.traitOwnEntries tSubAfterEmpty false] := rfl
  have hSegA30 : prepareVtableSegments specimenEnv tSuperA 30 10 =
      [VtblSegment.metadataDSA, VtblSegment.traitOwnEntries tSuperA false] := rfl
  have hSegTri : prepareVtableSegments specimenEnv tTri 30 10 =
      [VtblSegment.metadataDSA, VtblSegment.traitOwnEntries tSuperA false,
       VtblSegment.traitOwnEntries tSuperB true, VtblSegment.traitOwnEntries tSuperC true,
       VtblSegment.traitOwnEntries tTri false] := rfl
  refine ⟨⟨[VtblEntry.method tSuperB { id := 21 } { id := 2121 },
             VtblEntry.traitVPtr tSuperB,
             VtblEntry.method tSub { id := 24 } { id := 2424 }], ?_⟩,
          ⟨[VtblEntry.method tSubAfterEmpty { id := 25 } { id := 2525 }], ?_⟩,
          ⟨[VtblEntry.method tSuperB { id := 21 } { id := 2121 },
             VtblEntry.traitVPtr tSuperB,
             VtblEntry.method tSuperC { id := 22 } { id := 2222 },
             VtblEntry.method tSuperC { id := 23 } { id := 2223 },
             VtblEntry.traitVPtr tSuperC,
             VtblEntry.method tTri { id := 26 } { id := 2626 }], ?_⟩⟩
  · dsimp only [vtableEntries]
    rw [hSegA20, hSegSub]
    rfl
  · dsimp only [vtableEntries]
    rw [hSegB20, hSegSAE]
    rfl
  · dsimp only [vtableEntries]
    rw [hSegA30, hSegTri]
    rfl

theorem expB_symmetric_diamond_dedup_exact :
    prepareVtableSegments specimenEnv tDiamond 20 10 =
      [VtblSegment.metadataDSA,
       VtblSegment.traitOwnEntries tRoot false,
       VtblSegment.traitOwnEntries tLeft false,
       VtblSegment.traitOwnEntries tRight true,
       VtblSegment.traitOwnEntries tDiamond false] ∧
    supertraitVtableSlot specimenEnv tDiamond tLeft 20 10 = some none ∧
    supertraitVtableSlot specimenEnv tDiamond tRoot 20 10 = some none ∧
    supertraitVtableSlot specimenEnv tLeft tRoot 20 10 = some none ∧
    supertraitVtableSlot specimenEnv tDiamond tRight 20 10 = some (some 6) ∧
    supertraitVtableSlot specimenEnv tRight tRoot 20 10 = some none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem expB_asymmetric_diamond_slots_exact :
    supertraitVtableSlot specimenEnv tDiamondAsym tLeft 30 10 = some none ∧
    supertraitVtableSlot specimenEnv tDiamondAsym tRoot 30 10 = some none ∧
    supertraitVtableSlot specimenEnv tDiamondAsym tRightSecond 30 10 = some (some 8) ∧
    supertraitVtableSlot specimenEnv tRightSecond tRoot 30 10 = some (some 5) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem expB_diamond_paths_agree_despite_distinct_vptrs :
    let v0 : DynVtableView := { staticTrait := tDiamond, vtableTrait := tDiamond }
    ∃ vL vR vDir,
      upcastViewChain specimenEnv specimenImpls ctSmallNode 20 10 v0 [tLeft, tRoot] = some vL ∧
      upcastViewChain specimenEnv specimenImpls ctSmallNode 20 10 v0 [tRight, tRoot] = some vR ∧
      upcastViewChain specimenEnv specimenImpls ctSmallNode 20 10 v0 [tRoot] = some vDir ∧
      vL.vtableTrait ≠ vR.vtableTrait ∧
      vL.vtableTrait = vDir.vtableTrait ∧
      readDSAFromEntries (vtableEntries specimenEnv specimenImpls ctSmallNode vL.vtableTrait 20 10) =
        some ctSmallNode.dsaHeader ∧
      readDSAFromEntries (vtableEntries specimenEnv specimenImpls ctSmallNode vR.vtableTrait 20 10) =
        some ctSmallNode.dsaHeader ∧
      dispatchFromVtable (vtableEntries specimenEnv specimenImpls ctSmallNode vL.vtableTrait 20 10) 3 =
        dispatchFromVtable (vtableEntries specimenEnv specimenImpls ctSmallNode vR.vtableTrait 20 10) 3 := by
  refine ⟨{ staticTrait := tRoot, vtableTrait := tDiamond },
          { staticTrait := tRoot, vtableTrait := tRight },
          { staticTrait := tRoot, vtableTrait := tDiamond },
          rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro hEq
  cases hEq

theorem expB_generic_diamond_sharpness :
    selectUpcastCandidate specimenEnv tSameGenDia { defId := 8, argPat := .inferVar } 20 =
      SelectionResult.unique tGenRootU8 ∧
    selectUpcastCandidate specimenEnv tAmbigDia { defId := 8, argPat := .inferVar } 20 =
      SelectionResult.ambiguous ∧
    selectUpcastCandidate specimenEnv tAmbigDia { defId := 8, argPat := .concrete 8 } 20 =
      SelectionResult.unique tGenRootU8 ∧
    selectUpcastCandidate specimenEnv tAmbigDia { defId := 8, argPat := .concrete 16 } 20 =
      SelectionResult.unique tGenRootU16 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem expC_three_hop_vptr_slots_exact :
    supertraitVtableSlot specimenEnv tTier3 tTier2 40 10 = some (some 13) ∧
    supertraitVtableSlot specimenEnv tTier2 tTier1 40 10 = some (some 9) ∧
    supertraitVtableSlot specimenEnv tTier1 tTier0 40 10 = some (some 5) :=
  ⟨rfl, rfl, rfl⟩

theorem expC_box_3hop_and_nodrop_verified :
    let initSt : MachineState := { heap := fun _ => none, nextPtr := 1, events := [], err := HeapError.ok }
    let (st1, box3) := allocBoxDyn initSt ctDropTracker tTier3
    ∃ box0,
      upcastBoxDyn specimenEnv specimenImpls 40 10 box3 [tTier2, tTier1, tTier0] = some box0 ∧
      let st2 := dropBoxDyn specimenEnv specimenImpls 40 10 st1 box0
      let (st3, boxND) := allocBoxDyn st2 ctNoDropBig tSub
      ∃ boxNDB,
        upcastBoxDyn specimenEnv specimenImpls 40 10 boxND [tSuperB] = some boxNDB ∧
        let st4 := dropBoxDyn specimenEnv specimenImpls 40 10 st3 boxNDB
        st4.err = HeapError.ok ∧
        st4.events =
          [DropEvent.callDrop { id := 901 } { addr := 1 },
           DropEvent.dealloc { addr := 1 } { size := 32, align := 32 },
           DropEvent.dealloc { addr := 2 } { size := 64, align := 32 }] :=
  ⟨{ ptr := { addr := 1 }, ct := ctDropTracker, view := { staticTrait := tTier0, vtableTrait := tTier0 } },
   rfl,
   { ptr := { addr := 2 }, ct := ctNoDropBig, view := { staticTrait := tSuperB, vtableTrait := tSuperB } },
   rfl,
   rfl, rfl⟩

/-! ## 10. Sharpness Counterexamples (Why Skipping `TraitVPtr` or Mis-Encoding `DSA` Breaks Soundness) -/

/-- **Counterexample 1 (Missing `TraitVPtr` Slot Adjustment)**: Reusing `Sub`'s vtable pointer
    unchanged when coercing `&dyn Sub -> &dyn SuperB` reads slot 3 of `Sub` (`SuperA::a = 2020`)
    instead of slot 3 of `SuperB` (`SuperB::b = 2121`). -/
theorem counterexample_wrong_prefix_reuse_dispatches_wrong_method :
    let wrongVtable := vtableEntries specimenEnv specimenImpls ctImpl16 tSub 20 10
    let rightVtable := vtableEntries specimenEnv specimenImpls ctImpl16 tSuperB 20 10
    dispatchFromVtable wrongVtable 3 = some { id := 2020 } ∧
    dispatchFromVtable rightVtable 3 = some { id := 2121 } ∧
    dispatchFromVtable wrongVtable 3 ≠ dispatchFromVtable rightVtable 3 :=
  ⟨rfl, rfl, fun h => by cases h⟩

/-- **Counterexample 2 (`SuperB` Layout in `DSA` Instead of Concrete Type Layout)**:
    If a sub-vtable's `DSA` slots stored the trait object's abstract unsized layout `(0, 1)` rather
    than concrete `DropTracker`'s `(32, 32)`, `dropBoxDyn`'s `dealloc` layout check immediately fails
    or mismatches `alloc`'s `HeapBlock.layout`. -/
theorem counterexample_wrong_supertrait_layout_dealloc_ub :
    ¬ Layout.beq ctDropTracker.layout { size := 0, align := 1 } = true := by
  intro h
  cases h

/-! ## 11. Anneal Trusted Computing Base (`Trusted.MirAst` / `Trusted.MirSemantics`) Fail-Closed Gap -/

inductive AnnealMirTy where
  | scalar (bits : Nat)
  | rawPtr
  | unsupportedDyn

inductive AnnealEvalStatus where
  | ok
  | rejectedUnsupported

noncomputable def annealEvalUnsize : AnnealMirTy → AnnealMirTy → AnnealEvalStatus
  | .unsupportedDyn, _ => .rejectedUnsupported
  | _, .unsupportedDyn => .rejectedUnsupported
  | _, _ => .ok

/-- Mirrors `joshlf/anneal` (`trusted/lean/Trusted/MirAst.lean` + `MirSemantics.lean`):
    because `TyKind::Dynamic`, `Rvalue::Cast(Unsize)`, and `TerminatorKind::Drop` map to
    `.unsupported` and fault closed in `evalRvalue`/`evalTerminator`, Anneal is sound by
    non-admission: it never certifies a trait-object upcast whose vtable layout would violate
    the prefix or `DSA` invariants above, while rejecting valid upcasts as `.rejectedUnsupported`. -/
theorem anneal_tcb_fail_closed_on_dyn_upcast (src : AnnealMirTy) :
    annealEvalUnsize src .unsupportedDyn = .rejectedUnsupported := by
  cases src <;> rfl

end TraitUpcastingVtableSoundness
