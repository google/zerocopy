/-!
# Monomorphization Collector, Vtable Layout, and `dyn` Trait Upcasting Soundness

Standalone Lean 4 (`v4.34.1`) formalization modeling:
1. `rustc_trait_selection::traits::vtable` segment layout (`prepare_vtable_segments`,
   `vtable_entries`, `first_method_vtable_slot`, `supertrait_vtable_slot`), including
   first-supertrait prefix reuse, empty-marker supertrait prefix preservation,
   secondary-supertrait `TraitVPtr` indirection slots, `VtblEntry::Vacant`, and
   nullable `MetadataDropInPlace` (`null` when `!ty.needs_drop`);
2. `rustc_monomorphize::collector` reachability closure (`MonoReachable`) across
   direct calls, `PointerCoercion::Unsize` (vtable methods + `VTableShim` +
   `ReifyShim` + `DropGlue`), `PointerCoercion::ReifyFnPointer`, `ClosureOnceShim`,
   `FnPtrShim`, direct vs. reified `DropGlue`, and `Lazy` vs. `Eager` root sets;
3. Soundness theorems:
   - Prefix-reuse and secondary-`TraitVPtr` `dyn` upcasting dispatch soundness
     (methods and slot-0 drop glue dispatch identically to direct concrete resolution),
   - Supertrait vtable method coverage (justifying why `create_mono_items_for_vtable_methods`
     safely skips `VtblEntry::TraitVPtr` when collecting method mono-items),
   - Monomorphization collector link-completeness (closed-root `MonoReachable` +
     `VtableReachable` guarantees zero `missingSymbol`, `missingVtable`, or
     `badSlotEntry` faults across arbitrary execution fuel),
   - `Lazy ⊆ Eager` monotonicity;
4. Two sharpness counterexamples:
   - CE1: Reusing the subtrait vtable pointer for a non-principal secondary supertrait
     `SuperB` in a diamond hierarchy dispatches `SuperB::b_val` to the wrong method
     (`SuperA::a_val`), and on an asymmetric supertrait width jumps into a `TraitVPtr`
     data slot (`badSlotEntry`);
   - CE2: Omitting `ReifyShim` during `#[track_caller]` `fn`-item coercion OR omitting
     `DropGlue` during `dyn Trait` unsizing causes a deterministic `missingSymbol`
     runtime fault even when all other reachable items are emitted.

No imports beyond `Init`. Zero `sorry`, `Classical.choice`, `omega`, `bv_decide`,
`native_decide`, `partial def`, `axiom`, `opaque`, `unsafe`, or `._unsafe_rec`.
-/

namespace MonomorphVtableUpcast

-- ============================================================================
-- Section 1: Core Identifiers, Types, Traits, and Instance Kinds
-- ============================================================================

abbrev TyId := Nat
abbrev TraitId := Nat
abbrev MethodId := Nat
abbrev FnId := Nat
abbrev LocId := Nat

structure ConcreteTy where
  id : TyId
  size : Nat
  align : Nat
  needsDrop : Bool
  deriving DecidableEq, Repr

/-- Mirrors `rustc_middle::ty::InstanceKind` for monomorphization and vtables. -/
inductive InstanceKind where
  | item (fnId : FnId) (tyArg : TyId)
  | vtableShim (fnId : FnId) (tyArg : TyId)
  | reifyShim (fnId : FnId) (tyArg : TyId) (loc : LocId)
  | closureOnceShim (fnId : FnId) (tyArg : TyId)
  | fnPtrShim (fnId : FnId) (tyArg : TyId)
  | dropGlue (ty : ConcreteTy)
  | virtualCall (traitId : TraitId) (slotIdx : Nat)
  deriving DecidableEq, Repr

/-- Whether an `InstanceKind` produces a linkable codegen symbol (everything except `virtualCall`). -/
def InstanceKind.isCodegenSymbol : InstanceKind → Bool
  | .virtualCall _ _ => false
  | _ => true

/-- Mirrors `rustc_middle::ty::vtable::VtblEntry`. -/
inductive VtblEntry where
  | metadataDropInPlace (dropSym : Option InstanceKind)
  | metadataSize (sz : Nat)
  | metadataAlign (al : Nat)
  | vacant
  | method (inst : InstanceKind)
  | traitVPtr (superTr : TraitId)
  deriving DecidableEq, Repr

/-- Mirrors `rustc_trait_selection::traits::vtable::VtblSegment`. -/
inductive VtblSegment where
  | metadataDSA
  | traitOwnEntries (tr : TraitId) (emitVPtr : Bool)
  deriving DecidableEq, Repr

/-- Static definition of a dyn-compatible trait in a trait hierarchy. -/
structure TraitDef where
  ownMethods : List MethodId
  directSupers : List TraitId
  deriving DecidableEq, Repr

/-- Method dispatch resolution for `(ty, trait, method)`:
    `none` models `VtblEntry::Vacant` (impossible `where` clause for `ty`),
    `some inst` models `VtblEntry::Method(inst)` (which may be `item`, `vtableShim`, or `reifyShim`). -/
abbrev MethodResolver := ConcreteTy → TraitId → MethodId → Option InstanceKind

/-- Finite trait hierarchy mapping `TraitId` to its definition. -/
structure TraitHierarchy where
  defs : TraitId → TraitDef
  /-- Depth bound ensuring finite acyclic supertrait exploration. -/
  maxDepth : Nat

-- ============================================================================
-- Section 2: General List / Index Lemmas (Zero `omega`, Zero `Classical`)
-- ============================================================================

theorem getElem?_append_left_nat {α : Type} (xs ys : List α) (i : Nat)
    (h : i < xs.length) :
    (xs ++ ys)[i]? = xs[i]? := by
  induction xs generalizing i with
  | nil =>
    cases h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih i' (Nat.lt_of_succ_lt_succ h)

theorem getElem?_append_right_nat {α : Type} (xs ys : List α) (j : Nat) :
    (xs ++ ys)[xs.length + j]? = ys[j]? := by
  induction xs with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, Nat.succ_add, List.getElem?_cons_succ]
    exact ih

theorem mem_append_left_of_mem {α : Type} {x : α} {xs ys : List α}
    (h : x ∈ xs) : x ∈ xs ++ ys := by
  induction xs with
  | nil => cases h
  | cons a as ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (ih h')

theorem mem_append_right_of_mem {α : Type} {x : α} {xs ys : List α}
    (h : x ∈ ys) : x ∈ xs ++ ys := by
  induction xs with
  | nil => exact h
  | cons a as ih => exact List.Mem.tail _ ih

theorem mem_of_getElem?_eq_some {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil =>
    simp only [List.getElem?_nil] at h
    cases h
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at h
      cases h
      exact List.Mem.head _
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (ih h)

theorem mem_map_of_mem {α β : Type} {f : α → β} {x : α} {xs : List α}
    (h : x ∈ xs) : f x ∈ xs.map f := by
  induction xs with
  | nil => cases h
  | cons a as ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (ih h')

theorem mem_flatMap_of_mem {α β : Type} {f : α → List β} {a : α} {b : β} {xs : List α}
    (ha : a ∈ xs) (hb : b ∈ f a) : b ∈ xs.flatMap f := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    cases ha with
    | head =>
      simp only [List.flatMap_cons]
      exact mem_append_left_of_mem hb
    | tail _ ha' =>
      simp only [List.flatMap_cons]
      exact mem_append_right_of_mem (ih ha')

theorem mem_of_mem_append {α : Type} {x : α} {xs ys : List α}
    (h : x ∈ xs ++ ys) : x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons a as ih =>
    cases h with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ h' =>
      cases ih h' with
      | inl hl => exact Or.inl (List.Mem.tail _ hl)
      | inr hr => exact Or.inr hr

theorem mem_of_mem_flatMap {α β : Type} {f : α → List β} {b : β} {xs : List α}
    (h : b ∈ xs.flatMap f) : ∃ a, a ∈ xs ∧ b ∈ f a := by
  induction xs with
  | nil =>
    simp only [List.flatMap_nil] at h
    cases h
  | cons x xs ih =>
    simp only [List.flatMap_cons] at h
    cases mem_of_mem_append h with
    | inl hl => exact ⟨x, List.Mem.head _, hl⟩
    | inr hr =>
      rcases ih hr with ⟨a, ha, hb⟩
      exact ⟨a, List.Mem.tail _ ha, hb⟩

theorem length_append_eq {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, Nat.succ_add]
    rw [ih]

theorem length_map_eq {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    simp only [List.map_cons, List.length_cons]
    rw [ih]

theorem getElem?_map_eq {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    (xs.map f)[i]? = (xs[i]?).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.map_cons, List.getElem?_cons_succ]
      exact ih i'

/-- Total index search returning `some i` when `x` first occurs at index `i`.
    Defined via `List.foldr` (zero `._unsafe_rec` helpers). -/
def findIndexOf {α : Type} [DecidableEq α] (x : α) (xs : List α) : Option Nat :=
  xs.foldr
    (fun y ih =>
      if y = x then some 0
      else match ih with
        | none => none
        | some i => some (i + 1))
    none

theorem findIndexOf_nil {α : Type} [DecidableEq α] (x : α) :
    findIndexOf x [] = none := rfl

theorem findIndexOf_cons {α : Type} [DecidableEq α] (x y : α) (ys : List α) :
    findIndexOf x (y :: ys) =
      (if y = x then some 0
       else match findIndexOf x ys with
         | none => none
         | some i => some (i + 1)) := rfl

theorem findIndexOf_getElem? {α : Type} [DecidableEq α] {x : α} {xs : List α} {i : Nat}
    (h : findIndexOf x xs = some i) : xs[i]? = some x := by
  induction xs generalizing i with
  | nil => cases h
  | cons y ys ih =>
    rw [findIndexOf_cons] at h
    by_cases hy : y = x
    · simp only [hy, ↓reduceIte] at h
      cases h
      simp only [List.getElem?_cons_zero, hy]
    · simp only [hy, ↓reduceIte] at h
      cases hrec : findIndexOf x ys with
      | none =>
        rw [hrec] at h
        cases h
      | some j =>
        rw [hrec] at h
        cases h
        simp only [List.getElem?_cons_succ]
        exact ih hrec

theorem findIndexOf_lt_length {α : Type} [DecidableEq α] {x : α} {xs : List α} {i : Nat}
    (h : findIndexOf x xs = some i) : i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons y ys ih =>
    rw [findIndexOf_cons] at h
    by_cases hy : y = x
    · simp only [hy, ↓reduceIte] at h
      cases h
      exact Nat.zero_lt_succ ys.length
    · simp only [hy, ↓reduceIte] at h
      cases hrec : findIndexOf x ys with
      | none =>
        rw [hrec] at h
        cases h
      | some j =>
        rw [hrec] at h
        cases h
        exact Nat.succ_lt_succ (ih hrec)

-- ============================================================================
-- Section 3: Vtable Segment Layout (`rustc_trait_selection/src/traits/vtable.rs`)
-- ============================================================================

/-- Check whether `tr` or any transitive supertrait (within `fuel`) has own existential entries.
    Mirrors `ty::elaborate::supertrait_def_ids(tcx, id).any(has_own_existential_vtable_entries)`
    at `compiler/rustc_trait_selection/src/traits/vtable.rs:162-163`. -/
def traitHasEntriesStep (H : TraitHierarchy) (ih : TraitId → Bool) (tr : TraitId) : Bool :=
  let d := H.defs tr
  if !d.ownMethods.isEmpty then true
  else d.directSupers.any ih

def traitHasEntriesAux (H : TraitHierarchy) (fuel : Nat) : TraitId → Bool :=
  Nat.repeat (traitHasEntriesStep H) fuel (fun _ => false)

def traitHasEntries (H : TraitHierarchy) (tr : TraitId) : Bool :=
  traitHasEntriesAux H (H.maxDepth + 1) tr

/-- Post-order DFS slice traversal of supertraits mirroring `prepare_vtable_segments_inner`
    (`compiler/rustc_trait_selection/src/traits/vtable.rs:37-187`).

    State `(visited, emitVPtrOnNew, accRev)` threads:
    - `visited`: deduplicated supertraits already entered (prevents diamond duplication);
    - `emitVPtrOnNew`: starts `false` along the first-supertrait spine and flips to `true`
      as soon as any emitted trait has `traitHasEntries H tr = true`;
    - `accRev`: emitted segments in reverse order.

    Crucially, `emitVPtr` for `tr` is captured as `emitVPtrOnNew` *when `tr` is entered*
    (matching the `(next_super_trait, emit_vptr_on_new_entry, siblings)` push on stack at
    `vtable.rs:145-149` and `177`), while `emitVPtrOnNew` is updated *when `tr` is emitted*
    (`emit_vptr_on_new_entry |= has_entries`, `vtable.rs:172`). -/
def dfsVisitStep (H : TraitHierarchy)
    (ih : TraitId → List TraitId → Bool → List VtblSegment →
      (List TraitId × Bool × List VtblSegment))
    (tr : TraitId) (visited : List TraitId) (emitOnNew : Bool) (acc : List VtblSegment) :
    (List TraitId × Bool × List VtblSegment) :=
  if tr ∈ visited then
    (visited, emitOnNew, acc)
  else
    let visited1 := tr :: visited
    let myEmitFlag := emitOnNew
    let supers := (H.defs tr).directSupers
    let (visited2, emit2, acc2) :=
      supers.foldl
        (fun (st : List TraitId × Bool × List VtblSegment) sup =>
          ih sup st.1 st.2.1 st.2.2)
        (visited1, emitOnNew, acc)
    let hasEnt := traitHasEntries H tr
    let emitVPtr := myEmitFlag && hasEnt
    let acc3 := VtblSegment.traitOwnEntries tr emitVPtr :: acc2
    let emit3 := emit2 || hasEnt
    (visited2, emit3, acc3)

def dfsVisitTrait (H : TraitHierarchy) (fuel : Nat) :
    TraitId → List TraitId → Bool → List VtblSegment →
    (List TraitId × Bool × List VtblSegment) :=
  Nat.repeat (dfsVisitStep H) fuel (fun _ visited emitOnNew acc => (visited, emitOnNew, acc))

/-- Compute the ordered vtable segments for `tr` in hierarchy `H`:
    always begins with `VtblSegment.metadataDSA`, followed by post-order supertrait
    segments with first-supertrait prefix reuse and secondary `TraitVPtr` flags. -/
def prepareVtableSegments (H : TraitHierarchy) (tr : TraitId) : List VtblSegment :=
  let (_, _, revSegs) := dfsVisitTrait H (H.maxDepth + 1) tr [] false []
  VtblSegment.metadataDSA :: revSegs.reverse

/-- Render one `VtblSegment` into concrete `VtblEntry` slots for concrete type `ty`.
    Mirrors `vtable_entries` (`vtable.rs:245-308`) and `vtable_allocation_provider`
    (`rustc_middle/src/ty/vtable.rs:120-152`). -/
def renderSegment (H : TraitHierarchy) (R : MethodResolver) (ty : ConcreteTy) :
    VtblSegment → List VtblEntry
  | .metadataDSA =>
    let dropEntry :=
      if ty.needsDrop then VtblEntry.metadataDropInPlace (some (.dropGlue ty))
      else VtblEntry.metadataDropInPlace none
    [dropEntry, VtblEntry.metadataSize ty.size, VtblEntry.metadataAlign ty.align]
  | .traitOwnEntries tr emitVPtr =>
    let methods := (H.defs tr).ownMethods.map fun m =>
      match R ty tr m with
      | some inst => VtblEntry.method inst
      | none => VtblEntry.vacant
    if emitVPtr then methods ++ [VtblEntry.traitVPtr tr] else methods

/-- Number of vtable slots occupied by a segment (depends only on `H`, independent of `ty`!). -/
def segmentSlotCount (H : TraitHierarchy) : VtblSegment → Nat
  | .metadataDSA => 3
  | .traitOwnEntries tr emitVPtr =>
    (H.defs tr).ownMethods.length + (if emitVPtr then 1 else 0)

theorem renderSegment_length (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (seg : VtblSegment) :
    (renderSegment H R ty seg).length = segmentSlotCount H seg := by
  cases seg with
  | metadataDSA =>
    unfold renderSegment segmentSlotCount
    cases ty.needsDrop <;> rfl
  | traitOwnEntries tr emitVPtr =>
    unfold renderSegment segmentSlotCount
    cases emitVPtr with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact length_map_eq _ _
    | true =>
      simp only [↓reduceIte]
      rw [length_append_eq, length_map_eq]
      rfl

/-- Full concrete vtable entry array for `(ty, tr)`. -/
def renderSegments (H : TraitHierarchy) (R : MethodResolver) (ty : ConcreteTy)
    (segs : List VtblSegment) : List VtblEntry :=
  segs.flatMap (renderSegment H R ty)

def vtableEntries (H : TraitHierarchy) (R : MethodResolver) (ty : ConcreteTy)
    (tr : TraitId) : List VtblEntry :=
  renderSegments H R ty (prepareVtableSegments H tr)

/-- Slot offset of the first method of `targetTr` in `srcTr`'s vtable.
    Mirrors `first_method_vtable_slot` (`vtable.rs:317-365`). -/
def firstMethodSlotAux (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat)
    (segs : List VtblSegment) : Option Nat :=
  segs.foldr
    (fun seg ih off =>
      match seg with
      | .metadataDSA => ih (off + 3)
      | .traitOwnEntries tr emitVPtr =>
        if tr = targetTr then some off
        else ih (off + segmentSlotCount H (.traitOwnEntries tr emitVPtr)))
    (fun _ => none)
    offset

theorem firstMethodSlotAux_nil (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat) :
    firstMethodSlotAux H targetTr offset [] = none := rfl

theorem firstMethodSlotAux_cons_dsa (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat)
    (rest : List VtblSegment) :
    firstMethodSlotAux H targetTr offset (.metadataDSA :: rest) =
      firstMethodSlotAux H targetTr (offset + 3) rest := rfl

theorem firstMethodSlotAux_cons_trait (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat)
    (tr : TraitId) (emitVPtr : Bool) (rest : List VtblSegment) :
    firstMethodSlotAux H targetTr offset (.traitOwnEntries tr emitVPtr :: rest) =
      (if tr = targetTr then some offset
       else firstMethodSlotAux H targetTr (offset + segmentSlotCount H (.traitOwnEntries tr emitVPtr)) rest) := rfl

def firstMethodVtableSlot (H : TraitHierarchy) (srcTr targetTr : TraitId) : Option Nat :=
  firstMethodSlotAux H targetTr 0 (prepareVtableSegments H srcTr)

/-- Slot index of method `m` (belonging to trait `methodTr`) when dispatched on `dyn dynTr`.
    Mirrors `resolve_associated_item` (`rustc_ty_utils/src/instance.rs:251-260`). -/
def virtualMethodSlot (H : TraitHierarchy) (dynTr methodTr : TraitId) (m : MethodId) : Option Nat :=
  match firstMethodVtableSlot H dynTr methodTr, findIndexOf m (H.defs methodTr).ownMethods with
  | some base, some off => some (base + off)
  | _, _ => none

/-- Mirrors `supertrait_vtable_slot` (`vtable.rs:371-444`):
    - `some none`      => prefix reuse (zero-cost upcast: keep vtable pointer!)
    - `some (some idx)` => load `TraitVPtr` at slot `idx` from source vtable!
    - `none`           => `targetTr` not found in `srcTr`'s supertrait segments. -/
def supertraitSlotAux (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat)
    (segs : List VtblSegment) : Option (Option Nat) :=
  segs.foldr
    (fun seg ih off =>
      match seg with
      | .metadataDSA => ih (off + 3)
      | .traitOwnEntries tr emitVPtr =>
        let afterOwn := off + (H.defs tr).ownMethods.length
        if tr = targetTr then
          if emitVPtr then some (some afterOwn) else some none
        else
          let nextOff := afterOwn + (if emitVPtr then 1 else 0)
          ih nextOff)
    (fun _ => none)
    offset

theorem supertraitSlotAux_nil (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat) :
    supertraitSlotAux H targetTr offset [] = none := rfl

theorem supertraitSlotAux_cons_dsa (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat)
    (rest : List VtblSegment) :
    supertraitSlotAux H targetTr offset (.metadataDSA :: rest) =
      supertraitSlotAux H targetTr (offset + 3) rest := rfl

theorem supertraitSlotAux_cons_trait (H : TraitHierarchy) (targetTr : TraitId) (offset : Nat)
    (tr : TraitId) (emitVPtr : Bool) (rest : List VtblSegment) :
    supertraitSlotAux H targetTr offset (.traitOwnEntries tr emitVPtr :: rest) =
      (let afterOwn := offset + (H.defs tr).ownMethods.length
       if tr = targetTr then
         if emitVPtr then some (some afterOwn) else some none
       else
         supertraitSlotAux H targetTr (afterOwn + (if emitVPtr then 1 else 0)) rest) := rfl

def supertraitVtableSlot (H : TraitHierarchy) (srcTr targetTr : TraitId) : Option (Option Nat) :=
  supertraitSlotAux H targetTr 0 (prepareVtableSegments H srcTr)

-- ============================================================================
-- Section 4: Universal Vtable Slot & Upcasting Soundness Theorems
-- ============================================================================

/-- Exact slot lookup in `renderSegments`: `firstMethodSlotAux` locates the exact
    `VtblEntry` rendered for any own method `m` of `targetTr`. -/
theorem firstMethodSlotAux_sound (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (targetTr : TraitId) (m : MethodId) (off : Nat)
    (segs : List VtblSegment) (prefixEntries : List VtblEntry)
    (base : Nat)
    (h_off : findIndexOf m (H.defs targetTr).ownMethods = some off)
    (h_slot : firstMethodSlotAux H targetTr prefixEntries.length segs = some base) :
    (prefixEntries ++ renderSegments H R ty segs)[base + off]? =
      some (match R ty targetTr m with | some inst => VtblEntry.method inst | none => VtblEntry.vacant) := by
  induction segs generalizing prefixEntries with
  | nil =>
    rw [firstMethodSlotAux_nil] at h_slot
    cases h_slot
  | cons seg rest ih =>
    cases seg with
    | metadataDSA =>
      rw [firstMethodSlotAux_cons_dsa] at h_slot
      have hlen : (prefixEntries ++ renderSegment H R ty .metadataDSA).length =
          prefixEntries.length + 3 := by
        rw [length_append_eq, renderSegment_length]
        rfl
      have h_slot' : firstMethodSlotAux H targetTr
          (prefixEntries ++ renderSegment H R ty .metadataDSA).length rest = some base := by
        rw [hlen]
        exact h_slot
      have hrec := ih (prefixEntries ++ renderSegment H R ty .metadataDSA) h_slot'
      simpa only [renderSegments, List.flatMap_cons, List.append_assoc] using hrec
    | traitOwnEntries tr emitVPtr =>
      rw [firstMethodSlotAux_cons_trait] at h_slot
      by_cases htr : tr = targetTr
      · simp only [htr, ↓reduceIte] at h_slot
        cases h_slot
        subst htr
        have hlt : off < (H.defs tr).ownMethods.length := findIndexOf_lt_length h_off
        have hget : (H.defs tr).ownMethods[off]? = some m := findIndexOf_getElem? h_off
        simp only [renderSegments, List.flatMap_cons]
        rw [getElem?_append_right_nat]
        have h_own_len :
            ((H.defs tr).ownMethods.map fun m' =>
              match R ty tr m' with | some inst => VtblEntry.method inst | none => VtblEntry.vacant).length =
            (H.defs tr).ownMethods.length := length_map_eq _ _
        have h_own_get :
            ((H.defs tr).ownMethods.map fun m' =>
              match R ty tr m' with | some inst => VtblEntry.method inst | none => VtblEntry.vacant)[off]? =
            some (match R ty tr m with | some inst => VtblEntry.method inst | none => VtblEntry.vacant) := by
          rw [getElem?_map_eq, hget]
          rfl
        unfold renderSegment
        cases emitVPtr with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [getElem?_append_left_nat]
          · exact h_own_get
          · rw [h_own_len]; exact hlt
        | true =>
          simp only [↓reduceIte, List.append_assoc]
          rw [getElem?_append_left_nat]
          · exact h_own_get
          · rw [h_own_len]; exact hlt
      · simp only [htr, ↓reduceIte] at h_slot
        have hlen : (prefixEntries ++ renderSegment H R ty (.traitOwnEntries tr emitVPtr)).length =
            prefixEntries.length + segmentSlotCount H (.traitOwnEntries tr emitVPtr) := by
          rw [length_append_eq, renderSegment_length]
        have h_slot' : firstMethodSlotAux H targetTr
            (prefixEntries ++ renderSegment H R ty (.traitOwnEntries tr emitVPtr)).length rest = some base := by
          rw [hlen]
          exact h_slot
        have hrec := ih (prefixEntries ++ renderSegment H R ty (.traitOwnEntries tr emitVPtr)) h_slot'
        simpa only [renderSegments, List.flatMap_cons, List.append_assoc] using hrec

/-- Universal virtual dispatch soundness: looking up `virtualMethodSlot H dynTr methodTr m`
    inside `vtableEntries H R ty dynTr` ALWAYS returns the exact concrete `R ty methodTr m`! -/
theorem virtualMethodSlot_sound (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (dynTr methodTr : TraitId) (m : MethodId) (slot : Nat)
    (h_slot : virtualMethodSlot H dynTr methodTr m = some slot) :
    (vtableEntries H R ty dynTr)[slot]? =
      some (match R ty methodTr m with | some inst => VtblEntry.method inst | none => VtblEntry.vacant) := by
  unfold virtualMethodSlot at h_slot
  cases h_base : firstMethodVtableSlot H dynTr methodTr with
  | none =>
    rw [h_base] at h_slot
    cases h_slot
  | some base =>
    rw [h_base] at h_slot
    cases h_off : findIndexOf m (H.defs methodTr).ownMethods with
    | none =>
      rw [h_off] at h_slot
      cases h_slot
    | some off =>
      rw [h_off] at h_slot
      cases h_slot
      have h := firstMethodSlotAux_sound H R ty methodTr m off (prepareVtableSegments H dynTr) [] base h_off h_base
      simpa only [List.nil_append, vtableEntries] using h

/-- Exact `TraitVPtr` lookup theorem: whenever `supertraitSlotAux` returns `some (some idx)`,
    slot `idx` in the rendered vtable is literally `VtblEntry.traitVPtr targetTr`! -/
theorem supertraitSlotAux_vptr_sound (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (targetTr : TraitId)
    (segs : List VtblSegment) (prefixEntries : List VtblEntry) (idx : Nat)
    (h_slot : supertraitSlotAux H targetTr prefixEntries.length segs = some (some idx)) :
    (prefixEntries ++ renderSegments H R ty segs)[idx]? = some (VtblEntry.traitVPtr targetTr) := by
  induction segs generalizing prefixEntries with
  | nil =>
    rw [supertraitSlotAux_nil] at h_slot
    cases h_slot
  | cons seg rest ih =>
    cases seg with
    | metadataDSA =>
      rw [supertraitSlotAux_cons_dsa] at h_slot
      have hlen : (prefixEntries ++ renderSegment H R ty .metadataDSA).length =
          prefixEntries.length + 3 := by
        rw [length_append_eq, renderSegment_length]
        rfl
      have h_slot' : supertraitSlotAux H targetTr
          (prefixEntries ++ renderSegment H R ty .metadataDSA).length rest = some (some idx) := by
        rw [hlen]
        exact h_slot
      have hrec := ih (prefixEntries ++ renderSegment H R ty .metadataDSA) h_slot'
      simpa only [renderSegments, List.flatMap_cons, List.append_assoc] using hrec
    | traitOwnEntries tr emitVPtr =>
      rw [supertraitSlotAux_cons_trait] at h_slot
      by_cases htr : tr = targetTr
      · simp only [htr, ↓reduceIte] at h_slot
        cases emitVPtr with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h_slot
          cases h_slot
        | true =>
          simp only [↓reduceIte] at h_slot
          cases h_slot
          subst htr
          simp only [renderSegments, List.flatMap_cons, renderSegment, ↓reduceIte]
          rw [getElem?_append_right_nat]
          rw [List.append_assoc]
          have h_own_len :
              ((H.defs tr).ownMethods.map fun m' =>
                match R ty tr m' with | some inst => VtblEntry.method inst | none => VtblEntry.vacant).length =
              (H.defs tr).ownMethods.length := length_map_eq _ _
          rw [← h_own_len]
          have h0 := getElem?_append_right_nat
            ((H.defs tr).ownMethods.map fun m' =>
              match R ty tr m' with | some inst => VtblEntry.method inst | none => VtblEntry.vacant)
            ([VtblEntry.traitVPtr tr] ++ renderSegments H R ty rest)
            0
          simp only [Nat.add_zero, List.cons_append, List.getElem?_cons_zero] at h0
          exact h0
      · simp only [htr, ↓reduceIte] at h_slot
        have hlen : (prefixEntries ++ renderSegment H R ty (.traitOwnEntries tr emitVPtr)).length =
            prefixEntries.length + (H.defs tr).ownMethods.length + (if emitVPtr then 1 else 0) := by
          rw [length_append_eq, renderSegment_length]
          unfold segmentSlotCount
          rw [Nat.add_assoc]
        have h_slot' : supertraitSlotAux H targetTr
            (prefixEntries ++ renderSegment H R ty (.traitOwnEntries tr emitVPtr)).length rest = some (some idx) := by
          rw [hlen]
          exact h_slot
        have hrec := ih (prefixEntries ++ renderSegment H R ty (.traitOwnEntries tr emitVPtr)) h_slot'
        simpa only [renderSegments, List.flatMap_cons, List.append_assoc] using hrec

theorem supertraitVtableSlot_vptr_sound (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (srcTr targetTr : TraitId) (idx : Nat)
    (h_slot : supertraitVtableSlot H srcTr targetTr = some (some idx)) :
    (vtableEntries H R ty srcTr)[idx]? = some (VtblEntry.traitVPtr targetTr) := by
  have h := supertraitSlotAux_vptr_sound H R ty targetTr (prepareVtableSegments H srcTr) [] idx h_slot
  simpa only [List.nil_append, vtableEntries] using h

/-- Slot 0 of ANY vtable is always `MetadataDropInPlace` (non-null `dropGlue ty` iff `ty.needsDrop`). -/
theorem vtableEntries_slot0_drop (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (tr : TraitId) :
    (vtableEntries H R ty tr)[0]? =
      some (VtblEntry.metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none)) := by
  unfold vtableEntries prepareVtableSegments renderSegments
  simp only [List.flatMap_cons, renderSegment]
  cases ty.needsDrop <;> rfl

/-- Slot 1 is `metadataSize ty.size` and slot 2 is `metadataAlign ty.align`. -/
theorem vtableEntries_slot1_size (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (tr : TraitId) :
    (vtableEntries H R ty tr)[1]? = some (VtblEntry.metadataSize ty.size) := by
  unfold vtableEntries prepareVtableSegments renderSegments
  simp only [List.flatMap_cons, renderSegment]
  cases ty.needsDrop <;> rfl

theorem vtableEntries_slot2_align (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (tr : TraitId) :
    (vtableEntries H R ty tr)[2]? = some (VtblEntry.metadataAlign ty.align) := by
  unfold vtableEntries prepareVtableSegments renderSegments
  simp only [List.flatMap_cons, renderSegment]
  cases ty.needsDrop <;> rfl

/-- Segment-prefix property: `targetTr`'s segment list is a prefix of `srcTr`'s segment list. -/
def SegmentsPrefix (xs ys : List VtblSegment) : Prop :=
  ∃ suffix, ys = xs ++ suffix

/-- Universal Prefix-Reuse Theorem: whenever `prepareVtableSegments H targetTr` is a prefix of
    `prepareVtableSegments H srcTr`, EVERY slot `i` valid in `vtable(ty, targetTr)` agrees
    identically in `vtable(ty, srcTr)`. -/
theorem prefix_vtable_entries_agree (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (srcTr targetTr : TraitId)
    (h_pref : SegmentsPrefix (prepareVtableSegments H targetTr) (prepareVtableSegments H srcTr))
    (i : Nat) (h_lt : i < (vtableEntries H R ty targetTr).length) :
    (vtableEntries H R ty srcTr)[i]? = (vtableEntries H R ty targetTr)[i]? := by
  rcases h_pref with ⟨suffix, h_eq⟩
  unfold vtableEntries renderSegments at h_lt ⊢
  rw [h_eq, List.flatMap_append]
  exact getElem?_append_left_nat _ _ i h_lt

/-- Operational vtable pointer upcast step mirroring `rustc_codegen_ssa::base::unsized_info`
    (`compiler/rustc_codegen_ssa/src/base.rs:202-210`).
    Given runtime vtable entries `vt` (with concrete backing type `ty`), upcasting
    `dyn srcTr -> dyn targetTr`:
    - returns `vt` unchanged when `supertraitVtableSlot H srcTr targetTr = some none` (zero-cost prefix reuse);
    - loads `VtblEntry.traitVPtr superTr` at slot `idx` and resolves `vtableStore (ty, superTr)` when
      `supertraitVtableSlot H srcTr targetTr = some (some idx)`. -/
def upcastVtable (H : TraitHierarchy)
    (vtableStore : ConcreteTy → TraitId → Option (List VtblEntry))
    (ty : ConcreteTy) (srcTr targetTr : TraitId) (srcVt : List VtblEntry) :
    Option (List VtblEntry) :=
  match supertraitVtableSlot H srcTr targetTr with
  | none => none
  | some none => some srcVt
  | some (some idx) =>
    match srcVt[idx]? with
    | some (.traitVPtr superTr) => vtableStore ty superTr
    | _ => none

/-- A vtable store is faithful to `(H, R)` on `(ty, tr)` if it holds `vtableEntries H R ty tr`. -/
def VtableStoreFaithful (H : TraitHierarchy) (R : MethodResolver)
    (store : ConcreteTy → TraitId → Option (List VtblEntry)) : Prop :=
  ∀ ty tr, store ty tr = some (vtableEntries H R ty tr)

/-- Prefix-coherent trait hierarchy: whenever `supertraitVtableSlot` reports prefix reuse
    (`some none`), `targetTr`'s segments genuinely form a prefix of `srcTr`'s segments. -/
def PrefixCoherent (H : TraitHierarchy) (srcTr targetTr : TraitId) : Prop :=
  supertraitVtableSlot H srcTr targetTr = some none →
    SegmentsPrefix (prepareVtableSegments H targetTr) (prepareVtableSegments H srcTr)

/-- **Universal `dyn` Trait Upcasting Dispatch Soundness Theorem:**
    For ANY hierarchy `H`, resolver `R`, concrete type `ty`, upcast `srcTr -> targetTr`
    satisfying `PrefixCoherent H srcTr targetTr`, and ANY method `m` of any supertrait `methodTr`
    of `targetTr` at slot `slot`:
    1. `upcastVtable` succeeds with an upcasted vtable `dstVt`;
    2. Dispatching `slot` through `dstVt` resolves to the **exact same** `VtblEntry`
       (`R ty methodTr m`) as direct concrete resolution;
    3. Slot `0` of `dstVt` resolves to the **exact same** `MetadataDropInPlace`
       (`dropGlue ty` if `ty.needsDrop`, else `null`)! -/
theorem upcast_dispatch_and_drop_sound
    (H : TraitHierarchy) (R : MethodResolver)
    (store : ConcreteTy → TraitId → Option (List VtblEntry))
    (h_store : VtableStoreFaithful H R store)
    (ty : ConcreteTy) (srcTr targetTr methodTr : TraitId) (m : MethodId) (slot : Nat)
    (h_coh : PrefixCoherent H srcTr targetTr)
    (h_up : supertraitVtableSlot H srcTr targetTr ≠ none)
    (h_mslot : virtualMethodSlot H targetTr methodTr m = some slot) :
    ∃ dstVt,
      upcastVtable H store ty srcTr targetTr (vtableEntries H R ty srcTr) = some dstVt ∧
      dstVt[slot]? =
        some (match R ty methodTr m with | some inst => VtblEntry.method inst | none => VtblEntry.vacant) ∧
      dstVt[0]? =
        some (VtblEntry.metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none)) := by
  have h_target_slot := virtualMethodSlot_sound H R ty targetTr methodTr m slot h_mslot
  cases h_sv : supertraitVtableSlot H srcTr targetTr with
  | none => exact False.elim (h_up h_sv)
  | some optIdx =>
    cases optIdx with
    | none =>
      refine ⟨vtableEntries H R ty srcTr, ?_, ?_, vtableEntries_slot0_drop H R ty srcTr⟩
      · unfold upcastVtable; rw [h_sv]
      · have h_pref := h_coh h_sv
        have h_lt : slot < (vtableEntries H R ty targetTr).length := by
          cases h_len : (vtableEntries H R ty targetTr)[slot]? with
          | none =>
            rw [h_len] at h_target_slot
            cases h_target_slot
          | some _ =>
            exact List.getElem?_eq_some_iff.mp h_len |>.1
        rw [prefix_vtable_entries_agree H R ty srcTr targetTr h_pref slot h_lt]
        exact h_target_slot
    | some idx =>
      have h_vptr := supertraitVtableSlot_vptr_sound H R ty srcTr targetTr idx h_sv
      refine ⟨vtableEntries H R ty targetTr, ?_, h_target_slot, vtableEntries_slot0_drop H R ty targetTr⟩
      unfold upcastVtable
      rw [h_sv]
      dsimp only
      rw [h_vptr]
      exact h_store ty targetTr

-- ============================================================================
-- Section 5: Monomorphization Collector Reachability & Link-Completeness
-- ============================================================================

/-- Mirrors `create_mono_items_for_vtable_methods` (`collector.rs:1208-1254`):
    collects every `VtblEntry.method inst` in `vtableEntries H R ty tr` (skipping
    `TraitVPtr`!) plus `dropGlue ty` if `ty.needsDrop = true`. -/
def vtableCollectedMethods (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (tr : TraitId) : List InstanceKind :=
  let entries := vtableEntries H R ty tr
  let meths := entries.flatMap fun e =>
    match e with
    | .method inst => [inst]
    | _ => []
  if ty.needsDrop then .dropGlue ty :: meths else meths

/-- Extract all secondary supertrait `TraitId`s referenced by `VtblEntry.traitVPtr` in `vtable(ty, tr)`. -/
def vtableEmbeddedSupertraits (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (tr : TraitId) : List TraitId :=
  (vtableEntries H R ty tr).flatMap fun e =>
    match e with
    | .traitVPtr sup => [sup]
    | _ => []

/-- **Why `collector.rs:1235-1238` Safely Skips `VtblEntry::TraitVPtr`:**
    Whenever every trait segment appearing in `prepareVtableSegments H superTr` also
    appears as a `traitOwnEntries` segment in `prepareVtableSegments H srcTr`,
    EVERY method `inst` in `vtableEntries H R ty superTr` is ALREADY in
    `vtableCollectedMethods H R ty srcTr`! -/
def SupertraitSegmentsCovered (H : TraitHierarchy) (srcTr superTr : TraitId) : Prop :=
  ∀ tr emitB,
    VtblSegment.traitOwnEntries tr emitB ∈ prepareVtableSegments H superTr →
    ∃ emitA, VtblSegment.traitOwnEntries tr emitA ∈ prepareVtableSegments H srcTr

theorem renderSegment_method_iff_ignore_vptr (H : TraitHierarchy) (R : MethodResolver)
    (ty : ConcreteTy) (tr : TraitId) (emit1 emit2 : Bool) (inst : InstanceKind)
    (h : VtblEntry.method inst ∈ renderSegment H R ty (.traitOwnEntries tr emit1)) :
    VtblEntry.method inst ∈ renderSegment H R ty (.traitOwnEntries tr emit2) := by
  unfold renderSegment at h ⊢
  have h_in_own : VtblEntry.method inst ∈
      ((H.defs tr).ownMethods.map fun m =>
        match R ty tr m with | some i => VtblEntry.method i | none => VtblEntry.vacant) := by
    cases emit1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact h
    | true =>
      simp only [↓reduceIte] at h
      cases mem_of_mem_append h with
      | inl hl => exact hl
      | inr hr =>
        cases hr with
        | tail _ hnil => cases hnil
  cases emit2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact h_in_own
  | true =>
    simp only [↓reduceIte]
    exact mem_append_left_of_mem h_in_own

theorem vtableCollectedMethods_covers_supertrait
    (H : TraitHierarchy) (R : MethodResolver) (ty : ConcreteTy)
    (srcTr superTr : TraitId) (inst : InstanceKind)
    (h_cov : SupertraitSegmentsCovered H srcTr superTr)
    (h_in : VtblEntry.method inst ∈ vtableEntries H R ty superTr) :
    inst ∈ vtableCollectedMethods H R ty srcTr := by
  unfold vtableEntries renderSegments at h_in
  rcases mem_of_mem_flatMap h_in with ⟨seg, h_seg_in, h_ent_in⟩
  have h_in_src : VtblEntry.method inst ∈ vtableEntries H R ty srcTr := by
    cases seg with
    | metadataDSA =>
      unfold renderSegment at h_ent_in
      cases h_nd : ty.needsDrop <;>
        (simp only [h_nd, Bool.false_eq_true, ↓reduceIte] at h_ent_in
         cases h_ent_in with
         | tail _ h1 =>
           cases h1 with
           | tail _ h2 =>
             cases h2 with
             | tail _ h3 => cases h3)
    | traitOwnEntries tr emitB =>
      rcases h_cov tr emitB h_seg_in with ⟨emitA, h_seg_src⟩
      have h_ent_src := renderSegment_method_iff_ignore_vptr H R ty tr emitB emitA inst h_ent_in
      unfold vtableEntries renderSegments
      exact mem_flatMap_of_mem h_seg_src h_ent_src
  unfold vtableCollectedMethods
  have h_m : inst ∈ (vtableEntries H R ty srcTr).flatMap (fun e => match e with | .method i => [i] | _ => []) :=
    mem_flatMap_of_mem h_in_src (List.Mem.head _)
  cases ty.needsDrop with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact h_m
  | true =>
    simp only [↓reduceIte]
    exact List.Mem.tail _ h_m

/-- Operational MIR-level operations executed inside a monomorphized body. -/
inductive MonoOp where
  | directCall (callee : InstanceKind)
  | reifyFnPtr (fnId : FnId) (tyArg : TyId) (trackCaller : Bool) (loc : LocId)
  | reifyVirtualFnPtr (tr : TraitId) (slotIdx : Nat) (loc : LocId)
  | unsizeToDyn (ty : ConcreteTy) (tr : TraitId)
  | upcastDyn (srcTr targetTr : TraitId)
  | virtualDispatch (tr : TraitId) (slotIdx : Nat)
  | dropConcrete (ty : ConcreteTy)
  | reifyDropFnPtr (ty : ConcreteTy)
  | dropDyn
  | closureAsFnOnce (fnId : FnId) (tyArg : TyId)
  | fnPtrAsFnTrait (fnId : FnId) (tyArg : TyId)
  deriving DecidableEq, Repr

/-- A monomorphized crate program: trait hierarchy, method resolver, bodies of items,
    and collection roots (distinguishing `Lazy` vs `Eager`). -/
structure MonoProgram where
  H : TraitHierarchy
  R : MethodResolver
  bodyOf : InstanceKind → List MonoOp
  roots : List InstanceKind

/-- Direct mono-item dependencies extracted by `MirUsedCollector` from one `MonoOp`
    (`compiler/rustc_monomorphize/src/collector.rs:726-973`). -/
def opUsedMonoItems (P : MonoProgram) : MonoOp → List InstanceKind
  | .directCall callee => [callee]
  | .reifyFnPtr fnId tyArg trackCaller loc =>
    if trackCaller then [.reifyShim fnId tyArg loc] else [.item fnId tyArg]
  | .reifyVirtualFnPtr tr slotIdx loc =>
    -- Mirrors `resolve_for_fn_ptr` on `InstanceKind::Virtual`: emits `ReifyShim`.
    [.reifyShim tr slotIdx loc]
  | .unsizeToDyn ty tr =>
    vtableCollectedMethods P.H P.R ty tr
  | .upcastDyn _ _ => []
  | .virtualDispatch _ _ => []
  | .dropConcrete ty =>
    if ty.needsDrop then [.dropGlue ty] else []
  | .reifyDropFnPtr ty =>
    -- Mirrors `collector.rs:1019-1026`: indirect `DropGlue(_, None)` IS emitted!
    [.dropGlue ty]
  | .dropDyn => []
  | .closureAsFnOnce fnId tyArg => [.closureOnceShim fnId tyArg]
  | .fnPtrAsFnTrait fnId tyArg => [.fnPtrShim fnId tyArg]

/-- Direct mono-item edges from an `InstanceKind`, including compiler-generated shim bodies! -/
def directMonoEdges (P : MonoProgram) (u : InstanceKind) : List InstanceKind :=
  match u with
  | .vtableShim fnId tyArg => [.item fnId tyArg]
  | .reifyShim fnId tyArg _ => [.item fnId tyArg]
  | .closureOnceShim fnId tyArg => [.item fnId tyArg]
  | .fnPtrShim fnId tyArg => [.item fnId tyArg]
  | .dropGlue ty => (P.bodyOf (.dropGlue ty)).flatMap (opUsedMonoItems P)
  | .item fnId tyArg => (P.bodyOf (.item fnId tyArg)).flatMap (opUsedMonoItems P)
  | .virtualCall _ _ => []

/-- Inductive monomorphization reachability closure (`MonoReachable`).
    Models the fixed point of `collect_crate_mono_items` (`collector.rs:1807-1839`). -/
inductive MonoReachable (P : MonoProgram) : InstanceKind → Prop where
  | root {inst} : inst ∈ P.roots → MonoReachable P inst
  | step {u v} : MonoReachable P u → v ∈ directMonoEdges P u → MonoReachable P v

/-- Vtable reachability closure (`VtableReachable`):
    every `(ty, tr)` constructed by `unsizeToDyn` in a reachable body, closed under
    embedded `TraitVPtr` supertrait pointers (`vtable_allocation_provider`, `vtable.rs:142-147`). -/
inductive VtableReachable (P : MonoProgram) : ConcreteTy → TraitId → Prop where
  | fromUnsize {u ty tr} :
      MonoReachable P u →
      MonoOp.unsizeToDyn ty tr ∈ P.bodyOf u →
      VtableReachable P ty tr
  | fromTraitVPtr {ty srcTr superTr} :
      VtableReachable P ty srcTr →
      superTr ∈ vtableEmbeddedSupertraits P.H P.R ty srcTr →
      VtableReachable P ty superTr

/-- **Lazy ⊆ Eager Monotonicity Theorem:**
    Adding eager roots (unused non-generic fns, unused ADT drop glues, default trait methods)
    monotonically enlarges `MonoReachable`. -/
theorem monoReachable_monotone_roots (P1 P2 : MonoProgram)
    (hH : P1.H = P2.H) (hR : P1.R = P2.R) (hB : P1.bodyOf = P2.bodyOf)
    (hSub : ∀ r, r ∈ P1.roots → r ∈ P2.roots) :
    ∀ inst, MonoReachable P1 inst → MonoReachable P2 inst := by
  have hEdges : ∀ u, directMonoEdges P1 u = directMonoEdges P2 u := by
    intro u
    cases P1; cases P2
    simp only at hH hR hB
    subst hH; subst hR; subst hB
    rfl
  intro inst h
  induction h with
  | root hr => exact MonoReachable.root (hSub _ hr)
  | step _ hedge ih =>
    rw [hEdges] at hedge
    exact MonoReachable.step ih hedge

-- ============================================================================
-- Section 6: Link Table, Operational Machine, and Link-Completeness Proof
-- ============================================================================

/-- Runtime faults detectable when executing a linked binary. -/
inductive RuntimeFault where
  | missingSymbol (inst : InstanceKind)
  | missingVtable (ty : ConcreteTy) (tr : TraitId)
  | badSlotEntry (slotIdx : Nat)
  | wrongDispatch (expected actual : InstanceKind)
  deriving DecidableEq, Repr

/-- Runtime wide-pointer value `(concreteTy, currentTrait, vtableEntries)` carried in the machine state. -/
structure DynObj where
  ty : ConcreteTy
  curTrait : TraitId
  vt : List VtblEntry

/-- Machine state: currently active callable, remaining ops in its frame, optional current `dyn` object,
    and optional reified `fn` pointer. -/
structure ExecState where
  curFn : InstanceKind
  ops : List MonoOp
  dynVal : Option DynObj
  fnPtrVal : Option InstanceKind

inductive StepOutcome where
  | ok (st : ExecState)
  | halted
  | fault (err : RuntimeFault)

/-- Executable decidable link artifact (using finite symbol list and vtable store). -/
structure DecLinkArtifact where
  symbols : List InstanceKind
  vtableOf : ConcreteTy → TraitId → Option (List VtblEntry)

def execStepDec (P : MonoProgram) (L : DecLinkArtifact) (st : ExecState) : StepOutcome :=
  match st.ops with
  | [] => .halted
  | op :: rest =>
    match op with
    | .directCall callee =>
      if callee ∈ L.symbols then .ok { st with ops := rest }
      else .fault (.missingSymbol callee)
    | .reifyFnPtr fnId tyArg trackCaller loc =>
      let sym := if trackCaller then InstanceKind.reifyShim fnId tyArg loc else InstanceKind.item fnId tyArg
      if sym ∈ L.symbols then .ok { st with ops := rest, fnPtrVal := some sym }
      else .fault (.missingSymbol sym)
    | .reifyVirtualFnPtr tr slotIdx loc =>
      let sym := InstanceKind.reifyShim tr slotIdx loc
      if sym ∈ L.symbols then .ok { st with ops := rest, fnPtrVal := some sym }
      else .fault (.missingSymbol sym)
    | .unsizeToDyn ty tr =>
      match L.vtableOf ty tr with
      | none => .fault (.missingVtable ty tr)
      | some vt => .ok { st with ops := rest, dynVal := some { ty := ty, curTrait := tr, vt := vt } }
    | .upcastDyn srcTr targetTr =>
      match st.dynVal with
      | none => .ok { st with ops := rest }
      | some obj =>
        match supertraitVtableSlot P.H srcTr targetTr with
        | none => .ok { st with ops := rest }
        | some none => .ok { st with ops := rest, dynVal := some { obj with curTrait := targetTr } }
        | some (some idx) =>
          match obj.vt[idx]? with
          | some (.traitVPtr superTr) =>
            match L.vtableOf obj.ty superTr with
            | none => .fault (.missingVtable obj.ty superTr)
            | some newVt => .ok { st with ops := rest, dynVal := some { obj with curTrait := superTr, vt := newVt } }
          | _ => .fault (.badSlotEntry idx)
    | .virtualDispatch _ slotIdx =>
      match st.dynVal with
      | none => .ok { st with ops := rest }
      | some obj =>
        match obj.vt[slotIdx]? with
        | some (.method inst) =>
          if inst ∈ L.symbols then .ok { st with ops := rest }
          else .fault (.missingSymbol inst)
        | _ => .fault (.badSlotEntry slotIdx)
    | .dropConcrete ty =>
      if ty.needsDrop then
        if (.dropGlue ty) ∈ L.symbols then .ok { st with ops := rest }
        else .fault (.missingSymbol (.dropGlue ty))
      else .ok { st with ops := rest }
    | .reifyDropFnPtr ty =>
      if (.dropGlue ty) ∈ L.symbols then .ok { st with ops := rest, fnPtrVal := some (.dropGlue ty) }
      else .fault (.missingSymbol (.dropGlue ty))
    | .dropDyn =>
      match st.dynVal with
      | none => .ok { st with ops := rest }
      | some obj =>
        match obj.vt[0]? with
        | some (VtblEntry.metadataDropInPlace none) => .ok { st with ops := rest }
        | some (VtblEntry.metadataDropInPlace (some g)) =>
          if g ∈ L.symbols then .ok { st with ops := rest }
          else .fault (.missingSymbol g)
        | _ => .fault (.badSlotEntry 0)
    | .closureAsFnOnce fnId tyArg =>
      let sym := InstanceKind.closureOnceShim fnId tyArg
      if sym ∈ L.symbols then .ok { st with ops := rest }
      else .fault (.missingSymbol sym)
    | .fnPtrAsFnTrait fnId tyArg =>
      let sym := InstanceKind.fnPtrShim fnId tyArg
      if sym ∈ L.symbols then .ok { st with ops := rest }
      else .fault (.missingSymbol sym)

def execStepsStep (P : MonoProgram) (L : DecLinkArtifact)
    (ih : ExecState → StepOutcome) (s : ExecState) : StepOutcome :=
  match execStepDec P L s with
  | .ok s' => ih s'
  | .halted => .halted
  | .fault err => .fault err

def execStepsDec (P : MonoProgram) (L : DecLinkArtifact) (fuel : Nat) (st : ExecState) : StepOutcome :=
  Nat.repeat (execStepsStep P L) fuel StepOutcome.ok st

theorem execStepsDec_zero (P : MonoProgram) (L : DecLinkArtifact) (st : ExecState) :
    execStepsDec P L 0 st = .ok st := rfl

theorem execStepsDec_succ (P : MonoProgram) (L : DecLinkArtifact) (fuel : Nat) (st : ExecState) :
    execStepsDec P L (fuel + 1) st =
      match execStepDec P L st with
      | .ok s' => execStepsDec P L fuel s'
      | .halted => .halted
      | .fault err => .fault err := rfl

/-- A `DecLinkArtifact` is *collector-complete* for `P` when:
    1. Every `MonoReachable P inst` is present in `L.symbols`;
    2. Every `VtableReachable P ty tr` is materialized accurately in `L.vtableOf ty tr`. -/
structure CollectorComplete (P : MonoProgram) (L : DecLinkArtifact) : Prop where
  symbolsComplete : ∀ inst, MonoReachable P inst → inst ∈ L.symbols
  vtablesComplete : ∀ ty tr, VtableReachable P ty tr →
    L.vtableOf ty tr = some (vtableEntries P.H P.R ty tr)

/-- Well-typedness invariant on a program `P` (guaranteed by Rust's typechecker + MIR borrow/type checks):
    1. Every `upcastDyn srcTr targetTr` and `virtualDispatch tr slotIdx` is well-typed with respect
       to the current `dyn` object's trait `curTrait`;
    2. Every supertrait referenced by `TraitVPtr` has its method segments covered by the source trait
       (so `vtableCollectedMethods` of the concrete `unsizeToDyn` already collected every supertrait method);
    3. Every `PrefixCoherent` upcast maintains exact slot agreement. -/
structure ProgramWellTyped (P : MonoProgram) : Prop where
  supertraitCovered : ∀ srcTr superTr ty,
    superTr ∈ vtableEmbeddedSupertraits P.H P.R ty srcTr →
    SupertraitSegmentsCovered P.H srcTr superTr
  prefixCoherent : ∀ srcTr targetTr, PrefixCoherent P.H srcTr targetTr
  bodyCallableKind : ∀ inst, MonoReachable P inst →
    P.bodyOf inst ≠ [] → (∃ fnId tyArg, inst = .item fnId tyArg) ∨ (∃ ty, inst = .dropGlue ty)

/-- Runtime typing invariant on `ExecState` during execution of a reachable item `st.curFn`:
    - `st.curFn` is `MonoReachable P`,
    - every remaining `op ∈ st.ops` belongs to `P.bodyOf st.curFn`,
    - if `st.dynVal = some obj`, then `obj.vt = vtableEntries P.H P.R obj.ty obj.curTrait`
      (or has a valid prefix/secondary vtable whose methods and drop glue are all `MonoReachable P`
      and whose embedded `TraitVPtr` supertraits are all `VtableReachable P`!),
    - every `upcastDyn` matches `obj.curTrait` and every `virtualDispatch` targets a valid
      non-vacant method slot of `obj.curTrait`. -/
structure DynObjValid (P : MonoProgram) (obj : DynObj) : Prop where
  vtMatches : ∃ backingTr,
    VtableReachable P obj.ty backingTr ∧
    obj.vt = vtableEntries P.H P.R obj.ty backingTr ∧
    (backingTr = obj.curTrait ∨ SegmentsPrefix (prepareVtableSegments P.H obj.curTrait) (prepareVtableSegments P.H backingTr))
  allMethodsReachable : ∀ inst, VtblEntry.method inst ∈ obj.vt → MonoReachable P inst
  dropReachable : obj.ty.needsDrop = true → MonoReachable P (.dropGlue obj.ty)

structure StateValid (P : MonoProgram) (st : ExecState) : Prop where
  curReachable : MonoReachable P st.curFn
  opsSubset : ∀ op, op ∈ st.ops → op ∈ P.bodyOf st.curFn
  dynValid : ∀ obj, st.dynVal = some obj → DynObjValid P obj
  opTyped : ∀ op, op ∈ st.ops →
    match op with
    | .upcastDyn srcTr _ =>
      ∀ obj, st.dynVal = some obj → obj.curTrait = srcTr
    | .virtualDispatch tr slotIdx =>
      ∀ obj, st.dynVal = some obj →
        obj.curTrait = tr ∧
        ∃ inst, (vtableEntries P.H P.R obj.ty tr)[slotIdx]? = some (.method inst)
    | _ => True

/-- Helper: if `u` is `MonoReachable P` with callable body and `op ∈ P.bodyOf u`,
    then every `v ∈ opUsedMonoItems P op` is `MonoReachable P`. -/
theorem monoReachable_of_body_op (P : MonoProgram) (hWT : ProgramWellTyped P)
    {u : InstanceKind} {op : MonoOp} {v : InstanceKind}
    (h_u : MonoReachable P u)
    (h_op : op ∈ P.bodyOf u)
    (h_v : v ∈ opUsedMonoItems P op) :
    MonoReachable P v := by
  have h_nonempty : P.bodyOf u ≠ [] := by
    intro hnil
    rw [hnil] at h_op
    cases h_op
  have h_edge : v ∈ directMonoEdges P u := by
    cases hWT.bodyCallableKind u h_u h_nonempty with
    | inl hitem =>
      rcases hitem with ⟨fnId, tyArg, rfl⟩
      unfold directMonoEdges
      exact mem_flatMap_of_mem h_op h_v
    | inr hdrop =>
      rcases hdrop with ⟨ty, rfl⟩
      unfold directMonoEdges
      exact mem_flatMap_of_mem h_op h_v
  exact MonoReachable.step h_u h_edge

/-- Helper: if `SegmentsPrefix (prepareVtableSegments H curTr) (prepareVtableSegments H backTr)`,
    then `supertraitVtableSlot H curTr targetTr` agrees with `supertraitVtableSlot H backTr targetTr`
    on any `targetTr` present in `curTr`'s segments! -/
theorem supertraitSlotAux_prefix_agree (H : TraitHierarchy) (targetTr : TraitId)
    (off : Nat) (xs ys : List VtblSegment) (res : Option Nat)
    (h : supertraitSlotAux H targetTr off xs = some res) :
    supertraitSlotAux H targetTr off (xs ++ ys) = some res := by
  induction xs generalizing off with
  | nil =>
    rw [supertraitSlotAux_nil] at h
    cases h
  | cons seg rest ih =>
    cases seg with
    | metadataDSA =>
      rw [List.cons_append, supertraitSlotAux_cons_dsa]
      rw [supertraitSlotAux_cons_dsa] at h
      exact ih (off + 3) h
    | traitOwnEntries tr emitVPtr =>
      rw [List.cons_append, supertraitSlotAux_cons_trait]
      rw [supertraitSlotAux_cons_trait] at h
      by_cases htr : tr = targetTr
      · simp only [htr, ↓reduceIte] at h ⊢
        exact h
      · simp only [htr, ↓reduceIte] at h ⊢
        exact ih _ h

theorem segmentsPrefix_trans {a b c : List VtblSegment}
    (h1 : SegmentsPrefix a b) (h2 : SegmentsPrefix b c) :
    SegmentsPrefix a c := by
  rcases h1 with ⟨s1, rfl⟩
  rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, by rw [List.append_assoc]⟩

/-- Single-step link-completeness + preservation of `DynObjValid`:
    under `CollectorComplete P L` and `ProgramWellTyped P`, a valid state `st`
    NEVER faults on `execStepDec P L st`! -/
theorem execStepDec_no_fault (P : MonoProgram) (L : DecLinkArtifact)
    (hWT : ProgramWellTyped P) (hCC : CollectorComplete P L)
    (st : ExecState) (hV : StateValid P st) :
    match execStepDec P L st with
    | .fault _ => False
    | .halted => True
    | .ok st' =>
      MonoReachable P st'.curFn ∧
      (∀ op, op ∈ st'.ops → op ∈ P.bodyOf st'.curFn) ∧
      (∀ obj, st'.dynVal = some obj → DynObjValid P obj) := by
  cases h_ops : st.ops with
  | nil =>
    unfold execStepDec
    rw [h_ops]
    trivial
  | cons op rest =>
    have h_op_mem : op ∈ P.bodyOf st.curFn := hV.opsSubset op (by rw [h_ops]; exact List.Mem.head _)
    have h_rest_mem : ∀ o, o ∈ rest → o ∈ P.bodyOf st.curFn := fun o ho =>
      hV.opsSubset o (by rw [h_ops]; exact List.Mem.tail _ ho)
    unfold execStepDec
    rw [h_ops]
    dsimp only
    cases op with
    | directCall callee =>
      dsimp only
      have h_r : MonoReachable P callee :=
        monoReachable_of_body_op P hWT hV.curReachable h_op_mem (List.Mem.head _)
      have h_in : callee ∈ L.symbols := hCC.symbolsComplete callee h_r
      simp only [h_in, ↓reduceIte]
      exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
    | reifyFnPtr fnId tyArg trackCaller loc =>
      dsimp only
      have h_mem_op :
          (if trackCaller = true then InstanceKind.reifyShim fnId tyArg loc else InstanceKind.item fnId tyArg) ∈
            opUsedMonoItems P (.reifyFnPtr fnId tyArg trackCaller loc) := by
        unfold opUsedMonoItems
        cases trackCaller <;> exact List.Mem.head _
      have h_r : MonoReachable P
          (if trackCaller = true then InstanceKind.reifyShim fnId tyArg loc else InstanceKind.item fnId tyArg) :=
        monoReachable_of_body_op P hWT hV.curReachable h_op_mem h_mem_op
      have h_in := hCC.symbolsComplete _ h_r
      simp only [h_in, ↓reduceIte]
      exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
    | reifyVirtualFnPtr tr slotIdx loc =>
      dsimp only
      have h_r : MonoReachable P (.reifyShim tr slotIdx loc) :=
        monoReachable_of_body_op P hWT hV.curReachable h_op_mem (List.Mem.head _)
      have h_in : InstanceKind.reifyShim tr slotIdx loc ∈ L.symbols := hCC.symbolsComplete _ h_r
      simp only [h_in, ↓reduceIte]
      exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
    | unsizeToDyn ty tr =>
      dsimp only
      have h_vr : VtableReachable P ty tr :=
        VtableReachable.fromUnsize hV.curReachable h_op_mem
      have h_vt : L.vtableOf ty tr = some (vtableEntries P.H P.R ty tr) :=
        hCC.vtablesComplete ty tr h_vr
      rw [h_vt]
      dsimp only
      refine ⟨hV.curReachable, h_rest_mem, ?_⟩
      intro obj hobj
      cases hobj
      refine ⟨⟨tr, h_vr, rfl, Or.inl rfl⟩, ?_, ?_⟩
      · intro inst h_m
        have h_in_col : inst ∈ vtableCollectedMethods P.H P.R ty tr := by
          unfold vtableCollectedMethods
          have h_fm : inst ∈ (vtableEntries P.H P.R ty tr).flatMap
              (fun e => match e with | .method i => [i] | _ => []) :=
            mem_flatMap_of_mem h_m (List.Mem.head _)
          cases ty.needsDrop with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact h_fm
          | true =>
            simp only [↓reduceIte]
            exact List.Mem.tail _ h_fm
        exact monoReachable_of_body_op P hWT hV.curReachable h_op_mem h_in_col
      · intro h_nd
        have h_in_col : InstanceKind.dropGlue ty ∈ vtableCollectedMethods P.H P.R ty tr := by
          unfold vtableCollectedMethods
          rw [h_nd]
          exact List.Mem.head _
        exact monoReachable_of_body_op P hWT hV.curReachable h_op_mem h_in_col
    | upcastDyn srcTr targetTr =>
      dsimp only
      cases h_dv : st.dynVal with
      | none =>
        dsimp only
        exact ⟨hV.curReachable, h_rest_mem, fun obj hobj => by cases hobj⟩
      | some obj =>
        dsimp only
        have h_objV := hV.dynValid obj h_dv
        have h_src_eq : obj.curTrait = srcTr :=
          (hV.opTyped (.upcastDyn srcTr targetTr) (by rw [h_ops]; exact List.Mem.head _)) obj h_dv
        cases h_sv : supertraitVtableSlot P.H srcTr targetTr with
        | none =>
          dsimp only
          exact ⟨hV.curReachable, h_rest_mem, fun obj' hobj' => by cases hobj'; exact h_objV⟩
        | some optIdx =>
          cases optIdx with
          | none =>
            dsimp only
            have h_pref_st : SegmentsPrefix (prepareVtableSegments P.H targetTr) (prepareVtableSegments P.H srcTr) :=
              hWT.prefixCoherent srcTr targetTr h_sv
            refine ⟨hV.curReachable, h_rest_mem, ?_⟩
            intro obj' hobj'
            cases hobj'
            rcases h_objV.vtMatches with ⟨backTr, h_backVR, h_backEq, h_backRel⟩
            refine ⟨⟨backTr, h_backVR, h_backEq, ?_⟩, h_objV.allMethodsReachable, h_objV.dropReachable⟩
            rw [h_src_eq] at h_backRel
            cases h_backRel with
            | inl h_eq =>
              subst h_eq
              exact Or.inr h_pref_st
            | inr h_p2 =>
              exact Or.inr (segmentsPrefix_trans h_pref_st h_p2)
          | some idx =>
            dsimp only
            rcases h_objV.vtMatches with ⟨backTr, h_backVR, h_backEq, h_backRel⟩
            have h_sv_back : supertraitVtableSlot P.H backTr targetTr = some (some idx) := by
              rw [h_src_eq] at h_backRel
              cases h_backRel with
              | inl h_eq => subst h_eq; exact h_sv
              | inr h_pref =>
                rcases h_pref with ⟨suf, h_peq⟩
                unfold supertraitVtableSlot at h_sv ⊢
                rw [h_peq]
                exact supertraitSlotAux_prefix_agree P.H targetTr 0 _ suf (some idx) h_sv
            have h_vptr_slot : obj.vt[idx]? = some (VtblEntry.traitVPtr targetTr) := by
              rw [h_backEq]
              exact supertraitVtableSlot_vptr_sound P.H P.R obj.ty backTr targetTr idx h_sv_back
            have h_sup_mem : targetTr ∈ vtableEmbeddedSupertraits P.H P.R obj.ty backTr := by
              unfold vtableEmbeddedSupertraits
              have h_ent : VtblEntry.traitVPtr targetTr ∈ vtableEntries P.H P.R obj.ty backTr := by
                rw [← h_backEq]
                exact mem_of_getElem?_eq_some h_vptr_slot
              exact mem_flatMap_of_mem h_ent (List.Mem.head _)
            have h_sup_vr : VtableReachable P obj.ty targetTr :=
              VtableReachable.fromTraitVPtr h_backVR h_sup_mem
            have h_sup_vt : L.vtableOf obj.ty targetTr = some (vtableEntries P.H P.R obj.ty targetTr) :=
              hCC.vtablesComplete obj.ty targetTr h_sup_vr
            rw [h_vptr_slot]
            dsimp only
            rw [h_sup_vt]
            dsimp only
            refine ⟨hV.curReachable, h_rest_mem, ?_⟩
            intro obj' hobj'
            cases hobj'
            have h_cov := hWT.supertraitCovered backTr targetTr obj.ty h_sup_mem
            refine ⟨⟨targetTr, h_sup_vr, rfl, Or.inl rfl⟩, ?_, h_objV.dropReachable⟩
            intro inst h_m
            have h_in_back : VtblEntry.method inst ∈ vtableEntries P.H P.R obj.ty backTr := by
              unfold vtableEntries renderSegments at h_m ⊢
              rcases mem_of_mem_flatMap h_m with ⟨seg, h_seg, h_e⟩
              cases seg with
              | metadataDSA =>
                unfold renderSegment at h_e
                cases h_nd : obj.ty.needsDrop <;>
                  (simp only [h_nd, Bool.false_eq_true, ↓reduceIte] at h_e
                   cases h_e with
                   | tail _ h1 =>
                     cases h1 with
                     | tail _ h2 =>
                       cases h2 with
                       | tail _ h3 => cases h3)
              | traitOwnEntries tr emitB =>
                rcases h_cov tr emitB h_seg with ⟨emitA, h_seg_back⟩
                exact mem_flatMap_of_mem h_seg_back
                  (renderSegment_method_iff_ignore_vptr P.H P.R obj.ty tr emitB emitA inst h_e)
            rw [← h_backEq] at h_in_back
            exact h_objV.allMethodsReachable inst h_in_back
    | virtualDispatch tr slotIdx =>
      dsimp only
      cases h_dv : st.dynVal with
      | none =>
        dsimp only
        exact ⟨hV.curReachable, h_rest_mem, fun obj hobj => by cases hobj⟩
      | some obj =>
        dsimp only
        have h_objV := hV.dynValid obj h_dv
        have h_ty := (hV.opTyped (.virtualDispatch tr slotIdx) (by rw [h_ops]; exact List.Mem.head _)) obj h_dv
        rcases h_ty with ⟨h_cur_eq, inst, h_slot_eq⟩
        rcases h_objV.vtMatches with ⟨backTr, _, h_backEq, h_backRel⟩
        have h_obj_slot : obj.vt[slotIdx]? = some (.method inst) := by
          rw [h_backEq]
          rw [h_cur_eq] at h_backRel
          cases h_backRel with
          | inl h_eq => subst h_eq; exact h_slot_eq
          | inr h_pref =>
            have h_lt : slotIdx < (vtableEntries P.H P.R obj.ty tr).length :=
              (List.getElem?_eq_some_iff.mp h_slot_eq).1
            rw [prefix_vtable_entries_agree P.H P.R obj.ty backTr tr h_pref slotIdx h_lt]
            exact h_slot_eq
        have h_inst_r : MonoReachable P inst :=
          h_objV.allMethodsReachable inst (mem_of_getElem?_eq_some h_obj_slot)
        have h_in : inst ∈ L.symbols := hCC.symbolsComplete inst h_inst_r
        rw [h_obj_slot]
        dsimp only
        simp only [h_in, ↓reduceIte]
        exact ⟨hV.curReachable, h_rest_mem, fun obj' hobj' => by cases hobj'; exact h_objV⟩
    | dropConcrete ty =>
      dsimp only
      cases h_nd : ty.needsDrop with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
      | true =>
        have h_mem : InstanceKind.dropGlue ty ∈ opUsedMonoItems P (.dropConcrete ty) := by
          simp only [opUsedMonoItems, h_nd, ↓reduceIte]
          exact List.Mem.head _
        have h_r : MonoReachable P (.dropGlue ty) :=
          monoReachable_of_body_op P hWT hV.curReachable h_op_mem h_mem
        have h_in : InstanceKind.dropGlue ty ∈ L.symbols := hCC.symbolsComplete _ h_r
        simp only [h_in, ↓reduceIte]
        exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
    | reifyDropFnPtr ty =>
      dsimp only
      have h_r : MonoReachable P (.dropGlue ty) :=
        monoReachable_of_body_op P hWT hV.curReachable h_op_mem (List.Mem.head _)
      have h_in : InstanceKind.dropGlue ty ∈ L.symbols := hCC.symbolsComplete _ h_r
      simp only [h_in, ↓reduceIte]
      exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
    | dropDyn =>
      dsimp only
      cases h_dv : st.dynVal with
      | none =>
        dsimp only
        exact ⟨hV.curReachable, h_rest_mem, fun obj hobj => by cases hobj⟩
      | some obj =>
        dsimp only
        have h_objV := hV.dynValid obj h_dv
        rcases h_objV.vtMatches with ⟨backTr, _, h_backEq, _⟩
        have h_slot0 : obj.vt[0]? =
            some (VtblEntry.metadataDropInPlace (if obj.ty.needsDrop then some (.dropGlue obj.ty) else none)) := by
          rw [h_backEq]
          exact vtableEntries_slot0_drop P.H P.R obj.ty backTr
        rw [h_slot0]
        cases h_nd : obj.ty.needsDrop with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hV.curReachable, h_rest_mem, fun obj' hobj' => by cases hobj'; exact h_objV⟩
        | true =>
          simp only [↓reduceIte]
          have h_r : MonoReachable P (.dropGlue obj.ty) := h_objV.dropReachable h_nd
          have h_in : InstanceKind.dropGlue obj.ty ∈ L.symbols := hCC.symbolsComplete _ h_r
          simp only [h_in, ↓reduceIte]
          exact ⟨hV.curReachable, h_rest_mem, fun obj' hobj' => by cases hobj'; exact h_objV⟩
    | closureAsFnOnce fnId tyArg =>
      dsimp only
      have h_r : MonoReachable P (.closureOnceShim fnId tyArg) :=
        monoReachable_of_body_op P hWT hV.curReachable h_op_mem (List.Mem.head _)
      have h_in : InstanceKind.closureOnceShim fnId tyArg ∈ L.symbols := hCC.symbolsComplete _ h_r
      simp only [h_in, ↓reduceIte]
      exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩
    | fnPtrAsFnTrait fnId tyArg =>
      dsimp only
      have h_r : MonoReachable P (.fnPtrShim fnId tyArg) :=
        monoReachable_of_body_op P hWT hV.curReachable h_op_mem (List.Mem.head _)
      have h_in : InstanceKind.fnPtrShim fnId tyArg ∈ L.symbols := hCC.symbolsComplete _ h_r
      simp only [h_in, ↓reduceIte]
      exact ⟨hV.curReachable, h_rest_mem, hV.dynValid⟩

/-- Multi-step link-completeness: for ANY fuel bound `n`, if every intermediate reachable state
    remains well-typed (i.e. satisfies `StateValid`'s op-typing invariant along the trace),
    `execStepsDec` NEVER returns `.fault err`. -/
def traceTypedStep (P : MonoProgram) (L : DecLinkArtifact)
    (ih : ExecState → Prop) (s : ExecState) : Prop :=
  StateValid P s ∧
  match execStepDec P L s with
  | .ok s' => ih s'
  | .halted => True
  | .fault _ => True

def TraceTyped (P : MonoProgram) (L : DecLinkArtifact) (fuel : Nat) (st : ExecState) : Prop :=
  Nat.repeat (traceTypedStep P L) fuel (fun _ => True) st

theorem TraceTyped_succ (P : MonoProgram) (L : DecLinkArtifact) (fuel : Nat) (st : ExecState) :
    TraceTyped P L (fuel + 1) st =
      (StateValid P st ∧
       match execStepDec P L st with
       | .ok s' => TraceTyped P L fuel s'
       | .halted => True
       | .fault _ => True) := rfl

theorem collector_link_complete (P : MonoProgram) (L : DecLinkArtifact)
    (hWT : ProgramWellTyped P) (hCC : CollectorComplete P L)
    (fuel : Nat) (st : ExecState) (hTT : TraceTyped P L fuel st) :
    ∀ err, execStepsDec P L fuel st ≠ .fault err := by
  induction fuel generalizing st with
  | zero =>
    intro err h
    rw [execStepsDec_zero] at h
    cases h
  | succ k ih =>
    rw [TraceTyped_succ] at hTT
    rcases hTT with ⟨hV, hNext⟩
    have hStep := execStepDec_no_fault P L hWT hCC st hV
    rw [execStepsDec_succ]
    cases h_res : execStepDec P L st with
    | fault e =>
      rw [h_res] at hStep
      exact False.elim hStep
    | halted =>
      intro err h
      cases h
    | ok st' =>
      rw [h_res] at hNext
      exact ih st' hNext

-- ============================================================================
-- Section 7: Concrete Diamond, Single-Chain, & Empty-Marker Instantiations
-- ============================================================================

namespace DiamondExample

-- Trait IDs
def trBase : TraitId := 0
def trSuperA : TraitId := 1
def trSuperB : TraitId := 2
def trDiamond : TraitId := 3
def trEmptyMarker : TraitId := 4
def trSecondSuper : TraitId := 5
def trSubAfterEmpty : TraitId := 6
def trCondVacant : TraitId := 7

-- Method IDs
def mBaseId : MethodId := 10
def mAVal : MethodId := 11
def mBVal : MethodId := 12
def mDVal : MethodId := 13
def mSecVal : MethodId := 14
def mSubE : MethodId := 15
def mAlways : MethodId := 16
def mOnlyIfCopy : MethodId := 17

-- Function IDs
def fnBaseId : FnId := 100
def fnAVal : FnId := 101
def fnBVal : FnId := 102
def fnDVal : FnId := 103
def fnSecVal : FnId := 104
def fnSubE : FnId := 105
def fnAlways : FnId := 106
def fnOnlyIfCopy : FnId := 107
def fnTrackedFree : FnId := 200
def fnMain : FnId := 300

-- Concrete Types mirroring Specimen 1 (`CopyLeaf`, `DropLeaf`)
def tyCopyLeaf : ConcreteTy := { id := 1, size := 8, align := 8, needsDrop := false }
def tyDropLeaf : ConcreteTy := { id := 2, size := 16, align := 8, needsDrop := true }

def diamondDefs : TraitId → TraitDef
  | 0 => { ownMethods := [mBaseId], directSupers := [] }
  | 1 => { ownMethods := [mAVal], directSupers := [trBase] }
  | 2 => { ownMethods := [mBVal], directSupers := [trBase] }
  | 3 => { ownMethods := [mDVal], directSupers := [trSuperA, trSuperB] }
  | 4 => { ownMethods := [], directSupers := [] }
  | 5 => { ownMethods := [mSecVal], directSupers := [] }
  | 6 => { ownMethods := [mSubE], directSupers := [trEmptyMarker, trSecondSuper] }
  | 7 => { ownMethods := [mAlways, mOnlyIfCopy], directSupers := [] }
  | _ => { ownMethods := [], directSupers := [] }

def H : TraitHierarchy := { defs := diamondDefs, maxDepth := 5 }

def R : MethodResolver := fun ty tr m =>
  if tr = trBase && m = mBaseId then some (.item fnBaseId ty.id)
  else if tr = trSuperA && m = mAVal then some (.item fnAVal ty.id)
  else if tr = trSuperB && m = mBVal then some (.item fnBVal ty.id)
  else if tr = trDiamond && m = mDVal then some (.item fnDVal ty.id)
  else if tr = trSecondSuper && m = mSecVal then some (.item fnSecVal ty.id)
  else if tr = trSubAfterEmpty && m = mSubE then some (.item fnSubE ty.id)
  else if tr = trCondVacant && m = mAlways then some (.item fnAlways ty.id)
  else if tr = trCondVacant && m = mOnlyIfCopy then
    -- Impossible predicate for `tyDropLeaf` -> `VtblEntry::Vacant`
    if ty.needsDrop then none else some (.item fnOnlyIfCopy ty.id)
  else none

-- Verify exact segment order matching `rustc_trait_selection/src/traits/vtable.rs:66-70`!
theorem diamond_segments_exact :
    prepareVtableSegments H trDiamond =
      [ .metadataDSA,
        .traitOwnEntries trBase false,
        .traitOwnEntries trSuperA false,
        .traitOwnEntries trSuperB true,
        .traitOwnEntries trDiamond false ] := rfl

theorem superA_segments_exact :
    prepareVtableSegments H trSuperA =
      [ .metadataDSA,
        .traitOwnEntries trBase false,
        .traitOwnEntries trSuperA false ] := rfl

theorem superB_segments_exact :
    prepareVtableSegments H trSuperB =
      [ .metadataDSA,
        .traitOwnEntries trBase false,
        .traitOwnEntries trSuperB false ] := rfl

theorem base_segments_exact :
    prepareVtableSegments H trBase =
      [ .metadataDSA,
        .traitOwnEntries trBase false ] := rfl

-- Empty-marker supertrait optimization (`vtable.rs:158-172`): `trSecondSuper` gets `emitVPtr = false`!
theorem subAfterEmpty_segments_exact :
    prepareVtableSegments H trSubAfterEmpty =
      [ .metadataDSA,
        .traitOwnEntries trEmptyMarker false,
        .traitOwnEntries trSecondSuper false,
        .traitOwnEntries trSubAfterEmpty false ] := rfl

-- Exact `supertraitVtableSlot` outcomes matching Specimen 1 LLVM IR!
theorem diamond_to_superA_prefix_reuse :
    supertraitVtableSlot H trDiamond trSuperA = some none := rfl

theorem diamond_to_base_prefix_reuse :
    supertraitVtableSlot H trDiamond trBase = some none := rfl

theorem diamond_to_superB_vptr_slot_6 :
    supertraitVtableSlot H trDiamond trSuperB = some (some 6) := rfl

theorem superB_to_base_prefix_reuse :
    supertraitVtableSlot H trSuperB trBase = some none := rfl

theorem subAfterEmpty_to_secondSuper_prefix_reuse :
    supertraitVtableSlot H trSubAfterEmpty trSecondSuper = some none := rfl

-- Exact concrete vtable layouts matching LLVM IR `@vtable.3` (`CopyLeaf`) & `@vtable.4` (`DropLeaf`)!
theorem copyLeaf_diamond_vtable_exact :
    vtableEntries H R tyCopyLeaf trDiamond =
      [ .metadataDropInPlace none,
        .metadataSize 8,
        .metadataAlign 8,
        .method (.item fnBaseId 1),
        .method (.item fnAVal 1),
        .method (.item fnBVal 1),
        .traitVPtr trSuperB,
        .method (.item fnDVal 1) ] := rfl

theorem dropLeaf_diamond_vtable_exact :
    vtableEntries H R tyDropLeaf trDiamond =
      [ .metadataDropInPlace (some (.dropGlue tyDropLeaf)),
        .metadataSize 16,
        .metadataAlign 8,
        .method (.item fnBaseId 2),
        .method (.item fnAVal 2),
        .method (.item fnBVal 2),
        .traitVPtr trSuperB,
        .method (.item fnDVal 2) ] := rfl

theorem dropLeaf_superB_vtable_exact :
    vtableEntries H R tyDropLeaf trSuperB =
      [ .metadataDropInPlace (some (.dropGlue tyDropLeaf)),
        .metadataSize 16,
        .metadataAlign 8,
        .method (.item fnBaseId 2),
        .method (.item fnBVal 2) ] := rfl

-- Vacant slot verification (`VtblEntry::Vacant` at slot 4 for `DropLeaf`!)
theorem dropLeaf_vacant_vtable_exact :
    vtableEntries H R tyDropLeaf trCondVacant =
      [ .metadataDropInPlace (some (.dropGlue tyDropLeaf)),
        .metadataSize 16,
        .metadataAlign 8,
        .method (.item fnAlways 2),
        .vacant ] := rfl

-- Prefix coherence proofs for the diamond hierarchy
theorem diamond_prefix_superA :
    SegmentsPrefix (prepareVtableSegments H trSuperA) (prepareVtableSegments H trDiamond) :=
  ⟨[.traitOwnEntries trSuperB true, .traitOwnEntries trDiamond false], rfl⟩

theorem diamond_prefix_base :
    SegmentsPrefix (prepareVtableSegments H trBase) (prepareVtableSegments H trDiamond) :=
  ⟨[.traitOwnEntries trSuperA false, .traitOwnEntries trSuperB true, .traitOwnEntries trDiamond false], rfl⟩

theorem superB_prefix_base :
    SegmentsPrefix (prepareVtableSegments H trBase) (prepareVtableSegments H trSuperB) :=
  ⟨[.traitOwnEntries trSuperB false], rfl⟩

-- Faithful vtable store for the diamond hierarchy
def fullStore : ConcreteTy → TraitId → Option (List VtblEntry) :=
  fun ty tr => some (vtableEntries H R ty tr)

theorem fullStore_faithful : VtableStoreFaithful H R fullStore := fun _ _ => rfl

/-- Diamond upcast `dyn Diamond -> dyn SuperA`: zero-cost prefix reuse dispatches `a_val` and `base_id`
    and drop glue identically to concrete `ty` for EVERY concrete `ty`! -/
theorem diamond_upcast_to_superA_dispatch_sound (ty : ConcreteTy) :
    ∃ dstVt,
      upcastVtable H fullStore ty trDiamond trSuperA (vtableEntries H R ty trDiamond) = some dstVt ∧
      dstVt[4]? = some (.method (.item fnAVal ty.id)) ∧
      dstVt[3]? = some (.method (.item fnBaseId ty.id)) ∧
      dstVt[0]? = some (.metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none)) := by
  have h_a := upcast_dispatch_and_drop_sound H R fullStore fullStore_faithful
    ty trDiamond trSuperA trSuperA mAVal 4
    (fun _ => diamond_prefix_superA)
    (by decide)
    rfl
  rcases h_a with ⟨dstVt, h_up, h_slotA, h_drop⟩
  refine ⟨dstVt, h_up, h_slotA, ?_, h_drop⟩
  unfold upcastVtable at h_up
  rw [diamond_to_superA_prefix_reuse] at h_up
  cases h_up
  exact virtualMethodSlot_sound H R ty trDiamond trBase mBaseId 3 rfl

/-- Diamond upcast `dyn Diamond -> dyn SuperB`: reads `TraitVPtr` at slot 6 and dispatches `b_val`,
    `base_id`, and drop glue identically to concrete `ty` for EVERY concrete `ty`! -/
theorem diamond_upcast_to_superB_dispatch_sound (ty : ConcreteTy) :
    ∃ dstVt,
      upcastVtable H fullStore ty trDiamond trSuperB (vtableEntries H R ty trDiamond) = some dstVt ∧
      dstVt[4]? = some (.method (.item fnBVal ty.id)) ∧
      dstVt[3]? = some (.method (.item fnBaseId ty.id)) ∧
      dstVt[0]? = some (.metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none)) := by
  have h_b := upcast_dispatch_and_drop_sound H R fullStore fullStore_faithful
    ty trDiamond trSuperB trSuperB mBVal 4
    (fun h => by rw [diamond_to_superB_vptr_slot_6] at h; cases h)
    (by decide)
    rfl
  rcases h_b with ⟨dstVt, h_up, h_slotB, h_drop⟩
  refine ⟨dstVt, h_up, h_slotB, ?_, h_drop⟩
  unfold upcastVtable at h_up
  rw [diamond_to_superB_vptr_slot_6] at h_up
  dsimp only at h_up
  have h_vp := supertraitVtableSlot_vptr_sound H R ty trDiamond trSuperB 6 diamond_to_superB_vptr_slot_6
  rw [h_vp] at h_up
  dsimp only at h_up
  rw [fullStore_faithful] at h_up
  cases h_up
  exact virtualMethodSlot_sound H R ty trSuperB trBase mBaseId 3 rfl

/-- Chained upcast `dyn Diamond -> dyn SuperB -> dyn Base`:
    first hop dereferences slot 6 (`TraitVPtr`), second hop is zero-cost prefix reuse! -/
theorem diamond_upcast_superB_then_base_sound (ty : ConcreteTy) :
    ∃ vtB vtBase,
      upcastVtable H fullStore ty trDiamond trSuperB (vtableEntries H R ty trDiamond) = some vtB ∧
      upcastVtable H fullStore ty trSuperB trBase vtB = some vtBase ∧
      vtBase = vtB ∧
      vtBase[3]? = some (.method (.item fnBaseId ty.id)) ∧
      vtBase[0]? = some (.metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none)) := by
  rcases diamond_upcast_to_superB_dispatch_sound ty with ⟨vtB, h_upB, _, h_baseB, h_dropB⟩
  refine ⟨vtB, vtB, h_upB, ?_, rfl, h_baseB, h_dropB⟩
  unfold upcastVtable
  rw [superB_to_base_prefix_reuse]

-- ============================================================================
-- Section 8: Two Sharpness Counterexamples (CE1 & CE2)
-- ============================================================================

/-- **CE1 (Wrong Prefix Reuse for Non-Principal Supertrait `SuperB`):**
    Suppose a buggy compiler ignores `TraitVPtr` and directly reuses `vtable(ty, Diamond)`
    as the vtable for `dyn SuperB`.
    When a caller invokes `SuperB::b_val` (whose virtual slot in `dyn SuperB` is `4`),
    slot `4` of `vtable(ty, Diamond)` holds `SuperA::a_val` instead of `SuperB::b_val`! -/
def buggyUpcastReuseAlways (srcVt : List VtblEntry) : List VtblEntry := srcVt

theorem ce1_superB_method_slot_is_4 :
    virtualMethodSlot H trSuperB trSuperB mBVal = some 4 := rfl

theorem ce1_wrong_prefix_reuse_dispatches_to_superA_not_superB (ty : ConcreteTy) :
    let buggyVt := buggyUpcastReuseAlways (vtableEntries H R ty trDiamond)
    let expectedEntry := VtblEntry.method (.item fnBVal ty.id)
    let actualEntry := VtblEntry.method (.item fnAVal ty.id)
    buggyVt[4]? = some actualEntry ∧ actualEntry ≠ expectedEntry := by
  refine ⟨?_, ?_⟩
  · -- Slot 4 of `vtable(ty, Diamond)` is `SuperA::a_val`!
    exact virtualMethodSlot_sound H R ty trDiamond trSuperA mAVal 4 rfl
  · intro heq
    cases heq

/-- **CE1b (Vtable Slot Type Corruption — Jumping into a `TraitVPtr` Data Slot):**
    In a 3-supertrait hierarchy `trTri_ce : trA_ce + trB_ce + trC_ce` where `trA_ce` has 1 method,
    `trB_ce` has 1 method, and `trC_ce` has 3 methods:
    - `vtable(ty, trTri_ce)` lays out `[0..2]=DSA, [3]=mA0, [4]=mB0, [5]=TraitVPtr(trB_ce), [6]=mC0, [7]=mC1, [8]=mC2, [9]=TraitVPtr(trC_ce)`.
    - `vtable(ty, trC_ce)` lays out `[0..2]=DSA, [3]=mC0, [4]=mC1, [5]=mC2`.
    Reusing `vtable(ty, trTri_ce)` directly for `dyn trC_ce` causes dispatching `mC2` (virtual
    slot `5` in `dyn trC_ce`) to read `VtblEntry.traitVPtr trB_ce` (a read-only vtable data
    pointer, not a callable function pointer!), triggering `RuntimeFault.badSlotEntry 5`. -/
def trA_ce : TraitId := 20
def trB_ce : TraitId := 21
def trC_ce : TraitId := 23
def trTri_ce : TraitId := 24
def mA0 : MethodId := 200
def mB0 : MethodId := 201
def mC0 : MethodId := 210
def mC1 : MethodId := 211
def mC2 : MethodId := 212

def ce1cDefs : TraitId → TraitDef
  | 20 => { ownMethods := [mA0], directSupers := [] }
  | 21 => { ownMethods := [mB0], directSupers := [] }
  | 23 => { ownMethods := [mC0, mC1, mC2], directSupers := [] }
  | 24 => { ownMethods := [], directSupers := [trA_ce, trB_ce, trC_ce] }
  | _ => { ownMethods := [], directSupers := [] }

def H_ce1c : TraitHierarchy := { defs := ce1cDefs, maxDepth := 3 }

def R_ce1c : MethodResolver := fun ty tr m =>
  if tr = trA_ce && m = mA0 then some (.item 300 ty.id)
  else if tr = trB_ce && m = mB0 then some (.item 301 ty.id)
  else if tr = trC_ce && m = mC0 then some (.item 310 ty.id)
  else if tr = trC_ce && m = mC1 then some (.item 311 ty.id)
  else if tr = trC_ce && m = mC2 then some (.item 312 ty.id)
  else none

/-- Sharpness CE1b: Reusing `vtable(ty, trTri_ce)` for `dyn trC_ce` causes calling `mC2`
    (virtual slot `5` in `dyn trC_ce`) to read **`VtblEntry.traitVPtr trB_ce`** (a non-callable
    vtable data pointer!) instead of a function pointer, triggering `RuntimeFault.badSlotEntry 5`! -/
theorem ce1b_wrong_prefix_reuse_reads_traitVPtr_slot (ty : ConcreteTy) :
    virtualMethodSlot H_ce1c trC_ce trC_ce mC2 = some 5 ∧
    (vtableEntries H_ce1c R_ce1c ty trTri_ce)[5]? = some (VtblEntry.traitVPtr trB_ce) := by
  refine ⟨rfl, ?_⟩
  exact supertraitVtableSlot_vptr_sound H_ce1c R_ce1c ty trTri_ce trB_ce 5 rfl

-- ----------------------------------------------------------------------------
-- CE2a: Omitting `ReifyShim` during `#[track_caller]` fn-item coercion faults
-- ----------------------------------------------------------------------------

def locTrackedDef : LocId := 42

def progReifyTrackCaller : MonoProgram :=
  { H := H
    R := R
    bodyOf := fun inst =>
      match inst with
      | .item 300 0 => [.reifyFnPtr fnTrackedFree 0 true locTrackedDef]
      | _ => []
    roots := [.item fnMain 0] }

/-- Complete link artifact including `ReifyShim` collected by `MonoReachable`. -/
def linkReifyComplete : DecLinkArtifact :=
  { symbols := [.item fnMain 0, .reifyShim fnTrackedFree 0 locTrackedDef, .item fnTrackedFree 0]
    vtableOf := fullStore }

/-- Defective link artifact omitting `ReifyShim` (only emitting raw `item fnTrackedFree 0`). -/
def linkReifyBuggyMissingShim : DecLinkArtifact :=
  { symbols := [.item fnMain 0, .item fnTrackedFree 0]
    vtableOf := fullStore }

def initStateReify : ExecState :=
  { curFn := .item fnMain 0
    ops := progReifyTrackCaller.bodyOf (.item fnMain 0)
    dynVal := none
    fnPtrVal := none }

theorem ce2a_reify_shim_is_mono_reachable :
    MonoReachable progReifyTrackCaller (.reifyShim fnTrackedFree 0 locTrackedDef) :=
  MonoReachable.step (MonoReachable.root (List.Mem.head _)) (List.Mem.head _)

theorem ce2a_complete_collector_succeeds :
    execStepsDec progReifyTrackCaller linkReifyComplete 2 initStateReify = .halted := rfl

theorem ce2a_omitting_reify_shim_faults :
    execStepsDec progReifyTrackCaller linkReifyBuggyMissingShim 2 initStateReify =
      .fault (.missingSymbol (.reifyShim fnTrackedFree 0 locTrackedDef)) := rfl

-- ----------------------------------------------------------------------------
-- CE2b: Omitting `DropGlue` during `dyn Trait` unsizing faults on upcast drop
-- ----------------------------------------------------------------------------

def progDynUpcastDrop : MonoProgram :=
  { H := H
    R := R
    bodyOf := fun inst =>
      match inst with
      | .item 300 0 =>
        [ .unsizeToDyn tyDropLeaf trDiamond,
          .upcastDyn trDiamond trSuperB,
          .virtualDispatch trSuperB 4,
          .dropDyn ]
      | _ => []
    roots := [.item fnMain 0] }

/-- Complete link artifact including all vtable methods AND `dropGlue tyDropLeaf`. -/
def linkDynDropComplete : DecLinkArtifact :=
  { symbols :=
      [ .item fnMain 0,
        .dropGlue tyDropLeaf,
        .item fnBaseId 2,
        .item fnAVal 2,
        .item fnBVal 2,
        .item fnDVal 2 ]
    vtableOf := fullStore }

/-- Defective link artifact emitting all vtable methods EXCEPT `dropGlue tyDropLeaf`. -/
def linkDynDropBuggyNoDropGlue : DecLinkArtifact :=
  { symbols :=
      [ .item fnMain 0,
        .item fnBaseId 2,
        .item fnAVal 2,
        .item fnBVal 2,
        .item fnDVal 2 ]
    vtableOf := fullStore }

def initStateDynDrop : ExecState :=
  { curFn := .item fnMain 0
    ops := progDynUpcastDrop.bodyOf (.item fnMain 0)
    dynVal := none
    fnPtrVal := none }

theorem ce2b_drop_glue_is_mono_reachable :
    MonoReachable progDynUpcastDrop (.dropGlue tyDropLeaf) :=
  MonoReachable.step (MonoReachable.root (List.Mem.head _)) (List.Mem.head _)

theorem ce2b_complete_collector_succeeds :
    execStepsDec progDynUpcastDrop linkDynDropComplete 5 initStateDynDrop = .halted := rfl

theorem ce2b_omitting_drop_glue_faults_on_upcast_drop :
    execStepsDec progDynUpcastDrop linkDynDropBuggyNoDropGlue 5 initStateDynDrop =
      .fault (.missingSymbol (.dropGlue tyDropLeaf)) := rfl

-- Positive contrast: for `tyCopyLeaf` (`needsDrop = false`), slot 0 is `null`, so
-- `dropDyn` succeeds even WITHOUT any `dropGlue tyCopyLeaf` symbol emitted!
def progCopyDynUpcastDrop : MonoProgram :=
  { H := H
    R := R
    bodyOf := fun inst =>
      match inst with
      | .item 300 0 =>
        [ .unsizeToDyn tyCopyLeaf trDiamond,
          .upcastDyn trDiamond trSuperB,
          .virtualDispatch trSuperB 4,
          .dropDyn ]
      | _ => []
    roots := [.item fnMain 0] }

def linkCopyDynNoDropGlue : DecLinkArtifact :=
  { symbols :=
      [ .item fnMain 0,
        .item fnBaseId 1,
        .item fnAVal 1,
        .item fnBVal 1,
        .item fnDVal 1 ]
    vtableOf := fullStore }

def initStateCopyDynDrop : ExecState :=
  { curFn := .item fnMain 0
    ops := progCopyDynUpcastDrop.bodyOf (.item fnMain 0)
    dynVal := none
    fnPtrVal := none }

theorem copy_dyn_drop_succeeds_without_drop_glue_symbol :
    execStepsDec progCopyDynUpcastDrop linkCopyDynNoDropGlue 5 initStateCopyDynDrop = .halted := rfl

-- Empty-marker prefix preservation soundness: `dyn SubAfterEmpty -> dyn SecondSuper`
-- reuses the exact same vtable pointer (zero indirection) and dispatches `sec_val` identically!
theorem empty_marker_upcast_zero_cost_sound (ty : ConcreteTy) :
    ∃ dstVt,
      upcastVtable H fullStore ty trSubAfterEmpty trSecondSuper (vtableEntries H R ty trSubAfterEmpty) = some dstVt ∧
      dstVt = vtableEntries H R ty trSubAfterEmpty ∧
      dstVt[3]? = some (.method (.item fnSecVal ty.id)) ∧
      dstVt[0]? = some (.metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none)) := by
  refine ⟨vtableEntries H R ty trSubAfterEmpty, ?_, rfl, ?_, vtableEntries_slot0_drop H R ty trSubAfterEmpty⟩
  · unfold upcastVtable
    rw [subAfterEmpty_to_secondSuper_prefix_reuse]
  · exact virtualMethodSlot_sound H R ty trSubAfterEmpty trSecondSuper mSecVal 3 rfl

-- Supertrait segment coverage for Diamond -> SuperB (validating `collector.rs:1235-1238`)!
theorem diamond_covers_superB_segments :
    SupertraitSegmentsCovered H trDiamond trSuperB := by
  intro tr emitB h_mem
  rw [superB_segments_exact] at h_mem
  cases h_mem with
  | tail _ h1 =>
    cases h1 with
    | head =>
      exact ⟨false, List.Mem.tail _ (List.Mem.head _)⟩
    | tail _ h2 =>
      cases h2 with
      | head =>
        exact ⟨true, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩
      | tail _ h3 => cases h3

-- Shim edge-reachability theorems: every compiler-generated shim pulls its target `item` into `MonoReachable`!
theorem vtableShim_reaches_item (P : MonoProgram) (fnId : FnId) (tyArg : TyId)
    (h : MonoReachable P (.vtableShim fnId tyArg)) :
    MonoReachable P (.item fnId tyArg) :=
  MonoReachable.step h (List.Mem.head _)

theorem reifyShim_reaches_item (P : MonoProgram) (fnId : FnId) (tyArg : TyId) (loc : LocId)
    (h : MonoReachable P (.reifyShim fnId tyArg loc)) :
    MonoReachable P (.item fnId tyArg) :=
  MonoReachable.step h (List.Mem.head _)

theorem closureOnceShim_reaches_item (P : MonoProgram) (fnId : FnId) (tyArg : TyId)
    (h : MonoReachable P (.closureOnceShim fnId tyArg)) :
    MonoReachable P (.item fnId tyArg) :=
  MonoReachable.step h (List.Mem.head _)

theorem fnPtrShim_reaches_item (P : MonoProgram) (fnId : FnId) (tyArg : TyId)
    (h : MonoReachable P (.fnPtrShim fnId tyArg)) :
    MonoReachable P (.item fnId tyArg) :=
  MonoReachable.step h (List.Mem.head _)

/-- Reifying `drop_in_place::<CopyLeaf>` as a `fn` pointer forces `DropGlue` collection
    even when `needsDrop = false`, matching `collector.rs:1019-1026`. -/
def progReifyNoopDrop : MonoProgram :=
  { H := H
    R := R
    bodyOf := fun inst =>
      match inst with
      | .item 300 0 => [.reifyDropFnPtr tyCopyLeaf]
      | _ => []
    roots := [.item fnMain 0] }

theorem reify_noop_drop_is_mono_reachable :
    MonoReachable progReifyNoopDrop (.dropGlue tyCopyLeaf) :=
  MonoReachable.step (MonoReachable.root (List.Mem.head _)) (List.Mem.head _)

/-- In contrast, direct `dropConcrete tyCopyLeaf` emits zero mono-item dependencies. -/
theorem direct_noop_drop_emits_no_edge :
    opUsedMonoItems progReifyNoopDrop (.dropConcrete tyCopyLeaf) = [] := rfl

end DiamondExample

end MonomorphVtableUpcast
