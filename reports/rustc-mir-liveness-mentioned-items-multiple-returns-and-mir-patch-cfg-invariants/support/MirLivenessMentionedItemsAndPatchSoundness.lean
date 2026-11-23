/-!
# Mechanized Soundness & CFG Invariants for `rustc` MIR Liveness, `MentionedItems`, `MultipleReturnTerminators`, and `MirPatch`

Kernel-checked Lean `v4.34.1` formalization establishing:

* **Part 0 — Constructive Finite Bitset & Arithmetic Helpers**:
  Zero-`omega`, zero-`Classical.choice`, zero-`partial`, zero-`_unsafe_rec` finite bitset
  (`LiveSet := List Bool`, modeling `DenseBitSet<PlaceIndex>`) and list-insertion primitives.
* **Part 1 — `check_liveness` (`compiler/rustc_mir_transform/src/liveness.rs`)**:
  Exact `DefUse::for_place` classification, monotone `MaybeLivePlaces` backward dataflow
  transfer (including `FakeRead(ForLet(None) | ForGuardBinding)` exemption, `self_assignment`,
  by-ref capture liveness on `Return`/`Yield`/`Goto(START_BLOCK)`/`Call { target: None }`,
  and dead-capture filtering), `FnMut` `Return | UnwindResume -> Goto(START_BLOCK)` loop-closure
  soundness, `merge_guards` & `maybe_drop_guard` field-vs-direct laws, and constructive proof of
  BOTH layers of the Edition 2024 `CoroutineClosure` (`async move ||`) dead-capture blind spot
  (Layer 1: omission of `AggregateKind::CoroutineClosure` at `liveness.rs:1448`; Layer 2:
  `AsyncFnMut` lending `&mut` capture + `is_synthetic_mir` bypass).
* **Part 2 — `MentionedItems` (`mentioned_items.rs` + `rustc_monomorphize::collector`)**:
  All 6 `MentionedItemsVisitor` patterns + `(Array, Str | Slice)` exclusion, pre-optimization
  over-approximation across DCE, exact equivalence of the `used_mentioned_items` deduplication
  optimization, post-DCE PME preservation conditioned on root instantiation, exclusion of
  mentioned-only items from `usage_map` / codegen, and constructive witness of the `rlib`
  `cross_crate_inlinable(optimized_mir)` root-selection opt-level flip.
* **Part 3 — `MultipleReturnTerminators` (`multiple_return_terminators.rs`)**:
  Bipartite cleanup safety (showing why `multiple_return_terminators.rs:28-31` preserves
  `!bb.is_cleanup` on synthesized `Return`s), forward and backward small-step bisimulation
  across empty-`Return` tail duplication, non-empty `Return` epilogue preservation, and
  lockstep bisimulation of `remove_dead_blocks` compaction.
* **Part 4 — `MirPatch` (`patch.rs` + `validate.rs`)**:
  4-stage transactional `apply` semantics, `as_mut_preserves_cfg()` edge-preservation proof,
  `nop_statements` index stability, FIFO queue-order preservation for same-location insertions,
  exact observational equivalence (`applyDeltaInsertions = applyMergeInsertions`) across the
  upstream `patch.rs` refactor from `delta`-shifted `Vec::insert` (`14210df0e`/`3ef0c22cd`) to
  linear `merge` (`137d1d494`), `Unreachable` statement clearing *after* `new_statements`,
  `term_patch_map` permutation independence, bipartite `unreachable_cleanup_block` vs.
  `unreachable_no_cleanup_block` validator preservation, and single-slot `terminate_block`
  reallocation on alternating `UnwindTerminateReason`s.

Purity guarantees (verified under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`):
  - Zero `sorry` / `sorryAx`
  - Zero `Classical.choice`
  - Zero `omega`, `bv_decide`, `native_decide` (`Lean.ofReduceBool`)
  - Zero `partial def`
  - Zero `._unsafe_rec` constants in the environment (no `deriving` on recursive/container inductives)
-/

namespace MirLivenessMentionedItemsAndPatch

/-! ============================================================================
    PART 0: Constructive Arithmetic, Option/List Helpers, and Finite Bitsets
    ============================================================================ -/

section Part0Helpers

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem nat_lt_succ_self (n : Nat) : n < n + 1 := Nat.lt_succ_self n

theorem nat_add_succ_eq (a b : Nat) : a + (b + 1) = (a + b) + 1 :=
  Nat.add_assoc a b 1

theorem nat_succ_le_succ_iff {a b : Nat} : a + 1 ≤ b + 1 ↔ a ≤ b :=
  ⟨Nat.le_of_succ_le_succ, Nat.succ_le_succ⟩

theorem nat_eq_zero_of_le_zero {n : Nat} (h : n ≤ 0) : n = 0 :=
  Nat.le_antisymm h (Nat.zero_le n)

theorem nat_ne_of_lt {a b : Nat} (h : a < b) : a ≠ b :=
  fun heq => Nat.lt_irrefl a (heq ▸ h)

theorem nat_ne_of_gt {a b : Nat} (h : b < a) : a ≠ b :=
  fun heq => Nat.lt_irrefl b (heq ▸ h)

theorem nat_le_of_lt_succ {a b : Nat} (h : a < b + 1) : a ≤ b :=
  Nat.le_of_succ_le_succ h

theorem nat_lt_succ_of_le {a b : Nat} (h : a ≤ b) : a < b + 1 :=
  Nat.succ_le_succ h

theorem nat_not_lt_zero (n : Nat) : ¬ (n < 0) := Nat.not_lt_zero n

theorem nat_cases_lt_or_eq_of_le {a b : Nat} (h : a ≤ b) : a < b ∨ a = b :=
  match Nat.eq_or_lt_of_le h with
  | Or.inl heq => Or.inr heq
  | Or.inr hlt => Or.inl hlt

/-- Structural `List.get?` via `List.foldr` (zero `_unsafe_rec` helpers). -/
def getOpt {α : Type} (xs : List α) (n : Nat) : Option α :=
  xs.foldr (fun x ih k => match k with | 0 => some x | k' + 1 => ih k') (fun _ => none) n

theorem getOpt_nil (n : Nat) : getOpt ([] : List α) n = none := rfl

theorem getOpt_cons_zero (x : α) (xs : List α) : getOpt (x :: xs) 0 = some x := rfl

theorem getOpt_cons_succ (x : α) (xs : List α) (n : Nat) :
    getOpt (x :: xs) (n + 1) = getOpt xs n := rfl

theorem getOpt_append_left {xs ys : List α} {i : Nat} (h : i < xs.length) :
    getOpt (xs ++ ys) i = getOpt xs i := by
  induction xs generalizing i with
  | nil => exact False.elim (nat_not_lt_zero i h)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k =>
      simp only [List.cons_append, getOpt_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ h)

theorem getOpt_append_right {xs ys : List α} {i : Nat} (h : xs.length ≤ i) :
    getOpt (xs ++ ys) i = getOpt ys (i - xs.length) := by
  induction xs generalizing i with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
  | cons x xs ih =>
    cases i with
    | zero =>
      exact False.elim (nat_not_lt_zero xs.length (Nat.lt_of_succ_le h))
    | succ k =>
      simp only [List.cons_append, getOpt_cons_succ, List.length_cons, Nat.succ_sub_succ_eq_sub]
      exact ih (Nat.le_of_succ_le_succ h)

theorem getOpt_some_lt {xs : List α} {i : Nat} {v : α} (h : getOpt xs i = some v) :
    i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ xs.length
    | succ k => exact Nat.succ_lt_succ (ih h)

theorem getOpt_none_of_ge {xs : List α} {i : Nat} (h : xs.length ≤ i) :
    getOpt xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => exact False.elim (nat_not_lt_zero xs.length (Nat.lt_of_succ_le h))
    | succ k => exact ih (Nat.le_of_succ_le_succ h)

theorem getOpt_map (f : α → β) (xs : List α) (i : Nat) :
    getOpt (xs.map f) i = (getOpt xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

/-- Structural `List.set` at index `i` via `@Nat.recCompiled` (zero `_unsafe_rec` helpers). -/
def setAt {α : Type} (xs : List α) (i : Nat) (v : α) : List α :=
  @Nat.recCompiled (fun _ => List α → List α)
    (fun ys => match ys with | [] => [] | _ :: ys' => v :: ys')
    (fun _ ih ys => match ys with | [] => [] | y :: ys' => y :: ih ys')
    i xs

theorem setAt_nil (i : Nat) (v : α) : setAt ([] : List α) i v = [] := by
  cases i <;> rfl

theorem setAt_cons_zero (x : α) (xs : List α) (v : α) :
    setAt (x :: xs) 0 v = v :: xs := rfl

theorem setAt_cons_succ (x : α) (xs : List α) (k : Nat) (v : α) :
    setAt (x :: xs) (k + 1) v = x :: setAt xs k v := rfl

theorem setAt_length (xs : List α) (i : Nat) (v : α) :
    (setAt xs i v).length = xs.length := by
  induction xs generalizing i with
  | nil => rw [setAt_nil]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => simp [setAt_cons_succ, ih]

theorem getOpt_setAt_same {xs : List α} {i : Nat} (h : i < xs.length) (v : α) :
    getOpt (setAt xs i v) i = some v := by
  induction xs generalizing i with
  | nil => exact False.elim (nat_not_lt_zero i h)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih (Nat.lt_of_succ_lt_succ h)

theorem getOpt_setAt_ne {xs : List α} {i j : Nat} (hne : i ≠ j) (v : α) :
    getOpt (setAt xs i v) j = getOpt xs j := by
  induction xs generalizing i j with
  | nil => rw [setAt_nil]
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ k => rfl
    | succ m =>
      cases j with
      | zero => rfl
      | succ k =>
        exact ih (fun h => hne (congrArg Nat.succ h))

/-- Structural element insertion at index `i` via `@Nat.recCompiled` (zero `_unsafe_rec` helpers). -/
def insertAt {α : Type} (xs : List α) (i : Nat) (v : α) : List α :=
  @Nat.recCompiled (fun _ => List α → List α)
    (fun ys => v :: ys)
    (fun _ ih ys => match ys with | [] => [v] | y :: ys' => y :: ih ys')
    i xs

theorem insertAt_zero (xs : List α) (v : α) :
    insertAt xs 0 v = v :: xs := rfl

theorem insertAt_nil_succ (k : Nat) (v : α) :
    insertAt ([] : List α) (k + 1) v = [v] := rfl

theorem insertAt_cons_succ (x : α) (xs : List α) (k : Nat) (v : α) :
    insertAt (x :: xs) (k + 1) v = x :: insertAt xs k v := rfl

theorem insertAt_length (xs : List α) (i : Nat) (v : α) :
    (insertAt xs i v).length = xs.length + 1 := by
  induction xs generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => simp [insertAt_cons_succ, ih]

theorem insertAt_append_of_le {xs ys : List α} {i : Nat} (h : i ≤ xs.length) (v : α) :
    insertAt (xs ++ ys) i v = insertAt xs i v ++ ys := by
  induction xs generalizing i with
  | nil =>
    have h0 := nat_eq_zero_of_le_zero h
    subst h0
    rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k =>
      simp only [List.cons_append, insertAt_cons_succ]
      exact congrArg (List.cons x) (ih (Nat.le_of_succ_le_succ h))

/-- Finite bitset modeling `DenseBitSet<PlaceIndex>` as a `List Bool`. -/
abbrev LiveSet := List Bool

namespace LiveSet

def empty (n : Nat) : LiveSet := List.replicate n false

def get (s : LiveSet) (p : Nat) : Bool :=
  match getOpt s p with
  | some b => b
  | none => false

def insert (s : LiveSet) (p : Nat) : LiveSet := setAt s p true

def remove (s : LiveSet) (p : Nat) : LiveSet := setAt s p false

def union (a b : LiveSet) : LiveSet :=
  a.foldr
    (fun x ih ys =>
      match ys with
      | [] => x :: ih []
      | y :: ys' => (x || y) :: ih ys')
    (fun ys => ys)
    b

theorem union_nil_left (b : LiveSet) : union [] b = b := rfl

theorem union_cons_nil (x : Bool) (xs : LiveSet) : union (x :: xs) [] = x :: union xs [] := rfl

theorem union_nil_right (a : LiveSet) : union a [] = a := by
  induction a with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem union_cons_cons (x : Bool) (xs : LiveSet) (y : Bool) (ys : LiveSet) :
    union (x :: xs) (y :: ys) = (x || y) :: union xs ys := rfl

def subset (a b : LiveSet) : Prop :=
  ∀ p : Nat, get a p = true → get b p = true

def eqBool (a b : LiveSet) : Bool :=
  a.foldr
    (fun x ih ys =>
      match ys with
      | [] => false
      | y :: ys' => (x == y) && ih ys')
    (fun ys => match ys with | [] => true | _ :: _ => false)
    b

theorem empty_length (n : Nat) : (empty n).length = n := List.length_replicate

theorem insert_length (s : LiveSet) (p : Nat) : (insert s p).length = s.length :=
  setAt_length s p true

theorem remove_length (s : LiveSet) (p : Nat) : (remove s p).length = s.length :=
  setAt_length s p false

theorem get_empty (n p : Nat) : get (empty n) p = false := by
  induction n generalizing p with
  | zero => rfl
  | succ k ih =>
    cases p with
    | zero => rfl
    | succ j => exact ih j

theorem get_insert_same {s : LiveSet} {p : Nat} (h : p < s.length) :
    get (insert s p) p = true := by
  unfold get insert
  rw [getOpt_setAt_same h]

theorem get_insert_ne (s : LiveSet) {p q : Nat} (hne : p ≠ q) :
    get (insert s p) q = get s q := by
  unfold get insert
  rw [getOpt_setAt_ne hne]

theorem get_remove_same {s : LiveSet} {p : Nat} (h : p < s.length) :
    get (remove s p) p = false := by
  unfold get remove
  rw [getOpt_setAt_same h]

theorem get_remove_ne (s : LiveSet) {p q : Nat} (hne : p ≠ q) :
    get (remove s p) q = get s q := by
  unfold get remove
  rw [getOpt_setAt_ne hne]

theorem get_union (a b : LiveSet) (p : Nat) :
    get (union a b) p = (get a p || get b p) := by
  induction a generalizing b p with
  | nil =>
    rw [union_nil_left]
    unfold get; simp [getOpt]
  | cons x xs ih =>
    cases b with
    | nil =>
      rw [union_nil_right]
      unfold get; simp [getOpt]
    | cons y ys =>
      rw [union_cons_cons]
      cases p with
      | zero => rfl
      | succ k => exact ih ys k

theorem union_length_eq {a b : LiveSet} (h : a.length = b.length) :
    (union a b).length = a.length := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases b with
    | nil => cases h
    | cons y ys =>
      rw [union_cons_cons, List.length_cons, List.length_cons]
      exact congrArg Nat.succ (ih (Nat.succ.inj h))

theorem subset_refl (a : LiveSet) : subset a a := fun _ h => h

theorem subset_trans {a b c : LiveSet} (h1 : subset a b) (h2 : subset b c) :
    subset a c := fun p hp => h2 p (h1 p hp)

theorem empty_subset (n : Nat) (a : LiveSet) : subset (empty n) a := by
  intro p hp
  rw [get_empty] at hp
  cases hp

theorem subset_union_left (a b : LiveSet) : subset a (union a b) := by
  intro p hp
  rw [get_union, hp]
  rfl

theorem subset_union_right (a b : LiveSet) : subset b (union a b) := by
  intro p hp
  rw [get_union, hp, Bool.or_true]

theorem union_lub {a b c : LiveSet} (ha : subset a c) (hb : subset b c) :
    subset (union a b) c := by
  intro p hp
  rw [get_union] at hp
  cases hpa : get a p with
  | true => exact ha p hpa
  | false =>
    rw [hpa, Bool.false_or] at hp
    exact hb p hp

theorem union_mono {a a' b b' : LiveSet} (ha : subset a a') (hb : subset b b') :
    subset (union a b) (union a' b') :=
  union_lub (subset_trans ha (subset_union_left a' b')) (subset_trans hb (subset_union_right a' b'))

theorem insert_mono {a b : LiveSet} (h : subset a b) (heq : a.length = b.length) (p : Nat) :
    subset (insert a p) (insert b p) := by
  intro q hq
  by_cases hqp : p = q
  · subst hqp
    by_cases hlt : p < a.length
    · rw [get_insert_same (heq ▸ hlt)]
    · have hge : a.length ≤ p := Nat.le_of_not_lt hlt
      unfold get insert at hq
      have hlen : (setAt a p true).length = a.length := setAt_length a p true
      rw [getOpt_none_of_ge (hlen.symm ▸ hge)] at hq
      cases hq
  · rw [get_insert_ne b hqp]
    rw [get_insert_ne a hqp] at hq
    exact h q hq

theorem remove_mono {a b : LiveSet} (h : subset a b) (p : Nat) :
    subset (remove a p) (remove b p) := by
  intro q hq
  by_cases hqp : p = q
  · subst hqp
    by_cases hlt : p < a.length
    · rw [get_remove_same hlt] at hq
      cases hq
    · have hge : a.length ≤ p := Nat.le_of_not_lt hlt
      unfold get remove at hq
      have hlen : (setAt a p false).length = a.length := setAt_length a p false
      rw [getOpt_none_of_ge (hlen.symm ▸ hge)] at hq
      cases hq
  · rw [get_remove_ne b hqp]
    rw [get_remove_ne a hqp] at hq
    exact h q hq

theorem subset_insert_self {s : LiveSet} {p : Nat} : subset s (insert s p) := by
  intro q hq
  by_cases hqp : p = q
  · subst hqp
    have hlt : p < s.length := by
      unfold get at hq
      cases hg : getOpt s p with
      | none => rw [hg] at hq; cases hq
      | some v => exact getOpt_some_lt hg
    exact get_insert_same hlt
  · rw [get_insert_ne s hqp]
    exact hq

theorem remove_subset_self (s : LiveSet) (p : Nat) : subset (remove s p) s := by
  intro q hq
  by_cases hqp : p = q
  · subst hqp
    by_cases hlt : p < s.length
    · rw [get_remove_same hlt] at hq
      cases hq
    · unfold get remove at hq
      have hlen : (setAt s p false).length = s.length := setAt_length s p false
      rw [getOpt_none_of_ge (hlen.symm ▸ Nat.le_of_not_lt hlt)] at hq
      cases hq
  · rw [get_remove_ne s hqp] at hq
    exact hq

theorem eqBool_cons_cons (x : Bool) (xs : LiveSet) (y : Bool) (ys : LiveSet) :
    eqBool (x :: xs) (y :: ys) = ((x == y) && eqBool xs ys) := rfl

theorem eqBool_true_iff (a b : LiveSet) : eqBool a b = true ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons _ _ => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | cons x xs ih =>
    cases b with
    | nil => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | cons y ys =>
      rw [eqBool_cons_cons]
      constructor
      · intro h
        cases hxy : (x == y) with
        | false => rw [hxy, Bool.false_and] at h; cases h
        | true =>
          rw [hxy, Bool.true_and] at h
          have hx : x = y := beq_iff_eq.mp hxy
          have hxs : xs = ys := (ih ys).mp h
          rw [hx, hxs]
      · intro h
        injection h with hx hxs
        subst hx; subst hxs
        rw [beq_self_eq_true, Bool.true_and]
        exact (ih xs).mpr rfl

end LiveSet

end Part0Helpers

/-! ============================================================================
    PART 1: `check_liveness` (`compiler/rustc_mir_transform/src/liveness.rs`)
    ============================================================================ -/

section Part1Liveness

inductive ClosureTraitKind where
  | fn_
  | fnMut
  | fnOnce

def ClosureTraitKind.beq : ClosureTraitKind → ClosureTraitKind → Bool
  | .fn_, .fn_ => true
  | .fnMut, .fnMut => true
  | .fnOnce, .fnOnce => true
  | _, _ => false

inductive CaptureKind where
  | closure (k : ClosureTraitKind)
  | coroutine
  | coroutineClosure
  | none

def CaptureKind.isNotNone : CaptureKind → Bool
  | .none => false
  | _ => true

def CaptureKind.isFnMutClosure : CaptureKind → Bool
  | .closure .fnMut => true
  | _ => false

/-- Mirrors `rustc_middle::mir::AggregateKind` variants relevant to `liveness.rs:1447-1461`. -/
inductive AggKind where
  | closure (childId : Nat)
  | coroutine (childId : Nat)
  | coroutineClosure (childId : Nat)
  | adt

/-- Mirrors `PlaceContext` classification in `liveness.rs:1519-1575`. -/
inductive PlaceCtx where
  | store
  | setDiscriminant
  | callDest
  | yieldDest
  | asmOutput
  | copy
  | move
  | borrow
  | rawBorrow
  | drop
  | fakeBorrow
  | placeMention
  | storageLive
  | storageDead
  | varDebugInfo

inductive DefUse where
  | def_
  | use_

/-- Exact model of `DefUse::for_place` (`liveness.rs:1519-1575`).
`isIndirect` indicates whether any extra projection beyond the tracked place is a `Deref`;
`projEmpty` indicates whether the extra projection slice is empty. -/
def defUseForPlace (isIndirect projEmpty : Bool) (ctx : PlaceCtx) : Option DefUse :=
  match ctx with
  | .store | .setDiscriminant =>
    if isIndirect then some .use_
    else if projEmpty then some .def_
    else none
  | .callDest | .yieldDest | .asmOutput =>
    if isIndirect then some .use_ else none
  | .copy | .move | .borrow | .rawBorrow | .drop | .fakeBorrow | .placeMention =>
    some .use_
  | .storageLive | .storageDead | .varDebugInfo =>
    none

theorem defUse_indirect_store_is_use (projEmpty : Bool) :
    defUseForPlace true projEmpty .store = some .use_ := rfl

theorem defUse_direct_store_is_def :
    defUseForPlace false true .store = some .def_ := rfl

theorem defUse_field_store_is_none :
    defUseForPlace false false .store = none := rfl

/-- Reflects `liveness.rs:1353-1360` (`apply_call_return_effect` is a no-op) +
`liveness.rs:1540-1544`: direct `Call`/`Yield`/`AsmOutput` destinations never kill liveness. -/
theorem defUse_direct_call_never_kills (projEmpty : Bool) :
    defUseForPlace false projEmpty .callDest = none := rfl

/-- Apply a single `DefUse` effect to a `LiveSet`. -/
def applyDefUse (p : Nat) (du : Option DefUse) (s : LiveSet) : LiveSet :=
  match du with
  | some .def_ => LiveSet.remove s p
  | some .use_ => LiveSet.insert s p
  | none => s

theorem applyDefUse_length (p : Nat) (du : Option DefUse) (s : LiveSet) :
    (applyDefUse p du s).length = s.length := by
  cases du with
  | none => rfl
  | some d =>
    cases d with
    | def_ => exact LiveSet.remove_length s p
    | use_ => exact LiveSet.insert_length s p

theorem applyDefUse_mono (p : Nat) (du : Option DefUse) {a b : LiveSet}
    (h : LiveSet.subset a b) (hlen : a.length = b.length) :
    LiveSet.subset (applyDefUse p du a) (applyDefUse p du b) := by
  cases du with
  | none => exact h
  | some d =>
    cases d with
    | def_ => exact LiveSet.remove_mono h p
    | use_ => exact LiveSet.insert_mono h hlen p

/-- Insert all places in a list into `LiveSet` via `List.foldl` (zero `_unsafe_rec` helpers). -/
def insertAll (ps : List Nat) (s : LiveSet) : LiveSet :=
  ps.foldl LiveSet.insert s

theorem insertAll_nil (s : LiveSet) : insertAll [] s = s := rfl

theorem insertAll_cons (p : Nat) (ps : List Nat) (s : LiveSet) :
    insertAll (p :: ps) s = insertAll ps (LiveSet.insert s p) := rfl

theorem insertAll_length (ps : List Nat) (s : LiveSet) :
    (insertAll ps s).length = s.length := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [insertAll_cons, ih, LiveSet.insert_length]

theorem insertAll_mono (ps : List Nat) {a b : LiveSet}
    (h : LiveSet.subset a b) (hlen : a.length = b.length) :
    LiveSet.subset (insertAll ps a) (insertAll ps b) := by
  induction ps generalizing a b with
  | nil => exact h
  | cons p ps ih =>
    rw [insertAll_cons, insertAll_cons]
    exact ih (LiveSet.insert_mono h hlen p)
      (by rw [LiveSet.insert_length, LiveSet.insert_length, hlen])

theorem subset_insertAll (ps : List Nat) (s : LiveSet) :
    LiveSet.subset s (insertAll ps s) := by
  induction ps generalizing s with
  | nil => exact LiveSet.subset_refl s
  | cons p ps ih =>
    rw [insertAll_cons]
    exact LiveSet.subset_trans LiveSet.subset_insert_self (ih (LiveSet.insert s p))

theorem get_insertAll_mem {ps : List Nat} {s : LiveSet} {p : Nat}
    (hmem : p ∈ ps) (hlt : p < s.length) :
    LiveSet.get (insertAll ps s) p = true := by
  induction ps generalizing s with
  | nil => cases hmem
  | cons q qs ih =>
    rw [insertAll_cons]
    cases hmem with
    | head _ =>
      have h1 : LiveSet.get (LiveSet.insert s p) p = true := LiveSet.get_insert_same hlt
      exact subset_insertAll qs (LiveSet.insert s p) p h1
    | tail _ htail =>
      exact ih htail (by rw [LiveSet.insert_length]; exact hlt)

/-- MIR statements modeled for backward liveness (`liveness.rs:1372-1464`). -/
inductive LiveStmt where
  | assign (dest : Nat) (destIndirect destDirect : Bool) (rhsUses : List Nat)
  | selfAssignChecked (rhsUses : List Nat)
  | fakeReadForLetNone (p : Nat)
  | fakeReadForGuard (p : Nat)
  | fakeReadOther (p : Nat)
  | aggregate (dest : Nat) (kind : AggKind) (operands : List Nat)
  | nop

/-- MIR terminators modeled for backward liveness (`liveness.rs:1415-1440`). -/
inductive LiveTerm where
  | goto (target : Nat)
  | branch (cond : Nat) (tTarget fTarget : Nat)
  | ret
  | unwindResume
  | yield_ (next : Nat)
  | callDiverge (args : List Nat)
  | drop_ (place : Nat) (target : Nat) (unwind : Option Nat)
  | assert_ (cond : Nat) (target : Nat)

structure LiveBlock where
  stmts : List LiveStmt
  term : LiveTerm

/-- Oracle returning `dead_captures : Nat → Bool` (field index -> is dead) for a child closure/coroutine. -/
abbrev DeadCaptureOracle := Nat → Nat → Bool

/-- Filter aggregate operands by `dead_captures` (`liveness.rs:1453-1459`) via `List.foldr`. -/
def filterLiveOperands (isDead : Nat → Bool) (idx : Nat) (ops : List Nat) : List Nat :=
  ops.foldr
    (fun op ih i => if isDead i then ih (i + 1) else op :: ih (i + 1))
    (fun _ => [])
    idx

/-- Backward statement transfer mirroring `TransferFunction::visit_statement` + `visit_rvalue`
(`liveness.rs:1372-1464`).
When `handlesCoroClosure = false`, mirrors upstream `rustc` `liveness.rs:1448` (which matches
`Closure | Coroutine` and omits `CoroutineClosure`); when `true`, models the repaired visitor. -/
def transferStmt (oracle : DeadCaptureOracle) (handlesCoroClosure : Bool)
    (stmt : LiveStmt) (after : LiveSet) : LiveSet :=
  match stmt with
  | .fakeReadForLetNone _ | .fakeReadForGuard _ => after
  | .fakeReadOther p => LiveSet.insert after p
  | .assign dest isInd isDir rhsUses =>
    let s1 := applyDefUse dest (defUseForPlace isInd isDir .store) after
    insertAll rhsUses s1
  | .selfAssignChecked rhsUses =>
    insertAll rhsUses after
  | .aggregate dest kind ops =>
    let s1 := LiveSet.remove after dest
    match kind with
    | .closure cid | .coroutine cid =>
      insertAll (filterLiveOperands (oracle cid) 0 ops) s1
    | .coroutineClosure cid =>
      if handlesCoroClosure then
        insertAll (filterLiveOperands (oracle cid) 0 ops) s1
      else
        insertAll ops s1
    | .adt =>
      insertAll ops s1
  | .nop => after

theorem transferStmt_length (oracle : DeadCaptureOracle) (fix : Bool)
    (stmt : LiveStmt) (s : LiveSet) :
    (transferStmt oracle fix stmt s).length = s.length := by
  cases stmt with
  | assign dest isInd isDir rhsUses =>
    unfold transferStmt
    rw [insertAll_length, applyDefUse_length]
  | selfAssignChecked rhsUses =>
    exact insertAll_length rhsUses s
  | fakeReadForLetNone _ => rfl
  | fakeReadForGuard _ => rfl
  | fakeReadOther p => exact LiveSet.insert_length s p
  | aggregate dest kind ops =>
    unfold transferStmt
    cases kind with
    | closure cid => rw [insertAll_length, LiveSet.remove_length]
    | coroutine cid => rw [insertAll_length, LiveSet.remove_length]
    | coroutineClosure cid =>
      cases fix <;> simp [insertAll_length, LiveSet.remove_length]
    | adt => rw [insertAll_length, LiveSet.remove_length]
  | nop => rfl

theorem transferStmt_mono (oracle : DeadCaptureOracle) (fix : Bool) (stmt : LiveStmt)
    {a b : LiveSet} (h : LiveSet.subset a b) (hlen : a.length = b.length) :
    LiveSet.subset (transferStmt oracle fix stmt a) (transferStmt oracle fix stmt b) := by
  cases stmt with
  | assign dest isInd isDir rhsUses =>
    unfold transferStmt
    exact insertAll_mono rhsUses (applyDefUse_mono dest _ h hlen)
      (by rw [applyDefUse_length, applyDefUse_length, hlen])
  | selfAssignChecked rhsUses =>
    exact insertAll_mono rhsUses h hlen
  | fakeReadForLetNone _ => exact h
  | fakeReadForGuard _ => exact h
  | fakeReadOther p => exact LiveSet.insert_mono h hlen p
  | aggregate dest kind ops =>
    unfold transferStmt
    have hrm := LiveSet.remove_mono h dest
    have hrlen : (LiveSet.remove a dest).length = (LiveSet.remove b dest).length := by
      rw [LiveSet.remove_length, LiveSet.remove_length, hlen]
    cases kind with
    | closure cid => exact insertAll_mono _ hrm hrlen
    | coroutine cid => exact insertAll_mono _ hrm hrlen
    | coroutineClosure cid =>
      cases fix
      · exact insertAll_mono _ hrm hrlen
      · exact insertAll_mono _ hrm hrlen
    | adt => exact insertAll_mono _ hrm hrlen
  | nop => exact h

/-- Backward terminator transfer mirroring `TransferFunction::visit_terminator`
(`liveness.rs:1415-1440`). `byRefCaptures` lists tracked `PlaceIndex`es ending in `PlaceElem::Deref`. -/
def transferTerm (ck : CaptureKind) (byRefCaptures : List Nat)
    (term : LiveTerm) (after : LiveSet) : LiveSet :=
  match term with
  | .ret | .yield_ _ | .callDiverge _ =>
    if ck.isNotNone then insertAll byRefCaptures after else
      match term with
      | .callDiverge args => insertAll args after
      | _ => after
  | .goto target =>
    if target == 0 && ck.isNotNone then insertAll byRefCaptures after else after
  | .branch cond _ _ => LiveSet.insert after cond
  | .unwindResume => after
  | .drop_ _ _ _ => after
  | .assert_ _ _ => after

theorem transferTerm_length (ck : CaptureKind) (byRef : List Nat)
    (term : LiveTerm) (s : LiveSet) :
    (transferTerm ck byRef term s).length = s.length := by
  cases term with
  | ret => cases ck <;> simp [transferTerm, CaptureKind.isNotNone, insertAll_length]
  | yield_ _ => cases ck <;> simp [transferTerm, CaptureKind.isNotNone, insertAll_length]
  | callDiverge args =>
    cases ck <;> simp [transferTerm, CaptureKind.isNotNone, insertAll_length]
  | goto t =>
    unfold transferTerm
    cases hcond : (t == 0 && ck.isNotNone) with
    | false => simp [hcond]
    | true => simp [hcond, insertAll_length]
  | branch c _ _ => exact LiveSet.insert_length s c
  | unwindResume => rfl
  | drop_ _ _ _ => rfl
  | assert_ _ _ => rfl

theorem transferTerm_mono (ck : CaptureKind) (byRef : List Nat) (term : LiveTerm)
    {a b : LiveSet} (h : LiveSet.subset a b) (hlen : a.length = b.length) :
    LiveSet.subset (transferTerm ck byRef term a) (transferTerm ck byRef term b) := by
  cases term with
  | ret =>
    cases ck <;> simp [transferTerm, CaptureKind.isNotNone]
    all_goals first | exact insertAll_mono byRef h hlen | exact h
  | yield_ _ =>
    cases ck <;> simp [transferTerm, CaptureKind.isNotNone]
    all_goals first | exact insertAll_mono byRef h hlen | exact h
  | callDiverge args =>
    cases ck <;> simp [transferTerm, CaptureKind.isNotNone]
    all_goals first | exact insertAll_mono byRef h hlen | exact insertAll_mono args h hlen
  | goto t =>
    dsimp only [transferTerm]
    cases hcond : (t == 0 && ck.isNotNone) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact h
    | true =>
      simp only [ite_true]
      exact insertAll_mono byRef h hlen
  | branch c _ _ => exact LiveSet.insert_mono h hlen c
  | unwindResume => exact h
  | drop_ _ _ _ => exact h
  | assert_ _ _ => exact h

/-- Backward statement-list transfer (reverse order through basic block) via `List.foldr`. -/
def transferStmts (oracle : DeadCaptureOracle) (fix : Bool)
    (stmts : List LiveStmt) (after : LiveSet) : LiveSet :=
  stmts.foldr (transferStmt oracle fix) after

theorem transferStmts_length (oracle : DeadCaptureOracle) (fix : Bool)
    (stmts : List LiveStmt) (s : LiveSet) :
    (transferStmts oracle fix stmts s).length = s.length := by
  induction stmts with
  | nil => rfl
  | cons st rest ih =>
    unfold transferStmts
    simp only [List.foldr_cons]
    rw [transferStmt_length]
    exact ih

theorem transferStmts_mono (oracle : DeadCaptureOracle) (fix : Bool) (stmts : List LiveStmt)
    {a b : LiveSet} (h : LiveSet.subset a b) (hlen : a.length = b.length) :
    LiveSet.subset (transferStmts oracle fix stmts a) (transferStmts oracle fix stmts b) := by
  induction stmts with
  | nil => exact h
  | cons st rest ih =>
    unfold transferStmts
    simp only [List.foldr_cons]
    exact transferStmt_mono oracle fix st ih
      (by
        show (rest.foldr (transferStmt oracle fix) a).length =
             (rest.foldr (transferStmt oracle fix) b).length
        exact (transferStmts_length oracle fix rest a).trans
          (hlen.trans (transferStmts_length oracle fix rest b).symm))

def termSuccessors : LiveTerm → List Nat
  | .goto t => [t]
  | .branch _ t f => [t, f]
  | .ret => []
  | .unwindResume => []
  | .yield_ t => [t]
  | .callDiverge _ => []
  | .drop_ _ t none => [t]
  | .drop_ _ t (some u) => [t, u]
  | .assert_ _ t => [t]

/-- Exact `FnMut` CFG loop rewrite (`liveness.rs:115-127`): replaces `Return` and `UnwindResume`
with `Goto START_BLOCK` (`bb0`). -/
def fnMutRewriteTerm : LiveTerm → LiveTerm
  | .ret => .goto 0
  | .unwindResume => .goto 0
  | t => t

def fnMutRewriteBlock (b : LiveBlock) : LiveBlock :=
  { stmts := b.stmts, term := fnMutRewriteTerm b.term }

def fnMutRewriteBody (ck : CaptureKind) (blocks : List LiveBlock) : List LiveBlock :=
  if ck.isFnMutClosure then blocks.map fnMutRewriteBlock else blocks

/-- Join successor entry states for a block in backward analysis via `List.foldr`. -/
def joinSuccs (numPlaces : Nat) (entries : List LiveSet) (succs : List Nat) : LiveSet :=
  succs.foldr
    (fun s acc =>
      let cur := match getOpt entries s with
                 | some ls => ls
                 | none => LiveSet.empty numPlaces
      LiveSet.union cur acc)
    (LiveSet.empty numPlaces)

theorem joinSuccs_nil (numPlaces : Nat) (entries : List LiveSet) :
    joinSuccs numPlaces entries [] = LiveSet.empty numPlaces := rfl

theorem joinSuccs_cons (numPlaces : Nat) (entries : List LiveSet) (s : Nat) (rest : List Nat) :
    joinSuccs numPlaces entries (s :: rest) =
    LiveSet.union (match getOpt entries s with | some ls => ls | none => LiveSet.empty numPlaces)
                  (joinSuccs numPlaces entries rest) := rfl

theorem joinSuccs_length {numPlaces : Nat} {entries : List LiveSet}
    (hlen : ∀ s ∈ entries, s.length = numPlaces) (succs : List Nat) :
    (joinSuccs numPlaces entries succs).length = numPlaces := by
  induction succs with
  | nil => exact LiveSet.empty_length numPlaces
  | cons t ts ih =>
    rw [joinSuccs_cons]
    have hcur : (match getOpt entries t with | some ls => ls | none => LiveSet.empty numPlaces).length = numPlaces := by
      cases hg : getOpt entries t with
      | none => exact LiveSet.empty_length numPlaces
      | some ls =>
        have hmem : ls ∈ entries := by
          clear ih
          induction entries generalizing t with
          | nil => cases hg
          | cons e es ihe =>
            cases t with
            | zero =>
              simp only [getOpt_cons_zero] at hg
              injection hg with heq
              subst heq
              exact List.Mem.head es
            | succ k =>
              exact List.Mem.tail e (ihe (fun x hx => hlen x (List.Mem.tail e hx)) k hg)
        exact hlen ls hmem
    rw [LiveSet.union_length_eq (hcur.trans ih.symm), hcur]

theorem getOpt_subset_joinSuccs {numPlaces : Nat} {entries : List LiveSet} {succs : List Nat}
    {t : Nat} {ls : LiveSet} (hmem : t ∈ succs) (hget : getOpt entries t = some ls) :
    LiveSet.subset ls (joinSuccs numPlaces entries succs) := by
  induction succs with
  | nil => cases hmem
  | cons s ss ih =>
    rw [joinSuccs_cons]
    cases hmem with
    | head _ =>
      rw [hget]
      exact LiveSet.subset_union_left ls (joinSuccs numPlaces entries ss)
    | tail _ htail =>
      exact LiveSet.subset_trans (ih htail) (LiveSet.subset_union_right _ _)

/-- A state table `entries` is a sound backward post-fixpoint for `blocks`. -/
def IsBackwardPostFixpoint (oracle : DeadCaptureOracle) (fix : Bool)
    (ck : CaptureKind) (byRef : List Nat) (numPlaces : Nat)
    (blocks : List LiveBlock) (entries : List LiveSet) : Prop :=
  (∀ s ∈ entries, s.length = numPlaces) ∧
  ∀ (bb : Nat) (b : LiveBlock) (entry : LiveSet),
    getOpt blocks bb = some b →
    getOpt entries bb = some entry →
    let exitLive := joinSuccs numPlaces entries (termSuccessors b.term)
    let beforeTerm := transferTerm ck byRef b.term exitLive
    let beforeStmts := transferStmts oracle fix b.stmts beforeTerm
    LiveSet.subset beforeStmts entry

/-- **Theorem 1.1 (`fnMut_postFixpoint_propagates_start_to_exits`)**:
For any `FnMut` closure body rewritten by `fnMutRewriteBody`, in every backward post-fixpoint
every block whose original terminator was `Return` or `UnwindResume` receives `entry(START_BLOCK)`
inside its exit liveness set, closing the multi-invocation loop (`liveness.rs:115-127`). -/
theorem fnMut_postFixpoint_propagates_start_to_exits
    (numPlaces : Nat)
    (blocks : List LiveBlock) (entries : List LiveSet)
    (bb : Nat) (b : LiveBlock) (entry0 : LiveSet)
    (hget : getOpt blocks bb = some b)
    (hexit : b.term = .ret ∨ b.term = .unwindResume)
    (h0 : getOpt entries 0 = some entry0) :
    let rewritten := fnMutRewriteBody (.closure .fnMut) blocks
    ∃ b', getOpt rewritten bb = some b' ∧
      LiveSet.subset entry0 (joinSuccs numPlaces entries (termSuccessors b'.term)) := by
  refine ⟨fnMutRewriteBlock b, ?_, ?_⟩
  · unfold fnMutRewriteBody CaptureKind.isFnMutClosure
    simp only [ite_true]
    rw [getOpt_map, hget]
    rfl
  · cases hexit with
    | inl hret =>
      unfold fnMutRewriteBlock
      rw [hret]
      exact getOpt_subset_joinSuccs (List.Mem.head []) h0
    | inr hunw =>
      unfold fnMutRewriteBlock
      rw [hunw]
      exact getOpt_subset_joinSuccs (List.Mem.head []) h0

/-- One backward Kleene iteration step over all blocks. -/
def backwardStep (oracle : DeadCaptureOracle) (fix : Bool) (ck : CaptureKind)
    (byRef : List Nat) (numPlaces : Nat) (blocks : List LiveBlock)
    (entries : List LiveSet) : List LiveSet :=
  blocks.map fun b =>
    let exitLive := joinSuccs numPlaces entries (termSuccessors b.term)
    let beforeTerm := transferTerm ck byRef b.term exitLive
    transferStmts oracle fix b.stmts beforeTerm

def runBackwardIter (oracle : DeadCaptureOracle) (fix : Bool) (ck : CaptureKind)
    (byRef : List Nat) (numPlaces : Nat) (blocks : List LiveBlock)
    (fuel : Nat) (entries : List LiveSet) : List LiveSet :=
  @Nat.recCompiled (fun _ => List LiveSet → List LiveSet)
    (fun e => e)
    (fun _ ih e => ih (backwardStep oracle fix ck byRef numPlaces blocks e))
    fuel entries

def runBackwardLiveness (oracle : DeadCaptureOracle) (fix : Bool) (ck : CaptureKind)
    (byRef : List Nat) (numPlaces : Nat) (blocks : List LiveBlock) (fuel : Nat) :
    List LiveSet :=
  let rwBlocks := fnMutRewriteBody ck blocks
  let init := List.replicate rwBlocks.length (LiveSet.empty numPlaces)
  runBackwardIter oracle fix ck byRef numPlaces rwBlocks fuel init

theorem backwardStep_lengths {oracle : DeadCaptureOracle} {fix : Bool} {ck : CaptureKind}
    {byRef : List Nat} {numPlaces : Nat} {blocks : List LiveBlock} {entries : List LiveSet}
    (hlen : ∀ s ∈ entries, s.length = numPlaces) :
    ∀ s ∈ backwardStep oracle fix ck byRef numPlaces blocks entries, s.length = numPlaces := by
  intro s hs
  unfold backwardStep at hs
  induction blocks with
  | nil => cases hs
  | cons b bs ih =>
    cases hs with
    | head _ =>
      rw [transferStmts_length, transferTerm_length]
      exact joinSuccs_length hlen (termSuccessors b.term)
    | tail _ htail => exact ih htail

/-- Pointwise subset relation on per-block `LiveSet` tables. -/
def TableSubset (t1 t2 : List LiveSet) : Prop :=
  ∀ (bb : Nat) (s1 s2 : LiveSet),
    getOpt t1 bb = some s1 → getOpt t2 bb = some s2 → LiveSet.subset s1 s2

theorem joinSuccs_mono {numPlaces : Nat} {t1 t2 : List LiveSet}
    (hsub : TableSubset t1 t2) (hlen : t1.length = t2.length) (succs : List Nat) :
    LiveSet.subset (joinSuccs numPlaces t1 succs) (joinSuccs numPlaces t2 succs) := by
  induction succs with
  | nil => exact LiveSet.subset_refl _
  | cons s ss ih =>
    unfold joinSuccs
    have hcur : LiveSet.subset
        (match getOpt t1 s with | some ls => ls | none => LiveSet.empty numPlaces)
        (match getOpt t2 s with | some ls => ls | none => LiveSet.empty numPlaces) := by
      cases hg1 : getOpt t1 s with
      | none => exact LiveSet.empty_subset numPlaces _
      | some ls1 =>
        have hlt : s < t2.length := hlen ▸ getOpt_some_lt hg1
        cases hg2 : getOpt t2 s with
        | none =>
          have hcontra : ∀ (xs : List LiveSet) (i : Nat), i < xs.length → getOpt xs i ≠ none := by
            intro xs
            induction xs with
            | nil => intro i hi; exact False.elim (nat_not_lt_zero i hi)
            | cons x xs ihx =>
              intro i hi
              cases i with
              | zero => intro h; cases h
              | succ k => exact ihx k (Nat.lt_of_succ_lt_succ hi)
          exact False.elim (hcontra t2 s hlt hg2)
        | some ls2 => exact hsub s ls1 ls2 hg1 hg2
    exact LiveSet.union_mono hcur ih

/-- **Theorem 1.2 (`backwardStep_monotone`)**:
One iteration of `MaybeLivePlaces` backward dataflow is monotone on the per-block bitset lattice. -/
theorem backwardStep_monotone (oracle : DeadCaptureOracle) (fix : Bool) (ck : CaptureKind)
    (byRef : List Nat) (numPlaces : Nat) (blocks : List LiveBlock)
    {t1 t2 : List LiveSet}
    (h1len : ∀ s ∈ t1, s.length = numPlaces)
    (h2len : ∀ s ∈ t2, s.length = numPlaces)
    (htlen : t1.length = t2.length)
    (hsub : TableSubset t1 t2) :
    TableSubset (backwardStep oracle fix ck byRef numPlaces blocks t1)
                (backwardStep oracle fix ck byRef numPlaces blocks t2) := by
  intro bb s1 s2 hs1 hs2
  unfold backwardStep at hs1 hs2
  rw [getOpt_map] at hs1 hs2
  cases hb : getOpt blocks bb with
  | none => rw [hb] at hs1; cases hs1
  | some b =>
    rw [hb] at hs1 hs2
    injection hs1 with hs1eq
    injection hs2 with hs2eq
    subst hs1eq; subst hs2eq
    have hj := joinSuccs_mono (numPlaces := numPlaces) hsub htlen (termSuccessors b.term)
    have hjlen : (joinSuccs numPlaces t1 (termSuccessors b.term)).length =
                 (joinSuccs numPlaces t2 (termSuccessors b.term)).length := by
      rw [joinSuccs_length h1len, joinSuccs_length h2len]
    have ht := transferTerm_mono ck byRef b.term hj hjlen
    have htlen' : (transferTerm ck byRef b.term (joinSuccs numPlaces t1 (termSuccessors b.term))).length =
                  (transferTerm ck byRef b.term (joinSuccs numPlaces t2 (termSuccessors b.term))).length := by
      rw [transferTerm_length, transferTerm_length, hjlen]
    exact transferStmts_mono oracle fix b.stmts ht htlen'

/-- **Theorem 1.3 (`fnMut_vs_fnonce_accumulator_witness`)**:
Constructive witness on the stateful counter closure (`let prev = acc; acc = prev + 1; prev`):
place `0 = acc`, place `1 = prev`.
Under `FnMut`, the trailing store `acc = prev + 1` has `acc` LIVE immediately after it (because
`Return -> Goto(bb0)` loops back to `prev = acc`); under `FnOnce`, `acc` is DEAD after the store. -/
def accClosureBody : List LiveBlock :=
  [ { stmts := [ .assign 1 false true [0]   -- prev = acc
               , .assign 0 false true [1] ] -- acc = prev + 1
    , term := .ret } ]

def noOracle : DeadCaptureOracle := fun _ _ => false

theorem fnMut_acc_entry_live_and_fnonce_exit_dead :
    let fnMutRes := runBackwardLiveness noOracle false (.closure .fnMut) [] 2 accClosureBody 4
    let fnOnceRes := runBackwardLiveness noOracle false (.closure .fnOnce) [] 2 accClosureBody 4
    -- Under FnMut, `acc` (place 0) is live at bb0 entry AND at exit (looped to bb0):
    (match getOpt fnMutRes 0 with | some s => LiveSet.get s 0 | none => false) = true ∧
    (LiveSet.get (joinSuccs 2 fnMutRes [0]) 0) = true ∧
    -- Under FnOnce, `acc` is live at bb0 entry (read by `prev = acc`),
    -- but DEAD at bb0 exit (empty successor list -> `acc = prev + 1` is dead!):
    (match getOpt fnOnceRes 0 with | some s => LiveSet.get s 0 | none => false) = true ∧
    (LiveSet.get (joinSuccs 2 fnOnceRes []) 0) = false := by
  decide

/-- **Theorem 1.4 (`coroutineClosure_two_layer_blind_spot`)**:
Constructive proof of BOTH layers of the Edition 2024 `async move || { u = 30; }` asymmetry:
* **Layer 1 (`AsyncFnOnce` / by-value inner coroutine)**:
  - Child `Coroutine` (`cid = 1`, `byRef = []`) overwrites capture `0` (`u = 30`) and returns ->
    `u` is DEAD (`deadCapture = true`).
  - Enclosing function constructs `AggregateKind::CoroutineClosure 1 [0]`.
  - Under upstream `handlesCoroClosure = false` (`liveness.rs:1448`), enclosing function marks `u`
    **LIVE** (suppressing `unused_variables`), whereas `AggregateKind::Closure` / `Coroutine` AND
    the repaired `handlesCoroClosure = true` mark `u` **DEAD**!
* **Layer 2 (`AsyncFnMut` / lending `&mut` inner coroutine + skipped `synthetic_by_move`)**:
  - Lending inner `Coroutine` (`cid = 2`, `byRef = [0]`) overwrites `*(_1.0) = 30` and returns ->
    `transferTerm .coroutine [0] .ret` marks `0` **LIVE** (`deadCapture = false`), so EVEN with
    `handlesCoroClosure = true`, the enclosing function STILL observes `0` as LIVE! -/
def deadWriteBody : List LiveBlock :=
  [ { stmts := [ .assign 0 false true [] ] -- u = 30 (no read of u)
    , term := .ret } ]

/-- Collect `ever_live` across block end and every pre-statement point (`liveness.rs:686-726`) via `List.foldr`. -/
def everLiveStmts (oracle : DeadCaptureOracle) (fix : Bool)
    (stmts : List LiveStmt) (after : LiveSet) : LiveSet × LiveSet :=
  stmts.foldr
    (fun st acc =>
      let liveBeforeSt := transferStmt oracle fix st acc.1
      (liveBeforeSt, LiveSet.union liveBeforeSt acc.2))
    (after, after)

def everLiveBlock (oracle : DeadCaptureOracle) (fix : Bool) (ck : CaptureKind)
    (byRef : List Nat) (numPlaces : Nat) (entries : List LiveSet) (b : LiveBlock) : LiveSet :=
  let exitLive := joinSuccs numPlaces entries (termSuccessors b.term)
  let beforeTerm := transferTerm ck byRef b.term exitLive
  let (_, everStmts) := everLiveStmts oracle fix b.stmts beforeTerm
  LiveSet.union beforeTerm everStmts

def isCaptureDeadInBody (ck : CaptureKind) (byRef : List Nat) (body : List LiveBlock) : Bool :=
  let res := runBackwardLiveness noOracle false ck byRef 1 body 3
  let everAll := body.foldl
    (fun acc b => LiveSet.union acc (everLiveBlock noOracle false ck byRef 1 res b))
    (LiveSet.empty 1)
  !(LiveSet.get everAll 0)

def outerAggBody (kind : AggKind) : List LiveBlock :=
  [ { stmts := [ .assign 0 false true []    -- let mut u = 10
               , .fakeReadForLetNone 0
               , .aggregate 1 kind [0]      -- let _c = {closure/coro/coro_closure} { u }
               , .fakeReadForLetNone 1 ]
    , term := .ret } ]

def coroClosureOracle : DeadCaptureOracle := fun cid field =>
  if cid == 1 && field == 0 then
    isCaptureDeadInBody .coroutine [] deadWriteBody         -- AsyncFnOnce: by-value inner coro
  else if cid == 2 && field == 0 then
    isCaptureDeadInBody .coroutine [0] deadWriteBody        -- AsyncFnMut: lending &mut inner coro
  else
    false

def isOuterLocalLive (fix : Bool) (kind : AggKind) : Bool :=
  let res := runBackwardLiveness coroClosureOracle fix .none [] 2 (outerAggBody kind) 3
  -- Check liveness of `u` (place 0) immediately after `u = 10`, i.e., before `aggregate`:
  let afterRet := LiveSet.empty 2
  let beforeAgg := transferStmts coroClosureOracle fix
    [ .fakeReadForLetNone 0, .aggregate 1 kind [0], .fakeReadForLetNone 1 ] afterRet
  let _ := res
  LiveSet.get beforeAgg 0

theorem edition2024_coroutineClosure_two_layer_blind_spot :
    -- Layer 1a: by-value inner coroutine (AsyncFnOnce) DOES detect capture 0 as dead:
    isCaptureDeadInBody .coroutine [] deadWriteBody = true ∧
    -- Layer 1b: sync Closure and async-block Coroutine propagate dead capture -> outer u is DEAD:
    isOuterLocalLive false (.closure 1) = false ∧
    isOuterLocalLive false (.coroutine 1) = false ∧
    -- Layer 1c: upstream `liveness.rs:1448` (`fix = false`) omits CoroutineClosure -> outer u FALSELY LIVE:
    isOuterLocalLive false (.coroutineClosure 1) = true ∧
    -- Layer 1d: repaired visitor (`fix = true`) restores outer u DEAD for AsyncFnOnce:
    isOuterLocalLive true (.coroutineClosure 1) = false ∧
    -- Layer 2: lending AsyncFnMut inner coroutine (`byRef = [0]`) marks capture 0 LIVE at Return,
    -- so even with `fix = true`, outer u STILL stays LIVE unless lending indirection is resolved:
    isCaptureDeadInBody .coroutine [0] deadWriteBody = false ∧
    isOuterLocalLive true (.coroutineClosure 2) = true := by
  decide

/-- **Theorem 1.5 (`mergeGuards_sound` & `maybeDropGuard_suppression`)**:
Exact semantics of `merge_guards` (`liveness.rs:814-855`) and `report_unused_assignments`
drop-guard gating (`liveness.rs:1212`). -/
def mergeGuardEverLive (armEverLive guardEverLive : Bool) : Bool :=
  armEverLive || guardEverLive

theorem mergeGuard_no_false_unused_if_either_live (a g : Bool) :
    (a = true ∨ g = true) → mergeGuardEverLive a g = true := by
  intro h
  cases h with
  | inl ha => rw [ha]; rfl
  | inr hg => cases a <;> rw [hg] <;> rfl

def shouldReportUnusedAssign (isLive isDirect isMaybeDropGuard : Bool) : Bool :=
  (!isLive) && (isDirect || (!isMaybeDropGuard))

theorem maybeDropGuard_suppresses_field_write_only :
    shouldReportUnusedAssign false false true = false ∧
    shouldReportUnusedAssign false true true = true ∧
    shouldReportUnusedAssign false false false = true ∧
    shouldReportUnusedAssign true true false = false := by
  decide

end Part1Liveness

/-! ============================================================================
    PART 2: `MentionedItems` (`mentioned_items.rs` + `rustc_monomorphize::collector`)
    ============================================================================ -/

section Part2MentionedItems

/-- The 6 MIR operations visited by `MentionedItemsVisitor` (`mentioned_items.rs:38-118`)
plus non-mentioning statements. -/
inductive MirMentionOp where
  | call (fnId : Nat)
  | tailCall (fnId : Nat)
  | drop_ (tyId : Nat)
  | inlineAsmSymFn (fnId : Nat)
  | unsizeCast (srcTy dstTy : Nat) (isArrayToSlice : Bool)
  | closureFnPtr (closureId : Nat)
  | reifyFnPtr (fnId : Nat)
  | other

inductive MentionedItem where
  | fn_ (fnId : Nat)
  | drop_ (tyId : Nat)
  | unsizeCast (srcTy dstTy : Nat)
  | closure (closureId : Nat)

def MentionedItem.beq : MentionedItem → MentionedItem → Bool
  | .fn_ a, .fn_ b => a == b
  | .drop_ a, .drop_ b => a == b
  | .unsizeCast s1 d1, .unsizeCast s2 d2 => (s1 == s2) && (d1 == d2)
  | .closure a, .closure b => a == b
  | _, _ => false

theorem MentionedItem.beq_iff_eq (x y : MentionedItem) :
    MentionedItem.beq x y = true ↔ x = y := by
  cases x <;> cases y <;> simp [MentionedItem.beq]

def memItem (x : MentionedItem) (xs : List MentionedItem) : Bool :=
  xs.foldr (fun y ih => MentionedItem.beq x y || ih) false

theorem memItem_cons (x y : MentionedItem) (ys : List MentionedItem) :
    memItem x (y :: ys) = (MentionedItem.beq x y || memItem x ys) := rfl

theorem memItem_true_iff (x : MentionedItem) (xs : List MentionedItem) :
    memItem x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | cons y ys ih =>
    rw [memItem_cons]
    constructor
    · intro h
      cases hxy : MentionedItem.beq x y with
      | true =>
        rw [(MentionedItem.beq_iff_eq x y).mp hxy]
        exact List.Mem.head ys
      | false =>
        rw [hxy, Bool.false_or] at h
        exact List.Mem.tail y (ih.mp h)
    · intro h
      cases h with
      | head _ =>
        have hself : MentionedItem.beq x x = true := (MentionedItem.beq_iff_eq x x).mpr rfl
        rw [hself]; rfl
      | tail _ htail =>
        rw [ih.mpr htail, Bool.or_true]

/-- Single-operation projection of `MentionedItemsVisitor` (`mentioned_items.rs:38-118`). -/
def opToMentioned : MirMentionOp → Option MentionedItem
  | .call f => some (.fn_ f)
  | .tailCall f => some (.fn_ f)
  | .drop_ t => some (.drop_ t)
  | .inlineAsmSymFn f => some (.fn_ f)
  | .unsizeCast s d isArrSlice =>
    if isArrSlice then none else some (.unsizeCast s d)
  | .closureFnPtr c => some (.closure c)
  | .reifyFnPtr f => some (.fn_ f)
  | .other => none

/-- Exact list produced by `MentionedItems::run_pass` (`mentioned_items.rs:26-30`) via `List.foldr`. -/
def collectMentioned (ops : List MirMentionOp) : List MentionedItem :=
  ops.foldr
    (fun op ih => match opToMentioned op with | some item => item :: ih | none => ih)
    []

theorem collectMentioned_cons (o : MirMentionOp) (os : List MirMentionOp) :
    collectMentioned (o :: os) =
    match opToMentioned o with
    | some item => item :: collectMentioned os
    | none => collectMentioned os := rfl

theorem mem_collectMentioned_of_mem {op : MirMentionOp} {item : MentionedItem}
    {ops : List MirMentionOp} (hmem : op ∈ ops) (hproj : opToMentioned op = some item) :
    item ∈ collectMentioned ops := by
  induction ops with
  | nil => cases hmem
  | cons o os ih =>
    rw [collectMentioned_cons]
    cases hmem with
    | head _ =>
      rw [hproj]
      exact List.Mem.head _
    | tail _ htail =>
      cases opToMentioned o with
      | none => exact ih htail
      | some m => exact List.Mem.tail m (ih htail)

/-- **Theorem 2.1 (`mentioned_overapproximates_post_dce_used`)**:
Whenever runtime optimizations (`run_optimization_passes`) only drop dead ops so that
`∀ op ∈ postOptOps, op ∈ preOptOps`, every item used by `MirUsedCollector` on `postOptOps`
is already present in the pre-optimization `body.mentioned_items()` list. -/
theorem mentioned_overapproximates_post_dce_used
    {preOptOps postOptOps : List MirMentionOp}
    (hdce : ∀ op, op ∈ postOptOps → op ∈ preOptOps) :
    ∀ item, item ∈ collectMentioned postOptOps → item ∈ collectMentioned preOptOps := by
  intro item hitem
  induction postOptOps with
  | nil => cases hitem
  | cons o os ih =>
    rw [collectMentioned_cons] at hitem
    cases hproj : opToMentioned o with
    | none =>
      rw [hproj] at hitem
      exact ih (fun op hop => hdce op (List.Mem.tail o hop)) hitem
    | some m =>
      rw [hproj] at hitem
      cases hitem with
      | head _ =>
        exact mem_collectMentioned_of_mem (hdce o (List.Mem.head os)) hproj
      | tail _ htail =>
        exact ih (fun op hop => hdce op (List.Mem.tail o hop)) htail

/-- Models `collector.rs:1390-1395`: skipping items already recorded in `used_mentioned_items`. -/
def filterUnseenMentioned (usedMentioned ms : List MentionedItem) : List MentionedItem :=
  ms.foldr (fun m ih => if memItem m usedMentioned then ih else m :: ih) []

theorem filterUnseenMentioned_cons (used : List MentionedItem) (m : MentionedItem)
    (rest : List MentionedItem) :
    filterUnseenMentioned used (m :: rest) =
    if memItem m used then filterUnseenMentioned used rest
    else m :: filterUnseenMentioned used rest := rfl

theorem mem_filterUnseen_iff (used ms : List MentionedItem) (x : MentionedItem) :
    x ∈ filterUnseenMentioned used ms ↔ x ∈ ms ∧ x ∉ used := by
  induction ms with
  | nil =>
    exact ⟨fun h => (by cases h), fun h => (by cases h.1)⟩
  | cons m rest ih =>
    rw [filterUnseenMentioned_cons]
    cases hmem : memItem m used with
    | true =>
      have hmIn : m ∈ used := (memItem_true_iff m used).mp hmem
      simp only [ite_true]
      rw [ih]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨List.Mem.tail m h1, h2⟩
      · intro ⟨h1, h2⟩
        cases h1 with
        | head _ => exact False.elim (h2 hmIn)
        | tail _ ht => exact ⟨ht, h2⟩
    | false =>
      have hmNotIn : m ∉ used := fun hin => by
        have ht := (memItem_true_iff m used).mpr hin
        rw [hmem] at ht; cases ht
      simp only [Bool.false_eq_true, ite_false]
      constructor
      · intro h
        cases h with
        | head _ => exact ⟨List.Mem.head rest, hmNotIn⟩
        | tail _ ht =>
          let ⟨h1, h2⟩ := ih.mp ht
          exact ⟨List.Mem.tail m h1, h2⟩
      · intro ⟨h1, h2⟩
        cases h1 with
        | head _ => exact List.Mem.head _
        | tail _ ht => exact List.Mem.tail m (ih.mpr ⟨ht, h2⟩)

/-- **Theorem 2.2 (`used_mentioned_dedup_preserves_total_checked_set`)**:
The `used_mentioned_items` deduplication optimization in `collect_items_of_instance`
(`collector.rs:1348-1395`) checks the EXACT same total set of items (`used ∪ mentioned`)
as an unoptimized traversal of `used ++ mentioned`. -/
theorem used_mentioned_dedup_preserves_total_checked_set
    (used mentioned : List MentionedItem) (x : MentionedItem) :
    (x ∈ used ∨ x ∈ filterUnseenMentioned used mentioned) ↔
    (x ∈ used ∨ x ∈ mentioned) := by
  rw [mem_filterUnseen_iff]
  constructor
  · intro h
    cases h with
    | inl hu => exact Or.inl hu
    | inr hm => exact Or.inr hm.1
  · intro h
    cases h with
    | inl hu => exact Or.inl hu
    | inr hm =>
      cases hmem : memItem x used with
      | true => exact Or.inl ((memItem_true_iff x used).mp hmem)
      | false =>
        refine Or.inr ⟨hm, fun hin => ?_⟩
        have ht := (memItem_true_iff x used).mpr hin
        rw [hmem] at ht; cases ht

/-- Models `collector.rs:575-577` + `1382-1396`: `UsedItems` feeds BOTH `usageMap` (codegen)
and PME checking; `MentionedItems` feeds ONLY PME checking (`usageMap` unchanged). -/
structure CollectorOutcome where
  codegenItems : List MentionedItem
  pmeCheckedItems : List MentionedItem

def runSingleBodyCollector (isRoot : Bool) (preOptOps postOptOps : List MirMentionOp) :
    CollectorOutcome :=
  if !isRoot then
    { codegenItems := [], pmeCheckedItems := [] }
  else
    let used := collectMentioned postOptOps
    let mentioned := collectMentioned preOptOps
    let extra := filterUnseenMentioned used mentioned
    { codegenItems := used
    , pmeCheckedItems := used ++ extra }

/-- **Theorem 2.3 (`post_dce_pme_preservation_when_root`)**:
Given a root body (`isRoot = true`) and any DCE pass (`postOptOps ⊆ preOptOps`), every
pre-optimization mentioned item (including dead calls/drops/vtables/asm/reify/closures)
remains in `pmeCheckedItems` after optimization, while dead items are excluded from
`codegenItems` (`usage_map`). -/
theorem post_dce_pme_preservation_when_root
    {preOptOps postOptOps : List MirMentionOp}
    (hdce : ∀ op, op ∈ postOptOps → op ∈ preOptOps)
    (m : MentionedItem) :
    (m ∈ (runSingleBodyCollector true preOptOps postOptOps).pmeCheckedItems ↔
     m ∈ collectMentioned preOptOps) ∧
    (m ∉ collectMentioned postOptOps →
     m ∉ (runSingleBodyCollector true preOptOps postOptOps).codegenItems) := by
  unfold runSingleBodyCollector
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  constructor
  · rw [List.mem_append, used_mentioned_dedup_preserves_total_checked_set]
    constructor
    · intro h
      cases h with
      | inl hu => exact mentioned_overapproximates_post_dce_used hdce m hu
      | inr hm => exact hm
    · intro hm; exact Or.inr hm
  · intro hnot; exact hnot

/-- Models `cross_crate_inlinable` (`cross_crate_inline.rs:108-116`) + `is_root` (`collector.rs:1751-1778`)
in an `rlib` crate: `cross_crate_inlinable` reads post-optimization `optimized_mir`. -/
def isRlibRoot (inlineNever : Bool) (optLevel : Nat) (threshold : Nat)
    (postOptOps : List MirMentionOp) : Bool :=
  if inlineNever then true
  else if optLevel == 0 then true
  else
    let hasCall := postOptOps.any fun op =>
      match op with | .call _ | .tailCall _ | .drop_ _ | .inlineAsmSymFn _ => true | _ => false
    let smallLeaf := (!hasCall) && (postOptOps.length ≤ threshold)
    !smallLeaf

/-- **Theorem 2.4 (`rlib_cross_crate_inlinable_opt_level_flip`)**:
Constructive proof of the empirical `rlib` seam (Probe B4): when `f` has a dead branch
calling `trigger_pme` (present in `preOptOps`, removed in `postOptOps` at `-O3`),
* without `#[inline(never)]`: `-O0` marks `f` a root and checks `trigger_pme`, whereas `-O3`
  marks `f` `cross_crate_inlinable` -> NOT a root -> `pmeCheckedItems = []`!
* with `#[inline(never)]` (or `threshold = 0` with `postOptOps.length > 0`, or bin root):
  BOTH `-O0` and `-O3` check `trigger_pme`! -/
theorem rlib_cross_crate_inlinable_opt_level_flip :
    let preOpt := [MirMentionOp.other, MirMentionOp.call 42]
    let postOptO0 := preOpt
    let postOptO3 := [MirMentionOp.other]
    let outDefaultO0 := runSingleBodyCollector (isRlibRoot false 0 5 postOptO0) preOpt postOptO0
    let outDefaultO3 := runSingleBodyCollector (isRlibRoot false 3 5 postOptO3) preOpt postOptO3
    let outPinnedO3 := runSingleBodyCollector (isRlibRoot true 3 5 postOptO3) preOpt postOptO3
    memItem (.fn_ 42) outDefaultO0.pmeCheckedItems = true ∧
    memItem (.fn_ 42) outDefaultO3.pmeCheckedItems = false ∧
    memItem (.fn_ 42) outPinnedO3.pmeCheckedItems = true ∧
    memItem (.fn_ 42) outPinnedO3.codegenItems = false := by
  decide

end Part2MentionedItems

/-! ============================================================================
    PART 3: `MultipleReturnTerminators` (`multiple_return_terminators.rs`)
    ============================================================================ -/

section Part3MultipleReturnTerminators

/-- Statement in the CFG bisimulation model (`nop`, `assignConst`, `copyLocal`). -/
inductive CfgStmt where
  | nop
  | assignConst (dst : Nat) (val : Nat)
  | copyLocal (dst src : Nat)

inductive CfgTerm where
  | goto (target : Nat)
  | branchZero (local_ : Nat) (zeroTarget nonZeroTarget : Nat)
  | ret
  | unreachable
  | unwindResume
  | unwindTerminate (reason : Nat)

def CfgTerm.isRet : CfgTerm → Bool
  | .ret => true
  | _ => false

def CfgTerm.normalSuccs : CfgTerm → List Nat
  | .goto t => [t]
  | .branchZero _ z nz => [z, nz]
  | _ => []

structure CfgBlock where
  stmts : List CfgStmt
  term : CfgTerm
  isCleanup : Bool

abbrev Cfg := List CfgBlock

/-- Exact `validate.rs:145-162` & `516-538` bipartite cleanup invariant. -/
def ValidCleanupCfg (cfg : Cfg) : Prop :=
  ∀ (bb : Nat) (b : CfgBlock),
    getOpt cfg bb = some b →
    (∀ t, t ∈ b.term.normalSuccs →
      ∃ tb, getOpt cfg t = some tb ∧ tb.isCleanup = b.isCleanup) ∧
    (b.term = .ret → b.isCleanup = false) ∧
    (b.term = .unwindResume → b.isCleanup = true) ∧
    (∀ r, b.term = .unwindTerminate r → b.isCleanup = true)

/-- Mirrors `multiple_return_terminators.rs:22`: empty statements + `Return` terminator. -/
def isSimpleReturn (b : CfgBlock) : Bool :=
  b.stmts.isEmpty && b.term.isRet

/-- Mirrors `multiple_return_terminators.rs:27-33`: replace `Goto { target }` with `Return`
whenever `target` is a simple-return block. -/
def mrtRewriteBlock (cfg : Cfg) (b : CfgBlock) : CfgBlock :=
  match b.term with
  | .goto target =>
    match getOpt cfg target with
    | some tb =>
      if isSimpleReturn tb then { b with term := .ret } else b
    | none => b
  | _ => b

def mrtRewrite (cfg : Cfg) : Cfg :=
  cfg.map (mrtRewriteBlock cfg)

theorem mrtRewriteBlock_isCleanup (cfg : Cfg) (b : CfgBlock) :
    (mrtRewriteBlock cfg b).isCleanup = b.isCleanup := by
  dsimp only [mrtRewriteBlock]
  cases ht : b.term with
  | goto target =>
    dsimp only
    cases getOpt cfg target with
    | none => rfl
    | some tb =>
      dsimp only
      cases isSimpleReturn tb <;> rfl
  | branchZero _ _ _ => rfl
  | ret => rfl
  | unreachable => rfl
  | unwindResume => rfl
  | unwindTerminate _ => rfl

/-- **Theorem 3.1 (`mrtRewrite_preserves_validCleanupCfg`)**:
Even though `multiple_return_terminators.rs:28-31` never explicitly checks `!bb.is_cleanup`,
any MIR body satisfying the Validator's bipartite cleanup invariant (`ValidCleanupCfg`) still
satisfies `ValidCleanupCfg` after `mrtRewrite` — in particular, no cleanup block ever gets a
`Return` terminator (preserving `Trusted.MirSemantics.evalTerminator`'s `!bb.cleanup` guard). -/
theorem mrtRewrite_preserves_validCleanupCfg {cfg : Cfg} (hval : ValidCleanupCfg cfg) :
    ValidCleanupCfg (mrtRewrite cfg) := by
  intro bb b' hb'
  unfold mrtRewrite at hb'
  rw [getOpt_map] at hb'
  cases hb : getOpt cfg bb with
  | none => rw [hb] at hb'; cases hb'
  | some b =>
    rw [hb] at hb'
    simp only [Option.map_some] at hb'
    injection hb' with heq
    subst heq
    let ⟨hsucc, hret, hres, hterm⟩ := hval bb b hb
    dsimp only [mrtRewriteBlock]
    cases ht : b.term with
    | goto target =>
      dsimp only
      cases htb : getOpt cfg target with
      | none =>
        dsimp only
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro t htmem
          rw [ht] at hsucc htmem
          let ⟨tb, htb', hcl⟩ := hsucc t htmem
          refine ⟨mrtRewriteBlock cfg tb, ?_, (mrtRewriteBlock_isCleanup cfg tb).trans hcl⟩
          unfold mrtRewrite; rw [getOpt_map, htb']; rfl
        · intro h; rw [ht] at h; cases h
        · intro h; rw [ht] at h; cases h
        · intro r h; rw [ht] at h; cases h
      | some tb =>
        dsimp only
        cases hsr : isSimpleReturn tb with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro t htmem
            rw [ht] at hsucc htmem
            let ⟨tb2, htb2, hcl⟩ := hsucc t htmem
            refine ⟨mrtRewriteBlock cfg tb2, ?_, (mrtRewriteBlock_isCleanup cfg tb2).trans hcl⟩
            unfold mrtRewrite; rw [getOpt_map, htb2]; rfl
          · intro h; rw [ht] at h; cases h
          · intro h; rw [ht] at h; cases h
          · intro r h; rw [ht] at h; cases h
        | true =>
          simp only [ite_true]
          have htbRet : tb.term = .ret := by
            unfold isSimpleReturn at hsr
            cases hst : tb.stmts <;> cases htr : tb.term <;> simp [hst, CfgTerm.isRet, htr] at hsr
            rfl
          have htbNotClean : tb.isCleanup = false := (hval target tb htb).2.1 htbRet
          rw [ht] at hsucc
          let ⟨tb2, htb2, hcl⟩ := hsucc target (List.Mem.head [])
          rw [htb] at htb2
          injection htb2 with htbEq
          subst htbEq
          have hbNotClean : b.isCleanup = false := hcl.symm.trans htbNotClean
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro t htmem; cases htmem
          · intro _; exact hbNotClean
          · intro h; cases h
          · intro r h; cases h
    | branchZero loc z nz =>
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t htmem
        rw [ht] at hsucc htmem
        let ⟨tb, htb', hcl⟩ := hsucc t htmem
        refine ⟨mrtRewriteBlock cfg tb, ?_, (mrtRewriteBlock_isCleanup cfg tb).trans hcl⟩
        unfold mrtRewrite; rw [getOpt_map, htb']; rfl
      · intro h; rw [ht] at h; cases h
      · intro h; rw [ht] at h; cases h
      · intro r h; rw [ht] at h; cases h
    | ret =>
      dsimp only
      refine ⟨fun _ h => (by rw [ht] at h; cases h), fun _ => hret ht,
              fun h => (by rw [ht] at h; cases h), fun _ h => (by rw [ht] at h; cases h)⟩
    | unreachable =>
      dsimp only
      refine ⟨fun _ h => (by rw [ht] at h; cases h), fun h => (by rw [ht] at h; cases h),
              fun h => (by rw [ht] at h; cases h), fun _ h => (by rw [ht] at h; cases h)⟩
    | unwindResume =>
      dsimp only
      refine ⟨fun _ h => (by rw [ht] at h; cases h), fun h => (by rw [ht] at h; cases h),
              fun _ => hres ht, fun _ h => (by rw [ht] at h; cases h)⟩
    | unwindTerminate r =>
      dsimp only
      refine ⟨fun _ h => (by rw [ht] at h; cases h), fun h => (by rw [ht] at h; cases h),
              fun h => (by rw [ht] at h; cases h),
              fun r' hr => (by rw [ht] at hr; injection hr with hrr; subst hrr; exact hterm r ht)⟩

/-- Small-step operational semantics for `Cfg` (modeling `Trusted.MirSemantics`). -/
abbrev LocalStore := List (Option Nat)

def execStmt (s : LocalStore) : CfgStmt → LocalStore
  | .nop => s
  | .assignConst d v => setAt s d (some v)
  | .copyLocal d src =>
    match getOpt s src with
    | some v => setAt s d v
    | none => s

def execStmts (s : LocalStore) (stmts : List CfgStmt) : LocalStore :=
  stmts.foldl execStmt s

theorem execStmts_nil (s : LocalStore) : execStmts s [] = s := rfl

inductive StepOut where
  | next (bb : Nat) (store : LocalStore)
  | returned (val : Nat)
  | faultUB
  | faultUnsupported

def stepBlock (cfg : Cfg) (bb : Nat) (store : LocalStore) : StepOut :=
  match getOpt cfg bb with
  | none => .faultUnsupported
  | some b =>
    let store' := execStmts store b.stmts
    match b.term with
    | .goto target => .next target store'
    | .branchZero loc z nz =>
      match getOpt store' loc with
      | some (some 0) => .next z store'
      | some (some (_ + 1)) => .next nz store'
      | some none => .faultUB
      | none => .faultUnsupported
    | .ret =>
      if b.isCleanup then .faultUnsupported
      else
        match getOpt store' 0 with
        | some (some v) => .returned v
        | some none => .faultUB
        | none => .faultUnsupported
    | .unreachable => .faultUB
    | .unwindResume | .unwindTerminate _ => .faultUnsupported

/-- Inductive big-step termination relation `EvalTo cfg bb store res` (zero fuel hacks). -/
inductive TerminalRes where
  | returned (val : Nat)
  | faultUB
  | faultUnsupported

inductive EvalTo (cfg : Cfg) : Nat → LocalStore → TerminalRes → Prop where
  | doneRet {bb s v} (h : stepBlock cfg bb s = .returned v) :
      EvalTo cfg bb s (.returned v)
  | doneUB {bb s} (h : stepBlock cfg bb s = .faultUB) :
      EvalTo cfg bb s .faultUB
  | doneUnsup {bb s} (h : stepBlock cfg bb s = .faultUnsupported) :
      EvalTo cfg bb s .faultUnsupported
  | step {bb s bb' s' res}
      (h : stepBlock cfg bb s = .next bb' s')
      (hrest : EvalTo cfg bb' s' res) :
      EvalTo cfg bb s res

/-- Core 1-step-vs-2-step simulation lemma for `mrtRewrite` under `ValidCleanupCfg`. -/
theorem stepBlock_mrtRewrite_dichotomy {cfg : Cfg} (hval : ValidCleanupCfg cfg)
    (bb : Nat) (s : LocalStore) :
    (stepBlock (mrtRewrite cfg) bb s = stepBlock cfg bb s) ∨
    (∃ target s',
      stepBlock cfg bb s = .next target s' ∧
      stepBlock (mrtRewrite cfg) bb s = stepBlock cfg target s' ∧
      ∀ bb'' s'', stepBlock cfg target s' ≠ .next bb'' s'') := by
  cases hb : getOpt cfg bb with
  | none =>
    left
    unfold stepBlock mrtRewrite
    rw [getOpt_map, hb]
    rfl
  | some b =>
    cases ht : b.term with
    | goto target =>
      cases htb : getOpt cfg target with
      | none =>
        left
        unfold stepBlock mrtRewrite
        rw [getOpt_map, hb]
        simp only [Option.map_some, mrtRewriteBlock, ht, htb]
      | some tb =>
        cases hsr : isSimpleReturn tb with
        | false =>
          left
          unfold stepBlock mrtRewrite
          rw [getOpt_map, hb]
          simp only [Option.map_some, mrtRewriteBlock, ht, htb, hsr, Bool.false_eq_true, ite_false]
        | true =>
          right
          have htbEmpty : tb.stmts = [] := by
            unfold isSimpleReturn at hsr
            cases hst : tb.stmts with
            | nil => rfl
            | cons _ _ => rw [hst] at hsr; cases hsr
          have htbRet : tb.term = .ret := by
            unfold isSimpleReturn at hsr
            rw [htbEmpty] at hsr
            cases htr : tb.term with
            | ret => rfl
            | goto _ => rw [htr] at hsr; cases hsr
            | branchZero _ _ _ => rw [htr] at hsr; cases hsr
            | unreachable => rw [htr] at hsr; cases hsr
            | unwindResume => rw [htr] at hsr; cases hsr
            | unwindTerminate _ => rw [htr] at hsr; cases hsr
          have htbClean : tb.isCleanup = false := (hval target tb htb).2.1 htbRet
          have hbClean : b.isCleanup = false := by
            have hsucc := (hval bb b hb).1
            rw [ht] at hsucc
            let ⟨tb2, htb2, hcl⟩ := hsucc target (List.Mem.head [])
            rw [htb] at htb2; injection htb2 with heq; subst heq
            exact hcl.symm.trans htbClean
          refine ⟨target, execStmts s b.stmts, ?_, ?_, ?_⟩
          · unfold stepBlock; rw [hb]; dsimp only; rw [ht]
          · unfold stepBlock mrtRewrite
            rw [getOpt_map, hb, htb]
            simp only [Option.map_some, mrtRewriteBlock, ht, htb, hsr, ite_true,
                       htbEmpty, htbRet, htbClean, hbClean, Bool.false_eq_true, ite_false, execStmts_nil]
          · intro bb'' s'' hnext
            unfold stepBlock at hnext
            rw [htb] at hnext; dsimp only at hnext
            rw [htbEmpty, htbRet, htbClean, execStmts_nil] at hnext
            simp only [Bool.false_eq_true, ite_false] at hnext
            cases hg : getOpt (execStmts s b.stmts) 0 with
            | none => rw [hg] at hnext; cases hnext
            | some o =>
              rw [hg] at hnext
              cases o <;> cases hnext
    | branchZero _ _ _ =>
      left; unfold stepBlock mrtRewrite; rw [getOpt_map, hb]; simp only [Option.map_some, mrtRewriteBlock, ht]
    | ret =>
      left; unfold stepBlock mrtRewrite; rw [getOpt_map, hb]; simp only [Option.map_some, mrtRewriteBlock, ht]
    | unreachable =>
      left; unfold stepBlock mrtRewrite; rw [getOpt_map, hb]; simp only [Option.map_some, mrtRewriteBlock, ht]
    | unwindResume =>
      left; unfold stepBlock mrtRewrite; rw [getOpt_map, hb]; simp only [Option.map_some, mrtRewriteBlock, ht]
    | unwindTerminate _ =>
      left; unfold stepBlock mrtRewrite; rw [getOpt_map, hb]; simp only [Option.map_some, mrtRewriteBlock, ht]

/-- **Theorem 3.2 (`mrtRewrite_forward_refinement`)**:
Every terminating or faulting execution of `cfg` produces the EXACT same `TerminalRes`
in `mrtRewrite cfg` (requires `ValidCleanupCfg cfg` so synthesized `Return` blocks have
matching `isCleanup = false`). -/
theorem mrtRewrite_forward_refinement {cfg : Cfg} (hval : ValidCleanupCfg cfg)
    {bb : Nat} {s : LocalStore} {res : TerminalRes}
    (heval : EvalTo cfg bb s res) :
    EvalTo (mrtRewrite cfg) bb s res := by
  induction heval with
  | @doneRet bb s v h =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.doneRet (heq.trans h)
    | inr h2 => let ⟨_, _, hnext, _, _⟩ := h2; rw [hnext] at h; cases h
  | @doneUB bb s h =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.doneUB (heq.trans h)
    | inr h2 => let ⟨_, _, hnext, _, _⟩ := h2; rw [hnext] at h; cases h
  | @doneUnsup bb s h =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.doneUnsup (heq.trans h)
    | inr h2 => let ⟨_, _, hnext, _, _⟩ := h2; rw [hnext] at h; cases h
  | @step bb s bb' s' res hstep hrest ih =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.step (heq.trans hstep) ih
    | inr h2 =>
      let ⟨target, s'', hnext, hshort, hnoNext⟩ := h2
      rw [hnext] at hstep
      injection hstep with htEq hsEq
      subst htEq; subst hsEq
      cases hrest with
      | doneRet hr => exact EvalTo.doneRet (hshort.trans hr)
      | doneUB hu => exact EvalTo.doneUB (hshort.trans hu)
      | doneUnsup hun => exact EvalTo.doneUnsup (hshort.trans hun)
      | step hbad _ => exact False.elim (hnoNext _ _ hbad)

/-- **Theorem 3.3 (`mrtRewrite_backward_refinement`)**:
Conversely, every execution of `mrtRewrite cfg` is simulated by `cfg` with the exact same
`TerminalRes` — completing full forward+backward semantic bisimulation! -/
theorem mrtRewrite_backward_refinement {cfg : Cfg} (hval : ValidCleanupCfg cfg)
    {bb : Nat} {s : LocalStore} {res : TerminalRes}
    (heval : EvalTo (mrtRewrite cfg) bb s res) :
    EvalTo cfg bb s res := by
  induction heval with
  | @doneRet bb s v h =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.doneRet (heq.symm.trans h)
    | inr h2 =>
      let ⟨target, s', hnext, hshort, _⟩ := h2
      exact EvalTo.step hnext (EvalTo.doneRet (hshort.symm.trans h))
  | @doneUB bb s h =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.doneUB (heq.symm.trans h)
    | inr h2 =>
      let ⟨target, s', hnext, hshort, _⟩ := h2
      exact EvalTo.step hnext (EvalTo.doneUB (hshort.symm.trans h))
  | @doneUnsup bb s h =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.doneUnsup (heq.symm.trans h)
    | inr h2 =>
      let ⟨target, s', hnext, hshort, _⟩ := h2
      exact EvalTo.step hnext (EvalTo.doneUnsup (hshort.symm.trans h))
  | @step bb s bb' s' res hstep hrest ih =>
    cases stepBlock_mrtRewrite_dichotomy hval bb s with
    | inl heq => exact EvalTo.step (heq.symm.trans hstep) ih
    | inr h2 =>
      let ⟨target, s'', _, hshort, hnoNext⟩ := h2
      exact False.elim (hnoNext bb' s' (hshort.symm.trans hstep))

/-- **Theorem 3.4 (`mrt_preserves_nonempty_return_epilogue`)**:
A shared return block with non-empty statements (e.g., `Drop` epilogue) is NEVER duplicated. -/
theorem mrt_preserves_nonempty_return_epilogue (cfg : Cfg) (b tb : CfgBlock)
    (target : Nat) (st : CfgStmt) (rest : List CfgStmt)
    (hgoto : b.term = .goto target)
    (htb : getOpt cfg target = some tb)
    (hnonempty : tb.stmts = st :: rest) :
    mrtRewriteBlock cfg b = b := by
  have hfalse : isSimpleReturn tb = false := by
    unfold isSimpleReturn; rw [hnonempty]; rfl
  dsimp only [mrtRewriteBlock]
  rw [hgoto]; dsimp only
  rw [htb]; dsimp only
  rw [hfalse]
  rfl

/-- **Theorem 3.5 (`removeDeadBlocks_lockstep_bisimulation`)**:
Compacting dead blocks (`simplify::remove_dead_blocks`, `multiple_return_terminators.rs:35`)
via any reachability-preserving remapping `remap : Nat → Option Nat` preserves `EvalTo`
step-for-step! -/
def remapTerm (remap : Nat → Nat) : CfgTerm → CfgTerm
  | .goto t => .goto (remap t)
  | .branchZero l z nz => .branchZero l (remap z) (remap nz)
  | t => t

def IsValidCompaction (cfg compact : Cfg) (reach : Nat → Prop) (remap : Nat → Nat) : Prop :=
  ∀ bb, reach bb →
    (∃ b, getOpt cfg bb = some b) ∧
    ∀ b, getOpt cfg bb = some b →
      getOpt compact (remap bb) = some { b with term := remapTerm remap b.term } ∧
      ∀ t, t ∈ b.term.normalSuccs → reach t

theorem removeDeadBlocks_preserves_eval {cfg compact : Cfg} {reach : Nat → Prop} {remap : Nat → Nat}
    (hcomp : IsValidCompaction cfg compact reach remap)
    {bb : Nat} {s : LocalStore} {res : TerminalRes}
    (hreach : reach bb) (heval : EvalTo cfg bb s res) :
    EvalTo compact (remap bb) s res := by
  induction heval with
  | @doneRet bb s v h =>
    apply EvalTo.doneRet
    unfold stepBlock at h ⊢
    cases hb : getOpt cfg bb with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h; dsimp only at h
      let ⟨hcb, _⟩ := (hcomp bb hreach).2 b hb
      rw [hcb]; dsimp only
      cases ht : b.term with
      | goto _ => rw [ht] at h; cases h
      | branchZero loc _ _ =>
        rw [ht] at h; dsimp only at h
        cases hg : getOpt (execStmts s b.stmts) loc with
        | none => rw [hg] at h; cases h
        | some o =>
          rw [hg] at h
          cases o with
          | none => cases h
          | some n => cases n <;> cases h
      | ret => rw [ht] at h; dsimp only [remapTerm]; exact h
      | unreachable => rw [ht] at h; cases h
      | unwindResume => rw [ht] at h; cases h
      | unwindTerminate _ => rw [ht] at h; cases h
  | @doneUB bb s h =>
    apply EvalTo.doneUB
    unfold stepBlock at h ⊢
    cases hb : getOpt cfg bb with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h; dsimp only at h
      let ⟨hcb, _⟩ := (hcomp bb hreach).2 b hb
      rw [hcb]; dsimp only
      cases ht : b.term with
      | goto _ => rw [ht] at h; cases h
      | branchZero loc _ _ =>
        rw [ht] at h; dsimp only [remapTerm] at h ⊢
        cases hg : getOpt (execStmts s b.stmts) loc with
        | none => rw [hg] at h; cases h
        | some o =>
          rw [hg] at h
          cases o with
          | none => rfl
          | some n => cases n <;> cases h
      | ret => rw [ht] at h; dsimp only [remapTerm]; exact h
      | unreachable => rfl
      | unwindResume => rw [ht] at h; cases h
      | unwindTerminate _ => rw [ht] at h; cases h
  | @doneUnsup bb s h =>
    unfold stepBlock at h
    cases hb : getOpt cfg bb with
    | none =>
      let ⟨b, hb'⟩ := (hcomp bb hreach).1
      rw [hb] at hb'; cases hb'
    | some b =>
      rw [hb] at h; dsimp only at h
      let ⟨hcb, _⟩ := (hcomp bb hreach).2 b hb
      apply EvalTo.doneUnsup
      unfold stepBlock; rw [hcb]; dsimp only
      cases ht : b.term with
      | goto _ => rw [ht] at h; cases h
      | branchZero loc _ _ =>
        rw [ht] at h; dsimp only [remapTerm] at h ⊢
        cases hg : getOpt (execStmts s b.stmts) loc with
        | none => rfl
        | some o =>
          rw [hg] at h
          cases o with
          | none => cases h
          | some n => cases n <;> cases h
      | ret => rw [ht] at h; dsimp only [remapTerm]; exact h
      | unreachable => rw [ht] at h; cases h
      | unwindResume => rfl
      | unwindTerminate _ => rfl
  | @step bb s bb' s' res hstep hrest ih =>
    unfold stepBlock at hstep
    cases hb : getOpt cfg bb with
    | none => rw [hb] at hstep; cases hstep
    | some b =>
      rw [hb] at hstep; dsimp only at hstep
      let ⟨hcb, hsuccReach⟩ := (hcomp bb hreach).2 b hb
      cases ht : b.term with
      | goto target =>
        rw [ht] at hstep
        injection hstep with hbb' hs'; subst hbb'; subst hs'
        have hr' : reach target := hsuccReach target (by rw [ht]; exact List.Mem.head [])
        have hs2 : stepBlock compact (remap bb) s = .next (remap target) (execStmts s b.stmts) := by
          unfold stepBlock; rw [hcb]; dsimp only; rw [ht]; rfl
        exact EvalTo.step hs2 (ih hr')
      | branchZero loc z nz =>
        rw [ht] at hstep; dsimp only at hstep
        cases hg : getOpt (execStmts s b.stmts) loc with
        | none => rw [hg] at hstep; cases hstep
        | some o =>
          rw [hg] at hstep
          cases o with
          | none => cases hstep
          | some val =>
            cases val with
            | zero =>
              injection hstep with hbb' hs'; subst hbb'; subst hs'
              have hr' : reach z := hsuccReach z (by rw [ht]; exact List.Mem.head _)
              have hs2 : stepBlock compact (remap bb) s = .next (remap z) (execStmts s b.stmts) := by
                unfold stepBlock; rw [hcb]; dsimp only; rw [ht]; dsimp only [remapTerm]; rw [hg]
              exact EvalTo.step hs2 (ih hr')
            | succ _ =>
              injection hstep with hbb' hs'; subst hbb'; subst hs'
              have hr' : reach nz := hsuccReach nz (by rw [ht]; exact List.Mem.tail _ (List.Mem.head _))
              have hs2 : stepBlock compact (remap bb) s = .next (remap nz) (execStmts s b.stmts) := by
                unfold stepBlock; rw [hcb]; dsimp only; rw [ht]; dsimp only [remapTerm]; rw [hg]
              exact EvalTo.step hs2 (ih hr')
      | ret =>
        rw [ht] at hstep; dsimp only at hstep
        cases hc : b.isCleanup with
        | true => rw [hc] at hstep; cases hstep
        | false =>
          rw [hc] at hstep
          cases hg : getOpt (execStmts s b.stmts) 0 with
          | none => rw [hg] at hstep; cases hstep
          | some o => rw [hg] at hstep; cases o <;> cases hstep
      | unreachable => rw [ht] at hstep; cases hstep
      | unwindResume => rw [ht] at hstep; cases hstep
      | unwindTerminate _ => rw [ht] at hstep; cases hstep

end Part3MultipleReturnTerminators

/-! ============================================================================
    PART 4: `MirPatch` (`compiler/rustc_mir_transform/src/patch.rs`)
    ============================================================================ -/

section Part4MirPatch

/-- Statement entry `(statement_index, stmt)` for a single basic block. -/
abbrev BlockIns := Nat × CfgStmt

/-- Non-decreasing `statement_index` order matching `new_statements.sort_by_key(|s| s.0)`
(`patch.rs:290`). -/
inductive SortedIns : List BlockIns → Prop where
  | nil : SortedIns []
  | single (p : BlockIns) : SortedIns [p]
  | cons {i j : Nat} {si sj : CfgStmt} {rest : List BlockIns}
      (hle : i ≤ j) (htail : SortedIns ((j, sj) :: rest)) :
      SortedIns ((i, si) :: (j, sj) :: rest)

inductive AllLe (bound : Nat) : List BlockIns → Prop where
  | nil : AllLe bound []
  | cons {i : Nat} {s : CfgStmt} {rest : List BlockIns}
      (hle : i ≤ bound) (hrest : AllLe bound rest) : AllLe bound ((i, s) :: rest)

/-- Classic `delta`-shifted `Vec::insert` loop (`patch.rs:282-295` at `14210df0e` / `3ef0c22cd`)
via `List.foldl` (zero `_unsafe_rec` helpers). -/
def applyDeltaLoop (delta : Nat) (stmts : List CfgStmt) (ins : List BlockIns) : List CfgStmt :=
  (ins.foldl (fun (acc : Nat × List CfgStmt) (p : BlockIns) =>
    (acc.1 + 1, insertAt acc.2 (p.1 + acc.1) p.2)) (delta, stmts)).2

theorem applyDeltaLoop_nil (delta : Nat) (stmts : List CfgStmt) :
    applyDeltaLoop delta stmts [] = stmts := rfl

theorem applyDeltaLoop_cons (delta : Nat) (stmts : List CfgStmt) (idx : Nat) (s : CfgStmt)
    (rest : List BlockIns) :
    applyDeltaLoop delta stmts ((idx, s) :: rest) =
    applyDeltaLoop (delta + 1) (insertAt stmts (idx + delta) s) rest := rfl

def applyDeltaInsertions (stmts : List CfgStmt) (ins : List BlockIns) : List CfgStmt :=
  applyDeltaLoop 0 stmts ins

/-- Linear $O(n+m)$ `merge` algorithm (`patch.rs:304-315, 343-366` at `137d1d494`)
via `List.foldr` and `@Nat.recCompiled` (zero `_unsafe_rec` helpers). -/
def addIdxOffsets (offset : Nat) (ins : List BlockIns) : List BlockIns :=
  ins.foldr (fun p ih o => (p.1 + o, p.2) :: ih (o + 1)) (fun _ => []) offset

theorem addIdxOffsets_nil (offset : Nat) : addIdxOffsets offset [] = [] := rfl

theorem addIdxOffsets_cons (offset idx : Nat) (s : CfgStmt) (rest : List BlockIns) :
    addIdxOffsets offset ((idx, s) :: rest) = (idx + offset, s) :: addIdxOffsets (offset + 1) rest := rfl

def mergeFuel (fuel : Nat) : Nat → List CfgStmt → List BlockIns → List CfgStmt :=
  @Nat.recCompiled (fun _ => Nat → List CfgStmt → List BlockIns → List CfgStmt)
    (fun _ xs ys => xs ++ ys.map Prod.snd)
    (fun _ ih zi xs ys =>
      match xs, ys with
      | [], ys => ys.map Prod.snd
      | xs, [] => xs
      | x :: xs', (yi, s) :: ys' =>
        if yi == zi then
          s :: ih (zi + 1) (x :: xs') ys'
        else
          x :: ih (zi + 1) xs' ((yi, s) :: ys'))
    fuel

def mergeStmts (zi : Nat) (xs : List CfgStmt) (ys : List BlockIns) : List CfgStmt :=
  mergeFuel (xs.length + ys.length) zi xs ys

def applyMergeInsertions (stmts : List CfgStmt) (ins : List BlockIns) : List CfgStmt :=
  mergeStmts 0 stmts (addIdxOffsets 0 ins)

theorem applyDeltaLoop_length (delta : Nat) (stmts : List CfgStmt) (ins : List BlockIns) :
    (applyDeltaLoop delta stmts ins).length = stmts.length + ins.length := by
  induction ins generalizing delta stmts with
  | nil => simp [applyDeltaLoop_nil]
  | cons p rest ih =>
    cases p with
    | mk idx s =>
      rw [applyDeltaLoop_cons, ih, insertAt_length, List.length_cons, Nat.add_right_comm, Nat.add_assoc]

theorem mergeFuel_zero (zi : Nat) (xs : List CfgStmt) (ys : List BlockIns) :
    mergeFuel 0 zi xs ys = xs ++ ys.map Prod.snd := rfl

theorem mergeFuel_succ_nil_left (k zi : Nat) (ys : List BlockIns) :
    mergeFuel (k + 1) zi [] ys = ys.map Prod.snd := rfl

theorem mergeFuel_succ_nil_right (k zi : Nat) (x : CfgStmt) (xs : List CfgStmt) :
    mergeFuel (k + 1) zi (x :: xs) [] = x :: xs := rfl

theorem mergeFuel_succ_cons (k zi : Nat) (x : CfgStmt) (xs : List CfgStmt)
    (yi : Nat) (s : CfgStmt) (ys : List BlockIns) :
    mergeFuel (k + 1) zi (x :: xs) ((yi, s) :: ys) =
    if yi == zi then s :: mergeFuel k (zi + 1) (x :: xs) ys
    else x :: mergeFuel k (zi + 1) xs ((yi, s) :: ys) := rfl

theorem mergeFuel_length (fuel : Nat) :
    ∀ (zi : Nat) (xs : List CfgStmt) (ys : List BlockIns),
      (mergeFuel fuel zi xs ys).length = xs.length + ys.length := by
  induction fuel with
  | zero =>
    intro zi xs ys
    rw [mergeFuel_zero, List.length_append, List.length_map]
  | succ k ih =>
    intro zi xs ys
    cases xs with
    | nil => rw [mergeFuel_succ_nil_left, List.length_map, List.length_nil, Nat.zero_add]
    | cons x xs' =>
      cases ys with
      | nil => rw [mergeFuel_succ_nil_right, List.length_nil, Nat.add_zero]
      | cons p ys' =>
        cases p with
        | mk yi s =>
          rw [mergeFuel_succ_cons]
          cases hcmp : (yi == zi) with
          | true =>
            simp only [ite_true, List.length_cons]
            rw [ih (zi + 1) (x :: xs') ys', List.length_cons, Nat.add_assoc]
          | false =>
            simp only [Bool.false_eq_true, ite_false, List.length_cons]
            rw [ih (zi + 1) xs' ((yi, s) :: ys'), List.length_cons, Nat.add_right_comm]

theorem mergeStmts_length (zi : Nat) (xs : List CfgStmt) (ys : List BlockIns) :
    (mergeStmts zi xs ys).length = xs.length + ys.length :=
  mergeFuel_length (xs.length + ys.length) zi xs ys

theorem addIdxOffsets_length (off : Nat) (ins : List BlockIns) :
    (addIdxOffsets off ins).length = ins.length := by
  induction ins generalizing off with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | mk idx s =>
      rw [addIdxOffsets_cons, List.length_cons, List.length_cons, ih]

theorem applyDeltaInsertions_length (stmts : List CfgStmt) (ins : List BlockIns) :
    (applyDeltaInsertions stmts ins).length = stmts.length + ins.length :=
  applyDeltaLoop_length 0 stmts ins

theorem applyMergeInsertions_length (stmts : List CfgStmt) (ins : List BlockIns) :
    (applyMergeInsertions stmts ins).length = stmts.length + ins.length := by
  unfold applyMergeInsertions
  rw [mergeStmts_length, addIdxOffsets_length]

/-- Helper: `insertAt` at `pos ≥ xs.length` appends `v` at the end. -/
theorem insertAt_of_ge {xs : List α} {pos : Nat} (h : xs.length ≤ pos) (v : α) :
    insertAt xs pos v = xs ++ [v] := by
  induction xs generalizing pos with
  | nil =>
    cases pos <;> rfl
  | cons x xs ih =>
    cases pos with
    | zero => exact False.elim (nat_not_lt_zero xs.length (Nat.lt_of_succ_le h))
    | succ k =>
      simp only [insertAt_cons_succ, List.cons_append]
      exact congrArg (List.cons x) (ih (Nat.le_of_succ_le_succ h))

/-- Helper: `insertAt (pfx ++ xs) pfx.length v = (pfx ++ [v]) ++ xs`. -/
theorem insertAt_append_exact (pfx xs : List α) (v : α) :
    insertAt (pfx ++ xs) pfx.length v = (pfx ++ [v]) ++ xs := by
  induction pfx with
  | nil => simp only [List.nil_append, List.length_nil, insertAt_zero, List.cons_append]
  | cons p ps ih =>
    simp only [List.cons_append, List.length_cons, insertAt_cons_succ]
    exact congrArg (List.cons p) ih

/-- Sequential insertion using pre-shifted target positions `(pos, s)` via `List.foldl`. -/
def applyTargets (stmts : List CfgStmt) (ys : List BlockIns) : List CfgStmt :=
  ys.foldl (fun acc p => insertAt acc p.1 p.2) stmts

theorem applyTargets_nil (stmts : List CfgStmt) : applyTargets stmts [] = stmts := rfl

theorem applyTargets_cons (stmts : List CfgStmt) (pos : Nat) (s : CfgStmt) (rest : List BlockIns) :
    applyTargets stmts ((pos, s) :: rest) = applyTargets (insertAt stmts pos s) rest := rfl

theorem applyDeltaLoop_eq_applyTargets (delta : Nat) (stmts : List CfgStmt)
    (ins : List BlockIns) :
    applyDeltaLoop delta stmts ins = applyTargets stmts (addIdxOffsets delta ins) := by
  induction ins generalizing delta stmts with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | mk idx s =>
      rw [applyDeltaLoop_cons, addIdxOffsets_cons, applyTargets_cons]
      exact ih (delta + 1) (insertAt stmts (idx + delta) s)

/-- Strict monotonicity of pre-shifted target indices starting at `lo`. -/
inductive StrictlySortedFrom : Nat → List BlockIns → Prop where
  | nil (lo : Nat) : StrictlySortedFrom lo []
  | cons {lo yi : Nat} {s : CfgStmt} {rest : List BlockIns}
      (hge : lo ≤ yi) (htail : StrictlySortedFrom (yi + 1) rest) :
      StrictlySortedFrom lo ((yi, s) :: rest)

theorem addIdxOffsets_strictlySorted {ins : List BlockIns} (hsort : SortedIns ins)
    (off : Nat) (lo : Nat) (hlo : ∀ p, ins.head? = some p → lo ≤ p.1 + off) :
    StrictlySortedFrom lo (addIdxOffsets off ins) := by
  induction hsort generalizing off lo with
  | nil => exact StrictlySortedFrom.nil lo
  | single p =>
    cases p with
    | mk i s =>
      rw [addIdxOffsets_cons, addIdxOffsets_nil]
      apply StrictlySortedFrom.cons (hlo (i, s) rfl)
      exact StrictlySortedFrom.nil _
  | @cons i j si sj rest hle htail ih =>
    rw [addIdxOffsets_cons]
    apply StrictlySortedFrom.cons (hlo (i, si) rfl)
    apply ih (off + 1) (i + off + 1)
    intro p hp
    simp only [List.head?_cons] at hp
    injection hp with hpeq
    subst hpeq
    rw [nat_add_succ_eq]
    exact Nat.succ_le_succ (Nat.add_le_add_right hle off)

theorem applyTargets_eq_mergeFuel (fuel : Nat) :
    ∀ (pfx xs : List CfgStmt) (ys : List BlockIns),
      xs.length + ys.length ≤ fuel →
      StrictlySortedFrom pfx.length ys →
      applyTargets (pfx ++ xs) ys = pfx ++ mergeFuel fuel pfx.length xs ys := by
  induction fuel with
  | zero =>
    intro pfx xs ys hlen _
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => exact False.elim (nat_not_lt_zero _ (Nat.lt_of_succ_le hlen))
    | cons _ _ =>
      simp only [List.length_cons, Nat.succ_add] at hlen
      exact False.elim (nat_not_lt_zero _ (Nat.lt_of_succ_le hlen))
  | succ k ih =>
    intro pfx xs ys hlen hss
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons p rest =>
        cases p with
        | mk yi s =>
          cases hss with
          | cons hge htail =>
            simp only [List.append_nil, applyTargets_cons]
            dsimp only [mergeFuel]
            rw [insertAt_of_ge hge s]
            have hlen1 : (pfx ++ [s]).length = pfx.length + 1 := by simp
            have hss' : StrictlySortedFrom (pfx ++ [s]).length rest := by
              rw [hlen1]
              cases htail with
              | nil _ => exact StrictlySortedFrom.nil _
              | cons hge2 htail2 =>
                exact StrictlySortedFrom.cons (Nat.le_trans (Nat.succ_le_succ hge) hge2) htail2
            have hbound : ([] : List CfgStmt).length + rest.length ≤ k := by
              simp only [List.length_nil, List.length_cons, Nat.zero_add] at hlen ⊢
              exact Nat.le_of_succ_le_succ hlen
            have hrec := ih (pfx ++ [s]) [] rest hbound hss'
            simp only [List.append_nil] at hrec
            have hmergeNil : ∀ (f : Nat) (z : Nat) (rs : List BlockIns),
                mergeFuel f z [] rs = rs.map Prod.snd := by
              intro f; cases f <;> intro z rs <;> rfl
            rw [hmergeNil] at hrec
            rw [hrec, List.append_assoc]
            rfl
    | cons x xs' =>
      cases ys with
      | nil =>
        rw [applyTargets_nil]
        rfl
      | cons p rest =>
        cases p with
        | mk yi s =>
          cases hss with
          | cons hge htail =>
            rw [mergeFuel_succ_cons]
            cases hcmp : (yi == pfx.length) with
            | true =>
              have heq : yi = pfx.length := beq_iff_eq.mp hcmp
              subst heq
              simp only [ite_true]
              rw [applyTargets_cons, insertAt_append_exact pfx (x :: xs') s]
              have hlen1 : (pfx ++ [s]).length = pfx.length + 1 := by simp
              have hss' : StrictlySortedFrom (pfx ++ [s]).length rest := hlen1 ▸ htail
              have hbound : (x :: xs').length + rest.length ≤ k := by
                simp only [List.length_cons] at hlen ⊢
                rw [nat_add_succ_eq] at hlen
                exact Nat.le_of_succ_le_succ hlen
              have hrec := ih (pfx ++ [s]) (x :: xs') rest hbound hss'
              rw [hlen1] at hrec
              rw [hrec, List.append_assoc]
              rfl
            | false =>
              have hne : yi ≠ pfx.length := fun heq => by
                have ht : (yi == pfx.length) = true := beq_iff_eq.mpr heq
                rw [ht] at hcmp; cases hcmp
              have hlt : pfx.length < yi :=
                match nat_cases_lt_or_eq_of_le hge with
                | Or.inl hl => hl
                | Or.inr he => False.elim (hne he.symm)
              have hge1 : (pfx ++ [x]).length ≤ yi := by
                simp only [List.length_append, List.length_singleton]
                exact hlt
              simp only [Bool.false_eq_true, ite_false]
              have happ : pfx ++ (x :: xs') = (pfx ++ [x]) ++ xs' := by
                rw [List.append_assoc]; rfl
              rw [happ]
              have hss' : StrictlySortedFrom (pfx ++ [x]).length ((yi, s) :: rest) :=
                StrictlySortedFrom.cons hge1 htail
              have hbound : xs'.length + ((yi, s) :: rest).length ≤ k := by
                simp only [List.length_cons, Nat.succ_add] at hlen ⊢
                exact Nat.le_of_succ_le_succ hlen
              have hrec := ih (pfx ++ [x]) xs' ((yi, s) :: rest) hbound hss'
              have hlen1 : (pfx ++ [x]).length = pfx.length + 1 := by simp
              rw [hlen1] at hrec
              rw [hrec, List.append_assoc]
              rfl

/-- **Theorem 4.1 (`delta_eq_merge_for_all_sorted_insertions`)**:
Exact observational equivalence between `MirPatch::apply`'s `delta`-shifted `Vec::insert` loop
(`14210df0e` / `3ef0c22cd`) and its linear $O(n+m)$ `merge` algorithm (`137d1d494`, `patch.rs:304-366`)
for EVERY initial statement list `stmts` and EVERY non-decreasingly sorted insertion queue `ins`! -/
theorem delta_eq_merge_for_all_sorted_insertions (stmts : List CfgStmt) (ins : List BlockIns)
    (hsort : SortedIns ins) :
    applyDeltaInsertions stmts ins = applyMergeInsertions stmts ins := by
  unfold applyDeltaInsertions applyMergeInsertions mergeStmts
  rw [applyDeltaLoop_eq_applyTargets]
  have hss : StrictlySortedFrom ([] : List CfgStmt).length (addIdxOffsets 0 ins) :=
    addIdxOffsets_strictlySorted hsort 0 0 (fun _ _ => Nat.zero_le _)
  exact applyTargets_eq_mergeFuel (stmts.length + (addIdxOffsets 0 ins).length)
    [] stmts (addIdxOffsets 0 ins) (nat_le_refl _) hss

/-- **Theorem 4.2 (`same_loc_queue_order_preserved`)**:
Mirrors the docstring example in `patch.rs:243-249`: queueing `s1` then `s2` at the same
location `loc` places `s1, s2` immediately before `old[loc]` in FIFO queue order! -/
theorem same_loc_queue_order_preserved (s0 s1 s2 : CfgStmt) :
    applyDeltaInsertions [s0] [(0, s1), (0, s2)] = [s1, s2, s0] ∧
    applyMergeInsertions [s0] [(0, s1), (0, s2)] = [s1, s2, s0] :=
  ⟨rfl, rfl⟩

/-- **Theorem 4.3 (`in_bounds_delta_all`)**:
If every `(idx, _)` in `ins` satisfies `idx ≤ stmts.length`, then at every step of
`applyDeltaLoop`, the shifted index `idx + delta` is `≤` the current vector length
(proving Rust's `Vec::insert(loc.statement_index + delta, ...)` never panics out-of-bounds). -/
inductive DeltaStepsInBounds : Nat → Nat → List BlockIns → Prop where
  | nil (delta curLen : Nat) : DeltaStepsInBounds delta curLen []
  | cons {delta curLen idx : Nat} {s : CfgStmt} {rest : List BlockIns}
      (hle : idx + delta ≤ curLen)
      (hrest : DeltaStepsInBounds (delta + 1) (curLen + 1) rest) :
      DeltaStepsInBounds delta curLen ((idx, s) :: rest)

theorem in_bounds_delta_all (baseLen delta : Nat) (ins : List BlockIns)
    (hall : AllLe baseLen ins) :
    DeltaStepsInBounds delta (baseLen + delta) ins := by
  induction hall generalizing delta with
  | nil => exact DeltaStepsInBounds.nil delta (baseLen + delta)
  | cons hle _ ih =>
    apply DeltaStepsInBounds.cons (Nat.add_le_add_right hle delta)
    have h := ih (delta + 1)
    rw [nat_add_succ_eq] at h
    exact h

/-- Full 4-stage `MirPatch` model (`patch.rs:12-33, 261-328`). -/
structure MirLoc where
  block : Nat
  stmtIdx : Nat

structure MirPatch where
  termPatches : List (Nat × CfgTerm)
  nopLocs : List MirLoc
  newBlocks : List CfgBlock
  newStmts : List (Nat × List BlockIns) -- already grouped & stably sorted per block

def MirPatch.preservesCfg (p : MirPatch) : Bool :=
  p.termPatches.isEmpty && p.newBlocks.isEmpty

/-- Stage 1: replace statements at `nopLocs` with `.nop` without changing vector length. -/
def applyOneNop (cfg : Cfg) (loc : MirLoc) : Cfg :=
  match getOpt cfg loc.block with
  | none => cfg
  | some b => setAt cfg loc.block { b with stmts := setAt b.stmts loc.stmtIdx .nop }

def applyNops (cfg : Cfg) (locs : List MirLoc) : Cfg :=
  locs.foldl applyOneNop cfg

theorem applyNops_cons (cfg : Cfg) (l : MirLoc) (ls : List MirLoc) :
    applyNops cfg (l :: ls) = applyNops (applyOneNop cfg l) ls := rfl

theorem applyOneNop_length (cfg : Cfg) (loc : MirLoc) :
    (applyOneNop cfg loc).length = cfg.length := by
  unfold applyOneNop
  cases getOpt cfg loc.block with
  | none => rfl
  | some b => exact setAt_length cfg loc.block _

theorem applyOneNop_preserves_term_and_cleanup (cfg : Cfg) (loc : MirLoc) (bb : Nat) :
    (getOpt (applyOneNop cfg loc) bb).map (fun b => (b.term, b.isCleanup, b.stmts.length)) =
    (getOpt cfg bb).map (fun b => (b.term, b.isCleanup, b.stmts.length)) := by
  unfold applyOneNop
  cases hb : getOpt cfg loc.block with
  | none => rfl
  | some b =>
    by_cases heq : loc.block = bb
    · subst heq
      rw [getOpt_setAt_same (getOpt_some_lt hb), hb]
      simp [setAt_length]
    · rw [getOpt_setAt_ne heq]

theorem applyNops_preserves_term_and_cleanup (cfg : Cfg) (locs : List MirLoc) (bb : Nat) :
    (getOpt (applyNops cfg locs) bb).map (fun b => (b.term, b.isCleanup, b.stmts.length)) =
    (getOpt cfg bb).map (fun b => (b.term, b.isCleanup, b.stmts.length)) := by
  induction locs generalizing cfg with
  | nil => rfl
  | cons l ls ih =>
    rw [applyNops_cons, ih, applyOneNop_preserves_term_and_cleanup]

/-- Stage 2: insert per-block stably sorted statements using `applyMergeInsertions`. -/
def applyBlockStmtPatch (cfg : Cfg) (entry : Nat × List BlockIns) : Cfg :=
  match getOpt cfg entry.1 with
  | none => cfg
  | some b => setAt cfg entry.1 { b with stmts := applyMergeInsertions b.stmts entry.2 }

def applyNewStmts (cfg : Cfg) (entries : List (Nat × List BlockIns)) : Cfg :=
  entries.foldl applyBlockStmtPatch cfg

theorem applyNewStmts_cons (cfg : Cfg) (e : Nat × List BlockIns) (es : List (Nat × List BlockIns)) :
    applyNewStmts cfg (e :: es) = applyNewStmts (applyBlockStmtPatch cfg e) es := rfl

theorem applyBlockStmtPatch_length (cfg : Cfg) (e : Nat × List BlockIns) :
    (applyBlockStmtPatch cfg e).length = cfg.length := by
  unfold applyBlockStmtPatch
  cases getOpt cfg e.1 with
  | none => rfl
  | some _ => exact setAt_length cfg e.1 _

theorem applyBlockStmtPatch_preserves_term_and_cleanup (cfg : Cfg)
    (e : Nat × List BlockIns) (bb : Nat) :
    (getOpt (applyBlockStmtPatch cfg e) bb).map (fun b => (b.term, b.isCleanup)) =
    (getOpt cfg bb).map (fun b => (b.term, b.isCleanup)) := by
  unfold applyBlockStmtPatch
  cases hb : getOpt cfg e.1 with
  | none => rfl
  | some b =>
    by_cases heq : e.1 = bb
    · subst heq
      rw [getOpt_setAt_same (getOpt_some_lt hb), hb]
      rfl
    · rw [getOpt_setAt_ne heq]

theorem applyNewStmts_preserves_term_and_cleanup (cfg : Cfg)
    (entries : List (Nat × List BlockIns)) (bb : Nat) :
    (getOpt (applyNewStmts cfg entries) bb).map (fun b => (b.term, b.isCleanup)) =
    (getOpt cfg bb).map (fun b => (b.term, b.isCleanup)) := by
  induction entries generalizing cfg with
  | nil => rfl
  | cons e es ih =>
    rw [applyNewStmts_cons, ih, applyBlockStmtPatch_preserves_term_and_cleanup]

theorem applyNewStmts_length (cfg : Cfg) (entries : List (Nat × List BlockIns)) :
    (applyNewStmts cfg entries).length = cfg.length := by
  induction entries generalizing cfg with
  | nil => rfl
  | cons e es ih =>
    rw [applyNewStmts_cons, ih, applyBlockStmtPatch_length]

/-- Stage 3: patch terminators, clearing `bb.statements` on `TerminatorKind::Unreachable`
(`patch.rs:320-327`). -/
def applyOneTermPatch (cfg : Cfg) (entry : Nat × CfgTerm) : Cfg :=
  match getOpt cfg entry.1 with
  | none => cfg
  | some b =>
    let newStmts := match entry.2 with | .unreachable => [] | _ => b.stmts
    setAt cfg entry.1 { b with stmts := newStmts, term := entry.2 }

def applyTermPatches (cfg : Cfg) (entries : List (Nat × CfgTerm)) : Cfg :=
  entries.foldl applyOneTermPatch cfg

theorem applyTermPatches_nil (cfg : Cfg) : applyTermPatches cfg [] = cfg := rfl

theorem applyTermPatches_cons (cfg : Cfg) (e : Nat × CfgTerm) (es : List (Nat × CfgTerm)) :
    applyTermPatches cfg (e :: es) = applyTermPatches (applyOneTermPatch cfg e) es := rfl

/-- Full 4-stage `MirPatch::apply` (`patch.rs:261-328`):
Stage 0 (`extend(newBlocks)`), Stage 1 (`nopLocs`), Stage 2 (`newStmts`), Stage 3 (`termPatches`). -/
def MirPatch.apply (p : MirPatch) (cfg : Cfg) : Cfg :=
  let s0 := cfg ++ p.newBlocks
  let s1 := applyNops s0 p.nopLocs
  let s2 := applyNewStmts s1 p.newStmts
  applyTermPatches s2 p.termPatches

/-- **Theorem 4.4 (`preservesCfg_soundness`)**:
Whenever `p.preservesCfg = true` (`termPatches.isEmpty && newBlocks.isEmpty`),
`p.apply cfg` preserves BOTH the basic-block count AND every block's `(term, isCleanup)`,
justifying `body.basic_blocks.as_mut_preserves_cfg()` at `patch.rs:274-278` (`basic_blocks.rs:102-116`)! -/
theorem preservesCfg_soundness (p : MirPatch) (cfg : Cfg) (h : p.preservesCfg = true) :
    (p.apply cfg).length = cfg.length ∧
    ∀ bb, (getOpt (p.apply cfg) bb).map (fun b => (b.term, b.isCleanup)) =
          (getOpt cfg bb).map (fun b => (b.term, b.isCleanup)) := by
  unfold MirPatch.preservesCfg at h
  cases ht : p.termPatches with
  | cons _ _ => rw [ht] at h; cases h
  | nil =>
    cases hnb : p.newBlocks with
    | cons _ _ => rw [ht, hnb] at h; cases h
    | nil =>
      unfold MirPatch.apply
      rw [ht, hnb, List.append_nil, applyTermPatches_nil]
      constructor
      · rw [applyNewStmts_length]
        clear h ht hnb
        induction p.nopLocs generalizing cfg with
        | nil => rfl
        | cons l ls ih =>
          rw [applyNops_cons, ih, applyOneNop_length]
      · intro bb
        rw [applyNewStmts_preserves_term_and_cleanup]
        have hnop := applyNops_preserves_term_and_cleanup cfg p.nopLocs bb
        cases hg1 : getOpt (applyNops cfg p.nopLocs) bb <;>
          cases hg2 : getOpt cfg bb <;>
          simp [hg1, hg2] at hnop ⊢
        exact ⟨hnop.1, hnop.2.1⟩

/-- Distinct keys invariant enforced by `patch_terminator`'s `assert!(!contains_key(&block))`
(`patch.rs:208`). -/
inductive KeysDistinct : List (Nat × CfgTerm) → Prop where
  | nil : KeysDistinct []
  | cons {k : Nat} {t : CfgTerm} {rest : List (Nat × CfgTerm)}
      (hfresh : ∀ p ∈ rest, p.1 ≠ k) (hrest : KeysDistinct rest) :
      KeysDistinct ((k, t) :: rest)

theorem applyOneTermPatch_comm (cfg : Cfg) (e1 e2 : Nat × CfgTerm) (hne : e1.1 ≠ e2.1) :
    applyOneTermPatch (applyOneTermPatch cfg e1) e2 =
    applyOneTermPatch (applyOneTermPatch cfg e2) e1 := by
  -- Prove elementwise equality via `List.ext_get?` / structural helper:
  have hext : ∀ (xs ys : List CfgBlock),
      xs.length = ys.length → (∀ i, getOpt xs i = getOpt ys i) → xs = ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys hlen _
      cases ys with
      | nil => rfl
      | cons _ _ => cases hlen
    | cons x xs ih =>
      intro ys hlen hget
      cases ys with
      | nil => cases hlen
      | cons y ys =>
        have h0 := hget 0
        simp only [getOpt_cons_zero] at h0
        injection h0 with hxy
        subst hxy
        exact congrArg (List.cons x) (ih ys (Nat.succ.inj hlen) (fun i => hget (i + 1)))
  have hlen1 : ∀ c e, (applyOneTermPatch c e).length = c.length := by
    intro c e; unfold applyOneTermPatch; cases getOpt c e.1 with | none => rfl | some _ => exact setAt_length _ _ _
  apply hext
  · rw [hlen1, hlen1, hlen1, hlen1]
  · intro i
    dsimp only [applyOneTermPatch]
    cases h1 : getOpt cfg e1.1 with
    | none =>
      dsimp only
      cases h2 : getOpt cfg e2.1 with
      | none =>
        dsimp only; rw [h1]
      | some b2 =>
        dsimp only
        rw [getOpt_setAt_ne (fun h => hne h.symm), h1]
    | some b1 =>
      dsimp only
      cases h2 : getOpt cfg e2.1 with
      | none =>
        dsimp only
        rw [getOpt_setAt_ne hne, h2]
        dsimp only
        rw [h1]
      | some b2 =>
        dsimp only
        rw [getOpt_setAt_ne hne, h2, getOpt_setAt_ne (fun h => hne h.symm), h1]
        dsimp only
        by_cases hi1 : e1.1 = i
        · subst hi1
          rw [getOpt_setAt_ne (fun h => hne h.symm), getOpt_setAt_same (getOpt_some_lt h1)]
          have hlt1 : e1.1 < (setAt cfg e2.1 { b2 with stmts := match e2.2 with | .unreachable => [] | _ => b2.stmts, term := e2.2 }).length := by
            rw [setAt_length]; exact getOpt_some_lt h1
          rw [getOpt_setAt_same hlt1]
        · by_cases hi2 : e2.1 = i
          · subst hi2
            have hlt2 : e2.1 < (setAt cfg e1.1 { b1 with stmts := match e1.2 with | .unreachable => [] | _ => b1.stmts, term := e1.2 }).length := by
              rw [setAt_length]; exact getOpt_some_lt h2
            rw [getOpt_setAt_same hlt2, getOpt_setAt_ne hi1, getOpt_setAt_same (getOpt_some_lt h2)]
          · rw [getOpt_setAt_ne hi2, getOpt_setAt_ne hi1, getOpt_setAt_ne hi1, getOpt_setAt_ne hi2]

/-- **Theorem 4.5 (`term_patch_swap_order_independent`)**:
Because `patch_terminator` enforces distinct block keys (`patch.rs:208`), swapping any two
distinct terminator patches in `term_patch_map` produces the identical MIR body — justifying
`#[allow(rustc::potential_query_instability)]` at `patch.rs:319`! -/
theorem term_patch_swap_order_independent (cfg : Cfg) (e1 e2 : Nat × CfgTerm)
    (rest : List (Nat × CfgTerm)) (hne : e1.1 ≠ e2.1) :
    applyTermPatches cfg (e1 :: e2 :: rest) = applyTermPatches cfg (e2 :: e1 :: rest) := by
  rw [applyTermPatches_cons, applyTermPatches_cons, applyTermPatches_cons, applyTermPatches_cons]
  rw [applyOneTermPatch_comm cfg e1 e2 hne]

/-- **Theorem 4.6 (`unreachable_term_patch_clears_prior_and_new_statements`)**:
Because Stage 3 (`term_patch_map`) runs *after* Stage 2 (`new_statements`), patching block `bb`
to `TerminatorKind::Unreachable` clears `bb.statements` to `[]` EVEN IF `new_statements`
inserted statements into `bb` within the very same `MirPatch` (`patch.rs:320-327`)! -/
theorem unreachable_term_patch_clears_prior_and_new_statements
    (p : MirPatch) (cfg : Cfg) (bb : Nat) (rest : List (Nat × CfgTerm))
    (hpatch : p.termPatches = (bb, .unreachable) :: rest)
    (hdist : ∀ e ∈ rest, e.1 ≠ bb)
    (hlt : bb < (cfg ++ p.newBlocks).length) :
    ∃ b, getOpt (p.apply cfg) bb = some b ∧ b.stmts = [] ∧ b.term = .unreachable := by
  unfold MirPatch.apply
  rw [hpatch]
  let s2 : Cfg := applyNewStmts (applyNops (cfg ++ p.newBlocks) p.nopLocs) p.newStmts
  have hs2len : s2.length = (cfg ++ p.newBlocks).length := by
    dsimp only [s2]
    rw [applyNewStmts_length]
    generalize (cfg ++ p.newBlocks) = base
    induction p.nopLocs generalizing base with
    | nil => rfl
    | cons l ls ih =>
      rw [applyNops_cons, ih, applyOneNop_length]
  have hlt2 : bb < s2.length := hs2len.symm ▸ hlt
  have hget2 : ∃ b0, getOpt s2 bb = some b0 := by
    have haux : ∀ (xs : Cfg) (k : Nat), k < xs.length → ∃ b0, getOpt xs k = some b0 := by
      intro xs
      induction xs with
      | nil => intro k hk; exact False.elim (nat_not_lt_zero k hk)
      | cons x xs ih =>
        intro k hk
        cases k with
        | zero => exact ⟨x, rfl⟩
        | succ m => exact ih m (Nat.lt_of_succ_lt_succ hk)
    exact haux s2 bb hlt2
  let ⟨b0, hb0⟩ := hget2
  have hstep1 : getOpt (applyOneTermPatch s2 (bb, .unreachable)) bb =
                some { b0 with stmts := [], term := .unreachable } := by
    dsimp only [applyOneTermPatch]
    rw [hb0]
    exact getOpt_setAt_same hlt2 _
  have hpres : ∀ (c : Cfg) (es : List (Nat × CfgTerm)),
      (∀ e ∈ es, e.1 ≠ bb) → getOpt (applyTermPatches c es) bb = getOpt c bb := by
    intro c es hne
    induction es generalizing c with
    | nil => rfl
    | cons e es' ih =>
      rw [applyTermPatches_cons, ih _ (fun x hx => hne x (List.Mem.tail e hx))]
      dsimp only [applyOneTermPatch]
      cases getOpt c e.1 with
      | none => rfl
      | some _ => exact getOpt_setAt_ne (hne e (List.Mem.head es')) _
  refine ⟨{ b0 with stmts := [], term := .unreachable }, ?_, rfl, rfl⟩
  rw [applyTermPatches_cons, hpres _ rest hdist, hstep1]

/-- Singleton-block cache model mirroring `MirPatch` lines 19-25, 86-150. -/
structure SingletonCache where
  blocks : Cfg
  unreachableCleanup : Option Nat
  unreachableNoCleanup : Option Nat
  terminateSlot : Option (Nat × Nat) -- `(BasicBlock, UnwindTerminateReason)`

def SingletonCache.getUnreachableCleanup (sc : SingletonCache) : Nat × SingletonCache :=
  match sc.unreachableCleanup with
  | some bb => (bb, sc)
  | none =>
    let bb := sc.blocks.length
    let blk : CfgBlock := { stmts := [], term := .unreachable, isCleanup := true }
    (bb, { sc with blocks := sc.blocks ++ [blk], unreachableCleanup := some bb })

def SingletonCache.getUnreachableNoCleanup (sc : SingletonCache) : Nat × SingletonCache :=
  match sc.unreachableNoCleanup with
  | some bb => (bb, sc)
  | none =>
    let bb := sc.blocks.length
    let blk : CfgBlock := { stmts := [], term := .unreachable, isCleanup := false }
    (bb, { sc with blocks := sc.blocks ++ [blk], unreachableNoCleanup := some bb })

def SingletonCache.getTerminateBlock (sc : SingletonCache) (reason : Nat) :
    Nat × SingletonCache :=
  match sc.terminateSlot with
  | some (bb, cachedReason) =>
    if reason == cachedReason then (bb, sc)
    else
      let newBb := sc.blocks.length
      let blk : CfgBlock := { stmts := [], term := .unwindTerminate reason, isCleanup := true }
      (newBb, { sc with blocks := sc.blocks ++ [blk], terminateSlot := some (newBb, reason) })
  | none =>
    let newBb := sc.blocks.length
    let blk : CfgBlock := { stmts := [], term := .unwindTerminate reason, isCleanup := true }
    (newBb, { sc with blocks := sc.blocks ++ [blk], terminateSlot := some (newBb, reason) })

/-- **Theorem 4.7 (`bipartite_unreachable_singletons_preserve_validator`)**:
Allocating `unreachable_cleanup_block` yields an empty `Unreachable` block with `isCleanup = true`,
and `unreachable_no_cleanup_block` yields an empty `Unreachable` block with `isCleanup = false`,
preserving `ValidCleanupCfg` (`validate.rs:145-162` & `537`) on both partitions — whereas routing
a normal edge from a non-cleanup block to a cleanup unreachable block breaks `ValidCleanupCfg`! -/
theorem bipartite_unreachable_singletons_preserve_validator (cfg : Cfg) (hval : ValidCleanupCfg cfg) :
    let sc0 : SingletonCache := { blocks := cfg, unreachableCleanup := none,
                                  unreachableNoCleanup := none, terminateSlot := none }
    let (bbClean, sc1) := sc0.getUnreachableCleanup
    let (bbNoClean, sc2) := sc1.getUnreachableNoCleanup
    getOpt sc2.blocks bbClean = some { stmts := [], term := .unreachable, isCleanup := true } ∧
    getOpt sc2.blocks bbNoClean = some { stmts := [], term := .unreachable, isCleanup := false } ∧
    ValidCleanupCfg sc2.blocks := by
  dsimp only [SingletonCache.getUnreachableCleanup, SingletonCache.getUnreachableNoCleanup]
  let blkC : CfgBlock := { stmts := [], term := .unreachable, isCleanup := true }
  have hlen1 : (cfg ++ [blkC]).length = cfg.length + 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [getOpt_append_left (by rw [hlen1]; exact nat_lt_succ_self cfg.length)]
    rw [getOpt_append_right (nat_le_refl cfg.length), Nat.sub_self]
    rfl
  · rw [getOpt_append_right (nat_le_refl _), Nat.sub_self]
    rfl
  · intro bb b hb
    by_cases hlt : bb < cfg.length
    · rw [getOpt_append_left (Nat.lt_trans hlt (by rw [hlen1]; exact nat_lt_succ_self _))] at hb
      rw [getOpt_append_left hlt] at hb
      let ⟨hsucc, hret, hres, hterm⟩ := hval bb b hb
      refine ⟨?_, hret, hres, hterm⟩
      intro t ht
      let ⟨tb, htb, hcl⟩ := hsucc t ht
      have htlt : t < cfg.length := getOpt_some_lt htb
      refine ⟨tb, ?_, hcl⟩
      rw [getOpt_append_left (Nat.lt_trans htlt (by rw [hlen1]; exact nat_lt_succ_self _))]
      rw [getOpt_append_left htlt]
      exact htb
    · have hge : cfg.length ≤ bb := Nat.le_of_not_lt hlt
      by_cases heq1 : bb = cfg.length
      · subst heq1
        rw [getOpt_append_left (by rw [hlen1]; exact nat_lt_succ_self _)] at hb
        rw [getOpt_append_right (nat_le_refl _), Nat.sub_self] at hb
        simp only [getOpt_cons_zero] at hb
        injection hb with hbeq; subst hbeq
        exact ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩
      · have hgt : cfg.length + 1 ≤ bb := by
          cases nat_cases_lt_or_eq_of_le hge with
          | inl hl => exact hl
          | inr he => exact False.elim (heq1 he.symm)
        rw [getOpt_append_right (hlen1.symm ▸ hgt)] at hb
        cases hdiff : (bb - (cfg ++ [blkC]).length) with
        | zero =>
          rw [hdiff] at hb
          simp only [getOpt_cons_zero] at hb
          injection hb with hbeq; subst hbeq
          exact ⟨fun _ h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩
        | succ _ =>
          rw [hdiff] at hb; cases hb

/-- **Theorem 4.8 (`terminate_block_single_slot_reallocation`)**:
Models `MirPatch::terminate_block` (`patch.rs:134-150`):
* Repeating the same `UnwindTerminateReason` reuses the cached block (`0` new allocations).
* Alternating reasons `Abi (0)` -> `InCleanup (1)` -> `Abi (0)` evicts the single slot and
  allocates `3` distinct blocks (not `2`)! -/
theorem terminate_block_single_slot_reallocation :
    let sc0 : SingletonCache := { blocks := [], unreachableCleanup := none,
                                  unreachableNoCleanup := none, terminateSlot := none }
    let (b1, sc1) := sc0.getTerminateBlock 0
    let (b2, sc2) := sc1.getTerminateBlock 0
    let (b3, sc3) := sc2.getTerminateBlock 1
    let (b4, sc4) := sc3.getTerminateBlock 0
    b1 = 0 ∧ b2 = 0 ∧ sc2.blocks.length = 1 ∧
    b3 = 1 ∧ b4 = 2 ∧ sc4.blocks.length = 3 := by
  decide

end Part4MirPatch

end MirLivenessMentionedItemsAndPatch

