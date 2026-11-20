import ToyPerm.PCM

/-!
# The sharing-depth design

A toy model of a per-byte permission design in which every *view* (an
allocation record or a raw-pointer exposure) holds one cell per byte:

* `shared 0 v` — exclusive (writable) permission, payload `v`;
* `shared (d+1) v` — read permission; the view has recorded `d+1` outstanding
  local shares (the depth is a counter kept by the view, not a fraction);
* `borrowed` — the view has lent its permission away and contributes none.

Several views may describe the same physical byte. The global invariant
requires every two active views at the same address to be *compatible*:
`borrowed` is compatible with everything; two `shared` cells are compatible iff
both depths are positive and the payloads are equal. A per-view transition
(write, borrow, end-borrow, share, end-share) is enabled iff it is defined on the
view's cell and the resulting configuration is still pairwise compatible.

This mirrors the cell type, the per-cell operations, and the compatibility check
of a public memory-model prototype for the Aeneas Rust verification toolchain
(pull request 1497 of the `AeneasVerif/aeneas` repository, head commit
`d17ca83fc07d712d1785f650840cb2073c259e69`, file
`backends/lean/Aeneas/Std/Heap/Repr.lean`: `Cell`, `Cell.write`, `Cell.borrow`,
`Cell.endBorrow`, `Cell.share`, `Cell.endShare`, `Cell.compatible`). The model
here is a restatement at a single address; allocation, ranges, provenance,
view creation and retirement, scoped return authority, and permissions held
implicitly outside the explicit heap are not modelled. In particular the
prototype retires an independent shared exposure at depth 1 (removing the view)
instead of decrementing it to depth 0; this model has no retirement step, so a
configuration here keeps all its views.
-/

namespace Toy.Perm

/-- One view's permission cell for one byte: `shared d v` (readable; exclusive
iff `d = 0`; `d` counts the view's outstanding local shares) or `borrowed`
(permission lent away, no access). -/
inductive Cell (V : Type) where
  /-- Readable contribution with payload `value` at sharing depth `depth`. -/
  | shared (depth : Nat) (value : V)
  /-- The view's permission is lent away; it contributes no permission. -/
  | borrowed
deriving DecidableEq, Repr

namespace Cell

variable {V : Type} [DecidableEq V]

/-- Compatibility of two contributions at the same address held by two distinct
views: `borrowed` is compatible with everything, and two `shared` cells are
compatible iff both depths are positive and the payloads agree. In particular a
depth-0 (exclusive) cell is compatible only with `borrowed`. -/
def compat : Cell V → Cell V → Bool
  | .borrowed, _ => true
  | _, .borrowed => true
  | .shared n x, .shared m y => decide (0 < n) && decide (0 < m) && decide (x = y)

theorem compat_comm (a b : Cell V) : compat a b = compat b a := by
  cases a with
  | borrowed => cases b <;> rfl
  | shared n x =>
    cases b with
    | borrowed => rfl
    | shared m y =>
      simp only [compat]
      by_cases h : x = y
      · subst h; simp [Bool.and_comm]
      · have h' : ¬ y = x := fun e => h e.symm
        simp [h, h']

/-- Positive examples of `compat`: readers at different positive depths with the
same payload coexist, and `borrowed` coexists with a writer. -/
theorem compat_examples (v : V) :
    compat (.shared 1 v) (.shared 2 v) = true ∧ compat (.shared 0 v) .borrowed = true ∧
      compat .borrowed (.borrowed : Cell V) = true := by
  simp [compat]

/-- Negative examples of `compat`: a writer excludes readers and other writers,
and readers with different payloads conflict. -/
theorem compat_negative_examples (v w : V) (hvw : v ≠ w) :
    compat (.shared 0 v) (.shared 1 v) = false ∧ compat (.shared 0 v) (.shared 0 v) = false ∧
      compat (.shared 1 v) (.shared 1 w) = false := by
  simp [compat, hvw]

end Cell

/-- The per-view operations of the design. -/
inductive CellStep (V : Type) where
  /-- Overwrite the payload (requires depth 0). -/
  | write (v : V)
  /-- Lend the whole permission away (depth 0 to `borrowed`). -/
  | borrow
  /-- Take a lent permission back with a new payload (`borrowed` to depth 0). -/
  | endBorrow (v : V)
  /-- Record one more outstanding share (depth `d` to `d+1`). -/
  | share
  /-- Record that one share ended (depth `d+1` to `d`). -/
  | endShare

namespace CellStep

variable {V : Type}

/-- The effect of an operation on one cell, `none` if the operation is not
defined on that cell. -/
def apply : CellStep V → Cell V → Option (Cell V)
  | .write v, .shared 0 _ => some (.shared 0 v)
  | .borrow, .shared 0 _ => some .borrowed
  | .endBorrow v, .borrowed => some (.shared 0 v)
  | .share, .shared d v => some (.shared (d + 1) v)
  | .endShare, .shared (d + 1) v => some (.shared d v)
  | _, _ => none

/-- Positive examples of `apply`. -/
theorem apply_examples (v w : V) :
    (CellStep.endShare).apply (.shared 1 v) = some (.shared 0 v) ∧
      (CellStep.share).apply (.shared 0 v) = some (.shared 1 v) ∧
      (CellStep.write w).apply (.shared 0 v) = some (.shared 0 w) ∧
      (CellStep.endBorrow w).apply (.borrowed : Cell V) = some (.shared 0 w) := by
  simp [apply]

/-- Negative examples of `apply`: no write or borrow below a positive depth, no
end-share at depth 0, and nothing but `endBorrow` applies to `borrowed`. -/
theorem apply_negative_examples (v w : V) :
    (CellStep.write w).apply (.shared 1 v) = none ∧ (CellStep.borrow).apply (.shared 1 v) = none ∧
      (CellStep.endShare).apply (.shared 0 v) = none ∧
      (CellStep.share).apply (.borrowed : Cell V) = none := by
  simp [apply]

/-- A step *restores exclusivity* on a cell if it produces a depth-0 cell from a
cell that was not at depth 0. These are exactly the last end-share
(`shared 1 v ⇝ shared 0 v`) and end-borrow (`borrowed ⇝ shared 0 v`). -/
def RestoresExclusive (t : CellStep V) (c : Cell V) : Prop :=
  (∃ v, t.apply c = some (.shared 0 v)) ∧ ∀ w, c ≠ .shared 0 w

/-- Positive examples: the last end-share and end-borrow restore exclusivity. -/
theorem restoresExclusive_examples (v w : V) :
    (CellStep.endShare).RestoresExclusive (.shared 1 v) ∧
      (CellStep.endBorrow w).RestoresExclusive (.borrowed : Cell V) := by
  refine ⟨⟨⟨v, rfl⟩, fun u h => ?_⟩, ⟨⟨w, rfl⟩, fun u h => ?_⟩⟩ <;> cases h

/-- Negative examples: a write at depth 0 and an end-share from depth 2 do not
restore exclusivity. -/
theorem restoresExclusive_negative_examples (v w : V) :
    ¬ (CellStep.write w).RestoresExclusive (.shared 0 v) ∧
      ¬ (CellStep.endShare).RestoresExclusive (.shared 2 v) := by
  refine ⟨fun h => h.2 v rfl, fun h => ?_⟩
  obtain ⟨⟨u, hu⟩, _⟩ := h
  simp [apply] at hu

/-- **The exclusivity-restoring steps are exactly the last end-share and the
end-borrow.** -/
theorem restoresExclusive_iff (t : CellStep V) (c : Cell V) :
    t.RestoresExclusive c ↔
      (t = .endShare ∧ ∃ v, c = .shared 1 v) ∨ (∃ v, t = .endBorrow v ∧ c = .borrowed) := by
  constructor
  · rintro ⟨⟨v, hv⟩, hne⟩
    cases t with
    | write w =>
      cases c with
      | borrowed => simp [apply] at hv
      | shared d u =>
        cases d with
        | zero => exact absurd rfl (hne u)
        | succ _ => simp [apply] at hv
    | borrow =>
      cases c with
      | borrowed => simp [apply] at hv
      | shared d u =>
        cases d with
        | zero => exact absurd rfl (hne u)
        | succ _ => simp [apply] at hv
    | endBorrow w =>
      cases c with
      | borrowed => exact .inr ⟨w, rfl, rfl⟩
      | shared _ _ => simp [apply] at hv
    | share =>
      cases c with
      | borrowed => simp [apply] at hv
      | shared _ _ => simp [apply] at hv
    | endShare =>
      cases c with
      | borrowed => simp [apply] at hv
      | shared d u =>
        cases d with
        | zero => simp [apply] at hv
        | succ d =>
          cases d with
          | zero => exact .inl ⟨rfl, u, rfl⟩
          | succ _ => simp [apply] at hv
  · rintro (⟨rfl, v, rfl⟩ | ⟨v, rfl, rfl⟩)
    · exact ⟨⟨v, rfl⟩, fun w h => by cases h⟩
    · exact ⟨⟨v, rfl⟩, fun w h => by cases h⟩

end CellStep

namespace Cell

variable {V : Type} [DecidableEq V]

/-- A configuration (the cells of all active views at one address) is valid iff
its cells are pairwise compatible. -/
def Valid (cfg : List (Cell V)) : Prop := cfg.Pairwise (fun a b => compat a b = true)

instance (cfg : List (Cell V)) : Decidable (Valid cfg) := by
  unfold Valid; infer_instance

/-- Apply operation `t` to the view at position `i`: defined iff `t` is defined
on that view's cell and the resulting configuration is valid. -/
def stepAt (cfg : List (Cell V)) (i : Nat) (t : CellStep V) : Option (List (Cell V)) :=
  match cfg[i]? with
  | none => none
  | some c =>
    match t.apply c with
    | none => none
    | some c' => if Valid (cfg.set i c') then some (cfg.set i c') else none

/-- Positive example of `Valid`: two readers and a borrowed view. Negative
example: a writer next to a reader. -/
theorem valid_examples :
    Valid [Cell.shared 1 (7 : Nat), .shared 2 7, .borrowed] ∧
      ¬ Valid [Cell.shared 0 (7 : Nat), .shared 1 7] := by
  decide

/-- Positive example of `stepAt`: a lone view at depth 1 ends its last share and
becomes exclusive. Negative example: with a second reader present, neither view
can end its last share. -/
theorem stepAt_examples :
    stepAt [Cell.shared 1 (7 : Nat)] 0 .endShare = some [.shared 0 7] ∧
      stepAt [Cell.shared 1 (7 : Nat), .shared 1 7] 0 .endShare = none := by
  decide

/-- A frame-preserving cell update with respect to `compat`: every cell
compatible with `a` is compatible with `b`. -/
def CompatFPU (a b : Cell V) : Prop := ∀ f, compat a f = true → compat b f = true

/-- Positive example: sharing from depth 0 is frame-preserving. Negative example:
the last end-share is not (the frame `shared 1 v` witnesses it). -/
theorem compatFPU_examples (v : V) :
    CompatFPU (.shared 0 v) (.shared 1 v) ∧ ¬ CompatFPU (.shared 1 v) (.shared 0 v) := by
  refine ⟨fun f hf => ?_, fun h => ?_⟩
  · cases f with
    | borrowed => rfl
    | shared m y => simp [compat] at hf
  · have := h (.shared 1 v) (by simp [compat]); simp [compat] at this

/-! ## Results -/

/-- Helper lemma (definitional): for every frame cell `f`, a cell
`shared (n+1) v` is compatible with `f` iff `shared (m+1) v` is; the value of a
positive depth plays no role in compatibility. -/
theorem compat_positive_depth_irrelevant (n m : Nat) (v : V) (f : Cell V) :
    compat (.shared (n + 1) v) f = compat (.shared (m + 1) v) f := by
  cases f with
  | borrowed => rfl
  | shared k y => simp [compat]

/-- **Characterization of the frame-preserving cell updates.** With respect to
the compatibility relation of the sharing-depth design, `a ⇝ b` is
frame-preserving iff `b = borrowed`, or `a` is a writer (`shared 0 _`), or `a`
and `b` are both readers (positive depth) with the same payload. -/
theorem compatFPU_iff (a b : Cell V) :
    CompatFPU a b ↔
      b = .borrowed ∨ (∃ v, a = .shared 0 v) ∨
        (∃ n m v, a = .shared (n + 1) v ∧ b = .shared (m + 1) v) := by
  constructor
  · intro h
    cases b with
    | borrowed => exact .inl rfl
    | shared m w =>
      cases a with
      | borrowed =>
        have := h (.shared 0 w) rfl
        simp [compat] at this
      | shared n v =>
        cases n with
        | zero => exact .inr (.inl ⟨v, rfl⟩)
        | succ n =>
          cases m with
          | zero =>
            have := h (.shared 1 v) (by simp [compat])
            simp [compat] at this
          | succ m =>
            have := h (.shared 1 v) (by simp [compat])
            simp [compat] at this
            subst this
            exact .inr (.inr ⟨n, m, w, rfl, rfl⟩)
  · rintro (rfl | ⟨v, rfl⟩ | ⟨n, m, v, rfl, rfl⟩) f hf
    · cases f <;> rfl
    · cases f with
      | borrowed => cases b <;> rfl
      | shared _ _ => simp [compat] at hf
    · rwa [← compat_positive_depth_irrelevant n m v f]

/-- Non-vacuity / illustration of `compatFPU_iff` (at `V = Nat`, `v = 7`): the
writer disjunct is inhabited (`share` from depth 0) and so is the reader
disjunct (`endShare` from depth 2 to depth 1); the `borrowed` disjunct is
inhabited trivially. The last end-share (`shared 1 7 ⇝ shared 0 7`) falls under
none of the three. -/
theorem compatFPU_iff_nonvacuous :
    (∃ w, (Cell.shared 0 (7 : Nat)) = .shared 0 w) ∧
      (∃ n m w, (Cell.shared 2 (7 : Nat)) = .shared (n + 1) w ∧
        (Cell.shared 1 (7 : Nat)) = .shared (m + 1) w) ∧
      ¬ ((Cell.shared 0 (7 : Nat)) = .borrowed ∨ (∃ w, (Cell.shared 1 (7 : Nat)) = .shared 0 w) ∨
        (∃ n m w, (Cell.shared 1 (7 : Nat)) = .shared (n + 1) w ∧
          (Cell.shared 0 (7 : Nat)) = .shared (m + 1) w)) := by
  refine ⟨⟨7, rfl⟩, ⟨1, 0, 7, rfl, rfl⟩, ?_⟩
  rintro (h | ⟨w, h⟩ | ⟨n, m, w, _, h⟩) <;> cases h

/-- Proof helper: validity as pairwise compatibility of the cells at every two
positions `j < k`. -/
private theorem valid_iff_getElem_lt (cfg : List (Cell V)) :
    Valid cfg ↔ ∀ (j k : Nat) (a b : Cell V), j < k → cfg[j]? = some a → cfg[k]? = some b →
      compat a b = true := by
  induction cfg with
  | nil => simp [Valid]
  | cons x xs ih =>
    simp only [Valid, List.pairwise_cons]
    constructor
    · rintro ⟨hx, hxs⟩ j k a b hjk hj hk
      cases j with
      | zero =>
        cases k with
        | zero => omega
        | succ k =>
          simp at hj hk; subst hj
          exact hx b (List.mem_of_getElem? hk)
      | succ j =>
        cases k with
        | zero => omega
        | succ k =>
          simp at hj hk
          exact (ih.mp hxs) j k a b (by omega) hj hk
    · intro h
      refine ⟨fun b hb => ?_, ih.mpr fun j k a b hjk hj hk => h (j + 1) (k + 1) a b (by omega) hj hk⟩
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb
      exact h 0 (k + 1) x b (by omega) rfl hk

/-- Proof helper: validity as pairwise compatibility of the cells at every two
distinct positions. -/
private theorem valid_iff_getElem_ne (cfg : List (Cell V)) :
    Valid cfg ↔ ∀ (j k : Nat) (a b : Cell V), j ≠ k → cfg[j]? = some a → cfg[k]? = some b →
      compat a b = true := by
  rw [valid_iff_getElem_lt]
  constructor
  · intro h j k a b hne hj hk
    by_cases hlt : j < k
    · exact h j k a b hlt hj hk
    · rw [compat_comm]; exact h k j b a (by omega) hk hj
  · intro h j k a b hlt hj hk
    exact h j k a b (by omega) hj hk

/-- Proof helper: a defined per-view operation that does not restore
exclusivity is a frame-preserving update. -/
private theorem nonRestoring_step_compatFPU {t : CellStep V} {c c' : Cell V}
    (ht : t.apply c = some c') (hnr : ¬ t.RestoresExclusive c) : CompatFPU c c' := by
  rw [compatFPU_iff]
  cases t with
  | write v =>
    cases c with
    | borrowed => simp [CellStep.apply] at ht
    | shared d u =>
      cases d with
      | zero => exact .inr (.inl ⟨u, rfl⟩)
      | succ _ => simp [CellStep.apply] at ht
  | borrow =>
    cases c with
    | borrowed => simp [CellStep.apply] at ht
    | shared d u =>
      cases d with
      | zero => simp [CellStep.apply] at ht; subst ht; exact .inl rfl
      | succ _ => simp [CellStep.apply] at ht
  | endBorrow v =>
    cases c with
    | borrowed => exact absurd ((CellStep.restoresExclusive_iff _ _).mpr (.inr ⟨v, rfl, rfl⟩)) hnr
    | shared _ _ => simp [CellStep.apply] at ht
  | share =>
    cases c with
    | borrowed => simp [CellStep.apply] at ht
    | shared d u =>
      simp [CellStep.apply] at ht; subst ht
      cases d with
      | zero => exact .inr (.inl ⟨u, rfl⟩)
      | succ d => exact .inr (.inr ⟨d, d + 1, u, rfl, rfl⟩)
  | endShare =>
    cases c with
    | borrowed => simp [CellStep.apply] at ht
    | shared d u =>
      cases d with
      | zero => simp [CellStep.apply] at ht
      | succ d =>
        cases d with
        | zero => exact absurd ((CellStep.restoresExclusive_iff _ _).mpr (.inl ⟨rfl, u, rfl⟩)) hnr
        | succ d =>
          simp [CellStep.apply] at ht; subst ht
          exact .inr (.inr ⟨d + 1, d, u, rfl, rfl⟩)

/-- **Characterization of the transition system.** In a valid configuration,
applying a per-view operation `t` that is defined on view `i`'s cell `c`
(result `c'`) yields a valid configuration iff, in case the operation restores
exclusivity, every *other* view at that address is `borrowed`. By
`CellStep.restoresExclusive_iff` the restoring operations are exactly the last
end-share and the end-borrow; every other operation, when defined on the cell
(write and borrow at depth 0, share, end-share from depth at least 2), always
yields a valid configuration. -/
theorem valid_set_iff (cfg : List (Cell V)) (hv : Valid cfg) (i : Nat) (c c' : Cell V)
    (t : CellStep V) (hi : cfg[i]? = some c) (ht : t.apply c = some c') :
    Valid (cfg.set i c') ↔
      (t.RestoresExclusive c → ∀ j d, j ≠ i → cfg[j]? = some d → d = .borrowed) := by
  have hilen : i < cfg.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [valid_iff_getElem_ne] at hv ⊢
  have hget : ∀ k, (cfg.set i c')[k]? = if k = i then some c' else cfg[k]? := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [hilen]
    · simp [List.getElem?_set_ne, hk, Ne.symm hk]
  constructor
  · intro hv' hrest j d hne hj
    obtain ⟨⟨v, hv0⟩, _⟩ := hrest
    rw [ht] at hv0; cases hv0
    have hc := hv' i j (.shared 0 v) d (Ne.symm hne) (by rw [hget]; simp) (by rw [hget]; simp [hne, hj])
    cases d with
    | borrowed => rfl
    | shared _ _ => simp [compat] at hc
  · intro hcond j k a b hne hj hk
    rw [hget] at hj hk
    by_cases hji : j = i
    · subst hji; simp at hj; subst hj
      have hki : k ≠ j := Ne.symm hne
      simp [hki] at hk
      by_cases hrest : t.RestoresExclusive c
      · have hd := hcond hrest k b hki hk; subst hd; cases c' <;> rfl
      · exact nonRestoring_step_compatFPU ht hrest b (hv j k c b (Ne.symm hki) hi hk)
    · by_cases hki : k = i
      · subst hki; simp at hk; subst hk
        simp [hji] at hj
        rw [compat_comm]
        by_cases hrest : t.RestoresExclusive c
        · have hd := hcond hrest j a hji hj; subst hd; cases c' <;> rfl
        · exact nonRestoring_step_compatFPU ht hrest a (hv k j c a (Ne.symm hji) hi hj)
      · simp [hji] at hj; simp [hki] at hk
        exact hv j k a b hne hj hk

/-- **Bridge to `stepAt`.** In a valid configuration, `stepAt cfg i t` is
enabled iff view `i` exists with cell `c`, `t` is defined on `c`, and if `t`
restores exclusivity then every other view is `borrowed`. (Derived from
`valid_set_iff`.) -/
theorem stepAt_isSome_iff (cfg : List (Cell V)) (hv : Valid cfg) (i : Nat) (t : CellStep V) :
    (stepAt cfg i t).isSome = true ↔
      ∃ c c', cfg[i]? = some c ∧ t.apply c = some c' ∧
        (t.RestoresExclusive c → ∀ j d, j ≠ i → cfg[j]? = some d → d = .borrowed) := by
  unfold stepAt
  cases hi : cfg[i]? with
  | none => simp
  | some c =>
    dsimp only
    cases ht : t.apply c with
    | none => simp [ht]
    | some c' =>
      dsimp only
      by_cases hval : Valid (cfg.set i c')
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hval)]
        simp only [Option.isSome_some, true_iff]
        exact ⟨c, c', rfl, ht, (valid_set_iff cfg hv i c c' t hi ht).mp hval⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hval)]
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        rintro ⟨c₁, c₁', hc₁, hc₁', hcond⟩
        cases hc₁
        rw [ht] at hc₁'; cases hc₁'
        exact hval ((valid_set_iff cfg hv i c c' t hi ht).mpr hcond)

/-- Tightness of `hv` in `valid_set_iff` (canonical form): in the invalid
configuration `[shared 0 7, shared 0 7]`, view 0 holds `shared 0 7` and sharing
it is defined (`hi`, `ht` hold), but the equivalence fails: sharing does not
restore exclusivity (so the right-hand side holds) while the result
`[shared 1 7, shared 0 7]` is invalid. -/
theorem valid_set_iff_needs_valid :
    ¬ Valid [Cell.shared 0 (7 : Nat), .shared 0 7] ∧
      [Cell.shared 0 (7 : Nat), .shared 0 7][0]? = some (.shared 0 7) ∧
      (CellStep.share : CellStep Nat).apply (.shared 0 7) = some (.shared 1 7) ∧
      ¬ (Valid ([Cell.shared 0 (7 : Nat), .shared 0 7].set 0 (.shared 1 7)) ↔
        ((CellStep.share : CellStep Nat).RestoresExclusive (.shared 0 7) →
          ∀ j d, j ≠ 0 → [Cell.shared 0 (7 : Nat), .shared 0 7][j]? = some d → d = .borrowed)) := by
  refine ⟨by decide, rfl, rfl, fun hiff => ?_⟩
  have hv : Valid ([Cell.shared 0 (7 : Nat), .shared 0 7].set 0 (.shared 1 7)) :=
    hiff.mpr (fun h => absurd rfl (h.2 7))
  revert hv; decide

/-- Tightness of `hv` in `stepAt_isSome_iff` (canonical form): in the invalid
configuration `[shared 0 7, shared 0 7]`, sharing view 0 is defined on its cell
and does not restore exclusivity, so the right-hand side holds, yet the step is
not enabled because the result is invalid. -/
theorem stepAt_isSome_iff_needs_valid :
    ¬ Valid [Cell.shared 0 (7 : Nat), .shared 0 7] ∧
      ¬ ((stepAt [Cell.shared 0 (7 : Nat), .shared 0 7] 0 .share).isSome = true ↔
        ∃ c c', [Cell.shared 0 (7 : Nat), .shared 0 7][0]? = some c ∧
          (CellStep.share : CellStep Nat).apply c = some c' ∧
          ((CellStep.share : CellStep Nat).RestoresExclusive c →
            ∀ j d, j ≠ 0 → [Cell.shared 0 (7 : Nat), .shared 0 7][j]? = some d → d = .borrowed)) := by
  refine ⟨by decide, fun hiff => ?_⟩
  have h := hiff.mpr ⟨.shared 0 7, .shared 1 7, rfl, rfl, fun h => absurd rfl (h.2 7)⟩
  revert h; decide

/-- Tightness of `ht` in `valid_set_iff` (canonical form): with the valid
configuration `[shared 1 7, shared 1 7]`, `i = 0` (`hi` holds), `t = share` and
the unrelated `c' = shared 0 7` (so `ht` fails), the equivalence fails: `share`
does not restore exclusivity (the right-hand side holds) but the result is
invalid. -/
theorem valid_set_iff_needs_apply :
    Valid [Cell.shared 1 (7 : Nat), .shared 1 7] ∧
      [Cell.shared 1 (7 : Nat), .shared 1 7][0]? = some (.shared 1 7) ∧
      (CellStep.share : CellStep Nat).apply (.shared 1 7) ≠ some (.shared 0 7) ∧
      ¬ (Valid ([Cell.shared 1 (7 : Nat), .shared 1 7].set 0 (.shared 0 7)) ↔
        ((CellStep.share : CellStep Nat).RestoresExclusive (.shared 1 7) →
          ∀ j d, j ≠ 0 → [Cell.shared 1 (7 : Nat), .shared 1 7][j]? = some d → d = .borrowed)) := by
  refine ⟨by decide, rfl, by decide, fun hiff => ?_⟩
  have hnr : ¬ (CellStep.share : CellStep Nat).RestoresExclusive (.shared 1 7) := by
    rintro ⟨⟨u, hu⟩, _⟩; simp [CellStep.apply] at hu
  have hv : Valid ([Cell.shared 1 (7 : Nat), .shared 1 7].set 0 (.shared 0 7)) :=
    hiff.mpr (fun h => absurd h hnr)
  revert hv; decide

/-- Tightness of `hi` in `valid_set_iff` (canonical form): with the valid
configuration `[shared 1 7, shared 1 7]`, `i = 5` (out of range, so `hi` fails
for `c = borrowed`), `t = endBorrow 8` and `c' = shared 0 8` (`ht` holds), the
equivalence fails: the step restores exclusivity and view 0 is not borrowed (the
right-hand side is false), yet `set 5` changes nothing and the result is
valid. -/
theorem valid_set_iff_needs_lookup :
    Valid [Cell.shared 1 (7 : Nat), .shared 1 7] ∧
      [Cell.shared 1 (7 : Nat), .shared 1 7][5]? ≠ some .borrowed ∧
      (CellStep.endBorrow 8 : CellStep Nat).apply .borrowed = some (.shared 0 8) ∧
      ¬ (Valid ([Cell.shared 1 (7 : Nat), .shared 1 7].set 5 (.shared 0 8)) ↔
        ((CellStep.endBorrow 8 : CellStep Nat).RestoresExclusive .borrowed →
          ∀ j d, j ≠ 5 → [Cell.shared 1 (7 : Nat), .shared 1 7][j]? = some d → d = .borrowed)) := by
  refine ⟨by decide, by decide, rfl, fun hiff => ?_⟩
  have h := hiff.mp (by decide) (CellStep.restoresExclusive_examples 8 8).2 0 (.shared 1 7)
    (by decide) rfl
  cases h

/-- Non-vacuity of `valid_set_iff`: the configuration `[shared 1 v, borrowed]`
is valid, and ending view 0's last share is defined, restores exclusivity, and
yields the valid configuration `[shared 0 v, borrowed]`. -/
theorem valid_set_iff_nonvacuous :
    Valid [Cell.shared 1 (7 : Nat), .borrowed] ∧
      [Cell.shared 1 (7 : Nat), .borrowed][0]? = some (.shared 1 7) ∧
      (CellStep.endShare : CellStep Nat).apply (.shared 1 7) = some (.shared 0 7) ∧
      (CellStep.endShare : CellStep Nat).RestoresExclusive (.shared 1 7) ∧
      Valid ([Cell.shared 1 (7 : Nat), .borrowed].set 0 (.shared 0 7)) :=
  ⟨by decide, rfl, rfl, (CellStep.restoresExclusive_examples 7 7).1, by decide⟩

end Cell

open Cell

/-! ## Partial algebras on cells -/

/-- Depth-sum composition of cells: `borrowed` is the unit, and two readers with
the same payload compose to a reader whose depth is the sum; all other pairs are
undefined. -/
def cellSumOp {V : Type} [DecidableEq V] : Cell V → Cell V → Option (Cell V)
  | .borrowed, c => some c
  | c, .borrowed => some c
  | .shared (n + 1) x, .shared (m + 1) y => if x = y then some (.shared (n + m + 2) x) else none
  | _, _ => none

/-- The depth-sum partial algebra on cells, with unit `borrowed`. -/
def cellSumAlg (V : Type) [DecidableEq V] : PartialAlg (Cell V) where
  op := cellSumOp
  unit := .borrowed

/-- Positive and negative examples of the depth-sum composition. -/
theorem cellSumAlg_examples :
    (cellSumAlg Nat).op (.shared 1 7) (.shared 2 7) = some (.shared 3 7) ∧
      (cellSumAlg Nat).op (.shared 0 7) .borrowed = some (.shared 0 7) ∧
      (cellSumAlg Nat).op (.shared 0 7) (.shared 1 7) = none ∧
      (cellSumAlg Nat).op (.shared 1 7) (.shared 1 8) = none := by
  decide

/-- **A partial commutative monoid with exactly the design's compatibility
exists.** The depth-sum algebra on cells is commutative, associative, has
`borrowed` as unit, is cancellative and positive, and two cells have a defined
composite iff they are compatible in the sense of `Cell.compat`. -/
theorem cellSumAlg_isPCM_cancel_positive_compat_iff (V : Type) [DecidableEq V] :
    (cellSumAlg V).IsPCM ∧ (cellSumAlg V).Cancel ∧ (cellSumAlg V).Positive ∧
      ∀ a b, (cellSumAlg V).Compat a b ↔ compat a b = true := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a b
    cases a with
    | borrowed => cases b <;> rfl
    | shared n x =>
      cases b with
      | borrowed => rfl
      | shared m y =>
        cases n <;> cases m <;> simp [cellSumAlg, cellSumOp]
        by_cases hxy : x = y
        · subst hxy; simp; omega
        · have hyx : y ≠ x := fun e => hxy e.symm
          simp [hxy, hyx]
  · intro a b c
    cases a with
    | borrowed =>
      show (cellSumOp .borrowed b).bind (fun ab => cellSumOp ab c) =
        (cellSumOp b c).bind (fun bc => cellSumOp .borrowed bc)
      change cellSumOp b c = (cellSumOp b c).bind (fun bc => some bc)
      cases cellSumOp b c <;> rfl
    | shared n x =>
      cases b with
      | borrowed => cases c <;> rfl
      | shared m y =>
        cases c with
        | borrowed =>
          show (cellSumOp (.shared n x) (.shared m y)).bind (fun ab => cellSumOp ab .borrowed) =
            cellSumOp (.shared n x) (.shared m y)
          cases cellSumOp (.shared n x) (.shared m y) with
          | none => rfl
          | some z => cases z <;> rfl
        | shared k z =>
          cases n <;> cases m <;> cases k <;> simp only [cellSumAlg, cellSumOp, Option.bind_none]
          · split <;> rfl
          · split <;> rfl
          · by_cases hxy : x = y <;> by_cases hyz : y = z
            · subst hxy; subst hyz; simp; omega
            · subst hxy; simp [hyz]
            · subst hyz; simp [hxy]
            · simp [hxy, hyz]
  · intro a; rfl
  · intro a b c d hab hac
    cases a with
    | borrowed => cases hab; cases hac; rfl
    | shared n x =>
      cases b with
      | borrowed =>
        cases c with
        | borrowed => rfl
        | shared k z =>
          cases n <;> cases k <;> simp [cellSumAlg, cellSumOp] at hab hac
          subst hab; simp at hac; omega
      | shared m y =>
        cases c with
        | borrowed =>
          cases n <;> cases m <;> simp [cellSumAlg, cellSumOp] at hab hac
          subst hac; simp at hab; omega
        | shared k z =>
          cases n <;> cases m <;> cases k <;> simp [cellSumAlg, cellSumOp] at hab hac
          obtain ⟨rfl, rfl⟩ := hab
          obtain ⟨rfl, h⟩ := hac
          simp only [Cell.shared.injEq] at h
          congr 1; omega
  · intro a b h
    cases a with
    | borrowed => rfl
    | shared n x =>
      cases b with
      | borrowed => simp [cellSumAlg, cellSumOp] at h
      | shared m y =>
        cases n <;> cases m <;> simp [cellSumAlg, cellSumOp] at h
  · intro a b
    cases a with
    | borrowed => cases b <;> simp [PartialAlg.Compat, cellSumAlg, cellSumOp, compat]
    | shared n x =>
      cases b with
      | borrowed => simp [PartialAlg.Compat, cellSumAlg, cellSumOp, compat]
      | shared m y =>
        cases n <;> cases m <;> simp [PartialAlg.Compat, cellSumAlg, cellSumOp, compat]

/-- Non-vacuity illustration for `cellSumAlg_isPCM_cancel_positive_compat_iff`:
the algebra has non-trivial defined and undefined composites matching
`Cell.compat`. -/
theorem cellSumAlg_compat_examples :
    (cellSumAlg Nat).Compat (.shared 1 7) (.shared 2 7) ∧ compat (Cell.shared 1 7) (.shared 2 7) = true ∧
      ¬ (cellSumAlg Nat).Compat (.shared 0 7) (.shared 1 7) ∧
      compat (Cell.shared 0 7) (.shared 1 7) = false := by
  decide

/-- An idempotent alternative to the depth-sum algebra: `borrowed` is the unit,
two readers with the same payload compose to a depth-1 reader (depths are not
added), and all other pairs are undefined. Its definedness relation is exactly
`Cell.compat`, but it is not cancellative. -/
def cellAgreeOp {V : Type} [DecidableEq V] : Cell V → Cell V → Option (Cell V)
  | .borrowed, c => some c
  | c, .borrowed => some c
  | .shared (_ + 1) x, .shared (_ + 1) y => if x = y then some (.shared 1 x) else none
  | _, _ => none

/-- The idempotent reader-join algebra on cells, with unit `borrowed`. -/
def cellAgreeAlg (V : Type) [DecidableEq V] : PartialAlg (Cell V) where
  op := cellAgreeOp
  unit := .borrowed

/-- **Cancellativity is a choice, not forced by the compatibility relation.**
The idempotent reader-join algebra is commutative and has `borrowed` as unit,
two cells have a defined composite in it iff they are compatible in the sense of
`Cell.compat`, and it is not cancellative (`shared 1 7 · shared 1 7 =
shared 1 7 = shared 1 7 · borrowed`). -/
theorem cellAgreeAlg_comm_unit_compat_iff_not_cancel :
    (∀ (V : Type) [DecidableEq V], (cellAgreeAlg V).Comm ∧ (cellAgreeAlg V).UnitLeft ∧
      ∀ a b : Cell V, (cellAgreeAlg V).Compat a b ↔ compat a b = true) ∧
    ¬ (cellAgreeAlg Nat).Cancel := by
  refine ⟨fun V _ => ⟨?_, fun a => rfl, ?_⟩, ?_⟩
  · intro a b
    cases a with
    | borrowed => cases b <;> rfl
    | shared n x =>
      cases b with
      | borrowed => rfl
      | shared m y =>
        cases n <;> cases m <;> simp [cellAgreeAlg, cellAgreeOp]
        by_cases hxy : x = y
        · subst hxy; simp
        · have hyx : y ≠ x := fun e => hxy e.symm
          simp [hxy, hyx]
  · intro a b
    cases a with
    | borrowed => cases b <;> simp [PartialAlg.Compat, cellAgreeAlg, cellAgreeOp, compat]
    | shared n x =>
      cases b with
      | borrowed => simp [PartialAlg.Compat, cellAgreeAlg, cellAgreeOp, compat]
      | shared m y =>
        cases n <;> cases m <;> simp [PartialAlg.Compat, cellAgreeAlg, cellAgreeOp, compat]
  · intro h
    have := h (.shared 1 7) (.shared 1 7) .borrowed (.shared 1 7) (by decide) (by decide)
    cases this

/-- **No partial algebra with the design's exclusivity and sharing behaviour
makes the exclusivity-restoring steps frame-preserving.** Let `A` be any partial
algebra on any carrier `M` and `e` any interpretation of cells in it. If (i) two
depth-1 readers with payload `v` are compatible, (ii) a depth-0 writer with
payload `v` is incompatible with a depth-1 reader with payload `v`, and (iii)
`borrowed` is compatible with a depth-1 reader with payload `v` (all after
interpretation by `e`), then neither the last end-share
`e(shared 1 v) ⇝ e(shared 0 v)` nor the end-borrow `e(borrowed) ⇝ e(shared 0 v)`
is a frame-preserving update. (Conjunct 1 uses (i) and (ii); conjunct 2 uses
(ii) and (iii).) -/
theorem restoring_steps_not_framePreserving_of_sharing_exclusion_neutral {M V : Type}
    (A : PartialAlg M) (e : Cell V → M) (v : V)
    (h_readers : A.Compat (e (.shared 1 v)) (e (.shared 1 v)))
    (h_excl : ¬ A.Compat (e (.shared 0 v)) (e (.shared 1 v)))
    (h_neutral : A.Compat (e .borrowed) (e (.shared 1 v))) :
    ¬ A.FramePreserving (e (.shared 1 v)) (e (.shared 0 v)) ∧
      ¬ A.FramePreserving (e .borrowed) (e (.shared 0 v)) :=
  ⟨fun h => h_excl (h _ h_readers), fun h => h_excl (h _ h_neutral)⟩

/-- `h_neutral` is automatic in unital algebras that interpret `borrowed` as the
unit: then `e(borrowed)` is compatible with everything. It is kept as a
hypothesis because `restoring_steps_not_framePreserving_of_sharing_exclusion_neutral`
does not assume the unit law. -/
theorem h_neutral_of_unitLeft {M V : Type} (A : PartialAlg M) (e : Cell V → M)
    (hunit : A.UnitLeft) (hb : e .borrowed = A.unit) (x : M) : A.Compat (e .borrowed) x := by
  rw [hb]; simp [PartialAlg.Compat, hunit x]

/-- Non-vacuity of `restoring_steps_not_framePreserving_of_sharing_exclusion_neutral`:
the depth-sum algebra with `e = id` and `v = 7` satisfies all three
hypotheses. -/
theorem restoring_steps_not_framePreserving_nonvacuous :
    (cellSumAlg Nat).Compat (id (.shared 1 7)) (id (.shared 1 7)) ∧
      ¬ (cellSumAlg Nat).Compat (id (.shared 0 7)) (id (.shared 1 7)) ∧
      (cellSumAlg Nat).Compat (id .borrowed) (id (.shared 1 7)) := by
  decide

/-- Variant algebra in which no two views may hold non-borrowed contributions
at the same address: the composite is defined only when one side is
`borrowed`. (A single-holder regime, as in a counting design where all readers
go through one source.) -/
def singleHolderAlg (V : Type) : PartialAlg (Cell V) where
  op
    | .borrowed, c => some c
    | c, .borrowed => some c
    | _, _ => none
  unit := .borrowed

/-- **Positive control** for
`restoring_steps_not_framePreserving_of_sharing_exclusion_neutral` and tightness
of `h_readers` (canonical form, `e = id`, `v = 7`): in the single-holder
algebra, hypotheses (ii) and (iii) hold, (i) fails, and the last end-share
`shared 1 7 ⇝ shared 0 7` *is* frame-preserving, so the conclusion fails. The
end-borrow is still not frame-preserving there: the single-holder regime rescues
only the last end-share. -/
theorem singleHolderAlg_last_endShare_framePreserving :
    ¬ (singleHolderAlg Nat).Compat (id (.shared 1 7)) (id (.shared 1 7)) ∧
      ¬ (singleHolderAlg Nat).Compat (id (.shared 0 7)) (id (.shared 1 7)) ∧
      (singleHolderAlg Nat).Compat (id .borrowed) (id (.shared 1 7)) ∧
      (singleHolderAlg Nat).FramePreserving (id (.shared 1 7)) (id (.shared 0 7)) ∧
      ¬ (singleHolderAlg Nat).FramePreserving (id .borrowed) (id (.shared 0 7)) := by
  refine ⟨by decide, by decide, by decide, fun f hf => ?_, fun h => ?_⟩
  · cases f with
    | borrowed => rfl
    | shared _ _ => simp [PartialAlg.Compat, singleHolderAlg] at hf
  · have := h (.shared 0 7) rfl
    simp [PartialAlg.Compat, singleHolderAlg] at this

/-- An artificial algebra with two compatibility classes: `borrowed` and writers
are all mutually compatible, readers with equal payload are mutually compatible,
and nothing else is. It does not satisfy the unit law (`borrowed` is not a unit
for readers). Used only as a tightness witness. -/
def twoClassAlg : PartialAlg (Cell Nat) where
  op
    | .borrowed, .borrowed => some .borrowed
    | .borrowed, .shared 0 _ => some .borrowed
    | .shared 0 _, .borrowed => some .borrowed
    | .shared 0 _, .shared 0 _ => some .borrowed
    | .shared (_ + 1) x, .shared (_ + 1) y => if x = y then some .borrowed else none
    | _, _ => none
  unit := .borrowed

/-- Tightness of `h_neutral` in
`restoring_steps_not_framePreserving_of_sharing_exclusion_neutral` (canonical
form, `e = id`, `v = 7`): in `twoClassAlg`, (i) and (ii) hold, (iii) fails, and
the end-borrow `borrowed ⇝ shared 0 7` is frame-preserving (so the conclusion
fails). `twoClassAlg` is not unital; by `h_neutral_of_unitLeft`, no unital
algebra interpreting `borrowed` as its unit can drop (iii). -/
theorem twoClassAlg_endBorrow_framePreserving :
    twoClassAlg.Compat (id (.shared 1 7)) (id (.shared 1 7)) ∧
      ¬ twoClassAlg.Compat (id (.shared 0 7)) (id (.shared 1 7)) ∧
      ¬ twoClassAlg.Compat (id .borrowed) (id (.shared 1 7)) ∧
      twoClassAlg.FramePreserving (id .borrowed) (id (.shared 0 7)) ∧ ¬ twoClassAlg.UnitLeft := by
  refine ⟨by decide, by decide, by decide, fun f hf => ?_, fun h => ?_⟩
  · cases f with
    | borrowed => rfl
    | shared d y =>
      cases d with
      | zero => rfl
      | succ d => simp [PartialAlg.Compat, twoClassAlg] at hf
  · have := h (.shared 1 7); simp [twoClassAlg] at this

/-- The algebra in which every composite is defined. -/
def allCompatAlg (V : Type) : PartialAlg (Cell V) where
  op _ _ := some .borrowed
  unit := .borrowed

/-- Tightness of `h_excl` in
`restoring_steps_not_framePreserving_of_sharing_exclusion_neutral` (canonical
form, `e = id`, `v = 7`): when every composite is defined, (i) and (iii) hold,
(ii) fails, and both updates are frame-preserving. -/
theorem allCompatAlg_restoring_steps_framePreserving :
    (allCompatAlg Nat).Compat (id (.shared 1 7)) (id (.shared 1 7)) ∧
      (allCompatAlg Nat).Compat (id .borrowed) (id (.shared 1 7)) ∧
      (allCompatAlg Nat).Compat (id (.shared 0 7)) (id (.shared 1 7)) ∧
      (allCompatAlg Nat).FramePreserving (id (.shared 1 7)) (id (.shared 0 7)) ∧
      (allCompatAlg Nat).FramePreserving (id .borrowed) (id (.shared 0 7)) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **In an associative partial algebra, a view's last share cannot be returned
by composing with a token while another reader may exist.** Let `A` be an
associative partial algebra (strong associativity `Assoc`; commutativity and
the unit law are not assumed), `e` an interpretation of cells in it, and `t` an
element standing for the one outstanding share of a depth-1 view. Suppose
(i) the state "two depth-1 views with payload `v`, and the outstanding share
`t`" is consistent, written with the two views composed first:
`(e(shared 1 v) · e(shared 1 v)) · t` is defined; (ii) absorbing the token turns
a depth-1 view into the depth-0 cell (`e(shared 1 v) · t = e(shared 0 v)`); and
(iii) a depth-1 reader cannot be composed with the depth-0 cell
(`e(shared 1 v) · e(shared 0 v)` is undefined). Then contradiction. A view's
own count reaching zero does not account for readers held through other
views. -/
theorem no_assoc_alg_returns_last_share_by_composition_beside_another_reader {M V : Type}
    (A : PartialAlg M) (hassoc : A.Assoc) (e : Cell V → M) (t : M) (v : V)
    (hstate : ((A.op (e (.shared 1 v)) (e (.shared 1 v))).bind fun x => A.op x t) ≠ none)
    (hret : A.op (e (.shared 1 v)) t = some (e (.shared 0 v)))
    (hexcl : ¬ A.Compat (e (.shared 1 v)) (e (.shared 0 v))) : False := by
  rw [hassoc, hret, Option.bind_some] at hstate
  exact hexcl (Option.isSome_iff_ne_none.mpr hstate)

/-- The same impossibility for partial commutative monoids, with the state
written as the composite of the list `[t, e(shared 1 v), e(shared 1 v)]` and
exclusion in the order `e(shared 0 v) · e(shared 1 v)`. Corollary of
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader`. -/
theorem no_pcm_returns_last_share_by_composition_beside_another_reader {M V : Type}
    (A : PartialAlg M) (hpcm : A.IsPCM) (e : Cell V → M) (t : M) (v : V)
    (hstate : A.opList [t, e (.shared 1 v), e (.shared 1 v)] ≠ none)
    (hret : A.op (e (.shared 1 v)) t = some (e (.shared 0 v)))
    (hexcl : ¬ A.Compat (e (.shared 0 v)) (e (.shared 1 v))) : False := by
  obtain ⟨hcomm, hassoc, hunit⟩ := hpcm
  have hunitR : ∀ x, A.op x A.unit = some x := fun x => (hcomm x A.unit).trans (hunit x)
  refine no_assoc_alg_returns_last_share_by_composition_beside_another_reader A hassoc e t v
    ?_ hret ?_
  · simp only [PartialAlg.opList, Option.bind_some, hunitR] at hstate
    rw [show (A.op (e (.shared 1 v)) (e (.shared 1 v))).bind (A.op t) =
      (A.op (e (.shared 1 v)) (e (.shared 1 v))).bind (fun x => A.op x t) from by
        congr 1; funext x; exact hcomm t x] at hstate
    exact hstate
  · intro h; apply hexcl; unfold PartialAlg.Compat at h ⊢; rw [hcomm]; exact h

/-- Carrier of small witness algebras: a unit `u`, a writer class `w`, a reader
class `r`, and a token `k`. -/
inductive Wit where
  | u | w | r | k
deriving DecidableEq, Repr

/-- Interpretation of cells in `Wit`: `borrowed ↦ u`, `shared 0 _ ↦ w`,
`shared (n+1) _ ↦ r`. -/
def Wit.ofCell {V : Type} : Cell V → Wit
  | .borrowed => .u
  | .shared 0 _ => .w
  | .shared (_ + 1) _ => .r

/-- Carrier of a five-element witness algebra: unit, depth-0, depth-1, depth-2
classes and a token. -/
inductive Wit5 where
  | u | s0 | s1 | s2 | tok
deriving DecidableEq, Repr

/-- Interpretation of cells in `Wit5` (payloads ignored; depths at least 2 are
identified). -/
def Wit5.ofCell {V : Type} : Cell V → Wit5
  | .borrowed => .u
  | .shared 0 _ => .s0
  | .shared 1 _ => .s1
  | .shared (_ + 2) _ => .s2

/-- A commutative, unital, non-associative algebra on `Wit5`: `s1·tok = s0`,
`s1·s1 = s2`, `s2·tok = s1` (and symmetric), all other non-unit composites
undefined. -/
def nonAssocDepthAlg : PartialAlg Wit5 where
  op
    | .u, x => some x
    | x, .u => some x
    | .s1, .tok => some .s0
    | .tok, .s1 => some .s0
    | .s1, .s1 => some .s2
    | .tok, .s2 => some .s1
    | .s2, .tok => some .s1
    | _, _ => none
  unit := .u

/-- Tightness of `hassoc` in
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader`
(canonical form): `nonAssocDepthAlg` with `e = Wit5.ofCell`, `t = tok`, `v = 7`
satisfies (i)–(iii) and is not associative (it is commutative and unital, so
the impossibility needs associativity even for commutative unital algebras). -/
theorem nonAssocDepthAlg_returns_last_share_beside_reader :
    ((nonAssocDepthAlg.op (Wit5.ofCell (Cell.shared 1 (7 : Nat))) (Wit5.ofCell (Cell.shared 1 (7 : Nat)))).bind
        fun x => nonAssocDepthAlg.op x .tok) ≠ none ∧
      nonAssocDepthAlg.op (Wit5.ofCell (Cell.shared 1 (7 : Nat))) .tok =
        some (Wit5.ofCell (Cell.shared 0 (7 : Nat))) ∧
      ¬ nonAssocDepthAlg.Compat (Wit5.ofCell (Cell.shared 1 (7 : Nat))) (Wit5.ofCell (Cell.shared 0 (7 : Nat))) ∧
      ¬ nonAssocDepthAlg.Assoc ∧ nonAssocDepthAlg.Comm ∧ nonAssocDepthAlg.UnitLeft := by
  refine ⟨by decide, rfl, by decide, fun h => ?_, ?_, ?_⟩
  · have := h .s1 .s1 .tok; simp [nonAssocDepthAlg] at this
  · intro a b; cases a <;> cases b <;> rfl
  · intro a; cases a <;> rfl

/-- The writer-exclusive, reader-agreement algebra on `Wit`: `u` is the unit,
`r·r = r`, every other non-unit composite is undefined. -/
def exclAgreeAlg : PartialAlg Wit where
  op
    | .u, x => some x
    | x, .u => some x
    | .r, .r => some .r
    | _, _ => none
  unit := .u

/-- Tightness of `hret` in
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader`
(canonical form): `exclAgreeAlg` with `e = Wit.ofCell`, the unit as token and
`v = 7` is associative, satisfies (i) and (iii), and absorbing the token does not
yield the depth-0 cell. -/
theorem exclAgreeAlg_unit_token_does_not_restore :
    exclAgreeAlg.Assoc ∧
      ((exclAgreeAlg.op (Wit.ofCell (Cell.shared 1 (7 : Nat))) (Wit.ofCell (Cell.shared 1 (7 : Nat)))).bind
        fun x => exclAgreeAlg.op x .u) ≠ none ∧
      exclAgreeAlg.op (Wit.ofCell (Cell.shared 1 (7 : Nat))) .u ≠ some (Wit.ofCell (Cell.shared 0 (7 : Nat))) ∧
      ¬ exclAgreeAlg.Compat (Wit.ofCell (Cell.shared 1 (7 : Nat))) (Wit.ofCell (Cell.shared 0 (7 : Nat))) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-- The algebra in which every composite is the depth-0 cell with payload `7`. -/
def allZeroAlg : PartialAlg (Cell Nat) where
  op _ _ := some (.shared 0 7)
  unit := .borrowed

/-- Tightness of `hexcl` in
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader`
(canonical form): `allZeroAlg` with `e = id`, `t = borrowed`, `v = 7` is
associative and satisfies (i) and (ii), but a depth-1 reader composes with the
depth-0 cell. -/
theorem allZeroAlg_return_beside_reader :
    allZeroAlg.Assoc ∧
      ((allZeroAlg.op (id (.shared 1 7)) (id (.shared 1 7))).bind fun x => allZeroAlg.op x .borrowed) ≠ none ∧
      allZeroAlg.op (id (.shared 1 7)) .borrowed = some (id (.shared 0 7)) ∧
      allZeroAlg.Compat (id (.shared 1 7)) (id (.shared 0 7)) :=
  ⟨fun _ _ _ => rfl, by decide, rfl, rfl⟩

/-- A single-reader token algebra on `Wit`: `u` is the unit, a reader absorbs
the token and becomes the writer (`r·k = k·r = w`), and every other non-unit
composite is undefined (in particular two readers cannot coexist). -/
def tokenReturnAlg : PartialAlg Wit where
  op
    | .u, x => some x
    | x, .u => some x
    | .r, .k => some .w
    | .k, .r => some .w
    | _, _ => none
  unit := .u

/-- **Positive control** for
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader` and
tightness of `hstate` (canonical form): `tokenReturnAlg` with `e = Wit.ofCell`,
`t = k`, `v = 7` is a partial commutative monoid in which absorbing the token
does turn a depth-1 view into the depth-0 cell and a depth-1 reader is excluded
by the depth-0 cell; this is consistent exactly because two depth-1 readers
cannot coexist there, so (i) fails. -/
theorem tokenReturnAlg_returns_last_share_without_second_reader :
    tokenReturnAlg.Assoc ∧ tokenReturnAlg.Comm ∧ tokenReturnAlg.UnitLeft ∧
      ((tokenReturnAlg.op (Wit.ofCell (Cell.shared 1 (7 : Nat))) (Wit.ofCell (Cell.shared 1 (7 : Nat)))).bind
        fun x => tokenReturnAlg.op x .k) = none ∧
      tokenReturnAlg.op (Wit.ofCell (Cell.shared 1 (7 : Nat))) .k = some (Wit.ofCell (Cell.shared 0 (7 : Nat))) ∧
      ¬ tokenReturnAlg.Compat (Wit.ofCell (Cell.shared 1 (7 : Nat))) (Wit.ofCell (Cell.shared 0 (7 : Nat))) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, by decide⟩
  · intro a b c; cases a <;> cases b <;> cases c <;> rfl
  · intro a b; cases a <;> cases b <;> rfl
  · intro a; cases a <;> rfl

/-- Non-vacuity of the hypotheses of
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader`, taken
separately: (i) and the exclusion (iii) hold together in the depth-sum algebra
(with `e = id` and the unit as `t`), and (ii) and (iii) hold together in
`tokenReturnAlg`. No algebra satisfies all of them, which is the content of the
theorem. -/
theorem no_assoc_alg_returns_last_share_hypotheses_satisfiable :
    ((cellSumOp (Cell.shared 1 (7 : Nat)) (.shared 1 7)).bind fun x => cellSumOp x .borrowed) ≠ none ∧
      cellSumOp (Cell.shared 1 (7 : Nat)) (.shared 0 7) = none ∧
      tokenReturnAlg.op (Wit.ofCell (Cell.shared 1 (7 : Nat))) .k = some (Wit.ofCell (Cell.shared 0 (7 : Nat))) := by
  decide

/-- **The depth-sum composite does not determine whether a view's last end-share
is enabled.** For every payload `v`, the configurations `[shared 2 v]` (one view
with two outstanding shares) and `[shared 1 v, shared 1 v]` (two views with one
each) have the same depth-sum composite `shared 2 v`, yet from the first the
view regains exclusivity by two enabled end-shares, while in the second neither
view's end-share is enabled. -/
theorem cellSumAlg_composite_does_not_determine_endShare_enabled {V : Type} [DecidableEq V]
    (v : V) :
    (cellSumAlg V).opList [.shared 2 v] = some (.shared 2 v) ∧
      (cellSumAlg V).opList [.shared 1 v, .shared 1 v] = some (.shared 2 v) ∧
      ((stepAt [Cell.shared 2 v] 0 .endShare).bind (fun cfg => stepAt cfg 0 .endShare)) =
        some [.shared 0 v] ∧
      stepAt [Cell.shared 1 v, .shared 1 v] 0 .endShare = none ∧
      stepAt [Cell.shared 1 v, .shared 1 v] 1 .endShare = none := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [PartialAlg.opList, cellSumAlg, cellSumOp]
  · simp [stepAt, CellStep.apply, Valid]
  · simp [stepAt, CellStep.apply, Valid, compat]
  · simp [stepAt, CellStep.apply, Valid, compat]

/-- Non-vacuity witness for
`cellSumAlg_composite_does_not_determine_endShare_enabled` at the inhabited
payload type `Nat` (payload `7`): `[shared 2 7]` and `[shared 1 7, shared 1 7]`
have the same depth-sum composite `shared 2 7`; from the first, two end-shares
reach `[shared 0 7]`; in the second, neither view's end-share is enabled. -/
theorem cellSumAlg_composite_does_not_determine_endShare_enabled_nat :
    (cellSumAlg Nat).opList [.shared 2 7] = some (.shared 2 7) ∧
      (cellSumAlg Nat).opList [.shared 1 7, .shared 1 7] = some (.shared 2 7) ∧
      ((stepAt [Cell.shared 2 (7 : Nat)] 0 .endShare).bind (fun cfg => stepAt cfg 0 .endShare)) =
        some [.shared 0 7] ∧
      stepAt [Cell.shared 1 (7 : Nat), .shared 1 7] 0 .endShare = none ∧
      stepAt [Cell.shared 1 (7 : Nat), .shared 1 7] 1 .endShare = none :=
  cellSumAlg_composite_does_not_determine_endShare_enabled (7 : Nat)

end Toy.Perm
