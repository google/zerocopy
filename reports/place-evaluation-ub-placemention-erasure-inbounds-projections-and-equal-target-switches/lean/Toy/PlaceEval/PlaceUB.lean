import Toy.PlaceEval.RunLemmas

/-!
# Exact UB conditions of place evaluation
-/

namespace Toy.PlaceEval

theorem evalProjs_append (st : State) :
    ∀ (πs ρs : List Proj) (q : Ptr),
      evalProjs st q (πs ++ ρs) = (evalProjs st q πs).bind fun r => evalProjs st r ρs
  | [], ρs, q => by simp [evalProjs]
  | π :: πs, ρs, q => by
    simp only [List.cons_append, evalProjs]
    cases projStep st q π with
    | none => rfl
    | some q' => simp only [Option.bind_some]; exact evalProjs_append st πs ρs q'

/-- A projection list fails exactly when some projection fails at the pointer reached by
the projections before it. -/
theorem evalProjs_eq_none_iff (st : State) :
    ∀ (πs : List Proj) (q : Ptr),
      evalProjs st q πs = none ↔
        ∃ i r π, evalProjs st q (πs.take i) = some r ∧ πs[i]? = some π ∧ projStep st r π = none
  | [], q => by simp [evalProjs]
  | π :: πs, q => by
    simp only [evalProjs]
    cases h : projStep st q π with
    | none =>
      simp only [Option.bind_none, true_iff]
      exact ⟨0, q, π, by simp [evalProjs], rfl, h⟩
    | some q' =>
      simp only [Option.bind_some]
      rw [evalProjs_eq_none_iff st πs q']
      constructor
      · rintro ⟨i, r, π', h1, h2, h3⟩
        refine ⟨i + 1, r, π', ?_, by simpa using h2, h3⟩
        simp only [List.take_succ_cons, evalProjs, h, Option.bind_some]
        exact h1
      · rintro ⟨i, r, π', h1, h2, h3⟩
        cases i with
        | zero =>
          simp only [List.take_zero, evalProjs, Option.some.injEq] at h1
          subst h1
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
          subst h2
          rw [h] at h3
          cases h3
        | succ i =>
          refine ⟨i, r, π', ?_, by simpa using h2, h3⟩
          simp only [List.take_succ_cons, evalProjs, h, Option.bind_some] at h1
          exact h1

/-- **`Deref` step.** The `Deref` projection fails exactly when its pointer load fails. -/
theorem projStep_deref_eq_none_iff (st : State) (q : Ptr) :
    projStep st q .deref = none ↔ ¬ DerefLoadOk st.mem q := by
  rw [← loadPtr_isSome_iff]
  simp [projStep]

/-- **`Field` step.** A field projection fails exactly when its offset is non-zero and the
range is not in bounds of a live allocation the pointer is derived from. -/
theorem projStep_field_eq_none_iff (st : State) (q : Ptr) (off : Nat) :
    projStep st q (.field off) = none ↔ off ≠ 0 ∧ st.mem.inBounds q off = false := by
  simp only [projStep, Mem.offsetInbounds]
  by_cases h0 : off = 0
  · subst h0; simp
  · by_cases hb : st.mem.inBounds q off = true
    · simp [h0, hb]
    · simp [h0, hb]

/-- **`Index` step.** An index projection fails exactly when reading the index local fails,
or the byte offset `n * sz` is non-zero and not in bounds. -/
theorem projStep_index_eq_none_iff (st : State) (q : Ptr) (j : Local) (sz : Nat) :
    projStep st q (.index j sz) = none ↔
      st.readIndex j = none ∨
        ∃ n, st.readIndex j = some n ∧ n * sz ≠ 0 ∧ st.mem.inBounds q (n * sz) = false := by
  simp only [projStep]
  cases h : st.readIndex j with
  | none => simp
  | some n =>
    simp only [Mem.offsetInbounds, reduceCtorEq, false_or, Option.some.injEq, exists_eq_left']
    by_cases h0 : n * sz = 0
    · simp [h0]
    · by_cases hb : st.mem.inBounds q (n * sz) = true
      · simp [h0, hb]
      · simp [h0, hb]

/-- **Exact UB conditions of place evaluation.** For every state `st` (reachable or not)
and place `p`, evaluating `p` is UB (`evalPlace st p = none`) iff
* (a) `st.basePtr p.base = none`: the frame has no allocation for the base local, or names
  an allocation index missing from the table (a frame entry naming a freed allocation still
  yields a pointer), or
* for some projection index `i`, the first `i` projections evaluate to a pointer `q` and
  projection `i`
  * (b) is a `deref` whose pointer load at `q` fails (`¬ DerefLoadOk`: not dereferenceable
    for `ptrSize` bytes, misaligned for `ptrAlign`, or not holding a pointer value), or
  * (c) is a `field off` with `off ≠ 0` whose range is not in bounds of a live allocation
    that `q` is derived from, or
  * (d) is an `index j sz` whose index-local read fails, or
  * (e) is an `index j sz` whose index value `n` gives a non-zero offset `n * sz` that is
    not in bounds.

Degenerate edges: a zero offset (`off = 0`, or `n = 0` or `sz = 0` for `index`) is never
checked, even for a null or dangling `q`. No condition mentions the pointer that evaluation
finally produces. -/
theorem evalPlace_eq_none_iff (st : State) (p : Place) :
    evalPlace st p = none ↔
      st.basePtr p.base = none ∨
      ∃ i q, evalPrefix st p i = some q ∧
        ((p.proj[i]? = some .deref ∧ ¬ DerefLoadOk st.mem q) ∨
         (∃ off, p.proj[i]? = some (.field off) ∧ off ≠ 0 ∧ st.mem.inBounds q off = false) ∨
         (∃ j sz, p.proj[i]? = some (.index j sz) ∧ st.readIndex j = none) ∨
         (∃ j sz n, p.proj[i]? = some (.index j sz) ∧ st.readIndex j = some n ∧
            n * sz ≠ 0 ∧ st.mem.inBounds q (n * sz) = false)) := by
  unfold evalPlace evalPrefix
  cases hb : st.basePtr p.base with
  | none => simp
  | some q0 =>
    simp only [Option.bind_some, reduceCtorEq, false_or]
    rw [evalProjs_eq_none_iff]
    constructor
    · rintro ⟨i, r, π, h1, h2, h3⟩
      refine ⟨i, r, h1, ?_⟩
      cases π with
      | deref => exact Or.inl ⟨h2, (projStep_deref_eq_none_iff st r).1 h3⟩
      | field off =>
        exact Or.inr (Or.inl ⟨off, h2, (projStep_field_eq_none_iff st r off).1 h3⟩)
      | index j sz =>
        rcases (projStep_index_eq_none_iff st r j sz).1 h3 with h | ⟨n, hn, h0, hin⟩
        · exact Or.inr (Or.inr (Or.inl ⟨j, sz, h2, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨j, sz, n, h2, hn, h0, hin⟩))
    · rintro ⟨i, r, h1, h⟩
      rcases h with ⟨h2, h3⟩ | ⟨off, h2, h3⟩ | ⟨j, sz, h2, h3⟩ | ⟨j, sz, n, h2, h3, h4, h5⟩
      · exact ⟨i, r, .deref, h1, h2, (projStep_deref_eq_none_iff st r).2 h3⟩
      · exact ⟨i, r, .field off, h1, h2, (projStep_field_eq_none_iff st r off).2 h3⟩
      · exact ⟨i, r, .index j sz, h1, h2, (projStep_index_eq_none_iff st r j sz).2 (Or.inl h3)⟩
      · exact ⟨i, r, .index j sz, h1, h2,
          (projStep_index_eq_none_iff st r j sz).2 (Or.inr ⟨n, h3, h4, h5⟩)⟩

theorem evalProjs_replicate_field_zero (st : State) :
    ∀ (k : Nat) (r : Ptr), evalProjs st r (List.replicate k (.field 0)) = some r
  | 0, r => rfl
  | k + 1, r => by
    simp only [List.replicate_succ, evalProjs, projStep, Mem.offsetInbounds]
    simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, Option.bind_some]
    have : r.offset 0 = r := by simp [Ptr.offset]
    rw [this]
    exact evalProjs_replicate_field_zero st k r

/-- **The final pointee is never inspected.** A place ending in `deref` followed by any
number of zero-offset field projections evaluates to exactly the loaded pointer, with no
condition on that pointer (it may be null, dangling, freed, misaligned, or point to
uninitialized memory). -/
theorem evalPlace_deref_zeroFields (st : State) (x : Local) (pre : List Proj) (k : Nat) :
    evalPlace st ⟨x, pre ++ .deref :: List.replicate k (.field 0)⟩ =
      (evalPlace st ⟨x, pre⟩).bind st.mem.loadPtr := by
  unfold evalPlace
  simp only
  cases st.basePtr x with
  | none => rfl
  | some q =>
    simp only [Option.bind_some]
    rw [evalProjs_append]
    cases evalProjs st q pre with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, evalProjs, projStep]
      cases st.mem.loadPtr r with
      | none => rfl
      | some r' => simp only [Option.bind_some]; exact evalProjs_replicate_field_zero st k r'

/-- Corollary of `evalPlace_deref_zeroFields`: a place `pre ++ [deref]` evaluates iff
`pre` evaluates to some `q` at which the pointer load succeeds; the loaded pointer itself
is unconstrained. -/
theorem evalPlace_append_deref_isSome_iff (st : State) (x : Local) (pre : List Proj) :
    (evalPlace st ⟨x, pre ++ [.deref]⟩).isSome = true ↔
      ∃ q, evalPlace st ⟨x, pre⟩ = some q ∧ DerefLoadOk st.mem q := by
  have h := evalPlace_deref_zeroFields st x pre 0
  simp only [List.replicate_zero] at h
  rw [h]
  cases evalPlace st ⟨x, pre⟩ with
  | none => simp
  | some q => simp [loadPtr_isSome_iff]

end Toy.PlaceEval
