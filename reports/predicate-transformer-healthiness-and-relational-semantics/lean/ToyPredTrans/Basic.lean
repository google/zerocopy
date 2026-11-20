import ToyPredTrans.Defs

/-!
# Basic facts: implications between the laws, and the laws satisfied by `wlp` and `wp`

Everything in this file is fully proved.  These lemmas justify which laws are *derivable*
from others (and therefore never appear as separate hypotheses of the main results):

`ConjAll → ConjNonempty → ConjBin → Monotone`, and `ConjAll ↔ ConjNonempty ∧ TopPreserving`;
`DirContinuous → OmegaContinuous`; `CountableState → ContinuumState`.
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-! ## Extensionality -/

/-- Predicates that hold of the same states are equal (`propext` + `funext`). -/
theorem pred_ext {P Q : Pred σ} (h : ∀ s, P s ↔ Q s) : P = Q :=
  funext fun s => propext (h s)

/-- Transformers that agree pointwise are equal. -/
theorem trans_ext {T U : Transformer σ} (h : ∀ Q s, T Q s ↔ U Q s) : T = U :=
  funext fun Q => funext fun s => propext (h Q s)

/-- Relations that agree pointwise are equal. -/
theorem rel_ext {R R' : Rel σ} (h : ∀ s s', R s s' ↔ R' s s') : R = R' :=
  funext fun s => funext fun s' => propext (h s s')

/-! ## Equational forms of the pointwise laws

The laws in `Defs` are stated pointwise.  Each is equivalent to the familiar equation between
predicates. -/

/-- `Strict T` is the equation `T False = False`. -/
theorem strict_iff_eq (T : Transformer σ) :
    Strict T ↔ T (fun _ => False) = fun _ => False := by
  constructor
  · intro h
    exact pred_ext fun s => ⟨fun hs => h s hs, False.elim⟩
  · intro h s hs
    rw [h] at hs
    exact hs

/-- `TopPreserving T` is the equation `T True = True`. -/
theorem topPreserving_iff_eq (T : Transformer σ) :
    TopPreserving T ↔ T (fun _ => True) = fun _ => True := by
  constructor
  · intro h
    exact pred_ext fun s => ⟨fun _ => trivial, fun _ => h s⟩
  · intro h s
    rw [h]
    trivial

/-- `ConjBin T` is the equation `T (P ∧ Q) = T P ∧ T Q`. -/
theorem conjBin_iff_eq (T : Transformer σ) :
    ConjBin T ↔ ∀ P Q : Pred σ, T (fun t => P t ∧ Q t) = fun s => T P s ∧ T Q s := by
  constructor
  · intro h P Q
    exact pred_ext fun s => h P Q s
  · intro h P Q s
    rw [h P Q]

/-- `ConjAll T` is the equation `T (⋂ᵢ Q i) = ⋂ᵢ T (Q i)` for every family. -/
theorem conjAll_iff_eq (T : Transformer σ) :
    ConjAll T ↔ ∀ (ι : Type u) (Q : ι → Pred σ),
      T (fun t => ∀ i, Q i t) = fun s => ∀ i, T (Q i) s := by
  constructor
  · intro h ι Q
    exact pred_ext fun s => h ι Q s
  · intro h ι Q s
    rw [h ι Q]

/-- Universal conjunctivity over indexed families is the same as distributing over the
intersection of an arbitrary *set* of predicates. -/
theorem conjAll_iff_set (T : Transformer σ) :
    ConjAll T ↔ ∀ (F : Pred σ → Prop) (s : σ),
      T (fun t => ∀ Q, F Q → Q t) s ↔ ∀ Q, F Q → T Q s := by
  constructor
  · intro h F s
    have key := h { Q : Pred σ // F Q } (fun i => i.1) s
    have hEq : (fun t => ∀ i : { Q : Pred σ // F Q }, i.1 t) = fun t => ∀ Q, F Q → Q t :=
      pred_ext fun t => ⟨fun hh Q hQ => hh ⟨Q, hQ⟩, fun hh i => hh i.1 i.2⟩
    rw [hEq] at key
    exact ⟨fun hT Q hQ => key.mp hT ⟨Q, hQ⟩, fun hh => key.mpr fun i => hh i.1 i.2⟩
  · intro h ι Q s
    have key := h (fun P => ∃ i, P = Q i) s
    have hEq : (fun t => ∀ P, (∃ i, P = Q i) → P t) = fun t => ∀ i, Q i t :=
      pred_ext fun t =>
        ⟨fun hh i => hh (Q i) ⟨i, rfl⟩, fun hh P hP => by
          obtain ⟨i, rfl⟩ := hP
          exact hh i⟩
    rw [hEq] at key
    exact ⟨fun hT i => key.mp hT (Q i) ⟨i, rfl⟩, fun hh => key.mpr fun P hP => by
      obtain ⟨i, rfl⟩ := hP
      exact hh i⟩

/-- Positive conjunctivity over indexed families is the same as distributing over the
intersection of an arbitrary *nonempty set* of predicates. -/
theorem conjNonempty_iff_set (T : Transformer σ) :
    ConjNonempty T ↔ ∀ (F : Pred σ → Prop), (∃ Q, F Q) → ∀ (s : σ),
      T (fun t => ∀ Q, F Q → Q t) s ↔ ∀ Q, F Q → T Q s := by
  constructor
  · intro h F hF s
    obtain ⟨Q₀, hQ₀⟩ := hF
    have key := h { Q : Pred σ // F Q } (fun i => i.1) ⟨⟨Q₀, hQ₀⟩⟩ s
    have hEq : (fun t => ∀ i : { Q : Pred σ // F Q }, i.1 t) = fun t => ∀ Q, F Q → Q t :=
      pred_ext fun t => ⟨fun hh Q hQ => hh ⟨Q, hQ⟩, fun hh i => hh i.1 i.2⟩
    rw [hEq] at key
    exact ⟨fun hT Q hQ => key.mp hT ⟨Q, hQ⟩, fun hh => key.mpr fun i => hh i.1 i.2⟩
  · intro h ι Q hι s
    obtain ⟨i₀⟩ := hι
    have key := h (fun P => ∃ i, P = Q i) ⟨Q i₀, i₀, rfl⟩ s
    have hEq : (fun t => ∀ P, (∃ i, P = Q i) → P t) = fun t => ∀ i, Q i t :=
      pred_ext fun t =>
        ⟨fun hh i => hh (Q i) ⟨i, rfl⟩, fun hh P hP => by
          obtain ⟨i, rfl⟩ := hP
          exact hh i⟩
    rw [hEq] at key
    exact ⟨fun hT i => key.mp hT (Q i) ⟨i, rfl⟩, fun hh => key.mpr fun P hP => by
      obtain ⟨i, rfl⟩ := hP
      exact hh i⟩

/-- `ConjAll` (stated for index types in the universe of `σ`) gives conjunctivity over
families indexed by any `Sort`. -/
theorem conjAll_arbitrary_sort.{v} {T : Transformer σ} (h : ConjAll T)
    (ι : Sort v) (Q : ι → Pred σ) (s : σ) :
    T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s := by
  have hset := (conjAll_iff_set T).mp h (fun P => ∃ i : ι, P = Q i) s
  have hEq : (fun t => ∀ P, (∃ i : ι, P = Q i) → P t) = fun t => ∀ i, Q i t :=
    pred_ext fun t =>
      ⟨fun hh i => hh (Q i) ⟨i, rfl⟩, fun hh P hP => by
        obtain ⟨i, rfl⟩ := hP
        exact hh i⟩
  rw [hEq] at hset
  exact ⟨fun hT i => hset.mp hT (Q i) ⟨i, rfl⟩, fun hh => hset.mpr fun P hP => by
    obtain ⟨i, rfl⟩ := hP
    exact hh i⟩

/-- `ConjNonempty` (stated for index types in the universe of `σ`) gives conjunctivity over
nonempty families indexed by any `Sort`. -/
theorem conjNonempty_arbitrary_sort.{v} {T : Transformer σ} (h : ConjNonempty T)
    (ι : Sort v) (Q : ι → Pred σ) (hι : Nonempty ι) (s : σ) :
    T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s := by
  obtain ⟨i₀⟩ := hι
  have hset := (conjNonempty_iff_set T).mp h (fun P => ∃ i : ι, P = Q i) ⟨Q i₀, i₀, rfl⟩ s
  have hEq : (fun t => ∀ P, (∃ i : ι, P = Q i) → P t) = fun t => ∀ i, Q i t :=
    pred_ext fun t =>
      ⟨fun hh i => hh (Q i) ⟨i, rfl⟩, fun hh P hP => by
        obtain ⟨i, rfl⟩ := hP
        exact hh i⟩
  rw [hEq] at hset
  exact ⟨fun hT i => hset.mp hT (Q i) ⟨i, rfl⟩, fun hh => hset.mpr fun P hP => by
    obtain ⟨i, rfl⟩ := hP
    exact hh i⟩

/-! ## Implications between the laws -/

/-- Binary conjunctivity implies monotonicity. -/
theorem monotone_of_conjBin {T : Transformer σ} (h : ConjBin T) : Monotone T := by
  intro P Q hPQ s hP
  have hEq : (fun t => P t ∧ Q t) = P :=
    pred_ext fun t => ⟨fun hp => hp.1, fun hp => ⟨hp, hPQ t hp⟩⟩
  have hP' : T (fun t => P t ∧ Q t) s := by
    rw [hEq]
    exact hP
  exact ((h P Q s).mp hP').2

/-- Positive conjunctivity implies binary conjunctivity (use a two-element index type). -/
theorem conjBin_of_conjNonempty {T : Transformer σ} (h : ConjNonempty T) : ConjBin T := by
  intro P Q s
  have key := h (ULift.{u} Bool) (fun b => cond b.down P Q) ⟨⟨true⟩⟩ s
  have hEq : (fun t => ∀ i : ULift.{u} Bool, (cond i.down P Q) t) = fun t => P t ∧ Q t :=
    pred_ext fun t =>
      ⟨fun hh => ⟨hh ⟨true⟩, hh ⟨false⟩⟩, fun hh i => by
        obtain ⟨b⟩ := i
        cases b
        · exact hh.2
        · exact hh.1⟩
  rw [hEq] at key
  constructor
  · intro hT
    exact ⟨key.mp hT ⟨true⟩, key.mp hT ⟨false⟩⟩
  · intro hh
    refine key.mpr fun i => ?_
    obtain ⟨b⟩ := i
    cases b
    · exact hh.2
    · exact hh.1

/-- Positive conjunctivity implies monotonicity. -/
theorem monotone_of_conjNonempty {T : Transformer σ} (h : ConjNonempty T) : Monotone T :=
  monotone_of_conjBin (conjBin_of_conjNonempty h)

/-- Universal conjunctivity implies positive conjunctivity. -/
theorem conjNonempty_of_conjAll {T : Transformer σ} (h : ConjAll T) : ConjNonempty T :=
  fun ι Q _ s => h ι Q s

/-- Universal conjunctivity implies top preservation (use the empty family). -/
theorem topPreserving_of_conjAll {T : Transformer σ} (h : ConjAll T) : TopPreserving T := by
  intro s
  have key := h PEmpty.{u + 1} (fun i => i.elim) s
  have hEq : (fun t : σ => ∀ i : PEmpty.{u + 1}, (i.elim : Pred σ) t) = fun _ => True :=
    pred_ext fun t => ⟨fun _ => trivial, fun _ i => i.elim⟩
  rw [hEq] at key
  exact key.mpr fun i => i.elim

/-- Universal conjunctivity is exactly positive conjunctivity plus top preservation.  The
empty family is the only difference between `ConjAll` and `ConjNonempty`. -/
theorem conjAll_iff_conjNonempty_and_topPreserving (T : Transformer σ) :
    ConjAll T ↔ ConjNonempty T ∧ TopPreserving T := by
  constructor
  · intro h
    exact ⟨conjNonempty_of_conjAll h, topPreserving_of_conjAll h⟩
  · rintro ⟨hn, ht⟩ ι Q s
    by_cases hι : Nonempty ι
    · exact hn ι Q hι s
    · have hEq : (fun t => ∀ i, Q i t) = fun _ => True :=
        pred_ext fun t => ⟨fun _ => trivial, fun _ i => (hι ⟨i⟩).elim⟩
      rw [hEq]
      exact ⟨fun _ i => (hι ⟨i⟩).elim, fun _ => ht s⟩

/-- Binary conjunctivity plus top preservation gives conjunctivity over every finite list of
postconditions (including the empty list).  This is the precise sense in which `ConjBin` and
`TopPreserving` together are "all finitary conjunctivity laws". -/
theorem conjList_of_conjBin_of_topPreserving {T : Transformer σ} (hb : ConjBin T)
    (ht : TopPreserving T) (l : List (Pred σ)) (s : σ) :
    T (fun t => ∀ Q, Q ∈ l → Q t) s ↔ ∀ Q, Q ∈ l → T Q s := by
  induction l with
  | nil =>
    have hEq : (fun t : σ => ∀ Q : Pred σ, Q ∈ ([] : List (Pred σ)) → Q t) = fun _ => True :=
      pred_ext fun t => ⟨fun _ => trivial, fun _ Q hQ => (by cases hQ)⟩
    rw [hEq]
    exact ⟨fun _ Q hQ => (by cases hQ), fun _ => ht s⟩
  | cons P l ih =>
    have hEq : (fun t : σ => ∀ Q : Pred σ, Q ∈ P :: l → Q t)
        = fun t => P t ∧ ∀ Q, Q ∈ l → Q t :=
      pred_ext fun t =>
        ⟨fun hh => ⟨hh P (List.mem_cons_self), fun Q hQ => hh Q (List.mem_cons_of_mem _ hQ)⟩,
         fun hh Q hQ => by
          rcases List.mem_cons.mp hQ with rfl | hQ'
          · exact hh.1
          · exact hh.2 Q hQ'⟩
    rw [hEq, hb P (fun t => ∀ Q, Q ∈ l → Q t) s, ih]
    constructor
    · rintro ⟨hP, hl⟩ Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ'
      · exact hP
      · exact hl Q hQ'
    · intro hh
      exact ⟨hh P (List.mem_cons_self), fun Q hQ => hh Q (List.mem_cons_of_mem _ hQ)⟩

/-- A chain is increasing along `≤`, not only along successor. -/
theorem Chain.mono {Q : Nat → Pred σ} (hQ : Chain Q) {n m : Nat} (hnm : n ≤ m) (s : σ) :
    Q n s → Q m s := by
  induction hnm with
  | refl => exact id
  | step _ ih => exact fun h => hQ _ s (ih h)

/-- The two-sided continuity equation over chains is equivalent to monotonicity together with
the one-sided law `OmegaContinuous`. -/
theorem omegaContinuous_two_sided_iff (T : Transformer σ) :
    (∀ Q : Nat → Pred σ, Chain Q → ∀ s, T (fun t => ∃ n, Q n t) s ↔ ∃ n, T (Q n) s)
      ↔ Monotone T ∧ OmegaContinuous T := by
  constructor
  · intro h
    refine ⟨?_, fun Q hQ s => (h Q hQ s).mp⟩
    intro P Q hPQ s hP
    let C : Nat → Pred σ := fun n => match n with
      | 0 => P
      | _ + 1 => Q
    have hC : Chain C := by
      intro n t hn
      cases n with
      | zero => exact hPQ t hn
      | succ n => exact hn
    have hEq : (fun t => ∃ n, C n t) = Q :=
      pred_ext fun t =>
        ⟨fun ⟨n, hn⟩ => by
          cases n with
          | zero => exact hPQ t hn
          | succ n => exact hn,
         fun hq => ⟨1, hq⟩⟩
    have := (h C hC s).mpr ⟨0, hP⟩
    rw [hEq] at this
    exact this
  · rintro ⟨hm, hc⟩ Q hQ s
    refine ⟨hc Q hQ s, ?_⟩
    rintro ⟨n, hn⟩
    exact hm (Q n) (fun t => ∃ n, Q n t) (fun t ht => ⟨n, ht⟩) s hn

/-- Continuity over directed families implies ω-continuity: an increasing chain is a
directed family. -/
theorem omegaContinuous_of_dirContinuous {T : Transformer σ} (h : DirContinuous T) :
    OmegaContinuous T := by
  intro Q hQ s hT
  have hdir : Directed (fun n : ULift.{u} Nat => Q n.down) := by
    refine ⟨⟨⟨0⟩⟩, fun i j => ⟨⟨i.down + j.down⟩, fun t ht => ?_, fun t ht => ?_⟩⟩
    · exact hQ.mono (Nat.le_add_right _ _) t ht
    · exact hQ.mono (Nat.le_add_left _ _) t ht
  have hEq : (fun t => ∃ i : ULift.{u} Nat, Q i.down t) = fun t => ∃ n, Q n t :=
    pred_ext fun t => ⟨fun ⟨i, hi⟩ => ⟨i.down, hi⟩, fun ⟨n, hn⟩ => ⟨⟨n⟩, hn⟩⟩
  have hT' : T (fun t => ∃ i : ULift.{u} Nat, Q i.down t) s := by
    rw [hEq]
    exact hT
  obtain ⟨i, hi⟩ := h _ _ hdir s hT'
  exact ⟨i.down, hi⟩

/-- Every countable state type has at most the cardinality of the continuum. -/
theorem continuumState_of_countableState (h : CountableState σ) : ContinuumState σ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun x k => decide (k = f x), fun x y hxy => hf x y ?_⟩
  have h1 : decide (f x = f x) = decide (f x = f y) := congrFun hxy (f x)
  have h2 : decide (f x = f y) = true := h1 ▸ decide_eq_true rfl
  exact of_decide_eq_true h2

/-! ## Laws satisfied by `wlp` and `wp` -/

/-- `wlp R` is `wp R` with the always-true termination predicate. -/
theorem wlp_eq_wp_true (R : Rel σ) : wlp R = wp R (fun _ => True) :=
  trans_ext fun _ _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

/-- Every `wlp` is universally conjunctive. -/
theorem conjAll_wlp (R : Rel σ) : ConjAll (wlp R) :=
  fun _ _ _ => ⟨fun h i s' hr => h s' hr i, fun h s' hr i => h i s' hr⟩

/-- Every `wp` is positively conjunctive. -/
theorem conjNonempty_wp (R : Rel σ) (term : Pred σ) : ConjNonempty (wp R term) := by
  intro ι Q hι s
  obtain ⟨i₀⟩ := hι
  exact ⟨fun h i => ⟨h.1, fun s' hr => h.2 s' hr i⟩,
    fun h => ⟨(h i₀).1, fun s' hr i => (h i).2 s' hr⟩⟩

/-- Every `wp` is binary conjunctive. -/
theorem conjBin_wp (R : Rel σ) (term : Pred σ) : ConjBin (wp R term) :=
  conjBin_of_conjNonempty (conjNonempty_wp R term)

/-- Every `wlp` is binary conjunctive. -/
theorem conjBin_wlp (R : Rel σ) : ConjBin (wlp R) :=
  conjBin_of_conjNonempty (conjNonempty_of_conjAll (conjAll_wlp R))

/-- Every `wp` is monotone. -/
theorem monotone_wp (R : Rel σ) (term : Pred σ) : Monotone (wp R term) :=
  fun _ _ hPQ _ h => ⟨h.1, fun s' hr => hPQ s' (h.2 s' hr)⟩

/-- Every `wlp` is monotone. -/
theorem monotone_wlp (R : Rel σ) : Monotone (wlp R) :=
  fun _ _ hPQ _ h s' hr => hPQ s' (h s' hr)

/-- Every `wlp` preserves top. -/
theorem topPreserving_wlp (R : Rel σ) : TopPreserving (wlp R) :=
  fun _ _ _ => trivial

/-- A `wp` preserves top exactly when its termination predicate holds everywhere. -/
theorem topPreserving_wp_iff (R : Rel σ) (term : Pred σ) :
    TopPreserving (wp R term) ↔ ∀ s, term s :=
  ⟨fun h s => (h s).1, fun h s => ⟨h s, fun _ _ => trivial⟩⟩

/-- The termination predicate is recovered from a `wp` by `termOf`. -/
theorem termOf_wp (R : Rel σ) (term : Pred σ) : termOf (wp R term) = term :=
  pred_ext fun _ => ⟨fun h => h.1, fun h => ⟨h, fun _ _ => trivial⟩⟩

/-- For a monotone transformer, the pair read off by `relOf` and `termOf` is in chaos normal
form. -/
theorem chaosNormal_relOf_termOf_of_monotone {T : Transformer σ} (h : Monotone T) :
    ChaosNormal (relOf T) (termOf T) :=
  fun s hs _ Q hT => (hs (h Q _ (fun _ _ => trivial) s hT)).elim

/-- For a monotone transformer, `relOf T s s'` (the intersection of all postconditions
established from `s`) holds exactly when `T` cannot guarantee from `s` that the final state
differs from `s'`: the two natural ways of reading a relation off a transformer agree.  The
backward direction uses excluded middle. -/
theorem relOf_iff_not_avoids_of_monotone {T : Transformer σ} (h : Monotone T) (s s' : σ) :
    relOf T s s' ↔ ¬ T (fun t => t ≠ s') s := by
  constructor
  · intro hk hT
    exact hk _ hT rfl
  · intro hr Q hQ
    apply Classical.byContradiction
    intro hq
    apply hr
    refine h Q _ ?_ s hQ
    intro t ht hts'
    rw [hts'] at ht
    exact hq ht

/-- Replacing `R` by its chaos normal form does not change `wp`. -/
theorem wp_chaos_eq (R : Rel σ) (term : Pred σ) :
    wp (fun s s' => term s → R s s') term = wp R term :=
  trans_ext fun _ _ =>
    ⟨fun h => ⟨h.1, fun s' hr => h.2 s' fun _ => hr⟩,
     fun h => ⟨h.1, fun s' hr => h.2 s' (hr h.1)⟩⟩

/-- The chaos normal form of any pair is in chaos normal form. -/
theorem chaosNormal_chaos (R : Rel σ) (term : Pred σ) :
    ChaosNormal (fun s s' => term s → R s s') term :=
  fun _ hs _ ht => (hs ht).elim

/-- Restricting `R` to terminating start states does not change `wp` either: the behaviour of
`R` outside `term` is irrelevant to `wp R term`. -/
theorem wp_restrict_eq (R : Rel σ) (term : Pred σ) :
    wp (fun s s' => term s ∧ R s s') term = wp R term :=
  trans_ext fun _ _ =>
    ⟨fun h => ⟨h.1, fun s' hr => h.2 s' ⟨h.1, hr⟩⟩,
     fun h => ⟨h.1, fun s' hr => h.2 s' hr.2⟩⟩

end Toy.PredTrans
