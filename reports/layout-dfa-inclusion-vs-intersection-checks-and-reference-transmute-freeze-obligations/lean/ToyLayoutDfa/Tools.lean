import ToyLayoutDfa.Basic

/-!
# Proof tools for concrete layouts

Fully proved helper lemmas used by the examples, counterexamples and non-vacuity
witnesses: one-step characterizations of `Path`, a Boolean acceptance test `acceptsB`
(which gives a `Decidable` instance for `Accepts` and `Lang`), a bounded word enumerator
`wordsFrom`, and two certificates: `RankCert` (implies `FixedSize`) and `LiveCert`
(implies `ReachableLive`). None of these is a result of the package.
-/

namespace Toy.LayoutDfa
namespace Layout

theorem mem_out {A : Layout} {q : Nat} {a : Sym} {q' : Nat} :
    (a, q') ∈ A.out q ↔ (q, a, q') ∈ A.edges := by
  unfold out
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨q0, a0, q0'⟩, hmem, h⟩
    by_cases hq : q0 = q
    · subst hq
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hmem
    · simp [hq] at h
  · intro h
    exact ⟨(q, a, q'), h, by simp⟩

theorem path_nil_iff {A : Layout} {q r : Nat} : A.Path q [] r ↔ q = r := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Path.nil _

theorem path_cons_iff {A : Layout} {q : Nat} {a : Sym} {w : List Sym} {r : Nat} :
    A.Path q (a :: w) r ↔ q ≠ A.accept ∧ ∃ q', (q, a, q') ∈ A.edges ∧ A.Path q' w r := by
  constructor
  · intro h
    cases h with
    | cons hq he hp => exact ⟨hq, _, he, hp⟩
  · rintro ⟨hq, q', he, hp⟩
    exact Path.cons hq he hp

/-- Boolean acceptance test, by recursion on the word. -/
def acceptsB (A : Layout) : Nat → List Sym → Bool
  | q, [] => decide (q = A.accept)
  | q, a :: w =>
    decide (q ≠ A.accept) && (A.out q).any (fun p => decide (p.1 = a) && acceptsB A p.2 w)

theorem acceptsB_iff {A : Layout} : ∀ {q : Nat} {w : List Sym},
    A.acceptsB q w = true ↔ A.Accepts q w
  | q, [] => by
    simp [acceptsB, Accepts, path_nil_iff]
  | q, a :: w => by
    simp only [acceptsB, Accepts, path_cons_iff, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    constructor
    · rintro ⟨hq, ⟨a', q'⟩, hmem, heq, hacc⟩
      simp only at heq
      subst heq
      exact ⟨hq, q', mem_out.mp hmem, acceptsB_iff.mp hacc⟩
    · rintro ⟨hq, q', he, hp⟩
      exact ⟨hq, ⟨a, q'⟩, mem_out.mpr he, rfl, acceptsB_iff.mpr hp⟩

instance instDecidableAccepts (A : Layout) (q : Nat) (w : List Sym) :
    Decidable (A.Accepts q w) :=
  decidable_of_iff _ acceptsB_iff

instance instDecidableLang (A : Layout) (w : List Sym) : Decidable (A.Lang w) :=
  instDecidableAccepts A A.start w

instance instDecidableDeterministic (A : Layout) : Decidable A.Deterministic := by
  unfold Deterministic
  infer_instance

/-- All words of length at most `f` accepted from `q` (by bounded depth-first expansion). -/
def wordsFrom (A : Layout) : Nat → Nat → List (List Sym)
  | 0, q => if q = A.accept then [[]] else []
  | f + 1, q =>
    if q = A.accept then [[]]
    else (A.out q).flatMap (fun p => (wordsFrom A f p.2).map (fun w => p.1 :: w))

theorem accepts_of_mem_wordsFrom {A : Layout} :
    ∀ {f q : Nat} {w : List Sym}, w ∈ A.wordsFrom f q → A.Accepts q w
  | 0, q, w, h => by
    unfold wordsFrom at h
    by_cases hq : q = A.accept
    · simp [hq] at h
      subst h
      exact hq ▸ Path.nil _
    · simp [hq] at h
  | f + 1, q, w, h => by
    unfold wordsFrom at h
    by_cases hq : q = A.accept
    · simp [hq] at h
      subst h
      exact hq ▸ Path.nil _
    · simp only [hq, ite_false, List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨a, q'⟩, hmem, w', hw', rfl⟩ := h
      exact Path.cons hq (mem_out.mp hmem) (accepts_of_mem_wordsFrom hw')

theorem mem_wordsFrom_of_accepts {A : Layout} :
    ∀ {q : Nat} {w : List Sym}, A.Accepts q w → w ∈ A.wordsFrom w.length q
  | q, [], h => by
    have hq : q = A.accept := path_nil_iff.mp h
    simp [wordsFrom, hq]
  | q, a :: w, h => by
    obtain ⟨hq, q', he, hp⟩ := path_cons_iff.mp h
    have ih := mem_wordsFrom_of_accepts (A := A) hp
    simp only [List.length_cons, wordsFrom, hq, ite_false, List.mem_flatMap, List.mem_map]
    exact ⟨(a, q'), mem_out.mpr he, w, ih, rfl⟩

/-- A rank certificate: the accept state has rank 0 and every edge out of a non-accept
state decreases the rank by exactly one. -/
def RankCert (A : Layout) (rank : Nat → Nat) : Prop :=
  rank A.accept = 0 ∧ ∀ e ∈ A.edges, e.1 ≠ A.accept → rank e.1 = rank e.2.2 + 1

instance (A : Layout) (rank : Nat → Nat) : Decidable (A.RankCert rank) := by
  unfold RankCert
  infer_instance

theorem length_of_accepts_of_rankCert {A : Layout} {rank : Nat → Nat} (h : A.RankCert rank) :
    ∀ {q : Nat} {w : List Sym}, A.Accepts q w → w.length = rank q
  | q, [], hw => by
    have hq : q = A.accept := path_nil_iff.mp hw
    simp [hq, h.1]
  | q, a :: w, hw => by
    obtain ⟨hq, q', he, hp⟩ := path_cons_iff.mp hw
    have ih := length_of_accepts_of_rankCert h hp
    have hr := h.2 (q, a, q') he hq
    simp only at hr
    simp [ih, hr]

theorem fixedSize_of_rankCert {A : Layout} {rank : Nat → Nat} (h : A.RankCert rank) :
    A.FixedSize (rank A.start) :=
  fun _ hw => length_of_accepts_of_rankCert h hw

/-- A liveness certificate: a list `R` of states containing the start state and closed
under edges out of non-accept states, such that every non-accept state of `R` has an edge
to a state of smaller `rank`. -/
def LiveCert (A : Layout) (rank : Nat → Nat) (R : List Nat) : Prop :=
  A.start ∈ R ∧ (∀ e ∈ A.edges, e.1 ∈ R → e.1 ≠ A.accept → e.2.2 ∈ R) ∧
    (∀ q ∈ R, q ≠ A.accept → ∃ e ∈ A.edges, e.1 = q ∧ rank e.2.2 < rank q)

instance (A : Layout) (rank : Nat → Nat) (R : List Nat) : Decidable (A.LiveCert rank R) := by
  unfold LiveCert
  infer_instance

theorem mem_of_path_of_liveCert {A : Layout} {rank : Nat → Nat} {R : List Nat}
    (h : A.LiveCert rank R) {q : Nat} {w : List Sym} {r : Nat} (hp : A.Path q w r) :
    q ∈ R → r ∈ R := by
  induction hp with
  | nil q => exact id
  | cons hq he _ ih => exact fun hqR => ih (h.2.1 _ he hqR hq)

theorem live_of_liveCert {A : Layout} {rank : Nat → Nat} {R : List Nat}
    (h : A.LiveCert rank R) : ∀ k q, q ∈ R → rank q < k → ∃ v, A.Accepts q v
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, q, hqR, hk => by
    by_cases hq : q = A.accept
    · exact ⟨[], hq ▸ Path.nil _⟩
    · obtain ⟨⟨q0, a, q'⟩, he, hq0, hlt⟩ := h.2.2 q hqR hq
      simp only at hq0 hlt
      subst hq0
      have hq'R : q' ∈ R := h.2.1 _ he hqR hq
      obtain ⟨v, hv⟩ := live_of_liveCert h k q' hq'R (by omega)
      exact ⟨a :: v, Path.cons hq he hv⟩

theorem reachableLive_of_liveCert {A : Layout} {rank : Nat → Nat} {R : List Nat}
    (h : A.LiveCert rank R) : A.ReachableLive := by
  intro w q hp
  have hqR := mem_of_path_of_liveCert h hp h.1
  exact live_of_liveCert h (rank q + 1) q hqR (Nat.lt_succ_self _)

/-- Inclusion from enumeration: if `A` has fixed size `n` and every word enumerated from
`A`'s start with depth `n` is accepted by `B`, then `L(A) ⊆ L(B)`. -/
theorem forall_lang_of_wordsFrom {A : Layout} {n : Nat} (hA : A.FixedSize n)
    {P : List Sym → Prop} (h : ∀ w ∈ A.wordsFrom n A.start, P w) : ∀ w, A.Lang w → P w := by
  intro w hw
  have hm := mem_wordsFrom_of_accepts hw
  rw [hA w hw] at hm
  exact h w hm

theorem fixedSize_of_rankCert' {A : Layout} {rank : Nat → Nat} {n : Nat}
    (h : A.RankCert rank) (hn : rank A.start = n) : A.FixedSize n :=
  hn ▸ fixedSize_of_rankCert h

/-- A word of a length other than `n` in the language refutes `FixedSize n`. -/
theorem not_fixedSize_of_lang {A : Layout} {n : Nat} {w : List Sym} (hw : A.Lang w)
    (hn : w.length ≠ n) : ¬ A.FixedSize n :=
  fun h => hn (h w hw)

end Layout
end Toy.LayoutDfa
