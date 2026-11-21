import ToyInline.Semantics

/-!
# Auxiliary facts about the runner (fully proved)

Monotonicity and stability of `runWith`, and the two tools used by every concrete
counterexample and positive control: equal halted observations give behavioural equivalence
from that entry, and different halted observations refute it.
-/

namespace Toy.Inline

theorem runWith_halted (pol : LocPolicy) (p : Program) (n : Nat) (o : Outcome) :
    runWith pol p n (.halted o) = ⟨[], some o⟩ := by
  cases n <;> rfl

theorem Obs.Prefix.refl (o : Obs) : o.Prefix o := ⟨List.prefix_rfl, fun _ => rfl⟩

theorem Obs.Prefix.trans {a b c : Obs} (h1 : a.Prefix b) (h2 : b.Prefix c) : a.Prefix c := by
  refine ⟨h1.1.trans h2.1, fun h => ?_⟩
  have hb : b = a := h1.2 h
  subst hb
  exact h2.2 h

/-- More fuel extends the observation. -/
theorem runWith_mono (pol : LocPolicy) (p : Program) :
    ∀ (n m : Nat) (c : Config), n ≤ m → (runWith pol p n c).Prefix (runWith pol p m c) := by
  intro n
  induction n with
  | zero =>
    intro m c _
    cases c with
    | halted o => rw [runWith_halted, runWith_halted]; exact Obs.Prefix.refl _
    | running s =>
      refine ⟨List.nil_prefix, ?_⟩
      intro h
      simp [runWith] at h
  | succ n ih =>
    intro m c hnm
    cases c with
    | halted o => rw [runWith_halted, runWith_halted]; exact Obs.Prefix.refl _
    | running s =>
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h := ih m' (step pol p s).1 (by omega)
      refine ⟨?_, ?_⟩
      · simp only [runWith]
        exact (List.prefix_append_right_inj _).mpr h.1
      · intro hs
        simp only [runWith] at hs ⊢
        rw [h.2 hs]

/-- Once halted, the observation no longer changes. -/
theorem runWith_prefix_of_halted {pol : LocPolicy} {p : Program} {n : Nat} {c : Config}
    (hn : (runWith pol p n c).outcome.isSome) (n' : Nat) :
    (runWith pol p n' c).Prefix (runWith pol p n c) := by
  by_cases h : n' ≤ n
  · exact runWith_mono pol p n' n c h
  · have := (runWith_mono pol p n n' c (by omega)).2 hn
    rw [this]
    exact Obs.Prefix.refl _

/-- Two halted observations of the same run coincide. -/
theorem runWith_halted_unique {pol : LocPolicy} {p : Program} {n m : Nat} {c : Config}
    (hn : (runWith pol p n c).outcome.isSome) (hm : (runWith pol p m c).outcome.isSome) :
    runWith pol p n c = runWith pol p m c := by
  by_cases h : n ≤ m
  · exact ((runWith_mono pol p n m c h).2 hn).symm
  · exact (runWith_mono pol p m n c (by omega)).2 hm

/-- Equal halted observations give behavioural equivalence from that entry. -/
theorem behEquivAtWith_of_halted_eq {pol : LocPolicy} {p q : Program} {e : Entry} {n m : Nat}
    (hh : (runWith pol p n (init p e)).outcome.isSome)
    (heq : runWith pol p n (init p e) = runWith pol q m (init q e)) :
    BehEquivAtWith pol p q e := by
  have hq : (runWith pol q m (init q e)).outcome.isSome := heq ▸ hh
  refine ⟨fun n' => ⟨m, ?_⟩, fun m' => ⟨n, ?_⟩⟩
  · rw [← heq]; exact runWith_prefix_of_halted hh n'
  · rw [heq]; exact runWith_prefix_of_halted hq m'

/-- Different halted observations refute behavioural equivalence from that entry. -/
theorem not_behEquivAtWith_of_halted_ne {pol : LocPolicy} {p q : Program} {e : Entry}
    {n m : Nat}
    (hp : (runWith pol p n (init p e)).outcome.isSome)
    (hq : (runWith pol q m (init q e)).outcome.isSome)
    (hne : runWith pol p n (init p e) ≠ runWith pol q m (init q e)) :
    ¬ BehEquivAtWith pol p q e := by
  intro h
  obtain ⟨m', hm'⟩ := h.1 n
  have h1 : runWith pol q m' (init q e) = runWith pol p n (init p e) := hm'.2 hp
  have hq' : (runWith pol q m' (init q e)).outcome.isSome := h1 ▸ hp
  exact hne (h1.symm.trans (runWith_halted_unique hq' hq))

/-- `BehEquivAtWith` is an equivalence relation; reflexivity and symmetry are immediate. -/
theorem behEquivAtWith_refl (pol : LocPolicy) (p : Program) (e : Entry) :
    BehEquivAtWith pol p p e :=
  ⟨fun n => ⟨n, Obs.Prefix.refl _⟩, fun n => ⟨n, Obs.Prefix.refl _⟩⟩

theorem behEquivAtWith_symm {pol : LocPolicy} {p q : Program} {e : Entry}
    (h : BehEquivAtWith pol p q e) : BehEquivAtWith pol q p e :=
  ⟨h.2, h.1⟩

end Toy.Inline
