/-
Toy.SCT.Ramsey
==============

A self-contained proof of the infinite Ramsey theorem for pairs with finitely many colours (the
colours of all pairs lie in a finite list), by iterated infinite pigeonhole. Only core Lean is
used.
-/

namespace Toy.SCT.RamseyProof

/-- A predicate on the naturals holds infinitely often. -/
def InfOften (X : Nat → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ X n

theorem InfOften.mono {X Y : Nat → Prop} (h : InfOften X) (hXY : ∀ n, X n → Y n) : InfOften Y :=
  fun N => let ⟨n, hn, hx⟩ := h N; ⟨n, hn, hXY n hx⟩

/-- Infinite pigeonhole: if infinitely many naturals satisfy `X` and each of them gets a colour from
the finite list `S`, some colour is taken infinitely often. -/
theorem infOften_pigeonhole {α : Type} (S : List α) :
    ∀ (X : Nat → Prop) (c : Nat → α), InfOften X → (∀ n, X n → c n ∈ S) →
      ∃ a, InfOften (fun n => X n ∧ c n = a) := by
  induction S with
  | nil =>
    intro X c hX hc
    obtain ⟨n, -, hn⟩ := hX 0
    exact absurd (hc n hn) (List.not_mem_nil)
  | cons a S ih =>
    intro X c hX hc
    by_cases ha : InfOften (fun n => X n ∧ c n = a)
    · exact ⟨a, ha⟩
    · have ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → ¬ (X n ∧ c n = a) :=
        Classical.byContradiction fun hne => ha fun N =>
          Classical.byContradiction fun hno =>
            hne ⟨N, fun n hn hx => hno ⟨n, hn, hx⟩⟩
      have hX' : InfOften (fun n => X n ∧ N ≤ n) := fun M =>
        let ⟨n, hn, hx⟩ := hX (M + N)
        ⟨n, by omega, hx, by omega⟩
      have hc' : ∀ n, (X n ∧ N ≤ n) → c n ∈ S := by
        intro n ⟨hx, hn⟩
        have hmem := hc n hx
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd ⟨hx, h⟩ (hN n hn)
        · exact h
      obtain ⟨b, hb⟩ := ih _ c hX' hc'
      exact ⟨b, hb.mono fun n ⟨⟨hx, _⟩, he⟩ => ⟨hx, he⟩⟩

/-- Enumeration of an infinite set of naturals by a strictly increasing sequence. -/
noncomputable def enum (X : Nat → Prop) (hX : InfOften X) : Nat → Nat
  | 0 => Classical.choose (hX 0)
  | n + 1 => Classical.choose (hX (enum X hX n + 1))

theorem enum_spec (X : Nat → Prop) (hX : InfOften X) :
    ∀ n, X (enum X hX n) ∧ enum X hX n < enum X hX (n + 1) := by
  intro n
  cases n with
  | zero =>
    refine ⟨(Classical.choose_spec (hX 0)).2, ?_⟩
    have := (Classical.choose_spec (hX (enum X hX 0 + 1))).1
    show enum X hX 0 < Classical.choose (hX (enum X hX 0 + 1))
    omega
  | succ n =>
    refine ⟨(Classical.choose_spec (hX (enum X hX n + 1))).2, ?_⟩
    have := (Classical.choose_spec (hX (enum X hX (n + 1) + 1))).1
    show enum X hX (n + 1) < Classical.choose (hX (enum X hX (n + 1) + 1))
    omega

theorem strictMono_of_succ (e : Nat → Nat) (h : ∀ n, e n < e (n + 1)) :
    ∀ m n, m < n → e m < e n := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with h' | h'
    · exact Nat.lt_trans (ih h') (h n)
    · subst h'; exact h m

/-- The state of the Ramsey construction: an infinite set of candidate positions. -/
abbrev RState := {X : Nat → Prop // InfOften X}

section Construction

/-- The next chosen position: some element of the current candidate set. -/
noncomputable def pick (st : RState) : Nat := Classical.choose (st.2 0)

theorem pick_mem (st : RState) : st.1 (pick st) := (Classical.choose_spec (st.2 0)).2

theorem tail_inf (st : RState) : InfOften (fun n => st.1 n ∧ pick st < n) := fun N =>
  let ⟨n, hn, hx⟩ := st.2 (N + pick st + 1)
  ⟨n, by omega, hx, by omega⟩

theorem exists_color {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) (st : RState) :
    ∃ a, InfOften (fun n => (st.1 n ∧ pick st < n) ∧ col (pick st) n = a) :=
  infOften_pigeonhole S _ (fun n => col (pick st) n) (tail_inf st)
    (fun _ ⟨_, hlt⟩ => hS _ _ hlt)

/-- The colour shared by the chosen position and all later candidates. -/
noncomputable def color {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) (st : RState) : α := Classical.choose (exists_color S col hS st)

/-- The next candidate set: later candidates whose pair with the chosen position has the
chosen colour. -/
noncomputable def next {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) (st : RState) : RState :=
  ⟨fun m => (st.1 m ∧ pick st < m) ∧ col (pick st) m = color S col hS st,
    Classical.choose_spec (exists_color S col hS st)⟩

/-- The sequence of candidate sets. -/
noncomputable def states {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) : Nat → RState
  | 0 => ⟨fun _ => True, fun N => ⟨N, Nat.le_refl _, trivial⟩⟩
  | i + 1 => next S col hS (states S col hS i)

theorem states_sub {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) : ∀ i j, i ≤ j → ∀ n, (states S col hS j).1 n → (states S col hS i).1 n := by
  intro i j hij
  induction hij with
  | refl => exact fun _ h => h
  | step _ ih => exact fun n h => ih n h.1.1

theorem pairs_colored {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) (i j : Nat) (hij : i < j) :
    pick (states S col hS i) < pick (states S col hS j) ∧
    col (pick (states S col hS i)) (pick (states S col hS j)) = color S col hS (states S col hS i) := by
  have hmem := states_sub S col hS (i + 1) j hij _ (pick_mem (states S col hS j))
  exact ⟨hmem.1.2, hmem.2⟩

end Construction

/-- **Infinite Ramsey theorem for pairs, finitely many colours.** -/
theorem ramsey {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) :
    ∃ h : Nat → Nat, (∀ m n, m < n → h m < h n) ∧
      ∃ a : α, ∀ m n, m < n → col (h m) (h n) = a := by
  let x : Nat → Nat := fun i => pick (states S col hS i)
  let a : Nat → α := fun i => color S col hS (states S col hS i)
  have hall : InfOften (fun _ : Nat => True) := fun N => ⟨N, Nat.le_refl _, trivial⟩
  have hcol : ∀ i, True → a i ∈ S := by
    intro i _
    have := pairs_colored S col hS i (i + 1) (Nat.lt_succ_self i)
    show color S col hS (states S col hS i) ∈ S
    rw [← this.2]
    exact hS _ _ this.1
  obtain ⟨c, hc⟩ := infOften_pigeonhole S (fun _ => True) a hall hcol
  let e := enum _ hc
  have he := enum_spec _ hc
  have hemono := strictMono_of_succ e (fun n => (he n).2)
  refine ⟨fun n => x (e n), fun m n hmn => (pairs_colored S col hS _ _ (hemono m n hmn)).1, c,
    fun m n hmn => ?_⟩
  have h1 := (pairs_colored S col hS _ _ (hemono m n hmn)).2
  have h2 : a (e m) = c := (he m).1.2
  exact h1.trans h2

end Toy.SCT.RamseyProof
