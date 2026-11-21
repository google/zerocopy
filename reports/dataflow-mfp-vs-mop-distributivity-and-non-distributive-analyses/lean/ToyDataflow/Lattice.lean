/-!
# Join-semilattices with bottom (toy model, core Lean only)

A dataflow analysis computes in a join-semilattice: `join` merges facts arriving
along different control-flow paths and `bot` is "no information yet". This file
gives the operations as a plain structure `Lat` and keeps every law a separate
named `Prop`, so each theorem can name exactly the laws it uses.

Orientation: `le a b` means "`a` is at least as precise as `b`" (`b` is a sound
over-approximation of `a`); joins move up. This is the orientation of a forward
*may* analysis. Meet-semilattice presentations (Kildall; Kam and Ullman) are the
order dual.
-/

namespace Toy.Dataflow

/-- The operations of a join-semilattice with bottom: an order relation `le`,
a binary `join` (intended least upper bound), and a bottom element `bot`.
No laws are bundled; see `Lat.IsJSL`. -/
structure Lat (α : Type) where
  le : α → α → Prop
  join : α → α → α
  bot : α

namespace Lat

variable {α : Type} (L : Lat α)

/-- Reflexivity of `le`. -/
def LeRefl : Prop := ∀ a, L.le a a

/-- Transitivity of `le`. -/
def LeTrans : Prop := ∀ a b c, L.le a b → L.le b c → L.le a c

/-- Antisymmetry of `le`. -/
def LeAntisymm : Prop := ∀ a b, L.le a b → L.le b a → a = b

/-- `join a b` is a least upper bound of `a` and `b`:
`join a b ≤ c` exactly when both `a ≤ c` and `b ≤ c`. -/
def JoinLeIff : Prop := ∀ a b c, L.le (L.join a b) c ↔ (L.le a c ∧ L.le b c)

/-- `bot` is below every element. -/
def BotLe : Prop := ∀ a, L.le L.bot a

/-- All join-semilattice-with-bottom laws: `le` is a partial order, `join` is the
binary least upper bound, and `bot` is the least element. Each field is a
separate named law.

The field `trans` is redundant given `refl`, `antisymm` and `join_le_iff`
(`Lat.leTrans_of_leRefl_leAntisymm_joinLeIff`). It is kept as its own field so
that results needing only transitivity (such as the soundness theorems in
`MopMfp.lean`) can assume `LeTrans` alone. -/
structure IsJSL : Prop where
  refl : L.LeRefl
  trans : L.LeTrans
  antisymm : L.LeAntisymm
  join_le_iff : L.JoinLeIff
  bot_le : L.BotLe

/-- Strict order: `le a b` and `a ≠ b`. -/
def lt (a b : α) : Prop := L.le a b ∧ a ≠ b

/-- Ascending chain condition: there is no infinite strictly ascending chain
`a₀ < a₁ < a₂ < ⋯`. Stated as well-foundedness of the reversed strict order. -/
def AscendingChainCondition : Prop := WellFounded (fun a b : α => L.lt b a)

/-- Height bound `h`: every strictly ascending chain `c 0 < c 1 < ⋯ < c k` has at
most `h` steps (`k ≤ h`). -/
def HeightLe (h : Nat) : Prop :=
  ∀ (k : Nat) (c : Nat → α), (∀ i, i < k → L.lt (c i) (c (i + 1))) → k ≤ h

/-- `a` is an upper bound of the set `S` (a predicate). -/
def IsUB (S : α → Prop) (a : α) : Prop := ∀ b, S b → L.le b a

/-- `a` is a least upper bound of the set `S`: an upper bound below every upper
bound. This is how infinite joins (over unboundedly many paths) are specified. -/
def IsLUB (S : α → Prop) (a : α) : Prop := L.IsUB S a ∧ ∀ u, L.IsUB S u → L.le a u

/-- Join of a finite list (`bot` for the empty list). -/
def joinList : List α → α
  | [] => L.bot
  | a :: l => L.join a (joinList l)

/-! ## Basic consequences of the laws (all proved) -/

variable {L}

/-- Transitivity follows from reflexivity, antisymmetry and the join law: from
`a ≤ b` the join law and reflexivity give `join a b = b`, and then `b ≤ c` gives
`join a b ≤ c`, hence `a ≤ c`. So no structure can violate `LeTrans` while
satisfying `LeRefl`, `LeAntisymm` and `JoinLeIff`. -/
theorem leTrans_of_leRefl_leAntisymm_joinLeIff (hrefl : L.LeRefl) (hanti : L.LeAntisymm)
    (hjoin : L.JoinLeIff) : L.LeTrans := by
  intro a b c hab hbc
  have h1 : L.le (L.join a b) b := (hjoin a b b).2 ⟨hab, hrefl b⟩
  have h2 : L.le b (L.join a b) := ((hjoin a b (L.join a b)).1 (hrefl (L.join a b))).2
  have heq : L.join a b = b := hanti _ _ h1 h2
  exact ((hjoin a b c).1 (heq.symm ▸ hbc)).1

theorem le_join_left (hL : L.IsJSL) (a b : α) : L.le a (L.join a b) :=
  ((hL.join_le_iff a b (L.join a b)).1 (hL.refl _)).1

theorem le_join_right (hL : L.IsJSL) (a b : α) : L.le b (L.join a b) :=
  ((hL.join_le_iff a b (L.join a b)).1 (hL.refl _)).2

theorem join_le (hL : L.IsJSL) {a b c : α} (ha : L.le a c) (hb : L.le b c) :
    L.le (L.join a b) c :=
  (hL.join_le_iff a b c).2 ⟨ha, hb⟩

theorem join_eq_right_of_le (hL : L.IsJSL) {a b : α} (h : L.le a b) : L.join a b = b :=
  hL.antisymm _ _ (join_le hL h (hL.refl b)) (le_join_right hL a b)

theorem join_self (hL : L.IsJSL) (a : α) : L.join a a = a :=
  join_eq_right_of_le hL (hL.refl a)

theorem join_bot (hL : L.IsJSL) (a : α) : L.join a L.bot = a :=
  hL.antisymm _ _ (join_le hL (hL.refl a) (hL.bot_le a)) (le_join_left hL a L.bot)

theorem IsLUB.unique (hL : L.IsJSL) {S : α → Prop} {a b : α}
    (ha : L.IsLUB S a) (hb : L.IsLUB S b) : a = b :=
  hL.antisymm _ _ (ha.2 b hb.1) (hb.2 a ha.1)

theorem isLUB_pair (hL : L.IsJSL) (a b : α) :
    L.IsLUB (fun c => c = a ∨ c = b) (L.join a b) := by
  refine ⟨?_, ?_⟩
  · rintro c (rfl | rfl)
    · exact le_join_left hL _ _
    · exact le_join_right hL _ _
  · intro u hu
    exact join_le hL (hu a (Or.inl rfl)) (hu b (Or.inr rfl))

theorem isLUB_singleton (hL : L.IsJSL) (a : α) : L.IsLUB (fun c => c = a) a := by
  refine ⟨?_, ?_⟩
  · rintro c rfl; exact hL.refl _
  · intro u hu; exact hu a rfl

theorem isLUB_empty (hL : L.IsJSL) : L.IsLUB (fun _ => False) L.bot :=
  ⟨fun _ h => h.elim, fun u _ => hL.bot_le u⟩

/-- A rank function into `Nat` that strictly increases along `lt` and is bounded
by `h` yields the height bound `h`. -/
theorem heightLe_of_rank (r : α → Nat) (hr : ∀ a b, L.lt a b → r a < r b)
    (h : Nat) (hb : ∀ a, r a ≤ h) : L.HeightLe h := by
  intro k c hc
  have key : ∀ j, j ≤ k → r (c 0) + j ≤ r (c j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have h2 := hr _ _ (hc j hj)
      omega
  have := key k (Nat.le_refl k)
  have := hb (c k)
  omega

/-- A height bound implies the ascending chain condition. -/
theorem acc_of_heightLe {h : Nat} (hh : L.HeightLe h) : L.AscendingChainCondition := by
  -- `Bounded m a`: every strictly ascending chain starting at `a` has at most `m` steps.
  have main : ∀ m (a : α),
      (∀ (k : Nat) (c : Nat → α), c 0 = a → (∀ i, i < k → L.lt (c i) (c (i + 1))) → k ≤ m) →
      Acc (fun a b : α => L.lt b a) a := by
    intro m
    induction m with
    | zero =>
      intro a ha
      refine Acc.intro a (fun b hab => ?_)
      have := ha 1 (fun i => if i = 0 then a else b) (by simp) (by
        intro i hi
        have : i = 0 := by omega
        subst this; simpa using hab)
      omega
    | succ m ih =>
      intro a ha
      refine Acc.intro a (fun b hab => ih b ?_)
      intro k c hc0 hc
      have := ha (k + 1) (fun i => if i = 0 then a else c (i - 1)) (by simp) (by
        intro i hi
        cases i with
        | zero => simpa [hc0] using hab
        | succ i =>
          have := hc i (by omega)
          simpa using this)
      omega
  exact ⟨fun a => main h a (fun k c _ hc => hh k c hc)⟩

theorem joinList_le_iff (hL : L.IsJSL) (l : List α) (c : α) :
    L.le (L.joinList l) c ↔ ∀ s ∈ l, L.le s c := by
  induction l with
  | nil =>
    exact ⟨fun _ _ hs => False.elim (List.not_mem_nil hs), fun _ => hL.bot_le c⟩
  | cons a l ih =>
    simp only [Lat.joinList, List.mem_cons]
    constructor
    · intro h s hs
      have h1 := (hL.join_le_iff a (L.joinList l) c).1 h
      rcases hs with rfl | hs
      · exact h1.1
      · exact ih.1 h1.2 s hs
    · intro h
      exact (hL.join_le_iff a (L.joinList l) c).2
        ⟨h a (Or.inl rfl), ih.2 (fun s hs => h s (Or.inr hs))⟩

end Lat

/-! ## The pointwise lattice on assignments `Fin n → α` -/

/-- The pointwise order, join and bottom on `Fin n → α`. -/
def pwLat (n : Nat) {α : Type} (L : Lat α) : Lat (Fin n → α) where
  le x y := ∀ v, L.le (x v) (y v)
  join x y v := L.join (x v) (y v)
  bot _ := L.bot

theorem pwLat_isJSL (n : Nat) {α : Type} {L : Lat α} (hL : L.IsJSL) : (pwLat n L).IsJSL where
  refl x v := hL.refl (x v)
  trans x y z hxy hyz v := hL.trans _ _ _ (hxy v) (hyz v)
  antisymm x y hxy hyx := funext fun v => hL.antisymm _ _ (hxy v) (hyx v)
  join_le_iff x y z := by
    simp only [pwLat]
    constructor
    · intro h
      exact ⟨fun v => ((hL.join_le_iff _ _ _).1 (h v)).1,
        fun v => ((hL.join_le_iff _ _ _).1 (h v)).2⟩
    · rintro ⟨h1, h2⟩ v
      exact (hL.join_le_iff _ _ _).2 ⟨h1 v, h2 v⟩
  bot_le x v := hL.bot_le (x v)

/-- The ascending chain condition is inherited by the pointwise lattice on a finite
index type (induction on `n`, lexicographic on the first coordinate). -/
theorem pwLat_acc : ∀ (n : Nat) {α : Type} {L : Lat α},
    L.AscendingChainCondition → (pwLat n L).AscendingChainCondition
  | 0, _, _, _ => ⟨fun x => Acc.intro x (fun y hy => by
      exfalso; apply hy.2; funext i; exact Fin.elim0 i)⟩
  | n + 1, α, L, hacc => by
    classical
    have ih := pwLat_acc n hacc
    have step : ∀ (a : α),
        ∀ (t : Fin n → α) (x : Fin (n + 1) → α),
          x 0 = a → (fun i : Fin n => x i.succ) = t →
          Acc (fun y z => (pwLat (n + 1) L).lt z y) x := by
      intro a
      refine hacc.induction (C := fun a => ∀ (t : Fin n → α) (x : Fin (n + 1) → α),
          x 0 = a → (fun i : Fin n => x i.succ) = t →
          Acc (fun y z => (pwLat (n + 1) L).lt z y) x) a ?_
      intro a iha t
      refine ih.induction (C := fun t => ∀ (x : Fin (n + 1) → α),
          x 0 = a → (fun i : Fin n => x i.succ) = t →
          Acc (fun y z => (pwLat (n + 1) L).lt z y) x) t ?_
      intro t iht x hx0 hxt
      refine Acc.intro x (fun y hy => ?_)
      obtain ⟨hle, hne⟩ := hy
      by_cases h0 : x 0 = y 0
      · have htne : (fun i : Fin n => x i.succ) ≠ (fun i : Fin n => y i.succ) := by
          intro heq
          apply hne
          funext i
          by_cases hi : i.val = 0
          · have : i = 0 := Fin.ext hi
            subst this; exact h0
          · have hj : i.val - 1 < n := by omega
            have hi' : i = Fin.succ ⟨i.val - 1, hj⟩ := by
              apply Fin.ext
              simp only [Fin.val_succ]
              omega
            rw [hi']
            exact congrFun heq ⟨i.val - 1, hj⟩
        have htle : (pwLat n L).lt (fun i => x i.succ) (fun i => y i.succ) :=
          ⟨fun j => hle j.succ, htne⟩
        exact iht (fun i => y i.succ) (hxt ▸ htle) y (h0.symm.trans hx0) rfl
      · have hale : L.lt a (y 0) := ⟨hx0 ▸ hle 0, fun h => h0 (hx0.trans h)⟩
        exact iha (y 0) hale (fun i => y i.succ) y rfl rfl
    exact ⟨fun x => step (x 0) (fun i => x i.succ) x rfl rfl⟩


/-! ## Transfer-function properties -/

variable {α : Type}

/-- `f` is monotone: it preserves `le`. Monotone transfer functions are the
setting of monotone dataflow frameworks. -/
def Monotone (L : Lat α) (f : α → α) : Prop := ∀ a b, L.le a b → L.le (f a) (f b)

/-- `f` distributes over binary joins: `f (a ⊔ b) = f a ⊔ f b`. This is the
"distributive framework" condition (Kildall's "homomorphic" condition, dualized). -/
def Distributive (L : Lat α) (f : α → α) : Prop := ∀ a b, f (L.join a b) = L.join (f a) (f b)

/-- `f` is strict: it maps `bot` to `bot`. -/
def Strict (L : Lat α) (f : α → α) : Prop := f L.bot = L.bot

/-- Distributivity implies monotonicity (under the lattice laws). -/
theorem monotone_of_distributive {L : Lat α} (hL : L.IsJSL) {f : α → α}
    (hf : Distributive L f) : Monotone L f := by
  intro a b hab
  have h1 : L.join a b = b := Lat.join_eq_right_of_le hL hab
  have h2 : f b = L.join (f a) (f b) := by rw [← hf, h1]
  rw [h2]
  exact Lat.le_join_left hL _ _

end Toy.Dataflow
