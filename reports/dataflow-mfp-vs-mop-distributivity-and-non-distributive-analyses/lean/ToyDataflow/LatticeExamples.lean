import ToyDataflow.Lattice

/-!
# Positive and negative examples for the lattice definitions

Intended instances (`boolLat`, `natMaxLat`, a lattice with the ascending chain
condition but no finite height bound, finite chains, `Int` with a bottom
element) and, for each separate law, a structure that violates it.

For `LeRefl`, `LeAntisymm`, `JoinLeIff` and `BotLe` the negative example violates
exactly that law and satisfies the other four (`*_law_profile`). No structure can
violate `LeTrans` alone, because `LeRefl ∧ LeAntisymm ∧ JoinLeIff` implies it
(`Lat.leTrans_of_leRefl_leAntisymm_joinLeIff`); the `LeTrans` examples therefore
also violate other laws, and their exact profiles are proved.
-/

namespace Toy.Dataflow

/-- The two-point lattice `false < true` (one bit of a may-analysis). -/
def boolLat : Lat Bool where
  le a b := a = true → b = true
  join a b := a || b
  bot := false

instance (a b : Bool) : Decidable (boolLat.le a b) :=
  inferInstanceAs (Decidable (a = true → b = true))

/-- Positive example: `boolLat` satisfies every law. -/
theorem boolLat_isJSL : boolLat.IsJSL where
  refl := by intro a; cases a <;> decide
  trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  antisymm := by intro a b; cases a <;> cases b <;> decide
  join_le_iff := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  bot_le := by intro a; cases a <;> decide

/-- Positive example: `boolLat` has height at most `1`. -/
theorem boolLat_heightLe_one : boolLat.HeightLe 1 := by
  refine Lat.heightLe_of_rank (fun b => if b then 1 else 0) ?_ 1 ?_
  · intro a b ⟨hab, hne⟩
    cases a <;> cases b <;> simp_all [boolLat]
  · intro a; cases a <;> simp

/-- Positive example: `boolLat` satisfies the ascending chain condition. -/
theorem boolLat_acc : boolLat.AscendingChainCondition :=
  Lat.acc_of_heightLe boolLat_heightLe_one

/-- Negative example: `boolLat` does not have height `0` (`false < true`). -/
theorem boolLat_not_heightLe_zero : ¬ boolLat.HeightLe 0 := by
  intro h
  have := h 1 (fun i => if i = 0 then false else true) (by
    intro i hi
    have : i = 0 := by omega
    subst this
    exact ⟨by decide, by decide⟩)
  omega

/-- The natural numbers under `max`: a join-semilattice with bottom but with
infinite ascending chains. -/
def natMaxLat : Lat Nat where
  le a b := a ≤ b
  join a b := max a b
  bot := 0

/-- Positive example: `natMaxLat` satisfies every lattice law. -/
theorem natMaxLat_isJSL : natMaxLat.IsJSL where
  refl := fun a => Nat.le_refl a
  trans := fun _ _ _ => Nat.le_trans
  antisymm := fun _ _ => Nat.le_antisymm
  join_le_iff := fun _ _ _ => Nat.max_le
  bot_le := fun a => Nat.zero_le a

/-- Negative example: `natMaxLat` violates the ascending chain condition
(`0 < 1 < 2 < ⋯`). So `AscendingChainCondition` is not implied by the lattice laws. -/
theorem natMaxLat_not_acc : ¬ natMaxLat.AscendingChainCondition := by
  intro hwf
  have : ∀ a : Nat, Acc (fun a b : Nat => natMaxLat.lt b a) a → False := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      exact ih (a + 1) ⟨Nat.le_succ a, by omega⟩
  exact this 0 (hwf.apply 0)

/-- Negative example: `natMaxLat` has no finite height bound. -/
theorem natMaxLat_not_heightLe (h : Nat) : ¬ natMaxLat.HeightLe h := by
  intro hh
  have := hh (h + 1) (fun i => i) (fun i _ => ⟨Nat.le_succ i, by omega⟩)
  omega

/-! ### One structure per law -/

/-- Violates reflexivity only: `le a b := (a = false)`, so `true ≤ true` fails. -/
def notReflLat : Lat Bool := { boolLat with le := fun a _ => a = false }

instance (a b : Bool) : Decidable (notReflLat.le a b) :=
  inferInstanceAs (Decidable (a = false))

theorem notReflLat_not_leRefl : ¬ notReflLat.LeRefl := fun h => by
  simpa [notReflLat] using h true

/-- `notReflLat` violates `LeRefl` and satisfies the other four laws. -/
theorem notReflLat_law_profile :
    ¬ notReflLat.LeRefl ∧ notReflLat.LeTrans ∧ notReflLat.LeAntisymm ∧
      notReflLat.JoinLeIff ∧ notReflLat.BotLe := by
  refine ⟨notReflLat_not_leRefl, ?_, ?_, ?_, ?_⟩
  · intro a b c; cases a <;> cases b <;> cases c <;> decide
  · intro a b; cases a <;> cases b <;> decide
  · intro a b c; cases a <;> cases b <;> cases c <;> simp [notReflLat, boolLat]
  · intro a; simp [notReflLat, boolLat]

/-- Violates transitivity: `0 ≤ 1` and `1 ≤ 2` but not `0 ≤ 2`. It also violates
`JoinLeIff` and `BotLe` (`notTransLat_law_profile`); violating `LeTrans` alone is
impossible (`no_lat_violates_only_leTrans`). -/
def notTransLat : Lat (Fin 3) where
  le a b := a.val ≤ b.val ∧ b.val ≤ a.val + 1
  join a b := if a.val ≤ b.val then b else a
  bot := 0

instance (a b : Fin 3) : Decidable (notTransLat.le a b) :=
  inferInstanceAs (Decidable (a.val ≤ b.val ∧ b.val ≤ a.val + 1))

theorem notTransLat_not_leTrans : ¬ notTransLat.LeTrans := by
  intro h
  have := h 0 1 2 (by simp [notTransLat]) (by simp [notTransLat])
  simp [notTransLat] at this

/-- `notTransLat` satisfies `LeRefl` and `LeAntisymm` and violates the other three laws. -/
theorem notTransLat_law_profile :
    notTransLat.LeRefl ∧ ¬ notTransLat.LeTrans ∧ notTransLat.LeAntisymm ∧
      ¬ notTransLat.JoinLeIff ∧ ¬ notTransLat.BotLe := by
  refine ⟨fun a => by simp [notTransLat], notTransLat_not_leTrans,
    fun a b h1 h2 => Fin.ext (Nat.le_antisymm h1.1 h2.1), fun h => ?_, fun h => ?_⟩
  · have := (h 0 1 2).1 (by simp [notTransLat])
    simp [notTransLat] at this
  · have := h 2
    simp [notTransLat] at this

/-- No structure violates `LeTrans` while satisfying the other four laws. -/
theorem no_lat_violates_only_leTrans {α : Type} :
    ¬ ∃ L : Lat α, L.LeRefl ∧ ¬ L.LeTrans ∧ L.LeAntisymm ∧ L.JoinLeIff ∧ L.BotLe := by
  rintro ⟨L, hr, hnt, ha, hj, _⟩
  exact hnt (Lat.leTrans_of_leRefl_leAntisymm_joinLeIff hr ha hj)

/-- A preorder-like structure on `Fin 4` satisfying `LeRefl`, `JoinLeIff` and `BotLe`
but neither `LeAntisymm` nor `LeTrans`: antisymmetry is needed to derive
transitivity. -/
def fin4PreLat : Lat (Fin 4) where
  le a b := match a, b with
    | 0, _ => True
    | 1, 1 | 1, 2 | 1, 3 => True
    | 2, 0 | 2, 2 | 2, 3 => True
    | 3, 2 | 3, 3 => True
    | _, _ => False
  join a b := match a, b with
    | 0, b => b
    | a, 0 => a
    | 1, 1 => 1
    | 2, 2 => 2
    | _, _ => 3
  bot := 0

instance (a b : Fin 4) : Decidable (fin4PreLat.le a b) := by
  unfold fin4PreLat
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  dsimp
  match a, b with
  | 0, _ => exact isTrue trivial
  | 1, 1 | 1, 2 | 1, 3 => exact isTrue trivial
  | 2, 0 | 2, 2 | 2, 3 => exact isTrue trivial
  | 3, 2 | 3, 3 => exact isTrue trivial
  | 1, 0 | 2, 1 | 3, 0 | 3, 1 => exact isFalse (fun h => h)

theorem fin4_cases (a : Fin 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  revert a; decide

theorem fin4PreLat_law_profile :
    fin4PreLat.LeRefl ∧ ¬ fin4PreLat.LeTrans ∧ ¬ fin4PreLat.LeAntisymm ∧
      fin4PreLat.JoinLeIff ∧ fin4PreLat.BotLe := by
  refine ⟨?_, fun h => ?_, fun h => ?_, ?_, ?_⟩
  · intro a; rcases fin4_cases a with rfl | rfl | rfl | rfl <;> decide
  · have : fin4PreLat.le 2 1 := h 2 0 1 (by decide) (by decide)
    revert this; decide
  · have : (0 : Fin 4) = 2 := h 0 2 (by decide) (by decide)
    simp at this
  · intro a b c
    rcases fin4_cases a with rfl | rfl | rfl | rfl <;>
      rcases fin4_cases b with rfl | rfl | rfl | rfl <;>
      rcases fin4_cases c with rfl | rfl | rfl | rfl <;>
      decide
  · intro a; rcases fin4_cases a with rfl | rfl | rfl | rfl <;> decide

/-- Violates antisymmetry (`le` is total). -/
def notAntisymmLat : Lat Bool := { boolLat with le := fun _ _ => True }

theorem notAntisymmLat_not_leAntisymm : ¬ notAntisymmLat.LeAntisymm := by
  intro h
  exact Bool.false_ne_true (h false true trivial trivial)

theorem notAntisymmLat_law_profile :
    notAntisymmLat.LeRefl ∧ notAntisymmLat.LeTrans ∧ ¬ notAntisymmLat.LeAntisymm ∧
      notAntisymmLat.JoinLeIff ∧ notAntisymmLat.BotLe := by
  refine ⟨?_, ?_, notAntisymmLat_not_leAntisymm, ?_, ?_⟩
  · intro a; simp [notAntisymmLat]
  · intro a b c _ _; simp [notAntisymmLat]
  · intro a b c; simp [notAntisymmLat]
  · intro a; simp [notAntisymmLat]

/-- Violates the join law: `join` is the left projection. -/
def notJoinLat : Lat Bool := { boolLat with join := fun a _ => a }

theorem notJoinLat_not_joinLeIff : ¬ notJoinLat.JoinLeIff := by
  intro h
  have := (h false true false).1 (by simp [notJoinLat, boolLat])
  simpa [notJoinLat, boolLat] using this.2

theorem notJoinLat_law_profile :
    notJoinLat.LeRefl ∧ notJoinLat.LeTrans ∧ notJoinLat.LeAntisymm ∧
      ¬ notJoinLat.JoinLeIff ∧ notJoinLat.BotLe := by
  refine ⟨?_, ?_, ?_, notJoinLat_not_joinLeIff, ?_⟩
  · intro a; simp [notJoinLat, boolLat]
  · intro a b c hab hbc ha; exact hbc (hab ha)
  · intro a b hab hba; cases a <;> cases b <;> simp_all [notJoinLat, boolLat]
  · intro a ha; simp [notJoinLat, boolLat] at ha

/-- Violates the bottom law: `bot := true`. -/
def notBotLat : Lat Bool := { boolLat with bot := true }

theorem notBotLat_not_botLe : ¬ notBotLat.BotLe := by
  intro h
  simpa [notBotLat, boolLat] using h false

theorem notBotLat_law_profile :
    notBotLat.LeRefl ∧ notBotLat.LeTrans ∧ notBotLat.LeAntisymm ∧
      notBotLat.JoinLeIff ∧ ¬ notBotLat.BotLe := by
  refine ⟨?_, ?_, ?_, ?_, notBotLat_not_botLe⟩
  · intro a; simp [notBotLat, boolLat]
  · intro a b c hab hbc ha; exact hbc (hab ha)
  · intro a b hab hba; cases a <;> cases b <;> simp_all [notBotLat, boolLat]
  · intro a b c; cases a <;> cases b <;> cases c <;> simp [notBotLat, boolLat] <;> decide

/-! ### Transfer-function properties on `boolLat` -/

/-- Positive example: the identity is monotone, distributive, and strict. -/
theorem id_monotone_distributive_strict :
    Monotone boolLat id ∧ Distributive boolLat id ∧ Strict boolLat id :=
  ⟨fun _ _ h => h, fun _ _ => rfl, rfl⟩

/-- Negative example: Boolean negation is not monotone. -/
theorem not_not_monotone : ¬ Monotone boolLat (fun b => !b) := by
  intro h
  exact absurd (h false true (by decide)) (by decide)

/-- Negative example: Boolean negation is not distributive. -/
theorem not_not_distributive : ¬ Distributive boolLat (fun b => !b) := by
  intro h
  exact absurd (h false true) (by decide)

/-- Negative example: the constant `true` is monotone and distributive but not strict. -/
theorem const_true_not_strict :
    Monotone boolLat (fun _ => true) ∧ Distributive boolLat (fun _ => true) ∧
      ¬ Strict boolLat (fun _ => true) :=
  ⟨fun _ _ _ => fun _ => rfl, fun _ _ => rfl, by simp [Strict, boolLat]⟩

/-! ### The ascending chain condition without a finite height bound -/

/-- Disjoint union of the finite chains `mid m 0 < mid m 1 < ... < mid m m`, one for
each `m`, with a common `bot` and `top`. It satisfies the ascending chain condition
but has no finite height bound (`unboundedChainsLat_acc`, `unboundedChainsLat_not_heightLe`). -/
inductive UnboundedChains where
  | bot
  | mid (m k : Nat)
  | top
  deriving DecidableEq

namespace UnboundedChains

def le : UnboundedChains → UnboundedChains → Prop
  | bot, _ => True
  | _, top => True
  | mid m₁ k₁, mid m₂ k₂ => (m₁ = m₂ ∧ k₁ = k₂) ∨ (m₁ = m₂ ∧ k₁ ≤ k₂ ∧ k₂ ≤ m₁)
  | _, _ => False

def join : UnboundedChains → UnboundedChains → UnboundedChains
  | bot, b => b
  | a, bot => a
  | top, _ => top
  | _, top => top
  | mid m₁ k₁, mid m₂ k₂ =>
    if m₁ = m₂ then
      if k₁ = k₂ then mid m₁ k₁
      else if max k₁ k₂ ≤ m₁ then mid m₁ (max k₁ k₂)
      else top
    else top

def rem : UnboundedChains → Nat
  | top => 0
  | mid m k => if k ≤ m then m + 1 - k else 1
  | bot => 0

end UnboundedChains

def unboundedChainsLat : Lat UnboundedChains :=
  ⟨UnboundedChains.le, UnboundedChains.join, .bot⟩

instance : DecidableRel unboundedChainsLat.le := fun a b =>
  match a, b with
  | .bot, _ => isTrue trivial
  | .mid _ _, .top => isTrue trivial
  | .top, .top => isTrue trivial
  | .mid m₁ k₁, .mid m₂ k₂ =>
    inferInstanceAs (Decidable ((m₁ = m₂ ∧ k₁ = k₂) ∨ (m₁ = m₂ ∧ k₁ ≤ k₂ ∧ k₂ ≤ m₁)))
  | .mid _ _, .bot => isFalse (fun h => h)
  | .top, .bot => isFalse (fun h => h)
  | .top, .mid _ _ => isFalse (fun h => h)

theorem unboundedChainsLat_isJSL : unboundedChainsLat.IsJSL where
  refl a := by cases a <;> simp [unboundedChainsLat, UnboundedChains.le]
  trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp [unboundedChainsLat, UnboundedChains.le] at hab hbc ⊢ <;>
      omega
  antisymm a b hab hba := by
    cases a <;> cases b <;> simp [unboundedChainsLat, UnboundedChains.le] at hab hba ⊢ <;>
      omega
  join_le_iff a b c := by
    cases a with
    | bot => simp [unboundedChainsLat, UnboundedChains.le, UnboundedChains.join]
    | top =>
      cases b <;> cases c <;> simp [unboundedChainsLat, UnboundedChains.le, UnboundedChains.join]
    | mid m₁ k₁ =>
      cases b with
      | bot => simp [unboundedChainsLat, UnboundedChains.le, UnboundedChains.join]
      | top => cases c <;> simp [unboundedChainsLat, UnboundedChains.le, UnboundedChains.join]
      | mid m₂ k₂ =>
        cases c with
        | bot =>
          by_cases hm : m₁ = m₂
          · subst hm
            by_cases hk : k₁ = k₂ <;> by_cases hmax : max k₁ k₂ ≤ m₁ <;>
              simp [unboundedChainsLat, UnboundedChains.join, UnboundedChains.le, hk, hmax]
          · simp [unboundedChainsLat, UnboundedChains.join, UnboundedChains.le, hm]
        | top =>
          by_cases hm : m₁ = m₂
          · subst hm
            by_cases hk : k₁ = k₂ <;> by_cases hmax : max k₁ k₂ ≤ m₁ <;>
              simp [unboundedChainsLat, UnboundedChains.join, UnboundedChains.le, hk, hmax]
          · simp [unboundedChainsLat, UnboundedChains.join, UnboundedChains.le, hm]
        | mid m₃ k₃ =>
          simp only [unboundedChainsLat, UnboundedChains.join, UnboundedChains.le]
          by_cases hm : m₁ = m₂
          · subst hm
            by_cases hk : k₁ = k₂
            · subst hk; simp
            · by_cases hmax : max k₁ k₂ ≤ m₁
              · simp only [↓reduceIte, hk, hmax]
                constructor
                · intro h
                  rcases h with ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ <;> omega
                · rintro ⟨h1, h2⟩
                  right
                  omega
              · simp only [↓reduceIte, hk, hmax]
                constructor
                · intro h; simp at h
                · rintro ⟨h1, h2⟩
                  exfalso; omega
          · simp only [hm, ↓reduceIte]
            constructor
            · intro h; simp at h
            · rintro ⟨h1, h2⟩
              exfalso; omega
  bot_le a := by simp [unboundedChainsLat, UnboundedChains.le]

theorem unboundedChainsLat_acc : unboundedChainsLat.AscendingChainCondition := by
  have nonbot : ∀ r (x : UnboundedChains), x ≠ .bot → x.rem ≤ r →
      Acc (fun a b => unboundedChainsLat.lt b a) x := by
    intro r
    induction r with
    | zero =>
      intro x hx hr
      refine Acc.intro x (fun y hy => ?_)
      exfalso
      cases x with
      | bot => exact hx rfl
      | top => cases y <;> simp [Lat.lt, unboundedChainsLat, UnboundedChains.le] at hy
      | mid m k =>
        simp [UnboundedChains.rem] at hr
        split at hr <;> omega
    | succ r ih =>
      intro x hx hr
      refine Acc.intro x (fun y hy => ?_)
      have hyne : y ≠ .bot := by
        intro hyb; subst hyb
        cases x <;> simp [Lat.lt, unboundedChainsLat, UnboundedChains.le] at hy
      have hrem : y.rem < x.rem := by
        obtain ⟨hle, hne⟩ := hy
        cases x with
        | bot => exact absurd rfl hx
        | top => cases y with
          | top => exact absurd rfl hne
          | bot => simp [unboundedChainsLat, UnboundedChains.le] at hle
          | mid _ _ => simp [unboundedChainsLat, UnboundedChains.le] at hle
        | mid m₁ k₁ =>
          cases y with
          | bot => simp [unboundedChainsLat, UnboundedChains.le] at hle
          | top =>
            simp only [UnboundedChains.rem]
            split <;> omega
          | mid m₂ k₂ =>
            simp only [unboundedChainsLat, UnboundedChains.le] at hle
            simp only [UnboundedChains.rem]
            rcases hle with ⟨rfl, rfl⟩ | ⟨rfl, h12, h2m⟩
            · exact absurd rfl hne
            · have hklt : k₁ < k₂ := by
                rcases Nat.eq_or_lt_of_le h12 with rfl | hlt
                · exact absurd rfl hne
                · exact hlt
              have hk1m : k₁ ≤ m₁ := Nat.le_trans h12 h2m
              simp only [hk1m, h2m, ↓reduceIte]
              omega
      exact ih y hyne (by omega)
  refine ⟨fun x => ?_⟩
  cases x with
  | bot =>
    refine Acc.intro UnboundedChains.bot (fun y hy => ?_)
    have hyne : y ≠ .bot := fun h => by subst h; exact hy.2 rfl
    exact nonbot y.rem y hyne (Nat.le_refl _)
  | mid m k => exact nonbot _ _ (by simp) (Nat.le_refl _)
  | top => exact nonbot _ _ (by simp) (Nat.le_refl _)

theorem unboundedChainsLat_not_heightLe (h : Nat) : ¬ unboundedChainsLat.HeightLe h := by
  intro hh
  have hchain := hh (h + 1) (fun i => .mid (h + 1) i) (by
    intro i hi
    refine ⟨Or.inr ⟨rfl, Nat.le_succ i, hi⟩, by simp⟩)
  omega

/-- The ascending chain condition is strictly weaker than a finite height bound. -/
theorem acc_strictly_weaker_than_heightLe :
    unboundedChainsLat.IsJSL ∧ unboundedChainsLat.AscendingChainCondition ∧
      ∀ h, ¬ unboundedChainsLat.HeightLe h :=
  ⟨unboundedChainsLat_isJSL, unboundedChainsLat_acc, unboundedChainsLat_not_heightLe⟩

/-! ### `Int` with a bottom element (no ascending chain condition) -/

/-- `Int` with an explicit bottom element `⊥`. -/
inductive WithBotInt where
  | bot
  | val (z : Int)
  deriving DecidableEq

namespace WithBotInt

def le : WithBotInt → WithBotInt → Prop
  | bot, _ => True
  | val _, bot => False
  | val a, val b => a ≤ b

def join : WithBotInt → WithBotInt → WithBotInt
  | bot, b => b
  | a, bot => a
  | val a, val b => val (max a b)

end WithBotInt

def withBotIntLat : Lat WithBotInt := ⟨WithBotInt.le, WithBotInt.join, .bot⟩

theorem withBotIntLat_isJSL : withBotIntLat.IsJSL where
  refl a := by cases a <;> simp [withBotIntLat, WithBotInt.le]
  trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp [withBotIntLat, WithBotInt.le] at hab hbc ⊢ <;> omega
  antisymm a b hab hba := by
    cases a <;> cases b <;> simp [withBotIntLat, WithBotInt.le] at hab hba ⊢ <;> omega
  join_le_iff a b c := by
    cases a <;> cases b <;> cases c <;>
      simp [withBotIntLat, WithBotInt.le, WithBotInt.join, Int.max_def] <;> split <;> omega
  bot_le a := by simp [withBotIntLat, WithBotInt.le]

/-- Negative example: `withBotIntLat` violates the ascending chain condition. -/
theorem withBotIntLat_not_acc : ¬ withBotIntLat.AscendingChainCondition := by
  intro hwf
  have : ∀ a : WithBotInt, Acc (fun a b => withBotIntLat.lt b a) a → False := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      cases a with
      | bot => exact ih (.val 0) ⟨by simp [withBotIntLat, WithBotInt.le], by simp⟩
      | val z => exact ih (.val (z + 1)) ⟨by simp [withBotIntLat, WithBotInt.le]; omega, by simp; omega⟩
  exact this .bot (hwf.apply .bot)

/-! ### Finite chains -/

/-- Finite chain `0 < 1 < ... < h` of height `h`. -/
def finChainLat (h : Nat) : Lat (Fin (h + 1)) where
  le a b := a.val ≤ b.val
  join a b := if a.val ≤ b.val then b else a
  bot := ⟨0, Nat.zero_lt_succ h⟩

instance (h : Nat) : DecidableRel (finChainLat h).le :=
  fun a b => Nat.decLe a.val b.val

theorem finChainLat_isJSL (h : Nat) : (finChainLat h).IsJSL where
  refl a := Nat.le_refl a.val
  trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  antisymm _ _ h1 h2 := Fin.ext (Nat.le_antisymm h1 h2)
  join_le_iff a b c := by
    simp only [finChainLat]
    split <;> exact ⟨fun hc => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => by omega⟩
  bot_le a := Nat.zero_le a.val

theorem finChainLat_heightLe (h : Nat) : (finChainLat h).HeightLe h :=
  Lat.heightLe_of_rank (fun a : Fin (h + 1) => a.val)
    (fun a b ⟨hle, hne⟩ => by
      have : a.val ≠ b.val := fun e => hne (Fin.ext e)
      exact Nat.lt_of_le_of_ne hle this)
    h (fun a => Nat.le_of_lt_succ a.isLt)

end Toy.Dataflow
