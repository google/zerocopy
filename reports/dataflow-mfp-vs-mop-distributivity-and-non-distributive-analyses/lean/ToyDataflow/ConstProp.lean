import ToyDataflow.MopMfp
import ToyDataflow.Diamond

/-!
# Constant propagation: a monotone, non-distributive framework

Per-variable flat lattice `⊥ ⊑ const c ⊑ ⊤` (`⊤` = not a constant), lifted
pointwise to the three variables `x, y, z`. Transfer functions model
`y := c; z := d` and `x := y + z` with strict abstract addition.

Modeling choice: `cpLat` is the *unsmashed* product `Flat³`. Its bottom
`⟨⊥, ⊥, ⊥⟩` is not a separate "unreachable" element, and a state can be `⊥` in
some variables and not in others. Constant assignments are therefore not strict
(`assignYZ_not_strict`). Presentations that use a single added bottom for
unreachable code (a lifted lattice `(Var → Flat)_⊥` with transfers that map that
bottom to itself) make every transfer strict; that variant is not modeled here.
Because `⊥` is the identity of `Flat.join`, an entry state that should mean
"value unknown" has to be `⊤` in that variable, not `⊥`; the results below hold
for every entry state `a`.
-/

namespace Toy.Dataflow

/-- The flat constant lattice over `Int`. -/
inductive Flat where
  | bot
  | const (c : Int)
  | top
  deriving DecidableEq, Repr

namespace Flat

/-- `a ⊑ b`: `a` is `⊥`, or `b` is `⊤`, or they are equal. -/
def le (a b : Flat) : Prop := a = bot ∨ b = top ∨ a = b

instance (a b : Flat) : Decidable (le a b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Join: two different constants join to `⊤`. -/
def join : Flat → Flat → Flat
  | bot, b => b
  | const c, bot => const c
  | const c, const d => if c = d then const c else top
  | const _, top => top
  | top, _ => top

/-- Abstract addition, strict in `⊥`. -/
def add : Flat → Flat → Flat
  | bot, _ => bot
  | const _, bot => bot
  | const c, const d => const (c + d)
  | const _, top => top
  | top, bot => bot
  | top, _ => top

/-- Height rank: `⊥ ↦ 0`, `const ↦ 1`, `⊤ ↦ 2`. -/
def rank : Flat → Nat
  | bot => 0
  | const _ => 1
  | top => 2

theorem le_refl (a : Flat) : le a a := Or.inr (Or.inr rfl)

theorem le_trans {a b c : Flat} (h1 : le a b) (h2 : le b c) : le a c := by
  unfold le at *
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;> simp_all

theorem le_antisymm {a b : Flat} (h1 : le a b) (h2 : le b a) : a = b := by
  unfold le at *
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;> simp_all

theorem join_le_iff (a b c : Flat) : le (join a b) c ↔ le a c ∧ le b c := by
  cases a <;> cases b <;> cases c <;> simp [join, le] <;> split <;> simp_all <;> omega

theorem bot_le (a : Flat) : le bot a := Or.inl rfl

theorem rank_lt {a b : Flat} (h1 : le a b) (h2 : a ≠ b) : rank a < rank b := by
  unfold le at h1
  rcases h1 with rfl | rfl | rfl
  · cases b <;> simp_all [rank]
  · cases a <;> simp_all [rank]
  · exact absurd rfl h2

theorem rank_le {a b : Flat} (h1 : le a b) : rank a ≤ rank b := by
  by_cases h : a = b
  · subst h; exact Nat.le_refl _
  · exact Nat.le_of_lt (rank_lt h1 h)

theorem rank_le_two (a : Flat) : rank a ≤ 2 := by cases a <;> simp [rank]

theorem add_mono {a a' b b' : Flat} (ha : le a a') (hb : le b b') : le (add a b) (add a' b') := by
  unfold le at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | (cases a <;> cases b <;> simp [add, le])
    | (cases a' <;> cases b' <;> simp [add, le])
    | (cases a <;> cases b' <;> simp [add, le])
    | (cases a' <;> cases b <;> simp [add, le])
    | (cases a <;> simp [add, le])
    | (cases a' <;> simp [add, le])
    | (cases b <;> simp [add, le])
    | (cases b' <;> simp [add, le])
    | exact le_refl _

end Flat

/-- The flat lattice as a `Lat`. -/
def flatLat : Lat Flat := ⟨Flat.le, Flat.join, Flat.bot⟩

/-- Positive example: the flat lattice satisfies every law. -/
theorem flatLat_isJSL : flatLat.IsJSL where
  refl := Flat.le_refl
  trans := fun _ _ _ => Flat.le_trans
  antisymm := fun _ _ => Flat.le_antisymm
  join_le_iff := Flat.join_le_iff
  bot_le := Flat.bot_le

/-- Negative example: two different constants are incomparable (so `join` must
go to `⊤`), and `⊤` is not below a constant. -/
theorem flat_const_incomparable :
    ¬ Flat.le (.const 1) (.const 2) ∧ ¬ Flat.le (.const 2) (.const 1) ∧
      ¬ Flat.le .top (.const 1) ∧ Flat.join (.const 1) (.const 2) = .top := by
  decide

/-- Abstract states for three variables `x, y, z` (pointwise lift of `Flat`). -/
structure St where
  x : Flat
  y : Flat
  z : Flat
  deriving DecidableEq, Repr

/-- The pointwise constant-propagation lattice on `{x, y, z}`. -/
def cpLat : Lat St where
  le s t := Flat.le s.x t.x ∧ Flat.le s.y t.y ∧ Flat.le s.z t.z
  join s t := ⟨Flat.join s.x t.x, Flat.join s.y t.y, Flat.join s.z t.z⟩
  bot := ⟨.bot, .bot, .bot⟩

instance (s t : St) : Decidable (cpLat.le s t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Positive example: `cpLat` satisfies every law. -/
theorem cpLat_isJSL : cpLat.IsJSL where
  refl := fun s => ⟨Flat.le_refl _, Flat.le_refl _, Flat.le_refl _⟩
  trans := fun _ _ _ h1 h2 =>
    ⟨Flat.le_trans h1.1 h2.1, Flat.le_trans h1.2.1 h2.2.1, Flat.le_trans h1.2.2 h2.2.2⟩
  antisymm := by
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h1 h2
    simp only [St.mk.injEq]
    exact ⟨Flat.le_antisymm h1.1 h2.1, Flat.le_antisymm h1.2.1 h2.2.1,
      Flat.le_antisymm h1.2.2 h2.2.2⟩
  join_le_iff := by
    intro s t u
    simp only [cpLat, Flat.join_le_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩; exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
    · rintro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩; exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
  bot_le := fun _ => ⟨Flat.bot_le _, Flat.bot_le _, Flat.bot_le _⟩

/-- Positive example: `cpLat` has height at most `6`. -/
theorem cpLat_heightLe : cpLat.HeightLe 6 := by
  refine Lat.heightLe_of_rank (fun s => s.x.rank + s.y.rank + s.z.rank) ?_ 6 ?_
  · rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ ⟨⟨h1, h2, h3⟩, hne⟩
    have r1 : a1.rank ≤ b1.rank := Flat.rank_le h1
    have r2 : a2.rank ≤ b2.rank := Flat.rank_le h2
    have r3 : a3.rank ≤ b3.rank := Flat.rank_le h3
    show a1.rank + a2.rank + a3.rank < b1.rank + b2.rank + b3.rank
    by_cases e1 : a1 = b1
    · by_cases e2 : a2 = b2
      · by_cases e3 : a3 = b3
        · exact absurd (by rw [e1, e2, e3]) hne
        · have : a3.rank < b3.rank := Flat.rank_lt h3 e3
          omega
      · have : a2.rank < b2.rank := Flat.rank_lt h2 e2
        omega
    · have : a1.rank < b1.rank := Flat.rank_lt h1 e1
      omega
  · intro s
    have := Flat.rank_le_two s.x
    have := Flat.rank_le_two s.y
    have := Flat.rank_le_two s.z
    omega

theorem cpLat_acc : cpLat.AscendingChainCondition := Lat.acc_of_heightLe cpLat_heightLe

/-- Transfer of `y := c; z := d`. -/
def assignYZ (c d : Int) (s : St) : St := { s with y := .const c, z := .const d }

/-- Transfer of `x := y + z`. -/
def assignXYZ (s : St) : St := { s with x := Flat.add s.y s.z }

theorem assignYZ_monotone (c d : Int) : Monotone cpLat (assignYZ c d) :=
  fun _ _ h => ⟨h.1, Flat.le_refl _, Flat.le_refl _⟩

theorem assignYZ_distributive (c d : Int) : Distributive cpLat (assignYZ c d) := by
  intro s t
  simp [assignYZ, cpLat, Flat.join]

/-- Negative example for `Strict`: a constant assignment maps `⟨⊥, ⊥, ⊥⟩` to a
state with constants. -/
theorem assignYZ_not_strict (c d : Int) : ¬ Strict cpLat (assignYZ c d) := by
  intro h
  have := congrArg St.y h
  simp [assignYZ, cpLat] at this

/-- Transfer of the copy `x := y`. -/
def copyXY (s : St) : St := { s with x := s.y }

/-- Positive example: copy assignments are distributive (as are constant
assignments, `assignYZ_distributive`); the non-distributivity below comes from the
binary operation in `x := y + z`. -/
theorem copyXY_distributive : Distributive cpLat copyXY := by
  intro s t
  simp [copyXY, cpLat]

theorem assignXYZ_monotone : Monotone cpLat assignXYZ :=
  fun _ _ h => ⟨Flat.add_mono h.2.1 h.2.2, h.2.1, h.2.2⟩

/-- Negative example for `Distributive`: `x := y + z` on the two branch states of
the diamond below. -/
theorem assignXYZ_not_distributive : ¬ Distributive cpLat assignXYZ := by
  intro h
  have := h ⟨.top, .const 1, .const 2⟩ ⟨.top, .const 2, .const 1⟩
  revert this
  decide

/-- The constant-propagation diamond: branches `y := 1; z := 2` and
`y := 2; z := 1`, then `x := y + z`, with arbitrary entry state `a`. -/
def cpDiamond (a : St) : CFG 5 St := diamond a (assignYZ 1 2) (assignYZ 2 1) assignXYZ

theorem cpDiamond_isLeastSolution (a : St) :
    IsLeastSolution cpLat (cpDiamond a) (diamondSol cpLat a (assignYZ 1 2) (assignYZ 2 1) assignXYZ) :=
  diamondSol_isLeastSolution_of_monotone cpLat_isJSL a (assignYZ_monotone 1 2)
    (assignYZ_monotone 2 1) assignXYZ_monotone

/-- Constant propagation is not exact on the diamond: for every entry state, MOP
after `x := y + z` is `x = 3, y = ⊤, z = ⊤`, while the least solution (MFP) there is
`x = ⊤, y = ⊤, z = ⊤`; so MFP is not MOP at node 4. -/
theorem cpDiamond_mfp_x_top_ne_mop_x_const3 (a : St) {x : Fin 5 → St}
    (hx : IsLeastSolution cpLat (cpDiamond a) x) :
    x 4 = ⟨.top, .top, .top⟩ ∧ IsMOPAt cpLat (cpDiamond a) 4 ⟨.const 3, .top, .top⟩ ∧
      ¬ IsMOPAt cpLat (cpDiamond a) 4 (x 4) := by
  have hx4 : x 4 = ⟨.top, .top, .top⟩ := by
    rw [diamond_isLeastSolution_eq cpLat_isJSL a _ _ _ hx]
    cases h : a.x <;> simp [diamondSol, assignXYZ, assignYZ, cpLat, Flat.join, Flat.add, h]
  have hm : IsMOPAt cpLat (cpDiamond a) 4 ⟨.const 3, .top, .top⟩ := by
    show IsMOPAt cpLat (diamond a (assignYZ 1 2) (assignYZ 2 1) assignXYZ) 4 _
    have := diamond_isMOPAt cpLat_isJSL a (assignYZ 1 2) (assignYZ 2 1) assignXYZ 4
    simpa [diamondMOP, assignXYZ, assignYZ, cpLat, Flat.join, Flat.add] using this
  refine ⟨hx4, hm, fun h => ?_⟩
  have := IsMOPAt.unique cpLat_isJSL h hm
  rw [hx4] at this
  simp at this

/-- The same counterexample with the least solution exposed: for every entry state
the diamond has a least solution, at node 4 it is `⟨⊤, ⊤, ⊤⟩`, the MOP value there
is `⟨3, ⊤, ⊤⟩`, and the least solution is not the MOP value. -/
theorem cpDiamond_exists_isLeastSolution_mfp_x_top_ne_mop_x_const3 (a : St) :
    ∃ x, IsLeastSolution cpLat (cpDiamond a) x ∧
      x 4 = ⟨.top, .top, .top⟩ ∧ IsMOPAt cpLat (cpDiamond a) 4 ⟨.const 3, .top, .top⟩ ∧
      ¬ IsMOPAt cpLat (cpDiamond a) 4 (x 4) :=
  ⟨_, cpDiamond_isLeastSolution a,
    cpDiamond_mfp_x_top_ne_mop_x_const3 a (cpDiamond_isLeastSolution a)⟩

/-- Counterexample for the hypothesis `hx` of `cpDiamond_mfp_x_top_ne_mop_x_const3`:
the assignment that is `⟨3, ⊤, ⊤⟩` everywhere is not a least solution, and the
conclusion fails for it (its value at node 4 is not `⟨⊤, ⊤, ⊤⟩`). -/
theorem cpDiamond_mfp_needs_least (a : St) :
    ¬ IsLeastSolution cpLat (cpDiamond a) (fun _ => ⟨.const 3, .top, .top⟩) ∧
      ¬ ((fun _ => (⟨.const 3, .top, .top⟩ : St)) 4 = ⟨.top, .top, .top⟩ ∧
        IsMOPAt cpLat (cpDiamond a) 4 ⟨.const 3, .top, .top⟩ ∧
        ¬ IsMOPAt cpLat (cpDiamond a) 4 ((fun _ => (⟨.const 3, .top, .top⟩ : St)) 4)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (cpDiamond_mfp_x_top_ne_mop_x_const3 a h).1
    simp at this
  · simp at h

/-- Positive control: with identical branches (`y := 1; z := 2` twice) the same
analysis is exact on the diamond and finds `x = 3`. -/
theorem cpDiamond_sameBranches_exact (a : St) {x : Fin 5 → St}
    (hx : IsLeastSolution cpLat (diamond a (assignYZ 1 2) (assignYZ 1 2) assignXYZ) x) :
    (∀ v, IsMOPAt cpLat (diamond a (assignYZ 1 2) (assignYZ 1 2) assignXYZ) v (x v)) ∧
      (x 4).x = .const 3 := by
  refine ⟨(diamond_isMOPAt_iff cpLat_isJSL a _ _ _ hx).2 (by rw [Lat.join_self cpLat_isJSL,
    Lat.join_self cpLat_isJSL]), ?_⟩
  rw [diamond_isLeastSolution_eq cpLat_isJSL a _ _ _ hx]
  simp [diamondSol, assignXYZ, assignYZ, cpLat, Flat.join, Flat.add]

end Toy.Dataflow
