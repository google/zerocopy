import ToyUB.Undef
import ToyUB.Poison

/-!
# Auxiliary lemmas

Model-independent facts about outcome lists and refinement, and parity facts about
`w`-bit integers used by the counterexamples.
-/

namespace Toy.UB

variable {V α β : Type}

theorem mayUB_iff {S : List (Outcome V)} : MayUB S ↔ Outcome.ub ∈ S := by
  unfold MayUB
  constructor
  · rintro ⟨o, h, hu⟩
    cases o with
    | ub => exact h
    | val _ => simp [Outcome.isUB] at hu
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_bind1 {A : List (Outcome α)} {f : α → List (Outcome β)} {o : Outcome β} :
    o ∈ bind1 A f ↔ (o = .ub ∧ Outcome.ub ∈ A) ∨ ∃ a, Outcome.val a ∈ A ∧ o ∈ f a := by
  unfold bind1
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, ho⟩
    cases x with
    | ub => exact Or.inl ⟨by simpa using ho, hx⟩
    | val a => exact Or.inr ⟨a, hx, ho⟩
  · rintro (⟨rfl, h⟩ | ⟨a, ha, ho⟩)
    · exact ⟨.ub, h, by simp⟩
    · exact ⟨.val a, ha, ho⟩

@[simp] theorem bind1_val_singleton {a : α} {f : α → List (Outcome β)} :
    bind1 [Outcome.val a] f = f a := by
  simp [bind1]

@[simp] theorem bind1_ub_singleton {f : α → List (Outcome β)} :
    bind1 [Outcome.ub] f = [Outcome.ub] := by
  simp [bind1]

theorem ub_mem_bind1_of_ub_mem {A : List (Outcome α)} {f : α → List (Outcome β)}
    (h : Outcome.ub ∈ A) : Outcome.ub ∈ bind1 A f :=
  mem_bind1.mpr (Or.inl ⟨rfl, h⟩)

theorem outRef_of_mayUB {R : V → V → Prop} {T S : List (Outcome V)} (h : MayUB S) :
    OutRef R T S := Or.inl h

theorem outRef_refl {R : V → V → Prop} (hR : ∀ v, R v v) (S : List (Outcome V)) :
    OutRef R S S := by
  by_cases h : MayUB S
  · exact Or.inl h
  · refine Or.inr fun o ho => ⟨o, ho, ?_⟩
    cases o with
    | ub => exact absurd (mayUB_iff.mpr ho) h
    | val v => exact hR v

theorem outRef_of_subset {R : V → V → Prop} (hR : ∀ v, R v v) {T S : List (Outcome V)}
    (h : ∀ o ∈ T, o ∈ S) : OutRef R T S := by
  rcases outRef_refl hR S with hS | hS
  · exact Or.inl hS
  · exact Or.inr fun o ho => hS o (h o ho)

theorem outRef_trans {R : V → V → Prop} (hR : ∀ a b c, R a b → R b c → R a c)
    {T S U : List (Outcome V)} (h1 : OutRef R T S) (h2 : OutRef R S U) : OutRef R T U := by
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · rcases h1 with h1 | h1
    · obtain ⟨o', ho', hle⟩ := h2 _ (mayUB_iff.mp h1)
      cases o' <;> simp [Outcome.LeVal] at hle
    · refine Or.inr fun o ho => ?_
      obtain ⟨o', ho', h⟩ := h1 o ho
      obtain ⟨o'', ho'', h'⟩ := h2 o' ho'
      refine ⟨o'', ho'', ?_⟩
      cases o <;> cases o' <;> cases o'' <;> simp_all [Outcome.LeVal]
      exact hR _ _ _ h h'

theorem USet.Sub.refl {w : Nat} (A : USet w) : USet.Sub A A := fun _ h => h

theorem USet.Sub.trans {w : Nat} {A B C : USet w} (h1 : USet.Sub A B) (h2 : USet.Sub B C) :
    USet.Sub A C := fun z h => h2 z (h1 z h)

theorem PVal.Refines.refl {w : Nat} (v : PVal w) : PVal.Refines v v := by
  cases v <;> simp [PVal.Refines]

theorem PVal.Refines.trans {w : Nat} {a b c : PVal w} (h1 : PVal.Refines a b)
    (h2 : PVal.Refines b c) : PVal.Refines a c := by
  cases c with
  | poison => trivial
  | int v =>
    simp only [PVal.Refines] at h2
    subst h2
    exact h1

/-! ### Parity of `w`-bit integers -/

theorem two_dvd_two_pow {w : Nat} (hw : 1 ≤ w) : 2 ∣ 2 ^ w :=
  ⟨2 ^ (w - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩

/-- `v + v` is even at every width (at width `0` every value is `0`). -/
theorem toNat_add_self_mod_two {w : Nat} (v : BitVec w) : (v + v).toNat % 2 = 0 := by
  rw [BitVec.toNat_add]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Nat.mod_one]
  · rw [Nat.mod_mod_of_dvd _ (two_dvd_two_pow hw)]
    omega

theorem toNat_one_mod_two {w : Nat} (hw : 1 ≤ w) : (1#w).toNat % 2 = 1 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]

theorem one_ne_add_self {w : Nat} (hw : 1 ≤ w) (v : BitVec w) : (1#w) ≠ v + v := by
  intro h
  have h1 := toNat_one_mod_two hw
  rw [h, toNat_add_self_mod_two] at h1
  exact absurd h1 (by decide)

theorem one_ne_zero_bv {w : Nat} (hw : 1 ≤ w) : (1#w) ≠ 0#w := by
  intro h
  have h1 := toNat_one_mod_two hw
  rw [h] at h1
  simp at h1

theorem two_mul_eq_add_self {w : Nat} (v : BitVec w) : BitVec.ofNat w 2 * v = v + v :=
  BitVec.two_mul

theorem bv_zero_eq {v : BitVec 0} : v = 0#0 := BitVec.eq_nil v

/-! ### Refinement is a preorder (both models) -/

/-- Reflexivity of undef-model refinement. -/
theorem refinesU_refl (w : Nat) (e : Expr) : RefinesU w e e :=
  fun _ _ => outRef_refl USet.Sub.refl _

/-- Transitivity of undef-model refinement. -/
theorem refinesU_trans (w : Nat) {a b c : Expr} (hab : RefinesU w a b) (hbc : RefinesU w b c) :
    RefinesU w a c :=
  fun ρ hρ => outRef_trans (R := USet.Sub) (fun _ _ _ h1 h2 => USet.Sub.trans h1 h2) (hab ρ hρ) (hbc ρ hρ)

/-- Reflexivity of poison(+freeze)-model refinement. -/
theorem refinesP_refl (w : Nat) (e : Expr) : RefinesP w e e :=
  fun _ => outRef_refl PVal.Refines.refl _

/-- Transitivity of poison(+freeze)-model refinement. -/
theorem refinesP_trans (w : Nat) {a b c : Expr} (hab : RefinesP w a b) (hbc : RefinesP w b c) :
    RefinesP w a c :=
  fun ρ => outRef_trans (R := PVal.Refines) (fun _ _ _ h1 h2 => PVal.Refines.trans h1 h2) (hab ρ) (hbc ρ)

end Toy.UB
