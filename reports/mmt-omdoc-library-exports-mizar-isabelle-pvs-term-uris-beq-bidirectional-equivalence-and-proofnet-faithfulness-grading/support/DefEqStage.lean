-- Micro-probe of the definitional-equality stage used by the BEq reference
-- implementation (equivalence/def_eq.py builds exactly this shape of input:
-- two `sorry`-proved theorems followed by `example : thm_P = thm_Q := by rfl`).
-- `thm_P = thm_Q` only typechecks when the two statement types are
-- definitionally equal, so success of the `example` is the test.

namespace Case1  -- surface-different, definitionally equal: accepted
theorem thm_P : (2 : Nat) + 2 = 4 := sorry
theorem thm_Q : Nat.add 2 2 = 4 := by sorry
example : thm_P = thm_Q := by rfl
end Case1

namespace Case2  -- hypothesis order swapped: logically equivalent, not defeq: rejected
theorem thm_P (p q : Prop) (hp : p) (hq : q) : p ∧ q := sorry
theorem thm_Q (p q : Prop) (hq : q) (hp : p) : p ∧ q := by sorry
example : thm_P = thm_Q := by rfl
end Case2

namespace Case3  -- the same pair, bidirectional proof with only `exact`: accepted
theorem thm_P (p q : Prop) (hp : p) (hq : q) : p ∧ q := sorry
theorem thm_Q (p q : Prop) (hq : q) (hp : p) : p ∧ q := by
  exact thm_P p q hp hq
theorem thm_P' (p q : Prop) (hq : q) (hp : p) : p ∧ q := sorry
theorem thm_Q' (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact thm_P' p q hq hp
end Case3

namespace Case4  -- a `sorry` proof is reported with warning severity, not error severity
theorem thm_P : (1 : Nat) = 1 := sorry
theorem thm_Q : (1 : Nat) = 2 := by
  sorry -- mentions thm_P only in this comment
end Case4
