/-
# A padded system with a divergent behaviour

The same construction as `ToyRice.Padded`, with three behaviours instead of two: a program
diverges (`none`), returns `true`, or returns `false`. Codes are literal programs `lit b n`, whose
behaviour is visible in their text, and hidden programs `hid b n`, whose behaviour is not; `n` is
padding. Admissible transformers are, outside a finite set of codes, either the identity or
functions of the visible part of the code (hidden codes lose their behaviour). The class contains
all constants and is closed under literal code-equality tests, and the fixpoint principle holds by
the fresh-padding obliviousness argument of `ToyRice.Padded`.

This system is the witness that all hypotheses of the restriction theorem
`not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial`
hold together with a nontrivial fragment ("the program halts") and a predicate ("returns `true`") that is
nontrivial on it. It is not a model of any real language.
-/
import ToyRice.Abstract

namespace Toy.Rice.PaddedDiv

/-- A code: a literal program `lit b n` or a hidden program `hid b n`, with behaviour `b`
(`none` = diverges) and padding `n`. -/
inductive Code where
  | lit (b : Option Bool) (n : Nat)
  | hid (b : Option Bool) (n : Nat)
  deriving DecidableEq

namespace Code

/-- The behaviour. -/
def beh : Code → Option Bool
  | lit b _ => b
  | hid b _ => b

/-- The padding. -/
def pad : Code → Nat
  | lit _ n => n
  | hid _ n => n

/-- The visible part of a code: hidden codes lose their behaviour. -/
def erase : Code → Code
  | lit b n => lit b n
  | hid _ n => hid none n

end Code

open Code

/-- Outside a finite set of codes, `f` is the identity. -/
def IdOffFinite (f : Code → Code) : Prop :=
  ∃ F : List Code, ∀ c, c ∉ F → f c = c

/-- Outside a finite set of codes, the output of `f` depends only on the input's visible part. -/
def VisOnlyOffFinite (f : Code → Code) : Prop :=
  ∃ (F : List Code) (h : Code → Code), ∀ c, c ∉ F → f c = h c.erase

/-- Admissible transformers. -/
def Admissible (f : Code → Code) : Prop := IdOffFinite f ∨ VisOnlyOffFinite f

/-- The padded system with divergence. -/
abbrev sys : System := ⟨Code, Option Bool, Code.beh, Admissible⟩

theorem exists_fresh_pad (F : List Code) : ∃ n, ∀ p ∈ F, p.pad < n := by
  induction F with
  | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | cons q F ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨max (q.pad + 1) n, fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with h | h
    · subst h; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (hn p h) (Nat.le_max_right _ _)

theorem not_mem_of_fresh {F : List Code} {n : Nat} (hn : ∀ p ∈ F, p.pad < n) (c : Code)
    (hc : c.pad = n) : c ∉ F := fun h => Nat.lt_irrefl n (hc ▸ hn _ h)

/-- The fixpoint principle holds (fresh-padding obliviousness argument). -/
theorem fixpointPrinciple : FixpointPrinciple sys := by
  intro f hf
  rcases hf with ⟨F, hF⟩ | ⟨F, h, hF⟩
  · obtain ⟨n, hn⟩ := exists_fresh_pad F
    exact ⟨hid none n, by rw [hF _ (not_mem_of_fresh hn _ rfl)]⟩
  · obtain ⟨n, hn⟩ := exists_fresh_pad F
    refine ⟨hid (h (hid none n)).beh n, ?_⟩
    show (f (hid (h (hid none n)).beh n)).beh = (h (hid none n)).beh
    rw [hF _ (not_mem_of_fresh hn _ rfl)]
    rfl

theorem constClosed : ConstClosed sys :=
  fun k => Or.inr ⟨[], fun _ => k, fun _ _ => rfl⟩

/-- The system is closed under literal code-equality tests. -/
theorem eqTestClosed : EqTestClosed sys := by
  intro f hf k a b
  rcases hf with ⟨F, hF⟩ | ⟨F, h, hF⟩
  · refine Or.inr ⟨F ++ [k], fun _ => b, fun c hc => ?_⟩
    have hcF : c ∉ F := fun h => hc (List.mem_append_left _ h)
    have hck : c ≠ k := fun h => hc (List.mem_append_right _ (by simp [h]))
    show (@ite _ (f c = k) (Classical.propDecidable _) a b) = b
    rw [hF c hcF]
    simp [hck]
  · refine Or.inr ⟨F, fun e => @ite _ (h e = k) (Classical.propDecidable _) a b, fun c hc => ?_⟩
    show (@ite _ (f c = k) (Classical.propDecidable _) a b) =
      (@ite _ (h c.erase = k) (Classical.propDecidable _) a b)
    rw [hF c hc]

/-- "The program halts." -/
def Halts (c : Code) : Prop := c.beh ≠ none

/-- "The program returns `true`." -/
def ReturnsTrue (c : Code) : Prop := c.beh = some true

theorem halts_extensional : Extensional sys Halts := by
  intro c d h
  show c.beh ≠ none ↔ d.beh ≠ none
  have h' : c.beh = d.beh := h
  rw [h']

theorem returnsTrue_extensional : Extensional sys ReturnsTrue := by
  intro c d h
  show c.beh = some true ↔ d.beh = some true
  have h' : c.beh = d.beh := h
  rw [h']

/-- On the halting fragment, "returns `true`" is nontrivial. -/
theorem returnsTrue_nontrivial_halting :
    NontrivialPred (fun x : {c // Halts c} => ReturnsTrue x.val) :=
  ⟨⟨⟨lit (some true) 0, fun h => by cases h⟩, rfl⟩,
    ⟨⟨lit (some false) 0, fun h => by cases h⟩, fun h => by
      have : (some false : Option Bool) = some true := h
      cases this⟩⟩

end Toy.Rice.PaddedDiv
