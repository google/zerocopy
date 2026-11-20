/-
# A padded system with literal and hidden codes

A small system in which the fixpoint principle holds *and* several kinds of checker are
decided inside it, so that the abstract Rice theorem applies and yet does not forbid them.

Codes come in two forms, each carrying a behaviour bit `b` and a *padding* `n : ℕ`:
* `lit b n`: a *literal* program, whose behaviour is visible in its text (think
  `return b` followed by `n` bytes of comments);
* `hid b n`: a program whose behaviour is *hidden* (think an arbitrary program that happens to
  return `b`; its text does not reveal which).

The behaviour of either is `b`, and padding never affects behaviour, so every behaviour has
infinitely many codes.

A transformer can see a code only through its *visible part* `erase c`, which forgets the
behaviour bit of hidden codes. Admissible transformers are those that, outside some finite set
of codes, either leave the code unchanged (`IdOffFinite`) or produce an output that depends
only on the input's visible part (`VisOnlyOffFinite`). This class contains every constant,
every finite patch, and every switch on a checker that reads only visible parts (outside a
finite set), and it is closed under composition and under literal code-equality tests. The
fixpoint principle holds by a fresh-padding obliviousness argument: a hidden code whose padding
lies outside the finite exception set is seen by the transformer only through its visible part,
so its behaviour bit can be chosen to match the output.

In this system, inside a setting where the abstract Rice theorem applies:
* the nontrivial syntactic predicate "the padding is even" is decided inside the system;
* the checker "the code is a literal `true`" is sound for the extensional property "the
  behaviour is `true`", accepts infinitely many codes, and rejects every hidden code;
* finite allowlists are sound checkers.

Limitation: `Adm` is deliberately small: off a finite set, its transformers cannot read the
behaviour of hidden codes at all. The system shows that these phenomena are *consistent with*
the fixpoint principle; it is not a model of any real language.
-/
import ToyRice.Abstract

namespace Toy.Rice.Padded

/-- A code: a literal program `lit b n` or a hidden program `hid b n`, with behaviour bit `b`
and padding `n`. -/
inductive Code where
  | lit (b : Bool) (n : Nat)
  | hid (b : Bool) (n : Nat)
  deriving DecidableEq, Repr

namespace Code

/-- The behaviour bit. -/
def beh : Code → Bool
  | lit b _ => b
  | hid b _ => b

/-- The padding. -/
def pad : Code → Nat
  | lit _ n => n
  | hid _ n => n

/-- The visible part of a code: hidden codes lose their behaviour bit. -/
def erase : Code → Code
  | lit b n => lit b n
  | hid _ n => hid false n

@[simp] theorem beh_lit (b : Bool) (n : Nat) : (lit b n).beh = b := rfl
@[simp] theorem beh_hid (b : Bool) (n : Nat) : (hid b n).beh = b := rfl
@[simp] theorem pad_lit (b : Bool) (n : Nat) : (lit b n).pad = n := rfl
@[simp] theorem pad_hid (b : Bool) (n : Nat) : (hid b n).pad = n := rfl
@[simp] theorem erase_lit (b : Bool) (n : Nat) : (lit b n).erase = lit b n := rfl
@[simp] theorem erase_hid (b : Bool) (n : Nat) : (hid b n).erase = hid false n := rfl

@[simp] theorem pad_erase (c : Code) : c.erase.pad = c.pad := by cases c <;> rfl

end Code

open Code

/-- Outside a finite set of codes, `f` is the identity. -/
def IdOffFinite (f : Code → Code) : Prop :=
  ∃ F : List Code, ∀ c, c ∉ F → f c = c

/-- Outside a finite set of codes, the output of `f` depends only on the input's visible
part. -/
def VisOnlyOffFinite (f : Code → Code) : Prop :=
  ∃ (F : List Code) (h : Code → Code), ∀ c, c ∉ F → f c = h c.erase

/-- Admissible transformers of the padded system. -/
def Admissible (f : Code → Code) : Prop := IdOffFinite f ∨ VisOnlyOffFinite f

/-- The padded system: the behaviour of a code is its behaviour bit. -/
abbrev sys : System := ⟨Code, Bool, Code.beh, Admissible⟩

/-- A padding larger than every padding occurring in a finite list of codes. -/
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

/-- **The fixpoint principle holds in the padded system.** For a transformer that is the
identity off `F`, any code with fresh padding is fixed. For a transformer that reads only
visible parts off `F`, the hidden code `hid b n` with fresh `n` and `b` the behaviour of
`h (hid false n)` is a semantic fixed point. -/
theorem fixpointPrinciple : FixpointPrinciple sys := by
  intro f hf
  rcases hf with ⟨F, hF⟩ | ⟨F, h, hF⟩
  · obtain ⟨n, hn⟩ := exists_fresh_pad F
    exact ⟨hid true n, by rw [hF _ (not_mem_of_fresh hn _ rfl)]⟩
  · obtain ⟨n, hn⟩ := exists_fresh_pad F
    refine ⟨hid (h (hid false n)).beh n, ?_⟩
    show (f (hid (h (hid false n)).beh n)).beh = (h (hid false n)).beh
    rw [hF _ (not_mem_of_fresh hn _ rfl)]
    rfl

/-- Constants are admissible. -/
theorem constClosed : ConstClosed sys :=
  fun k => Or.inr ⟨[], fun _ => k, fun _ _ => rfl⟩

/-- Admissible transformers are closed under composition. -/
theorem compClosed : CompClosed sys := by
  intro f g hf hg
  rcases hg with ⟨G, hG⟩ | ⟨G, hg, hG⟩
  · rcases hf with ⟨F, hF⟩ | ⟨F, hf', hF⟩
    · refine Or.inl ⟨G ++ F, fun c hc => ?_⟩
      have hcG : c ∉ G := fun h => hc (List.mem_append_left _ h)
      have hcF : c ∉ F := fun h => hc (List.mem_append_right _ h)
      show f (g c) = c
      rw [hG c hcG, hF c hcF]
    · refine Or.inr ⟨G ++ F, hf', fun c hc => ?_⟩
      have hcG : c ∉ G := fun h => hc (List.mem_append_left _ h)
      have hcF : c ∉ F := fun h => hc (List.mem_append_right _ h)
      show f (g c) = hf' c.erase
      rw [hG _ hcG, hF _ hcF]
  · refine Or.inr ⟨G, fun c => f (hg c), fun c hc => ?_⟩
    show f (g c) = f (hg c.erase)
    rw [hG _ hc]

/-- A checker that reads only visible parts has admissible switches. -/
theorem switchAdmissible_of_visOnly {chk : Code → Bool} (h : ∀ c, chk c.erase = chk c) :
    SwitchAdmissible sys chk :=
  fun a b => Or.inr ⟨[], switch chk a b, fun c _ => by simp [switch, h]⟩

/-! ## Predicates and checkers -/

/-- Extensional: "the behaviour is `true`". -/
def BehTrue (c : Code) : Prop := c.beh = true

/-- Syntactic: "the padding is even". Not extensional. -/
def EvenPad (c : Code) : Prop := c.pad % 2 = 0

/-- Checker for `EvenPad`. -/
def evenPadCheck (c : Code) : Bool := c.pad % 2 == 0

/-- Syntactic certificate checker: accept exactly the literal `true` programs (any padding). -/
def litTrueCheck : Code → Bool
  | lit b _ => b
  | hid _ _ => false

/-- Allowlist checker: accept exactly the codes on a finite list. -/
def allowlist (L : List Code) (c : Code) : Bool := decide (c ∈ L)

-- Small cases.
example : evenPadCheck (lit true 4) = true := by decide
example : evenPadCheck (hid true 3) = false := by decide
example : litTrueCheck (lit true 9) = true := by decide
example : litTrueCheck (hid true 9) = false := by decide
example : allowlist [hid true 0] (hid true 0) = true := by decide
example : allowlist [hid true 0] (hid true 1) = false := by decide

theorem behTrue_extensional : Extensional sys BehTrue := by
  intro c d h
  show c.beh = true ↔ d.beh = true
  have h' : c.beh = d.beh := h
  rw [h']

theorem behTrue_nontrivial : NontrivialPred BehTrue :=
  ⟨⟨hid true 0, rfl⟩, ⟨hid false 0, fun h => Bool.noConfusion h⟩⟩

theorem evenPad_not_extensional : ¬ Extensional sys EvenPad := by
  intro h
  have := (h (hid true 0) (hid true 1) rfl).1 rfl
  exact absurd this (by unfold EvenPad; decide)

theorem evenPad_nontrivial : NontrivialPred EvenPad :=
  ⟨⟨hid true 0, rfl⟩, ⟨hid true 1, by unfold EvenPad; decide⟩⟩

theorem evenPadCheck_decides : Decides evenPadCheck EvenPad := by
  intro c; simp [evenPadCheck, EvenPad]

/-- Switches on `evenPadCheck` read only padding, so they are admissible. -/
theorem evenPadCheck_switchAdmissible : SwitchAdmissible sys evenPadCheck :=
  switchAdmissible_of_visOnly (fun c => by simp [evenPadCheck])

theorem litTrueCheck_erase (c : Code) : litTrueCheck c.erase = litTrueCheck c := by
  cases c <;> rfl

/-- Switches on `litTrueCheck` read only visible parts, so they are admissible. -/
theorem litTrueCheck_switchAdmissible : SwitchAdmissible sys litTrueCheck :=
  switchAdmissible_of_visOnly litTrueCheck_erase

theorem litTrueCheck_sound : SoundFor litTrueCheck BehTrue := by
  intro c h
  cases c with
  | lit b n => exact h
  | hid b n => exact Bool.noConfusion h

/-- Allowlist checkers are switch-admissible: off the list, every switch is constant. -/
theorem allowlist_switchAdmissible (L : List Code) : SwitchAdmissible sys (allowlist L) := by
  intro a b
  refine Or.inr ⟨L, fun _ => b, fun c hc => ?_⟩
  show cond (decide (c ∈ L)) a b = b
  simp [hc]

/-- An allowlist checker is sound for `P` exactly when every listed code satisfies `P`. -/
theorem allowlist_sound_iff (L : List Code) (P : Code → Prop) :
    SoundFor (allowlist L) P ↔ ∀ c ∈ L, P c := by
  constructor
  · intro h c hc; exact h c (by simp [allowlist, hc])
  · intro h c hc; exact h c (by simpa [allowlist] using hc)

/-- A sound (not deciding) checker can have an admissible *swapped* switch: with `a = hid true 0`
satisfying `BehTrue` and `b = hid false 0` violating it, the switch
`c ↦ if litTrueCheck c then b else a` is admissible. -/
theorem litTrueCheck_swappedSwitch_admissible :
    SoundFor litTrueCheck BehTrue ∧ BehTrue (hid true 0) ∧ ¬ BehTrue (hid false 0) ∧
      sys.Adm (switch litTrueCheck (hid false 0) (hid true 0)) :=
  ⟨litTrueCheck_sound, rfl, fun h => Bool.noConfusion h, litTrueCheck_switchAdmissible _ _⟩

/-- The padded system is closed under literal code-equality tests. -/
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

/-- "The code is a literal program": a fragment that is *not* closed under same behaviour. -/
def IsLit : Code → Prop
  | lit _ _ => True
  | hid _ _ => False

theorem isLit_not_extensional : ¬ Extensional sys IsLit := by
  intro h
  exact (h (lit true 0) (hid true 0) rfl).1 trivial

/-- `BehTrue` is not decided inside the padded system (from the abstract Rice theorem). -/
theorem behTrue_not_decidedInside : ¬ DecidedInside sys BehTrue :=
  not_decidedInside_of_fixpointPrinciple_extensional_nontrivial fixpointPrinciple
    behTrue_extensional behTrue_nontrivial

/-- In particular the checker that reads the behaviour bit is not switch-admissible. -/
theorem behCheck_not_switchAdmissible : ¬ SwitchAdmissible sys Code.beh := by
  intro h
  exact behTrue_not_decidedInside ⟨Code.beh, fun c => Iff.rfl, h⟩

/-! ## Main results -/

/-- **Syntactic predicates are not forbidden.** In the padded system, which has the fixpoint
principle, the nontrivial non-extensional predicate `EvenPad` is decided inside the system by
`evenPadCheck`. -/
theorem padded_fixpointPrinciple_and_evenPad_decidedInside :
    FixpointPrinciple sys ∧ ¬ Extensional sys EvenPad ∧ NontrivialPred EvenPad ∧
      Decides evenPadCheck EvenPad ∧ SwitchAdmissible sys evenPadCheck :=
  ⟨fixpointPrinciple, evenPad_not_extensional, evenPad_nontrivial, evenPadCheck_decides,
    evenPadCheck_switchAdmissible⟩

/-- **Nontrivial sound checkers for a syntactic subclass are not forbidden.** In the padded
system, which has the fixpoint principle, `BehTrue` is extensional, nontrivial, and not decided
inside the system; yet `litTrueCheck` is switch-admissible and sound for `BehTrue`, accepts the
infinitely many codes `lit true n`, and rejects every hidden code `hid true n` although those
satisfy `BehTrue`. -/
theorem padded_litTrueCheck_sound_infinite_incomplete :
    FixpointPrinciple sys ∧ Extensional sys BehTrue ∧ NontrivialPred BehTrue ∧
      ¬ DecidedInside sys BehTrue ∧
      SoundFor litTrueCheck BehTrue ∧ SwitchAdmissible sys litTrueCheck ∧
      (∀ n, litTrueCheck (lit true n) = true) ∧
      (∀ n, BehTrue (hid true n) ∧ litTrueCheck (hid true n) = false) :=
  ⟨fixpointPrinciple, behTrue_extensional, behTrue_nontrivial, behTrue_not_decidedInside,
    litTrueCheck_sound, litTrueCheck_switchAdmissible, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- **Finite allowlists are not forbidden.** In the padded system the allowlist for the single
code `hid true 0` is sound for `BehTrue`, switch-admissible, accepts that code, and rejects
`hid true 1`, which has the same behaviour. -/
theorem padded_allowlist_sound_nontrivial_incomplete :
    FixpointPrinciple sys ∧ Extensional sys BehTrue ∧
      SoundFor (allowlist [hid true 0]) BehTrue ∧
      SwitchAdmissible sys (allowlist [hid true 0]) ∧
      allowlist [hid true 0] (hid true 0) = true ∧
      (BehTrue (hid true 1) ∧ allowlist [hid true 0] (hid true 1) = false) :=
  ⟨fixpointPrinciple, behTrue_extensional,
    (allowlist_sound_iff _ _).2 (by intro c hc; simp at hc; subst hc; rfl),
    allowlist_switchAdmissible _, by decide, ⟨rfl, by decide⟩⟩

end Toy.Rice.Padded
