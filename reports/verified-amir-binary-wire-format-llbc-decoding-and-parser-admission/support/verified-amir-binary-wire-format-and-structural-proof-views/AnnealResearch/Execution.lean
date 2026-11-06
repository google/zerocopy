import Std

/-!
Finite-prefix safety research pilot. This module is not a Rust semantics.

`Step` is a fixed, justified execution subject: any prediction/strategy has
already been resolved coherently. Instantiating `Step` with every raw angelic
guess would change those guesses into demonic alternatives and is not licensed.
`Allowed` is an explicit classification policy, not a theorem about Rust stops.
-/

namespace AnnealResearch.Execution

universe u

inductive Reach {S : Type u} (Step : S → S → Prop) : S → S → Prop where
  | refl (s : S) : Reach Step s s
  | tail {s t v : S} : Reach Step s t → Step t v → Reach Step s v

theorem Reach.trans {S : Type u} {Step : S → S → Prop} {s t v : S}
    (first : Reach Step s t) (second : Reach Step t v) : Reach Step s v := by
  induction second with
  | refl => exact first
  | tail _ edge ih => exact Reach.tail ih edge

def NoUB {S : Type u} (Step : S → S → Prop) (Bad : S → Prop) (initial : S) : Prop :=
  ∀ reached, Reach Step initial reached → ¬ Bad reached

def ReachableProgress {S : Type u} (Step : S → S → Prop)
    (Allowed : S → Prop) (initial : S) : Prop :=
  ∀ reached, Reach Step initial reached → Allowed reached ∨ ∃ next, Step reached next

def Verified {S : Type u} (Step : S → S → Prop) (Bad Allowed : S → Prop)
    (initial : S) : Prop :=
  NoUB Step Bad initial ∧ ReachableProgress Step Allowed initial

theorem invariant_reachable {S : Type u} {Step : S → S → Prop}
    {Invariant : S → Prop} {initial reached : S}
    (initialInvariant : Invariant initial)
    (preservation : ∀ {s t}, Invariant s → Step s t → Invariant t)
    (path : Reach Step initial reached) : Invariant reached := by
  induction path with
  | refl => exact initialInvariant
  | tail _ edge ih => exact preservation ih edge

theorem invariant_noUB {S : Type u} {Step : S → S → Prop}
    {Bad Invariant : S → Prop} {initial : S}
    (initialInvariant : Invariant initial)
    (preservation : ∀ {s t}, Invariant s → Step s t → Invariant t)
    (excludesBad : ∀ s, Invariant s → ¬ Bad s) : NoUB Step Bad initial := by
  intro reached path
  exact excludesBad reached (invariant_reachable initialInvariant preservation path)

theorem bad_prefix_not_noUB {S : Type u} {Step : S → S → Prop}
    {Bad : S → Prop} {initial reached : S}
    (path : Reach Step initial reached) (bad : Bad reached) :
    ¬ NoUB Step Bad initial := by
  intro safe
  exact safe reached path bad

theorem NoUB.after_step {S : Type u} {Step : S → S → Prop}
    {Bad : S → Prop} {s t : S} (safe : NoUB Step Bad s) (edge : Step s t) :
    NoUB Step Bad t := by
  intro reached path
  exact safe reached ((Reach.tail (Reach.refl s) edge).trans path)

theorem invariant_verified {S : Type u} {Step : S → S → Prop}
    {Bad Allowed Invariant : S → Prop} {initial : S}
    (initialInvariant : Invariant initial)
    (preservation : ∀ {s t}, Invariant s → Step s t → Invariant t)
    (excludesBad : ∀ s, Invariant s → ¬ Bad s)
    (classification : ∀ s, Invariant s → Allowed s ∨ ∃ next, Step s next) :
    Verified Step Bad Allowed initial := by
  constructor
  · exact invariant_noUB initialInvariant preservation excludesBad
  · intro reached path
    exact classification reached (invariant_reachable initialInvariant preservation path)

/- Concrete prefix discriminators. UB is visible before its continuation. -/
namespace PrefixExamples

inductive State where
  | spin
  | beforeUBSpin
  | badSpin
  | beforeUBEmpty
  | badEmpty
  | emptyDemonic
  | unsupported
  deriving DecidableEq

inductive Step : State → State → Prop where
  | spin : Step .spin .spin
  | enterUBSpin : Step .beforeUBSpin .badSpin
  | continueSpin : Step .badSpin .spin
  | enterUBEmpty : Step .beforeUBEmpty .badEmpty
  | continueEmpty : Step .badEmpty .emptyDemonic

def Bad : State → Prop
  | .badSpin | .badEmpty => True
  | _ => False

def Allowed : State → Prop
  | .emptyDemonic => True
  | _ => False

theorem spin_verified : Verified Step Bad Allowed .spin := by
  apply invariant_verified (Invariant := fun s => s = .spin) rfl
  · intro s t hs edge
    subst s
    cases edge
    rfl
  · intro s hs
    subst s
    exact False.elim
  · intro s hs
    subst s
    exact Or.inr ⟨.spin, Step.spin⟩

-- This is an actual infinite sequence of enabled safe steps, without fairness.
def spinRun (_ : Nat) : State := .spin

theorem spin_progresses_forever : ∀ n, Step (spinRun n) (spinRun (n + 1)) := by
  intro n
  exact Step.spin

theorem ub_then_spin_unsafe : ¬ NoUB Step Bad .beforeUBSpin := by
  exact bad_prefix_not_noUB (Reach.tail (Reach.refl _) Step.enterUBSpin) True.intro

theorem ub_then_empty_unsafe : ¬ NoUB Step Bad .beforeUBEmpty := by
  exact bad_prefix_not_noUB (Reach.tail (Reach.refl _) Step.enterUBEmpty) True.intro

theorem unsupported_noUB : NoUB Step Bad .unsupported := by
  apply invariant_noUB (Invariant := fun s => s = .unsupported) rfl
  · intro s t hs edge
    subst s
    cases edge
  · intro s hs
    subst s
    exact False.elim

theorem unsupported_not_verified : ¬ Verified Step Bad Allowed .unsupported := by
  intro verified
  have classified := verified.2 .unsupported (Reach.refl _)
  rcases classified with allowed | ⟨next, edge⟩
  · exact allowed
  · cases edge

theorem empty_demonic_verified : Verified Step Bad Allowed .emptyDemonic := by
  apply invariant_verified (Invariant := fun s => s = .emptyDemonic) rfl
  · intro s t hs edge
    subst s
    cases edge
  · intro s hs
    subst s
    exact False.elim
  · intro s hs
    subst s
    exact Or.inl True.intro

theorem empty_demonic_no_successor : ¬ ∃ next, Step .emptyDemonic next := by
  rintro ⟨next, edge⟩
  cases edge

end PrefixExamples

/- A single prediction p permits p safe ticks and then UB. SafeFor k p says
   the first k ticks avoid UB. The witness must be fixed across every prefix. -/
namespace Prediction

def SafeFor (fuel prediction : Nat) : Prop := fuel ≤ prediction

theorem countdown_nonuniform : ∀ fuel, ∃ prediction, SafeFor fuel prediction := by
  intro fuel
  exact ⟨fuel, Nat.le_refl fuel⟩

theorem no_uniform_countdown : ¬ ∃ prediction, ∀ fuel, SafeFor fuel prediction := by
  rintro ⟨prediction, safe⟩
  exact Nat.not_succ_le_self prediction (safe (prediction + 1))

theorem quantifier_exchange_fails :
    (∀ fuel, ∃ prediction, SafeFor fuel prediction) ∧
    ¬ (∃ prediction, ∀ fuel, SafeFor fuel prediction) :=
  ⟨countdown_nonuniform, no_uniform_countdown⟩

/- A monotone safety transformer for an illustrative causal game. Root makes
   one angelic Nat choice; ticks count down to the bad state ticks 0. This
   transformer is a proposed mathematical discriminator, not MiniRust authority. -/
inductive CountdownState where
  | root
  | ticks (remaining : Nat)

def countdownF (X : CountdownState → Prop) : CountdownState → Prop
  | .root => ∃ n, X (.ticks n)
  | .ticks 0 => False
  | .ticks (n + 1) => X (.ticks n)

theorem countdownF_mono {X Y : CountdownState → Prop}
    (inclusion : ∀ s, X s → Y s) : ∀ s, countdownF X s → countdownF Y s := by
  intro s membership
  cases s with
  | root =>
    obtain ⟨n, hn⟩ := membership
    exact ⟨n, inclusion _ hn⟩
  | ticks n =>
    cases n with
    | zero => exact False.elim membership
    | succ n => exact inclusion _ membership

def Approximant : Nat → CountdownState → Prop
  | 0, _ => True
  | k + 1, s => countdownF (Approximant k) s

theorem approximant_ticks (k n : Nat) : Approximant k (.ticks n) ↔ k ≤ n := by
  induction k generalizing n with
  | zero => simp [Approximant]
  | succ k ih =>
    cases n with
    | zero => simp [Approximant, countdownF]
    | succ n =>
      simpa only [Approximant, countdownF, Nat.succ_le_succ_iff] using ih n

theorem root_in_every_approximant : ∀ k, Approximant k .root := by
  intro k
  cases k with
  | zero => exact True.intro
  | succ k => exact ⟨k, (approximant_ticks k k).mpr (Nat.le_refl k)⟩

def OmegaIntersection (s : CountdownState) : Prop := ∀ k, Approximant k s

theorem no_ticks_in_omega (n : Nat) : ¬ OmegaIntersection (.ticks n) := by
  intro membership
  exact Nat.not_succ_le_self n ((approximant_ticks (n + 1) n).mp (membership (n + 1)))

theorem omega_intersection_not_postfixed :
    ¬ (∀ s, OmegaIntersection s → countdownF OmegaIntersection s) := by
  intro postfixed
  obtain ⟨n, hn⟩ := postfixed .root root_in_every_approximant
  exact no_ticks_in_omega n hn

-- Union of all postfixed predicates, the greatest safety fixed point below.
def GreatestSafety (s : CountdownState) : Prop :=
  ∃ X : CountdownState → Prop, X s ∧ ∀ t, X t → countdownF X t

theorem greatestSafety_closed {s : CountdownState} (safe : GreatestSafety s) :
    countdownF GreatestSafety s := by
  obtain ⟨X, member, closed⟩ := safe
  exact countdownF_mono (fun t ht => ⟨X, ht, closed⟩) s (closed s member)

theorem greatestSafety_unfold (s : CountdownState) :
    GreatestSafety s ↔ countdownF GreatestSafety s := by
  constructor
  · exact greatestSafety_closed
  · intro member
    refine ⟨countdownF GreatestSafety, member, ?_⟩
    intro t ht
    exact countdownF_mono (fun _ hu => greatestSafety_closed hu) t ht

theorem no_postfixed_ticks (X : CountdownState → Prop)
    (closed : ∀ t, X t → countdownF X t) : ∀ n, ¬ X (.ticks n) := by
  intro n
  induction n with
  | zero =>
    intro membership
    exact closed _ membership
  | succ n ih =>
    intro membership
    exact ih (closed _ membership)

theorem root_not_in_greatestSafety : ¬ GreatestSafety .root := by
  rintro ⟨X, member, closed⟩
  obtain ⟨n, hn⟩ := closed .root member
  exact no_postfixed_ticks X closed n hn

theorem finite_approximants_do_not_establish_greatestSafety :
    OmegaIntersection .root ∧ ¬ GreatestSafety .root :=
  ⟨root_in_every_approximant, root_not_in_greatestSafety⟩

end Prediction

/- Finite order/information alternatives only. These formulas do not select
   a normative interpretation of MiniRust predict or any Rust primitive. -/
namespace ChoiceScope

def CausalBefore : Prop := ∃ prediction : Bool, ∀ demonic : Bool, prediction = demonic
def PropheticBefore : Prop := ∀ demonic : Bool, ∃ prediction : Bool, prediction = demonic
def CausalAfter : Prop := ∃ strategy : Bool → Bool, ∀ demonic, strategy demonic = demonic

theorem causal_before_impossible : ¬ CausalBefore := by
  rintro ⟨prediction, wins⟩
  cases prediction with
  | false => have impossible := wins true; cases impossible
  | true => have impossible := wins false; cases impossible

theorem prophetic_before_possible : PropheticBefore := by
  intro demonic
  exact ⟨demonic, rfl⟩

theorem causal_after_possible : CausalAfter := by
  exact ⟨fun demonic => demonic, fun _ => rfl⟩

def observingAdversary (prediction : Bool) : Bool := !prediction

theorem observing_adversary_defeats_every_prediction :
    ∀ prediction, prediction ≠ observingAdversary prediction := by
  intro prediction
  cases prediction <;> decide

theorem order_and_information_discriminator :
    ¬ CausalBefore ∧ PropheticBefore ∧ CausalAfter :=
  ⟨causal_before_impossible, prophetic_before_possible, causal_after_possible⟩

end ChoiceScope

#print axioms invariant_noUB
#print axioms invariant_verified
#print axioms NoUB.after_step
#print axioms PrefixExamples.spin_verified
#print axioms PrefixExamples.spin_progresses_forever
#print axioms PrefixExamples.ub_then_spin_unsafe
#print axioms PrefixExamples.ub_then_empty_unsafe
#print axioms PrefixExamples.unsupported_noUB
#print axioms PrefixExamples.unsupported_not_verified
#print axioms PrefixExamples.empty_demonic_verified
#print axioms Prediction.quantifier_exchange_fails
#print axioms Prediction.greatestSafety_unfold
#print axioms Prediction.omega_intersection_not_postfixed
#print axioms Prediction.finite_approximants_do_not_establish_greatestSafety
#print axioms ChoiceScope.order_and_information_discriminator
#print axioms ChoiceScope.observing_adversary_defeats_every_prediction

end AnnealResearch.Execution
