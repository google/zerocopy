/-
A toy borrow check for match guards: fake borrows and conflict detection.

These are definitions of a toy model. `borrowck` is meant to capture the check that rustc's
borrow checker performs on the fake borrows inserted by match lowering: a shallow fake borrow of
every switched place, a deep fake borrow of every deref-pattern scrutinee, all live across every
guard. It is not rustc's borrow checker.
-/
import ToyMatchGuard.Instances

namespace Toy.MatchGuard

/-- The two kinds of fake borrow. -/
inductive FakeKind where
  | shallow
  | deep
  deriving DecidableEq, Repr

/-- The fake borrows of a match: a shallow borrow of every place switched on by any arm, and a
deep borrow of every deref-pattern scrutinee of any arm. -/
def fakeBorrows (arms : List Arm) : List (Place × FakeKind) :=
  arms.flatMap (fun b => b.switchPlaces.map (fun p => (p, FakeKind.shallow))) ++
    arms.flatMap (fun b => b.derefScrutinees.map (fun p => (p, FakeKind.deep)))

/-- Whether a write at `w` conflicts with a fake borrow of kind `k` on place `p`
(computed with `List.isPrefixOf`). -/
def conflicts : FakeKind → Place → Place → Bool
  | .shallow, p, w => w.isPrefixOf p
  | .deep, p, w => w.isPrefixOf p || p.isPrefixOf w

/-- The toy borrow check: accepts a match iff no guard write conflicts with any fake borrow. -/
def borrowck (arms : List Arm) : Bool :=
  arms.all (fun a => a.guardWrites.all (fun w =>
    (fakeBorrows arms).all (fun pk => !conflicts pk.2 pk.1 w)))

theorem conflicts_shallow_iff (p w : Place) :
    conflicts .shallow p w = true ↔ ShallowConflict w p := by
  simp [conflicts, ShallowConflict, List.isPrefixOf_iff_prefix]

theorem conflicts_deep_iff (p w : Place) :
    conflicts .deep p w = true ↔ DeepConflict w p := by
  simp [conflicts, DeepConflict, List.isPrefixOf_iff_prefix]

/-- **The toy borrow check decides static freezing.** For every arm list `arms`,
`borrowck arms = true` iff `ShallowFrozenAll arms` and `DeepFrozenAll arms`. -/
theorem borrowck_eq_true_iff (arms : List Arm) :
    borrowck arms = true ↔ ShallowFrozenAll arms ∧ DeepFrozenAll arms := by
  simp only [borrowck, List.all_eq_true, fakeBorrows, List.mem_append, List.mem_flatMap,
    List.mem_map, Bool.not_eq_true']
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha w hw b hb p hp hc
      have := h a ha w hw (p, .shallow) (Or.inl ⟨b, hb, p, hp, rfl⟩)
      rw [(conflicts_shallow_iff p w).mpr hc] at this
      cases this
    · intro a ha w hw b hb p hp hc
      have := h a ha w hw (p, .deep) (Or.inr ⟨b, hb, p, hp, rfl⟩)
      rw [(conflicts_deep_iff p w).mpr hc] at this
      cases this
  · rintro ⟨hs, hd⟩ a ha w hw pk hpk
    rcases hpk with ⟨b, hb, p, hp, rfl⟩ | ⟨b, hb, p, hp, rfl⟩
    · cases hc : conflicts .shallow p w
      · rfl
      · exact absurd ((conflicts_shallow_iff p w).mp hc) (hs a ha w hw b hb p hp)
    · cases hc : conflicts .deep p w
      · rfl
      · exact absurd ((conflicts_deep_iff p w).mp hc) (hd a ha w hw b hb p hp)

/-- **Soundness of the toy borrow check.** For every value domain `Dom`, every arm list `arms`
accepted by `borrowck` and exhaustive on `Dom`, and every `v` in `Dom`, `runMatch arms v` does
not reach `Unreachable`. -/
theorem runMatch_not_unreachable_of_borrowck_of_exhaustive (Dom : Val → Prop) (arms : List Arm)
    (hck : borrowck arms = true) (hex : Exhaustive Dom arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := by
  obtain ⟨hs, hd⟩ := (borrowck_eq_true_iff arms).mp hck
  exact runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll Dom arms hex
    hs hd v hv

/-- Positive example (`borrowck`): the check accepts `shallowGuardArms`. -/
theorem borrowck_shallowGuardArms : borrowck shallowGuardArms = true := by decide

/-- Negative example (`borrowck`): the check rejects `reassignArms`. -/
theorem borrowck_reassignArms : borrowck reassignArms = false := by decide

/-- Negative example (`borrowck`): the check rejects `boxBoolArms` (deep conflict). -/
theorem borrowck_boxBoolArms : borrowck boxBoolArms = false := by decide

/-- **Incompleteness of the toy borrow check.** `sameVariantArms` is rejected by `borrowck`, is
exhaustive on `OptIntDom`, and for every `v` in `OptIntDom` its lowered execution does not reach
`Unreachable` (its guard reassigns the scrutinee to a value with the same variant, and every test
of `sameVariantArms` reads the variant at `[]`). -/
theorem sameVariantArms_rejected_exhaustive_and_never_unreachable :
    borrowck sameVariantArms = false ∧ Exhaustive OptIntDom sameVariantArms ∧
      ∀ v, OptIntDom v → (runMatch sameVariantArms v).reachesUnreachable = false := by
  refine ⟨by decide, sameVariantArms_exhaustive, ?_⟩
  intro v hv
  rcases hv with rfl | ⟨n, rfl⟩
  · decide
  · rfl

/-- Example (`runMatch`): on `Some(0)`, `sameVariantArms` selects arm `2` with post-guard memory
`Some(5)`: the guard's same-variant write changes the memory that the selected arm runs with. -/
theorem runMatch_sameVariantArms_some0 :
    (match runMatch sameVariantArms (vSome (.int 0)) with
      | .arm i _ mem => decide (i = 2 ∧ mem = vSome (.int 5))
      | .unreachable _ => false) = true := by decide

/-- **Counterexample (borrow check acceptance).** `reassignArms` is rejected by `borrowck`, is
exhaustive on `RefOptBoolDom`, and reaches `Unreachable` on `&Some(true)`. -/
theorem reassignArms_rejected_exhaustive_and_reaches_unreachable :
    borrowck reassignArms = false ∧ Exhaustive RefOptBoolDom reassignArms ∧
      RefOptBoolDom (.box (vSome vTrue)) ∧
      (runMatch reassignArms (.box (vSome vTrue))).reachesUnreachable = true :=
  ⟨by decide, reassignArms_exhaustive, Or.inr (Or.inr rfl), by decide⟩

/-- **Counterexample (exhaustiveness, borrow-check form).** `missingArms` is accepted by `borrowck`,
is not exhaustive on `OptBoolDom`, and reaches `Unreachable` on `Some(false)`. -/
theorem missingArms_accepted_and_reaches_unreachable :
    borrowck missingArms = true ∧ ¬ Exhaustive OptBoolDom missingArms ∧
      OptBoolDom (vSome vFalse) ∧ (runMatch missingArms (vSome vFalse)).reachesUnreachable = true :=
  ⟨by decide, missingArms_frozen_not_exhaustive_and_reaches_unreachable.1, Or.inr (Or.inl rfl),
    by decide⟩

/-- **Counterexample (domain membership, borrow-check form).** `boolArms` is accepted by
`borrowck` and exhaustive on `BoolDom`, and reaches `Unreachable` on the integer `0`, which is
not in `BoolDom`. -/
theorem boolArms_accepted_and_reaches_unreachable_outside_dom :
    borrowck boolArms = true ∧ Exhaustive BoolDom boolArms ∧ ¬ BoolDom (.int 0) ∧
      (runMatch boolArms (.int 0)).reachesUnreachable = true :=
  ⟨by decide, boolArms_exhaustive, by unfold BoolDom; decide, by decide⟩

/-- **Non-vacuity (borrow-check soundness, joint).** `mixedStaticArms` is accepted by `borrowck`
and is exhaustive on `OptPairBoxBoolDom`, which is inhabited; its fake borrows include a shallow
borrow of `[]` and a deep borrow of `[.field 1 0, .field 0 0]`, and its guard writes
`[.field 1 0, .field 0 1]`. -/
theorem mixedStaticArms_accepted_exhaustive :
    borrowck mixedStaticArms = true ∧ Exhaustive OptPairBoxBoolDom mixedStaticArms ∧
      OptPairBoxBoolDom (vSome (.ctor 0 [.box vFalse, vFalse])) ∧
      ([], FakeKind.shallow) ∈ fakeBorrows mixedStaticArms ∧
      ([.field 1 0, .field 0 0], FakeKind.deep) ∈ fakeBorrows mixedStaticArms ∧
      mixedStaticArms.map Arm.guardWrites = [[], [], [[.field 1 0, .field 0 1]], []] :=
  ⟨by decide, mixedStaticArms_exhaustive, Or.inr ⟨vFalse, vFalse, Or.inl rfl, Or.inl rfl, rfl⟩,
    by decide, by decide, by decide⟩

end Toy.MatchGuard
