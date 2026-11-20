/-
# Lookup tables with a divergent code: a fragment that escapes Rice, and why

Codes are `Option Table`: `some t` is the lookup-table program `t` (it halts), and `none` is a
single divergent program. Behaviours are `Option (ℕ → ℕ)`: `none` is divergence. Admissible
transformers are the constant transformers and the *strict* extensions of table transformers
(`none ↦ none`, `some t ↦ some (p.run t)` for a `TProg` program `p`).

Strictness is the domain-theoretic reading of "the transformer runs its input first": on the
divergent program it produces the divergent program. In this system the fixpoint principle holds
for the domain-theoretic reason (constants have fixed points; strict maps fix `none`), so the
abstract Rice theorem applies to the full system.

Strictness also makes the full system degenerate as a host for checkers: only the two constant
checkers are switch-admissible in it (`switchAdmissible_const`), because a switch whose two
branches are halting codes does not send `none` to `none` and so must be constant. Hence no
nontrivial predicate whatever, extensional or syntactic, is decided inside the full system
(`not_decidedInside_of_nontrivial`, `isEmptyTable_not_decidedInside`), for the same reason as in
the flat-domain system (`Flat.switchAdmissible_const`). The non-degenerate object is the halting
fragment below, whose admissible class is proper and decides more than the constant checkers.

The *halting fragment* (`some t`) is closed under same behaviour. Restricted to it, the admissible
class stays a proper class (it is the table transformers), the fixpoint principle fails, and the
extensional property "halts and computes the zero function" is decided inside the restricted
system. The escape relies on strictness: the full-system transformer that agrees with a fragment
switch sends the divergent code to the divergent code, which models an analyzer allowed to diverge
outside the fragment. This system is not closed under literal code-equality tests
(`not_eqTestClosed`), and
`not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial`
shows that with such tests the escape is impossible.
-/
import ToyRice.Abstract
import ToyRice.Tables

namespace Toy.Rice.Lifted

open Toy.Rice.Tables

/-- Admissible transformers: constants, and strict extensions of `TProg` programs. -/
def Admissible (f : Option Table → Option Table) : Prop :=
  (∃ k, f = fun _ => k) ∨ (f none = none ∧ ∃ p : TProg, ∀ t, f (some t) = some (p.run t))

/-- The lifted lookup-table system. -/
abbrev sys : System := ⟨Option Table, Option (Nat → Nat), Option.map eval, Admissible⟩

/-- The fixpoint principle holds: constants are fixed at their value, strict maps at `none`. -/
theorem fixpointPrinciple : FixpointPrinciple sys := by
  intro f hf
  rcases hf with ⟨k, rfl⟩ | ⟨hnone, _⟩
  · exact ⟨k, rfl⟩
  · exact ⟨none, by show Option.map eval (f none) = Option.map eval none; rw [hnone]⟩

theorem constClosed : ConstClosed sys := fun k => Or.inl ⟨k, rfl⟩

/-- "The program halts": the fragment of table programs. -/
abbrev Halts (c : Option Table) : Prop := c.isSome = true

/-- The halting fragment. -/
abbrev totalSys : System := sys.restrict Halts

/-- "The program halts and computes the zero function." -/
def HaltsZero (c : Option Table) : Prop := ∃ t, c = some t ∧ IsZeroFn t

theorem halts_extensional : Extensional sys Halts := by
  intro c d h
  change Option.map eval c = Option.map eval d at h
  cases c <;> cases d <;> simp [Halts] at h ⊢

theorem haltsZero_extensional : Extensional sys HaltsZero := by
  intro c d h
  change Option.map eval c = Option.map eval d at h
  cases c with
  | none =>
    cases d with
    | none => exact Iff.rfl
    | some _ => simp at h
  | some t =>
    cases d with
    | none => simp at h
    | some s =>
      have hts : eval t = eval s := Option.some.inj h
      constructor
      · rintro ⟨_, h1, hz⟩
        cases h1
        exact ⟨s, rfl, fun n => (congrFun hts n) ▸ hz n⟩
      · rintro ⟨_, h1, hz⟩
        cases h1
        exact ⟨t, rfl, fun n => (congrFun hts n).symm ▸ hz n⟩

theorem haltsZero_nontrivial : NontrivialPred HaltsZero :=
  ⟨⟨some [], [], rfl, fun _ => rfl⟩, ⟨none, fun ⟨_, h, _⟩ => by cases h⟩⟩

theorem haltsZero_nontrivial_fragment :
    NontrivialPred (fun x : totalSys.Code => HaltsZero x.val) :=
  ⟨⟨⟨some [], rfl⟩, [], rfl, fun _ => rfl⟩,
    ⟨⟨some [(0, 1)], rfl⟩, fun ⟨t, h, hz⟩ => by
      cases h
      exact isZeroFn_neg' hz⟩⟩
where
  isZeroFn_neg' (hz : IsZeroFn [(0, 1)]) : False := by
    have := hz 0
    simp [eval] at this

/-- The checker on the fragment: run `zeroCheck` on the table. -/
def fragCheck (x : totalSys.Code) : Bool :=
  match x with
  | ⟨some t, _⟩ => zeroCheck t
  | ⟨none, h⟩ => absurd h (by decide)

theorem fragCheck_decides : Decides fragCheck (fun x => HaltsZero x.val) := by
  rintro ⟨c, hc⟩
  cases c with
  | none => exact absurd hc (by decide)
  | some t =>
    show zeroCheck t = true ↔ HaltsZero (some t)
    constructor
    · intro h; exact ⟨t, rfl, (zeroCheck_decides t).1 h⟩
    · rintro ⟨s, hs, hz⟩
      injection hs with hs
      subst hs
      exact (zeroCheck_decides _).2 hz

/-- Every switch on `fragCheck` is admissible in the fragment: its strict extension is a
full-system transformer agreeing with it literally on the fragment. -/
theorem fragCheck_switchAdmissible : SwitchAdmissible totalSys fragCheck := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  cases a with
  | none => exact absurd ha (by decide)
  | some ta =>
    cases b with
    | none => exact absurd hb (by decide)
    | some tb =>
      refine ⟨fun c => match c with
        | none => none
        | some t => some (cond (zeroCheck t) ta tb),
        Or.inr ⟨rfl, .branch (.allEntries (.evalAtKeyEq 0)) (.const ta) (.const tb),
          fun _ => rfl⟩, ?_⟩
      rintro ⟨c, hc⟩
      cases c with
      | none => exact absurd hc (by decide)
      | some t =>
        change (cond (zeroCheck t) (⟨some ta, ha⟩ : totalSys.Code) ⟨some tb, hb⟩).val =
          some (cond (zeroCheck t) ta tb)
        cases zeroCheck t <;> rfl

/-- The admissible class of the fragment is a proper class: the fragment map induced by
`List.tail` is not admissible. -/
theorem totalSys_adm_proper : ¬ ∀ g : totalSys.Code → totalSys.Code, totalSys.Adm g := by
  intro hall
  let gTail : totalSys.Code → totalSys.Code := fun x =>
    match x with
    | ⟨some t, _⟩ => ⟨some t.tail, rfl⟩
    | ⟨none, h⟩ => absurd h (by decide)
  obtain ⟨f, hf, hfg⟩ := hall gTail
  rcases hf with ⟨k, rfl⟩ | ⟨_, p, hp⟩
  · have h1 := hfg ⟨some [(0, 0), (1, 1)], rfl⟩
    have h2 := hfg ⟨some [], rfl⟩
    have h3 : (some [(1, 1)] : Option Table) = some [] := h1.trans h2.symm
    cases h3
  · apply tail_not_admissible
    refine ⟨p, fun t => ?_⟩
    have h1 := hfg ⟨some t, rfl⟩
    rw [hp t] at h1
    exact Option.some.inj h1.symm

/-- The fragment has no fixpoint principle: incrementing the value at `0` changes every
behaviour. -/
theorem total_not_fixpointPrinciple : ¬ FixpointPrinciple totalSys := by
  intro hfix
  let gBump : totalSys.Code → totalSys.Code := fun x =>
    match x with
    | ⟨some t, _⟩ => ⟨some (bump t), rfl⟩
    | ⟨none, h⟩ => absurd h (by decide)
  have hgb : totalSys.Adm gBump := by
    refine ⟨fun c => match c with | none => none | some t => some (bump t),
      Or.inr ⟨rfl, .incrAt 0, fun _ => rfl⟩, ?_⟩
    rintro ⟨c, hc⟩
    cases c with
    | none => exact absurd hc (by decide)
    | some t => rfl
  obtain ⟨⟨c, hc⟩, hsem⟩ := hfix gBump hgb
  cases c with
  | none => exact absurd hc (by decide)
  | some t =>
    have hev : eval (bump t) = eval t := Option.some.inj hsem
    have h0 := congrFun hev 0
    simp [bump, eval] at h0

/-- "Halts and computes the zero function" is not decided inside the full system (an instance of
the abstract Rice theorem; it also follows from `not_decidedInside_of_nontrivial`, since only
constant checkers are switch-admissible in the full system). -/
theorem haltsZero_not_decidedInside : ¬ DecidedInside sys HaltsZero :=
  not_decidedInside_of_fixpointPrinciple_extensional_nontrivial fixpointPrinciple
    haltsZero_extensional haltsZero_nontrivial

/-- The full system is not closed under literal code-equality tests: following the identity by
the test "is the output `none`?" with branches `some []` and `some [(0, 1)]` gives a transformer
that is neither constant nor strict. -/
theorem not_eqTestClosed : ¬ EqTestClosed sys := by
  intro h
  rcases h id (Or.inr ⟨rfl, .ident, fun _ => rfl⟩) none (some []) (some [(0, 1)]) with
    ⟨k, hk⟩ | ⟨hnone, _⟩
  · have h1 := congrFun hk none
    have h2 := congrFun hk (some [])
    simp at h1 h2
    rw [← h1] at h2
    cases h2
  · simp at hnone

/-- Only the two constant checkers are switch-admissible in the full system. The switch with
branches `some []` and `some [(0, 1)]` never sends the divergent code `none` to `none`, so it is
not strict; it is therefore admissible only if it is constant, which forces the checker to be
constant. This is the same strictness obstruction as `Flat.switchAdmissible_const`. -/
theorem switchAdmissible_const (chk : Option Table → Bool) (hsw : SwitchAdmissible sys chk) :
    (∀ c, chk c = true) ∨ (∀ c, chk c = false) := by
  rcases hsw (some []) (some [(0, 1)]) with ⟨k, hk⟩ | ⟨hnone, _⟩
  · have hk' : ∀ c, cond (chk c) (some []) (some [(0, 1)]) = k := fun c => congrFun hk c
    cases h0 : chk none with
    | true =>
      left
      intro c
      have h1 := hk' none
      have h2 := hk' c
      rw [h0] at h1
      cases hc : chk c with
      | true => rfl
      | false =>
        rw [hc] at h2
        have h3 : (some [(0, 1)] : Option Table) = some [] := h2.trans h1.symm
        cases h3
    | false =>
      right
      intro c
      have h1 := hk' none
      have h2 := hk' c
      rw [h0] at h1
      cases hc : chk c with
      | false => rfl
      | true =>
        rw [hc] at h2
        have h3 : (some [] : Option Table) = some [(0, 1)] := h2.trans h1.symm
        cases h3
  · have h1 : cond (chk none) (some []) (some [(0, 1)]) = (none : Option Table) := hnone
    cases h0 : chk none <;> rw [h0] at h1 <;> cases h1

/-- Consequently no nontrivial predicate at all, extensional or not, is decided inside the full
system: a constant checker decides only trivial predicates. -/
theorem not_decidedInside_of_nontrivial {P : Option Table → Prop} (hnt : NontrivialPred P) :
    ¬ DecidedInside sys P := by
  rintro ⟨chk, hdec, hsw⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hnt
  rcases switchAdmissible_const chk hsw with hall | hnone
  · exact hb ((hdec b).1 (hall b))
  · have h := (hdec a).2 ha
    rw [hnone a] at h
    exact Bool.noConfusion h

/-- In particular the syntactic predicate "the code is the empty table" is not decided inside
the full system, although it is a property of the code text. -/
theorem isEmptyTable_not_decidedInside : ¬ DecidedInside sys (fun c => c = some []) :=
  not_decidedInside_of_nontrivial ⟨⟨some [], rfl⟩, ⟨none, fun h => by cases h⟩⟩

/-- **Fragments: what a total sublanguage buys, and how.** In the lifted lookup-table system
(fixpoint principle holds), the halting fragment has a proper admissible class and no fixpoint
principle, and the extensional property "halts and computes the zero function", nontrivial on the
fragment, is decided inside the fragment by `fragCheck`; in the full system that property is
nontrivial, extensional, and not decided inside. The full system is not closed under literal
code-equality tests. In the full system only constant checkers are switch-admissible
(`switchAdmissible_const`), so there every nontrivial predicate, syntactic ones included, fails to
be decided inside; the contrast that carries content is the proper admissible class of the
fragment. -/
theorem lifted_haltsZero_decidedInside_haltingFragment_not_full :
    FixpointPrinciple sys ∧ ¬ FixpointPrinciple totalSys ∧
      ¬ (∀ g : totalSys.Code → totalSys.Code, totalSys.Adm g) ∧
      Extensional sys Halts ∧
      Extensional totalSys (fun x => HaltsZero x.val) ∧
      NontrivialPred (fun x : totalSys.Code => HaltsZero x.val) ∧
      Decides fragCheck (fun x => HaltsZero x.val) ∧ SwitchAdmissible totalSys fragCheck ∧
      Extensional sys HaltsZero ∧ NontrivialPred HaltsZero ∧ ¬ DecidedInside sys HaltsZero ∧
      ¬ EqTestClosed sys :=
  ⟨fixpointPrinciple, total_not_fixpointPrinciple, totalSys_adm_proper, halts_extensional,
    extensional_restrict sys haltsZero_extensional, haltsZero_nontrivial_fragment,
    fragCheck_decides, fragCheck_switchAdmissible, haltsZero_extensional, haltsZero_nontrivial,
    haltsZero_not_decidedInside, not_eqTestClosed⟩

end Toy.Rice.Lifted
