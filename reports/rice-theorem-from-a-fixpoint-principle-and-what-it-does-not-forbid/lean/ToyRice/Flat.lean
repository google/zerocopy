/-
# A flat domain of Boolean results with divergence (fixpoint principle holds)

Codes are the three denotations of a Boolean-valued program: diverges (`bot`), returns
`true` (`tt`), returns `false` (`ff`). They are ordered by information: `bot` below both
results, which are incomparable. Admissible transformers are the monotone maps.

Monotonicity is the domain-theoretic shadow of computability: a program transformer cannot
turn "no information yet" into a definite answer and then change that answer when more
information arrives. In this system every admissible transformer has a fixed point (iterate from
`bot`: the least-fixed-point argument for monotone maps on a pointed poset), so the fixpoint
principle holds. It holds without any encoding of computation, universal program, or
self-reference. The abstract Rice theorem then says that halting and "returns `true`" are not
decided inside the system.

Limitations, stated as lemmas below: codes are denotations (`sem = id`), so every predicate is
extensional and the system cannot distinguish syntactic from semantic predicates (see
`ToyRice.Padded` for that); only the two constant checkers are switch-admissible
(`switchAdmissible_const`); and the restriction to the two-element total fragment admits every
transformer (`totalSys_adm`), so every predicate is decided there
(`totalSys_decides_every_predicate`). For a fragment with a proper admissible class see
`ToyRice.Lifted`.
-/
import ToyRice.Abstract

namespace Toy.Rice.Flat

/-- Denotations of Boolean-valued programs: diverge, return `true`, return `false`. -/
inductive Flat where
  | bot
  | tt
  | ff
  deriving DecidableEq, Repr

/-- The information order of the flat domain: `bot` is below everything; otherwise only
`x ≤ x`. -/
def le (x y : Flat) : Prop := x = .bot ∨ x = y

/-- Monotone maps for the information order. -/
def Monotone (f : Flat → Flat) : Prop := ∀ x y, le x y → le (f x) (f y)

/-- The flat-domain system: codes and behaviours are denotations; admissible transformers
are the monotone maps. -/
abbrev sys : System := ⟨Flat, Flat, id, Monotone⟩

/-- Any map sending `bot` to `bot` is monotone. -/
theorem monotone_of_map_bot {f : Flat → Flat} (h : f .bot = .bot) : Monotone f := by
  intro x y hle
  rcases hle with hx | hxy
  · subst hx; left; exact h
  · subst hxy; right; rfl

/-- **The fixpoint principle holds in the flat-domain system**: every monotone map on the
flat domain has a fixed point. -/
theorem fixpointPrinciple : FixpointPrinciple sys := by
  intro f hf
  show ∃ c, f c = c
  cases h : f .bot with
  | bot => exact ⟨.bot, h⟩
  | tt =>
    refine ⟨.tt, ?_⟩
    have := hf .bot .tt (Or.inl rfl)
    rw [h] at this
    rcases this with h1 | h1
    · cases h1
    · exact h1.symm
  | ff =>
    refine ⟨.ff, ?_⟩
    have := hf .bot .ff (Or.inl rfl)
    rw [h] at this
    rcases this with h1 | h1
    · cases h1
    · exact h1.symm

/-- "The program halts." -/
def Halts (c : Flat) : Prop := c ≠ .bot

/-- "The program returns `true`." -/
def ReturnsTt (c : Flat) : Prop := c = .tt

/-- Checker for `Halts`. -/
def haltCheck (c : Flat) : Bool := decide (c ≠ .bot)

theorem haltCheck_decides : Decides haltCheck Halts := by
  intro c; simp [haltCheck, Halts]

/-- Every predicate on this system is extensional, because `sem = id`. -/
theorem extensional_all (P : Flat → Prop) : Extensional sys P := by
  intro c d h
  have h' : c = d := h
  subst h'
  exact Iff.rfl

theorem halts_nontrivial : NontrivialPred Halts :=
  ⟨⟨.tt, fun h => Flat.noConfusion h⟩, ⟨.bot, fun h => h rfl⟩⟩

theorem returnsTt_nontrivial : NontrivialPred ReturnsTt :=
  ⟨⟨.tt, rfl⟩, ⟨.ff, fun h => Flat.noConfusion h⟩⟩

/-- Halting is not decided inside the flat-domain system (from the abstract Rice theorem). -/
theorem halts_not_decidedInside : ¬ DecidedInside sys Halts :=
  not_decidedInside_of_fixpointPrinciple_extensional_nontrivial fixpointPrinciple
    (extensional_all _) halts_nontrivial

/-- "Returns `true`" is not decided inside the flat-domain system. -/
theorem returnsTt_not_decidedInside : ¬ DecidedInside sys ReturnsTt :=
  not_decidedInside_of_fixpointPrinciple_extensional_nontrivial fixpointPrinciple
    (extensional_all _) returnsTt_nontrivial

/-- The *unswapped* halting switch `c ↦ if halts c then tt else bot` is monotone, hence
admissible. Only the swapped switch is ruled out. -/
theorem unswappedSwitch_admissible : sys.Adm (switch haltCheck .tt .bot) :=
  monotone_of_map_bot (f := switch haltCheck Flat.tt Flat.bot) rfl

/-- The *swapped* halting switch `c ↦ if halts c then bot else tt` is not monotone. -/
theorem swappedSwitch_not_admissible : ¬ sys.Adm (switch haltCheck .bot .tt) := by
  intro h
  have := h .bot .tt (Or.inl rfl)
  -- the switch sends `bot ↦ tt` and `tt ↦ bot`
  change le Flat.tt Flat.bot at this
  rcases this with h1 | h1 <;> cases h1

/-- **Positive control.** The flat-domain system satisfies the fixpoint principle and has a
nontrivial extensional predicate (halting), which the abstract Rice theorem then shows is not
decided inside the system. -/
theorem flat_fixpointPrinciple_and_halts_not_decidedInside :
    FixpointPrinciple sys ∧ Extensional sys Halts ∧ NontrivialPred Halts ∧
      ¬ DecidedInside sys Halts :=
  ⟨fixpointPrinciple, extensional_all _, halts_nontrivial, halts_not_decidedInside⟩

/-- **The one-sided switch is not forbidden.** Halting is not decided inside the flat-domain
system, but the one-sided switch "if the program halts then `tt`, else diverge"
(`c ↦ if halts c then tt else bot`) is admissible. No notion of semi-decision is defined here;
this only shows that `DecidedInside`, which needs both switches, is strictly stronger than
admissibility of that one switch. -/
theorem halts_unswappedSwitch_admissible_not_decidedInside :
    FixpointPrinciple sys ∧ sys.Adm (switch haltCheck .tt .bot) ∧ ¬ DecidedInside sys Halts :=
  ⟨fixpointPrinciple, unswappedSwitch_admissible, halts_not_decidedInside⟩

/-- Only the two constant checkers are switch-admissible in the flat-domain system. -/
theorem switchAdmissible_const (chk : Flat → Bool) (hsw : SwitchAdmissible sys chk) :
    (∀ c, chk c = true) ∨ (∀ c, chk c = false) := by
  have hm : Monotone (switch chk Flat.tt Flat.ff) := hsw Flat.tt Flat.ff
  cases hb : chk Flat.bot with
  | true =>
    left; intro c
    have hle := hm Flat.bot c (Or.inl rfl)
    simp only [switch, hb, Bool.cond_true] at hle
    rcases hle with h | h
    · cases h
    · cases hc : chk c <;> simp [hc] at h ⊢
  | false =>
    right; intro c
    have hle := hm Flat.bot c (Or.inl rfl)
    simp only [switch, hb, Bool.cond_false] at hle
    rcases hle with h | h
    · cases h
    · cases hc : chk c <;> simp [hc] at h ⊢

/-- The flat domain is not a lattice: `tt` and `ff` have no common upper bound. (So the
fixpoint principle here is not an instance of the fixed-point theorem for complete lattices; it
is the least-fixed-point argument for monotone maps on a pointed poset.) -/
theorem no_upper_bound_tt_ff : ¬ ∃ z, le Flat.tt z ∧ le Flat.ff z := by
  rintro ⟨z, h1, h2⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> cases h1 <;> cases h2

/-- The flat-domain system is not closed under literal code-equality tests: the test "is the
input `bot`?" with branches `tt`, `ff` is not monotone. -/
theorem not_eqTestClosed : ¬ EqTestClosed sys := by
  intro h
  have hm := h id (fun _ _ hle => hle) Flat.bot Flat.tt Flat.ff
  have := hm Flat.bot Flat.tt (Or.inl rfl)
  simp at this
  rcases this with h1 | h1 <;> cases h1

/-! ## The total fragment -/

/-- Totality: the program halts. -/
def IsTotal (c : Flat) : Prop := c ≠ .bot

/-- The total fragment of the flat-domain system (two codes). -/
abbrev totalSys : System := sys.restrict IsTotal

/-- **Degeneracy.** Every transformer of the total fragment is admissible: extend it by
`bot ↦ bot`. The fragment's admissible class is the class of all maps on a two-element set. -/
theorem totalSys_adm (g : {c // IsTotal c} → {c // IsTotal c}) : totalSys.Adm g := by
  refine ⟨fun (c : Flat) => if h : c = Flat.bot then Flat.bot else (g ⟨c, h⟩).val,
    monotone_of_map_bot (by simp), ?_⟩
  intro x
  have hx : x.val ≠ Flat.bot := x.2
  simp [hx]

/-- The total fragment has no fixpoint principle: the Boolean swap has no fixed point there. -/
theorem total_not_fixpointPrinciple : ¬ FixpointPrinciple totalSys := by
  intro hfix
  let swap : {c // IsTotal c} → {c // IsTotal c} := fun x =>
    if x.val = .tt then ⟨.ff, fun h => Flat.noConfusion h⟩ else ⟨.tt, fun h => Flat.noConfusion h⟩
  obtain ⟨c, hc⟩ := hfix swap (totalSys_adm swap)
  change (swap c).val = c.val at hc
  obtain ⟨v, hv⟩ := c
  cases v with
  | bot => exact hv rfl
  | tt => simp [swap] at hc
  | ff => simp [swap] at hc

/-- Consequently every predicate on the total fragment is decided inside it. -/
theorem totalSys_decides_every_predicate (P : totalSys.Code → Prop) : DecidedInside totalSys P :=
  ⟨fun x => @decide (P x) (Classical.propDecidable _), fun x => by simp, fun _ _ => totalSys_adm _⟩

end Toy.Rice.Flat
