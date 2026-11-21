import Implicature.Exh

/-!
# Reader models, blockers, normal-form compression, necessity words, disclaimers

* `Rule`: the default strengthening rules of a reader: conditional perfection,
  exhaustification, and qualifier dropping (the last models a hasty reader).
* `readings S alt F σ`: the one-step strengthening reader. Its readings are the literal `σ`
  and, for every rule not blocked by a flag in `F`, the results of applying that rule once at
  one site, kept only if consistent with `σ` (cancellation: a reader does not draw a
  strengthening that contradicts what was literally said).
* `readingsStar S alt F σ`: the composing reader, which applies any subset of the unblocked
  rules in the fixed order qualifier dropping, perfection, exhaustification.
* `blockers S alt E σ`: the computed blocker set (rules having a reading `E` does not entail).
-/

namespace Toy.Implicature

/-- Default strengthening rules. A blocker flag is an out-of-band annotation with no truth
conditions of its own: it disables exactly the rule it names and nothing else. Intended phrasings:
`perfection` ↔ "the converse is not claimed";
`exhaustification` ↔ "stronger alternatives are not claimed to fail";
`qualifierDrop` ↔ "established under `H`; not shown without `H`".
Disabling one rule leaves the others active: for example, flagging only `perfection` on
`∀x, a → b` still lets exhaustification negate the converse whenever the converse is innocently
excludable (`forall_conditional_blockers_by_converse_status`). -/
inductive Rule where
  | qualifierDrop
  | perfection
  | exhaustification
  deriving DecidableEq, Repr

/-- All rules, in the order in which the composing reader applies them. -/
def allRules : List Rule := [.qualifierDrop, .perfection, .exhaustification]

/-- Perfection of the core of a site: `A → B ↦ A ↔ B`, looking through a prefix of universal
quantifiers and hypothesis relativizations. -/
def perfCore : Claim → Option Claim
  | .imp a b => some (.iff a b)
  | .all c => (perfCore c).map .all
  | .rel h c => (perfCore c).map (.rel h)
  | _ => none

/-- Qualifier dropping at the core of a site: `(H ⇒ C) ↦ C`, looking through a prefix of
universal quantifiers. -/
def dropCore : Claim → Option Claim
  | .rel _ c => some c
  | .all c => (dropCore c).map .all
  | _ => none

/-- One application of a rule, before cancellation; one result per applicable site
(exhaustification applies to the whole rendering, with alternatives `alt σ`). -/
def step (S : Space) (alt : Claim → List Claim) : Rule → Claim → List Claim
  | .perfection, σ => siteSubst (fun c => (perfCore c).toList) σ
  | .qualifierDrop, σ => siteSubst (fun c => (dropCore c).toList) σ
  | .exhaustification, σ => [exh S (alt σ) σ]

/-- The readings a rule contributes to `σ`, after cancellation (kept iff consistent with `σ`). -/
def ruleReadings (S : Space) (alt : Claim → List Claim) (r : Rule) (σ : Claim) : List Claim :=
  (step S alt r σ).filter fun ρ => satB S [σ, ρ]

/-- One-step strengthening reader with blocker flags `F`: the literal reading plus every
uncancelled one-rule reading of an unblocked rule. -/
def readings (S : Space) (alt : Claim → List Claim) (F : List Rule) (σ : Claim) : List Claim :=
  σ :: (allRules.filter fun r => decide (r ∉ F)).flatMap fun r => ruleReadings S alt r σ

/-- Literal safety of a rendering: the report entails it. -/
def LiterallySafe (S : Space) (E : List Claim) (σ : Claim) : Prop := Entails S E σ

instance decLiterallySafe (S : Space) (E : List Claim) (σ : Claim) :
    Decidable (LiterallySafe S E σ) :=
  decEntails S E σ

/-- Strengthening safety (one-step reader): the report entails every reading. -/
def StrengtheningSafe (S : Space) (alt : Claim → List Claim) (F : List Rule) (E : List Claim)
    (σ : Claim) : Prop :=
  ∀ ρ ∈ readings S alt F σ, Entails S E ρ

instance decStrengtheningSafe (S : Space) (alt : Claim → List Claim) (F : List Rule)
    (E : List Claim) (σ : Claim) : Decidable (StrengtheningSafe S alt F E σ) := by
  unfold StrengtheningSafe; infer_instance

/-- The computed blocker set: the rules that contribute some reading `E` does not entail. -/
def blockers (S : Space) (alt : Claim → List Claim) (E : List Claim) (σ : Claim) : List Rule :=
  allRules.filter fun r => (ruleReadings S alt r σ).any fun ρ => !entailsB S E ρ

/-! ## The composing reader -/

/-- Apply any subset of the rules `rs`, in list order, each at most once and at one site. -/
def composeReadings (S : Space) (alt : Claim → List Claim) : List Rule → Claim → List Claim
  | [], ρ => [ρ]
  | r :: rs, ρ =>
      composeReadings S alt rs ρ ++ (step S alt r ρ).flatMap (composeReadings S alt rs)

/-- Composing strengthening reader with flags `F`: the literal reading plus every composition of
unblocked rules (in the order of `allRules`) that is consistent with `σ`. -/
def readingsStar (S : Space) (alt : Claim → List Claim) (F : List Rule) (σ : Claim) :
    List Claim :=
  σ :: (composeReadings S alt (allRules.filter fun r => decide (r ∉ F)) σ).filter
    fun ρ => satB S [σ, ρ]

/-- Strengthening safety for the composing reader. -/
def StrengtheningSafeStar (S : Space) (alt : Claim → List Claim) (F : List Rule)
    (E : List Claim) (σ : Claim) : Prop :=
  ∀ ρ ∈ readingsStar S alt F σ, Entails S E ρ

instance decStrengtheningSafeStar (S : Space) (alt : Claim → List Claim) (F : List Rule)
    (E : List Claim) (σ : Claim) : Decidable (StrengtheningSafeStar S alt F E σ) := by
  unfold StrengtheningSafeStar; infer_instance

/-! ## Normal-form claims and compression -/

/-- A normal-form established claim with one hypothesis `H`, one quantifier domain (the
parameter set) and a list of conclusions `C₁, …, Cₙ`, rendered one conclusion per top-level
conjunct: `(∀x, H x ⇒ C₁ x) ∧ … ∧ (∀x, H x ⇒ Cₙ x)` (`⊤` for `n = 0`). Each conclusion is its own
site, so perfection, qualifier dropping and the structural alternatives apply to each conclusion
separately. (A conjunction nested under `∀` or `⇒` would be a single site to which perfection and
the structural alternatives do not apply.) -/
def nf (H : Claim) (Cs : List Claim) : Claim := conjList (Cs.map fun c => .all (.rel H c))

/-- The claim of a normal-form entry `(H, Cs)`. -/
def nfOf (p : Claim × List Claim) : Claim := nf p.1 p.2

/-- `comp` is a conclusion-dropping compression of the normal-form entries `R`: every
compressed entry keeps the hypothesis (and the quantifier domain) of some entry of `R` and
keeps only conclusions of that entry. -/
def ConclusionDropping (R comp : List (Claim × List Claim)) : Prop :=
  ∀ p ∈ comp, ∃ q ∈ R, q.1 = p.1 ∧ ∀ c ∈ p.2, c ∈ q.2

/-- The rendering of a compression: the conjunction of its normal-form claims. -/
def renderComp (comp : List (Claim × List Claim)) : Claim := conjList (comp.map nfOf)

/-! ## Necessity words and tightness -/

/-- "`X` is needed for `Y`", read literally: `∀x, Y x → X x`. -/
def needed (X Y : Claim) : Claim := .all (.imp Y X)

/-- The counterexample half of "`H` is tight for `∀x, H x ⇒ C x`": some parameter value
violates `H` and `C` fails there. It does not check that `∀x, H x ⇒ C x` itself holds, and it
models a single hypothesis: for `∀x, (H₁ x ∧ H₂ x) ⇒ C x`, tightness of `H₁` also requires `H₂` to
hold at the witness, which `tightFor H₁ C` does not express. -/
def tightFor (H C : Claim) : Claim := .ex (.and (.not H) (.not C))

/-! ## Non-degeneracy conditions for a universal conditional -/

/-- `∀x, a → b` is consistent with its perfected reading `∀x, a ↔ b` (so perfection is not
cancelled). -/
def PerfectionConsistent (S : Space) (a b : Claim) : Prop :=
  Sat S [.all (.imp a b), .all (.iff a b)]

/-- `∀x, a → b` is consistent with the failure of its converse `∀x, b → a` (so the converse is
innocently excludable under the standard alternatives). -/
def ConverseExcludable (S : Space) (a b : Claim) : Prop :=
  Sat S [.all (.imp a b), .not (.all (.imp b a))]

instance decPerfectionConsistent (S : Space) (a b : Claim) :
    Decidable (PerfectionConsistent S a b) :=
  decSat _ _

instance decConverseExcludable (S : Space) (a b : Claim) : Decidable (ConverseExcludable S a b) :=
  decSat _ _

/-! ## Disclaimers -/

/-- A disclaimer about claim `c`: "`c` is not shown", or the blocked form "`c` is not shown,
and not refuted". Disclaimers are statements about the report, not about the worlds. -/
inductive Disclaimer where
  | notShown (c : Claim)
  | notShownNotRefuted (c : Claim)
  deriving DecidableEq, Repr

/-- `E` leaves `c` open: it neither proves nor refutes `c`. -/
def Open (S : Space) (E : List Claim) (c : Claim) : Prop :=
  ¬ Entails S E c ∧ ¬ Entails S E (.not c)

/-- Literal truth of a disclaimer relative to the report `E`. -/
def DisclaimerTrue (S : Space) (E : List Claim) : Disclaimer → Prop
  | .notShown c => ¬ Entails S E c
  | .notShownNotRefuted c => ¬ Entails S E c ∧ ¬ Entails S E (.not c)

/-- Object-level readings of a reader who maps "not shown" to "false". The blocked form
"not shown, and not refuted" disables that rule. Both readings are fixed by this definition; they
are not derived from exhaustification, the alternatives or the cancellation filter. -/
def disclaimerReadings : Disclaimer → List Claim
  | .notShown c => [.not c]
  | .notShownNotRefuted _ => []

/-- A disclaimer rendering is safe iff it is literally true and `E` entails every object-level
reading the reader draws from it. -/
def DisclaimerSafe (S : Space) (E : List Claim) (d : Disclaimer) : Prop :=
  DisclaimerTrue S E d ∧ ∀ ρ ∈ disclaimerReadings d, Entails S E ρ

instance decOpen (S : Space) (E : List Claim) (c : Claim) : Decidable (Open S E c) := by
  unfold Open; infer_instance

instance decDisclaimerTrue (S : Space) (E : List Claim) (d : Disclaimer) :
    Decidable (DisclaimerTrue S E d) := by
  cases d <;> unfold DisclaimerTrue <;> infer_instance

instance decDisclaimerSafe (S : Space) (E : List Claim) (d : Disclaimer) :
    Decidable (DisclaimerSafe S E d) := by
  unfold DisclaimerSafe; infer_instance

end Toy.Implicature
