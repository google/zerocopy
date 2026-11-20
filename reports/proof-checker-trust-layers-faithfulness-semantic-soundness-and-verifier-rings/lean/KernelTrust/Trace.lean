/-
  Toy.KernelTrust.Trace

  A second, architecturally different faithful checker: a linear proof table
  ("trace") in which every line cites earlier lines by index.  It exists so that
  the ring counterexamples can use more than one faithful implementation.
-/
import KernelTrust.Checker

namespace Toy.KernelTrust

/-- One line of a linear proof table: the sequent it claims, and either
"hypothesis" or a rule index, substitution, and the indices of earlier lines
used as premises. -/
structure TraceStep where
  ctx      : Ctx
  concl    : Form
  isHyp    : Bool
  ruleIdx  : Nat
  subst    : Subst
  premIdxs : List Nat
  deriving DecidableEq, Repr

/-- A trace is a list of lines; the last line is the proved sequent. -/
abbrev Trace := List TraceStep

/-- Check that the cited earlier lines are exactly the instantiated premises. -/
def premisesMatch (verified : List (Ctx × Form)) (Γ : Ctx) (σ : Subst) :
    List Nat → List PremiseSpec → Bool
  | [], [] => true
  | idx :: idxs, p :: ps =>
    (verified[idx]? == some (p.addedHyps.map (instPat σ) ++ Γ, instPat σ p.goal)) &&
    premisesMatch verified Γ σ idxs ps
  | _, _ => false

/-- Validity of a single line given the lines verified so far. -/
def traceStepOk (R : RuleSet) (acc : List (Ctx × Form)) (s : TraceStep) : Bool :=
  if s.isHyp then
    decide (s.concl ∈ s.ctx)
  else
    match R[s.ruleIdx]? with
    | some r =>
      (s.concl == instPat s.subst r.conclusion) &&
      premisesMatch acc s.ctx s.subst s.premIdxs r.premises
    | none => false

/-- Check all lines in order, accumulating the verified sequents. -/
def checkTraceSteps (R : RuleSet) : List (Ctx × Form) → Trace → Option (List (Ctx × Form))
  | acc, [] => some acc
  | acc, s :: rest =>
    if traceStepOk R acc s then checkTraceSteps R (acc ++ [(s.ctx, s.concl)]) rest else none

/-- The trace checker for rule table `R`. -/
def traceChecker (R : RuleSet) : Checker where
  Wit := Trace
  accepts tr Γ φ :=
    match checkTraceSteps R [] tr with
    | some verified => verified.getLast? == some (Γ, φ)
    | none          => false

private theorem premisesMatch_sound {R : RuleSet} {verified : List (Ctx × Form)}
    (hver : ∀ x ∈ verified, Derivable R x.1 x.2)
    {Γ : Ctx} {σ : Subst} {idxs : List Nat} {ps : List PremiseSpec}
    (hm : premisesMatch verified Γ σ idxs ps = true) :
    ∀ p ∈ ps, Derivable R (p.addedHyps.map (instPat σ) ++ Γ) (instPat σ p.goal) := by
  induction idxs generalizing ps with
  | nil =>
    cases ps with
    | nil => intro p hp; cases hp
    | cons _ _ => simp [premisesMatch] at hm
  | cons idx rest ih =>
    cases ps with
    | nil => simp [premisesMatch] at hm
    | cons p ps' =>
      simp only [premisesMatch, Bool.and_eq_true, beq_iff_eq] at hm
      intro q hq
      rcases List.mem_cons.mp hq with rfl | htl
      · exact hver _ (List.mem_of_getElem? hm.1)
      · exact ih hm.2 q htl

private theorem checkTraceSteps_sound {R : RuleSet} {acc out : List (Ctx × Form)} {tr : Trace}
    (hacc : ∀ x ∈ acc, Derivable R x.1 x.2)
    (htr : checkTraceSteps R acc tr = some out) :
    ∀ x ∈ out, Derivable R x.1 x.2 := by
  induction tr generalizing acc with
  | nil =>
    simp [checkTraceSteps] at htr; subst htr; exact hacc
  | cons s rest ih =>
    simp only [checkTraceSteps] at htr
    cases hok : traceStepOk R acc s
    · simp [hok] at htr
    · simp only [hok, ↓reduceIte] at htr
      apply ih _ htr
      intro x hx
      rcases List.mem_append.mp hx with hx1 | hx2
      · exact hacc x hx1
      · simp only [List.mem_singleton] at hx2; subst hx2
        unfold traceStepOk at hok
        by_cases hh : s.isHyp
        · simp [hh] at hok
          exact .hyp hok
        · simp [hh] at hok
          cases hr : R[s.ruleIdx]? with
          | none => simp [hr] at hok
          | some r =>
            simp only [hr, Bool.and_eq_true, beq_iff_eq] at hok
            rw [hok.1]
            exact .step r s.subst (List.mem_of_getElem? hr)
              (premisesMatch_sound hacc hok.2)

/-- The trace checker is faithful to every rule table. -/
theorem traceChecker_faithful (R : RuleSet) : Faithful (traceChecker R) R := by
  intro tr Γ φ h
  change (match checkTraceSteps R [] tr with
    | some verified => verified.getLast? == some (Γ, φ)
    | none => false) = true at h
  cases hs : checkTraceSteps R [] tr with
  | none => simp [hs] at h
  | some verified =>
    simp only [hs, beq_iff_eq] at h
    have hall := checkTraceSteps_sound (by intro x hx; cases hx) hs
    exact hall (Γ, φ) (List.mem_of_getLast? h)

/-! ## Concrete traces and examples -/

/-- A trace for `⊢ ⊥ → ⊥` under the standard rules. -/
def topTrace : Trace :=
  [ ⟨[.bot], .bot, true, 0, [], []⟩
  , ⟨[], Form.top, false, 0, [.bot, .bot], [0]⟩ ]

/-- A trace for `⊢ ⊥` under `badRules` (same derivation as `badBotCert`). -/
def badBotTrace : Trace :=
  [ ⟨[.bot, .bot], .bot, true, 0, [], []⟩
  , ⟨[.bot], Form.top, false, 0, [.bot, .bot], [0]⟩
  , ⟨[], .imp .bot Form.top, false, 0, [.bot, Form.top], [1]⟩
  , ⟨[], .imp Form.top .bot, false, 9, [.bot, Form.top], [2]⟩
  , ⟨[.bot], .bot, true, 0, [], []⟩
  , ⟨[], Form.top, false, 0, [.bot, .bot], [4]⟩
  , ⟨[], .bot, false, 1, [Form.top, .bot], [3, 5]⟩ ]

/-- Positive example (`traceChecker`): `topTrace` is accepted for `⊢ ⊥ → ⊥`. -/
theorem ex_traceChecker_accepts_topTrace_pos :
    (traceChecker stdRules).accepts topTrace [] Form.top = true := by decide

/-- Negative example (`traceChecker`): a line citing itself as its own premise
is rejected (premises must be *earlier* lines). -/
theorem ex_traceChecker_rejects_selfCitation_neg :
    (traceChecker stdRules).accepts [⟨[], .bot, false, 8, [.bot], [0]⟩] [] .bot = false := by
  decide

/-- Positive example (`traceChecker`, unsound rules): `badBotTrace` is accepted
for `⊢ ⊥` under `badRules`. -/
theorem ex_traceChecker_accepts_badBotTrace_pos :
    (traceChecker badRules).accepts badBotTrace [] .bot = true := by decide

/-- Negative example (`traceChecker`): the same trace is rejected under the
standard rules. -/
theorem ex_traceChecker_rejects_badBotTrace_neg :
    (traceChecker stdRules).accepts badBotTrace [] .bot = false := by decide

end Toy.KernelTrust
