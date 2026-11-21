/-
  Toy.KernelTrust.Cert

  A postfix (stack-machine) certificate format with one *derived field*, and two
  re-checkers over that single format:

  * `recheckRecompute R` recomputes the derived field from the rule table;
  * `recheckTrust R` uses the value stored in the certificate.

  The derived field is the `arity` of a rule application: the number of premises
  to pop from the stack.  It is determined by the rule table, so storing it in
  the certificate is a convenience for the consumer, and a trust decision.
-/
import KernelTrust.Checker

namespace Toy.KernelTrust

/-- One instruction of a postfix certificate.

* `hyp Γ φ` pushes the sequent `Γ ⊢ φ`, which must hold by membership.
* `rule Γ ruleIdx σ arity` applies rule number `ruleIdx` of the table under
  substitution `σ` in ambient context `Γ`: it pops the sequents for the rule's
  premises and pushes the conclusion.  `arity` is a **derived field**: an honest
  producer sets it to the number of premises of rule `ruleIdx`. -/
inductive CertStep : Type where
  | hyp  (Γ : Ctx) (φ : Form)
  | rule (Γ : Ctx) (ruleIdx : Nat) (σ : Subst) (arity : Nat)
  deriving DecidableEq, Repr

/-- A certificate is a list of instructions, executed left to right. -/
abbrev Cert := List CertStep

/-- The re-checker's stack of already-established sequents. -/
abbrev Stack := List (Ctx × Form)

/-- How a re-checker treats the derived `arity` field. -/
inductive FieldPolicy : Type where
  /-- Ignore the stored value and recompute it from the rule table. -/
  | recompute
  /-- Use the stored value as given by the certificate's producer. -/
  | trust
  deriving DecidableEq, Repr

/-- Pop one stack entry per listed premise, checking that each popped sequent is
exactly the instantiated premise. -/
def popPremises (Γ : Ctx) (σ : Subst) : List PremiseSpec → Stack → Option Stack
  | [], stk => some stk
  | p :: ps, (c, f) :: stk =>
    if c == (p.addedHyps.map (instPat σ) ++ Γ) && f == instPat σ p.goal then
      popPremises Γ σ ps stk
    else none
  | _ :: _, [] => none

/-- The premises a rule step must discharge under a field policy: all of the
rule's premises (`recompute`), or only the first `arity` of them (`trust`). -/
def premisesToCheck (pol : FieldPolicy) (r : RuleDesc) (arity : Nat) : List PremiseSpec :=
  match pol with
  | .recompute => r.premises
  | .trust     => r.premises.take arity

/-- Execute a certificate on a stack under a field policy.  `none` = rejected. -/
def execCert (pol : FieldPolicy) (R : RuleSet) : Stack → Cert → Option Stack
  | stk, [] => some stk
  | stk, (.hyp Γ φ) :: rest =>
    if decide (φ ∈ Γ) then execCert pol R ((Γ, φ) :: stk) rest else none
  | stk, (.rule Γ idx σ arity) :: rest =>
    match R[idx]? with
    | some r =>
      match popPremises Γ σ (premisesToCheck pol r arity).reverse stk with
      | some stk' => execCert pol R ((Γ, instPat σ r.conclusion) :: stk') rest
      | none => none
    | none => none

/-- The certificate re-checker for rule table `R` under field policy `pol`: a
certificate proves `Γ ⊢ φ` when executing it from the empty stack leaves
exactly `[(Γ, φ)]`. -/
def recheck (pol : FieldPolicy) (R : RuleSet) : Checker where
  Wit := Cert
  accepts c Γ φ := execCert pol R [] c == some [(Γ, φ)]

/-- The re-checker that **recomputes** the derived field. -/
abbrev recheckRecompute (R : RuleSet) : Checker := recheck .recompute R

/-- The re-checker that **trusts** the derived field. -/
abbrev recheckTrust (R : RuleSet) : Checker := recheck .trust R

/-- A certificate step is honest when its stored `arity` equals the arity of
the rule it names.  Two edge cases, both deliberate: a step naming a
nonexistent rule index counts as honest (every policy rejects such a step), and
a step whose stored `arity` *exceeds* the rule's arity is dishonest but is
treated by the trusting policy exactly like an honest one (`List.take` of more
than the list's length returns the whole list), so both re-checkers accept the
same certificates there. -/
def CertStep.honest (R : RuleSet) : CertStep → Bool
  | .hyp _ _ => true
  | .rule _ idx _ arity =>
    match R[idx]? with
    | some r => arity == r.premises.length
    | none => true

/-- A certificate is honest when all of its steps are. -/
def Cert.honest (R : RuleSet) (c : Cert) : Bool := c.all (CertStep.honest R)

/-- A mutant of the re-checker with one guard deleted: `hyp` steps are pushed
without checking `φ ∈ Γ`.  It is parameterised by the same field policy as
`execCert`, so that two *different* mutants sharing this one defect exist. -/
def execCertNoHypGuard (pol : FieldPolicy) (R : RuleSet) : Stack → Cert → Option Stack
  | stk, [] => some stk
  | stk, (.hyp Γ φ) :: rest => execCertNoHypGuard pol R ((Γ, φ) :: stk) rest
  | stk, (.rule Γ idx σ arity) :: rest =>
    match R[idx]? with
    | some r =>
      match popPremises Γ σ (premisesToCheck pol r arity).reverse stk with
      | some stk' => execCertNoHypGuard pol R ((Γ, instPat σ r.conclusion) :: stk') rest
      | none => none
    | none => none

/-- The missing-guard mutant of the *recomputing* re-checker.  Used as a
concrete unfaithful checker for sound rules. -/
def recheckNoHypGuard (R : RuleSet) : Checker where
  Wit := Cert
  accepts c Γ φ := execCertNoHypGuard .recompute R [] c == some [(Γ, φ)]

/-- The missing-guard mutant of the *trusting* re-checker: it has both defects
(missing `hyp` guard, trusted `arity`).  It shares the missing-guard defect
with `recheckNoHypGuard` and differs from it in the `arity` policy. -/
def recheckTrustNoHypGuard (R : RuleSet) : Checker where
  Wit := Cert
  accepts c Γ φ := execCertNoHypGuard .trust R [] c == some [(Γ, φ)]

/-! ## The recomputing re-checker is faithful (and complete) for every rule table -/

theorem popPremises_sound {R : RuleSet}
    {Γ : Ctx} {σ : Subst} {ps : List PremiseSpec} {stk stk' : Stack}
    (hstk : ∀ x ∈ stk, Derivable R x.1 x.2)
    (hpop : popPremises Γ σ ps stk = some stk') :
    (∀ x ∈ stk', Derivable R x.1 x.2) ∧
    (∀ p ∈ ps, Derivable R (p.addedHyps.map (instPat σ) ++ Γ) (instPat σ p.goal)) := by
  induction ps generalizing stk with
  | nil =>
    simp [popPremises] at hpop; subst hpop
    exact ⟨hstk, fun _ hp => by cases hp⟩
  | cons p ps' ih =>
    cases stk with
    | nil => simp [popPremises] at hpop
    | cons top rest =>
      rcases top with ⟨c, f⟩
      simp only [popPremises, Bool.and_eq_true, beq_iff_eq] at hpop
      split at hpop
      · rename_i hcf
        rcases hcf with ⟨hc, hf⟩
        rcases ih (fun x hx => hstk x (List.mem_cons_of_mem _ hx)) hpop with ⟨hstk', hps'⟩
        refine ⟨hstk', fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | htl
        · have htop := hstk (c, f) List.mem_cons_self
          simpa [hc, hf] using htop
        · exact hps' q htl
      · contradiction

theorem execCert_recompute_sound {R : RuleSet} {stk out : Stack} {c : Cert}
    (hstk : ∀ x ∈ stk, Derivable R x.1 x.2)
    (hex : execCert .recompute R stk c = some out) :
    ∀ x ∈ out, Derivable R x.1 x.2 := by
  induction c generalizing stk with
  | nil =>
    simp [execCert] at hex; subst hex; exact hstk
  | cons op ops ih =>
    cases op with
    | hyp Γ φ =>
      simp only [execCert, decide_eq_true_eq] at hex
      split at hex
      · rename_i hmem
        apply ih _ hex
        intro x hx
        rcases List.mem_cons.mp hx with rfl | htl
        · exact .hyp hmem
        · exact hstk x htl
      · contradiction
    | rule Γ rIdx σ arity =>
      simp only [execCert, premisesToCheck] at hex
      cases hr : R[rIdx]? with
      | none => simp [hr] at hex
      | some r =>
        simp only [hr] at hex
        cases hpop : popPremises Γ σ r.premises.reverse stk with
        | none => simp [hpop] at hex
        | some stk' =>
          simp only [hpop] at hex
          rcases popPremises_sound hstk hpop with ⟨hstk', hprems⟩
          apply ih _ hex
          intro x hx
          rcases List.mem_cons.mp hx with rfl | htl
          · exact .step r σ (List.mem_of_getElem? hr)
              (fun p hp => hprems p (List.mem_reverse.mpr hp))
          · exact hstk' x htl

/-- **What recomputation buys.**  The recomputing re-checker is faithful to
*every* rule table `R`, whatever the certificate's stored `arity` fields say. -/
theorem recheckRecompute_faithful (R : RuleSet) : Faithful (recheckRecompute R) R := by
  intro c Γ φ h
  change (execCert .recompute R [] c == some [(Γ, φ)]) = true at h
  simp only [beq_iff_eq] at h
  have hall := execCert_recompute_sound (fun _ hx => by cases hx) h
  exact hall (Γ, φ) List.mem_cons_self

theorem execCert_append {pol : FieldPolicy} {R : RuleSet} {s0 s1 s2 : Stack}
    {c1 c2 : Cert}
    (h1 : execCert pol R s0 c1 = some s1)
    (h2 : execCert pol R s1 c2 = some s2) :
    execCert pol R s0 (c1 ++ c2) = some s2 := by
  induction c1 generalizing s0 with
  | nil => simp [execCert] at h1; subst h1; exact h2
  | cons op ops ih =>
    cases op with
    | hyp Γ φ =>
      simp only [execCert, List.cons_append] at h1 ⊢
      cases hm : decide (φ ∈ Γ)
      · simp [hm] at h1
      · simp only [hm, ↓reduceIte] at h1 ⊢
        exact ih h1
    | rule Γ rIdx σ arity =>
      simp only [execCert, List.cons_append] at h1 ⊢
      cases hr : R[rIdx]? with
      | none => simp [hr] at h1
      | some r =>
        simp only [hr] at h1 ⊢
        cases hpop : popPremises Γ σ (premisesToCheck pol r arity).reverse s0 with
        | none => simp [hpop] at h1
        | some stk' =>
          simp only [hpop] at h1 ⊢
          exact ih h1

theorem premisesToCheck_honest (pol : FieldPolicy) (r : RuleDesc) :
    premisesToCheck pol r r.premises.length = r.premises := by
  cases pol <;> simp [premisesToCheck]

private theorem mem_rule_idx {R : RuleSet} {r : RuleDesc} (hr : r ∈ R) :
    ∃ idx : Nat, R[idx]? = some r := by
  induction R with
  | nil => cases hr
  | cons x xs ih =>
    rcases List.mem_cons.mp hr with rfl | htl
    · exact ⟨0, rfl⟩
    · rcases ih htl with ⟨i, hi⟩
      exact ⟨i + 1, hi⟩

private theorem push_premises_cert {pol : FieldPolicy} {R : RuleSet} (Γ : Ctx) (σ : Subst)
    (ps : List PremiseSpec)
    (ih : ∀ p ∈ ps, ∀ stk : Stack,
      ∃ cert, execCert pol R stk cert =
        some ((p.addedHyps.map (instPat σ) ++ Γ, instPat σ p.goal) :: stk)) :
    ∀ stk : Stack,
      ∃ cert stkMid,
        execCert pol R stk cert = some stkMid ∧
        popPremises Γ σ ps.reverse stkMid = some stk := by
  induction ps with
  | nil =>
    intro stk
    exact ⟨[], stk, rfl, rfl⟩
  | cons p ps' ihps =>
    intro stk
    rcases ih p (by simp) stk with ⟨c1, hc1⟩
    rcases ihps (fun q hq => ih q (by simp [hq]))
      ((p.addedHyps.map (instPat σ) ++ Γ, instPat σ p.goal) :: stk) with
      ⟨c2, stkMid, hc2, hpop2⟩
    refine ⟨c1 ++ c2, stkMid, execCert_append hc1 hc2, ?_⟩
    have hpop_app : ∀ (qs : List PremiseSpec) (sA sB : Stack),
        popPremises Γ σ qs sA =
          some ((p.addedHyps.map (instPat σ) ++ Γ, instPat σ p.goal) :: sB) →
        popPremises Γ σ (qs ++ [p]) sA = some sB := by
      intro qs
      induction qs with
      | nil =>
        intro sA sB h0
        simp [popPremises] at h0; subst h0
        simp [popPremises]
      | cons q qs' ihq =>
        intro sA sB h0
        cases sA with
        | nil => simp [popPremises] at h0
        | cons top rest =>
          rcases top with ⟨ct, ft⟩
          simp only [popPremises, List.cons_append] at h0 ⊢
          cases hcond : (ct == (q.addedHyps.map (instPat σ) ++ Γ) && ft == instPat σ q.goal)
          · simp [hcond] at h0
          · simp only [hcond, ↓reduceIte] at h0 ⊢
            exact ihq rest sB h0
    simpa [List.reverse_cons] using hpop_app ps'.reverse stkMid stk hpop2

theorem execCert_complete {pol : FieldPolicy} {R : RuleSet} {Γ : Ctx} {φ : Form}
    (h : Derivable R Γ φ) :
    ∀ stk : Stack, ∃ cert, execCert pol R stk cert = some ((Γ, φ) :: stk) := by
  induction h with
  | @hyp Γ φ hmem =>
    intro stk
    exact ⟨[.hyp Γ φ], by simp [execCert, hmem]⟩
  | @step Γ r σ hr _ ih =>
    intro stk
    rcases mem_rule_idx hr with ⟨rIdx, hrIdx⟩
    rcases push_premises_cert Γ σ r.premises (fun p hp s => ih p hp s) stk with
      ⟨cPrems, stkMid, hexPrems, hpop⟩
    have hRule : execCert pol R stkMid [.rule Γ rIdx σ r.premises.length] =
        some ((Γ, instPat σ r.conclusion) :: stk) := by
      simp [execCert, premisesToCheck_honest, hrIdx, hpop]
    exact ⟨cPrems ++ [.rule Γ rIdx σ r.premises.length], execCert_append hexPrems hRule⟩

/-- Both re-checkers are complete for every rule table: every derivable sequent
has an accepted certificate. -/
theorem recheck_complete (pol : FieldPolicy) (R : RuleSet) : Complete (recheck pol R) R := by
  intro Γ φ h
  rcases execCert_complete (pol := pol) h [] with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  show (execCert pol R [] c == some [(Γ, φ)]) = true
  rw [hc]
  exact beq_self_eq_true _

/-- On honest certificates the two field policies execute identically.  The
trusting re-checker is therefore not a strawman: it is correct whenever the
producer is honest about the derived field. -/
theorem execCert_trust_eq_recompute_of_honest {R : RuleSet} {c : Cert}
    (hc : Cert.honest R c = true) :
    ∀ stk : Stack, execCert .trust R stk c = execCert .recompute R stk c := by
  induction c with
  | nil => intro stk; rfl
  | cons op ops ih =>
    simp only [Cert.honest, List.all_cons, Bool.and_eq_true] at hc
    have ih' := ih (by simpa [Cert.honest] using hc.2)
    intro stk
    cases op with
    | hyp Γ φ =>
      simp only [execCert]
      split
      · exact ih' _
      · rfl
    | rule Γ rIdx σ arity =>
      simp only [execCert]
      cases hr : R[rIdx]? with
      | none => rfl
      | some r =>
        have harity : arity = r.premises.length := by
          have := hc.1
          simpa [CertStep.honest, hr] using this
        subst harity
        simp only [premisesToCheck_honest]
        cases popPremises Γ σ r.premises.reverse stk with
        | none => rfl
        | some stk' => exact ih' _

/-- On honest certificates the trusting and recomputing re-checkers agree. -/
theorem recheckTrust_eq_recheckRecompute_of_honest {R : RuleSet} {c : Cert}
    (hc : Cert.honest R c = true) (Γ : Ctx) (φ : Form) :
    (recheckTrust R).accepts c Γ φ = (recheckRecompute R).accepts c Γ φ := by
  show (execCert .trust R [] c == some [(Γ, φ)]) = (execCert .recompute R [] c == some [(Γ, φ)])
  rw [execCert_trust_eq_recompute_of_honest hc]

/-! ## Shared-artifact re-checking with disjoint defects -/

/-- Every `hyp` step of the certificate passes the membership guard. -/
def Cert.HypsOk (c : Cert) : Prop := ∀ (Γ : Ctx) (φ : Form), CertStep.hyp Γ φ ∈ c → φ ∈ Γ

/-- A certificate that a re-checker executes to completion (under any field
policy) passes every `hyp` guard: the guard depends neither on the stack nor on
the policy. -/
theorem hypsOk_of_execCert {pol : FieldPolicy} {R : RuleSet} {stk out : Stack} {c : Cert}
    (h : execCert pol R stk c = some out) : Cert.HypsOk c := by
  induction c generalizing stk with
  | nil => intro Γ φ hm; cases hm
  | cons op ops ih =>
    intro Γ φ hm
    cases op with
    | hyp Γ' φ' =>
      simp only [execCert, decide_eq_true_eq] at h
      split at h
      · rename_i hmem
        rcases List.mem_cons.mp hm with heq | htl
        · cases heq; exact hmem
        · exact ih h Γ φ htl
      · contradiction
    | rule Γ' idx σ arity =>
      rcases List.mem_cons.mp hm with heq | htl
      · cases heq
      · simp only [execCert] at h
        cases hr : R[idx]? with
        | none => simp [hr] at h
        | some r =>
          simp only [hr] at h
          cases hpop : popPremises Γ' σ (premisesToCheck pol r arity).reverse stk with
          | none => simp [hpop] at h
          | some stk' =>
            simp only [hpop] at h
            exact ih h Γ φ htl

/-- On a certificate that passes every `hyp` guard, the missing-guard mutant
executes exactly like the re-checker with the same field policy. -/
theorem execCertNoHypGuard_eq_of_hypsOk {pol : FieldPolicy} {R : RuleSet} {c : Cert}
    (hc : Cert.HypsOk c) :
    ∀ stk : Stack, execCertNoHypGuard pol R stk c = execCert pol R stk c := by
  induction c with
  | nil => intro stk; rfl
  | cons op ops ih =>
    have hc' : Cert.HypsOk ops := fun Γ φ hm => hc Γ φ (List.mem_cons_of_mem _ hm)
    intro stk
    cases op with
    | hyp Γ φ =>
      have hmem : φ ∈ Γ := hc Γ φ List.mem_cons_self
      simp only [execCertNoHypGuard, execCert, hmem, decide_true, ↓reduceIte]
      exact ih hc' _
    | rule Γ idx σ arity =>
      simp only [execCertNoHypGuard, execCert]
      cases R[idx]? with
      | none => rfl
      | some r =>
        simp only
        cases popPremises Γ σ (premisesToCheck pol r arity).reverse stk with
        | none => rfl
        | some stk' => exact ih hc' _

/-- **Shared-artifact re-checking defeats these two disjoint defects.**  With the
identity translation `tr = id` (both members read the same certificate), for every
rule table `R` the shared-artifact quorum of the arity-trusting re-checker and the
missing-guard mutant of the recomputing re-checker is faithful, although (for the
standard rules) neither member is: a certificate accepted by the trusting re-checker
passes every `hyp` guard, and on such a certificate the missing-guard mutant executes
exactly like the recomputing re-checker. -/
theorem sharedQuorum_recheckTrust_recheckNoHypGuard_faithful (R : RuleSet) :
    Faithful (sharedQuorum (recheckTrust R) (recheckNoHypGuard R) id) R := by
  intro c Γ φ h
  simp only [sharedQuorum, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : execCert .trust R [] c = some [(Γ, φ)] := by
    have h1'' : (execCert .trust R [] c == some [(Γ, φ)]) = true := h1
    simpa only [beq_iff_eq] using h1''
  have h2' : execCertNoHypGuard .recompute R [] c = some [(Γ, φ)] := by
    have h2'' : (execCertNoHypGuard .recompute R [] c == some [(Γ, φ)]) = true := h2
    simpa only [beq_iff_eq] using h2''
  rw [execCertNoHypGuard_eq_of_hypsOk (hypsOk_of_execCert h1')] at h2'
  apply recheckRecompute_faithful R c Γ φ
  show (execCert .recompute R [] c == some [(Γ, φ)]) = true
  rw [h2']
  exact beq_self_eq_true _

/-! ## Concrete certificates used by the examples and counterexamples -/

/-- An honest certificate for `⊢ ⊥ → ⊥` under the standard rules:
push `[⊥] ⊢ ⊥`, then `impIntro`. -/
def topCert : Cert :=
  [ .hyp [.bot] .bot
  , .rule [] 0 [.bot, .bot] 1 ]

/-- A certificate that **lies about the derived field**: it applies `botElim`
(rule 8, one premise) to conclude `φ`, but claims `arity = 0`, so a trusting
re-checker pops and checks nothing. -/
def lyingCert (φ : Form) : Cert := [ .rule [] 8 [φ] 0 ]

/-- A certificate exploiting the missing `hyp` guard: it pushes `[] ⊢ φ` as if
`φ` were a hypothesis. -/
def bogusHypCert (φ : Form) : Cert := [ .hyp [] φ ]

/-- An honest certificate for `⊢ ⊥` under `badRules`
(the derivation of `badRules_derives_bot`, in postfix form). -/
def badBotCert : Cert :=
  [ .hyp [.bot, .bot] .bot
  , .rule [.bot] 0 [.bot, .bot] 1            -- [⊥] ⊢ ⊤
  , .rule [] 0 [.bot, Form.top] 1            -- ⊢ ⊥ → ⊤
  , .rule [] 9 [.bot, Form.top] 1            -- ⊢ ⊤ → ⊥      (converseImp)
  , .hyp [.bot] .bot
  , .rule [] 0 [.bot, .bot] 1                -- ⊢ ⊤
  , .rule [] 1 [Form.top, .bot] 2 ]          -- ⊢ ⊥          (impElim)

/-! ## Examples for the definitions above -/

/-- Positive example (`recheckRecompute`): the honest certificate `topCert` is
accepted for `⊢ ⊥ → ⊥`. -/
theorem ex_recheckRecompute_accepts_topCert_pos :
    (recheckRecompute stdRules).accepts topCert [] Form.top = true := by decide

/-- Negative example (`recheckRecompute`): the same certificate is rejected for
a different statement. -/
theorem ex_recheckRecompute_rejects_topCert_neg :
    (recheckRecompute stdRules).accepts topCert [] .bot = false := by decide

/-- Positive example (`Faithful`, non-degenerate): the recomputing re-checker
is faithful and complete for the standard rules and accepts something. -/
theorem ex_faithful_recheckRecompute_pos :
    Faithful (recheckRecompute stdRules) stdRules ∧
    Complete (recheckRecompute stdRules) stdRules ∧
    (recheckRecompute stdRules).accepts topCert [] Form.top = true :=
  ⟨recheckRecompute_faithful stdRules, recheck_complete .recompute stdRules, by decide⟩

/-- Positive example (`recheckTrust`): on the honest `topCert` the trusting
re-checker accepts, exactly like the recomputing one. -/
theorem ex_recheckTrust_accepts_topCert_pos :
    (recheckTrust stdRules).accepts topCert [] Form.top = true := by decide

/-- Negative example (`recheckTrust`): the trusting re-checker is not faithful
to the standard rules. -/
theorem ex_faithful_recheckTrust_neg : ¬ Faithful (recheckTrust stdRules) stdRules :=
  fun h => stdRules_consistent (h (lyingCert .bot) [] .bot (by decide))

/-- Positive example (`Cert.honest`). -/
theorem ex_honest_topCert_pos : Cert.honest stdRules topCert = true := by decide

/-- Negative example (`Cert.honest`): the lying certificate is dishonest. -/
theorem ex_honest_lyingCert_neg (φ : Form) : Cert.honest stdRules (lyingCert φ) = false := rfl

/-- Positive example (`popPremises`): popping no premises leaves the stack. -/
theorem ex_popPremises_pos (stk : Stack) : popPremises [] [] [] stk = some stk := by
  cases stk <;> rfl

/-- Negative example (`popPremises`): a premise cannot be popped from an empty
stack. -/
theorem ex_popPremises_neg (p : PremiseSpec) : popPremises [] [] [p] [] = none := rfl

/-- Positive example (`premisesToCheck`): an honest arity makes both policies
check the same premises. -/
theorem ex_premisesToCheck_pos (r : RuleDesc) :
    premisesToCheck .trust r r.premises.length = premisesToCheck .recompute r r.premises.length := by
  simp [premisesToCheck_honest]

/-- Negative example (`premisesToCheck`): with a lying arity of `0` the
trusting policy checks nothing, although `botElim` has one premise. -/
theorem ex_premisesToCheck_neg :
    premisesToCheck .trust
        { name := "botElim", premises := [{ addedHyps := [], goal := .bot }],
          conclusion := .pvar 0 } 0 = [] ∧
    premisesToCheck .recompute
        { name := "botElim", premises := [{ addedHyps := [], goal := .bot }],
          conclusion := .pvar 0 } 0 ≠ [] := by
  constructor
  · rfl
  · simp [premisesToCheck]

/-- Positive example (`recheckNoHypGuard`): the mutant still accepts honest
certificates. -/
theorem ex_recheckNoHypGuard_accepts_topCert_pos :
    (recheckNoHypGuard stdRules).accepts topCert [] Form.top = true := by decide

/-- Negative example (`recheckNoHypGuard`): the mutant is not faithful to the
standard rules. -/
theorem ex_faithful_recheckNoHypGuard_neg : ¬ Faithful (recheckNoHypGuard stdRules) stdRules :=
  fun h => stdRules_consistent (h (bogusHypCert .bot) [] .bot (by decide))

/-- Positive example (`recheckTrustNoHypGuard`): the doubly broken mutant still
accepts honest certificates. -/
theorem ex_recheckTrustNoHypGuard_accepts_topCert_pos :
    (recheckTrustNoHypGuard stdRules).accepts topCert [] Form.top = true := by decide

/-- Negative example (`recheckTrustNoHypGuard`): it is not faithful to the
standard rules. -/
theorem ex_faithful_recheckTrustNoHypGuard_neg :
    ¬ Faithful (recheckTrustNoHypGuard stdRules) stdRules :=
  fun h => stdRules_consistent (h (bogusHypCert .bot) [] .bot (by decide))

/-- Positive example (`Cert.HypsOk`): the honest certificate `topCert`. -/
theorem ex_hypsOk_topCert_pos : Cert.HypsOk topCert := by
  intro Γ φ hm
  simp only [topCert, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · cases h; exact List.mem_singleton.mpr rfl
  · cases h

/-- Negative example (`Cert.HypsOk`): the certificate exploiting the missing
guard. -/
theorem ex_hypsOk_bogusHypCert_neg : ¬ Cert.HypsOk (bogusHypCert .bot) :=
  fun h => by cases h [] .bot (List.mem_singleton.mpr rfl)

/-- Positive example (`badBotCert`): the recomputing re-checker for `badRules`
accepts it for `⊢ ⊥`, and the certificate is honest. -/
theorem ex_badBotCert_pos :
    (recheckRecompute badRules).accepts badBotCert [] .bot = true ∧
    Cert.honest badRules badBotCert = true := by
  constructor <;> decide

/-- Negative example (`badBotCert`): the recomputing re-checker for the
*standard* rules rejects it (rule 9 does not exist there). -/
theorem ex_badBotCert_neg :
    (recheckRecompute stdRules).accepts badBotCert [] .bot = false := by decide

end Toy.KernelTrust
