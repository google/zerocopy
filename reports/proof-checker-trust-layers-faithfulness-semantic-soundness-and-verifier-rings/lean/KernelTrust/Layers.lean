/-
  Toy.KernelTrust.Layers

  K1: what faithfulness + semantic soundness buy (and, with statement pinning,
  what they buy for a *named* statement).
  K2: each assurance layer is necessary (four concrete counterexamples), and
  what separate-artifact and shared-artifact quorums of two checkers do and do
  not establish.
-/
import KernelTrust.Pinning
import KernelTrust.Trace

namespace Toy.KernelTrust

/-! ## K1 — faithfulness + semantic soundness -/

/-- **K1 (main statement).**  If the checker `C` is faithful to the rule table
`R` (`Faithful C R`) and `R` is semantically sound for the reference
truth-table semantics (`SemSound R`), then every sequent that `C` accepts, on
any proof object, is semantically valid.

Hypothesis ledger: `Faithful C R` is necessary
(`unfaithful_checker_for_sound_rules_accepts_bot`); `SemSound R` is necessary
(`faithful_checker_for_unsound_rules_accepts_bot`).
Depth: definitional (the composition of the two definitions). -/
theorem accepted_semValid_of_faithful_of_semSound
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R) :
    ∀ (w : C.Wit) (Γ : Ctx) (φ : Form), C.accepts w Γ φ = true → SemValid Γ φ :=
  fun w Γ φ h => hSemSound Γ φ (hFaithful w Γ φ h)

/-- **K1, `⊥` part.**  A checker that is faithful to semantically sound rules
never accepts `⊢ ⊥`.

This part needs only `Consistent R`, which `SemSound R` implies
(`SemSound.consistent`); `not_acceptsBot_of_faithful_of_consistent` states the
sharper form.  Proved here without using the K1 main statement. -/
theorem not_accepts_bot_of_faithful_of_semSound
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R) :
    ∀ w : C.Wit, C.accepts w [] .bot = false := by
  intro w
  cases h : C.accepts w [] .bot
  · rfl
  · exact absurd ⟨w, h⟩
      (not_acceptsBot_of_faithful_of_consistent hFaithful hSemSound.consistent)

/-- **K1 with pinning** (derived from the K1 main statement).  If, in addition,
the statement table `P` shipped with a proof is pinned to the official table on
`name` (`Pinned official P name`: `name` is defined in `official`, and `P`
resolves it to the same formula), then whenever `C` accepts a proof object for
`name` resolved through `P` (an empty-context sequent `[] ⊢ φ`), the official
meaning of `name` is semantically valid. -/
theorem pinned_accepted_name_semValid_of_faithful_of_semSound
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R)
    {official P : StmtTable} {name : String} (hPinned : Pinned official P name) :
    ∀ w : C.Wit, C.acceptsNamed P w name = true →
      ∀ φ, official.lookup name = some φ → SemValid [] φ := by
  intro w hAcc φ hφ
  obtain ⟨ψ, h1, h2⟩ := hPinned
  rw [hφ] at h1
  cases h1
  simp only [Checker.acceptsNamed, h2] at hAcc
  exact accepted_semValid_of_faithful_of_semSound C R hFaithful hSemSound w [] φ hAcc

/-- **K1 non-vacuity.**  The hypotheses of K1 hold together for a checker that
is not degenerate: the recomputing re-checker for the standard rules is
faithful and complete, the standard rules are semantically sound, and the
checker accepts a certificate for `⊢ ⊥ → ⊥`. -/
theorem k1_nonvacuous :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    Complete (recheckRecompute stdRules) stdRules ∧
    (recheckRecompute stdRules).accepts topCert [] Form.top = true :=
  ⟨recheckRecompute_faithful stdRules, stdRules_semSound,
   recheck_complete .recompute stdRules, by decide⟩

/-- **K1-pinned non-vacuity.**  All hypotheses of
`pinned_accepted_name_semValid_of_faithful_of_semSound` hold for the
recomputing re-checker, the standard rules, the official table on the name
`"True"`, and the antecedent of the conclusion is met by `topCert`. -/
theorem k1_pinned_nonvacuous :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    Pinned officialTable officialTable "True" ∧
    (recheckRecompute stdRules).acceptsNamed officialTable topCert "True" = true :=
  ⟨recheckRecompute_faithful stdRules, stdRules_semSound, by decide, by decide⟩

/-- The official meaning of `"False"` is not valid. -/
theorem officialTable_False_not_valid :
    ¬ ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ :=
  fun h => not_semValid_nil_bot (h .bot (by decide))

/-- **K1-pinned without `Faithful`.**  Every other hypothesis of K1-pinned holds
(sound rules, the official table pinned to itself on `"False"`), the checker is
the missing-guard mutant, and the conclusion fails: the mutant accepts a proof
object for `"False"`, whose official meaning `⊥` is not valid. -/
theorem pinned_name_semValid_fails_without_faithful :
    SemSound stdRules ∧
    Pinned officialTable officialTable "False" ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    ¬ (∀ w, (recheckNoHypGuard stdRules).acceptsNamed officialTable w "False" = true →
        ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ) :=
  ⟨stdRules_semSound, by decide, ex_faithful_recheckNoHypGuard_neg,
   fun h => officialTable_False_not_valid (h (bogusHypCert .bot) (by decide))⟩

/-- **K1-pinned without `SemSound`.**  The recomputing re-checker for the
unsound `badRules` is faithful, the official table is pinned to itself on
`"False"`, and the conclusion fails. -/
theorem pinned_name_semValid_fails_without_semSound :
    Faithful (recheckRecompute badRules) badRules ∧
    Pinned officialTable officialTable "False" ∧
    ¬ SemSound badRules ∧
    ¬ (∀ w, (recheckRecompute badRules).acceptsNamed officialTable w "False" = true →
        ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ) :=
  ⟨recheckRecompute_faithful badRules, by decide, ex_semSound_badRules_neg.1,
   fun h => officialTable_False_not_valid (h badBotCert (by decide))⟩

/-- **K1-pinned without `Pinned`.**  The recomputing re-checker for the sound
standard rules, with the poisoned table that renames `"False"` to `⊥ → ⊥`:
faithful, sound, not pinned, and the conclusion fails. -/
theorem pinned_name_semValid_fails_without_pinned :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    ¬ Pinned officialTable poisonedTable "False" ∧
    ¬ (∀ w, (recheckRecompute stdRules).acceptsNamed poisonedTable w "False" = true →
        ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ) :=
  ⟨recheckRecompute_faithful stdRules, stdRules_semSound, by decide,
   fun h => officialTable_False_not_valid (h topCert (by decide))⟩

/-- **What the definedness clause of `Pinned` contributes.**  Under
`Pinned official P name`, the universal form of K1-pinned's conclusion
(`∀ φ, official.lookup name = some φ → SemValid [] φ`) is equivalent to the
existential form (`name` has an official meaning, and it is valid). -/
theorem pinned_official_meaning_forall_iff_exists
    {official P : StmtTable} {name : String} (hPinned : Pinned official P name) :
    (∀ φ, official.lookup name = some φ → SemValid [] φ) ↔
      (∃ φ, official.lookup name = some φ ∧ SemValid [] φ) := by
  obtain ⟨ψ, hOff, _⟩ := hPinned
  constructor
  · intro h
    exact ⟨ψ, hOff, h ψ hOff⟩
  · rintro ⟨φ, hφ, hVal⟩ φ' hφ'
    rw [hφ] at hφ'
    cases hφ'
    exact hVal

/-- **K1-pinned's universal conclusion needs only agreement on defined official
names.**  If `P` resolves `name` to the official formula whenever `name` is
officially defined, the conclusion of K1-pinned already holds; the definedness
clause of `Pinned` is not used.  It matters for the existential reading
(`pinned_official_meaning_forall_iff_exists`) and for the decision procedure
`decide (Pinned official P name)`, which also rejects officially undefined
names (`ex_pinned_undefined_neg`). -/
theorem accepted_name_semValid_of_faithful_of_semSound_of_agreement
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R)
    {official P : StmtTable} {name : String}
    (hAgree : ∀ φ, official.lookup name = some φ → P.lookup name = some φ) :
    ∀ w : C.Wit, C.acceptsNamed P w name = true →
      ∀ φ, official.lookup name = some φ → SemValid [] φ := by
  intro w hAcc φ hOff
  have hP := hAgree φ hOff
  simp only [Checker.acceptsNamed, hP] at hAcc
  exact accepted_semValid_of_faithful_of_semSound C R hFaithful hSemSound w [] φ hAcc

/-! ## K2 — each layer is necessary -/

/-- **K2a (semantic soundness is necessary).**  The recomputing re-checker for
`badRules` is faithful (and complete) for `badRules`, yet it accepts the
certificate `badBotCert` for `⊢ ⊥`, which is not semantically valid; the only
K1 hypothesis that fails is `SemSound badRules`. -/
theorem faithful_checker_for_unsound_rules_accepts_bot :
    Faithful (recheckRecompute badRules) badRules ∧
    Complete (recheckRecompute badRules) badRules ∧
    ¬ SemSound badRules ∧
    (recheckRecompute badRules).accepts badBotCert [] .bot = true ∧
    ¬ SemValid [] .bot :=
  ⟨recheckRecompute_faithful badRules, recheck_complete .recompute badRules,
   ex_semSound_badRules_neg.1, by decide, not_semValid_nil_bot⟩

/-- **K2b (faithfulness is necessary).**  The standard rules are semantically
sound, yet the missing-guard mutant `recheckNoHypGuard stdRules` accepts the
certificate `bogusHypCert ⊥` for `⊢ ⊥`; the only K1 hypothesis that fails is
faithfulness. -/
theorem unfaithful_checker_for_sound_rules_accepts_bot :
    SemSound stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (recheckNoHypGuard stdRules).accepts (bogusHypCert .bot) [] .bot = true ∧
    ¬ SemValid [] .bot :=
  ⟨stdRules_semSound, ex_faithful_recheckNoHypGuard_neg, by decide, not_semValid_nil_bot⟩

/-- **K2c (pinning is necessary).**  A faithful checker for semantically sound
rules accepts a proof of the *name* `"False"` when the accompanying prelude
`poisonedTable` renames `"False"` to the provable formula `⊥ → ⊥`.  The
official meaning of `"False"` is `⊥`.  The only thing that fails is
`Pinned officialTable poisonedTable "False"`. -/
theorem unpinned_faithful_checker_for_sound_rules_accepts_renamed_False :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    officialTable.lookup "False" = some Form.bot ∧
    poisonedTable.lookup "False" = some Form.top ∧
    (recheckRecompute stdRules).acceptsNamed poisonedTable topCert "False" = true ∧
    ¬ Pinned officialTable poisonedTable "False" :=
  ⟨recheckRecompute_faithful stdRules, stdRules_semSound, by decide, by decide, by decide,
   by decide⟩

/-- **K2c, positive half.**  With pinning, the same checker accepts no proof
object for the name `"False"`, whatever table accompanies the proof. -/
theorem pinned_False_never_accepted (P : StmtTable) (w : Cert)
    (hPinned : Pinned officialTable P "False") :
    (recheckRecompute stdRules).acceptsNamed P w "False" = false :=
  not_acceptsNamed_of_pinned_bot (recheckRecompute_faithful stdRules) stdRules_consistent
    (by decide) hPinned w

/-- **K2d (recomputation of derived fields is necessary).**  Over one and the
same certificate format, for the semantically sound standard rules:

* the re-checker that *trusts* the derived `arity` field accepts `lyingCert ⊥`
  for `⊢ ⊥`;
* the re-checker that *recomputes* it rejects that certificate, and in fact
  rejects every certificate for `⊢ ⊥`;
* the certificate is dishonest, and on honest certificates the two re-checkers
  agree on every sequent.

Logically this is an instance of K2b (the trusting re-checker is an unfaithful
checker); its content is the mechanism and the paired positive statement. -/
theorem trusting_rechecker_accepts_bot_recomputing_rechecker_rejects :
    SemSound stdRules ∧
    (recheckTrust stdRules).accepts (lyingCert .bot) [] .bot = true ∧
    (recheckRecompute stdRules).accepts (lyingCert .bot) [] .bot = false ∧
    (∀ c : Cert, (recheckRecompute stdRules).accepts c [] .bot = false) ∧
    Cert.honest stdRules (lyingCert .bot) = false ∧
    (∀ (c : Cert) (Γ : Ctx) (φ : Form), Cert.honest stdRules c = true →
      (recheckTrust stdRules).accepts c Γ φ = (recheckRecompute stdRules).accepts c Γ φ) :=
  ⟨stdRules_semSound, by decide, by decide,
   not_accepts_bot_of_faithful_of_semSound _ _ (recheckRecompute_faithful stdRules)
     stdRules_semSound,
   rfl,
   fun _ Γ φ hc => recheckTrust_eq_recheckRecompute_of_honest hc Γ φ⟩

/-- **Honesty is necessary for `execCert_trust_eq_recompute_of_honest`.**  On
the dishonest certificate `lyingCert ⊥` (rule 8, `botElim`, stored with
`arity = 0`) the trusting and recomputing policies execute differently from
the empty stack: the hypothesis `Cert.honest R c = true` fails and so does the
conclusion. -/
theorem execCert_trust_eq_recompute_fails_without_honest :
    Cert.honest stdRules (lyingCert .bot) = false ∧
    ¬ (∀ stk : Stack, execCert .trust stdRules stk (lyingCert .bot) =
        execCert .recompute stdRules stk (lyingCert .bot)) :=
  ⟨rfl, fun h => absurd (h []) (by decide)⟩

/-- A lying `arity` of `0` lets the trusting re-checker derive any instance of
a rule's conclusion from nothing.  For the standard rules, rule 8 (`botElim`)
has conclusion `?0`, so every formula is accepted.  (For a general rule table
this makes `recheckTrust R` unfaithful only when some rule with premises has a
conclusion instance that is not otherwise derivable in `R` from the empty
context; a table whose premise-carrying rules are all redundant can make
`recheckTrust R` faithful.) -/
theorem recheckTrust_accepts_everything (φ : Form) :
    (recheckTrust stdRules).accepts (lyingCert φ) [] φ = true := by
  show (execCert .trust stdRules [] (lyingCert φ) == some [([], φ)]) = true
  simp [lyingCert, execCert, stdRules, premisesToCheck, popPremises, instPat, substLookup]

/-- The missing-guard mutant likewise accepts every formula. -/
theorem recheckNoHypGuard_accepts_everything (φ : Form) :
    (recheckNoHypGuard stdRules).accepts (bogusHypCert φ) [] φ = true := by
  show (execCertNoHypGuard .recompute stdRules [] (bogusHypCert φ) == some [([], φ)]) = true
  simp [bogusHypCert, execCertNoHypGuard]

/-! ## Quorums of two checkers -/

/-- **Separate-artifact quorum of two unfaithful checkers.**  The quorum of the
arity-trusting re-checker and the missing-guard mutant accepts `⊢ ⊥` for the
semantically sound standard rules *when each member is given its own
certificate*: `lyingCert ⊥` for the first, `bogusHypCert ⊥` for the second.
Each of those certificates is rejected by the other member.  (Positive halves:
`quorum_faithful_left` / `quorum_faithful_right`; and, for one shared
certificate, `shared_artifact_quorum_of_checkers_with_disjoint_defects_is_faithful`.) -/
theorem separate_artifact_quorum_of_two_unfaithful_checkers_accepts_bot :
    SemSound stdRules ∧
    (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)).accepts
        (lyingCert .bot, bogusHypCert .bot) [] .bot = true ∧
    (recheckNoHypGuard stdRules).accepts (lyingCert .bot) [] .bot = false ∧
    (recheckTrust stdRules).accepts (bogusHypCert .bot) [] .bot = false ∧
    ¬ Faithful (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)) stdRules := by
  have hacc : (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)).accepts
      (lyingCert .bot, bogusHypCert .bot) [] .bot = true := by decide
  exact ⟨stdRules_semSound, hacc, by decide, by decide,
    fun h => stdRules_consistent (h _ [] .bot hacc)⟩

/-- **Shared-artifact quorum of two different checkers with a shared defect.**
`recheckTrustNoHypGuard` and `recheckNoHypGuard` are different checkers (they
disagree on `lyingCert ⊥`) that share one defect (the missing `hyp` guard).
Their shared-artifact quorum accepts the single certificate `bogusHypCert ⊥`
for `⊢ ⊥`, for the semantically sound standard rules, and is unfaithful. -/
theorem shared_artifact_quorum_of_checkers_with_a_shared_defect_accepts_bot :
    SemSound stdRules ∧
    ¬ Faithful (recheckTrustNoHypGuard stdRules) stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (recheckTrustNoHypGuard stdRules).accepts (lyingCert .bot) [] .bot = true ∧
    (recheckNoHypGuard stdRules).accepts (lyingCert .bot) [] .bot = false ∧
    (sharedQuorum (recheckTrustNoHypGuard stdRules) (recheckNoHypGuard stdRules) id).accepts
        (bogusHypCert .bot) [] .bot = true ∧
    ¬ Faithful
        (sharedQuorum (recheckTrustNoHypGuard stdRules) (recheckNoHypGuard stdRules) id)
        stdRules := by
  have hacc : (sharedQuorum (recheckTrustNoHypGuard stdRules) (recheckNoHypGuard stdRules) id).accepts
      (bogusHypCert .bot) [] .bot = true := by decide
  have h1 : (recheckTrustNoHypGuard stdRules).accepts (lyingCert .bot) [] .bot = true := by decide
  exact ⟨stdRules_semSound,
    fun h => stdRules_consistent (h _ [] .bot h1),
    ex_faithful_recheckNoHypGuard_neg, h1, by decide, hacc,
    fun h => stdRules_consistent (h _ [] .bot hacc)⟩

/-- **Shared-artifact quorum of two checkers with disjoint defects is faithful
(here).**  Neither the arity-trusting re-checker nor the missing-guard mutant is
faithful to the standard rules, and their separate-artifact quorum accepts
`⊢ ⊥`, but their shared-artifact quorum is faithful
(`sharedQuorum_recheckTrust_recheckNoHypGuard_faithful`, for every rule table)
and accepts the honest certificate `topCert` for `⊢ ⊥ → ⊥`. -/
theorem shared_artifact_quorum_of_checkers_with_disjoint_defects_is_faithful :
    ¬ Faithful (recheckTrust stdRules) stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)).AcceptsBot ∧
    Faithful (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) id) stdRules ∧
    (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) id).accepts
        topCert [] Form.top = true :=
  ⟨ex_faithful_recheckTrust_neg, ex_faithful_recheckNoHypGuard_neg,
   ⟨(lyingCert .bot, bogusHypCert .bot), by decide⟩,
   sharedQuorum_recheckTrust_recheckNoHypGuard_faithful stdRules, by decide⟩

/-! ## Same-artifact quorums under a translation of proof objects -/

/-- A shared-artifact quorum is faithful as soon as its second member is, for
every translation `tr` of proof objects. -/
theorem sharedQuorum_faithful_right {C D : Checker} {tr : C.Wit → D.Wit} {R : RuleSet}
    (h : Faithful D R) : Faithful (sharedQuorum C D tr) R := by
  intro w Γ φ hw
  simp only [sharedQuorum, Bool.and_eq_true] at hw
  exact h (tr w) Γ φ hw.2

/-- A translation of certificates that rewrites the arity-trusting re-checker's
exploit certificate `lyingCert φ` into the missing-guard mutant's exploit
certificate `bogusHypCert φ`, and leaves every other certificate unchanged. -/
def exploitTranslator : Cert → Cert
  | [.rule [] 8 [φ] 0] => bogusHypCert φ
  | c => c

/-- **The disjoint-defect same-artifact quorum relies on the identity
translation.**  With the translation `exploitTranslator` in place of `id`, the
same-artifact quorum of the arity-trusting re-checker and the missing-guard
mutant accepts `lyingCert ⊥` for `⊢ ⊥` and is not faithful to the sound
standard rules: each member is shown the artifact that exploits its own
defect.  (`sharedQuorum_recheckTrust_recheckNoHypGuard_faithful` is stated for
`tr = id` only.) -/
theorem shared_artifact_quorum_of_disjoint_defects_accepts_bot_under_exploit_translator :
    SemSound stdRules ∧
    ¬ Faithful (recheckTrust stdRules) stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) exploitTranslator).accepts
        (lyingCert .bot) [] .bot = true ∧
    ¬ Faithful
        (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) exploitTranslator)
        stdRules := by
  have hacc :
      (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) exploitTranslator).accepts
        (lyingCert .bot) [] .bot = true := by decide
  exact ⟨stdRules_semSound, ex_faithful_recheckTrust_neg, ex_faithful_recheckNoHypGuard_neg,
    hacc, fun h => stdRules_consistent (h _ [] .bot hacc)⟩

end Toy.KernelTrust
