# Proof-checker trust layers: faithfulness, semantic soundness, statement pinning, recomputation, and verifier rings

## Summary

**Citing rule.** *An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Every result below is a Lean 4 theorem about a **toy model**, proved without `sorry` and kernel-checked under `leanprover/lean4:v4.34.1` (basis: execution, Lean kernel check; axioms at most `propext`, `Classical.choice`, `Quot.sound`). None of them is a theorem about a real proof checker; connections to real systems are separate claims labelled *derived (modeling bridge)*. One sentence per result, hypotheses included. **Read the non-claims under `## Boundaries` (listed first there) and on each card under `## Findings` before using any of them.**

All Lean names below live in namespace `Toy.KernelTrust`. The provability-interface predicates (`MpClosed`, `HasEfq`, `ImpClosed`, `D1`–`D3`, `HBL`, `LobRule`, `GodelII`, `CrossNec`, `CrossDistrib`, `CrossSigma1`, `CrossHBL`, `CrossHBLFrom`, `Consistent`, `con`) live in `Toy.KernelTrust.ProvFamily` and are written with dot notation (`F.ImpClosed i`).

| Id | Plain claim |
|:--|:--|
| **K1** | In the toy rules-as-data propositional logic, if a checker accepts only sequents derivable from the rule table `R` (`Faithful C R`) and every sequent derivable from `R` is truth-table valid (`SemSound R`), then every sequent the checker accepts is truth-table valid; in particular it never accepts `[] ⊢ ⊥`. |
| **K1-pinned** | If moreover the statement table shipped with a proof is pinned to the official table on a name (the name is officially defined and the shipped table resolves it to the same formula), then whenever the checker accepts a proof object for that name, the name's official meaning is valid. The conclusion is stated for every official meaning of the name; it says something only because `Pinned` asserts that the name is officially defined (under `Pinned` it is equivalent to "the official meaning exists and is valid"). |
| **K2a** | A checker that is faithful (and complete) for an unsound rule table accepts `[] ⊢ ⊥`: only `SemSound` fails. |
| **K2b** | An unfaithful checker (one deleted guard) for the sound standard rules accepts `[] ⊢ ⊥`: only `Faithful` fails. A separate-artifact quorum of two differently broken checkers accepts `[] ⊢ ⊥` when each is given its own certificate, and a same-artifact quorum of two different checkers that share one defect accepts one certificate for `[] ⊢ ⊥`. |
| **K2c** | A faithful checker for sound rules accepts a proof of the *name* `"False"` when the accompanying table renames `"False"` to a provable formula: only `Pinned` fails. Conversely, whenever the shipped table `P` is pinned to the official table on `"False"` (hypothesis `Pinned officialTable P "False"`), the same checker accepts no proof object for that name. |
| **K2d** | Over one certificate format with a derived `arity` field, the re-checker that trusts the stored field accepts `[] ⊢ ⊥` on a dishonest certificate; the one that recomputes it rejects every certificate for `[] ⊢ ⊥`; on honest certificates they agree. |
| **S-shared-quorum** | For every rule table, the same-artifact quorum of the arity-trusting re-checker and the missing-guard mutant of the recomputing re-checker, both reading the identical certificate (translation `tr = id`), is faithful, although neither member is faithful to the standard rules. |
| **K3a** | In a closed ring of verifier nodes sharing one rule table, **assuming** that every node with a faithful object-level checker also has sound certificate checking (`FaithfulImpliesMetaSound`), one node with sound certificate checking (`MetaSound` anchor) makes every node's object-level checker faithful; with consistent rules no node then accepts `[] ⊢ ⊥`. |
| **K3b** | Three unfaithful checkers for sound rules close a ring of faithfulness certificates while each accepts `[] ⊢ ⊥`: only the anchor is missing. One unfaithful checker already certifies itself. |
| **K3c** | A closed ring of three faithful checkers over unsound rules satisfies every hypothesis and the conclusion of K3a's faithfulness theorem, and every node accepts `[] ⊢ ⊥`; the consistency hypothesis of K3a's `⊥` corollary fails there (the rules are inconsistent). |
| **K4a** | For `n` abstract theories over one sentence language: if every theory is implicationally closed, at least one has Gödel's second incompleteness property (`GodelII`), and the cross-theory Hilbert–Bernays–Löb conditions hold (`CrossHBL`), then whenever each theory proves the consistency statement of its ring successor, every theory proves `⊥`. |
| **K4a-local** | On such a ring of consistency proofs, any single theory that is implicationally closed, has `GodelII`, and satisfies the cross-theory conditions towards every other theory (`CrossHBLFrom`) proves `⊥`; nothing else is assumed about the other theories, and no theory's own `D1`–`D3` is assumed. |
| **K4b** | Dropping only formalised Σ₁-completeness (`CrossSigma1`, in both directions), two consistent abstract theories exist that prove each other's consistency statement, and for every `n ≥ 2` a ring of `n` consistent abstract theories exists in which each theory proves its ring successor's consistency statement, while satisfying every other hypothesis of K4a; a variant exists in which no theory proves its own inconsistency statement. |
| **K5** | An inconsistent abstract theory closed under modus ponens and with ex falso proves the local reflection schema `□ⱼA → A` and the consistency statement of every theory in its family, itself included. |
| **K5-iff** | For a theory closed under modus ponens, with ex falso and with `GodelII`, proving its own local reflection schema is *equivalent* to inconsistency. |
| **S-semSound** | Every sequent derivable from the standard natural-deduction table is truth-table valid. |
| **S-recompute** | For every rule table, the recomputing re-checker and the trace checker are faithful, both certificate re-checkers are complete, and on honest certificates (`Cert.honest R c = true`) the two field policies agree. |
| **S-naive-interface** | A provability operator on meta-level propositions with "true implies provable" and Löb's rule is never consistent, so impossibility theorems over that interface are vacuous. |

## Applicability

**Model fidelity: toy model.** Every definition is a toy:

* The object logic is propositional (`var`, `⊥`, `→`, `∧`, `∨`). Rules are data (`RuleSet`): natural-deduction schemata with discharged hypotheses. There are no binders, types, definitional equality, universes or inductive definitions.
* A `Checker` is a mathematical function `Wit → Ctx → Form → Bool`. There is no notion of binary, compiler, runtime, memory, file format or I/O.
* The reference semantics is two-valued truth tables (`evalForm`). It is the trust root of everything called "semantic".
* A statement table maps names to formulas (first binding wins); statements have no definitional dependencies, and named statements are checked in the empty context only.
* A verifier ring has one rule table shared by all nodes, and its claim language contains one claim per ring member ("node `j` is faithful"); the toy logic cannot express such a claim, so self-hosted rings use opaque encodings.
* The provability results (K4, K5) are about an abstract interface `ProvFamily` (one sentence type shared by all theories, falsum, implication, one box per theory, a theoremhood predicate per theory). Countermodels are Kripke-style, neighbourhood-style, free-syntax or two-valued structures. No arithmetised provability predicate is constructed anywhere.

What the definitions are *meant* to capture, and the known gaps:

| Toy notion | Intended real-world reading | Known gap |
|:--|:--|:--|
| `Derivable R Γ φ` | the declarative inference specification of a kernel | propositional only |
| `Faithful C R` | "the kernel implementation accepts only what the specification derives" (the claim targeted by Lean4Lean, MetaRocq, Candle, Milawa) | source-level function only; soundness direction only |
| `SemSound R` | soundness of the logic for a model | the model (truth tables) is trivial compared with models of type theories; relative to a trusted semantics |
| `Pinned official P name` | comparing the statement that was checked with an independently held statement | no definitional dependencies, notation or elaboration; empty context only |
| `recheckTrust` vs `recheckRecompute` | an export re-checker that trusts vs recomputes producer-supplied derived data | one field, one format |
| `quorum` vs `sharedQuorum` | two checkers given separate artifacts vs two checkers re-checking one exported artifact | two specific defects; the translation `tr` of proof objects between the two checkers is trusted, and the disjoint-defect result is stated for `tr = id` |
| `VerifierRing`, `MetaSound` | checkers that check certificates of each other's faithfulness | one shared rule table; claims only about ring members; claims are opaque tokens |
| `ProvFamily`, `CrossHBL`, `GodelII` | formal systems reasoning about each other's provability | abstract; one shared sentence language; applies to concrete systems only if the named conditions are verified for them |

Toolchain: Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); core Lean only (no Mathlib, no other Lake dependency). The Lake project is `lean/` (library `KernelTrust`, eleven modules); `lean/AxiomAudit.lean` is an axiom-listing program outside the library target, and `support/revalidate.py` is the revalidation script (see `## Revalidation`).

**How the subjects in `REPORT.json` relate.** The Lean toolchain is the proof checker that kernel-checked every theorem here; nothing in the package is a statement *about* that toolchain. The two `leanprover/lean4` merge commits (pull requests 14807 and 14806) are the real-world events behind the modeling-bridge notes on K2b and S-shared-quorum; they were examined only through their published descriptions, not their code. The papers are the primary sources for the results tiered T0 (K1, K5, K5-iff, S-semSound, S-recompute) and the main prior art for the others; the Mathematics Stack Exchange answer is the informal source of the two-theory case of K4a. Further prior art is listed under `## Evidence`.

### Definitions

Each core definition with a sentence on intent and its proved positive and negative examples (theorem names unless marked `def`).

| Definition | Meant to capture | Positive example | Negative example |
|:--|:--|:--|:--|
| `instPat`, `substLookup` | instantiating a rule schema; out-of-range metavariables read as `⊥` | `ex_instPat_pos` | `ex_instPat_neg`, `ex_substLookup_neg` |
| `Derivable R Γ φ` | derivations from hypotheses and instances of rules of the table `R` | `ex_derivable_top_pos`, `ex_derivable_hyp_pos` | `ex_derivable_empty_neg` |
| `stdRules` / `badRules` / `anyImpRules` | a sound table / an inconsistent table (deriving every formula: `badRules_derives_every_formula`) / a consistent but unsound table | `ex_semSound_stdRules_pos` | `ex_semSound_badRules_neg`, `ex_consistent_not_semSound_anyImpRules` |
| `evalForm`, `evalCtx` | truth-table evaluation | `ex_evalForm_top_pos`, `ex_evalCtx_nil_pos` | `ex_evalForm_bot_neg`, `ex_evalCtx_bot_neg` |
| `SemValid Γ φ` | every valuation satisfying `Γ` satisfies `φ` | `ex_semValid_top_pos`, `ex_semValid_peirce_pos` | `ex_semValid_var_neg` |
| `SemSound R` | every `R`-derivable sequent is valid | `ex_semSound_stdRules_pos`, `ex_semSound_empty_pos` | `ex_semSound_badRules_neg` |
| `Consistent R` | `R` does not derive `[] ⊢ ⊥` (strictly weaker than `SemSound`) | `ex_semSound_stdRules_pos` | `ex_semSound_badRules_neg` |
| `Faithful C R` | the checker accepts only `R`-derivable sequents (soundness direction only) | `ex_faithful_recheckRecompute_pos`; degenerate: `ex_faithful_rejectAll_pos` | `ex_faithful_acceptAll_neg`, `ex_faithful_recheckTrust_neg`, `ex_faithful_recheckNoHypGuard_neg` |
| `Complete C R` | every derivable sequent has an accepted proof object | `ex_complete_acceptAll_pos`, `recheck_complete` | `ex_complete_rejectAll_neg` |
| `Checker.AcceptsBot` | some proof object is accepted for `[] ⊢ ⊥` | `ex_acceptsBot_acceptAll_pos` | `ex_acceptsBot_rejectAll_neg` |
| `quorum C D` | accept when both checkers accept, each on its own proof object | `ex_quorum_pos` | `ex_quorum_neg` |
| `sharedQuorum C D tr` | accept when both checkers accept the same proof object | `ex_sharedQuorum_pos` | `ex_sharedQuorum_neg` |
| `recheck pol R` (`recheckRecompute`, `recheckTrust`) | stack-machine certificate re-checker under a policy for the derived `arity` field | `ex_recheckRecompute_accepts_topCert_pos`, `ex_recheckTrust_accepts_topCert_pos` | `ex_recheckRecompute_rejects_topCert_neg`, `ex_faithful_recheckTrust_neg` |
| `premisesToCheck`, `popPremises` | which premises a rule step discharges under a policy | `ex_premisesToCheck_pos`, `ex_popPremises_pos` | `ex_premisesToCheck_neg`, `ex_popPremises_neg` |
| `Cert.honest R c` | stored `arity` fields equal the table's arities; a step naming a nonexistent rule counts as honest; a stored arity above the rule's arity is dishonest but treated like an honest one by both policies | `ex_honest_topCert_pos` | `ex_honest_lyingCert_neg` |
| `Cert.HypsOk c` | every hypothesis step passes the membership guard | `ex_hypsOk_topCert_pos` | `ex_hypsOk_bogusHypCert_neg` |
| `recheckNoHypGuard R`, `recheckTrustNoHypGuard R` | the recomputing / trusting re-checker with the hypothesis guard deleted | `ex_recheckNoHypGuard_accepts_topCert_pos`, `ex_recheckTrustNoHypGuard_accepts_topCert_pos` | `ex_faithful_recheckNoHypGuard_neg`, `ex_faithful_recheckTrustNoHypGuard_neg` |
| `traceChecker R` | a second, differently designed faithful checker (linear table citing earlier lines) | `ex_traceChecker_accepts_topTrace_pos` | `ex_traceChecker_rejects_selfCitation_neg` |
| `Checker.acceptsNamed C P w name` | checking a *name* by resolving it in the table shipped with the proof (empty context) | `ex_acceptsNamed_pos` | `ex_acceptsNamed_neg` |
| `Pinned official P name` | `name` is officially defined and the shipped table resolves it to the same formula | `ex_pinned_official_pos`, `ex_pinned_poisoned_true_pos` | `ex_pinned_poisoned_neg`, `ex_pinned_undefined_neg` |
| `ringNext`, `ringIter` | successor / `k`-fold successor on a ring of `n` nodes | `ex_ringNext_wrap_pos`, `ex_ringNext_self_pos`, `ex_ringIter_pos` | `ex_ringNext_neg`, `ex_ringIter_neg` |
| `RingClosed`, `LinkCertified` | every node accepts a faithfulness certificate for its successor | `ex_ringClosed_pos` | `ex_ringClosed_neg` |
| `MetaSound V R i` | every faithfulness claim about a ring member that node `i` accepts is true | `ex_metaSound_pos` (discriminating: rejects a false claim) | `ex_metaSound_neg` |
| `FaithfulImpliesMetaSound V R` | **the named assumption**: a node with a faithful object-level checker has sound certificate checking | `ex_faithfulImpliesMetaSound_pos` | `ex_faithfulImpliesMetaSound_neg` |
| `selfHostedRing`, `ClaimReflection` | certificates checked by the node's own kernel on an encoded claim; derivable encoded claims are true | `ex_claimReflection_pos` (non-vacuous: one derivable and one underivable claim) | `ex_claimReflection_neg` |
| `ProvFamily.Consistent`, `ProvFamily.con` | theory `i` does not prove `⊥`; the sentence `□ⱼ⊥ → ⊥` | `ex_consistent_pos`, `ex_con_pos` | `ex_consistent_neg`, `ex_con_neg` |
| `MpClosed`, `ImpClosed` | modus ponens; modus ponens plus the Hilbert axiom schemes K and S (no ex falso) | `ex_mpClosed_pos`, `ex_impClosed_pos` | `ex_mpClosed_neg`, `ex_impClosed_neg` |
| `HasEfq` | ex falso `⊥ → A` | `ex_hasEfq_pos` | `ex_hasEfq_neg` |
| `D1`, `D2`, `D3`, `HBL` | the Hilbert–Bernays–Löb derivability conditions for one theory | `ex_hbl_pos` | `ex_d1_neg`, `ex_hbl_neg` |
| `LobRule` | if `i ⊢ □ᵢA → A` then `i ⊢ A` | `ex_lobRule_pos` | `ex_lobRule_neg` |
| `GodelII` | if `i ⊢ □ᵢ⊥ → ⊥` then `i ⊢ ⊥` (Löb's rule at `A := ⊥`) | `ex_godelII_pos` | `ex_godelII_neg` |
| `CrossNec`, `CrossDistrib`, `CrossSigma1` | the three cross-theory conditions | `ex_crossNec_pos`, `ex_crossDistrib_pos`, `ex_crossSigma1_pos` | `ex_crossNec_neg`, `ex_crossDistrib_neg`, `ex_crossSigma1_neg` |
| `CrossHBL`, `CrossHBLFrom` | the cross-theory conditions for all index combinations (diagonal = `HBL`); those from one theory to every other theory | `ex_crossHBL_pos`, `ex_crossHBLFrom_pos` | `ex_crossHBL_neg`, `ex_crossHBLFrom_neg` |
| `PointedKripke.toFamily` | theories read off a pointed Kripke model: "`i` proves `A`" is truth of `□ᵢA` at the base world | `ex_toFamily_pos` | `ex_toFamily_neg` |
| `PointedKripke.GLFrame` | transitive and conversely well-founded relation | `ex_glFrame_pos` | `ex_glFrame_neg` |
| `NaivePropProv` (design counter-example) | a degenerate interface that conflates truth with theoremhood | `NaivePropProv.nonempty` (via `def NaivePropProv.trivial`) | `NaivePropProv.not_not_prov_false` |

### Concrete models and fixed objects

The examples, witnesses and counterexamples are built from the following objects. The descriptions are one-line paraphrases of the Lean definitions in `lean/KernelTrust/`, not verbatim quotes; `⊤` abbreviates `Form.top`.

| Object | Definition |
|:--|:--|
| `Form.top` (`⊤`) | the formula `⊥ → ⊥` |
| `acceptAll`, `rejectAll` | the checkers (proof objects of type `Unit`) that accept, respectively reject, every sequent |
| `topCert`, `topTrace` | an honest certificate and a trace for `[] ⊢ ⊤` under the standard rules: the hypothesis step `[⊥] ⊢ ⊥`, then `impIntro` |
| `bogusHypCert φ` | the one-step certificate that pushes `[] ⊢ φ` as a hypothesis step, accepted only by re-checkers without the hypothesis-membership guard |
| `badBotCert` | an honest certificate for `[] ⊢ ⊥` under `badRules` |
| `officialTable`, `poisonedTable` | the statement tables `[("False", ⊥), ("True", ⊤)]` and `[("False", ⊤), ("True", ⊤)]` |
| `anyImpRules` | a one-rule table whose only rule has no premises and concludes every implication `A → B` (consistent, not semantically sound) |
| `faithfulRing R` | the self-hosted three-node ring whose object-level checkers are `recheckRecompute R`, `traceChecker R` and their separate-artifact quorum, with every faithfulness claim encoded as `⊤` |
| `buggyRing` | the self-hosted three-node ring of `acceptAll`, `recheckTrust stdRules` and `recheckNoHypGuard stdRules`, with the claim "node `j` is faithful" encoded as the atom `p_j` (see K3b) |
| `rubberStampRing` | two nodes, certificates of type `Unit`: node 0 has object-level checker `acceptAll` and accepts a certificate exactly for the claim about node 1; node 1 has object-level checker `recheckRecompute stdRules` and accepts every claim |
| `brokenLinkRing` | two nodes, certificates of type `Unit`: node 0 has object-level checker `recheckRecompute stdRules` and accepts no certificate; node 1 has object-level checker `acceptAll` and accepts a certificate exactly for the claim about node 0 |
| `trivialFamily ι` | one sentence, proved by every theory: every closure condition holds and every theory is inconsistent |
| `starFamily n`, `omegaStarFamily n` | Kripke families with one tip world, respectively one descending ω-chain of worlds, per theory (see K4b) |
| `leafFamily n` | the Kripke family on worlds `base`, `tip i` and `leaf i` (`i : Fin n`), where relation `j` relates `base` to `tip j`, and `tip i` to `leaf i` when `j = ringNext i` |
| `possibilityFamily n` | not a Kripke family: sentences are predicates on `Fin n` (`⊥` empty, `→` pointwise), theory `i` proves `A` iff `A i`, and `□ⱼA` holds at `w` iff `w = j` or `A` holds at some index |
| `reflexiveFamily ι` | the Kripke family on one world that every relation relates to itself, so `□ⱼA` is `A` |
| `omegaChainFamily` | two theories, Kripke worlds `none` (base) and `some k` (`k : Nat`): from the base, relation 1 reaches every `some k` and relation 0 every `some (k + 1)`; from `some m`, relation 1 reaches `some k` for `k < m` and relation 0 reaches `some (k + 1)` for `k + 1 < m` |
| `oneBrokenNecFamily` | two theories, Kripke worlds `false` (base) and `true`: relation 0 is `{(true, true)}` and relation 1 is `{(false, true)}`, so theory 0 proves every sentence (it is inconsistent) and theory 1 proves exactly the sentences true at `true` |
| `SynSent n` | free polymodal syntax: `bot`, `imp A B`, and `box j A` for `j : Fin n` |
| `noMpFamily n` | sentences `SynSent n`; theory `i` proves the least set containing every instance of K, S, ex falso, `CrossDistrib i j`, `CrossSigma1 i j k` and the ring axiom `□ⱼ⊥ → ⊥` for `j = ringNext i`, closed under cross-necessitation (`j ⊢ A` gives `i ⊢ □ⱼA`) but not under modus ponens |
| `noKSFamily n` | sentences `SynSent n`; no theory proves `⊥`; `i ⊢ □ⱼA` iff `j ⊢ A`; `i ⊢ A → B` iff (`i ⊢ A` implies `i ⊢ B`) and `A` is not literally `□ᵢB` |
| `noMpEfqFamily` | one theory over `SynSent 1` proving exactly `⊥` and every `⊥ → A` |
| `noEfqBoolFamily` | one theory: sentences are Booleans, `⊥ := true`, `A → B := !A || B`, every box is `true`, and the theory proves exactly `true` |
| `onlyBotFamily` | one theory over `SynSent 1` proving exactly `⊥` (quoted under `### Auxiliary witness statements`) |

## Findings

Tier legend: **T0** re-derivation of a known result in this vocabulary (the statement itself is a published or mechanised theorem); **T1** folklore made precise (a known observation, not found mechanised in this form); **T2** known result in a more usable form; **T3** claimed novel. No result in this package is claimed T2 or T3.

Tightness legend: `tight: counterexample <name>` (a kernel-checked instance in which every other hypothesis holds and the conclusion fails), `harmless`, `unknown`.

Basis for every Lean statement: **execution (Lean kernel check)**. Every statement in this section is proved without `sorry`; its axioms and its statement and definition-closure hashes are recorded under `## Evidence`. Every sentence relating a statement to a real system is a separate claim labelled **Basis: derived (modeling bridge)**, with its reasoning.

---

### K1 — faithfulness + semantic soundness ⇒ accepted statements are valid

```lean
theorem accepted_semValid_of_faithful_of_semSound
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R) :
    ∀ (w : C.Wit) (Γ : Ctx) (φ : Form), C.accepts w Γ φ = true → SemValid Γ φ

theorem not_accepts_bot_of_faithful_of_semSound
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R) :
    ∀ w : C.Wit, C.accepts w [] .bot = false
```

Unfolded: `Faithful C R := ∀ w Γ φ, C.accepts w Γ φ = true → Derivable R Γ φ`; `SemSound R := ∀ Γ φ, Derivable R Γ φ → SemValid Γ φ`; `SemValid Γ φ := ∀ v, evalCtx v Γ = true → evalForm v φ = true`.

* **Plain claim.** See `## Summary`.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T0: re-derivation, for a toy logic, of the two-step soundness architecture of verified proof checkers (implementation refines inference system; inference system sound for a semantics), mechanised at production scale (Kumar et al. 2016; Candle 2022; Milawa 2015).
* **Hypothesis ledger.**

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `Faithful C R` | links what the implementation accepts to what the rules derive | tight: counterexample `unfaithful_checker_for_sound_rules_accepts_bot` (K2b) |
  | `SemSound R` | links what the rules derive to the semantics. For the `⊥` part alone, `Consistent R` suffices (`not_acceptsBot_of_faithful_of_consistent`) and is strictly weaker (`ex_consistent_not_semSound_anyImpRules`) | tight: counterexample `faithful_checker_for_unsound_rules_accepts_bot` (K2a) |

* **Depth.** `definitional`: the main statement is the composition of the two definitions. It is an architectural reference point; the work is in *establishing* the hypotheses for a particular checker and rule table (S-recompute, S-semSound).
* **Non-vacuity witness.** `k1_nonvacuous`.
* **Non-claims.** (i) Toy propositional logic only. (ii) Nothing about binaries, compilers, runtimes, I/O or hardware. (iii) `Faithful` is one direction; `rejectAll` is faithful to everything. (iv) Validity is relative to the trusted reference semantics; a misconception shared by rules and semantics is invisible. (v) Without pinning, nothing is said about *which* statement was checked. (vi) No completeness claim for `stdRules`.
* **Prior art.** Kumar et al. 2016; Candle 2022 and 2025; Davis, Myreen 2015 (Milawa); Harrison 2006; Barras 2010; Sozeau et al. 2020 (MetaCoq, now MetaRocq; POPL and JAR); Carneiro 2026 (Lean4Lean); Barendregt, Wiedijk 2005 (de Bruijn criterion); Abel, Öhman, Vezzosi 2018.
* **Basis: derived (modeling bridge).** Real-world grounding: Lean4Lean, MetaRocq, Candle and Milawa are efforts to establish the *faithfulness* layer for real checkers. The MetaCoq POPL 2020 paper proves its checker correct "with respect to its formal specification and axiomatisation of part of its metatheory" and explains that the correctness of the specification itself cannot be proved completely inside Coq, "thus moving from a trusted code base (TCB) to a trusted theory base (TTB) paradigm": faithfulness relative to axiomatised metatheory, not a semantic-soundness theorem for the rules. Relativised *semantic soundness* (the `SemSound` layer, proved in a stronger metatheory) is what Harrison 2006, Kumar et al. 2016 and Barras 2010 establish. The toy theorem does not apply to any of these systems.
* **Design question.** Which assurance layers must a proof-checking pipeline have, and which class of defect does each fail to cover?

### K1-pinned — what pinning adds

```lean
theorem pinned_accepted_name_semValid_of_faithful_of_semSound
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R)
    {official P : StmtTable} {name : String} (hPinned : Pinned official P name) :
    ∀ w : C.Wit, C.acceptsNamed P w name = true →
      ∀ φ, official.lookup name = some φ → SemValid [] φ
```

Unfolded: `Pinned official P name := ∃ φ, official.lookup name = some φ ∧ P.lookup name = some φ`; `C.acceptsNamed P w name := match P.lookup name with | some φ => C.accepts w [] φ | none => false`.

```lean
theorem pinned_official_meaning_forall_iff_exists
    {official P : StmtTable} {name : String} (hPinned : Pinned official P name) :
    (∀ φ, official.lookup name = some φ → SemValid [] φ) ↔
      (∃ φ, official.lookup name = some φ ∧ SemValid [] φ)

theorem accepted_name_semValid_of_faithful_of_semSound_of_agreement
    (C : Checker) (R : RuleSet)
    (hFaithful : Faithful C R) (hSemSound : SemSound R)
    {official P : StmtTable} {name : String}
    (hAgree : ∀ φ, official.lookup name = some φ → P.lookup name = some φ) :
    ∀ w : C.Wit, C.acceptsNamed P w name = true →
      ∀ φ, official.lookup name = some φ → SemValid [] φ
```

* **Plain claim.** See `## Summary`. `Pinned` already asserts that `name` has an official meaning; the theorem says that meaning is valid whenever a proof of the name is accepted.
* **The definedness clause of `Pinned`.** The conclusion is universal (`∀ φ, official.lookup name = some φ → SemValid [] φ`) and is trivially true for a name that `official` does not define. Under `Pinned` it is equivalent to the existential reading "the name has an official meaning and that meaning is valid" (`pinned_official_meaning_forall_iff_exists`). The universal conclusion itself needs only that `P` agrees with `official` on officially defined names (`accepted_name_semValid_of_faithful_of_semSound_of_agreement`); the definedness clause is what rules out the vacuous case, and the decision procedure `decide (Pinned official P name)` accordingly also rejects officially undefined names (`ex_pinned_undefined_neg`).
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1: comparing the checked statement with an independently held statement is established practice (Pollack 1998; Adams 2016; the separate specification file of Metamath Zero, Carneiro 2020); not found mechanised in this form.
* **Hypothesis ledger.**

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `Faithful C R` | acceptance ⇒ derivability | tight: counterexample `pinned_name_semValid_fails_without_faithful` |
  | `SemSound R` | derivability ⇒ validity | tight: counterexample `pinned_name_semValid_fails_without_semSound` |
  | `Pinned official P name` | checked formula = official formula, and `name` is officially defined (the definedness clause is not needed for the universal conclusion, only for its existential reading; see above) | tight: counterexample `pinned_name_semValid_fails_without_pinned` (also K2c) |

* **Depth.** `shallow` (unfold, then K1).
* **Non-vacuity witness.** `k1_pinned_nonvacuous` (the name `"True"`, accepted on `topCert`).
* **Non-claims.** (i) Pinning a theorem's top-level name in a flat lookup table does not prevent soundness or meaning-drift attacks via modified definitional dependencies, hidden axioms in the ambient environment, or duplicate-key shadowing (`StmtTable` uses first-binding-wins `List.lookup`). (ii) `Checker.acceptsNamed` checks empty-context sequents (`[] ⊢ φ`) only; nothing is stated about named statements proved under non-empty assumption contexts or custom axioms. (iii) No notation, parsing or pretty-printing is modelled; Pollack-inconsistency in the sense of Wiedijk 2012 (parser/printer round trips) is related but not modelled. (iv) A wrong official table is invisible: pinning moves trust to the official table. (v) The theorem yields "the official meaning exists and is valid" only through the definedness clause of `Pinned`; a pipeline that compares the shipped table with the official one only on officially defined names, without checking definedness, obtains the universal statement and nothing more, which is vacuous for an officially undefined name.
* **Prior art.** Pollack 1998; Adams 2016; Carneiro 2020 (Metamath Zero); Wiedijk 2012 (related).
* **Design question.** As K1.

---

### K2 — each layer is necessary (kernel-checked counterexamples)

Each, except the positive half of K2c (`pinned_False_never_accepted`), has the form "every other hypothesis of K1 (or K1-pinned) holds and the conclusion fails".

**K2a** — semantic soundness is necessary.

```lean
theorem faithful_checker_for_unsound_rules_accepts_bot :
    Faithful (recheckRecompute badRules) badRules ∧
    Complete (recheckRecompute badRules) badRules ∧
    ¬ SemSound badRules ∧
    (recheckRecompute badRules).accepts badBotCert [] .bot = true ∧
    ¬ SemValid [] .bot
```

`badRules` is the standard table plus the rule "from `A → B` infer `B → A`"; it derives every formula.

**K2b** — faithfulness is necessary; quorums of two checkers.

```lean
theorem unfaithful_checker_for_sound_rules_accepts_bot :
    SemSound stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (recheckNoHypGuard stdRules).accepts (bogusHypCert .bot) [] .bot = true ∧
    ¬ SemValid [] .bot

theorem separate_artifact_quorum_of_two_unfaithful_checkers_accepts_bot :
    SemSound stdRules ∧
    (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)).accepts
        (lyingCert .bot, bogusHypCert .bot) [] .bot = true ∧
    (recheckNoHypGuard stdRules).accepts (lyingCert .bot) [] .bot = false ∧
    (recheckTrust stdRules).accepts (bogusHypCert .bot) [] .bot = false ∧
    ¬ Faithful (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)) stdRules

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
        stdRules
```

`recheckNoHypGuard` is the recomputing re-checker with the membership test of hypothesis steps deleted; `recheckTrustNoHypGuard` is the trusting re-checker with the same deletion. `quorum C D` takes one proof object per checker; `sharedQuorum C D id` makes both checkers read the same certificate.

**K2c** — pinning is necessary.

```lean
theorem unpinned_faithful_checker_for_sound_rules_accepts_renamed_False :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    officialTable.lookup "False" = some Form.bot ∧
    poisonedTable.lookup "False" = some Form.top ∧
    (recheckRecompute stdRules).acceptsNamed poisonedTable topCert "False" = true ∧
    ¬ Pinned officialTable poisonedTable "False"

theorem pinned_False_never_accepted (P : StmtTable) (w : Cert)
    (hPinned : Pinned officialTable P "False") :
    (recheckRecompute stdRules).acceptsNamed P w "False" = false
```

`officialTable` binds `"False"` to `⊥` and `"True"` to `⊤`; `poisonedTable` binds both names to `⊤`. `pinned_False_never_accepted` is the positive half: pinning forces the shipped table `P` to resolve `"False"` to `⊥`, which the faithful checker for the consistent standard rules never accepts.

**K2d** — recomputation of derived fields is necessary.

```lean
theorem trusting_rechecker_accepts_bot_recomputing_rechecker_rejects :
    SemSound stdRules ∧
    (recheckTrust stdRules).accepts (lyingCert .bot) [] .bot = true ∧
    (recheckRecompute stdRules).accepts (lyingCert .bot) [] .bot = false ∧
    (∀ c : Cert, (recheckRecompute stdRules).accepts c [] .bot = false) ∧
    Cert.honest stdRules (lyingCert .bot) = false ∧
    (∀ (c : Cert) (Γ : Ctx) (φ : Form), Cert.honest stdRules c = true →
      (recheckTrust stdRules).accepts c Γ φ = (recheckRecompute stdRules).accepts c Γ φ)
```

`lyingCert φ` applies `botElim` (one premise) while storing `arity = 0`.

* **Plain claims.** See `## Summary`.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1 for all four: each is folklore (an implementation correct for wrong rules is wrong; sound rules do not protect against an implementation defect; agreement of checkers is not evidence by itself; one must compare the checked statement with the intended one; a validator must not trust producer-supplied derived data), made precise as kernel-checked counterexamples. Under the tier criterion above, K1 is T0 because its statement is a published mechanised architecture, while these necessity observations are not mechanised theorems in the literature.
* **Hypothesis ledger.** K2a, K2b, K2d and `unpinned_faithful_checker_for_sound_rules_accepts_renamed_False` (K2c) are closed statements without hypotheses; they *are* the tightness witnesses of K1 and K1-pinned. The positive half of K2c, `pinned_False_never_accepted`, has one hypothesis:

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `hPinned : Pinned officialTable P "False"` | forces the shipped table `P` to resolve `"False"` to its official meaning `⊥`, which the faithful checker for the consistent standard rules never accepts | tight: counterexample `unpinned_faithful_checker_for_sound_rules_accepts_renamed_False` (with `P := poisonedTable`, `w := topCert`) |

* **Depth.** `shallow`: finite evaluations on top of the general theorems about the re-checkers.
* **Non-vacuity witness.** K2a, K2b, K2d and the negative half of K2c exhibit their own witnesses. For `pinned_False_never_accepted` the hypothesis is satisfiable: `ex_pinned_official_pos : Pinned officialTable officialTable "False"`.
* **Non-claims.** (i) Toy logic only; no claim that any real rule set is unsound or any real checker unfaithful. (ii) The four layers are **not exhaustive**: binary, parser, I/O and "the official table is wrong" are not modelled. (iii) The layers are **not logically independent**: K2d is an instance of K2b (the trusting re-checker is an unfaithful checker); its content is the mechanism and the paired positive statement. (iv) `quorum C D` accepts a pair of independent proof objects `(w₁, w₂)`, one per checker; in `separate_artifact_quorum_of_two_unfaithful_checkers_accepts_bot`, the two checkers are given different certificates (`lyingCert .bot` and `bogusHypCert .bot`), each of which the other checker rejects. No single `Cert` is accepted for `[] ⊢ ⊥` by both `recheckTrust stdRules` and `recheckNoHypGuard stdRules` (by `sharedQuorum_recheckTrust_recheckNoHypGuard_faithful`). That theorem therefore does not model two independent checkers accepting the same bogus proof due to a shared defect, nor does it show that disjoint bugs defeat same-artifact N-version checking; the same-artifact cases are `shared_artifact_quorum_of_checkers_with_a_shared_defect_accepts_bot` and S-shared-quorum. (v) Nothing is said about how likely independent implementations are to share a defect. (vi) K2c: the checker accepted a *valid* sequent; no definitional dependencies, notation or elaboration; empty context only. (vii) K2d: one derived field in one toy format; the recomputing re-checker ignores the stored field (recompute-and-ignore) rather than validating it against the recomputed value (validate-and-reject). (viii) K2a's unsound rule is detectable by a truth table; unsoundness arising only from feature interaction is not illustrated.
* **Prior art.** Pollack 1998; Adams 2016; Carneiro 2020 (Metamath Zero); Hurd 2011 (OpenTheory proof articles); Barendregt, Wiedijk 2005; Kumar et al. 2016; Harrison 2006; Carneiro 2026; Candle 2022.
* **Basis: derived (modeling bridge).** Real-world grounding; each item below is a separate modeling claim, not a kernel-checked fact.
  * K2b, same-artifact quorum with a shared defect: repository `leanprover/lean4`, pull request 14807, "fix: make the kernel `is_prop` check require a sort" (merged 2026-08-18T01:37:02Z, merge commit `7412bc4c852c9a9fafa69b67a11e4bf9f5dcbc24`). Its description states: "The bogus proof was also accepted by nanoda, an independent implementation of the Lean kernel. We believe the lean4lean external kernel does not have this bug." Reasoning: one artifact (a bogus proof of `False`) was accepted by two independently written kernels, so a same-artifact quorum of those two kernels would have accepted it; `shared_artifact_quorum_of_checkers_with_a_shared_defect_accepts_bot` is the toy form of exactly this structure (two different checkers, one shared defect, one artifact, `[] ⊢ ⊥` accepted). The bridge concerns only the quorum structure: the toy says nothing about the actual defect (a stuck inferred type treated as "not a proposition"), the statement about lean4lean is the pull request authors' belief and was not examined here, and nothing is inferred about how often independent kernels share defects.
  * K2b: `leanprover/lean4` issue 14484, "Missing check apparently allows proof of False after adversarial metaprogram" (opened 2026-07-22). Toy analogue: the deleted-guard mutant.
  * K2b / S-shared-quorum: `leanprover/lean4` pull request 14806, "fix: make kernel `is_def_eq` caching order-independent" (merged 2026-08-18, merge commit `d108aae3bf7edbaf705b71c01ddb3b264ef72c44`); its description states that both exploits are also caught by nanoda. Toy analogue: a defect not shared by the second checker of a same-artifact quorum; the toy has no caching.
  * K2c: `leanprover/lean4` issue 15908, "Kernel accepts an axiom-free proof of `False`: native `Nat.add` reduction trusts the constant's name, not its definition" (opened 2026-10-24). Toy analogue: a name is taken to carry its official meaning without comparison against the official table. In the real report the unpinned name is consumed *inside* the kernel, so that defect is also a faithfulness defect; the toy separates the two.
  * K2d: `leanprover/lean4` issue 15100, "leanchecker accepts constructor entries whose map key differs from the embedded name" (opened 2026-09-09): the checker built its replay map from parallel producer-supplied arrays without validating the documented invariant relating them. Toy analogue: trusting redundant producer-supplied data. The toy's remedy is to ignore the redundant field; validating agreement between redundant fields is the other remedy and is not modelled.
* **Design question.** As K1; for the quorums, whether re-checking with two independent checkers adds assurance and whether they must re-check the same artifact.

### S-shared-quorum — same-artifact re-checking with disjoint defects

```lean
theorem sharedQuorum_recheckTrust_recheckNoHypGuard_faithful (R : RuleSet) :
    Faithful (sharedQuorum (recheckTrust R) (recheckNoHypGuard R) id) R

theorem shared_artifact_quorum_of_checkers_with_disjoint_defects_is_faithful :
    ¬ Faithful (recheckTrust stdRules) stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (quorum (recheckTrust stdRules) (recheckNoHypGuard stdRules)).AcceptsBot ∧
    Faithful (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) id) stdRules ∧
    (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) id).accepts
        topCert [] Form.top = true
```

Same-artifact quorums under a translation `tr` of proof objects (supporting statements for non-claim (iii)):

```lean
theorem sharedQuorum_faithful_left {C D : Checker} {tr : C.Wit → D.Wit} {R : RuleSet}
    (h : Faithful C R) : Faithful (sharedQuorum C D tr) R

theorem sharedQuorum_faithful_right {C D : Checker} {tr : C.Wit → D.Wit} {R : RuleSet}
    (h : Faithful D R) : Faithful (sharedQuorum C D tr) R

def exploitTranslator : Cert → Cert
  | [.rule [] 8 [φ] 0] => bogusHypCert φ
  | c => c

theorem shared_artifact_quorum_of_disjoint_defects_accepts_bot_under_exploit_translator :
    SemSound stdRules ∧
    ¬ Faithful (recheckTrust stdRules) stdRules ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) exploitTranslator).accepts
        (lyingCert .bot) [] .bot = true ∧
    ¬ Faithful
        (sharedQuorum (recheckTrust stdRules) (recheckNoHypGuard stdRules) exploitTranslator)
        stdRules
```

* **Plain claim.** See `## Summary`.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1 (diverse checkers re-checking one artifact catch defects they do not share: folklore, made precise for one pair of defects).
* **Hypothesis ledger.** None (universally quantified over `R`).
* **Depth.** `shallow`: a certificate accepted by the trusting re-checker passes every hypothesis guard (`hypsOk_of_execCert`), and on such certificates the mutant runs exactly like the recomputing re-checker (`execCertNoHypGuard_eq_of_hypsOk`).
* **Non-vacuity witness.** `shared_artifact_quorum_of_checkers_with_disjoint_defects_is_faithful`: both members unfaithful to the standard rules, their separate-artifact quorum accepts `[] ⊢ ⊥`, and their shared-artifact quorum accepts `topCert` for `[] ⊢ ⊥ → ⊥`.
* **Non-claims.** (i) One pair of defects in one format; it does not show that a shared-artifact quorum catches every pair of disjoint defects (here each member enforces exactly the check the other omits). (ii) Nothing about how likely real independent implementations are to have disjoint defects; K2b exhibits two different checkers that share one. (iii) Same-artifact checking also trusts the translation of proof objects between the two checkers, and any translator or exporter shared by both. `sharedQuorum C D tr` is faithful whenever either member is faithful, for every `tr` (`sharedQuorum_faithful_left`, `sharedQuorum_faithful_right`), but the disjoint-defect theorem is stated for `tr = id` only: with an untrusted translator that shows each member the artifact exploiting its own defect, the same quorum of the same two re-checkers accepts `[] ⊢ ⊥` (`shared_artifact_quorum_of_disjoint_defects_accepts_bot_under_exploit_translator`). A defective translator, exporter or serialiser upstream of both checkers is not covered.
* **Prior art.** Carneiro 2026 (external checkers for Lean); Barendregt, Wiedijk 2005; Wheeler 2009 (diversity, at the compiler level).
* **Design question.** Does re-checking with two independent checkers add assurance, and does it matter whether they re-check the same exported artifact?

---

### K3a — a meta-sound anchor propagates faithfulness around a ring, *assuming* `FaithfulImpliesMetaSound`

```lean
structure VerifierRing (n : Nat) where
  checker     : Fin n → Checker
  MetaCert    : Fin n → Type
  acceptsCert : (i : Fin n) → MetaCert i → Fin n → Bool
```

```lean
def ringNext {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def LinkCertified {n : Nat} (V : VerifierRing n) (i : Fin n) : Prop :=
  ∃ m : V.MetaCert i, V.acceptsCert i m (ringNext i) = true

def RingClosed {n : Nat} (V : VerifierRing n) : Prop :=
  ∀ i : Fin n, LinkCertified V i

def MetaSound {n : Nat} (V : VerifierRing n) (R : RuleSet) (i : Fin n) : Prop :=
  ∀ (m : V.MetaCert i) (j : Fin n), V.acceptsCert i m j = true → Faithful (V.checker j) R

def FaithfulImpliesMetaSound {n : Nat} (V : VerifierRing n) (R : RuleSet) : Prop :=
  ∀ i : Fin n, Faithful (V.checker i) R → MetaSound V R i
```

```lean
theorem ring_all_faithful_of_metaSound_anchor_of_faithfulImpliesMetaSound
    {n : Nat} (V : VerifierRing n) (R : RuleSet)
    (hClosed : RingClosed V)
    (hFaithfulImpliesMetaSound : FaithfulImpliesMetaSound V R)
    (hAnchor : ∃ i₀ : Fin n, MetaSound V R i₀) :
    ∀ j : Fin n, Faithful (V.checker j) R

theorem ring_no_node_accepts_bot_of_metaSound_anchor_of_faithfulImpliesMetaSound_of_consistent
    {n : Nat} (V : VerifierRing n) (R : RuleSet)
    (hClosed : RingClosed V)
    (hFaithfulImpliesMetaSound : FaithfulImpliesMetaSound V R)
    (hAnchor : ∃ i₀ : Fin n, MetaSound V R i₀)
    (hConsistent : Consistent R) :
    ∀ (j : Fin n) (w : (V.checker j).Wit), (V.checker j).accepts w [] .bot = false

theorem ring_metaSound_of_all_faithful {n : Nat} (V : VerifierRing n) (R : RuleSet)
    (hAll : ∀ j, Faithful (V.checker j) R) :
    (∀ i, MetaSound V R i) ∧ FaithfulImpliesMetaSound V R
```

* **Plain claim.** See `## Summary`.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1. Trust propagation from a trusted base along verified links is folklore (compare the tower of checkers in Milawa). The ring form with the meta-soundness assumption named was not found in the literature; no novelty is claimed.
* **Hypothesis ledger.**

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `RingClosed V` | propagation passes only through certified links | tight: counterexample `ring_with_uncertified_link_does_not_propagate` |
  | `FaithfulImpliesMetaSound V R` | **carries the substance**: converts faithfulness of a node's object-level checker into soundness of its certificate checking. Not derivable from `VerifierRing`. Not needed for `n = 1` | tight: counterexample `metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound` |
  | `∃ i₀, MetaSound V R i₀` | a ring has no base case of its own; unsatisfiable for `n = 0` | tight: counterexample `three_unfaithful_checkers_close_faithfulness_ring` (K3b) |
  | `Consistent R` (`⊥` corollary only) | faithfulness ⇒ rejection of `[] ⊢ ⊥`; strictly weaker than `SemSound R` | tight: counterexample `ring_of_faithful_checkers_over_unsound_rules_accepts_bot` (K3c). Its last conjunct is `¬ SemSound badRules`; that `Consistent badRules` itself fails follows from its `Faithful` and `AcceptsBot` conjuncts (an accepted proof object for `[] ⊢ ⊥` is, by faithfulness, a derivation of `[] ⊢ ⊥`) and is stated directly by `ex_semSound_badRules_neg` |

  What `FaithfulImpliesMetaSound` packages: `faithfulImpliesMetaSound_of_selfHosted_of_claimReflection` shows it follows when (a) each node checks certificates with its *own* kernel on an encoded claim (`selfHostedRing`) and (b) the rule table derives an encoded faithfulness claim only if the claim is true (`ClaimReflection`). Condition (b) is a reflection property of the logic in which faithfulness is stated; the toy logic cannot state faithfulness, so (b) is never established from first principles here. An inconsistent self-hosting table cannot satisfy (b) once any member is unfaithful (`not_claimReflection_badRules_of_unfaithful`).

  Converse: for `n ≥ 1`, if every member is faithful then every node is meta-sound and `FaithfulImpliesMetaSound` holds, whatever the certificate checkers do (`ring_metaSound_of_all_faithful`). So under `RingClosed` the two assumptions together are exactly as strong as the conclusion: the theorem transports faithfulness, it does not create it.
* **Depth.** `shallow`: induction around the ring. The substance is in the named assumption.
* **Non-vacuity witness.** `k3a_nonvacuous`: `faithfulRing stdRules` (the recomputing certificate re-checker, the trace checker, their separate-artifact quorum) is closed, satisfies `FaithfulImpliesMetaSound`, has a meta-sound node, and the rules are sound and consistent. Its certificate checkers accept every claim; they are meta-sound only because every member is faithful.
* **Non-claims.** (i) Not "rings are useless"; this is what a ring buys under the named assumption. (ii) Not "rings are sufficient": the conclusion is faithfulness only and says nothing about the rules (K3c). (iii) `MetaSound V R i` quantifies only over the fixed nodes `j : Fin n` of the ring `V`, not over arbitrary candidate checkers. Whenever every node of `V` is already faithful to `R` (as in `k3a_nonvacuous` and K3c), `MetaSound` and `FaithfulImpliesMetaSound` hold vacuously even for a rubber-stamp certificate checker or a self-hosted inconsistent rule table such as `badRules`; K3c therefore does not show that an inconsistent logic can serve as a non-trivially meta-sound self-hosted verifier. (iv) The discriminating power of `MetaSound` (rejecting a false claim) cannot be exhibited inside any ring satisfying all of K3a's hypotheses with `n ≥ 1`, since every member is then faithful; it is exhibited by node 0 of `rubberStampRing` (`ex_metaSound_pos`). (v) `VerifierRing` fixes a single shared rule table `R` for every node in the ring. K3a models multiple checkers implementing the same specification `R`, not a heterogeneous ring of proof assistants implementing distinct logics (such as Lean, Rocq, and HOL Light certifying each other's faithfulness to separate specifications). (vi) Closing a cycle adds no assurance over a directed chain when a known anchor is already faithful and meta-sound; the cycle is used only because the anchor is existential (unknown index `i₀`) and assumed `MetaSound` rather than already `Faithful`. In `ring_with_uncertified_link_does_not_propagate`, with node 1 as the anchor, the missing link is exactly the one back into the anchor, and the anchor's own object-level checker is the unfaithful one. (vii) The anchor must be meta-sound for a reason external to the ring; without one a closed ring establishes nothing (K3b). (viii) Toy model; nothing about binaries.
* **Prior art.** Davis, Myreen 2015 (Milawa); Abrahamsson et al. 2022 (Candle); Carneiro 2026 (Lean4Lean); Sozeau et al. 2020.
* **Basis: derived (modeling bridge).** Real-world grounding: Milawa's tower of checkers is a directed chain rooted at a base verified in an external system; in this card's terms it has a known anchor and needs no cycle.
* **Design question.** Does having checkers certify each other in a cycle, or a checker certify itself, add assurance, and under what explicit assumption?

### K3b — three unfaithful checkers close a ring

```lean
theorem three_unfaithful_checkers_close_faithfulness_ring :
    SemSound stdRules ∧
    RingClosed buggyRing ∧
    FaithfulImpliesMetaSound buggyRing stdRules ∧
    (∀ i, ¬ MetaSound buggyRing stdRules i) ∧
    (∀ i, ¬ Faithful (buggyRing.checker i) stdRules) ∧
    (∀ i, (buggyRing.checker i).AcceptsBot)

theorem unfaithful_checker_certifies_its_own_faithfulness :
    RingClosed (selfHostedRing (fun _ : Fin 1 => recheckTrust stdRules) (fun _ => Form.var 0)) ∧
    ¬ Faithful (recheckTrust stdRules) stdRules ∧
    (recheckTrust stdRules).AcceptsBot
```

`buggyRing` is self-hosted: node 0 accepts everything, node 1 is `recheckTrust stdRules`, node 2 is `recheckNoHypGuard stdRules`; the claim "node j is faithful" is encoded as the atom `p_j`, which the sound standard rules cannot derive, and each node's own broken kernel "proves" its successor's claim.

* **Plain claims.** See `## Summary`.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1 (a cycle of mutual certification has no base case). **Depth.** `shallow`.
* **Hypothesis ledger.** None (closed statements). **Non-vacuity witness.** Not applicable: the statements exhibit their witnesses.
* **Non-claims.** The checkers are deliberately broken; the statement is "a closed ring is possible without any faithful node", not "closed rings of real checkers are probably broken". Not "self-verification is worthless": a self-certificate is not evidence *by itself*.
* **Prior art.** Davis, Myreen 2015; Harrison 2006.
* **Design question.** Can mutually certifying or self-certifying checkers establish faithfulness of their implementations, or consistency / soundness of their logics, and under exactly which assumptions?

### K3c — a ring of faithful checkers over unsound rules

```lean
theorem ring_of_faithful_checkers_over_unsound_rules_accepts_bot :
    RingClosed (faithfulRing badRules) ∧
    (∀ i, MetaSound (faithfulRing badRules) badRules i) ∧
    FaithfulImpliesMetaSound (faithfulRing badRules) badRules ∧
    (∀ i, Faithful ((faithfulRing badRules).checker i) badRules) ∧
    (∀ i, ((faithfulRing badRules).checker i).AcceptsBot) ∧
    ¬ SemSound badRules
```

* **Plain claim.** See `## Summary`. Every hypothesis and the conclusion of K3a's faithfulness theorem (`ring_all_faithful_of_metaSound_anchor_of_faithfulImpliesMetaSound`) hold in this ring; the hypothesis `Consistent badRules` of K3a's `⊥` corollary fails. The statement records `¬ SemSound badRules`; `¬ Consistent badRules` follows from its `Faithful` and `AcceptsBot` conjuncts (an accepted proof object for `[] ⊢ ⊥` is, by faithfulness, a derivation of `[] ⊢ ⊥`) and is stated directly by `ex_semSound_badRules_neg`.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1. **Depth.** `shallow`.
* **Hypothesis ledger.** None (closed statement). **Non-vacuity witness.** Not applicable: the statement exhibits its witnesses.
* **Non-claims.** Not "faithfulness proofs are pointless" (with sound rules the same ring rejects `[] ⊢ ⊥`). The three checkers share the rule table by construction: the example is about a defect in the shared specification, not about correlated implementation defects. Because `badRules` derives every formula, the self-hosted certificate checkers here accept every claim, and `MetaSound` holds only because every member is faithful (non-claim (iii) of K3a).
* **Prior art.** Kumar et al. 2016; Harrison 2006.
* **Basis: derived (modeling bridge).** Real-world grounding: the realistic reading is a sound *external* meta-logic verifying that several checkers faithfully implement an unsound object specification; all of them then accept the same invalid statements.
* **Design question.** As K3b.

---

### K4a / K4a-local — no ring of consistency proofs under the named conditions

```lean
structure ProvFamily (ι : Type) where
  Sent : Type
  bot  : Sent
  imp  : Sent → Sent → Sent
  box  : ι → Sent → Sent          -- box j A : "theory j proves A"
  Thm  : ι → Sent → Prop          -- Thm i A : theory i proves A

-- The definitions below, and those in the next block, are declared inside
-- `namespace ProvFamily` with `variable {ι : Type} (F : ProvFamily ι)`.
def con (j : ι) : F.Sent := F.imp (F.box j F.bot) F.bot

def GodelII (i : ι) : Prop := F.Thm i (F.con i) → F.Thm i F.bot
```

```lean
def MpClosed (i : ι) : Prop :=
  ∀ {A B : F.Sent}, F.Thm i (F.imp A B) → F.Thm i A → F.Thm i B

structure ImpClosed (i : ι) : Prop where
  mp  : F.MpClosed i
  axK : ∀ A B : F.Sent, F.Thm i (F.imp A (F.imp B A))
  axS : ∀ A B C : F.Sent,
    F.Thm i (F.imp (F.imp A (F.imp B C)) (F.imp (F.imp A B) (F.imp A C)))

structure CrossHBL : Prop where
  nec     : ∀ i j : ι, F.CrossNec i j
  distrib : ∀ i j : ι, F.CrossDistrib i j
  sigma1  : ∀ i j k : ι, F.CrossSigma1 i j k

structure CrossHBLFrom (i : ι) : Prop where
  nec     : ∀ j : ι, j ≠ i → F.CrossNec i j
  distrib : ∀ j : ι, j ≠ i → F.CrossDistrib i j
  sigma1  : ∀ j k : ι, j ≠ i → F.CrossSigma1 i j k
```

```lean
theorem consistencyRing_anchor_inconsistent_of_impClosed_godelII_crossHBLFrom
    {n : Nat} (F : ProvFamily (Fin n)) (i₀ : Fin n)
    (hImpClosed : F.ImpClosed i₀)
    (hGodelII : F.GodelII i₀)
    (hFrom : F.CrossHBLFrom i₀)
    (hRing : ∀ i, F.Thm i (F.con (ringNext i))) :
    F.Thm i₀ F.bot

theorem inconsistent_of_proves_con_of_inconsistent {ι : Type} (F : ProvFamily ι) {j k : ι}
    (hMp : F.MpClosed j) (hNec : F.CrossNec j k) (hCon : F.Thm j (F.con k))
    (hk : F.Thm k F.bot) : F.Thm j F.bot

theorem consistencyRing_all_inconsistent_of_impClosed_godelIIAnchor_crossHBL
    {n : Nat} (F : ProvFamily (Fin n))
    (hImpClosed : ∀ i, F.ImpClosed i)
    (hGodelII : ∃ i₀ : Fin n, F.GodelII i₀)
    (hBridge : F.CrossHBL)
    (hRing : ∀ i, F.Thm i (F.con (ringNext i))) :
    ∀ i, F.Thm i F.bot
```

**Exactly which conditions are assumed** (writing `i ⊢ A` for `F.Thm i A`, `□ⱼ` for `F.box j`):

| Name | Statement | Diagonal case | K4a assumes | K4a-local assumes |
|:--|:--|:--|:--|:--|
| `ImpClosed i` | modus ponens; `i ⊢ A → (B → A)`; `i ⊢ (A → (B → C)) → ((A → B) → (A → C))` | | every `i` | anchor only |
| `HasEfq i` | `i ⊢ ⊥ → A` | | not assumed | not assumed |
| `GodelII i` | if `i ⊢ □ᵢ⊥ → ⊥` then `i ⊢ ⊥` | | some `i₀` | the anchor |
| `CrossNec i j` | if `j ⊢ A` then `i ⊢ □ⱼA` | `D1` | all `i, j` | `i = i₀`, all `j ≠ i₀` |
| `CrossDistrib i j` | `i ⊢ □ⱼ(A → B) → (□ⱼA → □ⱼB)` | `D2` | all `i, j` | `i = i₀`, all `j ≠ i₀` |
| `CrossSigma1 i j k` | `i ⊢ □ₖA → □ⱼ□ₖA` | `D3` | all `i, j, k` | `i = i₀`, all `j ≠ i₀`, all `k` |
| ring | `i ⊢ □ᵢ₊₁⊥ → ⊥` for every `i` (indices mod `n`) | | yes | yes |

`CrossHBL` is the conjunction of `CrossNec`, `CrossDistrib`, `CrossSigma1` over all index combinations; its diagonal is exactly the Hilbert–Bernays–Löb conditions `D1`–`D3` of each theory (`CrossHBL.hbl`). `CrossHBLFrom i₀` is the off-diagonal part from `i₀`. Neither statement uses any theory's own `D1`–`D3`. **Not assumed:** any diagonal (fixed-point) lemma, Löb's rule beyond the `⊥` instance, ex falso, soundness or ω-consistency of any theory, inclusion between theories, or any link between `Thm` and truth.

* **Plain claims.** See `## Summary`. K4a is derived from K4a-local plus backward propagation of inconsistency along the ring links (`inconsistent_of_proves_con_of_inconsistent`). For `n = 1`, K4a-local is Gödel II itself (the ring hypothesis is `i₀ ⊢ con i₀`) and needs neither `ImpClosed` nor `CrossHBLFrom`; for `n = 0` the K4a anchor hypothesis is unsatisfiable.
* **Basis: derived (modeling bridge).** Applicability to concrete theories: the theorems are about abstract structures. They apply to concrete formal systems **only insofar as** those systems, with a concrete choice of provability predicates and a common sentence language, satisfy every condition in the table. For standard arithmetised provability predicates of sufficiently strong recursively axiomatised theories, textbooks establish `D1`–`D3` and Löb's theorem (Boolos 1993; Smoryński 1985), and the cross-theory conditions are the two-theory versions of the same facts (the informal two-theory argument in Mummert 2013 uses them); Kurahashi 2020 classifies which derivability conditions suffice for which forms of Gödel II. None of that is verified in this package. Theories with non-standard provability predicates, or too weak for the conditions, are outside its scope (Feferman 1960; Willard 2001).
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1 for both. Gödel II and Löb are T0. The two-theory case is folklore, written out informally by Mummert (2013); the `n`-cycle is the same argument iterated (irreflexivity plus transitivity of "proves the consistency statement of", compare Mathematics Stack Exchange question 2208419). Polymodal provability logics for several theories (Carlson 1986; Smoryński 1985; Beklemishev 1996; Japaridze, de Jongh 1998) are the classical setting for such arguments; whether the two-theory case is literally a theorem of a specific bimodal logic in those works was not checked against their axiomatisations, so no such claim is made. Mechanised accounts of Gödel II exist (Paulson 2015; Popescu, Traytel 2019 and 2021; Saitou, Noguchi 2026, in Lean 4; first-incompleteness mechanisations: Shankar 1994, O'Connor 2005, Kirst, Hermes 2023); none was found to state the ring form with separately named cross-theory conditions. No novelty is claimed. Search record: the works just listed; Pakhomov, Walsh 2021; Hamkins 2022; Lindström 2017; Mathematics Stack Exchange questions 563641 and 2208419; web searches for "theories proving each other's consistency", "mutual consistency proofs", "consistency strength cycle".
* **Hypothesis ledger, K4a.**

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `∀ i, ImpClosed i` | chaining implications; modus ponens at every theory, K and S at the anchor | tight: counterexamples `consistencyRing_consistent_without_mp`, `consistencyRing_consistent_without_axK_axS` |
  | `∃ i₀, GodelII i₀` | **carries the substance** of Gödel II, at one node only; for concrete theories it follows from Löb's theorem (`LobRule.godelII`) | tight: counterexample `consistencyRing_consistent_without_godelII` |
  | `hBridge.nec` | theory `i` verifies actual proofs of theory `j` | tight: counterexamples `consistencyRing_consistent_without_crossNec`, `one_unverified_ring_link_leaves_anchor_inconsistent` |
  | `hBridge.distrib` | theory `i` proves theory `j` closed under modus ponens | tight: counterexample `consistencyRing_consistent_without_crossDistrib` |
  | `hBridge.sigma1` | theory `i` proves that theory `j` verifies proofs of theory `k` | tight: counterexamples `consistencyRing_consistent_without_crossSigma1` (K4b), `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency` |
  | ring | the cycle itself | tight: counterexample `consistency_proof_along_open_chain_is_consistent` |

* **Hypothesis ledger, K4a-local.** `ImpClosed i₀`: tight (`consistencyRing_consistent_without_mp`, `consistencyRing_consistent_without_axK_axS`); `GodelII i₀`: tight (`consistencyRing_consistent_without_godelII`); `CrossHBLFrom i₀` — `nec` tight (`consistencyRing_consistent_without_crossNec`), `distrib` tight (`consistencyRing_consistent_without_crossDistrib`), `sigma1` tight (`consistencyRing_consistent_without_crossSigma1`, `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency`); ring: tight (`consistency_proof_along_open_chain_is_consistent`). Each witness states its conditions for *every* theory, so it applies at every choice of anchor.

  Each tightness witness is a family in which **every other hypothesis holds and every theory is consistent**; in each, the broken condition fails at every node (except `one_unverified_ring_link_leaves_anchor_inconsistent`, which breaks a single ring link and keeps the anchor inconsistent).
* **Depth.** `shallow` for both. K4a-local: the anchor shows that "proves the consistency statement of" is transitive along the ring (three lines per step), reaches its own consistency statement, and applies `GodelII`. The substance of Gödel's theorem is inside the assumed `GodelII`.
* **Non-vacuity witnesses.** `k4a_nonvacuous` (all hypotheses of K4a in `trivialFamily (Fin n)`, `n ≥ 1`), `k4a_local_nonvacuous` (same for K4a-local at every node). Necessarily inconsistent families; the tightness witnesses are consistent families satisfying all hypotheses but one. For K4a-local there is also a non-degenerate instance: in `oneBrokenNecFamily` (two theories) theory 0 satisfies every hypothesis of K4a-local while theory 1 of the same ring is consistent (`k4a_local_hypotheses_hold_in_mixed_ring`).
* **Positive controls (nearby settings where the conclusion fails).** `consistency_proof_along_open_chain_is_consistent` (ω-chain model: every structural hypothesis holds, theory 0 proves theory 1's consistency, both consistent, no theory proves any `□ⱼ⊥` or `□ⱼ□ₖ⊥`: only *closing the cycle* is excluded); `two_consistent_theories_prove_each_others_consistency_without_crossSigma1` (K4b); `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency`; `one_unverified_ring_link_leaves_anchor_inconsistent` (two theories with one unverified ring link, `¬ CrossNec 1 0`). For K4a it is a positive control because theory 1, the theory before the broken link, is consistent, so K4a's conclusion "every theory proves `⊥`" fails. For K4a-local it is a positive control **at theory 1**: there every hypothesis of K4a-local holds except `CrossHBLFrom 1` (its `nec` part fails, because `CrossNec 1 0` fails), and the conclusion fails (`Consistent 1`). Theory 0 of the same family, the "anchor" of the theorem's name, is not a control: it satisfies every hypothesis of K4a-local and proves `⊥`, as K4a-local requires, and is the mixed-ring non-vacuity witness above (`k4a_local_hypotheses_hold_in_mixed_ring`).
* **Non-claims.** (i) About abstract `ProvFamily` structures only (see the applicability paragraph). (ii) Dropping Löb's rule or Gödel's second incompleteness property (or `CrossSigma1`, `CrossNec`, `CrossDistrib`) at a single node or in a single direction does not escape K4a: as soon as even one node `i₀` satisfies the Gödel-II instance (`Thm i₀ (con i₀) → Thm i₀ bot`), implicational closure, and the cross-theory conditions from `i₀` to the other theories, `i₀` proves `⊥` (K4a-local), and `CrossNec` on the ring links together with the ring hypothesis and modus ponens forces every other node to prove `⊥` as well. For every theory of the ring to be consistent, every theory must fail at least one of its own anchor conditions (`ImpClosed`, `GodelII`, `CrossHBLFrom`); breaking a single ring link `CrossNec i (ringNext i)` only shields theory `i` from inheriting an anchor's inconsistency. In K4b's two-theory countermodel `starFamily 2`, both `CrossSigma1 0 1 0` and `CrossSigma1 1 0 1` fail. (iii) K4a excludes cycles of categorical consistency proofs (`Thm i (con (ringNext i))`); it does not exclude mutual relative consistency proofs or equiconsistency (`Thm i (con i → con j)` and `Thm j (con j → con i)`), nor mutual interpretability between consistent theories of equal consistency strength (such as ZF and ZFC, or PA and ACA₀). (iv) `ProvFamily` assumes all `n` theories share a single sentence type `Sent` with common `bot`, `imp`, and provability boxes. Applying K4a to distinct concrete formal systems (such as Lean and Rocq) additionally requires translating provability statements into a common syntactic fragment (such as arithmetic) so that the bridge conditions hold across those translations. (v) Like K4b's `starFamily`, the abstract models `leafFamily` and `possibilityFamily`, and theory 1 of `oneBrokenNecFamily`, contain consistent theories that prove their own inconsistency statement `□ᵢ⊥` (and in `leafFamily` and `possibilityFamily` every theory proves every `□ⱼ□ₖ⊥`, so `CrossSigma1` holds there vacuously): `finite_countermodels_prove_own_inconsistency`. They establish logical independence of K4a's conditions, not the existence of Σ₁-sound theories exhibiting those behaviours. `omegaChainFamily` and `omegaStarFamily` contain no theory proving its own inconsistency statement. (vi) Does **not** say one theory cannot prove another's consistency (open chain). (vii) Does not exclude infinite descending sequences of theories each proving the next one's consistency (Pakhomov, Walsh 2021, abstract: "it is possible to construct descending chains of artificial theories with respect to consistency strength"). (viii) `GodelII` is a hypothesis; the package proves Gödel's second theorem or Löb's theorem for no theory. (ix) Not a statement about proof checkers or kernels: reading it as "two type theories cannot prove each other consistent" requires verifying every named condition, and a common sentence language, for those theories. (x) About consistency statements `□ⱼ⊥ → ⊥` only; it does not address relativised soundness results (soundness assuming a stronger principle), which is how real self-hosted soundness proofs are stated. (xi) K4a-local's conclusion concerns the anchor only, and its freedom from `D1`–`D3` does not suggest that dropping `D1`–`D3` is a realistic escape for concrete theories.
* **Prior art.** Gödel 1931; Hilbert, Bernays 1939; Löb 1955; Feferman 1960; Kreisel, Lévy 1968; Boolos 1993; Smoryński 1985; Carlson 1986; Beklemishev 1996; Japaridze, de Jongh 1998; Willard 2001; Kurahashi 2020; Mummert 2013; Mathematics Stack Exchange 2208419; Pakhomov, Walsh 2021; Hamkins 2022; Lindström 2017; Paulson 2015; Popescu, Traytel 2019, 2021; Saitou, Noguchi 2026; Shankar 1994; O'Connor 2005; Kirst, Hermes 2023.
* **Design question.** Can mutually certifying or self-certifying systems establish consistency or soundness of their *logics*, rather than faithfulness of their implementations?

### K4b — consistent theories proving each other's consistency once `CrossSigma1` is dropped

```lean
theorem two_consistent_theories_prove_each_others_consistency_without_crossSigma1 :
    (starFamily 2).Consistent 0 ∧
    (starFamily 2).Consistent 1 ∧
    (starFamily 2).Thm 0 ((starFamily 2).con 1) ∧
    (starFamily 2).Thm 1 ((starFamily 2).con 0) ∧
    (∀ i, (starFamily 2).ImpClosed i) ∧
    (∀ i, (starFamily 2).HBL i) ∧
    (∀ i, (starFamily 2).LobRule i) ∧
    (∀ i j, (starFamily 2).CrossNec i j) ∧
    (∀ i j, (starFamily 2).CrossDistrib i j) ∧
    ¬ (starFamily 2).CrossSigma1 0 1 0 ∧
    ¬ (starFamily 2).CrossSigma1 1 0 1

theorem consistencyRing_consistent_without_crossSigma1 (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (starFamily n).ImpClosed i) ∧
    (∀ i, (starFamily n).HBL i) ∧
    (∀ i, (starFamily n).LobRule i) ∧
    (∀ i, (starFamily n).GodelII i) ∧
    (∀ i j, (starFamily n).CrossNec i j) ∧
    (∀ i j, (starFamily n).CrossDistrib i j) ∧
    (∀ i, (starFamily n).Thm i ((starFamily n).con (ringNext i))) ∧
    (∀ i, (starFamily n).Consistent i) ∧
    ¬ (∀ i, (starFamily n).Thm i (starFamily n).bot) ∧
    (∀ i, ¬ (starFamily n).CrossSigma1 i (ringNext i) i)

theorem consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency
    (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (omegaStarFamily n).ImpClosed i) ∧
    (∀ i, (omegaStarFamily n).HBL i) ∧
    (∀ i, (omegaStarFamily n).LobRule i) ∧
    (∀ i, (omegaStarFamily n).GodelII i) ∧
    (∀ i j, (omegaStarFamily n).CrossNec i j) ∧
    (∀ i j, (omegaStarFamily n).CrossDistrib i j) ∧
    (∀ i, (omegaStarFamily n).Thm i ((omegaStarFamily n).con (ringNext i))) ∧
    (∀ i, (omegaStarFamily n).Consistent i) ∧
    ¬ (∀ i, (omegaStarFamily n).Thm i (omegaStarFamily n).bot) ∧
    (∀ i, ¬ (omegaStarFamily n).Thm i ((omegaStarFamily n).box i (omegaStarFamily n).bot)) ∧
    (∀ i, ¬ (omegaStarFamily n).CrossSigma1 i (ringNext i) i)

theorem starFamily_proves_own_inconsistency (n : Nat) (i : Fin n) :
    (starFamily n).Thm i ((starFamily n).box i (starFamily n).bot)
```

`starFamily n` is read off the Kripke model with a base world and one "tip" world per theory, where relation `i` relates every world other than tip `i` to tip `i`; "theory `i` proves `A`" means `□ᵢA` holds at the base. For `n = 2` this is the three-world frame `{w, a, b}` with `R₀ = {(w,a),(b,a)}`, `R₁ = {(w,b),(a,b)}`. `omegaStarFamily n` replaces each tip by an ω-chain of worlds, so that no theory proves `□ᵢ⊥`.

* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T1. A routine polymodal Kripke countermodel; polymodal provability logics and their Kripke semantics are classical (Carlson 1986; Beklemishev 1996; Smoryński 1985; Japaridze, de Jongh 1998). No source stating this countermodel was found; no novelty is claimed.
* **Depth.** `shallow`.
* **Hypothesis ledger.** `two_consistent_theories_prove_each_others_consistency_without_crossSigma1` is a closed statement and `starFamily_proves_own_inconsistency` has no hypothesis. The two general-`n` statements have one:

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `hn : 2 ≤ n` (`consistencyRing_consistent_without_crossSigma1`, `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency`) | a ring of consistency proofs between distinct theories needs two theories: for `n = 1` the ring successor of theory 0 is theory 0 itself, and neither `starFamily 1` nor `omegaStarFamily 1` proves its own consistency statement, so the ring conjunct fails; for `n = 0` there is no theory, so the conjunct `¬ ∀ i, Thm i ⊥` fails | tight: counterexample `consistencyRing_consistent_without_crossSigma1_fails_below_two` |

* **Non-vacuity witness.** Not applicable: the statements exhibit their witnesses (`hn` holds, for example, for `n = 2`).
* **Non-claims.** (i) Does **not** exhibit real formal systems that consistently prove each other's consistency; the theories are artefacts of Kripke models and their boxes are not arithmetised provability predicates. (ii) In `starFamily` each theory, although consistent, proves its own inconsistency statement `□ᵢ⊥`; `omegaStarFamily` removes that defect, and no theory of `omegaStarFamily n` proves any `□ⱼ□ₖ⊥` (`omegaStarFamily_not_proves_nested_box_bot`). (iii) Standard provability predicates in theories strong enough to formalize Σ₁-completeness (such as extensions of `IΣ₁`) satisfy `CrossSigma1`, whereas sufficiently weak theories (such as Robinson's `Q`) or non-standard provability predicates can fail it; K4b's abstract Kripke model shows logical necessity of `CrossSigma1` in `ProvFamily`, not how concrete theories fail it. (iv) Breaking `CrossSigma1` in one direction only would not suffice (K4a-local). (v) Shows necessity of one condition at a time.
* **Prior art.** Carlson 1986; Beklemishev 1996; Smoryński 1985; Boolos 1993; Solovay 1976; Feferman 1960; Kurahashi 2020; Japaridze, de Jongh 1998.
* **Design question.** As K3b.

---

### K5 / K5-iff — an inconsistent theory proves every local reflection schema, its own included

```lean
theorem inconsistent_proves_every_local_reflection_of_mp_efq {ι : Type} (F : ProvFamily ι)
    (i : ι) (hMp : F.MpClosed i) (hEfq : F.HasEfq i) (hInconsistent : F.Thm i F.bot) :
    ∀ (j : ι) (A : F.Sent), F.Thm i (F.imp (F.box j A) A)

theorem inconsistent_proves_every_con_of_mp_efq {ι : Type} (F : ProvFamily ι) (i : ι)
    (hMp : F.MpClosed i) (hEfq : F.HasEfq i) (hInconsistent : F.Thm i F.bot) :
    ∀ j : ι, F.Thm i (F.con j)

theorem proves_own_local_reflection_iff_inconsistent_of_mp_efq_godelII
    {ι : Type} (F : ProvFamily ι) (i : ι)
    (hMp : F.MpClosed i) (hEfq : F.HasEfq i) (hGodelII : F.GodelII i) :
    (∀ A : F.Sent, F.Thm i (F.imp (F.box i A) A)) ↔ F.Thm i F.bot
```

`□ⱼA → A` (for all `A`) is the *local reflection schema* for theory `j` (Kreisel, Lévy 1968).

* **Plain claims.** See `## Summary`. So an unconditional self-soundness theorem is not evidence of soundness: an inconsistent system has one, and a consistent system with Gödel's second incompleteness property cannot have one.
* **Basis.** execution (Lean kernel check), for every Lean statement of this card.
* **Tier.** T0 (ex falso inside the theory; the equivalence is the standard consequence of Löb's theorem).
* **Hypothesis ledger.**

  | Hypothesis | Why it is there | Tightness |
  |:--|:--|:--|
  | `MpClosed i` (K5, K5-iff) | combines the ex falso instance with `⊥` | tight: counterexamples `local_reflection_fails_without_mp` (reflection form, K5-iff), `con_fails_without_mp` (consistency form) |
  | `HasEfq i` (K5, K5-iff) | supplies `⊥ → (□ⱼA → A)`; for the consistency form it can be replaced by the axiom scheme K | tight: counterexamples `local_reflection_fails_without_efq` (reflection form, K5-iff; its theory has K, so it still proves every consistency statement), `con_fails_without_efq` (consistency form; a theory with neither ex falso nor K) |
  | `Thm i bot` (K5) | the theory is inconsistent | tight: counterexample `local_reflection_fails_without_inconsistency` |
  | `GodelII i` (K5-iff) | gives "proves own reflection ⇒ inconsistent" | tight: counterexample `local_reflection_iff_fails_without_godelII` |

* **Depth.** `shallow` (one application of modus ponens to an ex falso instance; the equivalence adds one use of `GodelII`).
* **Non-vacuity witnesses.** `k5_nonvacuous` (`trivialFamily`); `k5_iff_nonvacuous` (`trivialFamily`: both sides true) and `k5_iff_nonvacuous_consistent` (theory 0 of `omegaChainFamily`: consistent, both sides false).
* **Non-claims.** (i) Abstract structures only. (ii) The implication from inconsistency (`Thm i bot`) to every local reflection schema (`□ⱼA → A`) depends essentially on ex falso quodlibet (`HasEfq`) and does not apply to paraconsistent or minimal-logic theories; deriving `con j := □ⱼ⊥ → ⊥` from `Thm i bot` requires only modus ponens and either ex falso or the axiom scheme K. (iii) Proving implementation faithfulness (that a checker accepts only derivations of a specification `R`) inside a system implementing `R` is not a proof of the local reflection schema `□A → A` or of `Con(R)`, and is not forbidden by K5 or Löb's rule. (iv) K5 alone does **not** say that a system proving its own soundness is inconsistent; that needs `GodelII` (K5-iff). (v) Nothing is said about uniform reflection, typed soundness theorems, or soundness proofs carried out in a stronger metatheory. (vi) Not "verified or self-verified kernels are worthless": relativised results are untouched.
* **Prior art.** Löb 1955; Kreisel, Lévy 1968; Feferman 1962; Boolos 1993; Smoryński 1985; Beklemishev 2005; Feferman 1960; Willard 2001.
* **Basis: derived (modeling bridge).** Real-world grounding: self-hosted correctness developments such as Lean4Lean and MetaRocq prove faithfulness of an implementation to a specification, which K5 does not concern (non-claim (iii)).
* **Design question.** As K4a.

---

### Supporting results and reference points

```lean
theorem stdRules_semSound : SemSound stdRules

theorem stdRules_consistent : Consistent stdRules

theorem recheckRecompute_faithful (R : RuleSet) : Faithful (recheckRecompute R) R

theorem recheck_complete (pol : FieldPolicy) (R : RuleSet) : Complete (recheck pol R) R

theorem execCert_trust_eq_recompute_of_honest {R : RuleSet} {c : Cert}
    (hc : Cert.honest R c = true) :
    ∀ stk : Stack, execCert .trust R stk c = execCert .recompute R stk c

theorem traceChecker_faithful (R : RuleSet) : Faithful (traceChecker R) R

structure NaivePropProv where
  Prov : Prop → Prop
  nec  : ∀ {P : Prop}, P → Prov P
  lob  : ∀ {P : Prop}, Prov (Prov P → P) → Prov P

theorem NaivePropProv.not_not_prov_false (T : NaivePropProv) : ¬ ¬ T.Prov False
```

Unfolded: `Consistent R := ¬ Derivable R [] .bot`.

| Id | Lean | Plain claim | Tier | Depth | Non-vacuity |
|:--|:--|:--|:--|:--|:--|
| S-semSound | `stdRules_semSound`, `stdRules_consistent` | every sequent derivable from the standard table is truth-table valid; `[] ⊢ ⊥` is not derivable | T0 (textbook soundness of natural deduction: van Dalen 2013; Troelstra, Schwichtenberg 2000) | substantive (induction over derivations) | unconditional (`ex_semSound_stdRules_pos`) |
| S-recompute | `recheckRecompute_faithful`, `recheck_complete`, `execCert_trust_eq_recompute_of_honest`, `traceChecker_faithful` | for every rule table the recomputing re-checker and the trace checker are faithful; both certificate re-checkers are complete; on honest certificates the two policies execute identically | T0 (stack-machine proof formats: Hurd 2011; Carneiro 2020) | substantive (inductions over certificates and derivations) | `ex_faithful_recheckRecompute_pos`, `ex_traceChecker_accepts_topTrace_pos`, `ex_honest_topCert_pos` |
| S-naive-interface | `NaivePropProv.not_not_prov_false` | a provability operator on meta-level propositions with "true implies provable" (`nec`) and Löb's rule (`lob`) is never consistent (only these two fields exist and both are used), so an impossibility theorem over that interface is vacuous | T1 (interface-design note) | shallow | `NaivePropProv.nonempty` |

Basis for the three rows: execution (Lean kernel check).

**Hypothesis ledger, S-recompute.** `recheckRecompute_faithful`, `recheck_complete` and `traceChecker_faithful` hold for every rule table and have no hypotheses. `execCert_trust_eq_recompute_of_honest` has one:

| Hypothesis | Why it is there | Tightness |
|:--|:--|:--|
| `hc : Cert.honest R c = true` | on honest certificates the stored `arity` fields equal the table's arities, so both policies pop the same premises; on the dishonest `lyingCert ⊥` they diverge (the mechanism of K2d) | tight: counterexample `execCert_trust_eq_recompute_fails_without_honest` |

S-semSound and S-naive-interface have no hypotheses.

**Non-claims, prior art and design questions of the supporting results.**

* **S-semSound.** Non-claims: (i) toy propositional logic only: no binders, dependent types, definitional equality, universes or inductive types; nothing here is a theorem about Lean, Rocq, HOL Light, Metamath or any production checker; (ii) no completeness claim. Prior art: van Dalen 2013 (soundness of propositional natural deduction for truth tables; book level); Troelstra, Schwichtenberg 2000 (book level). Design question: reference point supporting K1 and the K2 counterexamples.
* **S-recompute.** Non-claims: (i) toy propositional logic only, as for S-semSound; (ii) nothing about compiled binaries, compilers, runtimes, memory safety, serialisation, I/O or hardware faults: a `Checker` is a mathematical function, and the model cannot express miscompilation. Prior art: Hurd 2011 (OpenTheory proof articles); Carneiro 2020 (Metamath Zero). Design question: reference point supporting K1, K2d and the rings.
* **S-naive-interface.** Non-claims: (i) only the fields `nec` and `lob` are used; (ii) a statement about this interface, not about provability in any formal system. Prior art: Boolos 1993; Smoryński 1985. Design question: how should an abstract provability interface be designed so that impossibility results stated over it are not vacuous?

S-naive-interface is a reference point for interface design (how to state an abstract provability interface so that impossibility results over it are not vacuous); it is why `ProvFamily` separates theoremhood `Thm` from truth.

### Auxiliary witness statements

Tightness counterexamples, positive controls and non-vacuity witnesses referenced above, in full.

```lean
theorem ex_pinned_official_pos : Pinned officialTable officialTable "False"

theorem ex_semSound_stdRules_pos : SemSound stdRules ∧ Consistent stdRules

theorem ex_faithful_recheckRecompute_pos :
    Faithful (recheckRecompute stdRules) stdRules ∧
    Complete (recheckRecompute stdRules) stdRules ∧
    (recheckRecompute stdRules).accepts topCert [] Form.top = true

theorem ex_traceChecker_accepts_topTrace_pos :
    (traceChecker stdRules).accepts topTrace [] Form.top = true

theorem ex_honest_topCert_pos : Cert.honest stdRules topCert = true

def NaivePropProv.trivial : NaivePropProv where
  Prov := fun _ => True
  nec := fun _ => True.intro
  lob := fun _ => True.intro

theorem NaivePropProv.nonempty : Nonempty NaivePropProv
```

```lean
theorem pinned_name_semValid_fails_without_faithful :
    SemSound stdRules ∧
    Pinned officialTable officialTable "False" ∧
    ¬ Faithful (recheckNoHypGuard stdRules) stdRules ∧
    ¬ (∀ w, (recheckNoHypGuard stdRules).acceptsNamed officialTable w "False" = true →
        ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ)

theorem pinned_name_semValid_fails_without_semSound :
    Faithful (recheckRecompute badRules) badRules ∧
    Pinned officialTable officialTable "False" ∧
    ¬ SemSound badRules ∧
    ¬ (∀ w, (recheckRecompute badRules).acceptsNamed officialTable w "False" = true →
        ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ)

theorem pinned_name_semValid_fails_without_pinned :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    ¬ Pinned officialTable poisonedTable "False" ∧
    ¬ (∀ w, (recheckRecompute stdRules).acceptsNamed poisonedTable w "False" = true →
        ∀ φ, officialTable.lookup "False" = some φ → SemValid [] φ)

theorem k1_nonvacuous :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    Complete (recheckRecompute stdRules) stdRules ∧
    (recheckRecompute stdRules).accepts topCert [] Form.top = true

theorem k1_pinned_nonvacuous :
    Faithful (recheckRecompute stdRules) stdRules ∧
    SemSound stdRules ∧
    Pinned officialTable officialTable "True" ∧
    (recheckRecompute stdRules).acceptsNamed officialTable topCert "True" = true
```

```lean
theorem metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound :
    SemSound stdRules ∧
    RingClosed rubberStampRing ∧
    MetaSound rubberStampRing stdRules 0 ∧
    ¬ FaithfulImpliesMetaSound rubberStampRing stdRules ∧
    ¬ Faithful (rubberStampRing.checker 0) stdRules ∧
    (rubberStampRing.checker 0).AcceptsBot

theorem ring_with_uncertified_link_does_not_propagate :
    SemSound stdRules ∧
    (∀ i, MetaSound brokenLinkRing stdRules i) ∧
    FaithfulImpliesMetaSound brokenLinkRing stdRules ∧
    LinkCertified brokenLinkRing 1 ∧
    ¬ LinkCertified brokenLinkRing 0 ∧
    ¬ Faithful (brokenLinkRing.checker 1) stdRules ∧
    (brokenLinkRing.checker 1).AcceptsBot

theorem k3a_nonvacuous :
    RingClosed (faithfulRing stdRules) ∧
    FaithfulImpliesMetaSound (faithfulRing stdRules) stdRules ∧
    (∃ i₀, MetaSound (faithfulRing stdRules) stdRules i₀) ∧
    SemSound stdRules ∧
    Consistent stdRules

theorem ex_metaSound_pos :
    MetaSound rubberStampRing stdRules 0 ∧
    rubberStampRing.acceptsCert 0 () 0 = false ∧
    ¬ Faithful (rubberStampRing.checker 0) stdRules
```

```lean
theorem consistencyRing_consistent_without_mp (n : Nat) (hn : 2 ≤ n) :
    (∀ i A B, (noMpFamily n).Thm i ((noMpFamily n).imp A ((noMpFamily n).imp B A))) ∧
    (∀ i A B C, (noMpFamily n).Thm i
      ((noMpFamily n).imp ((noMpFamily n).imp A ((noMpFamily n).imp B C))
        ((noMpFamily n).imp ((noMpFamily n).imp A B) ((noMpFamily n).imp A C)))) ∧
    (∀ i, (noMpFamily n).HasEfq i) ∧
    (∀ i, (noMpFamily n).LobRule i) ∧
    (∀ i, (noMpFamily n).GodelII i) ∧
    (noMpFamily n).CrossHBL ∧
    (∀ i, (noMpFamily n).Thm i ((noMpFamily n).con (ringNext i))) ∧
    (∀ i, (noMpFamily n).Consistent i) ∧
    ¬ (∀ i, (noMpFamily n).Thm i (noMpFamily n).bot) ∧
    (∀ i, ¬ (noMpFamily n).MpClosed i) ∧
    (∀ i, ¬ (noMpFamily n).ImpClosed i)

theorem consistencyRing_consistent_without_axK_axS (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (noKSFamily n).MpClosed i) ∧
    (∀ i, (noKSFamily n).HasEfq i) ∧
    (∀ i, (noKSFamily n).LobRule i) ∧
    (∀ i, (noKSFamily n).GodelII i) ∧
    (noKSFamily n).CrossHBL ∧
    (∀ i, (noKSFamily n).Thm i ((noKSFamily n).con (ringNext i))) ∧
    (∀ i, (noKSFamily n).Consistent i) ∧
    ¬ (∀ i, (noKSFamily n).Thm i (noKSFamily n).bot) ∧
    (∀ i, ¬ ∀ A B, (noKSFamily n).Thm i ((noKSFamily n).imp A ((noKSFamily n).imp B A))) ∧
    (∀ i, ¬ ∀ A B C, (noKSFamily n).Thm i
      ((noKSFamily n).imp ((noKSFamily n).imp A ((noKSFamily n).imp B C))
        ((noKSFamily n).imp ((noKSFamily n).imp A B) ((noKSFamily n).imp A C)))) ∧
    (∀ i, ¬ (noKSFamily n).ImpClosed i)

theorem consistencyRing_consistent_without_godelII (n : Nat) (hn : 1 ≤ n) :
    (∀ i, (reflexiveFamily (Fin n)).ImpClosed i) ∧
    (reflexiveFamily (Fin n)).CrossHBL ∧
    (∀ i, (reflexiveFamily (Fin n)).Thm i ((reflexiveFamily (Fin n)).con (ringNext i))) ∧
    (∀ i, (reflexiveFamily (Fin n)).Consistent i) ∧
    ¬ (∀ i, (reflexiveFamily (Fin n)).Thm i (reflexiveFamily (Fin n)).bot) ∧
    (∀ i, ¬ (reflexiveFamily (Fin n)).GodelII i) ∧
    (∀ i, ¬ (reflexiveFamily (Fin n)).LobRule i)

theorem consistencyRing_consistent_without_crossNec (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (leafFamily n).ImpClosed i) ∧
    (∀ i, (leafFamily n).HBL i) ∧
    (∀ i, (leafFamily n).LobRule i) ∧
    (∀ i, (leafFamily n).GodelII i) ∧
    (∀ i j, (leafFamily n).CrossDistrib i j) ∧
    (∀ i j k, (leafFamily n).CrossSigma1 i j k) ∧
    (∀ i, (leafFamily n).Thm i ((leafFamily n).con (ringNext i))) ∧
    (∀ i, (leafFamily n).Consistent i) ∧
    ¬ (∀ i, (leafFamily n).Thm i (leafFamily n).bot) ∧
    (∀ i, ¬ (leafFamily n).CrossNec i (ringNext i))

theorem consistencyRing_consistent_without_crossDistrib (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (possibilityFamily n).ImpClosed i) ∧
    (∀ i, (possibilityFamily n).HBL i) ∧
    (∀ i, (possibilityFamily n).LobRule i) ∧
    (∀ i, (possibilityFamily n).GodelII i) ∧
    (∀ i j, (possibilityFamily n).CrossNec i j) ∧
    (∀ i j k, (possibilityFamily n).CrossSigma1 i j k) ∧
    (∀ i, (possibilityFamily n).Thm i ((possibilityFamily n).con (ringNext i))) ∧
    (∀ i, (possibilityFamily n).Consistent i) ∧
    ¬ (∀ i, (possibilityFamily n).Thm i (possibilityFamily n).bot) ∧
    (∀ i, ¬ (possibilityFamily n).CrossDistrib i (ringNext i))

theorem consistency_proof_along_open_chain_is_consistent :
    (∀ i, omegaChainFamily.ImpClosed i) ∧
    (∀ i, omegaChainFamily.LobRule i) ∧
    (∀ i, omegaChainFamily.GodelII i) ∧
    omegaChainFamily.CrossHBL ∧
    (∀ i, omegaChainFamily.Consistent i) ∧
    omegaChainFamily.Thm 0 (omegaChainFamily.con 1) ∧
    ¬ omegaChainFamily.Thm 1 (omegaChainFamily.con 0) ∧
    ¬ (∀ i, omegaChainFamily.Thm i (omegaChainFamily.con (ringNext i))) ∧
    ¬ (∀ i, omegaChainFamily.Thm i omegaChainFamily.bot) ∧
    (∀ i j, ¬ omegaChainFamily.Thm i (omegaChainFamily.box j omegaChainFamily.bot)) ∧
    (∀ i j k, ¬ omegaChainFamily.Thm i
      (omegaChainFamily.box j (omegaChainFamily.box k omegaChainFamily.bot)))

theorem one_unverified_ring_link_leaves_anchor_inconsistent :
    (∀ i, oneBrokenNecFamily.ImpClosed i) ∧
    (∀ i, oneBrokenNecFamily.LobRule i) ∧
    (∀ i, oneBrokenNecFamily.GodelII i) ∧
    (∀ i j, oneBrokenNecFamily.CrossDistrib i j) ∧
    (∀ i j k, oneBrokenNecFamily.CrossSigma1 i j k) ∧
    oneBrokenNecFamily.D1 0 ∧
    oneBrokenNecFamily.D1 1 ∧
    oneBrokenNecFamily.CrossNec 0 1 ∧
    oneBrokenNecFamily.CrossHBLFrom 0 ∧
    (∀ i, oneBrokenNecFamily.Thm i (oneBrokenNecFamily.con (ringNext i))) ∧
    oneBrokenNecFamily.Thm 0 oneBrokenNecFamily.bot ∧
    oneBrokenNecFamily.Consistent 1 ∧
    ¬ oneBrokenNecFamily.CrossNec 1 0

theorem finite_countermodels_prove_own_inconsistency (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (starFamily n).Thm i ((starFamily n).box i (starFamily n).bot)) ∧
    (∀ i, (leafFamily n).Thm i ((leafFamily n).box i (leafFamily n).bot)) ∧
    (∀ i j k, (leafFamily n).Thm i
      ((leafFamily n).box j ((leafFamily n).box k (leafFamily n).bot))) ∧
    (∀ i, (possibilityFamily n).Thm i ((possibilityFamily n).box i (possibilityFamily n).bot)) ∧
    (∀ i j k, (possibilityFamily n).Thm i
      ((possibilityFamily n).box j ((possibilityFamily n).box k (possibilityFamily n).bot))) ∧
    oneBrokenNecFamily.Thm 1 (oneBrokenNecFamily.box 1 oneBrokenNecFamily.bot)

theorem k4a_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    (∀ i, (trivialFamily (Fin n)).ImpClosed i) ∧
    (∃ i₀ : Fin n, (trivialFamily (Fin n)).GodelII i₀) ∧
    (trivialFamily (Fin n)).CrossHBL ∧
    (∀ i, (trivialFamily (Fin n)).Thm i ((trivialFamily (Fin n)).con (ringNext i)))

theorem k4a_local_nonvacuous (n : Nat) (i₀ : Fin n) :
    (trivialFamily (Fin n)).ImpClosed i₀ ∧
    (trivialFamily (Fin n)).GodelII i₀ ∧
    (trivialFamily (Fin n)).CrossHBLFrom i₀ ∧
    (∀ i, (trivialFamily (Fin n)).Thm i ((trivialFamily (Fin n)).con (ringNext i)))

theorem consistencyRing_consistent_without_crossSigma1_fails_below_two :
    ringNext (0 : Fin 1) = 0 ∧
    ¬ (∀ i, (starFamily 1).Thm i ((starFamily 1).con (ringNext i))) ∧
    ¬ (∀ i, (omegaStarFamily 1).Thm i ((omegaStarFamily 1).con (ringNext i))) ∧
    (∀ i, (starFamily 0).Thm i (starFamily 0).bot) ∧
    (∀ i, (omegaStarFamily 0).Thm i (omegaStarFamily 0).bot)
```

```lean
theorem local_reflection_fails_without_mp :
    noMpEfqFamily.HasEfq 0 ∧
    noMpEfqFamily.Thm 0 noMpEfqFamily.bot ∧
    noMpEfqFamily.GodelII 0 ∧
    ¬ noMpEfqFamily.MpClosed 0 ∧
    ¬ (∀ (j : Fin 1) (A : noMpEfqFamily.Sent),
        noMpEfqFamily.Thm 0 (noMpEfqFamily.imp (noMpEfqFamily.box j A) A)) ∧
    ¬ ((∀ A : noMpEfqFamily.Sent,
          noMpEfqFamily.Thm 0 (noMpEfqFamily.imp (noMpEfqFamily.box 0 A) A)) ↔
        noMpEfqFamily.Thm 0 noMpEfqFamily.bot)

theorem local_reflection_fails_without_efq :
    noEfqBoolFamily.MpClosed () ∧
    (∀ A B, noEfqBoolFamily.Thm () (noEfqBoolFamily.imp A (noEfqBoolFamily.imp B A))) ∧
    (∀ A B C, noEfqBoolFamily.Thm ()
      (noEfqBoolFamily.imp (noEfqBoolFamily.imp A (noEfqBoolFamily.imp B C))
        (noEfqBoolFamily.imp (noEfqBoolFamily.imp A B) (noEfqBoolFamily.imp A C)))) ∧
    noEfqBoolFamily.LobRule () ∧
    noEfqBoolFamily.GodelII () ∧
    noEfqBoolFamily.Thm () noEfqBoolFamily.bot ∧
    ¬ noEfqBoolFamily.HasEfq () ∧
    ¬ (∀ (j : Unit) (A : noEfqBoolFamily.Sent),
        noEfqBoolFamily.Thm () (noEfqBoolFamily.imp (noEfqBoolFamily.box j A) A)) ∧
    ¬ ((∀ A : noEfqBoolFamily.Sent,
          noEfqBoolFamily.Thm () (noEfqBoolFamily.imp (noEfqBoolFamily.box () A) A)) ↔
        noEfqBoolFamily.Thm () noEfqBoolFamily.bot)

theorem local_reflection_fails_without_inconsistency :
    omegaChainFamily.MpClosed 0 ∧
    omegaChainFamily.HasEfq 0 ∧
    omegaChainFamily.Consistent 0 ∧
    ¬ (∀ (j : Fin 2) (A : omegaChainFamily.Sent),
        omegaChainFamily.Thm 0 (omegaChainFamily.imp (omegaChainFamily.box j A) A)) ∧
    ¬ (∀ j : Fin 2, omegaChainFamily.Thm 0 (omegaChainFamily.con j))

theorem local_reflection_iff_fails_without_godelII :
    (reflexiveFamily Unit).MpClosed () ∧
    (reflexiveFamily Unit).HasEfq () ∧
    (reflexiveFamily Unit).Consistent () ∧
    ¬ (reflexiveFamily Unit).GodelII () ∧
    (∀ A : (reflexiveFamily Unit).Sent,
        (reflexiveFamily Unit).Thm () ((reflexiveFamily Unit).imp ((reflexiveFamily Unit).box () A) A)) ∧
    ¬ ((∀ A : (reflexiveFamily Unit).Sent,
          (reflexiveFamily Unit).Thm ()
            ((reflexiveFamily Unit).imp ((reflexiveFamily Unit).box () A) A)) ↔
        (reflexiveFamily Unit).Thm () (reflexiveFamily Unit).bot)

theorem k5_nonvacuous :
    (trivialFamily Unit).MpClosed () ∧ (trivialFamily Unit).HasEfq () ∧
    (trivialFamily Unit).Thm () (trivialFamily Unit).bot

theorem k5_iff_nonvacuous :
    (trivialFamily Unit).MpClosed () ∧ (trivialFamily Unit).HasEfq () ∧
    (trivialFamily Unit).GodelII ()

theorem k5_iff_nonvacuous_consistent :
    omegaChainFamily.MpClosed 0 ∧
    omegaChainFamily.HasEfq 0 ∧
    omegaChainFamily.GodelII 0 ∧
    omegaChainFamily.Consistent 0 ∧
    ¬ (∀ A : omegaChainFamily.Sent,
        omegaChainFamily.Thm 0 (omegaChainFamily.imp (omegaChainFamily.box 0 A) A))
```

```lean
theorem execCert_trust_eq_recompute_fails_without_honest :
    Cert.honest stdRules (lyingCert .bot) = false ∧
    ¬ (∀ stk : Stack, execCert .trust stdRules stk (lyingCert .bot) =
        execCert .recompute stdRules stk (lyingCert .bot))

theorem con_fails_without_mp :
    noMpEfqFamily.HasEfq 0 ∧
    noMpEfqFamily.Thm 0 noMpEfqFamily.bot ∧
    ¬ noMpEfqFamily.MpClosed 0 ∧
    ¬ (∀ j : Fin 1, noMpEfqFamily.Thm 0 (noMpEfqFamily.con j))

def onlyBotFamily : ProvFamily Unit where
  Sent := SynSent 1
  bot  := .bot
  imp  := .imp
  box  := fun _ => .box 0
  Thm  := fun _ s => s = .bot

theorem con_fails_without_efq :
    onlyBotFamily.MpClosed () ∧
    onlyBotFamily.Thm () onlyBotFamily.bot ∧
    ¬ onlyBotFamily.HasEfq () ∧
    ¬ (∀ A B : onlyBotFamily.Sent,
        onlyBotFamily.Thm () (onlyBotFamily.imp A (onlyBotFamily.imp B A))) ∧
    ¬ (∀ j : Unit, onlyBotFamily.Thm () (onlyBotFamily.con j))

theorem k4a_local_hypotheses_hold_in_mixed_ring :
    oneBrokenNecFamily.ImpClosed 0 ∧
    oneBrokenNecFamily.GodelII 0 ∧
    oneBrokenNecFamily.CrossHBLFrom 0 ∧
    (∀ i, oneBrokenNecFamily.Thm i (oneBrokenNecFamily.con (ringNext i))) ∧
    oneBrokenNecFamily.Consistent 1

theorem omegaStarFamily_not_proves_nested_box_bot (n : Nat) (i j k : Fin n) :
    ¬ (omegaStarFamily n).Thm i
        ((omegaStarFamily n).box j ((omegaStarFamily n).box k (omegaStarFamily n).bot))
```

`noMpEfqFamily` is the free-syntax family whose theory proves exactly `⊥` and the formulas `⊥ → A`.

### Supporting lemmas cited in the cards

Statements cited in the prose above that are neither results nor witnesses of a card, in full, with the two definitions they need. Their axioms are listed under `## Evidence`.

```lean
theorem not_acceptsBot_of_faithful_of_consistent {C : Checker} {R : RuleSet}
    (hF : Faithful C R) (hC : Consistent R) : ¬ C.AcceptsBot

theorem ex_consistent_not_semSound_anyImpRules :
    Consistent anyImpRules ∧ ¬ SemSound anyImpRules

theorem badRules_derives_every_formula (φ : Form) : Derivable badRules [] φ

theorem ex_semSound_badRules_neg : ¬ SemSound badRules ∧ ¬ Consistent badRules

theorem ex_pinned_undefined_neg : ¬ Pinned officialTable officialTable "Undefined"

theorem hypsOk_of_execCert {pol : FieldPolicy} {R : RuleSet} {stk out : Stack} {c : Cert}
    (h : execCert pol R stk c = some out) : Cert.HypsOk c

theorem execCertNoHypGuard_eq_of_hypsOk {pol : FieldPolicy} {R : RuleSet} {c : Cert}
    (hc : Cert.HypsOk c) :
    ∀ stk : Stack, execCertNoHypGuard pol R stk c = execCert pol R stk c
```

```lean
def selfHostedRing {n : Nat} (C : Fin n → Checker) (enc : Fin n → Form) : VerifierRing n where
  checker := C
  MetaCert := fun i => (C i).Wit
  acceptsCert := fun i m j => (C i).accepts m [] (enc j)

def ClaimReflection {n : Nat} (R : RuleSet) (C : Fin n → Checker) (enc : Fin n → Form) : Prop :=
  ∀ j : Fin n, Derivable R [] (enc j) → Faithful (C j) R

theorem faithfulImpliesMetaSound_of_selfHosted_of_claimReflection {n : Nat}
    {R : RuleSet} {C : Fin n → Checker} {enc : Fin n → Form}
    (hRefl : ClaimReflection R C enc) :
    FaithfulImpliesMetaSound (selfHostedRing C enc) R

theorem not_claimReflection_badRules_of_unfaithful {n : Nat} (C : Fin n → Checker)
    (enc : Fin n → Form) (j : Fin n) (hU : ¬ Faithful (C j) badRules) :
    ¬ ClaimReflection badRules C enc
```

```lean
-- Declared inside `namespace ProvFamily` with `variable {ι : Type} (F : ProvFamily ι)`;
-- `HBL i` is the conjunction of `D1 i`, `D2 i` and `D3 i`.
theorem LobRule.godelII {i : ι} (h : F.LobRule i) : F.GodelII i

theorem CrossHBL.hbl (h : F.CrossHBL) (i : ι) : F.HBL i
```

```lean
theorem omegaChainFamily_not_proves_con_zero :
    ¬ omegaChainFamily.Thm 1 (omegaChainFamily.con 0)

theorem ex_mpClosed_neg : ¬ (noMpFamily 2).MpClosed 0
```

## Boundaries

**Non-claims first (package-wide).**

1. **Toy model.** Propositional logic with rules as data. Nothing here is a theorem about Lean, Rocq, HOL Light, Metamath, or any production checker. Every connection to real systems in this document is labelled "derived (modeling bridge)".
2. **No binaries, no hardware** (known not to apply). Checkers are mathematical functions. Miscompilation, runtime defects, memory corruption, serialisation and I/O cannot be expressed in this model, so no result covers them. The "trusting trust" problem (Thompson 1984) and its diverse double-compiling countermeasure (Wheeler 2009) concern a layer that is absent here.
3. **Not exhaustive.** The four layers are shown *necessary* for the modelled failure modes. They are not shown sufficient for a real pipeline.
4. **Not independent.** Recomputation (K2d) is a special case of faithfulness (K2b).
5. **Not "rings are useless"** and not "rings suffice". K3a says what a closed ring buys under a named assumption; K3b and K3c say what it does not.
6. **Not "self-verification is worthless".** K5 and the length-one case of K3b say an *unconditional* self-certificate is not evidence by itself.
7. **Abstract provability structures.** K4a, K4a-local, K4b, K5 and K5-iff are about `ProvFamily` structures over one shared sentence language. They transfer to concrete theories only through a verification of the named conditions, which this package does not perform for any theory.
8. **Trusted roots.** The reference semantics `evalForm` and the official statement table are trusted. A misconception shared by rules and semantics, or a wrong official table, is invisible.
9. **Homogeneous rings.** Verifier rings share one rule table and make claims only about ring members.
10. **Translations and exporters are trusted.** The disjoint-defect same-artifact result (S-shared-quorum) is proved only for the identity translation of proof objects; with an untrusted translation the same two re-checkers accept `[] ⊢ ⊥` (`shared_artifact_quorum_of_disjoint_defects_accepts_bot_under_exploit_translator`). A translator, exporter or serialiser shared by both checkers is outside every result here.
11. **Pinning needs definedness.** K1-pinned's conclusion says that the official meaning is valid only because `Pinned` asserts that the name is officially defined; comparing tables only on defined names gives a statement that is vacuous for undefined names.

**Attractive stronger conclusions that are not established.**

* "A faithful kernel is a sound kernel." No: K2a, K3c.
* "Two (or N) independent kernels agreeing is strong evidence." Not established: K2b (separate artifacts; and same artifact with a shared defect); S-shared-quorum shows a benefit only for one pair of disjoint defects re-checking one artifact; nothing is said about the probability of shared defects.
* "A verified kernel that checks its own correctness proof is thereby trustworthy." No: K3b at length one; K5.
* "A closed ring of faithfulness certificates with a meta-sound node certifies its members from nothing." No: K3a converts the named assumption `FaithfulImpliesMetaSound` into the conclusion, and under `RingClosed` the assumptions are exactly as strong as the conclusion.
* "No formal system can prove another's consistency." No: `consistency_proof_along_open_chain_is_consistent`.
* "Lean and Rocq (or any two concrete systems) cannot prove each other consistent." Not established; it would follow only after verifying the conditions of K4a, and a common sentence language, for them.
* "Two theories cannot be equiconsistent or prove each other's relative consistency." Not addressed: K4a concerns categorical consistency statements only.
* "Breaking one condition at one theory, or in one direction, escapes K4a." No: K4a-local.
* "Dropping formalised Σ₁-completeness is a realistic way to obtain mutually certifying consistent systems." No: K4b is an abstract countermodel.

**Escape hatches of the impossibility results.** For K4a-local at a given anchor: drop modus ponens or the axiom schemes K/S at the anchor (`consistencyRing_consistent_without_mp`, `consistencyRing_consistent_without_axK_axS`); drop Gödel II at the anchor (`consistencyRing_consistent_without_godelII`); drop one of the cross-theory conditions from the anchor (`consistencyRing_consistent_without_crossNec`, `consistencyRing_consistent_without_crossDistrib`, `consistencyRing_consistent_without_crossSigma1`); or do not close the cycle (`consistency_proof_along_open_chain_is_consistent`). For *every* theory of a ring to be consistent, *every* theory must use one of these escapes for itself. For K4a's conclusion "every theory proves `⊥`" to fail while some anchor exists, a ring link `CrossNec i (ringNext i)` or modus ponens at some theory must fail, and then only the theories that cannot inherit the anchor's inconsistency are spared (`one_unverified_ring_link_leaves_anchor_inconsistent`).

**Unknown / not examined.**

* Whether `FaithfulImpliesMetaSound` can be *derived* in a logic expressive enough to state faithfulness: outside the toy model (not examined).
* Whether a heterogeneous version of K3a (one rule table per node, claims about faithfulness to another node's table) has the same shape: not examined.
* Whether each of the axiom schemes K and S is individually necessary for K4a (the witness drops both): not examined.

**Disproved or dropped statements.** None. Every one of the 18 results was proved exactly as stated; no statement was found false, and none was weakened or removed.

## Evidence

**Kernel-check record.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); `lake build` of `lean/` succeeds with no warnings and no `sorry`. The axiom audit and the hashes below were recomputed on 2026-11-20 by loading the built library and running `Lean.collectAxioms` on every declaration of the package's modules (855 declarations, recorded in `audit/axioms.json`): 601 use no axiom, 219 use only `propext`, 31 use `propext` and `Quot.sound`, and 4 use `propext`, `Classical.choice` and `Quot.sound` (`consistencyRing_consistent_without_mp`, `consistency_proof_along_open_chain_is_consistent`, `ex_mpClosed_neg`, `omegaChainFamily_not_proves_con_zero`; the choice comes from tactic automation in the proofs, not from any statement). No declaration depends on `sorryAx` or `Lean.ofReduceBool`; no `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern` or `unsafe` occurs in the sources.

Per Lean name referenced by `results.json`: the card and role, the axioms, the **statement hash** (SHA-256 of the `repr` of the declaration's type) and the **definition-closure hash** (SHA-256 of the newline-joined, sorted list of every package constant reachable from the type through types, definition bodies and inductive constructors, each rendered as `name : <repr of type>` followed, for constants other than theorems, by ` := <repr of value>`; theorem proofs are not included), with the closure size. The same values are in `audit/statements.json`; `support/revalidate.py` recomputes them (see `## Revalidation`).

| Lean name | Card | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|:--|:--|:--|:--|:--|:--|
| `accepted_semValid_of_faithful_of_semSound` | K1 | result | none | `edc419aedc1704ca2ea11928a69f2b588509c4a97791b96bab81493aece95412` | `63cfaa14ba632a8cb3da072714f422821013f58615896dbd01ee3ce55a63ee1b` (56) |
| `not_accepts_bot_of_faithful_of_semSound` | K1 | result | `propext` | `116a109fa11b723a1eaac0235838cc4c63be12a4a715d69ccf8baa23a925730b` | `63cfaa14ba632a8cb3da072714f422821013f58615896dbd01ee3ce55a63ee1b` (56) |
| `k1_nonvacuous` | K1 | non-vacuity | `propext` | `34b89cdd1a61ed5c1e1980ed7532c6a2bce2a705da18f2ed517971e7af76809d` | `9a2ea38e81263c9c43a48336071c7c85ae99815572f2dab9e5d844d9a228f082` (102) |
| `unfaithful_checker_for_sound_rules_accepts_bot` | K1 | counterexample | `propext` | `6e93050b5753770d6772d35f9147595695d23e1836642f867f6b168d28498395` | `12f2a6cc64da01c3157d2b95e24bf1a4c626532f1da28e3bf9e31d030277a41a` (99) |
| `faithful_checker_for_unsound_rules_accepts_bot` | K1 | counterexample | `propext` | `6d594714b65cfab452fab3656449319eba6d827cf91a490d19051627c44c195f` | `c4c518f7b23ebaf5866a64154213b3fc65c591ae417c2f2c5135e8f90dc27e6e` (104) |
| `pinned_accepted_name_semValid_of_faithful_of_semSound` | K1-pinned | result | none | `cad09dd7c78bcb3bfe9f61237490fe2a300a908cc09a072f8172a903be0d2df1` | `87bd6bc2c9193805179b856d99d9eee9167536c8bc77659d87336e1167b87f73` (60) |
| `k1_pinned_nonvacuous` | K1-pinned | non-vacuity | `propext` | `ede578d5090e50775956a78c5a53464944ec19ae0b15f0bfabc3780628c65ab1` | `93d9cbd3409a9f0f5bc33cc073888b7c0339d09e890853846ea3ffdf217b20d9` (106) |
| `pinned_name_semValid_fails_without_faithful` | K1-pinned | counterexample | `propext` | `9c23420c6eee1d1c5d787905e604d036e9d55babd21623dfda99eb533ed3e0d3` | `9a72bb35e707f35d2657624b55a32a441b9616cd42101ab364f84f0238a4b697` (104) |
| `pinned_name_semValid_fails_without_semSound` | K1-pinned | counterexample | `propext` | `c273e47247b3fdb9f23ca7fa3e619e7791461af71004f24d3ab70dd8e7a83b53` | `b30957b6cb5d7afe1ca9bc19bd9e8dde44062881e1538d1ddc8909521735efc3` (107) |
| `pinned_name_semValid_fails_without_pinned` | K1-pinned | counterexample | `propext` | `c80c162a6ead9032b84f7af39dbacca5ed1d0b604a0fe4ba721b5422429d5a19` | `35ede5551a269b081d9e0b2f8c094a33c70ed8227d84bd22cc9612ce0cd41df4` (106) |
| `unpinned_faithful_checker_for_sound_rules_accepts_renamed_False` | K1-pinned | counterexample | `propext` | `778809cd324d5ae8831e24ce318284455f262643a20ea4ef0879cfa8abd5dfbf` | `e2b75142357938425323b4dbac94177d0c36e32e064b7949ba926f79fb49539b` (107) |
| `faithful_checker_for_unsound_rules_accepts_bot` | K2a | result | `propext` | `6d594714b65cfab452fab3656449319eba6d827cf91a490d19051627c44c195f` | `c4c518f7b23ebaf5866a64154213b3fc65c591ae417c2f2c5135e8f90dc27e6e` (104) |
| `unfaithful_checker_for_sound_rules_accepts_bot` | K2b | result | `propext` | `6e93050b5753770d6772d35f9147595695d23e1836642f867f6b168d28498395` | `12f2a6cc64da01c3157d2b95e24bf1a4c626532f1da28e3bf9e31d030277a41a` (99) |
| `separate_artifact_quorum_of_two_unfaithful_checkers_accepts_bot` | K2b | result | `propext` | `70bc5531e8281d57abaa1ebf18346ceb278892f4861175e9d570c36035891e50` | `4abd6b544b7eacca76d3f2560fbe9ba94d4b00fced604239777342a9ff1ff318` (105) |
| `shared_artifact_quorum_of_checkers_with_a_shared_defect_accepts_bot` | K2b | result | `propext` | `fd6d48624e1bc03ec22e336abdfaf53d8821e0d8387f03e5ecb798ab3b672c5b` | `71f12a61c27f9b85cf541f5d248b284798a1d02f65f31f8f73946b3a8ddee8e4` (102) |
| `unpinned_faithful_checker_for_sound_rules_accepts_renamed_False` | K2c | result | `propext` | `778809cd324d5ae8831e24ce318284455f262643a20ea4ef0879cfa8abd5dfbf` | `e2b75142357938425323b4dbac94177d0c36e32e064b7949ba926f79fb49539b` (107) |
| `pinned_False_never_accepted` | K2c | result | `propext` | `ebcd6b860b4f4d0f10d8e72c644ed27dac1a9095e3f5daef9d1a4e517544cd84` | `3da393d63263806c444f4ff659e0668ca24702429d3f357cbc92dea1e8906ea4` (92) |
| `ex_pinned_official_pos` | K2c | non-vacuity | `propext` | `f1127b5104c70464a6d54c69df90d2c46ac57898c60b86e3a93f71bd4e391dac` | `113a5cfdf429e4e9da123bf9863a264d38cea38a070851277caff38adeb5b3ab` (10) |
| `unpinned_faithful_checker_for_sound_rules_accepts_renamed_False` | K2c | counterexample | `propext` | `778809cd324d5ae8831e24ce318284455f262643a20ea4ef0879cfa8abd5dfbf` | `e2b75142357938425323b4dbac94177d0c36e32e064b7949ba926f79fb49539b` (107) |
| `trusting_rechecker_accepts_bot_recomputing_rechecker_rejects` | K2d | result | `Quot.sound`, `propext` | `17e3b26b2fb9d510882261ea23853e7ec2288508531aae6fb05c53db0e311c11` | `697b5d7ef4c579313d97c45e551ff1bcf5f4d7dfa636ad64f1441caac87c32e4` (103) |
| `sharedQuorum_recheckTrust_recheckNoHypGuard_faithful` | S-shared-quorum | result | `propext` | `01a6717d104b581101601230909e66a43177a91bff8ae689041011c6a3e3e37a` | `4d8f508045a3612c663906ba3a00e004baf203f45753edbc5d44b21ac687a5e8` (93) |
| `shared_artifact_quorum_of_checkers_with_disjoint_defects_is_faithful` | S-shared-quorum | result | `propext` | `ece2b0fced91129c970c956ce1a75ae7b7eedc6da2566904abacc18bb25e2e95` | `8ecb1c9360c10acd2f6ee4bdbb48b3a426b842367eceff8716d3be10751f5863` (98) |
| `shared_artifact_quorum_of_checkers_with_disjoint_defects_is_faithful` | S-shared-quorum | non-vacuity | `propext` | `ece2b0fced91129c970c956ce1a75ae7b7eedc6da2566904abacc18bb25e2e95` | `8ecb1c9360c10acd2f6ee4bdbb48b3a426b842367eceff8716d3be10751f5863` (98) |
| `ring_all_faithful_of_metaSound_anchor_of_faithfulImpliesMetaSound` | K3a | result | `Quot.sound`, `propext` | `5de0584378275646e3442a2745a00b6bfb9802b0b0271fbb47eb6b255aed1a0a` | `8a98589b85737ae252998c2e5290eae9f9204b2cc2a0f35560b81890a93fa393` (53) |
| `ring_no_node_accepts_bot_of_metaSound_anchor_of_faithfulImpliesMetaSound_of_consistent` | K3a | result | `Quot.sound`, `propext` | `6471efcfb9d6260fe06fe199b8d660fc46777b5d9c2ecee4cd210e524c0fffa1` | `75854b3f00f79ee52a7ca170a61355eb9f6477a89d0b0b56e1089e4a794bbaf8` (54) |
| `k3a_nonvacuous` | K3a | non-vacuity | `propext` | `21d4550e090cb2c8b3e4be7e1125de123cb1de3b88ad1e3c88acf301c1bdc945` | `57de51c7d6e5c07e3acacf82279ea162a08d2b58052e68a02f0bb498277f0afe` (137) |
| `ring_with_uncertified_link_does_not_propagate` | K3a | counterexample | `propext` | `56a1a751f9d89fcda6a3af4c831e7ef9fe2426282b417440586be6ed9ec07755` | `69be0736de3be1ca125480d0d881e0c6b5ab356c06364edd0abd34a9c12159ac` (114) |
| `metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound` | K3a | counterexample | `propext` | `4c034e9ba515106eb07a541aa6df4070b0ddbbcb22769d8f25d6c11337a8a5b6` | `1d7e88a0393aee4fed24238b18ca2dba63488633bf36356ac1439c2db0239a66` (115) |
| `three_unfaithful_checkers_close_faithfulness_ring` | K3a | counterexample | `propext` | `1991f62315032b6f07dd0ba98624f82f378fd4a479912c7e0f26b4ea6da026fd` | `383370154a242e42b637265541a50e4f389a6fe47c4a7d445fba8e878983c726` (118) |
| `ring_of_faithful_checkers_over_unsound_rules_accepts_bot` | K3a | counterexample | `propext` | `f70d5d7280cfd66f49d09dcbfe6679f09acd1efff651b8e4269002658c856d9f` | `8133b3347de3a13bc1a831c832cdc3f66ded3c600416547519e63a4761f7d527` (139) |
| `three_unfaithful_checkers_close_faithfulness_ring` | K3b | result | `propext` | `1991f62315032b6f07dd0ba98624f82f378fd4a479912c7e0f26b4ea6da026fd` | `383370154a242e42b637265541a50e4f389a6fe47c4a7d445fba8e878983c726` (118) |
| `unfaithful_checker_certifies_its_own_faithfulness` | K3b | result | `propext` | `45aed8a4e8f0dc8cc14012376f79310436450c226adaef19378690d7652b5f5d` | `418a0ddd6adbbe3aa5bc09af0709f32d0e30aaae691992e787dc67291888ac80` (100) |
| `ring_of_faithful_checkers_over_unsound_rules_accepts_bot` | K3c | result | `propext` | `f70d5d7280cfd66f49d09dcbfe6679f09acd1efff651b8e4269002658c856d9f` | `8133b3347de3a13bc1a831c832cdc3f66ded3c600416547519e63a4761f7d527` (139) |
| `consistencyRing_all_inconsistent_of_impClosed_godelIIAnchor_crossHBL` | K4a | result | `Quot.sound`, `propext` | `f16a8765404771bf4034be240ef2d711bdf163a28c7e489e90d221ad167693de` | `ac23f82eb193abeedad818255d44a10a6a0b493c51b3db9cd0f0d8af8b78f41e` (19) |
| `k4a_nonvacuous` | K4a | non-vacuity | none | `b9590e03db7a287d0f42a4d54295ecab2baa0cd3f69fa5d8ee8231791473d07b` | `11b07c2da2338aea6c3bd421addde84e1802724e032605c5cc4feaac3e850546` (20) |
| `consistency_proof_along_open_chain_is_consistent` | K4a | positive control | `Classical.choice`, `Quot.sound`, `propext` | `148473ac9091b4e8168b761b249bce8a9de171482524649f9923c8aee80f0f93` | `110cb9c0b1345f32336acab3be7af6a3783218ae88cdd4cc08a4c0962a4b06fe` (30) |
| `two_consistent_theories_prove_each_others_consistency_without_crossSigma1` | K4a | positive control | `Quot.sound`, `propext` | `03e40c38de6011ccf083f78deed8c592562003e4ef102247a38c71a1c3d1fb37` | `1a6455e78af057b5b395fa100ceffb5055a8d1d3f81f15167f2a4658e5ab918b` (29) |
| `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency` | K4a | positive control | `Quot.sound`, `propext` | `b4fc43bfc7c376d78c86ed6645f1334e9877b831652373fd1bdef6059ded280a` | `7b7f673155833b4cae46fa51b93432a9bd1df6d8826130b017ac9c383e7c278d` (33) |
| `one_unverified_ring_link_leaves_anchor_inconsistent` | K4a | positive control | `propext` | `c109e69206bc09ab6f0be59e85379bb8fd3263db9e9ec4b8c62cded12e565682` | `f899b2b85ff620dd7eb9248a8db0a1e224b8df3d5c8e16e6f61c28f2fd9efc34` (31) |
| `consistencyRing_consistent_without_mp` | K4a | counterexample | `Classical.choice`, `Quot.sound`, `propext` | `24147cc0de413cec03c836901139f129a65706994c269e5718a8d203ac122569` | `4f2a2816646e2ea0f5c7c13948fbcebbcbbceb5fd05385c069037fdeb00e891b` (35) |
| `consistencyRing_consistent_without_axK_axS` | K4a | counterexample | `Quot.sound`, `propext` | `38edcbaf574251994700b0afb1cfc779f73330bbc1e543a98fe457cda77f6a48` | `88c2bb2070ddc4fcc74c3b468b03b9df0b0fb0e503dd5affa7d519947a3fd124` (35) |
| `consistencyRing_consistent_without_godelII` | K4a | counterexample | none | `0e42e3fa51ef23ac692c2b7770fc32b3178a683b9147d419848404deaf7fa25f` | `89d92c7d395ed040fb7086a731f6210622450626bddf2b8071acf4a678cc844d` (29) |
| `consistencyRing_consistent_without_crossNec` | K4a | counterexample | `Quot.sound`, `propext` | `e9de7c38e687fa3318c7cfc739f487401b0e91091e11e93ee87991f44431a644` | `8071fef323e49fdf5aa8484c8e382bbbca0003aba252a653ed32790d69c7fa5a` (36) |
| `one_unverified_ring_link_leaves_anchor_inconsistent` | K4a | counterexample | `propext` | `c109e69206bc09ab6f0be59e85379bb8fd3263db9e9ec4b8c62cded12e565682` | `f899b2b85ff620dd7eb9248a8db0a1e224b8df3d5c8e16e6f61c28f2fd9efc34` (31) |
| `consistencyRing_consistent_without_crossDistrib` | K4a | counterexample | `Quot.sound`, `propext` | `6d97720d4d5ba167d6c2537af9399177f05cd68b8af36316bdd17ad43a8d0461` | `99371d2be12bafba43ad3704c4cc6fceefe8fe4da9289c6badaeb9ae7de06163` (25) |
| `consistencyRing_consistent_without_crossSigma1` | K4a | counterexample | `Quot.sound`, `propext` | `d34055ec7eaaa70da38c58b790dc97d0081b974908588c94ec234255dceaa2ef` | `f5d5229fd06c829bf33fd1b70f28db63aa0f2d0510b68d98930803a90f0d747b` (32) |
| `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency` | K4a | counterexample | `Quot.sound`, `propext` | `b4fc43bfc7c376d78c86ed6645f1334e9877b831652373fd1bdef6059ded280a` | `7b7f673155833b4cae46fa51b93432a9bd1df6d8826130b017ac9c383e7c278d` (33) |
| `consistency_proof_along_open_chain_is_consistent` | K4a | counterexample | `Classical.choice`, `Quot.sound`, `propext` | `148473ac9091b4e8168b761b249bce8a9de171482524649f9923c8aee80f0f93` | `110cb9c0b1345f32336acab3be7af6a3783218ae88cdd4cc08a4c0962a4b06fe` (30) |
| `consistencyRing_anchor_inconsistent_of_impClosed_godelII_crossHBLFrom` | K4a-local | result | `Quot.sound`, `propext` | `1114771c55922730d585b434b40f09c1f6950c3e79edde1f850ccd7a810ff79e` | `ff8bd93d9b4c43463fd45ec06077a8ed88e64c826c44896e0a0d3c89091b0b1a` (19) |
| `k4a_local_nonvacuous` | K4a-local | non-vacuity | none | `e0cb18f67e1568255e7268c08a699beca994b7b9fb3e14e58a0351845ba790b7` | `0527d7d82217107562eaf8cda3919b9ed55862aeec56ade0863c656b6299dc68` (20) |
| `k4a_local_hypotheses_hold_in_mixed_ring` | K4a-local | non-vacuity | `propext` | `6c70391ef22ed988091d19a6515ffc22fd3a4be91771516cd89817830ce9a0af` | `61a927feb4753164fa77ab8c5807abf8ebf75d765fd5b938934ba1ec769b90d8` (29) |
| `consistency_proof_along_open_chain_is_consistent` | K4a-local | positive control | `Classical.choice`, `Quot.sound`, `propext` | `148473ac9091b4e8168b761b249bce8a9de171482524649f9923c8aee80f0f93` | `110cb9c0b1345f32336acab3be7af6a3783218ae88cdd4cc08a4c0962a4b06fe` (30) |
| `two_consistent_theories_prove_each_others_consistency_without_crossSigma1` | K4a-local | positive control | `Quot.sound`, `propext` | `03e40c38de6011ccf083f78deed8c592562003e4ef102247a38c71a1c3d1fb37` | `1a6455e78af057b5b395fa100ceffb5055a8d1d3f81f15167f2a4658e5ab918b` (29) |
| `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency` | K4a-local | positive control | `Quot.sound`, `propext` | `b4fc43bfc7c376d78c86ed6645f1334e9877b831652373fd1bdef6059ded280a` | `7b7f673155833b4cae46fa51b93432a9bd1df6d8826130b017ac9c383e7c278d` (33) |
| `one_unverified_ring_link_leaves_anchor_inconsistent` | K4a-local | positive control | `propext` | `c109e69206bc09ab6f0be59e85379bb8fd3263db9e9ec4b8c62cded12e565682` | `f899b2b85ff620dd7eb9248a8db0a1e224b8df3d5c8e16e6f61c28f2fd9efc34` (31) |
| `consistencyRing_consistent_without_mp` | K4a-local | counterexample | `Classical.choice`, `Quot.sound`, `propext` | `24147cc0de413cec03c836901139f129a65706994c269e5718a8d203ac122569` | `4f2a2816646e2ea0f5c7c13948fbcebbcbbceb5fd05385c069037fdeb00e891b` (35) |
| `consistencyRing_consistent_without_axK_axS` | K4a-local | counterexample | `Quot.sound`, `propext` | `38edcbaf574251994700b0afb1cfc779f73330bbc1e543a98fe457cda77f6a48` | `88c2bb2070ddc4fcc74c3b468b03b9df0b0fb0e503dd5affa7d519947a3fd124` (35) |
| `consistencyRing_consistent_without_godelII` | K4a-local | counterexample | none | `0e42e3fa51ef23ac692c2b7770fc32b3178a683b9147d419848404deaf7fa25f` | `89d92c7d395ed040fb7086a731f6210622450626bddf2b8071acf4a678cc844d` (29) |
| `consistencyRing_consistent_without_crossNec` | K4a-local | counterexample | `Quot.sound`, `propext` | `e9de7c38e687fa3318c7cfc739f487401b0e91091e11e93ee87991f44431a644` | `8071fef323e49fdf5aa8484c8e382bbbca0003aba252a653ed32790d69c7fa5a` (36) |
| `consistencyRing_consistent_without_crossDistrib` | K4a-local | counterexample | `Quot.sound`, `propext` | `6d97720d4d5ba167d6c2537af9399177f05cd68b8af36316bdd17ad43a8d0461` | `99371d2be12bafba43ad3704c4cc6fceefe8fe4da9289c6badaeb9ae7de06163` (25) |
| `consistencyRing_consistent_without_crossSigma1` | K4a-local | counterexample | `Quot.sound`, `propext` | `d34055ec7eaaa70da38c58b790dc97d0081b974908588c94ec234255dceaa2ef` | `f5d5229fd06c829bf33fd1b70f28db63aa0f2d0510b68d98930803a90f0d747b` (32) |
| `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency` | K4a-local | counterexample | `Quot.sound`, `propext` | `b4fc43bfc7c376d78c86ed6645f1334e9877b831652373fd1bdef6059ded280a` | `7b7f673155833b4cae46fa51b93432a9bd1df6d8826130b017ac9c383e7c278d` (33) |
| `consistency_proof_along_open_chain_is_consistent` | K4a-local | counterexample | `Classical.choice`, `Quot.sound`, `propext` | `148473ac9091b4e8168b761b249bce8a9de171482524649f9923c8aee80f0f93` | `110cb9c0b1345f32336acab3be7af6a3783218ae88cdd4cc08a4c0962a4b06fe` (30) |
| `two_consistent_theories_prove_each_others_consistency_without_crossSigma1` | K4b | result | `Quot.sound`, `propext` | `03e40c38de6011ccf083f78deed8c592562003e4ef102247a38c71a1c3d1fb37` | `1a6455e78af057b5b395fa100ceffb5055a8d1d3f81f15167f2a4658e5ab918b` (29) |
| `consistencyRing_consistent_without_crossSigma1` | K4b | result | `Quot.sound`, `propext` | `d34055ec7eaaa70da38c58b790dc97d0081b974908588c94ec234255dceaa2ef` | `f5d5229fd06c829bf33fd1b70f28db63aa0f2d0510b68d98930803a90f0d747b` (32) |
| `consistencyRing_consistent_without_crossSigma1_not_proving_own_inconsistency` | K4b | result | `Quot.sound`, `propext` | `b4fc43bfc7c376d78c86ed6645f1334e9877b831652373fd1bdef6059ded280a` | `7b7f673155833b4cae46fa51b93432a9bd1df6d8826130b017ac9c383e7c278d` (33) |
| `starFamily_proves_own_inconsistency` | K4b | result | none | `db27af9aeabe9c0dcc207b2849aa7012c7b013c750b4d3750f566d965956f87d` | `67ecf5b7442b0377d79aa2d6a04d372187f0588ad92038ce9f56db5a3241f647` (14) |
| `consistencyRing_consistent_without_crossSigma1_fails_below_two` | K4b | counterexample | `propext` | `457c51c96087d88e15da28002fe829481260acfaacb2183d23c4fbd302368eed` | `55fceda797a94c9d497205f1d67b7a58866a5002fd1367f46cb0fc5ca4cebbc9` (21) |
| `inconsistent_proves_every_local_reflection_of_mp_efq` | K5 | result | none | `fcfcdf196893074b314e70cba3adcc0f320593d71251878f8e5b69b041413237` | `615fc1e1dd526351e3c51827edd90a23971b6801d5202038b9dd3580bf73d0ca` (9) |
| `inconsistent_proves_every_con_of_mp_efq` | K5 | result | none | `b94327d2a2ef0def6d59e3b4609e21acc78c2556c4dcb17b6b10b059f81f12db` | `031beaf08d7554138380f52c746efbbd50a976b4c461ea05d31229d836e75486` (10) |
| `k5_nonvacuous` | K5 | non-vacuity | none | `f7674f17e6978fa5d3f5ac601857b0724bc849b93aca4055b4777476fcae4ff0` | `7d309ad091fb80b50262fa31af212b1439bb7383c4322b6a6782482a5fbf7660` (9) |
| `local_reflection_fails_without_mp` | K5 | counterexample | `propext` | `7ec0773e1935ec3234a5ad0bcfc912646d82166b6d9fb85e4b505edd7ffc06c1` | `8a52220bbf9f0eedbf4839933577087c0304099c46c5a11e82de01b5cef74655` (16) |
| `con_fails_without_mp` | K5 | counterexample | `propext` | `387da85fb143495f7be628e0b70b010732df47eb557f179146017ee8865c91c1` | `1c7b221edb864e4e467b59705874145436aa4cd227710094b27173a5410ce7af` (15) |
| `local_reflection_fails_without_efq` | K5 | counterexample | `propext` | `2387602f76887bbecde92afe40a70116598c4669eb6aef3197951284e67e5407` | `57597557444ac76d348a615f5e6ee0f1d51843f6feb8ac23aaf3fc7318753791` (13) |
| `con_fails_without_efq` | K5 | counterexample | `propext` | `c23ac853dc5ce072a6933da61ddcce2066a169f3d91ea21a1d44f7c77d4243fa` | `8c2cb18f0f9b3e736c7ac4ab74c16536549376c80211d7771fa86acb9f3a7c02` (16) |
| `local_reflection_fails_without_inconsistency` | K5 | counterexample | `Quot.sound`, `propext` | `db100b8a323c28373e247a63a8fd147b36d38c71e2acbe9e0f2220a116c8205b` | `030d4b84fe39f900cd69e226501be1854384ce56db4ae0c1b55f3d022c2e60f0` (20) |
| `proves_own_local_reflection_iff_inconsistent_of_mp_efq_godelII` | K5-iff | result | none | `49829f9fe0f2e9e9ada98e6c4b466745f6e35de806e85a2b4c43735358e0bed0` | `917c8a9475c3f60212cdacea495b0f09d2f1d2fbdd610a21b04b703e9dc9cf64` (11) |
| `k5_iff_nonvacuous` | K5-iff | non-vacuity | none | `18a8e0d40ed089c6e7ce6248ee9fc939e3c25fe99774ae1d8c97c7565fefcfc2` | `a513d60a39a2d949bcb8f2361833721a83aad1acb8abbbff002b3bccafff54c6` (12) |
| `k5_iff_nonvacuous_consistent` | K5-iff | non-vacuity | `Quot.sound`, `propext` | `c0aa3b173702c91705b964c6635ca5c00c0688c38f9d16bd9fe12b957b80dc0d` | `06cc2dcd754e4a6f07d9cf2bd6061799057f4323aea1317c59edabc8ccba138a` (21) |
| `local_reflection_fails_without_mp` | K5-iff | counterexample | `propext` | `7ec0773e1935ec3234a5ad0bcfc912646d82166b6d9fb85e4b505edd7ffc06c1` | `8a52220bbf9f0eedbf4839933577087c0304099c46c5a11e82de01b5cef74655` (16) |
| `local_reflection_fails_without_efq` | K5-iff | counterexample | `propext` | `2387602f76887bbecde92afe40a70116598c4669eb6aef3197951284e67e5407` | `57597557444ac76d348a615f5e6ee0f1d51843f6feb8ac23aaf3fc7318753791` (13) |
| `local_reflection_iff_fails_without_godelII` | K5-iff | counterexample | none | `b7e7340978725772eb0595bfc7aa9927c529de0bf4adb5972e67d22ae8488d78` | `5d9d59d60360b9bf7afda50aa96f8efb1b111408c4575026795f41a2724b2d73` (20) |
| `stdRules_semSound` | S-semSound | result | `propext` | `b218a5fabb2a0a06981125f0b36ca77436c67be7d8b71aba2d95a3045ad0981a` | `f5f7fed033b5a35555b193c52081ac2763704a22ec9a036e37ff390d93292751` (52) |
| `stdRules_consistent` | S-semSound | result | `propext` | `18fab44983f97c6825fe891546a964e6ddc25287853475a7c597be8de6800740` | `aaa1455b5ac0a0acf466e7eaacf5ff803d865de1a45ee2908a61ed7c837dc307` (39) |
| `ex_semSound_stdRules_pos` | S-semSound | non-vacuity | `propext` | `cdf95304b033b0e74a86bf02eb9666ae72d9843fa6d2cdf1809b93c5f96ae071` | `f91abc46cd0327ecc499e2b23f63e025bee99cb106b8d3bc31418a48d8cbe88e` (53) |
| `recheckRecompute_faithful` | S-recompute | result | `propext` | `6dc1906e115cf6964a8af9ed4b5eb2942f03ec17c88b8d82f9ff6909fa7535ff` | `f27dd34b8d4a0020b241000b79cb0c13a033b0729c35d5771bf2b86e5c6e7f17` (89) |
| `recheck_complete` | S-recompute | result | `propext` | `aa8346ea854b711d4fa1df9ea6f7488f32943f86e496fac7d9761c4dee69ca30` | `1ff14843c5b0f1dd4b6bd237bdcb9f350c5922b57c85fbdc5987d1d72e768a8d` (88) |
| `execCert_trust_eq_recompute_of_honest` | S-recompute | result | `Quot.sound`, `propext` | `f7188cc015af5da119418ed7f39670b498a552f213ae217911abcbce6f7e16a3` | `ab5079f967388692d4650b246b9d478f5b6d26d6eee4ffff2044363824b919e8` (82) |
| `traceChecker_faithful` | S-recompute | result | `propext` | `fee10e4915233dd9500fc3be3fa14d7312e04836714665bcb4a89d27f51534fa` | `09e4d1b45dc7acdd431490d45466df0f74e1003b3f1914f34dc4ce64173b8c1a` (86) |
| `ex_faithful_recheckRecompute_pos` | S-recompute | non-vacuity | `propext` | `94b6bfe7355bc0cbfee46d3721f52365c00a3c98906764a053b9ca1d90547695` | `eae32694cde5cb8e90026a19e667583ed85b2bb552bc3848d65fe4619e7ad594` (93) |
| `ex_traceChecker_accepts_topTrace_pos` | S-recompute | non-vacuity | `propext` | `07ab4d0695760206285176c3f8bf8f9329bd769a178790c37c2db9a3447dfda9` | `11dd4cb49f837977d6fbbd065a482f4db5b8aaa727df854a0a807829252ce5a2` (85) |
| `ex_honest_topCert_pos` | S-recompute | non-vacuity | `propext` | `59b0a961db1e56f511fdf08ee9e6703ef189f558d4eeb2bfacff8a9f72ea1e7e` | `45513d4585a96d776340dd28b180b08045041207f883e20e5be555a563da3b2d` (32) |
| `execCert_trust_eq_recompute_fails_without_honest` | S-recompute | counterexample | `propext` | `8f922043c8dad2e44ad5e645df2e64be94ec25e3ac6ef790f04cd4f68d83b0ad` | `378ad8fa5953201ad89579792e70137c4b3ee1682dda52f5912e3715ebcd3d81` (84) |
| `NaivePropProv.not_not_prov_false` | S-naive-interface | result | none | `45869b0dd3cf556ccf7c5696050c721ed483df3ac10589d481fdc0c6069090cf` | `6e445e2e886608cdeb9e6eaba6d95e3cfc26c2b62ece5f20307eff0adf6105e4` (3) |
| `NaivePropProv.nonempty` | S-naive-interface | non-vacuity | none | `a4e74f3109f3b12e339d39d098c6a4438c36479fbb31a19dd3cb40cd6a30b590` | `6b67193358a82243f694adafffc8cc65d04cfc4591a360ed83c94cd104a998d8` (2) |

Supporting statements cited in the cards but not referenced by `results.json` (axioms only):

| Lean name | Axioms |
|:--|:--|
| `pinned_official_meaning_forall_iff_exists` | none |
| `accepted_name_semValid_of_faithful_of_semSound_of_agreement` | none |
| `sharedQuorum_faithful_left` | `propext` |
| `sharedQuorum_faithful_right` | `propext` |
| `shared_artifact_quorum_of_disjoint_defects_accepts_bot_under_exploit_translator` | `propext` |
| `omegaStarFamily_not_proves_nested_box_bot` | `propext` |
| `ring_metaSound_of_all_faithful` | none |
| `inconsistent_of_proves_con_of_inconsistent` | none |
| `finite_countermodels_prove_own_inconsistency` | `Quot.sound`, `propext` |
| `not_acceptsBot_of_faithful_of_consistent` | none |
| `ex_consistent_not_semSound_anyImpRules` | `propext` |
| `badRules_derives_every_formula` | `propext` |
| `ex_semSound_badRules_neg` | `propext` |
| `ex_pinned_undefined_neg` | `propext` |
| `hypsOk_of_execCert` | `propext` |
| `execCertNoHypGuard_eq_of_hypsOk` | `propext` |
| `faithfulImpliesMetaSound_of_selfHosted_of_claimReflection` | none |
| `not_claimReflection_badRules_of_unfaithful` | `propext` |
| `ProvFamily.LobRule.godelII` | none |
| `ProvFamily.CrossHBL.hbl` | none |
| `omegaChainFamily_not_proves_con_zero` | `Classical.choice`, `Quot.sound`, `propext` |
| `ex_mpClosed_neg` | `Classical.choice`, `Quot.sound`, `propext` |

**Prior art** (bibliographic data checked against Crossref, DataCite, the arXiv listing, or the Stack Exchange API unless stated).

* A. Abel, J. Öhman, A. Vezzosi. *Decidability of conversion for type theory in type theory.* Proc. ACM Program. Lang. 2(POPL), 23:1–23:29, 2018. doi:10.1145/3158111.
* O. Abrahamsson, M. O. Myreen, R. Kumar, T. Sewell. *Candle: A Verified Implementation of HOL Light.* ITP 2022, LIPIcs vol. 237, pp. 3:1–3:17. doi:10.4230/LIPIcs.ITP.2022.3. Extended version: *Candle: A Verified Implementation of HOL Light (Extended Version).* J. Autom. Reason. 69(4), 2025. doi:10.1007/s10817-025-09743-8.
* M. Adams. *Proof Auditing Formalised Mathematics.* J. Formaliz. Reason. 9(1):3–32, 2016. doi:10.6092/issn.1972-5787/4576.
* H. Barendregt, F. Wiedijk. *The challenge of computer mathematics.* Phil. Trans. R. Soc. A 363(1835):2351–2375, 2005. doi:10.1098/rsta.2005.1650.
* B. Barras. *Sets in Coq, Coq in Sets.* J. Formaliz. Reason. 3(1):29–48, 2010. doi:10.6092/issn.1972-5787/1695.
* L. D. Beklemishev. *Bimodal Logics for Extensions of Arithmetical Theories.* J. Symb. Log. 61(1):91–124, 1996. doi:10.2307/2275600.
* L. D. Beklemishev. *Reflection principles and provability algebras in formal arithmetic.* Russian Math. Surveys 60(2):197–268, 2005. doi:10.1070/RM2005v060n02ABEH000823.
* G. Boolos. *The Logic of Provability.* Cambridge University Press, 1993. doi:10.1017/CBO9780511625183.
* M. Carneiro. *Lean4Lean: Verifying a Typechecker for Lean, in Lean.* TYPES 2025 (post-proceedings), LIPIcs vol. 384, pp. 2:1–2:23, 2026. doi:10.4230/LIPIcs.TYPES.2025.2. Preprint arXiv:2403.14064.
* M. Carneiro. *Metamath Zero: Designing a Theorem Prover Prover.* CICM 2020, LNCS 12236, pp. 71–88. doi:10.1007/978-3-030-53518-6_5.
* T. Carlson. *Modal logics with several operators and provability interpretations.* Israel J. Math. 54(1):14–24, 1986. doi:10.1007/BF02764872.
* J. Davis, M. O. Myreen. *The Reflective Milawa Theorem Prover is Sound (Down to the Machine Code that Runs it).* J. Autom. Reason. 55(2):117–183, 2015. doi:10.1007/s10817-015-9324-6.
* S. Feferman. *Arithmetization of metamathematics in a general setting.* Fund. Math. 49(1):35–92, 1960. doi:10.4064/fm-49-1-35-92.
* S. Feferman. *Transfinite recursive progressions of axiomatic theories.* J. Symb. Log. 27(3):259–316, 1962. doi:10.2307/2964649.
* K. Gödel. *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I.* Monatsh. Math. Phys. 38:173–198, 1931. doi:10.1007/BF01700692.
* J. D. Hamkins. *Nonlinearity and illfoundedness in the hierarchy of large cardinal consistency strength.* arXiv:2208.07445, 2022.
* J. Harrison. *Towards Self-verification of HOL Light.* IJCAR 2006, LNCS 4130, pp. 177–191. doi:10.1007/11814771_17.
* D. Hilbert, P. Bernays. *Grundlagen der Mathematik*, Vol. II. Springer, Berlin, 1939. (Bibliographic record only; no DOI.)
* J. Hurd. *The OpenTheory Standard Theory Library.* NASA Formal Methods (NFM 2011), LNCS 6617, pp. 177–191. doi:10.1007/978-3-642-20398-5_14.
* G. Japaridze, D. de Jongh. *The Logic of Provability.* In: S. R. Buss (ed.), *Handbook of Proof Theory*, Studies in Logic and the Foundations of Mathematics 137, Elsevier, 1998, pp. 475–546. doi:10.1016/S0049-237X(98)80022-0.
* D. Kirst, M. Hermes. *Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq.* J. Autom. Reason. 67(1), 2023. doi:10.1007/s10817-022-09647-x.
* G. Kreisel, A. Lévy. *Reflection Principles and their Use for Establishing the Complexity of Axiomatic Systems.* Z. Math. Logik Grundlagen Math. 14(7–12):97–142, 1968. doi:10.1002/malq.19680140702.
* R. Kumar, R. Arthan, M. O. Myreen, S. Owens. *Self-Formalisation of Higher-Order Logic: Semantics, Soundness, and a Verified Implementation.* J. Autom. Reason. 56(3):221–259, 2016. doi:10.1007/s10817-015-9357-x.
* T. Kurahashi. *A note on derivability conditions.* J. Symb. Log. 85(3):1224–1253, 2020. doi:10.1017/jsl.2020.33. Preprint arXiv:1902.00895.
* P. Lindström. *Aspects of Incompleteness.* Lecture Notes in Logic 10; Cambridge University Press re-issue, 2017. doi:10.1017/9781316716854.
* M. H. Löb. *Solution of a Problem of Leon Henkin.* J. Symb. Log. 20(2):115–118, 1955. doi:10.2307/2266895.
* C. Mummert. Answer 564027 (accepted) to "Impossibility of theories proving consistency of each other?", Mathematics Stack Exchange question 563641, 2013-11-12. https://math.stackexchange.com/questions/563641 (the two-theory argument, informally).
* Mathematics Stack Exchange question 2208419, "Can the 'proves consistent' relation be proven antisymmetric?", 2017-03-29 (accepted answer 2208896). https://math.stackexchange.com/questions/2208419
* R. O'Connor. *Essential Incompleteness of Arithmetic Verified by Coq.* TPHOLs 2005, LNCS 3603, pp. 245–260. doi:10.1007/11541868_16.
* F. Pakhomov, J. Walsh. *Reflection ranks and ordinal analysis.* J. Symb. Log. 86(4):1350–1384, 2021. doi:10.1017/jsl.2020.9.
* L. C. Paulson. *A Mechanised Proof of Gödel's Incompleteness Theorems Using Nominal Isabelle.* J. Autom. Reason. 55(1):1–37, 2015. doi:10.1007/s10817-015-9322-8.
* R. Pollack. *How to believe a machine-checked proof.* In: Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998. doi:10.1093/oso/9780198501275.003.0013. Earlier version: BRICS Report Series 4(18), RS-97-18, 1997. doi:10.7146/brics.v4i18.18945.
* A. Popescu, D. Traytel. *A Formally Verified Abstract Account of Gödel's Incompleteness Theorems.* CADE 27, LNCS 11716, pp. 442–461, 2019. doi:10.1007/978-3-030-29436-6_26.
* A. Popescu, D. Traytel. *Distilling the Requirements of Gödel's Incompleteness Theorems with a Proof Assistant.* J. Autom. Reason. 65(7):1027–1070, 2021. doi:10.1007/s10817-021-09599-8.
* S. Saitou, M. Noguchi. *Mechanizing Gödel's Incompleteness Theorems and Provability Logic.* arXiv:2609.13780, 2026 (Lean 4; repository FormalizedFormalLogic/Foundation; listing checked, content not re-read).
* N. Shankar. *Metamathematics, Machines and Gödel's Proof.* Cambridge University Press, 1994. doi:10.1017/CBO9780511569883.
* C. Smoryński. *Self-Reference and Modal Logic.* Universitext, Springer, 1985. doi:10.1007/978-1-4613-8601-8.
* R. M. Solovay. *Provability interpretations of modal logic.* Israel J. Math. 25(3–4):287–304, 1976. doi:10.1007/BF02757006.
* M. Sozeau, A. Anand, S. Boulier, C. Cohen, Y. Forster, F. Kunze, G. Malecha, N. Tabareau, T. Winterhalter. *The MetaCoq Project.* J. Autom. Reason. 64(5):947–999, 2020. doi:10.1007/s10817-019-09540-0. (Now MetaRocq.)
* M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter. *Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq.* Proc. ACM Program. Lang. 4(POPL), 8:1–8:28, 2020. doi:10.1145/3371076. (Abstract quoted from the Crossref record.)
* K. Thompson. *Reflections on trusting trust.* Commun. ACM 27(8):761–763, 1984. doi:10.1145/358198.358210.
* A. S. Troelstra, H. Schwichtenberg. *Basic Proof Theory*, 2nd ed. Cambridge University Press, 2000. doi:10.1017/CBO9781139168717. (Book level.)
* D. van Dalen. *Logic and Structure.* Universitext, Springer, 2013. doi:10.1007/978-1-4471-4558-5. (Book level.)
* D. A. Wheeler. *Fully Countering Trusting Trust through Diverse Double-Compiling.* PhD thesis, George Mason University, 2009. arXiv:1004.5534.
* F. Wiedijk. *Pollack-inconsistency.* UITP 2010, Electron. Notes Theor. Comput. Sci. 285:85–100, 2012. doi:10.1016/j.entcs.2012.06.008.
* D. E. Willard. *Self-Verifying Axiom Systems, the Incompleteness Theorem and Related Reflection Principles.* J. Symb. Log. 66(2):536–596, 2001. doi:10.2307/2695030.

**Primary sources for the grounding notes** (repository `leanprover/lean4` on GitHub; titles, dates, merge commits and quoted description text read from the GitHub REST API on 2026-11-20):

* Pull request 14807, "fix: make the kernel `is_prop` check require a sort": merged 2026-08-18T01:37:02Z, merge commit `7412bc4c852c9a9fafa69b67a11e4bf9f5dcbc24`. Quoted sentence (from the description's summary paragraph, and repeated later in the description): "The bogus proof was also accepted by nanoda, an independent implementation of the Lean kernel." The summary paragraph continues: "We believe the lean4lean external kernel does not have this bug."
* Pull request 14806, "fix: make kernel `is_def_eq` caching order-independent": merged 2026-08-18T00:42:28Z, merge commit `d108aae3bf7edbaf705b71c01ddb3b264ef72c44`. Quoted: "Both exploits are also caught by nanoda, and both are caught by the new lean-inductive-models developed by Joachim Breitner."
* Issue 14484, "Missing check apparently allows proof of False after adversarial metaprogram": opened 2026-07-22, closed as completed.
* Issue 15100, "leanchecker accepts constructor entries whose map key differs from the embedded name": opened 2026-09-09, closed as completed.
* Issue 15908, "Kernel accepts an axiom-free proof of `False`: native `Nat.add` reduction trusts the constant's name, not its definition": opened 2026-10-24, closed as completed.
* Lean toolchain: tag `v4.34.1` of `leanprover/lean4` resolves to commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub REST API, 2026-11-20).

The DOIs listed as subjects in `REPORT.json` were re-resolved on 2026-11-20 (Crossref; DataCite for the two LIPIcs papers), and Mathematics Stack Exchange questions 563641 and 2208419 (accepted answers 564027 and 2208896) through the Stack Exchange API.

Mathematics Stack Exchange posts have no DOI and no immutable revision identifier. The `REPORT.json` subject for question 563641 is therefore identified only by its URL (with the accepted answer, 564027, named in the subject), and either post may have been edited after the observation date 2026-11-20. Both posts are cited only as informal prior art; no kernel-checked statement depends on their text.

## Revalidation

Requirements: `elan`, which installs the toolchain pinned by `lean/lean-toolchain` (`leanprover/lean4:v4.34.1`), and `python3`; the Lake project has no dependencies. Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` builds a temporary copy of `lean/` with `lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` declarations in the Lean sources, checks with `Lean.collectAxioms` that every declaration of the `KernelTrust` library depends only on `propext`, `Classical.choice` and `Quot.sound`, and recomputes the statement and definition-closure hash (as defined under `## Evidence`) of every name referenced by `results.json` or recorded in `audit/statements.json`, comparing each with the recorded value. Expected output: `ok   lake build`, `ok   axioms (855 declarations)`, `ok   statement hashes (68 hashed names; 0 referenced names exist but carry no recorded hash)` and `REVALIDATED`, with exit status 0. A line `FAIL statement hash <name>` means that the statement of `<name>` or one of the definitions it depends on has changed, so every card citing that name must be re-examined; the script never modifies the package.

For a human-readable axiom listing, run from the package's `lean/` directory:

```sh
lake build                       # expect: Build completed successfully (14 jobs), no warnings
lake env lean AxiomAudit.lean    # prints `#print axioms` for every name referenced by results.json,
                                 # the supporting statements, and every definition example
```

Expected axiom output: every printed declaration depends on at most `propext`, `Classical.choice` and `Quot.sound`, and `Classical.choice` appears only for the four declarations named under `## Evidence`. Any `sorryAx` or `Lean.ofReduceBool` in that output invalidates the package.

A passing build establishes only that the statements type-check and that every example, witness and counterexample is kernel-checked. It does not establish any of the modeling bridges. To re-check a grounding note, re-read the cited pull request or issue at the recorded merge commit or opening date.
