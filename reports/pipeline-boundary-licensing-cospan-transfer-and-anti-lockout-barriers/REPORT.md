# Pipeline Boundary Licensing: Cospan Transfer, Pragmatic Compression, and Anti-Lockout Barriers

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool. Read the non-claims in `## Boundaries` and on each card before applying any result.

- **`single-boundary-transfer-soundness`** (`Toy.BoundaryLicensing.transfer_sound`): For every boundary relation `rel : BoundaryRel`, positive claim shape `sh : PosShape`, negation-free positive propositional state formula `P : Spec`, and Kripke systems `src tgt : Sys`: if `Realizes rel src tgt` holds, then `transfer rel sh (statusOf src sh P)` is below or equal to `statusOf tgt sh P` in the epistemic information order `Status.le`.
- **`five-shape-upper-triangular-separation`** (`Toy.BoundaryLicensing.sepMatrix_upperTriangular`, `Toy.BoundaryLicensing.sepMatrix_subdiagonal_countermodels`, `Toy.BoundaryLicensing.posShape_columns_pairwise_distinct`): Ordering the five boundary relations via `sepRel` (`.litEntails`, `.lockStepSim .s2m`, `.wfStutterSim .s2m`, `.stutterSim .s2m`, `.embed .m2s`) and the five positive claim shapes via `sepShape` (`.hyperGeneral`, `.hyperSubsetClosed`, `.termination`, `.univSafety`, `.existWitness`), every diagonal cell `(i, i)` maps `.supported` to `.supported` under `transfer` and every strict sub-diagonal cell `(i, j)` with `j.1 < i.1` maps `.supported` to `.undetermined` (`sepMatrix_upperTriangular`) and admits a concrete `Realizes (sepRel i) src tgt` Kripke pair flipping `.supported` to `.contradicted` at `specAtom0` (`sepMatrix_subdiagonal_countermodels`); consequently, whenever `sh₁ ≠ sh₂`, some `BoundaryRel` separates `sh₁` and `sh₂` on `.supported` (`posShape_columns_pairwise_distinct`).
- **`undetermined-cell-sharpness`** (`Toy.BoundaryLicensing.transfer_undetermined_sharp`): For every boundary relation `rel : BoundaryRel`, positive shape `sh : PosShape`, positive propositional formula `P : Spec`, and verdict `st : Status`: if `NonDegen sh P` holds, `st.Definite` holds (`st = .supported ∨ st = .contradicted`), and `transfer rel sh st = .undetermined`, then there exist Kripke systems `src₁, tgt₁, src₂, tgt₂ : Sys` realizing `rel` (`Realizes rel src₁ tgt₁` and `Realizes rel src₂ tgt₂`) such that both `src₁` and `src₂` have verdict `st` for `(sh, P)`, `tgt₁` has verdict `.supported`, and `tgt₂` has verdict `.contradicted`.
- **`paired-biconditional-transfer-and-unlicensed-converse`** (`Toy.BoundaryLicensing.transferIff_sound`, `Toy.BoundaryLicensing.transferIff_univSafety_existWitness_supported_iff`, `Toy.BoundaryLicensing.cex_iff_converse_unlicensed`): For every boundary relation `rel : BoundaryRel`, paired directional claim-shape tuple `sh : PosShape × PosShape`, positive formulas `P₁ P₂ : Spec`, and Kripke systems `src tgt : Sys`: if `Realizes rel src tgt` holds, then each component of `transferIff rel sh (statusOf src sh.1 P₁, statusOf src sh.2 P₂)` bounds the corresponding component status of `tgt` under `Status.le` (`transferIff_sound`); `transferIff rel (.univSafety, .existWitness) (.supported, .supported)` equals `(.supported, .supported)` iff `rel` is `.posBoundedMorph .m2s`, `.certFaithfulSoundPinned`, `.termRoundTrip`, or `.litEntails` (`transferIff_univSafety_existWitness_supported_iff`), whereas there exist `src, tgt` realizing `.lockStepSim .s2m` where `src` supports `.univSafety` at `specAtom0` and `.existWitness` at `specAtom1` while `tgt` preserves `.univSafety` at `specAtom0` and falsifies `.existWitness` at that same `specAtom1` (`cex_iff_converse_unlicensed`).
- **`cospan-capture-and-lowering-subset-closed-transfer`** (`Toy.BoundaryLicensing.cospan_subsetClosed_transfer`): Across a universe-polymorphic cospan `a_ir ←(cap ∘ runPasses passes)— a_src —(lower)→ lower a_src` over carrier types `Src : Type u`, `Ir : Type v`, `Exec : Type w`, error type `Err : Type e`, and behavior type `B : Type b` with trace semantics `semS`, `semIr`, and `semExec`: if `cap (runPasses passes a_src) = .ok a_ir`, `LosesNoBehaviourAtInputs semS passes a_src` holds along the pre-capture pass list, `OverApproxOnOk semS semIr cap` holds, `LowerRefinesAt semS semExec lower a_src` holds, `SubsetClosed H` holds, and `H (semIr a_ir)` holds on the captured IR, then `H` holds on both the source artifact `semS a_src` and the lowered executable `semExec (lower a_src)`.
- **`uniform-chain-composition-iff`** (`Toy.BoundaryLicensing.transferChain_eq_iff_forall_realizesChain`): For every finite boundary list `rels : List BoundaryRel`, positive shape `sh : PosShape`, positive formula `P : Spec`, and initial status `st₀ : Status`: if `NonDegen sh P` holds, then `transferChain rels sh st₀ = st₀` holds iff for every pair of Kripke systems `S₀ Sₙ : Sys` connected by `RealizesChain rels S₀ Sₙ` with `statusOf S₀ sh P = st₀`, the final target satisfies `statusOf Sₙ sh P = st₀`.
- **`operational-tcb-warrant-gating-and-bilateral-collapse`** (`Toy.BoundaryLicensing.licensedTransfer_eq_iff_forall_realizesUnderTCB`, `Toy.BoundaryLicensing.unwarranted_collapses_both_statuses`): For every operational warrant boolean `warrantValid : Bool`, boundary chain `rels : List BoundaryRel`, positive shape `sh : PosShape`, positive formula `P : Spec`, and status `st₀ : Status`: if `NonDegen sh P` holds, then `licensedTransfer warrantValid rels sh st₀ = st₀` iff every TCB-conditional realization `RealizesUnderTCB warrantValid rels S₀ Sₙ` starting at `statusOf S₀ sh P = st₀` ends at `statusOf Sₙ sh P = st₀` (`licensedTransfer_eq_iff_forall_realizesUnderTCB`); in particular, when `warrantValid = false` and `NonDegen sh P` holds, `licensedTransfer` equals `.undetermined` for both `.supported` and `.contradicted` and admits opposite-verdict `RealizesUnderTCB false` pairs in both directions (`unwarranted_collapses_both_statuses`).
- **`positive-allowlist-exactness-and-finite-denylist-impossibility`** (`Toy.BoundaryLicensing.allowlistAccepts_iff_onlyDeclaredAxioms`, `Toy.BoundaryLicensing.freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist`, `Toy.BoundaryLicensing.no_finite_denylist_enforces_allowlist`): For every finite declared axiom allowlist `allow : List AxiomId` and used-axiom list `used : List AxiomId` over `AxiomId = Nat`: `allowlistAccepts allow used = true` iff `OnlyDeclaredAxioms allow used` (`allowlistAccepts_iff_onlyDeclaredAxioms`), whereas for every finite denylist `deny : List AxiomId`, the witness `a := freshAxiomOutside allow deny` has `[a]` accepted by `denylistAccepts deny`, rejected by `allowlistAccepts allow`, and outside `OnlyDeclaredAxioms allow` (`freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist`), so no finite denylist `deny` satisfies `∀ used, denylistAccepts deny used = true → OnlyDeclaredAxioms allow used` (`no_finite_denylist_enforces_allowlist`).
- **`certificate-trust-triple-soundness-and-independence`** (`Toy.BoundaryLicensing.cert_trust_triple_sound`): For every universe-polymorphic certificate verifier `V : CertVerifier Stmt Rule Cert`, rule parameter `R : Rule`, shipped statement table `shipped : Nat → Option Stmt`, certificate `c : Cert`, and theorem identifier `name : Nat`: if `CertFaithful V R`, `CertSemSound V R`, `TablePinned V.official shipped name`, and `acceptsNamed V R shipped c name = true` all hold, then there exists `φ : Stmt` such that `V.official name = some φ` and `V.valid φ`.
- **`bare-only-exhaustification-iff-and-neither-nor-safety`** (`Toy.BoundaryLicensing.exhaustifiedOnly_sound_iff_contradictsEv`, `Toy.BoundaryLicensing.neitherNorDisclaimerSafe_iff`, `Toy.BoundaryLicensing.exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`): For every world space `W : Type`, evidence predicate `E : WorldClaim W`, model claim `M : WorldClaim W`, and outside-model claim `S_ext : WorldClaim W`: if `EntailsEv E M` holds, then `EntailsEv E (exhaustifiedOnlyReading M S_ext)` (`∀ w, E w → M w ∧ ¬ S_ext w`) holds iff `ContradictsEv E S_ext` holds (`exhaustifiedOnly_sound_iff_contradictsEv`); `NeitherNorDisclaimerSafe E M S_ext` (`DisclaimerSafe E M S_ext .neitherNor`) holds iff `EntailsEv E M ∧ UndeterminedEv E S_ext` (`neitherNorDisclaimerSafe_iff`); and whenever `EntailsEv E M` and `UndeterminedEv E S_ext` hold, `DisclaimerSafe E M S_ext .bareOnly` and `EntailsEv E (exhaustifiedOnlyReading M S_ext)` fail while `NeitherNorDisclaimerSafe E M S_ext` holds (`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`).
- **`compression-blocker-non-inheritance-and-non-markovian-barrier`** (`Toy.BoundaryLicensing.condPerfection_compression_breaks_minimal_safe_blocker`, `Toy.BoundaryLicensing.scalarExh_compression_breaks_blocker_minimality`, `Toy.BoundaryLicensing.no_stateless_implicature_transfer_for_compression`): Under genuine conclusion-dropping `(H, G₁ ∧ G₂) ↦ (H, G₁)` with no side-channel fields on `SummaryCard`: over `Bool` with `E = True` and `alts = []`, `B = []` is minimal and `ImplicatureSafe` on `fullConjCard` (`H → True ∧ H`) yet fails `ImplicatureSafe` after dropping `G₂` to `compressedG1Card` (`H → True`) (`condPerfection_compression_breaks_minimal_safe_blocker`); dually, over `Fin 3` with fixed `E = fin3Alt12` and fixed alternatives `alts = [fin3Alt02, fin3Alt12]`, `[.scalarExh]` is minimal and safe on `⟨True, (fin3Alt02 ∨ fin3Alt12) ∧ fin3Alt12⟩` yet loses `MinimalSafeBlockers` after dropping `fin3Alt12` because `{fin3Alt02}` and `{fin3Alt12}` clash under `innocentExh` (`scalarExh_compression_breaks_blocker_minimality`); consequently, no stateless function `f : Bool → Bool` computes post-drop `ImplicatureSafe` from pre-drop `ImplicatureSafe` across all conclusion-drops `(H, G₁ ∧ G₂) ↦ (H, G₁)` (`no_stateless_implicature_transfer_for_compression`).
- **`sequent-refutation-context-split-and-dead-branch-vacuity`** (`Toy.BoundaryLicensing.refutation_not_fullPremiseNonVacuous`, `Toy.BoundaryLicensing.cex_global_ctxNonVacuous_dead_right_branch`): For every sequent `sq : Sequent α m k`: if `∀ x, sq.goal x ↔ False` and `sq.Holds` hold, then `sq.FullPremiseNonVacuous` fails (`refutation_not_fullPremiseNonVacuous`), motivating `Sequent.CtxNonVacuous`; however, on `Sum Unit Unit`, the explicit sequent `deadRightBranchSequent` satisfies both `Sequent.Holds` and global `Sequent.CtxNonVacuous` (witnessed at `Sum.inl ()`) while vacuously entailing `False` on every `Sum.inr u`, and is rejected by `Sequent.NonVacuousOnBranches` over `[isLeft, isRight]` (`cex_global_ctxNonVacuous_dead_right_branch`).
- **`finite-suite-allowlist-separation-barrier`** (`Toy.BoundaryLicensing.finite_suite_allowlist_barrier`): For every decidable-equality artifact type `α`, validity predicate `good : α → Prop`, pre-fixed finite suite `F : List α`, law `L : (α → Bool) → Prop`, and checker `c : α → Bool`: if `CheckerSound good c`, `SuiteSoundInvariant good F L`, `L c`, and `∃ p, p ∉ F ∧ c p = true` all hold, then `L (suiteAllowlist F c)` holds even though `suiteAllowlist F c ≠ c`.
- **`extensional-lookup-wrapper-barrier`** (`Toy.BoundaryLicensing.extensional_law_admits_lookupWrapper`): For every decidable-equality type `α`, representation type `Code`, law `L : ImplChecker α Code → Prop`, representations `code₁ code₂ : Code`, checker `c : α → Bool`, and lookup table `table : List (α × Bool)`: if `ImplExtensionalLaw L`, `TableConsistentWith table c`, and `L ⟨code₁, c⟩` hold, then `L ⟨code₂, lookupWrapper table c⟩` holds and `code₁ ≠ code₂` implies `⟨code₂, lookupWrapper table c⟩ ≠ ⟨code₁, c⟩`.
- **`anti-lockout-exactness-and-warn-adjudicate-repair`** (`Toy.BoundaryLicensing.zeroLockout_and_zeroFalseAccept_iff_exact`, `Toy.BoundaryLicensing.blockingGate_locks_out_strict_proxy`, `Toy.BoundaryLicensing.warnAdjudicateGate_zeroLockout_and_sound`): For every artifact type `α`, semantic validity predicate `P : α → Prop`, and boolean check `Q : α → Bool`: `blockingGate Q` achieves both `ZeroLockout P` and `ZeroFalseAccept P` iff `∀ x, Q x = true ↔ P x` (`zeroLockout_and_zeroFalseAccept_iff_exact`); if `P x₀` and `Q x₀ = false` hold for some `x₀ : α`, then `blockingGate Q x₀ = false` and `ZeroLockout P (blockingGate Q)` fails (`blockingGate_locks_out_strict_proxy`), whereas if `ExactAdjudicatorOnWarnings P Q adj` and `ZeroFalseAccept P Q` hold, then `warnAdjudicateGate Q adj` achieves both `ZeroLockout P` and `ZeroFalseAccept P` (`warnAdjudicateGate_zeroLockout_and_sound`).

## Applicability

**Model fidelity.** Model–system relation: none proved. Every structure, transition system, pass pipeline, certificate verifier, summary card, and gate predicate in `Toy.BoundaryLicensing` is a self-contained mathematical definition in Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, core Lean and `Std` only, no Mathlib). These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.

**Relationship among `REPORT.json` subjects.** The pinned `leanprover/lean4` `v4.34.1` toolchain is the verification kernel used to type-check and audit every declaration in `lean/`. The twenty-two literature subjects are the primary mathematical, verification, compiler, security, and linguistics sources whose concepts the formal definitions restate, unify, or contrast; two of those sources (Merz 2012 in the *Archive of Formal Proofs* and Geis & Zwicky 1971 in *Linguistic Inquiry*) have no Crossref DOI and are recorded via their archive entry URL / ISSN and print journal coordinates.

All Lean blocks below are verbatim quotes of the package sources under `lean/Toy/BoundaryLicensing/`, labelled `-- path:line` or `-- path:start-end` relative to the package root.

### Epistemic status, positive claim shapes, and Kripke systems (`Basic.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:8-12
inductive Status where
  | undetermined
  | supported
  | contradicted
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:15-23
def Status.le : Status → Status → Prop
  | .undetermined, _ => True
  | s₁, s₂ => s₁ = s₂

instance (s₁ s₂ : Status) : Decidable (Status.le s₁ s₂) :=
  match s₁, s₂ with
  | .undetermined, _ => isTrue trivial
  | .supported, s₂ => inferInstanceAs (Decidable (Status.supported = s₂))
  | .contradicted, s₂ => inferInstanceAs (Decidable (Status.contradicted = s₂))
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:26-29
def Status.flip : Status → Status
  | .undetermined => .undetermined
  | .supported => .contradicted
  | .contradicted => .supported
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:32-33
def Status.Definite (st : Status) : Prop :=
  st = .supported ∨ st = .contradicted
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:36-39
inductive SimDir where
  | m2s
  | s2m
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:42-48
inductive PosShape where
  | univSafety
  | existWitness
  | termination
  | hyperSubsetClosed
  | hyperGeneral
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:51
abbrev Atom := Nat
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:54
abbrev Valuation := Atom → Bool
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:57
abbrev Trace := Nat → Valuation
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:60-66
structure Sys where
  State : Type
  init : State → Prop
  step : State → State → Prop
  val : State → Valuation
  init_nonempty : ∃ s, init s
  step_total : ∀ s, ∃ s', step s s'
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:69-70
def IsExec (S : Sys) (π : Nat → S.State) : Prop :=
  S.init (π 0) ∧ ∀ n, S.step (π n) (π (n + 1))
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:73-74
def HasTrace (S : Sys) (τ : Trace) : Prop :=
  ∃ π, IsExec S π ∧ ∀ n, τ n = S.val (π n)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:77-83
inductive Spec where
  | top
  | bot
  | atom (a : Atom)
  | conj (φ ψ : Spec)
  | disj (φ ψ : Spec)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:86-91
def evalVal : Spec → Valuation → Bool
  | .top, _ => true
  | .bot, _ => false
  | .atom a, v => v a
  | .conj φ ψ, v => evalVal φ v && evalVal ψ v
  | .disj φ ψ, v => evalVal φ v || evalVal ψ v
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:94-106
def EvalShape : PosShape → Sys → Spec → Prop
  | .univSafety, S, P =>
      ∀ τ, HasTrace S τ → ∀ n, evalVal P (τ n) = true
  | .existWitness, S, P =>
      ∃ τ, HasTrace S τ ∧ ∃ n, evalVal P (τ n) = true
  | .termination, S, P =>
      ∀ τ, HasTrace S τ → ∃ n, evalVal P (τ n) = true
  | .hyperSubsetClosed, S, P =>
      ∀ τ₁ τ₂, HasTrace S τ₁ → HasTrace S τ₂ →
        evalVal P (τ₁ 0) = evalVal P (τ₂ 0) → ∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)
  | .hyperGeneral, S, P =>
      ∀ τ₁, HasTrace S τ₁ → ∃ τ₂, HasTrace S τ₂ ∧
        evalVal P (τ₂ 0) = evalVal P (τ₁ 0) ∧ ∃ n, evalVal P (τ₂ n) ≠ evalVal P (τ₁ n)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:109-111
noncomputable def statusOf (S : Sys) (sh : PosShape) (P : Spec) : Status := by
  letI := Classical.propDecidable (EvalShape sh S P)
  exact if EvalShape sh S P then .supported else .contradicted
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:114-115
def NonDegen (sh : PosShape) (P : Spec) : Prop :=
  (∃ S : Sys, statusOf S sh P = .supported) ∧ (∃ S : Sys, statusOf S sh P = .contradicted)
```

### Pipeline boundary relations, realizations, and directional transfer (`Basic.lean`, `Transfer.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:118-132
inductive BoundaryRel where
  | none
  | hom (d : SimDir)
  | surjHom (d : SimDir)
  | posBoundedMorph (d : SimDir)
  | embed (d : SimDir)
  | traceRefine (d : SimDir)
  | stutterSim (d : SimDir)
  | wfStutterSim (d : SimDir)
  | lockStepSim (d : SimDir)
  | cospanCaptureLower
  | certFaithfulSoundPinned
  | termRoundTrip
  | litEntails
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:135-139
def IsHomFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    (∀ s, A.init s → B.init (h s)) ∧
    (∀ s s', A.step s s' → B.step (h s) (h s')) ∧
    (∀ s a, A.val s a = true → B.val (h s) a = true)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:143-148
def IsSurjHomFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    Function.Surjective h ∧
    (∀ s, A.init s → B.init (h s)) ∧
    (∀ s s', A.step s s' → B.step (h s) (h s')) ∧
    (∀ s a, A.val s a = true → B.val (h s) a = true)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:152-158
def IsPosBoundedMorphFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    (∀ s, A.init s → B.init (h s)) ∧
    (∀ t, B.init t → ∃ s, A.init s ∧ h s = t) ∧
    (∀ s s', A.step s s' → B.step (h s) (h s')) ∧
    (∀ s t', B.step (h s) t' → ∃ s', A.step s s' ∧ h s' = t') ∧
    (∀ s a, A.val s a = true → B.val (h s) a = true)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:161-166
def IsEmbedFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    Function.Injective h ∧
    (∀ s, B.init (h s) ↔ A.init s) ∧
    (∀ s s', B.step (h s) (h s') ↔ A.step s s') ∧
    (∀ s, B.val (h s) = A.val s)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:169-170
def TraceIncl (A B : Sys) : Prop :=
  ∀ τ, HasTrace A τ → HasTrace B τ
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:173-176
inductive PlusMatch {A B : Sys} (R : A.State → B.State → Prop) (s s' : A.State) :
    B.State → Prop where
  | step_done {t t' : B.State} : R s t → B.step t t' → R s' t' → PlusMatch R s s' t
  | step_stut {t u : B.State} : R s t → B.step t u → PlusMatch R s s' u → PlusMatch R s s' t
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:179-183
def StutterSimFrom (A B : Sys) : Prop :=
  ∃ R : A.State → B.State → Prop,
    (∀ s₀, A.init s₀ → ∃ t₀, B.init t₀ ∧ R s₀ t₀) ∧
    (∀ s t, R s t → A.val s = B.val t) ∧
    (∀ s s' t, R s t → A.step s s' → R s' t ∨ PlusMatch R s s' t)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:186-191
def WfStutterSimFrom (A B : Sys) : Prop :=
  ∃ (R : A.State → B.State → Prop) (rank : A.State → B.State → Nat),
    (∀ s₀, A.init s₀ → ∃ t₀, B.init t₀ ∧ R s₀ t₀) ∧
    (∀ s t, R s t → A.val s = B.val t) ∧
    (∀ s s' t, R s t → A.step s s' →
      (R s' t ∧ rank s' t < rank s t) ∨ PlusMatch R s s' t)
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:194-198
def LockStepSimFrom (A B : Sys) : Prop :=
  ∃ R : A.State → B.State → Prop,
    (∀ s₀, A.init s₀ → ∃ t₀, B.init t₀ ∧ R s₀ t₀) ∧
    (∀ s t, R s t → A.val s = B.val t) ∧
    (∀ s s' t, R s t → A.step s s' → ∃ t', B.step t t' ∧ R s' t')
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:201-207
def CospanSysWitness (ir exec : Sys) : Prop :=
  ∃ (s0 : Sys) (pass : Sys → Sys) (cap : Sys → Except Unit Sys) (lower : Sys → Sys),
    cap (pass s0) = .ok ir ∧
    lower s0 = exec ∧
    TraceIncl s0 (pass s0) ∧
    (∀ p q, cap p = .ok q → TraceIncl p q) ∧
    TraceIncl (lower s0) s0
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:211-220
def CertPinnedLink (src tgt : Sys) : Prop :=
  ∃ (Stmt Rule Cert : Type) (V : CertVerifier Stmt Rule Cert) (R : Rule)
    (denote : Stmt → Sys × Sys) (shipped : Nat → Option Stmt) (c : Cert) (name : Nat),
    (∀ φ, V.valid φ ↔
      TraceIncl (denote φ).1 (denote φ).2 ∧ TraceIncl (denote φ).2 (denote φ).1) ∧
    (∃ φ₀, V.official name = some φ₀ ∧ denote φ₀ = (src, tgt)) ∧
    CertFaithful V R ∧
    CertSemSound V R ∧
    TablePinned V.official shipped name ∧
    acceptsNamed V R shipped c name = true
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:224-230
def RoundTripLink (src tgt : Sys) : Prop :=
  ∃ (Dom Syn : Type) (print : Dom → Syn) (elabTerm : Syn → Option Dom)
    (denote : Dom → Sys) (d_src d_tgt : Dom),
    (∀ d : Dom, elabTerm (print d) = some d) ∧
    elabTerm (print d_src) = some d_tgt ∧
    TraceIncl src (denote d_src) ∧ TraceIncl (denote d_src) src ∧
    TraceIncl tgt (denote d_tgt) ∧ TraceIncl (denote d_tgt) tgt
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:233-234
def LitEntailsLink (src tgt : Sys) : Prop :=
  ∀ sh P, EvalShape sh src P → EvalShape sh tgt P
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:237-258
def Realizes : BoundaryRel → Sys → Sys → Prop
  | .none, _, _ => True
  | .hom .m2s, src, tgt => IsHomFrom src tgt
  | .hom .s2m, src, tgt => IsHomFrom tgt src
  | .surjHom .m2s, src, tgt => IsSurjHomFrom src tgt
  | .surjHom .s2m, src, tgt => IsSurjHomFrom tgt src
  | .posBoundedMorph .m2s, src, tgt => IsPosBoundedMorphFrom src tgt
  | .posBoundedMorph .s2m, src, tgt => IsPosBoundedMorphFrom tgt src
  | .embed .m2s, src, tgt => IsEmbedFrom src tgt
  | .embed .s2m, src, tgt => IsEmbedFrom tgt src
  | .traceRefine .m2s, src, tgt => TraceIncl src tgt
  | .traceRefine .s2m, src, tgt => TraceIncl tgt src
  | .stutterSim .m2s, src, tgt => StutterSimFrom src tgt
  | .stutterSim .s2m, src, tgt => StutterSimFrom tgt src
  | .wfStutterSim .m2s, src, tgt => WfStutterSimFrom src tgt
  | .wfStutterSim .s2m, src, tgt => WfStutterSimFrom tgt src
  | .lockStepSim .m2s, src, tgt => LockStepSimFrom src tgt
  | .lockStepSim .s2m, src, tgt => LockStepSimFrom tgt src
  | .cospanCaptureLower, src, tgt => CospanSysWitness src tgt
  | .certFaithfulSoundPinned, src, tgt => CertPinnedLink src tgt
  | .termRoundTrip, src, tgt => RoundTripLink src tgt
  | .litEntails, src, tgt => LitEntailsLink src tgt
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:261-331
def preservesDefinite : BoundaryRel → PosShape → Bool → Bool
  | .none, _, _ => false
  | .hom .m2s, .existWitness, true => true
  | .hom .m2s, _, _ => false
  | .hom .s2m, .existWitness, false => true
  | .hom .s2m, _, _ => false
  | .surjHom .m2s, .existWitness, true => true
  | .surjHom .m2s, _, _ => false
  | .surjHom .s2m, .existWitness, false => true
  | .surjHom .s2m, _, _ => false
  | .posBoundedMorph .m2s, .univSafety, true => true
  | .posBoundedMorph .m2s, .existWitness, true => true
  | .posBoundedMorph .m2s, .termination, true => true
  | .posBoundedMorph .m2s, _, _ => false
  | .posBoundedMorph .s2m, .univSafety, false => true
  | .posBoundedMorph .s2m, .existWitness, false => true
  | .posBoundedMorph .s2m, .termination, false => true
  | .posBoundedMorph .s2m, _, _ => false
  | .embed .m2s, .existWitness, true => true
  | .embed .m2s, .univSafety, false => true
  | .embed .m2s, .termination, false => true
  | .embed .m2s, .hyperSubsetClosed, false => true
  | .embed .m2s, _, _ => false
  | .embed .s2m, .univSafety, true => true
  | .embed .s2m, .existWitness, false => true
  | .embed .s2m, .termination, true => true
  | .embed .s2m, .hyperSubsetClosed, true => true
  | .embed .s2m, _, _ => false
  | .traceRefine .m2s, .existWitness, true => true
  | .traceRefine .m2s, .univSafety, false => true
  | .traceRefine .m2s, .termination, false => true
  | .traceRefine .m2s, .hyperSubsetClosed, false => true
  | .traceRefine .m2s, _, _ => false
  | .traceRefine .s2m, .univSafety, true => true
  | .traceRefine .s2m, .existWitness, false => true
  | .traceRefine .s2m, .termination, true => true
  | .traceRefine .s2m, .hyperSubsetClosed, true => true
  | .traceRefine .s2m, _, _ => false
  | .stutterSim .m2s, .existWitness, true => true
  | .stutterSim .m2s, .univSafety, false => true
  | .stutterSim .m2s, _, _ => false
  | .stutterSim .s2m, .univSafety, true => true
  | .stutterSim .s2m, .existWitness, false => true
  | .stutterSim .s2m, _, _ => false
  | .wfStutterSim .m2s, .existWitness, true => true
  | .wfStutterSim .m2s, .univSafety, false => true
  | .wfStutterSim .m2s, .termination, false => true
  | .wfStutterSim .m2s, _, _ => false
  | .wfStutterSim .s2m, .univSafety, true => true
  | .wfStutterSim .s2m, .existWitness, false => true
  | .wfStutterSim .s2m, .termination, true => true
  | .wfStutterSim .s2m, _, _ => false
  | .lockStepSim .m2s, .existWitness, true => true
  | .lockStepSim .m2s, .univSafety, false => true
  | .lockStepSim .m2s, .termination, false => true
  | .lockStepSim .m2s, .hyperSubsetClosed, false => true
  | .lockStepSim .m2s, _, _ => false
  | .lockStepSim .s2m, .univSafety, true => true
  | .lockStepSim .s2m, .existWitness, false => true
  | .lockStepSim .s2m, .termination, true => true
  | .lockStepSim .s2m, .hyperSubsetClosed, true => true
  | .lockStepSim .s2m, _, _ => false
  | .cospanCaptureLower, .univSafety, true => true
  | .cospanCaptureLower, .existWitness, false => true
  | .cospanCaptureLower, .termination, true => true
  | .cospanCaptureLower, .hyperSubsetClosed, true => true
  | .cospanCaptureLower, _, _ => false
  | .certFaithfulSoundPinned, _, _ => true
  | .termRoundTrip, _, _ => true
  | .litEntails, _, true => true
  | .litEntails, _, false => false
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:334-337
def transfer (rel : BoundaryRel) (sh : PosShape) : Status → Status
  | .undetermined => .undetermined
  | .supported => if preservesDefinite rel sh true then .supported else .undetermined
  | .contradicted => if preservesDefinite rel sh false then .contradicted else .undetermined
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:340-342
def transferIff (rel : BoundaryRel) (sh : PosShape × PosShape) (st : Status × Status) :
    Status × Status :=
  (transfer rel sh.1 st.1, transfer rel sh.2 st.2)
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:615-620
def sepRel : Fin 5 → BoundaryRel
  | ⟨0, _⟩ => .litEntails
  | ⟨1, _⟩ => .lockStepSim .s2m
  | ⟨2, _⟩ => .wfStutterSim .s2m
  | ⟨3, _⟩ => .stutterSim .s2m
  | ⟨4, _⟩ => .embed .m2s
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:623-628
def sepShape : Fin 5 → PosShape
  | ⟨0, _⟩ => .hyperGeneral
  | ⟨1, _⟩ => .hyperSubsetClosed
  | ⟨2, _⟩ => .termination
  | ⟨3, _⟩ => .univSafety
  | ⟨4, _⟩ => .existWitness
```

### Universe-polymorphic three-leg cospan capture and lowering (`Cospan.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:12
abbrev TraceSet (B : Type b) := B → Prop
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:15-16
def TraceSub {B : Type b} (T₁ T₂ : TraceSet B) : Prop :=
  ∀ x, T₁ x → T₂ x
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:19-20
def SubsetClosed {B : Type b} (H : TraceSet B → Prop) : Prop :=
  ∀ T₁ T₂ : TraceSet B, TraceSub T₁ T₂ → H T₂ → H T₁
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:23-24
def runPasses {Src : Type u} (passes : List (Src → Src)) (a : Src) : Src :=
  passes.foldl (fun acc f => f acc) a
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:27-30
def LosesNoBehaviourAtInputs {Src : Type u} {B : Type b} (semS : Src → TraceSet B) :
    List (Src → Src) → Src → Prop
  | [], _ => True
  | f :: fs, a => TraceSub (semS a) (semS (f a)) ∧ LosesNoBehaviourAtInputs semS fs (f a)
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:33-35
def OverApproxOnOk {Src : Type u} {Ir : Type v} {Err : Type e} {B : Type b}
    (semS : Src → TraceSet B) (semIr : Ir → TraceSet B) (cap : Src → Except Err Ir) : Prop :=
  ∀ p q, cap p = .ok q → TraceSub (semS p) (semIr q)
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:38-40
def LowerRefinesAt {Src : Type u} {Exec : Type w} {B : Type b}
    (semS : Src → TraceSet B) (semExec : Exec → TraceSet B) (lower : Src → Exec) (a : Src) : Prop :=
  TraceSub (semExec (lower a)) (semS a)
```

### Heterogeneous boundary chains and TCB warrant gating (`Chain.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:10-13
inductive RealizesChain : List BoundaryRel → Sys → Sys → Prop where
  | nil (S : Sys) : RealizesChain [] S S
  | cons {rel : BoundaryRel} {rels : List BoundaryRel} {S₀ S₁ Sₙ : Sys} :
      Realizes rel S₀ S₁ → RealizesChain rels S₁ Sₙ → RealizesChain (rel :: rels) S₀ Sₙ
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:16-17
def transferChain (rels : List BoundaryRel) (sh : PosShape) (st₀ : Status) : Status :=
  rels.foldl (fun st rel => transfer rel sh st) st₀
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:20-21
def gateWarrant (warrantValid : Bool) (st : Status) : Status :=
  if warrantValid then st else .undetermined
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:24-26
def licensedTransfer (warrantValid : Bool) (rels : List BoundaryRel)
    (sh : PosShape) (st₀ : Status) : Status :=
  gateWarrant warrantValid (transferChain rels sh st₀)
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:29-30
def RealizesUnderTCB (warrantValid : Bool) (rels : List BoundaryRel) (S₀ Sₙ : Sys) : Prop :=
  warrantValid = true → RealizesChain rels S₀ Sₙ
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:33-34
def TraceDeterministic (S : Sys) : Prop :=
  ∀ τ₁ τ₂, HasTrace S τ₁ → HasTrace S τ₂ → τ₁ = τ₂
```

### Axiom allowlisting and polymorphic certificate verifiers (`Trust.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:10
abbrev AxiomId := Nat
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:13-14
def allowlistAccepts (allow : List AxiomId) (used : List AxiomId) : Bool :=
  used.all (fun a => allow.contains a)
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:17-18
def denylistAccepts (deny : List AxiomId) (used : List AxiomId) : Bool :=
  used.all (fun a => !deny.contains a)
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:21-22
def OnlyDeclaredAxioms (allow : List AxiomId) (used : List AxiomId) : Prop :=
  ∀ a ∈ used, a ∈ allow
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:25-26
def freshAxiomOutside (allow deny : List AxiomId) : AxiomId :=
  (allow ++ deny).foldl Nat.max 0 + 1
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:109-113
structure CertVerifier (Stmt : Type u) (Rule : Type v) (Cert : Type w) where
  derivable : Rule → Stmt → Prop
  valid : Stmt → Prop
  check : Rule → Cert → Stmt → Bool
  official : Nat → Option Stmt
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:116-118
def CertFaithful {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) : Prop :=
  ∀ c φ, V.check R c φ = true → V.derivable R φ
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:121-123
def CertSemSound {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) : Prop :=
  ∀ φ, V.derivable R φ → V.valid φ
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:126-127
def TablePinned {Stmt : Type u} (official shipped : Nat → Option Stmt) (name : Nat) : Prop :=
  ∃ φ, official name = some φ ∧ shipped name = some φ
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:130-135
def acceptsNamed {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) (shipped : Nat → Option Stmt)
    (c : Cert) (name : Nat) : Bool :=
  match shipped name with
  | some φ => V.check R c φ
  | none => false
```

### Refutation sequents and branch-partition non-vacuity (`Sequent.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:10-13
structure Sequent (α : Type) (m k : Nat) where
  ctxHyps : Fin m → α → Prop
  badHyps : Fin k → α → Prop
  goal : α → Prop
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:16-17
def AllCtx {α : Type} {m : Nat} (ctxHyps : Fin m → α → Prop) (x : α) : Prop :=
  ∀ i : Fin m, ctxHyps i x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:20-21
def AllBad {α : Type} {k : Nat} (badHyps : Fin k → α → Prop) (x : α) : Prop :=
  ∀ j : Fin k, badHyps j x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:24-25
def Sequent.Holds {α : Type} {m k : Nat} (sq : Sequent α m k) : Prop :=
  ∀ x : α, AllCtx sq.ctxHyps x → AllBad sq.badHyps x → sq.goal x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:28-29
def Sequent.CtxNonVacuous {α : Type} {m k : Nat} (sq : Sequent α m k) : Prop :=
  ∃ x : α, AllCtx sq.ctxHyps x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:32-33
def Sequent.FullPremiseNonVacuous {α : Type} {m k : Nat} (sq : Sequent α m k) : Prop :=
  ∃ x : α, AllCtx sq.ctxHyps x ∧ AllBad sq.badHyps x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:36-38
def Sequent.NonVacuousOnBranches {α : Type} {m k : Nat} (sq : Sequent α m k)
    (branches : List (α → Prop)) : Prop :=
  branches ≠ [] ∧ ∀ b ∈ branches, ∃ x : α, b x ∧ AllCtx sq.ctxHyps x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:41-42
def Sequent.TightCtxAt {α : Type} {m k : Nat} (sq : Sequent α m k) (i : Fin m) : Prop :=
  ∃ x : α, (∀ i' : Fin m, i' ≠ i → sq.ctxHyps i' x) ∧ AllBad sq.badHyps x ∧ ¬ sq.goal x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:45-46
def Sequent.TightBadAt {α : Type} {m k : Nat} (sq : Sequent α m k) (j : Fin k) : Prop :=
  ∃ x : α, AllCtx sq.ctxHyps x ∧ (∀ j' : Fin k, j' ≠ j → sq.badHyps j' x) ∧ ¬ sq.goal x
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:100-103
def deadRightBranchSequent : Sequent (Sum Unit Unit) 1 0 where
  ctxHyps := fun _ x => x.isLeft = true
  badHyps := fun j => Fin.elim0 j
  goal := fun x => x.isRight = true → False
```

### Scope disclaimers, innocent exclusion, and summary compression (`Compression.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:10
abbrev WorldClaim (W : Type) := W → Prop
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:13-14
def EntailsEv {W : Type} (E C : WorldClaim W) : Prop :=
  ∀ w : W, E w → C w
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:17-18
def ContradictsEv {W : Type} (E C : WorldClaim W) : Prop :=
  ∀ w : W, E w → ¬ C w
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:21-22
def UndeterminedEv {W : Type} (E C : WorldClaim W) : Prop :=
  ¬ EntailsEv E C ∧ ¬ ContradictsEv E C
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:25-26
def exhaustifiedOnlyReading {W : Type} (M S_ext : WorldClaim W) : WorldClaim W :=
  fun w => M w ∧ ¬ S_ext w
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:29-33
inductive ScopeDisclaimer where
  | bareOnly
  | unblockedUnshown
  | neitherNor
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:36-39
def DisclaimerLitTrue {W : Type} (E M S_ext : WorldClaim W) : ScopeDisclaimer → Prop
  | .bareOnly => EntailsEv E M ∧ ¬ EntailsEv E S_ext
  | .unblockedUnshown => EntailsEv E M ∧ ¬ EntailsEv E S_ext
  | .neitherNor => EntailsEv E M ∧ ¬ EntailsEv E S_ext ∧ ¬ ContradictsEv E S_ext
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:44-47
def disclaimerReadings {W : Type} (M S_ext : WorldClaim W) : ScopeDisclaimer → List (WorldClaim W)
  | .bareOnly => [M, exhaustifiedOnlyReading M S_ext]
  | .unblockedUnshown => [M, fun w => ¬ S_ext w]
  | .neitherNor => [M]
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:51-52
def DisclaimerSafe {W : Type} (E M S_ext : WorldClaim W) (d : ScopeDisclaimer) : Prop :=
  DisclaimerLitTrue E M S_ext d ∧ ∀ C ∈ disclaimerReadings M S_ext d, EntailsEv E C
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:55-56
def NeitherNorDisclaimerSafe {W : Type} (E M S_ext : WorldClaim W) : Prop :=
  DisclaimerSafe E M S_ext .neitherNor
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:156-159
inductive PragRule where
  | condPerfection
  | scalarExh
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:162-164
structure SummaryCard (W : Type) where
  hyp : WorldClaim W
  concl : WorldClaim W
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:167-168
def SummaryCard.lit {W : Type} (card : SummaryCard W) : WorldClaim W :=
  fun w => card.hyp w → card.concl w
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:172-174
def ConsistentExcl {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W))
    (S : Fin alts.length → Prop) : Prop :=
  ∃ w : W, pre w ∧ ∀ i : Fin alts.length, S i → ¬ alts[i] w
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:177-180
def MaximalConsistentExcl {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W))
    (S : Fin alts.length → Prop) : Prop :=
  ConsistentExcl pre alts S ∧
    ∀ S' : Fin alts.length → Prop, (∀ i, S i → S' i) → ConsistentExcl pre alts S' → ∀ i, S' i → S i
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:184-186
def InnocentlyExcludable {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W))
    (i : Fin alts.length) : Prop :=
  ∀ S : Fin alts.length → Prop, MaximalConsistentExcl pre alts S → S i
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:189-190
def innocentExh {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W)) : WorldClaim W :=
  fun w => pre w ∧ ∀ i : Fin alts.length, InnocentlyExcludable pre alts i → ¬ alts[i] w
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:194-197
def SummaryCard.pragReading {W : Type} (alts : List (WorldClaim W)) (card : SummaryCard W) :
    PragRule → WorldClaim W
  | .condPerfection => fun w => card.concl w → card.hyp w
  | .scalarExh => innocentExh card.lit alts
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:201-203
def ImplicatureSafe {W : Type} (E : WorldClaim W) (alts : List (WorldClaim W))
    (B : List PragRule) (card : SummaryCard W) : Prop :=
  EntailsEv E card.lit ∧ ∀ r : PragRule, r ∉ B → EntailsEv E (card.pragReading alts r)
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:207-210
def MinimalSafeBlockers {W : Type} (E : WorldClaim W) (alts : List (WorldClaim W))
    (B : List PragRule) (card : SummaryCard W) : Prop :=
  B.Nodup ∧ ImplicatureSafe E alts B card ∧
    ∀ r ∈ B, ¬ ImplicatureSafe E alts (B.filter (fun x => x != r)) card
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:213-218
noncomputable def recomputeBlockers {W : Type} (E : WorldClaim W) (alts : List (WorldClaim W))
    (card : SummaryCard W) : List PragRule := by
  letI : DecidablePred (fun r => ¬ EntailsEv E (card.pragReading alts r)) :=
    fun r => Classical.propDecidable _
  exact ([PragRule.condPerfection, PragRule.scalarExh]).filter
    (fun r => decide (¬ EntailsEv E (card.pragReading alts r)))
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:221-223
def fullConjCard : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun b => True ∧ b = true
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:226-228
def compressedG1Card : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun _ => True
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:264
def fin3Alt02 : WorldClaim (Fin 3) := fun w => w.1 ≠ 1
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:267
def fin3Alt12 : WorldClaim (Fin 3) := fun w => w.1 ≠ 0
```

### Finite-suite allowlists, extensional lookup caches, and anti-lockout gates (`Barriers.lean`)

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:12-13
def CheckerSound {α : Type} (good : α → Prop) (c : α → Bool) : Prop :=
  ∀ x : α, c x = true → good x
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:16-17
def suiteAllowlist {α : Type} [DecidableEq α] (F : List α) (c : α → Bool) (x : α) : Bool :=
  decide (x ∈ F) && c x
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:21-26
def SuiteSoundInvariant {α : Type} (good : α → Prop) (F : List α)
    (L : (α → Bool) → Prop) : Prop :=
  ∀ c₁ c₂ : α → Bool,
    (CheckerSound good c₁ ↔ CheckerSound good c₂) →
    (∀ x ∈ F, c₁ x = c₂ x) →
    L c₁ → L c₂
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:156-158
structure ImplChecker (α Code : Type) where
  code : Code
  run : α → Bool
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:161-162
def ImplExtensionalLaw {α Code : Type} (L : ImplChecker α Code → Prop) : Prop :=
  ∀ c₁ c₂ : ImplChecker α Code, (∀ x : α, c₁.run x = c₂.run x) → L c₁ → L c₂
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:165-166
def TableConsistentWith {α : Type} (table : List (α × Bool)) (c : α → Bool) : Prop :=
  ∀ p ∈ table, p.2 = c p.1
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:169-173
def lookupWrapper {α : Type} [DecidableEq α] (table : List (α × Bool))
    (fallback : α → Bool) (x : α) : Bool :=
  match table.find? (fun p => p.1 == x) with
  | some (_, b) => b
  | none => fallback x
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:275-276
def ZeroLockout {α : Type} (P : α → Prop) (accept : α → Bool) : Prop :=
  ∀ x : α, P x → accept x = true
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:279-280
def ZeroFalseAccept {α : Type} (P : α → Prop) (accept : α → Bool) : Prop :=
  ∀ x : α, accept x = true → P x
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:283-284
def blockingGate {α : Type} (Q : α → Bool) (x : α) : Bool :=
  Q x
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:287-288
def warnAdjudicateGate {α : Type} (Q : α → Bool) (adj : α → Bool) (x : α) : Bool :=
  if Q x then true else adj x
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:291-293
def ExactAdjudicatorOnWarnings {α : Type} (P : α → Prop) (Q : α → Bool)
    (adj : α → Bool) : Prop :=
  ∀ x : α, Q x = false → (adj x = true ↔ P x)
```

### Key definitions unfolded (prose)

Unfolded (prose):
- `Status.le s₁ s₂` holds iff `s₁ = .undetermined` or `s₁ = s₂`: `.undetermined` is the bottom element and `.supported`, `.contradicted` are incomparable (`status_le_iff`).
- `statusOf S sh P` is classically two-valued on every Kripke system `S : Sys`: it returns `.supported` iff `EvalShape sh S P` (`statusOf_eq_supported_iff`), returns `.contradicted` iff `¬ EvalShape sh S P` (`statusOf_eq_contradicted_iff`), and never returns `.undetermined` (`statusOf_ne_undetermined`). Because `statusOf S₀ sh P = .undetermined` is unsatisfiable, chain characterizations (`transferChain_eq_iff_forall_realizesChain`, `licensedTransfer_eq_iff_forall_realizesUnderTCB`) hold without a separate `st₀.Definite` premise.
- `Sys` is an initialized total Kripke structure (`init_nonempty` and `step_total`), ensuring every system admits an infinite execution (`hasTrace_nonempty`) and avoiding empty-trace vacuity.
- `Spec` is the inductive syntax of negation-free positive propositional state formulas (`top`, `bot`, `atom`, `conj`, `disj`) evaluated monotonically via `evalVal` (`evalVal_mono`); `NonDegen sh P` holds uniformly across all five `PosShape` values iff `evalVal P valFalse = false` and `evalVal P valTrue = true` (`nonDegen_iff_evalVal_false_true`).
- `EvalShape sh S P` evaluates five positive claim schemas over infinite traces (`HasTrace`): universal state invariants (`∀ τ ∈ S, ∀ n, evalVal P (τ n) = true`), existential reachability (`∃ τ ∈ S, ∃ n, evalVal P (τ n) = true`), eventual visit on total runs (`∀ τ ∈ S, ∃ n, evalVal P (τ n) = true`), all-step 2-safety observational determinism (`∀ τ₁, τ₂ ∈ S, evalVal P (τ₁ 0) = evalVal P (τ₂ 0) → ∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)`), and any-step possibilistic two-trace variation (`∀ τ₁ ∈ S, ∃ τ₂ ∈ S, evalVal P (τ₂ 0) = evalVal P (τ₁ 0) ∧ ∃ n, evalVal P (τ₂ n) ≠ evalVal P (τ₁ n)`).
- `Realizes rel src tgt` pairs `.m2s` (`src → tgt`) and `.s2m` (`tgt → src`) orientations across twenty-one `BoundaryRel` constructors: positive homomorphisms (`IsHomFrom`), plain surjective positive homomorphisms (`IsSurjHomFrom`, no transition back-lifting), positive bounded morphisms / p-morphisms (`IsPosBoundedMorphFrom`, with `init` and `step` back-lifting), induced-substructure embeddings (`IsEmbedFrom`), trace inclusion (`TraceIncl`), unranked and `Nat`-ranked stuttering simulations (`StutterSimFrom`, `WfStutterSimFrom`), lock-step simulations (`LockStepSimFrom`), and four cross-system summary links on `Sys` — `CospanSysWitness` (equivalent to `TraceIncl tgt src` via `cospanSysWitness_iff_traceIncl`), `CertPinnedLink` (backed by a faithful, sound, pinned `CertVerifier` and equivalent to trace equivalence via `certPinnedLink_iff_traceEquiv`), `RoundTripLink` (a left-inverse `print`/`elabTerm` section over trace-equivalent presentations, equivalent to trace equivalence via `roundTripLink_iff_traceEquiv`), and `LitEntailsLink` (direct positive `EvalShape` entailment).

### Definitions

- `Status.le` — characterized: status_le_iff
- `Status.Definite` — tests: status_definite_pos, status_definite_neg — pins down that `.supported` and `.contradicted` are definite while `.undetermined` is not
- `evalVal` — tests: evalVal_pos, evalVal_neg — pins down negation-free positive propositional evaluation (`top`, `bot`, `atom`, `conj`, `disj`) preserving upward valuation monotonicity
- `EvalShape` — tests: evalShape_univSafety_pos, evalShape_univSafety_neg — pins down total-trace evaluation across `.univSafety`, `.existWitness`, `.termination`, all-step `.hyperSubsetClosed`, and any-step `.hyperGeneral`
- `statusOf` — characterized: statusOf_eq_supported_iff
- `NonDegen` — characterized: nonDegen_iff_evalVal_false_true
- `IsSurjHomFrom` — tests: isSurjHomFrom_pos, isSurjHomFrom_neg — pins down plain surjective positive homomorphisms without backward transition lifting
- `IsPosBoundedMorphFrom` — tests: isPosBoundedMorphFrom_pos, isPosBoundedMorphFrom_neg — pins down positive bounded morphisms (p-morphisms) requiring initial-state and step back-lifting
- `CertPinnedLink` — characterized: certPinnedLink_iff_traceEquiv
- `RoundTripLink` — characterized: roundTripLink_iff_traceEquiv
- `CospanSysWitness` — characterized: cospanSysWitness_iff_traceIncl
- `Realizes` — tests: realizes_pos, realizes_neg — pins down that `.hom .m2s` preserves positive atomic truth (`true ↦ true`) while `.embed .m2s` also reflects `false` valuations, with `.surjHom` and `.posBoundedMorph` separated and summary links characterized above
- `transfer` — tests: transfer_pos, transfer_neg — pins down that `.lockStepSim .s2m` preserves `.hyperSubsetClosed` (`.supported`) while returning `.undetermined` on `.hyperGeneral`
- `transferIff` — tests: transferIff_pos, transferIff_neg — pins down independent component-wise transfer across paired directional claim-shape tuples
- `specAtom0` — transparent
- `specAtom1` — transparent
- `sepRel` — tests: sepRel_pos, sepRel_neg — pins down row indexing `0 ↦ .litEntails` and `1 ↦ .lockStepSim .s2m` of the `5 × 5` separation matrix
- `sepShape` — tests: sepShape_pos, sepShape_neg — pins down column indexing `0 ↦ .hyperGeneral` and `1 ↦ .hyperSubsetClosed` matching `sepRel`
- `TraceSub` — tests: traceSub_pos, traceSub_neg — pins down covariant behavior-set inclusion `∀ b, T₁ b → T₂ b`
- `SubsetClosed` — tests: subsetClosed_pos, subsetClosed_neg — pins down downward trace-set closure admitting safety hyperproperties and rejecting two-branch GNI requirements
- `runPasses` — tests: runPasses_pos, runPasses_neg — pins down left-to-right `List.foldl` application order `[f₁, f₂]` (`f₂ (f₁ a)`)
- `LosesNoBehaviourAtInputs` — tests: losesNoBehaviourAtInputs_pos, losesNoBehaviourAtInputs_neg — pins down behavior preservation at each pass's actual intermediate input rather than globally
- `OverApproxOnOk` — tests: overApproxOnOk_pos, overApproxOnOk_neg — pins down `semS p ⊆ semIr q` on `.ok q` while leaving `.error` unconstrained
- `LowerRefinesAt` — tests: lowerRefinesAt_pos, lowerRefinesAt_neg — pins down post-capture trace refinement `semExec (lower a) ⊆ semS a`
- `transferChain` — characterized: transferChain_eq_iff_forall_realizesChain
- `licensedTransfer` — characterized: licensedTransfer_eq_iff_forall_realizesUnderTCB
- `RealizesUnderTCB` — tests: realizesUnderTCB_pos, realizesUnderTCB_neg — pins down conditional obligation `warrantValid = true → RealizesChain rels S₀ Sₙ` (vacuously satisfied when `warrantValid = false`)
- `TraceDeterministic` — tests: traceDeterministic_pos, traceDeterministic_neg — pins down trace uniqueness (`∀ τ₁ τ₂, HasTrace S τ₁ → HasTrace S τ₂ → τ₁ = τ₂`)
- `AxiomId` — transparent
- `allowlistAccepts` — characterized: allowlistAccepts_iff_onlyDeclaredAxioms
- `denylistAccepts` — tests: denylistAccepts_pos, denylistAccepts_neg — pins down fail-open acceptance whenever no used axiom appears in the finite denylist
- `OnlyDeclaredAxioms` — tests: onlyDeclaredAxioms_pos, onlyDeclaredAxioms_neg — pins down subset inclusion `∀ a ∈ used, a ∈ allow`
- `freshAxiomOutside` — tests: freshAxiomOutside_pos, freshAxiomOutside_neg — pins down strict upper-bound witness `max(allow ++ deny) + 1`
- `CertFaithful` — tests: certFaithful_pos, certFaithful_neg — pins down soundness-only derivability (`check = true → derivable`), without completeness
- `CertSemSound` — tests: certSemSound_pos, certSemSound_neg — pins down semantic validity of all `R`-derivable statements
- `TablePinned` — tests: tablePinned_pos, tablePinned_neg — pins down agreement of `official` and `shipped` tables at `some φ` (rejecting `none` and remapped names)
- `acceptsNamed` — tests: acceptsNamed_pos, acceptsNamed_neg — pins down resolving `name` in `shipped` and rejecting missing names (`none ↦ false`)
- `AllCtx` — tests: allCtx_pos, allCtx_neg — pins down universal conjunction across all `Fin m` domain context hypotheses
- `AllBad` — tests: allBad_pos, allBad_neg — pins down universal conjunction across all `Fin k` bad-event premises
- `Sequent.Holds` — tests: sequent_holds_pos, sequent_holds_neg — pins down `AllCtx → AllBad → goal` validity
- `Sequent.CtxNonVacuous` — tests: ctxNonVacuous_pos, ctxNonVacuous_neg — pins down satisfiability of `ctxHyps` alone so `goal = False` refutations remain non-vacuous
- `Sequent.FullPremiseNonVacuous` — tests: fullPremiseNonVacuous_pos, fullPremiseNonVacuous_neg — pins down joint satisfiability of `ctxHyps ∧ badHyps`, which necessarily fails on valid refutations
- `Sequent.NonVacuousOnBranches` — tests: nonVacuousOnBranches_pos, nonVacuousOnBranches_neg — pins down non-empty `branches ≠ []` together with an existential `ctxHyps` witness inside every listed branch predicate
- `deadRightBranchSequent` — transparent
- `EntailsEv` — tests: entailsEv_pos, entailsEv_neg — pins down universal implication `∀ w, E w → C w` across all evidence-compatible worlds
- `ContradictsEv` — tests: contradictsEv_pos, contradictsEv_neg — pins down universal refutation `∀ w, E w → ¬ C w`
- `UndeterminedEv` — tests: undeterminedEv_pos, undeterminedEv_neg — pins down simultaneous absence of entailment and refutation (`¬ EntailsEv ∧ ¬ ContradictsEv`)
- `exhaustifiedOnlyReading` — tests: exhaustifiedOnlyReading_pos, exhaustifiedOnlyReading_neg — pins down conjunction `M w ∧ ¬ S_ext w` negating the outside-model alternative
- `DisclaimerSafe` — tests: disclaimerSafe_pos, disclaimerSafe_neg — pins down meta-epistemic `DisclaimerLitTrue` together with `E`-entailment of every reading in `disclaimerReadings`
- `NeitherNorDisclaimerSafe` — characterized: neitherNorDisclaimerSafe_iff
- `SummaryCard.lit` — transparent
- `innocentExh` — tests: innocentExh_pos, innocentExh_neg — pins down Fox (2007) innocent exclusion negating alternatives belonging to every maximal consistently excludable subset
- `ImplicatureSafe` — tests: implicatureSafe_pos, implicatureSafe_neg — pins down literal entailment together with entailment of every unblocked pragmatic strengthening under `(E, alts)`
- `MinimalSafeBlockers` — tests: minimalSafeBlockers_pos, minimalSafeBlockers_neg — pins down duplicate-free `ImplicatureSafe` blocker lists where deleting any blocker breaks safety
- `fullConjCard` — transparent
- `compressedG1Card` — transparent
- `fin3Alt02` — transparent
- `fin3Alt12` — transparent
- `CheckerSound` — tests: checkerSound_pos, checkerSound_neg — pins down `∀ x, c x = true → good x`
- `suiteAllowlist` — tests: suiteAllowlist_pos, suiteAllowlist_neg — pins down conjunction `decide (x ∈ F) && c x`
- `SuiteSoundInvariant` — tests: suiteSoundInvariant_pos, suiteSoundInvariant_neg — pins down invariance under preserving `CheckerSound` truth and agreement on `F`
- `ImplExtensionalLaw` — tests: implExtensionalLaw_pos, implExtensionalLaw_neg — pins down invariance across distinct `ImplChecker.code` values sharing pointwise-equal `run` functions
- `TableConsistentWith` — tests: tableConsistentWith_pos, tableConsistentWith_neg — pins down agreement `p.2 = c p.1` on every cached `(input, verdict)` pair
- `lookupWrapper` — characterized: lookupWrapper_eq_of_consistent
- `ZeroLockout` — tests: zeroLockout_pos, zeroLockout_neg — pins down completeness on valid artifacts (`∀ x, P x → accept x = true`)
- `ZeroFalseAccept` — tests: zeroFalseAccept_pos, zeroFalseAccept_neg — pins down soundness (`∀ x, accept x = true → P x`)
- `blockingGate` — tests: blockingGate_pos, blockingGate_neg — pins down direct pass-through `Q x`
- `warnAdjudicateGate` — tests: warnAdjudicateGate_pos, warnAdjudicateGate_neg — pins down fast-path acceptance on `Q x = true` and fallback to `adj x` on `Q x = false`
- `ExactAdjudicatorOnWarnings` — tests: exactAdjudicatorOnWarnings_pos, exactAdjudicatorOnWarnings_neg — pins down exactness `adj x = true ↔ P x` required on warned inputs `Q x = false`

### Modeling bridge — `derived (modeling bridge)`

Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool. As a conceptual taxonomy (`derived (modeling bridge)`), the modules correspond to six recurring boundary types in formal-verification pipelines:

1. **Capture and TCB boundary (`Cospan.lean`, `Trust.lean`):** A frontend translates compiler IR after pre-capture passes into a formal IR while a backend lowers source/IR to executable code (`cospan_subsetClosed_transfer`), gated by positive axiom allowlisting (`allowlistAccepts_iff_onlyDeclaredAxioms`).
2. **Model–system boundary (`Basic.lean`, `Transfer.lean`, `Chain.lean`):** An abstract transition model is connected (or unconnected, `BoundaryRel.none`) to an implementation via morphisms, bounded morphisms, or simulations (`transfer_sound`, `transfer_undetermined_sharp`, `transferChain_eq_iff_forall_realizesChain`), subject to operational TCB assumptions (`licensedTransfer_eq_iff_forall_realizesUnderTCB`).
3. **Specification non-vacuity boundary (`Sequent.lean`):** Theorem premises split into domain invariants `ctxHyps` and refuted bad events `badHyps`, with per-branch witness obligations `Sequent.NonVacuousOnBranches` on sum/enum domains.
4. **Certificate checker boundary (`Trust.lean`):** Named theorem verification factors into polymorphic `CertFaithful`, `CertSemSound`, and `TablePinned` (`cert_trust_triple_sound`).
5. **Rendering round-trip and paired-claim boundary (`Basic.lean`, `Transfer.lean`):** Pretty-printed statements preserve verdicts when backed by `RoundTripLink`, whereas paired directional claim tuples (`transferIff_sound`) lose existential witness halves under one-way simulations (`cex_iff_converse_unlicensed`).
6. **Summary compression and gate-wiring boundaries (`Compression.lean`, `Barriers.lean`):** Scope disclaimers under `BoundaryRel.none` avoid bare `"only"` exhaustification (`exhaustifiedOnly_sound_iff_contradictsEv`, `neitherNorDisclaimerSafe_iff`), summary compression recomputes pragmatic blockers under conditional perfection and innocent exclusion (`recomputeBlockers_safe_and_minimal`), and syntactic proxy checks wire as `warnAdjudicateGate` rather than `blockingGate` to preserve `ZeroLockout` (`warnAdjudicateGate_zeroLockout_and_sound`).

## Findings

### `single-boundary-transfer-soundness`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T1 — Preservation of individual formula and temporal classes across homomorphisms, bounded morphisms, simulations, and trace inclusion is classical; unifying all twenty-one directional pipeline boundary relations (separating plain surjective homomorphisms from positive bounded morphisms) and five positive claim shapes over negation-free propositional state formulas into a single decidable epistemic status transformer `transfer` on Kripke structures is parameterized here.
- **Lean:** `Toy.BoundaryLicensing.transfer_sound`
- **Plain claim:** For every boundary relation `rel : BoundaryRel`, positive claim shape `sh : PosShape`, negation-free positive propositional state formula `P : Spec`, and Kripke systems `src tgt : Sys`: if `Realizes rel src tgt` holds, then `transfer rel sh (statusOf src sh P)` is below or equal to `statusOf tgt sh P` in the epistemic information order `Status.le`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:354-356
theorem transfer_sound (rel : BoundaryRel) (sh : PosShape) (P : Spec) (src tgt : Sys)
    (hrel : Realizes rel src tgt) :
    (transfer rel sh (statusOf src sh P)).le (statusOf tgt sh P) := …
```

Unfolded (`transfer_sound`, equivalent via `status_le_iff`):

```lean
transfer rel sh (statusOf src sh P) = Status.undetermined ∨
  transfer rel sh (statusOf src sh P) = statusOf tgt sh P
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hrel : Realizes rel src tgt` | witnesses that the semantic link declared by `rel` actually holds between `src` and `tgt` | tight: counterexample `cex_transfer_sound_without_realizes` (witness class: two 1-state Kripke systems `constSys valTrue` and `constSys valFalse` paired under `.termRoundTrip` at `.univSafety` and `specAtom0`) |

- **Depth:** substantive.
- **Non-vacuity witness:** `nonvacuity_transfer_sound`: `constSys valTrue` realizes `.lockStepSim .s2m` to itself and preserves `.supported` on `.hyperSubsetClosed` at `specAtom0`. (`Toy.BoundaryLicensing.nonvacuity_transfer_sound`).
- **Non-claims:**
  - When `transfer rel sh st = .undetermined`, `Status.le .undetermined (statusOf tgt sh P)` holds trivially without constraining `tgt`'s verdict; completeness of `.undetermined` is established separately in `transfer_undetermined_sharp`.
  - Every `Sys` has a non-empty initial state set (`init_nonempty`) and a total transition relation (`step_total`), ensuring every system admits at least one infinite execution (`hasTrace_nonempty`); systems with empty initial sets or deadlocked finite-only runs are not modeled.
  - `BoundaryRel.surjHom` (`IsSurjHomFrom`) models plain surjective positive homomorphisms without transition back-lifting and preserves `.supported` on `.existWitness` (`isHomFrom_preserves_existWitness`), whereas plain surjective (even bijective, exact-valuation) homomorphisms without step back-lifting fail to preserve `.univSafety` and `.termination` over execution traces (`surjHom_breaks_trace_univSafety_and_termination`); preserving `.univSafety` and `.termination` forward requires `BoundaryRel.posBoundedMorph` (`IsPosBoundedMorphFrom`, a positive bounded morphism / p-morphism with `init` and `step` back-lifting).
  - Inside `Basic.lean`, `CertPinnedLink`, `RoundTripLink`, `LitEntailsLink`, and `CospanSysWitness` summarize cross-system semantic links on `Sys`: `CertPinnedLink` instantiates a `CertFaithful`, `CertSemSound`, `TablePinned` verifier over `Sys` and reduces to trace equivalence (`certPinnedLink_iff_traceEquiv`), `RoundTripLink` requires a left-inverse `print`/`elabTerm` section over trace-equivalent presentations and reduces to trace equivalence (`roundTripLink_iff_traceEquiv`), `LitEntailsLink` assumes positive `EvalShape` entailment (`∀ sh P, EvalShape sh src P → EvalShape sh tgt P`) directly, and `CospanSysWitness ir exec` reduces to `TraceIncl exec ir` (`cospanSysWitness_iff_traceIncl`); concrete polymorphic certificate and cospan hypotheses are analyzed separately in `cert_trust_triple_sound` and `cospan_subsetClosed_transfer`.
  - `Spec` ranges over negation-free positive propositional state formulas (`top`, `bot`, `atom`, `conj`, `disj`) and cannot negate a single atom (`v a = false`); because `IsHomFrom`, `IsSurjHomFrom`, and `IsPosBoundedMorphFrom` preserve only positive truth (`evalVal_mono`), universal absence of a positive bad-event atom (`∀ τ n, v bad = false`) is not preserved forward along `.posBoundedMorph .m2s` or `.surjHom .m2s` (`isPosBoundedMorphFrom_to_constValTrue`, `isSurjHomFrom_to_constValTrue`).
  - `EvalShape` evaluates single representative schemas — state invariants (`∀ τ n, evalVal P (τ n) = true`) for `.univSafety`, eventual formula visit (`∀ τ, ∃ n, evalVal P (τ n) = true`) on total infinite runs for `.termination`, all-step 2-safety observational determinism (`∀ τ₁ τ₂, evalVal P (τ₁ 0) = evalVal P (τ₂ 0) → ∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)`) for `.hyperSubsetClosed`, and any-step two-trace variation (`∀ τ₁, ∃ τ₂, evalVal P (τ₂ 0) = evalVal P (τ₁ 0) ∧ ∃ n, evalVal P (τ₂ n) ≠ evalVal P (τ₁ n)`) for `.hyperGeneral` — rather than arbitrary prefix-closed safety properties, finite-run halting, or arbitrary subset-closed/`∀∃` hyperproperties.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - M. R. Clarkson, F. B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, doi:10.3233/JCS-2009-0393: subset-closed hyperproperties preserved under trace refinement vs. general hyperproperties such as generalized noninterference.
  - K. S. Namjoshi, "A Simple Characterization of Stuttering Bisimulation", FSTTCS 1997, LNCS 1346, pp. 284–296, 1997, doi:10.1007/BFb0058037: well-founded ranking prevents silent divergence under stuttering bisimulation.
  - P. Manolios, "A Compositional Theory of Refinement for Branching Time", CHARME 2003, LNCS 2860, pp. 304–318, 2003, doi:10.1007/978-3-540-39724-3_28 (and UT Austin PhD dissertation, 2001): directed well-founded stuttering simulation/refinement mechanized in ACL2; S. Merz, "Stuttering Equivalence", Archive of Formal Proofs, 2012: Isabelle/HOL mechanization of stuttering equivalence.
  - M. C. Browne, E. M. Clarke, O. Grumberg, "Characterizing Finite Kripke Structures in Propositional Temporal Logic", Theoretical Computer Science 59(1–2):115–131, 1988, doi:10.1016/0304-3975(88)90098-9: stuttering invariance on initialized total Kripke structures.
  - R. C. Lyndon, "Properties Preserved under Homomorphism", Pacific Journal of Mathematics 9(1):143–154, 1959, doi:10.2140/pjm.1959.9.143; P. Blackburn, M. de Rijke, Y. Venema, Modal Logic, Cambridge University Press, 2001, §2.1, doi:10.1017/CBO9781107050884; J. M. Han, F. van Doorn, "A Formal Proof of the Independence of the Continuum Hypothesis", CPP 2020, pp. 353–366, doi:10.1145/3372885.3373826: positive homomorphism preservation, bounded morphisms (p-morphisms), and Lean Mathlib `FirstOrder.Language` homomorphisms/embeddings.
  - C. Abate, R. Blanco, D. Garg, C. Hrițcu, M. Patrignani, J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", IEEE CSF 2019, pp. 256–271, doi:10.1109/CSF.2019.00025 (Coq mechanization); T. Dardinier, P. Müller, "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties", PACMPL 8(PLDI):207, 2024, doi:10.1145/3656437 (Isabelle AFP `HyperHoareLogic`); J. McLean, "A General Theory of Composition for Trace Sets Closed Under Selective Interleaving Functions", IEEE S&P 1994, pp. 79–93, doi:10.1109/RISP.1994.296590: hyperproperty preservation and GNI refinement failure.
  - Reference corpus package `toy-model-transfer-preservation-of-claim-shapes-under-embeddings-homomorphisms-and-simulations`: single-boundary first-order homomorphism, surjective-homomorphism, and embedding preservation.
  - Reference corpus package `refinement-and-hyperproperties-noninterference-and-randomness`: trace-inclusion preservation of subset-closed hyperproperties and failure on generalized noninterference.
  - Reference corpus package `claim-strength-order-quantifier-drift-relativization-and-non-claims`: three-valued epistemic answer space and literal entailment.
  - Reference corpus package `scheduler-adequacy-generated-execution-domains-and-restricted-quantifiers`: full execution-domain quantification (`HasTrace`) vs. restricted generator adequacy.
- **Design question:** Across a multi-boundary formal-verification pipeline (`capture → model → spec → checker → rendering → summary`), which positive and negative claim verdicts are soundly licensed across each boundary relation?

### `five-shape-upper-triangular-separation`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T1 — Individual separations among existential reachability, universal safety, termination under stuttering, synchronous 2-safety, and generalized noninterference are standard; organizing them into an explicit `5 × 5` upper-triangular transfer matrix paired with `Sys` sub-diagonal countermodels and pairwise `PosShape` column distinctness is made precise here.
- **Lean:** `Toy.BoundaryLicensing.sepMatrix_upperTriangular`, `Toy.BoundaryLicensing.sepMatrix_subdiagonal_countermodels`, `Toy.BoundaryLicensing.posShape_columns_pairwise_distinct`
- **Plain claim:** Ordering the five boundary relations via `sepRel` (`.litEntails`, `.lockStepSim .s2m`, `.wfStutterSim .s2m`, `.stutterSim .s2m`, `.embed .m2s`) and the five positive claim shapes via `sepShape` (`.hyperGeneral`, `.hyperSubsetClosed`, `.termination`, `.univSafety`, `.existWitness`), every diagonal cell `(i, i)` maps `.supported` to `.supported` under `transfer` and every strict sub-diagonal cell `(i, j)` with `j.1 < i.1` maps `.supported` to `.undetermined` (`sepMatrix_upperTriangular`) and admits a concrete `Realizes (sepRel i) src tgt` Kripke pair flipping `.supported` to `.contradicted` at `specAtom0` (`sepMatrix_subdiagonal_countermodels`); consequently, whenever `sh₁ ≠ sh₂`, some `BoundaryRel` separates `sh₁` and `sh₂` on `.supported` (`posShape_columns_pairwise_distinct`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:637-639
theorem sepMatrix_upperTriangular :
    (∀ i : Fin 5, transfer (sepRel i) (sepShape i) .supported = .supported) ∧
    (∀ i j : Fin 5, j.1 < i.1 → transfer (sepRel i) (sepShape j) .supported = .undetermined) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1596-1600
theorem sepMatrix_subdiagonal_countermodels (i j : Fin 5) (hlt : j.1 < i.1) :
    ∃ src tgt : Sys,
      Realizes (sepRel i) src tgt ∧
      statusOf src (sepShape j) specAtom0 = .supported ∧
      statusOf tgt (sepShape j) specAtom0 = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:643-644
theorem posShape_columns_pairwise_distinct (sh₁ sh₂ : PosShape) (hne : sh₁ ≠ sh₂) :
    ∃ rel : BoundaryRel, transfer rel sh₁ .supported ≠ transfer rel sh₂ .supported := …
```

Unfolded (`sepMatrix_upperTriangular`):

```lean
(∀ i : Fin 5,
    (if preservesDefinite (sepRel i) (sepShape i) true then Status.supported else Status.undetermined) =
      Status.supported) ∧
  (∀ i j : Fin 5, j.1 < i.1 →
    (if preservesDefinite (sepRel i) (sepShape j) true then Status.supported else Status.undetermined) =
      Status.undetermined)
```

Unfolded (`sepMatrix_subdiagonal_countermodels`):

```lean
∃ src tgt : Sys,
  Realizes (sepRel i) src tgt ∧
  statusOf src (sepShape j) specAtom0 = Status.supported ∧
  statusOf tgt (sepShape j) specAtom0 = Status.contradicted
```

Unfolded (`posShape_columns_pairwise_distinct`):

```lean
∃ rel : BoundaryRel,
  (if preservesDefinite rel sh₁ true then Status.supported else Status.undetermined) ≠
    (if preservesDefinite rel sh₂ true then Status.supported else Status.undetermined)
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hlt : j.1 < i.1` (in `sepMatrix_subdiagonal_countermodels`) | restricts countermodel construction to strict sub-diagonal entries `(i, j)` where `sepRel i` does not preserve `sepShape j` | tight: counterexample `cex_sepMatrix_subdiagonal_without_lt` (witness class: diagonal index `i = j = ⟨0, _⟩` (`.litEntails`, `.hyperGeneral`), where `transfer_sound` preserves `.supported`) |
| `hne : sh₁ ≠ sh₂` (in `posShape_columns_pairwise_distinct`) | excludes identical shapes whose `transfer` column values coincide on every `BoundaryRel` | tight: counterexample `cex_posShape_distinct_without_ne` (witness class: `sh₁ = sh₂ = .univSafety`, where `transfer rel .univSafety .supported` equals itself for all `rel`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_posShape_distinct`: `(⟨1, _⟩ : Fin 5).1 < (⟨2, _⟩ : Fin 5).1` and `.termination ≠ .hyperSubsetClosed`, with `.wfStutterSim .s2m` mapping `.supported` to `.supported` on `.termination` and to `.undetermined` on `.hyperSubsetClosed`. (`Toy.BoundaryLicensing.nonvacuity_posShape_distinct`).
- **Non-claims:**
  - Upper-triangularity holds for the listed row and column orderings `sepRel` and `sepShape` on `.supported`; super-diagonal entries `j > i` are not all `.supported` (for instance, `.lockStepSim .s2m` maps `.existWitness` `.supported` to `.undetermined`).
  - Distinctness of the five `PosShape` columns does not imply that all twenty-one `BoundaryRel` rows are pairwise distinct under `transfer` (for example, `.lockStepSim .s2m`, `.traceRefine .s2m`, `.embed .s2m`, and `.cospanCaptureLower` share the same trace-refinement transfer row) (by inspection of `preservesDefinite`; not proved as a separate theorem here).
  - `transfer (.wfStutterSim .s2m) .hyperSubsetClosed .supported = .undetermined` reflects step-index sensitivity of `EvalShape .hyperSubsetClosed` (`∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)` under synchronous step indexing); stutter-invariant subset-closed hyperproperties are not refuted under well-founded stuttering simulation (not proved here).
  - Row `0` (`.litEntails`) preserves `.hyperGeneral` because `LitEntailsLink` assumes `∀ sh P, EvalShape sh src P → EvalShape sh tgt P` directly by definition, not via a structural morphism on states or transitions.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - M. R. Clarkson, F. B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, doi:10.3233/JCS-2009-0393: separation between 1-safety, liveness, k-safety/subset-closed hyperproperties, and ∀∃ hyperproperties.
  - K. S. Namjoshi, "A Simple Characterization of Stuttering Bisimulation", FSTTCS 1997, LNCS 1346, pp. 284–296, 1997, doi:10.1007/BFb0058037; P. Manolios, "A Compositional Theory of Refinement for Branching Time", CHARME 2003, LNCS 2860, pp. 304–318, 2003, doi:10.1007/978-3-540-39724-3_28; S. Merz, "Stuttering Equivalence", Isabelle AFP, 2012: separation between unranked stuttering and well-founded ranked stuttering on termination/liveness.
  - C. Abate et al., "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", IEEE CSF 2019, pp. 256–271, doi:10.1109/CSF.2019.00025; T. Dardinier, P. Müller, "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties", PACMPL 8(PLDI):207, 2024, doi:10.1145/3656437: mechanized hierarchies separating safety, hyper-safety, and existential hyperproperties.
  - Reference corpus package `simulation-diagrams-and-multi-pass-compiler-correctness`: well-founded forward simulation diagrams.
- **Design question:** Are all five positive claim shapes (`univSafety`, `existWitness`, `termination`, `hyperSubsetClosed`, `hyperGeneral`) irreducibly needed in the boundary transfer table, or do two columns collapse?

### `undetermined-cell-sharpness`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T1 — Countermodels for individual unlicensed cells (such as refinement breaking GNI or unranked stuttering breaking termination) are classical; uniform sharpness across all 210 `(BoundaryRel, PosShape, definite Status)` cells for every non-degenerate negation-free positive formula `P : Spec` is proved here.
- **Lean:** `Toy.BoundaryLicensing.transfer_undetermined_sharp`
- **Plain claim:** For every boundary relation `rel : BoundaryRel`, positive shape `sh : PosShape`, positive propositional formula `P : Spec`, and verdict `st : Status`: if `NonDegen sh P` holds, `st.Definite` holds (`st = .supported ∨ st = .contradicted`), and `transfer rel sh st = .undetermined`, then there exist Kripke systems `src₁, tgt₁, src₂, tgt₂ : Sys` realizing `rel` (`Realizes rel src₁ tgt₁` and `Realizes rel src₂ tgt₂`) such that both `src₁` and `src₂` have verdict `st` for `(sh, P)`, `tgt₁` has verdict `.supported`, and `tgt₂` has verdict `.contradicted`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1626-1634
theorem transfer_undetermined_sharp (rel : BoundaryRel) (sh : PosShape) (P : Spec) (st : Status)
    (hnd : NonDegen sh P) (hdef : st.Definite) (hund : transfer rel sh st = .undetermined) :
    ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
      Realizes rel src₁ tgt₁ ∧
      Realizes rel src₂ tgt₂ ∧
      statusOf src₁ sh P = st ∧
      statusOf src₂ sh P = st ∧
      statusOf tgt₁ sh P = .supported ∧
      statusOf tgt₂ sh P = .contradicted := …
```

Unfolded (`transfer_undetermined_sharp`):

```lean
∃ src₁ tgt₁ src₂ tgt₂ : Sys,
  Realizes rel src₁ tgt₁ ∧
  Realizes rel src₂ tgt₂ ∧
  statusOf src₁ sh P = st ∧
  statusOf src₂ sh P = st ∧
  statusOf tgt₁ sh P = Status.supported ∧
  statusOf tgt₂ sh P = Status.contradicted
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hnd : NonDegen sh P` | ensures `(sh, P)` admits both `.supported` and `.contradicted` Kripke systems (`evalVal P valFalse = false ∧ evalVal P valTrue = true`) rather than a constant tautology or contradiction | tight: counterexample `cex_sharp_without_nonDegen` (witness class: the tautological formula `specConstTrue` at `.none`, `.univSafety`, and `.supported`, where no Kripke system is `.contradicted`) |
| `hdef : st.Definite` | restricts the source verdict `st` to `.supported` or `.contradicted`, since `statusOf` on a Kripke system is two-valued and never equals `.undetermined` | tight: counterexample `cex_sharp_without_definite` (witness class: `st = .undetermined` at `.none`, `.univSafety`, and `specAtom0`, where no `src₁ : Sys` has `statusOf src₁ = .undetermined`) |
| `hund : transfer rel sh st = .undetermined` | excludes preserved cells where `transfer_sound` forces every target `tgt` to share verdict `st` | tight: counterexample `cex_sharp_without_undetermined` (witness class: the sound cell `.lockStepSim .s2m`, `.univSafety`, `.supported` at `specAtom0`, where no realized target can be `.contradicted`) |

- **Depth:** substantive.
- **Non-vacuity witness:** `nonvacuity_transfer_sharp`: `NonDegen .termination specAtom0`, `Status.Definite .supported`, and `transfer (.stutterSim .s2m) .termination .supported = .undetermined`. (`Toy.BoundaryLicensing.nonvacuity_transfer_sharp`).
- **Non-claims:**
  - Sharpness constructs finite Kripke countermodels (`constSys`, `stepSys`, `twoBranchSys`, `threeBranchSys`, `finiteStutterSys`) over `Sys`; restricting `Sys` to a narrower subclass (for example, `TraceDeterministic` systems) can validate additional transfers not licensed in general (`determinizing_stage_breaks_markovian_completeness`).
  - Sharpness of `transfer .litEntails sh .contradicted = .undetermined` relies on `Spec` containing only negation-free positive propositional state formulas (`evalVal_mono`); if `LitEntailsLink` quantified over negation-closed state predicates `Valuation → Bool`, dualizing `p` with `fun v => !p v` would force universal entailment to preserve `.contradicted` on both `.univSafety` and `.existWitness` (`negation_closed_entailment_preserves_contradicted`).
  - For `.hyperSubsetClosed`, `EvalShape` evaluates synchronous all-step 2-safety observational determinism (`evalVal P (τ₁ 0) = evalVal P (τ₂ 0) → ∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)`), which is broken by finite stuttering (`finiteStutterSys`); stutter-invariant subset-closed properties such as `.univSafety` are already covered by the `.univSafety` column.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - M. Abadi, L. Lamport, "The Existence of Refinement Mappings", Theoretical Computer Science 82(2):253–284, 1991, doi:10.1016/0304-3975(91)90224-P: limits of direct refinement mappings without auxiliary history or prophecy state.
  - R. C. Lyndon, "Properties Preserved under Homomorphism", Pacific Journal of Mathematics 9(1):143–154, 1959, doi:10.2140/pjm.1959.9.143; P. Blackburn, M. de Rijke, Y. Venema, Modal Logic, Cambridge University Press, 2001, §2.1, doi:10.1017/CBO9781107050884: why negation-free positive polarity is necessary for homomorphism preservation.
  - M. R. Clarkson, F. B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, doi:10.3233/JCS-2009-0393; J. McLean, "A General Theory of Composition for Trace Sets Closed Under Selective Interleaving Functions", IEEE S&P 1994, pp. 79–93, doi:10.1109/RISP.1994.296590: non-preservation of ∀∃ hyperproperties under trace refinement.
  - P. Manolios, "A Compositional Theory of Refinement for Branching Time", CHARME 2003, LNCS 2860, pp. 304–318, 2003, doi:10.1007/978-3-540-39724-3_28: counterexamples separating unranked stuttering from ranked well-founded stuttering.
  - Reference corpus package `toy-model-transfer-preservation-of-claim-shapes-under-embeddings-homomorphisms-and-simulations`: finite countermodels for unlicensed first-order transfer cells.
- **Design question:** Is any `.undetermined` entry in `transfer` overly conservative over general Kripke structures `Sys` and positive specifications `Spec`, or is every `.undetermined` cell witnessed by concrete models of opposite target truth?

### `paired-biconditional-transfer-and-unlicensed-converse`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T0 — Elementary reference point: `transferIff_sound` is the direct component-wise product of `transfer_sound` across a paired directional claim tuple `(sh.1, sh.2)`, included so asymmetric loss of an existential witness claim alongside a preserved universal safety claim (`cex_iff_converse_unlicensed`, evaluated on the fixed pair `specAtom0` and `specAtom1`) and the exact four-relation preservation list (`transferIff_univSafety_existWitness_supported_iff`) can be cited directly.
- **Lean:** `Toy.BoundaryLicensing.transferIff_sound`, `Toy.BoundaryLicensing.transferIff_univSafety_existWitness_supported_iff`, `Toy.BoundaryLicensing.cex_iff_converse_unlicensed`
- **Plain claim:** For every boundary relation `rel : BoundaryRel`, paired directional claim-shape tuple `sh : PosShape × PosShape`, positive formulas `P₁ P₂ : Spec`, and Kripke systems `src tgt : Sys`: if `Realizes rel src tgt` holds, then each component of `transferIff rel sh (statusOf src sh.1 P₁, statusOf src sh.2 P₂)` bounds the corresponding component status of `tgt` under `Status.le` (`transferIff_sound`); `transferIff rel (.univSafety, .existWitness) (.supported, .supported)` equals `(.supported, .supported)` iff `rel` is `.posBoundedMorph .m2s`, `.certFaithfulSoundPinned`, `.termRoundTrip`, or `.litEntails` (`transferIff_univSafety_existWitness_supported_iff`), whereas there exist `src, tgt` realizing `.lockStepSim .s2m` where `src` supports `.univSafety` at `specAtom0` and `.existWitness` at `specAtom1` while `tgt` preserves `.univSafety` at `specAtom0` and falsifies `.existWitness` at that same `specAtom1` (`cex_iff_converse_unlicensed`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1732-1735
theorem transferIff_sound (rel : BoundaryRel) (sh : PosShape × PosShape) (P₁ P₂ : Spec)
    (src tgt : Sys) (hrel : Realizes rel src tgt) :
    let out := transferIff rel sh (statusOf src sh.1 P₁, statusOf src sh.2 P₂)
    out.1.le (statusOf tgt sh.1 P₁) ∧ out.2.le (statusOf tgt sh.2 P₂) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1751-1755
theorem transferIff_univSafety_existWitness_supported_iff (rel : BoundaryRel) :
    transferIff rel (.univSafety, .existWitness) (.supported, .supported) =
      (.supported, .supported) ↔
      rel = .posBoundedMorph .m2s ∨ rel = .certFaithfulSoundPinned ∨
      rel = .termRoundTrip ∨ rel = .litEntails := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1761-1769
theorem cex_iff_converse_unlicensed :
    ∃ src tgt : Sys,
      Realizes (.lockStepSim .s2m) src tgt ∧
      statusOf src .univSafety specAtom0 = .supported ∧
      statusOf src .existWitness specAtom1 = .supported ∧
      transferIff (.lockStepSim .s2m) (.univSafety, .existWitness) (.supported, .supported) =
        (.supported, .undetermined) ∧
      statusOf tgt .univSafety specAtom0 = .supported ∧
      statusOf tgt .existWitness specAtom1 = .contradicted := …
```

Unfolded (`transferIff_sound`):

```lean
Status.le (transfer rel sh.1 (statusOf src sh.1 P₁)) (statusOf tgt sh.1 P₁) ∧
  Status.le (transfer rel sh.2 (statusOf src sh.2 P₂)) (statusOf tgt sh.2 P₂)
```

Unfolded (`transferIff_univSafety_existWitness_supported_iff`):

```lean
(transfer rel PosShape.univSafety Status.supported, transfer rel PosShape.existWitness Status.supported) =
    (Status.supported, Status.supported) ↔
  rel = BoundaryRel.posBoundedMorph SimDir.m2s ∨ rel = BoundaryRel.certFaithfulSoundPinned ∨
    rel = BoundaryRel.termRoundTrip ∨ rel = BoundaryRel.litEntails
```

Unfolded (`cex_iff_converse_unlicensed`):

```lean
∃ src tgt : Sys,
  Realizes (BoundaryRel.lockStepSim SimDir.s2m) src tgt ∧
  statusOf src PosShape.univSafety specAtom0 = Status.supported ∧
  statusOf src PosShape.existWitness specAtom1 = Status.supported ∧
  transferIff (BoundaryRel.lockStepSim SimDir.s2m) (PosShape.univSafety, PosShape.existWitness)
    (Status.supported, Status.supported) = (Status.supported, Status.undetermined) ∧
  statusOf tgt PosShape.univSafety specAtom0 = Status.supported ∧
  statusOf tgt PosShape.existWitness specAtom1 = Status.contradicted
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hrel : Realizes rel src tgt` (in `transferIff_sound`) | witnesses the boundary relation for both components of the paired directional claim tuple | tight: counterexample `cex_transferIff_sound_without_realizes` (witness class: `constSys valTrue` and `constSys valFalse` without a `RoundTripLink` under `.termRoundTrip` at `(.univSafety, .existWitness)` and `(specAtom0, specAtom1)`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `cex_iff_converse_unlicensed`: a concrete `.lockStepSim .s2m` pair `(src, tgt)` where `src` supports `.univSafety` on `specAtom0` and `.existWitness` on `specAtom1`, while `tgt` preserves `.univSafety` on `specAtom0` and flips `.existWitness` on `specAtom1` from `.supported` to `.contradicted`. (`Toy.BoundaryLicensing.cex_iff_converse_unlicensed`).
- **Non-claims:**
  - `transferIff` tracks two independent unconditional statuses `(statusOf src sh.1 P₁, statusOf src sh.2 P₂)` rather than a single system-level material biconditional `EvalShape sh.1 src P₁ ↔ EvalShape sh.2 src P₂`: if both halves are false on `src` (`False ↔ False`), a `.lockStepSim .s2m` refinement can still make `.univSafety` true while leaving `.existWitness` false (`True ↔ False`), whereas a state-level invariant biconditional decomposes into two `.univSafety` claims that both survive `.lockStepSim .s2m` (not proved here).
  - The four `BoundaryRel` constructors preserving `(.supported, .supported)` on `(.univSafety, .existWitness)` are `.posBoundedMorph .m2s`, `.certFaithfulSoundPinned`, `.termRoundTrip`, and `.litEntails` (`transferIff_univSafety_existWitness_supported_iff`); `.posBoundedMorph .m2s` and `.litEntails` are one-directional positive links rather than symmetric equivalences.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - Reference corpus package `printing-elaboration-round-trips-coercions-and-statement-certificates`: round-trip equivalence preserving full statement meaning across rendering and elaboration.
  - Reference corpus package `claim-strength-order-quantifier-drift-relativization-and-non-claims`: directional entailment vs. equivalence.
- **Design question:** When a specification pairs a universal safety claim with an existential witness claim as a directional tuple, which components survive across a one-directional simulation and which boundary relations preserve `.supported` on both?

### `cospan-capture-and-lowering-subset-closed-transfer`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T1 — Pre-capture fail-closed over-approximation (`fail-closed-ir-capture-...`) and subset-closed trace-refinement contravariance (`refinement-and-hyperproperties-...`) were previously established on separate legs; composing pre-capture pass chains, partial `Except` capture, and post-capture lowering across universe-independent `Src`, `Ir`, and `Exec` carrier types into one cospan transfer lemma is packaged here.
- **Lean:** `Toy.BoundaryLicensing.cospan_subsetClosed_transfer`
- **Plain claim:** Across a universe-polymorphic cospan `a_ir ←(cap ∘ runPasses passes)— a_src —(lower)→ lower a_src` over carrier types `Src : Type u`, `Ir : Type v`, `Exec : Type w`, error type `Err : Type e`, and behavior type `B : Type b` with trace semantics `semS`, `semIr`, and `semExec`: if `cap (runPasses passes a_src) = .ok a_ir`, `LosesNoBehaviourAtInputs semS passes a_src` holds along the pre-capture pass list, `OverApproxOnOk semS semIr cap` holds, `LowerRefinesAt semS semExec lower a_src` holds, `SubsetClosed H` holds, and `H (semIr a_ir)` holds on the captured IR, then `H` holds on both the source artifact `semS a_src` and the lowered executable `semExec (lower a_src)`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:63-74
theorem cospan_subsetClosed_transfer
    {Src : Type u} {Ir : Type v} {Exec : Type w} {Err : Type e} {B : Type b}
    (semS : Src → TraceSet B) (semIr : Ir → TraceSet B) (semExec : Exec → TraceSet B)
    (passes : List (Src → Src)) (cap : Src → Except Err Ir) (lower : Src → Exec)
    (a_src : Src) (a_ir : Ir) (H : TraceSet B → Prop)
    (hok : cap (runPasses passes a_src) = .ok a_ir)
    (hpass : LosesNoBehaviourAtInputs semS passes a_src)
    (hcap : OverApproxOnOk semS semIr cap)
    (hlow : LowerRefinesAt semS semExec lower a_src)
    (hsub : SubsetClosed H)
    (hir : H (semIr a_ir)) :
    H (semS a_src) ∧ H (semExec (lower a_src)) := …
```

Unfolded (`cospan_subsetClosed_transfer`):

```lean
H (semS a_src) ∧ H (semExec (lower a_src))
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hok : cap (runPasses passes a_src) = .ok a_ir` | ties the verified IR artifact `a_ir` to the successful capture of `runPasses passes a_src` | tight: counterexample `cex_cospan_without_capture_ok` (witness class: there is a fail-closed capture returning `.error ()` on `a_src = 2` while an unrelated `a_ir = 0` satisfies `allSafeH`) |
| `hpass : LosesNoBehaviourAtInputs semS passes a_src` | prevents pre-capture compiler passes from erasing source behaviors that `lower a_src` still exhibits | tight: counterexample `cex_cospan_without_prepass_no_loss` (witness class: there is a single-pass pre-capture pipeline `[fun _ => 0]` erasing `true` from `bitSem 2` while `lower = id`) |
| `hcap : OverApproxOnOk semS semIr cap` | ensures `.ok` capture loses no behavior present after the pre-capture passes | tight: counterexample `cex_cospan_without_overApproxOnOk` (witness class: there is an under-approximating capture `fun _ => .ok 0` on `a_src = 2` with `passes = []` and `lower = id`) |
| `hlow : LowerRefinesAt semS semExec lower a_src` | ensures post-capture backend lowering introduces no new behavior absent from `semS a_src` | tight: counterexample `cex_cospan_without_lowerRefines` (witness class: there is a post-capture lowering `fun _ => 1` introducing behavior `true` absent from `a_src = 0`) |
| `hsub : SubsetClosed H` | allows `H` to transfer contravariantly along `semExec (lower a_src) ⊆ semS a_src ⊆ semIr a_ir` | tight: counterexample `cex_cospan_without_subsetClosed` (witness class: the two-branch GNI-like hyperproperty `bothBranchesH` when `lower` refines `{false, true}` (`2`) to `{false}` (`0`)) |
| `hir : H (semIr a_ir)` | supplies the verified hyperproperty on the captured IR artifact | tight: counterexample `cex_cospan_without_ir_holds` (witness class: identity passes, capture, and lowering on `1`, where `allSafeH (bitSem 1)` fails) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_cospan_transfer`: cross-universe cospan (`Src = Nat : Type 0`, `Ir = Sys : Type 1`, `Exec = Bool : Type 0`) with pre-capture pass `[fun n => n + 1]`, partial capture (`cap 1 = .ok a_ir`, `cap 2 = .error ()`), and strict behavioral refinement (`¬ TraceSub (semS 0) (semExec (lower 0))`). (`Toy.BoundaryLicensing.nonvacuity_cospan_transfer`).
- **Non-claims:**
  - When `lower` runs on `runPasses passes a_src` rather than `a_src` (sharing pre-capture passes with the backend), undefined-behavior-erasing passes still require source-to-pass trace inclusion (`semS a ⊆ semS (f a)`, i.e., pass over-approximation rather than undefined-behavior-erasing pass refinement `semS (f a) ⊆ semS a`) if the claim is stated about `a_src`, whereas claims scoped to `runPasses passes a_src` drop `hpass` (not proved here; see `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`).
  - `LowerRefinesAt` assumes unconditional trace inclusion `TraceSub (semExec (lower a_src)) (semS a_src)` at `a_src`. For compilers whose backend refinement holds only when `a_src` has no undefined behavior, `cospan_subsetClosed_transfer` applies only when `semS` models undefined behavior chaotically (admitting all traces) or when undefined-behavior freedom of `a_src` is independently established from `H (semIr a_ir)` and `semS a_src ⊆ semIr a_ir` (not proved here; see `simulation-diagrams-and-multi-pass-compiler-correctness` and `law-dependent-rewrites-after-capture-safe-vs-unsafe-trait-laws-and-relational-semantics`).
  - `semS`, `semIr`, and `semExec` share a common trace type `B`; cross-language trace abstraction or observation maps between IR events and machine events are not modeled.
  - Existential witness properties and general ∀∃ hyperproperties (`bothBranchesH`) do not transfer across `cospan_subsetClosed_transfer` (`cex_cospan_without_subsetClosed`).
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4: backward behavior refinement across compiler lowering conditioned on source safety.
  - A. W. Appel, "Verified Software Toolchain", ESOP 2011, LNCS 6602, pp. 1–17, 2011, doi:10.1007/978-3-642-19718-5_1: composing front-end IR program verification with CompCert backend lowering in Coq.
  - M. R. Clarkson, F. B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, doi:10.3233/JCS-2009-0393; C. Abate et al., "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", IEEE CSF 2019, pp. 256–271, doi:10.1109/CSF.2019.00025: preservation of subset-closed hyperproperties under trace inclusion.
  - Reference corpus package `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`: `OverApproxOnOk` and `LosesNoBehaviourAtInputs` on pre-capture compiler pipelines.
  - Reference corpus package `simulation-diagrams-and-multi-pass-compiler-correctness`: conditional backward trace inclusion under `NeverGoesWrong`.
  - Reference corpus package `law-dependent-rewrites-after-capture-safe-vs-unsafe-trait-laws-and-relational-semantics`: post-capture codegen rewrites relative to captured IR.
- **Design question:** How do pre-capture IR passes (which may erase behaviors), fail-closed partial IR capture, and post-capture backend lowering compose as a cospan to transfer properties from verified IR to compiled executables?

### `uniform-chain-composition-iff`

Basis: `execution (Lean kernel check)`

- **Kind:** characterization. **Tier:** T1 — Composing individual simulation links by transitivity is standard; proving that the folded decidable status transformer `transferChain` is both sound and complete (`↔`) with respect to universal preservation over all unconstrained `n`-step `RealizesChain` realizations on `Sys` is established here.
- **Lean:** `Toy.BoundaryLicensing.transferChain_eq_iff_forall_realizesChain`
- **Plain claim:** For every finite boundary list `rels : List BoundaryRel`, positive shape `sh : PosShape`, positive formula `P : Spec`, and initial status `st₀ : Status`: if `NonDegen sh P` holds, then `transferChain rels sh st₀ = st₀` holds iff for every pair of Kripke systems `S₀ Sₙ : Sys` connected by `RealizesChain rels S₀ Sₙ` with `statusOf S₀ sh P = st₀`, the final target satisfies `statusOf Sₙ sh P = st₀`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:109-113
theorem transferChain_eq_iff_forall_realizesChain (rels : List BoundaryRel) (sh : PosShape)
    (P : Spec) (st₀ : Status) (hnd : NonDegen sh P) :
    transferChain rels sh st₀ = st₀ ↔
      ∀ S₀ Sₙ : Sys, RealizesChain rels S₀ Sₙ →
        statusOf S₀ sh P = st₀ → statusOf Sₙ sh P = st₀ := …
```

Unfolded (`transferChain_eq_iff_forall_realizesChain`):

```lean
List.foldl (fun st rel => transfer rel sh st) st₀ rels = st₀ ↔
  ∀ S₀ Sₙ : Sys, RealizesChain rels S₀ Sₙ →
    statusOf S₀ sh P = st₀ → statusOf Sₙ sh P = st₀
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hnd : NonDegen sh P` | rules out degenerate formulas (`specConstTrue`, `specConstFalse`) where every Kripke system shares a fixed verdict even across `.none` | tight: counterexample `cex_transferChain_iff_without_nonDegen` (witness class: `rels = [.none]`, `sh = .univSafety`, `P = specConstTrue`, `st₀ = .supported`) |

- **Depth:** substantive.
- **Non-vacuity witness:** `nonvacuity_transferChain`: explicit 3-step `RealizesChain` along `[.cospanCaptureLower, .lockStepSim .s2m, .litEntails]` from `twoBranchSys` (`S₀`) to `oneBranchSys` (`S₃`) with `¬ TraceIncl S₀ S₃`, preserving `.supported` on `.hyperSubsetClosed` at `specAtom0`. (`Toy.BoundaryLicensing.nonvacuity_transferChain`).
- **Non-claims:**
  - At `st₀ = .undetermined`, both sides of the biconditional hold trivially (`transferChain` returns `.undetermined`, and `statusOf S₀ sh P = .undetermined` is vacuously false because `statusOf` on `Sys` is two-valued via `statusOf_ne_undetermined`).
  - Coincidental agreement on a single concrete realization chain (`S₀, …, Sₙ`) does not license the boundary list `rels` (`cex_coincidental_truth_on_unlicensed_chain`).
  - Completeness (`←`) of `transferChain` relies on intermediate stages ranging over arbitrary nondeterministic Kripke structures `Sys` (`realizes_refl`); restricting an intermediate stage's codomain to `TraceDeterministic` systems allows `.traceRefine .s2m` to preserve `.existWitness` `.supported` even though `transfer (.traceRefine .s2m) .existWitness .supported = .undetermined` (`determinizing_stage_breaks_markovian_completeness`).
  - `RealizesChain rels S₀ Sₙ` quantifies over unconstrained intermediate systems `S₁, …, Sₙ₋₁ : Sys`; pipelines whose stages satisfy a coupled joint invariant (for example, an `.embed .m2s` instrumentation pass followed by its paired state-erasing retraction) can preserve claims even when link-by-link `transferChain` returns `.undetermined` (not proved here).
  - `transferChain` tracks preservation of a fixed `(sh, P)` and verdict `st₀` across `Sys` (where `Spec` is negation-free and `EvalShape` evaluates fixed representative schemas); negation or complementation steps (such as reducing validity of `φ` to unsatisfiability of `¬φ`) and non-Markovian pragmatic effects (`no_stateless_implicature_transfer_for_compression`) are not represented in `BoundaryRel`.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - Reference corpus package `simulation-diagrams-and-multi-pass-compiler-correctness`: multi-step composition of homogeneous well-founded forward simulations.
  - Reference corpus package `toy-model-transfer-preservation-of-claim-shapes-under-embeddings-homomorphisms-and-simulations`: single-step soundness and sharpness for model-theoretic maps.
- **Design question:** Across an `n`-step heterogeneous verification pipeline `[rel₁, …, relₙ]` over unconstrained intermediate systems, does folding single-boundary `transfer` lose precision, or is `transferChain rels sh st₀ = st₀` exact for universal preservation across all realizations?

### `operational-tcb-warrant-gating-and-bilateral-collapse`

Basis: `execution (Lean kernel check)`

- **Kind:** characterization. **Tier:** T1 — That violating TCB assumptions invalidates positive guarantees is standard; formalizing global TCB warrant as conditional realization `warrantValid = true → RealizesChain rels S₀ Sₙ` makes precise when `warrantValid = false` symmetrically invalidates `.contradicted` refutations as well (and clarifies where directional replay escapes bilateral collapse).
- **Lean:** `Toy.BoundaryLicensing.licensedTransfer_eq_iff_forall_realizesUnderTCB`, `Toy.BoundaryLicensing.unwarranted_collapses_both_statuses`
- **Plain claim:** For every operational warrant boolean `warrantValid : Bool`, boundary chain `rels : List BoundaryRel`, positive shape `sh : PosShape`, positive formula `P : Spec`, and status `st₀ : Status`: if `NonDegen sh P` holds, then `licensedTransfer warrantValid rels sh st₀ = st₀` iff every TCB-conditional realization `RealizesUnderTCB warrantValid rels S₀ Sₙ` starting at `statusOf S₀ sh P = st₀` ends at `statusOf Sₙ sh P = st₀` (`licensedTransfer_eq_iff_forall_realizesUnderTCB`); in particular, when `warrantValid = false` and `NonDegen sh P` holds, `licensedTransfer` equals `.undetermined` for both `.supported` and `.contradicted` and admits opposite-verdict `RealizesUnderTCB false` pairs in both directions (`unwarranted_collapses_both_statuses`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:212-216
theorem licensedTransfer_eq_iff_forall_realizesUnderTCB (warrantValid : Bool)
    (rels : List BoundaryRel) (sh : PosShape) (P : Spec) (st₀ : Status) (hnd : NonDegen sh P) :
    licensedTransfer warrantValid rels sh st₀ = st₀ ↔
      ∀ S₀ Sₙ : Sys, RealizesUnderTCB warrantValid rels S₀ Sₙ →
        statusOf S₀ sh P = st₀ → statusOf Sₙ sh P = st₀ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:255-262
theorem unwarranted_collapses_both_statuses (rels : List BoundaryRel) (sh : PosShape)
    (P : Spec) (hnd : NonDegen sh P) :
    licensedTransfer false rels sh .supported = .undetermined ∧
    licensedTransfer false rels sh .contradicted = .undetermined ∧
    (∃ S₀ Sₙ : Sys, RealizesUnderTCB false rels S₀ Sₙ ∧
      statusOf S₀ sh P = .supported ∧ statusOf Sₙ sh P = .contradicted) ∧
    (∃ S₀ Sₙ : Sys, RealizesUnderTCB false rels S₀ Sₙ ∧
      statusOf S₀ sh P = .contradicted ∧ statusOf Sₙ sh P = .supported) := …
```

Unfolded (`licensedTransfer_eq_iff_forall_realizesUnderTCB`):

```lean
(if warrantValid then List.foldl (fun st rel => transfer rel sh st) st₀ rels else Status.undetermined) = st₀ ↔
  ∀ S₀ Sₙ : Sys, (warrantValid = true → RealizesChain rels S₀ Sₙ) →
    statusOf S₀ sh P = st₀ → statusOf Sₙ sh P = st₀
```

Unfolded (`unwarranted_collapses_both_statuses`):

```lean
licensedTransfer false rels sh Status.supported = Status.undetermined ∧
  licensedTransfer false rels sh Status.contradicted = Status.undetermined ∧
  (∃ S₀ Sₙ : Sys, (false = true → RealizesChain rels S₀ Sₙ) ∧
    statusOf S₀ sh P = Status.supported ∧ statusOf Sₙ sh P = Status.contradicted) ∧
  (∃ S₀ Sₙ : Sys, (false = true → RealizesChain rels S₀ Sₙ) ∧
    statusOf S₀ sh P = Status.contradicted ∧ statusOf Sₙ sh P = Status.supported)
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hnd : NonDegen sh P` (in `licensedTransfer_eq_iff_forall_realizesUnderTCB`, `unwarranted_collapses_both_statuses`) | ensures opposite-verdict target systems exist when `warrantValid = false` leaves `RealizesUnderTCB` unconstrained | tight: counterexample `cex_licensedTransfer_iff_without_nonDegen`, `cex_unwarranted_collapse_without_nonDegen` (witness class: `specConstTrue` at `.univSafety`, `.supported`, and `warrantValid = false`, where every `Sₙ` has verdict `.supported` even under unconstrained `RealizesUnderTCB false`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_licensedTransfer`: `warrantValid = true` on `[.cospanCaptureLower, .lockStepSim .s2m, .litEntails]` from `twoBranchSys` to `oneBranchSys` preserves `.supported` for `.hyperSubsetClosed` at `specAtom0`, while `warrantValid = false` collapses to `.undetermined`. (`Toy.BoundaryLicensing.nonvacuity_licensedTransfer`).
- **Non-claims:**
  - `warrantValid` is modeled as a global boolean summary of whether external TCB assumptions hold; how operational evidence establishes `warrantValid = true` (hardware, OS, compiler binary integrity) lies outside the formal model.
  - Bilateral collapse under `warrantValid = false` (`unwarranted_collapses_both_statuses`) holds because `RealizesUnderTCB false rels S₀ Sₙ` (`false = true → RealizesChain rels S₀ Sₙ`) leaves `S₀` and `Sₙ` completely unrelated; when a partial TCB degradation breaks `.s2m` over-approximation while `.m2s` concrete execution under-approximation (`Realizes (.traceRefine .m2s) S₀ Sₙ`) remains valid, `.supported` on `.univSafety` collapses to `.undetermined` while `.contradicted` remains licensed (`transfer_sound`).
  - At `st₀ = .undetermined`, both sides of `licensedTransfer_eq_iff_forall_realizesUnderTCB` hold trivially even at `warrantValid = false` (`unwarranted_undetermined_vacuous_agreement`), because `licensedTransfer` returns `.undetermined` and `statusOf S₀ sh P = .undetermined` is vacuously false (`statusOf_ne_undetermined`).
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - R. Pollack, "How to Believe a Machine-Checked Proof", in Twenty-Five Years of Constructive Type Theory (G. Sambin, J. M. Smith, eds.), Oxford University Press, pp. 205–220, 1998: separation between formal kernel derivability and operational/specification trust assumptions.
  - Reference corpus package `proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`: explicit TCB assumptions for proof checkers.
- **Design question:** When an operational TCB assumption fails globally (`warrantValid = false`, with no remaining directional replay link), does a tool's negative refutation (`.contradicted`) survive even though its positive proof (`.supported`) fails, or do both verdicts collapse to `.undetermined`?

### `positive-allowlist-exactness-and-finite-denylist-impossibility`

Basis: `execution (Lean kernel check)`

- **Kind:** impossibility. **Tier:** T0 — Re-derivation of fail-safe positive allowlisting vs. finite exclusion denylisting over an infinite identifier domain (Saltzer & Schroeder 1975), packaged with the explicit `freshAxiomOutside` witness and finite closed-universe complement positive control.
- **Lean:** `Toy.BoundaryLicensing.allowlistAccepts_iff_onlyDeclaredAxioms`, `Toy.BoundaryLicensing.freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist`, `Toy.BoundaryLicensing.no_finite_denylist_enforces_allowlist`
- **Plain claim:** For every finite declared axiom allowlist `allow : List AxiomId` and used-axiom list `used : List AxiomId` over `AxiomId = Nat`: `allowlistAccepts allow used = true` iff `OnlyDeclaredAxioms allow used` (`allowlistAccepts_iff_onlyDeclaredAxioms`), whereas for every finite denylist `deny : List AxiomId`, the witness `a := freshAxiomOutside allow deny` has `[a]` accepted by `denylistAccepts deny`, rejected by `allowlistAccepts allow`, and outside `OnlyDeclaredAxioms allow` (`freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist`), so no finite denylist `deny` satisfies `∀ used, denylistAccepts deny used = true → OnlyDeclaredAxioms allow used` (`no_finite_denylist_enforces_allowlist`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:59-60
theorem allowlistAccepts_iff_onlyDeclaredAxioms (allow used : List AxiomId) :
    allowlistAccepts allow used = true ↔ OnlyDeclaredAxioms allow used := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:66-71
theorem freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist
    (allow deny : List AxiomId) :
    let a := freshAxiomOutside allow deny
    ¬ OnlyDeclaredAxioms allow [a] ∧
    allowlistAccepts allow [a] = false ∧
    denylistAccepts deny [a] = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:84-86
theorem no_finite_denylist_enforces_allowlist (allow : List AxiomId) :
    ¬ ∃ deny : List AxiomId, ∀ used : List AxiomId,
        denylistAccepts deny used = true → OnlyDeclaredAxioms allow used := …
```

Unfolded (`allowlistAccepts_iff_onlyDeclaredAxioms`):

```lean
used.all (fun a => allow.contains a) = true ↔ ∀ a ∈ used, a ∈ allow
```

Unfolded (`freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist`):

```lean
¬ OnlyDeclaredAxioms allow [freshAxiomOutside allow deny] ∧
  allowlistAccepts allow [freshAxiomOutside allow deny] = false ∧
  denylistAccepts deny [freshAxiomOutside allow deny] = true
```

Unfolded (`no_finite_denylist_enforces_allowlist`):

```lean
¬ ∃ deny : List Nat, ∀ used : List Nat,
    used.all (fun a => !deny.contains a) = true → ∀ a ∈ used, a ∈ allow
```

Hypothesis ledger: no hypotheses beyond the universally quantified parameters.

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_allowlist_vs_denylist`: `allowlistAccepts [0, 1] [1, 0] = true` and `OnlyDeclaredAxioms [0, 1] [1, 0]` hold, while `freshAxiomOutside [1, 4] [2] = 5` satisfies `5 ∉ [1, 4]`, `5 ∉ [2]`, `denylistAccepts [2] [5] = true`, and `allowlistAccepts [1, 4] [5] = false`. (`Toy.BoundaryLicensing.nonvacuity_allowlist_vs_denylist`).
- **Positive control:** `Toy.BoundaryLicensing.denylist_complement_sound_on_closed_universe`.
- **Non-claims:**
  - The impossibility relies on `AxiomId = Nat` being infinite and `deny` being a finite `List AxiomId`; over a fixed finite closed universe `univ` (`OnlyDeclaredAxioms univ used`), the complement denylist `univ.filter (!allow.contains ·)` is sound (`denylist_complement_sound_on_closed_universe`), and a decidable predicate denylist `AxiomId → Bool` (such as `fun a => !allow.contains a`) can likewise complement `allow`.
  - `allowlistAccepts allow used = true` checks only that `used ⊆ allow` and trusts that `used` collects all axioms transitively depended on; it neither establishes consistency of the axioms inside `allow` nor detects soundness bypasses that introduce no axiom identifier into `used` (such as incomplete axiom collection, unsound reduction rules, foreign-function overrides, or unpinned definitions; see `cert_trust_triple_sound`).
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - J. H. Saltzer, M. D. Schroeder, "The Protection of Information in Computer Systems", Proceedings of the IEEE 63(9):1278–1308, 1975, doi:10.1109/PROC.1975.9939 (Section I-A-2, Fail-Safe Defaults): permission allowlists vs. exclusion denylists.
  - R. Pollack, "How to Believe a Machine-Checked Proof", in Twenty-Five Years of Constructive Type Theory (G. Sambin, J. M. Smith, eds.), Oxford University Press, pp. 205–220, 1998: auditing all axioms and definitions transitively depended on by a checked theorem.
  - Reference corpus package `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`: fail-closed vs. fail-open syntactic checks.
- **Design question:** Why must a TCB gate check axiom dependencies against a positive finite allowlist (`used ⊆ allow`) rather than grepping for a finite list of known banned axioms?

### `certificate-trust-triple-soundness-and-independence`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T0 — Elementary polymorphic reference point: restates the three-layer kernel-trust decomposition (`proof-checker-trust-layers-...`) over universe-polymorphic `CertVerifier Stmt Rule Cert` interfaces (`Type u`, `Type v`, `Type w`), used directly by `CertPinnedLink` on `Sys : Type 1` and paired with four pairwise independence counterexamples.
- **Lean:** `Toy.BoundaryLicensing.cert_trust_triple_sound`
- **Plain claim:** For every universe-polymorphic certificate verifier `V : CertVerifier Stmt Rule Cert`, rule parameter `R : Rule`, shipped statement table `shipped : Nat → Option Stmt`, certificate `c : Cert`, and theorem identifier `name : Nat`: if `CertFaithful V R`, `CertSemSound V R`, `TablePinned V.official shipped name`, and `acceptsNamed V R shipped c name = true` all hold, then there exists `φ : Stmt` such that `V.official name = some φ` and `V.valid φ`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:139-146
theorem cert_trust_triple_sound {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) (shipped : Nat → Option Stmt)
    (c : Cert) (name : Nat)
    (hfaith : CertFaithful V R)
    (hsem : CertSemSound V R)
    (hpin : TablePinned V.official shipped name)
    (hacc : acceptsNamed V R shipped c name = true) :
    ∃ φ, V.official name = some φ ∧ V.valid φ := …
```

Unfolded (`cert_trust_triple_sound`):

```lean
∃ φ : Stmt, V.official name = some φ ∧ V.valid φ
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfaith : CertFaithful V R` | ensures `V.check R c φ = true` implies `V.derivable R φ` | tight: counterexample `cex_trust_triple_without_faithful` (witness class: `boolUnfaithfulVerifier` (`check = true` always) with sound rules and pinned table at `name = 0`) |
| `hsem : CertSemSound V R` | ensures every `R`-derivable statement satisfies `V.valid` | tight: counterexample `cex_trust_triple_without_semSound` (witness class: `boolHonestVerifier` at unsound rule flag `R = false` with pinned table at `name = 0`) |
| `hpin : TablePinned V.official shipped name` | prevents `shipped` from remapping `name` to a trivially true statement while `V.official name` is false | tight: counterexample `cex_trust_triple_without_pinned` (witness class: `boolHonestVerifier` at `R = true` with `shipped 0 = some true` and `official 0 = some false`) |
| `hacc : acceptsNamed V R shipped c name = true` | requires the certificate check on `name` to actually pass | tight: counterexample `cex_trust_triple_without_accepted` (witness class: `boolHonestVerifier` at `R = true` with pinned table at `name = 0`, where `acceptsNamed = false`) |

- **Depth:** definitional.
- **Non-vacuity witness:** `nonvacuity_cert_trust_triple`: `boolHonestVerifier` at `R = true` and `name = 1` (`official 1 = some true`). (`Toy.BoundaryLicensing.nonvacuity_cert_trust_triple`).
- **Non-claims:**
  - `TablePinned` checks equality of `Stmt` values at `name` only; in languages with definitional dependencies, pinning the surface statement without pinning the transitive definition closure of `φ` (not modeled in `TablePinned`) leaves statement spoofing open.
  - `TablePinned` pins `shipped name` to `V.official name` only; it neither pins the rule parameter `R` (whose soundness must be supplied separately via `CertSemSound V R`) nor establishes that the formal predicate `V.valid φ` matches informal user intent.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - R. Pollack, "How to Believe a Machine-Checked Proof", in Twenty-Five Years of Constructive Type Theory (G. Sambin, J. M. Smith, eds.), Oxford University Press, pp. 205–220, 1998: separation between checker derivability and statement faithfulness.
  - M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter, "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq", PACMPL 4(POPL):8, 2020, doi:10.1145/3371076; O. Abrahamsson, M. O. Myreen, R. Kumar, T. Sewell, "Candle: A Verified Implementation of HOL Light", ITP 2022, LIPIcs 237, pp. 3:1–3:17, doi:10.4230/LIPIcs.ITP.2022.3; M. Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean", arXiv:2403.14064, 2024: mechanized kernel verifiers separating algorithmic typechecking from declarative typing and environment lookup.
  - Reference corpus package `proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`: concrete propositional rule-table formulation of `Faithful`, `SemSound`, and `Pinned`.
- **Design question:** Can any two of checker faithfulness (`CertFaithful`), rule soundness (`CertSemSound`), and statement-table pinning (`TablePinned`) guarantee end-to-end validity of an accepted theorem name without the third?

### `bare-only-exhaustification-iff-and-neither-nor-safety`

Basis: `execution (Lean kernel check)`

- **Kind:** characterization. **Tier:** T0 — Re-derivation of focus-sensitive `only` exhaustification (Fox 2007) and explicit neither-nor scope-disclaimer safety (`implicature-safe-summaries-...`) over arbitrary world predicates `WorldClaim W`.
- **Lean:** `Toy.BoundaryLicensing.exhaustifiedOnly_sound_iff_contradictsEv`, `Toy.BoundaryLicensing.neitherNorDisclaimerSafe_iff`, `Toy.BoundaryLicensing.exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`
- **Plain claim:** For every world space `W : Type`, evidence predicate `E : WorldClaim W`, model claim `M : WorldClaim W`, and outside-model claim `S_ext : WorldClaim W`: if `EntailsEv E M` holds, then `EntailsEv E (exhaustifiedOnlyReading M S_ext)` (`∀ w, E w → M w ∧ ¬ S_ext w`) holds iff `ContradictsEv E S_ext` holds (`exhaustifiedOnly_sound_iff_contradictsEv`); `NeitherNorDisclaimerSafe E M S_ext` (`DisclaimerSafe E M S_ext .neitherNor`) holds iff `EntailsEv E M ∧ UndeterminedEv E S_ext` (`neitherNorDisclaimerSafe_iff`); and whenever `EntailsEv E M` and `UndeterminedEv E S_ext` hold, `DisclaimerSafe E M S_ext .bareOnly` and `EntailsEv E (exhaustifiedOnlyReading M S_ext)` fail while `NeitherNorDisclaimerSafe E M S_ext` holds (`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:73-75
theorem exhaustifiedOnly_sound_iff_contradictsEv {W : Type} (E M S_ext : WorldClaim W)
    (hM : EntailsEv E M) :
    EntailsEv E (exhaustifiedOnlyReading M S_ext) ↔ ContradictsEv E S_ext := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:60-61
theorem neitherNorDisclaimerSafe_iff {W : Type} (E M S_ext : WorldClaim W) :
    NeitherNorDisclaimerSafe E M S_ext ↔ EntailsEv E M ∧ UndeterminedEv E S_ext := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:84-88
theorem exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined {W : Type}
    (E M S_ext : WorldClaim W) (hM : EntailsEv E M) (hund : UndeterminedEv E S_ext) :
    ¬ DisclaimerSafe E M S_ext .bareOnly ∧
    ¬ EntailsEv E (exhaustifiedOnlyReading M S_ext) ∧
    NeitherNorDisclaimerSafe E M S_ext := …
```

Unfolded (`exhaustifiedOnly_sound_iff_contradictsEv`):

```lean
(∀ w : W, E w → M w ∧ ¬ S_ext w) ↔ (∀ w : W, E w → ¬ S_ext w)
```

Unfolded (`neitherNorDisclaimerSafe_iff`):

```lean
DisclaimerSafe E M S_ext ScopeDisclaimer.neitherNor ↔
  (∀ w : W, E w → M w) ∧ ¬ (∀ w : W, E w → S_ext w) ∧ ¬ (∀ w : W, E w → ¬ S_ext w)
```

Unfolded (`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`):

```lean
¬ DisclaimerSafe E M S_ext ScopeDisclaimer.bareOnly ∧
  ¬ (∀ w : W, E w → M w ∧ ¬ S_ext w) ∧
  DisclaimerSafe E M S_ext ScopeDisclaimer.neitherNor
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hM : EntailsEv E M` (in `exhaustifiedOnly_sound_iff_contradictsEv`, `exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`) | supplies entailment of the positive prejacent `M` used by both `exhaustifiedOnlyReading M S_ext` and `NeitherNorDisclaimerSafe E M S_ext` | tight: counterexample `cex_exhaustifiedOnly_without_model_entailed`, `cex_neitherNor_without_model_entailed` (witness class: `W = Bool` with `E = True` and `M = (· = true)`, failing at `w = false` under both `S_ext = False` (refuted) and `S_ext = (· = false)` (undetermined)) |
| `hund : UndeterminedEv E S_ext` (in `exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`) | excludes cases where `E` already refutes `S_ext` (making `.bareOnly` sound and `.neitherNor` literally false) | tight: counterexample `cex_exhaustifiedOnly_unsound_without_undetermined` (witness class: `W = Bool` with `E = (· = true)`, `M = (· = true)`, and `S_ext = (· = false)`, where `DisclaimerSafe E M S_ext .bareOnly` holds and `NeitherNorDisclaimerSafe E M S_ext` fails) |

- **Depth:** definitional.
- **Non-vacuity witness:** `nonvacuity_exhaustifiedOnly`: over `W = Bool`, `(E = (· = true), M = (· = true), S_ext = (· = false))` witnesses `EntailsEv E M ∧ ContradictsEv E S_ext`, while `(E = True, M = True, S_ext = (· = true))` witnesses `EntailsEv E M ∧ UndeterminedEv E S_ext ∧ NeitherNorDisclaimerSafe E M S_ext`. (`Toy.BoundaryLicensing.nonvacuity_exhaustifiedOnly`).
- **Non-claims:**
  - When `E` explicitly proves a refutation of `S_ext` (`ContradictsEv E S_ext` with `¬ EntailsEv E S_ext`), `exhaustifiedOnlyReading M S_ext` and `DisclaimerSafe E M S_ext .bareOnly` ARE supported by `E`; what is unsound is writing bare `"only"` when `S_ext` is undetermined (`UndeterminedEv E S_ext`; `exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`).
  - `NeitherNorDisclaimerSafe E M S_ext` (`DisclaimerSafe E M S_ext .neitherNor`) is equivalent to `EntailsEv E M ∧ UndeterminedEv E S_ext` (`neitherNorDisclaimerSafe_iff`): it checks `DisclaimerLitTrue` together with entailment of `disclaimerReadings M S_ext .neitherNor = [M]`, and is false whenever `E` does not entail `M`, whenever `E` entails or contradicts `S_ext`, or whenever `E` is unsatisfiable (`∀ w, ¬ E w`).
  - Probabilistic or context-dependent reader cancellation cues beyond the three deterministic `ScopeDisclaimer` forms (`bareOnly`, `unblockedUnshown`, `neitherNor`) are not modeled.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - D. Fox, "Free Choice and the Theory of Scalar Implicatures", in Presupposition and Implicature in Compositional Semantics (U. Sauerland, P. Stateva, eds.), Palgrave Macmillan, pp. 71–120, 2007, doi:10.1057/9780230210752_4: covert exhaustification (`Exh`) as silent `only` negating excludable alternatives.
  - Reference corpus package `implicature-safe-summaries-conditional-perfection-and-exhaustification-of-formal-claims`: finite-world innocent exclusion and disclaimer safety (`notShown` vs. `notShownNotRefuted`).
- **Design question:** Under `BoundaryRel.none` (no proved model–system bridge), when is scoping a result with bare `"only"` sound, and why is `"neither establish nor refute"` required whenever the system-level claim is undetermined?

### `compression-blocker-non-inheritance-and-non-markovian-barrier`

Basis: `execution (Lean kernel check)`

- **Kind:** impossibility. **Tier:** T1 — Non-inheritance of inherited blockers after conjunct-dropping was established on a finite multi-world model in `implicature-safe-summaries-...`; isolating the minimal 2-world conditional-perfection witness on `Bool`, the 3-world Fox (2007) innocent-exclusion minimality-loss witness on `Fin 3` under genuine conclusion-dropping, and the resulting impossibility of any stateless boolean transfer function `Bool → Bool` for `(H, G₁ ∧ G₂) ↦ (H, G₁)` are proved here.
- **Lean:** `Toy.BoundaryLicensing.condPerfection_compression_breaks_minimal_safe_blocker`, `Toy.BoundaryLicensing.scalarExh_compression_breaks_blocker_minimality`, `Toy.BoundaryLicensing.no_stateless_implicature_transfer_for_compression`
- **Plain claim:** Under genuine conclusion-dropping `(H, G₁ ∧ G₂) ↦ (H, G₁)` with no side-channel fields on `SummaryCard`: over `Bool` with `E = True` and `alts = []`, `B = []` is minimal and `ImplicatureSafe` on `fullConjCard` (`H → True ∧ H`) yet fails `ImplicatureSafe` after dropping `G₂` to `compressedG1Card` (`H → True`) (`condPerfection_compression_breaks_minimal_safe_blocker`); dually, over `Fin 3` with fixed `E = fin3Alt12` and fixed alternatives `alts = [fin3Alt02, fin3Alt12]`, `[.scalarExh]` is minimal and safe on `⟨True, (fin3Alt02 ∨ fin3Alt12) ∧ fin3Alt12⟩` yet loses `MinimalSafeBlockers` after dropping `fin3Alt12` because `{fin3Alt02}` and `{fin3Alt12}` clash under `innocentExh` (`scalarExh_compression_breaks_blocker_minimality`); consequently, no stateless function `f : Bool → Bool` computes post-drop `ImplicatureSafe` from pre-drop `ImplicatureSafe` across all conclusion-drops `(H, G₁ ∧ G₂) ↦ (H, G₁)` (`no_stateless_implicature_transfer_for_compression`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:244-249
theorem condPerfection_compression_breaks_minimal_safe_blocker :
    let E : WorldClaim Bool := fun _ => True
    MinimalSafeBlockers E [] [] fullConjCard ∧
    EntailsEv fullConjCard.lit compressedG1Card.lit ∧
    EntailsEv E compressedG1Card.lit ∧
    ¬ ImplicatureSafe E [] [] compressedG1Card := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:275-287
theorem scalarExh_compression_breaks_blocker_minimality :
    let E : WorldClaim (Fin 3) := fin3Alt12
    let alts : List (WorldClaim (Fin 3)) := [fin3Alt02, fin3Alt12]
    let H : WorldClaim (Fin 3) := fun _ => True
    let G₁ : WorldClaim (Fin 3) := fun w => fin3Alt02 w ∨ fin3Alt12 w
    let G₂ : WorldClaim (Fin 3) := fin3Alt12
    let preCard : SummaryCard (Fin 3) := ⟨H, fun w => G₁ w ∧ G₂ w⟩
    let postCard : SummaryCard (Fin 3) := ⟨H, G₁⟩
    MinimalSafeBlockers E alts [.scalarExh] preCard ∧
    EntailsEv preCard.lit postCard.lit ∧
    ImplicatureSafe E alts [] postCard ∧
    ImplicatureSafe E alts [.scalarExh] postCard ∧
    ¬ MinimalSafeBlockers E alts [.scalarExh] postCard := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:386-391
theorem no_stateless_implicature_transfer_for_compression :
    ¬ ∃ f : Bool → Bool,
        ∀ (H G₁ G₂ : WorldClaim Bool) (b₁ b₂ : Bool),
          (b₁ = true ↔ ImplicatureSafe (fun _ => True) [] [] ⟨H, fun w => G₁ w ∧ G₂ w⟩) →
          (b₂ = true ↔ ImplicatureSafe (fun _ => True) [] [] ⟨H, G₁⟩) →
          f b₁ = b₂ := …
```

Unfolded (`condPerfection_compression_breaks_minimal_safe_blocker`):

```lean
MinimalSafeBlockers (fun _ : Bool => True) [] [] fullConjCard ∧
  EntailsEv fullConjCard.lit compressedG1Card.lit ∧
  EntailsEv (fun _ : Bool => True) compressedG1Card.lit ∧
  ¬ ImplicatureSafe (fun _ : Bool => True) [] [] compressedG1Card
```

Unfolded (`scalarExh_compression_breaks_blocker_minimality`):

```lean
MinimalSafeBlockers fin3Alt12 [fin3Alt02, fin3Alt12] [PragRule.scalarExh]
    ⟨fun _ => True, fun w => (fin3Alt02 w ∨ fin3Alt12 w) ∧ fin3Alt12 w⟩ ∧
  EntailsEv (SummaryCard.lit ⟨fun _ => True, fun w => (fin3Alt02 w ∨ fin3Alt12 w) ∧ fin3Alt12 w⟩)
    (SummaryCard.lit ⟨fun _ => True, fun w => fin3Alt02 w ∨ fin3Alt12 w⟩) ∧
  ImplicatureSafe fin3Alt12 [fin3Alt02, fin3Alt12] []
    ⟨fun _ => True, fun w => fin3Alt02 w ∨ fin3Alt12 w⟩ ∧
  ImplicatureSafe fin3Alt12 [fin3Alt02, fin3Alt12] [PragRule.scalarExh]
    ⟨fun _ => True, fun w => fin3Alt02 w ∨ fin3Alt12 w⟩ ∧
  ¬ MinimalSafeBlockers fin3Alt12 [fin3Alt02, fin3Alt12] [PragRule.scalarExh]
      ⟨fun _ => True, fun w => fin3Alt02 w ∨ fin3Alt12 w⟩
```

Unfolded (`no_stateless_implicature_transfer_for_compression`):

```lean
¬ ∃ f : Bool → Bool,
    ∀ (H G₁ G₂ : WorldClaim Bool) (b₁ b₂ : Bool),
      (b₁ = true ↔ ImplicatureSafe (fun _ => True) [] [] ⟨H, fun w => G₁ w ∧ G₂ w⟩) →
      (b₂ = true ↔ ImplicatureSafe (fun _ => True) [] [] ⟨H, G₁⟩) →
      f b₁ = b₂
```

Hypothesis ledger: no hypotheses beyond the universally quantified parameters.

- **Depth:** shallow.
- **Non-vacuity witness:** `condPerfection_compression_breaks_minimal_safe_blocker`: `MinimalSafeBlockers (fun _ => True) [] [] fullConjCard` and `EntailsEv fullConjCard.lit compressedG1Card.lit` hold while `¬ ImplicatureSafe (fun _ => True) [] [] compressedG1Card`. (`Toy.BoundaryLicensing.condPerfection_compression_breaks_minimal_safe_blocker`).
- **Positive control:** `Toy.BoundaryLicensing.recomputeBlockers_safe_and_minimal`.
- **Non-claims:**
  - Literal truth (`EntailsEv E card.lit`) IS preserved by conclusion-dropping (`LitEntailsLink`); what fails stateless inheritance is pragmatic `ImplicatureSafe` and `MinimalSafeBlockers` (`no_stateless_implicature_transfer_for_compression`, `condPerfection_compression_breaks_minimal_safe_blocker`, `scalarExh_compression_breaks_blocker_minimality`).
  - `no_stateless_implicature_transfer_for_compression` rules out an exact two-valued boolean predictor `f : Bool → Bool` computing post-compression `ImplicatureSafe` from pre-compression `ImplicatureSafe` alone; a conservative three-valued `Status` transformer mapping `.supported` to `.undetermined` remains sound under `Status.le` because stateless compression cannot license post-compression `.supported` safety without recomputing blockers on `(E, alts, c₂)`.
  - Recomputing `recomputeBlockers E alts card` directly from `(E, alts, card)` after compression restores both `ImplicatureSafe` and `MinimalSafeBlockers` (`recomputeBlockers_safe_and_minimal`).
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - M. L. Geis, A. M. Zwicky, "On Invited Inferences", Linguistic Inquiry 2(4):561–566, 1971: conditional perfection (`if H then C` inviting `if C then H`), whose antecedent `C` sits in contravariant position when `C` is weakened.
  - D. Fox, "Free Choice and the Theory of Scalar Implicatures", in Presupposition and Implicature in Compositional Semantics (U. Sauerland, P. Stateva, eds.), Palgrave Macmillan, pp. 71–120, 2007, doi:10.1057/9780230210752_4: innocent exclusion (`InnocentlyExcludable`, `innocentExh`) over maximal consistently excludable subsets of scalar alternatives.
  - Reference corpus package `implicature-safe-summaries-conditional-perfection-and-exhaustification-of-formal-claims`: blocker sets and conclusion-dropping summary compression.
- **Design question:** Why cannot summary compression (`H → G₁ ∧ G₂` compressed to `H → G₁`) be treated as a stateless Markovian `BoundaryRel` that carries forward the full card's minimal blocker annotations?

### `sequent-refutation-context-split-and-dead-branch-vacuity`

Basis: `execution (Lean kernel check)`

- **Kind:** theorem. **Tier:** T1 — Global hypothesis non-vacuity was formalized in `hypothesis-ledgers-...`; splitting `Sequent` into `ctxHyps` vs. `badHyps` (with tight premises on `refutation_not_fullPremiseNonVacuous`) and isolating sum-branch vacuity closed by non-empty `NonVacuousOnBranches` are made explicit here.
- **Lean:** `Toy.BoundaryLicensing.refutation_not_fullPremiseNonVacuous`, `Toy.BoundaryLicensing.cex_global_ctxNonVacuous_dead_right_branch`
- **Plain claim:** For every sequent `sq : Sequent α m k`: if `∀ x, sq.goal x ↔ False` and `sq.Holds` hold, then `sq.FullPremiseNonVacuous` fails (`refutation_not_fullPremiseNonVacuous`), motivating `Sequent.CtxNonVacuous`; however, on `Sum Unit Unit`, the explicit sequent `deadRightBranchSequent` satisfies both `Sequent.Holds` and global `Sequent.CtxNonVacuous` (witnessed at `Sum.inl ()`) while vacuously entailing `False` on every `Sum.inr u`, and is rejected by `Sequent.NonVacuousOnBranches` over `[isLeft, isRight]` (`cex_global_ctxNonVacuous_dead_right_branch`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:50-52
theorem refutation_not_fullPremiseNonVacuous {α : Type} {m k : Nat} (sq : Sequent α m k)
    (href : ∀ x, sq.goal x ↔ False) (hholds : sq.Holds) :
    ¬ sq.FullPremiseNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:108-113
theorem cex_global_ctxNonVacuous_dead_right_branch :
    deadRightBranchSequent.Holds ∧
    deadRightBranchSequent.CtxNonVacuous ∧
    (∀ u : Unit, AllCtx deadRightBranchSequent.ctxHyps (.inr u) → False) ∧
    ¬ deadRightBranchSequent.NonVacuousOnBranches
        [fun x => x.isLeft = true, fun x => x.isRight = true] := …
```

Unfolded (`refutation_not_fullPremiseNonVacuous`):

```lean
¬ ∃ x : α, (∀ i : Fin m, sq.ctxHyps i x) ∧ (∀ j : Fin k, sq.badHyps j x)
```

Unfolded (`cex_global_ctxNonVacuous_dead_right_branch`):

```lean
(∀ x : Sum Unit Unit, AllCtx deadRightBranchSequent.ctxHyps x →
    AllBad deadRightBranchSequent.badHyps x → deadRightBranchSequent.goal x) ∧
  (∃ x : Sum Unit Unit, AllCtx deadRightBranchSequent.ctxHyps x) ∧
  (∀ u : Unit, AllCtx deadRightBranchSequent.ctxHyps (Sum.inr u) → False) ∧
  ¬ ([fun x : Sum Unit Unit => x.isLeft = true, fun x => x.isRight = true] ≠ [] ∧
      ∀ b ∈ [fun x : Sum Unit Unit => x.isLeft = true, fun x => x.isRight = true],
        ∃ x : Sum Unit Unit, b x ∧ AllCtx deadRightBranchSequent.ctxHyps x)
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `href : ∀ x, sq.goal x ↔ False` (in `refutation_not_fullPremiseNonVacuous`) | restricts full-premise impossibility to refutation sequents whose goal is logically false | tight: counterexample `cex_refutation_not_fullPremise_without_href` (witness class: there is a positive sequent on `Nat` (`ctx: x < 5`, `bad: x = 3`, `goal: True`) satisfying both `Holds` and `FullPremiseNonVacuous` at `x = 3`) |
| `hholds : sq.Holds` (in `refutation_not_fullPremiseNonVacuous`) | requires the refutation sequent to be valid so `ctxHyps` and `badHyps` cannot hold simultaneously | tight: counterexample `cex_refutation_not_fullPremise_without_hholds` (witness class: there is an invalid refutation sequent on `Nat` (`ctx: x < 5`, `bad: x = 3`, `goal: False`) satisfying `FullPremiseNonVacuous` at `x = 3`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_sequent_refutation_and_branches`: `natBoundRefutation` satisfies `∀ x, goal x ↔ False`, `Sequent.Holds`, and `Sequent.CtxNonVacuous`, and the unrestricted `Sum Unit Unit` sequent satisfies `NonVacuousOnBranches` over `[isLeft, isRight]`. (`Toy.BoundaryLicensing.nonvacuity_sequent_refutation_and_branches`).
- **Non-claims:**
  - `Sequent.NonVacuousOnBranches` requires `branches ≠ []` (so `nonVacuousOnBranches_implies_ctxNonVacuous` holds) and `∃ x, b x ∧ AllCtx sq.ctxHyps x` for each `b ∈ branches`, without requiring `branches` to be disjoint or exhaustive and without inspecting guards placed inside `sq.badHyps` or inside an implicational `sq.goal` (`fun x => guard x → P x`); encoding a dead branch restriction inside `goal` or omitting a constructor from `branches` leaves branch vacuity undetected.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - Reference corpus package `hypothesis-ledgers-tightness-irredundancy-weakest-premises-and-vacuity`: `Sufficient`, global `NonVacuous`, and `TightAt` over unpartitioned hypothesis families.
- **Design question:** Why does naive all-premise non-vacuity fail on refutation theorems (`goal = False`), and why is global domain non-vacuity (`∃ x, AllCtx ctxHyps x`) still insufficient on sum or enum domains?

### `finite-suite-allowlist-separation-barrier`

Basis: `execution (Lean kernel check)`

- **Kind:** impossibility. **Tier:** T1 — Refines the anchor-allowlist acceptance lemmas of `sound-checker-laws-anchors-allowlists-and-certificates` into a parametric invariance barrier over higher-order laws `SuiteSoundInvariant good F L` with four canonical tightness counterexamples and a post-freeze probe positive control.
- **Lean:** `Toy.BoundaryLicensing.finite_suite_allowlist_barrier`
- **Plain claim:** For every decidable-equality artifact type `α`, validity predicate `good : α → Prop`, pre-fixed finite suite `F : List α`, law `L : (α → Bool) → Prop`, and checker `c : α → Bool`: if `CheckerSound good c`, `SuiteSoundInvariant good F L`, `L c`, and `∃ p, p ∉ F ∧ c p = true` all hold, then `L (suiteAllowlist F c)` holds even though `suiteAllowlist F c ≠ c`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:49-55
theorem finite_suite_allowlist_barrier {α : Type} [DecidableEq α]
    (good : α → Prop) (F : List α) (L : (α → Bool) → Prop) (c : α → Bool)
    (hsound : CheckerSound good c)
    (hinv : SuiteSoundInvariant good F L)
    (hlaw : L c)
    (hout : ∃ p : α, p ∉ F ∧ c p = true) :
    L (suiteAllowlist F c) ∧ suiteAllowlist F c ≠ c := …
```

Unfolded (`finite_suite_allowlist_barrier`):

```lean
L (fun x => decide (x ∈ F) && c x) ∧ (fun x => decide (x ∈ F) && c x) ≠ c
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsound : CheckerSound good c` | ensures `CheckerSound good c ↔ CheckerSound good (suiteAllowlist F c)` both hold (`True ↔ True`, and implies `good p` on the outside witness via `outside_accepted_good_iff`), since `suiteAllowlist F` can turn an unsound `c` into a sound checker | tight: counterexample `cex_suite_barrier_without_sound` (witness class: `good = (· % 2 = 0)`, `F = [0]`, `c = fun _ => true` (unsound at `1`, accepting valid outside witness `p = 2`), and `L = (¬ CheckerSound good ·)`, where `suiteAllowlist [0] c` becomes sound and falsifies `L`) |
| `hinv : SuiteSoundInvariant good F L` | restricts `L` to depend only on `CheckerSound good ·` truth and checker outputs on `F` | tight: counterexample `cex_suite_barrier_without_invariant` (witness class: there is an even-number checker `c` on `F = [0]` with `L d := d 2 = true` probing `2 ∉ F`) |
| `hlaw : L c` | supplies satisfaction of `L` on the original checker `c` | tight: counterexample `cex_suite_barrier_without_law` (witness class: `L = fun _ => False` on `F = [0]` and `c = (· % 2 == 0)`) |
| `hout : ∃ p : α, p ∉ F ∧ c p = true` | ensures `suiteAllowlist F c` actually differs extensionally from `c` on at least one accepted input outside `F` (automatically valid under `hsound` by `outside_accepted_good_iff`) | tight: counterexample `cex_suite_barrier_without_outside_witness` (witness class: `good = (· = 0)` and `c = (· == 0)` on `F = [0]`, where `suiteAllowlist [0] c = c`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_finite_suite_barrier`: `good = (· % 2 = 0)`, `c = (· % 2 == 0)`, `F = [0]`, `L d := CheckerSound good d ∧ d 0 = true`, and outside witness `p = 2`. (`Toy.BoundaryLicensing.nonvacuity_finite_suite_barrier`).
- **Positive control:** `Toy.BoundaryLicensing.positive_control_postFreeze_probe_separates`.
- **Non-claims:**
  - The barrier applies to a fixed finite suite `F` chosen before the checker is frozen; evaluating `c` on held-out or post-freeze valid artifacts outside `F` breaks `SuiteSoundInvariant` and separates `c` from `suiteAllowlist F c` (`positive_control_postFreeze_probe_separates`).
  - Universal relational or metamorphic checker laws across unbounded inputs (for example, monotonicity or equivalence-invariance `∀ x y, rel x y → c x = true → c y = true`) and proof-certificate obligations depend on behavior outside `F`, violate `SuiteSoundInvariant`, and are not subject to `finite_suite_allowlist_barrier` (not proved here).
  - Over bounded finite state spaces where `F` enumerates every accepted input (`∀ p, c p = true → p ∈ F`), `suiteAllowlist F c` equals `c` (`cex_suite_barrier_without_outside_witness`).
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - Reference corpus package `sound-checker-laws-anchors-allowlists-and-certificates`: elementary anchor-allowlist acceptance (`R2a`, `R2c`, `R2f`).
  - Reference corpus package `finite-test-suites-teaching-sets-and-bounded-state-completeness`: finite test suites vs. unbounded domains.
- **Design question:** Can any acceptance criterion combining soundness with pass rates on a pre-published finite benchmark suite `F` distinguish a general compositional verifier from a hardcoded `F`-allowlist?

### `extensional-lookup-wrapper-barrier`

Basis: `execution (Lean kernel check)`

- **Kind:** impossibility. **Tier:** T0 — Elementary intensional-representation reference point: restates extensional lookup-wrapper indistinguishability (`sound-checker-laws-...` `R3a`) over explicit `ImplChecker α Code` pairs so `ImplExtensionalLaw` does not collapse trivially under Lean function extensionality on bare `α → Bool`.
- **Lean:** `Toy.BoundaryLicensing.extensional_law_admits_lookupWrapper`
- **Plain claim:** For every decidable-equality type `α`, representation type `Code`, law `L : ImplChecker α Code → Prop`, representations `code₁ code₂ : Code`, checker `c : α → Bool`, and lookup table `table : List (α × Bool)`: if `ImplExtensionalLaw L`, `TableConsistentWith table c`, and `L ⟨code₁, c⟩` hold, then `L ⟨code₂, lookupWrapper table c⟩` holds and `code₁ ≠ code₂` implies `⟨code₂, lookupWrapper table c⟩ ≠ ⟨code₁, c⟩`.

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:206-213
theorem extensional_law_admits_lookupWrapper {α Code : Type} [DecidableEq α]
    (L : ImplChecker α Code → Prop) (code₁ code₂ : Code) (c : α → Bool)
    (table : List (α × Bool))
    (hext : ImplExtensionalLaw L)
    (hcons : TableConsistentWith table c)
    (hlaw : L ⟨code₁, c⟩) :
    L ⟨code₂, lookupWrapper table c⟩ ∧ (code₁ ≠ code₂ →
      (⟨code₂, lookupWrapper table c⟩ : ImplChecker α Code) ≠ ⟨code₁, c⟩) := …
```

Unfolded (`extensional_law_admits_lookupWrapper`):

```lean
L ⟨code₂, lookupWrapper table c⟩ ∧
  (code₁ ≠ code₂ → (⟨code₂, lookupWrapper table c⟩ : ImplChecker α Code) ≠ ⟨code₁, c⟩)
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hext : ImplExtensionalLaw L` | prevents `L` from inspecting `ImplChecker.code` directly rather than input-output behavior `run` | tight: counterexample `cex_lookup_without_extensional` (witness class: `L chk := chk.code = true` separating `code₁ = true` from `code₂ = false`) |
| `hcons : TableConsistentWith table c` | ensures every cached entry in `table` agrees with `c` so `lookupWrapper table c` has identical `run` behavior | tight: counterexample `cex_lookup_without_consistent` (witness class: there is an inconsistent entry `[(1, true)]` wrapping `c = (· == 0)` under `L chk := CheckerSound (· = 0) chk.run`) |
| `hlaw : L ⟨code₁, c⟩` | supplies satisfaction of `L` on the original implementation `⟨code₁, c⟩` | tight: counterexample `cex_lookup_without_law` (witness class: `L = fun _ => False` with `table = [(0, true)]` and `c = (· == 0)`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_extensional_lookupWrapper`: on `L chk := CheckerSound (· = 0) chk.run ∧ chk.run 0 = true`, `c = (· == 0)`, `table = [(0, true)]`, `code₁ = true`, and `code₂ = false`, all three hypotheses (`ImplExtensionalLaw L`, `TableConsistentWith table c`, `L ⟨true, c⟩`) and `true ≠ false` hold jointly. (`Toy.BoundaryLicensing.nonvacuity_extensional_lookupWrapper`).
- **Positive control:** `Toy.BoundaryLicensing.positive_control_intensional_code_law_separates`.
- **Non-claims:**
  - `lookupWrapper table c` retains the full fallback checker `c` for every input absent from `table` (and when `code₁ = code₂`, `⟨code, lookupWrapper table c⟩ = ⟨code, c⟩` by `lookupWrapper_same_code_eq`); `extensional_law_admits_lookupWrapper` establishes extensional indistinguishability of fronting `c` with a consistent memoization cache, not that a standalone finite lookup table without `c` can match `c` over an unbounded input domain.
  - Intensional or certificate-emitting requirements that inspect `code` or require independently checkable proof objects (`positive_control_intensional_code_law_separates`, `cert_trust_triple_sound`) are not `ImplExtensionalLaw` and DO separate compositional checkers from lookup-wrapped representations.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - Reference corpus package `sound-checker-laws-anchors-allowlists-and-certificates`: extensional checker equivalence (`R3a`).
- **Design question:** Can any black-box input-output testing law (even over all inputs `α`) distinguish a compositional checker implementation from one fronted by a consistent lookup cache, without inspecting code or proof certificates?

### `anti-lockout-exactness-and-warn-adjudicate-repair`

Basis: `execution (Lean kernel check)`

- **Kind:** characterization. **Tier:** T0 — Elementary re-derivation of sound-and-complete boolean decision equivalence (`sound-checker-laws-...` `R6c`) paired with conservative fast-path filtering (`warnAdjudicateGate`), explicitly recording the four tightness obligations separating hard `blockingGate` lockout from `warn + adjudicate`.
- **Lean:** `Toy.BoundaryLicensing.zeroLockout_and_zeroFalseAccept_iff_exact`, `Toy.BoundaryLicensing.blockingGate_locks_out_strict_proxy`, `Toy.BoundaryLicensing.warnAdjudicateGate_zeroLockout_and_sound`
- **Plain claim:** For every artifact type `α`, semantic validity predicate `P : α → Prop`, and boolean check `Q : α → Bool`: `blockingGate Q` achieves both `ZeroLockout P` and `ZeroFalseAccept P` iff `∀ x, Q x = true ↔ P x` (`zeroLockout_and_zeroFalseAccept_iff_exact`); if `P x₀` and `Q x₀ = false` hold for some `x₀ : α`, then `blockingGate Q x₀ = false` and `ZeroLockout P (blockingGate Q)` fails (`blockingGate_locks_out_strict_proxy`), whereas if `ExactAdjudicatorOnWarnings P Q adj` and `ZeroFalseAccept P Q` hold, then `warnAdjudicateGate Q adj` achieves both `ZeroLockout P` and `ZeroFalseAccept P` (`warnAdjudicateGate_zeroLockout_and_sound`).

Statement:

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:297-299
theorem zeroLockout_and_zeroFalseAccept_iff_exact {α : Type} (P : α → Prop) (Q : α → Bool) :
    (ZeroLockout P (blockingGate Q) ∧ ZeroFalseAccept P (blockingGate Q)) ↔
      ∀ x : α, Q x = true ↔ P x := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:308-310
theorem blockingGate_locks_out_strict_proxy {α : Type} (P : α → Prop) (Q : α → Bool)
    (x₀ : α) (hvalid : P x₀) (hproxy : Q x₀ = false) :
    blockingGate Q x₀ = false ∧ ¬ ZeroLockout P (blockingGate Q) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:321-326
theorem warnAdjudicateGate_zeroLockout_and_sound {α : Type} (P : α → Prop)
    (Q adj : α → Bool)
    (hadj : ExactAdjudicatorOnWarnings P Q adj)
    (hfast : ZeroFalseAccept P Q) :
    ZeroLockout P (warnAdjudicateGate Q adj) ∧
    ZeroFalseAccept P (warnAdjudicateGate Q adj) := …
```

Unfolded (`zeroLockout_and_zeroFalseAccept_iff_exact`):

```lean
((∀ x : α, P x → Q x = true) ∧ (∀ x : α, Q x = true → P x)) ↔
  (∀ x : α, Q x = true ↔ P x)
```

Unfolded (`blockingGate_locks_out_strict_proxy`):

```lean
Q x₀ = false ∧ ¬ (∀ x : α, P x → Q x = true)
```

Unfolded (`warnAdjudicateGate_zeroLockout_and_sound`):

```lean
(∀ x : α, P x → (if Q x then true else adj x) = true) ∧
  (∀ x : α, (if Q x then true else adj x) = true → P x)
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hvalid : P x₀` (in `blockingGate_locks_out_strict_proxy`) | supplies a semantically valid artifact `x₀` so rejecting `x₀` constitutes a genuine lockout rather than a sound rejection | tight: counterexample `cex_blocking_lockout_without_valid_witness` (witness class: `P = (· = true)` and exact `Q = id` at invalid `x₀ = false`, where `Q false = false` yet `ZeroLockout P (blockingGate Q)` holds) |
| `hproxy : Q x₀ = false` (in `blockingGate_locks_out_strict_proxy`) | witnesses strictness of the proxy check `Q` rejecting the valid artifact `x₀` | tight: counterexample `cex_blocking_lockout_without_proxy_reject` (witness class: `P = (· = true)` and exact `Q = id` at `x₀ = true`, where `P true` holds and `ZeroLockout P (blockingGate Q)` holds) |
| `hadj : ExactAdjudicatorOnWarnings P Q adj` (in `warnAdjudicateGate_zeroLockout_and_sound`) | ensures warned inputs (`Q x = false`) are neither falsely locked out nor falsely accepted by `adj` | tight: counterexample `cex_warnAdjudicate_without_exact_adjudicator` (witness class: `P = (· = true)`, `Q = fun _ => false`, and `adj = fun _ => false`, which satisfies `ZeroFalseAccept P Q` yet violates `ZeroLockout`) |
| `hfast : ZeroFalseAccept P Q` (in `warnAdjudicateGate_zeroLockout_and_sound`) | ensures inputs accepted immediately on the `Q x = true` fast path (bypassing `adj`) satisfy `P` | tight: counterexample `cex_warnAdjudicate_without_sound_fastPath` (witness class: `P = (· = true)`, `Q = fun _ => true`, and `adj = id`, where `ExactAdjudicatorOnWarnings` holds vacuously yet `false` is falsely accepted) |

- **Depth:** definitional.
- **Non-vacuity witness:** `nonvacuity_exact_blockingGate` and `nonvacuity_warnAdjudicate_strict_proxy`: exact `Q = (· == 0)` for `P = (· = 0)` satisfies both sides of `zeroLockout_and_zeroFalseAccept_iff_exact`, while strict proxy `Q = (· == 0)` for `P = (· % 2 = 0)` rejects valid `x₀ = 2` and is repaired by `warnAdjudicateGate Q (· % 2 == 0)`. (`Toy.BoundaryLicensing.nonvacuity_exact_blockingGate`, `Toy.BoundaryLicensing.nonvacuity_warnAdjudicate_strict_proxy`).
- **Non-claims:**
  - `warnAdjudicateGate_zeroLockout_and_sound` requires `ZeroFalseAccept P Q` (`∀ x, Q x = true → P x`) on the unwarned fast path (`cex_warnAdjudicate_without_sound_fastPath`): a heuristic `Q` that silently passes invalid artifacts (`Q x = true ∧ ¬ P x`) cannot skip adjudication without false acceptances.
  - `ExactAdjudicatorOnWarnings P Q adj` assumes a total boolean function `adj : α → Bool` that decides `P` without error on every warned input (`Q x = false`). When `P` is undecidable or when human or automated adjudication is fallible or partial (abstaining on hard instances), no total boolean `adj` satisfies `ExactAdjudicatorOnWarnings` (`cex_warnAdjudicate_without_exact_adjudicator`, undecidability not proved here).
  - Latency, human/computational cost of `adj`, and warning volume (`|{x | Q x = false}|`) are not modeled.
  - Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool.
- **Prior art:**
  - E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, "Counterexample-Guided Abstraction Refinement for Symbolic Model Checking", Journal of the ACM 50(5):752–794, 2003, doi:10.1145/876638.876643: conservative over-approximation accepting immediately when abstractly safe and routing abstract counterexamples to concrete feasibility checking and iterative refinement.
  - Reference corpus package `sound-checker-laws-anchors-allowlists-and-certificates`: exactness equivalence for universal soundness and completeness (`R6c`).
  - Reference corpus package `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`: fail-closed syntactic checks and incompleteness.
- **Design question:** When may an automated pipeline check `Q` be wired as hard `blocking` without locking out valid work, and under what exact hypotheses does `warn + adjudicate` eliminate lockout while preserving zero false acceptances?

### Auxiliary declarations cited by name

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:279-280
theorem acceptsNamed_neg :
    acceptsNamed boolHonestVerifier true boolHonestVerifier.official () 0 = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:276-277
theorem acceptsNamed_pos :
    acceptsNamed boolHonestVerifier true boolHonestVerifier.official () 1 = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:143
theorem allBad_neg : ¬ AllBad natBoundRefutation.badHyps 1 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:142
theorem allBad_pos : AllBad natBoundRefutation.badHyps 3 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:139
theorem allCtx_neg : ¬ AllCtx natBoundRefutation.ctxHyps 5 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:138
theorem allCtx_pos : AllCtx natBoundRefutation.ctxHyps 1 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:224
theorem allowlistAccepts_neg : allowlistAccepts [0, 1] [1, 2] = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:223
theorem allowlistAccepts_pos : allowlistAccepts [0, 1] [1, 0] = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:114-115
def allSafeH : TraceSet Bool → Prop :=
  fun T => ∀ b, T b → b = false
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:108-111
def bitSem : Nat → TraceSet Bool
  | 0 => fun b => b = false
  | 1 => fun b => b = true
  | _ => fun _ => True
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:434
theorem blockingGate_neg : blockingGate (fun b : Bool => b) false = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:433
theorem blockingGate_pos : blockingGate (fun b : Bool => b) true = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:152-156
def boolHonestVerifier : CertVerifier Bool Bool Unit where
  derivable := fun r φ => if r then φ = true else True
  valid := fun φ => φ = true
  check := fun r _ φ => if r then φ else true
  official := fun n => if n == 0 then some false else some true
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:159-163
def boolUnfaithfulVerifier : CertVerifier Bool Unit Unit where
  derivable := fun _ φ => φ = true
  valid := fun φ => φ = true
  check := fun _ _ _ => true
  official := fun _ => some false
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:118-119
def bothBranchesH : TraceSet Bool → Prop :=
  fun T => T false ∧ T true
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:91-94
theorem branch_nonVacuous_blocks_vacuous_branch_false {α : Type} {m : Nat}
    (sq : Sequent α m 0) (branches : List (α → Prop)) (b : α → Prop)
    (hmem : b ∈ branches) (hnv : sq.NonVacuousOnBranches branches) :
    ¬ (∀ x : α, b x → AllCtx sq.ctxHyps x → False) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:254
theorem certFaithful_neg : ¬ CertFaithful boolUnfaithfulVerifier () := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:251
theorem certFaithful_pos : CertFaithful boolHonestVerifier true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:527-528
theorem certPinnedLink_iff_traceEquiv (src tgt : Sys) :
    CertPinnedLink src tgt ↔ TraceIncl src tgt ∧ TraceIncl tgt src := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:261
theorem certSemSound_neg : ¬ CertSemSound boolHonestVerifier false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:258
theorem certSemSound_pos : CertSemSound boolHonestVerifier true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:374-377
theorem cex_blocking_lockout_without_proxy_reject :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun b => b
    P true ∧ ZeroLockout P (blockingGate Q) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:367-370
theorem cex_blocking_lockout_without_valid_witness :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun b => b
    Q false = false ∧ ZeroLockout P (blockingGate Q) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:171-178
theorem cex_coincidental_truth_on_unlicensed_chain :
    let rels : List BoundaryRel := [.stutterSim .s2m, .lockStepSim .s2m]
    RealizesChain rels (constSys valTrue) (constSys valTrue) ∧
    statusOf (constSys valTrue) .termination specAtom0 = .supported ∧
    transferChain rels .termination .supported = .undetermined ∧
    ∃ S₀ Sₙ : Sys, RealizesChain rels S₀ Sₙ ∧
      statusOf S₀ .termination specAtom0 = .supported ∧
      statusOf Sₙ .termination specAtom0 = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:222-231
theorem cex_cospan_without_capture_ok :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := fun _ => .error ()
    let lower : Nat → Nat := id
    LosesNoBehaviourAtInputs bitSem passes 2 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 2)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:298-307
theorem cex_cospan_without_ir_holds :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := id
    cap (runPasses passes 1) = .ok 1 ∧
    LosesNoBehaviourAtInputs bitSem passes 1 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 1 ∧
    SubsetClosed allSafeH ∧
    ¬ allSafeH (bitSem (lower 1)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:268-277
theorem cex_cospan_without_lowerRefines :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := fun _ => 1
    cap (runPasses passes 0) = .ok 0 ∧
    LosesNoBehaviourAtInputs bitSem passes 0 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 0)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:253-262
theorem cex_cospan_without_overApproxOnOk :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := fun _ => .ok 0
    let lower : Nat → Nat := id
    cap (runPasses passes 2) = .ok 0 ∧
    LosesNoBehaviourAtInputs bitSem passes 2 ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 2)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:238-247
theorem cex_cospan_without_prepass_no_loss :
    let passes : List (Nat → Nat) := [fun _ => 0]
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := id
    cap (runPasses passes 2) = .ok 0 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 2)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:283-292
theorem cex_cospan_without_subsetClosed :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := fun _ => 0
    cap (runPasses passes 2) = .ok 2 ∧
    LosesNoBehaviourAtInputs bitSem passes 2 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    bothBranchesH (bitSem 2) ∧
    ¬ bothBranchesH (bitSem (lower 2)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:129-137
theorem cex_exhaustifiedOnly_unsound_without_undetermined :
    let E : WorldClaim Bool := fun b => b = true
    let M : WorldClaim Bool := fun b => b = true
    let S_ext : WorldClaim Bool := fun b => b = false
    EntailsEv E M ∧
    ¬ UndeterminedEv E S_ext ∧
    DisclaimerSafe E M S_ext .bareOnly ∧
    EntailsEv E (exhaustifiedOnlyReading M S_ext) ∧
    ¬ NeitherNorDisclaimerSafe E M S_ext := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:99-103
theorem cex_exhaustifiedOnly_without_model_entailed :
    let E : WorldClaim Bool := fun _ => True
    let M : WorldClaim Bool := fun b => b = true
    let S_ext : WorldClaim Bool := fun _ => False
    ContradictsEv E S_ext ∧ ¬ EntailsEv E (exhaustifiedOnlyReading M S_ext) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:243-247
theorem cex_licensedTransfer_iff_without_nonDegen :
    licensedTransfer false [.certFaithfulSoundPinned] .univSafety .supported ≠ .supported ∧
    ∀ S₀ Sₙ : Sys, RealizesUnderTCB false [.certFaithfulSoundPinned] S₀ Sₙ →
      statusOf S₀ .univSafety specConstTrue = .supported →
      statusOf Sₙ .univSafety specConstTrue = .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:247-252
theorem cex_lookup_without_consistent :
    let L : ImplChecker Nat Bool → Prop := fun chk => CheckerSound (· = 0) chk.run
    let c : Nat → Bool := fun n => n == 0
    ImplExtensionalLaw L ∧
    L ⟨true, c⟩ ∧
    ¬ L ⟨false, lookupWrapper [(1, true)] c⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:236-241
theorem cex_lookup_without_extensional :
    let L : ImplChecker Nat Bool → Prop := fun chk => chk.code = true
    let c : Nat → Bool := fun n => n == 0
    TableConsistentWith [(0, true)] c ∧
    L ⟨true, c⟩ ∧
    ¬ L ⟨false, lookupWrapper [(0, true)] c⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:263-268
theorem cex_lookup_without_law :
    let L : ImplChecker Nat Bool → Prop := fun _ => False
    let c : Nat → Bool := fun n => n == 0
    ImplExtensionalLaw L ∧
    TableConsistentWith [(0, true)] c ∧
    ¬ L ⟨false, lookupWrapper [(0, true)] c⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:112-116
theorem cex_neitherNor_without_model_entailed :
    let E : WorldClaim Bool := fun _ => True
    let M : WorldClaim Bool := fun b => b = true
    let S_ext : WorldClaim Bool := fun b => b = false
    UndeterminedEv E S_ext ∧ ¬ NeitherNorDisclaimerSafe E M S_ext := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:653-655
theorem cex_posShape_distinct_without_ne :
    ¬ ∃ rel : BoundaryRel,
        transfer rel .univSafety .supported ≠ transfer rel .univSafety .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:69-75
theorem cex_refutation_not_fullPremise_without_hholds :
    let sq : Sequent Nat 1 1 := {
      ctxHyps := fun _ x => x < 5
      badHyps := fun _ x => x = 3
      goal := fun _ => False
    }
    (∀ x, sq.goal x ↔ False) ∧ ¬ sq.Holds ∧ sq.FullPremiseNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:58-64
theorem cex_refutation_not_fullPremise_without_href :
    let sq : Sequent Nat 1 1 := {
      ctxHyps := fun _ x => x < 5
      badHyps := fun _ x => x = 3
      goal := fun _ => True
    }
    sq.Holds ∧ sq.FullPremiseNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1609-1615
theorem cex_sepMatrix_subdiagonal_without_lt :
    let i : Fin 5 := ⟨0, by omega⟩
    ¬ (i.1 < i.1) ∧
    ¬ ∃ src tgt : Sys,
        Realizes (sepRel i) src tgt ∧
        statusOf src (sepShape i) specAtom0 = .supported ∧
        statusOf tgt (sepShape i) specAtom0 = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1657-1666
theorem cex_sharp_without_definite :
    NonDegen .univSafety specAtom0 ∧
    transfer .none .univSafety .undetermined = .undetermined ∧
    ¬ ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
        Realizes .none src₁ tgt₁ ∧
        Realizes .none src₂ tgt₂ ∧
        statusOf src₁ .univSafety specAtom0 = .undetermined ∧
        statusOf src₂ .univSafety specAtom0 = .undetermined ∧
        statusOf tgt₁ .univSafety specAtom0 = .supported ∧
        statusOf tgt₂ .univSafety specAtom0 = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1641-1650
theorem cex_sharp_without_nonDegen :
    Status.Definite .supported ∧
    transfer .none .univSafety .supported = .undetermined ∧
    ¬ ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
        Realizes .none src₁ tgt₁ ∧
        Realizes .none src₂ tgt₂ ∧
        statusOf src₁ .univSafety specConstTrue = .supported ∧
        statusOf src₂ .univSafety specConstTrue = .supported ∧
        statusOf tgt₁ .univSafety specConstTrue = .supported ∧
        statusOf tgt₂ .univSafety specConstTrue = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1672-1681
theorem cex_sharp_without_undetermined :
    NonDegen .univSafety specAtom0 ∧
    Status.Definite .supported ∧
    ¬ ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
        Realizes (.lockStepSim .s2m) src₁ tgt₁ ∧
        Realizes (.lockStepSim .s2m) src₂ tgt₂ ∧
        statusOf src₁ .univSafety specAtom0 = .supported ∧
        statusOf src₂ .univSafety specAtom0 = .supported ∧
        statusOf tgt₁ .univSafety specAtom0 = .supported ∧
        statusOf tgt₂ .univSafety specAtom0 = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:111-118
theorem cex_suite_barrier_without_invariant :
    let good : Nat → Prop := fun n => n % 2 = 0
    let c : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun d => d 2 = true
    CheckerSound good c ∧
    L c ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) ∧
    ¬ L (suiteAllowlist [0] c) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:125-132
theorem cex_suite_barrier_without_law :
    let good : Nat → Prop := fun n => n % 2 = 0
    let c : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun _ => False
    CheckerSound good c ∧
    SuiteSoundInvariant good [0] L ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) ∧
    ¬ L (suiteAllowlist [0] c) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:137-144
theorem cex_suite_barrier_without_outside_witness :
    let good : Nat → Prop := fun n => n = 0
    let c : Nat → Bool := fun n => n == 0
    let L : (Nat → Bool) → Prop := fun _ => True
    CheckerSound good c ∧
    SuiteSoundInvariant good [0] L ∧
    L c ∧
    suiteAllowlist [0] c = c := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:86-94
theorem cex_suite_barrier_without_sound :
    let good : Nat → Prop := fun n => n % 2 = 0
    let L : (Nat → Bool) → Prop := fun d => ¬ CheckerSound good d
    let c : Nat → Bool := fun _ => true
    SuiteSoundInvariant good [0] L ∧
    L c ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ good p ∧ c p = true) ∧
    ¬ L (suiteAllowlist [0] c) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:532-534
theorem cex_transfer_sound_without_realizes :
    ¬ (transfer .termRoundTrip .univSafety (statusOf (constSys valTrue) .univSafety specAtom0)).le
        (statusOf (constSys valFalse) .univSafety specAtom0) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:159-163
theorem cex_transferChain_iff_without_nonDegen :
    transferChain [.none] .univSafety .supported ≠ .supported ∧
    ∀ S₀ Sₙ : Sys, RealizesChain [.none] S₀ Sₙ →
      statusOf S₀ .univSafety specConstTrue = .supported →
      statusOf Sₙ .univSafety specConstTrue = .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1739-1745
theorem cex_transferIff_sound_without_realizes :
    let src := constSys valTrue
    let tgt := constSys valFalse
    let out := transferIff .termRoundTrip (.univSafety, .existWitness)
      (statusOf src .univSafety specAtom0, statusOf src .existWitness specAtom1)
    ¬ (out.1.le (statusOf tgt .univSafety specAtom0) ∧
       out.2.le (statusOf tgt .existWitness specAtom1)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:209-213
theorem cex_trust_triple_without_accepted :
    CertFaithful boolHonestVerifier true ∧
    CertSemSound boolHonestVerifier true ∧
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 0 ∧
    ¬ ∃ φ, boolHonestVerifier.official 0 = some φ ∧ boolHonestVerifier.valid φ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:167-171
theorem cex_trust_triple_without_faithful :
    CertSemSound boolUnfaithfulVerifier () ∧
    TablePinned boolUnfaithfulVerifier.official boolUnfaithfulVerifier.official 0 ∧
    acceptsNamed boolUnfaithfulVerifier () boolUnfaithfulVerifier.official () 0 = true ∧
    ¬ ∃ φ, boolUnfaithfulVerifier.official 0 = some φ ∧ boolUnfaithfulVerifier.valid φ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:193-198
theorem cex_trust_triple_without_pinned :
    let shipped : Nat → Option Bool := fun _ => some true
    CertFaithful boolHonestVerifier true ∧
    CertSemSound boolHonestVerifier true ∧
    acceptsNamed boolHonestVerifier true shipped () 0 = true ∧
    ¬ ∃ φ, boolHonestVerifier.official 0 = some φ ∧ boolHonestVerifier.valid φ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:180-184
theorem cex_trust_triple_without_semSound :
    CertFaithful boolHonestVerifier false ∧
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 0 ∧
    acceptsNamed boolHonestVerifier false boolHonestVerifier.official () 0 = true ∧
    ¬ ∃ φ, boolHonestVerifier.official 0 = some φ ∧ boolHonestVerifier.valid φ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:270-273
theorem cex_unwarranted_collapse_without_nonDegen :
    ¬ ∃ S₀ Sₙ : Sys, RealizesUnderTCB false [] S₀ Sₙ ∧
        statusOf S₀ .univSafety specConstTrue = .supported ∧
        statusOf Sₙ .univSafety specConstTrue = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:343-348
theorem cex_warnAdjudicate_without_exact_adjudicator :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun _ => false
    let adj : Bool → Bool := fun _ => false
    ZeroFalseAccept P Q ∧
    ¬ ZeroLockout P (warnAdjudicateGate Q adj) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:356-361
theorem cex_warnAdjudicate_without_sound_fastPath :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun _ => true
    let adj : Bool → Bool := fun b => b
    ExactAdjudicatorOnWarnings P Q adj ∧
    ¬ ZeroFalseAccept P (warnAdjudicateGate Q adj) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:385
theorem checkerSound_neg : ¬ CheckerSound (fun n : Nat => n = 0) (fun _ => true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:382
theorem checkerSound_pos : CheckerSound (fun n : Nat => n = 0) (fun n => n == 0) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:368-374
def constSys (v : Valuation) : Sys where
  State := Unit
  init := fun _ => True
  step := fun _ _ => True
  val := fun _ => v
  init_nonempty := ⟨(), trivial⟩
  step_total := fun _ => ⟨(), trivial⟩
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:466
theorem contradictsEv_neg : ¬ ContradictsEv (fun _ : Bool => True) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:463
theorem contradictsEv_pos : ContradictsEv (fun b : Bool => b = true) (fun _ => False) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:87-95
theorem cospan_sys_hyperSubsetClosed_transfer (s0 ir exec : Sys) (P : Spec)
    (passes : List (Sys → Sys)) (cap : Sys → Except Unit Sys) (lower : Sys → Sys)
    (hok : cap (runPasses passes s0) = .ok ir)
    (hpass : LosesNoBehaviourAtInputs HasTrace passes s0)
    (hcap : OverApproxOnOk HasTrace HasTrace cap)
    (hlow : LowerRefinesAt HasTrace HasTrace lower s0)
    (hexec : lower s0 = exec)
    (hir : EvalShape .hyperSubsetClosed ir P) :
    EvalShape .hyperSubsetClosed s0 P ∧ EvalShape .hyperSubsetClosed exec P := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:78-79
theorem cospanSysWitness_iff_traceIncl (ir exec : Sys) :
    CospanSysWitness ir exec ↔ TraceIncl exec ir := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:160-162
theorem ctxNonVacuous_neg :
    ¬ ({ ctxHyps := fun _ _ => False, badHyps := fun _ _ => True, goal := fun _ => False } :
        Sequent Nat 1 1).CtxNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:159
theorem ctxNonVacuous_pos : natBoundRefutation.CtxNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:94-97
theorem denylist_complement_sound_on_closed_universe (univ allow used : List AxiomId)
    (hclosed : OnlyDeclaredAxioms univ used)
    (hacc : denylistAccepts (univ.filter (fun a => !allow.contains a)) used = true) :
    OnlyDeclaredAxioms allow used := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:227
theorem denylistAccepts_neg : denylistAccepts [2, 3] [0, 2] = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:226
theorem denylistAccepts_pos : denylistAccepts [2, 3] [0, 1] = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:192-198
theorem determinizing_stage_breaks_markovian_completeness :
    transfer (.traceRefine .s2m) .existWitness .supported = .undetermined ∧
    ∀ (S₀ S₁ S₂ : Sys) (P : Spec),
      (TraceIncl S₀ S₁ ∧ TraceDeterministic S₁) →
      Realizes (.traceRefine .s2m) S₁ S₂ →
      statusOf S₀ .existWitness P = .supported →
      statusOf S₂ .existWitness P = .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:487-488
theorem disclaimerSafe_neg :
    ¬ DisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b => b = true) .bareOnly := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:483-484
theorem disclaimerSafe_pos :
    DisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b => b = true) .neitherNor := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:460
theorem entailsEv_neg : ¬ EntailsEv (fun _ : Bool => True) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:459
theorem entailsEv_pos : EntailsEv (fun b : Bool => b = true) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:816
theorem evalShape_univSafety_neg : ¬ EvalShape .univSafety (constSys valFalse) specAtom0 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:813
theorem evalShape_univSafety_pos : EvalShape .univSafety (constSys valTrue) specAtom0 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:421-423
theorem evalVal_mono {P : Spec} {v₁ v₂ : Valuation}
    (hmono : ∀ a, v₁ a = true → v₂ a = true) (h : evalVal P v₁ = true) :
    evalVal P v₂ = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:811
theorem evalVal_neg : evalVal specMultiPos (fun a => a == 0) = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:810
theorem evalVal_pos : evalVal specMultiPos (fun a => a == 0 || a == 2) = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:446-447
theorem exactAdjudicatorOnWarnings_neg :
    ¬ ExactAdjudicatorOnWarnings (fun b : Bool => b = true) (fun _ => false) (fun _ => false) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:442-443
theorem exactAdjudicatorOnWarnings_pos :
    ExactAdjudicatorOnWarnings (fun b : Bool => b = true) (fun _ => false) (fun b => b) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:479-480
theorem exhaustifiedOnlyReading_neg :
    ¬ exhaustifiedOnlyReading (fun b : Bool => b = true) (fun _ => True) true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:475-476
theorem exhaustifiedOnlyReading_pos :
    exhaustifiedOnlyReading (fun b : Bool => b = true) (fun _ => False) true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1580-1583
theorem exists_flip_realization (rel : BoundaryRel) (sh : PosShape) (P : Spec) (st : Status)
    (hnd : NonDegen sh P) (hdef : st.Definite) (hund : transfer rel sh st = .undetermined) :
    ∃ src tgt : Sys, Realizes rel src tgt ∧
      statusOf src sh P = st ∧ statusOf tgt sh P = st.flip := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:406-419
def finiteStutterSys (v₀ v₁ : Valuation) : Sys where
  State := Fin 3
  init := fun s => s.1 = 0
  step := fun s s' =>
    (s.1 = 0 ∧ (s'.1 = 1 ∨ s'.1 = 2)) ∨
    (s.1 = 1 ∧ s'.1 = 2) ∨
    (s.1 = 2 ∧ s'.1 = 2)
  val := fun s => if s.1 == 2 then v₁ else v₀
  init_nonempty := ⟨⟨0, by omega⟩, rfl⟩
  step_total := fun s => by
    rcases s with ⟨n, hn⟩
    refine ⟨⟨2, by omega⟩, ?_⟩
    dsimp only
    omega
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:237
theorem freshAxiomOutside_neg : freshAxiomOutside [1, 4] [2] ≠ 4 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:46-47
theorem freshAxiomOutside_not_mem (allow deny : List AxiomId) :
    freshAxiomOutside allow deny ∉ allow ∧ freshAxiomOutside allow deny ∉ deny := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:236
theorem freshAxiomOutside_pos : freshAxiomOutside [1, 4] [2] = 5 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:170
theorem fullPremiseNonVacuous_neg : ¬ natBoundRefutation.FullPremiseNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:165-167
theorem fullPremiseNonVacuous_pos :
    ({ ctxHyps := fun _ x => x < 5, badHyps := fun _ x => x = 3, goal := fun x => x = 3 } :
      Sequent Nat 1 1).FullPremiseNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:309
theorem gateWarrant_neg : gateWarrant false .contradicted ≠ .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:308
theorem gateWarrant_pos : gateWarrant true .contradicted = .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:448
theorem hasTrace_nonempty (S : Sys) : ∃ τ, HasTrace S τ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:409-410
theorem implExtensionalLaw_neg :
    ¬ ImplExtensionalLaw (fun chk : ImplChecker Nat Bool => chk.code = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:405-406
theorem implExtensionalLaw_pos :
    ImplExtensionalLaw (fun chk : ImplChecker Nat Bool => chk.run 0 = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:504
theorem implicatureSafe_neg : ¬ ImplicatureSafe (fun _ => True) [] [] compressedG1Card := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:501
theorem implicatureSafe_pos : ImplicatureSafe (fun _ => True) [] [] fullConjCard := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:522-523
theorem innocentExh_neg :
    ¬ innocentExh (fun _ : Bool => True) [(fun b : Bool => b = true)] true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:513-514
theorem innocentExh_pos :
    innocentExh (fun _ : Bool => True) [(fun b : Bool => b = true)] false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:90-91
theorem isHomFrom_preserves_existWitness {A B : Sys} (h : IsHomFrom A B) (P : Spec) :
    EvalShape .existWitness A P → EvalShape .existWitness B P := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:851-852
theorem isPosBoundedMorphFrom_neg :
    ¬ IsPosBoundedMorphFrom (stepSys valFalse valTrue) (constSys valFalse) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:847
theorem isPosBoundedMorphFrom_pos : IsPosBoundedMorphFrom (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:912-913
theorem isPosBoundedMorphFrom_to_constValTrue (A : Sys) :
    IsPosBoundedMorphFrom A (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:839
theorem isSurjHomFrom_neg : ¬ IsSurjHomFrom (constSys valTrue) (stepSys valTrue valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:836
theorem isSurjHomFrom_pos : IsSurjHomFrom (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:919
theorem isSurjHomFrom_to_constValTrue (A : Sys) : IsSurjHomFrom A (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:315-317
theorem licensedTransfer_neg :
    licensedTransfer false [.certFaithfulSoundPinned, .termRoundTrip] .hyperGeneral .contradicted ≠
      .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:311-313
theorem licensedTransfer_pos :
    licensedTransfer true [.certFaithfulSoundPinned, .termRoundTrip] .hyperGeneral .contradicted =
      .contradicted := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:175-177
theorem lookupWrapper_eq_of_consistent {α : Type} [DecidableEq α]
    (table : List (α × Bool)) (c : α → Bool) (hcons : TableConsistentWith table c) (x : α) :
    lookupWrapper table c x = c x := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:421
theorem lookupWrapper_neg : lookupWrapper [(0, true)] (fun _ : Nat => false) 1 = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:420
theorem lookupWrapper_pos : lookupWrapper [(0, true)] (fun _ : Nat => false) 0 = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:195-198
theorem lookupWrapper_same_code_eq {α Code : Type} [DecidableEq α]
    (code : Code) (c : α → Bool) (table : List (α × Bool))
    (hcons : TableConsistentWith table c) :
    (⟨code, lookupWrapper table c⟩ : ImplChecker α Code) = ⟨code, c⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:141-142
theorem losesNoBehaviourAtInputs_neg :
    ¬ LosesNoBehaviourAtInputs bitSem [fun _ => 0] 2 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:138-139
theorem losesNoBehaviourAtInputs_pos :
    LosesNoBehaviourAtInputs bitSem [fun _ => 2] 0 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:157
theorem lowerRefinesAt_neg : ¬ LowerRefinesAt bitSem bitSem (fun _ => 2) 0 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:154
theorem lowerRefinesAt_pos : LowerRefinesAt bitSem bitSem (fun _ => 0) 2 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:510
theorem minimalSafeBlockers_neg : ¬ MinimalSafeBlockers (fun _ => True) [] [] compressedG1Card := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:507
theorem minimalSafeBlockers_pos : MinimalSafeBlockers (fun _ => True) [] [] fullConjCard := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:133-136
def natBoundRefutation : Sequent Nat 1 1 where
  ctxHyps := fun _ x => x < 2
  badHyps := fun _ x => x = 3
  goal := fun _ => False
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1699-1707
theorem negation_closed_entailment_preserves_contradicted (src tgt : Sys)
    (hlit : ∀ (p : Valuation → Bool),
      ((∀ τ, HasTrace src τ → ∀ n, p (τ n) = true) → (∀ τ, HasTrace tgt τ → ∀ n, p (τ n) = true)) ∧
      ((∃ τ, HasTrace src τ ∧ ∃ n, p (τ n) = true) → (∃ τ, HasTrace tgt τ ∧ ∃ n, p (τ n) = true)))
    (p : Valuation → Bool) :
    (¬ (∀ τ, HasTrace src τ → ∀ n, p (τ n) = true) →
      ¬ (∀ τ, HasTrace tgt τ → ∀ n, p (τ n) = true)) ∧
    (¬ (∃ τ, HasTrace src τ ∧ ∃ n, p (τ n) = true) →
      ¬ (∃ τ, HasTrace tgt τ ∧ ∃ n, p (τ n) = true)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:496-497
theorem neitherNorDisclaimerSafe_neg :
    ¬ NeitherNorDisclaimerSafe (fun b : Bool => b = true) (fun _ => True) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:492-493
theorem neitherNorDisclaimerSafe_pos :
    NeitherNorDisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:729-730
theorem nonDegen_iff_evalVal_false_true (sh : PosShape) (P : Spec) :
    NonDegen sh P ↔ evalVal P valFalse = false ∧ evalVal P valTrue = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:829
theorem nonDegen_MultiPos : NonDegen .hyperSubsetClosed specMultiPos := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:832
theorem nonDegen_neg : ¬ NonDegen .univSafety specConstTrue := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:826
theorem nonDegen_pos : NonDegen .univSafety specAtom0 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:240-247
theorem nonvacuity_allowlist_vs_denylist :
    allowlistAccepts [0, 1] [1, 0] = true ∧
    OnlyDeclaredAxioms [0, 1] [1, 0] ∧
    freshAxiomOutside [1, 4] [2] = 5 ∧
    5 ∉ ([1, 4] : List AxiomId) ∧
    5 ∉ ([2] : List AxiomId) ∧
    denylistAccepts [2] [5] = true ∧
    allowlistAccepts [1, 4] [5] = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:283-287
theorem nonvacuity_cert_trust_triple :
    CertFaithful boolHonestVerifier true ∧
    CertSemSound boolHonestVerifier true ∧
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 1 ∧
    acceptsNamed boolHonestVerifier true boolHonestVerifier.official () 1 = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:166-187
theorem nonvacuity_cospan_transfer :
    let vAlt : Valuation := fun a => a == 1
    let a_ir : Sys := threeBranchSys valFalse valFalse valFalse valTrue vAlt valTrue
    let semS : Nat → TraceSet Trace := fun n =>
      match n with
      | 0 => HasTrace (twoBranchSys valFalse valFalse valFalse valTrue)
      | 1 => HasTrace a_ir
      | _ => HasTrace (constSys valTrue)
    let semExec : Bool → TraceSet Trace := fun b =>
      if b then HasTrace (constSys valTrue) else HasTrace (oneBranchSys valFalse valFalse)
    let passes : List (Nat → Nat) := [fun n => n + 1]
    let cap : Nat → Except Unit Sys := fun n => if n == 1 then .ok a_ir else .error ()
    let lower : Nat → Bool := fun _ => false
    let H : TraceSet Trace → Prop := fun T => ∀ τ, T τ → evalVal specAtom0 (τ 0) = false
    cap (runPasses passes 0) = .ok a_ir ∧
    cap 2 = .error () ∧
    LosesNoBehaviourAtInputs semS passes 0 ∧
    OverApproxOnOk semS HasTrace cap ∧
    LowerRefinesAt semS semExec lower 0 ∧
    SubsetClosed H ∧
    H (HasTrace a_ir) ∧
    ¬ TraceSub (semS 0) (semExec (lower 0)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:487-492
theorem nonvacuity_exact_blockingGate :
    let P : Nat → Prop := fun n => n = 0
    let Q : Nat → Bool := fun n => n == 0
    ZeroLockout P (blockingGate Q) ∧
    ZeroFalseAccept P (blockingGate Q) ∧
    (∀ x : Nat, Q x = true ↔ P x) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:537-542
theorem nonvacuity_exhaustifiedOnly :
    (EntailsEv (fun b : Bool => b = true) (fun b => b = true) ∧
     ContradictsEv (fun b : Bool => b = true) (fun b => b = false)) ∧
    (EntailsEv (fun _ : Bool => True) (fun _ => True) ∧
     UndeterminedEv (fun _ : Bool => True) (fun b : Bool => b = true) ∧
     NeitherNorDisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b : Bool => b = true)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:468-476
theorem nonvacuity_extensional_lookupWrapper :
    let L : ImplChecker Nat Bool → Prop := fun chk => CheckerSound (· = 0) chk.run ∧ chk.run 0 = true
    let c : Nat → Bool := fun n => n == 0
    let table : List (Nat × Bool) := [(0, true)]
    ImplExtensionalLaw L ∧
    TableConsistentWith table c ∧
    L ⟨true, c⟩ ∧
    (true ≠ false) ∧
    (⟨false, lookupWrapper table c⟩ : ImplChecker Nat Bool) ≠ ⟨true, c⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:451-458
theorem nonvacuity_finite_suite_barrier :
    let good : Nat → Prop := fun n => n % 2 = 0
    let c : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun d => CheckerSound good d ∧ d 0 = true
    CheckerSound good c ∧
    SuiteSoundInvariant good [0] L ∧
    L c ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:392-400
theorem nonvacuity_licensedTransfer :
    let rels : List BoundaryRel := [.cospanCaptureLower, .lockStepSim .s2m, .litEntails]
    let S₀ : Sys := twoBranchSys valTrue valTrue valFalse valFalse
    let S₃ : Sys := oneBranchSys valTrue valTrue
    NonDegen .hyperSubsetClosed specAtom0 ∧
    licensedTransfer true rels .hyperSubsetClosed .supported = .supported ∧
    RealizesUnderTCB true rels S₀ S₃ ∧
    statusOf S₀ .hyperSubsetClosed specAtom0 = .supported ∧
    licensedTransfer false rels .hyperSubsetClosed .supported = .undetermined := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:660-664
theorem nonvacuity_posShape_distinct :
    ((⟨1, by omega⟩ : Fin 5).1 < (⟨2, by omega⟩ : Fin 5).1) ∧
    PosShape.termination ≠ PosShape.hyperSubsetClosed ∧
    transfer (.wfStutterSim .s2m) .termination .supported = .supported ∧
    transfer (.wfStutterSim .s2m) .hyperSubsetClosed .supported = .undetermined := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:212-218
theorem nonvacuity_sequent_refutation_and_branches :
    (∀ x, natBoundRefutation.goal x ↔ False) ∧
    natBoundRefutation.Holds ∧
    natBoundRefutation.CtxNonVacuous ∧
    ({ ctxHyps := fun _ _ => True, badHyps := Fin.elim0, goal := fun _ => True } :
      Sequent (Sum Unit Unit) 1 0).NonVacuousOnBranches
      [fun x => x.isLeft = true, fun x => x.isRight = true] := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:1689-1692
theorem nonvacuity_transfer_sharp :
    NonDegen .termination specAtom0 ∧
    Status.Definite .supported ∧
    transfer (.stutterSim .s2m) .termination .supported = .undetermined := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:542-546
theorem nonvacuity_transfer_sound :
    Realizes (.lockStepSim .s2m) (constSys valTrue) (constSys valTrue) ∧
    transfer (.lockStepSim .s2m) .hyperSubsetClosed
      (statusOf (constSys valTrue) .hyperSubsetClosed specAtom0) = .supported ∧
    statusOf (constSys valTrue) .hyperSubsetClosed specAtom0 = .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:346-355
theorem nonvacuity_transferChain :
    let rels : List BoundaryRel := [.cospanCaptureLower, .lockStepSim .s2m, .litEntails]
    let S₀ : Sys := twoBranchSys valTrue valTrue valFalse valFalse
    let S₃ : Sys := oneBranchSys valTrue valTrue
    NonDegen .hyperSubsetClosed specAtom0 ∧
    transferChain rels .hyperSubsetClosed .supported = .supported ∧
    RealizesChain rels S₀ S₃ ∧
    ¬ TraceIncl S₀ S₃ ∧
    statusOf S₀ .hyperSubsetClosed specAtom0 = .supported ∧
    statusOf S₃ .hyperSubsetClosed specAtom0 = .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:500-506
theorem nonvacuity_warnAdjudicate_strict_proxy :
    let P : Nat → Prop := fun n => n % 2 = 0
    let Q : Nat → Bool := fun n => n == 0
    let adj : Nat → Bool := fun n => n % 2 == 0
    P 2 ∧ Q 2 = false ∧
    ExactAdjudicatorOnWarnings P Q adj ∧
    ZeroFalseAccept P Q := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:81-84
theorem nonVacuousOnBranches_implies_ctxNonVacuous {α : Type} {m k : Nat}
    (sq : Sequent α m k) (branches : List (α → Prop))
    (hnv : sq.NonVacuousOnBranches branches) :
    sq.CtxNonVacuous := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:184-186
theorem nonVacuousOnBranches_neg :
    ¬ deadRightBranchSequent.NonVacuousOnBranches
        [fun x => x.isLeft = true, fun x => x.isRight = true] := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:173-176
theorem nonVacuousOnBranches_pos :
    ({ ctxHyps := fun _ _ => True, badHyps := Fin.elim0, goal := fun _ => True } :
      Sequent (Sum Unit Unit) 1 0).NonVacuousOnBranches
      [fun x => x.isLeft = true, fun x => x.isRight = true] := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:12-13
def oneBranchSys (v₀ v₁ : Valuation) : Sys :=
  maskedBranchSys (k := 0) (fun _ => (v₀, v₁))
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:232
theorem onlyDeclaredAxioms_neg : ¬ OnlyDeclaredAxioms [0, 1] [2] := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:229
theorem onlyDeclaredAxioms_pos : OnlyDeclaredAxioms [0, 1] [1] := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:37-39
theorem outside_accepted_good_iff {α : Type} (good : α → Prop) (F : List α) (c : α → Bool)
    (hsound : CheckerSound good c) :
    (∃ p : α, p ∉ F ∧ good p ∧ c p = true) ↔ (∃ p : α, p ∉ F ∧ c p = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:149-150
theorem overApproxOnOk_neg :
    ¬ OverApproxOnOk bitSem bitSem (fun _ => (.ok 0 : Except Unit Nat)) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:146
theorem overApproxOnOk_pos : OverApproxOnOk bitSem bitSem (Except.ok : Nat → Except Unit Nat) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:223-228
theorem positive_control_intensional_code_law_separates :
    let L : ImplChecker Nat Bool → Prop := fun chk => chk.code = true ∧ CheckerSound (· = 0) chk.run
    let c : Nat → Bool := fun n => n == 0
    TableConsistentWith [(0, true)] c ∧
    L ⟨true, c⟩ ∧
    ¬ L ⟨false, lookupWrapper [(0, true)] c⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:68-74
theorem positive_control_postFreeze_probe_separates :
    let good : Nat → Prop := fun n => n % 2 = 0
    let evenChk : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun d => CheckerSound good d ∧ d 2 = true
    CheckerSound good evenChk ∧
    L evenChk ∧
    ¬ L (suiteAllowlist [0] evenChk) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:860
theorem realizes_neg : ¬ Realizes (.embed .m2s) (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:857
theorem realizes_pos : Realizes (.hom .m2s) (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:572
theorem realizes_refl (rel : BoundaryRel) (S : Sys) : Realizes rel S S := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:292-293
theorem realizesChain_neg :
    ¬ RealizesChain [.embed .m2s] (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:288-289
theorem realizesChain_pos :
    RealizesChain [.cospanCaptureLower, .lockStepSim .s2m] (constSys valTrue) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:323-324
theorem realizesUnderTCB_neg :
    ¬ RealizesUnderTCB true [.embed .m2s] (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:319-320
theorem realizesUnderTCB_pos :
    RealizesUnderTCB false [.embed .m2s] (constSys valFalse) (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:420-423
theorem recomputeBlockers_safe_and_minimal {W : Type} (E : WorldClaim W)
    (alts : List (WorldClaim W)) (card : SummaryCard W)
    (hlit : EntailsEv E card.lit) :
    MinimalSafeBlockers E alts (recomputeBlockers E alts card) card := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:556-557
theorem roundTripLink_iff_traceEquiv (src tgt : Sys) :
    RoundTripLink src tgt ↔ TraceIncl src tgt ∧ TraceIncl tgt src := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:136
theorem runPasses_neg : runPasses ([fun n => n + 1] : List (Nat → Nat)) 3 ≠ 3 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:135
theorem runPasses_pos : runPasses ([fun n => n + 1, fun n => n * 2] : List (Nat → Nat)) 3 = 8 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:631
theorem sepRel_neg : sepRel ⟨1, by omega⟩ ≠ .litEntails := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:630
theorem sepRel_pos : sepRel ⟨0, by omega⟩ = .litEntails := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:633
theorem sepShape_neg : sepShape ⟨1, by omega⟩ ≠ .hyperGeneral := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:632
theorem sepShape_pos : sepShape ⟨0, by omega⟩ = .hyperGeneral := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:153-155
theorem sequent_holds_neg :
    ¬ ({ ctxHyps := fun _ x => x < 5, badHyps := fun _ x => x = 3, goal := fun _ => False } :
        Sequent Nat 1 1).Holds := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:146
theorem sequent_holds_pos : natBoundRefutation.Holds := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:353
def specAtom0 : Spec := .atom 0
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:356
def specAtom1 : Spec := .atom 1
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:365
def specConstFalse : Spec := .bot
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:362
def specConstTrue : Spec := .top
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:359
def specMultiPos : Spec := .conj (.atom 0) (.disj (.atom 1) (.atom 2))
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:807
theorem status_definite_neg : ¬ Status.Definite .undetermined := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:806
theorem status_definite_pos : Status.Definite .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:500-501
theorem status_le_iff (s₁ s₂ : Status) :
    Status.le s₁ s₂ ↔ s₁ = .undetermined ∨ s₁ = s₂ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:486-487
theorem statusOf_eq_contradicted_iff (S : Sys) (sh : PosShape) (P : Spec) :
    statusOf S sh P = .contradicted ↔ ¬ EvalShape sh S P := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:481-482
theorem statusOf_eq_supported_iff (S : Sys) (sh : PosShape) (P : Spec) :
    statusOf S sh P = .supported ↔ EvalShape sh S P := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:496-497
theorem statusOf_ne_undetermined (S : Sys) (sh : PosShape) (P : Spec) :
    statusOf S sh P ≠ .undetermined := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:377-383
def stepSys (v₀ v₁ : Valuation) : Sys where
  State := Bool
  init := fun b => b = false
  step := fun _ b' => b' = true
  val := fun b => if b then v₁ else v₀
  init_nonempty := ⟨false, rfl⟩
  step_total := fun _ => ⟨true, rfl⟩
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:129
theorem subsetClosed_neg : ¬ SubsetClosed bothBranchesH := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:128
theorem subsetClosed_pos : SubsetClosed allSafeH := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:389
theorem suiteAllowlist_neg : suiteAllowlist [0, 2] (fun n => n % 2 == 0) 4 = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:388
theorem suiteAllowlist_pos : suiteAllowlist [0, 2] (fun n => n % 2 == 0) 2 = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:395-396
theorem suiteSoundInvariant_neg :
    ¬ SuiteSoundInvariant (fun n : Nat => n % 2 = 0) [0] (fun c => c 2 = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:391-392
theorem suiteSoundInvariant_pos :
    SuiteSoundInvariant (fun n : Nat => n % 2 = 0) [0] (fun c => c 0 = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Transfer.lean:554-560
theorem surjHom_breaks_trace_univSafety_and_termination :
    (∃ A B : Sys, IsSurjHomFrom A B ∧
      statusOf A .univSafety specAtom0 = .supported ∧
      statusOf B .univSafety specAtom0 = .contradicted) ∧
    (∃ C D : Sys, IsSurjHomFrom C D ∧
      statusOf C .termination specAtom0 = .supported ∧
      statusOf D .termination specAtom0 = .contradicted) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:236-238
def symmetricCard : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun b => b = true
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:231-233
def symmetricConjCard : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun b => b = true ∧ True
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:417
theorem tableConsistentWith_neg : ¬ TableConsistentWith [(1, true)] (fun n : Nat => n == 0) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:414
theorem tableConsistentWith_pos : TableConsistentWith [(0, true)] (fun n : Nat => n == 0) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:269-270
theorem tablePinned_neg :
    ¬ TablePinned boolHonestVerifier.official (fun _ => some true) 0 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Trust.lean:265-266
theorem tablePinned_pos :
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 1 := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:399-403
def threeBranchSys (a₀ a₁ b₀ b₁ c₀ c₁ : Valuation) : Sys :=
  maskedBranchSys (k := 2) (fun i =>
    if i.1 == 0 then (a₀, a₁)
    else if i.1 == 1 then (b₀, b₁)
    else (c₀, c₁))
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:205-207
theorem tightBadAt_neg :
    ¬ ({ ctxHyps := fun _ _ => False, badHyps := fun _ _ => True, goal := fun _ => False } :
        Sequent Nat 1 1).TightBadAt ⟨0, by omega⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:200
theorem tightBadAt_pos : natBoundRefutation.TightBadAt ⟨0, by omega⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:194-196
theorem tightCtxAt_neg :
    ¬ ({ ctxHyps := fun _ _ => True, badHyps := fun _ _ => False, goal := fun _ => False } :
        Sequent Nat 1 1).TightCtxAt ⟨0, by omega⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Sequent.lean:189
theorem tightCtxAt_pos : natBoundRefutation.TightCtxAt ⟨0, by omega⟩ := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:332-333
theorem traceDeterministic_neg :
    ¬ TraceDeterministic (twoBranchSys valFalse valTrue valFalse valFalse) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:327
theorem traceDeterministic_pos : TraceDeterministic (constSys valTrue) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:125
theorem traceSub_neg : ¬ TraceSub (bitSem 2) (bitSem 0) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Cospan.lean:124
theorem traceSub_pos : TraceSub (bitSem 0) (bitSem 2) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:866
theorem transfer_neg : transfer (.lockStepSim .s2m) .hyperGeneral .supported ≠ .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:865
theorem transfer_pos : transfer (.lockStepSim .s2m) .hyperSubsetClosed .supported = .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:304-306
theorem transferChain_neg :
    transferChain [.cospanCaptureLower, .wfStutterSim .s2m] .hyperSubsetClosed .supported ≠
      .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:300-302
theorem transferChain_pos :
    transferChain [.cospanCaptureLower, .lockStepSim .s2m, .litEntails] .hyperSubsetClosed .supported =
      .supported := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:872-874
theorem transferIff_neg :
    transferIff (.lockStepSim .s2m) (.univSafety, .existWitness) (.supported, .supported) ≠
      (.supported, .supported) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:868-870
theorem transferIff_pos :
    transferIff .termRoundTrip (.univSafety, .existWitness) (.supported, .supported) =
      (.supported, .supported) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:395-396
def twoBranchSys (a₀ a₁ b₀ b₁ : Valuation) : Sys :=
  maskedBranchSys (k := 1) (fun i => if i.1 == 0 then (a₀, a₁) else (b₀, b₁))
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:472
theorem undeterminedEv_neg : ¬ UndeterminedEv (fun b : Bool => b = true) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Compression.lean:469
theorem undeterminedEv_pos : UndeterminedEv (fun _ : Bool => True) (fun b => b = true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Chain.lean:279-283
theorem unwarranted_undetermined_vacuous_agreement (rels : List BoundaryRel) (sh : PosShape)
    (P : Spec) :
    licensedTransfer false rels sh .undetermined = .undetermined ∧
    ∀ S₀ Sₙ : Sys, RealizesUnderTCB false rels S₀ Sₙ →
      statusOf S₀ sh P = .undetermined → statusOf Sₙ sh P = .undetermined := …
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:350
def valFalse : Valuation := fun _ => false
```

```lean
-- lean/Toy/BoundaryLicensing/Basic.lean:347
def valTrue : Valuation := fun _ => true
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:439-440
theorem warnAdjudicateGate_neg :
    warnAdjudicateGate (fun _ : Bool => false) (fun b => b) false = false := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:436-437
theorem warnAdjudicateGate_pos :
    warnAdjudicateGate (fun _ : Bool => false) (fun b => b) true = true := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:430
theorem zeroFalseAccept_neg : ¬ ZeroFalseAccept (fun b : Bool => b = true) (fun _ => true) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:427
theorem zeroFalseAccept_pos : ZeroFalseAccept (fun b : Bool => b = true) (fun _ => false) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:424
theorem zeroLockout_neg : ¬ ZeroLockout (fun b : Bool => b = true) (fun _ => false) := …
```

```lean
-- lean/Toy/BoundaryLicensing/Barriers.lean:423
theorem zeroLockout_pos : ZeroLockout (fun b : Bool => b = true) (fun b => b) := …
```

## Boundaries

### Non-claims

Model–system relation: none proved. These are statements about the formal definitions in this package; they neither establish nor refute the corresponding claims about any compiler, proof assistant, or verification tool. No embedding, abstraction, or simulation is proved between `Toy.BoundaryLicensing` and any external implementation. Each card under `## Findings` lists its result-specific non-claims in full; the cross-cutting non-claims below govern how the fifteen results compose:

- **Epistemic bottom vs. definite verdicts (`single-boundary-transfer-soundness`, `undetermined-cell-sharpness`, `paired-biconditional-transfer-and-unlicensed-converse`):** `Status.le .undetermined s` holds trivially for every `s`, so `transfer rel sh st = .undetermined` imposes no constraint on `tgt` (`transfer_undetermined_sharp` constructs opposite-verdict Kripke realizations on every `.undetermined` cell for non-degenerate positive `Spec`). `statusOf` on `Sys` is classically two-valued (`statusOf_ne_undetermined`). `transferIff` tracks two independent unconditional verdicts `(statusOf src sh.1 P₁, statusOf src sh.2 P₂)` rather than a single material system-level biconditional `EvalShape sh.1 src P₁ ↔ EvalShape sh.2 src P₂` (not proved here).
- **Initialized total Kripke structures, positive formulas, and representative trace schemas (`Basic.lean`, `Transfer.lean`):** Every `Sys` has non-empty initial states (`init_nonempty`) and a total step relation (`step_total`), guaranteeing at least one infinite execution (`hasTrace_nonempty`). `Spec` contains negation-free positive propositional state formulas (`top`, `bot`, `atom`, `conj`, `disj`) and cannot negate a single atom (`evalVal_mono`, `isPosBoundedMorphFrom_to_constValTrue`, `isSurjHomFrom_to_constValTrue`). `BoundaryRel.surjHom` (`IsSurjHomFrom`, without transition back-lifting) fails `.univSafety` and `.termination` (`surjHom_breaks_trace_univSafety_and_termination`), whereas `BoundaryRel.posBoundedMorph` (`IsPosBoundedMorphFrom`) supplies `init` and `step` back-lifting; not all twenty-one `BoundaryRel` rows are pairwise distinct under `transfer` (by inspection of `preservesDefinite`; not proved as a separate theorem here). `EvalShape .hyperSubsetClosed` tests synchronous step-aligned 2-safety observational determinism (`∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)`), so stutter-invariant subset-closed hyperproperties are not refuted under `.wfStutterSim .s2m` (not proved here). On `Sys`, summary links `CertPinnedLink`, `RoundTripLink`, and `CospanSysWitness` reduce to trace equivalence or trace inclusion (`certPinnedLink_iff_traceEquiv`, `roundTripLink_iff_traceEquiv`, `cospanSysWitness_iff_traceIncl`).
- **Pre-capture over-approximation, undefined-behavior preconditions, and decoupled chains (`cospan-capture-and-lowering-subset-closed-transfer`, `uniform-chain-composition-iff`, `operational-tcb-warrant-gating-and-bilateral-collapse`):** `LosesNoBehaviourAtInputs` requires source-to-pass trace inclusion (`TraceSub (semS a) (semS (f a))`, i.e., pass over-approximation rather than undefined-behavior-erasing refinement), and `LowerRefinesAt` requires unconditional `TraceSub (semExec (lower a_src)) (semS a_src)` at `a_src` (which in real compilers typically holds conditionally on undefined-behavior-free inputs; not proved here). `RealizesChain` quantifies existential intermediate systems `S₁, …, Sₙ₋₁ : Sys` without cross-stage coupling invariants, and `RealizesUnderTCB false` agrees vacuously at `st₀ = .undetermined` (`unwarranted_undetermined_vacuous_agreement`) while failing to model directional partial TCB degradation (not proved here).
- **Pinned statement tables, pragmatic scope disclaimers, and branch partitions (`Trust.lean`, `Compression.lean`, `Sequent.lean`):** `cert_trust_triple_sound` establishes `V.valid φ` relative to the fixed rule parameter `R` and single-entry `TablePinned V.official shipped name`, without checking human-intent alignment of `V.official` or unpinned transitive dependencies. Bare `"only"` scope disclaimers are sound when `E` refutes `S_ext` (`exhaustifiedOnly_sound_iff_contradictsEv`) and unsound when `S_ext` is undetermined (`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`), while `NeitherNorDisclaimerSafe E M S_ext` requires both `EntailsEv E M` and `UndeterminedEv E S_ext` (`neitherNorDisclaimerSafe_iff`). Conclusion-dropping preserves literal entailment (`LitEntailsLink`) while breaking stateless inheritance of `ImplicatureSafe` and `MinimalSafeBlockers` (`no_stateless_implicature_transfer_for_compression`, `condPerfection_compression_breaks_minimal_safe_blocker`, `scalarExh_compression_breaks_blocker_minimality`). `Sequent.NonVacuousOnBranches` checks non-emptiness of `ctxHyps` on listed branches without enforcing partition exhaustiveness across `α` or satisfiability of `badHyps`.

### Escape hatches and narrower system classes

- **Narrower system classes and negation-closed formulas (`known not to apply`):** Cell sharpness (`transfer_undetermined_sharp`) constructs general nondeterministic Kripke countermodels (`Sys`) over negation-free positive state formulas (`Spec`). Restricting intermediate systems to `TraceDeterministic` validates existential preservation across `.traceRefine .s2m` (`determinizing_stage_breaks_markovian_completeness`), and closing specifications under negation forces universal entailment to preserve `.contradicted` (`negation_closed_entailment_preserves_contradicted`).
- **Impossibility escape hatches (`known not to apply`):**
  - Finite-denylist impossibility (`no_finite_denylist_enforces_allowlist`) is escaped when identifiers range over a fixed finite closed universe (`denylist_complement_sound_on_closed_universe`) or when exclusion is given by a decidable predicate `AxiomId → Bool` rather than a finite `List AxiomId`.
  - Non-Markovian compression impossibility (`no_stateless_implicature_transfer_for_compression`) is escaped by carrying `(E, alts, card)` and recomputing blockers (`recomputeBlockers_safe_and_minimal`), or by conservatively mapping `.supported` to `.undetermined` in three-valued `Status`.
  - Finite-suite allowlist indistinguishability (`finite_suite_allowlist_barrier`) is escaped by post-freeze or held-out probes outside `F` (`positive_control_postFreeze_probe_separates`) or by universal relational/certificate obligations.
  - Extensional lookup indistinguishability (`extensional_law_admits_lookupWrapper`) is escaped by intensional code or proof-certificate laws (`positive_control_intensional_code_law_separates`, `cert_trust_triple_sound`); when `code₁ = code₂`, `lookupWrapper table c = c` (`lookupWrapper_same_code_eq`) makes the two pairs equal.
  - Blocking-proxy lockout (`blockingGate_locks_out_strict_proxy`) is escaped by conservative fast-path filtering (`ZeroFalseAccept P Q`) routed to exact warning adjudication (`warnAdjudicateGate_zeroLockout_and_sound`).

### Unresolved hypothesis tightness

- **Unknown tightness (`unknown`):** None. Every hypothesis across all fifteen result ledgers (thirty-four hypothesis entries in total) is marked `tight` and paired with a kernel-checked counterexample theorem establishing that all remaining hypotheses hold while the conclusion fails. No target statements were disproved or omitted.

### Not examined

- Quantitative or probabilistic bounds, negated atomic formulas inside `Spec`, deadlocked finite-trace Kripke structures without `step_total`, cross-language trace abstraction maps in `Cospan.lean`, transitive environment closure pinning inside `TablePinned`, fallible or partial warning adjudicators when `P` is undecidable, and human or computational cost of `adj` in `warnAdjudicateGate`.

## Evidence

Observed 2026-11-22. Toolchain: Lean `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub `leanprover/lean4`, `refs/tags/v4.34.1`).

- **Lean kernel check (`execution (Lean kernel check)`):** All 8 library modules (`Trust.lean`, `Basic.lean`, `Transfer.lean`, `Cospan.lean`, `Chain.lean`, `Sequent.lean`, `Compression.lean`, `Barriers.lean`) and root `Toy.lean` build cleanly under `lake build` with `0` warnings and `0` occurrences of `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, or `unsafe`. Across all `918` compiled `Toy.*` declarations audited via `Lean.collectAxioms`, every declaration depends only on a subset of `{propext, Classical.choice, Quot.sound}` (`audit/axioms.json`).
- **What is hashed (`audit/statements.json`):** For every Lean declaration referenced by `results.json` (`350` declarations in total), `audit/statements.json` records `statement_sha256` (the SHA-256 of `toString (repr ci.type)` for the declaration's kernel `ConstantInfo`) and `closure_sha256` (the SHA-256 of the newline-joined sorted array of `name : repr(type)` entries, with ` := repr(value)` appended for non-theorem definitions, over every package-local constant transitively reachable from `ci.type`, excluding theorem proof terms), together with `closure_size`.

### Per-declaration kernel-check and hash record

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- |
| `Toy.BoundaryLicensing.AllBad` | none | `27f466cfef0ef5acaf47afcd3869a508c2b1242b8e6bbbd03a247a0d6487e244` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.AllCtx` | none | `5ba1dc017229f623a75ce6d22adbf83c6ceab77eddf8e97a20bd3aa8d9d4e5bf` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.AxiomId` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.BoundaryRel` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.CertFaithful` | none | `a3d8b7181b8dc86ada9eb20dd38a6e492dafa55b02e46254595a48f6a36ba230` | `d5ad6b6376a7a004e4374818cddfaa4edf4dd245f91cdf32e067752890a7696e` (2) |
| `Toy.BoundaryLicensing.CertPinnedLink` | none | `75210e1f381656c3c72afce5d9bf291047ae0b3ac4e93ba37f6e4d4348a402f5` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.CertSemSound` | none | `a3d8b7181b8dc86ada9eb20dd38a6e492dafa55b02e46254595a48f6a36ba230` | `d5ad6b6376a7a004e4374818cddfaa4edf4dd245f91cdf32e067752890a7696e` (2) |
| `Toy.BoundaryLicensing.CertVerifier` | none | `412163aecffff8a4c98544a4f91b1f50dfbb2217f8b2b1039c0d7dbc3acf1415` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.CheckerSound` | none | `137bee97664788d4358ed8a67e031a569bca947aa5d2ef5bfa6a1182869a4b17` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.ConsistentExcl` | Quot.sound, propext | `4feefed4c45e50ab8dbad3e86535ad9e48514da8dd754a7ba1ba43a5d5af77fa` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.ContradictsEv` | none | `eea4cc927df970b93f6b0781d6e5ceb347ff23c6fbe2ebfb333b299f119b3981` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.CospanSysWitness` | none | `22e7b07d8d6b1ee1b48b67d9265a58e2ab27dd5f8c4499eb056cbf4225fb1ae3` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.DisclaimerLitTrue` | none | `92c52e88ba9e1ace5e8f35512296aeca0784e2122e4a262e08611b73d7f94b50` | `ec7b10e54ee42508ebd17cb171a93f7be2cd5fecea660f449559cf3f57717a98` (5) |
| `Toy.BoundaryLicensing.DisclaimerSafe` | none | `e9ea12a6530e9468dc96e50b12365a77b22963d83ff940aa5d551c159818262a` | `ec7b10e54ee42508ebd17cb171a93f7be2cd5fecea660f449559cf3f57717a98` (5) |
| `Toy.BoundaryLicensing.EntailsEv` | none | `eea4cc927df970b93f6b0781d6e5ceb347ff23c6fbe2ebfb333b299f119b3981` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.EvalShape` | none | `178b65cad4a27c46f5ae0b4e0d8b5e582ee88a3142e118d2449780ea0ada51a1` | `14a9d324bc166ddaf9c6d30e3b54498c3cf5f6d23460f54c136d8c071938ec50` (16) |
| `Toy.BoundaryLicensing.ExactAdjudicatorOnWarnings` | none | `25ba4fe6f8170450de9a0861d5c1a99beda7819ac964311e0cdfb76ba282f45a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.HasTrace` | none | `ff94d255a2e23dc2633def34a8ba25db8fa296042b2c00e59f0c5415feaf16a1` | `99cc5cd976c079b3120a2777f77fffd46d3bcd9acec01fcc8d3034ae3eaf005d` (5) |
| `Toy.BoundaryLicensing.ImplChecker` | none | `39f252632fda763e92284a08f55ba17e5a0250daaf063876ab2385fac80933db` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.ImplExtensionalLaw` | none | `dd62c4510e2d94e129766595cfea4764b8c4aeb37247d4f091139094831b0fd8` | `5ed812cd3c48415b1db59247fa471b41fa57eb2da1b57aa37e511dcdc173d8f3` (2) |
| `Toy.BoundaryLicensing.ImplicatureSafe` | Quot.sound, propext | `48b2295da6c64553ab018630d6b61c74ef2b003c678a5de8d428585437b57165` | `3d2f61bcb718ec763353fdd6befe267ae73e36d33f09d78563f01da8cb40d67a` (6) |
| `Toy.BoundaryLicensing.InnocentlyExcludable` | Quot.sound, propext | `51dc53fd13e266a3c13bd8c9d6f807132fd77dc991fddf749c748d74c8550da2` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.IsEmbedFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.IsExec` | none | `2e44d7f336bd55bc5459067e124981c57cee1243e56f5137e2f91d6bf92bd19e` | `53b71c94c7aff5522d558f9c940a7039a86829848a72119e2f9df2827b77770d` (5) |
| `Toy.BoundaryLicensing.IsHomFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.IsPosBoundedMorphFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.IsSurjHomFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.LitEntailsLink` | none | `75210e1f381656c3c72afce5d9bf291047ae0b3ac4e93ba37f6e4d4348a402f5` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.LockStepSimFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.LosesNoBehaviourAtInputs` | none | `dd7ad9d62f58f6735ccf6d1ce46bcaf4043e767d49b42423b3eb30ee5a5aa3ab` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.LowerRefinesAt` | none | `f1687aa68ec74dcdbe5270a857e0506f9437dea404167694fe4604d1d5bd9dd5` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.MaximalConsistentExcl` | Quot.sound, propext | `4feefed4c45e50ab8dbad3e86535ad9e48514da8dd754a7ba1ba43a5d5af77fa` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.MinimalSafeBlockers` | Quot.sound, propext | `48b2295da6c64553ab018630d6b61c74ef2b003c678a5de8d428585437b57165` | `3d2f61bcb718ec763353fdd6befe267ae73e36d33f09d78563f01da8cb40d67a` (6) |
| `Toy.BoundaryLicensing.NeitherNorDisclaimerSafe` | none | `458caee8f4c0349039a97d99187b0ad12c934fd0210fca5e0abbb1c06e1abbc1` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.NonDegen` | Classical.choice, Quot.sound, propext | `37c322d190494068cad6bb0117d5ef02bbc640be4c7000cb6621c73b68d9de14` | `9e442bf4e10df8ebb205a3539f93d1bee1ad41e338a3a16530cb27be66a43bce` (13) |
| `Toy.BoundaryLicensing.OnlyDeclaredAxioms` | none | `59c321167f961bd24b55f11abba0ba6cc2dfe80d41a6110d7d2d5dba5783c68d` | `5c6e99dbc7d5c999eb03fd3ecf703ec8289ebdfea193f831e7a3a2c9eb989da4` (1) |
| `Toy.BoundaryLicensing.OverApproxOnOk` | none | `7f917c993ea0ee931cfbfbb883eaed7bfee2531ec8f32ec289dc0624184ccfc4` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.PosShape` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.Realizes` | none | `4343d87bfd26a387d927e43888f72a7c9bfc3bf7b60019e932e748ff5fa68762` | `4ecf395058b73629af7798ff9944c6e903e6054ffe325a38293685a86dd6beba` (21) |
| `Toy.BoundaryLicensing.RealizesChain` | none | `0ac14e08416b5bbb306507dd260024b6d6dcfadc306bf590a1f5335a718f88a1` | `4ecf395058b73629af7798ff9944c6e903e6054ffe325a38293685a86dd6beba` (21) |
| `Toy.BoundaryLicensing.RealizesUnderTCB` | none | `2e05dd272541b400921454f092b67cae2ec8559a46cea754d6f8287f05e0dd1e` | `4ecf395058b73629af7798ff9944c6e903e6054ffe325a38293685a86dd6beba` (21) |
| `Toy.BoundaryLicensing.RoundTripLink` | none | `75210e1f381656c3c72afce5d9bf291047ae0b3ac4e93ba37f6e4d4348a402f5` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.ScopeDisclaimer` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.Sequent` | none | `c3a5ac33b5d0ad59c6998bbbab5ad10bceeb843a01aebd203b5af1c945ade931` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.Sequent.CtxNonVacuous` | none | `1d1e14a596c1654102e9506061bccdd7c19596c925d6c3d9ffc0c955482efaa6` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.Sequent.FullPremiseNonVacuous` | none | `1d1e14a596c1654102e9506061bccdd7c19596c925d6c3d9ffc0c955482efaa6` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.Sequent.Holds` | none | `1d1e14a596c1654102e9506061bccdd7c19596c925d6c3d9ffc0c955482efaa6` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.Sequent.NonVacuousOnBranches` | none | `49ceb9d020e8068e65ff318057677fec83c0b056eea290a6caccf6514a1c9a7d` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.Sequent.TightBadAt` | none | `6c1c9f6f4cff9512f2d126725d63c7e4d88e2dc0cc9f3177b848d856f65b0303` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.Sequent.TightCtxAt` | none | `ebc3d0baeb7054bbf5c0660c04a5b3de502164c56226b23ace88dd0977428a67` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.Spec` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.Status` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.Status.Definite` | none | `f8d4fa4fd5460b839901d9e47e633e6e8012fa764d5789fbf45fab64b82e4e94` | `899e390232b3f7fefa97e6f549cadd61f7ab265ae43478d68460d26ada719d7b` (4) |
| `Toy.BoundaryLicensing.Status.le` | propext | `4710188eb9feb4e4c66eaf9e86069c9c2fa8c6ca6da51d68c7ebcb8ebb151bda` | `899e390232b3f7fefa97e6f549cadd61f7ab265ae43478d68460d26ada719d7b` (4) |
| `Toy.BoundaryLicensing.StutterSimFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.SubsetClosed` | none | `2d9cf4d138fb661b84bfde1f7b1393221087b31123dde922fbeba7c9c78d2bf2` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.SuiteSoundInvariant` | none | `b59a01f53e215a76b5b4be831c2f8e48ae6318ff56b615b15d010d8898fabd32` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.SummaryCard` | none | `da46238a3c743dcbbc48f1d0d2464e94469b283ac56bf5ddb75aea16bf58d296` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.SummaryCard.lit` | none | `39a8e674d8a36b6c88c6e2d080df9a9a7f58d8b78170978515d1e13f1e35741f` | `4697e75ecbfb8bfcafc48a3d9032be87b4052e39a32aa40199630aa12891c741` (3) |
| `Toy.BoundaryLicensing.SummaryCard.pragReading` | Quot.sound, propext | `e46417346ea23d8862352873ca1bcd7f678852ef3d3cf3244eb375971af73cb3` | `3d2f61bcb718ec763353fdd6befe267ae73e36d33f09d78563f01da8cb40d67a` (6) |
| `Toy.BoundaryLicensing.Sys` | none | `8c2dfcd107aac381cf7fdb44dab35e922e30295bb40e848486da26728ca08152` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.TableConsistentWith` | none | `121ffff3458ab54ed2170c0674b034339c054351ab2a74ccb9685cd08fdef65e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.TablePinned` | none | `08405a7b90d3bbd9bc2e64264a5219d7215acbbe742627e5c8582bfdc917a31d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.TraceDeterministic` | none | `94a6eb6ee305b61c0042c0278b6c4d792422c3089633583f8687c40c3b915ee8` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.TraceIncl` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.TraceSub` | none | `8d3cf288f1991cb2de0d5f1cc5987c924f76d3c39749c58385a3b3811ae4d9c0` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.UndeterminedEv` | none | `eea4cc927df970b93f6b0781d6e5ceb347ff23c6fbe2ebfb333b299f119b3981` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.Valuation` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.WfStutterSimFrom` | none | `51658d5ab6fbcd2e9f99002a2313a995ce719bdd2f7f5b0276115ac6b5819b27` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.WorldClaim` | none | `da46238a3c743dcbbc48f1d0d2464e94469b283ac56bf5ddb75aea16bf58d296` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.ZeroFalseAccept` | none | `2398892673bda04cfca2a510e156851c4be356c6ddc457a63390e626bd776255` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.ZeroLockout` | none | `2398892673bda04cfca2a510e156851c4be356c6ddc457a63390e626bd776255` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.acceptsNamed` | none | `5b9e05a39db1ae8cb6cb3aea2e422162a25ac2c8136d9c4b833d0b7e3e246bdc` | `d5ad6b6376a7a004e4374818cddfaa4edf4dd245f91cdf32e067752890a7696e` (2) |
| `Toy.BoundaryLicensing.acceptsNamed_neg` | none | `d7c1d7cb759529a56333bc93752703d10e0bbae964077f86b111a2fb233eba4c` | `dad2578a8e9d01fa5e971a8e614dd1ee9feff46eeeaf73d79af77b4e97b220db` (7) |
| `Toy.BoundaryLicensing.acceptsNamed_pos` | none | `98aa9ec22c821ab9624810a3304dfd317d987aac7240d818c412dc5ac42932f4` | `dad2578a8e9d01fa5e971a8e614dd1ee9feff46eeeaf73d79af77b4e97b220db` (7) |
| `Toy.BoundaryLicensing.allBad_neg` | Quot.sound, propext | `5d3e6a838c159ec832ad74aa1156b7bef8d2855cdd488a53e00fc99b7b4cb067` | `a489da64d66bb9ed0ffd8be2e5ca83fdaeff9017df4dc23840fc38ae9929c0b1` (5) |
| `Toy.BoundaryLicensing.allBad_pos` | none | `67e8af87b60f248aa0f543a879196116ef738f7c2d5f39e43fc9327eeeb2e47a` | `a489da64d66bb9ed0ffd8be2e5ca83fdaeff9017df4dc23840fc38ae9929c0b1` (5) |
| `Toy.BoundaryLicensing.allCtx_neg` | Quot.sound, propext | `81de7fb4841ce17c04359500944a68408cdce15d58bfd42adafad1651108efce` | `170d10798064e6e4d3978963b2c850523fb44cad3186f47bbf12855ee19f066f` (5) |
| `Toy.BoundaryLicensing.allCtx_pos` | propext | `dbe6695fa0d14ca683281c79697fbec6b392b4fcaad66f8700a88416debb66ad` | `170d10798064e6e4d3978963b2c850523fb44cad3186f47bbf12855ee19f066f` (5) |
| `Toy.BoundaryLicensing.allSafeH` | none | `37c96eee9b52ed1fb91eb658d21500518529fb85b221ced6bf466e4b3f526a57` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.allowlistAccepts` | none | `15e0872a017f1129fa6e16a42abfa444cce1794eb24f8127f4b521badd87082b` | `5c6e99dbc7d5c999eb03fd3ecf703ec8289ebdfea193f831e7a3a2c9eb989da4` (1) |
| `Toy.BoundaryLicensing.allowlistAccepts_iff_onlyDeclaredAxioms` | Quot.sound, propext | `ae70da00fc8098ec8039de5c0fdebbf587d591f5ec789089d4728cf70caaf135` | `f00b8b8719b69300e1f3ceabb1cd86afddcb097ebbaa99cfab42d1a61033ed79` (3) |
| `Toy.BoundaryLicensing.allowlistAccepts_neg` | none | `9f5a27226b8ea426004eec9d848771eba0fff105a3aed34daad0beda028769d5` | `5b384deee4bcbfd7bb19e8b7a23a2bd19c9d85de38ea18099995e07b65471764` (2) |
| `Toy.BoundaryLicensing.allowlistAccepts_pos` | none | `516780ab94ee53730e28954b1d618a65461dcd837c9405501804bb48bce85fe8` | `5b384deee4bcbfd7bb19e8b7a23a2bd19c9d85de38ea18099995e07b65471764` (2) |
| `Toy.BoundaryLicensing.bitSem` | none | `02ef6b3ab50c0a2254faac7720264d212e3520755728e3a1dbf11dcb2af24a27` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.blockingGate` | none | `61358193554eecccecc6a2b231144d0694528b0208947a0443d06c7352a353ad` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.blockingGate_locks_out_strict_proxy` | none | `ac3e4545db9e30953592b400fd2d57eaceb97627f02e2a0a3e41cf1181a051c8` | `af92f06f418d814add5dfc413f58a6bc7f730d202d8de5d7ec999a44594164af` (2) |
| `Toy.BoundaryLicensing.blockingGate_neg` | none | `5477db7c9f88bca3e25c1f5e42c0b6e6b65b46ef6e5ff9ece889544fc3ac3051` | `fc82c5aabf2cf215c493eba26232667d72e64226168b02821e3b229450723a21` (1) |
| `Toy.BoundaryLicensing.blockingGate_pos` | none | `2e98708a8c1347046f929b2343673870bce12c2410bc341a43cdcdb01a70b4e5` | `fc82c5aabf2cf215c493eba26232667d72e64226168b02821e3b229450723a21` (1) |
| `Toy.BoundaryLicensing.boolHonestVerifier` | none | `949ea7f725c63664e74bfdebb7340dda1212d1db3cc75335715439d92ffd7057` | `d5ad6b6376a7a004e4374818cddfaa4edf4dd245f91cdf32e067752890a7696e` (2) |
| `Toy.BoundaryLicensing.boolUnfaithfulVerifier` | none | `a64e55cf0a744e49b75d4a51526f11638b02dfb3c69bb4678c3552e1a328dc62` | `d5ad6b6376a7a004e4374818cddfaa4edf4dd245f91cdf32e067752890a7696e` (2) |
| `Toy.BoundaryLicensing.bothBranchesH` | none | `37c96eee9b52ed1fb91eb658d21500518529fb85b221ced6bf466e4b3f526a57` | `891a00e3e8ed783ee196f395dd4e673c90e07654d62ae56e46c27e6544c50e84` (1) |
| `Toy.BoundaryLicensing.branch_nonVacuous_blocks_vacuous_branch_false` | none | `6cca0977bec858f81ab148775ec2ef8fb4c9e9c477077fa7bb1d2ff4fbb917f0` | `deb6f52aeef2d4aeddacd7393d16c2d32e5c65965e72f1a8078dc764e3f37cc1` (5) |
| `Toy.BoundaryLicensing.certFaithful_neg` | none | `f8b04f09891fd051371a23a2ebea7ba29ff479d44ff14e4360b3bc3e584b7bb7` | `e5df3ea1bf54426a7186c92ffd21b8b182d6ef7964c3a48216fb1c22b6bf1a51` (6) |
| `Toy.BoundaryLicensing.certFaithful_pos` | Quot.sound, propext | `1888dc2de1a3be14dc2b8e3f1d8d0775a910363bbdc0bfff1c9280e9c75c0183` | `cd5cd40c25c377452898a39f542da8fff5a49f83cd85140190c56767dcc22fac` (6) |
| `Toy.BoundaryLicensing.certPinnedLink_iff_traceEquiv` | none | `ff02dde6d1b687eeb84ae7971ba98c9b877e56d30f60310cf1910ad78f93d309` | `abc587b308b0e8f1c449c49ad1a0be0ec6ee2054a93c065a16b1b970f0fded98` (24) |
| `Toy.BoundaryLicensing.certSemSound_neg` | none | `de8a412a59f5737fa169ee64661fe02e2e365735d51f5369ed23d008474b4fd6` | `3c6f2a3f75a700dc6b5a703a787818422996fe5bce13996fb96dcb7a794a9798` (6) |
| `Toy.BoundaryLicensing.certSemSound_pos` | Quot.sound, propext | `74135ce70991924139677a105ee07baf40f15e989cd4f104fa26c8c2064739bc` | `3c6f2a3f75a700dc6b5a703a787818422996fe5bce13996fb96dcb7a794a9798` (6) |
| `Toy.BoundaryLicensing.cert_trust_triple_sound` | none | `c35810b67a394729a7b5fd3c61359de6803cdf5b574448770bfb20c4453a9f0f` | `01862b253d094b5c6ece783ae0f47141b60b3e8657ec099a802ef4c417fce15c` (11) |
| `Toy.BoundaryLicensing.cex_blocking_lockout_without_proxy_reject` | none | `80970a8f0b2add6384cd036355379deb725453dbd0cc5d861f82367559c26bf3` | `af92f06f418d814add5dfc413f58a6bc7f730d202d8de5d7ec999a44594164af` (2) |
| `Toy.BoundaryLicensing.cex_blocking_lockout_without_valid_witness` | none | `885bf3e554a445ec569e71c46702e7061c7fb10cadfd2eb476cc835c609e7b36` | `af92f06f418d814add5dfc413f58a6bc7f730d202d8de5d7ec999a44594164af` (2) |
| `Toy.BoundaryLicensing.cex_coincidental_truth_on_unlicensed_chain` | Classical.choice, Quot.sound, propext | `7135925b14fa54f0eb290d72e1a6f77bf8bc8b4c64376d7cdc07b298aaef9c9d` | `d311165e58c123024e7ce68fd917247d73fe38eb461bdc767a21109b48fd662b` (114) |
| `Toy.BoundaryLicensing.cex_cospan_without_capture_ok` | none | `085d501df303c0882421f87c0636fc337c049246bcff080e547f14bc5b57f661` | `46cd25d7882f04b65ad37aef8161de3d23c895d6daa079be98c8f281a0490356` (11) |
| `Toy.BoundaryLicensing.cex_cospan_without_ir_holds` | none | `e1f01dfaaacd1b78fde1908ceb2e7bb607181a318f97c768aa002873a5fab944` | `2f0d3c23b4a7138f49cf67c216509e91c61e54040595c4d93c5fb6b5867a6640` (12) |
| `Toy.BoundaryLicensing.cex_cospan_without_lowerRefines` | none | `0768cc4e24823857e9d41aa374321b290cfd1ade6cf42380acaaebe037e01466` | `fb366bd045f618985368772f6a666626ae1196366ca9a0f4b1d6d722e7695942` (11) |
| `Toy.BoundaryLicensing.cex_cospan_without_overApproxOnOk` | none | `d361f5836ddd7eb9649e3361a25a6e0ff1a2b1b7d31595b72ed9d4cdf3d7a35a` | `0b5285a21a45235a12ccb9043d5cf1cf4760cb032642ab250257008d574da749` (11) |
| `Toy.BoundaryLicensing.cex_cospan_without_prepass_no_loss` | none | `cd5378708fdbda960ed73dbdbd7ce6a307321d46715b5fcf5ed6a7cfdfa285e2` | `d2887313179f283777baa7bd166d1f6eb1b0493da0f36118bc0c2464af308c9d` (9) |
| `Toy.BoundaryLicensing.cex_cospan_without_subsetClosed` | none | `3a6586de1b8e1aae86c1c39e51b6e714e35e842ea86baf0901e21127492b5f7d` | `1c3c9eca0feacd94fdab8ad2071497a0d34b2defdf829fca2305f1f407798061` (11) |
| `Toy.BoundaryLicensing.cex_exhaustifiedOnly_unsound_without_undetermined` | propext | `09aedb0aefa85f21022c2bcc34021372b8174755074974c5d76c388d29063d89` | `ecd63bfa4ca8bd555adc1b38dee8f6cdef8d8c6fd59e4e5dc0e0318d607df21b` (16) |
| `Toy.BoundaryLicensing.cex_exhaustifiedOnly_without_model_entailed` | none | `58796ebf7998c00635361d46a745b281ff614a9c4bc4940518cdc2dcb20920c6` | `d6ee8eb3fce8b2ebc10e59f9132f48b00fb8225c73654fc2b93a1fdd46013180` (4) |
| `Toy.BoundaryLicensing.cex_global_ctxNonVacuous_dead_right_branch` | Quot.sound, propext | `bb9ac2ef890f0d322819e04c0479c0646497a3c6a815afd2c5c0329d1feb81d7` | `4710313e32a84c6bf23faccc31ab6da769adcaed5bb87a0579f92e3c8c2b107e` (11) |
| `Toy.BoundaryLicensing.cex_iff_converse_unlicensed` | Classical.choice, Quot.sound, propext | `4583fe95ad878b8ac27c8394fc18eccf809c01f3d3b70b003abc0ec5728d56b1` | `51ac99fc5b25dae9a716fa15fc4d44d5e49a9215dfd4c4a3831ec17669662488` (108) |
| `Toy.BoundaryLicensing.cex_licensedTransfer_iff_without_nonDegen` | Classical.choice, Quot.sound, propext | `6ba0cb9c8f187b35f2b9a81bf26a4ba203d24a90db1ba25bcec67551f955a3d1` | `e645b8de865e23149b6311fdcf523f4cf7815a6c0037aede1ff4c9ffbab95713` (113) |
| `Toy.BoundaryLicensing.cex_lookup_without_consistent` | Quot.sound, propext | `ad910758a9d0d637bb38b272dedc3aa49e03de592b0d6ca0160a5afaf96c3242` | `95a1ea0d8263802bbd55b101e8a1275c96e4a567407f4f781aa061a967d3d7b2` (7) |
| `Toy.BoundaryLicensing.cex_lookup_without_extensional` | propext | `b0b1c5f333d5778dfa5e6a272d58ce2345608c99a80602b7a4a52d55f8a6e9da` | `3841c8423c2e6b00f3106602b38d9649abfb2d26ea1cd8868fdf1f6dfafc6542` (6) |
| `Toy.BoundaryLicensing.cex_lookup_without_law` | propext | `71ab5b711005f15406a6d7a89246c855bfcae891f7f26e26db57220390feb0a4` | `5b647f7081238447d12992bd998467128bfef7d9c51dc443979f0c271e9846ee` (7) |
| `Toy.BoundaryLicensing.cex_neitherNor_without_model_entailed` | propext | `5d2a418a47699928f4de6c9d5f41849cc75fa04b3a9aab96a269dc2704250ee6` | `ecd63bfa4ca8bd555adc1b38dee8f6cdef8d8c6fd59e4e5dc0e0318d607df21b` (16) |
| `Toy.BoundaryLicensing.cex_posShape_distinct_without_ne` | propext | `462d49e1e510be11a66d4616f073b49255baa108df34411cacbcc85d595a6545` | `9ce8b9bc6efb313cfa2fcc0cc09481cc35572c3d3db8fceebf19b8b658a8e05d` (49) |
| `Toy.BoundaryLicensing.cex_refutation_not_fullPremise_without_hholds` | Quot.sound, propext | `5e769e1fdc0eef45064e623839b231080cf38397b198e0fcc421315ae5c83eea` | `951549243f937117d20c968fac54f04fd5d3a6df613d3ede13eb7592243f126a` (9) |
| `Toy.BoundaryLicensing.cex_refutation_not_fullPremise_without_href` | Quot.sound, propext | `e75e460277e27f02579b7c17cc2aaf097a3150ed3b8a5dd1c1505daf9cc4762d` | `951549243f937117d20c968fac54f04fd5d3a6df613d3ede13eb7592243f126a` (9) |
| `Toy.BoundaryLicensing.cex_sepMatrix_subdiagonal_without_lt` | Classical.choice, Quot.sound, propext | `d6e803f755b08427a420035822090a2be947978bc8e7cf40258f6e3ba7a93e85` | `d669daea13023fba0b59df0cb31fa7fa5bbfed004623ea161f4ed059a26fd8cf` (94) |
| `Toy.BoundaryLicensing.cex_sharp_without_definite` | Classical.choice, Quot.sound, propext | `b5c9f2a2024ec1fda21a6a1c633e52d68280519dcd53e5a2685044756d7a7e40` | `e3ec82c8beda0f36b63d338fda2211a29e2ce1cfbfdf767cd201ecfea081f065` (107) |
| `Toy.BoundaryLicensing.cex_sharp_without_nonDegen` | Classical.choice, Quot.sound, propext | `0f30a8b8fbcb139b13392659f1c0ada57e06db2f8c10861c9d5661eb4e3af47d` | `df1b09a94407913871d3195b1955cdb6e053d1ca04674e1a1f05d4998c656e8d` (107) |
| `Toy.BoundaryLicensing.cex_sharp_without_undetermined` | Classical.choice, Quot.sound, propext | `074aea7d01c86194c2a2c91a8d1cc4afab7fd259b0f65d789aee7e6193302b02` | `529da49f3e473c47e09cde61a7278a6ba0725af703ade205dace711fe2122ca4` (92) |
| `Toy.BoundaryLicensing.cex_suite_barrier_without_invariant` | Quot.sound, propext | `521feb7e5072566021b8b671c4506443ba7d49375d07968568cd0f62113c6645` | `98abcf155a91b9a7d0fd17ae83856cbe67dec799d1dd15ca2bbb6c009071192e` (2) |
| `Toy.BoundaryLicensing.cex_suite_barrier_without_law` | Quot.sound, propext | `c6c9dd873d065d965060d627a5afc03dbd94cfa8a91fd3a3c6f13a81f4788e6d` | `602345c6e178365bb8a5d2ee44374cb0bba8ce0a792b1cc3ad629153d3f80e36` (3) |
| `Toy.BoundaryLicensing.cex_suite_barrier_without_outside_witness` | Quot.sound, propext | `b02ffb6dad58ce658631c018d3cd7238ee3cc53da39e20ce0ecc6e69ed107d9f` | `602345c6e178365bb8a5d2ee44374cb0bba8ce0a792b1cc3ad629153d3f80e36` (3) |
| `Toy.BoundaryLicensing.cex_suite_barrier_without_sound` | Quot.sound, propext | `ab3a3c01d2b1ad6e78bc80d9a9e612073631ddf5f0f6cf51c317833cf9aaabde` | `602345c6e178365bb8a5d2ee44374cb0bba8ce0a792b1cc3ad629153d3f80e36` (3) |
| `Toy.BoundaryLicensing.cex_transferChain_iff_without_nonDegen` | Classical.choice, Quot.sound, propext | `8293fc99808e13b9f3ec3ca90e170c684ea3ebb0c1310067d6699a71700e3ca2` | `ef71e65668bc4b5cfabaae7608e056493c1df78162c1113a9da76b58445b5cb1` (110) |
| `Toy.BoundaryLicensing.cex_transferIff_sound_without_realizes` | Classical.choice, Quot.sound, propext | `dfbfc78c38692570de20e0544e9e02eb706ec4644e8be77179beeab4a7ba2cf4` | `ce820ae9f7f1bcda71eff77a72838c5cee49e0ac2cb095ef9951201624102754` (89) |
| `Toy.BoundaryLicensing.cex_transfer_sound_without_realizes` | Classical.choice, Quot.sound, propext | `1b08fe07ff8594f8f6b6da2d4a302ed34e37b740656182949ac5d7c7b017f07d` | `0a37c0418f06c514cbd18b2c2333cc3dec25a42540845933faa492210a453e44` (87) |
| `Toy.BoundaryLicensing.cex_trust_triple_without_accepted` | Quot.sound, propext | `47423cf0c9c873e5efd84cd7d93090d8cecab545c44cfa614ecd677b97965384` | `ba04594dc489573d524d09b9d93deacdfed6c9ddd4b073a0edbf08fec0096648` (10) |
| `Toy.BoundaryLicensing.cex_trust_triple_without_faithful` | propext | `8471e63fbea427b8c0b624aaf93d835d9dd888d5ec7bcfd6dd2e6550c1f82d64` | `d34065b3891834b83e5eb3019b571dde51b22d31b56745daa94aa59419571629` (11) |
| `Toy.BoundaryLicensing.cex_trust_triple_without_pinned` | Quot.sound, propext | `fdc884e3e5a0c938009915a65c7be220e5a0ef5e6c9e55028ddb44f1546db747` | `c96fb1308b4652c48993c257bfd443b739c8128f20f2d7cdde54270da0b5f4cc` (11) |
| `Toy.BoundaryLicensing.cex_trust_triple_without_semSound` | Quot.sound, propext | `18db0e6e04142df87631fb1955b2533baf31128ef12fe7ffbbc92652e0055bfe` | `ea1c112489983217504e05c637674bf8791d7259156cdb5f5fcfc7356211fe35` (11) |
| `Toy.BoundaryLicensing.cex_unwarranted_collapse_without_nonDegen` | Classical.choice, Quot.sound, propext | `67fe7856f5c20a05cd11f9dd22c2e376b9b47a1351bceab231d5c44db88af8a3` | `262d8d53aa4e5948b31dff881998bca71e095f27ec8142a7388b1be5b71dbc77` (94) |
| `Toy.BoundaryLicensing.cex_warnAdjudicate_without_exact_adjudicator` | none | `2c380da9883fe7005d7debe57709d89cb24eacb3ba32d78364cef53d0240383b` | `ecb5e2c8ce06a66e579bd2533afb9e73a02d89dce42b203937c49f62d50fdfe4` (3) |
| `Toy.BoundaryLicensing.cex_warnAdjudicate_without_sound_fastPath` | none | `b233ea351fbb44d96c6b4a5f2c140c533e926ca1a420391c3ca3c02a5260a27f` | `7f5a0ca0b70f589a6bd83491ad1c59286ce88ac74f98e51e03cda19556774770` (3) |
| `Toy.BoundaryLicensing.checkerSound_neg` | Quot.sound, propext | `acd6b549a24421011b3de5e52c65a1b4ae8af5b32da066195a88f25be4737bb0` | `9b9349fcf67387ae89f39c0d87a7d1c046e14bdb0dc5b90e18a0f90b782d1708` (1) |
| `Toy.BoundaryLicensing.checkerSound_pos` | Quot.sound, propext | `d49327ec64eb30761e389fdb2810fa5437b6e814105e4ea1f9eaf94b6e843fe7` | `9b9349fcf67387ae89f39c0d87a7d1c046e14bdb0dc5b90e18a0f90b782d1708` (1) |
| `Toy.BoundaryLicensing.compressedG1Card` | none | `b19829d4ae630b21259503395403a0522c2fdb07163999d4c1f179e330aa5762` | `4697e75ecbfb8bfcafc48a3d9032be87b4052e39a32aa40199630aa12891c741` (3) |
| `Toy.BoundaryLicensing.condPerfection_compression_breaks_minimal_safe_blocker` | Quot.sound, propext | `08a3f10e41c2b458391ba9923330aa47c9fd6cdd48fe5f59fab9a981dfe00f97` | `94e496ad3bc5d147e4b327363aab3273d57201c579690aeb849b401a11291217` (27) |
| `Toy.BoundaryLicensing.constSys` | none | `8dfe1d56f85f10346f2255ba873ec696d5649b9af0935ac6c5068eda786be437` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.contradictsEv_neg` | none | `e70e87634b3ceab72d307331b4f65f8968cabcfb7abd4eeba889cfc2fe468784` | `7b3e9d6b29df34c1f20f1309d2d9d6b973210e28aed70852aea92b5b7d34c375` (2) |
| `Toy.BoundaryLicensing.contradictsEv_pos` | none | `6dca294ad03986622d47e228b9649f176caa240e940053e86379d517f57630a6` | `7b3e9d6b29df34c1f20f1309d2d9d6b973210e28aed70852aea92b5b7d34c375` (2) |
| `Toy.BoundaryLicensing.cospanSysWitness_iff_traceIncl` | none | `d56b49cfb878aeb651078bce5cc4efadc447bd60d0704f597b2d0e5dffe4eb68` | `6389009f44872119a33355b8ec1a83788ca138ccc12ff9eb0559c6801b110d70` (13) |
| `Toy.BoundaryLicensing.cospan_subsetClosed_transfer` | none | `47f2e5cd17cf588af51a772319384f3c118c80d923f1f393a40d21afc5b9ef85` | `0479bac66ddffcb7f7091d66860fff7330c7f7f2c7daef335efb676c35bf46ce` (9) |
| `Toy.BoundaryLicensing.cospan_sys_hyperSubsetClosed_transfer` | none | `638f5adcaa089d9da2a7aad418941d523b102a78217a834888c50e93c1235e8f` | `21efe256f988dd5514940e3e8da12064c725950e7abf8517b59470ec54ae2a14` (43) |
| `Toy.BoundaryLicensing.ctxNonVacuous_neg` | Quot.sound, propext | `7024316c982ec322e85f155821a0b0bd99f5acbd07cbce2d567a276d0f56910b` | `8be596975f9b98649325d2c783fefa3363cb7dada975003f9afdd152fd1c8df5` (5) |
| `Toy.BoundaryLicensing.ctxNonVacuous_pos` | propext | `c540de00e431e81247ee456701396b50f6a3f1f6f5e9168dc7cdeb6f021cf8dc` | `41b473a429f60a33a125d75581f902006f1d75f7c253063daf9cd3c274dcb4a5` (6) |
| `Toy.BoundaryLicensing.deadRightBranchSequent` | none | `28b442f80d4678242c0b00471efcbbc13cd7ffc2ac90c5c143a717f9e0068822` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.denylistAccepts` | none | `827a5218613047c6982b78a02c603ffd54d45b07ee27075919946579a1422d2f` | `5c6e99dbc7d5c999eb03fd3ecf703ec8289ebdfea193f831e7a3a2c9eb989da4` (1) |
| `Toy.BoundaryLicensing.denylistAccepts_neg` | none | `1a4baf65dbab6eaa77c1c5e0bd6ef6e4aa406dc44a9aac6c448fe0fb4d67a0ce` | `4c2aee5ad830a21c73400d569980545a354a3e12628976b3385dfbeeb54f9075` (2) |
| `Toy.BoundaryLicensing.denylistAccepts_pos` | none | `62b935a6e4c0ff58daec73a9284bbf9503c59a9c966317e4a940735d41653ca6` | `4c2aee5ad830a21c73400d569980545a354a3e12628976b3385dfbeeb54f9075` (2) |
| `Toy.BoundaryLicensing.denylist_complement_sound_on_closed_universe` | Quot.sound, propext | `1c9ede4e7cbc6f87324d90913e4fdfe91f2eac34abf833933c8efefb7df82650` | `b9a8ce6fdc615c97b3da22161c3c8533e9f5fec31ef10a4988f93920a37362f3` (3) |
| `Toy.BoundaryLicensing.determinizing_stage_breaks_markovian_completeness` | Classical.choice, Quot.sound, propext | `f6cc26da3459a3bc236b8fb75a64bfd722b2aebb41edb276f5c4911175703e46` | `f303906c6aba0cc0fa2b04065fb4f25c2643c4c2330fb1bd1a4c5e08d8e40e51` (106) |
| `Toy.BoundaryLicensing.disclaimerReadings` | none | `ed6de66e9754b0df93b79bdebaeae0096cef5fbfd14beb703cc9f7a5ce584343` | `ec7b10e54ee42508ebd17cb171a93f7be2cd5fecea660f449559cf3f57717a98` (5) |
| `Toy.BoundaryLicensing.disclaimerSafe_neg` | propext | `f869ab73dfc436078414911d71ca56fcdadfe730428db2c9a6bc6477bfd3e89e` | `a0d0c9256526e5963716825ec34342ab2af0b869ace8b3282fccbde01d473370` (14) |
| `Toy.BoundaryLicensing.disclaimerSafe_pos` | propext | `dfa72eb41de907fbd407aadb430f398f50e298fadbd97924694fbb68830cb354` | `a0d0c9256526e5963716825ec34342ab2af0b869ace8b3282fccbde01d473370` (14) |
| `Toy.BoundaryLicensing.entailsEv_neg` | none | `8b9b5d0a43ffd47e6e5fae381498a381c1b41d6805cfacb8fde708e9885f1815` | `4a9cadd35d2e784263fb94f5ad61a0580ac973870bcf5e609e2a2e5e98587bca` (2) |
| `Toy.BoundaryLicensing.entailsEv_pos` | none | `d678881c6be2f0f326040a33e667dca153edfce30bcbca5b7d74a52a7da6fe0b` | `4a9cadd35d2e784263fb94f5ad61a0580ac973870bcf5e609e2a2e5e98587bca` (2) |
| `Toy.BoundaryLicensing.evalShape_univSafety_neg` | propext | `e851e48a9be9a9baeafd8261f3508a28f320de845ed5d5160798df4103f5f98e` | `a385a83452abb6916744f72f119f6ac9c10bffd656760c07ed89a5d5d302ad72` (40) |
| `Toy.BoundaryLicensing.evalShape_univSafety_pos` | none | `452f587db61a8e589bb86abe4cceb178654aec0a2cce35d850446f3455fa9680` | `a87df308de0507600f3549f78eba98e7555d44a7c9052e0bc289f50bffe2c56f` (40) |
| `Toy.BoundaryLicensing.evalVal` | none | `fdcd551ec4c8b15ce000636c7eb2d3a01fd91117ba7c45d152d98e27db020ed2` | `88e07525f25a7537e0088168866077274ade2f448ea8ae9484445da825227628` (8) |
| `Toy.BoundaryLicensing.evalVal_mono` | propext | `31b7a6269c5072a3267b159f93cfb5bc7e22cb484c802b27b65e646ddac8f1c2` | `c6493eb83e97c40e680fb1dbbc7a5dc69fbe32838da757aba1166c5984af5ec8` (16) |
| `Toy.BoundaryLicensing.evalVal_neg` | none | `fcaea52881c111437b950b32239ee4045cf8ce50b3bb6573ea44981639f5066b` | `df4e2d25485f984cb745b8ab90f76055e11ecac9813fefd95c4bcf0c64a0f718` (17) |
| `Toy.BoundaryLicensing.evalVal_pos` | none | `ef6635b83a9e64c11ccffb40f87db3f6ad7db479fcc06cce51005ebfa49ac4ec` | `df4e2d25485f984cb745b8ab90f76055e11ecac9813fefd95c4bcf0c64a0f718` (17) |
| `Toy.BoundaryLicensing.exactAdjudicatorOnWarnings_neg` | none | `17c5095514348f4f48b40fabae30fbd749e9e88069bd6515402b604f358f5f38` | `742f0a408b9dd2de7accf1835ff17f9dc6db82f9f791581a6d59904ab1ae008c` (1) |
| `Toy.BoundaryLicensing.exactAdjudicatorOnWarnings_pos` | none | `7d6efc25c2f989565b9b4ab44836ef554a1b5f22f9d74b1699e7db2da4ca400a` | `742f0a408b9dd2de7accf1835ff17f9dc6db82f9f791581a6d59904ab1ae008c` (1) |
| `Toy.BoundaryLicensing.exhaustifiedOnlyReading` | none | `d858f84255e67271b99810c238917c4bc008a4f4a71880a498f7f51e90558d78` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.exhaustifiedOnlyReading_neg` | none | `a6dacfb3349b22916d182b7cbfa2f9ad2c44aa9275fc429b8fe5ceecdfed79dc` | `6b0426973e9ac4e59b31e9249a2bfa29374cdfa377f8a7089c5501ef6f2cfd60` (2) |
| `Toy.BoundaryLicensing.exhaustifiedOnlyReading_pos` | none | `4ac9b261cbf1b743187ca4caa2a9cebdf1b16c57cce3de95785e84549c7a9872` | `6b0426973e9ac4e59b31e9249a2bfa29374cdfa377f8a7089c5501ef6f2cfd60` (2) |
| `Toy.BoundaryLicensing.exhaustifiedOnly_sound_iff_contradictsEv` | none | `4b0f3f79fab6dd4d4ad2564ecdb87a3c257d84027e618941f6695edc44cb7116` | `d6ee8eb3fce8b2ebc10e59f9132f48b00fb8225c73654fc2b93a1fdd46013180` (4) |
| `Toy.BoundaryLicensing.exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined` | propext | `a8467a144524005edbc4ade6edb7528fafdffb3362a9c62f6defee6d38e5c71d` | `ecd63bfa4ca8bd555adc1b38dee8f6cdef8d8c6fd59e4e5dc0e0318d607df21b` (16) |
| `Toy.BoundaryLicensing.exists_flip_realization` | Classical.choice, Quot.sound, propext | `1a003f4c533063acb00f2004e3d2231df8b3a929560b326609748d5af58059f7` | `3b978206c4563dd4ebbc34001ea91f3c66dd6b2d30f3931e44a85510582c68e6` (108) |
| `Toy.BoundaryLicensing.extensional_law_admits_lookupWrapper` | propext | `16f0f835d6d3e7000e73ad955c1e3a903ad2b9991b83f508493c613e4a75a4fd` | `5b647f7081238447d12992bd998467128bfef7d9c51dc443979f0c271e9846ee` (7) |
| `Toy.BoundaryLicensing.fin3Alt02` | none | `e208e23a0bd6ed305ee7c36965cc5bdc7b3e9f3a8e976b7a40da79e4201842f8` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.fin3Alt12` | none | `e208e23a0bd6ed305ee7c36965cc5bdc7b3e9f3a8e976b7a40da79e4201842f8` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.finiteStutterSys` | Classical.choice, Quot.sound, propext | `324c655eabeeb2ad5e7022b04db1baa60c35fca85ca749dc95999d0685dab3cb` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.finite_suite_allowlist_barrier` | propext | `82918306bb2996593e47061b6b9846204ac1a1eef495b68df6d2ef629f010c6f` | `602345c6e178365bb8a5d2ee44374cb0bba8ce0a792b1cc3ad629153d3f80e36` (3) |
| `Toy.BoundaryLicensing.freshAxiomOutside` | none | `a18d361fa5884bc84dc84d1fb76fcb29a78d5d62a722e880678bc7948cb3eea5` | `5c6e99dbc7d5c999eb03fd3ecf703ec8289ebdfea193f831e7a3a2c9eb989da4` (1) |
| `Toy.BoundaryLicensing.freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist` | Quot.sound, propext | `e302e5462b07b8b483dcd295a91bb88d67ecbcb3adda0f6928faebe7465cac7c` | `12a2f9886a84348d8be50221750367bf7a3e1c82d104e3eca9013a6d6909be18` (5) |
| `Toy.BoundaryLicensing.freshAxiomOutside_neg` | none | `06fc9a656f2e48b81e6cc3ae26f488d56e71196c4f7fa300a72002c9ba10cb23` | `720a10c1bb49aeeab217e770053003a7b97a83f8da368b765b9b5370af29afe7` (2) |
| `Toy.BoundaryLicensing.freshAxiomOutside_not_mem` | Quot.sound, propext | `afa00af619e842dc21587e0684a374705ca55dba96156f210b4218cb22e7b89e` | `720a10c1bb49aeeab217e770053003a7b97a83f8da368b765b9b5370af29afe7` (2) |
| `Toy.BoundaryLicensing.freshAxiomOutside_pos` | none | `4f9327238a8fd55c90e5c833dff2619ced3fe8e055b5770ad80073d2c45a2af5` | `720a10c1bb49aeeab217e770053003a7b97a83f8da368b765b9b5370af29afe7` (2) |
| `Toy.BoundaryLicensing.fullConjCard` | none | `b19829d4ae630b21259503395403a0522c2fdb07163999d4c1f179e330aa5762` | `4697e75ecbfb8bfcafc48a3d9032be87b4052e39a32aa40199630aa12891c741` (3) |
| `Toy.BoundaryLicensing.fullPremiseNonVacuous_neg` | Classical.choice, Quot.sound, propext | `df3d95f576104c50596aaf10f1d6e72bb27ca7ddcddd32e2a4ca393c07433cb0` | `de18bd8e8e4ec3d9ef163501d3a3aa0db0ec761cfa1e80fdbababaca53d39055` (8) |
| `Toy.BoundaryLicensing.fullPremiseNonVacuous_pos` | Quot.sound, propext | `88d2bcdbba36c2f985512d25497b251bf14f5d11b4dfa28abd8f84e182c71e9a` | `ffde42045e8a3b0643a8ba871978fbb8eba7bdcabb5ce2b52ff93a587ea6f659` (7) |
| `Toy.BoundaryLicensing.gateWarrant` | none | `ef205c4a3f00c68aa4f8b70afa0d928cabc205de22857b9456d9c967faecfd86` | `899e390232b3f7fefa97e6f549cadd61f7ab265ae43478d68460d26ada719d7b` (4) |
| `Toy.BoundaryLicensing.gateWarrant_neg` | none | `395969e517f6ea7c4f21e63274d05fefbc928d501506fd96b6e4f13b2123f340` | `624e32adcfee108884d0280384975242d9a4c057142b829dca4558caf74173d8` (5) |
| `Toy.BoundaryLicensing.gateWarrant_pos` | none | `f1346db16d3de5e0c938c4be98bc459d56a45c39c625be7f794306bd4fd52366` | `624e32adcfee108884d0280384975242d9a4c057142b829dca4558caf74173d8` (5) |
| `Toy.BoundaryLicensing.hasTrace_nonempty` | Classical.choice | `864872d571e07bca9a8bcf95aad9bbe85b267b63e0fbb62f311132d1d2d87f82` | `37e144b581f3112acd474501895c1aac20c508072ae119fd7f4b96fb6e60bec7` (11) |
| `Toy.BoundaryLicensing.implExtensionalLaw_neg` | none | `5c8afeedf513375b7b88c1a72a193f9692a26db69d6cef7e606f2fa1b543cf33` | `4cfd87976d1392075c3fc54f319dbe836c42c9b1d3593abc2f2aef3a0cc6f82f` (5) |
| `Toy.BoundaryLicensing.implExtensionalLaw_pos` | none | `b3ae80942a1cbda6f03464d04e809cd4017bc8e7faafb479392cf766ea2de24d` | `6f4af4294d6db8b5a725dc1c9cbfa82e6c1739b5d9f495258bb9aafb2c02f822` (4) |
| `Toy.BoundaryLicensing.implicatureSafe_neg` | Quot.sound, propext | `8ea38d1a1a145a7a6f2c973338daa5352ed1b217cb19e272a1c2527264ddb4b5` | `2a20458dca680caa90a6fa3020e9b0342347fd53cde330bb0475d37018288cea` (21) |
| `Toy.BoundaryLicensing.implicatureSafe_pos` | Quot.sound, propext | `ca7f2f7d8b7ef3b5219e25bc9453963101a70a0d133974a3fe6a2a219eb573cd` | `bd2a656bafebd1f0a83559acc62bbbdfc1ab570da3b22291903a465a70ae7360` (21) |
| `Toy.BoundaryLicensing.innocentExh` | Quot.sound, propext | `c7a2b063d5f862762945a272263d7cd811bec383106e5916fee5851fc756edcc` | `00edf746f3e86c352b5f1999fe6f21d7d5ff87368368b5e42dbf8585e5e47435` (1) |
| `Toy.BoundaryLicensing.innocentExh_neg` | Quot.sound, propext | `16d2a35ef200de829f45514e3feafbfc751fffc02092bf35e134c902652acba9` | `4959157ce971b7e1042353816b7834322900034c1f6df3e0466c90ca52c3ce4d` (6) |
| `Toy.BoundaryLicensing.innocentExh_pos` | Quot.sound, propext | `35a44f8fa1e4f085063fe6cedbb35647e40c4c21654e809a0ff7795db81b9e30` | `4959157ce971b7e1042353816b7834322900034c1f6df3e0466c90ca52c3ce4d` (6) |
| `Toy.BoundaryLicensing.isHomFrom_preserves_existWitness` | propext | `5b75edf95b790b825d73ecbe74744efdf7311c8dd631689885fd7f90f4c0c264` | `06b801fa0794f9430086b3eacab186eedfc09c4323f4a3c9e8f3e6c5ffda84f0` (36) |
| `Toy.BoundaryLicensing.isPosBoundedMorphFrom_neg` | none | `034c24ec99f1c7a11a9e29c51b54be6c62466a6e13787b0180ff4846fe8c8870` | `a018b06f4eb05477117c7dcc626834ca0dcf7147842df310505af0ae3e5871ad` (17) |
| `Toy.BoundaryLicensing.isPosBoundedMorphFrom_pos` | none | `003dfb11b8cfc56401d843d057169b7e6d462ad086a2abe008509afe1dd73f63` | `8c6aaf5401338f83cae13f234a9f2399041d4d01a039141430b5264055d187e2` (14) |
| `Toy.BoundaryLicensing.isPosBoundedMorphFrom_to_constValTrue` | none | `8b8264b0fa19fed27bce4c8c60f803d320f88db50525e4b29ba1eff9ad252feb` | `4dd56822cc086a4ed645ed67f486b451d1b0741f09fb40f81a4d0f757a499c7f` (13) |
| `Toy.BoundaryLicensing.isSurjHomFrom_neg` | none | `9443d36f81a998e7decf030afdd7edda588850caa210f30e4c8a52e5492368fa` | `dfa511fbb302da335c88a7ff1906e01aa5551e0b42888da42aff42e1b0475b6d` (16) |
| `Toy.BoundaryLicensing.isSurjHomFrom_pos` | none | `201164a60d874e0f68b4a97ac0b45a12cd6a042c1f6c031d1fb3a67a3d1ccf8c` | `07c4b64dbdc6b6ded13b0cd723ec4f1dc0e8df8a634a0e0c11588e73e0a678de` (14) |
| `Toy.BoundaryLicensing.isSurjHomFrom_to_constValTrue` | none | `14a841495913df0e7f52de99ed2bdc2dd2032eebbe7d04d3fa523a5ae0afdae1` | `dd674cd29b15fafbd95c53a68c55d5d4edb471c832c1608efc5ec62343d3fda2` (13) |
| `Toy.BoundaryLicensing.licensedTransfer` | propext | `bf636d1038953ffa89d2ea5cf86f0035c8f635f87534053c89c538503fd6602d` | `108bea8aeee5b245b0abfeda10107d1b10ad3f12bd9bebbbe28383d9ec90860b` (27) |
| `Toy.BoundaryLicensing.licensedTransfer_eq_iff_forall_realizesUnderTCB` | Classical.choice, Quot.sound, propext | `daa0b694f9d20327d08c4965bf67dfaaca92d744413e30fcd0dd27e492e33856` | `4c1bcca2e81bf35a44bf8495b9a8674dc8c3be886192fb3e9b9cfccac461572c` (113) |
| `Toy.BoundaryLicensing.licensedTransfer_neg` | propext | `003ad8224766d72f2c9fb0ca381b51ffd4ddfc3b212b1f727d7f5ffae925d6bd` | `b6d711cb7b1cd3003553e3fed3201c85fa1bffc3a475de85d4143f7a748ab2fd` (52) |
| `Toy.BoundaryLicensing.licensedTransfer_pos` | propext | `e72f93b64ffc348152baff122b53eda25a389a80ab75d97d5b73aef9c0bce81d` | `b6d711cb7b1cd3003553e3fed3201c85fa1bffc3a475de85d4143f7a748ab2fd` (52) |
| `Toy.BoundaryLicensing.lookupWrapper` | none | `e81440d8e237163f86d28a2e36f63e8d5826c558f5d143a48dc856dd59f3b9f6` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.lookupWrapper_eq_of_consistent` | propext | `fe6b3b7b3bb85015f424d0af4e5d7c55e720a89a991baeca23fe2eec2e5b87f3` | `77ad09d8502717e42e6095c27aeb5f5c1990d90de4721d3cf62efcddf704fe45` (3) |
| `Toy.BoundaryLicensing.lookupWrapper_neg` | none | `6fae9fe832853452d3d03238f3588e084e3a0e37a0808e0a77c12c869fca232a` | `0c3e440c68f0d41b0c6e32686371daf495674fece5ef6994a4ada5a15a9cc67a` (2) |
| `Toy.BoundaryLicensing.lookupWrapper_pos` | none | `98f5bd3ed90eccb4a6e12b9a2d6cecd00d6f06230650a2b0dc473f48b15b09bf` | `0c3e440c68f0d41b0c6e32686371daf495674fece5ef6994a4ada5a15a9cc67a` (2) |
| `Toy.BoundaryLicensing.lookupWrapper_same_code_eq` | Quot.sound, propext | `dd7f065c22bf6f3da37fcec460aa33bf8f8ab32b609e00ec64e4d183453e0ffc` | `077d15bc82712b9397274ab1eff1cabbb62a5c9c2a208a416b497c802114191f` (5) |
| `Toy.BoundaryLicensing.losesNoBehaviourAtInputs_neg` | none | `4cb3b5e43e136847957b36f9c403464874bb6e5992a4aba4a788c675014f5e99` | `6fd647c9ee6fbc25cda37a7cccbd50ca692d6f02be9615833b3da3970d9569a4` (7) |
| `Toy.BoundaryLicensing.losesNoBehaviourAtInputs_pos` | none | `0e076a21e4880c06e07d8358dff458d9f22bd45868bdb5a15e44cb9075a95f95` | `6fd647c9ee6fbc25cda37a7cccbd50ca692d6f02be9615833b3da3970d9569a4` (7) |
| `Toy.BoundaryLicensing.lowerRefinesAt_neg` | none | `60441dc4d0d0f3b6b812a11e1cb6d03844844d4bf7eac8feb6b4a222772878a1` | `9ae9a839ed80b8b53feabc98aac2c772d76ddefcc2d80c68c7bdc6b349b2614d` (5) |
| `Toy.BoundaryLicensing.lowerRefinesAt_pos` | none | `53c8f7ec66675a726314daea4a5f30d487eae4be0d68cddcc38285634594a7a0` | `9ae9a839ed80b8b53feabc98aac2c772d76ddefcc2d80c68c7bdc6b349b2614d` (5) |
| `Toy.BoundaryLicensing.minimalSafeBlockers_neg` | Quot.sound, propext | `f6d15a87d231f7e4f5882c8e4f4ad567c482ab6ce959153d4cab2642f94d0e3d` | `9c2bfbfac387ab21f045825cbb6d490ef0af9a00d794730e077722db03c40e2a` (26) |
| `Toy.BoundaryLicensing.minimalSafeBlockers_pos` | Quot.sound, propext | `29b3525989f200fbd1eeaa90d4099728ccc47238b9f3006e4bc71c6e55a54d19` | `2b32035ffadb505adc904b3bc8a050578e42e38b7fa1e471660150d9ab547eb6` (26) |
| `Toy.BoundaryLicensing.natBoundRefutation` | none | `b5f8aeb8a64b0f5c446ed77b0d51a94433b7575549335c8de19d91feecff0731` | `ff5919b756a826cb22537502e08a9875c9ea404f05e47f02b89323d37efed833` (2) |
| `Toy.BoundaryLicensing.negation_closed_entailment_preserves_contradicted` | Classical.choice, Quot.sound, propext | `957578cc1b74e6ff2342800f2e7b5c07ed401b8c23956abb3c436a740fc0ca48` | `37e144b581f3112acd474501895c1aac20c508072ae119fd7f4b96fb6e60bec7` (11) |
| `Toy.BoundaryLicensing.neitherNorDisclaimerSafe_iff` | propext | `94ebb2bef44608b5b9d782c5742e70313335adf9a740524a151e9b673da67a83` | `ecd63bfa4ca8bd555adc1b38dee8f6cdef8d8c6fd59e4e5dc0e0318d607df21b` (16) |
| `Toy.BoundaryLicensing.neitherNorDisclaimerSafe_neg` | propext | `511ed9c0ccac13c01828d3178e78c7411953f30d12ddf019dcb1a30dbcd696e3` | `2ec4e3eb9d8c5d324a5d3b98581e54d832d306dbca0ebeb37ccf22fd33d49581` (15) |
| `Toy.BoundaryLicensing.neitherNorDisclaimerSafe_pos` | propext | `4b8bf685027ced061ae4a1a80d33983aab9afa15bf286973f19d95805eeaf19b` | `2ec4e3eb9d8c5d324a5d3b98581e54d832d306dbca0ebeb37ccf22fd33d49581` (15) |
| `Toy.BoundaryLicensing.no_finite_denylist_enforces_allowlist` | Quot.sound, propext | `d1802256d408787a253735957939453f610850c3652d02aaac5f98dd93ee9f2c` | `b9a8ce6fdc615c97b3da22161c3c8533e9f5fec31ef10a4988f93920a37362f3` (3) |
| `Toy.BoundaryLicensing.no_stateless_implicature_transfer_for_compression` | Quot.sound, propext | `1d7950b9fc58b049ef3d35fd171bd6e2b836c4e4ed01c7e2db67d063f0cbdb70` | `d13abf5b56c9f81378b270265c3fd2525cc0bdc23da621b0e21af511166510bc` (20) |
| `Toy.BoundaryLicensing.nonDegen_MultiPos` | Classical.choice, Quot.sound, propext | `d4b09b5b06be34cc791d8600affc92a1e1cfc962707ff9f968f0e50d98f66fc6` | `9ac49bb1195db3b0b41e975c87b47323a333b856f54f1034769cc4a1ea740beb` (42) |
| `Toy.BoundaryLicensing.nonDegen_iff_evalVal_false_true` | Classical.choice, Quot.sound, propext | `37dfa81f8062b43efcf2ab563bd53107ea7cd3b654561fec8eb05b0001106691` | `8a21fa136b20e021b766b15dc73f0eab40d6980a59c2d57874342080fe13bfa6` (43) |
| `Toy.BoundaryLicensing.nonDegen_neg` | Classical.choice, Quot.sound, propext | `e1a399cb894b72495aa5ecaed6257f0d464258c0d95d6dddc9eef2812882ec13` | `da4a6ab2da3891f6c03b9a6486c85e498f70d221373c07e9652859c906928728` (42) |
| `Toy.BoundaryLicensing.nonDegen_pos` | Classical.choice, Quot.sound, propext | `6a565539ab748c106cc91a6fdfa8ca9a003730fdbe57391e25bb22b5f1ae72f8` | `59906ea93fb34ada995071cc85356d309f9d29c00543eb81e45783887117929c` (42) |
| `Toy.BoundaryLicensing.nonVacuousOnBranches_implies_ctxNonVacuous` | none | `2db2bbc6d8608746a4bd4170dfeeade275e81e795d144ae3bef4abdd864006cf` | `7788188c985366355bfab3e8c290b9bf0c1bd6f96a57a0714b8656d857686cea` (6) |
| `Toy.BoundaryLicensing.nonVacuousOnBranches_neg` | Quot.sound, propext | `61477a0c03221ced5b1691e0bb1750a271261056be4ffb21ffc71629856d5efc` | `33c9d1eb6a6cbdab4f5fe5c512fb71a92412be100cc375f1e5659ce36e81a69b` (6) |
| `Toy.BoundaryLicensing.nonVacuousOnBranches_pos` | propext | `5a216b208caaf7f6405dfd4f8d581d80a73db574a1ee3bb1a2cd3824dc6d8423` | `deb6f52aeef2d4aeddacd7393d16c2d32e5c65965e72f1a8078dc764e3f37cc1` (5) |
| `Toy.BoundaryLicensing.nonvacuity_allowlist_vs_denylist` | Quot.sound, propext | `448a210b3cca3aa44b2aaacd60fa6cce5a32c51eca477855119b54c061cfe2e5` | `12a2f9886a84348d8be50221750367bf7a3e1c82d104e3eca9013a6d6909be18` (5) |
| `Toy.BoundaryLicensing.nonvacuity_cert_trust_triple` | Quot.sound, propext | `c98a551485ace1b808a17eda505630cc79e3d3e446e03b7334e55e6fdd6eb297` | `3d85c4808836fc9df6446235c0a35986f01189d6b7c59d4433fa45e3d73148a3` (12) |
| `Toy.BoundaryLicensing.nonvacuity_cospan_transfer` | Classical.choice, Quot.sound, propext | `ec56fb00e74eee6ffeed627e3eee45e9f1b1fcbb0bfc91418e64fc6c4d148f33` | `734a4fa5a7af4125eb39246d358ebb796bf49f94fc565df2414e9668d9b7310e` (47) |
| `Toy.BoundaryLicensing.nonvacuity_exact_blockingGate` | Quot.sound, propext | `1996f1663dd38e2ef862a523e3e90968158ef7cddba7f487af2a1c23aa111ab0` | `048bc5fe2265561b790ad9868e21bddfd68fae634a0bfd23e3e3fdb755157fa8` (3) |
| `Toy.BoundaryLicensing.nonvacuity_exhaustifiedOnly` | propext | `50c73d2f2eeaae72bbdce48b15c3586887356ccb2e785dc70c22e9443b8037ae` | `ecd63bfa4ca8bd555adc1b38dee8f6cdef8d8c6fd59e4e5dc0e0318d607df21b` (16) |
| `Toy.BoundaryLicensing.nonvacuity_extensional_lookupWrapper` | Quot.sound, propext | `0d18964be9e1acedf209799665e8e26b4bd7d5c9418dd7bbf93d893b524a27a3` | `53ad3876c08bdbf57eb470fb438ff549865f6bc2ac2f88c5bd24a280fa20ae35` (8) |
| `Toy.BoundaryLicensing.nonvacuity_finite_suite_barrier` | Quot.sound, propext | `a1ab1a86add786aa3647f817dd7f3a500a9c3e3c4dbd8c31662ff353d7f06740` | `a35540ddc140e4c1a263f7633853a6db8aea12ff5aba303c8a16c6f21e0e6dd1` (2) |
| `Toy.BoundaryLicensing.nonvacuity_licensedTransfer` | Classical.choice, Quot.sound, propext | `4975320b3ae4e38ecbb68150269c484e17ea931092398ca22265391730712530` | `4919cf82144677309d3ae7aca753aad04de7e6560fc8be2a9e441c9bb7267b83` (121) |
| `Toy.BoundaryLicensing.nonvacuity_posShape_distinct` | Quot.sound, propext | `c65362da1f5524ebee5d78cbf7298f2c7d3764ae6c53e4f3cbdf0c59dc0ff4fe` | `fd6518da1b89e7d3e22065ed3920e1563053e6f472b481c75b2ae33e12d6ea8f` (51) |
| `Toy.BoundaryLicensing.nonvacuity_sequent_refutation_and_branches` | Classical.choice, Quot.sound, propext | `3ab5309ddead983f2ca648031a9570ec91e06fb55cae818a41ada72d1be6e480` | `b30680e5ddcc632de9a91156d76d3348e862900c6a4b5777c28239e04c2f92da` (11) |
| `Toy.BoundaryLicensing.nonvacuity_transferChain` | Classical.choice, Quot.sound, propext | `62c43dc03d5490737ec1c62dcf80ec8f9342b2176d968b9ce866b6688129e5c8` | `4348860be127676e32926a665459de379166983deb8ce6b799c350c7298fc511` (118) |
| `Toy.BoundaryLicensing.nonvacuity_transfer_sharp` | Classical.choice, Quot.sound, propext | `a1ddc30b63eab49d30a74f86195c9a979a1af1576d4eed2a376074341675b55d` | `c96b892ac151e94ee278538e3464b80069350db3228e0106643d8f260d51fd57` (80) |
| `Toy.BoundaryLicensing.nonvacuity_transfer_sound` | Classical.choice, Quot.sound, propext | `18bdb62651b9b3d946a12af229b5bab1292d2cd8257deceae761b4092105735d` | `9d3468d51aaa90850299dda10cb36ba0690f8f5422ab709d0ec6e103e9858bb6` (110) |
| `Toy.BoundaryLicensing.nonvacuity_warnAdjudicate_strict_proxy` | Quot.sound, propext | `857b5b2c63459a5da99a8f9c3893d8d0aa0ee575c40c5937d67900f01a040745` | `0d9c78c9735aea372136daa2bb3ea744d027e1355c92edc77453c90bdc307d10` (2) |
| `Toy.BoundaryLicensing.oneBranchSys` | none | `324c655eabeeb2ad5e7022b04db1baa60c35fca85ca749dc95999d0685dab3cb` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.onlyDeclaredAxioms_neg` | Quot.sound, propext | `8143d8a3016ec7a6ce4abfc9bf7490227ebbfdde65d46c7ce9c5f6dc184269a4` | `0acef53ae8f816133eee9a14377e77abe8f54371eb02c0ef5401d2bfcb99e54c` (2) |
| `Toy.BoundaryLicensing.onlyDeclaredAxioms_pos` | Quot.sound, propext | `92a4308381c93f7fa34d6bfc1af4f71046c712087b366416d47f2f585fdc7051` | `0acef53ae8f816133eee9a14377e77abe8f54371eb02c0ef5401d2bfcb99e54c` (2) |
| `Toy.BoundaryLicensing.outside_accepted_good_iff` | none | `70e3a6c23894cce2966283c8a506f316f3c32274b033c9086e57e0269c2dd506` | `9b9349fcf67387ae89f39c0d87a7d1c046e14bdb0dc5b90e18a0f90b782d1708` (1) |
| `Toy.BoundaryLicensing.overApproxOnOk_neg` | none | `66003c0819881d02f84e000e10b5cf4e15b72c28c5ad0d7356a1c9526a7616bb` | `de00c337acc445570ba8a05d2198ea7ea55ccfb3355b6904d4ac427c7c3d037e` (5) |
| `Toy.BoundaryLicensing.overApproxOnOk_pos` | none | `b360ff6fa9bcbce859971b53b335dac97adb7ade2bd4311868e75a1f264875fa` | `de00c337acc445570ba8a05d2198ea7ea55ccfb3355b6904d4ac427c7c3d037e` (5) |
| `Toy.BoundaryLicensing.posShape_columns_pairwise_distinct` | propext | `4a1f326bf3b0efe1cf25dec329e3535036099bfe446600667db01761aacb836f` | `9ce8b9bc6efb313cfa2fcc0cc09481cc35572c3d3db8fceebf19b8b658a8e05d` (49) |
| `Toy.BoundaryLicensing.positive_control_intensional_code_law_separates` | Quot.sound, propext | `3c84b825e46b7122f11e22ecec1f1d1f84338b64f637bf753a3df8667ec8ca5b` | `cc44bbf15b9bf61d67be0d880cb2be24023d92594a6d768e138746e2f698bfa0` (8) |
| `Toy.BoundaryLicensing.positive_control_postFreeze_probe_separates` | Quot.sound, propext | `2647eb40f35284a3c6b7afecb20eb539c557df75f3c0960613de6510f3def876` | `98abcf155a91b9a7d0fd17ae83856cbe67dec799d1dd15ca2bbb6c009071192e` (2) |
| `Toy.BoundaryLicensing.preservesDefinite` | propext | `7766c9ed1da2814cc9cec8b34f8d12dd549508aea6d190908c8001b4714bbb7a` | `10544f205bc2098b466d4834610b17ac8b41f793f63bb7985544af0e77c20b55` (23) |
| `Toy.BoundaryLicensing.realizesChain_neg` | propext | `1343f030799006979c965fb1c881c700fb6ccab05e4fac3b43ebf0bcb640b2b8` | `96ce8f01c966effd4cfee4aa6f0c52a9d907c8fa5dc0bf639aa06467b812708b` (92) |
| `Toy.BoundaryLicensing.realizesChain_pos` | none | `df3ca891cf4b41316e9511f1c4a5e25647696a6d9322efadc79828b43cbe3038` | `b6baab5791da4cb00c5573cdfd7d3641b3f2b9fac0b9c839ce5892624eeff349` (91) |
| `Toy.BoundaryLicensing.realizesUnderTCB_neg` | propext | `d9b6a885eaf939ffa7394710842f5f17eb913eeaaabe8515aa33da3a768b791c` | `24f8200f6ab7d886eb7a58b5cae29575577e2af2f14f59f689966b65892fe383` (93) |
| `Toy.BoundaryLicensing.realizesUnderTCB_pos` | none | `727962d2a74aca8257c9193c4acdeae5b27812c5aa0eae7d5e9dc06e4f4f7259` | `24f8200f6ab7d886eb7a58b5cae29575577e2af2f14f59f689966b65892fe383` (93) |
| `Toy.BoundaryLicensing.realizes_neg` | propext | `18515f113c52c4e3476c758926ce7941793ad9d3fdca602994312ca12a4db611` | `8a641b9357fdea8d1a089edc74012a71707382ce2ce8e2734de85cfaf56a77e6` (89) |
| `Toy.BoundaryLicensing.realizes_pos` | none | `cc63618f1cd022e1337b4c731b8ec6fdb973318c9049b91a7403a4edad33d5d2` | `8a641b9357fdea8d1a089edc74012a71707382ce2ce8e2734de85cfaf56a77e6` (89) |
| `Toy.BoundaryLicensing.realizes_refl` | none | `659530430deda2756d53bcd8b5bd435952fb50cb100497e5812e0bf53033bd84` | `1eba8dc42722facbf34ce31c1f8ead979975e1617b524a30aec271b473209d93` (84) |
| `Toy.BoundaryLicensing.recomputeBlockers` | Classical.choice, Quot.sound, propext | `6721a3ce7e60e01aba59a9eda36d1b0998994b31efb4f23088b239630e38ccc6` | `3d2f61bcb718ec763353fdd6befe267ae73e36d33f09d78563f01da8cb40d67a` (6) |
| `Toy.BoundaryLicensing.recomputeBlockers_safe_and_minimal` | Classical.choice, Quot.sound, propext | `3c7e732f7a9ef9b669e2e1230bae49bff5869e9da42d99417029a8d12c6c5da4` | `6b34f1e6309d79c6ef6d3408316efdec9a3a3c5c13e691afec8c2e99a7970c1b` (26) |
| `Toy.BoundaryLicensing.refutation_not_fullPremiseNonVacuous` | none | `a35a5a813131f40fd2d72ac72e9cc01befc94797c9b1d00a6f12acc51c59823d` | `951549243f937117d20c968fac54f04fd5d3a6df613d3ede13eb7592243f126a` (9) |
| `Toy.BoundaryLicensing.roundTripLink_iff_traceEquiv` | none | `5cc22c4b867eae428bc01b9873517fa5852a76e215b1f9fe054eef33eae72927` | `30ccb5822e4b5c65422297234570b36a01c76197c70aebdd737876a1d6e7f715` (13) |
| `Toy.BoundaryLicensing.runPasses` | none | `39d48c598a9c6ef69c189f74e3abf6b40cce6fa3e689e781e3c229c3b9b93544` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.runPasses_neg` | none | `194de2367daad8fde2f5960ec52a0f3542f019de6f37c6104f807337f361d09f` | `b94ad20e02901843482c2f00afeb0849de60f921b5bfd6a5c45ccac3ae69960b` (1) |
| `Toy.BoundaryLicensing.runPasses_pos` | none | `87ae7b9872ecbd0b16935a72655a7805ae3737ee5295b59a7ebb741dc3caaa19` | `b94ad20e02901843482c2f00afeb0849de60f921b5bfd6a5c45ccac3ae69960b` (1) |
| `Toy.BoundaryLicensing.scalarExh_compression_breaks_blocker_minimality` | Classical.choice, Quot.sound, propext | `eb96d8f9a39aa350ef721b9f390b4d69b5f90238b298fbb56378fb9986ba0da1` | `37f40ed5ec5f2f60ae8ea57e1567b0fbacc480935c233f7d9837aca56ff6f0a8` (27) |
| `Toy.BoundaryLicensing.sepMatrix_subdiagonal_countermodels` | Classical.choice, Quot.sound, propext | `edd0366bca8c5f58a753114b6a8a304c6138ce5a0fdfb52708b5ae2ac9605467` | `ffc225f7690742920ab0c74da29e270736dbdee806aacb70bafadb7f2cbb0219` (93) |
| `Toy.BoundaryLicensing.sepMatrix_upperTriangular` | propext | `e0273a7049c764c72f501d2f28b43e0cd546ebc71a480d6a0bff637aea1bf72a` | `16de6385590ba015e5bbc8a63189e222a4b33ed838ecdaf129cc432ec6b04e81` (52) |
| `Toy.BoundaryLicensing.sepRel` | propext | `7628480da036aba89d7706d263fa0ce897a65d306694f8e139821a952bf6e82a` | `cf92f04baf1dff943ba132d480d1b9c6a3cb1278e2b082180ef7665316d871b9` (17) |
| `Toy.BoundaryLicensing.sepRel_neg` | Quot.sound, propext | `7d0c22369e465343c55e7a8a2b2e687f8a9b042d979070e9557cd84917b50b71` | `2617c245e7dc11ea6d10ad969900f2a5d02429ccae15589a337dc14eaefd6ed3` (20) |
| `Toy.BoundaryLicensing.sepRel_pos` | Quot.sound, propext | `6eea20bc320ba0bfb5f8f3febb7e9d0046617dc977007e27d5e29252c0958a14` | `0874d9e8edf001ebb4f7878eeea04717e37255e783a229c33182f3d4cc731a7e` (20) |
| `Toy.BoundaryLicensing.sepShape` | propext | `f0cc8234998b8e4e1bbdf9f035317f7e2776f86f97a3eebd70fd54f19b49a1b8` | `08483fd2527452885a825dba9a43bc6ae961cf250a6ed163283135f72d5a0a8f` (6) |
| `Toy.BoundaryLicensing.sepShape_neg` | Quot.sound, propext | `f5aca3b66722049b09e0d1f4e28830870f207640e050bd09f12dec40313a5c49` | `006079f2f593b6fa0de536bed5a8d0070d5358c9b6813441220e44f362d499be` (9) |
| `Toy.BoundaryLicensing.sepShape_pos` | Quot.sound, propext | `7f360c0fe2ba36701ce87bfde8987058915d4be3193e3c954f8ee53de88b415c` | `3faa551f7bc4ef3c300001ccd29b86d60408c39b869c5fa16835add31465d88b` (9) |
| `Toy.BoundaryLicensing.sequent_holds_neg` | Quot.sound, propext | `e5934e1ef05c177fea1bbae8849e8afb81de77602677fa2416d6a329591701e9` | `7836f90d60cb07c5e0f11f2b9e1af50a45eed3ea4f7d078328839249a5234f74` (8) |
| `Toy.BoundaryLicensing.sequent_holds_pos` | Classical.choice, Quot.sound, propext | `27b043e4085d3727bec73756703ae292798cd5fcabd6cfe762a0cbd93c13d67c` | `8b0f75c181d8f9c6f02409b6f7471d95cb31e845ecb8884b3bade38ac1d2bff7` (9) |
| `Toy.BoundaryLicensing.specAtom0` | none | `c3da7cc964972d6e8e8a8c396b498d92e31298c808e636b526d7edd86ade4331` | `b11f49b7c8a55576c539433dc55adf7238786e8c66026507233817283f4b5314` (7) |
| `Toy.BoundaryLicensing.specAtom1` | none | `c3da7cc964972d6e8e8a8c396b498d92e31298c808e636b526d7edd86ade4331` | `b11f49b7c8a55576c539433dc55adf7238786e8c66026507233817283f4b5314` (7) |
| `Toy.BoundaryLicensing.specConstFalse` | none | `c3da7cc964972d6e8e8a8c396b498d92e31298c808e636b526d7edd86ade4331` | `b11f49b7c8a55576c539433dc55adf7238786e8c66026507233817283f4b5314` (7) |
| `Toy.BoundaryLicensing.specConstTrue` | none | `c3da7cc964972d6e8e8a8c396b498d92e31298c808e636b526d7edd86ade4331` | `b11f49b7c8a55576c539433dc55adf7238786e8c66026507233817283f4b5314` (7) |
| `Toy.BoundaryLicensing.specMultiPos` | none | `c3da7cc964972d6e8e8a8c396b498d92e31298c808e636b526d7edd86ade4331` | `b11f49b7c8a55576c539433dc55adf7238786e8c66026507233817283f4b5314` (7) |
| `Toy.BoundaryLicensing.statusOf` | Classical.choice, Quot.sound, propext | `7b8415a230c4f601ed8755db743a60a206ea4288f36edf5c13aaf9905a841257` | `60f9a27211c6a6e24aa9cbc450fc5f29883e37d47688e9f4443489efa82277a5` (20) |
| `Toy.BoundaryLicensing.statusOf_eq_contradicted_iff` | Classical.choice, Quot.sound, propext | `9d1845aedd8a7437c097c71de2864cddbbc3f6f93ffd6a77a846bc1a94e14b20` | `2d6885a8ae1b2956a35102aae4b4b75066834e4d9683ea2b3e374d16c3599b68` (40) |
| `Toy.BoundaryLicensing.statusOf_eq_supported_iff` | Classical.choice, Quot.sound, propext | `30f901aaf3e7e34e0a89e6e022f284bff22374334090e5dd2dd8747392417f39` | `2d6885a8ae1b2956a35102aae4b4b75066834e4d9683ea2b3e374d16c3599b68` (40) |
| `Toy.BoundaryLicensing.statusOf_ne_undetermined` | Classical.choice, Quot.sound, propext | `5acf19fe9044adebc1e61fa501721f9186a2d21d75d1adcb70f4c9568e99c583` | `2d6885a8ae1b2956a35102aae4b4b75066834e4d9683ea2b3e374d16c3599b68` (40) |
| `Toy.BoundaryLicensing.status_definite_neg` | none | `fe01e937b1620ab32030bea5fa63c9cd16231cbd91b4a2cf03d2f2a32f8ba348` | `09a9eb142ccce090ba3222261721ad22dbdf05a04d3bcd40e1848ecb113b0cb3` (5) |
| `Toy.BoundaryLicensing.status_definite_pos` | none | `09777a990822ce8323edb0c6365a3943244f10d75baeb455e7b0b081caf84232` | `09a9eb142ccce090ba3222261721ad22dbdf05a04d3bcd40e1848ecb113b0cb3` (5) |
| `Toy.BoundaryLicensing.status_le_iff` | propext | `3ffe51886da743f198f0d00decfa6c95dd15ddf9ffb01408a3ed088a138796e3` | `1e2084a91a66f6019db07105f4598f15474d4e3d357d9102cc584f2b36681cca` (10) |
| `Toy.BoundaryLicensing.stepSys` | none | `324c655eabeeb2ad5e7022b04db1baa60c35fca85ca749dc95999d0685dab3cb` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.subsetClosed_neg` | none | `ffd13a7d13c4044f177464d25d463bbd7edf4b89672688ef96ac334350bd3c90` | `d04b74a36ba7ecc5e09ba6b1c27b5f502510cebcd6a8577224622b93ec785cb1` (4) |
| `Toy.BoundaryLicensing.subsetClosed_pos` | none | `08c346bcb6898da621316a874dd917aaaa78a9c39c6935f1f013bb50831cd92c` | `9d8d710a833b174a24847e3b04fcda914e8e93adfc9668df359acea25ee6e4cf` (4) |
| `Toy.BoundaryLicensing.suiteAllowlist` | propext | `ae020de904b34ff6fab53f7e4fb7fff4fd60cc57ccd9cbff2b63ca4d37002d28` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.suiteAllowlist_neg` | propext | `9af141a462931f1266470c740ac9bc0d111612c4e8b46d6410e9f04b34974749` | `07065db5c6145a06f3a587b6d8aa8df0791142066061b03f612ffe98b7b7ceb0` (1) |
| `Toy.BoundaryLicensing.suiteAllowlist_pos` | propext | `5e2ad7dcabdcd03e0c4009cb7b6ed601c582bc13b6e11673a17f9e72020a0ff2` | `07065db5c6145a06f3a587b6d8aa8df0791142066061b03f612ffe98b7b7ceb0` (1) |
| `Toy.BoundaryLicensing.suiteSoundInvariant_neg` | Quot.sound, propext | `16f80ef2c0c20aa8adf4b3e2fd5c207256ddf8b14f184cb52cd181445b187aa2` | `a35540ddc140e4c1a263f7633853a6db8aea12ff5aba303c8a16c6f21e0e6dd1` (2) |
| `Toy.BoundaryLicensing.suiteSoundInvariant_pos` | propext | `4e91f4fac24ac497159d51105aa21aa4b9f15967b3affaf02364b9fab97b1fbc` | `a35540ddc140e4c1a263f7633853a6db8aea12ff5aba303c8a16c6f21e0e6dd1` (2) |
| `Toy.BoundaryLicensing.surjHom_breaks_trace_univSafety_and_termination` | Classical.choice, Quot.sound, propext | `1b6dbc5cf7fd992d3018771dc9a0c86a1f2c6449967897886699c6e2c4118e37` | `0afa944331135c579b993968ac41752c99e22ead01b01db74bf94d3f9d101b52` (42) |
| `Toy.BoundaryLicensing.symmetricCard` | none | `b19829d4ae630b21259503395403a0522c2fdb07163999d4c1f179e330aa5762` | `4697e75ecbfb8bfcafc48a3d9032be87b4052e39a32aa40199630aa12891c741` (3) |
| `Toy.BoundaryLicensing.symmetricConjCard` | none | `b19829d4ae630b21259503395403a0522c2fdb07163999d4c1f179e330aa5762` | `4697e75ecbfb8bfcafc48a3d9032be87b4052e39a32aa40199630aa12891c741` (3) |
| `Toy.BoundaryLicensing.tableConsistentWith_neg` | propext | `cb5aa0cba45725b1bc770038d2213f4567abc9810c48ec1437cf38853072e964` | `804425282048b06630c0c7a809856ca0476d730923ee99c388ad5b2bd24cc224` (1) |
| `Toy.BoundaryLicensing.tableConsistentWith_pos` | propext | `17797bf58ff658532014d25cbf38bf951bfd6814f7573a8d50bf13334e77a391` | `804425282048b06630c0c7a809856ca0476d730923ee99c388ad5b2bd24cc224` (1) |
| `Toy.BoundaryLicensing.tablePinned_neg` | Quot.sound, propext | `00d7b7e075c4699d3507cf1640a05a2540faa1c9a6ca4e89f59aa44201ebff4d` | `0a64aa650ec701dbaf424fd0cc110061469f2bc1a1823cd51008b17bdb9843e9` (5) |
| `Toy.BoundaryLicensing.tablePinned_pos` | none | `65c368caac6f8480e545d71530dc77547be519ab3ae3f58874074c2d3ac4f501` | `0a64aa650ec701dbaf424fd0cc110061469f2bc1a1823cd51008b17bdb9843e9` (5) |
| `Toy.BoundaryLicensing.threeBranchSys` | none | `b795d1b331c76d82ac1fbda198e64cf30ccd6405daf3e0345b35370175574e57` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.tightBadAt_neg` | Quot.sound, propext | `490cc546dfc357a2fc9615ad41cef557c0bad5bbcb51f9c2e96b1fe139ab8a61` | `044a04ecc86ec38224e00168247d73cd22a6fbe36f9ff8970a494deb779a9997` (8) |
| `Toy.BoundaryLicensing.tightBadAt_pos` | Quot.sound, propext | `373b5bf6e74579bee4054fae6a8d69ab194e9ef729e1cadf46bf58f0f02e1cd8` | `545aacac2b691c32decc93cd14c1dcdd6bcce527f9d1293c3ef7a0811c1510e1` (9) |
| `Toy.BoundaryLicensing.tightCtxAt_neg` | Quot.sound, propext | `98122a6710edc12370a3ceb8dc339e705bb64b908d98cfc8dd53bb701307d5c8` | `744993d1c8d3e1c3256afee5b73f1995edce56c4c25aed6f2717e53969411d3b` (8) |
| `Toy.BoundaryLicensing.tightCtxAt_pos` | Quot.sound, propext | `3369a1102408f6314b9a0b0eaf80cb813b6945ffde9de3aedd052be681f9bec4` | `d652bd2e22d7f856429abc9933abe106bc71464219b7c190de05b8154304f392` (9) |
| `Toy.BoundaryLicensing.traceDeterministic_neg` | Quot.sound, propext | `9695b22e483517b0cb52468d2ff6c3b7a11028bf0fe431b4e9749f7d2e7facdb` | `d82129f2d76d4f80227b41e6ddeeaa85bdaa676b6fd4db8c14d6815dfa6d3d8a` (18) |
| `Toy.BoundaryLicensing.traceDeterministic_pos` | Quot.sound | `d41bdee8a492d9ac1ee1b415458312c0cf5ebb5cd3cb1989de7f8b8d26ee6e95` | `e82a878ce21696243a0124ac53dd882c7016c3fc6f18fb671d8aa09b8bd8006d` (16) |
| `Toy.BoundaryLicensing.traceSub_neg` | none | `46e59a9af455a8a045d0914f23123a60bd543d476125658557066e349fd2488f` | `efb29f48e3ab040096e11f0d50a239b46a455c00821ed02730636ae603cdb9a0` (4) |
| `Toy.BoundaryLicensing.traceSub_pos` | none | `27815cab9c1ce7ea0c988f70004306ac3310f55287a5ddd25b560da41a9e4388` | `efb29f48e3ab040096e11f0d50a239b46a455c00821ed02730636ae603cdb9a0` (4) |
| `Toy.BoundaryLicensing.transfer` | propext | `6e09c216959adb5cdcdc2f5d47f798cc06c8c7c971d43bbe1216a7792b56d5d2` | `108bea8aeee5b245b0abfeda10107d1b10ad3f12bd9bebbbe28383d9ec90860b` (27) |
| `Toy.BoundaryLicensing.transferChain` | propext | `574243d5248bf98c19c3e92c472cdb56e2a1c844c48f14ada0a9ce1105d46e46` | `108bea8aeee5b245b0abfeda10107d1b10ad3f12bd9bebbbe28383d9ec90860b` (27) |
| `Toy.BoundaryLicensing.transferChain_eq_iff_forall_realizesChain` | Classical.choice, Quot.sound, propext | `22a727961644455b5211bf7569b3f36034a8d91cc60b3a7917130d7daf5bd94e` | `4a44c123aaff7e65977e722e5a6b76751c4904afc2a0f9e86b8377cddef342ce` (110) |
| `Toy.BoundaryLicensing.transferChain_neg` | propext | `50e835c6d26d121bee9354419d95659b2e08c2deb5bad3c22f91e0976bd5fa0f` | `7dd17f0d09ea2067f860bce3fb12f2af7b9a34af274f3801b60db53f98582e0b` (50) |
| `Toy.BoundaryLicensing.transferChain_pos` | propext | `824f7ba302d647cadd4ce935712ed45c96d798947c4cbc62d7480e7e4960cf60` | `7dd17f0d09ea2067f860bce3fb12f2af7b9a34af274f3801b60db53f98582e0b` (50) |
| `Toy.BoundaryLicensing.transferIff` | propext | `632259ade693a4d82a18b115efdd2d79d54650b3c04b1b54af85b1bb87ec0020` | `108bea8aeee5b245b0abfeda10107d1b10ad3f12bd9bebbbe28383d9ec90860b` (27) |
| `Toy.BoundaryLicensing.transferIff_neg` | propext | `118304414b0c61f49765452c77c21d468919e13866ce2b5218a2689b9a9744fa` | `6fdc70a6b59e97c9b8a4a1cb69c38bb7442c04fa47c57b2fd4db461ac8bc5bc8` (50) |
| `Toy.BoundaryLicensing.transferIff_pos` | propext | `4671160b81f281e355b0903eff74da8e2fab2ce7944de7a1c3581c2418663bfc` | `6fdc70a6b59e97c9b8a4a1cb69c38bb7442c04fa47c57b2fd4db461ac8bc5bc8` (50) |
| `Toy.BoundaryLicensing.transferIff_sound` | Classical.choice, Quot.sound, propext | `5716e026d1653793e8915e6e14d49e75b40a0167edd9860cd9eebca76f90e7e2` | `90bf7f4912b54dba79a0ace237015d4fa0bf29b2829331d2b2b73caf93fac0c0` (110) |
| `Toy.BoundaryLicensing.transferIff_univSafety_existWitness_supported_iff` | propext | `c841086ca1238dcf94f6cd757e4522116a6fc4cb373925602da272696eeb692e` | `6fdc70a6b59e97c9b8a4a1cb69c38bb7442c04fa47c57b2fd4db461ac8bc5bc8` (50) |
| `Toy.BoundaryLicensing.transfer_neg` | propext | `ec8f50f42b940733a172799daec588134d110c8130c7984d2b33cfff0ddf33f9` | `9ce8b9bc6efb313cfa2fcc0cc09481cc35572c3d3db8fceebf19b8b658a8e05d` (49) |
| `Toy.BoundaryLicensing.transfer_pos` | propext | `d182fbccf189c53e90a0e0062accdfce58b30551348bac421e601a6d66015b7e` | `9ce8b9bc6efb313cfa2fcc0cc09481cc35572c3d3db8fceebf19b8b658a8e05d` (49) |
| `Toy.BoundaryLicensing.transfer_sound` | Classical.choice, Quot.sound, propext | `382d356ed74d2c54a650bb74cdef707165a1aebd4b147c15ae2bff6ee058c26a` | `1d9a84587dd184890abf019c9fd2ffc02582fbf589f5e6dda7856d9ae6cb2441` (109) |
| `Toy.BoundaryLicensing.transfer_undetermined_sharp` | Classical.choice, Quot.sound, propext | `fe6bed4b8f7680cc81bc716bc38ef6bfce06457bae6ab0636e00eb1db0782d33` | `5be62d4749a699cf878f2aeb58ed5c1c092e04a63f9bf26346a65ffe37bedac6` (107) |
| `Toy.BoundaryLicensing.twoBranchSys` | none | `8db4a5de751efdce6794428f0a51988aa77254137e300b52155025b94d36895a` | `468842f7a8158d44f738aefedc4eb684eaf2755cb035ce9d7b23c28ff3350302` (4) |
| `Toy.BoundaryLicensing.undeterminedEv_neg` | none | `7103e428b835a54e30fd3db0acc0c0528c026f76e0087569e7f717fa57912f2a` | `bbe82a132b00e1cc6cc735e19755de130eb055753f38a4279370ec1413fe4e25` (4) |
| `Toy.BoundaryLicensing.undeterminedEv_pos` | none | `401daf575e917b5ebfad8db09753482299897bbb84a41f637c5faf6a1a1b2ede` | `bbe82a132b00e1cc6cc735e19755de130eb055753f38a4279370ec1413fe4e25` (4) |
| `Toy.BoundaryLicensing.unwarranted_collapses_both_statuses` | Classical.choice, Quot.sound, propext | `0acab7a4ca36122d65dae193399ab20d40a80541eb3dc490d28eef37837df95e` | `4c1bcca2e81bf35a44bf8495b9a8674dc8c3be886192fb3e9b9cfccac461572c` (113) |
| `Toy.BoundaryLicensing.unwarranted_undetermined_vacuous_agreement` | Classical.choice, Quot.sound, propext | `39cd1a9655d89ccc09b07cc12887ea7699047f4251f347090efe8f5759300443` | `7f92720e9cbc2fdb05643fcbc8496f2efc7861a9cbd3323ba515161aa541dd24` (112) |
| `Toy.BoundaryLicensing.valFalse` | none | `9ad53392114b8e2a426be83604ba316d4152638a76e3a565f51a31f431e22290` | `e12cfa03d248f9e81a536d584141c19a5b506a944f1b670f2c867250e251fd2b` (2) |
| `Toy.BoundaryLicensing.valTrue` | none | `9ad53392114b8e2a426be83604ba316d4152638a76e3a565f51a31f431e22290` | `e12cfa03d248f9e81a536d584141c19a5b506a944f1b670f2c867250e251fd2b` (2) |
| `Toy.BoundaryLicensing.warnAdjudicateGate` | none | `344c4e9ad008b829821b587b88d4d47c7aa132b1df41d21dc43b75dd66878b65` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.BoundaryLicensing.warnAdjudicateGate_neg` | none | `f766e7215d48f8c0204f80227b67e8221410717b7d8ae06d2449f1281e2307c8` | `157a86d2446c8b5f7b1780d02d5d11ff6b02b66a984fa930ee1737bf0ac359f0` (1) |
| `Toy.BoundaryLicensing.warnAdjudicateGate_pos` | none | `4fc2609c1dfe58b997654e8d816afd08f50588ff53e87717b785e02023e88d13` | `157a86d2446c8b5f7b1780d02d5d11ff6b02b66a984fa930ee1737bf0ac359f0` (1) |
| `Toy.BoundaryLicensing.warnAdjudicateGate_zeroLockout_and_sound` | none | `5318243fd1747de9e1536c7b83b01738eb671b0c7f3bd3b7c1cdd1b7f1986710` | `8ab55d5a5c6190ee54075271bd569f79fffc78e75b167f312d9b9587dc2c2710` (4) |
| `Toy.BoundaryLicensing.zeroFalseAccept_neg` | none | `b906e2f3b180aba619a7a140831be570f170c6f82c068b3a90cad4a04b6963e1` | `c8a0daf2cb46a9e5b0e62f5ce59d68095284a0ac1b976524e589976ed5ce3710` (1) |
| `Toy.BoundaryLicensing.zeroFalseAccept_pos` | none | `704a4d34b4256368cb7c9403fa13544745934d4a37dca43ae6a78556e2bd3fdd` | `c8a0daf2cb46a9e5b0e62f5ce59d68095284a0ac1b976524e589976ed5ce3710` (1) |
| `Toy.BoundaryLicensing.zeroLockout_and_zeroFalseAccept_iff_exact` | none | `525b6c445e538d76aae78e3f6950114f7fae77dfdaa9462e9bdcce3455ed2c19` | `048bc5fe2265561b790ad9868e21bddfd68fae634a0bfd23e3e3fdb755157fa8` (3) |
| `Toy.BoundaryLicensing.zeroLockout_neg` | none | `607c73462f402f4cdaea1b751300e748216f23f3fd7a56123b22e04cd562219d` | `f9e48c53119ddd7c73315a5ab682c3ee363735e2c61630641dd5e7c0ee11ceab` (1) |
| `Toy.BoundaryLicensing.zeroLockout_pos` | none | `9afd651b639f265cc6b4eed4cc0445a53f52cb2e37ae12d6f5bca68771e2f17a` | `f9e48c53119ddd7c73315a5ab682c3ee363735e2c61630641dd5e7c0ee11ceab` (1) |

### Primary literature

- M. R. Clarkson, F. B. Schneider, "Hyperproperties", *Journal of Computer Security* 18(6):1157–1210, 2010, doi:10.3233/JCS-2009-0393.
- M. C. Browne, E. M. Clarke, O. Grumberg, "Characterizing Finite Kripke Structures in Propositional Temporal Logic", *Theoretical Computer Science* 59(1–2):115–131, 1988, doi:10.1016/0304-3975(88)90098-9.
- K. S. Namjoshi, "A Simple Characterization of Stuttering Bisimulation", *FSTTCS 1997*, LNCS 1346, pp. 284–296, 1997, doi:10.1007/BFb0058037.
- P. Manolios, *Mechanical Verification of Reactive Systems*, PhD Dissertation, University of Texas at Austin, 2001; and "A Compositional Theory of Refinement for Branching Time", *CHARME 2003*, LNCS 2860, pp. 304–318, 2003, doi:10.1007/978-3-540-39724-3_28.
- S. Merz, "Stuttering Equivalence", *Archive of Formal Proofs*, ISSN 2150-914x, submitted 2012-05-07, https://www.isa-afp.org/entries/Stuttering_Equivalence.html (no Crossref DOI assigned; identified by AFP entry name, ISSN, submission date, and canonical URL).
- R. C. Lyndon, "Properties Preserved under Homomorphism", *Pacific Journal of Mathematics* 9(1):143–154, 1959, doi:10.2140/pjm.1959.9.143.
- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge Tracts in Theoretical Computer Science 53, Cambridge University Press, 2001, §2.1, doi:10.1017/CBO9781107050884.
- J. M. Han, F. van Doorn, "A Formal Proof of the Independence of the Continuum Hypothesis", *CPP 2020*, pp. 353–366, 2020, doi:10.1145/3372885.3373826.
- M. Abadi, L. Lamport, "The Existence of Refinement Mappings", *Theoretical Computer Science* 82(2):253–284, 1991, doi:10.1016/0304-3975(91)90224-P.
- C. Abate, R. Blanco, D. Garg, C. Hrițcu, M. Patrignani, J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", *IEEE CSF 2019*, pp. 256–271, 2019, doi:10.1109/CSF.2019.00025.
- T. Dardinier, P. Müller, "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties", *PACMPL* 8(PLDI):207, 2024, doi:10.1145/3656437 (Isabelle AFP `HyperHoareLogic`, https://www.isa-afp.org/entries/HyperHoareLogic.html).
- J. McLean, "A General Theory of Composition for Trace Sets Closed Under Selective Interleaving Functions", *IEEE Symposium on Research in Security and Privacy*, pp. 79–93, 1994, doi:10.1109/RISP.1994.296590.
- X. Leroy, "A Formally Verified Compiler Back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4.
- A. W. Appel, "Verified Software Toolchain", *ESOP 2011*, LNCS 6602, pp. 1–17, 2011, doi:10.1007/978-3-642-19718-5_1.
- J. H. Saltzer, M. D. Schroeder, "The Protection of Information in Computer Systems", *Proceedings of the IEEE* 63(9):1278–1308, 1975, doi:10.1109/PROC.1975.9939.
- R. Pollack, "How to Believe a Machine-Checked Proof", in *Twenty-Five Years of Constructive Type Theory* (G. Sambin, J. M. Smith, eds.), Oxford University Press, pp. 205–220, 1998, doi:10.1093/oso/9780198501275.003.0013, ISBN 978-0-19-850127-5.
- M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter, "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq", *PACMPL* 4(POPL):8, 2020, doi:10.1145/3371076.
- O. Abrahamsson, M. O. Myreen, R. Kumar, T. Sewell, "Candle: A Verified Implementation of HOL Light", *ITP 2022*, LIPIcs 237, pp. 3:1–3:17, 2022, doi:10.4230/LIPIcs.ITP.2022.3.
- M. Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean", arXiv:2403.14064, 2024, doi:10.48550/arXiv.2403.14064.
- D. Fox, "Free Choice and the Theory of Scalar Implicatures", in *Presupposition and Implicature in Compositional Semantics* (U. Sauerland, P. Stateva, eds.), Palgrave Macmillan, pp. 71–120, 2007, doi:10.1057/9780230210752_4.
- M. L. Geis, A. M. Zwicky, "On Invited Inferences", *Linguistic Inquiry* 2(4):561–566, 1971, https://www.jstor.org/stable/4177664 (no Crossref DOI assigned; identified by journal, volume, issue, page range, year, and stable JSTOR URL).
- E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, "Counterexample-Guided Abstraction Refinement for Symbolic Model Checking", *Journal of the ACM* 50(5):752–794, 2003, doi:10.1145/876638.876643.

### Related reference-corpus packages (cited by slug, zero cross-package build dependencies)

- `sound-checker-laws-anchors-allowlists-and-certificates`
- `finite-test-suites-teaching-sets-and-bounded-state-completeness`
- `refinement-and-hyperproperties-noninterference-and-randomness`
- `simulation-diagrams-and-multi-pass-compiler-correctness`
- `proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`
- `scheduler-adequacy-generated-execution-domains-and-restricted-quantifiers`
- `hypothesis-ledgers-tightness-irredundancy-weakest-premises-and-vacuity`
- `claim-strength-order-quantifier-drift-relativization-and-non-claims`
- `printing-elaboration-round-trips-coercions-and-statement-certificates`
- `implicature-safe-summaries-conditional-perfection-and-exhaustification-of-formal-claims`
- `toy-model-transfer-preservation-of-claim-shapes-under-embeddings-homomorphisms-and-simulations`
- `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`
- `law-dependent-rewrites-after-capture-safe-vs-unsafe-trait-laws-and-relational-semantics`

## Revalidation

Requirements: `elan` (so that `lake` selects the `leanprover/lean4:v4.34.1` toolchain pinned in `lean/lean-toolchain`) and `python3`.

Primary revalidation check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory without modifying the package. It runs `lake build`; scans every `.lean` source file (after stripping comments) to ensure zero `sorry`, `admit`, `native_decide`, or `axiom` declarations; executes an inline Lean `CommandElabM` audit program that runs `Lean.collectAxioms` over every declaration in `Toy` and fails on any axiom outside `{propext, Classical.choice, Quot.sound}`; and recomputes, for every declaration referenced by `results.json` or recorded in `audit/statements.json`, both `statement_sha256` (SHA-256 of `repr` of the kernel `Expr` type) and `closure_sha256` (SHA-256 of the sorted `name : repr(type)` and non-theorem ` := repr(value)` entries across all reachable package constants), verifying exact equality with `audit/statements.json`. It prints `REVALIDATED` and exits with code `0` iff all checks pass.

Manual build and `#print axioms` audit of the twenty-nine primary card theorems (run from the package directory):

```sh
cd lean
lake build
cat > /tmp/boundary_licensing_axioms.lean <<'EOF'
import Toy
#print axioms Toy.BoundaryLicensing.transfer_sound
#print axioms Toy.BoundaryLicensing.sepMatrix_upperTriangular
#print axioms Toy.BoundaryLicensing.sepMatrix_subdiagonal_countermodels
#print axioms Toy.BoundaryLicensing.posShape_columns_pairwise_distinct
#print axioms Toy.BoundaryLicensing.transfer_undetermined_sharp
#print axioms Toy.BoundaryLicensing.transferIff_sound
#print axioms Toy.BoundaryLicensing.transferIff_univSafety_existWitness_supported_iff
#print axioms Toy.BoundaryLicensing.cex_iff_converse_unlicensed
#print axioms Toy.BoundaryLicensing.cospan_subsetClosed_transfer
#print axioms Toy.BoundaryLicensing.transferChain_eq_iff_forall_realizesChain
#print axioms Toy.BoundaryLicensing.licensedTransfer_eq_iff_forall_realizesUnderTCB
#print axioms Toy.BoundaryLicensing.unwarranted_collapses_both_statuses
#print axioms Toy.BoundaryLicensing.allowlistAccepts_iff_onlyDeclaredAxioms
#print axioms Toy.BoundaryLicensing.freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist
#print axioms Toy.BoundaryLicensing.no_finite_denylist_enforces_allowlist
#print axioms Toy.BoundaryLicensing.cert_trust_triple_sound
#print axioms Toy.BoundaryLicensing.exhaustifiedOnly_sound_iff_contradictsEv
#print axioms Toy.BoundaryLicensing.neitherNorDisclaimerSafe_iff
#print axioms Toy.BoundaryLicensing.exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined
#print axioms Toy.BoundaryLicensing.condPerfection_compression_breaks_minimal_safe_blocker
#print axioms Toy.BoundaryLicensing.scalarExh_compression_breaks_blocker_minimality
#print axioms Toy.BoundaryLicensing.no_stateless_implicature_transfer_for_compression
#print axioms Toy.BoundaryLicensing.refutation_not_fullPremiseNonVacuous
#print axioms Toy.BoundaryLicensing.cex_global_ctxNonVacuous_dead_right_branch
#print axioms Toy.BoundaryLicensing.finite_suite_allowlist_barrier
#print axioms Toy.BoundaryLicensing.extensional_law_admits_lookupWrapper
#print axioms Toy.BoundaryLicensing.zeroLockout_and_zeroFalseAccept_iff_exact
#print axioms Toy.BoundaryLicensing.blockingGate_locks_out_strict_proxy
#print axioms Toy.BoundaryLicensing.warnAdjudicateGate_zeroLockout_and_sound
EOF
lake env lean /tmp/boundary_licensing_axioms.lean
```

Expected outcome: `lake build` exits `0` with zero warnings, and every `#print axioms` line reports either `'...' does not depend on any axioms` or a subset of `{propext, Classical.choice, Quot.sound}`. Any change to the type or definition body of a package declaration reachable from a recorded theorem alters its `statement_sha256` or `closure_sha256` and is flagged immediately by `python3 support/revalidate.py .`.
