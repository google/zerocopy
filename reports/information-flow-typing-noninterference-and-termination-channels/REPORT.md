# Information-flow typing, noninterference, and termination channels (Lean 4, toy model)

## Summary

This package is a Lean 4 mechanization (core library only, no Mathlib) of syntax-directed program-counter (`pc`-label) information-flow security typing, termination-insensitive noninterference (`TINI`), termination-sensitive noninterference (`TSNI`), four formalized ablations of the control-dependence (`pc`) and `while`-termination restrictions within this rule family, the deterministic decomposition `TSNI ↔ TINI ∧ CoTerminates`, and complete-observation hyperproperty classifications (`IsTwoSafety`, `SubsetClosed`, `tiniHyperprop`, `tsniHyperprop`, `tsniOutHyperprop`). All 13 results (51 distinct card-hashed declarations: 17 main result theorems and 34 additional tightness counterexamples, non-vacuity witnesses, and positive controls; plus 22 unhashed scope witnesses listed in `scope_witnesses_lean`) are kernel-checked; their axiom footprints are at most `propext`, `Classical.choice`, and `Quot.sound` and are recorded per theorem under Evidence.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

- **Result 1 (`cmd-typed-implies-tini`).** Under the syntax-directed program-counter (`pc`-label) security type system `CmdTyped Γ pc c` (explicit-flow assignment bound `exprLevel Γ e ≤ Γ x` and `pc` tracking `pc ≤ Γ x` raised by guard levels at both `if` and `while`), any well-typed command satisfies termination-insensitive noninterference (`TINI Γ c`): whenever two `low`-equivalent initial stores both terminate, their final stores are `low`-equivalent.
- **Result 2 (`no-pc-typed-implicit-flow-counterexample`).** For any labeling `Γ` and variables `l, h` with `Γ l = low` and `Γ h = high`, omitting `pc` tracking everywhere (`NoPcTyped Γ`) accepts `if h then l := 1 else l := 0`, which violates `TINI Γ`.
- **Result 3 (`cmd-typed-termination-channel-counterexample`).** For any labeling `Γ`, program counter `pc`, and variable `h` with `Γ h = high`, `CmdTyped Γ pc` accepts `while h do skip`, which terminates from `zeroStore` and diverges from `Store.update zeroStore h 1`, refuting `TSNI Γ`.
- **Result 4 (`cmd-typed-implies-tini-hyperprop`).** As a definitional corollary of Result 1 via `tini_iff_tiniHyperprop`, whenever `CmdTyped Γ pc c` holds, the terminating I/O behavior `ioBehavior c` satisfies the 2-safety hyperproperty `tiniHyperprop Γ`.
- **Result 5 (`two-safety-implies-subset-closed`).** Every pairwise-determined hyperproperty over complete observations (`IsTwoSafety H`, equivalent to the non-empty bad-pair condition `CSTwoSafety H`) is subset-closed (`SubsetClosed H`).
- **Result 6 (`tini-hyperprop-is-two-safety`).** Unconditionally for every labeling `Γ : Var → Level`, `tiniHyperprop Γ` satisfies `IsTwoSafety` and therefore `SubsetClosed`.
- **Result 7 (`tsni-hyperprop-not-subset-closed`).** Whenever `Γ` contains at least one `high` variable (`Γ h = high`), termination-sensitive noninterference over terminating-pair I/O trace sets (`tsniHyperprop Γ`, encoding divergence by absence of a pair) is neither `SubsetClosed` nor `IsTwoSafety`.
- **Result 8 (`ts-typed-implies-tsni`).** Under `TsTyped Γ pc c`—which strengthens `CmdTyped` with base explicit/implicit-flow bounds plus both `exprLevel Γ e = low` and `pc = low` at every `while` loop—every well-typed command satisfies termination-sensitive noninterference (`TSNI Γ c`).
- **Result 9 (`low-guard-while-typed-termination-channel-counterexample`).** For any `Γ`, `pc`, and `h` with `Γ h = high`, enforcing `exprLevel Γ e = low` on `while` guards without also requiring `pc = low` at `while` (`LowGuardWhileTyped Γ pc`) still accepts `if h then (while 1 do skip) else skip`, violating `TSNI Γ`.
- **Result 10 (`tsni-iff-tini-and-coterminates`).** In this deterministic big-step semantics (for every `Var`, `[DecidableEq Var]`, `Γ`, and `c`), `TSNI Γ c` is equivalent to `TINI Γ c ∧ CoTerminates Γ c`.
- **Result 11 (`pc-low-while-typed-termination-channel-counterexample`).** For any `Γ` and `h` with `Γ h = high`, enforcing `pc = low` at `while` without also requiring `exprLevel Γ e = low` (`PcLowWhileTyped Γ .low`) still accepts `while h do skip`, violating `TSNI Γ`.
- **Result 12 (`while-no-pc-typed-implicit-flow-counterexample`).** For any `Γ` and variables `l, h` with `Γ l = low` and `Γ h = high`, raising `pc` at `if` while omitting `pc` raising at `while` (`WhileNoPcTyped Γ .low`) still accepts `while h do (l := 1; h := 0)`, violating `TINI Γ`.
- **Result 13 (`tsni-out-hyperprop-is-two-safety`).** Unconditionally (using determinism of `Eval` and classical case analysis on `Terminates`), when divergence is encoded explicitly as `none : Option (Store Var)` (`OutTrace Var`, `outcomeBehavior c`), `TSNI Γ c` is equivalent to `tsniOutHyperprop Γ (outcomeBehavior c)`, and `tsniOutHyperprop Γ` satisfies `IsTwoSafety` and `SubsetClosed`.

Every result carries non-claims ruling out tempting stronger readings; they are listed first under **Boundaries**, per result. Each result's hypothesis ledger under **Findings** records which hypotheses are tight (each with a proved Lean counterexample) or absent. Everything proved here applies strictly to a toy deterministic imperative model (`Toy.IFC`); claims connecting these definitions to real languages or tools are separate `derived (modeling bridge)` statements under **Findings**, and model gaps are detailed under **Applicability**. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real imperative languages or the information-flow type checkers, static analyzers and compiler passes that enforce noninterference for them (the modeling-bridge statements under **Findings** argue the connection separately).

Design question informed: *what confidentiality guarantee does syntax-directed `pc`-label security typing establish, which covert channels remain open, which syntactic checks are individually necessary within this rule family, and how do TINI and TSNI sit in the complete-observation hyperproperty hierarchy?* Answer within this model: `CmdTyped` enforces batch-job `TINI` (Result 1), while leaving the termination covert channel open (Result 3) and permitting total secret recovery across repeated runs with chosen low inputs (`probeProg`); closing the termination channel in deterministic semantics means enforcing `CoTerminates` alongside `TINI` (Result 10), which `TsTyped` achieves by requiring both `pc = low` and `exprLevel Γ e = low` at every `while` loop (Result 8), though `TsTyped` is sufficient rather than necessary (`whileHZero`). Each of the four formalized ablations fails: dropping `pc` everywhere (Result 2), dropping `pc` at `while` alone (Result 12), checking `exprLevel Γ e = low` at `while` without `pc = low` (Result 9), and checking `pc = low` at `while` without `exprLevel Γ e = low` (Result 11) all admit leaks—yet `NoHighGuardTyped` shows a `pc` label is not the sole sound control-dependence discipline. Not every rule component has its own relaxed system: no system here drops `pc` raising at `if` alone (that case is covered only through `NoPcTyped`, which drops all `pc` tracking, and its loop-free witness `if h then l := 1 else l := 0`), and none drops only the explicit-flow bound (that case is covered only by the program `l := h`, which the full systems reject; see the Result 1 and Result 8 ledgers). Over complete observations, `tiniHyperprop` is `IsTwoSafety` and `SubsetClosed` (Results 4–6), whereas encoding divergence by omission of a pair (`tsniHyperprop`) breaks both `SubsetClosed` and `IsTwoSafety` whenever any secret exists (Result 7); switching to explicit-outcome traces (`OutTrace`, `tsniOutHyperprop`) restores both `IsTwoSafety` and `SubsetClosed` (Result 13). Timing channels are unmodeled (documented under **Boundaries**).

## Applicability

### Model fidelity

This is a **toy model**, not a formalization of a production compiler IR, language runtime, or industrial static analyzer. It models a minimal deterministic sequential imperative language (`Expr`, `Cmd`, inductive big-step semantics `Eval`) over a two-point confidentiality lattice `{low, high}` (`Level`) with static, flow-insensitive variable labelings `Γ : Var → Level`. Known modeling gaps relative to real systems include:

- **Batch-job final stores only:** `Eval c σ σ'` models terminating input–output pairs `(σ, σ')`. Interactive/intermediate public outputs (progress-sensitive noninterference, Askarov et al. 2008) are excluded. Moreover, the informal "at most one bit" intuition for the termination channel applies at most per run, for a fixed low input. This is derived, not kernel-checked, and no theorem in this package states an information bound: for a fixed low input, `TINI` and determinism of `Eval` leave a low observer only two possible outcomes of a run (divergence, or termination with the single low final state shared by all terminating low-equivalent runs). An attacker who can rerun a `CmdTyped`-well-typed program with chosen low inputs can recover a secret completely through termination (kernel-checked: `Toy.IFC.probeProg_cmdTyped`, `Toy.IFC.probeProg_termination_profile_determines_secret`).
- **Timing and step counts (not formalized):** `Eval` records neither execution steps nor wall-clock time, so neither `TINI` nor `TSNI` rules out timing side channels. Even under `TsTyped`, `if h then (h := h + 1; h := h + 1) else skip` is accepted at `pc = low` (`Toy.IFC.timingExample_tsTyped`), while its branches execute different numbers of steps depending on `h` (informal observation; step counts are not modeled in `Eval`).
- **Total expressions:** `eval` covers integer literals, variables, `+`, `-`, `=`, `<`, and `not` (`= 0`), with no partial operations (division by zero, out-of-bounds indexing, or exceptions).
- **Deterministic and single-threaded:** `Eval` is deterministic (`Toy.IFC.eval_deterministic`) and sequential; concurrency, scheduling leaks, and possibilistic or probabilistic nondeterminism are excluded (`Toy.IFC.nondet_existential_tsni_not_tini`).
- **Two-point `pc`-label rules vs. richer type systems:** `CmdTyped` is Nipkow & Klein's syntax-directed `pc`-label `sec_type` system (§9.2.2) specialized to `{low, high}`. Equivalence with Volpano, Irvine & Smith's (1996) declarative phrase-type (`τ var` / `τ cmd`) and contravariant subtyping formulation over an arbitrary lattice is not formalized, nor are flow-sensitive variable labels (Hunt & Sands 2006), pointers/aliasing, procedures, or declassification.
- **Complete-observation hyperproperties vs. infinite-trace topology:** `IsTwoSafety` is a package-specific pairwise-determinedness predicate over complete observations (`IOTrace Var` or `OutTrace Var`), proved equivalent to the non-empty bad-pair condition `CSTwoSafety` (`Toy.IFC.isTwoSafety_iff_csTwoSafety`) and forcing `H ∅` (`Toy.IFC.isTwoSafety_holds_empty`); consequently the empty hyperproperty `fun _ => False`, which holds of no trace set, fails it (`Toy.IFC.false_hyperprop_not_isTwoSafety`). Despite the theorem's name, that empty hyperproperty is not Clarkson & Schneider's (2010) hyperproperty `false`, which they define as `{∅}`. Clarkson & Schneider's prefix-based infinite-trace topology (which they show equivalent to the lower Vietoris construction applied to the Plotkin topology; under it, relational `TSRNI` with explicit `s^ω` divergence is neither hypersafety nor hyperliveness for `Rel`, §7.2.1) is not formalized; remarks linking the complete-observation results to infinite-trace topology are unformalized modeling-bridge remarks.

Any claim connecting these theorems to real systems or external frameworks is a separate `derived (modeling bridge)` claim under **Findings** and is not established by the Lean kernel check.

### Toolchain and project

- **Toolchain:** `leanprover/lean4:v4.34.1` (GitHub tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean library only: no Mathlib, no external package `[[require]]` dependencies.
- **Lake project:** `lean/` (`lakefile.toml`, package `information-flow-typing-noninterference-and-termination-channels`, one `[[lean_lib]]` `Toy`), namespace `Toy.IFC`, divided into five modules under `lean/Toy/IFC/`:
  - `Core.lean`: security lattice `Level`, stores and `LowEq`, total expressions `Expr`/`eval`/`exprLevel`, commands `Cmd`, deterministic big-step semantics `Eval`, `Terminates`, `TINI`, `CoTerminates`, `TSNI`, `TwoVar` test harness, and definition examples.
  - `Typing.lean`: `CmdTyped`, `TsTyped`, ablations (`NoPcTyped`, `WhileNoPcTyped`, `LowGuardWhileTyped`, `PcLowWhileTyped`), alternative `NoHighGuardTyped`, anti-monotonicity, inclusion lemmas, and positive/negative typing examples.
  - `Hyperproperties.lean`: `IOTrace`, `OutTrace`, `ioBehavior`, `outcomeBehavior`, `SubsetClosed`, `IsOneSafety`, `IsTwoSafety`, `CSTwoSafety`, `tiniHyperprop`, `tsniHyperprop`, `tsniOutHyperprop`, and hyperproperty results (Results 5, 6, 7, 13) plus adequacy lemmas.
  - `Results.lean`: confinement (`cmdTyped_high_preserves_lowEq`), totality (`tsTyped_high_total`), and Results 1–4 and 8–12 (`cmdTyped_implies_tini`, `tsTyped_implies_tsni`, `tsni_iff_tini_and_coterminates`, and the typing-rule ablation counterexamples).
  - `Witnesses.lean`: `ThreeVar` / `allLowEnv` environments, canonical tightness counterexamples, positive controls, non-vacuity witnesses, and kernel-checked scope lemmas cited in non-claims.
- **Revalidation script:** `support/revalidate.py` (Python 3 standard library only; see Revalidation).

### Subjects and their relationship

`REPORT.json` lists the Lean 4 toolchain release (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`) that kernel-checked every declaration, together with 17 primary literature and external mechanization sources (12 peer-reviewed papers/books identified by DOI, 3 Archive of Formal Proofs entries linked to `isabelle-prover/mirror-afp-devel` at commit `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`, the Isabelle/HOL HOL-IMP distribution theories `Sec_Typing.thy` / `Sec_TypingT.thy` pinned to `isabelle-prover/mirror-isabelle` commit `d2ede99d0077d2777ed2b83d084d3aadf93826b5` (path `src/HOL/IMP`), and *Security Foundations* Vol. 7 `StaticIFC` at Version 1.2, 2026-08-24). The Lean project is completely self-contained and does not import any external development; the external sources document provenance and prior art. The HOL-IMP theories were read on the Isabelle library web pages (`https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_Typing.html` / `Sec_TypingT.html`). The pinned mirror commit `d2ede99d0077d2777ed2b83d084d3aadf93826b5` (2024-09-20) is, according to the GitHub API on 2026-11-20, the most recent commit on the mirror's `master` branch that modifies either file, and at that commit both files have exactly the same token sequence as the observed web text. For *Security Foundations* (`https://softwarefoundations.cis.upenn.edu/secf-current/`) no immutable identity was found: the live text was observed directly (it reports Version 1.2, `2026-08-24`), and that moving URL together with the version is recorded as the strongest available coordinate.

## Findings

### Setting and definitions

Basis: execution (Lean kernel check) for every named positive and negative example and proved helper lemma below; the "Meant to capture" column states the intended modeling reading, not a formal claim about real systems.

All core definitions live in `Toy/IFC/Core.lean`, `Toy/IFC/Typing.lean`, and `Toy/IFC/Hyperproperties.lean`.

#### Language, semantics, and noninterference predicates (`Core.lean`)

| Definition | Lean summary | Meant to capture | Positive example(s) (proved) | Negative example(s) (proved) |
|---|---|---|---|---|
| `Level`, `Level.le`, `Level.join` | Two constructors `low`, `high`; `low ≤ _`, `high ≤ high`, `¬ (high ≤ low)`; `⊔` join | Two-point confidentiality lattice `low ≤ high` | `level_le_pos_low_high` | `level_le_neg_high_low` |
| `Store`, `Store.update`, `zeroStore` | `Var → Int`; functional point update; `fun _ => 0` | Imperative variable state | — | — |
| `LowEq Γ σ₁ σ₂` | `∀ x, Γ x = .low → σ₁ x = σ₂ x` | Attacker indistinguishability of stores on public variables | `lowEq_pos_high_diff` | `lowEq_neg_low_diff` |
| `Expr`, `eval`, `exprLevel` | Literals, variables, `+`, `-`, `=`, `<`, `not`; total `eval`; join of variable levels `exprLevel` | Total integer expressions and static upper bound on read secrets | `exprLevel_low_agrees` (semantic bridge) | — |
| `Cmd`, `Eval`, `Terminates` | `skip`, `assign`, `seq`, `ite`, `whileLoop`; inductive big-step `Eval c σ σ'`; `∃ σ', Eval c σ σ'` | Deterministic big-step imperative execution (`eval_deterministic`) | `eval_pos_while_decrement`, `terminates_pos_assign` | `eval_neg_wrong_final`, `terminates_neg_while_one` |
| `TINI Γ c` | `∀ σ₁ σ₂ σ₁' σ₂', LowEq Γ σ₁ σ₂ → Eval c σ₁ σ₁' → Eval c σ₂ σ₂' → LowEq Γ σ₁' σ₂'` | Batch-job termination-insensitive noninterference | `tini_pos_high_branch_high_write` | `tini_neg_explicit_flow` |
| `CoTerminates Γ c` | `∀ σ₁ σ₂, LowEq Γ σ₁ σ₂ → (Terminates c σ₁ ↔ Terminates c σ₂)` | Absence of termination differences across low-equivalent inputs | `coTerminates_pos_skip`, `coTerminates_pos_while_l` | `coTerminates_neg_while_h` |
| `TSNI Γ c` | `∀ σ₁ σ₂ σ₁', LowEq Γ σ₁ σ₂ → Eval c σ₁ σ₁' → ∃ σ₂', Eval c σ₂ σ₂' ∧ LowEq Γ σ₁' σ₂'` | Batch-job termination-sensitive noninterference | `tsni_pos_low_inc` | `tsni_neg_while_h` |

#### Security type systems (`Typing.lean`)

| Definition | Rule structure | Meant to capture | Positive example(s) (proved) | Negative example(s) (proved) |
|---|---|---|---|---|
| `CmdTyped Γ pc c` | `exprLevel Γ e ≤ Γ x` and `pc ≤ Γ x` on `assign`; raises `pc := pc ⊔ exprLevel Γ e` at `ite` and `whileLoop` | Nipkow & Klein `sec_type` (§9.2.2) specialized to `{low, high}` | `cmdTyped_pos_sampleTypedProg`, `cmdTyped_pos_while_h`, `whileHZero_cmdTyped_high` | `cmdTyped_neg_explicit_flow`, `cmdTyped_neg_implicit_flow` |
| `NoPcTyped Γ c` | Checks `exprLevel Γ e ≤ Γ x` on `assign`; omits `pc` everywhere | Explicit-flow-only static taint check (ablation) | `noPcTyped_pos_implicit_flow` | `noPcTyped_neg_explicit_flow` |
| `WhileNoPcTyped Γ pc c` | Raises `pc` at `ite`, leaves `pc` unchanged at `whileLoop` | Partial `pc`-tracking ablation omitting `while` guard in `pc` | `whileNoPcTyped_pos_whileLeakProg` | `whileNoPcTyped_neg_implicit_flow` |
| `NoHighGuardTyped Γ c` | Checks `exprLevel Γ e ≤ Γ x` on `assign` and `exprLevel Γ e = .low` at `ite` and `whileLoop` | Alternative `pc`-free sound discipline (embeds into `CmdTyped Γ .low` via `noHighGuardTyped_implies_cmdTyped_low`) | `noHighGuardTyped_pos_low_ite` | `noHighGuardTyped_neg_implicit_flow` |
| `LowGuardWhileTyped Γ pc c` | `CmdTyped` plus `exprLevel Γ e = .low` on `whileLoop`, omitting `pc = .low` on `whileLoop` | Ablation checking literal "low loop guard" rule | `lowGuardWhileTyped_pos_high_if_low_while` | `lowGuardWhileTyped_neg_while_h` |
| `PcLowWhileTyped Γ pc c` | `CmdTyped` plus `pc = .low` on `whileLoop`, omitting `exprLevel Γ e = .low` on `whileLoop` | Symmetric ablation checking `pc = low` at loops without low guards | `pcLowWhileTyped_pos_while_h` | `pcLowWhileTyped_neg_high_if_low_while` |
| `TsTyped Γ pc c` | `CmdTyped` plus both `pc = .low` and `exprLevel Γ e = .low` (body at `.low`) on `whileLoop` | Termination-sensitive typing (VS97 `(WHILE)`, N&K Fig. 9.10, SF `ts_well_typed`) | `tsTyped_pos_sampleTsProg` | `tsTyped_neg_while_h`, `tsTyped_neg_high_if_low_while` |

Proved inclusions and anti-monotonicity: `TsTyped.antitone`, `CmdTyped.antitone`, `WhileNoPcTyped.antitone`, `tsTyped_implies_lowGuardWhileTyped`, `tsTyped_implies_pcLowWhileTyped`, `lowGuardWhileTyped_implies_cmdTyped`, `pcLowWhileTyped_implies_cmdTyped`, `tsTyped_implies_cmdTyped`, `noHighGuardTyped_implies_cmdTyped_low`, `cmdTyped_implies_whileNoPcTyped`, `whileNoPcTyped_implies_noPcTyped`, and `cmdTyped_implies_noPcTyped`.

#### Hyperproperties and observation encodings (`Hyperproperties.lean`)

| Definition | Lean summary | Meant to capture | Positive example(s) (proved) | Negative example(s) (proved) |
|---|---|---|---|---|
| `IOTrace Var`, `ioBehavior c` | `Store Var × Store Var`; `fun p => Eval c p.1 p.2` | Terminating-pairs behavior (divergence = missing pair) | `ioBehavior_pos_assign` | `ioBehavior_neg_wrong_final` |
| `OutTrace Var`, `outcomeBehavior c` | `Store Var × Option (Store Var)`; `some σ'` for `Eval`, `none` for `¬ Terminates` | Explicit-outcome behavior (Sabelfeld & Myers §IV-C `⊥`) | `outcomeBehavior_pos_assign`, `outcomeBehavior_pos_while_one` | `outcomeBehavior_neg_assign_none`, `outcomeBehavior_neg_wrong_final` |
| `SubsetClosed H` | `∀ S₁ S₂, (∀ t, S₁ t → S₂ t) → H S₂ → H S₁` | Downward closure under trace-set refinement | `subsetClosed_pos_tiniHyperprop` | `subsetClosed_neg_nonEmpty`, `subsetClosed_neg_tsniHyperprop` |
| `IsOneSafety H` | `∀ S, H S ↔ ∀ t, S t → H (fun u => u = t)` | Single-trace (ordinary safety) property | `isOneSafety_pos_lowOutputZero` | `tiniHyperprop_not_oneSafety` |
| `IsTwoSafety H` | `∀ S, H S ↔ ∀ t₁ t₂, S t₁ → S t₂ → H (fun t => t = t₁ ∨ t = t₂)` | Package-specific pairwise-determinedness over complete observations | `isTwoSafety_pos_tiniHyperprop` | `atMostTwoTraces_subsetClosed_not_twoSafety`, `false_hyperprop_not_isTwoSafety` (the empty hyperproperty `fun _ => False`; not Clarkson & Schneider's `false = {∅}`, which satisfies `IsTwoSafety`) |
| `CSTwoSafety H` | `∀ S, ¬ H S → ∃ t₁ t₂, S t₁ ∧ S t₂ ∧ ∀ S', S' t₁ → S' t₂ → ¬ H S'` | Non-empty bad-pair characterization (`isTwoSafety_iff_csTwoSafety`) | `csTwoSafety_pos_tiniHyperprop` | `csTwoSafety_neg_atMostTwoTraces` |
| `nonEmptyTraceSet` | `fun S => ∃ t, S t` | Auxiliary witness: non-emptiness, which is not subset-closed (`subsetClosed_neg_nonEmpty`, `nonEmptyTraceSet_not_subsetClosed`, both at `α := Unit`) | — | — |
| `atMostTwoTraces` | `fun S => ∀ t₁ t₂ t₃, S t₁ → S t₂ → S t₃ → t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃` | Auxiliary witness: a 3-safety cardinality bound, subset-closed but not `IsTwoSafety` (`atMostTwoTraces_subsetClosed_not_twoSafety`, `csTwoSafety_neg_atMostTwoTraces`, both at `α := Fin 3`) | — | — |
| `tiniHyperprop Γ` | `fun S => ∀ t₁ t₂, S t₁ → S t₂ → tiniRel Γ t₁ t₂` | Batch-job TINI as a hyperproperty (`tini_iff_tiniHyperprop`) | `tiniHyperprop_pos_skip` | `tiniHyperprop_neg_explicit_flow` |
| `tsniHyperprop Γ` | `fun S => ∀ σ₁ σ₂ σ₁', LowEq Γ σ₁ σ₂ → S (σ₁, σ₁') → ∃ σ₂', S (σ₂, σ₂') ∧ LowEq Γ σ₁' σ₂'` | TSNI over terminating-pair sets (`tsni_iff_tsniHyperprop`) | `tsniHyperprop_pos_skip` | `tsniHyperprop_neg_while_h` |
| `tsniOutHyperprop Γ` | `fun S => ∀ t₁ t₂, S t₁ → S t₂ → tsniOutRel Γ t₁ t₂` | TSNI over explicit-outcome trace sets (`tsni_iff_tsniOutHyperprop`) | `tsniOutHyperprop_pos_skip` | `tsniOutHyperprop_neg_while_h` |

#### Test environments and witness programs (`Core.lean`, `Typing.lean`, `Witnesses.lean`)

```lean
inductive TwoVar where | l | h
def twoVarEnv : TwoVar → Level | .l => .low | .h => .high
def storeZero : Store TwoVar := zeroStore
def storeHighOne : Store TwoVar := Store.update storeZero .h 1
def storeLowOne : Store TwoVar := Store.update storeZero .l 1
inductive ThreeVar where | l | m | h
def mixedHighEnv : ThreeVar → Level | .l => .low | .m => .high | .h => .high
def mixedLowEnv : ThreeVar → Level | .l => .low | .m => .low | .h => .high
def allLowEnv : TwoVar → Level := fun _ => .low

def explicitFlowProg l h    := .assign l (.var h)
def implicitFlowProg l h    := .ite (.var h) (.assign l (.lit 1)) (.assign l (.lit 0))
def termChannelProg h       := .whileLoop (.var h) .skip
def highIfLowWhileProg h    := .ite (.var h) (.whileLoop (.lit 1) .skip) .skip
def whileLeakProg l h       := .whileLoop (.var h) (.seq (.assign l (.lit 1)) (.assign h (.lit 0)))
def probeProg l h           := .whileLoop (.lt (.var l) (.var h)) .skip
def whileHZero : Cmd TwoVar := .whileLoop (.var .h) (.assign .h (.lit 0))
def sampleTypedProg         := .seq (.ite (.var .h) (.assign .h (.add (.var .h) (.lit 1))) (.assign .h (.lit 0))) (.assign .l (.add (.var .l) (.lit 1)))
def sampleTsProg            := .whileLoop (.var .l) (.seq (.ite (.var .h) (.assign .h (.sub (.var .h) (.lit 1))) (.assign .h (.lit 0))) (.assign .l (.sub (.var .l) (.lit 1))))
```

Depth labels: *definitional* = unfolding definitions plus at most quantifier permutation/instantiation; *shallow* = short direct proof or explicit finite counterexample construction; *substantive* = structural induction over executions/typing with auxiliary confinement or totality lemmas.

### Result cards

#### Result 1 — `cmd-typed-implies-tini`

- **Lean:** `Toy.IFC.cmdTyped_implies_tini` (namespace `Toy.IFC`).
- **Kind:** theorem. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@cmdTyped_implies_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → TINI Γ c
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c →
  ∀ (σ₁ σ₂ σ₁' σ₂' : Var → Int),
    (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
    Eval c σ₁ σ₁' →
    Eval c σ₂ σ₂' →
    (∀ x, Γ x = .low → σ₁' x = σ₂' x)
```

**Plain claim.** Under the syntax-directed program-counter (`pc`-label) security type system (`CmdTyped Γ pc c`, matching Nipkow & Klein's `sec_type` specialized to `{low, high}`), any well-typed command satisfies termination-insensitive noninterference (`TINI Γ c`): whenever two `low`-equivalent initial stores both lead to terminating big-step executions, their final stores are `low`-equivalent.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hTyped (explicit-flow assignment bound) | Certifies that every direct assignment obeys `exprLevel Γ e ≤ Γ x`, blocking explicit flows from `high` expressions to `low` variables. | tight | `untyped_explicit_flow_violates_tini`. Kernel-checked: `l := h` (`explicitFlowProg .l .h`) is rejected by `CmdTyped` at every `pc` and violates `TINI`. Not kernel-checked: that this program satisfies the remaining (`pc`-tracking) component; this holds by inspection, since at `pc = low` the side condition `pc ≤ Γ l` holds and the program contains no `if` or `while`. |
| hTyped (program-counter tracking at if and while) | Certifies that `pc` is raised by guard security levels at both `if` and `while` and enforced via `pc ≤ Γ x` on assignments, blocking control-flow implicit flows. | tight | `noPcTyped_violates_tini_witness`, `whileNoPcTyped_violates_tini_witness` |

**Depth.** substantive.

**Non-vacuity witness.** Two concrete witnesses under `twoVarEnv` (`l ↦ low`, `h ↦ high`) and `pc = low`: (1) `sampleTypedProg` (`if h then h := h + 1 else h := 0; l := l + 1`), where `storeZero` and `storeHighOne` terminate in distinct final stores with `l = 1`; and (2) `whileHZero` (`while h do h := 0`), a high-guarded loop accepted by `CmdTyped` (and rejected by `TsTyped`) that terminates from both `storeZero` (0 iterations) and `storeHighOne` (1 iteration). (`cmdTyped_implies_tini_nonvacuous`, `cmdTyped_implies_tini_nonvacuous_highLoop`)

**Prior art.**

- Dorothy E. Denning and Peter J. Denning, "Certification of programs for secure information flow", Communications of the ACM 20(7):504–513, July 1977, DOI 10.1145/359636.359712 (origin of the static certification approach; does not contain a noninterference soundness proof).
- Dennis Volpano, Cynthia Irvine, and Geoffrey Smith, "A sound type system for secure flow analysis", Journal of Computer Security 4(2–3):167–187, 1996, DOI 10.3233/JCS-1996-42-304 (Theorem 6.8, Type Soundness, in phrase-type/subsumption form).
- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121.
- Gregor Snelting and Daniel Wasserrab, "A Correctness Proof for the Volpano/Smith Security Typing System", Archive of Formal Proofs, September 2008, https://isa-afp.org/entries/VolpanoSmith.html.
- Lennart Beringer and Martin Hofmann, "Secure information flow and program logics", Archive of Formal Proofs, November 2008, https://isa-afp.org/entries/SIFPL.html.
- Tobias Nipkow and Gerwin Klein, Concrete Semantics: With Isabelle/HOL, Springer, 2014, Chapter 9 ("Types", §9.2.2, Theorem 9.14), pp. 115–142, DOI 10.1007/978-3-319-10542-0_9; mechanized in Isabelle/HOL HOL-IMP `Sec_Typing.thy` (`sec_type`, `anti_mono`, `confinement`, `noninterference` for `0 ⊢ c`), https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_Typing.html (this package's arbitrary-`pc` statement generalizes `0 ⊢ c` trivially via `CmdTyped.antitone`).
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`ni_well_typed`, `ni_well_typed_noninterferent`), https://softwarefoundations.cis.upenn.edu/secf-current/.

**Design question informed.** Establishes the baseline confidentiality guarantee of the syntax-directed `pc`-label security type system (`TINI`): only terminating runs' final public states are protected, while termination channels remain open (see Result 3, `cmd-typed-termination-channel-counterexample`) and typing is sufficient rather than necessary for `TINI`.

**Non-claims:** see Boundaries, Result 1.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `cmdTyped_allows_termination_channel`, `probeProg_cmdTyped`, `probeProg_termination_profile_determines_secret`, `subSelf_tini_not_cmdTyped`, `constBranch_tini_not_cmdTyped`.

Basis: execution (Lean kernel check) — `cmdTyped_implies_tini` (axioms: `propext`).

#### Result 2 — `no-pc-typed-implicit-flow-counterexample`

- **Lean:** `Toy.IFC.noPcTyped_accepts_implicit_flow_violating_tini` (namespace `Toy.IFC`).
- **Kind:** counterexample. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@noPcTyped_accepts_implicit_flow_violating_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → NoPcTyped Γ (implicitFlowProg l h) ∧ ¬TINI Γ (implicitFlowProg l h)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = .low → Γ h = .high →
  NoPcTyped Γ (.ite (.var h) (.assign l (.lit 1)) (.assign l (.lit 0))) ∧
  ¬ (∀ σ₁ σ₂ σ₁' σ₂',
       (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
       Eval (.ite (.var h) (.assign l (.lit 1)) (.assign l (.lit 0))) σ₁ σ₁' →
       Eval (.ite (.var h) (.assign l (.lit 1)) (.assign l (.lit 0))) σ₂ σ₂' →
       (∀ x, Γ x = .low → σ₁' x = σ₂' x))
```

**Plain claim.** For any security labeling `Γ` with `Γ l = low` and `Γ h = high`, the explicit-flow-only typing system `NoPcTyped` (which omits program-counter tracking) accepts `if h then l := 1 else l := 0` (`implicitFlowProg l h`), which violates termination-insensitive noninterference (`¬ TINI Γ (implicitFlowProg l h)`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hLow | Ensures the assigned variable `l` is observable to the `low` attacker so differing constant assignments break `LowEq`. | tight | `implicitFlowProg_target_high_satisfies_tini` |
| hHigh | Ensures the branch guard `h` is secret so two `low`-equivalent initial stores can take opposite branches. | tight | `implicitFlowProg_guard_low_satisfies_tini` |

**Depth.** shallow.

**Non-vacuity witness.** `twoVarEnv` assigns `l ↦ low` and `h ↦ high`. (`noPcTyped_implicit_flow_nonvacuous`)

**Positive control.** `Toy.IFC.implicitFlowProg_rejected_by_cmdTyped`, `Toy.IFC.noHighGuardTyped_neg_implicit_flow`, `Toy.IFC.noHighGuardTyped_implies_cmdTyped_low`.

**Prior art.**

- Dorothy E. Denning and Peter J. Denning, "Certification of programs for secure information flow", Communications of the ACM 20(7):504–513, July 1977, DOI 10.1145/359636.359712 (origin of the static certification approach).
- Dennis Volpano, Cynthia Irvine, and Geoffrey Smith, "A sound type system for secure flow analysis", Journal of Computer Security 4(2–3):167–187, 1996, DOI 10.3233/JCS-1996-42-304.
- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121.
- Sebastian Hunt and David Sands, "On flow-sensitive security types", Proceedings of the 33rd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '06), pp. 79–90, January 2006, DOI 10.1145/1111037.1111045.
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`cf_well_typed`), https://softwarefoundations.cis.upenn.edu/secf-current/.

**Design question informed.** Shows that some control-dependence restriction is essential for blocking control-flow implicit flows: omitting control-dependence tracking entirely (`NoPcTyped`) in favor of explicit expression checks alone is unsound.

**Non-claims:** see Boundaries, Result 2.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `noHighGuardTyped_implies_cmdTyped_low`, `noHighGuardTyped_neg_implicit_flow`, `constBranch_tini_not_cmdTyped`, `noPcTyped_neg_explicit_flow`, `whileNoPcTyped_accepts_leak_violating_tini`.

Basis: execution (Lean kernel check) — `noPcTyped_accepts_implicit_flow_violating_tini` (axioms: `propext`).

#### Result 3 — `cmd-typed-termination-channel-counterexample`

- **Lean:** `Toy.IFC.cmdTyped_allows_termination_channel` (namespace `Toy.IFC`).
- **Kind:** counterexample. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@cmdTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var},
  Γ h = Level.high →
    CmdTyped Γ pc (termChannelProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (termChannelProg h) zeroStore ∧
          ¬Terminates (termChannelProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (termChannelProg h)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var},
  Γ h = .high →
  CmdTyped Γ pc (.whileLoop (.var h) .skip) ∧
  (∀ x, Γ x = .low → zeroStore x = Store.update zeroStore h 1 x) ∧
  (∃ σ', Eval (.whileLoop (.var h) .skip) zeroStore σ') ∧
  ¬ (∃ σ', Eval (.whileLoop (.var h) .skip) (Store.update zeroStore h 1) σ') ∧
  ¬ (∀ σ₁ σ₂ σ₁',
       (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
       Eval (.whileLoop (.var h) .skip) σ₁ σ₁' →
       ∃ σ₂', Eval (.whileLoop (.var h) .skip) σ₂ σ₂' ∧
              (∀ x, Γ x = .low → σ₁' x = σ₂' x))
```

**Plain claim.** For any security labeling `Γ`, program counter `pc`, and `high` variable `h` (`Γ h = high`), the standard type system `CmdTyped Γ pc` accepts `while h do skip` (`termChannelProg h`), which terminates from `zeroStore` and diverges from the `low`-equivalent store `Store.update zeroStore h 1`, refuting termination-sensitive noninterference (`¬ TSNI Γ (termChannelProg h)`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hHigh | Ensures the loop guard variable `h` is `high` so two `low`-equivalent initial stores can disagree on whether the loop exits or loops forever. | tight | `termChannelProg_low_guard_satisfies_tsni` |

**Depth.** shallow.

**Non-vacuity witness.** `twoVarEnv` assigns `h ↦ high`. (`high_var_nonvacuous`)

**Positive control.** `Toy.IFC.termChannelProg_rejected_by_tsTyped`.

**Prior art.**

- Dennis Volpano, Cynthia Irvine, and Geoffrey Smith, "A sound type system for secure flow analysis", Journal of Computer Security 4(2–3):167–187, 1996, DOI 10.3233/JCS-1996-42-304.
- Dennis Volpano and Geoffrey Smith, "Eliminating Covert Flows with Minimum Typings", Proceedings of the 10th IEEE Computer Security Foundations Workshop (CSFW '97), pp. 156–168, June 1997, DOI 10.1109/CSFW.1997.596807.
- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121 (§IV-C).
- Aslan Askarov, Sebastian Hunt, Andrei Sabelfeld, and David Sands, "Termination-Insensitive Noninterference Leaks More Than Just a Bit", ESORICS 2008, LNCS 5283, pp. 333–348, Springer, 2008, DOI 10.1007/978-3-540-88313-5_22.
- Tobias Nipkow and Gerwin Klein, Concrete Semantics: With Isabelle/HOL, Springer, 2014, Chapter 9 (§9.2.6 "What About Termination?"), pp. 115–142, DOI 10.1007/978-3-319-10542-0_9.
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`termination_leak`), https://softwarefoundations.cis.upenn.edu/secf-current/.

**Design question informed.** Demonstrates concretely why classic `pc`-label security typing provides only termination-insensitive noninterference and leaves the termination covert channel open.

**Non-claims:** see Boundaries, Result 3.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `tsni_char_nonvacuous`, `probeProg_cmdTyped`, `probeProg_termination_profile_determines_secret`, `lowGuardWhileTyped_allows_termination_channel`, `pcLowWhileTyped_allows_termination_channel`.

Basis: execution (Lean kernel check) — `cmdTyped_allows_termination_channel` (axioms: `propext`).

#### Result 4 — `cmd-typed-implies-tini-hyperprop`

- **Lean:** `Toy.IFC.cmdTyped_implies_tiniHyperprop` (namespace `Toy.IFC`).
- **Kind:** theorem. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@cmdTyped_implies_tiniHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → tiniHyperprop Γ (ioBehavior c)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c →
  ∀ (t₁ t₂ : Store Var × Store Var),
    Eval c t₁.1 t₁.2 →
    Eval c t₂.1 t₂.2 →
    (∀ x, Γ x = .low → t₁.1 x = t₂.1 x) →
    (∀ x, Γ x = .low → t₁.2 x = t₂.2 x)
```

**Plain claim.** As a definitional corollary of `cmdTyped_implies_tini` via `tini_iff_tiniHyperprop`, any command well typed under `CmdTyped Γ pc c` has terminating big-step I/O behavior `ioBehavior c` satisfying the 2-safety hyperproperty `tiniHyperprop Γ`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hTyped | Ensures `c` has no explicit or implicit flows from `high` to `low`, guaranteeing pairwise `LowEq` agreement across all pairs of terminating runs in `ioBehavior c`. | tight | `untyped_explicit_flow_violates_tiniHyperprop` |

**Depth.** definitional.

**Non-vacuity witness.** Same two concrete witnesses as `cmd-typed-implies-tini`: `sampleTypedProg` (loop-free high conditional + low write) and `whileHZero` (terminating high-guarded loop) under `twoVarEnv` and `pc = low`. (`cmdTyped_implies_tini_nonvacuous`, `cmdTyped_implies_tini_nonvacuous_highLoop`)

**Prior art.**

- Gilles Barthe, Pedro R. D'Argenio, and Tamara Rezk, "Secure Information Flow by Self-Composition", Proceedings of the 17th IEEE Computer Security Foundations Workshop (CSFW 2004), pp. 100–114, DOI 10.1109/CSFW.2004.1310735 (journal version: Mathematical Structures in Computer Science 21(6):1207–1252, 2011, DOI 10.1017/S0960129511000193).
- Tachio Terauchi and Alex Aiken, "Secure Information Flow as a Safety Problem", Static Analysis (SAS 2005), LNCS 3672, pp. 352–367, Springer, 2005, DOI 10.1007/11547662_24.
- Michael R. Clarkson and Fred B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, DOI 10.3233/JCS-2009-0393.

**Design question informed.** Reference point (definitional corollary of `cmd-typed-implies-tini`): bridges static security typing into the hyperproperty vocabulary (`tini_iff_tiniHyperprop`, `tiniHyperprop_isTwoSafety`, `tiniHyperprop_subsetClosed`), showing `CmdTyped` enforces a relational 2-safety policy on terminating I/O behaviors.

**Non-claims:** see Boundaries, Result 4.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `cmdTyped_implies_tini`, `tini_iff_tiniHyperprop`.

Basis: execution (Lean kernel check) — `cmdTyped_implies_tiniHyperprop` (axioms: `propext`).

#### Result 5 — `two-safety-implies-subset-closed`

- **Lean:** `Toy.IFC.isTwoSafety_implies_subsetClosed` (namespace `Toy.IFC`).
- **Kind:** theorem. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@isTwoSafety_implies_subsetClosed : ∀ {α : Type} {H : Hyperproperty α}, IsTwoSafety H → SubsetClosed H
```

Unfolded statement (key definitions expanded):

```lean
∀ {α : Type} {H : (α → Prop) → Prop},
  (∀ S : α → Prop, H S ↔ ∀ t₁ t₂, S t₁ → S t₂ → H (fun t => t = t₁ ∨ t = t₂)) →
  ∀ S₁ S₂ : α → Prop, (∀ t, S₁ t → S₂ t) → H S₂ → H S₁
```

**Plain claim.** Every pairwise-determined hyperproperty over complete observations (`IsTwoSafety H`, proved equivalent to the non-empty bad-pair condition `CSTwoSafety H`) is subset-closed (`SubsetClosed H`), meaning any sub-behavior `S₁ ⊆ S₂` of a compliant trace set `S₂` remains compliant.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| h2 | Ensures membership in `H` is completely determined by checking every pair of traces `{t₁, t₂}` in the trace set, which is preserved downward when traces are removed. | tight | `nonEmptyTraceSet_not_subsetClosed` |

Definitions used by this counterexample and by the first non-claim (both printed under Evidence, Core definitions): `nonEmptyTraceSet := fun S => ∃ t, S t`, instantiated at `α := Unit` in `nonEmptyTraceSet_not_subsetClosed`; and `atMostTwoTraces := fun S => ∀ t₁ t₂ t₃, S t₁ → S t₂ → S t₃ → t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃`, instantiated at `α := Fin 3` in `atMostTwoTraces_subsetClosed_not_twoSafety`. Under Evidence, both statements are printed with `set_option pp.analyze true`, which displays these instantiations; default `#check` output omits them.

**Depth.** shallow.

**Non-vacuity witness.** `tiniHyperprop twoVarEnv` satisfies `IsTwoSafety`. (`isTwoSafety_implies_subsetClosed_nonvacuous`)

**Prior art.**

- Michael R. Clarkson and Fred B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, DOI 10.3233/JCS-2009-0393 (Theorem 1: `SHP ⊂ SSC`).

**Design question informed.** Supporting lemma / reference point (generic hyperproperty fact without information-flow content): formalizes why pairwise-determined 2-safety policies (such as `tiniHyperprop` and `tsniOutHyperprop`) are preserved under trace-set subset refinement.

**Non-claims:** see Boundaries, Result 5.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `atMostTwoTraces_subsetClosed_not_twoSafety`, `isTwoSafety_iff_csTwoSafety`, `isTwoSafety_holds_empty`, `false_hyperprop_not_isTwoSafety`.

Basis: execution (Lean kernel check) — `isTwoSafety_implies_subsetClosed` (axioms: `propext`).

#### Result 6 — `tini-hyperprop-is-two-safety`

- **Lean:** `Toy.IFC.tiniHyperprop_isTwoSafety`, `Toy.IFC.tiniHyperprop_subsetClosed` (namespace `Toy.IFC`).
- **Kind:** theorem. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@tiniHyperprop_isTwoSafety : ∀ {Var : Type} (Γ : Var → Level), IsTwoSafety (tiniHyperprop Γ)
@tiniHyperprop_subsetClosed : ∀ {Var : Type} (Γ : Var → Level), SubsetClosed (tiniHyperprop Γ)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} (Γ : Var → Level) (S : Store Var × Store Var → Prop),
  (∀ t₁ t₂, S t₁ → S t₂ → (∀ x, Γ x = .low → t₁.1 x = t₂.1 x) →
     (∀ x, Γ x = .low → t₁.2 x = t₂.2 x)) ↔
  ∀ t₁ t₂, S t₁ → S t₂ →
    ∀ a b, (a = t₁ ∨ a = t₂) → (b = t₁ ∨ b = t₂) →
      (∀ x, Γ x = .low → a.1 x = b.1 x) → (∀ x, Γ x = .low → a.2 x = b.2 x)

∀ {Var : Type} (Γ : Var → Level)
  (S₁ S₂ : Store Var × Store Var → Prop),
  (∀ t, S₁ t → S₂ t) →
  tiniHyperprop Γ S₂ → tiniHyperprop Γ S₁
```

**Plain claim.** For every security labeling `Γ : Var → Level`, the batch-job termination-insensitive noninterference hyperproperty `tiniHyperprop Γ` is a 2-safety hyperproperty (`IsTwoSafety (tiniHyperprop Γ)`), and hence subset-closed (`tiniHyperprop_subsetClosed`).

**Hypothesis ledger.**

None (universally valid for all types/labelings/commands in the signature; any internal determinism or classical reasoning is noted in Boundaries).

**Depth.** definitional.

**Non-vacuity witness.** `tiniHyperprop twoVarEnv` is a nontrivial hyperproperty: it accepts `ioBehavior .skip` and rejects `ioBehavior (explicitFlowProg .l .h)`. (`tiniHyperprop_isTwoSafety_nonvacuous`)

**Prior art.**

- Tachio Terauchi and Alex Aiken, "Secure Information Flow as a Safety Problem", Static Analysis (SAS 2005), LNCS 3672, pp. 352–367, Springer, 2005, DOI 10.1007/11547662_24 (Definition 4 and Theorem 1).
- Michael R. Clarkson and Fred B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, DOI 10.3233/JCS-2009-0393 (§7.2.1).

**Design question informed.** Reference point (definitional unfolding of `tiniHyperprop`): places batch-job TINI in the complete-observation 2-safety and subset-closed classes, contrasting with `tsniHyperprop` over terminating pairs.

**Non-claims:** see Boundaries, Result 6.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `tiniHyperprop_not_oneSafety`, `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`, `isTwoSafety_iff_csTwoSafety`, `isTwoSafety_holds_empty`, `false_hyperprop_not_isTwoSafety`.

Basis: execution (Lean kernel check) — `tiniHyperprop_isTwoSafety` (axioms: none); `tiniHyperprop_subsetClosed` (axioms: `propext`).

#### Result 7 — `tsni-hyperprop-not-subset-closed`

- **Lean:** `Toy.IFC.tsniHyperprop_termPairs_not_subsetClosed_of_high_var`, `Toy.IFC.tsniHyperprop_termPairs_not_twoSafety_of_high_var` (namespace `Toy.IFC`).
- **Kind:** impossibility. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@tsniHyperprop_termPairs_not_subsetClosed_of_high_var : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ¬SubsetClosed (tsniHyperprop Γ)
@tsniHyperprop_termPairs_not_twoSafety_of_high_var : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ¬IsTwoSafety (tsniHyperprop Γ)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = .high →
  ¬ (∀ S₁ S₂ : Store Var × Store Var → Prop,
       (∀ t, S₁ t → S₂ t) →
       (∀ σ₁ σ₂ σ₁', (∀ x, Γ x = .low → σ₁ x = σ₂ x) → S₂ (σ₁, σ₁') →
          ∃ σ₂', S₂ (σ₂, σ₂') ∧ (∀ x, Γ x = .low → σ₁' x = σ₂' x)) →
       (∀ σ₁ σ₂ σ₁', (∀ x, Γ x = .low → σ₁ x = σ₂ x) → S₁ (σ₁, σ₁') →
          ∃ σ₂', S₁ (σ₂, σ₂') ∧ (∀ x, Γ x = .low → σ₁' x = σ₂' x)))

∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = .high →
  ¬ (∀ S : Store Var × Store Var → Prop,
       tsniHyperprop Γ S ↔
       ∀ t₁ t₂, S t₁ → S t₂ → tsniHyperprop Γ (fun t => t = t₁ ∨ t = t₂))
```

**Plain claim.** Whenever a security labeling `Γ : Var → Level` contains at least one `high` variable (`Γ h = high`), termination-sensitive noninterference over terminating-pair I/O trace sets (`tsniHyperprop Γ`, where divergence is represented by absence of a pair) is not subset-closed (`¬ SubsetClosed (tsniHyperprop Γ)`), and therefore is not a 2-safety hyperproperty (`¬ IsTwoSafety (tsniHyperprop Γ)`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hHigh | Ensures two distinct stores can be `low`-equivalent, so removing one store's terminating trace from the identity behavior breaks the existential co-termination requirement of `tsniHyperprop` (when all variables are `low`, `tsniHyperprop` is both `SubsetClosed` and `IsTwoSafety`, refuting both `¬ SubsetClosed` and `¬ IsTwoSafety`). | tight | `tsniHyperprop_all_low_subsetClosed_witness`, `tsniHyperprop_all_low_isTwoSafety_witness` |

**Depth.** shallow.

**Non-vacuity witness.** `twoVarEnv` assigns `h ↦ high`. (`high_var_nonvacuous`)

**Positive control.** `Toy.IFC.tsniOutHyperprop_isTwoSafety`, `Toy.IFC.tsniOutHyperprop_subsetClosed`, `Toy.IFC.tsni_iff_tsniOutHyperprop`, `Toy.IFC.tsniHyperprop_all_low_subsetClosed`.

**Prior art.**

- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121 (§IV-C explicit-⊥ low-view relation for TSNI).
- Tachio Terauchi and Alex Aiken, "Secure Information Flow as a Safety Problem", Static Analysis (SAS 2005), LNCS 3672, pp. 352–367, Springer, 2005, DOI 10.1007/11547662_24 (§1, characterizing TSNI as a "2-liveness" property observing up to two possibly infinite traces).
- Michael R. Clarkson and Fred B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, DOI 10.3233/JCS-2009-0393 (§7.2.1 "Relational systems" showing `TSRNI` with explicit `s^ω` divergence is neither hypersafety nor hyperliveness for `Rel`, and footnote 23 discussing Terauchi & Aiken's "2-liveness" vs. "2-infinite-safety").

**Design question informed.** Clarifies an observation-model pitfall over behaviors that record only terminating runs (divergence encoded as a missing pair): under that encoding, `tsniHyperprop Γ` is neither subset-closed nor `IsTwoSafety` whenever any secret exists, whereas switching to explicit-outcome behaviors (`OutTrace Var`, `tsniOutHyperprop`) defeats the impossibility.

**Non-claims:** see Boundaries, Result 7.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `tsni_iff_tsniOutHyperprop`, `tsniOutHyperprop_isTwoSafety`, `tsniOutHyperprop_subsetClosed`, `tsni_iff_tini_and_coterminates`, `tsniHyperprop_all_low_subsetClosed`, `tsTyped_implies_tsni`.

Basis: execution (Lean kernel check) — `tsniHyperprop_termPairs_not_subsetClosed_of_high_var` (axioms: `propext`); `tsniHyperprop_termPairs_not_twoSafety_of_high_var` (axioms: `propext`).

#### Result 8 — `ts-typed-implies-tsni`

- **Lean:** `Toy.IFC.tsTyped_implies_tsni` (namespace `Toy.IFC`).
- **Kind:** theorem. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@tsTyped_implies_tsni : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → TSNI Γ c
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c →
  ∀ (σ₁ σ₂ σ₁' : Var → Int),
    (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
    Eval c σ₁ σ₁' →
    ∃ σ₂', Eval c σ₂ σ₂' ∧ (∀ x, Γ x = .low → σ₁' x = σ₂' x)
```

**Plain claim.** Under the termination-sensitive security type system `TsTyped Γ pc c`—which strengthens `CmdTyped` by requiring both `pc = low` and `exprLevel Γ e = low` at every `while` loop—every well-typed command satisfies termination-sensitive noninterference (`TSNI Γ c`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hTyped (base CmdTyped explicit/implicit rules) | Prevents direct explicit flows via `exprLevel Γ e ≤ Γ x` and conditional control-flow implicit flows via `pc ≤ Γ x`. | tight | `untyped_explicit_flow_violates_tsni`, `noPcTyped_implicit_flow_violates_tsni_witness`. For `untyped_explicit_flow_violates_tsni`, kernel-checked: `l := h` is rejected by `TsTyped` and `CmdTyped` at every `pc` and violates `TSNI`; not kernel-checked: that it satisfies the remaining components (`pc` tracking and both `while` conjuncts), which holds by inspection, since at `pc = low` the side condition `pc ≤ Γ l` holds and the program contains no `if` or `while`. For `noPcTyped_implicit_flow_violates_tsni_witness`, acceptance by `NoPcTyped` (the explicit-flow bounds hold) is kernel-checked; the `while` conjuncts hold vacuously because the program is loop-free (by inspection). |
| hTyped (while guard: exprLevel Γ e = low) | Forbids `high`-dependent loop guards so a loop cannot exit on one `low`-equivalent store and diverge on another, even when `pc = low` at the loop. | tight | `pcLowWhileTyped_violates_tsni_witness`, `pcLowWhileTyped_allows_termination_channel` |
| hTyped (while context: pc = low) | Forbids `while` loops inside `high`-guarded conditionals so high-`pc` subcommands are loop-free (total and low-preserving), closing divergence leaks from low-guarded loops under secret branches. | tight | `lowGuardWhileTyped_violates_tsni_witness`, `lowGuardWhileTyped_allows_termination_channel` |

**Depth.** substantive.

**Non-vacuity witness.** Under `twoVarEnv` and `pc = low`, the looping program `while l do (if h then h := h - 1 else h := 0; l := l - 1)` (`sampleTsProg`) satisfies `TsTyped`, enters the loop from two `low`-equivalent stores with `l = 1` and distinct `h` values (`0` vs. `5`), executes opposite high branches, and terminates. (`tsTyped_implies_tsni_nonvacuous`)

**Prior art.**

- Dennis Volpano and Geoffrey Smith, "Eliminating Covert Flows with Minimum Typings", Proceedings of the 10th IEEE Computer Security Foundations Workshop (CSFW '97), pp. 156–168, June 1997, DOI 10.1109/CSFW.1997.596807 (rule `(WHILE)`, Theorem 3.1 Termination Agreement; §5 Theorem 5.3 Timing Agreement for a stricter timing-sensitive discipline).
- Geoffrey Smith and Dennis Volpano, "Secure information flow in a multi-threaded imperative language", Proceedings of the 25th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '98), pp. 355–364, 1998, DOI 10.1145/268946.268975.
- Johan Agat, "Transforming out timing leaks", Proceedings of the 27th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '00), pp. 40–53, January 2000, DOI 10.1145/325694.325702 (timing-leak transformation pointer).
- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121 (§IV-C).
- Tobias Nipkow and Gerwin Klein, Concrete Semantics: With Isabelle/HOL, Springer, 2014, Chapter 9 (§9.2.6 Fig. 9.10, Lemma 9.21, Theorem 9.22), pp. 115–142, DOI 10.1007/978-3-319-10542-0_9; mechanized in Isabelle/HOL HOL-IMP `Sec_TypingT.thy` (`While`, `termi_if_non0`, `noninterference` for `0 ⊢ c`), https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_TypingT.html (this package's arbitrary-`pc` statement generalizes `0 ⊢ c` trivially via `TsTyped.antitone`).
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`ts_well_typed`, `TSWT_While`), https://softwarefoundations.cis.upenn.edu/secf-current/.
- Pasquale Noce, "Information Flow Control via Stateful Intransitive Noninterference in Language IMP", Archive of Formal Proofs, February 2024, https://isa-afp.org/entries/IMP_Noninterference.html.

**Design question informed.** Provides the positive control showing a sufficient syntactic restriction on `while` loops (`pc = low` and `exprLevel Γ e = low`) that closes the termination covert channel while still permitting high conditionals and high-variable mutations inside low-guarded loops; each of the two `while` conjuncts is individually necessary within this rule family, though the restriction is not necessary for `TSNI` itself (see `Toy.IFC.whileHZero_tsni_not_tsTyped`).

**Non-claims:** see Boundaries, Result 8.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `whileOne_tsTyped_low_not_high`, `lowGuardWhileTyped_allows_termination_channel`, `pcLowWhileTyped_allows_termination_channel`, `cmdTyped_allows_termination_channel`, `cmdTyped_violates_tsni_witness`, `whileHZero_tsni_not_tsTyped`, `timingExample_tsTyped`.

Basis: execution (Lean kernel check) — `tsTyped_implies_tsni` (axioms: `propext`).

#### Result 9 — `low-guard-while-typed-termination-channel-counterexample`

- **Lean:** `Toy.IFC.lowGuardWhileTyped_allows_termination_channel` (namespace `Toy.IFC`).
- **Kind:** counterexample. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@lowGuardWhileTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level}
  {h : Var},
  Γ h = Level.high →
    LowGuardWhileTyped Γ pc (highIfLowWhileProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (highIfLowWhileProg h) zeroStore ∧
          ¬Terminates (highIfLowWhileProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (highIfLowWhileProg h)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var},
  Γ h = .high →
  LowGuardWhileTyped Γ pc (.ite (.var h) (.whileLoop (.lit 1) .skip) .skip) ∧
  (∀ x, Γ x = .low → zeroStore x = Store.update zeroStore h 1 x) ∧
  (∃ σ', Eval (.ite (.var h) (.whileLoop (.lit 1) .skip) .skip) zeroStore σ') ∧
  ¬ (∃ σ', Eval (.ite (.var h) (.whileLoop (.lit 1) .skip) .skip) (Store.update zeroStore h 1) σ') ∧
  ¬ (∀ σ₁ σ₂ σ₁',
       (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
       Eval (.ite (.var h) (.whileLoop (.lit 1) .skip) .skip) σ₁ σ₁' →
       ∃ σ₂', Eval (.ite (.var h) (.whileLoop (.lit 1) .skip) .skip) σ₂ σ₂' ∧
              (∀ x, Γ x = .low → σ₁' x = σ₂' x))
```

**Plain claim.** For any security labeling `Γ`, program counter `pc`, and `high` variable `h` (`Γ h = high`), restricting only `while` loop guards to `low` without also requiring `pc = low` (`LowGuardWhileTyped Γ pc`) accepts `if h then (while 1 do skip) else skip` (`highIfLowWhileProg h`), which terminates from `zeroStore` and diverges from `Store.update zeroStore h 1`, violating `TSNI Γ`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hHigh | Ensures the outer `if` guard `h` is secret so one `low`-equivalent run enters the diverging `low`-guarded loop while the other takes `skip`. | tight | `highIfLowWhileProg_low_guard_satisfies_tsni` |

**Depth.** shallow.

**Non-vacuity witness.** `twoVarEnv` assigns `h ↦ high`. (`high_var_nonvacuous`)

**Positive control.** `Toy.IFC.highIfLowWhileProg_rejected_by_tsTyped`.

**Prior art.**

- Dennis Volpano and Geoffrey Smith, "Eliminating Covert Flows with Minimum Typings", Proceedings of the 10th IEEE Computer Security Foundations Workshop (CSFW '97), pp. 156–168, June 1997, DOI 10.1109/CSFW.1997.596807 (contrast §1 prose mentioning only minimum guard type with rule `(WHILE)`, which types the loop itself at the minimum `τ cmd` and thus forbids loops under high branches).
- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121 (§IV-C explicitly noting that Volpano & Smith 1997 disallows both high loops and loops inside high conditionals).
- Tobias Nipkow and Gerwin Klein, Concrete Semantics: With Isabelle/HOL, Springer, 2014, Chapter 9 (§9.2.6 Fig. 9.10), pp. 115–142, DOI 10.1007/978-3-319-10542-0_9; mechanized in Isabelle/HOL HOL-IMP `Sec_TypingT.thy` (`While`), https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_TypingT.html.
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`TSWT_While`, `termination_leak`), https://softwarefoundations.cis.upenn.edu/secf-current/.

**Design question informed.** Documents the soundness pitfall of reading informal descriptions of termination-sensitive typing (e.g., "loop guards must be low") literally: enforcing `exprLevel Γ e = low` on `while` guards alone is unsound unless `pc = low` is also enforced at every `while` loop.

**Non-claims:** see Boundaries, Result 9.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `pcLowWhileTyped_allows_termination_channel`, `lowGuardWhileTyped_implies_cmdTyped`, `cmdTyped_implies_tini`, `lowGuardWhileTyped_neg_while_h`, `whileHZero_tsni_not_tsTyped`.

Basis: execution (Lean kernel check) — `lowGuardWhileTyped_allows_termination_channel` (axioms: `propext`).

#### Result 10 — `tsni-iff-tini-and-coterminates`

- **Lean:** `Toy.IFC.tsni_iff_tini_and_coterminates` (namespace `Toy.IFC`).
- **Kind:** characterization. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@tsni_iff_tini_and_coterminates : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ TINI Γ c ∧ CoTerminates Γ c
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  (∀ σ₁ σ₂ σ₁',
     (∀ x, Γ x = .low → σ₁ x = σ₂ x) → Eval c σ₁ σ₁' →
     ∃ σ₂', Eval c σ₂ σ₂' ∧ (∀ x, Γ x = .low → σ₁' x = σ₂' x))
  ↔
  (∀ σ₁ σ₂ σ₁' σ₂',
     (∀ x, Γ x = .low → σ₁ x = σ₂ x) → Eval c σ₁ σ₁' → Eval c σ₂ σ₂' →
     (∀ x, Γ x = .low → σ₁' x = σ₂' x)) ∧
  (∀ σ₁ σ₂,
     (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
     ((∃ σ₁', Eval c σ₁ σ₁') ↔ (∃ σ₂', Eval c σ₂ σ₂')))
```

**Plain claim.** In this deterministic big-step imperative semantics, a command `c` satisfies termination-sensitive noninterference (`TSNI Γ c`) if and only if it satisfies both termination-insensitive noninterference (`TINI Γ c`) and co-termination on `low`-equivalent initial stores (`CoTerminates Γ c`).

**Hypothesis ledger.**

None (universally valid for all types/labelings/commands in the signature; any internal determinism or classical reasoning is noted in Boundaries).

**Depth.** shallow.

**Non-vacuity witness.** `tsni_char_nonvacuous` witnesses all three cases under `twoVarEnv`: `l := l + 1` satisfies `TSNI` (both conjuncts), `while h do skip` satisfies `TINI ∧ ¬ CoTerminates`, and `l := h` satisfies `CoTerminates ∧ ¬ TINI` (`coTerminates_without_tini`), proving the two right-hand conjuncts are mutually independent. (`tsni_char_nonvacuous`)

**Prior art.**

- Dennis Volpano and Geoffrey Smith, "Eliminating Covert Flows with Minimum Typings", Proceedings of the 10th IEEE Computer Security Foundations Workshop (CSFW '97), pp. 156–168, June 1997, DOI 10.1109/CSFW.1997.596807 (Theorem 3.1 Termination Agreement and its alternative statement splitting into joint divergence or joint termination with agreeing low memories).
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`tsni_com_tsni_alt_same : ∀ L c, tsni_com L c ↔ tsni_alt L c`, proved using `ceval_deterministic`), https://softwarefoundations.cis.upenn.edu/secf-current/.

**Design question informed.** Pins down the exact logical gap between the classic guarantee (`TINI`) and its termination-sensitive strengthening (`TSNI`) in deterministic sequential languages: co-termination on low-equivalent inputs is both necessary and sufficient to bridge the two.

**Non-claims:** see Boundaries, Result 10.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `eval_deterministic`, `nondet_existential_tsni_not_tini`.

Basis: execution (Lean kernel check) — `tsni_iff_tini_and_coterminates` (axioms: none).

#### Result 11 — `pc-low-while-typed-termination-channel-counterexample`

- **Lean:** `Toy.IFC.pcLowWhileTyped_allows_termination_channel` (namespace `Toy.IFC`).
- **Kind:** counterexample. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@pcLowWhileTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {h : Var},
  Γ h = Level.high →
    PcLowWhileTyped Γ Level.low (termChannelProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (termChannelProg h) zeroStore ∧
          ¬Terminates (termChannelProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (termChannelProg h)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {h : Var},
  Γ h = .high →
  PcLowWhileTyped Γ .low (.whileLoop (.var h) .skip) ∧
  (∀ x, Γ x = .low → zeroStore x = Store.update zeroStore h 1 x) ∧
  (∃ σ', Eval (.whileLoop (.var h) .skip) zeroStore σ') ∧
  ¬ (∃ σ', Eval (.whileLoop (.var h) .skip) (Store.update zeroStore h 1) σ') ∧
  ¬ (∀ σ₁ σ₂ σ₁',
       (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
       Eval (.whileLoop (.var h) .skip) σ₁ σ₁' →
       ∃ σ₂', Eval (.whileLoop (.var h) .skip) σ₂ σ₂' ∧
              (∀ x, Γ x = .low → σ₁' x = σ₂' x))
```

**Plain claim.** For any security labeling `Γ` and `high` variable `h` (`Γ h = high`), requiring `pc = low` at every `while` loop without also requiring `exprLevel Γ e = low` (`PcLowWhileTyped Γ .low`) accepts `while h do skip` (`termChannelProg h`), which terminates from `zeroStore` and diverges from `Store.update zeroStore h 1`, violating `TSNI Γ`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hHigh | Ensures the loop guard `h` is secret so two `low`-equivalent stores disagree on whether the loop terminates or diverges. | tight | `termChannelProg_low_guard_satisfies_tsni_pcLow` |

**Depth.** shallow.

**Non-vacuity witness.** `twoVarEnv` assigns `h ↦ high`. (`high_var_nonvacuous`)

**Positive control.** `Toy.IFC.termChannelProg_rejected_by_tsTyped`.

**Prior art.**

- Dennis Volpano and Geoffrey Smith, "Eliminating Covert Flows with Minimum Typings", Proceedings of the 10th IEEE Computer Security Foundations Workshop (CSFW '97), pp. 156–168, June 1997, DOI 10.1109/CSFW.1997.596807 (rule `(WHILE)`).
- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121 (§IV-C).
- Tobias Nipkow and Gerwin Klein, Concrete Semantics: With Isabelle/HOL, Springer, 2014, Chapter 9 (§9.2.6 Fig. 9.10), pp. 115–142, DOI 10.1007/978-3-319-10542-0_9; HOL-IMP `Sec_TypingT.thy`, https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_TypingT.html.
- Cătălin Hriţcu and Yonghyun Kim et al., Security Foundations (Software Foundations Vol. 7, Version 1.2, 2026), chapter `StaticIFC` (`TSWT_While`), https://softwarefoundations.cis.upenn.edu/secf-current/.

**Design question informed.** Completes the symmetric ablation of `TsTyped.whileLoop`, isolating the individual necessity of `exprLevel Γ e = low` within this rule family even when `pc = low` is enforced at every `while` loop.

**Non-claims:** see Boundaries, Result 11.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `pcLowWhileTyped_implies_cmdTyped`, `cmdTyped_implies_tini`, `pcLowWhileTyped_neg_high_if_low_while`, `lowGuardWhileTyped_allows_termination_channel`, `whileHZero_tsni_not_tsTyped`.

Basis: execution (Lean kernel check) — `pcLowWhileTyped_allows_termination_channel` (axioms: `propext`).

#### Result 12 — `while-no-pc-typed-implicit-flow-counterexample`

- **Lean:** `Toy.IFC.whileNoPcTyped_accepts_leak_violating_tini` (namespace `Toy.IFC`).
- **Kind:** counterexample. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@whileNoPcTyped_accepts_leak_violating_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → WhileNoPcTyped Γ Level.low (whileLeakProg l h) ∧ ¬TINI Γ (whileLeakProg l h)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = .low → Γ h = .high →
  WhileNoPcTyped Γ .low (.whileLoop (.var h) (.seq (.assign l (.lit 1)) (.assign h (.lit 0)))) ∧
  ¬ (∀ σ₁ σ₂ σ₁' σ₂',
       (∀ x, Γ x = .low → σ₁ x = σ₂ x) →
       Eval (.whileLoop (.var h) (.seq (.assign l (.lit 1)) (.assign h (.lit 0)))) σ₁ σ₁' →
       Eval (.whileLoop (.var h) (.seq (.assign l (.lit 1)) (.assign h (.lit 0)))) σ₂ σ₂' →
       (∀ x, Γ x = .low → σ₁' x = σ₂' x))
```

**Plain claim.** For any security labeling `Γ` with `Γ l = low` and `Γ h = high`, raising `pc` at `if` while omitting `pc` tracking at `while` (`WhileNoPcTyped Γ .low`) accepts `while h do (l := 1; h := 0)` (`whileLeakProg l h`), which terminates on two `low`-equivalent stores with different final values of `l`, violating `TINI Γ`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample |
|---|---|---|---|
| hLow | Ensures the assigned variable `l` is `low`-observable so writing `1` on one run and leaving `0` on the other breaks `LowEq`. | tight | `whileLeakProg_target_high_satisfies_tini` |
| hHigh | Ensures the loop guard `h` is secret so two `low`-equivalent initial stores can differ on whether the loop body executes. | tight | `whileLeakProg_guard_low_satisfies_tini` |

**Depth.** shallow.

**Non-vacuity witness.** `twoVarEnv` assigns `l ↦ low` and `h ↦ high`. (`noPcTyped_implicit_flow_nonvacuous`)

**Positive control.** `Toy.IFC.whileLeakProg_rejected_by_cmdTyped`.

**Prior art.**

- Dorothy E. Denning and Peter J. Denning, "Certification of programs for secure information flow", Communications of the ACM 20(7):504–513, July 1977, DOI 10.1145/359636.359712.
- Dennis Volpano, Cynthia Irvine, and Geoffrey Smith, "A sound type system for secure flow analysis", Journal of Computer Security 4(2–3):167–187, 1996, DOI 10.3233/JCS-1996-42-304.
- Tobias Nipkow and Gerwin Klein, Concrete Semantics: With Isabelle/HOL, Springer, 2014, Chapter 9 (§9.2.2), pp. 115–142, DOI 10.1007/978-3-319-10542-0_9; HOL-IMP `Sec_Typing.thy`, https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_Typing.html.

**Design question informed.** Isolates the `while`-loop control-dependence check in `CmdTyped`, proving that raising `pc` at conditionals alone is insufficient unless `pc` is also raised by the loop guard at `while`.

**Non-claims:** see Boundaries, Result 12.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `whileNoPcTyped_neg_implicit_flow`.

Basis: execution (Lean kernel check) — `whileNoPcTyped_accepts_leak_violating_tini` (axioms: `propext`).

#### Result 13 — `tsni-out-hyperprop-is-two-safety`

- **Lean:** `Toy.IFC.tsni_iff_tsniOutHyperprop`, `Toy.IFC.tsniOutHyperprop_isTwoSafety`, `Toy.IFC.tsniOutHyperprop_subsetClosed` (namespace `Toy.IFC`).
- **Kind:** characterization. **Tier:** T0.

Statement, as printed by `#check` on the built library:

```lean
@tsni_iff_tsniOutHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ tsniOutHyperprop Γ (outcomeBehavior c)
@tsniOutHyperprop_isTwoSafety : ∀ {Var : Type} (Γ : Var → Level), IsTwoSafety (tsniOutHyperprop Γ)
@tsniOutHyperprop_subsetClosed : ∀ {Var : Type} (Γ : Var → Level), SubsetClosed (tsniOutHyperprop Γ)
```

Unfolded statement (key definitions expanded):

```lean
∀ {Var : Type} [DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  (∀ σ₁ σ₂ σ₁', (∀ x, Γ x = .low → σ₁ x = σ₂ x) → Eval c σ₁ σ₁' →
     ∃ σ₂', Eval c σ₂ σ₂' ∧ (∀ x, Γ x = .low → σ₁' x = σ₂' x))
  ↔
  (∀ t₁ t₂ : Store Var × Option (Store Var),
     (match t₁.2 with | some σ' => Eval c t₁.1 σ' | none => ¬ ∃ σ', Eval c t₁.1 σ') →
     (match t₂.2 with | some σ' => Eval c t₂.1 σ' | none => ¬ ∃ σ', Eval c t₂.1 σ') →
     (∀ x, Γ x = .low → t₁.1 x = t₂.1 x) →
     match t₁.2, t₂.2 with
     | some a, some b => ∀ x, Γ x = .low → a x = b x
     | none, none => True
     | _, _ => False)

∀ {Var : Type} (Γ : Var → Level), IsTwoSafety (tsniOutHyperprop Γ)
∀ {Var : Type} (Γ : Var → Level), SubsetClosed (tsniOutHyperprop Γ)
```

**Plain claim.** When divergence is represented explicitly as `none : Option (Store Var)` (`OutTrace Var`, `outcomeBehavior c`), command-level `TSNI Γ c` is equivalent to `tsniOutHyperprop Γ (outcomeBehavior c)`, and for every security labeling `Γ` the hyperproperty `tsniOutHyperprop Γ` satisfies `IsTwoSafety` and `SubsetClosed`.

**Hypothesis ledger.**

None (universally valid for all types/labelings/commands in the signature; any internal determinism or classical reasoning is noted in Boundaries).

**Depth.** shallow.

**Non-vacuity witness.** Under the mixed environment `twoVarEnv`, `tsniOutHyperprop twoVarEnv` is nontrivial: it accepts `outcomeBehavior .skip` and rejects `outcomeBehavior (termChannelProg .h)`. (`tsniOutHyperprop_nonvacuous`)

**Prior art.**

- Andrei Sabelfeld and Andrew C. Myers, "Language-based information-flow security", IEEE Journal on Selected Areas in Communications 21(1):5–19, January 2003, DOI 10.1109/JSAC.2002.806121 (§IV-C explicit-⊥ low-view relation for TSNI).
- Tachio Terauchi and Alex Aiken, "Secure Information Flow as a Safety Problem", Static Analysis (SAS 2005), LNCS 3672, pp. 352–367, Springer, 2005, DOI 10.1007/11547662_24 (§1).
- Michael R. Clarkson and Fred B. Schneider, "Hyperproperties", Journal of Computer Security 18(6):1157–1210, 2010, DOI 10.3233/JCS-2009-0393 (§7.2.1 and footnote 23).

**Design question informed.** Provides the non-degenerate escape hatch for `tsni-hyperprop-not-subset-closed`, showing that over complete explicit-outcome observations (`Option (Store Var)`), deterministic TSNI is a pairwise 2-safety (`IsTwoSafety`) and subset-closed hyperproperty.

**Non-claims:** see Boundaries, Result 13.

**Scope witnesses (`scope_witnesses_lean`: every package theorem named in the non-claims; statements printed under Evidence).** `tsni_iff_tsniOutHyperprop`, `eval_deterministic`, `tsniOutHyperprop_isTwoSafety`, `isTwoSafety_iff_csTwoSafety`, `isTwoSafety_holds_empty`, `false_hyperprop_not_isTwoSafety`.

Basis: execution (Lean kernel check) — `tsni_iff_tsniOutHyperprop` (axioms: `Classical.choice`, `Quot.sound`, `propext`); `tsniOutHyperprop_isTwoSafety` (axioms: `propext`); `tsniOutHyperprop_subsetClosed` (axioms: `propext`).

### Modeling bridge

Basis: derived (modeling bridge) from inspecting the formal definitions in `Toy/IFC/` alongside the primary literature (`Nipkow & Klein 2014`, `Volpano, Irvine & Smith 1996`, `Volpano & Smith 1997`, `Sabelfeld & Myers 2003`, `Askarov et al. 2008`, `Clarkson & Schneider 2010`, and `Terauchi & Aiken 2005`). None of the bridges to external systems below are kernel-checked.

- **Mapping `CmdTyped` / `TsTyped` to a real static analyzer or compiler pass.** Soundness of `CmdTyped` (Result 1) and `TsTyped` (Result 8) carries over to a real imperative language only when every premise of the toy semantics holds for the real target: total expression evaluation (no traps, panics, or division-by-zero exceptions), deterministic single-threaded control flow, static flow-insensitive variable security classes with no aliasing or indirect memory writes bypassing `Γ x`, and attacker observation limited to terminating final public values (plus termination vs. divergence under `TSNI`). Where an implementation adds exceptions, heap aliasing, concurrency, intermediate outputs, or step-count/wall-clock timing channels, `TINI` and `TSNI` in this model do not suffice.
- **Why per-run `TINI` does not bound cumulative leakage across chosen inputs.** Result 1 certifies `TINI` per execution, and Result 3 shows `CmdTyped` leaves a termination channel (`while h do skip`). Reasoning: in an interactive or multi-run setting where an attacker supplies chosen `low` inputs and observes termination per run, `probeProg` (`while l < h do skip`, proved well-typed in `probeProg_cmdTyped` and invertible in `probeProg_termination_profile_determines_secret`) reveals `σ h` uniquely. Thus the informal "one bit per run" intuition (derived, not kernel-checked; see Applicability) does not cap total information leakage across queries.
- **Complete-observation `IsTwoSafety` vs. infinite-trace prefix hypersafety.** Under `IOTrace`, Result 7 proves `tsniHyperprop` fails `SubsetClosed` and `IsTwoSafety` because divergence is encoded by absence of a pair (`S₁ ⊆ S₂` can delete a terminating witness for a low-equivalent input). Switching to explicit `Option (Store Var)` outcomes (`OutTrace`, Result 13) makes `tsniOutHyperprop` satisfy `IsTwoSafety` and `SubsetClosed`. In Clarkson & Schneider's (2010, §7.2.1) infinite-trace prefix topology (not formalized here), relational `TSRNI` with explicit `s^ω` divergence still fails hypersafety in that (lower Vietoris) topology for a different reason—divergence requires observing an entire infinite trace rather than a finite prefix.

## Boundaries

### Non-claims (per result)

Each list states what the result does **not** show. Package theorems cited in parentheses are fully proved in the library and printed under Evidence.

**Result 1 — `cmd-typed-implies-tini`.**

1. `CmdTyped` is the syntax-directed program-counter presentation, matching Nipkow & Klein's `sec_type` specialized to two levels. It is not Volpano–Irvine–Smith's original formulation, which uses command types `τ cmd`, contravariant subtyping, and an arbitrary lattice. Equivalence with that formulation is not proved here.
2. Does not establish termination-sensitive noninterference (`TSNI`) or co-termination (`CoTerminates`); a well-typed `while` loop guarded by a `high` variable can diverge on one `low`-equivalent input and terminate on another (see `Toy.IFC.cmdTyped_allows_termination_channel`).
3. No theorem here states or proves a bound on the information leaked per run. The informal one-bit intuition is derived, not kernel-checked: for a fixed low input, `TINI` (which `CmdTyped` guarantees by Result 1) and determinism of `Eval` leave a low observer only two possible outcomes of a run (divergence, or termination with the single low final state shared by all terminating low-equivalent runs), so the intuition applies at most per run. It does not bound total leakage: an attacker who can rerun a well-typed program with chosen low inputs can recover a secret completely through termination alone. For example, `while l < h do skip` is accepted by `CmdTyped` at every `pc`, and whether it terminates, as a function of the low input `l`, determines `h` exactly.
4. The repeated-run termination leak above is kernel-checked in `Toy.IFC.probeProg_cmdTyped` and `Toy.IFC.probeProg_termination_profile_determines_secret`.
5. Does not rule out timing or step-count side channels; the big-step semantics `Eval` does not model execution steps or wall-clock time.
6. Does not cover interactive or intermediate-output languages (progress-sensitive noninterference), where termination-insensitive noninterference permits leaking all secrets via repeated public outputs prior to divergence, although the best attack is brute force and cannot reliably learn a uniformly distributed secret in polynomial time with more than negligible advantage (Askarov et al. 2008).
7. Does not cover partial expressions or runtime exceptions (e.g., division by zero), nondeterminism, concurrency, declassification, flow-sensitive variable labels, or arbitrary multi-level security lattices beyond `{low, high}`.
8. Does not claim completeness: `CmdTyped` is a conservative syntactic approximation and rejects semantically noninterfering programs such as `l := h - h` (`Toy.IFC.subSelf_tini_not_cmdTyped`) and `if h then l := 0 else l := 0` (`Toy.IFC.constBranch_tini_not_cmdTyped`).

**Result 2 — `no-pc-typed-implicit-flow-counterexample`.**

1. Does not show that a program-counter label is the only sound way to block implicit flows. It shows that omitting control-dependence tracking entirely (`NoPcTyped`) is unsound. Other sound disciplines exist: forbidding high guards in `if` and `while` altogether (no pc label needed; such a system embeds into `CmdTyped Γ .low`), Volpano–Irvine–Smith's original command types `τ cmd` with subsumption, and flow-sensitive security typing (Hunt & Sands 2006).
2. The `pc`-free high-guard-forbidding discipline noted above is formalized as `Toy.IFC.NoHighGuardTyped`, with `Toy.IFC.noHighGuardTyped_implies_cmdTyped_low` and `Toy.IFC.noHighGuardTyped_neg_implicit_flow`.
3. Does not claim that every program accepted by `NoPcTyped` violates `TINI`; pure low computations and semantically constant branches (e.g., `if h then l := 0 else l := 0`, see `Toy.IFC.constBranch_tini_not_cmdTyped`) satisfy `TINI`.
4. Does not claim that `NoPcTyped` omits explicit-flow checks; `NoPcTyped` still rejects direct leaks such as `l := h` (`Toy.IFC.noPcTyped_neg_explicit_flow`).
5. Witnesses an implicit flow through `if` (`ite`); omitting `pc` only at `while` while keeping `pc` at `if` is tested separately in `Toy.IFC.whileNoPcTyped_accepts_leak_violating_tini` (id `while-no-pc-typed-implicit-flow-counterexample`).

**Result 3 — `cmd-typed-termination-channel-counterexample`.**

1. Does not refute `TINI` for `CmdTyped`: `while h do skip` vacuously preserves `LowEq` whenever both runs terminate (in fact it satisfies `TINI`, see `Toy.IFC.tsni_char_nonvacuous`).
2. No theorem here states or proves a bound on the information leaked per run. The informal one-bit intuition is derived, not kernel-checked: for a fixed low input, `TINI` (which `CmdTyped` guarantees by Result 1) and determinism of `Eval` leave a low observer only two possible outcomes of a run (divergence, or termination with the single low final state shared by all terminating low-equivalent runs), so the intuition applies at most per run. It does not bound total leakage: an attacker who can rerun a well-typed program with chosen low inputs can recover a secret completely through termination alone. For example, `while l < h do skip` is accepted by `CmdTyped` at every `pc`, and whether it terminates, as a function of the low input `l`, determines `h` exactly.
3. The repeated-run termination leak above is kernel-checked in `Toy.IFC.probeProg_cmdTyped` and `Toy.IFC.probeProg_termination_profile_determines_secret`.
4. Does not model interactive languages with intermediate public outputs; Askarov et al. (2008) show that with intermediate outputs TINI permits leaking all secrets, while also proving an upper bound: the best an attacker can do is a brute-force attack, so the attacker cannot reliably learn a secret in polynomial time in the size of the secret (negligible advantage for uniformly distributed secrets).
5. Does not claim that forbidding high-guarded `while` loops alone eliminates termination channels; a low-guarded loop nested inside a high conditional still leaks termination unless `pc = low` is also required on `while` (see `Toy.IFC.lowGuardWhileTyped_allows_termination_channel`), and conversely requiring `pc = low` alone without a low guard still admits `while h do skip` (see `Toy.IFC.pcLowWhileTyped_allows_termination_channel`).

**Result 4 — `cmd-typed-implies-tini-hyperprop`.**

1. Reference point / definitional corollary: proved directly in one line from `Toy.IFC.cmdTyped_implies_tini` by argument permutation (`Toy.IFC.tini_iff_tiniHyperprop`); all substantive semantic induction lives in `Toy.IFC.cmdTyped_implies_tini`.
2. Models a command's behavior strictly as its set of terminating `(σ, σ')` pairs (`ioBehavior c`); non-terminating runs do not appear as elements of `ioBehavior c`, so divergence channels are invisible to `tiniHyperprop`.
3. Does not establish that `ioBehavior c` satisfies `tsniHyperprop Γ` or any hyperliveness property.

**Result 5 — `two-safety-implies-subset-closed`.**

1. The converse is false: `SubsetClosed` is strictly weaker than `IsTwoSafety`, witnessed by the 3-safety cardinality property `atMostTwoTraces` on `Fin 3` (`Toy.IFC.atMostTwoTraces_subsetClosed_not_twoSafety`).
2. `IsTwoSafety` is a package-specific pairwise-determinedness notion proved equivalent to the non-empty bad-pair formulation `Toy.IFC.CSTwoSafety` (`Toy.IFC.isTwoSafety_iff_csTwoSafety`) and forcing `H ∅` (`Toy.IFC.isTwoSafety_holds_empty`), so the empty hyperproperty `fun _ => False`, which holds of no trace set, fails it (`Toy.IFC.false_hyperprop_not_isTwoSafety`). Despite its name, that theorem is not about Clarkson & Schneider's (2010) hyperproperty `false`, which they define as `{∅}` (it holds of exactly the empty trace set) and call hypersafety; `{∅}` also satisfies this package's `IsTwoSafety` (derived, not kernel-checked: for a non-empty `S` both sides of the defining equivalence are false, and for the empty `S` both are true). Under a discrete-observation reading (`M ≤ T` iff `M ⊆ T`) plus `H ∅`, `IsTwoSafety` coincides with Clarkson & Schneider 2-hypersafety (not formalized here). The two notions differ on the empty hyperproperty: Clarkson & Schneider's definition admits it as hypersafety with the empty observation `M = ∅` (derived from their definitions, which the paper does not spell out for this case: `Obs = Pfin(Ψfin)` contains `∅`, and `∅ ≤ T` for every `T`). Their prefix-based infinite-trace topology (the lower Vietoris construction applied to the Plotkin topology) is not formalized.
3. Differs from Terauchi & Aiken's (2005, Def. 4) notion of 2-safety, which is a set of programs defined with an explicit `⊥` outcome for nontermination.

**Result 6 — `tini-hyperprop-is-two-safety`.**

1. Does not make `tiniHyperprop Γ` a 1-safety (single-trace) property; in fact `Toy.IFC.tiniHyperprop_not_oneSafety` proves `¬ IsOneSafety (tiniHyperprop twoVarEnv)` because every singleton trace set satisfies `tiniHyperprop` while `ioBehavior (l := h)` does not.
2. Does not extend to terminating-pairs TSNI (`tsniHyperprop Γ`), which fails subset closure and 2-safety whenever any `high` variable exists (see `Toy.IFC.tsniHyperprop_termPairs_not_subsetClosed_of_high_var`).
3. `IsTwoSafety` is this package's complete-observation pairwise-determinedness notion (`Toy.IFC.isTwoSafety_iff_csTwoSafety`, `Toy.IFC.isTwoSafety_holds_empty`, `Toy.IFC.false_hyperprop_not_isTwoSafety`; the last concerns the empty hyperproperty `fun _ => False`, not Clarkson & Schneider's hyperproperty `false = {∅}`), coinciding with Clarkson & Schneider (2010) 2-hypersafety under a discrete-observation reading plus `H ∅` (not formalized) and distinct from Terauchi & Aiken's (2005, Def. 4) program-set 2-safety with `⊥`.
4. Applies to complete big-step terminating I/O observations (`IOTrace Var`); does not model infinite execution traces or intermediate outputs.

**Result 7 — `tsni-hyperprop-not-subset-closed`.**

1. This result depends on encoding a command's behavior as its set of *terminating* pairs, so that a missing pair means divergence. Under this encoding, `S₁ ⊆ S₂` means `S₁` diverges on at least the inputs where `S₂` does, so removing pairs can create a termination channel. The witness involves no program or type system.
2. With divergence represented explicitly (outcomes in `Option (Store Var)`, as in Sabelfeld & Myers's ⊥-based formulation of termination-sensitive noninterference), termination-sensitive noninterference of a deterministic command is a pairwise condition on its total behavior. That hyperproperty satisfies `IsTwoSafety`, and hence `SubsetClosed`, in this package's sense (`Toy.IFC.tsni_iff_tsniOutHyperprop`, `Toy.IFC.tsniOutHyperprop_isTwoSafety`, `Toy.IFC.tsniOutHyperprop_subsetClosed`; id `tsni-out-hyperprop-is-two-safety`). So the failure here concerns the encoding, not TSNI as such.
3. Does not imply that TSNI cannot be established by two-run (relational, product-program, or self-composition) reasoning. In this deterministic language, TSNI is equivalent to TINI ∧ CoTerminates (`tsni_iff_tini_and_coterminates`). What resists safety-style checking in a trace model is that divergence is only infinitely observable: Clarkson & Schneider (2010, §7.2.1) show their relational TSNI is neither hypersafety nor hyperliveness, and Terauchi & Aiken (2005) call it '2-liveness'.
4. The positive control `tsniHyperprop_all_low_subsetClosed` covers only the case with no secret variables, where every noninterference notion is trivial. It is not evidence that a nontrivial policy escapes the result. For that, see the explicit-divergence encoding (`Toy.IFC.tsniOutHyperprop_isTwoSafety`, `Toy.IFC.tsniOutHyperprop_subsetClosed`, `Toy.IFC.tsni_iff_tsniOutHyperprop`, id `tsni-out-hyperprop-is-two-safety`).
5. Modeling-bridge remark (unformalized): this package's result concerns the terminating-pairs (missing-pair) encoding and does not refute Clarkson & Schneider's (2010, §7.2.1) `∀ t₁, t₂` relational TSNI (`TSRNI`) with explicit `s^ω` divergence, which fails hypersafety for a different reason (infinite observability of divergence; footnote 23 suggests "2-infinite-safety" in contrast to Terauchi & Aiken's "2-liveness").
6. Does not claim that `TSNI` is impossible to enforce statically; `TsTyped` enforces `TSNI` soundly for imperative programs (see `Toy.IFC.tsTyped_implies_tsni`).

**Result 8 — `ts-typed-implies-tsni`.**

1. Does not guarantee termination itself: `while 1 do skip` is accepted by `TsTyped Γ .low` (though rejected by `TsTyped Γ .high`, see `Toy.IFC.whileOne_tsTyped_low_not_high`) and diverges identically on all inputs.
2. Removing `pc = low` from the `while` rule (Result 9), removing the low-guard condition (a pc-only rule accepts `while h do skip`), or removing both (Result 3) each yields a system that accepts a TSNI-violating program. Each condition is thus shown necessary within this rule format (Results 9 and 11). Whether every type discipline that enforces `TSNI` must impose these conditions is not examined here (neither proved nor refuted). The terminating high-guarded loop `while h do h := 0` (with `h` high under `twoVarEnv`) satisfies `TSNI` yet is rejected by `TsTyped` at every `pc` (`Toy.IFC.whileHZero_tsni_not_tsTyped`), so `TsTyped` is sufficient for `TSNI` (this result) but not complete: it does not accept every command that satisfies `TSNI`.
3. All witnesses in the preceding non-claim are kernel-checked: `Toy.IFC.lowGuardWhileTyped_allows_termination_channel`, `Toy.IFC.pcLowWhileTyped_allows_termination_channel`, `Toy.IFC.cmdTyped_allows_termination_channel` (and `Toy.IFC.cmdTyped_violates_tsni_witness`), and `Toy.IFC.whileHZero_tsni_not_tsTyped`.
4. Timing is outside the model: `Eval` has no notion of execution steps or elapsed time, so the package neither proves nor formally refutes timing-channel freedom for `TsTyped` (or for any other system here). A stricter discipline that also forbids high guards on conditionals gives timing agreement in a step-counting semantics (Volpano & Smith 1997, §5, Theorem 5.3); the package neither states nor proves this.
5. Does not establish freedom from timing or step-count side channels. Illustration only (informal and unmodeled): `if h then (h := h + 1; h := h + 1) else skip` is accepted by `TsTyped twoVarEnv .low` (only this typing fact is kernel-checked, in `Toy.IFC.timingExample_tsTyped`), and under an informal step-counting reading its two branches execute different numbers of steps depending on `h`. Because `Eval` does not model step counts, this example is not a formal counterexample to any theorem here and does not formally refute timing-channel freedom; it only illustrates that the package's results say nothing about timing.
6. Does not cover partial expressions / runtime errors (Volpano & Smith 1997), intermediate public outputs, nondeterminism, or multi-threaded concurrency (Smith & Volpano 1998).

**Result 9 — `low-guard-while-typed-termination-channel-counterexample`.**

1. Does not show that requiring `pc = low` alone suffices. Keeping `pc = low` but dropping the low-guard condition also admits a termination channel (`while h do skip`).
2. The converse ablation noted above is kernel-checked in `Toy.IFC.pcLowWhileTyped_allows_termination_channel` (id `pc-low-while-typed-termination-channel-counterexample`).
3. Does not refute `TINI` for `LowGuardWhileTyped`: because `LowGuardWhileTyped Γ pc c → CmdTyped Γ pc c` (`Toy.IFC.lowGuardWhileTyped_implies_cmdTyped`), every `LowGuardWhileTyped` program still satisfies `TINI` (`Toy.IFC.cmdTyped_implies_tini`).
4. Does not claim that `LowGuardWhileTyped` allows high-guarded loops; `LowGuardWhileTyped` rejects `while h do skip` (`Toy.IFC.lowGuardWhileTyped_neg_while_h`), showing that high loop guards are not the sole source of termination leaks.
5. Does not rule out disciplines that permit provably terminating loops under a high `pc` (see `Toy.IFC.whileHZero_tsni_not_tsTyped`).

**Result 10 — `tsni-iff-tini-and-coterminates`.**

1. Depends critically on determinism of the big-step semantics (`Toy.IFC.eval_deterministic`). For a general nondeterministic input–output relation `R`, existential TSNI does not imply universal pairwise TINI (`Toy.IFC.nondet_existential_tsni_not_tini`).
2. Does not include execution time, step counts, or intermediate output traces in either `TINI` or `CoTerminates`.

**Result 11 — `pc-low-while-typed-termination-channel-counterexample`.**

1. Does not refute `TINI` for `PcLowWhileTyped`: because `PcLowWhileTyped Γ pc c → CmdTyped Γ pc c` (`Toy.IFC.pcLowWhileTyped_implies_cmdTyped`), every `PcLowWhileTyped` program still satisfies `TINI` (`Toy.IFC.cmdTyped_implies_tini`).
2. Does not claim `PcLowWhileTyped` allows loops nested inside high conditionals; `PcLowWhileTyped` rejects `if h then (while 1 do skip) else skip` at every `pc` (`Toy.IFC.pcLowWhileTyped_neg_high_if_low_while`).
3. Does not show that requiring `exprLevel Γ e = low` alone suffices (the converse ablation `Toy.IFC.lowGuardWhileTyped_allows_termination_channel` refutes that).
4. `exprLevel Γ e = low` is shown necessary within this rule format (this result); whether every type discipline that enforces `TSNI` must impose it is not examined here (neither proved nor refuted). The terminating high-guarded loop `while h do h := 0` (with `h` high under `twoVarEnv`) satisfies `TSNI` yet is rejected by `TsTyped` at every `pc` (`Toy.IFC.whileHZero_tsni_not_tsTyped`).

**Result 12 — `while-no-pc-typed-implicit-flow-counterexample`.**

1. Does not claim that `WhileNoPcTyped` drops `pc` tracking on conditionals; `WhileNoPcTyped` still rejects `if h then l := 1 else l := 0` at every `pc` (`Toy.IFC.whileNoPcTyped_neg_implicit_flow`).
2. Does not show that a program-counter label is the only sound control-dependence mechanism (for example, `Toy.IFC.NoHighGuardTyped` forbids high guards on both `if` and `while` without a `pc` label and embeds into `CmdTyped Γ .low`).
3. Does not claim that every program accepted by `WhileNoPcTyped` violates `TINI`.

**Result 13 — `tsni-out-hyperprop-is-two-safety`.**

1. Serves as the non-degenerate positive control and escape hatch for `tsni-hyperprop-not-subset-closed`: switching from terminating-pair behaviors (`IOTrace Var`) to explicit-outcome behaviors (`OutTrace Var`) defeats the non-subset-closure impossibility even in the presence of secret variables.
2. Does not imply that TSNI is hypersafety in Clarkson & Schneider's (2010, §7.2.1) prefix-based infinite-trace topology: because observing divergence (`none` / `s^ω`) requires infinite time, Clarkson & Schneider prove their relational TSNI (`TSRNI`) is neither hypersafety nor hyperliveness for `Rel` (and footnote 23 contrasts Terauchi & Aiken's 2005 §1 "2-liveness" with "2-infinite-safety"). This infinite-trace distinction is a modeling-bridge remark not formalized here.
3. `tsni_iff_tsniOutHyperprop` relies on determinism of `Eval` (`Toy.IFC.eval_deterministic`) and classical case analysis on `Terminates c σ₂`.
4. `tsniOutHyperprop_isTwoSafety` uses this package's complete-observation pairwise-determinedness predicate `IsTwoSafety` (`Toy.IFC.isTwoSafety_iff_csTwoSafety`, `Toy.IFC.isTwoSafety_holds_empty`, `Toy.IFC.false_hyperprop_not_isTwoSafety`), not Clarkson & Schneider's infinite-trace hypersafety (whose topology is the lower Vietoris construction applied to the Plotkin topology).

### Escape hatches

- **For Result 7 (`tsni-hyperprop-not-subset-closed`):** the impossibility holds because `IOTrace Var` records only terminating pairs (divergence = absent pair) and requires at least one secret variable (`Γ h = high`). It is defeated either by switching to explicit-outcome behaviors (`OutTrace Var`, `outcomeBehavior`, `tsniOutHyperprop`), which restores both `IsTwoSafety` and `SubsetClosed` while preserving equivalence with `TSNI` (`tsni_iff_tsniOutHyperprop`, `tsniOutHyperprop_isTwoSafety`, `tsniOutHyperprop_subsetClosed`, Result 13), or trivially in the degenerate policy where every variable is `low` (`tsniHyperprop_all_low_subsetClosed`, `tsniHyperprop_all_low_isTwoSafety`).
- **For the typing-ablation counterexamples (Results 2, 3, 9, 11, 12):** implicit-flow leaks in `NoPcTyped` and `WhileNoPcTyped` are closed by restoring full `pc` tracking (`CmdTyped`, Result 1; `implicitFlowProg_rejected_by_cmdTyped`, `whileLeakProg_rejected_by_cmdTyped`) or by a `pc`-free rule forbidding secret guards (`NoHighGuardTyped`, `noHighGuardTyped_implies_cmdTyped_low`, `noHighGuardTyped_neg_implicit_flow`). Termination leaks in `CmdTyped`, `LowGuardWhileTyped`, and `PcLowWhileTyped` are closed by enforcing both `pc = low` and `exprLevel Γ e = low` at `while` (`TsTyped`, Result 8; `termChannelProg_rejected_by_tsTyped`, `highIfLowWhileProg_rejected_by_tsTyped`), or alternatively (outside this syntactic rule family) by proving termination of high-guarded loops (`whileHZero_tsni_not_tsTyped`).

### Unformalized and unexamined boundaries

- **Timing and step-count channels (`not examined` / `not formalized`):** `Eval` does not record step counts or wall-clock duration. Even `TsTyped` accepts programs whose branches take different numbers of steps depending on `high` inputs (`timingExample_tsTyped`, where the step-count difference is an informal observation outside the model). For timing-sensitive formalizations, see Volpano & Smith (CSFW 1997, §5 Theorem 5.3), Nipkow & Klein (2014, §9.2.6), and Agat (POPL 2000).
- **Equivalence with declarative Volpano–Irvine–Smith phrase typing (`not examined`):** `CmdTyped` is Nipkow & Klein's syntax-directed `pc`-label system specialized to `{low, high}`; equivalence with Volpano, Irvine & Smith's (1996) command types `τ cmd`, contravariant subtyping, `letvar`, and arbitrary lattices is not formalized.
- **Infinite-trace prefix hyperproperty topology (`not examined`):** `IsTwoSafety` is complete-observation pairwise-determinedness (`CSTwoSafety`, forcing `H ∅`); Clarkson & Schneider's (2010) prefix-based topology for infinite execution traces is not formalized.
- **Unsupported language features (`unsupported`):** interactive intermediate outputs (progress-sensitive noninterference), partial operations or runtime exceptions, nondeterminism (`nondet_existential_tsni_not_tini`), multi-threaded concurrency, declassification, flow-sensitive variable labels, and multi-level lattices beyond `{low, high}`.

### Hypotheses of unknown tightness

None. Every hypothesis listed across all 13 result cards has status `tight` with a kernel-checked Lean counterexample demonstrating that the conclusion fails when that hypothesis is dropped while the remaining hypotheses hold, with one qualification. For the explicit-flow rows (Result 1's explicit-flow assignment bound, via `untyped_explicit_flow_violates_tini`, and the explicit-flow part of Result 8's base row, via `untyped_explicit_flow_violates_tsni`), the counterexamples kernel-check only that `l := h` is rejected by the full system at every `pc` and violates the noninterference property. That `l := h` satisfies the remaining components (`pc` tracking, and for Result 8 also both `while` conjuncts) holds by inspection (at `pc = low`, `pc ≤ Γ l` holds and the program contains no `if` or `while`) and is not kernel-checked. Results 6, 10, and 13 take no explicit hypotheses (Results 10 and 13 rely internally on `eval_deterministic`, and Result 13 uses classical case analysis on `Terminates`).

### Disproved or withdrawn statements

None. Every statement on the result cards is proved in Lean exactly as printed, and no statement considered for this package was disproved.

## Evidence

### Kernel-check record

- **Toolchain:** `leanprover/lean4:v4.34.1`, GitHub repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (verified via GitHub API and `lean --version`).
- **Build:** `lake build` of a fresh copy of `lean/` succeeds cleanly with zero warnings and zero `sorry` tokens.
- **Declaration sweep (`audit/axioms.json`):** 578 non-internal declarations of the `Toy` modules audited with `Lean.collectAxioms`; zero `axiom` or `opaque` declarations; zero `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, or `debug.skipKernelTC` in the sources. Axiom footprints across all 578 declarations: 472 use no axioms; 89 use `propext`; 8 use `Classical.choice`, `Quot.sound`, `propext`; 6 use `Quot.sound`, `propext`; 3 use `Quot.sound`.
- **Statement hashes (`audit/statements.json`):** 51 declarations referenced in `lean`, `nonvacuity_witness_lean`, `positive_control_lean`, and `hypotheses[*].counterexample` fields of `results.json`. `statement_sha256` is the SHA-256 of `toString (repr ci.type)`; `closure_sha256` is the SHA-256 of the newline-joined sorted entries `name : repr type [:= repr value]` for every package constant reachable from the statement's type (definition values included, theorem proofs excluded). Scope witnesses (`scope_witnesses_lean`) are not hashed unless they also appear in one of those fields; `support/revalidate.py` checks that they exist.
- **Revalidation script:** `support/revalidate.py` (8052 bytes, SHA-256 `8cbdc4bced1eb6aa3257b72ab54ffec3778a1c7988dfcaab1eb459488219b687`); run on 2026-11-20 with the output shown under Revalidation.
- **Observation date:** 2026-11-20 (build, axiom audit, statement hashing, GitHub API checks, and source checks).

### Axiom footprints of the main theorems

| Result | Theorem | Axioms |
|---|---|---|
| 1 | `cmdTyped_implies_tini` | `propext` |
| 2 | `noPcTyped_accepts_implicit_flow_violating_tini` | `propext` |
| 3 | `cmdTyped_allows_termination_channel` | `propext` |
| 4 | `cmdTyped_implies_tiniHyperprop` | `propext` |
| 5 | `isTwoSafety_implies_subsetClosed` | `propext` |
| 6 | `tiniHyperprop_isTwoSafety` | none |
| 6 | `tiniHyperprop_subsetClosed` | `propext` |
| 7 | `tsniHyperprop_termPairs_not_subsetClosed_of_high_var` | `propext` |
| 7 | `tsniHyperprop_termPairs_not_twoSafety_of_high_var` | `propext` |
| 8 | `tsTyped_implies_tsni` | `propext` |
| 9 | `lowGuardWhileTyped_allows_termination_channel` | `propext` |
| 10 | `tsni_iff_tini_and_coterminates` | none |
| 11 | `pcLowWhileTyped_allows_termination_channel` | `propext` |
| 12 | `whileNoPcTyped_accepts_leak_violating_tini` | `propext` |
| 13 | `tsni_iff_tsniOutHyperprop` | `Classical.choice`, `Quot.sound`, `propext` |
| 13 | `tsniOutHyperprop_isTwoSafety` | `propext` |
| 13 | `tsniOutHyperprop_subsetClosed` | `propext` |

### Hashed declarations

| Declaration | Card role (result, role) | Axioms | Closure size | `statement_sha256` | `closure_sha256` |
|---|---|---|---:|---|---|
| `cmdTyped_allows_termination_channel` | 3 main | `propext` | 55 | `ab864e1bbb4c51eec1d7e622a7465dc39aca79d932331908ea7dc8f67bac18fb` | `b0f8640ed525cf9fcd09f251746fb59f2039a1204300e287231b7c084adae4d5` |
| `cmdTyped_implies_tini` | 1 main | `propext` | 52 | `99b051726124982918b517ef3f5d79508e309d6da56305d529e98577aebaa372` | `23795dc6e3c3fe4719ae8032888a276e5e99beedb02f4f612ed5cfe8f15eb078` |
| `cmdTyped_implies_tiniHyperprop` | 4 main | `propext` | 57 | `74d21c4486dd7b27571dd61648ec4a92e4ce67f543e54344d1ff1318c411048a` | `73130490fc1d83f594a9c2bf7a9560049d64ce5dd52a00a2b1fb917a7fa9c1cc` |
| `cmdTyped_implies_tini_nonvacuous` | 1 non-vacuity; 4 non-vacuity | `Quot.sound`, `propext` | 67 | `0a9e3349dfbf0cc56316b0a370ab7e5026d50a528a0c1fd1742171dfaec0dbca` | `543699db7a395e47d7883239e258c0abea84e0a9f0d6365cc9f9f8cadf052803` |
| `cmdTyped_implies_tini_nonvacuous_highLoop` | 1 non-vacuity; 4 non-vacuity | `Quot.sound`, `propext` | 66 | `c0055f3c7bd4c244f480c6b7ecfaae0d30eb8d0e0f5c49a61cc88279a8443606` | `cce78c7d801940100d2e1d484ba748c047a54746c54e53b1ed501c82fbee7c76` |
| `highIfLowWhileProg_low_guard_satisfies_tsni` | 9 tightness | `propext` | 66 | `701a7afe00f45fe2fb4ad9f81c9303378475c0d208a2a193f7527031d64c642c` | `2bb9f4275b5a72fa515b7e70b0996dda01ae5d03591379140d605f991ef3084f` |
| `highIfLowWhileProg_rejected_by_tsTyped` | 9 positive control | `propext` | 39 | `1e8dfc3f075819eabc85bea1dc737da8d207a600c1cf191d1b6ab1f82c32276b` | `7ca46938db05147492f1a7932a6d0362aced63d4bb9ce070fba7a08dd1c09f46` |
| `high_var_nonvacuous` | 3 non-vacuity; 7 non-vacuity; 9 non-vacuity; 11 non-vacuity | none | 10 | `73aa88646daa388fff68703f45040d819dea2901988c36c4273647f12d037531` | `abb71ffa4fdd1f8e1c7587281d23bd9906ed1f036c2c0b4a31919adb0b2ca0f0` |
| `implicitFlowProg_guard_low_satisfies_tini` | 2 tightness | `propext` | 65 | `c8377af7174c4a0f0b849e2042f3ebd79369f5cb2fec3decc84d91d4ecb93835` | `d79b8f080943f7fa141684750082ce4235ec64cf32a92d6f3b4f53ce71a01057` |
| `implicitFlowProg_rejected_by_cmdTyped` | 2 positive control | none | 39 | `5713445f5a80cb38f23583bcb1292ffcf121053af7ae8ae78e141ddb95e0402e` | `de47a4042aea3620c32541c9f7f2416e9e487d39e44819d8734b49acea3854fb` |
| `implicitFlowProg_target_high_satisfies_tini` | 2 tightness | `propext` | 65 | `780a3b98cac616c4f54fc5aea8e727fb2535127468c113803e1eb7304e53d147` | `e23ee8279c587b048d65c55196677f1574939e042a1d751e4adb0e1e2cf0d3c4` |
| `isTwoSafety_implies_subsetClosed` | 5 main | `propext` | 4 | `f9bc6b4399e379def6069053b93e8f2d590a256fa9bf04c1fb7474fd769e4ab7` | `3e4f6b37b2769df57a8801ee7cecf1a958d5d0551811e431fbadd26bc8049099` |
| `isTwoSafety_implies_subsetClosed_nonvacuous` | 5 non-vacuity | none | 18 | `17bda079623d38012aba0ab15c81e2accecb7cee406ced6410f3a9cccb7c42e9` | `7a5ebb6654048ff21251bb40a45c2b4e2b7ad190483c6091349386830caa2f4b` |
| `lowGuardWhileTyped_allows_termination_channel` | 8 tightness; 9 main | `propext` | 55 | `c840e62abd61a40b8034dbc7df2630eac28b7af37d20fab3a497642eefc359f0` | `3667f014d70c3b6c7571fae1feed1ff41be228f07b61eedf104b6a27093e76ae` |
| `lowGuardWhileTyped_violates_tsni_witness` | 8 tightness | `propext` | 70 | `3168877194974feb139092571439acd0a0ec4207a6f5617363e0afffbf9760c2` | `2ba3c3dc4f47b724b9b2ff83ef37a6b64761f6c164394c20f06a97c9efc185f6` |
| `noHighGuardTyped_implies_cmdTyped_low` | 2 positive control | none | 44 | `0046112b43091f0cd62fc15befc7ba2b12ee632853431c20d24a1db05edd2640` | `cf192b9a846b5c8ae57417bdf0520754ddb0763a54591177ab8a812d639be774` |
| `noHighGuardTyped_neg_implicit_flow` | 2 positive control | `propext` | 46 | `72d4bf67858fd20f0e6458484078e1198756ec542a1ee0efb3916e60c83d95ed` | `29f621c67a38ddfd1c51903767edca6b90c826b5bc67afca3a27adac278d398c` |
| `noPcTyped_accepts_implicit_flow_violating_tini` | 2 main | `propext` | 53 | `e07a04de80cf7eac53141ce190d0ef7759d26f0d63fed40cfa151d89e6e6c1a2` | `601e646fc8fa33b49a076bd05079d77699ed46f8619fb45d0b0ffccf6d634eac` |
| `noPcTyped_implicit_flow_nonvacuous` | 2 non-vacuity; 12 non-vacuity | none | 10 | `fa9f0552af49c83aaf5f067878291b905e708b9d4373a380e6b4ae3e3367aa04` | `abb71ffa4fdd1f8e1c7587281d23bd9906ed1f036c2c0b4a31919adb0b2ca0f0` |
| `noPcTyped_implicit_flow_violates_tsni_witness` | 8 tightness | `propext` | 70 | `64eeb1504e3c5aad9ec7a5fcd5188dee4684662ba1bfabbffe2e0cc654688f3f` | `73ae0851cc8ca9d907de51301a83f580fd47c4a7cbd4d6c95ce6c2473ecf0857` |
| `noPcTyped_violates_tini_witness` | 1 tightness | `propext` | 70 | `37de0d50e7e8698db0b4b9738ad5a47eca52dbce9e4246df6a681dd59d8b7005` | `4e0af8af0d824cb29d908f974d7c8ff5bd68064f650e5cf50771c423cf0825c4` |
| `nonEmptyTraceSet_not_subsetClosed` | 5 tightness | `propext` | 5 | `8b900ae3028011db8354e92bcfb50ef06c1542d4c039f7063c57d1636f4312ad` | `1fc5caba09c99fb2182dd30a1acb9a47ef34df67266b7f6035c35c26cec73a90` |
| `pcLowWhileTyped_allows_termination_channel` | 8 tightness; 11 main | `propext` | 55 | `1949358a1f67b6a9a5892c039806a80c579eaa4ab454017cb92b18c3bf99c352` | `ef52e9b353ab4b4ae4c6d423a735c2e7e2c535ecea37c14a7de2c224ec15dca8` |
| `pcLowWhileTyped_violates_tsni_witness` | 8 tightness | `propext` | 70 | `8221717c4fbeb167f99c031cca82e5e0285860e5e6d7531cffd512563ef2d92d` | `43f08eaa48a28b8c7a3665e974205f20a2a5a0563b746c101915609ee2a74ca0` |
| `termChannelProg_low_guard_satisfies_tsni` | 3 tightness | none | 66 | `d44821efc96494eed0635f1502b8f744085a945ed1ca837a21a1fc75126effd3` | `2c1461a3e310d90282d85da37e8b58c807eda803fc09457abcdf94a72f04d372` |
| `termChannelProg_low_guard_satisfies_tsni_pcLow` | 11 tightness | none | 66 | `89f535d6fa0127fe233dd3f7a2afe8d74afb98d50cf50f6f77af0e15ccdf56fc` | `441586a330f0443ec190eab069289940dbfaea15ba99d62a09bd023339472274` |
| `termChannelProg_rejected_by_tsTyped` | 3 positive control; 11 positive control | `propext` | 39 | `7690e22e9b8eef8c28c5b6c698b3f3f5d710fdb285acf2364b84f14f5283db6e` | `aef56bfa30c6c1b74b50d96a9fe6c50433cdd96e2ff64a9cc82cb2dc6b99c805` |
| `tiniHyperprop_isTwoSafety` | 6 main | none | 11 | `556f23f9db7392e31efb9b2a7ff4fb6626229a278b82d95b8d464217bcdcb675` | `860991441654b839c0859bf7e5e53d826676e1644a5f3267aad2a0f8563b230a` |
| `tiniHyperprop_isTwoSafety_nonvacuous` | 6 non-vacuity | `propext` | 54 | `168c80116cf8d8b693bbd008af2638184a81e29ca684380b490f83ae3a2b070a` | `aca7044b7e14c7a124751ff687ad40302bf7a55b719cce61c32cb2f77666192a` |
| `tiniHyperprop_subsetClosed` | 6 main | `propext` | 11 | `4f790311b5de0b3060d183bae77753bae114787993fceced59e205118e412427` | `5777a1f408943ba4a111bfb24c5910feb2622f631e2123f2b8d6327756c232ca` |
| `tsTyped_implies_tsni` | 8 main | `propext` | 52 | `8d89397d49893e6793a4a703edfb505694e30b889822cbd2bc9a0fbae6eb8612` | `4d232a4e1698ccc29e0a3c2c52f728c650c00af59f17ada7ddcbfca394f5817e` |
| `tsTyped_implies_tsni_nonvacuous` | 8 non-vacuity | `Quot.sound`, `propext` | 66 | `1dfcec76e871e2950f54841d6fdccda076cba1acb434b8b34390dae72d4ede6c` | `f4fcb96a3dd919e1214fc293d027b7d4ce070a10720e8688947bdd8185efbc4e` |
| `tsniHyperprop_all_low_isTwoSafety_witness` | 7 tightness | `Quot.sound` | 14 | `aebc784bee23d5eba3277ca3bb00b40f14da62d235f233a9a1a2cddec0bc8b36` | `4f8c38faa831073b62ae5b1818abac83221392828be02b73b665bd87dd45f440` |
| `tsniHyperprop_all_low_subsetClosed` | 7 positive control | `Quot.sound`, `propext` | 10 | `a8c0f9c633f6179bf1f598ecf693846692d3911a554344160932364918ee3f8b` | `49b4cb36597fe17e434970b624eec135ea7b49a3534d557f577eb7cc0d197c1c` |
| `tsniHyperprop_all_low_subsetClosed_witness` | 7 tightness | `Quot.sound`, `propext` | 14 | `e51c8a544edba398f0c008baf67b3283e4370baeb41df7fdd42a95d30d6928de` | `d610e0edab74870ff2d6c49ac4a844e81ad5de3ff9f89f2e95d1812de8dd3145` |
| `tsniHyperprop_termPairs_not_subsetClosed_of_high_var` | 7 main | `propext` | 10 | `39a1f2138399279a000d11bca5dbb49c5eac59ba1e47f23200c36fa5fe2a0680` | `49b4cb36597fe17e434970b624eec135ea7b49a3534d557f577eb7cc0d197c1c` |
| `tsniHyperprop_termPairs_not_twoSafety_of_high_var` | 7 main | `propext` | 10 | `76dd3ee4718caa10fc617e05ca52384ec25e0c152efc21c7b26753a8221ffc82` | `b247f0d578fcf490317a0d59fd92d25f482a05b1b246443f2edc83e95b800c32` |
| `tsniOutHyperprop_isTwoSafety` | 7 positive control; 13 main | `propext` | 14 | `0cf14217640e48a8472880fb29b809387841435650f3e1407ed79ab42750b236` | `bf67e8050adec3562434b81a1675b6bdbd963e2e91d13e352c93615001f9e18f` |
| `tsniOutHyperprop_nonvacuous` | 13 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | 59 | `3159a2a9a59a40aa829df8d2ef70b3858082e2d5273fc026991da458a002f5c7` | `fc3810c4201e36b28b67e80e2ab39c4f97f5306f67659e72f14ee9f96ce87477` |
| `tsniOutHyperprop_subsetClosed` | 7 positive control; 13 main | `propext` | 14 | `b599099fd9d7563cd8e2ea8df76dc871f4944a109bec7c3d6beaf04fc3e45648` | `d809c18b99b859e45b5b4f10d914c7ff99d677987e08285c0295984fc4da2fac` |
| `tsni_char_nonvacuous` | 10 non-vacuity | `propext` | 53 | `88e8e7ecb344c418098fd7e7379d84ab84efb715173c7d3a0cf0733c07f99d55` | `bc55033d8e624d8f0aba3ea5f995a9c03474328066bf8ea7943ecaf9af9c5506` |
| `tsni_iff_tini_and_coterminates` | 10 main | none | 40 | `d02f9698e6708c9b9461572fa298229cb86c8050d75c51e13a16b94c0f38da8d` | `d68d5ce06adb9a66a66ec4eb4631f51906612b63736b15ce76bb88ed463d5f95` |
| `tsni_iff_tsniOutHyperprop` | 7 positive control; 13 main | `Classical.choice`, `Quot.sound`, `propext` | 48 | `5ef2faef5f061bf34844ff91aff98f57c18ce3b5943dd356329cc176caaa097d` | `9217237e8947c5f10c8b4dfda1ffb99a2a570b276e2698a4ea700e588d2696ae` |
| `untyped_explicit_flow_violates_tini` | 1 tightness | `propext` | 64 | `70e83b978e3444207b644cc565a4544b1a06d748a113d87febb65d856c065fba` | `6a50328ab9ca426de6070ba3fdba9f8264205876f7d5902ea799b175ecab18a4` |
| `untyped_explicit_flow_violates_tiniHyperprop` | 4 tightness | `propext` | 69 | `dee28c24cb086f3a3dda785ff7fc8415516b434b37381258bdc2789aee60607c` | `26c68514ba4a4f432ec139357658ba7f100e34a910593f6fdcc2a71027a405da` |
| `untyped_explicit_flow_violates_tsni` | 8 tightness | `propext` | 70 | `0c4ba3e76252e09c37f9f030a4df545bae9851a65aba4cc93b7f36058ed51d42` | `37bfd0e6f1ae892209a6e03201a39e2986cde75c2a01973d60689816e1050591` |
| `whileLeakProg_guard_low_satisfies_tini` | 12 tightness | `propext` | 65 | `d3da5301ab0a252821a78e7be08436aec310afd6315c5f47d9c3278b4e98f322` | `31fe30e3e1d896c11b61db2f6d2d62875fdf29cfa8c2a4c1b579fb22f7b57724` |
| `whileLeakProg_rejected_by_cmdTyped` | 12 positive control | none | 39 | `ff213e9d37552e9a684b8ecb543d6bcbafd0c7c6966ee9c34562cc7201b7c284` | `afaa45f400722dc0d001e1114af17c6ca58b288885ba627e921dbc30712617e9` |
| `whileLeakProg_target_high_satisfies_tini` | 12 tightness | `propext` | 65 | `3fe9c5a0f417aaa8cd23fc43b8161550ea5890a8a65a821a7a09e6e89230f486` | `2cbf0e3168bf25f430095fd5b2a610f8c89cd086a792b4b99297c8da4d990598` |
| `whileNoPcTyped_accepts_leak_violating_tini` | 12 main | `propext` | 53 | `ce82d932cae4a9c70214cf4998bcb685bbceeba169b072bd810488270662c916` | `d3bd1684f203e0169c644058519f2d7dfc2e10227af0003e71bdce274bd6fc96` |
| `whileNoPcTyped_violates_tini_witness` | 1 tightness | `propext` | 70 | `cfaae516a47b64771738bf4cbb827181c1a514340cabde4421b3e3768bad42fa` | `4d4169d2cb3a4c36a4268d5b70936028446e9cede30afdd894712dfb5858856d` |

### Statements of all card-hashed declarations, as printed by Lean

Output of `#check @name` (with `open Toy.IFC`) on the built library, unedited, for all 51 declarations hashed in `audit/statements.json`. The entry for `nonEmptyTraceSet_not_subsetClosed` is printed with `set_option pp.analyze true`, which shows the instantiation `(α := Unit)` that the default output omits.

```lean
@cmdTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var},
  Γ h = Level.high →
    CmdTyped Γ pc (termChannelProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (termChannelProg h) zeroStore ∧
          ¬Terminates (termChannelProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (termChannelProg h)
@cmdTyped_implies_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → TINI Γ c
@cmdTyped_implies_tiniHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → tiniHyperprop Γ (ioBehavior c)
cmdTyped_implies_tini_nonvacuous : CmdTyped twoVarEnv Level.low sampleTypedProg ∧
  LowEq twoVarEnv storeZero storeHighOne ∧
    Eval sampleTypedProg storeZero storeLowOne ∧
      Eval sampleTypedProg storeHighOne ((storeHighOne.update TwoVar.h 2).update TwoVar.l 1)
cmdTyped_implies_tini_nonvacuous_highLoop : CmdTyped twoVarEnv Level.low whileHZero ∧
  LowEq twoVarEnv storeZero storeHighOne ∧ Eval whileHZero storeZero storeZero ∧ Eval whileHZero storeHighOne storeZero
highIfLowWhileProg_low_guard_satisfies_tsni : twoVarEnv TwoVar.l = Level.low ∧
  TSNI twoVarEnv (highIfLowWhileProg TwoVar.l) ∧
    ¬(LowGuardWhileTyped twoVarEnv Level.low (highIfLowWhileProg TwoVar.l) ∧
        LowEq twoVarEnv zeroStore (zeroStore.update TwoVar.l 1) ∧
          Terminates (highIfLowWhileProg TwoVar.l) zeroStore ∧
            ¬Terminates (highIfLowWhileProg TwoVar.l) (zeroStore.update TwoVar.l 1) ∧
              ¬TSNI twoVarEnv (highIfLowWhileProg TwoVar.l))
@highIfLowWhileProg_rejected_by_tsTyped : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ∀ (pc : Level), ¬TsTyped Γ pc (highIfLowWhileProg h)
high_var_nonvacuous : twoVarEnv TwoVar.h = Level.high
implicitFlowProg_guard_low_satisfies_tini : mixedLowEnv ThreeVar.l = Level.low ∧
  TINI mixedLowEnv (implicitFlowProg ThreeVar.l ThreeVar.m) ∧
    ¬(NoPcTyped mixedLowEnv (implicitFlowProg ThreeVar.l ThreeVar.m) ∧
        ¬TINI mixedLowEnv (implicitFlowProg ThreeVar.l ThreeVar.m))
@implicitFlowProg_rejected_by_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → ∀ (pc : Level), ¬CmdTyped Γ pc (implicitFlowProg l h)
implicitFlowProg_target_high_satisfies_tini : mixedHighEnv ThreeVar.h = Level.high ∧
  TINI mixedHighEnv (implicitFlowProg ThreeVar.m ThreeVar.h) ∧
    ¬(NoPcTyped mixedHighEnv (implicitFlowProg ThreeVar.m ThreeVar.h) ∧
        ¬TINI mixedHighEnv (implicitFlowProg ThreeVar.m ThreeVar.h))
@isTwoSafety_implies_subsetClosed : ∀ {α : Type} {H : Hyperproperty α}, IsTwoSafety H → SubsetClosed H
isTwoSafety_implies_subsetClosed_nonvacuous : IsTwoSafety (tiniHyperprop twoVarEnv)
@lowGuardWhileTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level}
  {h : Var},
  Γ h = Level.high →
    LowGuardWhileTyped Γ pc (highIfLowWhileProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (highIfLowWhileProg h) zeroStore ∧
          ¬Terminates (highIfLowWhileProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (highIfLowWhileProg h)
lowGuardWhileTyped_violates_tsni_witness : LowGuardWhileTyped twoVarEnv Level.low (highIfLowWhileProg TwoVar.h) ∧
  (∀ (pc : Level), ¬TsTyped twoVarEnv pc (highIfLowWhileProg TwoVar.h)) ∧ ¬TSNI twoVarEnv (highIfLowWhileProg TwoVar.h)
@noHighGuardTyped_implies_cmdTyped_low : ∀ {Var : Type} {Γ : Var → Level} {c : Cmd Var},
  NoHighGuardTyped Γ c → CmdTyped Γ Level.low c
noHighGuardTyped_neg_implicit_flow : ¬NoHighGuardTyped twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h)
@noPcTyped_accepts_implicit_flow_violating_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → NoPcTyped Γ (implicitFlowProg l h) ∧ ¬TINI Γ (implicitFlowProg l h)
noPcTyped_implicit_flow_nonvacuous : twoVarEnv TwoVar.l = Level.low ∧ twoVarEnv TwoVar.h = Level.high
noPcTyped_implicit_flow_violates_tsni_witness : NoPcTyped twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h) ∧
  (∀ (pc : Level), ¬TsTyped twoVarEnv pc (implicitFlowProg TwoVar.l TwoVar.h)) ∧
    ¬TSNI twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h)
noPcTyped_violates_tini_witness : NoPcTyped twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h) ∧
  (∀ (pc : Level), ¬CmdTyped twoVarEnv pc (implicitFlowProg TwoVar.l TwoVar.h)) ∧
    ¬TINI twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h)
nonEmptyTraceSet_not_subsetClosed : ¬IsTwoSafety (α := Unit) nonEmptyTraceSet ∧
  ¬SubsetClosed (α := Unit) nonEmptyTraceSet
@pcLowWhileTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {h : Var},
  Γ h = Level.high →
    PcLowWhileTyped Γ Level.low (termChannelProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (termChannelProg h) zeroStore ∧
          ¬Terminates (termChannelProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (termChannelProg h)
pcLowWhileTyped_violates_tsni_witness : PcLowWhileTyped twoVarEnv Level.low (termChannelProg TwoVar.h) ∧
  (∀ (pc : Level), ¬TsTyped twoVarEnv pc (termChannelProg TwoVar.h)) ∧ ¬TSNI twoVarEnv (termChannelProg TwoVar.h)
termChannelProg_low_guard_satisfies_tsni : twoVarEnv TwoVar.l = Level.low ∧
  TSNI twoVarEnv (termChannelProg TwoVar.l) ∧
    ¬(CmdTyped twoVarEnv Level.low (termChannelProg TwoVar.l) ∧
        LowEq twoVarEnv zeroStore (zeroStore.update TwoVar.l 1) ∧
          Terminates (termChannelProg TwoVar.l) zeroStore ∧
            ¬Terminates (termChannelProg TwoVar.l) (zeroStore.update TwoVar.l 1) ∧
              ¬TSNI twoVarEnv (termChannelProg TwoVar.l))
termChannelProg_low_guard_satisfies_tsni_pcLow : twoVarEnv TwoVar.l = Level.low ∧
  TSNI twoVarEnv (termChannelProg TwoVar.l) ∧
    ¬(PcLowWhileTyped twoVarEnv Level.low (termChannelProg TwoVar.l) ∧
        LowEq twoVarEnv zeroStore (zeroStore.update TwoVar.l 1) ∧
          Terminates (termChannelProg TwoVar.l) zeroStore ∧
            ¬Terminates (termChannelProg TwoVar.l) (zeroStore.update TwoVar.l 1) ∧
              ¬TSNI twoVarEnv (termChannelProg TwoVar.l))
@termChannelProg_rejected_by_tsTyped : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ∀ (pc : Level), ¬TsTyped Γ pc (termChannelProg h)
@tiniHyperprop_isTwoSafety : ∀ {Var : Type} (Γ : Var → Level), IsTwoSafety (tiniHyperprop Γ)
tiniHyperprop_isTwoSafety_nonvacuous : tiniHyperprop twoVarEnv (ioBehavior Cmd.skip) ∧
  ¬tiniHyperprop twoVarEnv (ioBehavior (explicitFlowProg TwoVar.l TwoVar.h))
@tiniHyperprop_subsetClosed : ∀ {Var : Type} (Γ : Var → Level), SubsetClosed (tiniHyperprop Γ)
@tsTyped_implies_tsni : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → TSNI Γ c
tsTyped_implies_tsni_nonvacuous : TsTyped twoVarEnv Level.low sampleTsProg ∧
  LowEq twoVarEnv storeLowOne (storeLowOne.update TwoVar.h 5) ∧
    Eval sampleTsProg storeLowOne storeZero ∧
      Eval sampleTsProg (storeLowOne.update TwoVar.h 5) (storeZero.update TwoVar.h 4)
tsniHyperprop_all_low_isTwoSafety_witness : IsTwoSafety (tsniHyperprop allLowEnv)
@tsniHyperprop_all_low_subsetClosed : ∀ {Var : Type} {Γ : Var → Level},
  (∀ (x : Var), Γ x = Level.low) → SubsetClosed (tsniHyperprop Γ)
tsniHyperprop_all_low_subsetClosed_witness : SubsetClosed (tsniHyperprop allLowEnv)
@tsniHyperprop_termPairs_not_subsetClosed_of_high_var : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ¬SubsetClosed (tsniHyperprop Γ)
@tsniHyperprop_termPairs_not_twoSafety_of_high_var : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ¬IsTwoSafety (tsniHyperprop Γ)
@tsniOutHyperprop_isTwoSafety : ∀ {Var : Type} (Γ : Var → Level), IsTwoSafety (tsniOutHyperprop Γ)
tsniOutHyperprop_nonvacuous : tsniOutHyperprop twoVarEnv (outcomeBehavior Cmd.skip) ∧
  ¬tsniOutHyperprop twoVarEnv (outcomeBehavior (termChannelProg TwoVar.h))
@tsniOutHyperprop_subsetClosed : ∀ {Var : Type} (Γ : Var → Level), SubsetClosed (tsniOutHyperprop Γ)
tsni_char_nonvacuous : TSNI twoVarEnv (Cmd.assign TwoVar.l ((Expr.var TwoVar.l).add (Expr.lit 1))) ∧
  (TINI twoVarEnv (termChannelProg TwoVar.h) ∧ ¬CoTerminates twoVarEnv (termChannelProg TwoVar.h)) ∧
    CoTerminates twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h) ∧ ¬TINI twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
@tsni_iff_tini_and_coterminates : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ TINI Γ c ∧ CoTerminates Γ c
@tsni_iff_tsniOutHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ tsniOutHyperprop Γ (outcomeBehavior c)
untyped_explicit_flow_violates_tini : (∀ (pc : Level), ¬CmdTyped twoVarEnv pc (explicitFlowProg TwoVar.l TwoVar.h)) ∧
  ¬TINI twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
untyped_explicit_flow_violates_tiniHyperprop : (∀ (pc : Level),
    ¬CmdTyped twoVarEnv pc (explicitFlowProg TwoVar.l TwoVar.h)) ∧
  ¬tiniHyperprop twoVarEnv (ioBehavior (explicitFlowProg TwoVar.l TwoVar.h))
untyped_explicit_flow_violates_tsni : (∀ (pc : Level), ¬TsTyped twoVarEnv pc (explicitFlowProg TwoVar.l TwoVar.h)) ∧
  (∀ (pc : Level), ¬CmdTyped twoVarEnv pc (explicitFlowProg TwoVar.l TwoVar.h)) ∧
    ¬TSNI twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
whileLeakProg_guard_low_satisfies_tini : mixedLowEnv ThreeVar.l = Level.low ∧
  TINI mixedLowEnv (whileLeakProg ThreeVar.l ThreeVar.m) ∧
    ¬(WhileNoPcTyped mixedLowEnv Level.low (whileLeakProg ThreeVar.l ThreeVar.m) ∧
        ¬TINI mixedLowEnv (whileLeakProg ThreeVar.l ThreeVar.m))
@whileLeakProg_rejected_by_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → ∀ (pc : Level), ¬CmdTyped Γ pc (whileLeakProg l h)
whileLeakProg_target_high_satisfies_tini : mixedHighEnv ThreeVar.h = Level.high ∧
  TINI mixedHighEnv (whileLeakProg ThreeVar.m ThreeVar.h) ∧
    ¬(WhileNoPcTyped mixedHighEnv Level.low (whileLeakProg ThreeVar.m ThreeVar.h) ∧
        ¬TINI mixedHighEnv (whileLeakProg ThreeVar.m ThreeVar.h))
@whileNoPcTyped_accepts_leak_violating_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → WhileNoPcTyped Γ Level.low (whileLeakProg l h) ∧ ¬TINI Γ (whileLeakProg l h)
whileNoPcTyped_violates_tini_witness : WhileNoPcTyped twoVarEnv Level.low (whileLeakProg TwoVar.l TwoVar.h) ∧
  (∀ (pc : Level), ¬CmdTyped twoVarEnv pc (whileLeakProg TwoVar.l TwoVar.h)) ∧
    ¬TINI twoVarEnv (whileLeakProg TwoVar.l TwoVar.h)
```

### Scope witnesses (`scope_witnesses_lean`)

Each result's `scope_witnesses_lean` field in `results.json` lists every package theorem named in that result's non-claims; definitions named there are printed under Core definitions. There are 37 distinct scope witnesses. 15 of them are also among the 51 hashed declarations (`cmdTyped_allows_termination_channel`, `noHighGuardTyped_implies_cmdTyped_low`, `noHighGuardTyped_neg_implicit_flow`, `whileNoPcTyped_accepts_leak_violating_tini`, `tsni_char_nonvacuous`, `lowGuardWhileTyped_allows_termination_channel`, `pcLowWhileTyped_allows_termination_channel`, `cmdTyped_implies_tini`, `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`, `tsni_iff_tsniOutHyperprop`, `tsniOutHyperprop_isTwoSafety`, `tsniOutHyperprop_subsetClosed`, `tsni_iff_tini_and_coterminates`, `tsniHyperprop_all_low_subsetClosed`, `tsTyped_implies_tsni`); the other 22 carry no statement hash. `support/revalidate.py` checks that every scope witness exists in the built library and checks the recorded hashes of the hashed ones; for the unhashed ones, compare the statements below with fresh `#check` output.

| Result | `scope_witnesses_lean` |
|---|---|
| 1 `cmd-typed-implies-tini` | `cmdTyped_allows_termination_channel`, `probeProg_cmdTyped`, `probeProg_termination_profile_determines_secret`, `subSelf_tini_not_cmdTyped`, `constBranch_tini_not_cmdTyped` |
| 2 `no-pc-typed-implicit-flow-counterexample` | `noHighGuardTyped_implies_cmdTyped_low`, `noHighGuardTyped_neg_implicit_flow`, `constBranch_tini_not_cmdTyped`, `noPcTyped_neg_explicit_flow`, `whileNoPcTyped_accepts_leak_violating_tini` |
| 3 `cmd-typed-termination-channel-counterexample` | `tsni_char_nonvacuous`, `probeProg_cmdTyped`, `probeProg_termination_profile_determines_secret`, `lowGuardWhileTyped_allows_termination_channel`, `pcLowWhileTyped_allows_termination_channel` |
| 4 `cmd-typed-implies-tini-hyperprop` | `cmdTyped_implies_tini`, `tini_iff_tiniHyperprop` |
| 5 `two-safety-implies-subset-closed` | `atMostTwoTraces_subsetClosed_not_twoSafety`, `isTwoSafety_iff_csTwoSafety`, `isTwoSafety_holds_empty`, `false_hyperprop_not_isTwoSafety` |
| 6 `tini-hyperprop-is-two-safety` | `tiniHyperprop_not_oneSafety`, `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`, `isTwoSafety_iff_csTwoSafety`, `isTwoSafety_holds_empty`, `false_hyperprop_not_isTwoSafety` |
| 7 `tsni-hyperprop-not-subset-closed` | `tsni_iff_tsniOutHyperprop`, `tsniOutHyperprop_isTwoSafety`, `tsniOutHyperprop_subsetClosed`, `tsni_iff_tini_and_coterminates`, `tsniHyperprop_all_low_subsetClosed`, `tsTyped_implies_tsni` |
| 8 `ts-typed-implies-tsni` | `whileOne_tsTyped_low_not_high`, `lowGuardWhileTyped_allows_termination_channel`, `pcLowWhileTyped_allows_termination_channel`, `cmdTyped_allows_termination_channel`, `cmdTyped_violates_tsni_witness`, `whileHZero_tsni_not_tsTyped`, `timingExample_tsTyped` |
| 9 `low-guard-while-typed-termination-channel-counterexample` | `pcLowWhileTyped_allows_termination_channel`, `lowGuardWhileTyped_implies_cmdTyped`, `cmdTyped_implies_tini`, `lowGuardWhileTyped_neg_while_h`, `whileHZero_tsni_not_tsTyped` |
| 10 `tsni-iff-tini-and-coterminates` | `eval_deterministic`, `nondet_existential_tsni_not_tini` |
| 11 `pc-low-while-typed-termination-channel-counterexample` | `pcLowWhileTyped_implies_cmdTyped`, `cmdTyped_implies_tini`, `pcLowWhileTyped_neg_high_if_low_while`, `lowGuardWhileTyped_allows_termination_channel`, `whileHZero_tsni_not_tsTyped` |
| 12 `while-no-pc-typed-implicit-flow-counterexample` | `whileNoPcTyped_neg_implicit_flow` |
| 13 `tsni-out-hyperprop-is-two-safety` | `tsni_iff_tsniOutHyperprop`, `eval_deterministic`, `tsniOutHyperprop_isTwoSafety`, `isTwoSafety_iff_csTwoSafety`, `isTwoSafety_holds_empty`, `false_hyperprop_not_isTwoSafety` |

Output of `#check @name` (with `open Toy.IFC`) on the built library for all 37 scope witnesses, sorted by name, unedited, except that the entries for `atMostTwoTraces_subsetClosed_not_twoSafety` and `false_hyperprop_not_isTwoSafety` are printed with `set_option pp.analyze true`, which shows the instantiations `(α := Fin 3)` and `(α := Unit)` that the default output omits:

```lean
atMostTwoTraces_subsetClosed_not_twoSafety : SubsetClosed (α := Fin 3) atMostTwoTraces ∧
  ¬IsTwoSafety (α := Fin 3) atMostTwoTraces
@cmdTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var},
  Γ h = Level.high →
    CmdTyped Γ pc (termChannelProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (termChannelProg h) zeroStore ∧
          ¬Terminates (termChannelProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (termChannelProg h)
@cmdTyped_implies_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → TINI Γ c
cmdTyped_violates_tsni_witness : CmdTyped twoVarEnv Level.low (termChannelProg TwoVar.h) ∧
  (∀ (pc : Level), ¬TsTyped twoVarEnv pc (termChannelProg TwoVar.h)) ∧ ¬TSNI twoVarEnv (termChannelProg TwoVar.h)
constBranch_tini_not_cmdTyped : TINI twoVarEnv
    (Cmd.ite (Expr.var TwoVar.h) (Cmd.assign TwoVar.l (Expr.lit 0)) (Cmd.assign TwoVar.l (Expr.lit 0))) ∧
  ∀ (pc : Level),
    ¬CmdTyped twoVarEnv pc
        (Cmd.ite (Expr.var TwoVar.h) (Cmd.assign TwoVar.l (Expr.lit 0)) (Cmd.assign TwoVar.l (Expr.lit 0)))
@eval_deterministic : ∀ {Var : Type} [inst : DecidableEq Var] {c : Cmd Var} {σ σ₁ σ₂ : Store Var},
  Eval c σ σ₁ → Eval c σ σ₂ → σ₁ = σ₂
false_hyperprop_not_isTwoSafety : ¬IsTwoSafety (α := Unit) fun x => False
@isTwoSafety_holds_empty : ∀ {α : Type} {H : Hyperproperty α}, IsTwoSafety H → H fun x => False
@isTwoSafety_iff_csTwoSafety : ∀ {α : Type} (H : Hyperproperty α), IsTwoSafety H ↔ CSTwoSafety H
@lowGuardWhileTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level}
  {h : Var},
  Γ h = Level.high →
    LowGuardWhileTyped Γ pc (highIfLowWhileProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (highIfLowWhileProg h) zeroStore ∧
          ¬Terminates (highIfLowWhileProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (highIfLowWhileProg h)
@lowGuardWhileTyped_implies_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  LowGuardWhileTyped Γ pc c → CmdTyped Γ pc c
lowGuardWhileTyped_neg_while_h : ∀ (pc : Level), ¬LowGuardWhileTyped twoVarEnv pc (termChannelProg TwoVar.h)
@noHighGuardTyped_implies_cmdTyped_low : ∀ {Var : Type} {Γ : Var → Level} {c : Cmd Var},
  NoHighGuardTyped Γ c → CmdTyped Γ Level.low c
noHighGuardTyped_neg_implicit_flow : ¬NoHighGuardTyped twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h)
noPcTyped_neg_explicit_flow : ¬NoPcTyped twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
nondet_existential_tsni_not_tini : have R := fun x σ' => σ' = storeZero ∨ σ' = storeLowOne;
(∀ (σ₁ σ₂ σ₁' : Store TwoVar), LowEq twoVarEnv σ₁ σ₂ → R σ₁ σ₁' → ∃ σ₂', R σ₂ σ₂' ∧ LowEq twoVarEnv σ₁' σ₂') ∧
  ¬∀ (σ₁ σ₂ σ₁' σ₂' : Store TwoVar), LowEq twoVarEnv σ₁ σ₂ → R σ₁ σ₁' → R σ₂ σ₂' → LowEq twoVarEnv σ₁' σ₂'
@pcLowWhileTyped_allows_termination_channel : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {h : Var},
  Γ h = Level.high →
    PcLowWhileTyped Γ Level.low (termChannelProg h) ∧
      LowEq Γ zeroStore (zeroStore.update h 1) ∧
        Terminates (termChannelProg h) zeroStore ∧
          ¬Terminates (termChannelProg h) (zeroStore.update h 1) ∧ ¬TSNI Γ (termChannelProg h)
@pcLowWhileTyped_implies_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  PcLowWhileTyped Γ pc c → CmdTyped Γ pc c
pcLowWhileTyped_neg_high_if_low_while : ∀ (pc : Level), ¬PcLowWhileTyped twoVarEnv pc (highIfLowWhileProg TwoVar.h)
@probeProg_cmdTyped : ∀ {Var : Type} (Γ : Var → Level) (pc : Level) (l h : Var), CmdTyped Γ pc (probeProg l h)
@probeProg_termination_profile_determines_secret : ∀ {Var : Type} [inst : DecidableEq Var] {l h : Var},
  l ≠ h →
    ∀ (σ σ' : Store Var),
      (∀ (n : Int), Terminates (probeProg l h) (σ.update l n) ↔ Terminates (probeProg l h) (σ'.update l n)) → σ h = σ' h
subSelf_tini_not_cmdTyped : TINI twoVarEnv (Cmd.assign TwoVar.l ((Expr.var TwoVar.h).sub (Expr.var TwoVar.h))) ∧
  ∀ (pc : Level), ¬CmdTyped twoVarEnv pc (Cmd.assign TwoVar.l ((Expr.var TwoVar.h).sub (Expr.var TwoVar.h)))
timingExample_tsTyped : TsTyped twoVarEnv Level.low
  (Cmd.ite (Expr.var TwoVar.h)
    ((Cmd.assign TwoVar.h ((Expr.var TwoVar.h).add (Expr.lit 1))).seq
      (Cmd.assign TwoVar.h ((Expr.var TwoVar.h).add (Expr.lit 1))))
    Cmd.skip)
tiniHyperprop_not_oneSafety : ¬IsOneSafety (tiniHyperprop twoVarEnv)
@tini_iff_tiniHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TINI Γ c ↔ tiniHyperprop Γ (ioBehavior c)
@tsTyped_implies_tsni : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → TSNI Γ c
@tsniHyperprop_all_low_subsetClosed : ∀ {Var : Type} {Γ : Var → Level},
  (∀ (x : Var), Γ x = Level.low) → SubsetClosed (tsniHyperprop Γ)
@tsniHyperprop_termPairs_not_subsetClosed_of_high_var : ∀ {Var : Type} {Γ : Var → Level} {h : Var},
  Γ h = Level.high → ¬SubsetClosed (tsniHyperprop Γ)
@tsniOutHyperprop_isTwoSafety : ∀ {Var : Type} (Γ : Var → Level), IsTwoSafety (tsniOutHyperprop Γ)
@tsniOutHyperprop_subsetClosed : ∀ {Var : Type} (Γ : Var → Level), SubsetClosed (tsniOutHyperprop Γ)
tsni_char_nonvacuous : TSNI twoVarEnv (Cmd.assign TwoVar.l ((Expr.var TwoVar.l).add (Expr.lit 1))) ∧
  (TINI twoVarEnv (termChannelProg TwoVar.h) ∧ ¬CoTerminates twoVarEnv (termChannelProg TwoVar.h)) ∧
    CoTerminates twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h) ∧ ¬TINI twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
@tsni_iff_tini_and_coterminates : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ TINI Γ c ∧ CoTerminates Γ c
@tsni_iff_tsniOutHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ tsniOutHyperprop Γ (outcomeBehavior c)
whileHZero_tsni_not_tsTyped : TSNI twoVarEnv whileHZero ∧ ∀ (pc : Level), ¬TsTyped twoVarEnv pc whileHZero
@whileNoPcTyped_accepts_leak_violating_tini : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {l h : Var},
  Γ l = Level.low → Γ h = Level.high → WhileNoPcTyped Γ Level.low (whileLeakProg l h) ∧ ¬TINI Γ (whileLeakProg l h)
whileNoPcTyped_neg_implicit_flow : ∀ (pc : Level), ¬WhileNoPcTyped twoVarEnv pc (implicitFlowProg TwoVar.l TwoVar.h)
whileOne_tsTyped_low_not_high : TsTyped twoVarEnv Level.low (Cmd.whileLoop (Expr.lit 1) Cmd.skip) ∧
  ¬TsTyped twoVarEnv Level.high (Cmd.whileLoop (Expr.lit 1) Cmd.skip)
```

### Statements of supporting lemmas, scope witnesses, and definition examples cited in prose and non-claims, as printed by Lean

These proved declarations are cited in non-claims, definitions, or prose, or serve as proof helpers (outside the 51 card-hashed names above). Every one is kernel-checked in the same build and recorded in `audit/axioms.json`.

| Declaration | Cited in | Axioms |
|---|---|---|
| `cmdTyped_violates_tsni_witness` | Result 8 non-claim 3; retained witness (not hashed) | `propext` |
| `cmdTyped_high_preserves_lowEq` | Proof helper (confinement) for Results 1 and 8 | `propext` |
| `tsTyped_high_total` | Proof helper (loop-free totality at pc = high) for Result 8 | none |
| `isTwoSafety_holds_empty` | Definitions, Results 5, 6, 7, 13 non-claims | none |
| `isTwoSafety_admits_empty` | Hyperproperties.lean (duplicate of `isTwoSafety_holds_empty`) | none |
| `isTwoSafety_iff_csTwoSafety` | Definitions, Results 5, 6, 7, 13 non-claims | `Classical.choice`, `Quot.sound`, `propext` |
| `false_hyperprop_not_isTwoSafety` | Definitions, Results 5, 6, 7, 13 non-claims | none |
| `atMostTwoTraces_subsetClosed_not_twoSafety` | Result 5 non-claim 1; `IsTwoSafety` negative example | `propext` |
| `tiniHyperprop_not_oneSafety` | Result 6 non-claim 1; `IsOneSafety` negative example | `propext` |
| `tini_iff_tiniHyperprop` | Result 4 proof & design question | none |
| `tsni_iff_tsniHyperprop` | `tsniHyperprop` characterization bridge | none |
| `tsniHyperprop_all_low_isTwoSafety` | Base theorem for `tsniHyperprop_all_low_isTwoSafety_witness` | `Quot.sound` |
| `probeProg_cmdTyped` | Results 1 & 3 non-claims (multi-run termination probe) | none |
| `probeProg_terminates_iff` | Exact termination condition for `probeProg` | `propext` |
| `probeProg_termination_profile_determines_secret` | Results 1 & 3 non-claims (repeated-run secret recovery) | `Classical.choice`, `Quot.sound`, `propext` |
| `whileHZero_tsni_not_tsTyped` | Results 8, 9, 11 non-claims (incompleteness of `TsTyped`) | `propext` |
| `subSelf_tini_not_cmdTyped` | Result 1 non-claim 8 (incompleteness of `CmdTyped`) | `propext` |
| `constBranch_tini_not_cmdTyped` | Results 1 & 2 non-claims (incompleteness of `CmdTyped`) | `propext` |
| `whileOne_tsTyped_low_not_high` | Result 8 non-claim 1 (`TsTyped` pc sensitivity on `while 1`) | none |
| `timingExample_tsTyped` | Result 8 non-claim 5 (typing half of timing boundary example) | none |
| `nondet_existential_tsni_not_tini` | Result 10 non-claim 1 (determinism boundary) | `propext` |
| `coTerminates_without_tini` | Result 10 non-vacuity witness (`CoTerminates ∧ ¬ TINI`) | `propext` |
| `eval_deterministic` | Results 10 & 13 proof dependency (determinism of `Eval`) | none |
| `low_ne_high_var` | Derivable `l ≠ h` lemma for Results 2 & 12 | none |
| `exprLevel_low_agrees` | Core expression-level agreement bridge | `propext` |
| `CmdTyped.antitone` | Results 1 & 8 prior art (`0 ⊢ c` generalization) | none |
| `TsTyped.antitone` | Result 8 prior art (`0 ⊢ c` generalization) | none |
| `WhileNoPcTyped.antitone` | Typing anti-monotonicity for `WhileNoPcTyped` | none |
| `tsTyped_implies_lowGuardWhileTyped` | Typing inclusion hierarchy | none |
| `tsTyped_implies_pcLowWhileTyped` | Typing inclusion hierarchy | none |
| `lowGuardWhileTyped_implies_cmdTyped` | Result 9 non-claim 3 (preserves `TINI`) | none |
| `pcLowWhileTyped_implies_cmdTyped` | Result 11 non-claim 1 (preserves `TINI`) | none |
| `tsTyped_implies_cmdTyped` | Typing inclusion hierarchy | none |
| `cmdTyped_implies_whileNoPcTyped` | Typing inclusion hierarchy | none |
| `whileNoPcTyped_implies_noPcTyped` | Typing inclusion hierarchy | none |
| `cmdTyped_implies_noPcTyped` | Typing inclusion hierarchy | none |
| `noPcTyped_neg_explicit_flow` | Result 2 non-claim 4 (`NoPcTyped` negative example) | none |
| `whileNoPcTyped_neg_implicit_flow` | Result 12 non-claim 1 (`WhileNoPcTyped` negative example) | none |
| `lowGuardWhileTyped_neg_while_h` | Result 9 non-claim 4 (`LowGuardWhileTyped` negative example) | `propext` |
| `pcLowWhileTyped_neg_high_if_low_while` | Result 11 non-claim 2 (`PcLowWhileTyped` negative example) | `propext` |
| `level_le_pos_low_high` | `Level.le` positive example | none |
| `level_le_neg_high_low` | `Level.le` negative example | none |
| `lowEq_pos_high_diff` | `LowEq` positive example | none |
| `lowEq_neg_low_diff` | `LowEq` negative example | `propext` |
| `eval_pos_while_decrement` | `Eval` positive example | `Quot.sound`, `propext` |
| `eval_neg_wrong_final` | `Eval` negative example | `propext` |
| `terminates_pos_assign` | `Terminates` positive example | none |
| `terminates_neg_while_one` | `Terminates` negative example | `propext` |
| `tini_pos_high_branch_high_write` | `TINI` positive example | `propext` |
| `tini_neg_explicit_flow` | `TINI` negative example | `propext` |
| `coTerminates_pos_skip` | `CoTerminates` positive example | none |
| `coTerminates_pos_while_l` | `CoTerminates` non-trivial positive example | `propext` |
| `coTerminates_neg_while_h` | `CoTerminates` negative example | `propext` |
| `tsni_pos_low_inc` | `TSNI` positive example | `propext` |
| `tsni_neg_while_h` | `TSNI` negative example | `propext` |
| `cmdTyped_pos_sampleTypedProg` | `CmdTyped` positive example | none |
| `cmdTyped_pos_while_h` | `CmdTyped` positive example | none |
| `whileHZero_cmdTyped_high` | `CmdTyped` positive example (`whileHZero` at `high`) | none |
| `cmdTyped_neg_explicit_flow` | `CmdTyped` negative example | none |
| `cmdTyped_neg_implicit_flow` | `CmdTyped` negative example | none |
| `noPcTyped_pos_implicit_flow` | `NoPcTyped` positive example | none |
| `whileNoPcTyped_pos_whileLeakProg` | `WhileNoPcTyped` positive example | none |
| `noHighGuardTyped_pos_low_ite` | `NoHighGuardTyped` positive example | none |
| `tsTyped_pos_sampleTsProg` | `TsTyped` positive example | none |
| `tsTyped_neg_while_h` | `TsTyped` negative example | `propext` |
| `tsTyped_neg_high_if_low_while` | `TsTyped` negative example | `propext` |
| `lowGuardWhileTyped_pos_high_if_low_while` | `LowGuardWhileTyped` positive example | none |
| `pcLowWhileTyped_pos_while_h` | `PcLowWhileTyped` positive example | none |
| `ioBehavior_pos_assign` | `ioBehavior` positive example | none |
| `ioBehavior_neg_wrong_final` | `ioBehavior` negative example | `propext` |
| `outcomeBehavior_pos_assign` | `outcomeBehavior` positive example | none |
| `outcomeBehavior_pos_while_one` | `outcomeBehavior` positive example | `propext` |
| `outcomeBehavior_neg_assign_none` | `outcomeBehavior` negative example | none |
| `outcomeBehavior_neg_wrong_final` | `outcomeBehavior` negative example | `propext` |
| `subsetClosed_pos_tiniHyperprop` | `SubsetClosed` positive example | `propext` |
| `subsetClosed_neg_nonEmpty` | `SubsetClosed` negative example | none |
| `subsetClosed_neg_tsniHyperprop` | `SubsetClosed` negative example | `propext` |
| `isOneSafety_pos_lowOutputZero` | `IsOneSafety` positive example | none |
| `isTwoSafety_pos_tiniHyperprop` | `IsTwoSafety` positive example | none |
| `csTwoSafety_pos_tiniHyperprop` | `CSTwoSafety` positive example | `Classical.choice`, `Quot.sound`, `propext` |
| `csTwoSafety_neg_atMostTwoTraces` | `CSTwoSafety` negative example | `Classical.choice`, `Quot.sound`, `propext` |
| `tiniHyperprop_pos_skip` | `tiniHyperprop` positive example | none |
| `tiniHyperprop_neg_explicit_flow` | `tiniHyperprop` negative example | `propext` |
| `tsniHyperprop_pos_skip` | `tsniHyperprop` positive example | none |
| `tsniHyperprop_neg_while_h` | `tsniHyperprop` negative example | `propext` |
| `tsniOutHyperprop_pos_skip` | `tsniOutHyperprop` positive example | `Classical.choice`, `Quot.sound`, `propext` |
| `tsniOutHyperprop_neg_while_h` | `tsniOutHyperprop` negative example | `Classical.choice`, `Quot.sound`, `propext` |

Output of `#check @name` (with `open Toy.IFC`) on the built library, unedited, except that the entries for `false_hyperprop_not_isTwoSafety`, `atMostTwoTraces_subsetClosed_not_twoSafety`, `subsetClosed_neg_nonEmpty` and `csTwoSafety_neg_atMostTwoTraces` are printed with `set_option pp.analyze true`, which shows the instantiations `(α := Unit)` or `(α := Fin 3)` that the default output omits:

```lean
cmdTyped_violates_tsni_witness : CmdTyped twoVarEnv Level.low (termChannelProg TwoVar.h) ∧
  (∀ (pc : Level), ¬TsTyped twoVarEnv pc (termChannelProg TwoVar.h)) ∧ ¬TSNI twoVarEnv (termChannelProg TwoVar.h)
@cmdTyped_high_preserves_lowEq : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {c : Cmd Var}
  {σ σ' : Store Var}, Eval c σ σ' → ∀ {pc : Level}, CmdTyped Γ pc c → pc = Level.high → LowEq Γ σ σ'
@tsTyped_high_total : ∀ {Var : Type} [inst : DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → pc = Level.high → ∀ (σ : Store Var), ∃ σ', Eval c σ σ'
@isTwoSafety_holds_empty : ∀ {α : Type} {H : Hyperproperty α}, IsTwoSafety H → H fun x => False
@isTwoSafety_admits_empty : ∀ {α : Type} {H : Hyperproperty α}, IsTwoSafety H → H fun x => False
@isTwoSafety_iff_csTwoSafety : ∀ {α : Type} (H : Hyperproperty α), IsTwoSafety H ↔ CSTwoSafety H
false_hyperprop_not_isTwoSafety : ¬IsTwoSafety (α := Unit) fun x => False
atMostTwoTraces_subsetClosed_not_twoSafety : SubsetClosed (α := Fin 3) atMostTwoTraces ∧
  ¬IsTwoSafety (α := Fin 3) atMostTwoTraces
tiniHyperprop_not_oneSafety : ¬IsOneSafety (tiniHyperprop twoVarEnv)
@tini_iff_tiniHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TINI Γ c ↔ tiniHyperprop Γ (ioBehavior c)
@tsni_iff_tsniHyperprop : ∀ {Var : Type} [inst : DecidableEq Var] (Γ : Var → Level) (c : Cmd Var),
  TSNI Γ c ↔ tsniHyperprop Γ (ioBehavior c)
@tsniHyperprop_all_low_isTwoSafety : ∀ {Var : Type} {Γ : Var → Level},
  (∀ (x : Var), Γ x = Level.low) → IsTwoSafety (tsniHyperprop Γ)
@probeProg_cmdTyped : ∀ {Var : Type} (Γ : Var → Level) (pc : Level) (l h : Var), CmdTyped Γ pc (probeProg l h)
@probeProg_terminates_iff : ∀ {Var : Type} [inst : DecidableEq Var] (l h : Var) (σ : Store Var),
  Terminates (probeProg l h) σ ↔ ¬σ l < σ h
@probeProg_termination_profile_determines_secret : ∀ {Var : Type} [inst : DecidableEq Var] {l h : Var},
  l ≠ h →
    ∀ (σ σ' : Store Var),
      (∀ (n : Int), Terminates (probeProg l h) (σ.update l n) ↔ Terminates (probeProg l h) (σ'.update l n)) → σ h = σ' h
whileHZero_tsni_not_tsTyped : TSNI twoVarEnv whileHZero ∧ ∀ (pc : Level), ¬TsTyped twoVarEnv pc whileHZero
subSelf_tini_not_cmdTyped : TINI twoVarEnv (Cmd.assign TwoVar.l ((Expr.var TwoVar.h).sub (Expr.var TwoVar.h))) ∧
  ∀ (pc : Level), ¬CmdTyped twoVarEnv pc (Cmd.assign TwoVar.l ((Expr.var TwoVar.h).sub (Expr.var TwoVar.h)))
constBranch_tini_not_cmdTyped : TINI twoVarEnv
    (Cmd.ite (Expr.var TwoVar.h) (Cmd.assign TwoVar.l (Expr.lit 0)) (Cmd.assign TwoVar.l (Expr.lit 0))) ∧
  ∀ (pc : Level),
    ¬CmdTyped twoVarEnv pc
        (Cmd.ite (Expr.var TwoVar.h) (Cmd.assign TwoVar.l (Expr.lit 0)) (Cmd.assign TwoVar.l (Expr.lit 0)))
whileOne_tsTyped_low_not_high : TsTyped twoVarEnv Level.low (Cmd.whileLoop (Expr.lit 1) Cmd.skip) ∧
  ¬TsTyped twoVarEnv Level.high (Cmd.whileLoop (Expr.lit 1) Cmd.skip)
timingExample_tsTyped : TsTyped twoVarEnv Level.low
  (Cmd.ite (Expr.var TwoVar.h)
    ((Cmd.assign TwoVar.h ((Expr.var TwoVar.h).add (Expr.lit 1))).seq
      (Cmd.assign TwoVar.h ((Expr.var TwoVar.h).add (Expr.lit 1))))
    Cmd.skip)
nondet_existential_tsni_not_tini : have R := fun x σ' => σ' = storeZero ∨ σ' = storeLowOne;
(∀ (σ₁ σ₂ σ₁' : Store TwoVar), LowEq twoVarEnv σ₁ σ₂ → R σ₁ σ₁' → ∃ σ₂', R σ₂ σ₂' ∧ LowEq twoVarEnv σ₁' σ₂') ∧
  ¬∀ (σ₁ σ₂ σ₁' σ₂' : Store TwoVar), LowEq twoVarEnv σ₁ σ₂ → R σ₁ σ₁' → R σ₂ σ₂' → LowEq twoVarEnv σ₁' σ₂'
coTerminates_without_tini : CoTerminates twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h) ∧
  ¬TINI twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
@eval_deterministic : ∀ {Var : Type} [inst : DecidableEq Var] {c : Cmd Var} {σ σ₁ σ₂ : Store Var},
  Eval c σ σ₁ → Eval c σ σ₂ → σ₁ = σ₂
@low_ne_high_var : ∀ {Var : Type} {Γ : Var → Level} {l h : Var}, Γ l = Level.low → Γ h = Level.high → l ≠ h
@exprLevel_low_agrees : ∀ {Var : Type} {Γ : Var → Level} {σ₁ σ₂ : Store Var} {e : Expr Var},
  LowEq Γ σ₁ σ₂ → exprLevel Γ e = Level.low → eval σ₁ e = eval σ₂ e
@CmdTyped.antitone : ∀ {Var : Type} {Γ : Var → Level} {pc₁ pc₂ : Level} {c : Cmd Var},
  pc₁ ≤ pc₂ → CmdTyped Γ pc₂ c → CmdTyped Γ pc₁ c
@TsTyped.antitone : ∀ {Var : Type} {Γ : Var → Level} {pc₁ pc₂ : Level} {c : Cmd Var},
  pc₁ ≤ pc₂ → TsTyped Γ pc₂ c → TsTyped Γ pc₁ c
@WhileNoPcTyped.antitone : ∀ {Var : Type} {Γ : Var → Level} {pc₁ pc₂ : Level} {c : Cmd Var},
  pc₁ ≤ pc₂ → WhileNoPcTyped Γ pc₂ c → WhileNoPcTyped Γ pc₁ c
@tsTyped_implies_lowGuardWhileTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → LowGuardWhileTyped Γ pc c
@tsTyped_implies_pcLowWhileTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → PcLowWhileTyped Γ pc c
@lowGuardWhileTyped_implies_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  LowGuardWhileTyped Γ pc c → CmdTyped Γ pc c
@pcLowWhileTyped_implies_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  PcLowWhileTyped Γ pc c → CmdTyped Γ pc c
@tsTyped_implies_cmdTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  TsTyped Γ pc c → CmdTyped Γ pc c
@cmdTyped_implies_whileNoPcTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → WhileNoPcTyped Γ pc c
@whileNoPcTyped_implies_noPcTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  WhileNoPcTyped Γ pc c → NoPcTyped Γ c
@cmdTyped_implies_noPcTyped : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c : Cmd Var},
  CmdTyped Γ pc c → NoPcTyped Γ c
noPcTyped_neg_explicit_flow : ¬NoPcTyped twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
whileNoPcTyped_neg_implicit_flow : ∀ (pc : Level), ¬WhileNoPcTyped twoVarEnv pc (implicitFlowProg TwoVar.l TwoVar.h)
lowGuardWhileTyped_neg_while_h : ∀ (pc : Level), ¬LowGuardWhileTyped twoVarEnv pc (termChannelProg TwoVar.h)
pcLowWhileTyped_neg_high_if_low_while : ∀ (pc : Level), ¬PcLowWhileTyped twoVarEnv pc (highIfLowWhileProg TwoVar.h)
level_le_pos_low_high : Level.low ≤ Level.high
level_le_neg_high_low : ¬Level.high ≤ Level.low
lowEq_pos_high_diff : LowEq twoVarEnv storeZero storeHighOne
lowEq_neg_low_diff : ¬LowEq twoVarEnv storeZero storeLowOne
eval_pos_while_decrement : Eval
  (Cmd.whileLoop (Expr.var TwoVar.l) (Cmd.assign TwoVar.l ((Expr.var TwoVar.l).sub (Expr.lit 1)))) storeLowOne storeZero
eval_neg_wrong_final : ¬Eval (Cmd.assign TwoVar.l (Expr.lit 1)) storeZero storeZero
terminates_pos_assign : Terminates (Cmd.assign TwoVar.l (Expr.lit 1)) storeZero
terminates_neg_while_one : ¬Terminates (Cmd.whileLoop (Expr.lit 1) Cmd.skip) storeZero
tini_pos_high_branch_high_write : TINI twoVarEnv
  (Cmd.ite (Expr.var TwoVar.h) (Cmd.assign TwoVar.h (Expr.lit 1)) (Cmd.assign TwoVar.h (Expr.lit 0)))
tini_neg_explicit_flow : ¬TINI twoVarEnv (explicitFlowProg TwoVar.l TwoVar.h)
coTerminates_pos_skip : CoTerminates twoVarEnv Cmd.skip
coTerminates_pos_while_l : CoTerminates twoVarEnv (termChannelProg TwoVar.l) ∧
  ¬∀ (σ : Store TwoVar), Terminates (termChannelProg TwoVar.l) σ
coTerminates_neg_while_h : ¬CoTerminates twoVarEnv (termChannelProg TwoVar.h)
tsni_pos_low_inc : TSNI twoVarEnv (Cmd.assign TwoVar.l ((Expr.var TwoVar.l).add (Expr.lit 1)))
tsni_neg_while_h : ¬TSNI twoVarEnv (termChannelProg TwoVar.h)
cmdTyped_pos_sampleTypedProg : CmdTyped twoVarEnv Level.low sampleTypedProg
cmdTyped_pos_while_h : CmdTyped twoVarEnv Level.low (termChannelProg TwoVar.h)
whileHZero_cmdTyped_high : CmdTyped twoVarEnv Level.high whileHZero
cmdTyped_neg_explicit_flow : ∀ (pc : Level), ¬CmdTyped twoVarEnv pc (explicitFlowProg TwoVar.l TwoVar.h)
cmdTyped_neg_implicit_flow : ∀ (pc : Level), ¬CmdTyped twoVarEnv pc (implicitFlowProg TwoVar.l TwoVar.h)
noPcTyped_pos_implicit_flow : NoPcTyped twoVarEnv (implicitFlowProg TwoVar.l TwoVar.h)
whileNoPcTyped_pos_whileLeakProg : WhileNoPcTyped twoVarEnv Level.low (whileLeakProg TwoVar.l TwoVar.h)
noHighGuardTyped_pos_low_ite : NoHighGuardTyped twoVarEnv
  (Cmd.ite (Expr.var TwoVar.l) (Cmd.assign TwoVar.h (Expr.lit 1)) (Cmd.assign TwoVar.l (Expr.lit 0)))
tsTyped_pos_sampleTsProg : TsTyped twoVarEnv Level.low sampleTsProg
tsTyped_neg_while_h : ∀ (pc : Level), ¬TsTyped twoVarEnv pc (termChannelProg TwoVar.h)
tsTyped_neg_high_if_low_while : ∀ (pc : Level), ¬TsTyped twoVarEnv pc (highIfLowWhileProg TwoVar.h)
lowGuardWhileTyped_pos_high_if_low_while : LowGuardWhileTyped twoVarEnv Level.low (highIfLowWhileProg TwoVar.h)
pcLowWhileTyped_pos_while_h : PcLowWhileTyped twoVarEnv Level.low (termChannelProg TwoVar.h)
ioBehavior_pos_assign : ioBehavior (Cmd.assign TwoVar.l (Expr.lit 1)) (storeZero, storeLowOne)
ioBehavior_neg_wrong_final : ¬ioBehavior (Cmd.assign TwoVar.l (Expr.lit 1)) (storeZero, storeZero)
outcomeBehavior_pos_assign : outcomeBehavior (Cmd.assign TwoVar.l (Expr.lit 1)) (storeZero, some storeLowOne)
outcomeBehavior_pos_while_one : outcomeBehavior (Cmd.whileLoop (Expr.lit 1) Cmd.skip) (storeZero, none)
outcomeBehavior_neg_assign_none : ¬outcomeBehavior (Cmd.assign TwoVar.l (Expr.lit 1)) (storeZero, none)
outcomeBehavior_neg_wrong_final : ¬outcomeBehavior (Cmd.assign TwoVar.l (Expr.lit 1)) (storeZero, some storeZero)
subsetClosed_pos_tiniHyperprop : SubsetClosed (tiniHyperprop twoVarEnv)
subsetClosed_neg_nonEmpty : ¬SubsetClosed (α := Unit) nonEmptyTraceSet
subsetClosed_neg_tsniHyperprop : ¬SubsetClosed (tsniHyperprop twoVarEnv)
isOneSafety_pos_lowOutputZero : IsOneSafety fun S => ∀ (t : IOTrace TwoVar), S t → t.snd TwoVar.l = 0
isTwoSafety_pos_tiniHyperprop : IsTwoSafety (tiniHyperprop twoVarEnv)
csTwoSafety_pos_tiniHyperprop : CSTwoSafety (tiniHyperprop twoVarEnv)
csTwoSafety_neg_atMostTwoTraces : ¬CSTwoSafety (α := Fin 3) atMostTwoTraces
tiniHyperprop_pos_skip : tiniHyperprop twoVarEnv (ioBehavior Cmd.skip)
tiniHyperprop_neg_explicit_flow : ¬tiniHyperprop twoVarEnv (ioBehavior (explicitFlowProg TwoVar.l TwoVar.h))
tsniHyperprop_pos_skip : tsniHyperprop twoVarEnv (ioBehavior Cmd.skip)
tsniHyperprop_neg_while_h : ¬tsniHyperprop twoVarEnv (ioBehavior (termChannelProg TwoVar.h))
tsniOutHyperprop_pos_skip : tsniOutHyperprop twoVarEnv (outcomeBehavior Cmd.skip)
tsniOutHyperprop_neg_while_h : ¬tsniOutHyperprop twoVarEnv (outcomeBehavior (termChannelProg TwoVar.h))
```

### Core definitions, as printed by Lean

Output of `#print` on the built library, unedited:

```lean
inductive Toy.IFC.Level : Type
number of parameters: 0
constructors:
Toy.IFC.Level.low : Level
Toy.IFC.Level.high : Level
def Toy.IFC.Level.le : Level → Level → Prop :=
fun x x_1 =>
  match x, x_1 with
  | Level.low, x => True
  | Level.high, Level.high => True
  | Level.high, Level.low => False
def Toy.IFC.Level.join : Level → Level → Level :=
fun x x_1 =>
  match x, x_1 with
  | Level.low, l => l
  | Level.high, x => Level.high
@[reducible] def Toy.IFC.Store : Type → Type :=
fun Var => Var → Int
def Toy.IFC.Store.update : {Var : Type} → [DecidableEq Var] → Store Var → Var → Int → Store Var :=
fun {Var} [DecidableEq Var] σ x v y => if y = x then v else σ y
def Toy.IFC.zeroStore : {Var : Type} → Store Var :=
fun {Var} x => 0
def Toy.IFC.LowEq : {Var : Type} → (Var → Level) → Store Var → Store Var → Prop :=
fun {Var} Γ σ₁ σ₂ => ∀ (x : Var), Γ x = Level.low → σ₁ x = σ₂ x
inductive Toy.IFC.Expr : Type → Type
number of parameters: 1
constructors:
Toy.IFC.Expr.lit : {Var : Type} → Int → Expr Var
Toy.IFC.Expr.var : {Var : Type} → Var → Expr Var
Toy.IFC.Expr.add : {Var : Type} → Expr Var → Expr Var → Expr Var
Toy.IFC.Expr.sub : {Var : Type} → Expr Var → Expr Var → Expr Var
Toy.IFC.Expr.eq : {Var : Type} → Expr Var → Expr Var → Expr Var
Toy.IFC.Expr.lt : {Var : Type} → Expr Var → Expr Var → Expr Var
Toy.IFC.Expr.not : {Var : Type} → Expr Var → Expr Var
def Toy.IFC.eval : {Var : Type} → Store Var → Expr Var → Int :=
fun {Var} σ x => Expr.brecOn x (eval._f σ)
def Toy.IFC.exprLevel : {Var : Type} → (Var → Level) → Expr Var → Level :=
fun {Var} Γ x => Expr.brecOn x (exprLevel._f Γ)
inductive Toy.IFC.Cmd : Type → Type
number of parameters: 1
constructors:
Toy.IFC.Cmd.skip : {Var : Type} → Cmd Var
Toy.IFC.Cmd.assign : {Var : Type} → Var → Expr Var → Cmd Var
Toy.IFC.Cmd.seq : {Var : Type} → Cmd Var → Cmd Var → Cmd Var
Toy.IFC.Cmd.ite : {Var : Type} → Expr Var → Cmd Var → Cmd Var → Cmd Var
Toy.IFC.Cmd.whileLoop : {Var : Type} → Expr Var → Cmd Var → Cmd Var
inductive Toy.IFC.Eval : {Var : Type} → [DecidableEq Var] → Cmd Var → Store Var → Store Var → Prop
number of parameters: 2
constructors:
Toy.IFC.Eval.skip : ∀ {Var : Type} [inst : DecidableEq Var] {σ : Store Var}, Eval Cmd.skip σ σ
Toy.IFC.Eval.assign : ∀ {Var : Type} [inst : DecidableEq Var] {x : Var} {e : Expr Var} {σ : Store Var},
  Eval (Cmd.assign x e) σ (σ.update x (eval σ e))
Toy.IFC.Eval.seq : ∀ {Var : Type} [inst : DecidableEq Var] {c₁ c₂ : Cmd Var} {σ σm σ' : Store Var},
  Eval c₁ σ σm → Eval c₂ σm σ' → Eval (c₁.seq c₂) σ σ'
Toy.IFC.Eval.iteTrue : ∀ {Var : Type} [inst : DecidableEq Var] {e : Expr Var} {c₁ c₂ : Cmd Var} {σ σ' : Store Var},
  eval σ e ≠ 0 → Eval c₁ σ σ' → Eval (Cmd.ite e c₁ c₂) σ σ'
Toy.IFC.Eval.iteFalse : ∀ {Var : Type} [inst : DecidableEq Var] {e : Expr Var} {c₁ c₂ : Cmd Var} {σ σ' : Store Var},
  eval σ e = 0 → Eval c₂ σ σ' → Eval (Cmd.ite e c₁ c₂) σ σ'
Toy.IFC.Eval.whileFalse : ∀ {Var : Type} [inst : DecidableEq Var] {e : Expr Var} {c : Cmd Var} {σ : Store Var},
  eval σ e = 0 → Eval (Cmd.whileLoop e c) σ σ
Toy.IFC.Eval.whileTrue : ∀ {Var : Type} [inst : DecidableEq Var] {e : Expr Var} {c : Cmd Var} {σ σm σ' : Store Var},
  eval σ e ≠ 0 → Eval c σ σm → Eval (Cmd.whileLoop e c) σm σ' → Eval (Cmd.whileLoop e c) σ σ'
def Toy.IFC.Terminates : {Var : Type} → [DecidableEq Var] → Cmd Var → Store Var → Prop :=
fun {Var} [DecidableEq Var] c σ => ∃ σ', Eval c σ σ'
def Toy.IFC.TINI : {Var : Type} → [DecidableEq Var] → (Var → Level) → Cmd Var → Prop :=
fun {Var} [DecidableEq Var] Γ c =>
  ∀ (σ₁ σ₂ σ₁' σ₂' : Store Var), LowEq Γ σ₁ σ₂ → Eval c σ₁ σ₁' → Eval c σ₂ σ₂' → LowEq Γ σ₁' σ₂'
def Toy.IFC.CoTerminates : {Var : Type} → [DecidableEq Var] → (Var → Level) → Cmd Var → Prop :=
fun {Var} [DecidableEq Var] Γ c => ∀ (σ₁ σ₂ : Store Var), LowEq Γ σ₁ σ₂ → (Terminates c σ₁ ↔ Terminates c σ₂)
def Toy.IFC.TSNI : {Var : Type} → [DecidableEq Var] → (Var → Level) → Cmd Var → Prop :=
fun {Var} [DecidableEq Var] Γ c =>
  ∀ (σ₁ σ₂ σ₁' : Store Var), LowEq Γ σ₁ σ₂ → Eval c σ₁ σ₁' → ∃ σ₂', Eval c σ₂ σ₂' ∧ LowEq Γ σ₁' σ₂'
inductive Toy.IFC.CmdTyped : {Var : Type} → (Var → Level) → Level → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.CmdTyped.skip : ∀ {Var : Type} {Γ : Var → Level} {pc : Level}, CmdTyped Γ pc Cmd.skip
Toy.IFC.CmdTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → pc ≤ Γ x → CmdTyped Γ pc (Cmd.assign x e)
Toy.IFC.CmdTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c₁ c₂ : Cmd Var},
  CmdTyped Γ pc c₁ → CmdTyped Γ pc c₂ → CmdTyped Γ pc (c₁.seq c₂)
Toy.IFC.CmdTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  CmdTyped Γ (pc ⊔ exprLevel Γ e) c₁ → CmdTyped Γ (pc ⊔ exprLevel Γ e) c₂ → CmdTyped Γ pc (Cmd.ite e c₁ c₂)
Toy.IFC.CmdTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c : Cmd Var},
  CmdTyped Γ (pc ⊔ exprLevel Γ e) c → CmdTyped Γ pc (Cmd.whileLoop e c)
inductive Toy.IFC.NoPcTyped : {Var : Type} → (Var → Level) → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.NoPcTyped.skip : ∀ {Var : Type} {Γ : Var → Level}, NoPcTyped Γ Cmd.skip
Toy.IFC.NoPcTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → NoPcTyped Γ (Cmd.assign x e)
Toy.IFC.NoPcTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {c₁ c₂ : Cmd Var},
  NoPcTyped Γ c₁ → NoPcTyped Γ c₂ → NoPcTyped Γ (c₁.seq c₂)
Toy.IFC.NoPcTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  NoPcTyped Γ c₁ → NoPcTyped Γ c₂ → NoPcTyped Γ (Cmd.ite e c₁ c₂)
Toy.IFC.NoPcTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {e : Expr Var} {c : Cmd Var},
  NoPcTyped Γ c → NoPcTyped Γ (Cmd.whileLoop e c)
inductive Toy.IFC.WhileNoPcTyped : {Var : Type} → (Var → Level) → Level → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.WhileNoPcTyped.skip : ∀ {Var : Type} {Γ : Var → Level} {pc : Level}, WhileNoPcTyped Γ pc Cmd.skip
Toy.IFC.WhileNoPcTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → pc ≤ Γ x → WhileNoPcTyped Γ pc (Cmd.assign x e)
Toy.IFC.WhileNoPcTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c₁ c₂ : Cmd Var},
  WhileNoPcTyped Γ pc c₁ → WhileNoPcTyped Γ pc c₂ → WhileNoPcTyped Γ pc (c₁.seq c₂)
Toy.IFC.WhileNoPcTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  WhileNoPcTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
    WhileNoPcTyped Γ (pc ⊔ exprLevel Γ e) c₂ → WhileNoPcTyped Γ pc (Cmd.ite e c₁ c₂)
Toy.IFC.WhileNoPcTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c : Cmd Var},
  WhileNoPcTyped Γ pc c → WhileNoPcTyped Γ pc (Cmd.whileLoop e c)
inductive Toy.IFC.NoHighGuardTyped : {Var : Type} → (Var → Level) → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.NoHighGuardTyped.skip : ∀ {Var : Type} {Γ : Var → Level}, NoHighGuardTyped Γ Cmd.skip
Toy.IFC.NoHighGuardTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → NoHighGuardTyped Γ (Cmd.assign x e)
Toy.IFC.NoHighGuardTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {c₁ c₂ : Cmd Var},
  NoHighGuardTyped Γ c₁ → NoHighGuardTyped Γ c₂ → NoHighGuardTyped Γ (c₁.seq c₂)
Toy.IFC.NoHighGuardTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  exprLevel Γ e = Level.low → NoHighGuardTyped Γ c₁ → NoHighGuardTyped Γ c₂ → NoHighGuardTyped Γ (Cmd.ite e c₁ c₂)
Toy.IFC.NoHighGuardTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {e : Expr Var} {c : Cmd Var},
  exprLevel Γ e = Level.low → NoHighGuardTyped Γ c → NoHighGuardTyped Γ (Cmd.whileLoop e c)
inductive Toy.IFC.LowGuardWhileTyped : {Var : Type} → (Var → Level) → Level → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.LowGuardWhileTyped.skip : ∀ {Var : Type} {Γ : Var → Level} {pc : Level}, LowGuardWhileTyped Γ pc Cmd.skip
Toy.IFC.LowGuardWhileTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → pc ≤ Γ x → LowGuardWhileTyped Γ pc (Cmd.assign x e)
Toy.IFC.LowGuardWhileTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c₁ c₂ : Cmd Var},
  LowGuardWhileTyped Γ pc c₁ → LowGuardWhileTyped Γ pc c₂ → LowGuardWhileTyped Γ pc (c₁.seq c₂)
Toy.IFC.LowGuardWhileTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  LowGuardWhileTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
    LowGuardWhileTyped Γ (pc ⊔ exprLevel Γ e) c₂ → LowGuardWhileTyped Γ pc (Cmd.ite e c₁ c₂)
Toy.IFC.LowGuardWhileTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c : Cmd Var},
  exprLevel Γ e = Level.low → LowGuardWhileTyped Γ pc c → LowGuardWhileTyped Γ pc (Cmd.whileLoop e c)
inductive Toy.IFC.PcLowWhileTyped : {Var : Type} → (Var → Level) → Level → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.PcLowWhileTyped.skip : ∀ {Var : Type} {Γ : Var → Level} {pc : Level}, PcLowWhileTyped Γ pc Cmd.skip
Toy.IFC.PcLowWhileTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → pc ≤ Γ x → PcLowWhileTyped Γ pc (Cmd.assign x e)
Toy.IFC.PcLowWhileTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c₁ c₂ : Cmd Var},
  PcLowWhileTyped Γ pc c₁ → PcLowWhileTyped Γ pc c₂ → PcLowWhileTyped Γ pc (c₁.seq c₂)
Toy.IFC.PcLowWhileTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  PcLowWhileTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
    PcLowWhileTyped Γ (pc ⊔ exprLevel Γ e) c₂ → PcLowWhileTyped Γ pc (Cmd.ite e c₁ c₂)
Toy.IFC.PcLowWhileTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c : Cmd Var},
  pc = Level.low → PcLowWhileTyped Γ (pc ⊔ exprLevel Γ e) c → PcLowWhileTyped Γ pc (Cmd.whileLoop e c)
inductive Toy.IFC.TsTyped : {Var : Type} → (Var → Level) → Level → Cmd Var → Prop
number of parameters: 2
constructors:
Toy.IFC.TsTyped.skip : ∀ {Var : Type} {Γ : Var → Level} {pc : Level}, TsTyped Γ pc Cmd.skip
Toy.IFC.TsTyped.assign : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {x : Var} {e : Expr Var},
  exprLevel Γ e ≤ Γ x → pc ≤ Γ x → TsTyped Γ pc (Cmd.assign x e)
Toy.IFC.TsTyped.seq : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {c₁ c₂ : Cmd Var},
  TsTyped Γ pc c₁ → TsTyped Γ pc c₂ → TsTyped Γ pc (c₁.seq c₂)
Toy.IFC.TsTyped.ite : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c₁ c₂ : Cmd Var},
  TsTyped Γ (pc ⊔ exprLevel Γ e) c₁ → TsTyped Γ (pc ⊔ exprLevel Γ e) c₂ → TsTyped Γ pc (Cmd.ite e c₁ c₂)
Toy.IFC.TsTyped.whileLoop : ∀ {Var : Type} {Γ : Var → Level} {pc : Level} {e : Expr Var} {c : Cmd Var},
  pc = Level.low → exprLevel Γ e = Level.low → TsTyped Γ Level.low c → TsTyped Γ pc (Cmd.whileLoop e c)
@[reducible] def Toy.IFC.IOTrace : Type → Type :=
fun Var => Store Var × Store Var
@[reducible] def Toy.IFC.OutTrace : Type → Type :=
fun Var => Store Var × Option (Store Var)
@[reducible] def Toy.IFC.TraceSet : Type → Type :=
fun α => α → Prop
@[reducible] def Toy.IFC.Hyperproperty : Type → Type :=
fun α => TraceSet α → Prop
def Toy.IFC.ioBehavior : {Var : Type} → [DecidableEq Var] → Cmd Var → TraceSet (IOTrace Var) :=
fun {Var} [DecidableEq Var] c p => Eval c p.fst p.snd
def Toy.IFC.outcomeBehavior : {Var : Type} → [DecidableEq Var] → Cmd Var → TraceSet (OutTrace Var) :=
fun {Var} [DecidableEq Var] c p =>
  match p.snd with
  | some σ' => Eval c p.fst σ'
  | none => ¬Terminates c p.fst
def Toy.IFC.SubsetClosed : {α : Type} → Hyperproperty α → Prop :=
fun {α} H => ∀ (S₁ S₂ : TraceSet α), (∀ (t : α), S₁ t → S₂ t) → H S₂ → H S₁
def Toy.IFC.IsOneSafety : {α : Type} → Hyperproperty α → Prop :=
fun {α} H => ∀ (S : TraceSet α), H S ↔ ∀ (t : α), S t → H fun u => u = t
def Toy.IFC.IsTwoSafety : {α : Type} → Hyperproperty α → Prop :=
fun {α} H => ∀ (S : TraceSet α), H S ↔ ∀ (t₁ t₂ : α), S t₁ → S t₂ → H fun t => t = t₁ ∨ t = t₂
def Toy.IFC.CSTwoSafety : {α : Type} → Hyperproperty α → Prop :=
fun {α} H => ∀ (S : TraceSet α), ¬H S → ∃ t₁ t₂, S t₁ ∧ S t₂ ∧ ∀ (S' : TraceSet α), S' t₁ → S' t₂ → ¬H S'
def Toy.IFC.nonEmptyTraceSet : {α : Type} → Hyperproperty α :=
fun {α} S => ∃ t, S t
def Toy.IFC.atMostTwoTraces : {α : Type} → Hyperproperty α :=
fun {α} S => ∀ (t₁ t₂ t₃ : α), S t₁ → S t₂ → S t₃ → t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃
def Toy.IFC.tiniRel : {Var : Type} → (Var → Level) → IOTrace Var → IOTrace Var → Prop :=
fun {Var} Γ t₁ t₂ => LowEq Γ t₁.fst t₂.fst → LowEq Γ t₁.snd t₂.snd
def Toy.IFC.tiniHyperprop : {Var : Type} → (Var → Level) → Hyperproperty (IOTrace Var) :=
fun {Var} Γ S => ∀ (t₁ t₂ : IOTrace Var), S t₁ → S t₂ → tiniRel Γ t₁ t₂
def Toy.IFC.tsniHyperprop : {Var : Type} → (Var → Level) → Hyperproperty (IOTrace Var) :=
fun {Var} Γ S => ∀ (σ₁ σ₂ σ₁' : Store Var), LowEq Γ σ₁ σ₂ → S (σ₁, σ₁') → ∃ σ₂', S (σ₂, σ₂') ∧ LowEq Γ σ₁' σ₂'
def Toy.IFC.tsniOutRel : {Var : Type} → (Var → Level) → OutTrace Var → OutTrace Var → Prop :=
fun {Var} Γ t₁ t₂ =>
  LowEq Γ t₁.fst t₂.fst →
    match t₁.snd, t₂.snd with
    | some a, some b => LowEq Γ a b
    | none, none => True
    | x, x_1 => False
def Toy.IFC.tsniOutHyperprop : {Var : Type} → (Var → Level) → Hyperproperty (OutTrace Var) :=
fun {Var} Γ S => ∀ (t₁ t₂ : OutTrace Var), S t₁ → S t₂ → tsniOutRel Γ t₁ t₂
```

### Primary sources

Bibliographic data for DOIs were checked against Crossref records; AFP mirror paths were checked via the GitHub API at `isabelle-prover/mirror-afp-devel` commit `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`; the HOL-IMP files `src/HOL/IMP/Sec_Typing.thy` and `src/HOL/IMP/Sec_TypingT.thy` were fetched at `isabelle-prover/mirror-isabelle` commit `d2ede99d0077d2777ed2b83d084d3aadf93826b5` and compared token for token with the Isabelle library web pages (identical). "Content seen" indicates the cited passage or source file was read directly; "abstract" indicates only the landing page/abstract was read; "bibliographic only" indicates only the bibliographic record was verified.

| Source | Used for | Status |
|---|---|---|
| D. E. Denning and P. J. Denning, "Certification of programs for secure information flow", *CACM* 20(7):504–513, July 1977, DOI `10.1145/359636.359712` | Origin of static certification approach (no soundness proof) | Crossref (bibliographic only; VSI 1996 abstract consulted on lack of soundness proof) |
| D. Volpano, C. Irvine, and G. Smith, "A sound type system for secure flow analysis", *J. Comput. Secur.* 4(2–3):167–187, 1996, DOI `10.3233/JCS-1996-42-304` | Phrase types `τ var`/`τ cmd`, contravariant subtyping, Theorem 6.8 (TINI soundness) | Crossref + content seen (author preprint PDF) |
| D. Volpano and G. Smith, "Eliminating Covert Flows with Minimum Typings", *CSFW '97*, pp. 156–168, June 1997, DOI `10.1109/CSFW.1997.596807` | Rule `(WHILE)`, §1 prose contrast, Thm 3.1 (TSNI & alternative decomposition), §5 Thm 5.3 (Timing Agreement) | Crossref + content seen (PDF) |
| G. Smith and D. Volpano, "Secure information flow in a multi-threaded imperative language", *POPL '98*, pp. 355–364, 1998, DOI `10.1145/268946.268975` | Multi-threaded concurrency non-claim boundary | Crossref (bibliographic + secondary summary in Sabelfeld & Myers 2003) |
| J. Agat, "Transforming out timing leaks", *POPL '00*, pp. 40–53, Jan. 2000, DOI `10.1145/325694.325702` | Timing-leak transformation boundary pointer | Crossref (bibliographic + secondary summary in Sabelfeld & Myers 2003) |
| A. Sabelfeld and A. C. Myers, "Language-based information-flow security", *IEEE JSAC* 21(1):5–19, Jan. 2003, DOI `10.1109/JSAC.2002.806121` | Survey, `pc`-label overview, §IV-C termination channels, explicit-`⊥` low-view relation, VS97 loop rules | Crossref + content seen (author PDF) |
| G. Barthe, P. R. D'Argenio, and T. Rezk, "Secure Information Flow by Self-Composition", *CSFW 2004*, pp. 100–114, DOI `10.1109/CSFW.2004.1310735`; journal *MSCS* 21(6):1207–1252, 2011, DOI `10.1017/S0960129511000193` | Self-composition formulation of noninterference | Crossref (bibliographic + descriptions in C&S 2010 and T&A 2005) |
| T. Terauchi and A. Aiken, "Secure Information Flow as a Safety Problem", *SAS 2005*, LNCS 3672, pp. 352–367, 2005, DOI `10.1007/11547662_24` | Def. 4 (`⊥`-based 2-safety program set), Thm 1, §1 "2-liveness" remark | Crossref + content seen (author PDF) |
| S. Hunt and D. Sands, "On flow-sensitive security types", *POPL '06*, pp. 79–90, Jan. 2006, DOI `10.1145/1111037.1111045` | Alternative flow-sensitive control-dependence discipline | Crossref (bibliographic only) |
| A. Askarov, S. Hunt, A. Sabelfeld, and D. Sands, "Termination-Insensitive Noninterference Leaks More Than Just a Bit", *ESORICS 2008*, LNCS 5283, pp. 333–348, 2008, DOI `10.1007/978-3-540-88313-5_22` | Interactive outputs leak all secrets; brute-force lower/upper bound & polynomial-time infeasibility for uniform secrets | Crossref + content seen (author PDF) |
| M. R. Clarkson and F. B. Schneider, "Hyperproperties", *J. Comput. Secur.* 18(6):1157–1210, 2010, DOI `10.3233/JCS-2009-0393` | Thm 1 (`SHP ⊂ SSC`), §7.2.1 (`TSRNI` neither hypersafety nor hyperliveness for `Rel`), fn. 23 (`2-infinite-safety`) | Crossref + content seen (author PDF) |
| T. Nipkow and G. Klein, *Concrete Semantics: With Isabelle/HOL*, Ch. 9 "Types", pp. 115–142, Springer, 2014, DOI `10.1007/978-3-319-10542-0_9` | §9.2.2 `sec_type`, Thm 9.14 (`TINI`), §9.2.6 termination/timing channels, Fig. 9.10, Lemma 9.21, Thm 9.22 (`TSNI`) | Crossref + content seen (authors' online edition) |
| T. Nipkow, Isabelle/HOL HOL-IMP `Sec_Typing.thy` and `Sec_TypingT.thy`, <https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_Typing.html> and <https://isabelle.in.tum.de/library/HOL/HOL-IMP/Sec_TypingT.html> (`mirror-isabelle` `d2ede99d…`, `src/HOL/IMP`) | Exact mechanized counterparts (`sec_type`, `anti_mono`, `confinement`, `noninterference`, `termi_if_non0`) | Content seen (theory web pages); same token sequence verified at the pinned mirror commit |
| C. Hriţcu, Y. Kim, et al., *Security Foundations* (Software Foundations Vol. 7, Version 1.2, 2026-08-24, Rocq 9.0.0+), chapter `StaticIFC`, <https://softwarefoundations.cis.upenn.edu/secf-current/> | `cf_well_typed`, `ni_well_typed_noninterferent`, `ts_well_typed` (`TSWT_While`), `termination_leak`, `tsni_com_tsni_alt_same` | Content seen (TOC and `StaticIFC`; Version 1.2 verified 2026-11-20) |
| G. Snelting and D. Wasserrab, "A Correctness Proof for the Volpano/Smith Security Typing System", *AFP*, Sept. 2008, <https://isa-afp.org/entries/VolpanoSmith.html> (`mirror-afp-devel` `523cdc72…`, `thys/VolpanoSmith`) | Isabelle/HOL VSI baseline TINI mechanization | Abstract read; directory path verified at pinned mirror commit |
| L. Beringer and M. Hofmann, "Secure information flow and program logics", *AFP*, Nov. 2008, <https://isa-afp.org/entries/SIFPL.html> (`mirror-afp-devel` `523cdc72…`, `thys/SIFPL`) | Isabelle/HOL VSI & Hunt–Sands program-logic mechanization | Abstract read; directory path verified at pinned mirror commit |
| P. Noce, "Information Flow Control via Stateful Intransitive Noninterference in Language IMP", *AFP*, Feb. 2024, <https://isa-afp.org/entries/IMP_Noninterference.html> (`mirror-afp-devel` `523cdc72…`, `thys/IMP_Noninterference`) | Isabelle/HOL TSNI degenerating to Nipkow & Klein's TS system | Abstract read; directory path verified at pinned mirror commit |

Lean / Mathlib search record: best-effort search for Lean 4 formalizations of Volpano–Smith / Nipkow–Klein noninterference typing and termination channels found no existing Lean 4 or Mathlib formalization (absence not guaranteed).

## Revalidation

Requires `elan` (which provides the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The primary check is the included script `support/revalidate.py` (Python 3 standard library only; its SHA-256 is recorded under Evidence). Run it from the package directory:

```bash
python3 support/revalidate.py .
```

The script never modifies the package: it copies `lean/` to a temporary directory and builds there. It performs exactly these checks:

1. **Banned tokens.** Every `.lean` file under `lean/` (comments stripped) is scanned for `sorry`, `admit`, `native_decide`, and `axiom` declarations.
2. **Build.** `lake build` of the copied Lake project must succeed.
3. **Axioms.** A generated audit program, run with `lake env lean`, computes with `Lean.collectAxioms` the axioms of every non-internal declaration of the `Toy` library; every footprint must lie within `propext`, `Classical.choice`, and `Quot.sound`.
4. **Names and statement hashes.** The script collects every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, `scope_witnesses_lean`, `corollaries_lean`, and hypothesis `counterexample`s; this package uses all of them except `lean_names` and `corollaries_lean`) together with every name recorded in `audit/statements.json`. Each must exist in the built library. For each recorded name it recomputes exactly three values and compares them with `audit/statements.json`:
   - `statement_sha256`: the SHA-256 of the UTF-8 text `toString (repr ci.type)` of the declaration's type;
   - `closure_sha256`: the SHA-256 of the newline-joined, sorted entries `name : repr type`, each followed by ` := repr value` for constants that are not theorems and have a value, covering every constant of the `Toy` modules reachable from the statement's type through types, non-theorem definition values, and inductive constructors (theorem proofs are never hashed);
   - `closure_size`: the number of such entries.

   Referenced names without a recorded hash (here, the 22 unhashed scope witnesses) are checked for existence only; their statements are printed under Evidence for comparison with fresh `#check` output.

Expected output (observed 2026-11-20), with exit status 0:

```text
ok   lake build
ok   axioms (578 declarations)
ok   statement hashes (51 hashed names; 22 referenced names exist but carry no recorded hash)
REVALIDATED
```

### Manual alternative (also compares `audit/axioms.json`)

The following procedure uses only `lake`, `lean`, and `python3` with an inline audit program. It recomputes the same 51 statement hashes and additionally compares every declaration's axiom list with `audit/axioms.json`, which `support/revalidate.py` does not do. It does not check that the 22 unhashed `scope_witnesses_lean` names exist and does not scan the sources for banned tokens; `support/revalidate.py` performs both checks. Work on a scratch copy so no build artifacts enter the package tree. From the package directory:

```bash
WORK="$(mktemp -d)"
cp -R lean "$WORK/lean"
cp -R results.json audit "$WORK/"
cd "$WORK/lean"

# 1. Build under the pinned toolchain (expect success, zero warnings).
lake build

# 2. Card-hashed names (expect 51 lines; unhashed scope witnesses are not collected).
python3 - <<'EOF'
import json
R = json.load(open('../results.json'))
names = set()
for r in R:
    le = r['lean'] if isinstance(r['lean'], list) else [r['lean']]
    nw = r.get('nonvacuity_witness_lean', [])
    nw = [nw] if isinstance(nw, str) else list(nw)
    pc = r.get('positive_control_lean', [])
    pc = [pc] if isinstance(pc, str) else list(pc)
    names |= set(le) | set(nw) | set(pc)
    for h in r['hypotheses']:
        ce = h.get('counterexample', [])
        ce = [ce] if isinstance(ce, str) else list(ce)
        names |= set(ce)
open('card_names.txt', 'w').write('\n'.join(sorted(names)) + '\n')
EOF
```

3. Save the following as `RevalidationAudit.lean` in `$WORK/lean` and run `lake env lean RevalidationAudit.lean > audit_output.json`:

```lean
import Lean
import Toy
open Lean Elab Command

/-! Revalidation audit: axioms of every declaration of the library, and the statement and
definition-closure text of every declaration named in `results.json`. -/

private def inLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLib env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names ← (do
    let txt ← IO.FS.readFile "card_names.txt"
    pure ((txt.splitOn "\n").filter (· ≠ "") |>.map String.toName))
  let mut decls : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if inLib env n && !n.isInternal then
      let axs ← collectAxioms n
      let kind := match ci with
        | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .thmInfo _ => "theorem"
        | .defnInfo _ => "def" | _ => "other"
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("kind", toJson kind),
        ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in names do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := closure env ci.type.getUsedConstants.toList {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ((Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
```

4. Compare with the recorded audit in the copied `audit/` directory:

```bash
python3 - audit_output.json .. <<'EOF'
import hashlib, json, sys

out = json.load(open(sys.argv[1]))
pkg = sys.argv[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}
ax_rec = json.load(open(f"{pkg}/audit/axioms.json"))["declarations"]
st_rec = json.load(open(f"{pkg}/audit/statements.json"))["statements"]
ax_now = {d["name"]: sorted(d["axioms"]) for d in out["decls"]}
bad = [d["name"] for d in out["decls"] if set(d["axioms"]) - allowed or d["kind"] in ("axiom", "opaque")]
st_now = {}
missing = []
for s in out["stmts"]:
    if s.get("missing"):
        missing.append(s["name"])
        continue
    st_now[s["name"]] = {
        "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
        "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
        "closure_size": len(s["closure"]),
    }
print("declarations audited:", len(ax_now))
print("disallowed axioms or axiom/opaque declarations:", bad)
print("axioms match audit/axioms.json:", ax_now == ax_rec)
print("missing card names:", missing)
print("statement hashes match audit/statements.json:", st_now == st_rec, f"({len(st_now)} hashed)")
EOF
```

Expected output: `declarations audited: 578`, an empty list of disallowed axioms, `axioms match audit/axioms.json: True`, no missing card names, and `statement hashes match audit/statements.json: True (51 hashed)`.

### What these checks establish

That the Lean statements and definitions are unchanged and kernel-check with the recorded axioms under this toolchain. They do not re-verify prose claims; after any change to a definition or statement, re-read the affected cards against the new `#check` output. For a different Lean version, rebuild first; statement hashes depend on `repr` output and may differ across toolchains even when the mathematics is unchanged.
