# Verified checker theorem endpoints: Lean4Lean, MetaRocq, and Candle

## Summary

The inspected systems verify different parts of theorem acceptance. Lean4Lean supplies source-level correctness results relating a Lean implementation to its formal typing/environment model, with an admitted inductive-declaration case and explicit assumptions about upstream operations. MetaRocq's checker returns typed evidence for an encoded PCUIC program under configuration, normalization, and abstract-environment premises; its inspected extraction unit also assumes a guard implementation's correctness. Candle's source theorem constrains theorem-channel events under stated program and state conditions, and its published compiler theorem carries this result to a particular machine-code execution model.

A verified logical checker, a complete declaration checker, a faithful reifier, a certified extracted implementation, and the binary actually run are separate endpoints. The source evidence here supports that distinction; it does not establish an assumption-free executable checker for Anneal.

## Applicability

Directly inspected source pins are Lean4Lean `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, MetaRocq `c8cd46054518193103c3bb33aa6e15c7f489e72c`, and CakeML `f73189499bb295f0859dec7ee38c169c48da682c`. Lean4Lean's own `lean-toolchain` selects Lean 4.33.0-rc2. The available Lean 4.34.1 was not used to build Lean4Lean, and no compatibility with Anneal's 4.31 pin is inferred.

The Candle publication is the extended version identified by DOI `10.1007/s10817-025-09743-8`. The current pinned source was inspected separately; this report does not assert that it is the exact publication artifact or that a published binary was rebuilt. No Lean4Lean, Rocq/MetaRocq, HOL4, or CakeML build or installation was performed.

## Findings

### Lean4Lean's checking results expose both successful checks and their context premises

`TypeChecker.checkType.WF` states that successful checking yields a translation of the input expression and its inferred type into the formal typing relation, given the context/state invariants. The `inferOnly` variant has a stronger caller obligation: when inference-only mode is enabled, an appropriate translation of the term must already be supplied. `isDefEq.WF` establishes equality in the formal relation only from translated input expressions and a successful Boolean result.

`checkTheorem.WF` additionally relates a theorem declaration to a formal declaration whose body is well typed, whose type inhabits `Prop`, and whose name is fresh and not a reserved primitive. The environment well-formedness bundle contains a translation, primitive conditions, and safety-level relationships. The implementation theorem is conditional on that formal environment; accepting a theorem against an arbitrary imported environment is not its conclusion.

Basis: **source**, `Lean4Lean/Verify/TypeChecker.lean`, `checkType.WF`, `inferType.WF'`, `isDefEq.WF`; `Lean4Lean/Verify/Environment/Checker.lean`, `checkTheorem.WF`.

### The all-declaration theorem still has an admitted inductive case

At this exact pin, `Lean4Lean/Verify/Environment.lean` ends `addDecl.WF` with an admitted `inductDecl` case. The theorem is therefore not a completed assumption-free verification of every declaration form. The same file explains that its abstract `AddInduct` boundary has no constructors; `checkEqType.WF` derives an impossible successful case, and the non-initialized quotient branch is presently vacuous because the translated environment cannot yet contain the required inductive `Eq` declaration.

This is a limitation of the formal coverage at the pin, not evidence that the executable checker accepts invalid inductives. Nor does it erase the separate checking results for supported formal contexts. It prevents using the aggregate theorem as completed evidence for the full declaration/environment chain.

Basis: **source**, `Lean4Lean/Verify/Environment.lean`, `checkEqType.WF`, `addQuot.WF`, `addDecl.WF`, especially lines 113–139 and 220–235.

### Upstream operation assumptions and the executable wrapper remain distinct

`Lean4Lean/Verify/Axioms.lean` contains explicit assumptions about persistent arrays/maps, expression operations, and level operations. For example, it assumes equivalence between the upstream partial level normalizer and a total copy; comments identify opacity or partial definitions as the obstacle to proving several equations. These assumptions can be narrow implementation obligations, but they are not discharged by calling the surrounding checker verified.

The CLI is an `unsafe` Lean program that discovers `.olean` files and offers two replay modes. `replayFromImports` constructs a base environment from imported module artifacts and rechecks the selected module's new declarations. `replayFromFresh` imports the target artifact and replays its constants into an empty checker environment. The latter broadens logical replay coverage; both still use module loading, in-memory representations, runtime memory management, I/O, and compiled Lean execution. This audit did not compute the exact transitive axiom set for a built checker theorem or prove these wrappers correct.

Basis: **source**, `Verify/Axioms.lean`; `Main.lean`; `Replay.lean`, `replayFromImports`, `replayFromFresh`; **derived** endpoint distinction.

### MetaRocq checks an encoded program under explicit logical premises

`PCUICSafeChecker.typecheck_program` checks the encoded global environment and infers the top-level term's type. Its result carries an abstract-environment relationship, well-formedness, and a PCUIC inference judgment. The Boolean specification `check_wf_env_bool_spec` separately states that a successful Boolean type check yields the corresponding typing judgment for every related concrete environment.

The checker is parameterized by checker/normalizing flags and an abstract environment implementation. Its program entry point takes normalization evidence for the relevant environments. `PCUICSN.NormalizationIn` expresses well-foundedness of reduction for well-typed terms; the ordinary universe-checking flag record is not by itself a proof of normalization. The plugin's `infer_template_program` translates the encoded Template program and calls the PCUIC checker, again with these premises.

Basis: **source**, `safechecker/theories/PCUICSafeChecker.v`, `check_wf_env_bool_spec`, `typecheck_program`; `pcuic/theories/PCUICSN.v`, `normalizing_flags`, `NormalizationIn`, `Normalization`; `SafeTemplateChecker.v`, `trans_program`, `infer_template_program`.

### The inspected extraction unit assumes a constant-true guard implementation is correct

`PCUICWfEnvImpl.abstract_guard_impl` requires a Boolean guard function and a proof relating its result to the declarative guarding predicate. The same file defines `fake_guard_impl` to return `true` for every input. `safechecker-plugin/theories/Extraction.v` introduces `fake_abstract_guard_impl_properties` as an axiom asserting that this function agrees with declarative guarding, uses it to instantiate the abstract implementation, and extracts an entry point using that instance.

This is direct evidence of an explicit assumption in this extraction configuration. It is not a proof that the guard check is implemented faithfully, and it must not disappear from trust accounting. This report did not audit a complete built plugin, alternate guard instance, reifier, or external caller precondition; it consequently makes no blanket unsoundness classification for all MetaRocq deployments.

Basis: **source**, `PCUICWfEnvImpl.v`, lines 10–16; `safechecker-plugin/theories/Extraction.v`, the axiom, local instance, and extracted entry point.

### Formal translation and erasure do not cover arbitrary reification or binary execution

`template_to_pcuic_typing` preserves typing from the formal Template judgment in a well-formed environment to the translated PCUIC judgment. Its subject is the formal AST translation, not the OCaml process that quotes a live Rocq environment into those ASTs.

`ErasureCorrectness.erases_correct` relates a well-typed PCUIC term and its erased term: given the erasure and dependency relations and a source evaluation to a value, an erased evaluation to a related value exists. Its direction, well-typedness, global dependency and evaluation premises matter. It is not a complete printing/parser/runtime/compiler theorem for an arbitrary deployed checker binary. CertiRocq's later compilation path was not audited in this wave.

Basis: **source**, `template-pcuic/theories/TemplateToPCUICCorrectness.v`, `template_to_pcuic_typing`; `erasure/theories/ErasureCorrectness.v`, `erases_correct`; **derived** boundary on the theorem endpoints.

### Candle makes the accepted output channel part of its theorem

At the inspected CakeML source, `semantics_thm` constrains events from terminating or diverging execution of the Candle prefix followed by a program. Its premises include suitable evaluation state, syntax checks, safe declarations, initially empty I/O events, and absence of `Fail`. `events_of_semantics` exposes the event-level consequence. `holSoundness.proves_sound` separately connects derivability to semantic entailment under its set-theory premise.

`print_thmScript.sml` defines encodings of a theorem and its logical context and proves inverse laws for the emitted representations. This provides a concrete acceptance interface: a theorem result includes its context and a defined serialization, rather than a user-customized pretty-printed string. The inspected theorem concerns its formal event predicate; this report did not rebuild or audit the complete FFI implementation.

Basis: **source**, `candle/prover/candle_prover_semanticsScript.sml`, `semantics_thm`, `events_of_semantics`; `candle/standard/semantics/holSoundnessScript.sml`, `proves_sound`; `candle/standard/ml_kernel/print_thmScript.sml`, encoding and inverse theorems.

### Candle's published machine theorem retains installation and resource premises

The extended Candle paper's Section 5 gives an in-logic compiler-result theorem and applies compiler correctness to the REPL. Its machine-state premise requires the generated code to be installed with the expected entry point; permitted behaviors include early resource-limit exits. The reported guarantee concerns exported facts on the protected theorem channel, not arbitrary strings printed by users. This is a stronger executable endpoint than a checker-function theorem, while retaining formal machine/environment and HOL4 assurance premises. The exact compiled proof object, machine-code bytes, and publication artifact were not acquired or rebuilt here. [Primary paper, Section 5](https://doi.org/10.1007/s10817-025-09743-8).

Basis: primary publication **documentation** of the proved theorem; source-to-binary applicability for this wave remains **not examined**.

## Boundaries

- **Not established:** complete, assumption-free Lean4Lean environment verification. The admitted inductive branch and operation assumptions are recorded explicitly.
- **Not examined:** full Lean4Lean metatheory consistency, exact built theorem axiom closures, parser/export formats, executable behavior equivalence, compatibility with Anneal 4.31, or checker performance.
- **Not established:** correctness of the MetaRocq plugin's live reifier, the constant-true extraction guard, every alternate guard configuration, extracted OCaml compilation/runtime, or exact transitive theorem assumptions. Normalization remains an explicit parameter of the inspected entry points.
- **Not examined:** CertiRocq/CertiCoq compilation, full MetaRocq typed-extraction and foreign-interface theorem chains, or a data-only deployment recipe proven to preserve the formal program.
- **Not examined:** a complete CakeML frontend/backend/bootstrapping audit, Candle's compiled artifact or FFI implementation, or correspondence between this current CakeML pin and the paper artifact.
- **Not established:** cross-logic transfer to a Lean theorem about Rust, or end-to-end Anneal acceptance. Each import requires interpretation, exact subject identity, and assumption accounting.

## Evidence

`support/source-index.json` records the directly inspected immutable source files and hashes. Important theorem/implementation endpoints are:

- [Lean4Lean checking proofs](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/TypeChecker.lean): `checkType.WF`, `inferType.WF'`, `isDefEq.WF`.
- [Lean4Lean theorem declaration check](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Environment/Checker.lean#L147): `checkTheorem`, `checkTheorem.WF`.
- [Lean4Lean declaration coverage](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Environment.lean#L113): quotient premises; aggregate `addDecl.WF`, lines 220–235.
- [Lean4Lean operation assumptions](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Axioms.lean): persistent collections, expression operations, level-normalizer equations; [replay wrapper](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Replay.lean#L284); [toolchain](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/lean-toolchain).
- [MetaRocq checker entry](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/safechecker/theories/PCUICSafeChecker.v#L2448): Boolean specification and `typecheck_program`; [normalization premise](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/pcuic/theories/PCUICSN.v#L12).
- [MetaRocq guard interface](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/safechecker/theories/PCUICWfEnvImpl.v#L10); [extraction assumption and entry point](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/safechecker-plugin/theories/Extraction.v#L31); [Template checker wrapper](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/safechecker-plugin/theories/SafeTemplateChecker.v#L22).
- [Template-to-PCUIC theorem](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/template-pcuic/theories/TemplateToPCUICCorrectness.v#L3328); [erasure theorem](https://github.com/MetaRocq/metarocq/blob/c8cd46054518193103c3bb33aa6e15c7f489e72c/erasure/theories/ErasureCorrectness.v#L51).
- [Candle source event theorem](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/candle/prover/candle_prover_semanticsScript.sml#L423); [HOL semantic soundness](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/candle/standard/semantics/holSoundnessScript.sml#L313); [theorem/context encoding](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/candle/standard/ml_kernel/print_thmScript.sml).
- [Candle extended paper](https://doi.org/10.1007/s10817-025-09743-8), Section 5, Theorems 5–6, supplies the published compiler and machine-state endpoint account separately from the inspected source.

No fresh tool execution or proof rebuild supports this package. Mathematical statements were inspected directly in source; acceptance by their development's prover was not independently re-executed.

## Revalidation

Read the actual aggregate theorem and its transitive assumptions before relying on a project's verification description. For Lean4Lean, inspect whether the inductive declaration case is now proved, whether quotient initialization is constructive, and whether upstream-operation equations remain axioms; then build the selected proof targets under their own pin and query their axiom closure.

For MetaRocq, instantiate normalization and a genuinely justified guard implementation, trace the live reifier and extraction directives to the executable entry point, and check the exact theorem assumptions. A general checker theorem cannot certify a concrete configuration that substitutes an assumed guard.

For Candle, recover the exact compiled proof and code identity, check machine-state/resource/FFI premises, and test that only the defined theorem channel is consumed as authoritative output. A normal stdout line is not the theorem-channel guarantee.

*Authored by an AI agent acting on joshlf's behalf.*
