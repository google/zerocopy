# Aeneas extrinsic termination facilities at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, there are two materially different ways to supply termination evidence around the Lean translation, and Anneal should not conflate them.

First, Aeneas has an opt-in translation mode, `-decreases-clauses`, intended to generate `termination_by` and `decreasing_by` clauses for recursive translated functions and translated loop helpers. Aeneas derives stable helper names, emits a termination-measure template, and emits a tactic-template hook for the decrease proof. The substantive measure and proof remain user responsibilities. The generated default proof template expands to `sorry`; the Lean backend rejects `-use-fuel`; and the driver rejects decreases-clause mode for mutually recursive source groups.

At the exact Aeneas and Lean revisions selected by Anneal, the translation-time Lean mode has a stronger problem. Aeneas emits `termination_by ...`, then `decreasing_by ...`, but its ordinary recursive-definition printer still appends `partial_fixpoint`. Lean v4.30.0-rc2 parses a recursive definition's termination suffix as one choice among `termination_by`, `termination_by?`, or `partial_fixpoint` (plus an optional trailing `decreasing_by`). It does not admit `termination_by ... decreasing_by ... partial_fixpoint` as one suffix. The pinned Aeneas tree contains no checked-in Lean decreases-clause output fixture, and no fresh Aeneas/Lean invocation was run for this report. The source establishes a grammar incompatibility; it does not establish the exact parser diagnostic that an executed probe would print.

Second, termination can be proved at the proof layer while the translated program remains partial. Aeneas's normal WP/specification interface rejects `Result.div`, so a theorem proving `f x ⦃ y => P y ⦄` establishes successful return rather than divergence for the covered invocation. User-written recursive specification theorems can use ordinary Lean `termination_by` / `decreasing_by`. For fixed-point loop semantics, Aeneas provides `loop.spec` and `loop.spec_decr_nat`, which require a well-founded measure that decreases on every continuation step. These proof-time facilities do not rewrite the translated function into a total definition; they prove termination only where their obligations are discharged.

For Anneal at this pin, the proof-time facilities are the usable source-grounded termination interface. The Aeneas translation-time `-decreases-clauses` mode should not be treated as operationally available for Lean until an exact-pin execution either demonstrates a repaired generation path or the source-level suffix conflict is corrected and revalidated.

## Applicability

This report applies to:

- Aeneas release `nightly-2026.06.03`, repository revision `ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- Aeneas's Lean backend and its termination-related command-line configuration;
- Lean `v4.30.0-rc2` at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the Lean revision selected by the Anneal toolchain.

Here, **extrinsic termination evidence** means evidence supplied outside the translated Rust operational body. It includes both:

1. generator-level termination measures/proofs that Aeneas intends to splice into generated recursive definitions; and
2. proof-level well-founded arguments used in user-written theorems about otherwise partial translated computations.

Those two mechanisms have different trust, syntax, and usability boundaries.

The default `partial_fixpoint` semantics, Aeneas's `Result.div` domain, and ordinary recursion classification are covered by neighboring corpus reports. This report uses those facts only where they are necessary to explain what the extrinsic facilities prove.

No fresh Aeneas generation or Lean elaboration was performed for this report.

## Findings

### `-decreases-clauses` is an explicit opt-in mode

Aeneas exposes `-decreases-clauses` with the description “Use decreases clauses/termination measures for the recursive definitions.” The configuration flag is off by default.

The option is distinct from `-use-fuel`. The command-line checker rejects enabling both at once. For the Lean backend, `-use-fuel` is rejected outright.

The decreases option therefore represents Aeneas's only generator-level attempt, at this pin, to turn a recursive Lean translation into a definition justified by an explicit termination measure rather than merely by the default partial fixed-point semantics.

Basis: Aeneas **source** in `src/Main.ml` and `src/Config.ml`.

### Aeneas marks recursive functions and translated loops for generated termination evidence

When extraction starts, Aeneas computes a set of declarations that should receive decreases material.

The set includes:

- a translated forward function whose effect metadata says it is recursive; and
- every translated loop function in that function translation.

When `-decreases-clauses` is enabled, names for a termination measure and, on Lean, a decreases proof are registered for those declarations.

For Lean, the generated names use the suffixes:

- `_terminates` for the termination measure; and
- `_decreases` for the proof/tactic hook.

The extraction path also deliberately shares a forward function's termination argument with any generated backward functions. Its source comment explains the intent: termination should depend on forward inputs, and additional backward state is ignored for this purpose.

Basis: Aeneas **source** in `src/Translate.ml`, `src/extract/Extract.ml`, and `src/extract/ExtractBase.ml`.

### The generated Lean template is scaffolding, not a completed termination proof

For Lean, `extract_template_lean_termination_and_decreasing` emits two kinds of template material.

The first is a termination-measure definition. Its default body is mechanically derived from the translated function inputs: a single input is returned directly; multiple inputs are bundled as a tuple. This gives the user a type-correct starting point, not a proof that the chosen measure decreases.

The second is a syntax/macro hook for the `decreasing_by` proof. The generated macro body expands to `sorry`.

This distinction is important for a verification corpus. Enabling template generation does not supply a trusted termination proof. A no-`sorry` proof workflow must replace the scaffold with a real measure/proof.

In split-file mode Aeneas writes the template into a `Clauses.Template` module, while the generated function module imports `Clauses.Clauses`. The intended workflow is therefore to provide the actual clauses module separately rather than silently treating the template as authoritative proof material.

Basis: Aeneas **source** in `src/extract/Extract.ml` and `src/Translate.ml`.

### Generated Lean definitions are intended to receive both `termination_by` and `decreasing_by`

When a translated definition is marked as having a decreases clause, the Lean extractor emits:

1. a `termination_by` clause that calls the generated `_terminates` measure on the function's parameters; and
2. a `decreasing_by` clause that invokes the generated `_decreases` tactic hook on those parameters.

This is the correct general shape for ordinary Lean well-founded recursion: the measure states what decreases, and the tactic discharges each recursive-call decrease obligation.

The source is explicit that the generated helper bodies are supplied by the user. Aeneas is wiring a proof obligation into the generated definition, not automatically deriving a semantic termination theorem from Rust source.

Basis: Aeneas **source** in `src/extract/Extract.ml`.

### The pinned generator also appends `partial_fixpoint`, which conflicts with the pinned Lean grammar

Aeneas's recursive-definition qualifier is independent of the decreases-clause option. For the Lean backend, every recursive declaration kind maps to the post-qualifier `partial_fixpoint`.

The extractor emits the optional `termination_by` and `decreasing_by` clauses first. After those clauses, it unconditionally emits the recursive declaration's post-qualifier, so a recursive definition in decreases mode is intended to end with both the well-founded-recursion clauses and `partial_fixpoint`.

At Lean v4.30.0-rc2, `Termination.suffix` does not permit that combination. Its grammar accepts:

- an optional single choice among `termination_by?`, `termination_by`, `partial_fixpoint`, `coinductive_fixpoint`, or `inductive_fixpoint`; followed by
- an optional `decreasing_by`.

Therefore the Aeneas sequence `termination_by ... decreasing_by ... partial_fixpoint` is not a valid single Lean termination suffix at this pin.

This conclusion is stronger than “the mode is undocumented”: it follows directly from the pinned producer and consumer grammars. However, no fresh generated specimen was parsed in this investigation, so the report does not claim an observed error string, parser location, or later recovery behavior.

Basis: Aeneas **source** in `src/extract/Extract.ml` and `src/extract/ExtractBase.ml`; Lean **source/documentation** in `src/Lean/Parser/Term.lean`.

### There is no checked-in Lean decreases-clause golden specimen at the selected Aeneas revision

The exact pinned Aeneas tree contains checked-in decreases-clause templates and concrete clauses for the F* backend, including arrays, hashmap, and rename tests.

The same tree contains many checked-in Lean translation artifacts, including recursive and loop-heavy examples, but no checked-in Lean `Clauses` / decreases-clause generated artifact.

This absence does not prove that the Lean mode was never executed elsewhere. It does remove an otherwise useful preserved execution artifact that could have contradicted or contextualized the source-level syntax problem.

Basis: exact pinned repository **tree inspection**.

### Lean fuel is not an alternate termination mechanism for this backend

Aeneas has a general `-use-fuel` option described as using a fuel parameter to control divergence. The Lean backend explicitly rejects that option.

Consequently, at this pin an Anneal user cannot avoid the translation-time decreases-mode problem by selecting Aeneas's fuel translation on Lean. The relevant Lean choices are the default partial semantics and proof-time termination arguments, plus the source-intended but currently unvalidated decreases-clause generator path.

Basis: Aeneas **source** in `src/Main.ml`, `src/Config.ml`, and the backend built-in tables.

### Mutually recursive groups are explicitly unsupported by Lean decreases mode

Before translation, the Aeneas driver checks whether the input contains a mutually recursive function group. If the backend is Lean and decreases clauses are enabled, such a group is rejected with an error stating that the Lean backend does not support `decreasing_by` / `termination_by` clauses with mutually recursive definitions.

This is a hard applicability limit independent of the suffix incompatibility above.

Basis: Aeneas **source** in `src/Main.ml`.

### Proof-time recursive specifications use ordinary Lean termination

The default translated program can remain a `partial_fixpoint` while a theorem about it is proved by ordinary terminating recursion.

Aeneas's own documentation and checked-in proof style use `termination_by` and `decreasing_by` on recursive specification theorems. This termination argument belongs to the theorem definition in Lean. It does not rewrite the translated Rust function.

That distinction matters semantically because Aeneas's WP `spec` rejects `Result.div`. Proving a specification for a recursive call therefore establishes that the covered invocation reaches `Result.ok` satisfying the postcondition; the theorem's well-founded recursion supplies the proof-side justification needed to make that argument recursively.

A proof for selected inputs can thus rule out modeled divergence without asserting that the translated function is globally total.

Basis: Aeneas **source/documentation** in `backends/lean/Aeneas/Std/WP.lean`, `documentation/aeneas-overview.md`, and `documentation/proof-strategies.md`; Lean **source/documentation** for `termination_by` / `decreasing_by`.

### Fixed-point loops have explicit well-founded specification lemmas

Aeneas's Lean WP library provides a theorem `loop.spec` parameterized by:

- a measure from loop state to an arbitrary type with a `WellFoundedRelation`;
- an invariant;
- a postcondition; and
- a body proof showing that every continuation state preserves the invariant and strictly decreases the measure.

It also provides `loop.spec_decr_nat`, specialized to a `Nat` measure and `<`.

These are extrinsic termination facilities in the proof layer. The loop's semantic definition may remain a fixed point, but a successful application of these lemmas proves that the in-scope execution satisfies the postcondition through a well-founded descent argument.

The proof obligation is explicit: every `.cont x'` branch must establish a smaller measure. The theorem does not infer that property from the Rust loop automatically.

Basis: Aeneas **source** in `backends/lean/Aeneas/Std/WP.lean`.

### Translation-time and proof-time termination answer different questions

The two facilities should be kept separate in Anneal's mental model.

Translation-time decreases mode is intended to make the generated recursive program definition itself acceptable as ordinary well-founded Lean recursion, assuming user-supplied measure/proof helpers. At the selected revision that path has an unresolved source-level syntax incompatibility and no preserved Lean decreases-mode fixture.

Proof-time termination leaves the translated semantics partial and proves that a particular specification theorem excludes divergence under its preconditions. This path composes naturally with Aeneas's existing `Result.div` / `WP.spec` semantics.

A successful proof-time theorem therefore establishes termination for the theorem's covered inputs; it does not retroactively change the translated function's semantic domain or prove termination for all callers.

Basis: **derived** from the pinned generator, Lean termination syntax, and Aeneas WP definitions.

## Boundaries

- No fresh Aeneas invocation, generated Lean parsing, Lake build, or Lean elaboration was run.
- The translation-time syntax incompatibility is a source-level conclusion. This report does not assert a specific runtime diagnostic.
- The repository-tree absence of a checked-in Lean decreases-clause fixture is not evidence that nobody has ever run the mode.
- The F* decreases-clause backend is outside scope except where its checked-in artifacts help establish that decreases templates are part of the repository's test practice.
- The exact user experience of repairing the generated Lean output is untested. In particular, this report does not claim that removing only the trailing `partial_fixpoint` is sufficient for every generated recursive function.
- The generated `_decreases` template expands to `sorry`; whether a project permits such assumptions is a trust-policy question. Anneal's no-assumption guarantees must be evaluated separately.
- Mutually recursive definitions are explicitly rejected in Lean decreases mode; this report does not propose a workaround.
- Aeneas's fuel mechanism is unavailable for Lean at this pin. Its behavior on other backends is outside scope.
- Proof-time `termination_by` / `decreasing_by` establishes termination of the Lean theorem's recursive proof, not semantic preservation from Rust to Lean.
- `loop.spec` and `loop.spec_decr_nat` prove only what their invariant, measure, and body obligations justify.
- Adjacent Aeneas or Lean revisions may change either the generator or the termination grammar.

## Evidence

Primary Aeneas subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

Pinned Aeneas source and documentation:

- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc` — `-decreases-clauses`, `-use-fuel`, template controls, incompatibility checks, Lean fuel rejection, and mutually recursive decreases-mode rejection.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355` — termination configuration and the explicit statement that termination-measure/proof bodies are user supplied.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379` — recursive/loop selection, helper generation, split-file clauses modules, and propagation of decreases configuration into function extraction.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8` — Lean termination-measure template, `sorry`-based decreases macro template, and emitted `termination_by` / `decreasing_by` clauses.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9` — `_terminates` / `_decreases` naming and unconditional `partial_fixpoint` post-qualifier for recursive Lean declarations.
- `backends/lean/Aeneas/Std/WP.lean`, blob `018c456bcab5374de0b09b17eda0df1a48e2288b` — `spec` rejects `div`; `loop.spec` and `loop.spec_decr_nat` expose well-founded termination obligations.
- `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756` — repository proof workflow for recursive specifications and loop measures.
- `documentation/proof-strategies.md`, blob `2b10ed04a1594d6b8a95a80c742af10885974143` — recursive specification and loop termination proof patterns.
- `documentation/tips-and-tricks.md`, blob `c5d891ed25f689f2fe42578efdedc428bdecfe5e` — direct-recursion and fixed-point-loop proof guidance.
- `tests/README.md`, blob `5aa96fab26146514d0ecb2e26fcc40a5a45c94d9` — test-runner decreases configuration examples.

Exact pinned tree inspection also found F* `Clauses` artifacts but no checked-in Lean `Clauses` artifact.

Primary Lean subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Lean/Parser/Term.lean`, blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559` — contracts and grammar for `termination_by`, `partial_fixpoint`, `decreasing_by`, and the combined `Termination.suffix`.

No evidence above is fresh **execution**.

## Revalidation

For another Aeneas or Lean revision:

1. Recheck the Aeneas command-line contract for `-decreases-clauses`, `-use-fuel`, and template generation.
2. Recompute how Aeneas identifies recursive forward functions and translated loop helpers.
3. Recheck generation of `_terminates` and `_decreases` helpers, including whether the template still introduces `sorry`.
4. Recheck `extract_fun_decl_gen` and `fun_decl_kind_to_post_qualif` together. The key question is whether a decreases-mode recursive definition still receives `partial_fixpoint`.
5. Recheck Lean's `Termination.suffix` grammar and elaboration contract.
6. Recheck the mutually recursive restriction and Lean fuel restriction.
7. Recheck `WP.spec`, `loop.spec`, and `loop.spec_decr_nat`.

On an execution-capable surface, preserve an exact-pin probe matrix:

- generate one singly recursive Rust function with `-backend lean -decreases-clauses`;
- repeat with split files and preserve the generated `Clauses.Template` and imported clauses-module names;
- replace template holes with explicit measure/proof definitions and elaborate the generated project;
- test a mutually recursive source group and preserve the expected rejection;
- invoke Lean with `-use-fuel` through Aeneas and preserve the expected backend rejection;
- under default translation, prove a recursive WP theorem using `termination_by` / `decreasing_by`;
- prove a fixed-point loop theorem with `loop.spec_decr_nat`.

Preserve complete commands, stdout/stderr, generated source, tool revisions, and file hashes.

The first probe should specifically determine the exact runtime manifestation of the source-level suffix conflict. If the generated source no longer contains both well-founded clauses and `partial_fixpoint`, this report has become stale and should be revised before publication.
