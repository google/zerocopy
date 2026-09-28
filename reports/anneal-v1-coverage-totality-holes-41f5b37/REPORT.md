# Anneal V1 coverage and annotation-totality holes at `41f5b37`

## Summary

Retained Anneal V1 at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` verifies an **annotation-selected theorem domain**. It does not establish that every unsafe operation, unsafe function, or intended proof obligation in the selected Cargo targets is covered.

The key boundary occurs before Charon. Anneal source-scans for recognized `anneal` doc blocks, constructs one or more `start_from` roots from the items carrying those blocks, and passes those roots to Charon. Charon can recursively pull in unannotated semantic dependencies of an annotated root, so “unannotated” does **not** mean “necessarily absent from LLBC.” But Anneal does not create a user specification or proof obligation merely because a callee becomes reachable in Charon. In particular, only a function carrying an `unsafe(axiom)` Anneal block is deliberately marked opaque by Anneal's leaf-modeling path.

There is no retained V1 enforcement pass on this control path that inventories the selected crate's unsafe surface and checks annotation totality. The historical design document confirms the gap directly: it lists a future “strict mode” that would fail verification when an unsafe block lacks an Anneal annotation.

The most important fail-open behavior is syntactic. Once the parser recognizes the `anneal` token, malformed attributes and malformed clause syntax are errors. But if the identifying `anneal` token itself is absent or misspelled, the doc block is treated as unrelated documentation and silently ignored. If that removes the last recognized annotation, `cargo anneal verify` logs “Nothing to verify.” and returns success before validation, Charon, Aeneas, or Lean runs.

This makes a successful retained-V1 invocation a claim about the recognized annotation roots that actually entered the pipeline, not a crate-wide completeness certificate for unsafe Rust.

## Applicability

This report applies to the retained Anneal V1 implementation under `anneal/v1` at:

- repository: `google/zerocopy`;
- revision: `41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

It addresses the #3720 inventory item:

> **V1 coverage/totality holes** — unannotated unsafe callees, missing annotations, typo/fail-open risks.

The report is historical. Current Anneal V2 design on `main` is authoritative for new architecture and policy. This report preserves V1 behavior that is easy to accidentally rediscover or overgeneralize from.

## Findings

### Verification begins with recognized annotations, not with an unsafe-code inventory

`prepare_and_run` first resolves Cargo targets and then calls `scanner::scan_workspace`. The scanner describes its job as finding Anneal entry points and collects only items for which the parser returns an Anneal block. Each collected item contributes both an `items` entry and a Charon `start_from` root.

When scanner results are assembled into `AnnealArtifact`s, a target without collected entry points is omitted. Nothing in this path first enumerates unsafe functions, unsafe blocks, raw-pointer operations, or the selected crate's full Rust safety surface and then asks whether each element has an annotation.

This is an **opt-in root model**: recognized annotations select what Anneal attempts to verify.

Basis: **source** — `anneal/v1/src/main.rs`, `scanner.rs`, and `parse/attr.rs`.

### Zero recognized annotations is a successful no-op

The top-level pipeline makes the completeness consequence explicit. Immediately after scanning:

```text
if packages.is_empty() {
    warn!("No Anneal annotations ... found ... Nothing to verify.");
    return Ok(None);
}
```

That return happens before `validate_artifacts`, `run_charon`, `run_aeneas`, and the command-specific Lean work.

Therefore the absence of recognized annotations is not a verification failure. The command succeeds after a warning. If a developer expected an unsafe function to be covered but its annotation was absent or not recognized, V1 has no independent totality check at this point that converts the omission into an error.

Basis: **source** — `anneal/v1/src/main.rs`.

### An annotated root brings semantic dependencies into Charon, but that is not the same as annotating them

Anneal passes the scanner-derived roots to Charon using `--start-from`. The current reference corpus separately establishes Charon's behavior at the pinned 0.1.210 revision: translation begins from configured semantic roots and recursively enqueues definitions reached from them.

Consequently, an unannotated callee can still appear in LLBC and downstream Aeneas output when it is semantically reachable from an annotated root. This is important because the opposite simplification—“unannotated means untranslated”—would be wrong.

The distinction is instead:

- an **annotated root** receives Anneal's explicit user-level specification/proof treatment;
- an **unannotated reachable dependency** can be translated because Charon reaches it, but it does not acquire an Anneal annotation merely by being reachable;
- an **unannotated item outside the semantic closure** of every selected root is outside that verification run's extracted theorem domain.

Thus transitive translation improves operational coverage without establishing annotation totality.

Basis: **source** — V1 `scanner.rs` and `charon.rs`; current native **reference report** `charon-dependency-and-source-coverage-nightly-2026-06-03`.

### Unannotated unsafe callees are not automatically converted into Anneal leaf axioms

The V1 leaf mechanism is explicit. A function annotated `unsafe(axiom)` is recognized by the Anneal parser, collected by the scanner, passed to Charon with `--opaque`, and represented by generated Anneal Lean as an axiom rather than a theorem proved from the Aeneas body.

That special handling is driven by the annotation. The retained V1 control path does not independently discover every unsafe callee reachable from an annotated root and synthesize the same Anneal contract for it.

An unannotated unsafe callee can therefore have one of several downstream outcomes depending on the exact Rust construct and the pinned Charon/Aeneas support boundary: it may translate, it may become opaque through upstream semantics, or translation may fail. What Anneal V1 does **not** provide merely from reachability is an explicit user-authored unsafe contract plus a proof/axiom decision attached to that callee.

Accordingly, success of an annotated caller proof must not be promoted into the stronger statement “every reachable unsafe callee had its Rust safety contract explicitly modeled and checked by Anneal.”

Basis: **source** — `anneal/v1/src/charon.rs`, `generate.rs`, `parse/attr.rs`; **derived** boundary from the annotation-driven control flow.

### Retained V1 has no mandatory unsafe-annotation mode

The historical design document gives unusually direct negative evidence. Under future work it proposes:

> a “strict mode” that fails verification if any unsafe block lacks an Anneal annotation.

That proposal is not presented as the behavior of the retained implementation. Combined with the scanner and top-level control flow, it confirms that ordinary V1 verification did not make unsafe-annotation completeness a success criterion.

This distinction matters for interpreting V1's stated ambition. The design prose describes machine-enforced verification of unsafe code, but the implemented verification domain is still chosen by annotations. The tool can prove obligations inside that selected domain without proving that the domain is complete.

Basis: **historical design documentation** + **source**.

### Typos split into fail-closed and fail-open classes

The parser is strict **after** it recognizes the `anneal` marker.

`parse_anneal_info_string` searches comma-separated info-string tokens for the exact token `anneal`. When it finds that token, unsupported attributes are errors. For example, malformed `unsafe...` forms produce a diagnostic suggesting `unsafe(axiom)`, and arbitrary attributes after `anneal` are rejected. The checked-in parser tests exercise these cases.

The body parser is similarly strict about the recognized annotation grammar. Invalid indentation or unexpected top-level text produces a diagnostic that can explicitly ask whether a keyword was misspelled.

But the identifying marker itself is different. If the info string has no exact `anneal` token—because it was omitted or misspelled—`parse_anneal_info_string` returns `Ok(None)`. `parse_anneal_block_common` then treats the code block as unrelated documentation and continues scanning. It does not diagnose “this looked like an intended Anneal block.”

That yields the important matrix:

- `anneal, unsafe` → error;
- `anneal, unknown` → error;
- recognized `anneal` block with malformed clause structure → error;
- `aneal` or another misspelling of the identifying token → ignored as non-Anneal documentation.

The last case is fail-open with respect to the author's intended coverage. If it removes the final recognized annotation, the top-level successful no-op behavior compounds the problem.

Basis: **source** + checked-in **tests** — `anneal/v1/src/parse/attr.rs` and `main.rs`.

### Validation cannot reject an annotation that never entered the artifact set

`validate_artifacts` iterates the `AnnealArtifact`s produced by the scanner. Its checks therefore operate only on recognized annotations.

This function can reject specific problems inside selected items—for example, disallowed `isValid` use unless an explicit unsound flag is supplied, reserved-name collisions, or some proof-shape errors. Other missing proof material can intentionally fall through to Lean's `autoParam` machinery, and `--allow-sorry` changes proof-completeness behavior further.

Those rules are downstream of root selection. They cannot establish annotation totality because a missing or unrecognized annotation never creates the `ParsedItem` that the validator would inspect.

Basis: **source** — `anneal/v1/src/validate.rs`.

### “Verification succeeded” is weaker than “the crate's unsafe surface is covered”

The retained implementation therefore supports several distinct success claims that must not be conflated:

1. the selected Cargo target compiled far enough for the invoked toolchain;
2. the recognized annotation roots were scanned and converted into Anneal artifacts;
3. Charon/Aeneas processed the semantic closure selected by those roots, subject to their own support and opacity semantics;
4. generated Lean obligations for the recognized Anneal items passed under the chosen flags and assumptions.

None of those steps independently proves that every unsafe function or unsafe operation the user intended to verify was represented by a recognized Anneal annotation.

For historical V1 results, annotation coverage is therefore part of the trusted workflow/process boundary. A completeness claim needs separate evidence that the intended unsafe surface was actually enumerated and selected.

Basis: **derived** from the retained source control flow and documented future strict-mode gap.

## Adjacent but separate V1 gaps

Several nearby #3720 items should remain separate rather than being folded into this report:

- **V1 source scanner versus rustc** covers `cfg`, aliases, macros, modules, imports, local items, and source/compiler correspondence. The parser itself warns that some `cfg_attr(..., path = ...)` cases may cause annotations to be ignored. That is a source-correspondence problem beyond the simpler annotation-totality gap established here.
- **V1 `isValid` unsoundness** covers mutation-boundary and compound-type holes; retained source explicitly notes that unannotated code can violate those invariants.
- **V1 `isSafe` implementation/semantic gaps** covers unsafe-trait proof propagation and unsafe-impl enforcement.
- **V1 `unsafe(axiom)` semantics** covers what an accepted leaf axiom means, not whether every required leaf received one.
- **V1 generated-Lean ABI**, **lifetime erasure**, and **orthogonal progress/correctness** have distinct soundness or coupling questions.

Keeping these scopes separate avoids turning a concrete totality result into a general verdict on all V1 soundness mechanisms.

## Boundaries

- No fresh Anneal V1, Charon, Aeneas, Lean, or Cargo execution was performed. The report reconstructs behavior from the exact retained source, checked-in tests, historical V1 documentation, and current native reference reports.
- The report does not claim that every unannotated reachable callee is omitted from LLBC. Charon's semantic closure can include unannotated dependencies of annotated roots.
- The report does not claim that every reachable unsafe callee is accepted unsoundly. Exact behavior depends on Charon/Aeneas support, opacity, and failure handling. The narrower established fact is that Anneal does not automatically attach an explicit `unsafe(axiom)` contract to an unannotated callee.
- The report does not evaluate the completeness of V1 source scanning under `cfg`, macros, aliases, module-path indirection, generated code, or local items. Those belong to the separate scanner-versus-rustc inventory item.
- Missing proof blocks inside a recognized annotation are not treated as missing annotations. Their validation/`autoParam`/`--allow-sorry` behavior is a separate proof-completeness concern.
- Current V2 semantics and design are out of scope except that current `main` is the authority and this V1 report is historical evidence only.

## Evidence

**Retained V1 source — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.**

- `anneal/v1/src/main.rs` — top-level scan-first pipeline and successful early return when no packages/annotations are found.
- `anneal/v1/src/scanner.rs` — annotation-selected `AnnealArtifact` construction and `start_from` roots.
- `anneal/v1/src/charon.rs` — `--start-from` forwarding and annotation-driven `unsafe(axiom)` → `--opaque` handling.
- `anneal/v1/src/parse/attr.rs` — exact `anneal` token recognition, ignored unrelated blocks, malformed recognized attributes, and strict block grammar.
- `anneal/v1/src/validate.rs` — checks over already-collected items only.
- `anneal/v1/src/generate.rs` — generated Lean for collected items, including theorem versus axiom generation.
- `anneal/v1/src/resolve.rs` — adjacent retained note about unannotated code bypassing `isValid` invariant enforcement.

**Historical V1 documentation at the same revision.**

- `anneal/v1/docs/agent/01_philosophy_and_pipeline.md` — Charon is rooted at annotated functions and their transitive dependencies; unsafe leaf modeling uses `unsafe(axiom)`.
- `anneal/v1/docs/design/design.md` — architecture narrative plus future-work “strict mode” for mandatory unsafe documentation.

**Current native reference corpus.**

- `reports/charon-dependency-and-source-coverage-nightly-2026-06-03/REPORT.md` — custom `--start-from` narrows the Charon theorem domain while recursively including semantic dependencies.
- `CATALOG.json` at the observed reference revision — no dedicated V1 coverage/annotation-totality package was present when this candidate was prepared.

## Revalidation

For a newer retained V1 revision or a historical execution-capable reproduction, the cheapest discriminating probe is one small Cargo crate with five cases:

1. an annotated wrapper that calls an unannotated ordinary helper;
2. an annotated wrapper that reaches an unannotated unsafe leaf;
3. an unannotated unsafe function outside every annotated root's semantic closure;
4. an otherwise valid annotation whose info string misspells `anneal` as `aneal`;
5. an annotation with the correct `anneal` token but a malformed attribute such as `anneal, unsafe`.

Record:

- scanner-discovered items and `start_from` roots;
- the exact Charon command, especially `--start-from` and `--opaque`;
- whether each helper/leaf appears in LLBC and generated Aeneas Lean;
- generated Anneal specification files;
- diagnostics and process exit status.

The retained source predicts:

- recognized roots enter the pipeline and can pull in transitive semantic dependencies;
- unannotated code outside the selected closure is not part of the run;
- an unannotated unsafe callee is not automatically given Anneal's `unsafe(axiom)` treatment;
- a misspelled `anneal` marker is ignored rather than diagnosed;
- if that leaves zero recognized annotations, verification warns and returns successfully;
- a malformed attribute after a correctly recognized `anneal` marker fails parsing.

Running this fixture would validate the concrete control-flow observations against a built historical binary. It would not by itself prove semantic preservation of Charon/Aeneas or completeness of V1's source scanner relative to rustc.
