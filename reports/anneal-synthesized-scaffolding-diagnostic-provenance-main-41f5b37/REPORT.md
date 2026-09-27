# Mapping synthesized Lean scaffolding failures to Rust constructs

## Summary

Current Anneal requires ordinary verification failures to connect back to the Rust program, but it has not selected a source-mapping architecture. Historical Anneal V1 demonstrates both a useful technique and the limit of the implementation that existed at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

V1 classifies generated-to-Rust mappings as `Source`, `Synthetic`, or `Keyword`. `Source` is reserved for Lean text copied from the user's Rust-hosted proof/specification text. `Synthetic` and `Keyword` are generator-chosen anchors for Lean text that does not literally exist in Rust. In the production generator, the main synthesized anchor is the generated specification theorem name: Anneal maps it to the Rust function identifier. A generated theorem's initial `by` can receive a `Keyword` mapping to the first user proof-context line or proof-case keyword. A separate diagnostic heuristic recognizes one Lean message, `declaration uses `sorry``, and can redirect a diagnostic from the synthetic theorem name to a later keyword mapping inside the same generated theorem.

That machinery is **not** a general source map for synthesized scaffolding. Most generator-owned Lean—the `Pre`/`Post` structure syntax, theorem arguments, calls into Aeneas specifications, `apply Anneal.wp_prove_orthogonal`, `rintro`, generated `rcases`, `exact`, missing-proof helpers such as `verify_user_bound`, and other structural glue—is emitted with plain `push_str` and has no source mapping. A Lean diagnostic that lands only on such text falls back to the generated Lean location unless it happens to trigger the special `sorry` redirect or overlap another mapped range.

The source also exposes a narrower implementation gap: although `render_theorem` can map a generated `axiom` keyword when `keyword_span` is present, the production `generate_function` path supplies `None` for that field for `FunctionBlockInner::Axiom`. At this revision, the intended axiom-keyword anchor is therefore not populated in ordinary generation.

The durable conclusion is negative but actionable. Neither the pinned upstream Charon/Aeneas/Lean chain nor historical Anneal V1 provides a complete automatic mapping from every synthesized Lean failure to the responsible Rust construct. Precise responsibility for generated scaffolding has to be carried explicitly by the generator as provenance. Item-level Aeneas comments can provide a coarse containing Rust declaration, but they cannot justify an exact Rust token for arbitrary generated syntax.

Basis: current Anneal **design authority**, historical V1 **implementation source and unit tests**, and existing pinned source-correspondence evidence. No fresh Anneal or Lean execution was performed.

## Applicability

The current authority boundary is `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

At this revision, `anneal/README.md` states that `anneal/` is the current redesign and `anneal/v1/` is historical. `anneal/DESIGN.md` requires the ordinary user experience to connect unsatisfied obligations to Rust, while deliberately leaving the source/model-correspondence mechanism and the source language/location of proofs undecided.

This report therefore answers two separate questions:

1. what provenance historical V1 actually attached to synthesized Lean; and
2. what that evidence says about the minimum information a future implementation needs if it wants Rust-oriented diagnostics for generated proof scaffolding.

It does not make V1's JSON sidecar, annotation syntax, or exact anchoring choices current architecture.

The existing reference package `end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2` already establishes the broader chain: Aeneas gives generated declarations item-level Rust identity/span comments, Lean diagnostics identify ranges in Lean documents, and V1 experimented with a finer sidecar. This report narrows that result to synthesized Anneal-owned scaffolding and inventories which generated ranges actually receive responsibility anchors at the pinned revision.

## Findings

### Generated scaffolding needs a different provenance claim from copied user proof text

`anneal/v1/src/generate.rs` defines three mapping kinds.

`Source` means a generated Lean range corresponds directly to user-authored text. V1 uses it when it copies proof/specification lines from Rust documentation comments into Lean.

`Synthetic` means Anneal generated the Lean text and intentionally associates it with a relevant Rust source span. The source comment gives the canonical example: a generated Lean theorem named `spec` is mapped to the Rust function identifier so a diagnostic on that theorem name can underline the function name in Rust.

`Keyword` is another anchor class for generated structural syntax. Its intended use is to associate generated syntax such as `by` or `axiom` with a structurally relevant location in the Rust-hosted annotation.

The distinction is semantically important. A `Synthetic` or `Keyword` mapping says "show this generated failure here"; it does not say those Rust bytes generated the target text by direct copying.

Basis: historical V1 **source** in `anneal/v1/src/generate.rs`.

### The theorem name is explicitly assigned to the Rust function identifier

Every generated function theorem goes through `render_theorem`. Immediately after emitting `theorem` or `axiom`, the renderer calls `push_mapped` for `ast.spec_name` with `ast.fn_span` and `MappingKind::Synthetic`.

`generate_function` obtains `fn_span` from the function signature's name span. For a free function that is the Rust function identifier; the equivalent mirrored signature name span is used for supported method/trait/foreign-function forms.

This is an explicit responsibility decision. An error whose range covers the generated theorem/specification name can be presented on the Rust function name even though the Lean theorem identifier is synthesized.

Basis: historical V1 **source** in `anneal/v1/src/generate.rs`.

### Most theorem scaffolding has no mapping entry

The same renderer emits the rest of the theorem signature and proof framework largely with plain buffer writes. Examples include:

- generated instance parameters and arguments;
- an optional generated `h_req : Pre ...` binder;
- the generated Aeneas/WP call and `Post` application;
- `apply Anneal.wp_prove_orthogonal`;
- generated progress-proof fallback text;
- `rintro` patterns and `h_returns`;
- generated `rcases h_req` destructuring;
- `exact` and generated record braces/field labels; and
- generated helper tactics used when user proof cases are missing or validity obligations are supplied automatically.

Those ranges do not call `push_mapped` merely because they are generated from information about a Rust function. A diagnostic confined to one of them has no general sidecar route to a Rust construct.

This is the central negative result for the inventory item. V1 had a mapping representation capable of synthetic anchors, but it did not annotate the full generated scaffold with responsibility metadata.

Basis: historical V1 **source** in `anneal/v1/src/generate.rs`.

### Generated `Pre` and `Post` structures mix mapped propositions with unmapped structure

The `Pre`/`Post` structure renderer demonstrates the same split at a finer scale. User-authored proposition lines are emitted with `push_spanned`, so Lean diagnostics inside copied proposition text can map directly back to those Rust annotation ranges.

The generated structure header, generated field names, punctuation, automatically appended tactic text, and surrounding layout are ordinary generated strings. They do not acquire a mapping simply because a user proposition appears nearby.

Therefore one generated declaration can contain both direct-source ranges and generator-owned unmapped ranges. A source mapper must use the exact diagnostic overlap rather than assigning the whole generated declaration to the nearest annotation line.

Basis: historical V1 **source** in `anneal/v1/src/generate.rs`.

### The generated theorem `by` may receive a structural anchor

When generating a proof theorem, V1 can map the generated `by` token with `MappingKind::Keyword`.

The production source chooses its Rust anchor as follows: if proof context exists, it uses the first proof-context line's span; otherwise it takes a proof case's keyword span. If neither exists, the `by` is emitted without a keyword mapping. A checked-in unit test explicitly asserts that an implicit/empty proof produces no `Keyword` mapping.

This is more limited than the renderer's surrounding comments might suggest. In the proof-context case the Rust anchor is the first content line rather than necessarily the literal `proof` keyword. The mapping remains useful for user presentation, but it should be described as a generator-selected structural anchor rather than a guaranteed keyword-to-keyword correspondence.

Basis: historical V1 **source and unit test** in `anneal/v1/src/generate.rs`.

### The ordinary axiom path does not populate the renderer's axiom-keyword mapping

`render_theorem` contains code that would map the generated Lean word `axiom` through `MappingKind::Keyword` if `ast.keyword_span` were present.

The production caller does not provide one for axioms. `FunctionBlockInner::Axiom` carries no span field, and `generate_function` selects `("axiom", None, None, None)` for the theorem kind/proof data/keyword span tuple. It then passes that `None` into `AstTheorem.keyword_span`.

At this pinned revision, ordinary axiom generation therefore cannot take the renderer's `Keyword` branch for the generated `axiom` token. The generated theorem name still receives its `Synthetic` mapping to the Rust function identifier, but the axiom keyword itself does not receive the intended structural mapping from this path.

This is a source-level implementation fact. No fresh execution was performed to demonstrate the resulting diagnostic presentation.

Basis: historical V1 **source** in `anneal/v1/src/parse/attr.rs` and `anneal/v1/src/generate.rs`.

### V1 has one targeted redirect for a synthetic diagnostic

`anneal/v1/src/aeneas.rs::resolve_mapping` recognizes one diagnostic family specially. If a Lean diagnostic message contains `declaration uses `sorry`` and its range overlaps a `Synthetic` mapping, V1 searches for a later `Keyword` mapping associated with the same Rust source file and before the next synthetic theorem mapping. If found, the diagnostic is redirected there.

The fence is important. The implementation does not globally pick any nearby keyword; it uses the next synthetic mapping as a boundary for the generated theorem region and also requires matching source-file identity.

Unit tests verify that the redirect does not cross source files and does not accidentally choose a different function's proof keyword when generated function order differs from Rust source order.

This is a concrete example of a safe-ish scaffolding heuristic: a recognized generated diagnostic is given a more helpful Rust anchor only inside an established local provenance region.

Basis: historical V1 **source and unit tests** in `anneal/v1/src/aeneas.rs`.

### The `sorry` redirect does not make unmapped scaffolding generally recoverable

The redirect begins only after a diagnostic has overlapped a `Synthetic` mapping. It does not search arbitrary generated text for a containing function and then redirect every error. A type error on an unmapped generated `apply`, binder, destructuring term, or auto-generated helper invocation therefore does not enter this path merely because it belongs to the same theorem.

When `resolve_mapping` finds no applicable mapping, it falls back to the Lean diagnostic's own file/range. `DiagnosticMapper::render_raw` likewise falls back when the resolved source path/range cannot be presented in the user workspace.

This conservative fallback is preferable to inventing a Rust blame site. It preserves the distinction between "Anneal knows which Rust source owns this generated text" and "Anneal only knows where Lean reported the failure."

Basis: historical V1 **source** in `anneal/v1/src/aeneas.rs` and `anneal/v1/src/diagnostics.rs`.

### Aeneas offers a coarse containing-item origin for some synthesized Lean

The pinned upstream chain gives another provenance layer. Aeneas retains Charon item metadata on translated declarations and emits Lean doc comments that identify the original Rust item and declaration span. Generated loop/termination helpers can also carry comments tied to the originating Rust function.

That information can answer "which Rust declaration did this generated Lean declaration come from?" It cannot determine a unique responsible Rust token for arbitrary synthesized value flow or helper syntax. The existing end-to-end source-correspondence report already establishes this item-level versus generated-range distinction.

For diagnostics on Anneal-owned synthesized code, item-level Aeneas provenance is therefore a useful fallback/context source but not a substitute for an explicit generated-range responsibility map.

Basis: existing current reference evidence plus pinned Aeneas **source**, as preserved by `end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2`.

### Responsibility has to be assigned when synthesized text is emitted

V1's successful mappings share one property: the generator knows both sides at emission time. For copied user text, it has the original line span and current generated byte offset. For the synthetic theorem name, it deliberately chooses the Rust function name as owner. For the proof `by`, it deliberately chooses a proof-related Rust span.

The unmapped scaffolding lacks that explicit ownership assignment. After Lean reports an error, a consumer can often infer a containing theorem, but it no longer has enough evidence to know whether the most helpful/accurate Rust owner should be the function declaration, a `requires` clause, an `ensures` clause, a proof section, a generated validity obligation, or Anneal itself.

A future implementation that wants precise Rust diagnostics for generated scaffolding therefore needs provenance that records **responsibility**, not just textual origin. That provenance can reuse an item-level owner for coarse cases and narrower obligation/source anchors where justified, but it should not be inferred by proximity after the fact.

Basis: **derived** from the V1 mapping taxonomy, its uncovered generated ranges, and current Anneal's Rust-oriented diagnostic requirement.

### Some generated failures should be classified as tool/scaffolding failures rather than blamed on user Rust

Current Anneal's design promise says missing evidence, unsupported semantics, and failed tooling must not silently acquire the meaning of verification success. The same discipline applies to diagnostics: if generated scaffolding is internally malformed or Anneal emitted an inconsistent theorem, choosing an arbitrary Rust span can misleadingly present an Anneal defect as a user program error.

V1's fallback to the generated Lean file is crude but epistemically safer than assigning an unsupported Rust location. A current implementation can improve the presentation—for example, associate the failure with the containing verification subject while labeling it as generated/internal—but the provenance record should preserve that it lacks a justified user-authored blame range.

This report does not define Anneal's final diagnostic taxonomy. It establishes why the mapping layer needs to retain the difference between user-source ownership, generated-obligation ownership, and tool-internal scaffolding.

Basis: current Anneal **design authority** plus **derived** diagnostic consequence.

## Minimal provenance model suggested by the evidence

The pinned evidence supports a small responsibility model without prescribing serialization:

1. **Direct source** — generated bytes copied from a specific Rust-hosted user proof/spec range.
2. **Construct owner** — generated bytes synthesized for a specific Rust construct, such as a verification theorem owned by a function identifier.
3. **Obligation owner** — generated bytes synthesized for a specific user-visible obligation or annotation clause, such as a particular `requires`/`ensures`/proof case.
4. **Generated/internal** — generated bytes whose failure can be associated only with a verification subject or generator stage, not a defensible Rust byte range.

Historical `Source`, `Synthetic`, and `Keyword` mappings partially instantiate the first three classes. The unmapped scaffold demonstrates the need for the fourth.

This taxonomy is **derived**. It is not a current Anneal API decision.

## Boundaries

- Current Anneal has not chosen the final annotation language, proof placement, or source-map architecture. V1 is historical evidence only.
- No fresh Anneal, Lean, Aeneas, Charon, or Lake execution was performed.
- The report does not claim every possible V1 generated string is enumerated by name. It establishes the mapping mechanism exhaustively enough to show that only `push_spanned` and `push_mapped` produce sidecar entries, and that the production generator uses `push_mapped` only for the theorem name and limited theorem/axiom keyword paths.
- The source-level axiom-keyword gap is not an execution reproduction. It follows from the production construction of `AstTheorem.keyword_span`.
- The `declaration uses `sorry`` redirect is message-specific. It does not establish a generic generated-error classifier.
- Aeneas item-level source comments do not provide arbitrary generated-range ownership.
- This report does not close the separate questions of inline-user-Lean direct mapping, external-crate source recovery, UTF-8 coordinate behavior, or distinguishing all user errors from unsupported/tool failures.
- It does not prescribe whether future provenance lives in JSON, source maps, Lean syntax metadata, an in-memory graph, or another representation.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Current Anneal authority at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/README.md`, blob `bf22d554437659f38d8918c1e7c3480f4f62b126`: current redesign versus historical V1 authority boundary.
- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: Rust-oriented user goals and verification promise.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: Rust-oriented ordinary interface and deliberate non-decision on proof/source-correspondence mechanism.

Historical V1 implementation at the same repository revision:

- `anneal/v1/src/parse/attr.rs`, blob `9f352d511ca964e8c58d24206a3088608cb8aaf6`: `FunctionBlockInner`, proof clauses/keyword spans, and source-spanned annotation lines.
- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: `MappingKind`, `SourceMapping`, `push_spanned`, `push_mapped`, `render_struct`, `render_theorem`, function-identifier span selection, production axiom/proof construction, and mapping-related unit tests.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: `.lean.map` loading, diagnostic overlap resolution, `sorry` redirection, generated-order/cross-file tests, and conservative fallback.
- `anneal/v1/src/diagnostics.rs`, blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`: presentation on mapped Rust source and fallback behavior.
- `anneal/v1/README.md`, blob `2bfda6336f87bf3cd785a19286363ab13423bd7d`: historical user workflow and V1's explicit non-authoritative status for current design.

Current reference context:

- `reports/end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2`, `REPORT.md` blob `f6d9139254827972c6b41ae4bcbb8bbeccd20241`: item-level Charon/Aeneas/Lean provenance, historical V1 sidecar overview, and explicit boundary that synthesized target syntax may lack a unique Rust source token.

Evidence roles are current **design authority**, historical **source**, historical **unit tests**, existing current-corpus **derived/source synthesis**, and new **derived** conclusions. There is no fresh **execution** evidence.

## Revalidation

For a future Anneal revision, begin with current `anneal/README.md`, `PRINCIPLES.md`, and `DESIGN.md` to determine whether the redesign has selected a proof/source-mapping architecture. Do not assume V1 remains relevant.

If generated Lean remains part of the user-visible checking boundary, inventory every generator operation that can emit diagnostic-bearing Lean and classify it by provenance: copied user source, Rust-construct owner, obligation owner, or generated/internal. Mechanically verify that every intended non-internal class emits an explicit provenance record.

A useful execution fixture should trigger at least these cases:

1. an error in copied user proof text;
2. an error reported on a generated theorem name;
3. an admitted-proof / missing-proof diagnostic that should redirect to a proof obligation;
4. an error in generated `Pre`/`Post` scaffolding outside copied proposition text;
5. an error in generated theorem glue such as a binder/destructuring/application;
6. an axiom-related diagnostic;
7. two adjacent Rust functions whose generated order differs from source order; and
8. the same cases split across multiple Rust files.

Preserve the exact Rust source, generated Lean, provenance sidecar/metadata, raw Lean JSON diagnostic, and final user-facing diagnostic. A correct result is not "every error has a Rust squiggle". A correct result is that every Rust squiggle is justified by explicit provenance, while genuinely generator-owned failures remain visibly generator-owned rather than being misattributed to user source.
