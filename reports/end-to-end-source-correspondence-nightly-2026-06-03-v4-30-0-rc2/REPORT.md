# Source correspondence across Charon, Aeneas, Lean, and historical Anneal V1

## Summary

At the revisions selected by current Anneal, source correspondence is a chain of useful but different identities, not one end-to-end source map.

Charon retains structured item identity and Rust source metadata. Aeneas carries an item's Charon `item_meta` through its pure translation and emits generated Lean declarations with doc comments that contain the Rust item name and Charon definition span. At the pinned Aeneas revision, a generated comment can therefore say, for example, that Lean `choose` came from `no_nested_borrows::choose` at `tests/src/no_nested_borrows.rs`, lines `200:0-206:1`. If Charon's span records a macro-origin span, Aeneas's span formatter also prints that secondary origin.

Lean's diagnostics point into the Lean document, not back into Rust. Lean messages carry a Lean file name and start/end positions; the language server converts those positions to LSP ranges in the open Lean document. The pinned Aeneas output does not contain a machine-readable mapping from arbitrary generated Lean byte or token ranges to Rust byte ranges. Its per-declaration comments provide an item-level bridge, not an operation-level source map. Generated backward value flow, loop helpers, proof scaffolding, and other synthesized Lean can therefore have a clear originating Rust item without having a precise Rust span for every generated subexpression.

This distinction matters for Anneal's Rust-oriented diagnostics. Historical Anneal V1 independently built a sidecar mapping from generated Lean byte ranges to Rust byte ranges and used it to remap Lean diagnostics. That mechanism is evidence that precise remapping is feasible, not current V2 architecture authority. Current `anneal/DESIGN.md` explicitly leaves the source/model-correspondence strategy undecided.

No fresh rustc, Charon, Aeneas, Lean, or language-server execution was performed. The report uses pinned implementation source, checked-in generated Lean, and historical Anneal source. It establishes what correspondence metadata exists and where precision is lost; it does not empirically validate every diagnostic shape or macro/generated-source case.

## Applicability

This report describes the combination selected by `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`;
- Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`;
- Lean `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, version `v4.30.0-rc2`.

The report uses current Anneal V2 design documents at the same zerocopy revision only to state design constraints and non-decisions. It uses `anneal/v1/` at that revision as preserved historical evidence of a source-mapping experiment. V1 is not current architecture authority.

"Source correspondence" here covers four distinct questions:

1. which Rust item or generated Rust artifact a Charon declaration came from;
2. which Charon/Rust item an Aeneas-generated Lean declaration came from;
3. which range in a generated Lean document a Lean diagnostic identifies; and
4. whether that Lean range can be projected precisely back into Rust source.

The first three have source-defined answers at these pins. The fourth is only partial in the upstream Charon/Aeneas/Lean chain: item-level correspondence exists, but arbitrary generated-Lean ranges do not have a preserved upstream Rust byte-range map.

Adjacent Charon, Aeneas, or Lean revisions are outside this report. In particular, later Aeneas source contains additional output facilities that are not evidence for `nightly-2026.06.03`.

## Findings

### There is no single identity that survives unchanged across all four layers

Charon deliberately separates typed in-crate item IDs, structured Rust names, and source spans. Its typed IDs are useful for semantic references inside one extracted crate; structured `Name` values recover recognizable Rust paths; `ItemMeta` carries source and attribute metadata. The pinned Charon source does not promise that numeric item IDs are stable across independent extraction runs.

Aeneas then assigns its own pure-AST identifiers and target names. Its pure declarations retain Charon metadata, but generated Lean names are computed for the target language and can be affected by rename/model rules. Lean finally identifies declarations and diagnostics in Lean modules and documents.

A cross-layer consumer therefore needs an explicit relation among identities. A display spelling such as `foo::bar`, a Charon numeric ID, a generated Lean name, and a source span each answer different questions.

Basis: **source** + **derived**.

### Charon preserves item-level source metadata, while macro provenance is intentionally incomplete

At the pinned Charon revision, `ItemMeta` includes the item's structured name and definition `Span`. A span contains file identity and begin/end locations. Charon also supports a `generated_from_span` origin used when translated rustc source information says that code came from another span.

This is useful but not a complete rustc expansion provenance graph. The pinned representation does not serialize the full macro expansion/hygiene chain. Procedural macros can assign token spans, so the source location visible after expansion is partly controlled by the macro. Build-script-generated files that rustc reads as source can instead appear as ordinary files with their own paths and spans.

Consequently, "this LLBC operation has a Rust span" is not equivalent to "this operation can always be attributed to a unique user-authored macro invocation."

Basis: **source** plus the existing checked-in Charon/generated-source reference evidence.

### Aeneas carries Charon item metadata into its pure declarations

At `AeneasVerif/aeneas@ac9f1bc...`, the pure AST aliases Charon's `span` and `llbc_name` types. Pure type declarations retain `item_meta : T.item_meta`; pure function declarations retain `item_meta : T.item_meta`; globals and traits likewise retain source-facing metadata.

`Translate.translate_function_to_pure_aux` starts from an LLBC `fun_decl`, uses `fdef.item_meta.span` as the translation span, and produces a pure function declaration with that context. If a function translation fails, `translate_function_to_pure` reports the function name and raw definition span and returns `None`.

The correspondence boundary is therefore explicit: Aeneas does not have to rediscover the Rust item after symbolic execution. It carries the upstream item metadata alongside the functionalized declaration. But this is declaration metadata, not a statement that every pure expression has a Rust source range.

Basis: **source**.

### Aeneas emits Rust item names and Charon definition spans into Lean doc comments

The pinned Lean extractor intentionally calls `extract_fun_comment` before a generated function declaration "to link the extracted definition to its original rust definition." The comment starts with the Charon/Aeneas printable Rust name and passes the function's `item_meta.span` to `extract_comment_with_span`.

For Lean, `extract_comment_with_span` emits a doc comment. It appends `Errors.span_to_string span`, and may also append an external name pattern and public visibility. `Errors.span_to_string` prints the Charon file and begin/end positions. If `span.generated_from_span` is present, the formatter adds a second clause identifying the macro-invocation origin recorded by Charon.

The checked-in generated `tests/lean/NoNestedBorrows.lean` is a preserved execution artifact. At the pinned commit it contains:

`[no_nested_borrows::choose]` followed by `Source: 'tests/src/no_nested_borrows.rs', lines 200:0-206:1`

immediately before the generated Lean `def choose`.

This gives a durable, human-readable Rust-item-to-Lean-declaration link without rerunning Aeneas.

Basis: **source** + preserved upstream **execution** artifact. No fresh execution was performed.

### The emitted span is a declaration span, not a token-by-token Rust-to-Lean map

`extract_fun_comment` passes one `item_meta.span` for the generated function declaration. `extract_comment_with_span` formats that span as prose. It does not emit a table assigning Rust ranges to each generated Lean token or expression.

That distinction is visible in Aeneas's transformation model. A Rust function can become a Lean function whose signature and body contain synthesized value flow: mutable references are functionalized, backward functions can be introduced, loops can become helper functions, and effect wrappers can be synthesized. Those target constructs can be derived from one Rust item without having a one-to-one Rust syntax node.

The doc comment therefore answers "which Rust declaration did this Lean declaration come from?" It does not by itself answer "which Rust operation should receive a squiggle for this arbitrary Lean subexpression?"

Basis: **source** + **derived** from the pinned Aeneas translation and extraction representations.

### Generated helper identities are derived identities

Aeneas's pure `fun_decl` explicitly distinguishes generated loop functions with `loop_id`, and its extractor annotates loop/loop-body output relative to the originating Rust function. Termination-measure and decreases-proof templates are also emitted with comments using the original function's `item_meta.span`.

The same general issue applies to backward borrow machinery: the Rust-to-Lean translation can synthesize continuations or return functions that have no independent Rust declaration. A target-language diagnostic inside such generated structure can still be associated with the source function, but the source item span alone cannot identify a unique source token that "is" the synthesized operation.

Basis: **source** + existing Aeneas translation reference evidence.

### Lean diagnostics are ranges in Lean source

At Lean `v4.30.0-rc2`, a `Lean.Message` is a `BaseMessage` containing `fileName`, `pos`, and optional `endPos`. These positions describe the Lean source being elaborated.

The language server's `Widget.msgToInteractiveDiagnostic` converts `Message.pos` and `Message.endPos` through the open document's `FileMap.leanPosToLspPos`. It produces an LSP `range` and a `fullRange`; long diagnostic ranges can be visually truncated while `fullRange` retains the untruncated end. `FileWorker.publishDiagnostics` publishes those converted diagnostics for the current Lean document.

Nothing in this conversion consults Charon or Rust spans. The server knows where an error lies in the generated Lean document. A downstream source-correspondence layer must provide the Rust projection if the user-facing location should be Rust.

Basis: **source**.

### Tactic-state position and diagnostic position share the generated Lean document boundary

The pinned Lean server can answer goal-state requests at a Lean document position, and its diagnostics are also attached to the Lean document. This makes the generated Lean document a natural common coordinate system for interactive proof tooling.

It does not make that coordinate system a Rust source map. A tool can reliably ask "what is the tactic state at this position in generated Lean?" while still lacking a precise answer to "which Rust byte range should own this goal?" Those are separate relations.

Basis: **source** + **derived**.

### Aeneas name comments remain useful when exact range projection is impossible

Even without operation-level mapping, the generated comments retain enough context to recover the containing Rust item for many failures. A diagnostic range can first be located in the generated Lean file; nearby declaration structure and the Aeneas doc comment can then identify the Rust declaration and its Charon span.

This is a coarse correspondence mechanism. It can be adequate for reporting "verification of function `f` failed" or for directing a specialist to the relevant source item. It cannot justify a precise source underline inside the function body unless additional mapping evidence exists.

Basis: **derived** from Aeneas emitted comments and Lean diagnostic ranges.

### Translation failures create correspondence holes before Lean diagnostics exist

Charon and Aeneas can both fail before a Lean declaration is available. The pinned Charon report records best-effort/partial extraction modes and explicit error nodes. The pinned Aeneas source catches per-function `CFailure`, emits a warning with the Rust/LLBC declaration span, and returns no pure translation for that function.

A user-facing diagnostic system therefore cannot assume that every Rust item reaches the generated Lean coordinate system. Pre-Lean failures must retain and report their own Rust/Charon source identity rather than being forced through a Lean source map.

Basis: **source** + existing reference evidence.

### Generated Rust has different provenance classes before Charon

Build-script output and procedural-macro expansion do not have the same source-provenance behavior.

When a build script creates a Rust file that is later included and parsed by rustc, the generated file can have ordinary source-file identity and spans. When a procedural macro emits tokens, their spans are supplied through proc-macro span/hygiene mechanisms; Charon sees post-expansion compiler locations and does not preserve the full expansion chain.

End-to-end diagnostics therefore need to distinguish "generated file with a real source span" from "expanded token whose current span points at call-site/definition-site/mixed provenance." Treating both as generic "generated code" loses information a later diagnostic policy may need.

Basis: **source** + existing reference evidence.

### Historical Anneal V1 built an explicit byte-range sidecar for precise Rust diagnostics

The preserved V1 implementation did not rely only on Aeneas declaration comments. `anneal/v1/src/generate.rs` defines `SourceMapping` entries with:

- generated Lean byte start/end;
- original Rust source file;
- Rust byte start/end; and
- a mapping kind: `Source`, `Synthetic`, or `Keyword`.

Its `LeanBuilder` records direct mappings for user-authored proof lines and intentional anchor mappings for synthesized Lean. For example, generated theorem identifiers could be anchored to a Rust function identifier even though the generated identifier had no literal source counterpart.

`anneal/v1/src/aeneas.rs` then resolves Lean diagnostic byte ranges against those mappings. It intersects overlapping ranges, maps the overlap back into Rust byte offsets, and contains a targeted heuristic that redirects some synthetic "`sorry`" diagnostics to the relevant Rust proof/axiom keyword.

This mechanism demonstrates one concrete way to bridge a generated Lean coordinate system back to Rust with finer precision than Aeneas's item comments. It also demonstrates that synthesized target syntax sometimes needs an explicitly chosen source anchor rather than a mechanically identical source span.

Basis: historical Anneal **source**.

### V1's sidecar is evidence about the problem, not a V2 design decision

Current `anneal/DESIGN.md` requires ordinary diagnostics to connect unsatisfied obligations to Rust, but explicitly leaves the "exact theorem or validation strategy used to justify source/model correspondence and complete obligation coverage" undecided.

The V1 sidecar therefore should not be copied merely because it exists. Its durable lesson is narrower: item-level provenance and target-language positions are not the same thing as precise generated-to-source range correspondence, and one prior implementation had to represent that missing relation explicitly.

Basis: current Anneal **documentation/source authority** + historical **source** + **derived** conclusion.

### The current chain supports a useful correspondence taxonomy

For later work, the current evidence separates four correspondence strengths:

1. **Semantic item identity** — Charon typed IDs and declaration references identify items inside the extracted crate.
2. **Human-recognizable source identity** — structured Rust names, file identity, and declaration spans identify the source item.
3. **Generated-declaration provenance** — Aeneas doc comments connect a generated Lean declaration to a Rust/Charon item and span.
4. **Generated-range provenance** — a mapping from arbitrary Lean ranges to Rust ranges. The pinned upstream chain does not provide this generally; V1 supplied its own sidecar for Anneal-generated material.

Confusing these levels creates concrete failure modes. A generated Lean declaration can have good item provenance while a diagnostic inside its synthesized body has no defensible exact Rust token. Conversely, a pre-Lean Charon/Aeneas error can have a precise Rust span without any Lean position.

Basis: **derived** synthesis of the pinned source.

## Boundaries

- No fresh rustc, Charon, Aeneas, Lean, Lake, LSP, or `lean --json` execution was performed.
- The checked-in Aeneas Lean file is preserved upstream output. It is not output generated by this report.
- This report establishes the metadata and conversion paths in the exact pinned sources. It does not claim that every legal Rust construct, macro expansion, Aeneas helper, or Lean diagnostic was empirically sampled.
- Charon's `generated_from_span` is not a full rustc macro-expansion/hygiene history.
- Aeneas declaration comments are not a proof that all generated Lean syntax has a unique Rust source location.
- A nearby Aeneas declaration comment can identify a containing Rust item; using it to select an exact source token is a heuristic unless separate range evidence exists.
- The report does not establish stable Charon numeric IDs across reruns or stable generated Lean names across Aeneas revisions.
- It does not establish path relocatability. Charon and Aeneas can print source paths, but whether those paths resolve in a later machine/workspace is a separate question.
- It does not establish multibyte UTF-8 equivalence among Charon columns, Lean positions, LSP UTF-16 positions, and Rust byte offsets. That requires a dedicated probe/specification analysis.
- It does not compare batch `lean --json` diagnostics with LSP diagnostics in every field. The report relies on Lean's core `Message` position fields and the pinned LSP conversion for the server-side claim.
- It does not establish external-crate source recovery when the referenced source tree is absent locally.
- V1's sidecar mapped Anneal-generated Lean and user-authored proof material. It is not evidence that Aeneas itself emitted equivalent sidecar mappings.
- Current Anneal V2 deliberately has not selected a source/model-correspondence strategy. Nothing here selects one.

## Evidence

**Source — Charon pinned by Aeneas.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/ast/krate.rs`, blob `fabd29106ded9cc2116ce508cbae7ccfbaef4070`: typed item IDs and crate maps.
- `charon/src/ast/names.rs`, blob `30441a758993d4f8f280702d175a2a6c7dc574b9`: structured `Name`/path representation.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`: `Span`, `SpanData`, file identity, `ItemMeta`, `generated_from_span`.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: rustc definition/source translation, path normalization, inlining/generated-span handling.

The existing reference packages `charon-item-identity-spans-comments-nightly-2026-06-03` and `generated-rust-visibility-nightly-2026-05-31` preserve the broader source investigation and checked-in Charon specimens behind those facts.

**Source — Aeneas selected by Anneal.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: pure declarations retaining LLBC/Charon names, spans, and `item_meta`; generated-loop identity.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: LLBC-to-pure translation, use of `fdef.item_meta.span`, and per-function failure reporting.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: target name registration and collision reporting tied to item spans.
- `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`: `extract_comment_with_span`; Lean doc-comment formatting with Rust name patterns, span text, and visibility.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: `extract_fun_comment`, generated function/loop/termination-helper comments, and Rust-model attributes.
- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: `span_data_to_string`, `raw_span_to_string`, `span_to_string`, including the optional macro-origin clause.

**Preserved Aeneas execution artifact — same revision.**

- `tests/lean/NoNestedBorrows.lean`, blob `e2a706b744e2e9a105e305cf8a2b353354209dae`, especially the generated `choose` declaration whose doc comment records `no_nested_borrows::choose` and source lines `200:0-206:1`.

This artifact was already checked into Aeneas. The present report did not regenerate it.

**Source — Lean `v4.30.0-rc2`.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`: `BaseMessage` file name, start/end positions, severity, and structured message data.
- `src/Lean/Widget/InteractiveDiagnostic.lean`, blob `5fc9e0b22a3195c7843f7a45b7c0bdab870fce08`: `msgToInteractiveDiagnostic`, conversion from Lean positions through the document `FileMap` to LSP `range`/`fullRange`.
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`: conversion and publication of document diagnostics.
- `src/Lean/Server/ProtocolOverview.lean`, blob `4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`: server request/notification inventory and open-document/RPC model.

The existing `lean-server-tactic-state-v4-30-0-rc2` package preserves the broader tactic-state-at-position investigation.

**Historical Anneal V1 source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: `MappingKind`, `SourceMapping`, `LeanBuilder::push_spanned`, and `LeanBuilder::push_mapped`.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: native Lean diagnostic decoding and `resolve_mapping` from generated Lean byte ranges to Rust byte ranges.
- `anneal/v1/src/diagnostics.rs`, blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`: user-facing mapped diagnostics.

**Current Anneal design authority at the same zerocopy revision.**

- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: Rust-oriented diagnostic requirement and deliberate non-decision on the exact source/model-correspondence mechanism.
- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: governing project principles.

No source listed above was freshly executed for this report.

## Revalidation

For a future Anneal toolchain, revalidate the correspondence chain in this order.

First resolve the exact Charon, Aeneas, and Lean commits. In Charon, diff `ast/meta.rs`, `ast/names.rs`, and `translate_meta.rs` for changes to `ItemMeta`, span/macro provenance, file identity, and name representation. In Aeneas, diff `Pure.ml`, `Translate.ml`, `ExtractTypes.ml`, `Extract.ml`, and `Errors.ml` for whether item metadata still survives translation and what the Lean extractor emits. In Lean, diff `Message.lean`, `InteractiveDiagnostic.lean`, and `FileWorker.lean` for the diagnostic coordinate system and LSP conversion.

Then inspect one checked-in Aeneas Lean golden corresponding to a known Rust fixture. Confirm that the generated declaration still records the Rust item identity and source span. If the format changed, record the new machine/human-readable contract rather than assuming this report's comment syntax.

On a capable execution surface, use one small fixture containing:

- a handwritten function with a proof failure tied to one source expression;
- a mutable borrow that causes Aeneas to synthesize backward value flow;
- a loop that creates a generated helper;
- a `include!` of build-script-generated Rust;
- a procedural macro whose emitted token has an intentional call-site or definition-site span; and
- at least one non-ASCII character before a mapped source position.

At the exact selected revisions, preserve the Rust files, LLBC, generated Lean, Aeneas stdout/stderr, and both a batch Lean diagnostic and an LSP diagnostic. Record all files and hashes. For each diagnostic, classify what can be recovered mechanically: exact Rust byte range, Rust declaration only, generated file only, or no source.

As a control, add an explicit sidecar map from generated Lean byte ranges to Rust byte ranges and verify only that diagnostics falling inside mapped ranges project to the intended source. This tests the range-mapping mechanism; it does not prove that the mapping producer is semantically correct or that every verification obligation has source correspondence.

The multibyte case is required before asserting equivalence among Rust bytes, Charon columns, Lean `Position`, and LSP positions. A successful ASCII-only probe does not establish UTF-8/UTF-16 correctness.
