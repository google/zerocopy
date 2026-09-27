# Rust comment preservation in Aeneas-generated Lean at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, original Rust prose comments are not generally reproduced in generated Lean. Aeneas does emit Lean doc comments before generated declarations, but those are synthetic correspondence metadata constructed from the Rust item name, source span, optional external name pattern, and visibility.

The distinction is visible in exact-revision golden files. `tests/src/arrays.rs` places the Rust doc comment `/// This test is to exercise the pure micro passes` immediately before `array_update2`. The corresponding `tests/lean/Arrays.lean` definition contains only Aeneas's synthesized `[arrays::array_update2]`, `Source: ...`, and `Visibility: public` comment; the Rust prose sentence is absent. The same Rust fixture contains ordinary body comments inside `non_copyable_array`, including `// x is moved (not deep copied!)`; the generated Lean body contains the translated call but not that comment text.

This loss happens despite richer metadata upstream. The Charon revision selected by this Aeneas release explicitly recovers body comments and assigns them to LLBC statements through `comments_before`; Charon item metadata also contains optional `source_text`. Aeneas's ordinary Lean comment printer does not copy either field into generated Lean. The generated Lean file is therefore useful for source correspondence, but it is not a comment-preserving source representation.

The existing corpus report `end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2` already establishes Aeneas's declaration-level `Source:` comments, macro-origin rendering, and the lack of a fine-grained Rust-to-Lean source map. This report is deliberately narrower: it records what happens to original Rust comment prose and why the richer Charon comment metadata should not be mistaken for generated-Lean preservation.

No fresh Charon, Aeneas, Rust, or Lean execution was performed. The findings use exact pinned source plus checked-in Rust and generated-Lean fixtures.

## Applicability

The primary subject is Aeneas release `nightly-2026.06.03`, which resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`. Current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` fetches that release archive.

That Aeneas revision pins `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`. Charon is relevant because it demonstrates that comment loss in generated Lean is not simply caused by Charon having no comment representation.

“Comment preservation” here means reproduction of user-authored Rust comment text in the generated Lean source. It is distinct from Aeneas's own generated Lean doc comments, which carry source-correspondence information.

This report covers the ordinary Lean extraction path and the checked-in test fixtures at these exact revisions. It does not generalize to later Aeneas output facilities or specialized downstream tooling that may separately retain LLBC.

## Findings

### Aeneas-generated declaration comments are synthetic metadata

`src/extract/ExtractTypes.ml` defines `extract_comment_with_span`. For Lean, it emits a `/-- ... -/` doc comment. The content is assembled from:

- caller-supplied descriptive strings;
- `Errors.span_to_string span`;
- an optional external name pattern; and
- optional `Visibility: public`.

Function extraction constructs its descriptive string in `extract_fun_comment`, including special labels for generated loop and loop-body functions. Type extraction supplies the Rust item name. Neither helper takes original Rust comment text as an input.

These generated doc comments should therefore be read as Aeneas metadata about the generated declaration, not as preserved Rust documentation.

Basis: **source**.

### A Rust doc comment can disappear while Aeneas still emits a Lean doc comment

At the exact Aeneas revision, `tests/src/arrays.rs` contains:

```rust
/// This test is to exercise the pure micro passes
pub fn array_update2(a: &mut [u32], i: usize, x: u32) {
    ...
}
```

The corresponding checked-in `tests/lean/Arrays.lean` output begins the translated definition with a different doc comment:

```lean
/-- [arrays::array_update2]:
    Source: 'tests/src/arrays.rs', lines 133:0-136:1
    Visibility: public -/
def array_update2 ...
```

The Rust sentence does not appear in the generated Lean file.

This is a direct counterexample to any assumption that a Rust doc comment is carried into generated Lean merely because the generated Lean declaration itself has a doc comment.

Basis: checked-in Rust source + checked-in generated **execution artifact**.

### Ordinary body comments are also absent from the corresponding Lean body

The same Rust fixture gives a body-level example. `non_copyable_array` contains:

```rust
// x is moved (not deep copied!)
// TODO: determine whether the translation needs to be aware of that and pass by ref instead of by copy
take_array_t(x);

// this fails, naturally:
// take_array_t(x);
```

The corresponding generated Lean declaration retains the source span for the whole Rust function and translates the live call:

```lean
def non_copyable_array : Result Unit := do
  take_array_t (Array.make 2#usize [ AB.A, AB.B ])
```

The body-comment prose does not appear in `tests/lean/Arrays.lean`.

The result is stronger than “doc comments are treated specially.” At least this ordinary statement-adjacent comment material is also omitted from the generated Lean surface.

Basis: checked-in Rust source + checked-in generated **execution artifact**.

### Charon explicitly recovers body comments before Aeneas consumes LLBC

The pinned Charon source contains a pass named `recover_body_comments.rs`. Its module comment states that it takes comments found in the original body and assigns them to statements. The pass attaches comment strings to `comments_before` on LLBC and ULLBC statements.

The pinned generated LLBC AST confirms the representation: a statement carries its source `span`, statement ID, kind, and `comments_before : string list`.

Thus the ordinary body-comment omission observed in generated Lean is not evidence that Charon necessarily discarded those comments first. Charon has a dedicated representation and recovery pass for them.

Basis: **source**.

### Charon item metadata is richer than Aeneas's generated comment surface

At the pinned Charon revision, `item_meta` contains the structured item name, source span, optional `source_text`, attribute information, locality, and opacity. Aeneas's pure top-level declarations retain Charon `item_meta`, as established by the existing source-correspondence report.

But Aeneas's Lean correspondence printer selects only a small subset of that information. It formats the source span and selected naming/visibility information. It does not print `source_text`, nor does the ordinary declaration-comment helper consume statement `comments_before`.

This is an important layering boundary: “metadata survives into Aeneas's translation structures” is not the same statement as “metadata is serialized into generated Lean.”

Basis: **source** + existing corpus evidence + **derived** distinction.

### Generated Lean should not be used as the sole store for source prose

A consumer that needs original comments—for example, to attach user-written proof intent or explanatory prose to a generated obligation—cannot safely recover those comments from the generated Lean file at this revision.

The generated Lean retains useful item-level source correspondence. It does not retain enough original comment text to act as a lossless source annotation store. Such a consumer would need to keep the Rust source itself, retain and interpret Charon/LLBC comment metadata, or introduce a separate sidecar representation.

This is a capability boundary, not a recommendation for Anneal's architecture.

Basis: **derived** from source and exact-revision golden artifacts.

## Boundaries

- No fresh Charon, Aeneas, Rust, Lean, Lake, or Nix execution was performed.
- The report establishes that Rust comments are **not generally preserved** in ordinary generated Lean. It does not claim that every possible comment is always absent.
- It does not inventory every Rust comment form, including all combinations of inner/outer doc comments, attributes generated from docs, macro-produced comments, or comments attached to unusual syntax.
- It does not claim that Charon preserves every Rust comment perfectly. The pinned recovery pass describes a heuristic for assigning body comments to statements.
- `item_meta.source_text` is evidence that Charon can retain item source text. This report does not assert that the field necessarily contains leading doc-comment text for every item.
- It does not claim that Aeneas discards all comment metadata immediately on input. The result concerns ordinary generated Lean output.
- It does not duplicate the broader source-correspondence result. Rust item/span comments, macro-origin rendering, Lean diagnostic coordinates, and historical Anneal V1 range mapping remain covered by `reports/end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2/`.
- The checked-in generated Lean is preserved upstream output from the same revision, not output freshly regenerated by this report.

## Evidence

**Anneal selection.**

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: selects Aeneas release `nightly-2026.06.03`.
- The release tag resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- At that Aeneas revision, `charon-pin`, blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`, pins Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`.

**Aeneas extraction source — exact selected revision.**

- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`, lines 1197-1257: Lean comment delimiters and `extract_comment_with_span`.
- Same file, lines 1497-1509: type declarations construct correspondence comments from name/span/visibility.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`, lines 2047-2065: `extract_fun_comment`.
- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`, lines 13-36: formatting of the source span used by generated comments.

**Exact source/golden pair demonstrating omitted Rust prose.**

- `tests/src/arrays.rs`, blob `478af7171452826436f56f12c88493debac8e0d0`, lines 132-136: the `array_update2` Rust doc comment and function.
- Same file, lines 255-268: ordinary comments inside and around `non_copyable_array`.
- `tests/lean/Arrays.lean`, blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`, lines 221-231: generated `array_update2` with synthesized source/visibility comment but no Rust doc prose.
- Same file, lines 417-427: generated `take_array_t` and `non_copyable_array`, with source comments on declarations but no body-comment prose.

**Charon source — exact Aeneas-pinned revision.**

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/transform/add_missing_info/recover_body_comments.rs`, blob `d1defb3d5b552c4f1309f9b7990b0ce1cca492c0`, especially lines 1-19 and 39-79: recovery and assignment of original body comments to statement `comments_before`.
- `charon-ml/src/generated/Generated_LlbcAst.ml`, blob `2a9a9aa71ae863fb3178eaee9f790de16a9f28ea`, lines 9-19: LLBC statement representation including `comments_before`.
- `charon-ml/src/generated/Generated_Types.ml`, blob `69aad6059931c8b365f7d1abb800e5716aec8ad5`, lines 963-987: `item_meta`, including `span`, optional `source_text`, and attributes.

**Related canonical corpus evidence.**

- `reports/end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2/`, current report blob `f6d9139254827972c6b41ae4bcbb8bbeccd20241`: declaration-level Aeneas `Source:` comments, item metadata retention, macro-origin formatting, Lean diagnostic coordinates, and historical Anneal V1 range mapping.

All evidence was materially inspected on 2026-09-27.

## Revalidation

For a future Aeneas revision, use one deliberately distinctive fixture rather than attempting to infer behavior from generated comment syntax alone:

```rust
/// SENTINEL_DOC
pub fn f(x: u32) -> u32 {
    // SENTINEL_BODY
    x
}
```

Generate Lean at the exact target revision and search the output separately for `SENTINEL_DOC`, `SENTINEL_BODY`, and Aeneas's own source-correspondence metadata. Preserve the Rust input and Lean output together.

Then inspect `extract_comment_with_span` and its callers. If they now consume source comment fields, `source_text`, documentation attributes, or a new structured metadata channel, record that change. Also inspect Charon's body-comment representation and recovery pass so that an observed omission can still be attributed to the correct layer.

A successful sentinel test establishes behavior only for the tested comment forms. If Anneal needs a guarantee about all doc-comment or macro-comment cases, expand the fixture matrix accordingly instead of extrapolating from one function.