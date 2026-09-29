# Incomplete annotations, authored text, and multi-edit boundaries in a controlled fixture

## Summary

A small invented Rust-comment annotation fixture separates discovery from semantic attachment. Its scanner still located a complete annotation while the containing Rust source failed to compile, but it withheld projection after an unfinished closing marker or a malformed payload line. Regeneration from an unsaved source buffer retained exact authored proof spacing through a Rust-body change. A two-edit action was accepted only when both edits mapped to authored payload ranges under the same source version and projection digest; adding one synthetic-header edit rejected the entire action. Direct Lean 4.30.0-rc2 checks showed that helper order and namespace placement change whether otherwise simple proof fragments elaborate.

This is a controlled design probe, not an implementation test of Anneal's current or historical parser, editor integration, or LSP code-action handler. It offers partial evidence for [#3731](https://github.com/google/zerocopy/issues/3731) I017, I022, I024, and I030, and for the corresponding [#3730](https://github.com/google/zerocopy/issues/3730) B06, B08, B10, B11, and B15 questions. It does not close those investigations.

## Applicability

The preserved `support/probe.py` invents `//% begin <id>`, `//% ` payload lines, and `//% end` in a Rust source file. It scans lines without parsing Rust, retains source intervals, and wraps complete payloads in synthetic Lean namespaces. Only ASCII source specimens were used, so its Python string offsets equal UTF-8 byte offsets in these runs. The script is a deliberately narrow model; the `//%` syntax is not asserted to be Anneal syntax.

On macOS 26.6.2 arm64, the run used CPython 3.14.7, Homebrew rustc 1.98.1 (`48a229cea`), and the locally installed Lean 4.30.0-rc2 (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`). Six Rust/source specimens, six projected edit-action cases, and four direct Lean layout cases were executed. The full inputs, outputs, hashes, commands, and diagnostics are in `support/raw-results.json`.

## Findings

### Discovery can continue during a Rust error while attachment remains unavailable

Changing `pub fn f() -> u32 { 7 }` to the syntactically broken `pub fn f( -> u32 { 7 }` made rustc exit 1. The line scanner still returned the same complete annotation and two payload intervals as baseline. This is evidence only that text discovery can be independent of Rust compilation for this marker grammar. It did not establish which Rust item owns the annotation; a compiler-backed subject is unavailable in the broken case. In the unclosed-marker case the scanner retained an incomplete block but projected no Lean payload. Replacing a `//% ` payload prefix with `// ` likewise retained the block as malformed and withheld it from the projection. **Basis: execution** of the fixture and rustc.

The practical distinction is between preserving text for the user and granting it a verified subject or editable Lean projection. The controlled scanner can report a tentative region while refusing to bind it to a compiled declaration. **Basis: derived** from the explicit fixture states; no editor diagnostic lifetime was tested.

### Regeneration should consume the authoritative authored buffer

The baseline proof used `exact helper`. A separate unsaved-buffer specimen changed it to `  exact helper -- retained spacing`; its source and projected hashes differed from baseline. Changing the Rust function body from 7 to 9 in that buffer left the authored proof spacing and comment intact in the regenerated projection. The on-disk baseline fixture remained separate in the raw record. The source buffer, rather than prior generated Lean, was the fixture's input to regeneration. **Basis: execution** of `render` over the preserved specimens.

This one-buffer control illustrates I024 and B15 but does not exercise an actual editor buffer, save event, external proof file, formatter, LLBC, or generated Lean import. It cannot establish a complete ownership policy.

### A multi-edit action needs one atomic source decision

The fixture rendered a synthetic header followed by two authored proof lines. Two plain edits wholly within mapped payloads passed a combined source-hash, projection-hash, version, exact-range, and expected-text guard and were applied as one source replacement. When the action also contained an edit to the synthetic header, the handler rejected the whole action with `no-single-authored-origin`; the source remained byte-identical to baseline. It likewise rejected a snippet containing a placeholder as `unsupported-snippet`, and rejected the old action after an unrelated Rust-body change, a version change, or a projection-identity change as `stale-generation`. Five of six action cases were rejected; all five preserved their starting source. **Basis: execution** of the fixture.

The accepted second edit was a plain replacement of a helper proof tactic; its placement inside one copied segment gave an exact source interval. A location used to explain a synthetic diagnostic would not have passed this exact-origin guard. **Basis: derived** from the mapping and synthetic-header negative control. The fixture did not invoke a Lean LSP code-action request, perform multi-file writes, or preserve snippet tab-stop semantics; rejecting snippets is one possible conservative policy, not a recommendation that all snippet actions must be rejected.

### Fragment order and namespace are semantic inputs

Direct Lean accepted `helper` followed by `proof` and rejected the reversed order with `Unknown identifier helper`. A duplicate `helper` in the same namespace failed with `` `helper` has already been declared ``, while one `helper` in each of namespaces `A` and `B` compiled. The exact four Lean source texts and command results are preserved. **Basis: execution** of pinned Lean.

These cases show that distributing helper declarations across annotations needs an explicit composition order and namespace context if a generated module is to preserve authored meaning. They do not compare per-annotation virtual documents, import boundaries, section variables, local instances, recursive dependencies, or real Aeneas/Anneal names.

## Boundaries

- **I017/B06:** One invented line-comment marker was tested. Attribute, block-comment, doc-comment, delimited Lean, nested marker, Unicode, incomplete Lean, and actual V1/V2 parser recovery remain untested. The scanner's continued discovery under invalid Rust is not semantic attachment.
- **I022/B08:** Only helper order, duplicate names, and separate namespaces were compiled. The experiment does not decide document granularity, cross-annotation invalidation, or whether a particular layout preserves batch semantics.
- **I024/B15:** One unsaved source string was used as a regeneration input. No real editor, concurrent save, external proof ownership, or user override was observed.
- **I030/B10/B11:** The action handler is fixture code. It did not request a real completion, rename, import suggestion, or code action from Lean. New imports, multiple source files, zero-width insertion, overlapping edits, syntax-aware snippet translation, and an LSP WorkspaceEdit transaction remain open.
- **I018–I021/I023/I025–I029/I031–I032:** This run does not add compiler-backed attachment, identity through structural moves, broken-model proof interaction, Unicode coordinate properties, general provenance, batch/live generator equivalence, or edit-stream cost. Existing reports address subsets of those separately.
- Lean compiled only the four standalone layout specimens, not the invented scanner's projected Rust payload. Rustc compiled only the six Rust specimens, not the Lean text inside comments. The two executions support separate facts and cannot be combined into an Anneal end-to-end claim.

## Evidence

- `support/probe.py`, SHA-256 `c80616ee85dcb6437eff17c18e1cf1a03b6f3037c61238ea7f47d1e5c5ee8b7b`, contains all source strings, scanner/projector, guarded action application, subprocess calls, and assertions.
- `support/raw-results.json`, SHA-256 `dc81039a29949d647c4594a2ca1f73658a077378ce7acca87a654c9b0e036cbe`, records six full source/projection specimens and rustc outcomes, six action results, and four Lean source/diagnostic outcomes. The driver substitutes `$WORK` for its disposable temporary path; two replays reproduced this JSON hash.
- Lean executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; rustc executable SHA-256 `2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340`. These identify the local binaries used, while `REPORT.json` records their release/commit identities.
- Relevant prior reports: `anneal-v1-annotation-diagnostics-history-2026-09-27` describes actual historical V1 parsing, `anneal-3730-projection-properties-2026-09-29` checks Unicode and edit streams in a separate illustrative projector, and `anneal-3730-charon-subject-identity-2026-09-29` directly inspects compiler-derived subject multiplicity. This package adds no claim about their implementation subjects.

## Revalidation

From this report directory, run `python3 support/probe.py` with the pinned Lean binary at the path in the script and a known rustc on `PATH`. The script rewrites only `support/raw-results.json`; compare the six fixture states, five rejected action reasons, and the Lean unknown-name/duplicate-name diagnostics. At a new Anneal implementation, replace this scanner and guard with its actual annotation/parser and edit API, then repeat with a real unsaved editor buffer, compiler-backed subject, LSP multi-edit action, and batch/live Lean projection.
