# Source-owned proof ranges versus compiler and Lean diagnostic origins

## Summary

A pinned Rust→Charon→Aeneas→Lean run retained source bytes, LLBC, generated Lean, compiled model modules, and a projected proof document. Rustc located a deliberately wrong Rust expression at source bytes 156–163. Charon gave ordinary functions source spans/text but gave a macro-generated function a span inside the macro definition with no `source_text`. Aeneas printed all three names and source locations in generated Lean comments; those are lexical navigation candidates, not authenticated editable edges. A separate, explicitly illustrative copier mapped six projected proof segments to exact Rust doc-comment payload bytes. Only those copied bytes received source edit authority in the model.

Fresh `lean --json` and a fresh Lean LSP server produced the same four diagnostic messages for identical projected Lean text. The copied typo appeared twice because one authored block fed two obligations. Unicode before the token made byte, scalar, and UTF-16 columns differ; Lean's diagnostic landed one column after the token start in both batch and LSP coordinates. While a version-1 live diagnostic request was pending, the owning Rust doc-comment line was deleted on disk. The server returned version-1 diagnostics about its open old text, and the model rejected a version-1 patch against the changed version-2 Rust source. This is evidence for explicit version/source ownership checks, not a claim that Anneal's editor UI implements them.

The package addresses bounded parts of [#3731](https://github.com/google/zerocopy/issues/3731) I025–I032/I059–I063 and the related [#3730](https://github.com/google/zerocopy/issues/3730) B/K crosswalk. The actual compiler/Lean ranges and the invented `///| ` projection are deliberately distinguished throughout.

## Toolchain and subjects

The host was macOS 26.6.2 arm64. Executed binary SHA-256: nightly-2026-05-31 rustc `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`; Charon 0.1.210 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; Aeneas `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`; Lean 4.30.0-rc2 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The existing Aeneas Lean library OLean had SHA-256 `67701a9e8bf68cf0d51a01a4cb5648e2981c08d09402c4c4ac7bb8452d6263cb`. No dependency was installed.

`support/source.rs` (SHA-256 `36b8dc373f8217d0cceaf4574ee8cd06c7567d373345a90e053eccb1fb552c1f`) contains two ordinary functions with `///| ` proof payloads and one macro-generated helper. Rustc metadata compilation, `charon rustc --preset aeneas`, Aeneas split-file Lean generation, and direct Lean compilation of `Source.Types` and `Source.Funs` all exited 0. The acquired `support/artifacts/source.llbc` SHA-256 was `6464c34c0a2b6b61670e84dda6dd46273a261515dd5c16b7e707d6181f17ea4f`. Aeneas' `Funs.lean` SHA-256 was `abad37a40ebb84fb556edd905616762c8f08e685bdb7c573e42af22fc5a37b59`. The baseline and two-range-patched proof files then passed direct Lean batch checks. No Rust/Lean semantic correspondence theorem was attempted.

## Origin and editability matrix

| Specimen | Actual range/provenance evidence | Edit authority in this report |
| --- | --- | --- |
| Deliberately invalid Rust `"wrong"` expression | rustc JSON primary span source bytes 156–163, line 7, columns 5–12; rustc exited 1. | Ordinary Rust source range only; it is a rustc error, not a projected proof edit. |
| `step` and `select` | Charon local item spans lines 6–8 and 13–15 with `source_text`; Aeneas generated comments and `def` names at lines 18/21 and 24/27 of `Funs.lean`. | Charon spans explain model provenance. The Aeneas comments are lexical candidates and do not license writing generated Lean back into Rust. |
| `macro_generated` | Charon span line 19, columns 8–67 inside macro definition; `source_text` and `generated_from_span` null. Aeneas printed a matching source comment and declaration at lines 33/36. | None. Neither the macro definition span nor the generated declaration establishes an authored proof range. |
| Six projected proof segments | An illustrative copier stripped each five-byte `///| ` prefix, then copied exact UTF-8 payload byte intervals. The first two lines were emitted twice; the second two once. | Only a single wholly contained copied segment can authorize a projected edit, contingent on source/projection hashes and version. Synthetic imports, theorem wrappers, and Aeneas files are read-only in this model. |
| Generated-model diagnostic | Mutating Aeneas' `Funs.lean` yielded Lean JSON `Unknown identifier missingGeneratedModelName` at line 22, column 2. | Preserve the generated-file location for explanation; no exact authored Rust proof target follows from it. |

These categories prevent an item span, generated comment, or diagnostic anchor from silently becoming an edit range. The candidate map and all raw files are retained in `support/results.json` and `support/artifacts/`.

## Unicode and batch/live diagnostic comparison

The illustrative proof generator added a synthetic `import Source.Funs` and a one-second elaboration delay, then emitted three theorems from two Rust doc blocks. The first copied tactic line contains `/- 🦀 é -/ missingProof`; the source uses a supplementary Unicode scalar and a combining mark. The `missingProof` token began on projected zero-based line 4 at UTF-8 byte column 17, Unicode scalar column 13, and UTF-16 column 14. A position inside the crab's surrogate pair would not be an invertible scalar boundary and is never used as an edit address.

Fresh batch Lean returned four errors: two `unknown tactic` and two `unsolved goals`. A fresh `lean --server` opened the exact same projected text at document version 1; its settled nonempty published diagnostics had the same four message strings. For the first typo, batch's `unknown tactic` position was one-based line 5, scalar column 14; LSP's was zero-based line 4, UTF-16 character 15. Both are **one coordinate unit after** the token start. The second copied occurrence produced corresponding errors on lines 8/7. The original Lean positions are preserved. A source mapper may use the copied segment to explain the diagnostic, but the diagnostic's offset is not itself an exact replacement range.

Intermediate LSP notifications included empty and partial diagnostic lists; the harness waited for `textDocument/waitForDiagnostics` for version 1 and compared the last nonempty version-1 set. This checks message agreement for one fresh batch/live pair, not stable ranges across all Lean revisions or incremental edits.

## Versioned multi-range patches and deletion during query

The model applied a two-range action replacing `trivial` with `simp` in both authored Rust blocks. Regeneration changed both projected copies of the first block; the resulting Lean file passed a fresh batch check. Five rejected controls left Rust bytes unchanged: a generated-model URI, a synthetic import-header edit, conflicting replacements for the two copies of one source interval, a mixed-version action, and an A→B→A source-byte state at a newer monotonic version. This model does not represent a production LSP `WorkspaceEdit` or client capabilities.

For the in-flight control, the live server had opened the projected bad proof at version 1 and received a version-1 diagnostic request. The harness then deleted the Rust line that owned `missingProof` in an active scratch copy, about 0.14 ms after sending the request. The server settled about 2,754 ms after the request with the old open-buffer diagnostics. The source version had advanced to 2 and its hash changed from `4ee11307f8efb232f2dfa4098c3d775d44a4484a98a9cf63d2614e7488625bcf` to `2e27c2c8df36bdbef058443b560da76b50036a71b5a3f7423eef79441b3c1c44`. Applying the old corrective patch was rejected as `stale-source-or-projection`. The server was not sent a version-2 Lean `didChange`, so its version-1 response is expected; this test isolates the canonical Rust-source freshness check rather than claiming automatic server invalidation.

## Exact residuals

| IDs | New evidence | Still unresolved |
| --- | --- | --- |
| I025/I026 | Exact copied byte intervals and Unicode byte/scalar/UTF-16 coordinates; synthetic ranges excluded. | Actual Anneal parser, escaping/normalization, invalid UTF-8, zero-width border policy, negotiated alternate encodings. |
| I027/I028 | One doc block feeds two obligations; one generator's materialized proof text was checked in batch and opened unchanged in live Lean. | Production batch/live generator identity, many-to-one obligations, incomplete proofs/import mutations, elaborated-declaration equality. |
| I029/I030 | Two-range source patch passed; stale/mixed/conflicting/generated/synthetic controls rejected. | Real atomic editor transactions, snippets/import code actions, rename/resource ops, concurrent clients. |
| I031 | Actual rustc, Charon, Aeneas, Lean batch/LSP, and generated-model ranges classified without granting unsupported edit authority. | Integrated related-information policy, responsibility for scaffold/external dependency errors, source unavailable locally. |
| I032 | Source-owned map and stale deletion check for one fixture; prior projection property reports supply larger edit streams. | Production incremental map cost, formatter/edit-stream stress and map equality across actual Anneal syntax. |
| I059/I060 | Generated model stays read-only; lexical Aeneas links are navigation candidates; model rejects cross-URI edits. | Real hover/navigation/semantic-token and rename/workspace-edit requests, multi-file preconditions, partial clients. |
| I061 | None. | InfoView/RPC/widgets, goal display from Rust position, reconnect behavior. |
| I062/I063 | Fresh batch/LSP coordinate comparison and old live version after a canonical source deletion. | Client encoding negotiation, full versus incremental sync, autosave/format-on-save/watch/build loops, generated-file notifications. |

The Anneal editor UI remains gated. No run here authorizes an edit based solely on Charon spans, Aeneas comments, or Lean diagnostic locations.

## Evidence and replay

`support/probe.py` SHA-256 `694521d4e7f656bfdbbd75785e59e814e80b52606ed807fdd7dc6d13568f8bb3` is the self-validating replay. `support/results.json` SHA-256 `d290f01d3db7146cceebe862d317406787be98c5b3b2a00233c16609ee68900e` retains 11 stage calls, complete source/LLBC/generated/compiled/proof inventories, raw batch JSON, the LSP transcript and settled result, source maps, patch outcomes, and deletion timing. `support/artifacts/` retains rustc metadata and error source, LLBC, all Aeneas generated Lean files, locally compiled `.olean` modules, good/patched/error proof files, and the generated-model error file.

Replay with `python3 support/probe.py --work /absolute/absent/owned/path` on the pinned host. The work parent needs 15 GiB free. The script replaces package-local `support/artifacts/` and `support/results.json`, so copy the package before replay if preserving the acquired run. It asserts stage exits, compiler item/candidate counts, exact patch rejection, fresh batch/live diagnostic message equality, explicit coordinate offsets, and stale-source rejection after deletion. Raw LLBC order, generated absolute source comments, timings, and LSP notification order may vary; compare their structured evidence rather than raw hashes alone.
