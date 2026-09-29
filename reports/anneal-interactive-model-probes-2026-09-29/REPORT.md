# Bounded identity, projection, and generation-publication probes for Anneal

## Summary

Three small experiments support distinct contracts: URI/path or document-version identity alone collides across changed source/import state; source-map edits must reject synthetic gaps and compare the host/projection generation before applying; and atomic replacement of a mutable generation pointer does not make a multi-file read coherent unless the consumer pins one immutable generation directory. These are bounded model/filesystem results, not proof that a specific Anneal implementation follows or violates the contracts.

The Python harness checked ten identity mutations, 2,092 valid Unicode scalar boundaries, all 120 orderings of a five-event two-generation schedule, and a controlled APFS pointer-swap interleaving. Raw outcomes and replay scripts are included under `support/`.

## Applicability

The identity and schedule checks are executable finite models written with the Python standard library. Their state variables are drawn from the #3730/#3731 proposed Anneal pipeline: Cargo subject, source snapshot, Charon/Aeneas configuration, LLBC, generated source, Lake environment/import identity, projected document, version, worker, and RPC session. The chosen counterexamples model required distinctions; they do not encode Lean, Charon, Aeneas, Lake, LSP, or MCP internals.

The coordinate corpus uses CPython 3.14.7 and strings containing ASCII, non-ASCII BMP characters, supplementary characters, combining marks, tabs, CRLF, and LF. It checks valid Unicode scalar boundaries only; an LSP UTF-16 position in the middle of a surrogate pair is not invertible.

The publication experiment used a disposable directory on macOS 26.6.2 APFS. It atomically replaced a symlink with `os.replace` between reads of separately opened files. The test does not establish the semantics of other filesystems or Lake's own package/archive formats.

## Findings

### Result identity and cache reuse need different roles

The harness compared six keys: workspace/path; workspace/URI/version; projected-content hash; a limited document/import key; a broader semantic-content key; and a causal response identity that additionally includes workspace and worker/RPC incarnations. The ten mutations included same path with changed Rust bytes, same URI/version with changed proof bytes, same proof with changed imports, changed Cargo subject or backend configuration, changed prepared environment, A→B→A content with a later worker epoch, and RPC reconnection.

Path-only, URI/version, and proof-hash keys collided for their corresponding source, proof, import, and subject changes. A content-oriented key can still be reused when equivalent inputs recur, but the response must carry the current causal generation. The model therefore separates content identity used for cache reuse from the provenance/freshness tag attached to an answer. This is a derived design constraint from the finite examples, not a claim that one exact tuple is minimal.

Basis: **execution** of `support/model_probes.py`; **derived** interpretation of the enumerated cases.

### Valid Unicode scalar boundaries round-trip across UTF-8 and UTF-16 units

Across 59 deterministic strings, the harness checked 2,092 scalar boundaries. UTF-8 byte prefixes decoded back to the original scalar prefix, and UTF-16 code-unit counts matched the expected prefix length. Supplementary characters occupy two UTF-16 units; combining marks remain separate scalar/code-unit positions. This validates the conversion arithmetic used by the fixture, not any editor's coordinate negotiation or a Rust parser's annotation spans.

The piecewise fixture mapped authored segments and rejected positions in synthetic gaps. Its version/hash compare-and-swap control rejects a patch after either the host or projection changes, even if a stored offset still maps to a plausible location. The exact projection parser, completion edits, diagnostics, and formatter behavior remain untested.

Basis: **execution** of `support/model_probes.py`; **derived** for the safe-patch rule.

### Resolve and pin the generation before reading multiple files

The controlled reader first opened `Types.lean` through `current -> gen-A`. The publisher atomically replaced `current` with a link to `gen-B`; the reader then opened `Funs.lean` through the new pointer and observed a mixed A/B generation. A second reader resolved the symlink once to the immutable `gen-A` directory before the swap and read both files from that pinned directory; it saw a coherent old generation.

An incomplete `gen-C` stage missing `Funs.lean` remained unpublished and did not replace `gen-B`. The old generation remained readable after pointer replacement. Thus a final pointer swap is useful only with complete staging, consumer pinning, and retention until readers release the old generation; the pointer operation alone does not give a multi-file snapshot to consumers that resolve it independently for each open.

Basis: **execution** on APFS using `support/publication_probe.py`; broader Lake/build implications are **derived** and bounded by the filesystem fixture.

## Boundaries

- The finite identity model demonstrates collisions in chosen keys; it does not prove a particular production key is incomplete or that the listed full tuple is minimal.
- The projection fixture is hand-authored. No Rust annotation parser, Lean formatter, LSP client, macro expansion, or actual edit application was exercised here.
- The schedule model explores all permutations of five abstract events, not all states or schedules of an implementation. Its counterexamples do not establish the presence of a race in Anneal.
- The APFS probe uses symlink indirection. It does not test Lake's trace/hash cache, mmap behavior, artifact-cache restoration, crash durability, or network filesystems.
- This report does not cover human/agent studies, cross-platform publication, high-concurrency resource sweeps, or independent reproduction.

## Evidence

- `support/model_probes.py` — executable identity ablation, Unicode coordinate corpus, patch-boundary controls, and bounded schedule enumeration.
- `support/model-probes.json` — exact counts and results emitted by the harness.
- `support/publication_probe.py` — controlled APFS generation-pointer swap.
- `support/publication-fixture/` — disposable A/B generations and unpublished partial C generation.
- `support/publication-fixture/publication-probe.json` — per-file hashes and observed interleaving.

Issue alignment: #3730 A01–A08, B02–B05, K01, F15, N01/N02/N07/N09/N12, and #3731 I011, I025–I032, I045, I051–I053, I097, I133–I135, I145, and I151 are only partially informed by these probes. The complete per-investigation ledger is in the companion #3730/#3731 coverage report.

## Revalidation

Run `python3 support/model_probes.py` and `python3 support/publication_probe.py` from the package root. Review the assertions and emitted JSON. The filesystem probe should be repeated on each supported filesystem before generalizing atomic rename or pointer behavior. Replace the hand-authored segments with a real parser/projection implementation before treating the coordinate results as product evidence.
