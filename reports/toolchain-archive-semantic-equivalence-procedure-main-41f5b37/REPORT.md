# Toolchain-archive semantic-equivalence comparison procedure

## Summary

Two Anneal toolchain archives can differ byte-for-byte without differing in the prepared toolchain that Anneal consumes. Tar member order, tar headers, and compression are obvious examples. The reverse is more dangerous: two archives can have similar layouts, matching version labels, or matching Lake trace captions while differing in proof-critical binaries, module artifacts, dependency identity, or cache state.

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the useful comparison is therefore a **layered, fail-closed procedure** rather than one hash comparison or one recursive directory diff. The procedure first fixes the comparison domain: same supported system, same intended Aeneas/Rust/Lean/Mathlib identity graph, and the same consumer contract. It then compares, in order:

1. compressed archive bytes;
2. decompressed tar bytes and tar metadata;
3. the extracted filesystem graph;
4. proof-critical file classes and Lake state using class-specific rules; and
5. the consumer behaviors that the equivalence claim actually promises.

The procedure permits only differences with a demonstrated non-semantic role. For the current Anneal/Lake stack, examples include compression bytes and some saved Lake trace captions. It does **not** classify differing compiler binaries, differing `.olean` families, differing source/configuration bytes, differing executable modes, or unknown trace fields as equivalent merely because a smoke test passes.

This distinction is especially important for current Anneal. The omnibus archive intentionally rewrites and vendors Lake state, removes write bits, normalizes selected modification times, patches Linux binaries, and packages platform-specific Rust, Lean, and Aeneas assets. Lake can also accept prepared outputs through `--old` modification-time fallback after dependency hashes change. A comparison that ignores these dimensions can certify the wrong property.

The final result should use one of four outcomes:

- **archive-byte-identical** — the complete compressed archive bytes are identical;
- **payload-identical** — the extracted filesystem graph and all semantically relevant metadata/bytes are identical, even if container/compression bytes differ;
- **equivalent-under-declared-consumer-contract** — every difference is explicitly classified as non-semantic for the declared contract, all required exact-byte gates pass, and the contract-specific execution probes pass; or
- **not established** — any proof-critical difference, unknown field, unvalidated platform change, or missing required probe remains.

“Not established” is the normal outcome for an unexplained difference. The procedure is designed to preserve that uncertainty instead of converting similarity into a semantic claim.

## Applicability

The archive-construction facts apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. At that revision Anneal stages three top-level trees—`aeneas/`, `lean/`, and `rust/`—then performs platform-specific cleanup, rejects recognized absolute producer roots in selected Lake traces, resets selected Aeneas source/configuration mtimes, removes write bits recursively, creates an uncompressed tar, and compresses it with Zstandard. The local and CI archive variants intentionally use different compression levels.

The Lean/Lake rules apply to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), the toolchain selected by the current Anneal dependency graph.

The procedure is for comparing two archives that are intended to be substitutable for the **same declared consumer contract**. Before comparing payloads, record at least:

- the exact Anneal source revision;
- host/system or target-triple identity;
- Aeneas source/release identity;
- Charon and Rust identities relevant to the installed Aeneas toolchain;
- Lean identity;
- Mathlib and transitive Lake dependency identities;
- archive variant and construction path; and
- the consumer operations the equivalence claim covers.

If those identities intentionally differ, the task is an **upgrade or migration validation**, not same-contract archive equivalence. The corresponding release-upgrade checklists and cross-version validation procedures should govern that comparison.

The default comparison domain is one supported system at a time. Current Anneal selects different release assets and fixed-output hashes across `x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, and `aarch64-darwin`. Lake also treats native products as platform-sensitive. No cross-platform equivalence should be inferred from this procedure unless the relevant artifact classes have independent portability evidence.

This report defines the procedure from source and existing exact-pin reference evidence. It does not report a fresh two-archive execution and does not claim that any particular pair of current archives is semantically equivalent.

## Findings

### Begin with a declared equivalence contract, not a directory diff

“Same toolchain” is underspecified. A useful comparison must state what substitutions are allowed to remain observationally invisible.

For current Anneal, a conservative contract is:

> Either archive may replace the other on the same supported system, in a fresh installation root, without changing the selected tool identities, dependency graph, proof-critical source/configuration, Lean/Lake build identity, generated proof behavior, read-only/offline expectations, or the success/failure behavior of the declared archive-consumption tests.

This contract deliberately excludes properties such as tar member order, compression level, and producer-root text in a Lake trace caption when the pinned Lake implementation does not use that caption for freshness.

A narrower contract may ignore more observables, but it must say so before comparison. For example, a contract that ignores replayed Lake log text cannot later use log equality as evidence of semantic identity. Conversely, a contract that promises diagnostic reproducibility must treat those logs as observable.

The procedure stores this contract in the comparison record before classifying differences. That prevents post-hoc redefinition of “semantic” to excuse an unexpected mismatch.

Basis: **derived** from the current archive construction and exact-pin Lake state model.

### Gate the comparison on exact identity and platform facts

The current Anneal toolchain is a graph, not one version string. The installed archive combines an Anneal-selected Aeneas release, a separately fetched Rust toolchain, a separately fetched Lean toolchain, Aeneas's own Charon/Rust/Lean pins, and a Mathlib/Lake dependency graph.

The first comparison gate therefore records immutable identities rather than comparing display versions alone. Matching `nightly-2026.06.03` or `v4.30.0-rc2` labels is insufficient if the underlying source revision, build configuration, release asset, or platform differs.

For the current baseline, the relevant graph includes:

- Anneal `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`;
- Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- Aeneas-pinned Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Rust `nightly-2026-05-31`;
- Lean `v4.30.0-rc2` / `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`; and
- Mathlib `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6` plus its resolved transitive graph.

If one archive intentionally carries a different member of this graph, stop the same-contract procedure and classify the comparison as an upgrade/migration evaluation. Do not hide the difference behind equal output from a small test.

Basis: **current reference synthesis** of Anneal's exact version-coupling graph.

### Compare container bytes before extracting, but do not stop at a mismatch

For each archive, record size and a cryptographic digest over the complete compressed file. If local bytes are available, direct byte comparison is stronger still.

If the compressed files are identical, the archive-container comparison can terminate successfully: the two files are the same input to extraction. The broader consumer contract may still depend on external state, but there is no archive-content difference left to explain.

If compressed bytes differ, decompress both without modifying them and compare the complete raw tar streams. Equal raw tar bytes isolate the difference to compression. Current Anneal already has two legitimate compression configurations: local `omnibus-archive` defaults to Zstandard level 1, while `omnibus-archive-ci` uses level 6. Compression inequality is therefore not evidence of toolchain semantic inequality.

If raw tar bytes differ, inspect the tar layer before extraction. Record member order, path, entry type, link target, mode, ownership metadata, size, modification time, and payload digest. Current Anneal's ordinary `tar -cf $out *` does not canonicalize every reproducibility-sensitive tar field. A raw-tar mismatch can therefore come from container metadata even when the extracted payload is otherwise equivalent.

Do not classify that mismatch as harmless yet. Proceed to the extracted-tree comparison, because modes, symlinks, hardlink relationships, and selected mtimes can affect current Anneal behavior.

Basis: **source** in `anneal/flake.nix`; **current reference** on omnibus-archive byte reproducibility.

### Compare the extracted filesystem as a typed graph

Extract both archives with the same trusted extraction procedure into separate fresh roots. Do not compare through an already-populated Exocrate installation: current local-archive setup can return an existing versioned installation without opening the newly supplied archive.

Construct an inventory for every path containing at least:

- relative path;
- file type;
- regular-file cryptographic digest and size;
- symlink target;
- hardlink identity if the archive represents hardlinks;
- executable and write permission bits; and
- modification time, recorded separately from byte identity.

Reject unexpected special file types unless the declared contract explicitly supports them.

Path-set, type, symlink-target, and execute-bit differences are material by default. Write permissions are also material for current Anneal because archive production deliberately removes write bits and archive-consumption tests use that read-only state as part of the prepared-toolchain contract.

Do not require all mtimes to match exactly. Current Anneal intentionally uses timestamps for two different purposes, and exact equality is not the relevant semantic condition for one of them. Instead, preserve the timestamp data for the Lake-specific comparison described below.

Ownership metadata belongs in the evidence even if the chosen extraction path does not preserve it. It may be classified as non-semantic only after the actual installer/extractor behavior for the declared contract establishes that it cannot affect the resulting installation.

Basis: **current reference** on archive read-only behavior, local-archive trust semantics, and timestamp/Lake reuse.

### Treat source, configuration, and dependency files as proof-critical inputs

For source files, `lean-toolchain`, Lake manifests, Lake package configuration, and other dependency selectors, exact byte equality is the default automatic-acceptance rule.

A schema-aware semantic comparison can replace byte equality only when all of the following are established:

1. the file format and consumer are known at the pinned revision;
2. the normalization preserves every consumer-visible value;
3. ordering, comments, whitespace, or path spelling being ignored are actually non-semantic for that consumer; and
4. the normalized form is retained as comparison evidence.

An unexplained source/configuration difference means **not established**. It is not enough for both archives to report the same high-level version.

This rule is intentionally stricter than text similarity. These files determine imports, dependency materialization, compiler options, and build identities; a small textual change can change proof behavior while leaving top-level layout unchanged.

Basis: **derived** from the current toolchain-version graph, Lake materialization, and archive construction.

### Require exact bytes for proof-critical binaries in the automatic path

Rust, Charon, Aeneas, Lean, Lake, `leantar`, native plugins, object files, static/shared libraries, and executables sit on or near the proof-generating/checking path. For the same-contract automatic equivalence path, differing bytes in these classes are material.

Version output is not an adequate substitute for byte identity. Two binaries can report the same version while differing in build flags, patches, runtime linkage, or implementation.

If proof-critical native bytes differ, classify the pair as **not established under the strict same-contract procedure**. A separate upgrade/migration investigation may establish a weaker consumer-equivalence claim using source provenance, build recipes, ABI checks, and representative execution. That is a different claim and should not be silently promoted to archive semantic equivalence.

The same-platform gate matters here. Lake explicitly includes platform identity in native-object and shared-library build traces, and current Anneal assembles platform-specific release assets.

Basis: **current reference** on cross-platform artifact portability and exact toolchain coupling.

### Treat Lean module artifacts as coherent proof-critical families

A `.olean` is not a portable logical certificate. At the selected Lean revision it is a native serialized `ModuleData` image. Module-mode builds can also produce `.olean.server` and `.olean.private` parts that share storage with preceding parts and must be loaded as a coherent prefix.

For automatic same-contract equivalence:

- require exact bytes for the complete `.olean` family and other proof-critical Lean module outputs that are retained by the archive;
- require the same Lean/toolchain identity and relevant Lake dependency state; and
- keep module artifacts paired with their matching Lake metadata rather than comparing extensions in isolation.

A differing `.olean` is not accepted merely because both files import successfully in one smoke test. Such a mismatch crosses into compiler/artifact validation and needs a separate investigation.

Likewise, Lake's adjacent `.hash` files are not cryptographic integrity commitments. They are 64-bit Lake hashes and may be trusted instead of recomputed in some modes. The comparison should compute its own cryptographic digest over the artifact bytes and, when execution evidence is required, force Lake rehashing rather than treating equal sidecars as proof of equal artifacts.

Basis: **current reference** on `.olean` format/identity and Lean/Lake artifact hashes.

### Compare Lake traces by field semantics, not by whole-file text

Lake trace files are not one uniform semantic object.

For ordinary `BuildMetadata` traces, compare at least:

- `depHash`;
- `outputs`;
- `synthetic`; and
- the presence/identity of the output artifact to which the trace belongs.

Treat saved `inputs` captions and `log` separately. At the selected revision, the core freshness path compares the current dependency hash with saved `depHash`; it does not reconstruct that hash from saved captions. Changing a caption can therefore alter provenance without changing the freshness decision. Saved logs are also outside the hash comparison, but Lake can replay them, so they are observable if diagnostic reproducibility is part of the contract.

Do **not** apply that rule to every `*.trace`. Compiled package configuration uses a different `ConfigTrace` schema whose identity fields and persisted options can affect configuration reuse and re-elaboration. A path-like string there can be operational state.

Accordingly:

- parse each known trace schema;
- compare fields according to their consumer role;
- permit a difference only when the pinned consumer proves that field non-semantic for the declared contract; and
- reject unknown schemas or unknown differing fields.

Current Anneal's producer-root path scan is useful evidence of path neutrality, but it is not a semantic-equivalence check. Whole-file textual path rewriting likewise cannot serve as a generic equivalence normalization.

Basis: **current reference** on Lake trace relocation/rewrite boundaries and trace/hash artifacts.

### Compare Lake freshness mode, not only the final artifact bytes

Current Anneal deliberately vendors Lake dependencies in a way that changes dependency hashes, then uses `lake --old build` to preserve prepared outputs. Under the pinned Lake implementation, an output may be accepted either because its dependency hash matches or because old mode accepts an mtime fallback.

These are not equivalent evidence. Lake marks mtime-only freshness separately and does not treat it as cacheable.

For every prepared output whose reuse matters to the declared contract, record:

- the current dependency hash;
- the saved `depHash`;
- whether reuse is `hashUpToDate` or `mtimeUpToDate`;
- the input/reference mtime used by the fallback; and
- the output mtime.

If either archive relies on old-mode fallback, compare the **ordering predicate**, not raw timestamp equality. The relevant current module path requires the input/reference time to be strictly older than the output. Equalized timestamps can therefore break reuse even when every file byte is otherwise identical.

A comparison that reports “same `.olean` bytes” but causes one archive to rebuild and the other to reuse is not equivalent under a consumer contract that promises prepared-cache reuse.

Basis: **current reference** on archive timestamp normalization and Lake old-mode behavior.

### Keep installation identity separate from archive identity

Current `--local-archive` setup does not hash the supplied local archive into Exocrate's installation namespace. If the versioned installation directory already exists, setup may return it without opening the newly supplied archive at all.

Therefore:

- never compare two archives by installing A and then asking setup to “install” B into the same managed namespace;
- use fresh, separate installation roots or extract the archives directly;
- compute comparison digests independently of Exocrate; and
- preserve which archive bytes produced which extracted tree.

Otherwise the second run can accidentally inspect the first archive's already-installed tree and report a false equivalence.

Basis: **current reference** on Exocrate local-archive trust/checksum semantics.

### Run consumer probes only after static differences have been classified

Execution probes are confirmation for a declared contract, not a substitute for understanding proof-critical byte differences.

For a pair that passes the static exact-byte gates and differs only in explicitly allowed classes, run both archives through the same fresh-root consumer matrix. For current Anneal that matrix should include, as applicable:

1. install/extract each archive independently;
2. verify expected read-only/executable permission properties;
3. make the producer/staging root unavailable;
4. invoke the archived Lean/Lake/Aeneas toolchain from each fresh root under the same controlled environment;
5. exercise the archive-consumption workspace/test path with the same source input;
6. record whether Lake reuses or rebuilds each relevant prepared target and by which freshness mode;
7. compare success/failure, generated proof-critical source where applicable, and resulting diagnostics under the declared contract; and
8. if offline execution is part of the contract, run inside an actual network-denied or network-observed environment rather than inferring network silence from path dependencies alone.

A passing test matrix cannot certify an unexplained compiler or `.olean` mismatch. It can, however, validate that a difference already justified as non-semantic—such as compression bytes, container ordering, or an explanatory trace caption—does not violate the declared consumer behavior.

Basis: **derived** from current archive-consumption, relocation, offline, and Lake-reuse evidence.

### Produce a difference ledger, not a single Boolean

The comparison result should preserve each observed difference with:

- path or archive field;
- artifact class;
- old and new cryptographic identities;
- whether the difference is proof-critical;
- the rule used to classify it;
- supporting source/reference evidence;
- required execution probe, if any; and
- final disposition.

Then compute the archive-level result from the ledger:

| Outcome | Required condition |
| --- | --- |
| `archive-byte-identical` | Complete compressed bytes are identical. |
| `payload-identical` | Extracted path/type/link/mode/content graph is identical and every semantically relevant timestamp relation matches; container-only differences may remain. |
| `equivalent-under-declared-consumer-contract` | Identity/platform gates pass; every payload difference has an explicit non-semantic rule; all proof-critical exact-byte gates pass; every required probe passes. |
| `not-established` | Any unexplained, proof-critical, platform-changing, or unprobed required difference remains. |

Do not choose the strongest result merely because a weaker probe passes. For example, a successful Lean invocation cannot turn differing Lean binaries into `payload-identical`, and matching tar member lists cannot turn differing `.olean` bytes into semantic equivalence.

This ledger is the durable evidence that allows a later agent to understand why two non-identical archives were—or were not—accepted.

Basis: **derived** synthesis of the comparison rules above.

## Boundaries

**No current archive pair was executed.** This report defines a source-grounded procedure. It does not claim current local and CI archives, independently rebuilt archives, or archives from different hosts are semantically equivalent.

**No universal program-equivalence theorem.** `equivalent-under-declared-consumer-contract` is parameterized by an explicit consumer contract and exact baseline. It is not a theorem that two arbitrary compiler/toolchain trees are indistinguishable for all programs.

**No automatic acceptance of differing proof-critical bytes.** Different compiler, verifier, Lean module, source, or configuration bytes require a separate upgrade/migration argument. Finite smoke tests do not establish universal semantic equality.

**No cross-platform default.** Native artifacts and current package selection are platform-sensitive. Compare within one supported system unless a narrower artifact class has independent portability evidence.

**No blanket timestamp normalization.** Exact mtime equality is not generally required, but current Lake old-mode reuse can depend on strict input-before-output ordering. The comparison must preserve the relation that the actual consumer uses.

**No blanket trace normalization.** Ordinary `BuildMetadata` captions and logs differ from operational output state and from compiled-configuration traces. Parse and classify known fields; reject unknown differing fields.

**No checksum inference from Exocrate local setup.** A local archive can populate the same managed namespace without contributing its bytes to the namespace identity, and later setup can bypass the supplied source. Compare archive bytes and extracted trees independently.

**No process-wide offline guarantee without execution evidence.** Path-vendored dependencies and an environment-cleared consumer reduce known network paths, but they do not deny sockets. A contract that includes network silence needs network isolation or observation.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary Anneal source:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.
  - Archive staging and the `aeneas/`, `lean/`, `rust/` top-level payload.
  - Linux ELF patching/stripping.
  - producer-root trace scan.
  - final Aeneas source/configuration mtime normalization.
  - recursive removal of write bits.
  - raw tar construction.
  - Zstandard level distinction.
  - structural archive-layout check.

Current `reference` evidence:

- `reports/anneal-toolchain-version-coupling-main-41f5b37/REPORT.md`, blob `91ac8612cc400e531363fde5c870abaded6b7eb7`: exact version/revision/dependency graph and duplicated selector boundaries.
- `reports/anneal-omnibus-archive-byte-reproducibility-main-41f5b37/REPORT.md`, blob `fc8efde016747587d53224b41f3e90c32ba187de`: final tar non-canonicalization, local/CI compression distinction, and paired-build boundary.
- `reports/anneal-archive-read-only-behavior-main-41f5b37/REPORT.md`, blob `8bf004ea28e08ce855bffcaa47aab1ce6f1cac00`: payload write-bit invariant and installed-tree boundaries.
- `reports/anneal-archive-timestamps-lake-reuse-v4-30-0-rc2/REPORT.md`, blob `0c860874507245a88d8aea57ff9b71ef3d200290`: hash-first versus `--old` mtime freshness and strict timestamp ordering.
- `reports/anneal-offline-installation-execution-main-41f5b37/REPORT.md`, blob `90b4d82bec82549f786a90d7c52c7cbb68a051c1`: local installation, path-vendored dependency graph, controlled environment, and network-denial boundary.
- `reports/exocrate-local-archive-trust-checksum-main-41f5b37/REPORT.md`, blob `cfe5e974a792ce82319aab7eda4233da55cb7359`: local archive bytes are outside Exocrate namespace/checksum identity and existing-target resolution can bypass the source.
- `reports/lake-trace-relocation-rewrite-boundaries-v4-30-0-rc2/REPORT.md`, blob `96a177e6eccaedd37da4aecec5b8d008f0c312c5`: field-level semantics of `BuildMetadata`, `ConfigTrace`, and path rewriting.
- `reports/lean-lake-trace-hash-artifacts-v4-30-0-rc2/REPORT.md`, blob `0711960b59e1366dcbecdda7764be16bf50501c5`: Lean identity in Lake traces, per-artifact Lake hashes, and non-cryptographic sidecar boundary.
- `reports/lean-olean-format-identity-v4-30-0-rc2/REPORT.md`, blob `cd5b8d2da578f08b5540d097c20c3e5ff96e408e`: native `.olean` serialization, coherent module-part family, and build-freshness boundary.
- `reports/lean-lake-cross-platform-artifact-portability-v4-30-0-rc2/REPORT.md`, blob `065d325b6a3e8b34a5f42c04bdaae83c1791df22`: platform-sensitive native outputs and the absence of a blanket cross-platform module-artifact guarantee.

Evidence roles are **source**, **current reference synthesis**, and **derived procedure**. There is no fresh **execution** evidence in this report.

## Revalidation

To apply the procedure to two concrete archives A and B:

1. **Freeze the contract and baseline.** Record the exact source revisions, target system, expected dependency graph, archive construction variant, and consumer operations whose equivalence is being claimed.
2. **Hash complete inputs.** Record file sizes and SHA-256 digests of A and B. If bytes are directly available, also compare them byte-for-byte.
3. **Compare decompressed tar streams.** Record raw-tar digests. If they differ, emit a normalized tar-entry inventory before extraction.
4. **Extract independently.** Use separate fresh roots. Record path, type, symlink/hardlink identity, mode, mtime, size, and SHA-256 for every regular file.
5. **Build the difference ledger.** Classify every mismatch using `comparison-procedure.json`. Unknown file classes and unknown trace fields remain `not-established`.
6. **Recompute proof-critical identities.** Do not trust Lake `.hash` sidecars as cryptographic evidence. Hash the underlying files independently. Parse known Lake trace schemas instead of diffing them as undifferentiated text.
7. **Check prepared-state freshness.** For retained Lake outputs, record current/saved hashes and whether the result is hash-current or accepted only through old-mode mtime fallback. Verify strict input-before-output ordering where the fallback matters.
8. **Run the declared consumer matrix.** Use a fresh root for each archive. Make producer roots unavailable. Use the same controlled environment and identical input. Record reuse/rebuild decisions, proof-critical generated outputs, success/failure, and contract-visible diagnostics.
9. **Add network enforcement if promised.** If “offline” means process-wide no network, execute under network denial or trace network operations. Do not infer it from vendored paths.
10. **Assign the weakest justified outcome.** `archive-byte-identical`, `payload-identical`, `equivalent-under-declared-consumer-contract`, or `not-established`.
11. **Preserve the evidence.** Retain both archive digests, normalized inventories, difference ledger, trace-field comparisons, commands, environment, output hashes, and logs.

Re-run the procedure after any change to Anneal archive construction, Aeneas/Charon/Rust/Lean/Mathlib identities, Lake trace schemas, `.olean` serialization, Exocrate installation semantics, or the consumer contract itself.
