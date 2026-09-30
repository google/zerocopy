# Copied empty Rust doc line, unsaved Lean insertion, and coordinate ownership

## Summary

A dependency-free Rust fixture compiled successfully with the locally installed pinned nightly. A hand-authored copier then supplied a Lean file with a synthetic header, a copied Unicode doc-comment payload, and a separately owned empty `///| ` payload line. In a direct Lean 4.30.0-rc2 server, a version-2 incremental insertion at that empty line produced `Unknown identifier missingEmpty` while the disk file retained the version-1 hash. Fresh batch `lean --json` on the exact version-2 bytes reported the same identifier error. The observed LSP range was zero-based line 3, UTF-16 columns 16–28; batch reported one-based line 4, scalar columns 15–27. The hand-authored map identifies the empty-line insertion with Rust byte 58, after its five-byte `///| ` prefix. Five invalid/unowned controls were rejected by the offline checker.

This adds a **bounded I025 component specimen**: an actual Lean versioned edit on a zero-length copied segment, with source-byte ownership checked independently. The bridge is not Anneal's parser or source map. I025 remains partial and product-gated; I026 receives border-policy context only. No editor client, generated obligation, or production Rust-to-Lean projection was exercised.

## Applicability

The acquired run used the local `nightly-2026-05-31-aarch64-apple-darwin` `rustc` executable with SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc` and local Lean 4.30.0-rc2 executable with SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. These hashes identify the binaries run; this package does not establish the source commit used to build either binary. The host was arm64 macOS, and the observed UTC date was 2026-09-30. Both tools were already installed locally; nothing was downloaded.

The construction copies bytes from two `///| ` Rust doc-comment lines into a Lean file after `import Lean\r\n\r\n`. The first payload is `#check "🙂é"`; the second has zero payload bytes. The host and projected files retain CRLF. The first Lean blank line is synthetic; the later blank line is explicitly owned by the second Rust doc comment. This choice of marker, parser rule and source ownership is an illustrative fixture, not an observation of Anneal syntax.

The [earlier compiler-backed bridge](../anneal-3731-compiler-backed-coordinate-bridge-2026-09-29/REPORT.md) copied one nonempty doc line and never sent `didChange`. The [source-owned diagnostic matrix](../anneal-3730-source-owned-projection-diagnostic-matrix-2026-09-29/REPORT.md) invalidated a Rust source line while Lean remained at version 1; it did not send a version-2 Lean change. The [projection property harness](../anneal-3730-projection-properties-2026-09-29/REPORT.md) already covers abstract empty-line coordinate round trips and conservatively rejects insertion at ambiguous segment borders. This report tests a unique, declared empty-line owner against a real Lean server; it does not present empty-line arithmetic or unsaved Lean editing as new general findings.

## Findings

### An empty copied payload has a source insertion anchor only with explicit ownership

The retained oracle was written before tool launch and hashed at acquisition start. It records Rust `Host.rs` SHA-256 `9e32bf3e46146fb293ba1cf06a5817c73d5088ec41ea8193a2c10a635fb3508e`, projected v1 SHA-256 `28f76f64a2d7a9d1b28f7df403fdf4a69ecebdc7ecc887cdc8cdb5e2ffa9f5b9`, and projected v2 SHA-256 `bcd5968dc5282d430a961ad40cfa1b84e244a1f3343e9942507f8639a73401c7`. The empty owned payload begins at host byte 58, zero-based host line 2, byte/scalar/UTF-16 column 5. Its projected insertion point is byte 33, zero-based Lean line 3, column 0 in all three units. Inserting the exact 32-byte UTF-8 text `#check ("🙂é", missingEmpty)` there yields the retained v2 bytes, while retaining the existing CRLF.

The copied nonempty line before it supplies an independent Unicode control: at the payload end the projected byte/scalar/UTF-16 columns are 16/12/13. In v2, `missingEmpty` starts at projected byte column 19, scalar column 15 and UTF-16 column 16. These coordinates follow exact UTF-8 source bytes and are checked against the retained files; the zero-length segment does not itself encode an editing policy.

The offline mapper accepts the empty-line insertion only when the projected offset, source hash, projected hash and document version match the declared owner. It rejects an insertion in the synthetic header, an insertion in the synthetic blank line, a position inside the owned line's CRLF, a version-2 request against the version-1 map, and a UTF-16 position inside the emoji surrogate pair. This is a deliberately conservative local policy. It does not show how Anneal would represent empty ranges, competing owners, or a production editor write.

### Direct Lean version-2 diagnostics agree with fresh batch on this token

The guarded sequence was Rust metadata compilation, one `lean --server` session, then fresh original and patched `lean --json` invocations. Rust exited 0; Lean server exited 0 after shutdown; batch v1 exited 0 and batch v2 exited 1 because of the intentional unknown name. The server opened disk-v1 bytes at document version 1, waited for settled diagnostics, then received one incremental `didChange` to version 2 at `(line 3, character 0)`. The disk file still had the v1 hash after that edit. Version-1 diagnostics contained only the expected information message for the Unicode `#check`; version 2 added `Unknown identifier missingEmpty` at UTF-16 line 3, columns 16–28. Fresh batch v2 reported the same error at one-based line 4, scalar columns 15–27. Its other informational message is not used as an error-location claim.

The raw client/server frames, JSON-RPC events, command arguments, process IDs, environment details, stderr, return codes, resource samples and source hashes are retained. The checker requires the matching `waitForDiagnostics` response to have a `result` and no `method`, and compares the final versioned diagnostic with the batch JSON token range.

### A first acquisition is preserved but excluded

An initial harness run exited within limits, but its `receive_until` routine matched a server-initiated refresh request by numeric ID as if it were the `waitForDiagnostics` response. It closed the server before settled version-2 diagnostics appeared. Its empty LSP sets are **invalid evidence**, even though its Rust and batch commands exited as expected. The raw first attempt and its resource trace are preserved under `attempt1/`; none of its LSP observations support the findings above. The corrected response discriminator was statically checked, a fresh admission passed, and a single final acquisition produced the reported diagnostics. No resource guard tripped in either acquisition.

## Boundaries

- This is one hand-authored exact-byte projection and one Lean versioned insertion. There is no Anneal V2 parser, projection, source map, obligation generator, editor client, or actual Rust edit application.
- The Rust compiler successfully accepted documentation; it did not check Lean proof semantics or connect the `#check` snippet to `pub fn probe`.
- The version-1 Rust source remained unchanged while Lean held v2 unsaved text. Host byte 58 is an illustrative insertion anchor under the version-1 map, not an authorized production patch after an independent Rust source change.
- The synthetic and CRLF controls are local policy checks, not protocol responses from Lean. The run does not address display-width inversion from Charon, negotiated UTF-8 LSP behavior, invalid UTF-8, concurrent clients, multiple empty owners, normalization by an editor, or generated files.
- Sampled process RSS can miss brief peaks between samples. The observed maxima were 6,432 KiB for Rust, 149,104 KiB for the server, and 1,155,872 KiB for the larger batch run. The minimum sampled reclaimable estimate was 29.9864%; minimum disk free was 17.424 GiB; maximum temporary work scratch was 10,127 bytes. All remained inside live limits.

## Evidence

`fixture/Host.rs`, `fixture/ProjectedV1.lean`, `fixture/ProjectedV2.lean` retain exact bytes. `prepare.py` defines construction and byte/scalar/UTF-16 predictions; `oracle.json` fixes them before execution. `probe.py` performs the guarded one-shot acquisition and `results.json` records the valid run (SHA-256 `99adb9571ff46b91c8813ff266cf79fe259dcc1b6248357683ce0e00697c0e72`). `raw/` holds Rust, Lean server and batch transcripts. `attempt1/` retains the excluded protocol-harness run. `check.py` verifies source hashes, exact copied segments and edit bytes, all four exit statuses, disk-v1 identity, versioned LSP/batch error coordinates, five negative controls, resource bounds, complete cleanup and the exclusion; `comparison.json` retains its expected summary. Running `python3 -B check.py` in this package passes offline.

The final acquisition's initial admission showed 31.5413% estimated reclaimable memory and 17.424 GiB free disk, above required 30% and 10 GiB. Live abort thresholds were below 20% reclaimable, below 10 GiB disk, above 512 MiB Rust process-group RSS, above 1.2 GiB Lean group RSS, above 100 MiB scratch, or over 30 seconds per process. The session completed and its temporary work directory was removed; retained fixture, raw and results files remain.

## Revalidation

Run `python3 -B check.py` for offline verification. For a new acquisition, copy `prepare.py`, `probe.py`, `check.py`, `fixture/`, and `oracle.json` to a fresh private directory, retain the same binary hashes or document changed subjects, and run `python3 -B probe.py` only after a fresh resource admission. The runner refuses to overwrite existing raw evidence. Compare diagnostic structures and source-byte hashes; absolute paths, PIDs, timings, and incidental information messages are not semantic invariants. Implemented Anneal projection/editor integration is still needed to test I025's product-level coordinate contract.
