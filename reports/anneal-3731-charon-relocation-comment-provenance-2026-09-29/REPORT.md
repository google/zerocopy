# Charon source-location and inert-comment effects across LLBC and Aeneas Lean

## Summary

On one pinned macOS toolchain, moving identical Rust bytes between two roots changed exactly the local source-file path in a schema-aware LLBC comparison, and changed only the source-path documentation line in Aeneas's generated Lean. Appending a comment after the function changed the complete source contents embedded in LLBC but produced byte-identical Lean at the same path. A repeated original extraction had the same normalized LLBC and Lean as the first. These observations separate reusable model text from the provenance needed to associate it with an editor buffer.

## Applicability

The four executions used the Charon and Aeneas binaries identified in `REPORT.json`, Rust `1.98.0-nightly (f8a08b688 2026-05-30)` on `aarch64-apple-darwin`, and a dependency-free one-function Rust library. The source revisions in metadata are the release-pair coordinates used elsewhere in this corpus; the binary SHA-256 values pin the executables actually invoked and are not independent build attestation. Charon ran `rustc --preset aeneas --dest-file <private-output> -- <absolute-src> --crate-type lib --crate-name probe --edition 2021`. Aeneas ran `-backend lean -dest <private-output>/lean -no-progress-bar -sequential <llbc>`. All outputs were private to their invocation. The `CHARON_TOOLCHAIN_IS_IN_PATH=1` environment selected the installed nightly.

The sequence was original source at `origin-root/src/lib.rs`, byte-identical source at `other-root/src/lib.rs`, an appended line comment at the original path, then restored original bytes at the original path. Thus the last case is A→comment→A at one source locator, with different LLBC destination paths for the two A cases. The appended comment was after the only function and did not move its line/column span.

## Findings

### Relocation carries through both artifacts

Both source files had SHA-256 `f665adfda34d93ee8dd8db1ee7d798dc449d7e498bffd31634eec59d8f243b94`. After replacing only `translated.options.dest_file` and sorting the three keyed name-map arrays (`item_names`, `short_names`, `assoc_item_names`) by serialized key, the *sole* LLBC JSON value difference was `translated.files[0].name.Local`. Charon exited 0 with `has_errors: false` in both cells. Aeneas exited 0 and emitted `Probe.lean` in each. The Lean files differed in exactly the `Source: '<path>', lines 1:0-1:48` line of the generated declaration comment; after replacing that one line, all remaining bytes matched. The raw Lean hashes were `1faf6714...` and `adbae3eb...`.

Basis: **execution**, retained `support/artifacts/{origin,relocated}/` and `support/results.json`, checked by `support/check.py`. The comparison retains target information, declaration order, spans, bodies, attributes and all other fields; it does not assert that every possible path move has this effect.

### Inert appended comment changes LLBC source identity without changing emitted Lean

At the same `origin-root/src/lib.rs` locator, appending `// Inert fixture note after the function.` changed the source SHA-256 to `174c26fe...`. Under the same narrow LLBC normalization, the only JSON value difference was `translated.files[0].contents`; local function source text, span and translated body remained equal in this fixture. Aeneas's `Probe.lean` was byte-identical to the original (`1faf6714...`). Restoring the original source yielded no normalized LLBC differences and the same generated Lean bytes, despite another private LLBC destination.

Basis: **execution**, retained `support/artifacts/{origin,comment,repeat}/` and exact diff paths in `support/results.json`. The full SHA-256 values are in that record and verified against retained bytes.

### Consequence for a generated workspace key

A raw LLBC digest distinguishes source relocation, destination, and this appended comment. In this fixture the Aeneas executable generated equal Lean after the comment edit, and its path relocation affected a comment rather than the definition body. Therefore a cache or deduplication scheme can consider narrower *model-content* reuse only if it separately maintains current source/provenance identity and re-emits or remaps path-bearing generated comments as needed. A raw generated-tree hash will distinguish these two relocated Lean outputs even though their declaration text matches after the documented one-line replacement. This is a **derived** design implication from the exact observed diffs, not evidence that arbitrary comments or path-sensitive Rust builds are harmless.

This supplies a bounded I079 and I148 control and is relevant to I009/I074 source snapshot identity. It does not mark those rows complete: build scripts, macros, `include_*`, paths used by `env!`, multiple files, edited in-function comments, and downstream Lake cost were not tested.

## Boundaries

- Only one safe function, one crate, one target, one preset, one Aeneas backend, and sequential invocations were examined. The probe does not establish general Charon or Aeneas determinism, translation correctness, or Lean acceptance.
- The comment was placed after the function. A comment that changes line positions, macro input, documentation attributes, or build-time source reads can affect more fields or semantics.
- Relocation used absolute source paths under one report-owned tree. It did not move a Cargo workspace, path dependencies, generated files, or build scripts; no shadow-workspace fidelity claim follows.
- The three-map sorting is specific to the keyed arrays observed in this schema. It is a comparison procedure, not permission to erase provenance or normalize unknown fields. Raw artifacts remain retained.
- The probe did not measure Lake traces, Lean command-prefix reuse, proof obligations, or cost of regenerating path comments.

## Evidence

- `support/probe.py`: complete offline commands, pinned executable hashes, four source states, private output creation, process exit checks, and structural comparison. The runner uses only Python's standard library and installed local binaries; it deletes only its own `support/work/` and `support/artifacts/` before a replay.
- `support/results.json`: rustc version, per-case source/LLBC/Lean hashes and byte counts, exit codes/streams, local-file records, exact normalized diff paths, and Lean-equality matrix.
- `support/artifacts/<case>/probe.llbc` and `support/artifacts/<case>/lean/Probe.lean`: raw Charon and Aeneas evidence for `origin`, `relocated`, `comment`, and `repeat`.
- `support/check.py`: read-only verification of retained hashes, tool schema/options, successful outcomes, path relationship, embedded source bytes, all normalized diff paths, Lean equality, and the provenance-only Lean difference.
- Executed binaries: Charon SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; Aeneas SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`. Paired source release coordinates are in `REPORT.json`; these source coordinates were not independently inspected for this report.

## Revalidation

Run `python3 -B support/check.py` to verify the retained specimen without executing a compiler. On a host with the exact local binaries and nightly, run `python3 -B support/probe.py`, then the checker. For a different Charon or Aeneas pin, rerun the four cells and inspect the full field-level LLBC diffs and generated Lean diff before carrying forward either narrow equality; in particular, do not accept a changed output solely because a path or comment appears in the raw diff.
