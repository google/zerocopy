# Translation output goldens and revision diffs

## Summary

A three-function macOS probe passed through Charon and Aeneas. Repeated raw LLBC JSON differed only in item-name map ordering in this sample; pretty LLBC and generated Lean were byte-identical. The report proposes a schema-aware golden corpus and revision-diff harness without treating textual stability as a correctness proof.

## Applicability

One dependency-free Rust library, Charon 0.1.210 with the Aeneas preset, Aeneas nightly-2026.06.03, and the pinned aarch64-apple-darwin Rust nightly. The source report records exact commands, output hashes, and binary provenance. Related corpus reports: [charon-ullbc-llbc-schema-nightly-2026-06-03](../charon-ullbc-llbc-schema-nightly-2026-06-03/REPORT.md), [charon-cli-invocation-modes-0-1-210](../charon-cli-invocation-modes-0-1-210/REPORT.md), [aeneas-rust-to-lean-translation-nightly-2026-06-03](../aeneas-rust-to-lean-translation-nightly-2026-06-03/REPORT.md).

## Findings


Scope: current Anneal redesign, with a small local Charon/Aeneas probe. This is research and a proposed test design, not a decision that a particular translation is sound. Anneal's [principles](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/PRINCIPLES.md) and [design contract](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/DESIGN.md) require complete accounting of behavior and explicit trust before a Rust-level verification claim. Matching goldens can detect drift; it cannot establish source/model correspondence or UB freedom.

### Directly observed baseline

The checked-in `anneal/Cargo.toml` pins Charon `nightly-2026.06.03`; `anneal/Cargo.lock` resolves it to `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`. The local Charon source checkout is at that commit. The local Aeneas source checkout is `ac9f1bc5262a5e4ff1e24ca78617121382202727`; `anneal/flake.nix` names the Aeneas release `nightly-2026.06.03`. These source checkouts and the release binaries are separate artifacts, so the source commit is supporting provenance, not proof of the binary's build identity. The binary reports Charon `0.1.210`; `aeneas -version` reports `unknown`. The paired local Rust compiler reports `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, host `aarch64-apple-darwin`, LLVM `22.1.6`.

The current Anneal `src/scanner.rs` defines one LLBC path per target and an artifact slug based partly on the manifest path. This is an output collision control, not an appropriate cross-checkout golden name: the same fixture in two checkout roots can have different slugs. The historical `v1/` implementation is not used as current design authority here.

#### Reproducible small probe

All probe files are in `support/translation-goldens`. The Rust source is:

```rust
#![allow(dead_code)]

pub fn checked_add(x: u32, y: u32) -> Option<u32> {
    x.checked_add(y)
}

pub fn choose(flag: bool, left: u32, right: u32) -> u32 {
    if flag { left } else { right }
}

pub fn bump(value: &mut u32) {
    *value = value.wrapping_add(1);
}
```

From the repository root, with the fixture saved as `support/translation-goldens/probe.rs`, the commands were:

```sh
# Set PATH to the pinned local binaries identified above.
CHARON_TOOLCHAIN_IS_IN_PATH=1 charon rustc --preset aeneas \
  --dest-file support/translation-goldens/probe.llbc \
  -- support/translation-goldens/probe.rs \
  --crate-type lib --crate-name probe --edition 2021
charon pretty-print support/translation-goldens/probe.llbc
mkdir -p support/translation-goldens/lean
aeneas -backend lean \
  -dest support/translation-goldens/lean \
  -no-progress-bar support/translation-goldens/probe.llbc
```

All commands exited successfully. Charon's final pretty print had `if move _4` with both branches for `choose`, a call to opaque `core::num::{u32}::checked_add` for `checked_add`, and a dereference, `wrapping_add`, and write through `&mut u32` for `bump`. Aeneas emitted a 1,219-byte `Probe.lean` with `Result` definitions. In particular, `bump (value : Std.U32) : Result Std.U32` returned the updated value, and `choose` became a Lean `if`. The emitted source comments retained the fixture path and line ranges. The probe did **not** typecheck the Lean output, prove a theorem, or exercise unsafe Rust.

The serialized LLBC is JSON with top-level `charon_version`, `translated`, and `has_errors` fields. In this probe `translated` contained target information, source files and contents, translation options, item-name maps, declarations, and declaration order. Its target was `aarch64-apple-darwin` with eight-byte pointers. The Aeneas preset recorded `reconstruct_fallible_operations`, `reconstruct_asserts`, `index_to_function_calls`, and `ops_to_function_calls` as enabled. Charon's own CLI help cautions that index-to-function-calls may introduce UB by creating references; any such transformation must be evaluated under Anneal's design contract before relying on a golden for a Rust-level claim.

At one fixed `--dest-file`, repeated Charon runs produced different raw JSON SHA-256 digests (`3b29f4aeaa6abce2bc8fe2e6c7c3ccde063a7555eaf4d7e4488ed1c12d655511` and `b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098`). The only textual JSON difference between those two saved runs was the order of two `translated.item_names` entries (`Fun: 1` and `Fun: 2`). A second run to a different `--dest-file` also changed the embedded `translated.options.dest_file` value. In contrast, the two pretty-printed LLBC outputs were byte identical (1,542 bytes, SHA-256 `0d671705f8d15327fca8355c3e1dfb8cccf7d9f100e21996356e042e46250d27`), as were the two generated Lean files (SHA-256 `767acaeb0288a57cfdabdb1c276cbf0f7d9a85a0558f367601f5082c60349bca`). Sorting the keyed name-map arrays by their serialized key made the two JSON values equal. This is one fixture and a few runs; it shows a concrete nondeterminism to control, not a general guarantee that pretty LLBC or Lean output is deterministic.

Upstream source already offers useful precedents. Charon's `charon/tests/ui.rs` compares pretty-printed `.out` files in CI, `charon/tests/cargo.rs` covers Cargo-specific behavior, and `charon/tests/crate_data.rs` asserts structured AST facts. Aeneas `tests/README.md` describes committed generated backend files and separate verifier checks. Its single-file runner calls `charon rustc --preset=aeneas` before Aeneas. Those tests are upstream regression evidence, not Anneal's own coverage of its configuration and trust boundary.

### Proposed golden corpus

Keep each Rust fixture small, dependency-free where possible, with a stable crate name and a manifest that records the exact Rust target, edition, flags, Charon preset/options, Aeneas options, and expected outcome. Use a fixed path inside the test sandbox, and key each committed case by fixture name plus target/configuration rather than Anneal's path-derived artifact slug. For each success case, commit the Rust source, final Charon pretty LLBC, a canonical structured LLBC projection, and generated Lean. Preserve full raw `.llbc` as a run artifact for debugging and Aeneas replay, but avoid a byte-for-byte raw JSON golden until nondeterministic map ordering is addressed upstream or normalized by a schema-aware adapter.

| Fixture class | Translation feature to pin | Additional assertion |
| --- | --- | --- |
| Scalars and branch | checked/wrapping arithmetic, `if`, `match`, casts | Preserve operation kind and branch arms; record overflow settings. |
| Ownership and borrows | move, shared borrow, mutable borrow/reborrow, lifetime-bearing signature | Preserve read/write place and Aeneas's functional update interface. |
| Aggregates | struct/enum construction and match, tuple, array, slice indexing | Preserve variants, discriminants, bounds behavior, and index transformation. |
| Loops and early exits | `while`, `break`, `return`, panic path | Preserve control flow and termination/partiality representation. |
| Generics and calls | trait method/associated type, monomorphization, opaque external call | Preserve resolution and distinguish an opaque signature from a translated body. |
| Effects and layout | `Drop`, raw pointer read/write, alignment, uninitialized storage, target-specific layout | Use explicit expected failure or coverage assertions when unsupported; never treat omitted behavior as passing. |
| Build identity | `cfg`, feature flag, target architecture, separate library/bin targets | Assert each requested build variant and target is represented in the emitted artifact. |

For every case, test the exact boundary the golden claims to cover: Charon exit status and `has_errors`; expected item names and bodies; Aeneas exit status and expected Lean declarations; and, where a Lean golden is claimed to compile, a separate Lean check. A successful process exit plus a file is insufficient if items disappear. Reject unsupported features explicitly with an expected diagnostic and source span; do not bless an empty or partial translation as a success golden. Include a few metamorphic probes: repeat a run, move the fixture root, reorder independent functions, and change one operator. These should demonstrate which output differences are presentation noise and which are semantic.

The canonical structured projection should retain target information, source span identity, item signatures, bodies, opacity, generated obligations, and declaration relationships. It may normalize only fields whose meaning is established: JSON object key order, map-as-list entries keyed by stable IDs (such as `item_names`), and designated sandbox path prefixes or the output destination option. Do **not** sort statement sequences, declaration order, branch arms, or arrays merely to make diffs pass. Do **not** erase target, feature, MIR stage, preset, source contents, or diagnostics. Keep the raw LLBC beside a failure so canonicalization errors can be investigated. An adapter should fail on an unknown schema or unrecognized volatile field rather than silently dropping it.

### Proposed revision-diff harness

1. Pin two toolchain manifests: baseline and candidate Charon commit/release, Aeneas commit/release, Rust nightly and target, plus binary hashes. Never label an `aeneas -version` value of `unknown` as a commit identity. Record host and every invocation flag.
2. For each fixture, run the baseline and candidate in isolated, identical fixture roots with fixed destination names. Bound parallelism and time; keep builds limited to the small corpus. Save source, raw LLBC, pretty LLBC, canonical projection, diagnostics, and generated Lean for both sides.
3. Compare stages independently: Rust→LLBC and a fixed LLBC→Lean. When both LLBC schema versions are accepted by both Aeneas revisions, add a 2×2 matrix (old/new Charon output through old/new Aeneas) to localize drift. If a revision cannot deserialize the other format, report an explicit compatibility gap and compare supported diagonal pairs only; do not convert that gap into a translation success.
4. Emit a machine-readable inventory of item names, opacity/body presence, operation classes, source spans, target/feature configuration, and error state, plus concise textual diffs of pretty LLBC and Lean. Classify changes as map/format ordering, source-span/path, Charon semantic change, Aeneas model change, coverage loss/gain, or compatibility/tool failure. Any missing item, weakened body, new opaque call, lost error, or changed safety-relevant operation receives manual review before golden update.
5. Update goldens only through a reviewable diff with the manifest and a short explanation of each intentional semantic change. Keep the previous revision artifacts available to reproduce a regression. Check generated Lean separately from textual equality; a stable string can still fail to typecheck after a library update.

This harness tests regression and attribution. The trust log still needs to identify which Charon/Aeneas/Rust/Lean semantics are assumed or checked, and a result must not imply complete verification when translation coverage, typechecking, or correspondence evidence is absent.

### Limits and immediate next step

The probe covers three safe functions on one macOS target and one Charon/Aeneas release pair. It does not establish behavior for Cargo workspaces, alternate targets, unsafe operations, drops, generated code, or cross-revision compatibility. A practical first implementation is a tiny harness for the three observed functions plus one expected-failure case, with schema-aware LLBC normalization and a repeat-run determinism check. Add the larger fixture classes only as each has a clear observable invariant and review path.

## Boundaries

The direct experiment covers three safe functions, one host/target, one tool pair, and no Lean typecheck. Unsafe semantics, broad translation patterns, Cargo workspaces, and cross-revision runs were not exercised; revision comparison is a proposed harness.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. Executed-probe support material is included under `support/translation-goldens/`; local home/checkout prefixes are redacted in text artifacts.

## Revalidation

Run the small fixture and repeat Charon serialization with fixed and changed destinations, then compare raw JSON, a schema-aware LLBC projection, pretty LLBC, and Aeneas output. The package support contains the fixture and observed outputs; verify all pinned executable hashes first.
