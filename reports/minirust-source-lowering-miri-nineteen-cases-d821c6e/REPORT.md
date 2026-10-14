# Actual MiniRust lowering and Miri comparison: nineteen captured sources

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Nineteen source fixtures have captured Miri Tree Borrows outcomes. Seventeen
were actually lowered to emitted MiniRust JSON and interpreted under both
MiniRust Tree Borrows and Basic memory: twelve successful executions and four
UB controls agree with Miri; a valid wide-pointer union copy succeeds in Miri
but is rejected as UB by both MiniRust configurations. Two other sources stop
with lowering ICEs and have no MiniRust semantic result.

The union disagreement is supported by an actual emitted layout/chunk defect:
the 16-byte wide-pointer union preserves only its first eight-byte chunk. A
two-word field control preserves sixteen bytes and succeeds. The actual
source-generated single-variant enum has a checked Branch discriminator with
Invalid fallback, correcting the earlier synthetic Known-discriminator concern
for this source case.

This report is a static publication projection of completed execution evidence.
No compiler, interpreter, test, build, repair or new code experiment was run
while preparing it. The recorded stop remains in force. E05 and E06 remain
partial; no repair or optimized-MIR erasure experiment exists.

## Applicability

The source is MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, with the
earlier generated runtime associated with Specr
`15200eb5e676e2ee91f43bd79e674f8fc32e5348`. The restored compiler and Miri are
the requested nightly 2026-05-01, Rust commit
`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, for
`aarch64-apple-darwin`. Generated-runtime source hashes, exact component archive
identities, lockfiles and inspected upstream paths are preserved. This wave
does not claim fresh Specr generation or a verified source-to-runtime compiler.

The actual target passes minimize's pointer-size/alignment, endianness and
integer-alignment checks against `DefaultTarget`; it is a little-endian,
64-bit-pointer representation configuration. This is not x86 or AArch64 ISA
validation. No native subject program was executed in the captured experiments.
Invalid-source controls were interpreter subjects only.

### Recorded flags and configuration differences

All source commands use edition 2021, target `aarch64-apple-darwin`, debug
assertions off and panic strategy `unwind`. The separate compiler MIR emission
uses minimize's recorded defaults:

```
--cfg=miri -Zalways-encode-mir -Zextra-const-ub-checks
-Zmir-emit-retag -Zmir-opt-level=0 -Zmir-enable-passes=-CheckAlignment
-Zmir-preserve-ub -Zub-checks=false
```

Minimize inserts those defaults internally. Miri is invoked separately with
`-Zmiri-tree-borrows` and its own rebuilt sysroot; its default validation is
retained. The inspected Miri driver inserts `MIRI_DEFAULT_ARGS`, and minimize's
source describes its defaults as matching Miri. That comment is not a proof of
identical internal passes or validation. The full Miri default-argument
definition was not independently expanded by this reporting task.

MiniRust uses `--minirust-tree-borrows` with recorded default parameters
(`implicit_writes=false`), and also runs Basic memory without that option. No
MiniRust implicit-writes option or additional Miri parameter override is present
in the recorded commands. Do not infer complete cross-engine parameter equality
from the shared “Tree Borrows” name. Both model executions use the exact emitted
JSON, not a hand-built replacement. Per-command argument vectors, environment
records and return codes remain available in the evidence.

`rustc-input.mir` is a separate emit-only compiler control under the recorded
flags. Minimize receives the Rust source directly. This is not a captured
byte-for-byte internal MIR input to minimize or a certificate for its passes.

## Findings

### F1. The actual source-to-model corpus has seventeen comparisons and two lowering failures

Basis: captured execution + static identity checks.

| Case | MiniRust Tree / Basic | Miri Tree |
| --- | --- | --- |
| `smoke` | success / success | success |
| `union_wide_one_field` | UB / UB | success |
| `union_wide_two_word_control` | success / success | success |
| `wide_pointer_control` | success / success | success |
| `enum_single_zero` | success / success | success |
| `enum_single_invalid_one` | UB / UB | UB |
| `enum_pair_one` | success / success | success |
| `enum_pair_invalid_two` | UB / UB | UB |
| `library_split_cell` | success / success | success |
| `library_box` | lowering ICE; no model | success |
| `library_drop_count` | success / success | success |
| `library_drop_unwind` | lowering ICE; no model | success, expected caught panic |
| `upstream_pass_enum_direct_tag` | success / success | success |
| `upstream_pass_enum_niche_tag` | success / success | success |
| `upstream_pass_slice` | success / success | success |
| `upstream_pass_drop` | success / success | success |
| `upstream_pass_tree_borrows_cell_inside_struct` | success / success | success |
| `upstream_ub_inv_bool` | UB / UB | UB |
| `upstream_ub_enum_ub_discriminant` | UB / UB | UB |

[case-index.json](case-index.json) binds all nineteen source hashes, upstream or
owned origins, selected run groups, outcomes and evidence directories. Every
successful lowering has compiler MIR, actual lowering stdout, the identical
MiniRust JSON, execution streams and statuses. Reporting checks matched each
source to its inventory hash, each generated program to lowering stdout and
each recorded stdout/stderr hash to the raw stream. All seventeen public JSON
program files remain byte-identical to the actual emitted programs.

Miri's four UB controls exit 1; MiniRust's UB result convention exits 101. A
nonzero status is interpreted through its diagnostic and phase, not treated
uniformly as UB. In particular, the two lowering ICEs are outside the seventeen
semantic comparisons. Agreement here is bounded observation for these exact
sources/configurations, not equivalence of the interpreters or source adequacy.

### F2. The valid union copy exposes a one-word chunk for a two-word pointer

Basis: source + captured execution + derived diagnosis.

The owned [one-field union source](cases/union_wide_one_field.rs) initializes a
`*const [u8]` from a live three-byte array, copies its union through a non-inlined
identity function, then reads the same pointer field and uses its length and
third byte. Miri succeeds. Both MiniRust memory models report:

```
fatal error: UB: load at type Ptr(Raw { meta_kind: ElementCount }) but the data in memory violates the language invariant
```

The actual source MIR contains the union copy. Its raw SHA256 is
`42a8bafb7c383558deb03c16fad17bc192e15cc67ac407e75d21412ae46b0b22`.
The emitted program SHA256 is
`777d5f58831da2911bf7c9c3265f5edbd18a8af649f9a96d4e680458ceae3327`.
Both model stderr streams have raw SHA256
`a859ffe2bfb0e80addc18ab82e593a1ef8a4801d70f5445f5e1ffb03f78df6fc`.

The emitted union has size 16, alignment 8, the raw `ElementCount` pointer field
at offset zero, and chunks `[[0,8]]`. The
[two-word field control](cases/union_wide_two_word_control.rs) adds an unobserved
`[usize; 2]` field; its emitted chunks are `[[0,16]]`, and both model executions
and Miri succeed. A [direct wide-pointer copy](cases/wide_pointer_control.rs)
also succeeds. [representation-findings.json](representation-findings.json)
preserves the relevant JSON paths and exact extracted type shapes.

Pinned `chunks.rs:47` marks every `Type::Ptr` using only
`DefaultTarget::PTR_SIZE`. The union translation in `ty.rs:217–220` uses that
chunk calculation. The specification's `PtrType::as_wide_pair` represents
metadata-bearing pointers as two pointer-sized words. Its union encoder first
sets the entire union to Uninit, then restores only the listed chunks. Together
these source facts and controls explain the lost metadata word in this case.

This is a valid-source rejection/false positive in the tested translation-model
pipeline. It does not establish acceptance of an invalid source, a general
union theorem, or either direction of a source-safety reflection theorem. The
two model runs share this frontend/representation path and are not independent
confirmation of translation correctness. No pointer-layout repair was
implemented, built or tested; the proposed repair is not evidence.

### F3. The actual source enum rejects the invalid tag

Basis: actual generated program + captured execution.

The owned `#[repr(u8)] enum E { Only = 0 }` produces a one-byte enum with a tagger
at offset zero and a **Branch** discriminator: the interval `[0,1)` leads to
`Known 0`, while the fallback is `Invalid`. The discriminator itself is not an
unconditional Known value. Valid tag zero succeeds; reading invalid tag one is
rejected by MiniRust Tree, Basic and Miri. The two-variant tags and selected
upstream direct/niche enum controls also have the tabled outcomes.

This corrects the attempted transfer of an earlier synthetic Known-discriminator
concern to this actual source enum. It does not prove all enum/discriminator,
niche, padding or invalid-value translations adequate. Original programs and
diagnostics are retained rather than replaced by the correction.

### F4. Allocation and caught-unwind cases stop at a specific foreign-item ICE

Basis: source + captured operational failure.

Both `library_box` and `library_drop_unwind` first emit compiler MIR successfully.
Minimize then exits 101 with an internal compiler error at `bb.rs:790`, naming
the foreign allocator entry `alloc::alloc::__rust_dealloc`. The exact installed
`library/alloc/src/alloc.rs:128` calls that entry. Source inspection finds the
explicit `span_bug!` branch for foreign functions that lack MIR. The diagnostic
and both original stream/status sets are preserved.

These are lowering-tool failures with a diagnosed entry point. Neither has an
emitted model, so neither has MiniRust UB or unwind behavior to compare. They
are not blanket findings that Rust Box, allocation or unwinding is unsupported
by every tool or configuration. The failing lowering was not retried.

Miri independently succeeds on both. The caught-unwind fixture deliberately
panics with `OWNED_EXPECTED_DROP_UNWIND`, catches it, and checks that the outer
guard's Drop count is one. Its Miri process exits zero; the expected subject
panic is distinguished from the lowering compiler panic. The non-unwinding
`library_drop_count` and `library_split_cell` cases have actual successful
MiniRust executions, but do not discharge the missing allocation/unwind path.

### F5. The harness correction and stop are preserved as separate events

Basis: captured diagnostics + source inventory.

The first upstream Drop attempt named its dependency metadata
`intrinsics.rmeta`; rustc rejected the filename before subject MIR emission.
The owned harness was corrected to `libintrinsics.rmeta`, keeping the test
source unchanged. Fresh output was written to a distinct run group. The original
failure, old/new driver source hashes and corrected successful outputs are
retained. This was a harness defect, not a repaired upstream semantic result.
The selected upstream Drop test uses the pinned intrinsics helper; it is not
interchangeable with the real std Box/deallocation case.

The prior agent stopped on a parent instruction reporting an automated
cybersecurity-content flag. The exact flagged/interrupted operation is not
visible in the captured output. This report does not attribute it to a
particular source or operation and does not resume it. The checkpoint identifies
`upstream_ub_enum_ub_discriminant` as the final completed experiment; subsequent
pre-stop tools only inspected source. The publication task performs static
reading/copying/normalization only.

No isolated repair workspace, source patch, patched build/test, extended metadata
fixture, paired optimized-MIR erasure comparison or repair JSON comparison
exists. These remain unperformed work, not a successful outcome hidden by the
stop. The local source remains at the recorded upstream code; configuration
changes to exact-version path-source lock entries are separately inventoried.

## Boundaries

E05 remains partial: real source/MIR/lowering/model evidence exists, with two
lowering failures and a concrete representation disagreement, but relevant
first-bad-prefix operations have not been compared across actual MIR passes.
E06 remains partial: these nineteen Miri outcomes and seventeen model
comparisons do not cover general retags, protectors, wildcard/exposed provenance,
allocation reuse, zero-size ranges, races or all interpreter choices.

Unknown/unexamined matters include a general recursive union-chunk invariant;
the proposed repair across metadata forms, nested unions and padding; complete
allocation and caught-unwind lowering; matching validity/aliasing relations;
arbitrary source, library, compiler or target correspondence. The original
broader source-generality and source-safety goals are not replaced by corpus
agreement. The false positive alone supplies neither a false-acceptance example
nor a proof of safety reflection.

The exact automated flag operation remains unknown. No absence of a diagnostic
or failure to access a source is used to establish language unsupportedness.
This reporting task adds no fresh compiler/interpreter outcome. The copied
historical drivers are text evidence, not runnable public replay helpers.

## Evidence

- [case-index.json](case-index.json): nineteen sources, exact hashes, provenance,
  selected evidence locations and outcome totals. `cases/` preserves the selected
  fixtures and the necessary upstream intrinsics helper, not an upstream source
  mirror.
- `evidence/cases/`: original captured source MIR, all seventeen unchanged
  programs, lowering/execution stdout and stderr, separate command statuses and
  original result records. `evidence/historical-harness-failure/` retains the
  failed pre-MIR dependency-filename attempt.
- [source-evidence.json](source-evidence.json): inspected primary paths, full
  source revisions, hashes, generated-runtime source identities and tool identity
  limitations. Only four later result records captured the minimize binary hash;
  it matches the current statically read binary. Current minimize/minirun hashes
  are labeled current identities, not invented per-run historical measurements.
- [source-copy-revalidation.json](source-copy-revalidation.json): all 333
  inventoried workspace files still match their prepared copies and pinned
  originals, with only the recorded configured `tooling/Cargo.lock` difference.
  This is a static hash check; no compiler/build command is involved.
- [normalization-receipts.json](normalization-receipts.json): every projected
  captured file's raw and published SHA256/length plus exact token replacement
  counts. All seventeen program JSON files and nineteen source fixtures are
  unchanged. Diagnostics, status paths and some MIR display locations are
  normalized. Hash fields inside old statuses/results continue to name raw
  observations; the package manifest names the published bytes.
- `evidence/status/` and `evidence/logs/`: the earlier successful offline locked
  minimize/minirun build (19.748 s), minimize sysroot setup (11.933 s) and Miri
  sysroot setup (10.868 s). Dependency inventories retain 102 archive identities;
  archives, binaries, caches and sysroots are not published. Builder manifests,
  lockfiles and original exact local-path override inventories are retained.
- Primary mechanism sources: [union chunks](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/chunks.rs),
  [type translation](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/ty.rs),
  [representation specification](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md),
  [foreign-call lowering](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs)
  and the pinned [Miri driver](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/src/tools/miri/src/bin/miri.rs).

The source checkpoint is preserved in normalized form as historical evidence.
Its original private capture remains read-only. No Git, canonical, publication,
cleanup, network, build or subject-execution effect was performed in preparing
this package.

## Revalidation

The cheapest current check is static: verify this package's manifest, match
each source/model public hash, follow raw-to-public receipts, and compare the
retained classifications with exact statuses and diagnostics. A published
normalized MIR or log is a display copy; use its receipt when comparing it with
an original raw artifact. The generated JSON programs require no such adjustment.

A separately authorized future execution should use the exact compiler/Miri and
MiniRust/Specr/generated-runtime identities and recorded sysroot configurations.
Reconstruct an isolated capture layout from `source_relative_to_capture` in the
receipts. Resolve `@CAPTURE@`, `@RUST_TOOLCHAIN@`, `@MINIRUST_SOURCE@` and
`@GENERATED_RUNTIME@` to caller-selected physical paths; the public token strings
are not literal executable paths. The original statuses retain complete argument
vectors, and historical driver text explains internal/default flags and the
correct dependency filename. Do not substitute a current nightly, default
sysroot, memory model or optimized MIR while claiming the same subject.

The original stop and two lowering ICEs require their own disposition before
dependent repair/replay. This report authorizes no retry and claims none. A
future patch needs separate source identity, source-derived layout comparison,
negative controls and a fresh recorded result; it must retain the present
unrepaired disagreement and operational failures.
