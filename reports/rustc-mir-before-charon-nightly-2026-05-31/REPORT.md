# rustc MIR stages and unreachable code before Charon at nightly-2026-05-31

## Summary

At the Charon revision pinned by Aeneas for Anneal's 2026-05-31 Rust
toolchain, Charon does **not** consume a literal transcription of Rust source and
does **not** normally consume rustc's optimized MIR for the current crate.
Charon's default MIR level is `Promoted`; the `Aeneas` preset does not override
that choice. For a local function, Charon therefore requests
`tcx.mir_promoted`: MIR after THIR-to-MIR lowering, rustc's initial CFG
simplification, constant promotion, and a second CFG simplification, but before
borrow checking's post-analysis cleanup, drop elaboration, runtime lowering, and
the main MIR optimization pipeline.

This matters for coverage. Even rustc's earliest query named `mir_built` has
already run `SimplifyCfg::Initial`. That pass always calls
`remove_dead_blocks`, which retains only CFG blocks reachable from
`START_BLOCK` and rewrites block indices. Thus source that was lowered into a
disconnected MIR block can disappear before Charon's default extraction. This is
not the same as constant folding: for an ordinary `if false { ... }`, the MIR
builder emits a `SwitchInt` with distinct then/else successors, and at the
built/analysis phases `SimplifyCfg` deliberately preserves switch reads. The
constant-condition optimizer that turns such a switch into a goto runs later in
optimized MIR and requires MIR optimization level at least 1. Charon sets
`mir_opt_level = 0` and `mir_preserve_ub = true`.

Charon applies a second reachability boundary. Its MIR-to-ULLBC translator starts
with MIR `START_BLOCK` and discovers blocks only by translating successor
references. Disconnected MIR blocks are therefore not translated even if a rustc
body happens to contain them. A **reachable** MIR `Unreachable` terminator is
not silently dropped: Charon translates it to
`Abort(UndefinedBehavior)`. After translation, Charon's own transformations can
make blocks dangling; before final ULLBC/LLBC serialization it performs another
DFS from Charon block 0 and removes any such unreachable blocks.

Consequently, absence of an operation from final LLBC is not by itself evidence
that the operation was absent from the Rust source. It may have been removed by
rustc's pre-analysis CFG cleanup or excluded by Charon's reachability traversal,
or made unreachable and removed by Charon's later transformations. Conversely,
a syntactically constant branch is not generally proof that the branch has
already disappeared at Charon's default promoted-MIR boundary.

The stage is different for non-local bodies. Charon's source says only optimized
MIR is generally available for dependency functions, with CTFE MIR used for
globals and const functions; a local request also falls back to optimized MIR if
the requested earlier body has already been stolen. Any coverage argument must
therefore identify both the item provenance and the actual MIR level rather than
assuming one uniform rustc representation for every translated body.

No fresh rustc or Charon execution was performed for this report. The findings
are based on the exact compiler/Charon source plus rustc's checked-in MIR golden
tests. The **Revalidation** section specifies a small executable matrix for a
surface that can run the pinned toolchain.

## Applicability

The Charon subject is
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
the Charon revision pinned by the Aeneas release selected by the examined Anneal
configuration. Its `rust-toolchain` names `nightly-2026-05-31`.

The rustc source examined is
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
That source revision is from the 2026-05-31 nightly toolchain era and was used to
inspect the rustc-private queries and passes Charon calls. As with the companion
Cargo report, this observation environment did not independently prove a
reproducible byte-for-byte mapping from Anneal's downloaded static Rust
distribution archive to this Git revision. The exact source claims below are
therefore claims about this immutable rustc source revision; Charon's exact
private-API calls and matching toolchain date establish why it is the relevant
source subject.

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/flake.nix` sets `rustDate = "2026-05-31"`. The current V2 CLI is
still incomplete, so this report does not claim that a current end-user Anneal
command has exercised every path described here. It records the external
rustc/Charon behavior that Anneal's selected toolchain makes relevant.

Unless stated otherwise, “default Charon MIR” means Charon with no explicit
`--mir` and without `--precise-drops`. `TranslateOptions::new` chooses
`MirLevel::Promoted` in that case. The `Aeneas` preset changes a number of
Charon transformations but does not set `options.mir`, so it retains
`Promoted`. `--precise-drops` raises the minimum to `Elaborated`.

The report distinguishes four Charon `MirLevel` values:

- **Built** — rustc `mir_built`, immediately after MIR lowering plus rustc's
  initial MIR lints and `SimplifyCfg::Initial`.
- **Promoted** — rustc `mir_promoted`, after constant promotion,
  `SimplifyCfg::PromoteConsts`, and coverage instrumentation; Charon documents
  this as the MIR used by borrow checking.
- **Elaborated** — rustc `mir_drops_elaborated_and_const_checked`, after
  borrow checking, analysis cleanup, drop elaboration/runtime lowering, and
  runtime cleanup.
- **Optimized** — rustc `optimized_mir`, after the runtime optimization
  pipeline, subject to compiler flags and pass-specific enablement.

These are implementation stages at the pinned revisions, not stable public rustc
APIs.

## Findings

### Charon hooks rustc early so it can still request pre-borrowck MIR

Charon's rustc driver installs its translation callback in
`Callbacks::after_expansion`. The source comment explains why: borrow checking
requires promoted MIR, and computing promoted MIR steals the built MIR; Charon
currently needs access to early MIR levels, so it performs extraction before the
ordinary MIR-based analysis callbacks proceed.

The callback timing does not mean Charon receives MIR “as of expansion.”
Charon invokes rustc queries from that callback. Those queries themselves build
MIR and run the passes associated with the requested level. An early callback can
therefore request promoted or even elaborated MIR and cause the corresponding
query pipeline to execute.

Charon's driver also globally configures rustc for MIR preservation:

- `always_encode_mir = true`;
- `mir_opt_level = Some(0)`;
- `mir_preserve_ub = true`;
- `CheckAlignment` explicitly disabled in `mir_enable_passes`.

The rustc option description says `mir_preserve_ub` keeps place-mention
statements and reads in trivial `SwitchInt` terminators that are interpreted by
tools such as Miri, and implies MIR optimization level 0.

Basis: **source** — Charon
`charon/src/bin/charon-driver/driver.rs`; rustc
`compiler/rustc_session/src/options.rs`.

### The Aeneas preset uses promoted MIR by default

Charon's `MirLevel` enum exposes Built, Promoted, Elaborated, and Optimized.
`TranslateOptions::new` computes:

`options.mir.unwrap_or(MirLevel::Promoted)`

and only raises that choice to at least Elaborated when `precise_drops` is set.
The `Preset::Aeneas` branch enables Aeneas-oriented output transformations such
as assertion/fallible-operation reconstruction and trait simplifications, but
does not set `options.mir` or `precise_drops`.

Thus `--preset aeneas` without an explicit MIR override consumes **Promoted**
MIR for local bodies.

Basis: **source** — Charon `charon/src/options.rs`.

### `mir_built` has already simplified the CFG and removed dead blocks

rustc's `mir_built` query first calls `build_mir_inner_impl`, which lowers
the compiler's typed representation into a MIR `Body`. It then runs MIR-level
lints followed by `SimplifyCfg::Initial`.

`SimplifyCfg` is not gated on a positive MIR optimization level. Its default
`is_enabled` is true, and the `mir_built` invocation allows optimizations.
The pass performs local CFG simplifications and then unconditionally calls
`remove_dead_blocks`.

`remove_dead_blocks` computes the blocks reachable from `START_BLOCK`, removes
every block outside that reachability set, deduplicates equivalent reachable
empty-`Unreachable` blocks, and rewrites successor block IDs.

rustc's own source describes why this is not merely a code-generation
optimization. Dead blocks can contain MIR that is ill-typed under the normal
rules because Rust type checking permits arbitrary types in source regions whose
end is unreachable. The source explicitly warns that `SimplifyCfg` is one of
the few optimizations run on built/analysis MIR and can affect MIR analysis; it
must preserve UB and nondeterminism at these phases.

The practical boundary is therefore:

**THIR/MIR lowering → initial MIR lints → `SimplifyCfg::Initial` (including
dead-block removal) → the value exposed as `mir_built`.**

A Charon request for even `MirLevel::Built` cannot recover the removed CFG
blocks through `mir_built`.

Basis: **source** — rustc
`compiler/rustc_mir_transform/src/lib.rs::mir_built` and
`compiler/rustc_mir_transform/src/simplify.rs`.

### Promoted MIR performs another reachability cleanup

`mir_promoted` steals the built body and runs:

1. `PromoteTemps`;
2. `SimplifyCfg::PromoteConsts`;
3. coverage instrumentation;

then transitions the body to the initial Analysis MIR phase.

Because every `SimplifyCfg` invocation calls `remove_dead_blocks`, Charon's
default promoted body has passed the reachability cleanup twice: once in
`mir_built` and once after constant promotion.

Promotion itself can replace selected temporaries with promoted constants and
remove assignments/storage/drop operations associated with promoted temporaries.
Accordingly, promoted MIR is not simply built MIR plus a side table of promoted
bodies.

Basis: **source** — rustc
`compiler/rustc_mir_transform/src/lib.rs::mir_promoted`,
`promote_consts.rs`, and `simplify.rs`.

### Elaborated MIR crosses the borrow-analysis/runtime boundary

If Charon requests Elaborated MIR, rustc first ensures borrow checking and
liveness have run, steals the promoted body, and calls
`run_analysis_to_runtime_passes`.

That pipeline performs materially semantic lowering:

- post-borrowck analysis cleanup;
- removal of false edges/fake analysis artifacts and user type annotations;
- further CFG simplification;
- drop elaboration and related drop/runtime transformations;
- coroutine state transformation where applicable;
- intrinsic lowering;
- removal of place mentions;
- another pre-optimization CFG simplification.

rustc's `cleanup_post_borrowck.rs` explicitly says it removes information that
is no longer relevant after analysis/borrow checking: false edges,
`AscribeUserType`, fake reads/borrows, coverage markers, and user type
annotations. The surrounding source comments say that after the analysis cleanup
passes, lifetime analysis based on borrowing can no longer be performed.

This is why the Charon `MirLevel` comment calls Elaborated “the first MIR to
include all the runtime information”: it has crossed from analysis-oriented MIR
into runtime-oriented MIR, including explicit drop behavior, while losing
analysis-only structure.

Basis: **source** — rustc
`mir_drops_elaborated_and_const_checked`,
`run_analysis_to_runtime_passes`, and
`cleanup_post_borrowck.rs`; Charon `options.rs`.

### Optimized MIR is a distinct fallback/dependency boundary

For a local real item, Charon first tries the requested MIR query. If the
corresponding early body has already been stolen, Charon falls back to optimized
MIR.

For non-local definitions, Charon's source says the earlier MIR levels are not
generally retrievable. It uses:

- optimized MIR for non-global functions when rustc reports MIR available;
- CTFE MIR for globals and const functions where appropriate.

Charon enables `-Zalways-encode-mir` so dependencies compiled during the
Charon/Cargo invocation carry MIR more broadly. Its source explicitly notes an
exception for the prebuilt standard library, where only the MIR rustc ordinarily
encodes—such as const items and generic/inlineable functions—is available.

Therefore “the MIR Charon sees” is not one global stage. A local current-crate
body normally uses promoted MIR under the Aeneas preset, while dependency bodies
can enter through optimized or CTFE MIR. A local body can also fall back to
optimized MIR if query stealing makes the requested stage unavailable.

Basis: **source** — Charon
`charon/src/bin/charon-driver/translate/get_mir.rs`.

### Charon's rustc flags suppress major optimization-only unreachable propagation

rustc's optimized-MIR pipeline contains transformations that can erase additional
control-flow distinctions. In particular:

- `UnreachablePropagation` propagates unreachable successors backward through
  gotos/switches and is enabled only at MIR optimization level at least 2.
- `SimplifyConstCondition` replaces a constant `SwitchInt` or successful
  constant assertion with a goto; the instances used in the main optimization
  pipeline are wrapped in a minimum optimization level of 1.
- later CFG simplification removes blocks made dead by those optimizations.

Charon sets MIR optimization level 0 and `mir_preserve_ub = true`. Therefore
those optimization-only transformations are not the normal explanation for code
missing from a local default promoted body.

This does **not** imply that optimized MIR under Charon is byte-identical to
Elaborated MIR. The optimized pipeline still contains required or independently
enabled passes, Charon explicitly disables `CheckAlignment`, and encoded MIR
from a prebuilt dependency may have been produced under another compilation
configuration. Charon's own comment that optimized MIR is “sensibly the same”
as elaborated because it disables the optimizations it can should be read as an
engineering approximation, not a format-equivalence guarantee.

Basis: **source** — rustc `run_optimization_passes`,
`unreachable_prop.rs`, `simplify_branches.rs`,
`pass_manager.rs`; Charon `driver.rs` and `options.rs`.

### A literal constant `if` branch survives the default promoted-MIR boundary

rustc's MIR builder lowers an ordinary `if` by evaluating the condition into a
temporary and terminating the condition block with a two-way branch to separately
lowered then/else blocks. The generic condition path constructs
`TerminatorKind::if_`, which is a `SwitchInt`.

For a literal such as:

```rust
if false {
    f();
}
```

the condition is represented by a constant value in a temporary, but the CFG
still contains distinct then/else successors.

At Built and Analysis MIR, `SimplifyCfg` deliberately does **not** replace a
`SwitchInt` merely because its successor structure could be simplified in a way
that removes an operand read; `preserve_switch_reads` is true at these phases,
and Charon additionally requests `mir_preserve_ub`. More importantly for a
literal false branch with distinct successors, CFG reachability sees both
successors as reachable because it is structural reachability, not value-range
evaluation.

The separate `SimplifyConstCondition` optimization is what evaluates a constant
switch operand and changes the switch to a goto. rustc's checked-in
`tests/mir-opt/simplify_if.rs` and corresponding golden diff preserve exactly
this specimen: immediately before
`SimplifyConstCondition-after-inst-simplify`, `main` still contains
`_1 = const false` followed by a `switchInt` whose false arm skips the call;
the pass then rewrites it to a goto. That optimization is not run at Charon's
default Promoted boundary.

Thus “the branch condition is compile-time constant” and “the branch is absent
from the MIR Charon normally translates” are different claims.

Basis: **source** — rustc MIR builder
`builder/matches/mod.rs::then_else_break_inner`,
`simplify.rs`, `simplify_branches.rs`, and the checked-in MIR test/golden
`tests/mir-opt/simplify_if.*`.

### Structurally unreachable source tails can disappear much earlier

The MIR builder deliberately creates `Unreachable` terminators and fresh
continuation blocks around expressions of the never type and other control-flow
constructs. Source after an unconditional exit can therefore initially exist in
a MIR block with no path from `START_BLOCK`.

`SimplifyCfg::Initial` removes such disconnected blocks structurally, without
needing value-based constant propagation. rustc's checked-in
`simplify_cfg.main.SimplifyCfg-initial.diff` demonstrates this class of change:
the initial pass collapses goto chains and deletes multiple blocks that have no
remaining path from the entry while retaining the live loop/return/cleanup CFG.

Accordingly, source text after an unconditional `return`, an unconditional
divergence, or another lowering that leaves a disconnected continuation can be
absent from even `mir_built`, and therefore from Charon's default Promoted
input.

Basis: **source** + **checked-in generated evidence** — MIR builder
`expr/into.rs`, rustc `SimplifyCfg`, and
`tests/mir-opt/simplify_cfg.*`.

### Reachable MIR `Unreachable` is semantic, not “dead code”

rustc documents `TerminatorKind::Unreachable` as a terminator whose execution is
undefined behavior. A block ending in `Unreachable` can itself be reachable
from `START_BLOCK`; “unreachable terminator” therefore must not be confused
with “unreachable basic block.”

Charon's terminator translation preserves this distinction:

`rustc MIR Unreachable → ULLBC Abort(UndefinedBehavior)`.

It likewise translates an unwind action that rustc marks `Unreachable` into an
undefined-behavior abort.

The checked-in rustc `unreachable_diverging` MIR test illustrates why this
matters: optimized MIR can propagate `Unreachable` backward through paths known
to end in uninhabited/diverging control flow. Charon's local default promoted
path avoids that opt-level-2 propagation, but any reachable `Unreachable`
already present remains a semantic endpoint that Charon records.

Basis: **source** — rustc `syntax.rs`; Charon
`translate_bodies.rs`; rustc checked-in
`tests/mir-opt/unreachable_diverging.*`.

### Panic/unwind edges are part of CFG reachability

rustc MIR terminators that can panic carry an `UnwindAction`. `Assert`
represents a dynamic check whose failure initiates a panic; calls, drops, and
inline assembly can likewise have unwind behavior. Cleanup unwind targets are CFG
successors and participate in structural reachability.

At the Promoted stage, borrow-checking-oriented false edges/unwind structure can
also still be present. Charon's source explicitly notes that `FalseEdge` occurs
in promoted MIR but not optimized MIR and translates a false edge using only its
real target. Charon translates cleanup unwind targets to ordinary ULLBC block
references and maps `Continue`, `Unreachable`, and `Terminate` unwind
actions to explicit ULLBC unwind/abort behavior.

Later Aeneas-preset Charon transformations can resugar assertions and fallible
operations. Charon's own option documentation warns that
`reconstruct_fallible_operations` loses unwinding information. That is a
**post-extraction Charon transformation**, not evidence that rustc's promoted MIR
lacked the unwind path.

This report records the stage boundary; a complete semantic account of panic,
abort, and unwind behavior remains a separate #3720 subject.

Basis: **source** — rustc MIR `syntax.rs`; Charon
`translate_bodies.rs`, `options.rs`, and transformation pipeline.

### Charon independently walks only MIR blocks reachable from the entry

Charon's MIR-to-ULLBC body translation does not iterate over
`mir_body.basic_blocks` and copy every entry.

It:

1. registers only rustc `START_BLOCK`;
2. pops registered blocks from a work queue;
3. translates each block;
4. registers new blocks only when a translated terminator/unwind action refers to
   them;
5. stops when that successor-driven work queue is empty.

This implements another structural reachability filter. If an input MIR body
contains a disconnected block, that block is not copied to ULLBC even before any
Charon transformation pass runs.

This filtering is semantically different from translating a reachable block
whose terminator is `Unreachable`: the latter block is discovered through a
predecessor edge and its UB terminator is translated.

Basis: **source** — Charon
`charon/src/bin/charon-driver/translate/translate_bodies.rs::translate_body`,
`translate_basic_block_id`, and `translate_terminator`.

### Final ULLBC/LLBC undergoes a third reachability cleanup

Immediately after MIR translation Charon can print “ULLBC after translation from
MIR.” It then runs a substantial transformation pipeline: insertion/cleanup
passes, selected inlining, assertion/fallible-operation reconstruction, constant
simplification, goto-chain merging, local cleanup, and other resugaring.

Those transformations can make blocks dangling. Near the end of unstructured
body cleanup, Charon runs `filter_unreachable_blocks`. The implementation does a
DFS from Charon block 0, retains only visited blocks, renumbers them, and rewrites
block IDs.

The source comment specifically says passes such as assertion reconstruction can
cause dangling blocks. The filter runs before the “Final ULLBC before
control-flow reconstruction” point and therefore before ULLBC serialization as
well as before ULLBC→LLBC reconstruction. Both ordinary final ULLBC and LLBC have
passed this Charon reachability filter.

Basis: **source** — Charon
`charon/src/transform/mod.rs` and
`normalize/filter_unreachable_blocks.rs`.

### Final LLBC absence cannot be used as source-text coverage evidence

Combining the boundaries above yields a concrete coverage rule.

A source construct may be absent from final LLBC because:

1. it never entered the compiled configuration at all (for example, conditional
   compilation; covered by a separate #3720 subject);
2. THIR→MIR lowering represented it indirectly rather than preserving its source
   syntax;
3. `SimplifyCfg::Initial` removed its disconnected MIR block before
   `mir_built`;
4. `SimplifyCfg::PromoteConsts` removed a block made unreachable during
   promotion;
5. a different MIR level was used, especially optimized/CTFE MIR for a
   dependency;
6. Charon's successor-driven initial body translation never reached the block;
7. a Charon transformation made the block unreachable and the final DFS removed
   it.

Therefore “not present in LLBC” is not a mechanically valid synonym for “no such
Rust source exists.” A source-completeness claim must separately account for the
source/configuration and the transformations that justify omission.

For **behavioral** verification, an omitted truly unreachable source path may be
semantically harmless because it cannot execute. That is a different claim and
requires confidence that the reachability/lowering transformation is faithful.
This report establishes where omission occurs; it does not by itself prove
end-to-end semantic preservation of rustc or Charon.

Basis: **derived** from the exact source behavior above.

## Boundaries

- **No fresh rustc/Charon execution was performed.** The structural conclusions
  are from exact source. The report additionally cites rustc's checked-in MIR
  test inputs and golden outputs as preserved upstream evidence; they were not
  regenerated on this execution surface.
- **Binary provenance of the downloaded nightly was not independently proved.**
  The rust source subject is an immutable revision from the matching nightly era,
  and Charon pins `nightly-2026-05-31`; this report does not claim a
  reproducible-build proof from Anneal's static toolchain archive to that Git
  tree.
- **Only the MIR distinctions needed to understand stage/reachability loss are
  inventoried.** This is not a complete account of every HIR/THIR/source
  distinction lost during MIR lowering. Unsafe lexical boundaries, detailed
  lifetime/region survival, spans, macros, and individual unsafe operations have
  separate #3720 subjects.
- **The constant-branch claim is intentionally narrow.** The source establishes
  the ordinary `if false { ... }` lowering and the later constant-condition
  optimization. Other compile-time constructs, pattern-match specialization,
  const evaluation, uninhabited types, and monomorphization can make control flow
  unreachable through different mechanisms.
- **Dependency MIR is configuration-sensitive.** Charon's source specifies its
  optimized/CTFE fallback policy, but a prebuilt dependency's encoded MIR may
  have been produced under compiler options other than the current Charon
  invocation's settings. This report does not generalize the local Promoted
  behavior to every standard-library/dependency body.
- **Reachability is not semantic equivalence.** Structural removal of blocks not
  reachable in a CFG is only as sound as the preceding lowering and edge model.
  This report does not prove rustc's MIR construction, `SimplifyCfg`, or
  Charon's translation correct.
- **Aeneas's treatment of the resulting LLBC is out of scope.** The report stops
  at Charon output and does not claim that downstream Aeneas preserves every
  remaining control-flow distinction.
- **Panic/unwind is only covered as needed to identify the reachability boundary.**
  A full panic/unwind/abort/divergence semantics report remains useful and should
  not be considered completed by this package.

## Evidence

**Source — Anneal configuration.**
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/flake.nix`: the selected Rust date is `2026-05-31`.

**Source — Charon MIR selection and rustc configuration.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `rust-toolchain` — `nightly-2026-05-31`;
- `charon/src/options.rs` — `MirLevel`, default Promoted selection,
  `precise_drops`, and Aeneas preset;
- `charon/src/bin/charon-driver/driver.rs` — `after_expansion` hook and
  `set_mir_options`;
- `charon/src/bin/charon-driver/translate/get_mir.rs` — exact mapping from
  Charon MIR levels to rustc queries and optimized/CTFE fallback;
- `charon/src/bin/charon-driver/translate/translate_bodies.rs` —
  successor-driven block traversal and MIR terminator translation;
- `charon/src/transform/mod.rs` — transformation ordering;
- `charon/src/transform/normalize/filter_unreachable_blocks.rs` — final DFS
  reachability filter.

**Source — rustc MIR query pipeline.**
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `compiler/rustc_mir_transform/src/lib.rs` — `mir_built`,
  `mir_promoted`, `mir_drops_elaborated_and_const_checked`,
  analysis→runtime lowering, and `optimized_mir`;
- `compiler/rustc_mir_transform/src/pass_manager.rs` — pass enablement,
  minimum optimization-level wrappers, and override handling;
- `compiler/rustc_mir_transform/src/simplify.rs` — `SimplifyCfg`,
  preservation of switch reads, and `remove_dead_blocks`;
- `compiler/rustc_mir_transform/src/simplify_branches.rs` — constant-condition
  branch simplification;
- `compiler/rustc_mir_transform/src/unreachable_prop.rs` —
  opt-level-2 unreachable propagation;
- `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs` — removal of
  analysis-only structure;
- `compiler/rustc_session/src/options.rs` — semantics of
  `mir_opt_level`, `mir_preserve_ub`, and pass overrides;
- `compiler/rustc_middle/src/mir/syntax.rs` — MIR terminator and unwind
  semantics;
- `compiler/rustc_mir_build/src/builder/expr/into.rs` and
  `builder/matches/mod.rs` — lowering of `if`, never-typed control flow, and
  branch construction.

**Preserved upstream generated evidence.**
At the same rust revision:

- `tests/mir-opt/simplify_if.rs` and
  `simplify_if.main.SimplifyConstCondition-after-inst-simplify.*.diff` show
  `if false` retaining a constant-valued `SwitchInt` until a later
  optimization rewrites it to a goto.
- `tests/mir-opt/simplify_cfg.rs` and
  `simplify_cfg.main.SimplifyCfg-initial.diff` show the initial CFG pass
  collapsing/removing unreachable/goto-chain blocks before later analysis.
- `tests/mir-opt/read_from_trivial_switch.*` records the
  `mir-preserve-ub` requirement that a trivial switch read remain observable.
- `tests/mir-opt/unreachable_diverging.*` records the later optimized-MIR
  `UnreachablePropagation` behavior.

These files are checked-in upstream artifacts, not execution performed during
this report.

**Derived.**
The coverage implications—particularly that absence from final LLBC does not
alone establish absence from source—follow from composing the rustc dead-block
removal, Charon's reachability-driven translation, and Charon's final
reachability filter.

## Revalidation

For a newer rustc/Charon pair, the cheapest source-level revalidation is:

1. In Charon, inspect `options.rs` for the default/Aeneas `MirLevel` and
   `driver.rs` for MIR-related rustc options.
2. Inspect `translate/get_mir.rs` for the exact rustc queries used for local,
   stolen, dependency, const, and promoted bodies.
3. In rustc, inspect `mir_built` and `mir_promoted` plus
   `SimplifyCfg::run_pass` / `remove_dead_blocks`. Confirm whether structural
   dead-block removal still precedes the query Charon consumes.
4. Inspect the optimized-MIR pass list and pass enablement for
   `UnreachablePropagation`, constant-condition simplification, and any new
   reachability/value-range pass.
5. In Charon, inspect `translate_body` to confirm whether translation is still
   successor-driven from `START_BLOCK`, and inspect the final transformation
   list for reachability filtering.

On a surface capable of running the exact toolchain, preserve a compact golden
matrix with one Rust crate containing:

```rust
fn marker() {}

fn constant_branch() {
    if false {
        marker();
    }
}

fn after_return() {
    return;
    #[allow(unreachable_code)]
    marker();
}

fn diverges() -> ! {
    loop {}
}

fn after_diverge() {
    diverges();
    #[allow(unreachable_code)]
    marker();
}

fn dynamic_branch(x: bool) {
    if x {
        marker();
    }
}
```

For each function, record:

- rustc MIR immediately after `SimplifyCfg::Initial`;
- rustc MIR after `SimplifyCfg::PromoteConsts`;
- Charon `--mir promoted --print-original-ullbc`;
- final ULLBC and final LLBC under `--preset aeneas`;
- an explicit `--mir optimized` control.

The discriminating expectations from this report are:

- the literal-false body is still represented as a promoted-MIR branch before
  optimization-only constant-condition simplification;
- source tails made structurally disconnected by unconditional exits are absent
  after initial CFG cleanup;
- reachable MIR `Unreachable` becomes Charon UB abort rather than vanishing;
- Charon's original ULLBC contains only blocks reachable from MIR
  `START_BLOCK`;
- final Charon output contains no blocks made dangling by Charon transformations.

Also run one dependency fixture and record whether its body enters Charon as
optimized/CTFE MIR. A passing fixture would validate these concrete observations
for the exact pair; it would not prove rustc's or Charon's semantic preservation.
