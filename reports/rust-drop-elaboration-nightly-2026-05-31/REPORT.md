# Rust drop elaboration and downstream visibility at nightly-2026-05-31

## Summary

Rust source semantics require destruction only for initialized values and initialized subobjects. The compiler does not encode that rule directly in newly built MIR. It first inserts `Drop` terminators at places where destruction may occur, including normal scope exits and cleanup paths. At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the mandatory `ElaborateDrops` pass combines move-path dataflow with generated drop flags and rewrites those potential drops into runtime control flow. It classifies each drop as dead, static, conditional, or open; open drops recursively destroy only the still-initialized subobjects. After elaboration, a remaining `Drop` terminator means an actual invocation of the type's drop glue rather than merely a possible source-level destruction point.

That distinction is directly relevant to the Anneal toolchain. At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon defaults to promoted MIR. Its Aeneas preset does not opt into precise drops. Charon therefore marks drops from built/analysis MIR as `Conditional`, explicitly warning that the exact runtime drop behavior may still depend on later rustc elaboration. `--precise-drops` raises extraction to at least elaborated MIR and attempts to recover drop glue, but Charon also documents that this mode can trigger rustc failures for polymorphic types.

The next boundary is stronger. At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the default functional interpreter treats LLBC `Drop` statements as no-ops. Its `-eval-drops` option can instead update the symbolic place as dropped, but the inspected statement evaluator ignores Charon's `DropKind` and drop-function pointer in either case. Thus the ordinary pinned Aeneas functional translation does not establish the Rust destructor body's effects merely because a `Drop` node is present upstream.

No fresh rustc, Charon, Aeneas, or Lean execution was performed. The report establishes the pinned source semantics, phase boundaries, configuration defaults, and the exact missing-information boundary. It does not claim that a particular fresh Rust fixture produces a particular LLBC or Lean artifact on this execution surface.

## Applicability

The Rust compiler findings apply to the Rust nightly selected by current Anneal:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`;
- toolchain date `2026-05-31`.

Normative source-language statements use:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

The downstream findings apply to the tool pair selected by Anneal's pinned Aeneas release:

- Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`;
- Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`.

Current `google/zerocopy` `main` at `41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects Rust date `2026-05-31` and Aeneas release `nightly-2026.06.03` in `anneal/flake.nix`. Current Anneal design does not freeze the exact Rust/Charon/Aeneas proof boundary. This report records the behavior of the selected external tools; it does not prescribe how V2 must use them.

"Built/promoted MIR" below means MIR before rustc's drop-elaboration runtime phase. "Elaborated MIR" means MIR after rustc has made dynamic initializedness and drop-glue control flow explicit. Charon's own `MirLevel` documentation uses the same distinction.

## Findings

### Rust destruction is conditional on initialization

The Rust Reference states that an initialized variable or temporary is dropped when its drop scope is left, assignment first drops an initialized old value, and a partially initialized value drops only its initialized fields. A type's destructor first runs its `Drop::drop` implementation when one exists and then recursively runs the destructors of its fields. For enums, only the active variant's fields participate.

The semantic obligation is therefore not "execute every syntactically implied drop." It is "execute destruction for the parts that remain initialized at the relevant exit or overwrite point."

Basis: **normative**.

### MIR construction inserts potential drops before their runtime condition is known

During MIR building, rustc schedules values for destruction in lexical scopes. `rustc_mir_build::builder::scope` records those scheduled drops and inserts them on outgoing edges. Early exits such as `break`, `continue`, and `return` accumulate the currently scheduled drops into drop trees. Panic-capable paths use a separate unwind-drop tree that is linked after the function body has been lowered.

At this phase, a `Drop` terminator is a possible destruction point, not proof that a destructor will execute. The target may have been moved from or may be only partially initialized when control reaches that point.

Basis: **source** + compiler **documentation**.

### Drop elaboration computes initializedness from move paths

`ElaborateDrops` gathers move paths for values whose types need dropping. It then runs both `MaybeInitializedPlaces` and `MaybeUninitializedPlaces` dataflow analyses. For each relevant path, the pair answers whether the path can be initialized, uninitialized, or either at the drop location.

The pass uses those results to classify a drop:

- **Dead**: the target cannot be initialized; remove the drop.
- **Static**: the target is always initialized; keep an unconditional runtime drop.
- **Conditional**: the target may be wholly initialized or wholly uninitialized; guard the runtime drop with a drop flag.
- **Open**: different subpaths can have different initializedness; recursively elaborate destruction for the applicable subobjects.

This classification is an implementation technique for the normative initializedness rule. It is not a new source-language category visible to Rust programmers.

Basis: **source** + compiler **documentation**.

### Drop flags represent dynamic initializedness only where needed

The pass creates a Boolean drop flag for a move path when dataflow says that path may be both initialized and uninitialized at a relevant drop. It initializes generated flags to false and updates them as arguments, successful call destinations, moves, assignments, and other initialization transitions change the path state.

The implementation therefore avoids a universal "one Boolean per local" scheme. Dataflow removes statically decidable cases; flags remain for the runtime distinctions that cannot be decided at compilation time.

A verifier reading pre-elaboration MIR cannot recover the final runtime branch merely from the existence of the original `Drop` terminator. It must either model the earlier initializedness semantics itself or consume a representation after rustc has made the branch explicit.

Basis: **source** + **derived**.

### Open drops preserve partial-initialization semantics structurally

An open drop is used when only some fields or elements remain initialized. `elaborate_drop.rs` recursively descends into subpaths that need drop glue and constructs "drop ladders" for the remaining components. For ADTs, it uses the active variant and field structure; the generated ladder also contains corresponding unwind continuations so a panic while destroying one field continues cleanup with the appropriate later fields.

This is why partially moving a field does not require running drop glue for the whole original value. The original whole-value drop would assume initializedness that no longer holds. Rustc instead emits the destruction of the remaining initialized pieces.

Basis: **source**.

### Unwind cleanup is a distinct control-flow obligation

The MIR builder constructs unwind drop trees for panic-capable control flow. During elaboration, rustc retains cleanup targets for drops that can actually run and computes dead unwind edges for drops whose targets cannot be initialized. The elaborator's drop ladders distinguish the mainline successor from the unwind successor; if a destructor panics while already in cleanup, the generated unwind action terminates rather than recursively unwinding indefinitely.

Thus "drop order on normal return" is not the whole drop semantics. A representation intended to preserve Rust execution must also account for which destruction remains reachable on unwind and for the cleanup path after a destructor itself unwinds.

Basis: **source**.

### After elaboration, a `Drop` terminator has a stronger meaning

The source comment on `ElaborateDrops` says that, once the pass is complete, remaining MIR `Drop` terminators correspond to calls to the type's drop glue or drop shim. The rustc developer guide states the same boundary: before elaboration a `Drop` is only a possible destructor call; after elaboration dead drops are removed, dynamic cases are guarded, and open drops are decomposed.

This phase boundary is useful when interpreting downstream extraction. A consumer of elaborated/runtime MIR can treat a remaining `Drop` as a concrete runtime operation. A consumer of promoted/analysis MIR cannot.

Basis: **source** + compiler **documentation**.

### Charon exposes the phase distinction as `DropKind`

At the pinned Charon revision, `DropKind` has two values:

- `Precise`: a real drop that calls Charon's modeled `Destruct::drop_in_place` path and marks the place moved-out-of;
- `Conditional`: a pre-runtime drop whose actual behavior can depend on the path, partial initialization, or later drop elaboration.

Charon's body translator chooses `Conditional` for rustc `Built` and `Analysis` phases and `Precise` for `Runtime` phases. Its ULLBC terminator retains the `DropKind`, place, a function pointer for `drop_in_place`, normal target, and unwind target.

The serialized presence of `Drop` alone therefore does not establish one semantic category. Consumers must account for its `DropKind` and the extraction phase.

Basis: **source**.

### Charon's default and Aeneas preset do not request elaborated MIR

Pinned Charon defaults `MirLevel` to `Promoted`. Its `Preset::Aeneas` enables a number of transformations but does not set `precise_drops` and does not change the MIR level. Consequently, `--preset=aeneas` by itself remains on promoted MIR and yields the pre-elaboration `Conditional` drop category for the current crate.

Charon documents `MirLevel::Elaborated` as the first MIR level to contain all runtime drop information. `--precise-drops` raises the selected level to at least `Elaborated`, adds `Destruct` bounds, and attempts to retrieve drop glue.

Basis: **source**.

### Precise-drop extraction has a documented polymorphic limitation

Charon's `--precise-drops` documentation warns that retrieving drop glue for polymorphic types can trigger rustc panics. The option suggests making problematic `Destruct` implementations opaque as a workaround.

This matters for coverage accounting: "use elaborated MIR" is not, at this pinned revision, evidence that all generic code can be extracted without qualification. A pipeline must record whether it stayed on conditional drops, enabled precise drops successfully, or excluded/opaque-modeled cases that could not be extracted.

Basis: **source**.

### Aeneas defaults to treating LLBC drops as no-ops

At the pinned Aeneas revision, `Config.drop_as_no_op` defaults to `true`. The CLI option `-eval-drops` clears that flag; its help text says that drops are otherwise not borrow-checked and are treated as no-ops.

`InterpStatements.eval_statement` matches `Drop (p, _, _)`. When the default flag is true, the interpreter returns without changing the symbolic context. When `-eval-drops` is enabled, it calls `drop_value`, which prepares the place, preserves borrow-bearing values in a dummy binding, and replaces the dropped place with `VBottom`.

Basis: **source**.

### The inspected Aeneas drop evaluator does not dispatch the Rust destructor body

The `Drop (p, _, _)` match ignores both non-place fields of the LLBC drop node. In the default mode it is a no-op. In `-eval-drops` mode it performs symbolic place invalidation through `drop_value`. The inspected path does not invoke the retained drop function pointer.

Therefore `-eval-drops` should not be described, from this evidence, as "executing Rust destructors." It strengthens Aeneas's symbolic treatment of the dropped place and its borrow state. The source inspected here does not establish execution of arbitrary `Drop::drop` side effects or drop glue.

Basis: **source** + **derived**.

### Storage death and Rust destruction are different operations in Aeneas

The same Aeneas statement evaluator sends `StorageDead local` through `drop_value` unconditionally, while the separate LLBC `Drop` branch is controlled by `drop_as_no_op`. This makes the purpose of `drop_value` clearer: it primarily updates Aeneas's symbolic local/borrow state when a place ceases to be usable. It is not, by itself, a model of the source destructor.

A future verifier must not equate "Aeneas invalidated the local" with "all Rust destructor effects were modeled."

Basis: **source** + **derived**.

### Destructor-sensitive Rust claims cross two independent downstream boundaries

For the pinned ordinary path, two separate questions matter.

First, Charon's Aeneas preset begins from promoted MIR, where a drop may still be conditional or partial and later rustc elaboration determines exact runtime behavior.

Second, Aeneas's default interpreter treats the resulting drop statement as a no-op rather than interpreting destructor execution.

These are independent information/semantics boundaries. Solving only one does not establish a faithful Rust destructor model. For example, switching Charon to precise drops would make runtime destruction sites more explicit, but the inspected default Aeneas statement semantics would still not execute their destructor function pointers. Conversely, enabling Aeneas `-eval-drops` would update dropped symbolic places but would not recover rustc's lost pre-elaboration runtime branch or prove destructor-body execution.

Basis: **derived** from pinned Charon and Aeneas **source**.

### Rust-level verification must state what it assumes about drops

A Rust-level proof can be sensitive to destruction even when source code never writes `drop(x)` explicitly. Scope exit, assignment, partial moves, and panic cleanup can all cause destruction. A safe API can also rely on a destructor to release or update external resources even though suppressing destruction with safe `mem::forget` remains legal; which property is being proved determines whether that omission matters.

The reusable conclusion is narrower than an Anneal design choice: a verification claim that depends on destructor behavior must identify which layer supplies that behavior and which configuration establishes it. Promoted Charon LLBC plus default Aeneas drop handling does not, by itself, establish arbitrary Rust destructor effects.

Basis: **derived** from **normative** Rust semantics and pinned downstream **source**.

## Boundaries

- No fresh rustc MIR dump, Charon extraction, Aeneas translation, or Lean elaboration was executed.
- The report does not claim that every potential drop in built/promoted MIR survives Charon unchanged; only the pinned phase/default rules and representation are established from source.
- It does not claim that `--precise-drops` succeeds for all Rust. Charon explicitly documents a polymorphic rustc failure mode.
- It does not claim that Aeneas `-eval-drops` executes Rust destructor bodies. The inspected statement evaluator updates symbolic place state and does not dispatch the retained function pointer.
- It does not establish the semantics of every Aeneas micro-pass that may later transform or remove drop-related syntax.
- Async drop/coroutine destruction is not exhaustively analyzed. rustc and Charon both contain separate machinery for it at these revisions.
- The report covers unwind cleanup only as it interacts with drop construction/elaboration. It is not a general Rust panic/unwind/abort semantics report.
- It does not analyze FFI destructors, allocator effects, OS resources, or application-specific `Drop` side effects.
- It does not prove semantic correctness of rustc's drop elaboration or Charon/Aeneas. It records their pinned specified/source-visible behavior.
- Current Anneal V2 architecture is deliberately not inferred from historical V1 orchestration or from these tool defaults.

## Evidence

**Normative — Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/destructors.md`, blob `aa27842622f5fe25efb0f1005d8901e6b77a71c7`: initialization-conditioned destruction, partial initialization, destructor composition, drop scopes, and order.
- `src/expressions/operator-expr.md`: assignment drops the previous initialized value before moving or copying the replacement.

**Source/documentation — Rust compiler.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_mir_build/src/builder/scope.rs`, blob `3343bec30caf58a38d129dc4a2787f7e0828d15c`: scheduled drops, early-exit drop trees, unwind trees, and coroutine drop-tree separation.
- `compiler/rustc_mir_transform/src/elaborate_drops.rs`, blob `3787276919cf5b4b827bd167d421e0dc2bb7223c`: `ElaborateDrops`, initialized/uninitialized dataflow, drop-flag creation/update, dead-unwind computation, and Dead/Static/Conditional/Open classification.
- `compiler/rustc_mir_transform/src/elaborate_drop.rs`, blob `0eb7db8dbed2d6f04223b42447591664b5f98daa`: `DropStyle`, recursive open-drop expansion, field/variant drop ladders, and mainline/unwind cleanup construction.
- `src/doc/rustc-dev-guide/src/mir/drop-elaboration.md`, blob `7ef60f4cca00b37bdf2fa270d13ae35921aa02be`: compiler-maintainer description of dynamic drop obligations, flags, open drops, and the pre/post-elaboration meaning of `Drop`. Its cleanup-path section is explicitly unfinished, so unwind conclusions above come from compiler source rather than that missing documentation.

**Source — Charon.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: default `MirLevel::Promoted`, `MirLevel::Elaborated`, `--precise-drops`, and `Preset::Aeneas`.
- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `DropKind::{Precise, Conditional}` and their documented phase-dependent meaning.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: body-phase mapping from `Built/Analysis` to conditional drops and `Runtime` to precise drops.
- `charon/src/ast/ullbc_ast.rs`, blob `3c6179f10742b2ee82c8ca07e6d51be6c8dc7694`: ULLBC `Drop` terminator fields, including kind, place, function pointer, normal target, and unwind target.

**Source — Aeneas.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: `drop_as_no_op = true` default and its stated meaning.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: `-eval-drops` CLI option.
- `src/interp/InterpStatements.ml`, blob `97452f658bbd773c16386592d31b0bf61da8891f`: default `Drop` no-op, enabled `drop_value`, unconditional `StorageDead` state update, and `drop_value` implementation.

**Configuration — Anneal.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`: Rust date `2026-05-31`, Aeneas release `nightly-2026.06.03`, and Lean version `v4.30.0-rc2`.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For a later Rust/Charon/Aeneas pin, the cheapest source check is:

1. Diff rustc's `ElaborateDrops`, `DropStyle`, and scope/drop-tree code. Confirm the pre/post-elaboration phase boundary and the initializedness analyses still have the same semantic role.
2. Diff Charon's `MirLevel`, `--precise-drops`, Aeneas preset, `DropKind`, and rustc-phase mapping.
3. Diff Aeneas's `drop_as_no_op`, `-eval-drops`, and LLBC `Drop` evaluator. In particular, check whether it has begun dispatching the retained drop function pointer or distinguishing Charon drop kinds.

On a capable execution surface, preserve one compact fixture set at the exact revisions:

- a struct with two drop-requiring fields where one field is conditionally moved, forcing partial/open destruction;
- an assignment that overwrites an initialized drop-requiring value;
- a partially initialized value followed by a panic-capable operation, exercising cleanup;
- a type with its own `Drop` implementation and drop-requiring fields;
- a control type with no drop glue.

For each fixture:

1. dump rustc MIR at built/promoted and elaborated stages;
2. extract with Charon `--preset=aeneas`;
3. extract again with `--preset=aeneas --precise-drops`;
4. preserve LLBC `DropKind`, generated control flow, drop-glue references, and unwind edges;
5. run the paired Aeneas translator once at default settings and once with `-eval-drops`;
6. preserve generated Lean, diagnostics, exact commands, revisions, and artifact hashes.

The comparison should establish which source-level destruction distinctions are visible at each boundary and whether a later Aeneas has started modeling destructor execution. It does not by itself prove that the downstream semantics are equivalent to Rust; that stronger claim requires a semantic-preservation argument rather than only matching golden output.
