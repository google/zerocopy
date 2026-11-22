# rustc `EarlyOtherwiseBranch` read hoisting onto uninitialized paths, `SimplifyComparisonIntegral` operand rewriting, and `required_panic_strategy` link checking

## Summary

This report covers three rustc mechanisms that sit below the level at which Rust source is usually reasoned about, and that decide whether a property established for a function's MIR still holds for the compiled artifact.

**`EarlyOtherwiseBranch` hoists a read onto paths that never performed it.** The pass turns a two-level `switchInt` on `(Q, P)` into one comparison `Ne(Q, copy P)` placed at the end of the parent block. When the parent's `otherwise` edge leads to a real block, the original program reads `P` only if `Q` matched an arm; the rewritten program reads `P` always. The pass decided legality from the *shape* of the place `P`, never from its initialization state:

- In `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (1.98.0-nightly, 2026-05-31) any `copy P` child switch qualified.
- At `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (1.102.0-nightly, 2026-11-11) `P` additionally had to be a "stable offset" place (no `Deref`, no `Index`). A plain local such as `_2: u32` is a stable-offset place, so the hoist still happened.
- At `01afe534803b93889b85f6028117251cfbd431da` (main on 2026-11-22) the hoist is restricted to unchanged function arguments projected through struct or tuple fields. This change landed two days after the 2026-11-11 revision, as the fix for upstream issue 164765.

Executed on the 2026-05-31 toolchain on x86-64 Linux, the hoist turns defined programs into wrong code. A program written in surface Rust with a `union`, no feature gates, and a `SAFETY` argument that holds, prints `999` for inputs outside `{1, 2}` at `-C opt-level=0` and `200` at `-C opt-level=1`, `2`, `3` and `s`. Disabling the single pass restores `999`. A custom-MIR function whose local is never written compiles to `ret i32 42` without the pass and to an LLVM function whose whole body is `unreachable` with it; the binary then prints an arbitrary number that changed from run to run.

**The exact legality condition is small and is mechanized.** For a parent switch with a reachable `otherwise`, the rewrite is a refinement on a set of reachable states if and only if `P` holds a valid, initialized value with live storage on every reachable state that takes the `otherwise` edge. With an exhaustive parent switch (the `otherwise` target is an empty `unreachable` block) the rewrite is always a refinement.

**`SimplifyComparisonIntegral` at the 2026-11-11 revision** rewrites `_t = Eq/Ne(move _x, const K); switchInt(_t)` into `_t = Eq/Ne(copy _x, const K); switchInt(copy _x)`, and refuses when a `StorageLive(_x)` or `StorageDead(_x)` sits between the comparison and the terminator. The mechanized model shows that "no storage marker in between" is exactly the condition under which the rewrite is a refinement. The downgrade from `move` to `copy` only matters under a semantics in which a move de-initializes its source. The 2026-05-31 toolchain implements an older version of the pass (it deletes the comparison when the switch consumed `_t` by move, and relocates `StorageDead(_x)` into the successors), so the 2026-11-11 behavior was read, not run.

**`required_panic_strategy` makes a `-C panic=unwind` crate with an FFI-unwind call site unlinkable into a `-C panic=abort` program, but only when a panic-runtime crate is part of the link.** A crate compiled with `panic=unwind` reports `None` (linkable either way) unless one of its bodies that can itself unwind contains a call to a foreign `-unwind` ABI item, a call through a `-unwind` ABI function pointer, or `asm!` with `may_unwind`; then it reports `Some(Unwind)`. A crate compiled with `panic=abort` always reports `Some(Abort)`. The observed twelve-row link matrix matches the source exactly. The per-crate comparison in the linker-side check is nested under "a panic runtime was found", and on the 2026-05-31 toolchain a `#![no_std]` executable compiled with `panic=abort` links, without any diagnostic, against a `panic=unwind` rlib whose `entry` calls a foreign `"C-unwind"` item. The emitted MIR shows `unwind continue` in the upstream body and `unwind unreachable` at the downstream call site, which is the pairing the check exists to reject. The Reference states that rustc enforces the rule automatically when it does the linking.

What was executed and what was only read differs per revision and is spelled out under Applicability. Nothing in this report was executed on the 2026-11-11 or 2026-11-22 revisions.

## Applicability

### Subjects and how they relate

Three revisions of `rust-lang/rust` are examined. They are referred to by date below.

| Label | Revision | Version string | How examined |
|---|---|---|---|
| 2026-05-31 toolchain | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6 | source read; `rustc` and the `miri` driver of this toolchain executed on `x86_64-unknown-linux-gnu` |
| 2026-11-11 revision | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5 (per the preserved record) | source read; **not executed** for this report; one earlier execution record is preserved and discussed separately |
| 2026-11-22 main | `01afe534803b93889b85f6028117251cfbd431da` | none (branch tip when observed) | source read only |

The 2026-11-11 revision is the primary object of the source audit. The 2026-05-31 toolchain is the only one that could be run where this investigation was carried out, so every execution claim in this report is about that toolchain unless it is explicitly attributed to the preserved record. The 2026-11-22 revision is included because it changes the `EarlyOtherwiseBranch` guard.

The other subjects play supporting roles:

- `rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` supplies the normative statements about uninitialized integers, dangling places, unwinding past frames that do not allow it, and the linkage rule for mixed panic strategies.
- `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, file `trusted/lean/Trusted/MirSemantics.lean`, is a Lean model of MIR execution used by a Rust verifier. It is read here for one question only: what its semantics says about `Operand::Move`, about reads of uninitialized or dead locals, and therefore about the MIR shapes discussed below. None of its definitions are imported by the support material.
- `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (v4.34.1) is the checker for the mechanized model in `support/EarlyOtherwiseBranchAndFfiUnwindSoundness.lean`.

### Configuration the findings depend on

- **MIR optimization level.** `EarlyOtherwiseBranch` and `SimplifyComparisonIntegral` run only at MIR optimization level 2 or higher. In the 2026-05-31 toolchain the default level is 2 whenever `-C opt-level` is not `0`, and 1 otherwise, so both passes are on in every optimized build and off in debug builds. `-Z mir-opt-level=N` overrides the default; `-Z mir-enable-passes=-EarlyOtherwiseBranch` and `+SimplifyComparisonIntegral` switch single passes.
- **Storage markers.** `RemoveStorageMarkers` deletes every `StorageLive`/`StorageDead` at MIR optimization level 1 or higher when LLVM lifetime markers would not be emitted, which is the case at `-C opt-level=0`. Whether a hoisted read hits "dead local" or "uninitialized" therefore depends on `-C opt-level` as well as on the MIR level.
- **Miri.** Miri's default arguments include `-Zmir-opt-level=0` and `-Zmir-preserve-ub`. With the defaults no MIR optimization runs, so Miri interprets the unoptimized program. Passing `-Zmir-opt-level=2` to Miri makes it interpret optimized MIR; `-Zmir-preserve-ub` then still changes which statements survive, which decides whether the `EarlyOtherwiseBranch` pattern matches for MIR built from surface Rust.
- **Host and target.** All executions were on `x86_64-unknown-linux-gnu` (an Intel Xeon host). The linker-side panic-strategy check is target independent in the source. Whether a hoisted read becomes an observable wrong result depends on LLVM and the target; only x86-64 was run.
- **Custom MIR.** Three of the five `EarlyOtherwiseBranch` inputs are written with the unstable `custom_mir` feature, in the runtime dialect. They pass `-Z validate-mir`. The remaining two inputs are ordinary Rust.

### Extending beyond what was run

Two extensions are made, both by argument from source and both labeled where they are used:

1. That the 2026-11-11 revision performs the same hoist for a stable-offset local as the 2026-05-31 toolchain. Argument: the 2026-11-11 guard is the 2026-05-31 guard plus one extra rejection (`!place.is_stable_offset()`), and `is_stable_offset` is true for a place without projections. Supporting, but not re-executed: upstream issue 164765 (opened 2026-10-22, closed by a change merged 2026-11-13) and the preserved execution record.
2. That the linker-side check is skipped without a panic runtime at the 2026-11-11 revision as well. Argument: the enclosing `if let Some(..) = panic_runtime` is present, with the same body, in both revisions.

No claim is made about stable releases, about other targets, or about revisions between the three examined.

## Findings

### 1. `EarlyOtherwiseBranch`

#### 1.1 What the pass matches and what it produces

Basis: source (2026-11-11 revision, `compiler/rustc_mir_transform/src/early_otherwise_branch.rs`, lines 96-200 for the rewrite and 211-421 for the matcher).

The pass looks at each non-cleanup block `parent` ending in `switchInt(Q)`. Every arm target (`child`) must itself end in a `switchInt` on an operand of the same type, must contain at most one statement, and must have exactly one arm, whose value equals the value of the parent arm that leads to it. All children must fall through to the same block `destination` when their switch misses. Two child shapes are accepted:

```text
child: switchInt(copy P) -> [c: then_c, otherwise: destination]            (no statement)
child: _d = discriminant(P); switchInt(move _d) -> [c: then_c, otherwise: destination]
```

The second shape sets the flag `need_hoist_discriminant`. With `Q` the parent operand and `P` the child place, the pass appends to `parent`

```text
_s = discriminant(P);            // only when need_hoist_discriminant
_t = Ne(Q, copy P);              // or Ne(Q, move _s)
switchInt(move _t) -> [0: bbEq, otherwise: destination];
```

and creates `bbEq: switchInt(Q) -> [c1: then_c1, ..., otherwise: <parent's otherwise>]`. The statements are inserted at `parent_end`, the location just before the parent's terminator (lines 123-156). The pass enables itself through `PassPolicy::optional(ctx.mir_opt_level() >= 2)` (line 98) and runs directly after `JumpThreading` and directly before `SimplifyComparisonIntegral` (`compiler/rustc_mir_transform/src/lib.rs`, lines 764-766).

What `destination` is depends on the parent's `otherwise` target (lines 259 and 289-293):

- If that target is an empty `unreachable` block (`otherwise_is_empty_unreachable`), the parent switch is exhaustive and `destination` is the children's common `otherwise`.
- Otherwise `destination` is the parent's own `otherwise` target, and every child must fall through to that same block.

The second case is the one this report is about: the parent's `otherwise` edge is taken by real executions, and on that edge the original program never evaluates `P`.

#### 1.2 Three generations of the legality guard

Basis: source at the three revisions.

**2026-05-31 toolchain** (`early_otherwise_branch.rs`, lines 261-297 and 325-330). The only state-related restriction is on discriminant hoisting:

```rust
let need_hoist_discriminant = bbs[child].statements.len() == 1;
let child_place = if need_hoist_discriminant {
    if !bbs[targets.otherwise()].is_empty_unreachable() {
        // ... Hoisting the `discriminant(Q)` out of the `A` arm causes us to compute the
        // discriminant of an invalid value, which is UB. ...
        // FIXME(#95162) For the moment, we adopt a conservative approach and
        // consider only the `otherwise` branch has no statements and an unreachable terminator.
        return None;
    }
    ...
```

A child of the form `switchInt(copy P)` is accepted for any `P`, including `*_2`.

**2026-11-11 revision** (lines 329-383, inside `verify_candidate_branch`). The discriminant restriction is kept and one more is added, with a reference to upstream issue 159591:

```rust
if !otherwise_is_empty_unreachable {
    // ... For <https://github.com/rust-lang/rust/issues/95162>, we adopt a conservative
    // approach and consider only the `otherwise` branch has no statements and an
    // unreachable terminator.
    if need_hoist_discriminant {
        return false;
    }
    // For <https://github.com/rust-lang/rust/issues/159591>: ...
    // We cannot hoist the dereference of `_2` to `bb0`,
    // because execution can reach `bb5` without dereferencing `_2`.
    if let Some(place) = switch_op.place()
        && !place.is_stable_offset()
    {
        return false;
    }
}
```

`Place::is_stable_offset` is `self.projection.iter().all(|elem| elem.is_stable_offset())`, and the element-level function returns `false` exactly for `Deref` and `Index(_)` and `true` for `Field`, `OpaqueCast`, `ConstantIndex`, `Subslice`, `Downcast`, `UnwrapUnsafeBinder` and `PhantomDeref` (`compiler/rustc_middle/src/mir/statement.rs`, lines 279-290 and 383-385). Its doc comment states the property it captures: the place "always refers to the same memory region whatever the state of the program". That is a statement about the *address*. It says nothing about whether the memory is allocated for the local at this point, or initialized.

**2026-11-22 main** (lines 316-325 in `evaluate_candidate`, and a new `UnchangedArguments` helper at lines 385-431). Both earlier checks are removed from `verify_candidate_branch` and replaced by:

```rust
// A stable address does not imply that the child place is initialized on the otherwise path.
// Keep discriminant hoisting restricted to exhaustive switches (#95162).
if !otherwise_is_empty_unreachable
    && (need_hoist_discriminant
        || !unchanged_arguments
            .get_or_insert_with(|| UnchangedArguments::new(tcx, body))
            .can_hoist(body, child_place))
{
    return None;
}
```

`UnchangedArguments::new` collects the argument locals that are SSA and not borrowed, then removes every local that appears in a `Move` operand or in a storage marker ("SSA does not track storage lifetimes or invalidate moved places"). `can_hoist` requires the base local to be in that set and every projection to be a `Field` whose owning type is a tuple or a struct ("A valid union or enum need not have initialized bytes in every field"). This is commit `43dc29bb3fab2a69f47900f562f4b1315dda8bcf` ("Prevent early otherwise branch from hoisting uninitialized reads"), merged as `9c4122425e680b510907d1ca643ee9b0815052fb` on 2026-11-13 by pull request 164864, whose description reads "EarlyOtherwiseBranch can hoist a read onto a path where its operand is uninitialized, causing a miscompilation" and "The tradeoff is conservative: some safe computed locals and borrowed or modified arguments lose this optimization. Supporting those cases would require a broader initialization analysis."

The history of the guard, from the commit list for the file:

| Commit | Date | Subject |
|---|---|---|
| `a22fed77686db50c1185e4267743924ac50f584a` | 2026-07-20 | early_otherwise: Don't hoist dereferences when the otherwise branch is reachable |
| `43dc29bb3fab2a69f47900f562f4b1315dda8bcf` | 2026-11-12 | Prevent early otherwise branch from hoisting uninitialized reads |
| `9c4122425e680b510907d1ca643ee9b0815052fb` | 2026-11-13 | Rollup merge of #164864 |

#### 1.3 Why a stable address is not enough

Basis: derived from 1.1 and 1.2, and normative (Reference, `src/behavior-considered-undefined.md`).

Take the smallest instance, with `_1` the parent operand and `_2` a local of type `u32`:

```text
bb0: switchInt(copy _1) -> [1: bb1, 2: bb2, otherwise: bb5]
bb1: switchInt(copy _2) -> [1: bb3, otherwise: bb5]
bb2: switchInt(copy _2) -> [2: bb4, otherwise: bb5]
```

An execution with `_1 == 99` goes `bb0 -> bb5` and never evaluates `_2`. After the pass, `bb0` starts with `_3 = Ne(copy _1, copy _2)`, which every execution evaluates. If `_2` is uninitialized at the end of `bb0` on the `_1 == 99` path, the rewritten program produces an integer from uninitialized memory, which the Reference lists as invalid ("An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be initialized, i.e., must not be obtained from uninitialized memory"). If `_2` has no live storage there, the rewritten program accesses a dead local. In both cases a defined execution has become an undefined one, which a compiler transformation must not do.

Neither the 2026-05-31 guard nor the 2026-11-11 guard looks at anything that could exclude this: `_2` has no projections, so it is a stable-offset place, and the children carry no discriminant computation.

#### 1.4 Execution on the 2026-05-31 toolchain

Basis: execution. Inputs and driver: `support/probe_early_otherwise_branch_uninit_miscompile_and_ffi_unwind.py`. Recorded output: `support/probe_results_rustc_1.98.0-nightly_14210df0e.json`, key `early_otherwise_branch`.

Five programs were run. Native builds used `rustc --edition 2021 -Z validate-mir` plus the flags in the tables, with `--emit=mir,llvm-ir,link`; every compile succeeded, so every input is accepted by the MIR validator. "Hoisted" means the emitted MIR of the function contains a statement of the form `_n = Ne(copy _a, copy <place>)`.

**(a) Never-initialized local.** The function `eob_silicon_miscompile(q: u32) -> u32` is exactly the three blocks of 1.3 plus `bb3: RET = 10`, `bb4: RET = 20`, `bb5: RET = 42`, with `_2` declared and never written. It is free of undefined behavior for every input other than 1 and 2. It is called once, with `black_box(99)`.

| Flags | Hoisted | LLVM IR body of the function | Program output | Miri |
|---|---|---|---|---|
| `-Z mir-opt-level=0 -C opt-level=2` | no | `ret i32 42` | `OUT=42` | `OUT=42`, exit 0 |
| `-Z mir-opt-level=1 -C opt-level=2` | no | `ret i32 42` | `OUT=42` | `OUT=42`, exit 0 |
| `-Z mir-opt-level=2 -C opt-level=2` | yes | `unreachable` | `OUT=21878` | exit 1, `Undefined Behavior: using uninitialized data, but this operation requires initialized memory` |
| level 2 with `-Z mir-enable-passes=-EarlyOtherwiseBranch` | no | `ret i32 42` | `OUT=42` | `OUT=42`, exit 0 |

The MIR at level 2:

```text
bb0: {
    _3 = Ne(copy _1, copy _2);
    switchInt(move _3) -> [0: bb4, otherwise: bb3];
}
...
bb4: {
    switchInt(copy _1) -> [1: bb1, 2: bb2, otherwise: bb3];
}
```

and the complete LLVM function, whose attribute list gains `noreturn`:

```llvm
; Function Attrs: mustprogress nofree noinline norecurse noreturn nosync nounwind nonlazybind willreturn memory(none) uwtable
define dso_local noundef i32 @eob_silicon_miscompile(i32 noundef %_1) unnamed_addr #3 {
start:
  unreachable
}
```

In the generated assembly the function is `movl $42, %eax; retq` without the pass and a single `ud2` with it, and at every MIR level the executable contains no direct call to the function (probe fields `asm_fn_instructions` and `asm_direct_calls_to_fn`). The value that `main` prints is therefore not produced by executing the function: the optimizer has substituted the callee's result into the caller, which is the constant 42 without the pass and an undefined value with it (the substitution is inferred from the two observations; the assembly of `main` was not analyzed further). The printed number is arbitrary. Across the runs made for this report it varied, for example `21977`, `22057` and `22091`; the preserved output has `21878`.

**(b) Local without live storage on one path.** `eob_dead_local_ub(q: u32) -> u32` branches first: for `q == 99` it goes straight to the parent block; for every other `q` it executes `StorageLive(d); d = q;` and then goes to the parent block. The parent and children are as in 1.3 with `d` in the role of `_2`, and all three exit blocks begin with `StorageDead(d)`. This function is free of undefined behavior for **every** input, because `d` is read only under `q == 1` or `q == 2`, where it is live and initialized. It is called with 99, 1, 2 and 7.

| Flags | Hoisted | Program output | Miri |
|---|---|---|---|
| level 0, 1 | no | `42, 10, 20, 42` | same, exit 0 |
| `-Z mir-opt-level=2 -C opt-level=2` | yes | `42, 10, 20, 42` | see below |
| level 2 without the pass | no | `42, 10, 20, 42` | same, exit 0 |

Miri at `-Zmir-opt-level=2` with its default `-C opt-level=0` reports `using uninitialized data` (the storage markers have been removed, so `d` is an always-live, never-written local on the 99 path). Miri at `-Zmir-opt-level=2 -C opt-level=2`, which keeps the markers, reports `Undefined Behavior: accessing a dead local variable`. The native binary still prints 42 for `q == 99` on this toolchain: the machine code at level 2 is two compare-and-conditional-move pairs that yield 20 for 2, 10 for 1 and 42 for everything else, with no trace of the hoisted comparison. So for this input the pass introduces undefined behavior that Miri detects, without an observed wrong result.

**(c) The reproducer from upstream issue 164765.** A custom-MIR function `foo(q: u64) -> u64` that writes `x = 1` when `q == 1`, `x = 2` when `q == 2`, writes nothing otherwise, and then runs the two-level switch returning 100, 200 or 999. Free of undefined behavior for every input.

| Flags | Hoisted | Output for `q` in `0, 1, 2, 3, u64::MAX` |
|---|---|---|
| `-Z mir-opt-level=0 -C opt-level=2` | no | `999, 100, 200, 999, 999` |
| `-Z mir-opt-level=2 -C opt-level=2` | yes | `200, 100, 200, 200, 200` |
| level 2 without the pass | no | `999, 100, 200, 999, 999` |

In the level-2 MIR the two initializing paths no longer pass through the parent block (their blocks jump straight to the blocks that return 100 and 200), so the parent is reached only with `x` unwritten, and the function compiles to `%0 = icmp eq i64 %_1, 1; %. = select i1 %0, i64 100, i64 200; ret i64 %.`, in machine code `cmpq $1, %rdi; movl $100, %ecx; movl $200, %eax; cmoveq %rcx, %rax; retq`. The fallback value 999 no longer exists in the function. Miri at `-Zmir-opt-level=2` reports `using uninitialized data`; at level 0 and at level 2 without the pass it prints the correct five results.

**(d) Surface Rust with a union.** This is the body of the regression test that the upstream fix added as `tests/ui/mir/hoist_uninit_early_else.rs`, with the assertion replaced by a print (layout condensed here; the probe holds the exact text):

```rust
union U { a: u64, b: () }

#[inline(never)]
fn foo(q: u64) -> u64 {
    let mut u = U { b: () };
    match q { 1 => u.a = 1, 2 => u.a = 2, _ => {} }
    black_box(());
    let mut r = 999;
    // SAFETY: Each read of `u.a` is preceded by its initialization for the same value of `q`.
    unsafe {
        match q {
            1 => match u.a { 1 => r = 100, _ => {} },
            2 => match u.a { 2 => r = 200, _ => {} },
            _ => {}
        }
    }
    r
}
```

| Flags | Hoisted | Output for `q` in `0, 1, 2, 3, u64::MAX` |
|---|---|---|
| `-C opt-level=0` | no | `999, 100, 200, 999, 999` |
| `-C opt-level=1` | yes | `200, 100, 200, 200, 200` |
| `-C opt-level=2` | yes | `200, 100, 200, 200, 200` |
| `-C opt-level=s` | yes | `200, 100, 200, 200, 200` |
| `-C opt-level=3` | yes | `200, 100, 200, 200, 200` |
| `-C opt-level=3 -Z mir-enable-passes=-EarlyOtherwiseBranch` | no | `999, 100, 200, 999, 999` |

The hoisted statement is `_4 = Ne(copy _1, copy (_2.0: u64))`, a read of a union field, which is a stable-offset place. After the `black_box` call the optimized machine code of `foo` is the same five instructions as in (c): it returns 100 for `q == 1` and 200 for every other `q`. This case needs no unstable feature and no unusual flag: an ordinary optimized build of the 2026-05-31 toolchain produces a wrong result for three of the five inputs.

**(e) Surface Rust with a raw pointer** (the reproducer from upstream issue 159591): `foo(q, p)` reads `*p` only under `q == 1` or `q == 2`, and is called with `q = 3` and a null `p`. On the 2026-05-31 toolchain, which predates the stable-offset check, the read is hoisted as `_3 = Ne(copy _1, copy (*_2))`; the program prints `999` at `-C opt-level=0` and with the pass disabled, and dies with signal 11 at `-C opt-level=1`, `2`, `s` and `3`, where the machine code of `foo` is branch-free and contains the unconditional load `cmpq (%rsi), %rdi`.

**Miri and `-Zmir-preserve-ub`.** For the two surface-Rust inputs Miri at `-Zmir-opt-level=2` reports nothing and prints the correct results. The cause is not that the hoisted read is harmless. With `-Zmir-preserve-ub` (a Miri default, `src/tools/miri/src/lib.rs`, `MIRI_DEFAULT_ARGS`) the `RemovePlaceMention` pass is disabled and `SimplifyLocals` keeps otherwise-dead reads (`compiler/rustc_mir_transform/src/remove_place_mention.rs` line 11 and `simplify.rs` line 130 in the 2026-05-31 sources), so the child blocks retain a statement and no longer match the pattern: in the MIR of input (d) built with the flag, each child block reads `PlaceMention((_2.0: u64)); switchInt(copy (_2.0: u64)) -> [...]`. Running `rustc -C opt-level=0 -Z mir-opt-level=2 -Z mir-preserve-ub` on inputs (d) and (e) gives MIR without the hoisted `Ne`; without `-Z mir-preserve-ub` the `Ne` is there (probe rows `opt_level_0_mir_opt_2_preserve_ub` and `opt_level_0_mir_opt_2`). With `-Zmir-opt-level=2 -Zmir-preserve-ub=no` Miri interprets the MIR that the native build uses and reports

- for (d): `Undefined Behavior: reading memory at alloc190[0x0..0x8], but memory is uninitialized at [0x0..0x8], and this operation requires initialized memory`;
- for (e): `Undefined Behavior: memory access failed: attempting to access 8 bytes, but got null pointer`;

and with the pass additionally disabled it reports nothing. The custom-MIR inputs have no such statements, which is why Miri catches them without the extra flag.

Consequence: a clean Miri run with `-Zmir-opt-level=2` and default arguments does not show that optimized MIR is free of pass-introduced undefined behavior.

#### 1.5 The preserved execution record for the 2026-11-11 revision

Basis: a recorded execution that this report did not repeat. File: `support/recorded_observation_rustc_1.102.0-nightly_3ef0c22cd.json`, preserved byte for byte (SHA-256 `b6f540399502783a3903d8b42d524a42749e22d9d858ed873e33d93ea89de43f`).

The file is the JSON output of an earlier run of a probe of the same design against `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5. For a function named `eob_silicon_miscompile` it records, at MIR levels 0 and 1, a clean `-Z validate-mir`, Miri exit 0 with `OUT=42`, the LLVM body `ret i32 42` and native output `OUT=42`; at MIR level 2, a clean `-Z validate-mir`, Miri exit 1 with undefined behavior, the LLVM body `unreachable` with `noreturn` in the attribute list, and native output `OUT=0`. It records the same pattern for a function named `eob_dead_local_ub`. It also records two rows of the panic-strategy matrix, discussed in 3.5.

Limits of this record:

- The Rust inputs of that run were not preserved with it. The function names and the reported shapes match input (a) of this package, and the LLVM functions it quotes for `eob_silicon_miscompile` have the same bodies (`ret i32 42` and `unreachable`) and the same attribute lists as those observed here on the older toolchain, apart from a `!guid` metadata attachment on the `define` line. Identity of the inputs cannot be established from that.
- For `eob_dead_local_ub` the record shows an `unreachable` body and `OUT=0` at level 2. Input (b) of this package, run on the 2026-05-31 toolchain, keeps printing 42. Either the recorded run used a different function body under that name, or the two toolchains differ here. This report cannot tell which.
- The record stores only "Miri reported undefined behavior", not the message.

What the record adds is therefore limited to this: a run on the 2026-11-11 revision observed the same `ret i32 42` versus `unreachable` contrast for a function of the same name. The claim that the 2026-11-11 revision hoists the read rests on the source argument in 1.2 and 1.3 and on the upstream issue, not on this file.

#### 1.6 The upstream issues

Basis: documentation (issue and pull request text on `rust-lang/rust`, read on 2026-11-22).

| Issue | Title | Opened | Closed |
|---|---|---|---|
| 95162 | Early otherwise branch MIR opt is unsound | 2022-03-21 | 2024-04-09 |
| 159591 | Optimization introduces a pointer dereference on unreachable path | 2026-07-20 | 2026-07-24 |
| 164765 | Unexpected result when optimizing custom MIR with an otherwise branch | 2026-10-22 | 2026-11-13 |

Issue 95162 already states the general requirement: "we would either need to show that the discriminant computation of `place` is computed in all branches, including the `otherwise` branch, or we would need another analysis pass to determine that the place is fully initialized." Issue 159591 reports the null-dereference program (e) against `rustc 1.99.0-nightly (3659db0d3 2026-07-05)`. Issue 164765 reports input (c), carries the `I-miscompile` label, and was closed by pull request 164864. The uninitialized-read hoist was thus a known, tracked defect when the 2026-11-11 revision was built, and that revision is among the last before the fix.

#### 1.7 The exact condition, mechanized

Basis: derived, kernel-checked. File: `support/EarlyOtherwiseBranchAndFfiUnwindSoundness.lean`, namespace `EobFfi`, Part 1.

The model fixes one candidate. `arms` is the list of pairs `(c, then_c)`; `dest` is the common fall-through block; `q` is the value of `Q`; `p : Slot` is the state of the memory `P` denotes at the end of the parent block, one of `dead` (no live storage), `uninit`, `invalid` (bytes that are not a value of the type), `dangling` (`P` is `*ptr` with `ptr` not dereferenceable), or `init v`. Reading a slot yields the value for `init v` and undefined behavior otherwise. Two functions give the block the program reaches:

```lean
def runOrig (arms : Arms) (dest : Block) (q : Nat) (p : Slot) : Outcome Block :=
  match armTarget arms q with
  | none => .ok dest
  | some tgt =>
    match p.read with
    | .ub u => .ub u
    | .ok v => if v = q then .ok tgt else .ok dest

def runEob (arms : Arms) (dest : Block) (q : Nat) (p : Slot) : Outcome Block :=
  match p.read with
  | .ub u => .ub u
  | .ok v =>
    if v = q then
      match armTarget arms q with
      | none => .ok dest
      | some tgt => .ok tgt
    else .ok dest
```

`Refines src tgt` holds when `src` is undefined, or `src` and `tgt` are the same defined result. The theorems:

- `eob_refines_iff`: for one state, `Refines (runOrig arms dest q p) (runEob arms dest q p)` holds if and only if `armTarget arms q = none → p.isInit = true`.
- `eob_repaired_definite_init_sound_iff`: for any predicate `R` describing the states that reach the end of the parent block, the rewrite refines the original on all of `R` if and only if every state in `R` that takes the `otherwise` edge has `P` initialized.
- `eob_sound_of_definitely_init`: if `P` is initialized on every state in `R`, the rewrite is a refinement. This is the condition a forward "definitely initialized, with live storage" dataflow analysis evaluated at `parent_end` would establish.
- `eob_exhaustive_parent_refines`: with the exhaustive parent switch (a non-matching `Q` executes `unreachable`), the rewrite is a refinement for every `q` and every slot state. This is why the discriminant hoist is allowed in that case at all three revisions.

The three guards of 1.2 are modeled as `guardDiscriminantOnly` (2026-05-31), `guardStableOffset` (2026-11-11) and `guardUnchangedArgument` (2026-11-22), each a boolean function of the candidate's two flags, its place, and for the last one a record of whole-body facts about the base local.

- `eob_current_guard_introduces_uninit_and_deadLocal_ub`: for `arms = [(1, 3), (2, 4)]`, `dest = 5`, `q = 99` and the candidate "no discriminant hoist, reachable `otherwise`, place `_2` without projections", the 2026-05-31 guard and the 2026-11-11 guard both accept, the 2026-11-22 guard rejects (the local is not an argument), `runOrig` gives block 5 for both `uninit` and `dead`, and `runEob` gives an uninitialized read and a dead-local access respectively.
- `guardStableOffset_does_not_constrain_initialization`: for *every* candidate the 2026-11-11 guard accepts with a reachable `otherwise`, and every arm list, every `otherwise`-path state with `P` not initialized fails refinement. The guard has no input through which the state of `P` could matter.
- `stableOffset_place_never_dangling` and `stableOffset_place_can_be_any_non_dangling_state`: in a small place-evaluation model, a stable-offset place never denotes a dangling dereference, and can denote any of the other four slot states. This separates what the 2026-11-11 check achieves (issue 159591) from what it leaves open (issue 164765).
- `eob_unchangedArgument_sound` and `eob_unchanged_nonargument_local_unsound`: if the place starts initialized (a function argument) and no statement on the path to the parent block writes it, moves out of it, re-allocates it or writes through a borrow of it, the rewrite is a refinement; if it starts uninitialized under the same "nothing touches it" hypothesis, the rewrite fails on every `otherwise` path. This is the reasoning behind the 2026-11-22 guard, stated for the modeled effects.

The 2026-11-22 guard is a sufficient approximation of the exact condition, not the condition itself: it rejects, for instance, a local that is assigned in the entry block and never touched again, for which hoisting would be a refinement.

### 2. `SimplifyComparisonIntegral`

#### 2.1 The pass at the 2026-11-11 revision

Basis: source (`compiler/rustc_mir_transform/src/simplify_comparison_integral.rs`, 218 lines, identical at the 2026-11-22 revision).

The pass is enabled at MIR optimization level 2 or higher (lines 30-32) and runs right after `EarlyOtherwiseBranch`. The finder (lines 114-172) looks, in each block ending in `switchInt(discr)`, for the last statement assigning the switched place, and requires it to be `lhs = Eq(l, r)` or `lhs = Ne(l, r)` with one operand a constant of integer or `char` type and the other a `Copy` or `Move` of a place `to_switch_on` (lines 174-200). Both the switched place and `to_switch_on` must be based on an SSA local and be stable-offset places (lines 124 and 186). The last check (lines 139-151):

```rust
// The transformation adds a use of `to_switch_on` at the
// terminator. Both storage markers make the local uninitialized,
// so either invalidates the value used by the comparison.
if bb.statements[stmt_idx + 1..].iter().any(|stmt| {
    matches!(
        stmt.kind,
        StatementKind::StorageLive(local)
            | StatementKind::StorageDead(local)
            if local == to_switch_on.local
    )
}) {
    return None;
}
```

The rewrite (lines 41-106) keeps the comparison statement, replaces a `Move` operand in it by `Copy` (lines 76-94), and replaces the terminator by `switchInt(copy to_switch_on) -> [K: bb_cond, otherwise: bb_otherwise]`, with the two targets ordered according to whether the operator was `Eq` or `Ne` (lines 57-74 and 96-105). The comment on the downgrade:

```rust
// if the integer being compared to a const integral is being moved into the
// comparison, e.g `_2 = Eq(move _3, const 'x');`
// we want to avoid making a double move later on in the switchInt on _3.
// So to avoid `switchInt(move _3) -> ['x': bb2, otherwise: bb1];`,
// we convert the move in the comparison statement to a copy.
```

The comparison statement is left in place even when its result is no longer used; removing it is left to later dead-store elimination.

#### 2.2 The pass on the 2026-05-31 toolchain is an older design

Basis: source (253 lines at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and execution (probe key `simplify_comparison_integral`).

The older file differs in three ways: the enabling condition is written `sess.mir_opt_level() > 1`; when the terminator consumed the comparison result by move (`can_remove_bin_op_stmt: discr.is_move()`, line 187) the comparison statement is turned into a `nop` instead of being rewritten (lines 79-83); and a `StorageDead(to_switch_on.local)` in the block is turned into a `nop` and re-inserted at the top of every successor (lines 105-127 and 141-147). There is no check for storage markers. Between the two revisions the commit list for the file shows `a642d9b63c6236074005c10d52df5aef691b4815` ("don't try to remove assignments in SimplifyComparisonIntegral", 2026-06-21) and `e6b982a0156eaf2f429ee5233bac0e5d428659ef` ("don't optimize across StorageLive in SimplifyComparisonIntegral", 2026-07-27).

Four custom-MIR functions were compiled with `-Z mir-opt-level=0` and again with `-Z mir-enable-passes=+SimplifyComparisonIntegral` added. Block `bb0` before and after, on the 2026-05-31 toolchain:

| Input | Before | After |
|---|---|---|
| S1 | `_2 = Eq(move _1, const 43_i32); switchInt(copy _2) -> [1: bb1, otherwise: bb2]` | `_2 = Eq(copy _1, const 43_i32); switchInt(copy _1) -> [43: bb1, otherwise: bb2]` |
| S2 | `_2 = Ne(move _1, const 43_i32); switchInt(move _2) -> [1: bb1, otherwise: bb2]` | `nop; switchInt(copy _1) -> [43: bb2, otherwise: bb1]` |
| S3 | `StorageLive(_2); _2 = copy _1; _3 = Eq(move _2, const 43_i32); StorageDead(_2); switchInt(copy _3) -> [1: bb1, otherwise: bb2]` | `StorageLive(_2); _2 = copy _1; _3 = Eq(copy _2, const 43_i32); nop; switchInt(copy _2) -> [43: bb1, otherwise: bb2]`, and `StorageDead(_2)` now heads `bb1` and `bb2` |
| S4 | `_2 = Eq(move _1, const 43_i32); switchInt(move _1) -> [43: bb1, otherwise: bb2]` | unchanged |

Rows S1 and S4 exercise code that is the same at both revisions. Rows S2 and S3 show the older behavior; from the 2026-11-11 source, S2 would keep `_2 = Ne(copy _1, const 43_i32)` and S3 would not be transformed at all (derived, not executed). All four functions return the same results for inputs 43 and 7 with and without the pass, natively and under Miri (`x=43 S1=1 S2=0 S3=1 S4=1`, `x=7 S1=0 S2=1 S3=0 S4=0`).

#### 2.3 What "double move" means, and for whom it is undefined

Basis: execution, source, derived.

S4 is the shape the pass would produce if it kept the `move`: the local is moved into the comparison and then moved again by the terminator. On the 2026-05-31 toolchain this MIR passes `-Z validate-mir` and Miri executes it without any diagnostic, at MIR level 0, with and without `-C opt-level=2`. So neither the MIR validator nor Miri treats the second use as an error.

The Anneal trusted MIR semantics does. In `trusted/lean/Trusted/MirSemantics.lean` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `evalOperandToSlot` (line 949) evaluates `.move place` by reading the slot and then setting the local to `liveUninitSlot ty`, and returns the fault `.undefined` for a `.dead` local; `evalPrimitiveOperand` (line 1007), "used by `.binaryOp`, `.unaryOp`, and `.switchInt`", returns `.undefined` when the slot holds no value. Its documentation quotes the rustc interpreter's own note, "FIXME: do some more logic on `move` to invalidate the old location", and describes the de-initialization as "a deliberate, conservative over-approximation (sound because deinitializing can only introduce faults on subsequent reads)". Under that semantics (derived by reading the definitions; not executed):

- S4 faults at the terminator, because the comparison's `move _1` has de-initialized `_1`;
- the output of the pass, with `copy` in both places, does not;
- the hoisted `Ne(copy _1, copy _2)` of section 1 faults with `.undefined` for an uninitialized or dead `_2`, in agreement with Miri.

The `move`-to-`copy` downgrade is therefore what keeps the pass's output inside the set of MIR that a move-de-initializes semantics accepts. Under Miri's current treatment of `Move` operands it is not observable.

#### 2.4 The condition, mechanized

Basis: derived, kernel-checked (`EobFfi`, Part 2).

The model describes one block from the point of view of the compared local `x`: its slot state, the comparison `op` (`eq` or `ne`) against a constant `k`, the operand mode `m` (`copy` or `move`), a list `mid` of statements between the comparison and the terminator, each either irrelevant to `x`, `StorageLive(x)` (the slot becomes `uninit`) or `StorageDead(x)` (the slot becomes `dead`), and a boolean `deinit` choosing whether a `move` leaves its source uninitialized. A block run exposes the successor, the value left in the comparison temporary, and the final state of `x`; two runs are compared up to replacing a final `uninit` by a value.

- `simplifyComparisonIntegral_sound_iff`: for either value of `deinit`, either operator, either original operand mode, any constant and any targets, the rewritten block refines the original from every initial state of `x` if and only if `mid` contains no storage marker of `x`. The "only if" direction uses the state `init k`: the original block is defined, while the rewritten block reads `x` after the marker.
- `sciKeepMove_ub_under_move_deinit`: with `deinit = true`, the variant that keeps `move` in the comparison reads an uninitialized local at the terminator for every initialized input, and does not refine the original.
- `sciKeepMove_eq_sciPass_without_move_deinit`: with `deinit = false` that variant is literally equal to the pass.
- `sciPass_storageDead_between_concrete`: with `mid = [StorageDead(x)]`, constant 43 and `x = 43`, the original block is defined and the rewritten block reads a dead local. This is shape S3; the 2026-11-11 pass refuses it.

The model treats `StorageLive` on an already live local as "fresh uninitialized storage", following the source comment quoted in 2.1.

### 3. `ffi_unwind_calls` and `required_panic_strategy`

#### 3.1 Which bodies are flagged

Basis: source (2026-11-11 revision, `compiler/rustc_mir_transform/src/ffi_unwind_calls.rs`, lines 15-130).

`has_ffi_unwind_calls(def_id)` works on `mir_built`, the MIR before any pass. It returns `false` unless the item is function-like, and unless the body itself can unwind:

```rust
let body_can_unwind = layout::fn_can_unwind(tcx, Some(def_id), body_abi);
// Foreign unwinds cannot leak past functions that themselves cannot unwind.
if !body_can_unwind {
    return false;
}
```

It then scans the terminators of the non-cleanup blocks and marks the body as tainted for:

- `InlineAsm` whose options contain `MAY_UNWIND` (lines 51-76);
- a `Call` whose callee ABI is not a rustic ABI, when the callee is a function pointer, or a `FnDef` that is a foreign item, and `fn_can_unwind(tcx, fn_def_id, abi)` holds (lines 78-126).

Calls with a rustic ABI are skipped ("Rust calls cannot themselves create foreign unwinds"), and so are calls to a `FnDef` that is not a foreign item, whatever its ABI ("So the leak of the foreign unwind into Rust can only be elsewhere, not here"). Every flagged site also emits the allow-by-default lint `ffi_unwind_calls`.

`fn_can_unwind` (`compiler/rustc_middle/src/ty/layout.rs`, line 1321) returns `false` for any function *defined in Rust* when the session's panic strategy does not unwind (line 1332: "a `extern "C-unwind"` function defined in Rust is also required to abort"); otherwise it returns the `unwind` flag of a `C`-family ABI, `false` for the listed non-unwinding ABIs, and "the session's strategy unwinds" for the rustic ABIs.

#### 3.2 What a crate requires

Basis: source (same file, lines 132-173).

```rust
fn required_panic_strategy(tcx: TyCtxt<'_>, _: LocalCrate) -> Option<PanicStrategy> {
    let local_strategy = tcx.sess.panic_strategy();
    if tcx.is_panic_runtime(LOCAL_CRATE) {
        return Some(local_strategy);
    }
    match local_strategy {
        PanicStrategy::Abort | PanicStrategy::ImmediateAbort => return Some(local_strategy),
        _ => {}
    }
    for def_id in tcx.hir_body_owners() {
        if tcx.has_ffi_unwind_calls(def_id) {
            return Some(PanicStrategy::Unwind);
        }
    }
    // This crate can be linked with either runtime.
    None
}
```

So a panic runtime and any `panic=abort` crate require their own strategy; a `panic=unwind` crate requires `unwind` exactly when it has a flagged body, and otherwise nothing. The source comment gives the reason and names the issue: with `panic=unwind` "the `AbortUnwindingCalls` MIR pass will not be run on FFI-unwind call sites, therefore a foreign exception can enter Rust through these sites", while `panic=abort` crates expect "that all Rust functions cannot unwind (whether it's caused by Rust panic or foreign exception), and this expectation mismatch can cause unsoundness (#96926)". It also states why `None` is safe: with no flagged site, a foreign exception "can only enter Rust in a `panic=abort` crate, which will lead to an abort", and no Rust panic unwinds under the abort runtime. The 2026-11-22 revision differs from this file only in spelling `fn_sig(tcx).abi()` as `fn_sig_abi(tcx)`.

Upstream issue 96926 ("Mixing crates using different panic modes may introduce UB if a non-Rust unwind "escapes" into panic=abort crate via "C-unwind"", opened 2022-05-10, closed 2022-07-02) describes the pairing: a `panic=unwind` crate declaring `extern "C-unwind" { fn cpp_unwind(); }` and calling it from a Rust function, "then called from a crate compiled with `panic=abort`, the behavior is undefined, because the calling function will be compiled with the assumption that unwinding is impossible."

#### 3.3 Where the requirement is enforced, and under which condition

Basis: source (2026-11-11 revision, `compiler/rustc_metadata/src/dependency_format.rs`, `verify_ok`, lines 403-502).

`verify_ok` runs over the crates that are actually linked. After a separate block for the immediate-abort strategy, it finds the panic runtime among them, and then (abridged: struct fields and the `panic_in_drop` comparison are elided):

```rust
if let Some((runtime_cnum, found_strategy)) = panic_runtime {
    if found_strategy != desired_strategy {
        sess.dcx().emit_err(BadPanicStrategy { .. });
    }
    for cnum in list.iter().copied() {
        if cnum == runtime_cnum || tcx.is_compiler_builtins(cnum) {
            continue;
        }
        if let Some(found_strategy) = tcx.required_panic_strategy(cnum)
            && desired_strategy != found_strategy
        {
            sess.dcx().emit_err(RequiredPanicStrategy { crate_name, found_strategy, desired_strategy });
        }
        ...
    }
}
```

Three properties follow directly:

1. The comparison is an inequality test in both directions. A `panic=abort` rlib (`Some(Abort)`) is rejected in a `panic=unwind` link just as a flagged `panic=unwind` rlib is rejected in a `panic=abort` link. The comment above the loop says "if our strategy is abort then it's compatible with everything"; the code does not special-case abort that way, and the execution in 3.5 follows the code.
2. The `compiler_builtins` crate is never checked.
3. The whole comparison is inside `if let Some(..) = panic_runtime` (line 460; line 461 in the 2026-05-31 sources). If no linked crate is a panic runtime, no crate's requirement is compared with anything.

#### 3.4 The abort guard

Basis: source (2026-11-11 revision, `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`) and execution (probe key `ffi_unwind_link_matrix`, field `upstream_call_terminators`).

`AbortUnwindingCalls` is a required pass (line 145). For each call-like terminator it computes `call_can_unwind` from `fn_can_unwind` of the callee (or the `may_unwind` option, or the drop and assert rules), and then (lines 117-135):

- if the call cannot unwind, the unwind action becomes `UnwindAction::Unreachable`;
- else if the enclosing body cannot unwind and the action was `Continue`, it becomes `UnwindAction::Terminate(UnwindTerminateReason::Abi)`;
- else it is left alone.

The emitted MIR on the 2026-05-31 toolchain shows each case:

| Upstream body | `-C panic` | Call terminator |
|---|---|---|
| Rust fn calling a foreign `"C-unwind"` item | unwind | `_0 = may_throw(copy _1) -> [return: bb1, unwind continue];` |
| Rust fn calling a foreign `"C-unwind"` item | abort | `_0 = may_throw(copy _1) -> [return: bb1, unwind: bb2];` with one `terminate(abi)` in the cleanup block |
| `extern "C"` fn calling a foreign `"C-unwind"` item | unwind | `_0 = may_throw(copy _1) -> [return: bb1, unwind terminate(abi)];` |
| Rust fn calling a foreign `"C"` item | unwind | `_0 = may_throw(copy _1) -> [return: bb1, unwind unreachable];` |
| Rust fn calling a Rust fn | abort | `... -> [return: bb1, unwind unreachable];` |

The first row is the unguarded site that `has_ffi_unwind_calls` flags. The last row is what a `panic=abort` caller emits for a call into any Rust function, including one that lives in a `panic=unwind` crate.

#### 3.5 The link matrix

Basis: execution on the 2026-05-31 toolchain (probe key `ffi_unwind_link_matrix`).

Each upstream crate is an rlib named `ffi_up` exposing `pub fn entry(u32) -> u32`; the downstream crate is a `std` binary that defines `may_throw` and calls `ffi_up::entry`. Nothing actually unwinds in these runs; the matrix tests the link decision.

| Upstream body of `entry` | Upstream `-C panic` | Downstream `-C panic` | Lint at upstream site | Link |
|---|---|---|---|---|
| pure Rust | unwind | abort | none | ok, runs |
| calls foreign `"C-unwind"` item | unwind | abort | `call to foreign function with FFI-unwind ABI` | error |
| calls foreign `"C"` item | unwind | abort | none | ok, runs |
| calls an `extern "C"` Rust fn that calls the foreign `"C-unwind"` item | unwind | abort | none | ok, runs |
| calls a `"C-unwind"` function pointer | unwind | abort | `call to function pointer with FFI-unwind ABI` | error |
| calls a Rust-defined `extern "C-unwind"` fn | unwind | abort | none | ok, runs |
| `asm!("nop", options(may_unwind))` | unwind | abort | `call to inline assembly that may unwind` | error |
| calls foreign `"C-unwind"` item | unwind | unwind | (as above) | ok, runs |
| calls foreign `"C-unwind"` item | abort | abort | none | ok, runs |
| calls foreign `"C-unwind"` item | abort | unwind | none | error |
| pure Rust | abort | unwind | none | error |
| pure Rust | abort | abort | none | ok, runs |

The two error texts are ``error: the crate `ffi_up` requires panic strategy `unwind` which is incompatible with this crate's strategy of `abort` `` and the same sentence with the two strategy names exchanged. Every row agrees with 3.1 to 3.3. The lint is silent in `panic=abort` upstream builds because no body there can unwind.

The preserved record for the 2026-11-11 revision (1.5) contains rows 1 and 2 of this matrix with the same outcomes and the same error text.

#### 3.6 A link without a panic runtime is not checked

Basis: execution on the 2026-05-31 toolchain (probe key `ffi_unwind_no_std_link`), source (3.3, property 3), documentation (Reference).

The pairing of row 2 was rebuilt without `std`: the upstream rlib is `#![no_std]` and unchanged otherwise; the downstream crate is `#![no_std] #![no_main]` with its own `#[panic_handler]` and an `extern "C" fn main`. Compiled with `-C panic=unwind` upstream and `-C panic=abort` downstream:

- both compiles and the link succeed without any error, and the program runs and exits 0;
- the upstream MIR contains `_0 = may_throw(copy _1) -> [return: bb1, unwind continue];`
- the downstream MIR contains `_2 = entry(move _3) -> [return: bb2, unwind unreachable];`

In a `no_std` link no crate is a panic runtime, so by property 3 of 3.3 the loop that would have emitted the row-2 error is not executed. The result is a linked artifact in which a foreign exception thrown by `may_throw` would propagate out of `entry` into a frame whose call site was compiled as non-unwinding.

The Reference at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/linkage.md`, rules `link.unwinding.potential` and `link.unwinding.prohibited`) defines an artifact as potentially unwinding if, among other conditions, it "contains a crate built with the `unwind` panic strategy that makes a call to a function using a `-unwind` ABI", requires that then "all its crates must be built with the `unwind` panic strategy. Otherwise, unwinding can cause undefined behavior", and adds in a note: "If you are using `rustc` to link, these rules are enforced automatically." The artifact above is potentially unwinding by that definition, contains a crate built with `abort`, and was linked by `rustc`. The documentation and the observed behavior of the 2026-05-31 toolchain disagree for this configuration. This report records the disagreement and does not resolve which side is intended.

No foreign exception was thrown in this experiment, so no runtime misbehavior was observed; see Boundaries.

#### 3.7 The link check, mechanized

Basis: derived, kernel-checked (`EobFfi`, Part 3).

A link is a list of crates. A crate has the strategy it was compiled with, two flags (panic runtime, `compiler_builtins`) and a list of functions; a function has an ABI class (rustic, non-rustic permitting unwinding, non-rustic not permitting it) and a list of call sites (rustic call to a Rust function, non-rustic call to a Rust function, foreign item, function pointer, inline assembly, the last three with their unwind flag). `bodyCanUnwind`, `callCanUnwindAsSeenBy`, `hasFfiUnwindCalls`, `requiredPanicStrategy` and `linkOk` transcribe the decisions of 3.1 to 3.4, including the panic-runtime condition and the `compiler_builtins` exemption. The immediate-abort strategy is not modeled.

Unwinding is an inductive predicate `MayUnwindOut final link crate fn`: an unwind can leave a body that was compiled as able to unwind if (i) the body has a flagged foreign site, or (ii) the final strategy is `unwind` (a Rust panic), or (iii) it calls, through a site compiled with a landing pad, a Rust function out of which an unwind can come. `UnwindReachesNounwindSite` says that some body calls, through a site its own crate compiled as non-unwinding, a Rust function out of which an unwind can come.

- `crossCrateLink_no_uncaught_foreign_unwind_in_abort_crate`: if the final strategy is `abort`, some crate in the link is a panic runtime, the exempted `compiler_builtins` crate has no flagged site in a body that can unwind, and `linkOk` accepts, then no body in the link lets an unwind out and no unwind reaches a non-unwinding call site.
- `unchecked_link_admits_foreign_unwind_into_abort_crate`: for the row-2 pairing, `linkOk` rejects; and in that link an unwind can leave the upstream `entry` and reaches the downstream call site, which was compiled as non-unwinding. This is issue 96926 in the model.
- `no_panic_runtime_link_is_unchecked`: the same two crates in a link without a panic runtime are accepted by `linkOk`, and the unwind still reaches the non-unwinding site. This is 3.6 in the model.
- `compilerBuiltins_exemption_is_trusted`: marking the leaking crate as `compiler_builtins` also makes `linkOk` accept. The hypothesis about that crate in the main theorem cannot be dropped.
- `pureRust_unwind_crate_requires_nothing`, `pureRust_unwind_crate_links_with_either`: a `panic=unwind` crate that is not a panic runtime and has no flagged site requires nothing and is compatible with both final strategies.
- `linkOk_unwind_all_crates_unwind`: in an accepted `unwind` link with a panic runtime every crate except `compiler_builtins` was compiled with `panic=unwind`.
- `linkMatrix`: the twelve decisions of the table in 3.5, evaluated in the model, equal the observed ones.

### 4. The Lean development as a whole

Basis: execution of the checker (`support/lean_check_output.txt`).

`support/EarlyOtherwiseBranchAndFfiUnwindSoundness.lean` has 1299 lines (1136 non-blank), 52 theorems, 56 definitions, 3 abbreviations, 12 inductive types and 7 structures, all in the namespace `EobFfi`. It imports the `Lean` package only so that the final command can inspect the environment; the model itself uses nothing beyond the core library.

It was checked with Lean v4.34.1 using `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, exit status 0. The file ends with an audit command that fails the whole check unless every declaration of the module in `EobFfi` depends on no axiom other than `propext` and `Quot.sound`, and no constant declared by the module is a compiler-generated unsafe-recursion helper. Its output for the checked file: `audit ok: 646 declarations in EobFfi (197 theorems); axioms used: [Quot.sound, propext]; unsafe recursion helpers in this module: 0; imported constants in EobFfi: 0`, followed by `environment: 661 constants declared by this module; 208024 imported constants, of which 3016 are unsafe recursion helpers of the imported libraries` (the counts include auto-generated declarations). Ten of the eleven headline theorems depend on `propext` only; `crossCrateLink_no_uncaught_foreign_unwind_in_abort_crate` depends on `propext` and `Quot.sound`.

Two properties of this toolchain shaped the file and are worth knowing when extending it:

- In Lean v4.34.1 every `def` written with structural recursion produces an auxiliary constant whose name ends in the unsafe-recursion suffix (observed for two throwaway list functions). The file therefore contains no recursive `def` at all: list traversals use `List.lookup`, `List.any`, `List.all` and `List.foldl`, and recursion appears only in proofs (`induction`) and in one inductive predicate.
- Constants declared by the file being checked are in the second stage of the environment's constant map (`Environment.constants.map₂`); the first stage (`map₁`) holds imported constants only. An audit that inspects only the first stage sees none of the file's own declarations. With `import Lean` the first stage holds 208,024 constants, 3,016 of them unsafe-recursion helpers from the imported libraries, none in `EobFfi` (both numbers are printed by the check). The audit command inspects the second stage and, separately, confirms that the first stage contains nothing in the file's namespace.

The audit was exercised against three deliberately broken copies of the file (one extra theorem proved with the classical excluded middle, one extra recursive `def`, one extra theorem with an unfinished proof). Each copy failed with exit status 1 and the corresponding audit message. The copies are not preserved; the three injected fragments are listed under Revalidation.

### 5. Consequences for reasoning about compiled Rust from MIR

Basis: derived from sections 1 to 3.

- A property proved about a function's MIR *before* `EarlyOtherwiseBranch`, under a semantics in which the function is defined for an input, does not transfer to the artifact produced by the 2026-05-31 toolchain, and by the source argument not to the one produced by the 2026-11-11 revision, when the function contains the two-level switch shape with a reachable `otherwise` and a child place that is not initialized on that edge. Inputs (c) and (d) are complete examples: the unoptimized MIR is defined for every input and the binary returns a different value.
- A property proved about the MIR *after* the pass is not affected in the same way: a semantics that faults on reads of uninitialized or dead locals rejects the hoisted read, so the defect shows up as a failed proof for a defined program rather than as an accepted wrong one.
- A tool that consumes MIR and assigns de-initializing semantics to `Operand::Move` depends on passes such as `SimplifyComparisonIntegral` not introducing a second use after a move. At the 2026-11-11 revision the pass upholds this by construction (2.1); neither the MIR validator nor Miri would detect a violation (2.3).
- "No unwind crosses a frame compiled with `panic=abort`" is established by rustc's link check only under the hypotheses of the theorem in 3.7. For a `no_std` program, for links performed by another tool, and for whatever `compiler_builtins` contains, it is an assumption.

## Boundaries

**Not examined**

- No toolchain other than `rustc 1.98.0-nightly (14210df0e 2026-05-31)` was executed. In particular the 2026-11-11 and 2026-11-22 revisions were not run: where this investigation was carried out, only the already-installed toolchain was available. All statements about those revisions are from source, from upstream issue text, or from the preserved record, as marked.
- No stable or beta release was examined, by source or by execution. Whether a given stable release contains the unguarded hoist was not determined.
- Targets other than `x86_64-unknown-linux-gnu`. Upstream issue 164765 reports the same wrong value (200) on `aarch64-apple-darwin`; that was not reproduced here.
- The discriminant-hoisting shape (`need_hoist_discriminant`) was read but not executed, and the model treats a discriminant read as a scalar read.
- Runtime behavior of an actual foreign exception. In 3.5 and 3.6 nothing unwinds. That a foreign exception arriving at an `unwind unreachable` site misbehaves is taken from the Reference and from issue 96926, not observed.
- `PanicStrategy::ImmediateAbort`, the `panic_in_drop` strategy check, dynamic libraries, and links not performed by `rustc`.
- `SimplifyComparisonIntegral` on places with projections, and its handling of pointer-valued constants (`Scalar::Ptr`, which it skips).
- The interaction of `EarlyOtherwiseBranch` with every other pass. Only the default pipeline and "pipeline minus this one pass" were compared.
- The Anneal semantics was read, not run: no MIR from this report was encoded as a term of that model.

**Unknown**

- Whether the preserved record's `eob_dead_local_ub` is the same function as input (b) of this package (1.5).
- Whether the absence of the link check without a panic runtime (3.6) is intended upstream. No upstream issue or documentation addressing it was looked for beyond the Reference text quoted.
- Whether the 2026-11-22 guard is complete for all places it accepts. The model shows the argument-is-untouched reasoning; it does not model types, so "a struct or tuple field of a valid argument is initialized" is an assumption of the model, justified informally by the validity requirement on by-value arguments.
- Why Miri accepts the hand-written double move (2.3) at the level of Miri's design: the observation is that it does, on one toolchain.

**Known not to apply**

- The `EarlyOtherwiseBranch` defect does not apply to builds at `-C opt-level=0` without an explicit `-Z mir-opt-level` of 2 or more: the pass does not run (inputs (d) and (e) are correct there).
- It does not apply when the parent switch is exhaustive (1.7, `eob_exhaustive_parent_refines`).
- The stable-offset check of the 2026-11-11 revision does prevent the raw-pointer case (e) at that revision, by source: `*_2` is not a stable-offset place. The segmentation fault in 1.4(e) is specific to revisions before commit `a22fed77686db50c1185e4267743924ac50f584a`.
- The S2 and S3 rows of 2.2 do not describe the 2026-11-11 pass.
- The `ffi_unwind_calls` lint and `Some(Unwind)` do not arise for calls to Rust-defined functions of any ABI, nor inside bodies that cannot unwind.

**Unsupported**

- Direct invocation of the `miri` driver binary, as the probe does, is described by the driver itself as unsupported ("directly invoking the `miri` binary is not supported; please use `cargo miri` instead" appears when no Miri sysroot is given). The probe passes `--sysroot` pointing at a sysroot built by `cargo miri setup`, which works on the examined toolchain.
- `custom_mir` is an internal, unstable feature. Inputs (a), (b), (c) and the four `SimplifyComparisonIntegral` inputs depend on it.

**Stronger conclusions the evidence does not support**

- "rustc 1.102.0-nightly miscompiles input (d)": plausible from the source and the upstream regression test, not observed here.
- "The 2026-11-22 guard is the definite-initialization analysis": it is a conservative syntactic approximation; the upstream change says so itself.
- "A program is free of this defect if Miri accepts it at `-Zmir-opt-level=2`": false for inputs (d) and (e) with Miri's default arguments.
- "The mechanized theorems are about rustc": they are about a hand-written model whose correspondence to rustc is argued in prose in sections 1.7, 2.4 and 3.7 and is not itself checked.
- "The `no_std` link in 3.6 is a demonstrated miscompilation": it is an accepted link whose MIR has the unsound shape; no misbehavior was produced.

## Evidence

All upstream material was read on 2026-11-22. Revision identifiers were resolved through the GitHub commits API on that date; file contents were fetched by full revision from `raw.githubusercontent.com`. SHA-256 values are of the fetched file contents.

### rust-lang/rust at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`

Commit subject "Auto merge of #165821", committed 2026-11-11T17:59:24Z.

| Path | Lines used | SHA-256 |
|---|---|---|
| `compiler/rustc_mir_transform/src/early_otherwise_branch.rs` (421 lines) | 96-200 `MirPass` impl; 211-315 `evaluate_candidate`; 317-421 `verify_candidate_branch`; 329-383 guards | `4db5c025fcf94941be71291a50fe8f505b59c35bb47138de0b29d031a512978e` |
| `compiler/rustc_mir_transform/src/simplify_comparison_integral.rs` (218 lines) | 27-108 pass; 76-94 move-to-copy; 114-172 finder; 139-151 marker scan; 174-200 operand classification | `c2fef52205e7c9493a9809e6e05e8dbd036b876239e57de94a152c6e5f1a44e5` |
| `compiler/rustc_mir_transform/src/ffi_unwind_calls.rs` (177 lines) | 15-130 `has_ffi_unwind_calls`; 132-173 `required_panic_strategy` | `c3f083c0eb82ec2256d3f186a7719c31c528497d53371da3321d5509ec2767f9` |
| `compiler/rustc_metadata/src/dependency_format.rs` | 403-502 `verify_ok`; 460 runtime condition; 474-486 comparison | `c03923941a8da1fa95dc031554772a3a97faa20ed4e0ee08ac153cf6571ee24c` |
| `compiler/rustc_middle/src/ty/layout.rs` | 1321-1384 `fn_can_unwind`; 1332 abort rule | `c2dd3910865b3aecedd282c1f8c83afa3c6504347b8ae3df51655402cd0a9911` |
| `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` (147 lines) | 90-135 unwind actions; 145 required | `958dfcbbe6cc2dde935ff10dc6fe71dfcaaeb451b9ee9a4eced1fcc98afbe27b` |
| `compiler/rustc_middle/src/mir/statement.rs` | 279-290, 383-385 `is_stable_offset` | `26807fee09ef3e984c5f7e6cc23523546385af1321b6462b506f7a8bad18bebd` |
| `compiler/rustc_mir_transform/src/lib.rs` | 669 `AbortUnwindingCalls`; 728 `RemoveStorageMarkers`; 764-766 pass order | `16aad377ca3dccd2b436be7cd3a1a07b925301d3521c908f0195357d88091912` |
| `compiler/rustc_mir_transform/src/remove_storage_markers.rs` (27 lines) | 12-14 enabling condition | not recorded |
| `compiler/rustc_session/src/session.rs` | 883-884 `emit_lifetime_markers`; 987-989 `mir_opt_level` | not recorded |
| `src/tools/miri/src/lib.rs` | 200-216 `MIRI_DEFAULT_ARGS` | not recorded |

### rust-lang/rust at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`

Commit subject "Auto merge of #157219", committed 2026-05-31T20:13:59Z. The four files marked with an asterisk were compared byte for byte between the GitHub revision and the `rustc-src` component of the executed toolchain and are identical.

| Path | Lines used | SHA-256 |
|---|---|---|
| `compiler/rustc_mir_transform/src/early_otherwise_branch.rs`* (401 lines) | 96-98 enabling; 214-351 `evaluate_candidate`; 263-296 discriminant restriction; 325-330 destination; 353-401 `verify_candidate_branch` | `f1cb4612f5cad152bc0f1edbe7ccb63ad3c0b8ccf8bb5feb229ea34789d1f62d` |
| `compiler/rustc_mir_transform/src/simplify_comparison_integral.rs`* (253 lines) | 31-33 enabling; 79-103 nop or move-to-copy; 105-127, 141-147 `StorageDead` relocation; 187 `can_remove_bin_op_stmt` | `32e44cece543da05b3fecb45d0d6ab3eb99af04bc043d3a243d8880fdba35282` |
| `compiler/rustc_mir_transform/src/ffi_unwind_calls.rs`* (177 lines) | 15, 132 | `0b9e273896daa9d3c98da73a2cb2c8c95ff2ee27072eba875412dcb7938b3c6e` |
| `compiler/rustc_metadata/src/dependency_format.rs`* | 404 `verify_ok`; 461 runtime condition | not recorded |
| `compiler/rustc_mir_transform/src/lib.rs` | 640, 714, 750-752 | not recorded |
| `compiler/rustc_mir_transform/src/remove_storage_markers.rs` | 10-12 | not recorded |
| `compiler/rustc_mir_transform/src/remove_place_mention.rs`, `simplify.rs` | 11; 130 (`mir_preserve_ub`) | not recorded |
| `compiler/rustc_session/src/session.rs` | 547-548; 617-622 | not recorded |
| `src/tools/miri/src/lib.rs` | 183-199 `MIRI_DEFAULT_ARGS` | not recorded |

The lines in the last five rows were read from the toolchain's `rustc-src` component (and, for Miri, from the GitHub revision).

### rust-lang/rust at `01afe534803b93889b85f6028117251cfbd431da`

Commit subject "Auto merge of #166288", committed 2026-11-22T13:52:58Z; the result of resolving `HEAD` when observed.

| Path | Lines used | SHA-256 |
|---|---|---|
| `compiler/rustc_mir_transform/src/early_otherwise_branch.rs` (431 lines) | 316-325 new guard; 385-431 `UnchangedArguments` | `4de812cadf63fe6f91c61979ccced57be242890d642f3b2b9906b1ac442da47d` |
| `compiler/rustc_mir_transform/src/simplify_comparison_integral.rs` | whole file, identical to the 2026-11-11 revision | `c2fef52205e7c9493a9809e6e05e8dbd036b876239e57de94a152c6e5f1a44e5` |
| `compiler/rustc_mir_transform/src/ffi_unwind_calls.rs` | differs from the 2026-11-11 revision at lines 29, 81, 85 and 103 only | `933fb766610ae2afd4d3fce4cb30ef1031333be92f505a06c5b484269dc90240` |
| `compiler/rustc_mir_transform/src/lib.rs` | 766-768 pass order | not recorded |
| `tests/ui/mir/hoist_uninit_early_else.rs`, `tests/ui/mir/hoist_discriminant_early_else.rs`, `tests/mir-opt/early_otherwise_branch_arguments.rs` | present; the first is the source of input (d) | not recorded |

### Commits, issues and the pull request (rust-lang/rust)

- Commit lists for `early_otherwise_branch.rs` and `simplify_comparison_integral.rs` (GitHub commits API, `path=` filter): the commits and dates quoted in 1.2 and 2.2.
- Pull request 164864, "Avoid hoisting uninitialized reads in EarlyOtherwiseBranch": head `43dc29bb3fab2a69f47900f562f4b1315dda8bcf`, merge commit `9c4122425e680b510907d1ca643ee9b0815052fb`, merged 2026-11-13T16:18:01Z; 12 files changed, including the three test files above.
- Issues 95162, 96926, 159591 and 164765: titles, dates, labels and the passages quoted in 1.6 and 3.2.

### Other repositories

- `rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (result of resolving `HEAD`, committed 2026-11-17T20:49:56Z): `src/behavior-considered-undefined.md` lines 19, 56, 134 and 200 (SHA-256 `aa140daf1029fc523ec167345d5697b0741973464c90c3902e9e3574cb696555`); `src/linkage.md` lines 154-176, rules `link.unwinding.*` (`9a5c108d2e2e2a5a5bda0c4a6926fd1791621e124d273944b21d5357853f1c44`); `src/panic.md` lines 86-101 and 118-128 (`a327d969688c61e26888e87a2bb172268b66963208c02a0deb60c8012109b480`).
- `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (commit subject "[theory] Bridge PureLift onto Trusted MIR semantics (#266)", 2026-11-19): `trusted/lean/Trusted/MirSemantics.lean` (2681 lines, SHA-256 `b8378127ea7b81b473a5f86cd164df430feb56296cbbbe57457cc2b125316c0a`), lines 916-976 `evalOperandToSlot` and its documentation, 978-1018 `evalPrimitiveOperand` and its documentation. Read from a local clone containing that commit.
- `leanprover/lean4`: tag `v4.34.1` resolves to `5045d0056413266e57c625dcd7c365b10e377c52`, which is also the commit printed by `lean --version` of the checker used.

### Execution

Environment: `x86_64-unknown-linux-gnu`, Intel Xeon (8 logical CPUs), `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM 22.1.6, the `miri` driver of the same toolchain with a sysroot built by `cargo miri setup`, system `cc` as linker driver.

Command:

```text
python3 support/probe_early_otherwise_branch_uninit_miscompile_and_ffi_unwind.py \
    --rustc <toolchain>/bin/rustc --miri <toolchain>/bin/miri \
    --miri-sysroot <sysroot built by cargo miri setup> \
    --out support/probe_results_rustc_1.98.0-nightly_14210df0e.json
```

The script writes every input into a temporary directory, records the `rustc -Vv` text, and stores for each case the flags, exit statuses, standard output, the MIR text of the function, the LLVM IR of the function, the instructions of the function in the generated assembly together with the number of direct calls to it, and the `error`-level diagnostics. A run takes about 20 seconds. The preserved JSON is the output of the last of several runs made on 2026-11-22; the runs agreed in everything reported here except the arbitrary number printed by input (a) at MIR level 2.

Lean check: `support/lean_check_output.txt` holds the `lean --version` line, the command line, the complete output and the exit status.

### Preserved support material

| File | Role | SHA-256 |
|---|---|---|
| `support/probe_early_otherwise_branch_uninit_miscompile_and_ffi_unwind.py` | probe: all Rust inputs, the driver, the JSON writer | `cee06cbac1d06171deb605eed9eb271aef616fd0ddd637139c859ff86e07b23b` |
| `support/probe_results_rustc_1.98.0-nightly_14210df0e.json` | output of the probe on the 2026-05-31 toolchain | `0a501a470439a52b17db38b4be2d3dbae908307e1c141871b1faeca4ee8f3408` |
| `support/recorded_observation_rustc_1.102.0-nightly_3ef0c22cd.json` | earlier execution record for the 2026-11-11 revision, unmodified | `b6f540399502783a3903d8b42d524a42749e22d9d858ed873e33d93ea89de43f` |
| `support/EarlyOtherwiseBranchAndFfiUnwindSoundness.lean` | mechanized model and audit command | `556d378a3841e1efe7d2621a22a21af3f66afffdfc79039548a747ece04e0c65` |
| `support/lean_check_output.txt` | checker transcript | `a05a99cb9a569bc2b92695fd6df2dcefdbb553ed6770e0223608ea7bd1f4af26` |

The preserved record's `probe_id` field is an identifier internal to the process that produced the file and has no meaning for this report.

## Revalidation

**Is the hoist still performed by a given toolchain?** Run the probe against that toolchain's `rustc` (nightly required) and look at `summary` in the output:

- `eob_surface_union.native_stdout_opt_level_3` equal to `native_stdout_opt_level_0` means input (d) is compiled correctly. A difference reproduces the defect. This check needs no Miri.
- `eob_never_initialized_local.hoisted_at_mir_opt_2` says whether a non-argument local is still hoisted. On a toolchain containing commit `43dc29bb3fab2a69f47900f562f4b1315dda8bcf` it should be `false`; this report did not run such a toolchain, so the expectation is from source.
- `eob_surface_deref.native_run_rc_opt_level_3` equal to `-11` identifies a toolchain older than commit `a22fed77686db50c1185e4267743924ac50f584a`.

A one-file check without the probe: compile the `union` program of 1.4(d) with `-C opt-level=3` and with `-C opt-level=3 -Z mir-enable-passes=-EarlyOtherwiseBranch`, and compare the outputs for `q = 0`.

**Has the guard changed?** Diff `compiler/rustc_mir_transform/src/early_otherwise_branch.rs` against the 2026-11-22 revision and look at the condition guarding `!otherwise_is_empty_unreachable` in `evaluate_candidate` and at `UnchangedArguments::{new, can_hoist}`. Any new way for a place to qualify has to be checked against the condition of 1.7: initialized, with live storage, on every path that reaches the end of the parent block and takes the `otherwise` edge.

**Does Miri see it?** For MIR built from surface Rust, pass `-Zmir-opt-level=2 -Zmir-preserve-ub=no`; the probe's `mir_opt_2_preserve_ub_off` rows do this. If `-Zmir-preserve-ub` changes meaning or default, rerun the two `eob_surface_*` cases and compare the `default_preserve_ub` and `preserve_ub_off` rows.

**`SimplifyComparisonIntegral`.** Compare `simplify_comparison_integral.mir` in the probe output for S1 to S4 with the table in 2.2. On a toolchain at or after the 2026-11-11 revision, S2 is expected to keep a comparison statement with a `copy` operand and S3 is expected to be unchanged by the pass; this expectation is from source and has not been run. If S4 starts failing `-Z validate-mir` or Miri, the treatment of repeated moves has changed and 2.3 needs to be revisited.

**Panic-strategy linking.** `summary.ffi_link_matrix` must equal the table in 3.5. `summary.ffi_no_std_unwind_rlib_with_ffi_unwind_call_into_abort_binary_links` is `true` on the 2026-05-31 toolchain; `false` on another toolchain means the check now covers links without a panic runtime, and 3.6 no longer applies to it. In source, the question is whether the loop over `required_panic_strategy` in `verify_ok` is still nested under `if let Some(..) = panic_runtime`.

**The mechanized model.** With Lean v4.34.1:

```text
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/EarlyOtherwiseBranchAndFfiUnwindSoundness.lean
```

must exit 0 and print a line starting `audit ok:`. To confirm that the audit is effective, insert one of the following just before `end EobFfi` and check that the command fails with the matching message: a theorem `negClassical (p : Prop) : p ∨ ¬ p` proved by the classical excluded middle (message names the choice axiom); a recursive definition such as a list-length function written by pattern matching (message lists an unsafe-recursion helper); a theorem whose proof is left unfinished (message names the placeholder axiom). A passing check shows that the stated theorems hold of the model. It does not show that the model matches a newer rustc; for that, compare the definitions `runEob`, `sciRewritten`, `requiredPanicStrategy` and `linkOk` with the source regions listed under Evidence.

**What cannot be rechecked cheaply.** The claim about the 2026-11-11 revision's runtime behavior requires installing that nightly and running the probe. By the naming pattern of the executed toolchain (installed as `nightly-2026-06-01`, commit date 2026-05-31) the nightly dated 2026-11-12 is expected to be that revision; confirm with `rustc -Vv`. This was not possible where this report was written and remains to be done.
