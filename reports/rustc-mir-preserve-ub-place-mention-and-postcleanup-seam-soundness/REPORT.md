# `-Zmir-preserve-ub`, `StatementKind::PlaceMention`, `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`: `Runtime(PostCleanup)` Pre-Capture UB Erasure, RFC 2582 Semantics, `-Zub-checks` Blind Spots, and Anneal TCB Capture Seam Completeness

## Summary

In `rust-lang/rust`, the unstable compiler flag `-Zmir-preserve-ub` (default `false`) directly gates whether undefined behavior (UB) carried by `StatementKind::PlaceMention` and equal-target `TerminatorKind::SwitchInt` discriminants survives lowering across `run_runtime_cleanup_passes` into `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`compiler/rustc_mir_transform/src/lib.rs:682-696` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, lines `653-673` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). When `-Zmir-preserve-ub` is unset (`false`, the compiler default):

1. **`RemovePlaceMention`** (`compiler/rustc_mir_transform/src/remove_place_mention.rs:1-25` at `3ef0c22cdb`; lines `1-27` at `14210df0e2`) runs with `PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)` prior to `MirPhase::Runtime(RuntimePhase::PostCleanup)` and deletes every `StatementKind::PlaceMention(..)` and `StatementKind::Nop` statement. Because `PlaceMention(place)` executes `InterpCx::eval_place(**place, false)?` (`compiler/rustc_const_eval/src/interpret/step.rs:118-123`) rather than performing a no-op, deleting it silently erases live UB triggers including non-zero field/index `OffsetMode::Inbounds` pointer-arithmetic violations (such as `unsafe { let _ = (*null_pair).1; }` or `(*one_byte_ptr).1` on a 1-byte stack allocation).
2. **`SimplifyCfg::PreOptimizations`** (`compiler/rustc_mir_transform/src/simplify.rs:130-137, 308-330` at `3ef0c22cdb`; lines `128-135, 307-329` at `14210df0e2`) computes `preserve_switch_reads = matches!(body.phase, MirPhase::Built | MirPhase::Analysis(_)) || tcx.sess.opts.unstable_opts.mir_preserve_ub`. Because `body.phase` has already entered `MirPhase::Runtime(Initial)` before `run_runtime_cleanup_passes`, `preserve_switch_reads` flips to `false`, collapsing equal-target `SwitchInt` terminators (all case arms equal to `otherwise`) into unconditional `TerminatorKind::Goto` edges and silently erasing uninitialized/invalid-discriminant reads even when zero `PlaceMention` statements exist.
3. **`compiler/rustc_session/src/options.rs` option documentation disagrees with `session.rs`**: while `options.rs:2729-2731` (`2469-2471` in `14210df0e2`) claims `-Zmir-preserve-ub` `"implies -Zmir-opt-level=0"`, `Session::mir_opt_level` (`compiler/rustc_session/src/session.rs:987-989`) ignores `mir_preserve_ub`. Empirically, `-Zmir-preserve-ub=yes` alone still runs `Runtime(Optimized)` branch folding and dead-branch elimination unless `-Zmir-opt-level=0` is also supplied explicitly (which Miri's `MIRI_DEFAULT_ARGS` explicitly does in `src/tools/miri/src/lib.rs:200-218` / `183-200`).
4. **Native `-Zub-checks=yes` does not inspect `PlaceMention`**: `CheckAlignment`, `CheckNull`, and `CheckEnums` execute in `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:700-715`) *after* `Runtime(PostCleanup)` (`lib.rs:709-710`), and their shared `PointerFinder` visitor (`compiler/rustc_mir_transform/src/check_pointers.rs:160-176`) ignores `NonMutatingUseContext::PlaceMention` (`compiler/rustc_middle/src/mir/visit.rs:455-461`). Consequently, native execution with `-Zub-checks=yes -Zmir-preserve-ub=yes -Zmir-opt-level=0` still exits `0` cleanly on `unsafe { let _ = (*null_pair).1; }` with zero emitted UB checks.
5. **`Derefer` is *not* gated by `-Zmir-preserve-ub`**: correcting a pre-existing inaccuracy in the corpus companion report `rustc-mir-phases-reachability-and-postcleanup-lowering`, `Derefer` runs inside `run_analysis_cleanup_passes` (`lib.rs:648` / `613`) with `PassPolicy::Required` (`deref_separator.rs:103-106`), followed by required `EraseDerefTemps` (`lib.rs:673`, `erase_deref_temps.rs:42-45`). On chained dereferences like `(*(*pp)).1`, `Derefer` hoists the inner load into a temporary copy `_tmp = copy (*pp)` before `RemovePlaceMention`, so inner uninitialized/null reads survive default `RemovePlaceMention`, whereas the outer `PlaceMention(((*_tmp).1))` inbounds check does not.
6. **RFC 2582 places vs. non-zero offsets**: under RFC 2582 (`rust-lang/rfcs` `text/2582-raw-reference-mir-operator.md`), `eval_place` intentionally skips pointee dereferenceability, alignment, and null checks on raw pointer `*raw_ptr` dereferences (and zero-offset projections `(*null_pair).0` short-circuit `accessSize == 0` in `check_and_deref_ptr`), whereas non-zero offsets trigger `OffsetMode::Inbounds`. A naive `PlaceMention` formalization that performs full-read checks on `*raw_ptr` would reject valid Rust programs such as `let _ = *unaligned_raw_u64;`.
7. **Anneal TCB capture seam and `google/zerocopy` exposure**: at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs:25` captures `Runtime(PostCleanup)` without passing `-Zmir-preserve-ub=yes -Zmir-opt-level=0`, and `trusted/lean/Trusted/MirAst.lean:640,655-663` maps `StatementKind::PlaceMention` to `.unsupported`, even though `vendor/lean-miri/Miri/Interpreter/Step.lean:73-74` already implements `.PlaceMention` via `hooks.evalPlace`. Across `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`rustc 1.98.0-nightly`), enabling `-Zmir-preserve-ub=yes -Zmir-opt-level=0` exposes `1,019` `PlaceMention` statements across `206` of `4,715` default-feature bodies (`17` deref places including `zerocopy.layout-{impl#4}-metadata_for_exact_size` non-zero field `PlaceMention(((*_1).1: layout::SizeInfo))`) and `41` equal-target `SwitchInt`s across `20` bodies (`1,073` `PlaceMention`s across `222` of `5,012` bodies and `44` equal-target `SwitchInt`s with `--all-features`).

All formal claims are kernel-checked in standalone Lean `v4.34.1` (`support/MirPreserveUbAndPlaceMentionSeam.lean`, `1,878` lines, `465` theorems, `0` warnings, `0` forbidden tokens, `0` audit violations, using only `[propext, Quot.sound]`), and all compiler/Miri/native claims are verified by an automated 14-specimen + `zerocopy` probe (`support/probe_mir_preserve_ub_and_postcleanup_seam.py`).

## Applicability

These findings govern:

- **Rust compilers and Miri operational semantics**: `rust-lang/rust` spanning `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, matching the locally verified `rustc 1.98.0-nightly` / `miri 0.1.0` toolchain) through `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), as well as the Anneal vendored pins (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and `8144389c895da997dbdecaa635e41d6a50be6ffd`).
- **Any MIR consumer capturing at `MirPhase::Runtime(RuntimePhase::PostCleanup)`**: specifically `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `theory/Anneal/MirWp.lean`, and `theory/Anneal/PureLift/MirBridge.lean`), and any downstream verification or static analysis consuming post-cleanup MIR bodies.
- **Unsafe and low-level Rust crates utilizing raw pointers, unions, or match control flow**, illustrated empirically across `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`) under default, `--no-default-features`, and `--all-features` builds, and compared with the baseline `1.102.0-nightly` census (`4,663` default-feature bodies).
- **Lean 4 (`v4.34.1`) mechanization scope**: `support/MirPreserveUbAndPlaceMentionSeam.lean` covers single-body operational semantics over local slots, stack/heap allocations, zero/non-zero field and slice projections, `.rawPtr` vs. `.safeRef` dereference rules, `PlaceMention`, `SwitchInt`, `Nop`-filtering, `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`.

## Findings

### Finding 1: Complete `mir_preserve_ub` Audit in `rust-lang/rust` and Options vs. `Session::mir_opt_level` Divergence

Across `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `opts.unstable_opts.mir_preserve_ub` (`compiler/rustc_session/src/options.rs:2726-2732` at `3ef0c22cdb`; lines `2466-2472` at `14210df0e2`) defaults to `false` and acts as a pre-capture UB-preservation toggle at two MIR transformation sites, while also being consumed by option validation tests (`compiler/rustc_interface/src/tests.rs`), a `rustc_codegen_gcc` regression test (`compiler/rustc_codegen_gcc/tests/run/mir_preserve_ub_empty_switch.rs:1-36`), and Miri's driver (`src/tools/miri/src/lib.rs:200-218` at `3ef0c22cdb`; lines `183-200` at `14210df0e2`).

Table 1 summarizes every compiler and Miri site interacting with `-Zmir-preserve-ub`:

| Site (`rust-lang/rust`) | `3ef0c22cdb` (`1.102.0-nightly`) | `14210df0e2` (`1.98.0-nightly`) | Effect & Nuance |
| :--- | :--- | :--- | :--- |
| Option declaration (`compiler/rustc_session/src/options.rs`) | Lines `2726–2732` (`2729–2731`) | Lines `2466–2472` (`2469–2471`) | Defaults `mir_preserve_ub: bool = (false)`. Help string claims `(implies -Zmir-opt-level=0)`. |
| `Session::mir_opt_level` (`compiler/rustc_session/src/session.rs`) | Lines `987–989` | Same (`session.rs`) | **Does not read `mir_preserve_ub`!** Passing `-Zmir-preserve-ub=yes` alone keeps default optimization level unless `-Zmir-opt-level=0` is also passed. |
| Miri CLI arguments (`src/tools/miri/src/lib.rs`) | Lines `200–218` | Lines `183–200` | `MIRI_DEFAULT_ARGS` explicitly passes **both** `"-Zmir-preserve-ub"` and `"-Zmir-opt-level=0"`, plus `"-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-ReferencePropagation,-GVN"`. |
| `Derefer` pass (`compiler/rustc_mir_transform/src/lib.rs`, `deref_separator.rs`) | `lib.rs:648`, `deref_separator.rs:103-106` | `lib.rs:613`, `deref_separator.rs:104-106` | Runs in `run_analysis_cleanup_passes` with `PassPolicy::Required` / `is_required() -> true`. **Not** gated by `mir_preserve_ub`. |
| `EraseDerefTemps` (`compiler/rustc_mir_transform/src/lib.rs`, `erase_deref_temps.rs`) | `lib.rs:673`, `erase_deref_temps.rs:42-45` | Same pipeline | Required runtime cleanup pass rewriting `CopyForDeref` into temporary value copies prior to `RemovePlaceMention`. |
| `RemovePlaceMention` (`compiler/rustc_mir_transform/src/remove_place_mention.rs`, `lib.rs`) | `lib.rs:682-696`, `remove_place_mention.rs:1-25` | `lib.rs:653-673`, `remove_place_mention.rs:1-27` | `PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)` (or `is_enabled` `!sess.opts.unstable_opts.mir_preserve_ub`). Runs inside `run_runtime_cleanup_passes` **before** `Runtime(PostCleanup)`, deleting `PlaceMention(..)` and `Nop`. |
| `SimplifyCfg::PreOptimizations` (`compiler/rustc_mir_transform/src/simplify.rs`) | Lines `130–137, 308–330` | Lines `128–135, 307–329` | Sets `preserve_switch_reads = matches!(body.phase, MirPhase::Built | MirPhase::Analysis(_)) || tcx.sess.opts.unstable_opts.mir_preserve_ub`. Inside `run_runtime_cleanup_passes`, `body.phase` is `MirPhase::Runtime(Initial)`, so equal-target `SwitchInt`s collapse to `Goto` unless `mir_preserve_ub` is `true`. |
| `CheckAlignment` / `CheckNull` (`lib.rs`, `check_pointers.rs`, `visit.rs`) | `lib.rs:709-710`, `check_pointers.rs:160-176`, `visit.rs:455-461` | Same pipeline (`lib.rs`, `check_pointers.rs`) | Run in `run_optimization_passes` **after** `Runtime(PostCleanup)`. `PointerFinder::should_visit_place` ignores `NonMutatingUseContext::PlaceMention`. |

Empirical specimen `c08_mir_opt_level_help_string_mismatch` (`pub fn branch_fold(x: u32) -> u32 { if false { x + 55 } else { x + 1 } }`) confirms the `options.rs` vs. `session.rs` divergence directly:

- With default flags (`default_postcleanup`), `switchInt(move _2) -> [0: bb3, otherwise: bb1];` appears in `Runtime(PostCleanup)` (`switchint_count: 1`) and is folded away in `runtime-optimized.after.mir` (`switchint_count: 0`).
- With `-Zmir-preserve-ub=yes` alone (`preserve_ub_alone`), `runtime-optimized.after.mir` **still** has `switchint_count: 0`: `Session::mir_opt_level()` did not switch to `0`, and `SimplifyConstCondition` still folded the dead branch.
- With `-Zmir-preserve-ub=yes -Zmir-opt-level=0` (`preserve_ub_opt0`), `switchInt(move _2) -> [0: bb3, otherwise: bb1];` remains in `runtime-optimized.after.mir` (`switchint_count: 1`).
- Likewise, in `c06` and `c07`/`c10`, passing `-Zmir-preserve-ub=yes` alone allows post-cleanup optimization passes to rewrite `switchInt(copy _1) -> [0: bb1, otherwise: bb1];` into an `otherwise`-only single-target switch `switchInt(copy _1) -> bb1;` (`c07` `runtime_optimized_after`: `switchInt(copy _1) -> bb1;`), whereas adding `-Zmir-opt-level=0` leaves the full `[0: bb1, otherwise: bb1]` switch intact.

### Finding 2: `Runtime(PostCleanup)` Pass Ordering vs. `Derefer`, `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`

Tracing `compiler/rustc_mir_transform/src/lib.rs` (`641–715` at `3ef0c22cdb`; `607–698` at `14210df0e2`) establishes the exact `MirPhase` pass ordering that isolates `MirPhase::Runtime(RuntimePhase::PostCleanup)` from runtime UB checks while exposing it to pre-capture erasure:

```text
MirPhase::Analysis(Initial)
  └─► run_analysis_cleanup_passes
        ├─ CleanupPostBorrowck, RemoveNoopLandingPads, SimplifyCfg::PostAnalysis
        └─ Derefer (lib.rs:648 / 613; PassPolicy::Required — NOT gated by mir_preserve_ub)
  └─► MirPhase::Analysis(PostCleanup)
        ├─ AddCallGuards, ElaborateDrops, AbortUnwindingCalls, ...
        ├─ EraseDerefTemps (lib.rs:673; required — converts CopyForDeref into Copy)
        └─ StateTransform
  └─► MirPhase::Runtime(RuntimePhase::Initial)
        └─► run_runtime_cleanup_passes (lib.rs:682-696 / 653-673)
              ├─ LowerIntrinsics
              ├─ RemovePlaceMention  <── SKIPPED iff -Zmir-preserve-ub=yes
              └─ SimplifyCfg::PreOptimizations
                   ├─ strip_nops() unconditionally deletes StatementKind::Nop
                   └─ simplify_branches() collapses equal-target SwitchInt -> Goto
                      iff !preserve_switch_reads (i.e., !mir_preserve_ub in Runtime)
  └─► MirPhase::Runtime(RuntimePhase::PostCleanup)  ◄── ANNEAL CAPTURE SEAM
  └─► run_optimization_passes (lib.rs:700-715)
        ├─ CheckAlignment (lib.rs:709)  [disabled by MIRI_DEFAULT_ARGS]
        ├─ CheckNull (lib.rs:710)       [disabled by MIRI_DEFAULT_ARGS]
        ├─ CheckEnums                   [disabled by MIRI_DEFAULT_ARGS]
        └─ GVN / CopyProp / InstSimplify / SimplifyCfg::Final
  └─► MirPhase::Runtime(RuntimePhase::Optimized)
```

Two architectural consequences follow immediately:

1. **Pre-capture erasure under default flags**: Any MIR verifier capturing at `MirPhase::Runtime(RuntimePhase::PostCleanup)` with `-Zmir-preserve-ub` unset (`false`) observes bodies *after* `RemovePlaceMention` has deleted every `StatementKind::PlaceMention` and *after* `SimplifyCfg::PreOptimizations` has converted every equal-target `SwitchInt` to `Goto`. UB present in the source Rust program and caught by Miri (`Runtime(Initial)` equivalent for cleanup behavior) has already disappeared from the captured CFG.
2. **`Derefer` chained-deref splitting (`c05a` vs. `c05b`)**: Because `Derefer` runs *unconditionally* (`PassPolicy::Required`, `deref_separator.rs:103-106`) during analysis cleanup and `EraseDerefTemps` converts its `CopyForDeref` rvalue before `RemovePlaceMention`, a chained dereference `unsafe { let _ = (*(*pp)).1; }` (`pp: *const *const Pair`) splits into:
   - An unconditional temporary read of the inner pointer (`_tmp = copy (*_1)`), which **survives** `RemovePlaceMention` and triggers UB whenever `*pp` is uninitialized (`c05a`: Miri exits `rc = 1` with `"reading memory ... but memory is uninitialized"` in **both** `miri_default` and `miri_no_preserve_ub_opt0`);
   - An outer `PlaceMention(((*_3).1: u64))`, which performs offset-8 `Inbounds` arithmetic on `_tmp` and is **erased** by `RemovePlaceMention` when `-Zmir-preserve-ub=no` (`c05b` with `*pp = null`: Miri exits `rc = 1` with `"in-bounds pointer arithmetic failed: attempting to offset pointer by 8 bytes, but got null pointer"` under `miri_default`, silently flipping to `rc = 0` under `miri_no_preserve_ub_opt0`).

The companion corpus report `rustc-mir-phases-reachability-and-postcleanup-lowering` inaccurately described `Derefer` as gated on `!mir_preserve_ub`; `deref_separator.rs:103-106` (`3ef0c22cdb`) and `104-106` (`14210df0e2`), together with identical `Derefer.after` MIR dumps across both `default_postcleanup` and `preserve_ub_opt0` in `probe_results.json`, establish that `Derefer` is unconditional.

### Finding 3: `StatementKind::PlaceMention` Semantics vs. RFC 2582, Zero-Offset Short-Circuiting, and `14210df0e2` -> `3ef0c22cdb` Reference Checks

In `compiler/rustc_const_eval/src/interpret/step.rs:118-123`, evaluating `StatementKind::PlaceMention(place)` invokes:

```rust
PlaceMention(place) => {
    self.eval_place(**place, false)?;
}
```

Understanding why Miri traps on some `PlaceMention`s and permits others requires tracing the exact call chain across `place.rs`, `projection.rs`, `intrinsics.rs`, and `memory.rs`:

1. **Raw pointer `*raw_ptr` without field/index offset (`c03`)**: RFC 2582 (`rust-lang/rfcs` `text/2582-raw-reference-mir-operator.md`) guarantees that projecting `*raw_ptr` (e.g., to form `&raw const *raw_ptr`, or mentioning `unsafe { let _ = *raw_ptr; }`) creates an `MPlaceTy` in memory without asserting that `raw_ptr` is aligned, non-null, or dereferenceable and without reading pointee bytes. Specimen `c03_rfc2582_raw_u64_unaligned_place_mention` evaluates `unsafe { let _ = *p; }` where `p: *const u64` is 1-byte aligned (`buf.as_ptr().add(1).cast::<u64>()`); MIR confirms `PlaceMention((*_1));` executes, and Miri exits `rc = 0` cleanly. Conversely, a naive semantics equating `PlaceMention(pl)` with a full memory load or `checkRefDeref` alignment check falsely rejects RFC 2582 programs (mechanized in Lean Theorem `ce3_naive_full_read_semantics_for_place_mention_falsely_rejects_rfc2582_raw_deref`).
2. **Zero-offset vs. non-zero-offset field projection (`c02a` vs. `c01` & `c04`)**: Every subsequent field projection `.f` or array/slice indexing `[i]` calls `InterpCx::project` (`compiler/rustc_const_eval/src/interpret/projection.rs:55-451`) using `OffsetMode::Inbounds`, which routes through `ptr_offset_inbounds` (`intrinsics.rs:1026-1042`) into `check_and_deref_ptr` (`memory.rs:480-565`). Crucially:
   - At byte offset `0` (`c02a_null_pair_field0_place_mention`: `unsafe { let _ = (*null_pair).0; }`), `check_and_deref_ptr` receives `size = 0` and short-circuits (`if size == 0 { return interp_ok(None); }`), returning `rc = 0` in Miri even for `null` despite emitting `PlaceMention(((*_1).0: u64));` in MIR!
   - At byte offset `8` (`c01_null_pair_field1_place_mention`: `unsafe { let _ = (*null_pair).1; }`), `check_and_deref_ptr` checks non-zero `size = 8` against the base pointer, immediately failing with Miri UB (`"in-bounds pointer arithmetic failed: attempting to offset pointer by 8 bytes, but got null pointer"`, `rc = 1`), or for a 1-byte allocation (`c04`: `let small = 7u8; unsafe { let _ = (*(&small as *const u8).cast::<Pair>()).1; }`), failing with `"attempting to offset pointer by 8 bytes, but got alloc153 which is only 1 byte from the end of the allocation"` (`rc = 1`). Under `-Zmir-preserve-ub=no -Zmir-opt-level=0`, `RemovePlaceMention` erases both `PlaceMention(((*_1).1: u64))` statements, turning both into silent `rc = 0` exits!
3. **AST lowering contrast (`c02a` vs. `c02b`)**: Small syntactic changes alter whether `rustc` lowers a discarded expression to a pure `PlaceMention` vs. a memory copy:
   - `unsafe { let _ = (*p).0; }` (`c02a`) lowers directly to `PlaceMention(((*_1).0: u64));` (`rc = 0`).
   - Block-value expression `let _ = unsafe { (*p).0 };` (`c02b`) forces a real load `_2 = copy ((*_1).0)` into a block result temporary followed by `PlaceMention(_2);`. Thus `c02b` performs an 8-byte memory access on `null` and triggers Miri UB (`"memory access failed: attempting to access 8 bytes, but got null pointer"`, `rc = 1`) in **both** `miri_default` and `miri_no_preserve_ub_opt0`.
4. **Upstream evolution of `deref_pointer` on references between `14210df0e2` and `3ef0c22cdb` (`c11a` vs. `c11b`)**: In `3ef0c22cdb`, `compiler/rustc_const_eval/src/interpret/place.rs:468-538` takes `skip_validity_for_simple_deref: bool` (`step.rs:120-121` passes `false`) and explicitly validates non-null, dereferenceability, and alignment for `ref` and `Box` dereferences inside `deref_pointer` while skipping those checks for raw pointers (except unsized `ty::Dynamic` vtable checks). Under the earlier `14210df0e2` (`1.98.0-nightly`) toolchain, specimen `c11a_dangling_safe_ref_place_mention` (`let r = &*raw; drop(Box::from_raw(raw)); let _ = *r;`) emits `PlaceMention((*_3));` in MIR and exits `rc = 0` under Miri even in default mode (confirming that `14210df0e2` `deref_pointer` only read the pointer scalar and skipped pointee allocation liveness for `PlaceMention((*_r))`), whereas adding non-zero field offset `8` (`c11b`: `let _ = (*r).1;`) immediately triggers `"in-bounds pointer arithmetic failed: alloc238 has been freed, so this pointer is dangling"` (`rc = 1`) under `miri_default` and silently flips to `rc = 0` under `-Zmir-preserve-ub=no -Zmir-opt-level=0`.

### Finding 4: Equal-Target `SwitchInt` Erasure by `SimplifyCfg::PreOptimizations` (`simplify.rs`)

Even when a function contains **zero** `PlaceMention` statements, default `Runtime(PostCleanup)` lowers `SwitchInt` unsafely under `SimplifyCfg::PreOptimizations` (`compiler/rustc_mir_transform/src/simplify.rs:130-137, 308-330` at `3ef0c22cdb`; lines `128-135, 307-329` at `14210df0e2`):

```rust
// simplify.rs:130-137 (conceptually reproduced from primary audit)
let preserve_switch_reads = matches!(body.phase, MirPhase::Built | MirPhase::Analysis(_))
    || tcx.sess.opts.unstable_opts.mir_preserve_ub;
```

In `simplify_branches` (`simplify.rs:308-330`), when `!preserve_switch_reads` and every branch target of a `TerminatorKind::SwitchInt` equals the `otherwise` block, `SimplifyCfg::PreOptimizations` replaces `SwitchInt` with `TerminatorKind::Goto { target: otherwise }`. Empirical specimens delineate the exact boundary:

- **`c07_custom_mir_pure_equal_target_switchint_zero_pm` (`u8`) and `c10_uninit_bool_switchint_erasure` (`bool`)**: Using `#![feature(custom_mir, core_intrinsics)]` at `#[custom_mir(dialect = "analysis", phase = "post-cleanup")]`, `bb0` allocates an uninitialized local (`StorageLive(x)`) and executes `match x { 0 => bb1, _ => bb1 }` (`0` `PlaceMention` statements). In `default_postcleanup`, `switchInt(copy _1) -> [0: bb1, otherwise: bb1];` disappears during `SimplifyCfg::PreOptimizations` (`switchint_count: 1 -> 0`). Miri flips from `rc = 1` (`"using uninitialized data, but this operation requires initialized memory"`) under `miri_default` to `rc = 0` under `miri_no_preserve_ub_opt0`.
- **`c06_equal_target_switchint_uninit_u8_loop`**: In ordinary unsafe Rust (no `custom_mir`), `loop { ... match u.byte { 0 => continue, _ => continue } }` (`#[repr(C)] union UninitU8 { byte: u8, empty: () }`) emits `PlaceMention((_1.0: u8));` alongside `switchInt(copy (_1.0: u8)) -> [0: bb1, otherwise: bb1];`. Both vanish before `Runtime(PostCleanup)`, flipping Miri `rc = 1 -> 0`.
- **`c09_empty_arms_not_equal_target_switchint` (contrast)**: Writing `let _ = match unsafe { *p } { 0 => (), _ => () };` emits two *distinct* empty basic blocks (`[0: bb4, otherwise: bb3]`) prior to `SimplifyCfg::PreOptimizations`. Because `bb4 != bb3`, `all_targets_equal` is `false`, so `switchInt(copy _5) -> [0: bb4, otherwise: bb3];` survives `SimplifyCfg::PreOptimizations` (`equal_target_switchint_count: 0`, `switchint_count: 1`) and traps in Miri (`rc = 1`) in both `miri_default` and `miri_no_preserve_ub_opt0`.

### Finding 5: The `-Zub-checks=yes` Blind Spot (`check_pointers.rs`, `visit.rs`)

Because `CheckAlignment` (`lib.rs:709`) and `CheckNull` (`lib.rs:710`) execute during `run_optimization_passes` *after* `MirPhase::Runtime(RuntimePhase::PostCleanup)` and both rely on `check_pointers.rs`, one might hope `-Zub-checks=yes` paired with `-Zmir-preserve-ub=yes -Zmir-opt-level=0` would insert native runtime pointer assertions for preserved `PlaceMention` statements. However, `PointerFinder::should_visit_place` (`compiler/rustc_mir_transform/src/check_pointers.rs:160-176`) dispatches on `PlaceContext` (`compiler/rustc_middle/src/mir/visit.rs:455-461, 1321-1326`) and explicitly skips `NonMutatingUseContext::PlaceMention`.

Empirical probe `c01.native_ub_checks` confirms this in native x86_64 execution on `rustc 1.98.0-nightly`:

- Under `-Zub-checks=yes` (`ub_checks_default`): `CheckNull.after` and `CheckAlignment.after` contain `0` `PlaceMention`s and `ubcheck_lines: []`; native execution exits `rc = 0`.
- Under `-Zub-checks=yes -Zmir-preserve-ub=yes -Zmir-opt-level=0` (`ub_checks_preserve_ub_opt0`): `CheckNull.after` and `CheckAlignment.after` contain `PlaceMention(((*_1).1: u64));` (`placemention_count: 1`), **yet `ubcheck_lines: []`**, and native execution still exits `rc = 0` without aborting! (Under Miri, `-CheckAlignment,-CheckNull,-CheckEnums` are disabled anyway, so Miri catches `(*p).1` purely via `eval_place` -> `project` -> `check_and_deref_ptr`!)

### Finding 6: Anneal TCB Capture Seam Completeness and Empirical `google/zerocopy` Census

At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- **Compiler capture configuration (`trusted/rustc-capture/src/driver.rs:25`)**: The capture driver targets the `1.98.0-nightly` toolchain (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and serializes `MirPhase::Runtime(RuntimePhase::PostCleanup)` bodies without setting `-Zmir-preserve-ub=yes -Zmir-opt-level=0`. Consequently, all `PlaceMention` UB (such as `(*null_pair).1` field offsets) and all equal-target `SwitchInt` discriminant UB are erased *inside `rustc`* before Anneal even constructs `Trusted.MirAst.Body`.
- **Lean AST and correspondence seam (`trusted/lean/Trusted/MirAst.lean:53,640,655-663`, `trusted/correspondence/Trusted/Correspondence.lean:1317,2229`, `vendor/lean-miri/Miri/Interpreter/Step.lean:73-74`)**: Currently, `Trusted/MirAst.lean:640,655-663` translates `StatementKind::PlaceMention` to `.unsupported`, and `Correspondence.lean:2229` sets `refStepHooksFor.evalPlace` to return `.error (.unsupported "SetDiscriminant")` even though `vendor/lean-miri/Miri/Interpreter/Step.lean:73-74` (from upstream pin `8144389c`) already lowers `.PlaceMention place` to `hooks.evalPlace choice place false state`. Enabling `-Zmir-preserve-ub=yes` in `driver.rs` therefore requires adding one constructor `StatementKind.placeMention` (wired across `MirAst.lean`, `MirSemantics.lean`, `Correspondence.lean:1317,2229`, `theory/Anneal/MirWp.lean:2390`, and `theory/Anneal/PureLift/MirBridge.lean:1948,2992`) that evaluates `Place` via `evalPlace` (honoring RFC 2582 on simple raw derefs and `OffsetMode::Inbounds` on field/index projections without performing a pointee read).

Running `support/probe_mir_preserve_ub_and_postcleanup_seam.py` live across the full `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`) library on `rustc 1.98.0-nightly` quantifies exact `Runtime(PostCleanup)` surface growth (`SimplifyCfg-pre-optimizations.after.mir`):

| Feature Configuration / Toolchain | PostCleanup Bodies | `PlaceMention` (Default) | `PlaceMention` (`-Zmir-preserve-ub=yes -Zmir-opt-level=0`) | Deref `PlaceMention`s | Field/Cast / Plain-Local `PlaceMention`s | `SwitchInt` Total (`def` -> `pres`) | Equal-Target `SwitchInt`s (`pres`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `zerocopy` default features (`1.98.0-nightly`) | `4,715` | `0` | `1,019` across `206` bodies | `17` (`1` with field projection) | `60` / `942` | `1,137 -> 1,178` | `41` across `20` bodies |
| `zerocopy --no-default-features` (`1.98.0-nightly`) | `4,715` | `0` | `1,019` across `206` bodies | `17` (`1` with field projection) | `60` / `942` | `1,137 -> 1,178` | `41` across `20` bodies |
| `zerocopy --all-features` (`1.98.0-nightly`) | `5,012` | `0` | `1,073` across `222` bodies | `17` (`1` with field projection) | `60` / `996` | `1,196 -> 1,240` | `44` across `21` bodies |
| Prior baseline (`1.102.0-nightly`, `3ef0c22cd`, default) | `4,663` | `0` | `986` across `194` bodies | `16` | — | `1,100` | present (`0` otherwise-only) |

Concrete inspection of `google/zerocopy@907b9175fe` `SimplifyCfg-pre-optimizations.after.mir` under `-Zmir-preserve-ub=yes -Zmir-opt-level=0` confirms real instances of every modeled construct:

- **Non-zero field dereference `PlaceMention`**: `zerocopy.layout-{impl#4}-metadata_for_exact_size.3-1-002` emits `PlaceMention(((*_1).1: layout::SizeInfo));` (the `1` deref-with-field `PlaceMention` observed across all three feature sets), alongside `16` `PlaceMention((*_1));` statements in `byteorder`, `pointer::invariant`, `layout::try_to_nonzero_elem_size`, and `wrappers::get`.
- **Dense plain-local `PlaceMention`s**: `zerocopy.impls-tuples-_-{impl#1427}-is_safe` (through `{impl#626}`) emits up to `52` `PlaceMention`s per body; `942` of `1,019` (`92.4%` default-features) are pure frame-local `PlaceMention`s that satisfy the static `allPlaceMentionsLocalOnly` predicate in our mechanization.
- **Equal-target `SwitchInt`s**: `zerocopy.TryFromBytes-try_read_from_prefix` (`switchInt(move _29) -> [0: bb16, otherwise: bb16];`), `TryFromBytes-try_read_from_suffix`, `FromBytes-read_from_io` (`switchInt(move _26) -> [1: bb17, otherwise: bb17];`, enabled with `--all-features`), and `error::From` (`switchInt(move _13) -> [0: bb7, 1: bb7, otherwise: bb7];`) exhibit genuine equal-target `SwitchInt` terminators (`41` in default features, `44` in `--all-features`, `0` otherwise-only).

### Finding 7: Kernel-Checked Lean 4 Mechanization (`support/MirPreserveUbAndPlaceMentionSeam.lean`)

`support/MirPreserveUbAndPlaceMentionSeam.lean` (`1,878` lines, `77,105` bytes, SHA-256 `e42331e2a8b9bd0940baf9733aa7313e8a12e1c960a6644b96b8931166720488`) formalizes the operational semantics of `evalPlaceMPlace`, `evalPlaceNaiveFullRead`, small-step MIR execution (`runSteps`, `evalBody`), `passRemovePlaceMention`, `passSimplifyCfgPreOpt`, `toRuntimePostCleanup`, and `lowerChainedPlaceMentionDerefer` in standalone Lean `v4.34.1` with zero external dependencies and zero classical/unsafe axioms (`465` kernel theorems, `357` axiom-free; remaining theorems use only `[propext, Quot.sound]`, verified by `support/MirPreserveUbAudit.lean` and `support/check_lean.py`).

Table 2 indexes the core kernel-checked theorems and constructive counterexamples:

| Lean Declaration (`MirPreserveUbSeam.*`) | Statement Proven | Axioms Used (`#print axioms`) |
| :--- | :--- | :--- |
| `evalPlaceMPlace_raw_deref_zero_offset_ok` | Evaluating `*raw_ptr` or `(*raw_ptr).0` (`field 0`) on any initialized pointer `p` returns `.ok (.memBase p)` even when `p = .null` or unaligned (RFC 2582 + zero-size `checkAndDerefPtr` short-circuit). | `[propext]` |
| `evalPlaceMPlace_null_nonzero_field_ub` | Evaluating `(*null_ptr).field off` with `(off == 0) = false` immediately faults `.error .nullInboundsOrDeref`. | `[propext]` |
| `evalPlaceMPlace_safeRef_null_ub` | Evaluating `*(.null : &T)` (or field off a `.safeRef`) immediately faults `.error .nullInboundsOrDeref` (`place.rs:468-538`). | `[propext]` |
| `evalBody_runtimePostCleanup_preserveUb_true_exact_noNops` | On every `Nop`-free `Runtime(Initial)` body, `evalBody (toRuntimePostCleanup true body) st fuel = evalBody body st fuel` holds identically. | `[propext]` |
| `evalBody_runtimePostCleanup_preserveUb_true_complete` | For arbitrary `Runtime(Initial)` bodies (including arbitrary `Nop` compression by `strip_nops`), every terminating or UB-faulting execution reproduces identically under `toRuntimePostCleanup true` at adjusted fuel. | `[propext]` |
| `evalPlaceMPlace_ok_of_safeToErasePlaceMention` | Any `(st, pl)` satisfying decidable `safeToErasePlaceMention st pl = true` (local-only place or initialized zero-offset `.rawPtr` `*p` / `(*p).0`) evaluates `evalPlaceMPlace` cleanly without UB. | `[propext]` |
| `evalBody_removePlaceMention_exact_of_localOnly` | When all `PlaceMention`s in `body` satisfy static `allPlaceMentionsLocalOnly minLocals body = true` (`minLocals ≤ st.locals.length`), `RemovePlaceMention` alone (`simplifyEqualBranchTerm true`) is unconditionally exact. | `[propext, Quot.sound]` |
| `evalBody_postCleanup_false_exact_of_traceCertified` | Along any `traceCertifiedSafe` execution (covering local-only places, zero-offset `*raw_ptr`/`(*raw_ptr).0` mentions, and initialized/valid equal-target `SwitchInt` discriminants), full default `toRuntimePostCleanup false` preserves `evalBody` identically. | `[propext, Quot.sound]` |
| `Examples.ce1_null_nonzero_field_place_mention_ub_erased_in_default_postcleanup` | Constructive counterexample: `let _ = (*null_pair).1` returns `.ub .nullInboundsOrDeref` under `toRuntimePostCleanup true`, and `.returned (.intVal 42)` under `toRuntimePostCleanup false`. | `[propext]` |
| `Examples.ce1b_null_zero_offset_field0_defined_both_modes` | Offset-0 `let _ = (*null_pair).0` evaluates to `.returned (.intVal 42)` in both modes (`checkAndDerefPtr` `accessSize == 0` short-circuit). | `[propext]` |
| `Examples.ce2_uninit_local_equal_target_switchint_ub_erased_in_default_postcleanup` | Constructive counterexample with zero `PlaceMention`s: equal-target `switchInt` over an uninitialized local returns `.ub .uninitRead` under `true` vs. `.returned (.intVal 42)` under `false`. | `[propext]` |
| `Examples.ce3_naive_full_read_semantics_for_place_mention_falsely_rejects_rfc2582_raw_deref` | Evaluating `PlaceMention((*unaligned_raw_u64))` returns `.returned (.intVal 42)` under `evalPlaceMPlace`, whereas `evalPlaceNaiveFullRead` falsely faults `.error .misalignedRefDeref`. | `[propext]` |
| `Examples.ce4_derefer_chained_deref_inner_uninit_survives_while_outer_field_ub_erased` | Under `lowerChainedPlaceMentionDerefer` (`Derefer` hoisting), inner uninit `*pp` faults `.ub .uninitRead` in both modes, whereas `*pp = null` outer `(*_tmp).1` UB survives only when `mirPreserveUb = true`. | `[propext]` |
| `Examples.runtimePostCleanup_preserveUb_false_unsound` | Witnessed general unsoundness theorem proving `toRuntimePostCleanup false` turns both `.nullInboundsOrDeref` and `.uninitRead` bodies (even with `allPlaceMentionsLocalOnly = true`) into `.returned 42`. | `[propext]` |

## Boundaries

The scope and exact negative/exclusion boundaries of this report are categorized as follows:

- **`unsupported`**:
  - **Interprocedural calls, heap deallocation reborrows/aliasing models (Stacked Borrows / Tree Borrows), dynamically sized trait objects (`ty::Dynamic` vtable validation), and arbitrary bit-level uninitialized sub-bytes**: `support/MirPreserveUbAndPlaceMentionSeam.lean` models single-body operational semantics over concrete local slots (`Val`/`LocalSlot`), bounded allocation entries (`AllocInfo`), zero/non-zero offsets, `.rawPtr` vs. `.safeRef`, `PlaceMention`, and `SwitchInt`. While `1.98.0-nightly` Miri empirically demonstrates `c11a` (`rc = 0` on `let _ = *dangling_safe_ref`), Stacked/Tree Borrows retag rules and unsized `ty::Dynamic` vtable dereferences inside `eval_place` (`place.rs:468-538`) are outside the Lean model's inductive types.
  - **Mutating `joshlf/anneal` or downstream LLVM codegen (`rustc_codegen_llvm` / `rustc_codegen_ssa`)**: Code modifications to `joshlf/anneal` (`trusted/rustc-capture/src/driver.rs`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `Trusted/Correspondence.lean`, `MirWp.lean`, `MirBridge.lean`) are specified and scoped at exact pinned lines rather than implemented upstream.
- **`known not to apply`**:
  - **`-Zmir-preserve-ub=yes` implies `-Zmir-opt-level=0`**: Directly disproved by primary source (`compiler/rustc_session/src/session.rs:987-989` ignores `mir_preserve_ub`) and specimen `c08` (`runtime-optimized.after.mir` folds `if false { x + 55 } else { x + 1 }` to straight-line code under `-Zmir-preserve-ub=yes` alone, keeping `switchInt` only when `-Zmir-opt-level=0` is also passed).
  - **`Derefer` (`deref_separator.rs`) is gated by `!mir_preserve_ub`**: Directly disproved by `deref_separator.rs:103-106` (`PassPolicy::Required` / `is_required() -> true`) and empirical specimen `c05a` (`Derefer.after` identical and Miri `rc = 1` in both modes).
  - **`-Zub-checks=yes` paired with `-Zmir-preserve-ub=yes -Zmir-opt-level=0` inserts runtime checks on `PlaceMention`**: Directly disproved by `check_pointers.rs:160-176` (`visit.rs:455-461`) and `c01.native_ub_checks` (`ubcheck_lines: []` and `exec_rc: 0`).
  - **Block-value discard `let _ = unsafe { (*p).0 };` lowers identically to `unsafe { let _ = (*p).0; }`**: Directly disproved by `c02a` (`PlaceMention(((*_1).0: u64))`, `miri_default rc = 0`) vs. `c02b` (`_2 = copy ((*_1).0); PlaceMention(_2);`, `miri_default rc = 1` memory access UB).
  - **Every `match` on an uninitialized value with identical body expressions lowers to equal-target `SwitchInt`**: Directly disproved by `c09` (`let _ = match unsafe { *p } { 0 => (), _ => () };` produces distinct blocks `bb4 != bb3`, surviving `SimplifyCfg::PreOptimizations` even when `mir_preserve_ub = false`).
- **`not examined`**:
  - **`rustc` `runtime-post-cleanup` MIR captures with alternative codegen backends (`rustc_codegen_gcc` beyond `mir_preserve_ub_empty_switch.rs`, `rustc_codegen_cranelift`)**, non-`lib` targets of `google/zerocopy` (integration test crates / derive macro proc-macro internals beyond `--lib`), and intermediate `rust-lang/rust` nightly commits strictly between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` where `place.rs:468-538` landed.
- **`unknown`**:
  - **Exact fraction of `zerocopy`'s `41` (`default`) / `44` (`--all-features`) equal-target `SwitchInt`s or `17` deref `PlaceMention`s reachable with uninitialized or dangling/out-of-bounds operands along valid/unsafe call paths**: Static `SimplifyCfg-pre-optimizations.after.mir` censuses establish exact syntactic presence (`PlaceMention(((*_1).1: layout::SizeInfo))` in `zerocopy.layout-{impl#4}-metadata_for_exact_size`, `41`/`44` equal-target `SwitchInt`s), but full interprocedural reachability over every `zerocopy` entry point under unsafe caller contracts was not symbolically discharged here.

## Evidence

### Normative Specifications (`normative`)

- **`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2582-raw-reference-mir-operator.md`** (committed `2025-11-29T00:07:16Z`): Defines raw place projection semantics permitting misaligned/dangling `*raw_ptr` without reference-validity assertions while preserving `OffsetMode::Inbounds` GEP semantics on field projections such as `.field`.
- **Lean 4 kernel mechanization `support/MirPreserveUbAndPlaceMentionSeam.lean`** (`support/MirPreserveUbAudit.lean`, `support/check_lean.py`, receipt `support/lean_check_receipt.json`):
  - Compiler version: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` with flags `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.
  - Artifact metrics: `1,878` lines, `77,105` bytes, SHA-256 `e42331e2a8b9bd0940baf9733aa7313e8a12e1c960a6644b96b8931166720488`, `0` errors, `0` warnings, `4,103,752` `.olean` bytes, `6.482s` compile wall time (`590,724` KB peak RSS).
  - Audit summary (`MirPreserveUbAudit.lean`, `3.256s` wall time): `1,028` constants (`465` theorems with `357` axiom-free, `478` definitions, `17` inductive types, `51` constructors, `17` recursors), `0` violations, `0` `_unsafe_rec` helpers, `0` occurrences of all `13` scanned forbidden tokens (`sorry`, `admit`, `omega`, `bv_decide`, `native_decide`, `partial`, `unsafe`, `axiom`, `opaque`, `implemented_by`, `extern`, `Classical`, `_unsafe_rec`), and `#print axioms` strictly within `[propext, Quot.sound]`.

### Primary Source Audit (`source`) and Documentation (`documentation`)

Verified against live GitHub blob hashes in `support/pin_receipt.json` across `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `8144389c895da997dbdecaa635e41d6a50be6ffd`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- **Flag declaration vs. opt-level behavior (`documentation` drift vs. `source`)**: `compiler/rustc_session/src/options.rs:2726-2732` (`2729-2731` in `3ef0c22cdb`; `2466-2472` in `14210df0e2`) vs. `compiler/rustc_session/src/session.rs:987-989` (per-file git blob digests recorded in `support/pin_receipt.json`).
- **Miri default invocation (`source`)**: `src/tools/miri/src/lib.rs:200-218` (`3ef0c22cdb`; `183-200` in `14210df0e2`).
- **MIR cleanup & optimization pipelines (`source`)**:
  - `compiler/rustc_mir_transform/src/lib.rs:641-715` (`3ef0c22cdb`; `607-698` in `14210df0e2`).
  - `compiler/rustc_mir_transform/src/remove_place_mention.rs:1-25` (`3ef0c22cdb`; `1-27` in `14210df0e2`).
  - `compiler/rustc_mir_transform/src/simplify.rs:130-137, 308-330` (`3ef0c22cdb`; `128-135, 307-329` in `14210df0e2`).
  - `compiler/rustc_mir_transform/src/deref_separator.rs:103-106` (`3ef0c22cdb`; `104-106` in `14210df0e2`) and `erase_deref_temps.rs:42-45` (`3ef0c22cdb`).
  - `compiler/rustc_mir_transform/src/check_pointers.rs:1-195` (`160-176`), `check_alignment.rs`, `check_null.rs`, `check_enums.rs`, and `compiler/rustc_middle/src/mir/visit.rs:455-461, 1321-1326`.
- **Interpreter semantics (`source`)**: `compiler/rustc_const_eval/src/interpret/step.rs:118-123`, `place.rs:468-538` (`3ef0c22cdb` vs. `14210df0e2`), `projection.rs:55-451`, `intrinsics.rs:1026-1042`, and `memory.rs:480-565`.
- **Anneal TCB capture & Lean seam (`source`)**: `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` `trusted/rustc-capture/src/driver.rs:25`, `trusted/lean/Trusted/MirAst.lean:53,640,655-663`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean:1317,2229`, `vendor/lean-miri/Miri/Interpreter/Step.lean:73-74`, `theory/Anneal/MirWp.lean:2390`, and `theory/Anneal/PureLift/MirBridge.lean:1948,2992`.

### Empirical Execution and Census (`execution` & `derived`)

Executed live via `support/probe_mir_preserve_ub_and_postcleanup_seam.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)` and recorded in `support/probe_results.json` (`mir-preserve-ub-probe/1`), supplemented by historical baseline counts on `1.102.0-nightly (3ef0c22cd 2026-11-11)`:

| Specimen ID | Construct Tested | MIR (`default_postcleanup` -> `preserve_ub_opt0`) | Miri Default (`-Zmir-preserve-ub=yes -Zmir-opt-level=0`) | Miri `MIRIFLAGS="-Zmir-preserve-ub=no -Zmir-opt-level=0"` | Native `-Zub-checks=yes` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `c01_null_pair_field1_place_mention` | `unsafe { let _ = (*null_pair).1; }` | `0 -> 1` `PlaceMention(((*_1).1: u64))` | `rc = 1` (in-bounds offset `8` on null) | `rc = 0` (**erased**) | `rc = 0` in both modes (`0` checks) |
| `c02a_null_pair_field0_place_mention` | `unsafe { let _ = (*null_pair).0; }` | `0 -> 1` `PlaceMention(((*_1).0: u64))` | `rc = 0` (offset `0` short-circuit) | `rc = 0` | — |
| `c02b_block_value_field0_read_control` | `let _ = unsafe { (*null_pair).0 };` | `0 -> 1` `PlaceMention(_2)` after copy load | `rc = 1` (`memory access failed`) | `rc = 1` (copy load remains) | — |
| `c03_rfc2582_raw_u64_unaligned_place_mention` | `unsafe { let _ = *unaligned_raw_u64; }` | `0 -> 1` `PlaceMention((*_1))` | `rc = 0` (RFC 2582 valid) | `rc = 0` | — |
| `c04_oob_small_alloc_field1_place_mention` | `unsafe { let _ = (*one_byte_ptr).1; }` | `0 -> 1` `PlaceMention(((*_1).1: u64))` | `rc = 1` (in-bounds offset `8` > 1B alloc) | `rc = 0` (**erased**) | — |
| `c05a_derefer_chained_deref_inner_uninit` | `unsafe { let _ = (*(*uninit_pp)).1; }` | `_tmp = copy (*_1)` hoisted; `0 -> 1` `PlaceMention(((*_3).1))` | `rc = 1` (`memory is uninitialized`) | `rc = 1` (`Derefer` load survives) | — |
| `c05b_derefer_chained_deref_inner_null` | `unsafe { let _ = (*(*null_holder_pp)).1; }` | `_tmp = copy (*_1)` hoisted; `0 -> 1` `PlaceMention(((*_3).1))` | `rc = 1` (outer `.1` offset `8` on null) | `rc = 0` (**outer UB erased**) | — |
| `c06_equal_target_switchint_uninit_u8_loop` | `loop { match uninit_union.byte { 0 => continue, _ => continue } }` | `PlaceMention` `0 -> 1`; `switchInt` `1 -> 2` (`eq: 0 -> 1`) | `rc = 1` (`memory is uninitialized`) | `rc = 0` (**both erased**) | — |
| `c07_custom_mir_pure_equal_target_switchint_zero_pm` | `#[custom_mir]` `match uninit_u8 { 0 => bb1, _ => bb1 }` (`0` `PlaceMention`) | `PlaceMention` `0 -> 0`; `switchInt` `0 -> 1` (`eq: 0 -> 1`) | `rc = 1` (`using uninitialized data`) | `rc = 0` (**erased**) | — |
| `c08_mir_opt_level_help_string_mismatch` | `if false { x + 55 } else { x + 1 }` | `runtime-optimized`: `0` switch default, `0` with `-Zmir-preserve-ub=yes` alone, **`1` only with `-Zmir-opt-level=0`** | skipped | skipped | — |
| `c09_empty_arms_not_equal_target_switchint` | `let _ = match unsafe { *uninit_u8_ptr } { 0 => (), _ => () };` | `switchInt` `1 -> 1` (`bb4 != bb3`, `eq: 0`) | `rc = 1` (`memory is uninitialized`) | `rc = 1` (`bb4 != bb3` survives) | — |
| `c10_uninit_bool_switchint_erasure` | `#[custom_mir]` `match uninit_bool { false => bb1, _ => bb1 }` (`0` `PlaceMention`) | `PlaceMention` `0 -> 0`; `switchInt` `0 -> 1` (`eq: 0 -> 1`) | `rc = 1` (`using uninitialized data`) | `rc = 0` (**erased**) | — |
| `c11a_dangling_safe_ref_place_mention` | `let r: &u64 = ...; drop(Box); let _ = *r;` | `0 -> 1` `PlaceMention((*_3))` | `rc = 0` (also `rc = 0` with `-Zmiri-disable-stacked-borrows`) on `1.98.0-nightly` | `rc = 0` (pre-`3ef0c22cdb` `eval_place` reference gap) | — |
| `c11b_dangling_safe_ref_field1_place_mention` | `let r: &Pair = ...; drop(Box); let _ = (*r).1;` | `0 -> 1` `PlaceMention(((*_4).1: u64))` | `rc = 1` (`alloc238 has been freed`) | `rc = 0` (**erased**) | — |

## Revalidation

Every claim in this report is deterministically re-executable from the package `support/` directory against pinned toolchains:

1. **Lean 4 kernel & axiom re-verification (`v4.34.1`, exit code `0`)**:

   ```bash
   python3 support/check_lean.py --lean lean
   ```

   Compiles `support/MirPreserveUbAndPlaceMentionSeam.lean` with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` inside an isolated temporary directory, scans all lines for forbidden tokens, executes `support/MirPreserveUbAudit.lean` (`#audit_mir_preserve_ub` and 14 `#print axioms` checks), and regenerates `support/lean_check_receipt.json` asserting `"passed": true` and `"violations": 0`.

2. **Empirical `rustc`, Miri, native `-Zub-checks=yes`, and `google/zerocopy` census (`1.98.0-nightly` or newer)**:

   ```bash
   python3 support/probe_mir_preserve_ub_and_postcleanup_seam.py \
     --zerocopy-dir /path/to/zerocopy/zerocopy \
     --out support/probe_results.json
   ```

   Re-runs all 14 MIR/Miri/native specimens inside a fresh temporary Cargo crate (using distinct `CARGO_TARGET_DIR` paths per `MIRIFLAGS` configuration so Cargo never reuses stale compilation artifacts) and re-measures `SimplifyCfg-pre-optimizations.after.mir` across `default`, `--no-default-features`, and `--all-features` on `google/zerocopy`. (Omit `--zerocopy-dir` to run only the 14 standalone compiler/Miri specimens.)

3. **Live upstream commit and blob hash re-verification (`support/pin_receipt.json`)**:

   ```bash
   gh api repos/rust-lang/rust/commits/3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 --jq .sha
   gh api repos/rust-lang/rust/commits/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 --jq .sha
   gh api repos/rust-lang/rfcs/commits/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 --jq .sha
   gh api repos/joshlf/anneal/commits/c131b320eeeb26ef692e5afd5ec8db49ee518613 --jq .sha
   gh api repos/google/zerocopy/commits/907b9175fee081872ec883ca4709e6ad922f8ed0 --jq .sha
   gh api repos/leanprover/lean4/commits/5045d0056413266e57c625dcd7c365b10e377c52 --jq .sha
   ```

4. **Corpus schema and validator check (from corpus root)**:

   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```
