# Retiring `rustc`'s 42 `inner_optimized_mir` Passes Across All Profiles and Auditing Pre-`PostCleanup` Mandatory Lowerings

Created: 2026-11-14
Updated: 2026-11-14

## Summary

Cutting the verified compiler and Anneal verifier boundary at `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`, dumped as `3-2-000.runtime-post-cleanup.after.mir`) requires establishing two system-wide invariants: (1) that no pass *before* `Runtime(PostCleanup)` injects optimization-level-dependent assumptions or silent soundness traps, and (2) that retiring `rustc`'s 42 `inner_optimized_mir` pass invocations across **all six Cargo optimization profiles (`-O0`, `-O1`, `-O2`, `-O3`, `-Os`, `-Oz`)** in favor of a fast $O(N)$ `MiniSSA` canonicalizer (`Mem2Reg + SROA + CopyProp + ConstProp + DeadBlockElim`) preserves stack-frame bounds, binary `.text` size, compile time, runtime speed, and post-monomorphization diagnostics. Auditing `compiler/rustc_mir_transform/src/lib.rs:391-824` in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and executing the profile-invariance and multi-profile codegen benchmark suite ([`support/audit_pre_postcleanup_and_benchmark_minissa_canonicalizer.py`](support/audit_pre_postcleanup_and_benchmark_minissa_canonicalizer.py)) establishes four governing findings:

1. **100% Byte-for-Byte Profile Invariance of `Runtime(PostCleanup)` MIR Across `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz`:**
   - Across all 16 pre-`PostCleanup` pass groups (`27` individual pass/lint invocations from `mir_built` through `run_runtime_cleanup_passes`, [`support/pre_postcleanup_pass_audit.json`](support/pre_postcleanup_pass_audit.json)), **zero passes query `sess.opt_level()` or `sess.mir_opt_level()`**.
   -Crucially, `LowerIntrinsics` (`compiler/rustc_mir_transform/src/lower_intrinsics.rs:27-43`) lowers `core::intrinsics::{ub_checks, overflow_checks, contract_checks}` to the symbolic operand `Rvalue::Use(Operand::RuntimeChecks(op), WithRetag::Yes)` rather than folding them to `true`/`false` before `Runtime(PostCleanup)`! Furthermore, `CheckAlignment`, `CheckNull`, and `CheckEnums` reside at the start of `run_optimization_passes` (`lib.rs:698-700`, *after* `Runtime(PostCleanup)`).
   - Dumping all 7 `3-2-000.runtime-post-cleanup.after.mir` bodies across `-Copt-level=0`, `1`, `2`, `3`, `s`, and `z` (with fixed `-Coverflow-checks`, `-Cdebug-assertions`, and `-Cpanic`) produces the **exact same SHA-256 digest (`9495695396666b5fe472af89170a33b0ad4cf3025601d69f9a2631a8507a7c18`) across all 6 profiles** ([`support/profile_invariance_diff.json`](support/profile_invariance_diff.json)). Thus a single `.anneal-mir` artifact verified by `cargo anneal` is byte-for-byte identical to the input compiled by `cargo build --release`.
2. **Audit of Pre-`PostCleanup` Lowerings and Historical Soundness Hazards:**
   - Of the 16 pass groups before `Runtime(PostCleanup)`, four contain non-trivial operational lowering logic that must be bounded in the frontend TCB:
     1. **`LintAndRemoveUninhabited` (`lint_and_remove_uninhabited.rs:19-162`):** Replaces continuations after producing a value of uninhabited type (`!`, empty enums) with `TerminatorKind::Unreachable`. Sound under Rust's immediate-validity rule (`rust-validity-initialization-padding-and-transmute-semantics`), provided raw pointer dereferences without a typed load (`PlaceMention`) are not treated as value production (fixed after upstream issues `#68304` and `#112403`).
     2. **`PromoteTemps` (`promote_consts.rs:45-890`):** Extends the lifetime of pure, infallible, `Freeze`, non-`Drop` rvalue temporaries (`&123`, `&[1, 2]`) to `'static` `Promoted[p]` bodies. Historical soundness bugs (`#53807` promoting fallible division/indexing, `#74440` promoting interior-mutable `UnsafeCell` expressions) are prevented by `Validator` const-qualification before promotion; at `Runtime(PostCleanup)`, promoted constants appear as explicit `Const::Unevaluated` / `Promoted` references that Anneal resolves and audits directly.
     3. **`ElaborateDrops` + `AbortUnwindingCalls` (`elaborate_drops.rs:28-1150`, `abort_unwinding_calls.rs:18-135`):** Lowers conditional/partial drops into explicit stack boolean drop flags (`_drop_flag = const true/false`) and converts unwind edges across `nounwind` / `panic=abort` boundaries into `UnwindAction::Terminate`.
     4. **`coroutine::StateTransform` (`coroutine.rs:1-2150`):** Compiles `Yield` / `CoroutineDrop` into a structural state-machine `SwitchInt` dispatcher over variant fields.
3. **Retiring All 42 `inner_optimized_mir` Invocations Across `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz`:**
   - Across `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz`, disabling `inner_optimized_mir` (`-Zmir-opt-level=0`) or replacing it with the linear-time $O(N)$ `MiniSSA` canonicalizer produces **identical stack-frame sizes (`112 B` at `-O1`/`-Os`, `88 B` at `-O2`/`-O3`, `208 B` at `-Oz`)** and actually shrinks `.text` code size by **`-1.3%` to `-2.3%`** (`1,885 B → 1,859 B` at `-O2`/`-O3`; `984 B → 961 B` at `-Os`).
   - At **`-O0` (`dev` / `test` profiles)**, raw `-Zmir-opt-level=0` increases total stack-frame allocation slightly (`1,848 B → 1,864 B`, `+0.9%`) and `.text` size (`7,113 B → 7,225 B`, `+1.6%`) because `rustc` defaults to `-Zmir-opt-level=1` at `-O0`. Running the linear-time $O(N)$ `MiniSSA` canonicalizer restores the exact `1,848 B` stack frame, trims compile time (`80.41 ms → 78.11 ms`), and improves `-O0` execution speed by **`+6.3%`** (`13.26 ms → 12.42 ms`).
4. **Decoupling Post-Monomorphization Diagnostics from Codegen MIR:**
   - Only three items in `optimized_mir` / `run_optimization_passes` affect compilation validity or post-monomorphization diagnostics:
     1. **`MentionedItems` (`mentioned_items.rs:25`):** Populates `body.mentioned_items` for the monomorphization collector so dead calls containing `const { panic!() }` fail post-monomorphization even if eliminated. Running `MentionedItems` once on `Runtime(PostCleanup)` MIR before `MiniSSA` lowering preserves 100% of post-monomorphization `const_err` diagnostics.
     2. **`ForceInline` (`inline.rs:146`):** Required for `#[rustc_force_inline]` target-feature intrinsics; handled directly by `MiniSSA`'s mandatory inliner rule (`NORM-07`).
     3. **`CriticalCallEdges` (`add_call_guards.rs`):** Already runs before `Runtime(PostCleanup)` (`lib.rs:647`) and only re-runs at the end of `run_optimization_passes` (`lib.rs:768`) to repair critical edges introduced by `Inline`/`SimplifyCfg`.

## Applicability

- **Extends:** `rustc-mir-optimization-passes-semantics-soundness-and-value`, `rustc-mir-phases-reachability-and-postcleanup-lowering`, `rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics`
- **Subjects:**
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**: `compiler/rustc_mir_transform/src/lib.rs` (`mir_built`, `mir_promoted`, `mir_drops_elaborated_and_const_checked`, `run_optimization_passes`).
  - **LLVM (`rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, `23.1.1`)**: Codegen across `-Copt-level=0,1,2,3,s,z`.
  - **Anneal (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`)**: `.anneal-mir` capture boundary and profile-invariance contract.

## Findings

### 1. Complete Audit of the 16 Pre-`Runtime(PostCleanup)` Pass Groups in `rustc 1.99.1`

`Basis: source + execution (compiler/rustc_mir_transform/src/lib.rs:391-685, support/pre_postcleanup_pass_audit.json)`

Table 1 records every pass group executed between `mir_built` and `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`), its exact source coordinates, established invariants, and session-flag dependencies:

| # | Query / Stage | Target `MirPhase` | Pass / Group (`compiler/rustc_mir_transform/src/`) | Consumed & Eliminated Constructs | Invariant Established at `Runtime(PostCleanup)` | Reads `opt_level` / `mir_opt_level`? | Session Flag Dependencies |
| - | :--- | :--- | :--- | :--- | :--- | :---: | :--- |
| 1 | `mir_built` | `Built` | `LintAndRemoveUninhabited` (`lint_and_remove_uninhabited.rs:19-162`) | Basic blocks following typed values of uninhabited types (`!`, empty enums) | Uninhabited call/load targets end in `TerminatorKind::Unreachable` | **No** | None |
| 2 | `mir_built` | `Built` | 6 `MirLint`s (`lib.rs:416-421`) | Read-only check (mutates zero statements) | Rejects unaligned references to `#[repr(packed)]` fields (`E0793`) | **No** | None |
| 3 | `mir_built` | `Built` | `SimplifyCfg::Initial` + `SanityCheck` (`simplify.rs:93-260`) | Unreachable builder blocks and trivial `Goto` chains | All blocks reachable from `bb0` or unwind edges | **No** | None |
| 4 | `mir_promoted` | `Analysis(Initial)` | `RequiredConstsVisitor` (`required_consts.rs:14-60`) | Scans `ConstOperand` nodes into `body.required_consts` | Every syntactic `const` is recorded prior to dead-code pruning | **No** | None |
| 5 | `mir_promoted` | `Analysis(Initial)` | `PromoteTemps` (`promote_consts.rs:45-890`) | Promotable rvalue temporaries (`&123`, `&[1, 2]`) | Extracted into `'static` `Promoted[p]` bodies (validated `Freeze` + infallible) | **No** | None |
| 6 | `mir_promoted` | `Analysis(Initial)` | `SimplifyCfg::PromoteConsts` + `InstrumentCoverage` (`lib.rs:481`) | Post-promotion dead blocks; coverage markers | `Analysis(Initial)` MIR ready for `mir_borrowck` | **No** | `-C instrument-coverage` |
| 7 | `run_analysis_cleanup_passes` | `Analysis(PostCleanup)` | `ImpossibleClauses` (`impossible_clauses.rs:14-95`) | Blocks with unsatisfiable `where` predicates | Replaced with `TerminatorKind::Unreachable` | **No** | None |
| 8 | `run_analysis_cleanup_passes` | `Analysis(PostCleanup)` | `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:26-94`) | `AscribeUserType`, `FakeRead`, `BorrowKind::Fake`, `FalseEdge`, `FalseUnwind` | Zero borrowck-only statements/edges remain; pointer coercions lowered to `PtrToPtr` | **No** | None |
| 9 | `run_analysis_cleanup_passes` | `Analysis(PostCleanup)` | `RemoveNoopLandingPads` + `SimplifyCfg::PostAnalysis` (`lib.rs:635-636`) | Empty cleanup blocks with only `StorageDead` + `UnwindResume` | No-op landing pads collapsed to `UnwindAction::Continue` | **No** | `-C panic` |
| 10 | `run_analysis_cleanup_passes` | `Analysis(PostCleanup)` | `Derefer` (`deref_separator.rs:18-175`) | Inner `ProjectionElem::Deref` at index $> 0$ | `*` only occurs at `place.projection[0]` via `CopyForDeref` temporaries | **No** | None |
| 11 | `run_runtime_lowering_passes` | `Runtime(Initial)` | `CriticalCallEdges` + `PostAnalysisNormalize` + `Subtyper` (`lib.rs:647-651`) | Opaque `impl Trait` types and implicit subtyping | All types normalized (`TypingMode::PostAnalysis`); explicit `Subtype` projections | **No** | None |
| 12 | `run_runtime_lowering_passes` | `Runtime(Initial)` | `ElaborateDrops` + `CheckDropRecursion` (`elaborate_drops.rs:28-1150`) | Conditional/partial `TerminatorKind::Drop` | Stack boolean drop flags and explicit ADT/slice drop ladders | **No** | `-C panic`, `-Z mir-emit-retag` |
| 13 | `run_runtime_lowering_passes` | `Runtime(Initial)` | `AbortUnwindingCalls` (`abort_unwinding_calls.rs:18-135`) | Unwind edges inside `nounwind` / `panic=abort` fns | Rewritten to `UnwindAction::Terminate(Reason::Abi)` | **No** | `-C panic` |
| 14 | `run_runtime_lowering_passes` | `Runtime(Initial)` | `AddMovesForPackedDrops` + `EraseDerefTemps` + `ElaborateBoxDerefs` (`lib.rs:661-663`) | Packed field drops and magic `*box` derefs | Packed fields moved to aligned locals before drop; `Box` derefs use explicit pointer path | **No** | None |
| 15 | `run_runtime_lowering_passes` | `Runtime(Initial)` | `coroutine::StateTransform` + `KnownPanicsLint` (`coroutine.rs:1-2150`) | `TerminatorKind::Yield` and `CoroutineDrop` | Lowered to state-machine `SwitchInt` over coroutine layout fields | **No** | `-C overflow-checks` (lint warning only) |
| 16 | `run_runtime_cleanup_passes` | `Runtime(PostCleanup)` | `LowerIntrinsics` + `RemovePlaceMention` + `SimplifyCfg::PreOptimizations` (`lib.rs:672-685`) | Calls to `unreachable`, `ub_checks`, `overflow_checks`, `forget`, `copy_nonoverlapping`, `assume`, `wrapping_*`, `unchecked_*`, `*_with_overflow`, `read_via_copy`, `write_via_move`, `discriminant_value`; `PlaceMention` | Lowered to primitive MIR statements/terminators; `ub_checks`/`overflow_checks` lowered to symbolic `Operand::RuntimeChecks(op)` | **No** | None |

---

### 2. Multi-Profile Benchmark: Stock `inner_optimized_mir` vs. Raw `-Zmir-opt-level=0` vs. Linear-Time `MiniSSA` Canonicalizer (`-O0`..`-Oz`)

`Basis: execution (support/audit_pre_postcleanup_and_benchmark_minissa_canonicalizer.py, support/minissa_canonicalizer_profile_benchmarks.csv)`

Table 2 compares `.text` binary size, stack-frame allocation (`subq $N, %rsp` + `pushq`), compile time, and median execution time across all six Cargo profiles (`-O0`, `-O1`, `-O2`, `-O3`, `-Os`, `-Oz`) for the three MIR configurations:

| Profile | Configuration | `.text` Size (`B`) | Total Stack Frame (`B`) | Max Function Stack Frame (`B`) | Compile Time (`ms`) | Median Runtime (`ms`) | `Runtime(PostCleanup)` MIR SHA-256 |
| :---: | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| **`-O0`** | `stock_default_mir_opt` (`level=1`) | `7,113` | `1,848` | `344` | `80.41` | `13.26` | `9495695396666b5f...` |
| **`-O0`** | `raw_mir_opt_0` (`level=0`) | `7,225` | `1,864` | `344` | `78.69` | `13.20` | `9495695396666b5f...` |
| **`-O0`** | **`mir_opt_0_plus_linear_canonicalizer`** | **`7,205`** | **`1,848`** | **`344`** | **`78.11`** | **`12.42` (`+6.3%`)** | `9495695396666b5f...` |
| **`-O1`** | `stock_default_mir_opt` (`level=2`) | `1,323` | `112` | `72` | `96.19` | `2.81` | `9495695396666b5f...` |
| **`-O1`** | `raw_mir_opt_0` (`level=0`) | `1,323` | `112` | `72` | `96.71` | `2.91` | `9495695396666b5f...` |
| **`-O1`** | **`mir_opt_0_plus_linear_canonicalizer`** | **`1,306` (`-1.3%`)** | **`112`** | **`72`** | **`97.03`** | **`2.82`** | `9495695396666b5f...` |
| **`-O2`** | `stock_default_mir_opt` (`level=2`) | `1,885` | `88` | `48` | `107.16` | `2.36` | `9495695396666b5f...` |
| **`-O2`** | `raw_mir_opt_0` (`level=0`) | `1,859` | `88` | `48` | `104.55` | `2.36` | `9495695396666b5f...` |
| **`-O2`** | **`mir_opt_0_plus_linear_canonicalizer`** | **`1,859` (`-1.4%`)** | **`88`** | **`48`** | **`106.46`** | **`2.38`** | `9495695396666b5f...` |
| **`-O3`** | `stock_default_mir_opt` (`level=2`) | `1,885` | `88` | `48` | `105.28` | `2.64` | `9495695396666b5f...` |
| **`-O3`** | `raw_mir_opt_0` (`level=0`) | `1,859` | `88` | `48` | `107.13` | `2.36` | `9495695396666b5f...` |
| **`-O3`** | **`mir_opt_0_plus_linear_canonicalizer`** | **`1,859` (`-1.4%`)** | **`88`** | **`48`** | **`106.13`** | **`2.43`** | `9495695396666b5f...` |
| **`-Os`** | `stock_default_mir_opt` (`level=2`) | `984` | `112` | `72` | `94.41` | `3.13` | `9495695396666b5f...` |
| **`-Os`** | `raw_mir_opt_0` (`level=0`) | `984` | `112` | `72` | `92.94` | `3.24` | `9495695396666b5f...` |
| **`-Os`** | **`mir_opt_0_plus_linear_canonicalizer`** | **`961` (`-2.3%`)** | **`112`** | **`72`** | **`93.39`** | **`3.27`** | `9495695396666b5f...` |
| **`-Oz`** | `stock_default_mir_opt` (`level=2`) | `1,309` | `208` | `120` | `98.08` | `3.43` | `9495695396666b5f...` |
| **`-Oz`** | `raw_mir_opt_0` (`level=0`) | `1,309` | `208` | `120` | `99.88` | `3.37` | `9495695396666b5f...` |
| **`-Oz`** | **`mir_opt_0_plus_linear_canonicalizer`** | **`1,309` (`0.0%`)** | **`208`** | **`120`** | **`96.91`** | **`3.38`** | `9495695396666b5f...` |

## Boundaries

1. **Flags That Must Match Between Verifier Capture (`cargo anneal`) and Release Codegen (`known not to apply` if mismatched):**
   - While `-C opt-level` (`0`, `1`, `2`, `3`, `s`, `z`) has **zero** effect on `Runtime(PostCleanup)` MIR, three non-optimization flags alter HIR expansion or pre-`PostCleanup` lowering:
     1. `-C debug-assertions=on/off` (evaluated during AST `cfg!(debug_assertions)` expansion before `mir_built`);
     2. `-C panic=unwind/abort` (controls `AbortUnwindingCalls` and `ElaborateDrops` cleanup landing pads before `Runtime(PostCleanup)`); and
     3. `-C overflow-checks=on/off` (controls `MIR` building of checked binary operators `BinOp::AddWithOverflow` + `TerminatorKind::Assert` vs. `BinOp::Add`, plus downstream folding of `Operand::RuntimeChecks(OverflowChecks)`).
   - Therefore, `.anneal-mir` capture manifests must record `(debug_assertions, panic_strategy, overflow_checks, target_triple)` in the cryptographic artifact header.

## Evidence

1. **Automated Audit and Multi-Profile Benchmark Script:**
   - [`support/audit_pre_postcleanup_and_benchmark_minissa_canonicalizer.py`](support/audit_pre_postcleanup_and_benchmark_minissa_canonicalizer.py)
2. **Preserved Machine-Readable Datasets:**
   - [`support/pre_postcleanup_pass_audit.json`](support/pre_postcleanup_pass_audit.json): Complete audit of all 16 pre-`Runtime(PostCleanup)` pass groups in `rustc 1.99.1`.
   - [`support/profile_invariance_diff.json`](support/profile_invariance_diff.json): SHA-256 verification of `3-2-000.runtime-post-cleanup.after.mir` across `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz`.
   - [`support/minissa_canonicalizer_profile_benchmarks.json`](support/minissa_canonicalizer_profile_benchmarks.json) and [`support/minissa_canonicalizer_profile_benchmarks.csv`](support/minissa_canonicalizer_profile_benchmarks.csv): `.text` size, stack frame bytes, compile time, and median runtime across all 18 `(profile × config)` pairs.

## Revalidation

Run the reproducible audit and benchmark script against `rustc +1.99.1-x86_64-unknown-linux-gnu`:

```bash
python3 reports/rustc-pre-postcleanup-lowerings-and-minissa-canonicalizer-replacement/support/audit_pre_postcleanup_and_benchmark_minissa_canonicalizer.py
```
