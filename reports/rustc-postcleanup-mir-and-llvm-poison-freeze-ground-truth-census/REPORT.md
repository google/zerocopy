# Post-Cleanup MIR Move-Aliasing Hazards and LLVM 23.1.1 Poison, Freeze, and Unwind Ground-Truth Census

## Summary

Empirical inspection of `16,379` `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `LLVM 23.1.1`) MIR bodies (`57,591` basic blocks) across `library/core` (`11,339`), `zerocopy 0.9.0-alpha.1` (`4,791`), `joshlf/anneal` TCB crates (`110`), and `tests/mir-opt` (`139`), paired with `667` post-`-O3` LLVM IR functions (`8,862` basic blocks, `2,976` `phi`s) across `core.ll` (`543`), `anneal_audit.ll` (`79`), and `cargo_anneal.ll` (`45`), establishes four ground-truth invariants for verified Rust IRs:

1. **Two `deinitMovedPlace = true` Hazards Appear in Production MIR:** Upstream `rustc` (`ssa.rs`, `operand.rs`) treats `Operand::Move` as a non-mutating read outside in-place `Call` arguments, whereas `joshlf/anneal`'s `Trusted.MirSemantics.evalOperandToSlot` (`MirSemantics.lean:949-976`) overwrites moved non-ZST locals with `.live none`. In `rustc 1.99.1` MIR: (a) **partial-field moves (`m3_partial_field_move`)**—moving `(local.0)` then reading/moving disjoint `(local.1)`—occur in `0.04%` of `libcore` (`4` bodies), `0.27%` of `zerocopy` (`13`), and `4.32%` of `tests/mir-opt` (`6`), refuting whole-local move deinitialization on aggregates; and (b) **same-call `copy _k, move _k` aliasing (`m4_same_stmt_move_alias`)** occurs in `0.07%` of `libcore` (`8` bodies, `9` `slice_index_fail` calls from `RangeFrom::index` + `GVN`), requiring strictly left-to-right stateful operand threading across `TerminatorKind::Call`.
2. **Post-`-O3` `LLVM 23.1.1` IR Mixes Frontend Attributes with Optimizer-Synthesized Poison Flags and `freeze`:** Alongside `rustc`-emitted `noundef` (`99.82%–100.0%`), `noalias` (`96.69%–98.73%`), `captures(none)` (`71.09%–86.08%`), `nuw` (`73.30%–87.34%`, including `getelementptr inbounds nuw`), `nsw` (`39.24%–43.83%`), and `range(...)` (`27.44%–71.11%`), LLVM's middle-end synthesizes `zext`/`uitofp` `nneg` (`26.34%` in `libcore`), `icmp samesign` (`22.10%` in `libcore`; `13.33%–15.19%` in `anneal` TCB), `or disjoint` (`14.73%`), `poison` literals (`6.33%–10.50%`), `undef` (`5.06%–7.18%`), and `freeze` (`2.22%–3.50%`, `26` `.fr` instructions across SROA split structs, `@bcmp` folds, and loop-unswitched pointers).
3. **A `219x` Unwinding Cliff Separates `libcore` from `std` Binaries (`0.18%` vs. `40.32%` `invoke`/`landingpad`):** Because `UnwindAction::Continue` lowers to plain `call` (`block.rs:228`) while only active `Drop` cleanups (`UnwindAction::Cleanup`) and `Terminate` edges emit `invoke` + `landingpad`, `core.ll` has `1 / 543` (`0.18%`) unwinding functions (and polymorphic `zerocopy.ll` emits `0` concrete functions), whereas `cargo_anneal` (`37.78%`) and `anneal_audit` (`41.77%`) average `40.32%` (`50 / 124` functions, `817` `invoke`s) plus up to `16.46%` `dead_on_unwind` (`abi.rs:503-512`).
4. **Architectural Split Between MIR-Level Verification and LLVM-IR Validation:** Unprojected, raw-pointer-free, non-unwinding MIR covers `57.55%` of `libcore` and `64.37%` of `zerocopy` (`40.91%` of `std` TCB crates), with `StorageLive`/`StorageDead` comprising `60.19%–63.21%` of tracked statements. Lowering directly from post-cleanup MIR into total verified SSA avoids importing LLVM's `undef`/`poison`/`freeze`/`captures(...)` lattice into the TCB.

---

## Applicability

Findings apply to `rustc 1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`) with bundled `LLVM 23.1.1` (`rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, matching `llvm/llvm-project@6dfe1677ab8dffbc6ec13d53a1e0215d75147689`, tag `llvmorg-23.1.1`) on `x86_64-unknown-linux-gnu` (`-C opt-level=3` / `--release`, default `panic=unwind` plus paired `panic-abort`/`panic-unwind` dumps in `tests/mir-opt`).

Relationships among the six subjects in `REPORT.json`:

- **`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):** Supplies compiler pass/codegen sources, the `11,339`-body / `543`-LLVM-function `libcore` census, and `139` `tests/mir-opt` runtime-optimized dumps.
- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `LLVM 22.1.6`):** Used solely by `support/analyze_census_and_probe.py --run-live-probe` on the 6-function specimen `support/reproduce_hazards_probe.rs`; all crate-census tables come strictly from `rustc 1.99.1`.
- **`llvm/llvm-project@6dfe1677ab8dffbc6ec13d53a1e0215d75147689` & `rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`:** Supply identical `30,337`-line `llvm/docs/LangRef.md` specifications (migrated from `LangRef.rst` in LLVM 23) and middle-end pass sources (`SROA.cpp`, `SimplifyCFG.cpp`, `InstCombineCompares.cpp`, `InstCombineSelect.cpp`, `SimpleLoopUnswitch.cpp`).
- **`google/zerocopy@9384a926b073a866a3e6b1f7fa3db3925c9485b6` (`0.9.0-alpha.1`):** Polymorphic `#[no_std]` library supplying `4,791` MIR bodies and `0` standalone `.rlib` LLVM functions.
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Target mechanized MIR semantics (`trusted/lean/Trusted/MirSemantics.lean`, `Trusted/MirAst.lean`, `Trusted/Correspondence.lean`) and `std` binary crates `anneal_audit` and `cargo_anneal` (`110` MIR bodies, `124` LLVM functions).

Adjacent packages cover complementary theory without duplication: `mir-move-deinit-gvn-cse-and-guarded-preheader-licm-soundness` specifies unprojected scalar `MoveToCopy`/`StorageSafe` checkers, and `undefined-values-poison-undef-freeze-and-refinement` formalizes abstract `undef`/`poison`/`freeze` refinement laws.

---

## Findings

### 1. Corpus-Wide `rustc 1.99.1` MIR Structural Baseline (`16,379` Bodies)

`Basis: execution (rustc 1.99.1 real crate census in support/rustc_1_99_1_census.json) + source`

In `compiler/rustc_mir_transform/src/lib.rs:537-824` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`), `mir_drops_elaborated_and_const_checked` (`L537-626`) runs `run_analysis_to_runtime_passes` (`ElaborateDrops`, `AbortUnwindingCalls`, `AddMovesForPackedDrops`, `ElaborateBoxDerefs`, `StateTransform`, `LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`). `optimized_mir` / `inner_optimized_mir` (`L778-824`) steals that body and runs `run_optimization_passes` (`L687-775`), including `LowerSliceLenCalls`, `Inline`, `RemoveStorageMarkers`, `ScalarReplacementOfAggregates`, `GVN`, `SsaRangePropagation`, `JumpThreading`, `CopyProp`, and `DeadStoreElimination`. Even after `RemoveStorageMarkers` (`L717`), `rustc` preserves `StorageLive`/`StorageDead` whenever LLVM stack coloring is active.

Table 1 reports the measured `rustc 1.99.1` MIR census (`support/rustc_1_99_1_census.json`, verified by `support/analyze_census_and_probe.py`):

| Metric / Construct | `libcore` (`1.99.1`) | `zerocopy` (`0.9.0-alpha.1`) | `anneal` TCB (`2` crates) | `tests/mir-opt` (`runtime-opt`) |
| :--- | ---: | ---: | ---: | ---: |
| **Total MIR bodies** | `11,339` | `4,791` | `110` | `139` |
| **Total basic blocks (mean / body)** | `40,946` (`3.61`) | `15,112` (`3.15`) | `923` (`8.39`) | `610` (`4.39`) |
| **BB count `p50 / p95 / p99 / max`** | `2 / 9 / 28 / 127` | `1 / 11 / 16 / 131` | `2 / 31 / 59 / 202` | `3 / 13 / 17 / 19` |
| **`fits_unproj_no_unwind_no_rawptr`** | `6,526` (**`57.55%`**) | `3,084` (**`64.37%`**) | `45` (**`40.91%`**) | `67` (**`48.20%`**) |
| **`has_deref_proj` (`*place`)** | `3,854` (`33.99%`) | `1,081` (`22.56%`) | `52` (`47.27%`) | `63` (`45.32%`) |
| **`has_transmute` (`CastKind::Transmute`)** | `1,241` (`10.94%`) | `1,396` (**`29.14%`**) | `17` (`15.45%`) | `32` (`23.02%`) |
| **`has_raw_ptr` (`&raw` / `*const` / `*mut`)** | `237` (`2.09%`) | `460` (`9.60%`) | `15` (`13.64%`) | `13` (`9.35%`) |
| **`has_mir_intrinsic` (`StatementKind::Intrinsic`)** | `449` (`3.96%`) | `69` (`1.44%`) | `9` (`8.18%`) | `7` (`5.04%`) |
| **`has_loop` (CFG back-edge)** | `168` (`1.48%`) | `23` (`0.48%`) | `1` (`0.91%`) | `18` (`12.95%`) |
| **`has_unwind_cleanup` (cleanup BB / `Resume`)** | `133` (`1.17%`) | `20` (`0.42%`) | `25` (**`22.73%`**) | `9` (`6.47%`) |
| **`m3_partial_field_move` bodies** | `4` (`0.04%`) | `13` (**`0.27%`**) | `0` (`0.00%`) | `6` (**`4.32%`**) |
| **`m4_same_stmt_move_alias` bodies (sites)** | `8` (**`0.07%`**, `9` sites) | `0` (`0.00%`) | `0` (`0.00%`) | `0` (`0.00%`) |
| **`Assign` statements** | `60,161` | `18,360` | `1,825` | `906` |
| **`StorageLive` / `StorageDead` statements** | `49,000` / `53,665` | `15,791` / `16,478` | `1,328` / `1,520` | `632` / `750` |
| **`Storage{Live,Dead}` share of tracked stmts** | **`62.84%`** | **`63.21%`** | **`60.74%`** | **`60.19%`** |
| **Terminators: `Call / Return / SwitchInt / Goto`** | `11,085 / 11,055 / 6,813 / 8,254` | `3,790 / 4,763 / 1,941 / 3,205` | `323 / 110 / 138 / 188` | `82 / 139 / 125 / 193` |
| **Terminators: `Assert / Unreachable / Drop / Resume`** | `1,395 / 932 / 236 / 133` | `359 / 831 / 48 / 20` | `2 / 18 / 112 / 25` | `9 / 21 / 26 / 9` |
| **Rvalues: `Transmute / RawPtr / PtrMetadata / CheckedOp`** | `2,418 / 356 / 405 / 253` | `3,728 / 497 / 42 / 47` | `154 / 52 / 14 / 1` | `153 / 19 / 22 / 3` |
| **Unwind actions: `continue / unreachable / terminate`** | `9,089 / 3,965 / 351` | `3,205 / 1,052 / 24` | `151 / 5 / 60` | `34 / 64 / 9` |

Key baseline properties: (1) `StorageLive`/`StorageDead` account for `60.19%–63.21%` (`139,164` vs. `81,252` `Assign`s) of tracked statements across every corpus; (2) unprojected, raw-pointer-free, unwind-free bodies cover `57.55%` of `libcore` and `64.37%` of `zerocopy`, while `has_deref_proj` (`22.56%–47.27%`) and `has_transmute` (`10.94%–29.14%`, `3,728` sites in `zerocopy`) dominate the remainder; and (3) `zerocopy-1d9b641a4817cd80.ll` contains **`0` LLVM IR `define`s** because all non-const items in `zerocopy` are generic and monomorphize only inside downstream consumer crates.

---

### 2. `deinitMovedPlace = true` Partial-Field-Move (`m3_partial_field_move`) and Intra-Call Aliasing (`m4_same_stmt_move_alias`) Hazards

`Basis: execution (rustc 1.99.1 crate census + live rustc 1.98.0-nightly probe) + source + derived`

#### 2.1 Upstream `rustc` vs. `Trusted.MirSemantics`

In `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `compiler/rustc_middle/src/mir/syntax.rs:1289-1306` notes `Operand::Move` *may* overwrite a place with `uninit` (`UCG#188`), yet states *"Currently (both in Miri and codegen) it has no effect at all unless it appears in an argument to `Call`."* Concretely: (1) `visit.rs:538, 831` visits `Operand::Move` as `PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)`; (2) `ssa.rs:247-250, 301, 421-440` treats `Move` as non-mutating, merges `Copy | Move` equivalence classes, and marks locals uninitialized only on `Storage{Live,Dead}`; and (3) `rustc_codegen_ssa/src/mir/operand.rs:1133-1144` lowers `Copy` and `Move` identically via `codegen_consume`.

Conversely, `joshlf/anneal` (`trusted/lean/Trusted/MirSemantics.lean:949-976` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`) sets `deinitMovedPlace = true`: evaluating `.move place` on a non-ZST unprojected local updates `locals[place.localId]` to `liveUninitSlot ty = .live none`, faulting with `FaultKind.undefined` on any subsequent read before re-initialization.

#### 2.2 Partial-Field-Move Hazard (`m3_partial_field_move`: `0.04%–4.32%`)

Twenty-three MIR bodies move `(local.i)` and then read or move sibling `(local.j)` (`i != j`) without re-initializing `local`:

| Corpus | Bodies (`%`) | Upstream Functions & Spans | Emitted `rustc 1.99.1` MIR |
| :--- | ---: | :--- | :--- |
| **`libcore`** | `4 / 11,339` (`0.04%`) | `{f16,f32,f64,f128}::clamp` (`library/core/src/num/f32.rs:1604-1611`) | `_0 = f32::<impl f32>::clamp::do_panic::compiletime(move (_3.0: f32), move (_3.1: f32)) -> unwind continue;` |
| **`zerocopy`** | `13 / 4,791` (`0.27%`) | `MetadataOf::padding_needed_for` (`src/util/mod.rs:481-483`), `Ref::from_suffix_with_elems` (`src/ref.rs:501-504`), `Split::via_*` (`src/split_at.rs:297-299, 595-597, 800-803`), `swap` | Moves `(_1.0: &T)` (or `(_2.0: usize)`), then `_12 = move (_1.1: usize);` |
| **`tests/mir-opt`** | `6 / 139` (`4.32%`) | `slice_{index,get_unchecked_mut,ptr_get_unchecked}_range` (`tests/mir-opt/pre-codegen/slice_index.rs:29-60`, `panic-{abort,unwind}`) | `bb0: _3 = move (_2.0: usize); _4 = move (_2.1: usize);` (`_2: Range<usize>`, `.mir:35-36`) |

At `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `evalOperandToSlot` returns `.error .unsupported` on non-empty projections (`MirSemantics.lean:962-964`). Generalizing `deinitMovedPlace = true` to aggregates by setting the whole root slot `locals[place.localId] := .live none` on `move (_2.0)` causes `_4 = move (_2.1)` to fault with spurious `FaultKind.undefined`. Aggregate `LocalSlot`s must track initialization per leaf field (or byte), and `MoveToCopy` bitmasks (`mir-move-deinit-gvn-cse-and-guarded-preheader-licm-soundness`) must index flattened `(localId, fieldPath)` leaves.

#### 2.3 Intra-Call `copy _k, move _k` Aliasing (`m4_same_stmt_move_alias`: `0.07%`)

In `libcore`, `8` bodies (`0.07%`) across `9` `TerminatorKind::Call` sites pass `copy _k` and `move _k` for the same `usize` local in one argument list: `parse_decimal_seq` (`bb59`, `_104`), `try_parse_digits` (`bb9`, `_34`), `parse_partial_number` (`bb41`, `_108`), `dec2flt` (`bb38`, `_42`), `round_up` (`bb10` and `bb13`, `_12`), `digits_to_dec_str` (`bb44`, `_69`), `digits_to_exp_str` (`bb31`, `_66`), and `num::imp::fmt` (`bb13`, `_56`), all of the form:

```text
_105 = slice_index_fail(const 8_usize, copy _104, move _104) -> unwind continue;
```

**Root cause:** `<ops::RangeFrom<usize> as SliceIndex<[T]>>::index` (`library/core/src/slice/index.rs:542-546`) calls `slice_index_fail(self.start, slice.len(), slice.len())`. After `Inline` + `LowerSliceLenCalls` (`lib.rs:705, 712`), `GVN` (`lib.rs:744`) deduplicates both `PtrMetadata(copy _slice)` locals into `_k`, leaving `copy _k` in `args[1]` and promoting the last-live use in `args[2]` to `move _k` (reproduced live by `probe_m4_range_from_const`). Under `deinitMovedPlace = true`, admitting `TerminatorKind.call` requires folding `evalOperandToSlot` **strictly left-to-right** across `args` (matching `evalRvalue`'s `.binaryOp` threading at `MirSemantics.lean:1252-1261` and `pass_argument` in `rustc_const_eval/src/interpret/call.rs:340-360, 523-530`); upfront `move`-set deinitialization or right-to-left evaluation faults with spurious UB on all `9` sites. Zero instances of `(move _k, copy _k)` occur in the `16,379` bodies.

---

### 3. `LLVM 23.1.1` Poison, Provenance, and `freeze` Ground-Truth Prevalence (`667` Functions)

`Basis: execution (rustc 1.99.1 / LLVM 23.1.1 census + live probe) + normative (llvm/docs/LangRef.md) + source`

#### 3.1 Function Prevalence and Violation Semantics

Table 2 gives `fn_with_feature` (`%`) / `total_occurrences` across `667` post-`-O3` LLVM 23.1.1 functions alongside emission origins and `llvm/docs/LangRef.md` (`6dfe1677ab8dffbc6ec13d53a1e0215d75147689`) semantics:

| LLVM 23.1.1 Construct | `core.ll` (`543` fns) | `anneal_audit.ll` (`79` fns) | `cargo_anneal.ll` (`45` fns) | Origin (`rustc` vs. LLVM) | Violation Semantics (`LangRef.md`) |
| :--- | ---: | ---: | ---: | :--- | :--- |
| **`noundef`** | `542` (**`99.82%`**) / `9,070` | `79` (**`100.0%`**) / `3,211` | `45` (**`100.0%`**) / `1,574` | `rustc` (`abi.rs:45, 107`) | **Immediate UB** on any `undef`/`poison` bit (`L1699-1706`). |
| **`noalias`** | `525` (**`96.69%`**) / `7,498` | `78` (**`98.73%`**) / `4,021` | `44` (**`97.78%`**) / `1,915` | `rustc` (`abi.rs:42`) + inline | **Immediate UB** on un-based conflicting access (`L1512-1534`). |
| **`nuw`** (arith/GEP/`trunc`) | `398` (**`73.30%`**) / `5,112` | `69` (**`87.34%`**) / `1,940` | `35` (**`77.78%`**) / `1,051` | `rustc` (`builder.rs:979`) + LLVM | **`poison`** on unsigned wrap (`L10671`, `L12338`, `L12491`). |
| **`captures(none)`** | `386` (**`71.09%`**) / `674` | `68` (**`86.08%`**) / `142` | `37` (**`82.22%`**) / `63` | `rustc` (`abi.rs:54-56`) + LLVM | UB/poison on `address`/`provenance` capture (`L1538-1573`). |
| **`nsw`** | `238` (**`43.83%`**) / `1,743` | `31` (**`39.24%`**) / `77` | `18` (**`40.00%`**) / `63` | `rustc` + LLVM `InstCombine` | **`poison`** on signed wrap; `inbounds` implies `nusw` (`L12371`). |
| **`@llvm.lifetime.*`** | `210` (`38.67%`) / `1,315` | `25` (`31.65%`) / `485` | `8` (`17.78%`) / `242` | `rustc` (`builder.rs:1444`) | Access outside `[start, end]` is UB/poison. |
| **`range(<ty> a, b)`** | `149` (`27.44%`) / `244` | `55` (**`69.62%`**) / `356` | `32` (**`71.11%`**) / `219` | `rustc` (`abi.rs:492, 533, 557`) | **`poison`** if scalar outside `[a, b)` (`L1915-1925`). |
| **`nneg`** (`zext`/`uitofp`) | `143` (**`26.34%`**) / `499` | `2` (`2.53%`) / `11` | `0` (`0.00%`) / `0` | **100% LLVM** (`0` in `rustc`) | **`poison`** if operand sign bit is `1` (`L12537`, `L12780`). |
| **`samesign`** (`icmp`) | `120` (**`22.10%`**) / `418` | `12` (**`15.19%`**) / `23` | `6` (**`13.33%`**) / `13` | **100% LLVM** (`InstCombineCompares.cpp:681, 7169`) | **`poison`** if operand sign bits differ (`L13211-13212`). |
| **`select`** | `111` (`20.44%`) / `556` | `9` (`11.39%`) / `25` | `7` (`15.56%`) / `11` | `rustc` + LLVM | `cond = poison` -> `poison`; untaken arm masked (`L13408-13419`). |
| **`@llvm.assume`** | `104` (`19.15%`) / `369` | `26` (`32.91%`) / `148` | `12` (`26.67%`) / `46` | `rustc` validity checks | **Immediate UB** if `false` or `poison`. |
| **`disjoint`** (`or`) | `80` (**`14.73%`**) / `293` | `2` (`2.53%`) / `9` | `1` (`2.22%`) / `6` | `rustc` (`builder.rs:575`) + LLVM | **`poison`** if overlapping `1`-bits (`L11355-11359`). |
| **`@llvm.memcpy`** | `59` (`10.87%`) / `115` | `18` (`22.78%`) / `252` | `5` (`11.11%`) / `117` | `rustc` + `MemCpyOpt` | Bytewise copy preserving `undef`/`poison` bits. |
| **`sret(<ty>)`** | `58` (`10.68%`) / `91` | `6` (`7.59%`) / `33` | `4` (`8.89%`) / `27` | `rustc` (`abi.rs:498, 627`) | Indirect caller-allocated return slot. |
| **`poison` literal** | `57` (**`10.50%`**) / `102` | `5` (`6.33%`) / `13` | `0` (`0.00%`) / `0` | LLVM `SROA`/`SCCP` + `rustc` | Deferred error; UB at `br`, deref, div-0, `noundef` (`L5417-5434`). |
| **SIMD `<N x ty>`** | `54` (`9.94%`) / `647` | `4` (`5.06%`) / `32` | `2` (`4.44%`) / `28` | `rustc` + `SLP`/`LoopVec` | Element-wise `poison`/`undef`/`freeze` (`L13466`). |
| **`switch`** | `53` (`9.76%`) / `87` | `9` (`11.39%`) / `17` | `3` (`6.67%`) / `5` | `rustc` + `SimplifyCFG` | **Immediate UB** on `undef`/`poison` condition (`L5375`). |
| **`dead_on_unwind`** | `46` (`8.47%`) / `46` | `13` (**`16.46%`**) / `13` | `2` (`4.44%`) / `2` | `rustc` (`abi.rs:509`) | Callee writes become **`poison`** on unwind (`L1878-1890`). |
| **`undef` literal** | `39` (`7.18%`) / `227` | `4` (`5.06%`) / `16` | `3` (`6.67%`) / `14` | `rustc` `insertvalue` + LLVM | Per-use arbitrary bits (`x ^ x != 0` allowed; `L5223-5335`). |
| **`freeze`** | `19` (**`3.50%`**) / `22` | `2` (**`2.53%`**) / `2` | `1` (**`2.22%`**) / `2` | **100% LLVM** (`.fr` suffix) | Fixes `undef`/`poison` to one arbitrary value (`L13436-13490`). |
| **`exact`** / **`atomic`** | `14` (`2.58%`) / `13` (`2.39%`) | `5` (`6.33%`) / `7` (`8.86%`) | `5` (`11.11%`) / `5` (`11.11%`) | `rustc` + LLVM | `exact`: `poison` on remainder; `atomic`: memory ordering. |
| **`dead_on_return`** | `4` (`0.74%`) / `4` | `2` (`2.53%`) / `3` | `0` (`0.00%`) / `0` | `rustc` (`abi.rs:542`) | Callee writes become **`poison`** on return/unwind (`L1892-1913`). |
| **`invoke` / `landingpad`** | `1` (**`0.18%`**) / `2` & `1` | `33` (**`41.77%`**) / `502` & `184` | `17` (**`37.78%`**) / `315` & `125` | `rustc` (`block.rs:220-260`) | Unwind CFG split + cleanup pad (Section 4). |

#### 3.2 Frontend Migrations vs. Optimizer-Synthesized Flags and `freeze` Idioms

1. **LLVM 22–23 frontend shifts (`abi.rs`, `builder.rs`):** Legacy `nocapture` is replaced by parameterized `captures(...)` (`abi.rs:54-56`, `LangRef.md:1538-1573`, distinguishing `captures(none)` from `captures(address, read_provenance)` on sub-slice borrows and `ptrtoaddr` at `L12882-12915`). `nuw` reaches `73.30%–87.34%` (`8,103` sites) via `inbounds_nuw_gep` (`builder.rs:979`). Slice-pair metadata carries `range(i64 0, (isize::MAX / elem_size) + 1)` (`abi.rs:559-575`), driving `range_attr` to `69.62%–71.11%` in `&str`/`&[T]`-heavy `std` binaries. Because `noundef` sits on `99.82%–100.0%` of functions, almost every Rust call/return boundary converts deferred `poison` into immediate UB (Lee et al., PLDI 2017, DOI `10.1145/3062341.3062343`).
2. **Optimizer-only `nneg` (`26.34%`) and `samesign` (`22.10%`):** `rustc_codegen_llvm` emits neither flag; LLVM's `InstCombine` upgrades `zext` to `zext nneg` and `icmp` to `icmp samesign` (`InstCombineCompares.cpp:680-681, 7165-7170`) using `KnownBits` seeded by unsigned casts and `range(...)` attributes.
3. **Three concrete `freeze` families (`22` functions, `26` instructions):** `rustc` emits zero `freeze`s; LLVM inserts `.fr` instructions whenever branch/select/loop transforms risk branching on `poison` (`br poison` is immediate UB, `LangRef.md:5426`):
   - **SROA split-struct scalarization (`core.ll`, `19` fns / `22` sites):** `%decoded.sroa.4.0.i.fr.i = freeze i8 %decoded.sroa.4.0.i.i` across `core::fmt::float::float_to_{decimal,exponential}_common_{exact,shortest}` (`f16`/`f32`/`f64`, `library/core/src/fmt/float.rs:36-57`), where trailing `Decoded` bytes are uninitialized on non-finite float paths (`SROA.cpp:5048-5198`, `SimplifyCFG.cpp:5345-5346`).
   - **Unannotated `@bcmp` folding (`anneal_audit.ll`, `cargo_anneal.ll`):** `%bcmp.i.fr... = freeze i32 %bcmp...` in `clap_builder::FlatMap::remove_entry` and `cargo_anneal::main`, because `@bcmp`'s declared `i32` return lacks `noundef` (`InstCombineSelect.cpp:1055, 3948`, `SimpleLoopUnswitch.cpp:320-321`).
   - **Pointer condition freezing (`anneal_audit.ll`, `cargo_anneal.ll`):** `%.fr = freeze ptr %1` in `FlattenCompat::next` and `%.fr.i.i.i.i.i.i.i = freeze ptr %278` in `cargo_anneal::main` (`LangRef.md:13462-13464`: frozen `poison` pointers yield deterministic bits but remain non-dereferenceable). As shown in `undefined-values-poison-undef-freeze-and-refinement`, non-monotonic `freeze` invalidates naive e-graph congruence (`freeze(x + x)` vs. `freeze(x) + freeze(x)`).

---

### 4. The `libcore` vs. `std`-Crate Unwinding Cliff (`0.18%` vs. `37.78%–41.77%`)

`Basis: execution (rustc 1.99.1 / LLVM 23.1.1 census) + source + normative`

| Metric | `core.ll` (`543` fns) | `cargo_anneal.ll` (`45` fns) | `anneal_audit.ll` (`79` fns) | Combined TCB (`124` fns) |
| :--- | ---: | ---: | ---: | ---: |
| **Functions with `invoke` (`landingpad`)** | `1` (**`0.18%`**) | `17` (**`37.78%`**) | `33` (**`41.77%`**) | `50` (**`40.32%`**, **`219.0x`** `core`) |
| **Total `invoke` / `landingpad` sites** | `2` / `1` | `315` / `125` | `502` / `184` | **`817` / `309`** (`16.34` `invoke`/unw fn) |
| **BBs `p50 / p95 / max` & `dead_on_unwind`** | `4 / 41 / 225` (`8.47%`) | `8 / 77 / 415` (`4.44%`) | `11 / 94 / 445` (**`16.46%`**) | — (`12.10%` `dead_on_unwind`) |

In `compiler/rustc_codegen_ssa/src/mir/block.rs:216-260`, `do_call` maps `UnwindAction::Continue` (`9,089` MIR edges in `libcore`) to `unwind_block = None` (`L228`), emitting a plain `call` unwound zero-cost via `.eh_frame` CFI; `bx.invoke` + `landingpad cleanup` are emitted *only* for `UnwindAction::Cleanup` (non-nop local `Drop` destructors, `L221-226`) or `Terminate` (`L230-244`). Because `libcore` lacks heap-owning `Drop` types (`String`, `Vec`, `BTreeMap`, `PathBuf`), `core.ll` is `99.82%` `invoke`-free, whereas `std` binaries hit `40.32%` unwinding functions (`16.34` `invoke`s per unwinding function) plus `16.46%` `dead_on_unwind` (`abi.rs:503-512`, overwriting `sret` memory with `poison` on unwind per `LangRef.md:1878-1890`).

---

### 5. Implications for Verified MIR-to-SSA and LLVM-to-MiniMach Coverage

`Basis: derived + source + execution`

1. **Direct MIR-to-SSA Lowering Avoids the LLVM Poison/Freeze TCB Tax:** Ingesting MIR directly after `mir_drops_elaborated_and_const_checked` (`Trusted.MirSemantics`) works over total two's-complement arithmetic and explicit `FaultKind.undefined`, keeping `undef`, `freeze`, `samesign`, `nneg`, and `captures(...)` out of the TCB. When untrusted LLVM 23.1.1 hints guide a verified MiniSSA/MiniMach replayer, `samesign`/`nneg`/`disjoint`/`nuw` hints require checked non-wrap/sign certificates seeded by MIR type validity (`abi.rs:559-575`) rather than blind flag copying.
2. **Sequenced MIR Coverage Roadmap:** Discharging `StorageLive`/`StorageDead` (`60.2%–63.2%` of statements) unlocks fast symbolic execution on the `57.55%–64.37%` scalar/unprojected `#[no_std]` core; admitting aggregates and calls under `deinitMovedPlace = true` immediately requires leaf-field initialization tracking (`m3_partial_field_move`) and left-to-right `Call` operand threading (`m4_same_stmt_move_alias`), followed by deref projections (`22.6%–47.3%`), `Transmute` (`10.9%–29.1%`), and `Cleanup` unwinding (`22.7%` MIR / `40.3%` binary LLVM IR).
3. **Black-Box Post-`-O3` LLVM Validator Floor (Alive2, Lopes et al., PLDI 2021, DOI `10.1145/3453483.3454030`):** Validating `rustc 1.99.1 -O` LLVM IR requires modeling `noundef` (`100%`), `noalias` (`98.7%`), `captures(...)` (`86.1%`), `nuw`/`nsw` (`87.3%`), `invoke`/`landingpad` + `dead_on_unwind` (`40.3%`), `nneg`/`samesign` (`22.1%–26.3%`), and `freeze` (`2.2%–3.5%`).

---

### 6. Performance (`L1`–`L6`), Comprehensibility (`C1`–`C2`), and Validation (`V1`–`V4`)

`Basis: execution + source + derived`

- **Performance & Footprint (`L1`–`L6`):** **`L1` (Proof velocity):** Certified storage-marker erasure strips `60.19%–63.21%` of MIR statements; leaf-field move tracking avoids manual rewrites on `4.32%` of `mir-opt` and `0.27%` of `zerocopy` bodies. **`L2` (Toolchain build time):** `not measured`. **`L3` (Compile / scan latency):** Live `rustc 1.98.0-nightly -O --emit=mir,llvm-ir` compilation of `support/reproduce_hazards_probe.rs` plus full JSON census analysis runs in `~1.8 s`; full-crate `rustc 1.99.1` compile times are `not measured`. **`L4` (Generated code runtime):** `not measured` in this static IR census. **`L5` (Checker throughput):** `not measured`, bounded structurally by `bb_p99 = 59` / `bb_max = 202` (MIR) and `bb_p95 = 94` / `bb_max = 445` (`anneal_audit.ll`). **`L6` (Footprint):** `support/rustc_1_99_1_census.json` is `30.5 KiB` (`< 64 MiB` analyzer RSS); `libcore` peak compile RSS is `not measured`.
- **Comprehensibility (`C1`–`C2`):** **`C1` (Auditability):** Auditing `Trusted.MirSemantics.lean` (`2,681` lines, two-pole `FaultKind`) with leaf-field initialization and left-to-right `Call` threading is substantially smaller than auditing LLVM 23.1.1's coupled `undef`/`poison`/`freeze`/`noalias`/`captures`/`dead_on_unwind` rules (`30,337`-line `LangRef.md`). **`C2` (Orthogonality):** Neither `deinitMovedPlace = true` (over `SsaLocals`) nor non-monotonic `freeze` (over `poison`) is macro-expressible; both are irreducible semantic primitives.
- **Validation (`V1`–`V4`):** **`V1` (Adequacy):** Real-crate scanning falsified whole-local aggregate move-deinit (`23` bodies) and unsequenced call move-deinit (`8` bodies) prior to mechanization. **`V2` (Live differential probe):** `support/analyze_census_and_probe.py --run-live-probe` reproduces `m3_partial_field_move`, `m4_same_stmt_move_alias`, `noundef`, `noalias`, `captures(...)`, `range`, `nuw`, `nsw`, `disjoint`, `nneg`, `samesign`, `dead_on_unwind`, `dead_on_return`, and `invoke`/`landingpad` live. **`V3` (Weak-memory / silicon leakage):** `not measured`. **`V4` (Held-out crates):** Spanning `libcore`, `zerocopy`, `anneal` TCB binaries, and `tests/mir-opt` exposed the `0.18% -> 40.32%` unwinding cliff and `0`-function generic `.rlib` trap.

---

## Boundaries

- **Known not to apply:** Whole-local `deinitMovedPlace = true` on projected `.field` moves (`23` counterexamples); simultaneous or right-to-left `Call` argument move-deinitialization (`9` `libcore` sites); extrapolating `core.ll`'s `0.18%` `invoke` rate to `std` binaries (`40.32%`); estimating generic library codegen from standalone `.rlib` `.ll` files (`zerocopy.ll` = `0` functions); and citing `llvm/docs/LangRef.rst` on `LLVM 23.1.1` (migrated to `llvm/docs/LangRef.md`).
- **Unsupported:** In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`MirSemantics.lean:953-964, 1407, 1568`), non-empty `Place.projection`, `Rvalue.{ref, addressOf}`, and `TerminatorKind.{call, assert, drop, unwindResume}` step to `.fault .unsupported`.
- **Not examined:** Downstream monomorphized `zerocopy` LLVM IR, sysroot `alloc`/`std` `.ll` files, `panic=abort` `std` binaries, non-`x86_64` EH funclets (`wasm32`/SEH, `block.rs:231-241`), and full-crate pass-threshold diffs between `LLVM 22.1.6` (`0` `freeze`s on the 6-fn micro-probe) and `LLVM 23.1.1` (`26` `freeze`s across `core`/`anneal`).
- **Unknown:** Non-`Transmute` `Rvalue::Cast` breakdown in `support/rustc_1_99_1_census.json` (`casts_top20` suffered parenthesized-type regex truncation, whereas `rvals.Transmute` was counted independently); and upstream resolution of `UCG#188` (`syntax.rs:1291-1305`).

---

## Evidence

1. **Preserved Census & Live Probe (`Basis: execution`, `2026-11-20`):** `support/rustc_1_99_1_census.json` (`rustc 1.99.1`, `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), `support/reproduce_hazards_probe.rs`, and `support/analyze_census_and_probe.py` (live-tested on `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`).
2. **`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`Basis: source + documentation`):** `compiler/rustc_middle/src/mir/syntax.rs:434-465, 683-1025, 1282-1345`; `visit.rs:538, 815-835`; `compiler/rustc_mir_transform/src/lib.rs:537-824`; `ssa.rs:150-166, 228-292, 301-347, 400-455`; `compiler/rustc_const_eval/src/interpret/call.rs:340-360, 523-530`; `compiler/rustc_codegen_ssa/src/mir/operand.rs:1100-1144` & `block.rs:168-260`; `compiler/rustc_codegen_llvm/src/abi.rs:42-56, 107-108, 488-575` & `builder.rs:451, 575, 960-979, 1444, 1915`; `library/core/src/num/f32.rs:1604-1620`; `library/core/src/slice/index.rs:39-47, 542-551`; `library/core/src/fmt/float.rs:36-57`; `tests/mir-opt/pre-codegen/slice_index.slice_index_range.runtime-optimized.after.panic-unwind.mir:32-40, 83-87`.
3. **`llvm/llvm-project` @ `6dfe1677ab8dffbc6ec13d53a1e0215d75147689` & `rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`Basis: normative + source`):** `llvm/docs/LangRef.md` (`L1512-1925`, `L5223-5456`, `L10671-10675`, `L11355-11359`, `L12198-12915`, `L13211-13490`); `llvm/lib/Transforms/InstCombine/InstCombineCompares.cpp:680-681, 7165-7170`; `InstCombineSelect.cpp:1054-1063, 3947-3952, 4727-4733`; `Utils/SimplifyCFG.cpp:5345-5350`; `Scalar/SimpleLoopUnswitch.cpp:319-323`; `Scalar/SROA.cpp:5048-5198`.
4. **`google/zerocopy` @ `9384a926b073a866a3e6b1f7fa3db3925c9485b6` & `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Basis: source`):** `zerocopy` `src/util/mod.rs:481-483`, `src/split_at.rs:297-299, 595-597, 800-803`, `src/ref.rs:501-504`; `anneal` `trusted/lean/Trusted/MirSemantics.lean:66-163, 949-1019, 1240-1269, 1370-1427, 1537-1570` and `trusted/correspondence/Trusted/Correspondence.lean:69-75, 1389-1410, 2616-2645`.
5. **Literature (`Basis: normative + documentation`):** Lee et al., *"Taming Undefined Behavior in LLVM"*, PLDI 2017, pp. 633–647, DOI `10.1145/3062341.3062343`; Lopes et al., *"Alive2: Bounded Translation Validation for LLVM"*, PLDI 2021, pp. 65–79, DOI `10.1145/3453483.3454030`.

---

## Revalidation

1. **Recompute census metrics and run live `rustc` hazard probe (`< 3 s`):**
   ```bash
   python3 reports/rustc-postcleanup-mir-and-llvm-poison-freeze-ground-truth-census/support/analyze_census_and_probe.py --run-live-probe
   ```
   Confirm `16,379` MIR bodies, `m3_partial_field_move` = `4 / 13 / 0 / 6`, `m4_same_stmt_move_alias` = `8` bodies (`9` sites), `anneal_tcb_invoke_fn_pct` = `40.32%` vs. `core.ll` `0.18%`, and live detection of `move (_2.1: usize)` and `slice_index_fail(const 8_usize, copy _5, move _5)`.
2. **Check upstream `rustc` source drift at `<NEW_RUST_SHA>`:**
   ```bash
   BASE="https://raw.githubusercontent.com/rust-lang/rust/${NEW_RUST_SHA}"
   curl --http1.1 -fsSL "${BASE}/compiler/rustc_mir_transform/src/ssa.rs" | grep -nE "Operand::Move|NonMutatingUse|MaybeUninitializedLocals"
   curl --http1.1 -fsSL "${BASE}/library/core/src/slice/index.rs" | grep -nC2 "slice_index_fail(self.start, slice.len(), slice.len())"
   curl --http1.1 -fsSL "${BASE}/compiler/rustc_codegen_llvm/src/abi.rs" | grep -nE "NoUndef|Captures|DeadOnUnwind|DeadOnReturn"
   ```
3. **Check `Trusted.MirSemantics` admission upgrades:** Whenever `MirSemantics.lean` admits `.field` projections or `TerminatorKind.call`, execute canary proofs on `move (_2.0); move (_2.1)` and `call f(copy _k, move _k)` to verify neither steps to `FaultKind.undefined`.
