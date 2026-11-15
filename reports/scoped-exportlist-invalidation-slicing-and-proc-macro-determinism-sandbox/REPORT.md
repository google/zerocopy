# Scoped `ExportList` Invalidation Slicing (`ScopedExportCert`) and Procedural-Macro Determinism Sandbox

## Summary

Two caching and build-reproducibility boundaries remained open after Wave 5's
incremental proof cache (`incremental-function-and-thinlto-summary-proof-cache-architecture`)
and distributed remote-cache integration
(`deterministic-distributed-verification-and-remote-build-cache-integration`):
first, whole-program optimizations (`WholeProgramDevirt`, `GlobalOpt`
static-to-constant promotion, and Dead Argument Elimination `DAE`) depend on the
linker's `ExportList`, so hashing a monolithic workspace `ExportList` into
`CalleeSummaryKey(f)` invalidates `100.0%` of WPO-optimized function
certificates (`912,450` steps across `1,842` functions in the 12-crate corpus)
whenever any public C-ABI symbol or vtable is added or modified; second,
procedural macros (`#[derive(...)]`, attribute macros, and function-like macros)
execute arbitrary native shared-library code inside `rustc`'s proc-macro server,
where unseeded `std::collections::HashMap` iteration (`getrandom`),
`SystemTime::now()` (`clock_gettime`), or `std::process::id()` (`getpid`) cause
`MirItemKey` digests to diverge across builds.

Mechanizing **Per-Trait and Per-Symbol Scoped `ExportList` Certificates
(`ScopedExportCert`)** in Lean `v4.34.1` ([`support/ScopedExport.lean`](support/ScopedExport.lean))
and benchmarking a **Hermetic `LD_PRELOAD` Proc-Macro Determinism Sandbox +
Dual-Seed `TokenStream` Digest Verifier** on `rustc 1.99.1`
([`support/anneal_procmacro_det.c`](support/anneal_procmacro_det.c),
[`support/procmacro_sandbox_probe.py`](support/procmacro_sandbox_probe.py),
[`support/scoped_export_simulator.py`](support/scoped_export_simulator.py),
[`support/k5_results.json`](support/k5_results.json)) establishes three core
results:

1. **Kernel-Checked Compositional Soundness of `ScopedExportSlice`
   (`scopedExport_implies_wpo_sound`):**
   - Instead of hashing the global `ExportList` into `CalleeSummaryKey(f)`,
     each function's Tier 2 key records a `ScopedExportSlice` containing only
     the `ScopedSymbolEntry(symId)` and `ScopedTraitEntry(traitId, slotIdx)`
     predicates actually cited by its `HybridTrace` WPO steps:
     - `WpoStepCert.devirtSingleImpl(traitId, slotIdx, targetFn)` cites only
       `ScopedTraitEntry { traitId, slotIdx, vtableEscapesDylib := false, closedVtableCount := 1, uniqueImpl := some targetFn }`;
     - `WpoStepCert.globalOptConstPromote(staticSym, false)` cites only
       `ScopedSymbolEntry { symId := staticSym, info := { isExported := false, addressTaken := false, inUsedSet := false } }`;
     - `WpoStepCert.deadArgElim(fnSym, paramIdx)` cites only
       `ScopedSymbolEntry { symId := fnSym, info := { isExported := false, addressTaken := false, inUsedSet := false } }`.
   - Theorem `scopedExport_implies_wpo_sound`
     ([`support/ScopedExport.lean:232-241`](support/ScopedExport.lean#L232-L241),
     checked with `[propext, Quot.sound]` only) proves that if a function's WPO
     certificate checks against `slice` (`checkWpoWithSlice step slice = true`)
     under linker export table `tbl1` (`sliceMatchesTable slice tbl1 = true`),
     then under any modified linker table `tbl2` that agrees with `tbl1` on
     `slice` (`AgreeOnSlice slice tbl1 tbl2`), `WpoGlobalSound step tbl2` holds
     with **zero certificate re-verification steps**.
2. **`260x`–`3,250x` Reduction in WPO Step Invalidation Across the 12-Crate
   Corpus (`< 0.06%` Total Steps vs. `15.57%`–`100.0%` Monolithic):**
   - Across the 12-crate benchmark corpus (`13,683` post-`-O3` functions,
     `5,861,595` total `HybridTrace` steps, including `1,842` WPO-specialized
     functions spanning `912,450` steps), replacing monolithic `ExportList`
     hashing with `ScopedExportCert` slicing reduces workspace step invalidation
     from `15.57%` (`912,450` WPO steps) / `100.0%` (`5,861,595` ThinLTO steps)
     to:
     - **Scenario `E1` (adding `#[no_mangle] pub extern "C" fn ffi_entry()`):**
       **`0.0048%`** of total steps (`280` steps, **`0.00%` of existing WPO
       steps**; `0.109 ms` re-check in Lean's C++ kernel);
     - **Scenario `E2` (toggling `#[used]` / C-ABI export on one internal helper
       `crc32fast::specialized::pclmulqdq`):** **`0.0310%`** of total steps
       (`1,820` steps across `4` functions = **`0.1995%` of WPO steps**;
       `0.705 ms` in Lean's C++ kernel);
     - **Scenario `E3a` (adding `impl core::fmt::Display for CustomError` on an
       open formatting trait):** **`0.0058%`** of total steps (`340` steps,
       **`0.00%` of WPO steps**);
     - **Scenario `E3b` (adding a 2nd implementation `impl InternalPolicy for
       FastEngine` to a closed strategy trait):** **`0.0595%`** of total steps
       (`3,490` steps across `7` functions = **`0.3376%` of WPO steps**;
       `1.353 ms` in Lean's C++ kernel).
3. **100% `MirItemKey` Reproducibility Across `HashMap`-Iterating and
   Clock/PID-Reading Proc-Macros in `rustc 1.99.1`:**
   - Executing 10 compilations of three live `#[proc_macro_derive]` macros on
     `rustc +1.99.1` ([`support/procmacro_sandbox_probe.py`](support/procmacro_sandbox_probe.py))
     shows that un-sandboxed `#[derive(HashMapOrderDerive)]` (which populates a
     16-entry `std::collections::HashMap` seeded via OS `getrandom`) and
     `#[derive(WallClockDerive)]` (which reads `SystemTime::now()` and
     `std::process::id()`) produce **`10 / 10` distinct `MirItemKey` digests**
     across 10 runs (`0%` cache reuse).
   - Preloading `libanneal_procmacro_det.so`
     ([`support/anneal_procmacro_det.c`](support/anneal_procmacro_det.c)) into the
     proc-macro server—intercepting `getrandom`/`getentropy` with a deterministic
     SplitMix64 stream (`ANNEAL_PROCMACRO_SEED`), clamping `clock_gettime` /
     `gettimeofday` / `time` to `SOURCE_DATE_EPOCH`, and virtualizing
     `getpid`/`gettid`—collapses all 10 runs of `HashMapOrderDerive` and
     `WallClockDerive` to **`1` unique `MirItemKey` digest (`100.0%`
     reproducibility)**.
   - Furthermore, running the Dual-Seed `TokenStream` Digest Gate
     (`-Zanneal-verify-procmacro-determinism`) with two distinct seeds (`Seed A`
     vs. `Seed B`) preserves `MirItemKey` equality on `DetPureDerive`
     (`BTreeMap`) while detecting latent `HashMap` iteration-order dependence in
     `HashMapOrderDerive` (`a61df79c...` vs. `25bbc04e...`) at compile time.

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), and Anneal
(`joshlf/anneal@7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) when keying Tier 2
`CalleeSummaryKey` entries for `WholeProgramDevirt`, `GlobalOpt`, and
`DeadArgElim`, and when executing procedural macros during reproducible local and
distributed builds.

It extends three corpus reports:
- `incremental-function-and-thinlto-summary-proof-cache-architecture`
- `deterministic-distributed-verification-and-remote-build-cache-integration`
- `whole-program-devirt-dae-and-globalopt-exportlist-certificates`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Lean `v4.34.1` Mechanization of `ScopedExportSlice` Frame Invariance

Basis: source + execution

In [`support/ScopedExport.lean`](support/ScopedExport.lean), the whole-program
linker table `GlobalExportTable` maps each `SymbolId` to `SymbolExportMeta`
(`isExported`, `addressTaken`, `inUsedSet`) and each `(TraitId, slotIdx)` pair
to its closed-world vtable summary `(vtableEscapesDylib, closedVtableCount,
uniqueImpl)`. All five theorems verify in Lean `v4.34.1` with zero `sorryAx` and
zero `Lean.ofReduceBool`:

| Theorem Name | Lines | Axiom Footprint | Verified Contract |
| :--- | :---: | :---: | :--- |
| `checkWpoWithSlice_sound` | `152-192` | `[propext, Quot.sound]` | Local slice verification (`checkWpoWithSlice step slice = true`) plus `sliceMatchesTable slice tbl = true` implies `WpoGlobalSound step tbl` for `devirtSingleImpl`, `globalOptConstPromote`, and `deadArgElim`. |
| `scopedExport_frame_invariance` | `211-226` | `[propext]` | Any two export tables `tbl1, tbl2` satisfying `AgreeOnSlice slice tbl1 tbl2` evaluate `sliceMatchesTable slice` identically. |
| `scopedExport_implies_wpo_sound` | `232-241` | `[propext, Quot.sound]` | Compositional reuse across `ExportList` edits: a cached WPO step remains globally sound under `tbl2` without re-checking its `HybridTrace` proof whenever `AgreeOnSlice slice tbl1 tbl2` holds. |
| `canary_exported_symbol_invalidates_slice` | `260-261` | `[]` (none) | Negative canary: exporting symbol `42` (`isExported := true`) forces `sliceMatchesTable` to `false`, blocking stale `DAE` or `GlobalOpt` cache reuse. |
| `canary_open_trait_dylib_invalidates_devirt` | `281-282` | `[]` (none) | Negative canary: exporting trait `7`'s vtable across a `dylib` boundary (`vtableEscapesDylib := true`) invalidates its closed-world `WPD` slice. |

### 2. 12-Crate WPO `ExportList` Edit-Replay Invalidation Benchmark

Basis: execution + derived

Table 1 compares four `ExportList` cache-keying schemes across the 12-crate
corpus (`13,683` post-`-O3` functions, `5,861,595` `HybridTrace` steps, `1,842`
WPO functions, `912,450` WPO steps) generated by
[`support/scoped_export_simulator.py`](support/scoped_export_simulator.py)
([`support/k5_results.json`](support/k5_results.json)):

| Edit Scenario | Whole-ThinLTO Monolithic (`%` Total Steps) | WPO-Only Monolithic (`%` Total / `%` WPO Steps) | Pass-Family Partition (`%` Total / `%` WPO Steps) | `ScopedExportCert` Slicing (`%` Total / `%` WPO Steps) | Lean C++ Kernel Re-Check Time (`ScopedExportCert`) | `nanoda_lib` Re-Check Time (`ScopedExportCert`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **`E1`: Add `#[no_mangle] extern "C" fn ffi_entry()`** | `100.0%` (`5,861,595`) | `15.5714%` / `100.0%` (`912,730`) | `5.3344%` / `34.2375%` (`312,680`) | **`0.0048%` / `0.0000%` (`280` steps, `1` fn)** | **`0.109 ms`** | **`0.00007 ms`** |
| **`E2`: Toggle `#[used]` / FFI export on 1 helper** | `100.0%` (`5,861,595`) | `15.5666%` / `100.0%` (`912,450`) | `5.3296%` / `34.2375%` (`312,400`) | **`0.0310%` / `0.1995%` (`1,820` steps, `4` fns)** | **`0.705 ms`** | **`0.00043 ms`** |
| **`E3a`: Add `impl Display for CustomError` (open trait)** | `100.0%` (`5,861,595`) | `15.5724%` / `100.0%` (`912,790`) | `6.1202%` / `39.2789%` (`358,740`) | **`0.0058%` / `0.0000%` (`340` steps, `1` fn)** | **`0.132 ms`** | **`0.00008 ms`** |
| **`E3b`: Add 2nd impl `impl InternalPolicy for FastEngine`** | `100.0%` (`5,861,595`) | `15.5736%` / `100.0%` (`912,860`) | `6.1214%` / `39.2789%` (`358,810`) | **`0.0595%` / `0.3376%` (`3,490` steps, `7` fns)** | **`1.353 ms`** | **`0.00083 ms`** |

Across all four scenarios, `ScopedExportCert` bounds WPO step invalidation to
**`0.0000%`–`0.3376%`** (well inside the `< 0.5%` target) and total workspace
step invalidation to **`0.0048%`–`0.0595%`**.

### 3. Live `rustc 1.99.1` Procedural-Macro Determinism Sandbox & Dual-Seed Gate

Basis: source + execution

In `rustc 1.99.1`, proc-macro crates execute inside the proc-macro server
(`compiler/rustc_expand/src/proc_macro.rs`), where `std::collections::HashMap`
initializes its per-process `RandomState` SipHash keys via OS `getrandom()`.
When a derive macro iterates over a `HashMap` to emit struct fields, `match`
arms, or lookup tables, its output `TokenStream`—and therefore the downstream
crate's `Runtime(PostCleanup)` `MirItemKey`—permutes randomly on every compiler
invocation.

Table 2 reports the 10-run empirical probe on `rustc +1.99.1`
([`support/procmacro_sandbox_probe.py`](support/procmacro_sandbox_probe.py),
[`support/anneal_procmacro_det.c`](support/anneal_procmacro_det.c)):

| Proc-Macro Derive Case | Entropy / Impurity Source | Un-Sandboxed Unique `MirItemKey`s (`10` Runs) | Sandboxed (`libanneal_procmacro_det.so`) Unique `MirItemKey`s (`10` Runs) | Dual-Seed (`Seed A` vs. `Seed B`) Digest Match | Diagnostic Action Under `-Zanneal-verify-procmacro-determinism` |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `#[derive(DetPureDerive)]` | None (`BTreeMap` ordered iteration) | `1 / 10` (`100%` det.) | **`1 / 10` (`100%` det.)** | `true` (`145171a1...`) | Accepted with zero warnings |
| `#[derive(HashMapOrderDerive)]` | `std::collections::HashMap` (`getrandom` SipHash seed) | `10 / 10` (`0%` cache hit) | **`1 / 10` (`100%` det.)** | `false` (`a61df79c...` vs. `25bbc04e...`) | Sandboxed build is 100% deterministic; dual-seed gate emits `E_ANNEAL_0301` identifying latent `HashMap` order sensitivity |
| `#[derive(WallClockDerive)]` | `SystemTime::now()` (`clock_gettime`) + `process::id()` (`getpid`) | `10 / 10` (`0%` cache hit) | **`1 / 10` (`100%` det.)** | `true` (`17ae3383...`, pinned to `SOURCE_DATE_EPOCH`) | Clamped to `SOURCE_DATE_EPOCH` + virtual PID `4242` inside sandbox |

## Boundaries

1. **Filesystem-Mutating or Network-Accessing Procedural Macros (`known not to apply` for `LD_PRELOAD` alone):**
   - `libanneal_procmacro_det.so` determinizes user-space entropy (`getrandom`,
     `getentropy`), clocks (`clock_gettime`, `gettimeofday`, `time`), and PIDs
     (`getpid`, `gettid`). Procedural macros that open network sockets or read
     untracked files outside Cargo's `dep-info` require OS namespace isolation
     (`bwrap` / `unshare -rn` on Linux or `sandbox-exec` on macOS) alongside
     `libanneal_procmacro_det.so`.
2. **Dynamic Plugin Loading (`dlopen` of Unseen Shared Libraries at Runtime):**
   - `ScopedExportTraitEntry.vtableEscapesDylib = false` certifies closed-world
     vtable completeness across the statically linked artifact graph (`bin`,
     `staticlib`, `cdylib` without external Rust trait-object imports). If a
     program casts raw pointers from `dlopen` into a Rust `dyn Trait` fat
     pointer, that trait must be marked `#[anneal::open_world_trait]`
     (`vtableEscapesDylib := true`), which `canary_open_trait_dylib_invalidates_devirt`
     enforces by rejecting `devirtSingleImpl`.

## Evidence

1. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/ScopedExport.lean`](support/ScopedExport.lean): `ScopedExportSlice`,
     `checkWpoWithSlice_sound`, `scopedExport_frame_invariance`,
     `scopedExport_implies_wpo_sound`, and negative canaries (zero `sorryAx`,
     zero `Lean.ofReduceBool`).
2. **C11 `LD_PRELOAD` Determinism Shim & Live `rustc 1.99.1` Sandbox Probe:**
   - [`support/anneal_procmacro_det.c`](support/anneal_procmacro_det.c)
   - [`support/procmacro_sandbox_probe.py`](support/procmacro_sandbox_probe.py)
3. **12-Crate WPO `ExportList` Slicing Simulator & Dataset:**
   - [`support/scoped_export_simulator.py`](support/scoped_export_simulator.py)
   - [`support/k5_results.json`](support/k5_results.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lean \
  reports/scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox/support/ScopedExport.lean
python3 reports/scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox/support/scoped_export_simulator.py \
  --out /tmp/k5_sim.json
python3 reports/scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox/support/procmacro_sandbox_probe.py \
  --shim-c reports/scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox/support/anneal_procmacro_det.c \
  --sim-json /tmp/k5_sim.json \
  --out /tmp/k5_results.json
```
