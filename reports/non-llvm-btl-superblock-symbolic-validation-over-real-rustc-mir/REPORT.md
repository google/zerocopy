# Non-LLVM `CompCert BTL`-Style Superblock Optimization Replay and Symbolic Equivalence Validation over `66,438` Real `rustc 1.99.1` MIR Basic Blocks

## Summary

An earlier exploratory report in this corpus claimed `100.01%` oracle-replay
parity (`U2`) using a script that invoked LLVM's own `opt -passes=...` and
`llc -O3` with zero independent optimization or translation-validation code.
Meanwhile, our companion measurements established two sharp constraints on any
real verified `rustc` optimizer:

1. Neither debuginfo-free 1-WL CFG alignment (`10.37%` BB micro-recall across
   `-O0 -> -O3`) nor standard `-O3` DWARF (`48.86%` PC-byte coverage, `44.43%`
   zero-coverage locals) can reconstruct optimization provenance post-hoc.
2. Live kernel reflection (`486` steps/s in Lean `4.35.0`, `1,219` steps/s in
   `nanoda_bin 0.4.19`) is three orders of magnitude too slow for workspace MIR
   volumes (`1.64M` post-`-O3` LLVM instructions across `109` crates).

This report replaces the refuted LLVM proxy with a **genuine, zero-LLVM,
compiled Rust `CompCert BTL`-style superblock optimizer and independent
hash-consed symbolic equivalence validator** (`support/e2_1_real_btl_replay.rs`,
`support/e2_1b_real_ebb_superblocks.rs`, `support/e2_1c_real_memver_ebb_btl.rs`)
evaluated across **`20,025` real `rustc 1.99.1` MIR functions (`66,438` real
basic blocks)** spanning `zerocopy` (`Runtime(PostCleanup)` and `Optimized`),
`libcore`, `anneal-audit`, and `cargo-anneal` (`[real measurement]`):

- **Three-Tier Coverage Ablation Proves Why Pure Single-BB Scalar Validation
  Stalls — and How Conservative `mem_ver` + `SwitchInt` EBB Chaining Reaches
  `96.97%` Coverage** `[real measurement]`:
  - **Tier 1 (Pure Scalar, Single-BB, No `Call`):** Admits only **`36.74%`**
    (`19,892 / 54,140` BBs, `2.04M` MIR stmts/s), because `term_opaque_call`
    (`8,768` BBs) and `deref_or_index_mem` (`6,740` BBs) dominate real Rust MIR.
  - **Tier 2 (+ `Call` as CompCert-BTL Block-Ending Barrier):** Lifts admission
    to **`54.79%`** (`36,404 / 66,438` BBs; `63.01%` on `zerocopy`
    `Runtime(PostCleanup)` vs. `46.80%` on `Optimized`) at **`3.60M` MIR
    stmts/s** (`20.98 ms`), yet yields **`0` GVN hits and `0` eliminated bounds
    checks** because real Rust MIR shatters code into **`2.07`-statement basic
    blocks** and only `7` multi-BB chains form without memory modeling.
  - **Tier 3 (+ Conservative `mem_ver` Versioning + `SwitchInt`/`Assert` EBB
    Superblock Chaining):** Lifts real-MIR admission to **`96.97%` (`64,425 /
    66,438` BBs; `99.85%` on `zerocopy` `Runtime(PostCleanup)`)**, chains
    **`6,168` multi-BB EBB superblocks (up to `13` consecutive basic blocks)**,
    executes genuine non-LLVM optimizations (`20,207` field-granular certified
    `MoveToCopy`, `8,179` copy propagations, `28` pure + `9` same-`mem_ver`
    memory-read GVN hits, **`59` path-guarded redundant `Assert` / bounds
    checks eliminated**, `7,633` dead temporaries eliminated), and
    independently validates **`57,021 / 57,021` (`100.0%`, `0` failures)**
    superblocks in **`112.84 ms`** (**`2.17 million` MIR ops/sec**, `1.98 µs`
    per superblock)!
- **Soundness Verified Against `7 / 7` (`100%`) Planted Adversarial Optimizer
  Bugs** `[real measurement]`: Injecting real unsound bugs into the optimizer —
  dropping an unproved bounds check, swapping `M4` `(copy _1, move _1)` order,
  unguarded `MoveToCopy` erasing use-after-move UB, local-granular deinit
  breaking `M3` sibling field moves, unsound `(x & 255) < 200` BCE, deleting a
  live-out write, and unsound memory-load CSE across an intervening store — is
  rejected **`7 / 7`** by the independent symbolic validator.
- **Orders-of-Magnitude Validation Headroom Over Kernel Reflection**
  `[real measurement]`: At **`2.17M–3.60M` MIR ops/sec** in safe compiled
  Rust, native BTL symbolic validation is **`1,777x–2,951x` faster than
  `nanoda_bin 0.4.19`** (`1,219` steps/s) and **`4,454x–7,400x` faster than
  `Lean 4.35.0` kernel `rfl`** (`486` steps/s). Applying our measured pure-total
  compiled Lean ratio (`2.18x–3.36x` of Rust `-O3`), a **proved-once
  Lean-extracted pure-total BTL validator** projects to **`~0.65M–1.65M` MIR
  ops/sec** (`~150–380 ms` for `244K` ops) `[conjecture]`.

## Applicability

This progressive benchmark validates the **compile-time translation-validation
architecture** for a verified drop-in `rustc` (specifically replacing post-hoc
whole-pipeline LLVM alignment with pass-local `CompCert BTL` superblock
validation):

- **Where this architecture directly applies:** Intra-function MIR / `MiniSSA`
  optimization passes running after `Runtime(PostCleanup)` with compiler-internal
  `OriginTag` provenance, field-granular `deinitMovedPlace = true` semantics
  (matching `joshlf/anneal`'s `Trusted.MirSemantics.lean` + `F1-1`), and
  conservative store-versioned memory barriers (`mem_ver`).
- **What it proves about `Runtime(PostCleanup)` vs. `Optimized` MIR:** Pure
  scalar+`CallBarrier` admission is `+16.21` percentage points higher on
  `zerocopy`'s `Runtime(PostCleanup)` MIR (`63.01%`) than on `Optimized` MIR
  (`46.80%`), and Tier 3 reaches `99.85%` (`12,280 / 12,298` BBs) on
  `PostCleanup`, confirming `Runtime(PostCleanup)` as the right verified
  optimizer entry point.

## Findings

### 1. Three-Tier Progressive Ablation Across `66,438` Real `rustc 1.99.1` Basic Blocks

All three tiers execute strictly in compiled Rust (`rustc 1.99.1 -C
opt-level=3`, zero LLVM `opt`/`llc` calls) over real emitted `.mir` files from
`rustc 1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`)
(`[real measurement]`):

| Validator Tier | Real MIR Corpora | Admitted BBs | Admission Rate | Multi-BB Superblocks (Max Chain) | Moves Demoted | Copy Prop | GVN (Pure / Mem) | Path BCE Elim | Dead Ops Elim | Validated OK / Fail | Val Time (ms) | Throughput (ops/sec) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Tier 1:** Pure Scalar Single-BB (no `Call`) | `4` `Optimized` (`54,140` BBs) | `19,892` | `36.74%` | `0` (`1`) | `1,753` | `1,175` | `0 / 0` | `0` | `1,015` | `19,892 / 0` | `17.84` | `2,036,801` |
| **Tier 2:** Pure Scalar + `CallBarrier` (single-BB / Goto-Assert EBB) | `5` (`PostCleanup` + `4` `Opt`, `66,438` BBs) | `36,404` | `54.79%` | `7` (`2`) | `2,222` | `1,703` | `0 / 0` | `0` | `1,533` | `36,404 / 0` | `20.98` | **`3,597,310`** |
| **Tier 3:** Conservative `mem_ver` + `SwitchInt`/`Assert` EBBs | `5` (`PostCleanup` + `4` `Opt`, `66,438` BBs) | **`64,425`** | **`96.97%`** | **`6,168` (`13`)** | **`20,207`** | **`8,179`** | **`28 / 9`** | **`59`** | **`7,633`** | **`57,021 / 0`** | **`112.84`** | **`2,165,679`** |

*(Note: Tier 1 also executed `80` constant folds in `core.mir`. Tier 3 ran over
`244,383` total MIR ops -> `236,691` ops (`-3.15%` net statement count) with
`125.59 ms` total optimization time and `112.84 ms` independent validation
time.)*

### 2. Per-Corpus Breakdown (Tier 3 Conservative `mem_ver` + `SwitchInt` EBBs)

| Corpus (`rustc 1.99.1` `.mir`) | Total BBs | Admitted BBs | Admitted % | EBB Superblocks | Multi-BB Chains (Max) | Ops Before -> After | Moves Demoted | Copy Prop | GVN (Pure/Mem) | Path BCE Elim | Dead Elim | Val Time (ms) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `zerocopy_postcleanup.mir` (`4,427` fns) | `12,298` | `12,280` | **`99.85%`** | `11,746` | `519` (`4`) | `38,779 -> 38,393` | `1,287` | `216` | `0 / 0` | `0` | `386` | `15.91` |
| `core.mir` (`10,948` fns) | `39,711` | `38,233` | **`96.28%`** | `32,733` | **`4,355` (`13`)** | `159,109 -> 152,537` | `15,952` | `7,188` | `15 / 8` | **`57`** | `6,515` | `73.77` |
| `zerocopy.mir` (`4,561` fns) | `13,693` | `13,240` | **`96.69%`** | `11,898` | `1,266` (`4`) | `42,913 -> 42,218` | `2,710` | `734` | `1 / 1` | **`2`** | `693` | `21.24` |
| `anneal_audit.mir` (`23` fns) | `430` | `395` | `91.86%` | `382` | `13` (`2`) | `1,967 -> 1,963` | `141` | `4` | `4 / 0` | `0` | `4` | `1.06` |
| `cargo_anneal.mir` (`66` fns) | `306` | `277` | `90.52%` | `262` | `15` (`2`) | `1,615 -> 1,580` | `117` | `37` | `8 / 0` | `0` | `35` | `0.86` |

### 3. Explicit Fail-Closed Bailout Taxonomy (Why Real MIR Needs Tier 3)

Comparing Tier 1 (`34,248` bailed-out BBs) to Tier 3 (`2,013` bailed-out BBs)
quantifies exactly which MIR features drive real-world coverage
(`[real measurement]`):

- **Tier 1 Top Bailouts (`34,248` BBs excluded):** `term_opaque_call` (`8,768`,
  `25.6%`), `deref_or_index_mem` (`6,740`, `19.7%`), `aggregate_or_adt_ctor`
  (`4,057`, `11.8%`), `complex_const_or_generic` (`3,982`, `11.6%`),
  `transmute_or_ptr_cast` (`2,977`, `8.7%`), `other_cast` (`2,669`, `7.8%`),
  `metadata_or_discr` (`1,482`, `4.3%`), `checked_or_unchecked_arith` (`1,255`,
  `3.7%`).
- **Tier 3 Remaining Bailouts (`2,013` BBs = `3.03%` excluded):**
  `unparsed_stmt` (`982` — e.g., rare `FakeRead`/`AscribeUserType`/multiline
  MIR syntax), `switch_complex_discr` (`779` — projected/deref switch
  discriminants), `term_drop` (`180` — `drop(...)` terminators), and
  `other_term` (`72` — `resume`/`unwind`/inline `asm!`).
- **Why Single-BB Validation Yields `0` GVN and `0` BCE:** Real `rustc` MIR
  splits code at every `assert`, `switchInt`, and `Call`, leaving an average of
  only **`2.07` statements per admitted Tier 2 basic block**. Only after
  admitting conservative `mem_ver` memory reads/stores AND chaining
  `SwitchInt -> Assert` unique-predecessor paths (forming `6,168` multi-BB
  superblocks up to `13` BBs deep) did cross-block GVN (`37` hits) and
  path-guarded BCE (`59` redundant `Assert`s eliminated across `core.mir` and
  `zerocopy.mir`) unlock.

### 4. Seven Adversarial Bug-Injection Negative Controls (`7 / 7` Rejected)

| Control ID | Planted Unsound Optimizer Bug | Validator Verdict | Exact Rejection Diagnostic |
| :--- | :--- | :--- | :--- |
| `BUG-1` | Drop unproved `Assert(Lt(_1, _2))` -> `Goto` | **REJECTED** | `terminator mismatch: src=Assert(2, true, "oob", 1) opt=Goto(1)` |
| `BUG-2` | Swap `M4` operand order `(copy _1, move _1)` -> `(move _1, copy _1)` | **REJECTED** | `move_ub mismatch: src=false opt=true` |
| `BUG-3` | Unguarded `MoveToCopy` erasing real use-after-move UB | **REJECTED** | `move_ub mismatch: src=true opt=false` |
| `BUG-4` | Local-granular `deinit` corrupting `M3` sibling field moves | **REJECTED** | `field_granular_ub=false local_granular_ub=true` |
| `BUG-5` | Unsound bitwise BCE `(x & 255) < 200` -> `Goto` (`255 >= 200`) | **REJECTED** | `terminator mismatch: src=Assert(5, true, "oob", 1) opt=Goto(1)` |
| `BUG-6` | Delete live-out write `_0 = Add(_1, 1)` | **REJECTED** | `live_out symbolic state mismatch` |
| `BUG-7` | Unsound memory-load CSE `(*_1)` across intervening store `(*_1) = 99` | **REJECTED** | `mem_ver` increment (`0 -> 1`) rejects `live_out` mismatch |

## Boundaries

- **MIR-to-MIR Superblock Validator Only (Not Full Machine Codegen):** This
  artifact builds and measures a genuine non-LLVM MIR-to-MIR superblock
  optimizer and independent symbolic validator. It does **not** perform
  instruction selection, register allocation, or x86-64/AArch64 machine-code
  emission, and makes zero claims of runtime parity with LLVM `-O3`.
- **Prototype Validator Implemented in Rust (Not Yet Extracted from Lean 4):**
  The symbolic equivalence validator here is an unverified Rust implementation
  (`~450` LOC of validation logic) serving as an empirical coverage,
  optimization-yield, and native-throughput probe. Mechanizing its soundness
  theorem against `Trusted.MirSemantics` and compiling it from pure-total Lean
  4 (expected `2.18x–3.36x` overhead per our companion measurement) is the
  target of subsequent formalization stages.
- **Conservative `mem_ver` Aliasing & Pretty-Printed `.mir` Input:** Tier 3
  treats every memory store (`MemStore`) as an opaque barrier incrementing
  `mem_ver` (preventing false alias CSE, at the cost of missing store-to-load
  forwarding across disjoint fields — which requires `F1-2`-style Tree Borrows
  / `PartialSROA` witnesses). Parsing human-readable `rustc --emit=mir` text
  rather than `rustc_middle::mir::Body` accounts for the `982` `unparsed_stmt`
  bailouts.

## Evidence

All source code and measured JSON outputs are included under `support/`:

- `support/e2_1_real_btl_replay.rs`: Standalone Rust Tier 1 + Tier 2 pure
  scalar + `CallBarrier` non-LLVM optimizer, symbolic validator, and `BUG-1..6`
  negative controls.
- `support/e2_1b_real_ebb_superblocks.rs`: Standalone Rust Tier 2 multi-BB
  `Goto`/`Assert` EBB chaining experiment.
- `support/e2_1c_real_memver_ebb_btl.rs`: Standalone Rust Tier 3 conservative
  `mem_ver` + `SwitchInt`/`Assert` EBB superblock optimizer, symbolic
  validator, and `BUG-7` store-barrier negative control.
- `support/e2_1_real_btl_replay.json`, `support/e2_1b_real_ebb_superblocks.json`,
  `support/e2_1c_real_memver_ebb_btl.json`: Exact measured counts, bailout
  taxonomies, negative-control receipts, and wall-clock timings.
- Related ground-truth reports in this corpus:
  - `field-granular-deinit-move-mir-to-minissa-bisimulation-and-vc-transport`
  - `rustc-release-abi-drift-binary-validation-cfg-alignment-and-surviving-bounds-checks`
  - `lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`
  - `lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb`

## Revalidation

Compile and run against any fresh `rustc` `--emit=mir` or `-Z dump-mir` corpus:

```bash
rustc +1.99.1 -C opt-level=3 support/e2_1_real_btl_replay.rs -o /tmp/btl_t2
rustc +1.99.1 -C opt-level=3 support/e2_1c_real_memver_ebb_btl.rs -o /tmp/btl_t3
/tmp/btl_t2 /path/to/core.mir /path/to/zerocopy.mir
/tmp/btl_t3 /path/to/zerocopy_postcleanup.mir /path/to/core.mir /path/to/zerocopy.mir
```

Confirm `validated_fail == 0`, `7/7` negative controls rejected, and track
`admitted_pct`, `multi_bb` superblock counts, and `val_ops_per_sec` as new MIR
lowering features (e.g., `Drop` terminators and store-forwarding witnesses) are
added.
