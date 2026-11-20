# Real-Kernel `Anneal.MirWp` Proof Scaling Across MIR Normalization Regimes and Transport-Checker Overhead

## Summary

Prior corpus reports claimed that normalizing `Runtime(PostCleanup)` MIR to a
canonical SSA form yields `10.79×` weakest-precondition AST compression, `6.19×`
proof-line reduction, and `10.68×` Lean `v4.34.1` checking speedup on
straight-line Anneal obligations
(`anneal-spec-minissa-normalization-and-proof-compression`), and `13.61×` AST
compression with `15.48×` checking speedup on loop obligations
(`loop-invariant-and-recursive-spec-minissa-vc-transport`). Forensic inspection
(`google/zerocopy@0afd1cbbdb7d8947f9b3a44dc0fccaab3e688689`) refuted both sets
of numbers because their benchmark scripts hardcoded every timing and AST metric
without invoking Lean on `Trusted.MirSemantics`, and the loop benchmark replaced
operational loop execution with a closed-form multiplication.

This report replaces those refuted projections with **`64` synchronous,
real-kernel Lean `v4.34.1`**
(`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
`-DElab.async=false -Ddebug.skipKernelTC=false`, default `maxRecDepth = 512`
without `set_option` overrides, `3`-run medians) measurements directly over
unmodified **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`**
(`Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`) and the published
direct transport checker **`VrustcFormal.F1_1b`**
(`google/zerocopy@6e24ad128d7f29afc0f47733eb42ec4d3392ba63`,
`reports/anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/support/AnnealTrustedMirMoveToCopyStorage.lean`).
Across four MIR normalization regimes (`R0_RawPostCleanup`, `R1_F1_1b_Nop`,
`R2_StorageDeleted`, `R3_MinLocalCompact`) and four benchmark suites (`A`–`D`),
the measurements establish five architectural results:

1. **Concrete `RunsFrom` (`rfl`) Hits an Invariant `maxRecDepth = 512` Cliff at
   `K = 14 → 16` Across All Four Regimes (`[real measurement]`):** Even under
   maximal normalization (`R3_MinLocalCompact`: `2` locals, `16` statements,
   `fuel = 18`), concrete `rfl` execution of `Anneal.MirWp.RunsFrom` fails with
   `maximum recursion depth has been reached` at `K = 16` `u32` additions, the
   exact same `K` cliff as raw `PostCleanup` MIR (`R0`: `18` locals, `49`
   statements, `fuel = 51`). At `K = 14`, `R0 → R3` improves wall time by
   `1.58×` (`0.9206 s → 0.5845 s`) and `.olean` size by `1.90×`, while
   `R0 → R1` inflates the unfolded proof tree `2,700×`
   (`1.456 × 10²³ → 3.931 × 10²⁶` nodes). Because `TrustedBoundary.lean` forbids
   `set_option`, concrete `RunsFrom` `rfl` proofs cannot scale past tiny
   arithmetic blocks regardless of MIR normalization.
2. **`.nop`-Preserving Lowering (`R1_F1_1b_Nop`) Makes Symbolic `Executes`
   Proofs *Slower* (`0.85×` at `K = 32`) and Crashes at `K = 64`
   (`[real measurement]`):** On universally quantified symbolic proofs
   (`∀ x : BitVec 128`) over `Anneal.MirWp.Executes`, applying `MoveToCopy` plus
   1-to-1 `StorageLive`/`StorageDead ↦ .nop` replacement alone (`R1`) is
   **`18.0%` slower** than raw `PostCleanup` MIR (`R0`) at `K = 32`
   (`4.0246 s` vs. `3.4099 s`, peak RSS `324.00 MB` vs. `308.00 MB`), and
   **grows** the unfolded kernel proof tree (`517,943 → 579,377` nodes, `+11.9%`)
   even though the shared proof DAG shrinks (`5,100 → 3,753`). Because `.nop`
   still consumes an `Executes.next` step and removing `.move`/`StorageDead`
   leaves dead `BitVec 128` scalar terms live inside `List LocalSlot` across all
   remaining steps, both `R0` and `R1` crash with `maxRecDepth = 512` at
   `K = 64` (`9.75 s / 488.79 MB` and `13.98 s / 671.00 MB`).
3. **True Proof Scaling Requires Both Statement Deletion (`R2`) and Dead-Local
   Compaction (`R3`) (`[real measurement]`):** Deleting storage markers and
   `.nop` statements (`R2_StorageDeleted`) delivers a **`1.92×`** wall speedup at
   `K = 32` (`3.4099 s → 1.7806 s`) and **survives `K = 64`** (`5.8278 s`,
   `377.96 MB` RSS). Compacting dead temporary locals from `K + 2` down to `2`
   (`R3_MinLocalCompact`) adds another **`2.50×`** at `K = 32`—for a combined
   **`4.78×`** wall speedup (`3.4099 s → 0.7127 s`), **`1.72×`** lower peak RSS
   (`308.00 → 179.24 MB`), **`2.71×`** smaller `.olean`
   (`238,176 → 87,832 B`), **`1.68×`** fewer proof LOC (`324 → 193`),
   **`2.30×`** smaller kernel proof DAG (`5,100 → 2,218`), and **`2.28×`**
   smaller unfolded tree (`517,943 → 227,077`). At `K = 64`, `R3` finishes in
   **`1.3906 s`** (`4.19×` faster than `R2`, `195.70 MB` RSS).
4. **Authentic Symbolic Loop Verification (`sum_loop`, `∀ n : Nat`) Yields
   `1.34×` Wall Speedup—Refuting the Prior `15.48×` Claim
   (`[real measurement]`):** Across a genuine `3`-block CFG loop proved by
   structural induction over `Executes`, `R0 → R3` yields **`1.34×`** wall
   speedup (`0.6205 s → 0.4645 s`), **`1.12×`** fewer LOC (`130 → 116`),
   **`1.33×`** smaller proof DAG (`932 → 700`), and **`1.78×`** smaller unfolded
   tree (`15,229 → 8,571`). Furthermore, `R1` and `R2` force generalizing two
   dead-temporary parameters `(v3 v4 : Option Val)` in the loop invariant
   because `StorageDead` no longer resets temporaries to `.dead` at latch exit.
5. **Naive `O(S × L)` Kernel `rfl` Checking Breaks Net Speedup Even Against
   `R3` (`[real measurement]` + `[derived]`):** Checking `VrustcFormal.F1_1b`'s
   `isMoveToCopyProgram`, `checkNoUseAfterMoveProgram`,
   `isRemoveStorageMarkersProgram`, and `checkStorageSafeProgram` by `rfl`
   produces a constant `366`-node `bench_thm` proof DAG (`1,167`-node tree), but
   its kernel reduction time grows superlinearly as `O(S × L)` across `K = 4..32`
   (`0.5321 s → 0.6832 s → 1.1960 s → 2.8819 s`). End-to-end `R0 → R1` transport
   is strictly net-slower at every `K` (**`6.9065 s` vs. `3.4099 s` = `2.03×`
   slower at `K = 32`**). Even paired counterfactually with `R3`'s `4.78×` proof
   savings (`-2.6972 s`), a `2.8819 s` `O(S × L)` `rfl` checker still totals
   `3.5946 s` (`1.05×` slower than direct `R0`). A net-positive normalization
   bridge must combine **statement deletion + dead-local compaction (`R0 → R3`)**
   with an **`O(S)` indexed or externally-checked certificate validator**.

---

## Applicability

### Subjects, Toolchain, and Configuration

All measurements were acquired on `2026-11-20` (`2026-11-20T21:33:37Z`, total
wall time `187.44 s`) on a single `x86_64-unknown-linux-gnu` host using
synchronous Lean compilation (`-DElab.async=false -Ddebug.skipKernelTC=false`,
default `maxRecDepth = 512`, `0` `set_option` overrides, `3` cold-`.olean` runs
per benchmark configuration reporting median wall time and `/usr/bin/time -v`
peak RSS):

- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`** (`[published source]`):
  Supplies unmodified `Trusted/MirAst.lean` (`40,381 B`),
  `Trusted/MirSemantics.lean` (`111,865 B`, `List LocalSlot` state with
  `deinitMovedPlace = true` and `O(L)` `getElem?`/`setElem?`),
  `theory/Anneal/MirWp.lean` (`115,247 B`, defining `RunsFrom`, `Executes`,
  `mkState`, `bodyProg`, `wellFormed_and_spec_of_wp`), and
  `trusted/audit/TrustedBoundary.lean` (`117,602 B`, excluding `set_option` from
  `allowedCommandKinds`).
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`,
  `x86_64-unknown-linux-gnu`, Release)** (`[real measurement]`): Executes all
  `64` benchmark configurations, one-time helper/bridge module builds, and the
  single-process `BatchInspect.lean` kernel `Expr` DAG/tree counter.
- **`google/zerocopy@6e24ad128d7f29afc0f47733eb42ec4d3392ba63`**
  (`reports/anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/support/AnnealTrustedMirMoveToCopyStorage.lean`,
  `6,489` lines, `275,460 B`, SHA-256
  `79d0c63cfe045233d1dcc491529b585981c7afe715bb876f52d314d0a7c91a5c`,
  `[real measurement]`): Directly compiled and imported in Suite D to measure
  real `VrustcFormal.F1_1b` `rfl` checking and bidirectional VC transport
  overhead.

### Relationship to Prior Corpus Reports

- **Replaces refuted quantitative claims** in
  `anneal-spec-minissa-normalization-and-proof-compression` (`10.79×` WP AST /
  `6.19×` LOC / `10.68×` elab) and
  `loop-invariant-and-recursive-spec-minissa-vc-transport` (`13.61×` AST /
  `15.48×` elab), whose epistemic audit errata were recorded at
  `google/zerocopy@0afd1cbbdb7d8947f9b3a44dc0fccaab3e688689`.
- **Directly benchmarks the open scaling boundary** flagged in Section 6 and
  Boundary 6 of
  `anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge`
  (`VrustcFormal.F1_1b` `List`-based `getElem?`/`setElem?` and
  `hasStorageAnnotation` kernel reduction cost).
- **Composes with**
  `lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`,
  which independently established Lean 4's `~290–590` real SSA steps/s kernel
  `rfl` ceiling and `2.18×–3.36×` pure-total native checker parity with Rust.

### Scope of Generalization

Exact wall times, `.olean` byte sizes, and `maxRecDepth = 512` cliffs apply to
synthetic single-block `u32` addition chains (`K = 2..64`) and a `3`-block
`sum_loop` CFG under `Trusted.MirSemantics@c131b320e` (value-only, single-frame,
unprojected `List LocalSlot`, no heap/pointers/calls). The qualitative scaling
mechanisms—`O(S × L)` `List LocalSlot` traversal, dead-value retention when
`.move`/`StorageDead` are replaced by `.copy`/`.nop`, and `maxRecDepth`
sensitivity to linear `List` indexing and nested concrete `evalBinOp`—generalize
to any `Anneal.MirWp` proof over the `List`-based v1 `MirSemantics`
representation, while exact speedup ratios will differ for multi-block control
flow, memory/pointer loads, or `Array`/balanced-tree state representations (see
`## Boundaries`).

---

## Findings

### 1. Experimental Matrix: Four MIR Normalization Regimes (`R0`–`R3`) and Base Compilation Costs

`Basis: source + execution (support/e2_8_real_anneal_mirwp_scaling.py, support/e2_8_real_anneal_mirwp_scaling.json; [real measurement])`

To isolate the separate effects of (i) `MoveToCopy` + `.nop`-preserving
`RemoveStorageMarkers`, (ii) statement deletion, and (iii) dead-local
compaction, every benchmark family compiles four semantically equivalent
`Trusted.MirAst.Body` representations directly against unmodified
`Trusted.MirSemantics` (`MirSemantics.lean:650–661, 687–790, 949–976, 1370–1405`)
and `Anneal.MirWp` (`MirWp.lean:1640, 1978, 2013–2035`):

| Regime | Exact Transformation Applied | Straight-Line Chain (`K` stages) | `sum_loop` (`bb1` latch) | Entry Slot State (`mkState 0 0`) |
| :--- | :--- | :--- | :--- | :--- |
| **`R0_RawPostCleanup`** | Unmodified `Runtime(PostCleanup)` MIR shape: per-temporary `StorageLive`, `.move` reads (`deinitMovedPlace = true`), `StorageDead` after last use. | `L = K + 2`, `S = 3K + 1`, `fuel = 3K + 3` | `L = 5`, `S_latch = 8` | `_0: .live none`, params `.live (some _)`, temps `.dead` |
| **`R1_F1_1b_Nop`** | Exact `VrustcFormal.F1_1b` output: `.move ↦ .copy` and `StorageLive`/`StorageDead ↦ .nop` 1-to-1. Same `L` and `S`. | `L = K + 2`, `S = 3K + 1`, `fuel = 3K + 3` | `L = 5`, `S_latch = 8` | `_0: .live none`, params `.live (some _)`, temps `.live none` (or `.live v3, .live v4` in loop invariant) |
| **`R2_StorageDeleted`** | All `StorageLive`/`StorageDead`/`.nop` statements deleted (`SimplifyCfg`-style), `.move ↦ .copy`, dead local slots retained. | `L = K + 2`, `S = K + 1`, `fuel = K + 3` | `L = 5`, `S_latch = 4` | Same all-live entry state as `R1` |
| **`R3_MinLocalCompact`** | Dead temporary locals compacted away and storage markers eliminated; in-place updates on minimal live locals. | `L = 2`, `S = K`, `fuel = K + 2` | `L = 3`, `S_latch = 2` | Only `_0` + arguments (`2` locals in chain; `3` in `sum_loop`), valid under standard `initState` |

**One-Time Shared Module Compilation Costs (`[real measurement]`):**

- **`E28Helpers.lean`** (`421` LOC; reusable symbolic stepping lemmas
  `evalStep_assign_{add,sub,use}_{copy,move}`, `evalStep_switch_u32_*`,
  `evalStep_return_u32` over `Trusted.MirSemantics`): **`1.5756 s`**,
  `185.39 MB` peak RSS, `432,928 B` `.olean`, `rc = 0`.
- **`F1_1b_Mod.lean`** (verbatim copy of published
  `AnnealTrustedMirMoveToCopyStorage.lean`, `6,489` LOC, `VrustcFormal.F1_1b`):
  **`16.4345 s`**, `569.20 MB` peak RSS, `11,353,400 B` `.olean`, `rc = 0`.

Kernel `Expr` sizes were measured in a single `BatchInspect.lean` invocation
over all `58` passing theorem `.olean`s, computing both **DAG nodes** (unique
`Expr` subterms in a `Std.HashMap`) and **unfolded tree nodes** (memoized total
node count without sharing).

---

### 2. Suite A: Concrete `RunsFrom` (`rfl`) Scaling and the Universal `K = 14 → 16` `maxRecDepth` Cliff

`Basis: execution (support/e2_8_real_anneal_mirwp_scaling.json, suite_a_concrete_runs; [real measurement]) + derived`

Suite A proves `RunsFrom bodyBench fuel (mkState 0 0 init_concrete) (u32Val expected) := rfl`
for concrete input `x = 7u32` and `K ∈ {2, 4, 6, 8, 10, 12, 14, 16}` (`32` total
configurations). Because `TrustedBoundary.lean` (`L447–490, 962`) forbids
`set_option`, Lean runs with its fixed default `maxRecDepth = 512`.

| `K` | Regime | `L` | `S` | Fuel | `rc` | Median Wall (s) | RSS (MB) | `.olean` (B) | LOC | Proof DAG | Unfolded Proof Tree |
| :-: | :--- | :-: | :-: | :-: | :-: | ---: | ---: | ---: | :-: | ---: | ---: |
| `2` | `R0_RawPostCleanup` | `4` | `7` | `9` | `0` | `0.3146` | `171.04` | `25,400` | `35` | `275` | `607,153` |
| `2` | `R1_F1_1b_Nop` | `4` | `7` | `9` | `0` | `0.3800` | `171.04` | `24,360` | `35` | `260` | `1,397,709` |
| `2` | `R2_StorageDeleted` | `4` | `3` | `5` | `0` | `0.3133` | `167.02` | `22,080` | `31` | `199` | `15,211` |
| `2` | `R3_MinLocalCompact` | `2` | `2` | `4` | `0` | `0.3181` | `167.00` | `20,656` | `30` | `177` | `3,945` |
| `4` | `R0_RawPostCleanup` | `6` | `13` | `15` | `0` | `0.4189` | `171.05` | `32,040` | `41` | `440` | `491,715,681` |
| `4` | `R1_F1_1b_Nop` | `6` | `13` | `15` | `0` | `0.3662` | `173.05` | `30,168` | `41` | `407` | `3,686,475,991` |
| `4` | `R2_StorageDeleted` | `6` | `5` | `7` | `0` | `0.3651` | `171.03` | `25,704` | `33` | `286` | `301,299` |
| `4` | `R3_MinLocalCompact` | `2` | `4` | `6` | `0` | `0.3116` | `171.04` | `23,552` | `32` | `253` | `73,225` |
| `6` | `R0_RawPostCleanup` | `8` | `19` | `21` | `0` | `0.4660` | `176.96` | `38,992` | `47` | `617` | `3.899 × 10¹¹` |
| `6` | `R1_F1_1b_Nop` | `8` | `19` | `21` | `0` | `0.4828` | `173.08` | `36,032` | `47` | `558` | `9.585 × 10¹²` |
| `6` | `R2_StorageDeleted` | `8` | `7` | `9` | `0` | `0.5256` | `174.81` | `29,656` | `35` | `377` | `5,273,407` |
| `6` | `R3_MinLocalCompact` | `2` | `6` | `8` | `0` | `0.5484` | `170.91` | `26,448` | `34` | `329` | `1,250,345` |
| `8` | `R0_RawPostCleanup` | `10` | `25` | `27` | `0` | `0.6195` | `175.13` | `46,304` | `53` | `801` | `3.071 × 10¹⁴` |
| `8` | `R1_F1_1b_Nop` | `10` | `25` | `27` | `0` | `0.5192` | `177.62` | `42,000` | `53` | `708` | `2.460 × 10¹⁶` |
| `8` | `R2_StorageDeleted` | `10` | `9` | `11` | `0` | `0.5838` | `173.07` | `33,576` | `37` | `467` | `87,772,303` |
| `8` | `R3_MinLocalCompact` | `2` | `8` | `10` | `0` | `0.5827` | `175.06` | `29,176` | `36` | `400` | `20,697,225` |
| `10` | `R0_RawPostCleanup` | `12` | `31` | `33` | `0` | `0.6087` | `183.17` | `54,096` | `59` | `1,002` | `2.406 × 10¹⁷` |
| `10` | `R1_F1_1b_Nop` | `12` | `31` | `33` | `0` | `0.5615` | `179.57` | `48,192` | `59` | `867` | `6.246 × 10¹⁹` |
| `10` | `R2_StorageDeleted` | `12` | `11` | `13` | `0` | `0.5379` | `177.05` | `37,720` | `39` | `566` | `1,428,755,619` |
| `10` | `R3_MinLocalCompact` | `2` | `10` | `12` | `0` | `0.4105` | `173.06` | `32,072` | `38` | `476` | `337,359,145` |
| `12` | `R0_RawPostCleanup` | `14` | `37` | `39` | `0` | `0.7186` | `189.02` | `63,360` | `65` | `1,215` | `1.875 × 10²⁰` |
| `12` | `R1_F1_1b_Nop` | `14` | `37` | `39` | `0` | `0.6708` | `183.02` | `55,440` | `65` | `1,030` | `1.573 × 10²³` |
| `12` | `R2_StorageDeleted` | `14` | `13` | `15` | `0` | `0.5219` | `175.05` | `41,992` | `41` | `669` | `23,023,902,523` |
| `12` | `R3_MinLocalCompact` | `2` | `12` | `14` | `0` | `0.4765` | `175.04` | `34,968` | `40` | `552` | `5,453,551,625` |
| **`14`** | **`R0_RawPostCleanup`** | `16` | `43` | `45` | **`0`** | **`0.9206`** | `193.04` | `71,920` | `71` | `1,440` | `1.456 × 10²³` |
| **`14`** | **`R1_F1_1b_Nop`** | `16` | `43` | `45` | **`0`** | **`0.8236`** (`1.12×`) | `187.04` | `61,888` (`1.16×`) | `71` | `1,197` (`1.20×`) | **`3.931 × 10²⁶`** (`2,700×` larger!) |
| **`14`** | **`R2_StorageDeleted`** | `16` | `15` | `17` | **`0`** | **`0.7316`** (`1.26×`) | `181.09` | `46,392` (`1.55×`) | `43` | `776` (`1.86×`) | `3.694 × 10¹¹` |
| **`14`** | **`R3_MinLocalCompact`** | `2` | `14` | `16` | **`0`** | **`0.5845`** (`1.58×`) | `177.08` | `37,864` (`1.90×`) | `42` | `628` (`2.29×`) | `8.776 × 10¹⁰` |
| **`16`** | **`R0_RawPostCleanup`** | `18` | `49` | `51` | **`1`** | *FAIL* (`1.17 s`) | `201.04` | — | — | — | `maxRecDepth` at `L75:8` |
| **`16`** | **`R1_F1_1b_Nop`** | `18` | `49` | `51` | **`1`** | *FAIL* (`1.20 s`) | `190.34` | — | — | — | `maxRecDepth` at `L75:8` |
| **`16`** | **`R2_StorageDeleted`** | `18` | `17` | `19` | **`1`** | *FAIL* (`0.73 s`) | `184.39` | — | — | — | `maxRecDepth` at `L43:8` |
| **`16`** | **`R3_MinLocalCompact`** | `2` | `16` | `18` | **`1`** | *FAIL* (`0.51 s`) | `172.97` | — | — | — | `maxRecDepth` at `L42:8` |

*(Exact integer unfolded tree counts for `K ≥ 6` are preserved in
`support/e2_8_real_anneal_mirwp_scaling.json`; e.g., at `K = 14`, `R0` is
`145,582,513,964,029,819,592,233` and `R1` is
`393,065,336,852,904,125,969,860,017`.)*

**Key Diagnostic Findings (`[real measurement]` + `[derived]`):**

1. **Identical `K = 14 → 16` Hard Cliff Regardless of `L`, `S`, or Fuel:**
   `R0` (`fuel = 45`, `43` statements, `16` locals) succeeds at `K = 14`, yet
   `R3` (`fuel = 18`, `16` statements, `2` locals) crashes at `K = 16` on the
   `theorem bench_thm : RunsFrom ... := rfl` declaration (`L42:8`). Because all
   four regimes fail at the exact same arithmetic depth `K = 16` despite `2.7×`
   different statement counts and `9×` different local counts, the bottleneck is
   the nested kernel WHNF reduction depth of `K` chained `evalBinOp .add` →
   `evalArithOp` → `truncateScalar` → `bvOfInt` → `truncateBits` calls inside
   `@Nat.rec` (`execState`, `MirWp.lean:112–125`) hitting Lean's default
   `maxRecDepth = 512`.
2. **Exponential Unfolded Proof-Tree Growth Under `rfl`:** Every `+2` increase
   in `K` multiplies the unfolded `Expr` tree of `bench_thm` by `~16×` in `R3`,
   `~780×` in `R0`, and `~2,500×` in `R1`. Even though Lean's DAG sharing keeps
   `proof_dag_nodes` linear (`628`–`1,440` at `K = 14`), `RunsFrom` concrete
   `rfl` is fundamentally limited to small positive/negative canaries—never
   scalable function verification.

---

### 3. Suite B: Universally Quantified Symbolic `Executes` Scaling (`∀ x : BitVec 128`, `K = 2..64`)

`Basis: execution (support/e2_8_real_anneal_mirwp_scaling.json, suite_b_symbolic_executes; [real measurement]) + source`

Suite B eliminates `RunsFrom` `rfl` blowup by proving universally quantified
symbolic correctness (`∀ x : BitVec 128, Executes bodyBench (mkState 0 0 init_sym) (.scalar ⟨.i32, false, chainVal x⟩)`)
using explicit `let y_i := addU32Bits ...` sharing and step-by-step
`Executes.next` applications backed by `E28Helpers` (`24` total configurations
across `K ∈ {2, 4, 8, 16, 32, 64}`):

| `K` | Regime | `L` | `S` | `rc` | Median Wall (s) | Speedup vs. `R0` | RSS (MB) | `.olean` (B) | LOC | Proof DAG | Proof Tree |
| :-: | :--- | :-: | :-: | :-: | ---: | ---: | ---: | ---: | :-: | ---: | ---: |
| `2` | `R0_RawPostCleanup` | `4` | `7` | `0` | `0.3080` | `1.00×` | `169.84` | `31,456` | `54` | `531` | `7,593` |
| `2` | `R1_F1_1b_Nop` | `4` | `7` | `0` | `0.3067` | `1.00×` | `170.20` | `29,496` | `54` | `480` | `7,527` |
| `2` | `R2_StorageDeleted` | `4` | `3` | `0` | `0.3079` | `1.00×` | `168.93` | `26,472` | `46` | `403` | `5,603` |
| `2` | `R3_MinLocalCompact` | `2` | `2` | `0` | `0.2694` | `1.14×` | `166.96` | `23,752` | `43` | `328` | `3,457` |
| `4` | `R0_RawPostCleanup` | `6` | `13` | `0` | `0.4096` | `1.00×` | `173.14` | `40,496` | `72` | `803` | `17,151` |
| `4` | `R1_F1_1b_Nop` | `6` | `13` | `0` | `0.4224` | **`0.97×`** | `171.79` | `36,840` | `72` | `699` | `17,531` |
| `4` | `R2_StorageDeleted` | `6` | `5` | `0` | `0.3720` | `1.10×` | `169.10` | `31,864` | `56` | `562` | `12,179` |
| `4` | `R3_MinLocalCompact` | `2` | `4` | `0` | `0.3605` | `1.14×` | `169.05` | `28,024` | `53` | `454` | `8,005` |
| `8` | `R0_RawPostCleanup` | `10` | `25` | `0` | `0.6445` | `1.00×` | `173.95` | `60,112` | `108` | `1,395` | `46,179` |
| `8` | `R1_F1_1b_Nop` | `10` | `25` | `0` | `0.7730` | **`0.83×`** | `175.18` | `51,912` | `108` | `1,149` | `49,011` |
| `8` | `R2_StorageDeleted` | `10` | `9` | `0` | `0.5546` | `1.16×` | `173.09` | `43,032` | `76` | `892` | `32,291` |
| `8` | `R3_MinLocalCompact` | `2` | `8` | `0` | `0.4890` | `1.32×` | `171.07` | `36,568` | `73` | `706` | `21,541` |
| `16` | `R0_RawPostCleanup` | `18` | `49` | `0` | `1.0698` | `1.00×` | `200.05` | `106,488` | `180` | `2,779` | `145,248` |
| `16` | `R1_F1_1b_Nop` | `18` | `49` | `0` | `1.2116` | **`0.88×`** | `201.34` | `84,208` | `180` | `2,093` | `159,224` |
| `16` | `R2_StorageDeleted` | `18` | `17` | `0` | `0.7200` | `1.49×` | `179.23` | `66,904` | `116` | `1,600` | `100,355` |
| `16` | `R3_MinLocalCompact` | `2` | `16` | `0` | `0.4110` | `2.60×` | `173.61` | `53,656` | `113` | `1,210` | `66,373` |
| **`32`** | **`R0_RawPostCleanup`** | `34` | `97` | `0` | **`3.4099`** | `1.00×` | `308.00` | `238,176` | `324` | `5,100` | `517,943` |
| **`32`** | **`R1_F1_1b_Nop`** | `34` | `97` | `0` | **`4.0246`** | **`0.85×`** | `324.00` | `198,032` | `324` | `3,753` | **`579,377`** |
| **`32`** | **`R2_StorageDeleted`** | `34` | `33` | `0` | **`1.7806`** | **`1.92×`** | `217.05` | `126,496` | `196` | `2,796` | `358,553` |
| **`32`** | **`R3_MinLocalCompact`** | `2` | `32` | `0` | **`0.7127`** | **`4.78×`** | **`179.24`** | **`87,832`** | **`193`** | **`2,218`** | **`227,077`** |
| **`64`** | **`R0_RawPostCleanup`** | `66` | `193` | **`1`** | *FAIL* (`9.75 s`) | — | `488.79` | — | — | — | `maxRecDepth` at `L611:74` |
| **`64`** | **`R1_F1_1b_Nop`** | `66` | `193` | **`1`** | *FAIL* (`13.98 s`) | — | `671.00` | — | — | — | `maxRecDepth` at `L611:74` |
| **`64`** | **`R2_StorageDeleted`** | `66` | `65` | **`0`** | **`5.8278`** | *Survives* | `377.96` | `275,256` | `356` | `5,371` | `1,332,809` |
| **`64`** | **`R3_MinLocalCompact`** | `2` | `64` | **`0`** | **`1.3906`** | **`4.19×` vs `R2`** | **`195.70`** | **`157,888`** | **`353`** | **`4,250`** | **`842,620`** |

#### Mechanistic Dissection of the Four Regimes (`[real measurement]` + `[derived]`)

1. **Why `R1_F1_1b_Nop` Regresses Wall Time, Peak RSS, and Unfolded Proof Tree
   at Every `K ≥ 4`:** At `K = 32`, `R1` is `18.0%` slower (`4.0246 s` vs.
   `3.4099 s`), uses `+16.00 MB` more RSS (`324.00` vs. `308.00 MB`), and
   enlarges the unfolded proof tree by `+11.9%` (`579,377` vs. `517,943`), even
   though its shared DAG drops (`5,100 → 3,753`) because `evalStep_assign_add_copy`
   omits the `hdeinit : setElem?` premise required by `evalStep_assign_add_move`.
   Two concrete structural causes explain this inversion:
   - **Zero step reduction:** Replacing `StorageLive`/`StorageDead` 1-to-1 with
     `.nop` leaves `S = 3K + 1 = 97` statements unchanged, so the proof still
     emits `97` `Executes.next` steps and `97` explicit `34`-element `mkState`
     slot lists.
   - **Dead-value retention in `List LocalSlot`:** In `R0`, `.move` clears the
     consumed source slot to `.live none` and `StorageDead` clears it to
     `.dead` (`1` constructor node). In `R1`, `.copy` and `.nop` preserve
     `.live (some (.scalar ⟨.i32, false, y_j⟩))` in every dead temporary slot
     `_2.._(K+1)` across all remaining `97 - 3j` steps—strictly increasing the
     symbolic `LocalSlot` term carried through every `Executes.next` and every
     `rfl` reduction of `getElem?`/`setElem?` (`MirSemantics.lean:650–661`).
2. **Exact Cause of the `K = 64` `maxRecDepth = 512` Cliff in `R0` and `R1`:**
   In both `Bench_symbolic_R0_RawPostCleanup_K64.lean` and
   `Bench_symbolic_R1_F1_1b_Nop_K64.lean`, Lean crashes at line `611` column
   `74`—the third `rfl` (`hlen : Nat.beq 193 bb.statements.length = true`)
   inside `exact Executes.ret (evalStep_return_u32 bodyBench _ 0 193 _ y64 rfl rfl rfl rfl rfl rfl)`.
   Walking `193` `List.cons` nodes in `List.length` and `Nat.beq` atop the
   tactic elaborator stack exceeds `maxRecDepth = 512`. Deleting storage markers
   (`R2`, `S = 65`) drops statement depth `~3×`, allowing `K = 64` to pass cleanly.
3. **Multiplicative Factoring of `R0 → R3` (`4.78×` at `K = 32`):**
   - **Statement deletion (`R0 → R2`, `S: 97 → 33` at fixed `L = 34`):**
     **`1.92×`** wall (`3.4099 → 1.7806 s`), `1.42×` RSS (`308.00 → 217.05 MB`),
     `1.88×` `.olean`, `1.65×` LOC, `1.82×` DAG, `1.44×` tree.
   - **Dead-local compaction (`R2 → R3`, `L: 34 → 2` at `S: 33 → 32`):**
     **`2.50×`** wall (`1.7806 → 0.7127 s`), `1.21×` RSS (`217.05 → 179.24 MB`),
     `1.44×` `.olean`, `1.26×` DAG, `1.58×` tree. At `K = 64` (`L: 66 → 2` at
     `S: 65 → 64`), local compaction alone delivers **`4.19×`** wall speedup
     (`5.8278 → 1.3906 s`) and **`1.93×`** lower peak RSS (`377.96 → 195.70 MB`).
   - **Combined (`R0 → R3` at `K = 32`):** `1.92 × 2.50 = 4.78×` wall speedup,
     `2.71×` smaller `.olean`, `1.68×` fewer LOC, `2.30×` smaller DAG, and
     `2.28×` smaller tree—still far below the refuted `10.79×` AST / `6.19×` LOC
     / `10.68×` elab figures in
     `anneal-spec-minissa-normalization-and-proof-compression` (which assumed
     additional `SROA`/`Mem2Reg` memory elimination on synthetic dicts never run
     through Lean).

---

### 4. Suite C: Symbolic Loop Invariant Proof (`sum_loop`, `∀ n : Nat`)

`Basis: execution (support/e2_8_real_anneal_mirwp_scaling.json, suite_c_symbolic_loop; [real measurement])`

Suite C verifies a genuine `3`-block CFG countdown loop (`bb0`: `switchInt` on
counter `_1`; `bb1`: latch updating `acc := acc + i`, `i := i - 1`, `goto bb0`;
`bb2`: return `acc`) universally quantified over
`(n : Nat) (hn : n < 4294967296) (acc : BitVec 128) (hacc : ScalarVal.wf ⟨.i32, false, acc⟩ = true)`
by structural induction (`induction n generalizing acc`) against recursive
`sumSpec : Nat → BitVec 128 → BitVec 128` directly in `Anneal.MirWp.Executes`:

| Regime | `L` | Latch Stmts | `rc` | Median Wall (s) | Wall Runs (s) | Speedup vs. `R0` | RSS (MB) | `.olean` (B) | LOC | Type DAG / Tree | Proof DAG | Proof Tree |
| :--- | :-: | :-: | :-: | ---: | :--- | ---: | ---: | ---: | :-: | :---: | ---: | ---: |
| **`R0_RawPostCleanup`** | `5` | `8` | `0` | **`0.6205`** | `0.6205, 0.6801, 0.5607` | `1.00×` | `180.46` | `143,576` | `130` | `98 / 175` | **`932`** | **`15,229`** |
| **`R1_F1_1b_Nop`** | `5` | `8` | `0` | **`0.6279`** | `0.6746, 0.6279, 0.6193` | **`0.99×`** | `180.45` | `143,288` | `131` | `105 / 187` | `922` (`1.01×`) | `15,627` (`0.97×`) |
| **`R2_StorageDeleted`** | `5` | `4` | `0` | **`0.6102`** | `0.6102, 0.6217, 0.5384` | **`1.02×`** | `180.51` | `141,272` | `123` | `105 / 187` | `860` (`1.08×`) | `13,479` (`1.13×`) |
| **`R3_MinLocalCompact`** | `3` | `2` | `0` | **`0.4645`** | `0.4645, 0.6261, 0.4632` | **`1.34×`** | `177.60` | `135,496` (`1.06×`) | `116` (`1.12×`) | `94 / 163` | **`700`** (`1.33×`) | **`8,571`** (`1.78×`) |

**Two Concrete Findings (`[real measurement]` + `[source]`):**

1. **Direct Refutation of `13.61×` AST / `15.48×` Elab Loop Claims:** On a real
   inductive `Anneal.MirWp` loop proof, fixed per-module elaboration overhead
   (loading `Trusted.MirSemantics`/`Anneal.MirWp` + proving arithmetic loop
   lemmas `toNat_ofNat_lt_128`, `bitvec_ofNat_succ_ne_zero`, and
   `subU32Bits_succ_one`) dominates total checking cost. Even maximal
   `R0 → R3` simplification (`5 → 3` locals, `8 → 2` latch statements) achieves
   **`1.34×` wall speedup**, **`1.12×` LOC reduction**, **`1.33×` kernel proof
   DAG compression**, and **`1.78×` unfolded tree compression**—an order of
   magnitude smaller than the fabricated `13.61×` / `15.48×` figures in
   `loop-invariant-and-recursive-spec-minissa-vc-transport`.
2. **Loop-Invariant Generalization Penalty in `R1` and `R2`:** In `R0`,
   `StorageDead 3` and `StorageDead 4` restore slots `_3` and `_4` to `.dead`
   before the `goto 0` backedge, matching entry state directly. In `R1` and
   `R2`, removing `StorageDead` leaves stale values (`acc'`, `i'`) in `_3` and
   `_4` across the backedge, forcing the inductive theorem statement to add
   extra universally quantified parameters `(v3 v4 : Option Val)` and
   `induction n generalizing acc v3 v4` (growing `type_dag_nodes` from `98` to
   `105` and `type_tree_nodes` from `175` to `187`). Compacting `_3` and `_4`
   away in `R3` removes this extra quantification (`type_dag_nodes = 94`,
   `type_tree_nodes = 163`).

---

### 5. Suite D: Direct `VrustcFormal.F1_1b` `rfl` Checker Overhead and Net Break-Even Analysis

`Basis: execution (support/e2_8_real_anneal_mirwp_scaling.json, suite_d_f1_1b_transport_checker; [real measurement]) + derived`

Suite D imports `VrustcFormal.F1_1b` (`AnnealTrustedMirMoveToCopyStorage.lean`)
and instantiates the full two-pass certified VC-transport pipeline
(`progR0 → progM2C → progR1`) for `K ∈ {4, 8, 16, 32}`, proving four `rfl`
check obligations (`isMoveToCopyProgram`, `checkNoUseAfterMoveProgram`,
`isRemoveStorageMarkersProgram`, `checkStorageSafeProgram`) and composing
`vc_transport_moveToCopy_certified_iff` with
`vc_transport_removeStorageMarkers_certified_iff` into `bench_thm`:

| `K` | `L` | `S` | `S × L` | `rc` | Checker Median Wall (s) | Wall Runs (s) | RSS (MB) | `.olean` (B) | LOC | `bench_thm` Type DAG / Tree | `bench_thm` Proof DAG / Tree |
| :-: | :-: | :-: | ---: | :-: | ---: | :--- | ---: | ---: | :-: | :---: | :---: |
| `4` | `6` | `13` | `78` | `0` | **`0.5321`** | `0.5301, 0.5364, 0.5321` | `179.26` | `57,864` | `110` | `28 / 37` | **`366 / 1,167`** |
| `8` | `10` | `25` | `250` | `0` | **`0.6832`** | `0.6832, 0.7025, 0.6811` | `181.31` | `67,912` | `146` | `28 / 37` | **`366 / 1,167`** |
| `16` | `18` | `49` | `882` | `0` | **`1.1960`** | `1.1673, 1.1960, 1.2986` | `193.32` | `89,552` | `218` | `28 / 37` | **`366 / 1,167`** |
| `32` | `34` | `97` | `3,298` | `0` | **`2.8819`** | `2.8292, 2.8819, 3.0143` | `240.58` | `132,016` | `362` | `28 / 37` | **`366 / 1,167`** |

**Constant Proof-Term Size vs. Superlinear `O(S × L)` Kernel Reduction Time:**
Because reflective `rfl` hides checker execution inside kernel definitional
equality, `bench_thm` retains an invariant **`366`-node proof DAG**
(`1,167`-node unfolded tree) across all `K`. However, wall time accelerates
superlinearly (`1.28×` from `K=4→8`, `1.75×` from `K=8→16`, **`2.41×` from
`K=16→32`**); subtracting fixed `~0.45 s` startup yields marginal checking times
of `~0.08 s → 0.23 s → 0.75 s → 2.43 s` (`~3.0×–3.3×` per doubling of `K`),
tracking the `O(S × L)` cost of `List` `getElem?`/`setElem?` and
`hasStorageAnnotation` inside `checkAbsBody` (`AnnealTrustedMirMoveToCopyStorage.lean:480–508`).

#### Net Break-Even Comparison (Suite B Proof + Suite D Checker vs. Direct `R0` Proof)

| `K` | Direct `R0` Proof (s) | Actual `R1 + F1_1b` Total (s) | Actual `R1` Pipeline vs. `R0` | `R0 → R3` Proof Saving (s) | Suite D `O(S × L)` Checker (s) | Counterfactual `R3 + O(S × L)` Total (s) | Counterfactual Net vs. `R0` |
| :-: | ---: | ---: | :---: | ---: | ---: | ---: | :---: |
| `4` | `0.4096` | **`0.9545`** (`0.4224 + 0.5321`) | **`2.33×` slower** (`+0.5449 s`) | `0.0491` | `0.5321` | `0.8926` | `2.18×` slower (`+0.4830 s`) |
| `8` | `0.6445` | **`1.4562`** (`0.7730 + 0.6832`) | **`2.26×` slower** (`+0.8117 s`) | `0.1555` | `0.6832` | `1.1722` | `1.82×` slower (`+0.5277 s`) |
| `16` | `1.0698` | **`2.4076`** (`1.2116 + 1.1960`) | **`2.25×` slower** (`+1.3378 s`) | `0.6588` | `1.1960` | `1.6070` | `1.50×` slower (`+0.5372 s`) |
| **`32`** | **`3.4099`** | **`6.9065`** (`4.0246 + 2.8819`) | **`2.03×` slower** (`+3.4966 s`) | **`2.6972`** | **`2.8819`** | **`3.5946`** | **`1.05×` slower** (`+0.1847 s`) |

*(One-time `16.4345 s` compilation of `AnnealTrustedMirMoveToCopyStorage.lean`
and `1.5756 s` compilation of `E28Helpers.lean` are amortized per crate and
excluded from the per-function totals above.)*

#### Architecture Verdict (`[derived]` from `[real measurement]`)

1. **`.nop`-Preserving Lowering (`R0 → R1`) Cannot Pay Back Its Own Cost:**
   Because `R1` makes symbolic `Executes` proofs `18.0%` slower at `K = 32`
   *before* adding checker overhead, the real end-to-end `R0 → R1` pipeline is
   `2.03×–2.33×` slower across all measured sizes (`6.9065 s` vs. `3.4099 s` at
   `K = 32`) and still hits the `K = 64` `maxRecDepth` wall.
2. **Two Joint Prerequisites for a Net-Positive Normalization Bridge:**
   - **Pass expressiveness (`R0 → R3`):** A real Anneal / verified-`rustc`
     normalization bridge must eliminate dead statements (`StorageLive`,
     `StorageDead`, `.nop` via stuttering simulation) **and** compact dead
     temporary locals (via local-index remapping) to unlock `R3`'s `4.78×`
     proof speedup (`K = 32`) and `K = 64` survival (`1.3906 s`).
   - **Checker complexity (`O(S)` or external):** Even `R3`'s `2.6972 s` saving
     at `K = 32` is completely erased by a `2.8819 s` naive `O(S × L)` `List`
     `rfl` checker. Consistent with
     `lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`,
     a production transport checker must either eliminate quadratic `List`
     traversals (e.g., `O(S)` indexed/balanced-tree kernel encoding or explicit
     structural proof terms) or run as a verified compiled native / externally
     checked certificate validator.

---

### 6. Analytical Dimensions Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

`Basis: execution (support/e2_8_real_anneal_mirwp_scaling.json) + source + derived`

| Dim | Category | Measured Status / Assessment |
| :-: | :--- | :--- |
| **`L1`** | Authoring & proof velocity | `[real measurement]` Programmatically generated proofs (`30–356` LOC per module + `421`-LOC shared `E28Helpers.lean`); `R0 → R3` cuts proof script LOC by `1.68×` at `K = 32` (`324 → 193`) and `1.12×` on `sum_loop` (`130 → 116`) while removing dead-temp invariant parameters `(v3 v4)`. Interactive human authoring time: **`not measured`**. |
| **`L2`** | Toolchain / TCB build time | `[real measurement]` One-time `E28Helpers.lean` build: `1.5756 s` (`185.39 MB`); one-time `AnnealTrustedMirMoveToCopyStorage.lean` build: `16.4345 s` (`569.20 MB`). Pre-cached `Trusted.{MirAst,MirSemantics}` + `Anneal.MirWp` `.olean`s were reused (`not re-timed` here; see `anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge` for fresh TCB compile timings). |
| **`L3`** | Pass / cert synthesis latency | **`not measured`** — Benchmark generates MIR regimes and `certEntry` deterministically in Python; no live Rust MIR pass or CFG certificate synthesizer was timed. |
| **`L4`** | Generated code performance | **`not examined`** — Pure MIR proof-checking and transport-checker scaling benchmark; no machine codegen. |
| **`L5`** | Checking latency & throughput | `[real measurement]` Full `64`-configuration synchronous Lean `v4.34.1` matrix (`3`-run medians): Suite A hits `maxRecDepth` at `K = 16` across `R0..R3` (`K = 14`: `0.9206 s → 0.5845 s`); Suite B `K = 32`: `3.4099 s (R0) / 4.0246 s (R1) / 1.7806 s (R2) / 0.7127 s (R3)` (`4.78×`); `K = 64`: `R0`/`R1` fail, `R2 = 5.8278 s`, `R3 = 1.3906 s` (`4.19×`); Suite C `sum_loop`: `0.6205 s → 0.4645 s` (`1.34×`); Suite D `F1_1b` `rfl` checker: `0.5321 s → 2.8819 s` (`K = 4..32`, net `R1` total `6.9065 s` = `2.03×` slower than `R0`). |
| **`L6`** | RAM & artifact footprint | `[real measurement]` Peak RSS (`K = 32` Suite B): `308.00 MB (R0)`, `324.00 MB (R1)`, `217.05 MB (R2)`, `179.24 MB (R3)` (`1.72×` lower); `K = 64`: `488.79 MB (R0 fail)`, `671.00 MB (R1 fail)`, `377.96 MB (R2)`, `195.70 MB (R3)`. `.olean` (`K = 32` Suite B): `238,176 B → 87,832 B` (`2.71×`). Kernel `Expr` DAG/tree measured across all `58` passing theorems. |
| **`C1`** | Spec & assumption auditability | `[real measurement]` + `[published source]` Zero fake `namespace Trusted`, zero `set_option`, synchronous `-DElab.async=false -Ddebug.skipKernelTC=false` directly against unmodified `joshlf/anneal@c131b320e` and `VrustcFormal.F1_1b`. |
| **`C2`** | Orthogonality & simplicity | `[derived]` Four-regime ablation (`R0 → R1 → R2 → R3`) cleanly separates operand rewriting + `.nop` (`0.85×`), statement deletion (`1.92×`), and dead-local compaction (`2.50×` at `K = 32`, `4.19×` at `K = 64`). |
| **`V1`** | Adequacy & non-vacuity | `[real measurement]` Every passing theorem is kernel-checked over real `Trusted.MirSemantics` and `Anneal.MirWp` (`rc = 0`, `58 / 64` passing, `6 / 64` genuine `maxRecDepth` boundary failures); Suite D reuses the `nanoda`-verified `VrustcFormal.F1_1b` theorems. Separate `TrustedBoundary.lean` replay on the `58` generated benchmark modules was **`not measured`** (helper/benchmark modules use only `prelude` + `TrustedBoundary`-admitted imports and tactics, except `BatchInspect.lean` which is an out-of-band `import Lean` `partial def` metric inspector). |
| **`V2`** | Differential fuzzing | **`not examined`** — Fixed deterministic chain and loop templates; no randomized MIR fuzzing. |
| **`V3`** | Weak-memory / crash / silicon | **`known not to apply`** — Strictly sequential, deterministic, single-frame value-only MIR fragment. |
| **`V4`** | Held-out ecosystem replay | **`not examined`** — Synthetic straight-line and single-loop MIR harnesses only; no real captured `rustc` crates (e.g., `zerocopy` or `memchr`) were replayed. |

---

## Boundaries

### Honest Scope & Explicit Non-Claims

1. **Synthetic Straight-Line and Single-Loop MIR Harnesses (`not examined` on
   real captured crates):** All four suites measure synthetic `u32` addition
   chains (`K = 2..64`, `1` basic block) and one synthetic `3`-block countdown
   loop (`sum_loop`). They do **not** measure real captured `rustc` crate bodies
   with branching CFGs, multi-block SSA join phis, function calls, panics, or
   `#[anneal_spec]` companion contracts (`V4` `not examined`).
2. **Unmodified `Trusted.MirSemantics@c131b320e` v1 `List LocalSlot` Value-Only
   Fragment (`known not to apply` to memory/SROA/Tree Borrows):**
   `Trusted.MirSemantics@c131b320e` models strictly single-frame, deterministic,
   unprojected scalar/bool/unit/never/fieldless-enum execution over a linked
   `List LocalSlot` (`MirSemantics.lean:650–661, 721–724, 801–829`). These
   numbers do **not** measure heap/stack memory lenses, `&`/`&mut` references,
   projections, `SROA`, `Mem2Reg` over address-taken stack slots, or Tree
   Borrows protectors—nor do they prove that `SROA`/`Mem2Reg` over memory-heavy
   Rust code cannot exceed `4.78×` once `Trusted.MirSemantics` adds memory.
3. **Counterfactual `R3 + Suite D` Break-Even Estimate (`derived` upper-bound
   comparison, `not examined` for a real `R0 → R3` checker):** Suite D times
   `VrustcFormal.F1_1b`'s actual `R0 → R1` `rfl` checker (`checkNoUseAfterMoveProgram`
   + `checkStorageSafeProgram`), because no direct `R0 → R3` stuttering +
   dead-local-compaction bridge over `Trusted.MirSemantics` exists yet. Adding
   Suite D's `2.8819 s` to `R3`'s `0.7127 s` (`3.5946 s`) illustrates that a
   naive `O(S × L)` `List`-based `rfl` checker consumes all `R3` savings at
   `K = 32`; the exact checking cost of a real `R0 → R3` validator (stuttering
   simulation + local-renaming map) is **`unknown`** until implemented and
   timed.
4. **Suite D Scaling Beyond `K = 32` (`not examined`):** Suite D was measured
   at `K ∈ {4, 8, 16, 32}` (`S ≤ 97`, `L ≤ 34`). Whether `VrustcFormal.F1_1b`'s
   `rfl` checker survives `K = 64` (`S = 193`, `L = 66`) under default
   `maxRecDepth = 512` was **`not examined`** directly (though the `R0`/`R1`
   `List.length` crash at `S = 193` in Suite B indicates `K = 64` `rfl`
   checking over `193`-element `List`s is also near or past `maxRecDepth`).
5. **Single-Host Measurement Conditions and Noise (`[real measurement]` caveat):**
   All `64` configurations ran sequentially on one `x86_64-unknown-linux-gnu`
   machine (`3` repeats each, median reported). At small `K` (`K = 2..8`,
   `0.27–0.68 s`), process startup and OS jitter represent a large fraction of
   wall time (for example, `R3` `sum_loop` repeats were `0.4645, 0.6261,
   0.4632 s`, and Suite A `K = 6` showed `0.4660–0.5484 s` noise across
   regimes). Cross-version Lean (`v4.28.0-rc1`, `v4.35.0`) and `nanoda_bin`
   external replay timings for Suites A–D were **`not examined`**.
6. **Per-Module `TrustedBoundary.lean` Audit Not Re-Run on Generated Benchmarks
   (`not examined`):** The `58` generated benchmark `.lean` files were compiled
   synchronously with `-DElab.async=false -Ddebug.skipKernelTC=false` and
   default `maxRecDepth = 512` (zero `set_option`, zero `sorry`, zero
   `bv_decide`/`native_decide`), importing only `Init.*`, `Trusted.*`,
   `Anneal.MirWp`, `E28Helpers`, and `F1_1b_Mod`; running `TrustedBoundary.lean`
   `"preflight"` / `"audit"` over each generated file individually was
   `not examined` (and `BatchInspect.lean` uses `import Lean` + `partial def`
   strictly as an out-of-band `.olean` AST size reader, never imported by any
   benchmark theorem).

---

## Evidence

### Preserved Package Artifacts & Upstream Sources (`2026-11-20`)

| Artifact / Upstream Subject | Pin / Path | Size / Scope | SHA-256 / Exact Coordinates |
| :--- | :--- | ---: | :--- |
| `support/e2_8_real_anneal_mirwp_scaling.json` | Package artifact | `45,124 B` / `1,481` lines | `69638e2ce2dd1625b27baa0c8f8343fd29f554efc2c30476ba68cd561a718bc8` (`64` timed configs + `58` AST counts; `6` failure `stderr` paths sanitized) |
| `support/e2_8_real_anneal_mirwp_scaling.py` | Package artifact | `75,276 B` / `1,277` lines | `03d87c79268b62af465a86a035e21bd9b77cffe2ce2c3b62416d2cf3711546d1` (env-var portable harness; `py_compile` clean) |
| `support/README.md` | Package artifact | `2,767 B` | Documents exact sanitization diff and env vars |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` | `40,381 B` | `71b57539fa1d462e1e856db4d7b0c7a260f7c39255c05cf489cfe87edc1a77c8` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean` | `111,865 B` | `b8378127ea7b81b473a5f86cd164df430feb56296cbbbe57457cc2b125316c0a` (`L650–661` `getElem?`/`setElem?`, `L687` `hasStorageAnnotation`, `L775` `initLocalsLoop`, `L949` `evalOperandToSlot`, `L1060–1111` `evalArithOp`/`evalBinOp`, `L1370` `evalStatement`, `L1597` `evalStep`) |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `theory/Anneal/MirWp.lean` | `115,247 B` | `3c5458c796b0f477a689bbee116632b0a79d0f9b021120dfceec0ccacd67e6dc` (`L112–125` `execOutcomeState`/`execState`, `L429` `wellFormed_and_spec_of_wp`, `L1640` `mkState`, `L1978` `bodyProg`, `L2013–2035` `RunsFrom`/`Runs`/`Executes`) |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean` | `117,602 B` | `6f19cc602cf931522d61efb320eae3ca60d7759db20ba6304c912bf372f2fc6a` (`L447–490, 962` `allowedCommandKinds` excluding `set_option`) |
| `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` (`x86_64-unknown-linux-gnu`, Release) | Lean compiler & kernel | Invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` (default `maxRecDepth = 512`) |
| `google/zerocopy@6e24ad128d7f29afc0f47733eb42ec4d3392ba63` | `reports/anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/support/AnnealTrustedMirMoveToCopyStorage.lean` | `275,460 B` / `6,489` lines | `79d0c63cfe045233d1dcc491529b585981c7afe715bb876f52d314d0a7c91a5c` (compiled as `F1_1b_Mod` in Suite D) |
| `google/zerocopy@0afd1cbbdb7d8947f9b3a44dc0fccaab3e688689` | Epistemic audit errata commit | `34` packages | Recorded `REFUTED` errata on `anneal-spec-minissa-normalization-and-proof-compression` and `loop-invariant-and-recursive-spec-minissa-vc-transport` |

### Complete Failure Diagnostics (`6` of `64` Configurations, `rc = 1`)

All `6` failures occurred solely from Lean `v4.34.1`'s default
`maxRecDepth = 512` limit:

| Suite | Module | `L` | `S` | Failing Line:Col & Construct | Elapsed (s) | Peak RSS (MB) | Exact Diagnostic |
| :---: | :--- | :-: | :-: | :--- | ---: | ---: | :--- |
| A | `Bench_concrete_R0_RawPostCleanup_K16` | `18` | `49` | `L75:8` (`theorem bench_thm : RunsFrom ... := rfl`) | `1.17` | `201.04` | `error: maximum recursion depth has been reached` |
| A | `Bench_concrete_R1_F1_1b_Nop_K16` | `18` | `49` | `L75:8` (`theorem bench_thm : RunsFrom ... := rfl`) | `1.20` | `190.34` | `error: maximum recursion depth has been reached` |
| A | `Bench_concrete_R2_StorageDeleted_K16` | `18` | `17` | `L43:8` (`theorem bench_thm : RunsFrom ... := rfl`) | `0.73` | `184.39` | `error: maximum recursion depth has been reached` |
| A | `Bench_concrete_R3_MinLocalCompact_K16` | `2` | `16` | `L42:8` (`theorem bench_thm : RunsFrom ... := rfl`) | `0.51` | `172.97` | `error: maximum recursion depth has been reached` |
| B | `Bench_symbolic_R0_RawPostCleanup_K64` | `66` | `193` | `L611:74` (`evalStep_return_u32 ... rfl` on `Nat.beq 193 bb.statements.length`) | `9.75` | `488.79` | `error: maximum recursion depth has been reached` |
| B | `Bench_symbolic_R1_F1_1b_Nop_K64` | `66` | `193` | `L611:74` (`evalStep_return_u32 ... rfl` on `Nat.beq 193 bb.statements.length`) | `13.98` | `671.00` | `error: maximum recursion depth has been reached` |

---

## Revalidation

1. **Zero-Lean Dataset & Arithmetic Check (~0.1 s):** Verify SHA-256 digests of
   `support/e2_8_real_anneal_mirwp_scaling.json`
   (`69638e2ce2dd1625b27baa0c8f8343fd29f554efc2c30476ba68cd561a718bc8`) and
   `support/e2_8_real_anneal_mirwp_scaling.py`
   (`03d87c79268b62af465a86a035e21bd9b77cffe2ce2c3b62416d2cf3711546d1`), confirm
   `python3 -m py_compile support/e2_8_real_anneal_mirwp_scaling.py` exits `0`,
   and recompute every table ratio directly from the JSON.
2. **Full Real-Kernel Replay Against Unmodified `joshlf/anneal@c131b320e` (~3 min):**
   Compile `Trusted.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`,
   and `Anneal/MirWp.lean` from
   `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` under
   `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) into
   `/tmp/reval_anneal_cache`, then run:
   ```bash
   ANNEAL_OLEAN_CACHE=/tmp/reval_anneal_cache \
   F1_1B_SRC=reports/anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/support/AnnealTrustedMirMoveToCopyStorage.lean \
   LEAN_BIN="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
   OUT_JSON=/tmp/reval_e2_8.json \
   python3 support/e2_8_real_anneal_mirwp_scaling.py
   ```
   Confirm: (a) Suite A passes through `K = 14` and fails with `maxRecDepth` at
   `K = 16` across all four regimes; (b) Suite B `K = 32` reproduces `R1 > R0 > R2 > R3`
   wall ordering (`R3` `~4–5×` faster than `R0`, `R1` slower than `R0` with
   larger unfolded tree) and `K = 64` fails on `R0`/`R1` while succeeding on
   `R2`/`R3`; (c) Suite C `sum_loop` reproduces `~1.3×` wall speedup and exact
   proof DAG/tree counts (`932 → 700`, `15,229 → 8,571`); and (d) Suite D
   reproduces exact constant `366`-node `bench_thm` DAG with superlinear `K = 4..32`
   `rfl` checking time exceeding `R0 → R3` savings at `K = 32`.
3. **Drift Triggers Requiring Re-Benchmarking:** Re-run Suites A–D whenever
   `joshlf/anneal` changes `Trusted.MirSemantics`'s `List LocalSlot`
   representation (e.g., to `Array` or balanced trees), changes `evalArithOp` /
   `BitVec 128` scalar encoding, upgrades its pinned Lean toolchain beyond
   `v4.34.1`, or lands a stuttering + dead-local-compaction (`R0 → R3`)
   transport checker or `O(S)` indexed checker replacing `VrustcFormal.F1_1b`'s
   `List`-based `rfl` checks.
