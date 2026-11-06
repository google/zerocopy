# Lean 4 Kernel Memory Ceilings, C++ WHNF Reduction Scaling, Pre-Proved Validator Architectures, and Persistent Collection Telemetry

## Summary

Across Lean `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), empirical measurement and C++ kernel source analysis establish the exact memory ceilings, WHNF reduction complexity classes, pre-proved validator architectures, `<fn>._unsafe_rec` elaboration rules, and persistent-collection runtime behaviors that govern large-scale mechanized verification in Anneal (`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` and `joshlf/anneal@beb778bb135474a67dc017c185d2753a60693d8c`):

1. **Kernel Memory Ceilings (`-M768` vs. `-M2048`), Eliminator Synthesis, LCNF String Hoisting, and Equality Reflection (`CargoLeanCostCold2*`)**:
   - Importing `Std` on Linux `x86_64` (`v4.34.1` `5045d0056413`) consumes `~785–800 MB` of resident set size (RSS) (`~680–695 MB` on `aarch64-apple-darwin`, vs. `~510–545 MB` for `Init`-only modules). Each `inductive` or `structure` declaration synthesizes 6–15 auxiliary eliminators (`.casesOn`, `.recOn`, `.noConfusion`, `.below`, `.brecOn`, `.ctorIdx`, `.ctorElim`), adding `~12–25 MB` of kernel heap pressure; breaching `-M768` mid-declaration triggers `(kernel) excessive memory consumption detected` followed by an LCNF compiler panic at `Lean.Compiler.LCNF.ExplicitBoxing:301:45`. Replacing enumeration inductives with `abbrev ... := Nat`, `noncomputable def`, and `set_option Elab.async false` eliminates eliminator and LCNF overhead (`SpecChallengeResolution.lean`, `0.557s`, `799.8 MB` RSS).
   - Embedding a `10,366`-byte source string literal and running `String.Slice` / `List Char` reductions in kernel WHNF (`EndCallSourceShape.lean.txt`) fails `-M768` at `894.6 MB` RSS with `compiler IR check failed at extractEndCall._closed_2. Error: unknown join point 'block_0'`, whereas binary `.amir` v3 byte-list parsers using `UInt8`, `bif`, and `LawfulBEq` (`SubstantiveMirByteParser.lean`, `7.937s`, `799.8 MB` RSS) pass `-j1 -M768`.
   - On 618-byte `List UInt8` payloads, proving equality via `(beq_iff_eq _ _).mpr rfl` (`CargoLeanCostCold2Binding.lean`, `0.421s`, `548.4 MB` RSS) is **24.1x faster** and uses **1,403.6 MB less RSS** than `by decide` (`CargoLeanCostCold2BindingGround.lean`, `10.148s`, `1,952.0 MB` RSS), while monolithic `decide` over full acceptance (`CargoLeanCostCold2Monolithic.lean`) exceeds `-M2048` (`2,099.7 MB` RSS).
2. **C++ Kernel Expression Representation, Absence of Hash-Consing, and the $O(N^2)$ vs. $O(N)$ Small-Step Scaling Laws**:
   - Lean 4's C++ kernel (`src/kernel/expr.cpp`, `replace_fn.cpp`, `type_checker.cpp`) does not hash-cons `expr` allocations and disables `replace_rec_fn::m_cache` whenever `m_rc == 1` (`is_likely_unshared`). Alternating `App` and `Lambda` binders in continuation-passing small-step proofs (`Arch 1b`) force `type_checker::infer_lambda` to call `instantiate_rev` on the entire remaining $(N - k)$-step subtree at every step $k$, cloning $O(N^2)$ unshared nodes (`4,715.554 ms` replay at $N = 500$). Binding intermediate states in a single contiguous `let`-block (`infer_let`) and stepping via structural suffix consumption (`SuffixReach`, `Arch 2`) reduces $N = 500$ kernel replay to **`78.048 ms` (60.42x speedup)**.
   - In `type_checker::reduce_nat` (`src/kernel/type_checker.cpp:703`), the C++ GMP fast path aborts immediately if `has_fvar(e) == true` before calling `whnf` on operands, causing lazy field projections out of `let`-bound state `FVar`s (`st_k.r0`) to get permanently stuck on `WellFounded.fix` in `Nat.shiftRight`, `Nat.div`, `Nat.mod`, `Nat.land`, `Nat.lor`, and `Nat.xor`. Unpacking states at step entry via `State.casesOn` (`reduce_rec` at `type_checker.cpp:462`) forces `whnf(major)` first and restores GMP reduction.
   - `String.beq` has no native C++ kernel reducer and costs **`~11.5 ms` per comparison** in the kernel UTF-8 interpreter, whereas structural `List.Mem` (`.tail`/`.head`) witnesses short-circuit on $O(1)$ pointer equality (`is_bi_equal`) and `Nat.beq` runs in `< 1 us` via GMP.
3. **Three-Layer Hybrid Validator Architecture, Hint-Driven `Language.Abstracts` Passes, Flat-Tuple Summaries, and Incremental `ShardCert` Replay (`3,001.5x` Speedup)**:
   - Combining **Layer 1** pre-proved GMP `Nat` side-condition reflection (`51.72x` faster than `omega`), **Layer 2** `cv_trans` `Nat`-domain reflection (`evalCvProg_sound`, `116.59x` faster than continuation lambdas at $N = 500$) and fused 5-instruction idioms (`step_idiom5`, `173.29x` faster), and **Layer 3** cut-point diamond convergence (`diamond_converge_step`, `201.35x` faster at $D = 10$), flat-tuple interprocedural call summaries (`call1_summary_flat_sound`, eliminating the $O(3^K)$ `{ s with ... }` record-update tree blowup to cut `TREE_NODES` at $K = 10$ by **1,800.8x** from `17,134,141` to `9,515`), and loop summaries (`625.01x` faster at $M = 100$), together with hint-driven `SymPlan` validation (`point3_evalSym_bodyN`), two-stage prefix caching in `TrustedBoundary.lean`, and per-function `ShardCert` sharding reduces 10-function crate kernel replay from **`5,042.587 ms` (`Stage 0`) to `157.056 ms` (`Stage 3`, `32.11x` speedup)** and single-function incremental replay to **`1.680 ms` (`Stage 4`, `3,001.54x` speedup)**.
4. **`<fn>._unsafe_rec` Emission in `noncomputable section` and Call-by-Name Kernel WHNF Spine Duplication ($O(2^K)$) in State Maps**:
   - In `v4.34.1`, `mkDefView` (`Lean/Elab/DefView.lean:219-225`) and `shouldGenCodeFor` (`Lean/Elab/PreDefinition/Basic.lean:134-141`) ignore `isNoncomputableSection`, so any recursive `def` lacking an explicit `noncomputable` keyword emits `<fn>._unsafe_rec` (`safety = .partial`) into `ModuleData.constants`, which `TrustedBoundary.lean:855` rejects. Explicit `noncomputable def` or recursion via `Nat.repeat`/`Nat.rec`/`List.foldr` emits zero `._unsafe_rec` constants.
   - In recursive state maps (`BinTrie`, `CanonList`), reconstructing child nodes from pattern-matched constructor variables in smart constructors (`BinTrie.mkNode`) and forcing the root of updated memory before exposing `.step` via a 2-line CPS combinator `ops.seq` prevents $O(2^K)$ call-by-name WHNF spine duplication ($K = 500$ replays in `245.97 ms` for `BinTrie` and merges $D = 8$ / $256$-path diamonds by `rfl` in `45.28 ms`, whereas `FnMap` times out at $>10^7$ heartbeats).
5. **`PersistentArray` and `PersistentHashMap` Runtime Continuity (`v4.30.0-rc2` → `v4.34.1`)**:
   - `setAux`..`set` in `Lean/Data/PersistentArray.lean` and `insertAux`..`insert` in `Lean/Data/PersistentHashMap.lean` remain byte-identical in their core path-copying logic between `v4.30.0-rc2` (`3dc1a088b6d2`) and `v4.34.1` (`5045d0056413`), while traversal/lookup helpers gain `@&` borrow annotations and `PersistentHashMap.alter` is added. Across 48 serial `lean --run` executions at $n \in \{8{,}192, 65{,}536\}$, all retained and discarded root updates produce identical semantic outputs, with retained map roots at $n = 65{,}536$ adding `~5.9 MB` median peak RSS over discarded roots in both versions.

## Applicability

This report applies to:

- **Lean 4 `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`arm64-apple-darwin24.6.0` binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`).
- **Lean 4 `v4.34.1`**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`x86_64-unknown-linux-gnu` release and `arm64-apple-darwin24.6.0` binary SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`; plus `aarch64-apple-darwin` build `d8ef7fd2d72efbe2ee2cefd1b62bf8ab2ff3f205` in historical replay ledgers).
- **Anneal repository revisions**:
  - `joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f` (`PRINCIPLES.md`, `AGENTS.md`) and `beb778bb135474a67dc017c185d2753a60693d8c` (`TrustedBoundary.lean` and verification framework);
  - Prototype commits `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, `e75556f5767705404404c0675c6d2d9bcee41d6f`, and `4f45f0a391a921ced9c9dc773b9a040dbc215d14`, and target Rust workload patterns from `google/zerocopy@1897ac488fd7bf2bc7bbe2cf7f1bfa0dcde2e1fc`.

To keep all semantic references self-contained without depending on unmerged prototype branches, Anneal's small-step execution and behavioral refinement types are defined inline as:

```lean
inductive StepResult (State : Type) where
  | step (next : State)
  | done
  | trapped
  | stuck

inductive Behavior (Obs : Type) where
  | terminates (trace : List Obs)
  | traps      (trace : List Obs)
  | diverges   (trace : Nat → Obs)
  | goesWrong

inductive ChoiceKind where
  | demonic
  | angelic
```

## Findings

### 1. Kernel Memory Ceilings (`-M768` vs. `-M2048`), Eliminator Overhead, LCNF String Hoisting, and Ground `decide` vs. Equality Reflection (`v4.34.1`)

Basis: **execution** + **source** + **derived** ([`support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/r12_m768_replay.json`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/r12_m768_replay.json), [`support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/r12_m2048_replay.json`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/r12_m2048_replay.json)).

#### 1.1 Base `.olean` Import Footprint and Per-`inductive` Eliminator Cascade
1. **Baseline RSS (`import Std` vs. `Init`-only)**: On Linux `x86_64` (`5045d0056413`), `Init`-only modules (`CargoLeanCostCold2Data.lean`) run at `521–566 MB` RSS (`395–438 MiB` on `aarch64-apple-darwin`), whereas modules importing `Std` start at `~785–800 MB` RSS (`~680–708 MB` on `aarch64-apple-darwin`).
2. **Per-`inductive` eliminator synthesis and LCNF Explicit-Boxing panic**: Each `inductive` or `structure` synthesizes `.casesOn`, `.recOn`, `.noConfusion`, `.noConfusionType`, `.below`, `.brecOn`, `.ctorIdx`, and `.ctorElim` (`~12–25 MB` kernel heap per type). When `-M768` trips during `inductive` elaboration, the kernel aborts with `(kernel) excessive memory consumption detected`, `.ctorElim` is never registered, and LCNF panics in `Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType` (`Lean.Compiler.LCNF.ExplicitBoxing:301:45: unreachable code has been reached`):

| Specimen | Type & Proof Representation | `-j1 -M768` Outcome (Linux `x86_64`) | Wall Time | Peak RSS |
| :--- | :--- | :--- | ---: | ---: |
| [`SpecValidationControls-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SpecValidationControls-initial.lean.txt) | `inductive ChallengeStatus \| validated \| rejectedWeak ... deriving DecidableEq` + computable defs | **Fails** (`(kernel) excessive memory consumption detected` at line 58 + 5 cascading errors) | `0.819s` | `808.7 MB` |
| [`SpecChallengeResolution.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SpecChallengeResolution.lean) | `abbrev ChallengeStatus : Type := Nat` + `noncomputable def` + `set_option Elab.async false` | **Passes** (all 8 theorems verified, `#print axioms` clean) | `0.557s` | `799.8 MB` |
| [`SpecValidation.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SpecValidation.lean) | Zero-`inductive` `abbrev` + `noncomputable def` + `set_option Elab.async false` | **Passes** (all 8 theorems verified) | `0.558s` | `799.8 MB` |

#### 1.2 LCNF String Literal Hoisting vs. Wire-Format `Nat` and `UInt8` Parsers
- In [`EndCallSourceShape.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/EndCallSourceShape.lean.txt) (`15,280` B), embedding a `10,366`-byte Markdown string literal (`memoryMd`) and proving `extractEndCall memoryMd = some (actualBasic, actualTree)` fails `-M768` after `2.186s` (`894,582,784` B RSS) with `compiler IR check failed at extractEndCall._closed_2. Error: unknown join point 'block_0'` and `ExplicitBoxing:301:45`.
- By contrast, [`MirWireParser.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/MirWireParser.lean) (`13,448` B, 6-word `List Nat` packet parser) checks in `0.625s` under `-j1 -M768`, and [`SubstantiveMirByteParser.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SubstantiveMirByteParser.lean) (`27,631` B, 639 lines, prelude-only `.amir` v3 `List UInt8` binary wire parser using `bif` and `LawfulBEq`) checks 7 compiled Rust MIR byte packages by kernel `rfl` in `7.937s` (`799.8 MB` RSS) under `-j1 -M768`.

#### 1.3 Compositional Continuation Reuse vs. Phase-Invariant Scaling (`ProofCost*` & `ProgramCost*`)
In the 12-module `ProofCost*` suite, repeating a cached 3-operation memory cycle (`allocate`, `store`, `deallocate`) $k \in \{1, 4, 16\}$ times is $O(1)$ (`0.336–0.360s`), but extending the body to two live buffers requires re-proving all 9 phase constructors in `ProofCostInvariantExtension.lean` (`12,916` B source, `140,864` B `.olean`, `0.654s`), whereas `ProofCostContinuation.lean` (`7,452` B source, `66,464` B `.olean`, `0.553s`) composes existing per-operation continuation lemmas:

| Module | Source Bytes | `.olean` Bytes | Fresh Linux `-M2048` Wall (s) | Fresh Linux Max RSS (KB) | Historical Darwin `-M768` Wall (s) |
| :--- | ---: | ---: | ---: | ---: | ---: |
| [`ProofCostCommon.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostCommon.lean) | 17,135 | 175,880 | `1.106` | `814,632` | `0.629` |
| [`ProofCostFrames.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostFrames.lean) | 8,275 | 94,008 | `0.917` | `804,256` | `0.483` |
| [`ProofCostContinuationBase.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostContinuationBase.lean) | 920 | 32,768 | `0.345` | `785,292` | `0.214` |
| [`ProofCostContinuation.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostContinuation.lean) | 7,452 | 66,464 | `0.553` | `798,352` | `0.341` |
| [`ProofCostContinuationClientOne.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostContinuationClientOne.lean) | 791 | 29,648 | `0.336` | `786,660` | `0.223` |
| [`ProofCostContinuationClientFour.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostContinuationClientFour.lean) | 797 | 29,672 | `0.360` | `785,800` | `0.213` |
| [`ProofCostContinuationClientSixteen.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostContinuationClientSixteen.lean) | 815 | 29,720 | `0.350` | `786,656` | `0.215` |
| [`ProofCostInvariant.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostInvariant.lean) | 6,600 | 91,008 | `0.531` | `800,664` | `0.331` |
| [`ProofCostInvariantExtension.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostInvariantExtension.lean) | 12,916 | 140,864 | `0.654` | `809,524` | `0.399` |
| [`ProofCostInvariantClientOne.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostInvariantClientOne.lean) | 783 | 29,480 | `0.356` | `786,756` | `0.215` |
| [`ProofCostInvariantClientFour.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostInvariantClientFour.lean) | 789 | 29,504 | `0.350` | `786,752` | `0.217` |
| [`ProofCostInvariantClientSixteen.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProofCostInvariantClientSixteen.lean) | 807 | 29,552 | `0.336` | `786,752` | `0.217` |

Across unrolled straight-line horizons $N \in \{8, 32, 128\}$ (`ProgramCost*`), the continuation route scales cleanly to $N = 128$ (`0.703s`, `814.4 MB` RSS), whereas the 130-constructor `Phase` inductive in `ProgramCostInvariant128-initial.lean.txt` breaches `-M768` with 74 kernel excessive-memory errors:

| Module | Horizon $N$ | Source Bytes | `.olean` Bytes | Fresh Linux `-M2048` Wall (s) | Fresh Linux Max RSS (KB) | Historical Darwin `-M768` Wall (s) / RSS |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| [`ProgramCostCommon.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostCommon.lean) | shared | 39,602 | 645,448 | `1.250` | `825,548` | `0.733s` / `719.2 MB` |
| [`ProgramCostPrimitives.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostPrimitives.lean) | shared | 15,320 | 147,552 | `0.940` | `812,020` | `0.583s` / `712.7 MB` |
| [`ProgramCostSmallControls.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostSmallControls.lean) | $N=8$ controls | 13,223 | 173,272 | `0.908` | `808,228` | `0.580s` / `707.0 MB` |
| [`ProgramCostContinuation8.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostContinuation8.lean) | $N=8$ | 11,497 | 80,680 | `0.600` | `806,340` | `0.382s` / `703.7 MB` |
| [`ProgramCostInvariant8.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostInvariant8.lean) | $N=8$ | 11,663 | 136,416 | `0.624` | `812,932` | `0.422s` / `710.1 MB` |
| [`ProgramCostContinuation32.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostContinuation32.lean) | $N=32$ | 15,769 | 127,480 | `0.646` | `806,880` | `0.431s` / `706.5 MB` |
| [`ProgramCostInvariant32.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostInvariant32.lean) | $N=32$ | 32,152 | 418,752 | `1.131` | `844,512` | `0.708s` / `739.1 MB` |
| [`ProgramCostContinuation128.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostContinuation128.lean) | $N=128$ | 19,799 | 206,536 | `0.703` | `814,444` | `0.488s` / `707.2 MB` |
| [`ProgramCostInvariant128-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ProgramCostInvariant128-initial.lean.txt) | $N=128$ | 97,876 | *failed* | *quarantined* | *quarantined* | **Fails `-M768`** at `1.311s` / `839.4 MB` (74 kernel excessive-memory errors) |

Similarly, 9-deep right-associated product projections (`.2.2.2.2.2.2.2.2.2` in [`ServiceIntervals-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ServiceIntervals-initial.lean.txt), failing `-M768` at `1.876s` / `820.9 MB` RSS due to $O(k^2)$ implicit type arguments) and ~66 chained `rw` steps over a 9-field tuple ([`ClaimChangeReport-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ClaimChangeReport-initial.lean.txt), failing `-M768` at `1.304s` / `807.3 MB` RSS due to 66 `Eq.ndrec` motive copies) are resolved by per-field congruence helpers in [`ClaimChangeResolution.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ClaimChangeResolution.lean) (`0.636s` under `-j1 -M768`).

#### 1.4 Ground `by decide` vs. `(beq_iff_eq _ _).mpr rfl` and Symbolic `∀ base : Nat` Step Factoring
| Module | Proof Strategy | Fresh Linux `-M2048` Wall (s) | Fresh Linux Max RSS (KB) | Historical Darwin `-M2048` Wall (s) / RSS |
| :--- | :--- | ---: | ---: | :--- |
| [`CargoLeanCostCold2Data.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/CargoLeanCostCold2Data.lean) | Data definitions only (`14,888` B) | `0.567` | `543,504` | `0.369s` / `430.5 MiB` |
| [`CargoLeanCostCold2Binding.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/CargoLeanCostCold2Binding.lean) | Factored `(beq_iff_eq _ _).mpr rfl` on `cold2BindingCheck` | **`0.421`** | **`548,436`** | **`0.327s` / `435.0 MiB`** |
| [`CargoLeanCostCold2BindingGround.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/CargoLeanCostCold2BindingGround.lean) | Ground `by decide` on the **exact same** `cold2BindingCheck` proposition | **`10.148`** | **`1,951,988`** | **`5.544s` / `1,811.4 MiB`** |
| `CargoLeanCostCold2Composed` | 11-module factored composition of full `cold2` acceptance | `4.896` | `1,000,360` | `2.659s` / `872.0 MiB` |
| [`CargoLeanCostCold2Monolithic.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/CargoLeanCostCold2Monolithic.lean) | Monolithic `by decide` on full `cold2` acceptance | **Fails `-M2048`** (`11.585s`) | **`2,099,692`** | `5.657s` / `1,816.8 MiB` |

In [`StatefulGenericLibraryH3H7Core.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/StatefulGenericLibraryH3H7Core.lean) (`22.992s`, `749,344 KB` RSS), ground execution of a 3-crate `.amir` v3 call tree (`evalSteps 60`) checks in `< 0.5s` via `decide`, whereas universal symbolic proofs (`∀ base : Nat`) over 60 steps must be factored through single-step lemmas (`evalStepGenericSlot_true_universal`) to stay within `400,000` heartbeats and `749.3 MB` RSS.

---

### 2. Lean `v4.34.1` C++ Kernel Cost Model: Absence of Hash-Consing, `infer_lambda` vs. `infer_let`, GMP `has_fvar` Hazard, and `String.beq` Tax

Basis: **source** + **execution** + **derived** (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`: `src/kernel/expr.h`, `expr.cpp`, `type_checker.h`, `type_checker.cpp`, `instantiate.cpp`, `replace_fn.cpp`, `expr_eq_fn.cpp`, `inductive.cpp`; [`support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/BenchmarkProofStrategies.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/BenchmarkProofStrategies.lean)).

#### 2.1 Absence of Hash-Consing, `replace_rec_fn::m_cache`, and $O(N^2)$ `infer_lambda` Cloning vs. $O(N)$ Contiguous `infer_let`
1. **No expression hash-consing and `m_rc == 1` cache bypass**: Each `expr_cell` (`src/kernel/expr.h:99-145`) stores an atomic reference count `m_rc`, an 8-bit `m_kind`, and a 64-bit `m_data` word (32-bit hash, 16-bit loose bvar range, and `has_fvar`, `has_expr_mvar`, `has_univ_mvar`). Two structurally identical expressions constructed at different times have `!is_eqp(a, b)`. In `replace_rec_fn::operator()` (`src/kernel/replace_fn.cpp:34-46`), `m_cache` is used **only when `!is_likely_unshared(e)` (`m_rc > 1`)**. Whenever `instantiate_fn` (`src/kernel/instantiate.cpp:25-44`) substitutes into a binder body containing a loose `BVar`, every newly allocated node along the path has `m_rc == 1`, disabling `m_cache` on all subsequent substitutions.
2. **Kernel caches (`src/kernel/type_checker.h:32-44`)**: `m_infer_type[2]`, `m_whnf_core`, `m_whnf`, `m_success`, and `m_failure` key by `expr_hash` and `is_bi_equal` (`src/kernel/expr_eq_fn.cpp:17-58`), which short-circuits in $O(1)$ on `is_eqp(a, b)` but traverses both trees when `!is_eqp(a, b)`. Note that `whnf_core` (`type_checker.cpp:503`) unfolds `FVar`s before checking `m_whnf_core`, whereas `whnf(e)` (`type_checker.cpp:749, 771`) caches `let`-bound `FVar` unfoldings in `m_st->m_whnf`.
3. **Why alternating `App`/`Lambda` continuations (`Arch 1b`) and global PC indexing (`Arch 1a`) are $O(N^2)$ while contiguous `infer_let` + `SuffixReach` (`Arch 2`) is $O(N)$**:
   - In `Arch 1b` (`reachesPrefix_safeAndEnsures_of_step`), `App` and `fun n_k hr_k =>` alternate at every step $k$, so `while (is_lambda(e))` in `type_checker::infer_lambda` (`type_checker.cpp:129-142`) peels only 2 binders before calling `instantiate_rev` on the entire remaining $(N - k)$-step subtree, cloning $\sum_{k=1}^N O(N - k) = O(N^2)$ nodes with `m_rc == 1` (`4,715.554 ms` replay at $N = 500$).
   - In `Arch 1a` (flat `Reach.step`), indexing `prog[s_k.pc]?` in a length-$N$ list performs $k$ `List.getElem?_cons_succ` unfoldings at step $k$ ($\sum_{k=0}^{N-1} O(k) = O(N^2)$, `4,681.158 ms` replay at $N = 500$).
   - In `Arch 2`, binding all $N + 1$ closed states `let st_0 := ...; ...; let st_N := ...; body` lets `while (is_let(e))` in `type_checker::infer_let` (`type_checker.cpp:208-230`) process each closed `let_value` in $O(1)$ (`!has_loose_bvars`, `instantiate.cpp:60-61`) and call `instantiate_rev` on `body` **once** in $O(N)$, while `SuffixReach (i :: rest)` matches the head instruction in $O(1)$ (**`78.048 ms` replay at $N = 500$, a 60.42x speedup**).

#### 2.2 Complete Inventory of Native C++ GMP Kernel Reducers (`type_checker::reduce_nat`) and the `has_fvar` Bypass Hazard
`type_checker::reduce_nat` (`src/kernel/type_checker.cpp:702-733`) is the **sole** native arithmetic fast path in the Lean `v4.34.1` C++ kernel (no native reducers exist for `BitVec`, `UInt64`, `Fin`, `Int`, `ByteArray`, or `String`):

| Lean Constant | Arity | C++ Implementation (`src/kernel/type_checker.cpp`) | Preconditions & Resource Guards | Fallback When Guard / `has_fvar` Fails |
| :--- | :---: | :--- | :--- | :--- |
| `Nat.succ` | 1 | `reduce_unary_nat_op`: `a + 1` (line `706`) | `!has_fvar(e)`; `v1 = whnf(e1)` is `Nat.zero` or `natVal` | Constructor `Nat.succ e1` (stays in WHNF) |
| `Nat.add` | 2 | `reduce_bin_nat_op`: `a + b` (line `710`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Structural recursion on arg 2 (`Nat.brecOn`, $O(b)$) |
| `Nat.sub` | 2 | `reduce_bin_nat_op`: `a <= b ? 0 : a - b` (line `711`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Structural recursion on arg 2 (`Nat.brecOn`, $O(b)$) |
| `Nat.mul` | 2 | `reduce_bin_nat_op`: `a * b` (lines `667-675, 712`) | `!has_fvar(e)`; `v1.size() + v2.size() <= g_nat_max_size` (`128 MiB`) | Structural recursion on arg 2 ($O(b)$ additions) |
| `Nat.pow` | 2 | `reduce_pow`: `mpz::pow(a, b)` (lines `643-665, 713`) | `!has_fvar(e)`; `b <= UINT_MAX`; `v1.log2() * b <= g_nat_max_size * 8` | Structural recursion on exponent $b$ |
| `Nat.gcd` | 2 | `reduce_bin_nat_op`: `gcd(a, b)` (line `714`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `WellFounded.fix` (**stuck in kernel `whnf`**) |
| `Nat.mod` | 2 | `reduce_bin_nat_op`: `b == 0 ? 0 : a % b` (line `715`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.modCore` via `WellFounded.fix` (**stuck if $a \ge b$**) |
| `Nat.div` | 2 | `reduce_bin_nat_op`: `b == 0 ? 0 : a / b` (line `716`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.divCore` via `WellFounded.fix` (**stuck if $a \ge b$**) |
| `Nat.beq` | 2 | `reduce_bin_nat_pred`: `a == b` (line `717`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Mutual structural recursion ($O(\min(a, b))$) |
| `Nat.ble` | 2 | `reduce_bin_nat_pred`: `a <= b` (line `718`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Mutual structural recursion ($O(\min(a, b))$) |
| `Nat.land` | 2 | `reduce_bin_nat_op`: `a & b` (line `719`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.bitwise and` via `WellFounded.fix` (**stuck**) |
| `Nat.lor` | 2 | `reduce_bin_nat_op`: `a \| b` (line `720`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.bitwise or` via `WellFounded.fix` (**stuck**) |
| `Nat.xor` | 2 | `reduce_bin_nat_op`: `a ^ b` (line `721`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.bitwise bne` via `WellFounded.fix` (**stuck**) |
| `Nat.shiftLeft` | 2 | `reduce_shift_left`: `a << b` (lines `677-686, 722`) | `!has_fvar(e)`; `b <= UINT_MAX`; `v1.size() + b/8 <= g_nat_max_size` | Structural recursion on shift count $b$ ($O(b)$) |
| `Nat.shiftRight` | 2 | `reduce_shift_right`: `a >> b` (lines `688-700, 723`) | `!has_fvar(e)`; `b <= UINT_MAX` | Structural recursion on shift count $b$ $\to$ `Nat.div 2` (**stuck if $b > 0$**) |

- **The `has_fvar` GMP bypass hazard and `State.casesOn` fix**: Both `type_checker::reduce_nat` (`type_checker.cpp:703`, `if (has_fvar(e)) return none_expr();`) and `Lean.Meta.WHNF.withNatValue` (`src/lean/Lean/Meta/WHNF.lean:994`) check `has_fvar` on the outer application *before* calling `whnf` on arguments. When `st_k` is a `let`-bound `FVar`, lazy projections like `Nat.xor st_k.r0.toNat st_k.r2.toNat` or `Nat.shiftRight (s.getReg src).toNat 4` have `has_fvar == true`, bypassing GMP and getting stuck on `WellFounded.fix`. Wrapping `stepInstr` / `evalStep` in `State.casesOn s` at function entry forces `reduce_rec` (`type_checker.cpp:462`) to call `whnf(s)` first, unfolding `s` to a closed `State.mk` constructor (`has_fvar == false`) before arithmetic expressions are constructed.
- **The `String.beq` UTF-8 interpreter bottleneck (`~11.5 ms` per comparison)**: In `src/kernel/expr.cpp:427-446`, `string_lit_to_constructor` expands a $B$-byte string literal into $B$ `UInt8.ofBitVec` list cells. Evaluating `lookupFn crateProg fnName` by `rfl` across 4 `core` callees (10 `String.beq` comparisons) takes **`114.645 ms` (`11.46 ms` / comparison)** (`10.294 ms` for index 0 `"core::mem::size_of"`, `24.244 ms` for index 1 `"core::num::usize::checked_add"`, `35.851 ms` for index 2 `"core::num::NonZeroUsize::new"`, `44.256 ms` for index 3 `"core::option::Option::unwrap_or"`). Structural `List.Mem` witnesses (`.tail`/`.head`) use `is_bi_equal` pointer equality in nanoseconds, and interning `FnId := Nat` uses `Nat.beq` in `< 1 us`.

---

### 3. Empirical Scaling Across 6 Proof Architectures (`Suite A`, `Suite B`, Side Conditions, `Language.Abstracts`, Flat-Tuple Summaries, and `Stage 0`..`Stage 4`)

Basis: **execution** + **derived** ([`support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/suite_a_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/suite_a_results.json), [`support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/suite_b_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/suite_b_results.json), [`support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/side_condition_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/side_condition_results.json), [`support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/unified_benchmark_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/unified_benchmark_results.json)).

#### 3.1 Suite A: Straight-Line 5-Instruction Checked-Arithmetic + Bitwise-Mix Idioms ($N \in \{10, 50, 100, 250, 500\}$)
| $N$ | Architecture | Elab Time (ms) | Kernel Replay (ms) | Kernel Replay ($\mu$s) | `.olean` Size (Bytes) | `DECLS` | `DAG_NODES` | `TREE_NODES` | Replay Speedup vs. Arch 1b |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **10** | Arch 1a (Flat `Reach.step`) | 273.0 | 3.855 | 3,855 | 13,576 | 1 | 250 | 3,232 | 1.07x |
| **10** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 273.4 | 4.136 | 4,136 | 19,096 | 1 | 361 | 4,750 | 1.00x |
| **10** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 265.8 | 1.812 | 1,812 | 18,544 | 1 | 341 | 2,221 | 2.28x |
| **10** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 227.1 | **0.803** | **803** | 12,416 | 1 | 173 | 457 | **5.15x** |
| **10** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 221.2 | 1.446 | 1,446 | 5,912 | 1 | 40 | 52 | 2.86x |
| **10** | Arch 5 (Cut-Point Block `evalBlock_step`) | 229.7 | 2.345 | 2,345 | 12,456 | 1 | 170 | 377 | 1.76x |
| **10** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **221.1** | 1.153 | 1,153 | **5,632** | 1 | **33** | **44** | 3.59x |
| **50** | Arch 1a (Flat `Reach.step`) | 520.2 | 45.528 | 45,528 | 40,896 | 1 | 1,086 | 16,032 | 1.04x |
| **50** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 505.0 | 47.134 | 47,134 | 62,736 | 1 | 1,557 | 23,390 | 1.00x |
| **50** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 364.2 | 7.194 | 7,194 | 56,680 | 1 | 1,387 | 27,852 | 6.55x |
| **50** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 275.0 | **2.740** | **2,740** | 26,008 | 1 | 549 | 5,512 | **17.20x** |
| **50** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 234.5 | 5.676 | 5,676 | 5,912 | 1 | 40 | 52 | 8.30x |
| **50** | Arch 5 (Cut-Point Block `evalBlock_step`) | 302.1 | 9.801 | 9,801 | 27,400 | 1 | 570 | 5,102 | 4.81x |
| **50** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **232.3** | 4.324 | 4,324 | **5,632** | 1 | **33** | **44** | 10.90x |
| **100** | Arch 1a (Flat `Reach.step`) | 953.3 | 178.425 | 178,425 | 74,832 | 1 | 2,116 | 32,032 | 1.00x |
| **100** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 1,119.7 | 178.401 | 178,401 | 117,072 | 1 | 3,037 | 46,690 | 1.00x |
| **100** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 498.5 | 14.466 | 14,466 | 103,144 | 1 | 2,658 | 98,417 | 12.33x |
| **100** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 312.7 | **5.228** | **5,228** | 41,616 | 1 | 978 | 19,537 | **34.12x** |
| **100** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 272.7 | 10.988 | 10,988 | 5,920 | 1 | 40 | 52 | 16.24x |
| **100** | Arch 5 (Cut-Point Block `evalBlock_step`) | 379.7 | 19.318 | 19,318 | 45,008 | 1 | 1,039 | 18,702 | 9.23x |
| **100** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **266.5** | 8.157 | 8,157 | **5,640** | 1 | **33** | **44** | 21.87x |
| **250** | Arch 1a (Flat `Reach.step`) | 3,535.2 | 1,144.303 | 1,144,303 | 179,296 | 1 | 5,266 | 80,032 | 1.03x |
| **250** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 7,080.0 | 1,173.815 | 1,173,815 | 282,736 | 1 | 7,537 | 116,590 | 1.00x |
| **250** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 962.6 | 37.546 | 37,546 | 243,880 | 1 | 6,446 | 579,287 | 31.26x |
| **250** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 423.6 | **13.506** | **13,506** | 87,424 | 1 | 2,178 | 115,367 | **86.91x** |
| **250** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 328.5 | 27.934 | 27,934 | 5,920 | 1 | 40 | 52 | 42.02x |
| **250** | Arch 5 (Cut-Point Block `evalBlock_step`) | 586.7 | 50.413 | 50,413 | 96,112 | 1 | 2,337 | 113,317 | 23.28x |
| **250** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **313.0** | 19.896 | 19,896 | **5,640** | 1 | **33** | **44** | 59.00x |
| **500** | Arch 1a (Flat `Reach.step`) | 12,366.4 | 4,681.158 | 4,681,158 | 354,248 | 1 | 10,512 | 160,032 | 1.01x |
| **500** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 55,796.6 | 4,715.554 | 4,715,554 | 559,688 | 1 | 15,033 | 233,090 | 1.00x |
| **500** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 1,905.5 | 78.048 | 78,048 | 479,496 | 1 | 12,781 | 2,254,787 | 60.42x |
| **500** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 627.5 | **27.212** | **27,212** | 164,728 | 1 | 4,205 | 449,947 | **173.29x** |
| **500** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 423.5 | 55.694 | 55,694 | 5,920 | 1 | 40 | 52 | 84.67x |
| **500** | Arch 5 (Cut-Point Block `evalBlock_step`) | 957.4 | 103.992 | 103,992 | 182,712 | 1 | 4,542 | 445,822 | 45.35x |
| **500** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **383.7** | 40.446 | 40,446 | **5,640** | 1 | **33** | **44** | **116.59x** |

#### 3.2 Suite B: Chained Diamonds ($D \in \{2..10\}$), Multi-Call ($K \in \{2..20\}$), Loops, and Side-Condition Reflection
| Workload | Parameter | Paths / Instrs | Architecture | Elab Time (ms) | Kernel Replay (ms) | Kernel Replay ($\mu$s) | `.olean` Size (Bytes) | `DAG_NODES` | `TREE_NODES` | Arch 5 Replay Speedup |
| :--- | ---: | ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Diamonds** | $D = 2$ | $2^2 = 4$ paths | Arch 4 ($2^D$ Path Split) | 233.3 | 4.837 | 4,837 | 13,056 | 186 | 550 | — |
| **Diamonds** | $D = 2$ | $2^2 = 4$ paths | Arch 5 ($O(D)$ `diamond_converge_step`) | 242.2 | **3.372** | **3,372** | **12,496** | **162** | **395** | **1.43x** |
| **Diamonds** | $D = 6$ | $2^6 = 64$ paths | Arch 4 ($2^D$ Path Split) | 720.3 | 122.465 | 122,465 | 97,216 | 2,474 | 12,598 | — |
| **Diamonds** | $D = 6$ | $2^6 = 64$ paths | Arch 5 ($O(D)$ `diamond_converge_step`) | **296.1** | **9.011** | **9,011** | **20,272** | **362** | **1,687** | **13.59x** |
| **Diamonds** | $D = 10$ | $2^{10} = 1,024$ paths | Arch 4 ($2^D$ Path Split) | 11,488.6 | 2,998.350 | 2,998,350 | 1,434,176 | 38,962 | 243,646 | — |
| **Diamonds** | $D = 10$ | $2^{10} = 1,024$ paths | Arch 5 ($O(D)$ `diamond_converge_step`) | **327.3** | **14.891** | **14,891** | **28,048** | **562** | **3,747** | **201.35x** |
| **Multi-Call** | $K = 2$ | 40 instrs | Arch 4 (Inlined Call `rfl`) | 247.0 | 4.496 | 4,496 | 5,944 | 40 | 52 | — |
| **Multi-Call** | $K = 2$ | 40 instrs | Arch 5 (`call_summary_sound`) | **223.1** | **0.248** | **248** | 7,160 | 60 | 98 | **18.13x** |
| **Multi-Call** | $K = 10$ | 200 instrs | Arch 4 (Inlined Call `rfl`) | 305.7 | 20.786 | 20,786 | 5,944 | 40 | 52 | — |
| **Multi-Call** | $K = 10$ | 200 instrs | Arch 5 (`call_summary_sound`) | **222.7** | **0.454** | **454** | 8,696 | 108 | 1,474 | **45.78x** |
| **Multi-Call** | $K = 20$ | 400 instrs | Arch 4 (Inlined Call `rfl`) | 377.2 | 41.406 | 41,406 | 5,944 | 40 | 52 | — |
| **Multi-Call** | $K = 20$ | 400 instrs | Arch 5 (`call_summary_sound`) | **221.9** | **0.668** | **668** | 10,616 | 168 | 5,714 | **61.99x** |
| **Loop** | $M = 10$ | 50 instrs | Arch 4 (Unrolled Loop `rfl`) | 262.6 | 7.534 | 7,534 | 5,944 | 40 | 52 | — |
| **Loop** | $M = 10$ | 50 instrs | Arch 5 (`loop_summary_sound`) | **213.3** | **0.127** | **127** | 7,128 | 48 | 68 | **59.32x** |
| **Loop** | $M = 100$ | 500 instrs | Arch 4 (Unrolled Loop `rfl`) | 527.5 | 76.251 | 76,251 | 5,944 | 40 | 52 | — |
| **Loop** | $M = 100$ | 500 instrs | Arch 5 (`loop_summary_sound`) | **218.4** | **0.122** | **122** | 7,128 | 48 | 68 | **625.01x** |
| **Loop (Symbolic)** | `m : Nat` | `5 * m` instrs | Arch 5 (`loop_summary_sound`) | **217.4** | **0.134** | **134** | 8,528 | 68 | 208 | **$\infty$ (Symbolic)** |

For 50 arithmetic/pointer side conditions ([`ProbeSideConditionReflection.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbeSideConditionReflection.lean)), pre-proved `Theory` reflection (`rfl`) checks all 50 declarations in **`3.312 ms`** (`62,856` B `.olean`, `1,006` DAG nodes, `5,500` tree nodes) vs. **`171.299 ms`** (`516,760` B `.olean`, `14,091` DAG nodes, `374,710` tree nodes) for `omega` (**51.72x speedup**), and bundling 50 intervals into `checkIntervalBatch_sound rfl` produces **12 DAG nodes** (`3,872` B `.olean`, **39.96x speedup**).

#### 3.3 Hint-Driven `Language.Abstracts` Validators, Flat-Tuple `Call1Summary`, and 5-Stage End-to-End Crate Verification
- **Hint-driven `SymPlan` validation ([`ProbePreprovedPasses.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbePreprovedPasses.lean))**: Emitting a `SymPlan` witness (`point3_evalSym_body12`: `59` DAG / `223` tree / `17,221 us`) beats unhinted in-kernel `computePlan` (`point2_lowerToPure_body12`: `60` DAG / `227` tree / `22,726 us`) and per-step tactical stepping (`point1_tactical_body12`: `665` DAG / `34,705` tree / `21,328 us`), while pre-composing pass chains (`point4_preproved_pipeline_body12`: `5` DAG / `9` tree / `67 us`) beats per-function chaining (`262 us`) by **3.91x**.
- **Fixing `MirLang.sem` single-entry call table and `{ s with ... }` $O(3^K)$ tree blowup ([`ProbePreprovedSummaries.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbePreprovedSummaries.lean))**: Changing `MirLang.Prog` from `MirBody` to `MirProg × MirBody` resolves interprocedural `Terminator.call` targets (`Trusted/MirSemantics.lean:1794`), and replacing `{ s with ... }` post-states (`summary_caller10`: `916` DAG / `17,134,141` tree / `6,626 us`) with flat constructor tuples `⟨curBody, locals, blk, stmtIdx, stack⟩` (`summary_flat_caller10`: `814` DAG / **`9,515` tree** / `6,393 us`) reduces unshared tree size by **1,800.8x**.
- **Unified 5-Stage Benchmark ([`UnifiedEndToEndStack.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/UnifiedEndToEndStack.lean), [`unified_benchmark_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/unified_benchmark_results.json))**:

| Stage | Architecture & Active Optimizations | Elab Time (ms) | Elab Speedup vs. S0 | Stage-2 Kernel Replay (ms) | Replay Speedup vs. S0 | Replayed `.olean` Bytes | Replayed `DECLS` | Replayed `DAG_NODES` | Replayed `TREE_NODES` |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Stage 0** | **Baseline:** `Theory` in `locals` + continuation lambdas + `{ s with ... }` + inlined calls + `omega` + `by decide` TCB lookup | `18,750.3` | `1.00x` | `5,042.587` | `1.00x` | `5,148,336` | `906` | `86,385` | `51,614,627` |
| **Stage 1** | **+ Two-Stage Pre-Audited `Theory` in `base`:** `UnifiedEndToEndStack` in `base`; only `CrateMir + Stage0_Proof` replayed | `16,131.7` | `1.16x` | `4,787.113` | `1.05x` | `1,729,760` | `151` | `33,489` | `50,745,839` |
| **Stage 2** | **+ Flat-Tuple & Structural Proof Hygiene:** `SuffixReach` with `State.casesOn`, contiguous `let st_k`, structural `.tail`/`.head` TCB witnesses, `checkSideCondBatch_sound rfl` | `5,593.1` | `3.35x` | `512.698` | `9.84x` | `1,301,592` | `101` | `22,952` | `567,704` |
| **Stage 3** | **+ 3-Layer Hybrid `Theory` Validators:** `evalCvProg_sound` (`cv_trans`), `evalIdiomPlan_sound`, `diamond_converge_step`, `CalleeSummary`, `loop_summary_sound` | `813.8` | `23.04x` | `157.056` | `32.11x` | `581,048` | `73` | `2,708` | `51,858` |
| **Stage 4** | **+ Per-Function `ShardCert` Incremental Sharding:** 9/10 unchanged shards in `base`; re-verifying `Shard 9` loop + `Stage4_Root` (`CrateTheorem`) | `472.7` | `39.67x` | **`1.680`** | **`3,001.54x`** | **`30,008`** | **`3`** | **`384`** | **`6,714`** |

Across all 10 per-function shards (`Shard 0`..`Shard 9`), Stage-4 incremental replay ranges from `1.680 ms` (`Shard 9` loop) to `11.279 ms` (`Shard 8` diamonds), and all 5 positive boundary canaries pass while all 5 negative soundness canaries fail with `returncode == 1`.

---

### 4. `<fn>._unsafe_rec` Emission in `noncomputable section` and Call-by-Name State-Map WHNF Scaling (`v4.34.1`)

Basis: **source** + **execution** (`src/Lean/Elab/PreDefinition/{Main,Basic}.lean`, `src/Lean/Elab/DefView.lean`, `src/Lean/Compiler/LCNF/{ToLCNF,ToImpure,Main}.lean`, `src/Lean/Environment.lean`, `src/Lean/Replay.lean`; [`support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/UnsafeRecProbe.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/UnsafeRecProbe.lean), [`support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/PreludeRecProbe.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/PreludeRecProbe.lean), [`support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/StateMapBenchmarks.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/StateMapBenchmarks.lean), [`support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/RefinementBridge.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/RefinementBridge.lean), [`support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/benchmark_results.json`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/benchmark_results.json)).

#### 4.1 `<fn>._unsafe_rec` in `ModuleData.constants` and `noncomputable section` Scope Leakage
In `Lean/Elab/DefView.lean:219-225` (`mkDefView`), `(← getScope).isNoncomputable` is **not** propagated into `modifiers.computeKind`, and both branches of `shouldGenCodeFor` (`Lean/Elab/PreDefinition/Basic.lean:134-141`) return `!preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable`. Consequently, every recursive `def` (structural, well-founded, `partial_fixpoint`, mutual, `where`/`let rec`, or `deriving DecidableEq`/`BEq`/`Repr`/`Ord` on a recursive `inductive`) without an explicit `noncomputable` keyword calls `addAndCompilePartialRec` (`Basic.lean:280-296`), which inserts `<fn>._unsafe_rec` (`safety = .partial`) into `env.checked` (`ModuleData.constants`), causing `TrustedBoundary.lean:855` (`if ci.isUnsafe || ci.isPartial`) to reject the module. Marking recursive definitions `noncomputable def`—or expressing computable recursion via `Nat.repeat`, `Nat.rec` (`@[csimp] theorem Nat.rec_eq_recCompiled`), or `List.foldr` from `foundation-lock.json` ([`PreludeRecProbe.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/PreludeRecProbe.lean))—produces zero `isUnsafe || isPartial` constants.

#### 4.2 Call-by-Name Kernel WHNF Spine Duplication ($O(2^K)$) and 5 State-Map Representations
Because `whnf_core` is call-by-name, wildcard arms in smart constructors (`| _, _, _ => .node v l r`) and lazy `.step { s with mem := ops.set ... }` returns leave unreduced `ops.set` redexes on the state spine that duplicate at every subsequent read+write step ($O(2^K)$, timing out at $K = 50$). Reconstructing child nodes from matched constructor variables in `BinTrie.mkNode` / `CanonList.cons` and forcing the root of updated memory via CPS `ops.seq` restores linear $O(K)$ scaling and $O(D)$ diamond join merging by `rfl`:

| Representation | Type in `prelude` | Disjoint Update Commutativity by `rfl` | Dead-Slot Erasure by `rfl` | Asymmetric Branch Join by `rfl` | `get_set` Proof Lines | $K=500$ `evalBlock` Elab / Replay (ms) | $D=4$ Merged Elab / Replay (ms) | $D=8$ ($256$ paths) Merged Elab / Replay (ms) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`BinTrie` (Rep 5)** | `inductive BinTrie` (`leaf \| node val l r`) | Yes | Yes (`.node none .leaf .leaf` $\mapsto$ `.leaf`) | Yes | 58 | 2329.4 / **245.97** | **261.8** / **23.38** | **426.2** / **45.28** |
| **`CanonList` (Rep 2b)** | `List (Option Val)` (trailing `none`s trimmed) | Yes | Yes (`CanonList.cons none []` $\mapsto$ `[]`) | Yes | **18** | 2798.0 / **260.34** | 281.3 / 23.42 | 469.9 / 45.74 |
| **`DenseList` (Rep 2a)** | `List (Option Val)` (fixed length $N$) | Yes | Yes (for $i < N$) | Yes (if pre-sized to $N$) | 22 | 2676.8 / 271.42 | 293.8 / 24.82 | 501.5 / 48.78 |
| **`SortedAList` (Rep 4)** | `List (Nat × Val)` (sorted by key) | Yes | Yes (`erase` removes key) | Yes | 65 | 5491.9 / 1321.25 | 286.8 / 24.71 | 475.5 / 48.41 |
| **`DenseArray` (Rep 3)** | `Array (Option Val)` | Yes | Yes (for $i < N$) | Yes (if pre-sized to $N$) | 30 | 5801.6 / 611.41 | 380.1 / 36.26 | 655.0 / 72.70 |
| **`FnMap` (Rep 1)** | `Nat → Option Val` | **No** | **No** | **No** (unmerged $O(2^D)$) | 10 | **1332.9** / 285.96 | **51,728.5** / **68.56** | **TIMEOUT** ($>10^7$ heartbeats) |

---

### 5. `PersistentArray` and `PersistentHashMap` Source and Runtime Comparison (`v4.30.0-rc2` → `v4.34.1`)

Basis: **source** + **execution** ([`support/lean-persistent-collections-r506-runtime-430rc2-to-4341/source-diff.patch`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/source-diff.patch), [`support/lean-persistent-collections-r506-runtime-430rc2-to-4341/source-observation.json`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/source-observation.json), [`support/lean-persistent-collections-r506-runtime-430rc2-to-4341/results.json`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/results.json), [`support/lean-persistent-collections-r506-runtime-430rc2-to-4341/fixture/Probe.lean`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/fixture/Probe.lean)).

| Collection Source Path | Lean `v4.30.0-rc2` (`3dc1a088b6d2`) Blob | Lean `v4.34.1` (`5045d0056413`) Blob | Source Comparison |
| :--- | :--- | :--- | :--- |
| `src/Lean/Data/PersistentArray.lean` | `516fb0ce50651c1ef39cccdca48663335dac7790` | `e252526851a5eb4bb988d67dd8854b90a2cf970c` | `setAux` through `set` is byte-identical; `forInAux`/`forIn` gain `@&` borrow annotations, and namespace placement changes. |
| `src/Lean/Data/PersistentHashMap.lean` | `f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d` | `e4d81c5cc33ac8d6e67ad217402ec8688b11486e` | `insertAux` through `insert` is byte-identical; lookup/traversal functions gain `@&` borrow annotations, and `alter` is added. |

Across 48 serial `lean --run` processes executing [`support/lean-persistent-collections-r506-runtime-430rc2-to-4341/fixture/Probe.lean`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/fixture/Probe.lean) (3 runs per mode at $n \in \{8{,}192, 65{,}536\}$; minimum admission 22.51% reclaimable RAM and 4,722,233,344 free disk bytes; peak sampled RSS 439,009,280 B), all runs exited `0` with identical outputs:

| Entries and Updates ($n$) | Toolchain | `PersistentArray` Retained / Discarded Median Peak RSS (MB) | `PersistentHashMap` Retained / Discarded Median Peak RSS (MB) |
| ---: | :--- | ---: | ---: |
| `8,192` | `v4.30.0-rc2` (`3dc1a088b6d2`) | `393.15` / `393.02` | `397.61` / `397.21` |
| `8,192` | `v4.34.1` (`5045d0056413`) | `422.25` / `421.48` | `427.39` / `427.21` |
| `65,536` | `v4.30.0-rc2` (`3dc1a088b6d2`) | `397.59` / `397.72` | `408.76` / `402.82` |
| `65,536` | `v4.34.1` (`5045d0056413`) | `428.18` / `427.20` | `438.80` / `432.91` |

## Boundaries

- **Multi-threaded elaboration (`-j > 1`), Mathlib-scale `.olean` graphs, and native C/LLVM codegen for `._unsafe_rec` (`not examined`)**: All memory-ceiling and kernel-replay benchmarks were conducted single-threaded (`-j1`, `-DElab.async=false`). Floating-point MIR operations, inline assembly, concurrency primitives, and `dyn Trait` were also `not examined`.
- **Future LCNF compiler recovery after `-M` kernel memory errors (`unknown`)**: It is `unknown` whether future Lean releases will replace the `ExplicitBoxing:301:45` panic after a kernel memory-ceiling failure with a graceful compiler bailout.
- **Boundaries `known not to apply` and `unsupported`**:
  - `by decide` over multi-hundred-element `List UInt8` / `String` conjunctions (`~1.95 GB` RSS) and monolithic $\ge 128$-constructor phase-invariant inductives are `known not to apply` within `-M768`.
  - Monolithic `rfl` reflection (`Arch 4` / `Arch 6`) is `known not to apply` to exponential diamond graphs without cut-point merging (`Arch 5`) and is `unsupported` for symbolic loop bounds (`m : Nat`) or unfactored `evalSteps 60` over symbolic `∀ base : Nat`.
  - `noncomputable section` alone is `known not to apply` as a suppressor of `<fn>._unsafe_rec`; `Array (Option Val)` is `known not to apply` as an $O(1)$ container inside kernel `whnf_core`; and `native_decide` is `unsupported` under Anneal's kernel-only TCB policy.

## Evidence

- **Kernel Memory Ceilings & Proof-Cost Scaling (`support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/`)**:
  - Replay ledgers: [`r12_m768_replay.json`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/r12_m768_replay.json) (`091d039abbbf9365f6889b87bee67ff19c4167fa34b95480a4ad69357756774d`), [`r12_m2048_replay.json`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/r12_m2048_replay.json) (`e967cb95eda8121c5d9e4f1c6a2afef6387bc4d531a67112fd2bd54993364401`).
  - Specimens (`36` `.lean` / `.txt` files): [`SubstantiveMirByteParser.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SubstantiveMirByteParser.lean) (`9e24337cdf324d6f1d41914a6302b8e72560fd0de1f542da43507dc3b71def7a`), [`MirWireParser.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/MirWireParser.lean) (`9fa2f09b01ac3cc23297431402fc5b24f8fb3930436755354d4947a93f81c34b`), [`EndCallSourceShape.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/EndCallSourceShape.lean.txt) (`618886f7b3c9ba98bfa47ed4d36b09bc8a85b52b7f05ffc255ef4c5f60d202ba`), [`SpecValidationControls-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SpecValidationControls-initial.lean.txt) (`80327853d135c6d26c84a62a8de1e1ab4e6387b0f5af04f2a757e6adea26be0b`), [`SpecChallengeResolution.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SpecChallengeResolution.lean) (`bb6c49b749f15b489680f49a70bbca29ae46830b9ad97e3dd3eeb73196d5139a`), [`SpecValidation.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SpecValidation.lean), [`ServiceIntervals-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ServiceIntervals-initial.lean.txt) (`08328762e08bfdc8352fcc4b6a7790663949ed9e370d75c7f174866d16bcb9c0`), [`ClaimChangeReport-initial.lean.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ClaimChangeReport-initial.lean.txt) (`3419c524945178bfa559a71e31218e2295fbed9400f47d33a56efef3211f2f2e`), [`ClaimChangeResolution.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/ClaimChangeResolution.lean) (`b0d63e18438f0f2aa6017d8b19e00e98664536f622af7bf32d9063b2ac80204f`), [`StatefulGenericLibraryH3H7Core.lean`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/StatefulGenericLibraryH3H7Core.lean) (`ddcd212ee3175dcad9a1a2a927454806039d10429de44ecf4ebe0f402bd341b0`), [`Post96LifecycleGenerated.lean.failed.txt`](support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/Post96LifecycleGenerated.lean.failed.txt) (`c88d61017f795633934ec2c733d014899c21cd50887e66ace53d2b0149ad7979`), plus the `ProofCost*`, `ProgramCost*`, and `CargoLeanCostCold2*` modules listed in §1.3–§1.4.
- **Kernel Proof Scaling & Validator Architectures (`support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/`)**:
  - [`UnifiedEndToEndStack.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/UnifiedEndToEndStack.lean) (`5cb80e03825037ecc1177ce6cf26d4bae9c63017434ed6b5e99ff48376e200b1`), [`run_unified_benchmark.py`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/run_unified_benchmark.py) (`75481083294165f880aa91b84d6db22bdab445d9de1cb056e64ecb28bdb7504a`), [`unified_benchmark_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/unified_benchmark_results.json) (`116b056204c4a91721af14ebda3626049d554d5bb9fe3f00b7468321725595d1`).
  - [`BenchmarkProofStrategies.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/BenchmarkProofStrategies.lean) (`0e6a9f9ef904a29e53a2fff4b2446599b4d22ecee97ebc80f19417e221725a81`), [`MeasureKernel.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/MeasureKernel.lean) (`ac90f46e0a474d7f444d08daa7a7ef0186ea1c3fc43bbace0bfca6242aac3ecc`), [`run_suite_a.py`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/run_suite_a.py) (`1d9d9800835c05e755cc4542e3ba7c7518591cddefc47a79d0d5cb9d90ae3e1e`), [`suite_a_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/suite_a_results.json) (`defe94560343e972617ffa8f2933e3e1baaa8b5f38fe63189d5222e04f69f1b3`), [`run_suite_b.py`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/run_suite_b.py) (`687c86b7f521c1b51a78ce535fb67d0302b4627f73dc1915e7806987a45688ed`), [`suite_b_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/suite_b_results.json) (`c29912a8a9bd0f00756d6a419c32f13f055e5153a386c420aa0f66fe9f849bdc`).
  - [`ProbeSideConditionReflection.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbeSideConditionReflection.lean) (`6f0c20ec262c0cdc604389d4d92b40331e6d3fea4d5db37fb51a9eb254e7c173`), [`run_side_conditions.py`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/run_side_conditions.py) (`8a1a6256a028619f8ff77fef67c0250a68dd1963e6667484bbae92aeb6c564ee`), [`side_condition_results.json`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/side_condition_results.json) (`40b359e6eba5165fe39aa7e1609e2f18b7050da52ad9def8b818dcb9b78a6d1a`), [`ProbePreprovedPasses.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbePreprovedPasses.lean) (`f3977937f95f16ae341d0e350adedbcc1c5ceeb3268ab8077ef1a6646b2964f7`), [`ProbePreprovedSummaries.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbePreprovedSummaries.lean) (`7ea6bed3f8dcb2181ba6860fa424063e027ffa56b67874f3172bf56294773792`), [`ProbeShardedCrateProof.lean`](support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbeShardedCrateProof.lean) (`402ec578ad1dc407312536f607182ff32e68655a43637ca5eed0585b7c12c811`).
- **`._unsafe_rec` Emission & State-Map WHNF Scaling (`support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/`)**:
  - [`PreludeRecProbe.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/PreludeRecProbe.lean) (`d9073c51de34b2fdeb14d93ca983596424837422947dd24b9a7d89ef14a0829c`), [`UnsafeRecProbe.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/UnsafeRecProbe.lean) (`3b2df1273552285e62563f939f6b1be6dca63c5cb0cb9f455702836147f8a169`), [`StateMapBenchmarks.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/StateMapBenchmarks.lean) (`f7f19be1e27e3ef9d60b35f949324830423f9e77aae3348aa354e15c52f90528`), [`RefinementBridge.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/RefinementBridge.lean) (`1491b69dbaaf3776558196fface01ef63e8aa99c984ccde3b12451b07bd9bc61`), [`BenchCommon.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/BenchCommon.lean) (`b0e3900949b4b4732edaaa4c514e282891d0a2d1fffed99ae48019b2fc33fcea`), [`MeasureKernel.lean`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/MeasureKernel.lean) (`c2215c1f1df5605e15f9b551dba137e7734fcae4e9cbc665fd68cf02832e6a66`), [`benchmark_results.json`](support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/benchmark_results.json) (`ea0eb6a10bbe507722b7029107b3fc4bab4170a6f12bfe237f36c51bb4a68ab7`).
- **Persistent Collections (`support/lean-persistent-collections-r506-runtime-430rc2-to-4341/`)**:
  - [`results.json`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/results.json), [`source-observation.json`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/source-observation.json), [`source-diff.patch`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/source-diff.patch), [`probe.py`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/probe.py), [`check.py`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/check.py), [`fixture/Probe.lean`](support/lean-persistent-collections-r506-runtime-430rc2-to-4341/fixture/Probe.lean), and 96 raw stdout/stderr files under `support/lean-persistent-collections-r506-runtime-430rc2-to-4341/raw/`.

## Revalidation

1. **Re-verify the `-M768` byte parser, validator probes, state-map benchmarks, and persistent-collection checks**:
   ```bash
   lean -j1 -M768 support/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/SubstantiveMirByteParser.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbePreprovedPasses.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbePreprovedSummaries.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures/ProbeShardedCrateProof.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false -o PreludeRecProbe.olean support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/PreludeRecProbe.lean
   LEAN_PATH=. lean -DElab.async=false -Ddebug.skipKernelTC=false support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/UnsafeRecProbe.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/StateMapBenchmarks.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/RefinementBridge.lean
   python3 -B support/lean-persistent-collections-r506-runtime-430rc2-to-4341/check.py
   ```
2. **Diff C++ kernel and elaborator control points on toolchain upgrades**:
   Inspect `src/kernel/type_checker.cpp` (`reduce_nat` `has_fvar` guard, `infer_lambda` vs. `infer_let`), `src/kernel/replace_fn.cpp` (`is_likely_unshared`), `src/Lean/Elab/DefView.lean` (`mkDefView`), and `src/Lean/Elab/PreDefinition/Basic.lean` (`shouldGenCodeFor`).
