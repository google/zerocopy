# MIR `R3` Dead-Local Compaction, Fast `O(L + S log₂(L/8))` Certificate Checking, and Tarjan SCC `.olean` Sharding on `joshlf/anneal`

## Summary

Dead-local compaction (`R0 → R3`: deleting `.nop`, `.storageLive`, and `.storageDead` annotations while injectively renumbering surviving locals `π : LiveLocals → Fin M` with ABI slots `_0.._argc` fixed) bridges directly onto unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirAst` and `Trusted.MirSemantics`), resolving two scaling bottlenecks identified in prior corpus evaluations (`anneal-mirwp-proof-scaling-normalization-and-f1-checker-overhead` at commit `44c31fc277f0943c5e2e666884087e7ced453080` and `anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge` at commit `6e24ad128d7f29afc0f47733eb42ec4d3392ba63`):

1. **Constructive `R0 ↔ R3` Refinement & Unmodified `TrustedBoundary.lean` Audit (`support/MirR3LocalCompactionRefinement.lean`, `5,192` lines):** Over scalar/bool/unit/never/fieldless-enum `Trusted.MirSemantics` programs (`[propext]` only across all `22` exported theorems; zero `Classical.choice`, zero `Quot.sound`, zero `sorry`, zero `omega`/`bv_decide`/`native_decide`/`partial def`/`._unsafe_rec`), `ValidProgramCompaction` implies full bidirectional `compact_preserves_eval_iff` (`WellFormed`, `Behavior`, `ReachesResult _ (.fault k)`, `Diverges`, `SatisfiesPost`), `bodyVerified_compact_iff`, `programVerified_compact_iff` (for compaction-invariant `Specs.property`), and `wpProg_transport_compact_iff`. Four mechanized counterexamples establish precondition sharpness: non-injective slot renumbering (`CE1`), compacting a live referenced local (`CE2a`), moving an argument ABI slot (`CE2b`), and moving return slot `_0` (`CE2c`). Unmodified `TrustedBoundary.lean` passes both `"preflight"` (`ok = true`) and `"audit"` (`replay = true`, `replayedDeclarations = 2314`, `reachableDeclarations = 3120`, `axioms = ["propext"]`).
2. **`O(L + S log₂(L/8))` Stride-8 Radix-8 Positional Checker Beats `O(S × L)` Scanning Up to `9.05×` and Eliminates the `K = 64` `maxRecDepth` Cliff (`execution`, `3`-run medians on Lean `v4.34.1`):** Naive `O(S × L)` association-list scanning (`checkR3LinearAssoc`) takes `9.0533 s` (`478.60 MB` RSS) at `K = 32` (`L₀ = 96`, `S₀ = 97`) and crashes at default `maxRecDepth = 512` at `K = 64` (`L₀ = 192`, `S₀ = 193`). Single-pass lockstep validation over `(locals, liveMask, slotMap, targetLocals)` paired with a balanced radix-8 `MaskTree` and stride-8 loop unrolling (`checkR3PositionalBatched`, proved observationally equivalent via `checkR3PositionalBatched_eq`) runs in `1.1395 s` (`rfl`, `7.95×` faster) and `1.0007 s` (`decide`, **`9.05×` faster**) at `K = 32`, scaling cleanly through `K = 64` (`1.9738 s` `rfl` / `2.8342 s` `decide`) and `K = 128` (`L₀ = 384`, `S₀ = 385`: `7.6866 s` `rfl` / `6.7403 s` `decide`, `370.02–372.41 MB` RSS) where both unbatched positional checking (`checkR3Positional`) and linear scanning hit `maxRecDepth`. Paired with `R3` execution (`6.2835 s` vs. `39.9738 s` for `R0` at `K = 32`, **`6.36×` proof speedup**), end-to-end `PositionalBatched (decide) + R3` totals `7.2843 s` (**`5.49×` net speedup** over `R0`, only `13.7%` checker tax) and succeeds at `K = 64` (`19.9928 s` total with `rfl`) where `R0` alone crashes at `maxRecDepth`.
3. **Real Rust Call-Graph Tarjan SCC `.olean` Sharding Cuts Per-Shard RAM `1.38×–1.44×` and Incremental Rebuilds `11.04×–11.68×` (`execution`):** Live `rustc 1.98.0-nightly` `--emit=llvm-ir` intra-crate call graphs show zero multi-function SCCs in `google/zerocopy 0.8.63` (`284` fns, `8` intra edges, `max_dag_depth = 1`) and `miniz_oxide 0.8.9` (`609` fns, `921` edges, `max_dag_depth = 15`), vs. `9` multi-node SCCs in `regex-syntax 0.8.11` (`2,836` fns, `5,258` edges, `7` self-recursive, `2,749` SCCs with sizes `[25, 23, 18, 11, 5, 4, 4, 4, 2]`, condensed DAG depth `29`). Splitting a 2-node cyclic SCC across two Lean `.olean` modules fails in either build order (`CycleNodeA ↔ CycleNodeB`). Coarsening Tarjan SCCs into `CalleesFirst` DAG `.olean` shards (`12` shards for `miniz_oxide`, `14` for `regex_syntax`, `14`-body/shard representative `Anneal.MirWp` obligations) incurs `1.07×–1.23×` cold total CPU overhead while cutting per-shard peak RSS (`238.72 → 172.57 MB` and `249.47 → 172.86 MB`) and cutting proof-only single-shard rebuilds under signature-digest gating (`H_sig`) to `1.7735 s` (`miniz_oxide`, **`11.04×`** vs. monolithic `19.5841 s`, **`15.53×`** vs. naive `mtime` cascade `27.5380 s`) and `1.8365 s` (`regex_syntax`, **`11.68×`** vs. `21.4418 s`, **`10.70×`** vs. naive cascade `19.6499 s`).

---

## Applicability

### Examined Subjects and Their Relationship

- **Verification TCB (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Supplies unmodified `Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`, and `TrustedBoundary.lean`. `MirR3LocalCompactionRefinement.lean` imports strictly `prelude`, locked `Init.*` modules, `Trusted.MirAst`, and `Trusted.MirSemantics` (`0` `Anneal.*` references), passing both `"preflight"` (`SourceRole.theory`) and `"audit"` (`trustLevel := 0`, `loadExts := false`, `requireMirWp := true`). Benchmark proofs in `probe_r3_compaction_and_scc_sharding.py` execute `Anneal.MirWp.positiveCanary_of_exec` over `Trusted.MirSemantics.PositiveCanaryClaim`.
- **Lean Kernel & Rust Toolchain (`leanprover/lean4` `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`; `rust-lang/rust` `rustc 1.98.0-nightly` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** All Lean checks run synchronously (`-DElab.async=false -Ddebug.skipKernelTC=false`) with default `maxRecDepth = 512` (zero `set_option` overrides). Rust crates (`google/zerocopy` `0.8.63` at `0f4623ace6d17078dabe62799cf86f5533eba522`, `Frommi/miniz_oxide` `0.8.9` at `44e43c7786e379b2b1a7fde4aa0e63be719e583d` compiled with `--extern adler2` from `oyvindln/adler2` `2.0.1` at `89a031a0f42eeff31c70dc598b398cbf31f1680f`, and `rust-lang/regex` `regex-syntax` `0.8.11` at `140167995737fa11dfe11b8af8b9aa143b790b4e`) supply live `--edition 2021 --crate-type lib -C opt-level=0 -C codegen-units=1 --emit=llvm-ir` intra-crate call graphs for Tarjan (1972, DOI `10.1137/0201010`) SCC condensation and `.olean` sharding. `adler2` is compiled strictly as an `.rlib` dependency for `miniz_oxide`; its internal call graph was not analyzed separately.

### Relationship to Prior Corpus Reports

- Extends `anneal-mirwp-proof-scaling-normalization-and-f1-checker-overhead` (`44c31fc277f0943c5e2e666884087e7ced453080`), which showed a `4.78×` `R0 → R3` `Anneal.MirWp` speedup at `K = 32` (`3.4099 s → 0.7127 s`) and warned that pairing `R3` with an `O(S × L)` `List`-based transport checker (`2.8819 s`) destroys net break-even. Here, `checkR3PositionalBatched` reduces checker latency at `K = 32` to `1.0007 s` (`decide`) / `1.1395 s` (`rfl`), restores a `5.39×–5.49×` end-to-end speedup over `R0`, and scales through `K = 64` and `K = 128`.
- Closes the two `R1`-only limitations recorded for `support/AnnealTrustedMirMoveToCopyStorage.lean` in `anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge` (`6e24ad128d7f29afc0f47733eb42ec4d3392ba63`): (1) `MirR3LocalCompactionRefinement.lean` eliminates dead local slots (`R3`) rather than leaving unused slots allocated behind `.nop`, and (2) marks all recursive `Prop` helper predicates `noncomputable def`, preventing `._unsafe_rec` compiler helpers so unmodified `TrustedBoundary.lean` `"audit"` accepts every declaration cleanly under `['propext']`.
- Grounds the sharded verification architecture analyzed in `tarjan-scc-proof-sharding-acyclic-interface-digests-and-incremental-olean-auditing` (`d9e0710ae3f78e7ab9d1c5d458cba2d0c170fdc`) and `scc-condensation-and-mutual-recursion-fixpoint-summaries` (`9a6617e007e953b87dad028926b0a76627ed47fe` / `2f3c272261d10a1115a28c11f20370cdb0b0c870`) in live Rust crate LLVM-IR call graphs and synchronous Lean `v4.34.1` compilation measurements.

### Supported MIR Fragment

Claims proved in `MirR3LocalCompactionRefinement.lean` govern the **executable, value-only, unprojected, scalar/bool/unit/never/fieldless-enum fragment** of `Trusted.MirSemantics@c131b320e` (`isSupportedScalarOrUnitTy`, `locals.all isSupportedScalarOrUnitTy`, `.assign`, `.storageLive`, `.storageDead`, `.nop`, `.goto`, `.switchInt`, `.assert`, `.return_`, `.unreachable`, `.unwindResume`). Non-empty `callerMem`, pointer dereferences, `ProjectionElem` chains, and heap/stack references remain outside `Trusted.MirSemantics` execution paths and evaluate to `.unsupported`.

---

## Findings

### 1. Constructive `R0 → R3` Compaction Specification and Equivalence Theorems (`support/MirR3LocalCompactionRefinement.lean`)

`Basis: source + execution (Lean v4.34.1 kernel & TrustedBoundary.lean audit)`

In `Trusted.MirSemantics@c131b320e`, `hasStorageAnnotation` initializes return slot `_0` and arguments `1..argc` as `.live _`, whereas temporaries `_k` (`k > argc`) start `.dead` (when annotations exist) or `.live none` (when absent), and `.storageLive` / `.storageDead` toggle individual `LocalSlot`s between `.dead` and `.live none`. Compaction (`R0 → R3`) deletes `.nop`, `.storageLive _`, and `.storageDead _`, replaces `b.locals` (`length = L`) with compacted `spec.targetLocals` (`length = M ≤ L`), and remaps every surviving `Place.localId` via `spec.slotMap` (`π : LiveLocals → Fin M`, witnessed explicitly by `piFin`).

#### Key Definitions (`namespace AnnealMirR3Compaction`)

```lean
structure CompactionSpec where
  liveMask : List Bool
  slotMap : List Nat
  targetLocals : List MirTy

noncomputable def piFin (spec : CompactionSpec)
    (hBound : ∀ i : LocalId, isLiveLocal spec.liveMask i = true →
      mapLocal spec.slotMap i < spec.targetLocals.length)
    (i : LocalId) (hi : isLiveLocal spec.liveMask i = true) :
    Fin spec.targetLocals.length :=
  ⟨mapLocal spec.slotMap i, hBound i hi⟩

noncomputable def compactBody (spec : CompactionSpec) (b : Body) : Body :=
  { b with
    locals := spec.targetLocals
    basicBlocks := compactBasicBlockList spec.slotMap b.basicBlocks }

def PreservesAbiSlots (argc : Nat) (spec : CompactionSpec) : Prop :=
  argc < spec.liveMask.length ∧
  ∀ i : LocalId, i ≤ argc →
    isLiveLocal spec.liveMask i = true ∧ mapLocal spec.slotMap i = i

def InjectiveOnLive (spec : CompactionSpec) : Prop :=
  ∀ i j : LocalId,
    isLiveLocal spec.liveMask i = true →
    isLiveLocal spec.liveMask j = true →
    mapLocal spec.slotMap i = mapLocal spec.slotMap j →
    i = j

def ValidBodyCompaction (bSrc : Body) (spec : CompactionSpec) : Prop :=
  PreservesAbiSlots bSrc.argumentCount spec ∧
  InjectiveOnLive spec ∧
  ValidTargetTypes bSrc spec ∧
  AllReferencedLocalsInLiveMask spec.liveMask bSrc ∧
  StorageMarkersOnlyOnDead spec.liveMask bSrc.locals.length bSrc
```

#### Soundness Mechanics: Slot-Frame State Sync & `Classical.choice`-Free `Diverges`

Every reachable pair `(sSrc, sTgt)` maintains `StateSync`: equal stack depth, matching `defId` and `blockIdx`, target statement cursor aligned to skipped-marker source cursor (`countLiveStmts`), identical `callerMem`, and **at every live index `i`** (`isLiveLocal spec.liveMask i = true`), `getElem? tgt.locals (mapLocal spec.slotMap i) = getElem? src.locals i`. Two edge conditions proved essential in Part III:
- **Forward marker deletion vs. dynamic dead slots (`StorageMarkersOnlyOnDead`):** Deleting `.storageDead 0` (`id = 0` faults `.undefined` in `Trusted.MirSemantics`) or out-of-bounds `.storageLive L` / `.storageDead L` (`fault .outOfBounds`) would suppress source faults; `StorageMarkersOnlyOnDead` restricts `.storageLive id` to `id < L ∧ !isLiveLocal mask id` and `.storageDead id` to `0 < id ∧ id < L ∧ !isLiveLocal mask id`, ensuring deleted markers step silently inside one basic block before the next live instruction or terminator. Forward simulation therefore holds under the **same** fuel (`wpProg_forward_of_compact`), while backward lifting scales fuel by `maxBlockStmtsInBodies pSrc.bodies + 1` (`wpProg_backward_of_compact`).
- **`Classical.choice`-free infinite-trace construction (`Diverges`):** Because `Trusted.MirSemantics.evalStep` is deterministic at choice `0`, `iterTrace p s0 n` builds the deterministic execution trace constructively from `initState p q = .ok s0`. If `pTgt` diverges, it reaches neither `.done out` nor `.fault k`, so by `reachesResult_compact_iff` neither does `pSrc`, yielding `diverges_compact_iff` strictly under `[propext]` without classical choice.

#### Exported Equivalence & Transport Theorems (`support/MirR3LocalCompactionRefinement.lean`)

```lean
theorem compact_preserves_eval_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query)
    (post : TerminalOut → Prop) :
    (WellFormed pSrc q ↔ WellFormed (compactProgram specs pSrc) q) ∧
    (∀ out, Behavior pSrc q out ↔ Behavior (compactProgram specs pSrc) q out) ∧
    (∀ k, ReachesResult pSrc q (.fault k) ↔ ReachesResult (compactProgram specs pSrc) q (.fault k)) ∧
    (Diverges pSrc q ↔ Diverges (compactProgram specs pSrc) q) ∧
    (SatisfiesPost pSrc q post ↔ SatisfiesPost (compactProgram specs pSrc) q post)

theorem bodyVerified_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    (defId : DefId) (bSrc : Body) (spec : CompactionSpec)
    (hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc)
    (hSpec : Trusted.MirSemantics.getElem? specs defId = some spec)
    (safetyPre : List Val → Prop) :
    BodyVerified pSrc defId bSrc safetyPre ↔
      BodyVerified (compactProgram specs pSrc) defId (compactBody spec bSrc) safetyPre

theorem programVerified_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    {propSpec : Specs}
    (hValid : ValidProgramCompaction specs pSrc)
    (hProp : propSpec.property pSrc ↔ propSpec.property (compactProgram specs pSrc)) :
    ProgramVerified pSrc propSpec ↔ ProgramVerified (compactProgram specs pSrc) propSpec

theorem wpProg_forward_of_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {fuel : Nat} {q : Query} {post : TerminalOut → Prop}
    (h : wpProg pSrc fuel q post) :
    wpProg (compactProgram specs pSrc) fuel q post

theorem wpProg_backward_of_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {fuelTgt : Nat} {q : Query} {post : TerminalOut → Prop}
    (h : wpProg (compactProgram specs pSrc) fuelTgt q post) :
    wpProg pSrc (fuelTgt * (maxBlockStmtsInBodies pSrc.bodies + 1)) q post

theorem wpProg_transport_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    (q : Query) (post : TerminalOut → Prop) :
    (∃ fuelSrc : Nat, wpProg pSrc fuelSrc q post) ↔
      (∃ fuelTgt : Nat, wpProg (compactProgram specs pSrc) fuelTgt q post)
```

*Important Boundary:* To respect `TrustedBoundary.lean` Pass-1 isolation (`0` `Anneal.*` imports), `AnnealMirR3Compaction.wpProg` is defined standalone over `Trusted.MirSemantics.initState` and `evalStep`, connected back to `Trusted.MirSemantics.SatisfiesPost` and `¬ Diverges` via `satisfiesPost_and_not_diverges_of_wpProg`.

### 2. Mechanized Sharpness Counterexamples and Positive Certified Witness

`Basis: execution (Lean v4.34.1 kernel proofs under TrustedBoundary.lean audit)`

Part V constructs a positive certified witness (`pos_witness_valid`, `pos_witness_behavior_iff`: compacting `4` locals with dead slot `2` down to `3` locals certified by `checkR3PositionalBatched ... = true` via `rfl`) alongside **four sharpness counterexamples**, each satisfying all other `ValidBodyCompaction` conjuncts while breaking one invariant:

| Witness / CE | Violated Invariant | Source Program Outcome (`Behavior`) | Compacted Program Outcome | Lean Theorem (`['propext']` only) |
| :--- | :--- | :--- | :--- | :--- |
| **`posSrcBody`** | None (`ValidBodyCompaction`) | `.returned (.bool true)` | Bidirectional `↔` preserved | `pos_witness_valid`, `pos_witness_behavior_iff` |
| **`CE1`** | `¬ InjectiveOnLive ce1Spec` (`slotMap = [0, 1, 1]`) | Returns `.bool false` (`_1 := false; _2 := true; _0 := _1`) | Aliases `_2` onto `_1`, returning `.bool true` (`¬ Behavior _ _ (.returned (.bool false))`) | `ce1_non_injective_renumbering_breaks_eval` |
| **`CE2a`** | `¬ AllReferencedLocalsInLiveMask ce2aSpec.liveMask ce2aBody` | Returns `.bool true` via `_1` (`liveMask = [true, false]`, `slotMap = [0, 0]`) | `_1` collapses onto `_0` (`∀ out, ¬ Behavior ce2aTgtProg ... out`) | `ce2a_referenced_local_compacted_breaks_eval` |
| **`CE2b`** | `¬ PreservesAbiSlots 1 ce2bSpec` (`slotMap = [0, 2, 1]`, swaps `_1 ↔ _2`) | Returns input argument `_1 = .bool true` | `initState` rejects input `.bool true` against `.unit` param (`∀ out, ¬ Behavior ... out`) | `ce2b_abi_arg_slot_not_preserved_breaks_eval` |
| **`CE2c`** | `¬ PreservesAbiSlots 0 ce2cSpec` (`slotMap = [1, 0]`, swaps `_0 ↔ _1`) | Assigns `_0 := true`, returns `.bool true` | Writes `_1 := true`; `.return_` reads uninitialized `_0` → **`ReachesResult ... (.fault .undefined)`** | `ce2c_return_slot_zero_moved_breaks_eval` |

### 3. Fast `O(L + S log₂(L/8))` Certificate Checking vs. `O(S × L)` Linear Association Scanning

`Basis: source + execution (support/probe_r3_compaction_and_scc_sharding.py, Suite 1, 3-run medians) + derived`

We mechanized three progressive checkers inside `MirR3LocalCompactionRefinement.lean`, each proved sound against `ValidBodyCompaction`:

1. **`checkR3LinearAssoc` (`O(S × L)`, `validBodyCompaction_of_checkR3LinearAssoc`):** Constructs `mkAssocPairs 0 spec.liveMask` (`[(0, b₀), ...]`) and executes linear `assocLookup` per statement/operand plus `O(L²)` `checkInjectiveLoop`.
2. **`checkR3Positional` (`O(L + S log₂(L/8))` unbatched tree lookup):** Runs a single lockstep zip validator `checkZipLocalsCount` enforcing `PreservesAbiSlots`, strict-monotone `InjectiveOnLive` (`expTgtIdx == mapLocal`), and `ValidTargetTypes` in one `O(L)` pass while propagating `numLocals` directly (avoiding a separate `List.length` traversal), and builds a balanced radix-8 binary `MaskTree` (`buildMaskTree`, depth `≤ ceil(log₂(L/8))`) queried one statement at a time (`checkBlocksTreeSeq`).
3. **`checkR3PositionalBatched` (`validBodyCompaction_of_checkR3PositionalBatched` via `checkR3PositionalBatched_eq`):** Unrolls both the lockstep local zip (`checkZipLocals8Count`) and statement scanning (`checkStmtsTree8`) by stride `8`. Unbatched `1`-by-`1` statement recursion (`checkStmtsTreeSeq`) or computing `bSrc.locals.length` separately hits Lean's `512` `maxRecDepth` threshold by `K = 64` (`S₀ = 193`, `L₀ = 192`). Stride-8 unrolling plus inline `numLocals` threading cuts kernel `whnf` recursion stack depth `8×` and replaces `O(L)` list scanning with `O(log₂(L/8))` tree indexing.

#### Live Lean `v4.34.1` Benchmark Matrix (`Suite 1`: `K = 4..128`, `L₀ = 3K`, `S₀ = 3K + 1` → `L₃ = K`, `S₃ = K - 1`, default `maxRecDepth = 512`)

| `K` | `(L₀, S₀)` → `(L₃, S₃)` | `LinearAssoc_OSL_rfl` | `PositionalUnbatched_OS_rfl` | `PositionalBatched_OS_rfl` | `PositionalBatched_OS_decide` | `R3_SymbolicExecutes_Proof` (`PositiveCanaryClaim`) | `R0_SymbolicExecutes_Proof` (`PositiveCanaryClaim`) |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `4` | `(12, 13) → (4, 3)` | `0.3851 s` (`172.6 MB`) | `0.2683 s` (`169.2 MB`) | `0.2818 s` (`168.2 MB`) | `0.3114 s` (`169.0 MB`) | `0.4138 s` (`174.0 MB`) | `0.7592 s` (`176.7 MB`) |
| `8` | `(24, 25) → (8, 7)` | `0.6993 s` (`181.0 MB`) | `0.3171 s` (`170.7 MB`) | `0.3524 s` (`171.0 MB`) | `0.2953 s` (`170.7 MB`) | `0.5790 s` (`179.0 MB`) | `1.4207 s` (`189.0 MB`) |
| `16` | `(48, 49) → (16, 15)` | `2.3101 s` (`244.5 MB`) | `0.5476 s` (`177.3 MB`) | `0.6308 s` (`179.6 MB`) | `0.5048 s` (`178.6 MB`) | `1.5303 s` (`192.4 MB`) | `4.4122 s` (`227.9 MB`) |
| `32` | `(96, 97) → (32, 31)` | `9.0533 s` (`478.6 MB`) | `1.1385 s` (`183.0 MB`) | `1.1395 s` (`188.4 MB`) | **`1.0007 s`** (`189.5 MB`) | **`6.2835 s`** (`224.0 MB`, `107,760 B`) | `39.9738 s` (`405.8 MB`, `314,200 B`) |
| `64` | `(192, 193) → (64, 63)` | **FAIL** `maxRecDepth` (`0.7119 s`) | **FAIL** `maxRecDepth` (`0.8239 s`) | **`1.9738 s`** (`230.8 MB`, `101,344 B`) | `2.8342 s` (`232.6 MB`, `102,368 B`) | **`18.0190 s`** (`385.5 MB`, `219,536 B`) | **FAIL** `maxRecDepth` (`1.3939 s`) |
| `128` | `(384, 385) → (128, 127)` | **FAIL** `maxRecDepth` (`1.8915 s`) | **FAIL** `maxRecDepth` (`3.3051 s`) | `7.6866 s` (`370.0 MB`, `184,312 B`) | **`6.7403 s`** (`372.4 MB`, `185,328 B`) | **FAIL** `maxRecDepth` (`1.9449 s`) | **FAIL** `maxRecDepth` (`2.4350 s`) |

#### Net Checker + Proof Speedup Analysis (`R0` vs. `R3` End-to-End Pipeline)

- **At `K = 32`:** `R3` alone cuts `PositiveCanaryClaim` wall time `6.36×` (`39.9738 s → 6.2835 s`), peak RSS `1.81×` (`405.78 → 224.04 MB`), and `.olean` size `2.92×` (`314,200 B → 107,760 B`). Combining `LinearAssoc + R3` spends `9.0533 s` on the checker (`15.3369 s` total = `2.61×` net, `59.0%` checker tax), whereas `PositionalBatched` (`decide`) spends `1.0007 s` (`7.2843 s` total = **`5.49×` net speedup**, `13.7%` tax) and `PositionalBatched` (`rfl`) spends `1.1395 s` (`7.4230 s` total = **`5.39×` net speedup**, `15.4%` tax).
- **At `K = 64`:** `R0`, `LinearAssoc`, and `PositionalUnbatched` all fail deterministically at `maxRecDepth = 512`. Only **`PositionalBatched + R3`** completes end-to-end verification in **`19.9928 s`** (`1.9738 + 18.0190` with `rfl`; **`20.8532 s`** with `decide`).
- **At `K = 128`:** `checkR3PositionalBatched` validates a `384`-local / `385`-statement compaction certificate in `6.7403 s` (`decide`) / `7.6866 s` (`rfl`), **whereas `R3_SymbolicExecutes_Proof` itself crashes at `maxRecDepth` (`L108:43`)** when stepping `127` assignments inline inside a single monolithic theorem—demonstrating why per-body compaction must compose with call-graph sharding for multi-function crates.

### 4. Real Rust Call-Graph Extraction & Tarjan SCC `.olean` Sharding

`Basis: normative (DOI 10.1137/0201010) + execution (Suite 2: rustc 1.98.0-nightly --emit=llvm-ir + Lean v4.34.1)`

#### Extracted Real Crate LLVM-IR Call Graphs (`rustc 1.98.0-nightly`, `--edition 2021 --crate-type lib -C opt-level=0 -C codegen-units=1 --emit=llvm-ir`)

| Crate (Version & Revision) | Defined Fns | Intra Edges | Self-Rec Fns | Tarjan SCCs | Multi-Node SCCs (`≥ 2` fns) | Multi-Node SCC Sizes | Condensed DAG Edges | Max DAG Depth |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`zerocopy` (`0.8.63`, `0f4623ace6`)** | `284` | `8` | `0` | `284` | `0` | `[]` | `8` | `1` |
| **`miniz_oxide` (`0.8.9`, `44e43c7786`)** | `609` | `921` | `0` | `609` | `0` | `[]` | `921` | `15` |
| **`regex-syntax` (`0.8.11`, `1401679957`)** | `2,836` | `5,258` | `7` | `2,749` | `9` | `[25, 23, 18, 11, 5, 4, 4, 4, 2]` | `5,058` | `29` |

#### Empirical Confirmation That Cyclic SCCs Cannot Span Distinct `.olean` Modules

Executing `probe_cyclic_scc_split_fails` over a minimal 2-function mutual recursion cycle (`CycleNodeA.fnA ↔ CycleNodeB.fnB`) in Lean `v4.34.1` confirms deterministic failure in both build orders: compiling `CycleNodeA.lean` first fails with `rc = 1` (`unknown module prefix 'CycleNodeB'`), and compiling `CycleNodeB.lean` first fails with `rc = 1` (`unknown module prefix 'CycleNodeA'`). Tarjan SCC condensation is therefore mandatory before splitting Lean proofs into acyclically imported `.olean` shards (unless cycles are broken by opaque specification axioms validated by an external rank/signature-digest linker as described in `tarjan-scc-proof-sharding-acyclic-interface-digests-and-incremental-olean-auditing` `d9e0710ae3f78e7ab9d1c5d458cba2d0c170fdc`).

#### Monolithic vs. Tarjan-SCC-Sharded & `H_sig`-Gated Incremental Lean `v4.34.1` Compilation (`3`-run medians)

Each workload coarsens the extracted `CalleesFirst` SCC DAG into balanced atomic shards (preserving all multi-node SCCs intact inside single shards) instantiated at `14` representative `R3`-compacted `PositiveCanaryClaim` obligations per shard (`168` total items across `12` shards for `miniz_oxide_DAG`, depth `10`; `196` items across `14` shards for `regex_syntax_MultiSCC`, keeping `[18, 4]` inside shard `2` and `[25, 23]` inside shard `10`):

| Metric (`3`-Run Median) | `miniz_oxide_DAG` (`12` shards, depth `10`) | `regex_syntax_MultiSCC` (`14` shards, `9` multi-SCCs) |
| :--- | :---: | :---: |
| **Monolithic Cold Wall / Peak RSS / `.olean`** | `19.5841 s` / `238.72 MB` / `1,066,144 B` | `21.4418 s` / `249.47 MB` / `1,263,528 B` |
| **Sharded Cold Total Wall / Ratio vs. Mono** | `24.0268 s` / `1.23×` | `22.9890 s` / `1.07×` |
| **Sharded Critical-Path Wall (level-parallel)** | `20.4381 s` (`0.96×` crit-path speedup) | `22.9890 s` (`0.93×` crit-path speedup) |
| **Sharded Max Per-Shard RSS (Reduction)** | **`172.57 MB`** (**`1.38×`** lower) | **`172.86 MB`** (**`1.44×`** lower) |
| **Sharded Total `.olean` Footprint** | `1,421,216 B` (`1.33×` mono) | `1,704,712 B` (`1.35×` mono) |
| **Edited Mid Shard & Downstream Cascade Span** | Shard `0` → `12 / 12` shards | Shard `2` (`multi-SCC [18, 4]`) → `12 / 14` shards |
| **`H_sig` Digest Preserved After Proof Edit** | `aaed36dd...` (`identical`) | `dc6916c0...` (`identical`) |
| **`H_sig`-Gated 1-Shard Rebuild Wall** | **`1.7735 s`** | **`1.8365 s`** |
| **Naive `mtime` Downstream Cascade Wall / Crit-Path** | `27.5380 s` / `22.3956 s` | `19.6499 s` / `19.6499 s` |
| **`H_sig` Speedup vs. Monolithic / vs. Naive Cascade** | **`11.04×`** / **`15.53×`** (`12.63×` vs. crit) | **`11.68×`** / **`10.70×`** |
| **Leaf Shard Rebuild (`0` downstream) / vs. Mono** | Shard `11`: `2.6621 s` (**`7.36×`**) | Shard `13`: `1.8237 s` (**`11.76×`**) |

Without canonical interface digests (`H_sig`), editing a proof body inside shard `0` (`miniz_oxide`) or multi-SCC shard `2` (`regex_syntax`) invalidates `12` downstream shards under `mtime`/`.olean`-hash invalidation (`27.5380 s` vs. `19.5841 s` monolithic for `miniz_oxide`—`0.71×` slower than monolithic rebuilds). Under `H_sig` hashing strictly exported interface specs (`ShardSpec` / `DepSummary`) while omitting opaque proof bodies, downstream shards stay cached (`0` invalidations), achieving **`11.04×–11.68×` incremental speedups**.

### 5. Analytical Dimensions Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

`Basis: execution + source + derived`

| Dim | Category | Measured Status / Assessment |
| :-: | :--- | :--- |
| **`L1`** | Authoring & proof velocity | `source` + `derived`: Constructive `5,192`-line mechanization (`239,819 B`) provides reusable decidable checker theorems (`validBodyCompaction_of_checkR3PositionalBatched`) reducing per-body `R0 → R3` transport to `1`-line `by rfl` / `by decide` obligations. Human interactive authoring hours: `not measured`. |
| **`L2`** | Toolchain / TCB build time | `execution`: Suite 1 & Suite 2 runs reuse cached `.olean`s of unmodified `Trusted`, `Trusted.MirAst` (`1,387,952 B`), `Trusted.MirSemantics` (`1,235,928 B`), `Anneal.MirWp` (`4,379,472 B`), and `MirR3LocalCompactionRefinement` (`9,301,800 B`). Fresh cold build time of base modules was `not measured` (`"cached": true` in JSON). |
| **`L3`** | Pass / cert synthesis latency | `not measured`: Python test harness emits `CompactionSpec` and Tarjan shard partitions in memory; standalone `rustc`/Anneal MIR pass execution time was not timed separately. |
| **`L4`** | Generated code performance | `known not to apply`: Compaction transforms Anneal's MIR representation solely for proof checking; no runtime binary execution throughput is claimed (`rustc --emit=llvm-ir` used only for call-graph extraction). |
| **`L5`** | Checking latency & throughput | `execution` (`3`-run medians, Lean `v4.34.1`): `checkR3PositionalBatched` checks `K = 32` (`L₀=96, S₀=97`) in `1.0007 s` (`decide`, `9.05×` faster than `checkR3LinearAssoc` `9.0533 s`), `K = 64` in `1.9738 s` (`rfl`), `K = 128` (`L₀=384, S₀=385`) in `6.7403 s` (`decide`). End-to-end `PositionalBatched + R3` at `K = 32` is `5.49×` faster than `R0` (`7.2843 s` vs. `39.9738 s`). Suite 2 `H_sig` 1-shard rebuild achieves `11.04×` (`miniz_oxide`) and `11.68×` (`regex_syntax`) speedups vs. monolithic rebuild. |
| **`L6`** | RAM & artifact footprint | `execution`: `checkR3PositionalBatched` at `K = 32` cuts peak RSS `2.54×` vs. `LinearAssoc` (`188.37 MB` vs. `478.60 MB`), staying at `370.02–372.41 MB` at `K = 128`. `R3` cuts `K = 32` proof RSS `1.81×` (`405.78 → 224.04 MB`) and `.olean` `2.92×` (`314,200 → 107,760 B`). Suite 2 sharding cuts peak per-process RSS `1.38×` (`238.72 → 172.57 MB`) and `1.44×` (`249.47 → 172.86 MB`) at `1.33×–1.35×` total `.olean` overhead. |
| **`C1`** | Spec & assumption auditability | `execution`: Zero `Anneal.*` imports inside `MirR3LocalCompactionRefinement.lean`; all `22` exported theorems depend strictly on `['propext']` (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`); unmodified `TrustedBoundary.lean` `"preflight"` (`ok=true`) and `"audit"` (`replay=true`, `2314` replayed, `3120` reachable) pass cleanly. |
| **`C2`** | Orthogonality & simplicity | `derived` + `source`: `ValidBodyCompaction` factors into ABI preservation (`PreservesAbiSlots`), slot injectivity (`InjectiveOnLive`), live coverage (`AllReferencedLocalsInLiveMask`), target typing (`ValidTargetTypes`), and dead-marker hygiene (`StorageMarkersOnlyOnDead`), each proven necessary by `CE1`–`CE2c`. Balanced radix-8 `MaskTree` (`checkR3PositionalBatched`) cleanly decouples execution speedup from specification via `checkR3PositionalBatched_eq`. |
| **`V1`** | Adequacy & non-vacuity | `execution`: Positive witness `pos_witness_valid` / `pos_witness_behavior_iff` proves non-vacuity via `checkR3PositionalBatched`; `CE1`–`CE2c` prove sharpness on returning source programs; `Suite 1` executes live `Anneal.MirWp` obligations; `Suite 2` demonstrates mutual-cycle split impossibility (`CycleNodeA ↔ CycleNodeB`). External `nanoda_bin` export/check was `not measured` (verified via `TrustedBoundary.lean` kernel replay). |
| **`V2`** | Differential fuzzing | `not examined`: Deterministic `K = 4..128` chains and deterministic crate LLVM-IR extraction; no randomized property fuzzing over arbitrary CFGs was executed. |
| **`V3`** | Weak-memory / crash / silicon | `known not to apply`: Strictly sequential, deterministic `Trusted.MirSemantics@c131b320e` model without concurrency, weak memory, or crash semantics. |
| **`V4`** | Held-out ecosystem replay | `execution` (partial) / `not examined` (full body lifting): Call graphs extracted from `3` real crates (`zerocopy`, `miniz_oxide`, `regex-syntax`) via `rustc --emit=llvm-ir`; Lean `.olean` shard compilation evaluated on `14`-item-per-shard representative `Anneal.MirWp` bodies over the real extracted Tarjan DAG/SCC topology rather than full un-budgeted lifting of all `2,836` `regex-syntax` bodies. |

---

## Boundaries

- **Known not to apply (`Trusted.MirSemantics@c131b320e` memory/aliasing & concurrency extensions):** All equivalence theorems (`compact_preserves_eval_iff`, `bodyVerified_compact_iff`, `wpProg_transport_compact_iff`) apply to the scalar/bool/unit/never/fieldless-enum value-only fragment where `isSupportedScalarOrUnitTy` holds across locals and `.assign` operands use unprojected places; address-taken locals, `&mut` references, heap loads/stores, Tree Borrows aliasing, and concurrent memory models (`V3`) fall outside the modeled semantics.
- **Unsupported (splitting mutual recursion cycles across `.olean` modules):** Direct cross-module cyclic `import`s (`CycleNodeA ↔ CycleNodeB`) are unsupported by Lean `v4.34.1` and fail deterministically regardless of compilation order; mutually recursive definitions must stay within one SCC shard (as implemented in Suite 2) or be decoupled via explicit opaque axioms checked by an external rank/digest linker.
- **Not examined:**
  1. Un-budgeted monolithic Lean elaboration of all `609` (`miniz_oxide`) or `2,836` (`regex-syntax`) full Rust MIR bodies (`Suite 2` caps each shard at `node_budget_per_shard = 14` representative `Anneal.MirWp` bodies to measure import fanout and multi-SCC clustering within bounded wall time).
  2. Call edges omitted by `--crate-type lib -C opt-level=0 --emit=llvm-ir`: Rust generic functions not monomorphized in library roots (seen in `zerocopy`'s `284` non-generic symbols / `8` edges) do not appear in library LLVM IR; binary-level post-monomorphization or pre-monomorphization MIR call graphs may yield larger SCCs.
  3. Cold un-cached build times of `Trusted.*` / `Anneal.MirWp` (`"cached": true`), external `nanoda_bin` replay beyond `TrustedBoundary.lean`, standalone Rust MIR pass synthesis latency (`L3`), and randomized CFG differential fuzzing (`V2`).
- **Unknown:** Downstream cache hit-rate distributions under realistic mixed interface + proof refactoring commits across multi-thousand-function verified Rust crates remain unmeasured beyond single-proof-edit vs. full-cascade bounds.

---

## Evidence

### Package Support Artifacts (`support/`)

| Artifact | Size / LOC | SHA-256 Digest | Role |
| :--- | :---: | :--- | :--- |
| `support/MirR3LocalCompactionRefinement.lean` | `5,192` LOC (`239,819` B) | `9d233a6c51aa2acfb9b020dec22882a91f6238f13dec3af17fea00513697b130` | Formal `R0 → R3` refinement, `O(L + S log₂(L/8))` & `O(S × L)` checkers, `wpProg`/`BodyVerified`/`ProgramVerified` transport, `CE1`–`CE2c` |
| `support/probe_r3_compaction_and_scc_sharding.py` | `1,185` LOC (`50,681` B) | `eb8e163bfa1c18e45c023981966de9464bceb967a4bba36f0d04dee42a0ad116` | Live Lean `v4.34.1` + `rustc 1.98.0-nightly` Suite 1 & Suite 2 benchmark harness |
| `support/r3_compaction_and_scc_sharding_results.json` | `1,997` LOC (`47,756` B) | `3967475d51391134afe516e27b686c92c2ded0b41e42e008cf1764b130e268e6` | Complete `3`-run recorded measurement JSON (`Suite 1` + `Suite 2` + `cyclic_split_negative_check`) |

### Kernel Verification & `TrustedBoundary.lean` Audit Log (`2026-11-21`, Synchronous `v4.34.1`)

- Synchronous compile: `lean -DElab.async=false -Ddebug.skipKernelTC=false -R support -o <cache>/MirR3LocalCompactionRefinement.olean support/MirR3LocalCompactionRefinement.lean` → exit `0`.
- Kernel `#print axioms` across all `22` exported theorems (`validBodyCompaction_of_check`, `validProgramCompaction_of_check`, `wellFormed_compact_iff`, `behavior_compact_iff`, `diverges_compact_iff`, `satisfiesPost_compact_iff`, `compact_preserves_eval_iff`, `bodyVerified_compact_iff`, `programVerified_compact_iff`, `validBodyCompaction_of_checkR3LinearAssoc`, `checkR3PositionalBatched_eq`, `validBodyCompaction_of_checkR3PositionalBatched`, `wpProg_forward_of_compact`, `wpProg_backward_of_compact`, `wpProg_transport_compact_iff`, `satisfiesPost_and_not_diverges_of_wpProg`, `pos_witness_valid`, `pos_witness_behavior_iff`, `ce1_non_injective_renumbering_breaks_eval`, `ce2a_referenced_local_compacted_breaks_eval`, `ce2b_abi_arg_slot_not_preserved_breaks_eval`, `ce2c_return_slot_zero_moved_breaks_eval`): strictly `['propext']` on every theorem (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).
- Unmodified `joshlf/anneal@c131b320e` `trusted/audit/TrustedBoundary.lean` `"preflight"` (`SourceRole.theory`): `ok = true`.
- Unmodified `trusted/audit/TrustedBoundary.lean` `"audit"` (`trustLevel := 0`, `loadExts := false`, `requireMirWp := true`, importing `Trusted`, `Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`, `MirR3LocalCompactionRefinement`): `ok = true`, `replay = true`, `replayedDeclarations = 2314`, `reachableDeclarations = 3120`, `axioms = ["propext"]`.

### Primary Sources & Peer Corpus Citations

| Source | Immutable Revision / Identifier | Inspected Elements | Role |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `theory/Anneal/MirWp.lean`, `trusted/audit/TrustedBoundary.lean` | Normative / Source |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Lean 4 compiler & kernel (`-DElab.async=false -Ddebug.skipKernelTC=false`) | Normative / Execution |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) | Host `rustc` emitting `--emit=llvm-ir` call graphs | Execution |
| `google/zerocopy` | `0f4623ace6d17078dabe62799cf86f5533eba522` (`0.8.63`) | `zerocopy/src/lib.rs` compiled to LLVM IR (`284` fns, `8` intra edges) | Source / Execution |
| `Frommi/miniz_oxide` | `44e43c7786e379b2b1a7fde4aa0e63be719e583d` (`0.8.9`) | `miniz_oxide/src/lib.rs` compiled with `adler2` (`609` fns, `921` edges) | Source / Execution |
| `oyvindln/adler2` | `89a031a0f42eeff31c70dc598b398cbf31f1680f` (`2.0.1`) | `src/lib.rs` compiled to `--crate-type rlib` dependency for `miniz_oxide` | Execution |
| `rust-lang/regex` | `140167995737fa11dfe11b8af8b9aa143b790b4e` (`regex-syntax 0.8.11`) | `regex-syntax/src/lib.rs` compiled to LLVM IR (`2,836` fns, `5,258` edges, `9` multi-SCCs) | Source / Execution |
| Tarjan (1972) | `doi: 10.1137/0201010` | *Depth-First Search and Linear Graph Algorithms*, SIAM J. Comput. `1(2):146-160` | Normative |
| Peer Corpus Reports | `44c31fc277f0943c5e2e666884087e7ced453080`, `6e24ad128d7f29afc0f47733eb42ec4d3392ba63`, `2f3c272261d10a1115a28c11f20370cdb0b0c870` / `9a6617e007e953b87dad028926b0a76627ed47fe`, `d9e0710ae3f78e7ab9d1c5d458cba2d0c170fdc` | Baseline `R0..R3` scaling, `MoveToCopy`/`RemoveStorageMarkers` checker, SCC fixpoint summaries, sharded `.olean` auditing | Documentation / Reference |

---

## Revalidation

1. **Verify File Integrity & Dataset Consistency (`~0.1 s`):**
   Confirm `sha256sum support/*` matches the digests in **Evidence**, run `python3 -B -m py_compile support/probe_r3_compaction_and_scc_sharding.py` (using a `/tmp` pycache or `rm -rf support/__pycache__` afterward), and verify corpus structure via `python3 tools/reference.py catalog && python3 tools/reference.py check` from the corpus root.
2. **Synchronous Kernel Check & `TrustedBoundary.lean` Audit (`~20 s`):**
   Compile `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` into `/tmp/reval_cache` under Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `-DElab.async=false -Ddebug.skipKernelTC=false`), compile `support/MirR3LocalCompactionRefinement.lean` synchronously into `/tmp/reval_cache/MirR3LocalCompactionRefinement.olean` (verifying exit `0`, zero `sorry`, and `#print axioms` strictly `['propext']` across all `22` exported theorems), and run `trusted/audit/TrustedBoundary.lean` in `"preflight"` (`SourceRole.theory`) and `"audit"` (`trustLevel := 0`, `loadExts := false`, `requireMirWp := true`) modes to confirm `ok = true` and `replay = true`.
3. **Rerun Live Suite 1 & Suite 2 Benchmarks (`~5–10 min`):**
   Execute:
   ```bash
   python3 support/probe_r3_compaction_and_scc_sharding.py \
     --anneal-dir /path/to/anneal@c131b320e \
     --zerocopy-dir /path/to/zerocopy/zerocopy \
     --cache-dir /tmp/reval_cache \
     --repeats 3 \
     --out /tmp/reval_results.json
   ```
   Verify: (a) `LinearAssoc_OSL_rfl` and `PositionalUnbatched_OS_rfl` pass at `K = 32` (`~9.05 s` vs. `~1.14 s`) and fail at `K = 64` (`maxRecDepth`), while `PositionalBatched_OS_rfl` and `PositionalBatched_OS_decide` pass through `K = 128`; (b) `R3_SymbolicExecutes_Proof` beats `R0_SymbolicExecutes_Proof` (`~6.36×` at `K = 32`) and passes at `K = 64` where `R0` hits `maxRecDepth`; (c) `regex_syntax` LLVM IR contains `9` multi-node SCCs (`max size 25`), `CycleNodeA ↔ CycleNodeB` split fails in both build orders, and `H_sig`-gated 1-shard rebuild achieves `>10×` speedup vs. monolithic and naive cascades.
4. **Drift Triggers Requiring Re-Evaluation:** Re-verify whenever `joshlf/anneal` changes `Trusted.MirAst`, `Trusted.MirSemantics` (`LocalSlot`, `hasStorageAnnotation`, `evalStep`), or `TrustedBoundary.lean`, or when the Lean toolchain advances past `v4.34.1` (default `maxRecDepth` / kernel reduction changes).
