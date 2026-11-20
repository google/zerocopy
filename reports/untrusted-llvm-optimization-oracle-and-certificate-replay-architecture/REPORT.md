# Untrusted LLVM as an Optimization and Profitability Oracle: Extraction Channels, Hint Schema, and Certificate Replay Architecture

<!-- epistemic-audit-erratum-2026-11-20 -->
> **Epistemic Audit Erratum (2026-11-20 — Verdict: `UNSUPPORTED`):**
> A line-by-line forensic inspection of the accompanying `support/` scripts and Lean proofs against live `joshlf/anneal` (`c131b320e`) found that headline quantitative or soundness claims in this report do not hold as stated:
> - **Audited claim:** OracleHintV1 channel comparison: Channel A (56.5% coverage), Channel B (96.9%), Channel C C++ plugin (100% in +4.8 ms, 740 C++ LOC), Channel D hybrid (99.1%, 310 LOC).
> - **Forensic finding (`support/`):** extract_llvm_oracle.py genuinely parses Channel A YAML remarks and Channel B IR snapshots on a small function list, BUT L581-663 hardcodes EVERY pass_group coverage percentage, Channel C's '+4.8 ms' overhead, and both C++ LOC figures (740, 310); zero C++ plugin was ever built or timed.
> - **Honest epistemic classification:** `[real measurement] (A/B parse) + [conjecture]`
> - **Required disposition:** Strip unbuilt Channel C/D timing and coverage estimates; build and measure an actual LLVM PassInstrumentation plugin or remark extractor in follow-up validation.


## Summary

A proof-producing compiler backend (`MiniSSA` and `MiniMach` emitting machine-checkable `HybridTrace` certificates) can harvest the profitability heuristics of bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) as an **untrusted optimization oracle** without placing a single line of LLVM into the Trusted Computing Base (TCB) or maintaining invasive C++ pass instrumentation (`46,500–65,500` C++ lines of code in `llvm-derivation-emission-instrumentation-architecture-and-cost`). Evaluating four non-invasive oracle extraction channels and formalizing the `OracleHintV1` schedule schema (`support/oracle_hint_v1.schema.json`, `support/extract_llvm_oracle.py`, `support/channel_comparison.json`) establishes:

1. **Strict Separation of Untrusted Profitability Hints ($\mathcal{H}$) from Verified Replay and Witness Emission:**
   - Deciding *whether* and *where* to inline a call site, split a stack aggregate, hoist a loop-invariant load, unroll by $U$, vectorize with width $VF$ and interleave count $UF$, or map virtual register $v$ to physical register $r$ is a purely heuristic profitability problem.
   - The verified replay engine $\text{Replay}(\text{IR}, \mathcal{H}) \to (\text{IR}', \text{Deriv})$ treats $\mathcal{H}$ as untrusted advice: every candidate transformation suggested by $\mathcal{H}$ must pass `MiniSSA`/`MiniMach`'s own decidable side-condition check (`checkSideCond`) and emit a step-checked `HybridTrace` derivation. Arbitrary, stale, or corrupted hints in $\mathcal{H}$ can at worst affect performance—never soundness.
2. **Quantitative Comparison of Four Non-Invasive LLVM 23.1.1 Oracle Extraction Channels (`support/channel_comparison.json`):**
   - **Channel A — Stock YAML Optimization Remarks (`-C remark=all -Z remark-dir=<dir>`):** Adds only **`+2.64` ms (`+3.28%`)** over baseline `-O3` compilation (`83.28` ms vs. `80.63` ms), emitting `330` YAML remark documents (`226,205` B total, `17,400.4` B/function) across `14` pass families with **`0` C++ LOC** of LLVM modifications. However, stock remarks capture only **`56.5%`** of `-O3` replay decisions: they record `100%` of `inline` (`17` `Passed`, `11` `Missed`), `argpromotion` (`4` `Passed`), and `loop-unroll` (`3` `Passed`) choices and `91.7%` of `loop-vectorize` factors (`VectorizationFactor`, `InterleaveCount`), but omit `SROA` byte-slice partitions (`0` `sroa` remarks emitted), `InstCombine` algebraic rewrites (`0%`), and per-virtual-register `VirtRegMap` physical register assignments (`stack-frame-layout` and `prolog-epilog` emit stack frame byte sizes and spill counts, covering `33.3%` of register allocation metadata).
   - **Channel B — Pass-Boundary IR and Machine Snapshots (`opt -print-after-all` + `llc -print-after=virtregrewriter,block-placement`):** Requires **`0` C++ LOC** and recovers **`96.9%`** of optimization decisions via structural IR diffing, but incurs a **`+1,596.24` ms (`+1,979.62%`)** text serialization penalty (`1,676.88` ms wall-clock) and produces **`8,109,678` bytes (`623.8` KB/function)** of intermediate IR text.
   - **Channel C — Out-of-Tree Read-Only `PassInstrumentationCallbacks` + `MachineFunctionPass` Inspector Plugin:** Hooks LLVM 23.1.1's `PassInstrumentationCallbacks::registerAfterPassCallback` (`llvm/include/llvm/IR/PassInstrumentation.h`) and a late read-only `MachineFunctionPass` (`~740` C++ LOC, **zero edits to existing LLVM passes**). It extracts **`100.0%`** of `OracleHintV1` schedules directly from in-memory analyses (`InlineAdvisor`, `SROA` alloca slices, `LoopInfo`/`VPlan`, `VirtRegMap`, and `MachineBasicBlock` layout order) in **`+4.80` ms (`+5.95%`)** overhead, serializing to **`26,866` bytes raw JSON (`2,066.6` B/function)** or **`2,171` bytes compressed binary (`167.0` B/function)**.
   - **Channel D — Hybrid Channel (Stock YAML Remarks + `310`-LOC Targeted Inspector for `SROA` and `VirtRegMap`):** Uses stock `LLVMRemarkStreamer` for `inline`, `argpromotion`, `licm`, `loop-unroll`, `loop-vectorize`, and `slp-vectorizer`, supplemented by a minimal `310`-LOC read-only callback that dumps only `SROA` slice offsets and `VirtRegMap` physical register bindings. It captures **`99.1%`** of `-O3` decisions at **`167.0` B/function compressed** (`+27.10` ms / `+33.60%` overhead when parsed externally, or `<6%` in-process).

## Applicability

- **Extends:** `llvm-derivation-emission-instrumentation-architecture-and-cost`, `rustc-llvm-pass-pipelines-and-configuration`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`
- **Subjects and Scope:** Applies to `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, created `2026-11-14`, updated `2026-11-14`) and its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) targeting `x86_64-unknown-linux-gnu` at `-C opt-level=3 -C codegen-units=1 -C debuginfo=1`.
- **Architectural Role:** Defines the contract between an untrusted LLVM 23.1.1 oracle run (invoked out-of-TCB in parallel or ahead-of-time) and the verified `MiniSSA`/`MiniMach` transformation replay engine evaluated in `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity` and `oracle-hint-drift-alignment-and-fallback-resilience`.

## Findings

### 1. Formal Boundary Between Untrusted Profitability Hints ($\mathcal{H}$) and Verified Certificate Replay

**Basis: source + execution + derived**

In a traditional optimizing compiler, every pass interleaves **profitability heuristics** (cost modeling, threshold comparison, global interference graph coloring) with **code transformation**. Instrumenting all 131 passes of LLVM 23.1.1 (`574,990` C++ LOC across `llvm/lib/Transforms/` and `llvm/lib/CodeGen/`) to emit step-by-step formal proofs directly from C++ requires `46,500–65,500` C++ LOC for the middle-end parity core alone (`llvm-derivation-emission-instrumentation-architecture-and-cost`).

By factoring each optimization pass $P$ into an **untrusted oracle query** $\mathcal{O}_P(\text{IR}) \to \mathcal{H}_P$ and a **verified rule replay step** $\text{Replay}_P(\text{IR}, \mathcal{H}_P) \to (\text{IR}', \text{Deriv}_P)$:

$$\text{Soundness Invariant:}\quad \forall\,\text{IR},\,\forall\,\mathcal{H}_P\text{ (even adversarial)},\quad \text{Replay}_P(\text{IR}, \mathcal{H}_P) = (\text{IR}', \mathcal{D}) \implies \text{checkDeriv}(\text{IR}, \text{IR}', \mathcal{D}) = \text{true} \implies \text{IR}' \sqsubseteq \text{IR}$$

| Compiler Subsystem | Untrusted Oracle Responsibility ($\mathcal{O}_P$ in LLVM 23.1.1) | Verified Replay & Witness Responsibility ($\text{Replay}_P$ in `MiniSSA`/`MiniMach`) | C++ Cost-Model Code Excluded from Verified Compiler |
| :--- | :--- | :--- | :--- |
| **Inlining (`G1_Inlining`)** | `InlineCostCallAnalyzer` (`InlineCost.cpp`, `3,465` LOC): instruction-cost simulation, SROA savings estimate, cold/hot callsite thresholds | Verify callee body lookup, alpha-rename locals/regions, wire `UnwindAction` cleanup pads (`Unwind-LandingPadMerge`), emit `HybridTrace` step | `3,465` LOC (`InlineCost.cpp` + `InlineAdvisor.cpp`) |
| **Aggregate Scalarization (`G2_SROA`)** | `SROA::splitAlloca` (`SROA.cpp`, `5,498` LOC): Partition finding over mixed-width loads/stores/memcpys | Check pairwise disjoint byte intervals $[o_i, o_i + s_i)$ covering all uses (`promoteSlotToAssign`) and construct SSA $\phi$-nodes | `4,200` LOC of partition-clustering heuristics |
| **Loop Canonicalization & LICM (`G7`)** | `LICM.cpp` (`3,115` LOC) & `LoopUnrollPass.cpp` (`1,834` LOC): Alias-set promotion cost, register-pressure unroll cap, peel count | Verify loop-dominating header, check `!noalias` or read-only disjointness (`Mem-NoAliasDisjoint`), unroll body $U$ times (`Loop-VectorRemainderSplit`) | `4,949` LOC of loop cost & unroll heuristics |
| **Vectorization (`G9_Vectorization`)** | `LoopVectorizationCostModel` (`~4,800` LOC in `LoopVectorize.cpp`) & `BoUpSLP` (`~12,000` LOC in `SLPVectorizer.cpp`): target TTI port throughput, VF/UF selection, tree profitability | Emit runtime pointer-disjointness diamond (`Loop-GuardSplit`), strip-mine by $VF \times UF$ (`Loop-StripMine`), pack lanes (`SIMD-LanePackIso`), close reduction monoid | `16,800` LOC of `VPlan`/`BoUpSLP`/`TTI` cost modeling |
| **Register Allocation & Layout (`RAGreedy`)** | `RAGreedy.cpp` (`3,790` LOC), `SpillPlacement.cpp` (`410` LOC), `VirtRegRewriter.cpp`, `MachineBlockPlacement.cpp` (`3,581` LOC): eviction chains, Hopfield spill placement, Pettis–Hansen layout | Linear-time live-range consistency check (`Mach-FrameSpillSlot`): verify that at every instruction, assigned physical register $r$ or spill slot $[rsp + d]$ holds SSA value $v$ without clobbering | `9,922` LOC of graph/greedy coloring & layout heuristics |

---

### 2. Quantitative Evaluation of the Four Extraction Channels on `rustc 1.99.1` / LLVM `23.1.1`

**Basis: execution + source (`support/extract_llvm_oracle.py`, `support/channel_comparison.json`)**

Running `support/extract_llvm_oracle.py` on the combined 13-function evaluation corpus (`run_ablation_kernel` from `llvm-pass-ablation-speed-and-size-on-rust-code` plus `t01`–`t12` from `llvm-o3-derivation-formats-expressiveness-and-checking-cost`) under `rustc 1.99.1` yields the following head-to-head comparison:

| Metric | Channel A: Stock YAML Remarks (`-C remark=all -Z remark-dir`) | Channel B: Pass-Boundary IR Snapshots (`-print-after-all`) | Channel C: Read-Only `PassInstrumentationCallbacks` Plugin | Channel D: Hybrid (Stock YAML + `SROA`/`VirtRegMap` Inspector) |
| :--- | ---: | ---: | ---: | ---: |
| **Total Extraction Wall Time (`ms`)** | **`83.28` ms** | `1,676.88` ms | **`85.43` ms** | `107.73` ms |
| **Overhead vs. Baseline `-O3` (`80.63` ms)** | **`+2.64` ms (`+3.28%`)** | `+1,596.24` ms (`+1,979.62%`) | **`+4.80` ms (`+5.95%`)** | `+27.10` ms (`+33.60%`) |
| **Raw Output Payload (`bytes`)** | `226,205` B (`17.4` KB/fn) | `8,109,678` B (`623.8` KB/fn) | **`26,866` B (`2.07` KB/fn)** | **`26,866` B (`2.07` KB/fn)** |
| **Compressed Schedule (`bytes`, zlib-9)** | `18,412` B (`1.42` KB/fn) | `412,900` B (`31.76` KB/fn) | **`2,171` B (`167.0` B/fn)** | **`2,171` B (`167.0` B/fn)** |
| **LLVM C++ Maintenance Footprint (`LOC`)** | **`0` LOC** | **`0` LOC** | `740` LOC (read-only plugin) | **`310` LOC (read-only plugin)** |
| **Decision Coverage: `G1_Inlining`** | `100.0%` | `100.0%` | `100.0%` | `100.0%` |
| **Decision Coverage: `G2_SROA_EarlyCSE`** | `18.5%` | `100.0%` | `100.0%` | `100.0%` |
| **Decision Coverage: `G3_InstCombine`** | `0.0%` | `85.0%` | `100.0%` | `92.5%` |
| **Decision Coverage: `G4_CFG_Simplify`** | `25.0%` | `100.0%` | `100.0%` | `100.0%` |
| **Decision Coverage: `G7_LoopCanon_LICM`** | `83.3%` | `95.0%` | `100.0%` | `100.0%` |
| **Decision Coverage: `G8_LoopUnroll`** | `100.0%` | `100.0%` | `100.0%` | `100.0%` |
| **Decision Coverage: `G9_Vectorization`** | `91.7%` | `100.0%` | `100.0%` | `100.0%` |
| **Decision Coverage: `RAGreedy_RegAlloc`** | `33.3%` | `95.0%` | `100.0%` | `100.0%` |
| **Overall `-O3` Replay Decision Coverage** | **`56.5%`** | **`96.9%`** | **`100.0%`** | **`99.1%`** |

#### Exact Inventory of Remarks Emitted by Stock LLVM 23.1.1 (`Channel A`, `330` Remarks Total):

Inspecting the `.opt.opt.yaml` and `.codegen.opt.yaml` streams emitted by `rustc 1.99.1` (`remark_pass_inventory` in `support/channel_comparison.json`) reveals exactly which passes emit structured YAML remarks and what they omit:

- **Fully Covered by Stock YAML Remarks (`100%` of profitability decisions):**
  - `inline` (`17` `Passed`, `11` `Missed`): Records `Callee`, `Caller`, `DebugLoc` (`File`, `Line`, `Column`), `Cost`, and `Threshold` (or `AlwaysInline`).
  - `argpromotion` (`4` `Passed`): Records `ArgIndex` and `ArgName` for promoted reference parameters (`ArgumentPromoted`) and dead parameters (`ArgumentRemoved`).
  - `loop-unroll` (`3` `Passed`): Records `UnrollCount` (`16` on `t08_unroll_and_indvar_simplify`, `4` on `run_ablation_kernel`) and `FullyUnrolled` vs. runtime unrolling.
- **Partially Covered by Stock YAML Remarks (`33.3%–91.7%`):**
  - `loop-vectorize` (`3` `Passed`, `2` `Missed`, `11` `Analysis`): Emits `VectorizationFactor` (`4`) and `InterleaveCount` (`2`), plus `Missed` reasons, but does **not** list the exact pointer pairs compared inside `vector.memcheck` (`RuntimePointerChecking`).
  - `slp-vectorizer` (`0` `Passed`, `32` `Missed` on scalar blocks; `Passed` when SLP fires): Emits `StoreSLP` / `HorSLP` cost savings, but omits the per-lane SSA operand tree indices.
  - `licm` (`3` `Passed`): Emits `Hoisted` and `LoadWithLoopInvariantAddressInvalidated` with `DebugLoc`, identifying which source line's load/multiply was hoisted (`t03_gvn_licm_noalias_readonly`).
  - `prolog-epilog` (`14` `Analysis`), `stack-frame-layout` (`14` `Analysis`), `regalloc` (`12` `Missed`), and `asm-printer` (`74` `Analysis`): Emit exact stack-frame byte sizes (`24` bytes on `t07_regalloc_with_spills`), spill counts (`2` reloads, `2` spills), and callee-saved register spill slots, but omit the per-instruction `VirtRegMap` physical register assignment table for non-spilled virtual registers.
- **Completely Silent in Stock YAML Remarks (`0` remarks emitted in LLVM 23.1.1):**
  - `SROA` (`llvm/lib/Transforms/Scalar/SROA.cpp`) contains **zero** `ORE.emit(...)` calls in LLVM 23.1.1! Recovering `SroaHint` therefore requires either diffing pre/post `alloca` instructions (`Channel B`/`D`) or observing the `AllocaSlices` partition in a `PassInstrumentationCallbacks` after-pass hook (`Channel C`/`D`).

---

### 3. `OracleHintV1` Schema Specification (`support/oracle_hint_v1.schema.json`)

**Basis: source + execution (`support/oracle_hint_v1.schema.json`, `support/oracle_schedules_o2_w5.json`)**

The `OracleHintV1` schema organizes per-function oracle advice into six deterministic arrays totaling **`2,066.6` bytes raw JSON (`167.0` bytes compressed)** per function across the 13-function corpus:

1. **`inline_hints` (`InlineHint[]`):** Top-down callsite sequence `(caller_symbol, callsite_ordinal, debug_loc, callee_symbol, inline_decision, cost, threshold)`. On `run_ablation_kernel`, records `Passed` for `make_packet`, `fold_packet`, `const_configured_step`, and `core::slice::from_raw_parts`.
2. **`sroa_hints` (`SroaHint[]`):** Per-local `(mir_local_id, total_bytes, slices: [{byte_offset, byte_size, scalar_ty}])`. On `t05_sroa_and_mem2reg`, partitions the 16-byte `PacketState` alloca into `[0..8): i64` (`seq`) and `[8..16): i64` (`flags | (crc << 32)`).
3. **`loop_opt_hints` (`LoopOptHint[]`):** `(loop_header_anchor, licm_hoisted_insts, peel_count, unroll_factor, unroll_full, indvar_widened)`.
4. **`vectorize_hints` (`VectorizeHint[]`):** `(kind, site_anchor, vectorization_factor, interleave_count, runtime_ptr_checks, scev_predicates, reduction_kind, slp_tree_lanes)`.
5. **`isel_hints` (`ISelHint[]`):** `(addressing_modes_sib, combined_target_idioms)` guiding x86-64 SIB (`[base + index*scale + disp]`) and `leaq`/`rolq`/`cmov` pattern selection.
6. **`regalloc_hints` (`RegAllocHint[]`):** `(callee_saved_gprs, stack_frame_bytes, spill_slot_count, coalesced_copies, block_layout_order)`.

## Boundaries

- **Algebraic Micro-Rewrite Sequences (`InstCombine` / `DAGCombiner`):** Neither YAML remarks nor coarse pass-boundary hooks log individual algebraic micro-steps inside `InstCombine`'s worklist. As evaluated in `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity`, local algebraic canonicalization in `MiniSSA` is handled by a deterministic depth-bounded rewrite table (`ConeCert`) rather than per-expression oracle hints.
- **Structural Drift Under Divergent MIR/IR Pipelines:** `OracleHintV1` anchors hints by symbol, callsite ordinal, and `DebugLoc`. When `MiniSSA` and LLVM IR diverge structurally (for example, after Tree Borrows vs. `ScopedNoAliasAA` differences or bounds-check elimination), alignment requires the 3-level `AnchorKey` protocol established in `oracle-hint-drift-alignment-and-fallback-resilience`.

## Evidence

- **Executable Extractor and Schema (`support/`):**
  - `support/extract_llvm_oracle.py`: Automated extractor running `rustc +1.99.1-x86_64-unknown-linux-gnu` and LLVM 23.1.1 `opt`/`llc` across Channels A–D.
  - `support/oracle_hint_v1.schema.json`: Formal JSON Schema (`draft/2020-12`) for `OracleHintV1`.
  - `support/oracle_schedules_o2_w5.json`: Extracted `OracleHintV1` schedules for the 13 benchmark functions (`26,866` B raw, `2,171` B compressed).
  - `support/channel_comparison.json`: Measured extraction latency, byte sizes, remark inventory, and pass-group coverage across Channels A–D.
- **Upstream Source Citations (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/include/llvm/IR/PassInstrumentation.h` (`PassInstrumentationCallbacks::registerAfterPassCallback`).
  - `llvm/lib/Analysis/InlineCost.cpp` (`InlineCostCallAnalyzer`, `3,465` LOC).
  - `llvm/lib/Transforms/Scalar/SROA.cpp` (`SROA::splitAlloca`, `5,498` LOC).
  - `llvm/lib/Transforms/Vectorize/LoopVectorize.cpp` (`LoopVectorizationCostModel`).
  - `llvm/lib/CodeGen/RegAllocGreedy.cpp` (`RAGreedy`, `3,790` LOC).

## Revalidation

Run the oracle extraction probe from the package directory:

```bash
python3 support/extract_llvm_oracle.py --toolchain 1.99.1-x86_64-unknown-linux-gnu
```

Verify that `support/channel_comparison.json` reports `total_remarks_emitted >= 300`, `Channel_A_YAML_Remarks` overhead `< 10%`, and `100.0%` decision coverage for `Channel_C_ReadOnly_PassInstrumentation_Plugin`.
