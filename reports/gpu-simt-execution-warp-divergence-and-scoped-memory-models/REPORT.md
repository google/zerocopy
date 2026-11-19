# GPU SIMT Execution, Warp Divergence, Scoped Weak Memory Models, Asynchronous Pipelines, and Safe Ownership

## Summary

Programmable GPUs invalidate four assumptions built into scalar CPU compilers, flat C/C++11/Rust memory models, and sequential borrow checkers:

1. **SIMT Convergence & Uniformity:** Since NVIDIA Volta (`sm_70`), Independent Thread Scheduling (ITS) gives every thread its own PC and call stack, breaking pre-Volta warp-synchronous lockstep and requiring explicit `bar.warp.sync` (`__syncwarp(mask)`) and `elect.sync` (`sm_90+`). Scalar CFG optimizations (hoisting, sinking, jump threading, unrolling) miscompile convergent collectives unless constrained by LLVM convergence-control tokens (`llvm.experimental.convergence.{entry,loop,anchor}` with `convergencectrl` operand bundles), SPIR-V `SPV_KHR_maximal_reconvergence`, or W3C WGSL's compile-time static uniformity dependency graph (`RequiredToBeUniform.error ->* MayBeNonUniform`).
2. **Scoped Weak Memory & Proxies:** NVIDIA PTX ISA 9.5 §8 (formalized by Lustig, Sahasrabuddhe & Giroux, ASPLOS '19) and Khronos Vulkan require **symmetric scope inclusion** (`morally strong` / `mutually-ordered`). Direct cross-scope pairs (`.cta` $\to$ `.gpu` across CTAs) and mismatched `fence.sc` pairs fail to synchronize. On mixed-scope chains $A(\text{CTA }0) \xrightarrow{\text{.cta}} B(\text{CTA }0) \xrightarrow{\text{.gpu}} C(\text{CTA }1)$, models diverge normatively: PTX's base causality order (`cause_base`) is transitive (A-cumulative) when each hop is morally strong and proxy-preserved, whereas HRF-direct rejects mixed scopes and base Vulkan (`vulkanMemoryModelAvailabilityVisibilityChains = VK_FALSE`) caps availability/visibility chains at length 1 (making $A \to C$ a data race unless chains are enabled). Distinct **memory proxies** (`generic`, `async`, `tensormap`, `fabric`, `readonly`, `alias`) break `proxy-preserved base causality order` without explicit proxy fences (`fence.proxy.async`, `fence.proxy.tensormap::generic.acquire`).
3. **Hopper (`sm_90`) & Blackwell (`sm_100`) Async Pipelines:** Tensor Memory Accelerator (`TMA`, `cp.async.bulk.tensor`) runs in the `async` proxy alongside 64-bit SMEM `mbarrier` objects whose 1-bit phase parity (`0 <-> 1`) and byte-counted transactions (`mbarrier.arrive.expect_tx`, `mbarrier.try_wait.parity`) prevent circular-buffer races only under strict initial parity, wraparound flips, single-lane `elect.sync` arrival, and exact byte counts. Blackwell adds 256 KiB/CTA 2D **Tensor Memory (`TMEM`)** (`128 lanes × 512 cols × 32-bit`, warp-partitioned into 32-lane slices for `tcgen05.ld`/`st`), single-thread async `tcgen05.mma`, and warpgroup-aligned `setmaxnreg.{inc,dec}.sync.aligned.u32` register transfers.
4. **Static Verification & Ownership:** **Faial** (Cogumbreiro et al., CAV '21) proves intra-block CUDA data-race freedom compositionally via Coq-mechanized Memory Access Protocols (barrier alignment + SMT-checked symbolic traces). **Descend** (Köpcke, Gorlatch & Steuwer, PLDI '24) extends Rust ownership with address-space-qualified references (`&r w m d`), execution-hierarchy narrowing (`narrowing_check`), disjoint array views, and static barrier-divergence rejection (`syncable_under_exec`).

A standalone Python 3.10+ probe (`support/verify_gpu_scoped_memory_and_mbarrier.py`) mechanizes all three layers: 6 scoped-memory/proxy litmus tests, an explicit-state BFS `mbarrier` pipeline model checker (proving 2-stage and 3-stage safety across 62 and 148 states while synthesizing minimal deadlock/race/UB traces for 6 bug classes), and a 6-case WGSL uniformity analyzer.

## Applicability

This report synthesizes eleven durable primary subjects across four related technical layers:

- **NVIDIA PTX & Hardware Execution:** **PTX ISA Version 9.5** provides normative semantics for ITS (§3.2, `sm_70+`), Memory Consistency (§8, `sm_70+`), `.cluster` scope (PTX 7.8, `sm_90+`), `elect.sync` / `fence.proxy.async` / `setmaxnreg` (PTX 8.0, `sm_90+`/`sm_90a`), `mbarrier` (§9.7.15.16), TMA `cp.async.bulk.tensor` (§9.7.10.28), and Blackwell `TMEM`/`tcgen05.*` (§9.7.18, `sm_100a`/`sm_100f`). **Lustig, Sahasrabuddhe & Giroux (ASPLOS '19)** and **`NVlabs/ptxmemorymodel`** (`f0dc6b7f85f34fc19fb76e7495864656276fa002`) formalize the `sm_70+` model in Alloy (`ptx.als`), define Scoped RC11 (`src11.als`), and prove Scoped RC11 $\to$ PTX compilation sound in Coq (`src11_ptx.v`); they predate Hopper `.cluster` and `async`/`tensormap` proxies, which are covered from PTX ISA 9.5. **`NVIDIA/cutlass`** (`88d690dec7c58a291e95ae44c9e68d800602fed5`) supplies production inline-PTX lowering evidence.
- **Portable Shader & IR Standards:** **Khronos Vulkan Memory Model** (`KhronosGroup/Vulkan-Docs@f7de774cace1509af0f10b8d859c973b5354ff62`), **SPIR-V `SPV_KHR_maximal_reconvergence`** (`KhronosGroup/SPIRV-Registry@25574da230687e0beb5d285c2746a7c0d2e17dcd`), **W3C WGSL** (`gpuweb/gpuweb@d178d9145ab1652ec933e71a8c30e8f6470f00a3`), and **LLVM Convergence Control** (`llvm/llvm-project@1780833aa0f119a425d7f993aaac29d03cb04da6`) provide cross-vendor IR and shader convergence/memory semantics.
- **Static DRF & Safe GPU Ownership:** **Faial** (CAV '21) applies to intra-CTA barrier-synchronized CUDA kernels; **Descend** (PLDI '24; `arXiv:2305.03448`; `descend-lang/descend@e98d4c086f369496b79294b333086020ab08e0c6`) applies to safe host+device CUDA programs (distinguishing the May 2023 preprint from the pinned compiler's added warp/atomic support).

**Adjacent Corpus Packages:** Flat CPU weak memory models (C11, RC11, IMM, Promising Semantics, x86-TSO, ARMv8-A, and Rust `core::sync::atomic` lowering) live in `weak-memory-concurrency-models-hardware-mappings-and-optimizations` and are not duplicated here. Broader shader-verification context appears in `anneal-ai-safety-neural-planning-cad-media-and-iot-survey`.

**Probe Scope:** `support/verify_gpu_scoped_memory_and_mbarrier.py` checks abstract axiomatic and finite-state models transcribed directly from PTX ISA 9.5, `ptx.als`, Vulkan `memorymodel.adoc`, and WGSL `index.bs`; it does not execute on physical GPU hardware (see **Boundaries**).

## Findings

### 1. SIMT Execution, Volta+ Independent Thread Scheduling (ITS), and Convergence Semantics

Basis: normative + documentation + source

#### 1.1 Pre-Volta IPDom Lockstep vs. Volta+ (`sm_70+`) Independent Thread Scheduling

Prior to Volta (`sm_6x` and earlier), each 32-thread warp shared one PC, a 32-bit active mask, and a hardware divergence stack reconverging at the Immediate Post-Dominator (IPDom) of conditional branches (PTX ISA 9.5 §3.2, L2052–L2056). Single-PC lockstep caused intra-warp spinlocks to deadlock when divergent lanes serialized, while allowing legacy "warp-synchronous" kernels to omit barriers after branches or during intra-warp shared-memory reductions.

Starting with Volta (`sm_70`), **Independent Thread Scheduling (ITS)** maintains a per-thread PC and call stack and lets the hardware schedule optimizer yield, diverge, and reconverge at sub-warp granularity (PTX ISA 9.5 §3.2, L2058–L2065):
1. **Explicit warp barriers replace implicit lockstep:** Threads reaching the same post-branch instruction on `sm_70+` need not execute together unless synchronized with `bar.warp.sync membermask;` (`__syncwarp(mask)`, PTX ISA 9.5 §9.7.15.2) or `.sync` collectives (`shfl.sync`, `vote.sync`, `match.sync`, `redux.sync`).
2. **Deterministic leader election (`elect.sync`):** Introduced in PTX ISA 8.0 (`sm_90+`, §9.7.15.15, L34954–L34996), `elect.sync d|p, membermask;` waits for all threads in `membermask` (UB if the executing lane is absent) and sets predicate `p = True` on exactly one deterministic active leader lane (`False` elsewhere; lane ID in `d` or `_`). Production Hopper/Blackwell kernels (`NVIDIA/cutlass` `include/cute/arch/cluster_sm90.hpp` L189, L219) use `elect.sync`—not `threadIdx.x == 0`—to guard single-thread TMA, `mbarrier.arrive.expect_tx`, and `tcgen05.mma` launches.

#### 1.2 Scalar Compiler Miscompilations and LLVM Convergence Control

Scalar LLVM IR omits the active communicating thread set ("tangle") from SSA dataflow, causing standard CPU transforms to miscompile GPU collectives (`__syncthreads`, `__shfl_sync`, `ballot`, pixel-shader `textureSample` derivatives; `llvm/docs/ConvergentOperations.md` L48–L90, L1192–L1460):
- **Hoisting & CSE (L1379–L1446):** Merging convergent calls across `if`/`else` changes the communicating set from disjoint subsets $S_1, S_2$ to $S_1 \cup S_2$; speculative hoisting above a guard `if (cond)` can read out-of-range lane IDs or introduce UB on lanes where `cond` is false.
- **Sinking & Jump Threading:** Cloning or sinking a barrier into divergent blocks splits a converged set $S$ across distinct static instructions, causing permanent barrier deadlock.
- **Loop Unrolling / Unswitching (L1209–L1260):** Unrolling a loop with divergent trip counts changes which iterations coalesce in the unrolled tail.

Because LLVM's legacy `convergent` attribute could not express opportunistic sub-warp collectives or divergent loop exits (L220–L495), LLVM **Convergence Control** (`ConvergentOperations.md` L496–L948; `ConvergenceAndUniformity.md`) introduces SSA `token` values (forbidden in `phi` and `select`, L514–L516) attached via `"convergencectrl"(token %tok)` operand bundles:

| Intrinsic (`ConvergentOperations.md` L556–L700) | Semantics | Typical Role |
| :--- | :--- | :--- |
| `@llvm.experimental.convergence.entry()` | Token for the converged thread set entering the current function (entry block only; no bundle). | Barriers and structured subgroup collectives tied to caller convergence. |
| `@llvm.experimental.convergence.anchor()` | Implementation-defined opportunistic subset of converged threads at the anchor (no bundle). | Opportunistic warp aggregation (`match.sync`/atomic coalescing). |
| `@llvm.experimental.convergence.loop() [ "convergencectrl"(token %outer) ]` | Cycle-header token: two threads converge on iteration $k$ iff they held converged `%outer` tokens entering the cycle and reached iteration $k$ together. | Constraining loop unrolling and divergent-exit sinking in cycles. |

Well-formedness relies on two normative laws (L522–L527, L772–L948):
- **Token Equivalence:** Convergent call `U` controlled by `%tok` (defined by `D`) executes converged dynamic instances across two threads **iff** both threads received `%tok` from converged dynamic instances of `D`.
- **Static Closed-Path / Convergence Region Rules:** No cycle in the CFG may traverse a convergence region without re-evaluating its defining token `D`, preventing temporal divergence from mixing iteration $k$ of one lane with iteration $k+1$ of another.

#### 1.3 SPIR-V `SPV_KHR_maximal_reconvergence`

`SPV_KHR_maximal_reconvergence` (`KhronosGroup/SPIRV-Registry@25574da230687e0beb5d285c2746a7c0d2e17dcd`, L147–L309) eliminates cross-vendor SPIR-V reconvergence ambiguity by modeling execution with **tangles** $T(I)$:
- **Initial State (L158):** Entry instruction $F$ starts maximally converged.
- **Exclusive Divergence Points (L174–L199):** Invocations never spontaneously diverge; divergence occurs *only* at `OpBranchConditional` (at most 2 tangles), `OpSwitch` (at least one tangle per case construct, at most one per unique selector), or when the last active lane in a 2×2 pixel quad runs `OpDemoteToHelperInvocation`/`OpKill`.
- **Mandatory Reconvergence Points (L250–L289):** All non-escaping invocations of a parent tangle reconverge at: (1) `OpSelectionMerge` Merge Block, (2) `OpLoopMerge` Merge Block, (3) `OpLoopMerge` Continue Target (ensuring converged loop iterations), and (4) the instruction after `OpFunctionCall`.
- **Non-Reconvergence Prohibition (L291–L309):** Tangles **must not** merge elsewhere—in particular, lanes exiting a loop on different iterations stay diverged inside break blocks until the loop's Merge Block, and instructions cannot be sunk into continue constructs unless proven converged.

#### 1.4 Cross-Model Comparison of SIMT Execution & Reconvergence

| Dimension | Pre-Volta IPDom | Volta+ ITS (`sm_70+`, PTX 9.5) | SPIR-V `SPV_KHR_maximal_reconvergence` | LLVM Convergence Control |
| :--- | :--- | :--- | :--- | :--- |
| **Execution State** | 1 PC + 32-bit mask + stack/warp | Per-thread PC + call stack | Structured CFG tangles $T(I)$ | Dynamic instances + SSA `token` |
| **Spontaneous Divergence** | Impossible | Permitted between `.sync` ops | Forbidden (except quad demotion) | Governed by token provenance |
| **Intra-Warp Spinlocks** | Deadlocks on divergence | Can yield and progress | Outside extension scope | Orthogonal (L850) |
| **Post-`if` Reconvergence** | Guaranteed at IPDom | Requires `bar.warp.sync` | Guaranteed at Merge Block | Only when sharing same `token` |
| **Loop Iteration Alignment** | At backedge / IPDom | Requires explicit `.sync` | Guaranteed at Continue Target | Via `convergence.loop` token |

---

### 2. Static Uniformity Analysis (W3C WGSL) and Compositional DRF Verification (Faial)

Basis: normative + source + execution

#### 2.1 W3C WGSL Static Uniformity Analysis

To guarantee portable shader safety across Vulkan, Metal, and D3D12 without hardware hangs, **W3C WGSL** (`gpuweb/gpuweb@d178d9145ab1652ec933e71a8c30e8f6470f00a3`, `wgsl/index.bs` L12504–L13950) enforces a compile-time **Static Uniformity Analysis** for barriers (`workgroupBarrier`, `storageBarrier`, `textureBarrier`, `workgroupUniformLoad`), implicit-derivative sampling (`textureSample`), and uniform-argument subgroup operations.

**Dependency Graph & Rejection Rule (L12633–L12674):**
Each function builds a directed graph with sentinel nodes `RequiredToBeUniform.{error,warning,info}` (obligations) and `MayBeNonUniform` (non-uniform sources such as `local_invocation_id` or non-uniform buffer loads), plus control-flow (`CF`) and expression-value (`V`) nodes. A compile-time **uniformity error** triggers **iff** a directed path exists from `RequiredToBeUniform.error` to `MayBeNonUniform` (L12663–L12664). Because WGSL forbids recursion, functions are summarized bottom-up via call-site tags (`CallSiteRequiredToBeUniform.S` / `CallSiteNoRestriction`), return tags (`ReturnValueMayBeNonUniform` / `NoRestriction`), and parameter tags (`ParameterRequiredToBeUniform.S`, `ParameterContentsRequiredToBeUniform.S`, L12676–L12735).

**Behavior-Coupled Control-Flow Rules (L13079–L13260):**
WGSL pairs uniformity with static statement behaviors $\subseteq \{\text{Next}, \text{Break}, \text{Continue}, \text{Return}\}$:
- **`if e s1 else s2` (L13168–L13178):** Analyzes `s1, s2` under branch condition node `V`. If combined behavior is `{Next}`, **reconvergence restores the entry `CF`** for following statements; otherwise (e.g., `{Next, Return}` from a divergent early `return`), exit control flow becomes a fresh `CFend -> {CF1, CF2}`, tainting all subsequent statements in the block.
- **Loops & `break if` (L13111–L13225, L13250–L13258):** Header `CF'` links `CF' -> CF` and, whenever body `s1` intersects `{Next, Continue}`, adds back-edge `CF' -> CF1` (or `CF2` via `continuing`). A `break if e;` adds `CFend -> V`; any non-uniform loop exit therefore feeds `MayBeNonUniform` around the back-edge into `CF'`, rejecting barriers/subgroup ops even *before* the `break if`.
- **Incompleteness (L13810 `#uniformity-example3`):** Flow-insensitivity across composite struct/array members and lack of arithmetic refinement cause WGSL to reject some semantically uniform shaders (mitigated via `workgroupUniformLoad` or `{Next}`-only refactoring).

**Probe Verification (`support/verify_gpu_scoped_memory_and_mbarrier.py`, Part 3):**
All 6 modeled WGSL test cases match `wgsl/index.bs`:
1. `if (uniform_buf) { workgroupBarrier(); }` $\to$ **PASS**.
2. `if (lid.x) { workgroupBarrier(); }` $\to$ **REJECT** (`RequiredToBeUniform.error -> Call_workgroupBarrier_3 -> CF_branch_2 -> V_lid_1 -> MayBeNonUniform`).
3. `if (lid.x) { return; } workgroupBarrier();` $\to$ **REJECT** (via `CF_if_end_3 -> CF_branch_2 -> V_lid_1`).
4. `loop { subgroupAdd(); break if (lid.x); }` $\to$ **REJECT** (back-edge `CF_loop_hdr_1 -> CF_break_if_4 -> V_lid_3`).
5. `if (lid.x) { x = 1; } else { x = 2; } workgroupBarrier();` $\to$ **PASS** (`{Next}` restores `CF_start`).
6. Same reconverged `if`, followed by uniform-argument consumer of `x` $\to$ **REJECT** (value edge `V_load_x_9 -> VarMerge_x_7 -> CF_branch_2 -> V_lid_1` survives CF reconvergence).

#### 2.2 Compositional GPU Data-Race Verification: Faial (CAV '21)

**Faial** (Cogumbreiro, Lange, Liew Zhen Rong & Zicarelli, CAV '21, DOI `10.1007/978-3-030-81685-8_19`) verifies intra-block CUDA **Data-Race Freedom (DRF)** without user-supplied loop invariants or symbolic-execution loop unrolling by inferring **Memory Access Protocols (MAPs)**—behavioral types abstracting away data values to record only array indices and barrier positions—with **Coq-mechanized** correctness proofs:

1. **Well-Formed Protocols ($p \in \mathcal{W}$, Def. 1):** Separates unsynchronized fragments $u$ (`rd[e]`, `wr[e]`, conditionals, unsynchronized loops) from synchronized protocols $p$ (`sync`, `p; q`, `forS x in n..m { p }`), requiring `swf(p)`, `fv(p) ⊆ {tid}`, and non-empty synchronized loops. Barriers partition histories into phases $P$; a phase is safe iff no distinct threads $t_1 \ne t_2$ access the same index $k$ with at least one write.
2. **Barrier Alignment (Theorem 1, L1110):** Synchronized loops with trailing unsynchronized accesses (`u1 ; forS x in n..m { p ; u2 }`) overlap `u2` of iteration $x$ with the start of iteration $x+1$ (the cross-iteration matrix-transpose race missed by `PUG`). `align(p) = (q, u)` peels the first iteration and shifts trailing accesses across the loop boundary; **Theorem 1** proves `p` is DRF iff `q ; u` is DRF.
3. **Compositionality & Splitting (Theorems 2 & 3, L1198, L1288):** For any aligned $p \in \mathcal{A}$ and DRF context $C[\text{skip}; \text{sync}]$, $C[p]$ is DRF iff $p$ is DRF (**Theorem 2**). `split(p)` breaks $p$ into independent barrier-free symbolic traces $h$ checked independently by Z3; **Theorem 3** proves `safe(H1) <-> safe(H2)` (exact race preservation and reflection—imprecision arises solely in front-end CUDA-to-MAP inference).

Across CAV '21's 260-kernel (5-tool) and 487-kernel (3-tool) benchmarks, Faial correctly verified at least **1.42× more real-world kernels** with near-linear scaling (e.g., Table 1: on `transposeDiagonal`, `first-iter`, and `last-iter`, Faial accurately flagged `1/1` true races and certified fixed kernels `DRF`, while `PUG` missed the `transposeDiagonal` race, `GPUVerify` emitted `0/2` and `0/1` false positives, and `GKLEE`/`SESA` timed out at 90 s).

---

### 3. Scoped Weak Memory Models, Non-Transitivity, and Memory Proxies (PTX, Vulkan, WGSL)

Basis: normative + source + execution + derived

Physically distributed, non-coherent per-SM L1 caches, cluster DSMEM, shared L2, and host PCIe/NVLink fabrics force GPUs away from flat CPU coherence (documented in `weak-memory-concurrency-models-hardware-mappings-and-optimizations`) toward **scoped, non-multi-copy-atomic, proxy-partitioned weak memory models**.

#### 3.1 NVIDIA PTX Memory Consistency Model (PTX ISA 9.5 §8 & Lustig et al. ASPLOS '19)

Applicable to all PTX versions on **`sm_70` and later** (excluding texture `ld.global.nc` and surface accesses, §8.1), the PTX model (`NVlabs/ptxmemorymodel/ptx.als`, Lustig et al. ASPLOS '19 §3.3–§3.5, PTX ISA 9.5 §8.5–§8.10) defines:

- **Four Scopes (§8.5, Table 21):** `.cta` (same CTA; **warp is NOT a scope**, L8840), `.cluster` (same cluster, PTX 7.8 / `sm_90+`), `.gpu` (same device across grids), and `.sys` (all devices + host CPU, subject to host atomicity limits in §8.1.1).
- **Morally Strong Operations (§8.7; `ptx.als` L113–L124):** Operations $A, B$ are **morally strong relative to each other** iff: (1) they are in `po`, **or** both are strong (`.relaxed`/`.acquire`/`.release`/`.acq_rel`/fence) and each specifies a scope containing the other's thread (`strong_r = symmetric[scope.*subscope.start.*po]`); (2) both use the **same proxy**; and (3) if both are memory accesses, they **overlap completely**.
- **Six Top-Level Axioms (§8.10; ASPLOS '19 Fig. 7; `ptx.als` L71–L79):**
  1. **Coherence:** $[W]; \text{cause}; [W] \subseteq \text{co}$ ($\text{co}$ is a *partial* order, giving well-defined semantics to uniform-size data races while mixed-size data races fall outside the axioms, §8.7.2).
  2. **Fence-SC:** $\text{irreflexive}(\text{sc}; \text{cause})$ ($\text{sc}$ totally orders every pair of morally strong `fence.sc` ops).
  3. **Atomicity:** $\text{empty}(((\text{morally\_strong} \cap \text{fr}); (\text{morally\_strong} \cap \text{co})) \cap \text{rmw})$ + single-copy atomicity for morally strong conflicting ops.
  4. **No-Thin-Air:** $\text{acyclic}(\text{rf} \cup \text{dep})$ (unconditional Load Buffering without dependencies is permitted, §8.10.4).
  5. **SC-per-Location:** $\text{acyclic}((\text{morally\_strong} \cap (\text{rf} \cup \text{co} \cup \text{fr})) \cup \text{po\_loc})$.
  6. **Causality:** $\text{irreflexive}((\text{rf} \cup \text{fr}); \text{cause})$.
- **Acquire Exclusion Pitfall (§8.11.1, L9706–L9756):** Atomic reductions (`red.*`) do **NOT** form acquire patterns with `fence.acquire` (`red.sys.global.add [flag], 1; fence.acquire.gpu; ld.weak [x]` can read stale `x == 0`; `atom.*` is required).
- **Machine-Checked Scoped RC11 Lowering:** `NVlabs/ptxmemorymodel` (`src11.als`, `compile_src11_ptx.als`, `src11_ptx.v`, ~3,100 LoC Coq checking in ~15 s) proves Scoped RC11 $\to$ PTX compilation sound for all program sizes, overcoming Alloy's 6.4-hour bound-5 Coherence blowup with scopes (ASPLOS '19 §6.1–§6.2).

#### 3.2 Scope Non-Transitivity & Exact Cross-Model Divergence (PTX vs. Vulkan vs. HRF-Direct)

Direct comparison of PTX ISA 9.5 (§8.9.4–§8.9.5), `ptx.als` (L92–L100), Lustig et al. (§3.3–§3.4.4), and Khronos Vulkan (`appendices/memorymodel.adoc` L287–L294, L680–L729, L865–L891, L1056–L1068) distinguishes four synchronization patterns:

1. **Direct Mismatched Scope Pair (`A(CTA 0): rel.cta` $\to$ `C(CTA 1): acq.gpu`) — Fails Everywhere:** Symmetric moral strength (`strong_r` / Vulkan `mutually-ordered`) fails because `.cta` excludes $C$. No `sw` edge forms; stale reads and data races are allowed (and `atom.cta` vs. `atom.gpu` across CTAs loses RMW atomicity, PTX §8.10.3 Litmus Test 2).
2. **Broken Intermediate Hop (`A(0) -.cta-> B(0) -.cta-> C(1)(.gpu)`) — Fails Everywhere:** The second hop fails moral strength, severing causality $A \to C$.
3. **Scope-Inclusive Mixed Chain $A(\text{CTA }0) \xrightarrow{\text{rel.cta}/\text{acq.cta}} B(\text{CTA }0) \xrightarrow{\text{rel.gpu}/\text{acq.gpu}} C(\text{CTA }1)$ — Exact Cross-Model Divergence:**
   - **HRF-direct** (Lustig et al. §3.3, L433): Requires *identical* scopes across synchronizing chains; `.cta` + `.gpu` does **not** compose transitively.
   - **Khronos Vulkan Memory Model (`memorymodel.adoc` L715–L729, L865–L891, L1056–L1068):** Happens-before is explicitly **not transitive** across `po` and `inter-thread-happens-before<SC>` (L724) and is **insufficient for visibility**. Non-atomic visibility requires **Availability (`AV`)** and **Visibility (`VIS`)** operations across domains (`Workgroup` vs. `Shader`/`Device`). When `vulkanMemoryModelAvailabilityVisibilityChains == VK_FALSE` (base profile), `AV` and `VIS` chains are capped at **length 1** (L1065–L1068): $A$'s Workgroup-domain `AV` cannot chain through $B$'s Shader-domain `AV`, so $(W_x, R_x)$ is **NOT location-ordered** (a **data race**). Enabling `vulkanMemoryModelAvailabilityVisibilityChains == VK_TRUE` allows an availability chain (`AVC`) to compose Workgroup $\to$ Shader and restore visibility.
   - **NVIDIA PTX (`PTX ISA 9.5 §8.9.5`, `ptx.als` L95–L97):** Because each hop is morally strong and `cause_base = (po?; sw; po?)+` is **transitive (A-cumulative, L9227)**, PTX **forbids** $r_C(x) = 0$ on the generic proxy (hardware $B$'s `.gpu` release flushes the shared CTA-0 L1 cache to L2).
4. **Scoped `fence.sc` Non-Totality:** `sc` totally orders only pairwise morally strong `fence.sc` pairs (ASPLOS '19 L552); Store Buffering with `fence.sc.cta` (CTA 0) and `fence.sc.gpu` (CTA 1) legally yields `(0, 0)`.

**WGSL Memory Model (`wgsl/index.bs` L12315–L12406):** WGSL maps onto the Vulkan Memory Model; each `@group/@binding` resource and `workgroup`/`private`/`function` variable is a distinct reference. Writing one vector component (e.g., `v.y`) **may read and write all components of that vector** (L12362–L12369), causing data races if distinct threads concurrently mutate different fields of a shared `vec3`/`vec4`.

#### 3.3 Memory Proxies and Non-Cumulative Cross-Proxy Rules (PTX ISA 9.5 §8.6, §8.9.5, §9.7.15.4)

PTX ISA 9.5 §8.6 distinguishes six memory proxies: `generic` (`ld`/`st`/`atom`/`cp.async`), `async` (`cp.async.bulk*`, `cp.reduce.async.bulk*`, `wgmma`), `tensormap`, `fabric`, `readonly` (`ld.proxy::readonly`), and `alias` (distinct virtual addresses aliasing one physical location). A base-causality path $X \to_{\text{base}} Y$ enters **causality order** only when **proxy-preserved** (§8.9.5, L9198–L9212): same generic proxy, same proxy within the same CTA, or an explicit cross-proxy fence along the path. Key normative hazards:
- **Generic SMEM write $\to$ TMA store:** Requires explicit **`fence.proxy.async.shared::cta`** even within one thread; conversely, observing `cp{.reduce}.async.bulk` completion via `mbarrier` or async-group wait provides an **implicit generic-async fence** (§9.7.10.28.2, L25722–L25725).
- **Tensormap proxy acquisition (§8.9.5, L9161–L9164):** CUDA kernel-start synchronization does **not** acquire `tensormap-proxy` from `generic-proxy`; device-modified tensor maps require explicit `fence.proxy.tensormap::generic.acquire` (fixed 128-byte size, §9.7.15.4 L33059–L33063).
- **Non-cumulative async primitives:** `cp.async.bulk`'s implicit `complete-tx` orders *only* that instruction's accesses and **not** prior thread instructions (§8.9.1.1, L9075–L9079); `fence.proxy.async::generic.release.sync_restrict::shared::cluster::read.cluster` is explicitly **non-cumulative** (§9.7.15.4 Caution, L33053–L33057).

#### 3.4 Probe-Verified Scoped Memory & Proxy Litmus Matrix

Verified by `support/verify_gpu_scoped_memory_and_mbarrier.py` (Part 1):

| Litmus Test | Configuration | PTX ISA 9.5 | Vulkan (`Chains=FALSE`) | Vulkan (`Chains=TRUE`) | HRF-Direct |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. `MP-Direct-Mismatch`** | $A(0)$ `rel.cta` $\to$ $C(1)$ `acq.gpu` | Stale allowed (Race) | Race | Race | Stale allowed |
| **2. `MP-Chain-Broken-Hop`** | $A(0) \xrightarrow{\text{.cta}} B(0) \xrightarrow{\text{.cta}} C(1)(\text{.gpu})$ | Stale allowed (Race) | Race | Race | Stale allowed |
| **3. `MP-Chain-CTA-then-GPU`** | $A(0) \xrightarrow{\text{.cta}} B(0) \xrightarrow{\text{.gpu}} C(1)$ | **Forbidden** (Cumulative) | **Race** (Len-1 `AV` cap) | **Location-ordered** (`AVC`) | **Stale allowed** |
| **4. `MP-Sound-GPU`** | $A(0)$ `rel.gpu` $\to$ $C(1)$ `acq.gpu` | Forbidden | Location-ordered | Location-ordered | Forbidden |
| **5. `SB-FenceSC`** | `.cta`/`.gpu` vs. `.gpu`/`.gpu` | Mismatch allows `(0,0)`; `.gpu`/`.gpu` forbids | N/A | N/A | Same as PTX |
| **6. `TMA-Cross-Proxy`** | Generic `st.shared` $\to$ Async TMA read | Stale allowed w/o fence; **Forbidden** w/ `fence.proxy.async.shared::cta` | N/A | N/A | N/A |

---

### 4. Hopper (SM90) & Blackwell (SM100) Asynchronous Engines, `mbarrier` Phase Parity, `TMEM`, and Warp Specialization

Basis: normative + source + execution

#### 4.1 Tensor Memory Accelerator (`TMA`, `sm_90+`)

TMA offloads 1D–5D strided tile copies between `.global` and `.shared::{cta,cluster}` (plus `.multicast::cluster` and `im2col`) to a hardware DMA engine parameterized by a 128-byte `CUtensorMap` descriptor (`NVIDIA/cutlass` `include/cute/arch/copy_sm90_tma.hpp` L61–L671; PTX ISA 9.5 §9.7.10.28.5.3). One `elect.sync` leader thread issues:
```ptx
cp.async.bulk.tensor.2d.shared::cta.global.mbarrier::complete_tx::bytes
    [smem_dst], [tensor_map, {c0, c1}], [mbar];
```
Hardware performs bounds zero-fill and SMEM XOR-swizzling without register traffic; completion signals via `mbarrier::complete_tx::bytes` (loads) or `cp.async.bulk.commit_group`/`wait_group` (stores).

#### 4.2 64-bit SMEM `mbarrier` Objects and Circular-Buffer Phase Parity

An `mbarrier` is an opaque **`.b64` (8-byte), 8-byte-aligned object in `.shared`** supporting `.layout::v0` and `.layout::v1` (PTX ISA 9.5 §9.7.15.16.1–§9.7.15.16.19; `cutlass/arch/barrier.h` L405–L1067). Remote CTAs may arrive on `.shared::cluster` mbarriers, but **`test_wait`/`try_wait` are restricted strictly to `.shared::cta`** (L35007–L35010).

**State Machine (`.layout::v0`, tuple `(phase ∈ {0,1}, expected_arr, pending_arr, tx_count)`):**
1. **`mbarrier.init.shared::cta.b64 [addr], count`:** Sets `phase = 0`, `expected_arr = pending_arr = count`, `tx_count = 0`. Non-mbarrier accesses to initialized barriers or operations on uninitialized barriers are **UB** (L35053–L35056).
2. **`mbarrier.arrive.expect_tx` & TMA `complete_tx`:** `arrive.expect_tx` adds `tx_bytes` to `tx_count` and decrements `pending_arr`; TMA subtracts completed bytes from `tx_count`.
3. **Atomic Phase Completion (§9.7.15.16.8, L35332–L35368):** When `pending_arr == 0 && tx_count == 0`, hardware atomically flips `phase := phase ^ 1` and resets `pending_arr := expected_arr`.
4. **`mbarrier.try_wait.parity{.acquire.cta}` (§9.7.15.16.19, L36300–L36385):** Valid **only** for the current incomplete phase (returns `False`, may suspend up to `timeHint` ns) or the immediately preceding completed phase (returns `True`, forming an acquire pattern when `.acquire` is set). Phases $\ge 2$ behind alias the current parity bit modulo 2.

**Canonical $N$-Stage Circular Protocol:**
With `full[0..N-1]` and `empty[0..N-1]` initialized to `phase = 0, expected_arr = 1`:
- **Producer** starts at `(p_stage = 0, p_phase = 1)` (initialized to **`1`** so the first $N$ waits on `empty[s]` at phase `0 != 1` pass immediately): `try_wait.parity(empty[p_stage], p_phase)` $\to$ elected-lane `arrive.expect_tx(full[p_stage], tile_bytes)` + TMA $\to$ `p_stage = (p_stage + 1) % N`, flipping `p_phase ^= 1` on wrap.
- **Consumer** starts at `(c_stage = 0, c_phase = 0)`: `try_wait.parity(full[c_stage], c_phase)` $\to$ consume tile $\to$ `arrive(empty[c_stage])` $\to$ `c_stage = (c_stage + 1) % N`, flipping `c_phase ^= 1` on wrap.

**Exhaustive BFS Model-Checker Results (`support/verify_gpu_scoped_memory_and_mbarrier.py`, Part 2):**

| Scenario | States | Outcome | Minimal Counterexample Witness |
| :--- | :---: | :--- | :--- |
| **Sound 2-stage** ($N=2, K=5$) | 62 | **SAFE** | 0 deadlocks, 0 races across all interleavings. |
| **Sound 3-stage** ($N=3, K=6$) | 148 | **SAFE** | 0 deadlocks, 0 races across all interleavings. |
| **Bug 1: `p_phase = 0`** | 1 | **DEADLOCK** | Immediate 0-step hang waiting on `empty[0]` phase 0. |
| **Bug 2a: No consumer flip** | 29 | **STALE / IN-FLIGHT READ RACE** | On wrap (tile 2), `full[0]` is at phase 1; stale `par=0` unblocks immediately and reads `gen=0` (11-step trace). |
| **Bug 2b: No producer flip** | 13 | **DMA OVERWRITE RACE** | Producer wraps to `slot 0` still polling `par=1` against `empty[0]` phase 0, overwriting in-flight tile 0 (6-step trace). |
| **Bug 3: 32-lane arrive** | 2 | **ARRIVAL UNDERFLOW UB** | All 32 lanes arrive on `expected_arr = 1`, underflowing `pending_arr` (2-step trace). |
| **Bug 4a: `expect_tx` +64 B** | 10 | **PERMANENT HANG** | `tx_count` sticks at `64 > 0` after 128 B TMA completes; `full[0]` never flips (6-step trace). |
| **Bug 4b: `expect_tx` -64 B** | 3 | **TX UNDERFLOW UB** | `complete_tx(128 B)` underflows `tx_count = 64 B` (3-step trace). |

#### 4.3 Blackwell (`sm_100a`/`sm_100f`) `TMEM`, Single-Thread `tcgen05.mma`, and `setmaxnreg`

1. **2D Tensor Memory (`TMEM`, PTX ISA 9.5 §9.7.18.1, L47227–L47281):**
   - Geometry: **128 lanes × 512 columns × 32-bit = 256 KiB/CTA** (`sm_100a`/`sm_100f`); 32-bit address packs `lane` in `[31:16]` and `col` in `[15:0]`.
   - Allocation (§9.7.18.1.2, §9.7.18.7.1; `tmem_allocator_sm100.hpp` L82–L227): Single warp invokes `tcgen05.alloc{.exclusive}.cta_group::{1,2}.sync.aligned.shared::cta.b32 [dst], num_cols` in **32-column quanta** with `num_cols` a **power of 2** (allocating all 128 lanes). Explicit `tcgen05.dealloc` before kernel exit is mandatory; `tcgen05.relinquish_alloc_permit` yields allocation rights.
   - **Hard Lane-to-Warp Partitioning (§9.7.18.8.1, L51420–L51459):** All 4 warps in a warpgroup access all 512 columns, but `tcgen05.ld`/`tcgen05.st` restrict lanes strictly by warp ID: **Warp 0 $\to$ lanes `0–31`, Warp 1 $\to$ `32–63`, Warp 2 $\to$ `64–95`, Warp 3 $\to$ `96–127`**.
2. **Single-Thread Async `tcgen05.mma` (§9.7.18.6, §9.7.18.10.10.1; `mma_sm100_umma.hpp`):**
   - Replaces Hopper's 4-warp-collective `wgmma` with a **single-thread-issued** async MMA spanning 1 or 2 peer CTAs (`.cta_group::{1,2}`), including sparse (`.sp`) and block-scaled microscaling formats (`.kind::mxf8f6f4`, `.kind::mxf4`, `.kind::mxf4nvf4`, L54290–L54302).
   - Same-thread `tcgen05.mma -> tcgen05.commit` (mbarrier completion) and `tcgen05.{ld,st} -> tcgen05.wait::{ld,st}` pairs with matching `.cta_group::N` are implicitly pipelined; **different warps are always non-pipelined** (L50847) and require `tcgen05.fence::{before,after}_thread_sync` bracketing standard inter-thread sync (§9.7.18.6.3–§9.7.18.6.4).
3. **Warp Specialization & `setmaxnreg` (§9.7.21.5, L57134–L57245; `reg_reconfig.h` L85, L93):**
   ```ptx
   setmaxnreg.dec.sync.aligned.u32 40;   // Producer warpgroup returns registers to CTA pool
   setmaxnreg.inc.sync.aligned.u32 232;  // Consumer warpgroup draws registers from CTA pool
   ```
   Normative constraints (`sm_90a`, `sm_100{a,f}`, `sm_110{a,f}`, `sm_120{a,f}`): `imm ∈ [24, 256]` inclusive and a **multiple of 8**; `.dec` requires `current >= imm` and `.inc` requires `current <= imm` (else UB); **all 4 warps in a warpgroup** must execute `.aligned` identically and sync before subsequent `setmaxnreg` (else UB); **`.inc` blocks** until the per-CTA pool has free registers (deadlocking if consumer demand exceeds released supply); new tail registers hold **undefined values**.

---

### 5. Execution-Hierarchy Ownership and Safe GPU Borrowing (`Descend`, PLDI '24)

Basis: documentation + source + derived

**Descend** (Köpcke, Gorlatch & Steuwer, PLDI '24, `arXiv:2305.03448`; inspected at `descend-lang/descend@e98d4c086f369496b79294b333086020ab08e0c6`) lifts Rust ownership to GPUs via three static mechanisms:

1. **Address-Space References & Execution-Hierarchy Paths (`src/ast/mod.rs` L498–L501, L1032–L1044, L1446–L1497):**
   References `&r w m d` bind lifetime `r`, `Ownership::{Shrd, Uniq}`, physical space `Memory::{CpuMem, GpuGlobal, GpuShared, GpuLocal, Ident}`, and data type `d`. Execution paths start at `BaseExec::{CpuThread, GpuGrid(Dim, Dim)}` and refine through `ExecPathElem::{ForAll(DimCompo), TakeRange(TakeRange), ToWarps, ToThreads(DimCompo)}`.
   *Preprint vs. Source:* `arXiv:2305.03448v1` (May 2023) covers `Grid -> Block -> Thread` without warps; the pinned repository adds `ToWarps`, `ExecTyKind::GpuWarp` (`src/ty_check/exec.rs` L46, L92), warp intrinsics (`shfl_sync`, `shfl_up`, `ballot_sync`, `get_warp_id`, `get_lane_id`), and atomics (`atomic_{store,load,fetch_add,fetch_or,min}`, `src/ty_check/pre_decl.rs` L16–L32).
2. **Parallel Data-Race Freedom via `narrowing_check` & Disjoint Views (`src/ty_check/borrow_check.rs` L218–L285, L386):**
   For any `Ownership::Uniq` access, `narrowable(from, to)` checks `exec_is_prefix_of` and **`no_forall_in_diff`**: crossing any `ForAll` parallel distribution to mutate an unpartitioned outer `uniq` binding is rejected. Mutation across `ForAll` requires `PlaceExprKind::Select` over disjoint **array-view combinators** (`pre_decl.rs` L34–L42: `to_view`, `grp`, `join`, `transp`, `take_left`, `take_right`, `select_range`, `rev`, `map`), which erase into zero-overhead CUDA indexing (`README.md` L48–L68). `access_conflict_check` rejects overlapping active loans within an unsynchronized phase.
3. **Static Barrier-Divergence Rejection (`src/ty_check/mod.rs` L288–L338):**
   `syncable_exec_ty` permits `sync` **only** on `ExecTyKind::GpuBlock(_)` and `ExecTyKind::GpuWarp` (rejecting `GpuGrid`, groups, and single threads). `syncable_under_exec` walks `&ctx.exec.exec.path[synced.exec.path.len()..]` and **rejects any `ExecPathElem::TakeRange(_)`** (`"tyring [sic] to synchronize on split execution resource"`), statically ruling out diverged barriers; valid syncs call `ctx.access_ctx.clear_sync_for` to release prior phase loans.
4. **Escape Hatch & Hopper/Blackwell Gaps:** `ExprKind::Unsafe` (`mod.rs` L259–L264) and raw pointers (`to_raw_ptr`, `offset_raw_ptr`) handle irregular patterns, but `descend-lang/descend@e98d4c086f369496b79294b333086020ab08e0c6` lacks `GpuCluster`/DSMEM, scoped/proxy-qualified atomics, linear TMA/`mbarrier` phase-parity typestates, TMEM lane ownership, and `setmaxnreg` budgets.

---

### 6. Synthesis: Host-Device FFI and Verification Architecture Implications

Basis: derived

| Boundary Layer | Why Scalar CPU / Rust Defaults Break | Minimal Required GPU Semantic Contract |
| :--- | :--- | :--- |
| **Control Flow & IR** | Scalar passes move collectives across active masks; Volta+ ITS drops warp lockstep. | WGSL uniformity or LLVM `convergencectrl` tokens + `SPV_KHR_maximal_reconvergence` merge points. |
| **Scoped Atomics & Proxies** | Flat `Ordering` omits scope/proxy; `.cta` $\not\to$ `.gpu` directly; base Vulkan breaks mixed-scope chains. | Parameterize ops by `(Ordering, Scope, Proxy)` with symmetric moral-strength proofs, `fence.proxy.*`, and Vulkan `AV`/`VIS` domain tracking. |
| **Async DMA & `mbarrier`** | Raw phase bits, byte arithmetic, and `setmaxnreg` pools silently hang or race. | Linear ring-buffer typestate (`AsyncRing<N, TileT>`) binding `elect.sync`, `expect_tx(sizeof(TileT))`, coupled `(stage, phase)` flips, and `fence.proxy.async`. |
| **Parallel Aliasing & FFI** | `&mut [T]` cannot split across `Grid`/`Block`/`Warp` or asynchronous host-device queues. | Execution-hierarchy ownership (`Descend` `Memory` + `narrowing_check` + views), warp-partitioned TMEM slices, and queue-completion lifetimes. |

## Boundaries

- **not examined:**
  - Vendor-specific AMD RDNA/CDNA (`s_waitcnt`, AMDGPU memory model) and Apple Metal ISA manuals were not directly inspected (cross-vendor coverage rests on LLVM, Khronos Vulkan/SPIR-V, and W3C WGSL).
  - Physical GPU silicon litmus testing (`nvcc`/`ptxas` compilation and execution on Volta/Hopper/Blackwell hardware) and `nvcc` compilation/benchmarking of Descend `.cu` outputs were not run.
  - PTX ISA 9.5 `fabric` proxy (`multimem`, multi-node NVLink) and `mbarrier` `.layout::v1` conditional-phase payload reporting were noted from PTX ISA 9.5 but not modeled in the Python probe.
- **unknown:**
  - The exact fraction of production Hopper/Blackwell CUTLASS kernels expressible in safe Descend without `unsafe` (unmeasured in both the PLDI '24 paper and `descend-lang/descend`).
  - General forward-progress guarantees for inter-CTA lock-free spinlocks under oversubscribed grids: PTX ISA 9.5 §3.2 documents intra-warp ITS yielding, but neither PTX nor Vulkan guarantees preemptive fairness across non-resident CTAs exceeding SM occupancy.
- **known not to apply:**
  - PTX Memory Consistency axioms (§8.1, §8.7.2) do **not** apply to pre-Volta GPUs (`sm_6x` and earlier), texture (`ld.global.nc`)/surface accesses, or programs with **mixed-size data races**.
  - Warp is **not** a PTX memory scope (§8.5); `red.*` instructions do **not** form PTX acquire patterns (§8.11.1); pre-Volta warp-synchronicity does **not** hold on `sm_70+` (§3.2).
  - Faial's CAV '21 Theorems 1–3 do **not** apply to inter-CTA communication, scoped weak-memory atomics, or asynchronous `mbarrier` phase-parity pipelines.
- **unsupported:**
  - `mbarrier.{test,try}_wait` on `.shared::cluster` addresses is unsupported (PTX ISA 9.5 §9.7.15.16, L35007–L35010).
  - Grid/cluster `sync` is unsupported in `descend-lang/descend@e98d4c086f369496b79294b333086020ab08e0c6` (`syncable_exec_ty`, `src/ty_check/mod.rs` L326–L338).
  - Cross-warp `tcgen05.{ld,st}` TMEM lane accesses are unsupported by Blackwell datapath wiring (PTX ISA 9.5 §9.7.18.8.1).
- **Stronger conclusions not established:**
  - The finite-state BFS probe proves safety for the modeled 2-stage ($K=5$) and 3-stage ($K=6$) single-producer/single-consumer rings, not an arbitrary-$N$ parameterized proof or dual-CTA `.cta_group::2` proof.
  - PTX's cumulative `.cta` $\to$ `.gpu` `cause_base` transitivity does **not** generalize to portable Vulkan/WebGPU shaders unless `vulkanMemoryModelAvailabilityVisibilityChains == VK_TRUE` is checked and enabled.

## Evidence

All primary sources were fetched and verified on `2026-11-19`:

1. **NVIDIA PTX ISA Version 9.5** (`https://docs.nvidia.com/cuda/parallel-thread-execution/index.html`): §3.2 ITS (L2050–L2073); §8.1–§8.11.1 Memory Consistency Model, Scopes, Proxies, Morally Strong, Causality, Axioms, `red` exclusion (L8548–L9756); §9.7.10.28.2 / §9.7.10.28.5.3 TMA & Async Proxy (L25713–L25726, L27325+); §9.7.15.2 `bar.warp.sync` (L32815+); §9.7.15.4 `fence.proxy` & non-cumulative caution (L32959–L33185); §9.7.15.15 `elect.sync` (L34954–L34996); §9.7.15.16 `mbarrier` (L34999–L36385); §9.7.18.1–§9.7.18.10 `TMEM`, `tcgen05` memory model, `alloc`/`dealloc`, lane access restrictions, `tcgen05.mma` (L47227–L54395); §9.7.21.5 `setmaxnreg` (L57134–L57245).
2. **Lustig, Sahasrabuddhe & Giroux (ASPLOS '19)**, DOI `10.1145/3297858.3304043`, and **`NVlabs/ptxmemorymodel`** (`f0dc6b7f85f34fc19fb76e7495864656276fa002`): `PTXMemoryModelASPLOS2019.pdf` (§3.3–§3.5, §6.1–§6.2), `ptx.als` (L71–L124), `src11.als` (L140–L188), `compile_src11_ptx.als` (L62–L173), `src11_ptx.v` (3,580 lines).
3. **`NVIDIA/cutlass`** (`88d690dec7c58a291e95ae44c9e68d800602fed5`): `include/cutlass/arch/barrier.h` (L405–L1067), `include/cute/arch/copy_sm90_tma.hpp` (L61–L671), `include/cute/arch/cluster_sm90.hpp` (L51–L219), `include/cute/arch/tmem_allocator_sm100.hpp` (L82–L227), `include/cute/arch/mma_sm100_umma.hpp` (L71–L660), `include/cutlass/arch/reg_reconfig.h` (L85, L93).
4. **Khronos Vulkan Memory Model** (`KhronosGroup/Vulkan-Docs@f7de774cace1509af0f10b8d859c973b5354ff62`, `appendices/memorymodel.adoc`): L287–L306 (`mutually-ordered`), L486–L620 (`Synchronizes-With`), L681–L729 (non-transitive `Happens-Before`), L733–L892 (`Availability`/`Visibility` chains), L1033–L1185 (`Location-Ordered`, `vulkanMemoryModelAvailabilityVisibilityChains` length-1 cap, `Data Race`, `Acyclicity`).
5. **Khronos SPIR-V `SPV_KHR_maximal_reconvergence`** (`KhronosGroup/SPIRV-Registry@25574da230687e0beb5d285c2746a7c0d2e17dcd`, `extensions/KHR/SPV_KHR_maximal_reconvergence.asciidoc`): L147–L309.
6. **W3C WGSL Specification** (`gpuweb/gpuweb@d178d9145ab1652ec933e71a8c30e8f6470f00a3`, `wgsl/index.bs`): L12315–L12406 (Memory Model & vector write aliasing), L12504–L13950 (Uniformity Analysis graph, tags, statement rules, composite limitations).
7. **LLVM Convergence Control** (`llvm/llvm-project@1780833aa0f119a425d7f993aaac29d03cb04da6`): `llvm/docs/ConvergentOperations.md` (L48–L90, L496–L948, L1192–L1460) and `llvm/docs/ConvergenceAndUniformity.md` (650 lines; migrated upstream from `.rst` to `.md`).
8. **Faial (CAV '21)** — Cogumbreiro et al., DOI `10.1007/978-3-030-81685-8_19` (`https://cogumbreiro.github.io/assets/faial-cav21.pdf`): Def. 1 (L946), Theorem 1 (L1110), Theorem 2 (L1198), Theorem 3 (L1288), Table 1 & evaluation (L1496–L1590).
9. **Descend (PLDI '24)** — Köpcke, Gorlatch & Steuwer, DOI `10.1145/3656411`, `arXiv:2305.03448`, and **`descend-lang/descend`** (`e98d4c086f369496b79294b333086020ab08e0c6`): `README.md` (L6–L68), `src/ast/mod.rs` (L498–L501, L1032–L1044, L1446–L1497), `src/ty_check/pre_decl.rs` (L7–L60), `src/ty_check/exec.rs` (L35–L280), `src/ty_check/borrow_check.rs` (L218–L285, L386), `src/ty_check/mod.rs` (L258–L338).
10. **Executable Probe (`support/verify_gpu_scoped_memory_and_mbarrier.py`):** Executed via `python3 -B support/verify_gpu_scoped_memory_and_mbarrier.py` (Python 3.10+ stdlib, ~0.29 s, exit code `0`), confirming all 6 scoped/proxy litmus tests, all 8 `mbarrier` BFS pipeline checks, and all 6 WGSL uniformity cases.

## Revalidation

1. **Rerun the Preserved Probe:**
   ```console
   python3 -B reports/gpu-simt-execution-warp-divergence-and-scoped-memory-models/support/verify_gpu_scoped_memory_and_mbarrier.py
   ```
   A zero exit code verifies all encoded PTX/Vulkan/HRF-direct litmus assertions, $N$-stage `mbarrier` state-space invariants, and WGSL uniformity graphs.
2. **Diff Narrow Upstream Spec Regions:**
   - **PTX ISA:** Inspect `Section 13. Release Notes` past version `9.5` for changes to §8 (scopes/proxies), §9.7.15.16 (`mbarrier`), §9.7.18 (`tcgen05`/TMEM), or §9.7.21.5 (`setmaxnreg`).
   - **Vulkan / SPIR-V / WGSL / LLVM:** Diff `KhronosGroup/Vulkan-Docs` `appendices/memorymodel.adoc` against `f7de774cace1509af0f10b8d859c973b5354ff62`, `KhronosGroup/SPIRV-Registry` `SPV_KHR_maximal_reconvergence.asciidoc` against `25574da230687e0beb5d285c2746a7c0d2e17dcd`, `gpuweb/gpuweb` `wgsl/index.bs` against `d178d9145ab1652ec933e71a8c30e8f6470f00a3`, and `llvm/llvm-project` `llvm/docs/ConvergentOperations.md` against `1780833aa0f119a425d7f993aaac29d03cb04da6` (watching for stabilization of `llvm.experimental.convergence.*`).
   - **Descend & CUTLASS:** Diff `descend-lang/descend` `src/ast/mod.rs` and `src/ty_check/{mod,borrow_check,exec}.rs` against `e98d4c086f369496b79294b333086020ab08e0c6` for cluster/async/scoped-atomic additions, and `NVIDIA/cutlass` SM90/SM100 arch headers against `88d690dec7c58a291e95ae44c9e68d800602fed5`.
3. **Hardware Confirmation:** Validating silicon-specific scheduling fairness, cache-flush latency, or mixed-size race hardware behavior requires running physical GPU litmus harnesses rather than re-running the abstract model probe.
