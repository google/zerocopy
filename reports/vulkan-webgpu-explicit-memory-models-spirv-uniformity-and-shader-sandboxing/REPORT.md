# Vulkan and WebGPU Explicit Memory Models, SPIR-V Structured Control Flow, WGSL Uniformity Analysis, and Shader Sandboxing

## Summary

Modern graphics and compute pipelines separate **memory ordering** from **cache coherence** and layer untrusted browser-level shader execution over vendor GPU driver compilers (`DXC`, `Metal`/LLVM, Vulkan SPIR-V JITs) that routinely assume C++-style undefined behavior (UB) freedom. Four tightly coupled technical contracts govern soundness, progress, and memory isolation across this stack:

1. **Vulkan's Two-Half Availability-Visibility Memory Model (`KhronosGroup/Vulkan-MemoryModel`, `Vulkan-Docs`):** Unlike C++11/C11—where `happens-before` (`hb`) alone suffices for inter-thread visibility—GPU hierarchies with non-coherent per-core L1 caches split non-atomic write propagation into **availability** (flushing a write out of a writer's cache into a hierarchical memory domain: `subgroup`, `workgroup`, `queue family`, `shader`, `device`, or `host`) and **visibility** (invalidating a reader's cache from that domain). Establishing `location-ordered` (`locord`) requires an asymmetric two-half chain: Write-after-Write (`WaW`) requires only availability plus `hb`, whereas Read-after-Write (`RaW`) requires availability, `hb`, *and* visibility, and non-atomic shader accesses default to `Private` (excluded from shader-domain inter-thread ordering unless tagged `NonPrivatePointer`/`NonPrivateTexel`). Multi-hop availability/visibility chains across nested domains require the `vulkanMemoryModelAvailabilityVisibilityChains` device feature; without it, chains collapse to single-hop operations. Exclusive-mode resources crossing queue families additionally require paired API-level release/acquire **Queue Family Ownership Transfers** (`QFOT`).
2. **SPIR-V Structured Control Flow and Maximal Reconvergence (`KhronosGroup/SPIRV-Tools`):** Shader-capability SPIR-V forbids irreducible CFGs and enforces strict nesting of selection (`OpSelectionMerge`), loop (`OpLoopMerge`), and continue constructs verified via structural dominance, structural post-dominance on continue constructs, single back-edge latches per loop header, and structured-exit invariants (`source/val/validate_cfg.cpp`). Under `SPV_KHR_maximal_reconvergence` (`ExecutionMode MaximallyReconvergesKHR`), `SPIRV-Tools` additionally bans identical true/false `OpBranchConditional` targets, forbids ray-tracing invocation-repack instructions, and restricts multi-predecessor basic blocks exclusively to loop headers, merge/continue targets, and switch targets.
3. **W3C WGSL Static Uniformity Analysis (`gpuweb/gpuweb`, `google/dawn` Tint, `gfx-rs/wgpu` Naga):** To prevent divergent barrier hangs (e.g., `workgroupBarrier()` reached by only a subset of invocations) without runtime barrier instrumentation, WGSL defines a bottom-up interprocedural implication-graph analysis (`wgsl/index.bs` §13.3). A shader triggers a uniformity failure iff a directed path exists from `RequiredToBeUniform.<S>` to `MayBeNonUniform`. Divergence inside an `if`/`switch`/`loop` with statement behavior `{Next}` conservatively reconverges at statement exit, whereas early `return` (`{Next, Return}`) propagates non-uniformity past the construct. Critical implementation differential: `google/dawn`'s Tint (`src/tint/lang/wgsl/resolver/uniformity.cc`) implements the normative implication-graph algorithm, whereas `gfx-rs/wgpu`'s Naga (`naga/src/valid/analyzer.rs`) currently uses a simpler statement-level pass that disables fragment-stage derivative uniformity checks (`DISABLE_UNIFORMITY_REQ_FOR_FRAGMENT_STAGE = true`) and skips uniformity checking on `Statement::WorkGroupUniformLoad`.
4. **Untrusted Shader Sandboxing Over Vendor Driver JITs (`gfx-rs/wgpu` Naga, `google/dawn` Tint, `SafeRace`):** Browser WebGPU runtimes cannot rely on native driver UB assumptions. Naga and Tint lower WGSL's dynamic-error out-of-bounds semantics into explicit `BoundsCheckPolicy` strategies (`Restrict` clamping/unsigned-min vs. `ReadZeroSkipWrite` vs. `Unchecked` when hardware `robustBufferAccess2` guarantees safety), zero-initialize workgroup memory (`Native` via `VK_KHR_zero_initialize_workgroup_memory` / Vulkan 1.3 or `Polyfill` for cross-origin leak prevention), and inject **simulated 64-bit `vec2<u32>` decrementing loop-bounding fuel counters** (`force_loop_bounding = true`, counting down from `u32::MAX` to defeat Intel driver hangs) specifically to block LLVM/Metal/DXC forward-progress UB optimizations from **proving infinite-loop guards unreachable and deleting injected array bounds checks**. Data races on index-carrying variables remain an active boundary (`SafeRace`, OOPSLA 2025) because downstream driver optimizers can reload racy indices across bounds checks (TOCTOU) unless indices are frozen into SSA values before clamping.

## Applicability

These findings govern:

- **Formal Vulkan/SPIR-V memory consistency:** Applies to Vulkan 1.2+ / `VK_KHR_vulkan_memory_model` and SPIR-V modules declaring `Capability VulkanMemoryModel` and `MemoryModel Logical Vulkan` (or `PhysicalStorageBuffer64 Vulkan`), as formalized in `KhronosGroup/Vulkan-MemoryModel` (`894ae9027ce8f66e40d5f79c3eb727e77955aef4`, `alloy/spirv.als`) and specified in `KhronosGroup/Vulkan-Docs` (`f7de774cace1509af0f10b8d859c973b5354ff62`, `appendices/memorymodel.adoc` and `chapters/synchronization.adoc`). Legacy `MemoryModel GLSL450` (without `VulkanMemoryModel`) lacks `QueueFamily` scope, explicit `MakePointerAvailable`/`MakePointerVisible` operands, and formal non-private semantics; findings on availability/visibility chains do **not** extend directly to pre-Vulkan-Memory-Model `GLSL450` shaders.
- **SPIR-V validation and structured CFGs:** Applies to shader-capability SPIR-V modules (`Capability Shader`) validated by `KhronosGroup/SPIRV-Tools` (`326b40880bd4a4e60b1b6b9cf31560b2f040de81`, `source/val/validate_cfg.cpp` and `source/val/validate_memory_semantics.cpp`). OpenCL `Kernel`-capability SPIR-V modules do not mandate `OpSelectionMerge`/`OpLoopMerge` structured CFGs and fall outside the structured control-flow findings.
- **WebGPU / WGSL memory semantics, uniformity, and compiler sandboxing:** Applies to W3C WGSL (`gpuweb/gpuweb` @ `d178d9145ab1652ec933e71a8c30e8f6470f00a3`, `wgsl/index.bs`) and two production translators interpreting it:
  - `gfx-rs/wgpu` (`9450c94c1ff2c734f7c73db604ad87501eee1803`, covering `naga` IR validation/lowering and `wgpu-hal` Vulkan/Metal/DX12 backend policy wiring).
  - `google/dawn` (`05a3f2091af9815b4412d188fe1ba2b29d6683c6`, covering `tint` WGSL uniformity analysis and core IR robustness transforms).
- **Relationship among subjects:** The WGSL specification explicitly defines its memory model by reduction to the Vulkan Memory Model (`wgsl/index.bs:12317–12474`), maps synchronization and memory operations onto SPIR-V memory semantics validated by `SPIRV-Tools`, and relies on `Naga` and `Tint` to enforce both static uniformity and runtime memory/termination containment when emitting SPIR-V, MSL, HLSL, and GLSL for untrusted web shaders. The five peer-reviewed papers supply the comparative methodology (`memalloy`), empirical GPU conformance testing frameworks (`Kirkham et al.`, `MC Mutants`), formal soundness analysis of WGSL uniformity (`Lee-Jones et al.`), and data-race-induced bounds-check bypass analysis (`SafeRace`).

## Findings

### 1. Formal Vulkan Availability-Visibility Memory Model

**Basis:** normative (`Vulkan-Docs/appendices/memorymodel.adoc`) + source (`Vulkan-MemoryModel/alloy/spirv.als`, `alloy/tests/*.test`) + execution (Probe 1A relational checker).

#### 1.1 Hierarchical Memory Domains, Scopes, and Non-Private Accesses

The Vulkan Memory Model (`KhronosGroup/Vulkan-MemoryModel/alloy/spirv.als` and `KhronosGroup/Vulkan-Docs/appendices/memorymodel.adoc`) models GPU hardware with non-coherent, multi-level caches where synchronization order (`happens-before`) does **not** automatically flush or invalidate caches. Every synchronization or memory operation carries an explicit **Scope** whose dual is a nested **Memory Domain** (`vulkan_memorymodel.adoc:744–784, 952–967`):

| Scope (SPIR-V / Vulkan) | Dual Memory Domain | Agents Covered | Accessible From Shader Instructions? |
| :--- | :--- | :--- | :--- |
| `Invocation` | *(none)* | Single shader invocation only | Yes (no AV/VIS ops performed) |
| `Subgroup` | Subgroup instance domain | Invocations in the same subgroup (warp/wavefront) | Yes (`avsg`/`vissg`; typically zero-cost in HW) |
| `Workgroup` | Workgroup instance domain | Invocations in the same workgroup | Yes (`avwg`/`viswg`) |
| `ShaderCallKHR` / `FragmentInterlock` | Extension-specific instance domain | Ray-tracing call-related / overlapping fragments | Yes (extension-gated, nested $\le$ queue family) |
| `QueueFamily` | Queue family instance domain | Shader invocations submitted to the same queue family | Yes (`avqf`/`visqf`) |
| `Device` | **Shader domain** *(not device domain!)* | All shader invocations on a logical device | Yes (`avsh`/`vissh`) |
| *(API-level only)* | **Device domain** | All device agents (shaders, transfer engines, fixed-function) | **No** — only via Vulkan API barriers / `vkQueueSubmit` |
| *(API-level only)* | **Host domain** | Host CPU threads | **No** — only via `vkFlushMappedMemoryRanges` / `vkInvalidateMappedMemoryRanges` |

Two critical design traps arise directly from the Alloy specification (`alloy/spirv.als`):

1. **Private-by-default non-atomic accesses (`spirv.als:217–222, 368–381`; `vulkan_memorymodel.adoc:655–677`):** Every non-atomic load or store is `PRIV` unless explicitly annotated with SPIR-V `NonPrivatePointer` / `NonPrivateTexel` (atomics are unconditionally `A in NONPRIV`). In `spirv.als:370–379`, every shader-level inter-thread `locord` rule restricts endpoints to `W-PRIV` and `R-PRIV`. Private accesses can **only** be ordered across threads via `^ssw` (`system-synchronizes-with`, line 371) or API-level `AVDEVICE`/`VISDEVICE` (lines 380–381). Omitting `NonPrivatePointer` on a regular load/store in a shader message-passing idiom causes a formal data race even when full `AcquireRelease + MakeAvailable + MakeVisible` barriers are present (`alloy/tests/privmp.test`, confirmed by Probe 1A: `#dr = 2`).
2. **Mutual Scope Inclusion (`inscope`, `spirv.als:287–293`):** Two synchronization or atomic operations participate in `sw` or `mutordatom` only if **both** operations specify a scope large enough to encompass both agents:
   ```alloy
   inscope = (SCOPEDEV -> SCOPEDEV) +
             (sqf & ((SCOPEDEV+SCOPEQF) -> (SCOPEDEV+SCOPEQF))) +
             (swg & ((SCOPEDEV+SCOPEQF+SCOPEWG) -> (SCOPEDEV+SCOPEQF+SCOPEWG))) +
             (ssg & ((SCOPEDEV+SCOPEQF+SCOPEWG+SCOPESG) -> (SCOPEDEV+SCOPEQF+SCOPEWG+SCOPESG)))
   mutordatom = (sloc & sref & (A -> A) & inscope) - iden
   ```
   A `Device`-scoped atomic release does **not** synchronize with a `Workgroup`-scoped atomic acquire from a different workgroup, nor do two `QueueFamily`-scoped atomics in different queue families synchronize (`alloy/tests/qfmpfail.test`, confirmed by Probe 1A: `#dr = 4`). Furthermore, `mutordatom` requires **both** `sloc` (same physical memory location) **and** `sref` (same memory-model reference, e.g., same storage buffer descriptor binding or same `Workgroup` variable); aliasing the same underlying `VkDeviceMemory` through two distinct buffer descriptors breaks `mutordatom` and shader-domain `locord`, requiring device-domain API barriers instead.

#### 1.2 Two-Half Availability/Visibility Chains, Storage-Class-Templated `hb`, and `WaW`/`RaW` Asymmetry

Unlike C++11's single `happens-before` relation, Vulkan's `hb` is **not globally transitive** (`vulkan_memorymodel.adoc:722–729`, `spirv.als:333–349`):
- `ithbsemsc<SC>` is parameterized by the set of storage-class semantics bits (`UniformMemory`, `WorkgroupMemory`, `ImageMemory`, `OutputMemoryKHR`, modeled as `SC0`, `SC1`, `SC01` in `spirv.als:333–347`) and is transitive *within* a fixed storage-class mask, while `po` is transitive within a single thread. `hb = ithbsemsc0 + ithbsemsc1 + ithbsemsc01 + po` (line 349) deliberately forbids chaining `po` with `ithbsemsc` across mismatched storage classes.
- Vulkan's **Release Sequence** (`rs = (stor[REL&A]) . *((imm[asmo]) . (stor[R&W]))`, `spirv.als:304–310`) explicitly drops C++11's "subsequent same-thread atomic write" clause (which C++20 later deprecated as well), retaining only contiguous RMW chains in `asmo`.

A write $W$ by agent $A_W$ to location $L$ via reference $R_W$ starts unavailable to all domains and visible only to $(A_W, R_W, L)$. Propagating $W$ to another invocation $A_R$ requires two distinct halves (`spirv.als:356–381`, `vulkan_memorymodel.adoc:838–893`):

1. **Availability Chain (`AVC`):** Flushes $W$ from writer cache upward through monotonically broader domains (`avsg` $\to$ `avwg` $\to$ `avqf` $\to$ `avsh`), where each hop occurs within the dual scope of the prior destination domain and is ordered by `hb & scope & avvisinc`. In `spirv.als:357–359`, every multi-hop prefix is intersected with `chains`, which equals `EV -> EV` iff `VkPhysicalDeviceVulkanMemoryModelFeatures::vulkanMemoryModelAvailabilityVisibilityChains == VK_TRUE`, and degrades to `stor[EV]` (identity—disabling all chains of length $\ge 2$) when `VK_FALSE`.
2. **Visibility Chain (`VISC`):** Invalidates caches downward from monotonically narrower domains (`vissh` $\to$ `visqf` $\to$ `viswg` $\to$ `vissg`) into $(A_R, R_R, L)$, symmetrically gated by `chains` (`spirv.als:363–365`).

Crucially, `locord` (`spirv.als:368–381`) exhibits **four-way operational asymmetry**:

| Access Pair ($X \to Y$, non-private, shader-synchronized) | Required Ordering Chain in `spirv.als` | Why Cache Operation Is Needed / Omitted |
| :--- | :--- | :--- |
| **RaR / WaR** (`R -> R`, `R -> W`) | `R --hb--> {R, W}` (line 370) | No cache flush or invalidate required to order a subsequent read or overwrite after a completed read. |
| **WaW** (`W1 -> W2`) | `W1 --(rc[po]&avvisinc)--> av_D --(hb&D)--> W2` (lines 372, 374, 376, 378) | `W1` must be flushed (`AV`) before `W2` executes so stale dirty lines from `W1` cannot be written back *after* `W2` and clobber it; `W2` does **not** need `VIS`. |
| **RaW** (`W -> R`) | `W --(rc[po]&avvisinc)--> av_D --(hb&D)--> vis_D --(rc[po]&avvisinc)--> R` (lines 373, 375, 377, 379) | Both halves mandatory: writer must flush (`AV`) to shared domain $D$ and reader must invalidate (`VIS`) from $D$. |
| **Host/Device API** (`W -> R`) | `W --hb--> AVDEVICE --hb--> DOM(D_X, D_Y) --hb--> VISDEVICE --hb--> R` (lines 380–381; `adoc:903–930`) | `vkFlushMappedMemoryRanges` performs host `AV`; `vkQueueSubmit` performs `DOM(host -> device)` + device-to-all-agents `VIS`; pipeline barriers perform `AV(src -> device)` + `VIS(device -> dst)`. |

Consistency (`consistent[X]`, `spirv.als:397–403`) enforces two axioms:
1. **Causality acyclicity:** `is_acyclic[locord + rf + fr + asmo]`, where `fr = (~rf . ((W->W) & locord)) + (~rf . asmo) + (stor[RFINIT] . sloc . stor[W]) - iden`.
2. **Non-atomic non-shadowing:** `no (rf . stor[R - A]) & twoplus[stor[W] . locord]` — a non-atomic read cannot read from a write overwritten by a later `locord`-ordered write.

A **data race** (`dr`, `spirv.als:391`) is any pair of distinct accesses to overlapping locations (`sloc`) containing at least one write that is neither in `mutordatom` nor in `locord ∪ ~locord`. As proven in `spirv.als:424–427` (`AssertLocordComplete1`/`AssertLocordComplete2`), consistent executions are race-free iff all conflicting non-atomic accesses are totally ordered by `locord`.

#### 1.3 Queue Family Ownership Transfers (`QFOT`) and Domain Mismatch Hazards

**Basis:** normative (`Vulkan-Docs/chapters/synchronization.adoc:8032–8200`, `appendices/memorymodel.adoc:903–930`).

For resources created with `VK_SHARING_MODE_EXCLUSIVE`, expressing a semaphore or fence execution/memory dependency between queues of two distinct queue families ($Q_A \to Q_B$) is **insufficient**: `synchronization.adoc:8090–8093` normatively specifies that resource contents become **undefined** for reads on $Q_B$ unless an explicit two-barrier **Queue Family Ownership Transfer** occurs:
1. **Release operation on source queue family $Q_A$:** A `VkBufferMemoryBarrier` / `VkImageMemoryBarrier` with `srcQueueFamilyIndex = Q_A`, `dstQueueFamilyIndex = Q_B`. Its `dstStageMask` and `dstAccessMask` are ignored (making writes available to the device domain and releasing family-local layout/compression metadata such as delta color compression / HTILE).
2. **Execution dependency (e.g., `VkSemaphore`)** bridging submission on $Q_A$ to submission on $Q_B$.
3. **Acquire operation on destination queue family $Q_B$:** An identical barrier with `srcQueueFamilyIndex = Q_A`, `dstQueueFamilyIndex = Q_B`, whose `srcStageMask` and `srcAccessMask` are ignored and whose `dstStageMask`/`dstAccessMask` make the transferred data visible to $Q_B$.

Note the crucial distinction highlighted in `vulkan_memorymodel.adoc:1079–1083`: **`Device` scope in SPIR-V synchronizes through the *shader domain*, NOT the *device domain***. Shader-side `Device`-scoped atomics/barriers can never synchronize with non-shader fixed-function units (transfer engines, color attachment outputs, host DMA) or replace `QFOT` metadata handoffs.

#### 1.4 Empirical Conformance and Specification Testing (`memalloy`, Kirkham et al., `MC Mutants`)

**Basis:** documentation + derived (`DOI: 10.1145/3009837.3009838`, `DOI: 10.1145/3428294`, `DOI: 10.1145/3575693.3575750`).

- `KhronosGroup/Vulkan-MemoryModel/alloy/spirv.als:7–9` explicitly derives its Alloy encoding pattern from **Memalloy** (Wickerson et al., POPL 2017, `10.1145/3009837.3009838`), which uses SAT-backed bounded relational model finding to synthesize minimal discriminating litmus tests between memory models (e.g., comparing C++11, OpenCL, PTX, and Vulkan).
- Kirkham, Sorensen, Tureci, and Martonosi (OOPSLA 2020, `10.1145/3428294`) formalized empirical GPU litmus testing strategies—showing that static stress idioms often miss weak-memory reorderings unless thread-to-workgroup mappings, memory stride padding (false sharing vs. same bank), and barrier/cache-warming stress loops actively trigger hardware store buffers and non-coherent L1s.
- **MC Mutants** (Levine et al., ASPLOS 2023, `10.1145/3575693.3575750`) applied mutation testing directly to Alloy memory-model specifications (including `Vulkan-MemoryModel`), automatically synthesizing targeted litmus suites that detect subtle conformance-suite blind spots and real driver memory-model bugs on Vulkan/WebGPU GPUs.

---

### 2. SPIR-V Structured Control Flow and Memory Semantics Validation

**Basis:** source (`KhronosGroup/SPIRV-Tools` @ `326b40880bd4a4e60b1b6b9cf31560b2f040de81`, `source/val/validate_cfg.cpp`, `source/val/validate_memory_semantics.cpp`).

#### 2.1 Structured Control Flow Rules (`validate_cfg.cpp`)

GPU SIMT hardware executes groups of invocations (subgroups/warps) in lockstep with a shared program counter and active execution mask. Arbitrary irreducible CFGs prevent compilers from determining deterministic reconvergence points, causing divergent threads to permanently split or deadlock at barriers. For `Shader`-capability modules, `SPIRV-Tools` enforces structured control flow in `StructuredControlFlowChecks` (`source/val/validate_cfg.cpp:753–937`):

1. **Single-latch natural loops (`validate_cfg.cpp:761–787`):** Every CFG back-edge $(b \to h)$ must target a loop header $h$ (`kBlockTypeLoop`, containing `OpLoopMerge` immediately before its terminator), and every structurally reachable loop header must be targeted by **exact cardinality 1** back-edge block (`num_latch_blocks != 1` returns `SPV_ERROR_INVALID_CFG`). Multi-latch loops or irreducible two-entry cycles are rejected outright.
2. **Strict structural dominance of merge blocks (`validate_cfg.cpp:807–821`):** Every construct's header $h$ must structurally dominate its exit block $m$; for selection (`OpSelectionMerge`) and loop (`OpLoopMerge`) constructs, dominance must be **strict** (`header != merge`). Structural reachability includes pseudo-edges from headers to their declared merge and continue targets, ensuring well-defined dominance even when all real branches return or kill.
3. **Structural post-dominance on continue constructs (`validate_cfg.cpp:825–832`):** For a loop's continue construct (spanning from the `Continue Target` block to the loop's single back-edge latch), the exit block must structurally **post-dominate** the continue target, preventing unstructured jumps out of continue sections.
4. **Single-entry / structured-exit construct nesting (`validate_cfg.cpp:838–881`):**
   - Every edge leaving a construct's block set `construct_blocks` must satisfy `construct.IsStructuredExit(_, succ)` (e.g., jumping to the construct's own merge block, an enclosing loop's merge/continue target, or an enclosing switch's merge block).
   - Every non-header block inside a construct may only receive predecessors from inside that construct (`pred` must be in `construct_blocks`), prohibiting jumps into the middle of an `if`/`switch`/`loop`.
   - If a nested selection or loop header $h'$ resides inside an outer construct $C$, $h'$'s own merge block $m'$ (if structurally reachable) **must also lie inside $C$** (`!construct_blocks.count(merge_block)` at line 871 is an error), enforcing strict tree-like nesting.
5. **Continue-target confinement (`validate_cfg.cpp:883–921`):** When a loop's `Continue Target` differs from its loop header, every structurally reachable non-back-edge predecessor of the continue target must belong to the loop construct.

#### 2.2 Maximal Reconvergence (`SPV_KHR_maximal_reconvergence`, `validate_cfg.cpp:961–1061`)

Traditional SPIR-V structured control flow guarantees reconvergence at merge blocks, but left reconvergence *inside* loops and across arbitrary branch joins under-specified across GPU vendors. `SPV_KHR_maximal_reconvergence` (`ExecutionMode MaximallyReconvergesKHR`) strengthens reconvergence semantics—crucial for subgroup ballots/shuffles and WebGPU's uniformity guarantees—by enforcing three additional static invariants in `MaximalReconvergenceChecks` (`validate_cfg.cpp:961–1061`):
1. **Distinct branch targets (`lines 997–1004`):** In any function reachable from a `MaximallyReconvergesKHR` entry point, `OpBranchConditional` must have `True Label != False Label`.
2. **No invocation repacking (`lines 940–959, 1005–1013`):** Ray-tracing invocation-repack instructions (`OpTraceRayKHR`, `OpReorderThreadWithHintEXT/NV`, `OpExecuteCallableKHR`, `OpReportIntersectionKHR`, etc.) are statically forbidden (`VUID-09565`), because repacking dynamically migrates invocations across subgroups.
3. **Restricted join points (`lines 1019–1058`):** A basic block may have $\ge 2$ unique predecessors **only** if it is a loop header (`OpLoopMerge` pre-terminator) or is referenced as a merge/continue/switch target by `OpSelectionMerge`, `OpLoopMerge`, or `OpSwitch`. Arbitrary diamond joins without an explicit merge annotation are rejected.

#### 2.3 SPIR-V Vulkan Memory Semantics Validation (`validate_memory_semantics.cpp`)

`ValidateMemorySemantics` (`source/val/validate_memory_semantics.cpp:25–226`) enforces the exact bitmask discipline connecting SPIR-V instructions to the Vulkan Memory Model:
- **Storage-class ↔ ordering bi-implication (`lines 130–152`):** Under Vulkan (`spvIsVulkanEnv` or `MemoryModel::VulkanKHR`), any non-relaxed ordering (`Acquire`, `Release`, `AcquireRelease`) **must** set at least one Vulkan storage-class bit (`UniformMemory`, `WorkgroupMemory`, `ImageMemory`, `OutputMemoryKHR`), and conversely setting any of those storage-class bits **must** pair with a non-relaxed ordering.
- **Availability/Visibility pairing (`lines 156–185`):** `MakeAvailableKHR` requires `Capability VulkanMemoryModel` and must pair with `Release` or `AcquireRelease`; `MakeVisibleKHR` requires `Capability VulkanMemoryModel` and must pair with `Acquire` or `AcquireRelease`.
- **`SequentiallyConsistent` prohibition (`lines 78–96`):** Vulkan forbids `SequentiallyConsistent` memory semantics (`must not be used in the Vulkan API`), forcing shaders onto release/acquire/relaxed scopes.
- **`Volatile` restriction (`lines 188–199`):** `Volatile` requires `Capability VulkanMemoryModel` and cannot be combined with memory-barrier instructions (`OpMemoryBarrier` / `OpControlBarrier`).

---

### 3. W3C WGSL Memory Model & Static Uniformity Analysis

**Basis:** normative (`gpuweb/gpuweb` @ `d178d9145ab1652ec933e71a8c30e8f6470f00a3`, `wgsl/index.bs`) + source (`google/dawn/src/tint/lang/wgsl/resolver/uniformity.cc`, `gfx-rs/wgpu/naga/src/valid/analyzer.rs`) + execution (Probe 1B) + documentation (`Lee-Jones et al., PLDI 2026`).

#### 3.1 WGSL Reduction to the Vulkan Memory Model (`wgsl/index.bs:12315–12474`)

Rather than exposing Vulkan's full non-coherent cache-domain matrix to web authors, WGSL defines a **fixed, simplified projection** onto the Vulkan Memory Model:
- **Non-atomic storage/workgroup/handle accesses (`lines 12451–12474`):** Every non-atomic read in `storage` or `workgroup` address space maps to `NonPrivatePointer | MakePointerVisible` with `Workgroup` scope; every non-atomic write maps to `NonPrivatePointer | MakePointerAvailable` with `Workgroup` scope (and analogously `NonPrivateTexel | MakeTexel{Visible,Available}` for `handle` textures). Cross-workgroup non-atomic visibility within a single dispatch is intentionally **unsupported**—inter-workgroup synchronization must occur at WebGPU command-buffer/pass boundaries or via atomics.
- **Atomics (`lines 12412–12434`):** All WGSL atomic built-ins (`atomicLoad`, `atomicStore`, `atomicAdd`, `atomicCompareExchangeWeak`, etc.) use **`Relaxed` memory semantics only** (no `Acquire`/`Release` atomics!), with memory scope `Workgroup` for `workgroup` address space and `QueueFamily` for `storage` address space (falling back to `Device` scope when the backend SPIR-V lacks `VulkanMemoryModel`, `line 12426`).
- **Synchronization built-ins (`lines 12419–12449, 20567–20671`):** `workgroupBarrier()` (`WorkgroupMemory`), `storageBarrier()` (`UniformMemory`), `textureBarrier()` (`ImageMemory`), and `workgroupUniformLoad(p)` all emit `Workgroup`-scoped execution+memory control barriers with `AcquireRelease` ordering and **no** `MakeAvailable`/`MakeVisible` bits (since per-instruction `MakePointer{Available,Visible}` already handles cache coherence on every non-atomic access). Note a subtle vector-aliasing rule (`lines 12362–12372`): writing a single component of a vector (e.g., `v.y = 1.0`) *may* read and write all components of `v`, potentially creating data races with concurrent accesses to `v.x`.

#### 3.2 WGSL Static Uniformity Analysis Algorithm (`wgsl/index.bs:12504–13950`)

Collective operations—synchronization barriers (`workgroupBarrier`, `storageBarrier`, `textureBarrier`, `workgroupUniformLoad`), implicit/explicit fragment derivatives (`dpdx`, `dpdy`, `textureSample`), and subgroup/quad operations—produce GPU hangs or non-portable garbage if executed in **non-uniform control flow**. WGSL mandates a static, conservative, interprocedural **Uniformity Analysis** (`wgsl/index.bs:12535–12811`):

1. **Topological bottom-up pass (`lines 12617–12622`):** Because WGSL forbids recursion, functions are analyzed in reverse topological call-graph order (callees before callers), summarizing each function with five compact tags:
   - `CallSiteTag`: `CallSiteRequiredToBeUniform.<S>` (with `potential-trigger-set`) or `CallSiteNoRestriction`.
   - `FunctionTag`: `ReturnValueMayBeNonUniform` or `NoRestriction`.
   - Per-parameter `ParameterTag`: `ParameterRequiredToBeUniform.<S>`, `ParameterContentsRequiredToBeUniform.<S>`, or `ParameterNoRestriction`.
   - Per-parameter `ParameterReturnTag`: `ParameterReturnContentsRequiredToBeUniform` or `ParameterReturnNoRestriction`.
   - Per-pointer-parameter `PointerParameterTag`: `PointerParameterMayBeNonUniform` or `PointerParameterNoRestriction`.
2. **Directed implication-graph construction (`lines 12633–13450`):** Within each function, the analyzer first desugars `function`-space pointer `let`-bindings to expose root identifiers (`#pointer-desugar`, `lines 12812–12863`), tracks reaching assignments of local `var`s (`#func-var-value-analysis`), and constructs a directed graph where nodes represent control-flow points, expression values, variables, or pointer contents, plus four sentinel nodes: `RequiredToBeUniform.{error, warning, info}` (interpreted as logical `True`) and `MayBeNonUniform` (interpreted as logical `False`). Every directed edge $A \to B$ encodes the implication *"for $A$ to be uniform, $B$ must be uniform"*:
   - A call to `workgroupBarrier()` adds `RequiredToBeUniform.error -> CallSite -> CF_current` (unfilterable).
   - A call to `textureSample(...)` adds `RequiredToBeUniform.<S> -> CallSite -> CF_current` where `<S>` is governed by `@diagnostic(..., derivative_uniformity)` (default `error`, filterable to `warning`/`info`/`off`).
   - Reading `local_invocation_id`, a non-uniform fragment input, or a mutable `storage`/`workgroup` variable adds `V(expr) -> MayBeNonUniform`.
   - `workgroupUniformLoad(p)` requires both `CF_current` and pointer `p` to be uniform (`RequiredToBeUniform.error -> {CF_current, V(p)}`), executes a workgroup barrier, and **returns a provably uniform value** (NO edge to `MayBeNonUniform` — serving as the primary escape hatch to convert shared-memory decisions back into uniform control flow!).
3. **Statement reconvergence and loop fixpoints (`wgsl/index.bs:13111–13331`):**
   - **`if e { s1 } else { s2 }`:** Evaluates `(CF, e) => V`, then analyzes `s1` and `s2` under control flow `V` producing `CF1, CF2`. If statement behavior is strictly `{Next}` (neither branch can `return`, `break`, or `continue` out), WGSL assumes reconvergence and sets the post-`if` control flow back to **`CF`** (`line 13173`). If behavior is anything else (e.g., `{Next, Return}` from an early `return`), a fresh node `CFend` is created with `CFend -> {CF1, CF2}` (`line 13178`), propagating divergence to every subsequent statement!
   - **`loop { s1 continuing { s2 } }`:** Creates iteration-start node `CF'` with `CF' -> CF`. If `s1`'s behavior intersects `{Next, Continue}`, adds back-edges `CF' -> CF2` (after continuing block) or `CF' -> CF1`, forming a graph cycle resolved cleanly by reachability. If `Return` is not in `s1`'s behavior, loop exit reconverges to `CF`; if `Return` *is* in `s1`'s behavior, loop exit inherits `CF'` (or `CF1`), keeping post-loop control flow non-uniform!
   - **`break if e;`:** Creates `CFend -> V(e)` (`lines 13250–13258`), tainting loop continuation uniformity when exit depends on a non-uniform condition.
4. **Reachability check (`lines 12785–12804`):** Traversing in severity order `{error, warning, info}`, if `MayBeNonUniform` is reachable from `RequiredToBeUniform.<S>`, a diagnostic of severity `<S>` is triggered. Otherwise, reachability from `RequiredToBeUniform.<S>` to `CF_start`, `param_i`, or `param_i_contents` sets the function's caller-facing summary tags; reachability from `Value_return` to `MayBeNonUniform` or `param_i` sets the return uniformity tags.
5. **Formal soundness and known over-approximations (`wgsl/index.bs:13810–13875`; `Lee-Jones et al., PLDI 2026`):**
   - **Composite coarseness (false positive):** A partial assignment `a[0] = local_invocation_id.x` taints the entire composite variable `a`, causing `if (a[1] == 2u) { workgroupBarrier(); }` to be rejected even though `a[1]` is dynamically uniform (`wgsl/index.bs` Example 3, confirmed in Probe 1B Case 4).
   - **Dynamic-error invalidation (`wgsl/index.bs:4208–4212, 12602–12604`):** Uniformity analysis explicitly assumes no dynamic errors occur. If a hardware implementation implements out-of-bounds access as **Trap** (terminating only the faulting invocation), a provably uniform `workgroupBarrier()` can still deadlock!
   - **Specification formalization (`Lee-Jones, Wickerson, Donaldson, PLDI 2026`, `DOI: 10.1145/3808331`):** Formalized an operational semantics (`TinyWGSL`) defining barrier divergence for the first time, reformulated the WGSL uniformity rules, and uncovered and upstreamed soundness and precision fixes to the W3C WGSL editors.

#### 3.3 Implementation Divergence: Dawn/Tint vs. wgpu/Naga Uniformity

**Basis:** source (`google/dawn/src/tint/lang/wgsl/resolver/uniformity.cc`, `gfx-rs/wgpu/naga/src/valid/analyzer.rs`).

| Dimension | W3C WGSL Normative Spec (`wgsl/index.bs`) | Dawn / Tint (`uniformity.cc`) | wgpu / Naga (`analyzer.rs`) |
| :--- | :--- | :--- | :--- |
| **Algorithmic Structure** | Per-function directed implication graph (`RequiredToBeUniform.S` $\to^*$ `MayBeNonUniform`), bottom-up call-graph tags | Direct implementation of spec implication graph (`CallSiteTag`, `FunctionTag`, `ParameterTag`, `Node` graph, `UniformityScope::{kAll, kWorkgroup, kSubgroup}`) | Single-pass AST/IR `UniformityDisruptor` propagation (`FunctionUniformity` with `non_uniform_result`, `UniformityRequirements`, `ExitFlags::{MAY_RETURN, MAY_KILL}`) |
| **Compute Barriers (`workgroupBarrier` / `storageBarrier`)** | Mandatory unfilterable `error` | Enforced (`CallSiteRequiredToBeUniform` error) | Enforced via `UniformityRequirements::WORK_GROUP_BARRIER` (`analyzer.rs:29, 953–959`) |
| **`workgroupUniformLoad` Uniformity Check** | Mandatory unfilterable `error` on CF and pointer `p` | Enforced | **Disabled (commented out)** in `analyzer.rs:960–986` (`"Don't check that this call occurs in uniform control flow until Naga implements WGSL's standard uniformity analysis"`) |
| **Fragment Derivatives (`dpdx`, `textureSample`)** | Default `error`, filterable via `derivative_uniformity` | Enforced with diagnostic severity filter | **Disabled at compile time** via `const DISABLE_UNIFORMITY_REQ_FOR_FRAGMENT_STAGE: bool = true;` (`analyzer.rs:21, 30–31`), setting `DERIVATIVE = 0` and `IMPLICIT_LEVEL = 0` |
| **Subgroup Uniformity (`subgroup_uniformity`)** | Separate analysis pass per `UniformityScope` | Supported (`UniformityScope::kSubgroup`) | Not separated into full implication-graph subgroup pass |

Engineering consequence: A WGSL shader containing a divergent `textureSample` or divergent `workgroupUniformLoad` will pass `wgpu`/Naga validation (`9450c94c1ff2c734f7c73db604ad87501eee1803`) while failing WebGPU conformance in Chromium/Dawn/Tint (`05a3f2091af9815b4412d188fe1ba2b29d6683c6`).

---

### 4. Untrusted Shader Sandboxing Over Vendor Driver JITs (`wgpu`/Naga & Dawn/Tint)

**Basis:** source (`gfx-rs/wgpu` `naga/src/proc/index.rs`, `naga/src/back/{spv,msl,hlsl}/`, `wgpu-hal/src/vulkan/device.rs`; `google/dawn` `src/tint/lang/core/ir/transform/robustness.cc`) + documentation (`SafeRace`, OOPSLA 2025, `10.1145/3763075`).

Browser WebGPU engines execute attacker-controlled WGSL inside multi-tenant GPUs whose vendor drivers (`DXC`, Apple Metal/LLVM, NVIDIA/AMD/Intel/Qualcomm SPIR-V compilers) aggressively optimize under C-like no-UB assumptions and share physical GPU memory across origins. Sandboxing rests on **four orthogonal defense layers**:

#### 4.1 Out-of-Bounds Memory Access Containment (`BoundsCheckPolicies`)

WGSL (`wgsl/index.bs:4151–4213`) forbids performing out-of-bounds memory accesses as written, permitting implementations either to redirect accesses to another in-bounds location within the same `GPUBuffer`/variable (`Restrict`) or to return zero on reads and drop writes (`ReadZeroSkipWrite`), while warning that **Trap** breaks uniformity. Naga (`naga/src/proc/index.rs:42–171`) splits policy enforcement across four distinct access classes in `BoundsCheckPolicies`:

| `BoundsCheckPolicies` Field | Covered Expressions (`index.rs:145–165`) | Policy Semantics | Typical Hardware Offload |
| :--- | :--- | :--- | :--- |
| `index` | `Private`, `Function`, `Workgroup` arrays, plus by-value vectors/matrices | `Restrict` (unsigned `min(idx, max_idx)`—note negative signed indices map to last element, `index.rs:45–48`) or `ReadZeroSkipWrite` (cache index in temp via `find_checked_indexes`, `index.rs:229–283`) | None (always compiler-injected; hardware buffer robustness does not cover local/workgroup memory) |
| `buffer` | `Storage` and `Uniform` `GlobalVariable` chains | `Restrict`, `ReadZeroSkipWrite`, or `Unchecked` | Can be `Unchecked` **only** when Vulkan `robustBufferAccess2` / `nullDescriptor` or D3D12 hardware bounds checks guarantee per-buffer containment |
| `image_load` | `Expression::ImageLoad` (coordinates, array index, sample, mip level) | `Restrict` or `ReadZeroSkipWrite` (`ImageStore` has no policy because all supported GPU APIs discard OOB image stores natively, `index.rs:116–119`) | Hardware `robustImageAccess2` where supported |
| `binding_array` | `TypeInner::BindingArray` dynamic descriptor indexing | `Restrict` / `ReadZeroSkipWrite` / `Unchecked` | Descriptor-table bounds checks |

Notice Naga's default hierarchy (`naga/src/proc/index.rs:21–33`): Naga's standalone `Default` is `Unchecked`, WebGPU requires `Restrict` for array/vector/matrix accesses, and native `wgpu` defaults to `ReadZeroSkipWrite` (overridable via `ShaderRuntimeChecks` in `wgpu-hal/src/vulkan/device.rs:760–782`, which explicitly turns off `bounds_check_policies`, `force_loop_bounding`, `int_div_checks`, `ray_query_initialization_tracking`, `task_shader_dispatch_tracking`, and `mesh_shader_primitive_indices_clamp` only when unsafe opt-out flags are passed).

#### 4.2 Loop-Bounding Fuel Counters Against Forward-Progress UB Bounds-Check Elision

**Basis:** source (`gfx-rs/wgpu` `naga/src/back/msl/writer.rs:1065–1185`, `naga/src/back/spv/block.rs:280–420`, `naga/src/back/{spv,msl,hlsl}/mod.rs`).

One of the most subtle compiler-security interactions in GPU sandboxing is **forward-progress UB exploitation** documented directly in `naga/src/back/msl/writer.rs:1065–1165`:

```c
// Attacker-crafted shader + Naga-injected bounds check:
if (i >= 10) {
    while (true) { }       // No side effects -> C++/LLVM forward-progress UB!
}
if (i < 10) {              // Naga-injected ReadZeroSkipWrite bounds check
    a[i] = secret_or_oob;
}
```

1. **The Exploit:** Vendor LLVM-based GPU compilers (notably Apple Metal/MSL and DXC/Vulkan SPIR-V backends) inherit C++11/LLVM `mustprogress` semantics: a side-effect-free infinite loop is UB. Range analysis proves `while (true) {}` unreachable $\implies$ infers `i < 10` $\implies$ **deletes Naga's `if (i < 10)` bounds check**—and in observed MSL compilations, **deletes the `while (true) {}` loop itself**, enabling an attacker shader to perform arbitrary out-of-bounds GPU reads/writes and terminate cleanly! (The same backwards-propagation hazard works even when the guarded access precedes the infinite loop.)
2. **Why `volatile` Breaks Failed:** Earlier Naga revisions emitted `if (volatile bool unpredictable = false; unpredictable) break;`. While sound against range analysis, `volatile` disabled safe loop unrolling and degraded shader throughput severely (`msl/writer.rs:1118–1133`).
3. **Simulated 64-Bit `vec2<u32>` Decrementing Fuel Counter (`force_loop_bounding = true` by default in SPV `mod.rs:1150`, MSL `mod.rs:347`, HLSL `mod.rs:594`):** Both Naga (`spv/block.rs:293–415`, `msl/writer.rs:1165–1185`) and Chromium Dawn/Tint (`prevent_infinite_loops.cc`) declare a per-loop function-scope `vec2<u32>` counter initialized to `(u32::MAX, u32::MAX)` ($2^{64} - 1$ iterations) and decrement it with borrow on every loop header iteration, breaking to `merge_id` at `(0, 0)`. Crucially, Naga counts **down from `u32::MAX`** rather than up from `0` specifically to work around an Intel GPU driver hang (`msl/writer.rs:1174–1175`). Because every loop now has a finite static upper bound of $2^{64}-1$ iterations, LLVM cannot invoke forward-progress UB while still permitting loop unrolling and vectorization on statically bounded loops. (Note: $2^{64}-1$ fuel does *not* prevent wall-clock GPU TDR denial-of-service; OS GPU watchdogs handle liveness timeouts separately.)

#### 4.3 Cross-Origin Workgroup Zero-Initialization and SafeRace TOCTOU Boundaries

- **Workgroup Memory Zero-Initialization (`naga/src/back/spv/mod.rs:1058–1095`, `wgpu-hal/src/vulkan/device.rs:750–805`):** GPU SRAM (`Workgroup` / threadgroup shared memory) retains residual data from prior dispatches—potentially belonging to a different browser origin or OS process. Naga enforces `ZeroInitializeWorkgroupMemoryMode::Native` (emitting `OpVariable` with `OpConstantNull` initializer via `VK_KHR_zero_initialize_workgroup_memory` / Vulkan 1.3) or `Polyfill` (injecting explicit zero stores + `workgroupBarrier()` at entry-point start). Notably, `wgpu-hal/src/vulkan/device.rs:750–758` detects `Workarounds::POLYFILL_MESH_TASK_WORKGROUP_ZERO_INIT` and forces `Polyfill` on Task/Mesh stages even when `Native` is enabled globally, guarding against driver bugs in native zero-init for mesh pipelines.
- **Data-Race Bounds-Check Bypass (`SafeRace`, Levine et al., OOPSLA 2025, `DOI: 10.1145/3763075`):** Even when WGSL/Naga/Tint inject bounds checks on every array index, if the index originates from a **data race** in `storage` or `workgroup` memory, WebGPU specifies an indeterminate value rather than UB—yet lowering to SPIR-V/LLVM/MSL maps data races into native UB or allows the downstream compiler to **rematerialize/reload the racy variable twice** (once for `idx < len`, a second time for `buf[idx]`), creating a classic TOCTOU out-of-bounds memory-safety bypass! `SafeRace` demonstrates concrete driver-level escapes and shows that sound race-resilient sandboxing requires freezing/pinning loaded indices (or atomic-relaxed loads / volatile barriers on racy loads) before applying bounds clamping so downstream optimizers cannot re-fetch mutated memory.

---

### 5. Executable Micro-Probe Verification Results

**Basis:** execution (standalone Python 3.13 relational checker and BFS implication-graph verifier; reproducible via the self-contained equations below).

#### 5.1 Probe 1A: Vulkan Memory Model Relational Checker (`alloy/spirv.als`)

Encoding the exact finite-execution relational equations of `KhronosGroup/Vulkan-MemoryModel/alloy/spirv.als` (`avvisinc`, `inscope`, `mutordatom`, `sw`, `ithbsemsc0`, `hb`, `avsg`–`avsh`, `vissg`–`vissh`, `locord`, `fr`, `dr`, `consistent`) in Python reproduces all core Khronos Alloy litmus verdicts and sharpens two critical invariants. The core verification kernel reduces directly to transitive closure (`rel_tc`) and relation composition (`rel_comp`) over finite event sets:

```python
# Reproducible core axioms mirroring alloy/spirv.als lines 356-403 (Python 3.13):
# locord = sloc & ((hb & sthd & sref) | (Rnp . hb . (R|W - PRIV)) | waw(av_D, D) | raw(av_D, D, vis_D))
# fr     = (~rf . ((W x W) & locord)) | (~rf . asmo) | (rfinit . sloc . W) - iden
# dr     = sloc & ((W x W | W x R | R x W) - mutordatom - iden - (locord | ~locord))
# consistent = is_acyclic(locord | rf | fr | asmo) and not ((rf . (R - A)) & twoplus(W . locord))
```

| Litmus Execution | `chains` Feature | `consistent[X]` | `#dr` (Data Races) | `locord` on Data `x` | Discriminating Insight |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `noncohmp` (`R(x)=1`) | `VK_TRUE` | `True` | `0` | `[('wx', 'rx')]` | `NonPrivate` + `SEMAV(WG)` + `SEMVIS(WG)` establishes `locord` and race freedom. |
| `noncohmp` (`R(x)=0` stale) | `VK_TRUE` | `False` | `0` | `[('wx', 'rx')]` | Forbidden: `rx --fr--> wx --locord--> rx` violates `is_acyclic[locord+rf+fr+asmo]`. |
| `privmp` (missing `NonPrivate`) | `VK_TRUE` | `True` | `2` | `[]` | Private ops excluded from shader `locord` $\implies$ formal data race despite full barriers. |
| `qfmp` (same QueueFamily) | `VK_TRUE` | `True` | `0` | `[('wx', 'rx')]` | `sqf` holds $\implies$ `inscope` holds $\implies$ valid `AVQF`/`VISQF` handoff. |
| `qfmpfail` (distinct QueueFamilies) | `VK_TRUE` | `True` | `4` | `[]` | `sqf` fails $\implies$ `inscope` fails on both flag `y` and data `x` $\implies$ 4 race pairs. |
| 2-hop chain (`WG -> Dev -> WG`) | `VK_TRUE` | `True` | `0` | `[('wx', 'rx')]` | Multi-hop `avwg -> avsh` and `vissh -> viswg` chain succeeds. |
| 2-hop chain (`WG -> Dev -> WG`) | `VK_FALSE` | `True` | `2` | `[]` | `chains = stor[EV]` collapses 2-hop chains $\implies$ silent data race! |
| `WaW` with `AV` only (no `VIS`) | `VK_TRUE` | `True` | `0` | `[('w1x', 'w2x')]` | Confirms `WaW` needs availability only (`spirv.als:374`). |
| `RaW` with `AV` only (missing `VIS`) | `VK_TRUE` | `True` | `2` | `[]` | Confirms `RaW` strictly requires both halves (`spirv.als:375`). |

#### 5.2 Probe 1B: W3C WGSL Static Uniformity Implication-Graph Verifier (`wgsl/index.bs` §13.3)

Running exact shortest-path reachability from `RequiredToBeUniform.error` to `MayBeNonUniform` over graphs built by `wgsl/index.bs:13131–13312` produces:
- **Case 1 (divergent `if (tid == 0u) { workgroupBarrier(); }`):** `REJECTED` — witness `RequiredToBeUniform.error -> Call(workgroupBarrier) -> V(tid==0) -> V(tid) -> MayBeNonUniform`.
- **Case 2 (post-`if` reconvergence, behavior `{Next}`):** `ACCEPTED` — post-`if` control flow resets to `CF_start`, isolating the barrier from `V(tid==0)`.
- **Case 3 (divergent early `return`, behavior `{Next, Return}`):** `REJECTED` — witness `RequiredToBeUniform.error -> Call(workgroupBarrier) -> CFend -> CF1_then -> V(tid==0) -> MayBeNonUniform`.
- **Case 4 (composite partial-write over-approximation, `a[0] = tid; if (a[1] == 2u) { workgroupBarrier(); }`):** `REJECTED` — witness `RequiredToBeUniform.error -> Call(workgroupBarrier) -> V(a[1]==2) -> V(a_after_partial_write) -> V(tid) -> MayBeNonUniform` (demonstrating sound whole-composite tainting).

## Boundaries

- **not examined:**
  - Direct execution of `KhronosGroup/Vulkan-MemoryModel/alloy/spirv.als` inside the Java Alloy Analyzer (`alloy/RunCommandLine.java`) against the full 67-file `alloy/tests/*.test` suite (we inspected `spirv.als` and representative `.test` files directly and cross-checked core axioms via an independent Python relational checker in Probe 1A).
  - Vendor-proprietary GPU binary ISA compilers (`NVIDIA PTX/SASS`, `AMD GCN/RDNA LLVM`, `Intel IGC`, `Apple AGX`, `Qualcomm Adreno`) and hardware microarchitectural errata beyond documented `wgpu`/Naga workarounds (`wgpu#7319` Intel decrement workaround and `POLYFILL_MESH_TASK_WORKGROUP_ZERO_INIT`).
  - Naga's HLSL and GLSL writer internals for `force_loop_bounding` and `ReadZeroSkipWrite` (we verified the option flags and defaults in `naga/src/back/{hlsl,msl,spv}/mod.rs` and the full lowering in `spv/block.rs` and `msl/writer.rs`, but did not audit every line of `hlsl/writer.rs` or `glsl/writer.rs`).
  - WGSL `subgroup_uniformity` edge cases for quad-control (`SPV_KHR_quad_control`) and subgroup matrix / cooperative matrix extensions (`vulkan_memorymodel.adoc:1316`).
- **unknown:**
  - Whether specific future revisions of `gfx-rs/wgpu`'s Naga have closed the two uniformity gaps verified at commit `9450c94c1ff2c734f7c73db604ad87501eee1803` (`DISABLE_UNIFORMITY_REQ_FOR_FRAGMENT_STAGE = true` and commented-out `WorkGroupUniformLoad` uniformity checking).
  - Whether all production Vulkan drivers faithfully implement `vulkanMemoryModelAvailabilityVisibilityChains = VK_TRUE` without silent miscompilations under stress litmus suites (empirical GPU hardware conformance remains hardware- and driver-version-dependent, per Kirkham et al. and `MC Mutants`).
- **known not to apply:**
  - `KhronosGroup/Vulkan-MemoryModel` shader-domain `Device`-scoped synchronization does **not** establish availability or visibility across the *device domain* (non-shader fixed-function/transfer units) or *host domain*; API barriers, `vkFlushMappedMemoryRanges`/`vkInvalidateMappedMemoryRanges`, and `QFOT` barriers remain mandatory.
  - Naga's 64-bit `force_loop_bounding` counter ($2^{64} - 1$ iterations) does **not** bound wall-clock shader execution time or prevent GPU denial-of-service hangs (TDR); its purpose is strictly to eliminate forward-progress UB so vendor compilers cannot elide injected bounds checks.
  - WGSL's static uniformity guarantee does **not** survive dynamic errors such as a trapping out-of-bounds access (`wgsl/index.bs:4208–4212`), nor does static bounds checking alone prevent bounds-check bypasses if a downstream compiler reloads a data-racy index expression (`SafeRace`, OOPSLA 2025).
- **unsupported:**
  - WGSL explicitly does **not** support `Acquire`/`Release` ordering on atomic built-in functions (`wgsl/index.bs:12431`, all atomics are `Relaxed`), nor cross-workgroup non-atomic `storage` visibility within a single compute dispatch (`MakePointer{Available,Visible}` is fixed at `Workgroup` scope, `wgsl/index.bs:12453–12463`), nor recursion (`wgsl/index.bs:12620`).
  - Vulkan's SPIR-V validator explicitly forbids `SequentiallyConsistent` memory semantics (`validate_memory_semantics.cpp:78–96`) and irreducible CFGs in `Shader`-capability modules (`validate_cfg.cpp:753–787`).

## Evidence

All primary repository sources were resolved on `2026-11-19` via `git -c protocol.version=0 ls-remote` and fetched directly at their exact 40-character commit SHAs:

1. **`KhronosGroup/Vulkan-MemoryModel` @ `894ae9027ce8f66e40d5f79c3eb727e77955aef4`:**
   - `alloy/spirv.als` (434 lines): `chains` feature toggle (lines 85–86, 354–366), `avvisinc` (lines 168–171), `NONPRIV`/`PRIV` (lines 217–222), `AV*`/`VIS*` domain mapping (lines 234–244), `inscope`/`mutordatom` (lines 287–293), `rs`/`hypors` omitting C++ same-thread atomic write clause (lines 304–310), `sw` (lines 313–325), storage-class-templated `ithbsemsc*`/`hb` (lines 333–349), `locord` asymmetric `WaW`/`RaW`/`RaR`/`WaR` (lines 368–381), `fr`/`dr`/`visto` (lines 387–394), `consistent`/`racefree`/`locordcomplete` (lines 397–427).
   - `alloy/tests/{noncohmp,noncohmpfail,qfmp,qfmpfail,privmp}.test`: positive/negative litmus specifications verifying non-private requirement, reference-specific availability, and queue-family scope boundaries.
2. **`KhronosGroup/Vulkan-Docs` @ `f7de774cace1509af0f10b8d859c973b5354ff62`:**
   - `appendices/memorymodel.adoc`: Private vs. Non-Private (lines 655–677), Inter-Thread-Happens-Before & Happens-Before non-transitivity note (lines 681–729), Memory Domains & Availability/Visibility Chains (lines 733–893), API Availability/Visibility/Domain ops for barriers, `vkFlushMappedMemoryRanges`, `vkInvalidateMappedMemoryRanges`, `vkQueueSubmit` (lines 896–930), Scope-to-Domain mapping (lines 952–967), Per-Instruction `MakePointer{Available,Visible}` (lines 978–1028), `Location-Ordered` + device-domain vs. device-scope warning + `Data Race` + `Acyclicity` (lines 1033–1188).
   - `chapters/synchronization.adoc`: `[[synchronization-queue-transfers]]` Queue Family Ownership Transfer normative release/acquire rules and undefined-content warning (lines 8032–8100).
3. **`KhronosGroup/SPIRV-Tools` @ `326b40880bd4a4e60b1b6b9cf31560b2f040de81` & `KhronosGroup/SPIRV-Headers` @ `50184103b19027f5c7080060712d6a9470cf59ee`:**
   - `source/val/validate_cfg.cpp`: `StructuredControlFlowChecks` (lines 753–937: single-latch loop check lines 761–787, strict merge dominance lines 807–821, continue post-dominance lines 825–832, structured exits & nested merge confinement lines 838–881, continue-target predecessors lines 883–921) and `MaximalReconvergenceChecks` (lines 961–1061: `IsInvocationRepackInstruction`, distinct conditional targets, restricted multi-predecessor join blocks).
   - `source/val/validate_memory_semantics.cpp`: `ValidateMemorySemantics` (lines 25–226: `SequentiallyConsistent` ban lines 78–96, storage-class ↔ ordering bi-implication lines 130–152, `MakeAvailableKHR`/`MakeVisibleKHR` pairing lines 156–185, `Volatile` checks lines 188–199).
4. **`gpuweb/gpuweb` @ `d178d9145ab1652ec933e71a8c30e8f6470f00a3`:**
   - `wgsl/index.bs`: Out-of-Bounds Access dynamic errors & uniformity invalidation note (lines 4151–4213), WGSL Memory Model reduction to Vulkan Memory Model (lines 12315–12474), Uniformity Analysis specification, tags, implication-graph construction, pointer desugaring, statement/loop/call rules, and composite over-approximation Example 3 (lines 12504–13910), Synchronization Built-ins `storageBarrier`/`textureBarrier`/`workgroupBarrier`/`workgroupUniformLoad` (lines 20567–20671).
5. **`gfx-rs/wgpu` @ `9450c94c1ff2c734f7c73db604ad87501eee1803` & `google/dawn` @ `05a3f2091af9815b4412d188fe1ba2b29d6683c6`:**
   - `naga/src/valid/analyzer.rs`: `DISABLE_UNIFORMITY_REQ_FOR_FRAGMENT_STAGE = true` (line 21), `UniformityRequirements` (lines 28–34), `Uniformity`/`ExitFlags`/`FunctionUniformity` (lines 41–123), commented-out `S::WorkGroupUniformLoad` uniformity check (lines 960–986).
   - `naga/src/proc/index.rs`: `BoundsCheckPolicy` (`Restrict`, `ReadZeroSkipWrite`, `Unchecked`, lines 42–63), `BoundsCheckPolicies` (`index`, `buffer`, `image_load`, `binding_array`, lines 70–171), `find_checked_indexes` (lines 229–283).
   - `naga/src/back/msl/writer.rs`: `gen_force_bounded_loop_statements` doc comment detailing the LLVM/Metal forward-progress UB bounds-check-elision attack, `volatile` regression, and decrementing `uint2` counter workaround for Intel drivers (lines 1065–1185).
   - `naga/src/back/spv/block.rs` (lines 280–420) & `naga/src/back/{spv,msl,hlsl}/mod.rs` (`force_loop_bounding: true` defaults at `spv/mod.rs:1150`, `msl/mod.rs:347`, `hlsl/mod.rs:594`; `ZeroInitializeWorkgroupMemoryMode` at `spv/mod.rs:1058–1149`).
   - `wgpu-hal/src/vulkan/device.rs`: runtime-check policy wiring and `POLYFILL_MESH_TASK_WORKGROUP_ZERO_INIT` workaround (lines 740–815).
   - `google/dawn/src/tint/lang/wgsl/resolver/uniformity.cc` (lines 1–120): `UniformityScope::{kAll, kWorkgroup, kSubgroup}`, `CallSiteTag`, `FunctionTag`, `ParameterTag`, `Node` graph directly realizing the W3C WGSL algorithm.
6. **Peer-reviewed literature:**
   - Wickerson, Batty, Sorensen, Constantinides, *"Automatically Comparing Memory Consistency Models"*, POPL 2017 (`DOI: 10.1145/3009837.3009838`).
   - Kirkham, Sorensen, Tureci, Martonosi, *"Foundations of Empirical Memory Consistency Testing"*, PACMPL (OOPSLA) 2020 (`DOI: 10.1145/3428294`).
   - Levine et al., *"MC Mutants: Evaluating and Improving Testing for Memory Consistency Specifications"*, ASPLOS 2023 (`DOI: 10.1145/3575693.3575750`).
   - Levine, Lee, Abbas, Little, Sorensen, *"SafeRace: Assessing and Addressing WebGPU Memory Safety in the Presence of Data Races"*, PACMPL (OOPSLA) 2025 (`DOI: 10.1145/3763075`).
   - Lee-Jones, Wickerson, Donaldson, *"Uniformity Analysis in the WebGPU Shading Language"*, PACMPL (PLDI) 2026 (`DOI: 10.1145/3808331`).
7. **Executable micro-probes (`2026-11-19`, Python 3.13):**
   - Probe 1A (Vulkan relational checker) and Probe 1B (WGSL implication-graph reachability) verified all 9 Vulkan litmus cases and 4 WGSL uniformity cases with zero errors (results tabulated in Section 5).

## Revalidation

To cheaply revalidate these findings against newer upstream revisions without repeating the full audit:

1. **Vulkan Memory Model axioms:** Diff `KhronosGroup/Vulkan-MemoryModel/alloy/spirv.als` (specifically `avvisinc`, `inscope`, `av*`/`vis*`, `locord`, `dr`, `consistent`) and `KhronosGroup/Vulkan-Docs/appendices/memorymodel.adoc` against `894ae9027ce8f66e40d5f79c3eb727e77955aef4` / `f7de774cace1509af0f10b8d859c973b5354ff62`. Any change to `chains`, `NONPRIV`, or `locord` requires re-running Probe 1A (or invoking `alloy/RunCommandLine` on `alloy/tests/*.test`).
2. **SPIR-V CFG and memory semantics rules:** Diff `KhronosGroup/SPIRV-Tools/source/val/validate_cfg.cpp` (`StructuredControlFlowChecks`, `MaximalReconvergenceChecks`) and `validate_memory_semantics.cpp` (`ValidateMemorySemantics`) against `326b40880bd4a4e60b1b6b9cf31560b2f040de81`.
3. **Naga uniformity gap closure check (cheapest high-signal check):** Inspect `gfx-rs/wgpu/naga/src/valid/analyzer.rs` for:
   - `DISABLE_UNIFORMITY_REQ_FOR_FRAGMENT_STAGE` (still `true` or removed/false?), and
   - `S::WorkGroupUniformLoad` (still commented out or replaced by an implication-graph pass matching `gpuweb/gpuweb/wgsl/index.bs`?).
4. **Loop-bounding and bounds-check sandboxing check:** Inspect `gfx-rs/wgpu/naga/src/back/msl/writer.rs` (`gen_force_bounded_loop_statements`), `naga/src/back/spv/block.rs` (`write_force_bounded_loop_instructions`), and `naga/src/proc/index.rs` (`BoundsCheckPolicies::choose_policy`) to verify that `force_loop_bounding` remains enabled by default, still defeats LLVM forward-progress UB range analysis, and that `SafeRace`-class index-freezing mitigations (if added upstream) are reflected in `naga` and `google/dawn/src/tint/lang/core/ir/transform/robustness.cc`.
