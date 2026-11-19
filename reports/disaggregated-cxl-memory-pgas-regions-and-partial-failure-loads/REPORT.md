# Disaggregated CXL Memory, PGAS Logical Regions, and Partial-Failure Loads

## Summary

Compute Express Link (`CXL` 2.0/3.0/3.1) maps rack-scale pooled memory directly into host CPU physical address spaces via `CXL.mem`, turning ordinary `MOV`/`LDR` instructions into multi-hop fabric transactions (`~130–600+ ns`) spanning cables, retimers, switches, and remote memory blades. This physical reality shatters four axioms baked into mainstream systems languages (`C`, `C++`, `Rust`), compiler IRs (`LLVM IR`), and formal memory models: **(1) infallible synchronous loads**, **(2) uniform single-machine coherence**, **(3) whole-machine simultaneous crash**, and **(4) single virtual-address pointer identity**.

Synthesizing CXL specifications, Linux kernel MCE recovery, LLVM speculation source, real `rustc` IR/assembly execution probes, CXL partial-failure research (`CXL0`, `CXLMC`, `DIKTAMO`/`ReCXL`, `Lupin`, `CXL-SHM`, `Cxlalloc`, Isabelle `CXL.cache`), and PGAS / logical-region languages (`Legion`/`Regent`, `Chapel`, `UPC++`) establishes six load-bearing conclusions:

1. **Ordinary Loads Can Trap Synchronously With Hardware Poison (`SRAR` `#MC` / `SEA`):** When a remote CXL blade or link suffers an uncorrectable error, `CXL.mem` returns a **Data Poison** flit (or trips fabric-wide **`Viral`** containment). Consuming a poisoned cache line raises a synchronous x86 Machine Check (`SRAR`) or ARM Synchronous External Abort (`SEA`). Linux `mm/memory-failure.c` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, lines 335–337) offlines the entire 4 KB page (`hwpoison`) and delivers `SIGBUS` (`BUS_MCEERR_AR`), killing userspace processes because neither C++ nor Rust offers exception-safe signal unwinding (unlike Linux kernel `copy_mc_64.S`, which uses `_ASM_EXTABLE_TYPE(..., EX_TYPE_DEFAULT_MCE_SAFE)`).
2. **Rust `&T` and LLVM `dereferenceable(N)` Actively Defeat Software Fault Guards (`Basis: execution`):** Normative LLVM LangRef (`llvm/docs/LangRef.md` lines 1650–1654) defines `dereferenceable(<n>)` as permitting speculative loads *"without a risk of trapping,"* enforced directly by `ValueTracking.cpp` lines 7935–7944 (`isDereferenceableAndAlignedPointer`). Compiling a real guarded Rust function (`if blade_ok { acc += *p }`) with `rustc 1.98.0-nightly -O` attaches `dereferenceable(8)` to `p: &u64`, hoists `load i64, ptr %p` unconditionally above `blade_ok` in LLVM IR, and lowers the loop to x86-64 **`cmovneq (%rdx), %rax`**—which architecturally performs the memory load from `(%rdx)` even when `blade_ok == false` and loop trip count `n == 0`, triggering a fatal `SRAR` `#MC` outside any guard. Replacing `&u64` with raw `*const u64` removes `dereferenceable(8)` and preserves the branch guard.
3. **Asymmetric Partial-Host Crashes Break TSO, Release-Acquire, and Even Full-System `Px86` Proofs (`CXL0`, `CXLMC`):** Unlike single-host NVMM (`Px86`, where the entire machine reboots into sequential recovery), CXL shared memory is *"barely distributed and almost persistent"* (`arXiv:2405.19626`): when Host A crashes, its private dirty L1/L2/L3 caches vanish permanently while surviving Host B continues executing concurrently. Our exhaustive `CXL0` operational probe confirms a 5-step counterexample (`A:store(val=42) -> A:store(ready=1) -> B:load(ready)==1 -> CRASH(HostA) -> B:load(val)==0`) under plain Release-Acquire even with coherent CXL 3.0 snooping, collapsing to `0` causal violations once Host A executes `clwb(val) + sfence` prior to publishing `ready`.
4. **Hardware Coherence Recovery (`DIKTAMO`) Still Leaves Locks Orphaned and Heaps Leaked (`Lupin`, `CXL-SHM`, `Cxlalloc`):** Standard CXL 3.0 `HDM-DB` (`BISnp`) ignores processor failures; a CPU dying with Modified (`M`) cache lines stalls or corrupts coherent sharers. `DIKTAMO` (evolved from `ReCXL`, MICRO 2026, `arXiv:2602.08271`) propagates writes to hardware replica Logging Units (`27–30%` slowdown, `2.82x` faster than write-through) to recover directories and cache lines—yet cannot complete a dead CPU's interrupted critical section. Thus standard Rust/C++ `Mutex`/`Arc`/`shared_ptr` deadlock or leak permanently across multi-kernel CXL pods, requiring era-based non-blocking reclamation (`CXL-SHM`, SOSP 2023), pod failure detection (`Lupin`, DIMES '24), and detectable CXL allocators (`Cxlalloc`, ASPLOS 2026).
5. **Cross-Host HDM/ASLR Aliasing Breaks Absolute Pointers and Self-Relative Provenance:** Independent `HDM` decoders and per-host ASLR map the same CXL object to different virtual addresses on Host A vs. Host B, invalidating raw pointers (`*const T`, `Box<T>`, `&T`, `dyn Trait` vtables). Self-relative pointers (`boost::interprocess::offset_ptr`, `rkyv::RelPtr`) restore VA portability but collide with LLVM `getelementptr inbounds` and Rust Stacked/Tree Borrows intra-object provenance unless derived from a region-wide base provenance handle.
6. **PGAS & Logical Regions Provide Three Clean-Slate Language Archetypes:** `Legion`/`Regent` abolish raw pointers via **Logical Regions** with field-level algebraic **Privileges** (`LEGION_READ_ONLY`, `LEGION_WRITE_PRIV`, `LEGION_REDUCE`, discard masks) and **Coherence Modes** (`LEGION_EXCLUSIVE`, `LEGION_ATOMIC`, `LEGION_SIMULTANEOUS`, `LEGION_RELAXED`); `Chapel` makes **Locales** first-class (`on`-clause computation shipping + `dmapped` domain maps) but risks silent remote-access cliffs behind transparent wide-pointer indexing; `UPC++` **bans naked remote dereferencing**, forcing explicit asynchronous `rget`/`rput` returning `future<T>` over `global_ptr<T>` and thread-affine `persona` progress scopes.

## Applicability

This report covers the hardware standards, kernel/compiler implementations, CXL systems literature, and PGAS runtimes enumerated in `REPORT.json`:

- **Hardware & Kernel Fault Path:** Compute Express Link 2.0 / 3.0 / 3.1 architectural primitives (`CXL.mem`, `CXL.cache`, `HDM-DB` / `BISnp`, `DCD`, `G-FAM`, `Poison`/`Viral`, `IDE`), inspected alongside `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`: `arch/x86/lib/copy_mc_64.S`, `mm/memory-failure.c`). Note: CXL 2.0 hardware deployments typically provide non-coherent or single-host/device bias-flipped pooling, whereas hardware-coherent multi-host sharing (`HDM-DB` with `BISnp`) and elastic extent revocation (`DCD`/`G-FAM`) require CXL 3.0/3.1 silicon and switches.
- **Compiler Speculation & Empirical Probes:** `llvm/llvm-project` (`b86056e175f63cb99c5ca7c4139244c60b1056aa`: `llvm/docs/LangRef.md`, `llvm/lib/Analysis/ValueTracking.cpp`) paired with live compilation and assembly inspection via `rustc 1.98.0-nightly (14210df0e 2026-05-31)` targeting `x86_64-unknown-linux-gnu`.
- **CXL Memory Models, Model Checking, and Partial-Failure Systems:** Primary verified sources include Tan, Donaldson, Wickerson (ASPLOS 2025, `arXiv:2410.15908v2`), Xu et al. (`arXiv:2405.19626v2`), `CXL0` (Assa et al., ASPLOS 2026, `arXiv:2407.16300v3`), `CXLMC` (Guo, Truong, Demsky, ASPLOS 2026, `DOI:10.1145/3779212.3790150`, `uci-plrg/cxlmc` @ `1391bcbc81bc30835994105127f1ffe9a806f0ba`), `DIKTAMO` (evolved from `ReCXL`, Psistakis et al., MICRO 2026, `arXiv:2602.08271v2`), `Lupin` (Zhu et al., DIMES @ SOSP 2024, `DOI:10.1145/3698783.3699377`), `Cxlalloc` (ASPLOS 2026, `DOI:10.1145/3779212.3790149`, `nwtnni/cxlalloc` @ `eba659a27ebd580cc72069dfb0bce625ef0580ca`), and `CXL-SHM` (Zhang et al., SOSP 2023, `DOI:10.1145/3600006.3613135`, `madsys-dev/sosp-paper19-ae` @ `0ae5ed7d073436eeaad331c05971874cc29a9889`).
- **PGAS and Logical-Region Runtimes:** Pinned source inspections of `StanfordLegion/legion` (`aea587e157abff12f7d089c81f29cd3a8b993a2b`, `runtime/legion/api/config.h`), `chapel-lang/chapel` (`732cf95e1d870063b5be878a8ba9f7ed0642645f`, `doc/rst/language/spec/locales.rst`), and `BerkeleyLab/upcxx` (`824c7c5521e6b56c564eb74e75fb7ff7b084fbb5`, `src/global_ptr.hpp`, `src/persona.hpp`).

## Findings

### 1. Disaggregated CXL Fabric Physical Reality, Latency Cliffs, and Coherence Formalization

Basis: normative + documentation + source

#### 1.1 Latency Tiers and Non-Uniform Failure Domains
Empirical characterizations on real CXL hardware and pools (`DirectCXL` USENIX ATC 2022, `Pond` ASPLOS 2023, `Demystifying CXL` MICRO 2023, `Memstrata` OSDI 2024, `HydraRPC` USENIX ATC 2024) establish that `CXL.mem` cannot be modeled accurately as uniform local DRAM or even symmetric dual-socket NUMA:
- **Local DDR5 DRAM:** `~70–100 ns` load-to-use latency, single board/power/crash domain, uniform socket-coherent MESI/MOESI.
- **Direct-attached CXL Type-3 memory expander:** `~130–200 ns` latency, lower bandwidth than local channels, independent media/link controller.
- **Single-switch pooled `CXL.mem` (CXL 2.0/3.0):** `~200–400 ns` unloaded latency, with asymmetric read/write queuing under multi-tenant contention (`Memstrata`, OSDI 2024).
- **Multi-hop switched CXL 3.0 `G-FAM` (Global Fabric-Attached Memory):** `~500–600+ ns` under contention (6–8× local DRAM), traversing SerDes FEC framing, retimers, fabric switches, and external memory controllers.

Treating pooled CXL memory as transparent flat `malloc` pages causes 3–10× latency collapses on pointer-chasing structures (linked lists, B-trees, GC mark stacks, hash chains) and collapses worst-case execution time (`WCET`) reasoning across FFI boundaries whenever local and remote slices share one flat `&[u8]` type.

#### 1.2 Hardware Cache Coherence (`CXL.cache` & CXL 3.0 `HDM-DB` / `BISnp`)
CXL 1.1/2.0 lacked true hardware-coherent multi-host sharing (`HDM-H` and `HDM-D` supported only single-host + accelerator bias-flipping), leaving multi-host CXL 2.0 pools **software-coherent** (requiring explicit `clwb`/`clflushopt` + `sfence` on *both* writer and reader!). CXL 3.0 introduced **`HDM-DB` (Device-Coherent with Back-Invalidate)** and the **`BISnp` (Back-Invalidate Snoop)** channel, allowing a Type-3 pool or switch directory to proactively invalidate cached copies on peer hosts.

Two critical limitations constrain CXL hardware coherence:
1. **Prose Specification Bugs (`Tan, Donaldson, Wickerson`, ASPLOS 2025, `arXiv:2410.15908v2`, `DOI:10.1145/3676641.3715999`):** Mechanizing the official English `CXL.cache` protocol specification in **Isabelle/HOL** (proving Single-Writer-Multiple-Reader coherence and `"Snoop-pushes-GO"` ordering across tens of thousands of lemmas) uncovered multiple unclear, ambiguous, and inaccurate passages in the CXL standard—several of which could induce hardware incoherence if implemented literally, with nearly all proposed fixes tentatively accepted by the CXL Consortium.
2. **Directory Capacity Evictions and Dead-Host `BISnp` Stalls:** Switch snoop directories have finite SRAM; capacity evictions generate spurious `BISnp` back-invalidations under contention, and—critically—the CXL 3.0 specification **does not handle a host CPU crashing while holding a line in Modified (`M`) state**, causing pending `BISnp` snoops either to hang surviving hosts or drop dirty writes silently.

#### 1.3 Dynamic Capacity Devices (`DCD`), Extent Revocation, and Link vs. End-to-End Security (`CXL IDE`)
CXL 3.0/3.1 **`DCD` (Dynamic Capacity Devices)** allow a central **Fabric Manager (`FM`)** to grant and revoke DPA extents dynamically across multi-tenant hosts. If an extent lease is forcibly revoked while a host process or DMA engine holds active PTEs or Rust `&'a [u8]` borrows, subsequent loads fault synchronously (`#MC`/unmapped) or leak cross-tenant bytes if scrubbing lags reallocation. Meanwhile, **`CXL IDE` (Integrity and Data Encryption)** applies AES-GCM **link-by-link** on external cables—it does **not** by itself provide end-to-end confidentiality through an untrusted CXL switch or compromised Fabric Manager, nor prevent cross-tenant aliasing caused by misprogrammed `HDM` decoders without TEE extensions (`TDX Connect` / `SEV-TIO` / `ARM CCA RME-DA`).

---

### 2. Partial-Failure Synchronous Loads (`Poison`/`Viral`, `SRAR` `#MC`, Linux `copy_mc_64.S`) vs. LLVM `dereferenceable(N)` Hoisting

Basis: normative + source + execution

#### 2.1 Hardware Poison Propagation and Linux Kernel vs. Userspace Recovery Asymmetry
When a remote CXL memory blade encounters an uncorrectable ECC error or mid-transaction link failure, `CXL.mem` tags the 64-byte response flit with a **Data Poison** bit (or escalates to fabric-wide **`Viral`** containment to stop silent corruption propagation on uncontained protocol violations). Consuming a poisoned cache line on an x86-64 CPU raises a synchronous **Machine Check Exception (`#MC`)** classified under Intel MCA Recovery as **`SRAR` (Software Recoverable Action Required)** (as opposed to background unconsumed **`SRAO` — Action Optional**; ARM RAS raises a **Synchronous External Abort `SEA`**).

Direct inspection of `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) exposes a sharp kernel-vs.-userspace recovery chasm:
- **Userspace (`mm/memory-failure.c`, lines 332–341):** Linux marks the entire 4 KB page (or 2 MB hugepage—a 64×–32,768× blast-radius amplification for a 64-byte CXL cache line!) as `hwpoison`, unmaps it, and terminates or signals the consuming thread via:
  ```c
  if ((flags & MF_ACTION_REQUIRED) && (t == current))
      ret = force_sig_mceerr(BUS_MCEERR_AR, (void __user *)tk->addr, addr_lsb);
  ```
  In C++ and Rust, catching `SIGBUS(BUS_MCEERR_AR)` with `siglongjmp` bypasses RAII destructors (`Drop`), leaves mutexes locked, corrupts thread-local invariants, and is Undefined Behavior. Consequently, **one poisoned 64-byte remote cache line kills the entire userspace process**.
- **Kernel Mode (`arch/x86/lib/copy_mc_64.S`, lines 1–165):** By contrast, the Linux kernel recovers synchronously from `SRAR` `#MC` without panicking by registering exact faulting instruction PCs in its kernel exception table (`__ex_table`) with type **`EX_TYPE_DEFAULT_MCE_SAFE`**:
  - `copy_mc_fragile` avoids fast-string (`rep movsb`) instructions and cacheline-straddling poison reads on quirky CPUs, tagging `.L_read_leading_bytes`, `.L_read_words` (`movq (%rsi), %r8`), and `.L_read_trailing_bytes` via `_ASM_EXTABLE_TYPE(..., EX_TYPE_DEFAULT_MCE_SAFE)`.
  - `copy_mc_enhanced_fast_string` executes `rep movsb` tagged with `_ASM_EXTABLE_TYPE(.L_copy, .E_copy, EX_TYPE_DEFAULT_MCE_SAFE)`, returning remaining uncopied bytes `%rcx` in `%rax` cleanly on `#MC`.
  No standardized zero-overhead ABI currently exposes per-instruction `EX_TYPE_DEFAULT_MCE_SAFE` fixup tables to userspace Rust/C++ compilers.

#### 2.2 Normative LLVM `dereferenceable(N)` and Empirical `rustc` Speculative Hoisting Proof
Basis: normative (`llvm/llvm-project` @ `b86056e175f63cb99c5ca7c4139244c60b1056aa`) + execution (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`)

Even if a userspace CXL runtime installs a fault guard (`if blade_ok { val = *ptr; }`), Rust's `&T` reference contract and LLVM's optimization passes **actively destroy the guard**:

1. **Normative LLVM IR Specification (`llvm/docs/LangRef.md`, lines 1650–1655):**
   > "`dereferenceable(<n>)`: This indicates that the parameter or return pointer is dereferenceable. This attribute may only be applied to pointer-typed parameters. **A pointer that is dereferenceable can be loaded from speculatively without a risk of trapping.**"
2. **LLVM Speculation Predicate (`llvm/lib/Analysis/ValueTracking.cpp`, lines 7935–7944):**
   ```cpp
   const LoadInst *LI = dyn_cast<LoadInst>(Inst);
   if (!LI)
     return false;
   if (mustSuppressSpeculation(*LI))
     return false;
   const DataLayout &DL = LI->getDataLayout();
   return isDereferenceableAndAlignedPointer(
       LI->getPointerOperand(), LI->getType(), LI->getAlign(),
       SimplifyQuery(DL, TLI, DT, AC, CtxI));
   ```
3. **Empirical Verification With `rustc 1.98.0-nightly -O` (`probe_cxl_hoist.rs`):** Compiling four variants of a guarded load with `rustc -O --emit=llvm-ir` and `--emit=asm` on `x86_64-unknown-linux-gnu` yields an unambiguous contrast:
   - **`guarded_ref_load(blade_ok: bool, p: &u64) -> u64`** receives `dereferenceable(8)` on `%p`. LLVM `SimplifyCFG` eliminates the branch completely and hoists `%0 = load i64, ptr %p, align 8` unconditionally before `select i1 %blade_ok, i64 %0, i64 0`.
   - **`loop_guarded_ref_load(n: usize, blade_ok: bool, p: &u64) -> u64`** (`for _ in 0..n { if blade_ok { acc = acc.wrapping_add(*p); } }`) hoists `%_5 = load i64, ptr %p, align 8` unconditionally outside **both** the `n` loop and the `blade_ok` branch in LLVM IR—and lowers on `x86-64` to:
     ```asm
     loop_guarded_ref_load:
         xorl    %eax, %eax
         testl   %esi, %esi
         cmovneq (%rdx), %rax
         imulq   %rdi, %rax
         retq
     ```
     Per the Intel 64 SDM (`CMOVcc`), a memory-operand **`cmovneq (%rdx), %rax` unconditionally performs the architectural memory read from `(%rdx)` regardless of whether `%esi` (`blade_ok`) is zero**—and executes even when `%rdi` (`n`) is `0`! Thus passing a CXL-backed address as a safe Rust `&u64` causes the CPU to retire an architectural load of a poisoned CXL cache line even on a dead blade with zero loop iterations, raising a fatal `SRAR` `#MC`.
   - **`guarded_raw_load(blade_ok: bool, p: *const u64) -> u64`** omits `dereferenceable(8)` in LLVM IR, preserving `br i1 %blade_ok, label %bb1, label %bb3` in IR and `testl %edi, %edi; je .LBB0_1; movq (%rsi), %rax` in x86-64 assembly. **`guarded_volatile_load`** additionally emits `load volatile i64`, suppressing both hoisting and load coalescing/widening.

*Compiler IR implication (derived):* Supporting fallible disaggregated memory safely requires splitting LLVM's monolithic `dereferenceable(N)` attribute into orthogonal **`inbounds(N)`** (spatial allocation provenance) and **`infallible_load`** (guaranteed trap-free local DRAM), blocking `LICM`, `SimplifyCFG`, and `CMOV` memory folding whenever a pointer carries a `LoadFault` effect.

---

### 3. Asymmetric Partial-Host Crash Semantics (`CXL0`, `CXLMC`) and Hardware/Software Recovery (`DIKTAMO`, `Lupin`, `CXL-SHM`, `Cxlalloc`)

Basis: normative + source + execution + derived

#### 3.1 "Barely Distributed and Almost Persistent": The `CXL0` Operational Model
Yi Xu, Suyash Mahar, Ziheng Liu, Mingyao Shen, and Steven Swanson (`arXiv:2405.19626v2`, 2024) established that CXL shared memory occupies a distinct failure regime between volatile DRAM and persistent NVM: **processes/hosts fail independently while shared CXL memory survives, yet rack power loss wipes the pool**. Gal Assa, Moritz Lumme, Lucas Bürgi, Michal Friedman, and Ori Lahav (`CXL0`, ASPLOS 2026, `arXiv:2407.16300v3`) formalized the first rigorous operational concurrent programming model for disaggregated CXL memory under partial host crashes, together with a general algorithmic transformation lifting linearizable concurrent algorithms to partial-crash durability.

Why do algorithms verified under single-host x86-TSO, C++20 Release-Acquire, and even full-system-crash `Px86` Durable Linearizability **fail silently under `CXL0`**? Because in `Px86`, a crash halts *all* threads simultaneously and runs a sequential recovery pass before any new read executes; in `CXL0`, **surviving Host B reads memory concurrently while Host A's dirty private cache vanishes asynchronously**.

Running our exhaustive operational state-space explorer `/tmp/probe_cxl0_partial_crash.py` (`Basis: execution`, preserved in **Evidence**) models Host A executing `store(val=42); store(ready=1)` and surviving Host B reading `if ready == 1 { read(val) }` over a CXL 3.0 coherent fabric with private write-back caches:

```text
[3B-CXL0-PlainRA] states=32, causal_violations=2, minimal_trace=['A:store(val=42)', 'A:store(ready=1)', 'B:load(ready)==1', 'CRASH(HostA)', 'B:load(val)==0']
[3B-CXL0-ClwbPublish] states=26, causal_violations=0
```

Two distinct causal-violation traces appear under plain Release-Acquire (`causal_violations=2`):
1. **Live-snoop-then-crash:** Host B reads `ready == 1` via CXL 3.0 coherent snoop directly from Host A's dirty L1/L3 cache while Host A is alive; Host A immediately crashes, erasing its dirty `val = 42` cache line; Host B then reads `val == 0` from the CXL pool!
2. **Out-of-order cache eviction:** Hardware evicts `ready = 1` from Host A's L3 cache to the CXL pool before `val = 42`, Host A crashes, and Host B reads `ready == 1` and `val == 0` straight from the pool!
Inserting explicit flush-before-publish (`clwb(&val); sfence()` before `store(ready=1)`) eliminates all violations across the entire reachable state space (`causal_violations=0`).

#### 3.2 `CXLMC`, `DIKTAMO` (`ReCXL`), `Lupin`, `CXL-SHM`, and `Cxlalloc`
| System & Venue | Layer & Core Mechanism | Failure Class Addressed | Residual Limitation / Verification Gap |
|---|---|---|---|
| **`CXLMC`** (Guo, Truong, Demsky, **ASPLOS 2026**, `DOI:10.1145/3779212.3790150`; `uci-plrg/cxlmc` @ `1391bcbc`) | LLVM instrumentation pass intercepting shared loads, stores, atomics, fences, `clwb`/`clflushopt` to systematically model-check cache-eviction subsets and partial host crashes | Crash-consistency & missing-flush concurrency bugs in C/C++ CXL shared-memory programs | Exponential eviction state space without DPOR/region framing; blind to uninstrumented precompiled libraries, inline assembly, and cross-language FFI |
| **`DIKTAMO`** (evolved from `ReCXL`; Psistakis et al., **MICRO 2026**, `arXiv:2602.08271v2`) | Hardware coherence extension propagating write transactions to peer **Replica** nodes' hardware **Logging Units**, dumping compressed logs to CXL memory; replays logs on CPU death to restore directories + memory (`27%` slowdown w/ 2 replicas, `30%` w/ 3 replicas; `2.82x` faster than write-through) | Dirty `M`-state cache loss and `BISnp` directory corruption when a host CPU dies under CXL 3.0 hardware coherence | **Hardware cache-line recovery != software critical-section atomicity:** dead CPU's register file, stack, and held mutexes vanish, leaving multi-word software invariants half-updated and locks orphaned |
| **`CXL-SHM`** (Zhang et al., **SOSP 2023**, `DOI:10.1145/3600006.3613135`; `madsys-dev/sosp-paper19-ae` @ `0ae5ed7d`) | Non-blocking **era-based automatic reference counting** evaluated on Intel Sapphire Rapids + Agilex R-Tile FPGA (`devdax` mode) | Shared heap memory leaks, double-frees, and wild pointers when clients crash mid-allocation or mid-refcount update | Reference counting alone does not reclaim cyclic shared graphs; requires era fencing against slow zombie hosts |
| **`Lupin`** (Zhu, Ni, Huang, Sun, Jia, Kim, Witchel, **DIMES @ SOSP 2024**, `DOI:10.1145/3698783.3699377`) | Kernel modifications + fabric-manager failure detection + user-level pod libraries | Multi-host CXL pod survival, dead-host resource reclamation, and process rejoining without whole-pod reboot | Relies on accurate failure-detector fencing to stop grey-failed ("zombie") hosts from writing after reclamation |
| **`Cxlalloc`** (Ni et al., **ASPLOS 2026**, `DOI:10.1145/3779212.3790149`; `nwtnni/cxlalloc` @ `eba659a2`) | Lock-free/recoverable CXL pod allocator (`cxlalloc` core + C FFI `cxlalloc-static` + Rust `cxlalloc-global`) | Safe multi-process CXL heap allocation and fast recovery | Source `README.md` notes an open API design seam: transactional link/unlink entangles allocator & app pointer layouts, pushing toward a detectable API (`fn detect_allocate(NonNull<T>) -> bool`) |

---

### 4. Cross-Host Virtual-Address Aliasing and Self-Relative Pointer Provenance

Basis: documentation + derived

In multi-host CXL pools, each host OS independently programs its own **`HDM` decoders** (`HPA -> DPA` interleaving) and independently applies process **ASLR** (`VA -> HPA`). Consequently, the exact same shared object resides at different virtual addresses across hosts (`0x7f12_0000_1000` on Host A vs. `0x7fa8_0040_1000` on Host B):
1. **Absolute Pointer & Vtable Invalidation:** Storing any native C/C++/Rust raw pointer (`T*`, `&T`, `Box<T>`), function pointer, or `dyn Trait` / C++ `virtual` vtable pointer inside shared CXL memory immediately causes segfaults or silent cross-host memory corruption when dereferenced by Host B—and fails completely across heterogeneous ISA hosts (x86-64 + ARM64 sharing one pool).
2. **Self-Relative Pointer (`offset_ptr` / `rkyv::RelPtr`) Provenance Breakdown:** Computing a target pointer by adding a stored signed byte offset to the address of the pointer field itself (`(self as *const _ as isize).wrapping_add(self.offset)`) avoids absolute VAs, yet violates LLVM `getelementptr inbounds` and Rust Stacked/Tree Borrows intra-object provenance because the derived pointer exits the allocation subobject of `&self` into an unrelated sibling object inside the shared pool. Sound optimization requires deriving provenance from a **region-wide base handle** (`region_base.byte_offset(rel_offset)`) rather than `&self`.
3. **Standard Rust/C++ Synchronization Unsoundness Across CXL Pods:** Rust's binary `Send`/`Sync` auto-traits assume one shared virtual address space, one coherence domain, and one crash domain. Placing standard `std::sync::Mutex<T>` (only poisons on in-process panic unwind, never on remote-host power loss—nor does POSIX `PTHREAD_MUTEX_ROBUST` work across separate Linux kernels!), `std::sync::Arc<T>` (leaks permanently on host crash), or `Box<T>` (absolute VA) into shared CXL memory silently breaks safety even with zero `unsafe` blocks in user logic.

---

### 5. PGAS and Logical-Region Languages (`Legion`/`Regent`, `Chapel`, `UPC++`) vs. C++/Rust References

Basis: normative + source + derived

| Dimension | Rust / C++ (`&T`, `T*`, `Atomic`) | `Legion` / `Regent` (`StanfordLegion/legion` @ `aea587e1`) | `Chapel` (`chapel-lang/chapel` @ `732cf95e`) | `UPC++` (`BerkeleyLab/upcxx` @ `824c7c55`) |
|---|---|---|---|---|
| **Address / Locality Abstraction** | Flat 64-bit host-local VA; locality invisible to types | **Logical Regions** (Index Space × Field Space), hierarchically partitioned; placement delegated to external **Mapper** | First-class **`locale`** type (`Locales[0..N-1]`) + 128-bit **wide pointers** `(locale_id, local_addr)` + `dmapped` Domain Maps | Explicit **`upcxx::global_ptr<T, Kind>`** `(rank, raw_ptr)`; `.local()` permitted only after `is_local()` check |
| **Remote Access Syntax & Cost Visibility** | Identical `*p` (silent 600 ns CXL cliff) | Deferred task launches over regions; runtime `Realm` schedules async DMA/copies | Transparent `A[i]` (risks silent 100× remote-GET cliff unless enclosed in `local { ... }` check or `on loc do`) | **Bans naked `*gptr`:** forces explicit async `upcxx::rget(gptr)` / `rput(val, gptr)` returning `upcxx::future<T>` |
| **Aliasing, Privileges & Concurrency** | Binary `&T` (shared read) vs. `&mut T` (exclusive write); no reduction borrow | Explicit field-level bitmask **`legion_privilege_mode_t`** (`READ_ONLY`, `WRITE_PRIV`, **`REDUCE`**, `DISCARD_INPUT/OUTPUT`) + **`legion_coherence_property_t`** (`EXCLUSIVE`, `ATOMIC`, `SIMULTANEOUS`, `RELAXED`, `COLLECTIVE_*`) | `on`-clause computation shipping (`on A[i] do`) + task-parallel `coforall` / `forall` | One-sided RMA + active-message `upcxx::rpc(rank, fn, ...)` + thread-affine **`upcxx::persona`** & `persona_scope` (`lpc()`) |
| **Partial-Failure Model** | Infallible loads (`dereferenceable`); whole-process `SIGBUS` death | Fail-stop HPC job + checkpoint/restart | Fail-stop HPC job (single dead locale aborts job) | Fail-stop HPC job (`future<T>` has no remote-fault error channel) |
| **FFI & Verification Friction** | Zero-overhead C ABI locally; completely unsound across CXL pods & partial crashes | Calling C/Rust requires pinning a concrete AoS/SoA physical instance, stalling deferred pipelining; dynamic dependence overhead on irregular pointer graphs | Wide pointers break 64-bit C ABI (require `localSlice` copy); FFI defeats compiler wide-pointer narrowing | Blocking C/Rust syscalls or `std::mutex` inside a `persona_scope` starve `upcxx::progress()` and deadlock cluster; `rput` source buffer lifetimes unchecked by C++ types |

#### Primary Source Details Verified Across the Three PGAS / Region Runtimes
1. **`Legion` / `Regent` (`runtime/legion/api/config.h`, lines 950–1029):** Directly defines the privilege algebra (`LEGION_NO_ACCESS = 0x0`, `LEGION_READ_ONLY = 0x1`, `LEGION_WRITE_PRIV = 0x2`, **`LEGION_REDUCE = 0x4`**, `LEGION_READ_WRITE = 0x7`, `LEGION_DISCARD_INPUT_MASK = 0x10000000`, `LEGION_DISCARD_OUTPUT_MASK = 0x20000000`) orthogonal to coherence (`LEGION_EXCLUSIVE = 0x0`, `LEGION_ATOMIC = 0x1`, `LEGION_SIMULTANEOUS = 0x2`, `LEGION_RELAXED = 0x3`, plus `LEGION_COLLECTIVE_MASK = 0x10000000`). The **`REDUCE`** privilege is uniquely powerful for disaggregated fabrics: declaring associative-commutative `reduces+(R.f)` eliminates cross-node cache coherence ping-pong by letting each host accumulate into a private local buffer before tree-reducing once.
2. **`Chapel` (`doc/rst/language/spec/locales.rst`, lines 1–75):** Models each hardware compute+memory unit as a `locale` value (default `Locales[0]`) and migrates tasks to data via **`on`-statements** rather than dragging remote data across the interconnect. However, transparent remote indexing hides fabric latency until runtime `local { ... }` assertions trap or compiler wide-pointer narrowing succeeds.
3. **`UPC++` (`src/global_ptr.hpp`, lines 39–200; `src/persona.hpp`, lines 37–160, 418–421):** Parameterizes `global_ptr<T, memory_kind Kind = memory_kind::host>` by memory kind (distinguishing host vs. GPU/device memory and asserting `Kind == memory_kind::host` in `local()`), forbids direct remote dereference in favor of composable futures (`rget`/`rput`), and isolates multi-threaded completion callbacks through zero-initialized thread-local `persona` / `persona_scope` handles (`persona::lpc(Fn&&)`). Its key FFI vulnerability is **progress starvation**: any blocking foreign call while holding an active `persona` prevents `upcxx::progress()` from servicing incoming RPCs.

## Boundaries

- **Physical CXL 3.0 `HDM-DB` / `DCD` hardware execution (`not examined`):** No physical multi-host CXL 3.0 switched fabric or `DCD` blade hardware was available on the observation host; findings on `HDM-DB` (`BISnp`), `DCD`, `G-FAM`, and `DIKTAMO` rely on specifications, peer-reviewed evaluations, and formal models (`arXiv:2410.15908v2`, `arXiv:2407.16300v3`, `arXiv:2602.08271v2`).
- **ARM64 `SEA` and RISC-V RAS codegen (`not examined`):** The live `rustc 1.98.0-nightly` speculative load-hoisting probe was compiled and verified on `x86_64-unknown-linux-gnu` (`cmovneq (%rdx), %rax`); equivalent `aarch64` (`csel`/hoisted `ldr`) and `riscv64` backend lowerings were not executed directly, though the frontend LLVM IR hoisting (`dereferenceable(8)`) is target-independent.
- **Full source audit of `uci-plrg/cxlmc`, `madsys-dev/sosp-paper19-ae`, and `nwtnni/cxlalloc` implementation files (`not examined`):** Exact HEAD commits and READMEs/DOIs were inspected directly, while individual C++/LLVM-pass and Rust allocator implementation files were not audited line by line.
- **Userspace MCE fixup ABI standardization (`unknown`):** No upstream Linux kernel syscall or ELF section ABI yet provides safe, portable userspace `EX_TYPE_DEFAULT_MCE_SAFE` per-PC recovery handlers equivalent to kernel `copy_mc_64.S` without `SIGBUS` overhead.
- **Scope boundary (`known not to apply`):** CXL 3.0 hardware cache-coherence guarantees (`HDM-DB`/`BISnp`) do **not** apply to CXL 2.0 multi-host pooled memory deployments (which require explicit software cache flushing and invalidation on both writer and reader). Conversely, `DIKTAMO` hardware cache-line recovery does **not** recover application-level mutexes or multi-word critical sections interrupted by a CPU crash.
- **Stronger conclusion not established:** Observing that `guarded_ref_load` happened to emit a conditional branch (`testl %edi, %edi; je`) in `x86-64` assembly despite LLVM IR hoisting does **not** make `&u64` safe over fallible CXL memory: as `loop_guarded_ref_load` demonstrates on the exact same compiler invocation, LLVM IR `dereferenceable(8)` legally authorizes the x86 backend to emit unconditional memory-operand `cmovneq (%rdx), %rax` loads that execute even when the guard is `false`.

## Evidence

### Normative Specifications and Peer-Reviewed Primary Literature
- **CXL Specification:** Compute Express Link Consortium, *CXL 2.0 / 3.0 / 3.1 Specification* (`CXL.mem`, `CXL.cache`, `HDM-DB`/`BISnp`, `DCD`, `G-FAM`, `Data Poison`, `Viral`, `CXL IDE`).
- **Formalising CXL Cache Coherence:** C. Tan, A. F. Donaldson, J. Wickerson, ASPLOS 2025 (`arXiv:2410.15908v2`, `DOI:10.1145/3676641.3715999`).
- **Barely Distributed and Almost Persistent:** Y. Xu, S. Mahar, Z. Liu, M. Shen, S. Swanson, 2024 (`arXiv:2405.19626v2`, `DOI:10.48550/arXiv.2405.19626`).
- **CXL0:** G. Assa, M. Lumme, L. Bürgi, M. Friedman, O. Lahav, *"A Programming Model for Disaggregated Memory over CXL"*, ASPLOS 2026 (`arXiv:2407.16300v3`, `DOI:10.48550/arXiv.2407.16300`).
- **CXLMC:** Y. (Simon) Guo, C. Truong, B. Demsky, *"CXLMC: Model Checking CXL Shared Memory Programs"*, ASPLOS 2026 (`DOI:10.1145/3779212.3790150`).
- **DIKTAMO (evolved from ReCXL):** A. Psistakis, B. Ocalan, C. Alverti, F. Chaix, R. Alagappan, J. Torrellas, *"DIKTAMO: Extending CXL for Resilience to CPU Failures"*, 59th IEEE/ACM MICRO 2026 (`arXiv:2602.08271v2`).
- **Lupin:** Z. Zhu, N. Ni, Y. Huang, Y. Sun, Z. Jia, N. S. Kim, E. Witchel, *"Lupin: Tolerating Partial Failures in a CXL Pod"*, DIMES @ SOSP 2024 (`DOI:10.1145/3698783.3699377`).
- **Cxlalloc:** *"Cxlalloc: Safe and Efficient Memory Allocation for a CXL Pod"*, ASPLOS 2026 (`DOI:10.1145/3779212.3790149`).
- **CXL-SHM:** M. Zhang, T. Ma, J. Hua, Z. Liu, K. Chen, N. Ding, F. Du, J. Jiang, T. Ma, Y. Wu, *"Partial Failure Resilient Memory Management System for (CXL-based) Distributed Shared Memory"*, SOSP 2023 (`DOI:10.1145/3600006.3613135`).
- **CXL Systems Characterizations:** `DirectCXL` (Gouk et al., USENIX ATC 2022), `Pond` (Li et al., ASPLOS 2023), `Demystifying CXL` (Sun et al., MICRO 2023), `Memstrata` (Zhong et al., OSDI 2024), `HydraRPC` (Ma et al., USENIX ATC 2024).
- **PGAS / Logical Regions:** `Legion` (Bauer et al., SC 2012, `DOI:10.1109/SC.2012.71`), `Regent` (Slaughter et al., SC 2015, `DOI:10.1145/2807591.2807629`), `Chapel` (Chamberlain et al., *IJHPCA* 2007, `DOI:10.1177/1094342007078442`), `UPC++` (Bachan et al., IPDPS 2019, `DOI:10.25344/S4V88H`).

### Pinned Upstream Source Inspections (Observed 2026-11-19)
- **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**:
  - `arch/x86/lib/copy_mc_64.S` lines 1–165 (`copy_mc_fragile`, `copy_mc_enhanced_fast_string`, `_ASM_EXTABLE_TYPE(..., EX_TYPE_DEFAULT_MCE_SAFE)`).
  - `mm/memory-failure.c` lines 331–341 (`MF_ACTION_REQUIRED` -> `force_sig_mceerr(BUS_MCEERR_AR, ...)`).
- **`llvm/llvm-project` @ `b86056e175f63cb99c5ca7c4139244c60b1056aa`**:
  - `llvm/docs/LangRef.md` lines 1650–1684 (`dereferenceable(<n>)` speculative non-trapping load contract).
  - `llvm/lib/Analysis/ValueTracking.cpp` lines 7935–7944 (`isSafeToSpeculativelyExecuteWithOpcode` `Instruction::Load` returning `isDereferenceableAndAlignedPointer(...)`).
- **`StanfordLegion/legion` @ `aea587e157abff12f7d089c81f29cd3a8b993a2b`**:
  - `runtime/legion/api/config.h` lines 950–1029 (`legion_privilege_mode_t`, `legion_coherence_property_t`).
- **`chapel-lang/chapel` @ `732cf95e1d870063b5be878a8ba9f7ed0642645f`**:
  - `doc/rst/language/spec/locales.rst` lines 1–75 (`locale` type, `Locales[0]`, `on`-statement migration).
- **`BerkeleyLab/upcxx` @ `824c7c5521e6b56c564eb74e75fb7ff7b084fbb5`**:
  - `src/global_ptr.hpp` lines 39–200 (`global_ptr<T, Kind>`, `is_local()`, `local()` host-kind assertion).
  - `src/persona.hpp` lines 37–160, 418–421 (`persona` thread-local constraints, `persona_scope`, `persona::lpc`).
- **CXL Artifact Repositories Resolved 2026-11-19:** `uci-plrg/cxlmc` @ `1391bcbc81bc30835994105127f1ffe9a806f0ba`, `nwtnni/cxlalloc` @ `eba659a27ebd580cc72069dfb0bce625ef0580ca`, `madsys-dev/sosp-paper19-ae` @ `0ae5ed7d073436eeaad331c05971874cc29a9889`.

### Preserved Standalone Execution Probes (Observed 2026-11-19)

#### Probe 3A: `rustc` LLVM IR & x86-64 Speculative Load Hoisting (`probe_cxl_hoist.rs`)
Commands (`rustc 1.98.0-nightly (14210df0e 2026-05-31)` on `x86_64-unknown-linux-gnu`):
```bash
rustc -O --emit=llvm-ir /tmp/probe_cxl_hoist.rs -o /tmp/probe_cxl_hoist.ll
rustc -O --emit=asm /tmp/probe_cxl_hoist.rs -o /tmp/probe_cxl_hoist.s
```
Source (`/tmp/probe_cxl_hoist.rs`):
```rust
#![crate_type = "lib"]

#[no_mangle]
pub fn guarded_ref_load(blade_ok: bool, p: &u64) -> u64 {
    if blade_ok { *p } else { 0 }
}

#[no_mangle]
pub unsafe fn guarded_raw_load(blade_ok: bool, p: *const u64) -> u64 {
    if blade_ok { *p } else { 0 }
}

#[no_mangle]
pub unsafe fn guarded_volatile_load(blade_ok: bool, p: *const u64) -> u64 {
    if blade_ok { p.read_volatile() } else { 0 }
}

#[no_mangle]
pub fn loop_guarded_ref_load(n: usize, blade_ok: bool, p: &u64) -> u64 {
    let mut acc = 0u64;
    for _ in 0..n {
        if blade_ok {
            acc = acc.wrapping_add(*p);
        }
    }
    acc
}
```
Observed LLVM IR excerpts (`/tmp/probe_cxl_hoist.ll`):
```llvm
define noundef i64 @guarded_raw_load(i1 noundef zeroext %blade_ok, ptr noundef readonly captures(none) %p) unnamed_addr #0 {
start:
  br i1 %blade_ok, label %bb1, label %bb3
bb1:
  %0 = load i64, ptr %p, align 8, !noundef !4
  br label %bb3
bb3:
  %_0.sroa.0.0 = phi i64 [ %0, %bb1 ], [ 0, %start ]
  ret i64 %_0.sroa.0.0
}

define noundef i64 @guarded_ref_load(i1 noundef zeroext %blade_ok, ptr noalias noundef readonly align 8 captures(none) dereferenceable(8) %p) unnamed_addr #0 {
start:
  %0 = load i64, ptr %p, align 8
  %_0.sroa.0.0 = select i1 %blade_ok, i64 %0, i64 0
  ret i64 %_0.sroa.0.0
}

define noundef i64 @loop_guarded_ref_load(i64 noundef %n, i1 noundef zeroext %blade_ok, ptr noalias noundef readonly align 8 captures(none) dereferenceable(8) %p) unnamed_addr #0 {
start:
  %_5 = load i64, ptr %p, align 8
  %_5.fr = freeze i64 %_5
  %_4 = select i1 %blade_ok, i64 %_5.fr, i64 0
  %0 = mul i64 %_4, %n
  ret i64 %0
}
```
Observed `x86-64` assembly excerpt (`/tmp/probe_cxl_hoist.s`) proving unconditional architectural memory access via memory-operand `cmovneq`:
```asm
loop_guarded_ref_load:
	.cfi_startproc
	xorl	%eax, %eax
	testl	%esi, %esi
	cmovneq	(%rdx), %rax
	imulq	%rdi, %rax
	retq
```

#### Probe 3B: `CXL0` Asymmetric Partial-Host Crash Operational Model Checker (`probe_cxl0_partial_crash.py`)
Run `python3 /tmp/probe_cxl0_partial_crash.py`:
```python
#!/usr/bin/env python3
from collections import deque

def explore(with_clwb_publish: bool):
    init = (0, True, None, None, 0, 0, False, None)
    seen = {init}
    q = deque([(init, [])])
    violations = []
    while q:
        st, trace = q.popleft()
        pcA, aliveA, c_val, c_rdy, p_val, p_rdy, b_rdy, b_val = st
        if b_rdy and b_val == 0:
            violations.append((trace, st))
            continue
        nexts = []
        if aliveA:
            if not with_clwb_publish:
                if pcA == 0:
                    nexts.append(((1, True, 42, c_rdy, p_val, p_rdy, b_rdy, b_val), "A:store(val=42)"))
                elif pcA == 1:
                    nexts.append(((2, True, c_val, 1, p_val, p_rdy, b_rdy, b_val), "A:store(ready=1)"))
            else:
                if pcA == 0:
                    nexts.append(((1, True, 42, c_rdy, p_val, p_rdy, b_rdy, b_val), "A:store(val=42)"))
                elif pcA == 1:
                    nv = c_val if c_val is not None else p_val
                    nexts.append(((2, True, None, c_rdy, nv, p_rdy, b_rdy, b_val), "A:clwb(val)+sfence"))
                elif pcA == 2:
                    nexts.append(((3, True, c_val, 1, p_val, p_rdy, b_rdy, b_val), "A:store(ready=1)"))
                elif pcA == 3:
                    nr = c_rdy if c_rdy is not None else p_rdy
                    nexts.append(((4, True, c_val, None, p_val, nr, b_rdy, b_val), "A:clwb(ready)+sfence"))
            if c_val is not None:
                nexts.append(((pcA, True, None, c_rdy, c_val, p_rdy, b_rdy, b_val), "HW:evict(val->pool)"))
            if c_rdy is not None:
                nexts.append(((pcA, True, c_val, None, p_val, c_rdy, b_rdy, b_val), "HW:evict(ready->pool)"))
            nexts.append(((pcA, False, None, None, p_val, p_rdy, b_rdy, b_val), "CRASH(HostA)"))
        vis_rdy = c_rdy if (aliveA and c_rdy is not None) else p_rdy
        vis_val = c_val if (aliveA and c_val is not None) else p_val
        if not b_rdy and vis_rdy == 1:
            nexts.append(((pcA, aliveA, c_val, c_rdy, p_val, p_rdy, True, None), "B:load(ready)==1"))
        if b_rdy and b_val is None:
            nexts.append(((pcA, aliveA, c_val, c_rdy, p_val, p_rdy, True, vis_val), f"B:load(val)=={vis_val}"))
        for nst, act in nexts:
            if nst not in seen:
                seen.add(nst)
                q.append((nst, trace + [act]))
    return len(seen), violations

s_plain, v_plain = explore(False)
s_flushed, v_flushed = explore(True)
print(f"[3B-CXL0-PlainRA] states={s_plain}, causal_violations={len(v_plain)}, minimal_trace={v_plain[0][0] if v_plain else None}")
print(f"[3B-CXL0-ClwbPublish] states={s_flushed}, causal_violations={len(v_flushed)}")
```
Observed output:
```text
[3B-CXL0-PlainRA] states=32, causal_violations=2, minimal_trace=['A:store(val=42)', 'A:store(ready=1)', 'B:load(ready)==1', 'CRASH(HostA)', 'B:load(val)==0']
[3B-CXL0-ClwbPublish] states=26, causal_violations=0
```

## Revalidation

1. **LLVM `dereferenceable` & `rustc` hoisting check:** Re-run `rustc -O --emit=llvm-ir` and `--emit=asm` on Probe 3A (`/tmp/probe_cxl_hoist.rs`) on newer `rustc`/LLVM releases, and diff `llvm/docs/LangRef.md` (`dereferenceable(<n>)`) and `llvm/lib/Analysis/ValueTracking.cpp` (`isSafeToSpeculativelyExecuteWithOpcode`) in `llvm/llvm-project` against `b86056e175f63cb99c5ca7c4139244c60b1056aa` to check whether LLVM introduces an orthogonal fallible-load attribute or suppresses memory-operand `CMOVcc` folding.
2. **Linux kernel MCE recovery & CXL poison path:** Diff `arch/x86/lib/copy_mc_64.S` (`EX_TYPE_DEFAULT_MCE_SAFE`), `mm/memory-failure.c` (`BUS_MCEERR_AR`), and `drivers/cxl/` in `torvalds/linux` against `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to check for sub-page (64-byte) CXL poison containment or userspace MCE fixup table APIs.
3. **PGAS privilege & pointer contracts:** Diff `runtime/legion/api/config.h` in `StanfordLegion/legion` (`aea587e157abff12f7d089c81f29cd3a8b993a2b`) and `src/global_ptr.hpp` / `src/persona.hpp` in `BerkeleyLab/upcxx` (`824c7c5521e6b56c564eb74e75fb7ff7b084fbb5`) to check whether fault-tolerant/partial-failure error types (`future<Result<T, RemoteFault>>`) or CXL memory kinds are added.
4. **Re-run `CXL0` operational model check:** Execute `python3 /tmp/probe_cxl0_partial_crash.py` to confirm the minimal partial-host-crash violation trace and `clwb+sfence` elimination proof.
