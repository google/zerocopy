# Rust Operating System Isolation Boundaries, Safe-Interface Authority Choke Points, Ownership Invariants, and Compatibility-Constrained Rewrites

## Summary

Across modern Rust operating systems and mixed-language kernel substrates—**Tock**, **Asterinas**, **RedLeaf**, **Rust-for-Linux**, **Theseus**, **zCore**, and **reL4**—"isolation" and "safe interface" name distinct, non-interchangeable properties that must never be collapsed into a single claim:
1. **Memory Safety / Absence of Undefined Behavior (UB)**: Whether untrusted extension or service code can corrupt the language abstract machine, manufacture invalid references, or trigger data races.
2. **Authority Confinement**: Whether a component can invoke a privileged effect (such as stopping a process, reprogramming an MPU/IOMMU, or advancing a canonical published reference) without holding an explicit capability that safe code cannot forge.
3. **Fault Containment, Cleanup, and Availability**: Whether a panic, infinite loop, deadlock, or out-of-memory condition in one component is prevented from corrupting shared state, leaking cross-domain allocations, or starving the rest of the system.
4. **Global Resource Identity, Freshness, and Semantic Correspondence**: Whether two local handles denote non-overlapping underlying resources (`RepCreator` vs. affine ownership in Theseus), whether a result corresponds to the current source/environment generation, and whether an output satisfies its functional or behavioral contract.

Synthesizing eight primary-source and current-revision investigations (2015–2026), this report establishes four foundational architectural conclusions:

- **Invariant-Complete Choke Points and Adversarial Policy Validation (`Tock` & `Asterinas`)**:
  - **Tock** (`tock/tock@78862168a64a4f9ce61c9c17370272770c4a7cbb`, `eaae5cbf62df2bc24ee809ff9d2c7ca124e42e73`, and forward `master` `842498efca186bba0071ed3d072fddd2dec3312e`; SOSP 2017 `10.1145/3132747.3132786` & SOSP 2025 `10.1145/3731569.3764828`) separates a privileged core kernel (`unsafe` permitted) from in-kernel safe-Rust **capsules** (`#![forbid(unsafe_code)]`) and hardware MPU-isolated **processes**. Because `unsafe` is too coarse to gate sensitive operations that are themselves memory-safe, Tock uses `unsafe` capability traits (`kernel/src/capabilities.rs`) minted only in visible board setup (`boards/components/README.md`) and process-lifetime-bound `Grant<T>` regions (`kernel/src/grant.rs`). Crucially, Tock's 2.0 syscall redesign proved that API narrowness is insufficient unless the core kernel owns buffer/callback lifetimes and revocation, and Tock's threat model (`tock/book@760025b0d8a1d5ff14d6015c1c50ac4e30490923`) explicitly notes that cooperatively scheduled capsules can still deny service or contain logic bugs.
  - **Asterinas** (`asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`, release `v0.18.1` tag `d924a9635a66c7c3bb43e563eaafa2c61d6ee9d5`; USENIX ATC 2025, `arXiv:2506.03876`) concentrates `unsafe` inside the **OSTD** framework (~14% TCB in ATC 2025) while compiling higher-level kernel services with `#![deny(unsafe_code)]`. OSTD classifies CPU, memory, and device resources by whether misuse can violate memory safety (`sensitivity-classification.md`), and enforces **safe policy injection** (`safe-policy-injection.md`): OSTD assumes safe-Rust schedulers, frame allocators, and slab allocators can return arbitrary buggy choices and independently validates task-execution state, frame metadata, and slot bounds at the OSTD mechanism boundary before acting on them.

- **Language-Based Fault Isolation vs. Foreign-Ownership Contracts and OS Process Boundaries (`RedLeaf` & `Rust-for-Linux`)**:
  - **RedLeaf** (OSDI 2020 USENIX paper 258949; `mars-research/redleaf@08753faee652495f55fc8cbb420e5123a183affc` on `osdi20_camera_ready`, contrasted with divergent `master` `7194295d1968c8013ae6b3d104a9192f03516449`) demonstrates that safe Rust alone does **not** provide fault isolation after a panic. RedLeaf requires heap isolation across domains, an `RRefable` trait forbidding raw pointers and ordinary Rust references (`&T`/`&mut T`) from crossing domains, shared-heap `RRef<T>` handles tracking owner-domain ID and borrow counts, IDL-generated proxies with runtime liveness checks and continuation unwinding (`RpcError`), and recursive allocation reclamation (`drop_domain` in `kernel/src/heap.rs`).
  - **Rust-for-Linux** (`torvalds/linux@551c722f40809618230001baccf219193e22fc5a`, 37 commits ahead of mainline tag `v7.3-rc5` `72d3fcf802c45d00b300f25b848a93c3a2bd7c7e`) localizes C FFI inside reviewed subsystem abstractions (`Documentation/rust/general-information.rst`) and makes cross-language ownership explicit via the `unsafe trait ForeignOwnable` (`rust/kernel/types.rs`), where uniqueness, borrow lifetimes, and single reclamation across raw `void *` pointers remain explicit caller obligations. Meanwhile, Linux's `seccomp_filter.rst` explicitly warns that syscall filtering is not a complete sandbox, reinforcing that OS subprocesses provide crash/reset separation for opaque tools (Charon, Aeneas, Lean) but still require generation-scoped identity fencing and authority confinement.

- **Local Affine Ownership vs. Global Resource Uniqueness (`Theseus`)**:
  - **Theseus** (PLOS 2017 `10.1145/3144555.3144560`, OSDI 2020, `arXiv:2501.00248v1` 2024-12-31, and `theseus-os/Theseus@1fbfe567075a65ed749b6680db1aeb538819c70c`) uses task-to-`LoadedCrate` strong/weak reference graphs (`StrongCrateRef`/`WeakCrateRef` in `kernel/crate_metadata/src/lib.rs`) to make in-process code/data liveness compositional across live cell swaps (`kernel/crate_swap/src/lib.rs`) while retaining an explicit `state_db` for unavoidable global state.
  - However, Theseus's own 2024 correctness study (`arXiv:2501.00248v1` §§5.2–5.3) and duplicate physical-frame allocation bug (`theseus-os/Theseus#451`, fixed in `abb5b83785224a78b2b22cc00d4e3af3865e60b6` and `5d62e567227e137db27c0c69728e732c5771c923`) refute the claim that affine/linear Rust types establish global resource uniqueness: single ownership of a *representation instance* (`AllocatedFrames`) does not prevent a constructor bug from minting a second instance with an overlapping physical address range (`ResourceIdentifier::overlaps`). Global uniqueness requires a verified constructor/registry (`RepCreator`); affine ownership only preserves uniqueness afterward.

- **Compatibility-Constrained Rewrites (`zCore`, `reL4`, `Theseus`, and `Anneal`)**:
  - Comparing **zCore** (`rcore-os/zCore@8de51f4ee053bcaaf435897febf648bcb4d45479`: clean Rust kernel-object and `kernel-hal` architecture targeting external Zircon and Linux behavioral compatibility), **reL4** (`rel4team/rel4_kernel@da74b45b69c89d9e6f43161006f3b586fda41107` and report `9dc90edc02e78ae79e647e1d1a4200c7cdf85afe`: incremental function-by-function Rust replacement inside the C seL4 build/test harness using explicitly temporary FFI compatibility shims), and **Theseus** (clean-slate intralingual OS sacrificing POSIX compatibility) shows that external behavioral compatibility, code ancestry, and internal architectural freedom are independent axes. For Anneal (`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`), durable commitments live in `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, whereas historical `anneal/v1/` CLI and generated-Lean names (`verify`, `generate`, `expand`, `Pre`, `Post`, `spec`) should be supported, if needed by consumers, via a versioned compatibility shell rather than freezing core architecture.

---

## Applicability

This report applies to:
- **Tock & Asterinas Baselines**:
  - `tock/tock` at `78862168a64a4f9ce61c9c17370272770c4a7cbb`, `eaae5cbf62df2bc24ee809ff9d2c7ca124e42e73`, forward `master` `842498efca186bba0071ed3d072fddd2dec3312e`, and divergent `release-2.2` tag `9554639b17501a9f5940cef7a1770a0823e790c3`; `tock/book@760025b0d8a1d5ff14d6015c1c50ac4e30490923`; SOSP 2017 (`10.1145/3132747.3132786`) and SOSP 2025 (`10.1145/3731569.3764828`).
  - `asterinas/asterinas` at `main` `a5238eb6a965a4616ce07a48f5dfbc8042c4cd44` and release tag `v0.18.1` (`d924a9635a66c7c3bb43e563eaafa2c61d6ee9d5`, 268 commits behind `a5238eb6`); USENIX ATC 2025 (`arXiv:2506.03876`).
- **RedLeaf & Linux Rust Baselines**:
  - `mars-research/redleaf` at `osdi20_camera_ready` (`08753faee652495f55fc8cbb420e5123a183affc`, committed 2021-02-20) and divergent `master` (`7194295d1968c8013ae6b3d104a9192f03516449`); OSDI 2020 paper 258949.
  - `torvalds/linux` at `551c722f40809618230001baccf219193e22fc5a` and mainline tag `v7.3-rc5` (`72d3fcf802c45d00b300f25b848a93c3a2bd7c7e`).
- **Theseus, zCore, reL4 & Anneal Baselines**:
  - `theseus-os/Theseus@1fbfe567075a65ed749b6680db1aeb538819c70c`, duplicate-frame repair commits `abb5b83785224a78b2b22cc00d4e3af3865e60b6` and `5d62e567227e137db27c0c69728e732c5771c923` (issue #451), PLOS 2017 (`10.1145/3144555.3144560`), OSDI 2020, and `arXiv:2501.00248v1`.
  - `rcore-os/zCore@8de51f4ee053bcaaf435897febf648bcb4d45479` (and early userboot commit `fdcdee0a664d0b9dc6984d2c70043485a7b5f3c9`), `rel4team/rel4_kernel@da74b45b69c89d9e6f43161006f3b586fda41107`, and `oscomp/first-prize-osf2024-StarryOS-yyds@9dc90edc02e78ae79e647e1d1a4200c7cdf85afe`.
  - `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` (`anneal/PRINCIPLES.md`, `anneal/DESIGN.md`, `anneal/README.md`, `anneal/src/main.rs`, `anneal/v1/`), plus frozen corpus reconciliation commits `327cce209828e92daba9e2be8a3f93232e35810c`, `d8ebe60bc920363d4e43d95713e7e6a2de5363d7`, `e1c4cf18da52136936eec8d6361607a9036adcb9`, and `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`.

---

## Findings

### 1. Small Trusted Mechanisms and Safe-Interface Choke Points in Tock and Asterinas

#### 1.1 Tock's Three-Tier Architecture, Capability Traits, Grants, and 2.0 Syscall Redesign
1. **Three-Tier Isolation (`tock/book@760025b0d8a1d5ff14d6015c1c50ac4e30490923`, `overview.md`, `design.md`, `capsule_isolation.md`, `threat_model.md`)**:
   - **Core Kernel (`kernel/src/`)**: Privileged layer allowed to use `unsafe` to manage hardware registers, context switches, MPU configuration (`kernel/src/platform/mpu.rs`), and grant lifecycles.
   - **Capsules (`capsules/core/src/lib.rs`)**: In-kernel drivers and virtualization services compiled with `#![forbid(unsafe_code)]`. Capsules share the kernel address space and cooperative event loop: Rust type safety prevents them from forging memory references, but they remain **semi-trusted for liveness** (an infinite loop or panic in a capsule stalls the kernel) and must be audited by board integrators.
   - **Processes**: Arbitrary-language userspace binaries isolated by hardware Memory Protection Units (MPUs / RISC-V PMP) and scheduled preemptively.
2. **Separating Language `unsafe` from System Authority (`kernel/src/capabilities.rs` & `boards/components/README.md`)**:
   - Because Rust's `unsafe` keyword is an all-or-nothing gate for language-level memory unsafety, operations that are memory-safe yet security-sensitive (such as stopping or restarting processes, entering the main loop, or creating network handles) are gated by zero-sized `unsafe trait` **capabilities** (`ProcessManagementCapability`, `ProcessStartCapability`, `MainLoopCapability`, `MemoryAllocationCapability`, `ExternalProcessCapability`, `UdpVisibilityCapability`).
   - Helper board components (`boards/components/`) forbid `unsafe` so capability minting stays visibly centralized in the board's main initialization file.
3. **Process-Bound Resource Lifetimes (`kernel/src/grant.rs`) and the Tock 2.0 Buffer Ownership Redesign (SOSP 2025 `10.1145/3731569.3764828`)**:
   - To prevent capsules from exhausting a global kernel heap on behalf of one application, `Grant<T>` allocates per-process capsule state inside the requesting process's grant region and revokes access automatically when the process terminates or restarts.
   - Early Tock 1.x syscall APIs allowed capsules to hold shared userspace buffers and callbacks in ways that violated Rust's aliasing and lifetime rules across process termination. Tock 2.0 required a breaking ABI and core-loop rewrite so the core kernel retains ownership of application buffers and lends capsules only temporary scoped closures—proving that a "narrow" safe API is unsound unless the trusted mechanism owns resource lifetime and revocation.
   - Even with a small core, hardware-boundary maintenance remains non-trivial: `CHANGELOG.md` and the SOSP 2025 retrospective document security-relevant bugs in RISC-V PMP region clearing across context switches and Cortex-M exception-return privilege modes.

#### 1.2 Asterinas's Framekernel Split, Resource Sensitivity Classification, and Safe Policy Injection
1. **OSTD vs. Safe Kernel Services (`asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`, `ostd/src/lib.rs`, `kernel/src/lib.rs`)**:
   - Asterinas runs in a single address space but confines `unsafe` to **OSTD** (`ostd/src/lib.rs`), while the Linux-compatible OS services layer (`kernel/src/lib.rs`, covering >210 syscalls in ATC 2025) uses `#![deny(unsafe_code)]`.
   - `book/src/ostd/soundness/what-soundness-means.md` (added systematically in commit `cef80ffa56d85e546144aa1747485ff2bc406da0`, 2026-03-18) defines OSTD soundness strictly as **absence of undefined behavior (UB)** under arbitrary safe-Rust service calls, userspace actions, and peripheral interactions—explicitly excluding deadlocks, livelocks, panics, starvation, or logical filesystem/network bugs.
2. **Resource Sensitivity Classification (`book/src/ostd/soundness/sensitivity-classification.md` & `safe-kernel-peripheral-interactions.md`)**:
   - OSTD classifies every CPU register, physical memory page, MMIO region, PIO port, and DMA target by whether misuse can corrupt the Rust execution environment. Kernel page tables, kernel stack/heap frames, interrupt controllers, and IOMMU configuration remain strictly encapsulated inside OSTD; untyped physical memory (`UntypedMem`), user virtual memory, and IOMMU-restricted device MMIO/DMA buffers are exposed to safe services.
3. **Adversarial Policy Validation (`book/src/ostd/soundness/safe-policy-injection.md`)**:
   - Complex policies (task scheduling, physical frame allocation, slab/heap allocation) are implemented outside OSTD via safe traits, and **OSTD re-validates every policy output before acting on it**:
     - *Task scheduler*: OSTD checks a private per-task execution-state flag atomically before context-switching so a buggy scheduler cannot run the same kernel stack on two CPUs simultaneously.
     - *Frame allocator*: OSTD checks private page metadata before minting a frame handle so a buggy allocator cannot hand out an already-in-use or sensitive physical frame.
     - *Heap/slab allocator*: OSTD verifies slot provenance, size, and alignment before using a returned slot to back a typed Rust object.

#### 1.3 Current-Source Verification Across Tock (`78862168` / `eaae5cbf` -> `842498ef`) and Asterinas (`a5238eb6` vs. `v0.18.1`)
As verified by `support/tock-asterinas-current-source-review/check_matrix.py` against `support/tock-asterinas-current-source-review/matrix.json` and `support/tock-asterinas-current-source-review/official-source-observation.json`:
- Official Tock `master` (`842498efca186bba0071ed3d072fddd2dec3312e`) is 23 commits (28 changed files) ahead of `78862168a64a4f9ce61c9c17370272770c4a7cbb` and 21 commits (25 changed files) ahead of `eaae5cbf62df2bc24ee809ff9d2c7ca124e42e73` (the two historical Tock pins differ only by 2 cryptography working-group note commits). Across all mapped Tock files (`kernel/src/lib.rs`, `kernel/src/capabilities.rs`, `kernel/src/grant.rs`, `kernel/src/platform/mpu.rs`, `capsules/core/src/lib.rs`, `boards/components/README.md`, `CHANGELOG.md`), only `kernel/src/lib.rs` changed (from blob `49f9ca34fcb2683eec5765a8364ed43423f04d16` to `84a9f806ac8028253799ed85c45b65a867ee1faa`), adding `#![deny(clippy::undocumented_unsafe_blocks)]` (alongside a `SAFETY:` comment in `kernel/src/process_loading.rs`). Tock's `release-2.2` tag (`9554639b17501a9f5940cef7a1770a0823e790c3`, 2025-01-06) is on a divergent release branch.
- Official Asterinas `main` remains at `a5238eb6a965a4616ce07a48f5dfbc8042c4cd44` (0 forward commits; all 9 mapped OSTD/kernel/book blobs identical), which is 268 commits ahead of release tag `v0.18.1` (`d924a9635a66c7c3bb43e563eaafa2c61d6ee9d5`, 2026-08-18).

---

### 2. Mixed-Language Isolation Boundaries: RedLeaf, Rust-for-Linux, and OS Tool Processes

#### 2.1 Why RedLeaf Requires Heavy Runtime Machinery Beyond Safe Rust (`OSDI 2020` & `mars-research/redleaf@08753faee`)
RedLeaf (Narayanan et al., OSDI 2020 pp. 21–39; paper-associated branch `osdi20_camera_ready` at `08753faee652495f55fc8cbb420e5123a183affc`) runs mutually distrusting safe-Rust domains in a single address space without hardware page-table switching on cross-domain calls. However, RedLeaf explicitly demonstrates that **safe Rust alone cannot isolate faults after a domain panic**:
1. **Constrained Cross-Domain Exchange (`lib/core/rref/src/rref.rs` blob `187e9245...` & `traits.rs` blob `1fd1dc9f...`)**:
   - Ordinary Rust references (`&T`, `&mut T`), slices, and raw pointers are forbidden from crossing domain boundaries by negative implementations of the `RRefable` auto trait.
   - Cross-domain heap data must be wrapped in `RRef<T>`, which stores a pointer to the current owner-domain ID, a borrow-count pointer, and a raw value pointer into a shared heap. Passing mutable state across a domain uses ownership movement (`RRef::move_to`, which notably still carries a `TODO: race here` comment at commit `08753faee`) rather than mutable borrows so a callee crash cannot leave caller-owned structures mid-mutation.
2. **Domain Crash Unwinding, Liveness Checks, and Recursive Reclamation (`kernel/src/heap.rs` blob `b643a13b...`, `kernel/src/unwind.rs` blob `f71d4d3c...`, `lib/core/interfaces/proxy/src/lib.rs`, `usr/src/rpc.rs`)**:
   - IDL-generated proxies check domain liveness on entry, save continuation state (`unwind.rs`), catch panics at the domain boundary, unwind migrating threads back to the caller, and return an explicit `RpcError` variant when a callee domain faults.
   - `drop_domain` in `kernel/src/heap.rs` walks the global shared-allocation table, identifies every allocation currently owned by the crashed domain, runs recursive cleanup callbacks, and frees its storage.
   - Device driver recovery requires an explicit **shadow driver** that logs and replays initialization state—proving that process/domain termination is not automatic rollback of external or device effects.
3. **Current-Source Recheck (`support/redleaf-linux-current-source-review/check_matrix.py`)**:
   - At the 2026-09-30 observation (`support/redleaf-linux-current-source-review/official-source-observation.json`), `mars-research/redleaf` branch `osdi20_camera_ready` still equals `08753faee652495f55fc8cbb420e5123a183affc`, whereas `master` (`7194295d1968c8013ae6b3d104a9192f03516449`) is a **divergent history** (314 commits ahead, 1 behind) where 5 of the 7 `lib/core/...` paths (`rref.rs`, `traits.rs`, `proxy/src/lib.rs`, `create/src/lib.rs`, `usr/src/rpc.rs`) do not exist and `kernel/src/heap.rs` / `kernel/src/unwind.rs` have different blobs.

#### 2.2 Rust-for-Linux Foreign Ownership (`ForeignOwnable`) and Subprocess Sandbox Limits (`torvalds/linux@551c722f`)
In `torvalds/linux@551c722f40809618230001baccf219193e22fc5a` (verified at zero forward commits on `master`, 37 commits ahead of `v7.3-rc5` `72d3fcf802c45d00b300f25b848a93c3a2bd7c7e`, with stable kernel `7.2.8` recorded in `support/kernel-releases.json`):
- **As-Safe-As-Possible Wrappers (`Documentation/rust/general-information.rst` blob `09234bed...`, `coding-guidelines.rst` blob `3198be3a...`, `rust/kernel/interop.rs` blob `3b371d78...`)**: Leaf Rust drivers do not call bindgen C signatures directly; subsystem abstractions localize `unsafe` FFI and separate public `# Safety` obligations from internal `// SAFETY:` proofs.
- **Explicit Cross-Language Ownership (`rust/kernel/types.rs` blob `132dd428...`, `unsafe trait ForeignOwnable`)**: `into_foreign` transfers Rust ownership into a raw C `void *` pointer; `from_foreign`, `borrow`, and `borrow_mut` require the C side to uphold pointer validity, single reclamation, and borrow non-overlap while the value resides outside Rust's type checker.
- **OS Process Reset vs. Sandbox Boundaries (`Documentation/userspace-api/seccomp_filter.rst` blob `cff0fa7f...`)**:
  - Separate OS processes provide language-independent crash containment and address-space reset for opaque verification tools ( corroborated by `anneal--lean-pool-failure-isolation` blob `d95b0ddc...`, where 4 independent Lean servers survived peer crashes, and `anneal--cross-tool-stage-cancellation-cleanup` blob `14e91986...`, in contrast to `aeneas-library-process-architecture` blob `90a1fa61...` which found process-global mutable OCaml state).
  - However, `seccomp_filter.rst` explicitly states that syscall filtering is *not* a complete sandbox, and process termination neither rolls back partial filesystem writes nor proves that a finished worker's output matches the current source generation.

---

### 3. Intralingual Ownership vs. Global Invariants in Theseus (`2017–2024`)

#### 3.1 Evolution from State-Spill Elimination to Explicit Roots and Reference-Counted Code Liveness
1. **From Absolute State-Spill Elimination to `state_db` (PLOS 2017 `10.1145/3144555.3144560` vs. OSDI 2020 §§5.1–5.2)**:
   - Theseus began in PLOS 2017 with the goal of eliminating "state spill" (where a server module retains lasting progress state on behalf of a client) by moving all resource state into client-owned affine Rust handles (`MappedPages`).
   - By OSDI 2020 (`theseus-os/Theseus@1fbfe567075a65ed749b6680db1aeb538819c70c`), the authors recognized that hardware-mandated state and asynchronous interrupt/entry context cannot be exported purely to clients, introducing an explicit minimal root (`state_db` and the cell `CrateNamespace` manager) with defined serialization and transfer rules.
2. **Task-to-`LoadedCrate` Liveness vs. Namespace Authority (`book/src/subsystems/task_invariants.md` blob `b624063b...`, `kernel/crate_metadata/src/lib.rs` blob `683bf27c...`, `kernel/crate_swap/src/lib.rs` blob `c9f943e8...`)**:
   - Every task owns the `LoadedCrate` (`StrongCrateRef`) containing its entry function, and each `LoadedCrate` holds strong references (`StrongCrateRef`) to the crates its sections depend on and weak back-links (`WeakCrateRef`) to its dependents.
   - During live evolution (`crate_swap::swap_crates` and `applications/upd/src/lib.rs` blob `562f6af8...`), replacement crates are loaded into an isolated temporary `CrateNamespace`, dependencies and `.data`/`.bss` state are transferred under metadata locks, and old entries are removed from the active namespace while outstanding `StrongCrateRef` handles keep old code alive for in-flight tasks until they finish. Crucially, `crate_swap/src/lib.rs` warns that **memory liveness does not guarantee semantic compatibility** across arbitrary code/data layout changes.

#### 3.2 Why Affine Ownership Does Not Establish Global Resource Uniqueness (`arXiv:2501.00248v1` & Issue `#451`)
The most important boundary finding in Theseus comes from its December 2024 correctness study (Ijaz, Boos & Zhong, *Combining Type Checking and Formal Verification for Lightweight OS Correctness*, `arXiv:2501.00248v1`, §§5.2–5.3) and repository history (`theseus-os/Theseus#451`):
- **The Affine Representation Fallacy**: Rust's affine type system guarantees that each instance of a linear type (such as `AllocatedFrames` or `AllocatedPages` in `book/src/subsystems/memory.md` blob `c0cdf1f9...`) has a **single owner**. It **does not** guarantee that two independently constructed instances represent **disjoint underlying physical resources**.
- **Concrete Failure (`theseus-os/Theseus#451`)**: During NIC driver memory setup in October 2021, Theseus's frame allocator returned two distinct `AllocatedFrames` objects covering the **same physical memory frame** because reserved and general-purpose frame bookkeeping overlapped (repaired across commits `abb5b83785224a78b2b22cc00d4e3af3865e60b6` and `5d62e567227e137db27c0c69728e732c5771c923`; similar progressive boundary tightening appears in `LoadedSection::as_func()` across `fbe80b05...`, `919d9a28...`, and `b92483cb...`).
- **The `RepCreator` Repair (`arXiv:2501.00248v1`)**: To establish true global exclusivity, Theseus introduced an **Intralingual Representation System (IRS)** centered on a formally verified constructor `RepCreator::create_unique_representation` that checks an explicit specification relation `ResourceIdentifier::overlaps` against global bookkeeping before minting a private linear type. **Formal verification/bookkeeping establishes the global creation invariant; Rust affine ownership preserves it afterward.**

---

### 4. Compatibility-Constrained Rewrites (`zCore`, `reL4`, `Theseus`, and `Anneal`)

| System & Pinned Source | Code Ancestry & Migration Strategy | External Behavioral Contract | Internal Architectural Freedom & Cost |
| :--- | :--- | :--- | :--- |
| **`zCore`** (`rcore-os/zCore@8de51f4ee053bcaaf435897febf648bcb4d45479`, early commit `fdcdee0a...`) | Clean Rust implementation (not an in-place C++ translation of Zircon). | Preserves Zircon syscall/userboot behavior (official Zircon core-tests) and Linux syscall behavior (libc-test) across libOS and bare-metal modes. | **High**: separates `zircon-object`, `zircon-syscall`, `linux-object`, `linux-syscall`, and `kernel-hal` (`kernel_handler.rs`). High ongoing cost to close remaining failed-test lists. |
| **`reL4`** (`rel4team/rel4_kernel@da74b45b69c89d9e6f43161006f3b586fda41107`, report `9dc90edc02e78ae79e647e1d1a4200c7cdf85afe`) | Incremental function-by-function C-to-Rust replacement embedded as a `staticlib` inside the C seL4 build (`build.py`). | Continuous compatibility with the native seL4 C test suite (`baseline` vs. Rust build). | **Medium during migration, higher afterward**: groups bidirectional C FFI (`src/deps.rs`, `#[no_mangle]`) into explicitly temporary compatibility modules (`src/cspace/mod.rs` marked for deletion) while refactoring C procedures into Rust methods and evolving toward pure-Rust `bin mode`. |
| **`Theseus`** (`theseus-os/Theseus@1fbfe567075a65ed749b6680db1aeb538819c70c`, OSDI 2020) | Clean-slate from-scratch Rust OS (~38k LoC, ~4 person-years in OSDI 2020). | None: intentionally dropped POSIX and legacy kernel ABI compatibility. | **Very high**: single-address-space cells and intralingual ownership, paid for via ecosystem and POSIX maturity gaps. |
| **`Anneal` Redesign vs. Historical `v1`** (`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/` vs. `anneal/v1/`) | Clean redesign (`anneal/src/main.rs` currently exposing `setup`) alongside archived `anneal/v1/` (`Verify`, `Setup`, `Expand`, `Generate`, `Pre`/`Post`/`spec`). | **Semantic contract (`PRINCIPLES.md`, `DESIGN.md`)**: fail-closed verification, explicit/shrinkable TCB log, justified Rust semantics, compositional abstraction, Rust-oriented diagnostics. | **High (`DESIGN.md` "Deliberate non-decisions")**: CLI flags, annotation syntax, proof encoding, and tool boundaries are intentionally unfrozen; if external users depend on `v1` CLI or generated Lean shapes, wrap the redesigned core in a versioned compatibility shell rather than freezing internal representations. |

---

## Boundaries

1. **Safe Rust Interfaces Do Not Guarantee Availability, Logical Correctness, or Native Code Confinement**:
   - Neither Tock's `#![forbid(unsafe_code)]` capsules nor Asterinas's `#![deny(unsafe_code)]` kernel services prevent deadlocks, infinite loops, starvation, panics, or functional protocol bugs (`what-soundness-means.md`, `capsule_isolation.md`).
   - Furthermore, wrapping an external binary, C/OCaml library, or Lean plugin in a safe Rust trait or struct (`PreparedEnvironment`) does not place that foreign execution inside Rust's memory model or prevent it from reading unrecorded ambient environment variables, search paths, or mutable files (`ForeignOwnable`).

2. **Local Affine Ownership Does Not Prove Global Identity, Disjointness, or Cross-Process Freshness**:
   - As proved by Theseus's duplicate-frame bug (`theseus-os/Theseus#451`) and `RepCreator` (`arXiv:2501.00248v1`), an affine Rust handle proves single ownership of the *handle struct*, not that two handles represent non-overlapping resources or that a generation handle is still the current published generation across processes. Global identity requires content-addressed digests or a serialized authority check; cross-process freshness requires atomic publication and readback.

3. **OS Subprocesses Are Crash/Reset Boundaries, Not Complete Sandboxes or Transactional Rollbacks**:
   - Killing a worker process group reclaims private memory and language-runtime globals, but does not roll back partial filesystem writes, kill escaped daemons, or enforce a security sandbox (`seccomp_filter.rst`), nor does it prevent a slow worker from returning a stale result after a newer generation becomes authoritative.

---

## Evidence

- **Structured Evidence & Comparison Matrices (`support/`)**:
  - `support/comparison-matrix.json`, `support/evidence-map.json`, and `support/source-map.json`.
  - `support/tock-asterinas-current-source-review/matrix.json`, `support/tock-asterinas-current-source-review/official-source-observation.json`, `support/tock-asterinas-current-source-review/frozen-cohort.csv`, `support/tock-asterinas-current-source-review/baseline-report-paths.txt`, `support/tock-asterinas-current-source-review/version-inventory-ebcdcad-581.csv`, and `support/tock-asterinas-current-source-review/check_matrix.py`.
  - `support/redleaf-linux-current-source-review/matrix.json`, `support/redleaf-linux-current-source-review/official-source-observation.json`, `support/redleaf-linux-current-source-review/linux-refs.txt`, `support/redleaf-linux-current-source-review/linux-mainline-tag-refs.txt`, `support/redleaf-linux-current-source-review/redleaf-refs.txt`, `support/redleaf-linux-current-source-review/redleaf-latest-release.json`, `support/redleaf-linux-current-source-review/kernel-releases.json`, and `support/redleaf-linux-current-source-review/check_matrix.py`.
  - Preserved Linux & RedLeaf source snapshots under `support/snapshots/linux/` (`Documentation/rust/general-information.rst`, `Documentation/rust/coding-guidelines.rst`, `Documentation/userspace-api/seccomp_filter.rst`, `rust/kernel/interop.rs`, `rust/kernel/types.rs`) and `support/snapshots/redleaf/` (`old/lib/core/rref/src/rref.rs`, `old/lib/core/rref/src/traits.rs`, `old/kernel/src/heap.rs`, `old/kernel/src/unwind.rs`, `old/lib/core/interfaces/proxy/src/lib.rs`, `old/lib/core/interfaces/create/src/lib.rs`, `old/lib/core/interfaces/usr/src/rpc.rs`, plus `current-master/kernel/src/heap.rs` and `current-master/kernel/src/unwind.rs`).
  - Per-study evidence maps: `support/redleaf-mixed-language-isolation-boundaries-2020-2026/comparison-matrix.json`, `support/redleaf-mixed-language-isolation-boundaries-2020-2026/evidence-map.json`, `support/theseus-ownership-global-invariants-2017-2024/evidence-map.json`, and `support/compatibility-constrained-rewrites-zcore-rel4-theseus-anneal/evidence-map.json`.

---

## Revalidation

1. **Run the Offline Matrix and Blob-Identity Verifiers for Tock, Asterinas, RedLeaf, and Linux Rust**:
   ```bash
   python3 support/tock-asterinas-current-source-review/check_matrix.py
   python3 support/redleaf-linux-current-source-review/check_matrix.py
   ```
   Confirm that both scripts exit `0`, validating all frozen claim mappings, Git blob SHA-1/SHA-256 hashes, forward/divergent branch comparisons, and release tag identities.

2. **Revalidate Tock and Asterinas Safe-Interface & Policy-Validation Boundaries**:
   - In `tock/tock`, inspect `capsules/core/src/lib.rs` (`#![forbid(unsafe_code)]`), `kernel/src/capabilities.rs`, and `kernel/src/grant.rs`.
   - In `asterinas/asterinas`, inspect `kernel/src/lib.rs` (`#![deny(unsafe_code)]`), `ostd/src/lib.rs`, `book/src/ostd/soundness/what-soundness-means.md`, `sensitivity-classification.md`, and `safe-policy-injection.md` to confirm that OSTD continues to validate scheduler, frame-allocator, and slab-allocator outputs before mutating privileged state.

3. **Revalidate RedLeaf, Rust-for-Linux, Theseus, zCore, and reL4 Source Anchors**:
   - Check `torvalds/linux` (`rust/kernel/types.rs::ForeignOwnable`, `Documentation/rust/general-information.rst`, `Documentation/userspace-api/seccomp_filter.rst`) and `mars-research/redleaf` (`osdi20_camera_ready` vs. `master`).
   - In `theseus-os/Theseus`, inspect `kernel/crate_metadata/src/lib.rs`, `kernel/crate_swap/src/lib.rs`, and check whether the `RepCreator` / `ResourceIdentifier::overlaps` mechanism from `arXiv:2501.00248v1` has been merged into `theseus_main`.
   - In `google/zerocopy`, re-read `anneal/PRINCIPLES.md`, `anneal/DESIGN.md` ("Deliberate non-decisions"), and `anneal/README.md` before hardening any CLI or generated-proof compatibility adapter.
