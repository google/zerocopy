# Atomic and Fence Mappings, AArch64 and x86-TSO Weak Memory Models, and Concurrent Reclamation Protocol Boundaries

## Summary

Verifying concurrent low-level Rust and assembly requires distinguishing four separate semantic layers that cannot be collapsed into a single "thread safety" claim or inferred from emitted instruction mnemonics alone:
1. **Language Access & Synchronization Semantics**: Rust's C++20-derived access-based memory model (`library/core/src/sync/atomic.rs`), data-race undefined behavior, mixed-size atomic overlap restrictions, inline assembly effect options (`nomem`, `readonly`), and `Send`/`Sync` ownership transfer obligations.
2. **Compiler Lowering & Effect Contracts**: The mapping from source atomic operations and fences (`Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst`, `compiler_fence`) through LLVM IR orderings and inline-assembly memory clobbers to target instructions, where identical machine opcodes (such as `MOV` on x86-64 for both `Relaxed` and `Acquire` loads, or `STLR` on AArch64 for both `Release` and `SeqCst` stores) carry distinct compiler transformation constraints.
3. **Hardware Weak Memory Models (`x86-TSO` and `AArch64` CAT)**: The axiomatic and operational hardware models (`herd/herdtools7@9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34` `x86tso.cat` and `aarch64.cat`) governing reads-from (`rf`), coherence (`co`), from-reads (`fr`), barrier-ordered-before (`bob`), exclusive load/store reservation pairing (`LDXR`/`STXR`, `LDAXR`/`STLXR`), LSE atomics (`LDADD`, `LDADDAL`, `CASAL`), and the distinction between RCpc acquire loads (`LDAPR`, annotation `Q`) and full RCsc acquire loads (`LDAR`, annotation `A`).
4. **Deductive Weak-Memory Logics, Stateless Model Checkers, and Safe Memory Reclamation (SMR) Protocols**: Program logics (`RSL`, `Strong Logic / iGPS`, `iRC11 / ORC11 / GPFSL`, `RustBelt Meets Relaxed Memory`), stateless model checkers (`GenMC`, `RustMC`), and whole-protocol memory reclamation verifications (`Arc`, sequentially consistent hazard pointers with immutable traversal optimization, and weak-memory RCU with explicit `FenceSC` epoch synchronization).

Across five integrated investigations, this report combines:
- **Cross-Architecture C11/LLVM Atomic & Fence Compilation (`support/atomics.c`)**: 51 function/configuration pairs and 167 verified IR/assembly predicates across `x86_64-unknown-linux-gnu`, baseline `aarch64-unknown-linux-gnu` (`-march=armv8-a -mno-outline-atomics`), and `aarch64` with LSE (`-march=armv8.1-a+lse`), plus 10 store-buffering (`SB`) relation projections (`support/sb_projection.py`).
- **Executable `herd7` AArch64 Model Runs, Rust Nightly Codegen, and 60,000 Native Execution Rounds (`support/evidence/`)**: 10 actual `herd7` (`7.58+1`, commit `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`) runs across message-passing (`MP-*`) and store-buffering (`SB-*`) litmus tests proving that `STLR` + `LDAPR` forbids stale message passing (`Never`, 3 states) but **permits** the store-buffering weak outcome `(0,0)` (`Sometimes`, 4 states), whereas `STLR` + `LDAR` and `DMB ISH` forbid `(0,0)` (`Never`, 3 states); Rust `nightly` (`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, default `target-cpu=apple-m1` with `+rcpc`) codegen emitting `LDAPR` for `Acquire` loads and `LDAR` for `SeqCst` loads; 60,000 native concurrent execution rounds on Apple M4 Pro; and compilation-only controls (`support/evidence/annotation_controls.rs`) showing that false `nomem` or `readonly` inline-assembly options cause LLVM to constant-fold a post-assembly reload to `mov w0, #7` (`ret i32 7`).
- **Concurrency Verification & Reclamation Protocol Boundaries**: Exact scope and adequacy analysis of `RSL` (OOPSLA 2013), `Strong Logic for Weak Memory` (ECOOP 2017), `GenMC` (CAV 2021), `RustMC` (FORTE 2026), `iRC11`/`ORC11` (`iris/gpfsl@48b7183f1b91f7cc53cfdab16e21387e9bfe9c14` vs. `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`), `lambda-rust` relaxed-memory `Arc` (`186900b2cf948835873281646ce20c7e8f084f17`), and the PLDI 2025 hazard-pointer (`zenodo:15183251`, DOI `10.1145/3729247`) and weak-memory RCU (`zenodo:15167032`, DOI `10.1145/3729246`) Rocq artifacts.

---

## Applicability

This report applies to:
- **Hardware & Cat Model Baselines**: `herd/herdtools7@9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34` (`herd/libdir/x86tso.cat`, `herd/libdir/aarch64.cat`, `aarch64hwreqs.cat`, `aarch64fences.cat`, `herd/AArch64Sem.ml`, `herd/AArch64Annot.ml`, `lib/AArch64Base.ml`, and executable `herd7` `7.58+1` SHA-256 `b50b95ab172b076b01d44b49e35cc86566ee6332550edce282a896db55e5095e`).
- **Rust Language, Standard Library & Compiler Subjects**:
  - `rust-lang/rust` at `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (`1.99.0`), `f53b654a8882fd5fc036c4ca7a4ff41ce32497a6` (`nightly-aarch64-apple-darwin`, LLVM `22.1.4`, `rustc` SHA-256 `c456b0855e2d148f5d517952f2cb684bf0379d125d2c89b5ca16d46e56c80988`), `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`), and `f6c1107f8be13e48465e12c0fd26e6a39fe18e4f` (`library/core/src/sync/atomic.rs`, `library/alloc/src/rcs/arc.rs`, `library/core/src/marker.rs`, `library/core/src/cell.rs`).
  - `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/inline-assembly.md`).
- **Compiler & Sequential ISA Semantics Baselines**:
  - Upstream LLVM `21.1.0` concurrency documentation (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`), Apple Clang `21.0.0` (`clang-2100.3.34.2`, binary SHA-256 `1590ac950a3d627817d09ade5cb60b2115f17a72182a3141e010b4bcc482a0c9`), and C++20 working draft `WG21 N4868` (2020-10-18).
  - `AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7` sequential machine-state and `Effects` model.
- **Weak-Memory Compilation & Reclamation Formalizations**:
  - Intermediate Memory Model (`weakmemory/imm@4ca191b072df081dd3a6d9aa755959dc901b1bd0`, POPL 2019 DOI `10.1145/3290382`), x86-TSO (Owens, Sarkar & Sewell CACM 2010), C++11 mapping (Batty et al. POPL 2011 DOI `10.1145/1926385.1926394`), and ARMv8 Flat/MCA equivalence (Pulte et al. POPL 2018 DOI `10.1145/3158107`).
  - `iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17` (POPL 2020 DOI `10.1145/3371102`), `iris/gpfsl@48b7183f1b91f7cc53cfdab16e21387e9bfe9c14`, `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`, PLDI 2025 weak-memory RCU (`zenodo:15167032`, DOI `10.1145/3729246`), and PLDI 2025 hazard pointers (`zenodo:15183251`, DOI `10.1145/3729247`).

---

## Findings

### 1. Rust Access-Based Atomic Rules vs. Machine-Instruction Coincidence

#### 1.1 Access-Based Data-Race and Mixed-Size Rules (`library/core/src/sync/atomic.rs`)
Across all inspected Rust revisions (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `f6c1107f8be13e48465e12c0fd26e6a39fe18e4f`, `d8ef4f3fe7031514cbd7d056b7b058814987ecec`), `library/core/src/sync/atomic.rs:25–58` specifies that Rust's atomic memory model follows C++20 (`WG21 N4868` §6.9.2.2 and §31.4) without `memory_order_consume`, translated from C++'s object-based model to Rust's **access-based** model:
1. **Data-Race Undefined Behavior**: Two accesses conflict if they overlap in byte range and at least one is a write (a failed `compare_exchange` is *not* a write). A data race occurs when two conflicting accesses are not ordered by happens-before and at least one is non-atomic. Concurrent atomic and non-atomic *reads* do not conflict and are permitted.
2. **Mixed-Size Atomic Access Restriction**: Even when both accesses are atomic, unsynchronized overlapping atomic accesses are undefined behavior unless they are disjoint, cover **exactly the same byte range and size**, or both read. Consequently, an unsynchronized 2-byte atomic write overlapping a 1-byte atomic write is UB in Rust even if the underlying ISA executes both instructions indivisibly. Synchronized changes of access width across a happens-before boundary remain legal.
3. **Fence Synchronization Requires Atomic Communication (`N4868` §31.11)**: Release/acquire fences establish happens-before only when paired with appropriate intervening atomic read/write operations on a shared location; surrounding racy non-atomic accesses with fences does not eliminate a data race.
4. **Lock-Free vs. Wait-Free Portability (`atomic.rs:115–155`)**: Rust guarantees that available atomic types (`target_has_atomic` widths) are lock-free, **not** necessarily wait-free (for example, LL/SC loops on baseline AArch64 can retry under contention).

#### 1.2 Why Machine-Instruction Coincidence Does Not Equate Source Semantics
When an `Acquire` load and a `Relaxed` load compile to the same x86-64 `MOV` instruction, or a `Release` store and a `SeqCst` store compile to the same AArch64 `STLR` instruction, their language-level and LLVM IR orderings remain distinct and continue to constrain compiler reorderings, alias assumptions, and surrounding non-atomic accesses. Sequential machine models such as `AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7` (`MachineData.load`/`store` over a single byte-map state with `Effects.All`) can verify exclusive sequential register/memory execution, but provide no concurrent execution graph (`rf`, `co`, `fr`, `bob`), no RMW pairing, and no justification for interthread synchronization annotations.

---

### 2. Hardware Weak Memory Models (`x86-TSO` and `AArch64` CAT) and Compilation Bridge Scope

#### 2.1 `x86-TSO` and `AArch64` Axiomatic & Operational Semantics (`herdtools7@9574394f`)
- **`x86-TSO` (`herd/libdir/x86tso.cat` and Owens, Sarkar & Sewell CACM 2010)**:
  - Operational FIFO store buffers allow a hardware thread to read its own buffered write (`rfi`) before that write becomes visible to other processors; `MFENCE` drains the store buffer, and `LOCK`-prefixed RMW instructions (`XADD`, `CMPXCHG`, `ORL`, and `XCHG` with memory, which is implicitly locked) enforce atomic read-modify-write semantics and flush store buffers.
  - `x86tso.cat` checks per-location coherence (`uniproc`), forbids intervening writes between paired RMW events (`rmw & (fre; coe) = 0`), and enforces acyclicity of the global implied/preserved program order (`po \ (W * R)`, `mfence`, locked atomics, `rfe`, `fr`, `co`). Ordinary write-to-read program order (`W ->po R`) is omitted unless bridged by `MFENCE` or a locked instruction. Note that `LFENCE` and `SFENCE` are declared in `x86fences.cat` but do not enter `x86tso.cat`'s ordinary coherent write-back memory relation (and the CACM 2010 equivalence theorem excludes exceptions, misaligned/mixed-size accesses, non-temporal stores, self-modifying code, and page-table walks).
- **`AArch64` (`herd/libdir/aarch64.cat`, `aarch64hwreqs.cat`, `aarch64fences.cat`, `herd/AArch64Sem.ml`)**:
  - `aarch64.cat:155–161` takes the transitive closure of hardware-required ordering (`hw-reqs`, including barrier-ordered-before `bob`, dependency edges `addr`/`data`/`ctrl`, and RMW atomicity) with observed-by edges (`obs = rfe | fr | co`), requiring irreflexivity alongside `internal` visibility (`po-loc | rf | fr | co` acyclic) and atomic RMW exclusion.
  - In `aarch64hwreqs.cat:122–138`, `bob` includes:
    - Full barrier `DMB ISH` (`dmb.full`) ordering all memory operations (`M ->dmb.full M`), load barrier `DMB ISHLD` (`dmb.ld`) ordering reads before subsequent memory (`R ->dmb.ld M`), and store barrier `DMB ISHST` (`dmb.st`) ordering writes (`W ->dmb.st W`). Thus an acquire barrier (`DMB ISHLD`) placed after a store does **not** order store-to-load (`W -> R`) pairs.
    - Release writes (`L`, emitted by `STLR` / `STLXR` / `LDADDL` / `LDADDAL` / `CASAL`) order all prior memory accesses before the release (`M ->po L`).
    - Both full acquire reads (`A`, emitted by `LDAR` / `LDAXR` / `LDADDA` / `LDADDAL` / `CASAL`) and RCpc acquire reads (`Q`, emitted by `LDAPR`) order the acquire read before all subsequent memory accesses (`(A | Q) ->po M`).
    - Crucially, `bob` includes the release-to-full-acquire store-to-load ordering clause **`L ->po A`** (`[L]; po; [A]`), which **excludes `Q` (`LDAPR`)**. In `lib/AArch64Base.ml:1254–1260`, `herd/AArch64Sem.ml:2056–2072`, and `herd/AArch64Annot.ml:39–59`, `LDAR` generates event set `A` whereas `LDAPR` generates event set `Q`.

#### 2.2 Scope Limits of Published Compilation & Equivalence Theorems
1. **Batty et al. (*Mathematizing C++ Concurrency*, POPL 2011 `10.1145/1926385.1926394`, §5 Theorem 3)**: Proves correctness of a proposed C++0x-to-x86 mapping for defined programs excluding SC fences, thread fork/join, and locks/unlocks, assuming 1-to-1 non-overlapping atomic locations.
2. **Pulte et al. (*Simplifying ARM Concurrency*, POPL 2018 `10.1145/3158107` & errata)**: Proves equivalence of the 2018 ARMv8 Flat operational and revised MCA axiomatic models over their common fragment, **explicitly excluding** mixed-size accesses, `LDAPR` (ARMv8.3-RCpc), LSE atomics (ARMv8.1-LSE), and system/translation semantics.
3. **Podkopaev, Lahav & Vafeiadis (*Bridging the Gap between Programming Languages and Hardware Weak Memory Models / IMM*, POPL 2019 `10.1145/3290382`, §4.2 Theorem 4.5, and Coq repository `weakmemory/imm@4ca191b072df081dd3a6d9aa755959dc901b1bd0`)**:
   - In `src/hardware/imm_sToARM.v` (historically referred to as `immToARM.v` in `README`), `IMM_s_psc_consistent:246–254` assumes finite events, Arm consistency, and RMW/dependency hypotheses to construct an SC witness, whereas `IMM_s_consistent:310–328` excludes SC fences, and `immToTSO.v:897–906` requires an explicit SC-store-to-SC-load fence premise.
   - **Annotation Vocabulary Inversion Hazard**: In `weakmemory/imm`, `Q` denotes standard acquire-mode reads and `A` denotes SC-mode reads, whereas in `herdtools7` (`AArch64Annot.ml`), `A` denotes full acquire (`LDAR`) and `Q` denotes RCpc acquire (`LDAPR`). Proofs or certificates bridging IMM and `herd7` must translate annotation sets explicitly rather than matching single-letter names.

---

### 3. Performed C11/Clang and Rust Nightly Atomic & Fence Compilation Observations

#### 3.1 C11 Atomic & Fence Lowering Across x86-64, Baseline AArch64, and AArch64+LSE (`support/atomics.c`)
Compiled with Apple Clang `21.0.0` (`clang-2100.3.34.2`, SHA-256 `1590ac950a3d627817d09ade5cb60b2115f17a72182a3141e010b4bcc482a0c9`) using `-std=c11 -O2 -Wall -Wextra -Werror -ffreestanding -fno-stack-protector -S` across 17 functions and 3 targets (`51` pairs, `167` passing IR/assembly checks in `support/observed` verified by `support/check.py`):

| Source Operation (`_Atomic(unsigned long long)`, 8-byte aligned) | `x86_64-unknown-linux-gnu` Observed | Baseline `aarch64` (`-march=armv8-a -mno-outline-atomics`) | `aarch64` + LSE (`-march=armv8.1-a+lse`) |
| :--- | :--- | :--- | :--- |
| `Relaxed` / `Acquire` / `SeqCst` load | `MOV` / `MOV` / `MOV` | `LDR` / `LDAR` / `LDAR` | `LDR` / `LDAR` / `LDAR` |
| `Relaxed` / `Release` / `SeqCst` store | `MOV` / `MOV` / `XCHG` | `STR` / `STLR` / `STLR` | `STR` / `STLR` / `STLR` |
| `Relaxed` `fetch_add` | `LOCK XADD` | `LDXR`, `ADD`, `STXR` retry loop | `LDADD` |
| `AcqRel` / `SeqCst` `fetch_add` | `LOCK XADD` | `LDAXR`, `ADD`, `STLXR` retry loop | `LDADDAL` |
| Strong CAS (`AcqRel` success / `Acquire` failure) | `LOCK CMPXCHG` | `LDAXR` / `STLXR` retry; `CLREX` on mismatch | `CASAL` |
| `Acquire` thread fence | *(no barrier opcode; IR `fence acquire`)* | `DMB ISHLD` | `DMB ISHLD` |
| `Release` / `AcqRel` thread fence | *(no barrier opcode; IR `fence release`/`acq_rel`)* | `DMB ISH` | `DMB ISH` |
| `SeqCst` thread fence | `LOCK ORL $0, -64(%rsp)` | `DMB ISH` | `DMB ISH` |
| `SeqCst` signal fence (`atomic_signal_fence`) | *(no barrier opcode; IR `fence syncscope("singlethread") seq_cst`)* | *(no barrier opcode)* | *(no barrier opcode)* |
| Empty volatile asm with `"memory"` clobber | *(no barrier opcode; retains IR clobber)* | *(no barrier opcode)* | *(no barrier opcode)* |
| Explicit hardware fence asm (`mfence` / `dmb ish`) + `"memory"` | `MFENCE` | `DMB ISH` | `DMB ISH` |

Note that on x86-64, Clang lowers `atomic_thread_fence(memory_order_seq_cst)` to `LOCK ORL $0, -64(%rsp)` rather than `MFENCE` (matching the alternative x86 C/C++ mapping documented in `cpp0xmappings.html`). In the 10 fixed-candidate store-buffering relation projections (`support/sb_projection.py` -> `support/sb-projection-result.json`), full fences (`MFENCE`, `LOCK ORL`, `DMB ISH`) or `XCHG` / `STLR`+`LDAR` close the store-buffering cycle, whereas placing an AArch64 `DMB ISHLD` (`dmb.ld`) after stores or using an empty compiler barrier leaves the cycle open.

#### 3.2 Actual `herd7` AArch64 Model Enumeration (`9574394f`) vs. Rust Nightly `LDAPR` / `LDAR` Lowering and 60,000 Native Rounds
In `support/evidence/`, `rustc 1.97.0-nightly` (`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, `nightly-aarch64-apple-darwin`, `-O`, default `target-cpu=apple-m1` with `rcpc` enabled) compiled eight 32-bit `AtomicU32` wrapper functions (`support/evidence/atomic_wrappers.rs` -> `support/evidence/atomic_wrappers.s`), emitting **`LDAPR` for `Ordering::Acquire` loads** and **`LDAR` for `Ordering::SeqCst` loads**:

| Rust Function (`support/evidence/atomic_wrappers.rs`) | Emitted AArch64 Instructions (`support/evidence/atomic_wrappers.s`) | Corresponding `herd7` Litmus Input (`support/evidence/inputs/`) | `herd7` Weak Target Verdict (`aarch64.cat`) | Enumerated Model States | Apple M4 Pro Native Histogram `[00, 01, 10, 11]` (10,000 rounds each) |
| :--- | :--- | :--- | :---: | :---: | :--- |
| `publish_relaxed` + `observe_relaxed` | `STR data; STR flag` / `LDR flag; LDR data` | `MP-r0-a0.litmus` (also `MP-r0-a1`, `MP-r0-p1`, `MP-r1-a0` all `Sometimes`, 4 states) | **`Sometimes`** (`(flag,data)=(1,0)` allowed) | 4 (1 pos, 3 neg) | `MP-relaxed`: `[4957, 0, 0, 5043]` (`10` weak count = `0`) |
| `publish_release` + `observe_acquire` (`LDAPR`) | `STR data; STLR flag` / `LDAPR flag; LDR data` | `MP-r1-p1.litmus` (and `MP-r1-a1.litmus` with `LDAR`: both `Never`, 3 states) | **`Never`** (`(flag,data)=(1,0)` forbidden) | 3 (0 pos, 3 neg) | `MP-release-acquire`: `[4947, 0, 0, 5053]` (`10` count = `0`) |
| `store_then_load_relaxed` | `STR own; LDR peer` | `SB.litmus` | **`Sometimes`** (`(r0,r1)=(0,0)` allowed) | 4 (1 pos, 3 neg) | `SB-relaxed`: `[0, 4960, 5040, 0]` (`00` weak count = `0`) |
| `store_then_load_release_acquire` (`STLR` + `LDAPR`) | `STLR own; LDAPR peer` | `SB-STLR-LDAPR.litmus` | **`Sometimes`** (`(r0,r1)=(0,0)` **allowed!**) | 4 (1 pos, 3 neg) | `SB-release-acquire`: `[0, 5032, 4968, 0]` (`00` weak count = `0`) |
| `store_then_load_seqcst` (`STLR` + `LDAR`) | `STLR own; LDAR peer` | `SB-STLR-LDAR.litmus` | **`Never`** (`(r0,r1)=(0,0)` forbidden) | 3 (0 pos, 3 neg) | `SB-seqcst`: `[0, 5007, 4993, 0]` (`00` count = `0`) |
| `store_then_load_fenced` (`STR; DMB ISH; LDR`) | `STR own; DMB ISH; LDR peer` | `SB-dmb.litmus` | **`Never`** (`(r0,r1)=(0,0)` forbidden) | 3 (0 pos, 3 neg) | `SB-fence`: `[0, 4936, 5064, 0]` (`00` count = `0`) |

**Key Technical Takeaways from the Combined `herd7` and Native Experiment**:
1. **RCpc (`LDAPR`) vs. RCsc (`LDAR`) Separation on Store Buffering**: Pairing `Release` stores (`STLR`, event `L`) with `Acquire` loads lowered to `LDAPR` (event `Q`) suffices to forbid the stale message-passing outcome (`MP-r1-p1`: `Never`), because `M ->po L` and `Q ->po M` order the writer's data store before `STLR` and the reader's `LDAPR` before the data load. However, on store buffering (`SB-STLR-LDAPR`), because `bob` in `aarch64hwreqs.cat:128–138` only orders `[L]; po; [A]` and **not** `[L]; po; [Q]`, `STLR` followed by `LDAPR` **permits** both threads to read `0` (`Sometimes`, 4 states). Lowering `SeqCst` loads to `LDAR` (event `A` in `SB-STLR-LDAR`) or inserting `DMB ISH` (`SB-dmb`) forbids `(0,0)` (`Never`, 3 states).
2. **Why Native Testing Cannot Substitute for Formal Model Verification**: Across 60,000 native rounds on an Apple M4 Pro host (`support/evidence/concurrent_assembly.rs`, using 128-byte aligned `Arc<AlignedAtomicU32>` cells and three-party start/done barriers), every observed outcome fell inside `herd7`'s allowed set, but **zero weak outcomes (`10` in MP or `00` in SB) were observed even in `MP-relaxed`, `SB-relaxed`, or `SB-release-acquire` where the architecture permits them**. Bounded native stress runs cannot falsify or distinguish `LDAPR` vs. `LDAR` store-buffering guarantees when thread scheduling and barrier cadence suppress the weak window.
3. **Inline Assembly Effect Violations (`nomem` / `readonly` in `support/evidence/annotation_controls.rs`)**:
   - Under `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/inline-assembly.md`, rules `asm.options.supported-options-nomem` lines 1104–1105, `asm.options.supported-options-readonly` lines 1150–1151, and `asm.rules.mem-same-as-ffi` lines 1338–1342), both `nomem` and `readonly` promise no interthread synchronization, `nomem` forbids accessing externally reachable memory, and `readonly` forbids mutating it.
   - In `support/evidence/annotation_controls.rs` (compiled-only to `support/evidence/annotation_controls.ll` and `support/evidence/annotation_controls.s`, never executed), storing `7` via `&mut u32`, overwriting the address with `9` inside `asm!("str w1, [x0]", ...)`, and returning `*ptr` preserves the actual `ldr w0, [x0]` load when no false option is passed, but under `options(nomem)` or `options(readonly)` LLVM elides the reload and emits `mov w0, #7` (`ret i32 7`).

---

### 4. Deductive Weak-Memory Logics, Stateless Model Checkers, and Safe Memory Reclamation Protocols

#### 4.1 Deductive Logics vs. Stateless Model Checkers (`RSL`, `Strong Logic`, `GenMC`, `RustMC`)

| Verification Approach | Primary Source / Artifact | Target Memory Model & Fragment | Core Mechanism & Soundness Boundary |
| :--- | :--- | :--- | :--- |
| **Relaxed Separation Logic (`RSL`)** | Vafeiadis & Narayan, OOPSLA 2013 (`10.1145/2509136.2509532`) | C11 relaxed-memory fragment (release/acquire/relaxed atomics + non-atomic accesses). | Transfers resource ownership across threads via release writes and acquire reads (relaxed accesses do not transfer ownership). Project page documents a Figure 13 erratum against the 2011 C11 formalization, underscoring sensitivity to exact model definitions. |
| **Strong Logic for Weak Memory (`iGPS` / `Iris`)** | Kaiser, Dang, Dreyer, Lahav & Vafeiadis, ECOOP 2017 (`10.4230/LIPIcs.ECOOP.2017.17`) | Operational characterization of the **C11 `RA+NA` fragment** (release/acquire + non-atomics). | Bridges Iris (which assumes an operational interleaving step relation) to weak memory by proving an operational `RA+NA` machine characterization and deriving higher-order GPS/RSL rules in Coq. Does not cover relaxed RMWs, `SeqCst` fences, or mixed-size accesses outside `RA+NA`. |
| **`GenMC`** | Kokologiannakis & Vafeiadis, CAV 2021 (`10.1007/978-3-030-81685-8_20`) | Parametric stateless model checking over `RC11`, `IMM`, and `LKMM`. | Explores consistent execution graphs Soundly, Completely, and Optimally **for a fixed bounded program/loop configuration** (`spin-assume` / loop bounding), producing concrete counterexample graphs on failure. Does not prove unbounded input theorems. |
| **`RustMC`** | Pearce, Lange & O'Keeffe, FORTE 2026 (`10.1007/978-3-032-28187-6_14`) | Concurrent Rust (and C/C++ FFI) lowered to LLVM IR and checked via `GenMC`. | Handles Rust-specific thread spawn/join, memory intrinsics, and uninitialized accesses at LLVM IR level; source-level soundness still depends on the unverified premise that `rustc` -> LLVM lowering preserves the concurrency behaviors relevant to the checked property. |

#### 4.2 View-Indexed Separation Logic (`iRC11` / `ORC11` / `GPFSL`) and Whole-Protocol Reclamation (`Arc`, Hazard Pointers, Weak-Memory RCU)
Under weak memory, **fractional permission arithmetic (`1/2 + 1/2 = 1`) is insufficient to justify memory deallocation**: collecting all fractional tokens in thread $T_2$ does not guarantee that $T_2$'s hardware/logical view has observed the prior read/write accesses performed by thread $T_1$ while holding its fraction (Dang, Jourdan, Kaiser & Dreyer, *RustBelt Meets Relaxed Memory*, POPL 2020 `10.1145/3371102`, §§4–5). In `iris/gpfsl@48b7183f1b91f7cc53cfdab16e21387e9bfe9c14` (`gpfsl/base_logic/vprop.v:20–45`, `surface_vSP.v:GPS_vSP_dealloc`, `adequacy.v:17–95`):
- Assertions `vProp` are monotone predicates indexed by a logical thread view `V` (`view_join V P`, `view_at V P`). Physical `drf_pre_dealloc` requires the reclaiming thread's view to cover all prior read and write histories at every deallocated location; `GPS_vSP_dealloc` requires synchronized ghost token transfer (`view_tok γi 1` + `GPS_vSP_Reader`) backed by physical release/acquire synchronization.
- Note that `iris/gpfsl@48b7183f` (`2026-09-25`) exposes `noprol_adequacy` with an explicit `time_ctx` premise (alongside `noprol_adequacy_no_time`), whereas the 2024 snapshot `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472` (`gpfsl/base_logic/adequacy.v:50`) used the no-time signature directly.

| Reclamation Protocol & Pinned Artifact | Underlying Memory Model & Adequacy Endpoint | Whole-Protocol Invariant & Validation Mechanism | Concrete Differences vs. Native Rust Implementation |
| :--- | :--- | :--- | :--- |
| **Relaxed-Memory `Arc`** (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`, `theories/lang/arc.v`, `theories/typing/lib/arc.v`; POPL 2020 `10.1145/3371102`) | `ORC11` / `iRC11` (`GPS` protocols + view-indexed lifetime logic `lrust`). | `arc_persist` (lines 29–36) couples strong/weak counter protocols with shared payload typing (`arc_send`/`arc_sync` lines 264–279 requiring payload `Send` **and** `Sync`) and guarded lifetime-ending restoration of owned payload + freeable block (`arc_clone_type` lines 636–637, `arc_drop_type` lines 847–848). | Model `clone_arc` uses a relaxed load/CAS loop and `drop_arc` returns `option ty` to caller without overflow checks; native `rust-lang/rust@f6c1107f` (`library/alloc/src/rcs/arc.rs:2514–2548, 2949+`) uses `fetch_add(Relaxed)` with `MAX_REFCOUNT` abort guard, `fetch_sub(Release)`, an `acquire!` fence/load macro, and `drop_slow`. |
| **Hazard Pointers with Immutability Optimization** (`zenodo:15183251`, `immut-artifact.zip` SHA-256 `485a24c8...`; PLDI 2025 `10.1145/3729247`) | **Sequentially Consistent (`SC`)** HeapLang (`lang/adequacy.v:heap_adequacy` lines 29–60). | `spec_hazptr.v` distinguishes `Deactivated`, `NotValidated p` (announcement only!), and `Validated(p, γ, R, sz)` shield states. `shield_validate'` requires management reachability evidence; `hazard_pointer_impl` (`closed_proofs.v:40–96`) and `harris_find_spec` (`proof_harris_find.v:989+`) close Harris list lookup/insert/delete. | Rocq proof elides fences under `SC`; accompanying native Rust list (`implementation/src/ds_impl/hp/list.rs:103–165` `traverse_with_anchor`) announces via `protect_raw`, calls `light_membarrier`, and validates anchors/predecessors with `Acquire` loads and CAS orderings. |
| **Weak-Memory RCU / Epoch Reclamation** (`zenodo:15167032`, `pldi25-3-artifact.zip` SHA-256 `e3c63792...`; PLDI 2025 `10.1145/3729246`) | **Operational Weak Memory (`ORC11` + `FenceSC`)** (`gpfsl/lang/lang.v:sc_fence_base_step`, `iwp_sc_fence`, `base_logic/adequacy.v:noprol_adequacy` lines 50–95). | `activate_loop` (`smr/rcu/code.v`) publishes epoch to slot, executes **`FenceSC`**, and re-reads global epoch; `try_advance` executes **`FenceSC`**, scans slots, and advances epoch; reclamation frees nodes retired at epoch $e$ only when global epoch reaches $e + 3$. `rcu_impl` (`base_proof.v:30–53`), `harris_impl`, and `msqueue_impl_rcu` (`3751–3763`) close the full records. | Unlike baseline `iris/gpfsl` (which omits SC fences), this artifact **explicitly adds and verifies `FenceSC`** (`sc_fence_base_step` / `iwp_sc_fence`). However, epochs are modeled as unbounded mathematical integers ($\mathbb{Z}$), so fixed-width native counter wraparound is not covered. |

---

## Boundaries

1. **Unestablished End-to-End Rust-to-LLVM-to-Hardware Weak-Memory Refinement**:
   - Inspecting emitted instructions (`LDAPR`, `LDAR`, `STLR`, `DMB ISH`, `LOCK XADD`, `LOCK ORL`) and enumerating finite 2-thread `herd7` litmus tests establish **compiler mapping observations and model state sets**, not a mechanized refinement theorem connecting Rust's access-based memory model (`atomic.rs`) through LLVM IR optimizations to `aarch64.cat` or `x86tso.cat`.
   - In particular, a safety proof in a restrictive operational model (`ORC11` or `SC`) transfers to source Rust only if every bad source execution is represented in the model (the reverse inclusion from proving that model executions are allowed by Rust), and uninitialized memory reads in `GPFSL` (which return a `poison` value) must be explicitly bridged to Rust's uninitialized-read UB.

2. **Adequacy Theorems Establish Partial Correctness (`NotStuck`), Not Termination or Fair Progress**:
   - Both `heap_adequacy` (`zenodo:15183251`) and `noprol_adequacy` (`zenodo:15167032` / `iris/gpfsl@48b7183f`) prove safety and postcondition validity for finite reachable steps (`adequate NotStuck`). They **do not** prove that CAS/LL-SC retry loops terminate, that RCU epochs eventually advance, or that retired memory is eventually reclaimed when readers remain active. Wait-freedom, lock-freedom, and bounded reclamation require separate scheduler fairness and liveness hypotheses.

3. **Fail-Closed Translation Boundary for Concurrent Rust Verification**:
   - A verifier whose target semantics is a sequential state transformer (such as `Kraken` `MachineData.load/store`) must **fail closed** (reject) when translating concurrent Rust constructs (atomics, fences, thread spawn/join, shared `UnsafeCell` / `Sync` interior mutability, or inline assembly without exclusive-ownership proofs) unless an explicit concurrency translation matrix binds each source construct, memory order, access width, and effect annotation to a sound target weak-memory proof rule.

---

## Evidence

- **C11/Clang Cross-Target Atomic & Fence Compilation (`support/`)**:
  - `support/atomics.c` (SHA-256 `70f3aaabb9c84b6dcbad33675981395c1864e04fc5654b77bc3e898f1a55b9aa`), `support/compile.py` (`51164c91bd66b127150986a19990ddacda844ede2d2184986885eea9a56b0514`), `support/check.py` (`abc879fed8c342f4b0a5562417c7c796e4748c5967a618912cb5e0880e533582`), and `support/sb_projection.py` (`468326373a9e2343136cdab537ac62adb8862c02fdc03ee912396ec6a5cbfb43`).
  - `support/observed`, `support/observed-dispatcher`, `support/sb-projection-result.json`, `support/source-index.json` (43 source entries with Git blob IDs and SHA-256 hashes), `support/primary-paper-index.json`, `support/public-path-projection.json`, and `support/compiler-identities.json`.
- **Executable `herd7` AArch64 Runs, Rust Nightly Codegen, and Native Controls (`support/evidence/`)**:
  - Litmus inputs (`support/evidence/inputs/MP-r0-a0.litmus` .. `MP-r1-p1.litmus`, `SB.litmus`, `SB-STLR-LDAPR.litmus`, `SB-STLR-LDAR.litmus`, `SB-dmb.litmus`) and full `herd7` outputs (`support/evidence/runs/MP-r1-p1.stdout`, `support/evidence/runs/SB-STLR-LDAPR.stdout`, `support/evidence/runs/SB-STLR-LDAR.stdout`, etc.).
  - Rust atomic codegen specimens (`support/evidence/atomic_wrappers.rs`, `support/evidence/atomic_wrappers.s`, `support/evidence/runs/final-rustc-atomic-asm.json`), native runner (`support/evidence/concurrent_assembly.rs`, `support/evidence/concurrent_assembly.s`, `support/evidence/concurrent-leaves-exact.s`, `support/evidence/runs/concurrent-native.json`, `support/evidence/runs/concurrent-native.stdout`), and inline-asm effect controls (`support/evidence/annotation_controls.rs`, `support/evidence/annotation_controls.ll`, `support/evidence/annotation_controls.s`).
  - Provenance and static audit artifacts: `support/validate.py`, `support/static-validation.json`, `support/projection-receipts.json`, `support/source-inventory-audit.json` (verifying 6,580 `herdtools7` files against `support/evidence/herd-source.sha256`), `support/upstream/herdtools7/VERSION.txt`, `support/evidence/runs/herd-version.stdout`, `support/evidence/runs/herd-binary-hash.stdout`, `support/evidence/build/herd-verified-build-parent-note.json`, `support/evidence/environment/container-resource.json`, `support/evidence/may1-tool-identities.json`, and `support/coverage.json`.
- **Concurrency & Reclamation Metadata (`support/`)**:
  - `support/approach-matrix.json`, `support/artifact-source-identities.json`, `support/source-identities.json`, and `support/source-evidence.json`.

---

## Revalidation

1. **Run the Static Evidence Auditor for the `herd7`, `rustc`, and Native Control Artifacts**:
   ```bash
   python3 support/validate.py
   ```
   Confirm that all file hashes, instruction sequences, `herd7` state sets, 60,000 native histogram counts, and `annotation_controls` IR/assembly checks match `support/static-validation.json`.

2. **Re-verify the 51-Pair C11/Clang Atomic Compilation Checks and 10 Store-Buffering Projections**:
   ```bash
   python3 support/check.py support/observed
   python3 support/sb_projection.py support/<replayed-sb>.json
   ```
   To re-run compilation with a local `clang` binary into a fresh output directory:
   ```bash
   python3 support/compile.py --clang /path/to/clang --out support/<replay-dir>
   python3 support/check.py support/<replay-dir>
   ```

3. **Replay `herd7` Litmus Suites and `rustc` Codegen**:
   Using `support/replay-commands.json` with `herdtools7@9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34` and `rustc` (`nightly-aarch64-apple-darwin` or newer toolchain), re-run the 10 `MP-*`/`SB-*` litmus tests against `herd/libdir/aarch64.cat` and inspect `atomic_wrappers.s` to verify whether `Acquire` loads emit `LDAPR` (`Q`) vs. `LDAR` (`A`). Keep `support/evidence/annotation_controls.rs` compilation-only (never execute the UB `nomem`/`readonly` controls).

4. **Revalidate Concurrency Logic and SMR Protocol Endpoints**:
   When upgrading Rust toolchains or importing an Iris/GPFSL/Rocq reclamation theorem, re-diff `library/core/src/sync/atomic.rs` and `library/alloc/src/rcs/arc.rs`, inspect the exact adequacy signature (`noprol_adequacy` vs. `heap_adequacy`), and verify every row of the concurrency translation matrix (source semantic rule, lowered representation, target model rule, bad-execution preservation direction, and fail-closed rejection on unsupported orderings or widths).
