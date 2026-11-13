# Weak-Memory Concurrency Theory: Source Models, Hardware Models, ISA Mappings, and Compiler Optimizations

## Summary

Choosing a concurrent semantics for Rust MIR and a verified compilation strategy to `x86-64` and `AArch64` requires reconciling a fundamental tension in weak-memory concurrency theory: **axiomatic no-thin-air models** (`RC11` and `IMM`) have complete, mechanized hardware mapping proofs in Coq/Rocq (`weakmemory/imm` at `4ca191b072df081dd3a6d9aa755959dc901b1bd0`), but forbid thread-local load-to-store reordering on `Relaxed` atomics (`acyclic(po | rf)`), whereas **operational timestamp/view models** (`Promising Semantics 2.0` / `2.1`) justify thread-local compiler optimizations and load-to-store reordering via local simulation, at the cost of significantly heavier certification state (`promise`-free vs. capped-certification steps).

Across the examined source models, hardware models, mapping theorems, and optimization frameworks, six architectural conclusions govern a verified Rust compiler:

1. **Source Model Selection (`RC11` / `IMM` vs. `Promising 2.0/2.1` vs. C++20):**
   - **Rust's stated model (`library/core/src/sync/atomic.rs:25-58` in `1.99.1`)** adopts the **C++20 (`N4868`)** rules (which incorporate `RC11`'s `psc` fix for `SeqCst` fences and `RMW` coherence, omit `memory_order_consume`, and change C++'s object-based model to an **access-based** model), while leaving the Out-of-Thin-Air (`OOTA`) load-buffering problem (`LB-data.litmus`) open in the normative specification.
   - **`RC11` (PLDI 2017, `herdtools7` `rc11.cat`)** and **`IMM` (POPL 2019, `weakmemory/imm`)** are the only models with end-to-end mechanized compilation chains from source through an intermediate IR down to `x86-TSO` and `ARMv8` (`immToTSO.v`, `imm_sToARM.v`). Under `RC11`, compiler passes may reorder independent non-atomic accesses and eliminate redundant accesses, but must preserve `po` from `Relaxed` loads to subsequent `Relaxed` stores (`LB-data.litmus`: `Never 0 3` under `rc11.cat` vs. `Sometimes 1 3` under `c11_orig.cat`).
2. **Mixed-Size Accesses, Seqlocks, `compiler_fence`, and Volatile Accesses:**
   - **Mixed-size atomics** that overlap with different widths without happens-before synchronization are **Undefined Behavior** in Rust (`atomic.rs:42-55`), `RC11`, `IMM`, and `Promising 2.0/2.1`, even when hardware models (`herd7 -variant mixed` on `AArch64-mixed-mp.litmus` and `X86-mixed-sbf.litmus`) assign them well-defined byte-level coherence.
   - **Seqlocks** written with non-atomic reader loads (`C-seqlock-na-race.litmus`) trigger immediate data-race UB (`Undef` in `herd7 -cat rc11.cat`) even when the reader checks `s1 == s2` after an `Acquire` fence and discards torn reads; sound seqlock readers in Rust must use `Ordering::Relaxed` atomic loads (or per-word `AtomicUsize::load(Relaxed)`) followed by `fence(Ordering::Acquire)` before reading the second sequence counter (`C-seqlock.litmus`: `Never 0 18`, zero `Undef`).
   - **`compiler_fence` (`atomic_signal_fence`)** emits LLVM `fence syncscope("singlethread") <ord>` and zero machine instructions on `x86-64` and `AArch64`; it constrains only intra-thread compiler reordering (for signal/interrupt handlers or `membarrier`-paired asymmetric synchronization) and adds **no** inter-thread edges in `RC11`, `IMM`, or `Promising`.
   - **Volatile accesses (`read_volatile` / `write_volatile`)** model single-thread external I/O side effects (`MMIO`) and are **not** atomic synchronization operations (`library/core/src/ptr/mod.rs`); concurrent unsynchronized `read_volatile`/`write_volatile` on ordinary RAM is a data race.
3. **Hardware Models and `IMM` Mapping Boundaries (`x86-TSO`, `Armv8` Flat/MCA, `LSE`, `RCpc`):**
   - `weakmemory/imm` (`4ca191b072df081dd3a6d9aa755959dc901b1bd0`) mechanizes `C11/RC11 -> IMM` (`src/c11/C11ToImm.v`), `IMM -> x86-TSO` (`src/hardware/immToTSO.v:897-906`), and `IMM_s -> ARMv8` (`src/hardware/imm_sToARM.v:246-328`).
   - **Critical gap between `rustc` AArch64 codegen and `IMM` / `RC11`:** When `+rcpc` (`ARMv8.3-A`) is enabled (default on `apple-m1` and `neoverse-n1+`), LLVM/Rust lowers `Ordering::Acquire` loads to **`LDAPR`** (`Q` in `aarch64.cat`) while lowering `Ordering::SeqCst` loads to **`LDAR`** (`A`) and both `Release` and `SeqCst` stores to **`STLR`** (`L`). Because `aarch64hwreqs.cat:128-138` includes `[L]; po; [A]` in `bob` but **omits `[L]; po; [Q]`**, `STLR` followed by `LDAPR` allows the weak store-buffering outcome `(0,0)`, whereas `IMM`'s `imm_sToARM.v` assumes all acquire/SC loads lower to `LDAR` (`A`) and does not model `LDAPR` (`Q`) or ARMv8.1-LSE (`LDADDAL`, `CASAL`).
4. **Invalid vs. Sound Optimizations Under Weak Memory:**
   - Standard sequential optimizations—including **speculative register promotion** across loops, **roach-motel reordering** of accesses *out* of critical sections, **unread load introduction** on potentially racing locations, and **thread inlining / sequentialization** in `Promising 1.0`—have published counterexamples under weak memory.
   - Sound optimization proofs factor into (a) **adjacent-access commutation and elimination** over `IMM`/timestamp traces (`CompCertTSO` JACM 2013, `CASCompCert` PLDI 2019, `Promising 2.0` PLDI 2020) and (b) **sequential-reasoning transfer for non-atomic code** between synchronization points (Cho, Lee, Hur & Kang, TOPLAS 2022, DOI `10.1145/3527633`).
5. **Embedding Sequential Proofs (`DRF-SC`, `Local DRF`, and `iRC11`/`GPFSL`):**
   - By the **Local DRF (`LDRF`)** theorem (Dolan, Sivaramakrishnan & Madhavapeddy, PLDI 2018; Cho et al., TOPLAS 2022), any program region that only accesses thread-local or properly lock/release-acquire synchronized locations (`race-free` on those locations) refines its **sequentially consistent** (and per-function sequential) semantics, even if unrelated locations in the program participate in `Relaxed` atomic races.
6. **Lean 4 Availability:** Neither `weakmemory/imm` (Coq 8.9–8.16), `kaist-cp/promising2-coq` (Coq), nor `iris/gpfsl` (Rocq) has been ported to Lean 4 in full; however, Anneal's `trusted/lean/` and corpus weak-memory mechanization (`support/track7_memory_ct_weakmem_elf_probe.lean` and `support/round2_track6_probe.lean` in `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`) mechanize the `Release`/`Acquire` message-passing (`MP`), `RMW` modification-order exclusivity, and `SeqCst` store-buffering (`SB`) soundness bridges directly in Lean `4.34.1`.

## Applicability

This report governs the concurrency semantics of Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), MiniRust (`063d784186d3252bee242217f218223205c0b568`), and middle-end/backend compilation targeting `x86_64` (`x86-TSO`) and `aarch64` (`ARMv8.0-A`, `ARMv8.1-LSE`, and `ARMv8.3-RCpc`).

The subjects in `REPORT.json` relate as follows:
- `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) defines the normative `core::sync::atomic` and `core::ptr::{read_volatile, write_volatile}` contracts and the LLVM atomic codegen rules.
- `herd/herdtools7` (`9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`, `herd7` `7.58`) provides the executable axiomatic specifications for `c11_orig.cat`, `rc11.cat`, `aarch64.cat` (including `-variant mixed`), and `x86tso.cat`.
- `weakmemory/imm` (`4ca191b072df081dd3a6d9aa755959dc901b1bd0`, POPL 2019 DOI `10.1145/3290382`), `RC11` (PLDI 2017 DOI `10.1145/3062341.3062352`), and `Promising 2.0/2.1` (`kaist-cp/promising2-coq`, PLDI 2020 DOI `10.1145/3385412.3386010`) provide the mechanized source and intermediate weak-memory models.
- `CompCertTSO` (JACM 2013 DOI `10.1145/2487241.2487248`), `CASCompCert` (PLDI 2019 DOI `10.1145/3314221.3314604`), `Local DRF` (PLDI 2018 DOI `10.1145/3192366.3192384`), and Cho et al. (TOPLAS 2022 DOI `10.1145/3527633`) provide the compiler optimization and sequential-embedding theorems.

## Findings

### 1. Source Concurrency Models Compared: C++20/Rust, RC11, IMM, and Promising (PS 1.0, 2.0, 2.1)

**Basis: normative specification + source + execution (`rust-lang/rust` `58cf8f9c35b3` `library/core/src/sync/atomic.rs:25-155`, `herd/herdtools7` `9574394fc4b2` `herd/libdir/{c11_orig.cat,rc11.cat}`, `weakmemory/imm` `4ca191b072df` `src/basic/Execution.v` & `src/imm/Imm.v`, `support/LB-data.litmus`, `support/C-seqlock.litmus`, `support/C-seqlock-na-race.litmus`, `support/concurrency_models_matrix.json`).**

| Dimension | C++20 as Adopted by Rust (`atomic.rs:25-58`, `N4868`) | `RC11` (Lahav et al. PLDI 2017; `rc11.cat`) | `IMM` (Podkopaev et al. POPL 2019; `weakmemory/imm`) | Promising 1.0 / 2.0 / 2.1 (`kaist-cp/promising2-coq`) |
| :--- | :--- | :--- | :--- | :--- |
| **Mathematical structure** | Axiomatic execution graphs `(E, po, rf, mo, sc, hb)` with `psc` SC-fence order (`N4868` §6.9.2.2, §31.4) | Axiomatic execution graphs (`hb`, `eco`, `psc_base`, `psc_f`, `po \| rf` acyclic) | Axiomatic intermediate IR model (`ppo`, `bob`, `ar = rfe \| bob \| ppo \| detour \| psc_f` acyclic) | Operational timestamped message memory with per-thread views, promises, and thread-local certification |
| **`OOTA` (`LB-data` cycle `r0=x; y=r0 \|\| r1=y; x=1`)** | Formally **allowed** by the axiomatic equations (`c11_orig.cat`: `Sometimes 1 3`), with prose stating implementations "should not" produce OOTA | **Forbidden** by `acyclic(po \| rf)` (`rc11.cat`: `Never 0 3`); forbids `Relaxed` load $\to$ store reordering | **Forbidden**Along syntactically tracked `data`/`ctrl`/`addr` dependencies (`ppo`), while allowing independent `Relaxed` load $\to$ store reordering! | **Forbidden** (`PS 1.0` allows global certification; `PS 2.0` caps promise timestamps to restore thread-local `register promotion` & `sequentialization`; `PS 2.1` adds undefinedness/undef bits) |
| **`SeqCst` semantics (`S` / `psc`)** | Partial `psc` order over `SeqCst` operations (`N4868` integrates the `RC11` fix so `SeqCst` fences restore `SB`, while mixing `SeqCst` stores with `Acquire` loads is weaker) | `acyclic(psc_base \| psc_f)` (`rc11.cat`); repairs C++11's unsound Power/ARMv8 compilation of `SeqCst` | `psc_f` (`Imm.v` / `imm_s.v`); `imm_s` strengthens `IMM` with an explicit total order `s` over `SC` accesses for ARMv8 mapping | Operational global `SC` view timestamp updated by `SeqCst` fences and `SeqCst` accesses |
| **Mixed-size accesses** | **UB** unless overlapping atomic accesses have identical byte address and width or both are reads (`atomic.rs:42-55`) | **Unmodeled / UB** (single-size abstract locations `Loc`) | **Unmodeled / UB** (single-size abstract locations `Loc`) | **Unmodeled / UB** in `PS 1.0/2.0/2.1` (uniform cell granularity) |
| **Hardware fences (`fence(ord)`)** | `Release`, `Acquire`, `AcqRel`, `SeqCst` (`N4868` §31.11); synchronize only when paired with atomic loads/stores | Modeled via `[F]; po; [W]` / `[R]; po; [F]` in `sw` and `psc_f` | Modeled as explicit `F_rel`, `F_acq`, `F_acqrel`, `F_sc` events in `bob` and `psc_f` | Operational thread-view advancements (`V_rel`, `V_acq`, `V_sc`) |
| **`compiler_fence` (`atomic_signal_fence`)** | Constrains intra-thread compiler movement only; establishes `sequenced-before` with signal handlers on the same thread; **zero** inter-thread synchronization | Intra-thread `po` is already fixed in an axiomatic graph; `compiler_fence` adds no `hb`/`sw` edge | Constrains middle-end pass reorderings before `IMM`; adds no `bob` edge at ISA level | Prevents compiler transformations across the fence point; operational step is a no-op on thread views |
| **Volatile accesses (`read_volatile` / `write_volatile`)** | External I/O (`MMIO`) side effects; **not** atomic (`ptr/mod.rs`); racy volatile accesses on RAM are data-race UB | Not synchronization; treated as non-atomic for data-race detection (or external trace events) | Lowered as external syscall/I/O or constrained memory accesses outside `IMM` optimization rules | Modeled as observable external events (`Event.syscall`) that cannot be elided or reordered |
| **Seqlocks (optimistic read + retry)** | **UB if payload is read non-atomically** (`C-seqlock-na-race.litmus`: `Undef`); **Valid** if payload uses `Relaxed` atomic loads + `fence(Acquire)` before second `seq` load (`C-seqlock.litmus`: `Never 0 18`) | Same as C++20: non-atomic racy read is immediate `Undef`; `Relaxed` atomic payload loads + `Acquire` fence is race-free and sound | Valid when payload uses `Relaxed` atomic loads and reader executes `F_acq` before the second `seq` read (`ppo` / `bob` orders payload loads before `seq` reload) | In `PS 2.1`, racy non-atomic reads return `undef`, which can be frozen/discarded if `s1 != s2`, whereas `Relaxed` atomic loads avoid `undef` entirely |
| **Combination with aliasing (`SB` / `TB`)** | Orthogonal in Miri (`src/tools/miri/src/concurrency/data_race.rs`): vector clocks check C++20 `hb` races while `SB`/`TB` runs in global step order | `ORC11` / `iRC11` (`iris/gpfsl` and `lambda-rust` POPL 2020) combines `RC11` views with fractional lifetime tokens (`&T` / `&mut T`), not dynamic `SB`/`TB` retag trees | No aliasing tags in `weakmemory/imm` (`Loc` is flat) | No `SB`/`TB` borrow trees in `promising2-coq` (`Simuliris` PLDI 2025 assumes SC interleaving) |

#### Empirical `herd7` Verification of `LB-data` and Seqlock Litmus Tests (`support/`)
Executing `herd7` (`7.58`, `herd/herdtools7` at `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`) on the preserved C11 litmus tests in `support/` establishes:
1. **`support/LB-data.litmus` (`c11_orig.cat` vs. `rc11.cat`):**
   - `herd7 -cat c11_orig.cat support/LB-data.litmus` reports `Observation LB-data Sometimes 1 3` (`States 3`), confirming that unpatched C++11/C++20 `hb`/`mo`/`rf` axioms permit the thin-air cycle `0:r0=1 /\ 1:r1=1`.
   - `herd7 -cat rc11.cat support/LB-data.litmus` reports `Observation LB-data Never 0 3` (`States 2`), confirming that `rc11.cat`'s `acyclic (po | rf)` axiom rules out `0:r0=1 /\ 1:r1=1`.
2. **`support/C-seqlock.litmus` vs. `support/C-seqlock-na-race.litmus` (`rc11.cat`):**
   - In `support/C-seqlock-na-race.litmus`, writer `P0` increments `seq` to `1` (`relaxed`), issues `fence(release)`, writes non-atomic `*d1 = 1`, and stores `seq = 2` (`release`), while reader `P1` loads `s1 = seq` (`acquire`), reads non-atomic `r1 = *d1`, issues `fence(acquire)`, and loads `s2 = seq` (`relaxed`). `herd7 -cat rc11.cat support/C-seqlock-na-race.litmus` flags **`Undef`** (`States 6`, `Observation Sometimes 2 9`), because when `P1` reads `s1 = 0` before `P0`'s stores, `P1`'s non-atomic read `*d1` has no `hb` edge relative to `P0`'s concurrent `*d1 = 1` write.
   - Replacing `d1, d2` with `atomic_int` accessed via `memory_order_relaxed` (`support/C-seqlock.litmus`) yields **`Observation C-seqlock Never 0 18` with zero `Undef`**, proving that when `1:s1=0 /\ 1:s2=0`, the `Acquire` fence between `r1, r2` and `s2` prevents observing `1:r1=1 /\ 1:r2=0`.

---

### 2. Hardware Weak Memory Models (`x86-TSO` and `Armv8`) and Mixed-Size Semantics

**Basis: source + execution (`herd/herdtools7` `9574394fc4b2` `herd/libdir/{x86tso.cat,aarch64.cat,aarch64hwreqs.cat,aarch64fences.cat}`, Owens et al. CACM 2010, Pulte et al. POPL 2018 DOI `10.1145/3158107`, Flur et al. POPL 2017 DOI `10.1145/3009837.3009839`, `support/AArch64-mixed-mp.litmus`, `support/X86-mixed-sbf.litmus`).**

| Hardware Model | Operational Formulation | Axiomatic (`cat`) Formulation (`herdtools7` `9574394fc4b2`) | Mixed-Size Variant (Flur et al. POPL 2017; `herd7 -variant mixed`) | Mechanization Status |
| :--- | :--- | :--- | :--- | :--- |
| **`x86-TSO`** | Shared coherent memory $M$ plus per-hardware-thread FIFO store buffer $B_t$; reads check $B_t$ before $M$ (`rfi`), `MFENCE` and `LOCK` RMWs drain $B_t$ | `herd/libdir/x86tso.cat`: `uniproc` (`acyclic(po-loc \| rf \| fr \| co)`), atomic RMW (`rmw & (fre; coe) = 0`), and `ghb` acyclicity (`po \ (W * R)`, `mfence`, `locked`, `rfe`, `fr`, `co`) | Byte-granular store-buffer forwarding: a 2-byte load (`movw (x), %bx`) after a 1-byte store (`movb $1, (x)`) forwards byte 0 from the store buffer and reads byte 1 from memory (`support/X86-mixed-sbf.litmus`: `Always 2 0`) | HOL4 (Owens et al. CACM 2010); Coq (`CompCertTSO`, `weakmemory/imm` `src/hardware/TSO.v`); Lean 4.34.1 (`anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`) |
| **`Armv8` (ARMv8.0–8.3)** | **Flat operational model** (Pulte et al. POPL 2018): explicit per-thread instruction trees with out-of-order issue/commit and a single flat multi-copy-atomic (`MCA`) storage subsystem | `herd/libdir/aarch64.cat` + `aarch64hwreqs.cat`: `internal` (`po-loc \| rf \| fr \| co` acyclic), `external` (`irreflexive(tc(hw-reqs \| obs))`), and `atomic` (`rmw & (fre; coe) = 0`), where `bob` orders `dmb.full`, `R ->dmb.ld M`, `W ->dmb.st W`, `M ->po L`, `(A \| Q) ->po M`, and **`L ->po A`** (excluding `L ->po Q`!) | Decomposes multi-byte reads/writes into per-byte elementary events coupled by single-copy-atomic (`sca`) coherence groups (`support/AArch64-mixed-mp.litmus`: two `STRB` stores before `STLR` cannot be partially observed after `LDAR` + `LDRH`, `Never 0 5`) | Lem / HOL4 / Coq (Pulte et al. POPL 2018 proves Flat $\iff$ axiomatic MCA for uniform-size ARMv8.0); Coq (`weakmemory/imm` `src/hardware/Arm.v`) |

---

### 3. Hardware Mapping Proofs (`IMM` to `x86-TSO` and `Armv8`) and `rustc` Lowering Alignment

**Basis: source (`weakmemory/imm` at `4ca191b072df081dd3a6d9aa755959dc901b1bd0`, `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`, `llvm/llvm-project` at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).**

In `weakmemory/imm` (`4ca191b072df081dd3a6d9aa755959dc901b1bd0`), the end-to-end compilation correctness from `RC11` through `IMM` (`src/c11/C11ToImm.v`) to hardware is proved in Coq across two backend modules:

| Rust / LLVM Atomic Construct | `x86-64` Lowering (`rustc 1.99.1`) | `IMM -> x86-TSO` Proof (`src/hardware/immToTSO.v:897-906`) | `AArch64` Lowering (`rustc 1.99.1` Baseline / `+lse` / `+rcpc`) | `IMM_s -> ARMv8` Proof (`src/hardware/imm_sToARM.v:246-328`) |
| :--- | :--- | :--- | :--- | :--- |
| **`load(Relaxed)`** | `mov` | Proven (`R_rlx` $\mapsto$ TSO read) | `ldr` | Proven (`R_rlx` $\mapsto$ ARM plain read) |
| **`load(Acquire)`** | `mov` | Proven (`R_acq` $\mapsto$ TSO read; TSO preserves `R ->po M`) | `ldar` (baseline) / **`ldapr` (`+rcpc`)** | **`imm_sToARM.v` proves `ldar` (`A`); does NOT model `ldapr` (`Q` in `aarch64.cat`)!** |
| **`load(SeqCst)`** | `mov` | Proven **assuming** `SeqCst` stores use `xchg` (or `mfence` between SC store and SC load; `immToTSO.v:897`) | `ldar` (even when `+rcpc` is enabled!) | Proven in `IMM_s_psc_consistent` (`imm_sToARM.v:246-254`) via `[L]; po; [A]` in `bob` |
| **`store(Relaxed)`** | `mov` | Proven (`W_rlx` $\mapsto$ TSO write) | `str` | Proven (`W_rlx` $\mapsto$ ARM plain write) |
| **`store(Release)`** | `mov` | Proven (`W_rel` $\mapsto$ TSO write; TSO preserves `M ->po W`) | `stlr` | Proven (`W_rel` $\mapsto$ `stlr` `L`; `M ->po L` in `bob`) |
| **`store(SeqCst)`** | `xchg` (implicitly locked) | Proven (`W_sc` $\mapsto$ locked RMW / `xchg` flushing store buffer) | `stlr` | Proven when paired with `ldar` (`A`) for `load(SeqCst)` (`[L]; po; [A]`) |
| **`fetch_add` / RMW (`Relaxed` / `AcqRel` / `SeqCst`)** | `lock xadd` / `lock cmpxchg` | Proven (`RMW` $\mapsto$ TSO locked RMW) | LL/SC loop (`ldxr`/`stxr`, `ldaxr`/`stlxr`) or **LSE (`ldadd`, `ldaddal`, `casal`)** | **`imm_sToARM.v` proves LL/SC (`ldxr`/`stxr` with `ctrl;isb` or `ldaxr`/`stlxr`); LSE single-instruction RMWs are assumed equivalent to atomic `(R, W)` pairs** |
| **`fence(Acquire)` / `fence(Release)` / `fence(AcqRel)`** | Compiler barrier only (no opcode) | Proven (TSO already enforces `R ->po M` and `M ->po W`) | `dmb ishld` (`Acquire`) / `dmb ish` (`Release`, `AcqRel`) | Proven (`F_acq` $\mapsto$ `dmb.ld`, `F_rel`/`F_acqrel` $\mapsto$ `dmb.sy`/`dmb.ish`) |
| **`fence(SeqCst)`** | `lock orl $0, -64(%rsp)` (or `mfence`) | Proven (`F_sc` $\mapsto$ `mfence` or locked RMW on stack slot) | `dmb ish` | Proven in `IMM_s_psc_consistent` (`F_sc` $\mapsto$ `dmb.sy`/`dmb.ish`) |

**What `IMM` Proves vs. What Must Be Discharged in a Verified `rustc` Backend:**
1. **`LDAPR` (`+rcpc`) Soundness Boundary:** Because `rustc` on `ARMv8.3+` (`+rcpc`) lowers `Ordering::Acquire` loads to `LDAPR` (`Q`) and `Ordering::SeqCst` loads to `LDAR` (`A`), `[L]; po; [A]` holds for `SeqCst` store $\to$ `SeqCst` load (`STLR` $\to$ `LDAR`), while `(A | Q) ->po M` and `M ->po L` hold for `Release`/`Acquire` message passing (`STLR` $\to$ `LDAPR`). However, `STLR` (`Release`) followed by `LDAPR` (`Acquire`) in program order is **not** ordered by `bob` (`SB-STLR-LDAPR` is `Sometimes` in `aarch64.cat`). This matches `RC11`/`C++20` (where a `Release` store followed by an `Acquire` load does not prevent store buffering), so `LDAPR` is sound for `Ordering::Acquire` under `RC11`/`C++20`, even though `weakmemory/imm`'s `imm_sToARM.v` predated `ARMv8.3-RCpc` and mapped both `Acquire` and `SeqCst` loads to `LDAR`.
2. **x86-64 `LOCK ORL $0, -64(%rsp)` for `fence(SeqCst)`:** LLVM lowers `fence seq_cst` on x86-64 to a locked `OR` of `0` against a scratch red-zone/stack offset rather than `MFENCE`. Under `x86tso.cat`, any `locked` RMW flushes the processor's store buffer identically to `mfence`, provided the target stack offset is valid, aligned, and disjoint from non-atomic data races (`-64(%rsp)` below the frame pointer).

---

### 4. Compiler Optimizations Under Weak Memory: Counterexamples and Sound Frameworks

**Basis: literature + source (`CompCertTSO` JACM 2013 DOI `10.1145/2487241.2487248`, `CASCompCert` PLDI 2019 DOI `10.1145/3314221.3314604`, `Promising 2.0` PLDI 2020 DOI `10.1145/3385412.3386010`, Cho et al. TOPLAS 2022 DOI `10.1145/3527633`).**

#### 4.1 Published Counterexamples to Naive Sequential Optimizations in Concurrent Code
1. **Speculative Store / Unconditional Register Promotion Across Loops (C++20 / `RC11` / `TSO`):** Promoting a shared variable `*p` into a register before a loop and writing it back unconditionally after the loop (`r = *p; while (...) { ... } *p = r;`) introduces a synthetic store on paths where the source never wrote `*p`, creating a data race with concurrent readers (`Boehm, PLDI 2005`).
2. **Spurious Load Introduction on Potentially Racing Locations:** Introducing a dead non-atomic load `let _ = *p;` (e.g., via speculative `Select` lowering or loop-invariant hoisting before a guard check) introduces immediate data-race UB in C++20/`RC11` if another thread concurrently writes `*p`.
3. **Roach-Motel Movement *Out* of Critical Sections:** Moving memory accesses *into* a lock/acquire-release critical section (`Acquire` $\downarrow$, `Release` $\uparrow$) is sound because it only adds synchronization, whereas hoisting a load above an `Acquire` operation or sinking a store below a `Release` operation breaks mutual exclusion and message passing.
4. **Global Value-Range Analysis & Thread Inlining in `Promising 1.0` (Kang et al. POPL 2017 $\to$ Lee et al. PLDI 2020):** In `Promising 1.0`, a thread could certify a future promise using any sequence of future thread-local steps. Merging two threads (`sequentialization`) or adding a global value-range invariant could invalidate a certification path that relied on an intermediate write, making `Promising 1.0` unsound for thread inlining and global dead-code elimination. `Promising 2.0` (Lee et al., PLDI 2020) solved this by restricting certification to **capped timestamp intervals** (`cap_view`), proving soundness of register promotion, global value-range optimizations, and thread sequentialization in Coq (`kaist-cp/promising2-coq`).
5. **Load-to-Store Reordering on `Relaxed` Atomics in `RC11`:** Reordering `r1 = x.load(Relaxed); y.store(1, Relaxed)` to `y.store(1, Relaxed); r1 = x.load(Relaxed)` is **unsound under `RC11`** (because in `LB-data`, pairing `y.store(1); r1 = x.load()` with `r0 = y.load(); x.store(r0)` produces `r0 = 1 /\ r1 = 1`, which violates `RC11`'s `acyclic(po | rf)`), whereas it is **sound under `IMM` and `Promising 2.0/2.1`** when `y.store(1)` has no syntactic data/control dependency on `r1`.

#### 4.2 Structure of Sound Weak-Memory Compiler Proofs (`CompCertTSO`, `CASCompCert`, `Promising 2.0`, `TOPLAS 2022`)
| Framework | Memory Model | Proof Architecture | Verified Optimizations |
| :--- | :--- | :--- | :--- |
| **`CompCertTSO`** (`Ševčík et al., JACM 2013`, Coq) | `x86-TSO` (single-copy atomic store buffers) | Thread-local buffered simulation + whole-system TSO trace composition; fence elimination phrased over unbuffered/buffered local states | Register allocation, CSE, constant propagation, tailcalls, and redundant fence elimination on x86 |
| **`CASCompCert`** (`Jiang et al., PLDI 2019`, Coq) | Share-memory concurrency with `CAS`/lock footprints | Footprint-preserving open simulation (`reachability` + ownership transfer at `CAS`/lock boundaries) | CompCert backend pipeline for concurrent C with inline assembly / `CAS` primitives |
| **`Promising 2.0 / 2.1`** (`Lee et al., PLDI 2020`, `kaist-cp/promising2-coq`) | Operational timestamped views + capped certification | Local thread simulation preserving promise-certification obligations + adjacent step reordering/elimination lemmas | All single-instruction eliminations/merges, `Relaxed` reorderings, register promotion, and thread sequentialization |
| **Sequential Reasoning for Optimizing Compilers** (`Cho et al., TOPLAS 2022`, Coq) | `Promising 2.0` / `RC11` | **Theorem (Soundness of Sequential Optimizations):** Any optimization validated against a **sequential** non-deterministic semantics (where synchronization operations are modeled as unknown external calls that may read/write non-local memory) is automatically sound under weak memory, **provided** it does not introduce new uncertified writes (`no thin-air promises`) | Enables reusing purely sequential middle-end pass proofs (`SROA`, `GVN`, `DCE`, `InstCombine` on local `alloca`s and `noalias` references) without Mentioning timestamps or execution graphs! |

---

### 5. Embedding Per-Function Sequential Proofs (`DRF-SC`, `Local DRF`, and Aliasing Transfer)

**Basis: literature + source (`Local DRF` PLDI 2018 DOI `10.1145/3192366.3192384`, Cho et al. TOPLAS 2022 DOI `10.1145/3527633`, `RustBelt Meets Relaxed Memory` POPL 2020 DOI `10.1145/3371102`, `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`).**

For a verified Rust compiler and verifier (such as Anneal) where 99%+ of functions and middle-end passes are verified against a **sequential** operational semantics (`MonoMIR` / `AnLLVM`):

1. **Global `DRF-SC` vs. `Local DRF` (`LDRF`):**
   - Classical `DRF-SC` (Batty et al. POPL 2011; Lahav et al. PLDI 2017) is an all-or-nothing whole-program property: if the *entire* program has no `Relaxed` atomics and no data races, its weak-memory executions coincide with `SC`. A single `AtomicUsize::fetch_add(1, Relaxed)` statistics counter anywhere in the binary invalidates global `DRF-SC`!
   - **Local DRF (`LDRF`, Dolan et al. PLDI 2018; Cho et al. TOPLAS 2022)** localizes `SC` and sequential reasoning to **specific memory locations $L_{\text{sync}}$**: for any execution where all conflicting accesses to locations in $L_{\text{sync}}$ are ordered by `happens-before` (`Release`/`Acquire` or `SeqCst` synchronization), every read of $x \in L_{\text{sync}}$ observes the immediately preceding `hb`-visible write to $x$, **regardless of arbitrary `Relaxed` atomic races on disjoint locations $y \notin L_{\text{sync}}$**.
2. **Exact Conditions Under Which Sequential Per-Function Proofs Transfer to Weak Memory:**
   Combining **Tree Borrows** (`S6`), **View-Indexed Separation Logic** (`iRC11` / `RustBelt Meets Relaxed Memory` POPL 2020), and **Cho et al.'s Sequential Optimization Theorem** (TOPLAS 2022) yields a four-part transfer contract:
   - **Condition A (Exclusive `&mut T` where `T: Unpin` and Stack Locals):** While a thread holds a protected `Unique`/`Active` `&mut T` (`T: Unpin`) or an unescaped stack allocation, any concurrent read or write by another thread is a data race (and `ProtectedDisabled` UB). By `LDRF` and Cho et al. (TOPLAS 2022), sequential verification and sequential `AnLLVM` optimizations (`SROA`, `Mem2Reg`, `DSE`, `GVN`) over those locations are unconditionally sound under weak memory.
   - **Condition B (Immutable `&T` where `T: Freeze`):** While a thread holds a protected `Frozen` `&T` (`T: Freeze`), any concurrent write is UB; concurrent reads commute under every weak-memory model (`RC11`, `IMM`, `PS 2.1`, `x86-TSO`, `Armv8`), so `noalias` + `readonly` load-forwarding and CSE transfer unchanged.
   - **Condition C (Ownership Transfer Across Threads via `Release`/`Acquire`):** Whenever an owned resource (`Box<T>`, `&mut T`, or an `UnsafeCell` payload inside `Mutex<T>`, `RwLock<T>`, `Channel<T>`, or `Arc<T>`) is transferred from thread $T_1$ to thread $T_2$, $T_1$'s last access must be `po`-followed by a `Release` store/RMW (or `fence(Release)` + atomic store) that `rf`-synchronizes with $T_2$'s `Acquire` load/RMW (or atomic load + `fence(Acquire)`). As proved in `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal` (`mp_release_acquire_sound_on_x86_and_arm`), this establishes $(w_{\text{data}}, r_{\text{data}}) \in \text{hb}$, transferring $T_1$'s post-state directly into $T_2$'s sequential pre-state.
   - **Condition D (Deallocation Synchronization):** Reclaiming shared memory (`Arc::drop`, epoch/RCU reclamation) requires a physical `Release`/`Acquire` (or `SeqCst` fence in RCU) synchronization chain from **every** prior reader/writer thread to the deallocating thread (`GPS_vSP_dealloc` in `iris/gpfsl@48b7183f`; `atomic::fence(Acquire)` in `library/alloc/src/rcs/arc.rs`), ensuring no buffered hardware read/write executes after `dealloc`.

---

### 6. Availability of Concurrency Models In or Near Lean 4

**Basis: source (`weakmemory/imm` at `4ca191b072df081dd3a6d9aa755959dc901b1bd0`, `kaist-cp/promising2-coq`, `iris/gpfsl` at `48b7183f1b91f7cc53cfdab16e21387e9bfe9c14`, `joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f`).**

| Model / Framework | Upstream Prover & Repository | Size & Axiom Status | Availability In or Near Lean 4 (`v4.34.1`) |
| :--- | :--- | :--- | :--- |
| **`IMM` (`RC11 -> IMM -> x86-TSO / ARMv8`)** | Coq (`weakmemory/imm` `4ca191b072df`) | `~45,000` LOC Coq (`v8.9–8.16`) using `hahn` relational algebra library | Not ported to Lean 4 in full; relational graph axioms (`hb`, `mo`, `rf`, `bob`, `psc`) are first-order relations over finite event sets and embed cleanly into Lean 4 (`anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`) |
| **`Promising 2.0 / 2.1`** | Coq (`kaist-cp/promising2-coq`) | `~55,000` LOC Coq | Not in Lean 4; Cho et al. (TOPLAS 2022) metatheorem allows keeping middle-end pass proofs in Lean 4 purely sequential |
| **`iRC11` / `ORC11` / `GPFSL`** | Rocq (`iris/gpfsl` `48b7183f1b91`, `iris/lambda-rust` `186900b2cf94`) | `~35,000` LOC Rocq/Iris | `iris-lean` (`81bc350`) provides BI/CMRA foundations in Lean 4, without `GPFSL` view-indexed `vProp` |
| **Anneal Weak-Memory & Hardware Lowering Bridges** | **Lean `4.34.1` (`5045d0056413`)** | `support/track7_memory_ct_weakmem_elf_probe.lean` (`774` lines) + `support/round2_track6_probe.lean` (`545` lines) in `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`; zero `sorryAx` | **Directly available in Lean 4.34.1** (`mp_release_acquire_sound_on_x86_and_arm`, `rmw_fetch_add_exclusivity_and_mo_total`, `sb_seqcst_forbids_both_zero_on_x86_and_arm`) |

## Boundaries

1. **No Unified Weak-Memory + Tree Borrows Mechanization (**unknown** in published literature):** While `Local DRF` and `iRC11` justify transferring sequential ownership of `&mut T` (`Unique`) and `&T` (`Frozen`) across `Release`/`Acquire` synchronization boundaries, no published theorem or mechanization combines Tree Borrows' lazy `Reserved -> Active` state transitions or `expose_provenance` wildcard tracking with `RC11`, `IMM`, or `Promising 2.0/2.1` on unsynchronized shared locations.
2. **Mixed-Size Atomics in `IMM` and `Promising` (`unsupported` at source/IR level):** Although `herd7 -variant mixed` (`aarch64.cat` and `x86-64`) defines hardware mixed-size coherence (`support/AArch64-mixed-mp.litmus` and `support/X86-mixed-sbf.litmus`), Rust (`atomic.rs:42-55`), `RC11`, `IMM`, and `Promising 2.0/2.1` all treat unsynchronized overlapping mixed-size atomic accesses as Undefined Behavior.
3. **`ARMv8.3-RCpc` (`LDAPR`) and `ARMv8.1-LSE` in `weakmemory/imm` (`not examined` in `imm_sToARM.v`):** The upstream Coq proof in `weakmemory/imm` (`4ca191b072df081dd3a6d9aa755959dc901b1bd0`, `src/hardware/imm_sToARM.v`) maps all acquire and SC reads to `LDAR` (`A`) and models RMWs via `LDXR`/`STXR` LL/SC pairs; extending the Coq proof to `LDAPR` (`Q`) for `Ordering::Acquire` and single-instruction LSE atomics (`LDADDAL`, `CASAL`) requires discharging their `aarch64hwreqs.cat` `bob` and `rmw` equivalences explicitly.
4. **Consume Ordering (`memory_order_consume`):** Rust omits `Ordering::Consume` entirely (`library/core/src/sync/atomic.rs`), and C++20 (`N4868`) discourages it; pointer-dependency preservation (`[[carries_dependency]]` / Linux kernel `rcu_dereference` via `READ_ONCE`) relies on hardware address dependencies (`addr` in `aarch64.cat`) outside standard Rust `Ordering`.

## Evidence

- **Rust `1.99.1` Concurrency and Volatile Specifications (`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `library/core/src/sync/atomic.rs:25-155` (C++20 access-based atomic model, mixed-size atomic UB restriction, lock-free vs. wait-free guarantees) and `library/core/src/sync/atomic.rs:3820-3950` (`fence` and `compiler_fence`).
  - `library/core/src/ptr/mod.rs:1950-2110` (`read_volatile` and `write_volatile` contracts and data-race caveats).
  - `src/tools/miri/src/concurrency/data_race.rs` (Miri's C++20 release/acquire vector-clock detector).
- **MiniRust Concurrent Memory Specification (`minirust/minirust` at `063d784186d3252bee242217f218223205c0b568`):**
  - `spec/mem/concurrent.md:1-177` (`AtomicMemory<M>` race detector over sequential `Memory`).
- **Hardware and Axiomatic `.cat` Models (`herd/herdtools7` at `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`, `herd7` `7.58`):**
  - `herd/libdir/c11_orig.cat`, `herd/libdir/rc11.cat`, `herd/libdir/x86tso.cat`, `herd/libdir/aarch64.cat`, `herd/libdir/aarch64hwreqs.cat:122-138`, `herd/libdir/aarch64fences.cat`.
- **Mechanized Weak-Memory Compilation and Optimization Literature:**
  - `weakmemory/imm` at `4ca191b072df081dd3a6d9aa755959dc901b1bd0` (POPL 2019 DOI `10.1145/3290382`): `src/imm/Imm.v`, `src/c11/C11ToImm.v`, `src/hardware/immToTSO.v:897-906`, `src/hardware/imm_sToARM.v:246-328`.
  - Lahav, Vafeiadis, Kang, Hur & Dreyer, *Repairing Sequential Consistency in C/C++11* (`RC11`, PLDI 2017, DOI `10.1145/3062341.3062352`).
  - Kang et al. (`Promising 1.0`, POPL 2017, DOI `10.1145/3009837.3009850`) and Lee, Cho, Podkopaev, Chakraborty, Hur, Lahav & Vafeiadis, *Promising 2.0: Global Optimizations in Relaxed Memory Concurrency* (PLDI 2020, DOI `10.1145/3385412.3386010`; `kaist-cp/promising2-coq`).
  - Pulte, Flur, Will, French, Norton & Sewell, *Simplifying ARM Concurrency: Multicopy-Atomic Axiomatic and Operational Models for ARMv8* (POPL 2018, DOI `10.1145/3158107`) and Flur et al., *Mixed-Size Concurrency: ARM, POWER, C/C++11, and SC* (POPL 2017, DOI `10.1145/3009837.3009839`).
  - Ševčík, Vafeiadis, Zappa Nardelli, Jagannathan & Sewell, *CompCertTSO: A Verified Compiler for Relaxed-Memory Concurrency* (JACM 2013, DOI `10.1145/2487241.2487248`).
  - Jiang, Liang, Xiao, Zha & Feng, *Towards Certified Separate Compilation for Concurrent Programs* (`CASCompCert`, PLDI 2019, DOI `10.1145/3314221.3314604`).
  - Dolan, Sivaramakrishnan & Madhavapeddy, *Bounding Data Races in Space and Time* (`Local DRF`, PLDI 2018, DOI `10.1145/3192366.3192384`).
  - Cho, Lee, Hur & Kang, *Sequential Reasoning for Optimizing Compilers Under Weak Memory Concurrency* (TOPLAS 2022, DOI `10.1145/3527633`).
- **Preserved Package Support Artifacts (`support/`):**
  - [`support/LB-data.litmus`](support/LB-data.litmus): C11 load-buffering with data dependency discriminating `c11_orig.cat` (`Sometimes`) from `rc11.cat` (`Never`).
  - [`support/C-seqlock.litmus`](support/C-seqlock.litmus) and [`support/C-seqlock-na-race.litmus`](support/C-seqlock-na-race.litmus): C11 seqlock litmus tests contrasting race-free `Relaxed` atomic payload reads (`Never`, no `Undef`) against racy non-atomic payload reads (`Undef`).
  - [`support/AArch64-mixed-mp.litmus`](support/AArch64-mixed-mp.litmus) and [`support/X86-mixed-sbf.litmus`](support/X86-mixed-sbf.litmus): Mixed-size AArch64 message-passing (`STRB` $\times 2$ + `STLR` vs. `LDAR` + `LDRH`) and x86-64 store-buffer forwarding (`movb` $\to$ `movw`) litmus tests.
  - [`support/concurrency_models_matrix.json`](support/concurrency_models_matrix.json): Machine-readable summary of `herd7` (`7.58`) verification outputs on all five litmus tests.

## Revalidation

1. **Replay the Five `herd7` Concurrency Discriminator Litmus Tests (`support/`):**
   Using `herd7` (`7.58+`, `herd/herdtools7` at `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`):
   ```bash
   herd7 -cat c11_orig.cat support/LB-data.litmus
   herd7 -cat rc11.cat support/LB-data.litmus
   herd7 -cat rc11.cat support/C-seqlock.litmus
   herd7 -cat rc11.cat support/C-seqlock-na-race.litmus
   herd7 -cat aarch64.cat -variant mixed support/AArch64-mixed-mp.litmus
   herd7 -variant mixed support/X86-mixed-sbf.litmus
   ```
   Verify that the `States`, `Observation`, and `Undef` outputs match `support/concurrency_models_matrix.json`.
2. **Revalidate Lean 4 Weak-Memory Lowering Theorems (`anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`):**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- lean reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal/support/track7_memory_ct_weakmem_elf_probe.lean
   anneal-lean-run --mode file --concurrency 4 -- lean reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal/support/round2_track6_probe.lean
   ```
   Confirm exit code `0` and zero `sorryAx` for `mp_release_acquire_sound_on_x86_and_arm`, `rmw_fetch_add_exclusivity_and_mo_total`, and `sb_seqcst_forbids_both_zero_on_x86_and_arm`.
3. **Diff `rustc` Atomic Lowering When Upgrading Toolchains:**
   Check `library/core/src/sync/atomic.rs` and `compiler/rustc_codegen_llvm/src/intrinsic.rs` (or `llvm-project/llvm/lib/Target/{AArch64,X86}/`) to confirm whether `Ordering::Acquire` / `Ordering::SeqCst` / `fence(SeqCst)` lowerings change on `x86_64` or `aarch64`.
