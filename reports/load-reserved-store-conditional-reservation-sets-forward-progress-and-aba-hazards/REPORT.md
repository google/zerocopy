# Load-Reserved / Store-Conditional Semantics: Reservation Sets, Forward Progress, Compiler Lowering, and ABA Hazards

## Summary

Verifying concurrent Rust and OS-kernel synchronization primitives built over Load-Reserved / Store-Conditional (`LR`/`SC` in RISC-V `Zalrsc`/RVWMO and `LDXR`/`LDAXR`/`STXR`/`STLXR` in Armv8-A) requires discharging three orthogonal specification obligations that naive cache-line models and C11/RC11 CAS abstractions conflate:

1. **Exact Safety Abstraction via Minimal Byte-Overlap Clearing plus Demonic Spurious Failure:** Modeling reservation tracking as a fixed cache-line granule (such as a 64-byte block) is **unsound in both directions**. On RISC-V (`Zalrsc` `[#norm:sc_other_device_write_fail]`), a non-hart peripheral or DMA write to a *different* word inside the same 64-byte reservation set is **not** required to invalidate the reservation, so `SC` is still architecturally permitted to succeed; conversely, Armv8-A allows the Exclusives Reservation Granule (`CTR_EL0.ERG`) to span up to 2048 bytes and RISC-V `Zalrsc` permits arbitrarily large hart-coherent reservation sets, allowing stores outside a 64-byte block to clear reservations. The sound two-sided safety abstraction tracks only the exact accessed byte interval `[paddr, paddr + width)` for **mandatory invalidation** (coherent cross-hart stores, overlapping device/DMA writes to `LR`'s bytes, local `SC`/`CLREX`, and Armv8 `ERET`) paired with an **unconstrained demonic `spuriousFail : Bool` input** on every `SC`/`STLXR`.
2. **Isolation of Forward-Progress Liveness (`ConstrainedLrScLoop` + Granule Disjointness):** Because demonic `spuriousFail` admits infinite failure loops at the safety layer, proving lock-freedom of `compare_exchange` or emulated AMOs requires proving separately that generated machine code satisfies architectural constrained-loop criteria. Under RISC-V `Zalrsc`, eventual success is guaranteed **only** inside constrained loops of at most 16 sequential instructions over base integer (`I`/`E`/`C`) ops containing zero intervening loads, stores, backward branches, `JALR`, `FENCE`, or `SYSTEM` instructions, matching the effective address and width of `LR` on an `RsrvEventual` PMA region—forcing LLVM (`AtomicExpandPass`) to hoist release barriers *above* `LR` on weak CAS and defer 32/64-bit `cmpxchg` loops until after register allocation so stack spills never enter the window.
3. **Erasure of Write-History Detection Across `CAS` Retries (ABA & Ordering Boundaries):** While a *single* unbroken hardware `LR`–`SC` pair rejects an $A \to B \to A$ write-back because the intermediate store clears the reservation, lifting `LR`/`SC` to Rust `core::sync::atomic` (`compare_exchange_weak` and `try_update`/`fetch_update`) **destroys write-history sensitivity across loop iterations**: any spurious `SC` failure restarts the loop with a fresh `LR` that observes recycled pointer `A` and succeeds on stale node invariants. Moreover, Linux kernel `cmpxchg` macros jump past trailing barriers on comparison mismatch (`Ordering::Relaxed` failure), making them unsound drop-ins for C11/RC11/Rust `Acquire`/`SeqCst` failure orderings, and baseline RV64GC (`Zalrsc`) lacks 128-bit `LR`/`SC` (requiring `Zacas` `amocas.q` or 64-bit packed `(gen, idx)` arena handles).

## Applicability

This report governs formal hardware/ISA modeling, compiler backend verification, and unsafe lock-free Rust design for targets lowering `core::sync::atomic` onto LL/SC primitives. The nine subjects in `REPORT.json` form a layered refinement stack:

- **Normative ISA Specifications and Executable Semantics (`riscv/riscv-isa-manual` at `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `riscv/sail-riscv` at `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`, and `rems-project/sail-arm` at `5416ef6b43e9527c38dc71fb752259c1d01a47e1` alongside ARM DDI 0487):** Define architectural reservation sets, exclusive monitors, `CTR_EL0.ERG`, ordering annotations (`aq`/`rl` vs. `LDAXR`/`STLXR`), and constrained-loop forward progress.
- **Compiler & Language Lowering (`rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and `llvm/llvm-project` at `90895e4f8b0f3c50816e7323c91c7a0634fc35b0`):** Define how `Atomic*::compare_exchange`, `compare_exchange_weak`, and `try_update` lower through `atomic_cxchg`/`atomic_cxchgweak`, `AtomicExpandPass`, and target pseudo expanders onto RISC-V and AArch64 LL/SC loops.
- **Kernel & Lock-Free Library Practice (`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854` and `crossbeam-rs/crossbeam` at `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`):** Contrast Linux LKMM `arch_cmpxchg` failure-path ordering and masked sub-word LL/SC loops against RC11/Rust contracts and epoch-reclaimed tagged pointers.
- **Formal Program-Logic & Lean 4 Verification Context (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` plus DOIs `10.1145/3158107`, `10.1145/3314221.3314624`, `10.1145/3458926`, `10.1145/3062341.3062352`, `10.1145/3519939.3523434`, and `10.1109/TPDS.2004.8`):** Ground operational equivalence proofs, RC11 `SeqCst` fixes, and Pass-1-compatible 3-axiom Lean 4 state machines.

This report complements prior corpus coverage of C11/Rust concurrency (`rust-atomics-weak-memory-and-aliasing-operational-models`), multi-target mappings (`weak-memory-concurrency-models-hardware-mappings-and-optimizations`), Tier-1 instruction lowering (`tier1-atomics-and-fences-instruction-lowering`), and DMA double-fetch contracts (`double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`), specializing on **reservation-set state, device/DMA vs. cross-hart asymmetry, constrained-loop liveness, compiler fence/spill traps, and CAS-retry ABA loss**.

## Findings

### 1. Normative Mechanics: RISC-V `Zalrsc` Reservation Sets vs. Armv8-A Exclusive Monitors

`Basis: normative + source`

RISC-V `Zalrsc` and Armv8-A Exclusives both pair a reserving load with a conditional store, yet diverge on five verification-critical invariants:

| Property | RISC-V `Zalrsc` / RVWMO (`zalrsc.adoc`, `sail-riscv`) | Armv8-A / Armv9-A (`sail-arm`, ARM DDI 0487) | Verification Implication |
| :--- | :--- | :--- | :--- |
| **Granule Size** | Implementation-defined **reservation set** $\supseteq$ `[addr, addr + width)` (`zalrsc.adoc:91–93`); bounded to $\le 64\text{ B}$ (`Za64rs`) or $\le 128\text{ B}$ (`Za128rs`, `zalrsc_insts.sail:10–11`). | Local + global exclusive monitors (`v8_base.sail:29053–29096`); `CTR_EL0.ERG` (`v8_base.sail:3851`) in $2^{\text{ERG}+2}$ words ($16\text{ B}..\text{2048 B}$; `0` means $\le 2048\text{ B}$). | Portable code needs `CachePadded` / `ERG` spacing to prevent false-sharing livelock across distinct atomics. |
| **Hart Store vs. Device/DMA** | Peer hart store to **reservation set** *must* fail `SC` (`[#norm:sc_other_hart_store_fail]`, `zalrsc.adoc:118–120`); device/DMA write *must* fail `SC` **only if overlapping `LR`'s exact accessed bytes** (`[#norm:sc_other_device_write_fail]`, `zalrsc.adoc:97–99, 110–114, 120–123`). | Coherent stores or `ClearExclusiveByAddress(paddress, id, size)` clear global monitor (`v8_base.sail:28087, 28353, 28602`) at ERG granularity; non-coherent DMA needs cache maintenance or SMMU coherence. | Treating RISC-V DMA writes as clearing a whole 64 B line falsely excludes legal `SC` successes after adjacent-word DMA writes. |
| **Address / Width Mismatch** | `SC` *may* succeed if target bytes lie in `LR`'s reservation set (`zalrsc.adoc:99–101, rvwmo.adoc:340–343`), forfeiting progress guarantees (`zalrsc.adoc:204–205`). | `AArch64_ExclusiveMonitorsPass` checks VA, local, and global monitors (`v8_base.sail:29083–29094`). Mismatched PA, size, or shareability is `CONSTRAINED UNPREDICTABLE` (store may succeed!). | Verified backends must prove exact `(addr, size)` equality; Armv8 does not guarantee `STXR` rejects size/address mismatches. |
| **Self-Clear & Trap Return** | Any `SC` or `LR` clears hart reservation (`zalrsc.adoc:23–24, 144–146`, `zalrsc_insts.sail:76` `cancel_reservation()`). `mret`/`sret` do **not** clear physical reservations (`zalrsc_insts.sail:32–39`), requiring OS dummy `SC` (`zalrsc.adoc:137–142`). | `AArch64_ExclusiveMonitorsPass` (`v8_base.sail:29091`) and `AArch64_ExceptionReturn` (`ERET`, `v8_base.sail:35713`) unconditionally call `ClearExclusiveLocal(ProcessorID())`; `CLREX` clears manually. | RISC-V OS context-switch proofs must verify a dummy `sc` executes before resuming another task over shared physical addresses; Armv8 `ERET` clears hardware monitors. |
| **Ordering & Status** | `.aq`/`.rl` (`RCsc`); `lr.w` sign-extends on RV64 (`zalrsc.adoc:25–26`); `SC` writes `0` on success, nonzero (`1` or reserved codes, `zalrsc.adoc:62–64`) on fail (`zalrsc_insts.sail:75`). | `LDAXR` (acquire-RCsc) / `STLXR` (release-RCsc); `STXR` sets status `0` on success, `1` on fail; failed store emits no memory write event. | RISC-V `SC` checks must branch on `!= 0` (`bnez`), never `== 1`. Failed `SC`/`STLXR` imposes zero barrier on surrounding plain accesses unless fenced. |

Two normative subtleties in `sail-riscv` (`ec5200bd...`) and `riscv-isa-manual` (`c05f1725...`) dictate operational semantics:
1. **Physical-Address Reservations (`zalrsc_insts.sail:32–39`):** Sail RISC-V tracks physical rather than virtual addresses because *"matching on physical addresses allows as many SC's to succeed as the spec allows,"* avoiding spurious divergences when verifying real silicon.
2. **Failed `SC` Protection Semantics (`zalrsc.adoc:17–22`):** Even on failure (`rd != 0`), `[#norm:sc_retire_permission]` requires `SC` to pass PMP/page-table write permissions and leaves dirty-bit (`D`) updates `UNSPECIFIED`.

### 2. Operational Abstraction Theorem: Minimal Byte-Overlap + Demonic Spurious Failure

`Basis: normative + source + derived`

Lifting ISA reservation state into operational concurrency verifiers (Promising-ARM/RISC-V, DOI `10.1145/3314221.3314624`; Islaris, DOI `10.1145/3519939.3523434`) using a fixed 64-byte granule (`addr & ~63`) breaks soundness in two directions:
- **False Invalidation on Non-Hart DMA:** When a NIC writes descriptor `[0x1008, 0x1010)` while a hart holds `lr.d` on `[0x1000, 0x1008)`, `Zalrsc` `[#norm:sc_other_device_write_fail]` (`zalrsc.adoc:97–123`) permits `SC` to succeed. A fixed 64 B model clears the reservation, falsely hiding post-`SC` states.
- **False Success on Coarse Granules (`ERG` / `Za128rs`):** When peer harts store to `0x1080` (128 B away, inside a 256 B–2048 B Armv8 `ERG` or unconstrained RISC-V granule), a fixed 64 B model falsely guarantees `SC` succeeds and omits `compare_exchange_weak` failure paths.

**Exact Two-Sided Safety Abstraction (`probe_llsc_aba.py`):**
Track per-hart `res[h] : Option (PhysAddr × Width)` with exact byte intervals:
1. `LR(h, pa, w)` sets `res[h] := some (pa, w)`.
2. Cross-hart `Store(h', pa', w')` ($h' \neq h$) clears `res[h]` **iff** `[pa, pa + w)` overlaps `[pa', pa' + w')`.
3. Device `DmaWrite(pa', w')` clears `res[h]` **iff** `[pa, pa + w)` overlaps `[pa', pa' + w')`.
4. `SC(h, pa_sc, w_sc, v, spuriousFail)` unconditionally sets `res[h] := none`, succeeds (writes `v`, returns `0`) iff `res[h] = some (pa, w)`, `(pa_sc, w_sc) == (pa, w)`, and `spuriousFail == false` (with Armv8 mismatched `(pa_sc, w_sc)` raising `CONSTRAINED UNPREDICTABLE` fault).
5. `CLREX`, context switches, and Armv8 `ERET` set `res[h] := none`.

This two-sided model captures every legal hardware granule for safety without introducing false impossibility.

### 3. Constrained Loops, Forward-Progress Liveness, and Compiler Lowering Traps

`Basis: normative + source + derived`

Safety proofs cannot discharge liveness under unconstrained `spuriousFail`. Proving lock-free termination requires checking the five RISC-V constrained `LR`/`SC` loop rules (`zalrsc.adoc:182–281`):
1. **Length (`[#norm:constrained_lrsc_loop_size]`):** At most **16 sequential instructions** in memory ($\le 64$ bytes in RV32/RV64I, bounding I-cache/I-TLB conflicts).
2. **Closed Instruction Set (`[#norm:constrained_lrsc_instruction_set]`, `[#norm:constrained_lrsc_compressed_allowed]`):** Dynamic ops between `LR` and `SC` must belong solely to base `I`/`E` (plus compressed `C`/`Zca`/`Zcb`), **banning** other loads/stores, backward jumps, taken backward branches, `JALR`, `FENCE`, `SYSTEM`, `M`-extension mul/div, and FP ops (`zalrsc.adoc:191–197, 216–224`).
3. **Retry Path (`[#norm:constrained_lrsc_retry_code]`):** Retry branches/jumps back to `LR` obey the same op exclusions.
4. **Target & Region (`[#norm:lrsc_eventuality_region]`, `[#norm:lrsc_same_address_and_size]`):** Exact `(effective_addr, width)` match on `RsrvEventual` memory (`sail-riscv/model/sys/mem.sail:111–114`).
5. **Eventuality Guarantee (`zalrsc.adoc:232–280`):** Guarantees **livelock freedom** (weakened from starvation freedom): either some hart succeeds an `SC`, a peer hart/device writes unconditionally to the reservation set, $H$ branches out, or $H$ traps. Peer loads and `LR`s cannot permanently block progress (`zalrsc.adoc:257–267`).

**Three Compiler Lowering Traps in LLVM (`90895e4f...`) and Linux (`65e4fd94...`):**
- **Fence-Inside-LL/SC Livelock (`AtomicExpandPass.cpp:1678–1689, 1758–1759`):** Sinking a `Release` `fence` between `LR` and `SC` violates `[#norm:constrained_lrsc_instruction_set]` and makes weak CAS fail deterministically (`compare_exchange_weak` never retries). LLVM computes `UseUnconditionalReleaseBarrier = (F->hasMinSize() && !CI->isWeak()) || (CI->isWeak() && TLI->fenceClearsLoadLinkedReservation())` to hoist `emitLeadingFence` *before* `StartBB`.
- **Register-Allocator Spill Hazards (`RISCVISelLowering.cpp:30550–30558, 30662–30674`; `AArch64ExpandPseudoInsts.cpp:241–319, 1720–1745`):** Expanding 32/64-bit CAS before register allocation invites stack spill loads/stores inside `LR`–`SC`. LLVM returns `AtomicExpansionKind::None` in IR and expands CAS post-RA via `expandCMP_SWAP` / `CMP_SWAP_8..128` pseudo-instructions, while converting FP `atomicrmw` ops (`fadd`/`fsub`) to `AtomicExpansionKind::CmpXChg` so FP instructions never enter `LR`–`SC`.
- **Masked Sub-Word Atomics & Intra-Word False Sharing (`RISCVISelLowering.cpp:30669–30673`; `linux/arch/riscv/include/asm/cmpxchg.h:19–58, 133–183`):** Without `Zabha`+`Zacas`, 8/16-bit atomics lower to aligned 32-bit `lr.w`/`and`/`or`/`sc.w` masking loops (`MaskedIntrinsic`), coupling disjoint adjacent fields within the same 4-byte word into a shared reservation granule.

### 4. Soundness Boundaries Between `LR`/`SC`, Linux LKMM, and Rust / RC11 Atomics

`Basis: source + documentation + derived`

Rust's `core::sync::atomic` (`rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `atomic.rs:930–1056, 3059–3415, 3969–4094`) lowers `compare_exchange` and `compare_exchange_weak` onto `intrinsics::atomic_cxchg` / `atomic_cxchgweak` under C++11/RC11 rules (Lahav et al., PLDI 2017, DOI `10.1145/3062341.3062352`), creating two critical seams against Linux LKMM inline assembly:

1. **Failure-Path Ordering (`Linux cmpxchg` vs. Rust `failure: Ordering`):** Linux RISC-V (`cmpxchg.h:209–215, 291–295`) and AArch64 (`atomic_ll_sc.h:256–262, 289–292`) branch immediately past `RISCV_FULL_BARRIER`/`dmb ish` when loaded `!= old`, providing only `Relaxed` failure semantics. Rust `compare_exchange(_, _, SeqCst, Acquire)` requires `Acquire`/`SeqCst` barriers even on failure—enforced in `AtomicExpandPass.cpp:1840–1848` by emitting `emitTrailingFence(FailureOrder)` in `FailureBB` (`RISCVISelLowering.cpp:30540–30541`). Wrapping Linux `cmpxchg` behind a Rust `Acquire`/`SeqCst`-failure API is **unsound**.
2. **Unbalanced Monitor Balance & RC11 `SeqCst` Uniformity:** When comparison fails before `SC`, `NoStoreBB` invokes `emitAtomicCmpXchgNoStoreLLBalance` (`AtomicExpandPass.cpp:1837`) so exclusive monitors do not remain armed across arbitrary user code; and per RC11 (`a-st-ext.adoc:21–23`), all `SeqCst` accesses in a program must use consistent leading/trailing fences or `RCsc` annotations to prevent `IRIW`/`2+2W` SC violations.

### 5. ABA Hazards Across `CAS` Retries and Constructive Lean 4 Mechanization

`Basis: source + derived + execution`

Although an unbroken `LR`–`SC` detects $A \to B \to A$ modifications (`zalrsc.adoc:30–34`), **lifting `LR`/`SC` to `compare_exchange_weak` (`atomic.rs:3123–3132`) or `try_update` (`atomic.rs:3405–3416`) erases write-history detection across retries**: a spurious `SC` failure returns `Err(A)`, prompting the next loop iteration to execute a **fresh `LR`**, observe recycled `A == prev`, and succeed on stale `A.next = B` (`atomic.rs:3108–3114, 3381–3385`).

| Mitigation Pattern | Mechanism & Width | Hardware / Target Support | Verification Invariant |
| :--- | :--- | :--- | :--- |
| **Epoch Reclamation (`crossbeam-epoch`)** | Low alignment-bit tags (`crossbeam-epoch/src/atomic.rs:60–85`: `low_bits`, `compose_tag`, `decompose_tag`) + `&Guard` (`lines 274–280`); delays freeing across 3 global epochs. | Baseline 64-bit `LR.D`/`SC.D` & `LDAXR`/`STLXR`. | `Pinned(g) → A ∉ Freed` (no reachable node reallocated while pinned). |
| **Hazard Pointers (DOI `10.1109/TPDS.2004.8`)** | Publishes `A` to per-thread slot and re-validates `head == A` before reading `A.next`. | Baseline 64-bit `LR.D`/`SC.D` & `LDAXR`/`STLXR`. | Re-check proves $A \in \text{HP}_t$ prior to peer retirement. |
| **Double-Width 128-bit CAS** | `(64-bit ptr, 64-bit monotonic tag)`. | Armv8 `LDXP`/`STXP` (`atomic_ll_sc.h:304–333`) / `CASP`; **RV64GC has NO 128-bit `LR`/`SC`**, requiring `Zacas` `amocas.q` (`cmpxchg.h:330–369`). | Monotonic `tag' = tag + 1` ($< 2^{64}$ wrap bound). |
| **Packed 64-bit `(gen, idx)` Arena** | Packs `(gen : u32, idx : u32)` into one `AtomicU64` (`packHandle`). | **Portable to baseline RV64GC and Armv8** with zero external allocation. | `gen' = gen + 1 < 2^32 ⇒ pack gen' idx ≠ pack gen idx`. |

#### Executable State-Machine Audit & Pass-1-Compatible Lean 4 (`v4.34.1`) Formalization

All four divergences (DMA non-invalidation, `ERG` false sharing, single-window ABA rejection vs. weak-CAS retry corruption, and packed 64-bit `(gen, idx)` handle injectivity) were checked via a standalone Python 3 state-machine script (`/tmp/probe_llsc_aba.py`, `exit 0`). The Lean 4 (`v4.34.1`) module below encodes the same theorems using strictly `prelude` + `Init.*` with zero `sorry` and zero `Classical.choice`:

```lean
-- Self-contained Pass-1-compatible Lean 4 (v4.34.1) model
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic

namespace LlscReservationsAba

structure Reservation where
  addr  : Nat
  width : Nat

structure MemAndHart where
  headVal   : Nat
  slotANext : Nat
  res       : Option Reservation

def intervalsOverlap (a0 w0 a1 w1 : Nat) : Bool :=
  !(Nat.ble (a0 + w0) a1 || Nat.ble (a1 + w1) a0)

def stepLr (st : MemAndHart) (addr width : Nat) : Nat × MemAndHart :=
  let v := match Nat.beq addr 0 with | true => st.headVal | false => st.slotANext
  (v, MemAndHart.mk st.headVal st.slotANext (some (Reservation.mk addr width)))

def stepPeerStore (st : MemAndHart) (addr width newVal : Nat) : MemAndHart :=
  let nextHead := match Nat.beq addr 0 with | true => newVal | false => st.headVal
  let nextSlot := match Nat.beq addr 0 with | true => st.slotANext | false => newVal
  let nextRes := match st.res with
    | none => none
    | some r => match intervalsOverlap r.addr r.width addr width with
      | true => none | false => some r
  MemAndHart.mk nextHead nextSlot nextRes

def stepDeviceDmaWrite (st : MemAndHart) (addr width : Nat) : MemAndHart :=
  let nextRes := match st.res with
    | none => none
    | some r => match intervalsOverlap r.addr r.width addr width with
      | true => none | false => some r
  MemAndHart.mk st.headVal st.slotANext nextRes

def stepSc (st : MemAndHart) (addr width newVal : Nat) (spuriousFail : Bool) : Bool × MemAndHart :=
  let ok := match st.res, spuriousFail with
    | some r, false => Nat.beq r.addr addr && Nat.beq r.width width
    | _, _ => false
  let nextHead := match ok && Nat.beq addr 0 with | true => newVal | false => st.headVal
  let nextSlot := match ok && !(Nat.beq addr 0) with | true => newVal | false => st.slotANext
  (ok, MemAndHart.mk nextHead nextSlot none)

/-- 1. RISC-V DMA asymmetry: disjoint DMA write [8,16) in same 64 B line allows SC on [0,8). -/
theorem riscv_dma_adjacent_word_allows_sc :
    let s1 := (stepLr (MemAndHart.mk 1 2 none) 0 8).2
    let s2 := stepDeviceDmaWrite s1 8 8
    (stepSc s2 0 8 2 false).1 = true := rfl

/-- 2. Unbroken single-window LR-SC rejects A -> B -> A peer writes. -/
theorem single_window_lrsc_rejects_aba (head0 slot0 : Nat) :
    let s1 := (stepLr (MemAndHart.mk head0 slot0 none) 0 8).2
    let s3 := stepPeerStore (stepPeerStore s1 0 8 2) 0 8 head0
    (stepSc s3 0 8 slot0 false).1 = false := by
  dsimp [stepLr, stepPeerStore, stepSc, intervalsOverlap]; rfl

/-- 3. Spurious failure in compare_exchange_weak retries LR and commits ABA dangling node `2`. -/
theorem weak_cas_retry_aba_corrupts_head :
    let s0 := MemAndHart.mk 1 2 none
    let r1 := stepLr s0 0 8
    let sc1 := stepSc r1.2 0 8 2 true
    let sPeer := stepPeerStore (stepPeerStore (stepPeerStore sc1.2 0 8 2) 8 8 999) 0 8 1
    let r2 := stepLr sPeer 0 8
    let sc2 := stepSc r2.2 0 8 s0.slotANext false
    sc1.1 = false ∧ Nat.beq r2.1 r1.1 = true ∧ sc2.1 = true ∧ sc2.2.headVal = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 4. Packed 64-bit `(gen, idx)` handles prevent ABA on baseline RV64GC LR.D/SC.D. -/
def packHandle (gen idx : Nat) : Nat :=
  gen * 4294967296 + (idx % 4294967296)

theorem packed_handle_injective_on_gen (g1 g2 idx : Nat) (hNe : g1 ≠ g2) :
    packHandle g1 idx ≠ packHandle g2 idx := by
  intro hEq; apply hNe; unfold packHandle at hEq
  have h1 : (g1 * 4294967296 + idx % 4294967296) / 4294967296 = g1 := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt (Nat.mod_lt idx (by decide)), Nat.zero_add]
  have h2 : (g2 * 4294967296 + idx % 4294967296) / 4294967296 = g2 := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt (Nat.mod_lt idx (by decide)), Nat.zero_add]
  rw [← h1, ← h2, hEq]

end LlscReservationsAba
```

## Boundaries

- **`known not to apply` — `compare_exchange_weak` / `try_update` preserving hardware `LR`/`SC` ABA immunity:** Retrying after a spurious `SC` failure executes a fresh `LR` and erases intermediate write history (`atomic.rs:3108–3114, 3405–3416`).
- **`known not to apply` — Linux LKMM `arch_cmpxchg` failure branches satisfying Rust `Ordering::Acquire` / `SeqCst` failure contracts:** Linux `cmpxchg.h` and `atomic_ll_sc.h` skip trailing fences on mismatch; LLVM `FailureBB` must emit `emitTrailingFence(FailureOrder)` (`AtomicExpandPass.cpp:1847`).
- **`known not to apply` — Fixed 64-byte reservation-set rules for RISC-V DMA or Armv8 `ERG > 64`:** Over-invalidating on non-overlapping DMA writes breaks `Zalrsc` `[#norm:sc_other_device_write_fail]`, while omitting `ERG ≤ 2048 B` false sharing omits legal spurious failures.
- **`known not to apply` — RISC-V `mret`/`sret` implicitly clearing physical reservations:** Unlike Armv8 `AArch64_ExceptionReturn` (`ERET`), RISC-V requires an explicit kernel dummy `SC` (`zalrsc.adoc:137–142`).
- **`unsupported` — 128-bit `LR`/`SC` on baseline RV64GC (`Zalrsc`):** `Zalrsc` defines only 32-bit `.w` and 64-bit `.d` (`zalrsc_insts.sail:16–22`); 128-bit CAS on RISC-V requires `Zacas` (`amocas.q`).
- **`unsupported` — Atomic RMWs and inline assembly in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** `Trusted.MirSemantics` evaluates sequential MIR and treats unmodeled intrinsics and inline asm as `FaultKind.unsupported`.
- **`not examined` — Hardware transactional memory (`TME`), x86 `LOCK CMPXCHG16B`, GPU scoped SIMT atomics, and Armv9 `FEAT_THE` read-check-write PTE updates:** Out of scope for this LL/SC study.
- **`unknown` — Worst-case livelock hold-off bounds on proprietary out-of-order RV64 silicon:** Public ISA specs mandate eventual progress for constrained loops on `RsrvEventual` memory without disclosing vendor coherence-timer constants under SMT cache contention.

## Evidence

| Subject / Source | Exact Coordinates | Role & Verified Fact |
| :--- | :--- | :--- |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/unpriv/zalrsc.adoc:6–281`, `zaamo.adoc:6–87`, `rvwmo.adoc:114–129, 278–352`, `a-st-ext.adoc:1–26` | `normative`: Reservation set semantics, hart vs. device-write asymmetry, context-switch dummy `SC`, 16-insn constrained loops, RVWMO Atomicity Axiom. |
| `riscv/sail-riscv` | `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`, `model/extensions/A/zalrsc_insts.sail:9–84`, `model/sys/mem.sail:35–59, 111–116` | `source`: 4/8-byte `lrsc_width_valid`, physical-address rationale (`lines 32–39`), unconditional `cancel_reservation()`, `RsrvEventual` PMA. |
| `rems-project/sail-arm` | `5416ef6b43e9527c38dc71fb752259c1d01a47e1`, `arm-v9.4-a/src/v8_base.sail:3845–3857, 12395–12415, 29051–29096, 35686–35714` | `source`: `CTR_EL0.ERG`, `AArch64_SetExclusiveMonitors`, `AArch64_ExclusiveMonitorsPass` (`ClearExclusiveLocal`), `AArch64_ExceptionReturn` monitor clear. |
| `rust-lang/rust` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `library/core/src/sync/atomic.rs:930–1056, 1325–1403, 3059–3415, 3969–4094` | `source`: `compare_exchange`, `compare_exchange_weak`, `try_update` CAS loop, and documented ABA limitations across retries. |
| `llvm/llvm-project` | `90895e4f8b0f3c50816e7323c91c7a0634fc35b0`, `AtomicExpandPass.cpp:1653–1890`, `RISCVISelLowering.cpp:30515–30693`, `AArch64ExpandPseudoInsts.cpp:241–319, 1720–1745` | `source`: `UseUnconditionalReleaseBarrier` hoisting release fences before `StartBB`, `FailureBB` `emitTrailingFence`, post-RA pseudo CAS, FP/sub-word rules. |
| `torvalds/linux` | `65e4fd942f72a9dba0e4e257290c4fa1aa756854`, `arch/riscv/include/asm/cmpxchg.h:19–58, 133–296, 330–369`, `arch/arm64/include/asm/atomic_ll_sc.h:218–334` | `source`: Linux LKMM mismatch fence-skip, masked 32-bit sub-word `lr.w`/`sc.w`, `amocas.q`, and AArch64 `ldxp`/`stxp`. |
| `crossbeam-rs/crossbeam` & `joshlf/anneal` | `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` (`crossbeam-epoch/src/atomic.rs:60–85, 274–280`); `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`TrustedBoundary.lean`, `MirSemantics.lean`) | `source`: Alignment-bit tagged pointers + epoch `&Guard`; Anneal Pass-1 `prelude` + `Init.*` boundary and `MirSemantics` fault classification. |
| Concurrency Literature | DOIs `10.1145/3290384`, `10.1145/3158107`, `10.1145/3314221.3314624`, `10.1145/3458926`, `10.1145/3519939.3523434`, `10.1145/3062341.3062352`, `10.1109/TPDS.2004.8` | `documentation`: Sail ISA models, ARMv8 operational/axiomatic equivalence, Promising-ARM/RISC-V, Armed Cats, Islaris, RC11, Hazard Pointers. |
| Python 3 Model Probe | Self-contained 2-sided reservation & ABA state checker (Python 3.13, `2026-11-20`) | `execution`: Verified `DMA adj word: minimal=True, fixed64=False`; `ERG false share: fixed64=True, minimal_spurious=False`; `single-window SC=False`; `weak-CAS head=B` (`exit 0`). |

## Revalidation

1. **ISA & Sail Diff Check (`< 2s`):** Diff `src/unpriv/zalrsc.adoc` (`riscv/riscv-isa-manual`), `zalrsc_insts.sail` (`riscv/sail-riscv`), and `AArch64_ExclusiveMonitorsPass` / `AArch64_ExceptionReturn` (`rems-project/sail-arm`) against the pinned commits for changes to DMA invalidation, constrained-loop bounds, or monitor clears.
2. **Compiler & Core Atomics Check (`< 2s`):** Inspect `AtomicExpandPass.cpp` (`UseUnconditionalReleaseBarrier`, `emitTrailingFence`) and `RISCVISelLowering.cpp` (`shouldExpandAtomicCmpXchgInIR`) in `llvm/llvm-project`, plus `atomic.rs` (`try_update` / `compare_exchange_weak`) in `rust-lang/rust`.
3. **Standalone Lean 4 (`v4.34.1`) Kernel Check (`< 2s`):** Save the Lean module in **Findings §5** to `/tmp/reval_llsc_aba.lean`, append `#print axioms` for all four theorems (`riscv_dma_adjacent_word_allows_sc`, `single_window_lrsc_rejects_aba`, `weak_cas_retry_aba_corrupts_head`, `packed_handle_injective_on_gen`), and verify `lean -DElab.async=false -Ddebug.skipKernelTC=false /tmp/reval_llsc_aba.lean` exits `0` with zero `sorryAx` and zero `Classical.choice`.
