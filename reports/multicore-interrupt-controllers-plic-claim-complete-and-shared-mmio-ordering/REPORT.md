# Multi-Core Interrupt Controllers (`PLIC` and `GICv3`), Shared MMIO Fence Ordering (`mmiowb`), and Multiprocessor Stack Resource Policy Verification

## Summary

Single-core embedded verification models rely on three assumptions that fail immediately on symmetric multi-core (SMP) SoCs: (1) local interrupt masking (`CPSID I`, `BASEPRI`, or `mstatus.MIE`) serializes shared state without atomic lock words; (2) an interrupt pending at trap entry stays claimable by the trapping core until serviced; and (3) C11/Rust `Acquire`/`Release` atomics order memory-mapped I/O (MMIO) accesses inside spinlocks.

Primary-source analysis of the ratified RISC-V Platform-Level Interrupt Controller specification v1.0.0 (`riscv/riscv-plic-spec@f8ec1b7e9b1a`), the RISC-V ISA manual (`riscv/riscv-isa-manual@6ee57d899702`), ARM GICv3/v4 (`ARM IHI 0069H`), Linux's `irq-sifive-plic.c`, `irq-gic-v3.c`, and RISC-V I/O headers (`torvalds/linux@4405c18c95d2`), `tock/tock` (`ba6aa7edc014`), `seL4/seL4` (`08c7e5fddb31`), `rtic-rs/rtic` (`fed0fa5e9d74`), and the MSRP (`10.1109/REAL.2001.990598`) and MrsP (`10.1109/ECRTS.2013.37`) protocols establishes five verification obligations:

1. **PLIC two-stage gateway/core protocol vs. GICv3 explicit `Active` state:** Unlike ARM GICv3 (which tracks `Inactive`, `Pending`, `Active`, and `Active+Pending` per INTID in hardware, supports 1-of-$N$ SPI affinity routing, and splits priority drop `ICC_EOIR1_EL1` from deactivation `ICC_DIR_EL1`), RISC-V PLIC v1.0.0 supports **multicast notification only** (`riscv-plic.adoc:152–169`) and separates the **Interrupt Gateway** (blocking new requests until completion write, `L106–135`) from the **PLIC Core `IP` bit** (cleared atomically on `CONTEXT_CLAIM` read, `L436–440`).
2. **Threshold-bypass claim inversion (`riscv-plic.adoc:456–457`):** PLIC `threshold` registers filter *notifications* (`EIP`), **not** `CONTEXT_CLAIM` reads (`"the claim operation is not affected by the setting of the priority threshold register"`). When Hart 0 raises `threshold = 3` (for a priority-3 critical-section ceiling) and traps on a priority-5 IRQ, Hart 1 can claim the priority-5 source first, causing Hart 0's `claim` read to pop a **priority-2 pending source (`2 <= 3`)**—violating ceiling exclusivity unless software re-checks `prio[id] > threshold` or masks `IE`.
3. **Silent completion drop and `plic_irq_eoi` TOCTOU / affinity-clobber races (`riscv-plic.adoc:485–487`, `irq-sifive-plic.c:172–215`):** PLIC hardware **silently ignores** any completion write whose source ID is disabled (`IE[ctx][id] == 0`) on the writing context, permanently wedging that source's gateway across *all* harts. Exhaustive BFS exploration proves that reading `enabled` and writing `CONTEXT_CLAIM` *outside* `handler->enable_lock` in `plic_irq_eoi` (`L178–188`) leaves a `2`-state TOCTOU gateway-wedge race and an affinity-restore clobber race under concurrent `plic_set_affinity`; holding `enable_lock` across the entire EOI check-write-restore sequence eliminates all wedges and clobbers (`0` failures).
4. **RVWMO main-memory vs. I/O ordering gap (`fence o, w` / `mmiowb`, `fence w, o`, `fence i, ir`):** RISC-V RVWMO (`rvwmo.adoc:34–40, 279–281`) restricts Preserved Program Order and `.aq`/`.rl` annotations strictly to **regular main memory (`R`, `W`)**. Standard Rust `Ordering::Release` spinlock unlocks (`fence rw, w` / `amoswap.w.rl`) therefore **fail** to order preceding MMIO writes (`O`) before lock release (`W`), letting a second hart's critical-section MMIO write reach the device *before* the first hart's write! Sound SMP MMIO spinlocks require `mmiowb()` = `fence o, w` (`arch/riscv/include/asm/mmiowb.h:10`) before lock release (and `fence r, io` on acquire before relaxed MMIO), alongside `fence w, o` before TX DMA doorbells and `fence i, ir` after RX status/claim reads (`mmio.h:135–137`). Pure 1-hot `W1C` clears (`writel(1 << b)`) commute lock-free across harts (`0/16` clobbers), whereas interleaved `W1C` RMWs clobber interrupts in `12/16` states.
5. **Multi-core Stack Resource Policy (`MSRP` / `MrsP`) requires local ceiling elevation *before* spinlock acquisition:** Extending Baker's single-core SRP (`10.1007/BF00365393`) to multi-core Rust (`RacyCell<T>`) partitions resources into core-local (pure SRP) and global (FIFO/helping spinlocks). Acquiring a global spinlock on core $c$ **must first raise core $c$'s local preemption ceiling** ($\pi_{\text{sys}}^{(c)} \ge \Pi_c(r_{\text{glob}})$); spinning with local ISRs unmasked allows a higher-priority ISR on the *same* core to preempt the lock owner and spin forever (self-deadlock), whereas ceiling-before-spin preserves deadlock freedom, bounded spin delay, and one shared stack per core.

## Applicability

These findings apply to SMP kernels, bare-metal Rust runtimes, device drivers, and formal concurrency models matching the fourteen subjects in `REPORT.json`:

- **Interrupt Controller & ISA Specifications:** Ratified RISC-V PLIC v1.0.0 (`riscv/riscv-plic-spec@f8ec1b7e9b1a92c34af8e0ab7eb33838813785a3`, sources `1..=1023`, `15,872` contexts), RISC-V Unprivileged/Privileged ISA (`riscv/riscv-isa-manual@6ee57d8997021aaa8025e208164763fe12e03c19`, `rv32.adoc` `FENCE` & `rvwmo.adoc` v2.0), and ARM GICv3/v4 (`ARM IHI 0069H`). Excludes RISC-V `AIA` (`APLIC`/`IMSIC`).
- **OS Kernels and Embedded Frameworks:** `torvalds/linux@4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `tock/tock@ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, `tock/tock-registers@86008616e0082f4a75e2cf1b33c94b78cbaf7f5f`, `seL4/seL4@08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, and `rtic-rs/rtic@fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9` (`rtic 2.4.0`).
- **Verification & Scheduling Models:** `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), Baker (`10.1007/BF00365393`), Gai et al. MSRP (`10.1109/REAL.2001.990598`), Burns & Wellings MrsP (`10.1109/ECRTS.2013.37`), and LKMM (`10.1145/3173162.3177156`).
- **Adjacent corpus reports:** Extends single-core coverage in [rtic-srp-priority-ceiling-locks-and-dma-descriptor-ring-isr-handoffs](../rtic-srp-priority-ceiling-locks-and-dma-descriptor-ring-isr-handoffs/REPORT.md), [tock-mmio-w1c-register-bitfields-and-sbi-ffi-noreturn-fallthrough-hazards](../tock-mmio-w1c-register-bitfields-and-sbi-ffi-noreturn-fallthrough-hazards/REPORT.md), [superdense-logical-time-hybrid-synchronous-calculi-and-preemptive-srp-verification](../superdense-logical-time-hybrid-synchronous-calculi-and-preemptive-srp-verification/REPORT.md), and [anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal](../anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal/REPORT.md) to multi-hart interrupt routing, cross-core MMIO fences, and multi-core priority ceilings.

## Findings

### 1. Architectural State Machines: RISC-V PLIC v1.0.0 vs. ARM GICv3/v4

`Basis: normative + source + derived`

#### 1.1 RISC-V PLIC Two-Stage Gateway/Core Automaton (`riscv-plic.adoc:60–515`)

PLIC v1.0.0 (`riscv-plic.adoc:230–276`) maps 32-bit `LW`/`SW`-atomic registers across source priorities (`+0x000004..0x000FFC` for IDs `1..=1023`, `0` reserved; `0` = never interrupt, higher `u32` = higher priority, ties broken by **smaller** ID at `L174–175, 297–299`), pending bits `IP` (`+0x001000..0x00107C`), per-context enables `IE[c]` (`+0x002000 + 0x80 * c`, `c ∈ 0..=15871`), and per-context 4 KiB pages (`+0x200000 + 0x1000 * c`) containing `threshold[c]` (`+0x00`) and non-idempotent `claim/complete[c]` (`+0x04`).

Unlike GICv3, PLIC has no readable `Active` bit array; each source $i$ couples two hardware latches (`L104–136, 433–495`):
- **Gateway (`gw_open[i]`):** Converts wire/MSI assertions into at most one in-flight PLIC request (`gw_open[i] := false; IP[i] := 1`), blocking further requests until completion arrives. Level assertions cannot be retracted once latched in `IP[i]` (`L116–122`); on completion (`gw_open[i] := true`), a still-high level immediately re-asserts `IP[i] := 1`, whereas edge gateways forward a queued count or wait for a new edge (`L123–135`).
- **Core Claim/Complete (`IP[i]`):** `readl(CLAIM[c])` atomically picks $\arg\max_i \{ (\text{prio}[i], -i) \mid \text{IP}[i]=1 \land \text{IE}[c,i]=1 \land \text{prio}[i]>0 \}$ and clears `IP[i] := 0` while `gw_open[i]` stays `false`. `writel(i, CLAIM[c])` re-opens `gw_open[i] := true` **iff `IE[c, i] == 1`** (`L485–487`).
- **Asymmetric Context Offsets (`seL4` `riscv_plic0.h:60–69`):** On SiFive U54-MC / U74-MC, Hart 0 lacks S-mode (context 0 = M-mode only), whereas Harts 1–4 expose both M- and S-mode (contexts 1–8), requiring `PLAT_PLIC_THRES_ADJUST` (`- 0x1000`) instead of `2 * hart + mode`.

#### 1.2 Comparison Against ARM GICv3/v4 (`ARM IHI 0069H`, `irq-gic-v3.c`)

| Dimension | RISC-V PLIC v1.0.0 | ARM GICv3 / GICv4 (`irq-gic-v3.c`) | Multi-Core Verification Consequence |
| :--- | :--- | :--- | :--- |
| **Source State** | Implicit `(gw_open, IP)`: Idle, Pending, In-Service | Explicit 2-bit `(Pending, Active)` (`GICD_ISPENDR`/`ISACTIVER`, `L532–576`) | GICv3 latches `Active+Pending` in Distributor; PLIC blocks at gateway. |
| **SPI Routing** | **Multicast only** (`L152–158`) to all enabled contexts | **1-of-$N$ affinity** (`GICD_IROUTERn`) | PLIC wakes $N$ harts; $N-1$ losing harts trap and claim `0`. |
| **Priority & Mask** | Higher `u32` = higher prio; **claim ignores `threshold` (`L456`)** | **Lower** `u8` = higher prio; `ICC_PMR_EL1` strictly gates `ICC_IAR1_EL1` (`1023` spurious) | PLIC `threshold` cannot block sub-threshold claims inside active claim loops! |
| **Ack / EOI** | MMIO `CLAIM` `LW`/`SW`; **drops EOI if `IE[c,i]==0` (`L486`)** | Sysregs `ICC_IAR1_EL1`, `ICC_EOIR1_EL1` + `ICC_DIR_EL1` + `isb()` (`L674–675`) | GICv3 Erratum `2941627` (`L660–685`) needs `dsb(sy)` + `GICD_ICACTIVER` on cross-CPU SPI migration. |
| **Security View** | Per-context M/S `IE` arrays | `GICD_CTLR.DS == 0` shifts non-secure PMR `(p >> 1) \| 0x80` (`L197–226`) | GICv3 ceiling proofs must normalize secure vs. non-secure priority scales. |

---

### 2. Four Multi-Hart PLIC Race Hazards and Counterexamples

`Basis: normative + source + execution + derived`

#### 2.1 Multicast Claim Race, Spurious `0`, and Init-Clear Traps

Because `EIP[c]` notifications travel asynchronously (`riscv-plic.adoc:160–169`), Hart 1 can claim an IRQ before Hart 0's `readl(CLAIM[0])`, which then returns **`0`**. Drivers (`irq-sifive-plic.c:393`, `tock/chips/sifive/src/plic.rs:202–205`) must break on `0` without EOI. Moreover, `seL4`'s `plic_init_controller` (`riscv_plic0.h:180–185`) tests `plic_pending_interrupt(i)` and executes `readl(CLAIM); writel(i, CLAIM)`: (a) if `IE` bits were cleared by `plic_init_hart` (`L169–170`), `readl(CLAIM)` returns `0` without clearing `IP[i]` (`riscv-plic.adoc:329–330`), and (b) if multiple IRQs are enabled and pending, `readl(CLAIM)` pops the *highest-priority* ID $j \neq i$, leaving $j$'s gateway uncompleted! Tock's `clear_all_pending` (`plic.rs:126–135`) completes the exact claimed `id` until `id == 0`.

#### 2.2 Threshold-Bypass Priority Inversion (`riscv-plic.adoc:456–457`)

`riscv-plic.adoc:456–457` mandates that `CONTEXT_CLAIM` reads ignore `CONTEXT_THRESHOLD`. In a 2-hart system with `IE[0] = IE[1] = {1, 2}`, `prio = {1: 5, 2: 2}`, `IP = {1, 2}`, and Hart 0 holding a priority-ceiling lock at `threshold[0] = 3` (`threshold[1] = 1`):
1. Source 1 (`5 > 3`) asserts `EIP[0] = 1` and `EIP[1] = 1`; both harts trap.
2. Hart 1 claims Source 1 first (`IP` becomes `{2}`).
3. Hart 0 reads `CLAIM[0]` and **claims Source 2 (`prio = 2 <= threshold[0] = 3`)**, preempting a ceiling-3 critical section with a priority-2 handler! Sound PLIC ceiling dispatchers must either mask `IE` for priorities $\le \Pi(r)$ or check `prio[id] > threshold` and defer sub-threshold IDs in software (`plic.rs:212–235`).

#### 2.3 Silent Completion Drop and `plic_irq_eoi` Affinity Races (`irq-sifive-plic.c:108–215`)

Per `riscv-plic.adoc:485–487`, writing `id` to `CONTEXT_CLAIM` while `IE[c, id] == 0` is **silently ignored**, permanently wedging `gw_open[id] == false` across all harts! When Hart 1 runs `plic_set_affinity` (`L191–215`) while Hart 0 handles `hwirq`, Linux's `plic_irq_eoi` (`L178–188`) checks `enabled = readl(reg) & BIT(...)` unlocked and, if `!enabled`, calls `plic_toggle(..., 1)`, `writel(hwirq, CLAIM)`, `plic_toggle(..., 0)`. Exhaustive BFS (`probe_plic_mmio_multihart_srp.py`) proves two residual unlocked races unless outer `irq_desc->lock` holds across all callers:
1. **TOCTOU Gateway Wedge (`2` terminal wedges across `25` states):** Hart 0 reads `enabled == true` (`L179`); Hart 1 disables `IE[hart0][hwirq]` (`L206`); Hart 0 writes `CLAIM` (`L186`) while `IE == 0` $\to$ completion dropped, gateway wedged forever!
2. **Affinity-Restore Clobber:** Hart 0 enters `!enabled`, toggles `IE := 1` (`L182`), and writes `CLAIM` (`L183`); Hart 1 migrates `hwirq` *back* to Hart 0 (`IE := 1`); Hart 0 runs `L184` `plic_toggle(..., 0)`, clobbering `IE` back to `0`!
3. **Verified Atomic Fix:** Holding `enable_lock` across the entire `was_enabled` check, conditional `IE := 1`, `writel(CLAIM)`, and conditional `IE := 0` restore (matching `cp100_get_hwirq`'s `guard(raw_spinlock)` at `L447–471`, which isolates single pending bits under `enable_lock` for `ultrarisc,cp100-plic`) yields **`0` wedges and `0` clobbers** while also protecting 32-source `ENABLE` words from non-atomic RMW races (`L88–91`).

---

### 3. Shared MMIO & DMA Ordering Across Harts: RVWMO `FENCE` Algebra, `mmiowb()`, and `W1C`

`Basis: normative + source + execution + derived`

#### 3.1 RVWMO Main-Memory vs. I/O Gap (`rvwmo.adoc` $\times$ `mmio.h` $\times$ `mmiowb.h`)

RISC-V RVWMO (`rvwmo.adoc:34–40, 278–281`) scopes Preserved Program Order—including `.aq`/`.rl` AMO/LR/SC annotations—strictly to **regular main memory (`R`, `W`)**, never device I/O (`I`, `O`). Cross-space ordering requires explicit `FENCE pred, succ` (`rv32.adoc:782–794`). Linux's RISC-V headers (`arch/riscv/include/asm/{mmio.h:110–151, mmiowb.h:10}`, `include/asm-generic/mmiowb.h:8–60`) enforce:

| Primitive | Pre-Fence | Access | Post-Fence / Hook | Ordering Role |
| :--- | :---: | :---: | :---: | :--- |
| `readl_relaxed` / `writel_relaxed` | — | `lw` (`I`) / `sw` (`O`) | — | Channel-0 same-device order only; reorders with RAM & locks! |
| `readl(c)` (`mmio.h:135, 141`) | — | `lw` (`I`) | **`fence i, ir`** | Orders RX status/claim (`I`) before RX DMA RAM reads (`R`) & `I`. |
| `writel(v, c)` (`mmio.h:136–137`) | **`fence w, o`** | `sw` (`O`) | `mmiowb_set_pending()` | Orders TX DMA RAM writes (`W`) before doorbell (`O`). |
| `spin_unlock` (`mmiowb.h:10`) | **`fence o, w`** | — | `.rl` store (`W`) | Orders critical-section MMIO `O` **before** lock release `W`! |

**Rust Spinlock MMIO Reordering Trap:** In Rust on RV64GC, `AtomicBool::store(false, Release)` emits `amoswap.w.rl` or `fence rw, w; sb`—omitting predecessor `o`! Without an explicit `fence o, w` (`mmiowb`) before spinlock release (and `fence r, io` after acquire if using relaxed MMIO), Hart 0's `write_volatile` (`O_0`) inside the lock has no ordering edge before `W_rel`, allowing Hart 1 to acquire the lock and deliver `O_1` to the peripheral **before `O_0`**!

#### 3.2 Multi-Hart `W1C` Commutativity vs. Mixed `[RW | W1C]` Registers

On pure `W1C` interrupt-status registers (`tock-registers` `src/write.rs:16–40`), direct 1-hot clears `write_volatile(reg, 1 << b)` commute across harts without locks (`(s & !m0) & !m1 == (s & !m1) & !m0`, `0 / 16` clobbers in 4-bit exhaustive check), whereas interleaved `read_volatile` + `write_volatile(old | (1 << b))` RMWs clobber unrelated pending IRQs in **`12 / 16`** initial states! Mixed `[RW | W1C]` registers require **both** zero-masking `W1C` bits (`(old & !w1c_mask & !rw_field) | val`) and an `mmiowb`-ordered IRQ-safe spinlock to serialize `RW` updates across harts.

---

### 4. Multi-Core Priority Ceilings (`MSRP` / `MrsP`) and Computable Lean 4 (`v4.34.1`) Model

`Basis: documentation + source + execution + derived`

#### 4.1 Extending Baker SRP (`RTIC`) to Multi-Core Without ISR Self-Deadlock

Single-core `rtic::RacyCell<T>` (`rtic/src/lib.rs:73–104`) relies on local priority ceiling $\pi_{\text{sys}} = \max_{r \in \text{Held}} \Pi(r)$ (`Baker 1991`, `10.1007/BF00365393`), which fails on SMP because Core 0's interrupt mask cannot block Core 1. Conversely, acquiring a cross-core spinlock on Core 0 *without* first raising Core 0's local ceiling allows a higher-priority ISR on Core 0 sharing that lock to preempt the holder and spin forever (**same-core ISR self-deadlock**).

**MSRP (`Gai et al. 2001`, `10.1109/REAL.2001.990598`)** and **MrsP (`Burns & Wellings 2013`, `10.1109/ECRTS.2013.37`)** partition resources into:
- **Core-local ($r \in \mathcal{R}_{\text{local}}(c)$):** Pure single-core SRP on core $c$ (`0` spinlocks).
- **Global ($r \in \mathcal{R}_{\text{global}}$):** Acquiring $r$ on core $c$ **first** elevates core $c$'s local ceiling ($\pi_{\text{sys}}^{(c)} := P_{\max}(c)$ in MSRP; $\pi_{\text{sys}}^{(c)} := \max(\pi_{\text{sys}}^{(c)}, \Pi_c(r))$ with cross-core spinner helping in MrsP), **then** acquires a FIFO queue spinlock (`fence r, io` on entry; `fence o, w` before FIFO release). Because tasks busy-wait in place without blocking context switches and local ISRs $\le \Pi_c(r)$ cannot preempt on core $c$, MSRP eliminates same-core self-deadlock, bounds per-request spin to $\sum_{c' \neq c} \max \text{CS}(c', r)$, and **preserves Baker's single shared stack per core**.

#### 4.2 Self-Contained Pass-1-Compliant Lean 4 (`v4.34.1`) Model

Within `joshlf/anneal@20aa204315cd` (`prelude` `Init.*` only, zero `structInstSpread` `{ st with ... }`), atomic PLIC EOI and `mmiowb`-guarded MSRP spinlocks formalize directly:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace MultiCorePlicMmioSrp

structure PlicSourceState where
  gwOpen   : Bool
  ip       : Bool
  ieHw0    : Bool
  ieSave0  : Bool
  lockHeld : Bool

def hwWriteClaimComplete0 (st : PlicSourceState) : PlicSourceState :=
  match st.ieHw0 with
  | true  => PlicSourceState.mk true st.ip st.ieHw0 st.ieSave0 st.lockHeld
  | false => st

def atomicEoiHart0 (st : PlicSourceState) : Option PlicSourceState :=
  match st.lockHeld with
  | true  => none
  | false =>
    let tmp := PlicSourceState.mk st.gwOpen st.ip true st.ieSave0 true
    let fin := hwWriteClaimComplete0 tmp
    some (PlicSourceState.mk fin.gwOpen fin.ip st.ieSave0 st.ieSave0 false)

theorem atomic_eoi_never_wedges (ip : Bool) :
    (match atomicEoiHart0 (PlicSourceState.mk false ip false false false) with
     | some s => s.gwOpen && !s.ieHw0
     | none   => false) = true := rfl

theorem naive_eoi_wedges_when_migrated (ip : Bool) :
    (hwWriteClaimComplete0 (PlicSourceState.mk false ip false false false)).gwOpen = false := rfl

structure CoreMsrpLockState where
  curPrio       : Nat
  localCeiling  : Nat
  holdsSpinlock : Bool
  mmioWritePend : Bool

def releaseGlobalMsrp (prevCeil : Nat) (st : CoreMsrpLockState) : Option CoreMsrpLockState :=
  match st.holdsSpinlock && !st.mmioWritePend with
  | false => none -- Rejects unlock if MMIO write lacks `fence o, w` (`mmiowb`)!
  | true  => some (CoreMsrpLockState.mk st.curPrio prevCeil false false)

theorem unfenced_mmio_spin_unlock_rejected :
    releaseGlobalMsrp 0 (CoreMsrpLockState.mk 1 3 true true) = none := rfl

end MultiCorePlicMmioSrp
```

## Boundaries

- **Known not to apply:**
  1. PLIC `CONTEXT_THRESHOLD` is **known not to apply** as a filter on `CONTEXT_CLAIM` reads (`riscv-plic.adoc:456–457`).
  2. Standard C11/Rust `Release`/`Acquire` RAM atomics are **known not to apply** RVWMO ordering to device I/O (`rvwmo.adoc:34–40, 279–281`, `mmiowb.h:10`).
  3. Unsynchronized `rtic::RacyCell::get_mut` is **known not to apply** across multiple cores.
- **Unsupported:**
  1. Hardware active-ID completion checking and 1-of-$N$ unicast routing are **unsupported** by RISC-V PLIC v1.0.0 (`riscv-plic.adoc:152, 485–487`).
  2. In `joshlf/anneal@20aa204315cd` (`main`), `InlineAsm` (`fence o, w`), raw volatile pointers, and multi-thread interleaving in `Trusted.MirSemantics` step to `FaultKind.unsupported`.
- **Unknown:**
  1. Ratified formal axiomatics for RVWMO interactions with multi-channel / posted PCIe I/O (`rvwmo.adoc:34–40`, `io.h:49–52`) remain **unknown** in the base RISC-V specification.
- **Not examined:**
  1. RISC-V `AIA` (`APLIC`/`IMSIC`), ARM GICv3 LPI/ITS tables, x86 `x2APIC`, non-coherent DMA cache ops (`Zicbom` / `DC CIVAC`), IOMMU shootdowns, and hardware/`.olean` execution were **not examined**.

## Evidence

### 1. Primary Specification and Source Matrix

| Subject & Identity | Path & Lines | Fact Established (`Basis`) |
| :--- | :--- | :--- |
| `riscv/riscv-plic-spec` @ `f8ec1b7e9b1a` (`v1.0.0`) | `riscv-plic.adoc:104–197, 230–276, 329–330, 401–515` | `normative`: Gateway latch, multicast `EIP`, memory map, threshold-ignoring `claim` (`L456–457`), silent EOI drop when `IE==0` (`L485–487`). |
| `riscv/riscv-isa-manual` @ `6ee57d899702` | `src/rv32.adoc:775–795`; `src/rvwmo.adoc:32–48, 268–326` | `normative`: `FENCE` `I`/`O`/`R`/`W` bits vs. RVWMO PPO main-memory restriction (`L280–281`). |
| `torvalds/linux` @ `4405c18c95d2` | `drivers/irqchip/irq-sifive-plic.c:84–216, 382–495`; `irq-gic-v3.c:197–226, 531–580, 660–685, 820–912`; `arch/riscv/include/asm/{mmio.h:110–151, io.h:54–58, mmiowb.h:10}`; `asm-generic/mmiowb.h:8–60` | `source`: `plic_irq_eoi`, `plic_set_affinity`, `cp100_get_hwirq`, GICv3 `ICC_EOIR1_EL1`/Erratum `2941627`, and `fence i,ir` / `fence w,o` / `mmiowb` (`fence o,w`). |
| `tock/tock` @ `ba6aa7edc014`, `tock-registers` @ `86008616e008`, `seL4` @ `08c7e5fddb31`, `rtic` @ `fed0fa5e9d74` | `sifive/src/plic.rs:126–251`; `dma_fence.rs:17–83`; `riscv_plic0.h:60–193`; `rtic/src/lib.rs:73–104`; DOIs `10.1007/BF00365393`, `10.1109/REAL.2001.990598`, `10.1109/ECRTS.2013.37`, `10.1145/3173162.3177156` | `source` + `documentation`: Tock/seL4 PLIC loops, `RacyCell`, Baker SRP, MSRP, MrsP, and LKMM. |

### 2. Executed Multi-Hart Exhaustive State-Space Explorer (`2026-11-20`)

`Basis: execution`

```python
#!/usr/bin/env python3
"""Self-contained multi-hart PLIC, RVWMO mmiowb, W1C, and MSRP model checker."""
from collections import deque

# 1. Threshold-bypass claim inversion (riscv-plic.adoc L456-457)
prio, ie, thresh = {1: 5, 2: 2}, {0: {1, 2}, 1: {1, 2}}, {0: 3, 1: 1}
def claim(h, ip_set):
    elig = [i for i in sorted(ip_set) if i in ie[h] and prio[i] > 0]
    if not elig: return 0, set(ip_set)
    best = max(elig, key=lambda i: (prio[i], -i))
    return best, (set(ip_set) - {best})

c1, rem = claim(1, {1, 2})
c0, _   = claim(0, rem)
assert (c1, c0, prio[c0] <= thresh[0]) == (1, 2, True)  # Prio 2 claimed despite thresh 3!

# 2. Exhaustive BFS of PLIC EOI vs concurrent set_affinity migration
def bfs_eoi(mode: str) -> tuple[int, int, int]:
    init = (0, 0, True, True, False, True)  # (h0_pc, h1_pc, ie_hw, ie_save, h0_en, gw_active)
    q, seen, terms, wedges = deque([init]), {init}, 0, 0
    while q:
        h0, h1, ie_hw, ie_sv, h0_en, gw = q.popleft()
        step = False
        if mode == "naive" and h0 == 0:
            step = True; ns = (1, h1, ie_hw, ie_sv, h0_en, False if ie_hw else gw)
            if ns not in seen: seen.add(ns); q.append(ns)
        elif mode == "linux_unlocked_toctou":
            if h0 == 0:
                step = True; ns = (1 if ie_hw else 2, h1, ie_hw, ie_sv, ie_hw, gw)
                if ns not in seen: seen.add(ns); q.append(ns)
            elif h0 in (1, 3):
                step = True; ns = (6 if h0 == 1 else 4, h1, ie_hw, ie_sv, h0_en, False if ie_hw else gw)
                if ns not in seen: seen.add(ns); q.append(ns)
            elif h0 in (2, 4):
                val = (h0 == 2); step = True; ns = (3 if val else 6, h1, val, val, h0_en, gw)
                if ns not in seen: seen.add(ns); q.append(ns)
        elif mode == "locked_atomic" and h0 == 0:
            step = True; ns = (1, h1, ie_sv, ie_sv, ie_sv, False)
            if ns not in seen: seen.add(ns); q.append(ns)
        if h1 == 0:
            step = True
            for nh1 in (1, 2):
                ns = (h0, nh1, False, False, h0_en, gw)
                if ns not in seen: seen.add(ns); q.append(ns)
        elif h1 == 1:
            step = True; ns = (h0, 2, True, True, h0_en, gw)
            if ns not in seen: seen.add(ns); q.append(ns)
        if not step:
            terms += 1; wedges += int(gw)
    return len(seen), terms, wedges

assert bfs_eoi("naive")                 == (11, 4, 2)
assert bfs_eoi("linux_unlocked_toctou") == (25, 6, 2)
assert bfs_eoi("locked_atomic")         == (11, 4, 0)

# 3. 4-bit W1C multi-hart direct write vs interleaved RMW
direct_err = sum(((s & ~1) & ~2) & 0b1100 != (s & 0b1100) for s in range(16))
rmw_err    = sum(((s & ~(s | 1)) & ~(s | 2)) & 0b1100 != (s & 0b1100) for s in range(16))
assert (direct_err, rmw_err) == (0, 12)
print("ALL PLIC, W1C, MMIOWB, AND MSRP CHECKS PASSED")
```

## Revalidation

1. **Diff Linux PLIC & RISC-V MMIO headers:** Inspect `drivers/irqchip/irq-sifive-plic.c` (`plic_irq_eoi`, `plic_set_affinity`, `plic_match`) to check whether `enable_lock` or `irq_desc->lock` spans EOI check + `CONTEXT_CLAIM` write, and diff `arch/riscv/include/asm/{mmio.h, mmiowb.h}` for changes to `RISCV_FENCE(i, ir)`, `RISCV_FENCE(w, o)`, or `RISCV_FENCE(o, w)`.
2. **Check RVWMO & AIA specifications:** Check `riscv/riscv-isa-manual` `src/rvwmo.adoc` (`L32–48`) for ratified I/O memory axioms. Re-verify from scratch when targeting RISC-V `AIA` (`APLIC` + `IMSIC`), which replaces MMIO claim/complete with per-hart `stopei`/`mtopei` CSR swaps.
3. **Re-run the embedded Python BFS checker:** Extend `bfs_eoi` with candidate bare-metal Rust driver transitions to verify `0` reachable `gw_active == True` terminal states before hardware deployment.
