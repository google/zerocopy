# RISC-V PLIC 1.0.0 Multi-Hart Interrupt Verification: Priority-Threshold Claim Ordering, `IE`-Disabled Wedges, `fence io, io` Device Hazards, Nested `sstatus.SIE`, and MSRP Cross-Hart Locking

## Summary

Verifying multi-hart interrupt handlers, real-time priority ceilings, and shared peripheral drivers on RISC-V systems with the Platform-Level Interrupt Controller (`PLIC 1.0.0`) requires reconciling subtle behavioral divergences among the ratified PLIC specification, QEMU's `sifive_plic` emulator, RISC-V Weak Memory Ordering (`RVWMO`) I/O fences, and Multiprocessor Stack Resource Policy (`MSRP`) locking rules:

1. **Threshold-Before-Claim Ordering Hazards and Spec-vs-QEMU Divergence:** Ratified PLIC 1.0.0 (`riscv-plic.adoc:453-457`) specifies that `claim` reads ignore the per-context priority `threshold` register (`threshold` masks only `EIP` external interrupt notifications), whereas QEMU `v9.1.0` (`hw/intc/sifive_plic.c:78, 105, 167`) filters `CONTEXT_CLAIM` reads by `prio > target_priority[addrid]`. Raising `threshold` at trap entry *before* reading `claim` drops the interrupt (`claim == 0`) on QEMU and threshold-gated silicon, whereas looping `while ((id = read(claim)) != 0)` while `threshold > 0` claims masked lower-priority interrupts on strict PLIC 1.0.0 silicon. The unique portable protocol is to enter with `sstatus.SIE = 0`, read `claim` **once** before raising `threshold`, treat `id == 0` (multicast steal by another hart) as an immediate no-op exit without writing `claim/complete`, and then raise `threshold := max(prev_threshold, prio(id))` before enabling nested preemption.
2. **`IE`-Disabled Completion Permanently Wedges PLIC Gateways (Masked on QEMU):** Ratified PLIC 1.0.0 (`riscv-plic.adoc:108-110, 486-491`) keeps a source's gateway closed (`inFlight = true`) until a valid completion message arrives, and **silently ignores** any completion write whose ID is disabled (`IE[ctx, id] == 0`) for that target. Clearing `IE[ctx, id]` before writing `claim/complete` wedges that source permanently across all harts—a hardware lockup Linux `v6.12` (`drivers/irqchip/irq-sifive-plic.c:136-165`) avoids by masking via `PRIORITY = 0` and toggling `IE = 1` around `CONTEXT_CLAIM` EOI writes, but which QEMU `v9.1.0` (`sifive_plic.c:241-245`) misses because `sifive_plic_write` omits the `enable` check.
3. **`core::sync::atomic::fence(Ordering::SeqCst)` Does Not Order MMIO `W1C` Before PLIC Complete:** LLVM's RISC-V backend (`RISCVInstrInfo.td:1726-1732`) lowers `Ordering::SeqCst` to `fence rw, rw` (`pred = 0b0011, succ = 0b0011`), omitting device input (`I = 0b1000`) and output (`O = 0b0100`) bits (`rv32.adoc:770-805`). Ordering a peripheral Write-1-to-Clear (`W1C`) status clear before a PLIC `claim/complete` store requires `fence io, io` (`fence iorw, iorw` if normal-memory DMA descriptors are also touched) plus a peripheral MMIO readback across posted bridges to prevent level-triggered gateway re-latching (`riscv-plic.adoc:114-116`, `rv32.adoc:782-795`). Pure `W1C` registers (`rwMask == 0`) commute across harts on disjoint bits; mixed `RW + W1C` registers clobber state unless protected by a cross-hart lock.
4. **Nested `sstatus.SIE` CSR Discipline and MSRP Local-Ceiling-Before-Spinlock Order:** Because S-mode traps overwrite `sepc`, `sstatus.SPIE`, `sstatus.SPP`, and `scause` without hardware stacking (`supervisor.adoc:103-125`), nested handlers must save CSRs under `sstatus.SIE = 0`, raise `CONTEXT_THRESHOLD >= prio(id)` + `fence io, io` before setting `SIE = 1`, and clear `SIE = 0` before restoring CSRs or completing the IRQ. Under MSRP (Gai, Lipari & Di Natale, RTSS 2001), acquiring a cross-hart spinlock *before* raising the local preemption ceiling (`SIE = 0` or `threshold = P_max`) causes single-hart self-deadlock and two-hart `AB-BA` preemption-spin deadlocks; local ceiling elevation must strictly precede spinlock acquisition and outlive spinlock release.

## Applicability

These findings apply to multi-hart RISC-V Machine-mode (`M-mode`) and Supervisor-mode (`S-mode`) kernels, real-time schedulers, hypervisors, and formal models built against:

- **Normative Hardware & ABI Contracts:** Ratified `RISC-V PLIC 1.0.0` (`riscv/riscv-plic-spec` @ `f8ec1b7e9b1a92c34af8e0ab7eb33838813785a3`), RISC-V ISA Manuals (`riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05`), and RISC-V ELF psABI (`riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`).
- **Drivers, Toolchains, and Emulators:** Linux `v6.12` (`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a`, `drivers/irqchip/irq-sifive-plic.c`, `arch/riscv/include/asm/{mmio,io}.h`), QEMU `v9.1.0` (`qemu/qemu` @ `fd1952d814da738ed107e05583b3e02ac11e88ff`, `hw/intc/sifive_plic.c`), Tock OS (`tock/tock` @ `842498efca186bba0071ed3d072fddd2dec3312e`, `chips/sifive/src/plic.rs`), Rust RTIC (`rtic-rs/rtic` @ `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`), LLVM `19.1.0` (`llvm/llvm-project` @ `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`), and Lean 4 (`leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`).

This package covers memory-mapped `sifive,plic-1.0.0` / `riscv,plic0` controllers (`1..=1023` sources, up to `15,872` hart contexts). For uniprocessor SRP schedulability, see `superdense-logical-time-hybrid-synchronous-calculi-and-preemptive-srp-verification`; for `sstatus.SIE = 0` secret-erasure sandboxes inside ISRs, see `compiler-abi-register-spills-stack-high-water-erasure-and-isr-secret-containment`.

## Findings

### 1. Ratified PLIC 1.0.0 Memory Map, Gateway Automaton, and Multi-Hart Multicasting

Basis: normative + source

A ratified PLIC 1.0.0 instance (`riscv-plic.adoc:230-276`, matching `offset_of!` assertions in `tock/tock` `chips/sifive/src/plic.rs:32-55` and `irq-sifive-plic.c:35-61`) exposes 32-bit aligned MMIO registers (`LW`/`SW` atomic access) across a `64 MiB` (`0x0400_0000`) aperture:

| Offset (`base + ...`) | Register Block | Domain & Bounds | Normative Semantics (`riscv-plic.adoc`) |
| :--- | :--- | :--- | :--- |
| `0x000000` | Reserved (Source 0) | `id = 0` | Hardwired `0`; ID `0` denotes "no interrupt" (`lines 172-173, 237`). |
| `0x000004 * id` | `priority[id]` | `id ∈ 1..=1023` | WARL unsigned integer; `0` = disabled; higher = higher priority; ties broken by **lowest `id`** (`lines 174-175, 281-299`). |
| `0x001000 + 4 * ⌊id / 32⌋` | `pending` (`IP`) | Global RO bitmap | Bit 0 hardwired `0`; latched from gateway, cleared atomically on `claim` (`lines 321-349`). |
| `0x002000 + 0x80 * ctx + 4 * ⌊id / 32⌋` | `enable[ctx]` (`IE`) | `ctx ∈ 0..=15871` | Bit 0 hardwired `0`; enables source `id` for hart context `ctx` (`lines 350-399`). |
| `0x200000 + 0x1000 * ctx` | `threshold[ctx]` | `4 KiB` stride WARL | Masks `EIP` notifications with `prio[id] <= threshold[ctx]`; `0` permits `prio >= 1` (`lines 401-429`). |
| `0x200004 + 0x1000 * ctx` | `claim/complete[ctx]` | Non-idempotent R/W | **`LW`:** atomic claim returning highest-priority enabled pending `id` (or `0`). **`SW`:** completion for `id` (`lines 431-515`). |

**Two-Component Gateway $\times$ Core Automaton (`riscv-plic.adoc:102-197`):**
Formal PLIC models must distinguish **per-source Gateway state** (`inFlight[id] : Bool`) from **Core pending state** (`IP[id] : Bool`):
1. **Gateway Forwarding (`lines 106-122`):** When `inFlight[id] == false` and source `id` asserts, the gateway sets `inFlight[id] := true` and `IP[id] := 1`. While `inFlight[id] == true`, the gateway blocks all further requests from `id`. Once forwarded, a request **cannot be retracted**: if a level source deasserts before claim, `IP[id]` stays `1`.
2. **Multicast Notification (`lines 139-168`):** Each context `ctx` asserts `EIP[ctx]` (`meip`/`seip`) iff $\exists\, \text{id} \in [1..1023] : \text{IP}[\text{id}] = 1 \land \text{IE}[\text{ctx}, \text{id}] = 1 \land \text{prio}[\text{id}] > \text{threshold}[\text{ctx}]$. Multi-hart enabled sources multicast `EIP` to all matching contexts (`lines 152-155`).
3. **Atomic Claim & Steal (`lines 164-168, 436-440`):** When multiple harts trap on a multicast `SEIP` and read `claim/complete[ctx]`, the fastest hart atomically receives `id` ($\ge 1$) and clears `IP[id] := 0` while `inFlight[id]` stays `true`; slower harts read **`0`** and **must** exit via `sret` without writing `0` to `claim/complete`.
4. **Gateway Re-Opening (`lines 114-116, 483-491`):** Writing `id` to `claim/complete[ctx]` (while `IE[ctx, id] == 1`) clears `inFlight[id] := false`; if a level-sensitive wire is still asserted, the gateway immediately re-latches `inFlight[id] := true` and `IP[id] := 1`.

### 2. Spec-vs-Emulator Divergences: Threshold-Before-Claim Interrupt Loss and `IE`-Disabled Completion Wedges

Basis: normative + source + derived

Comparing `riscv-plic.adoc`, QEMU `v9.1.0` (`hw/intc/sifive_plic.c`), and Linux `v6.12` (`drivers/irqchip/irq-sifive-plic.c`) reveals two critical divergences:

| Edge Case | Ratified PLIC 1.0.0 (`riscv-plic.adoc`) | QEMU `v9.1.0` (`sifive_plic.c`) | Linux `v6.12` (`irq-sifive-plic.c`) | Portable Contract |
| :--- | :--- | :--- | :--- | :--- |
| **`claim` read when `prio[id] <= threshold[ctx]`** | **Ignores `threshold`** (`lines 456-457`: *"claim operation is not affected by ... priority threshold"*). | **Filters by `threshold`:** `sifive_plic_claimed` (`lines 78, 105, 167`) checks `prio > target_priority[addrid]`, returning **`0`**. | Keeps `CONTEXT_THRESHOLD = 0` (`lines 63, 422`); masks individual IRQs via `PRIORITY = 0` (`line 140`). | **Claim once BEFORE raising `threshold`**; never loop `read(claim)` at `threshold > 0` without checking `sip.SEIP`. |
| **`complete` write when `IE[ctx, id] == 0`** | **Silently ignored** (`lines 486-487`), leaving `Gateway[id]` **permanently wedged**! | **Unconditionally completes** (`lines 241-245` omit `plic->enable` check). | `plic_irq_eoi` (`lines 154-165`) toggles `IE = 1`, writes `CONTEXT_CLAIM`, then restores `IE = 0`. | Gate `complete` on `IE[ctx, id] == 1` in models and drivers. |
| **Target mismatch (`ctx_complete != ctx_claim`)** | Allowed iff `IE[ctx_complete, id] == 1` (`lines 484-487`). | Global `claimed` bitmap (`line 72`). | Per-CPU `plic_handlers` (`line 156`); `plic_set_affinity` (`lines 182-187`) can clear `IE` mid-flight. | Enforce linear claim-to-complete ownership with `claimId >= 1`. |

1. **Bidirectional `threshold`-vs-`claim` Failure Modes:**
   - *Raising `threshold` before `claim`:* If an S-mode ISR writes `CONTEXT_THRESHOLD := 3` on trap entry before reading `CONTEXT_CLAIM`, QEMU `v9.1.0` (`sifive_plic.c:78, 105`) and SiFive-style shared-comparator RTL evaluate `3 > 3 == false` and return `0`, stranding `pending[id] = 1` with `SEIP` deasserted. Even on strict PLIC 1.0.0 silicon, checking `sip.SEIP` after raising `threshold` observes `SEIP == 0` and aborts.
   - *Unconditional `while (readl(claim) != 0)` loop at `threshold > 0`:* Conversely, on strict PLIC 1.0.0 silicon (`riscv-plic.adoc:456-457`), draining `while ((id = readl(claim)) != 0)` (`irq-sifive-plic.c:386`) while holding an SRP/MSRP ceiling `threshold == 4` **claims pending priority-`2` interrupts**, violating priority-ceiling mutual exclusion! Performing a single `claim` per trap entry *before* raising `threshold` (or gating drain iterations on `(csrr(sip) & SIE_SEIE) != 0`) is sound on both hardware interpretations.
2. **The `IE`-Disabled Completion Wedge (`irq-sifive-plic.c:154-165`):**
   ```c
   if (unlikely(irqd_irq_disabled(d))) {
       plic_toggle(handler, d->hwirq, 1);
       writel(d->hwirq, handler->hart_base + CONTEXT_CLAIM);
       plic_toggle(handler, d->hwirq, 0);
   } else {
       writel(d->hwirq, handler->hart_base + CONTEXT_CLAIM);
   }
   ```
   If a handler calls `disable_irq_nosync` or another CPU runs `plic_set_affinity` (`lines 168-190`, clearing `IE` on the old CPU) while `hwirq` is in flight, writing `CONTEXT_CLAIM` with `IE == 0` is dropped by PLIC 1.0.0 (`riscv-plic.adoc:486-487`), wedging `Gateway[hwirq]` across all CPUs until reset. QEMU `v9.1.0` never reproduces this bug because `sifive_plic_write` ignores `plic->enable`.

### 3. Peripheral `W1C` Ordering, RVWMO `FENCE` `I/O` Semantics, and Shared-MMIO Commutativity

Basis: normative + source + execution + derived

1. **Why `atomic::fence(Ordering::SeqCst)` Fails to Order MMIO (`RISCVInstrInfo.td:1725-1732`, `rv32.adoc:770-805`):**
   Clearing a level-triggered device's `W1C` status register must take effect at the PLIC gateway before `claim/complete` re-opens the gateway (`riscv-plic.adoc:114-116`). In LLVM `19.1.0` (`llvm/lib/Target/RISCV/RISCVInstrInfo.td:1726-1732`), every C11/Rust `atomic_fence` lowers strictly to main-memory `R`/`W` (`0b0010`/`0b0001`) bits, omitting device `I` (`0b1000`) and `O` (`0b0100`):
   ```tablegen
   def : Pat<(atomic_fence (XLenVT 4), (timm)), (FENCE 0b10, 0b11)>; // Acquire -> fence r, rw
   def : Pat<(atomic_fence (XLenVT 5), (timm)), (FENCE 0b11, 0b1)>;  // Release -> fence rw, w
   def : Pat<(atomic_fence (XLenVT 6), (timm)), (FENCE_TSO)>;        // AcqRel  -> fence.tso
   def : Pat<(atomic_fence (XLenVT 7), (timm)), (FENCE 0b11, 0b11)>; // SeqCst  -> fence rw, rw
   ```
   Even Linux `v6.12` `writel()` (`arch/riscv/include/asm/mmio.h:136-137, 145`) emits only `RISCV_FENCE(w, o)` + `mmiowb_set_pending()`, assuming single-channel strong PMA I/O (`mmio.h:105-107`; contrast PCI `outs*` in `io.h:52-53` using `RISCV_FENCE(iow, o)` / `RISCV_FENCE(o, io)`). Moreover, `rv32.adoc:782-795` warns that out-of-band device-to-PLIC interrupt wires lie outside `fence` coherence alone. Across posted AXI4/TileLink/PCIe bridges, drivers must execute: (i) `write_volatile(dev_w1c, mask)`, (ii) `read_volatile(dev_w1c)` (draining posted bus buffers to the peripheral), (iii) `asm!("fence io, io")` (`fence iorw, iorw` if DMA RAM rings were also accessed), and (iv) `write_volatile(plic_claim, id)`.
2. **Pure `W1C` Commutativity vs. Mixed `RW + W1C` Clobber Across Harts:**
   Under bitmask layout $L = (\text{rwMask}, \text{w1cMask}, \text{roMask})$ with transition $\text{step}(L, \text{hw}, \text{wr}) = (\text{hw} \mathbin{\&} \neg(\text{rwMask} \mathbin{|} (\text{wr} \mathbin{\&} \text{w1cMask}))) \mathbin{|} (\text{wr} \mathbin{\&} \text{rwMask})$:
   - **Pure `W1C` (`rwMask == 0`) on disjoint bits (`(wA & wB & w1cMask) == 0`):** Because $(h \land \neg a) \land \neg b = (h \land \neg b) \land \neg a$ and $(h \land \neg a) \land \neg a = h \land \neg a$, concurrent hart clears commute and are idempotent without locks.
   - **Mixed `RW + W1C` (`rwMask != 0`) or RMW Registers:** Non-commutative! With `rwMask = 0xF0, w1cMask = 0x0F, hw = 0x03`, writes `0x11` and `0x22` yield `0x20` in order `(H0, H1)` vs `0x10` in `(H1, H0)`, clobbering `RW` bits (and software RMW `writel(readl(reg) | mask, reg)` inadvertently clears concurrent `W1C` bits!). Mixed `RW + W1C` and PLIC `ENABLE` words (`irq-sifive-plic.c:86, 97-115`) require an MSRP cross-hart spinlock.

### 4. Nested Supervisor Interrupts (`sstatus.SIE`) and Trap-Context Stack Invariants

Basis: normative + source + derived

Hardware clears `sstatus.SIE := 0` on S-mode trap entry without stacking `sepc`, `scause`, `stval`, or `sstatus` (`SPIE`, `SPP`) (`supervisor.adoc:103-125`). Supporting nested preemption by strictly higher-priority PLIC sources requires four invariants:

1. **Save CSRs Before `SIE = 1`:** Allocate a 16-byte-aligned stack frame (`riscv-cc.adoc:18-26`) and save caller-saved GPRs plus `(sepc, sstatus, prev_threshold)` while `sstatus.SIE == 0`.
2. **Raise `CONTEXT_THRESHOLD` + `fence io, io` Before `SIE = 1`:** Write `max(prev_threshold, prio[id])` to `CONTEXT_THRESHOLD[ctx]` and execute `fence io, io` (or read back `CONTEXT_THRESHOLD`) *before* `csrsi sstatus, 0x2`; otherwise equal/lower-priority interrupts immediately re-trap before the threshold store reaches the PLIC.
3. **Bounded Priority Stack Depth:** Because preemption requires `prio_nested > threshold >= prio_cur >= 1`, nesting depth is strictly bounded by $\min(P_{\max}, N_{\text{distinct\_prios}})$ ($\le 7$ frames on 3-bit priority SiFive PLICs).
4. **Clear `SIE = 0` Before CSR Restore, EOI, and Stack Scrubbing:** Execute `csrci sstatus, 0x2` (`SIE := 0`) *before* `W1C`/EOI, restoring `(sepc, sstatus)`, or scrubbing sensitive stack slots; taking a nested trap between `csrw sepc` and `sret` clobbers `sepc` permanently.

```text
  Trap(SIE=0) -> (1) Save GPRs + (sepc, sstatus, prev_thresh) on 16B-aligned SP
              -> (2) id = lw(CLAIM) [id==0 => restore & sret]
              -> (3) sw(max(prev_thresh, prio[id]), THRESHOLD); fence io, io
              -> (4) csrsi sstatus, SIE   [Nested prio > threshold allowed; depth <= P_max]
              -> (5) csrci sstatus, SIE   [Mask BEFORE W1C, EOI, CSR restore, & scrub!]
              -> (6) sw(mask, DEV_W1C); lw(DEV_W1C); fence io, io; sw(prev_thresh, THRESHOLD); sw(id, CLAIM)
              -> (7) Scrub sensitive slots; restore (sepc, sstatus) & GPRs; sp += Frame; sret
```

### 5. Multiprocessor Stack Resource Policy (MSRP) and Cross-Hart Spinlock-After-Local-Ceiling Deadlock Freedom

Basis: documentation + derived

Uniprocessor **SRP** (Baker 1991, DOI `10.1007/BF00365393`; Rust **RTIC**, Eriksson et al., SIES 2013, DOI `10.1109/SIES.2013.6601482`, `rtic-rs/rtic` @ `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`) protects hart-local resources without spinlocks by raising `CONTEXT_THRESHOLD[h]` to $\lceil R \rceil_h = \max_{J \in h, R \in J} \pi(J)$. Across multiple harts, **MSRP** (Gai, Lipari & Di Natale, RTSS 2001, DOI `10.1109/REAL.2001.990598`; Brandenburg & Anderson, RTSS 2010, DOI `10.1109/RTSS.2010.17`) keeps hart-local resources lock-free via `CONTEXT_THRESHOLD[h]` and protects cross-hart global resources via **local preemption suppression FIRST, followed by a non-preemptible FIFO/ticket spinlock**:

1. **Two Deadlocks Caused by Spinlock-Before-Local-Ceiling:**
   - *Same-Hart Self-Deadlock:* $J_{\text{low}}$ ($\pi = 1$) on Hart 0 acquires spinlock $L$ with `SIE = 1, threshold = 0`; local $J_{\text{high}}$ ($\pi = 4$) preempts Hart 0 and spins on $L$ forever above suspended $J_{\text{low}}$.
   - *Two-Hart `AB-BA` Preemption-Spin Deadlock (Disjoint Local Locks, Ordered Global Locks $L_1 \prec L_2$):* Suppose $J_{\text{low}}$ on Hart 0 uses only $L_2$, $J_{\text{high}}$ ($\pi = 4$) on Hart 0 uses only $L_1$, and Hart 1 runs non-preemptibly (`SIE = 0`) acquiring $L_1$ then $L_2$ in legal global order $L_1 \prec L_2$. If $J_{\text{low}}$ on Hart 0 acquires $L_2$ preemptibly (`SIE = 1`), Hart 1 acquires $L_1$ and spins non-preemptibly waiting for $L_2$; then $J_{\text{high}}$ preempts $J_{\text{low}}$ on Hart 0 and spins waiting for $L_1$! Both harts deadlock permanently even though neither $J_{\text{low}}$ nor $J_{\text{high}}$ nested locks and Hart 1 obeyed $L_1 \prec L_2$.
2. **MSRP RISC-V Protocol (`msrpAcquireCrossHart` / `msrpReleaseCrossHart`):**
   - **Acquire:** First suppress local preemption on Hart $h$ (`csrrc s_old, sstatus, 0x2` setting `SIE = 0`, or `CONTEXT_THRESHOLD[h] := P_max` + `fence io, io`); second acquire the FIFO ticket spinlock (`amoadd.w.aq` + `fence r, rw`, obeying strict global order $R_a \prec R_b$ if nested).
   - **Release:** First release the spinlock (`fence iorw, w` / `amoswap.w.rl`, or `fence iorw, iorw` if MMIO occurred inside the critical section); second restore Hart $h$'s prior `CONTEXT_THRESHOLD[h]` / `sstatus.SIE`. Assert `heldMsrpRes == []` before `sret`.

### 6. Mechanized Multi-Hart PLIC + MSRP + `W1C` Verification Automaton

Basis: execution + derived

In Lean 4 (`v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`), encoding the coupled multi-hart PLIC 1.0.0, `W1C` + `fence io, io`, nested `SavedTrapCtx`, and MSRP protocol over `PlicGlobalState`:

```lean
structure IrqSourceState where
  prio : Nat
  inFlight : Bool          -- Gateway closed from claim until valid IE-enabled complete
  claimedBy : Option Nat
  ieHart0 : Bool
  ieHart1 : Bool
  devW1cPending : Nat
  devW1cFenceDone : Bool   -- Set true ONLY by fence io, io after devW1cPending == 0

def plicCompleteGate (st : PlicGlobalState) (hartId : Nat) : Bool :=
  let ieOk := match Nat.beq hartId 0 with | true => st.irq1.ieHart0 | false => st.irq1.ieHart1
  let ownerOk := match st.irq1.claimedBy with | some c => Nat.beq c hartId | none => false
  ieOk && ownerOk && st.irq1.inFlight && Nat.beq st.irq1.devW1cPending 0 && st.irq1.devW1cFenceDone
```

Kernel verification (`-DElab.async=false -Ddebug.skipKernelTC=false`) establishes: (1) all six protocol bugs (threshold-before-claim, `IE`-disabled complete wedge, `claimId == 0` complete, complete before `W1C` clear, complete without `fence io, io`, and spinlock-before-local-ceiling) evaluate to `none`/`false` by `rfl`; (2) `msrp_local_ceiling_blocks_same_hart_preemption` universally proves `plicClaimIrq1 st' hartId = (0, st')` whenever `irq.prio <= localCeil`; and (3) `512` 2-hart claim/steal/MSRP/`W1C`/`fence io, io`/complete rounds verify via `rfl` in `3.65 s` marginal kernel time (`7.1 ms/round`, `550.9 MiB` RSS) using strict-pair binary doubling.

## Boundaries

- **`known not to apply` — QEMU `sifive_plic` as a Standalone PLIC 1.0.0 Compliance Oracle:** Passing tests on QEMU `v9.1.0` (`sifive_plic.c`) is **known not to apply** as evidence of freedom from `IE`-disabled completion wedges (`sifive_plic.c:241-245` omits the `enable` check required by `riscv-plic.adoc:486-487`), or as evidence that `while (read(claim) != 0)` drain loops respect `threshold > 0` on strict PLIC 1.0.0 silicon (`sifive_plic.c:78, 105` filters claims by `threshold`).
- **`known not to apply` — `Ordering::SeqCst` for MMIO and Uniprocessor SRP Across Harts:** Rust/LLVM `Ordering::SeqCst` (`fence rw, rw`, `RISCVInstrInfo.td:1732`) is **known not to apply** to device `I`/`O` ordering. Local `CONTEXT_THRESHOLD[h]` elevation without an atomic cross-hart lock is **known not to apply** to multi-hart shared resources, and unlocked writes are **known not to apply** to mixed `RW + W1C` registers (`rwMask != 0`).
- **`unsupported` — Sub-32-Bit / AMO Accesses on PLIC MMIO and PLIC-Internal Preemption:** Byte/halfword PLIC accesses (`.min_access_size = 4`, `sifive_plic.c:262-265`, `riscv-plic.adoc:232-233`), `Zaamo` atomic instructions on PLIC `ENABLE` words (`irq-sifive-plic.c:83-86`), and hardware-managed nesting inside the PLIC (`riscv-plic.adoc:93-97`) are **unsupported**.
- **`not examined` — RISC-V `AIA` (`aplic` + `imsic`) and Hypervisor `VS`-Mode Virtual Interrupts:** Message-signaled `imsic` CSRs (`stopei`/`vstopei`), `hvip`/`hvictl` virtual interrupts, and vendor edge-counter quirks (`PLIC_QUIRK_EDGE_INTERRUPT` at `irq-sifive-plic.c:65, 430-433`) were **not examined**.
- **`unknown` — Out-of-Band Wire Propagation Delay Without SoC Timing Sheets:** Per `rv32.adoc:787-795`, physical wire deassertion delay from a peripheral to the PLIC gateway after `W1C` + `LW` readback + `fence io, io` is outside the ISA specification and remains **unknown** without SoC bus timing bounds; portable ISRs must tolerate one benign idempotent re-entry (`dev_status == 0` -> EOI, `riscv-plic.adoc:118-122`).

## Evidence

### 1. Normative Specifications and Upstream Repositories (Immutable 40-Char Revisions)
- **`riscv/riscv-plic-spec` @ `f8ec1b7e9b1a92c34af8e0ab7eb33838813785a3` (`1.0.0`):** `riscv-plic.adoc:60-176` (contexts, gateways, multicast steal), `230-429` (memory map, priorities, `IP`, `IE`, `threshold`), `431-515` (`claim` threshold-independence at `456-457`, `IE == 0` ignored completion at `486-487`).
- **`riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05`:** `src/priv/supervisor.adoc:41-125` (`sstatus` `SIE`/`SPIE`/`SPP`), `src/unpriv/rv32.adoc:762-835` (`FENCE` `I/O/R/W` and `782-795` interrupt-wire note), `src/unpriv/rvwmo.adoc:5-40, 274-298`.
- **`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a` (`v6.12`):** `drivers/irqchip/irq-sifive-plic.c:35-191, 375-435` (`enable_lock`, `plic_irq_mask` `PRIORITY = 0`, `plic_irq_eoi` `IE` toggle at `154-165`, `plic_handle_irq` at `386-393`), `arch/riscv/include/asm/mmio.h:101-150`, `arch/riscv/include/asm/io.h:50-54`.
- **`qemu/qemu` @ `fd1952d814da738ed107e05583b3e02ac11e88ff` (`v9.1.0`):** `hw/intc/sifive_plic.c:75-113, 166-176, 241-245`.
- **`tock/tock` @ `842498efca186bba0071ed3d072fddd2dec3312e`:** `chips/sifive/src/plic.rs:32-56, 131-140, 207-256`.
- **`llvm/llvm-project` @ `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4` (`llvmorg-19.1.0`):** `llvm/lib/Target/RISCV/RISCVInstrInfo.td:1725-1732`.
- **`rtic-rs/rtic` @ `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`** and **`riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`** (`riscv-cc.adoc:11-26`).

### 2. Peer-Reviewed Literature
- T. P. Baker, *"Stack-Based Scheduling of Realtime Processes"*, *Real-Time Systems*, 3(1), 1991, pp. 67–99, DOI: `10.1007/BF00365393`.
- P. Gai, G. Lipari, M. Di Natale, *"Minimizing Memory Utilization of Real-Time Task Sets in Single and Multi-Processor Systems-on-a-Chip"*, IEEE RTSS 2001, pp. 73–83, DOI: `10.1109/REAL.2001.990598`.
- B. B. Brandenburg, J. H. Anderson, *"Optimality Results for Multiprocessor Real-Time Locking"*, IEEE RTSS 2010, pp. 49–60, DOI: `10.1109/RTSS.2010.17`.
- J. Eriksson et al., *"Real-Time for the Masses, Step 1: Programming API and Static Priority SRP Kernel Primitives"*, IEEE SIES 2013, pp. 110–113, DOI: `10.1109/SIES.2013.6601482`.

### 3. Assembly Verification of `fence io, io` Emission (`2026-11-20`)
Compiling with `rustc 1.98.0-nightly -C opt-level=2 --crate-type=lib --target=riscv64gc-unknown-none-elf --emit=asm` verifies exact emission of `sw a3, 0(a0); fence io, io; sw a2, 0(a1); ret`:
```rust
#[cfg(target_arch = "riscv64")]
#[no_mangle]
pub unsafe extern "C" fn isr_w1c_complete_io_fence(dev_w1c: *mut u32, plic_claim: *mut u32, id: u32) {
    volatile_store(dev_w1c, 1);
    asm!("fence io, io", options(nostack, preserves_flags));
    volatile_store(plic_claim, id);
}
```

## Revalidation

1. **Diff QEMU `sifive_plic.c` (`< 10 s`):** Inspect `sifive_plic_claimed`, `sifive_plic_read`, and `sifive_plic_write` (`contextid == 4`) to check whether QEMU still filters `CONTEXT_CLAIM` reads by `target_priority` and still omits the `plic->enable` check on completion writes.
2. **Diff LLVM `RISCVInstrInfo.td` (`< 5 s`):** Check `atomic_fence` patterns (`lines 1725-1732`) to confirm `Ordering::SeqCst` still emits `(FENCE 0b11, 0b11)` (`fence rw, rw`), keeping explicit `asm!("fence io, io")` / `asm!("fence iorw, iorw")` mandatory for MMIO ordering.
3. **Static 5-Rule ISR Checklist:** Verify on any RISC-V PLIC + MSRP codebase that: (R1) `CONTEXT_CLAIM` is read under `sstatus.SIE = 0` *before* raising `CONTEXT_THRESHOLD` and `claim == 0` skips EOI; (R2) `IE[ctx, id] == 1` holds during `CONTEXT_CLAIM` EOI (or uses `plic_irq_eoi` toggling); (R3) `W1C` clears execute readback + `fence io, io` before EOI and lock mixed `RW + W1C` registers; (R4) nested `SIE = 1` saves `(sepc, sstatus, prev_thresh)` + `fence io, io` after threshold elevation and masks `SIE = 0` before CSR restore/EOI; and (R5) every cross-hart spinlock raises local ceiling (`SIE = 0` or `threshold = P_max`) *before* spinning and lowers it *after* unlock.
