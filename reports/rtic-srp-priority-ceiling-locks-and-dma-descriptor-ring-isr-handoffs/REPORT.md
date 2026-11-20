# RTIC Stack Resource Policy Priority-Ceiling Locks, Zero-Copy SPSC DMA Ring Handoffs, and Static Stack/WCET Bounds

## Summary

Single-core bare-metal Rust frameworks such as Real-Time Interrupt-driven Concurrency (`rtic-rs/rtic`) and `embassy-sync` (`embassy-rs/embassy`) eliminate heap allocation, per-task OS stacks, and atomic CAS lock words by coupling hardware interrupt prioritization with compile-time ownership checks. In `rtic` v2.4.0 (`fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`), shared static resources live in `RacyCell<T>(UnsafeCell<T>)` (`rtic/src/lib.rs:73–104`), whose raw pointer `.get_mut()` is soundly cast to `&mut T` solely because `rtic-macros` lowers Baker's **Stack Resource Policy (SRP)** (`Real-Time Systems` 1991, DOI `10.1007/BF00365393`) into static priority ceilings $\Pi(r)$ and hardware interrupt-masking prologues.

Five primary verification requirements govern these designs:

1. **Baker SRP unifies `&mut T` disjointness, deadlock freedom, and single-stack bounding:** Under Baker's preemption condition $P(\tau') > \pi_{\text{sys}}$ where holding resource $r$ raises system ceiling $\pi_{\text{sys}}$ to $\Pi(r) = \max \{ P(\tau) \mid r \in \text{uses}(\tau) \}$, no task capable of acquiring $r$ can preempt a holder of $r$. This discharges `&mut T` uniqueness on `RacyCell<T>`, bounds blocking to one critical section without deadlock, and bounds total stack depth to $S(\text{idle}) + \sum_{p > 0} \max_{P(\tau)=p} S(\tau)$.
2. **Macro-checked `lock_free` and `Send`/`Sync` boundaries (`rtic-macros/src/syntax/analyze.rs`):** `#[shared(lock_free)]` is forbidden across distinct priorities and across any `async` software task (`L75–108`), because cooperative `.await` interleaving on a shared dispatcher would allow two `async` tasks at the same priority to hold simultaneous `&mut T` borrows. Resources with `ceiling != 0` require `Send`, and immutably shared resources across priorities require `Sync`.
3. **Hardware ceiling locks have critical ISA/nesting corner cases:** On ARMv7-M/v8-M Mainline (`cortex_basepri.rs:62–83`), because hardware `BASEPRI = 0` disables masking, maximum-ceiling locks (`ceiling == 1 << nvic_prio_bits`) must escalate to `critical_section::with`, and every `basepri_max::write` needs an `isb()` plus an exit compiler barrier (`asm!("", options(nostack, preserves_flags))`). On ARMv6-M/v8-M Baseline (`cortex_source_mask.rs:137–216`), nested locks (`racy-source-masking.rs`) break `&mut T` exclusivity unless unlock writes `old_mask & mask` to `NVIC.ISER`.
4. **`embassy_sync::zerocopy_channel` is slot-disjoint modulo `Receiver::clear()` and DMA cancellation:** Exhaustive BFS over `State` (`zerocopy_channel.rs:338–416`) shows zero `SendSlot`/`ReceiveSlot` index collisions for capacities $N \in \{1..4\}$ without `clear()`. Yet `Receiver::clear(&mut self)` (`L284–288`) borrows only `&Channel` and resets `front = back = 0` without invalidating a live `SendSlot`, creating a 6-step desynchronization trace on $N=2$ where `try_receive()` yields cleared `slot[0]` and skips `slot[1]`. Hardware DMA rings additionally require completion gating before `SendSlot::drop` and explicit `DmaFence::release`/`acquire` (`tock/tock` `dma_fence.rs:67–83`).
5. **Pass-1 Lean 4 (`v4.34.1`) checking requires zero TCB growth for static SRP/ring properties:** Ceiling admissibility, `lockFree` rules, `srpSingleStackBound`, and guarded SPSC ring transitions express directly using `prelude` `Init.*` modules, `List.foldr`, and `@Nat.rec` within Anneal (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`).

## Applicability

These findings apply to single-core interrupt-driven Rust firmware and verification models matching `REPORT.json`:

- **RTIC (`rtic-rs/rtic` `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`, v2.4.0):** Hardware tasks (`#[task(binds = ..., priority = p)]`), async software tasks (`#[task(priority = p)]`), `#[idle]`, `RacyCell<T>`, ARM `cortex_basepri` (`thumbv7`/`thumbv8main`), ARM `cortex_source_mask` (`thumbv6`/`thumbv8base`), and RISC-V `riscv-slic` (`slic.rs`).
- **Embassy (`embassy-rs/embassy` `bb6ce6898623c65de7ae8f4ad5ef4f795eb1ee18`, `embassy-sync` v0.8.0):** `zerocopy_channel::{Channel, Sender, Receiver, SendSlot, ReceiveSlot}` over `RawMutex` (`CriticalSectionRawMutex`, `ThreadModeRawMutex`, or SRP ceiling mutex).
- **Tock DMA Fence (`tock/tock` `ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, v0.2.4-dev):** `kernel::platform::dma_fence::DmaFence`.
- **Lean 4 / Anneal (`joshlf/anneal` `20aa204315cd36aaf944778b7d33c0d609ced8e8`, Lean `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`):** Pure `prelude` certificate design; `Trusted.MirSemantics` at that baseline marks `InlineAsm` and raw pointers `.unsupported` (see **Boundaries**).
- **Corpus Cross-References:** Complements [anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal](../../reports/anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal/REPORT.md) and [tock-asterinas-redleaf-theseus-and-rust-os-isolation-boundaries](../../reports/tock-asterinas-redleaf-theseus-and-rust-os-isolation-boundaries/REPORT.md).

## Findings

### 1. Baker's Stack Resource Policy (SRP) and Single-Stack `&mut T` Disjointness

`Basis: documentation + derived`

Baker (1991, *Real-Time Systems* 3(1), DOI `10.1007/BF00365393`) refines Sha, Rajkumar, and Lehoczky's Priority Ceiling Protocol (PCP, IEEE *Trans. Computers* 1990, DOI `10.1109/12.57058`) and Liu–Layland fixed-priority scheduling (1973, *JACM*, DOI `10.1145/321738.321743`) so preempting tasks share one runtime call stack.

Let $\mathcal{T}$ be tasks with static priorities $P(\tau) \in \mathbb{N}$ ($P(\text{idle}) = 0$) and $\mathcal{R}$ be shared resources. Each resource $r \in \mathcal{R}$ has static ceiling $\Pi(r) \triangleq \max(\{0\} \cup \{ P(\tau) \mid r \in \text{uses}(\tau) \})$. The dynamic system ceiling is $\pi_{\text{sys}} = \max(P(\tau_{\text{running}}), \max_{r \in \text{Held}} \Pi(r))$. **Baker's Preemption Rule** permits an arriving job $\tau'$ to preempt $\tau_{\text{running}}$ iff $P(\tau') > \pi_{\text{sys}}$.

| Property | Priority Inheritance / Basic PCP | Baker's SRP | Embedded Rust Consequence |
| :--- | :--- | :--- | :--- |
| **Blocking Point** | At `lock()` inside preempted task | **Before** task starts (`preemption test`) | Zero blocked frames or TCB context switches |
| **Stack Architecture** | Separate stack per task ($O(\sum_\tau S(\tau))$) | **Single shared stack** | RAM shrinks to sum of max frame per priority level |
| **Deadlock / Chaining** | Deadlock-free; inheritance allows chains | **Zero deadlock, $\le 1$ blocking section** | Nested locks cannot deadlock regardless of order |
| **Lock Word** | Runtime `AtomicBool` per mutex | **None** on single core (IRQ mask is lock) | `RacyCell::get_mut()` casts directly to `&mut T` |

**Derived Soundness Consequences:**
1. **`&mut T` Aliasing Disjointness:** While $\tau_1$ holds $r$, any task $\tau_2$ using $r$ has $P(\tau_2) \le \Pi(r) \le \pi_{\text{sys}}$, so $\tau_2$ cannot preempt until $\tau_1$ unlocks $r$ and lowers $\pi_{\text{sys}}$. Thus at most one `&mut T` reference to $r$ is ever active on the single core.
2. **LIFO Unwinding:** Any preempting task $\tau_2$ has $P(\tau_2) > \pi_{\text{sys}} \ge \Pi(r)$ for all held $r$, so $\tau_2$ cannot request any held $r$ and finishes before $\tau_1$ resumes.
3. **Single-Blocking Bound:** Task $\tau_i$ suffers at most one priority-inversion block $B_i \le \max \{ C_{l,r} \mid P(\tau_l) < P(\tau_i) \le \Pi(r) \}$, where $C_{l,r}$ is $\tau_l$'s critical-section WCET holding $r$.
4. **Tight Single-Stack Bound:** At most one frame per priority level $p$ is active simultaneously:
   $$S_{\text{total}} = S(\text{idle}) + \sum_{p \in \mathcal{P}_{>0}} \max_{\tau \in \mathcal{T},\; P(\tau)=p} S(\tau)$$
   where $S(\tau)$ sums hardware interrupt-entry stacking (32 bytes on Cortex-M without FPU; +68/+72 bytes with lazy/eager FPU state) and $\tau$'s static call-DAG stack depth.

### 2. RTIC v2.4.0 `RacyCell<T>`, `Ownership` Lattice, and `#[shared(lock_free)]`

`Basis: source + derived`

RTIC stores shared statics inside `rtic::RacyCell<MaybeUninit<T>>` (`rtic-macros/src/codegen/shared_resources.rs:50`), defined at `rtic/src/lib.rs:73–104`:

```rust
#[repr(transparent)]
pub struct RacyCell<T>(UnsafeCell<T>);
impl<T> RacyCell<T> {
    pub const fn new(value: T) -> Self { RacyCell(UnsafeCell::new(value)) }
    pub unsafe fn get_mut(&self) -> *mut T { self.0.get() }
    pub unsafe fn get(&self) -> *const T { self.0.get() }
}
unsafe impl<T> Sync for RacyCell<T> {}
```

Because `RacyCell<T>` is unconditionally `Sync` (`L104`), type-safety rests on `rtic-macros/src/syntax/analyze.rs`:

1. **`Ownership` Lattice (`L212–244, 388–406`):** Maps each accessed shared resource to `Owned { priority }`, `CoOwned { priority }` (multiple tasks at identical `priority`), or `Contended { ceiling }` (`ceiling = cmp::max(ceiling, priority)`).
2. **`lock_free` Rules (`L75–108`):** `#[shared(lock_free)]` is rejected if used by distinct priorities (`L95–105`) **or** by any `app.software_tasks` (`L80–89`: *"Lock free shared resource ... is used by an async tasks, which is forbidden"*). Multiple `async` tasks at one priority share a cooperative dispatcher (`executor.rs`) and can hold live `&mut T` borrows across `.await` points concurrently; only synchronous run-to-completion hardware ISRs at identical priority serialize without locking.
3. **`Send`/`Sync` Obligations (`L225–295`):** Resources with `ceiling != 0` require `Send` (`send_types`); resources accessed immutably (`access.is_shared()`) across distinct priorities require `Sync` (`sync_types`).
4. **Dispatcher and Exception Bounds (`rtic-macros/src/analyze.rs:42–75`, `bindings/cortex.rs:273–373`):** `architecture_specific_analysis` forbids `NonMaskableInt` and `HardFault` as `binds` targets (since hardware masking cannot block them) and rejects Cortex-M exceptions from `dispatchers`. `analyze.rs:42–45` requires `available_dispatchers.len() >= nonzero_priorities.count()`. `RTIC_ASYNC_MAX_LOGICAL_PRIO` (`bindings/cortex.rs:349–373`) clamps `(min_hw_prio - 1).max(max_sw_prio.saturating_add(1))` to `[1, 1 << NVIC_PRIO_BITS]`.

### 3. Hardware SRP Realizations: `BASEPRI`, Pipeline Barriers, and Source-Mask Nesting

`Basis: source + execution + derived`

| Backend (`rtic/src/export/`) | Ceiling Mechanism | Max-Ceiling Fallback | Entry / Exit Barriers |
| :--- | :--- | :--- | :--- |
| `cortex_basepri.rs` (`L5–83`) | `cortex_logical2hw(c, bits) = ((1 << bits) - c) << (8 - bits)` via `basepri_max::write` | `critical_section::with` if `ceiling == 1 << nvic_prio_bits` (`L69–70`) | Entry `isb()` (`L76`); exit `asm!("", options(nostack, preserves_flags))` + `basepri::write(current)` (`L79–80`) |
| `cortex_source_mask.rs` (`L122–247`) | `Mask<M>` bitset disabling IRQs `< ceiling` in `NVIC.icer[i]` | `critical_section::with` if `ceiling >= 4` (`L129–134`) | `old_mask = read_mask(mask)`; `clear_enable_mask(mask)`; `dsb(); isb();`; body; `asm!(...)`; `set_enable_mask(mask, old_mask)` (`L137–155`) |
| `slic.rs` (`L1–16`) | `riscv_slic::lock` interrupt threshold | Delegated to `riscv-slic` | Delegated to `riscv-slic` CSR/fence primitives |

1. **`BASEPRI == 0` Disable-Masking Trap (`cortex_basepri.rs:69–70`):** On ARMv7-M/v8-M, writing `0` to `BASEPRI` disables priority masking entirely. Because `cortex_logical2hw(1 << bits, bits) == 0`, RTIC must escalate maximum-ceiling resources to `critical_section::with` (`CPSID I`).
2. **Entry `DSB`/`ISB` and Exit Compiler Barriers:** `MSR BASEPRI` requires `ISB` (`L76`) so instructions immediately following do not execute under the prior mask; NVIC `ICER` writes over PPB require `DSB` + `ISB` per ARM AN321 §4.6 (`cortex_source_mask.rs:141–144`). Exit uses `asm!("", options(nostack, preserves_flags))` (`L79` / `L150`) so LLVM cannot sink `*ptr` accesses past mask restoration.
3. **Nested Lock Unmasking Race on ARMv6-M (`racy-source-masking.rs:37–73`):** When task `foo` (prio 0) holds `shared2.lock` (mask `{GPIOA, GPIOB}`) and nests `shared1.lock` (same mask), naively writing `ISER = mask` on inner lock exit re-enables `GPIOB` while `&mut shared2` is still live (`Probe A2`: `gpiob_enabled_while_outer_lock_held = True`). RTIC's `read_mask(mask)` + `set_enable_mask(mask, old_mask)` (`L138, 212`) writes `old_mask.0[i] & mask.0[i]`, keeping `GPIOB` masked until `shared2.lock` exits (`gpiob_enabled_while_outer_lock_held = False`).

### 4. Zero-Copy SPSC Ring Handoffs (`embassy_sync::zerocopy_channel`) and DMA Coupling

`Basis: source + execution + derived`

`embassy_sync::zerocopy_channel::Channel<'a, M, T>` (`embassy-rs/embassy@bb6ce6898623c65de7ae8f4ad5ef4f795eb1ee18`, `embassy-sync/src/zerocopy_channel.rs:39–416`) manages a circular buffer `BufferPtr<T>(*mut T)` (`L101–110`, `unsafe impl Send/Sync`) using `Mutex<M, RefCell<State>>` (`capacity = buf.len() != 0`, `front`, `back`, `full`).

1. **Two-Phase Disjointness Without `clear()` (`L125–335, 381–415`):**
   - `Sender::{try_send, poll_send, send}(&mut self)` locks `state`, calls `push_index()` (`None` if `full`, else `Some(back)`), and returns `SendSlot<'_, M, T>` holding `value: &mut *buf.add(i)` **without advancing `back`**. Calling `SendSlot::send_done(self)` calls `push_done()`, incrementing `back := (back + 1) % capacity` and setting `full := (back == front)`.
   - `Receiver::{try_receive, poll_receive, receive}(&mut self)` symmetrically yields `ReceiveSlot<'_, M, T>` at `front` and advances `front` on `ReceiveSlot::receive_done(self)` (`full := false`).
   - Whenever both `SendSlot` and `ReceiveSlot` are live, `!full` and `!(front == back && !full)` force `front != back`. Exhaustive BFS (`Probe A1`) confirms `0` slot-aliasing or FIFO-desync states across $N \in \{1, 2, 3, 4\}$ (`13`, `29`, `49`, `73` states).
2. **Hazard 1 — `Receiver::clear(&mut self)` Desynchronization (`L284–288, 360–367`):**
   While `Channel::clear(&mut self)` (`L77–81`) exclusively borrows the entire channel, `Receiver::clear(&mut self)` borrows only `&mut Receiver` while `Sender` holds `&Channel`. `Probe A1` (`N = 2`, `123` states) yields a 6-step safe-Rust counterexample: `try_send -> 0`, `write(msg_0); send_done` (`back=1`), `try_send -> 1` (live `SendSlot[1]`), `receiver.clear()` (`front=0, back=0, full=false`), `write(msg_1); send_done` (`back=1` while writing to `slot[1]`), `try_receive()` -> reads **stale `slot[0] == msg_0`** while `msg_1` in `slot[1]` is lost!
3. **Hazard 2 — `RawMutex` Selection and Async DMA Cancellation (`dma_fence.rs:67–83`):**
   ISR/task SPSC handoffs require `CriticalSectionRawMutex` or an SRP ceiling lock (never `ThreadModeRawMutex`, which fails to mask ISRs). Moreover, if a producer passes `SendSlot` memory to hardware DMA and suspends at `.await`, future cancellation drops `SendSlot` without `send_done()`, returning the buffer to free rotation while DMA still writes to it. Non-coherent/weakly-ordered DMA additionally requires `DmaFence::release(buf)` before doorbell writes and `DmaFence::acquire(buf)` after completion observation (`tock/tock` `kernel/src/platform/dma_fence.rs:67–83`), because `read_volatile`/`write_volatile` and `core::sync::atomic::fence` do not flush/invalidate CPU data caches.

### 5. WCET Accounting and Pass-1 Lean 4 (`v4.34.1`) Checker Design

`Basis: source + documentation + derived`

Wilhelm et al. (2008, *ACM TECS* 7(3), DOI `10.1145/1347375.1347389`) separate static WCET into path/loop-bound analysis and microarchitectural timing. Combining SRP blocking $B_i$ with per-task WCET $C_i$ yields the response-time recurrence:

$$R_i^{(k+1)} = B_i + C_i + \sum_{P(\tau_h) > P(\tau_i)} \left\lceil \frac{R_i^{(k)}}{T_h} \right\rceil C_h, \qquad R_i \le D_i$$

In Anneal (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`), `Trusted.MirSemantics.evalStep` (`L1597–1615`) charges one step per MIR statement/terminator, so `MirWp`'s `@Nat.rec` fuel directly certifies path-step counts while cycle-level $C_i$ requires an ISA/cache bound.

The self-contained Lean 4 (`v4.34.1`) checker below adheres to `TrustedBoundary.lean`'s syntax allowlist (`L472–545`) and locked 51-module `Init.*` prelude (`foundation-lock.json`), using only `List.foldr`, non-dependent `Bool` matches, `0` `_unsafe_rec`, and `0` `Classical.choice`:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.List.Notation

namespace Anneal.Embedded.SrpRingModel

structure TaskSpec where
  id         : Nat
  prio       : Nat
  isAsync    : Bool
  frameBytes : Nat
  usedResIds : List Nat

structure ResourceSpec where
  id       : Nat
  ceiling  : Nat
  lockFree : Bool

def checkSrpResourceTable (resTable : List ResourceSpec) (tasks : List TaskSpec) : Bool :=
  let prioBoundOk :=
    tasks.foldr
      (fun t acc =>
        acc && t.usedResIds.foldr
          (fun rid ok =>
            match resTable.foldr
              (fun r prev => match Nat.beq r.id rid with | true => some r | false => prev)
              none with
            | none => false
            | some r =>
              let asyncOk := match r.lockFree with | true => !t.isAsync | false => true
              ok && asyncOk && Nat.ble t.prio r.ceiling)
          true)
      true
  let lockFreeSinglePrioOk :=
    resTable.foldr
      (fun r ok =>
        match r.lockFree with
        | false => ok
        | true =>
          let seenPrio :=
            tasks.foldr
              (fun t st =>
                let usesR :=
                  t.usedResIds.foldr (fun rid b => b || Nat.beq rid r.id) false
                match usesR with
                | false => st
                | true =>
                  match st with
                  | some (some p) =>
                    match Nat.beq p t.prio with | true => some (some p) | false => none
                  | some none => some (some t.prio)
                  | none => none)
              (some none)
          match seenPrio with
          | none => false
          | some _ => ok)
      true
  prioBoundOk && lockFreeSinglePrioOk

def maxFrameAtPrio (p : Nat) (tasks : List TaskSpec) : Nat :=
  tasks.foldr
    (fun t best =>
      match Nat.beq t.prio p with
      | true  => match Nat.blt best t.frameBytes with | true => t.frameBytes | false => best
      | false => best)
    0

def srpSingleStackBound (prios : List Nat) (tasks : List TaskSpec) : Nat :=
  prios.foldr (fun p acc => maxFrameAtPrio p tasks + acc) 0

structure SpscDmaRing where
  cap           : Nat
  front         : Nat
  back          : Nat
  full          : Bool
  sendInFlight  : Bool
  recvInFlight  : Bool
  dmaBusySlot   : Option Nat
  dmaFenceClean : Bool

def stepSafeRingClear (s : SpscDmaRing) : Option SpscDmaRing :=
  match s.sendInFlight || s.recvInFlight with
  | true  => none
  | false =>
    match s.dmaBusySlot with
    | some _ => none
    | none   => some { s with front := 0, back := 0, full := false }

def stepCommitDmaSend (s : SpscDmaRing) : Option SpscDmaRing :=
  match s.sendInFlight && s.dmaFenceClean with
  | false => none
  | true =>
    match s.dmaBusySlot with
    | some _ => none
    | none =>
      let nextBack := match Nat.beq (s.back + 1) s.cap with | true => 0 | false => s.back + 1
      let nextFull := Nat.beq nextBack s.front
      some { s with
        back := nextBack, full := nextFull, sendInFlight := false,
        dmaBusySlot := some s.back, dmaFenceClean := false }

theorem srp_valid_and_stack_bound_ok :
    checkSrpResourceTable
      [⟨0, 3, false⟩, ⟨1, 2, true⟩]
      [⟨0, 1, true, 128, [0]⟩, ⟨1, 3, false, 256, [0]⟩, ⟨2, 2, false, 192, [1]⟩] = true ∧
    srpSingleStackBound [0, 1, 2, 3]
      [⟨0, 1, true, 128, [0]⟩, ⟨1, 3, false, 256, [0]⟩, ⟨2, 2, false, 192, [1]⟩] = 576 :=
  ⟨rfl, rfl⟩

theorem srp_lock_free_in_async_rejected :
    checkSrpResourceTable [⟨0, 1, true⟩] [⟨0, 1, true, 64, [0]⟩] = false := rfl

theorem ring_clear_rejected_while_send_inflight :
    stepSafeRingClear ⟨2, 0, 1, false, true, false, none, true⟩ = none := rfl

end Anneal.Embedded.SrpRingModel
```

*(Design formulation following `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8` rules; not executed through `lean` during this inspection.)*

## Boundaries

- **known not to apply:**
  - Single-core SRP exclusion and `RacyCell<T>` `&mut T` soundness do **not** apply on multi-core `SMP` systems without cross-core spinlocks/atomics.
  - RTIC hardware masking does **not** protect resources accessed from `NonMaskableInt`, `HardFault`, or exceptions exceeding `critical_section` priority (`bindings/cortex.rs:316–328`).
  - `#[shared(lock_free)]` single-priority sharing does **not** apply to `async` software tasks (`syntax/analyze.rs:80–89`), and `Receiver::clear(&mut self)` (`zerocopy_channel.rs:284–288`) does **not** preserve SPSC FIFO invariants when a `SendSlot` is concurrently alive.
- **unsupported:**
  - `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8` (`MirAst.lean:782–796`, `MirSemantics.lean:1568–1615`) marks `TerminatorKind.inlineAsm`, `TerminatorKind.call`, raw pointers, and `UnsafeCell` as `.unsupported`.
- **unknown:**
  - Whether additive per-block WCET bounds remain sound on speculative or out-of-order pipelines subject to microarchitectural timing anomalies (Wilhelm et al. 2008) cannot be settled from MIR steps alone.
  - Hardware-level timing of `riscv-esp32c3`, `riscv-esp32c6`, and `riscv-clint` RTIC lock backends was not verified by silicon/QEMU execution.
- **not examined:**
  - EDF dynamic-deadline scheduling in `rtic-monotonics`, Baker's multi-unit semaphore extensions, commented-out RISC-V CLIC backends (`rtic/Cargo.toml:55–56`), and `WakerRegistration` missed-wakeup interleavings in `embassy-sync`.

## Evidence

### Primary Sources (`2026-11-20`)

- **`rtic-rs/rtic` (`fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`, v2.4.0):** `rtic/src/lib.rs:51–104` (`RacyCell`); `rtic/src/export/cortex_common.rs:5–7` (`cortex_logical2hw`); `rtic/src/export/cortex_basepri.rs:12–84` (`lock`, `isb`, `asm!`, `critical_section`); `rtic/src/export/cortex_source_mask.rs:16–229` (`read_mask`, `clear_enable_mask`, `dsb`, `isb`, `set_enable_mask`); `rtic/examples/racy-source-masking.rs:37–73`; `rtic/src/export/slic.rs:1–16`; `rtic-macros/src/syntax/analyze.rs:14–406`; `rtic-macros/src/analyze.rs:26–82`; `rtic-macros/src/codegen/shared_resources.rs:13–108`; `rtic-macros/src/codegen/bindings/cortex.rs:267–374`.
- **`embassy-rs/embassy` (`bb6ce6898623c65de7ae8f4ad5ef4f795eb1ee18`, `embassy-sync` v0.8.0):** `embassy-sync/src/zerocopy_channel.rs:39–416` (`Channel`, `BufferPtr`, `Sender`, `SendSlot`, `Receiver`, `ReceiveSlot`, `State`).
- **`tock/tock` (`ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, v0.2.4-dev):** `kernel/src/platform/dma_fence.rs:9–83` (`DmaFence`).
- **`joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`) & `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** `trusted/audit/TrustedBoundary.lean:472–545`, `trusted/lean/Trusted/{MirAst,MirSemantics,foundation-lock.json}`, `theory/Anneal/MirWp.lean:1–55`.
- **Papers:** Baker (1991, DOI `10.1007/BF00365393`), Sha et al. (1990, DOI `10.1109/12.57058`), Liu & Layland (1973, DOI `10.1145/321738.321743`), Lindgren et al. (2015, DOI `10.1109/ICIEA.2015.7334252`), Wilhelm et al. (2008, DOI `10.1145/1347375.1347389`).

### Finite-State Execution Probe & Output (`2026-11-20`, Python 3.13.5 stdlib)

```python
from collections import deque

def check_ring(capacity, allow_clear):
    init = (0, 0, False, None, None, tuple(f"init_{i}" for i in range(capacity)), 0, ())
    q, seen, parent, alias, desync = deque([init]), {init}, {init: None}, None, None
    inc = lambda i: 0 if i + 1 == capacity else i + 1
    def path(s):
        out = []
        while parent[s] is not None: s, a = parent[s]; out.append(a)
        return list(reversed(out))
    while q:
        st = q.popleft()
        f, b, full, si, ri, vals, seq, lq = st
        if si is not None and ri is not None and si == ri and alias is None: alias = path(st)
        tx = []
        if si is None and not full and seq < capacity + 2:
            tx.append((f"try_send() -> Some(SendSlot[{b}])", (f, b, full, b, ri, vals, seq, lq)))
        if si is not None:
            m, nv, nb = f"msg_{seq}", list(vals), inc(b)
            nv[si] = m
            tx.append((f"write(slot[{si}]={m}); send_done() -> back={nb}, full={nb==f}",
                       (f, nb, nb == f, None, ri, tuple(nv), seq + 1, lq + (m,))))
        if ri is None and not (f == b and not full):
            if vals[f] != (lq[0] if lq else "<empty>") and desync is None:
                desync = (st[:6], path(st) + [f"try_receive() -> slot[{f}] holds {vals[f]!r}, expected FIFO head {lq[0]!r}"])
            tx.append((f"try_receive() -> Some(ReceiveSlot[{f}], val={vals[f]})", (f, b, full, si, f, vals, seq, lq)))
        if ri is not None:
            tx.append((f"receive_done() -> front={inc(f)}, full=False", (inc(f), b, False, si, None, vals, seq, lq[1:])))
        if allow_clear and ri is None:
            tx.append(("receiver.clear() -> front=0, back=0, full=False", (0, 0, False, si, None, vals, seq, ())))
        for act, nxt in tx:
            if nxt not in seen: seen.add(nxt); parent[nxt] = (st, act); q.append(nxt)
    return len(seen), alias is not None, desync
```

Observed output (`python3 /tmp/ring_srp_probe.py`):

```text
cap=1 allow_clear=False: states=13 alias=False desync=False
cap=2 allow_clear=False: states=29 alias=False desync=False
cap=3 allow_clear=False: states=49 alias=False desync=False
cap=4 allow_clear=False: states=73 alias=False desync=False
cap=2 allow_clear=True: states=123 alias=False desync=True
Desync witness final pre-recv state: (0, 1, False, None, None, ('msg_0', 'msg_1'))
  1. try_send() -> Some(SendSlot[0])
  2. write(slot[0]=msg_0); send_done() -> back=1, full=False
  3. try_send() -> Some(SendSlot[1])
  4. receiver.clear() -> front=0, back=0, full=False
  5. write(slot[1]=msg_1); send_done() -> back=1, full=False
  6. try_receive() -> slot[0] holds 'msg_0', expected FIFO head 'msg_1'
RTIC cortex_source_mask nesting: buggy={'gpiob_enabled_while_outer_lock_held': True} fixed={'gpiob_enabled_while_outer_lock_held': False}
```

## Revalidation

1. **RTIC SRP & Cortex-M Lock Exports:**
   ```bash
   SHA=$(gh api repos/rtic-rs/rtic/commits/master --jq .sha)
   curl -fsSL "https://raw.githubusercontent.com/rtic-rs/rtic/$SHA/rtic-macros/src/syntax/analyze.rs" | sed -n '75,110p;210,295p'
   curl -fsSL "https://raw.githubusercontent.com/rtic-rs/rtic/$SHA/rtic/src/export/cortex_basepri.rs" | sed -n '60,86p'
   curl -fsSL "https://raw.githubusercontent.com/rtic-rs/rtic/$SHA/rtic/src/export/cortex_source_mask.rs" | sed -n '120,160p;205,217p'
   ```
   Verify `lock_free` still rejects `software_tasks` and mixed priorities, `BASEPRI` escalates at `1 << nvic_prio_bits` with `isb()`, and `cortex_source_mask` restores `old_mask & mask`.
2. **Embassy `zerocopy_channel` `clear()` & `State`:**
   ```bash
   ESHA=$(gh api repos/embassy-rs/embassy/commits/main --jq .sha)
   curl -fsSL "https://raw.githubusercontent.com/embassy-rs/embassy/$ESHA/embassy-sync/src/zerocopy_channel.rs" | sed -n '280,295p;335,416p'
   ```
   Confirm whether `Receiver::clear()` still runs concurrently with `SendSlot`, and re-run the Python BFS probe if `State` transitions change.
3. **Lean 4 Pass-1 Admissibility:** Save the Lean module from Finding 5 into a temporary `.lean` file and check it under Lean `v4.34.1` (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) plus `TrustedBoundary` audit to confirm zero `_unsafe_rec` and axiom subset `{propext}`.
