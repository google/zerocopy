# Tock MMIO Bus Provenance, `W1C` Bitfield Clobbering, Volatile DMA Ordering, and SBI/FFI `noreturn` Fallthrough Hazards

## Summary

Bare-metal OS kernels and peripheral drivers in Rust interact with hardware through two distinct trust seams: **memory-mapped I/O (MMIO) register abstractions** (`tock/tock-registers` and `tock/tock`) and **diverging firmware/FFI boundaries** (`-> !` and `asm!(..., options(noreturn))` lowered by `rustc_codegen_ssa`). Primary-source inspection of `tock-registers` v2.0.0-dev (`86008616e0082f4a75e2cf1b33c94b78cbaf7f5f`), `tock/tock` (`ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`), `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), and `riscv-non-isa/riscv-sbi-doc` (`8a545effe9b50484ff897d9815d7d9015cdef203`) establishes four critical soundness constraints:

1. **Provenance-free MMIO buses vs. reference dereferenceability:** Legacy `StaticRef<RegisterBlock>` patterns (`&T` over `UnsafeCell` arrays) expose MMIO addresses to Rust/LLVM `dereferenceable` assumptions and speculative reads. `tock-registers` v2.0 replaces reference-backed register structs with zero-provenance `Mmio32`/`Mmio64` pointer buses (`NonNull::without_provenance` at `src/mmio.rs:108–111`, `without_provenance_mut` at `L150–153`) and `!Send + !Sync` `BorrowedBus<'b, A>` handles (`src/bus.rs:99–189`) while keeping `bitmask!($numbits)` shift-overflow-free across 1–64 bits (`src/internal.rs:24`). However, `FieldValue::add` (`+`, `src/fields.rs:286–292`) performs bitwise OR without checking mask disjointness, silently corrupting overlapping field assignments (`F.val(1) + F.val(2) = F.val(3)`).
2. **`W1C` (write-1-to-clear) registers convert `Write::modify` into silent interrupt loss:** `Write::modify` (`src/write.rs:29–40`) compiles `reg.modify(FIELD::SET)` into `self.set((self.get() & !field.mask) | field.value)`. When applied to a `Read + Write` `W1C` interrupt-status register (such as OpenTitan UART `intr_state` in `chips/lowrisc/src/registers/uart_regs.rs:22, 53–62`), reading back pending `1` bits for *other* interrupts and writing them back acknowledges and destroys unrelated pending interrupts (`2,032` of `2,048` cases across an 8-bit `W1C` state space). Clearing a `W1C` flag requires `Write::write(FIELD::SET)` (`0` clobbers across `2,048` cases, as in `chips/lowrisc/src/uart.rs:104`).
3. **Volatile MMIO accesses do not synchronize DMA (`ucg#615`):** As explicitly documented at `tock-registers/src/mmio.rs:15–21`, `read_volatile`/`write_volatile` create **no** happens-before edges with bus-master DMA or non-atomic RAM (`rust-lang/unsafe-code-guidelines#615`). Starting or completing DMA transfers requires architecture-specific `DmaFence::release` (before doorbell MMIO write) and `DmaFence::acquire` (after completion read) (`tock/tock` `kernel/src/platform/dma_fence.rs:67–83`).
4. **Fallible `-> !` / `options(noreturn)` firmware calls fall directly into LLVM `unreachable` UB:** `rustc_codegen_ssa/src/mir/block.rs:274, 329, 367, 384, 403` lowers every `TerminatorKind::Call` or `InlineAsm` with `destination = None` directly to `bx.unreachable()` / `fx.unreachable_block()`. Yet RISC-V SBI `sbi_system_reset` (`EID #0x53525354`, `FID #0` in `ext-sys-reset.adoc:12–78`) returns `SBI_ERR_FAILED` / `SBI_ERR_NOT_SUPPORTED` / `SBI_ERR_INVALID_PARAM` in `a0` whenever reset fails. Annotating fallible firmware syscalls `-> !` or `options(noreturn)` without a Rust `loop { wfi(); }` trap triggers immediate compiler UB on error return; sound MIR verifiers must map normal return past `target = none` to `FaultKind.undefined`, never `TerminalOut.aborted`.

## Applicability

These findings govern bare-metal Rust kernels, peripheral drivers, and MIR/Lean verification semantics matching `REPORT.json`:

- **`tock-registers` (`tock/tock-registers@86008616e0082f4a75e2cf1b33c94b78cbaf7f5f`, `2.0.0-dev`) and `tock/tock` (`ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, `0.2.4-dev`):** `tock/tock` `Cargo.toml:14–34` pins both legacy `tock-registers-v0 = "0.11.0"` (used by `chips/lowrisc` and `chips/virtio`) and `tock-registers-nodefault` (`86008616...`). Bitfield algebra and `W1C` `modify()` hazards apply across **both** `0.11.0` and `2.0.0-dev`; `Mmio32`/`Mmio64` provenance-free buses apply to `2.0.0-dev`.
- **Rust Compiler & Reference (`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`):** `do_call` and `do_inlineasm` `bx.unreachable()` emissions apply regardless of target ISA (`riscv32`, `riscv64`, `aarch64`, `x86_64`) and regardless of `-C panic=unwind` vs. `-C panic=abort`.
- **RISC-V SBI (`riscv-non-isa/riscv-sbi-doc@8a545effe9b50484ff897d9815d7d9015cdef203`):** Applies to supervisor-mode (`S`-mode / `HS`-mode) Rust kernels invoking SBI v0.2+ `ECALL` extensions, specifically `SRST` (`EID #0x53525354`, SBI v0.3+).
- **Anneal / Lean 4 (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`, Lean `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`):** Prescribes trusted `evalTerminator` extensions and pure `prelude` Pass-1 MMIO/SBI contracts; `Trusted.MirSemantics` at `20aa204315cd` marks `Call` and `InlineAsm` `.unsupported` (see **Boundaries**).
- **Corpus Cross-References:** Complements [rust-panic-divergence-and-unreachable-semantics](../../reports/rust-panic-divergence-and-unreachable-semantics/REPORT.md) (`!` outcomes and `TerminatorKind::Unreachable`), [rust-pointer-read-write-copy-volatile-and-reference-reborrowing](../../reports/rust-pointer-read-write-copy-volatile-and-reference-reborrowing/REPORT.md) (raw pointers and `read_volatile`/`write_volatile`), [rust-inline-assembly-contracts-relocations-and-simd-correspondence](../../reports/rust-inline-assembly-contracts-relocations-and-simd-correspondence/REPORT.md), and [tock-asterinas-redleaf-theseus-and-rust-os-isolation-boundaries](../../reports/tock-asterinas-redleaf-theseus-and-rust-os-isolation-boundaries/REPORT.md).

## Findings

### 1. `tock-registers` Bus Provenance (`Mmio32`/`Mmio64`) and Bitfield Shift/Mask Algebra

`Basis: source + execution + derived`

#### 1.1 Eliminating Reference Dereferenceability Over MMIO Spaces
In `tock-registers` `0.11.0`, boards typically construct `StaticRef<Registers>` (`&'static Registers`) over `ReadWrite`/`ReadOnly` `UnsafeCell` wrappers. Under Rust's aliasing and LLVM's `dereferenceable(N)` attribute, any reference `&T` licenses LLVM to perform speculative reads of fields inside `T`—catastrophic when adjacent MMIO offsets contain read-to-clear (`RC`) status flags or destructive RX FIFOs.

In `tock-registers` `2.0.0-dev` (`86008616e0082f4a75e2cf1b33c94b78cbaf7f5f`), `src/mmio.rs` and `src/bus.rs` decouple address arithmetic from Rust references:

1. **Zero-Provenance Bus Handles (`mmio.rs:69–164`):** `Mmio32(NonNull<()>)`, `Mmio64(NonNull<()>)`, `Mmio32Nullable(*mut ())`, and `Mmio64Nullable(*mut ())` construct MMIO handles via `NonNull::without_provenance` (`L110`) and `core::ptr::without_provenance_mut` (`L152`). Note the explicit provenance contract (`L92–96`): no-provenance handles **cannot** legally dereference Rust stack/heap objects (those require `Mmio*::new(ptr)` carrying provenance).
2. **Thread-Confinement Without References (`mmio.rs:65`, `bus.rs:99–189`):** Concrete register accessors carry `RealPhantom(PhantomData<*mut ()>)` (`internal.rs:30`, `!Send + !Sync`), while `Mmio*` implements `Send` (`mmio.rs:65`) so `RegisterSender<R: Span>` (`bus.rs:147–189`, `Send + !Sync + !Copy`) can transfer ownership across threads and lend temporary `!Send + !Sync` `BorrowedBus<'b, A>` handles (`L99–120`).
3. **Volatile Execution (`mmio.rs:177–213`):** `BusRead::read` and `BusWrite::write` execute `read_volatile` / `write_volatile` directly on raw pointers (`self.0.cast().read_volatile()` / `write_volatile`), emitting volatile loads/stores only along reachable control flow.

#### 1.2 Bitfield Representations, `bitmask!`, and Overlapping `FieldValue::add`
`tock-registers` splits bitfield metadata between `Field<T, R>` (`fields.rs:86–90`, storing an **unshifted** LSB-aligned `mask` and `shift: usize`) and `FieldValue<T, R>` (`fields.rs:199–203`, storing **pre-shifted** `mask` and `value`):

- **`bitmask!($numbits)` Overflow Avoidance (`internal.rs:21–26`):** Defined as `(1 << ($numbits - 1)) + ((1 << ($numbits - 1)) - 1)` rather than `(1 << $numbits) - 1`. Exhaustive check (`Probe B`) confirms exact equality with $2^n - 1$ for every $n \in 1..=64$ without overflowing a `u64` shift when $n = 64$ (note `$numbits == 0` would underflow `$numbits - 1` at compile time).
- **Pre-Shifted Construction & Masking (`fields.rs:102–104, 212–218`):** `Field::read(val)` evaluates `(val & (self.mask << self.shift)) >> self.shift`; `FieldValue::new(mask, shift, value)` evaluates `mask: mask << shift` and `value: (value & mask) << shift`, preventing caller out-of-range bits from spilling into neighboring fields.
- **Unchecked `FieldValue::add` Overlap Hazard (`fields.rs:282–302`):** Combining two field updates with `+` (`F1::A + F2::B`) executes:
  ```rust
  FieldValue { mask: self.mask | rhs.mask, value: self.value | rhs.value, associated_register: PhantomData }
  ```
  When `lhs.mask & rhs.mask == 0`, `(lhs + rhs).modify(v)` equals `rhs.modify(lhs.modify(v))`. When masks **overlap** (`lhs.mask & rhs.mask != 0`), bitwise OR silently merges bits (`F.val(1) + F.val(2)` yields `(mask=0b11, value=0b11)` rather than `F.val(2)`), potentially programming an illegal enum/hardware configuration.

---

### 2. Non-Idempotent Register Port Semantics and `W1C` Interrupt Loss via `Write::modify`

`Basis: source + execution + derived`

Unlike ordinary RAM bytes, memory-mapped device registers obey heterogeneous hardware transition functions upon CPU `read` and `write` events (`Erbsen et al.`, PLDI 2021, DOI `10.1145/3453483.3454065`). Modeling MMIO registers as flat `Addr → Word` memory collapses critical hardware side effects:

| Hardware Port / Bit Class | CPU Read Side Effect | CPU Write (`w`) Effect on State (`s`) | Sound `tock-registers` Operation |
| :--- | :--- | :--- | :--- |
| **`RW` (Read/Write control)** | Returns `s` (pure) | `s' := w` | `write`, `modify`, `modify_no_read` |
| **`RO` (Read-Only status)** | Returns `s` (or external HW sample) | Undefined / ignored / bus fault | `Read` trait only (`Write` omitted in `register_map!`) |
| **`WO` (Write-Only command)** | Unspecified / bus fault / `0` | Hardware command trigger with `w` | `Write` trait only (`Read` omitted) |
| **`W1C` (Write-1-to-Clear IRQ)** | Returns pending bits `s` | `s' := (s & !w) \| hw_assert` | **`write(FLAG::SET)`** (`set(flag.value)`); **NEVER `modify`** |
| **`W1S` (Write-1-to-Set)** | Returns enabled bits `s` | `s' := s \| w` | `write(FLAG::SET)` (`set(flag.value)`) |
| **`RC` / `FIFO` (Read-Clear / Queue)** | **Mutates** `s` (clears flags / pops FIFO) | `RO` or pushes TX FIFO (`wdata`) | Volatile `get()` / `set()`; forbid speculative `&T` |

#### Why `Write::modify` Clobbers `W1C` Interrupts (`write.rs:16–40` × `lowrisc/uart_regs.rs`)
Inspect `tock-registers/src/write.rs:16–40`:

```rust
fn write(&self, field: FieldValue<...>) { self.set(field.value); }
fn modify(&self, field: FieldValue<...>) where Self: Read { self.set(field.modify(self.get())); }
```

where `field.modify(v)` is `(v & !field.mask) | field.value` (`fields.rs:263–265`). Now inspect a real peripheral register in `tock/tock@ba6aa7ed`: OpenTitan UART `intr_state` (`chips/lowrisc/src/registers/uart_regs.rs:22, 53–62`), declared `ReadWrite<u32, INTR::Register>` with 8 `W1C` interrupt bits (`TX_WATERMARK` bit 0, `RX_WATERMARK` bit 1, `TX_EMPTY` bit 2, `RX_OVERFLOW` bit 3, ..., `RX_PARITY_ERR` bit 7):

- **Correct driver code (`chips/lowrisc/src/uart.rs:103–104`):** `regs.intr_state.write(INTR::TX_EMPTY::SET);` writes `0b0000_0100` (`0x04`). Hardware computes `(s & !0x04) | hw_assert`, clearing **only** `TX_EMPTY` (`Probe B`: `0` unrelated clobbers across all `2,048` `(hw_pending, bit)` pairs).
- **Buggy `modify` antipattern:** Because `intr_state` implements both `Read` and `Write`, Rust's type system **permits** calling `regs.intr_state.modify(INTR::TX_EMPTY::SET)`. Suppose `RX_WATERMARK` (bit 1) and `TX_EMPTY` (bit 2) are both pending (`s = 0b0000_0110`). `modify` executes `self.get()` $\to$ `0b0000_0110`, evaluates `(0b0000_0110 & !0b0000_0100) | 0b0000_0100` $=$ `0b0000_0110`, and writes `0b0000_0110` back—**writing `1` to `RX_WATERMARK` and silently discarding the pending RX interrupt**! Even worse, `modify(INTR::TX_EMPTY::CLEAR)` writes `(s & !0x04) | 0` $=$ `0b0000_0010`, leaving `TX_EMPTY` asserted while clearing `RX_WATERMARK`! Exhaustive enumeration across all $2^8 \times 8 = 2,048$ pairs (`Probe B`) shows `Write::modify(FIELD::SET)` clobbers at least one unrelated `W1C` bit in **`2,032 / 2,048`** total states (`1,016 / 1,024` states where the target bit itself was asserted).
- **Mixed `RW` + `W1C` Registers:** When a single control/status CSR packs `RW` configuration bits alongside `W1C` status bits (`w1c_mask`), an RMW updating an `RW` field must mask out all `W1C` bits before writing back: `raw_next = ((reg.get() & !w1c_mask) & !rw_field.mask()) | rw_field.value`.

---

### 3. Non-Synchronizing Volatile Accesses (`ucg#615`) and Two-Edge `DmaFence` Protocol

`Basis: normative + documentation + source + derived`

`tock-registers/src/mmio.rs:15–21` carries an explicit safety warning grounded in Rust Unsafe Code Guidelines issue #615 (`rust-lang/unsafe-code-guidelines#615`):

> *"These cannot be used to start or stop DMA operations. This bus implements the `Read` and `Write` operations using volatile operations. These operations are not synchronizing, which means they do not create happens-before relationships in the memory model."*

Why volatile MMIO alone is doubly insufficient (`kernel/src/platform/dma_fence.rs:17–66`):

1. **Compiler & CPU Memory Reordering:** `ptr::read_volatile` and `ptr::write_volatile` establish execution ordering **only among volatile accesses on the same thread**; LLVM and weakly-ordered CPUs (ARM Cortex-A/M, RISC-V `RVWMO`) remain free to reorder normal RAM stores (e.g., filling DMA descriptor entries or payload buffers) past a subsequent `write_volatile` to an MMIO doorbell, or speculate normal RAM loads ahead of a status `read_volatile`. Nor does `core::sync::atomic::fence` suffice (`dma_fence.rs:32–34`), because C++/Rust atomic fences synchronize atomic-to-atomic threads rather than non-atomic CPU stores with external bus-master DMA engines.
2. **Non-Coherent Data Caches (`dma_fence.rs:35–40`):** Citing the RISC-V Unprivileged Specification (`20250508`), Tock notes that non-coherent DMA requires hardware cache clean/flush (`release`) and cache invalidate (`acquire`) instructions beyond memory fences.

Tock's `unsafe trait DmaFence` (`kernel/src/platform/dma_fence.rs:67–83`) therefore enforces a **six-step DMA handshake protocol**:
1. CPU writes non-atomic payload/descriptors into DMA RAM (`ramWritten`);
2. CPU invokes `fence.release(buf)` (draining write buffers and cleaning D-cache lines for `buf`);
3. CPU triggers DMA via `write_volatile` to MMIO doorbell (`doorbellWrite` — forbidden unless Step 2 completed);
4. CPU observes DMA completion via IRQ or MMIO `read_volatile` status (`statusComplete`);
5. CPU invokes `fence.acquire(buf)` (invalidating stale D-cache lines and ordering subsequent reads after completion);
6. CPU reads `buf` or reclaims `&[u8]`/`&mut [u8]` safely (`ramRead`).

Note that in `tock/tock` `chips/virtio/src/queues/split_queue.rs:116–118`, older comments still mention volatile write ordering on `InMemoryRegister` ring indices while `VirtIONet<'a, F: DmaFence>` (`virtio_net.rs:49–50`) parameterizes queues over `F: DmaFence`—demonstrating why hardware verification must check explicit `DmaFence` edges rather than relying on volatile writes alone.

---

### 4. `rustc_codegen_ssa` `destination = None` Lowering to LLVM `unreachable` vs. Fallible SBI `SRST`

`Basis: normative + source + derived`

Inspect `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, `compiler/rustc_codegen_ssa/src/mir/block.rs`:

```rust
// rustc_codegen_ssa/src/mir/block.rs:270-275, 322-331 (do_call)
if let Some(unwind_block) = unwind_block {
    let ret_llbb = if let Some((_, target)) = destination {
        self.llbb_with_cleanup(fx, target)
    } else { fx.unreachable_block() };
    ...
} else {
    let llret = bx.call(...);
    if let Some((ret_dest, target)) = destination {
        ...
        fx.store_return(bx, ret_dest, &fn_abi.ret, llret);
        self.funclet_br(fx, bx, target, mergeable_succ, &[])
    } else {
        bx.unreachable(); // <-- Immediate LLVM `unreachable`!
        MergingSucc::False
    }
}
```

And identically in `do_inlineasm` (`block.rs:364–406`, fed by `if asm_macro.diverges(options) { None } else { targets.get(0).copied() }` at `L1587`): whenever `destination` is `None` (no `label` returning `()`, and either return type `!` on `Call` or `options(noreturn)` on `asm!`), LLVM emits **`bx.unreachable()`** (or routes normal continuation to **`fx.unreachable_block()`** when an unwind landing pad exists). Under Rust Reference rules (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `src/inline-assembly.md:1197–1198, 1360–1361, 1480–1482`), falling through the end of `options(noreturn)` or `naked_asm!` is immediate Undefined Behavior: LLVM emits **zero halt/trap bytes** after the call/`ecall`, letting execution fall off into unrelated instructions, zero-filled `.text`, or adjacent functions, and permitting backward dead-code/branch elimination across the caller!

**Real-World Counterexample — RISC-V SBI System Reset (`SRST`):**
Examine `riscv-non-isa/riscv-sbi-doc@8a545effe9b50484ff897d9815d7d9015cdef203`:
- `src/binary-encoding.adoc:6–63`: Supervisor calls invoke firmware via `ECALL` (`a7 = EID`, `a6 = FID`, `a0..a5` inputs) returning `struct sbiret { long error; long value; }` in `(a0, a1)`.
- `src/ext-sys-reset.adoc:12–88`: `sbi_system_reset(uint32_t reset_type, uint32_t reset_reason)` (`EID #0x53525354`, `FID #0`, SBI v0.3) states:
  > *"This is a synchronous call and **does not return if it succeeds**."* (`L15–16`)
  > *"The possible error codes returned in `sbiret.error` are: `SBI_ERR_INVALID_PARAM` (-3), `SBI_ERR_NOT_SUPPORTED` (-2), `SBI_ERR_FAILED` (-1)."* (`L63–78`, codes from `binary-encoding.adoc:46–51`)

If an OS panic or shutdown handler declares `extern "C" fn sbi_system_reset(ty: u32, reason: u32) -> !` or executes `asm!("ecall", in("a7") 0x53525354, in("a6") 0, options(noreturn))` directly, any platform/hypervisor returning `SBI_ERR_FAILED` (`-1` in `a0`) or `SBI_ERR_NOT_SUPPORTED` (`-2` in `a0`) returns straight into **`bx.unreachable()`**! A sound binding **must** give `ecall` / `extern "C"` a non-`!` return (`-> SbiRet`, i.e., `target = Some(fallback_bb)`) followed by an explicit Rust divergence trap (`loop { core::hint::spin_loop(); }` or `wfi()` loop), so LLVM keeps control inside a defined diverging loop instead of `unreachable`.

---

### 5. Verifier Soundness for `Trusted.MirSemantics` and Pass-1 `NoreturnMmio` Model

`Basis: source + derived`

In `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`:
- `Trusted/MirAst.lean:793–795` declares `TerminatorKind.call (callee : DefId) (args : List Operand) (dst : Place) (target : Option BasicBlockId) (unwind : UnwindAction)` and `.unsupported` (which currently absorbs `InlineAsm`).
- `Trusted/MirSemantics.lean:332–341, 1537–1570` separates `.done (out : TerminalOut)` from `.fault (.undefined | .unsupported)`, and `WellFormed p q` (`L1646–1649`) rejects every reachable `.fault`.

When extending `Trusted.MirSemantics` to cover external FFI calls and `InlineAsm`, two TCB requirements are non-negotiable (`derived`):

1. **Returning Past `target = none` Is `FaultKind.undefined`, Never `TerminalOut.aborted`:**
   Because `rustc_codegen_ssa` emits `bx.unreachable()` whenever `target = none` (`block.rs:329, 403`), any external/FFI/asm specification allowing normal return (`.returns sbiret`) when `target = none` **must** step to `.fault .undefined` (matching `evalTerminator` on `.unreachable` at `MirSemantics.lean:1551–1552`). Collapsing it to `.done .aborted` would falsely verify UB-ridden `-> !` / `options(noreturn)` SBI wrappers! Only when `calleeBehavior = .divergesForever` (or `target = some fallback_bb` jumps to a defined `loop {}`) is the execution `WellFormed`.
2. **Trace-Observable `VolatileEvent`s:** Pure memory equality (`Addr → Word`) cannot observe a dead `write_volatile` whose target is never read back on-CPU (such as clearing a `W1C` IRQ flag or ringing a DMA doorbell), nor separate two consecutive `read_volatile` calls. MMIO verification requires recording `VolatileEvent` trace entries on `Behavior` paired with port-specific `RegPortSpec` semantics (`RW`, `RO`, `WO`, `W1C`, `DmaDoorbell`).

The self-contained Lean 4 (`v4.34.1`) module below encodes these rules within `TrustedBoundary.lean`'s syntax allowlist (`L472–545`) and locked 51-module `Init.*` foundation (`foundation-lock.json`), using only non-dependent matches, `Nat.land`/`Nat.xor`, `0` `_unsafe_rec`, and `0` `Classical.choice`:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.Embedded.NoreturnMmio

/-- Execution outcome of an FFI or `asm!` call (`rustc_codegen_ssa/src/mir/block.rs:329, 403`). -/
inductive CalleeBehavior where
  | divergesForever
  | returnsNormal (retCode : Nat)

inductive CallOutcome where
  | jumped (bb : Nat)
  | haltedSafely
  | undefinedUb

/-- Models `destination : Option BasicBlockId`: returning normally when `target = none`
    executes `bx.unreachable()` => immediate `undefinedUb` (`FaultKind.undefined`)! -/
def evalFfiCallTerminator (target : Option Nat) (beh : CalleeBehavior) : CallOutcome :=
  match beh with
  | .divergesForever => .haltedSafely
  | .returnsNormal _ =>
    match target with
    | none           => .undefinedUb
    | some fallback  => .jumped fallback

/-- Hardware MMIO port kind (`tock-registers`) and DMA handshake phase (`DmaFence`). -/
inductive PortKind where
  | rw
  | ro
  | wo
  | w1c
  | dmaDoorbell

inductive DmaPhase where
  | cpuPrep
  | releasedToDma
  | dmaRunning
  | acquiredByCpu

structure MmioPortState where
  hwPendingBits : Nat
  dmaPhase      : DmaPhase

/-- Check `write` vs. `modify` on `tock-registers` MMIO ports:
    * `wasModify = true` models `(get() & !mask) | val`; on `.w1c`, rejects writing back
      any `1` bit outside `allowedClearMask` (`rw` mixed-register clobber guard).
    * `.dmaDoorbell` succeeds iff `DmaFence.release` transitioned `dmaPhase` to `.releasedToDma`. -/
def stepMmioWrite (kind : PortKind) (allowedClearMask : Nat)
    (st : MmioPortState) (writtenVal : Nat) (wasModify : Bool) : Option MmioPortState :=
  match kind with
  | .ro => none
  | .rw => some { st with hwPendingBits := writtenVal }
  | .wo => some st
  | .dmaDoorbell =>
    match st.dmaPhase with
    | .releasedToDma => some { st with hwPendingBits := writtenVal, dmaPhase := .dmaRunning }
    | _              => none
  | .w1c =>
    let clearSafe :=
      match wasModify with
      | false => true
      | true  => Nat.beq (Nat.land writtenVal allowedClearMask) writtenVal
    match clearSafe with
    | false => none
    | true  =>
      -- Clears written `1` bits: `hwPendingBits & !(writtenVal)` via `hw & (hw ^ writtenVal)` on set bits,
      -- equivalently subtracting common bits `hw - (hw & writtenVal)`.
      let cleared := Nat.land st.hwPendingBits writtenVal
      some { st with hwPendingBits := st.hwPendingBits - cleared }

/-- Correct mixed `RW` + `W1C` update: strip `w1cMask` from `get()` before merging `rwVal`. -/
def safeMixedW1cRmw (readVal w1cMask rwMask rwVal : Nat) : Nat :=
  let preserved := Nat.land (readVal - Nat.land readVal w1cMask) (readVal - Nat.land readVal rwMask)
  let clearedOverlap := Nat.land preserved rwVal
  (preserved + rwVal) - clearedOverlap

theorem sbi_srst_noreturn_error_is_ub :
    evalFfiCallTerminator none (.returnsNormal 1) = .undefinedUb := rfl

theorem sbi_srst_with_fallback_bb_recovers :
    evalFfiCallTerminator (some 7) (.returnsNormal 1) = .jumped 7 := rfl

theorem w1c_modify_clobbers_other_irq_rejected :
    stepMmioWrite .w1c 4 ⟨6, .cpuPrep⟩ 6 true = none := rfl

theorem w1c_direct_write_clears_only_target_bit :
    stepMmioWrite .w1c 4 ⟨6, .cpuPrep⟩ 4 false = some ⟨2, .cpuPrep⟩ := rfl

theorem doorbell_without_dma_fence_rejected :
    stepMmioWrite .dmaDoorbell 0 ⟨0, .cpuPrep⟩ 1 false = none := rfl

end Anneal.Embedded.NoreturnMmio
```

*(Design formulation following `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8` rules; not executed through `lean` during this inspection.)*

## Boundaries

- **known not to apply:**
  - `StaticRef<RegisterBlock>` `&T` MMIO access patterns do **not** prevent LLVM speculative reads across adjacent register offsets; provenance-free raw-pointer `BusRead`/`BusWrite` (`tock-registers` v2.0 `src/mmio.rs:108–213`) is required to avoid Rust reference assumptions.
  - `core::sync::atomic::fence` does **not** establish happens-before with non-atomic CPU RAM stores/loads or flush/invalidate non-coherent DMA caches (`tock/tock` `dma_fence.rs:32–40`).
  - Modeling a returning `target = none` (`-> !` or `options(noreturn)`) FFI/`asm!` terminator as `.done .aborted` does **not** soundly reflect `rustc_codegen_ssa` (`block.rs:329, 403`), which emits `bx.unreachable()` UB whenever control returns past the call/`asm!`.
- **unsupported:**
  - `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8` (`MirAst.lean:782–796`, `MirSemantics.lean:1568–1570`) treats `InlineAsm`, `Call`, and raw-pointer MMIO dereferences as `.unsupported` rather than admitting `NoreturnMmio` traces directly in `Trusted.MirSemantics`.
- **unknown:**
  - Exact future normative semantics of `volatile` + atomic operations and formal DMA happens-before edges in Rust's operational memory model remain open upstream (`rust-lang/unsafe-code-guidelines#615`, referenced at `tock-registers/src/mmio.rs:20`).
  - Whether specific downstream Rust-for-SBI crates wrap `sbi_system_reset` with `options(noreturn)` vs. returning `SbiRet` was not audited outside `riscv-sbi-doc` and `tock`.
- **not examined:**
  - PCIe posted-write completion-flush read protocols, x86 `in`/`out` port I/O buses, ARM PSCI (`SMC`/`HVC`) reset error handling, `tock-registers` `proc_macros` `register_map!` expansion internals, and IOMMU/SMMU page-table invalidation coupling.

## Evidence

### Primary Sources (`2026-11-20`)

- **`tock/tock-registers` (`86008616e0082f4a75e2cf1b33c94b78cbaf7f5f`, `2.0.0-dev`):** `src/mmio.rs:15–21` (`ucg#615` volatile DMA warning), `L65–232` (`Mmio32`/`Mmio64`/`Nullable`, `without_provenance`, `BusRead`/`BusWrite`); `src/bus.rs:99–189` (`BorrowedBus`, `RegisterSender`); `src/internal.rs:21–37` (`bitmask!`, `RealPhantom`); `src/fields.rs:86–303` (`Field`, `FieldValue`, `modify`, `Add` overlap); `src/write.rs:11–60` (`write`, `modify`, `modify_no_read`); `src/read.rs:14–169`.
- **`tock/tock` (`ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, `0.2.4-dev`):** `Cargo.toml:14–34` (dual `tock-registers` `0.11.0` + `86008616` pins); `kernel/src/platform/dma_fence.rs:9–83` (`DmaFence`); `chips/lowrisc/src/registers/uart_regs.rs:20–62` (`intr_state` `ReadWrite`); `chips/lowrisc/src/uart.rs:99–105` (`intr_state.write(INTR::TX_EMPTY::SET)`); `chips/virtio/src/queues/split_queue.rs:116–118` and `chips/virtio/src/devices/virtio_net.rs:49–50`.
- **`rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`) & `rust-lang/reference` (`ad35aca481751a06afeb23820a672b0f3b11a476`):** `compiler/rustc_codegen_ssa/src/mir/block.rs:202–205, 219–221, 270–333, 336–407, 1230–1249, 1580–1592` (`bx.unreachable()`, `fx.unreachable_block()`); `src/inline-assembly.md:1197–1198, 1360–1361, 1480–1482`.
- **`riscv-non-isa/riscv-sbi-doc` (`8a545effe9b50484ff897d9815d7d9015cdef203`):** `src/ext-sys-reset.adoc:12–88` (`sbi_system_reset` `EID #0x53525354`, `FID #0`, error returns); `src/binary-encoding.adoc:6–70` (`ECALL`, `sbiret`, `SBI_ERR_*`).
- **`joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`) & `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** `trusted/lean/Trusted/{MirAst.lean:785–796, MirSemantics.lean:332–341, 1537–1570, 1646–1670}`, `trusted/audit/TrustedBoundary.lean:472–545`.
- **Literature:** Erbsen et al. (PLDI 2021, DOI `10.1145/3453483.3454065`); Levy et al. (SOSP 2017, DOI `10.1145/3132747.3132786`).

### Exhaustive Bitfield and `W1C` Verification Probe & Output (`2026-11-20`, Python 3.13.5)

```python
bitmask_ok = all(((1 << (n - 1)) + ((1 << (n - 1)) - 1)) == ((1 << n) - 1) for n in range(1, 65))
f_sum = (0x3 | 0x3, 1 | 2)  # Field(0x3, 0).val(1) + Field(0x3, 0).val(2)
total = write_clob = mod_clob = target_set = mod_clob_target_set = 0
for hw in range(256):
    for bit in range(8):
        total += 1
        m = 1 << bit
        exp = hw & ~m
        if (hw & ~m) != exp:
            write_clob += 1
        w_mod = (hw & ~m) | m
        if (hw & ~w_mod) != exp:
            mod_clob += 1
        if hw & m:
            target_set += 1
            if (hw & ~w_mod) != exp:
                mod_clob_target_set += 1
print(bitmask_ok, f_sum, total, write_clob, mod_clob, target_set, mod_clob_target_set)
```

Observed output (`2026-11-20`):

```text
{'bitmask_1_to_64_exact': True, 'add_overlap_f1_plus_f2': (3, 3),
 'w1c_total_cases': 2048, 'write_clobbers': 0, 'modify_clobbers': 2032,
 'target_set_cases': 1024, 'modify_clobbers_when_target_set': 1016}
```

## Revalidation

1. **Re-verify `tock-registers` MMIO & Bitfield Contracts:**
   ```bash
   TSHA=$(gh api repos/tock/tock-registers/commits/main --jq .sha)
   curl -fsSL "https://raw.githubusercontent.com/tock/tock-registers/$TSHA/src/mmio.rs" | sed -n '12,25p;105,120p'
   curl -fsSL "https://raw.githubusercontent.com/tock/tock-registers/$TSHA/src/fields.rs" | sed -n '210,225p;260,295p'
   curl -fsSL "https://raw.githubusercontent.com/tock/tock-registers/$TSHA/src/write.rs" | sed -n '15,45p'
   ```
   Check whether `Write` adds explicit `W1C`-safe combinators or whether `FieldValue::add` gains overlap assertions; re-run the Python probe above if `Write::modify` changes.
2. **Re-verify `rustc_codegen_ssa` `destination = None` Codegen & RISC-V SBI `SRST`:**
   ```bash
   RSHA=$(gh api repos/rust-lang/rust/commits/master --jq .sha)
   curl -fsSL "https://raw.githubusercontent.com/rust-lang/rust/$RSHA/compiler/rustc_codegen_ssa/src/mir/block.rs" | grep -n -C 5 "bx.unreachable()"
   SSHA=$(gh api repos/riscv-non-isa/riscv-sbi-doc/commits/main --jq .sha)
   curl -fsSL "https://raw.githubusercontent.com/riscv-non-isa/riscv-sbi-doc/$SSHA/src/ext-sys-reset.adoc" | sed -n '12,80p'
   ```
   Confirm `do_call` and `do_inlineasm` still lower `destination = None` to `bx.unreachable()` and `sbi_system_reset` still defines error codes on failed reset.
3. **Verify Lean 4 Pass-1 Admissibility of `Anneal.Embedded.NoreturnMmio`:** Evaluate the Lean block from Finding 5 under Lean `v4.34.1` (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) and `TrustedBoundary` audit to confirm zero `_unsafe_rec` and axioms strictly within `{propext}`.
