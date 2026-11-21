# Symbolic Loop Invariants, 64-Bit Memory-Slot Lenses, and Non-Vacuity Witnesses for Early-Boot Page-Table Verification

## Summary

Formally verifying operating system early-boot assembly (`boot.S` from `_start` to C or Rust kernel entry) requires proving multi-level page-table initialization loops—such as populating `32,768` 4 KiB `Sv39` leaf Page Table Entries (PTEs) across 64 L0 tables for a 128 MiB fine-grained direct map, or `2,048` to `32,768` 2 MiB huge-page entries on `x86-64` and `RV64`. Discharging such loops by concrete fuel unrolling (`stepN fuel s0` via definitional reduction) in dependent-type proof kernels such as Lean 4 fails deterministically against three C++ limits: the elaborator recursion cap (`maxRecDepth = 512`), the kernel `whnf_core` / `is_def_eq_core` recursion guard (`scope_rec_depth = 16 * maxRecDepth = 8,192` frames by default), and the OS thread-stack guard (`check_stack` over `RLIMIT_STACK`, exhausting an 8 MiB stack at `16,000`–`30,000` frames—far below the `131,072` instructions of a 4-instruction loop over `32,768` PTEs).

Scaling boot verification without trusting unverified assembly relies on three composable formal patterns:

1. **Parametric symbolic cut-induction (`O(1)` kernel reduction)**: Cut execution at the loop header with a closed-form invariant `PtFillInv s0 N s_base pa_base flags k s` proved by structural induction (`Nat.rec`) over symbolic `0 <= k <= N`. Each inductive step unfolds *only one loop body* (`4` ISA instructions), keeping kernel `whnf` depth `O(1)` for arbitrary `N`, gated by explicit `BitVec 64` pointer no-wrap (`8 * (s_base + N) < 2^64`) and `Sv39` 44-bit PPN no-overflow (`(pa_base >> 12) + N < 2^44`) side conditions.
2. **8-byte-aligned 64-bit slot lenses (`Slot64`) over byte-addressed ISA RAM**: Authoritative ISA models (`riscv/sail-riscv`) store physical RAM as a byte map (`Std.ExtHashMap Nat (BitVec 8)`), splitting each 64-bit `sd` via `to_bytes_le` into `8` byte writes (`262,144` updates for `32,768` PTEs) and reading PTEs via `from_bytes_le`. Factoring aligned accesses (`addr % 8 = 0`) through a `readSlot64` lens discharges all `8 x 8` byte-offset non-aliasing and endianness obligations once, reducing each `sd` to one slot update while framing `.boot.text` instruction fetches by interval disjointness.
3. **ELF-anchored compositional non-vacuity witnesses**: Multi-clause kernel contracts easily become vacuous (`Pre s <-> False` or 0-step termination) when `W^X` exclusivity, superpage granularity, non-leaf PTE reserved-bit rules (`A = D = U = 0`), and real ELF layouts collide—notably when `.text` (`0x8020_0000`) and `.bss`/stack (`0x8020_4000`) share one `2 MiB` superpage (`0` valid models under `W^X`). A four-link constructive witness (`s_reset -> s_kmain -> s_user -> s_trap`) proves joint satisfiability across ELF reset, `boot.S` MMU activation (`n_boot > 0`), `sret` exit, and synchronous trap return.

## Applicability

These findings apply to formal verification of startup assembly, bootloaders, microkernels, and confidential-VM monitors initializing `RISC-V Sv39` (and structurally `Sv48`/`Sv57`) or `x86-64` 4-level page tables in Lean 4, with comparative grounding in Isabelle/HOL (`seL4/l4v`), Coq (`CertiKOS`), and `Verus`.

The six subjects in `REPORT.json` anchor each layer of the analysis:

1. **`riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`)**: Normative `Sv39` canonical addressing (`bits 63:39 == bit 38`), 3-level 512-entry `4 KiB` tables, PTE bitfields (`[63:54]` reserved/`Svnapot`/`Svpbmt`, `[53:10]` `PPN`, `[9:8]` `RSW`, `[7:0]` `DAGUXWRV`), and superpage alignment rules.
2. **`riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`)**: Official Sail RISC-V specification and Lean 4 backend (`lean_emulator/LeanRiscv.lean`), including byte-addressed `write_ram`/`read_ram` (`model/core/phys_mem_interface.sail`) and `pte_is_invalid` (`model/sys/vmem_pte.sail`).
3. **`leanprover/lean4` (`3100ef55b25b50b44d2010ee44d266e75b28cddd`)**: C++ kernel checker (`src/kernel/type_checker.cpp`), `scope_rec_depth` (`src/runtime/interrupt.cpp`), and OS stack guard (`src/runtime/stackinfo.cpp`).
4. **`seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`) and `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`)**: Concrete `x86-64` and `RISC-V` early-boot paging code (`head.S`, `vspace.c`) and Isabelle/HOL boot axiomatization (`KernelInit_AI.thy`) paired with abstract state inhabitation (`RISCV64/ArchKernelInit_AI.thy`).
5. **`torvalds/linux` (`5f22fb20497f4983094131f00a734362300d22d2`)**: Production RV64 `.Lclear_bss` and `relocate_enable_mmu` boot assembly (`arch/riscv/kernel/head.S`).

This package complements general corpus coverage of specification vacuity (`specification-adequacy-vacuity-detection-and-anti-goodhart-verification`) and Lean 4 WHNF scaling (`lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`) with early-boot MMU loop invariants, `Slot64` lenses, PTE carry bounds, and ELF `W^X` witness chains.

## Findings

### 1. Early-Boot Page-Table Initialization Loops and Concrete-Unrolling Cliffs in Lean 4

`Basis: source + normative + derived`

OS boot code initializes thousands of PTE slots in tight assembly or freestanding C loops before kernel invariants hold:

- **`seL4` `x86-64` (`seL4/seL4`, `src/arch/x86/64/head.S:76-128, 222-245`)**: `setup_pml4` runs two `1,024`-iteration zeroing loops clearing `boot_pml4` and `boot_pdpt`, installs directory links, and executes a **`2,048`-iteration** loop (`head.S:119-127`) writing `2 MiB` huge-page PDEs (`0x87`, stride `+0x200000`) across four `_boot_pd` pages to map `4 GiB` before `enable_x64_mode` (`CR3 -> CR4.PAE -> IA32_EFER.LME -> CR0.PG`).
- **`RISC-V Sv39` direct maps (`supervisor.adoc:1849-1953`; `seL4/seL4`, `src/arch/riscv/kernel/vspace.c:106-165`)**: Each `4 KiB` `Sv39` page table holds $2^9 = 512$ eight-byte PTEs (`#norm:Sv39_pte_count_sz`). Constructing a `128 MiB` fine-grained `4 KiB` direct map (`0x8000_0000 .. 0x8800_0000`, isolating sub-2MiB `.text`, `.rodata`, `.data`, `.bss`, guard pages, and page-table frames under `W^X`) populates `64` L0 leaf tables ($64 \times 512 = \mathbf{32,768}$ leaf PTEs), `64` L1 directory PTEs, and `1` L2 root PTE (`32,833` 8-byte stores; similarly, mapping `64 GiB` with `2 MiB` L1 megapages writes `32,768` L1 leaves).

A standard 4-instruction RV64 PTE-fill loop over $N = 32{,}768$ entries executes $4 \times 32{,}768 = \mathbf{131,072}$ instructions:

```assembly
/* a0 = &pt_l0[0], a1 = &pt_l0[32768], a2 = ((RAM_BASE >> 12) << 10) | FLAGS, a3 = 1 << 10 */
1:  sd    a2, 0(a0)          /* [pc + 0] 8-byte aligned PTE store */
    addi  a0, a0, 8          /* [pc + 4] advance slot pointer by PTESIZE (8) */
    add   a2, a2, a3         /* [pc + 8] increment PPN field at bit 10 */
    bne   a0, a1, 1b         /* [pc + 12] loop while a0 != a1 */
```

Unrolling `runSteps 131072 s0` definitionally in `leanprover/lean4` (`3100ef55b25b50b44d2010ee44d266e75b28cddd`) hits three hard limits:

| Limit Layer | Upstream Mechanism (`leanprover/lean4`) | Default Bound | Failure Point on `boot.S` PTE Loop |
| --- | --- | --- | --- |
| Elaborator recursion guard | `maxRecDepth` (`LeanRiscv.lean:86` sets `2000000` just for flat register init) | `512` | ~`128` PTEs (`1/4` of one `4 KiB` table) |
| Kernel logical depth guard | `scope_rec_depth` in `src/runtime/interrupt.cpp:62-84` (`infer_type_core`, `whnf_core`, `is_def_eq_core` in `src/kernel/type_checker.cpp:321, 457, 1140`) | `16 * maxRecDepth = 8,192` | ~`512`–`2,048` steps (`<= 1` table) |
| Physical OS stack guard | `check_stack` in `src/runtime/stackinfo.cpp:83-106` (`check_system` at `interrupt.cpp:108-115`) over `RLIMIT_STACK` (`8 MiB`) | ~`16,000`–`30,000` C++ frames | `stack_space_exception("type checker: whnf")` well below `32,768` PTEs |

Unrolling also builds a `262,144`-deep map-insertion spine in WHNF, degrading post-`satp` page-table walks to $O(N)$ linear scans inside `is_def_eq`.

### 2. Parametric Symbolic Loop Invariants and `O(1)` Cut-Induction Pattern

`Basis: derived + source`

Following machine-code Hoare / decompilation-into-logic principles (Sewell, Myreen, and Klein, PLDI 2013), unrolling is eliminated by cutting execution at `pc_loop` with a parametric invariant `PtFillInv (s0 : MachineState) (N s_base pa_base : Nat) (flags : BitVec 10) (k : Nat) (s : MachineState) : Prop`:

1. **Control & bound**: `k <= N`, `s.priv = Supervisor`, `s.satp = 0`, `s.pc = BitVec.ofNat 64 pc_loop`.
2. **Closed-form GPRs**: `s.gpr a0 = BitVec.ofNat 64 (8 * (s_base + k))`, `s.gpr a1 = BitVec.ofNat 64 (8 * (s_base + N))`, `s.gpr a2 = mkSv39Pte (pa_base + 4096 * k) flags`, `s.gpr a3 = BitVec.ofNat 64 (1 <<< 10)`, with `sp`, `gp`, `tp`, `ra` preserved from `s0`.
3. **Completed prefix (`0 <= i < k`)**:
   $$\forall i < k,\ \text{readSlot64 } s.\text{mem } (s_{\text{base}} + i) = \text{mkSv39Pte } (\text{pa\_base} + 4096 \cdot i)\ \text{flags}$$
4. **Untouched frame (`q < s_base \/ s_base + k <= q`)**:
   $$\forall q,\ (q < s_{\text{base}} \lor s_{\text{base}} + k \le q) \implies \text{readSlot64 } s.\text{mem } q = \text{readSlot64 } s_0.\text{mem } q$$
5. **Code invariance**: `BootCodeLoaded s.mem` (carried via Clause 4 from `.boot.text` disjointness without re-decoding instructions).

Proving the 4-instruction inductive step over exact `BitVec 64` semantics exposes three essential hardware side conditions:

1. **Pointer non-wrap (`8 * (s_base + N) < 2^64`)**: Prevents `8 * (s_base + k) == 8 * (s_base + N) (mod 2^64)` from firing prematurely at $k < N$.
2. **Packed-PTE `PPN` no-overflow (`(pa_base / 4096) + N < 2^44`)**: Adding `1 << 10` directly to `a2` leaves `flags` (`[9:0]`) intact and increments `PPN` (`[53:10]`) cleanly **if and only if** `ppn_base + k + 1 < 2^44`. At `2^44`, bit 53 carries into **reserved bit 54**, setting `pte[60:54] != 0` and causing `PTW_Invalid_PTE` page faults (`#norm:Sv39_pte_future_rsv`, `supervisor.adoc:1915-1922`; `vmem_pte.sail:117`).
3. **Final-iteration fall-through**: `bne a0, a1, -12` loops to `pc_loop` for $k + 1 < N$ and falls through to `pc_loop + 16` at $k + 1 = N$. Structural induction on `k < N - 1` plus one 4-step exit lemma proves `Steps (4 * N) s_init s_exit` with strictly `O(1)` kernel `whnf` depth for any `N`. Multiple permission sub-ranges (`RX` `.text`, `R` `.rodata`, `RW` `.bss`/stack) compose transitively across $M \in [3, 6]$ consecutive loops via Clause 4.

### 3. Bridging 64-Bit Hardware Memory Slots to Byte-Addressed Abstract ISA Models

`Basis: source + derived + execution`

In `riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`), `lean_emulator/LeanRiscv.lean:34` models RAM as `Std.ExtHashMap Nat (BitVec 8)`, while `write_ram` and `read_ram` (`model/core/phys_mem_interface.sail:140-232`) convert 64-bit words via `to_bytes_le` and `from_bytes_le`. Reasoning directly over byte maps inside loops creates 8 updates and 64 byte-aliasing subgoals per `sd`. Defining an aligned `Slot64` lens eliminates that blowup:

```lean
def readSlot64 (m : UInt64 → BitVec 8) (slot : UInt64) : BitVec 64 :=
  let base := slot <<< 3
  (m (base + 7)).zeroExtend 64 <<< 56 ||| (m (base + 6)).zeroExtend 64 <<< 48 |||
  (m (base + 5)).zeroExtend 64 <<< 40 ||| (m (base + 4)).zeroExtend 64 <<< 32 |||
  (m (base + 3)).zeroExtend 64 <<< 24 ||| (m (base + 2)).zeroExtend 64 <<< 16 |||
  (m (base + 1)).zeroExtend 64 <<< 8  ||| (m (base + 0)).zeroExtend 64
```

Four bridge lemmas seal the byte-to-slot interface:
1. **Same-slot readback**: `addr &&& 7 = 0 -> addr < 2^64 - 7 -> readSlot64 (writeRam8 m addr val) (addr >>> 3) = val`.
2. **Disjoint-slot commutation**: `addr &&& 7 = 0 -> (slot <<< 3) < 2^64 - 7 -> slot != (addr >>> 3) -> readSlot64 (writeRam8 m addr val) slot = readSlot64 m slot`.
3. **Instruction-fetch framing**: If `[code_lo, code_hi)` is disjoint from `[8 * slot_base, 8 * slot_end)`, then `readInst32 (writeRam8 m (slot <<< 3) val) pc = readInst32 m pc` for all `pc` in `.boot.text` and `slot` in `[slot_base, slot_end)`.
4. **`Sv39` PTW correspondence**: Every `Sv39` table base `ppn <<< 12` and entry offset `vpn_i <<< 3` (`0 <= vpn_i < 512`) satisfies `pte_pa &&& 7 = 0` and `pte_pa >>> 3 = (ppn <<< 9) + vpn_i`, rewriting hardware PTW `read_ram` directly to `readSlot64 m ((ppn <<< 9) + vpn_i)`.

### 4. Precondition Vacuity Hazards in Early-Boot and Kernel Verification

`Basis: source + derived + execution`

A theorem $\forall s,\ \text{Pre}(s) \implies \text{Post}(s)$ holds vacuously when $\text{Pre}(s)$ has zero models or admits degenerate 0-step execution (Beer et al., *FMSD* 2001; Kupferman and Vardi, *STTT* 2003). Three domain-specific vacuity hazards arise in boot/kernel verification:

1. **Harness Termination-Flag Vacuity (`LeanRiscv.lean:246-247`)**: `LeanRiscv.lean` explicitly warns: `"an undefined true htif_done would skip execution of the ELF entirely."` Universally quantified initial-state theorems omitting `s0.htif_done = false` (or positive step counts `n > 0`) hold trivially on 0-step halted states.
2. **Cohabited `2 MiB` Superpage `W^X` Contradiction**: When a `4 KiB`-aligned linker script places `.text` at `0x8020_0000 .. 0x8020_4000` and `.bss`/boot-stack at `0x8020_4000 .. 0x8021_0000` inside the *same* `2 MiB` range `[0x8020_0000, 0x8040_0000)`, asserting (a) `W^X` (`¬(pte.W /\ pte.X)` and `¬(¬pte.R /\ pte.W)`), (b) `2 MiB` L1 superpage direct mapping, and (c) executable `PC` (`X = 1`) plus writable `SP` (`R = 1 /\ W = 1`) yields **zero valid `(R, W, X)` assignments**! Any kernel proof assuming `(a) /\ (b) /\ (c)` passes Lean 4 with zero `sorry`s while being completely vacuous on the ELF unless writable sections are aligned to `0x8040_0000` or mapped via `32,768` `4 KiB` L0 leaves.
3. **Non-Leaf `Sv39` PTE `A`/`D`/`U` Rejection (`vmem_pte.sail:106-110`)**: Unlike `x86-64` directory entries, `Sv39` `pte_is_invalid` rejects any non-leaf PTE (`R = W = X = 0`) with `A = 1`, `D = 1`, or `U = 1` when `pte_reserved_bits_must_be_zero` holds. Writing `V | A | D` (`0xC1`) instead of `V` (`0x01`) into L2/L1 pointers faults every hardware walk with `PTW_Invalid_PTE`.

### 5. Compositional Non-Vacuity Witness Construction Across Entry, Exit, and Trap Round-Trips

`Basis: derived + source + execution`

In `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`), `KernelInit_AI.thy:15-16` axiomatizes boot (`akernel_init_invs`), while `RISCV64/ArchKernelInit_AI.thy:17-19, 538` proves `lemma invs_A: "invs init_A_st"` so abstract invariants cannot self-contradict. Extending verification down to `boot.S` and real ELF layouts requires a **four-link constructive witness chain**:

```text
[Concrete ELF s_reset] ──(W1: decide/omega)──▶ ResetPre s_reset
  ──(T_boot: 32,768-PTE symbolic loop, n_boot > 0)──▶ KernelEntryPre s_kmain
  ──(W2: sret transition)──▶ UserModeInv s_user
  ──(W3: U-mode ecall step)──▶ KernelTrapEntryPre s_trap
```

- **W1 (Concrete ELF Inhabitation)**: Instantiate `s_reset` from exact linker intervals (`TEXT = [0x8020_0000, 0x8021_0000)`, `RODATA = [0x8021_0000, 0x8021_8000)`, `RW_BSS_STACK = [0x8040_0000, 0x8042_0000)`, `PT_POOL = [0x8060_0000, 0x8064_2000)`), with `htif_done = false`, `priv = Supervisor`, `satp = 0`, and `mstateen0.ENVCFG = 1`, discharging disjointness and alignment by `decide`/`omega`.
- **`T_boot` (Positive-Step Reachability to `kmain`)**: Composing `PtFillInv` (`n_boot > 131072`) with `stvec -> senvcfg -> sfence.vma -> satp -> sfence.vma` derives `KernelEntryPre s_kmain` constructively from `s_reset`, ruling out both 0-step vacuity and impossible `W^X` / non-leaf PTE contracts.
- **W2 & W3 (`sret` Exit and Trap Round-Trip)**: Stepping an inhabited `s_kmain` through `sret` into `s_user` (`PTE_U = 1` user code/stack) and executing a U-mode `ecall` (`0x00000073`) into `s_trap` proves that `BootPost`, `UserModeInv`, and `KernelTrapEntryPre` agree on `stvec` alignment/mode, `sscratch` swapping, and `Sv39` permissions.

### 6. Cross-Framework Comparison of Boot and Page-Table Verification Architectures

`Basis: documentation + source + derived`

| Framework | Paging Target | Early-Boot (`boot.S`) Scope | Loop & Memory Abstraction | Non-Vacuity Mechanism |
| --- | --- | --- | --- | --- |
| **seL4 (`seL4/l4v`)** (Klein et al. 2009; Sewell et al. 2013) | ARM, x86-64, RV64 `Sv39` | `head.S` + `boot.c` axiomatized (`KernelInit_AI.thy`) | Post-boot binary decompilation into tail-recursive HOL functions | Witness `init_A_st` (`invs_A` in `ArchKernelInit_AI.thy`) |
| **CertiKOS** (Gu et al. 2016) | x86 / x86-64 | Layered asm + C proving paging enabled after PT init | Coq contextual refinement abstracting array slots to `PTPool` | Bottom-up layer inhabitation from `mboot` |
| **Verus** (Lattuada et al. 2024) | x86-64 4-level PT | Rust init post-trampoline | Linear `PointsTo<u64>` ghost tokens + SMT `while` invariants | Constructive borrow-checked execution |
| **Islaris** (Sammler et al. 2022) | ARMv8-A / RV64 Sail | Per-block / loop-cut machine code | Isla symbolic traces + Coq Iris separation logic | Closed-trace Iris adequacy theorem |
| **Lean 4 + Sail RISC-V** | RV64 `Sv39` | Direct `_start -> kmain` assembly | `O(1)` `Nat.rec` cut invariant + `readSlot64` byte-map lens | 4-link ELF witness (`s_reset -> s_kmain -> s_user -> s_trap`) |

## Boundaries

- **Known not to apply — Concrete `rfl`/`decide` unrolling of `32,768`-entry loops in Lean 4**: Unrolling `131,072` ISA steps exceeds `scope_rec_depth` (`interrupt.cpp:78-84`) and `check_stack` (`stackinfo.cpp:100-106`); concrete unrolling is **known not to apply** at direct-map scale.
- **Known not to apply — Cohabited `2 MiB` `W^X` superpages and `A/D/U` bits on non-leaf `Sv39` PTEs**: Sharing one `2 MiB` superpage between `.text` and `.bss`/stack under `W^X` has zero models (`known not to apply`), and `A/D/U` bits on non-leaf `Sv39` PTEs fail `pte_is_invalid` (`vmem_pte.sail:107-109`) (`known not to apply`).
- **Unsupported — `readElf32` on 64-bit ELFs and reset-ROM execution in `LeanRiscv.lean` at `04bcb62c`**: `readElf32` returns `.error "64 bit ELF file not supported"` (`LeanRiscv.lean:25-26`) and `DEFAULT_RSTVEC` (`0x1000`) is commented out (`LeanRiscv.lean:37-55`), making stock reset-ROM boot **unsupported** without a custom harness.
- **Not examined — Multicore SMP `sfence.vma` shootdowns and dynamic `Svadu` A/D updates**: Concurrent cross-hart PTE updates under `RVWMO` and hardware `menvcfg.ADUE = 1` PTE writebacks were **not examined** (leaves pre-set `A = 1`, and `D = 1` when writable).
- **Unknown — Monolithic `bv_decide` scaling over `32,768` unframed stores**: Memory consumption of `bv_decide` on raw `32,768`-store byte-array terms without `Slot64` framing lemmas was not benchmarked and remains **unknown**.

## Evidence

### Normative Specifications and Peer-Reviewed Literature

- **`riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`)**: `src/priv/supervisor.adoc:1849-1953` (`Sv39` virtual addressing, PTE layout, reserved bits `[63:54]`, and superpage alignment).
- **Gerwin Klein et al.**, *"seL4: Formal Verification of an OS Kernel"*, ACM SOSP 2009, DOI: `10.1145/1629575.1629596`.
- **Thomas Sewell, Magnus O. Myreen, and Gerwin Klein**, *"Translation Validation for a Verified OS Kernel"*, ACM PLDI 2013, DOI: `10.1145/2491956.2462183`.
- **Ronghui Gu et al.**, *"CertiKOS: An Extensible Architecture for Building Certified Concurrent OS Kernels"*, USENIX OSDI 2016, DOI: `10.5555/3026877.3026928`.
- **Michael Sammler et al.**, *"Islaris: Verification of Machine Code Against Authoritative ISA Semantics"*, ACM PLDI 2022, DOI: `10.1145/3519939.3523434`.
- **Andrea Lattuada et al.**, *"Verus: A Practical Foundation for Systems Verification"*, ACM SOSP 2024, DOI: `10.1145/3694715.3695952`.
- **Ilan Beer et al.**, *"Efficient Detection of Vacuity in Temporal Model Checking"*, FMSD 18(2), 2001, DOI: `10.1023/A:1008779610539`, and **Orna Kupferman and Moshe Y. Vardi**, *"Vacuity Detection in Temporal Model Checking"*, STTT 4(2), 2003, DOI: `10.1007/s100090100062`.

### Upstream Source Repositories (Observed `2026-11-20`)

- **`leanprover/lean4` (`3100ef55b25b50b44d2010ee44d266e75b28cddd`)**: `src/kernel/type_checker.cpp:318-323, 456-459, 1139-1142`, `src/runtime/interrupt.cpp:54-86, 108-115`, `src/runtime/stackinfo.cpp:69-106`.
- **`riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`)**: `model/core/phys_mem_interface.sail:140-232`, `model/sys/vmem_pte.sail:19-119`, `model/sys/vmem_ptw.sail:16-142`, `lean_emulator/LeanRiscv.lean:17-103, 246-311`.
- **`seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`)**: `src/arch/x86/64/head.S:76-128, 222-245`, `src/arch/riscv/head.S:23-63`, `src/arch/riscv/kernel/vspace.c:106-165`.
- **`seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`)**: `proof/invariant-abstract/KernelInit_AI.thy:15-16`, `proof/invariant-abstract/RISCV64/ArchKernelInit_AI.thy:17-19, 538-565`.
- **`torvalds/linux` (`5f22fb20497f4983094131f00a734362300d22d2`)**: `arch/riscv/kernel/head.S:76-125, 274-305`.

### Execution Verification

Python 3.13 verification (`observed_at`: `2026-11-20`) populated `32,833` 64-bit PTE slots (`262,664` byte writes via `to_bytes_le`), confirmed identity 3-level `Sv39` PTW walks and `W^X` compliance across all `32,768` `4 KiB` leaves (`text=(0x80200000, 0x6b)`, `stack=(0x8041fff0, 0xe7)`), verified non-leaf `A = D = U = 0` checks, and confirmed `0` valid `(R, W, X)` models on cohabited `2 MiB` megapages.

## Revalidation

1. **Run the self-contained `32,768`-leaf `Sv39` `Slot64` and `W^X` non-vacuity probe** (Python 3.10+ stdlib; `<150 ms`):

   ```bash
   python3 - <<'PY'
   PAGESIZE, PTES, L0_CNT = 4096, 512, 64
   LEAVES = L0_CNT * PTES  # 32,768 4KiB PTEs (128 MiB)
   V, R, W, X, G, A, D = 1, 2, 4, 8, 32, 64, 128

   mem = {}
   def write_ram8(pa, val):
       assert (pa & 7) == 0
       for i, b in enumerate(val.to_bytes(8, "little")):
           mem[pa + i] = b

   def read_slot64(slot):
       pa = slot << 3
       return int.from_bytes(bytes(mem.get(pa + i, 0) for i in range(8)), "little")

   def pte(pa, flags):
       return ((pa >> 12) << 10) | flags

   RAM, TEXT, TEXT_END = 0x80000000, 0x80200000, 0x80210000
   L2, L1, L0 = 0x80600000, 0x80601000, 0x80602000

   write_ram8(L2 + 8 * ((RAM >> 30) & 0x1FF), pte(L1, V))
   for j in range(L0_CNT):
       write_ram8(L1 + 8 * j, pte(L0 + j * PAGESIZE, V))
   for k in range(LEAVES):
       pa = RAM + k * PAGESIZE
       fl = (V | R | X | G | A) if (TEXT <= pa < TEXT_END) else (V | R | W | G | A | D)
       write_ram8(L0 + 8 * k, pte(pa, fl))

   def walk_sv39(root, va):
       a = root
       for lvl in (2, 1, 0):
           idx = (va >> (12 + 9 * lvl)) & 0x1FF
           ent = read_slot64((a >> 3) + idx)
           if not (ent & V) or ((ent & W) and not (ent & R)) or (ent >> 54):
               return None
           ppn = (ent >> 10) & ((1 << 44) - 1)
           if not (ent & (R | X)):
               if ent & (A | D | 16):
                   return None
               a = ppn << 12
               continue
           return (ppn << 12) | (va & ((1 << (12 + 9 * lvl)) - 1)), ent & 0xFF
       return None

   assert len(mem) == (1 + L0_CNT + LEAVES) * 8 == 262664
   for k in range(LEAVES):
       va = RAM + k * PAGESIZE
       pa_out, fl = walk_sv39(L2, va)
       assert pa_out == va and not ((fl & W) and (fl & X))

   models = [
       (r, w, x) for r in (0, 1) for w in (0, 1) for x in (0, 1)
       if not (r == 0 and w == 1) and not (w and x) and x == 1 and (r and w)
   ]
   assert models == []
   print("OK: 32,768 Sv39 leaves verified via Slot64 lens; cohabited 2MiB W^X models = 0")
   PY
   ```

2. **Check upstream invariants on newer revisions**:
   - `leanprover/lean4`: check `g_kernel_rec_depth_factor` / `scope_rec_depth` in `src/runtime/interrupt.cpp` and `check_stack` in `src/runtime/stackinfo.cpp`.
   - `riscv/sail-riscv`: check `write_ram`/`read_ram` in `model/core/phys_mem_interface.sail`, `pte_is_invalid` in `model/sys/vmem_pte.sail`, and `LeanRiscv.lean`.
   - `seL4/l4v`: check `KernelInit_AI.thy` and `RISCV64/ArchKernelInit_AI.thy` for `akernel_init_invs` and `invs_A`.
