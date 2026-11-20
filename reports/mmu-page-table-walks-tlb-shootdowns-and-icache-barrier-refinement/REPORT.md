# Formal MMU Page-Table Walks, Cross-ISA TLB Shootdowns, and Instruction-Cache Barrier Refinement

## Summary

Hardware Memory Management Units (MMUs) and split Harvard instruction/data caches across RISC-V (`Sv39`/`Sv48` + `Zifencei`), ARMv8-A (`VMSAv8-64`), and x86-64 (`IA-32e` paging) violate naive memory-coupled semantics in two ways that break OS kernel and hypervisor proofs:

1. **Non-Deterministic Partial-Walk Directory Caching (PWCs):** Hardware address-translation caches store both resolved leaf translations (`level = 0` or superpages) and **intermediate directory entries** (`level > 0`: RISC-V non-leaf PTEs, ARMv8 walk-cache table descriptors, x86-64 PML4E/PDPTE/PDE paging-structure caches). Single-address invalidation instructions behave **asymmetrically across architectures**:
   - **RISC-V:** `SFENCE.VMA va, asid` (`rs1 ≠ x0, rs2 ≠ x0`) is guaranteed to invalidate **only leaf PTEs** at `(va, asid)` (`#norm:sfence_vma_va_asid`). Implementations may over-fence (`supervisor.adoc:1266–1275`), so software can rely only on the leaf guarantee; stale non-leaf directory PTEs survive unless software executes `SFENCE.VMA x0, asid` (`rs1 = x0`), and any path with `G = 1` survives unless `rs2 = x0`.
   - **ARMv8-A:** `TLBI VALE1IS` spares walk caches while `TLBI VAE1IS` flushes walk caches along `va`, yet unmapping an intermediate directory still leaves sibling leaf TLBs (`va' ≠ va`) active unless `TLBI ASIDE1IS` (or child-range invalidation) plus `DSB ISH` + `ISB` is executed—preceded by `DC CVAU` (`cleanByVA_PoU`) when page-table walkers do not snoop D-cache.
   - **x86-64:** `INVLPG m` wipes **all** PML4E/PDPTE/PDE paging-structure caches for the current PCID regardless of `m`, while sparing sibling leaf TLB entries (`m' ≠ m`) and other PCIDs.
2. **Executable ISA Simulator Under-Approximation:** Mainstream executable ISA specifications—including `riscv/sail-riscv` (`vmem_tlb.sail` leaf-only hash-indexed TLB; `zifencei_insts.sail` `fence.i` memory no-op) and `acl2/x86isa` (`cache.lisp` wiping the entire `:tlb` table on `INVLPG`)—**under-approximate** permissive hardware caching. One corner of `sail-riscv` goes the other way:
   - When hardware A/D updating is enabled, a TLB hit writes the *cached* PTE back with new A/D bits and no compare against memory (`model/sys/vmem.sail:370–413` → `update_and_write_pte:95–119`).
   - The specification's step 9 forbids this when the cached PTE is stale.
   - This was found by source reading only; see package `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors` §1.7.

   Verifying OS `VSpace` or JIT code directly against such deterministic simulators misses missing `rs1 = x0` directory flushes, global-bit leaks, and missing `fence.i`/`ISB` barriers.
3. **Ghost Dirty-Set Reduction & Specification-Role ISA Placement:** Kernel refinement proofs reduce full PWC + TLB + I-cache nondeterminism to a constructive `Type 0` **Ghost Dirty-Set Automaton** (`BarrierGhostState`: `tlbDirty`, `remoteDirty`, `icacheDirtyPpn`). Proving `coherentSystemWide = true` before user return discharges both cached-walk `W^X` isolation and dynamic code-load (`W → X`) instruction-fetch coherence. In modular Rust verifiers (`joshlf/anneal`), target ISA models belong in the human-reviewed **per-crate specification surface** (`Spec/*.lean`) paired with `0-TCB` `theory/` barrier combinators—never inside the language-level MIR TCB (`trusted/lean/`), and decoupled from `sail --lean`'s custom `axiom` declarations (`RiscvExtras.lean`).

## Applicability

This report governs formal verification of OS microkernels, VSpace managers, dynamic module/ELF loaders, JIT compilers, and trap/context-switch boundaries across 64-bit RISC-V, ARMv8-A, and x86-64 targets:

- **Normative Architectural Envelopes (`riscv/riscv-isa-manual` at `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, Intel SDM Vol. 3A §4.10, Arm ARM DDI 0487):** Define required invalidation scopes of `SFENCE.VMA`, `FENCE.I`, `TLBI` + `DSB` + `ISB`, `DC CVAU` + `IC IVAU`, `INVLPG`, and `INVPCID`.
- **Mechanized Simulators vs. Relaxed System Models (`riscv/sail-riscv` at `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`, `acl2/acl2` `books/projects/x86isa` at `08bec1884997560686932229dbfe458c1bba34bf`, Syeda & Klein JAR 2020, Simner et al. ESOP 2020 / ESOP 2022):** Contrast deterministic emulators (extending `formal-isa-models-x86-64-i386-and-aarch64-coverage` and `reference-model-bisimulation-executable-semantics-and-differential-oracles`) against relaxed cached-walk and instruction-fetch models.
- **Verified Microkernel Implementations (`seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `seL4/l4v` at `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):** Ground `unmapPageTable`, `unmapPage`, `deleteASID`, and `MachineOps` obligations on RISC-V and ARM64.
- **Lean 4 Trust-Boundary Architecture (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`):** Establishes `prelude` + `Init.*` 3-axiom barrier automata and specification-vs-TCB placement.

## Findings

### 1. The Simulator Soundness Trap: Deterministic ISA Emulators vs. Hardware Nondeterminism

`Basis: normative + source + derived`

Coupling kernel verification to an executable ISA simulator introduces a severe soundness gap whenever **refinement (`Behaviors_hw ⊆ Behaviors_spec`)** meets **deterministic cache simplification**:

1. **Normative Hardware Nondeterminism (`riscv-isa-manual` `src/priv/supervisor.adoc:1285–1341`):**
   Clause `#norm:sfence_vma_ordering_semantics` (`lines 1285–1298`) mandates that an implicit MMU read *"may return **any** translation for an address that was valid at any time since the most recent SFENCE.VMA that subsumes that address."* Consecutive accesses to one VA may alternate between old and new translations (`lines 1306–1313`), non-leaf PTEs may remain cached across superpage upgrades (`lines 1324–1329`), and invalid PTEs (`V = 0`) may be cached (`lines 1338–1341`).
   - The algorithm text (`lines 1769–1778`) caches each step-2 PTE read separately. A walk can therefore combine a stale non-leaf entry with a fresh read of a since-repurposed table, producing a translation that was valid at no single instant.
   - The per-entry `DirtyPteEntry` model below is consistent with that per-level reading. The "valid at any time" clause alone would be narrower.
   - See package `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors` §1.2 and its probe `PerLevelStaleTranslation.lean`.

   Likewise, `src/unpriv/zifencei.adoc:66–73` specifies that data stores to instruction memory need not be visible to instruction fetches on a hart until that hart executes `fence.i`.
2. **`riscv/sail-riscv` Leaf-Only TLB and `FENCE.I` No-Op (`ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`):**
   - In `model/sys/vmem_tlb.sail:24–37, 185–222`, `sail-riscv` maintains a hash-indexed array of resolved leaf/superpage `TLB_Entry` records inserted only after `pt_walk` (declared at `model/sys/vmem.sail:122`, defined at `137–261`) via `add_to_TLB`. It models **neither non-leaf partial-walk caches (PWCs) nor multi-entry stale sets**. In `flush_TLB_Entry` (`vmem_tlb.sail:135–164`), `SFENCE.VMA va, asid` (`Some(vaddr), Some(asid)`) evicts matching resolved entries without retaining cached `level > 0` directory pointers that on silicon can synthesize fresh hits for sibling pages `va' ≠ va`.
   - In `model/extensions/Zifencei/zifencei_insts.sail:23–32`, `execute FENCEI` is explicitly `"// fence.i is a nop for the memory model"`, emitting `sail_barrier(Barrier_RISCV_i)` while instruction fetch reads unified RAM directly.
3. **`acl2/x86isa` Global-Wipe `INVLPG` (`08bec1884997560686932229dbfe458c1bba34bf`):**
   - In `books/projects/x86isa/machine/instructions/cache.lisp:43–85`, `x86-invlpg` checks effective-address faults on `addr` and then executes `(x86 (!tlb :tlb x86))` (`lines 75–77`), **clearing the entire `:tlb` fast-alist across all addresses and PCIDs**. Passing a wrong VA `addr'` or flushing only the first page of a multi-page unmap succeeds in `x86-invlpg` while leaving stale leaf TLBs on hardware.

**Derived Rule:** Executable ISA simulators (`sail-riscv`, `x86isa`) are sound oracles for **decoding, bitvector ALU/CSR semantics, and coherent post-barrier walks (`pt_walk` / `ia32e-la-to-pa`)**. These are states in which every cached entry equals memory, which also keeps `sail-riscv`'s TLB-hit A/D write-back inside the specification, but **unsound for barrier sufficiency** unless wrapped in a ghost dirty-set envelope tracking all unsynchronized PTE and code-frame writes.

### 2. Cross-ISA Matrix: Page-Table Walks, PWCs, Shootdowns, and I-Cache Barriers

`Basis: normative + source + derived`

For an $L$-level radix page table (`Sv39`: $L = 3$, levels $2 \to 1 \to 0$; `Sv48` / ARMv8 4 KiB / x86-64 `IA-32e`: $L = 4$, levels $3 \to 2 \to 1 \to 0$), a partial-walk cache (PWC) stores intermediate directory prefixes $(r/\text{asid}, \text{vpn}[L-1 .. m]) \mapsto \text{table\_pa}_{m-1}$ for $m \ge 1$:

| Architectural Dimension | RISC-V `Sv39` / `Sv48` + `Zifencei` | ARMv8-A (`VMSAv8-64`, Stage 1 EL1/EL0) | x86-64 (`IA-32e` 4-Level + `PCID`) |
| :--- | :--- | :--- | :--- |
| **Root CSR/Reg Write Flushes TLB?** | **No** (`satp` write neither orders PTE stores nor flushes caches: `supervisor.adoc:1122–1128` `#norm:satp_op_sfence_vma`). | **No** (`MSR TTBR0_EL1, xN` switches base/ASID without TLB flush; needs `ISB` for context sync). | **Conditional:** `MOV CR3, rax` flushes target PCID non-globals *only* if `CR4.PCIDE = 0` or `rax[63] = 0`; `rax[63] = 1` (`NOFLUSH`) retains TLB/PWC! |
| **Single-VA Leaf Flush Opcode** | `SFENCE.VMA va, asid` (`rs1 ≠ x0, rs2 ≠ x0`; `Svinval`: `SINVAL.VMA`). | `TLBI VALE1IS, xN` (leaf only) vs. `TLBI VAE1IS, xN` (all levels along `va`), + `DSB ISH` + `ISB`. | `INVLPG [m]` (current PCID + global at `m`) or `INVPCID type=0, (pcid, m)`. |
| **Does Single-VA Flush Clear Non-Leaf PWCs?** | **Not guaranteed** (`#norm:sfence_vma_va_asid`, `supervisor.adoc:1252–1260`: `rs1 ≠ x0` is required to invalidate only leaf PTEs. Over-fencing is legal, `supervisor.adoc:1266–1275`, so non-leaf entries *may* survive). | **`VALE1IS`: NO** (spares walk caches). **`VAE1IS`: Only along `va`'s prefix** (spares sibling leaf TLBs `va' ≠ va`). | **YES for current PCID!** (Intel SDM Vol. 3A §4.10.4.1: `INVLPG m` clears **all** PML4E/PDPTE/PDE caches for current PCID, sparing sibling leaf TLBs `m' ≠ m`). |
| **Sequence After Non-Leaf Directory Unmap (`level > 0`)** | Clear PTE $\to$ **`SFENCE.VMA x0, asid`** (`rs1 = x0`, `supervisor.adoc:1376–1379`; `rs2 = x0` if `G = 1` on path). | Clear descriptor $\to$ `DC CVAU` (if non-coherent PTW) $\to$ `DSB ISH` $\to$ **`TLBI ASIDE1IS, asid`** (`vspace.c:1137`) $\to$ `DSB ISH` $\to$ `ISB`. | Clear PDE/PDPTE $\to$ `INVPCID type=1 (pcid)` / reload `CR3` (`bit 63 = 0`), OR `INVLPG` on **every** mapped child leaf `m'`. |
| **Global (`G = 1` / `nG = 0`) Flush** | Requires **`rs2 = x0`** (`SFENCE.VMA va, x0` leaf; `SFENCE.VMA x0, x0` directory: `supervisor.adoc:1245–1250, 1377–1383`). | `TLBI VAALE1IS` (leaf all-ASID) / `TLBI VAAE1IS` (all-level all-ASID) / `TLBI VMALLE1IS`. | `INVLPG m` flushes global leaf at `m`; full global flush toggles `CR4.PGE` or uses `INVPCID type=2`. |
| **SMP Remote Shootdown** | **Software IPI required** (`#norm:sfence_vma_local_only`, `supervisor.adoc:1209–1220`; SBI / kernel IPI + remote `SFENCE.VMA`). | **Hardware Inner-Shareable broadcast** (`TLBI *IS` + `DSB ISH`; remote PEs still require context sync before executing changed mappings). | **Software IPI required** (`INVLPG` / `INVPCID` is core-local unless AMD `INVLPGB` + `TLBSYNC` is used). |
| **D-Cache $\to$ I-Cache (`W → X` Code Load)** | Store visible $\to$ **`FENCE.I`** (`zifencei.adoc:66–75`, local hart only; SMP requires IPI + remote `FENCE.I`). | `DC CVAU, va` $\to$ `DSB ISH` $\to$ `IC IVAU, va` $\to$ `DSB ISH` $\to$ **`ISB`**. | Coherent I-cache snoops D-cache, **except** fetch pipeline requires a **serializing op** (`CPUID`, `IRET`, `SERIALIZE`). |

**`seL4` Verification Comparison (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`):** On ARM64 (`src/arch/arm/64/kernel/vspace.c:1110–1172`), `seL4` distinguishes `unmapPageTable` (`cleanByVA_PoU` + full-ASID `invalidateTLBByASID(asid)`, `line 1137`) from `unmapPage` (`cleanByVA_PoU` + leaf `invalidateTLBByASIDVA(asid, vptr)`, `line 1171`). On RISC-V (`src/arch/riscv/kernel/vspace.c:506–576`), both `unmapPageTable` (`line 545`) and `unmapPage` (`line 575`) conservatively invoke global `sfence()` (`sfence.vma x0, x0`, corresponding to `l4v/spec/machine/RISCV64/MachineOps.thy:203–209` `sfence`/`ifence`). Any kernel narrowing `unmapPage` to `sfence.vma va, asid` must discharge `level = 0 ∧ ¬hasGlobalOnPath`.

### 3. Ghost Dirty-Set Automata and Coupled `W^X` + `fence.i` Refinement

`Basis: documentation + derived`

Syeda & Klein (*Formal Reasoning Under Cached Address Translation*, JAR 64(6):911–945, 2020, DOI `10.1007/s10817-019-09539-7`) partition virtual addresses into consistent vs. inconsistent sets over saturated hardware TLB/walk caches, while Simner et al. (ESOP 2020, DOI `10.1007/978-3-030-44914-8_23`; ESOP 2022, DOI `10.1007/978-3-030-99336-8_6`) model per-core asynchronous `icache` buffers. In `Type 0` Lean 4 (avoiding `Prop`-valued `Set` decidability and `Classical.choice`), kernel barrier correctness at supervisor-to-user transitions reduces to a finite **Ghost Dirty-Set Automaton** (`BarrierGhostState`):

1. **Dirty-Obligation Recording (`tlbDirty` & `remoteDirty`):** Every PTE mutation that narrows permissions, changes `target` PPN, alters `U`/`G`, or clears `V` appends `DirtyPteEntry ⟨asid, vpnPage, level, hasGlobalOnPath⟩` to local `tlbDirty` and remote active-hart `remoteDirty`. Unmapped physical frames remain quarantined against reallocation until their dirty entries are cleared system-wide. *(Monotonic invalid-to-valid leaf upgrades `V: 0 → 1` may omit eager fencing per `supervisor.adoc:1384–1389` because stale `V = 0` hits trap idempotently without violating isolation.)*
2. **Temporal `W^X` + `fence.i` Coupling (`HarvardCodeState`):** Static `W^X` (`∀ pte, pte.valid → ¬(pte.write && pte.exec)`) forbids simultaneous write-and-execute aliases, **but fails across sequential `W → X` lifecycles** (ELF paging, kernel module loading, eBPF JIT). Writing instructions to `ppn` via a kernel `W ∧ ¬X` direct-map alias appends `ppn` to `icacheDirtyPpn` (`storeCodeWord`). Requiring `coherentSystemWide b = true` (`tlbDirty = [] ∧ remoteDirty = [] ∧ icacheDirtyPpn = []`) prior to `sret`/`eret` forces both `SFENCE.VMA` and `FENCE.I` before user instruction fetch can reach `ppn`.

### 4. ISA Seam Separation: Target `Specification` vs. Language-Level Verifier TCB

`Basis: source + derived`

Primary-source inspection of `riscv/sail-riscv` (`ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`) and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) establishes why hardware ISA specifications must sit outside a Rust verifier's language TCB:

1. **Incompatibility of Raw `sail --lean` Output with 3-Axiom Boundaries:**
   - `model/CMakeLists.txt:439–451` passes `--lean-noncomputable` and `--lean-import-file ../handwritten_support/RiscvExtras.lean`.
   - `handwritten_support/RiscvExtras.lean:31–112` declares exactly **75** custom `axiom`s:
     - 8 platform, reservation, random and config hooks, such as `axiom plat_term_write`, `axiom load_reservation`, `axiom get_16_random_bits`;
     - 67 SoftFloat hooks, `axiom riscv_f16Add` … `axiom riscv_f64roundToInt`.
   - The generated project's Lean version is fixed by the Sail compiler, not by sail-riscv (`rems-project/sail` `src/sail_lean_backend/sail_plugin_lean.ml:97, 100`):
     - release `0.20.3` emits `v4.29.0` with lean-sail `v6`;
     - `sail2` from `31342bdb` (2026-11-09) on emits `v4.34.1` with lean-sail `v10`;
     - `lean_emulator/lean-toolchain` separately pins `v4.29.0`.
   - Package `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config` gives the full axiom inventory and Sail-side TLB details (hit-path permission re-check, no flush on `satp` writes, superpage duplication).

   In `joshlf/anneal`, `trusted/audit/TrustedBoundary.lean:469–483, 640–655` enforces a closed syntax allowlist and a strict 3-axiom ceiling (`{propext, Quot.sound, Classical.choice}`), rejecting custom `axiom` declarations fail-closed.
2. **Three-Layer Trust Partition:**
   - **`trusted/lean/` (Language TCB):** Target-independent Rust MIR syntax/semantics (`Trusted.MirAst`, `Trusted.MirSemantics`), audited once against `lean-miri`.
   - **`theory/Anneal/` (`0-TCB` Proof Combinators):** Architecture-parametric coupling and ghost barrier automata (`BarrierGhostState`, `HarvardCodeState`), Pass-1-audited (`prelude` + `Init.*`, `0` custom axioms) and excluded from theorem statements by Statement-Origin Separation.
   - **Crate-Local `Spec/` (Human-Reviewed Target Specification):** Concrete target ISA step relation (`Spec/Isa/Riscv64.lean`, turning platform/FP hooks into explicit `structure` fields rather than Lean `axiom`s), bound to human review (`docs/trust-model.md`) and validated against `Sail` + assembly trap glue (`traps.S`) outside the MIR TCB.

### 5. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization of PWC Asymmetry and `fence.i`

`Basis: execution + derived`

The self-contained Lean 4 (`v4.34.1`) module below mechanizes `DirtyPteEntry`, `BarrierGhostState`, RISC-V `SFENCE.VMA` vs. x86-64 `INVLPG` PWC invalidation (`riscv_leafSfence_misses_nonLeaf_dir`, `riscv_asidSfence_misses_global`, `crossIsa_pwc_invalidation_asymmetry`, `riscv_asidSfence_clears_all_levels_for_nonGlobal_asid`, `riscv_globalSfence_clears_all`), and coupled `HarvardCodeState` `fence.i` coherence (`storeCodeWord_preserves_inv`, `runFenceI_restores_exact_fetch`, `missing_fenceI_fetches_stale_insn`), using strictly `prelude` + `Init.*` with zero `sorry` and zero `Classical.choice`:

```lean
-- Verified on Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace MmuTlbIcacheRefinement

theorem mem_filter_of_mem {α : Type} (p : α → Bool) {x : α} :
    ∀ {xs : List α}, x ∈ xs → p x = true → x ∈ List.filter p xs
  | [], hMem, _ => by cases hMem
  | y :: ys, hMem, hp => by
    cases hMem with
    | head _ => unfold List.filter; rw [hp]; dsimp; exact List.Mem.head _
    | tail _ hTail =>
      unfold List.filter
      cases p y with
      | true  => exact List.Mem.tail y (mem_filter_of_mem p hTail hp)
      | false => exact mem_filter_of_mem p hTail hp

theorem pred_of_mem_filter {α : Type} (p : α → Bool) {x : α} :
    ∀ {xs : List α}, x ∈ List.filter p xs → p x = true
  | [], hMem => by cases hMem
  | y :: ys, hMem => by
    unfold List.filter at hMem
    cases hpy : p y with
    | true =>
      rw [hpy] at hMem
      cases hMem with
      | head _ => exact hpy
      | tail _ hTail => exact pred_of_mem_filter p hTail
    | false => rw [hpy] at hMem; exact pred_of_mem_filter p hMem

structure Pte where
  valid  : Bool
  read   : Bool
  write  : Bool
  exec   : Bool
  user   : Bool
  global : Bool
  target : Nat

def LeafWxSafe (kernelFrames : List Nat) (p : Pte) : Prop :=
  p.valid = true →
    !(p.write && p.exec) = true ∧
    (p.user = true → p.target ∉ kernelFrames)

structure DirtyPteEntry where
  asid            : Nat
  vpnPage         : Nat
  level           : Nat   -- `0` = leaf PTE; `1`, `2` = non-leaf directory PTE (superpage leaves are treated conservatively as non-leaf)
  hasGlobalOnPath : Bool

structure BarrierGhostState where
  tlbDirty       : List DirtyPteEntry
  remoteDirty    : List (Nat × DirtyPteEntry)
  icacheDirtyPpn : List Nat

def BarrierGhostState.coherentForHart (b : BarrierGhostState) : Bool :=
  b.tlbDirty.isEmpty && b.icacheDirtyPpn.isEmpty

def BarrierGhostState.coherentSystemWide (b : BarrierGhostState) : Bool :=
  b.tlbDirty.isEmpty && b.remoteDirty.isEmpty && b.icacheDirtyPpn.isEmpty

def riscvKeptAfterSfence (va? asid? : Option Nat) (e : DirtyPteEntry) : Bool :=
  match va?, asid? with
  | none, none     => false
  | none, some a   => e.hasGlobalOnPath || !Nat.beq e.asid a
  | some v, none   => !(Nat.beq e.level 0 && Nat.beq e.vpnPage v)
  | some v, some a =>
    e.hasGlobalOnPath || !(Nat.beq e.level 0 && Nat.beq e.asid a && Nat.beq e.vpnPage v)

def execRiscvSfenceVma (va? asid? : Option Nat) (b : BarrierGhostState) : BarrierGhostState :=
  { b with tlbDirty := List.filter (riscvKeptAfterSfence va? asid?) b.tlbDirty }

def x86KeptAfterInvlpg (curPcid targetVpn : Nat) (e : DirtyPteEntry) : Bool :=
  match Nat.beq e.level 0 with
  | true =>
    match Nat.beq e.vpnPage targetVpn with
    | true  => !(Nat.beq e.asid curPcid || e.hasGlobalOnPath)
    | false => true
  | false =>
    !Nat.beq e.asid curPcid

theorem riscv_leafSfence_misses_nonLeaf_dir
    (v a asid vpn : Nat) (g : Bool) (b : BarrierGhostState)
    (hDirty : DirtyPteEntry.mk asid vpn 1 g ∈ b.tlbDirty) :
    DirtyPteEntry.mk asid vpn 1 g ∈ (execRiscvSfenceVma (some v) (some a) b).tlbDirty := by
  unfold execRiscvSfenceVma; dsimp
  refine mem_filter_of_mem (riscvKeptAfterSfence (some v) (some a)) hDirty ?_
  unfold riscvKeptAfterSfence; cases g <;> rfl

theorem riscv_asidSfence_misses_global
    (a asid vpn lvl : Nat) (b : BarrierGhostState)
    (hDirty : DirtyPteEntry.mk asid vpn lvl true ∈ b.tlbDirty) :
    DirtyPteEntry.mk asid vpn lvl true ∈ (execRiscvSfenceVma none (some a) b).tlbDirty :=
  mem_filter_of_mem (riscvKeptAfterSfence none (some a)) hDirty rfl

theorem crossIsa_pwc_invalidation_asymmetry (asid targetVpn otherVpn : Nat) :
    let dirEntry := DirtyPteEntry.mk asid otherVpn 1 false
    x86KeptAfterInvlpg asid targetVpn dirEntry = false ∧
    riscvKeptAfterSfence (some targetVpn) (some asid) dirEntry = true := by
  refine ⟨?_, rfl⟩
  unfold x86KeptAfterInvlpg; dsimp; rw [Nat.beq_refl]; rfl

theorem riscv_asidSfence_clears_all_levels_for_nonGlobal_asid
    (a : Nat) (b : BarrierGhostState) (e : DirtyPteEntry)
    (hSurvived : e ∈ (execRiscvSfenceVma none (some a) b).tlbDirty)
    (hNonGlobal : e.hasGlobalOnPath = false) :
    e.asid ≠ a := by
  unfold execRiscvSfenceVma at hSurvived; dsimp at hSurvived
  have hKeep := pred_of_mem_filter (riscvKeptAfterSfence none (some a)) hSurvived
  unfold riscvKeptAfterSfence at hKeep; dsimp at hKeep
  rw [hNonGlobal] at hKeep
  intro hEq; rw [hEq, Nat.beq_refl] at hKeep; cases hKeep

theorem riscv_globalSfence_clears_all (b : BarrierGhostState) :
    (execRiscvSfenceVma none none b).tlbDirty = [] := by
  unfold execRiscvSfenceVma riscvKeptAfterSfence; dsimp
  induction b.tlbDirty with
  | nil => rfl
  | cons _ tl ih => exact ih

structure HarvardCodeState where
  memCode        : Nat → Nat
  icacheCode     : Nat → Nat
  icacheDirtyPpn : List Nat

def IcacheCoherentInv (s : HarvardCodeState) : Prop :=
  ∀ ppn : Nat, ppn ∉ s.icacheDirtyPpn → s.icacheCode ppn = s.memCode ppn

def storeCodeWord (s : HarvardCodeState) (ppn newInsn : Nat) : HarvardCodeState :=
  { memCode := fun p => match Nat.beq p ppn with | true => newInsn | false => s.memCode p
    icacheCode := s.icacheCode
    icacheDirtyPpn := ppn :: s.icacheDirtyPpn }

def runFenceI (s : HarvardCodeState) : HarvardCodeState :=
  { memCode := s.memCode, icacheCode := s.memCode, icacheDirtyPpn := [] }

theorem storeCodeWord_preserves_inv (s : HarvardCodeState) (ppn newInsn : Nat)
    (hInv : IcacheCoherentInv s) :
    IcacheCoherentInv (storeCodeWord s ppn newInsn) := by
  intro p hNotDirty
  unfold storeCodeWord at hNotDirty ⊢; dsimp at hNotDirty ⊢
  cases hEq : Nat.beq p ppn with
  | false =>
    dsimp
    exact hInv p (fun hIn => hNotDirty (List.Mem.tail ppn hIn))
  | true =>
    have hSame : p = ppn := Nat.eq_of_beq_eq_true hEq
    subst hSame
    exact False.elim (hNotDirty (List.Mem.head s.icacheDirtyPpn))

theorem runFenceI_restores_exact_fetch (s : HarvardCodeState) (ppn : Nat) :
    (runFenceI s).icacheDirtyPpn = [] ∧
    (runFenceI s).icacheCode ppn = (runFenceI s).memCode ppn :=
  ⟨rfl, rfl⟩

theorem missing_fenceI_fetches_stale_insn :
    let s0 : HarvardCodeState := { memCode := fun _ => 0, icacheCode := fun _ => 0, icacheDirtyPpn := [] }
    let s1 := storeCodeWord s0 42 0x00008067
    s1.memCode 42 = 0x00008067 ∧ s1.icacheCode 42 = 0 ∧ s1.icacheCode 42 ≠ s1.memCode 42 := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  cases h

end MmuTlbIcacheRefinement
```

## Boundaries

- **`known not to apply` — Verification against `sail-riscv` `vmem_tlb.sail` or `acl2/x86isa` `x86-invlpg` as proof of hardware barrier sufficiency:** Passing `flush_TLB_Entry` in `riscv/sail-riscv` (`model/sys/vmem_tlb.sail`) or `x86-invlpg` in `acl2/x86isa` (`machine/instructions/cache.lisp`) is **known not to apply** as proof of hardware PWC or I-cache coherence, because `sail-riscv` omits non-leaf PWCs and treats `FENCE.I` as a memory no-op while `x86isa` wipes `:tlb` globally.
- **`known not to apply` — Static `W^X` PTE invariants without temporal `fence.i` / `IC IVAU + ISB` tracking:** Enforcing `¬(pte.write && pte.exec)` at each state is **known not to apply** to prevent stale instruction execution across sequential `W → X` code-loading transitions (`missing_fenceI_fetches_stale_insn`).
- **`known not to apply` — Porting x86-64 `INVLPG` directory-flush rules to RISC-V `SFENCE.VMA va, asid`:** Single-VA `INVLPG` clears current-PCID directory caches on x86-64, which is **known not to apply** on RISC-V (`crossIsa_pwc_invalidation_asymmetry`) or ARMv8 `TLBI VALE1IS`.
- **`unsupported` — Direct import of `sail --lean` `RiscvExtras.lean` into `joshlf/anneal` `TrustedBoundary`:** Because `riscv/sail-riscv` `handwritten_support/RiscvExtras.lean:31–112` declares 75 custom `axiom` items and `CMakeLists.txt:440` emits `noncomputable` code (on `v4.29.0` with the Sail 0.20.3 release, `v4.34.1` with current `sail2`), raw `sail --lean` output is **unsupported** inside `joshlf/anneal`'s 3-axiom `TrustedBoundary` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) without parameterizing external hooks as `structure` fields.
- **`not examined` — Two-stage hypervisor MMUs (`HFENCE.GVMA`/`HFENCE.VVMA`, `TLBI IPAS2E1IS`, `INVEPT`) and PCIe IOMMU `IOTLB` shootdowns:** Nested guest-physical translation caches and IOMMU `ATS`/`PRI` invalidations were **not examined**; nested virtualization requires a `(vmid, asid, gva, gpa)` dirty lattice where Stage-2 invalidation pairs with Stage-1 invalidation.
- **`unknown` — Hardware `Svadu` autonomous A/D-bit updates racing lockless software PTE updates (narrowed 2026-11-20):**
  - The required semantics are normative. The update must be atomic with respect to other accesses to the PTE and is a compare-and-retry: "Compare *pte* to the value of the PTE … If the comparison fails, return to step 2". The address-translation cache "cannot be used in step 9". Page tables need the RsrvEventual PMA (`riscv-isa-manual@c05f1725` `src/priv/supervisor.adoc:1622–1651, 1739–1749, 1780–1781`).
  - What remains **unknown** is vendor-microarchitecture conformance, unless `Svade` fault-on-A/D mode is enforced.
  - `sail-riscv`'s TLB-hit path does not perform the compare. See Summary item 2 and package `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors` §1.7.

## Evidence

| Subject / Artifact | Exact Coordinates | Role & Key Fact Verified |
| :--- | :--- | :--- |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/priv/supervisor.adoc:1122–1135, 1185–1396` | `normative`: `#norm:satp_op_sfence_vma`, `#norm:sfence_vma_local_only`, 4-case `rs1`/`rs2` matrix (`#norm:sfence_vma_va_asid` leaf-only rule), `#norm:sfence_vma_ordering_semantics`, and `lines 1376–1383` (`rs1 = x0` for non-leaf PTEs; `rs2 = x0` if `G = 1` on path). |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/unpriv/zifencei.adoc:30–75` | `normative`: `FENCE.I` synchronizes prior visible stores with instruction fetches on the local hart only (`lines 66–73`). |
| `riscv/sail-riscv` | `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`, `model/sys/vmem_tlb.sail:24–37, 135–222`; `vmem.sail:95–119, 122–261, 370–413`; `zifencei_insts.sail:23–32`; `model/CMakeLists.txt:423–493`; `handwritten_support/RiscvExtras.lean:31–112`; `lean_emulator/lean-toolchain` | `source`: Leaf-only `TLB_Entry` array omitting PWCs; TLB-hit A/D write-back without compare; `FENCEI` memory no-op; `--lean-noncomputable`; 75 custom `axiom` declarations in `RiscvExtras.lean`; `lean_emulator` pinned to `v4.29.0`. |
| `seL4/seL4` & `seL4/l4v` | `seL4` `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` (`src/arch/riscv/kernel/vspace.c:506–576`, `src/arch/arm/64/kernel/vspace.c:1110–1185`); `l4v` `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` (`spec/machine/RISCV64/MachineOps.thy:203–210`) | `source`: ARM64 `unmapPageTable` (`cleanByVA_PoU` + `invalidateTLBByASID`) vs `unmapPage` (`invalidateTLBByASIDVA`); RISC-V global `sfence()` and `MachineOps.thy` `sfence`/`ifence`. |
| `acl2/acl2` (`x86isa`) | `08bec1884997560686932229dbfe458c1bba34bf`, `books/projects/x86isa/machine/linear-memory.lisp:524–595`; `paging.lisp:58–128`; `instructions/cache.lisp:43–85`; DOI `10.1109/FMCAD.2014.6987600` | `source + documentation`: System-view `ia32e-la-to-pa`, `:tlb` state field, and `x86-invlpg` wiping `(!tlb :tlb x86)` globally. |
| Intel SDM & Arm ARM | Intel SDM Vol. 3A §4.10.4.1–4.10.4.2; Arm ARM DDI 0487 (`TLBI VAE1IS` vs `VALE1IS`, `DC CVAU`, `IC IVAU`, `ISB`) | `normative`: x86-64 `INVLPG` clearing current-PCID PML4E/PDPTE/PDE caches vs ARMv8 `VALE1IS` sparing walk caches. |
| Syeda & Klein & Simner et al. | JAR 64(6):911–945 (DOI `10.1007/s10817-019-09539-7`); ESOP 2020 (DOI `10.1007/978-3-030-44914-8_23`); ESOP 2022 (DOI `10.1007/978-3-030-99336-8_6`) | `documentation`: Consistent/inconsistent VA set invariants and operational per-core `icache` / VMSA barrier semantics. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/audit/TrustedBoundary.lean:469–483, 640–655`; `docs/trust-model.md` | `source`: Statement-Origin Separation, 3-axiom ceiling, and separation of `trusted/lean/` MIR TCB from target specifications. |
| `rems-project/sail` (observed 2026-11-20) | tag `0.20.3` = `3df54034910b31a1e00d948ee965b2e9603d68e0`; `31342bdbb5a3996d4c1f5231d06e7140df5d3288`; `sail2` HEAD `97aa617dcd4d01575f773cb58ea1e8686858c8c2`; `src/sail_lean_backend/sail_plugin_lean.ml:97, 100` | `source`: `let lean_version = "lean4:v4.29.0"` / `lib_default_rev = "v6"` at `0.20.3`; `"lean4:v4.34.1"` / `"v10"` from `31342bdb` on. sail-riscv requires Sail `0.20.3` (`cmake/sail_required_version.txt`), but its Lean CI builds Sail `latest` from the default `sail2` branch (`.github/workflows/compile-lean.yml:40, 86`; `.github/actions/sail-setup/action.yml:184–190`). |
| Corrections note (2026-11-20) | `riscv/riscv-isa-manual@c05f1725` `src/priv/supervisor.adoc:1266–1275, 1622–1651, 1739–1781`; `riscv/sail-riscv@ec5200bd` as listed above | `normative` + `source`: basis for the over-fencing qualification, the per-level caching note, the Sail TLB-hit A/D qualification, the narrowed Svadu boundary, the 75-axiom count, toolchain provenance and line ranges. The original Lean probe was re-run unchanged on 2026-11-20 with `Lean 4.34.1 (5045d005…)` and the axiom results recorded below were reproduced. |
| `leanprover/lean4` (`v4.34.1`) Probe | Commit `5045d0056413266e57c625dcd7c365b10e377c52` (`x86_64-unknown-linux-gnu`), `2026-11-20` | `execution`: `lean -DElab.async=false -Ddebug.skipKernelTC=false -M2048` checked all 7 theorems (`exit 0`, `< 0.6s`); 5 theorems use **zero axioms** and 2 (`crossIsa_pwc_invalidation_asymmetry`, `riscv_asidSfence_clears_all_levels_for_nonGlobal_asid`) use only `[propext]`. |

## Revalidation

1. **Re-run the Standalone Lean 4 Kernel Probe (`< 1s`):** Save the Lean 4 block from **Findings §5** to `/tmp/reval_mmu.lean`, append `#print axioms` for `MmuTlbIcacheRefinement.riscv_leafSfence_misses_nonLeaf_dir`, `MmuTlbIcacheRefinement.riscv_asidSfence_misses_global`, `MmuTlbIcacheRefinement.crossIsa_pwc_invalidation_asymmetry`, `MmuTlbIcacheRefinement.riscv_asidSfence_clears_all_levels_for_nonGlobal_asid`, `MmuTlbIcacheRefinement.storeCodeWord_preserves_inv`, and `MmuTlbIcacheRefinement.missing_fenceI_fetches_stale_insn`, and execute:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -M2048 /tmp/reval_mmu.lean
   ```
   Verify exit code `0`, zero `sorryAx`, and axiom closure inside `{propext}`.
2. **Check `sail-riscv` TLB/I-Cache Fidelity and Lean Backend Axioms (`riscv/sail-riscv`):** Diff `model/sys/vmem_tlb.sail`, `model/extensions/Zifencei/zifencei_insts.sail`, and `handwritten_support/RiscvExtras.lean` to check whether upstream adds partial-walk directory caches, split I-caches, or `axiom`-free Lean typeclass parameters.
3. **Check `SFENCE.VMA` / `Svinval` Clauses (`riscv/riscv-isa-manual`):** Diff `src/priv/supervisor.adoc` around `#norm:sfence_vma_va_asid` and `#norm:sfence_vma_ordering_semantics` across newer RISC-V Privileged Architecture revisions.
