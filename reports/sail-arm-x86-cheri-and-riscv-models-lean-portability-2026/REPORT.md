# Sail Arm, x86-64, CHERI Capability, and RISC-V ISA Models: Architecture, Lean 4 Codegen Obstacles, and Bridge Design for Anneal

## Summary

This report analyzes the architecture, state-monad lowering, memory interfaces, and Lean 4.34.1 portability of fourteen primary Sail and proof-assistant ISA repositories spanning four architectural families—**Arm (`sail-tiny-arm`, `sail-tiny-arm-lean`, `sail-small-arm`, `sail-arm`)**, **x86-64 (`sail-x86-from-acl2`, `sail-tiny-x86`)**, **CHERI Capabilities (`sail-morello`, `sail-cheri-riscv`, `cheriot-sail`, `rocq-cheriot-sail`, `coq-cheri-capabilities`)**, and **RISC-V Lean 4 Extractions (`opencompl/sail-riscv-lean`, `Verified-zkEVM/riscv-zkvm`, `axiom-crypto/sail-riscv-lean`)**—to establish concrete ISA and capability-memory integration strategies for Anneal (`joshlf/anneal-private`).

1. **Arm Sail Models (`sail-tiny-arm`, `sail-tiny-arm-lean`, `sail-small-arm`, `sail-arm`):**
   - `rems-project/sail-tiny-arm` (`98d904912620ddd74e76714b7ef8457192cb4e3a`) provides a 17-instruction user-mode AArch64 model (`instrs-user.sail`) and a `-D SYSTEM_TINY_ARM` mode (`instrs-sys.sail`, `translation.sail`) adding 37 EL1/EL2/EL3 system registers and a 4-level VMSA page-table walker (`pgt_walk`). However, `Makefile:27-29` runs `sail --lean` **without** `-D SYSTEM_TINY_ARM`, so `rems-project/sail-tiny-arm-lean` (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`, `SailTinyArmUser`) is strictly user-mode (`translate_address va := some va`) and replaces `e8fbacf0af7ff196cc84b95baa7c2dbb35c4dd3a`'s pure `decode : BitVec 32 → Option ast` (10 constructors) with a monadic `decode : BitVec 32 → SailM ast` (17 constructors) and `SailME.run` early-return blocks.
   - `rems-project/sail-small-arm` (`d6b7c9cf86adaa479492b3881884b190a48f385b`, 6,002 LOC) embeds existentially quantified dependent bitvector widths inside `union ast` constructors (`AddSubImmediate : {'R, RegisterSize('R). (..., bits('R))}` in `armV8.sail:54-102`), which Sail's Lean 4 backend does not support without monomorphization.
   - `rems-project/sail-arm` (`7d0581642d0e3aaca367bbc5650aca7c53057543`, 464,212 LOC in `arm-v9.4-a`) has a `gen_lean` target (`arm-v9.4-a/Makefile:85-97`), but its Lean extraction is **unsound as a zero-axiom TCB**: `arm-v9.4-a/lean/ArmExtras.lean:18-22` defines `macro_rules | `(tactic| decreasing_trivial) => `(tactic| first | grind | decide | sorry)`, while `arm-v9.4-a/src/termination_measures.sail:43-116` gates all 24 loop termination measures (`AArch64_S1Walk`, `AArch64_S2Walk`, `FPRoundBase__1`, `FloorPow2`) under `$iftarget coq`, silently discharging termination obligations with `sorryAx`. In addition, until commit `7d0581642d0e3aaca367bbc5650aca7c53057543` (`2026-10-11`), `arm-v9.4-a/src/prelude.sail:108-112` mapped `emod_nat` (`MOD`) to `"Nat.div"` in Lean instead of `"Nat.mod"`, corrupting `ROR` (`src/builtins.sail:101, 112`).

2. **x86-64 Sail Models (`sail-x86-from-acl2`, `sail-tiny-x86`):**
   - `rems-project/sail-x86-from-acl2` (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`, 32,896 LOC across 62 `.sail` files) translates the ACL2 `x86isa` model into a fused fetch-decode-execute pipeline (`x86_fetch_decode_execute` in `model/step.sail:2414-2493`) with **no `ast` union type**—fetching prefixes via recursive `get_prefixes` (`step.sail:86-145`) and fetching ModR/M, SIB, displacement, and immediate bytes on-the-fly via `rme08`..`rme64` inside each opcode handler. Direct `sail --lean` extraction is blocked by unbounded integer recursion without termination measures (`logcount_int`, `logand_int`, `get_prefixes`), SMT-dependent runtime range casts (`check_range` in `model/prelude.sail:133-173`), and legacy `__read_mem`/`__write_mem` primitives.
   - `rems-project/sail-tiny-x86` (`229bd8448937042baa51b0a2d14bc437929b0dce`, 1,998 model LOC) defines a 19-instruction 64-bit user-space model using `CONCURRENCY_INTERFACE_V2`, but exhibits three critical architectural hazards: (a) `decode(rip)` (`decode.sail:180-210, 271-334`) is impure and reads GPRs (`read_GPR`) during decoding to bake resolved 64-bit effective addresses `rm_MEM(bits(64))` into the `ast`; (b) **RIP-relative addressing bug (`decode.sail:300-308` vs `tiny-x86.sail:9-20`)**: when `mod == 0b00 & three_bit_rm_reg == 5`, `decode_rm_operand_inner` computes `add_bits(rip, sail_sign_extend(displacement, 64))` using the **un-incremented `rip` at instruction start** instead of `new_rip = rip + instr_len` (off by `instr_len` bytes on every RIP-relative instruction); and (c) `registers.sail:34-51` indexes a vector of register references `(*GPRs[i])`, which `sail --lean` does not support.

3. **CHERI Capability Sail Models (`sail-morello`, `sail-cheri-riscv`, `cheriot-sail`, `coq-cheri-capabilities`):**
   - Across 129-bit Arm Morello (`CTSRD-CHERI/sail-morello` `2305f656ff84619caf50107f49dae7be52aec72b`), 128+1-bit 64-bit CHERI-RISC-V (`CTSRD-CHERI/sail-cheri-riscv` `cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b`), and 64+1-bit 32-bit CHERIoT (`CHERIoT-Platform/cheriot-sail` `518813ec3e595f79930d9129eaded2521831cbe2`), capability safety rests on two architectural invariants: (a) **monotonic capability derivation** (`CAndPerm`, `CSetBounds`, `CIncOffset`, `CSetAddr` clear the validity `tag` whenever the source capability is sealed or the new bounds/address exceed representable parent bounds, mechanized in `cheriot-sail/properties/props.sail:154-167` and `rems-project/coq-cheri-capabilities` `b39cd73409d8c2a058ba8065f81dc72d3c84fb11`), and (b) **tag-stripping raw byte stores** (`__WriteMem` in `sail-morello/src/mem.sail:87-98` and `__WriteRAM_Meta(..., false)` in `sail-cheri-riscv/src/cheri_mem_metadata.sail:77-93`), which unconditionally clear the out-of-band capability tag of the enclosing capability granule (`16` bytes on Morello/RV64, `8` bytes on CHERIoT), preventing capability forgery via byte overwrites. (`christiankissig/rocq-cheriot-sail` is an empty upstream GitHub repository with 0 commits.)

4. **Specialized Lean 4 Sail RISC-V Extractions (`opencompl/sail-riscv-lean`, `Verified-zkEVM/riscv-zkvm`, `axiom-crypto/sail-riscv-lean`):**
   - While `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) extracts the full 353-instruction RV64D specification (161 `.lean` files, 173,776 lines, 0 `sorry`, 75 platform/SoftFloat axioms), `Verified-zkEVM/riscv-zkvm` (`6810fc14d9c40373101321cefaec59df8d82e3e7`, Lean `v4.33.1`) and `axiom-crypto/sail-riscv-lean` (`82afed87c9d6827d3691acbe66d5395fa37dc41d`, Lean `v4.34.0`) demonstrate production-grade patterns for Lean 4 ISA verification:
     - **Scoped module extraction (`sail-import/PROVENANCE.toml`):** Passing only `["main", "I_insts", "M_insts", "Zicsr_insts", "K_core", "Zkr", "Zicboz", "Zicbom_insts"]` to `sail --lean` shrinks the generated model from 353 instructions (173k LOC) to 33 instructions (60k LOC), and importing `RiscvZkvm.Sail.InstsEnd` instead of `RiscvZkvm.Sail` (`StateRel.lean:6-29`) prunes the ~14 GiB RSS `RvfiDii` module from the proof closure.
     - **Two-tier simulation (`RiscvZkvm.Rv64.SailEquiv`):** Rather than running separation-logic tactics directly over Sail's `PreSailM` monad, `riscv-zkvm` defines a pure functional `MachineState` (`RiscvZkvm.Rv64`) and proves 51 per-instruction equivalence theorems plus multi-step simulation (`sailStepN_run_sim` in `StepRun.lean:505-537`) using `StateRelPC`, range-level byte presence (`MemPresent lo hi`), platform-register framing (`PlatformFrame`), anti-vacuity satisfiability witnesses (`jalr_sideCond_satisfiable` for issue `#10688`), and a kernel-level axiom gate (`scripts/AxiomSweep.lean`).
     - **Zero-axiom computable extraction (`axiom-crypto/sail-riscv-lean`):** Replaces `RiscvExtras.lean`'s `axiom` declarations with total executable stubs in `RiscvExtrasExecutable.lean` and omits `--lean-noncomputable`, yielding a 34-instruction RV32IM + `Ext_Xopenvm` package on Lean `v4.34.0` with **zero `noncomputable` definitions, zero `sorry`, and zero `axiom` declarations**.

5. **Mechanized Lean 4.34.1 Probe (`support/sail_tiny_arm_and_capability_bridge_probe.lean`):**
   - Accompanying this report is a standalone 973-line Lean 4.34.1 file verified under `lean -j1 -M768` with zero `sorryAx` and zero custom axioms, mechanizing: (a) the `SailTinyArmUser` monadic `SailM`/`SailME` decode-execute architecture bridged into Anneal's `BridgeTransition`, (b) the `sail-tiny-x86` RIP-relative decode offset discrepancy (`tinyX86_rip_relative_discrepancy` and concrete counterexample `tinyX86_mov_rip_rel_counterexample`), and (c) a CHERI capability register/memory machine (`CapWord`, `CapMem`) proving capability monotonicity (`cSetBounds_monotone`, `cAndPerm_monotone`, `cIncOffset_monotone`), raw-byte tag stripping (`writeRawByte_strips_enclosing_cap_tag`, `readCapGranule_after_writeRawByte_untagged`), and refinement of Anneal's spatial/provenance memory checks (`cheri_load_check_implies_anneal_canRead`, `cheri_store_check_implies_anneal_canWrite`, `cheriByteStoreBridge`, `cheriCapStoreBridge`).

---

## Applicability

This report applies directly to Anneal (`joshlf/anneal-private` at `42f4571d761b46c7142815f38b69c3781b3555e3`):

- **`Trusted/StepResult.lean` & `Trusted/Refinement.lean`:** Defines how monadic Sail models (`SailM α = SequentialState → Except Error (α × SequentialState)` and early-return `SailME e α`) embed into Anneal's `StepResult` (`.next`, `.done`, `.trap`, `.stuck`), `SmallStepMachine`, `BehaviorOf`, and `BridgeTransition` without introducing `.stuck` (undefined behavior) states.
- **`Trusted/Memory.lean`:** Shows how CHERI capability bounds (`[base, top)`), permissions (`canLoad`, `canStore`, `canLoadCap`, `canStoreCap`), and out-of-band validity tags (`capTags`) refine Anneal's abstract `Pointer` / `AllocInfo` (`base`, `len`, `writable`, `live`) spatial and provenance checks in hardware (`CapRefinesAnneal`).
- **AArch64, x86-64, and RISC-V Backend Selection for Anneal:** Provides an evidence-backed decision matrix showing why Anneal should adopt `Verified-zkEVM/riscv-zkvm`'s **two-tier architecture** (a clean, pure, computable ISA state machine for WP/separation-logic tactics paired with per-instruction simulation theorems against a scoped Sail extraction) and `axiom-crypto/sail-riscv-lean`'s **zero-axiom executable support layer**, while avoiding `sail-arm`'s `sorry`-backed `ArmExtras.lean` and `sail-tiny-x86`'s impure decode pipeline.

---

## Findings

### 1. Area 1 — Arm Sail Models (`sail-tiny-arm`, `sail-tiny-arm-lean`, `sail-small-arm`, `sail-arm`)

#### 1.1 Comparative Overview of the Arm Sail Family

| Repository | Commit SHA | Scale | Target ISA Scope | Memory / Concurrency Interface | Lean 4 Extraction Status |
|---|---|---|---|---|---|
| `rems-project/sail-tiny-arm` | `98d904912620ddd74e76714b7ef8457192cb4e3a` | 1,683 LOC (`.sail`) | 17 user-mode + 4 system-mode AArch64 instruction families + 4-level EL1&0 VMSA walker | `CONCURRENCY_INTERFACE_V2` (`sail_mem_read`, `sail_mem_write`, `sail_barrier`, `sail_tlbi`, `sail_take_exception`) | User-only via `make lean` (`SailTinyArmUser`); system mode (`-D SYSTEM_TINY_ARM`) extracted only in `rocq/` |
| `rems-project/sail-tiny-arm-lean` | `4a474cfc415e46a0f6251c8c7d58a85e6411eb7b` (prev: `e8fbacf0af7ff196cc84b95baa7c2dbb35c4dd3a`) | 2,175 LOC across 9 `.lean` files | 17 user-mode AArch64 instruction families (`SailTinyArmUser`) | `ConcurrencyInterfaceV2` (`lean-sail@v7`, Lean `v4.29.0`) | Compiles cleanly with zero `sorry` and zero `axiom`; user-mode only (`translate_address va = some va`) |
| `rems-project/sail-small-arm` | `d6b7c9cf86adaa479492b3881884b190a48f385b` | 6,002 LOC across 5 `.sail` files | 49 handwritten AArch64 user-mode instruction constructors | Legacy `rMem_normal` / `wMem` / `FlushWriteBuffer` | No Lean target; blocked by existentially quantified bitvector widths inside `union ast` constructors |
| `rems-project/sail-arm` | `7d0581642d0e3aaca367bbc5650aca7c53057543` | `arm-v8.5-a`: 124,375 LOC; `arm-v9.3-a`: 384,419 LOC; `arm-v9.4-a`: 464,212 LOC | Full ASL-derived Armv8.5-A / Armv9.3-A / Armv9.4-A architecture | `arm-v9.4-a`: `sail_mem_read` / `sail_mem_write` | `arm-v9.4-a/Makefile` has `gen_lean`, but uses `-lean-noncomputable` and silently discharges termination via `sorry` in `ArmExtras.lean:22` |

#### 1.2 `sail-tiny-arm` vs. `sail-tiny-arm-lean`: User vs. System Mode and `e8fbacf` → `4a474cf` Evolution

In `rems-project/sail-tiny-arm` (`98d904912620ddd74e76714b7ef8457192cb4e3a`), conditional compilation via `#ifdef SYSTEM_TINY_ARM` splits the model into two tiers:

1. **User-Mode Tier (`instrs-user.sail`, 759 LOC):**
   - Defines 34 registers (`registers.sail:6-41, 128-130`): `R0`..`R30 : bits(64)` (indexed via `let GPRs : vector(31, dec, register(bits(64)))`), `_PC : bits(64)`, `NZCV : bits(4)`, and `SP_EL0 : bits(64)`. Reading/writing register index `31` via `rX`/`wX` (`registers.sail:107-115`) returns `0x0000000000000000` (`XZR`) or performs a no-op write, while `rSP`/`wSP` (`registers.sail:117-125`) accesses `SP_EL0` when `n == 31`.
   - Covers 17 `ast` instruction families:
     - Memory & Atomics: `Load(reg_index, reg_index, reg_index)` (`LDR Xt, [Xn, Xm]`), `Store(reg_index, reg_index, reg_index)` (`STR Xt, [Xn, Xm]`), and `AtomicRMW(AtomicOp, bool, bool, reg_index, reg_index, reg_index)` covering 64-bit `LDADD`, `LDCLR`, `LDEOR`, `LDSET`, and `SWP` with acquire/release bits (`instrs-user.sail:82-222`). Notably, `CAS`/`CASA`/`CASL`/`CASAL` (`instrs-user.sail:198-200`) and `CSEL` (`instrs-user.sail:327-329`) match their bit encodings in `decode` only to call `fail("CompareAndSwap is not implemented")` and `fail("ConditionalSelect is not implemented")`.
     - ALU & Bitfield: `BitwiseLogic` (`AND`/`ORR`/`EOR` 64-bit shifted register, where `shift != 0b00` or `imm6 != 0` calls `fail`), `Movz` (`MOVZ` 64-bit), `BitfieldMove` (`UBFM` 64-bit only), `AddSub` (`ADD`/`SUB` 64-bit register with zero shift), `PCRelativeAddress` (`ADR`/`ADRP`), and `Nop`.
     - Control Flow & Barriers: `CompareAndBranch` (`CBZ`/`CBNZ`), `TestAndBranch` (`TBZ`/`TBNZ`), `Branch` (`B`/`BL`), `ConditionalBranch` (`B.cond` for `EQ` `0b0000` and `NE` `0b0001` only), `BranchRegister` (`BR`/`BLR`/`RET`), `DataMemoryBarrier` (`DMB`), `DataSynchronizationBarrier` (`DSB`), and `InstructionSynchronizationBarrier` (`ISB`).
   - In user mode (`#else` branch of `translation.sail:331-336`), `translate_address(va, accdesc)` is the trivial identity `Some(va)`.

2. **System-Mode Tier (`-D SYSTEM_TINY_ARM` in `registers.sail`, `translation.sail`, `instrs-sys.sail`):**
   - Adds 37 system registers (`registers.sail:131-204`): `CurrentEL`, `SPSel`, `DAIF`, `SP_EL1`..`SP_EL3`, `ELR_EL1`..`ELR_EL3`, `ESR_EL1`..`ESR_EL3`, `FAR_EL1`..`FAR_EL3`, `SPSR_EL1`..`SPSR_EL3`, `SCTLR_EL1`..`SCTLR_EL3`, `TCR_EL1`..`TCR_EL3`, `TTBR0_EL1`..`TTBR0_EL3`, `TTBR1_EL1`, `TTBR1_EL2`, `VBAR_EL1`..`VBAR_EL3`, `HCR_EL2`, `MDCR_EL2`, `MDSCR_EL1`, `VTTBR_EL2`, `VTCR_EL2`, `TPIDR_EL0`, and `TPIDR_EL1`.
   - Implements a 4-level EL1&0 Stage-1 VMSA page-table walker `pgt_walk` (`translation.sail:141-201`, with `termination_measure pgt_walk level = 4 - level`) reading 64-bit page descriptors via `rMem_ptw`, checking valid bits, block vs. table descriptors, access permissions (`AP`), and `UXN`/`PXN`, bracketed by `sail_translation_start` and `sail_translation_end`. On translation or permission fault, `handle_fault` (`translation.sail:257-292`) populates `ESR_EL1` (`ISS` + `EC`), `FAR_EL1`, and `ELR_EL1`, and `take_exception` (`translation.sail:209-255`) dispatches to `VBAR_EL1 + offset` via `sail_take_exception`.
   - Adds 4 system `ast` constructors in `instrs-sys.sail`: `TLBInvalidation(TLBI_Op, reg_index)`, `SupervisorCall`, `ExceptionReturn` (`ERET`), and `SystemRegisterMove(bool, sys_reg_id, reg_index)` (`MRS`/`MSR`).

3. **Why `sail-tiny-arm-lean` omits System Mode and how `e8fbacf` evolved to `4a474cf`:**
   - Whereas `rocq/dune` in `sail-tiny-arm` invokes `sail --coq` twice (producing `User.v` and `System.v`), `Makefile:27-29` (`lean:` target) runs `sail $(SAIL_LEAN_FLAGS) --lean-output-dir lean-output -o SailTinyArmUser $(SAIL_FILES)` **without** `-D SYSTEM_TINY_ARM`. Consequently, `SailTinyArmUser/Defs.lean:473-498` defines `sys_reg_id := Unit`, `tlbi := Unit`, `exn := Unit`, `trans_start := Unit`, and `trans_end := Unit`, and `SailTinyArmUser/Translation.lean:55-56` emits `def translate_address (va : (BitVec 64)) (_ : AccessDescriptor) : (Option (BitVec 64)) := (some va)`.
   - Comparing the two commits of `rems-project/sail-tiny-arm-lean`:
     - At `e8fbacf0af7ff196cc84b95baa7c2dbb35c4dd3a` (`2026-01-22`, `leanprover/lean4:nightly-2026-01-22`, `lean-sail@v5`, module `Out`), `Out/Defs.lean` had only 10 `ast` constructors (`Load`, `Store`, `BitwiseLogic`, `Movz`, `AddSub`, `DataMemoryBarrier`, `DataSynchronizationBarrier`, `InstructionSynchronizationBarrier`, `Nop`, `CompareAndBranch`) and `Out/TinyArm.lean` emitted a **pure** decoder `def decode (arg_ : (BitVec 32)) : (Option ast)`.
     - At `4a474cfc415e46a0f6251c8c7d58a85e6411eb7b` (`2026-03-31`, `leanprover/lean4:v4.29.0`, `lean-sail@v7`, module `SailTinyArmUser`), `SailTinyArmUser/Defs.lean` expands to all 17 user-mode `ast` constructors, and because `sail-tiny-arm` replaced `Option(ast)` in `decode` with `fail(...)` and `assert(...)`, `SailTinyArmUser/TinyArm.lean:56-538` lowers `decode` to a **monadic** computation `def decode (op : (BitVec 32)) : SailM ast`. Furthermore, functions with early `return()` in Sail (`execute_Load`, `execute_Store`, `execute_AtomicRMW`, `fetch_and_execute`) lower to `SailME.run do ... SailME.throw (() : Unit)`.

#### 1.3 `sail-small-arm` and `sail-arm`: Dependent AST Existentials and `ArmExtras.lean` Termination Unsoundness

1. **`rems-project/sail-small-arm` (`d6b7c9cf86adaa479492b3881884b190a48f385b`):**
   - `armV8.sail:54-102` defines its 49-constructor `union ast` using **existentially quantified type variables inside AST constructors**, e.g.:
     ```sail
     union ast = {
       AddSubImmediate : {'R, RegisterSize('R).
         (reg_index, reg_index, int('R), boolean, boolean, bits('R))},
       LoadImmediate : {'R 'D, RegisterSize('R) & DataSize('D).
         (reg_index, reg_index, AccType, boolean, boolean, boolean, int('R), int('D), bits(64))},
       ...
     }
     ```
   - Unlike `sail-tiny-arm` (which fixes 64-bit register widths in `ast`) or `riscv/sail-riscv` (which uses fixed-width bitvectors or enum width tags `word_width`), `sail-small-arm` packs dependent bitvector widths `'R ∈ {32, 64}` and `'D ∈ {8, 16, 32, 64}` into the `ast` inductive itself. Sail's Lean 4 backend (`sail_plugin_lean.ml`) does not support existentially quantified bitvector widths inside inductive constructors without monomorphizing them first.

2. **`rems-project/sail-arm` (`7d0581642d0e3aaca367bbc5650aca7c53057543`):**
   - Contains three ASL-derived snapshots: `arm-v8.5-a` (124,375 LOC), `arm-v9.3-a` (384,419 LOC), and `arm-v9.4-a` (464,212 LOC). Only `arm-v9.4-a/Makefile:85-97` includes a Lean 4 target (`gen_lean`), running:
     ```bash
     sail $(SAIL_FLAGS) -lean -lean-output-dir $(LEAN_BUILD_DIR) \
       -lean-noncomputable -lean-import-file ../lean/ArmExtras.lean $(SAIL_SRCS)
     ```
   - Inspection of `arm-v9.4-a/lean/ArmExtras.lean`, `arm-v9.4-a/src/termination_measures.sail`, and `arm-v9.4-a/src/prelude.sail` reveals three critical verification hazards:
     1. **Unsound `sorry` fallback in `decreasing_trivial` (`arm-v9.4-a/lean/ArmExtras.lean:18-22`):**
        ```lean
        macro_rules | `(tactic| decreasing_trivial) =>
          `(tactic| first
                  | grind
                  | decide
                  | sorry)
        ```
        Every recursive function or loop generated by `sail -lean` whose termination obligation is not closed by `grind` or `decide` is silently discharged with `sorryAx`.
     2. **Coq-only termination measures (`arm-v9.4-a/src/termination_measures.sail:43-116`):** Since commit `dc802ff856cce91f24c221be676469aab790dfc8` (`2025-07-04`), all 24 `termination_measure ... loop` declarations (covering `AArch64_S1Walk`, `AArch64_S2Walk`, `FPRoundBase__1`, `FloorPow2`, `FPToFixedJS`, `ReservedValue`, etc.) are wrapped in `$iftarget coq ... $endif` and are invisible to the Lean backend.
     3. **Historical `emod_nat` → `"Nat.div"` bug (`arm-v9.4-a/src/prelude.sail:108-112`):** Until commit `7d0581642d0e3aaca367bbc5650aca7c53057543` (`2026-10-11`, *"Fix mistake in extern mapping for emod_nat for Lean"*), `emod_nat` (`MOD`) was mapped to `lean: "Nat.div"` instead of `lean: "Nat.mod"`, causing `ROR_C` and `ROR` (`arm-v9.4-a/src/builtins.sail:101, 112`) to divide by the bitvector width instead of taking the remainder.

---

### 2. Area 2 — x86-64 Sail Models (`sail-x86-from-acl2`, `sail-tiny-x86`)

#### 2.1 Comparative Overview of the x86-64 Sail Models

| Dimension | `rems-project/sail-x86-from-acl2` (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`) | `rems-project/sail-tiny-x86` (`229bd8448937042baa51b0a2d14bc437929b0dce`) |
|---|---|---|
| **Origin & Size** | Automated Python+ACL2 translation of Shilpi Goel's ACL2 `x86isa` model; 32,896 LOC across 62 `.sail` files | Handwritten 64-bit user-space x86-64 subset; 2,996 LOC total (1,998 LOC excluding `tests.sail`) across 8 `.sail` files |
| **Instruction Scope** | 1-byte (`step.sail`: 2,493 LOC), 2-byte `0F` (`two_byte_opcodes_dispatch.sail`: 2,805 LOC), VEX (`vex_opcodes_dispatch.sail`: 6,083 LOC), EVEX (`evex_opcodes_dispatch.sail`: 9,837 LOC); 3-byte opcodes stubbed (`1` line) | 19 `ast` constructors (`MOV`, `XOR`, `SFENCE`, `LFENCE`, `MFENCE`, `CMP`, `CMPXCHG`, `XCHG`, `PUSH`, `POP`, `ADD`, `SUB`, `IMUL`, `CALL`, `LEAVE`, `RET`, `JMP`, `JNS`, `JNE`) |
| **Fetch-Decode-Execute Architecture** | **Fused:** `x86_fetch_decode_execute` (`step.sail:2414-2493`) has **no `ast` type**; opcode handlers fetch ModR/M, SIB, displacement, and immediate bytes directly from memory during execution | **Two-phase but impure decode:** `fetch_execute` calls `decode(rip) -> (ast, new_rip)` (`decode.sail:405-527`), updates `rip = new_rip` (`tiny-x86.sail:13`), then calls `execute(decoded)` |
| **Address Translation & Modes** | Both `app_view : bool` (linear user memory) and 4-level IA-32e paging (`ia32e_la_to_pa_page_table_walk` in `paging.sail`); 64-bit (`n64_bit_modep`) and 32-bit modes | User-space 64-bit flat virtual addresses only (`bits(64)`); no segmentation, paging, or privilege levels |
| **Memory Interface** | Legacy `__read_mem` / `__write_mem` byte-loop (`prelude.sail:604-632, 677-709`) wrapped by `rb_1`/`wb_1` and `rme08`..`rme64` / `wme08`..`wme64` (`linear_memory.sail`) | `CONCURRENCY_INTERFACE_V2` (`sail_mem_read`, `sail_mem_write`, `sail_barrier` in `interface.sail:76-109`) |
| **Lean 4 Codegen Readiness** | Does not compile with `sail --lean` out of the box (unbounded `int` recursion, legacy memory builtins, `-memo_z3` range constraints) | Closer to `sail --lean` (`CONCURRENCY_INTERFACE_V2`), but blocked by `vector(16, register(bits(64)))` dereferencing (`*GPRs[i]`) and has a semantic RIP-relative addressing bug |

#### 2.2 `sail-x86-from-acl2`: Fused Variable-Length Fetch-Decode-Execute and Lean 4 Codegen Obstacles

In `rems-project/sail-x86-from-acl2` (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`), the Python translator (`translator/transform.py`, `config_patterns.py`, `specialTokens.py`, `manualInterventions.py`) queries a live ACL2 process (`callACL2.py`) to translate the ACL2 `x86isa` book into 62 `.sail` files under `model/`.

1. **Why there is no `ast` union type (`model/step.sail:2414-2493`):**
   - `x86_fetch_decode_execute()` starts at `start_rip = read_rip()`, calls the recursive function `get_prefixes(start_rip, 0x0000, 15)` (`step.sail:86-145`) to consume up to 15 legacy/REX prefix bytes one byte at a time via `rme08(proc_mode, start_rip, :x)` (instruction fetch), and reads the opcode byte at `temp_rip`.
   - If the opcode byte is `0xC4`/`0xC5` (VEX) or `0x62` (EVEX), `x86_fetch_decode_execute` fetches the subsequent prefix bytes and dispatches to `vex_two_byte_opcodes_dispatch` / `vex_three_byte_opcodes_dispatch` or `evex_two_byte_opcodes_dispatch` / `evex_three_byte_opcodes_dispatch`.
   - Otherwise, it checks `one_byte_opcode_modr_m_p(proc_mode, rex_byte, opcode)` (`prefix_modrm_sib_decoding.sail:72-96`), conditionally fetches `modr_m` and `sib` (`x86_decode_sib_p`) via `rme08`, and dispatches into the 256-arm `one_byte_opcode_execute` (`step.sail:150-2407`). Each instruction semantic function (e.g., `x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g` in `add_adc_sub_sbb_or_and_xor_cmp_test.sail`) then reads its own displacement and immediate bytes from `temp_rip`, computes `next_rip`, checks canonicality (`!CanonicalAddressCheck(next_rip)`), writes memory/registers/flags (`rflagsbits`), and finally commits `write_rip(next_rip)`.
2. **Incomplete subsystems in the ACL2 translation (`translator/config_patterns.py`):**
   - `model/three_byte_opcodes_dispatch.sail` is a 1-line placeholder comment (`// Placeholder for future precision enhancement`).
   - Floating-point arithmetic is excluded (`config_patterns.py:106-108` comments out `fp-structures.lisp` and `fp-primitives.lisp`); `model/topfp.sail` includes only `mov.sail` and `shuffle_and_unpack.sail`.
   - System calls (`x86-syscall-app-view`) are excluded (`config_patterns.py:191-193`) because the ACL2 syscall model mutates a host filesystem/environment state not modeled in Sail.
3. **Four concrete `sail --lean` codegen obstacles in `sail-x86-from-acl2`:**
   - **Obstacle 1 (Unbounded `int` recursion without termination measures):** `model/prelude.sail:336-408` defines `logcount_int`, `logand_int`, `logior_int`, `logxor_int` by general recursion over `int` (`n >> 1`) without `termination_measure`, and `model/step.sail:88` defines `get_prefixes(start_rip, prefixes, cnt : range(0, 15))` without a `termination_measure get_prefixes cnt = cnt`.
   - **Obstacle 2 (Legacy `__read_mem` / `__write_mem` interface):** `model/prelude.sail:604-632, 677-709` calls legacy Sail builtins `__read_mem` and `__write_mem` in a byte loop, rather than `CONCURRENCY_INTERFACE_V2` (`sail_mem_read` / `sail_mem_write`) expected by `rems-project/lean-sail`.
   - **Obstacle 3 (Runtime range check casts):** `model/prelude.sail:133-173` defines `check_range(low, high, x) -> {'n, low <= 'n <= high. int('n)}` using `assert(low <= x & x <= high)`, generating existential dependent integer witnesses across thousands of translated ACL2 expressions.
   - **Obstacle 4 (Exception and fault modeling):** Faults and unimplemented paths (`ms.sail`, `fault.sail`, `prelude.sail:61-70`) call `throw(Emsg("..."))`, aborting the Sail monad rather than transitioning to an architectural exception vector when `ms` (model state fault flag) is set.

#### 2.3 `sail-tiny-x86`: Impure Decode, Register-Reference Vectors, and the RIP-Relative Addressing Bug

`rems-project/sail-tiny-x86` (`229bd8448937042baa51b0a2d14bc437929b0dce`) is a 1,998-line (excluding `tests.sail`) handwritten x86-64 model with a Rocq snapshot (`snapshot/Tiny_x86.v`) using `CONCURRENCY_INTERFACE_V2`. Our audit identified three critical architectural findings:

1. **Impure `decode(rip)` that evaluates effective memory addresses at decode time (`decode.sail:180-210, 271-334`):**
   - In `decode.sail:1-23`, operands in `union ast` use `union reg_or_mem = { rm_REG : reg_index, rm_MEM : bits(64) }`.
   - Rather than representing an addressing mode syntactically as `(base : Option reg_index, index : Option (scale × reg_index), disp : bits(32))`, `decode_rm_operand_inner` (`decode.sail:271-334`) **reads the current values of base and index GPRs during `decode`** via `read_GPR(64, r_m)` and `read_SIB(...)` (`decode.sail:180-210`), computes the 64-bit effective virtual address `mem_loc : bits(64)`, and stores `rm_MEM(mem_loc)` inside the decoded `ast`!
   - As a result, `decode` in `sail-tiny-x86` is not a pure function of instruction bytes (or even of instruction bytes + `rip`); it depends on the live GPR file.

2. **Semantic Bug in RIP-Relative Addressing (`decode.sail:300-308` vs. `tiny-x86.sail:9-20`):**
   - In `tiny-x86.sail:9-20`, `fetch_execute()` runs:
     ```sail
     function fetch_execute() -> unit = {
         let (decoded, new_rip) = decode(rip);
         rip = new_rip;
         execute(decoded);
     }
     ```
   - During `decode(rip)`, when ModR/M has `mod == 0b00` and `three_bit_rm_reg == 5` (`0b101`, x86-64 RIP-relative addressing), `decode_rm_operand_inner` (`decode.sail:300-308`) executes:
     ```sail
     let displacement = read_memory(4, add_bits(rip, num_bytes_read), create_iFetchAccessDescriptor());
     num_bytes_read = add_bits(num_bytes_read, 0x0000000000000004);
     mem_loc = add_bits(rip, sail_sign_extend(displacement, 64));
     ```
   - Here `rip` is the **address of the start of the current instruction**, not `new_rip` (the address of the next instruction)! Even worse, for instructions with an immediate operand following the ModR/M displacement (such as `MOV r/m64, imm32` or `CMP r/m64, imm8` in `decode.sail:410-416, 444-451`), the trailing immediate bytes have not even been read yet when `decode_rm_operand` runs.
   - In actual x86-64 hardware (Intel SDM Vol. 2A §2.2.1.6), RIP-relative addressing computes `effective_address = next_rip + sign_extend(disp32) = (rip + instr_len) + sign_extend(disp32)`. Thus, `sail-tiny-x86` is off by `-instr_len` bytes on every RIP-relative memory access (mechanized in Part 2b of `support/sail_tiny_arm_and_capability_bridge_probe.lean`, theorems `tinyX86_rip_relative_discrepancy` and `tinyX86_mov_rip_rel_counterexample`).

3. **First-Class Register Reference Vector (`registers.sail:34-51`):**
   - `registers.sail:34-51` defines `let GPRs : vector(16, register(bits(64))) = [ref r15, ..., ref rax]` and reads/writes registers via `(*GPRs[index])`. While supported by Sail's C and Rocq backends, `sail --lean` does not support vectors of `register(...)` references and requires an explicit `match` dispatcher over `reg_index` (as used in `sail-x86-from-acl2/model/registers.sail:45-88`).

---

### 3. Area 3 — CHERI Capability Sail Models (`sail-morello`, `sail-cheri-riscv`, `cheriot-sail`, `coq-cheri-capabilities`)

#### 3.1 Cross-Architecture Capability Encoding Comparison

| Property | Arm Morello (`CTSRD-CHERI/sail-morello` `2305f656ff84619caf50107f49dae7be52aec72b`) | 64-Bit CHERI-RISC-V (`CTSRD-CHERI/sail-cheri-riscv` `cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b`) | 32-Bit CHERIoT (`CHERIoT-Platform/cheriot-sail` `518813ec3e595f79930d9129eaded2521831cbe2`) |
|---|---|---|---|
| **Capability Granule Size** | 128 bits (`CAPABILITY_DBYTES = 16`) + 1 out-of-band tag bit = `bits(129)` | 128 bits (`cap_size = 16`, `log2_cap_size = 4`) + 1 out-of-band `tag : bool` | 64 bits (`cap_size = 8`, `log2_cap_size = 3`) + 1 tag bit + 1 revocation bit per 8 bytes |
| **Address & Flags** | 64-bit `value` (`[63..0]`): 56-bit sign-extended `CapBoundsAddress` + 8 high `flags` bits (`[63..56]`) | 64-bit `address` (`[63..0]`) + 1-bit `flag_cap_mode` | 32-bit `address` (`[31..0]`) |
| **Compressed Bounds Mantissas & Exponent** | 16-bit `bottom` (`[79..64]`, `CAP_MW = 16`), 14-bit `top` (`[93..80]`), 1-bit `IE` (`[94]`); 6-bit exponent inverted in memory (`CapGetBounds` in `src/v8_base.sail:3018-3086`) | 14-bit `B` (`cap_mantissa_width = 14`), 12-bit `T`, `internal_E : bit` stealing 3 bits each from `T` and `B` for 6-bit exponent `E` (`max_E = 52`, `src/cheri_prelude_128.sail`, `src/cheri_cap_common.sail`) | 9-bit `B` (`cap_mantissa_width = 9`), 9-bit `T`, 4-bit compressed `cE` (`0xf` expands to `cap_max_E = 24`, `src/cheri_cap_common.sail:243-328`) |
| **Object Type (`otype`)** | 15-bit `otype` (`[109..95]`): `0` = unsealed, `1` = `RB` sentry, `2` = `LPB`, `3` = `LB` | 18-bit `otype` (`otype_unsealed = -1`, `otype_sentry = -2`) | 3-bit `cotype` expanding to 4-bit `otype` (executable vs. non-executable split; `0` = unsealed, `1..5` = forward/return/interrupt sentries) |
| **Permissions** | 18 bits (`[127..110]`): `Global`, `Executive`, 4 user bits, `MutableLoad`, `CompartmentID`, `BranchSealedPair`, `System`, `Unseal`, `Seal`, `StoreLocalCap`, `StoreCap`, `LoadCap`, `Execute`, `Store`, `Load` | 12 hardware permissions (`permit_load`, `permit_store`, `permit_execute`, `permit_load_cap`, `permit_store_cap`, `permit_store_local_cap`, `permit_seal`, `permit_unseal`, `permit_ccall`, `permit_set_cid`, `access_system_regs`, `global`) + 4 `uperms` | 6-bit Quadrant-compressed `cperms` (`mem_uty`, `mem_ex`, `sealing`, `user`) expanding to 12 architectural permissions (`src/cheri_cap_common.sail:184-241`) |
| **In-Memory Null Representation** |Exponent bits inverted (`not_vec`) when `IE == 0` so all-zero 128-bit memory decodes to `CapNull` | `capToMemBits` / `memBitsToCapability` (`cheri_cap_common.sail:259-265`) XORs the 64-bit metadata half with `null_cap_bits` | `capToMemBits` / `memBitsToCapability` (`cheri_cap_common.sail:330-336`) XORs the 32-bit metadata half with `null_cap_bits` |

#### 3.2 Tag-Preserving vs. Tag-Stripping Memory Accesses and Monotonicity Proofs

1. **Tag-Stripping on Raw Data Writes vs. Tag-Preserving Capability Accesses:**
   - In `CTSRD-CHERI/sail-morello/src/mem.sail:56-98`:
     - Capability loads/stores call `__ReadTaggedMem` and `__WriteTaggedMem`, asserting `addr == Align(addr, CAPABILITY_DBYTES)` (16-byte alignment) and reading/writing the 1-bit capability tag via `__read_tag_bool` / `__write_tag_bool`.
     - Non-capability data stores call `__WriteMem` (`src/mem.sail:87-98`), which **unconditionally clears the capability tag** of the enclosing 16-byte granule:
       ```sail
       let tag_addr = Align(addr, CAPABILITY_DBYTES);
       __write_tag_bool(ZeroExtend(tag_addr), false);
       ```
   - In `CTSRD-CHERI/sail-cheri-riscv/src/cheri_mem_metadata.sail:77-93` and `src/cheri_mem.sail:65-89` (and identically in `CHERIoT-Platform/cheriot-sail`):
     - Every RAM write updates metadata via `__WriteRAM_Meta(addr, width, tag)`. If an unaligned write straddles two capability granules (`tag_addr1 != tag_addr2`), both tags are updated.
     - Standard integer/floating-point stores invoke `mem_write_ea` with `default_meta = false`, stripping any capability tag overlapping the written bytes. Only `mem_write_cap` passes `cap.tag`, and `CLC` / `LC` (`src/cheri_insts.sail:1357-1431`) strips the loaded capability's tag if the authorizing capability lacks `permit_load_cap` (`clearTagIf(v, not(auth_val.permit_load_cap))`). In `cheriot-sail`, `mem_read_cap_revoked` (`src/cheri_mem.sail:102-110`) additionally clears the loaded tag if `permit_load_mutable` is false or if the hardware revocation bit for the target 8-byte granule is set.

2. **Monotonicity Specifications (`cheriot-sail/properties/props.sail` and `rems-project/coq-cheri-capabilities`):**
   - `CHERIoT-Platform/cheriot-sail/properties/props.sail` contains 13 formal `$property` specifications verified via Sail's SMT backend, including `prop_decEnc` (decode-encode roundtrip for valid capabilities), `prop_setbounds` (bounds requested by `setCapBounds` are enclosed by returned bounds), and `prop_setbounds_monotonic` (`props.sail:154-167`), which states that whenever `setCapBounds(c, req_base, req_top)` produces a capability `newCap` that does not exceed parent bounds, `newBase >= origBase` and `newTop <= origTop`.
   - `rems-project/coq-cheri-capabilities` (`b39cd73409d8c2a058ba8065f81dc72d3c84fb11`) defines an abstract `Module Type Capability_GS` (`theories/Common/Capabilities.v`) with `leq_bounds`, `leq_perms`, and `leq_cap`, instantiates it with the Sail-extracted Morello capability operations in `theories/Morello/CapFns.v` and `theories/Morello/Capabilities.v`, and proves in `theories/Morello/Lemmas.v` (`cap_set_bounds_Represents`, `cap_set_bounds_mono`, `leq_bounds_to_cap_addresses_subset`) that bounds narrowing and permission masking monotonically shrink the set of dereferenceable byte addresses.
   - Note on `christiankissig/rocq-cheriot-sail`: `git ls-remote https://github.com/christiankissig/rocq-cheriot-sail.git` returns 0 refs/commits as of `2026-10-29` (empty upstream repository).

---

### 4. Area 4 — Specialized Lean 4 Sail RISC-V Extractions (`opencompl/sail-riscv-lean`, `Verified-zkEVM/riscv-zkvm`, `axiom-crypto/sail-riscv-lean`)

#### 4.1 Quantitative Comparison of the Three RISC-V Lean 4 Repositories

| Metric / Architecture | `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) | `Verified-zkEVM/riscv-zkvm` (`6810fc14d9c40373101321cefaec59df8d82e3e7`) | `axiom-crypto/sail-riscv-lean` (`82afed87c9d6827d3691acbe66d5395fa37dc41d`) |
|---|---|---|---|
| **Lean 4 Toolchain** | `leanprover/lean4:v4.29.0` | `leanprover/lean4:v4.33.1` | `leanprover/lean4:v4.34.0` |
| **`lean-sail` Dependency** | `rems-project/lean-sail@v5` (`079463134b9c50450b8393e1566a09fc492a34d9`) | `rems-project/lean-sail@v5` (`079463134b9c50450b8393e1566a09fc492a34d9`) | Vendored in `Lean_RV32D/lean-sail` (`79b4d08505af29d88b3918f32d29840fae1fa191`) |
| **Upstream `sail-riscv` Base & Sail Compiler** | Full `riscv/sail-riscv` RV64D | `riscv/sail-riscv` tag `0.13.1` (`27224ccb...`), Sail `0.20.3` (`60695b1e...`) | `axiom-crypto/sail-riscv` (`3c31d86d...` on `0.13.1`), Sail `0.20.2` |
| **Extracted Sail `.lean` Files & LOC** | 161 files, 173,776 LOC (`LeanRV64D`) | 121 files, 60,078 LOC (`RiscvZkvm.Sail`); plus 89 files, 32,902 LOC in `Rv64` + `SailEquiv` + `Logic` | 115 files, 55,561 LOC (`LeanRV32D`) |
| **`instruction` Constructors** | 353 constructors (full RV64GC + V + Zvk + Zfa/Zfh + CFI + SV32/39/48/57) | 33 constructors in `RiscvZkvm.Sail` (scoped to `main`, `I_insts`, `M_insts`, `Zicsr_insts`, `K_core`, `Zkr`, `Zicboz`, `Zicbom_insts`); 56 in `RiscvZkvm.Rv64.Instr` | 34 constructors (RV32IM + `Zicsr` + `Zicfilp` + 5 custom `OPENVM_*` instructions) |
| **Computability (`noncomputable` count)** | 165 `noncomputable` occurrences (`--lean-noncomputable`) | 124 in `RiscvZkvm.Sail` (`--lean-noncomputable`), 5 in `SailEquiv`; `RiscvZkvm.Rv64` is 100% computable (`0`) | **0 `noncomputable` occurrences** across entire package (fully computable) |
| **`sorry` / `axiom` Count** | **0 `sorry`**; 75 `axiom` declarations in `LeanRV64D/RiscvExtras.lean` | **0 `sorry`**; 75 `axiom` declarations in `RiscvZkvm/Sail/RiscvExtras.lean` (only 4 reachable from `Rv64.SailEquiv`, enforced by `scripts/AxiomSweep.lean`) | **0 `sorry`** and **0 `axiom` declarations** (`RiscvExtrasExecutable.lean` uses total functions) |

#### 4.2 Architectural Lessons from `Verified-zkEVM/riscv-zkvm` and `axiom-crypto/sail-riscv-lean`

1. **Why `sail-riscv-lean` Has Zero `sorry` While `sail-arm` Uses `sorry` (`RiscvExtras.lean:119-123`):**
   - Unlike `rems-project/sail-arm` (which gates termination measures under `$iftarget coq` and puts `sorry` into `ArmExtras.lean`), `riscv/sail-riscv` passes `--variable "TERMINATION_FILE = true"` during Lean extraction, and `RiscvExtras.lean:119-123` supplies `instance : SizeOf extension where sizeOf := extension.ctorIdx` and `macro_rules | `(tactic| decreasing_trivial) => `(tactic| decide)`. Every recursive function in the 173,776-line `LeanRV64D` model and the 60,078-line `RiscvZkvm.Sail` model elaborates with kernel-checked termination proofs and zero `sorryAx`.

2. **Scoped Module Extraction and Narrow Import Closure (`Verified-zkEVM/riscv-zkvm`):**
   - Extracting the full `riscv/sail-riscv` specification produces 173k lines of Lean 4 and includes `RvfiDii.lean`, which takes ~13–14 GiB RSS and tens of minutes to elaborate from source.
   - `Verified-zkEVM/riscv-zkvm` solves this at two levels:
     - First, `scripts/regen-model.sh` (`sail-import/PROVENANCE.toml`) restricts `sail --lean` to the 8 Sail modules needed for RV64IM (`main`, `I_insts`, `M_insts`, `Zicsr_insts`, `K_core`, `Zkr`, `Zicboz`, `Zicbom_insts`), cutting the extraction to 33 `instruction` constructors and 60k lines.
     - Second, `RiscvZkvm/Rv64/SailEquiv/StateRel.lean:6-29` imports `RiscvZkvm.Sail.InstsEnd` rather than the umbrella `RiscvZkvm.Sail`, pruning `Step`, `Fetch`, and `RvfiDii` from the dependency graph of all 2,500+ downstream proof modules.

3. **Two-Tier Verification Bridge (`RiscvZkvm.Rv64` ↔ `RiscvZkvm.Sail` via `SailEquiv`):**
   - Symbolic execution (`sym_step`, `runBlock`, separation-logic frame cancellation `xcancel` in `RiscvZkvm.Rv64.Logic`) runs over the hand-written, computable `RiscvZkvm.Rv64.MachineState` (`regs : Reg → Word`, 8-byte aligned `mem : Word → Word`, `pc : Word`, `code : Word → Option Instr`), **not** directly over Sail's monadic `SequentialState` (`Std.ExtDHashMap` registers + byte-granular `Std.ExtHashMap Nat (BitVec 8)` memory).
   - `RiscvZkvm.Rv64.SailEquiv` bridges the two models via:
     - `StateRel` and `StateRelPC` (`StateRel.lean:221-256`): relates `sRv.getReg r` to `sailRegVal sSail r` (`x0` hardwired to `0#64`, `x1`..`x31` in `sSail.regs`), `sRv.getMem a` on 8-aligned addresses to `reconstructDword sSail.mem a.toNat`, and `sRv.pc` to `sSail.regs.get? Register.PC`.
     - `MemPresent lo hi mem` and `PlatformFrame s s'` (`StateRel.lean:266-379`): because Sail's `readByte` errors on absent `Std.ExtHashMap` keys and `vmem_read`/`vmem_write` consult 8 privilege/PMP/PMA/MMIO registers (`BareModeInv`), `PlatformFrame` proves that user-mode instructions leave all 8 platform registers unchanged and only grow `sSail.mem` (`mem_mono`), allowing `sailStep_run_sim` (`StepRun.lean:451-475`) to compose into the multi-step simulation theorem `sailStepN_run_sim` (`StepRun.lean:505-537`).
     - **The `#10688` Vacuity Lesson (`StepRun.lean:220-243, 540-605`):** When `sail-riscv` is extracted with a scoped module list, scattered functions like `currentlyEnabled` emit a failing catch-all for omitted extensions. In an earlier extraction that omitted `Zicsr_insts`, `execute_JALR` called `update_elp_state` (`Zicfilp`), which queried `currentlyEnabled Ext_Zicsr` and threw an exception in **every** state—making the `JALR` precondition `instrSideCond (.JALR ..)` unsatisfiable and rendering the `jalr_sail_equiv` implication theorem vacuously true! `riscv-zkvm` fixed this by including `Zicsr_insts` in the module scope and adding a mandatory constructive anti-vacuity theorem `jalr_sideCond_satisfiable` (`StepRun.lean:584-605`).

4. **Zero-Axiom Computable Extraction and Custom Extensions (`axiom-crypto/sail-riscv-lean`):**
   - `axiom-crypto/sail-riscv-lean` (`82afed87c9d6827d3691acbe66d5395fa37dc41d`) targets `leanprover/lean4:v4.34.0` and demonstrates that omitting `--lean-noncomputable` and replacing `RiscvExtras.lean`'s `axiom` declarations with total Lean functions in `RiscvExtrasExecutable.lean` (`panic "TODO: ..."` for unused float/reservation hooks, `false` for `valid_reservation` and `sys_enable_experimental_extensions`) yields a 100% computable Sail extraction with **zero axioms**.
   - It also demonstrates clean Sail-level extension modularity (`Lean_RV32D/LeanRV32D/XopenvmInsts.lean` and `InstsEnd.lean:4773-4803`): adding `Ext_Xopenvm` and 5 custom zkVM instructions (`OPENVM_TERMINATE`, `OPENVM_HINT_STOREW`, `OPENVM_HINT_BUFFER`, `OPENVM_REVEAL`, `OPENVM_PHANTOM`) operating on custom Sail registers `hint_oracle : list(bits(8))` and `reveal : vector(536870912, bits(8))`.

---

### 5. Area 5 — Synthesis & Lean 4.34.1 Mechanized Bridge for Anneal

#### 5.1 Architectural Recommendations for Anneal (`joshlf/anneal-private`)

1. **Adopt the Two-Tier `Rv64` + `SailEquiv` Pattern for Anneal's Target ISAs:**
   - Directly running Anneal's weakest-precondition and separation-logic automation over raw `sail --lean` output (`SequentialState` with `Std.ExtDHashMap` register lookups, `SailME.run` early-return transformers, and 8-register `BareModeInv` address-translation side conditions on every load/store) is orders of magnitude slower to elaborate than running tactics over a pure, total, computable functional machine model and discharging equivalence once per instruction via a `SailEquiv` simulation layer.
2. **For AArch64 Verification in Anneal:**
   - Use `rems-project/sail-tiny-arm-lean` (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`, `SailTinyArmUser`) as the baseline template for monadic `SailM` / `SailME` user-mode AArch64 semantics in Lean 4, or combine it with `Verified-zkEVM/riscv-zkvm`'s `StateRelPC` / `BridgeTransition` pattern.
   - If system-mode AArch64 (`pgt_walk`, `EL1` exceptions, `MRS`/`MSR`, `TLBI`) is required, extract `rems-project/sail-tiny-arm` with `sail --lean -D SYSTEM_TINY_ARM` (`translation.sail:141-201` already includes `termination_measure pgt_walk level = 4 - level`).
   - Do **not** import `rems-project/sail-arm`'s `arm-v9.4-a` Lean output into Anneal's TCB unless `arm-v9.4-a/lean/ArmExtras.lean:22` (`sorry` in `decreasing_trivial`) is removed and `arm-v9.4-a/src/termination_measures.sail` enables its 24 loop termination measures for the `lean` target (`$iftarget coq lean`).
3. **For x86-64 Verification in Anneal:**
   - Do **not** use `rems-project/sail-tiny-x86` without first fixing its impure `decode(rip)` design and its RIP-relative addressing bug (`decode.sail:300-308`, where `mem_loc` adds `displacement` to un-incremented `rip` instead of `new_rip`), and replacing `let GPRs : vector(16, register(bits(64)))` (`registers.sail:34-51`) with an explicit `match` over `reg_index`.
   - For broad user-mode x86-64 instruction semantics, `rems-project/sail-x86-from-acl2/model/` provides 32,896 lines of battle-tested opcode semantics, but porting it to Lean 4 requires adding `termination_measure` annotations to `get_prefixes` and `log*_int` and replacing `__read_mem`/`__write_mem` with `CONCURRENCY_INTERFACE_V2`.
4. **For Capability-Typed / Spatial-Provenance Memory in Anneal (`Trusted/Memory.lean`):**
   - Anneal's `Trusted/Memory.lean` checks allocation liveness, mutability (`writable`), provenance (`allocId`), and spatial bounds (`[base, base + len)`) on every byte load/store.
   - CHERI capabilities (`CapWord` in `sail-morello`, `sail-cheri-riscv`, `cheriot-sail`) enforce an isomorphic check in hardware: a capability `c` with `c.tag = true` and `c.isUnsealed = true` refined by an Anneal allocation (`CapRefinesAnneal c am`) guarantees that any CHERI-permitted load (`c.perms.canLoad && c.inBounds width`) or store (`c.perms.canStore && c.inBounds width`) automatically satisfies Anneal's `am.canRead` / `am.canWrite` checks, while capability monotonicity (`cSetBounds`, `cAndPerm`, `cIncOffset`) preserves `CapRefinesAnneal` without consulting the allocator table, and tag-stripping on raw byte writes (`writeRawByte`) prevents forging capabilities in memory.

#### 5.2 Summary of Verified Theorems in `support/sail_tiny_arm_and_capability_bridge_probe.lean`

All declarations in [`support/sail_tiny_arm_and_capability_bridge_probe.lean`](support/sail_tiny_arm_and_capability_bridge_probe.lean) compile standalone under `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768` with zero `sorryAx` and zero custom axioms:

| Namespace & Declaration | Lines | Statement & Role |
|---|---|---|
| `BridgeTransition.no_stuck` | `97-103` | Any machine step wrapped in a sound `BridgeTransition` never produces `.stuck` (UB). |
| `SailTinyArmModel.decode_nop`, `decode_add_x0_x1_x2`, `execute_add_x0_x1_x2` | `375-400` | Exact `SailTinyArmUser` monadic `decode : BitVec 32 → SailM ast` and `execute` semantics for `NOP` and `ADD X0, X1, X2`, plus `XZR` (`X31`) zero-register laws (`rX_xzr`, `wX_xzr`). |
| `SailTinyArmModel.tinyArmBridge`, `tinyArmBridge_never_stuck` | `408-424` | Packages `SailTinyArmUser`'s `fetch_and_execute` (with `SailME.run` early-return semantics) into Anneal's `BridgeTransition` and proves `.stuck`-freedom. |
| `SailTinyX86DecodeAudit.tinyX86_rip_relative_discrepancy`, `tinyX86_mov_rip_rel_counterexample` | `442-456` | Proves that `sail-tiny-x86/decode.sail:300-308` under-computes every RIP-relative effective address by `instrLen` bytes (`archX86RipRelativeAddr - tinyX86DecodedRipRelativeAddr = instrLen`), with concrete counterexample `MOV RAX, [RIP + 0x10]` at `0x1000` (`0x1010` vs `0x1017`). |
| `CheriCapabilityBridge.CapWord.cAndPerm_monotone`, `cSetBounds_monotone`, `cIncOffset_monotone` | `588-608` | Proves that whenever `cAndPerm`, `cSetBounds`, or `cIncOffset` yields a capability with `tag = true`, the parent capability was tagged and unsealed, new bounds are a subset of parent bounds (`CapBounds.subset`), permissions are a subset (`Perms.le`), and `allocId` provenance is preserved. |
| `CheriCapabilityBridge.CapMem.writeRawByte_strips_enclosing_cap_tag`, `readCapGranule_after_writeRawByte_untagged`, `readCapGranule_without_loadCap_strips_tag` | `632-695` | Proves that raw byte writes unconditionally clear the capability tag of the enclosing 16-byte granule (`capGranule addr`), preserve tags of disjoint granules, and force any subsequent capability load from that granule (or any load lacking `canLoadCap`) to return `tag = false`. |
| `CheriCapabilityBridge.CapRefinesAnneal.cSetBounds`, `cAndPerm`, `cIncOffset` | `742-774` | Proves that monotonic capability derivations preserve the `CapRefinesAnneal` spatial/provenance invariant against Anneal's `AnnealMem`. |
| `CheriCapabilityBridge.cheri_load_check_implies_anneal_canRead`, `cheri_store_check_implies_anneal_canWrite` | `781-815` | Proves that CHERI hardware tag, unsealed, permission, and bounds checks imply Anneal's abstract `canRead` / `canWrite` spatial and provenance checks. |
| `CheriCapabilityBridge.cheriByteStoreBridge`, `cheriCapStoreBridge`, `*_never_stuck` | `840-926` | Constructs sound `BridgeTransition` instances for both raw byte stores and 16-byte capability granule stores on `CoupledCapState` and proves `.stuck`-freedom. |

---

## Boundaries

1. **Unpopulated Upstream Repository (`christiankissig/rocq-cheriot-sail`):** As of `2026-10-29`, `https://github.com/christiankissig/rocq-cheriot-sail` is an empty GitHub repository (`git ls-remote` returns 0 refs/commits). All CHERIoT formalization findings in this report are therefore grounded in `CHERIoT-Platform/cheriot-sail` (`518813ec3e595f79930d9129eaded2521831cbe2`) and `rems-project/coq-cheri-capabilities` (`b39cd73409d8c2a058ba8065f81dc72d3c84fb11`).
2. **Compressed Bounds Mantissa Arithmetic vs. Decoded Bounds Interval (`CapBounds`):** Our Lean 4.34.1 probe (`support/sail_tiny_arm_and_capability_bridge_probe.lean`) models decoded capability bounds `CapBounds = { base : Nat, top : Nat }` together with an explicit `representable : Bool` parameter in `cSetBounds` and `cIncOffset`, matching the abstract specification layer `Capability_GS` in `rems-project/coq-cheri-capabilities/theories/Common/Capabilities.v`. It does not re-mechanize Morello's 16-bit/14-bit floating-point mantissa encoding (`CapGetBounds` / `CapSetBounds` in `sail-morello/src/v8_base.sail:3018-3230`).
3. **System-Mode `sail-tiny-arm` Lean Extraction:** While `rems-project/sail-tiny-arm` implements EL1&0 4-level page-table walks (`pgt_walk` in `translation.sail:141-201`) under `-D SYSTEM_TINY_ARM`, `rems-project/sail-tiny-arm-lean` (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`) only checks in the user-mode extraction (`SailTinyArmUser`).

---

## Evidence

All primary files, full 40-character commit SHAs, `git_blob` SHA-1 hashes, `sha256` digests, line counts, and symbol scopes are recorded in [`support/source-manifest.json`](support/source-manifest.json).

- **Arm Sail Models:**
  - `rems-project/sail` (`0f51056900af85d0b18928d6ea2d2271d18184e8`): `src/sail_lean_backend/sail_plugin_lean.ml` (blob `c4f31495b312316b026a9971a9cf3a198a3f9bf5`).
  - `rems-project/sail-tiny-arm` (`98d904912620ddd74e76714b7ef8457192cb4e3a`): `Makefile` (blob `f86366f4074d76182c7d4160b67d7524f3c13bf8`), `registers.sail` (blob `c4966376e7f7fc8fc0c42a3dc0166a4102348244`), `translation.sail` (blob `7825e1e9ca8558f74ff007bc16187b9c3549448e`), `instrs-user.sail` (blob `4270296ebca5771122a4efce59db786f0927c655`), `instrs-sys.sail` (blob `1f7a387ca6bc48486364fc7bb9d8586958ab3489`).
  - `rems-project/sail-tiny-arm-lean` (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b` and `e8fbacf0af7ff196cc84b95baa7c2dbb35c4dd3a`): `SailTinyArmUser/Defs.lean` (blob `b1564a17e772bfbd0ab5e4e20964ef8f0917e6d1`), `SailTinyArmUser/Translation.lean` (blob `e2df48441a084152a5c9ff31f108c7cc402d255b`), `SailTinyArmUser/TinyArm.lean` (blob `a27136f88922f262939c73168775e8a6e220b9f6`), `Out/Defs.lean` at `e8fbacf` (blob `6217ee317d6ff99c3831802f7ca57c047d7cf823`), `Out/TinyArm.lean` at `e8fbacf` (blob `06cf5cb0c2f7f1d958632761fd191d1d241b87d6`).
  - `rems-project/sail-small-arm` (`d6b7c9cf86adaa479492b3881884b190a48f385b`): `armV8.sail` (blob `b765065d6390b10bd262fb053e61ae8d79b15e19`), `armV8_A64_lib.sail` (blob `356a71a79d150b5efbe723bc15726b49d4649c00`).
  - `rems-project/sail-arm` (`7d0581642d0e3aaca367bbc5650aca7c53057543`): `arm-v9.4-a/Makefile` (blob `7825a701e9ef224f50c869ab8682cbffaa095d84`), `arm-v9.4-a/lean/ArmExtras.lean` (blob `c8d71c0a97ca8d567fb8aa84980c4f8f53f0fd39`), `arm-v9.4-a/src/termination_measures.sail` (blob `74fd9e7ef4ae448db4521ce0d2f07f6cc96df52f`), `arm-v9.4-a/src/prelude.sail` (blob `4b5d1cf2b7137cc218c9716578e2efbd4d10f12e`).
- **x86-64 Sail Models:**
  - `rems-project/sail-x86-from-acl2` (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`): `translator/config_patterns.py` (blob `95f97d2ec4b375cd8c8736a6e179128df0ec2833`), `model/prelude.sail` (blob `9ef3ff4e9b6fa915b383ab063d9ce297dc8fb34e`), `model/registers.sail` (blob `75bc5d7a36884aa73e79b28fd0603ff63700e6d2`), `model/linear_memory.sail` (blob `c707200ce04fb0018e54be63b7a001809e270cb0`), `model/paging.sail` (blob `2e7a8fa5fd6bb60a0d69df90a480b75cbca2b238`), `model/step.sail` (blob `3ab8bd368186be37364c434aa60508b36d6a622a`).
  - `rems-project/sail-tiny-x86` (`229bd8448937042baa51b0a2d14bc437929b0dce`): `registers.sail` (blob `5d26386bc8e86904973784a912a3cd21cf8a4971`), `interface.sail` (blob `b911cb51bf2eb6061fc52267ef2973bd7f9d4c4e`), `decode.sail` (blob `c80ee4cd0aa223f5d47762a28981115de1b79b65`), `tiny-x86.sail` (blob `f9fd9ab411bf8a8be530684bc22fb5f73bd0532c`).
- **CHERI Capability Sail Models:**
  - `CTSRD-CHERI/sail-morello` (`2305f656ff84619caf50107f49dae7be52aec72b`): `src/v8_base.sail` (blob `d6b80fc198532ef4c806a5f082ee0ee7e33022a6`), `src/instrs.sail` (blob `7f6282a4526592837959b329ffbeed8e87886352`), `src/mem.sail` (blob `56d8d4a0ff689b80d7e329f7e50821bc39402e4b`).
  - `CTSRD-CHERI/sail-cheri-riscv` (`cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b`): `src/cheri_prelude_128.sail` (blob `3ca3be8cd7764799bf9c4223d9f9bf4cf98b099f`), `src/cheri_cap_common.sail` (blob `765ce1980d0d508cc739778b316760d901c7eb96`), `src/cheri_mem_metadata.sail` (blob `03d71bc177c2685a2eb2898cf0f9e536931e6e1d`), `src/cheri_mem.sail` (blob `427f0376695f2fc9f00bc64e0b8681f90c313f11`), `src/cheri_insts.sail` (blob `855d0ff6370f6f8e2fb562e6a42b31861d945f2c`).
  - `CHERIoT-Platform/cheriot-sail` (`518813ec3e595f79930d9129eaded2521831cbe2`): `src/cheri_cap_common.sail` (blob `35629a59cb7334db79e5e5e7be9236391cb3ec1b`), `properties/props.sail` (blob `62c7df2213cf1597c606626a26ee83df109551e2`).
  - `rems-project/coq-cheri-capabilities` (`b39cd73409d8c2a058ba8065f81dc72d3c84fb11`): `theories/Common/Capabilities.v` (blob `447ae3e7fd842bc5879662bc36fc42a586aa0257`), `theories/Morello/Capabilities.v` (blob `1162a3d91cdbf597631173b3fd548e2948be95b1`), `theories/Morello/Lemmas.v` (blob `d255966a3c74e4be3fc35f2592c3480b78bfce98`).
- **Specialized Lean 4 Sail RISC-V Extractions:**
  - `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`): `lakefile.toml` (blob `078772e9170f4dc00ff0708949a01627cd96bf4c`), `LeanRV64D/RiscvExtras.lean` (blob `9510cf5919e7ce7638fd74bc190024bbffdd15bf`), `LeanRV64D/Defs.lean` (blob `bd4bd9e60a6c30bf51cf616931f49794246ce167`).
  - `Verified-zkEVM/riscv-zkvm` (`6810fc14d9c40373101321cefaec59df8d82e3e7`): `sail-import/PROVENANCE.toml` (blob `0f85b8d09ffab329713bc34bc93f7ab51bc3f16d`), `scripts/regen-model.sh` (blob `7c0b0916d3f7514e0415aa8091ce95958a1c6404`), `RiscvZkvm/Rv64/SailEquiv/StateRel.lean` (blob `7f54d60892bb8f39267780f6829b4d491c41a104`), `RiscvZkvm/Rv64/SailEquiv/StepSim.lean` (blob `85ff81bc204a0648f8bc9ecdb89bf5b2d478bf25`), `RiscvZkvm/Rv64/SailEquiv/StepRun.lean` (blob `23a8301c2224c6d0779fb3bc7a0ff2df15ca026e`), `scripts/AxiomSweep.lean` (blob `42ab528311ce6a9f06be520726c2f0c81048049e`).
  - `axiom-crypto/sail-riscv-lean` (`82afed87c9d6827d3691acbe66d5395fa37dc41d`): `Lean_RV32D/sail-source-provenance.tsv` (blob `efad40f6343a4072b4d48bfae0299c095826a32a`), `Lean_RV32D/LeanRV32D/RiscvExtrasExecutable.lean` (blob `f0d5cfdb22b1846df44fb26835be47fb5bc4839b`), `Lean_RV32D/LeanRV32D/XopenvmInsts.lean` (blob `b914483bc7dc88240568ff5a43269c069646d124`), `Lean_RV32D/LeanRV32D/InstsEnd.lean` (blob `e69939aa9ee227573dc422a2417b09d446750298`).

---

## Revalidation

To re-verify the standalone Lean 4.34.1 probe (`support/sail_tiny_arm_and_capability_bridge_probe.lean`) under the 768 MB memory cap and single-thread constraint, run:

```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M768 \
  reports/sail-arm-x86-cheri-and-riscv-models-lean-portability-2026/support/sail_tiny_arm_and_capability_bridge_probe.lean
```

The command must exit with status `0` and produce no output (all `#guard_msgs in #print axioms` assertions verify that only standard Lean axioms `propext` and `Quot.sound` are used, with zero `sorryAx` and zero custom axioms).

*Authored by an AI agent acting on joshlf's behalf.*
