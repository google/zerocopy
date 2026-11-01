<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Adapting LLVM's GlobalISel Backend and Composing the End-to-End `MIR -> AnLLVM -> ISA` Verification Pipeline in Anneal

## 1. Executive Summary

To extend Anneal's end-to-end verification boundary from Rust MIR through LLVM
IR down to target machine instructions (`PreDropMirLang -> MirLang -> AnLlvmLang
-> AnMachineLang -> PostRaMachineLang -> FramedIsaLang`), we must choose how to
structure, adapt, and verify the `llc` code-generation pipeline (`llvm/CodeGen/`
and `llvm/MC/`) and how to compose all ten stages of the compiler without
blowing up the Lean 4.34.1 kernel's reduction budget.

Based on primary-source inspection of LLVM 21.1.8 headers in
`/usr/include/llvm-21/llvm/`, empirical `llc` 21.1.8 pipeline and MIR dumps
across `x86_64`, `aarch64`, and `riscv64`, and two standalone Lean 4.34.1
mechanizations (`support/support_anllvm_globalisel_backend_probe.lean`, 3,547
lines, and `support/support_end_to_end_mir_anllvm_isa_pipeline_probe.lean`,
1,771 lines), we establish five core architectural conclusions:

1. **Adopt `GlobalISel`'s 4-stage SSA pipeline (`IRTranslator -> Legalizer +
  LegalizationArtifactCombiner -> RegBankSelect -> InstructionSelect`) and
  reject `SelectionDAGISel`.** `SelectionDAGISel`
  (`llvm/CodeGen/SelectionDAGISel.h`) converts each LLVM IR `BasicBlock` into an
  out-of-SSA dependency graph (`SDNode` / `SDValue`) whose side effects and
  instruction-coupling constraints are threaded through untyped `MVT::Other`
  chain edges (`EntryToken`, `TokenFactor`) and rigid `MVT::Glue` edges
  (`SelectionDAGNodes.h:158-218`). By contrast, `GlobalISel` maintains a single
  SSA `MachineFunction` representation
  (`MachineFunctionProperties::Property::IsSSA`, `MachineFunction.h:187-201`)
  typed by `LowLevelType` (`LLT`: `sN`, `p0`, `vN`, `LowLevelType.h:40-100`).
  Every pre-register-allocation stage is an in-place SSA-to-SSA refinement on
  `AnMachineLang` (`Compiles AnMachineLang AnMachineLang machineIdCodec`).
2. **Retain explicit SSA flag virtual registers (`vflag : VReg` in `.flag`
  register bank) on selected target instructions throughout `MachineSSA`,
  lowering them to physical `NZCV`/`EFLAGS` only at `RegAlloc`.** Empirical
  inspection of `llc -O2 -global-isel -print-after-all` on 128-bit addition
  (`add i128` in `support/backend_probe.ll`) reveals an asymmetry in upstream
  LLVM 21.1.8: `Legalizer` lowers `G_ADD s128` into `G_UADDO` and `G_UADDE`
  using an explicit SSA carry virtual register (`%15:_(s1)` on `x86_64`,
  `%19:_(s1)` on `aarch64`), making `Legalizer` and
  `LegalizationArtifactCombiner` pure SSA dataflow rewrites. However, upstream
  `InstructionSelect` immediately discards that SSA carry virtual register in
  favor of `implicit-def $nzcv` / `implicit $nzcv` (AArch64 `ADDSXrr`/`ADCXrr`)
  or `implicit-def $eflags` / `implicit $eflags` (`x86_64` `ADD64rr`/`ADC64rr`).
  On `x86_64`, because `EFLAGS` cannot be copied directly, upstream LLVM must
  run a complex fixup pass (`X86FlagsCopyLoweringPass`) that pattern-matches
  live physical flag ranges across control flow and rewrites `COPY` of `EFLAGS`
  into `SETB`/`ADD8ri` sequences. Keeping explicit SSA flag virtual registers on
  selected `TargetOpcode`s (`ADD64_FLAGS`, `ADDC64_FLAGS`, `CMP64_FLAGS`,
  `CSEL64`) until `RegAlloc`—and verifying physical `NZCV`/`EFLAGS` liveness in
  the `PostRA` certificate checker—eliminates `X86FlagsCopyLoweringPass` from
  the trusted computing base and catches flag-clobbering bugs such as
  intervening `xor r7d, r7d` (`MOV32r0`) between `ADD64` and `ADC64`.
3. **Partition the backend between verified constructive `PassCompiler`s and a
  verified symbolic `CertChecker` (`BB-8`) at the `RegAlloc` boundary.**
  Following CompCert (`Allocation.v` / `IRC.v`) and CakeML (`reg_alloc`),
  graph-coloring (`RAGreedy`), live-range splitting, spill-weight heuristics,
  and register coalescing (`RegisterCoalescer`) should never be verified as
  constructive algorithms inside the Lean kernel. Instead:
   - Stages 1–3 (`IRTranslator`, `Legalizer` + `LegalizationArtifactCombiner` +
     `RegBankSelect`, and `InstructionSelect`) and Stage 5
     (`PrologEpilogInserter` + `eliminateFrameIndex` + `MCCodeEmitter`) are
     verified as constructive `PassCompiler`s (`compiles_of_eval_eq`).
   - Stage 4 (`RegAlloc` + `Spiller` + `VirtRegRewriter` + `LiveDebugValues`)
     runs as an untrusted oracle (`M → Option PostRaMachineProg`) gated by a
     verified boolean symbolic equivalence checker `checkPostRaMachine` packaged
     as a `BB-8` `CertChecker` (`regAllocCertChecker.toPassCompiler`).
4. **End-to-End 10-Pass, 6-IR Vertical Pipeline Composition.** In
  `support/support_end_to_end_mir_anllvm_isa_pipeline_probe.lean`, we compose
  all ten compiler passes across six distinct intermediate representations
  (`PreDropMirLang -> MirLang -> AnLlvmLang -> AnMachineLang ->
  PostRaMachineLang -> FramedIsaLang`) into a single verified
  `fullEndToEndCompiler` (`fullEndToEndCompiler_verified`), showing that
  `Codec.comp`, `PassCompiler.comp`, and `CertChecker.toPassCompiler` bridge
  every representation boundary without custom glue logic.
5. **Stage-1 `.olean` Pre-Verification Scaling and `maxRecDepth` Thresholds.**
  Benchmarking per-function `rfl` proof reduction on pre-verified boolean
  equivalence checkers across `N = 25, 50, 100, 200` chained instructions in
  Lean 4.34.1 shows that Stage-1 `.olean` theorems (`checkScalePeephole_sound`)
  keep per-function Stage-2 tactics constant (`exact checkScalePeephole_sound _
  _ rfl`), while exposing that unary `Nat` kernel evaluation hits Lean 4's
  default `maxRecDepth = 4096` between `N = 100` and `N = 200` unless
  fixed-width `UInt64`/`BitVec 64` words or an elevated recursion bound
  (`set_option maxRecDepth 20000`) are used.

---

## 2. Primary-Source Architectural Comparison: `SelectionDAG` vs. `GlobalISel`

### 2.1 Why `SelectionDAGISel` Is Hostile to Formal Verification

Inspection of `/usr/include/llvm-21/llvm/CodeGen/SelectionDAGISel.h`,
`SelectionDAG.h`, and `SelectionDAGNodes.h` exposes five structural mismatches
between `SelectionDAG` and mechanized verification in Lean 4:

1. **Out-of-SSA Basic-Block Graph Translation (`SelectionDAGBuilder`):**
  `SelectionDAGISel` lowers one `BasicBlock` at a time into a directed acyclic
  graph (`SelectionDAG`) of `SDNode`s (`SelectionDAGNodes.h:475-620`). Values
  crossing basic-block boundaries must be exported to virtual registers via
  `CopyToReg` and re-imported via `CopyFromReg` (`ISD::CopyToReg`,
  `ISD::CopyFromReg`, `ISDOpcodes.h:204-215`). Defining a formal operational
  semantics for `SelectionDAG` requires maintaining two simultaneous evaluation
  models: an inter-block SSA `MachineFunction` environment and an intra-block
  partially ordered dataflow/token graph.
2. **Untyped `MVT::Other` Control/Memory Chains (`EntryToken`, `TokenFactor`):**
  Because `SelectionDAG` has no program counter or linear instruction order
  within a basic block, memory loads, stores, calls, and volatile operations
  must be explicitly serialized using `MVT::Other` chain operands
  (`SelectionDAGNodes.h:158-190`). Any legalization or DAG-combine rule that
  drops or miswires a chain edge silently reorders memory effects without a type
  error.
3. **Rigid `MVT::Glue` Scheduling Edges (`SDValue` Glue):** As documented in
  `SelectionDAGNodes.h:192-218`, flag-producing instructions (such as
  `ISD::ADDC`/`ISD::ADDE` or `X86ISD::CMP`) are coupled to their consumers via
  `MVT::Glue` operands, which force two `SDNode`s to be scheduled contiguously
  as a single scheduling unit (`ScheduleDAGSDNodes`). `MVT::Glue` cannot be
  spilled, copied, or live across basic blocks, requiring ad-hoc custom
  inserters (`EmitInstrWithCustomInserter`).
4. **Interleaved Mutating Phases (`DAGCombiner` + `SelectionDAGLegalize`):** In
  `SelectionDAGISel::CodeGenAndEmitDAG()`, `DAGCombiner` runs repeatedly before
  and after type legalization (`LegalizeTypes`), vector legalization
  (`LegalizeVectors`), and operation legalization (`LegalizeOp`), mutating the
  `SelectionDAG` in-place via hash-consing (`ContextualFoldingSet`) and morphing
  node opcodes.
5. **Non-Deterministic Schedule Linearization (`ScheduleDAGSDNodes`):** After
  `Select()` maps `ISD::*` nodes to target `MachineSDNode`s, `ScheduleDAGRRList`
  / `ScheduleDAGFast` linearizes the DAG back into a linear `MachineBasicBlock`
  sequence, requiring a separate graph-to-trace refinement proof.

### 2.2 Why `GlobalISel` (`AnMachineIR`) Fits Anneal's `BB-8` Architecture

Inspection of `/usr/include/llvm-21/llvm/CodeGen/GlobalISel/` and
`/usr/include/llvm-21/llvm/CodeGen/MachineFunction.h` shows that `GlobalISel`
eliminates every one of `SelectionDAG`'s representational impedance mismatches:

| Architectural Dimension | `SelectionDAG` (`SelectionDAGISel.h`) | `GlobalISel` (`GlobalISel/` & `AnMachineIR`) |
| :--- | :--- | :--- |
| **Core Program Representation** | Per-block `SelectionDAG` (`SDNode` / `SDValue`) separate from `MachineFunction` | Single unified `MachineFunction` (`MachineBasicBlock` + `MachineInstr`) from `IRTranslator` through `MC` |
| **Control & Memory Ordering** | Implicit partial order via `MVT::Other` chain edges (`EntryToken`, `TokenFactor`) | Explicit sequential instruction list per `MachineBasicBlock` (deterministic small-step trace) |
| **Type System** | `MVT` / `EVT` (`MachineValueType.h`) mixed with `MVT::Other` and `MVT::Glue` | `LowLevelType` (`LLT`, `LowLevelType.h:40-100`): orthogonal `.sN`, `.p0`, and `.vN` |
| **Phase Progression** | Interleaved `DAGCombiner` + `LegalizeTypes` + `LegalizeOp` + `ScheduleDAG` | Monotonic `MachineFunctionProperties` lattice (`IsSSA -> Legalized -> RegBankSelected -> Selected -> NoVRegs`) |
| **Artifact Cleanup** | Arbitrary graph rewrites in `DAGCombiner` | Local algebraic equations on `G_MERGE_VALUES` / `G_UNMERGE_VALUES` / `G_ZEXT` / `G_TRUNC` (`LegalizationArtifactCombiner.h`) |
| **Instruction Selection** | C++ `SelectionDAGISel::Select` + TableGen DAG bytecode | Linear bytecode state machine (`GIMatchTableExecutor.h`) rewriting `G_*` to `TargetOpcode` in-place |

Look at `MachineFunctionProperties::Property` in
`/usr/include/llvm-21/llvm/CodeGen/MachineFunction.h:187-201`:

```cpp
enum class Property : unsigned {
  IsSSA,
  NoPHIs,
  TracksLiveness,
  NoVRegs,
  FailedISel,
  Legalized,
  RegBankSelected,
  Selected,
  TiedOpsRewritten,
  FailsVerification,
  LastProperty = FailsVerification,
};
```

In Anneal's `BB-8` vocabulary, because `IRTranslator`, `Legalizer`,
`RegBankSelect`, and `InstructionSelect` all operate on the exact same
`AnMachineLang` (`MachineFunction`) type and semantics, each stage is an
in-place refinement `Compiles AnMachineLang AnMachineLang machineIdCodec mf
(pass mf)` whose well-formedness postcondition is recorded in
`MachineFunctionProperties` (`isSSA`, `legalized`, `regBankSelected`,
`selected`).

---

## 3. Empirical `llc` 21.1.8 Pipeline and `MachineIR` Findings Across `x86_64`, `aarch64`, and `riscv64`

We ran `llc` 21.1.8 (`/usr/bin/llc-21`) on `support/backend_probe.ll`
(containing `@add_u128_and_u8` and `@gep_load_select`) across
`x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` under both
`-global-isel=0` (`SelectionDAG`) and `-global-isel=1` (`GlobalISel`)
(`support/passes_gisel_aarch64-unknown-linux-gnu.txt`,
`support/passes_sdag_aarch64-unknown-linux-gnu.txt`,
`support/passes_gisel_x86_64-unknown-linux-gnu.txt`,
`support/passes_sdag_x86_64-unknown-linux-gnu.txt`, and the corresponding `.s`
outputs).

### 3.1 Empirical Pass-Pipeline Comparison (`-debug-pass=Structure`)

| Target & Mode | Pre-ISel IR Passes | ISel Lowering Stage(s) | Post-ISel MachineSSA Opts | RegAlloc & Coalescing Passes | Post-RA & Frame/MC Passes |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`aarch64` (`SelectionDAG`)** | 25 passes (`PreISelIntrinsicLowering` .. `ExpandIrreducible`) | 1 monolithic `AArch64 Instruction Selection` (`SelectionDAGISel`) | 21 passes (`EarlyIfConverter`, `MachineLICM`, `MachineCSE`, `PeepholeOptimizer`, ...) | 18 passes (`DetectDeadLanes`, `RegisterCoalescer`, `RAGreedy`, `VirtRegRewriter`) | 28 passes (`ShrinkWrap`, `PrologEpilogInserter`, `BranchFolder`, `AArch64AsmPrinter`) |
| **`aarch64` (`GlobalISel`)** | 25 passes | **6 modular passes**: `IRTranslator`, `AArch64PreLegalizerCombiner`, `Legalizer`, `AArch64PostLegalizerCombiner`, `RegBankSelect`, `InstructionSelect` | 21 passes | 18 passes | 28 passes |
| **`x86_64` (`SelectionDAG`)** | 26 passes | 1 monolithic `X86 DAG->DAG Instruction Selection` + **`X86FlagsCopyLoweringPass`** | 19 passes | 17 passes | 29 passes |
| **`x86_64` (`GlobalISel`)** | 26 passes | **4 modular passes**: `IRTranslator`, `Legalizer`, `RegBankSelect`, `InstructionSelect` + `X86FlagsCopyLoweringPass` | 19 passes | 17 passes | 29 passes |

### 3.2 Stage-by-Stage `GlobalISel` MIR Progression on `@add_u128_and_u8` (`aarch64` & `x86_64`)

Examining the `GlobalISel` stages on `@add_u128_and_u8` reveals how `LLT` types,
artifact combining, and carry flags behave in practice:

1. **Stage 1 (`IRTranslator`):** Lowers ABI register pairs `$x0, $x1` (`$rdi,
  $rsi` on `x86_64`) into 64-bit virtual registers and packs them via
  `G_MERGE_VALUES`:
   ```llvm
   %4:_(s64) = COPY $x0
   %5:_(s64) = COPY $x1
   %0:_(s128) = G_MERGE_VALUES %4(s64), %5(s64)
   %6:_(s64) = COPY $x2
   %7:_(s64) = COPY $x3
   %1:_(s128) = G_MERGE_VALUES %6(s64), %7(s64)
   %8:_(s32) = COPY $w4
   %2:_(s8) = G_TRUNC %8(s32)
   %9:_(s32) = COPY $w5
   %3:_(s8) = G_TRUNC %9(s32)
   %10:_(s128) = G_ADD %0, %1
   %11:_(s8) = G_ADD %2, %3
   %12:_(s64) = G_ZEXT %11(s8)
   %13:_(s128) = G_ZEXT %12(s64)
   %14:_(s128) = G_ADD %10, %13
   ```
2. **Stage 2 (`Legalizer` + `LegalizationArtifactCombiner`):**
  `LegalizerHelper::narrowScalar` decomposes `%10:_(s128) = G_ADD %0, %1` into
  `G_UNMERGE_VALUES` + `G_UADDO` + `G_UADDE` + `G_MERGE_VALUES`, and
  `LegalizationArtifactCombiner::tryCombineUnmergeValues`
  (`/usr/include/llvm-21/llvm/CodeGen/GlobalISel/LegalizationArtifactCombiner.h:1064-1270`)
  immediately cancels every `G_UNMERGE_VALUES` against its producer
  `G_MERGE_VALUES`, leaving zero `s128` virtual registers and an explicit SSA
  carry virtual register `%19:_(s1)`:
   ```llvm
   %18:_(s64), %19:_(s1) = G_UADDO %4, %6
   %20:_(s64), %21:_(s1) = G_UADDE %5, %7, %19
   %29:_(s32) = G_ADD %8, %9
   %31:_(s64) = G_ZEXT %29(s32)
   %12:_(s64) = G_AND %31, %30        ; %30 = G_CONSTANT i64 255
   %22:_(s64) = G_CONSTANT i64 0
   %25:_(s64), %26:_(s1) = G_UADDO %18, %12
   %27:_(s64), %28:_(s1) = G_UADDE %20, %22, %26
   ```
   The exact same SSA `G_UADDO` / `G_UADDE` representation is produced on
   `x86_64`:
   ```llvm
   %14:_(s64), %15:_(s1) = G_UADDO %4, %6
   %16:_(s64), %17:_(s1) = G_UADDE %5, %7, %15
   ```
3. **Stage 3 (`RegBankSelect`):** Annotates every virtual register with its
  register bank (`:gpr(s64)`, `:gpr(s1)`).
4. **Stage 4 (`InstructionSelect` — The Upstream Implicit-Flag Hazard):** In
  upstream LLVM 21.1.8, `InstructionSelect` discards the explicit SSA carry
  virtual registers `%19:gpr(s1)` and `%26:gpr(s1)` and replaces them with
  implicit physical condition-code register side effects:
   - On `aarch64`:
     ```llvm
     %18:gpr64 = ADDSXrr %4, %6, implicit-def $nzcv
     %20:gpr64 = ADCXrr %5, %7, implicit $nzcv
     ```
   - On `x86_64`:
     ```llvm
     %14:gr64 = ADD64rr %4, %6, implicit-def $eflags
     %16:gr64 = ADC64rr %5, %7, implicit-def dead $eflags, implicit $eflags
     ```
   Furthermore, on `x86_64`, `G_CONSTANT i64 0` is selected to `%23:gr32 =
   MOV32r0 implicit-def dead $eflags` (`xor eax, eax`), which clobbers
   `$eflags`. If `MOV32r0` is scheduled or rematerialized between `ADD64rr` and
   `ADC64rr`, it silently destroys the carry flag in `$eflags`.

---

## 4. `llc` Pass Classification and Adaptation Matrix for `AnMachineIR`

Every pass in `llc`'s backend pipeline falls into one of three categories in
Anneal's architecture:

### 4.1 Category A — Verify Directly as Constructive `PassCompiler`s (`compiles_of_eval_eq`)

| Pass / Component | Source -> Target IR | Verification Strategy in Anneal |
| :--- | :--- | :--- |
| **`IRTranslator`** (`GlobalISel/IRTranslator.h`) | `AnLlvmLang -> AnMachineLang` | Constructive 1-to-N instruction translation; ABI arguments lowered to explicit `COPY_FROM_ABI_GPR` + `G_MERGE_VALUES`; `gep inbounds` lowered to `G_MUL_IMM` + `G_PTR_ADD`. Verified by `irTranslator_*_compiles`. |
| **`LegalizerHelper`** (`GlobalISel/LegalizerHelper.h`) | `AnMachineLang -> AnMachineLang` | Constructive local rewrite rules: `narrowScalar` on `s128` (`G_UADDO` + `G_UADDE`), `widenScalar` on `s8`/`s16` (`G_TRUNC64_TO_8` + `G_ZEXT8_TO_64`), and strength reduction (`G_MUL_IMM 8 -> G_SHL_IMM 3`). |
| **`LegalizationArtifactCombiner`** (`GlobalISel/LegalizationArtifactCombiner.h`) | `AnMachineLang -> AnMachineLang` | Constructive symbolic environment (`merges`, `subst`) folding `G_UNMERGE_VALUES` against `G_MERGE_VALUES` (`legalizer_*_compiles`). |
| **`RegBankSelect`** (`GlobalISel/RegBankSelect.h`) | `AnMachineLang -> AnMachineLang` | Constructive type-directed bank assignment (`.gpr` for integers/pointers, `.flag` for `s1` carry/condition virtual registers); semantics-preserving annotation (`machineIdCodec`). |
| **`InstructionSelect`** (`GlobalISel/GIMatchTableExecutor.h`) | `AnMachineLang -> AnMachineLang` | Constructive structural pattern matcher (`selectBodyAux`) rewriting `G_*` to `TargetOpcode`s (`ADD_SHIFTED_PTR`, `ADD64_FLAGS`, `ADDC64_FLAGS`, `CMP64_FLAGS`, `CSEL64`) while preserving explicit SSA flag virtual registers (`instructionSelect_compiles`). |
| **`PrologEpilogInserter` + `eliminateFrameIndex` + `MCCodeEmitter`** | `PostRaMachineLang -> FramedIsaLang` | Constructive pass (`prologEpilogAndMcEncode`) wrapping the body in balanced `[ISA_SUB_SP k]` / `[ISA_ADD_SP k]` and lowering `SPILL_STORE`/`SPILL_RELOAD` to `ISA_STR_SP`/`ISA_LDR_SP`. Universally verified for all programs by `prologEpilogAndMcEncode_compiles`. |

### 4.2 Category B — Gate Untrusted Heuristics via `BB-8` `CertChecker.toPassCompiler`

| Pass / Component | Source -> Target IR | Verification Strategy in Anneal |
| :--- | :--- | :--- |
| **`RegisterCoalescer` + `RAGreedy` + `InlineSpiller` + `VirtRegRewriter`** | `AnMachineLang -> PostRaMachineLang` | Untrusted external oracle (`untrustedRegAllocOracle`) validated at compile time by the kernel-verified boolean symbolic checker `checkPostRaMachine` (`checkPostRaMachine_sound`, universally proved for all `mf` and `post`). Tracks `physToVReg : PhysReg → Option VReg`, `spillToVReg : SpillSlot → Option VReg`, and `flagVReg : Option VReg`. |
| **Post-ISel Peephole / MachineCSE / MachineScheduler (Optional)** | `AnMachineLang -> AnMachineLang` | Either omitted at initial verification tier or gated by an SSA symbolic block-simulation `CertChecker`. |

### 4.3 Category C — Omit or Replace by Design

| Upstream LLVM Pass | Why It Exists in Upstream `llc` | Disposition in Anneal |
| :--- | :--- | :--- |
| **`SelectionDAGISel`** | Legacy basic-block DAG instruction selector | **Omit completely.** Replaced by `GlobalISel` (`AnMachineIR`). |
| **`X86FlagsCopyLoweringPass`** | Rewrites `COPY` of physical `$eflags` introduced when `InstructionSelect` prematurely lowers `s1` virtual registers to `implicit-def $eflags` | **Omit completely.** `AnMachineIR` retains explicit SSA flag virtual registers (`vflag : VReg`) through `MachineSSA` until `RegAlloc`, where `checkPostRaMachine` verifies non-clobbering of physical `EFLAGS`/`NZCV`. |
| **`PHIElimination` + `TwoAddressInstructionPass` (as separate mutating passes)** | Mutates `MachineFunction` out-of-SSA before `RAGreedy` | **Fold into the `MachineSSA -> PostRA` translation-validation boundary.** `checkPostRaMachine` validates the post-allocation physical code (including two-address `MOV_REG` copies and phi moves) directly against the `MachineSSA` source. |
| **`ShrinkWrap`, `ImplicitNullChecks`, `MachineOutliner`, `TailDuplication`** | Speculative/code-size heuristics that alter frame layout or trap behavior | **Omit from the verified pipeline.** Standard `PrologEpilogInserter` handles deterministic entry/exit stack framing (`prologEpilogAndMcEncode`). |

---

## 5. Three `AnMachineIR` Semantic Cleanups Over Upstream LLVM `MachineInstr`

Our mechanization in `support/support_anllvm_globalisel_backend_probe.lean`
demonstrates that three small, principled cleanups to upstream LLVM's
`MachineInstr` simplify backend proofs without sacrificing generated code
quality:

1. **Cleanup 1: Explicit SSA Flag Virtual Registers on `TargetOpcode`s Until
  `RegAlloc`.** In `AnMachineInstr`, selected target instructions such as
  `ADD64_FLAGS (dst vflagOut lhs rhs : VReg)`, `ADDC64_FLAGS (dst vflagOut lhs
  rhs vflagIn : VReg)`, `CMP64_FLAGS (vflagOut : VReg) (pred : IntPred) (lhs rhs
  : VReg)`, and `CSEL64 (dst vflagIn tVal fVal : VReg)` carry explicit SSA
  `VReg` operands for condition codes instead of hidden `implicit-def $nzcv` /
  `$eflags` operands. Consequently:
   - `AnMachineLang` has a uniform SSA environment semantics (`env : VRegEnv`)
     with zero architectural flag state prior to `RegAlloc`.
   - Physical flag clobbering (`physFlag : Option Bool`) only enters the
     semantics in `PostRaMachineLang`, where `checkPostRaMachine` tracks
     `sym.flagVReg : Option VReg` and proves that any instruction that clobbers
     flags (such as `XOR_ZERO_CLOBBER` / `MOV32r0`) invalidates `sym.flagVReg :=
     none`.
2. **Cleanup 2: Preserving `LowLevelType` (`LLT`) Tags Across `AnMachineIR`.**
  Every `MVal` in `AnMachineLang` is tagged with its width/pointer sort (`.v1`,
  `.v8`, `.v32`, `.v64`, `.v128`, `.ptr`), matching `llvm::LLT`
  (`/usr/include/llvm-21/llvm/CodeGen/LowLevelType.h:40-100`). Narrow 8-bit
  arithmetic (`ADD8_MASK`) and explicit zero-extension (`ZEXT8_TO_64`) are
  checked at the type level rather than relying on untyped 32-bit subregister
  aliases (`$al` vs. `$eax` vs. `$w8`).
3. **Cleanup 3: Type-Separated `PostRaMachineProg` vs. `FramedIsaProg`.**
  Upstream LLVM reuses the single mutable `MachineFunction` container across
  pre-RA SSA, post-RA abstract stack slots (`MO_FrameIndex`), and post-PEI
  concrete SP offsets. Separating `AnMachineLang` (SSA `VReg`s),
  `PostRaMachineLang` (physical `PhysReg`s + abstract `SpillSlot`s), and
  `FramedIsaLang` (concrete `ISA_SUB_SP` / `ISA_ADD_SP` / `ISA_STR_SP` /
  `ISA_LDR_SP` + exit stack-balance check `st.spOffset = 0`) turns
  `MachineFunctionProperties` into static Lean types and allows
  `PassCompiler.comp` (`BB-8`) to compose their refinement proofs cleanly.

---

## 6. End-to-End 10-Pass, 6-IR Vertical Pipeline Composition and Kernel Scaling

To prove that the MIR front-end, `AnLLVM` middle-end, and `GlobalISel` backend
designs compose without representational mismatches, we built
`support/support_end_to_end_mir_anllvm_isa_pipeline_probe.lean` (1,771 lines).

### 6.1 The 6 Intermediate Representations and 10 Composed Passes

The end-to-end probe defines six `DetLanguage` instances sharing a common
`KernelInput` / `KernelOutput` boundary (`Codec.id`):

1. **`PreDropMirLang`**: Pre-drop-elaboration Rust MIR with abstract Aggregate /
  `Adt` values, `DropIfLive` conditional drop terminators, and explicit
  `StorageLive`/`StorageDead` slot sets.
2. **`MirLang`**: Post-`ElaborateDrops` runtime MIR with explicit drop-flag
  control flow (`Pass 1: elaborateDropsPass`).
3. **`AnLlvmLang`**: Clean-slate `AnLLVM-IR` with explicit allocation-epoch
  memory, `StorageLive` lifetime intervals, and SSA register map.
   - `Pass 2: destPropMirPass` (Category M2 `DestinationPropagation` with
     unioned `StorageLive` intervals).
   - `Pass 3: mirToAnLlvmPass` (`rustc_codegen_ssa` single-pass RPO lowering).
   - `Pass 4: sroaMem2RegPass` (Mode B `SROA + Mem2Reg` gated by
     `sroaMem2RegCertChecker`).
   - `Pass 5: instCombinePass` (Mode A constructive algebraic rewrite).
   - `Pass 6: dsePass` (Mode B `MemorySSA` dead-store elimination gated by
     `dseCertChecker`).
4. **`AnMachineLang`**: `GlobalISel` SSA `MachineIR` with explicit `vflag :
  VReg` virtual flag registers.
   - `Pass 7: irTranslatorLegalizePass` (`AnLlvmLang -> AnMachineLang`).
   - `Pass 8: instructionSelectPass` (`AnMachineLang -> AnMachineLang`).
5. **`PostRaMachineLang`**: Post-register-allocation physical-register machine
  code with abstract spill slots and physical `physFlag : Option Bool`.
   - `Pass 9: regAllocPass` (`AnMachineLang -> PostRaMachineLang`, gated by
     `regAllocCertChecker`).
6. **`FramedIsaLang`**: Target ISA assembly with explicit `ISA_SUB_SP` /
  `ISA_ADD_SP` stack-pointer arithmetic and exit stack-balance verification.
   - `Pass 10: prologEpilogMcPass` (`PostRaMachineLang -> FramedIsaLang`).

All ten passes compose into a single verified `PassCompiler` via
`PassCompiler.comp`:

```lean
def fullEndToEndCompiler : PassCompiler PreDropMirLang FramedIsaLang Codec.id :=
  elaborateDropsCompiler.comp
    (destPropMirCompiler.comp
      (mirToAnLlvmCompiler.comp
        (sroaMem2RegCompiler.comp
          (instCombineCompiler.comp
            (dseCompiler.comp
              (irTranslatorLegalizeCompiler.comp
                (instructionSelectCompiler.comp
                  (regAllocCompiler.comp prologEpilogMcCompiler))))))))
```

Theorem `fullEndToEndCompiler_verified` proves that compiling
`sourcePreDropMirProg` through all ten passes yields ` some targetFramedIsaProg`
and satisfies `Compiles PreDropMirLang FramedIsaLang Codec.id
sourcePreDropMirProg targetFramedIsaProg`.

### 6.2 Four Cross-Stage Negative Seam Canaries

Section 10 of `support/support_end_to_end_mir_anllvm_isa_pipeline_probe.lean`
mechanizes four negative canaries at the most bug-prone cross-stage seams:

1. **`canary_destProp_missing_live_union_rejected` (MIR `DestinationPropagation`
  $\to$ `SROA` Seam, `rust-lang/rust#146383`):** Proves that if
  `DestinationPropagation` merges `src` into `dst` without unioning `src`'s
  `StorageLive` range into `dst`, reading `dst` outside its original
  `StorageLive` window returns `none` (rejected by `checkDestPropMir`).
2. **`canary_dse_live_store_before_load_rejected` (`AnLLVM` `MemorySSA` `DSE`
  Seam):** Proves that `checkDseAnLlvm` rejects (`= false`) any candidate
  program that deletes a `store` before an intervening `load` of the same
  `AllocId`.
3. **`canary_flag_clobber_across_regalloc_rejected` (`GlobalISel` $\to$
  `RegAlloc` Flag Seam):** Proves that `checkPostRaMachine` rejects (`= false`)
  a post-RA schedule that inserts `PR_XOR_ZERO_CLOBBER` (`xor r3d, r3d`) between
  `PR_UADDO64_SET_CF` and `PR_UADDE64_USE_CF`.
4. **`canary_pei_unbalanced_sp_rejected` (`PrologEpilogInserter` $\to$ `ISA`
  Frame Seam):** Proves that `evalFramedIsa` returns `none` whenever
  `ISA_SUB_SP` and `ISA_ADD_SP` fail to restore `spOffset = 0` at `ISA_RET`.

### 6.3 Stage-1 vs. Stage-2 `.olean` Scaling (`scale25`, `scale50`, `scale100`, `scale200`)

Section 11 of `support/support_end_to_end_mir_anllvm_isa_pipeline_probe.lean`
benchmarks the per-function Stage-2 proof tactic:

```lean
exact checkScalePeephole_sound (mkScaleSource N) (mkScaleTarget N) rfl
```

across `N = 25, 50, 100, 200` instructions (`scale25_peephole_verified`,
`scale50_peephole_verified`, `scale100_peephole_verified`,
`scale200_peephole_verified`). Because `checkScalePeephole_sound` is proved once
in Stage 1 (`theory/`) and imported from `.olean`, the Stage-2 proof script size
is $O(1)$ regardless of $N$. However, at $N = 200$, kernel reduction of unary
`Nat` addition inside `rfl` exceeds Lean 4.34.1's default `maxRecDepth = 4096`
and requires `set_option maxRecDepth 20000`. In production `AnLLVM`,
`MaskedWord64` operations should therefore wrap `UInt64` / `BitVec 64` rather
than unary `Nat` modulo arithmetic so kernel `rfl` reduction remains well below
`maxRecDepth` even on multi-hundred-instruction basic blocks.

---

## 7. Mechanized Lean 4.34.1 Probe Summary

| File | Lines | Key Universal Theorems & Canaries | Axiom Footprint (`#print axioms`) |
| :--- | ---: | :--- | :--- |
| `support/support_anllvm_globalisel_backend_probe.lean` | 3,547 | `irTranslator_addU128AndU8_compiles`, `legalizer_s128_and_s8_compiles`, `instructionSelect_compiles`, `checkPostRaMachine_sound`, `prologEpilogAndMcEncode_compiles`, `anllvmBackendPipeline_verified`, `canary_intervening_flag_clobber_between_uaddo_and_uadde_rejected`, `canary_unbalanced_stack_frame_rejected` | `[propext]` / `[propext, Quot.sound]` |
| `support/support_end_to_end_mir_anllvm_isa_pipeline_probe.lean` | 1,771 | `fullEndToEndCompiler_verified`, `checkScalePeephole_sound`, `scale25_peephole_verified` .. `scale200_peephole_verified`, `canary_destProp_missing_live_union_rejected`, `canary_dse_live_store_before_load_rejected`, `canary_flag_clobber_across_regalloc_rejected`, `canary_pei_unbalanced_sp_rejected` | `[propext]` / `[propext, Quot.sound]` |
