# Reusing LLVM 23.1.1 TableGen Data for Verified Instruction Selection, Binary Encoding, Scheduling, and Drop-In Target Queries

## Summary

LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) maintains `202,383` LOC of declarative TableGen (`.td`) machine descriptions across x86 (`89,325` LOC in `llvm/lib/Target/X86/*.td`) and AArch64 (`113,058` LOC in `llvm/lib/Target/AArch64/*.td`), plus `59,406` LOC for RISC-V (`llvm/lib/Target/RISCV/*.td`). Running `llvm-tblgen --dump-json` (`llvm/lib/TableGen/JSONBackend.cpp`, `180` LOC) evaluates all TableGen multiclasses, `foreach` loops, bit-slice assignments, and DAG expressions into a single canonical JSON object (`160.5` MB / `85,558` records for X86; `100.0` MB / `82,807` records for AArch64; `263.8` MB / `245,043` records for RISC-V; `support/tblgen_summary.json`):

1. **Directly Reusable Non-TCB / Drop-In CLI Tables (Zero Soundness Risk or Trivially Validated)**:
   - **CPU Definitions (`Processor` / `ProcessorModel`: `136` on X86, `84` on AArch64, `59` on RISC-V) and Subtarget Features (`SubtargetFeature`: `231` on X86, `356` on AArch64, `379` on RISC-V)**: `rustc`'s `--print target-cpus` (`LLVMRustPrintTargetCPUs`, `PassWrapper.cpp:281-300`), `--print target-features` (`LLVMRustGetTargetFeature`, lines 302-334), and `-C target-cpu` / `-C target-feature` implication closure (`MCSubtargetInfo::checkFeatures`) read directly from the TableGen-generated `SubtargetSubTypeKV` and `SubtargetFeatureKV` tables. Importing `support/x86_tablegen_catalog.json` and `support/aarch64_tablegen_catalog.json` gives a clean-slate Rust compiler 100% drop-in CLI compatibility with `rustc` `1.99.1` without hand-maintaining CPU names or feature implication DAGs.
   - **Per-CPU Scheduling Models (`SchedMachineModel`: `23` on X86, `31` on AArch64; `SchedReadWrite`: `3,797` on X86, `4,448` on AArch64)**: Latency, micro-op count, and hardware port resource tables (`ProcResource`: `252` on X86, `438` on AArch64) affect only instruction ordering heuristics (`MachineScheduler`), never semantics.

2. **Schema-Extractable Structural Tables Requiring Validation Against Authoritative ISA Specs (Sail / ASL / Intel SDM)**:
   - **Registers and Register Classes (`Register`: `383` X86, `522` AArch64; `RegisterClass`: `86` X86, `83` AArch64; `RegisterBank`: `3` each)**: Contains DWARF register numbers (`DwarfNumbers`), hardware encoding indices (`HWEncoding`), subregister indices (`SubRegIndices`), lane masks, spill sizes/alignments, and allocation orders.
   - **Calling Conventions (`CallingConv`: `53` X86, `16` AArch64; `CCAction`: `442` X86, `190` AArch64)**: Declarative `CCIfType`, `CCAssignToReg`, `CCAssignToStack`, and `CalleeSavedRegs` rules.
   - **Instructions and Binary Encodings (`Instruction`: `22,373` X86, `9,196` AArch64)**:
     - On **AArch64**, non-pseudo, non-codegen-only instructions (`5,787` encodable instructions) specify their complete 32-bit fixed-width binary encoding directly in `Inst{31-0}` bit-field arrays inside `--dump-json` (merging constant bits and operand bit-slices). These bit-level templates can be cross-validated 1-to-1 against the official Arm Architecture Specification Language (ASL) / `sail-arm` instruction encodings!
     - On **X86**, `19,807` encodable instructions do **not** store raw machine bytes in `Inst{...}`; instead they store declarative format flags (`FormBits`, `OpPrefix`, `OpMap`, `REX_W`, `VEX`, `EVEX`, `EVEX_CD8`, `ModRM`) interpreted by `X86MCCodeEmitter.cpp`.
   - **Selection Patterns (`Pattern` / `Pat`: `5,658` standalone + `19,009` inline on X86; `12,232` standalone + `2,118` inline on AArch64; `GINodeEquiv`: `203` X86, `239` AArch64)**:
     - Express tree-rewriting rules from `SelectionDAG` (`SDNode`: `790` X86, `691` AArch64) to target `Instruction`s. However, `12` `ComplexPattern`s on X86 and `175` `ComplexPattern`s on AArch64 (plus `106` X86 and `621` AArch64 instructions with `usesCustomInserter = 1`, and C++ predicates in `PatFrag`) invoke arbitrary C++ methods in `X86ISelDAGToDAG.cpp` / `AArch64ISelDAGToDAG.cpp` and cannot be extracted purely from JSON without translating their C++ predicates.

3. **Licensing**: All LLVM 23.1.1 `.td` files and `llvm-tblgen` outputs are licensed under `Apache-2.0 WITH LLVM-exception`, which is explicitly compatible with Anneal and `rustc`'s `Apache-2.0 OR MIT` / `BSD` licensing.

## Applicability

These findings apply to `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) and `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`). All record counts and schemas were obtained by executing `/usr/local/google/home/joshlf/workspace/rust/build/x86_64-unknown-linux-gnu/ci-llvm/bin/llvm-tblgen --dump-json` against `llvm/lib/Target/{X86,AArch64,RISCV}/*.td` (`support/tblgen_summary.json`).

## Findings

### 1. Quantitative Inventory of LLVM 23.1.1 TableGen (`--dump-json`) Across X86, AArch64, and RISC-V

**Basis: source + execution**

`llvm-tblgen --dump-json` (`llvm/lib/TableGen/JSONBackend.cpp:1-180`) serializes the evaluated `RecordKeeper` into a top-level JSON dictionary containing metadata keys (`!tablegen_json_version`, `!instanceof`) alongside one object per concrete `Record`:

| TableGen Metric / Record Class (`!instanceof`) | X86 (`X86.td`) | AArch64 (`AArch64.td`) | RISC-V (`RISCV.td`) | Primary Consumer & Role |
| :--- | ---: | ---: | ---: | :--- |
| **Source `.td` Files / Total `.td` LOC** | `58` files / `89,325` LOC | `53` files / `113,058` LOC | `68` files / `59,406` LOC | Declarative target description source in `llvm/lib/Target/<Arch>/`. |
| **`--dump-json` Output Size (Bytes)** | `160,466,389` (`153.0` MiB) | `99,977,353` (`95.3` MiB) | `263,771,593` (`251.6` MiB) | Complete evaluated JSON record graph. |
| **Total Concrete `def` Records** | `85,558` | `82,807` | `245,043` | All evaluated `Record` objects (RISC-V is largest due to RVV vtype/LMUL pseudos). |
| **Total TableGen Classes in `!instanceof`** | `1,481` | `2,137` | `2,056` | Superclass hierarchy index. |
| **`Instruction` (Total)** | `22,373` | `9,196` | `16,887` | All target instructions (`MCInstrDesc`). |
| — `isPseudo == 1` | `451` | `1,712` | `13,725` | Expanded before/after RA (`ExpandPostRAPseudos`). |
| — `isCodeGenOnly == 1` | `2,115` | `1,708` | `13,689` | Duplicate codegen variants (e.g., 32/64-bit register tie aliases). |
| — **Real Encodable Instructions (`!isPseudo && !isCodeGenOnly`)** | **`19,807`** | **`5,787`** | **`3,157`** | Hardware instructions with real assembler/disassembler binary encodings. |
| — Instructions with inline `Pattern` (`Pattern != []`) | `19,009` | `2,118` | `43` | Single-instruction SelectionDAG/GlobalISel selection rules. |
| **`Pattern` / `Pat` (Standalone DAG Patterns)** | `5,658` | `12,232` | `34,575` | Multi-node or type-specialized SelectionDAG/GlobalISel rewrite rules. |
| **`ComplexPattern` (C++ Matcher Hooks)** | `12` | `175` | `45` | Addressing-mode and immediate matchers implemented in C++. |
| **`SDNode` (SelectionDAG Operators)** | `790` | `691` | `650` | Target-independent (`ISD::*`) and target-specific (`X86ISD::*`, `AArch64ISD::*`) DAG nodes. |
| **`GINodeEquiv` & `GICombineRule` (GlobalISel)** | `203` / `279` | `239` / `327` | `222` / `0` | Mapping between `SelectionDAG` nodes and `GlobalISel` `G_*` generic opcodes & combiner rules. |
| **`Register` / `RegisterClass` / `RegisterBank`** | `383` / `86` / `3` | `522` / `83` / `3` | `399` / `84` / `3` | Physical registers, subregister indices, allocation classes, and GPR/FPR/Vec banks. |
| **`CallingConv` / `CCAction`** | `53` / `442` | `16` / `190` | `0` / `0` | Declarative ABI argument/return assignment state machines (RISC-V uses C++ `CC_RISCV`). |
| **`SubtargetFeature`** | `231` | `356` | `379` | Target feature flags (`+avx2`, `+neon`, `+sve2`) and `Implies` dependency edges. |
| **`Processor` / `ProcessorModel`** | `136` | `84` | `59` | Named CPU models (`skylake`, `icelake-server`, `apple-m4`, `neoverse-v2`) for `-C target-cpu`. |
| **`SchedMachineModel` / `SchedReadWrite` / `ProcResource`** | `23` / `3,797` / `252` | `31` / `4,448` / `438` | `24` / `6,643` / `202` | Per-microarchitecture pipeline latency and execution port tables. |
| **`Intrinsic` (`Intrinsics*.td`)** | `16,423` | `16,423` | `16,423` | Target-independent and target-specific `@llvm.*` intrinsic signatures and `MemoryEffects`. |

---

### 2. Detailed Schema and Semantics of TableGen Domains

**Basis: source + execution**

#### 2.1 Instructions, Implicit Operands, and Side-Effect Flags (`Instruction`)
Every record in `!instanceof["Instruction"]` inherits from `class Instruction` (`llvm/include/llvm/Target/Target.td:510-760`) and carries explicit operand DAGs, implicit register lists, and boolean behavioral flags (`support/tblgen_summary.json`):

| Field in `Instruction` JSON Record | X86 Count (`22,373` total) | AArch64 Count (`9,196` total) | Semantic Meaning and Verification Obligation |
| :--- | ---: | ---: | :--- |
| `OutOperandList` (`dag`) | `22,373` | `9,196` | Explicit defined register operands (`outs GR64:$dst`). |
| `InOperandList` (`dag`) | `22,373` | `9,196` | Explicit input register/immediate/memory operands (`ins GR64:$src1, i32imm:$src2`). |
| `Uses` (`list<Register>`) | `8,942` (`40.0%`) | `1,217` (`13.2%`) | **Implicit register reads** (e.g., `EFLAGS`/`NZCV`, `RSP`/`SP`, `MXCSR`, `X0`). Must be included in dataflow liveness and instruction semantics! |
| `Defs` (`list<Register>`) | `2,640` (`11.8%`) | `613` (`6.7%`) | **Implicit register clobbers** (e.g., X86 arithmetic clobbering `EFLAGS`; `CALL` clobbering caller-saved registers). |
| `Constraints` (`string`) | Tied operands | Tied operands | Two-address register tying (e.g. `"$src1 = $dst"` on X86 destructive 2-operand instructions, enforced by `TwoAddressInstructionPass`). |
| `mayLoad` / `mayStore` (`bit`) | `8,247` / `1,080` | `1,766` / `1,472` | Marks instructions that read or write memory; controls `MachineLICM`, `MachineCSE`, `MachineScheduler`, and `AArch64LoadStoreOptimizer`. |
| `hasSideEffects` (`bit`) | `138` | `564` | Marks instructions with unmodeled side effects (`unmodeledSideEffects`) that must never be speculated or DCE'd. |
| `isCommutable` (`bit`) | `3,827` | `85` | Permits `TwoAddressInstructionPass` and `MachineCSE` to swap the first two input operands. Requires commutativity proof ($\text{op}(a, b) = \text{op}(b, a)$ including flags!). |
| `isBranch` / `isTerminator` / `isReturn` / `isCall` / `isBarrier` | `43` / `89` / `47` / `58` / `71` | `65` / `91` / `24` / `30` / `35` | CFG control-flow classification flags consumed by `MachineBlockPlacement`, `BranchFolder`, and `ShrinkWrap`. |
| `usesCustomInserter` / `hasPostISelHook` | `106` / `0` | `621` / `10` | **Escape hatch to C++**: `EmitInstrWithCustomInserter` in `X86ISelLowering.cpp` / `AArch64ISelLowering.cpp` expands the pseudo-instruction into a multi-block `MachineBasicBlock` diamond at the end of ISel. |

#### 2.2 Binary Encodings (`Inst{31-0}` on AArch64 vs Format Descriptors on X86)
- **AArch64 (`AArch64InstrFormats.td`)**: Every real instruction record in `AArch64.td` (`5,787` records) contains `"Inst": [bit_0, bit_1, ..., bit_31]`, where each element is either an integer (`0` or `1`) for fixed opcode bits or a variable reference (`{"kind": "varbit", "var": "Rd", "index": 0}`) mapping directly to an operand field (`Rd{4-0}`, `Rn{4-0}`, `imm12{11-0}`). Thus, a verified AArch64 encoder/decoder can be generated **100% mechanically** from the `--dump-json` `Inst` array and `AsmString`!
- **X86 (`X86InstrFormats.td`)**: Because x86-64 instructions are variable-length (`1`–`15` bytes) with legacy prefixes, `0F`/`0F38`/`0F3A` opcode maps, `REX`/`REX2`, `VEX`, `EVEX` (with compressed displacement `CD8_Scale`), `ModR/M`, `SIB`, and immediate bytes, `X86.td` stores `"Opcode"` (`bits<8>`) plus structural bitfields (`FormBits`, `OpPrefixBits`, `OpMapBits`, `AdSizeBits`, `REX_W`, `VEX_4V`, `EVEX_K`, `EVEX_B`, `CD8_Form`, `CD8_EltSize`). Generating a binary encoder from X86 TableGen JSON also requires porting the ~`1,800`-line bit-packing state machine in `llvm/lib/Target/X86/MCTargetDesc/X86MCCodeEmitter.cpp`.

#### 2.3 Selection Patterns (`Pattern`, `Pat`, `SDNode`, `GINodeEquiv`)
- **Structure**: Each `Pattern` (`5,658` standalone + `19,009` inline on X86; `12,232` standalone + `2,118` inline on AArch64) contains:
  - `"PatternToMatch"` (`dag`): Source `SelectionDAG` pattern tree (e.g., `(set GPR64:$dst, (add GPR64:$src1, (shl GPR64:$src2, (i32 imm_0_63:$shift))))`),
  - `"ResultInstrs"` (`list<dag>`): Target instruction tree (`[(ADD64rr_shifted ...)]` or `(ADDXrs GPR64:$src1, GPR64:$src2, ...)`),
  - `"Predicates"` (`list<Predicate>`): Required subtarget features (`[HasAVX2]`, `[HasNEON]`, `[IsLE]`).
- **Impediments to Pure JSON Extraction**:
  1. **`PatFrag` C++ Predicates**: Many `PatternToMatch` nodes reference `PatFrag` records whose `"PredicateCode"` or `"GISelPredicateCode"` field is a raw C++ string evaluated over `SDNode *N` or `MachineInstr &MI`.
  2. **`ComplexPattern` (`12` on X86, `175` on AArch64)**: Addressing modes (`addr`, `am_indexed8`, `ro_Windexed32`) invoke C++ methods (`SelectAddr`, `SelectRegOffset`) in `X86ISelDAGToDAG.cpp` / `AArch64ISelDAGToDAG.cpp`.
  3. **`SDNPCommutative` / `SDNPAssociative` Expansion**: `CodeGenDAGPatterns.cpp` (`llvm/utils/TableGen/Common/CodeGenDAGPatterns.cpp`) automatically permutes commutative operands and infers types before emitting `GenDAGISel.inc`.

#### 2.4 CPU Definitions (`Processor` / `ProcessorModel`) and Subtarget Features (`SubtargetFeature`) for the Drop-In Contract
- To satisfy the `rustc` drop-in CLI contract (`rustc --print target-cpus`, `rustc --print target-features`, `-C target-cpu=...`, `-C target-feature=...`, and `#[target_feature(enable = "...")]`), a compiler needs the exact target CPU list, feature names, descriptions, and transitive feature implication DAG (`Implies`).
- In `rustc` `1.99.1`, `PassWrapper.cpp:281-334` queries LLVM's `MCSubtargetInfo::getAllProcessorDescriptions()` and `getAllProcessorFeatures()`, which are generated directly from `SubtargetFeature` and `Processor` / `ProcessorModel` records in `.td`, filtered through `llvm_util::to_llvm_features` (`compiler/rustc_codegen_llvm/src/llvm_util.rs:239-300`, which translates a handful of Rust feature aliases like AArch64 `"rcpc2" -> "rcpc-immo"`, `"dpb" -> "ccpp"`, `"fp16" -> "fullfp16"`, and ties `"neon"` to `"fp-armv8"`).
- We extracted the complete X86 (`136` CPUs, `231` features, `86` register classes) and AArch64 (`84` CPUs, `356` features, `83` register classes) catalogs into `support/x86_tablegen_catalog.json` and `support/aarch64_tablegen_catalog.json`.

---

### 3. Prior Work on Verified TableGen Import and Verified Instruction Selector Generation

**Basis: documentation + derived**

| System / Paper | Approach to ISA / TableGen Descriptions | Verification Scope & Relevance to Anneal / Verified `rustc` |
| :--- | :--- | :--- |
| **Dias & Ramsey (POPL 2010)**, *"Automatically Generating Instruction Selectors Using Declarative Machine Descriptions"* | Expresses machine instructions in $\lambda$-RTL register-transfer semantics and uses heuristic search + algebraic laws to synthesize a maximal-munch instruction selector from IR to machine instructions. | Shows that declarative RTL semantics suffice to generate instruction selectors, though scaling heuristic search to AVX-512 / SVE vector instructions requires bounded rule templates. |
| **Hydride (ASPLOS 2022)**, *"Hydride: Aarget-Agnostic Synthesis-Based Compiler for Modern Hardware Accelerators"* | Imports vendor ISA pseudocode (Intel Intrinsics Guide XML, Arm Neon/HVX specs) into formal Rosette/Racket bitvector semantics and synthesizes LLVM IR $\to$ target intrinsic/instruction lowering rules via CEGIS + Halide scheduling. | Directly demonstrates automated extraction and SMT synthesis/verification of SIMD vector lowering rules across x86 AVX2/AVX-512 and Arm Neon. |
| **Cranelift ISLE Verification (`veri-isle` / Crocus, ASPLOS 2023 / PLDI 2024)** | Translates Cranelift's declarative ISLE (`Instruction Selection Lowering Expressions`) term-rewriting rules for `x86_64` and `aarch64` into SMT queries verified against official Arm ASL (`sail-arm`) and x86 semantics across bounded bitwidths. | **Closest architectural match for a clean-slate verified Rust backend**: writing or translating TableGen `Pat` rules into a pure typed DSL like ISLE (avoiding C++ `ComplexPattern` escape hatches) allows each rule to be verified offline via SMT (`veri-isle`) or Lean 4 (`bv_decide`) against Sail/ASL ISA semantics! |
| **CompCert `Selectionproof.v` & `Asmgenproof.v`** | Hand-authored Coq pattern-matching functions (`SelectOp`, `SelectLong`, `TranslInstr`) proved sound by induction against `Cminor` and target `Asm` operational semantics. | Gold standard for foundational Coq/Lean kernel verification; importing TableGen's `Inst{31-0}` encoding bits and register tables into Lean 4 inductive definitions eliminates manual transcription errors while keeping the selector proof in Lean. |

---

### 4. Recommended Import & Validation Plan by TableGen Sub-Domain

**Basis: derived**

| TableGen Sub-Domain | Import Method | Validation / Soundness Requirement | Recommended Usage |
| :--- | :--- | :--- | :--- |
| **1. `Processor` & `SubtargetFeature` (`--print target-cpus`, `-C target-feature`)** | Direct import from `llvm-tblgen --dump-json` (`support/*_tablegen_catalog.json`) + `llvm_util::to_llvm_features` mapping table. | Differential CLI output check against `rustc 1.99.1 --print target-cpus` and `--print target-features`. Zero TCB soundness impact. | **Import 100% directly.** |
| **2. `SchedMachineModel` & `SchedReadWrite`** | Direct import from `--dump-json` latency/resource fields. | Untrusted heuristic input to list scheduler (any permutation is checked by the schedule dependence validator). | **Import 100% directly.** |
| **3. `Register`, `RegisterClass`, `CallingConv`** | Import register numbers, subregister containment (`SubRegIndices`), DWARF numbers, and `CalleeSavedRegs` from `--dump-json`. | Validate against target ABI specifications (`System V AMD64`, `Win64`, `AAPCS64`); register allocator validator checks disjointness of physical register numbers and subregister aliases. | **Import directly + validate subregister alias graph.** |
| **4. `Instruction` Binary Encodings & Flags (`mayLoad`, `mayStore`, `Uses`, `Defs`)** | Import AArch64 `Inst{31-0}` bit arrays directly; for X86, import `Opcode`/`FormBits`/`OpPrefix`/`OpMap`/`REX`/`VEX`/`EVEX` fields. | **Cross-validate every imported instruction encoding and its `Uses`/`Defs`/`mayLoad`/`mayStore` flags against Sail/ASL (`sail-arm`, `sail-riscv`) or `x86` formal semantics** (or round-trip fuzz via `llvm-mc --disassemble`). | **Import + cross-validate against Sail/ASL/llvm-mc.** |
| **5. `Pattern` / `Pat` Selection Rules** | Import pure algebraic/memory `Pat` and `GINodeEquiv` trees (`19,009` inline + `5,658` standalone on X86; `2,118` inline + `12,232` standalone on AArch64) as candidate rewrite rules; rewrite the `12` X86 / `175` AArch64 `ComplexPattern` addressing matchers explicitly in pure code. | Verify each imported selection rule $(P_{\text{DAG}} \implies I_{\text{target}})$ offline via Lean 4 `bv_decide` / SMT (`veri-isle` style) against target instruction semantics. | **Import pure subset + verify each rule offline.** |

## Boundaries

- **C++ `ComplexPattern` and `usesCustomInserter` opacity**: `llvm-tblgen --dump-json` only records the C++ function name string (e.g., `"SelectAddr"`, `"SelectArithImmed"`) for `ComplexPattern`s and `"usesCustomInserter": 1` for custom-inserted instructions. Their operational behavior resides in `llvm/lib/Target/{X86,AArch64}/*ISelDAGToDAG.cpp` and `*ISelLowering.cpp` and cannot be recovered from `.td` files alone.
- **RISC-V Calling Convention**: Unlike X86 (`53` `CallingConv` records) and AArch64 (`16` `CallingConv` records), RISC-V defines `0` `CallingConv` records in `RISCV.td`; its calling convention is implemented entirely in C++ (`CC_RISCV` in `llvm/lib/Target/RISCV/RISCVISelLowering.cpp`).

## Evidence

- **Primary source files in `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)**:
  - `llvm/lib/TableGen/JSONBackend.cpp`: lines 1–180 (`EmitJSON` implementation for `llvm-tblgen --dump-json`).
  - `llvm/include/llvm/Target/Target.td`: lines 1–1850 (`Register`, `RegisterClass`, `Instruction`, `Pattern`, `Pat`, `ComplexPattern`, `SubtargetFeature`, `Processor`).
  - `llvm/lib/Target/X86/X86.td` and `X86*.td` (`58` files, `89,325` LOC).
  - `llvm/lib/Target/AArch64/AArch64.td` and `AArch64*.td` (`53` files, `113,058` LOC).
  - `llvm/lib/Target/RISCV/RISCV.td` and `RISCV*.td` (`68` files, `59,406` LOC).
- **Primary source files in `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`: lines 281–334 (`LLVMRustPrintTargetCPUs`, `LLVMRustGetTargetFeaturesCount`, `LLVMRustGetTargetFeature`).
  - `compiler/rustc_codegen_llvm/src/llvm_util.rs`: lines 239–300 (`to_llvm_features`).
- **Preserved support artifacts (`reports/llvm-tablegen-isa-extraction-and-verified-selector-reuse/support/`)**:
  - `tblgen_summary.json`: Exact record, class, instruction, pattern, register, feature, CPU, and flag counts extracted via `llvm-tblgen --dump-json` across X86, AArch64, and RISC-V.
  - `x86_tablegen_catalog.json` and `aarch64_tablegen_catalog.json`: Extracted compact catalogs of all `Processor` models, `SubtargetFeature` definitions (with `Implies` edges), and `RegisterClass` records for X86 and AArch64.
  - `extract_tablegen_json.py`: Standalone Python extraction script reproducing the `--dump-json` record analysis.

## Revalidation

To regenerate the TableGen summary and catalogs on a newer LLVM revision, run:

```bash
python3 reports/llvm-tablegen-isa-extraction-and-verified-selector-reuse/support/extract_tablegen_json.py \
  --llvm-tblgen /path/to/llvm-tblgen \
  --llvm-root /path/to/llvm-project/llvm \
  --target X86
```

Compare the output counts against `support/tblgen_summary.json`.
