# Machine-Code Verification Frameworks and Inline/Naked Assembly Contracts

## Summary

A verified Rust compiler or MIR-level program verifier that encounters `core::arch::asm!`, `core::arch::naked_asm!`, or `core::arch::global_asm!` must bridge the semantic gap between typed compiler intermediate representations (where local variables are abstract SSA/MIR places and memory is structured into allocations) and concrete target machine state (where registers, flags, the hardware stack pointer, and flat or page-mapped memory are directly mutated). Across existing verified compilers and machine-code verification frameworks, three distinct architectural patterns govern this boundary:

1. **Axiomatized or Annotated Builtin Calls (CompCert):** CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`) models inline assembly (`EF_inline_asm`) as an uninterpreted external call (`Pbuiltin`) governed by an axiomatic contract (`Axiom inline_assembly_properties` in `common/Events.v:1480-1481`), while providing zero-instruction assertion annotations (`EF_annot`, `EF_annot_val`) for instrumentation. It does not parse or verify the assembly string against `x86/Asm.v` or `aarch64/Asm.v`.
2. **Source-Integrated Ghost/Hoare Assembly DSLs (Jasmin, Vale, Bedrock2, CakeML, TAL/CAP/XCAP):** Code is written in a structured assembly DSL (`Jasmin`, `Vale`, `Bedrock2`) or target-agnostic abstract assembly (`CakeML` `asm`) equipped with explicit register/stack/memory framing contracts. These systems prove compilation or Hoare triples for whole procedures, either restricting inline assembly to verified intrinsics (`Jasmin` `#inline` / syscall primitives) or requiring full procedure-level separation-logic specifications (`Bedrock2`, `XCAP`).
3. **Post-Compilation / Instruction-Level Semantic Lifters and Weakest-Precondition Calculi (Islaris/CN2Islaris, s2n-bignum/cslib-bignum, LNSym, Kraken):** Machine instructions inside an assembly block or compiled binary are decoded into an operational ISA semantics (Sail/Isla traces in `Islaris`, HOL Light / Lean 4 state transformers in `s2n-bignum` and `cslib-bignum`, Lean 4 AArch64/x86-64 ASTs in `LNSym` and `Kraken`) and discharged against a pre/postcondition or separation-logic triple.

For a verified Rust compiler and the Anneal verification architecture, Rust's `TerminatorKind::InlineAsm` (`compiler/rustc_middle/src/mir/syntax.rs:924-968` in `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`) already canonicalizes register constraints, late outputs, options (`PURE`, `NOMEM`, `READONLY`, `PRESERVES_FLAGS`, `NORETURN`, `NOSTACK`, `MAY_UNWIND`), and `clobber_abi` sets (expanding `clobber_abi("C")` on `x86_64-unknown-linux-gnu` into 73 explicit `lateout("<reg>") _` clobber operands during MIR construction). This makes a **two-tier assembly contract architecture** optimal:
- **Tier A (Assumed / Compositional MIR Boundary Contract):** Every `asm!` block and `#[unsafe(naked)]` function carries an explicit MIR-level relational contract over its bound `In`/`Out`/`InOut` operands, allowed memory footprint (governed by `NOMEM` / `READONLY`), stack-frame preservation (`NOSTACK`), and flag preservation (`PRESERVES_FLAGS`), enabling surrounding Rust code to be verified modularly without an ISA decoder.
- **Tier B (Kernel-Checked ISA Refinement Discharge):** The assembly template itself is parsed or decoded from emitted object bytes into a Lean 4 ISA semantics (`Kraken` / `cslib-bignum` / `Sail-Lean`) and proved to refine the Tier A MIR contract under the register assignment and non-aliasing guarantees enforced by `rustc`'s register allocator.

## Applicability

The findings in this report apply to:
- **Rust compiler and language specifications:** `rustc 1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`), The Rust Reference (`rust-lang/reference@bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`, `src/inline-assembly.md`), and the Ferrocene Language Specification (`rust-lang/fls@946eacae5a4a33a89af7832178504692439e7478`, tag `1.99`, `src/inline-assembly.rst`).
- **Verified compilers and machine-code verification frameworks:**
  - `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc` (`common/Events.v`, `x86/Asm.v`, `aarch64/Asm.v`);
  - `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9` and `rems-project/CN2Islaris@f34f9a2f0a9b75a6b342aa966d0d14daca58c466`;
  - `awslabs/s2n-bignum@9f2cd960e11892a582e7facb0c191b4a2959ea91` and `cslib-community/bignum@92dc3ee58280db51bbbb4dd51b85a91abd0178ba`;
  - `jasmin-lang/jasmin@34f15840f10625bbc2cbf59b3d877e94c75bfbd9`;
  - `project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`;
  - `CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8`;
  - `mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13` and `mit-plv/riscv-coq@45dc8dfc17c77aabb433355b9d39edc6bfd429ae`;
  - `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92` and `AeneasVerif/kraken@c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`;
  - Foundational typed and certified assembly formalisms: TAL (Morrisett et al., TOPLAS 1999, `10.1145/319301.319345`), CAP (Yu, Hamid, and Shao, ESOP 2003, `10.1007/3-540-45927-8_19`), and XCAP (Ni and Shao, POPL 2006, `10.1145/113445.113468`; Feng, Shao, Vaynberg, Xiang, and Ni, PLDI 2006, `10.1145/1133981.1134018`).

## Findings

### 1. Comparative Taxonomy of Machine-Code Verification Frameworks

Basis: source + normative + documentation

The surveyed frameworks differ along five architectural axes: how instructions are represented, how contracts are stated, whether system/privileged instructions are modeled, how register/memory framing is enforced, and what remains in the trusted computing base (TCB).

| Framework | Proof Host & ISA Source | Contract Form | Framing & Memory Model | System & Privileged Instruction Support | Compiler Boundary Mechanism |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Islaris / CN2Islaris** (`rems-project/islaris@c978e10f`) | Rocq + Iris (`Lithium` automated solver) over `Isla` SMT-simplified `Sail` traces (AArch64 v9.4-A, RISC-V 64) | Higher-order separation logic (`instr pre_pc (λ _, P) * ...`) with step-indexed guarded recursion (`▷`) | Per-register points-to (`r ↦ᵣ v`), byte/dword memory (`a ↦ₘ v`), instruction memory (`a ↦ᵢ opc`) | **Full architectural coverage** via Sail: EL0–EL3 exceptions, `MRS`/`MSR`, page tables / TLB maintenance, PAC (`PACIASP`/`AUTIASP`), BTI (`CN2Islaris` translates CN C specs to AArch64 binary specs across `-O0`..`-O2`) | Matches DWARF line/type tables (`dwarfData.ml`) and AAPCS64 calling conventions at function entry/return |
| **s2n-bignum & cslib-bignum** (`awslabs/s2n-bignum@9f2cd960`, `cslib-community/bignum@92dc3ee5`) | HOL Light (`s2n-bignum`) and Lean 4 (`cslib-bignum`) over decoded ELF/Mach-O object bytes (x86-64 + AArch64) | Relational Hoare triple `ensures step P Q frame` (`maychange` frame condition) | Explicit `maychange` modifier set listing every mutated register, flag (`CF`, `ZF`, ...), and `[ptr, len)` memory range | User-space cryptographic and arithmetic ISA only (`ADX`, `BMI2`, `AVX2`/`AVX-512`, `NEON`/`AES`/`SHA`); no privileged instructions | Verifies ABI-compliant C-callable leaf functions (`System V AMD64`, `Windows x64`, `AAPCS64`) directly on object files |
| **Kraken** (`AeneasVerif/kraken@c9aa45ee`) | Lean 4 (`v4.36.0-nightly`) custom weakest-precondition (`WP`) engine for AArch64 and x86-64 assembly | `Spec.loop` / `WP.run` relational pre/postconditions over `MachineState` (`regs`, `flags`, `mem`) | Functional lenses over 64-bit GP/SIMD registers and flat/region-framed byte memory | User-space AArch64 and x86-64 instructions; parses `.s` / inline assembly sequences directly in Lean 4 | Designed to discharge inline assembly and external assembly leaf functions called from Aeneas/Charon-extracted Rust MIR |
| **AWS LNSym** (`leanprover/LNSym@5c05220f`) | Lean 4 symbolic simulator and proof framework over hand-translated ASL AArch64 semantics | Symbolic state-transition theorems `step_n s0 n = s1` with bitvector (`BitVec`) invariants | Explicit `ArmState` record (`gpr`, `sfp`, `pstate`, `mem`, `program`) | User-space AArch64 base + NEON/crypto (`AES`, `SHA512`, `SHA3`); system registers stubbed except `NZCV`/`FPCR` | Verifies ELF `.text` slices loaded into `ArmState.program` at fixed virtual addresses |
| **Jasmin** (`jasmin-lang/jasmin@34f15840`) | Rocq (`coqword`, `arch_decl.v`, `arch_sem.v`) + EasyCrypt relational logic (x86-64, AArch64, ARMv7) | Source-level safety + observational equivalence + constant-time leakage preservation | Compiler-managed `stk` and `reg` separation from caller-owned `mem` | User-space crypto + `#syscall` (`randombytes`) and inline intrinsics (`#ADCX`, `#ADOX`, `#MULX`, `#VPBROADCAST`) | Compiles `.jazz` procedures to `.s` assembly; compiler correctness theorem preserves semantics from source to `arch_sem` |
| **Vale** (`project-everest/vale@bbae0eb8`) | F* (`X64.Machine_s.fst`, `X64.Semantics_s.fst`) and Dafny (x86-64, AArch64, ARMv7) | Procedure Hoare triples (`requires` / `ensures` / `modifies` clauses) | Explicit `modifies` clauses on registers (`rax`, `efl`, `xmm0`..) and Ghost `memLayout` buffers (`validSrcAddrs`, `validDstAddrs`) | Primarily user-space crypto (`AES-NI`, `PCLMULQDQ`, `VAES`, `SHA-NI`), with Komodo extension modeling ARM TrustZone monitor mode | Generates verified `.S` files for GCC/Clang/MSVC consumption with verified C ABI wrappers |
| **CakeML** (`CakeML/cakeml@b064083e`) | HOL4 (`asmScript.sml`, `asmSemScript.sml`, `lab_to_targetProofScript.sml`) + L3 target models (x64, ARMv8, RISC-V, MIPS, Silver) | Target-level behavioral refinement (`machine_sem mc ffi ms ⊆ ...`) and decompilation into logic (`SPEC m p c q`) | Flat byte array restricted to `dm : word64 set` (accessible data domain) plus FFI shared-memory byte domains | User-space instructions in `asm` IR; L3 target models include privileged modes (used in seL4/Camkes integration) | External I/O and inline FFI transitions go through `call_FFI` oracle events with explicit byte-slice contracts |
| **Bedrock2 & riscv-coq** (`mit-plv/bedrock2@757f17c6`, `mit-plv/riscv-coq@45dc8dfc`) | Rocq (`RiscvMachine`, `Primitives`, `MinimalMMIO`, `FlatToRiscvCommon.v`) | Omni-semantics weakest precondition (`mcomp_sat`) with separating conjunction (`*`) on byte maps | Partial map `mem : word -> option byte`; MMIO addresses excluded from RAM map and routed to trace events | Full RV32/RV64 M-mode / S-mode CSRs (`mstatus`, `mtvec`, `mepc`), `ecall`/`mret`, and MMIO load/store traces (`Kami` hardware co-verification) | Compiles C-like `bedrock2` functions to RISC-V machine words; inline MMIO/CSR instructions modeled as primitive `ext_spec` actions |
| **TAL, CAP & XCAP** (`10.1145/319301.319345`, `10.1145/113445.113468`, `10.1145/1133981.1134018`) | Syntactic type systems (TAL) and Coq/Rocq predicative/impredicative assertion logics (CAP, XCAP) | Code-heap map $\Psi = \{f_1 \mapsto \text{a}_1, \dots\}$ assigning precondition assertions to code labels | First-order/higher-order predicates over register file $\mathsf{Reg}$ and heap $\mathsf{Heap}$; XCAP adds `Prop` embedded assertions for return pointers and `cli`/`sti` interrupt flags | **Explicit OS kernel support (XCAP/CertiKOS):** `cli`/`sti`, `iret`, `cr3` page-table switches, PIC/APIC EOI, and context-switch (`switch`) with saved-ESP/EIP invariants | Assembly blocks are basic blocks whose entry label carries $\text{a}_{\text{in}}$ and whose jump targets carry $\text{a}_{\text{out}} \in \Psi$ |

### 2. How CompCert Treats Inline Assembly and Annotations

Basis: source (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`)

CompCert represents both C `__asm__` blocks and verification annotations as variants of the `external_function` inductive type (`common/Events.v`):
- `EF_inline_asm (text: string) (sg: signature) (clobbers: list string)` represents an extended C inline assembly statement.
- `EF_annot (kind: positive) (text: string) (targs: list typ)` and `EF_annot_val (kind: positive) (text: string) (targ: typ)` represent zero-code compiler assertions or value-logging markers that pass through register allocation without emitting machine instructions.

In `common/Events.v:1478-1481`, CompCert does **not** parse `text` or interpret it against `x86/Asm.v` or `aarch64/Asm.v`. Instead, it axiomatizes the semantics of every inline assembly string as an opaque external call parameterized only by the text string and function signature:

```coq
Parameter inline_assembly_sem: String.string -> signature -> extcall_sem.

Axiom inline_assembly_properties:
  forall id sg, extcall_properties (inline_assembly_sem id sg) sg.
```

At the target assembly level (`x86/Asm.v:253, 977, 1115` and `aarch64/Asm.v:304, 1130, 1235`), `EF_inline_asm` compiles to the pseudo-instruction `Pbuiltin ef args res`. During register allocation (`backend/Allocation.v`), CompCert respects the `clobbers` register list by inserting conflict edges so live C variables are not allocated to clobbered registers, and maps input/output operands into `builtin_arg preg` and `builtin_res preg`. However, the operational transition in `Asm.step` (`x86/Asm.v:1115-1130`) transitions in a single atomic macro-step via `extcall_semantics ef ge args m t vres m'`, relying entirely on `inline_assembly_properties` (`Events.v:1524, 1543`).

This design has three direct consequences for a high-assurance Rust compiler:
1. **Unsoundness if the assembly violates `extcall_properties`:** CompCert's `extcall_properties` axiom asserts that the inline assembly preserves private caller stack frames, does not forge pointers, and commutes with memory injections (`Mem.inject`). Any inline assembly that manipulates `RSP`/`SP` directly, accesses unpassed stack slots, or branches out of the block invalidates `inline_assembly_properties` silently.
2. **Opaque to binary encoders:** Because `Pbuiltin (EF_inline_asm txt ...)` remains a string pseudo-instruction in `Asm.v`, CompCert's printer (`TargetPrinter.ml`) splice-prints `txt` into the `.s` file for the system assembler (`gas` / `clang`), preventing CompCert's internal verified instruction encoders (such as `CompCertELF`) from encoding functions that contain `EF_inline_asm`.
3. **Why `EF_annot` is useful:** `EF_annot` forces the register allocator to materialize specified SSA values into concrete registers or stack locations (`builtin_arg preg`) at a program point without emitting code, providing a clean mechanism to align source/MIR invariants with machine registers at loop headers or assembly boundaries.

### 3. Rust's Inline and Naked Assembly Surface and MIR Lowering

Basis: normative (`rust-lang/reference@bcd62f35`, `rust-lang/fls@946eacae`) + source (`rust-lang/rust@58cf8f9c`) + execution (`support/asm_mir_probe.rs`, `support/asm_mir_probe.mir.txt`)

Unlike C's loosely typed GCC inline assembly, Rust specifies a tightly constrained contract in The Rust Reference (`src/inline-assembly.md`) and FLS 1.99 (`src/inline-assembly.rst`) and lowers it into a structured MIR terminator before codegen.

#### 3.1 AST and MIR Representation in `rustc 1.99.1`

In `compiler/rustc_ast/src/ast.rs:2700-2713, 2821-2914`, `rustc` parses `asm!`, `naked_asm!`, and `global_asm!` into `ast::InlineAsm` with a 9-bit `InlineAsmOptions` bitflag:
- `PURE` (`1 << 0`): Assembly has no side effects and its outputs depend only on its direct `in` operands (requires `NOMEM` or `READONLY`).
- `NOMEM` (`1 << 1`): Assembly does not read or write memory accessible outside the assembly block.
- `READONLY` (`1 << 2`): Assembly may read memory but does not write any memory accessible outside the assembly block.
- `PRESERVES_FLAGS` (`1 << 3`): Assembly restores architectural condition flags (`RFLAGS` status flags / `x87` FP status word on x86; `NZCV` and `FPSR` on AArch64).
- `NORETURN` (`1 << 4`): Assembly never falls through to the end of the block; treated as returning `!`.
- `NOSTACK` (`1 << 5`): Assembly does not push data to the hardware stack or write to the stack red zone (`128` bytes below `RSP` on System V x86-64).
- `ATT_SYNTAX` (`1 << 6`) and `RAW` (`1 << 7`): Syntax/template formatting flags.
- `MAY_UNWIND` (`1 << 8`): Assembly is permitted to unwind the stack via the platform C++/Rust unwinder.

During MIR construction (`compiler/rustc_middle/src/mir/syntax.rs:924-968, 1055-1085`), `asm!` and `naked_asm!` become `TerminatorKind::InlineAsm`:

```rust
InlineAsm {
    asm_macro: InlineAsmMacro, // Asm | NakedAsm
    template: &'tcx [InlineAsmTemplatePiece],
    operands: Box<[InlineAsmOperand<'tcx>]>,
    options: InlineAsmOptions,
    line_spans: &'tcx [Span],
    targets: Box<[BasicBlock]>,
    unwind: UnwindAction,
}
```

where each `mir::InlineAsmOperand<'tcx>` (`syntax.rs:1055-1085`) is one of:
- `In { reg: InlineAsmRegOrRegClass, value: Operand<'tcx> }`
- `Out { reg: InlineAsmRegOrRegClass, late: bool, place: Option<Place<'tcx>> }`
- `InOut { reg: InlineAsmRegOrRegClass, late: bool, in_value: Operand<'tcx>, out_place: Option<Place<'tcx>> }`
- `Const { value: Box<ConstOperand<'tcx>> }`
- `SymFn { value: Box<ConstOperand<'tcx>> }`
- `SymStatic { def_id: DefId }`
- `Label { target_index: usize }`

#### 3.2 Empirical Observation of `clobber_abi` and `naked_asm!` in MIR

Running `rustc 1.99.1 -Zunpretty=mir --target x86_64-unknown-linux-gnu` on `support/asm_mir_probe.rs` (preserved in `support/asm_mir_probe.mir.txt`) establishes two critical properties for verification tools that consume MIR (such as `anneal-rustc-capture`):
1. **`clobber_abi` is completely desugared before MIR:** The `clobber_abis` field exists on `ast::InlineAsm` (`ast.rs:2910`) and `hir::InlineAsm`, but **does not exist** on `mir::TerminatorKind::InlineAsm`. Instead, typechecking/MIR lowering expands `clobber_abi("C")` on `x86_64-unknown-linux-gnu` directly into 73 explicit `lateout("<reg>") _` (`Out { reg: Reg(...), late: true, place: None }`) entries in `operands` covering every caller-saved register across all extension banks (`cx`, `dx`, `si`, `di`, `r8`..`r11`, `xmm0`..`xmm15`, `zmm16`..`zmm31`, `k0`..`k7`, `mm0`..`mm7`, `st(0)`..`st(7)`, `tmm0`..`tmm7`). Consequently, a MIR verifier does not need a separate ABI clobber table to know which registers an `asm!` block may overwrite—the `operands` array in `TerminatorKind::InlineAsm` is already exhaustive!
2. **`#[unsafe(naked)]` + `naked_asm!` lowers to a single-block MIR body:** For `naked_identity`, `rustc 1.99.1` produces a single basic block `bb0` containing zero statements and terminating in `asm!("mov rax, rdi\nret", options()) -> unwind unreachable` (`targets: []`, `asm_macro: InlineAsmMacro::NakedAsm`). Argument locals `_1: u64` exist in the MIR signature for typechecking, but are not referenced in `operands` because naked functions receive arguments directly in ABI registers (`rdi`) without compiler-generated prologue/epilogue code.

### 4. Contract Forms and Verification Discharge Architecture for Compiled-to-Assembly Boundaries

Basis: derived (synthesized from `rustc 1.99.1` MIR invariants, `s2n-bignum`/`Kraken`/`Islaris` operational models, and Anneal's `Trusted.CrateTheorem` architecture)

To support inline and naked assembly in a verified Rust compiler and in Anneal without weakening soundness, the contract between compiled MIR and machine code must bridge five state components: **operands/registers**, **clobbers**, **memory footprint**, **architectural flags**, and **stack discipline**.

#### 4.1 The Five Boundary Obligations

For any `TerminatorKind::InlineAsm` node $T$ in function $F$:

1. **Register Allocation & Non-Aliasing Precondition ($\mathsf{RegAllocValid}$):**
   Let $\sigma : \text{OperandIdx} \to \mathsf{PhysReg}$ be the physical register assignment chosen by the compiler backend (or fixed by explicit `Reg(r)` constraints). Rust's inline assembly rules (`rust-lang/reference@bcd62f35`, `src/inline-assembly.md`) guarantee—and a verified backend register allocator must prove—that:
   - Distinct `Out` and `InOut` operands receive pairwise disjoint physical registers $\sigma(i) \neq \sigma(j)$;
   - Every non-`late` `Out` operand (`late: false`) is disjoint from every `In` operand ($\sigma(i_{\text{out}}) \neq \sigma(j_{\text{in}})$), because the assembly may overwrite non-late outputs before reading all inputs;
   - Every `late` `Out` operand (`late: true`) may alias an `In` operand, requiring the assembly proof to establish that all `In` operands are consumed before any `lateout` register is written (Wait: we observed this exact hazard in practice when an `in(reg)` pointer allocated to `x8` was clobbered by `mov x8, #64` before `mov x1, x8`!).
   - Every register outside $\{\sigma(k) \mid k \in \text{Out} \cup \text{InOut}\}$ must have its entry value restored at block exit: $\forall r \notin \text{ModRegs}(T),\, \mathsf{ms}'.\mathsf{reg}(r) = \mathsf{ms}.\mathsf{reg}(r)$.

2. **Flag Preservation ($\mathsf{FlagsValid}$):**
   - On x86/x86-64, `RFLAGS.DF` (Direction Flag) must always be `0` on entry and exit.
   - If `options.contains(PRESERVES_FLAGS)`, the assembly must preserve status flags (`CF`, `PF`, `AF`, `ZF`, `SF`, `OF` and `x87` status word on x86; `PSTATE.NZCV` and `FPSR` on AArch64): $\mathsf{ms}'.\mathsf{flags} = \mathsf{ms}.\mathsf{flags}$.

3. **Stack Pointer & Red-Zone Discipline ($\mathsf{StackValid}$):**
   - The hardware stack pointer (`RSP` on x86-64, `ESP` on i386, `SP` on AArch64) must be restored to its exact entry value on normal fallthrough or label jump: $\mathsf{ms}'.\mathsf{sp} = \mathsf{ms}.\mathsf{sp}$.
   - If `options.contains(NOSTACK)`, the assembly trace may not write to any address below $\mathsf{ms}.\mathsf{sp}$ (permitting the compiler to keep live spills in the 128-byte System V x86-64 red zone $[\mathsf{sp}-128, \mathsf{sp})$). If `NOSTACK` is absent, the assembly may freely clobber $[\mathsf{sp}-\text{stack\_limit}, \mathsf{sp})$, and the compiler backend must not place live red-zone spills across $T$.

4. **Memory Framing & Provenance ($\mathsf{MemValid}$):**
   - If `options.contains(NOMEM)`, the assembly trace may not issue any memory load or store outside assembly-private scratch space, and $\mathsf{ms}'.\mathsf{mem} = \mathsf{ms}.\mathsf{mem}$.
   - If `options.contains(READONLY)`, the assembly trace may read only from memory regions authorized by its precondition $P_{\text{mem}}$ and must satisfy $\mathsf{ms}'.\mathsf{mem} = \mathsf{ms}.\mathsf{mem}$.
   - Otherwise, the assembly contract must specify a separation-logic or `maychange` memory frame $F_{\text{mem}}$ (as in `Islaris` or `s2n-bignum`) disjoint from all compiler-owned local stack slots (`StorageLive` MIR locals whose address has not been exposed via `&raw` / pointer-to-integer casts).

5. **Control-Flow Exit Discipline ($\mathsf{ExitValid}$):**
   - Standard `asm!` without `NORETURN` must reach the end of the template bytes (transitioning to `targets[0]`) or jump to one of the explicit `label` block addresses `targets[1..]` without modifying caller-saved frame pointers (`RBP`/`X29`).
   - `#[unsafe(naked)]` functions (`InlineAsmMacro::NakedAsm`) must satisfy a whole-function ABI contract (identical to `s2n-bignum`'s `ensures` theorem): starting from entry PC with arguments in ABI registers (`rdi, rsi, ...` or `x0, x1, ...`) and return address at `[rsp]` (x86-64) or `x30/LR` (AArch64), execution reaches the caller's return address with the return value in ABI return registers (`rax`/`x0`), callee-saved registers restored, and `rsp = rsp_0 + 8` (x86-64) or `sp = sp_0` (AArch64).

#### 4.2 Discharging Assembly Contracts in Lean 4

A Lean 4 verifier (such as Anneal extended with Kraken/LNSym/Sail-Lean ISA semantics) discharges inline and naked assembly in two composable layers:

```text
  [Rust MIR Function Body]
           │
           ▼  (1) MIR WP / Hoare Verification (Anneal theory/)
  ┌──────────────────────────────────────────────────────────────┐
  │ TerminatorKind::InlineAsm Contract Boundary                  │
  │   Precondition:  P_mir(in_vals, mem_pre)                     │
  │   Postcondition: Q_mir(in_vals, out_vals, mem_pre, mem_post) │
  │   Frame:         options (NOMEM / READONLY / NOSTACK / PURE) │
  └──────────────────────────────────────────────────────────────┘
           │
           ▼  (2) Universal Quantification over Valid Reg Assignments σ
  ┌──────────────────────────────────────────────────────────────┐
  │ Machine-Code Refinement Obligation (Kraken / cslib-bignum)   │
  │   ∀ σ : RegAssignment, RegAllocValid(operands, σ) →          │
  │   ∀ ms : MachineState, LiftState(ms, σ, in_vals, mem_pre) →  │
  │     ensures isa_step (EntryPC ms) (ExitPC ms)                │
  │       (λ ms' => LiftPost(ms, ms', σ, out_vals, mem_post) ∧   │
  │                 FramePreserved(ms, ms', σ, options))         │
  └──────────────────────────────────────────────────────────────┘
```

- **Crucial design insight for `in(reg)` template parameters:** When an `asm!` block uses register class constraints (`in(reg) x`) rather than fixed registers (`in("rax") x`), the template is instantiated by the backend register allocator with any valid physical register $\sigma(i) \in \mathsf{RegClass}$. If verification runs at the MIR level before register allocation, the ISA proof must quantify over all valid injective assignments $\sigma$ satisfying $\mathsf{RegAllocValid}$ (which in `Kraken` or `LNSym` reduces to symbolic register indices $r_1 \neq r_2$ unless instructions have register-specific encodings like `mul`/`div` on `rax:rdx`, which Rust already forces to use explicit `inout("rax")` / `out("rdx")` constraints). Alternatively, if verification runs after register allocation / object emission (as in `s2n-bignum` and `CN2Islaris`), $\sigma$ is concrete and the obligation is discharged on the exact emitted instruction sequence.

## Boundaries

- **Not examined:** Inline assembly on non-Tier-1 architectures (`riscv64gc`, `powerpc64`, `s390x`, `loongarch64`, `wasm32`) was not empirically probed in this package, though `TerminatorKind::InlineAsm` and `InlineAsmOptions` are target-independent in `rustc_middle::mir`.
- **Unsupported in upstream Anneal `origin/main`:** At `joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`, `trusted/rustc-capture` does not yet extract or verify `TerminatorKind::InlineAsm` bodies against an ISA model; the two-tier contract architecture in Finding 4 is a derived design specification for extending MIR verification to inline and naked assembly.
- **Known not to apply:** CompCert's `Axiom inline_assembly_properties` (`common/Events.v:1480-1481`) cannot be used as a sound verification mechanism for untrusted or general Rust `asm!` blocks because it assumes without proof that the assembly text obeys calling-convention, memory-injection, and stack-frame preservation invariants.

## Evidence

1. **Rust 1.99.1 AST, MIR, and Register Class Source:**
   - Repository: `rust-lang/rust`, revision `58cf8f9c35b355199727627d07ae34a4e2846d67`.
   - `compiler/rustc_ast/src/ast.rs:2700-2735` (`InlineAsmOptions` bitflags: `PURE`, `NOMEM`, `READONLY`, `PRESERVES_FLAGS`, `NORETURN`, `NOSTACK`, `ATT_SYNTAX`, `RAW`, `MAY_UNWIND`), `2821-2855` (`ast::InlineAsmOperand`), and `2905-2914` (`ast::InlineAsm`).
   - `compiler/rustc_middle/src/mir/syntax.rs:924-968` (`TerminatorKind::InlineAsm`) and `1055-1085` (`mir::InlineAsmOperand`).
   - `compiler/rustc_target/src/asm/mod.rs:755-776` (`InlineAsmRegOrRegClass`).
2. **Rust Normative Inline Assembly Specifications:**
   - The Rust Reference (`rust-lang/reference@bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`), `src/inline-assembly.md` (register classes, `lateout` aliasing rules, `clobber_abi` caller-saved sets, and `options` contracts).
   - Ferrocene Language Specification (`rust-lang/fls@946eacae5a4a33a89af7832178504692439e7478`, tag `1.99`), `src/inline-assembly.rst`.
3. **Executable MIR Lowering Probe (`rustc 1.99.1`):**
   - Preserved in `support/asm_mir_probe.rs` and `support/asm_mir_probe.mir.txt`, produced by:
     ```console
     RUSTC_BOOTSTRAP=1 rustc +1.99.1 -Zunpretty=mir --target x86_64-unknown-linux-gnu support/asm_mir_probe.rs
     ```
   - Demonstrates `options(PURE | NOMEM | PRESERVES_FLAGS | NOSTACK)`, the expansion of `clobber_abi("C")` into 73 explicit `lateout` register clobbers on `x86_64-unknown-linux-gnu`, and `#[unsafe(naked)]` lowering to `TerminatorKind::InlineAsm` with ` -> unwind unreachable`.
4. **CompCert Inline Assembly and Builtin Semantics:**
   - Repository: `AbsInt/CompCert`, revision `2685140bf72c959446981fb99b5e44a8975021bc`.
   - `common/Events.v:1478-1481, 1522-1543` (`Parameter inline_assembly_sem`, `Axiom inline_assembly_properties`, `EF_annot`, `EF_annot_val`, `EF_inline_asm`).
   - `x86/Asm.v:253, 977, 1115` and `aarch64/Asm.v:304, 1130, 1235` (`Pbuiltin` instruction constructor and `exec_instr` / `step` semantics).
5. **Surveyed Machine-Code Verification Frameworks:**
   - `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9` and `rems-project/CN2Islaris@f34f9a2f0a9b75a6b342aa966d0d14daca58c466`;
   - `awslabs/s2n-bignum@9f2cd960e11892a582e7facb0c191b4a2959ea91` (`x86/proofs/base.ml`, `arm/proofs/base.ml`) and `cslib-community/bignum@92dc3ee58280db51bbbb4dd51b85a91abd0178ba`;
   - `AeneasVerif/kraken@c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0` and `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`;
   - `jasmin-lang/jasmin@34f15840f10625bbc2cbf59b3d877e94c75bfbd9` (`proofs/arch/arch_decl.v`, `proofs/arch/arch_sem.v`);
   - `project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288` (`fstar/specs/hardware/X64.Machine_s.fst`, `X64.Semantics_s.fst`);
   - `CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8` (`compiler/encoders/asm/asmScript.sml`, `asmSemScript.sml`);
   - `mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13` and `mit-plv/riscv-coq@45dc8dfc17c77aabb433355b9d39edc6bfd429ae`.

## Revalidation

To revalidate Rust's MIR representation of `asm!`, `clobber_abi`, and `#[unsafe(naked)]` on a newer `rustc` toolchain:

```console
RUSTC_BOOTSTRAP=1 rustc -Zunpretty=mir --target x86_64-unknown-linux-gnu \
  reports/machine-code-verification-frameworks-and-assembly-contracts/support/asm_mir_probe.rs
```

Diff the output against `support/asm_mir_probe.mir.txt` and check `compiler/rustc_middle/src/mir/syntax.rs` (`TerminatorKind::InlineAsm` and `InlineAsmOperand`) and `compiler/rustc_ast/src/ast.rs` (`InlineAsmOptions`) for any new operand variants or option flags.
