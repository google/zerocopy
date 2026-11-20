# Verified Instruction Selection (`ISLE`, `Crocus`, `CompCert`, `CakeML`) and Unified Assembler-Free `MiniMach` Backend IR

## Summary

Production and verified compiler backends fracture post-optimization codegen across four disconnected representations and external tool boundaries: (1) instruction selection and virtual-register IR (`VCode` / `Mach`), (2) byte emission and constant-island/branch relaxation (`MachBuffer` / target `Asm`), (3) DWARF unwinding and debug locations (`UnwindInst` / `MC` tables), and (4) `core::arch::asm!` re-serialized into raw text strings parsed by an unverified external assembler (`llvm-mc` or GNU `as`). This split scatters sub-register lane aliasing, `IsUndef` / `NoUWrap` flag propagation, signed-8 branch overflow, outlined thunk stack shifts, and `-4` PC-relative relocation addends across separate passes with no unified semantic carrier.

Drawing on primary-source inspection of eight pinned upstream repositories and four peer-reviewed papers—complementing without duplicating [`isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026`](../isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026/REPORT.md) (aegraphs, `BTL`, checked integer arithmetic, DST/vtable lowering) and [`selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality`](../selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality/REPORT.md) (`SelectionDAG` undef/shift poison bugs, GCC `combine` recognizers, `Hydra` totality)—we design **`MiniMach<ISA, Form>`** (`Form ∈ {Virt, Alloc, Layout, Encoded}`). `MiniMach` is one canonical, assembler-free Lean 4 parameterized IR unifying selection, `LaneView`-aware allocation, monotone branch relaxation, direct ELF/PE/Mach-O emission, structured `asm!`, CFI/LSDA unwinding, machine outlining, and post-link checks with zero `llvm-mc` dependency. Executed probes against `rustc 1.98.0-nightly` ELF64 objects and Lean `4.34.1` kernel checks prove `12` axiom-clean theorems (`0` `sorry`, `0` `bv_decide`, `0` forbidden axioms) and kill `6/6` planted backend defects.

## Applicability

1. **Verified drop-in `rustc` backends (`AArch64`, `x86-64`, `RISC-V`)**: Replaces external `llvm-mc` / GNU `as` dependencies for object emission and `core::arch::asm!`, preserves `panic=unwind` `.eh_frame`/`.gcc_except_table` tables, and restricts proofs to axioms permitted by `joshlf/anneal` (`TrustedBoundary.lean:529-535, 1615-1617`). (Basis: `source`, `execution`)
2. **Authoritative ISA & selector verification bridges**: Connects declarative ISLE selectors (`cranelift/isle/veri`) and Sail-derived ISA semantics (`ASLp`, `riscv-lean`) to solver-free, kernel-checkable Lean 4 codec/lowering proofs. (Basis: `source`, `documentation`)
3. **Post-RA outlining, branch relaxation, and relocation auditing**: Retains structured operands, frame shifts, and relocation biases in `Form.Layout` and `Form.Encoded` instead of discarding semantics into opaque byte buffers or external printers. (Basis: `source`, `execution`)

## Findings

### 1. Primary-Source Anatomy of Real-Scale Instruction Selection & Backend IR Fragmentation

| System (Pinned Ref) | Selection & Pre-RA IR | Post-RA / Layout IR | Sub-Reg / Flag Model | Assembler & External TCB Boundary | Basis |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Wasmtime Cranelift** (`4eec6994`) | `ISLE` -> immutable `VCode<I>` (`vcode.rs:76-140`) | `regalloc2::Output` -> `MachBuffer` (`mod.rs:16-45`, `buffer.rs:408-442`) | `Reg(u32)` whole-reg / `REG_SPILLSLOT_BIT = 0x8000_0000` (`reg.rs:49-132`); no sub-reg lane algebra | `x64/inst/emit.rs` + `cranelift_assembler_x64`; prologue-only `UnwindInst` (`unwind.rs:51-215`); `VeriISLE`/`Arrival` uses Z3/CVC5 SMT | `source`, `documentation` |
| **CompCert** (`2685140b`) | `Selection.v:38-191` (`sel_expr`) -> RTL -> `Mach` (`Mach.v:54-125`) | Target `x86/Asm.v` / `aarch64/Asm.v` (no `backend/Asm.v`; `Compiler.v:28-29`) | `x86/Asm.v:25-58` `ireg`/`freg`/`crbit` omits `AL`/`AH`/`AX`/`EAX`; `aarch64/Asm.v:28-117` uses `isize := W \| X` | `Pjcc2`/`Pjmptbl`/`Pallocframe`/`Pcfi_adjust` rely on abstract `label_pos` (`x86/Asm.v:351-378`) + **unverified printer/assembler** | `source` |
| **Chamois-CompCert** (`OOPSLA 2023`) | Block Transfer Language (`BTL`) superblocks (`DOI: 10.1145/3622799`) | Lowers into CompCert `Mach`/target `Asm` | Superblock symbolic execution & scheduling in Coq | Inherits CompCert `Asm` printer and assembler TCB (`BTL.v` source blocked by Anubis PoW; see `## Boundaries`) | `documentation` |
| **CakeML** (`2874b664`) | `word_to_stack` (`word_to_stackScript.sml:28-194`, `parmove`, `write_bitmap_def`) | `labLang` (`Label`/`Asm`/`LabAsm`) -> `lab_to_target` (`prog_to_bytes_def`) | Abstract `asm` operands -> explicit byte encoders | **Zero external assembler**: `enc_lines_again_def` iterates branch sizes (`l1 = MAX (LENGTH bs) l`, `L130`) into concrete memory `targetSemScript.sml:118-243`; unverified x64 perf code (`L309-386`) | `source`, `documentation` |
| **LLVM + `rustc`** (`27825e75`, `560abf79`) | `SelectionDAG` vs `GlobalISel` (`GenericMachineInstrs`, `LegalizerInfo`, `RegBankSelect`) | `MachineInstr` / `MachineOperand` (`MachineOperand.h:51-199`, 22 union kinds) | `SubReg_TargetFlags` (12-bit), `IsUndef` multi-use rules (`L125-135`), `getPoisonGeneratingFlags()` (`NoUWrap`/`NoSWrap`/`Disjoint`/`SameSign`, `MachineInstr.h:89-139`) | `rustc_codegen_ssa` structured `InlineAsmOperandRef` (`asm.rs:13-66`) flattened into `"${0:e}"` / `"~{flags}"` text (`rustc_codegen_llvm/src/asm.rs:184-271`) for `llvm-mc` | `source` |

Five primary-source findings expose why unified lowering requires replacing these split representations:

1. **VeriISLE / Crocus & Arrival Verify Local Rewrites via External SMT Inside `wasmtime`**: `cranelift/isle/veri/{veri,isaspec,aslp}` (`Cargo.toml:192-196`) houses Crocus (VanHattum et al., ASPLOS 2024, `DOI: 10.1145/3617232.3624862` — not POPL 2024) and Arrival (`DOI: 10.1145/3764383`, PACMPL/OOPSLA2 2025). `veri/src/expand.rs:40-49, 245-350` unfolds ISLE rules under `Constrain::NotAll` and `Chaining`; `veri/src/runner.rs:38-76` and `veri/src/solver.rs:95-284` run `SolverBackend::{Z3, CVC5}` (`UNSPECIFIED_SORT`, `check_lhs_feasibility`, `check_verification_condition`); `isaspec/src/semantics.rs:9-23` encodes `aarch64::opcode(inst)` into ASLp across `27` `.isle` rule families (`isaspec/src/instructions.rs:41-152`). Meanwhile, production emission splits across `MachBuffer` (`buffer.rs:152, 351, 408-442`, `worst_case_end_of_island(0) <= soonest_deadline`, `BinaryHeap<MachLabelFixup<I>>`), manual `inverted` bytes (`[0x0F, 0x80 + ...]` at `x64/inst/emit.rs:42-57`), AArch64 `mem_finalize` (`aarch64/inst/emit.rs:14-96`), and prologue-only FP-anchored `UnwindInst` (`unwind.rs:39-49, 51-215`). (Basis: `source`, `documentation`)
2. **CompCert Stops Below Concrete Machine Encoding and Lacks Sub-Register Lanes**: `driver/Compiler.v:28-29, 231-260` goes `Stackingproof -> Asmgenproof` directly into target `Asm`, `Mach.v:210, 341` abstracts frame return slots via `return_address_offset`, and `x86/Asm.v:25-58, 239-266, 351-378` evaluates pseudo-instructions (`Pjcc2`, `Pjmptbl`, `Plabel`, `Pallocframe`, `Pcfi_adjust`) using abstract `find_instr`/`label_pos` over whole `RAX..R15` registers without `AL`/`AH`/`AX`/`EAX` lane semantics or verified object bytes. (Basis: `source`)
3. **CakeML Proves Assembler-Free Emission Only Inside Fixed Word/GC Assumptions**: `lab_to_targetScript.sml:15-16, 130, 285-336` (`enc_lines_again_def`, `remove_labels_loop_def`, `pad_section_def`, `prog_to_bytes_def`) eliminates external assemblers into concrete `targetSemScript.sml:118-243` memory, yet remains tied to HOL4, `ffi_offset = 16`, GC bitmaps (`word_to_stackScript.sml:28-194`), unverified x64 perf instrumentation (`L309-386`), and no ELF `.eh_frame`/LSDA tables. (Basis: `source`)
4. **LLVM Overloads `MachineOperand` While `rustc` Serializes Structured `asm!` to Text**: `llvm::MachineInstr` carries IR-level `NoUWrap`/`NoSWrap`/`Disjoint`/`SameSign` bits (`MachineInstr.h:89-139`), while `MachineOperand` packs 22 union kinds with subtle multi-use `IsUndef` rules (`MachineOperand.h:51-199`, `L125-135`) and indirect `MO_CFIIndex` handles. Furthermore, `rustc_codegen_ssa` builds structured `InlineAsmOperandRef`/`InlineAsmTemplatePiece` records (`traits/asm.rs:13-66`), then `rustc_codegen_llvm` (`asm.rs:184-271`) re-serializes them into `"${0:e}"` and `"~{dirflag},~{fpsr},~{flags}"` text solely for LLVM `llvm-mc` parsing. (Basis: `source`)
5. **Sail-Extracted Lean 4 Proofs Currently Rely on Disallowed `bv_decide`**: `opencompl/riscv-lean` calls `bv_decide` at `RISCV/SailToRV64.lean:106` (`shiftiop_srai_eq` over `RISCV/Instructions.lean:109-110`), and `opencompl/lean-mlir` (`lakefile.toml:2`, `Refinement.lean:24-35, 95-110`) permits `native_decide`. Both violate `joshlf/anneal`'s strict audit gate (`TrustedBoundary.lean:529-535, 1615-1617`). In `support/minimach_unified_probe.lean:12-24`, `srai_equiv_no_bv_decide` proves the exact `BitVec 64` `srai` equivalence algebraically via `BitVec.sshiftRight_eq'` using only `[propext]`. (Basis: `source`, `execution`)

### 2. Unified `MiniMach<ISA, Form>` Architecture (Zero `llvm-mc`, Single Parameterized IR)

`MiniMach (isa : TargetIsaSpec) (form : MachForm)` replaces separate selection, layout, unwind, and assembler IRs with one Lean 4 indexed ADT whose statement syntax stays invariant across four refinement forms:

```
  Post-AEGraph / BTL MIR
     │  (verified ISLE rules + parsed InlineAsmTemplateNode)
     ▼
  MiniMach ISA Form.Virt     ── VReg × LaneView, symbolic StackSlot, CFA anchors, structured InlineAsm
     │  (sub-register-aware RA + concrete frame offsets)
     ▼
  MiniMach ISA Form.Alloc    ── PhysReg × LaneView, concrete StackOff, CFIFrameDelta
     │  (monotone relaxLoop + outliner SP-shift + constant-island deadlines)
     ▼
  MiniMach ISA Form.Layout   ── Resolved pc : Nat, narrowed branches, shifted thunk offsets, FDE/LSDA records
     │  (isa.encode + relocFixups + direct ELF/PE/Mach-O emission)
     ▼
  MiniMach ISA Form.Encoded  ── Concrete byte stream + .rela.* + .eh_frame/.gcc_except_table (ZERO llvm-mc)
```

- **`TargetIsaSpec` & Zero-Assembler `InlineAsm`**: Packages `PhysReg`, bounded `Inst` AST (including native ops emitted directly from `InlineAsmTemplatePiece`), `execInst`, total `encode`/`decodeOne`, `decode_encode_append`, and explicit relocation addend bias (`relocBias`, e.g., `-4` for x86-64 `R_X86_64_PLT32` / `R_X86_64_PC32`). Parsing `asm!` constraints directly into `MiniMach` `Inst` operands removes `llvm-mc` from the TCB. (Basis: `source`, `derived`)
- **Explicit `LaneView` Sub-Register Algebra**: Every operand carries `.full64 | .lo32Zext | .lo16Keep | .lo8Keep | .hi8Keep`. Constructive Lean proofs establish 32-bit zero extension (`writeLane_lo32Zext_clears_upper`), non-interference of `AL` and `AH` (`disjoint_lo8_writes_preserve_hi8`, `disjoint_hi8_writes_preserve_lo8`), and register-index distinctness (`REXB`), eliminating `MachineOperand`'s `SubReg_TargetFlags`/`IsUndef` hazards. (Basis: `source`, `execution`)
- **Unified Control, CFI/LSDA, Outlining & Value-Liveness Operations**: `CondBr` (narrow/wide), `Jump`, `Call`, `InvokeLandingPad`, `FrameAdjust`, `SaveReg`, `CfaSet`, `CfaOffset`, `OutlinedCall`, `RelocFixup`, and `DebugBind` sit directly inside each `MachBlock`. Every transformation preserves CFI/LSDA invariants inline—fixing Cranelift's prologue-only `UnwindInst` gap and CompCert's unmodeled `Pcfi_adjust` oracle—while proving outlined thunks (`FrameOp.shiftSp 8#64`) simulate inline execution (`outlined_thunk_simulates_inline`) and restore caller `CFA`/`RA` (`fde_unwind_restores_caller`). (Basis: `execution`, `derived`)
- **Monotone Fixed-Point Relaxation & Direct Object Emission**: `relaxPassAux` strictly forbids instruction shrinking (`relaxPassAux_size_ge`), bounding iterations by `narrowCount xs` (`relaxLoop_converges_valid`), while `Form.Encoded` writes section bytes and `.rela.*` entries directly without assembler relaxation ambiguity. (Basis: `execution`, `derived`)

### 3. Real `rustc 1.98.0-nightly` + Lean `4.34.1` Probe Measurements

Our runnable probe (`support/rustc_minimach_seam_probe.py`, `support/minimach_unified_probe.lean`, recorded in `support/probe_results.json`) establishes the following real-toolchain and formal measurements:

- **`rustc 1.98.0-nightly` ELF64 Codegen (`Basis: execution`)**: Compiling `RUST_SPECIMENS` (`asm_alu_subreg` using `asm!("add {0}, {1}", "xor {0:e}, {1:e}", options(nomem, nostack))`, `unwind_call_lsda` with `extern "C-unwind"` + `DropGuard`, `subreg_lanes`, and `stack_frame_probe`) via `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`-C opt-level=2 -C panic=unwind -C force-unwind-tables=yes --emit=obj`) took `173.22 ms`, yielding a `2,704` B ELF64 (`EM_X86_64 = 62`) object with `116` `.text.*` bytes (`9` B `.text.asm_alu_subreg`, `51` B `unwind_call_lsda`, `19` B `subreg_lanes`, `27` B `stack_frame_probe`, plus `10` B matching `DropGuard::drop` in `GNU objdump 2.47`: `48 8b 07 / c7 00 01 00 00 00 / c3`). Unwind/relocation sections measured `176` B `.eh_frame` (`2` CIEs, `5` FDEs), `12` B `.gcc_except_table.*`, `3` `.rela.text.*` records (types `4` [`PLT32`] and `9` [`GOTPCREL`], addend `-4`), and `7` `.rela.eh_frame` records.
- **Direct Assembler-Free Codec Parity (`Basis: execution`)**: On `.text.asm_alu_subreg` (`4889f8 4801f0 31f0 c3`), `MiniX64Inst` (`rustc_minimach_seam_probe.py:87-162`) achieved `4/4` byte-exact round-trips (`all_roundtrip_matched: true`, `observed_add64_and_xor32_zext: true`) and emitted the inline `asm!` body `4801f031f0` directly (`direct_encoder_exact_subsequence_match: true`) with zero `llvm-mc` invocation. Note `31f0` omits optional `REX` (`canonical_rex: false`).
- **Lean `4.34.1` Kernel Proofs (`Basis: execution`, toy model of `MiniMach`, not a full compiler)**: Checking `support/minimach_unified_probe.lean` (`760` lines, `30,350` B) under `Lean 4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) exited `0` in `15,720.93 ms`. All `12` `#print axioms` checks use strictly `[propext]`, `[propext, Quot.sound]`, or `[propext, Classical.choice, Quot.sound]` (`forbidden_axioms_detected: false`): `srai_equiv_no_bv_decide`, `readLane_writeLane_lo32Zext`, `writeLane_lo32Zext_clears_upper`, `disjoint_lo8_writes_preserve_hi8`, `disjoint_hi8_writes_preserve_lo8`, `lo32Zext_clobbers_upper_canary`, `decodeOne_encodeInst_append` (all `8` instructions including REX-optional `push64`/`pop64`), `decodeStream_encodeStream_id`, `relaxPassAux_size_ge`, `relaxLoop_converges_valid`, `outlined_thunk_simulates_inline`, and `fde_unwind_restores_caller`.

### 4. Performance, Footprint, Simplicity, and Validation Evaluation (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

- **`L1` (Authoring & Proof Velocity)**: `Crocus`/`Arrival` verify single ISLE rules quickly via Z3/CVC5, whereas CompCert/CakeML require manual Coq/HOL4 invariants. Our Lean `4.34.1` probe discharges `12` core theorems across `760` lines using algebraic `BitVec` lemmas without `bv_decide`; scaling velocity to full AVX/SVE ISAs is `not measured`. (Basis: `source`, `execution`, `documentation`)
- **`L2` (Toolchain Build Time)**: `cranelift/isle/veri` pulls Z3/CVC5 and ASLp (`veri/Cargo.toml`, `aslp/Cargo.toml`), and `lean-mlir` pulls `bv_decide`/Mathlib. `minimach_unified_probe.lean` uses only Lean `Init`; full clean-build times for Cranelift/CompCert/CakeML/LLVM are `not measured`. (Basis: `source`, `execution`)
- **`L3` (Compile & Synthesis Latency)**: Eliminating `llvm-mc` string re-serialization and parsing removes subprocess overhead; our 4-function `rustc` specimen compiled in `173.22 ms`, while full-crate `MiniMach` compile throughput is `not measured`. (Basis: `source`, `execution`)
- **`L4` (Generated Code Execution Performance)**: Explicit `LaneView` preserves compact `xor32` zero-extension (`31f0`, `2` B) and `jcc rel8` branch shortening alongside verified SP-shifted outlining (`outlined_thunk_simulates_inline`); full hardware runtime benchmarks are `not measured`. (Basis: `execution`, `derived`)
- **`L5` (Certificate Checking Latency)**: Cold Lean `4.34.1` CLI verification of all `12` theorems in `minimach_unified_probe.lean` completed in `15,720.93 ms` with zero SAT invocations; full-crate MiB/s checking throughput is `not measured`. (Basis: `execution`)
- **`L6` (RAM & Binary Footprint)**: Measured `rustc` ELF64 object = `2,704` B (`116` B `.text.*`, `176` B `.eh_frame`, `12` B `.gcc_except_table.*`, `3` `.rela.text.*`, `7` `.rela.eh_frame`); probe files = `30,350` B (Lean), `24,066` B (Python), `5,446` B (`probe_results.json`); large-crate compiler RAM is `not measured`. (Basis: `execution`)
- **`C1`–`C2` (Spec Auditability & Orthogonality)**: Removing `llvm-mc` and unifying `Virt -> Alloc -> Layout -> Encoded` under `TrustedBoundary`-clean axioms cleanly decouples `LaneView`, branch relaxation, stack thunks, and relocation bias, avoiding LLVM `MachineOperand`'s 22-variant union and CompCert/Cranelift unwinding gaps. (Basis: `source`, `execution`, `derived`)
- **`V1` (Spec Adequacy, Mutation & Non-Vacuity)**: Mutation testing (`rustc_minimach_seam_probe.py:324-414`) killed **`6/6`** planted bugs: (1) `mutant1_lo32_zext_upper_preserve` (`0x0000000000000001` vs `0x1234567800000001`), (2) `mutant2_lo8_keep_clobbers_hi` (`AH=0xde` vs `0x00`), (3) `mutant3_missing_rex_r8_alias` (`4d01c8` vs `4801c8`), (4) `mutant4_jcc_rel8_plus_128_overflow` (`+128` outside `[-128, 127]`), (5) `mutant5_outliner_unshifted_sp_load` (`0x7fff00001010` vs `0x7fff00001008`), and (6) `mutant6_missing_plt32_addend_minus4` (`284` vs `288`). Theorem `lo32Zext_clobbers_upper_canary` certifies non-vacuity of 32-bit zero extension. (Basis: `execution`)
- **`V2` (Differential Cross-Check)**: `MiniX64Inst` matched `rustc 1.98.0-nightly` + `GNU objdump 2.47` byte-for-byte on `.text.asm_alu_subreg` (`4/4` instructions); large-scale arbitrary-CFG fuzzing is `not examined`. (Basis: `execution`)
- **`V3`–`V4` (Crash Unwind & Hardware Replay)**: `fde_unwind_restores_caller` verifies caller `CFA`/`RA` restoration across shifted frame ops matching `rustc`'s `5` FDEs + `12` B LSDA; concurrent weak-memory semantics, transient speculation channels, crates.io replay, and bare-metal silicon execution are `not examined` / `unknown`. (Basis: `execution`, `derived`)

## Boundaries

- **`not examined`**:
  - **Raw `Chamois-CompCert` `btl/BTL.v` source**: Upstream GitLab (`gricad-gitlab.univ-grenoble-alpes.fr/certicompil/Chamois-CompCert`) returned an **Anubis v1.25.0 Proof-of-Work anti-bot challenge**; fetching stopped immediately without bypassing it, restricting BTL analysis to Gourdin et al. (`DOI: 10.1145/3622799`) and [`isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026`](../isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026/REPORT.md). (Basis: `documentation`)
  - **Live runtime execution of `wasmtime` (`cranelift/isle/veri`), `CompCert`, `CakeML`, `lean-mlir`/`riscv-lean`, and LLVM `llc`/`llvm-mc`**: Only `rustc 1.98.0-nightly`, `Lean 4.34.1`, `GNU readelf 2.47`, `GNU objdump 2.47`, and our standalone probes ran locally. (Basis: `execution`)
  - **SIMD/vector lanes (`XMM`/`YMM`/`ZMM`/`NEON`), AArch64 constant-island veneers, PE `.pdata`/`.xdata`, Mach-O compact unwind, and full `asm!` modifiers** (`sym`, `const`, `lateout`, segment prefixes): Covered architecturally by `TargetIsaSpec`; Lean proofs verify the 8-op x86-64 integer subset. (Basis: `derived`, `execution`)
- **`unknown`**:
  - End-to-end `L3` compile latency, `L4` runtime performance, `L5` full-crate certificate MiB/s throughput, `L6` compiler RAM footprint, and `V3` weak-memory / speculative leakage invariants (`not measured`). (Basis: `derived`)
- **`known not to apply`**:
  - **Prefix-free bijectivity (`decodeOne_encodeInst_append`)**: Does not hold unconditionally across redundant legacy x86-64 prefixes unless normalized or indexed explicitly (`canonical_rex`). (Basis: `execution`)
  - **Mechanical `bv_decide` elimination (`srai_equiv_no_bv_decide`)**: Does not automatically cover complex multi-flag, FP, or MMU Sail definitions without algebraic lemmas. (Basis: `source`, `execution`)
  - **Fixed-point convergence (`relaxLoop_converges_valid`)**: Fails if relaxation can shrink items non-monotonically or oscillate with `p2align`/island deadlines. (Basis: `derived`, `execution`)
- **`unsupported`**:
  - **`bv_decide`, `native_decide`, `@[extern]`, `partial def`, and `sorry`** inside trusted verification modules (`TrustedBoundary.lean:529-535, 1615-1617`). (Basis: `source`)
  - Unannotated self-modifying code and silent external linker instruction-length relaxations outside `Form.Encoded`. (Basis: `derived`)

## Evidence

### Pinned Upstream Repositories and Peer-Reviewed Papers

| Source / Artifact | Pin / DOI | Inspected Scope | Basis |
| :--- | :--- | :--- | :--- |
| `bytecodealliance/wasmtime` | `4eec6994d538397a5170c782548631483fbbb87b` | `Cargo.toml:192-196`; `cranelift/isle/veri/{veri,isaspec,aslp}`; `cranelift/codegen/src/{machinst/{mod,vcode,buffer,reg}.rs,isa/{unwind,x64/inst/emit,aarch64/inst/emit}.rs}` | `source` |
| `AbsInt/CompCert` | `2685140bf72c959446981fb99b5e44a8975021bc` | `driver/Compiler.v:28-29,231-260`; `backend/{Selection,Selectionproof,Mach}.v`; `x86/Asm.v`; `aarch64/Asm.v` | `source` |
| `CakeML/cakeml` | `2874b664e10939a3ee462215b2e068c89c1f70eb` | `compiler/backend/{word_to_stackScript.sml,labLangScript.sml,lab_to_targetScript.sml,semantics/targetSemScript.sml}` | `source` |
| `opencompl/lean-mlir` | `b8c4a771319a044854a4bbb49b8821381ef86ff8` | `lakefile.toml:2`; `LeanMLIR/LeanMLIR/{Framework.lean,Framework/Refinement.lean:24-35,95-110}` | `source` |
| `opencompl/riscv-lean` | `0e3365ac7b670d79d70e9b4a8b7fba782607c44f` | `RISCV/{Instructions.lean:109-110,SailToRV64.lean:98-106}` | `source` |
| `rems-project/sail` | `97aa617dcd4d01575f773cb58ea1e8686858c8c2` | `src/sail_lean_backend/{pretty_print_lean.ml,sail_plugin_lean.ml}` | `source` |
| `llvm/llvm-project` | `27825e751662497914dac447753f6d8daca974ff` | `CodeGen/{MachineInstr.h:89-139,MachineOperand.h:51-199,SelectionDAGISel.h}`; `GlobalISel/{InstructionSelector,LegalizerInfo,GenericMachineInstrs,RegBankSelect}.h` | `source` |
| `rust-lang/rust` | `560abf7946ae41fd210edac5dfe829d7eff86eec` | `compiler/rustc_codegen_ssa/src/traits/asm.rs:13-66`; `compiler/rustc_codegen_llvm/src/asm.rs:184-271` | `source` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean:529-535,1615-1617` | `source` |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Local `Lean 4.34.1` execution | `execution` |
| VanHattum et al. (ASPLOS 2024) | `DOI: 10.1145/3617232.3624862` | Crocus / VeriISLE modular Wasm-to-native verification | `documentation` |
| McLoughlin et al. (OOPSLA2 2025) | `DOI: 10.1145/3764383` | Arrival ISel verification against authoritative ISA semantics | `documentation` |
| Gourdin et al. (OOPSLA2 2023) | `DOI: 10.1145/3622799` | Chamois-CompCert `BTL` block simulations | `documentation` |
| Tan et al. (JFP 2019) | `DOI: 10.1017/S0956796818000229` | Verified CakeML compiler backend | `documentation` |

### Support Artifacts (`support/`) & Related Corpus Reports

- [`support/minimach_unified_probe.lean`](support/minimach_unified_probe.lean) (`30,350` B, `760` lines): Standalone Lean `4.34.1` toy formalization proving all `12` `#print axioms`-audited theorems (`0` `sorryAx`, `0` `Lean.ofReduceBool`).
- [`support/rustc_minimach_seam_probe.py`](support/rustc_minimach_seam_probe.py) (`24,066` B, `642` lines): `rustc 1.98.0-nightly` + `GNU objdump 2.47` ELF64 probe, direct byte-codec checker, `6/6` mutant suite, and Lean runner.
- [`support/probe_results.json`](support/probe_results.json) (`5,446` B): Execution output (`173.22 ms` `rustc`, `2,704` B `.o`, `4889f84801f031f0c3`, `6/6` mutants, `15,720.93 ms` Lean).
- Peer reports: [`isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026`](../isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026/REPORT.md) and [`selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality`](../selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality/REPORT.md).

## Revalidation

```bash
# 1. Execute rustc ELF64 probe + 6/6 mutant suite + Lean 4.34.1 kernel check
python3 support/rustc_minimach_seam_probe.py --out support/probe_results.json

# 2. Verify Lean axioms directly (expect exit 0, zero sorryAx / ofReduceBool)
lean support/minimach_unified_probe.lean

# 3. Validate corpus schema, links, and tests from the corpus root
cd ../..
python3 tools/reference.py catalog
python3 tools/reference.py check
python3 -m unittest discover -s tests -v
```
