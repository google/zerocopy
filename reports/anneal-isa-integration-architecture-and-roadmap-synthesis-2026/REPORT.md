# Anneal ISA Integration Architecture and Roadmap Synthesis: Bridging Rust MIR Refinement, Trusted Boundary Invariants, and Lean 4 Machine-Code Semantics

## Summary

Integrating inline (`core::arch::asm!`) and out-of-line (`core::arch::global_asm!`, external `.s`/`.o`) assembly verification into Anneal (`joshlf/anneal-private`) faces a fundamental architectural tension: **full instruction-set architecture (ISA) specifications are 10,000–150,000 lines of machine-generated or hand-written decode/execute logic, whereas Anneal's entire trusted computing base (`trusted/lean/Trusted/`) is ~560 lines of human-auditable Lean 4 code governed by `TrustedBoundary.lean`.** Importing a monolithic ISA model (`leanprover/LNSym`, `rems-project/sail-tiny-arm-lean`, or `opencompl/riscv-lean`) directly into `trusted/` would expand Anneal's trusted kernel by two orders of magnitude and make human line-by-line auditing impossible.

This report synthesizes a **Split Contract-and-Trace Bridge Architecture**—mechanized end-to-end in `support/AnnealIsaBridgeSynthesis.lean` (2,289 lines of standalone Lean 4.34.1 code, zero `sorryAx`, zero custom axioms)—that resolves this tension while preserving every invariant of Anneal's 5-layer architecture:

1. **Minimal `@[candidate inline_asm]` Trusted Boundary Extension (~140 LOC in `trusted/`)**:
   Instead of embedding an ISA instruction decoder inside `trusted/lean/Trusted/`, `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` add only the **Rust `asm!` boundary contract**:
   - `PhysReg`, `RegClass` (`.fixed r`, `.gpr`), `AsmOperand` (`.inReg`, `.outReg`, `.inoutReg`), `InlineAsmOptions` (`pure_`, `nomem`, `readonly`, `preserves_flags`, `nostack`, `noreturn`), `AsmAccessEvent` (`.readNA`, `.writeNA`, `.atomicLoad`, `.stackTouch`), `AsmContract`, and `Terminator.inlineAsm`,
   - `evalInlineAsm` (`BridgeTransition`), which evaluates MIR input operands left-to-right, demonically quantifies (`StepResult.choice .demonic`) over **every valid non-aliasing physical register allocation** (`validRegAllocs`) and **unconstrained caller register/flag seeds**, checks post-execution register preservation (`checkRegisterPreservation`), and replays the assembly block's `AsmAccessEvent` trace (`replayAsmEvents`) against `MemState` (`readNA`, `writeNA`, `visibleAtomicMsgs`, alignment, spatial footprint, and `options(nomem | readonly | nostack)`).
2. **Untrusted ISA Backends Live Entirely in `theory/Anneal/Isa/` (0 Trusted LOC)**:
   Concrete ISA instruction decoders, `BitVec` semantics, monadic effects, and symbolic simulators reside in `theory/` (outside the TCB) and prove refinement/equivalence into the `@[candidate inline_asm]` event-trace contract:
   - **Backend 1 (`AeneasVerif/kraken` pattern)**: Structured assembly AST (`KrakenInst`) paired with a tightened `StrictObserve` memory discipline (`kraken_strict_observe_eq_kernel1`), correcting Kraken's permissive `MemModel.All` (which we prove unsound for Anneal's UB model on unaligned or out-of-footprint accesses in `kraken_all_unsound_on_unaligned_or_oob`).
   - **Backend 2 (`leanprover/LNSym` + `cslib-community/bignum` pattern)**: Byte-decoded `BitVec 32` AArch64 machine words (`[0xf9400002#32, 0x8b010002#32, 0xf9000002#32]`) with `Component` read/write lens orthogonality (`regComponent_orthogonal`) and `UArchEvent` constant-time side-channel traces (`bignum_lnsym_words_eq_kernel1`).
   - **Backend 3 (`rems-project/sail` + `lean-sail` + `archsem-lean` + `opencompl` pattern)**: Two-tier architecture bridging Tier-1 monadic `FreeM SailEffect` execution (`readReg`, `writeReg`, `readMem`, `writeMem`, `barrier`) to Tier-2 pure `BitVec 64` instruction summaries (`sail_tier1_equiv_tier2_summary`) amenable to `simp` and `bv_decide`.
3. **End-to-End Multi-Block Rust MIR + `asm!` Crate Verification and Negative Canaries**:
   We verify a complete 4-block Rust MIR function `checked_mmio_accum(ptr: &mut usize, delta: usize) -> usize` combining safe Rust branching (`switchInt`), safe pointer dereference (`Rvalue.deref`), and an inline AArch64 `ldr`/`add`/`str` `Terminator.inlineAsm` block across all 24 valid register allocations and 2 background register seeds (`verify_crate_with_inline_asm`, `non_vacuity_at_every_depth`), and prove 5 negative adequacy canaries (`canary_undeclared_clobber_ub`, `canary_readonly_write_ub`, `canary_nomem_read_ub`, `canary_unaligned_access_ub`, `canary_demonic_reg_aliasing_ub`) showing that any violation of Rust Reference `[asm.*]` rules steps to `StepResult.failed .ub` and refutes `MirLang.WellFormedOn`.

---

## Applicability

This report applies to:

- **Anneal (`joshlf/anneal-private`)** at commit `42f4571d761b46c7142815f38b69c3781b3555e3` (`skeleton` worktree), specifically:
  - Layer 1A (`trusted/lean/Trusted/Refinement.lean`, `theory/Anneal/Refinement.lean`): `FailureKind`, `Termination`, `Outcome`, `TracePrefix`, `Language`, `Compiler.SoundOn`, `Compiler.Verified`, `TCBItem`, `Crate`, and `CrateTheorem`.
  - Layer 1B (`trusted/lean/Trusted/StepResult.lean`, `theory/Anneal/StepResult.lean`): `ChoiceKind` (`.demonic`, `.angelic`), `StepResult`, `SmallStepMachine`, `ReachesPrefix`, `SmallStepLang`, and `TotalStep`.
  - Layer 2 (`trusted/lean/Trusted/Memory.lean`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/MirLemmas.lean`): `MemState` (`curView`, `atomicMsgs`, `naVal`, `naWriteTs`, `naReadTs`), `MirVal`, `Place`, `Operand`, `Rvalue`, `Statement`, `Terminator`, `MirBody`, `MirState`, `evalMirStep`, and `SafeAndReturns`.
  - Layer 3 (`theory/Anneal/FunctionalTranslation.lean`): `FuncLang`, `AeneasRes`, and hybrid functional/operational simulation.
  - Trusted Boundary Audit (`trusted/audit/TrustedBoundary.lean`): `@[tcb_item]`, `@[candidate <feature>]`, and automated declaration auditing.
- **Lean 4 (`leanprover/lean4`)** at `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Rust Inline Assembly (`core::arch::asm!`, `core::arch::global_asm!`)** as lowered by `rustc` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `rustc_middle::mir::TerminatorKind::InlineAsm`) and specified in *The Rust Reference* (`82da570bafd9efed421bdbae0f8603ede8dd308b`, Section `inline-assembly.md`, clauses `[asm.register-preservation]`, `[asm.options.pure]`, `[asm.options.nomem]`, `[asm.options.readonly]`, `[asm.options.preserves_flags]`, `[asm.options.nostack]`, `[asm.options.noreturn]`).
- **Sixteen Examined ISA and Machine-Code Verification Ecosystems**:
  - Lean 4 ISA models: `AeneasVerif/kraken` (`c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`), `leanprover/kraken` (`8af78062037bc237b341d20252aafd1797c1bcb7`), `leanprover/LNSym` (`5c05220ff970e3bdd7813ad0c9ef3741522c8b92`), `cslib-community/bignum` (`92dc3ee58280db51bbbb4dd51b85a91abd0178ba`), `rems-project/sail` (`0f51056900af85d0b18928d6ea2d2271d18184e8`), `rems-project/lean-sail` (`1e5b216bf881ef08da160db63b44ecda430802d6`), `rems-project/archsem-lean` (`318583a5f2052c039c25dfd69a3beec0b0a27090`), `rems-project/sail-tiny-arm-lean` (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`), `opencompl/riscv-lean` (`7c6b500c1744f40d928fb131125cd06edf9f4fce`), `opencompl/lean-mlir` (`b8c4a771319a044854a4bbb49b8821381ef86ff8`), and `BasisResearch/ship-your-interpreter` (`fb07094cff916318c34b07494a7d739f1e53989b`).
  - External theorem-prover / compiler benchmarks: `awslabs/s2n-bignum` (`9f2cd960e11892a582e7facb0c191b4a2959ea91`), `rems-project/archsem` (`42204d87df2e7d20e5ec23deb8ba8220e65148ab`), `rems-project/islaris` (`c978e10f50db5c40f0fdf113f5f76a779782c6f9`), `AbsInt/CompCert` (`74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`), `jasmin-lang/jasmin` (`34f15840f10625bbc2cbf59b3d877e94c75bfbd9`), and `project-everest/vale` (`bbae0eb89143734363b14a77642dbf8dec36e288`).

---

## Findings

### 1. Eight-Axis Master Comparison Matrix Across 16 ISA Formalization Ecosystems

`Basis: direct source inspection of all 16 repositories + execution of Lean 4.34.1 synthesis artifact`

To evaluate which architectural mechanisms belong in Anneal's trusted core (`trusted/`) versus its untrusted proof library (`theory/`), Table 1 compares all 16 examined ISA and assembly verification frameworks across 8 engineering axes:
1. **ISAs & Coverage**: Target architectures and instruction subset breadth.
2. **Instruction Representation**: Byte-level `BitVec` decode vs. structured assembly AST vs. SSA dialect.
3. **State & Lens Encoding**: Flat product struct vs. total register map vs. orthogonal `Component` lens hierarchy.
4. **Execution & Nondeterminism Model**: Pure total step vs. `Option`/`Except` vs. free monad (`FreeM`) vs. relational Prop.
5. **Memory & Concurrency Model**: Flat total byte map (`BitVec 64 → UInt8`) vs. allocation-tracked `MemModel` vs. timestamped weak-memory views (`ArchSem` / `MemState`).
6. **Proof Automation**: Symbolic simulation tactic (`symstep`, `sym_n`, `ARM_STEPS_TAC`) vs. bit-blasting (`bv_decide`) vs. separation logic (`Iris`).
7. **Hardware / Reference Validation**: Authoritative vendor specification generation (Arm ASL / Sail) vs. hardware/QEMU differential testing vs. hand-transcription.
8. **Anneal Integration Fit & TCB Impact**: Where the framework fits in Anneal's architecture and what TCB cost it would incur if trusted.

| Framework (`owner/repo @ sha`) | 1. ISAs & Coverage | 2. Instruction Representation | 3. State & Lens Encoding | 4. Execution & Nondeterminism | 5. Memory & Concurrency | 6. Proof Automation | 7. Hardware Validation | 8. Anneal Fit & TCB Impact |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`AeneasVerif/kraken`** (`c9aa45ee1b`) & **`leanprover/kraken`** (`8af7806203`) | AArch64 (scalar + NEON SIMD), RV32I | Structured assembly AST (`Inst`, `Program := Addr → Option Inst`) — no byte decoder | `MachineState` with `Regs`, `Flags` (`NZCV`), `Mem`, `PC` | Relational `Step : MachineState → MachineState → Prop` + executable `step?` | Pluggable `MemModel`: `.All` (total byte map, permissive) vs `.Allocated` (tracked footprint) | Custom `symstep` / `symsteps` + `omega` + `bv_decide`; direct Aeneas `Result` bridge | Hand-transcribed ISA subset; tested on curve25519 / ML-KEM | **Stage 1 (`theory/Anneal/Isa/KrakenBridge.lean`)**: Ideal for structured `asm!` templates; **must replace `MemModel.All` with `StrictObserve`** |
| **`leanprover/LNSym`** (`5c05220ff9`) | AArch64 (user-mode scalar + SIMD/crypto subset: AES, SHA-512, GCM) | Byte-decoded `BitVec 32` machine words (`decode_bitvec : BitVec 32 → Option ArmInst`) | `ArmState`: `gpr : BitVec 5 → BitVec 64`, `sfp : BitVec 5 → BitVec 128`, `pstate`, `pc`, `mem`, `program`, `error` | Total function `stepi : ArmState → ArmState` embedding errors in `ArmState.error` (`None` vs `Some err`) | Flat byte map `BitVec 64 → BitVec 8` with `mem_separate` range disjointness lemmas; sequential only | `sym_n` tactic driving `SymContext` symbolic evaluation + `bv_decide` | Validated via ELF cosimulation on physical AArch64 Linux hosts | **Stage 2 (`theory/Anneal/Isa/BignumLNSymBridge.lean`)**: Proven Lean 4 byte-level AArch64 decoder; ~35k LOC so **must stay in `theory/`** |
| **`cslib-community/bignum`** (`92dc3ee582`) | AArch64 scalar + multi-precision arithmetic subset | Byte-decoded `BitVec 32` words + `Fetch` relation from byte memory | Compositional **`Component S A`** lens (`read : S → A`, `write : S → A → S`) with `Orthogonal c₁ c₂` | Relational + functional `Next` and `Eventually` Hoare-triple reachability | Byte-addressed memory exposed as a parameterized `bytes64 addr : Component ArmState (BitVec 64)` lens | Lens-rewriting `simp` sets (`Component.read_write_same`, `read_write_orthogonal`) + `bv_decide` | Direct Lean 4 port of `awslabs/s2n-bignum` | **Stage 2 (`theory/Anneal/Isa/BignumLNSymBridge.lean`)**: Best-in-class **`Component` lens abstraction** and **`UArchEvent` constant-time trace** |
| **`awslabs/s2n-bignum`** (`9f2cd960e1`) | AArch64 + x86-64 (production crypto primitives: Montgomery, NTT, Ed25519, P-256/384/521) | Byte-decoded instruction streams in HOL Light (`arm_decode`, `x86_decode`) | Compositional `component` lenses (`rvalue`, `assign`, `orthogonal`) | Relational step + `ensures` Hoare triples with frame conditions (`MAYCHANGE`) | Flat byte-addressed memory with explicit ` aligned_bytes_loaded` and disjoint frame predicates | `ARM_STEPS_TAC` / `X86_STEPS_TAC` + `WORD_BLAST` + `BIGNUM_TERMRANGE_TAC` | Production CI against object files + constant-time microarchitectural leakage model | Reference blueprint for **frame-condition specifications (`MAYCHANGE`)** and **constant-time `UArchEvent` leakage proofs** |
| **`rems-project/sail`** (`0f51056900`) + **`lean-sail`** (`1e5b216bf8`) | Arm-A (v8.5–v9.4 ASL-derived), RISC-V (`sail-riscv`), CHERI-MIPS, x86 | Official vendor/committee bitpattern clauses compiled to Lean 4 `match` / bit-extractors | Generated `Register` inductive + `RegType : Register → Type` dependent register map | Free monad `PreSailM RegisterType TrivialChoice Exception := FreeM (Effect ...)` | Monadic `mem_read` / `mem_write` / `barrier` effects (uninterpreted until instantiated) | Requires unfolding large monadic definitions unless summarized into Tier-2 pure rules | **Gold-standard ISA fidelity**: generated directly from authoritative Arm ASL / RISC-V Sail specs | **Stage 3 Tier 1 (`theory/Anneal/Isa/SailArchSemBridge.lean`)**: Authoritative ground truth; **must be paired with Tier-2 pure `BitVec` summaries** |
| **`rems-project/archsem-lean`** (`318583a5f2`) & **`archsem`** (`42204d87df`) | Arm-A, RISC-V (via `lean-sail` `ArchSem.Interface`) | Consumes `ISem` monadic instruction semantics from `lean-sail` | `RegMap` (`(r : Reg) → RegType r`) + candidate execution graphs | `IMon` (`Outcome` free monad with `RegRead`, `RegWrite`, `MemRead`, `MemWrite`, `Barrier`, `Choice`, `Abort`) | Operational & axiomatic weak-memory concurrency (`umpaLumpa`, promising, Arm-v8 / RVWMO) | Execution-graphenumeration + monadic trace reduction | Validated against `litmus` hardware concurrency tests | **Stage 3 Concurrency Bridge**: `IMon` effects map 1-to-1 onto Anneal's `AsmAccessEvent` (`readNA`, `writeNA`, `atomicLoad`) and `MemState` views |
| **`rems-project/sail-tiny-arm-lean`** (`4a474cfc41`) | AArch64 representative subset (`LDR`, `STR`, `ADD`, `EOR`, `B`, barriers, page tables) | Sail-compiled `decodeExecute : BitVec 32 → PreSailM ...` | Dependent `Register → Type` (`R0`..`R30`, `SP`, `PC`, `PSTATE`) | `PreSailM` free monad over `lean-sail` | `mem_read` / `mem_write` / `barrier` effects consumed by `archsem-lean` | Monadic bind reduction (`simp`) on concrete opcodes | Compiled directly from REMS `sail-tiny-arm` specification | Concrete working prototype of the `sail` → `lean-sail` → `archsem-lean` pipeline in Lean 4 |
| **`opencompl/riscv-lean`** (`7c6b500c17`) + **`lean-mlir`** (`b8c4a77131`) | RV64IM (base 64-bit integer + multiplication/division) | `Com RV64` typed SSA dialect in `lean-mlir` (`Intrinsic` ops per RV64 instruction) | SSA valuation contexts (`Valuation Γ`) over `BitVec 64` | Pure total denotational semantics (`denote : Op → HVector → BitVec 64`) | Pure register/ALU focus; memory operations modeled via external SSA effects | **Best-in-class `bv_decide` automation**: 1-line bitvector refinement proofs (`rfl` / `bv_decide`) | Differential testing + SMT/SAT bit-blasting certificates | **Stage 3 Tier 2 (`theory/Anneal/Isa/SailArchSemBridge.lean`)**: Blueprint for **pure `BitVec` instruction summaries** discharged by `bv_decide` |
| **`BasisResearch/ship-your-interpreter`** (`fb07094cff`) | RV32I | Pure `BitVec 32` pattern-matching decoder (`decode : BitVec 32 → Option Instr`) | Flat struct `Cpu` (`regs : Array UInt32`, `pc : UInt32`, `mem : ByteArray`) | Executable `StateM Cpu` / pure step function compiled to native C via Lean 4 FFI | Flat `ByteArray` RAM | Executable differential testing rather than symbolic proofs | **C-FFI differential fuzzing** against `spike` / reference C emulators at MHz speeds | Blueprint for **fast C-FFI differential validation** of Lean 4 ISA decoders against hardware/emulators |
| **`rems-project/islaris`** (`c978e10f50`) | AArch64, RISC-V (full Sail ISA coverage via Isla) | **Per-instruction SMT/Isla symbolic execution traces** exported to Coq/Rocq AST (`isla_trace`) | Iris ghost state (`r ↦ᵣ v`, `a ↦ₘ w`) per register and memory word | Nondeterministic trace branching (`Smt`, `Assume`, `ReadReg`, `WriteReg`, `ReadMem`, `WriteMem`) | Iris separation logic over byte-addressed memory + MMIO specs | Automated Iris weakest-precondition (`wp_instr`) over compact Isla traces | Inherits full Arm ASL / Sail fidelity via `isla-footprint` without importing 150k-line decoder into proof assistant | **Crucial architectural insight**: per-block/per-instruction event traces decouple the core proof assistant from the 150k-line Sail decoder |
| **`AbsInt/CompCert`** (`74cbdbf0e8`) | x86-64, AArch64, RISC-V, PowerPC, ARM32 | Structured `Asm.instruction` AST + `EF_inline_asm` / `builtin_ais_annot` | `regset := preg → val` (`Vint`, `Vlong`, `Vptr b ofs`, `Vundef`) | Small-step labeled transition system (`step : state → trace → state → Prop`) | **Block-offset memory model (`Mem.mem`)** shared identically across C (`Clight`), IR (`RTL`), and `Asm` | Simulation diagrams (`forward_simulation`, `backward_simulation`) | Industry gold standard for verified C compilation (`Val.lessdef`, `Mem.extends`) | **Crucial architectural insight**: sharing the **exact same `MemState`** across source MIR and assembly avoids unprovable byte-flattening memory isomorphisms |
| **`jasmin-lang/jasmin`** (`34f15840f1`) | x86-64 (scalar + AVX2), AArch64, ARMv7 | Structured assembly-like source (`reg`, `stack`, `inline`) compiled to Coq/EasyCrypt | Split local variables vs architectural registers/flags | Small-step operational semantics instrumented with **leakage traces (`Leakage`)** | Flat byte memory (`WArray`) + explicit stack allocation | EasyCrypt relational Hoare logic + Coq compiler correctness | Hardware-validated cryptographic assembly (`libjade`) | Blueprint for **constant-time security (`leak_addr`, `leak_branch`)** via trace instrumentation |
| **`project-everest/vale`** (`bbae0eb891`) | x86-64, AArch64 | Structured assembly procedures with inline ghost annotations (`procedure`, `requires`, `ensures`) | Explicit register/flag/memory fields in `va_state` | Weakest-precondition (`va_wp`) transformer over big-step procedure summaries | Explicit heaplets / typed memory buffers (`mem64`, `buffer128`) | SMT-backed VC generation (F* / Dafny) with framing lemmas | Verified production TLS/crypto assembly (EverCrypt / HACL*) | Blueprint for **compositional procedure summaries** that lift straight-line assembly blocks into pure functional transformers |

---

### 2. Concrete `trusted/` vs `theory/` Integration Architecture for `joshlf/anneal-private`

`Basis: direct inspection of joshlf/anneal-private @ 42f4571d761b46c7142815f38b69c3781b3555e3 + machine-checked proof in support/AnnealIsaBridgeSynthesis.lean`

#### 2.1 Why Monolithic ISA Models Cannot Enter `trusted/lean/Trusted/`

In `joshlf/anneal-private` at `42f4571d761b46c7142815f38b69c3781b3555e3`, the entire trusted verification kernel consists of five files totaling **561 lines of Lean 4**:
- `trusted/lean/Trusted/Refinement.lean` (154 lines)
- `trusted/lean/Trusted/StepResult.lean` (100 lines)
- `trusted/lean/Trusted/Memory.lean` (77 lines)
- `trusted/lean/Trusted/MirAst.lean` (91 lines)
- `trusted/lean/Trusted/MirSemantics.lean` (139 lines)

Furthermore, `trusted/audit/TrustedBoundary.lean` enforces four hard invariants over every declaration in `trusted/lean/Trusted/`:
1. **Zero `sorryAx` and zero user `axiom`s**: Every declaration in `trusted/` must be a total definition or inductive type.
2. **Zero `unsafe`, `partial`, or `@[extern]` declarations**: All step functions (`evalMirStep`, `evalMirStmt`, `evalMirTerminator`) must be kernel-reducible total functions so that `SmallStepLang` (`ReachesPrefix`) is defined purely inductively.
3. **Explicit `@[tcb_item]` and `@[candidate <feature>]` annotation**: Any experimental extension to the MIR AST or operational semantics must be tagged `@[candidate <feature>]` so `TrustedBoundary.lean` inventories its exact footprint.
4. **Shared `MemState` without unverified memory marshaling**: `MirState.mem : MemState` models memory as abstract locations (`loc : Nat`) with non-atomic values (`naVal : Nat → Option MirVal`), happens-before read/write timestamps (`naReadTs`, `naWriteTs`), and an append-only message pool (`atomicMsgs : List AtomicMsg`) for C++20/Rust release-acquire atomics.

If Anneal were to import `leanprover/LNSym` (~35,000 LOC) or `rems-project/sail-tiny-arm-lean` + `lean-sail` (~15,000–150,000 LOC) directly into `trusted/lean/Trusted/`:
- The trusted kernel would grow from 561 lines to >35,000 lines, violating Anneal's foundational design principle that `trusted/` is small enough to be audited line-by-line by a human reviewer.
- A flat byte-array memory model (`BitVec 64 → UInt8`, as used in `Kraken`'s `MemModel.All` and `LNSym`) would conflict with Anneal's timestamped `MemState`, requiring either a trusted memory marshaling axiom or forfeiting happens-before race detection and allocation-bounds checking.

#### 2.2 The Split Contract-and-Trace Bridge Architecture

```
┌───────────────────────────────────────────────────────────────────────────────────┐
│                 TRUSTED KERNEL: trusted/lean/Trusted/ (~140 new LOC)              │
│                                                                                   │
│  Trusted/MirAst.lean (@[candidate inline_asm]):                                   │
│    • PhysReg (.x0..x3, .sp, .nzcv), RegClass (.fixed r, .gpr)                     │
│    • AsmOperand (.inReg, .outReg, .inoutReg), InlineAsmOptions                    │
│    • AsmAccessEvent (.readNA, .writeNA, .atomicLoad, .stackTouch)                 │
│    • AsmContract (kernel, operands, clobbers, options, allowedFootprint)          │
│    • Terminator.inlineAsm (contract : AsmContract) (target : Option BlockId)      │
│                                                                                   │
│  Trusted/MirSemantics.lean (@[candidate inline_asm]):                             │
│    • evalInlineAsm (BridgeTransition):                                            │
│        1. Evaluate MIR input operands left-to-right (UB on uninit local)          │
│        2. Demonic choice (StepResult.choice .demonic) over ALL valid              │
│           non-aliasing physical register allocations (validRegAllocs)             │
│           and unconstrained caller register/flag seeds (initRegSeeds)             │
│        3. Check post-state register preservation (checkRegisterPreservation)      │
│        4. Replay AsmAccessEvent trace against MemState (replayAsmEvents),         │
│           enforcing options(nomem|readonly|nostack), alignment, footprint,        │
│           and happens-before view checks; write output registers to MirState      │
└─────────────────────────────────────────▲─────────────────────────────────────────┘
                                          │
                 Pure Lean 4 Refinement / Equivalence Theorems (0 TCB Cost)
                                          │
┌─────────────────────────────────────────┴─────────────────────────────────────────┐
│                UNTRUSTED THEORY LIBRARY: theory/Anneal/Isa/                       │
│                                                                                   │
│  ┌─────────────────────────┐ ┌─────────────────────────┐ ┌──────────────────────┐ │
│  │ Stage 1: KrakenBridge   │ │ Stage 2: BignumLNSym    │ │ Stage 3: SailArchSem │ │
│  │ • Structured KrakenInst │ │ • BitVec 32 AArch64     │ │ • Tier-1 FreeM       │ │
│  │ • StrictObserve memory  │ │   decode & execution    │ │   SailEffect monad   │ │
│  │   discipline (rejects   │ │ • Component S A lenses  │ │ • Tier-2 pure BitVec │ │
│  │   unaligned/OOB access) │ │   & Orthogonality       │ │   summary + bv_decide│ │
│  │ • symstep tactic        │ │ • UArchEvent CT trace   │ │ • ArchSem weak mem   │ │
│  └─────────────────────────┘ └─────────────────────────┘ └──────────────────────┘ │
└───────────────────────────────────────────────────────────────────────────────────┘
```

#### 2.3 Exact Blueprint for `trusted/lean/Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`

In `support/AnnealIsaBridgeSynthesis.lean` (Sections 3–4, lines 488–1112), we mechanize the exact `@[candidate inline_asm]` additions to `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`:

1. **Physical Registers & Register Classes (`Trusted/MirAst.lean`)**:
   ```lean
   inductive PhysReg where
     | x0 | x1 | x2 | x3 | sp | nzcv
     deriving DecidableEq, Repr

   inductive RegClass where
     | fixed (reg : PhysReg) -- e.g. `in("x0") v` or `out("x2") _`
     | gpr                   -- e.g. `in(reg) v`, allocated demonically by rustc
     deriving DecidableEq, Repr
   ```
   Crucially, `RegClass.gpr` permits `.x0`, `.x1`, `.x2`, `.x3` while excluding `.sp` and `.nzcv` (matching the Rust Reference rule that `reg` operands are allocated from general-purpose registers, never the stack pointer or flags register).

2. **Rust `asm!` Operands, Options, and Memory/Barrier Events (`Trusted/MirAst.lean`)**:
   ```lean
   inductive AsmOperand where
     | inReg (cls : RegClass) (src : Operand)
     | outReg (cls : RegClass) (dst : Option Place) -- `none` for `out(reg) _` lateout clobber
     | inoutReg (cls : RegClass) (src : Operand) (dst : Option Place)
     deriving DecidableEq, Repr

   structure InlineAsmOptions where
     pure_ : Bool := false
     nomem : Bool := false
     readonly : Bool := false
     preserves_flags : Bool := false
     nostack : Bool := false
     noreturn : Bool := false
     deriving DecidableEq, Repr

   inductive AsmAccessEvent where
     | readNA (loc : Nat) (width : Nat) (val : Nat)
     | writeNA (loc : Nat) (width : Nat) (val : Nat)
     | atomicLoad (loc : Nat) (width : Nat) (ord : AtomicOrder) (bits : Nat) (ts : Timestamp)
     | stackTouch
     deriving DecidableEq, Repr
   ```

3. **Normative Rust Reference `[asm.*]` Checks in `evalInlineAsm` (`Trusted/MirSemantics.lean`)**:
   Every normative rule of *The Rust Reference* (`inline-assembly.md`) is enforced operationally in `evalInlineAsm` (`support/AnnealIsaBridgeSynthesis.lean`, lines 860–1105):
   - **Left-to-right input operand evaluation**: `evalAsmOperands` evaluates `.inReg` and `.inoutReg` `Operand`s before entering the assembly kernel; reading an uninitialized local returns `none` and transitions immediately to `StepResult.failed .ub`.
   - **Demonic register allocation (`validRegAllocs`)**: For `.gpr` operands (`in(reg)`, `out(reg)`, `inout(reg)`), `rustc`'s register allocator may assign *any* pairwise-distinct tuple of general-purpose registers `alloc : List PhysReg`. If an assembly block hardcodes a scratch register (e.g., `.x2`) without pinning the inputs away from `.x2`, at least one valid allocation assigns an `in(reg)` operand to `.x2`. Because `evalInlineAsm` fails to `.failed .ub` if *any* `(alloc, seed)` branch fails (`results.any Option.isNone`), register-aliasing bugs are caught automatically (proved in `canary_demonic_reg_aliasing_ub`).
   - **Demonic unconstrained register/flag initialization (`initRegSeeds`)**: Registers not bound by `.inReg`/`.inoutReg` operands (including `.sp`, `.nzcv`, and unallocated GPRs) cannot be assumed to hold `0` on entry. `allAsmBranches` tests each register allocation against multiple distinct background register seeds (`[0, 0xdeadbeef]`).
   - **Register preservation (`[asm.register-preservation]`, `checkRegisterPreservation`)**: Every register `r ∈ allPhysRegs` that is not an `.outReg`/`.inoutReg` destination, not listed in `contract.clobbers`, and not `.nzcv` when `preserves_flags = false` must satisfy `post.regs r == pre.regs r`. Violating this (e.g., modifying `.x3` or `.sp` without restoring it, or modifying `.nzcv` under `options(preserves_flags)`) returns `none` → `.failed .ub` (proved in `canary_undeclared_clobber_ub`).
   - **Option and memory footprint discipline (`replayAsmEvents`)**:
     - Under `options(nomem)`, any `AsmAccessEvent` returns `none` → `.failed .ub` (proved in `canary_nomem_read_ub`).
     - Under `options(readonly)`, any `.writeNA` or `.stackTouch` returns `none` → `.failed .ub` (proved in `canary_readonly_write_ub`).
     - Under `options(nostack)`, any `.stackTouch` returns `none` → `.failed .ub`.
     - Every `.readNA loc width val`, `.writeNA loc width val`, and `.atomicLoad loc width ord bits ts` must satisfy natural alignment (`width > 0 && loc % width == 0`), caller spatial footprint (`(loc, width) ∈ contract.allowedFootprint`), and Anneal's `MemState` happens-before timestamp checks (`m.readNA loc`, `m.writeNA loc`, `m.visibleAtomicMsgs loc`). Unaligned or out-of-bounds accesses return `none` → `.failed .ub` (proved in `canary_unaligned_access_ub`).

---

### 3. Machine-Checked Synthesis Results (`support/AnnealIsaBridgeSynthesis.lean`)

`Basis: standalone Lean 4.34.1 verification (/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768 support/AnnealIsaBridgeSynthesis.lean), exit code 0, 0 sorryAx, 0 custom axioms`

The standalone file `support/AnnealIsaBridgeSynthesis.lean` (2,289 lines, SHA-256 `0aea81289fb1cc881a7e492796f0cd40035fb8498c560ad767550eff07ad2a70`) embeds Anneal's exact Layer 1A, Layer 1B, and Layer 2 definitions and proves 16 theorems across the three ISA backend styles, the multi-block mixed Rust MIR + `asm!` function, and the five negative adequacy canaries:

#### 3.1 Backend 1: `AeneasVerif/kraken` Structured Assembly AST & `MemModel.All` vs `StrictObserve`

In `AeneasVerif/kraken` (`c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`), `Kraken/Mem/Models.lean` defines two memory models: `MemModel.All` (where *every* 64-bit address is readable and writable without alignment or allocation checks) and `MemModel.Allocated` (which tracks an explicit allocated footprint).

In Section 5.1 of `support/AnnealIsaBridgeSynthesis.lean` (lines 1114–1268), we formalize both `KrakenMemMode.allPermissive` and our tightened `KrakenMemMode.strictObserve` (which requires `width > 0 && addr % width == 0 && (addr, width) ∈ allowedFootprint` and emits `AsmAccessEvent`s), and prove two foundational theorems:

- **`kraken_all_unsound_on_unaligned_or_oob` (lines 1208–1225)**:
  Proves that under `KrakenMemMode.allPermissive`, executing `[.str .x1 .x0 0]` at unaligned address `3` (`3 % 8 ≠ 0`) or out-of-footprint address `64` (`(64, 8) ∉ [(8, 8)]`) **succeeds** (`some st'`), whereas Anneal's `replayAsmEvents` **rejects** the resulting memory event (`none`, triggering `.failed .ub`). Thus `Kraken`'s default `MemModel.All` is unsound as a direct memory model for Anneal's UB-detecting operational semantics.
- **`kraken_strict_observe_eq_kernel1` (lines 1236–1268)**:
  Proves that for the 3-instruction AArch64 sequence `krakenAccumProg r_ptr r_delta r_out = [.ldr r_out r_ptr 0, .add r_out r_out r_delta, .str r_out r_ptr 0]`, whenever the pointer in `r_ptr` is 8-byte aligned and in `allowedFootprint`, `evalKrakenProg .strictObserve` produces `some st'` if and only if Anneal's `evalAsmKernel 1` produces `some st'`, with identical post-state registers and `AsmAccessEvent` trace.

#### 3.2 Backend 2: `leanprover/LNSym` + `cslib-community/bignum` Byte-Decoded `BitVec 32` Words, `Component` Lenses, and `UArchEvent` Constant-Time Traces

In Section 5.2 of `support/AnnealIsaBridgeSynthesis.lean` (lines 1270–1458), we combine `cslib-community/bignum`'s `Component S A` lens framework (`Component.Orthogonal`) and `UArchEvent` constant-time trace model with `leanprover/LNSym`'s byte-decoded `BitVec 32` AArch64 instruction semantics:

- **`regComponent_orthogonal` (lines 1306–1321)**:
  Proves that for any two distinct physical registers `r₁ ≠ r₂`, `regComponent r₁` and `regComponent r₂` are `Component.Orthogonal`: writing to `r₁` leaves `r₂` invariant (`read_write_other`) and writes to `r₁` and `r₂` commute (`write_write_comm`).
- **Concrete AArch64 Machine Code Decoding (`decodeAArch64Word`, lines 1337–1370)**:
  Decodes concrete 32-bit little-endian AArch64 instruction words (`BitVec 32`) by bitfield extraction (`word.extractLsb' 22 10`, `Rn := word.extractLsb' 5 5`, `Rm := word.extractLsb' 16 5`, `Rd := word.extractLsb' 0 5`):
  - `0xf9400002#32` → `ldr x2, [x0]` (`opc = 0b1111100101#10`, `Rn = 0`, `Rd = 2`),
  - `0x8b010042#32` → `add x2, x2, x1` (`opc = 0b10001011000#11`, `Rm = 1`, `Rn = 2`, `Rd = 2`),
  - `0xf9000002#32` → `str x2, [x0]` (`opc = 0b1111100100#10`, `Rn = 0`, `Rd = 2`).
- **`bignum_lnsym_words_eq_kernel1` (lines 1425–1458)**:
  Proves two properties simultaneously for `accumMachineWords = [0xf9400002#32, 0x8b010042#32, 0xf9000002#32]`:
  1. **Functional & Trace Equivalence**: Executing the byte-decoded `BitVec 32` machine words (`execAArch64Words accumMachineWords`) produces the **exact same `Option AsmMachineState`** (both register file and `AsmAccessEvent` list) as `evalAsmKernel 1 [.x0, .x1, .x2]`.
  2. **Constant-Time Microarchitectural Side-Channel Invariance (`uarchTrace`)**: For any secret input values `delta₁, delta₂ : Nat` in `.x1` and any secret memory contents `v₁, v₂ : Nat` at address `addr`, the microarchitectural leakage trace `uarchTrace : List UArchEvent` (`[.memRead addr 8, .aluRegOp, .memWrite addr 8]`) is **independent of `(delta, v)`** (`st₁.uarchTrace = st₂.uarchTrace`).

#### 3.3 Backend 3: `rems-project/sail` + `lean-sail` + `archsem-lean` + `opencompl` Two-Tier Architecture

In Section 5.3 of `support/AnnealIsaBridgeSynthesis.lean` (lines 1460–1602), we formalize the two-tier architecture that makes Sail-generated ISA specifications tractable in Lean 4:
- **Tier 1 (`FreeM SailEffect` over `BitVec 64`)**: Models `lean-sail`'s free monad (`SailEffect.readReg`, `.writeReg`, `.readMem`, `.writeMem`, `.barrier`, `.abort`) and `archsem-lean`'s `interpSailM` interpreter over `BitVec 64` registers and memory oracle.
- **Tier 2 (`sailAccumSummaryBv`, OpenCompl-style pure `BitVec 64` summary)**: A pure single-step summary over `BitVec 64` arithmetic (`BitVec.ofNat 64 loaded + st.regs r_delta`).
- **`sail_tier1_equiv_tier2_summary` (lines 1559–1602)**:
  Proves that interpreting the 7-bind monadic `sailAccumMonadic r_ptr r_delta r_out : FreeM SailEffect Unit` program under `interpSailM` is **extensionally equal** to the pure Tier-2 summary `sailAccumSummaryBv`, and that whenever `loaded + st.regs r_delta < 2^64`, lifting the `BitVec 64` state back to `Nat` via `BitVec.toNat` equals `evalAsmKernel 1`.

#### 3.4 Multi-Block Rust MIR + `asm!` End-to-End Verification (`checked_mmio_accum`)

In Sections 6–7 of `support/AnnealIsaBridgeSynthesis.lean` (lines 1604–2069), we verify a realistic 4-block Rust function mixing safe Rust control flow, safe pointer dereferences, and inline assembly:

```rust
pub fn checked_mmio_accum(ptr: &mut usize, delta: usize) -> usize {
    let is_zero = delta == 0;
    let out: usize;
    if is_zero {
        // bb2: Fast path in safe Rust (no write traffic if delta == 0)
        out = *ptr;
    } else {
        // bb1: Inline AArch64 assembly read-modify-write
        unsafe {
            core::arch::asm!(
                "ldr {tmp}, [{ptr}]",
                "add {tmp}, {tmp}, {delta}",
                "str {tmp}, [{ptr}]",
                ptr = in(reg) ptr,
                delta = in(reg) delta,
                tmp = out(reg) out,
                options(nostack, preserves_flags),
            );
        }
    }
    // bb3: Join block returning `out`
    out
}
```

- **`accum_one_branch_eq` & `evalInlineAsm_accum_all_branches` (lines 1679–1821)**:
  Because `ptr = in(reg) _1`, `delta = in(reg) _2`, and `tmp = out(reg) _4` all use `RegClass.gpr`, `validRegAllocs accumAsmContract.operands` generates all $4 \times 3 \times 2 = 24$ pairwise-distinct GPR triples `[r0, r1, r2]` from `{.x0, .x1, .x2, .x3}`, and `allAsmBranches` pairs each with 2 background register seeds (`0` and `0xdeadbeef`), yielding **48 demonic branches**. We prove that every single one of those 48 branches satisfies `checkRegisterPreservation` and `replayAsmEvents` and evaluates to the **exact same post-state** `some expectedNext` (`locals 4 = some (.usize (x0 + delta))`, `mem = m2`, `block = 3`, `stmtIdx = 0`)!
- **`checkedMmio_safe_and_returns` & `checkedMmioBody_refines_spec` (lines 1865–2038)**:
  Proves `SafeAndReturns checkedMmioBody init (.usize (x0 + delta))` and `MirSem checkedMmioBody ≤ EnsuresCheckedMmio` across both the `delta = 0` (`bb0 → bb2 → bb3`) and `delta ≠ 0` (`bb0 → bb1 (inlineAsm) → bb3`) paths.
- **`verify_crate_with_inline_asm` & `non_vacuity_at_every_depth` (lines 1660–1671, 2059–2069)**:
  Discharges the top-level `CrateTheorem checkedMmioCrate` (`WellFormedOn PreCheckedMmio` + `EnsuresCheckedMmio`) and proves concrete witness reachability at step budgets `1..6` (`non_vacuity_at_every_depth`, which depends on **zero axioms**—pure kernel computation!).

#### 3.5 Five Negative Adequacy Canaries (Section 8, lines 2070–2219)

To ensure our `@[candidate inline_asm]` semantics is never vacuously permissive, Section 8 proves five negative adequacy canaries from the canonical valid initial state `canaryInitState`:

| Canary Theorem | Violated Rust Reference Rule | Contract Defect | Machine-Checked Outcome |
| :--- | :--- | :--- | :--- |
| **`canary_undeclared_clobber_ub`** | `[asm.register-preservation]` | Kernel 10 increments `.x3` when `clobbers = []` | Steps to `.failed .ub` at budget 1 & refutes `MirLang.WellFormedOn` |
| **`canary_readonly_write_ub`** | `[asm.options.readonly]` | Kernel 11 emits `.writeNA 8 8 99` under `options(readonly)` | Steps to `.failed .ub` at budget 1 & refutes `MirLang.WellFormedOn` |
| **`canary_nomem_read_ub`** | `[asm.options.nomem]` | Kernel 12 emits `.readNA 8 8 32` under `options(nomem)` | Steps to `.failed .ub` at budget 1 & refutes `MirLang.WellFormedOn` |
| **`canary_unaligned_access_ub`** | Memory alignment / spatial safety | Kernel 13 emits `.writeNA 3 8 99` (`3 % 8 ≠ 0`) | Steps to `.failed .ub` at budget 1 & refutes `MirLang.WellFormedOn` |
| **`canary_demonic_reg_aliasing_ub`** |Register allocation non-aliasing | Kernel 14 clobbers hardcoded `.x2` before reading `in(reg) ptr`; fails on the demonic branch where `ptr` is allocated to `.x2` | Steps to `.failed .ub` at budget 1 & refutes `MirLang.WellFormedOn` |

---

### 4. Four-Stage Incremental Implementation Roadmap for `joshlf/anneal-private`

`Basis: architectural synthesis of joshlf/anneal-private Issues #100 and #102 + examined ISA ecosystems`

Rather than attempting a monolithic multi-architecture integration in a single step, Anneal should execute a **4-stage incremental roadmap**, where every stage preserves the ~140-LOC cap on `trusted/` and adds capabilities strictly inside `theory/Anneal/Isa/`:

#### Stage 0: Out-of-Line Assembly (`global_asm!` / External `.s` Functions) via Existing `TCBItem.foreignBridge` (Zero `trusted/` Changes)
- **Scope**: Whole-function assembly routines invoked via Rust `extern "C" fn` declarations (e.g., standalone cryptographic kernels or context-switch routines).
- **Mechanism**: Requires **zero changes** to `trusted/lean/Trusted/`. In `Trusted/Refinement.lean`, `TCBItem.foreignBridge (name : String) (bridge : Compiler MirLang AsmLang)` already exists as a first-class TCB entry!
- **Deliverable in `theory/Anneal/Isa/`**: Instantiate `AsmLang : Language` using `SmallStepLang` over an assembly machine (`Kraken` or `LNSym`) and discharge `AsmSem prog ≤ ForeignSpec` in `theory/`, linking it to callers via `TCBItem.foreignBridge`.

#### Stage 1: Inline `asm!` Contract in `trusted/` + `Kraken`-Style Structured AST Bridge in `theory/`
- **Scope**: Inline `core::arch::asm!` blocks in systems and embedded Rust (MMIO register reads/writes, special system instructions, scalar arithmetic loops, barriers).
- **Deliverables**:
  1. Land the ~140-LOC `@[candidate inline_asm]` extension in `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` (`PhysReg`, `RegClass`, `AsmOperand`, `InlineAsmOptions`, `AsmAccessEvent`, `AsmContract`, `Terminator.inlineAsm`, `evalInlineAsm`) exactly as mechanized in `support/AnnealIsaBridgeSynthesis.lean`.
  2. Extend Charon/Anneal's MIR importer to lower `rustc_middle::mir::TerminatorKind::InlineAsm` into `Terminator.inlineAsm`.
  3. Create `theory/Anneal/Isa/KrakenBridge.lean` implementing structured AArch64/RISC-V instruction ASTs with the `StrictObserve` memory discipline (`kraken_strict_observe_eq_kernel1`) and a `symstep_asm` tactic that discharges straight-line `Terminator.inlineAsm` steps automatically.

#### Stage 2: Byte-Decoded `BitVec 32` Object-Code Verification + `Component` Lenses + Constant-Time `UArchEvent` Traces
- **Scope**: High-assurance cryptographic inline and out-of-line assembly (`zerocopy` SIMD/pointer primitives, Montgomery multiplication, NTT, AES/SHA-2/ChaCha20) where verification must cover actual assembled machine bytes (catching assembler encoding bugs) and prove constant-time execution.
- **Deliverables**:
  1. Create `theory/Anneal/Isa/Component.lean` porting `cslib-community/bignum`'s `Component S A` and `Orthogonal` lens hierarchy (`regComponent_orthogonal`) for O(1) register/flag/memory frame rewriting.
  2. Create `theory/Anneal/Isa/BignumLNSymBridge.lean` connecting `leanprover/LNSym`'s `BitVec 32` AArch64 decoder (`decodeAArch64Word`) and `cslib-community/bignum`'s `UArchEvent` trace (`bignum_lnsym_words_eq_kernel1`) to `evalInlineAsm`.
  3. Add constant-time specification combinators (`ConstantTimeOn Pre secretProj`) asserting that the emitted `UArchEvent` trace (`memRead` addresses, `memWrite` addresses, `branchTaken` conditions) is invariant across secret inputs.

#### Stage 3: Two-Tier `Sail` / `archsem-lean` + `opencompl` Pure `BitVec` Summary Architecture & Weak-Memory Concurrency
- **Scope**: Scaling beyond hand-transcribed AArch64 subsets to full authoritative Arm-A (v8.5–v9.4), RV64GC, and x86-64 specifications, plus concurrent lock-free assembly (`ldaxr`/`stlxr`, `cas`, `dmb ish`).
- **Deliverables**:
  1. **Tier-1 Ground Truth (`theory/Anneal/Isa/SailTier1.lean`)**: Import `rems-project/lean-sail` (`FreeM SailEffect`) and `rems-project/archsem-lean` (`IMon` / `Outcome`) instruction definitions generated by `rems-project/sail`.
  2. **Tier-2 Pure `BitVec` Summaries (`theory/Anneal/Isa/SailTier2.lean`)**: Following `opencompl/riscv-lean` and `rems-project/islaris`, generate per-instruction pure `BitVec` summary rules (`sailAccumSummaryBv`) and prove once per instruction (`sail_tier1_equiv_tier2_summary`) that the Tier-1 `FreeM SailEffect` denotation refines the Tier-2 pure summary. User crate proofs interact *only* with the fast Tier-2 summaries via `simp` and `bv_decide`.
  3. **Weak-Memory Event Bridge (`theory/Anneal/Isa/ArchSemMemoryBridge.lean`)**: Connect `archsem-lean`'s `MemRead`, `MemWrite`, and `Barrier` outcomes directly to `AsmAccessEvent.atomicLoad` and Anneal's timestamped `MemState` (`curView`, `atomicMsgs`, `View.join`), enabling end-to-end verification of Rust + inline-assembly release/acquire synchronization.

---

## Boundaries

1. **Pre-Linking MIR `asm!` Templates vs. Post-Linking ELF Binaries**:
   `Terminator.inlineAsm` at the MIR level verifies the assembly block against all valid register allocations (`validRegAllocs`) and abstract memory locations (`MemState`). In Stage 1, template strings are parsed into structured instructions (`KrakenInst`); only when combined with Stage 2 (`decodeAArch64Word` over assembled 32-bit words) does verification cover the assembler's encoding of mnemonics into machine bytes.
2. **Abstract Location-Indexed `MemState` vs. Byte-Reinterpreting Pointer Arithmetic**:
   Anneal's current `Trusted/Memory.lean` indexes memory by abstract location `loc : Nat` storing `MirVal` (`.usize`, `.bool`, references) with alignment/width checked via `AsmAccessEvent` (`width > 0 && loc % width == 0`). Assembly blocks that perform sub-word byte punning (e.g., writing a `u64` and reading back individual `u8` lanes at `loc + 1..loc + 7` via `ldrb`) require extending `MirVal` or `MemState.naVal` with byte-slice extraction in a future `@[candidate byte_mem]` extension.
3. **Inline Assembly Control-Flow Targets (`asm_goto` / `label` Operands)**:
   Our mechanized `Terminator.inlineAsm` supports single normal continuation (`target : Option BlockId`) plus `options(noreturn)`. Supporting RFC 2873 `label` operands (`asm_goto`, where inline assembly can jump to multiple MIR `BasicBlock` targets) requires changing `target : Option BlockId` to `targets : List BlockId` and having `AsmMachineState` return the selected target index.
4. **Floating-Point and Vector/SIMD Register Classes**:
   The mechanized `PhysReg` and `RegClass` in `support/AnnealIsaBridgeSynthesis.lean` model general-purpose registers (`.x0`..`.x3`), `.sp`, and `.nzcv`. Verification of NEON/SVE/AVX2 assembly requires adding `.v0`..`.v31` (`BitVec 128`) to `PhysReg` and `.vreg` to `RegClass` following `LNSym`'s `sfp : BitVec 5 → BitVec 128` representation.

---

## Evidence

1. **Standalone Machine-Checked Lean 4.34.1 Synthesis Proof (`support/AnnealIsaBridgeSynthesis.lean`)**:
   - **Path**: `reports/anneal-isa-integration-architecture-and-roadmap-synthesis-2026/support/AnnealIsaBridgeSynthesis.lean`
   - **Lines**: 2,289
   - **SHA-256**: `0aea81289fb1cc881a7e492796f0cd40035fb8498c560ad767550eff07ad2a70`
   - **Toolchain**: `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean` (`Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`)
   - **Axiom & Soundness Audit (enforced by `#guard_msgs in #print axioms` in Section 9, lines 2221–2289)**:
     - `kraken_all_unsound_on_unaligned_or_oob`: `[propext, Quot.sound]`
     - `kraken_strict_observe_eq_kernel1`: `[propext, Classical.choice, Quot.sound]`
     - `bignum_lnsym_words_eq_kernel1`: `[propext, Quot.sound]`
     - `sail_tier1_equiv_tier2_summary`: `[propext, Classical.choice, Quot.sound]`
     - `verify_crate_with_inline_asm`: `[propext, Classical.choice, Quot.sound]`
     - `non_vacuity_at_every_depth`: `does not depend on any axioms` (pure kernel reduction)
     - `canary_undeclared_clobber_ub`: `[propext, Quot.sound]`
     - `canary_readonly_write_ub`: `[propext, Quot.sound]`
     - `canary_nomem_read_ub`: `[propext, Quot.sound]`
     - `canary_unaligned_access_ub`: `[propext, Quot.sound]`
     - `canary_demonic_reg_aliasing_ub`: `[propext, Quot.sound]`
     - **Zero `sorryAx` and zero custom axioms** across the entire file.
2. **Source Manifest (`support/source-manifest.json`)**:
   - **Path**: `reports/anneal-isa-integration-architecture-and-roadmap-synthesis-2026/support/source-manifest.json`
   - Records the exact commit SHAs and SHA-256 digests of all examined `joshlf/anneal-private` files (`42f4571d761b46c7142815f38b69c3781b3555e3`) and all 19 external repositories.

---

## Revalidation

To revalidate the standalone Lean 4.34.1 mechanization and verify that all 16 theorems and all 11 `#guard_msgs in #print axioms` checks pass with zero errors, zero warnings, and zero `sorryAx`, run from the repository root:

```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M768 \
  reports/anneal-isa-integration-architecture-and-roadmap-synthesis-2026/support/AnnealIsaBridgeSynthesis.lean
```

Expected output: exit code `0` with empty stdout/stderr (all `#print axioms` outputs are verified inline against their `#guard_msgs` docstrings).

To verify the SHA-256 digest of `support/AnnealIsaBridgeSynthesis.lean`:

```bash
sha256sum reports/anneal-isa-integration-architecture-and-roadmap-synthesis-2026/support/AnnealIsaBridgeSynthesis.lean
# Expected: 0aea81289fb1cc881a7e492796f0cd40035fb8498c560ad767550eff07ad2a70
```

*Authored by an AI agent acting on joshlf's behalf.*
