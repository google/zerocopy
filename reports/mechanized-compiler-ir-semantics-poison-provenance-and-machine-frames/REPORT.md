# IR Semantics in Mechanized Compilers: SSA Forms, Poison/Undef/Freeze, Provenance Memory Models, and Machine Stack Frames

## Summary

A verified drop-in Rust compiler pipeline spans four semantic layers: source
`Runtime(PostCleanup)` MIR, a mid-level SSA optimization IR (`AnSSA` / `AnLLVM`),
a machine-level register/stack-slot IR (`LTL` / `Mach` / `VCode`), and target ISA
machine code (`Asm` / `RV64` / `x86-64` / `AArch64`). Surveying the nine major
mechanized compiler IR frameworks—**CompCert (`RTL`, `LTL`, `Mach`, `Asm`),
CompCertSSA, Vellvm (`VIR`), Alive2, Lean-MLIR (`VeIR`), Isabelle-LLVM, K-LLVM,
and Cranelift (`CLIF` / `ISLE` / `VCode`)**—together with our standalone Lean
`v4.34.1` mechanization (`support/MechanizedIrSemanticsProbe.lean`) establishes
four foundational design decisions:

1. **SSA Control-Flow Join Semantics (`phiBlock_equiv_blockArg`):**
   CompCertSSA (`RTL` + `phinode`), Vellvm (`VIR`), and K-LLVM place parallel
   $\phi$-nodes at block headers (evaluating all $\phi$-operands for predecessor
   index $k$ simultaneously in the pre-join register file), whereas Cranelift
   `CLIF`, Lean-MLIR (`VeIR`), and Lean 4's `LCNF` pass explicit arguments along
   branch edges to basic-block formal parameters. Our theorem
   `phiBlock_equiv_blockArg` proves that parallel $\phi$-joins and edge-argument
   block parameters produce identical post-join register environments, while
   block-argument SSA eliminates the non-local predecessor-index lookup table
   during CFG edge splitting and critical-edge insertion.
2. **Eliminating Multi-Valued `undef` in Favor of Single-Valued `poison` +
   Nondeterministic `freeze` (`undef_breaks_xor_self_and_cse` vs.
   `freeze_restores_cse_refinement`):**
   Multi-valued `undef` (where each syntactic read of an uninitialized value
   independently chooses any bit-pattern) invalidates `x ^^^ x = 0`, breaks common
   subexpression elimination (`CSE` / `GVN`), and forces complex set-of-values
   monads in Vellvm (`OOM` / `Undef`). By contrast, modeling deferred undefined
   behavior solely via single-valued `PoisonVal := .poison | .value (w : BitVec n)`
   together with a relational `FreezeStep` (`freeze(.poison)` nondeterministically
   picks one fixed `BitVec n` bound in the destination SSA register) restores
   `v ^^^ v = 0` (`freeze_restores_cse_refinement`) and matches LLVM's modern
   post-`undef` trajectory, Alive2, and Lean-MLIR (`PoisonOr`).
3. **Byte-Granularity Provenance Memory vs. Whole-Word Scalar Poison
   (`byte_load_preserves_field_across_uninit_padding`):**
   Rust ABI lowering (`PassMode::Cast` in `rustc_codegen_ssa` and SROA/memcpy)
   routinely performs widened $64$-bit integer loads across structs containing
   uninitialized padding bytes. An IR that models memory cells only at scalar
   word granularity (`Isabelle-LLVM` or naive `BitVec 64` memory) taints the
   entire loaded word as `.poison` whenever any padding byte is uninitialized
   (`loadWord64_wholePoison = .poison`), whereas a **byte-indexed block-offset
   memory (`AnByteVal := .uninit | .init (b : BitVec 8) (prov : Option AllocId)`)**
   modeled after Vellvm's `DTYPE_B`, Alive2's `Byte` encoding, and MiniRust
   preserves initialized struct fields across adjacent `.uninit` padding
   (`extractFieldByte0 = .init field0 (some 1)`).
4. **Machine-Level IR Stack-Slot Typing to Flat Hardware Stack Lowering
   (`mach_to_asm_frame_isolation`):**
   Between register allocation and assembly emission, CompCert's `LTL` and
   `Mach` (like Cranelift's `VCode` + `Regalloc2`) partition stack storage into
   typed disjoint slot classes (`SlotClass := .localSlot | .calleeSaved | .outgoingArg`)
   before `Stacking` lowers them into a single flat byte-addressed stack frame
   pointed to by `RSP`/`SP`. We prove in `mach_to_asm_frame_isolation` that
   disjoint `SlotClass` identifiers map to strictly non-overlapping physical
   8-byte intervals $[o_1, o_1 + 8) \cap [o_2, o_2 + 8) = \emptyset$, discharging
   frame preservation without global alias analysis.

## Applicability

This report synthesizes and extends `anllvm-clean-slate-ir-semantics-and-tree-borrows-lowering`,
`anllvm-globalisel-backend-and-certificate-checkers`,
`anssa-block-argument-ssa-mem2reg-and-mir-semantic-hazards-2026`,
`anneal-mid-level-ir-optimizations-and-lowering-survey`, and
`opencompl-riscv-lean-lean-mlir-and-ship-your-interpreter-2026`. All mechanized
theorems in `support/MechanizedIrSemanticsProbe.lean` are verified under Lean
`v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using only `[propext, Quot.sound]`,
and target the IR semantics needed to compile Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`).

## Findings

### 1. Comparative Taxonomy of Mechanized Compiler IRs

Basis: source + documentation across the nine surveyed IR frameworks.

| Mechanized IR System | Host Prover / Engine | Control-Flow & SSA Representation | Poison / Undef / Freeze Design | Memory & Provenance Model | Register & Stack-Slot Representation |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **CompCert `RTL` $\to$ `LTL` $\to$ `Mach` $\to$ `Asm`** (`AbsInt/CompCert`, Leroy CACM 09) | Coq / Rocq | CFG of indexed nodes (`PTree.t instruction`); non-SSA pseudo-registers in `RTL` | Single `Vundef` value representing uninitialized or indeterminate scalar results; strict UB on invalid branch/mem | Block-offset model (`Mem.mem`, `block * ptrofs`, byte-level `memval := Undef \| Byte b \| Fragment v q n`) with `Mem.inject` | `RTL`: infinite pseudo-regs; `LTL`: machine `mreg` + `SlLocal`/`SlIncoming`/`SlOutgoing` slots (`Locations.v`); `Mach`: abstract frame + `sp`; `Asm`: flat `RSP` block |
| **CompCertSSA** (Barthe, Demange, Pichardie TOPLAS 14) | Coq / Rocq | `RTL` extended with a separate per-join-block `phinode` table (`PTree.t (list phiinstruction)`) evaluated in parallel | Inherits CompCert `Vundef` | Inherits CompCert block-offset `Mem.mem` | SSA-renamed pseudo-registers (`reg`) with dominance-based well-formedness (`wf_ssa_function`) |
| **Vellvm (`VIR`)** (`vellvm/vellvm` @ `506f1eb0`, Zakowski et al. ICFP 21) | Coq / Rocq (`ITree` monad) | Named basic blocks with header $\phi$-nodes; denoted as comonadic `ktree` interaction trees over `L0..L4` event layers | Multi-layered: `dvalue` (concrete) vs. `uvalue` (symbolic expression trees for `undef` + `DT_Poison`) + nondeterministic `pick`/`freeze` handler | Framed block-offset memory with serialized byte cells `SByte := Byte b \| PtrFrag p i \| Poison \| Undef` and provenance allocation IDs | Infinite LLVM SSA `%id` identifiers + `alloca` memory blocks promoted via `vmem2reg` |
| **Alive2** (`AliveToolkit/alive2` @ `adacbd51`, Lopes et al. PLDI 21 / CAV 21) | Z3 SMT (`QF_ABV` / `QF_UFBV`) | Topologically sorted DAG/CFG (loops unrolled to bound $k$); SSA values encoded as `(val : bv, non_poison : bool)` pairs | **Full `poison` + `undef` + `freeze`**: `poison` is a per-value (and per-byte) boolean taint bit; `undef` introduces fresh existential SMT vars per use; `freeze` clears the poison bit | **8-bit SMT Byte encoding** (CAV 2021): distinguishes non-pointer bytes (per-byte `poison` bitmask) from pointer bytes (`bid`, `offset`, `prov`, `liveness`) | LLVM SSA values + explicit `local` (`alloca`) vs. `non-local` memory blocks with alignment/size bounds |
| **Lean-MLIR (`VeIR`)** (`opencompl/lean-mlir` @ `b8c4a771`, ITP 24) | Lean 4 (`v4.34.1`) | Intrinsically typed de Bruijn / region-based **block-argument SSA (`Com d Γ eff τ`)** | **`PoisonOr α` monad** (`EffectKind.pure`); omits multi-valued `undef`; models `llvm.freeze` and directional refinement `⊑` | Pure SSA dialect (`LLVM`, `RISCV64`, `LLVMPlusRiscV`) for register peepholes; memory modeled via separate state effect | Typed context $\Gamma$ of SSA values; `LLVMPlusRiscV` bridges `BitVec w` LLVM ops to 64-bit `RV64` register instructions |
| **Isabelle-LLVM** (Lammich ITP 2019 / IJCAR 2022, `doi:10.4230/LIPIcs.ITP.2019.22`) | Isabelle/HOL (`Sepref`) | Basic blocks with explicit label arguments / $\phi$-lowered monadic `llc_par` / `M` nondeterminism-error monad | **No `poison` or `undef` (`immediate UB`)**: arithmetic overflow (`nsw`/`nuw`) or uninitialized read triggers immediate `fail` in the monad | **Typed algebraic block-value memory** (blocks of arrays of structured values rather than raw untyped bytes; forbids type-punning casts) | Monadic local variables + `alloca` stack blocks refined from abstract imperative HOL data structures |
| **K-LLVM** (Li & Gunter ECOOP 2020, `doi:10.4230/LIPIcs.ECOOP.2020.7`) | $\mathbb{K}$ Framework | CFG basic blocks with explicit parallel $\phi$-node evaluation before block body | Supports both `undef` and `poison` markers at instruction and byte granularity | Byte-level symbolic memory array with object IDs, bounds, and sub-byte bitfields | LLVM SSA registers + explicit call-stack frame list (`StackFrame`) |
| **Cranelift (`CLIF` / `ISLE` / `VCode`)** (`bytecodealliance/wasmtime` @ `87282b8f`, `v0.136.2`) | Rust + ISLE SMT/Lean specs | **Block-argument SSA (`BlockCall` passing `Value` lists to `Block` parameters)**; `egraph` pass uses scoped Elaborated `aegraphs` | Integer ops are total wrapping two's-complement (`iadd`, `imul`); traps (`udiv` by 0, `trapz`) are explicit side effects | Untyped byte-addressed memory with explicit `MemFlags` (`trusted`, `aligned`, `notrap`, alias-region bits `heap`/`table`/`vmctx`) | `CLIF`: SSA `Value`s + `StackSlot`s; `VCode`: virtual `VReg`s lowered by `Regalloc2` into physical `PReg`s + `SpillSlot`s |

### 2. Block-Argument SSA vs. Parallel $\phi$-Nodes (`phiBlock_equiv_blockArg`)

Basis: source + execution (`support/MechanizedIrSemanticsProbe.lean`, lines 35–75) +
`anssa-block-argument-ssa-mem2reg-and-mir-semantic-hazards-2026`.

In CompCertSSA (`RTL` + `phinode`), entering a join block $B_{\text{join}}$ from
 its $k$-th predecessor executes all $\phi$-assignments $r_i := \phi(r_{i,0}, \dots, r_{i,m-1})$
**in parallel** (`evalPhiJoin`), reading every right-hand side $r_{i,k}$ from the
pre-join register file `rf` before updating any destination register $r_i$ (the
 classical "swap problem" of Briggs et al., SPE 1998, and Rideau, Serpette, &
Leroy, JAR 2008). However, indexing $\phi$-operands by predecessor position $k$
couples the syntax of $B_{\text{join}}$ to the ordering of its incoming CFG edges.

In Cranelift `CLIF` (`cranelift/codegen/src/ir/dfg.rs`), Lean-MLIR, and Lean 4's
`LCNF` (`src/Lean/Compiler/LCNF/Basic.lean`), basic blocks instead declare formal
parameters `params : List RegId`, and each terminator edge `jmp B_join (e_1, ..., e_n)`
carries the actual argument list (`evalBlockArgEdge`). In
`support/MechanizedIrSemanticsProbe.lean` (lines 47–75), we prove that
projecting predecessor $k$'s $\phi$-operands onto the incoming edge is
denotationally identical to parallel $\phi$-evaluation:

```lean
theorem phiBlock_equiv_blockArg (phis : List PhiAssign) (predIdx : Nat) (rf : RegFile) :
    evalPhiJoin phis predIdx rf =
      evalBlockArgEdge (phis.map PhiAssign.dst) (phis.map (fun p => p.rhs predIdx)) rf
```

Consequently, a verified mid-level IR (`AnSSA`) should use **block-argument SSA**
so that local terminator rewrites (branch folding, jump threading, critical-edge
splitting for out-of-SSA parallel-move insertion) never invalidate $\phi$-column
indices in successor blocks.

### 3. Why Multi-Valued `undef` Must Be Excluded: `poison` + Nondeterministic `freeze`

Basis: source + execution (`support/MechanizedIrSemanticsProbe.lean`, lines 78–111) +
Lee et al., PLDI 2017 (`doi:10.1145/3062341.3062343`).

In legacy LLVM IR, reading uninitialized memory or an `undef` constant yields a
*set* of all bit-vectors (`undefSet`), and each syntactic occurrence of a variable
bound to `undef` can resolve to a different bit-vector. In
`support/MechanizedIrSemanticsProbe.lean` (lines 80–96), we prove
`undef_breaks_xor_self_and_cse`:

```lean
theorem undef_breaks_xor_self_and_cse :
    (∀ y : BitVec 64, y ^^^ y = 0#64) ∧
    xorSet undefSet undefSet 1#64
```

Because `xorSet undefSet undefSet` contains `1#64` (by choosing `a = 0#64` and
`b = 1#64`), replacing `let y = undef; y ^^^ y` with `0#64` is valid only if `y`
denotes a *single* deterministic value, whereas substituting `y -> undef` (or
performing CSE `undef ^^^ undef -> let y = undef in y ^^^ y`) changes the set of
observable outcomes when followed by other operations.

By eliminating `undef` and representing all uninitialized bytes and overflowing
`nsw`/`nuw`/`exact` operations via **single-valued `PoisonVal := .poison | .value (BitVec 64)`**
plus a relational **`FreezeStep src v` instruction** (`freeze(.poison)`
nondeterministically steps to a single fixed `v : BitVec 64` stored in the SSA
register), every subsequent read of `v` observes the exact same bit-pattern, and
`v ^^^ v = 0#64` holds unconditionally (`freeze_restores_cse_refinement`, lines
102–110).

### 4. Memory Models for IRs: Byte-Granularity Provenance vs. Whole-Word Poison

Basis: source + execution (`support/MechanizedIrSemanticsProbe.lean`, lines 113–151) +
Lee et al., OOPSLA 2018 (`doi:10.1145/3276495`) + Alive2 CAV 2021
(`doi:10.1007/978-3-030-81688-9_35`) + Villani et al., PLDI 2025 (`doi:10.1145/3735592`,
Tree Borrows).

1. **Why Isabelle-LLVM's Typed Block Memory and Whole-Word Scalar Poison Fail on
   Rust ABI Lowering:**
   Isabelle-LLVM (`Lammich ITP 2019`) models memory as disjoint typed arrays of
   high-level values and treats any uninitialized read as immediate failure.
   However, `rustc_codegen_ssa` (`PassMode::Cast`) and `memcpy`/SROA lower small
   Rust structs (such as `#[repr(C)] struct Padded { a: u8, /* 3 bytes uninit pad */ b: u32 }`)
   into a single widened `i64` load followed by bit-shifts (`trunc`/`lshr`). If a
   $64$-bit load returns scalar `.poison` whenever *any* of the 8 constituent
   bytes is `.uninit` (`loadWord64_wholePoison`), then loading `Padded` destroys
   the initialized field `a`!
2. **Byte-Granularity Provenance Memory (`AnByteVal`):**
   Following Vellvm (`SByte`), Alive2 (`Byte`), and MiniRust, each memory cell at
   `(allocId : BlockId, offset : Nat)` must be a tagged byte:
   $$\text{AnByteVal} ::= \text{.uninit} \mid \text{.init}\;(b : \text{BitVec } 8)\;(\text{prov} : \text{Option AllocId}).$$
   Multi-byte register values loaded from memory carry an array of 8 `AnByteVal`
   cells (`AnByteWord := Fin 8 -> AnByteVal`, or equivalently Alive2's 8-bit
   per-byte poison mask + pointer provenance). In
   `support/MechanizedIrSemanticsProbe.lean` (lines 139–151), we prove
   `byte_load_preserves_field_across_uninit_padding`:
   ```lean
   theorem byte_load_preserves_field_across_uninit_padding (field0 : BitVec 8) :
       loadWord64_wholePoison (samplePaddedStruct field0) = .poison ∧
       extractFieldByte0 (samplePaddedStruct field0) = .init field0 (some 1)
   ```
3. **Integrating Tree Borrows / Quasi-Concrete Provenance:**
   At the MIR and mid-level IR layers, pointer provenance `prov : Option (AllocId × BorTag)`
   tracks both the CompCert block ID (`AllocId`) and the Tree Borrows node tag
   (`BorTag`, `compiler/rustc_const_eval/src/interpret/ borrow_tracker/tree_borrows/`
   in Rust `1.99.1` @ `58cf8f9c35b3`). Once alias-based optimizations complete,
   lowering to the machine IR erases `BorTag` via a trivial forgetful simulation
   while retaining `(AllocId, offset)` (or concrete integer addresses in
   Lee et al.'s OOPSLA 2018 twin-allocation / quasi-concrete model) down to `Asm`.

### 5. Machine-Level IRs with Registers and Stack Slots (`LTL` / `Mach` / `VCode` to `Asm`)

Basis: source + execution (`support/MechanizedIrSemanticsProbe.lean`, lines 153–209) +
CompCert (`backend/LTL.v`, `backend/Locations.v`, `backend/Mach.v`, `backend/Stackingproof.v`).

Lowering directly from an infinite-register SSA IR to flat assembly conflates two
orthogonal verification obligations: **register allocation (`Regalloc2` / IRC)**
and **stack-frame layout (`Stacking`)**. CompCert and Cranelift separate them via
a machine-level IR (`LTL` / `Mach` / `VCode`) whose locations are a sum type of
physical machine registers (`PReg` / `mreg`) and typed stack slots:

```lean
inductive SlotClass where
  | localSlot    : Fin 4 → SlotClass
  | calleeSaved  : Fin 4 → SlotClass
  | outgoingArg  : Fin 4 → SlotClass
```

In `LTL` and `Mach`, reading or writing `.calleeSaved i` cannot alias `.localSlot j`
or `.outgoingArg k` by syntactic construction. The `Stacking` pass then maps each
`SlotClass` to a concrete byte offset `slotByteOffset` relative to `SP`. Our
theorem `mach_to_asm_frame_isolation` (`support/MechanizedIrSemanticsProbe.lean`,
lines 169–209) proves that for all $s_1 \ne s_2$, their 8-byte intervals in the
flat `Asm` stack frame are strictly disjoint (`slotByteOffset s1 + 8 ≤ slotByteOffset s2 ∨ slotByteOffset s2 + 8 ≤ slotByteOffset s1`).

## Boundaries

- **Pointer-to-Integer Casts (`ptrtoint` / `inttoptr`) in Pure Block-Offset
  Memory:** CompCert's pure block-offset memory model (`Mem.mem`) forbids forging
  a valid pointer from an arbitrary integer (`inttoptr(ptrtoint(p))`) unless a
  quasi-concrete / twin-allocation model (Lee et al., OOPSLA 2018; CompCertMC /
  Kang et al., POPL 2015) assigns concrete base addresses to blocks upon address
  exposure (`expose_provenance`). Programs using Rust's strict-provenance APIs
  (`ptr.with_addr` / `addr`) remain purely within `(AllocId, offset)` block
  semantics without requiring twin allocations.
- **Target Instruction Decoding (`Asm` vs. Machine Bytes):** CompCert's `Asm`
  models assembly instructions as an algebraic datatype rather than raw encoded
  bytes. To close the final gap to ELF machine bytes on RISC-V or x86-64, the
  pipeline must compose `Asm` with a verified instruction decoder/encoder such as
  `BasisResearch/ship-your-interpreter` (`decodeN` over `Lean_RV64D_executable` at
  `fb07094cff91`) or `opencompl/riscv-lean` (`7c6b500c1744`).

## Evidence

- **Standalone Lean 4.34.1 Mechanization:**
  `support/MechanizedIrSemanticsProbe.lean` (`226` lines, zero `sorry`, verified
  under Lean `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52` using only
  `[propext, Quot.sound]`) mechanizes:
  - `phiBlock_equiv_blockArg` (lines 66–75),
  - `undef_breaks_xor_self_and_cse` and `freeze_restores_cse_refinement` (lines
    91–110),
  - `byte_load_preserves_field_across_uninit_padding` (lines 147–150),
  - `mach_to_asm_frame_isolation` (lines 169–209).
- **Primary Upstream Repositories Inspected:**
  - `vellvm/vellvm` at `506f1eb0be542611521985719b971fbce8498dc9` (`src/coq/Semantics/`
    for `uvalue`/`dvalue`, `SByte`, and `freeze`).
  - `AliveToolkit/alive2` at `adacbd5180ccf95075e9867c4f0c259f59c9fef2` (`ir/memory.cpp`,
    `ir/value.cpp` for 8-bit `Byte` and `freeze` encodings).
  - `opencompl/lean-mlir` at `b8c4a771319a044854a4bbb49b8821381ef86ff8` (`SSA/Core/`,
    `SSA/Projects/InstCombine/`, `SSA/Projects/LLVMRiscV/`) and
    `opencompl/riscv-lean` at `7c6b500c1744f40d928fb131125cd06edf9f4fce`.
  - `BasisResearch/ship-your-interpreter` at `fb07094cff916318c34b07494a7d739f1e53989b`.
  - `bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`
    (`cranelift/frontend/src/ssa.rs`, `cranelift/codegen/src/ir/`).
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (Rust `1.99.1`).

## Revalidation

Run the standalone Lean `v4.34.1` mechanization via `anneal-lean-run` to check
all four IR semantics theorems and their `#guard_msgs in #print axioms` outputs:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lake env lean reports/mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames/support/MechanizedIrSemanticsProbe.lean
```
