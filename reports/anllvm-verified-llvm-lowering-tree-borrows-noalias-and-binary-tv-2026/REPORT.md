# Verified LLVM IR Lowering (`AnLLVM`), Tree Borrows to `noalias`/`readonly`/`writable` Simulation, and `GraphLang` Binary Translation Validation

## Summary

Closing Anneal's (`joshlf/anneal`) verification boundary from monomorphized Rust
MIR (`MonoMIR`) through lowered LLVM IR (`AnLLVM`) down to machine code requires
(1) a directional poison/refinement dialect that repairs two soundness defects
in `opencompl/lean-mlir`, (2) a byte-accurate memory representation (`DTYPE_B` /
`AnByteWord`) for aggregates with uninitialized padding, (3) a relational
simulation connecting Miri's 4-state Tree Borrows permission machine to LLVM's
`noalias`, `readonly`, and `writable` parameter attributes (including `!Unpin`
and two-phase borrow exemptions), and (4) a kernel-checked `seL4/graph-refine`
(`GraphLang`) binary translation validator with static stack-slot scalarization
and hint-guided $k:1$ unrolled loop decomposition.

Our primary-source audit of `vellvm/vellvm`, `opencompl/lean-mlir` (`VeIR`),
`AliveToolkit/alive2` (v21.0), `snu-sf/crellvm`, `seL4/graph-refine`, and
`rust-lang/rust` (`rustc` LLVM ABI/retag lowering and Miri's `tree_borrows`),
paired with two standalone Lean 4.34.1 mechanizations
(`support/track6_llvm_lowering_and_binary_tv_probe.lean`, 1,215 lines; and
`support/round2_track5_probe.lean`, 1,532 lines; zero `sorryAx`, zero
`Lean.ofReduceBool`), establishes five main findings:

1. **Two soundness defects in `opencompl/lean-mlir` (`b8c4a77131`) and their
   zero-axiom `AnLLVM` repair:**
   - *Defect 1 — Deterministic `LLVM.freeze .poison = .value 0`
     (`LeanMLIR/Dialects/LLVM/Semantics.lean:636-640`):* Collapsing `.poison`
     deterministically to `.value 0` rather than a nondeterministic choice over
     `BitVec w` validates `icmp eq (freeze %p), 0 ↦ true` on poison and then
     miscompiles when `%p` is lowered to a hardware register holding a non-zero
     bitpattern (`42#64`, `leanMLIR_freeze_unsound_canary`, also referred to as
     `lean_mlir_freeze_zero_unfaithful`). Modeling `freeze` via Anneal's
     nondeterministic `Partial` predicate (`freezeSem_refines_any_bitvec`) or a
     per-byte nondeterministic oracle restores soundness.
   - *Defect 2 — `axiom refinement_correctness {p : Prop} : p` (`False`) in
     `toPeepholeUNSOUND` (`SSA/Projects/LLVMRiscV/PeepholeRefine.lean:33-53`):*
     Because `PeepholeRewrite` (`Rewrite.lean:23`) demands symmetric equality
     (`lhs.denote = rhs.denote`), `lean-mlir` bridges directional poison
     refinement (`src ⊑ₒ tgt`) into its rewrite engine by asserting `False`.
     Replacing `PeepholeRewrite` with a monotone directional pass driver
     (`DirectionalRewriteRefine`, `evalHybridProg_rewrite_refines` /
     `compiles_anllvm_rewrite_chain`) discharges `directionalRewriteCompiler_verified`
     (`peephole_rewrite_sound_zero_axioms`) with **zero axioms** (`[]`).
2. **Whole-word integer loads (`DTYPE_I`) taint initialized struct fields across
   uninitialized padding, requiring byte-typed memory (`DTYPE_B` / `AnByteWord`)
   with per-byte `freeze`:**
   When `rustc` lowers small aggregates via `PassMode::Cast`
   (`compiler/rustc_codegen_ssa/src/mir/block.rs:2082-2103`), emitting a typed
   integer load (`load i64`) across a struct containing even a single
   uninitialized (`.poison`) padding byte taints the entire 64-bit integer word
   to `.poison` in both `Vellvm` (`MemoryBytes.v:726-733`) and `Alive2`
   (`ir/memory.cpp:743-776`), so a subsequent whole-word `freeze` can clobber
   initialized field bytes (`canary_int64_load_on_padding_taints_word`, also
   denoted `canary_dtype_i_whole_word_load_taints_initialized_bytes`). Modeling
   8-byte words as `AnByteWord := Fin 8 → PoisonOr (BitVec 8)` (`DTYPE_B`,
   `MemoryBytes.v:747-755`) and applying per-byte `freeze` preserves every
   initialized byte lane (`passModeCast_byte_vs_int_load_sound`, also denoted
   `freezeByteWord_preserves_defined_bytes`), while omitting `noundef`/`!range`
   on `MaybeUninit`/padding loads discharges `mirToAnLLVMSafe_verified` vs.
   `canary_uninit_noundef_refutes_compiles`.
3. **Miri's 4-state Tree Borrows machine (`Reserved`, `Active`/`Unique`,
   `Frozen`, `Disabled` + `isProtected` and `accessed`) soundly simulates LLVM
   `noalias`, `readonly`, and `writable` (`treeBorrows_implies_llvm_noalias_readonly_sound`):**
   - *Protected `.frozen` (`&T` where `T: Freeze`) $\implies$ `noalias` +
     `readonly`:* Any child or foreign write during a protected call steps
     `tbStep` to `none` (UB), guaranteeing memory constancy across arbitrary
     interleaved calls and stores (`tb_protected_frozen_readonly_noalias_sound`).
   - *Protected `.active` (`&mut T` where `T: Unpin` with
     `-Zmiri-tree-borrows-implicit-writes`) $\implies$ `noalias` + `writable`:*
     Any foreign read or write during the protected call triggers
     `ProtectedDisabled` UB (`none`), licensing load-forwarding, dead-store
     elimination, and speculative entry writes
     (`tb_protected_active_noalias_writable_sound`).
   - *Why `!Unpin` requires `noalias` exemption:* Self-referential `!Unpin`
     futures hold internal raw pointers aliasing fields of the same struct;
     unconditionally emitting `noalias` on `&mut S` where `S: !Unpin` allows
     LLVM `GVN` load-forwarding to miscompile self-referential writes
     (`canary_self_referential_noalias_refutes_compiles`, also denoted
     `canary_unconditional_noalias_on_unpin_false_unsound`, vs.
     `mirToAnLLVMPinSafe_verified`).
   - *Why `-Zmiri-tree-borrows-implicit-writes` is necessary and sufficient for
     `writable`:* Without `implicit_writes`, function-entry `&mut T` starts in
     `.reserved true false`, which survives foreign reads
     (`two_phase_reserved_allows_foreign_read`). A foreign read during a call
     where the Rust source never writes to `*x` is then legal in Tree Borrows
     yet observes LLVM's speculative `writable` store
     (`canary_reserved_not_writable_refutes_compiles`, also denoted
     `canary_reserved_without_implicit_write_violates_llvm_writable`).
4. **`seL4/graph-refine` `stack_logic.py` stack-slot scalarization eliminates
   array-SMT blowup in Lean 4 binary translation validation:**
   Rewriting in-bounds `SP + const_ofs` local stack spills and reloads into
   virtual scalar registers `sreg baseReg ofs` (`scalarizeStackSlice`) preserves
   all architectural registers and heap memory (`scalarizeStackSlice_sound`) and
   verifies spilled-and-reloaded machine slices against pure-register `AnLLVM`
   slices (`spilledMachineSlice_refines_anLLVMSlice`) with zero array-theory SMT
   and zero `Lean.ofReduceBool`.
5. **Compiler-emitted `UnrollHint` certificates enable kernel-checked $k:1$
   unrolled loop binary translation validation:**
   While $1:1$ cut-point alignment (`checkBinaryGraphRefine_sound`, also denoted
   `checkBackedgeRefine_sound`) suffices for cut-point-preserving `-O1`/`-O2`
   loops, $k\times$ loop unrolling with a remainder epilogue breaks $1:1$
   splitting (`canary_unrolled_1to1_split_fails`). Using `UnrollHint :=
   { unrollFactor := k, hasRemainderEpilogue := true }` and Euclidean division
   decomposition $n = k \cdot (n / k) + (n \bmod k)$
   (`runCountedLoop_unroll_decomp`), theorem `checkUnrolledLoopRefine_sound`
   verifies the $2\times$ unrolled machine loop (`unrolled2x_loop_verified` and
   `endToEnd_unrolled2x_mir_to_machine_verified`) inside the Lean 4 kernel.

## Applicability

These findings govern:

- **Anneal's LLVM backend (`rustc_codegen_anneal_llvm` / `AnLLVM`) and binary
  translation validator (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):** Specifically the vertical
  refinement chain `MonoMIR` $\to$ `AnLLVM` $\to$ `MachineCode` composed via
  `Trusted.Compiles` and `Anneal.pass_trans` (`Trusted/Refinement.lean` and
  `Anneal/Refinement.lean`).
- **Rust ABI attribute and MIR `Retag` lowering:** Emission of `noalias`,
  `readonly`, `writable`, `noundef`, `!range`, and `PassMode::Cast` widened
  loads in `rustc` (`compiler/rustc_middle/src/ty/layout.rs`,
  `compiler/rustc_ty_utils/src/abi.rs`, `compiler/rustc_codegen_llvm/src/{abi,builder}.rs`,
  and `compiler/rustc_codegen_ssa/src/mir/{block,operand,retag}.rs`) when paired
  with Miri's Tree Borrows operational semantics (`src/tools/miri/src/borrow_tracker/tree_borrows/`).
- **Post-`AnLLVM` assurance tiers:** Tier 1 (foundational `MonoMIR` $\to$
  `AnLLVM` proof in Lean 4 with `TrustedAssumption.LlvmBackend`), Tier 2
  (`Alive2` CI translation-validation oracle on `opt`), and Tier 3 (kernel-checked
  `GraphLang` binary translation validation from `AnLLVM` to RISC-V/ARM64/x86-64
  machine slices).

The subjects in `REPORT.json` relate as follows: `vellvm/vellvm`
(`506f1eb0be542611521985719b971fbce8498dc9` /
`0d6d403b8d411cacdace3dba0ccfd2b41b811b1e`), `AliveToolkit/alive2` (`v21.0`,
`adacbd5180ccf95075e9867c4f0c259f59c9fef2`), `snu-sf/crellvm`
(`668249b88756233f96b3ef21f12993501a348afc`), and `opencompl/lean-mlir`
(`b8c4a77131919c8e18cf8bc7fdde40ef3cf87924` /
`b8c4a771319a044854a4bbb49b8821381ef86ff8`) are the four LLVM IR formalizations
compared for `AnLLVM`'s design; `rust-lang/rust`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`,
`8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and
`92b5b8c87c61b20adc9001b41baf587634a74734`) defines the `rustc` ABI/retag rules
and Miri Tree Borrows state machine; `seL4/graph-refine`
(`94c93d18830d680fc6732d21fb16ca58ebca9dc5` /
`33d94bbdd6448ada368d4d925935e8cfdf7d93b4`) defines the `GraphLang` binary
translation validator and `stack_logic.py` scalarizer; and the two preserved
probes in `support/` mechanize the complete pipeline in Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Comparative Matrix of `Vellvm`, `lean-mlir` (`VeIR`), `Alive2`, `Crellvm`, and `seL4/graph-refine`

Basis: **source** + **derived**

| System | Pinned Revision(s) | IR Coverage & Memory Model | `undef` / `poison` / `freeze` Semantics | Verification Mechanism & TCB Footprint |
| :--- | :--- | :--- | :--- | :--- |
| **`vellvm/vellvm`** | `506f1eb0be542611521985719b971fbce8498dc9` / `0d6d403b8d411cacdace3dba0ccfd2b41b811b1e` | Full intra/inter-procedural `VIR` (`Denotation.v:1-939`): SSA `ocfg`, `alloca`, `load`/`store`, `gep inbounds`, calls, intrinsics, and byte-addressed block-offset memory (`MemoryBytes.v`, `Implementations/Memory.v`) | `undef`-free (`EXP_Undef => DVALUE_Poison`, `Denotation.v:122`); fresh `alloca` and struct padding are `poison_memory_byte` (`MemoryBytes.v:113, 632`); integer loads taint the whole word on any poison byte (`MemoryBytes.v:726-733`), while `DTYPE_B sz` preserves byte/bit granularity; `freeze` uses nondeterministic `DrawE` (`Freeze.v:32-111`) | Coq/Rocq interaction trees (`itree`) parameterized by effects `L0`..`L4`; foundational relational proofs in Coq kernel; no automated binary translation validator for `llc` |
| **`opencompl/lean-mlir`** (`VeIR`) | `b8c4a77131919c8e18cf8bc7fdde40ef3cf87924` / `b8c4a771319a044854a4bbb49b8821381ef86ff8` | Pure single-basic-block SSA bitvector expression DAG (`LeanMLIR/Dialects/LLVM/Basic.lean:28-553`): 31 integer/bitwise/cast ops + `select`/`icmp`/`freeze`; **no memory, pointers, `alloca`, `gep`, or CFG branches** | `LLVM.IntW w := PoisonOr (BitVec w)` (`Semantics.lean:28`); `IsRefinedBy` (`Poison.lean:105-108`); `LLVM.freeze` (`Semantics.lean:636-640`) deterministically collapses `.poison` to `.value 0` (**unsound for non-zero hardware registers**); no `undef` | Lean 4 `bv_decide` bit-blasting on single-op theorems (`Semantics.lean`), but `PeepholeRewrite` (`Rewrite.lean:23`) requires `lhs.denote = rhs.denote`, so `PeepholeRefine.lean:33` injects `axiom refinement_correctness {p: Prop} : p` (`False`) |
| **`AliveToolkit/alive2`** | `v21.0` (`adacbd5180ccf95075e9867c4f0c259f59c9fef2`) | Rich intra-procedural LLVM IR (`ir/instr.cpp`, `ir/memory.cpp`, `ir/attrs.cpp`): `load`/`store`, `alloca`, `malloc`/`free`, `gep inbounds`/`nusw`/`nuw`, `memcpy`, `!noundef`, `!range`, `!nonnull`, `!align`, `noalias`, `readonly`, `writable`, `dereferenceable` | Both `undef` (symbolic `undef_vars` quantified in refinement) and per-bit `poison` (`Byte` in `ir/memory.h`); `State::freeze` (`ir/instr.cpp:3203-3207`) resets `undef_vars` and substitutes fresh bitvector vars for poison bits | Unverified C++20 symbolic executor (`util/symexec.cpp`) emitting Z3 SMT queries; loops unrolled to a fixed bound (`-src-unroll` / `-tgt-unroll`); **not proof-producing** |
| **`snu-sf/crellvm`** | `668249b88756233f96b3ef21f12993501a348afc` | Vellvm-derived Coq IR for LLVM 3.7 (`coq/def/Validator.v`, `coq/proof/Adequacy.v`): SSA CFG, `alloca`, `load`/`store`, `gep`, and CompCert-style block memory | Legacy LLVM 3.7 `undef`/`poison` model; `Behavior.beh_error` acts as universal bottom (`Behavior.v:39-48`, `beh_refine`) | Instrumented C++ LLVM passes emit JSON hint certificates checked by Coq's `valid_module` (`Adequacy.v:87`); covers 4 passes (`GVN`, `SROA`, `LICM`, `InstCombine`) and depends on 11 admitted lemmas (`Adequacy.v:15`) |
| **`seL4/graph-refine`** | `94c93d18830d680fc6732d21fb16ca58ebca9dc5` / `33d94bbdd6448ada368d4d925935e8cfdf7d93b4` | Target-independent `GraphLang` (`syntax.py`, `problem.py`, `check.py`, `stack_logic.py`): typed nodes (`Basic`, `Cond`, `Call`, `Ret`, `Err`) over explicit `Mem`, `Dom`, `HTD`, and `PMS` state tokens for C, LLVM IR (`graph-to-graph/`), and ARM/RISC-V binaries | Machine-level bitvectors (`BitVec 32`/`64`) and flat `Mem : Addr → Word` arrays; source safety conditions exported as `Err` nodes (`check_no_err`) | Decomposes CFGs at Tarjan SCC loop-head cut-points (`problem.py:166-275`, `check.py:154-355`) and scalarizes stack slots (`stack_logic.py:356-466`) into loop-free `QF_ABV` VCs exported to HOL4/Isabelle (`Loop.thy`) |

### 2. Two Soundness Defects in `opencompl/lean-mlir` and Anneal's Zero-Axiom `DirectionalRewriteRefine` Repair

Basis: **source** + **execution** + **derived**

1. **Defect 1 — Deterministic `LLVM.freeze .poison = .value 0`
   (`LeanMLIR/Dialects/LLVM/Semantics.lean:636-640`):**
   `opencompl/lean-mlir` defines `LLVM.freeze` as a pure function mapping
   `.poison` to `.value 0`:
   ```lean
   def freeze {w : Nat} (x : LLVM.IntW w) : LLVM.IntW w :=
     match x with
     | .poison => .value 0
     | .value a => .value a
   ```
   While this allows `bv_decide` to bit-blast `freeze` expressions as pure
   functions, it is unsound for compiler lowering: if a mid-level pass optimizes
   `icmp eq (freeze %p), 0` to `true` (valid under `freeze .poison = .value 0`
   when `%p = .poison`) and instruction selection lowers `%p` to a physical
   register holding `42#64`, the compiled binary evaluates `42#64 == 0#64`
   (`false`) instead of `true`.
   - **Mechanized Canary and Repair (`support/track6_llvm_lowering_and_binary_tv_probe.lean:368-415`):**
     Theorem `leanMLIR_freeze_unsound_canary` (`L389-396`, also referred to as
     `lean_mlir_freeze_zero_unfaithful`) refutes refinement of `freezeLeanMLIR .poison`
     by a physical register holding `42#64`. Theorem `freezeSem_refines_any_bitvec`
     (`L400-415`) proves that modeling `freeze` via Anneal's multi-outcome
     `Partial (BitVec 64 → Prop)` semantics (`defined := True, post := fun v =>
     match x with | .poison => True | .val a => v = a`) is soundly refined by
     **every** concrete hardware register value `v : BitVec 64`.
2. **Defect 2 — `axiom refinement_correctness {p : Prop} : p` (`False`) in
   `toPeepholeUNSOUND` (`SSA/Projects/LLVMRiscV/PeepholeRefine.lean:33-53`):**
   `lean-mlir`'s rewrite engine (`LeanMLIR/Transforms/Rewrite/Rewrite.lean:23`)
   requires symmetric semantic equality `correct : ∀ V, lhs.denote V = rhs.denote V`.
   Because lowering `LLVM` (`PoisonOr (BitVec 64)`) to `RISCV64` (`BitVec 64`) is
   strictly directional (`PoisonOr.isRefinedBy_not_symm`, `L307-312`),
   `PeepholeRefine.lean:33-53` introduces `axiom refinement_correctness {p : Prop} : p`
   inside `toPeepholeUNSOUND`, contaminating `SSA/Projects/LLVMRiscV/Pipeline/`
   (including `Pipeline/freeze.lean:99`) with `False`.
   - **Zero-Axiom `DirectionalRewriteRefine` Repair
     (`support/track6_llvm_lowering_and_binary_tv_probe.lean:469-656`):**
     First, theorem `isRefinedBy_iff_toObservablePartial_le` (`L330-356`) proves
     the exact order-reversal isomorphism between forward poison refinement
     `IsRefinedBy src tgt` (`src = .poison ∨ src = tgt`) and Anneal's backward
     `Trusted.Partial` ordering `toObservablePartial tgt ≤ toObservablePartial src`.
     Second, `DirectionalRewriteRefine` (`L527-530`) replaces symmetric equality
     with `∀ acc, IsRefinedBy (evalHybridOp lhs acc) (evalHybridOp rhs acc)`.
     Using monotonicity (`evalHybridOp_mono`, `evalHybridProg_mono`), theorems
     `evalHybridProg_rewrite_refines` (`L544-557`, also denoted
     `compiles_anllvm_rewrite_chain`), `addNswToRv64Add_compiles` (`L632-641`),
     and `directionalRewriteCompiler_verified` (`L644-656`, also denoted
     `peephole_rewrite_sound_zero_axioms`) prove that directional instruction
     rewrites (`llvm.add nsw ↦ rv64.add`, `llvm.gep inbounds ↦ rv64.add`) satisfy
     `Trusted.Compiler.Verified` with **zero axioms** (`#print axioms` reports
     `does not depend on any axioms`).

### 3. `Vellvm` `DTYPE_B` (`AnByteWord` `[8 x i8]`) + Per-Byte `freeze` vs. `DTYPE_I` Whole-Word Poison Taint

Basis: **source** + **execution** + **derived**

In `rustc` (`compiler/rustc_codegen_ssa/src/mir/block.rs:2082-2103, 2534-2555`,
`compiler/rustc_target/src/callconv/mod.rs:348-378`, and
`compiler/rustc_codegen_llvm/src/abi.rs:289-334`), passing or returning a small
struct by value under `PassMode::Cast` emits a widened integer load (`load i64,
ptr %scratch`) across the struct's memory footprint, including any uninitialized
inter-field or trailing padding bytes.

Under both `Vellvm` (`src/rocq/Semantics/MemoryBytes.v:726-733`,
`absorb_pois (memory_bytes_to_int sz dbs)`) and `Alive2`
(`ir/memory.cpp:743-776`, `bytesToValue`), loading an integer type `DTYPE_I 64`
from an 8-byte span containing even one `.poison` (`uninit`) padding byte taints
the **entire** 64-bit integer word as `.poison`:

- **Negative Canary (`canary_int64_load_on_padding_taints_word`,
  `support/round2_track5_probe.lean:291-293`, also denoted
  `canary_dtype_i_whole_word_load_taints_initialized_bytes`):**
  For `paddedStructWord` (where byte `0` is initialized to `.val 0x2A#8` and
  padding bytes `1..7` are `.poison`), `loadInt64FromBytes paddedStructWord = .poison`.
  Consequently, even wrapping the `i64` load in a whole-word `freeze i64` can
  nondeterministically pick `0x0000_0000_0000_0000`, destroying the initialized
  field byte `0x2A#8`.
- **Positive `DTYPE_B` Theorem (`passModeCast_byte_vs_int_load_sound`,
  `support/round2_track5_probe.lean:300-304`, also denoted
  `freezeByteWord_preserves_defined_bytes`, and `paddedStructWord_byte0_preserved`,
  `L306-308`):**
  Representing memory words in `AnLLVM` as `AnByteWord := Fin 8 → PoisonOr (BitVec 8)`
  (`DTYPE_B`, `MemoryBytes.v:747-755`) and applying per-byte
  `freezeAnByte` (`loadByte64ThenFreeze w ndBytes`) guarantees that for every
  lane `i : Fin 8` with `w i = .val v`, `loadByte64ThenFreeze w ndBytes i = v`
  regardless of the nondeterministic padding oracle `ndBytes`.
- **`noundef` and `!range` Gating on `MaybeUninit` (`support/track6_llvm_lowering_and_binary_tv_probe.lean:662-774`):**
  Theorem `mirToAnLLVMSafe_verified` (`L753-759`) proves that omitting `noundef`
  and `!range` (`noundef := false, range := none`) and inserting `freeze` when
  lowering `MaybeUninit`/union slots satisfies `Compiler.Verified`, whereas
  `canary_uninit_noundef_refutes_compiles` (`L771-774`) proves that attaching
  `noundef := true` to an uninitialized load refutes `Compiles`.

### 4. Formal 4-State Tree Borrows Machine and Simulation of LLVM `noalias`, `readonly`, and `writable`

Basis: **source** + **execution** + **derived**

We audited Miri's Tree Borrows implementation in `rust-lang/rust`
(`src/tools/miri/src/borrow_tracker/tree_borrows/{mod,perms,tree,tree_visitor,diagnostics,foreign_access_skipping}.rs`
and `src/tools/miri/src/borrow_tracker/mod.rs`) alongside `rustc`'s MIR retagger
(`compiler/rustc_codegen_ssa/src/mir/retag.rs:190-263`), layout analysis
(`compiler/rustc_middle/src/ty/layout.rs:1136-1172`), and ABI attribute emission
(`compiler/rustc_ty_utils/src/abi.rs:286-411`).

#### 4.1 Exact 4-State Permission Machine (`TBPerm`, `tbStepPerm`, `tbStep`)

In `support/round2_track5_probe.lean:363-482`, `TBPerm` models the four
permission states of Miri's `PermissionPriv` (`perms.rs:10-89`):
- `.reserved (freeze : Bool) (conflicted : Bool)` (`ReservedFrz { conflicted }`
  when `freeze = true`, `ReservedIM` when `freeze = false`),
- `.active` (`Unique` in `perms.rs`, `Active` in the Tree Borrows paper),
- `.frozen` (`Frozen`), and
- `.disabled` (`Disabled`),

paired in `TBLocState` (`L459-463`) with `isProtected : Bool` (from
`RetagMode::FnEntry` in `tree_borrows/mod.rs:139, 213-219`) and `accessed : Bool`
(initialized to `true` on all in-bounds bytes of a retagged reference by
`LocationState::new_init` in `tree.rs:50-66` and `Permission::associated_access`
in `tree_borrows/mod.rs:334-345`).

| Initial State `perm` | `Child Read` (`perms.rs:138`) | `Child Write` (`perms.rs:186`) | `Foreign Read` (`perms.rs:149`) | `Foreign Write` (`perms.rs:202`) |
| :--- | :--- | :--- | :--- | :--- |
| `.reserved true false` | `.reserved true false` | `.active` | If `isProtected`: `.reserved true true`<br>Else: `.reserved true false` | `.disabled` (if `isProtected && accessed`: **`ProtectedDisabled` UB**) |
| `.reserved true true` | `.reserved true true` | If `isProtected`: **`ChildAccessForbidden` UB**<br>Else: `.active` | `.reserved true true` | `.disabled` (if `isProtected && accessed`: **`ProtectedDisabled` UB**) |
| `.reserved false _` (`!Freeze`) | `.reserved false _` | `.active` | `.reserved false _` | If `isProtected`: `.disabled` (**UB**)<br>Else: `.reserved false _` |
| `.active` (`Unique`) | `.active` | `.active` | If `isProtected`: `.disabled` (**`ProtectedDisabled` UB**)<br>Else: `.frozen` | `.disabled` (if `isProtected && accessed`: **`ProtectedDisabled` UB**) |
| `.frozen` | `.frozen` | **`ChildAccessForbidden` UB** | `.frozen` | `.disabled` (if `isProtected && accessed`: **`ProtectedDisabled` UB**) |
| `.disabled` | **`ChildAccessForbidden` UB** | **`ChildAccessForbidden` UB** | `.disabled` | `.disabled` |

Theorems `tbStepPerm_idempotent` (`L429-436`) and
`tb_foreign_read_noop_after_foreign_write` (`L445-452`) mechanize Miri's own
algebraic transition invariants (`perms.rs:798-822`).

#### 4.2 Simulation of LLVM `noalias`, `readonly`, and `writable` (`treeBorrows_implies_llvm_noalias_readonly_sound`)

1. **Protected `.frozen` (`&T` where `T: Freeze`) $\implies$ `noalias` +
   `readonly` (`tb_protected_frozen_readonly_noalias_sound`,
   `support/round2_track5_probe.lean:716-740`):**
   Lemma `tb_protected_frozen_trace_preserves_memVal` (`L616-641`) proves by
   induction on any interleaved trace `es : List TBEvent` of child and foreign
   reads/writes that starting from `tbInitProtected .frozen`, either
   `evalTBTrace` traps with UB (`none`) or `s'.memVal = v0` and
   `s'.tb = tbInitProtected .frozen`. Therefore, forwarding a pre-call load
   `let a = *x` across an arbitrary opaque environment trace `envTrace` to
   replace a post-call reload `let b = *x` satisfies `Compiles` for all
   `TBMirProg` with `initPerm = .frozen`.
2. **Protected `.active` (`&mut T` where `T: Unpin` with `implicit_writes`)
   $\implies$ `noalias` + `writable` (`tb_protected_active_noalias_writable_sound`,
   `support/round2_track5_probe.lean:818-835`):**
   Lemma `tb_protected_active_foreign_obs_isolation` (`L796-815`) proves that
   starting from `tbInitProtected .active`, any non-empty trace of `.foreign`
   reads or writes immediately traps with `ProtectedDisabled` UB (`none`).
   Therefore, LLVM's `noalias writable` speculative entry store (writing a
   temporary value on function entry and restoring/overwriting before exit)
   satisfies `Compiles` for all `TBMirProg` with `initPerm = .active`.
3. **Why `!Unpin` Self-Referential Futures Require `noalias` Exemption
   (`canary_self_referential_noalias_refutes_compiles` /
   `canary_unconditional_noalias_on_unpin_false_unsound`):**
   In `compiler/rustc_middle/src/ty/layout.rs:1158-1172`,
   `compiler/rustc_ty_utils/src/abi.rs:286-351`, and
   `compiler/rustc_codegen_ssa/src/mir/retag.rs:208`, `rustc` gates both LLVM
   `noalias` and Tree Borrows function-entry protectors on `&mut T` and `Box<T>`
   on `T: Unpin`. A pinned self-referential `Future` state machine `S: !Unpin`
   holds an internal raw pointer `self.ptr` aliasing another field `self.val` of
   the same struct. In `support/track6_llvm_lowering_and_binary_tv_probe.lean:784-936`:
   - Theorem `mirToAnLLVMPinSafe_verified` (`L890-898`) proves that setting
     `noalias := p.isUnpin` satisfies `Compiler.Verified` under
     `optNoAliasLoadForward`.
   - Theorem `canary_self_referential_noalias_refutes_compiles` (`L920-936`,
     also denoted `canary_unconditional_noalias_on_unpin_false_unsound`) proves
     that emitting `noalias := true` when `isUnpin = false` licenses LLVM load
     forwarding across a self-referential raw-pointer write (`10#64 ≠ 20#64`),
     refuting `Compiles`.
4. **Why `-Zmiri-tree-borrows-implicit-writes` Is Necessary and Sufficient for
   LLVM `writable` (`canary_reserved_not_writable_refutes_compiles` /
   `canary_reserved_without_implicit_write_violates_llvm_writable`):**
   In `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:145-149, 182-188`
   and `compiler/rustc_ty_utils/src/abi.rs:374-383`, `rustc` only emits LLVM
   `writable` when `-Zllvm-writable` is enabled, which corresponds in Miri to
   `-Zmiri-tree-borrows-implicit-writes` (initializing protected `&mut T` where
   `T: Unpin` directly to `Unique` / `.active` rather than `ReservedFrz` /
   `.reserved true false`). In `support/round2_track5_probe.lean:508-534, 853-864`:
   - Theorem `two_phase_reserved_allows_foreign_read` (`L508-521`) proves that
     `.reserved true false` survives a `.foreign` `.read` (transitioning to
     `conflicted = true` if protected, which blocks only subsequent child writes
     in `protected_reserved_conflicted_blocks_child_write`, `L523-534`).
   - Theorem `canary_reserved_not_writable_refutes_compiles` (`L859-864`, also
     denoted `canary_reserved_without_implicit_write_violates_llvm_writable`)
     proves on `reservedNotWritableCanaryProg` that if a protected `&mut T`
     starts in `.reserved true false` and the callee does not write to `*x` in
     the source program, a foreign read during the call succeeds without UB in
     Tree Borrows (`some 10#64`) but observes LLVM's speculative `writable`
     store (`some 99#64`), refuting `Compiles`.

Master theorem `treeBorrows_implies_llvm_noalias_readonly_sound`
(`support/round2_track5_probe.lean:881-909`) packages all four simulation
results with axiom footprint `[propext]`.

### 5. `seL4/graph-refine` `GraphLang` Binary Translation Validation: Stack-Slot Scalarization, Loop Backedges, and $k:1$ Unrolled Loops

Basis: **source** + **execution** + **derived**

#### 5.1 Static Stack-Slot Scalarization (`scalarizeStackSlice_sound`, Modeling `stack_logic.py`)

In `seL4/graph-refine/stack_logic.py:29-466, 995-1041, 1258-1273`
(`33d94bbdd6448ada368d4d925935e8cfdf7d93b4`), the validator avoids encoding
local stack frames as SMT arrays by normalizing stack pointers via
`split_sum_s_expr` and `offs_expr_const` into `sp + const_ofs`, rewriting
`MemAcc(Mem, sp + ofs, k)` and `MemUpdate(Mem, sp + ofs, v)` into scalar
assignments on synthetic variables `('Fake', k, ofs)` (`stack_virtualise_expr`,
`stack_virtualise_upd`), and separating heap pointers via `SplitMem` and
`dom_stack`.

In `support/round2_track5_probe.lean:941-1263`, we mechanize this pass directly
in Lean 4:
- `scalarizeStackInst baseReg` (`L1011-1015`) rewrites `stackStore ofs src` into
  `regMove (sreg baseReg ofs) src` and `stackLoad dst ofs` into
  `regMove dst (sreg baseReg ofs)`, where `sreg baseReg ofs := baseReg + ofs`.
- Theorem `scalarizeStackSlice_sound` (`L1162-1182`) proves by induction on any
  `slice : List StackInst` satisfying `sliceInFrameBounds baseReg frameSize slice = true`
  that the scalarized register-only slice preserves the simulation relation
  `stackScalarSim` (`∀ r < baseReg, s_scal.regs r = s_mach.regs r` and
  `s_scal.heapMem = s_mach.heapMem`).
- Theorem `spilledMachineSlice_refines_anLLVMSlice` (`L1225-1263`) verifies that
  a concrete machine slice that spills intermediate ALU results to stack slots
  `0` and `1`, clobbers its scratch register, and reloads both stack slots
  produces the exact same return register and heap state as the pure-register
  `anLLVMRawRegSlice`.

#### 5.2 Loop Backedge Alignment and $k:1$ `UnrollHint`-Guided Unrolled Loop Validation

In `seL4/graph-refine` (`problem.py:166-275`, `rep_graph.py:24-340`,
`check.py:154-355, 512-565`), `Problem.do_loop_analysis` identifies Tarjan SCC
loop heads and `splittable_points` (nodes whose removal breaks every cycle in
the SCC), and `split_checks` discharges pre-loop entry, inductive backedge step
(`(l_step, r_step)`), and post-loop exit VCs.

1. **$1:1$ Cut-Point Backedge Alignment (`checkBinaryGraphRefine_sound` /
   `checkBackedgeRefine_sound` and `runBitVecLoop_cutpoint_induct`):**
   In `support/track6_llvm_lowering_and_binary_tv_probe.lean:1034-1160`,
   `checkBinaryGraphRefine` (`L1034-1040`) and `checkBinaryGraphRefine_sound`
   (`L1043-1061`, also denoted `checkBackedgeRefine_sound`) verify $1:1$ loop
   refinement when `opt`/`llc` preserves loop step ratios (`l_step = 1,
   r_step = 1`, e.g., under `InstCombine`, `SROA`, `GVN`, `LICM`, and
   `IndVarSimplify`), and `endToEnd_mir_to_machine_verified` (`L1108-1117`)
   composes `MonoMIRLoopLang → AnLLVMLoopLang → MachineLoopLang`. However, as
   proved in `canary_unrolled_1to1_split_fails` (`L1064-1071`), $2\times$ loop
   unrolling (`mcStep = 2`) breaks $1:1$ cut-point alignment.
2. **Hint-Guided $k:1$ Unrolled Loop Validation (`checkUnrolledLoopRefine_sound`,
   `unrolled2x_loop_verified`):**
   Instead of `seL4/graph-refine/search.py:678-690`'s bounded counterexample
   search over hardcoded `(l_step, r_step)` pairs, Anneal's compiler backend
   emits `UnrollHint := { unrollFactor : Nat, hasRemainderEpilogue : Bool }`
   (`support/round2_track5_probe.lean:1266-1269`).
   - Theorem `runCountedLoop_unroll_decomp` (`L1314-1326`) uses Euclidean
     division $k \cdot (n / k) + (n \bmod k) = n$ (`Nat.div_add_mod`) to prove
     that for any `k > 0` and trip count `n`:
     $$\text{runCountedLoop}(\text{step}, n, s) = \text{runCountedLoop}\bigl(\text{step}, n \bmod k, \text{runCountedLoop}(\text{iterateStep}(k, \text{step}), n / k, s)\bigr)$$
   - Theorem `checkUnrolledLoopRefine_sound` (`L1350-1371`) proves that whenever
     `hint.unrollFactor > 0`, `hint.hasRemainderEpilogue = true`, one unrolled
     machine step equals `iterateStep hint.unrollFactor srcStep`, and one
     epilogue step equals `srcStep`, the unrolled machine loop followed by its
     remainder epilogue refines the source loop for all trip counts `n : Nat`.
   - Theorems `unrolled2x_loop_verified` (`L1413-1421`) and
     `endToEnd_unrolled2x_mir_to_machine_verified` (`L1460-1482`) verify the
     $2\times$ unrolled machine loop end-to-end from `MonoMIR` to machine code,
     while `canary_unrolled_missing_epilogue_unsound` (`L1486-1495`) proves that
     omitting the remainder epilogue (`hasRemainderEpilogue = false`) fails on
     odd trip counts (`n = 3`).

### 6. Complete Lean 4.34.1 Theorem Inventories

Basis: **execution**

#### 6.1 `support/track6_llvm_lowering_and_binary_tv_probe.lean` (1,215 lines)

| Declaration | Lines | Kind | Description & Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `monotone_id` / `monotone_comp` | `L201-212` | Theorem | Identity and composition of `Trusted.Monotone` behavior maps (no axioms) |
| `pass_trans` / `Compiles.comp` | `L214-236` | Theorem | Transitive composition of `Trusted.Compiles` across intermediate languages (no axioms) |
| `Compiler.SoundOn.verify` / `Compiler.SoundOn.comp` | `L238-266` | Theorem | Lifting `SoundOn` to `Compiler.Verified` and composing verified compiler passes (no axioms) |
| `PoisonOr.isRefinedBy_refl` / `_trans` | `L290-304` | Theorem | Reflexivity and transitivity of directional poison refinement `IsRefinedBy` (no axioms) |
| `PoisonOr.isRefinedBy_not_symm` | `L307-312` | Theorem | Asymmetry of `IsRefinedBy` (`.poison ⊑ₒ .val 0`, but `¬ (.val 0 ⊑ₒ .poison)`, no axioms) |
| `PoisonOr.isRefinedBy_iff_toObservablePartial_le` | `L330-356` | Theorem | Order-reversal isomorphism between `IsRefinedBy src tgt` and `toObservablePartial tgt ≤ toObservablePartial src` (no axioms) |
| `leanMLIR_freeze_unsound_canary` | `L389-396` | Canary | Refutes `opencompl/lean-mlir`'s deterministic `freeze .poison = .val 0` when lowered to a register holding `42#64` (no axioms) |
| `freezeSem_refines_any_bitvec` | `L400-415` | Theorem | Nondeterministic `freezeSem` is refined by any concrete hardware `BitVec 64` (no axioms) |
| `evalHybridOp_mono` / `evalHybridProg_mono` | `L499-525` | Theorem | Monotonicity of `AnLLVM`/`RV64` hybrid operations with respect to `IsRefinedBy` (no axioms) |
| `evalHybridProg_rewrite_refines` / `evalHybridProg_lower_refines` | `L544-589` | Theorem | Directional single-step and whole-program peephole rewrites refine the source program (no axioms) |
| `lowerAnLLVMOpToRv64_refines` | `L601-624` | Theorem | Lowering `llvm.add nsw` and `llvm.gep inbounds` to `rv64.add` satisfies `IsRefinedBy` (no axioms) |
| `addNswToRv64Add_compiles` | `L632-641` | Theorem | `directionalRewriteCompiler` satisfies `Trusted.Compiles` (no axioms) |
| `directionalRewriteCompiler_verified` | `L644-656` | Theorem | **Zero-Axiom Peephole Lowering:** `directionalRewriteCompiler` satisfies `Compiler.Verified` without `toPeepholeUNSOUND` (no axioms) |
| `mirToAnLLVMSafe_compiles` / `mirToAnLLVMSafe_verified` | `L733-759` | Theorem | **Safe `MaybeUninit`/Padding Lowering:** Omitting `noundef`/`!range` and inserting `freeze` satisfies `Compiler.Verified` (no axioms) |
| `canary_uninit_noundef_refutes_compiles` | `L771-774` | Canary | Attaching `noundef := true` to an uninitialized/padding load refutes `Compiles` (no axioms) |
| `mirToAnLLVMPinSafe_compiles` / `mirToAnLLVMPinSafe_verified` | `L871-898` | Theorem | **Safe `!Unpin` Lowering:** Gating `noalias` on `p.isUnpin` satisfies `Compiler.Verified` under `optNoAliasLoadForward` (no axioms) |
| `canary_self_referential_noalias_refutes_compiles` | `L920-936` | Canary | Emitting `noalias := true` on `!Unpin` self-referential struct refutes `Compiles` (`[propext]`) |
| `mirToAnLLVMLoop_compiles` | `L991-997` | Theorem | `MonoMIRLoopLang → AnLLVMLoopLang` loop lowering satisfies `Compiles` (no axioms) |
| `checkBinaryGraphRefine_sound` | `L1043-1061` | Theorem | **`GraphLang` $1:1$ Cut-Point Binary TV Soundness** (`[propext, Quot.sound]`) |
| `canary_unrolled_1to1_split_fails` | `L1064-1071` | Canary | $2\times$ unrolled machine loop fails $1:1$ cut-point check `checkBinaryGraphRefine` (no axioms) |
| `anLLVMToMachineLoop_passes_tv` / `_compiles` | `L1086-1099` | Theorem | Cut-point-preserving machine loop passes `checkBinaryGraphRefine` and satisfies `Compiles` (`[propext, Quot.sound]`) |
| `endToEnd_mir_to_machine_verified` | `L1108-1117` | Theorem | **End-to-End `MonoMIR` $\to$ `AnLLVM` $\to$ `MachineCode` Loop Verification** (`[propext, Classical.choice, Quot.sound]`) |
| `runBitVecLoop_cutpoint_induct` / `reassociatedMachineLoop_eq_anLLVMLoop` | `L1137-1160` | Theorem | Inductive bitvector loop cut-point congruence and `(acc + x) + c = (acc + c) + x` loop equivalence (`[propext]`) |

#### 6.2 `support/round2_track5_probe.lean` (1,532 lines)

| Declaration | Lines | Kind | Description & Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `Compiles.comp` / `Compiler.SoundOn.comp` | `L165-186` | Theorem | Transitive composition of `Compiles` and `Compiler.SoundOn` |
| `canary_int64_load_on_padding_taints_word` | `L291-293` | Canary | `load i64` (`DTYPE_I`) on `paddedStructWord` taints the entire 64-bit word to `.poison` (no axioms) |
| `passModeCast_byte_vs_int_load_sound` | `L300-304` | Theorem | **`DTYPE_B` Load + Per-Byte `freeze` Soundness:** Preserves every initialized byte lane `w i = .val v` (`[propext]`) |
| `paddedStructWord_byte0_preserved` | `L306-308` | Theorem | Field byte `0` (`0x2A#8`) of `paddedStructWord` is preserved for all padding oracles `ndBytes` (`[propext]`) |
| `tbStepPerm_idempotent` | `L429-436` | Theorem | Idempotency of raw Tree Borrows permission transitions (`perms.rs:798-805`, `[propext]`) |
| `tb_foreign_read_noop_after_foreign_write` | `L445-452` | Theorem | Foreign read after foreign write is a no-op (`perms.rs:800-822`, `[propext]`) |
| `two_phase_reserved_allows_foreign_read` | `L508-521` | Theorem | Both unprotected and protected `.reserved true false` survive a `.foreign` `.read` (no axioms) |
| `protected_reserved_conflicted_blocks_child_write` | `L523-534` | Theorem | Protected `.reserved true true` (`conflicted`) traps on `.child` `.write` (`perms.rs:189`, no axioms) |
| `tb_protected_frozen_step_characterization` / `trace_preserves_memVal` | `L536-550, 616-641` | Theorem | Protected `.frozen` invariant and memory constancy across arbitrary interleaved traces (`[propext]`) |
| `tb_protected_active_step_characterization` / `foreign_trace_isolation` | `L553-568, 644-663` | Theorem | Protected `.active` invariant and trap on any foreign read or write (`[propext]`) |
| `tb_protected_frozen_readonly_noalias_sound` | `L716-740` | Theorem | **Protected `.frozen` $\implies$ `noalias` + `readonly`:** Load forwarding across arbitrary `envTrace` satisfies `Compiles` (`[propext]`) |
| `tb_protected_active_foreign_obs_isolation` | `L796-815` | Theorem | Non-empty foreign trace on protected `.active` traps with `none` (`[propext]`) |
| `tb_protected_active_noalias_writable_sound` | `L818-835` | Theorem | **Protected `.active` $\implies$ `noalias` + `writable`:** Speculative entry write satisfies `Compiles` (`[propext]`) |
| `canary_reserved_not_writable_refutes_compiles` | `L859-864` | Canary | `.reserved true false` without `implicit_writes` refutes `Compiles` under `writable` speculative store (no axioms) |
| `treeBorrows_implies_llvm_noalias_readonly_sound` | `L881-909` | Theorem | **Master Tree Borrows $\to$ LLVM `noalias`/`readonly`/`writable` Simulation Theorem** (`[propext]`) |
| `scalarizeStackInst_step_sim` | `L1036-1159` | Theorem | Single-instruction simulation for `scalarizeStackInst` |
| `scalarizeStackSlice_sound` | `L1162-1182` | Theorem | **`stack_logic.py` Stack-Slot Scalarization Soundness:** Preserves all architectural registers `< baseReg` and `heapMem` (`[propext, Quot.sound]`) |
| `initScalarState_sim` | `L1209-1222` | Theorem | Initial scalarized state satisfies `stackScalarSim` |
| `spilledMachineSlice_refines_anLLVMSlice` | `L1225-1263` | Theorem | Concrete spilled-and-reloaded machine slice refines pure-register `anLLVMRawRegSlice` (`[propext, Quot.sound]`) |
| `runCountedLoop_add` / `runCountedLoop_mul` | `L1282-1311` | Theorem | Additive and multiplicative decomposition laws for `runCountedLoop` |
| `runCountedLoop_unroll_decomp` | `L1314-1326` | Theorem | **Fundamental $k:1$ Loop Decomposition:** $n = k \cdot (n / k) + (n \bmod k)$ unrolling law (`[propext, Quot.sound]`) |
| `runCountedLoop_congr_step` | `L1328-1341` | Theorem | Pointwise step equality implies `runCountedLoop` equality |
| `checkUnrolledLoopRefine_sound` | `L1350-1371` | Theorem | **`UnrollHint`-Guided $k:1$ Loop Validator Soundness** (`[propext, Quot.sound]`) |
| `machLoopStep2x_eq_iterateStep2` | `L1394-1402` | Theorem | One $2\times$ unrolled machine step equals `iterateStep 2 srcLoopStep1x` (`[propext, Quot.sound]`) |
| `unrolled2x_loop_verified` | `L1413-1421` | Theorem | Verifies the $2\times$ unrolled machine loop + epilogue for all trip counts `n` (`[propext, Quot.sound]`) |
| `endToEnd_unrolled2x_mir_to_machine_verified` | `L1460-1482` | Theorem | **Vertical `MonoMIR` $\to$ `AnLLVM` $\to$ `MachineASM` Proof for $2\times$ Unrolled Loop** (`[propext, Quot.sound]`) |
| `canary_unrolled_missing_epilogue_unsound` | `L1486-1495` | Canary | $2\times$ unrolled loop without remainder epilogue fails on odd trip count `n = 3` (no axioms) |

## Boundaries

- **Loop vectorization (`LoopVectorizePass`, `SLPVectorizerPass`) and structural
  loop transformations (`LoopFusion`, `LoopInterchange`, `JumpThreading`
  irreducible loops, known not to apply to `GraphLang` binary TV):** While
  `checkUnrolledLoopRefine_sound` handles constant-factor $k:1$ loop unrolling
  with remainder epilogues via `UnrollHint`, loop vectorization introduces
  runtime pointer-aliasing guards that clone a single source loop into three
  machine loops (fast vector loop, scalar fallback loop, scalar remainder loop),
  violating single-SCC cut-point pairing in `seL4/graph-refine/problem.py:166-275`.
  In Tier 3 (binary TV), `AnLLVM` modules must be compiled with
  `-fno-vectorize -fno-slp-vectorize`.
- **Unrecorded cross-function inlining (`InlinerPass` without `inline_script`,
  unsupported without compiler hints):** `seL4/graph-refine` (`problem.py:428-436`,
  `check.py:51-110`) requires an explicit inline log (`-Rpass=inline`) to splice
  inlined callee `GraphLang` graphs into the caller before Tarjan SCC analysis.
- **Standard LLVM IR text emission of `DTYPE_B` (`unsupported` natively in
  upstream `llvm-project`):** Because upstream `llvm-project` has not yet merged
  a first-class byte type `b8`/`b64` (`DTYPE_B` in `Vellvm`), `rustc_codegen_anneal_llvm`
  must lower `AnByteWord` (`DTYPE_B`) operations into standard LLVM IR either by
  keeping padding-bearing aggregates in memory (`PassMode::Indirect` / `memcpy`,
  which copies raw bytes without integer poison taint) or by loading individual
  initialized fields rather than emitting a widened `load i64` over uninitialized
  padding bytes.
- **Weak-protector `Box<T>` deallocation ordering at function exit (not examined
  in the single-location trace model):** Our `TBLocState` mechanization in
  `support/round2_track5_probe.lean` models `ProtectorKind::StrongProtector`
  (`&T` and `&mut T`). For `Box<T>` (`ProtectorKind::WeakProtector` in
  `src/tools/miri/src/borrow_tracker/mod.rs:135-152`), the callee is permitted
  to deallocate the box during the call (`nofree` is omitted on `Box<T>` in
  `compiler/rustc_ty_utils/src/abi.rs:384-396`), which requires tracking
  allocation liveness alongside `TBLocState`.

## Evidence

### Primary upstream sources

1. **`vellvm/vellvm`** (`506f1eb0be542611521985719b971fbce8498dc9` and
   `0d6d403b8d411cacdace3dba0ccfd2b41b811b1e`):
   - `src/rocq/Semantics/Denotation.v:122, 255-282` (`EXP_Undef => DVALUE_Poison`,
     `load_metadata_attrs` for `!noundef`, `!nonnull`, `!align`).
   - `src/rocq/Semantics/MemoryBytes.v:101-115, 622-637, 720-758`
     (`poison_memory_byte`, `serialize_struct_elements` padding, `DTYPE_I` whole-word
     poison taint in `memory_bytes_to_int` at `L726-733` vs. `DTYPE_B` byte
     preservation at `L747-755`).
   - `src/rocq/Semantics/Operations/Freeze.v:32-111` (nondeterministic `DrawE`
     `freeze_dvalue` and `freeze_bit`).
2. **`opencompl/lean-mlir`** (`b8c4a77131919c8e18cf8bc7fdde40ef3cf87924` and
   `b8c4a771319a044854a4bbb49b8821381ef86ff8`):
   - `LeanMLIR/LeanMLIR/Dialects/LLVM/Semantics.lean:28, 636-640`
     (`LLVM.IntW w := PoisonOr (BitVec w)` and `freeze .poison = .value 0`).
   - `LeanMLIR/LeanMLIR/Transforms/Rewrite/Rewrite.lean:23` (`PeepholeRewrite`
     symmetric equality requirement).
   - `SSA/Projects/LLVMRiscV/PeepholeRefine.lean:33-53`
     (`axiom refinement_correctness {p: Prop} : p` and `toPeepholeUNSOUND`) and
     `SSA/Projects/LLVMRiscV/Pipeline/freeze.lean:51-102`.
3. **`AliveToolkit/alive2`** (`v21.0`, `adacbd5180ccf95075e9867c4f0c259f59c9fef2`):
   - `ir/memory.h` and `ir/memory.cpp:687-777` (`Byte` representation and
     `bytesToValue` integer poison propagation at `L743-776`).
   - `ir/attrs.cpp:347-462` (`ParamAttrs::encode` for `NoUndef`, `Dereferenceable`,
     `NonNull`, `Writable`) and `ir/instr.cpp:3203-3207, 3757-3894`
     (`State::freeze` and `AssumeVal::execute` for `!range`, `!align`, `!nonnull`).
4. **`snu-sf/crellvm`** (`668249b88756233f96b3ef21f12993501a348afc`):
   - `coq/def/Validator.v:1-250`, `coq/proof/Behavior.v:39-48`, and
     `coq/proof/Adequacy.v:15, 87` (11 admitted relational lemmas).
5. **`rust-lang/rust`** (`58cf8f9c35b355199727627d07ae34a4e2846d67`,
   `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and
   `92b5b8c87c61b20adc9001b41baf587634a74734`):
   - `compiler/rustc_middle/src/ty/layout.rs:1136-1172` (`pointee_info_at`,
     `PointerKind::SharedRef { frozen }`, `PointerKind::MutableRef { unpin }`).
   - `compiler/rustc_ty_utils/src/abi.rs:256-411` (`arg_attrs_for_rust_scalar`,
     `NoAlias`, `ReadOnly`, `Writable`, `NoUndef`, `pointee_range`).
   - `compiler/rustc_codegen_ssa/src/mir/block.rs:2082-2103, 2534-2555`
     (`PassMode::Cast` widened integer loads) and
     `compiler/rustc_codegen_ssa/src/mir/retag.rs:190-263` (`is_protected`).
   - `src/tools/miri/src/borrow_tracker/mod.rs:135-152, 359-397`
     (`ProtectorKind`, `on_stack_pop`).
   - `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:125-221, 334-397`
     (`NewPermission::from_ref_ty`, `miri_tree_borrows_implicit_writes`,
     `associated_access`).
   - `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:10-233, 753-822`
     (`PermissionPriv` 4-state lattice, child/foreign transitions, idempotency
     tests).
   - `src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs:50-66, 133-161, 671-727`
     (`LocationState::new_init`, `LocationState::perform_access`,
     `perform_protector_end_access`).
6. **`seL4/graph-refine`** (`94c93d18830d680fc6732d21fb16ca58ebca9dc5` and
   `33d94bbdd6448ada368d4d925935e8cfdf7d93b4`):
   - `problem.py:166-275, 428-436, 778-785` (`do_loop_analysis`,
     `splittable_points`), `rep_graph.py:24-340`, `check.py:154-355, 512-565`
     (`split_checks`), `search.py:210-260, 678-690` (`split_Loops`),
     `loop-example/O2/ASM-annotated.txt`.
   - `stack_logic.py:29-224, 356-466, 995-1041, 1258-1273` (`split_sum_s_expr`,
     `offs_expr_const`, `stack_virtualise_expr`, `stack_virtualise_upd`,
     `dom_stack`, `SplitMem`).
7. **`joshlf/anneal`** (`e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` and
   `e75556f5767705404404c0675c6d2d9bcee41d6f`):
   - `trusted/lean/Trusted/Refinement.lean:1-532` and
     `theory/Anneal/Refinement.lean:1-273`.

### Preserved Lean 4.34.1 support artifacts

- `support/track6_llvm_lowering_and_binary_tv_probe.lean` (SHA-256
  `f22d763bc5d8fc5832e164f12e0e8937880dc488313f6bad077222ee623c1027`, 1,215
  lines).
- `support/round2_track5_probe.lean` (SHA-256
  `0740195c02f1249a56635bed1ec1bcd7909dc127c3cae3ed111889dc44602a50`, 1,532
  lines).

## Revalidation

To re-verify both standalone Lean 4.34.1 mechanizations and their `#guard_msgs
in #print axioms` checks from the package directory:

```bash
lean -j1 -M1024 support/track6_llvm_lowering_and_binary_tv_probe.lean
lean -j1 -M1024 support/round2_track5_probe.lean
```

Both commands must exit with code `0` and produce empty output (confirming all
21 embedded `#guard_msgs in #print axioms` assertions match and neither
`sorryAx` nor `Lean.ofReduceBool` appears in any theorem's axiom footprint).

Revalidate the upstream findings if:

1. `opencompl/lean-mlir` changes `LLVM.freeze` in
   `LeanMLIR/Dialects/LLVM/Semantics.lean:636-640` or replaces `toPeepholeUNSOUND`
   in `SSA/Projects/LLVMRiscV/PeepholeRefine.lean:33-53`.
2. `rust-lang/rust` modifies Miri's `PermissionPriv::perform_access` transition
   table in `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:135-233`,
   stabilizes `-Zllvm-writable` / `-Zmiri-tree-borrows-implicit-writes`, or
   changes `UnsafePinned` / `!Unpin` handling in `compiler/rustc_ty_utils/src/abi.rs`.
3. `vellvm/vellvm` or `llvm-project` adopts a native `bN` byte type in textual
   LLVM IR.
