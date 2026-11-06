# Clean-Slate `AnLLVM-IR` Semantics, Middle-End Pass Adaptation, Tree Borrows Lowering, and `GraphLang` Binary Translation Validation

## Summary

Designing a formally verified port of LLVM (`AnLLVM`) inside the Anneal
framework (`MIR -> AnLLVM -> ISA`) does not require bitcode or command-line
compatibility with upstream LLVM tools, but it **does** require keeping the IR
and analysis APIs close enough to upstream LLVM that existing middle-end passes
(`SROA`, `PromoteMemToReg`, `InstCombine`, `GVN`/`NewGVN`, `SCCP`, `LICM`,
`SimpleLoopUnswitchPass`, `IndVarSimplify`, `DSE`, `MemCpyOpt`, `BDCE`, `ADCE`,
`LoopDeletion`, `SimplifyCFG`, `JumpThreading`, `Inliner`, and `StackColoring`)
can be adapted 1-to-1 rather than invented from scratch.

Upstream LLVM IR accumulated six interacting semantic pathologies that obstruct
compositional formal verification:
1. **Dual Deferred-UB Values (`undef` alongside `poison`):** Every
  value-tracking query in `/usr/include/llvm-21/llvm/Analysis/ValueTracking.h`
  is duplicated across `UndefOrPoison`, `Poison`, and `Undef` variants
  (`canCreateUndefOrPoison` vs. `canCreatePoison` at `ValueTracking.h:766-769`;
  `isGuaranteedNotToBeUndefOrPoison` vs. `isGuaranteedNotToBePoison` vs.
  `isGuaranteedNotToBeUndef` at `ValueTracking.h:786-812`), while multi-use
  `undef` invalidates algebraic identities such as `x - x = 0`, `x ^ x = 0`, and
  `x + x = x << 1`.
2. **Provenance Erasure via `ptrtoint`/`inttoptr` + `GVN` + `BasicAA`:** As
  reproduced empirically with LLVM 21.1.8 `/usr/bin/opt` in
  `support/probe_a_ptrtoint_gvn.ll` (`@ptrtoint_inttoptr_gvn_instcombine`),
  comparing the integer address of a one-past-the-end pointer `%p_end`
  (`getelementptr inbounds i8, ptr %p, i64 8`) with an adjacent `noalias`
  allocation `%q` allows `GVN` to substitute `%ip` for `%iq`, `InstCombine` to
  fold `inttoptr (ptrtoint %p_end)` to `%p_end`, and `BasicAA` + `GVN` to
  conclude `NoAlias` between `store i32 42, ptr %p_end` and `load i32, ptr %q`,
  miscompiling the return value from `42` to `0`.
3. **Whole-Value Scalar Poison vs. Struct Padding Widening (`SROA`, `MemCpyOpt`,
  and `rustc`'s `PassMode::Cast`):** In `rustc_codegen_ssa/src/mir/block.rs:646`
  (`load_cast`) and `rustc_codegen_llvm/src/abi.rs:252-282`, small Rust structs
  containing uninitialized padding bytes are loaded and passed as wide integer
  registers (`i64` or `[N x i64]`). Under upstream LLVM's whole-value scalar
  poison semantics, any single uninitialized padding byte poisons the entire
  `i64` load unless `SROA` splits every access before whole-word observation.
4. **Pointer-Based `llvm.lifetime.start.p0`/`end.p0` vs. `InstCombine` and
  `StackColoring`:** As reproduced empirically with LLVM 21.1.8 `/usr/bin/opt`
  and `/usr/bin/llc` in `support/probe_d_lifetime_aa.ll`
  (`@disjoint_lifetime_stack_coloring`), `InstCombine` folds `icmp eq ptr %a,
  %b` to `false` unconditionally while `StackColoring` merges `%a` and `%b` into
  the exact same stack slot `0(%rsp)` across disjoint lifetime intervals, so
  runtime address observations compare equal (`true`) while the IR comparison
  folded to `false`.
5. **Untyped Metadata-Based Aliasing (`!noalias` / `!alias.scope`):** Lowering
  Rust `&mut T` / `&T` uniqueness into metadata nodes and
  `llvm.experimental.noalias.scope.decl` intrinsics requires quadratic metadata
  cloning during inlining and cannot express Tree Borrows' lazy `Reserved ->
  Active` activation or `Frozen` transitions.
6. **C++-Centric `mustprogress` / `willreturn` Defaults vs. Rust Divergence:**
  In `support/probe_e_mustprogress_loops.ll`, `LoopDeletion` deletes
  side-effect-free potentially-infinite loops under `mustprogress` and folds
  infinite loops to `unreachable` under `willreturn`. Rust semantics treat
  silent divergence (`EventualOut.diverges`) as well-defined observable behavior
  unless a finite-trip proof witness exists.

This report establishes two complementary pillars for `AnLLVM`:
- **Part I (`AnLLVM-IR` Clean-Slate Semantics):** Specifies **seven surgical
  semantic modifications** over upstream LLVM IR that eliminate all six
  soundness contradictions while preserving 1-to-1 compatibility lenses for
  `ValueTracking`, `MemorySSA`, `AAResults`, `PHINode`, `GEPOperator`,
  `ScalarEvolution`, and `LifetimeIntrinsic`, mechanized in
  `support/support_clean_slate_llvm_ir_probe.lean` (`1,272` lines of Lean
  4.34.1, zero `sorryAx`).
- **Part II (`opt` Middle-End Pipeline Adaptation & Ablation):** Decomposes LLVM
  21.1.8's 84-invocation `default<O2>` pipeline across all 20 major pass
  families into Anneal **Mode A** (Verified Direct Function), **Mode B**
  (Untrusted Rust Oracle + $O(N)$ Verified Lean `CertChecker`), and **Mode C**
  (Decompose/Defer/Drop); benchmarks cumulative pipelines `P0..P6` across 6
  realistic Rust kernels (`support/ablation_benchmark.py`,
  `support/ablation_results.json`), proving that a 12-pass scalar core (`P5`)
  cuts whole-module IR size by `-67.0%`, `alloca`s by `-100.0%` (`44 -> 0`),
  `x86_64` assembly by `-68.5%`, and `aarch64` assembly by `-71.4%` (matching
  scalar `default<O2>` within 1%); and mechanizes all four core pass families in
  `support/support_anllvm_middle_end_passes_probe.lean` (`2,819` lines of Lean
  4.34.1, zero `sorryAx`).

---

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
`AliveToolkit/alive2` (release 21.0), `snu-sf/crellvm`, `seL4/graph-refine`, and
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

- **Anneal's LLVM backend (`rustc_codegen_anneal_llvm` / `AnLLVM`), middle-end pass pipeline, and binary translation validator (`joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f`):** Specifically the vertical refinement chain `MonoMIR` $	o$ `AnLLVM` $	o$ `MachineCode` composed over Anneal's constructive refinement preorder:
  ```lean
  class Preorder (B : Type u) extends LE B where
    le_refl  : ∀ (b : B), b ≤ b
    le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

  structure Partial (B : Type u) where
    defined : Prop
    val     : defined → B

  instance instPreorderPartial (B : Type u) [Preorder B] : Preorder (Partial B) where
    le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
    le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
    le_trans h₁₂ h₂₃ h₃ :=
      let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
      let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
      ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

  abbrev Behavior (Query Out : Type) : Type := Query → Partial (Out → Prop)

  structure Language where
    Prog  : Type
    Query : Type
    Out   : Type
    sem   : Prog → Behavior Query Out
    dom   : Prog → Query → Prop

  inductive TerminationKind (Val : Type) where
    | normal (ret : Val)
    | unwind

  inductive EventualOut (Obs : Type := Empty) (Val : Type) where
    | terminated (trace : List Obs) (term : TerminationKind Val)
    | diverges   (trace : List Obs)
    | reacts     (trace : List Obs)
  ```
  where cross-language compilation `Compiles L_src L_tgt π s t` holds when `L_tgt.sem t ≤ π (L_src.sem s)` for a monotone behavior map `π`, `ProductiveCompiles` additionally preserves non-empty outcome existence (`ProductiveOn`), and `pass_trans` composes `Compiles` transitively across intermediate IRs.
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
`0d6d403b8d411cacdace3dba0ccfd2b41b811b1e`), `AliveToolkit/alive2` (`release 21.0`,
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
- **LLVM 21.1.8 middle-end pass adaptation (`llvm-project` `3623fe661ae35c6c80ac221f14d85be76aa870f1` / `llvm-21-dev` `21.1.8` and `rust-lang/rust` `49d734536222bf28bb6d07d885b3a81d145981da`):** Applies to all 20 pass families in `PassBuilder::buildPerModuleDefaultPipeline` (`default<O2>`) and their 1-to-1 adaptation over `AnLLVM-IR`'s seven clean-slate semantic modifications.

## Findings

### 1. Primary-Source Audit: LLVM 21.1.8 and `rustc` (`49d734536222bf28bb6d07d885b3a81d145981da`)

#### 1.1 LLVM 21.1.8 IR & Analysis Headers (`/usr/include/llvm-21/llvm/`)

| Header File | Lines Audited | Key Classes / Methods / Flags & Role in `AnLLVM-IR` |
| :--- | :--- | :--- |
| `IR/Instruction.def` | `1–255` | Defines all 67 upstream instruction opcodes: Terminators `1..11` (`Ret`, `Br`, `Switch`, `IndirectBr`, `Invoke`, `Resume`, `Unreachable`, `CleanupRet`, `CatchRet`, `CatchSwitch`, `CallBr`), Unary `12` (`FNeg`), Binary `13..30` (`Add`..`Xor`), Memory `31..37` (`Alloca`, `Load`, `Store`, `GetElementPtr`, `Fence`, `AtomicCmpXchg`, `AtomicRMW`), Cast `38..50` (`Trunc`..`BitCast`, `AddrSpaceCast`), Pad `51..52`, Other `53..67` (`ICmp`, `FCmp`, `PHI`, `Call`, `Select`, `UserOp1`, `UserOp2`, `VAArg`, `ExtractElement`, `InsertElement`, `ShuffleVector`, `ExtractValue`, `InsertValue`, `LandingPad`, `Freeze`). |
| `IR/Operator.h` | `65–590` | `Operator::hasPoisonGeneratingFlags()` (line 67), `hasPoisonGeneratingAnnotations()` (line 72); `OverflowingBinaryOperator` (`NoUnsignedWrap = 1<<0`, `NoSignedWrap = 1<<1`, line 78–144); `PossiblyExactOperator` (`IsExact = 1<<0`, L154–190); `PossiblyDisjointInst` (`IsDisjoint`, for `or disjoint`); `GEPOperator` (`getNoWrapFlags()`, `isInBounds()`, `hasNoUnsignedSignedWrap()`, `hasNoUnsignedWrap()`, `accumulateConstantOffset()`, `collectOffset()`, L419–553); `PtrToIntOperator` (L561–590). |
| `IR/GEPNoWrapFlags.h` | `26–104` | Bitfield encoding of GEP poison flags: `InBoundsFlag = 1<<0`, `NUSWFlag = 1<<1`, `NUWFlag = 1<<2`. Note `inbounds` implies `nusw` (`GEPNoWrapFlags::inBounds()` sets `InBoundsFlag \| NUSWFlag` at line 47), and `intersectForOffsetAdd()` (`line 85–90`) drops `InBoundsFlag` when combining two dynamic offsets while preserving `NUWFlag` and `NUSWFlag`. |
| `IR/Instructions.h` | `64–5171` | `AllocaInst` (line 64–172), `LoadInst` (L180–289), `StoreInst` (L296–416), `GetElementPtrInst` (L949–1150), `PHINode` (`getIncomingValue`, `setIncomingValue`, `getIncomingBlock`, `setIncomingBlock`, `replaceIncomingBlockWith`, `addIncoming`, `removeIncomingValue`, `getBasicBlockIndex`, `getIncomingValueForBlock`, `setIncomingValueForBlock`, `hasConstantValue`, `hasConstantOrUndefValue`, `isComplete`, L2638–2861), `FreezeInst` (L5152–5171). |
| `IR/IntrinsicInst.h` | `155–1746` | `LifetimeIntrinsic` (`llvm.lifetime.start` / `llvm.lifetime.end`, L155–165), `NoAliasScopeDeclInst` (`llvm.experimental.noalias.scope.decl`, L1649–1669), `AssumeInst` (`llvm.assume`, L1738–1746). |
| `Analysis/ValueTracking.h` | `61–825` | `computeKnownBits` (line 61–93), `GetPointerBaseWithConstantOffset` (L344–360), `isGuaranteedToTransferExecutionToSuccessor` (L691–710), `propagatesPoison` (L728), `mustTriggerUB` (L736), `programUndefinedIfUndefOrPoison` / `programUndefinedIfPoison` (L745–746), `canCreateUndefOrPoison` / `canCreatePoison` (L766–769), `impliesPoison` (L774), `isGuaranteedNotToBeUndefOrPoison` / `isGuaranteedNotToBePoison` / `isGuaranteedNotToBeUndef` (L786–812), `mustExecuteUBIfPoisonOnPathTo` (L821–823). |
| `Analysis/MemorySSA.h` | `140–1305` | `MemoryAccess` (L140–231), `MemoryUseOrDef` (L250–303), `MemoryUse` (L310–356), `MemoryDef` (L371–419), `MemoryPhi` (L479–661), `MemorySSA` (L702–913), `MemorySSAWalker::getClobberingMemoryAccess` (L1024–1107), `upward_defs_iterator` & `PHITransAddr` (L1228–1305). |
| `Analysis/AliasAnalysis.h` | `78–716` | `AliasResult::Kind` (`NoAlias=0`, `MayAlias=1`, `PartialAlias=2`, `MustAlias=3` + 29-bit signed `Offset` bitfield, line 78–140); `AAQueryInfo` (`MayBeCrossIteration`, L242–306); `AAResults` (`alias`, `isNoAlias`, `isMustAlias`, `pointsToConstantMemory`, `getModRefInfoMask`, `getArgModRefInfo`, `getMemoryEffects`, `getModRefInfo`, `callCapturesBefore`, L318–648); `BatchAAResults` (L656–716). |
| `Analysis/ScalarEvolution.h` | `127–956` | `SCEV::NoWrapFlags` (`FlagAnyWrap`, `FlagNW`, `FlagNUW`, `FlagNSW`, L127–133); `SCEVWrapPredicate::IncrementWrapFlags` (`IncrementNUSW`, `IncrementNSSW`, L343–348); `ScalarEvolution` (`getSCEV`, `getLosslessPtrToIntExpr`, `getPtrToIntExpr`, `getAddRecExpr`, `getGEPExpr`, `getPointerBase`, `removePointerBase`, `containsUndefs`, `getBackedgeTakenCount`, `getExitCount`, `getSmallConstantTripCount`, L448–956). |

#### 1.2 `rustc_codegen_ssa` and `rustc_codegen_llvm` (`49d734536222bf28bb6d07d885b3a81d145981da`)

| Source File | Lines | Key Findings for `MIR -> AnLLVM-IR` Lowering |
| :--- | :--- | :--- |
| `compiler/rustc_codegen_ssa/src/traits/builder.rs` | `353–373` | `BuilderMethods` **already** defines `ptradd(&mut self, ptr: Self::Value, offset: Self::Value) -> Self::Value` (`gep(self.cx().type_i8(), ptr, &[offset])`, L368–370) and `inbounds_ptradd(&mut self, ptr: Self::Value, offset: Self::Value) -> Self::Value` (`inbounds_gep(self.cx().type_i8(), ptr, &[offset])`, L371–373). |
| `compiler/rustc_codegen_ssa/src/mir/place.rs` | `180–294` | Struct/enum field projection (`PlaceRef::project_field`, L180–198, L249) **already** calls `bx.inbounds_ptradd(self.val.llval, bx.const_usize(offset.bytes()))`. Only array/slice indexing (`project_index`, L277–294) calls `bx.inbounds_nuw_gep(bx.cx().backend_type(layout), self.val.llval, &[llindex])`, which lowers directly to `ptradd inbounds nuw %base, (mul nuw %idx, sizeof(Elem))`. |
| `compiler/rustc_codegen_ssa/src/mir/statement.rs` | `72–85` | `mir::StatementKind::StorageLive(local)` (`line 72–78`) and `StorageDead(local)` (`line 79–85`) act directly on `LocalRef::Place(cg_place)` via `cg_place.storage_live(bx)` / `cg_place.storage_dead(bx)`. |
| `compiler/rustc_codegen_llvm/src/builder.rs` | `1911–1929` | In `lifetime_start`/`lifetime_end` (`L1911–1929`), `rustc` already branches on `llvm_util::get_version() >= (22, 0, 0)` (`L1921`): LLVM 22 drops the byte-size parameter and requires the lifetime intrinsic to act directly on the `alloca` after `LLVMRustStripPointerCasts(ptr)`. `AnLLVM-IR`'s `AllocaLive(allocId)` / `AllocaDead(allocId)` completes this transition at the semantic level. |
| `compiler/rustc_codegen_ssa/src/mir/block.rs` & `rustc_codegen_llvm/src/abi.rs` | `block.rs:612–648`, `abi.rs:45, 108, 252–282` | Under `PassMode::Cast { pad_i32, cast }`, `rustc` calls `load_cast` (`block.rs:646`) and `store_cast` (`abi.rs:270`) to load/store a struct across uninitialized padding bytes using an integer register type (`i64` or `[N x i64]`). Notice `abi.rs:45, 108` only attaches `llvm::AttributeKind::NoUndef` to `PassMode::Direct` (when `attrs.regular.contains(ArgAttribute::NoUndef)`), **not** `PassMode::Cast`, because `PassMode::Cast` registers carry uninitialized padding bits. |
| `compiler/rustc_codegen_llvm/src/builder.rs` | `1635–1670` | `load_from_place` attaches `!range` (`L1659`), `!nonnull` (`L1663`), and `!noundef` (`L1667–1669`) metadata on scalar loads when `scalar.is_always_valid(cx)` holds. |
| `compiler/rustc_codegen_llvm/src/attributes.rs` | `90–145` | `rustc` emits `WillReturn` (`L103`) **only** when `CodegenFnAttrFlags::FFI_CONST` or `FFI_PURE` is set, and **never** emits C++'s `mustprogress` attribute on general Rust functions because Rust loops may legitimately diverge (`loop {}`). |

---

### 2. Empirical LLVM 21.1.8 `/usr/bin/opt` & `/usr/bin/llc` Semantic Probes

All five empirical LLVM IR probe suites and their LLVM 21.1.8 outputs are
preserved in `support/`:

#### 2.1 Probe A (`support/probe_a_ptrtoint_gvn.ll` -> `support/probe_a_ptrtoint_gvn.opt.ll`): `ptrtoint` + `GVN` + `InstCombine` + `BasicAA` Miscompilation

Command:
```bash
/usr/bin/opt -S -passes="gvn,instcombine,gvn" support/probe_a_ptrtoint_gvn.ll
```
Input (`@ptrtoint_inttoptr_gvn_instcombine`):
```llvm
define i32 @ptrtoint_inttoptr_gvn_instcombine(ptr noalias %p, ptr noalias %q) {
entry:
  store i32 0, ptr %q, align 4
  %p_end = getelementptr inbounds i8, ptr %p, i64 8
  %ip = ptrtoint ptr %p_end to i64
  %iq = ptrtoint ptr %q to i64
  %cmp = icmp eq i64 %ip, %iq
  br i1 %cmp, label %if.true, label %if.false

if.true:
  %q_cast = inttoptr i64 %iq to ptr
  store i32 42, ptr %q_cast, align 4
  %v = load i32, ptr %q, align 4
  ret i32 %v

if.false:
  ret i32 -1
}
```
LLVM 21.1.8 Output:
```llvm
define i32 @ptrtoint_inttoptr_gvn_instcombine(ptr noalias %p, ptr noalias %q) {
entry:
  store i32 0, ptr %q, align 4
  %p_end = getelementptr inbounds nuw i8, ptr %p, i64 8
  %cmp = icmp eq ptr %p_end, %q
  br i1 %cmp, label %if.true, label %if.false

if.true:                                          ; preds = %entry
  store i32 42, ptr %p_end, align 4
  ret i32 0

if.false:                                         ; preds = %entry
  ret i32 -1
}
```
**Diagnosis:**
1. The first `GVN` pass propagates `%ip == %iq` inside `if.true`, rewriting
  `%q_cast = inttoptr i64 %iq to ptr` into `inttoptr i64 %ip to ptr`.
2. `InstCombine` folds `inttoptr (ptrtoint %p_end)` to `%p_end`, silently
  replacing the provenance of `%q` (`allocId = q`) with the provenance of
  `%p_end` (`allocId = p`).
3. The second `GVN` pass queries `BasicAA` on `store i32 42, ptr %p_end` and
  `load i32, ptr %q`, receives `NoAlias` (since `%p` and `%q` are `noalias`),
  and forwards `store i32 0, ptr %q` to `ret i32 0`—even though `%p_end` and
  `%q` have the exact same runtime address.

#### 2.2 Probe B (`support/probe_b_sroa_padding.ll` -> `support/probe_b_sroa_padding.opt.ll`): `SROA` on `PassMode::Cast` Struct Padding

Command:
```bash
/usr/bin/opt -S -passes="sroa,instcombine,memcpyopt,sroa" support/probe_b_sroa_padding.ll
```
On `@rust_pass_mode_cast_sroa`, where `%slot = alloca { i8, [3 x i8], i32 }` is
initialized at offset `0` (`i8 %a`) and offset `4` (`i32 %b`) and loaded as a
single `i64`:
```llvm
define i64 @rust_pass_mode_cast_sroa(i8 %a, i32 %b) {
entry:
  %slot.sroa.21.0.insert.ext = zext i32 %b to i64
  %slot.sroa.21.0.insert.shift = shl nuw i64 %slot.sroa.21.0.insert.ext, 32
  %slot.sroa.0.0.insert.ext = zext i8 %a to i64
  %slot.sroa.0.0.insert.insert = or disjoint i64 %slot.sroa.21.0.insert.shift, %slot.sroa.0.0.insert.ext
  ret i64 %slot.sroa.0.0.insert.insert
}
```
**Diagnosis:** `SROA` synthesizes `zext` + `shl nuw` + `or disjoint`, filling
bits `8..31` (the 3 uninitialized padding bytes) with `0`. In upstream LLVM's
whole-value poison semantics, the unoptimized `load i64, ptr %slot` reads 3
uninitialized (`poison`) bytes, which under a whole-value scalar model would
make the entire `i64` poison. Under `AnLLVM-IR`'s `MaskedWord 64` (Modification
3), the unoptimized `load i64` has `poisonMask = 0x00000000_00FFFF00#64`, and
`SROA`'s output has `poisonMask = 0#64` with identical bits on `0..7` and
`32..63`—making `SROA`'s transformation a direct bitwise refinement
(`MaskedWord.Refines`).

#### 2.3 Probe C (`support/probe_c_unswitch_freeze.ll` -> `support/probe_c_unswitch_freeze.opt.ll`): `SimpleLoopUnswitchPass` Inserting `freeze`

Command:
```bash
/usr/bin/opt -S -passes="loop-mssa(simple-loop-unswitch<nontrivial>)" support/probe_c_unswitch_freeze.ll
```
- In `@unswitch_unconditional_no_freeze`, `br i1 %cond` executes unconditionally
  on the first loop iteration (`loop.header`), so
  `mustExecuteUBIfPoisonOnPathTo` (`ValueTracking.h:821`) proves `%cond` cannot
  be poison if the loop is entered, hoisting `br i1 %cond` without `freeze`.
- In `@unswitch_guarded_inserts_freeze`, `br i1 %cond` is guarded inside the
  loop by `%g = call i1 @step_guard(i32 %iv)`, so `%cond` might never be
  branched on in the source program. LLVM 21.1.8's `SimpleLoopUnswitchPass`
  automatically inserts `%cond.fr = freeze i1 %cond` in `loop.header.preheader`:
  ```llvm
  loop.header.preheader:                            ; preds = %entry
    %cond.fr = freeze i1 %cond
    br i1 %cond.fr, label %loop.header.preheader.split.us, label %loop.header.preheader.split
  ```

#### 2.4 Probe D (`support/probe_d_lifetime_aa.ll` -> `support/probe_d_lifetime_aa.opt.ll` & `support/probe_d_lifetime_aa.s`): `DSE`, `InstCombine`, and `StackColoring` Contradiction

Command:
```bash
/usr/bin/opt -S -passes="dse,gvn,instcombine" support/probe_d_lifetime_aa.ll > support/probe_d_lifetime_aa.opt.ll
/usr/bin/llc -O2 support/probe_d_lifetime_aa.opt.ll -o support/probe_d_lifetime_aa.s
```
In `@disjoint_lifetime_stack_coloring`:
1. `opt -passes="dse,gvn,instcombine"` folds `%cmp_ir = icmp eq ptr %a, %b` to
  `store i1 false, ptr %out_eq, align 1` (`movb $0, (%rdi)`).
2. `llc -O2` (`StackColoring`) merges `%a = alloca [64 x i8]` and `%b = alloca
  [64 x i8]` into a single 64-byte stack allocation (`subq $64, %rsp`) and
  passes `%rsp` to both `observe_addr(ptr %a)` (`movq %rsp, %rdi`) and
  `observe_addr(ptr %b)` (`movq %rsp, %rdi`).
3. Consequently, `*out_eq` receives `false` while `%addr_a == %addr_b` evaluates
  to `true` at runtime.

#### 2.5 Probe E (`support/probe_e_mustprogress_loops.ll` -> `support/probe_e_mustprogress_loops.opt.ll`): `LoopDeletion` and `ADCE` vs. `mustprogress` / `willreturn`

Command:
```bash
/usr/bin/opt -S -passes="loop(loop-deletion),adce,simplifycfg" support/probe_e_mustprogress_loops.ll
```
- `@rust_may_diverge_loop(i1 %c)` (no `mustprogress`): the potentially-infinite
  loop is **preserved**.
- `@cpp_mustprogress_loop(i1 %c) mustprogress`: `LoopDeletion` **deletes** the
  loop and simplifies the function to `ret i32 7`.
- `@unconditional_infinite_loop_willreturn() mustprogress willreturn`: folded to
  `unreachable`.

---

### 3. Part I: The Seven Clean-Slate Semantic Modifications of `AnLLVM-IR`

#### Modification 1: Complete `undef` Elimination -> Pure `poison` + `freeze`

- **Formal Semantics (`AnLLVM-IR`):**
  - `UndefValue` and `PoisonValue` (a subtype of `UndefValue` in upstream LLVM)
    are unified into a single deferred-UB lattice element: per-bit `poison` in
    scalars (`MaskedWord w`) and `Byte.poison` in memory.
  - Uninitialized `alloca` bytes, struct padding bytes, and dead stack bytes
    after `AllocaDead` hold `Byte.poison`.
  - `freeze` (`MaskedWord.freeze x choice`) is the **sole** instruction in
    `AnLLVM-IR` that introduces nondeterministic (demonic) bit choices,
    resolving only those bit positions where `x.poisonMask = 1` and clearing
    `poisonMask := 0`.
- **Upstream Pass Adaptation Recipe (1-to-1):**
  - In `ValueTracking`: collapse the duplicate API pairs in
    `/usr/include/llvm-21/llvm/Analysis/ValueTracking.h:745-812`:
    - `canCreateUndefOrPoison` $\equiv$ `canCreatePoison`
    - `isGuaranteedNotToBeUndefOrPoison` $\equiv$ `isGuaranteedNotToBePoison`
    - `programUndefinedIfUndefOrPoison` $\equiv$ `programUndefinedIfPoison`
    - `PHINode::hasConstantOrUndefValue` (`Instructions.h:2840`) $\equiv$
      `hasConstantOrPoisonValue`
    - `ScalarEvolution::containsUndefs` (`ScalarEvolution.h:550`) $\equiv$
      `containsPoison`
  - In `InstCombine` and `Reassociate`: forward value refinements `x - x -> 0`,
    `x ^ x -> 0`, `x & 0 -> 0`, `x | -1 -> -1`, and `x + x -> x << 1` become
    **unconditionally sound** for multi-use `x` without checking
    `isGuaranteedNotToBeUndef(x)` (and when bidirectional register-state
    equality is required, `freeze` is inserted explicitly).
  - Only transformations that *duplicate uses of a value into independent
    control-flow decisions* (such as `SimpleLoopUnswitchPass` hoisting a guarded
    branch condition, as verified in `support/probe_c_unswitch_freeze.ll`) must
    insert `freeze` when `!isGuaranteedNotToBePoison(cond)` and
    `!mustExecuteUBIfPoisonOnPathTo(cond, preheader)`.

#### Modification 2: First-Class Provenance Pointers `Ptr(allocId, offset, tag)` + `ptradd` + Split `ptrtoaddr` vs. `ptrtoint`

- **Formal Semantics (`AnLLVM-IR`):**
  - Every pointer value in `AnLLVM-IR` has semantic value `Ptr := { allocId :
    AllocId, offset : Int, tag : BorrowTag }` (or `null` / `poison`).
  - Type-indexed `getelementptr <ty>, ptr %p, idx...` is replaced in the core
    operational semantics by byte-offset pointer addition:
    $$\text{ptradd}(\text{flags}, p, \Delta) \quad (\text{flags} \subseteq
    \{\texttt{inbounds}, \texttt{nusw}, \texttt{nuw}\})$$ matching
    `GEPNoWrapFlags` (`/usr/include/llvm-21/llvm/IR/GEPNoWrapFlags.h:26-104`).
    Specifically, `ptradd inbounds p delta` returns `Ptr(p.allocId, p.offset +
    delta, p.tag)` if both `p.offset` and `p.offset + delta` lie in `[0,
    size(p.allocId)]` (explicitly permitting one-past-the-end `offset ==
    size(p.allocId)`), and `Ptr.poison` otherwise.
  - Pointer-to-integer conversion is split into two distinct operations:
    1. **`ptrtoaddr p : i64`**: Purely projects the runtime integer address
      `layout.base(p.allocId) + p.offset` without exposing `p.allocId` and
      without any inverse cast to `ptr`.
    2. **`ptrtoint_expose p : i64` / `inttoptr_reconstruct addr : ptr`**:
      Side-effecting provenance-exposure / angelically-nondeterministic
      reconstruction operations (ISO C 2023 PNVI-ae-udi / Rust Strict Provenance
      `expose_provenance` / `with_exposed_provenance`), marked with memory
      side-effects so `GVN` and `InstCombine` never fold `inttoptr(ptrtoint(p))`
      across provenance boundaries.
  - Pointer equality `icmp eq ptr %p, %q`:
    - Compares `ptrtoaddr(%p) == ptrtoaddr(%q)` (returning `poison` if either
      pointer's allocation is dead). Crucially, `GVN` is **forbidden** from
      substituting `%p` for `%q` as a `ptr` value from `icmp eq ptr %p, %q`
      unless `isSameProvenance(%p, %q)` holds; `GVN` may only substitute
      `ptrtoaddr(%p)` for `ptrtoaddr(%q)`.
- **Upstream Pass Adaptation Recipe (1-to-1):**
  - **Syntactic `GEPOperator` Adapter:** Keep `GEPOperator`
    (`Operator.h:419-553`) as a view over `ptradd` + linear `add`/`mul` trees
    via `GEPOperator::collectOffset` (`Operator.h:545`) and
    `GetPointerBaseWithConstantOffset` (`ValueTracking.h:344`).
  - **`GVN` Adapter:** In `GVN::propagateEquality`, when `icmp eq ptr %p, %q`
    holds on an edge, register equality of `ptrtoaddr(%p)` and `ptrtoaddr(%q)`
    automatically, and only register pointer-SSA replacement `%q -> %p` if
    `BasicAA::isMustAlias(%p, %q)` (same base `AllocId` and equal offset) holds.
  - **`InstCombine` Adapter:** Delete the unsound `inttoptr (ptrtoint %p) -> %p`
    fold when `%p` was substituted by integer `GVN`, and restrict `icmp eq ptr
    %alloca_a, %alloca_b -> false` to program points where both `AllocaId`s are
    proven simultaneously live (`isKnownLive(a, CxtI) && isKnownLive(b, CxtI)`).
  - **`rustc` Lowering (`rustc_codegen_ssa`):** `PlaceRef::project_field`
    (`place.rs:180-198, 249`) already emits `bx.inbounds_ptradd`. Rust's
    `ptr::addr()` lowers to `ptrtoaddr`, breaking the `ptrtoint` + `GVN` +
    `BasicAA` contradiction completely.

#### Modification 3: Bitwise-Masked Scalar Values (`MaskedWord w`) & First-Class Byte Memory (`Byte`)

- **Formal Semantics (`AnLLVM-IR`):**
  - Every `w`-bit scalar register value is a `MaskedWord w`:
    $$\texttt{MaskedWord } w := \{ \texttt{bits} : \texttt{BitVec } w,\;
    \texttt{poisonMask} : \texttt{BitVec } w \}$$ where bit `i` is defined iff
    `poisonMask[i] = 0`.
  - Bitwise operations (`and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `trunc`,
    `zext`, `sext`, `extractSlice`, `append`, `or disjoint`) propagate
    `poisonMask` per-bit (with Kleene absorption on `and` with a defined `0` bit
    and `or` with a defined `1` bit).
  - Arithmetic operations (`add`, `sub`, `mul`) propagate poison upward from the
    least significant poisoned bit `k` (bits `0..k-1` remain defined; bits
    `k..w-1` have `poisonMask = 1`), and overflow flags (`nuw`, `nsw`) set
    `poisonMask := allOnes w` on wrap.
  - Memory stores and loads operate on `Byte`:
    - `Byte.poison`: uninitialized or dead byte (`toMaskedByte = allPoison 8`).
    - `Byte.bits (v : MaskedWord 8)`: scalar byte with per-bit poison mask.
    - `Byte.ptrFrag (allocId : AllocId) (offset : Int) (tag : BorrowTag)
      (fragIdx : Fin 8)`: the `fragIdx`-th byte of a 64-bit pointer stored in
      memory. Loading all 8 consecutive fragments `0..7` of the same `(allocId,
      offset, tag)` as `ptr` reconstructs `Ptr(allocId, offset, tag)`; loading
      them as `i64` yields `allPoison 64` (since `ptrtoaddr` must be explicit).
  - Parameter/return `noundef` attribute is generalized to a bitmask attribute
    `noundef_mask(mask : BitVec w)` (where full `noundef` is
    `noundef_mask(allOnes w)`), triggering immediate UB iff `(val.poisonMask &&&
    mask) != 0`.
- **Upstream Pass Adaptation Recipe (1-to-1):**
  - **`computeKnownBits` (`ValueTracking.h:61-93`):** Upstream `KnownBits`
    (`Zero`, `One` bitvectors) is **already** a sound abstract domain over
    `MaskedWord w`: bit `i` is in `Known.Zero` iff `poisonMask[i] = 0 ∧ bits[i]
    = 0`, and in `Known.One` iff `poisonMask[i] = 0 ∧ bits[i] = 1`.
  - **`SROA` & `MemCpyOpt` (`support/probe_b_sroa_padding.ll`):** Widening
    adjacent field loads across uninitialized struct padding into an `i64` load
    and extracting the fields via `lshr`/`trunc`/`and` is **unconditionally
    sound without inserting `freeze`**, as proved in Theorem
    `sroa_load_widening_across_padding_sound`.
  - **`rustc` `PassMode::Cast` (`rustc_codegen_ssa/src/mir/block.rs:646`):**
    When `rustc` passes or returns a padded struct in an `i64` register via
    `load_cast` / `store_cast`, `rustc` can attach
    `noundef_mask(initialized_bits)` instead of dropping `noundef` entirely.

#### Modification 4: Predecessor-Indexed $\phi$-Tables / Basic-Block Arguments Isomorphism & `PHINode` Compatibility Lens

- **Formal Semantics (`AnLLVM-IR`):**
  - Each basic block header defines a typed parameter vector $\vec{x}_B =
    (x_{B,1} : \tau_1, \dots, x_{B,k} : \tau_k)$, and each terminator edge
    $(B_{\text{pred}} \to B)$ supplies an argument tuple
    $\vec{v}_{(B_{\text{pred}} \to B)}$, stored in a canonical
    predecessor-indexed table `PhiTable B : Fin k → (PredIndex B → ValId)`.
  - Unlike upstream LLVM IR—where a basic block can contain 50 separate
    `PHINode` instructions whose predecessor lists can be permuted or
    temporarily out of sync during CFG edits—`AnLLVM-IR` enforces by type
    construction that every join variable in block `B` is indexed by the exact
    same predecessor list `preds(B)`.
- **Upstream Pass Adaptation Recipe (1-to-1):**
  - Expose a zero-cost `PHINode` view over row `i` of `PhiTable B` implementing
    the exact methods of
    `/usr/include/llvm-21/llvm/IR/Instructions.h:2696-2820`:
    `getIncomingValueForBlock(BB)`, `setIncomingValueForBlock(BB, V)`,
    `addIncoming(V, BB)`, `removeIncomingValue(BB)`, and
    `replaceIncomingBlockWith(OldBB, NewBB)`.
  - As mechanized in `phi_table_block_arg_lens_isomorphism`, these lens
    operations commute with edge-argument redirection (`SimplifyCFG`,
    `JumpThreading`, `LoopUnswitch`) and satisfy the exact Put-Get / Put-Other
    laws expected by `Mem2Reg`, `SROA`, `GVN`, and `LCSSA` (`MemoryPhi` in
    `MemorySSA.h:479-661`).

#### Modification 5: Direct `AllocId`-Scoped `AllocaLive`/`AllocaDead` Instead of Pointer-Based `llvm.lifetime.start/end`

- **Formal Semantics (`AnLLVM-IR`):**
  - Stack allocation and lifetime are separated into:
    1. `%p = alloca <size>, <align>` (assigns a static `AllocId` `a` in the
      function frame, initially `live a = false` and filled with `Byte.poison`,
      or `live a = true` for entry-live allocas).
    2. `alloca_live(a : AllocId)`: sets `live a := true` and resets all bytes of
      `a` to `Byte.poison`, nondeterministically assigning `physAddr(a)`
      disjoint from all *currently live* allocations (`live b = true`).
    3. `alloca_dead(a : AllocId)`: sets `live a := false` and resets all bytes
      of `a` to `Byte.poison`.
  - Any `load`, `store`, or `ptrtoaddr` on a pointer `p` with `live(p.allocId) =
    false` is immediate UB (for `load`/`store`) or `poison` (for `ptrtoaddr`).
- **Why This Solves Both Upstream Pathologies:**
  1. **No Escaped-Alias Ambiguity:** Because `alloca_dead(a)` acts on the
    `AllocId` `a` in the machine state rather than a pointer SSA value `%ptr`,
    every alias `q` with `q.allocId = a` is deterministically invalidated the
    instant `alloca_dead(a)` executes.
  2. **Sound Stack Coloring (`StackColoring` + `InstCombine`):** As proved in
    `alloca_live_dead_disjoint_coloring_sound`, coloring two allocations `a` and
    `b` with disjoint live intervals to the same physical stack slot is a
    bi-simulation of the abstract machine, provided `InstCombine` only folds
    `icmp eq ptr %a, %b -> false` at program points where `a` and `b` are
    **simultaneously live**.

#### Modification 6: First-Class Tree-Borrows `BorrowTag` & `ProtectorId` on Memory Operations Instead of `noalias` Scope Metadata

- **Formal Semantics (`AnLLVM-IR`):**
  - Instead of untyped `!noalias` and `!alias.scope` metadata lists +
    `llvm.experimental.noalias.scope.decl` (`IntrinsicInst.h:1649`), `AnLLVM-IR`
    includes four first-class borrow instructions / annotations:
    1. `%p_child = retag %p_parent, <perm_init : Reserved|Active|Frozen>,
      <opt_protector : Option ProtectorId>`
    2. `protector_end <protector : ProtectorId>` (emitted before `ret` /
      `resume`)
    3. `load <ty>, ptr %p, align <A>, [protector_set : Set ProtectorId]`
    4. `store <ty> %v, ptr %p, align <A>, [protector_set : Set ProtectorId]`
  - In the operational semantics, each allocation `a` maintains a Tree Borrows
    tree $T_a$ of `BorrowTag`s with per-byte permissions $\{\texttt{Reserved},
    \texttt{Active}, \texttt{Frozen}, \texttt{Disabled}\}$. Every `load`/`store`
    through pointer `p = Ptr(a, off, tag)` performs a local access at `tag`
    (which is a **foreign** access to all non-ancestors/relatives in $T_a$),
    checking active `ProtectorId`s.
- **Upstream Pass Adaptation Recipe (1-to-1):**
  - **`AAResults` / `BasicAA` (`AliasAnalysis.h:318-648`) Plug-In:** Implement
    `TreeBorrowsAA::alias(LocA, LocB, AAQI)` and `getModRefInfo(Call, Loc,
    AAQI)`: if `LocA.Ptr` has tag $\tau_A$ and `LocB.Ptr` has tag $\tau_B$ in
    incompatible subtrees where at least one is `Active` (or protected `Frozen`
    vs. write), return `AliasResult::NoAlias`. Thus `GVN`, `LICM`, `DSE`, and
    `MemCpyOpt`—which query `AAResults::alias` and
    `MemorySSAWalker::getClobberingMemoryAccess` (`MemorySSA.h:1024`)—get full
    Rust reference aliasing power without changing their pass logic.
  - **`Inliner` Adaptation (Zero Metadata Cloning):** Inlining a callee simply
    **deletes `protector_end(p_id)` and removes `p_id` from the inlined
    instructions**. As proved in
    `inlining_protector_drop_refines_and_not_symmetric`, dropping a
    `ProtectorId` is a pure forward refinement (`tbTransition true ... ≤
    tbTransition false ...`) and requires zero metadata rewriting.

#### Modification 7: Rust-Default `mayDiverge` Loop/Function Semantics with Explicit `FiniteTripWitness`

- **Formal Semantics (`AnLLVM-IR`):**
  - In `AnLLVM-IR`'s instantiation of Anneal's `StepLanguage` (`EventualOut
    Obs`), silent divergence (`EventualOut.diverges`) is a well-defined
    observable behavior, **not** `Partial.ub`.
  - Functions and loop headers default to `mayDiverge` (no C++ `mustprogress` or
    `willreturn` assumption).
  - A loop header `L` or function `F` may carry an optional `FiniteTripWitness`
    annotation generated by `ScalarEvolution` (`getBackedgeTakenCount` /
    `getSmallConstantTripCount` in `ScalarEvolution.h:680-750`) certifying a
    bounded measure in `Nat` that strictly decreases on every backedge without
    poison.
- **Upstream Pass Adaptation Recipe (1-to-1):**
  - In `LoopDeletionPass::run` and `AggressiveDeadCodeElimination`, replace
    `F.mustProgress()` / `L.isFinite()` with
    `L.hasVerifiedFiniteTripWitness(SE)`. If `ScalarEvolution` provides a
    `FiniteTripWitness`, `LoopDeletion` deletes the dead loop soundly
    (`witnessed_loop_deletion_sound`); otherwise the loop is preserved
    (`canary_unwitnessed_loop_deletion_unsound`).

---

### 4. Part II: Structural Decomposition of LLVM 21.1.8's `default<O2>` Middle-End Pipeline

#### 4.1 Six-Phase Decomposition of the 84-Invocation `default<O2>` Pipeline

Executing `/usr/bin/opt -passes='default<O2>' -print-pipeline-passes
-disable-output` on LLVM 21.1.8 (`PassBuilder::buildPerModuleDefaultPipeline`)
reveals 84 pass invocations organized into six structural phases:

1. **Phase I — Early Function Canonicalization
  (`buildFunctionSimplificationPipeline` pre-IPO):** Runs `lower-expect`,
  conservative `simplifycfg` (`keep-loops`), `sroa<modify-cfg>`, and
  `early-cse<>` (hash-table value numbering without `MemorySSA`) to promote
  local stack variables before interprocedural analysis.
2. **Phase II — Early Interprocedural & Global Cleanup:** Runs `ipsccp`,
  `called-value-propagation`, `globalopt`, and a second function cleanup
  (`mem2reg`, `instcombine<max-iterations=1>`,
  `simplifycfg<switch-range-to-icmp>`).
3. **Phase III — CGSCC Bottom-Up Inlining + Function Simplification
  (`devirt<4>`):** Traverses the Call-Graph Strongly Connected Components
  bottom-up (iterating up to 4 times if devirtualization exposes new direct call
  targets). For each SCC, runs `inline` (`InlinerPass`), `function-attrs`, and
  the 31-step per-function simplification pipeline:
   - **Stage III.a (Post-Inlining Scalar Promotion & CFG Cleanup):**
     `sroa<modify-cfg> -> early-cse<memssa> -> jump-threading ->
     correlated-propagation -> simplifycfg -> instcombine ->
     aggressive-instcombine -> tailcallelim -> simplifycfg -> reassociate ->
     constraint-elimination`.
   - **Stage III.b (Canonical Loop Optimization Cycle):**
     `loop-mssa(loop-instsimplify -> loop-simplifycfg ->
     licm<no-allowspeculation> -> loop-rotate -> licm<allowspeculation> ->
     simple-loop-unswitch<trivial>) -> simplifycfg -> instcombine ->
     loop(loop-idiom -> indvars -> loop-deletion -> loop-unroll-full)`.
   - **Stage III.c (Global Redundancy & Memory Optimization Cycle):**
     `sroa<modify-cfg> -> mldst-motion -> gvn<> -> sccp -> bdce -> instcombine
     -> jump-threading -> correlated-propagation -> adce -> memcpyopt -> dse ->
     loop-mssa(licm<allowspeculation>) -> simplifycfg<hoist/sink-common-insts>
     -> instcombine`.
4. **Phase IV — Post-Inlining Module Dead-Code & Attribute Propagation:** Runs
  `deadargelim`, `globalopt`, `globaldce`, `elim-avail-extern`,
  `rpo-function-attrs`, and `recompute-globalsaa`.
5. **Phase V — Late Vectorization & Runtime Unrolling Pipeline:** Runs
  `loop-rotate`, `loop-deletion`, `loop-distribute`, `loop-vectorize`,
  `loop-load-elim`, `instcombine`,
  `simplifycfg<switch-to-lookup;no-keep-loops>`, `slp-vectorizer`,
  `vector-combine`, `loop-unroll<O2>`, `sroa<preserve-cfg>`, `licm`,
  `div-rem-pairs`, `tailcallelim`, and final `simplifycfg`.
6. **Phase VI — Module Finalization:** Runs `globaldce`, `constmerge`,
  `rel-lookup-table-converter`, and `verify`.

#### 4.2 Complete 20-Pass Architectural Adaptation Matrix for `AnLLVM`

Every major pass in `default<O2>` maps to one of three Anneal verification
modes:
- **Mode A (Verified Direct Function — `BB8.PassCompiler.ofFn`):** Implemented
  directly as a pure, total Lean 4 function `f : AnLLVMProg → AnLLVMProg` with a
  universal proof `∀ s, ProductiveCompiles s (f s)`.
- **Mode B (Untrusted Rust Oracle + Verified Lean Certificate Checker —
  `BB8.CertChecker`):** An untrusted Rust optimizer computes expensive fixed
  points, graph reachability, alias queries, or `SCEV` recurrences and emits
  `(t, cert)`. A small, total Lean 4 boolean checker `check s t cert = true`
  validates the transformation in $O(N)$ time, backed by `check_sound`.
- **Mode C (Decompose / Defer / Drop):** Decomposed into simpler Mode A/B
  primitives, deferred to Phase 2 vectorization, or dropped.

| # | Pass Name | LLVM 21.1.8 Header & Class | Positions in `default<O2>` | Upstream Analysis Dependencies | Anneal Mode | Certificate Schema (`Cert`) / Decomposition | Lean Kernel Validator Complexity |
| :- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | `SROA` | `llvm/Transforms/Scalar/SROA.h` (`SROAPass`) | Phase I, III.a, III.c, V (`4x`) | `AssumptionCache`, `DominatorTree`, `TargetTransformInfo` | **Mode B** | `SroaMem2RegCert`: `slices : List SroaSliceSpec` (`alloc`, `off`, `sz`, `ssaReg`), `phiMap : BlockId → List (SliceId × RegId)` | $O(\|I\| + \|S\|^2)$ (pairwise slice disjointness + single IR linear scan) |
| 2 | `PromoteMemToReg` (`mem2reg`) | `llvm/Transforms/Utils/PromoteMemToReg.h` (`PromotePass`) | Phase II (`1x`), plus inside `SROA::promoteAllocas` (`4x`) | `DominatorTree`, `AssumptionCache` | **Mode B** | Unified with `SroaMem2RegCert`: explicit per-block entry $\phi$ bindings and per-instruction reaching register map (no kernel IDF construction) | $O(\|I\| + \|E_{\text{CFG}}\| \cdot \|S\|)$ (local def-use + edge $\phi$ wiring check) |
| 3 | `EarlyCSE` | `llvm/Transforms/Scalar/EarlyCSE.h` (`EarlyCSEPass`) | Phase I (no `memssa`), Phase III.a (`memssa`) (`2x`) | `TargetLibraryInfo`, `TargetTransformInfo`, `DominatorTree`, `AssumptionCache`, optional `MemorySSA` | **Mode B** (subsumed by Pass 15) | Subsumed by `MemSsaGvnDseCert` (`leaderMap : InstId → RegId` + dominance witness); separate `EarlyCSE` validator unnecessary | $O(\|I\|)$ (dominating leader equality check) |
| 4 | `InstCombine` | `llvm/Transforms/InstCombine/InstCombine.h` (`InstCombinePass`) | Phase II, III.a, III.b, III.c (`2x`), V (`3x`) (`8x` total) | `AAResults`, `AssumptionCache`, `TargetLibraryInfo`, `TargetTransformInfo`, `DominatorTree`, `OptimizationRemarkEmitter` | **Mode A** (core ~120 rules) | Pure table-driven verified pattern matcher `rewriteStmtsInstCombine` (~120 rules with explicit `freeze` / non-poison guards; `Cert = PUnit`) | $O(\|I\|)$ single-pass linear reduction |
| 5 | `AggressiveInstCombine` | `llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h` (`AggressiveInstCombinePass`) | Phase III.a (`1x`) | `AssumptionCache`, `DominatorTree`, `TargetLibraryInfo`, `TargetTransformInfo` | **Mode C -> Mode A** | Decomposed: truncated bitwidth expression DAG folding (`TruncInstCombine`) merged as 8 width-narrowing rules in Mode A `InstCombine` | $O(\|I\|)$ |
| 6 | `SimplifyCFG` | `llvm/Transforms/Scalar/SimplifyCFGPass.h` (`SimplifyCFGPass`) | Phase I, II, III.a (`2x`), III.b, III.c, V (`2x`) (`8x` total) | `TargetTransformInfo`, `AssumptionCache`, `DominatorTree` | **Mode B** | `SimplifyCfgCert`: sequence of atomic CFG step witnesses (`FoldConstBr`, `MergeLinearBlocks`, `DropUnreachableBlock`, `ThreadEmptyBlock`, `SpeculateSelect`) | $O(\|B\| + \|E_{\text{CFG}}\|)$ per atomic step |
| 7 | `Inliner` + `AlwaysInliner` | `llvm/Transforms/IPO/Inliner.h` (`InlinerPass`), `AlwaysInliner.h` | Phase II (`always-inline`), Phase III (`cgscc(inline)`) | `AAResults`, `AssumptionCache`, `ProfileSummaryInfo`, `BlockFrequencyInfo`, `TargetTransformInfo`, `InlineAdvisor` | **Mode B** | `InlineCert`: `(callSiteId, calleeId, regRenameOffset, allocRenameOffset, returnBlockId)` (cost heuristics stay in untrusted Rust) | $O(\|I_{\text{caller}}\| + \|I_{\text{callee}}\|)$ alpha-renaming & CFG splice check |
| 8 | `IPSCCP` + `SCCP` | `llvm/Transforms/IPO/SCCP.h` (`IPSCCPPass`), `Scalar/SCCP.h` (`SCCPPass`) | Phase II (`ipsccp`), Phase III.c (`sccp`) | `DominatorTree`, `TargetLibraryInfo`, `AssumptionCache` | **Mode B** | `SccpCert`: post-fixpoint abstract lattice assignment `valMap : RegId → LatticeVal` (`Top ∣ Const c ∣ Bottom`) + `execBlocks : BlockSet` | $O(\|I\| + \|E_{\text{CFG}}\|)$ (1-pass post-fixpoint monotonicity check) |
| 9 | `CalledValuePropagation` (`CVP`) | `llvm/Transforms/IPO/CalledValuePropagation.h` | Phase II (`1x`) | `TargetLibraryInfo` | **Mode C** | Defer/Drop: attaches `!callees` metadata for indirect call promotion; redundant once `devirt` / trait-object vtable witnesses are explicit in Mode B `InlineCert` | N/A |
| 10 | `CorrelatedValuePropagation` | `llvm/Transforms/Scalar/CorrelatedValuePropagation.h` | Phase III.a, III.c (`2x`) | `LazyValueInfo` (`LVI`), `DominatorTree`, `AssumptionCache` | **Mode B** | `CvpRangeCert`: per-edge constant range interval `rangeMap : (BlockId × RegId) → ConstRange` validated along branch conditions (`icmp`) | $O(\|I\| + \|E_{\text{CFG}}\|)$ |
| 11 | `JumpThreading` | `llvm/Transforms/Scalar/JumpThreading.h` (`JumpThreadingPass`) | Phase III.a, III.c (`2x`) | `LazyValueInfo`, `DominatorTree`, `TargetLibraryInfo`, `TargetTransformInfo` | **Mode B** (merged with `SimplifyCFG`) | Decomposed into `DuplicatePredBlock + FoldConstBr` certificates inside `SimplifyCfgCert` (avoids verifying `LVI` cache invalidation) | $O(\|I_{\text{dup}}\|)$ |
| 12 | `Reassociate` | `llvm/Transforms/Scalar/Reassociate.h` (`ReassociatePass`) | Phase III.a (`1x`) | `DominatorTree` | **Mode B** | `ReassocCert`: sorted rank permutation witness `perm : List Nat` showing flattened AC expression trees are multiset-equal (`nuw`/`nsw` stripped unless proven) | $O(\|T\| \log \|T\|)$ multiset equality check |
| 13 | `TailCallElim` | `llvm/Transforms/Scalar/TailCallElimination.h` (`TailCallElimPass`) | Phase III.a, V (`2x`) | `TargetTransformInfo`, `DominatorTree`, `AAResults` | **Mode B** | `TailCallCert`: witness that no stack `alloca` escapes prior to `call`, followed by header $\phi$ backedge transformation for self-recursion | $O(\|I\|)$ |
| 14 | `ConstraintElimination` | `llvm/Transforms/Scalar/ConstraintElimination.h` | Phase III.a (`1x`) | `DominatorTree`, `LoopInfo`, `ScalarEvolution`, `OptimizationRemarkEmitter` | **Mode B** | `FarkasCert`: non-negative rational/integer Farkas multipliers $\lambda_1, \dots, \lambda_k \ge 0$ witnessing that dominating branch inequalities imply target `icmp` | $O(k \cdot \|C\|)$ linear combination check |
| 15 | `NewGVN` / `GVN` | `llvm/Transforms/Scalar/NewGVN.h` (`NewGVNPass`), `GVN.h` (`GVNPass`) | Phase III.c (`gvn<>`, replaced in `AnLLVM` by `NewGVN` congruence model) | `AssumptionCache`, `DominatorTree`, `TargetLibraryInfo`, `AAResults`, `MemorySSA` | **Mode B** | `MemSsaGvnDseCert`: congruence leader map `leader : RegId → RegId`, `MemorySSA` version tags `(memVer, prevVer)`, store-to-load & load-to-load witnesses | $O(\|I\|)$ |
| 16 | `MemCpyOpt` | `llvm/Transforms/Scalar/MemCpyOptimizer.h` (`MemCpyOptPass`) | Phase III.c (`1x`) | `AAResults`, `AssumptionCache`, `DominatorTree`, `TargetLibraryInfo`, `MemorySSA` | **Mode B** | Unified with `MemSsaGvnDseCert`: `MemSetFormation`, `MemCpyToMemSet`, and `CallSlotNoAliasForward` (`byval`/return-slot copy elision) witnesses | $O(\|I\|)$ |
| 17 | `DSE` (`DeadStoreElimination`) | `llvm/Transforms/Scalar/DeadStoreElimination.h` (`DSEPass`) | Phase III.c (`1x`) | `AAResults`, `DominatorTree`, `PostDominatorTree`, `MemorySSA`, `TargetLibraryInfo` | **Mode B** | Unified with `MemSsaGvnDseCert`: killing-store witness `(deadStoreIdx, killingStoreIdx, noAliasWitnessList)` along `MemorySSA` def-def chain | $O(\|I\| \cdot d_{\text{clobber}})$ |
| 18 | `BDCE` (`BitTrackingDCE`) | `llvm/Transforms/Scalar/BDCE.h` (`BDCEPass`), `Analysis/DemandedBits.h` | Phase III.c (`1x`) | `DemandedBits` (`DominatorTree`, `AssumptionCache`) | **Mode A** | Verified 1-pass backward `DemandedBits` bitmask propagation + dead-bit operand replacement (`(x ∣ c₁) & c₂ ↦ x & c₂` when `c₁ & c₂ = 0`) | $O(\|I\|)$ |
| 19 | `ADCE` (`AggressiveDCE`) | `llvm/Transforms/Scalar/ADCE.h` (`ADCEPass`) | Phase III.c (`1x`) | `PostDominatorTree` | **Mode A / Mode B** | `AdceCert`: `liveInsts : BitSet`, `liveBlocks : BitSet`; kernel checks closure under operand uses and control dependencies (with `FiniteTripWitness` for loops) | $O(\|I\| + \|E_{\text{CFG}}\|)$ |
| 20 | Loop Pass Suite (`LoopRotate`, `LICM`, `IndVarSimplify`, `LoopDeletion`, `LoopUnrollFull`) | `LoopRotation.h`, `LICM.h`, `IndVarSimplify.h`, `LoopDeletion.h`, `LoopUnrollPass.h` | Phase III.b, III.c, V (`3x` loop pipelines) | `LoopInfo`, `DominatorTree`, `ScalarEvolution` (`SCEV`), `MemorySSA`, `AAResults`, `TargetTransformInfo` | **Mode B** | `ScevLicmCert`: preheader hoist list with `isSafeToSpeculate` + non-interference check, `SCEVAddRecExpr` $\{base, +, stride\}$ induction witness, constant unroll factor $k$ | $O(\|I_{\text{loop}}\|)$ |

---

### 5. Empirical Pass-Ablation Benchmark (`P0..P6`) on Realistic Rust Code

#### 5.1 Benchmark Suite & Methodology (`support/ablation_benchmark.py`, `support/bench_suite.rs`)

To measure the quantitative contribution of each middle-end pass family on Rust
code, `support/ablation_benchmark.py` compiles six representative `#![no_std]`
Rust functions (`support/bench_suite.rs`, raw metrics in
`support/ablation_results.json`) using `rustc -Copt-level=0
-Coverflow-checks=off -Cpanic=abort --emit=llvm-ir`, strips `optnone`, runs
cumulative `opt 21.1.8` pipelines `P0` through `P6` (plus `P6_scalar`), and
lowers each IR module with `llc 21.1.8 -O2` to both `x86_64-unknown-linux-gnu`
and `aarch64-unknown-linux-gnu`:

1. **`slice_sum_stride`:** Strided slice accumulation (`while i < s.len() { acc
  = acc.wrapping_add((s[i] ^ mask) + (scale * 3)); i += stride }`) exercising
  `SROA`, `Inliner`, `LoopRotate`, `LICM`, and `IndVarSimplify`.
2. **`option_Result_chain`:** Nested `Option::map`, `Option::and_then`,
  `Option::filter`, and `unwrap_or` combinator chain exercising `Inliner`,
  post-inline `SROA`, `JumpThreading`, `SCCP`, and `SimplifyCFG`.
3. **`struct_field_packing`:** Local `PacketHeader` aggregate construction,
  method mutation, masked bitwise extraction (`(raw | 0x1000_0000) & 0x0FFF`),
  and redundant field overwrites exercising `SROA`, `InstCombine`, `BDCE`,
  `GVN`, and `DSE`.
4. **`checked_index_bounds`:** Sequential slice indexing (`buf[idx]`, `buf[idx +
  1]`, `buf[idx + 2]`, `buf[idx + 3]`) under an explicit guard `if idx + 4 <=
  buf.len()` exercising `Inliner`, `CorrelatedValuePropagation`,
  `ConstraintElimination`, and `SimplifyCFG`.
5. **`iterator_fold_filter`:** Idiomatic `s.iter().copied().map(...).filter(...)
  .fold(...)` pipeline exercising `Inliner` (across 11 `core::iter` closures and
  adapters), `SROA`, `SimplifyCFG`, and `LoopRotate`.
6. **`enum_state_machine`:** Loop-driven protocol state machine (`Idle`,
  `Header(u64)`, `Payload { acc, rem }`, `Done(u64)`) exercising `SROA` on
  tagged unions, `SimplifyCFG` switch-folding, `LICM`, and `GVN`.

#### 5.2 Whole-Module Quantitative Ablation Table

| Pipeline | IR Insts (vs. `P0`) | `alloca` (vs. `P0`) | `load` (vs. `P0`) | `store` (vs. `P0`) | `br`/`sw` | `call` (vs. `P0`) | `phi` | `x86_64` Asm Insts (vs. `P0`) | `aarch64` Asm Insts (vs. `P0`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`P0` (Baseline `-O0`)** | `697` (`100.0%`) | `44` (`100.0%`) | `110` (`100.0%`) | `109` (`100.0%`) | `95` | `74` (`100.0%`) | `0` | `733` (`100.0%`) | `718` (`100.0%`) |
| **`P1` (`SROA+Mem2Reg+SimplifyCFG`)** | `461` (`-33.9%`) | `10` (`-77.3%`) | `37` (`-66.4%`) | `28` (`-74.3%`) | `59` | `64` (`-13.5%`) | `33` | `653` (`-10.9%`) | `606` (`-15.6%`) |
| **`P2` (`P1 + InstCombine+EarlyCSE`)** | `424` (`-39.2%`) | `10` (`-77.3%`) | `35` (`-68.2%`) | `25` (`-77.1%`) | `59` | `65` (`-12.2%`) | `33` | `642` (`-12.4%`) | `598` (`-16.7%`) |
| **`P3` (`P2 + Inliner+SROA+GlobalDCE`)** | `303` (`-56.5%`) | **`0` (`-100.0%`)** | `9` (`-91.8%`) | `1` (`-99.1%`) | `69` | `5` (`-93.2%`) | `42` | `343` (`-53.2%`) | `308` (`-57.1%`) |
| **`P4` (`P3 + GVN+DSE+SCCP+BDCE+ADCE`)** | `260` (`-62.7%`) | `0` (`-100.0%`) | `8` (`-92.7%`) | `1` (`-99.1%`) | `57` | `5` (`-93.2%`) | `34` | `282` (`-61.5%`) | `253` (`-64.8%`) |
| **`P5` (`P4 + LoopRotate+LICM+IndVars`)** | **`230` (`-67.0%`)** | **`0` (`-100.0%`)** | **`8` (`-92.7%`)** | **`1` (`-99.1%`)** | **`49`** | **`5` (`-93.2%`)** | **`31`** | **`231` (`-68.5%`)** | **`205` (`-71.4%`)** |
| **`P6_scalar` (Scalar `default<O2>`)** | `235` (`-66.3%`) | `0` (`-100.0%`) | `8` (`-92.7%`) | `1` (`-99.1%`) | `49` | `5` (`-93.2%`) | `33` | `235` (`-67.9%`) | `205` (`-71.4%`) |
| **`P6` (Full SIMD `default<O2>`)** | `356` (`-48.9%`) | `0` (`-100.0%`) | `22` (`-80.0%`) | `1` (`-99.1%`) | `59` | `11` (`-85.1%`) | `53` | `331` (`-54.8%`) | `296` (`-58.8%`) |

#### 5.3 Per-Function Breakdown Across All 6 Rust Benchmark Kernels

| Rust Function | Metric | `P0` | `P1` | `P2` | `P3` | `P4` | `P5` | `P6_scalar` | `P6` (`default<O2>`) | Primary Winning Passes |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **`slice_sum_stride`** | IR Insts / `alloca` / `load` / `store` | `57` / `6` / `14` / `8` | `39` / `0` / `2` / `0` | `34` / `0` / `2` / `0` | `29` / `0` / `1` / `0` | `26` / `0` / `1` / `0` | **`23` / `0` / `1` / `0`** | `24` / `0` / `1` / `0` | `24` / `0` / `1` / `0` | `SROA` (`6 -> 0` `alloca`), `Inliner` (`slice::len`), `LICM` (`scale * 3` hoisted), `IndVarSimplify` |
| **`option_Result_chain`** | IR Insts / `alloca` / `load` / `store` | `36` / `3` / `5` / `6` | `36` / `3` / `5` / `6` | `36` / `3` / `5` / `6` | `21` / `0` / `0` / `0` | **`15` / `0` / `0` / `0`** | **`15` / `0` / `0` / `0`** | `15` / `0` / `0` / `0` | `15` / `0` / `0` / `0` | `Inliner + Post-Inline SROA` (eliminates all 3 `Option` stack slots that escaped into `Option::map` at `P1`), `JumpThreading + SCCP` (`21 -> 15` insts) |
| **`struct_field_packing`** | IR Insts / `alloca` / `load` / `store` | `37` / `3` / `6` / `5` | `30` / `1` / `2` / `4` | `28` / `1` / `2` / `4` | `26` / `0` / `1` / `1` | **`17` / `0` / `0` / `1`** | **`17` / `0` / `0` / `1`** | `16` / `0` / `0` / `1` | `16` / `0` / `0` / `1` | `Inliner + SROA` (`PacketHeader` promoted to registers), `GVN + DSE` (kills redundant `out[0]` store and forwards live store), `BDCE + InstCombine` |
| **`checked_index_bounds`** | IR Insts / `alloca` / `load` / `store` | `83` / `3` / `14` / `5` | `67` / `0` / `8` / `0` | `62` / `0` / `6` / `0` | `62` / `0` / `4` / `0` | **`47` / `0` / `4` / `0`** | **`47` / `0` / `4` / `0`** | `47` / `0` / `4` / `0` | `47` / `0` / `4` / `0` | `SROA` (`3 -> 0` `alloca`), `EarlyCSE` (`8 -> 6` `load`), `CVP + ConstraintElimination + SimplifyCFG` (`62 -> 47` insts by discharging redundant bounds checks) |
| **`iterator_fold_filter`** | IR Insts / `alloca` / `load` / `store` | `38` / `6` / `5` / `9` | `38` / `5` / `4` / `8` | `38` / `5` / `4` / `8` | `37` / `0` / `1` / `0` | `34` / `0` / `1` / `0` | **`18` / `0` / `1` / `0`** | `20` / `0` / `1` / `0` | `141` / `0` / `15` / `0` | `Inliner + Post-Inline SROA` (collapses `Copied<Iter>`, `Map`, `Filter` structs into `0` `alloca`s), `LoopRotate + LICM + IndVars` (`34 -> 18` insts; `P6` bloats to `141` insts via runtime unroll/vectorize) |
| **`enum_state_machine`** | IR Insts / `alloca` / `load` / `store` | `87` / `7` / `24` / `15` | `47` / `0` / `6` / `5` | `46` / `0` / `6` / `2` | `55` / `0` / `0` / `0` | `50` / `0` / `0` / `0` | **`43` / `0` / `0` / `0`** | `43` / `0` / `0` / `0` | `43` / `0` / `0` / `0` | `SROA` (`7 -> 0` `alloca`, `24 -> 6` `load`), `EarlyCSE` (`5 -> 2` `store`), `Inliner + SROA` (`6 -> 0` `load`), `LoopRotate + LICM` (`50 -> 43` insts) |

#### 5.4 Architectural Takeaways from the Ablation Study

1. **Why Two Rounds of `SROA` (Pre-Inline `P1` and Post-Inline `P3`) Are
  Mandatory:** In `P1` (before inlining), `SROA + Mem2Reg` eliminates `77.3%` of
  `alloca`s (`44 -> 10`), completely scalarizing `slice_sum_stride`,
  `checked_index_bounds`, and `enum_state_machine`. However, in
  `option_Result_chain` and `iterator_fold_filter`, `P1` removes almost no
  `alloca`s (`3 -> 3` and `6 -> 5`) because Rust passes `&mut Option<T>` and
  `&mut Filter<Map<...>>` by pointer to `Option::map`, `Option::and_then`, and
  `Iterator::fold`. Until `Inliner` (`P3`) inlines those trait methods, the
  stack allocations appear address-taken (`escapeStackAddr`). Running `SROA` a
  second time immediately after `Inliner` (`P3`) drops `alloca` count from `10`
  to **`0` (`-100.0%`)** and reduces `x86_64` assembly instructions from `642`
  to `343` (`-46.6%` in a single stage).
2. **Why `P4` (`GVN + DSE + BDCE + SCCP + CVP`) and `P5` (`LoopRotate + LICM +
  IndVarSimplify`) Are Complementary:** `P4` reduces `struct_field_packing` by
  `-34.6%` (`26 -> 17` IR insts), `option_Result_chain` by `-28.6%` (`21 -> 15`
  IR insts), and `checked_index_bounds` by `-24.2%` (`62 -> 47` IR insts). `P5`
  reduces `iterator_fold_filter` by `-47.1%` (`34 -> 18` IR insts),
  `enum_state_machine` by `-14.0%` (`50 -> 43` IR insts), and `slice_sum_stride`
  by `-11.5%` (`26 -> 23` IR insts), cutting whole-module `x86_64` assembly from
  `282` to `231` instructions and `aarch64` assembly from `253` to `205`
  instructions.
3. **Why `P5` Is the Pareto-Optimal Initial Target for `AnLLVM`:** Adding SIMD
  auto-vectorization and runtime unrolling (`P6`) increases
  `iterator_fold_filter` from `18` IR instructions to `141` IR instructions
  (`7.8x` larger) due to vector-length checks, alias-check guards, 4-wide SIMD
  loops, and unrolled scalar epilogues, while leaving the other 5 functions
  virtually unchanged.

---

### 6. Deep-Dive Verification Architectures for the Four Hardest Middle-End Components

#### 6.1 `SROA` (`SROA.h`) + `PromoteMemToReg` (`PromoteMemToReg.h`) via `SroaAndMem2RegCertChecker` (Mode B)

Verifying Lengauer-Tarjan dominator trees and `IDFCalculator` inside the Lean 4
kernel would require thousands of lines of graph theory for zero trust-boundary
benefit. Instead, `AnLLVM` fuses `SROA` and `PromoteMemToReg` into a single
**Mode B** certificate checker (`SroaAndMem2RegCertChecker` in Section 3 of
`support/support_anllvm_middle_end_passes_probe.lean`):

- **Certificate (`SroaMem2RegCert`):** Records `slices : List SroaSliceSpec`
  (`(alloc : AllocId, off : Nat, sz : Nat, ssaReg : RegId)`) and per-block entry
  $\phi$ bindings.
- **Lean Kernel Validator (`checkSroaMem2Reg`):**
  1. Checks in $O(|S|^2)$ time that every slice has `sz > 0`, distinct
    `ssaReg`s, and pairwise disjoint byte intervals (`s₁.off + s₁.sz ≤ s₂.off ∨
    s₂.off + s₂.sz ≤ s₁.off`) whenever `s₁.alloc = s₂.alloc`.
  2. Verifies in a single $O(|I|)$ pass that no promoted `alloc` appears in
    `escapeStackAddr`, every `stackStore`/`stackLoad` on a promoted `alloc`
    matches an exact slice `(alloc, off, sz)` in `slices`, and no original
    instruction reads or writes the fresh `ssaReg`s.
  3. Proves the lockstep relational invariant (`checkSroaMem2Reg_sound`):
    $$\forall \mathit{sl} \in \mathit{slices},\quad
    \mathit{st}_T.\text{regs}(\mathit{sl}.\text{ssaReg}) =
    \mathit{st}_S.\text{stack}(\mathit{sl}.\text{alloc},
    \mathit{sl}.\text{off})$$

#### 6.2 `InstCombine` (`InstCombine.h`) + `BDCE` (`DemandedBits.h`) via `InstCombineBdcePassCompiler` (Mode A)

Rather than porting 40,000 lines of procedural C++ visitors, `AnLLVM` implements
`InstCombine + BDCE` as a **Mode A** table-driven verified rewrite engine
(`passInstCombineBdce` in Section 4 of
`support/support_anllvm_middle_end_passes_probe.lean`):

- **Verified Peephole Table:** Each rule is a declarative pattern recognizer
  with an individual Lean 4 soundness lemma (`evalPureBinOp_add_zero`,
  `evalPureBinOp_mul_one`, `evalPureBinOp_bitOr_zero`,
  `evalPureBinOp_bitXor_zero`, `evalStmts_freeze_sub_self_eq`).
- **Integrated Demanded-Bits Absorption (`BDCE`):** Bitwise demanded-bits
  simplifications are mechanized via `Nat.and_or_distrib_right`
  (`nat_or_and_demanded_eq`): when `dst := x | c₁` is followed by `dst := dst &
  c₂` and `(c₁ &&& c₂) = 0`, `BDCE` fuses the pair into `dst := x & c₂`
  (`evalStmts_bdce_bitOr_bitAnd_eq`). If `(c₁ &&& c₂) ≠ 0`, the validator
  rejects the rewrite (`canary_bdce_overlapping_mask_rejected`).

#### 6.3 `NewGVN` (`NewGVN.h`), `MemorySSA` (`MemorySSA.h`), `DSE` (`DeadStoreElimination.h`), and `MemCpyOpt` (`MemCpyOptimizer.h`) via `MemorySsaGvnDseCertChecker` (Mode B)

`AnLLVM` unifies `NewGVN`, `DSE`, and `MemCpyOpt` into a single **Mode B**
`MemorySSA` validator (`MemorySsaGvnDseCertChecker` in Section 5 of
`support/support_anllvm_middle_end_passes_probe.lean`):

- **Three Commuting Heap Algebra Laws (`updateHeap_overwrite`,
  `updateHeap_comm`, `updateHeap_dse_across_noalias`):** Combining commutativity
  and overwrite proves in two lines that writing `v₁` to `(alloc₁, off₁)`, then
  `v₂` to a non-aliasing `(alloc₂, off₂)`, and then `v₃` to `(alloc₁, off₁)` is
  identical to writing only `v₂` and `v₃`.
- **Combined `DSE` + `NewGVN` Store-to-Load Forwarding (`tryMemSsaQuad`):**
  Validates in $O(1)$ per instruction window that a store `S₁` to `(a₁, o₁)` can
  be deleted across a non-aliasing store `S₂` to `(a₂, o₂)` when overwritten by
  `S₃` at `(a₁, o₁)`, and that a subsequent load `L₄` at the same `MemorySSA`
  version `v₃ = v₄` forwards the stored value (`checkMemSsaGvnDse_sound`).

#### 6.4 Loop Optimizations (`LoopRotate`, `LICM`, `IndVarSimplify` / `SCEV`) via `ScevIndVarAndLicmCertChecker` (Mode B)

In `AnLLVM` (`ScevIndVarAndLicmCertChecker` in Section 6 of
`support/support_anllvm_middle_end_passes_probe.lean`):

- **Inductive Proof of `SCEVAddRecExpr` Strength Reduction:** Replacing
  `IndVarMode.mulRecurrence base stride` (`base + curIter * stride`) with
  `IndVarMode.scevAddRec base stride` (`curIv ↦ curIv + stride`) reduces to the
  affine recurrence identity `scev_affine_recurrence_eq` and a 6-line structural
  induction (`runLoopAddRec_eq_runLoopMul`).
- **Speculation-Safe `LICM` Hoisting (`checkScevLicm`):** Verifies
  `L.invOp.isSafeToSpeculate = true` (rejecting trapping `BinOp.udiv` on 0-trip
  loops), operand non-interference, and loop-local scoping
  (`checkScevLicm_sound`, `canary_licm_trapping_div_rejected`,
  `canary_licm_trapping_div_on_zero_trip_unsound`).

---

### 7. Mechanized Lean 4.34.1 Soundness Probes

Both standalone Lean 4.34.1 files in `support/` are verified with:
```bash
lean \
  -j1 -M1024 -DElab.async=false -Ddebug.skipKernelTC=false <file.lean>
```
with exit code `0`, zero warnings, zero `sorryAx`, zero `Lean.ofReduceBool`, and
zero `Lean.trustCompiler`.

#### 7.1 `support/support_clean_slate_llvm_ir_probe.lean` (`1,272` lines, SHA-256 `fcc223ec1d1f32aeac617acbfed3ad1183dfc7ec2bcd2628185eec3eace17ee0`)

| Section / Modification | Theorem / Canary Name | Line Range | Statement Summary | Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- | :--- |
| **Sec 1: Anneal Spine** | `Language.refines_refl`, `Language.refines_trans`, `Language.refines_preserves_defined`, `StepLanguage` | `L135–L289` | Reflexivity, transitivity, and UB-preservation of `Language.Refines`; small-step operational `StepLanguage` over `EventualOut Obs`. | `[]` / `[propext]` |
| **Sec 2: Mod 1 & 3 (`MaskedWord` & `Byte`)** | `sroa_load_widening_across_padding_sound` | `L466–L483` | Widening adjacent `u8` and `u32` field loads across 3 bytes of `Byte.poison` struct padding into a 64-bit `MaskedWord` and extracting fields via shift/slice yields the exact defined fields `f0` and `f1` with `poisonMask = 0` without `freeze`. | `[propext, Quot.sound]` |
| **Sec 2: Mod 1 & 3 (Canary)** | `canary_upstream_whole_word_load_poison_unsound` | `L499–L505` | In upstream LLVM's whole-value scalar poison model, widening a load across any uninitialized padding byte poisons the entire 64-bit result (`none ≠ some f1`). | `[]` |
| **Sec 3: Mod 2 (`Ptr` & `ptrtoaddr`)** | `basicAA_disjoint_allocId_store_load_commute` | `L581–L596` | Storing to any pointer `p` with `p.allocId ≠ q.allocId` never alters a load from `q`, even when `ptrtoaddr p = ptrtoaddr q`. | `[propext, Quot.sound]` |
| **Sec 3: Mod 2 (`Ptr` & `ptrtoaddr`)** | `gvn_ptrtoaddr_equality_substitution_sound` | `L605–L619` | Substituting `ptrtoaddr p_end` for `ptrtoaddr q` under `ptrtoaddr p_end = ptrtoaddr q` preserves all integer computations and `Ptr`-provenance memory accesses. | `[]` |
| **Sec 3: Mod 2 (Canary)** | `canary_upstream_ptrtoint_gvn_collapse_unsound` | `L668–L674` | Mechanizes `support/probe_a_ptrtoint_gvn.ll`: on adjacent allocations `p` and `q`, the unoptimized program returns `some 42` while upstream `GVN + InstCombine + BasicAA` returns `some 0`. | `[]` |
| **Sec 4: Mod 4 ($\phi$-Table Lens)** | `phi_table_block_arg_lens_isomorphism` | `L810–L828` | Proves round-trip isomorphism between `CanonicalPhiNode` and `BlockArgSlot`, commutation of `replaceIncomingBlockWith` with `redirectPredecessor`, and Put-Get / Put-Other lens laws for `setIncomingValueForBlock` and `getIncomingValueForBlock`. | `[propext, Quot.sound]` |
| **Sec 5: Mod 5 (`AllocaLive`/`Dead`)** | `alloca_live_dead_disjoint_coloring_sound` | `L927–L1005` | Proves that stack-slot coloring of disjoint-lifetime `AllocId`s preserves `load`/`store` results and `ColoringSim`, and that `allocaDead` deterministically invalidates all pointers with `p.allocId = a`. | `[propext, Classical.choice, Quot.sound]` |
| **Sec 5: Mod 5 (Canary)** | `canary_escaped_pointer_lifetime_end_coloring_unsound` | `L1028–L1032` | Mechanizes `support/probe_d_lifetime_aa.ll`: when `StackColoring` merges disjoint-lifetime allocas `0` and `1` into slot `0`, runtime address comparison is `true` while upstream `InstCombine`'s unconditional alloca inequality fold yields `false`. | `[]` |
| **Sec 6: Mod 6 (Tree Borrows)** | `inlining_protector_drop_refines_and_not_symmetric` | `L1108–L1119` | Proves that dropping `isProtected` upon function inlining refines `tbTransition` in Anneal's `Partial` preorder for all `(isLocal, kind, perm)`, and is strictly asymmetric on foreign writes to `Frozen`. | `[]` |
| **Sec 7: Mod 7 (`FiniteTripWitness`)** | `witnessed_loop_deletion_sound` | `L1178–L1204` | Proves that deleting a side-effect-free loop with a `FiniteTripWitness` refines `EventualBehaviorOf` in `StepLanguage`. | `[propext]` |
| **Sec 7: Mod 7 (Canary)** | `canary_unwitnessed_loop_deletion_unsound` | `L1211–L1228` | Mechanizes `support/probe_e_mustprogress_loops.ll`: without a `FiniteTripWitness`, `DeletedLoopLang` exhibits `.defined (.terminates .normal 7)` while `LoopLang` exhibits only `.defined .diverges`. | `[propext]` |

#### 7.2 `support/support_anllvm_middle_end_passes_probe.lean` (`2,819` lines, SHA-256 `802f26cf0974d73ce80d89b9ea6263d9c36edc949ad3041d4c45a9b570ba9892`)

| Section | Symbol Name | Kind | Description |
| :--- | :--- | :--- | :--- |
| **Sec 1 (BB-8 Core)** | `Trusted.Partial.refines_refl`, `refines_trans`, `Trusted.ProductiveCompiles.refl`, `trans` | `theorem` | Reflexivity and vertical composition of partial program refinement and `ProductiveCompiles` |
| **Sec 1 (BB-8 Core)** | `BB8.PassCompiler.ofFn`, `CertChecker.toPassCompiler`, `PassCompiler.compId` | `def` | Mode A (`ofFn`), Mode B (`CertChecker`), and sequential composition (`compId`) combinators |
| **Sec 2 (`AnLLVM` IR)** | `PoisonOr`, `BinOp`, `Operand`, `IndVarMode`, `AnStmt`, `AnLoop`, `AnLLVMProg`, `AnState`, `AnLLVMLang` | `inductive` / `def` | Executable operational semantics of `AnLLVM` middle-end IR instantiated as `Trusted.Language AnObs` |
| **Sec 3 (`SROA+Mem2Reg`)** | `checkSroaMem2Reg_sound`, `SroaAndMem2RegCertChecker` | `theorem` / `def` | Mode B soundness theorem and `BB8.CertChecker` bundle for `SROA + PromoteMemToReg`, plus 3 negative canaries (`canary_sroa_overlapping_slices_rejected`, `canary_sroa_escaped_alloc_rejected`, `canary_sroa_overlapping_slices_unsound`) |
| **Sec 4 (`InstCombine+BDCE`)** | `instCombineBdce_productiveCompiles`, `InstCombineBdcePassCompiler` | `theorem` / `def` | Mode A soundness theorem and `BB8.PassCompiler` bundle for `InstCombine + BDCE`, plus 3 negative canaries (`canary_bdce_overlapping_mask_rejected`, `canary_bdce_overlapping_mask_unsound`, `canary_unfrozen_sub_self_state_mismatch`) |
| **Sec 5 (`NewGVN+DSE`)** | `checkMemSsaGvnDse_sound`, `MemorySsaGvnDseCertChecker` | `theorem` / `def` | Mode B soundness theorem and `BB8.CertChecker` bundle for `MemorySSA NewGVN + DSE`, plus 2 negative canaries (`canary_dse_across_aliasing_load_rejected`, `canary_dse_across_aliasing_load_unsound`) |
| **Sec 6 (`SCEV+LICM`)** | `checkScevLicm_sound`, `ScevIndVarAndLicmCertChecker` | `theorem` / `def` | Mode B soundness theorem and `BB8.CertChecker` bundle for `SCEV IndVarSimplify + LICM`, plus 2 negative canaries (`canary_licm_trapping_div_rejected`, `canary_licm_trapping_div_on_zero_trip_unsound`) |
| **Sec 7 (E2E Pipeline)** | `anllvmO2CorePipeline`, `anllvmO2CorePipeline_runs`, `anllvmO2CorePipeline_verified` | `def` / `theorem` | 4-stage `BB8.PassCompiler.compId` pipeline, `rfl` execution proof, and end-to-end `ProductiveCompiles` theorem |


---

### 8. Comparative Matrix of `Vellvm`, `lean-mlir` (`VeIR`), `Alive2`, `Crellvm`, and `seL4/graph-refine`

Basis: **source** + **derived**

| System | Pinned Revision(s) | IR Coverage & Memory Model | `undef` / `poison` / `freeze` Semantics | Verification Mechanism & TCB Footprint |
| :--- | :--- | :--- | :--- | :--- |
| **`vellvm/vellvm`** | `506f1eb0be542611521985719b971fbce8498dc9` / `0d6d403b8d411cacdace3dba0ccfd2b41b811b1e` | Full intra/inter-procedural `VIR` (`Denotation.v:1-939`): SSA `ocfg`, `alloca`, `load`/`store`, `gep inbounds`, calls, intrinsics, and byte-addressed block-offset memory (`MemoryBytes.v`, `Implementations/Memory.v`) | `undef`-free (`EXP_Undef => DVALUE_Poison`, `Denotation.v:122`); fresh `alloca` and struct padding are `poison_memory_byte` (`MemoryBytes.v:113, 632`); integer loads taint the whole word on any poison byte (`MemoryBytes.v:726-733`), while `DTYPE_B sz` preserves byte/bit granularity; `freeze` uses nondeterministic `DrawE` (`Freeze.v:32-111`) | Coq/Rocq interaction trees (`itree`) parameterized by effects `L0`..`L4`; foundational relational proofs in Coq kernel; no automated binary translation validator for `llc` |
| **`opencompl/lean-mlir`** (`VeIR`) | `b8c4a77131919c8e18cf8bc7fdde40ef3cf87924` / `b8c4a771319a044854a4bbb49b8821381ef86ff8` | Pure single-basic-block SSA bitvector expression DAG (`LeanMLIR/Dialects/LLVM/Basic.lean:28-553`): 31 integer/bitwise/cast ops + `select`/`icmp`/`freeze`; **no memory, pointers, `alloca`, `gep`, or CFG branches** | `LLVM.IntW w := PoisonOr (BitVec w)` (`Semantics.lean:28`); `IsRefinedBy` (`Poison.lean:105-108`); `LLVM.freeze` (`Semantics.lean:636-640`) deterministically collapses `.poison` to `.value 0` (**unsound for non-zero hardware registers**); no `undef` | Lean 4 `bv_decide` bit-blasting on single-op theorems (`Semantics.lean`), but `PeepholeRewrite` (`Rewrite.lean:23`) requires `lhs.denote = rhs.denote`, so `PeepholeRefine.lean:33` injects `axiom refinement_correctness {p: Prop} : p` (`False`) |
| **`AliveToolkit/alive2`** | `release 21.0` (`adacbd5180ccf95075e9867c4f0c259f59c9fef2`) | Rich intra-procedural LLVM IR (`ir/instr.cpp`, `ir/memory.cpp`, `ir/attrs.cpp`): `load`/`store`, `alloca`, `malloc`/`free`, `gep inbounds`/`nusw`/`nuw`, `memcpy`, `!noundef`, `!range`, `!nonnull`, `!align`, `noalias`, `readonly`, `writable`, `dereferenceable` | Both `undef` (symbolic `undef_vars` quantified in refinement) and per-bit `poison` (`Byte` in `ir/memory.h`); `State::freeze` (`ir/instr.cpp:3203-3207`) resets `undef_vars` and substitutes fresh bitvector vars for poison bits | Unverified C++20 symbolic executor (`util/symexec.cpp`) emitting Z3 SMT queries; loops unrolled to a fixed bound (`-src-unroll` / `-tgt-unroll`); **not proof-producing** |
| **`snu-sf/crellvm`** | `668249b88756233f96b3ef21f12993501a348afc` | Vellvm-derived Coq IR for LLVM 3.7 (`coq/def/Validator.v`, `coq/proof/Adequacy.v`): SSA CFG, `alloca`, `load`/`store`, `gep`, and CompCert-style block memory | Legacy LLVM 3.7 `undef`/`poison` model; `Behavior.beh_error` acts as universal bottom (`Behavior.v:39-48`, `beh_refine`) | Instrumented C++ LLVM passes emit JSON hint certificates checked by Coq's `valid_module` (`Adequacy.v:87`); covers 4 passes (`GVN`, `SROA`, `LICM`, `InstCombine`) and depends on 11 admitted lemmas (`Adequacy.v:15`) |
| **`seL4/graph-refine`** | `94c93d18830d680fc6732d21fb16ca58ebca9dc5` / `33d94bbdd6448ada368d4d925935e8cfdf7d93b4` | Target-independent `GraphLang` (`syntax.py`, `problem.py`, `check.py`, `stack_logic.py`): typed nodes (`Basic`, `Cond`, `Call`, `Ret`, `Err`) over explicit `Mem`, `Dom`, `HTD`, and `PMS` state tokens for C, LLVM IR (`graph-to-graph/`), and ARM/RISC-V binaries | Machine-level bitvectors (`BitVec 32`/`64`) and flat `Mem : Addr → Word` arrays; source safety conditions exported as `Err` nodes (`check_no_err`) | Decomposes CFGs at Tarjan SCC loop-head cut-points (`problem.py:166-275`, `check.py:154-355`) and scalarizes stack slots (`stack_logic.py:356-466`) into loop-free `QF_ABV` VCs exported to HOL4/Isabelle (`Loop.thy`) |

### 9. Two Soundness Defects in `opencompl/lean-mlir` and Anneal's Zero-Axiom `DirectionalRewriteRefine` Repair

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

### 10. `Vellvm` `DTYPE_B` (`AnByteWord` `[8 x i8]`) + Per-Byte `freeze` vs. `DTYPE_I` Whole-Word Poison Taint

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

### 11. Formal 4-State Tree Borrows Machine and Simulation of LLVM `noalias`, `readonly`, and `writable`

Basis: **source** + **execution** + **derived**

We audited Miri's Tree Borrows implementation in `rust-lang/rust`
(`src/tools/miri/src/borrow_tracker/tree_borrows/{mod,perms,tree,tree_visitor,diagnostics,foreign_access_skipping}.rs`
and `src/tools/miri/src/borrow_tracker/mod.rs`) alongside `rustc`'s MIR retagger
(`compiler/rustc_codegen_ssa/src/mir/retag.rs:190-263`), layout analysis
(`compiler/rustc_middle/src/ty/layout.rs:1136-1172`), and ABI attribute emission
(`compiler/rustc_ty_utils/src/abi.rs:286-411`).

#### 11.1 Exact 4-State Permission Machine (`TBPerm`, `tbStepPerm`, `tbStep`)

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

#### 11.2 Simulation of LLVM `noalias`, `readonly`, and `writable` (`treeBorrows_implies_llvm_noalias_readonly_sound`)

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

### 12. `seL4/graph-refine` `GraphLang` Binary Translation Validation: Stack-Slot Scalarization, Loop Backedges, and $k:1$ Unrolled Loops

Basis: **source** + **execution** + **derived**

#### 12.1 Static Stack-Slot Scalarization (`scalarizeStackSlice_sound`, Modeling `stack_logic.py`)

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

#### 12.2 Loop Backedge Alignment and $k:1$ `UnrollHint`-Guided Unrolled Loop Validation

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

### 13. Complete Lean 4.34.1 Theorem Inventories

Basis: **execution**

#### 13.1 `support/track6_llvm_lowering_and_binary_tv_probe.lean` (1,215 lines)

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

#### 13.2 `support/round2_track5_probe.lean` (1,532 lines)

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
- **SIMD auto-vectorization and runtime loop unrolling (`P6` vs. `P5` scalar core, deferred to Phase 2):** As demonstrated in the `P0..P6` ablation study (`support/ablation_results.json`), enabling `LoopVectorizePass`, `SLPVectorizerPass`, and runtime `LoopUnrollPass` in `P6` expands `iterator_fold_filter` from `18` to `141` IR instructions (`7.8x`) while leaving scalar kernels unchanged; `AnLLVM` Phase 1 targets the 12-pass scalar core `P5` (`-67.0%` IR instructions, `-100.0%` `alloca`s, `-68.5%` `x86_64` assembly, `-71.4%` `aarch64` assembly).

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
3. **`AliveToolkit/alive2`** (`release 21.0`, `adacbd5180ccf95075e9867c4f0c259f59c9fef2`):
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
7. **`joshlf/anneal`** (`24367bd1a8c784f2578535954f9915e24894a56f`):
   - `PRINCIPLES.md`, `trusted/audit/TrustedBoundary.lean`, and the standalone refinement and pass-verification formalizations preserved in `support/`.
8. **`llvm/llvm-project`** (`3623fe661ae35c6c80ac221f14d85be76aa870f1`, release `llvmorg-21.1.8`, `/usr/include/llvm-21/llvm/`) and **`rust-lang/rust`** (`49d734536222bf28bb6d07d885b3a81d145981da`):
   - `IR/Instruction.def:1-255`, `IR/Operator.h:65-590`, `IR/GEPNoWrapFlags.h:26-104`, `IR/Instructions.h:64-5171`, `IR/IntrinsicInst.h:155-1746`, `Analysis/ValueTracking.h:61-825`, `Analysis/MemorySSA.h:140-1305`, `Analysis/AliasAnalysis.h:78-716`, `Analysis/ScalarEvolution.h:127-956`.
   - `compiler/rustc_codegen_ssa/src/traits/builder.rs:353-373`, `compiler/rustc_codegen_ssa/src/mir/{place,statement,block}.rs`, `compiler/rustc_codegen_llvm/src/{abi,builder,attributes}.rs`.

### Preserved Lean 4.34.1 support artifacts

- `support/track6_llvm_lowering_and_binary_tv_probe.lean` (SHA-256
  `f22d763bc5d8fc5832e164f12e0e8937880dc488313f6bad077222ee623c1027`, 1,215
  lines).
- `support/round2_track5_probe.lean` (SHA-256
  `0740195c02f1249a56635bed1ec1bcd7909dc127c3cae3ed111889dc44602a50`, 1,532
  lines).
- `support/support_clean_slate_llvm_ir_probe.lean` (SHA-256 `fcc223ec1d1f32aeac617acbfed3ad1183dfc7ec2bcd2628185eec3eace17ee0`, 1,272 lines, observed `2026-11-01`).
- `support/support_anllvm_middle_end_passes_probe.lean` (SHA-256 `802f26cf0974d73ce80d89b9ea6263d9c36edc949ad3041d4c45a9b570ba9892`, 2,819 lines, observed `2026-11-01`).
- Empirical LLVM 21.1.8 `opt` and `llc` semantic probes (`support/probe_a_ptrtoint_gvn.ll`, `support/probe_a_ptrtoint_gvn.opt.ll`, `support/probe_b_sroa_padding.ll`, `support/probe_b_sroa_padding.opt.ll`, `support/probe_c_unswitch_freeze.ll`, `support/probe_c_unswitch_freeze.opt.ll`, `support/probe_d_lifetime_aa.ll`, `support/probe_d_lifetime_aa.opt.ll`, `support/probe_d_lifetime_aa.s`, `support/probe_e_mustprogress_loops.ll`, `support/probe_e_mustprogress_loops.opt.ll`, observed `2026-11-01`).
- Cumulative `P0..P6` middle-end pass ablation benchmark (`support/bench_suite.rs`, `support/ablation_benchmark.py`, `support/ablation_results.json`, observed `2026-11-01`).

## Revalidation

To re-verify both standalone Lean 4.34.1 mechanizations and their `#guard_msgs
in #print axioms` checks from the package directory:

```bash
lean -j1 -M1024 -DElab.async=false -Ddebug.skipKernelTC=false support/support_clean_slate_llvm_ir_probe.lean
lean -j1 -M1024 -DElab.async=false -Ddebug.skipKernelTC=false support/support_anllvm_middle_end_passes_probe.lean
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
