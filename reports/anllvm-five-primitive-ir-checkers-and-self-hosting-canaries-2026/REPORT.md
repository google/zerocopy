# AnLLVM Five-Primitive IR, Certificate Checkers, and Self-Hosting Canaries

## Summary

Anneal's verified `MIR -> AnLLVM -> RV64GC` (and multi-ISA `AArch64` / `x86-64`)
optimizing compiler and its self-hosted `$K_{\text{anc}}$` Rust implementation
(`anc`) converge on **five orthogonal IR and semantic primitives**, **five
certificate-checker families (`CC-1`–`CC-5`)**, **five self-hosting building
blocks (`BB-ANC-1`–`BB-ANC-5`)**, and a **root theorem decoupling** between
source-safety verification (`StrictUnitTheorem` / `CrateTheorem`) and
whole-crate compiler correctness (`VerifiedCompilationTheorem`). Together, these
components compile and validate all 26 optimization and code-generation passes
while adding **zero intermediate-IR lines** to `trusted/lean/Trusted/` beyond
the universal refinement kernel (`Trusted/Refinement.lean`,
`Trusted/StepResult.lean`) and target semantics (`Trusted/MirSemantics.lean`,
`Trusted/Rv64Semantics.lean`).

This report documents the converged semantic design and provides a standalone,
`prelude`-only Lean 4.34.1 mechanization
([`anllvm_five_primitive_and_canaries_probe.lean`](support/anllvm_five_primitive_and_canaries_probe.lean))
that proves all foundational invariants, compositional pass-checker bridges, and
21 adversarial negative canaries (`Canaries 1–11` and held-out stress suites
`HO-1`–`HO-10`) with **zero `sorryAx`**, **zero `Classical.choice`**, and **zero
`Lean.ofReduceBool`**
([`lean_verification_output.txt`](support/lean_verification_output.txt)):

1. **Five-Primitive Semantic Core & `CC-1`–`CC-5` Pass Coverage:**
   - **Carry/Borrow/Shift Poison Monotonicity (`MaskedWord w`, `VecWord N W`):**
     Naive bitwise poison propagation (`poisonMask := am ||| bm`) on `add`,
     `sub`, `udiv`, and `uaddo` violates `freeze` monotonicity (`a.freeze ⊑ a ⇏
     op(a.freeze, b) ⊑ op(a, b)`, `Canary 1`), and unguarded shifts by `sh >= w`
     shift `poisonMask` out to `0#w`. Tainting the full output word
     (`BitVec.allOnes w`) whenever any operand bit is poisoned on cross-bit
     carry/borrow/division operations or `sh >= w`—while keeping exact bit/byte
     masks on `evalAnd`, `evalOr`, `evalXor`, `pack8BytesLE`, and
     `extractByteLE` (`Canary 5` / `DC-5a`) and strict lane isolation on
     `VecWord N W` (`vecWord_map2_lane_isolated`)—restores `checkRefines`
     monotonicity (`canary1_carry_borrow_shift_monotonicity_restored`).
   - **Two-Tier `inttoptr` & Dynamic `TreeBorrows` (`DualViewMemory`):**
     Single-tier `inttoptr` resolution (`0 <= off <= byteSize`) misroutes a
     one-past-the-end pointer `base1 + size1` (`0x1008`) into the predecessor
     allocation `b1` (`[0x1000, 0x1008)`) instead of the adjacent allocation
     `b2` (`[0x1008, 0x1010)`, `Canary 2`). Two-tier `evalIntToPtrWithBoundary`
     checks Priority 1 strict interior (`0 <= off < byteSize`) before Priority 2
     boundary (`off == byteSize`), while `loadWord64` and `storeWord64` enforce
     `checkNoDupBlockIds`, `off % 8 == 0`, strict interior bounds `off + 8 <=
     byteSize`, and dynamic `stepTreeBorrows` transitions (`Reserved -> Active`
     on writes, disabling sibling `Frozen` tags in diamond CFGs, `HO-1`).
   - **Five Certificate-Checker Families (`CC-1`–`CC-5`):** Cover all 26 passes
     across `MIR`, `AnLLVM`, `AnMachine`, and `PostRaMachine`, catching
     speculative `udiv`/`load` hoisting (`Canary 2a/2b/2c`), un-unioned
     `DestinationPropagation` `StorageLive` intervals (`rust-lang/rust#146383`,
     `Canary 1a/1b`), `SROA` union-padding clobbers and `StackColoring`
     address-observed slot merges (`Canary 5a/5b/5c`), un-frozen
     `SimpleLoopUnswitch` (`LLVM #52865`, `Canary 4`), non-terminating
     `LoopDeletion` (`rust-lang/rust#28728`, `Canary 6`), `IndVarSimplify`
     `zext`/`sext` wrap and `LoopVectorize` distance-1 RAW hazards (`LLVM
     #64598`, `HO-2a/2b`), `TailCallElim` live-local/unwind corruption (`LLVM
     #58241`, `HO-3a/3b`), post-RA reused-input and hardware-flag clobbers
     (`Canary 7/7b`, `HO-4`), 256-instruction WHNF reduction scaling (`HO-5`),
     and cascading 2-round `BranchRelaxation` displacement overflow (`LLVM
     #61392`, `HO-6`).
2. **Five `$K_{\text{anc}}$` Self-Hosting Building Blocks (`BB-ANC-1`–`5`):**
   - `BB-ANC-1` (`ofRustTwoStepImp` + `ofRustTwoStepNonVacuous`) bridges
     fuel-bounded `$K_{\text{anc}}$` Rust checkers to `PassCertChecker` via
     one-way implication `rustCheck s t cert = true → P.check s t cert = true`
     paired with a positive acceptance witness (`Canary 8a/8b`, `DC-15`).
   - `BB-ANC-2` (`FreezeValueWitness` + `evalIntraWithFreezeGuard`) blocks
     safe-Rust `Cell`/`RefCell` (`UnsafeCell`) and stateful `Deref` TOCTOU
     spoofing between `P.check` and code emission (`Canary 9a` / `HO-7`).
   - `BB-ANC-3` (`withFallbackCompiler` + `withSelfCertifyingFallback` +
     3-stride `runPostRaCheckBlockV2Fast`) reuses `P.check` on
     `trivialSpillFallbackBlock` with zero extra semantic soundness theorems and
     validates 768-instruction spill blocks in 256 recursion frames (`Canary
     9b`, `HO-8`).
   - `BB-ANC-4` (`checkedAddU64` + `checkDisjointRangesU64Strict` +
     `nat_add_mod_no_wrap_zero_axioms`) defeats 64-bit modular wrapping on both
     lower and upper intervals (`[0, 8)` vs. `[2^64 - 8, 2^64 + 8)`, `Canary
     10`, `HO-9b`) and proves `Nat` disjointness with **zero axioms** (`#print
     axioms` = `does not depend on any axioms`).
   - `BB-ANC-5` (`PassExecMode.selectMode` + `checkBootstrapFixedPointWithUnit`)
     enforces `.option5B_machineBytesO` (`.directElfObject`),
     `u.waived.isEmpty`, `stage1VerifiedBytes == stage1ActualBytes`, and
     `stage1ActualBytes == stage2ActualBytes` to defeat both external `.s`
     assembler attacks and Thompson-style self-reproducing Stage-1 quines
     (`Canary 11` / `HO-10`).
3. **Decoupling `VerifiedCompilationTheorem` from `StrictUnitTheorem`:**
   - `StrictUnitTheorem` (and `CrateTheorem` under `defaultTrustPolicy`)
     enforces source-level deductive verification (`MirLang.WellFormedOn` +
     functional `specs`, `u.waived = []`).
   - `VerifiedCompilationTheorem` uses `compilationTrustPolicy` (`isAllowed
     (.rustcLowering _ _) := False`, `isAllowed (.userAxiom _ _) := False`,
     `isAllowed (.fnVerified _ _) := True`), requiring a constructive `Compiles
     MirLang Rv64Lang mirToRv64Codec` proof (`Or.inr`) and
     `EmittedArtifact.holds` for every function while permitting `.fnVerified`
     waivers (`Or.inl`) on unannotated upstream crates (`core`, `alloc`, `std`,
     `rustc`) without cross-obligation explosion
     (`verifiedCompilationTheorem_decouples_compiler_from_source_specs`).

## Applicability

The findings and mechanized artifacts in this report apply to the following
pinned repository revisions and toolchain environments:

| Subject | Repository / Path | Pinned Revision / Version | Role in This Report |
| :--- | :--- | :--- | :--- |
| Lean 4 Kernel & Toolchain | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel evaluator and axiom auditor (`#print axioms`) for all `prelude` proofs |
| Anneal Universal Refinement Core | `joshlf/anneal` | `beb778bb135474a67dc017c185d2753a60693d8c` | `Trusted/Refinement.lean`, `Trusted/StepResult.lean`, and `TrustedBoundary.lean` |
| Anneal MIR & RV64GC Compiler Tree | `joshlf/anneal` | `7677632ab267e6d7075fc9ddca7280ddf0296f87` | `Trusted/MirSemantics.lean`, `Trusted/Rv64Semantics.lean`, and `theory/Anneal/Compiler/*` |
| Rust Reference | `rust-lang/reference` | `82da570bafd9efed421bdbae0f8603ede8dd308b` | Undefined behavior, unsafety, and `StorageLive` / `Freeze` semantics |
| Rust Compiler | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Upstream `Runtime(PostCleanup)` MIR pass semantics and regression issues (`#146383`, `#28728`) |
| LLVM Project | `llvm/llvm-project` | `3623fe661ae35c6c80ac221f14d85be76aa870f1` (`llvmorg-21.1.8`) | Upstream IR/backend pass semantics and regression issues (`#52865`, `#58241`, `#61392`, `#64598`) |
| Sail RISC-V Lean Model | `opencompl/sail-riscv-lean` | `51c635c460125ac87955d061fcd902ce03b8011f` | Reference `RV64GC` instruction semantics |
| Mechanized Proof Probe | [`support/anllvm_five_primitive_and_canaries_probe.lean`](support/anllvm_five_primitive_and_canaries_probe.lean) | SHA-256 `16ee7f1ec68f3119eda7a5b8e7b2c3d67c55c7058a6253419db36f2e30f14177` | Self-contained 2,951-line `prelude`-only Lean 4.34.1 mechanization |
| Kernel Verification Log | [`support/lean_verification_output.txt`](support/lean_verification_output.txt) | SHA-256 `f278eacfa9363b1b900010b7057bb2acde078440fdd3dbc5784e681e834e3bcc` | Recorded `#print axioms` output from `lean` `v4.34.1` |

## Findings

### 1. The Converged Five-Primitive IR and Semantic Architecture

Anneal's `MIR -> AnLLVM -> AnMachine -> PostRaMachine -> IsaLang` pipeline
avoids adding any intermediate-IR definitions to `trusted/lean/Trusted/`.
Instead, all intermediate IRs and certificate checkers are constructed in
`theory/` from five orthogonal primitives:

| Layer | Primitive | Core Types & Combinators | Architectural Guarantee |
| :--- | :--- | :--- | :--- |
| **Layer 0** | `CompilerSpine` | `ArchEvent`, `ArchReturn`, `EventualOut ArchEvent ArchReturn` | Shared observable spine across all 5 languages; intermediate IRs cancel by `Compiles.comp` transitivity (`0` new lines in `trusted/`). |
| **Layer 1** | `MaskedWord w` + `VecWord N W` | `MaskedWord w := ⟨bits, poisonMask⟩`, `freeze`, `checkRefinesOnMask`, `VecWord N W` | Deterministic value + poison carrier unifying scalars (`w = 64`), bytes (`w = 8`), and lane-isolated SIMD vectors (`<N x iW>`) with zero `Classical.choice`. |
| **Layer 2** | `DualViewMemory` + Two-Tier `inttoptr` + `stepTreeBorrows` | `AllocId (.ext \| .loc)`, `MemBlock`, `MemState`, `evalIntToPtrWithBoundary`, `stepTreeBorrows` | Separates unexposed local stack slots from exposed allocations; enforces two-tier `inttoptr` resolution and dynamic `TreeBorrows` state transitions. |
| **Layer 3** | `FeatureProfile` + `mkTargetCodec` + `PassCertChecker` | `OptField`, `ExtVal`, `ProfiledState p`, `mkTargetCodec`, `mkLayerCodec`, `PassCertChecker.seq2` | Collapses disabled features (`.scalarCore`) to `Unit` by `rfl`; fails closed on `abiStackValid = false`; composes certificate checkers via `ProductiveCompilesPartial.comp`. |
| **Layer 4** | `CC-1`–`CC-5` + `TargetIsaBackend mode` | `evalDestPropFull`, `checkAliasDisjoint`, `checkUnswitchCondSafe`, `stepPostRaCheckV2`, `checkBranchRelaxationLayout` | Compresses all 26+ optimization and backend passes into 5 kernel-reducible certificate-checker families parameterized by `TargetIsaBackend`. |

#### 1.1 `MaskedWord w` Poison Monotonicity (`Canary 1`)

In `MaskedWord w`, `x : MaskedWord w` pairs data bits `x.bits : BitVec w` with a
per-bit poison mask `x.poisonMask : BitVec w` (`1` = poison / `Byte.uninit`, `0`
= clean). `MaskedWord.freeze x` clears all poisoned bits to deterministic `0`
(`⟨x.bits &&& ~~~x.poisonMask, 0#w⟩`), and directional refinement
`MaskedWord.checkRefines tgt src` requires every clean bit in `src`
(`~~~src.poisonMask`) to be clean in `tgt` and equal to `src.bits`.

A sound poison semantics must make every ALU operation monotone with respect to
`checkRefines` and `freeze`: because `a.freeze ⊑ a`, any operation `op` must
satisfy `op(a.freeze, b) ⊑ op(a, b)`. A naive bitwise poison propagation rule
(`NaiveBaseline`, which sets `poisonMask := am ||| bm` on `add`, `sub`, `udiv`,
and `uaddo`, and shifts `am <<< sh` without a width guard) violates this law in
five ways mechanized in `canary1_carry_borrow_shift_monotonicity_restored`:

1. **Addition Carry Bleed (`evalAdd`):** Let `a1 = ⟨1#64, 1#64⟩` (bit 0 is
   poisoned, holding underlying garbage bit `1`) and `b1 = ⟨1#64, 0#64⟩` (clean
   `1`). Freezing `a1` clears bit 0 to `0` (`a1.freeze = ⟨0#64, 0#64⟩`), so
   `NaiveBaseline.evalAdd a1.freeze b1 = ⟨1#64, 0#64⟩` (bit 1 is `0`). However,
   `NaiveBaseline.evalAdd a1 b1` computes `1 + 1 = 2` with `poisonMask := 1 |||
   0 = 1#64` (`⟨2#64, 1#64⟩`), marking bit 1 (`1`) as **clean** (`poisonMask`
   bit 1 is `0`). Because bit 1 is `0` in `evalAdd a1.freeze b1` and clean `1`
   in `evalAdd a1 b1`, `checkRefines` evaluates to `false`.
2. **Subtraction Borrow Bleed (`evalSub`):** For `aSub = ⟨0#64, 0#64⟩` and
   `bSub = ⟨1#64, 1#64⟩` (`bSub.freeze = ⟨0#64, 0#64⟩`), `NaiveBaseline.evalSub
   aSub bSub.freeze = ⟨0#64, 0#64⟩`, whereas `NaiveBaseline.evalSub aSub bSub =
   ⟨0xFFFFFFFFFFFFFFFF#64, 1#64⟩`, leaving bits 1..63 clean `1` and falsifying
   `checkRefines` (`= false`).
3. **Division Quotient Shift (`evalUdiv`):** For `aDiv = ⟨6#64, 2#64⟩` (bit 1
   poisoned) and `bDiv = ⟨3#64, 0#64⟩`, `aDiv.freeze = ⟨4#64, 0#64⟩` gives
   quotient `4 / 3 = 1` (bit 1 is `0`), whereas `6 / 3 = 2` with `poisonMask =
   2#64` leaves bit 0 clean `0` vs. `1`.
4. **Overflow Addition (`evalUaddo64`):** Adding `aOvf =
   ⟨0xFFFFFFFFFFFFFFFF#64, 1#64⟩` and `bOvf = ⟨1#64, 0#64⟩` under bitwise
   `pMask := am ||| bm` wraps `aOvf + 1` to `0#64` with `pMask = 1#64` while
   `aOvf.freeze + 1 = 0xFFFFFFFFFFFFFFFF#64`, falsifying `checkRefines` on the
   64-bit sum (`= false`).
5. **Shift-by-Width Poison Laundering (`evalShl` / `evalLshr`):** Shifting `a1 =
   ⟨1#64, 1#64⟩` left by `sh = 64` without a width guard shifts `am <<< 64` to
   `0#64`, laundering a poisoned input into a clean `0#64`.

**The Repair:** In `MaskedWord`:
- Cross-bit carry/borrow/quotient operations (`evalAdd`, `evalSub`, `evalUdiv`,
  `evalSdiv64`, `evalUaddo64`, `evalUadde64`) taint the **entire output word**
  (`BitVec.allOnes w`) whenever any input bit is poisoned (`am != 0#w || bm !=
  0#w`) or `nuw`/`nsw` overflows, and `evalShl`/`evalLshr` return
  `BitVec.allOnes w` whenever `sh >= w`.
- Bitwise operations (`evalAnd`, `evalOr`, `evalXor`) and byte packing/slicing
  (`pack8BytesLE`, `extractByteLE`) preserve **exact per-bit/per-byte masks**
  (with `evalAnd` clearing poison on known-`0` bits `~~~am &&& ~~~ab` and
  `evalOr` clearing poison on known-`1` bits `~~~am &&& ab`), which is essential
  for `SROA` and `Mem2Reg` on structs with uninitialized padding bytes (`Canary
  5`).
- SIMD vector operations use `VecWord N W` (`VecWord.map2`), isolating carry and
  `nuw` poison propagation strictly within each `W`-bit lane
  (`vecWord_map2_lane_isolated`, proved with zero axioms).
- Finally, `checkRefinesOnMask` uses a syntactic-equality fast path (`cond
  ((tBits.toNat == sBits.toNat) && (tMask.toNat == sMask.toNat)) true ...`) and
  `MaskedWord.decEq_refl` to prove `checkRefines_refl` constructively without
  `Classical.choice`.

#### 1.2 Two-Tier `inttoptr` Lookup in `DualViewMemory` (`Canary 2`)

In `DualViewMemory`, logical allocations are partitioned into unexposed local
stack slots (`AllocId.loc id`, `isExposed = false` until `ptrtoint` is executed)
and exposed allocations (`isExposed = true`). Theorem
`evalIntToPtr_never_returns_unexposed` proves with **zero axioms** that
`evalIntToPtr` never synthesizes a pointer to an unexposed allocation, allowing
`Mem2Reg`, `SROA`, and `BasicAA` to optimize local stack slots across arbitrary
integer-to-pointer casts.

When resolving `inttoptr(addr)` across exposed allocations, a naive single-tier
boundary check (`findBlockSingleTierBuggy`: `baseAddr <= addr && addr - baseAddr
<= byteSize`) suffers from an adjacent-allocation provenance bug (`Canary 2` /
`Canary 3b`):
- Suppose exposed allocation `b1` (`AllocId.ext 1`) occupies `[0x1000, 0x1008)`
  (`baseAddr = 0x1000`, `byteSize = 8`) and adjacent exposed allocation `b2`
  (`AllocId.ext 2`) occupies `[0x1008, 0x1010)` (`baseAddr = 0x1008`, `byteSize
  = 8`).
- The address `0x1008` is simultaneously the one-past-the-end boundary of `b1`
  (`offset = 8 == b1.byteSize`) and the strict interior start of `b2` (`offset =
  0 < b2.byteSize`).
- Because `b1` precedes `b2` in `mem.blocks`, `findBlockSingleTierBuggy` matches
  `b1` at offset `8` (`some (.ext 1)`). A subsequent load or store to `0x1008`
  intended for `b2[0]` then fails with out-of-bounds UB on `b1` (`off + 8 = 16 >
  8`)!

**The Repair (`evalIntToPtrWithBoundary`):** `MemState.evalIntToPtrWithBoundary`
implements a two-tier lookup proved in
`canary2_adjacent_twin_allocations_two_tier_inttoptr`:
1. **Priority 1 (`findInteriorExposedBlock`):** Scans all blocks for a live,
   exposed allocation whose **strict interior** `[baseAddr, baseAddr +
   byteSize)` contains `addr` (`0 <= off < byteSize`). On `memTwin`, `0x1008`
   skips `b1` (`8 < 8` is false) and resolves to `b2` at offset `0` (`some
   ⟨.ext 2, 0, 0#64, none⟩`).
2. **Priority 2 (`findBoundaryExposedBlock`):** Only if **no** live exposed
   block contains `addr` in its strict interior, falls back to matching `addr ==
   baseAddr + byteSize`. For an isolated block `bIso` at `[0x2000, 0x2008)`,
   `0x2008` resolves to `some ⟨.ext 3, 0, 8#64, none⟩` (preserving
   `slice::split_at(len)` empty tail-slice pointer round-trips), while
   `loadWord64` and `storeWord64` enforce `off + 8 <= byteSize` and reject
   dereferencing offset `8` (`memTwin.loadWord64 ⟨.ext 3, 0, 8#64, none⟩ =
   none`).

#### 1.3 How `CC-1`–`CC-5` Cover All 26 Passes and Catch Concrete Soundness Bugs

All 26 `MIR -> AnLLVM -> RV64GC` passes (plus `AArch64` and `x86-64` backend
instantiations) are validated by five certificate-checker families:

| Checker Family | Covered Passes (26 Total) | Key Soundness Guards & Mechanized Canaries |
| :--- | :--- | :--- |
| **`CC-1` (`ForwardDataflowChecker`)** | `MirConstProp`, `MirCopyProp`, `MirSimplifyCfg`, `AnLlvmInstCombine`, `EarlyCSE`, `GVN`, `SCCP`, `AnLlvmSimplifyCfg`, `AnLlvmJumpThreading`, `AnLlvmFreezeInsertion` | `isSpeculativelySafe` forbids hoisting partial/trapping operations (`udiv`, `sdiv`, unvalidated `load`) across branch guards (`Canary 2a/2b/2c`: `canary2abc_speculative_udiv_and_load_rejected`). |
| **`CC-2` (`BackwardLivenessChecker`)** | `MirDestProp`, `MirDeadStorageElim`, `MirSroa`, `AnLlvmSroa`, `AnLlvmMem2Reg`, `PrologEpilogInserter` | 2-parameter `evalDestPropFull hoistOuterLive deleteInnerLive` catches both unhoisted outer `StorageLive` (`rust-lang/rust#146383`, `Canary 1a`) and undeleted inner `StorageLive` clobbers (`Canary 1b`, `canary1ab_destProp_two_parameter_union`); `pack8BytesLE` + `checkRefines` catches `SROA` dropping or zeroing active union bytes while admitting `byteUninit -> 0x00` struct padding (`Canary 5a/5b`, `DC-5a`); `checkStackColoringMergeSafe` blocks merging slots with `addrObserved = true` (`Canary 5c`, `canary5abc_sroa_padding_and_stackColoring`). |
| **`CC-3` (`MemorySplitChecker`)** | `MirReborrowCollapse`, `BasicAA`, `ScopedNoAliasAA`, `AnLlvmDse`, `AnLlvmMemCpyOpt`, `ADCE` | `checkAliasDisjoint` enforces `checkNoDupBlockIds`, non-self `.unexposedVsRaw` (`p₁.bid != p₂.bid`), 8-byte aligned `.constOffsetDisj`, and registered `.noAliasScopeDisj` with at least one `.active` borrow (`Canary 3`: `canary3_alias_disjoint_blocks_all_four_exploits`); dynamic `stepTreeBorrows` transitions `Reserved -> Active` on writes and disables sibling `Frozen` tags in diamond CFGs (`HO-1`: `ho1_dynamic_treeBorrows_diamond_write_disables_sibling_frozen`). |
| **`CC-4` (`CfgEdgeCutChecker`)** | `LoopRotate`, `LICM`, `SimpleLoopUnswitch`, `LoopDeletion`, `IndVarSimplify`, `LoopUnroll`, `LoopVectorize`, `SLPVectorizer`, `TailCallElim` | `checkUnswitchCondSafe` requires `poisonMask == 0#1` via `freeze` (`LLVM #52865`, `Canary 4`); `checkLoopDeletionSafe` requires `mustprogress \|\| hasFiniteTripProof` (`rust-lang/rust#28728`, `Canary 6`); `checkIndVarWiden` requires `nuw` for `zext` and `nsw` for `sext` (`LLVM #64598`, `HO-2a`); `checkLoopVectorizeSafe` rejects distance-1 RAW hazards (`HO-2b`); `checkTailCallElim` and `mkTargetCodec` reject live `.loc` allocas and unwind callee-saved corruption (`LLVM #58241`, `HO-3a/3b`). |
| **`CC-5` (`PostRaSimChecker`)** | `GlobalISel`, `PeepholeOptimizer`, `MachineCombiner`, `RegAlloc` (`RAGreedy` + `VirtRegRewriter` + `MachineScheduler`), `StackColoring`, `BranchRelaxation`, `AsmPrinter` / `ElfObjectEmitter` | `stepPostRaCheckV2` (`FlagEffectV2` with `.readsFlag`, checking `src1`/`src2` before `dst` update and `actualEff == expectedEff`) catches `Canary 7` (`x86-64` `xor r, r` clobbering `CF` between `ADD64` and `ADC64`), `Canary 7b` (overwritten input physical register), and `HO-4` (`AArch64` `SUBS` vs `ADD` and `x86-64` `AND64` before `CMOVB`); `FastScalarState` reduces 256-instruction ARX blocks by `rfl` (`HO-5`); `checkBranchRelaxationLayout` enforces multi-round fixed-point branch relaxation (`LLVM #61392`, `HO-6`) and `PcRelBaseMode.nextPc` (`x86-64` `rip + instrByteLen + relDisp`). |

---

### 2. Self-Hosting Building Blocks (`BB-ANC-1`–`5`) and `Canaries 8–11`

To self-host the compiler (`anc`) in the terminating, `#![forbid(unsafe_code)]`,
interior-mutability-free Rust subset `$K_{\text{anc}}$` without re-proving
target-language semantics from scratch or opening *Trusting Trust* or TOCTOU
gaps, Anneal introduces five self-hosting building blocks:

#### 2.1 `BB-ANC-1`: `ofRustTwoStepImp` and `ofRustTwoStepNonVacuous`

When a certificate checker `rustCheck : L₁.Prog → L₂.Prog → Cert → Bool` is
written in `$K_{\text{anc}}$` Rust and extracted via `anneal-rustc-capture`,
proving biconditional equivalence `rustCheck s t cert = P.check s t cert` fails
whenever the Rust implementation uses finite `u32` loop/recursion fuel bounds
(returning `false` when `fuel == 0`).

`PassCertChecker.ofRustTwoStepImp` solves this by requiring only the **one-way
implication** `∀ s t cert, rustCheck s t cert = true → P.check s t cert = true`:
1. **Zero Duplicate Simulation Proofs:** `ofRustTwoStepImp` composes `h_imp`
   directly with the existing Lean soundness theorem `P.check_sound`, requiring
   zero new target-language simulation proofs.
2. **Fuel-Bounded Rust Checkers (`DC-15`):** Theorem
   `dc15_fuelBounded_rust_checker_satisfies_twoStepImp` proves with zero axioms
   that `rustCheckWithFuel fuel leanCheck x := (fuel > 0) && leanCheck x`
   satisfies `rustCheckWithFuel fuel leanCheck x = true → leanCheck x = true`
   for every `fuel : UInt32`.
3. **Blocking Vacuous `false` and Buggy Checkers (`Canary 8a/8b`):**
   Because a constant `fun _ _ _ => false` checker would satisfy `h_imp`
   vacuously while silently disabling all optimizations,
   `PassCertChecker.ofRustTwoStepNonVacuous` bundles `ofRustTwoStepImp` with a
   constructive positive acceptance witness `(witSrc, witTgt, witCert)`
   satisfying `rustCheck witSrc witTgt witCert = true`. Conversely,
   `canary8ab_buggy_rust_checker_refutes_twoStepImp` proves that a buggy Rust
   alias checker omitting the self-alias guard (`Canary 8a`) or a buggy post-RA
   checker omitting source-operand verification (`Canary 8b`) is immediately
   refuted.

#### 2.2 `BB-ANC-2`: `FreezeValueWitness` Against TOCTOU (`Canary 9a` / `HO-7`)

Executing untrusted optimization heuristics (`anc-opt`) in-memory inside the
same process as the verified checker (`anc-verified`) is faster than process
serialization, but `#![forbid(unsafe_code)]` alone is **unsound** as an
isolation boundary (`Canary 9a` / `HO-7`):
- Safe Rust permits interior mutability (`core::cell::Cell`, `RefCell`,
  `OnceLock`, backed by `UnsafeCell`) and custom stateful `Deref`
  implementations.
- As mechanized in `ho7_stateful_toctou_two_read_spoofing`, a malicious or buggy
  safe-Rust pass returning a `StatefulCandidate` can return the unmodified
  source program on the first read (`c.onFirstReadForCheck = 42`, passing
  `check 42 c.onFirstReadForCheck = true`) and a mutated program on the second
  read during code emission (`c.onSecondReadForEmit = 999`, where `check 42 999
  = false`).

`FreezeValueWitness T` and `checkInMemoryBoundarySafe` close this TOCTOU channel
by requiring four compile-time boolean properties on both the candidate program
`L.Prog` and certificate `Cert` before
`PassCertChecker.evalIntraWithFreezeGuard` accepts any candidate:
1. `hasForbidUnsafe`: `#![forbid(unsafe_code)]` is active in `anc-opt`;
2. `hasZeroUnsafeCell`: `T : Freeze` (contains zero `UnsafeCell`, `Cell`,
   `RefCell`, `Mutex`, or `OnceLock`);
3. `hasZeroCustomDeref`: `T` is a closed nominal AST/arena value type defined in
   `anc-verified` with zero custom `Deref` or `Drop` hooks; and
4. `isOwnedByMove`: ownership of `OptAttempt` is transferred by value to
   `anc-verified` before `P.check` runs, so `P.check` and code emission read the
   exact same immutable value.

Theorem `ho7_forbidUnsafe_without_freeze_or_nominal_deref_rejected` proves by
`rfl` that violating any of these four conditions causes
`checkInMemoryBoundarySafe` to return `false`, triggering deterministic fallback
to `src` (`withFreezeGuardedIdentityFallback_productiveSoundOn`).

#### 2.3 `BB-ANC-3`: Unified Fallback and 3-Stride `runPostRaCheckBlockV2Fast`

When an untrusted pass returns `.outOfFuel`, `.panicked`, or a candidate
rejected by `P.check` (`Canary 9b`), the compiler must fall back without
aborting compilation:
1. **Master Fallback Combinator (`withFallbackCompiler`):** Unifies intra-IR
   identity fallback (`withIdentityFallback`, returning `src` via
   `productiveCompiles_id_refl`), verified total cross-IR fallback
   (`withVerifiedFallback`), and self-certifying cross-IR fallback
   (`withSelfCertifyingFallback`) under a single soundness theorem
   `PassCertChecker.withFallbackCompiler_productiveSoundOn` (proved with zero
   axioms).
2. **Self-Certifying Cross-IR Fallback (`withSelfCertifyingFallback`, `HO-8`):**
   At cross-IR boundaries where `L₁.Prog ≠ L₂.Prog` (such as `RegAlloc` from
   virtual-register `AnMachineLang` to physical-register `PostRaMachineLang`),
   identity fallback `src` is ill-typed. Instead of proving a separate semantic
   simulation theorem for a fallback register allocator,
   `withSelfCertifyingFallback` invokes `trivialSpillRegAlloc` (`fallback :
   L₁.Prog → Option (L₂.Prog × Cert)`) and validates its output
   (`trivialSpillFallbackBlock`) through the **exact same checker `P.check`**,
   requiring **zero extra semantic soundness theorems**
   (`canary9_and_ho8_fallback_recovery`).
3. **3-Stride `runPostRaCheckBlockV2Fast`:** Because `trivialSpillRegAlloc`
   emits a `loadSpill` + `aluOp` + `storeSpill` triple (3 instructions) for each
   virtual-register instruction, a 256-instruction block expands to 768 post-RA
   instructions. `runPostRaCheckBlockV2Fast` steps 3 `PostRaCheckInstrV2`
   instructions per recursive call (proved pointwise equal to
   `runPostRaCheckBlockV2` in `runPostRaCheckBlockV2Fast_eq` with zero axioms),
   validating 768-instruction spill blocks in 256 recursion frames (well inside
   Lean 4.34.1's default `maxRecDepth = 4096`).

#### 2.4 `BB-ANC-4`: Overflow-Checked 64-Bit Range Disjointness (`Canary 10`)

When range and offset checks in `checkAliasDisjoint` (`.constOffsetDisj`),
`loadWord64`/`storeWord64`, or `checkBranchRelaxationLayout` are implemented in
`$K_{\text{anc}}$` using fixed-width 64-bit integers (`BitVec 64` / `u64`), two
distinct modular-wrapping bugs arise:
1. **Lower-Interval Wrapping (`Canary 10`):** Under naive modular addition
   `wrappingAddLeU64_buggy a b limit := BitVec.ule (a + b) limit`, setting
   `o₁ = 0xFFFFFFFFFFFFFFF8#64` ($2^{64} - 8$), `sz₁ = 16#64`, and `o₂ = 12#64`
   wraps `(o₁ + sz₁) mod 2^64` to `8#64 <= 12#64` (`true`), falsely certifying
   overlapping memory slices as disjoint! `checkAddLeU64` uses `checkedAddU64`
   (`if BitVec.ult (a + b) a then none else some (a + b)`) and rejects this wrap
   by `rfl` (`canary10_wrapping_u64_spoofs_disjointness_caught_by_checkedAdd`).
2. **Upper-Interval Wrapping (`HO-9b`):** Even with `checkAddLeU64`, testing
   only `checkAddLeU64 o₁ sz₁ o₂ || checkAddLeU64 o₂ sz₂ o₁` is unsound when the
   **upper** interval wraps $2^{64}$! For `o₁ = 0#64, sz₁ = 8#64` (`[0, 8)`) and
   `o₂ = 0xFFFFFFFFFFFFFFF8#64, sz₂ = 16#64` (`[2^64 - 8, 2^64 + 8)`, which
   wraps around $2^{64}$ to overlap `[0, 8)`), `checkAddLeU64 o₁ sz₁ o₂`
   evaluates `0 + 8 <= 2^64 - 8` (`= true`!). `checkDisjointRangesU64Strict`
   requires **both** `(checkedAddU64 o₁ sz₁).isSome` and
   `(checkedAddU64 o₂ sz₂).isSome` before testing
   `checkAddLeU64 o₁ sz₁ o₂ || checkAddLeU64 o₂ sz₂ o₁`, rejecting `HO-9b` by
   `rfl` (`ho9b_and_canary10ab_integer_and_fuel_guards`).

To bridge `BitVec 64` no-wrap checks to mathematical `Nat` inequalities without
importing `Std` or invoking `Classical.choice`/`propext`, our probe proves
`nat_add_mod_no_wrap_zero_axioms`, `checkAddLeU64_implies_toNat_le`, and
`checkDisjointRangesU64Strict_implies_nat_disjoint` from first principles over
`Nat.modCore`. `#print axioms` confirms that all three theorems depend on **zero
axioms** (`does not depend on any axioms`).

#### 2.5 `BB-ANC-5`: `PassExecMode` and 3-Stage Fixed Point (`Canary 11`)

`PassCertChecker.selectMode` parameterizes each pass by `mode : PassExecMode`
(`.leanKernel` at Stage 0 vs. `.selfHostedRust` at Stage 1+), allowing the 26
passes to migrate to `$K_{\text{anc}}$` Rust one pass at a time while preserving
`ProductiveSoundOn` (`PassCertChecker.selectMode_productiveSoundOn`).

At the 3-stage bootstrap gate (`Stage 0 -> Stage 1 -> Stage 2`), checking only
`stage1ActualBytes == stage2ActualBytes` is vulnerable to two classic bootstrap
attacks (`Canary 11` / `HO-10`):
1. **External Assembler *Trusting Trust* Attack:** If the compiler emits `.s`
   assembly text (`.option5A_assemblyTextS`), a trojaned external assembler can
   inject a backdoor when assembling both Stage 1 and Stage 2, producing
   identical trojaned binaries.
2. **Self-Reproducing Stage-1 Quine:** A corrupted Stage-1 binary whose machine
   bytes `stage1ActualBytes` differ from the Lean-verified `EmittedArtifact`
   bytes `stage1VerifiedBytes` can still reproduce its own corrupted bytes when
   compiling Stage 2 (`stage1ActualBytes == stage2ActualBytes`), passing a naive
   Stage-1-vs.-Stage-2 comparison!

`checkBootstrapFixedPoint` and `checkBootstrapFixedPointWithUnit` defeat both
attacks (`dc19_bootstrap_fixed_point_and_canaries_by_rfl`) by requiring:
- `c.emissionMode == .option5B_machineBytesO` (direct ELF `.o` emission);
- `u.waived.isEmpty` and `c.stage0WaivedEmpty` (zero waived obligations in the
  compiler's own `VerificationUnit`);
- `c.stage1VerifiedBytes == c.stage1ActualBytes` (anchoring the Stage-1 binary
  on disk to the Lean-verified `EmittedArtifact` bytes from Stage 0); and
- `c.stage1ActualBytes == c.stage2ActualBytes` (confirming the Stage-1-to-2
  reproducibility fixed point).

---

### 3. Decoupling `VerifiedCompilationTheorem` from `StrictUnitTheorem`

A central architectural question for compiling the Rust standard library and
`rustc` itself (249 crates, ~300k–907k symbols) is how to verify **compiler
correctness** for upstream crates that contain internal `unsafe` blocks (`core`,
`alloc`, `std`, `rustc`) but lack manual deductive functional specifications.

In `Trusted/MirSemantics.lean` and `Trusted/Refinement.lean` (mechanized in
Section 9 of
[`anllvm_five_primitive_and_canaries_probe.lean`](support/anllvm_five_primitive_and_canaries_probe.lean)),
each captured function `fn` generates two obligations in `fn.obligations`:
1. `.rustcLowering fn.name`: `Compiles MirLang Rv64Lang mirToRv64Codec fn.prog
   rv64Prog` (conditional forward semantics preservation from `MIR` to
   `RV64GC`); and
2. `.fnVerified fn.name`: `MirLang.WellFormedOn` + functional `specs` (source
   UB-freedom and specification satisfaction).

Anneal decouples source verification from compiler verification via two
orthogonal trust policies and root theorems:

| Root Theorem | Trust Policy | `.rustcLowering` Waiver | `.fnVerified` Waiver | `.userAxiom` Waiver | Target `rv64Body` & `EmittedArtifact.holds` | Primary Use Case |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`CrateTheorem`** (Source Verification Mode) | `defaultTrustPolicy` | Permitted (`True`) when using external `rustc` | **Forbidden (`False`)** | **Forbidden (`False`)** | Optional (`rv64Body = none` allowed) | Verifying source safety & functional specs of user Rust crates (`zerocopy`, `$K_{\text{anc}}$`). |
| **`StrictUnitTheorem`** (Zero-Debt Full Stack) | `TrustPolicy.strict` (`waived = []`) | **Forbidden (`False`)** | **Forbidden (`False`)** | **Forbidden (`False`)** | **Required (`EmittedArtifact.holds`)** | Self-hosted `$K_{\text{anc}}$` compiler (`anc`) where both source safety and `RV64GC` compilation are proved with zero waivers. |
| **`VerifiedCompilationTheorem`** (Compiler Correctness Mode) | `compilationTrustPolicy` | **Forbidden (`False`)** | Permitted (`True`) | **Forbidden (`False`)** | **Required (`rv64Body.isSome = true` & `EmittedArtifact.holds`)** | Compiling unannotated upstream crates (`core`, `alloc`, `std`, `rustc`) with a machine-checked `Compiles MirLang Rv64Lang` proof for every function. |

Why does waiving `.fnVerified` (`Or.inl`) in `VerifiedCompilationTheorem` never
weaken or contaminate the `.rustcLowering` (`Compiles`) proof?
1. **Positive Per-Obligation Disjunction (Zero Antecedent Explosion):**
   `VerificationResult policy waived obligations` checks
   `AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))` alongside
   `AllHold (waived.map policy.isAllowed)`. Because `ob.id ∈ waived ∨ ob.prop`
   contains **zero antecedent implications (`→`)**, waiving `.fnVerified fn` via
   `Or.inl` does not introduce a false hypothesis into the proof context that
   could discharge `.rustcLowering fn` via `False.elim`.
2. **Conditional Refinement Semantics of `Compiles`:**
   By definition of `Compiles MirLang Rv64Lang mirToRv64Codec fn.prog rv64Prog`,
   `Rv64Lang.sem rv64Prog ≤ mirToRv64Codec.toMorphism (MirLang.sem fn.prog)`
   quantifies over all initial states where the source `MIR` execution is
   defined (`h₂ : (MirLang.sem fn.prog q).defined`) and proves that the emitted
   `RV64GC` machine code is defined and produces a refining execution trace—the
   exact CompCert / Rust Reference compiler-correctness contract.

Theorem `verifiedCompilationTheorem_decouples_compiler_from_source_specs` proves
with **zero axioms** that an unannotated crate (`raw_vec_grow`) whose source
specification is unproved (`post := fun _ _ => False`) satisfies
`VerifiedCompilationTheorem` when `.fnVerified "raw_vec_grow"` is listed in
`tcb` (`Or.inl`) and `.rustcLowering "raw_vec_grow"` is proved constructively
(`Or.inr`), whereas any attempt to waive `.rustcLowering "raw_vec_grow"` is
refuted (`¬ VerifiedCompilationTheorem crBadWaiver`).

## Boundaries

The guarantees mechanized in this report are subject to four explicit scope
boundaries:

1. **Pre-`Runtime(PostCleanup)` Front-End Lowering:** Both `CrateTheorem` and
   `VerifiedCompilationTheorem` begin at `anneal-rustc-capture`'s extracted
   `Runtime(PostCleanup)` MIR. Parsing, macro expansion, trait resolution,
   borrow checking, and `THIR -> MIR` construction remain inside the front-end
   capture boundary until migrated into `$K_{\text{anc}}$`.
2. **Linker and OS Loader Outside `.directElfObject`:** While
   `ArtifactEmissionMode.option5B_machineBytesO` (`.directElfObject`) and
   `checkBootstrapFixedPointWithUnit` verify emitted `.o` machine bytes and
   eliminate the external `.s` assembler from the TCB, static/dynamic ELF
   relocation linking (`lld`) and OS kernel execve loading remain outside the
   per-crate `.o` artifact boundary unless a verified linker pass is composed.
3. **Hardware Execution vs. ISA Semantics:** `Rv64Lang`
   (`Trusted/Rv64Semantics.lean`, validated against `opencompl/sail-riscv-lean`)
   models architectural `RV64GC` user-mode instruction semantics. Physical
   silicon errata, speculative side channels beyond `ArchEvent.uarchLeakage`,
   and DMA device interference lie outside the architectural ISA model.
4. **Conditional Nature of `VerifiedCompilationTheorem`:** For unannotated
   crates verified under `VerifiedCompilationTheorem` (where `.fnVerified` is
   waived in `c.tcb`), the theorem guarantees that compilation preserves
   behavior on all inputs where the source `MIR` has defined behavior; proving
   that an `unsafe` source function never triggers `MIR` UB requires discharging
   `.fnVerified` under `CrateTheorem` or `StrictUnitTheorem`.

## Evidence

All claims in this report are backed by primary source files in `joshlf/anneal`
and by the standalone Lean 4.34.1 verification probe in [`support/`](support/):

- **Standalone Mechanized Probe
  ([`anllvm_five_primitive_and_canaries_probe.lean`](support/anllvm_five_primitive_and_canaries_probe.lean)):**
  - *Lines 34–395 (`Trusted` & `Anneal` Foundation):* Mechanizes `Preorder`,
    `Partial`, `Behavior`, `Language`, `BehaviorCodec`, `Compiles`,
    `ProductiveCompiles`, `Obligation`, `TrustPolicy`, `EmittedArtifact`,
    `NoDupIds`, `VerificationResult`, `VerificationUnit`, `UnitTheorem`,
    `StrictUnitTheorem`, and `BB8.PassCompiler`.
  - *Lines 397–686 (Layer 0 & Layer 1 — `CompilerSpine`, `MaskedWord w`,
    `VecWord N W`):* Mechanizes `ArchEvent`, `ArchReturn`, `CompilerSpine`,
    `MaskedWord.freeze`, `checkRefinesOnMask`, `checkRefines_refl`, `evalAdd`,
    `evalSub`, `evalAnd`, `evalOr`, `evalXor`, `evalShl`, `evalLshr`,
    `evalUdiv`, `evalSdiv64`, `evalZext32To64`, `evalUaddo64`, `evalUadde64`,
    `pack8BytesLE`, `extractByteLE`, and `vecWord_map2_lane_isolated`.
  - *Lines 688–994 (Layer 2 — `DualViewMemory`, Two-Tier `inttoptr`, Dynamic
    `TreeBorrows`):* Mechanizes `MemBlock`, `MemState`, `listSetStrict`,
    `checkNoDupBlockIds`, `evalPtrToInt`, `evalIntToPtr`,
    `evalIntToPtrWithBoundary`, `stepTreeBorrows`, `loadWord64`, `storeWord64`,
    and `evalIntToPtr_never_returns_unexposed`.
  - *Lines 996–1204 (Layer 3 — `BehaviorCodec`, `FeatureProfile`,
    `PassCertChecker`):* Mechanizes `mkTargetCodec`,
    `mkTargetCodec_rejects_invalid_abi_frame`, `mkLayerCodec`, `FeatureProfile`,
    `optField_false_rfl`, `ExtVal.elimScalarCore`, `ProfiledState`,
    `PassCertChecker.withWitness_productiveSoundOn`, and
    `PassCertChecker.seq2_productiveSoundOn`.
  - *Lines 1206–1572 (Layer 4 — `CC-1`–`CC-5` & `TargetIsaBackend`):* Mechanizes
    `evalDestPropFull`, `checkAliasDisjoint`, `checkUnswitchCondSafe`,
    `checkLoopDeletionSafe`, `checkIndVarWiden`, `checkTailCallElim`,
    `stepPostRaCheckV2`, `runPostRaCheckBlockV2`, `checkPcRelDisp`,
    `checkBranchRelaxationLayout`, `TargetIsaBackend`, and `NaiveBaseline`.
  - *Lines 1574–2310 (`BB-ANC-1`–`BB-ANC-5` Self-Hosting Building Blocks):*
    Mechanizes `ofRustTwoStepImp`, `ofRustTwoStepNonVacuous`, `ofRustLowerer`,
    `FreezeValueWitness`, `checkInMemoryBoundarySafe`,
    `withFreezeGuardedIdentityFallback_productiveSoundOn`,
    `withFallbackCompiler_productiveSoundOn`,
    `withSelfCertifyingFallback_productiveSoundOn`,
    `runPostRaCheckBlockV2Fast_eq`, `trivialSpillFallbackBlock`,
    `checkedAddU64`, `checkAddLeU64`, `nat_add_mod_no_wrap_zero_axioms`,
    `checkAddLeU64_implies_toNat_le`,
    `checkDisjointRangesU64Strict_implies_nat_disjoint`,
    `PassExecMode.selectMode`, `checkBootstrapFixedPoint`, and
    `checkBootstrapFixedPointWithUnit`.
  - *Lines 2312–2806 (Mechanized Canaries 1–11 & Held-Out `HO-1`–`HO-10`):*
    Proves `canary1_carry_borrow_shift_monotonicity_restored`,
    `canary1ab_destProp_two_parameter_union`,
    `canary2abc_speculative_udiv_and_load_rejected`,
    `canary2_adjacent_twin_allocations_two_tier_inttoptr`,
    `canary3_alias_disjoint_blocks_all_four_exploits`,
    `canary5abc_sroa_padding_and_stackColoring`,
    `ho1_dynamic_treeBorrows_diamond_write_disables_sibling_frozen`,
    `ho2ab_indvar_widen_and_loopVectorize_guards`,
    `ho3ab_tailCall_and_unwind_calleeSaved_guards`,
    `ho4_and_canary7b_postRa_input_and_flag_clobbers`,
    `ho5_scale256_fastScalarState_whnf_rfl`,
    `ho6_singlePass_fails_cascading_displacement_twoRound_succeeds`,
    `dc15_fuelBounded_rust_checker_satisfies_twoStepImp`,
    `canary8ab_buggy_rust_checker_refutes_twoStepImp`,
    `ho7_stateful_toctou_two_read_spoofing`,
    `canary9_and_ho8_fallback_recovery`, and
    `ho9b_and_canary10ab_integer_and_fuel_guards`.
  - *Lines 2808–2951 (`VerifiedCompilationTheorem` Decoupling & Kernel Axiom
    Audit):* Mechanizes `TCBItem`, `defaultTrustPolicy`,
    `compilationTrustPolicy`, `VerifiedCompilationTheorem`,
    `verifiedCompilationTheorem_decouples_compiler_from_source_specs`, and 28
    `#print axioms` queries.
- **Recorded Lean 4.34.1 Kernel Verification Output
  ([`lean_verification_output.txt`](support/lean_verification_output.txt)):**
  Records the exact output of `lean` `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`) on
  `support/anllvm_five_primitive_and_canaries_probe.lean`, confirming exit code
  `0`, 20 theorems with `does not depend on any axioms`, 8 `BitVec` theorems
  using only `[propext]` or `[propext, Quot.sound]`, and zero occurrences of
  `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool`.

## Revalidation

To revalidate the mechanized proofs and axiom audit in this report from a clean
checkout, run Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
directly on the standalone `prelude` probe and compare the output and SHA-256
digests:

```bash
lean support/anllvm_five_primitive_and_canaries_probe.lean > /tmp/lean_out.txt 2>&1
diff -u support/lean_verification_output.txt /tmp/lean_out.txt
sha256sum support/anllvm_five_primitive_and_canaries_probe.lean support/lean_verification_output.txt
```

Revalidation succeeds if:
1. `lean` exits with status `0` and `diff -u` produces empty output;
2. Every `#print axioms` line in `support/lean_verification_output.txt` reports
   either `does not depend on any axioms` or a subset of `[propext, Quot.sound]`
   (with zero `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool`); and
3. Any change to `Trusted/Refinement.lean`, `Trusted/MirSemantics.lean`, or
   `theory/Anneal/Compiler/AnLlvmCore.lean` in `joshlf/anneal` preserves all 28
   positive and negative canary theorems in
   `support/anllvm_five_primitive_and_canaries_probe.lean`.
