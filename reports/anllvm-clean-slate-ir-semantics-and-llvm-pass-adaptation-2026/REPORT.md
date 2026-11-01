<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Clean-Slate `AnLLVM-IR` Formal Semantics and LLVM Middle-End Pass Adaptation in Anneal

## Executive Summary

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

## 1. Primary-Source Audit: LLVM 21.1.8 and `rustc` (`49d734536222bf28bb6d07d885b3a81d145981da`)

### 1.1 LLVM 21.1.8 IR & Analysis Headers (`/usr/include/llvm-21/llvm/`)

| Header File | Lines Audited | Key Classes / Methods / Flags & Role in `AnLLVM-IR` |
| :--- | :--- | :--- |
| `IR/Instruction.def` | `1–255` | Defines all 67 upstream instruction opcodes: Terminators `1..11` (`Ret`, `Br`, `Switch`, `IndirectBr`, `Invoke`, `Resume`, `Unreachable`, `CleanupRet`, `CatchRet`, `CatchSwitch`, `CallBr`), Unary `12` (`FNeg`), Binary `13..30` (`Add`..`Xor`), Memory `31..37` (`Alloca`, `Load`, `Store`, `GetElementPtr`, `Fence`, `AtomicCmpXchg`, `AtomicRMW`), Cast `38..50` (`Trunc`..`BitCast`, `AddrSpaceCast`), Pad `51..52`, Other `53..67` (`ICmp`, `FCmp`, `PHI`, `Call`, `Select`, `UserOp1`, `UserOp2`, `VAArg`, `ExtractElement`, `InsertElement`, `ShuffleVector`, `ExtractValue`, `InsertValue`, `LandingPad`, `Freeze`). |
| `IR/Operator.h` | `65–590` | `Operator::hasPoisonGeneratingFlags()` (L67), `hasPoisonGeneratingAnnotations()` (L72); `OverflowingBinaryOperator` (`NoUnsignedWrap = 1<<0`, `NoSignedWrap = 1<<1`, L78–144); `PossiblyExactOperator` (`IsExact = 1<<0`, L154–190); `PossiblyDisjointInst` (`IsDisjoint`, for `or disjoint`); `GEPOperator` (`getNoWrapFlags()`, `isInBounds()`, `hasNoUnsignedSignedWrap()`, `hasNoUnsignedWrap()`, `accumulateConstantOffset()`, `collectOffset()`, L419–553); `PtrToIntOperator` (L561–590). |
| `IR/GEPNoWrapFlags.h` | `26–104` | Bitfield encoding of GEP poison flags: `InBoundsFlag = 1<<0`, `NUSWFlag = 1<<1`, `NUWFlag = 1<<2`. Note `inbounds` implies `nusw` (`GEPNoWrapFlags::inBounds()` sets `InBoundsFlag \| NUSWFlag` at L47), and `intersectForOffsetAdd()` (`L85–90`) drops `InBoundsFlag` when combining two dynamic offsets while preserving `NUWFlag` and `NUSWFlag`. |
| `IR/Instructions.h` | `64–5171` | `AllocaInst` (L64–172), `LoadInst` (L180–289), `StoreInst` (L296–416), `GetElementPtrInst` (L949–1150), `PHINode` (`getIncomingValue`, `setIncomingValue`, `getIncomingBlock`, `setIncomingBlock`, `replaceIncomingBlockWith`, `addIncoming`, `removeIncomingValue`, `getBasicBlockIndex`, `getIncomingValueForBlock`, `setIncomingValueForBlock`, `hasConstantValue`, `hasConstantOrUndefValue`, `isComplete`, L2638–2861), `FreezeInst` (L5152–5171). |
| `IR/IntrinsicInst.h` | `155–1746` | `LifetimeIntrinsic` (`llvm.lifetime.start` / `llvm.lifetime.end`, L155–165), `NoAliasScopeDeclInst` (`llvm.experimental.noalias.scope.decl`, L1649–1669), `AssumeInst` (`llvm.assume`, L1738–1746). |
| `Analysis/ValueTracking.h` | `61–825` | `computeKnownBits` (L61–93), `GetPointerBaseWithConstantOffset` (L344–360), `isGuaranteedToTransferExecutionToSuccessor` (L691–710), `propagatesPoison` (L728), `mustTriggerUB` (L736), `programUndefinedIfUndefOrPoison` / `programUndefinedIfPoison` (L745–746), `canCreateUndefOrPoison` / `canCreatePoison` (L766–769), `impliesPoison` (L774), `isGuaranteedNotToBeUndefOrPoison` / `isGuaranteedNotToBePoison` / `isGuaranteedNotToBeUndef` (L786–812), `mustExecuteUBIfPoisonOnPathTo` (L821–823). |
| `Analysis/MemorySSA.h` | `140–1305` | `MemoryAccess` (L140–231), `MemoryUseOrDef` (L250–303), `MemoryUse` (L310–356), `MemoryDef` (L371–419), `MemoryPhi` (L479–661), `MemorySSA` (L702–913), `MemorySSAWalker::getClobberingMemoryAccess` (L1024–1107), `upward_defs_iterator` & `PHITransAddr` (L1228–1305). |
| `Analysis/AliasAnalysis.h` | `78–716` | `AliasResult::Kind` (`NoAlias=0`, `MayAlias=1`, `PartialAlias=2`, `MustAlias=3` + 29-bit signed `Offset` bitfield, L78–140); `AAQueryInfo` (`MayBeCrossIteration`, L242–306); `AAResults` (`alias`, `isNoAlias`, `isMustAlias`, `pointsToConstantMemory`, `getModRefInfoMask`, `getArgModRefInfo`, `getMemoryEffects`, `getModRefInfo`, `callCapturesBefore`, L318–648); `BatchAAResults` (L656–716). |
| `Analysis/ScalarEvolution.h` | `127–956` | `SCEV::NoWrapFlags` (`FlagAnyWrap`, `FlagNW`, `FlagNUW`, `FlagNSW`, L127–133); `SCEVWrapPredicate::IncrementWrapFlags` (`IncrementNUSW`, `IncrementNSSW`, L343–348); `ScalarEvolution` (`getSCEV`, `getLosslessPtrToIntExpr`, `getPtrToIntExpr`, `getAddRecExpr`, `getGEPExpr`, `getPointerBase`, `removePointerBase`, `containsUndefs`, `getBackedgeTakenCount`, `getExitCount`, `getSmallConstantTripCount`, L448–956). |

### 1.2 `rustc_codegen_ssa` and `rustc_codegen_llvm` (`49d734536222bf28bb6d07d885b3a81d145981da`)

| Source File | Lines | Key Findings for `MIR -> AnLLVM-IR` Lowering |
| :--- | :--- | :--- |
| `compiler/rustc_codegen_ssa/src/traits/builder.rs` | `353–373` | `BuilderMethods` **already** defines `ptradd(&mut self, ptr: Self::Value, offset: Self::Value) -> Self::Value` (`gep(self.cx().type_i8(), ptr, &[offset])`, L368–370) and `inbounds_ptradd(&mut self, ptr: Self::Value, offset: Self::Value) -> Self::Value` (`inbounds_gep(self.cx().type_i8(), ptr, &[offset])`, L371–373). |
| `compiler/rustc_codegen_ssa/src/mir/place.rs` | `180–294` | Struct/enum field projection (`PlaceRef::project_field`, L180–198, L249) **already** calls `bx.inbounds_ptradd(self.val.llval, bx.const_usize(offset.bytes()))`. Only array/slice indexing (`project_index`, L277–294) calls `bx.inbounds_nuw_gep(bx.cx().backend_type(layout), self.val.llval, &[llindex])`, which lowers directly to `ptradd inbounds nuw %base, (mul nuw %idx, sizeof(Elem))`. |
| `compiler/rustc_codegen_ssa/src/mir/statement.rs` | `72–85` | `mir::StatementKind::StorageLive(local)` (`L72–78`) and `StorageDead(local)` (`L79–85`) act directly on `LocalRef::Place(cg_place)` via `cg_place.storage_live(bx)` / `cg_place.storage_dead(bx)`. |
| `compiler/rustc_codegen_llvm/src/builder.rs` | `1911–1929` | In `lifetime_start`/`lifetime_end` (`L1911–1929`), `rustc` already branches on `llvm_util::get_version() >= (22, 0, 0)` (`L1921`): LLVM 22 drops the byte-size parameter and requires the lifetime intrinsic to act directly on the `alloca` after `LLVMRustStripPointerCasts(ptr)`. `AnLLVM-IR`'s `AllocaLive(allocId)` / `AllocaDead(allocId)` completes this transition at the semantic level. |
| `compiler/rustc_codegen_ssa/src/mir/block.rs` & `rustc_codegen_llvm/src/abi.rs` | `block.rs:612–648`, `abi.rs:45, 108, 252–282` | Under `PassMode::Cast { pad_i32, cast }`, `rustc` calls `load_cast` (`block.rs:646`) and `store_cast` (`abi.rs:270`) to load/store a struct across uninitialized padding bytes using an integer register type (`i64` or `[N x i64]`). Notice `abi.rs:45, 108` only attaches `llvm::AttributeKind::NoUndef` to `PassMode::Direct` (when `attrs.regular.contains(ArgAttribute::NoUndef)`), **not** `PassMode::Cast`, because `PassMode::Cast` registers carry uninitialized padding bits. |
| `compiler/rustc_codegen_llvm/src/builder.rs` | `1635–1670` | `load_from_place` attaches `!range` (`L1659`), `!nonnull` (`L1663`), and `!noundef` (`L1667–1669`) metadata on scalar loads when `scalar.is_always_valid(cx)` holds. |
| `compiler/rustc_codegen_llvm/src/attributes.rs` | `90–145` | `rustc` emits `WillReturn` (`L103`) **only** when `CodegenFnAttrFlags::FFI_CONST` or `FFI_PURE` is set, and **never** emits C++'s `mustprogress` attribute on general Rust functions because Rust loops may legitimately diverge (`loop {}`). |

---

## 2. Empirical LLVM 21.1.8 `/usr/bin/opt` & `/usr/bin/llc` Semantic Probes

All five empirical LLVM IR probe suites and their LLVM 21.1.8 outputs are
preserved in `support/`:

### 2.1 Probe A (`support/probe_a_ptrtoint_gvn.ll` -> `support/probe_a_ptrtoint_gvn.opt.ll`): `ptrtoint` + `GVN` + `InstCombine` + `BasicAA` Miscompilation

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

### 2.2 Probe B (`support/probe_b_sroa_padding.ll` -> `support/probe_b_sroa_padding.opt.ll`): `SROA` on `PassMode::Cast` Struct Padding

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

### 2.3 Probe C (`support/probe_c_unswitch_freeze.ll` -> `support/probe_c_unswitch_freeze.opt.ll`): `SimpleLoopUnswitchPass` Inserting `freeze`

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

### 2.4 Probe D (`support/probe_d_lifetime_aa.ll` -> `support/probe_d_lifetime_aa.opt.ll` & `support/probe_d_lifetime_aa.s`): `DSE`, `InstCombine`, and `StackColoring` Contradiction

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

### 2.5 Probe E (`support/probe_e_mustprogress_loops.ll` -> `support/probe_e_mustprogress_loops.opt.ll`): `LoopDeletion` and `ADCE` vs. `mustprogress` / `willreturn`

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

## 3. Part I: The Seven Clean-Slate Semantic Modifications of `AnLLVM-IR`

### Modification 1: Complete `undef` Elimination -> Pure `poison` + `freeze`

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

### Modification 2: First-Class Provenance Pointers `Ptr(allocId, offset, tag)` + `ptradd` + Split `ptrtoaddr` vs. `ptrtoint`

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
      reconstruction operations (C23 PNVI-ae-udi / Rust Strict Provenance
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

### Modification 3: Bitwise-Masked Scalar Values (`MaskedWord w`) & First-Class Byte Memory (`Byte`)

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

### Modification 4: Predecessor-Indexed $\phi$-Tables / Basic-Block Arguments Isomorphism & `PHINode` Compatibility Lens

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

### Modification 5: Direct `AllocId`-Scoped `AllocaLive`/`AllocaDead` Instead of Pointer-Based `llvm.lifetime.start/end`

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

### Modification 6: First-Class Tree-Borrows `BorrowTag` & `ProtectorId` on Memory Operations Instead of `noalias` Scope Metadata

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

### Modification 7: Rust-Default `mayDiverge` Loop/Function Semantics with Explicit `FiniteTripWitness`

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

## 4. Part II: Structural Decomposition of LLVM 21.1.8's `default<O2>` Middle-End Pipeline

### 4.1 Six-Phase Decomposition of the 84-Invocation `default<O2>` Pipeline

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

### 4.2 Complete 20-Pass Architectural Adaptation Matrix for `AnLLVM`

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

## 5. Empirical Pass-Ablation Benchmark (`P0..P6`) on Realistic Rust Code

### 5.1 Benchmark Suite & Methodology (`support/ablation_benchmark.py`, `support/bench_suite.rs`)

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

### 5.2 Whole-Module Quantitative Ablation Table

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

### 5.3 Per-Function Breakdown Across All 6 Rust Benchmark Kernels

| Rust Function | Metric | `P0` | `P1` | `P2` | `P3` | `P4` | `P5` | `P6_scalar` | `P6` (`default<O2>`) | Primary Winning Passes |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **`slice_sum_stride`** | IR Insts / `alloca` / `load` / `store` | `57` / `6` / `14` / `8` | `39` / `0` / `2` / `0` | `34` / `0` / `2` / `0` | `29` / `0` / `1` / `0` | `26` / `0` / `1` / `0` | **`23` / `0` / `1` / `0`** | `24` / `0` / `1` / `0` | `24` / `0` / `1` / `0` | `SROA` (`6 -> 0` `alloca`), `Inliner` (`slice::len`), `LICM` (`scale * 3` hoisted), `IndVarSimplify` |
| **`option_Result_chain`** | IR Insts / `alloca` / `load` / `store` | `36` / `3` / `5` / `6` | `36` / `3` / `5` / `6` | `36` / `3` / `5` / `6` | `21` / `0` / `0` / `0` | **`15` / `0` / `0` / `0`** | **`15` / `0` / `0` / `0`** | `15` / `0` / `0` / `0` | `15` / `0` / `0` / `0` | `Inliner + Post-Inline SROA` (eliminates all 3 `Option` stack slots that escaped into `Option::map` at `P1`), `JumpThreading + SCCP` (`21 -> 15` insts) |
| **`struct_field_packing`** | IR Insts / `alloca` / `load` / `store` | `37` / `3` / `6` / `5` | `30` / `1` / `2` / `4` | `28` / `1` / `2` / `4` | `26` / `0` / `1` / `1` | **`17` / `0` / `0` / `1`** | **`17` / `0` / `0` / `1`** | `16` / `0` / `0` / `1` | `16` / `0` / `0` / `1` | `Inliner + SROA` (`PacketHeader` promoted to registers), `GVN + DSE` (kills redundant `out[0]` store and forwards live store), `BDCE + InstCombine` |
| **`checked_index_bounds`** | IR Insts / `alloca` / `load` / `store` | `83` / `3` / `14` / `5` | `67` / `0` / `8` / `0` | `62` / `0` / `6` / `0` | `62` / `0` / `4` / `0` | **`47` / `0` / `4` / `0`** | **`47` / `0` / `4` / `0`** | `47` / `0` / `4` / `0` | `47` / `0` / `4` / `0` | `SROA` (`3 -> 0` `alloca`), `EarlyCSE` (`8 -> 6` `load`), `CVP + ConstraintElimination + SimplifyCFG` (`62 -> 47` insts by discharging redundant bounds checks) |
| **`iterator_fold_filter`** | IR Insts / `alloca` / `load` / `store` | `38` / `6` / `5` / `9` | `38` / `5` / `4` / `8` | `38` / `5` / `4` / `8` | `37` / `0` / `1` / `0` | `34` / `0` / `1` / `0` | **`18` / `0` / `1` / `0`** | `20` / `0` / `1` / `0` | `141` / `0` / `15` / `0` | `Inliner + Post-Inline SROA` (collapses `Copied<Iter>`, `Map`, `Filter` structs into `0` `alloca`s), `LoopRotate + LICM + IndVars` (`34 -> 18` insts; `P6` bloats to `141` insts via runtime unroll/vectorize) |
| **`enum_state_machine`** | IR Insts / `alloca` / `load` / `store` | `87` / `7` / `24` / `15` | `47` / `0` / `6` / `5` | `46` / `0` / `6` / `2` | `55` / `0` / `0` / `0` | `50` / `0` / `0` / `0` | **`43` / `0` / `0` / `0`** | `43` / `0` / `0` / `0` | `43` / `0` / `0` / `0` | `SROA` (`7 -> 0` `alloca`, `24 -> 6` `load`), `EarlyCSE` (`5 -> 2` `store`), `Inliner + SROA` (`6 -> 0` `load`), `LoopRotate + LICM` (`50 -> 43` insts) |

### 5.4 Architectural Takeaways from the Ablation Study

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

## 6. Deep-Dive Verification Architectures for the Four Hardest Middle-End Components

### 6.1 `SROA` (`SROA.h`) + `PromoteMemToReg` (`PromoteMemToReg.h`) via `SroaAndMem2RegCertChecker` (Mode B)

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

### 6.2 `InstCombine` (`InstCombine.h`) + `BDCE` (`DemandedBits.h`) via `InstCombineBdcePassCompiler` (Mode A)

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

### 6.3 `NewGVN` (`NewGVN.h`), `MemorySSA` (`MemorySSA.h`), `DSE` (`DeadStoreElimination.h`), and `MemCpyOpt` (`MemCpyOptimizer.h`) via `MemorySsaGvnDseCertChecker` (Mode B)

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

### 6.4 Loop Optimizations (`LoopRotate`, `LICM`, `IndVarSimplify` / `SCEV`) via `ScevIndVarAndLicmCertChecker` (Mode B)

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

## 7. Mechanized Lean 4.34.1 Soundness Probes

Both standalone Lean 4.34.1 files in `support/` are verified with:
```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M1024 -DElab.async=false -Ddebug.skipKernelTC=false <file.lean>
```
with exit code `0`, zero warnings, zero `sorryAx`, zero `Lean.ofReduceBool`, and
zero `Lean.trustCompiler`.

### 7.1 `support/support_clean_slate_llvm_ir_probe.lean` (`1,272` lines, SHA-256 `fcc223ec1d1f32aeac617acbfed3ad1183dfc7ec2bcd2628185eec3eace17ee0`)

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

### 7.2 `support/support_anllvm_middle_end_passes_probe.lean` (`2,819` lines, SHA-256 `802f26cf0974d73ce80d89b9ea6263d9c36edc949ad3041d4c45a9b570ba9892`)

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
