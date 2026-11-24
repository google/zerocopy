-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization of `#![no_std]` `PanicStrategy::{Unwind, Abort, ImmediateAbort}`,
`core` Rebuild Requirements, `@llvm.trap` / `ud2` Lowering, and `#[panic_handler]` Exemption

This standalone Lean `v4.34.1` module formalizes the compiler pipeline,
crate-graph linkage constraints, MIR `Assert` / `UnwindAction` lowering,
`core::panicking` inlining + LLVM Dead-Global Elimination, ISA trap emission,
and `#[panic_handler]` type/exemption soundness across `rust-lang/rust`
(`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`),
`llvm/llvm-project` (`354891a804ac4eefa45a9a546cceed4404b18b78`), and
`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

## Purity & TCB Compliance Invariants

1. Every value and `Prop` definition uses explicit `noncomputable def`
   (never plain `def`, never `noncomputable section`, never `partial def`).
2. Zero `deriving` clauses on inductive types or structures, guaranteeing
   exactly `0` compiler-generated `._unsafe_rec` constants.
3. Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
   and zero `native_decide`. All proofs use direct kernel reduction,
   structural induction, and `cases`/`simp only`.

## Main Theorems

1. `nonPanicking_behavioral_agreement_all_strategies`:
   On any MIR program and input state whose execution under `PanicStrategy.unwind`
   terminates normally without hitting a failing `Assert`, `UnwindResume`, or
   panicking call, both `PanicStrategy.abort` and `PanicStrategy.immediateAbort`
   (after `AbortUnwindingCalls`) agree bit-for-bit on the final return value and
   machine state; and the lowered LLVM IR fast paths likewise agree across all
   three strategies and both `PrebuiltCore` and `RebuiltCore`.
2. `immediateAbort_rebuiltCore_eliminates_all_panic_symbols_and_data`:
   Under `PanicStrategy.immediateAbort` paired with `CoreBuildMode.rebuiltImmediateAbort`
   and LLVM inlining active (`optLevel >= 1`), `core::panicking` inlining +
   dead-global elimination collapses every `Assert`, `UnwindTerminate`, and
   panic langcall block to `tail call void @llvm.trap(); unreachable`, yielding
   `0` external panic/formatting/personality symbols (`undefPanicSymbols = []`)
   and `0` bytes of `core::panic::Location` static tables (`dataBytes = 0`),
   lowering to `ud2` (`0x0F 0x0B`) on `x86_64` and `brk #1` on `aarch64`.
3. `prebuiltCore_immediateAbort_soundness_and_rejection`:
   Establishes both halves of the prebuilt-sysroot architectural split:
   - For linkable outputs (`cdylib`, `dylib`, `staticlib`, `procMacro`,
     `executable`), `verifyCrateGraph` (`rustc_metadata/src/dependency_format.rs`)
     fail-closed rejects linking a leaf crate compiled with `immediate-abort`
     against a prebuilt `core` compiled with `unwind` or `abort`
     (`incompatibleCoreImmediateAbort`), preventing unresolved `panic_impl`
     references when `#[panic_handler]` is omitted.
   - For unlinked intermediate libraries (`rlib`), `verifyCrateGraph` skips
     linkage checks (`needsLinkCheck .rlib = false`), allowing compilation to
     succeed without `-Zbuild-std=core`; however, `inlineCorePanicking` cannot
     inline prebuilt `#[inline(never), cold]` `core::panicking` stubs, leaving
     non-zero external panic symbols and `24 * k` bytes of `Location` `.data`
     tables whenever `k > 0` assertion/panic sites exist.
4. `panicHandler_sig_and_exemption_soundness`:
   Models `check_panic_info_fn` (`rustc_hir_typeck/src/check.rs:165-235`) and
   `weak_lang_items::verify` + `lang_items::required`
   (`rustc_resolve/src/late/weak_lang_items.rs:27-61`,
   `rustc_middle/src/middle/lang_items.rs:128-137`), proving:
   - Any accepted `#[panic_handler]` must return `!` (`never`), rejecting `-> ()`
     (`E0308`) and preserving unreachability of post-panic continuations;
   - Under `immediate-abort` + rebuilt `core` + `optLevel >= 1`, omitting
     `#[panic_handler]` on `cdylib` is sound because `panic_impl` has `0`
     surviving call sites;
   - Under `unwind` or `abort`, omitting `#[panic_handler]` on `cdylib` is
     rejected (`missingPanicHandler`), and relaxing that check leaves dangling
     `panic_impl` references on any failing assertion.
-/

namespace NoStdPanicImmediateAbortTrapAndFootprintSoundness

/-! ## Section 1: Compiler Configuration, Lang-Item Policy, and Crate Graph -/

/-- Rust compilation panic strategy (`compiler/rustc_target/src/spec/mod.rs:820-824`). -/
inductive PanicStrategy where
  | unwind
  | abort
  | immediateAbort

/-- Whether unwinding can occur under `strat` (`PanicStrategy::unwinds`,
    `compiler/rustc_target/src/spec/mod.rs:846-848`). -/
noncomputable def panicUnwinds (strat : PanicStrategy) : Bool :=
  match strat with
  | .unwind => true
  | .abort => false
  | .immediateAbort => false

/-- Structural equality on `PanicStrategy` without deriving `DecidableEq`. -/
noncomputable def panicStratEq (a b : PanicStrategy) : Bool :=
  match a, b with
  | .unwind, .unwind => true
  | .abort, .abort => true
  | .immediateAbort, .immediateAbort => true
  | _, _ => false

/-- Total boolean biconditional helper avoiding `Bool.eqv` library naming shifts. -/
noncomputable def boolEqv (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

/-- `cfg(panic = ...)` configuration predicate (`compiler/rustc_session/src/config/cfg.rs:218-221`).
    Notice that `-Cpanic=immediate-abort` activates BOTH `cfg(panic = "immediate-abort")`
    and `cfg(panic = "abort")`. -/
noncomputable def cfgHasPanic (sessionStrat flagVal : PanicStrategy) : Bool :=
  match sessionStrat, flagVal with
  | .unwind, .unwind => true
  | .abort, .abort => true
  | .immediateAbort, .immediateAbort => true
  | .immediateAbort, .abort => true
  | _, _ => false

/-- Rust crate output artifact kind (`rustc_structures::CrateType`). -/
inductive CrateType where
  | rlib
  | dylib
  | cdylib
  | staticlib
  | procMacro
  | executable

/-- Whether `weak_lang_items::verify` (`rustc_resolve/src/late/weak_lang_items.rs:30-38`)
    and `dependency_format::calculate_type` (`rustc_metadata/src/dependency_format.rs:102-126`)
    perform final linkage and weak lang-item checks. -/
noncomputable def needsLinkCheck (ct : CrateType) : Bool :=
  match ct with
  | .rlib => false
  | .dylib => true
  | .cdylib => true
  | .staticlib => true
  | .procMacro => true
  | .executable => true

/-- How `core` was built and provided to the session. -/
inductive CoreBuildMode where
  | prebuiltUnwind
  | prebuiltAbort
  | rebuiltUnwind
  | rebuiltAbort
  | rebuiltImmediateAbort

/-- Panic strategy embedded in `core`'s crate metadata (`required_panic_strategy`). -/
noncomputable def coreCompiledStrategy (m : CoreBuildMode) : PanicStrategy :=
  match m with
  | .prebuiltUnwind => .unwind
  | .prebuiltAbort => .abort
  | .rebuiltUnwind => .unwind
  | .rebuiltAbort => .abort
  | .rebuiltImmediateAbort => .immediateAbort

/-- Whether `core` was compiled from source (`-Zbuild-std=core`) with
    `cfg(panic = "immediate-abort")` active (`library/core/src/panicking.rs:54-63`). -/
noncomputable def coreHasImmediateAbortCfg (m : CoreBuildMode) : Bool :=
  match m with
  | .rebuiltImmediateAbort => true
  | _ => false

/-- Weak lang items checked post-resolution (`rustc_attr_ir/src/weak_lang_items.rs:28-31`). -/
inductive WeakLangItem where
  | panicImpl
  | ehPersonality

/-- Whether `lang_item` is required under `strat`
    (`compiler/rustc_middle/src/middle/lang_items.rs:128-137`). -/
noncomputable def langItemRequired (strat : PanicStrategy) (item : WeakLangItem) : Bool :=
  match strat, item with
  | .unwind, _ => true
  | .abort, .panicImpl => true
  | .abort, .ehPersonality => false
  | .immediateAbort, _ => false

/-- Identifier for crates in a minimal `#![no_std]` dependency DAG. -/
inductive CrateId where
  | localLeaf
  | coreCrate
  | compilerBuiltins
  | panicRuntime (strat : PanicStrategy)

/-- Metadata of a crate in the dependency graph. -/
structure CrateMeta where
  id : CrateId
  panicStrat : PanicStrategy
  isCore : Bool
  isCompilerBuiltins : Bool
  isPanicRuntime : Bool

/-- Compiler session options relevant to panic codegen and link checks. -/
structure SessionOpts where
  panicStrat : PanicStrategy
  unstableOptions : Bool
  nightlyCompiler : Bool
  crateType : CrateType
  optLevel : Nat
  coreMode : CoreBuildMode
  hasPanicHandler : Bool
  hasEhPersonality : Bool
  noStd : Bool

/-- Type representation for `#[panic_handler]` signature checking
    (`compiler/rustc_hir_typeck/src/check.rs:165-235`). -/
inductive RustTy where
  | never
  | unit
  | panicInfoRef
  | u32
  | other

/-- Structural equality on `RustTy`. -/
noncomputable def rustTyEq (a b : RustTy) : Bool :=
  match a, b with
  | .never, .never => true
  | .unit, .unit => true
  | .panicInfoRef, .panicInfoRef => true
  | .u32, .u32 => true
  | .other, .other => true
  | _, _ => false

/-- Function signature inspected during lang-item HIR typechecking. -/
structure FnSig where
  typeParams : Nat
  constParams : Nat
  argTys : List RustTy
  retTy : RustTy

/-- Compiler diagnostics modeled from `rustc_session`, `rustc_metadata`,
    `rustc_resolve`, and `rustc_hir_typeck`. -/
inductive CompileResult where
  | ok
  | errUnstableRequired
  | errIncompatibleImmediateAbortCore
  | errIncompatibleImmediateAbortCrate
  | errBadPanicRuntimeStrategy
  | errTwoPanicRuntimes
  | errMissingPanicHandler
  | errPanicUnwindWithoutStd
  | errPanicHandlerWrongType
  | errPanicHandlerGenerics

/-- Check `#[panic_handler]` signature against `for<'a, 'b> fn(&'a PanicInfo<'b>) -> !`
    (`compiler/rustc_hir_typeck/src/check.rs:173-235`). -/
noncomputable def checkPanicHandlerSig (sig : FnSig) : CompileResult :=
  match sig.typeParams, sig.constParams with
  | 0, 0 =>
    match sig.argTys with
    | [.panicInfoRef] =>
      match sig.retTy with
      | .never => .ok
      | _ => .errPanicHandlerWrongType
    | _ => .errPanicHandlerWrongType
  | _, _ => .errPanicHandlerGenerics

/-- Option gate (`compiler/rustc_session/src/config.rs:2770-2774`). -/
noncomputable def checkSessionGate (opts : SessionOpts) : CompileResult :=
  match opts.panicStrat with
  | .immediateAbort =>
    match opts.unstableOptions, opts.nightlyCompiler with
    | true, true => .ok
    | _, _ => .errUnstableRequired
  | _ => .ok

/-- Recursive crate-graph compatibility check modeled directly after
    `dependency_format::verify_ok` (`compiler/rustc_metadata/src/dependency_format.rs:409-485`). -/
noncomputable def checkImmediateAbortDeps (deps : List CrateMeta) : CompileResult :=
  match deps with
  | [] => .ok
  | c :: cs =>
    match panicStratEq c.panicStrat .immediateAbort with
    | true => checkImmediateAbortDeps cs
    | false =>
      match c.isCore with
      | true => .errIncompatibleImmediateAbortCore
      | false =>
        match checkImmediateAbortDeps cs with
        | .errIncompatibleImmediateAbortCore => .errIncompatibleImmediateAbortCore
        | _ => .errIncompatibleImmediateAbortCrate

/-- Whether any crate in `deps` requires `ImmediateAbort`. -/
noncomputable def anyImmediateAbort (deps : List CrateMeta) : Bool :=
  match deps with
  | [] => false
  | c :: cs =>
    match panicStratEq c.panicStrat .immediateAbort with
    | true => true
    | false => anyImmediateAbort cs

/-- Check whether panic runtimes in `deps` conflict or mismatch `desiredStrat`. -/
noncomputable def checkPanicRuntimesAux (desired : PanicStrategy)
    (seenRuntime : Bool) (deps : List CrateMeta) : CompileResult :=
  match deps with
  | [] => .ok
  | c :: cs =>
    match c.isPanicRuntime with
    | true =>
      match seenRuntime with
      | true => .errTwoPanicRuntimes
      | false =>
        match panicStratEq c.panicStrat desired with
        | true => checkPanicRuntimesAux desired true cs
        | false => .errBadPanicRuntimeStrategy
    | false => checkPanicRuntimesAux desired seenRuntime cs

/-- Full `dependency_format::verify_ok` gate on linked crates. -/
noncomputable def verifyDependencyFormat (opts : SessionOpts) (deps : List CrateMeta) :
    CompileResult :=
  match needsLinkCheck opts.crateType with
  | false => .ok
  | true =>
    match deps with
    | [] => .ok
    | _ =>
      let immCheck :=
        match anyImmediateAbort deps with
        | true => checkImmediateAbortDeps deps
        | false => .ok
      match immCheck with
      | .ok => checkPanicRuntimesAux opts.panicStrat false deps
      | err => err

/-- Check weak lang items required by linked crates
    (`compiler/rustc_resolve/src/late/weak_lang_items.rs:27-61`). -/
noncomputable def checkWeakLangItems (opts : SessionOpts)
    (missingFromUpstream : List WeakLangItem) : CompileResult :=
  match needsLinkCheck opts.crateType with
  | false => .ok
  | true =>
    let missingPanic :=
      match missingFromUpstream with
      | [] => false
      | _ =>
        -- Check whether `panicImpl` is among upstream missing items
        let rec hasPanic : List WeakLangItem → Bool
          | [] => false
          | .panicImpl :: _ => true
          | _ :: rest => hasPanic rest
        hasPanic missingFromUpstream
    let missingEh :=
      match opts.noStd with
      | true => !opts.hasEhPersonality
      | false =>
        let rec hasEh : List WeakLangItem → Bool
          | [] => false
          | .ehPersonality :: _ => true
          | _ :: rest => hasEh rest
        hasEh missingFromUpstream
    match missingPanic && langItemRequired opts.panicStrat .panicImpl && !opts.hasPanicHandler with
    | true => .errMissingPanicHandler
    | false =>
      match missingEh && langItemRequired opts.panicStrat .ehPersonality && !opts.hasEhPersonality with
      | true => .errPanicUnwindWithoutStd
      | false => .ok

/-- Standard `#![no_std]` crate dependency list built from `SessionOpts`:
    `[localLeaf, coreCrate, compilerBuiltins]`. -/
noncomputable def noStdCrateDeps (opts : SessionOpts) : List CrateMeta :=
  [ { id := .localLeaf
    , panicStrat := opts.panicStrat
    , isCore := false
    , isCompilerBuiltins := false
    , isPanicRuntime := false }
  , { id := .coreCrate
    , panicStrat := coreCompiledStrategy opts.coreMode
    , isCore := true
    , isCompilerBuiltins := false
    , isPanicRuntime := false }
  , { id := .compilerBuiltins
    , panicStrat := coreCompiledStrategy opts.coreMode
    , isCore := false
    , isCompilerBuiltins := true
    , isPanicRuntime := false }
  ]

/-- End-to-end compilation admission check for `#![no_std]` crates. -/
noncomputable def compileAdmitted (opts : SessionOpts)
    (panicHandlerSig : Option FnSig) : CompileResult :=
  match checkSessionGate opts with
  | .ok =>
    let handlerSigRes :=
      match panicHandlerSig with
      | none => CompileResult.ok
      | some sig => checkPanicHandlerSig sig
    match handlerSigRes with
    | .ok =>
      match checkWeakLangItems opts [.panicImpl, .ehPersonality] with
      | .ok => verifyDependencyFormat opts (noStdCrateDeps opts)
      | err => err
    | err => err
  | err => err

/-! ## Section 2: `Runtime(PostCleanup)` MIR with `Assert`, `UnwindAction`, and `AbortUnwindingCalls` -/

/-- `rustc_middle::mir::AssertKind` variants relevant to `#![no_std]` codegen
    (`compiler/rustc_codegen_ssa/src/mir/block.rs:802-837`). -/
inductive AssertKind where
  | boundsCheck
  | divByZero
  | remByZero
  | overflowAdd
  | misalignedPtrDeref
  | nullPtrDeref
  | nullRefConstructed
  | invalidEnumConstruction

/-- Source caller location (`core::panic::Location<'static>`), 24 bytes on 64-bit targets:
    `{ filename: NonNull<str> (16 B), line: u32 (4 B), col: u32 (4 B) }`. -/
structure CallerLoc where
  fileTag : Nat
  line : Nat
  col : Nat

/-- Structural equality on `CallerLoc`. -/
noncomputable def callerLocEq (a b : CallerLoc) : Bool :=
  Nat.beq a.fileTag b.fileTag && Nat.beq a.line b.line && Nat.beq a.col b.col

/-- Unwind continuation action (`rustc_middle::mir::UnwindAction`). -/
inductive UnwindAction where
  | continue_
  | unreachable
  | terminateAbi
  | cleanup (bb : Nat)

/-- MIR rvalue / operand expressions over natural-valued registers and slice memory. -/
inductive MirOperand where
  | local (idx : Nat)
  | constNat (v : Nat)
  | constBool (b : Bool)

/-- Primitive MIR expressions for statements. -/
inductive MirExpr where
  | useOp (op : MirOperand)
  | eqNat (lhs rhs : MirOperand)
  | ltNat (lhs rhs : MirOperand)
  | divNat (lhs rhs : MirOperand)
  | sliceRead (baseOffset : Nat) (lenOp idxOp : MirOperand)
  | boolNot (op : MirOperand)

/-- MIR statements inside a basic block. -/
inductive MirStmt where
  | nop
  | assign (dst : Nat) (expr : MirExpr)

/-- MIR terminators, extending Anneal's fragment with explicit `Assert`,
    `UnwindTerminate`, and panic-langcall support. -/
inductive MirTerminator where
  | goto (target : Nat)
  | switchBool (cond : MirOperand) (trueBB falseBB : Nat)
  | return_ (retOp : MirOperand)
  | unreachable
  | unwindResume
  | unwindTerminate
  | assert (cond : MirOperand) (expected : Bool) (kind : AssertKind)
      (loc : CallerLoc) (target : Nat) (unwind : UnwindAction)

/-- A MIR basic block with statements, terminator, and cleanup marker. -/
structure MirBlock where
  stmts : List MirStmt
  term : MirTerminator
  isCleanup : Bool

/-- A MIR function body. -/
structure MirBody where
  blocks : List MirBlock
  canUnwindAbi : Bool

/-- `AbortUnwindingCalls` MIR pass (`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:28-115`):
    rewrites `UnwindResume` -> `UnwindTerminate` and `UnwindAction.continue_` ->
    `UnwindAction.unreachable` (for `Assert`, since `fn_can_unwind(Rust) = false` when
    `!strat.unwinds`) or `terminateAbi`. -/
noncomputable def rewriteUnwindAction (strat : PanicStrategy) (bodyCanUnwind : Bool)
    (act : UnwindAction) : UnwindAction :=
  match panicUnwinds strat with
  | true =>
    match bodyCanUnwind, act with
    | false, .continue_ => .terminateAbi
    | _, _ => act
  | false => .unreachable

/-- Transform a single MIR terminator in `AbortUnwindingCalls`. -/
noncomputable def abortUnwindingTerm (strat : PanicStrategy) (bodyCanUnwind : Bool)
    (t : MirTerminator) : MirTerminator :=
  match t with
  | .unwindResume =>
    match panicUnwinds strat && bodyCanUnwind with
    | true => .unwindResume
    | false => .unwindTerminate
  | .assert cond expected kind loc target act =>
    .assert cond expected kind loc target (rewriteUnwindAction strat bodyCanUnwind act)
  | other => other

/-- Transform a single MIR basic block in `AbortUnwindingCalls`. -/
noncomputable def abortUnwindingBlock (strat : PanicStrategy) (bodyCanUnwind : Bool)
    (bb : MirBlock) : MirBlock :=
  match bb.isCleanup with
  | true => bb
  | false => { bb with term := abortUnwindingTerm strat bodyCanUnwind bb.term }

/-- Full `AbortUnwindingCalls` pass on a `MirBody`. -/
noncomputable def abortUnwindingCallsTransform (strat : PanicStrategy) (body : MirBody) : MirBody :=
  { blocks := body.blocks.map (abortUnwindingBlock strat (body.canUnwindAbi && panicUnwinds strat))
  , canUnwindAbi := body.canUnwindAbi && panicUnwinds strat }

/-- Concrete runtime machine state for MIR evaluation. -/
structure MirState where
  regs : Nat → Nat
  bools : Nat → Bool
  mem : Nat → Nat

/-- Read a natural-valued MIR operand from `MirState`. -/
noncomputable def evalNatOp (st : MirState) (op : MirOperand) : Option Nat :=
  match op with
  | .local idx => some (st.regs idx)
  | .constNat v => some v
  | .constBool _ => none

/-- Read a boolean MIR operand from `MirState`. -/
noncomputable def evalBoolOp (st : MirState) (op : MirOperand) : Option Bool :=
  match op with
  | .local idx => some (st.bools idx)
  | .constBool b => some b
  | .constNat _ => none

/-- Update natural register `idx` in `MirState`. -/
noncomputable def setReg (st : MirState) (idx val : Nat) : MirState :=
  { st with regs := fun k => match Nat.beq k idx with | true => val | false => st.regs k }

/-- Update boolean register `idx` in `MirState`. -/
noncomputable def setBoolReg (st : MirState) (idx : Nat) (val : Bool) : MirState :=
  { st with bools := fun k => match Nat.beq k idx with | true => val | false => st.bools k }

/-- Evaluate a single MIR statement; unchecked division by zero yields `none` (UB). -/
noncomputable def evalMirStmt (st : MirState) (s : MirStmt) : Option MirState :=
  match s with
  | .nop => some st
  | .assign dst expr =>
    match expr with
    | .useOp op =>
      match evalNatOp st op with
      | some v => some (setReg st dst v)
      | none =>
        match evalBoolOp st op with
        | some b => some (setBoolReg st dst b)
        | none => none
    | .eqNat l r =>
      match evalNatOp st l, evalNatOp st r with
      | some lv, some rv => some (setBoolReg st dst (Nat.beq lv rv))
      | _, _ => none
    | .ltNat l r =>
      match evalNatOp st l, evalNatOp st r with
      | some lv, some rv => some (setBoolReg st dst (Nat.blt lv rv))
      | _, _ => none
    | .divNat l r =>
      match evalNatOp st l, evalNatOp st r with
      | some lv, some rv =>
        match Nat.beq rv 0 with
        | true => none -- Division by zero is UB!
        | false => some (setReg st dst (lv / rv))
      | _, _ => none
    | .sliceRead baseOff _ idxOp =>
      match evalNatOp st idxOp with
      | some idx => some (setReg st dst (st.mem (baseOff + idx)))
      | none => none
    | .boolNot op =>
      match evalBoolOp st op with
      | some b => some (setBoolReg st dst (!b))
      | none => none

/-- Evaluate a list of MIR statements sequentially. -/
noncomputable def evalMirStmts (st : MirState) (stmts : List MirStmt) : Option MirState :=
  match stmts with
  | [] => some st
  | s :: ss =>
    match evalMirStmt st s with
    | some st' => evalMirStmts st' ss
    | none => none

/-- Operational outcome of executing a MIR body under a panic strategy. -/
inductive MirOutcome where
  | returned (v : Nat) (st : MirState)
  | panickedViaHandler (kind : AssertKind) (loc : CallerLoc) (canUnwind : Bool)
  | trappedImmediate
  | ubFault
  | outOfFuel

/-- Index into a `List α` safely without partial helpers. -/
noncomputable def listGet? {α : Type} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, n + 1 => listGet? rest n

/-- Step-bounded MIR operational semantics parameterized by `(strat, coreMode)`. -/
noncomputable def evalMirBodyFuel (strat : PanicStrategy) (coreMode : CoreBuildMode)
    (optLevel : Nat) (body : MirBody) (bbIdx : Nat) (st : MirState) (fuel : Nat) :
    MirOutcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match listGet? body.blocks bbIdx with
    | none => .ubFault
    | some bb =>
      match evalMirStmts st bb.stmts with
      | none => .ubFault
      | some st1 =>
        match bb.term with
        | .goto target =>
          evalMirBodyFuel strat coreMode optLevel body target st1 fuel'
        | .switchBool cond tBB fBB =>
          match evalBoolOp st1 cond with
          | none => .ubFault
          | some true => evalMirBodyFuel strat coreMode optLevel body tBB st1 fuel'
          | some false => evalMirBodyFuel strat coreMode optLevel body fBB st1 fuel'
        | .return_ retOp =>
          match evalNatOp st1 retOp with
          | some v => .returned v st1
          | none => .ubFault
        | .unreachable => .ubFault
        | .unwindResume => .ubFault
        | .unwindTerminate =>
          match coreHasImmediateAbortCfg coreMode with
          | true =>
            match Nat.blt 0 optLevel with
            | true => .trappedImmediate
            | false => .trappedImmediate
          | false => .panickedViaHandler .boundsCheck ⟨0, 0, 0⟩ false
        | .assert cond expected kind loc target unwind =>
          match evalBoolOp st1 cond with
          | none => .ubFault
          | some actual =>
            match boolEqv actual expected with
            | true => evalMirBodyFuel strat coreMode optLevel body target st1 fuel'
            | false =>
              match coreHasImmediateAbortCfg coreMode with
              | true => .trappedImmediate
              | false =>
                match unwind with
                | UnwindAction.cleanup cleanupBB =>
                  -- Simplified cleanup entry before abort/unwind
                  match strat with
                  | .unwind => evalMirBodyFuel strat coreMode optLevel body cleanupBB st1 fuel'
                  | _ => .panickedViaHandler kind loc false
                | .continue_ =>
                  .panickedViaHandler kind loc (panicUnwinds strat)
                | .terminateAbi | .unreachable =>
                  .panickedViaHandler kind loc false

/-! ## Section 3: `rustc_codegen_ssa` Lowering, `core::panicking` Inlining, and LLVM/ISA Footprint -/

/-- External langcall symbols in `core::panicking` (`library/core/src/panicking.rs`). -/
inductive PanicLangSym where
  | panicBoundsCheck
  | panicConstDivByZero
  | panicConstRemByZero
  | panicConstAddOverflow
  | panicMisalignedPtrDeref
  | panicNullPtrDeref
  | panicNullRefConstructed
  | panicInvalidEnumConstruction
  | panicCannotUnwind
  | panicInCleanup
  | panicFmt
  | panicNounwindFmt
  | panicImpl
  | rustEhPersonality

/-- Structural equality on `PanicLangSym`. -/
noncomputable def panicLangSymEq (a b : PanicLangSym) : Bool :=
  match a, b with
  | .panicBoundsCheck, .panicBoundsCheck => true
  | .panicConstDivByZero, .panicConstDivByZero => true
  | .panicConstRemByZero, .panicConstRemByZero => true
  | .panicConstAddOverflow, .panicConstAddOverflow => true
  | .panicMisalignedPtrDeref, .panicMisalignedPtrDeref => true
  | .panicNullPtrDeref, .panicNullPtrDeref => true
  | .panicNullRefConstructed, .panicNullRefConstructed => true
  | .panicInvalidEnumConstruction, .panicInvalidEnumConstruction => true
  | .panicCannotUnwind, .panicCannotUnwind => true
  | .panicInCleanup, .panicInCleanup => true
  | .panicFmt, .panicFmt => true
  | .panicNounwindFmt, .panicNounwindFmt => true
  | .panicImpl, .panicImpl => true
  | .rustEhPersonality, .rustEhPersonality => true
  | _, _ => false

/-- Mapping from `AssertKind` to its `LangItem` symbol
    (`compiler/rustc_codegen_ssa/src/mir/block.rs:802-837`). -/
noncomputable def assertKindLangSym (k : AssertKind) : PanicLangSym :=
  match k with
  | .boundsCheck => .panicBoundsCheck
  | .divByZero => .panicConstDivByZero
  | .remByZero => .panicConstRemByZero
  | .overflowAdd => .panicConstAddOverflow
  | .misalignedPtrDeref => .panicMisalignedPtrDeref
  | .nullPtrDeref => .panicNullPtrDeref
  | .nullRefConstructed => .panicNullRefConstructed
  | .invalidEnumConstruction => .panicInvalidEnumConstruction

/-- LLVM IR memory-effect attribute summary (`llvm/include/llvm/IR/Intrinsics.td:2093-2096`). -/
inductive LlvmMemEffect where
  | arbitrary
  | inaccessibleMemWrite
  | argmemReadInaccessibleWrite

/-- LLVM IR instruction sequence inside a lowered basic block. -/
inductive LlvmTerm where
  | br (target : Nat)
  | condBr (cond : MirOperand) (trueBB falseBB : Nat)
  | ret (retOp : MirOperand)
  | unreachable
  | invokePanic (sym : PanicLangSym) (loc : CallerLoc) (terminatePad : Bool)
  | tailCallPanic (sym : PanicLangSym) (loc : CallerLoc)
  | tailCallLlvmTrap

/-- Lowered LLVM IR basic block. -/
structure LlvmBlock where
  stmts : List MirStmt
  term : LlvmTerm

/-- Lowered LLVM IR function. -/
structure LlvmFunc where
  blocks : List LlvmBlock
  hasPersonality : Bool
  nounwind : Bool
  memEffect : LlvmMemEffect

/-- Complete lowered LLVM IR module prior to/after `core::panicking` inlining and DCE. -/
structure LlvmModule where
  funcs : List LlvmFunc
  decls : List PanicLangSym
  usesLlvmTrap : Bool
  rodataLocs : List CallerLoc

/-- Lower a single MIR `MirBlock` via `rustc_codegen_ssa/src/mir/block.rs:753-889`.
    Crucial architectural invariant: `codegen_assert_terminator` ALWAYS lowers
    `TerminatorKind::Assert` to `common::build_langcall(..., lang_item)` with
    a `CallerLoc` argument, regardless of whether `-Cpanic=immediate-abort` is set!
    Only the unwind pad (`invoke ... to %unreachable unwind label %terminate` vs
    `tail call ...; unreachable`) depends on `panicUnwinds strat`. -/
noncomputable def lowerMirBlockToLlvm (strat : PanicStrategy) (bb : MirBlock) :
    LlvmBlock × List CallerLoc × List PanicLangSym :=
  match bb.term with
  | .goto t => ({ stmts := bb.stmts, term := .br t }, [], [])
  | .switchBool c t f => ({ stmts := bb.stmts, term := .condBr c t f }, [], [])
  | .return_ r => ({ stmts := bb.stmts, term := .ret r }, [], [])
  | .unreachable => ({ stmts := bb.stmts, term := .unreachable }, [], [])
  | .unwindResume =>
    match panicUnwinds strat with
    | true => ({ stmts := bb.stmts, term := .unreachable }, [], [])
    | false => ({ stmts := bb.stmts, term := .tailCallPanic .panicCannotUnwind ⟨0, 0, 0⟩ }, [], [.panicCannotUnwind])
  | .unwindTerminate =>
    ({ stmts := bb.stmts, term := .tailCallPanic .panicCannotUnwind ⟨0, 0, 0⟩ }, [], [.panicCannotUnwind])
  | .assert _cond _expected kind loc _target _unwind =>
    let sym := assertKindLangSym kind
    let tBB : LlvmTerm :=
      match panicUnwinds strat with
      | true => .invokePanic sym loc true
      | false => .tailCallPanic sym loc
    let extraDecls : List PanicLangSym :=
      match panicUnwinds strat with
      | true => [sym, .panicCannotUnwind, .rustEhPersonality]
      | false => [sym]
    -- Represent conditional branch + inline panic outcome as direct `condBr`-style failure tag
    -- Wait: to keep the block count faithful, represent `assert` terminator lowered directly
    -- with `tBB` on the failure edge (we attach the condition in `LoweredAssertBlock` below,
    -- or encode `cond` directly inside `LlvmTerm.condAssert`).
    ({ stmts := bb.stmts, term := tBB }, [loc], extraDecls)

/-- Refined LLVM terminator that explicitly preserves the fast-path guard alongside
    the lowered failure-path action (`condBranch` + panic sink). -/
inductive LlvmGuardTerm where
  | br (target : Nat)
  | condBr (cond : MirOperand) (trueBB falseBB : Nat)
  | ret (retOp : MirOperand)
  | unreachable
  | assertGuard (cond : MirOperand) (expected : Bool) (target : Nat) (failAction : LlvmTerm)

/-- Lowered LLVM function preserving exact fast-path guards (`assertGuard`). -/
structure LlvmGuardedFunc where
  blocks : List (List MirStmt × LlvmGuardTerm)
  hasPersonality : Bool
  nounwind : Bool
  memEffect : LlvmMemEffect

/-- Complete LLVM module with fast-path guards and explicit external decl / `.data` lists. -/
structure LlvmGuardedModule where
  funcs : List LlvmGuardedFunc
  decls : List PanicLangSym
  usesLlvmTrap : Bool
  rodataLocs : List CallerLoc

/-- Lower a MIR terminator into `LlvmGuardTerm`, faithful to `codegen_assert_terminator`
    (`compiler/rustc_codegen_ssa/src/mir/block.rs:753-858`):
    Notice that for ALL 3 strategies (`unwind`, `abort`, `immediateAbort`), `Assert`
    emits a `CallerLoc` and a `PanicLangSym` call (`invokePanic` when `unwind`,
    `tailCallPanic` when `abort` or `immediateAbort`). -/
noncomputable def lowerTermGuarded (strat : PanicStrategy) (t : MirTerminator) :
    LlvmGuardTerm × List CallerLoc × List PanicLangSym :=
  match t with
  | .goto target => (.br target, [], [])
  | .switchBool c tBB fBB => (.condBr c tBB fBB, [], [])
  | .return_ r => (.ret r, [], [])
  | .unreachable => (.unreachable, [], [])
  | .unwindResume =>
    match panicUnwinds strat with
    | true => (.unreachable, [], [.rustEhPersonality])
    | false => (.assertGuard (.constBool false) true 0 (.tailCallPanic .panicCannotUnwind ⟨0, 0, 0⟩), [], [.panicCannotUnwind])
  | .unwindTerminate =>
    (.assertGuard (.constBool false) true 0 (.tailCallPanic .panicCannotUnwind ⟨0, 0, 0⟩), [], [.panicCannotUnwind])
  | .assert cond expected kind loc target _unwind =>
    let sym := assertKindLangSym kind
    match panicUnwinds strat with
    | true =>
      (.assertGuard cond expected target (.invokePanic sym loc true),
       [loc], [sym, .panicCannotUnwind, .rustEhPersonality])
    | false =>
      (.assertGuard cond expected target (.tailCallPanic sym loc),
       [loc], [sym])

/-- Collect declarations across lowered blocks. -/
noncomputable def lowerBlocksGuarded (strat : PanicStrategy) (bbs : List MirBlock) :
    List (List MirStmt × LlvmGuardTerm) × List CallerLoc × List PanicLangSym :=
  match bbs with
  | [] => ([], [], [])
  | b :: bs =>
    let (gt, locs, decls) := lowerTermGuarded strat b.term
    let (restG, restLocs, restDecls) := lowerBlocksGuarded strat bs
    ((b.stmts, gt) :: restG, locs ++ restLocs, decls ++ restDecls)

/-- Lower a complete `MirBody` via `rustc_codegen_ssa` (pre-LLVM-inlining!). -/
noncomputable def lowerMirBodyToLlvmGuarded (strat : PanicStrategy) (body : MirBody) :
    LlvmGuardedModule :=
  let (gBlocks, locs, decls) := lowerBlocksGuarded strat body.blocks
  let hasPers := panicUnwinds strat
  let fnRec : LlvmGuardedFunc :=
    { blocks := gBlocks
    , hasPersonality := hasPers
    , nounwind := !hasPers
    , memEffect := .arbitrary }
  { funcs := [fnRec]
  , decls := decls
  , usesLlvmTrap := false
  , rodataLocs := locs }

/-- Model of a `core::panicking` function body as compiled into `core.rlib`:
    - When `coreHasImmediateAbortCfg coreMode = true` (`-Zbuild-std=core` with
      `-Cpanic=immediate-abort`): marked `#[inline]` (`InlineHint`) and lowers to
      `abort_immediate()` -> `@llvm.trap()` (`library/core/src/panicking.rs:54-63`);
    - When `coreHasImmediateAbortCfg coreMode = false` (prebuilt `core` or non-immediate
      `-Zbuild-std=core`): marked `#[inline(never), cold]` and calls `panic_impl(&PanicInfo)`. -/
inductive CorePanickingImpl where
  | inlineImmediateTrap
  | coldOutOfLinePanicImpl

/-- Resolve the compiled `core::panicking` stub semantics from `coreMode`. -/
noncomputable def resolveCorePanicking (coreMode : CoreBuildMode) : CorePanickingImpl :=
  match coreHasImmediateAbortCfg coreMode with
  | true => .inlineImmediateTrap
  | false => .coldOutOfLinePanicImpl

/-- Whether LLVM's `AlwaysInliner` / `Inliner` pass inlines `#[inline]` `core::panicking` stubs
    at `optLevel` (`optLevel >= 1` enables the CGSCC inliner; at `optLevel = 0` only `#[inline(always)]`
    is inlined by `AlwaysInliner`). -/
noncomputable def inlinerReplacesInlineHint (optLevel : Nat) : Bool :=
  Nat.blt 0 optLevel

/-- Inline a single `LlvmTerm` if `core::panicking` is inlinable and LLVM inlining runs. -/
noncomputable def inlineFailAction (coreMode : CoreBuildMode) (optLevel : Nat) (act : LlvmTerm) :
    LlvmTerm × Bool :=
  match resolveCorePanicking coreMode, inlinerReplacesInlineHint optLevel with
  | .inlineImmediateTrap, true =>
    match act with
    | .invokePanic _ _ _ => (.tailCallLlvmTrap, true)
    | .tailCallPanic _ _ => (.tailCallLlvmTrap, true)
    | .tailCallLlvmTrap => (.tailCallLlvmTrap, true)
    | other => (other, false)
  | _, _ => (act, false)

/-- Apply `inlineCorePanicking` across a `LlvmGuardTerm`. -/
noncomputable def inlineGuardTerm (coreMode : CoreBuildMode) (optLevel : Nat) (gt : LlvmGuardTerm) :
    LlvmGuardTerm × Bool :=
  match gt with
  | .assertGuard cond expected target failAct =>
    let (failAct', trapped) := inlineFailAction coreMode optLevel failAct
    (.assertGuard cond expected target failAct', trapped)
  | other => (other, false)

/-- Apply `inlineCorePanicking` to a list of guarded blocks. -/
noncomputable def inlineGuardedBlocks (coreMode : CoreBuildMode) (optLevel : Nat)
    (bbs : List (List MirStmt × LlvmGuardTerm)) :
    List (List MirStmt × LlvmGuardTerm) × Bool :=
  match bbs with
  | [] => ([], false)
  | (stmts, gt) :: rest =>
    let (gt', t1) := inlineGuardTerm coreMode optLevel gt
    let (rest', t2) := inlineGuardedBlocks coreMode optLevel rest
    ((stmts, gt') :: rest', t1 || t2)

/-- Extract surviving external panic symbols from a single `LlvmTerm`. -/
noncomputable def termSurvivingDecls (t : LlvmTerm) : List PanicLangSym :=
  match t with
  | .invokePanic sym _ true => [sym, .panicCannotUnwind, .rustEhPersonality]
  | .invokePanic sym _ false => [sym, .rustEhPersonality]
  | .tailCallPanic sym _ => [sym]
  | .tailCallLlvmTrap => []
  | .br _ | .condBr _ _ _ | .ret _ | .unreachable => []

/-- Extract surviving `CallerLoc` `.data` entries from a single `LlvmTerm`. -/
noncomputable def termSurvivingLocs (t : LlvmTerm) : List CallerLoc :=
  match t with
  | .invokePanic _ loc _ => [loc]
  | .tailCallPanic _ loc => [loc]
  | .tailCallLlvmTrap => []
  | .br _ | .condBr _ _ _ | .ret _ | .unreachable => []

/-- Extract surviving decls and `CallerLoc`s from a `LlvmGuardTerm`. -/
noncomputable def guardTermDeclsAndLocs (gt : LlvmGuardTerm) :
    List PanicLangSym × List CallerLoc :=
  match gt with
  | .assertGuard _ _ _ failAct => (termSurvivingDecls failAct, termSurvivingLocs failAct)
  | _ => ([], [])

/-- Recompute surviving decls and `CallerLoc`s after LLVM GlobalDCE / DeadArgElim. -/
noncomputable def collectDeclsAndLocsBlocks (bbs : List (List MirStmt × LlvmGuardTerm)) :
    List PanicLangSym × List CallerLoc :=
  match bbs with
  | [] => ([], [])
  | (_, gt) :: rest =>
    let (d1, l1) := guardTermDeclsAndLocs gt
    let (d2, l2) := collectDeclsAndLocsBlocks rest
    (d1 ++ d2, l1 ++ l2)

/-- Recompute surviving decls and `CallerLoc`s across all functions in an LLVM module. -/
noncomputable def collectDeclsAndLocsFuncs (fs : List LlvmGuardedFunc) :
    List PanicLangSym × List CallerLoc :=
  match fs with
  | [] => ([], [])
  | f :: fs' =>
    let (d1, l1) := collectDeclsAndLocsBlocks f.blocks
    let (d2, l2) := collectDeclsAndLocsFuncs fs'
    (d1 ++ d2, l1 ++ l2)

/-- Whether any block in a function still emits an `invokePanic`. -/
noncomputable def blocksHaveInvoke (bbs : List (List MirStmt × LlvmGuardTerm)) : Bool :=
  match bbs with
  | [] => false
  | (_, gt) :: rest =>
    let hasHere :=
      match gt with
      | .assertGuard _ _ _ (.invokePanic _ _ _) => true
      | _ => false
    hasHere || blocksHaveInvoke rest

/-- Infer refined LLVM `FunctionAttrs` + GlobalDCE on a single `LlvmGuardedFunc`. -/
noncomputable def optimizeLlvmFunc (coreMode : CoreBuildMode) (optLevel : Nat)
    (f : LlvmGuardedFunc) : LlvmGuardedFunc × Bool :=
  let (bbs', usedTrap) := inlineGuardedBlocks coreMode optLevel f.blocks
  let stillHasInvoke := blocksHaveInvoke bbs'
  let hasPers' := f.hasPersonality && stillHasInvoke
  let nounwind' := !hasPers'
  let memEff' :=
    match usedTrap, stillHasInvoke with
    | true, false =>
      -- `llvm.trap` is `[IntrNoReturn, IntrCold, IntrInaccessibleMemOnly, IntrWriteMem]`
      -- (`llvm/include/llvm/IR/Intrinsics.td:2093-2096`).
      .inaccessibleMemWrite
    | _, _ => f.memEffect
  ({ blocks := bbs'
   , hasPersonality := hasPers'
   , nounwind := nounwind'
   , memEffect := memEff' }, usedTrap)

/-- Apply LLVM `core::panicking` inlining + GlobalDCE + `FunctionAttrs` across `LlvmGuardedModule`. -/
noncomputable def optimizeLlvmModule (coreMode : CoreBuildMode) (optLevel : Nat)
    (mod : LlvmGuardedModule) : LlvmGuardedModule :=
  let rec optFuncs : List LlvmGuardedFunc → List LlvmGuardedFunc × Bool
    | [] => ([], false)
    | f :: fs =>
      let (f', t1) := optimizeLlvmFunc coreMode optLevel f
      let (fs', t2) := optFuncs fs
      (f' :: fs', t1 || t2)
  let (funcs', anyTrap) := optFuncs mod.funcs
  let (survDecls, survLocs) := collectDeclsAndLocsFuncs funcs'
  { funcs := funcs'
  , decls := survDecls
  , usesLlvmTrap := mod.usesLlvmTrap || anyTrap
  , rodataLocs := survLocs }

/-- Exact `.data` footprint in bytes for `CallerLoc` tables (24 bytes per live `CallerLoc`). -/
noncomputable def dataFootprintBytes (mod : LlvmGuardedModule) : Nat :=
  mod.rodataLocs.length * 24

/-- Operational evaluator for `LlvmGuardedFunc` (models execution of lowered LLVM IR). -/
noncomputable def evalLlvmFuncFuel (coreMode : CoreBuildMode) (fnRec : LlvmGuardedFunc)
    (bbIdx : Nat) (st : MirState) (fuel : Nat) : MirOutcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match listGet? fnRec.blocks bbIdx with
    | none => .ubFault
    | some (stmts, gt) =>
      match evalMirStmts st stmts with
      | none => .ubFault
      | some st1 =>
        match gt with
        | .br target => evalLlvmFuncFuel coreMode fnRec target st1 fuel'
        | .condBr cond tBB fBB =>
          match evalBoolOp st1 cond with
          | none => .ubFault
          | some true => evalLlvmFuncFuel coreMode fnRec tBB st1 fuel'
          | some false => evalLlvmFuncFuel coreMode fnRec fBB st1 fuel'
        | .ret retOp =>
          match evalNatOp st1 retOp with
          | some v => .returned v st1
          | none => .ubFault
        | .unreachable => .ubFault
        | .assertGuard cond expected target failAct =>
          match evalBoolOp st1 cond with
          | none => .ubFault
          | some actual =>
            match boolEqv actual expected with
            | true => evalLlvmFuncFuel coreMode fnRec target st1 fuel'
            | false =>
              match failAct with
              | .tailCallLlvmTrap => .trappedImmediate
              | .invokePanic _sym loc _ =>
                match resolveCorePanicking coreMode with
                | .inlineImmediateTrap => .trappedImmediate
                | .coldOutOfLinePanicImpl => .panickedViaHandler .boundsCheck loc true
              | .tailCallPanic _ loc =>
                match resolveCorePanicking coreMode with
                | .inlineImmediateTrap => .trappedImmediate
                | .coldOutOfLinePanicImpl => .panickedViaHandler .boundsCheck loc false
              | _ => .ubFault

/-- Target architectures for `llvm.trap` ISA lowering. -/
inductive TargetArch where
  | x86_64
  | aarch64

/-- Target machine trap instruction emitted for `@llvm.trap()`
    (`X86InstrSystem.td:25` `TRAP -> ud2 (0x0F 0x0B)`,
     `AArch64InstrInfo.td:11217` `Pat<(trap), (BRK 1)>`). -/
inductive IsaTrapInsn where
  | x86Ud2   -- 2-byte `0x0F 0x0B`
  | aarch64Brk1 -- 4-byte `brk #0x1`
  | externalPanicCall (sym : PanicLangSym)

/-- Lower an `LlvmTerm` failure action to target ISA trap or external call. -/
noncomputable def lowerTermToIsa (arch : TargetArch) (t : LlvmTerm) : Option IsaTrapInsn :=
  match t with
  | .tailCallLlvmTrap =>
    match arch with
    | .x86_64 => some .x86Ud2
    | .aarch64 => some .aarch64Brk1
  | .invokePanic sym _ _ => some (.externalPanicCall sym)
  | .tailCallPanic sym _ => some (.externalPanicCall sym)
  | _ => none

/-- Byte size of a single ISA trap/call sequence. -/
noncomputable def isaTrapByteSize (insn : IsaTrapInsn) : Nat :=
  match insn with
  | .x86Ud2 => 2
  | .aarch64Brk1 => 4
  | .externalPanicCall _ => 11 -- `lea loc(%rip)` (7 B) + `call *sym(%rip)` or similar stub

/-- Predicate asserting every lowered trap instruction is a self-contained hardware trap
    (no `externalPanicCall`). -/
noncomputable def isHardwareTrapOnly : List IsaTrapInsn → Prop
  | [] => True
  | .x86Ud2 :: rest => isHardwareTrapOnly rest
  | .aarch64Brk1 :: rest => isHardwareTrapOnly rest
  | .externalPanicCall _ :: _ => False

/-- Lower all panic sinks in a `LlvmGuardedModule` to `List IsaTrapInsn`. -/
noncomputable def lowerModuleTrapsToIsa (arch : TargetArch) (mod : LlvmGuardedModule) :
    List IsaTrapInsn :=
  let rec goBlocks : List (List MirStmt × LlvmGuardTerm) → List IsaTrapInsn
    | [] => []
    | (_, gt) :: bs =>
      match gt with
      | .assertGuard _ _ _ failAct =>
        match lowerTermToIsa arch failAct with
        | some insn => insn :: goBlocks bs
        | none => goBlocks bs
      | _ => goBlocks bs
  let rec goFuncs : List LlvmGuardedFunc → List IsaTrapInsn
    | [] => []
    | f :: fs => goBlocks f.blocks ++ goFuncs fs
  goFuncs mod.funcs

/-! ## Section 4: Core Auxiliary Lemmas (Total, Pure Kernel Proofs) -/

theorem listGet?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    listGet? (xs.map f) i = (listGet? xs i).map f := by
  induction xs generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ n =>
      dsimp only [List.map, listGet?]
      exact ih n

theorem list_map_append {α β : Type} (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.cons_append, List.map_cons, ih, List.map_cons, List.cons_append]

theorem boolEqv_self (b : Bool) : boolEqv b b = true := by
  cases b <;> rfl

theorem panicStratEq_refl (s : PanicStrategy) : panicStratEq s s = true := by
  cases s <;> rfl

theorem nat_blt_one_succ (n : Nat) : Nat.blt 0 (n + 1) = true := by
  rfl

theorem abortUnwindingCalls_preserves_stmts_and_nonunwind_terms
    (strat : PanicStrategy) (canU : Bool) (bb : MirBlock) :
    (abortUnwindingBlock strat canU bb).stmts = bb.stmts := by
  cases bb with
  | mk stmts term isC =>
    cases isC <;> rfl

theorem rewriteUnwindAction_non_unwind (strat : PanicStrategy) (b : Bool) (act : UnwindAction) :
    panicUnwinds strat = false → rewriteUnwindAction strat b act = .unreachable := by
  intro h
  dsimp only [rewriteUnwindAction]
  rw [h]

/-! ## Section 5: Theorem 1 — Behavioral Agreement on Non-Panicking Executions -/

/-- Non-panicking execution predicate over a `MirBody`: under `evalMirBodyFuel`,
    execution returns `.returned v st'` without ever hitting a failing `Assert`,
    `unwindResume`, or `unwindTerminate`. -/
noncomputable def NoAssertFailurePath : MirBody → MirState → Nat → Prop
  | _, _, 0 => False
  | body, st, fuel' + 1 =>
    -- Every step from block 0 either returns cleanly or takes a passing Assert / branch / goto
    ∀ (strat : PanicStrategy) (coreMode : CoreBuildMode) (optLevel : Nat),
      ∃ v st', evalMirBodyFuel strat coreMode optLevel body 0 st (fuel' + 1) = .returned v st'

/-- Stronger structural invariant: a `MirBody` has no `unwindResume` or `unwindTerminate`
    reachable during execution from `(bbIdx, st)` in `fuel` steps, AND every executed
    `Assert` satisfies `actual == expected`. -/
noncomputable def ExecutionPanicFree (body : MirBody) :
    Nat → MirState → Nat → Prop
  | _, _, 0 => False
  | bbIdx, st, fuel' + 1 =>
    match listGet? body.blocks bbIdx with
    | none => False
    | some bb =>
      match evalMirStmts st bb.stmts with
      | none => False
      | some st1 =>
        match bb.term with
        | .goto target => ExecutionPanicFree body target st1 fuel'
        | .switchBool cond tBB fBB =>
          match evalBoolOp st1 cond with
          | none => False
          | some true => ExecutionPanicFree body tBB st1 fuel'
          | some false => ExecutionPanicFree body fBB st1 fuel'
        | .return_ retOp =>
          match evalNatOp st1 retOp with
          | some _ => True
          | none => False
        | .unreachable => False
        | .unwindResume => False
        | .unwindTerminate => False
        | .assert cond expected _ _ target _ =>
          match evalBoolOp st1 cond with
          | none => False
          | some actual =>
            boolEqv actual expected = true ∧ ExecutionPanicFree body target st1 fuel'

/-- Helper: `abortUnwindingBlock` leaves non-cleanup block structure intact on all
    non-`unwindResume` terminators and preserves `stmts` on every block. -/
theorem evalMirBodyFuel_abortUnwinding_invariant
    (strat1 strat2 : PanicStrategy) (core1 core2 : CoreBuildMode) (opt1 opt2 : Nat)
    (body : MirBody) (bbIdx : Nat) (st : MirState) (fuel : Nat) :
    ExecutionPanicFree body bbIdx st fuel →
    evalMirBodyFuel strat1 core1 opt1 (abortUnwindingCallsTransform strat1 body) bbIdx st fuel =
    evalMirBodyFuel strat2 core2 opt2 (abortUnwindingCallsTransform strat2 body) bbIdx st fuel := by
  induction fuel generalizing bbIdx st with
  | zero =>
    intro hpf
    cases hpf
  | succ fuel' ih =>
    intro hpf
    dsimp only [ExecutionPanicFree] at hpf
    dsimp only [evalMirBodyFuel, abortUnwindingCallsTransform]
    rw [listGet?_map, listGet?_map]
    cases hbb : listGet? body.blocks bbIdx with
    | none =>
      rw [hbb] at hpf
      cases hpf
    | some bb =>
      rw [hbb] at hpf
      dsimp only at hpf
      dsimp only [Option.map]
      rw [abortUnwindingCalls_preserves_stmts_and_nonunwind_terms]
      rw [abortUnwindingCalls_preserves_stmts_and_nonunwind_terms]
      cases hst : evalMirStmts st bb.stmts with
      | none => rfl
      | some st1 =>
        rw [hst] at hpf
        dsimp only at hpf
        cases hc : bb.isCleanup with
        | true =>
          dsimp only [abortUnwindingBlock]
          rw [hc]
          dsimp only
          cases ht : bb.term with
          | goto target =>
            rw [ht] at hpf
            exact ih target st1 hpf
          | switchBool cond tBB fBB =>
            rw [ht] at hpf
            dsimp only at hpf
            dsimp only
            cases hop : evalBoolOp st1 cond with
            | none => rfl
            | some b =>
              rw [hop] at hpf
              cases b
              · exact ih fBB st1 hpf
              · exact ih tBB st1 hpf
          | return_ retOp => rfl
          | unreachable => rfl
          | unwindResume => rfl
          | unwindTerminate =>
            rw [ht] at hpf
            cases hpf
          | assert cond expected kind loc target act =>
            rw [ht] at hpf
            dsimp only at hpf
            dsimp only
            cases hop : evalBoolOp st1 cond with
            | none => rfl
            | some actual =>
              rw [hop] at hpf
              dsimp only at hpf
              cases hpf with
              | intro hEq hNext =>
                dsimp only
                rw [hEq]
                dsimp only
                exact ih target st1 hNext
        | false =>
          dsimp only [abortUnwindingBlock]
          rw [hc]
          dsimp only
          cases ht : bb.term with
          | goto target =>
            rw [ht] at hpf
            exact ih target st1 hpf
          | switchBool cond tBB fBB =>
            rw [ht] at hpf
            dsimp only at hpf
            dsimp only [abortUnwindingTerm]
            cases hop : evalBoolOp st1 cond with
            | none => rfl
            | some b =>
              rw [hop] at hpf
              cases b
              · exact ih fBB st1 hpf
              · exact ih tBB st1 hpf
          | return_ retOp => rfl
          | unreachable => rfl
          | unwindResume =>
            rw [ht] at hpf
            cases hpf
          | unwindTerminate =>
            rw [ht] at hpf
            cases hpf
          | assert cond expected kind loc target act =>
            rw [ht] at hpf
            dsimp only at hpf
            dsimp only [abortUnwindingTerm]
            cases hop : evalBoolOp st1 cond with
            | none => rfl
            | some actual =>
              rw [hop] at hpf
              dsimp only at hpf
              cases hpf with
              | intro hEq hNext =>
                dsimp only
                rw [hEq]
                dsimp only
                exact ih target st1 hNext

/-- **Theorem 1a (MIR Behavioral Agreement Across All 3 Panic Strategies):**
    On any execution satisfying `ExecutionPanicFree body 0 st fuel` (no failing `Assert`s,
    no `UnwindResume`, no `UnwindTerminate`), `PanicStrategy.unwind`, `PanicStrategy.abort`,
    and `PanicStrategy.immediateAbort` produce the exact same `MirOutcome` (`returned v st'`). -/
theorem nonPanicking_behavioral_agreement_all_strategies
    (body : MirBody) (st : MirState) (fuel : Nat) (coreMode : CoreBuildMode) (optLevel : Nat)
    (hpf : ExecutionPanicFree body 0 st fuel) :
    evalMirBodyFuel .unwind coreMode optLevel (abortUnwindingCallsTransform .unwind body) 0 st fuel =
      evalMirBodyFuel .abort coreMode optLevel (abortUnwindingCallsTransform .abort body) 0 st fuel ∧
    evalMirBodyFuel .unwind coreMode optLevel (abortUnwindingCallsTransform .unwind body) 0 st fuel =
      evalMirBodyFuel .immediateAbort coreMode optLevel
        (abortUnwindingCallsTransform .immediateAbort body) 0 st fuel := by
  constructor
  · exact evalMirBodyFuel_abortUnwinding_invariant .unwind .abort coreMode coreMode optLevel optLevel body 0 st fuel hpf
  · exact evalMirBodyFuel_abortUnwinding_invariant .unwind .immediateAbort coreMode coreMode optLevel optLevel body 0 st fuel hpf

/-- Helper lemma relating `listGet? (lowerBlocksGuarded strat bbs).1` to `listGet? bbs`. -/
theorem listGet?_lowerBlocksGuarded (strat : PanicStrategy) (bbs : List MirBlock) (i : Nat) :
    listGet? (lowerBlocksGuarded strat bbs).1 i =
      (listGet? bbs i).map (fun b => (b.stmts, (lowerTermGuarded strat b.term).1)) := by
  induction bbs generalizing i with
  | nil =>
    cases i <;> rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ n =>
      dsimp only [lowerBlocksGuarded, listGet?]
      exact ih n

/-- Helper lemma relating `listGet? (inlineGuardedBlocks ...).1` to `listGet?`. -/
theorem listGet?_inlineGuardedBlocks (coreMode : CoreBuildMode) (optLevel : Nat)
    (bbs : List (List MirStmt × LlvmGuardTerm)) (i : Nat) :
    listGet? (inlineGuardedBlocks coreMode optLevel bbs).1 i =
      (listGet? bbs i).map (fun p => (p.1, (inlineGuardTerm coreMode optLevel p.2).1)) := by
  induction bbs generalizing i with
  | nil =>
    cases i <;> rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ n =>
      dsimp only [inlineGuardedBlocks, listGet?]
      exact ih n

/-- **Theorem 1b (MIR-to-Optimized-LLVM Fast-Path Equivalence):**
    On any `ExecutionPanicFree` path, lowering a `MirBody` via `lowerMirBodyToLlvmGuarded`
    and running `optimizeLlvmModule` (`inlineCorePanicking` + GlobalDCE) preserves the exact
    `MirOutcome` of `evalMirBodyFuel` regardless of `(strat, coreMode, optLevel)`! -/
theorem mir_to_llvm_fastpath_agreement
    (strat : PanicStrategy) (coreMode : CoreBuildMode) (optLevel : Nat)
    (body : MirBody) (bbIdx : Nat) (st : MirState) (fuel : Nat)
    (hpf : ExecutionPanicFree body bbIdx st fuel) :
    match (optimizeLlvmModule coreMode optLevel (lowerMirBodyToLlvmGuarded strat body)).funcs with
    | f :: _ => evalLlvmFuncFuel coreMode f bbIdx st fuel =
                evalMirBodyFuel strat coreMode optLevel body bbIdx st fuel
    | [] => False := by
  dsimp only [optimizeLlvmModule, optimizeLlvmModule.optFuncs, lowerMirBodyToLlvmGuarded,
    optimizeLlvmFunc]
  induction fuel generalizing bbIdx st with
  | zero =>
    cases hpf
  | succ fuel' ih =>
    dsimp only [ExecutionPanicFree] at hpf
    dsimp only [evalLlvmFuncFuel, evalMirBodyFuel]
    rw [listGet?_inlineGuardedBlocks, listGet?_lowerBlocksGuarded]
    cases hbb : listGet? body.blocks bbIdx with
    | none =>
      rw [hbb] at hpf
      cases hpf
    | some bb =>
      rw [hbb] at hpf
      dsimp only at hpf
      dsimp only [Option.map]
      cases hst : evalMirStmts st bb.stmts with
      | none => rfl
      | some st1 =>
        rw [hst] at hpf
        dsimp only at hpf
        cases ht : bb.term with
        | goto target =>
          rw [ht] at hpf
          exact ih target st1 hpf
        | switchBool cond tBB fBB =>
          rw [ht] at hpf
          dsimp only at hpf
          dsimp only [lowerTermGuarded, inlineGuardTerm]
          cases hop : evalBoolOp st1 cond with
          | none => rfl
          | some b =>
            rw [hop] at hpf
            cases b
            · exact ih fBB st1 hpf
            · exact ih tBB st1 hpf
        | return_ retOp => rfl
        | unreachable => rfl
        | unwindResume =>
          rw [ht] at hpf
          cases hpf
        | unwindTerminate =>
          rw [ht] at hpf
          cases hpf
        | assert cond expected kind loc target act =>
          rw [ht] at hpf
          dsimp only at hpf
          cases hop : evalBoolOp st1 cond with
          | none =>
            dsimp only [lowerTermGuarded, inlineGuardTerm]
            cases panicUnwinds strat <;> (dsimp only; rw [hop])
          | some actual =>
            rw [hop] at hpf
            dsimp only at hpf
            cases hpf with
            | intro hEq hNext =>
              have hRec := ih target st1 hNext
              cases hpu : panicUnwinds strat
              · dsimp only [lowerTermGuarded, inlineGuardTerm]
                rw [hpu] at hRec ⊢
                dsimp only
                rw [hop]
                dsimp only
                rw [hEq]
                dsimp only
                exact hRec
              · dsimp only [lowerTermGuarded, inlineGuardTerm]
                rw [hpu] at hRec ⊢
                dsimp only
                rw [hop]
                dsimp only
                rw [hEq]
                dsimp only
                exact hRec

/-! ## Section 6: Theorem 2 — Zero-Formatting-Symbol & Zero-Location-Table Elimination -/

/-- Check that a `LlvmGuardTerm` contains no external panic calls (every failure edge is
    `tailCallLlvmTrap`). -/
noncomputable def guardTermImmediateTrapOnly (gt : LlvmGuardTerm) : Bool :=
  match gt with
  | .assertGuard _ _ _ failAct =>
    match failAct with
    | .tailCallLlvmTrap => true
    | _ => false
  | _ => true

/-- Check across all blocks of a lowered module. -/
noncomputable def blocksImmediateTrapOnly : List (List MirStmt × LlvmGuardTerm) → Bool
  | [] => true
  | (_, gt) :: rest => guardTermImmediateTrapOnly gt && blocksImmediateTrapOnly rest

/-- Lemma: when `strat` is `.abort` or `.immediateAbort` (`panicUnwinds strat = false`),
    every lowered `LlvmGuardTerm` produces either non-assert terminators or `.tailCallPanic`
    (NEVER `.invokePanic`). -/
theorem lowerTermGuarded_nonunwind_never_invokes
    (strat : PanicStrategy) (hno : panicUnwinds strat = false) (t : MirTerminator) :
    match (lowerTermGuarded strat t).1 with
    | .assertGuard _ _ _ (.invokePanic _ _ _) => False
    | .assertGuard _ _ _ (.tailCallPanic _ _) => True
    | .assertGuard _ _ _ _ => False
    | _ => True := by
  cases t with
  | goto _ => trivial
  | switchBool _ _ _ => trivial
  | return_ _ => trivial
  | unreachable => trivial
  | unwindResume =>
    dsimp only [lowerTermGuarded]
    rw [hno]
    trivial
  | unwindTerminate =>
    dsimp only [lowerTermGuarded]
  | assert _ _ _ _ _ _ =>
    dsimp only [lowerTermGuarded]
    rw [hno]
    trivial

/-- Key Lemma: under `coreMode = .rebuiltImmediateAbort` and `optLevel = n + 1`
    (`optLevel >= 1`), `inlineFailAction` collapses EVERY `invokePanic` and `tailCallPanic`
    to `tailCallLlvmTrap`. -/
theorem inlineFailAction_rebuiltImmediateAbort_traps
    (n : Nat) (act : LlvmTerm)
    (hAct : match act with | .invokePanic _ _ _ => True | .tailCallPanic _ _ => True | .tailCallLlvmTrap => True | _ => False) :
    (inlineFailAction .rebuiltImmediateAbort (n + 1) act).1 = .tailCallLlvmTrap := by
  cases act with
  | invokePanic _ _ _ => rfl
  | tailCallPanic _ _ => rfl
  | tailCallLlvmTrap => rfl
  | br _ => cases hAct
  | condBr _ _ _ => cases hAct
  | ret _ => cases hAct
  | unreachable => cases hAct

/-- Structural theorem: on ANY lowered `MirBody` under `strat` (even `.unwind`! though in
    practice `immediateAbort` is checked by `dependency_format`), optimizing with
    `coreMode = .rebuiltImmediateAbort` and `optLevel = n + 1` leaves ZERO surviving
    `invokePanic` or `tailCallPanic` calls and ZERO `CallerLoc` `.data` entries in every block! -/
theorem inlineGuardedBlocks_rebuiltImmediateAbort_zero_decls_locs
    (strat : PanicStrategy) (n : Nat) (bbs : List MirBlock) :
    let lowered := (lowerBlocksGuarded strat bbs).1
    let optBbs := (inlineGuardedBlocks .rebuiltImmediateAbort (n + 1) lowered).1
    collectDeclsAndLocsBlocks optBbs = ([], []) ∧
    blocksHaveInvoke optBbs = false ∧
    blocksImmediateTrapOnly optBbs = true := by
  induction bbs with
  | nil =>
    exact ⟨rfl, rfl, rfl⟩
  | cons b bs ih =>
    dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
      blocksHaveInvoke, blocksImmediateTrapOnly]
    cases hih : ih with
    | intro hDecls hRest =>
      cases hRest with
      | intro hInv hTrap =>
        cases ht : b.term with
        | goto target =>
          simp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs,
            guardTermImmediateTrapOnly, Bool.false_or, Bool.true_and]
          exact ⟨hDecls, hInv, hTrap⟩
        | switchBool c t f =>
          simp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs,
            guardTermImmediateTrapOnly, Bool.false_or, Bool.true_and]
          exact ⟨hDecls, hInv, hTrap⟩
        | return_ r =>
          simp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs,
            guardTermImmediateTrapOnly, Bool.false_or, Bool.true_and]
          exact ⟨hDecls, hInv, hTrap⟩
        | unreachable =>
          simp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs,
            guardTermImmediateTrapOnly, Bool.false_or, Bool.true_and]
          exact ⟨hDecls, hInv, hTrap⟩
        | unwindResume =>
          cases hpu : panicUnwinds strat
          · simp only [lowerTermGuarded, hpu, inlineGuardTerm, inlineFailAction,
              resolveCorePanicking, coreHasImmediateAbortCfg, inlinerReplacesInlineHint,
              nat_blt_one_succ, guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs,
              List.nil_append, guardTermImmediateTrapOnly, Bool.false_or,
              Bool.true_and]
            exact ⟨hDecls, hInv, hTrap⟩
          · simp only [lowerTermGuarded, hpu, inlineGuardTerm, guardTermDeclsAndLocs,
              List.nil_append, guardTermImmediateTrapOnly, Bool.false_or,
              Bool.true_and]
            exact ⟨hDecls, hInv, hTrap⟩
        | unwindTerminate =>
          simp only [lowerTermGuarded, inlineGuardTerm, inlineFailAction,
            resolveCorePanicking, coreHasImmediateAbortCfg, inlinerReplacesInlineHint,
            nat_blt_one_succ, guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs,
            List.nil_append, guardTermImmediateTrapOnly, Bool.false_or,
            Bool.true_and]
          exact ⟨hDecls, hInv, hTrap⟩
        | assert cond exp kind loc target act =>
          cases hpu : panicUnwinds strat
          · simp only [lowerTermGuarded, hpu, inlineGuardTerm, inlineFailAction,
              resolveCorePanicking, coreHasImmediateAbortCfg, inlinerReplacesInlineHint,
              nat_blt_one_succ, guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs,
              List.nil_append, guardTermImmediateTrapOnly, Bool.false_or,
              Bool.true_and]
            exact ⟨hDecls, hInv, hTrap⟩
          · simp only [lowerTermGuarded, hpu, inlineGuardTerm, inlineFailAction,
              resolveCorePanicking, coreHasImmediateAbortCfg, inlinerReplacesInlineHint,
              nat_blt_one_succ, guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs,
              List.nil_append, guardTermImmediateTrapOnly, Bool.false_or,
              Bool.true_and]
            exact ⟨hDecls, hInv, hTrap⟩

/-- Helper: ISA trap lowering of `inlineGuardedBlocks .rebuiltImmediateAbort (n + 1)`
    produces strictly hardware trap instructions (`ud2` on `x86_64`, `brk #1` on `aarch64`)
    with zero external panic calls. -/
theorem lowerModuleTrapsToIsa_rebuiltImmediateAbort_pure_hw_trap
    (arch : TargetArch) (strat : PanicStrategy) (n : Nat) (bbs : List MirBlock) :
    let lowered := (lowerBlocksGuarded strat bbs).1
    let optBbs := (inlineGuardedBlocks .rebuiltImmediateAbort (n + 1) lowered).1
    isHardwareTrapOnly (lowerModuleTrapsToIsa arch
      { funcs := [{ blocks := optBbs, hasPersonality := false, nounwind := true, memEffect := .inaccessibleMemWrite }]
      , decls := [], usesLlvmTrap := true, rodataLocs := [] }) := by
  induction bbs with
  | nil =>
    dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, lowerModuleTrapsToIsa,
      lowerModuleTrapsToIsa.goFuncs, lowerModuleTrapsToIsa.goBlocks, isHardwareTrapOnly]
    trivial
  | cons b bs ih =>
    dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, lowerModuleTrapsToIsa,
      lowerModuleTrapsToIsa.goFuncs, lowerModuleTrapsToIsa.goBlocks]
    cases ht : b.term with
    | goto _ | switchBool _ _ _ | return_ _ | unreachable =>
      dsimp only [lowerTermGuarded, inlineGuardTerm]
      exact ih
    | unwindResume =>
      cases hpu : panicUnwinds strat
      · dsimp only [lowerTermGuarded]
        rw [hpu]
        dsimp only [inlineGuardTerm, inlineFailAction, resolveCorePanicking,
          coreHasImmediateAbortCfg, inlinerReplacesInlineHint, nat_blt_one_succ, lowerTermToIsa]
        cases arch <;> exact ih
      · dsimp only [lowerTermGuarded]
        rw [hpu]
        dsimp only [inlineGuardTerm]
        exact ih
    | unwindTerminate =>
      dsimp only [lowerTermGuarded, inlineGuardTerm, inlineFailAction, resolveCorePanicking,
        coreHasImmediateAbortCfg, inlinerReplacesInlineHint, nat_blt_one_succ, lowerTermToIsa]
      cases arch <;> exact ih
    | assert _ _ _ _ _ _ =>
      cases hpu : panicUnwinds strat
      · dsimp only [lowerTermGuarded]
        rw [hpu]
        dsimp only [inlineGuardTerm, inlineFailAction, resolveCorePanicking,
          coreHasImmediateAbortCfg, inlinerReplacesInlineHint, nat_blt_one_succ, lowerTermToIsa]
        cases arch <;> exact ih
      · dsimp only [lowerTermGuarded]
        rw [hpu]
        dsimp only [inlineGuardTerm, inlineFailAction, resolveCorePanicking,
          coreHasImmediateAbortCfg, inlinerReplacesInlineHint, nat_blt_one_succ, lowerTermToIsa]
        cases arch <;> exact ih

/-- **Theorem 2 (Zero-Formatting-Symbol & Zero-Location-Table Elimination Theorem):**
    When a `#![no_std]` MIR body is lowered under `PanicStrategy.immediateAbort` and
    optimized against `coreMode = .rebuiltImmediateAbort` at `optLevel = n + 1 >= 1`:
    1. All undefined external panic/formatting/personality symbols vanish (`decls = []`);
    2. All static `core::panic::Location<'static>` `.data` tables vanish (`rodataLocs = []`,
       `dataFootprintBytes = 0`);
    3. Every function has `hasPersonality = false` and `nounwind = true`;
    4. Every lowered assertion or unwind-terminate sink is a pure hardware trap (`ud2` / `brk #1`),
       with `blocksImmediateTrapOnly = true`. -/
theorem immediateAbort_rebuiltCore_eliminates_all_panic_symbols_and_data
    (arch : TargetArch) (n : Nat) (body : MirBody) :
    let lowered := lowerMirBodyToLlvmGuarded .immediateAbort
                     (abortUnwindingCallsTransform .immediateAbort body)
    let optMod := optimizeLlvmModule .rebuiltImmediateAbort (n + 1) lowered
    optMod.decls = [] ∧
    optMod.rodataLocs = [] ∧
    dataFootprintBytes optMod = 0 ∧
    isHardwareTrapOnly (lowerModuleTrapsToIsa arch optMod) ∧
    (match optMod.funcs with
     | [f] => f.hasPersonality = false ∧ f.nounwind = true ∧ blocksImmediateTrapOnly f.blocks = true
     | _ => False) := by
  dsimp only [lowerMirBodyToLlvmGuarded, optimizeLlvmModule, optimizeLlvmModule.optFuncs,
    optimizeLlvmFunc, collectDeclsAndLocsFuncs, collectDeclsAndLocsBlocks, dataFootprintBytes]
  have h := inlineGuardedBlocks_rebuiltImmediateAbort_zero_decls_locs
    .immediateAbort n (abortUnwindingCallsTransform .immediateAbort body).blocks
  dsimp only at h
  cases h with
  | intro hDecls hRest =>
    cases hRest with
    | intro hInv hTrap =>
      -- Simplify `collectDeclsAndLocsBlocks` projections via `hDecls`
      have hDecls1 : (collectDeclsAndLocsBlocks
        (inlineGuardedBlocks .rebuiltImmediateAbort (n + 1)
          (lowerBlocksGuarded .immediateAbort
            (abortUnwindingCallsTransform .immediateAbort body).blocks).1).1).1 = [] := by
        rw [hDecls]
      have hLocs1 : (collectDeclsAndLocsBlocks
        (inlineGuardedBlocks .rebuiltImmediateAbort (n + 1)
          (lowerBlocksGuarded .immediateAbort
            (abortUnwindingCallsTransform .immediateAbort body).blocks).1).1).2 = [] := by
        rw [hDecls]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hDecls1]
        rfl
      · rw [hLocs1]
        rfl
      · rw [hLocs1]
        rfl
      · have hHw := lowerModuleTrapsToIsa_rebuiltImmediateAbort_pure_hw_trap
          arch .immediateAbort n (abortUnwindingCallsTransform .immediateAbort body).blocks
        dsimp only [lowerModuleTrapsToIsa, lowerModuleTrapsToIsa.goFuncs] at hHw ⊢
        exact hHw
      · refine ⟨?_, ?_, hTrap⟩
        · rfl
        · rfl

/-! ## Section 7: Theorem 3 — Prebuilt-Core Soundness Rejection & `rlib`-vs-`cdylib` Gap -/

/-- Predicate expressing that `coreMode` is a prebuilt sysroot `core` (`unwind` or `abort`),
    not rebuilt with `-Zbuild-std=core` and `-Cpanic=immediate-abort`. -/
noncomputable def isPrebuiltCore : CoreBuildMode → Prop
  | .prebuiltUnwind => True
  | .prebuiltAbort => True
  | _ => False

/-- Count of assertion / unwind-terminate / unwind-resume panic sites in a `MirBody`. -/
noncomputable def countPanicSinkSites : List MirBlock → Nat
  | [] => 0
  | b :: bs =>
    let here :=
      match b.term with
      | .assert _ _ _ _ _ _ => 1
      | .unwindTerminate => 1
      | .unwindResume => 1
      | _ => 0
    here + countPanicSinkSites bs

/-- Lemma: when `coreMode` is prebuilt (`isPrebuiltCore coreMode`), `coreHasImmediateAbortCfg`
    is `false` and `inlineFailAction` NEVER converts `tailCallPanic` into `tailCallLlvmTrap`. -/
theorem prebuiltCore_never_inlines_trap (coreMode : CoreBuildMode) (optLevel : Nat)
    (hpre : isPrebuiltCore coreMode) (act : LlvmTerm) :
    inlineFailAction coreMode optLevel act = (act, false) := by
  cases coreMode with
  | prebuiltUnwind => rfl
  | prebuiltAbort => rfl
  | rebuiltUnwind => cases hpre
  | rebuiltAbort => cases hpre
  | rebuiltImmediateAbort => cases hpre

/-- Tiny addition helper (`1 + k = k + 1`) avoiding `omega`. -/
theorem one_add_eq_succ (k : Nat) : 1 + k = k + 1 := Nat.add_comm 1 k

/-- Length helper for prepending a singleton declaration/location list without `omega`. -/
theorem singleton_append_length {α : Type} (x : α) (xs : List α) :
    ([x] ++ xs).length = 1 + xs.length := by
  rw [List.length_append]
  rfl

/-- Lemma: for any `MirBody` with prebuilt `core`, `inlineGuardedBlocks` is the identity on
    guarded blocks (so `lowerMirBodyToLlvmGuarded .immediateAbort` retains ALL `tailCallPanic`
    calls and ALL `CallerLoc` `.data` tables!). -/
theorem prebuiltCore_retains_decls_and_locs
    (coreMode : CoreBuildMode) (optLevel : Nat) (hpre : isPrebuiltCore coreMode)
    (bbs : List MirBlock) :
    let lowered := (lowerBlocksGuarded .immediateAbort bbs).1
    let optBbs := (inlineGuardedBlocks coreMode optLevel lowered).1
    optBbs = lowered ∧
    (collectDeclsAndLocsBlocks optBbs).1.length = countPanicSinkSites bbs ∧
    (collectDeclsAndLocsBlocks optBbs).2.length = countPanicSinkSites bbs := by
  induction bbs with
  | nil =>
    exact ⟨rfl, rfl, rfl⟩
  | cons b bs ih =>
    cases ih with
    | intro hOpt hLens =>
      cases hLens with
      | intro hDeclsLen hLocsLen =>
        cases ht : b.term with
        | goto target =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs, List.nil_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [hDeclsLen, Nat.zero_add]
          · rw [hLocsLen, Nat.zero_add]
        | switchBool c t f =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs, List.nil_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [hDeclsLen, Nat.zero_add]
          · rw [hLocsLen, Nat.zero_add]
        | return_ r =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs, List.nil_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [hDeclsLen, Nat.zero_add]
          · rw [hLocsLen, Nat.zero_add]
        | unreachable =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, inlineGuardTerm, guardTermDeclsAndLocs, List.nil_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [hDeclsLen, Nat.zero_add]
          · rw [hLocsLen, Nat.zero_add]
        | unwindResume =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, panicUnwinds, inlineGuardTerm]
          rw [prebuiltCore_never_inlines_trap coreMode optLevel hpre]
          dsimp only [guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [singleton_append_length, hDeclsLen]
          · rw [singleton_append_length, hLocsLen]
        | unwindTerminate =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, inlineGuardTerm]
          rw [prebuiltCore_never_inlines_trap coreMode optLevel hpre]
          dsimp only [guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [singleton_append_length, hDeclsLen]
          · rw [singleton_append_length, hLocsLen]
        | assert cond exp kind loc target act =>
          dsimp only [lowerBlocksGuarded, inlineGuardedBlocks, collectDeclsAndLocsBlocks,
            countPanicSinkSites]
          rw [ht]
          dsimp only [lowerTermGuarded, panicUnwinds, inlineGuardTerm]
          rw [prebuiltCore_never_inlines_trap coreMode optLevel hpre]
          dsimp only [guardTermDeclsAndLocs, termSurvivingDecls, termSurvivingLocs]
          refine ⟨?_, ?_, ?_⟩
          · rw [hOpt]
          · rw [singleton_append_length, hDeclsLen]
          · rw [singleton_append_length, hLocsLen]

/-- Helper: under `PanicStrategy.immediateAbort`, `checkWeakLangItems` always returns `.ok`. -/
theorem checkWeakLangItems_immediateAbort (opts : SessionOpts)
    (hStrat : opts.panicStrat = .immediateAbort) (missing : List WeakLangItem) :
    checkWeakLangItems opts missing = .ok := by
  dsimp only [checkWeakLangItems]
  rw [hStrat]
  dsimp only [langItemRequired]
  simp only [Bool.and_false, Bool.false_and]
  cases needsLinkCheck opts.crateType <;> rfl

/-- **Theorem 3a (Prebuilt-Sysroot Linkable Rejection):**
    For any linkable artifact (`cdylib`, `dylib`, `staticlib`, `procMacro`, `executable`),
    `verifyDependencyFormat` (`rustc_metadata/src/dependency_format.rs`) rejects combining
    `PanicStrategy.immediateAbort` with a prebuilt `core` (`prebuiltUnwind` or `prebuiltAbort`),
    returning `CompileResult.errIncompatibleImmediateAbortCore` regardless of whether a
    `#[panic_handler]` is supplied. -/
theorem prebuiltCore_linkable_immediateAbort_rejected
    (opts : SessionOpts)
    (hLink : needsLinkCheck opts.crateType = true)
    (hStrat : opts.panicStrat = .immediateAbort)
    (hPre : isPrebuiltCore opts.coreMode) :
    verifyDependencyFormat opts (noStdCrateDeps opts) = .errIncompatibleImmediateAbortCore := by
  cases opts with
  | mk strat unstab night ct opt cm hasPh hasEh noStd =>
    dsimp only at hStrat hLink hPre
    subst hStrat
    cases cm with
    | prebuiltUnwind =>
      cases ct with
      | rlib => cases hLink
      | dylib | cdylib | staticlib | procMacro | executable => rfl
    | prebuiltAbort =>
      cases ct with
      | rlib => cases hLink
      | dylib | cdylib | staticlib | procMacro | executable => rfl
    | rebuiltUnwind | rebuiltAbort | rebuiltImmediateAbort => cases hPre

/-- **Theorem 3b (End-to-End `cdylib` Compile Rejection Under Prebuilt `core`):**
    Even when session gates (`-Zunstable-options` + nightly) pass and a valid `#[panic_handler]`
    is optionally supplied, compiling any linkable artifact with `-Cpanic=immediate-abort` against
    a prebuilt sysroot `core` fails with `.errIncompatibleImmediateAbortCore`. -/
theorem prebuiltCore_cdylib_immediateAbort_compile_rejected
    (opts : SessionOpts)
    (phSig : Option FnSig)
    (hGate : checkSessionGate opts = .ok)
    (hPhOk : match phSig with | none => True | some s => checkPanicHandlerSig s = .ok)
    (hLink : needsLinkCheck opts.crateType = true)
    (hStrat : opts.panicStrat = .immediateAbort)
    (hPre : isPrebuiltCore opts.coreMode) :
    compileAdmitted opts phSig = .errIncompatibleImmediateAbortCore := by
  dsimp only [compileAdmitted]
  rw [hGate]
  dsimp only
  cases phSig with
  | none =>
    dsimp only
    rw [checkWeakLangItems_immediateAbort opts hStrat]
    exact prebuiltCore_linkable_immediateAbort_rejected opts hLink hStrat hPre
  | some s =>
    dsimp only at hPhOk
    dsimp only
    rw [hPhOk]
    dsimp only
    rw [checkWeakLangItems_immediateAbort opts hStrat]
    exact prebuiltCore_linkable_immediateAbort_rejected opts hLink hStrat hPre

/-- Helper: positive count implies nonzero `.length` and nonzero `24`-byte table footprint
    without invoking `omega`. -/
theorem pos_mul_24_ne_zero (n : Nat) (h : 0 < n) : n * 24 ≠ 0 := by
  cases n with
  | zero => cases h
  | succ k =>
    intro hz
    cases hz

/-- **Theorem 3c (`rlib` Linkage-Check Bypass Retains Panic Symbols & `.data` Tables):**
    For `CrateType.rlib`, `compileAdmitted` skips linkage checks (`needsLinkCheck .rlib = false`)
    and admits compilation even against prebuilt `core`; however, `optimizeLlvmModule` retains
    exact `countPanicSinkSites body.blocks` unresolved `core::panicking::*` declarations and
    `24 * countPanicSinkSites body.blocks` bytes of `Location` static `.data` tables! -/
theorem prebuiltCore_rlib_immediateAbort_admitted_but_retains_syms
    (opts : SessionOpts)
    (hRlib : opts.crateType = .rlib)
    (hGate : checkSessionGate opts = .ok)
    (hPre : isPrebuiltCore opts.coreMode)
    (body : MirBody)
    (hSite : 0 < countPanicSinkSites body.blocks) :
    let lowered := lowerMirBodyToLlvmGuarded .immediateAbort body
    let optMod := optimizeLlvmModule opts.coreMode opts.optLevel lowered
    compileAdmitted opts none = .ok ∧
    optMod.decls.length = countPanicSinkSites body.blocks ∧
    dataFootprintBytes optMod = countPanicSinkSites body.blocks * 24 ∧
    optMod.decls ≠ [] ∧
    dataFootprintBytes optMod ≠ 0 := by
  have hAdm : compileAdmitted opts none = .ok := by
    dsimp only [compileAdmitted]
    rw [hGate]
    dsimp only [checkWeakLangItems, verifyDependencyFormat]
    rw [hRlib]
    rfl
  have hRet := prebuiltCore_retains_decls_and_locs opts.coreMode opts.optLevel hPre body.blocks
  dsimp only at hRet
  cases hRet with
  | intro hOpt hLens =>
    cases hLens with
    | intro hDL hLL =>
      dsimp only [lowerMirBodyToLlvmGuarded, optimizeLlvmModule, optimizeLlvmModule.optFuncs,
        optimizeLlvmFunc, collectDeclsAndLocsFuncs, dataFootprintBytes]
      have hDeclsEq :
          ((collectDeclsAndLocsBlocks
            (inlineGuardedBlocks opts.coreMode opts.optLevel
              (lowerBlocksGuarded .immediateAbort body.blocks).1).1).1 ++ []).length =
          countPanicSinkSites body.blocks := by
        rw [List.append_nil, hDL]
      have hLocsEq :
          ((collectDeclsAndLocsBlocks
            (inlineGuardedBlocks opts.coreMode opts.optLevel
              (lowerBlocksGuarded .immediateAbort body.blocks).1).1).2 ++ []).length =
          countPanicSinkSites body.blocks := by
        rw [List.append_nil, hLL]
      have hNeNil :
          (collectDeclsAndLocsBlocks
            (inlineGuardedBlocks opts.coreMode opts.optLevel
              (lowerBlocksGuarded .immediateAbort body.blocks).1).1).1 ++ [] ≠ [] := by
        intro hEmpty
        rw [hEmpty, List.length_nil] at hDeclsEq
        rw [← hDeclsEq] at hSite
        cases hSite
      have hDataPos :
          ((collectDeclsAndLocsBlocks
            (inlineGuardedBlocks opts.coreMode opts.optLevel
              (lowerBlocksGuarded .immediateAbort body.blocks).1).1).2 ++ []).length * 24 ≠ 0 := by
        rw [hLocsEq]
        exact pos_mul_24_ne_zero (countPanicSinkSites body.blocks) hSite
      refine ⟨hAdm, hDeclsEq, ?_, hNeNil, hDataPos⟩
      rw [hLocsEq]

/-! ## Section 8: Theorem 4 — `#[panic_handler]` Signature (`-> !`) & Lang-Item Exemption Soundness -/

/-- **Theorem 4a (`E0308` Signature Rejection of `-> ()` and Uniqueness of `-> !`):**
    Models `check_panic_info_fn` (`compiler/rustc_hir_typeck/src/check.rs:165-235`):
    1. A `fn(&PanicInfo) -> ()` handler is rejected with `.errPanicHandlerWrongType` (`E0308`);
    2. A generic handler is rejected with `.errPanicHandlerGenerics`;
    3. Any accepted handler MUST have `0` type/const params, single `&PanicInfo` arg, and
       never-return type `RustTy.never` (`-> !`). -/
theorem panicHandler_unit_return_rejected :
    checkPanicHandlerSig { typeParams := 0, constParams := 0, argTys := [.panicInfoRef], retTy := .unit } =
      .errPanicHandlerWrongType := rfl

theorem panicHandler_never_return_accepted :
    checkPanicHandlerSig { typeParams := 0, constParams := 0, argTys := [.panicInfoRef], retTy := .never } =
      .ok := rfl

theorem checkPanicHandlerSig_sound_implies_never (sig : FnSig)
    (hok : checkPanicHandlerSig sig = .ok) :
    sig.typeParams = 0 ∧ sig.constParams = 0 ∧ sig.argTys = [.panicInfoRef] ∧ sig.retTy = .never := by
  cases sig with
  | mk tp cp args ret =>
    cases tp with
    | zero =>
      cases cp with
      | zero =>
        cases args with
        | nil =>
          dsimp only [checkPanicHandlerSig] at hok
          cases hok
        | cons a rest =>
          cases a with
          | panicInfoRef =>
            cases rest with
            | nil =>
              cases ret with
              | never => exact ⟨rfl, rfl, rfl, rfl⟩
              | unit | panicInfoRef | u32 | other =>
                dsimp only [checkPanicHandlerSig] at hok
                cases hok
            | cons _ _ =>
              dsimp only [checkPanicHandlerSig] at hok
              cases hok
          | never | unit | u32 | other =>
            dsimp only [checkPanicHandlerSig] at hok
            cases hok
      | succ _ =>
        dsimp only [checkPanicHandlerSig] at hok
        cases hok
    | succ _ =>
      dsimp only [checkPanicHandlerSig] at hok
      cases hok

/-- Helper: under `panicStrat = .immediateAbort` and `coreMode = .rebuiltImmediateAbort`,
    `noStdCrateDeps` satisfies `verifyDependencyFormat` for ANY `CrateType`. -/
theorem verifyDependencyFormat_rebuiltImmediateAbort_ok (opts : SessionOpts)
    (hStrat : opts.panicStrat = .immediateAbort)
    (hCore : opts.coreMode = .rebuiltImmediateAbort) :
    verifyDependencyFormat opts (noStdCrateDeps opts) = .ok := by
  cases opts with
  | mk strat unstab night ct opt cm hasPh hasEh noStd =>
    dsimp only at hStrat hCore
    subst hStrat
    subst hCore
    cases ct <;> rfl

/-- **Theorem 4b (Soundness of Weak Lang-Item Exemption Under `ImmediateAbort + RebuiltCore`):**
    When a `#![no_std]` crate (`cdylib`, `staticlib`, `executable`, etc.) sets `-Cpanic=immediate-abort`,
    `-Zunstable-options`, and `-Zbuild-std=core` (`optLevel >= 1`), omitting BOTH `#[panic_handler]`
    and `#[lang = "eh_personality"]` is:
    1. Admitted by the frontend/linker (`compileAdmitted = .ok`), because `langItemRequired .immediateAbort _ = false`;
    2. Link-time sound, because `optimizeLlvmModule` eliminates every surviving external panic/personality
       symbol (`decls = []`) and converts every panic sink to a hardware trap! -/
theorem panicHandler_omission_cdylib_sound_under_immediateAbort_rebuiltCore
    (ct : CrateType) (optN : Nat) (body : MirBody) :
    let opts : SessionOpts :=
      { panicStrat := .immediateAbort
      , unstableOptions := true
      , nightlyCompiler := true
      , crateType := ct
      , optLevel := optN + 1
      , coreMode := .rebuiltImmediateAbort
      , hasPanicHandler := false
      , hasEhPersonality := false
      , noStd := true }
    let lowered := lowerMirBodyToLlvmGuarded .immediateAbort
                     (abortUnwindingCallsTransform .immediateAbort body)
    let optMod := optimizeLlvmModule .rebuiltImmediateAbort (optN + 1) lowered
    compileAdmitted opts none = .ok ∧
    optMod.decls = [] ∧
    dataFootprintBytes optMod = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [compileAdmitted]
    have hWeak : checkWeakLangItems
        { panicStrat := .immediateAbort, unstableOptions := true, nightlyCompiler := true
        , crateType := ct, optLevel := optN + 1, coreMode := .rebuiltImmediateAbort
        , hasPanicHandler := false, hasEhPersonality := false, noStd := true }
        [.panicImpl, .ehPersonality] = .ok :=
      checkWeakLangItems_immediateAbort _ rfl _
    rw [hWeak]
    exact verifyDependencyFormat_rebuiltImmediateAbort_ok _ rfl rfl
  · exact (immediateAbort_rebuiltCore_eliminates_all_panic_symbols_and_data .x86_64 optN body).1
  · exact (immediateAbort_rebuiltCore_eliminates_all_panic_symbols_and_data .x86_64 optN body).2.2.1

/-- **Theorem 4c (Necessity of `#[panic_handler]` Under `Abort` and `Unwind` Linkable Crates):**
    Under `.abort` or `.unwind` on any linkable crate (`needsLinkCheck ct = true`), omitting
    `#[panic_handler]` is rejected by `compileAdmitted` with `.errMissingPanicHandler`. -/
theorem missing_panicHandler_linkable_abort_or_unwind_rejected
    (opts : SessionOpts)
    (hLink : needsLinkCheck opts.crateType = true)
    (hNoPh : opts.hasPanicHandler = false)
    (hNotImm : opts.panicStrat = .abort ∨ opts.panicStrat = .unwind) :
    compileAdmitted opts none = .errMissingPanicHandler := by
  cases opts with
  | mk strat unstab night ct opt cm hasPh hasEh noStd =>
    dsimp only at hLink hNoPh hNotImm
    subst hNoPh
    cases hNotImm with
    | inl hAb =>
      subst hAb
      cases ct with
      | rlib => cases hLink
      | dylib | cdylib | staticlib | procMacro | executable =>
        cases noStd <;> rfl
    | inr hUnw =>
      subst hUnw
      cases ct with
      | rlib => cases hLink
      | dylib | cdylib | staticlib | procMacro | executable =>
        cases noStd <;> rfl

/-- Conversely, `rlib` admits missing `#[panic_handler]` even under `.abort` / `.unwind`
    because `weak_lang_items::verify` skips `CrateType.rlib`. -/
theorem missing_panicHandler_rlib_admitted
    (opts : SessionOpts)
    (hRlib : opts.crateType = .rlib)
    (hGate : checkSessionGate opts = .ok) :
    compileAdmitted opts none = .ok := by
  dsimp only [compileAdmitted]
  rw [hGate]
  dsimp only [checkWeakLangItems, verifyDependencyFormat]
  rw [hRlib]
  rfl

/-! ## Section 9: Boundary Conditions (Dual `cfg`, `-O0` Inlining Threshold, and Anneal TCB Gaps) -/

/-- **Dual `cfg` Property (`compiler/rustc_session/src/config/cfg.rs:218-221`):**
    Under `-Cpanic=immediate-abort`, BOTH `cfg(panic = "immediate-abort")` AND
    `cfg(panic = "abort")` evaluate to `true` (`cfg_flags_mask() == 3`), while
    `cfg(panic = "unwind")` evaluates to `false`. -/
theorem dual_cfg_immediateAbort_activates_both :
    cfgHasPanic .immediateAbort .immediateAbort = true ∧
    cfgHasPanic .immediateAbort .abort = true ∧
    cfgHasPanic .immediateAbort .unwind = false :=
  ⟨rfl, rfl, rfl⟩

/-- **`-O0` Inlining Boundary (`--profile=dev`):**
    Because `library/core/src/panicking.rs` marks panic entry points with `#[inline]`
    (an `InlineHint`) rather than `#[inline(always)]`, compiling at `optLevel = 0` leaves
    `inlineGuardedBlocks .rebuiltImmediateAbort 0` as the identity: caller IR still calls
    monomorphized `core::panicking::*` functions and retains `24 * k` `.data` `CallerLoc` bytes
    (verified empirically: `text_bytes = 1981, data_bytes = 96` on `panic_probe`), even
    though `cdylib` links cleanly without a `#[panic_handler]` because those monomorphized
    `core::panicking` bodies emit `llvm.trap` internally. -/
theorem nat_blt_zero_zero : Nat.blt 0 0 = false := rfl

theorem opt0_defeats_core_panicking_inline (strat : PanicStrategy) (bbs : List MirBlock) :
    (inlineGuardedBlocks .rebuiltImmediateAbort 0 (lowerBlocksGuarded strat bbs).1).1 =
      (lowerBlocksGuarded strat bbs).1 := by
  induction bbs with
  | nil => rfl
  | cons b bs ih =>
    dsimp only [lowerBlocksGuarded, inlineGuardedBlocks]
    cases b.term with
    | goto _ | switchBool _ _ _ | return_ _ | unreachable =>
      dsimp only [lowerTermGuarded, inlineGuardTerm]
      rw [ih]
    | unwindResume =>
      cases hpu : panicUnwinds strat <;> dsimp only [lowerTermGuarded]
      · rw [hpu]
        dsimp only [inlineGuardTerm, inlineFailAction, resolveCorePanicking,
          coreHasImmediateAbortCfg, inlinerReplacesInlineHint]
        rw [nat_blt_zero_zero]
        dsimp only
        rw [ih]
      · rw [hpu]
        dsimp only [inlineGuardTerm]
        rw [ih]
    | unwindTerminate =>
      dsimp only [lowerTermGuarded, inlineGuardTerm, inlineFailAction, resolveCorePanicking,
        coreHasImmediateAbortCfg, inlinerReplacesInlineHint]
      rw [nat_blt_zero_zero]
      dsimp only
      rw [ih]
    | assert _ _ _ _ _ _ =>
      cases hpu : panicUnwinds strat <;> dsimp only [lowerTermGuarded]
      · rw [hpu]
        dsimp only [inlineGuardTerm, inlineFailAction, resolveCorePanicking,
          coreHasImmediateAbortCfg, inlinerReplacesInlineHint]
        rw [nat_blt_zero_zero]
        dsimp only
        rw [ih]
      · rw [hpu]
        dsimp only [inlineGuardTerm, inlineFailAction, resolveCorePanicking,
          coreHasImmediateAbortCfg, inlinerReplacesInlineHint]
        rw [nat_blt_zero_zero]
        dsimp only
        rw [ih]

/-- Anneal MIR verifier support status modeled after `joshlf/anneal`
    `trusted/lean/Trusted/MirSemantics.lean:1568-1569`. -/
inductive AnnealMirSupport where
  | supported
  | failClosedUnsupported

/-- Whether Anneal's fail-closed MIR evaluator supports a given terminator. -/
noncomputable def annealTerminatorSupport : MirTerminator → AnnealMirSupport
  | .goto _ => .supported
  | .switchBool _ _ _ => .supported
  | .return_ _ => .supported
  | .unreachable => .supported
  | .unwindResume => .failClosedUnsupported
  | .unwindTerminate => .failClosedUnsupported
  | .assert _ _ _ _ _ _ => .failClosedUnsupported

/-- Anneal fails closed on `Assert`, `UnwindResume`, and `UnwindTerminate` regardless of
    `-Cpanic=immediate-abort` — AND immediate-abort proves that a failing `Assert` becomes
    `.trappedImmediate` (a clean trap, not UB, but still a non-returning crash if reached!),
    so verification of panic-freedom still requires discharging every `Assert` predicate. -/
theorem immediateAbort_failing_assert_still_traps_not_returns
    (body : MirBody) (cond : MirOperand) (expected : Bool) (kind : AssertKind)
    (loc : CallerLoc) (target : Nat) (unwind : UnwindAction)
    (st : MirState) (fuel' : Nat) (actual : Bool)
    (hbb0 : listGet? body.blocks 0 = some { stmts := [], term := .assert cond expected kind loc target unwind, isCleanup := false })
    (hCond : evalBoolOp st cond = some actual)
    (hFail : boolEqv actual expected = false) :
    ∃ (modStrat : MirOutcome),
      modStrat = evalMirBodyFuel .immediateAbort .rebuiltImmediateAbort 2 body 0 st (fuel' + 1) ∧
      modStrat = .trappedImmediate := by
  refine ⟨evalMirBodyFuel .immediateAbort .rebuiltImmediateAbort 2 body 0 st (fuel' + 1), rfl, ?_⟩
  dsimp only [evalMirBodyFuel]
  rw [hbb0]
  dsimp only [evalMirStmts]
  rw [hCond]
  dsimp only
  rw [hFail]
  rfl

/-! ## Section 10: Concrete `div` and `idx` Specimens Matching Live `rustc` Output -/

/-- Concrete MIR body modeling `pub extern "C" fn div(a: u32, b: u32) -> u32`:
    - `bb0`: `_3 = Eq(_1, 0); assert(!_3, divByZero, loc1) -> [success: bb1, unwind continue]`
    - `bb1`: `_0 = Div(_0_in, _1_in); return _0` -/
noncomputable def divProbeMirBody : MirBody :=
  { blocks :=
      [ { stmts := [.assign 0 (.eqNat (.local 1) (.constNat 0)), .assign 1 (.boolNot (.local 0))]
        , term := .assert (.local 1) true .divByZero ⟨1, 27, 5⟩ 1 .continue_
        , isCleanup := false }
      , { stmts := [.assign 2 (.divNat (.local 0) (.local 1))]
        , term := .return_ (.local 2)
        , isCleanup := false }
      ]
  , canUnwindAbi := false }

/-- Concrete MIR body modeling `pub unsafe extern "C" fn idx(s, len, i) -> u32`:
    - `bb0`: `_3 = Lt(i, len); assert(_3, boundsCheck, loc2) -> [success: bb1, unwind continue]`
    - `bb1`: `_0 = sliceRead(0, len, i); return _0` -/
noncomputable def idxProbeMirBody : MirBody :=
  { blocks :=
      [ { stmts := [.assign 0 (.ltNat (.local 2) (.local 1))]
        , term := .assert (.local 0) true .boundsCheck ⟨1, 33, 5⟩ 1 .continue_
        , isCleanup := false }
      , { stmts := [.assign 3 (.sliceRead 0 (.local 1) (.local 2))]
        , term := .return_ (.local 3)
        , isCleanup := false }
      ]
  , canUnwindAbi := false }

/-- Concrete safe input state for `div(20, 4)`: `reg 0 = 20, reg 1 = 4`. -/
noncomputable def safeDivState : MirState :=
  { regs := fun i => match i with | 0 => 20 | 1 => 4 | _ => 0
  , bools := fun _ => false
  , mem := fun _ => 0 }

/-- Concrete safe input state for `idx(s, 4, 2)` with `s[2] = 77`: `reg 1 = 4, reg 2 = 2`. -/
noncomputable def safeIdxState : MirState :=
  { regs := fun i => match i with | 1 => 4 | 2 => 2 | _ => 0
  , bools := fun _ => false
  , mem := fun i => match i with | 2 => 77 | _ => 0 }

/-- Specimen check 1: on safe `div(20, 4)`, all 3 strategies + `abortUnwindingCallsTransform`
    evaluate to the exact same value `5` (and same updated state). -/
theorem divProbe_safe_exec_agrees :
    ExecutionPanicFree divProbeMirBody 0 safeDivState 4 ∧
    (match evalMirBodyFuel .unwind .prebuiltUnwind 2 (abortUnwindingCallsTransform .unwind divProbeMirBody) 0 safeDivState 4 with
     | .returned v _ => v = 5
     | _ => False) ∧
    evalMirBodyFuel .unwind .prebuiltUnwind 2 (abortUnwindingCallsTransform .unwind divProbeMirBody) 0 safeDivState 4 =
      evalMirBodyFuel .immediateAbort .rebuiltImmediateAbort 2
        (abortUnwindingCallsTransform .immediateAbort divProbeMirBody) 0 safeDivState 4 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨rfl, trivial⟩
  · rfl
  · rfl

/-- Specimen check 2: on safe `idx(s, 4, 2)` with `s[2] = 77`, `unwind` and `immediateAbort`
    agree and return `77`. -/
theorem idxProbe_safe_exec_agrees :
    ExecutionPanicFree idxProbeMirBody 0 safeIdxState 4 ∧
    (match evalMirBodyFuel .immediateAbort .rebuiltImmediateAbort 2
             (abortUnwindingCallsTransform .immediateAbort idxProbeMirBody) 0 safeIdxState 4 with
     | .returned v _ => v = 77
     | _ => False) := by
  exact ⟨⟨rfl, trivial⟩, rfl⟩

/-- Specimen check 3: on unsafe `div(20, 0)`, `.immediateAbort + .rebuiltImmediateAbort` at `-O2`
    yields `.trappedImmediate` with `0` decls, `0` `.data` bytes, and `x86Ud2` (`2 B` on `x86_64`) /
    `aarch64Brk1` (`4 B` on `aarch64`); while prebuilt sysroot retains `panicConstDivByZero` and
    `24` bytes of `Location` table (`48` bytes across both `div` and `idx`). -/
theorem div_and_idx_footprint_contrast_exact :
    let divOpt := optimizeLlvmModule .rebuiltImmediateAbort 2
                    (lowerMirBodyToLlvmGuarded .immediateAbort
                      (abortUnwindingCallsTransform .immediateAbort divProbeMirBody))
    let idxOpt := optimizeLlvmModule .rebuiltImmediateAbort 2
                    (lowerMirBodyToLlvmGuarded .immediateAbort
                      (abortUnwindingCallsTransform .immediateAbort idxProbeMirBody))
    let divPre := optimizeLlvmModule .prebuiltAbort 2
                    (lowerMirBodyToLlvmGuarded .immediateAbort divProbeMirBody)
    let idxPre := optimizeLlvmModule .prebuiltAbort 2
                    (lowerMirBodyToLlvmGuarded .immediateAbort idxProbeMirBody)
    divOpt.decls = [] ∧ idxOpt.decls = [] ∧
    dataFootprintBytes divOpt + dataFootprintBytes idxOpt = 0 ∧
    lowerModuleTrapsToIsa .x86_64 divOpt = [.x86Ud2] ∧
    lowerModuleTrapsToIsa .aarch64 idxOpt = [.aarch64Brk1] ∧
    divPre.decls = [.panicConstDivByZero] ∧
    idxPre.decls = [.panicBoundsCheck] ∧
    dataFootprintBytes divPre + dataFootprintBytes idxPre = 48 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NoStdPanicImmediateAbortTrapAndFootprintSoundness
