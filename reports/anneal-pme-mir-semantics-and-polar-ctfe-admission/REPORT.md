# Post-Monomorphization Errors, Polar CTFE Admission, Semantic Polarity, and Polymorphic Conditional Contracts in Anneal

## Summary

### Part I — Post-Monomorphization Error (PME) MIR Semantics and Polymorphic Conditional Contracts

A Rust function can pass polymorphic type checking and borrow checking yet fail
compile-time constant evaluation (CTFE) or layout computation when instantiated
during monomorphization, producing a Post-Monomorphization Error (PME,
`error[E0080]`). Both `const { assert!(N <= 1000) }` and `zerocopy`'s
`transmute_ref<Src, Dst>` rely on this mechanism: their runtime
`MirPhase::Runtime(RuntimePhase::PostCleanup)` basic blocks omit the assertion
logic, which `rustc` extracts into `Body::required_consts` (`ConstMirBody`) for
evaluation during `rustc_monomorphize::collector::collect_items_of_instance`.
If Anneal models only a function's runtime control-flow graph, safe functions
whose memory safety or arithmetic overflow freedom depends on a PME become
unverifiable because invalid instantiations exhibit runtime undefined behavior
(UB) in the unguarded runtime CFG.

Two standalone Lean 4 (`v4.34.1`) mechanizations preserved in this package—
[support/PmeMirSemantics.lean](support/PmeMirSemantics.lean) (2,563 lines, SHA-256
`c93ee5252538031e0953e154800573701515a564d86f7bbc2083a59ad0f2cc7f`) and
[support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean)
(2,110 lines, SHA-256
`9b7d816ea84413422941fdc4609b0939cc827ec413375d20314208cbf3207495`)—establish
five core results with zero `sorryAx` and zero `Lean.ofReduceBool`:

1. **Single-interpreter PME model (`ConstMirMachine` and `CompileAdmitted`):**
   Every entry in `Body::required_consts` is itself a `Runtime(PostCleanup)`
   MIR body (`tcx.mir_for_ctfe(def_id)`). Extending `MirBody` with
   `requiredConsts : List ConstMirBody` and `requiredLayouts : List TyLayout`
   lets `ConstMirMachine` evaluate CTFE obligations using the exact same
   small-step transition function (`evalBlocksStep`) as runtime `MirMachine`.
2. **Dead-branch retention vs. post-divergence stripping in `rustc`:**
   All conditional branches (`if false`, `match false`, `if (const { false })`,
   and `let b = false; if b`) lower to `TerminatorKind::SwitchInt` on a
   temporary local, remain reachable from `START_BLOCK` (`bb0`) through
   `SimplifyCfg::Initial`, populate `Body::required_consts` and
   `Body::mentioned_items`, and fail monomorphization with `error[E0080]`.
   Only statements after unconditional divergence (`return;`, `break;`,
   `continue;`, or `loop {}` without `break`) are lowered into zero-predecessor
   basic blocks that `SimplifyCfg::Initial` deletes before `mir_promoted` runs.
3. **Why `rustc --crate-type=lib` exit code 0 does not prove
   `CompileAdmitted`:**
   Under lazy monomorphization (`MonoItemCollectionStrategy::Lazy`), `rustc`
   skips root collection for generic functions, unreachable private
   non-generic functions, and cross-crate inlinable public non-generic
   functions (`#[inline]` or `-C opt-level=2` via
   `reachable_non_generics_helper`). Anneal must therefore verify
   `CompileAdmitted` explicitly rather than trusting `rustc`'s exit status.
4. **Adjoint equivalence of Approach 1 (`PartialCompiler`) and Approach 2
   (`MirMachine.withAdmitted`):**
   In `Behavior Query Out := Query → Partial (Out → Prop)`, gating a program
   behavior by a compile-time proposition `P` (`Behavior.when P b`, collapsing
   to `Partial.bot` when `¬ P`) is constructively left adjoint to guarding a
   specification by `P` (`Behavior.given P spec`, collapsing to `Partial.ub`
   when `¬ P`). Approach 2 (`MirSemAdmitted body ≤ spec`) preserves
   `TotalStep`, `InhabitedDemonic`, and `non_vacuity_at_every_depth` and is
   constructively equivalent (`↔`) to Approach 1's conditional obligation
   `body.CompileAdmitted → MirSem body ≤ spec` (`mirSemAdmitted_le_iff`).
5. **Polymorphic and cross-crate conditional contracts (`InstCtx`, Model I vs. Model II):**
   Representing a polymorphic function as an `InstCtx`-indexed family of
   `MonoMirUnit`s (Representation Model I, `PolyCapturedFnR1`) or as a
   query-enriched language `PolyMirLang InstCtx` with
   `PolyQuery InstCtx := InstCtx × ExecQuery MirState` (Representation Model II)
   requires no changes to `Trusted/Refinement.lean`. A two-pass
   `model-refinement` analysis shows that a naive conjunction of instantiation
   and runtime preconditions in Model II (`naiveTotalPre`) vacuously accepts a
   PME-failing program whenever the runtime argument precondition `argPre` is
   uninhabited (`naive_r2_vacuous_argPre_counterexample`). Including the 0-step
   compile-time prefix (`q.steps = 0 ∨ argPre inst q` in `unifiedTotalPre`)
   restores an exact constructive equivalence (`↔`) between Model I and Model II
   (`r1_iff_r2_source_wellFormed`) and supports modular cross-crate
   verification of callers alongside three distinct failure controls (PME
   violation, `LIB-07` semantic trait violation, and runtime argument
   precondition violation).

### Part II — Polar CTFE Admission, Step-Dilated Progress Preservation, and Four-Quadrant Semantic Polarity

- **Four-Quadrant Semantic Polarity Matrix and Two-Sided Sandwich Theorem:** In
  Anneal's demonic partial-behavior refinement lattice (`Partial.le`, where
  `Partial.ub` with `defined = False` is the top element $\top$ and
  `Partial.bot` / `Partial.magic` with `defined = True, val = ∅` is the bottom
  element $\bot$), whether an operational-semantics defect is **fail-open**
  (unsound) or **fail-closed** (conservative) depends on which of four polarity
  positions the language occupies:
  1. **Quadrant 1 (Trusted Source Language on LHS of `L_src.sem s ≤ spec` with
     unverified compiler in `hTcb`):** Omitting Undefined Behavior (UB) or
     demonic nondeterminism is fail-open; adding spurious `.failed` is
     fail-closed; adding spurious `.stuck` without positive `.stuck` rejection
     is fail-open.
  2. **Quadrant 2 (Trusted Target ISA on LHS of `L_tgt.sem t ≤ spec_tgt`):**
     Omitting hardware traps (`#DE`, `#GP`, `#UD`, or out-of-frame stack
     writes) or under-approximating architecturally undefined register/flag
     state is fail-open; adding spurious `.failed` is fail-closed.
  3. **Quadrant 3 (Source or Intermediate Language on RHS of
     `Compiles L_src L_tgt π_c s t`, i.e., `L_tgt.sem t ≤ π_c (L_src.sem s)`):**
     Declaring spurious UB (`defined = False`, $\top$) in `L_src.sem s` at
     `decompileQ q` makes `π_c (L_src.sem s) q = Partial.ub` ($\top$), which
     every arbitrary broken target binary `t` (including `ud2`) trivially
     refines (**the Spurious-UB Codegen Exploit**). Enforcing the **Two-Sided
     Sandwich**—requiring both `Compiles L_src L_tgt π_c s t` and
     `L_src.sem s ≤ L_src.SpecOn pre post`—forces `(L_src.sem s (decompileQ
     q)).defined` to hold on `pre`, neutralizing the Quadrant-3 exploit.
  4. **Quadrant 4 (Premise / Admission Language in Negative Polarity,
     `ConstSucceeds` / `MonoAdmitted` inside `initMirState` or
     `effectivePre`):** Because `MonoAdmitted` sits on the left-hand side of
     `→` inside `BehaviorOf.defined` or `SpecOn effectivePre post`, polarity
     flips: any spurious CTFE failure (`¬ ConstSucceeds` on a monomorphization
     that `rustc` accepts, whether via `.stuck` or `.failed`) shrinks the entry
     state or precondition to `False` ($\bot$) and **vacuously verifies**
     runtime-UB functions (fail-open).
- **Negative-Polarity `.stuck` and `.failed` Fail-Open Inversion in CTFE and the
  `ConstIsSafe` / `SafePolarMirSem` / `MonoInhabitedSafe` Solution:** In
  `Trusted/StepResult.lean`, `ReachesPrefix` maps unstepped states (`noStep`)
  and empty nondeterministic choices (`emptyChoice`) to `PrefixOutcome.stuck`
  with `PrefixOutcome.isSafe .stuck = False`, while `evalMirStep` maps unmodeled
  sub-cases (such as `evalBinOp` on `.bytes` or `.adt` operands returning
  `none`) to `StepResult.failed` (`PrefixOutcome.isSafe .failed = False`). Both
  are fail-closed in positive runtime position, but in negative CTFE admission
  position (`ConstSucceeds`, which checks `∃ ..., ReachesPrefix ...
  (.terminated (.normal v))`), both `.stuck` and `.failed` are
  indistinguishable from a legitimate post-monomorphization error (PME) panic
  (`.terminated .unwind`): all three falsify `ConstSucceeds` and `MonoAdmitted`,
  collapsing `MirSem` to `Partial.bot` and vacuously certifying unconditional
  runtime UB (`Terminator.unreachable` or size-mismatched `transmute_copy`).
  Moreover, `non_vacuity_at_every_depth` (`TotalStep` + `InhabitedDemonic`) does
  not catch empty `initMirState` because it assumes `M.initState p init` as a
  hypothesis, and entry-state inhabitation (`∃ s, initMirState body s`) or
  `ConstNoStuck` (`out ≠ .stuck`) alone fails on conditionally `.stuck` or
  conditionally `.failed` constants (`partiallyUnmodeledConst`,
  `partiallyFailedConst`). Defining **`ConstIsSafe`** (`∀ s₀ n tr out, ... →
  out.isSafe`), placing `BodyConstsSafe` in positive polarity inside
  `SafePolarMirSem.defined`, gating negative monomorphization filtering as
  `MonoAdmittedSafe` (`ConstIsSafe → ConstSucceeds`), and requiring
  `MonoInhabitedSafe` closes both `.stuck` and `.failed` fail-open holes while
  preserving legitimate PMEs (`sizeEq8ConstBody`, which terminates with
  `.terminated .unwind` where `(.terminated .unwind).isSafe = True`).
- **Transitive 4-Place `RequiresConst` with `substTySizes` vs. 2-Place
  `RequiresConst` in `MIR-to-x86-64 prototype`:** While `StepResult-refinement baseline`
  (`Trusted/MirSemantics.lean`) defines a 4-place inductive relation
  `RequiresConst tySizes body tySizes' c` that substitutes
  `substTySizes tySizes typeArgs` across `.call1` edges, `MIR-to-x86-64 prototype`
  (`Trusted/X86Semantics.lean` and `theory/Anneal/MirSemantics.lean`) simplifies
  `RequiresConst` to a 2-place relation `RequiresConst : Body → Body → Prop`
  and checks `ConstSucceeds tySizes c` at the **caller's** `tySizes`. For a
  generic caller `caller<U>` (`tySizes 0 = 8`) invoking
  `transmuteToUsizeChecked::<bool>(true)` (`typeArgs = [.bool]`), the 2-place
  relation evaluates `sizeEq8ConstBody` at the caller's `tySizes` (`8 = 8`,
  succeeding!) instead of the callee's `substTySizes` (`1 = 8`, panicking),
  falsely admitting a call that reaches `PrefixOutcome.failed` in 4 steps at
  runtime.
- **Constructive Step-Dilated Prefix Simulation (`π_dilated k`) via Fuel
  Absorption:** Because `PrefixOutcome.isSafe` maps both `.running` and
  `.terminated .unwind` to `True`, and `SpecOn` guards postconditions behind
  `out.outcome = .terminated (.normal ret) → ...`, degenerate compilers
  `loopCodegen` (`bb0: jmp 0`) and `unwindCodegen` (`bb0: abortPanic`) satisfy
  `X86Lang.WellFormed`, `EnsuresRetLibInv`, `EnsuresEqArg`, and `EnsuresConst`
  for every `MirBody`, and naive async relaxation (`π_naive_async`) certifies
  `loopCodegen` as a valid compilation of every well-formed `MirBody`. Because
  `ReachesPrefix.terminated` is parameterized over arbitrary remaining fuel
  `n : Nat`, terminal outcomes are **fuel-absorbing**: once a source execution
  terminates at budget $m_0$, its outcome remains `.terminated term` for all
  $m \ge m_0$ (`reachesPrefix_terminated_mono`). Exploiting fuel absorption,
  **step-dilated prefix simulation** (`π_dilated k`) relates target step budget
  $n$ to source budgets $m$ in `DilationWindow k m n` ($(m = 0 \land n = 0)
  \lor (n \le k \cdot m \land m \le n)$). Proved 100% constructively (relying
  solely on `[propext]`, with zero `Classical.choice` and zero coinduction),
  `π_dilated k` is `Monotone`, rejects `loopCodegen` and `unwindCodegen` on
  terminating programs for all $k \ge 1$, admits $1 \to [1..k]$ instruction
  expansion (`idCopyX86_2x`, which lockstep `Compiles` rejects), and admits
  genuine source loops and unwinds.
- **`x86_64-linux` Hardware Differential Audit of `X86Semantics.lean` and
  `render_x86_assembly`:** Executing `support/x86_conformance_probe.c` on
  `x86_64-unknown-linux-gnu` silicon and auditing `MIR-to-x86-64 prototype` at commit
  `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)` establishes that:
  1. `Trusted.CrateTheorem` is stated purely over `X86Lang` and
     `AssemblerCompiler` without referencing `MirSemantics`, and
     `MirLemmas.lean` uses `compileStage0` only as an AST macro without
     invoking `compileStage0_compiles`.
  2. `evalX86BinOp` (`Trusted/X86Semantics.lean:207-230`, as well as
     `evalBinOp` in `Trusted/MirSemantics.lean:207-230`) models 64-bit registers
     as unbounded `Nat`, producing Quadrant-2 fail-open divergences against
     hardware 64-bit modular arithmetic and shift masking (`0 - 1 = 0` vs.
     `0xffffffffffffffff`, `(2^64 - 1) + 1 = 2^64` vs. `0`, `1 <<< 64 = 2^64`
     vs. `1`, and `1 >>> 64 = 0` vs. `1`), while `X86State` omits `RFLAGS`,
     sub-register width rules, `div`/`idiv` `#DE` traps, and stack-frame bounds
     checks (`slot.index < active.slotCount`).
  3. `render_x86_assembly` (`trusted/rustc-capture/src/lib.rs:1742-1814`)
     violates `TCBItem.assemblerLowering` in three places: `CallSizeOf`
     hardcodes `mov QWORD PTR [rbp - dst], 8` regardless of `ty`,
     `CallTransmuteCopy` hardcodes a single 8-byte `mov rax, [rsi]` copy instead
     of `rep movsb` over `sizeof(Src)` bytes, and `Panic` emits `ud2` (`SIGILL`,
     modeled as `.failed .ub`) instead of `call abort`.

## Applicability

### Part I — Post-Monomorphization Error (PME) MIR Semantics and Polymorphic Conditional Contracts

The findings in this report apply to the combination of the five concrete
subjects recorded in `REPORT.json`:

- **Anneal verification framework (`joshlf/anneal` at
  `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)`):**
  Specifically the refinement lattice and `VerificationResultOn` envelope in
  `trusted/lean/Trusted/Refinement.lean`,
  the small-step prefix machine in
  `trusted/lean/Trusted/StepResult.lean`,
  the MIR AST and operational semantics in
  `trusted/lean/Trusted/MirAst.lean`
  and
  `trusted/lean/Trusted/MirSemantics.lean`,
  and the MIR extractor in
  `trusted/rustc-capture/src/lib.rs`.
- **Lean 4 theorem prover (`leanprover/lean4` at
  `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
  Used to elaborate and kernel-typecheck both standalone mechanizations with
  `-DElab.async=false -Ddebug.skipKernelTC=false`.
- **Rust compiler (`rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, `rustc 1.99.1`):**
  Examined across `compiler/rustc_middle`, `compiler/rustc_mir_build`,
  `compiler/rustc_mir_transform`, `compiler/rustc_monomorphize`, and
  `compiler/rustc_codegen_ssa`, and executed in empirical probes of
  `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`),
  `Runtime(Optimized)` MIR (`tcx.optimized_mir`), and `tcx.mir_for_ctfe`.
- **The Rust Reference (`rust-lang/reference` at
  `82da570bafd9efed421bdbae0f8603ede8dd308b`):**
  Normative rules for `const` block evaluation (`expression.block.const`),
  type layout properties (`layout.properties`), and reference validity
  (`undefined.validity.reference-box`).
- **`zerocopy` (`google/zerocopy` at
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`):**
  Specifically the `transmute_ref` and `static_assert!` compile-time size and
  alignment guard patterns in `src/util/macros.rs` and `src/lib.rs`.

Results concerning `Partial`, `Behavior`, `SmallStepMachine`, `ReachesPrefix`,
and the Model I / Model II equivalence are pure mathematical theorems in Lean 4 and hold
independently of host OS or target architecture. Results concerning `rustc` MIR
pass ordering, `Body::required_consts`, `Body::mentioned_items`, and
monomorphization root collection apply specifically to `rust-lang/rust` at
`58cf8f9c35b355199727627d07ae34a4e2846d67` under both `-Z mir-opt-level=0` and
default `-Z mir-opt-level=1`.

### Part II — Polar CTFE Admission, Step-Dilated Progress Preservation, and Four-Quadrant Semantic Polarity

This report applies to two immutable revisions of `joshlf/anneal`, the Lean 4
kernel (`v4.34.1`), and `x86_64-unknown-linux-gnu` user-space hardware
execution:

- **Subject 1 (`joshlf/anneal`, `StepResult-refinement baseline` worktree):** commit
  `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`, specifically
  `trusted/lean/Trusted/Refinement.lean`,
  `trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/MirAst.lean`,
  `trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/Refinement.lean`,
  `theory/Anneal/StepResult.lean`, and `theory/Anneal/MirLemmas.lean`.
- **Subject 2 (`joshlf/anneal`, `MIR-to-x86-64 prototype` worktree):** commit
  `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`, specifically
  `trusted/lean/Trusted/Refinement.lean`,
  `trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/X86Ast.lean`,
  `trusted/lean/Trusted/X86Semantics.lean`,
  `trusted/rustc-capture/src/lib.rs`, `theory/Anneal/MirAst.lean`,
  `theory/Anneal/MirSemantics.lean`, `theory/Anneal/Compiler/NaiveCodegen.lean`,
  `theory/Anneal/Compiler/Peephole.lean`, and `theory/Anneal/MirLemmas.lean`.
- **Subject 3 (`leanprover/lean4`):** commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), invoked with
  `-DElab.async=false -Ddebug.skipKernelTC=false` to force synchronous
  elaboration and full kernel type-checking.
- **Hardware execution environment:** `x86_64-unknown-linux-gnu` user-space
  execution compiled with `gcc -O2 -Wall -Wextra`.

The Four-Quadrant Semantic Polarity Matrix, the `ConstIsSafe` /
`SafePolarMirSem` / `MonoInhabitedSafe` polar CTFE architecture, and the
fuel-absorbing step-dilated prefix simulation `π_dilated k` (Findings 1, 2,
and 4) apply generally to any verification pipeline built on Anneal's
`Partial` and `ReachesPrefix` behavioral lattice. The 2-place vs. 4-place
`RequiresConst` analysis (Finding 3) and the instruction-level and assembly
lowering audit (Finding 5) apply specifically to commits
`5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)` and
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`.

### Inlined Core Anneal Refinement and MIR Semantic Definitions

To keep this reference self-contained without depending on unmerged prototype branches or external worktrees, the exact Lean 4 definitions of the core refinement, small-step machine, ADT invariant admissibility, interprocedural call, boolean AST equality, and crate-level verification judgments referenced across this report are reproduced below (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `theory/Anneal/MirLemmas.lean`):

```lean
/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` exactly when the computation exhibits undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language with program-indexed initial-state domain `dom`. -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  sem   : Prog → Behavior Query Out
  dom   : Prog → Query → Prop

/-- Domain-intersected precondition non-vacuity: some query is in `dom` *and*
satisfies `pre`. There is deliberately no "or `dom` is empty" alternative: an
empty domain is how a model limit at function entry shows up, so accepting it
would turn every such limit into vacuous verification. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against
`(pre, post)` within `prog`'s own domain `L.dom prog`. -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation with private constructor. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Obligation representing an explicit, unproved assumption (`prop := False`)
that can only be discharged when `id` appears in the crate's `waived` TCB list. -/
abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

/-- Waiver-aware verification judgment requiring distinct obligation IDs,
distinct waivers permitted by `policy`, and discharge of all unwaived obligations. -/
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))
```

```lean
/-- Admissibility of an ADT representation invariant `adtInv`
(`r[expr.struct.safety]`, `src/expressions/struct-expr.md`).
If safe code can build a struct directly (all fields public and safe), the
invariant must accept every structurally valid payload, in every state. -/
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (s : MirState) (payload : MirTy) (inner : MirVal),
      decl.payloadTy = some payload →
      inner.valid adts defaultAdtInv s 0 payload →
      adtInv decl.id inner

/-- Lowered MIR block terminators, including static single-argument calls
`Terminator.call1` referencing a `BodyId` in `Crate.bodies` (or a nested
`MirBody` in the recursive first-order variant). -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | panic
  | unwindResume
  | unwindTerminate
  | drop (place : Place) (target : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | switchIntGeneral (discr : Operand) (targets : List (Nat × BlockId))
      (otherwise : BlockId)
  | callSizeOf (dst : Place) (ty : MirTy) (target : BlockId)
  | callTransmuteCopy (dst : Place) (srcTy dstTy : MirTy) (op : Operand)
      (target : BlockId)
  | call1 (dst : Place) (callee : BodyId) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy := [])
  | call (dst : Place) (args : List Operand) (target : Option BlockId)
  | tailCall (args : List Operand)
  | yield (val : Operand) (resume : BlockId) (resumeArg : Place)
  | coroutineDrop
  | falseEdge (realTarget : BlockId) (imaginaryTarget : BlockId)
  | falseUnwind (realTarget : BlockId)
  | inlineAsm

/-- Per-function obligation inventory under `adts`, `bodies`, and `adtInv`. -/
def CapturedFn.obligations (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) : List (Obligation TCBItem) :=
  [
    Obligation.assumed (TCBItem.rustcLowering fn.name fn.bodyId),
    Obligation.wellFormedAndSpecsOn (TCBItem.fnVerified fn.name fn.bodyId)
      (MirLang adts bodies) (fn.effectivePre adts bodies adtInv)
      (fn.effectiveSpecs adts bodies adtInv) (fn.resolveBody bodies)
  ]

/-- Top-level theorem required of every verified Rust crate. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResult defaultTrustPolicy c.tcb
      (fn.obligations c.adts c.bodies c.adtInv)))
```

```lean
/-- Fuel-bounded structural boolean equality on recursive `MirBody` trees
(before flat `BodyId` indirection). -/
noncomputable def beqMirBodyFuel : Nat → MirBody → MirBody → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    listBeq beqMirTy a.argTys b.argTys &&
    beqMirTy a.retTy b.retTy &&
    a.localCount == b.localCount &&
    listBeq (beqBasicBlock (beqMirBodyFuel fuel)) a.blocks b.blocks &&
    listBeq (beqRcPair (beqMirBodyFuel fuel)) a.requiredConsts b.requiredConsts

/-- Fuel-free structural boolean equality on `MirBody`, enabled by flat `BodyId`
indirection in `Crate.bodies`. -/
def beqMirBody (a b : MirBody) : Bool :=
  listBeq beqMirTy a.argTys b.argTys &&
  beqMirTy a.retTy b.retTy &&
  a.localCount == b.localCount &&
  listBeq beqBasicBlock a.blocks b.blocks &&
  listBeq beqRcPair a.requiredConsts b.requiredConsts
```

## Findings

### Part I — Post-Monomorphization Error (PME) MIR Semantics and Polymorphic Conditional Contracts

#### 1. How `rustc` Lowers and Evaluates PMEs Across the MIR Pipeline

`Basis: normative + source + execution`

According to the Rust Reference
([`src/expressions/block-expr.md`](https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions/block-expr.md),
rule `expression.block.const`), whether an inline `const { ... }` block inside
a generic item is evaluated depends on whether the enclosing item is
monomorphized and whether the `const` block is reachable in the MIR control-flow
graph prior to constant-evaluation collection.

In `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, PME obligations
pass through four stages between MIR construction and code generation:

1. **Reachable constant collection in `mir_promoted`:**
   In [`compiler/rustc_mir_transform/src/lib.rs (lines 473-476)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs),
   `RequiredConstsVisitor::compute_required_consts`
   ([`compiler/rustc_mir_transform/src/required_consts.rs (lines 9-23)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/required_consts.rs))
   traverses `body` in `traversal::reverse_postorder(body)` from `START_BLOCK`
   (`bb0`) and records every `ConstOperand` whose `const_.is_required_const()`
   is `true` (`Const::Unevaluated`, covering both inline `const { ... }`
   blocks `fn_name::{constant#k}` and associated constants `<T as Trait>::C`)
   into `body.required_consts`.
2. **Mentioned-item collection at the entry to `inner_optimized_mir`:**
   In [`compiler/rustc_mir_transform/src/lib.rs (lines 808-819)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs),
   before optimization passes fold constant branches, `MentionedItemsVisitor`
   ([`compiler/rustc_mir_transform/src/mentioned_items.rs (lines 40-85)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/mentioned_items.rs))
   records zero-sized function items (`MentionedItem::Fn`), drop types, and
   unsizing casts in `body.mentioned_items` so monomorphization still evaluates
   a callee's `required_consts` even if dead-code optimizations later delete
   the call terminator.
3. **Runtime cleanup and dead-store elimination:**
   During `run_analysis_to_runtime_passes` and `run_runtime_cleanup_passes`
   ([`compiler/rustc_mir_transform/src/lib.rs (lines 653-693)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs)),
   `RemovePlaceMention` and `RemoveZsts` strip place mentions, and in
   `Runtime(Optimized)` (`-Z mir-opt-level >= 1`), dead-store elimination
   deletes unit-typed assignments `_2 = const fn_name::{constant#0};` from
   `body.basic_blocks` completely. Consequently, in optimized MIR the runtime
   basic blocks contain no reference to `{constant#0}`, and the assertion logic
   lives exclusively in `body.required_consts` and its separate CTFE MIR body
   `tcx.mir_for_ctfe(def_id)`.
4. **Monomorphization-time evaluation in `collect_items_of_instance`:**
   In [`compiler/rustc_monomorphize/src/collector.rs (lines 1364-1389)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs),
   `collect_items_of_instance` substitutes the concrete `Instance<'tcx>`
   arguments into each entry of `body.required_consts()`, evaluates it via
   `constant.eval(tcx, ty::TypingEnv::fully_monomorphized(), span)`, emits
   `error[E0080]` if CTFE panics or fails, and recursively traverses
   `body.mentioned_items()` in `CollectionMode::MentionedItems` to evaluate
   transitive `required_consts`.

#### 2. Dead Branches (`if false`, `match false`) vs. Post-Divergence (`return;`)

`Basis: source + execution`

A critical distinction governs which syntactically unreachable PMEs `rustc`
evaluates and which it discards:

- **All conditional branches (`if false`, `match false`, `if (const { false })`,
  `let b = false; if b`) retain CFG edges in `mir_built` and trigger PMEs:**
  When `Builder::expr_into_dest` lowers `ExprKind::If`
  ([`compiler/rustc_mir_build/src/builder/expr/into.rs (lines 61-126)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/into.rs)),
  `Builder::lower_if_condition`
  ([`compiler/rustc_mir_build/src/builder/matches/mod.rs (lines 206-214)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs))
  materializes the condition into a temporary local (`_1 = const false;`) and
  terminates `bb0` with
  `TerminatorKind::if_(Operand::Move(scrutinee), then_blk, else_blk)`
  (`switchInt(move _1) -> [0: else_blk, otherwise: then_blk]`). Similarly,
  `Builder::perform_test` for `ExprKind::Match` on a `bool` scrutinee
  ([`compiler/rustc_mir_build/src/builder/matches/test.rs (lines 136-141)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/test.rs))
  emits the same `TerminatorKind::if_`.
  When `SimplifyCfg::Initial` runs at the end of `mir_built`
  ([`compiler/rustc_mir_transform/src/lib.rs (line 422)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs)),
  `CfgSimplifier::simplify_branch`
  ([`compiler/rustc_mir_transform/src/simplify.rs (lines 250-272)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs))
  never inspects the constant value of a `SwitchInt` operand; folding constant
  `SwitchInt` discriminants is performed only by
  `SimplifyConstCondition::{AfterConstProp, Final}`
  ([`compiler/rustc_mir_transform/src/simplify_branches.rs (lines 30-98)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify_branches.rs))
  inside `run_optimization_passes` (`-Z mir-opt-level >= 1`), which runs
  *after* `mir_promoted` (`RequiredConstsVisitor`) and *after*
  `MentionedItems`.
- **Statements after unconditional divergence (`return;`, `break;`,
  `continue;`, `loop {}` without `break`) have zero CFG predecessors and are
  stripped before `mir_promoted`:**
  When `Builder::stmt_expr` lowers `ExprKind::Ret`, `ExprKind::Break`, or
  `ExprKind::Continue`
  ([`compiler/rustc_mir_build/src/builder/expr/stmt.rs (lines 96-107)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/stmt.rs)),
  `Builder::break_scope`
  ([`compiler/rustc_mir_build/src/builder/scope.rs (lines 823-830)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs))
  terminates the current block and returns `self.cfg.start_new_block().unit()`,
  a freshly allocated basic block with **zero incoming CFG edges**. Likewise,
  `Builder::in_breakable_scope` for a `loop {}` without `break`
  ([`compiler/rustc_mir_build/src/builder/scope.rs (lines 563-565)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs))
  allocates an unreachable exit block via `self.cfg.start_new_block()`.
  `SimplifyCfg::Initial` calls `remove_dead_blocks(body)`
  ([`compiler/rustc_mir_transform/src/simplify.rs (line 87)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs)),
  deleting those zero-predecessor blocks before `mir_promoted` runs.

| Construct with Failing Payload (`N = 2000`) | Predecessors in `mir_built` | Survives `SimplifyCfg::Initial`? | Recorded in `required_consts` / `mentioned_items`? | `rustc --emit=obj` Result |
| :--- | :--- | :--- | :--- | :--- |
| `if false { const { assert!(N <= 1000); } }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `if false { fail_const::<N>(); }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`mentioned_items`) | Fails (`error[E0080]`) |
| `match false { true => const { assert!(N <= 1000); }, false => () }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `match false { true => fail_const::<N>(), false => () }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`mentioned_items`) | Fails (`error[E0080]`) |
| `if (const { false }) { const { assert!(N <= 1000); } }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `let b = false; if b { const { assert!(N <= 1000); } }` | 1 (`bb0` via `SwitchInt`) | Yes (`bb1`) | Yes (`required_consts`) | Fails (`error[E0080]`) |
| `return; const { assert!(N <= 1000); };` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `return; fail_const::<N>();` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `loop { break; const { assert!(N <= 1000); }; }` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `while false { continue; const { assert!(N <= 1000); }; }` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |
| `loop {} const { assert!(N <= 1000); };` | 0 (`start_new_block`) | No (deleted) | No | Compiles (`exit code 0`) |

Because `Runtime(PostCleanup)` MIR
(`tcx.mir_drops_elaborated_and_const_checked`) is captured *after*
`SimplifyCfg::Initial` and *before* `SimplifyConstCondition`, its basic blocks
match the exact reachability horizon of `RequiredConstsVisitor` and
`MentionedItems`. Furthermore, because HIR lowering allocates a `LocalDefId` in
`tcx.mir_keys(())` even for an unreachable post-`return` `const { ... }` block,
`anneal-rustc-capture` must never attach an `InlineConst` item to a parent
function merely because its `DefId` or `--emit=mir` symbol prefix exists; a
constant body is a PME obligation of `f` if and only if `f`'s
`required_consts()` (or `Runtime(PostCleanup)` basic blocks) references it.

#### 3. Single-Interpreter Model of PMEs (`ConstMirMachine`, `CompileAdmitted`)

`Basis: source + execution + derived`

In [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean), `MirBody` is extended
with `requiredConsts : List ConstMirBody` and `requiredLayouts : List TyLayout`,
where each `ConstMirBody` (`localCount : Nat`, `blocks : List BasicBlock`) uses
the exact same `BasicBlock`, `Stmt`, `Rvalue`, and `Terminator` AST as runtime
`MirBody`:

- **Shared small-step transition function (`evalBlocksStep`):**
  Both `MirMachine`
  ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) and `ConstMirMachine`
  ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) execute
  `evalBlocksStep blocks s`
  ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)). `ConstMirMachine`
  starts from `initCtfeState` (`locals := fun _ => none`,
  `mem := MemState.empty`, `block := 0`, `stmtIdx := 0`).
- **CTFE admissibility (`CtfeAdmitted` and `MirBody.CompileAdmitted`):**
  A constant body `c : ConstMirBody` satisfies `CtfeAdmitted c`
  ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) when:
  1. Every finite execution prefix from `initCtfeState` is safe (`out.isSafe`,
     ruling out `.failed .contractViolation` from `Terminator.panic` /
     `Terminator.assertNotOverflow` and `.failed .ub`), and
  2. There exists a finite step budget `steps` reaching
     `.terminated (.normal .unit)` (ruling out CTFE non-termination such as
     `const { loop {} }`, verified by `negative_control_const_loop_not_admitted`
     in [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)).
  A function body satisfies `body.CompileAdmitted`
  ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) when
  `AllHold (body.requiredConsts.map CtfeAdmitted)` and
  `AllHold (body.requiredLayouts.map TyLayout.WellFormed)` hold.

#### 4. Why `rustc --crate-type=lib` Does Not Guarantee `CompileAdmitted`

`Basis: source + execution`

Inspecting `rustc_monomorphize::collector`
([`compiler/rustc_monomorphize/src/collector.rs (lines 1753-1792)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs))
and `rustc_codegen_ssa::back::symbol_export`
([`compiler/rustc_codegen_ssa/src/back/symbol_export.rs (lines 114-118)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/back/symbol_export.rs))
establishes three classes of functions for which `rustc --crate-type=lib` exits
with status `0` even when the function contains an unconditionally failing PME:

1. **Generic functions (`requires_monomorphization == true`):**
   `RootCollector::is_root` (`collector.rs:1754`) requires
   `!self.tcx.generics_of(def_id).requires_monomorphization(self.tcx)`. An
   uninstantiated generic function
   `pub fn broken<T>(x: T) -> T { const { assert!(false); } x }` is never
   collected in `--crate-type=lib`.
2. **Unreachable private non-generic functions
   (`is_reachable_non_generic == false`):**
   Under default `MonoItemCollectionStrategy::Lazy` (`collector.rs:1768-1778`),
   a private non-generic function
   `fn dead() -> usize { const_bounded_add::<2000>(5) }` is not reachable from
   any exported symbol and is skipped during monomorphization.
3. **Cross-crate inlinable public non-generic functions (`#[inline]` or
   `-C opt-level=2`):**
   In `reachable_non_generics_helper` (`symbol_export.rs:114-118`), `rustc`
   excludes any non-generic function where `instance.def.requires_inline(tcx)`
   or `tcx.cross_crate_inlinable(def_id)` holds. Consequently, a **public,
   non-generic** function
   `#[inline] pub fn call_top() -> usize { const_bounded_add::<2000>(5) }`
   (or an unannotated `pub fn` compiled with `--crate-type=lib -C opt-level=2`)
   has `is_reachable_non_generic == false`, is skipped by `RootCollector`, and
   compiles with exit code `0`, deferring the `error[E0080]` failure until a
   downstream crate codegens a call to it.

Anneal therefore cannot rely on `rustc`'s exit status to establish
`CompileAdmitted`; concrete functions require `ConcreteVerifiedAndAdmitted`
([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) and generic functions
certifying an explicit compilation domain require `GenericVerifiedWithDomain`
([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)).

#### 5. Approach 1 (`PartialCompiler`) vs. Approach 2 (`MirMachine.withAdmitted`)

`Basis: execution + derived`

In `Behavior Query Out := Query → Partial (Out → Prop)`, `Partial (Out → Prop)`
has both a top element `Partial.ub` (`defined := False`, used by `SpecOn`
outside `pre q`) and a bottom element `Partial.bot` (`defined := True`,
`val := fun _ _ => False`, representing zero runtime executions; see `bot_le`
and `le_ub` in [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)).

Defining the program-side compile-time gate `Behavior.when P b` and the
specification-side compile-time guard `Behavior.given P spec` purely
constructively (without `Classical.propDecidable`):

```lean
def Behavior.when (P : Prop) (b : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P → (b q).defined
    val := fun hdef out => ∃ hP : P, (b q).val (hdef hP) out
  }

def Behavior.given (P : Prop) (spec : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun hdef out => (spec q).val hdef.2 out
  }
```

yields the constructive Galois connection `Behavior.when P ⊣ Behavior.given P`
([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean), proved using **zero
axioms**, not even `propext`):

```text
Behavior.when P b ≤ spec  ↔  (P → b ≤ spec)  ↔  b ≤ Behavior.given P spec
```

This adjunction relates the two candidate ways of integrating `CompileAdmitted`
into Anneal:

- **Approach 1 (`PartialCompiler` at the TCB boundary,
  [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)):**
  Keeps `MirMachine` and `MirSem body` as pure runtime operational semantics.
  `PartialCompiler` models `compile : L_src.Prog → Partial L_tgt.Prog`, and
  `PartialCompiler.SoundOn` asserts both
  `(C.compile body).defined → body.CompileAdmitted` (compile-time PME gate
  soundness) and target lowering soundness for `(C.compile body).val h`.
  Equivalently, in
  [support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean),
  pairing `MonoMirLang.sem u` (where `defined` is
  `u.pmeOk ∧ (MirLang.sem u.body q).defined`) and
  `PartialTargetLang.sem := semTotalCompiled` embeds partial compilation
  directly into the existing `Trusted.Compiler` structure with zero changes to
  `Trusted/Refinement.lean`, where
  `verifiedTotal_iff_noPme_and_verifiedIfCompiled` proves that total
  verification is constructively equivalent to `NoPME` paired with
  `VerifiedIfCompiled`.
- **Approach 2 (`SmallStepMachine.withAdmitted`,
  [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean) and
  [ (lines 1273-1315)](support/PmeMirSemantics.lean)):**
  Defines `(M.withAdmitted Admitted).initState p s` as
  `Admitted p ∧ M.initState p s` while leaving `M.step` unchanged. Because
  `TotalStep M`, `InhabitedDemonic M`, and `ReachesPrefix M` depend only on
  `M.step`, gating `initState` preserves `TotalStep` (`totalStep_withAdmitted`),
  `InhabitedDemonic` (`inhabitedDemonic_withAdmitted`), and
  `non_vacuity_at_every_depth` identically. At the behavior level,
  `BehaviorOf (M.withAdmitted Admitted) p` is order-isomorphic to
  `Behavior.when (Admitted p) (BehaviorOf M p)`
  (`behaviorOf_withAdmitted_le_when`,
  `behavior_when_le_behaviorOf_withAdmitted`), yielding the universal
  equivalence (`mirSemAdmitted_le_iff`,
  [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)):
  ```lean
  theorem mirSemAdmitted_le_iff (body : MirBody) (spec : MirLang.Behavior) :
      MirSemAdmitted body ≤ spec ↔ (body.CompileAdmitted → MirSem body ≤ spec)
  ```

| Criterion | Approach 1 (`PartialCompiler` / `MonoMirLang` in `trusted/`) | Approach 2 (`MirMachineAdmitted` in `trusted/`) |
| :--- | :--- | :--- |
| **Trust-boundary clarity (`PRINCIPLES.md`)** | Separates compile-time PME rejection (`compile`) from runtime operational semantics (`MirSem`). | Conflates compile-time rejection with a runtime machine that has zero initial states (`Partial.bot`), allowing an uncompilable program to refine `SpecOn (fun _ => True) (fun _ _ => False)`. |
| **Interprocedural calls (`Call` terminator)** | `CompileAdmitted` is transitively closed over `mentioned_items`, matching `rustc_monomorphize::collector`. | Delegating a runtime `Call` to `MirSemAdmitted callee` without closing `caller.CompileAdmitted` over `mentioned_items` turns an uncompilable callee inside a runtime branch into a runtime `assume(false)` miracle. |
| **Proof ergonomics** | Proof authors assume `hAdm : body.CompileAdmitted` directly in `hAdm → MirSem body ≤ spec`. | Constructively equivalent via `mirSemAdmitted_le_iff` in `theory/`. |

#### 6. Case Studies: `const_bounded_add<N>` and `zerocopy::transmute_ref`

`Basis: source + execution`

Section 5 of [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean) mechanizes
two canonical PME patterns and four negative controls end-to-end:

1. **`const_bounded_add<const N: usize>(x: usize) -> usize`
   ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)):**
   The runtime body `constBoundedAddBody N` branches on `x <= 1000` and computes
   `CheckedBinOp.add` (`x + N`) guarded by `Terminator.assertNotOverflow`, while
   `requiredConsts := [constBoundedAddConst0 N]` checks `N <= 1000` in CTFE.
   - `constBoundedAdd_compileAdmitted_iff` proves
     `(constBoundedAddBody N).CompileAdmitted ↔ N ≤ 1000`.
   - `constBoundedAdd_source_verified` proves that
     `(constBoundedAddBody N).CompileAdmitted` implies
     `MirSem (constBoundedAddBody N) ≤ EnsuresConstBoundedAdd N`
     for all `N : Nat` with caller precondition `pre := fun _ => True` (because
     `x0 ≤ 1000` and `N ≤ 1000` imply `x0 + N ≤ 2000 ≤ usizeMax`).
   - `constBoundedAdd_generic_verified_with_domain` establishes
     `GenericVerifiedWithDomain` for `constBoundedAddBody` over `N ≤ 1000` and
     `EnsuresConstBoundedAdd`.
   - Negative controls prove `¬ (constBoundedAddBody 2000).CompileAdmitted`
     (`constBoundedAdd_2000_not_compileAdmitted`) and
     `¬ (MirSem (constBoundedAddBody usizeMax) ≤ MirLang.WellFormed)` when the
     PME gate is omitted (`constBoundedAdd_usizeMax_unguarded_runtime_fails`).
2. **`zerocopy`-style `transmute_ref<Src, Dst>(src: &Src) -> &Dst`
   ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)):**
   Models `zerocopy`'s safe reference transmutation
   (`&*(src as *const Src as *const Dst)`), whose runtime body executes
   `Rvalue.addrOfDeref`, `Rvalue.castPtrToPtr`, and `Rvalue.reborrowShared`
   with zero runtime branches. `evalMirStmt` on `.reborrowShared src dstLayout`
   ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) enforces Rust's
   reference validity invariant (`r[undefined.validity.reference-box]`:
   `addr ≠ 0`, `0 < dstLayout.align`, `dstLayout.align ∣ addr`, and
   `dstLayout.size ≤ s.mem.allocSize loc`), transitioning to `.failed .ub` if
   violated.
   - `transmuteRef_compileAdmitted_iff` proves that `transmuteRefBody src dst`
     is compile-time admissible if and only if `src.size = dst.size`,
     `dst.align ∣ src.align`, `src.WellFormed`, and `dst.WellFormed`.
   - `transmuteRef_source_verified` transfers reference validity from `src` to
     `dst` using `Nat.dvd_trans hAlignDvd hSrcAlignDvd` and `← hSizeEq`, proving
     `MirSem (transmuteRefBody src dst) ≤ EnsuresTransmuteRef src dst` with
     caller precondition `pre := fun _ => True`.
   - Four negative controls
     ([support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)) prove that:
     - omitting the PME (`transmuteRefNoPmeBody u8Layout u64Layout`) makes the
       body compile-time admissible (`CompileAdmitted`) while triggering runtime
       `.failed .ub` on a 1-byte-aligned `&u8`
       (`negative_control_omitted_pme_rejected`);
     - placing the assertion in an unreached runtime branch (`if false`,
       `transmuteRefDeadBranchBody u8Layout u64Layout`) instead of
       `requiredConsts` fails verification
       (`negative_control_dead_branch_assertion_rejected`);
     - `pub fn broken() { const { assert!(false) }; }` fails `CompileAdmitted`
       and `ConcreteVerifiedAndAdmitted`
       (`negative_control_const_assert_false_not_admitted`); and
     - `pub fn broken_loop() { const { loop {} }; }` fails `CompileAdmitted`
       because every step budget `n` evaluates to `.running`
       (`negative_control_const_loop_not_admitted`).

#### 7. Polymorphic Contracts: `InstCtx` and the Model I vs. Model II Analysis

`Basis: source + execution + derived`

A polymorphic public Rust function
`pub fn checked<T: Bound, const N: usize>(x: usize) -> usize` cannot be modeled
as a single unparameterized `MirBody` because four semantic inputs depend on the
monomorphization context `inst : InstCtx` (`rustc_middle::ty::Instance<'tcx>`):

1. **Concrete post-monomorphization layouts (`layoutValid`):** `tcx.layout_of`
   requires concrete type substitutions and can fail during monomorphization if
   a composite size exceeds `isize::MAX`.
2. **Substituted const generic operands (`constN`):** Const generic parameters
   appear as `Operand.constVal` inside MIR statements and `requiredConsts`.
3. **Caller-supplied trait implementations and `LIB-07` semantic contracts
   (`boundTraitContract`):** Associated constants (`<T as Bound>::LIMIT`) and
   trait methods (`<T as Bound>::delta()`) resolve via `Instance::try_resolve`
   against the caller's `impl Bound for T`. While `rustc` checks trait *type*
   conformance, sound verification requires the caller's `impl` to satisfy the
   trait's *semantic* contract (`delta() <= LIMIT ∧ LIMIT <= 1000`).
4. **Monomorphized `Body::required_consts` (`checkedPmeOk`):** Evaluating
   `const { assert!(N <= <T as Bound>::LIMIT); }` depends on both `N` and
   `<T as Bound>::LIMIT`.

In
[support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean),
we compare two representations under `model-refinement`:

- **Representation Model I (`PolyCapturedFnR1 InstCtx`,
  [support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean)):**
  Models a generic function as an `InstCtx`-indexed family of `MonoMirUnit`s and
  quantifies over `inst : InstCtx` outside `VerificationResultOn`, keeping
  `MirLang.Query := ExecQuery MirState` and scoping
  `tcb : InstCtx → List TCBItem` per monomorphized instance.
- **Representation Model II (`PolyMirLang InstCtx`,
  [support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean)):**
  Enriches `Language.Query` to
  `PolyQuery InstCtx := InstCtx × ExecQuery MirState` so that instantiation
  preconditions (`instPre`, `noPmePre`) and runtime argument preconditions
  (`argPre`) are both predicates on `PolyQuery InstCtx` inside the unchanged
  `VerificationResultOn` envelope.
- **Two-Pass `model-refinement` Boundary Discovery:**
  - *Pass 1 (Counterexample to naive Model II precondition merging):* Merging
    `instPre`, `noPmePre`, and `argPre` into the naive conjunction
    `naiveTotalPre` (`instPre inst ∧ noPmePre inst ∧ argPre inst q`)
    couples compile-time PME-freedom (`(prog inst).pmeOk`) to the existence of a
    runtime query `q` satisfying `argPre inst q`. Theorem
    `naive_r2_vacuous_argPre_counterexample`
    ([support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean))
    proves that `brokenPmeProg` (`pmeOk := False`) vacuously satisfies
    `WellFormedOn (naiveTotalPre ...)` whenever `argPre` is `fun _ _ => False`,
    even though `rustc` evaluates `Body::required_consts` during
    monomorphization regardless of runtime arguments
    (`brokenPmeProg_not_compiled`).
  - *Pass 2 (0-step compile-time query resolution):* In `Trusted.StepResult`,
    `q.steps = 0` represents 0 runtime transition steps, where
    `ReachesPrefix.zero` is the unique derivation and
    `(MirLang.sem body ⟨init, 0⟩).defined` is unconditionally `True`
    (`behaviorOf_defined_at_zero`,
    [support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean)).
    At `q.steps = 0`, `(PolyMirLang.sem prog ⟨inst, ⟨init, 0⟩⟩).defined`
    therefore reduces purely to `(prog inst).pmeOk`. Defining
    `unifiedTotalPre` as
    `instPre inst ∧ noPmePre inst ∧ (q.steps = 0 ∨ argPre inst q)`
    ([support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean))
    eliminates the vacuity defect
    (`refined_r2_rejects_pme_even_when_argPre_empty`,
    [ (lines 1149-1156)](support/PolymorphicConditionalVerification.lean)) and
    yields a constructive two-way equivalence (`↔`) with Model I
    (`r1_iff_r2_source_wellFormed`,
    [ (lines 994-1025)](support/PolymorphicConditionalVerification.lean)), while
    preserving monomorphic embedding (`mono_embeds_into_r2_iff`) and
    per-instance projection (`r2_projects_to_r1_instance`).

#### 8. Three-Way Polymorphic Library Guarantee and Cross-Crate Composition

`Basis: execution + derived`

Sections 6 and 7 of
[support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean)
mechanize `pub fn checked<T: Bound, const N: usize>(x: usize) -> usize` and its
cross-crate callers across all three verification guarantees and four negative
controls:

| Scenario / Theorem in `support/PolymorphicConditionalVerification.lean` | `LIB-07` (`boundTraitContract`) | PME Check (`N ≤ T::LIMIT`) | Runtime `argPre` (`x ≤ 1000`) | Mechanized Outcome |
| :--- | :--- | :--- | :--- | :--- |
| **Guarantee 1: Polymorphic Safety If Compiled** (`checked_polymorphic_safety_if_compiled_r1` ` (line 1480)`, `_r2` ` (line 1523)`) | Assumed (`h_trait`) | Assumed (`h_compiled` / `polyIfCompiledPre`) | Assumed (`checkedArgPre`) | Verified: UB-free across all `steps : Nat` and satisfies `checkedPost` (`ret = x0 + N + T::delta() ≤ x0 + 2 * T::LIMIT`). |
| **Guarantee 2: `NoPME` Sufficiency** (`checked_no_pme_r1` ` (line 1500)`, `_r2` ` (line 1548)`) | Assumed (`h_trait`) | Assumed (`checkedNoPmePre`: `N ≤ T::LIMIT`) | Not needed (`steps = 0`) | Verified: `(MonoRustcCompiler.compile (checkedUnit inst)).defined` holds (`NoPME`). |
| **Guarantee 3: Positive Cross-Crate Client (`client_good`)** (`checked::<TypeA, 1>(50)`, `LIMIT = 10, delta = 3`, `client_good_entry_verified` ` (line 1931)`) | Discharged (`3 ≤ 10 ≤ 1000`) | Discharged (`1 ≤ 10`, `NoPME`) | Discharged (`50 ≤ 1000`) | Verified modularly: derives `NoPME` and `VerificationResultOn` for `client_good::entry` (`ret = .usize 54`) from `checked_total_verified_r1` and `evalCheckedCallee_of_ensuresChecked` without re-proving `checkedMonoBody`. |
| **Negative Control 1: PME Violation (`client_bad_pme`)** (`checked::<TypeB, 1>(50)`, `LIMIT = 0, delta = 0`, `client_bad_entry_fails_to_compile_and_verify` ` (line 2004)`) | Holds (`0 ≤ 0 ≤ 1000`) | Fails (`1 ≰ 0`, PME) | Holds (`50 ≤ 1000`) | Refuted: `¬ (compile (checkedUnit instB1)).defined`, `¬ (compile (clientEntryUnit instB1)).defined`, and `¬ Verified`. |
| **Negative Control 2: `LIB-07` Trait Violation (`client_bad_trait`)** (`checked::<RogueType, 1>(50)`, `LIMIT = 10, delta = usizeMax`, `client_bad_trait_fails_at_runtime` ` (line 2046)`) | Fails (`usizeMax ≰ 10`) | Holds (`1 ≤ 10`, compiles without PME) | Holds (`50 ≤ 1000`) | Refuted: compiles without PME (`instRogue_compiles_without_pme`), but overflows in `bb1` at step 5 (`.failed .contractViolation`), refuting `WellFormedOn (checkedArgPre instRogue)`. |
| **Negative Control 3: Runtime Argument Violation (`client_bad_arg`)** (`checked::<TypeA, 1>(usizeMax)`, `client_bad_arg_refutes_unconditional_wellFormed` ` (line 2092)`) | Holds (`3 ≤ 10 ≤ 1000`) | Holds (`1 ≤ 10`, `NoPME`) | Fails (`usizeMax ≰ 1000`) | Refuted: overflows in `bb0` at step 2 (`.failed .contractViolation`), refuting unconditional `MonoMirLang.WellFormed`. |
| **Negative Control 4: Empty `argPre` with PME (`brokenPmeProg`)** (`refined_r2_rejects_pme_even_when_argPre_empty` ` (line 1149)`) | Holds (`True`) | Fails (`pmeOk = False`) | Empty (`False`) | Discriminates Model II preconditions: `naiveTotalPre` accepts vacuously (` (line 1139)`), whereas `unifiedTotalPre` rejects at `q.steps = 0`. |

### Part II — Polar CTFE Admission, Step-Dilated Progress Preservation, and Four-Quadrant Semantic Polarity

#### Finding 1: The Four-Quadrant Semantic Polarity Matrix and Two-Sided Sandwich Theorem

`Basis: source + execution + derived`

##### 1.1 Polarity in the Demonic `Partial` Refinement Lattice

In both `StepResult-refinement baseline` (`Trusted/Refinement.lean:43-88`) and `MIR-to-x86-64 prototype`
(`Trusted/Refinement.lean:45-62`), partial behaviors over an outcome carrier are
ordered by demonic refinement:

$$\mathsf{le}(a, b) \;\triangleq\; b.\mathsf{defined} \to \bigl(a.\mathsf{defined} \;\wedge\; \forall o,\; a.\mathsf{outcomes}\;o \to b.\mathsf{outcomes}\;o\bigr)$$

Under this order:
- `Partial.ub = ⟨False, ...⟩` is the **top element** $\top$: every computation
  refines `Partial.ub` (`Partial.le_ub`).
- `Partial.bot` / `Partial.magic = ⟨True, fun _ => False⟩` is the **bottom
  element** $\bot$: `Partial.bot` refines every computation.

For a small-step machine `M`, `BehaviorOf M p q` defines safety in `defined`
(requiring every reachable prefix outcome from an initial state `M.initState p
q.init` to satisfy `out.isSafe` / `¬ Reaches .failed`) and collects reachable
executions in `val` / `outcomes`. Consequently, whether an over- or
under-approximation in a language model is **fail-open** (unsound: admits
programs that fault or violate specifications at runtime) or **fail-closed**
(conservative: blocks verification of safe programs) depends on which of four
architectural positions the language occupies
(`support/SemanticPolarityAndCanaries.lean:190-527`):

| Quadrant | Architectural Position | Omitting Failure / Under-Approximating Nondeterminism | Adding Spurious Failure (`.failed`) | Adding Spurious Stuckness (`.stuck`) |
| :--- | :--- | :--- | :--- | :--- |
| **Q1: Trusted Source Language** (`StepResult-refinement baseline` `MirLang`) | LHS of `L_src.sem s ≤ SpecOn pre post` with unverified compiler in `hTcb` | **Fail-open (Unsound):** Lean proves `L_src.sem s ≤ spec`, while `rustc + LLVM` exploits the unmodeled UB (`q1_omitting_ub_is_fail_open`, `q1_omitting_nondet_is_fail_open`). | **Fail-closed:** `(L_src.sem s q).defined` becomes `False`, refuting `L_src.sem s ≤ SpecOn pre post` (`q1_spurious_ub_is_fail_closed`). | **Fail-closed** if `isSafe .stuck = False` (`BehaviorOf` in `PolarEvaluationAndProgress.lean`); **Fail-open** if `defined` checks only `¬ Reaches .failed` (`BehaviorOf` in `SemanticPolarityAndCanaries.lean`). |
| **Q2: Trusted Target ISA** (`MIR-to-x86-64 prototype` `X86Lang`) | LHS of `L_tgt.sem t ≤ spec_tgt` or `L_tgt.sem t ≤ π_c (L_src.sem s)` | **Fail-open (Unsound):** Lean proves the binary safe, while real silicon traps (`#DE`/`#GP`/`#UD`) or produces an unmodeled flag/register value (`q2_omitting_hw_trap_is_fail_open`, `q2_underapproximating_undef_flag_is_fail_open`). | **Fail-closed:** Rejects valid target instruction sequences by making `(L_tgt.sem t q).defined = False`. | **Fail-closed** if `isSafe .stuck = False`; **Fail-open** if `defined` checks only `¬ Reaches .failed` and `outcomes = ∅` ($\bot$). |
| **Q3: Intermediate / Source Language on RHS of Codegen** (`MirLang` in `Compiles MirLang X86Lang`) | RHS of `L_tgt.sem t ≤ π_c (L_src.sem s)` *without* source `SpecOn` | **Fail-closed for codegen:** Shrinks allowed target behaviors (`π_c (L_src.sem s)` moves down toward $\bot$). | **Fail-open (Unsound — Spurious-UB Codegen Exploit):** Makes `π_c (L_src.sem s) q = Partial.ub` ($\top$), so *any* broken target binary `t` (e.g., `ud2`) satisfies `Compiles` (`q3_spurious_ub_codegen_exploit`). **Neutralized by the Two-Sided Sandwich** (`q3_two_sided_sandwich_soundness`). | **Fail-closed for codegen** if `L_src` has no alternative trace (`outcomes = ∅` forces `L_tgt` to have `outcomes = ∅`). |
| **Q4: Premise / Admission Language** (`ConstMirMachine` in `MonoAdmitted`) | Negative-polarity premise inside `M.initState` (`StepResult-refinement baseline`) or `effectivePre` (`MIR-to-x86-64 prototype`) | **Fail-closed:** Admits *more* monomorphizations (`MonoAdmitted` holds more often), requiring runtime safety proofs over a superset of type sizes (`q4_omitting_ctfe_panic_is_fail_closed`). | **Fail-open (Unsound):** Causes `¬ ConstSucceeds` (`¬ MonoAdmitted`), shrinking `initMirState` or `effectivePre` to `False` ($\bot$) and **vacuously verifying** runtime-UB functions (`q4_spurious_ctfe_failure_vacuously_verifies_ub_in_initState`, `q4_spurious_ctfe_failure_vacuously_verifies_ub_in_effectivePre`). | **Fail-open (Unsound):** Because `ConstSucceeds` requires `∃ v, ReachesPrefix ... (.terminated (.normal v))`, stepping to `.stuck` falsifies `ConstSucceeds` identically to `.failed`, triggering the same vacuous-truth exploit! |

##### 1.2 The Quadrant-3 Spurious-UB Codegen Exploit and Two-Sided Sandwich Theorem

In `MIR-to-x86-64 prototype` at commit `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`,
`Trusted.CrateTheorem` (`Trusted/X86Semantics.lean:813-895`) is stated purely
over `X86Lang` and `AssemblerCompiler`:
- `CapturedFn.Verified` (`X86Semantics.lean:872-875`) unfolds to
  `AssemblerCompiler.Verified fn.prog fn.spec`, which requires
  `TCBValid [TCBItem.assemblerLowering]`, `X86Lang.sem fn.prog ≤ fn.spec`, and
  `∀ t, AssemblerCompiler.emits fn.prog t → Compiles X86Lang TargetLang id fn.prog t`.
- `Trusted/X86Semantics.lean` never imports `MirAst`, `MirSemantics`, or
  `NaiveCodegen`. In `trusted/rustc-capture/src/lib.rs:1435-1561`,
  `render_mir_lean_with_metadata` translates captured Rust MIR directly into
  `Trusted.X86Body` definitions inside `.anneal/Mir.lean` and emits raw
  assembly into `.anneal/Prog.s` via `render_x86_assembly`
  (`lib.rs:1589-1820`).
- Meanwhile, `theory/Anneal/MirLemmas.lean:43-44, 152-153, 526-529` uses
  `compileStage0` (`idCopyBody := compileStage0 idCopyMirBody`) purely as an
  AST macro and proves `X86Sem body ≤ ...` by unfolding `evalX86Step`, never
  calling `compileStage0_compiles`
  (`theory/Anneal/Compiler/NaiveCodegen.lean:821-857`).

If a verification pipeline instead proves `X86Sem x86Body ≤ spec_x86` by
chaining through an untrusted intermediate language `MirLang` in `theory/`,
proving `Compiles MirLang X86Lang π_stage0 mirBody x86Body` alone is vulnerable
to the **Quadrant-3 Spurious-UB Codegen Exploit**
(`q3_spurious_ub_codegen_exploit`,
`support/SemanticPolarityAndCanaries.lean:406-415`):
if `MirLang.sem s (decompileQ q)` declares spurious UB (`defined = False`),
then `(L_tgt.sem t_broken q).le (pullbackMorphism decompileQ decompileOut
(L_src.sem s) q)` holds trivially for every broken target program `t_broken`
(including `ud2`).

However, as mechanized in `q3_two_sided_sandwich_soundness`
(`support/SemanticPolarityAndCanaries.lean:427-447`), requiring **both**
`Compiles L_src L_tgt (pullbackMorphism decompileQ decompileOut) s t` and
`L_src.sem s ≤ L_src.SpecOn pre post` sandwiches `L_src.sem s`:

$$\mathsf{L\_tgt.sem}\;t \;\le\; \pi_c(\mathsf{L\_src.sem}\;s) \;\le\; \pi_c(\mathsf{L\_src.SpecOn}\;\mathit{pre}\;\mathit{post})$$

For every target query `q` satisfying `pre (decompileQ q)`:
1. `(L_src.sem s (decompileQ q)).defined` is **forced to hold** by `h_src_spec`,
   making the Quadrant-3 spurious-UB exploit impossible on `pre`.
2. By transitivity of `Sem.le`, `L_src.sem s` cancels out completely, yielding
   `L_tgt.sem t ≤ L_tgt.SpecOn (fun q => pre (decompileQ q)) (fun q o => post
   (decompileQ q) (decompileOut o))`.
3. **Residual TCB Boundary of the Sandwich:** Even when `L_src.sem` cancels out
   by transitivity, if the theorem in `CrateTheorem` is stated via
   `decompileQ` and `decompileOut` (or if `x86Body` is defined as
   `compileStage0 mirBody` rather than inspected directly against the emitted
   `.s` assembly), then `decompileQ`, `decompileOut`, and the correspondence
   between `x86Body` and `.anneal/Prog.s` remain trust-critical.

---

#### Finding 2: Negative-Polarity `.stuck` and `.failed` Fail-Open Inversion in `ConstSucceeds` / `MonoAdmitted` and the Polar CTFE Solution

`Basis: source + execution + derived`

##### 2.1 Exact Mechanism of the Negative-Polarity Inversion

In `Trusted/StepResult.lean` (`StepResult-refinement baseline` lines 53–57, 112–167),
`ReachesPrefix` maps a state with no outgoing transition (`noStep`) or an empty
nondeterministic branch set (`emptyChoice`) to `PrefixOutcome.stuck`, where
`PrefixOutcome.isSafe .stuck = False` and `PrefixOutcome.isSafe .failed =
False`. In `BehaviorOf M p`:

```lean
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
  }
```

When `p` is the runtime program on the left-hand side of `BehaviorOf M p ≤
Spec`, `ReachesPrefix M.step p` sits in **positive** polarity: if `p` reaches
`.stuck` or `.failed`, `out.isSafe` is `False` and verification fails closed.

However, in `Trusted/MirSemantics.lean` (`StepResult-refinement baseline` lines 585–613),
compile-time constant evaluation (`ConstSucceeds`) and monomorphization
admission (`MonoAdmitted`) are defined as:

```lean
def ConstSucceeds (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∃ (s₀ : MirState) (n : Nat) (tr : List Unit) (v : MirVal),
    s₀.tySizes = tySizes ∧
    initEntryState c s₀ ∧
    ReachesPrefix MirStep c n s₀ tr (.terminated (.normal v))

def MonoAdmitted (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c, RequiresConst tySizes body tySizes' c → ConstSucceeds tySizes' c

def initMirState (body : MirBody) (s : MirState) : Prop :=
  initEntryState body s ∧
  MonoAdmitted s.tySizes body
```

And in `MIR-to-x86-64 prototype` (`Trusted/X86Semantics.lean:815-828`), `SpecOn` places
`ConstSucceeds` inside `effectivePre` in `defined := effectivePre q.init`. In
both architectures, `ConstSucceeds` sits in **negative (premise) polarity**:
1. Inside `ConstSucceeds`, `ReachesPrefix` is tested for equality with
   `.terminated (.normal v)`. A legitimate PME panic (`.terminated .unwind`),
   an unmodeled statement reaching `.stuck`, and an unmodeled sub-case or CTFE
   UB reaching `.failed` (such as `evalBinOp` on `.bytes` or `.adt` operands
   returning `none` in `Trusted/MirSemantics.lean:296-302`, which `evalMirStmt`
   maps to `StepResult.failed`) **all** make `ConstSucceeds tySizes c` evaluate
   to `False`.
2. When `MonoAdmitted` becomes `False`, `initMirState body s` becomes `False`
   (collapsing `MirSem body q` to `Partial.bot`) or `effectivePre q.init`
   becomes `False` (collapsing `SpecOn` to `Partial.ub`).
3. Because `Partial.bot ≤ S` and `B ≤ Partial.ub` hold trivially for all `S`
   and `B`, any unmodeled CTFE construct or CTFE failure silently excludes the
   monomorphization and vacuously certifies runtime UB!

In `support/PolarEvaluationAndProgress.lean` (lines 753–872), we mechanize:
- `unmodeledConst : MirBody` (lines 753–761), whose `bb0` executes
  `Stmt.unmodeled` (stepping to `.stuck` via `ReachesPrefix.noStep`), and
  `buggyRuntimeFn : MirBody` (lines 766–774), whose runtime `bb0` immediately
  executes `Terminator.unreachable` with `requiredConsts := [unmodeledConst]`.
- `unmodeledConst_rejected_in_positive_position` (lines 778–800):
  `¬ (MirSem unmodeledConst ≤ MirLang.WellFormed)`.
- `buggyRuntimeFn_sem_eq_bot` (lines 844–853) and
  `buggyRuntimeFn_vacuously_satisfies_false_spec` (lines 860–871):
  `MirSem buggyRuntimeFn ≤ MirLang.WellFormed ∧ MirSem buggyRuntimeFn ≤
  MirLang.Spec (fun _ _ => False)`.

##### 2.2 Why `non_vacuity_at_every_depth`, Entry Inhabitation, and `ConstNoStuck` Are Insufficient

1. **Why `non_vacuity_at_every_depth` missed empty `initMirState`:** In
   `theory/Anneal/StepResult.lean` (`StepResult-refinement baseline` lines 25–106), `TotalStep M`
   and `InhabitedDemonic M` constrain only `M.step`, while
   `non_vacuity_at_every_depth` assumes `(h_init : M.initState p init)` as an
   explicit hypothesis rather than requiring `∃ init, M.initState p init`. In
   `totalStep_and_inhabitedDemonic_do_not_catch_empty_initState`
   (`support/PolarEvaluationAndProgress.lean:993-1004`), we prove on the
   deterministic machine `MirMachineDet` that `TotalStep MirMachineDet` and
   `InhabitedDemonic MirMachineDet` hold globally, yet `¬ ∃ s,
   MirMachineDet.initState buggyRuntimeFn s` and `MirLangDet.sem buggyRuntimeFn
   ≤ MirLangDet.Spec (fun _ _ => False)`.
2. **Why entry-state inhabitation (`∃ s, initMirState body s`) is
   insufficient:** Consider `transmuteWithFakePme`
   (`support/PolarEvaluationAndProgress.lean:1178-1188`),
   guarded by `partiallyUnmodeledConst` (lines 1143–1157), which returns
   `MirVal.unit` when `tySizes 0 = 8` and hits `Stmt.unmodeled` (`.stuck`) when
   `tySizes 0 ≠ 8`. We prove in `transmuteWithFakePme_initMirState_inhabited`
   (lines 1253–1307) that `∃ s, initMirState transmuteWithFakePme s` **holds**
   (witnessed at `tySizes = fun _ => 8`), yet at `tySizes = fun _ => 4` it
   reaches `.stuck`, making `ConstSucceeds` false and masking the
   size-mismatched `transmute_copy` UB at `tySizes 0 = 4`!
3. **Why `ConstNoStuck` (`out ≠ .stuck`) alone is insufficient:** In
   `Trusted/MirSemantics.lean` (lines 296–302, 497–571), unmodeled sub-cases of
   modeled instructions—such as `evalBinOp .eq (.bytes 8 0) (.bytes 8 0) =
   none`—step to `StepResult.failed` (`PrefixOutcome.failed`) rather than
   `.stuck`. Because `PrefixOutcome.failed ≠ PrefixOutcome.stuck`, a constant
   `partiallyFailedConst` (`support/PolarEvaluationAndProgress.lean:3880-3908`)
   that returns `.unit` at `tySizes 0 = 8` and executes an unmodeled `.bytes`
   comparison (`.failed`) at `tySizes 0 ≠ 8` satisfies `ConstNoStuck` for
   **every** `tySizes` (`partiallyFailedConst_constNoStuck`, lines 3911–3962),
   allowing `transmuteWithFailedConst` to pass both `PolarMirSem ≤
   MirLang.WellFormed` and `MonoInhabited`
   (`transmuteWithFailedConst_passes_polarMirSem_and_monoInhabited`, lines
   4101–4241) despite runtime UB at `tySizes 0 = 4`!

##### 2.3 Complete Closure via `ConstIsSafe`, `SafePolarMirSem`, and `MonoInhabitedSafe`

How does Rust CTFE distinguish a legitimate post-monomorphization error (`const
{ assert!(size_of::<Src>() == 8) }`) from CTFE UB or an unmodeled CTFE
construct?
- An explicit PME `const { assert!(...) }` lowers in MIR to a conditional branch
  into `core::panicking::panic` (`Terminator.panic`), which terminates with
  **`StepResult.terminated .unwind`** (`PrefixOutcome.terminated .unwind`).
- By contrast, both CTFE UB and unmodeled sub-cases (`evalBinOp` returning
  `none`) step to **`PrefixOutcome.failed`**, and unmodeled statements step to
  **`PrefixOutcome.stuck`**.

`PrefixOutcome.isSafe` (`Trusted/StepResult.lean:53-57`) already carves out this
exact boundary (`.running ↦ True`, `.terminated (.normal _) ↦ True`,
`.terminated .unwind ↦ True`, `.failed ↦ False`, `.stuck ↦ False`). Defining
`ConstIsSafe`, `BodyConstsSafe`, `MonoAdmittedSafe`, `SafePolarMirSem`, and
`MonoInhabitedSafe` (`support/PolarEvaluationAndProgress.lean:4248-4282`):

```lean
def ConstIsSafe (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∀ (s₀ : MirState) (n : Nat) (tr : List Unit) (out : PrefixOutcome MirVal),
    s₀.tySizes = tySizes →
    initEntryState c s₀ →
    ReachesPrefix MirStep c n s₀ tr out →
    out.isSafe

def BodyConstsSafe (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c, RequiresConst tySizes body tySizes' c → ConstIsSafe tySizes' c

def MonoAdmittedSafe (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c,
    RequiresConst tySizes body tySizes' c →
    (ConstIsSafe tySizes' c → ConstSucceeds tySizes' c)

def SafePolarMirSem (body : MirBody) : MirLang.Behavior :=
  fun q => {
    defined :=
      initEntryState body q.init →
        BodyConstsSafe q.init.tySizes body ∧
        (MonoAdmittedSafe q.init.tySizes body →
          ∀ tr out,
            ReachesPrefix MirStep body q.steps q.init tr out →
            out.isSafe)
    val := fun _ out =>
      initEntryState body q.init ∧
      MonoAdmittedSafe q.init.tySizes body ∧
      ReachesPrefix MirStep body q.steps q.init out.trace out.outcome
  }

def MonoInhabitedSafe (body : MirBody) : Prop :=
  ∃ s : MirState,
    initEntryState body s ∧
    BodyConstsSafe s.tySizes body ∧
    MonoAdmittedSafe s.tySizes body
```

closes every negative-polarity CTFE loophole while preserving legitimate PMEs:

| Candidate Design | Rejects `buggyRuntimeFn` (UB body + `.stuck` const)? | Rejects `idWithUnmodeledConst` (safe body + `.stuck` const)? | Rejects `transmuteWithFakePme` (conditional `.stuck` at `tySizes 0 ≠ 8`)? | Rejects `transmuteWithFailedConst` (conditional `.failed` at `tySizes 0 ≠ 8`)? | Rejects `buggyFnWithPanicConst` (`const { assert!(false) }`)? | Admits legitimate PME (`transmuteToUsizeCheckedBody`)? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Baseline `MirSem`** (`initMirState` with `ConstSucceeds`) | **No** (vacuously `True`) | **No** (vacuously `True`) | **No** (vacuously `True` at `4`) | **No** (vacuously `True` at `4`) | **No** (vacuously `True`) | Yes |
| **Candidate A:** Baseline + `∃ s, initMirState body s` | Yes | **No** (if another branch succeeds) | **No** (`transmuteWithFakePme_initMirState_inhabited`) | **No** | Yes | Yes |
| **Candidate B:** `PolarMirSem` (`ConstNoStuck`) + `MonoInhabited` | Yes (`buggyRuntimeFn_rejected_by_polarMirSem`) | Yes (`idWithUnmodeledConst_rejected_by_polarMirSem`) | Yes (`transmuteWithFakePme_rejected_by_polarMirSem`) | **No** (`transmuteWithFailedConst_passes_polarMirSem_and_monoInhabited`) | Yes (`buggyFnWithPanicConst_rejected_by_monoInhabited`) | Yes (`transmuteToUsizeCheckedBody_verified_polar`) |
| **Candidate C (Recommended):** `SafePolarMirSem` (`ConstIsSafe`) + `MonoInhabitedSafe` | **Yes** | **Yes** | **Yes** | **Yes** (`transmuteWithFailedConst_rejected_by_safePolarMirSem`) | **Yes** | **Yes** (`transmuteToUsizeCheckedBody_verified_safePolar`) |

---

#### Finding 3: Transitive 4-Place `RequiresConst` with `substTySizes` vs. Un-substituted 2-Place `RequiresConst` in `MIR-to-x86-64 prototype`

`Basis: source + execution + derived`

In `StepResult-refinement baseline:trusted/lean/Trusted/MirSemantics.lean` (lines 550–598),
`RequiresConst` is a 4-place inductive relation `RequiresConst tySizes body
tySizes' c` whose `.call1` constructor substitutes `substTySizes tySizes
typeArgs` into the callee's type-size environment:

```lean
  | call1 {tySizes tySizes' : Nat → Nat} {body callee c : MirBody}
      {bb : BasicBlock} {dst : LocalId} {arg : Operand} {target : BlockId}
      {typeArgs : List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst callee arg target typeArgs →
      RequiresConst (substTySizes tySizes typeArgs) callee tySizes' c →
      RequiresConst tySizes body tySizes' c
```

By contrast, in `MIR-to-x86-64 prototype:trusted/lean/Trusted/X86Semantics.lean` (lines
513–559) and `MIR-to-x86-64 prototype:theory/Anneal/MirSemantics.lean` (lines 328–355),
`RequiresConst` was simplified to a 2-place relation `RequiresConst : Body →
Body → Prop` without `substTySizes`, and `MonoAdmitted tySizes body` checks
`∀ c, RequiresConst body c → ConstSucceeds tySizes c` at the **caller's**
`tySizes`.

In Section 7 of `support/PolarEvaluationAndProgress.lean` (lines 4592–4823), we
mechanize a generic caller `callerWithSubstCall` (`fn caller<U>(x: U) -> bool`,
with `requiredConsts = []`) that invokes
`transmuteToUsizeCheckedBody::<bool>(true)` (`typeArgs = [.bool]`):
- At runtime, `.call1` updates the callee's `tySizes` to
  `substTySizes s.tySizes [.bool]` (`0 ↦ 1`), so from an entry state with
  caller `tySizes = fun _ => 8`, `callerWithSubstCall` reaches
  `PrefixOutcome.failed` in 4 steps when `callTransmuteCopy` checks `1 == 8`
  (`callerWithSubstCall_fails_at_runtime`, lines 4760–4822).
- Direct-only membership `MonoAdmittedDirect (fun _ => 8) callerWithSubstCall`
  evaluates to `True` (`callerWithSubstCall_admitted_by_direct`, lines
  4667–4670).
- `MIR-to-x86-64 prototype`'s un-substituted 2-place `MonoAdmittedUnsubst (fun _ => 8)
  callerWithSubstCall` **also evaluates to `True`**
  (`callerWithSubstCall_admitted_by_unsubst`, lines 4679–4725), because it
  evaluates `sizeEq8ConstBody` at the caller's `tySizes = fun _ => 8` (`8 = 8`)
  instead of the callee's `substTySizes (fun _ => 8) [.bool]` (`0 ↦ 1`).
- The 4-place `RequiresConst` with `substTySizes` evaluates `sizeEq8ConstBody`
  at `substTySizes (fun _ => 8) [.bool]` (`0 ↦ 1`), where `ConstSucceeds` is
  `False`, so both `MonoAdmitted (fun _ => 8) callerWithSubstCall` and
  `MonoAdmittedSafe (fun _ => 8) callerWithSubstCall` evaluate to `False`
  (`callerWithSubstCall_rejected_by_subst_requiresConst`, lines 4733–4753).

---

#### Finding 4: Infinite-Loop and Unwind Progress Collapse and Constructive Fuel-Absorbing Step-Dilated Simulation (`π_dilated k`)

`Basis: source + execution + derived`

##### 4.1 Why `loopCodegen` and `unwindCodegen` Satisfy `WellFormed` and Functional Specs

In `Trusted/StepResult.lean` (`MIR-to-x86-64 prototype` lines 76–82), `PrefixOutcome.isSafe`
maps both `.running` and `.terminated .unwind` to `True`, and in
`Trusted/X86Semantics.lean` (lines 815–828), `X86Lang.SpecOn` guards its
postcondition behind normal termination (`∀ ret, out.outcome = .terminated
(.normal ret) → post q.init ret`). Consequently
(`support/PolarEvaluationAndProgress.lean:2285-2508`):
- `loopCodegen (b : MirBody) : X86Body` (`[{ instrs := [], terminator := .jmp
  ⟨0⟩ }]`) has outcome `.running` at every step budget `n`
  (`loopCodegen_always_running`, lines 2303–2333) and therefore satisfies
  `X86Lang.WellFormed`, `X86Lang.SpecOn pre post`, `EnsuresRetLibInv`,
  `EnsuresEqArg`, and `EnsuresConst` for **every** `MirBody b` (lines
  2337–2384).
- `unwindCodegen (b : MirBody) : X86Body` (`[{ instrs := [], terminator :=
  .abortPanic }]`) has outcome `.running` ($n = 0$) or `.terminated .unwind`
  ($n \ge 1$) (`unwindCodegen_always_running_or_unwind`, lines 2389–2401) and
  likewise satisfies `X86Lang.WellFormed`, `X86Lang.SpecOn pre post`,
  `EnsuresRetLibInv`, `EnsuresEqArg`, and `EnsuresConst` for **every**
  `MirBody b` (lines 2405–2461).
- Baseline lockstep `π` (`Trusted/X86Semantics.lean:851-866`) requires
  `q_src.steps = q_tgt.steps`, which rejects any multi-instruction lowering
  such as `idCopyX86_2x` (`lockstep_compiles_rejects_idCopyX86_2x`, lines
  3169–3225). Yet relaxing `π` naively to allow `.running` at arbitrary budgets
  (`π_naive_async`, lines 2468–2480) certifies `loopCodegen b` as a valid
  compilation of **every** well-formed `MirBody b`
  (`loopCodegen_compiles_under_π_naive_async`, lines 2488–2508).

##### 4.2 Fuel Absorption of `ReachesPrefix.terminated` and Step-Dilated Simulation `π_dilated k`

In `Trusted/StepResult.lean` (`MIR-to-x86-64 prototype` lines 158–160, `StepResult-refinement baseline` lines
129–131), the `terminated` constructor of `ReachesPrefix` is parameterized over
unconstrained remaining fuel `n : Nat`:

```lean
| terminated (n : Nat) (s : State) (term : TerminationKind Val) :
    step p s (.terminated term) →
    ReachesPrefix step p (n + 1) s [] (.terminated term)
```

By induction on `ReachesPrefix`, terminal outcomes are **absorbing with respect
to fuel** (`reachesPrefix_terminated_mono`,
`support/PolarEvaluationAndProgress.lean:2579-2589`): once a source execution
terminates in $m_0$ steps, its `ReachesPrefix` outcome remains `.terminated
term` for **every** step budget $m \ge m_0$. Fuel absorption converts eventual
termination at $m_0$ into a universal property over all finite step budgets
$m \ge m_0$, requiring neither coinductive traces nor `Classical.choice`.

Exploiting fuel absorption, we define `DilationWindow` and `π_dilated k`
(`support/PolarEvaluationAndProgress.lean:2757-2779`):

```lean
def DilationWindow (k m n : Nat) : Prop :=
  (m = 0 ∧ n = 0) ∨ (n ≤ k * m ∧ m ≤ n)

def π_dilated (k : Nat) (B : MirLang.Behavior) : X86Lang.Behavior :=
  fun q_tgt => {
    defined := ∀ q_src : MirLang.Query,
      matchQuery q_src.init q_tgt.init →
      DilationWindow k q_src.steps q_tgt.steps →
      (B q_src).defined
    val := fun h out_tgt =>
      ∃ q_src : MirLang.Query,
        ∃ h_match : matchQuery q_src.init q_tgt.init,
        ∃ h_win : DilationWindow k q_src.steps q_tgt.steps,
        ∃ tr_src : List Unit,
          (B q_src).val (h q_src h_match h_win)
            { trace := tr_src, outcome := out_tgt.outcome }
  }
```

1. **During expanded instruction execution ($n < k \cdot m_0$):** If each source
   step expands to at most $k$ target steps, after $n$ target steps the source
   program has taken $m = \lceil n / k \rceil < m_0$ steps (still `.running`),
   which lies in `DilationWindow k m n`.
2. **At target budget $n = k \cdot m_0$:** Every $m$ satisfying
   `DilationWindow k m (k * m₀)` satisfies $k \cdot m_0 \le k \cdot m$, which
   for $k \ge 1$ forces $m_0 \le m$ (`two_le_of_dilationWindow_two_mul`, lines
   2929–2941). By fuel absorption, every source budget $m$ in the window has
   already reached `.terminated (.normal v)`, rejecting both `loopCodegen`
   (`.running`) and `unwindCodegen` (`.terminated .unwind`)!
3. **After target termination ($n \ge n_{\text{term}}$ with $m_0 \le
   n_{\text{term}} \le k \cdot m_0$):** By fuel absorption on both machines,
   target outcome `.terminated (.normal v)` matches source budget $m = n \ge
   m_0$.

| Refinement / Specification Design | Monotone with 0 `Classical.choice`? | Rejects `loopCodegen` on `idCopyBody`? | Rejects `unwindCodegen` on `idCopyBody`? | Admits 2x expansion `idCopyX86_2x`? | Admits legitimate source loop `mirLoopBody` & panic `panicConst`? | Composes Across Compiler Passes? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Baseline lockstep `π`** (`q_src.steps = q_tgt.steps`) | Yes | Yes (at $n = 2$) | Yes (at $n = 2$) | **No** (`lockstep_compiles_rejects_idCopyX86_2x`) | Yes (if 1:1) | Only 1:1 passes |
| **Naive async `π_naive_async`** (allows `.running` at any $n$) | Yes | **No** (`loopCodegen_compiles_under_π_naive_async`) | Yes | Yes | Yes | No (collapses progress) |
| **Step-Bounded Total Spec `EnsuresEqArgTotal n₀`** (lines 3525–3765) | N/A (spec-level) | **Yes** (`loopCodegen_rejected_by_ensuresEqArgTotal`) | **Yes** (`unwindCodegen_rejected_by_ensuresEqArgTotal`) | **Yes** (`idCopyX86_2x_satisfies_ensuresEqArgTotal_3`) | Requires separate partial spec | Requires caller to supply `n₀` |
| **Step-Dilated `π_dilated k`** (Recommended, lines 2757–3520) | **Yes** (`monotone_π_dilated`) | **Yes**, $\forall k \ge 1$ (`π_dilated_rejects_loopCodegen`) | **Yes**, $\forall k \ge 1$ (`π_dilated_rejects_unwindCodegen`) | **Yes**, at $k = 2$ (`idCopyX86_2x_compiles_dilated_2`) | **Yes** (`mirLoopBody_compiles_dilated`, `panicConst_compiles_dilated`) | **Yes** ($\pi_{k_2} \circ \pi_{k_1} \sqsubseteq \pi_{k_1 k_2}$) |

---

#### Finding 5: `x86_64-linux` Hardware Differential Audit of `Trusted/X86Semantics.lean`, `Trusted/MirSemantics.lean`, and `render_x86_assembly`

`Basis: normative + source + execution`

##### 5.1 Unbounded `Nat` ALU & Shifts vs. 64-Bit Modular `x86_64` Silicon

In `Trusted/X86Semantics.lean:18-23`, machine words are represented as
`X86Val.word64 (bits : Nat)` with no `bits < 2^64` invariant (`X86Val.hasTy` at
`line 125` defines `| .usize, .word64 _ => True`), and `evalX86BinOp`
(`lines 207-230`) evaluates 64-bit x86 instructions using unbounded/truncating
Peano `Nat` arithmetic. Identical unbounded `Nat` arithmetic appears in
`StepResult-refinement baseline:trusted/lean/Trusted/MirSemantics.lean:207-230` (`evalBinOp` on
`MirVal.scalar (bits : Nat)`). Executing `support/x86_conformance_probe.c` on
`x86_64-unknown-linux-gnu` silicon (`support/x86_conformance_probe.out`) and
mechanizing the comparison in `support/SemanticPolarityAndCanaries.lean:331-395`
establishes five Quadrant-2 fail-open ALU divergences:

| `X86BinOp` (`X86Ast.lean:166-196`) | Emitted Instruction (`lib.rs:1563-1575`) | `evalX86BinOp` (`X86Semantics.lean:207-230`) | Concrete Input `(a, b)` | `X86Semantics.lean` Result | Real `x86_64` Silicon Result (`x86_conformance_probe.out`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `.sub` (`sub rax, rcx`) | `sub rax, rcx` | `a - b` (`Nat` truncating subtraction) | `(0, 1)` | `0` (`x86sem_nat_sub_diverges_from_hw64`) | `0xffffffffffffffff` ($2^{64} - 1$, `CF=1, SF=1`) |
| `.add` (`add rax, rcx`) | `add rax, rcx` | `a + b` (unbounded `Nat`) | `(2^64 - 1, 1)` | `2^64` (`0x10000000000000000`, `x86sem_nat_add_diverges_from_hw64`) | `0x0000000000000000` (`CF=1, ZF=1`) |
| `.mul` (`imul rax, rcx`) | `imul rax, rcx` | `a * b` (unbounded `Nat`) | `(2^32, 2^32)` | `2^64` (`0x10000000000000000`) | `0x0000000000000000` (`CF=1, OF=1`) |
| `.shl` (`shl rax, cl`) | `shl rax, cl` | `a <<< b` (unmasked, unbounded `Nat`) | `(1, 64)` | `2^64` (`x86sem_nat_shl_diverges_from_hw64`) | `0x0000000000000001` (`cl & 0x3f = 0`) |
| `.shr` (`shr rax, cl`) | `shr rax, cl` | `a >>> b` (unmasked `Nat`) | `(1, 64)` | `0` (`x86sem_nat_shr_diverges_from_hw64`) | `0x0000000000000001` (`cl & 0x3f = 0`) |

##### 5.2 Omitted Register File, Sub-Register Widths, `RFLAGS`, `#DE` Traps, and Stack Frame Bounds

1. **Unused AST declarations and missing architectural state:**
   `Trusted/X86Ast.lean:65-119, 153-157` defines `Reg64`, `Reg64.index`,
   `sysvArgReg`, and `BytePerm`, but none of them is referenced in
   `Trusted/X86Semantics.lean`. `X86State` (`Trusted/X86Semantics.lean:72-78`)
   has no `regs` or `rflags` fields; instructions operate directly on an
   unbounded list `active.slots : List (Option X86Val)`.
2. **Sub-register writes, `RFLAGS`, and `div`/`idiv` traps** (mechanized with
   positive and negative mutation canaries in
   `support/SemanticPolarityAndCanaries.lean:530-704` and verified against
   silicon in `support/x86_conformance_probe.out`):
   - **Sub-register write rules** (Intel SDM Vol. 1 §3.4.1.1, `[TEST 1]`,
     `canary_pos_subregister_writes`, `canary_neg_subregister_writes`): 8-bit
     (`movb %al`) and 16-bit (`movw %ax`) writes merge into bits `[7:0]` /
     `[15:0]` preserving upper bits, whereas 32-bit (`movl %eax`) writes
     zero-extend into bits `[63:32]`.
   - **Flag preservation and demonic undefined flags** (`[TEST 3]`, `[TEST 4]`,
     `canary_pos_inc_dec_preserve_cf`, `canary_neg_inc_clobbers_cf`,
     `canary_pos_shl64_mask_and_flags`): `incq`/`decq` update `ZF`, `SF`, `OF`
     while preserving `CF`; `movq`/`leaq` preserve all arithmetic flags; and
     64-bit shifts mask `count` with `0x3f`, preserve all flags when `count &
     0x3f == 0`, and leave `OF` architecturally undefined (demonic choice over
     `Bool`) when `count & 0x3f > 1`.
   - **Division `#DE` traps** (`[TEST 5]`, `canary_idiv64_traps_vs_buggy`):
     `divq`/`idivq` raise `#DE` (`SIGFPE`) not only on `divisor == 0` but also
     on 128-bit unsigned quotient overflow (`q >= 2^64`) and 64-bit signed
     overflow (`INT64_MIN / -1`).
3. **Unchecked out-of-frame stack slot writes:** In
   `Trusted/X86Semantics.lean:105-115`, `writeSlot` extends `slots` to
   arbitrary length with `none` when `slot.index >= slots.length`, and
   `evalX86Instr` (`lines 324-356`) never checks `slot.index <
   active.slotCount`. By contrast, `render_x86_assembly`
   (`trusted/rustc-capture/src/lib.rs:1598-1607`) allocates a fixed frame of
   `frame_bytes = (func.local_count.div_ceil(2) * 2) * 8` bytes and accesses
   `[rbp - 8 * (slot + 1)]`. Any instruction with `slot.index >=
   active.slotCount` steps cleanly in `X86Semantics.lean` while clobbering
   memory below `rsp` on hardware.

##### 5.3 Three Soundness Bugs in `render_x86_assembly` (`trusted/rustc-capture/src/lib.rs`)

Comparing `render_x86_assembly` (`trusted/rustc-capture/src/lib.rs:1589-1820`)
against `Trusted/X86Semantics.lean` at
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`
identifies three concrete violations of `TCBItem.assemblerLowering`:
1. **`CallSizeOf` (`movSizeOfJmp`) hardcodes `8` in emitted assembly
   (`lib.rs:1773-1781` vs. `X86Semantics.lean:418-424`):** `X86Semantics.lean`
   writes `.word64 (evalX86TyByteSize s.tySizes ty)` to `dst`, whereas
   `lib.rs:1773-1781` ignores `ty` and emits `mov QWORD PTR [rbp - {dst_off}],
   8` for every type.
2. **`CallTransmuteCopy` (`repMovsbJmp`) hardcodes a single 8-byte copy in
   emitted assembly (`lib.rs:1782-1797` vs. `X86Semantics.lean:340-355,
   425-449`):** `X86Semantics.lean` models `repMovsbJmp` as copying the full
   `evalX86TyByteSize tySizes srcTy` bytes, whereas `lib.rs:1782-1797` emits a
   single 8-byte `mov rax, QWORD PTR [rsi]; mov QWORD PTR [rbp - {dst_off}],
   rax` (`[TEST 6]` in `support/x86_conformance_probe.out` shows the upper 8
   bytes of a 16-byte struct remaining uncopied `0xdeadbeefdeadbeef`), and
   `slot_offset(slot) = 8 * (slot + 1)` (`lib.rs:1585-1587`) allocates only 8
   bytes per local regardless of type size.
3. **`Panic` (`abortPanic`) emits `ud2` instead of `call abort`
   (`lib.rs:1756-1758` vs. `X86Semantics.lean:407-410`):** `X86Semantics.lean`
   models `.abortPanic` as `.terminated .unwind` (`isSafe = True`) and `.ud2`
   as `.failed .ub` (`isSafe = False`), but `lib.rs:1756-1758` emits `ud2`
   (`SIGILL`, hardware `#UD` trap) for both `Unreachable` and `Panic`.

## Boundaries

### Part I — Post-Monomorphization Error (PME) MIR Semantics and Polymorphic Conditional Contracts

- **Full CTFE interpreter fidelity (`not examined`):** `ConstMirMachine` in
  [support/PmeMirSemantics.lean](support/PmeMirSemantics.lean) executes the MIR
  fragment needed for arithmetic assertions, layout queries (`size_of`,
  `align_of`), and control flow (`SwitchInt`, `panic`, `goto`, `return_`). It
  does not model heap allocation inside `const` evaluation, `const` trait
  methods, or pointer-to-integer casts in CTFE (which `rustc`'s Miri-based CTFE
  engine rejects or restricts separately).
- **Subprocess `--emit=mir` vs. in-process `rustc_driver` extraction
  (`known not to apply` for default `--emit=mir`):** Textual `rustc --emit=mir`
  at default `-Z mir-opt-level=1` omits `body.required_consts` and
  `body.mentioned_items` metadata headers, erases unit-typed
  `_2 = const ...::{constant#0};` assignments via dead-store elimination, and
  folds away `if false { callee(); }` via `SimplifyConstCondition`. Sound PME
  extraction therefore requires either in-process `TyCtxt` queries
  (`post_cleanup_body.required_consts()`, `ty::Instance::try_resolve`, and
  `tcx.mir_for_ctfe`) or passing `-Z mir-opt-level=0` and resolving constant
  operands from reachable basic blocks.
- **Unwinding vs. aborting semantics (`not examined`):** Both mechanizations
  treat `Terminator.panic` and `Terminator.assertNotOverflow` failure as
  `.failed .contractViolation` (`isSafe = False`), matching Anneal's
  total-correctness / panic-freedom verification contract rather than modeling
  stack unwinding recovery.

### Part II — Polar CTFE Admission, Step-Dilated Progress Preservation, and Four-Quadrant Semantic Polarity

- **Floating-point, SIMD/AVX, and concurrency instructions (not examined):**
  Neither `StepResult-refinement baseline` nor `MIR-to-x86-64 prototype` models floating-point, vector, or
  atomic/fence instructions; our hardware differential probe and Lean 4
  canaries cover scalar 64-bit/sub-register general-purpose instructions,
  `RFLAGS`, stack frames, and `div`/`idiv`/`ud2` traps.
- **Full DWARF unwinding vs. `abort` on panic (known not to apply):**
  `MIR-to-x86-64 prototype` models panic termination as `.terminated .unwind` without
  modeling landing-pad cleanup frames (`X86Semantics.lean:409-410`), assuming
  `-C panic=abort` or no-unwind postconditions.
- **Step compression ($n < m$) in optimizing passes (not examined in
  `DilationWindow`):** `DilationWindow k m n` models lowering passes where each
  source step expands to between $1$ and $k$ target steps ($m \le n \le k \cdot
  m$). If a future optimization pass eliminates source steps ($n < m$),
  `DilationWindow` generalizes to two constants $(k_{\text{compress}},
  k_{\text{expand}})$ with $m \le k_{\text{compress}} \cdot n \land n \le
  k_{\text{expand}} \cdot m$; the fuel-absorption proof is unchanged because
  $n = k_{\text{expand}} \cdot m_0$ still forces $m \ge m_0$.

## Evidence

### Part I — Post-Monomorphization Error (PME) MIR Semantics and Polymorphic Conditional Contracts

#### Preserved Package Artifacts

1. **[support/PmeMirSemantics.lean](support/PmeMirSemantics.lean)** (2,563 lines, SHA-256
   `c93ee5252538031e0953e154800573701515a564d86f7bbc2083a59ad0f2cc7f`):
   - Section 1 (` (lines 68-274)`): `Partial.bot`, `Behavior.when`, `Behavior.given`,
     and `behavior_when_given_adjunction` (zero axioms).
   - Section 2 (` (lines 276-562)`): `SmallStepMachine.withAdmitted`,
     `totalStep_withAdmitted`, `inhabitedDemonic_withAdmitted`,
     `reachesPrefix_withAdmitted_iff`, and `behaviorOf_withAdmitted_le_iff`.
   - Section 3 (` (lines 564-724)`): `TyLayout`, `MirTy`, `MirVal`, `Rvalue`
     (`.addrOfDeref`, `.castPtrToPtr`, `.reborrowShared`), `ConstMirBody`, and
     `MirBody` (`requiredConsts`, `requiredLayouts`).
   - Section 4 (` (lines 726-1338)`): `evalBlocksStep`, `MirMachine`,
     `ConstMirMachine`, `CtfeAdmitted`, `MirBody.CompileAdmitted`,
     `PartialCompiler.SoundOn.verify`, `mirSemAdmitted_le_iff`,
     `ConcreteVerifiedAndAdmitted`, and `GenericVerifiedWithDomain`.
   - Section 5 (` (lines 1340-2563)`): `constBoundedAdd_compileAdmitted_iff`,
     `constBoundedAdd_source_verified`, `transmuteRef_compileAdmitted_iff`,
     `transmuteRef_source_verified`, and Negative Controls 1–4.
2. **[support/PolymorphicConditionalVerification.lean](support/PolymorphicConditionalVerification.lean)**
   (2,110 lines, SHA-256
   `9b7d816ea84413422941fdc4609b0939cc827ec413375d20314208cbf3207495`):
   - Section 1 (` (lines 80-274)`): Layer 1A definitions (`Partial`, `Language`,
     `SpecOn`, `WellFormedOn`, `Compiler.Verified`, `VerificationResultOn`,
     `specOn_antitone_pre`, `Compiler.Verified.mono`).
   - Section 2 (` (lines 276-618)`): Layer 1B small-step machine,
     `behaviorOf_defined_at_zero`, `CheckedInstCtx`, and `evalMirStep`.
   - Section 3 (` (lines 620-815)`): `MonoMirUnit`, `MonoMirLang`, `semIfCompiled`,
     `semTotalCompiled`, `semIfCompiled_le_iff`,
     `semTotalCompiled_le_iff_of_defined`, `defined_of_semTotalCompiled_le`, and
     `verifiedTotal_iff_noPme_and_verifiedIfCompiled`.
   - Section 4 (` (lines 817-1099)`): Representation Model I (`PolyCapturedFnR1`,
     `polyTotalVerifiedR1_of_ifCompiled_and_noPme`) vs. Representation Model II
     (`PolyMirLang`, `unifiedTotalPre`, `r1_iff_r2_source_wellFormed`,
     `mono_embeds_into_r2_iff`, `r2_projects_to_r1_instance`,
     `r2_total_verified_of_ifCompiled_and_noPme`).
   - Section 5 (` (lines 1101-1157)`): `brokenPmeProg`,
     `naive_r2_vacuous_argPre_counterexample`, and
     `refined_r2_rejects_pme_even_when_argPre_empty`.
   - Sections 6–7 (` (lines 1159-2110)`): `checked<T: Bound, const N: usize>`,
     Guarantees 1–3 (`checked_polymorphic_safety_if_compiled_r1`,
     `checked_no_pme_r1`, `client_good_entry_verified`), and Negative Controls
     1–3 (`client_bad_entry_fails_to_compile_and_verify`,
     `client_bad_trait_fails_at_runtime`,
     `client_bad_arg_refutes_unconditional_wellFormed`).

#### Primary Source Coordinates

- **`joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)`:**
  - `trusted/lean/Trusted/Refinement.lean (lines 1-245)`
  - `trusted/lean/Trusted/StepResult.lean (lines 1-150)`
  - `trusted/lean/Trusted/MirAst.lean (lines 1-140)`
  - `trusted/lean/Trusted/MirSemantics.lean (lines 1-280)`
  - `trusted/rustc-capture/src/lib.rs (lines 84-91)`
- **`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`:**
  - [`compiler/rustc_middle/src/mir/mod.rs (lines 278-295)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs)
    (`Body::required_consts` and `Body::mentioned_items` declarations)
  - [`compiler/rustc_mir_build/src/builder/matches/mod.rs (lines 206-214)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs)
    and
    [`compiler/rustc_mir_build/src/builder/matches/test.rs (lines 136-141)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/test.rs)
    (`if` and `match` lowering to `TerminatorKind::SwitchInt`)
  - [`compiler/rustc_mir_build/src/builder/scope.rs (lines 563-565)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs)
    and
    [` (lines 823-830)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs)
    (`loop {}` and `return`/`break`/`continue` allocating zero-predecessor
    blocks via `start_new_block`)
  - [`compiler/rustc_mir_transform/src/simplify.rs (lines 81-377)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs)
    (`SimplifyCfg::Initial` and `remove_dead_blocks`)
  - [`compiler/rustc_mir_transform/src/required_consts.rs (lines 9-23)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/required_consts.rs)
    (`RequiredConstsVisitor::compute_required_consts`)
  - [`compiler/rustc_mir_transform/src/mentioned_items.rs (lines 40-85)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/mentioned_items.rs)
    (`MentionedItemsVisitor`)
  - [`compiler/rustc_mir_transform/src/simplify_branches.rs (lines 30-98)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify_branches.rs)
    (`SimplifyConstCondition`)
  - [`compiler/rustc_monomorphize/src/collector.rs (lines 1364-1389)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs)
    and
    [` (lines 1753-1792)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs)
    (`collect_items_of_instance` and `RootCollector::is_root`)
  - [`compiler/rustc_codegen_ssa/src/back/symbol_export.rs (lines 114-118)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/back/symbol_export.rs)
    (`reachable_non_generics_helper` excluding `cross_crate_inlinable` items)

### Part II — Polar CTFE Admission, Step-Dilated Progress Preservation, and Four-Quadrant Semantic Polarity

#### Preserved Package Artifacts (`support/`)

1. **`support/PolarEvaluationAndProgress.lean`**
   - **Lines:** 4,870 lines
   - **SHA-256:**
     `237cc6a5798b74cd50c713f1ce89eabf23c58f5285086c2e1697d8b5379d8fa1`
   - **Scope:** Standalone Lean 4 (`v4.34.1`) mechanization of the
     negative-polarity `.stuck` and `.failed` CTFE fail-open exploits
     (`buggyRuntimeFn_vacuously_satisfies_false_spec`,
     `totalStep_and_inhabitedDemonic_do_not_catch_empty_initState`,
     `transmuteWithFakePme_initMirState_inhabited`,
     `transmuteWithFailedConst_passes_polarMirSem_and_monoInhabited`), the
     `ConstIsSafe` / `SafePolarMirSem` / `MonoInhabitedSafe` closure
     (`transmuteWithFailedConst_rejected_by_safePolarMirSem`,
     `sizeEq8ConstBody_constIsSafe`,
     `transmuteToUsizeCheckedBody_verified_safePolar`), the 2-place vs. 4-place
     `RequiresConst` `substTySizes` proofs
     (`callerWithSubstCall_admitted_by_unsubst`,
     `callerWithSubstCall_rejected_by_subst_requiresConst`,
     `callerWithSubstCall_fails_at_runtime`), and the fuel-absorbing
     step-dilated simulation `π_dilated k` (`reachesPrefix_terminated_mono`,
     `monotone_π_dilated`, `π_dilated_rejects_loopCodegen`,
     `π_dilated_rejects_unwindCodegen`, `idCopyX86_2x_compiles_dilated_2`,
     `mirLoopBody_compiles_dilated`, `panicConst_compiles_dilated`). All 38
     `#print axioms` checks depend solely on `[propext]`.
2. **`support/SemanticPolarityAndCanaries.lean`**
   - **Lines:** 726 lines
   - **SHA-256:**
     `a19876355730714c9a625ba5ab7dae072e8022418cd21fbc8a176c48dc91f8e9`
   - **Scope:** Standalone Lean 4 (`v4.34.1`) mechanization of the
     Four-Quadrant Semantic Polarity Matrix (`q1_omitting_ub_is_fail_open`,
     `q1_omitting_nondet_is_fail_open`, `q1_spurious_ub_is_fail_closed`,
     `q2_omitting_hw_trap_is_fail_open`,
     `q2_underapproximating_undef_flag_is_fail_open`,
     `q3_spurious_ub_codegen_exploit`, `q3_two_sided_sandwich_soundness`,
     `q4_spurious_ctfe_failure_vacuously_verifies_ub_in_initState`,
     `q4_spurious_ctfe_failure_vacuously_verifies_ub_in_effectivePre`,
     `q4_omitting_ctfe_panic_is_fail_closed`), the `evalX86BinOp` `Nat` vs.
     `BitVec 64` divergence theorems (`x86sem_nat_sub_diverges_from_hw64`,
     `x86sem_nat_add_diverges_from_hw64`, `x86sem_nat_shl_diverges_from_hw64`,
     `x86sem_nat_shr_diverges_from_hw64`), and the positive/negative `x86_64`
     hardware conformance canaries (`canary_pos_subregister_writes`,
     `canary_neg_subregister_writes`, `canary_pos_inc_dec_preserve_cf`,
     `canary_neg_inc_clobbers_cf`, `canary_pos_shl64_mask_and_flags`,
     `canary_idiv64_traps_vs_buggy`). All 10 Quadrant 1–4 theorems depend on
     zero axioms; the 10 `BitVec` divergence and canary theorems depend only on
     `[propext, Quot.sound]`.
3. **`support/x86_conformance_probe.c` and `support/x86_conformance_probe.out`**
   - **Lines (`x86_conformance_probe.c`):** 378 lines (SHA-256
     `1bb4b7373696556a7c7d6e7fc599729b9363f2ed38594be58595f03681b5dc26`)
   - **Lines (`x86_conformance_probe.out`):** 28 lines (SHA-256
     `075212f3b7b311135d9868fa59d15c97fe8b3a397664e86be2219362871816d7`)
   - **Scope:** User-space C/inline-assembly differential probe and recorded
     hardware output on `x86_64-unknown-linux-gnu` testing sub-register writes,
     64-bit modular ALU overflow/underflow, shift-count masking and `RFLAGS`,
     `incq`/`decq` `CF` preservation, `divq`/`idivq` `#DE` (`SIGFPE`) and `ud2`
     `#UD` (`SIGILL`) traps, and 8-byte `mov` vs. 16-byte `rep movsb` truncation
     in `CallTransmuteCopy`.

#### Primary Git Sources Examined

1. **`joshlf/anneal` (`StepResult-refinement baseline` worktree) at
   `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`:**
   - `trusted/lean/Trusted/Refinement.lean:43-245` (`Partial`,
     `Language.SpecOn`, `WellFormedOn`, `Compiles`, `Compiler.Verified`,
     `VerificationResultOn`)
   - `trusted/lean/Trusted/StepResult.lean:53-167` (`PrefixOutcome.isSafe`,
     `ReachesPrefix`, `BehaviorOf`, `toLanguage`)
   - `trusted/lean/Trusted/MirSemantics.lean:18-23` (`MirVal`), `207-302`
     (`evalBinOp`), `497-627` (`evalMirStmt`, `evalMirTerminator`,
     `evalMirStep`, `RequiresConst`, `ConstSucceeds`, `MonoAdmitted`,
     `initMirState`, `MirMachine`)
   - `theory/Anneal/StepResult.lean:25-106` (`TotalStep`, `InhabitedDemonic`,
     `non_vacuity_at_every_depth`)
2. **`joshlf/anneal` (`MIR-to-x86-64 prototype` worktree) at
   `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`:**
   - `trusted/lean/Trusted/StepResult.lean:76-180` (`PrefixOutcome.isSafe`,
     `ReachesPrefix`)
   - `trusted/lean/Trusted/X86Ast.lean:65-477` (`Reg64`, `sysvArgReg`,
     `BytePerm`, `X86BinOp`, `X86Instr`, `X86Terminator`, `X86Body`)
   - `trusted/lean/Trusted/X86Semantics.lean:18-130` (`X86Val`, `X86State`,
     `writeSlot`, `X86Val.hasTy`), `207-230` (`evalX86BinOp`), `324-449`
     (`evalX86Instr`, `evalX86Term`), `513-559` (`RequiresConst`,
     `ConstSucceeds`, `MonoAdmitted`), `813-895` (`CapturedFn`, `SpecOn`,
     `EnsuresRetLibInv`, `EnsuresEqArg`, `EnsuresConst`, `matchQuery`, `π`,
     `AssemblerCompiler`, `CrateTheorem`)
   - `theory/Anneal/MirSemantics.lean:112-162, 286, 328-355` (`evalMirStep`,
     `RequiresConst`, `MonoAdmitted`)
   - `theory/Anneal/Compiler/NaiveCodegen.lean:70-158, 821-857` (`compileBody`,
     `π_stage0`, `compileStage0_compiles`)
   - `theory/Anneal/MirLemmas.lean:43-44, 152-153, 526-529` (`idCopyBody`,
     `binOpBody`, `checkedBinOpBody`)
   - `trusted/rustc-capture/src/lib.rs:1435-1820`
     (`render_mir_lean_with_metadata`, `x86_binop_constructor`, `slot_offset`,
     `render_x86_assembly`)

## Revalidation

### Part I — Post-Monomorphization Error (PME) MIR Semantics and Polymorphic Conditional Contracts

1. **Re-verify the preserved Lean 4.34.1 mechanizations:**
   Run the Lean 4 (`v4.34.1`) kernel checker with asynchronous elaboration and
   kernel-check skipping disabled from this package directory:
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/PmeMirSemantics.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/PolymorphicConditionalVerification.lean
   ```
   Both commands must exit with status `0` and produce zero warnings or errors.
2. **Revalidate `rustc` MIR pass ordering and dead-branch vs. post-divergence
   PME behavior on a newer `rustc` revision:**
   Compile a minimal probe containing `if false`, `match false`, and `return;`
   followed by `const { assert!(N <= 1000); }` instantiated at `N = 2000` with
   `rustc --emit=obj` and
   `rustc -Z dump-mir=Built,SimplifyCfg-initial,RemovePlaceMention`.
   Verify whether `RequiredConstsVisitor` (`mir_promoted`) and `MentionedItems`
   (`inner_optimized_mir`) still execute after `SimplifyCfg::Initial` and before
   `SimplifyConstCondition`, and check `reachable_non_generics_helper` in
   `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` to confirm whether
   `cross_crate_inlinable` functions remain excluded from `--crate-type=lib`
   monomorphization roots.

### Part II — Polar CTFE Admission, Step-Dilated Progress Preservation, and Four-Quadrant Semantic Polarity

To revalidate all findings after modifying `Trusted/StepResult.lean`,
`Trusted/MirSemantics.lean`, `Trusted/X86Semantics.lean`, or
`trusted/rustc-capture/src/lib.rs`:

1. Re-verify both standalone Lean 4 mechanizations with synchronous elaboration
   and full kernel type-checking:
   ```bash
   lean \
     -DElab.async=false -Ddebug.skipKernelTC=false \
     support/PolarEvaluationAndProgress.lean
   lean \
     -DElab.async=false -Ddebug.skipKernelTC=false \
     support/SemanticPolarityAndCanaries.lean
   ```
2. Re-compile and execute the `x86_64` hardware conformance probe and compare
   its output against `support/x86_conformance_probe.out`:
   ```bash
   gcc -O2 -Wall -Wextra support/x86_conformance_probe.c -o ./x86_conformance_probe && \
     ./x86_conformance_probe | diff -u support/x86_conformance_probe.out -
   ```
3. Inspect `MonoAdmitted` in `Trusted/MirSemantics.lean` and
   `Trusted/X86Semantics.lean` to confirm that (a) CTFE safety (`ConstIsSafe` /
   `BodyConstsSafe`) is enforced in positive polarity while negative admission
   is gated as `ConstIsSafe → ConstSucceeds` (`MonoAdmittedSafe`) alongside
   `MonoInhabitedSafe`, and (b) `RequiresConst` uses the 4-place relation
   substituting `substTySizes tySizes typeArgs` across `.call1` edges.
4. Inspect `evalX86BinOp` (`Trusted/X86Semantics.lean`) and `evalBinOp`
   (`Trusted/MirSemantics.lean`) for `BitVec 64` modular arithmetic and shift
   masking (`count &&& 63#64`), and inspect `render_x86_assembly`
   (`trusted/rustc-capture/src/lib.rs`) for `CallSizeOf`, `CallTransmuteCopy`,
   and `Panic` lowering.
