# Behavior Codecs, Progress Refinement, Optimizer Anti-Degeneracy, and Partial Compilation Conditioning Algebra in Anneal

## Summary

### Part I — Behavior Codecs, Progress Refinement, Eventual Semantics, and Optimizer Anti-Degeneracy

Anneal's trusted refinement core (`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean`) mediates cross-language compilation
(`Compiles`), verification abstraction (`Abstracts`), compiler soundness
(`Compiler.SoundOn`), and target verification (`Compiler.Verified`) over
step-indexed prefix semantics `BehaviorOf M p` (`Query := ExecQuery State`,
`Out := ExecOut Obs Val`). Across
`joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)` and the MIR-to-x86-64
compiler branch `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`, three
structural tensions govern how behavior mappings
`π : L_src.Behavior → L_tgt.Behavior` and `BehaviorCodec L₁ L₂` interact with
multi-step compilation, target hardware encodings, and optimizing passes:

1. **Morphism degeneracy under unconstrained `Monotone π`:** Requiring only
   `Monotone π` in `Compiler.SoundOn` admits four orthogonal classes of
   degenerate morphisms—**(a) top collapse (`π_top`)**, **(b) chaotic defined
   outcome erasure (`π_chaosPure`, `π_chaosVal`)**, **(c) step-zero and
   bounded-fuel query truncation (`π_stepZero`, `π_boundedFuel K`)**, and
   **(d) observation and return-value erasure**—under which UB-free source
   programs compile to faulting, diverging, trace-deleting, or wrong-value
   target programs while satisfying `Compiler.SoundOn` and `Compiler.Verified`.
   Although anchoring a pass pipeline to a target specification
   (`C.π (π_v spec_v) ≤ spec_tgt`) rules out Classes (a), (b), and (d), every
   step-independent partial-correctness specification (`WellFormed`,
   `WellFormedOn`, `EnsuresRetLibInv`) satisfies `π_stepZero spec = spec` and
   `π_boundedFuel K spec = spec` definitionally (`rfl`), leaving target-anchored
   pipelines blind to Class (c) divergence introduction (`loop: jmp loop`) and
   late-UB masking unless step-budget coverage is enforced by the coupling.
2. **Variable-step stuttering and partial outcome decoding in `BehaviorCodec`:**
   `BehaviorCodec L₁ L₂` in `Trusted/Refinement.lean` assumes 1-to-1 query step
   mapping and a total section-retraction pair
   (`∀ o₂, encodeOut (decodeOut o₂) = o₂`) on outcomes. Variable-step
   instruction selection—such as lowering a 1-step MIR `Downcast` to `0` x86-64
   instructions and a 1-step `NicheDecode` to `3` x86-64 instructions—breaks
   1-to-1 step-indexed `Compiles` at intermediate step budgets, and no
   state-independent step projection `stepMap : Nat → Nat` can simultaneously
   validate passes that both compress ($2 \to 1$) and expand ($2 \to 3$) step
   counts. Moving `steps : Nat` inside the semantics constructor
   `EventualBehaviorOf` (`Query := State`, `Out := EventualOut Obs Val`)
   preserves exact all-prefix UB-freedom
   (`eventual_wellFormed_iff_prefix_wellFormed`) with zero `Classical.choice`
   and zero coinduction, strictly rejects infinite-loop codegen, and eliminates
   step-dilation bounds from `BehaviorCodec`. Independently, when a target
   representation type has strictly larger cardinality than the source type
   (such as an 8-bit or 64-bit register holding a 2-valued Rust `bool`), no
   total `(encodeOut, decodeOut)` can satisfy `encode_decode_out`. Generalizing
   `decodeOut` to `L₂.Out → Option L₁.Out` (`PartialBehaviorCodec`) with
   `decode_encode_out` and `encode_of_decode_some` preserves strict functorial
   composition via `Option.bind` and automatically rejects target programs that
   produce invalid bit patterns (`decodeOut o₂ = none`).
3. **Certifying pass anti-degeneracy and instruction deletion under `π_opt`:**
   In `theory/Anneal/Compiler/Peephole.lean`, `optimizePeephole` is unwired in
   `trusted/rustc-capture/src/lib.rs`, omits recursion into `X86Term.call1`
   callees and `requiredConsts`, and acts as the strict identity (`rfl`) on all
   four functions in the `MirLemmas.lean` corpus. Moreover, because
   `PeepholeCompiler` uses `π = id` over step-indexed `BehaviorOf`, no pass
   that deletes or coalesces even a single `.nop` instruction can satisfy
   `Compiles X86Lang X86Lang id s (opt s)`. Replacing `id` with the monotone
   step-rescaling morphism `π_opt` and gating certifying passes with
   `CertifiedOptimizationPass` (combining universal soundness under `π_opt`,
   kernel-`rfl` certificate acceptance on a corpus benchmark, and strict static
   and dynamic step reduction) rejects always-`false` validators (Trap 1),
   identity optimizers (Trap 2), and no-op `optimizePeephole`, while accepting a
   verified instruction-coalescing and constant-folding pass
   (`coalesceAndFoldBody`).

### Part II — Partial Compilation and Behavioral Conditioning Refinement Algebra

Anneal's Layer 1A refinement framework (`Trusted/Refinement.lean` and
`theory/Anneal/Refinement.lean`) models compilation (`Compiles`), verification
abstraction (`Abstracts`), and crate verification envelopes
(`VerificationResultOn` and `VerificationResult`) inside a single refinement
preorder (`≤`) over `Behavior Query Out := Query → Partial (Out → Prop)`. At
`joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)`, `Trusted.Compiler`
models compilation as a total function `compile : L_src.Prog → L_tgt.Prog`.
However, both `rustc` (which can reject a captured `Runtime(PostCleanup)` MIR
body during monomorphization-time `const { assert!(...) }` evaluation, layout
overflow checks, or codegen) and executable Lean lowering passes (which return
`Option L_tgt.Prog`) are partial.

Generalizing `Compiler.compile` to `L_src.Prog → Partial L_tgt.Prog` models
compile-time partiality using the same two-field `Partial` structure
(`defined : Prop`, `val : defined → B`) that already models runtime Undefined
Behavior (UB) in `Trusted/Refinement.lean`. This representation introduces zero
new carrier types into `trusted/`, embeds computable `Option`-returning passes
via `Option.toPartial` (which is isomorphic to `Partial` up to structural
equivalence whenever `.defined` is decidable), and composes multi-stage partial
pipelines via `Partial.bind`.

Conditioning behaviors and partial programs across the refinement preorder is
governed by the **Harmonized Conditioning Triad** (`Behavior.when`,
`Behavior.given`, and `Behavior.require`) and its dependent liftings
(`Language.semIfCompiled` and `Language.semPartial`):

- `Behavior.when P b` (angelic program gating on the left of `≤`, mapping `¬ P`
  to `Partial.bot` / $\bot$) is left adjoint to `Behavior.given P spec`
  (precondition specification gating on the right of `≤`, mapping `¬ P` to
  `Partial.ub` / $\top$):
  $$\mathsf{Behavior.when}\; P\; b \le \mathsf{spec} \iff (P \to b \le \mathsf{spec}) \iff b \le \mathsf{Behavior.given}\; P\; \mathsf{spec}$$
  with
  `L.SpecOn (fun q => P ∧ pre q) post = Behavior.given P (L.SpecOn pre post)`
  holding definitionally (`rfl`).
- `Behavior.require P b` (demonic program gating on the left of `≤`, mapping
  `¬ P` to `Partial.ub` / $\top$) forces `P` to hold at every query where the
  right-hand specification is defined.
- `Compiler.SoundOn` must always use the conditional polarity
  (`∀ h : (C.compile s).defined, Compiles ...`, equivalent to
  `L_tgt.semIfCompiled (C.compile s) ≤ C.π (L_src.sem s)`), never the demonic
  `semPartial` polarity, which would assert `(C.compile s).defined` as an
  unproved TCB axiom and become inconsistent (`False`) on programs rejected by
  a Post-Monomorphization Error (PME).
- Among the three verification modes (`VerifiedTotal` $\implies$ `Verified`
  $\implies$ `VerifiedWhenCompiled`), Mode 1 (`Compiler.Verified`) is the sole
  `Verified` primitive needed in `Trusted/Refinement.lean`: it prevents the
  silent vacuity hazard of unguarded Mode 2 while expressing PME-conditioned
  verification explicitly via `Behavior.given`
  (`verifiedWhenCompiled_iff_verified_given`).
- Conjoining `(rustc body).defined → body.CompileAdmitted` into the meaning of
  `TCBItem.rustcLowering` (`RustcLoweringSound`) enables the target-level
  discharge theorem `target_discharges_compileAdmitted`: a source proof
  conditioned on `body.CompileAdmitted` automatically discharges
  `body.CompileAdmitted` for any target artifact `(rustc body).val h_comp` that
  `rustc` emits, establishing the un-gated target specification under the
  runtime precondition `pre` alone.

## Applicability

### Part I — Behavior Codecs, Progress Refinement, Eventual Semantics, and Optimizer Anti-Degeneracy

The findings in this report apply to the three subjects recorded in
`REPORT.json`:

1. **Anneal core verification framework** at
   `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`:
   - `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Monotone`, `Behavior`,
     `Language`, `BehaviorCodec`, `Compiles`, `Abstracts`, `Compiler`,
     `Compiler.SoundOn`, `Compiler.Verified`, `VerificationResultOn`),
   - `trusted/lean/Trusted/StepResult.lean` (`TerminationKind`, `StepResult`,
     `PrefixOutcome`, `ExecQuery`, `ExecOut`, `SmallStepMachine`,
     `ReachesPrefix`, `BehaviorOf`),
   - `trusted/lean/Trusted/MirSemantics.lean` (`MirMachine`, `MirLang`,
     `EnsuresRetLibInv`, `RustcCompiler`), and
   - `theory/Anneal/Refinement.lean` (`pass_trans`, `Compiles.comp`,
     `Abstracts.comp`, `Compiler.SoundOn.verify`, `verify_through_passes`).
2. **Anneal MIR-to-x86-64 compiler branch** at
   `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`:
   - `trusted/lean/Trusted/X86Semantics.lean` (`X86Machine`, `X86Lang`,
     `EnsuresRetLibInv`, `AssemblerCompiler`),
   - `theory/Anneal/Compiler/NaiveCodegen.lean` (`compileStmt`, `compileStage0`,
     `naiveCodec`, `Stage0Compiler`),
   - `theory/Anneal/Compiler/Peephole.lean` (`optimizeInstr`, `optimizeTerm`,
     `optimizeBlock`, `optimizePeephole`, `PeepholeCompiler`), and
   - `theory/Anneal/MirLemmas.lean` (corpus verification over `idCopyBody`,
     `newUncheckedBody`, `makeNonZeroBody`, and `getUncheckedNonZeroBody`).
3. **Lean 4 theorem prover** at
   `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`),
   invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` over standalone
   modules using only `prelude` and `import Init.NotationExtra`.

All counterexamples, impossibility theorems, and replacement structures in this
report are kernel-verified in the preserved package files
[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean),
[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean),
and
[AntiDegeneracyAndCallbackFraming.lean](support/AntiDegeneracyAndCallbackFraming.lean).

### Part II — Partial Compilation and Behavioral Conditioning Refinement Algebra

The findings in this report apply to the combination of the two subjects in
`REPORT.json`:

1. **Anneal verification framework** at
   `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)`, specifically:
   - `trusted/lean/Trusted/Refinement.lean` (532 lines: Layer 1A refinement
     preorder, `Partial`, `Language`, `Compiler`, `Compiler.SoundOn`,
     `Compiler.Verified`, `VerificationResultOn`, and `VerificationResult`),
   - `theory/Anneal/Refinement.lean` (273 lines: `Partial` lattice lemmas,
     `SpecOn`/`WellFormedOn` characterizations, `pass_trans`, `Compiles.comp`,
     `Abstracts.comp`, `Compiler.SoundOn.verify`, `verify_through_passes`,
     `Compiler.Verified.mono`, and `Compiler.Verified.with_wellFormedOn`),
   - `trusted/lean/Trusted/MirAst.lean` (381 lines) and
     `trusted/lean/Trusted/MirSemantics.lean` (872 lines: `MirLang`, `rustc`,
     `TargetLang`, `RustcCompiler`, `TCBItem`, `CapturedFn`, `Crate`, and
     `CrateTheorem`), and
   - `trusted/audit/TrustedBoundary.lean` (1,014 lines) and
     `trusted/audit/src/lib.rs` (1,961 lines: `.olean` kernel replay, import
     DAG containment, inventory checks, axiom lock, and candidate-feature
     non-contamination).
2. **Lean 4 theorem prover** at
   `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`),
   invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` over standalone
   modules using only `prelude` and `import Init.NotationExtra` (matching
   `Trusted/Refinement.lean`).

All algebraic definitions, equivalences, bridge theorems, and discriminating
canaries in this report are kernel-verified in the preserved package artifacts
[support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) and
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean). Note on
terminology evolution between the two preserved files: in
[support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) (lines 384–389), the
right-hand specification precondition combinator
(`defined := P ∧ (b q).defined`) was initially named `Behavior.when`;
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
308–348) harmonizes the naming across all Anneal workstreams so that
`Behavior.when` denotes angelic left-hand program gating ($\bot$-on-false),
`Behavior.given` denotes right-hand specification gating ($\top$-on-false), and
`Behavior.require` denotes demonic left-hand program gating ($\top$-on-false).
This report uses the harmonized triad names throughout and cross-references both
mechanizations where names differ.

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

### Part I — Behavior Codecs, Progress Refinement, Eventual Semantics, and Optimizer Anti-Degeneracy

#### 1. Taxonomy of Morphism Degeneracy Under Unconstrained `Monotone π`

`Basis: source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 369–413 at
`5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`), cross-language refinement judgments
are parameterized by an arbitrary mapping `π : L_src.Behavior → L_tgt.Behavior`:

- `Compiles L_src L_tgt π_c s t` is `L_tgt.sem t ≤ π_c (L_src.sem s)`.
- `Abstracts L_v L_src π_v v s` is `L_src.sem s ≤ π_v (L_v.sem v)`.
- `Compiler.SoundOn C s` is
  `Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)`.
- `Compiler.Verified C s spec` is
  `L_src.sem s ≤ spec ∧ Compiles L_src L_tgt C.π s (C.compile s)` conjoined with
  `L_tgt.sem (C.compile s) ≤ C.π spec`.

Because `Partial B` places `Partial.ub` (`defined := False`) at the top element
$\top$ of the refinement order and `Out → Prop` is ordered by subset inclusion
$\subseteq$ with `fun _ => True` at the top of defined outcome sets,
`Monotone π` leaves three unconstrained degrees of freedom:

1. **Definedness inflation:** `π` can map a defined source behavior (`defined :=
   True`) to `Partial.ub` (`defined := False`), vacating both target safety and
   target outcome refinement.
2. **Outcome-predicate coarsening:** `π` can preserve `defined` while mapping
   `val` to `fun _ => True` (or an existential image under a non-injective
   projection), erasing postconditions, trace observations, return values, or
   `.stuck` distinctions.
3. **Contravariant query distortion:** Even when `π` is restricted to the
   contravariant pullback form (`pullbackMorphism` in
   [MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), lines
   788–800), `monotone_pullbackMorphism` holds unconditionally for *any*
   functions `mapQ : L₂.Query → L₁.Query` and `mapOut : L₂.Out → L₁.Out`. In
   `trusted/lean/Trusted/StepResult.lean` (lines 172–188),
   `BehaviorOf M p ⟨init, 0⟩` admits only the `ReachesPrefix.zero` derivation
   (`outcome = .running`, `trace = []`), so `(BehaviorOf M p ⟨init, 0⟩).defined`
   is unconditionally `True` for every program `p`
   (`behaviorOf_steps_zero_defined`, lines 805–812). Projecting `q.steps` to `0`
   or `min q.steps K` therefore allows `mapQ` to hide source UB or manufacture
   target divergence while preserving `Monotone`.

| Class | Degenerate Morphism | `Monotone`? | Preserves `.defined` on `mapQ q`? | Uses Identity `mapOut = id`? | Pathologies Admitted Under `Compiler.SoundOn` / `Compiler.Verified` | Mechanized Theorems ([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean)) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **(a) Top collapse** | `π_top := fun _ _ => Partial.ub` | Yes (`monotone_π_top`, L666) | No (`defined := False`) | N/A | Compiles UB-free `.good` to `.immediateUb` (`.failed`) and `.stuck`; abstracts `.immediateUb` by `.good`; satisfies `C_top.Verified .good specGood` while target faults at step 1 | `compiles_π_top_trivial` (L672), `abstracts_π_top_trivial` (L677), `counterexample_class_a_masks_target_ub` (L685) |
| **(b) Chaotic defined outcome** | `π_chaosPure := fun _ _ => Partial.pure (fun _ => True)` and `π_chaosVal mapQ` | Yes (`monotone_π_chaosPure`, L712; `monotone_π_chaosVal`, L722) | Yes (`(π_chaosVal id b q).defined ↔ (b q).defined`) | No (`val := fun _ => True`) | Rejects target `.failed`/`.stuck` on `BehaviorOf` (since `out.isSafe` is in `.defined`), but compiles `.good` to `.wrongVal` (`999 ≠ 42`), `.infiniteLoop`, and `.silentReturn` (and to `.stuck` in `RawToyLang`) while satisfying `C_chaos.Verified .good specGood` | `counterexample_class_b_erases_postconditions` (L735), `counterexample_class_b_allows_stuck_when_defined` (L777) |
| **(c) Step-zero / bounded-fuel query distortion** | `π_stepZero := pullbackMorphism (fun q => ⟨q.init, 0⟩) id` and `π_boundedFuel K` | Yes (`monotone_π_stepZero`, L823; `monotone_π_boundedFuel`, L890) | Yes (`(π b q).defined = (b (mapQ q)).defined`) | Yes (`mapOut = id`) | `π_stepZero` maps `.immediateUb` to a `WellFormed` behavior and compiles both `.good` and `.immediateUb` to `.infiniteLoop` (`loop: jmp loop`) while satisfying `C_zero.Verified .good specGood`; `π_boundedFuel 1` masks step-2 UB in `.lateUb` and compiles `.good` to `.loopAfter1` | `behaviorOf_steps_zero_defined` (L805), `counterexample_class_c_stepZero_diverges_and_masks_ub` (L830), `counterexample_class_c_boundedFuel_masks_late_ub_and_divergence` (L902) |
| **(d) Observation & return-value erasure** | `covariantMorphism eraseTraceProj`, `covariantMorphism collapseValProj`, `pullbackMorphism id spoofOutContra` | Yes (`monotone_covariantMorphism`, L1055; `monotone_pullbackMorphism`, L794) | Yes (`mapQ = id`) | No (non-injective `proj` / `mapOut`) | Compiles `.good` (trace `[10]`, return `42`) to `.silentReturn` (trace `[]`, deleting volatile I/O) or `.wrongVal` (return `999`) while satisfying `C.Verified .good specGood` | `counterexample_class_d_erases_observations_and_values` (L1097) |

#### 2. Target Specification Anchoring vs. Step-Independent Blindness

`Basis: source + execution + derived`

In `theory/Anneal/Refinement.lean` (lines 269–286 at
`5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`), `verify_through_passes` combines an
upward abstraction pass `Abstracts L_v L_src π_v v s` with a downward
compilation pass `C.SoundOn s` to conclude `C.Verified s (π_v spec)`. Because
`L_tgt.sem (C.compile s) ≤ C.π (π_v spec)` evaluates the specification through
the composed morphism `C.π ∘ π_v`, an unanchored pass pipeline is vulnerable to
degeneracy in either `π_v` or `C.π`
([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), Section 4,
lines 1675–1788):

- **Unanchored pipeline vulnerability
  (`verify_through_passes_unanchored_vulnerable`, L1680):** Even when the
  compiler is the exact identity `C_id := { compile := id, π := id }`, choosing
  `π_v := π_top ToyLang ToyLang` allows `verify_through_passes` to prove
  `C_id.Verified .immediateUb (π_top ToyLang ToyLang specGood)` from
  `progGood_satisfies_specGood`, even though `.immediateUb` faults at step 1
  (`¬ (ToyLang.sem .immediateUb ≤ ToyLang.WellFormed)`).
- **Target-anchored pipeline (`verify_through_passes_anchored`, L1699, and
  `target_anchor_rejects_degenerate_classes`, L1722):** Adding an explicit
  target-anchor obligation `h_anchor : C.π (π_v spec_v) ≤ spec_tgt` yields
  `L_tgt.sem (C.compile s) ≤ spec_tgt` directly in `L_tgt.Behavior`. When
  `spec_tgt` is defined (`specGood`) and constrains traces and return values,
  `C.π specGood ≤ specGood` is provably false (`¬ (π specGood ≤ specGood)`) for
  Class (a) (`π_top`), Class (b) (`π_chaosVal id`), and Class (d)
  (`covariantMorphism collapseValProj`). When `spec_tgt` is step-sensitive
  (`specTerminatesAt2`, requiring
  `q.steps = 2 → out.outcome = .terminated (.normal 42)`), it also rejects
  `π_stepZero`.
- **Why step-independent target anchors are blind to Class (c)
  (`stepIndependent_target_anchor_blind_to_class_c`, L1769):** Every canonical
  specification in Anneal (`Language.WellFormed`, `Language.WellFormedOn pre`,
  `EnsuresRetLibInv`, and `specGood`) is **step-independent**: its precondition
  `pre q` and postcondition `post q out` inspect `q.init` and `out`, but not
  `q.steps`. Pulling back any step-independent specification `spec` along
  `q ↦ ⟨q.init, 0⟩` or `q ↦ ⟨q.init, capSteps q.steps K⟩` leaves `spec`
  **definitionally unchanged**:
  $$\pi_{\text{stepZero}}(\text{specGood}) = \text{specGood} \quad (\text{by }\texttt{rfl}), \qquad \pi_{\text{boundedFuel } K}(\text{specGood}) = \text{specGood} \quad (\text{by }\texttt{rfl}).$$
  Consequently, the degenerate compiler
  `C_zero := { compile := fun _ => .infiniteLoop, π := π_stepZero }` that
  compiles every source program to `loop: jmp loop` simultaneously satisfies:
  1. `C_zero.SoundOn .good`,
  2. `C_zero.Verified .good specGood`, and
  3. the target-anchoring inequality `C_zero.π specGood ≤ specGood` (by
     `Preorder.le_refl specGood`).

  In partial correctness (`SpecOn`), `.infiniteLoop` never reaches `.failed`,
  `.stuck`, or `.terminated`, so it vacuously satisfies `specGood` at every step
  budget. The only obligation that prevents `.good` from compiling to
  `.infiniteLoop` is the operational simulation
  `Compiles ToyLang ToyLang C.π .good .infiniteLoop`, which `π_stepZero`
  defeats by querying `.good` exclusively at `steps = 0` where `.good` is still
  `.running`. Target specification anchoring therefore cannot substitute for
  step-budget coverage in the compiler morphism.

#### 3. Admissible Simulation Couplings and Total Lockstep `BehaviorCodec`

`Basis: source + execution + derived`

In [MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) (Sections
4–6, lines 1303–2945), two composable structures eliminate all four degeneracy
classes **(a)–(d)**:

##### 3.1 Total `BehaviorCodec L₁ L₂` (1-to-1 Lockstep Retraction-Section Codec)

`BehaviorCodec L₁ L₂`
([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), lines
2719–2726; matching `trusted/lean/Trusted/Refinement.lean`, lines 155–169 at
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`) pairs:

1. **Query retraction (`encodeQuery : L₁.Query → L₂.Query`,
   `decodeQuery : L₂.Query → L₁.Query`):**
   `decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁`. This forces
   `decodeQuery` to be **surjective** onto `L₁.Query`
   (`BehaviorCodec.decodeQuery_surjective`, L2729), ruling out Class (c) step
   truncation while allowing `L₂.Query` to carry additional target-only state.
2. **Outcome section (`decodeOut : L₂.Out → L₁.Out`,
   `encodeOut : L₁.Out → L₂.Out`):**
   `encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂` (together with
   `decode_encode_out` in `Trusted/Refinement.lean`). This forces `decodeOut` to
   be **injective** on `L₂.Out` (`BehaviorCodec.decodeOut_injective`, L2736),
   ruling out Class (d) trace, value, and outcome conflation.
3. **Pullback morphism (`BehaviorCodec.toMorphism`, L2746):**
   `c.toMorphism := pullbackMorphism c.decodeQuery c.decodeOut`.

Kernel-verified properties in
[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) establish that
`BehaviorCodec`:

- is unconditionally `Monotone` (`BehaviorCodec.monotone_toMorphism`, L2751),
- preserves `.defined` bi-directionally at every `q₂`
  (`BehaviorCodec.toMorphism_defined_iff`, L2757, ruling out Class (a)) and
  recovers `(b q₁)` exactly at `c.encodeQuery q₁`
  (`BehaviorCodec.toMorphism_encodeQuery`, L2772, and
  `BehaviorCodec.toMorphism_encodeQuery_val_iff`, L2781, ruling out Class (b)),
- is closed under `BehaviorCodec.id` (L2794) and `BehaviorCodec.comp` (L2807)
  with **strict definitional functoriality (`rfl`)**:
  `(BehaviorCodec.id L).toMorphism b = b` (`id_toMorphism`, L2802) and
  `(c₁₂.comp c₂₃).toMorphism b = c₂₃.toMorphism (c₁₂.toMorphism b)`
  (`comp_toMorphism`, L2821), and
- **bi-directionally preserves both termination and non-termination** on
  deterministic source / total target machines
  (`BehaviorCodec.compiles_bidirectional_outcome`, L2832): when `s` has unique
  outcome `o₁` at `q₁` and `t` is total at `c.encodeQuery q₁`,
  `Compiles L₁ L₂ c.toMorphism s t` forces every target outcome `o₂` at
  `c.encodeQuery q₁` to satisfy `c.decodeOut o₂ = o₁` and `o₂ = c.encodeOut o₁`.

##### 3.2 `ExecSimCoupling` and `AdmissibleExecCoupling` ($1 \to k$ Multi-Step)

For multi-step passes where 1 source step lowers to $k \ge 2$ target steps
over step-indexed `ExecQuery State`, a single-valued query pullback
`decodeQuery : L₂.Query → L₁.Query` is insufficient: at an intermediate target
micro-step $n_2 = k \cdot m + r$ ($0 < r < k$), the target's `.running` outcome
corresponds to completed source step $\lfloor n_2 / k \rfloor = m$, whereas a
mid-instruction target fault (`.failed`) must be gated by source safety at
started source step $\lceil n_2 / k \rceil = m + 1$.

`ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂`
([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), lines
1341–1380) couples step budgets via a relation
`stepCoupling : Nat → Nat → Prop` and induces `C.toMorphism` via dual
universal/existential quantification:

```lean
def ExecSimCoupling.toMorphism
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (b : Behavior (ExecQuery State₁) (ExecOut Obs₁ Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Obs₂ Val₂) :=
  fun q₂ => {
    defined :=
      ∀ n₁, C.stepCoupling q₂.steps n₁ →
        (b ⟨C.decompileInit q₂.init, n₁⟩).defined
    val := fun h out₂ =>
      ∃ n₁, ∃ (hn₁ : C.stepCoupling q₂.steps n₁),
        (b ⟨C.decompileInit q₂.init, n₁⟩).val (h n₁ hn₁) (C.decompileOut out₂)
  }
```

where `C.decompileOut` maps `⟨tr₂, outc₂⟩` to
`⟨C.decompileTrace tr₂, outc₂.map C.decompileVal⟩`, preserving `.running`,
`.terminated (.normal _)`, `.terminated .unwind`, `.failed`, and `.stuck`
constructors 1-to-1 (`PrefixOutcome.map`, L1316). `AdmissibleExecCoupling C`
(lines 1402–1423) requires four conditions:

1. `step_nonempty : ∀ n₂, ∃ n₁, C.stepCoupling n₂ n₁`,
2. `step_coverage : ∀ n₁, ∃ n₂, C.stepCoupling n₂ n₁` conjoined with uniqueness
   `∀ n₁', C.stepCoupling n₂ n₁' → n₁' = n₁`,
3. `trace_injective` on `C.decompileTrace`, and
4. `val_injective` on `C.decompileVal`.

Sections 4–6 of
[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) prove that
`AdmissibleExecCoupling`:

- is constructively `Monotone` (`ExecSimCoupling.monotone_toMorphism`, L1375),
  maps `SpecOn` to `SpecOn` (`toMorphism_specOn_le`, L1438), and satisfies
  `C.toMorphism L₁.WellFormed ≤ L₂.WellFormed` (`toMorphism_wellFormed_le`,
  L1471);
- rules out Class (a) (`admissible_rules_out_class_a_target_ub_and_stuck`,
  L1482; `π_top_not_admissible`, L1498), Class (b) (`π_chaosVal_not_admissible`,
  L1509), Class (c) (`stepZero_not_step_coverage`, L1528;
  `boundedFuel_not_step_coverage`, L1543;
  `admissible_rules_out_class_c_late_ub_and_divergence`, L1560), and Class (d)
  (`admissible_rules_out_class_d_trace_and_val_erasure`, L1619);
- is closed under identity (`AdmissibleExecCoupling.id`, L1802) and composition
  (`AdmissibleExecCoupling.comp`, L1867; `Compiles.comp_coupling`, L1972;
  `Abstracts.comp_coupling`, L1988); and
- verifies a concrete $1 \to 2$ multi-step lowering
  `MirMultiLang → X86MultiLang` (`compileMirToX86_compiles`, L2350) using
  `stepCoupling n₂ n₁ := n₁ = div2 n₂ ∨ n₁ = ceil2 n₂`
  (`admissible_mirToX86Coupling`, L2153), where single-valued floor pullback
  alone fails on `.failNow` at `n₂ = 1` (`not_compiles_floor_only_failNow`,
  L2409) and single-valued ceiling pullback alone fails on `.incAndRet` at
  `n₂ = 1` (`not_compiles_ceil_only_incAndRet`, L2430), and composes end-to-end
  with an upward functional abstraction `FuncLang → MirMultiLang`
  (`endToEnd_func_mir_x86_verified`, L2667).

#### 4. Variable-Step Stuttering and Eventual Semantics (`EventualBehaviorOf`)

`Basis: source + execution + derived`

In `theory/Anneal/Compiler/NaiveCodegen.lean` (lines 148–153 and 264–288 at
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`), `compileStmt` maps each MIR
statement to a single x86-64 instruction (`k = 1`), allowing `naiveCodec` to
copy the step budget unchanged (`steps := q.steps`). Realistic instruction
selection violates 1-to-1 step lockstep whenever some MIR statements lower to
`k = 0` instructions (e.g., `PlaceElem::Downcast`, `StorageLive`, `Nop`) and
others lower to `k ≥ 2` instructions (e.g., niche discriminant decoding or
compound `Rvalue` trees).

In
[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean)
(Section 2, lines 278–757), `s_var = [.downcast, .nicheDecodeRet]` models a
2-statement MIR program where statement 0 (`downcast`) takes 1 source step and
emits `0` target instructions (`[]`), and statement 1 (`nicheDecodeRet`) takes 1
source step and emits `3` target instructions
(`[.incAcc, .incAcc, .incAccRet]`):

| Step budget `steps` | Source `s_var` outcome (`VarMirMachine`) | Target `t_var` outcome (`VarX86Machine`) | Match under 1-to-1 `lockstepCodec`? |
| :--- | :--- | :--- | :--- |
| `0` | `.incomplete` | `.incomplete` | Yes |
| `1` | `.incomplete` | `.incomplete` | Yes |
| `2` | `.terminated (.normal (acc + 3))` | `.incomplete` | **No** (`t_var` is `.incomplete`, `s_var` has terminated) |
| `n + 3` | `.terminated (.normal (acc + 3))` | `.terminated (.normal (acc + 3))` | Yes |

This yields two mechanized impossibility results:

1. **Failure of 1-to-1 `lockstepCodec` (`lockstep_codec_fails_on_s_var`,
   L638):** At `q₂ = ⟨⟨0, 0⟩, 2⟩`, `t_var` produces `PrefixOutcome.incomplete`
   while `s_var` at `steps = 2` produces only `.terminated (.normal 3)`,
   refuting `Compiles` under `lockstepCodec.toMorphism`.
2. **Impossibility of any state-independent query step projection
   (`no_state_independent_step_map_for_variable_lowering`, L676):** Consider
   `s_fast = [.downcast, .retNow]`, which terminates in `2` source steps while
   `t_fast = compileVarProg s_fast = [.retNow]` terminates in `1` target step.
   Validating `s_fast → t_fast` at target budget `steps = 1` requires `s_fast`
   to have terminated at `stepMap 1`, forcing `stepMap 1 ≥ 2`; validating
   `s_var → t_var` at target budget `steps = 1` requires `s_var` to still be
   `.incomplete` at `stepMap 1`, forcing `stepMap 1 < 2`. Thus no
   state-independent function `stepMap : Nat → Nat` can serve as a pass-level
   `BehaviorCodec` for variable-step lowering.

Sections 3 and 4 of
[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean)
(lines 758–1297) mechanize and compare two 100% constructive
(`0 Classical.choice`, `0 coinduction`) replacements:

- **Architecture A — Bounded-Dilation `ExecQuery` Codec (`DilationCodec`,
  lines 767–1031):** Retains `Query := ExecQuery State` and equips the codec
  with a monotone, unbounded step-dilation window `[srcFloor n, srcCeil n]`
  (`floor_unbounded : ∀ M, ∃ N, ∀ n, N ≤ n → M ≤ srcFloor n`). While
  `DilationCodec` is monotone (`DilationCodec.monotone_toMorphism`, L803),
  rejects `loopX86Prog` (`dilationCodec_rejects_loopCodegen`, L932), and
  verifies `s_var → t_var` with `srcFloor n := n / 3` and `srcCeil n := n + 1`
  (`dilationCodec_verifies_s_var`, L970), it adds 6 step-dilation fields to
  `BehaviorCodec`, cannot express runtime data-dependent step ratios, and
  composes only laxly (`DilationCodec.comp_toMorphism_le`, L860:
  `c₂.toMorphism (c₁.toMorphism b) ≤ (c₂.comp c₁).toMorphism b`).
- **Architecture B — Step-Decoupled Eventual-Outcome Semantics
  (`EventualBehaviorOf`, lines 1050–1297):** Keeps `ReachesPrefix` inductive
  while moving the operational fuel coordinate `steps : Nat` inside the
  semantics constructor `EventualBehaviorOf` (`Query := State`,
  `Out := EventualOut Obs Val`):
  ```lean
  inductive EventualOut (Obs Val : Type) where
    | terminated (trace : List Obs) (term : TerminationKind Val)
    | diverges

  def EventualBehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
      State → Partial (EventualOut Obs Val → Prop) :=
    fun init => {
      defined :=
        M.initState p init →
          ∀ (n : Nat) (tr : List Obs) (out : PrefixOutcome Val),
            ReachesPrefix M p n init tr out →
            out.isSafe
      val := fun _ ev =>
        M.initState p init ∧
        match ev with
        | .terminated tr term =>
          ∃ (n : Nat), ReachesPrefix M p n init tr (.terminated term)
        | .diverges =>
          ∀ (n : Nat), ∃ (tr : List Obs),
            ReachesPrefix M p n init tr .incomplete
    }
  ```
  `EventualBehaviorOf` requires zero `Classical.choice`
  (`exists_nat_no_choice_canary`, L1050), is propositionally equivalent (with
  **zero axioms**) to all-prefix safety under `BehaviorOf`
  (`eventual_wellFormed_iff_prefix_wellFormed`, L1098), strictly rejects
  `loopX86Prog` (`eventual_rejects_loopCodegen`, L1164), and verifies both
  `s_var → t_var` (`eventual_verifies_s_var`, L1196) and `s_fast → t_fast`
  (`eventual_verifies_s_fast`, L1247) under the **exact same** step-free
  identity codec `eventualVarCodec` (L1150).

| Criterion | Step-Indexed `BehaviorOf` + `TotalBehaviorCodec` | Architecture A (`DilationCodec`) | Architecture B (`EventualBehaviorOf` + `PartialBehaviorCodec`) |
| :--- | :--- | :--- | :--- |
| Constructive (`0 Classical.choice`, `0 coinduction`)? | Yes | Yes | **Yes** |
| All-prefix UB-freedom preserved? | Yes | Yes (within window) | **Yes** (`eventual_wellFormed_iff_prefix_wellFormed`, 0 axioms) |
| Rejects `loopCodegen` (`bb0: jmp bb0`)? | Yes | Yes (`dilationCodec_rejects_loopCodegen`) | **Yes** (`eventual_rejects_loopCodegen`) |
| Handles fixed variable-step passes ($k = 0, 3$)? | **No** (`lockstep_codec_fails_on_s_var`) | Yes (`dilationCodec_verifies_s_var`) | **Yes** (`eventual_verifies_s_var`) |
| Handles unbounded / data-dependent step ratios? | No | **No** (bounds depend only on `n`) | **Yes** (`∃ n` in `.terminated`) |
| Extra fields required in `BehaviorCodec` | 0 (7 fields total) | +6 fields (`srcFloor`, `srcCeil`, 4 laws) | **0** (7 fields total) |
| Functorial composition of `.toMorphism` | Strict (`=`) | Lax (`≤` only) | **Strict (`=`)** |

#### 5. Non-Surjectivity Obstruction and `PartialBehaviorCodec`

`Basis: source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 155–169), `BehaviorCodec`
requires `encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂`, which forces
`encodeOut : L₁.Out → L₂.Out` to be **surjective** onto `L₂.Out`. Whenever the
target outcome carrier has strictly greater cardinality than the source outcome
carrier—such as an 8-bit or 64-bit x86-64 register (`UInt8`, `UInt64`, or `Nat`)
holding a 2-valued Rust `bool` where `0` encodes `false`, `1` encodes `true`,
and `2..255` are invalid bit patterns—no total section-retraction pair can
exist
([BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean),
Section 5, lines 1298–1802):

- **Impossibility of total section-retraction
  (`no_total_section_for_bool_in_uint8`, L1311, and
  `no_total_section_for_bool_in_nat`, L1349):** No total functions
  `encodeOut : Bool → UInt8` (or `Nat`) and `decodeOut : UInt8 → Bool` (or
  `Nat → Bool`) can satisfy `∀ o₂, encodeOut (decodeOut o₂) = o₂`. Furthermore,
  dropping `encode_decode_out` while keeping `decodeOut` total (e.g., mapping
  `2 ↦ true`) unsoundly accepts a buggy target program that outputs `al = 2` for
  a `bool`.
- **Partial outcome decoding (`PartialBehaviorCodec`, lines 1384–1404):**
  Replacing `decodeOut : L₂.Out → L₁.Out` with
  `decodeOut : L₂.Out → Option L₁.Out` governed by
  `decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁` and
  `encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
  strictly generalizes `TotalBehaviorCodec`
  (`TotalBehaviorCodec.toPartialCodec`, L1407) with the same 7-field footprint:
  ```lean
  structure PartialBehaviorCodec (L₁ L₂ : Language) where
    encodeQuery : L₁.Query → L₂.Query
    decodeQuery : L₂.Query → L₁.Query
    decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
    encodeOut : L₁.Out → L₂.Out
    decodeOut : L₂.Out → Option L₁.Out
    decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
    encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂

  def PartialBehaviorCodec.toMorphism {L₁ L₂ : Language}
      (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
    fun q₂ =>
      let p := b (c.decodeQuery q₂)
      { defined := p.defined
        val := fun h o₂ => ∃ o₁, c.decodeOut o₂ = some o₁ ∧ p.val h o₁ }
  ```
- **Kernel-verified properties of `PartialBehaviorCodec` (lines 1421–1802):**
  1. *Bi-directional injectivity:* `c.encodeOut` is injective
     (`encodeOut_injective`, L1421) and `c.decodeOut` is injective on `some`
     (`decodeOut_injective_on_some`, L1433), preventing distinct target bit
     patterns `o₂ ≠ o₂'` from decoding to the same `some o₁`.
  2. *Automatic rejection of invalid target bit patterns:* Whenever
     `c.decodeOut o₂ = none`, `¬ (c.toMorphism b q₂).val h o₂`
     (`invalid_target_out_rejected`, L1447), and any target program `t` that can
     emit `o₂` at a defined query is automatically rejected by `Compiles`
     (`compiles_rejects_invalid_target_out`, L1460).
  3. *Monotonicity, definedness preservation, and exact recovery:*
     `monotone_toMorphism` (L1474), `toMorphism_defined` (L1485),
     `toMorphism_encodeQuery_defined` (L1493), and `toMorphism_val_encodeOut`
     (L1502).
  4. *Identity and strict functorial composition via `Option.bind`:*
     `PartialBehaviorCodec.id` (L1517), `PartialBehaviorCodec.comp` (L1530),
     `comp_toMorphism_iff` (L1556, 0 axioms), `id_toMorphism` (L1583), and
     `comp_toMorphism` (L1596).
  5. *Concrete `MirAbiVal ↔ X86RawVal` instantiation:* `mirToX86AbiCodec`
     (L1760) verifies valid boolean negation (`0 ↔ 1`,
     `valid_bool_negation_compiles`, L1773) and automatically rejects a corrupt
     target implementation returning `.boolWord 2`
     (`corrupt_bool_bitpattern_2_rejected`, L1793).

#### 6. Certifying Pass Anti-Degeneracy and `CertifiedOptimizationPass`

`Basis: source + execution + derived`

Auditing `theory/Anneal/Compiler/Peephole.lean` (lines 45–205 at
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`) alongside
`theory/Anneal/MirLemmas.lean` (lines 380–755) and
`trusted/rustc-capture/src/lib.rs` (lines 1166–1340), and mechanizing the pass
in
[AntiDegeneracyAndCallbackFraming.lean](support/AntiDegeneracyAndCallbackFraming.lean)
(Section 3, lines 708–1565), reveals four findings:

1. **`Peephole.lean` is unwired, shallow on call trees, and a complete no-op on
   the `MirLemmas.lean` corpus (`peephole_noop_on_corpus`, L867):**
   - `optimizePeephole`, `PeepholeCompiler`, and `compileOptimized` are never
     referenced outside `Peephole.lean`; `rustc-capture` and `MirLemmas.lean`
     verify unoptimized Stage 0 `X86Body` values directly.
   - `optimizePeephole` maps `optimizeBlock` over `body.blocks`
     (`Peephole.lean`, line 66) but leaves `body.requiredConsts` and the
     `callee : X86Body` inside `X86Term.call1` (line 59) unoptimized; the
     step-commutation proof `evalX86Step_optimizePeephole` (line 115) relies on
     this omission so that `evalX86Step` inside `s.curBody = some callee`
     commutes by `rfl`.
   - Because unoptimized `rustc -Z mir-opt-level=0` MIR materializes operands
     into stack slots before binary operations or conditional branches,
     `optimizeInstr` (which matches only `.alu op dst (.imm v1) (.imm v2)`) and
     `optimizeTerm` (which matches only `.jccBool (.imm (.boolVal b)) ...`)
     never fire on Stage 0 output. On all four corpus functions in
     `MirLemmas.lean` (`idCopyBody`, `newUncheckedBody`, `makeNonZeroBody`, and
     `getUncheckedNonZeroBody`), `optimizePeephole body = body` holds by `rfl`
     (`peephole_noop_on_corpus`, L867).
2. **Vacuous translation validators (Trap 1) and identity optimizers (Trap 2):**
   In `runValidatedPass` (`if checkCert s t cert then t else s`, L739), the
   trivial validator `alwaysFalseCertifier := fun _ _ _ => false` satisfies
   `Compiles X86Lang X86Lang id s` on
   `runValidatedPass alwaysFalseCertifier s t cert` for every `s`, `t`, and
   `cert` via a 1-line `Preorder.le_refl` proof (`trap1_alwaysFalse_compiles`,
   L753) while rejecting 100% of optimizations
   (`trap1_alwaysFalse_never_accepts`, L760). Likewise, `idOptimizer s := s`
   satisfies `Compiles X86Lang X86Lang id s (idOptimizer s)` by
   `Preorder.le_refl` (`trap2_id_compiles`, L777).
3. **Why `Compiles X86Lang X86Lang id` forbids instruction deletion
   (`compiles_id_forbids_instruction_deletion`, L916):**
   In `BehaviorOf M p (q : ExecQuery State)`, every `ReachesPrefix.step`
   transition increments `q.steps` by `1` and prepends `()` to
   `out.trace : List Unit`. Under `PeepholeCompiler`'s identity behavior
   morphism `π = id` (`Peephole.lean`, line 179),
   `Compiles X86Lang X86Lang id s t` requires `t` to match `s` at the exact same
   step count `q.steps` and trace length `out.trace.length`. Consequently,
   deleting a single `.nop` instruction from the 2-instruction function
   `nopConstBody` (`.nop; .mov _0 42; .ret`, terminating at step 3) to produce
   `elimNopConstBody` (`.mov _0 42; .ret`, terminating at step 2) is **provably
   rejected** by `Compiles X86Lang X86Lang id`
   (`¬ Compiles X86Lang X86Lang (fun b => b) nopConstBody elimNopConstBody`,
   L916).
4. **Step-rescaling morphism `π_opt` and the `CertifiedOptimizationPass`
   contract (lines 991–1565):**
   Defining the step-rescaling morphism
   `π_opt : X86Lang.Behavior → X86Lang.Behavior` (L991):
   ```lean
   def π_opt (b : X86Lang.Behavior) : X86Lang.Behavior :=
     fun q => {
       defined := ∀ steps_src, (b { init := q.init, steps := steps_src }).defined
       val := fun hDef out =>
         ∃ steps_src tr_src,
           (b { init := q.init, steps := steps_src }).val (hDef steps_src)
             { trace := tr_src, outcome := out.outcome }
     }
   ```
   preserves monotonicity (`monotone_π_opt`, L1000), `WellFormedOn`
   (`π_opt_preserves_wellFormedOn`, L1015), and `EnsuresRetLibInv`
   (`π_opt_preserves_ensuresRetLibInv`, L1025). Pairing `π_opt` with
   `CertifiedOptimizationPass` (L1101)—which conjoins universal soundness of
   `runValidatedPass` under `π_opt`, constructive non-vacuity
   (`checkCert s_bench (pass s_bench) (genCert s_bench) = true`), strict static
   cost reduction (`staticCost (pass s_bench) < staticCost s_bench`), and strict
   dynamic step reduction (`steps_opt < steps_src` with
   `TerminatesInMinSteps`)—provably rejects `alwaysFalseCertifier`
   (`trap1_rejected_by_contract`, L1131), `idOptimizer`
   (`trap2_id_rejected_by_contract`, L1142), and `optimizePeephole` on
   `newUncheckedBody` (`peephole_on_newUnchecked_rejected`, L1154), while
   accepting the move/wrap-coalescing and constant-folding pass
   `coalesceAndFoldBody` (`genuineCoalescePass_certified`, L1540), which reduces
   `newUncheckedBody` from `staticCost = 7` (5 dynamic steps) to
   `staticCost = 3` (2 dynamic steps).

### Part II — Partial Compilation and Behavioral Conditioning Refinement Algebra

#### 1. Problem Framing and Partial `compile` Representations

`Basis: normative + source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 448–473), `Trusted.Compiler`
currently assumes that compilation is a total function:

```lean
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior
```

Real compilers and verification passes violate totality in two ways:

1. **Post-Monomorphization Errors (PMEs) and backend rejections in `rustc`:**
   `anneal-rustc-capture` extracts `Runtime(PostCleanup)` MIR before
   monomorphization-time `const { assert!(...) }` evaluation, layout and size
   overflow checks, inline-assembly constraint validation, and backend code
   generation. A captured `MirBody` (or a generic instantiation of it) can
   therefore be rejected by `rustc` during monomorphization or codegen.
2. **Partiality in computable Lean lowering passes:** Executable lowering
   passes written in Lean (returning `Option L_tgt.Prog`) can reject
   unsupported instructions or control-flow shapes.

Refining `Trusted/Refinement.lean` and `theory/Anneal/Refinement.lean` to
support partial `compile` must preserve five repository invariants
(`PRINCIPLES.md`, `AGENTS.md`, `trusted/audit/TrustedBoundary.lean`):

1. **No fail-open verification:** Anneal must never report that a function with
   reachable runtime UB is verified because of an unproved or vacuous compiler
   definedness assumption.
2. **TCB auditability and zero-theorem rule:** `Trusted/Refinement.lean` must
   contain only definitions, classes, structures, inductives, and named
   instances (zero theorems), with every declaration marked `@[vetted]` or
   `@[candidate refinement]`.
3. **Constructive, axiom-minimal preorder:** Core definitions and composition
   lemmas must not require `Classical.choice` or `Decidable` instances on
   semantic propositions.
4. **Transitive multi-pass composition:** Vertical compiler pipelines
   (`Compiler.comp`, `Compiles.comp`, `Compiler.Verified.comp`) and Y-diagram
   verification (`verify_through_passes`) must compose across partial passes.
5. **Backward compatibility with existing proofs:** Existing crate-discharge
   lemmas (`Compiler.SoundOn.verify`, `verify_through_passes`,
   `Compiler.Verified.mono`, `Compiler.Verified.with_wellFormedOn`) must retain
   their theorem signatures so existing proofs in `theory/Anneal/` and
   generated `.anneal/Proof.lean` scripts require no structural changes.

##### 1.1 Comparing `Partial L_tgt.Prog` and `Option L_tgt.Prog`

| Dimension | Baseline (`L_src.Prog → L_tgt.Prog`) | Design A (`L_src.Prog → Partial L_tgt.Prog`) | Design B (`L_src.Prog → Option L_tgt.Prog`) |
| :--- | :--- | :--- | :--- |
| **New types in `Trusted/Refinement.lean`** | 0 (baseline) | **0** (reuses existing `Partial`) | 0 (uses `Init` `Option`), but introduces a second partiality carrier alongside `Partial` |
| **Propositional definedness (PME predicates, `opaque rustc`)** | Requires subtype `Prog` or dummy target artifacts | **Native** (`defined : Prop`, `val : defined → L_tgt.Prog`) | Requires `Decidable` or `Classical.choice` to package a `Prop`-guarded compilation into `Option` |
| **Computable partial passes (`Option`)** | Not expressible without dummy values | **Direct via `Option.toPartial`** (`some t ↦ Partial.pure t`, `none ↦ Partial.ub`) | Native (`Option.bind`) |
| **Pass composition (`Compiler.comp`)** | Function composition `C₂.compile ∘ C₁.compile` | `Partial.bind (C₁.compile s) C₂.compile` | `Option.bind (C₁.compile s) C₂.compile` |
| **Proof ergonomics on `opaque rustc`** | Direct application `rustc body` | `h : (rustc body).defined` and `(rustc body).val h` (same `.defined`/`.val` API as `Behavior`) | `∀ t, rustc body = some t → ...` (equational unpacking) |

`Partial B` (`defined : Prop`, `val : defined → B`, `Trusted/Refinement.lean`
lines 292–295) is the semantic model of partiality in Anneal, whereas
`Option B` is the computable realization of `Partial B` when `.defined` is
decidable:

1. **Zero new carrier concepts in `Trusted/Refinement.lean`:** Using
   `compile : L_src.Prog → Partial L_tgt.Prog` represents both runtime
   partiality (UB at query `q`) and compile-time partiality (PME or lowering
   rejection of program `s`) with the same two-field structure.
2. **Dependent monadic bind (`Partial.bind`) and monad laws:** Sequential
   composition of partial values is defined in
   [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) (lines 135–138,
   238–266) and
   [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
   169–173, 203–240) by:
   ```lean
   def Partial.bind {B₁ : Type u} {B₂ : Type v}
       (p : Partial B₁) (f : B₁ → Partial B₂) : Partial B₂ where
     defined := ∃ h : p.defined, (f (p.val h)).defined
     val h := (f (p.val h.1)).val h.2
   ```
   Up to structural equivalence `Partial.Equiv p₁ p₂`
   (`(p₁.defined ↔ p₂.defined) ∧ ∀ h₁ h₂, p₁.val h₁ = p₂.val h₂`, which
   requires no `Preorder` on `B`), `Partial.bind` satisfies left
   identity (`Partial.bind_pure_left`), right identity
   (`Partial.bind_pure_right`), and associativity (`Partial.bind_assoc`), and
   is monotone in its continuation (`Partial.bind_mono_right`).
3. **Exact computable pass embedding (`Option.toPartial`) and decidable
   isomorphism:** Every computable `Option B` embeds into `Partial B` via
   ([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 275–370):
   ```lean
   def Option.toPartial {B : Type u} : Option B → Partial B
     | some b => Partial.pure b
     | none => Partial.ub

   def Partial.toOption {B : Type u} (p : Partial B) [Decidable p.defined] :
       Option B :=
     if h : p.defined then some (p.val h) else none
   ```
   Because `Option.toPartial` pattern-matches on `Option`,
   `Option.toPartial (some b) = Partial.pure b` (`Option.toPartial_some`) and
   `Option.toPartial none = Partial.ub` (`Option.toPartial_none`) hold by
   kernel `rfl`. Furthermore:
   - `Option.toPartial_defined_iff`:
     `(Option.toPartial o).defined ↔ ∃ b, o = some b`.
   - `Option.eq_some_iff_toPartial`: `o = some b` holds iff
     `∃ h : (Option.toPartial o).defined, (Option.toPartial o).val h = b`.
   - `Option.toPartial_bind`: `Option.toPartial (o.bind f)` is structurally
     equivalent (`Partial.Equiv`) to
     `Partial.bind (Option.toPartial o) (fun x => Option.toPartial (f x))`.
   - `Option.toOption_toPartial` and `Partial.toPartial_toOption`: whenever
     `[Decidable p.defined]` holds, `Option B` and `Partial B` are isomorphic
     up to `Partial.Equiv`.
   - Computable partial compilers `compile : L_src.Prog → Option L_tgt.Prog`
     lift via `Compiler.ofOption` (`compile s := Option.toPartial (compile s)`)
     and unfold directly to `compile s = some t` via
     `Compiler.ofOption_soundOn_iff` and `Compiler.ofOption_verified_iff`
     ([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 637–641,
     1397–1436).

---

#### 2. The Harmonized Conditioning Triad and Dependent Liftings

`Basis: source + execution + derived`

##### 2.1 Lattice Extremals and the Polarity of Behavioral Conditioning

In `Trusted/Refinement.lean` (lines 326–333), `Partial B` is ordered by forward
simulation:

```lean
le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
```

At each query `q : L.Query`, the observation-predicate lattice
`Partial (L.Out → Prop)` has two extremal elements
([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 113–121,
191–235;
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
149–158, 193–200):

- **Top ($\top = \mathsf{Partial.ub}$):** `defined := False`,
  `val := False.elim`. On the **right-hand side** of `≤` (as a specification),
  `p ≤ Partial.ub` holds vacuously for every `p` (`ub_top`). On the **left-hand
  side** of `≤` (as a program), `Partial.ub ≤ p` holds if and only if
  `¬ p.defined` (`ub_le_iff`), and never refines `Partial.pure b`
  (`not_ub_le_pure`).
- **Bottom ($\bot = \mathsf{Partial.bot}$):** `defined := True`,
  `val := fun _ _ => False` (`Partial.pure (fun _ => False)`). On the
  **left-hand side** of `≤` (as a program), `Partial.bot ≤ p` holds vacuously
  for every `p : Partial (Out → Prop)` (`bot_le`). On the **right-hand side**
  of `≤`, `p ≤ Partial.bot ↔ ∃ h : p.defined, ∀ o, ¬ p.val h o` (`le_bot_iff`).

Conditioning a behavior on a compile-time proposition `P : Prop` (such as
`(C.compile s).defined` or `body.CompileAdmitted`) therefore has three distinct
operational roles depending on whether `¬ P` maps to $\bot$ or $\top$ and
whether the operator stands on the left or right of `≤`:

| Harmonized Operator | Definition at Query `q` | Limit when `¬ P` | Position in `≤` | Operational Role |
| :--- | :--- | :--- | :--- | :--- |
| `Behavior.when P b` | `defined := P → (b q).defined`, `val := fun h o => ∃ hp : P, (b q).val (h hp) o` | `Partial.bot` ($\bot$) | Left-hand side (`Behavior.when P b ≤ spec`) | Angelic / conditional program gating |
| `Behavior.given P spec` | `defined := P ∧ (spec q).defined`, `val := fun h => (spec q).val h.2` | `Partial.ub` ($\top$) | Right-hand side (`b ≤ Behavior.given P spec`) | Precondition specification gating |
| `Behavior.require P b` | `defined := P ∧ (b q).defined`, `val := fun h => (b q).val h.2` | `Partial.ub` ($\top$) | Left-hand side (`Behavior.require P b ≤ spec`) | Demonic program assertion |

##### 2.2 Algebraic Laws of the Harmonized Conditioning Triad

In [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
315–502), the three conditioning operators and their exact laws are mechanized
constructively:

```lean
def Behavior.when {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P → (b q).defined
    val := fun h o => ∃ hp : P, (b q).val (h hp) o
  }

def Behavior.given {Query Obs : Type} (P : Prop) (spec : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun h => (spec q).val h.2
  }

def Behavior.require {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P ∧ (b q).defined
    val := fun h => (b q).val h.2
  }
```

Although `Behavior.given P` and `Behavior.require P` share the same underlying
term structure, giving them distinct names makes the lattice polarity of every
refinement inequality immediately legible to human auditors:

1. **Definitional specialization to `SpecOn` and `WellFormedOn`
   (`specOn_and_eq_given`, `wellFormedOn_and_eq_given`):** Conjoining `P` onto
   the query precondition `pre` of `L.SpecOn` or `L.WellFormedOn` is
   **definitionally equal** (`rfl`) to `Behavior.given P`
   ([support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
   352–362; also [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines
   455–468 as `specOn_and_eq_when` / `wellFormedOn_and_eq_when`):
   ```lean
   theorem specOn_and_eq_given (L : Language) (P : Prop)
       (pre : L.Query → Prop) (post : L.Query → L.Obs → Prop) :
       L.SpecOn (fun q => P ∧ pre q) post =
         Behavior.given P (L.SpecOn pre post) := rfl

   theorem wellFormedOn_and_eq_given (L : Language) (P : Prop)
       (pre : L.Query → Prop) :
       L.WellFormedOn (fun q => P ∧ pre q) =
         Behavior.given P (L.WellFormedOn pre) := rfl
   ```
2. **The Fundamental Galois Connection (`when` $\dashv$ `given`,
   `behavior_when_given_adjunction`):** `Behavior.when P` on the left of `≤` is
   left adjoint to `Behavior.given P` on the right of `≤`, with the meta-level
   implication `P → b ≤ spec` in the middle, proved with **zero axioms**
   ([support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
   366–414):
   ```lean
   theorem behavior_when_given_adjunction {Query Obs : Type} (P : Prop)
       (b spec : Behavior Query Obs) :
       (Behavior.when P b ≤ spec ↔ (P → b ≤ spec)) ∧
       ((P → b ≤ spec) ↔ b ≤ Behavior.given P spec)
   ```
   Once `hp : P` is established, `Behavior.le_of_le_given_of_true` discharges
   `Behavior.given P spec` to yield `b ≤ spec`.
3. **Universal property of `Behavior.require P` (`behavior_require_le_iff` and
   `behavior_require_le_iff_of_defined`):** Placing `Behavior.require P b` on
   the left of `≤` requires `P` to hold at every query where `spec` is defined
   ([support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
   420–453):
   ```lean
   theorem behavior_require_le_iff {Query Obs : Type} {P : Prop}
       {b spec : Behavior Query Obs} :
       Behavior.require P b ≤ spec ↔
         (∀ q, (spec q).defined → P) ∧ (P → b ≤ spec)

   theorem behavior_require_le_iff_of_defined {Query Obs : Type} {P : Prop}
       {b spec : Behavior Query Obs} {q₀ : Query} (hq₀ : (spec q₀).defined) :
       Behavior.require P b ≤ spec ↔ P ∧ b ≤ spec
   ```
4. **Lattice ordering and collapse under `P`:** For any `P : Prop` and
   `b : Behavior Query Obs`,
   `Behavior.when P b ≤ b ≤ Behavior.given P b = Behavior.require P b`
   (`when_le_self`, `self_le_given`, `self_le_require`, `when_le_require`), and
   when `hp : P` holds, all three are mutually refining (`≈`) with `b`
   (`when_equiv_of_true`, `given_equiv_of_true`, `require_equiv_of_true`).

##### 2.3 Dependent Liftings and Why `Compiler.SoundOn` Rejects `semPartial`

When a partial compiler `C : Compiler L_src L_tgt` produces
`p? := C.compile s : Partial L_tgt.Prog`, the target program
`(C.compile s).val h` depends on the proof `h : (C.compile s).defined`. The two
left-hand-side program-gating operators (`Behavior.when` and `Behavior.require`)
lift to dependent partial programs `p? : Partial L.Prog`
([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 478–584;
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
514–619):

```lean
/-- Lifting 1: Dependent angelic / conditional lifting (⊥-on-rejection). -/
def Language.semIfCompiled (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => {
    defined := ∀ h : p?.defined, (L.sem (p?.val h) q).defined
    val := fun hdef o => ∃ h : p?.defined, (L.sem (p?.val h) q).val (hdef h) o
  }

/-- Lifting 2: Dependent demonic / total lifting (⊤-on-rejection). -/
def Language.semPartial (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => Partial.bind p? (fun p => L.sem p q)
```

These liftings satisfy the following zero-axiom laws:

- **Specialization to the propositional triad:** On a constant partial program
  `{ defined := P, val := fun _ => p }`, `L.semIfCompiled` equals
  `Behavior.when P (L.sem p)` by `rfl` (`semIfCompiled_const_eq_when`), and
  `L.semPartial` is mutually refining (`≈`) with
  `Behavior.require P (L.sem p)` (`semPartial_const_equiv_require`).
- **Universal property of `semIfCompiled` (`semIfCompiled_le_iff`):**
  $$\mathsf{L.semIfCompiled}\; p? \le \mathsf{spec} \iff \forall h : p?.\mathsf{defined},\; \mathsf{L.sem}\; (p?.\mathsf{val}\; h) \le \mathsf{spec}$$
  When `p? = Partial.ub`, `L.semIfCompiled Partial.ub ≤ (fun _ => Partial.bot)`
  (`semIfCompiled_ub_le_bot`). When `p? = Partial.pure p`,
  `L.semIfCompiled (Partial.pure p)` is refinement-equivalent to `L.sem p`
  (`semIfCompiled_pure_equiv`).
- **Universal property of `semPartial` (`semPartial_le_iff`):**
  $$\mathsf{L.semPartial}\; p? \le \mathsf{spec} \iff (\forall q,\; (\mathsf{spec}\; q).\mathsf{defined} \to p?.\mathsf{defined}) \wedge (\forall h : p?.\mathsf{defined},\; \mathsf{L.sem}\; (p?.\mathsf{val}\; h) \le \mathsf{spec})$$
  In particular, if `(spec q₀).defined` holds at even one query `q₀`,
  `L.semPartial p? ≤ spec` forces `p?.defined` (`semPartial_le_imp_defined`)
  and is equivalent to `∃ h : p?.defined, L.sem (p?.val h) ≤ spec`
  (`semPartial_le_iff_exists_of_defined` / `semPartial_le_iff_of_defined`).
- **Duality ordering:** `L.semIfCompiled p? ≤ L.semPartial p?` always holds
  (`semIfCompiled_le_semPartial`), and when `h : p?.defined` holds, they
  mutually refine each other (`semPartial_le_semIfCompiled_of_defined`).

**Why `Compiler.SoundOn` must use the `semIfCompiled` polarity rather than
`semPartial`:** In Anneal, `C.SoundOn s` is the semantic meaning of the trusted
compiler assumption `TCBItem.rustcLowering fnName s`
(`Trusted/MirSemantics.lean` line 829). If `C.SoundOn s` were defined using
`semPartial` (`L_tgt.semPartial (C.compile s) ≤ C.π (L_src.sem s)`), then by
`semPartial_le_imp_defined`, for every source program `s` whose mapped behavior
`C.π (L_src.sem s)` is defined at some query `q` (which includes step `0` of
any small-step operational machine), `TCBItem.rustcLowering` would assert
`(C.compile s).defined` as an **unproved TCB axiom**. For a program whose
compilation fails a PME (`¬ (C.compile s).defined`), that TCB assumption would
be `False`, allowing any theorem to be proved ex falso and violating
`PRINCIPLES.md`. Consequently, `Compiler.SoundOn` must always condition on
`h : (C.compile s).defined` (`CompilesPartial`, which is equivalent to
`L_tgt.semIfCompiled (C.compile s) ≤ C.π (L_src.sem s)` by
`compilesPartial_iff_semIfCompiled_le` and
`Compiler.soundOn_iff_semIfCompiled`).

For human comprehension in `trusted/` (`AGENTS.md`), `Trusted/Refinement.lean`
should state
`∀ h : (C.compile s).defined, Compiles L_src L_tgt C.π s ((C.compile s).val h)`
directly in first-order logic, while `Language.semIfCompiled` and
`Language.semPartial` reside in `theory/Anneal/Refinement.lean`.

---

#### 3. Verification Modes, Vacuity Canaries, Composition, and `MonoMirSem`

`Basis: source + execution + derived`

##### 3.1 Algebraic Hierarchy of the Three Verification Modes

For a partial compiler `C : Compiler L_src L_tgt`, a source program
`s : L_src.Prog`, and a specification `spec : L_src.Behavior`, there are three
candidate definitions of end-to-end verification
([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 680–804;
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
694–758):

1. **Mode 1 (`Compiler.Verified` / `VerifiedIfCompiled` — Source-Unconditional,
   Target-Conditional):**
   ```lean
   def Compiler.Verified {L_src L_tgt : Language}
       (C : Compiler L_src L_tgt) (s : L_src.Prog)
       (spec : L_src.Behavior) : Prop :=
     L_src.sem s ≤ spec ∧
     ∀ h : (C.compile s).defined,
       Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
       L_tgt.sem ((C.compile s).val h) ≤ C.π spec
   ```
   (In [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean)
   lines 694–699, the second conjunct also packages `Monotone C.π` via
   `C.SoundOn s`.)
2. **Mode 2 (`Compiler.VerifiedWhenCompiled` — Both Source and Target
   Conditional on `(C.compile s).defined`):**
   ```lean
   def Compiler.VerifiedWhenCompiled {L_src L_tgt : Language}
       (C : Compiler L_src L_tgt) (s : L_src.Prog)
       (spec : L_src.Behavior) : Prop :=
     ∀ h : (C.compile s).defined,
       L_src.sem s ≤ spec ∧
       Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
       L_tgt.sem ((C.compile s).val h) ≤ C.π spec
   ```
3. **Mode 3 (`Compiler.VerifiedTotal` — Compilation Guaranteed plus Mode 1):**
   ```lean
   def Compiler.VerifiedTotal {L_src L_tgt : Language}
       (C : Compiler L_src L_tgt) (s : L_src.Prog)
       (spec : L_src.Behavior) : Prop :=
     (C.compile s).defined ∧ C.Verified s spec
   ```

We prove the strict implication chain
$$\mathsf{VerifiedTotal}\; C\; s\; \mathsf{spec} \implies \mathsf{Verified}\; C\; s\; \mathsf{spec} \implies \mathsf{VerifiedWhenCompiled}\; C\; s\; \mathsf{spec}$$
(`VerifiedTotal.to_verified`, `Verified.to_verifiedWhenCompiled`) together with
the exact characterizations:

- `Compiler.verified_iff_src_and_verifiedWhenCompiled`:
  `C.Verified s spec ↔ L_src.sem s ≤ spec ∧ C.VerifiedWhenCompiled s spec`.
- `Compiler.verifiedTotal_iff_defined_and_verifiedWhenCompiled`:
  `C.VerifiedTotal s spec` holds iff
  `(C.compile s).defined ∧ C.VerifiedWhenCompiled s spec`
  (once `(C.compile s).defined` is known, Mode 1 and Mode 2 coincide).
- `Compiler.verified_iff_semIfCompiled` and
  `Compiler.verifiedTotal_iff_semPartial`:
  Mode 1 corresponds to `L_tgt.semIfCompiled`, whereas Mode 3 corresponds to
  `(C.compile s).defined` plus `L_tgt.semPartial` (and by
  `Compiler.verifiedTotal_of_semPartial`,
  `L_tgt.semPartial (C.compile s) ≤ C.π spec` alone witnesses
  `(C.compile s).defined` whenever `(C.π spec q₀).defined` holds at a witness
  query `q₀`).
- **Conservative extension over total compilers (`Compiler.ofTotal`):** When a
  total compiler is lifted via `Partial.pure` (`Compiler.ofTotal compile π`),
  `SoundOn` (`Compiler.ofTotal_soundOn_iff`) and all three verification modes
  (`Compiler.ofTotal_verified_iff`, `Compiler.ofTotal_verifiedWhenCompiled_iff`,
  `Compiler.ofTotal_verifiedTotal_iff`,
  [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 1352–1394) are
  logically equivalent to the baseline total-compiler definitions in
  `Trusted/Refinement.lean`.

##### 3.2 Mode 2 Vacuity Hazard vs. PME Conditioning (Discriminating Canaries)

Section 5 of [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) (lines
840–953) mechanizes two families of discriminating canaries:

- **Canary Family 1 (`CanaryLang` and `rejectingCompiler`, lines 842–888):**
  `CanaryProg.ubProg` has unconditional runtime UB
  (`CanaryLang.sem .ubProg _ = Partial.ub`), and
  `rejectingCompiler.compile .ubProg = Partial.ub` (`defined := False`):
  - `canary_mode2_vacuous_on_rejected_ub`:
    `rejectingCompiler.VerifiedWhenCompiled .ubProg CanaryLang.WellFormed` holds
    **vacuously** (`fun h => False.elim h`). If `Compiler.Verified` were
    globally replaced by Mode 2 and a bug in the compiler model or PME
    extractor ever assigned `defined = False` (or an unsatisfiable compilation
    condition) to a function with reachable runtime UB, `VerificationResult`
    would silently pass without recording the conditionality in the theorem
    statement.
  - `canary_mode1_rejects_source_ub_even_when_uncompilable`:
    `¬ rejectingCompiler.Verified .ubProg CanaryLang.WellFormed`, because Mode 1
    checks `L_src.sem s ≤ spec` outside `∀ h : (C.compile s).defined`.
  - `canary_mode3_rejects_uncompilable`:
    `¬ rejectingCompiler.VerifiedTotal .ubProg CanaryLang.WellFormed`.
- **Canary Family 2 (`PmeLang` and `pmeCompiler`, lines 894–952):**
  Program `n : Nat` models a generic Rust function `first_elem<const N: usize>`
  with `const { assert!(N > 0); }` whose runtime semantics and compilation
  definedness both require `0 < n`:
  - `canary_pme_verified_with_pme_pre`: for all `n : Nat`,
    `pmeCompiler.Verified n (PmeLang.WellFormedOn (fun _ => 0 < n))` holds in
    Mode 1.
  - `canary_pme_verifiedWhenCompiled`: for all `n : Nat`,
    `pmeCompiler.VerifiedWhenCompiled n PmeLang.WellFormed` holds in Mode 2.
  - `canary_pme_zero_not_verifiedTotal` and `canary_pme_succ_verifiedTotal`:
    at `n = 0`, `¬ pmeCompiler.VerifiedTotal 0 PmeLang.WellFormed`; at
    `n = k + 1`, `pmeCompiler.VerifiedTotal (k + 1) PmeLang.WellFormed` holds.

##### 3.3 Mode Unification (`verifiedWhenCompiled_iff_verified_given`)

Mode 1 (`Compiler.Verified`) expresses Mode 2 (`Compiler.VerifiedWhenCompiled`)
without adding a second top-level verification primitive to
`Trusted/Refinement.lean`:

- In [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
  720–727, where `Verified` and `VerifiedWhenCompiled` state the target
  conclusion against `spec` and package `C.SoundOn s`),
  `verifiedWhenCompiled_iff_verified_given` proves directly from
  `Behavior.behavior_le_given_iff`:
  ```lean
  theorem verifiedWhenCompiled_iff_verified_given {S T : Language}
      (C : Compiler S T) (s : S.Prog) (spec : S.Behavior) :
      C.VerifiedWhenCompiled s spec ↔
        (S.sem s ≤ Behavior.given (C.compile s).defined spec ∧
         C.SoundOn s ∧
         ∀ h : (C.compile s).defined,
           T.sem ((C.compile s).val h) ⊑[C.π] spec)
  ```
- In [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) (lines 817–835,
  where `C.Verified s spec'` also substitutes `spec'` into the target
  obligation `L_tgt.sem ((C.compile s).val h) ≤ C.π spec'`),
  `Compiler.verifiedWhenCompiled_iff_verified_when` proves that under
  `Monotone C.π` (using `when_equiv_of_true hdef spec`),
  $$\mathsf{C.VerifiedWhenCompiled}\; s\; \mathsf{spec} \iff \mathsf{C.Verified}\; s\; (\mathsf{Behavior.given}\; (C.\mathsf{compile}\; s).\mathsf{defined}\; \mathsf{spec})$$
  and `verificationResultWhenCompiledOn_iff` (lines 1324–1343) lifts this
  equivalence to the full `VerificationResultOn` envelope:
  ```lean
  VerificationResultWhenCompiledOn C policy assumptions prog pre specs ↔
    VerificationResultOn C policy assumptions prog
      (fun q => (C.compile prog).defined ∧ pre q)
      (specs.map (Behavior.when (C.compile prog).defined))
  ```
  (where `Behavior.when` in `support/PartialCompileAlgebra.lean` is the right-hand
  specification-gating operator `Behavior.given`).

Consequently, Mode 1 (`Compiler.Verified`) is the sole `Verified` primitive
needed in `Trusted/Refinement.lean`: ordinary functions prove
`L_src.sem prog ≤ L_src.WellFormedOn pre` unconditionally with zero vacuity
hazard, while PME-dependent functions explicitly include the admissibility
predicate in `fn.pre` (`fun q => P_pme ∧ pre q`) and `fn.specs`.

##### 3.4 Multi-Pass Composition (`Compiler.comp` and `Verified.comp`)

Sequential composition of partial compilers uses `Partial.bind`
([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 961–964;
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
656–659):

```lean
def Compiler.comp {L₁ L₂ L₃ : Language}
    (C₁ : Compiler L₁ L₂) (C₂ : Compiler L₂ L₃) : Compiler L₁ L₃ where
  compile s := Partial.bind (C₁.compile s) C₂.compile
  π b := C₂.π (C₁.π b)
```

Mechanizing multi-pass composition exposes a structural distinction around
`Monotone C₂.π` when `(C₁.compile s).defined` is false: if we are given only
the dependent family
`h₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)` and
`(C₁.compile s).defined` is `False`, `h₂` is an empty function from which an
unconditional proof of `Monotone C₂.π` cannot be extracted.
[support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) (lines 1018–1148)
mechanizes three ways to compose across stages:

1. **`Compiler.Verified.comp` (zero extra hypotheses, lines 1109–1121):**
   ```lean
   theorem Compiler.Verified.comp
       {L₁ L₂ L₃ : Language}
       {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
       {s : L₁.Prog} {spec : L₁.Behavior}
       (h_ver₁ : C₁.Verified s spec)
       (h_sound₂ : ∀ h : (C₁.compile s).defined,
         C₂.SoundOn ((C₁.compile s).val h)) :
       (C₁.comp C₂).Verified s spec
   ```
   Because `(C₁.comp C₂).Verified s spec` quantifies over
   `⟨hdef₁, hdef₂⟩ : ((C₁.comp C₂).compile s).defined`, `hdef₁` is always in
   context when proving the target obligation, so `(h_sound₂ hdef₁).1` supplies
   `Monotone C₂.π` without any external hypothesis.
2. **`Compiler.SoundOn.comp` and `Compiler.SoundOn.comp_of_defined` (lines
   1032–1054; also `SoundOn.comp` in
   [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
   677–688):** Composes `C₁.SoundOn s` and `h₂` given either `Monotone C₂.π`
   (which is a program-independent property of `C₂.π`) or
   `hdef₁ : (C₁.compile s).defined`.
3. **`Compiler.SoundOnWhenCompiled.comp` (lines 1018–1029):** Scoping
   `Monotone C.π` inside `∀ h : (C.compile s).defined` composes directly with
   zero extra hypotheses and still discharges `C.Verified s spec` via
   `Compiler.SoundOnWhenCompiled.verify` (lines 1071–1078).

Crucially, with `Compiler.SoundOn` and `Compiler.Verified` (Mode 1) generalized
to `Partial L_tgt.Prog`, every bridge theorem in `theory/Anneal/Refinement.lean`
(lines 213–271) retains its **exact theorem signature**
([support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) lines 1060–1067,
1158–1168, 1189–1198, 1243–1251):

- `Compiler.SoundOn.verify`:
  `C.SoundOn s → L_src.sem s ≤ spec → C.Verified s spec`
- `verify_through_passes`:
  `L_v.sem v ≤ spec → Abstracts L_v L_src π_v v s → Monotone π_v →`
  `C.SoundOn s → C.Verified s (π_v spec)`
- `Compiler.Verified.mono`:
  `C.Verified s spec₁ → spec₁ ≤ spec₂ → Monotone C.π → C.Verified s spec₂`
- `Compiler.Verified.with_wellFormedOn`:
  `C.Verified s spec → spec ≤ L_src.WellFormedOn pre → Monotone C.π →`
  `AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s))`

##### 3.5 Reconciling `Behavior.given` with `MonoMirSem` (`Behavior.require`)

Section 5 of
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
1214–1311) reconciles `MirLang`'s right-hand `Behavior.given` specification
gating with `MonoMirLang`'s left-hand demonic `MonoMirSem` gating:

- For a monomorphized compilation unit `u : MonoMirUnit` with PME admissibility
  predicate `u.pmeOk := u.body.CompileAdmitted`, the demonic monomorphized
  semantics is definitionally `Behavior.require`:
  ```lean
  def MonoMirSem (u : MonoMirUnit) : MirLang.Behavior :=
    Behavior.require u.pmeOk (MirSem u.body)

  theorem monoMirSem_eq_require (u : MonoMirUnit) :
      MonoMirSem u = Behavior.require u.pmeOk (MirSem u.body) := rfl
  ```
- In any small-step operational machine `M : SmallStepMachine`, `BehaviorOf M q`
  is **unconditionally defined at `q.steps = 0`** via `ReachesPrefix.zero`
  (`behaviorOf_defined_at_zero`, lines 896–902), regardless of whether `M`
  steps to `.stuck` at step `1`.
- Defining `unifiedTotalPre pre q := q.steps = 0 ∨ pre q` (lines 1246–1247)
  makes `(MirLang.SpecOn (unifiedTotalPre pre) post ⟨0, 0⟩).defined` hold
  unconditionally via `Or.inl rfl`. Applying
  `Behavior.behavior_require_le_iff_of_defined` at `q₀ := ⟨0, 0⟩` yields
  `monoMirSem_le_unifiedTotalPre_iff` (lines 1262–1292): under
  `PostZeroCompatible post` (`∀ init, post ⟨0, init⟩ .outOfFuel`),
  $$\mathsf{MonoMirSem}\; u \le \mathsf{MirLang.SpecOn}\; (\mathsf{unifiedTotalPre}\; \mathsf{pre})\; \mathsf{post} \iff u.\mathsf{pmeOk} \wedge \mathsf{MirSem}\; u.\mathsf{body} \le \mathsf{MirLang.SpecOn}\; \mathsf{pre}\; \mathsf{post}$$
- Conversely, gating the specification in `MonoMirLang` by
  `Behavior.given u.pmeOk` neutralizes the left-hand `Behavior.require u.pmeOk`,
  recovering the exact conditional obligation of `MirLang`
  (`monoMirSem_le_given_pmeOk_iff_mirSem_le_given`, lines 1299–1311):
  $$\mathsf{MonoMirSem}\; u \le \mathsf{Behavior.given}\; u.\mathsf{pmeOk}\; (\mathsf{MirLang.SpecOn}\; \mathsf{pre}\; \mathsf{post}) \iff \mathsf{MirSem}\; u.\mathsf{body} \le \mathsf{MirLang.SpecOn}\; (\mathsf{fun}\; q \Rightarrow u.\mathsf{body.CompileAdmitted} \wedge \mathsf{pre}\; q)\; \mathsf{post}$$

---

#### 4. Unified `TCBItem.rustcLowering` and the Target-Level Discharge Bridge

`Basis: source + execution + derived`

##### 4.1 Modeling `CompileAdmitted`, Partial `rustc`, and `RustcLoweringSound`

In [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
914–1075), compile-time PME admissibility and partial `rustc` lowering are
modeled as follows:

1. **CTFE admissibility (`ConstMirBody`, `ConstMirMachine`, `CtfeAdmitted`):**
   Each inline `const { ... }` block (`mir::Const::Unevaluated`) is captured as
   a `ConstMirBody` evaluated by `ConstMirMachine cb`. `CtfeAdmitted cb` holds
   when `BehaviorOf (ConstMirMachine cb)` is defined at all fuel bounds `n` and
   reaches `some ()` at some fuel `n`
   (`ctfeAdmitted_iff_evalOk : CtfeAdmitted cb ↔ cb.evalOk = true`).
2. **Function compile-time admissibility (`MirBody.CompileAdmitted`):**
   ```lean
   def MirBody.CompileAdmitted (body : MirBody) : Prop :=
     body.localLayoutOk ∧ ∀ cb, cb ∈ body.requiredConsts → CtfeAdmitted cb
   ```
3. **Partial `rustc` lowering and `RustcLoweringSound`:**
   In `Trusted/MirSemantics.lean` (line 788), `rustc` is updated from
   `MirBody → TargetArtifact` to `MirBody → Partial TargetArtifact`, and the
   meaning of `TCBItem.rustcLowering fnName body` is defined as
   `RustcLoweringSound body`:
   ```lean
   def RustcLoweringSound (body : MirBody) : Prop :=
     RustcMirCompiler.SoundOn body ∧
     ((rustc body).defined → body.CompileAdmitted)
   ```

Why conjoining `(rustc body).defined → body.CompileAdmitted` into
`RustcLoweringSound` on `TCBItem.rustcLowering` (Approach A) is superior to
baking `CompileAdmitted` into `Language` / `Compiler.SoundOn` or replacing
`MirLang.sem` with demonic `MonoMirSem` (Approach B):

- **Zero contamination of Layer 1A (`Trusted/Refinement.lean`):** `Language`
  and `Compiler.SoundOn` remain generic across arbitrary languages `S` and `T`
  (including pure proof-side languages such as `FunctionalMirLang` that have no
  PME gate).
- **Orthogonal separation of runtime semantics and compile-time gates:**
  `MirSem body` remains the pure operational semantics of `body`'s runtime
  statements, while `body.CompileAdmitted` captures `rustc`'s compile-time
  checks.
- **Automatic target-level discharge:** Source proofs can assume
  `body.CompileAdmitted` via `Behavior.given`, while target-level theorems
  eliminate `body.CompileAdmitted` whenever `(rustc body).defined` holds.

##### 4.2 Target-Level Discharge (`target_discharges_compileAdmitted`)

Suppose a function `body : MirBody` is verified at the source level
conditionally on `body.CompileAdmitted`:

```lean
h_cond : body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post
```

By `mirSem_le_specOn_compileAdmitted_iff`
([support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) lines
1084–1089), `h_cond` is constructively equivalent to refining the PME-gated
specification:

```lean
h_src : MirSem body ≤ MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post
```

From `h_cond` (or `h_src`) and `h_lowering : RustcLoweringSound body`,
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) proves two
bridge theorems:

1. **Source/Crate Envelope Bridge (`verified_compileAdmitted_of_cond` and
   `verificationResultOn_compileAdmitted_of_cond`, lines 1096–1131):** Using
   `h_lowering.1 : RustcMirCompiler.SoundOn body`, `SoundOn.verify` and
   `Verified.with_wellFormedOn` establish `VerificationResultOn` over the
   PME-gated precondition `fun q => body.CompileAdmitted ∧ pre q`—even for
   uncompiled generic templates or dead functions where `body.CompileAdmitted`
   is false.
2. **Target-Level Discharge Bridge (`target_discharges_compileAdmitted`, lines
   1150–1183, and `target_verifiedTotal_unconditional_of_compiled`, lines
   1192–1204):** Whenever `rustc` compiles `body` to a target artifact
   (`h_comp : (rustc body).defined`), the second projection
   `h_lowering.2 : (rustc body).defined → body.CompileAdmitted` fires and
   **discharges `body.CompileAdmitted`** from both the source and target
   specifications:
   ```lean
   theorem target_discharges_compileAdmitted (body : MirBody)
       (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
       (h_lowering : RustcLoweringSound body)
       (h_src :
         MirSem body ≤
           MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post)
       (h_comp : (rustc body).defined) :
       body.CompileAdmitted ∧
       MirSem body ≤ MirLang.SpecOn pre post ∧
       Compiles MirLang TargetLang RustcMirCompiler.π
         body ((rustc body).val h_comp) ∧
       TargetLang.sem ((rustc body).val h_comp) ≤
         RustcMirCompiler.π (MirLang.SpecOn pre post)
   ```
   The proof proceeds in four constructive steps (zero axioms):
   - Extract `h_adm : body.CompileAdmitted := h_lowering.2 h_comp`.
   - Rewrite `MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post` to
     `Behavior.given body.CompileAdmitted (MirLang.SpecOn pre post)` by `rfl`
     (`specOn_and_eq_given`) and apply
     `Behavior.le_of_le_given_of_true h_src h_adm` to obtain the un-gated
     source refinement `h_src_uncond : MirSem body ≤ MirLang.SpecOn pre post`.
   - Extract
     `Compiles MirLang TargetLang RustcMirCompiler.π body`
     `((rustc body).val h_comp)` from `h_lowering.1.2 h_comp`.
   - Push `h_src_uncond` through `Monotone RustcMirCompiler.π`
     (`h_lowering.1.1`) and `Preorder.le_trans` to obtain
     `TargetLang.sem ((rustc body).val h_comp) ≤`
     `RustcMirCompiler.π (MirLang.SpecOn pre post)` (and
     `RustcMirCompiler.VerifiedTotal body (MirLang.SpecOn pre post)` by
     `target_verifiedTotal_unconditional_of_compiled`).

Section 6 of
[support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
1317–1518) instantiates this bridge on a concrete generic function
`const_bounded_add<const N: usize>(x: usize) -> usize` with
`const { assert!(N < 1000); }`, caller precondition `x ≤ 500`, and
postcondition `ret < 1500`, proving:

- `constBoundedAdd_conditional_refines (N : Nat)` (for all `N : Nat`, including
  `N ≥ 1000`),
- `constBoundedAdd_target_discharged (N : Nat)` (proving that any compiled
  artifact `h_comp : (rustc (constBoundedAddBody N)).defined` satisfies
  `N < 1000` and the un-gated target specification under `x ≤ 500` alone), and
- `verify_exampleCrate (N : Nat) : CrateTheorem (exampleCrate N)`.

---

#### 5. Audit Verification Against `TrustedBoundary.lean` and `audit/src/lib.rs`

`Basis: source + execution + derived`

##### 5.1 Exact Declaration Placement Across `trusted/` and `theory/`

| Declaration | Target File in `joshlf/anneal` | Trust / Candidate Attribute |
| :--- | :--- | :--- |
| `Partial.bot`, `Partial.map`, `Partial.bind`, `Option.toPartial` | `trusted/lean/Trusted/Refinement.lean` | `@[candidate refinement]` definitions |
| `Behavior.when`, `Behavior.given`, `Behavior.require` | `trusted/lean/Trusted/Refinement.lean` | `@[candidate refinement]` definitions |
| `Compiler` (`compile : L_src.Prog → Partial L_tgt.Prog`), `Compiler.id`, `Compiler.comp`, `Compiler.SoundOn`, `Compiler.Sound`, `Compiler.Verified`, `Compiler.VerifiedWhenCompiled`, `Compiler.VerifiedTotal` | `trusted/lean/Trusted/Refinement.lean` | `@[candidate refinement]` definitions |
| `ConstId`, `ConstMirBody`, `MirBody.requiredConsts` | `trusted/lean/Trusted/MirAst.lean` | `@[candidate mir_ast]` definitions |
| `ConstMirMachine`, `CtfeAdmitted`, `MirBody.CompileAdmitted` | `trusted/lean/Trusted/MirSemantics.lean` | `@[candidate mir_semantics]` definitions |
| `rustc : MirBody → Partial TargetArtifact`, `RustcLoweringSound`, updated `TCBItem` `TrustedAssumption` instance, `CapturedFn.isPublic`, updated `CrateTheorem` | `trusted/lean/Trusted/MirSemantics.lean` | `@[candidate rustc_capture]` / `@[candidate mir_semantics]` definitions |
| `Language.semIfCompiled`, `Language.semPartial`, and all algebraic, Galois-connection, composition, and target-discharge theorems | `theory/Anneal/Refinement.lean` (and `theory/Anneal/MirLemmas.lean`) | Pure definitions and kernel-checked theorems in `theory/` |

##### 5.2 Check-by-Check Audit Verification

1. **Module Import DAG Containment (`validateGraph` in
   `trusted/audit/TrustedBoundary.lean` lines 169–205; `auditVerifyPreflight`
   lines 869–877; `check_module_imports` in `trusted/audit/src/lib.rs` lines
   1384–1404, 1553–1585):**
   - `Trusted/Refinement.lean` imports only `foundation` (`prelude` +
     `Init.NotationExtra`).
   - `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` import only
     `foundation ++ trusted`.
   - `.anneal/Mir.lean` (`Mir`) imports only `Trusted.MirSemantics`
     (`foundation ++ trusted`). Because `MirBody.CompileAdmitted`,
     `ConstMirBody`, `CapturedFn`, `MirLang.SpecOn`, and `Behavior.given` all
     live in `Trusted.*`, `Mir.lean` requires zero imports from `Anneal.*`.
   - `.anneal/Proof.lean` (`Proof`) imports only
     `foundation ++ trusted ++ theory ++ {Mir}`.
2. **Zero Theorems in `trusted/` (`AGENTS.md` and `verifyAndCollectLocals` in
   `TrustedBoundary.lean` line 900):** Every declaration placed in
   `Trusted/Refinement.lean`, `Trusted/MirAst.lean`, and
   `Trusted/MirSemantics.lean` is a `def`, `abbrev`, `structure`, `inductive`,
   `opaque`, or `instance`; all `theorem` declarations reside in
   `theory/Anneal/*` or `.anneal/Proof.lean`.
3. **`checkMirCrate` and `checkVerifyCrate` (`TrustedBoundary.lean` lines
   945–959):** Updating `CapturedFn`, `MirBody`, and `CrateTheorem` inside
   `Trusted.MirSemantics` preserves the top-level constant names
   `Trusted.Crate` and `Trusted.CrateTheorem`. Therefore `Mir.crate` retains
   exact kernel type `Expr.const `Trusted.Crate []` and `Proof.verify_crate`
   retains exact kernel type
   `Expr.app (Expr.const `Trusted.CrateTheorem []) (Expr.const `Mir.crate [])`.
4. **Statement-Origin Separation:** The kernel type (`ci.type`) of
   `Proof.verify_crate` contains only two root constants:
   `Trusted.CrateTheorem` (origin `Trusted.MirSemantics ∈ trusted`) and
   `Mir.crate` (origin `Mir`). Because `Trusted.MirSemantics` and `Mir` import
   only `foundation ++ trusted` (enforced by `validateModuleImports` in
   `auditVerifyPreflight` at `TrustedBoundary.lean` line 875), every constant
   reachable from `Trusted.CrateTheorem` or `Mir.crate`—including every field of
   every `CapturedFn` in `Mir.crate.functions` and every `TCBItem` in
   `Mir.crate.tcb`—necessarily satisfies
   `origin env c ∈ foundation ∪ trusted ∪ {Mir}`. Untrusted definitions and
   lemmas in `theory/Anneal/*` and `.anneal/Proof.lean` appear exclusively in
   the proof term (`ci.value?`) of `Proof.verify_crate`.
5. **Axiom Lock and `native_decide` Prohibition (`inspectSyntax` and `closure`
   in `TrustedBoundary.lean` lines 318–340, 562–578, 933, 959):** Neither
   preserved Lean mechanization uses `native_decide`, `decide +native`,
   `Lean.ofReduceBool`, `Lean.trustCompiler`, `Classical.choice`, or `sorryAx`.
   The `#print axioms` audit at the end of
   [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (lines
   1524–1535) confirms:
   - **Zero axioms (`does not depend on any axioms`):**
     `Behavior.behavior_when_given_adjunction`,
     `Behavior.behavior_require_le_iff`, `Language.semIfCompiled_le_iff`,
     `Language.semPartial_le_iff`, `verify_through_passes`,
     `target_discharges_compileAdmitted`, and
     `target_verifiedTotal_unconditional_of_compiled`.
   - **`[propext]` only (permitted by `foundation-lock.json`):**
     `Behavior.behavior_require_le_iff_of_defined`,
     `Compiler.verifiedWhenCompiled_iff_verified_given`,
     `monoMirSem_le_unifiedTotalPre_iff`, `constBoundedAdd_target_discharged`,
     and `verify_exampleCrate`.
6. **Candidate-Feature Non-Contamination (`checkTrustedNonContamination` and
   `validCandidateFeatures` in `TrustedBoundary.lean` lines 65–72, 656–808):**
   All proposed `Trusted.*` declarations map to existing candidate feature names
   in `validCandidateFeatures` (`refinement`, `mir_ast`, `mir_semantics`,
   `rustc_capture`), requiring zero edits to `TrustedBoundary.lean` or
   `trusted/audit/src/lib.rs`.

## Boundaries

### Part I — Behavior Codecs, Progress Refinement, Eventual Semantics, and Optimizer Anti-Degeneracy

- **Non-deterministic target machines with empty outcome sets (`known not to
  apply` without totality):** Under demonic-choice refinement
  (`L_tgt.sem t ≤ π (L_src.sem s)`), an empty target outcome predicate
  (`val := fun _ => False`) refines any defined source behavior. In
  `BehaviorOf M p`, empty outcome sets arise only at invalid initial states
  (`¬ M.initState p q.init`); from any valid initial state, a total machine has
  at least one reachable prefix outcome at every step budget `n` (an explicit
  hypothesis in `BehaviorCodec.compiles_bidirectional_outcome`,
  [MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) L2832).
- **Silent vs. observable transitions in `StepResult` (`known not to apply` to
  non-Unit I/O traces without trace projection):** Because
  `StepResult.step obs next` always appends `obs` to `trace : List Obs` and both
  `MirMachine` and `X86Machine` instantiate `Obs := Unit`, `out.trace` is a
  unary step counter (`List.replicate k ()`). Any variable-step lowering or
  instruction-deleting optimization must either treat `Unit` ticks as silent (as
  in `SilentEventualBehaviorOf` and `π_opt`) or emit `.choice` for internal
  micro-steps while reserving `Obs` for external I/O observations.
- **Infinite reactive I/O streams under `EventualOut.diverges`
  (`not examined`):** `EventualOut Obs Val` records the finite observation trace
  `trace : List Obs` upon termination (`.terminated trace term`) and classifies
  non-terminating executions via `.diverges`
  (`∀ n, ∃ tr, ReachesPrefix M p n init tr .incomplete`). Distinguishing two
  intentionally non-terminating reactive loops by their infinite I/O trace
  prefixes was not examined because Anneal specifies Rust functions at
  call/return boundaries.
- **Unanchored `π_opt` and termination preservation (`known not to apply`
  without `EventualBehaviorOf` or `TerminatesInMinSteps`):** Because `π_opt`
  existentially quantifies `∃ steps_src` over step-indexed `BehaviorOf` where
  every program has an `.incomplete`/`.running` prefix at `steps_src = 0`,
  `π_opt` preserves safety (`WellFormedOn`) and partial-correctness
  postconditions (`EnsuresRetLibInv`) but relies on `TerminatesInMinSteps` in
  `CertifiedOptimizationPass` (or `EventualBehaviorOf` in Architecture B, where
  `.diverges` is disjoint from `.terminated`) to prevent an optimizer from
  replacing a terminating block with an infinite loop.

### Part II — Partial Compilation and Behavioral Conditioning Refinement Algebra

- **Standalone mechanization vs. in-tree migration (`not examined` as an applied
  worktree commit):** [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean)
  and
  [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) are
  self-contained Lean 4.34.1 modules (`prelude` + `import Init.NotationExtra`)
  that replicate the exact Layer 1A definitions of `Trusted/Refinement.lean`
  and `theory/Anneal/Refinement.lean` and verify the proposed extensions. This
  report does not modify the files inside the `joshlf/anneal` worktree itself.
- **Concrete `rustc` backend semantics (`known not to apply`):** Exactly as in
  `Trusted/MirSemantics.lean` (lines 788–794), `rustc`, `TargetArtifact`,
  `TargetSem`, and `π_c` remain `opaque` interfaces whose per-function
  soundness and PME gate (`RustcLoweringSound body`) are tracked explicitly in
  the crate's TCB audit log via `TCBItem.rustcLowering fnName body` rather than
  proved against a mechanized x86_64/AArch64/LLVM backend.
- **Demonic `semPartial` in `Compiler.SoundOn` (`known not to apply`):** Using
  `Language.semPartial` (`Partial.bind`) to define `Compiler.SoundOn` is sound
  only for total compilers; for partial compilers with non-empty query domains,
  it asserts `(C.compile s).defined` as an unproved TCB axiom and is
  unsound whenever compilation of `s` can fail.
- **Unguarded Mode 2 (`VerifiedWhenCompiled`) as the sole verification envelope
  (`known not to apply`):** Replacing Mode 1 (`Compiler.Verified`) globally by
  unguarded Mode 2 is vulnerable to silent vacuity whenever
  `(C.compile s).defined` is `False` (`canary_mode2_vacuous_on_rejected_ub`).
  Conditioning must instead be stated explicitly in `fn.pre` and `fn.specs` via
  `Behavior.given` / `L.SpecOn (fun q => P ∧ pre q) post`.

## Evidence

### Part I — Behavior Codecs, Progress Refinement, Eventual Semantics, and Optimizer Anti-Degeneracy

#### Preserved Mechanized Lean 4 Support Artifacts

All three standalone Lean 4 modules in `support/` were verified with Lean 4
`v4.34.1` (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) on `2026-10-31`
with exit code `0`, zero warnings, zero `sorryAx`, zero `Lean.ofReduceBool`, and
zero `Classical.choice`:

1. **[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean)**
   - **Lines:** `2982`
   - **SHA-256:**
     `6d9a6f0a68163d8751a4623f3b38cf084eaa13ee233bdc14096257625372c846`
   - **Key mechanized declarations and theorems (all 30 `#print axioms` checks
     report `does not depend on any axioms`):**
     - Class (a)–(d) counterexamples: `counterexample_class_a_masks_target_ub`
       (L685), `counterexample_class_b_erases_postconditions` (L735),
       `counterexample_class_b_allows_stuck_when_defined` (L777),
       `behaviorOf_steps_zero_defined` (L805),
       `counterexample_class_c_stepZero_diverges_and_masks_ub` (L830),
       `counterexample_class_c_boundedFuel_masks_late_ub_and_divergence` (L902),
       `counterexample_class_d_erases_observations_and_values` (L1097).
     - Pipeline anchoring and Class (c) step-independence blindness:
       `verify_through_passes_unanchored_vulnerable` (L1680),
       `verify_through_passes_anchored` (L1699),
       `target_anchor_rejects_degenerate_classes` (L1722),
       `stepIndependent_target_anchor_blind_to_class_c` (L1769).
     - `ExecSimCoupling` and `AdmissibleExecCoupling`: `ExecSimCoupling`
       (L1341), `AdmissibleExecCoupling` (L1402),
       `admissible_rules_out_class_a_target_ub_and_stuck` (L1482),
       `admissible_rules_out_class_c_late_ub_and_divergence` (L1560),
       `admissible_rules_out_class_d_trace_and_val_erasure` (L1619),
       `AdmissibleExecCoupling.id` (L1802), `AdmissibleExecCoupling.comp`
       (L1867), `compileMirToX86_compiles` (L2350),
       `not_compiles_floor_only_failNow` (L2409),
       `not_compiles_ceil_only_incAndRet` (L2430),
       `endToEnd_func_mir_x86_verified` (L2667).
     - Lockstep `BehaviorCodec`: `BehaviorCodec` (L2719),
       `BehaviorCodec.decodeQuery_surjective` (L2729),
       `BehaviorCodec.decodeOut_injective` (L2736),
       `BehaviorCodec.id_toMorphism` (L2802), `BehaviorCodec.comp_toMorphism`
       (L2821), `BehaviorCodec.compiles_bidirectional_outcome` (L2832),
       `SmallStepCodec.admissible_toExecSimCoupling` (L2927).

2. **[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean)**
   - **Lines:** `1837`
   - **SHA-256:**
     `bcdb2643cd16b6e22f202f95b757aa7b4dfd7236f7978b22b451297dfd23bc83`
   - **Key mechanized declarations and theorems (zero `Classical.choice`, zero
     `sorryAx`):**
     - Variable-step impossibility on step-indexed `BehaviorCodec`:
       `s_var_vs_t_var_step_mismatch` (L584), `lockstep_codec_fails_on_s_var`
       (L638), `no_state_independent_step_map_for_variable_lowering` (L676).
     - Architecture A (`DilationCodec`): `DilationCodec` (L767),
       `DilationCodec.monotone_toMorphism` (L803),
       `DilationCodec.comp_toMorphism_le` (L860),
       `dilationCodec_rejects_loopCodegen` (L932),
       `dilationCodec_verifies_s_var` (L970).
     - Architecture B (`EventualBehaviorOf`): `exists_nat_no_choice_canary`
       (L1050), `EventualOut` (L1059), `EventualBehaviorOf` (L1066),
       `eventual_wellFormed_iff_prefix_wellFormed` (L1098),
       `eventual_rejects_loopCodegen` (L1164), `eventual_verifies_s_var`
       (L1196), `eventual_verifies_s_fast` (L1247).
     - Non-surjectivity obstruction and `PartialBehaviorCodec`:
       `no_total_section_for_bool_in_uint8` (L1311),
       `no_total_section_for_bool_in_nat` (L1349), `PartialBehaviorCodec`
       (L1384), `PartialBehaviorCodec.encodeOut_injective` (L1421),
       `PartialBehaviorCodec.decodeOut_injective_on_some` (L1433),
       `PartialBehaviorCodec.invalid_target_out_rejected` (L1447),
       `PartialBehaviorCodec.compiles_rejects_invalid_target_out` (L1460),
       `PartialBehaviorCodec.monotone_toMorphism` (L1474),
       `PartialBehaviorCodec.comp_toMorphism_iff` (L1556),
       `PartialBehaviorCodec.id_toMorphism` (L1583),
       `PartialBehaviorCodec.comp_toMorphism` (L1596),
       `valid_bool_negation_compiles` (L1773),
       `corrupt_bool_bitpattern_2_rejected` (L1793).

3. **[AntiDegeneracyAndCallbackFraming.lean](support/AntiDegeneracyAndCallbackFraming.lean)**
   - **Lines:** `3956`
   - **SHA-256:**
     `3b8050a5d531ad98097cfe440a3a40bd02a25afc32ea25680244264d42e7c41f`
   - **Key mechanized declarations and theorems for certifying pass
     anti-degeneracy (Section 3, lines 708–1565):**
     - `trap1_alwaysFalse_compiles` (L753), `trap1_alwaysFalse_never_accepts`
       (L760), `trap2_id_compiles` (L777), `peephole_noop_on_corpus` (L867),
       `compiles_id_forbids_instruction_deletion` (L916).
     - `π_opt` (L991), `monotone_π_opt` (L1000),
       `π_opt_preserves_wellFormedOn` (L1015),
       `π_opt_preserves_ensuresRetLibInv` (L1025),
       `CertifiedOptimizationPass` (L1101), `trap1_rejected_by_contract`
       (L1131), `trap2_id_rejected_by_contract` (L1142),
       `peephole_on_newUnchecked_rejected` (L1154), `coalesceAndFoldBody`
       (L1186), `genuineCoalescePass_certified` (L1540).
     (Section 4 of this file, lines 1569–3955, additionally contains the shared
     callback re-entrancy and `StepResultExt.externalCall` mechanization.)

#### Upstream Repository Source Coordinates

- `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`:
  - `trusted/lean/Trusted/Refinement.lean` (lines 48–461)
  - `trusted/lean/Trusted/StepResult.lean` (lines 32–198)
  - `trusted/lean/Trusted/MirSemantics.lean` (lines 590–867)
  - `theory/Anneal/Refinement.lean` (lines 1–288)
- `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`:
  - `trusted/lean/Trusted/Refinement.lean` (lines 155–245)
  - `trusted/lean/Trusted/StepResult.lean` (lines 49–215)
  - `trusted/lean/Trusted/X86Semantics.lean` (lines 650–896)
  - `theory/Anneal/Compiler/NaiveCodegen.lean` (lines 38–153, 264–299, 810–870)
  - `theory/Anneal/Compiler/Peephole.lean` (lines 45–205)
  - `theory/Anneal/MirLemmas.lean` (lines 380–755)
  - `trusted/rustc-capture/src/lib.rs` (lines 1166–1340)

### Part II — Partial Compilation and Behavioral Conditioning Refinement Algebra

- **Primary repository sources (`joshlf/anneal` at commit
  `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)`):**
  - `trusted/lean/Trusted/Refinement.lean`: `Preorder` (lines 258–284),
    `Partial`, `Partial.pure`, `Partial.ub`, `Partial.map`,
    `instPreorderPartial` (lines 292–334), `Monotone`, `Behavior`, `Language`,
    `Language.SpecOn`, `Language.Spec`, `Language.WellFormedOn`,
    `Language.WellFormed` (lines 340–418), `Compiles`, `Abstracts`, `Compiler`,
    `Compiler.SoundOn`, `Compiler.Verified` (lines 427–473),
    `TrustedAssumption`, `TrustPolicy`, `AllHold`, `VerificationResultOn`,
    `VerificationResult` (lines 477–530).
  - `theory/Anneal/Refinement.lean`: `monotone_id`, `monotone_comp`,
    `Partial.monotone_map`, `ub_top`, `ub_le_iff`, `pure_le_pure_iff`,
    `not_ub_le_pure` (lines 51–100), `le_specOn_iff`, `le_wellFormedOn_iff`,
    `le_wellFormed_iff`, `specOn_le_wellFormedOn` (lines 104–164),
    `pass_trans`, `Compiles.comp`, `Abstracts.comp`, `Compiler.SoundOn.verify`,
    `verify_through_passes`, `Compiler.Verified.mono`,
    `Compiler.Verified.with_wellFormedOn` (lines 171–271).
  - `trusted/lean/Trusted/MirAst.lean` (lines 1–381) and
    `trusted/lean/Trusted/MirSemantics.lean`: `TargetArtifact`, `rustc`,
    `TargetSem`, `TargetLang`, `π_c`, `RustcCompiler`, `TCBItem`,
    `instTrustedAssumptionTCBItem`, `defaultTrustPolicy`, `CapturedFn`,
    `Crate`, `CrateTheorem` (lines 779–872).
  - `trusted/audit/TrustedBoundary.lean`: `validCandidateFeatures` (lines
    65–72), `validateGraph` (lines 169–205), `inspectSyntax` (lines 318–340),
    `closure` (lines 562–578), `checkTrustedNonContamination` (lines 656–808),
    `auditVerifyPreflight` (lines 869–877), `auditFull` (lines 892–938),
    `auditVerify`, `checkMirCrate`, `checkVerifyCrate` (lines 943–965).
  - `trusted/audit/src/lib.rs`: `run_setup_audit` and `trusted-roots.txt`
    validation (lines 973–984), `check_module_imports` (lines 1384–1404),
    `run_verify_audit` (lines 1553–1585).
- **Preserved mechanized Lean 4.34.1 support artifacts (observed 2026-10-30):**
  - [support/PartialCompileAlgebra.lean](support/PartialCompileAlgebra.lean) (1,438 lines;
    SHA-256:
    `fdd0c5a26c5c1bb85b80df84f72d617079f32947115a6496572bfdbe7445e27e`).
  - [support/UnifiedPmeConditionalSystem.lean](support/UnifiedPmeConditionalSystem.lean) (1,537
    lines; SHA-256:
    `e388b24a4b822408f29dd66987b884c3bff53778a108fa56ff4e753391f74763`).
- **Execution environment and verification commands (observed 2026-10-30):**
  Verified on Linux (`x86_64`) with Lean `v4.34.1`
  (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) using:
  ```console
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
    support/PartialCompileAlgebra.lean
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
    support/UnifiedPmeConditionalSystem.lean
  ```
  Both commands exited with status `0`, zero warnings, zero `sorryAx`, and zero
  `Lean.ofReduceBool`.

## Revalidation

### Part I — Behavior Codecs, Progress Refinement, Eventual Semantics, and Optimizer Anti-Degeneracy

Re-run the preserved Lean 4 checks and review this report's conclusions
whenever:

1. `trusted/lean/Trusted/Refinement.lean` modifies `Partial`, `BehaviorCodec`,
   `Compiles`, `Abstracts`, `Compiler`, `Compiler.SoundOn`, or
   `Compiler.Verified`.
2. `trusted/lean/Trusted/StepResult.lean` modifies `StepResult`,
   `PrefixOutcome`, `ExecQuery`, `ReachesPrefix`, or `BehaviorOf` (or adopts
   `EventualBehaviorOf`).
3. `theory/Anneal/Compiler/NaiveCodegen.lean` or
   `theory/Anneal/Compiler/Peephole.lean` expands `compileStmt` beyond 1-to-1
   instruction selection, lowers typed `X86Val` values into raw machine words,
   or wires an optimization pass into `rustc-capture`.

Deterministic kernel revalidation command from the package root:

```bash
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/MorphismAdmissibility.lean && \
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/BehaviorCodecExpressiveness.lean && \
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/AntiDegeneracyAndCallbackFraming.lean
```

### Part II — Partial Compilation and Behavioral Conditioning Refinement Algebra

To revalidate the algebraic, bridge, and axiom-audit claims of this report
against Lean `v4.34.1` or a newer Lean toolchain, run the kernel typechecker
with asynchronous elaboration and kernel-skipping disabled on both preserved
files inside this report directory:

```console
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/anneal-partial-compile-and-conditioning-refinement-algebra-2026/support/PartialCompileAlgebra.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/anneal-partial-compile-and-conditioning-refinement-algebra-2026/support/UnifiedPmeConditionalSystem.lean
```

Confirm that:

1. `support/PartialCompileAlgebra.lean` exits with status `0` and produces no output.
2. `support/UnifiedPmeConditionalSystem.lean` exits with status `0` and its
   `#print axioms` block prints `does not depend on any axioms` for
   `behavior_when_given_adjunction`, `behavior_require_le_iff`,
   `semIfCompiled_le_iff`, `semPartial_le_iff`, `verify_through_passes`,
   `target_discharges_compileAdmitted`, and
   `target_verifiedTotal_unconditional_of_compiled`, and
   `depends on axioms: [propext]` for the remaining five equivalence-rewriting
   theorems.
3. If `Trusted/Refinement.lean`, `theory/Anneal/Refinement.lean`, or
   `trusted/audit/TrustedBoundary.lean` changes in `joshlf/anneal`, diff those
   files against `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)` and re-run
   `cargo anneal --setup` and `cargo anneal --verify` to confirm that import
   DAG containment, `checkMirCrate`, `checkVerifyCrate`, and
   `foundation-lock.json` axiom checks continue to hold.

*Authored by an AI agent acting on joshlf's behalf.*
