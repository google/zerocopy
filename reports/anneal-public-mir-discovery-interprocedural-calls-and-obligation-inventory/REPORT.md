# Public MIR Discovery, Conditional Interprocedural Verification, Exhaustive Obligation Inventory, and Single-Source Codegen in Anneal

## Summary

### Part I — Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Call Verification

Moving Anneal from single-function unconditional verification (`pre := fun _ =>
True`) to crate-level verification of Rust libraries and binaries with private
helpers, conditional calling preconditions, and post-monomorphization
compile-time checks requires solving three coupled problems across
`trusted/rustc-capture`, `trusted/lean/`, and `theory/`:

1. **Public MIR Function Discovery in `rustc` (`58cf8f9c35`):**
   Textual MIR (`--emit=mir`, `-Z unpretty=mir`) and HIR (`-Z unpretty=hir`)
   outputs omit item visibility because `write_mir_sig` unconditionally prints
   `"fn "` and HIR stores visibilities out-of-band in
   `ResolverOutputs.visibilities`. An empirical 7-category `rustc_driver` probe
   ([`support/vis_probe/driver.rs`](support/vis_probe/driver.rs)) shows that no single `TyCtxt`
   query defines a crate's external entry surface: `tcx.local_visibility` has
   false positives on `pub fn` items inside private modules or private inherent
   `impl` blocks; `tcx.collect_and_partition_mono_items(())` omits
   uninstantiated generic `pub fn` items; `tcx.reachable_set(())` marks private
   helpers called by generic or `#[inline]` public functions as reachable in
   libraries and is nearly empty in binaries; and
   `tcx.effective_visibilities(())` has both an upstream `FIXME` false positive
   at `Level::ReachableThroughImplTrait` (marking all `OpaqueTy` hidden types in
   the crate as public even when their parent function is private) and a false
   negative on `<DynPrivStruct as PubTrait>` methods exposed via `&'static dyn
   PubTrait` coercion. Combining `tcx.mir_keys(())` with a 5-rule predicate
   `is_external_entry_fn(tcx, def_id)` resolves all seven categories and stamps
   an immutable `isPublic : Bool` field onto each `Trusted.CapturedFn` in
   `Mir.crate`.

2. **Three-Level Calling-Condition Taxonomy and Conditional `SpecOn`:**
   In Anneal's `Partial` refinement order (`p ≤ q` iff `∀ hq : q.defined, ∃ hp :
   p.defined, p.val hp ≤ q.val hq`), unconditional `MirLang.Spec post` sets
   `defined := True` at every query `q`. Consequently, any function `b` that can
   fail (`¬ (b q).defined`) on an input outside its precondition cannot refine
   `MirLang.Spec post` for *any* `post` (`not_le_spec_of_not_defined`,
   `addBody_not_le_spec` in
   [`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean)).
   Calling conditions partition cleanly into three orthogonal levels:
   - **Level 1 (ABI, type, memory, and aliasing validity):** Enforced in
     `MirMachine.initState` (`initMirState`), where queries outside
     `initMirState` satisfy `defined = True` and `val = False` and vacuously
     refine any specification (`behaviorOf_outside_initState_vacuous`).
   - **Level 2 (Safety and no-failure preconditions `pre`):** Placed in
     `.defined` via `MirLang.SpecOn pre post` and `MirLang.WellFormedOn pre`.
     Generalizing `FunctionalTranslation` with `funcSem_le_specOn` and
     `π_func_specOn_le` requires zero changes to `π_func` or `evalSym_sound`
     because `.fail` maps under `π_func` to `{ defined := False }` (the top
     element `⊤` of `Partial`).
   - **Level 3 (Functional domain assumptions `req` on safe functions):** Placed
     as an implicational guard `req q → post q out` inside `.val` of
     `MirLang.SpecOn pre`, preserving `spec ≤ MirLang.WellFormedOn pre`
     (`specOn_functional_req_le_wellFormedOn`).

3. **Call-Stack `Terminator.call`, Transitive `CompileAdmitted`, and Dual-Mode
   Interprocedural Symbolic Evaluation:**
   Replacing the skeleton's hardcoded two-callee `Terminator.callPure2` with a
   call-stack `Terminator.call dst callee args target` over `CrateEnv` and
   `MirState.frames : List CallFrame` in
   [`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean)
   eliminates both `PureCallee2` and `CalleeSummaryVerified` from `trusted/`
   while preserving `TotalStep`, `InhabitedDemonic`, and
   `mirMachine_non_vacuity_at_every_depth`. Pairing runtime call-stack semantics
   with transitive `CompileAdmitted` over `requiredConsts` and `mentionedItems`
   catches post-monomorphization CTFE failures even inside dead runtime branches
   (`if false { const_bounded_add::<2000>(x) }`,
   `deadBranchBadCaller_not_compileAdmitted`). In `theory/`, a unified
   spine-preserving evaluator `evalSymState` (`Option (Bool × SymVal)`) proved
   sound via a frame-stack continuation invariant `ReturnCont`
   (`evalSymState_sound`) supports both **Mode A** (zero-annotation symbolic
   call inlining via `TransPlan.callInline`) and **Mode B** (modular verified
   callee summaries via `TransPlan.callSummary`), reducing guarded and
   conditional callers by Lean kernel `rfl` to identical symbolic terms
   (`evalSymState_doubleGuarded_modeA_eq_modeB`).

### Part II — Exhaustive rustc Obligation Inventory and Single-Source x86-64 Artifact Binding

Sound whole-crate verification in Anneal requires two compiler-boundary
invariants:

1. **Exhaustive typed obligation inventory:** `anneal-rustc-capture` must
   discover 100% of soundness-bearing crate items and metadata from `rustc`'s
   typed query graph (`TyCtxt`) so that no verification obligation in
   `Mir.crate : Trusted.Crate` can be omitted or spoofed by surface syntax.
2. **Single-source artifact binding:** When Anneal lowers MIR to x86-64
   assembly, the assembly file `.anneal/Prog.s` assembled into the binary must
   be mathematically bound to the exact `X86Body` abstract syntax trees
   verified by `Proof.verify_crate` inside the Lean 4 kernel.

Direct source inspection and executable probes across Anneal's MIR semantic
verification baseline (`5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`) and
MIR-to-x86-64 codegen pipeline (`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`)
establish four core results:

1. **Textual source and `--emit=mir` scraping omits and spoofs crate
   obligations:** `capture_crate_with_options` reads only `src/lib.rs`, scans
   raw source lines via `parse_source_metadata`, and parses human-facing
   `--emit=mir` text via `parse_emitted_mir_with_metadata`. This pipeline
   hardcodes a single struct name (`NonZeroUsize`), allows comments or string
   literals to spoof field privacy and `pub unsafe fn` preconditions, never
   emits `unsafeImpls` (`Mir.crate.unsafeImpls` is unconditionally `[]`),
   collapses all constant bodies to a single hardcoded identifier
   (`pme_assert_const`), and omits submodule files, `#[unsafe]` fields,
   `#[non_exhaustive]` ADTs, inherited trait default methods,
   compiler-synthesized drop glue (`ShimKind::DropGlue`), and dead-branch
   `mentioned_items`.
2. **An in-process `rustc_driver` `TyCtxt` inventory closes all five obligation
   categories without text parsing:** A standalone `rustc_driver` probe
   (`support/obligation_inventory_probe/`) executed against `rustc 1.99.1`
   (`58cf8f9c35b355199727627d07ae34a4e2846d67`) demonstrates the exact `TyCtxt`
   queries required to enumerate every trait `impl` header and polarity, ADT
   field visibility/safety and `#[non_exhaustive]` flag, inherited trait
   default method instance, explicit destructor and `ShimKind::DropGlue` body,
   and `Runtime(PostCleanup)` MIR body across `mir_for_ctfe`,
   `mir_drops_elaborated_and_const_checked`, `required_consts`, and
   `mentioned_items`.
3. **Dual Rust emitters in the MIR-to-x86-64 pipeline leave `.anneal/Prog.s`
   unbound to the Lean kernel and diverge on four constructs:** In
   `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`, `anneal-rustc-capture` lowers
   MIR to x86-64 in Rust and runs two independent printers:
   `render_mir_lean_with_metadata` (writing `Trusted.X86Body` terms to
   `.anneal/Mir.lean`) and `render_x86_assembly` (writing
   `.intel_syntax noprefix` text to `.anneal/Prog.s`). Neither `anneal-audit`
   nor `TrustedBoundary.lean` ever reads or hashes `.anneal/Prog.s`. Four
   semantic discrepancies already exist between `Mir.lean`
   (`X86Semantics.lean`) and `Prog.s` (`render_x86_assembly`), including
   `CapturedTerminator::Panic` emitting a safe unwind terminator (`abortPanic`)
   in `Mir.lean` while emitting `ud2` (hardware `SIGILL` undefined behavior) in
   `Prog.s`.
4. **In-Lean deterministic `.s` serialization with `.olean` environment binding
   eliminates the shadow-artifact gap:** A mechanized Lean 4 (`v4.34.1`) and
   x86-64 prototype (`support/artifact_binding_probe/`) demonstrates a
   single-source pipeline where `Mir.crate` contains only `MirBody`,
   `Prog.x86Crate` is computed inside Lean via `compileStage0` and
   `optimizePeephole`, `Trusted.emitX86CrateAsm` is the sole assembly printer,
   `Trusted.CrateTheorem` checks `Trusted.emitX86CrateAsm xc = asmText` by
   kernel `rfl`, and `AuditMain.lean` verifies that `Prog.asmText` in the
   replayed `.olean` environment matches `Prog.s` on disk byte-for-byte.

## Applicability

### Part I — Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Call Verification

The findings in this report apply to the combination of three pinned subjects:

- **Anneal verification framework (`joshlf/anneal` at
  `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with PME/interprocedural prototype definitions inlined above and preserved in `support/`)`):** Specifically the behavioral
  refinement algebra (`trusted/lean/Trusted/Refinement.lean`), small-step MIR
  operational semantics (`trusted/lean/Trusted/MirSemantics.lean`), `.olean`
  boundary auditor (`trusted/audit/TrustedBoundary.lean`), `rustc` MIR capture
  driver (`trusted/rustc-capture/`), and pure functional translation layer
  (`theory/Anneal/FunctionalTranslation.lean`).
- **Rust compiler (`rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67`):** Specifically the query
  implementations in `rustc_middle` (`hir::ModuleItems`, `hir::map`,
  `middle::privacy`, `mir::pretty`, `mir::syntax`), `rustc_mir_transform`
  (`mir_keys`), `rustc_resolve` (`effective_visibilities`), `rustc_privacy`
  (`EmbargoVisitor`, `ReachEverythingInTheInterfaceVisitor`), `rustc_passes`
  (`reachable_set`), and `rustc_monomorphize` (`collector`).
- **Lean 4 theorem prover (`leanprover/lean4` at
  `5045d0056413266e57c625dcd7c365b10e377c52`, release `v4.34.1`):** All
  mechanized definitions, positive and negative controls, and kernel `rfl`
  symbolic-evaluation proofs in
  [`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean) and
  [`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean)
  were checked under `lean -DElab.async=false -Ddebug.skipKernelTC=false` with
  zero `sorryAx`, zero `Lean.ofReduceBool`, and zero `Classical.choice`.

The `rustc` visibility findings depend on internal `rustc_private` query
behavior at commit `58cf8f9c35b355199727627d07ae34a4e2846d67` (in particular,
the `krate.opaques()` loop in `compiler/rustc_privacy/src/lib.rs`) and must be
revalidated via [`support/vis_probe/driver.rs`](support/vis_probe/driver.rs) when advancing the
pinned Rust toolchain.

### Part II — Exhaustive rustc Obligation Inventory and Single-Source x86-64 Artifact Binding

The findings in this report apply to the interaction of four concrete subjects:

- **`joshlf/anneal` at `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`** (MIR
  semantic verification baseline): specifically
  `trusted/rustc-capture/src/lib.rs`, `trusted/rustc-capture/src/proof_gen.rs`,
  and `trusted/lean/Trusted/MirSemantics.lean`.
- **`joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`**
  (MIR-to-x86-64 codegen pipeline): specifically
  `trusted/rustc-capture/src/lib.rs`, `trusted/rustc-capture/src/proof_gen.rs`,
  `trusted/lean/Trusted/X86Semantics.lean`,
  `theory/Anneal/Compiler/NaiveCodegen.lean`,
  `theory/Anneal/Compiler/Peephole.lean`, and
  `trusted/audit/TrustedBoundary.lean`.
- **`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`** (`rustc
  1.99.1`, `x86_64-unknown-linux-gnu`), invoked with `RUSTC_BOOTSTRAP=1` and
  the `rustc-dev` and `rustc-src` toolchain components to access
  `rustc_private` internal query APIs (`rustc_driver`, `rustc_hir`,
  `rustc_interface`, `rustc_middle`).
- **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`** (Lean 4
  `v4.34.1`, `x86_64-unknown-linux-gnu`), invoked with `-DElab.async=false` and
  `-Ddebug.skipKernelTC=false`.

The `rustc_middle::ty` and `rustc_mir_transform` query signatures documented in
Section 2 are internal compiler APIs with no stability guarantee across `rustc`
releases; exact method names and return wrappers (such as `clauses_of`,
`impl_trait_header`, and `Instance::resolve_drop_glue`) apply specifically to
`58cf8f9c35b355199727627d07ae34a4e2846d67`. The kernel reduction costs for
`String` equality in Section 4 apply to Lean 4 `v4.34.1`, where `String` is
backed by `ByteArray` (`Array UInt8` / `List UInt8`).

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

### Part I — Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Call Verification

#### 1. Public MIR Function Discovery in `rustc` and `trusted/rustc-capture`

##### 1.1 Textual MIR and HIR Dumps Strip Item Visibility

`Basis: source + execution`

Running `rustc --emit=mir`, `rustc -Z unpretty=mir`, or `rustc -Z unpretty=hir`
cannot distinguish public entry points from private functions:

1. **Textual MIR (`--emit=mir` and `-Z unpretty=mir`):**
   [`write_mir_pretty`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs)
   iterates over `tcx.mir_keys(())` and formats each signature with
   [`write_mir_sig`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs),
   which unconditionally emits `"fn "` followed by `tcx.def_path_str(def_id)`.
   In our probe crate ([`support/vis_probe/src/lib.rs`](support/vis_probe/src/lib.rs)),
   `pub fn cat1_top_pub`, `fn cat1_top_priv`, `pub(crate) fn
   cat1_top_pub_crate`, and `#[no_mangle] fn cat6_ffi_no_mangle` all emit
   identical `fn <name>(_1: u32) -> u32 {` headers with no visibility modifier
   or attribute.
2. **Textual HIR (`-Z unpretty=hir`):**
   `rustc` does not store visibility on `rustc_hir::Item` or
   `rustc_hir::ImplItem`; instead, `rustc_resolve` records syntactic
   visibilities out-of-band in `ResolverOutputs.visibilities` (queried via
   [`tcx.local_visibility(def_id)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/map.rs)).
   Consequently, `-Z unpretty=hir` prints both `pub fn` and `pub use` without
   `pub`.

Discovering a crate's external entry surface therefore requires querying
`TyCtxt` inside an in-process `rustc_driver::Callbacks::after_analysis` pass.

##### 1.2 Candidate MIR Body Enumeration: `mir_keys` vs. `hir_body_owners`

`Basis: source + execution`

In
[`compiler/rustc_mir_transform/src/lib.rs (lines 325-358)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs),
`tcx.mir_keys(())` constructs the authoritative `FxIndexSet<LocalDefId>` of
definitions that own MIR bodies by starting from `tcx.hir_body_owners()`
([`compiler/rustc_middle/src/hir/mod.rs (lines 106-108)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/mod.rs))
and making three adjustments:

1. It removes `DefKind::GlobalAsm` fake bodies.
2. It inserts `tcx.coroutine_by_move_body_def_id(body_owner)`
   (`DefKind::SyntheticCoroutineBody`) for coroutine-closures.
3. It inserts synthetic tuple-struct and tuple-enum variant constructors
   (`DefKind::Ctor(CtorOf::Struct | CtorOf::Variant, CtorKind::Fn)`), which have
   callable `optimized_mir` bodies (`PubStruct(x)`) despite having no HIR
   `BodyId` (`in_bo = false, in_mk = true` in
   [`support/vis_probe/driver_lib.txt`](support/vis_probe/driver_lib.txt)).

Required trait methods without a default body (`PubTrait::cat4_trait_req`) have
no `BodyId` and are absent from both `hir_body_owners()` and `mir_keys(())`,
whereas default trait methods (`PubTrait::cat4_trait_default`) appear in both.
Following
[`write_mir_sig`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs),
a `LocalDefId` in `tcx.mir_keys(())` is a callable runtime function when its
`DefKind` is `Fn`, `AssocFn`, `Ctor(_, CtorKind::Fn)`, `SyntheticCoroutineBody`,
or `Closure`.

##### 1.3 Empirical Evaluation of `TyCtxt` Visibility and Reachability Queries Across 7 Categories

`Basis: source + execution`

We evaluated five `TyCtxt` mechanisms in
[`support/vis_probe/driver.rs`](support/vis_probe/driver.rs) against a 7-category test crate
([`support/vis_probe/src/lib.rs`](support/vis_probe/src/lib.rs)) under both `--crate-type=lib`
([`support/vis_probe/driver_lib.txt`](support/vis_probe/driver_lib.txt)) and `--crate-type=bin`
([`support/vis_probe/driver_bin.txt`](support/vis_probe/driver_bin.txt)):

- **`nom_vis` (`tcx.local_visibility(def_id)`):** Defined in
  [`compiler/rustc_middle/src/hir/map.rs (lines 1265-1324)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/map.rs).
  Purely syntactic (`Visibility::Public` vs. `Visibility::Restricted(ModId)`);
  panics with `bug!("visibility of unexpected DefKind: Closure")` on closures,
  `Impl`, and `OpaqueTy`.
- **`Direct`, `Reexp`, `Reach`, `ReachIT`
  (`tcx.effective_visibilities(())`):** Defined in
  [`compiler/rustc_middle/src/middle/privacy.rs (lines 20-289)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/middle/privacy.rs)
  and computed by `EffectiveVisibilitiesVisitor` in
  [`compiler/rustc_resolve/src/effective_visibilities.rs (lines 27-202)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_resolve/src/effective_visibilities.rs)
  and `EmbargoVisitor` / `ReachEverythingInTheInterfaceVisitor` in
  [`compiler/rustc_privacy/src/lib.rs (lines 510-828)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs)
  and
  [` (lines 1809-1855)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs).
  Tracks four monotonic levels:
  $\text{Direct} \le \text{Reexported} \le \text{Reachable} \le \text{ReachableThroughImplTrait}$.
- **`reach` (`tcx.reachable_set(())`):** Defined in
  [`compiler/rustc_passes/src/reachable.rs (lines 459-524)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs).
  Computes cross-crate symbol/MIR linkage reachability.
- **`extern` (`tcx.codegen_fn_attrs(def_id).contains_extern_indicator()`):**
  Checks `#[no_mangle]`, `#[export_name]`, and `#[rustc_std_internal_symbol]`.
- **`mono` (`tcx.collect_and_partition_mono_items(())`):** Defined in
  [`compiler/rustc_monomorphize/src/collector.rs (lines 1483-1957)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs).

| Cat | Function (`def_path_str`) | `DefKind` | `nom_vis` | `Direct` | `Reexp` | `Reach` | `ReachIT` | `reach (lib)` | `reach (bin)` | `extern` | `mono (lib)` | `mono (bin)` | **External Entry?** |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **1** | `cat1_top_pub` | `Fn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **1** | `cat1_top_priv` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `true` | `true` | **No** (`mono` false positive: called by `main`) |
| **1** | `cat1_top_pub_crate` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **2** | `priv_mod::cat2_priv_mod_unexported` | `Fn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `false` | `false` | `false` | `false` | `false` | **No** (`nom_vis` false positive) |
| **2** | `priv_mod::cat2_priv_mod_reexported` | `Fn` | `Pub` | `Restr` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** (`Direct` false negative) |
| **3** | `PubStruct::cat3_pub_struct_inh_pub` | `AssocFn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **3** | `PubStruct::cat3_pub_struct_inh_pub_crate` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **3** | `PubStruct::cat3_pub_struct_inh_priv` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **3** | `PrivStruct::cat3_priv_struct_inh_pub` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `false` | `false` | `false` | `false` | `false` | **No** (`nom_vis` false positive) |
| **3** | `PrivStruct::cat3_priv_struct_inh_priv` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **3** | `priv_mod_type::PubInPrivMod::cat3_pub_in_priv_mod_inh_pub` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** (leaked via `pub fn` return type; `Reexp` false negative) |
| **3** | `priv_mod_type::PubInPrivMod::cat3_pub_in_priv_mod_inh_priv` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **4a** | `<PubStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **4a** | `PubTrait::cat4_trait_default` | `AssocFn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **4b** | `<RpitPrivStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** (returned via `pub fn -> impl PubTrait`) |
| **4b** | `RpitPrivStruct::cat4_rpit_priv_struct_inh_pub` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `true` | `false` | **No** (`ReachIT` false positive: caller only sees `impl PubTrait`) |
| **4b** | `<PrivFnRpitStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes (conservative)** / `ReachIT` `opaques()` `FIXME` |
| **4c** | `<DynPrivStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `true` | `false` | `false` | `true` | `false` | **Yes** (callable via `&'static dyn PubTrait`; `ReachIT` false negative!) |
| **4d** | `<UnexportedPrivStruct as PubTrait>::cat4_trait_req` | `AssocFn` | `Pub` | `Restr` | `Restr` | `Restr` | `Restr` | `true` | `false` | `false` | `true` | `false` | **Yes (conservative)** (implements exported trait `PubTrait`) |
| **4e** | `<PubStruct as PrivTrait>::cat4_priv_trait_req` | `AssocFn` | `Restr` | `Restr` | `Restr` | `Restr` | `Restr` | `true` | `false` | `false` | `true` | `false` | **No** (`reach (lib)` false positive!) |
| **4e** | `PrivTrait::cat4_priv_trait_default` | `AssocFn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `false` | `false` | `false` | `false` | **No** (`reach (lib)` false positive!) |
| **5** | `cat5_generic_pub_uninstantiated<T>` | `Fn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `false` | `false` | **Yes** (`mono` false negative!) |
| **5** | `cat5_generic_pub_instantiated<T>` | `Fn` | `Pub` | `Pub` | `Pub` | `Pub` | `Pub` | `true` | `false` | `false` | `true` | `false` | **Yes** |
| **5** | `cat5_generic_priv_uninstantiated<T>` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `false` | `false` | **No** |
| **5** | `cat5_priv_helper_called_by_generic` | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `true` | `false` | `true` | `false` | **No** (`reach` false positive!) |
| **6** | `cat6_ffi_no_mangle` (`#[no_mangle]`) | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `true` | `true` | `true` | `true` | **Yes** (`EffectiveVisibilities` false negative) |
| **6** | `cat6_ffi_export_name` (`#[export_name]`) | `Fn` | `Restr` | `-` | `-` | `-` | `-` | `true` | `true` | `true` | `true` | `true` | **Yes** (`EffectiveVisibilities` false negative) |
| **6** | `main` (in `--crate-type=bin`) | `Fn` | `Pub`/`Restr` | `Pub`/`-` | `Pub`/`-` | `Pub`/`-` | `Pub`/`-` | `true` | `false` | `false` | `true` | `true` | **Yes** (`tcx.entry_fn(()) == Some((def_id, _))`) |
| **7** | `cat7_make_adder_pub::{closure#0}` | `Closure` | `-` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `false` | `false` | **Yes** (returned via `pub fn -> impl Fn`) |
| **7** | `cat7_make_adder_priv::{closure#0}` | `Closure` | `-` | `Restr` | `Restr` | `Restr` | `Pub` | `true` | `false` | `false` | `false` | `false` | **No** (`ReachIT` false positive due to `opaques()` `FIXME`!) |
| **7** | `cat7_internal_closure_only::{closure#0}` | `Closure` | `-` | `-` | `-` | `-` | `-` | `false` | `false` | `false` | `true` | `false` | **No** |

Four subtle compiler behaviors explain the off-diagonal entries in the table:

1. **`Level::Reachable` vs. `Level::Reexported`:**
   `priv_mod_type::PubInPrivMod::cat3_pub_in_priv_mod_inh_pub` is `Restricted`
   at `Level::Direct` and `Level::Reexported` because `PubInPrivMod` is never
   re-exported by a `pub use`, but becomes `Public` at `Level::Reachable`
   because `pub fn cat3_leak_pub_in_priv_mod() -> priv_mod_type::PubInPrivMod`
   exposes the struct in a public return signature, allowing external callers to
   write `cat3_leak_pub_in_priv_mod(1).cat3_pub_in_priv_mod_inh_pub()`.
2. **`rustc_privacy` `opaques()` `FIXME` false positive at
   `Level::ReachableThroughImplTrait`:**
   In
   [`compiler/rustc_privacy/src/lib.rs (lines 1841-1846)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs),
   `ReachEverythingInTheInterfaceVisitor` iterates over `for opaque in
   krate.opaques()` and marks the hidden type of *every* `OpaqueTy` (`impl
   Trait`) in the crate as `Public` at `Level::ReachableThroughImplTrait`—with a
   comment `FIXME: Actually compute visibility of opaque types instead of
   pessimistically considering all of them pub`. As a result, a private function
   `fn cat7_make_adder_priv(x: usize) -> impl Fn(usize) -> usize` marks its
   returned closure `cat7_make_adder_priv::{closure#0}` as `Public` at
   `Level::ReachableThroughImplTrait`, and `RpitPrivStruct` has its inherent
   method `cat4_rpit_priv_struct_inh_pub` marked `Public` at
   `Level::ReachableThroughImplTrait` even though callers receiving `impl
   PubTrait` can only invoke `PubTrait` methods, never inherent methods on the
   hidden type.
3. **`dyn Trait` vtable coercion false negative in `EffectiveVisibilities`:**
   Because `rustc_privacy` inspects item signatures rather than function bodies,
   when a private struct `DynPrivStruct` implements `PubTrait` and is coerced to
   `&'static dyn PubTrait` inside `pub fn cat4_return_dyn()`,
   `<DynPrivStruct as PubTrait>::cat4_trait_req` remains `Restricted` across all
   four `EffectiveVisibility` levels even though external callers can invoke it
   through the returned vtable.
4. **Why `tcx.reachable_set(())` cannot be used for entry-point discovery:**
   In
   [`compiler/rustc_passes/src/reachable.rs (lines 206-209)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs)
   and
   [` (lines 411-431)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs),
   `ReachableContext` walks the HIR bodies of all generic, `#[inline]`, and
   `const` reachable functions and adds every private helper they call
   (`cat5_priv_helper_called_by_generic`) plus every trait `impl` method in the
   crate (`<PubStruct as PrivTrait>::cat4_priv_trait_req`) to
   `reachable_symbols`. Treating `reachable_set` as the public entry surface
   would force private helpers called by generic or inline public functions to
   satisfy unrestricted public preconditions.

##### 1.4 Exact 5-Rule External-Entry Discovery Predicate (`is_external_entry_fn`)

`Basis: source + execution + derived`

Combining `tcx.mir_keys(())` with the following 5-rule predicate over `TyCtxt`
classifies every row of the 7-category probe matrix without false negatives on
`dyn Trait`, FFI symbols, or `fn main`, and without false positives on private
helpers, inherent methods on RPIT hidden types, or closures inside private RPIT
functions:

```rust
pub fn is_external_entry_fn(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let eff_vis = tcx.effective_visibilities(());

    // Rule 1: Direct, re-exported, or signature-reachable public items.
    if eff_vis.is_reachable(def_id) {
        return true;
    }

    // Rule 2: Executable entry point (`fn main` or `#[start]`).
    if tcx.entry_fn(()).and_then(|(id, _)| id.as_local()) == Some(def_id) {
        return true;
    }

    // Rule 3: FFI / custom symbol export (`#[no_mangle]`, `#[export_name]`, EII).
    let kind = tcx.def_kind(def_id);
    if kind.has_codegen_attrs() {
        let attrs = tcx.codegen_fn_attrs(def_id);
        if attrs.contains_extern_indicator()
            || !attrs.foreign_item_symbol_aliases.is_empty()
        {
            return true;
        }
    }

    // Rule 4: Associated functions in `impl Trait for Type` where `Trait` is
    // foreign or publicly reachable (covers RPIT `impl Trait` and `dyn Trait`).
    if kind == DefKind::AssocFn {
        let parent_id = tcx.local_parent(def_id);
        if matches!(tcx.def_kind(parent_id), DefKind::Impl { of_trait: true }) {
            let trait_def_id = tcx.impl_trait_id(parent_id.to_def_id());
            let trait_is_public = !trait_def_id.is_local()
                || eff_vis.is_reachable(trait_def_id.expect_local());
            if trait_is_public {
                return true;
            }
        }
    }

    // Rule 5: Closures (or synthetic coroutine bodies) that escape an external
    // entry item via `impl Trait` (filtering out `rustc_privacy`'s `opaques()`
    // false positive on private functions returning `impl Trait`).
    if tcx.is_closure_like(def_id.to_def_id()) {
        let root_owner = tcx.typeck_root_def_id_local(def_id);
        if is_external_entry_fn(tcx, root_owner)
            && eff_vis.is_public_at_level(def_id, Level::ReachableThroughImplTrait)
        {
            return true;
        }
    }

    false
}
```

##### 1.5 Public-Surface Completeness in `Trusted.CrateTheorem`

`Basis: source + derived`

In `trusted/lean/Trusted/MirSemantics.lean` and
`trusted/lean/Trusted/Refinement.lean`, `Trusted.Crate` must retain *both*
public entry points and private helpers in a single `functions : List
CapturedFn` table so that `Terminator.call` and `mentionedItems` inside public
functions resolve against private helper bodies. Adding `isPublic : Bool :=
true` to `Trusted.CapturedFn` (populated by `trusted/rustc-capture` via
`is_external_entry_fn` for every callable item in `tcx.mir_keys(())`) preserves
public-surface completeness without modifying
`trusted/audit/TrustedBoundary.lean`:

1. `checkModuleImports` verifies that `.anneal/Mir.lean` imports only
   `foundation ++ trusted`.
2. `checkMirCrate` verifies that `Mir.crate : Trusted.Crate` is defined in
   module `Mir`.
3. `checkVerifyCrate` verifies that `Proof.verify_crate` has the exact type
   `Trusted.CrateTheorem Mir.crate`.

Because `is_external_entry_fn` is computed from `TyCtxt` queries rather than
user attributes, and `Proof.lean` cannot mutate or shadow `Mir.crate`, user code
cannot omit a public function or downgrade `isPublic` from `true` to `false`.

---

#### 2. Conditional Crate Verification and the Three-Level Calling-Condition Taxonomy

##### 2.1 Impossibility of Unconditional `MirLang.Spec` for Conditional Functions

`Basis: source + execution`

In Anneal's behavioral lattice
([`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean)),
refinement `p ≤ q` on `Partial α` is defined as:

```lean
def Partial.le (p q : Partial α) : Prop :=
  ∀ hq : q.defined, ∃ hp : p.defined, p.val hp ≤ q.val hq
```

Because `Language.Spec L post` is an abbreviation for `L.SpecOn (fun _ => True)
post`, `(L.Spec post q).defined` is `True` at *every* query `q : L.Query`.
Consequently, whenever a program's behavior `b` has `¬ (b q).defined` at even a
single valid initial state `q` (for example, when an arithmetic helper overflows
and transitions to `.failed .contractViolation`), `b` cannot refine `L.Spec
post` for *any* postcondition `post`—even when `post` is guarded by an
implication `pre q → ...`:

```lean
theorem not_le_spec_of_not_defined {L : Language} {b : L.Behavior}
    {q : L.Query} (hundef : ¬ (b q).defined)
    (post : L.Query → L.Out → Prop) :
    ¬ (b ≤ L.Spec post) :=
  fun hle => hundef (hle q True.intro).1
```

In
[`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean),
`addBody_not_wellFormed` and `addBody_not_le_spec` instantiate this theorem on
`addBody` (`fn add(x: usize, y: usize) -> usize { x + y }`) at the valid initial
state `addOverflowInit` (`_1 = usizeMax, _2 = 1`, step budget `2`), proving
`¬ (MirSem addBody ≤ MirLang.Spec post)` for every `post`. Any function with a
non-trivial safety or no-failure precondition `pre` must therefore state its
contract using `MirLang.SpecOn pre post` (`defined := pre q`) and
`MirLang.WellFormedOn pre`.

##### 2.2 Three-Level Taxonomy of Calling Conditions

`Basis: derived + execution`

Mapping calling conditions onto the machine initial-state predicate
`M.initState` and the two fields of `Partial` (`defined` and `val`) yields three
orthogonal levels mechanized in
[`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean)
and [` (lines 673-685)`](support/ConditionalCrateVerification.lean):

| Level | Calling Condition Class | Representation in Anneal | Semantic Effect When Violated |
| :--- | :--- | :--- | :--- |
| **Level 1: ABI / Type / Memory / Aliasing Validity** | Well-typed arguments in `_1.._n`, uninitialized scratch locals, `block = 0`, `stmtIdx = 0`, `frames = []`, valid entry heap | `MirMachine.initState` (`initMirState`) | `(MirSem body q).defined = True` and `(MirSem body q).val = False`; vacuously refines any spec (`behaviorOf_outside_initState_vacuous`), mirrored by `AeneasRes.inapplicable` in `FuncLang` |
| **Level 2: Safety / No-Failure Precondition (`pre`)** | Checked-arithmetic bounds (`x + y <= usizeMax`), raw-pointer validity, slice bounds, `unsafe fn` contracts | `fn.pre : ExecQuery MirState → Prop` in `MirLang.WellFormedOn fn.pre` and `MirLang.SpecOn fn.pre post` (`.defined := fn.pre q`) | `(SpecOn fn.pre post q).defined = False` (`⊤` in `Partial`), imposing no obligation on `MirSem body q` outside `fn.pre` |
| **Level 3: Functional Precondition (`req`)** | Logical domain assumptions on an already-safe function (e.g., input slice is sorted for `binary_search`) | Implicational guard inside `.val`: `MirLang.SpecOn fn.pre (fun q out => req q → post q out)` | `.defined = fn.pre q` still holds (execution is still proved safe), while `post q out` is only promised when `req q` holds |

Two structural lemmas govern how these levels compose:

1. **Implicational vs. Existential State Preconditions
   ([`preAdd_iff_exists_on_init`](support/ConditionalCrateVerification.lean)):**
   Writing `FuncPreAdd init` implicationally (`∀ x0 y0, init.locals 1 = some
   (.usize x0) → init.locals 2 = some (.usize y0) → x0 + y0 ≤ usizeMax`) is
   equivalent to the existential form `PreAddExists` on every valid entry state
   satisfying `initMirState addBody q.init`, but automatically holds on
   ill-typed states outside `initMirState` where `translate body init =
   .inapplicable`.
2. **Single-Proof Discharge of `WellFormedOn`
   ([`specOn_le_wellFormedOn`](support/ConditionalCrateVerification.lean),
   [`specOn_functional_req_le_wellFormedOn`](support/ConditionalCrateVerification.lean),
   [`Compiler.Verified.with_wellFormedOn`](support/ConditionalCrateVerification.lean)):**
   Because `L.SpecOn pre post ≤ L.WellFormedOn pre` holds for any `post`
   (including `fun q out => req q → post q out`), a single proof of
   `C.Verified prog (L.SpecOn pre ...)` discharges both the functional
   specification and `L.WellFormedOn pre` in `VerificationResultOn`.

##### 2.3 Conditional `FunctionalTranslation` (`funcSem_le_specOn` and `π_func_specOn_le`)

`Basis: derived + execution`

Generalizing `FunctionalTranslation` to conditional specifications requires
replacing the unconditional bridge lemmas `funcSem_le_spec` and `π_func_spec_le`
with
[`funcSem_le_specOn`](support/ConditionalCrateVerification.lean) and
[`π_func_specOn_le`](support/ConditionalCrateVerification.lean):

```lean
theorem funcSem_le_specOn {p : MirState → AeneasRes MirVal}
    {Pre : MirState → Prop} {Post : MirState → MirVal → Prop}
    (h : ∀ init, Pre init → p init ≠ .fail ∧ ∀ v, p init = .ok v → Post init v) :
    FuncLang.sem p ≤ FuncLang.SpecOn Pre Post

theorem π_func_specOn_le (Pre : MirState → Prop) (Post : MirState → MirVal → Prop) :
    π_func (FuncLang.SpecOn Pre Post) ≤
      MirLang.SpecOn (fun q => Pre q.init) (fun q out =>
        ∀ v, out.outcome = .terminated (.normal v) → Post q.init v)
```

Crucially, `π_func`, `monotone_π_func`, and `evalSym_sound` (`MirSem body ≤
π_func (FuncLang.sem (evalSym plan body))`) require **zero changes**. When an
input violates `Pre init` and causes `evalSym plan body init = .fail`, `π_func`
maps `.fail` to `{ defined := False }` (`Partial.ub`, the top element `⊤` of the
refinement preorder), so `MirSem body q ≤ π_func (FuncLang.sem ...) q` holds
trivially on failing inputs while enforcing safety and functional correctness on
all inputs where `Pre init` holds and `evalSym` returns `.ok v`.

##### 2.4 Mode 1 (`.failed .contractViolation`) vs. Mode 2 (`.terminated .unwind`) Overflow Semantics

`Basis: normative + execution`

Section 7 of
[`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean)
compares Anneal's Mode 1 panic-free semantics (`MirLang`, where
`assertNotOverflow` transitions to `.failed .contractViolation`) against Mode 2
unwinding semantics (`MirLangUnwind`, where `assertNotOverflow` transitions to
`.terminated .unwind`) on the same `addBody` AST:

| Dimension | Mode 1: `.failed .contractViolation` (`MirLang`) | Mode 2: `.terminated .unwind` (`MirLangUnwind`) |
| :--- | :--- | :--- |
| **`outcome.isSafe` on arithmetic overflow** | `False` | `True` (stack unwinding is defined behavior in safe Rust) |
| **Unconditional `WellFormed` for `addBody`** | **False** ([`addBody_not_wellFormed`](support/ConditionalCrateVerification.lean)) | **True** ([`addBody_satisfies_wellFormedUnwind`](support/ConditionalCrateVerification.lean)) |
| **Specification level for `addBody` no-overflow** | Level 2 (`MirLang.SpecOn PreAdd PostAdd`, [`addBody_satisfies_ensuresOn`](support/ConditionalCrateVerification.lean)) | Level 3 (`MirLangUnwind.Spec` with `x0 + y0 ≤ usizeMax → out.outcome ≠ .terminated .unwind` in `.val`, [`addBody_satisfies_ensuresUnwind`](support/ConditionalCrateVerification.lean)) |
| **Where Level 2 (`SpecOn`) remains mandatory** | Checked arithmetic, `assert!`, division/remainder by zero, bounds checks, and `unsafe fn` preconditions | `unsafe fn` preconditions (raw-pointer dereference, aliasing, `get_unchecked`) where violation is true UB (`.failed .ub`) |

---

#### 3. Call-Stack `Terminator.call`, Transitive `CompileAdmitted`, and Dual-Mode Interprocedural Verification

##### 3.1 Eliminating `PureCallee2` and `CalleeSummaryVerified` from `trusted/` via Call-Stack `Terminator.call`

`Basis: normative + source + execution`

In Stage I ([`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean)),
interprocedural calls were modeled by extending `evalPureCallee2` to return
`Option (Bool × MirVal)` and requiring `CalleeSummaryVerified` in
`CrateTheorem`. While sound, that interim design kept a hardcoded `PureCallee2`
enumeration and summary-adequacy predicate inside the TCB.

Applying `model-refinement` in Stage II
([`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean)),
we replace `Terminator.callPure2` with a general crate-resolved
`Terminator.call dst callee args target` matching the normative semantics of
`TerminatorKind::Call` and `TerminatorKind::Return` in
[`compiler/rustc_middle/src/mir/syntax.rs (lines 696-784)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs):

1. **Call-Stack State (`CallFrame` and `MirState`):**
   `MirState` ([`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean))
   records the active `curBody : MirBody` and a stack of suspended caller
   continuations `frames : List CallFrame`, where each `CallFrame` stores
   `callerBody`, `dst : LocalIdx`, `returnTarget : BasicBlockIdx`, and
   `callerLocals : Nat → Option MirVal`.
2. **Operational Call and Return Transitions (`evalMirTerminator`):**
   - On `Terminator.call dst callee args target`
     ([` (lines 964-983)`](support/InterproceduralConditionalMir.lean)), the machine
     evaluates `args` left-to-right via `evalOperandList`, looks up `callee` in
     `env : CrateEnv`, validates argument arity and types via
     `argsHaveTysBool argVals calleeBody.argTys`, pushes a `CallFrame` onto
     `s.frames`, and steps to `calleeBody` at `block := 0, stmtIdx := 0` with
     `locals := buildCalleeLocals argVals`.
   - On `Terminator.return_`
     ([` (lines 940-958)`](support/InterproceduralConditionalMir.lean)), reading
     `s.locals 0 = some retVal` either terminates with `.terminated (.normal
     retVal)` when `s.frames = []` or pops `frame :: restFrames`, restoring
     `frame.callerBody` at `frame.returnTarget.index` with `frame.dst.index`
     updated to `some retVal`.
3. **Preservation of Layer 1B Machine Health Theorems:**
   Because `evalMirStep env s` is a total deterministic function that never
   emits `StepResult.choice`, the call-stack `MirMachine` satisfies:
   - [`mirMachine_totalStep`](support/InterproceduralConditionalMir.lean)
     (`TotalStep MirMachine`),
   - [`mirMachine_inhabitedDemonic`](support/InterproceduralConditionalMir.lean)
     (`InhabitedDemonic MirMachine`), and
   - [`mirMachine_non_vacuity_at_every_depth`](support/InterproceduralConditionalMir.lean)
     (every valid initial state has a non-`.stuck` execution prefix at every
     step budget `n : Nat` across arbitrary call depth).

Because `MirMachine` executes the callee's actual `MirBody` on the call stack,
`trusted/` needs neither `PureCallee2` nor `CalleeSummaryVerified`.

##### 3.2 Transitive `CompileAdmitted` Across `requiredConsts` and `mentionedItems`

`Basis: source + execution`

In
[`compiler/rustc_monomorphize/src/collector.rs (lines 1364-1389)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs),
`collect_items_of_instance` evaluates every constant in `body.required_consts()`
and visits every item in `body.mentioned_items()` (including items inside dead
runtime branches `if false { ... }`) in `CollectionMode::MentionedItems`, which
recursively evaluates the target item's `required_consts()`.

In
[`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean),
each `MirBody` carries `requiredConsts : List ConstMirBody` and `mentionedItems
: List String`, and transitive compile-time admissibility is defined alongside
its executable boolean checker:

```lean
def CompileAdmitted (env : CrateEnv) : Nat → MirBody → Prop
  | 0, _ => False
  | fuel + 1, body =>
    AllHold (body.requiredConsts.map CtfeAdmitted) ∧
    AllHold (body.mentionedItems.map (fun calleeName =>
      match lookupFn env calleeName with
      | some calleeBody => CompileAdmitted env fuel calleeBody
      | none => False))
```

By [`compileAdmitted_of_checkCompileAdmitted`](support/InterproceduralConditionalMir.lean),
`checkCompileAdmitted env ctfeFuel fuel body = true` implies
`CompileAdmitted env fuel body`, discharging compile-time admissibility on
concrete crates by kernel `rfl`. Section 7.4
([` (lines 3881-4117)`](support/InterproceduralConditionalMir.lean)) mechanizes
both positive and negative controls over `const_bounded_add<N>(x)` (containing
`const { assert!(N <= 1000) }` in `requiredConsts`):

- **Positive control (`caller_good_500`):** Calls `const_bounded_add::<500>(x)`.
  Proved both compile-admitted by `rfl`
  ([`callerGood500_compileAdmitted`](support/InterproceduralConditionalMir.lean))
  and runtime-safe via Mode A call inlining
  ([`callerGood500_runtime_verified`](support/InterproceduralConditionalMir.lean)).
- **Dead-branch negative control (`dead_branch_bad_caller`):** Executes `if
  false { const_bounded_add::<2000>(x) } else { x }`. At runtime, it is verified
  safe
  ([`deadBranchBadCaller_runtime_verified`](support/InterproceduralConditionalMir.lean))
  because `switchInt (const false)` always jumps to the live `else` branch. At
  compile time, however, `"const_bounded_add_2000" ∈ mentionedItems` causes
  `CompileAdmitted` to be refuted at **every** fuel depth `fuel : Nat`
  ([`deadBranchBadCaller_not_compileAdmitted`](support/InterproceduralConditionalMir.lean)),
  and its `Behavior.when`-gated behavior collapses to `Partial.bot`
  ([`deadBranchBadCaller_when_compileAdmitted_refines_any`](support/InterproceduralConditionalMir.lean)).

##### 3.3 Unified Spine-Preserving `evalSymState` and Dual-Mode Interprocedural Verification

`Basis: derived + execution`

In
[`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean),
`evalSymState env summaries plan body sym` returns `Option (Bool × SymVal)`
(`some (failed, retSv)`). Two combinators preserve outer `some` and `SymVal`
constructors across branches and calls so Lean's kernel reduces interprocedural
symbolic execution by `rfl`:

1. **Right-matching `orBool`
   ([` (lines 1643-1656)`](support/InterproceduralConditionalMir.lean)):**
   `def orBool (ov1 ov2 : Bool) : Bool := match ov2 with | false => ov1 | true
   => true`. Because `Terminator.return_` produces `failed = false`, matching on
   `ov2` first reduces `orBool (decide (usizeMax < x + x)) false` definitionally
   to `decide (usizeMax < x + x)` by `rfl` even when `x : Nat` is a free
   symbolic variable.
2. **Constructor-lifting `mergeBranchSymVal`
   ([` (lines 1660-1683)`](support/InterproceduralConditionalMir.lean)):**
   Lifts the shared `SymVal` constructor (`.usize`, `.bool`, `.unit`) outside
   `match cond with` across `Terminator.switchInt`.

To prove soundness across arbitrary call-stack depth in a single structural
induction without step-count arithmetic,
[`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean)
defines prefix safety `SafeFrom` and a frame-stack continuation invariant
`ReturnCont`:

```lean
def ReturnCont (env : CrateEnv) (frames : List CallFrame) (retVal : MirVal)
    (finalVal : MirVal) : Prop :=
  match frames with
  | [] => retVal = finalVal
  | frame :: restFrames =>
    ∀ (mem : MemState),
      SafeFrom env
        { curBody := frame.callerBody
          locals := updateLocal frame.callerLocals frame.dst.index (some retVal)
          mem := mem
          block := frame.returnTarget.index
          stmtIdx := 0
          frames := restFrames }
        finalVal
```

The master soundness theorem
[`evalSymState_sound`](support/InterproceduralConditionalMir.lean) handles
two interprocedural call plan constructors in `TransPlan`:

| Dimension | Mode A: Symbolic Call Inlining (`TransPlan.callInline`) | Mode B: Modular Callee Summaries (`TransPlan.callSummary`) |
| :--- | :--- | :--- |
| **User annotation burden on private helpers** | **Zero:** private helper `add` (`isPublic = false`) needs no `Pre`, `Post`, or summary ([`prove_guarded_crate_modeA`](support/InterproceduralConditionalMir.lean)) | Requires a conditional spec `MirLang.SpecOn Pre Post` ([`addBody_verified_specOn`](support/InterproceduralConditionalMir.lean)) and `CalleeSummary` ([`addSummary_sound`](support/InterproceduralConditionalMir.lean)) |
| **Kernel `rfl` reduction on `double_guarded(x)`** | [`evalSymState_doubleGuarded_modeA_rfl`](support/InterproceduralConditionalMir.lean) | [`evalSymState_doubleGuarded_modeB_rfl`](support/InterproceduralConditionalMir.lean) (definitionally equal to Mode A by `rfl` in [`evalSymState_doubleGuarded_modeA_eq_modeB`](support/InterproceduralConditionalMir.lean)) |
| **Summary soundness bridge** | Not needed (`summaries = []`) | [`summaryEntrySound_of_evalSymState`](support/InterproceduralConditionalMir.lean) proves `SummaryEntrySound` from `evalSymState` in 20 lines; [`bogusUnconditionalAddSummary_not_sound`](support/InterproceduralConditionalMir.lean) rejects an unconditional summary for `add` |
| **Top-level crate theorem** | [`PublicAdmittedCrateTheorem`](support/InterproceduralConditionalMir.lean) (checks `c.publicFns` while resolving calls against full `c.toEnv`) | [`ModularAdmittedCrateTheorem`](support/InterproceduralConditionalMir.lean) (verifies all `c.fns` against their respective `f.pre` and `f.specs`, [`prove_modular_crate_modeB`](support/InterproceduralConditionalMir.lean)) |

Because both Mode A and Mode B execute against the same call-stack `MirMachine`
in `trusted/` and the same `evalSymState` evaluator in `theory/`, Anneal can
default to Mode A (`callFuel > 0`) for unannotated private helpers and switch to
Mode B whenever a helper carries an explicit contract or is recursive, with zero
summary machinery in the TCB.

### Part II — Exhaustive rustc Obligation Inventory and Single-Source x86-64 Artifact Binding

#### 1. Omission and Spoofing Vulnerabilities in `trusted/rustc-capture`

`Basis: source + derived`

In both `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`
(`trusted/rustc-capture/src/lib.rs:399-550`) and
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`
(`trusted/rustc-capture/src/lib.rs:577-795`), `capture_crate_with_options`
reads a single source file (`src/lib.rs`), runs `parse_source_metadata` over
raw lines (`src.lines()`), invokes `rustc --emit=mir=crate.mir`, and parses the
textual MIR dump via `parse_emitted_mir_with_metadata`. This architecture has
six distinct soundness vulnerabilities:

1. **Single-file and hardcoded-identifier ADT discovery (`lib.rs:408`,
   `517-531`, `850-863`, `1296-1312` in `the `StepResult` MIR refinement prototype (`support/`)`):**
   `capture_crate_with_options` reads only `crate_dir.join("src/lib.rs")`; any
   item declared in a submodule file (`mod sub;`) is unseen by
   `parse_source_metadata`. Even within `src/lib.rs`, `parse_source_metadata`
   only checks `line.contains("struct NonZeroUsize")`. Every other `struct`,
   `enum`, or `union` in the crate is omitted from `Mir.crate.adts`.
2. **Line-scanner spoofing of `allFieldsPubSafe` and `FieldAccess`
   (`lib.rs:517-531` in `the `StepResult` MIR refinement prototype (`support/`)`; `lib.rs:762-776` in `the MIR-to-x86-64 codegen prototype (`support/`)`):**
   Once `"struct NonZeroUsize"` is seen, `parse_source_metadata` executes:
   ```rust
   } else if nonzero_field_pub_safe.is_some() {
       if line.starts_with("pub val: usize") {
           nonzero_field_pub_safe = Some(true);
       } else if line.starts_with("val: usize") {
           nonzero_field_pub_safe = Some(false);
       }
   }
   ```
   Because `nonzero_field_pub_safe.is_some()` remains `true` for the remainder
   of `src/lib.rs`, a struct with a public field (`pub val: usize`) followed
   anywhere later in the file by a raw string literal or multi-line comment
   containing a line starting with `val: usize` overwrites
   `nonzero_field_pub_safe` back to `Some(false)` (`FieldAccess.priv`). Even
   without a comment, formatting `pub\n val: usize` across two lines or using a
   tuple struct `pub struct NonZeroUsize(pub usize);` leaves
   `allFieldsPubSafe := false` in `Mir.crate`. In
   `Trusted/MirSemantics.lean:778-785`, `AdmissibleAdtInv` only constrains
   `allFieldsPubSafe = true` types to `TrivialValInv`; setting
   `allFieldsPubSafe := false` on a publicly constructible struct allows the
   crate to attach a non-trivial library invariant `I_lib(v) := v != 0` that
   safe external callers can violate by constructing `NonZeroUsize { val: 0 }`
   directly. Conversely, `#[unsafe]` fields (RFC 3458) and `#[non_exhaustive]`
   attributes are ignored.
3. **Spoofing and omission of `FnKind` (`pubSafe`, `pubUnsafe`, `priv`)
   (`lib.rs:532-542`, `701-705`, `1274-1287` in `the `StepResult` MIR refinement prototype (`support/`)`):**
   `parse_source_metadata` populates `meta.unsafe_fns` solely via
   `line.strip_prefix("pub unsafe fn ")`.
   - **False-positive `pubUnsafe` spoofing:** Placing `\npub unsafe fn foo(`
     inside a block comment `/* ... */` or raw string literal `r#"..."#`
     inserts `"foo"` into `meta.unsafe_fns`. When `foo` is actually a safe
     `pub fn foo(x: usize)`, `render_mir_lean_with_metadata` emits
     `FnKind.pubUnsafe True newUncheckedSafetyPre`, granting a safe public
     function an unchecked caller precondition (`x != 0`) and discharging its
     verification obligation under a false assumption.
   - **False-negative `pubSafe` and missing `priv` classification:** A public
     unsafe function written as `pub const unsafe fn`,
     `pub unsafe extern "C" fn`, or across two lines (`pub unsafe\nfn`) fails
     `strip_prefix("pub unsafe fn ")` and is emitted as
     `CapturedFnKind::PubSafe`. Moreover, `CapturedFnKind` has no `Priv`
     variant (`Trusted.FnKind.priv` exists in `MirSemantics.lean:769`, but
     `rustc-capture` only models `PubSafe` and `PubUnsafeNewUnchecked`), and
     `parse_fn_header` (`lib.rs:753-760`) strips all module and impl prefixes
     via `raw_name.rsplit("::").next()`, colliding functions that share a
     basename across modules or `impl` blocks.
4. **Total omission of `unsafeImpls` (`Trusted.UnsafeImplObligation`)
   (`MirSemantics.lean:826-838`, `X86Semantics.lean:855-867`):**
   Although `Trusted.Crate` defines
   `unsafeImpls : List UnsafeImplObligation := []` and `CrateTheorem` requires
   `AllHold (c.unsafeImpls.map ...)`, `render_mir_lean_with_metadata` in
   `trusted/rustc-capture/src/lib.rs` (`the `StepResult` MIR refinement prototype (`support/`):1296-1312` and
   `the MIR-to-x86-64 codegen prototype (`support/`):1532-1548`) never emits the `unsafeImpls` field. Consequently,
   `Mir.crate.unsafeImpls` defaults to `[]` for every crate, and every
   `unsafe impl Send`, `unsafe impl Sync`, or user-defined `unsafe trait`
   implementation is unverified.
5. **Constant/static collision and missing `mentioned_items` (`lib.rs:456-460`,
   `591-595`, `1062-1071` in `the `StepResult` MIR refinement prototype (`support/`)`):**
   `parse_emitted_mir_with_metadata` only recognizes top-level MIR headers
   matching `line.starts_with("const ")` or `line.contains("::{constant#")`
   combined with `line.ends_with(": () = {")`, and renames every matched
   constant to the single hardcoded identifier `"pme_assert_const"`. Any
   non-`()` constant or `static` initializer is rejected (`unsupported function
   header`), two `()` constants in the same crate produce duplicate Lean
   declarations (`Mir.pme_assert_const_body`), and `requiredConsts` is
   populated only by matching statement text against `::ASSERT` or
   `::{constant#`. Calls in dead branches (`if false { f::<0>(); }`) whose
   post-monomorphization error (PME) obligations are tracked via
   `Body::mentioned_items` are omitted when `SimplifyCfg` removes the branch.
6. **Invisibility of inherited trait default methods and compiler shims:**
   When a crate implements a trait (`impl SafeTrait for LocalAdt {}` or
   `impl Clone for LocalAdt { fn clone(&self) -> Self { ... } }`) without
   overriding a default method (`SafeTrait::default_mutate` or
   `Clone::clone_from`), `--emit=mir` emits no MIR body for the inherited
   method specialization on `LocalAdt`. Likewise, compiler-synthesized drop
   glue (`ShimKind::DropGlue`) for a struct containing droppable fields has no
   entry in `tcx.mir_keys(())` or `--emit=mir`.

#### 2. Exhaustive Crate Obligation Inventory via `rustc_driver` `TyCtxt` Queries

`Basis: source + execution`

Replacing the subprocess `--emit=mir` invocation with an in-process
`rustc_driver::Callbacks::after_analysis` pass provides direct access to
`TyCtxt` after type checking, borrow checking, privacy analysis, and drop
elaboration have succeeded (`compiler/rustc_interface/src/passes.rs:1154-1282`).
The standalone probe in `support/obligation_inventory_probe/` verifies the
exact `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) query recipes
and required guards across all five obligation categories:

| Category | Soundness-Bearing Obligation | Exact `rustc 1.99.1` (`58cf8f9c3`) `TyCtxt` Query Recipe | Empirical Pitfalls & Required Guards |
| :--- | :--- | :--- | :--- |
| **(a) `unsafe impl` & Polarities** | Every local trait `impl` (`unsafe impl`, safe `impl`, negative `impl !Trait`) and its `where`-clauses | Iterate `tcx.hir_crate_items(()).definitions()` where `tcx.def_kind(def_id) == DefKind::Impl { of_trait: true }`. Query `let header = tcx.impl_trait_header(def_id);` (`ty::ImplTraitHeader` at `rustc_middle/src/ty/mod.rs:299-304`) for `header.safety` (`hir::Safety::Unsafe` vs `Safe`), `header.polarity` (`ImplPolarity::Positive`, `Negative`, `Reservation`), `let trait_ref = header.trait_ref.skip_binder();`, `tcx.trait_def(trait_ref.def_id).safety`, and `tcx.clauses_of(def_id).clauses` (`rustc_middle/src/ty/generics.rs:386-389`). | In `rustc 1.99.1`, `header.trait_ref.instantiate_identity()` returns `Unnormalized<'tcx, TraitRef<'tcx>>`; use `header.trait_ref.skip_binder()` (or `.instantiate_identity().skip_norm_wip()`) to access `.def_id`, `.self_ty()`, and `.args`. Also, `tcx.predicates_of` was replaced by `tcx.clauses_of(def_id)`. Negative impls (`impl !Sync for RawPtrBox`) have `header.polarity == ImplPolarity::Negative` and no associated methods. |
| **(b) ADTs, Field Visibilities, `#[non_exhaustive]`, `#[unsafe]`** | Every `Struct`, `Enum`, and `Union`; per-field `Trusted.FieldAccess` (`pubSafe`, `priv`, `unsafeField`); `allFieldsPubSafe` | Filter `tcx.hir_crate_items(()).definitions()` for `DefKind::Struct \| DefKind::Enum \| DefKind::Union`. Query `let adt_def = tcx.adt_def(def_id);`, `let eff_vis = tcx.effective_visibilities(());`, `adt_def.adt_kind()`, `adt_def.repr()`, and `let is_non_exhaustive = adt_def.is_variant_list_non_exhaustive() \|\| adt_def.variants().iter().any(\|v\| v.is_field_list_non_exhaustive());`. For each `field` in `variant.fields`, inspect `field.safety` (`Safety::Unsafe` vs `Safe`) and `eff_vis.is_reachable(field.did.expect_local())`. | **Syntactic `vis.is_public()` vs. effective reachability:** In `mod inner_private { pub struct UnreachableAllPub { pub x: usize } }`, `field.vis.is_public()` is `true`, whereas `eff_vis.is_reachable(...)` is `false` because `inner_private` is unexported (`output.txt:41-43`). Conversely, for a reachable struct, `allFieldsPubSafe` is `true` iff `adt_def.is_struct() && !is_non_exhaustive && adt_eff_reachable && variants[0].fields.iter().all(\|f\| f.safety == Safety::Safe && eff_vis.is_reachable(f.did.expect_local()))`. Unions (`adt_def.is_union()`) have unsafe field reads in Rust even when all fields are `pub` (`output.txt:44-47`), so `allFieldsPubSafe` must be `false` for unions unless modeled separately. |
| **(c) Trait Default Methods & Safe Trait Impls** | Overridden and inherited default methods on every positive local trait `impl` (including foreign traits such as `core::clone::Clone`) | For each positive `DefKind::Impl { of_trait: true }`, obtain `let trait_ref = header.trait_ref.skip_binder();`, `let impl_map = tcx.impl_item_implementor_ids(impl_def_id);`, and `let typing_env = ty::TypingEnv::non_body_analysis(tcx, impl_def_id);`. Iterate `tcx.associated_items(trait_ref.def_id).in_definition_order().filter(\|it\| it.is_fn())` and resolve each method via `ty::Instance::try_resolve(tcx, typing_env, assoc_item.def_id, trait_ref.args)` (`rustc_middle/src/ty/instance.rs:562-601`). Fetch the body via `tcx.instance_mir(inst.def)`. | When an impl omits a default method (`SafeMutatorTrait::default_zero_out` or `core::clone::Clone::clone_from` on `EncapsulatedNonZero`), `impl_map.get(&assoc_item.def_id)` is `None`, and the specialized method does **not** appear in `tcx.mir_keys(())`. However, `Instance::try_resolve` resolves it to `Instance { def: Item(default_fn_did), args: [EncapsulatedNonZero, ...] }` (`output.txt:72, 76`), allowing `anneal-rustc-capture` to instantiate and verify the default method against `EncapsulatedNonZero`'s `AdmissibleAdtInv`. |
| **(d) `Drop::drop`, Drop Glue, & Shims** | Explicit `Drop::drop` impls, synthesized `ShimKind::DropGlue`, `ShimKind::ClosureOnce`, `ShimKind::Reify`, `ShimKind::VTable`, `ShimKind::Clone` | For each ADT, query `adt_def.destructor(tcx)` for explicit `Drop::drop`. For non-polymorphic ADTs (`!tcx.generics_of(def_id).requires_monomorphization(tcx)`), construct `let adt_ty = Ty::new_adt(tcx, adt_def, GenericArgs::identity_for_item(tcx, def_id));` and call `ty::Instance::resolve_drop_glue(tcx, adt_ty)` (`instance.rs:789-799`), then `tcx.instance_mir(drop_inst.def)`. For closures (`DefKind::Closure`), extract `let ty::TyKind::Closure(_, closure_args) = *tcx.type_of(def_id).skip_binder().kind()` and call `ty::Instance::fn_once_adapter_instance(tcx, def_id, closure_args)` (`instance.rs:823-851`). | 1. In `rustc 1.99.1`, `InstanceKind::Shim(ty::ShimKind::...)` wraps `ShimKind`, and `resolve_drop_in_place` was renamed to `Instance::resolve_drop_glue(tcx, ty)` (`instance.rs:789`).<br>2. For `OuterWithDropGlue`, `adt_def.destructor(tcx)` is `None`, yet `Instance::resolve_drop_glue` returns `Shim(DropGlue(core::ptr::drop_glue, Some(OuterWithDropGlue)))` (`bbs=2`, `output.txt:95`).<br>3. Calling `Instance::fn_once_adapter_instance` with `GenericArgs::identity_for_item(tcx, closure_did)` **panics** (`closure_sig_as_fn_ptr_ty is not a fn-ptr: /#1`) because closure identity args contain synthetic `ParamTy` placeholders; extract `closure_args` from `tcx.type_of(def_id).skip_binder().kind()`. |
| **(e) `static`, `const`, `required_consts`, & `mentioned_items`** | Every MIR body in `tcx.mir_keys(())`, CTFE initializers, inline `const { ... }` blocks, and PME obligations in dead branches | Iterate `tcx.mir_keys(())` (`rustc_mir_transform/src/lib.rs:327-358`). First check `if tcx.is_trivial_const(local_def_id)` and use `tcx.trivial_const(local_def_id)`. Otherwise: for `DefKind::Const { .. } \| DefKind::AssocConst { .. } \| DefKind::Static { .. } \| DefKind::AnonConst`, query `tcx.mir_for_ctfe(def_id)` (`phase == Runtime(PostCleanup)`). For `DefKind::Fn \| DefKind::AssocFn \| DefKind::Closure`, borrow `tcx.mir_drops_elaborated_and_const_checked(local_def_id)` **before** calling `tcx.optimized_mir(def_id)` to obtain the exact `Runtime(PostCleanup)` body, and then read `tcx.optimized_mir(def_id).mentioned_items`. | 1. **Trivial const guard:** Calling `tcx.mir_for_ctfe(def_id)` on a trivial constant (`pub const TRIVIAL_CONST: usize = 99;`) trips `debug_assert!(!tcx.is_trivial_const(def_id))` (`rustc_mir_transform/src/lib.rs:493`). Always check `tcx.is_trivial_const(local_def_id)` first (`output.txt:115, 122`).<br>2. **`mentioned_items` panic guard:** `MentionedItems` runs only inside `inner_optimized_mir` (`rustc_mir_transform/src/lib.rs:810`). Calling `body.mentioned_items()` on `mir_for_ctfe` (for any `Const`, `AssocConst`, `Static`, or `AnonConst`) **panics** (`mentioned_items for DefId(...) have not yet been set`). Read `body.required_consts.as_deref()` and `body.mentioned_items.as_deref()` as `Option`s.<br>3. **Steal ordering for `Runtime(PostCleanup)`:** `tcx.optimized_mir(did)` steals `tcx.mir_drops_elaborated_and_const_checked(did)` (`rustc_mir_transform/src/lib.rs:800`) and transitions `body.phase` to `Runtime(Optimized)` (even at `-Z mir-opt-level=0`, running passes such as `RemoveStorageMarkers`, `RemoveZsts`, and `InstSimplify`). To capture unadulterated `Runtime(PostCleanup)` MIR for functions while still obtaining `mentioned_items`, clone or serialize `tcx.mir_drops_elaborated_and_const_checked(local_def_id).borrow()` before invoking `tcx.optimized_mir(def_id)` (`output.txt:120`). |

#### 3. Dual-Emitter and Shadow-Artifact Defects in the MIR-to-x86-64 Pipeline

`Basis: source + derived`

Tracing the verification and assembly pipeline in `joshlf/anneal` at
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)` shows that there is no `Prog.lean`
artifact. Instead, `capture_crate_with_options`
(`trusted/rustc-capture/src/lib.rs:577-680`) parses textual MIR into a Rust
vector `Vec<CapturedFunction>` (each already lowered in Rust to `Vec<X86Block>`
via `lower_block` and `lower_rvalue` at lines 1123–1433) and feeds that slice
into two unlinked Rust string formatters:

1. `render_mir_lean_with_metadata(&functions, &meta)` (`lib.rs:1435-1561`),
   which writes `.anneal/Mir.lean` containing `def <fn>_body : Trusted.X86Body`
   and `def crate : Trusted.Crate` (with
   `tcb := [Trusted.TCBItem.assemblerLowering "<fn>" <fn>_body]`), and
2. `render_x86_assembly(&functions)` (`lib.rs:1589-1820`), which writes
   `.anneal/Prog.s` containing `.intel_syntax noprefix` GNU assembly text.

When `cargo-anneal` runs (`trusted/cargo-anneal/src/lib.rs:341-425`), it runs
`lake build Proof` (compiling `.anneal/Proof.lean` generated by
`render_proof_lean` in `trusted/rustc-capture/src/proof_gen.rs:42-201`) and
then invokes `anneal-audit` (`trusted/audit/src/lib.rs:1494-1658`) and
`TrustedBoundary.lean` (`trusted/audit/TrustedBoundary.lean:900-974`). Neither
`anneal-audit` nor `TrustedBoundary.lean` ever opens, hashes, or inspects
`.anneal/Prog.s`. In `Trusted/X86Semantics.lean:706-770`, `TargetArtifact` is
defined as a trivial unit wrapper
(`structure TargetArtifact where unit : Unit := ()`) and
`opaque assemble : X86Body → TargetArtifact := fun _ => { unit := () }`.

This pipeline has two structural soundness defects.

##### Defect 3.1: Discrepancies Between `Mir.lean` and `Prog.s`

`Basis: source`

Because `CapturedFunction::to_lean` (`lib.rs:334-465`) and
`render_x86_assembly` (`lib.rs:1589-1820`) are independent Rust code paths over
`CapturedFunction`, they disagree on four constructs in commit
`24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`:

| Construct in `trusted/rustc-capture/src/lib.rs` (`the MIR-to-x86-64 codegen prototype (`support/`)`) | What `render_mir_lean_with_metadata` Emits into `.anneal/Mir.lean` & How `X86Semantics.lean` Models It | What `render_x86_assembly` Emits into `.anneal/Prog.s` & What the CPU Executes | Soundness Impact |
| :--- | :--- | :--- | :--- |
| **`CapturedTerminator::Panic`** | Emits `Trusted.X86Term.abortPanic` (`lib.rs:422`). `X86Semantics.lean:410` (`execTerm`) models `.abortPanic` as `pure (.terminated .unwind s)`, which satisfies `SafeOutcome` (`X86Semantics.lean:486-490`: `.terminated .unwind _ => True`). | `lib.rs:1756-1758` merges `CapturedTerminator::Unreachable \| CapturedTerminator::Panic => writeln!(out, "    ud2")`! | **Unsoundness on panic paths:** Any function that panics (such as `assert!(x != 0)`) is verified in Lean as safely unwinding (`.terminated .unwind`), while `.anneal/Prog.s` executes `ud2` (`SIGILL` illegal instruction trap) instead of `call abort`. |
| **`CapturedTerminator::CallSizeOf { dst, ty, target }`** | Emits `Trusted.X86Term.movSizeOfJmp ⟨dst⟩ ty ⟨target⟩` (`lib.rs:433`). `X86Semantics.lean:419-424` writes `evalX86TyByteSize s.tySizes ty` (`0` for `unit`, `1` for `bool`, `8` for `usize`, `tySizes idx` for `param idx`). | `lib.rs:1773-1780` ignores `ty` (`let _ = ty;`) and unconditionally emits `mov QWORD PTR [rbp - {dst_off}], 8`! | **Wrong runtime value for `size_of::<T>()`:** For `bool`, `()`, or any generic `T` with `size_of::<T>() != 8`, Lean proves correctness assuming `size_of` returns `0`, `1`, or `tySizes idx`, while `.anneal/Prog.s` hardcodes `8`. |
| **`CapturedTerminator::CallTransmuteCopy { src_ptr, dst, src_ty, dst_ty, target }`** | Emits `Trusted.X86Term.repMovsbJmp ⟨src_ptr⟩ ⟨dst⟩ src_ty dst_ty ⟨target⟩` (`lib.rs:442`). `X86Semantics.lean:426-447` checks `n = evalX86TyByteSize s.tySizes dst_ty` and copies `n` bytes (`0`, `1`, `8`, or `tySizes idx`). | `lib.rs:1782-1796` ignores `src_ty` and `dst_ty` (`let _ = (src_ty, dst_ty);`) and unconditionally emits an 8-byte load/store (`mov rax, QWORD PTR [rsi]; mov QWORD PTR [rbp - {dst_off}], rax`)! | **Out-of-bounds 8-byte read on `<8`-byte `transmute_copy`:** For a 1-byte `bool` or 0-byte `()`, Lean verifies a 1-byte or 0-byte read, while `.anneal/Prog.s` performs an 8-byte `QWORD PTR [rsi]` read past the allocation. |
| **64-bit Arithmetic & Shifts (`evalX86BinOp`)** | `X86Semantics.lean:207-216` models `add`, `sub`, `mul`, `shl`, and `shr` over unbounded Lean `Nat`: `a + b`, `a - b` (saturating at `0` when `a < b`), `a * b`, `a <<< b` (unmasked), `a >>> b` (unmasked). | `lib.rs:1707-1725` emits 64-bit modular `add rax, rcx`, `sub rax, rcx` (wrapping modulo $2^{64}$, so `0 - 1 = UINT64_MAX`), `imul rax, rcx`, and `shl rax, cl` / `shr rax, cl` (which mask `cl` by `0x3f`, so `1ULL << 65 == 2ULL`). | **Semantic model mismatch between `X86Semantics.lean` and hardware ISA:** Proofs in Lean reason about saturating `Nat` subtraction and unmasked `Nat` shifts, whereas the emitted instructions wrap modulo $2^{64}$ and mask shift counts modulo 64. |

##### Defect 3.2: Unverified Rust Lowering and Bypassable `compileStage0`

`Basis: source + execution`

In `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`, `.anneal/Mir.lean` does not
contain `MirBody`; it contains `Trusted.X86Body` lowered by Rust code in
`trusted/rustc-capture/src/lib.rs:1123-1433`. Although
`theory/Anneal/MirLemmas.lean` (lines 448 and 761) defines
`idCopyBody : X86Body := compileStage0 idCopyMirBody` so that auto-generated
proofs check `compileStage0 idCopyMirBody = Mir.id_body` by definitional
equality (`rfl`), `Mir.crate` itself records only `X86Body`. Consequently:

1. **Custom proofs (`--keep-proof`) can bypass `compileStage0` and `MirSem`
   entirely:** A user-supplied `Proof.lean` only has to prove
   `Trusted.CrateTheorem Mir.crate` over the `X86Body` terms in `Mir.lean`.
   Nothing in `Trusted.CrateTheorem` or `TrustedBoundary.lean` requires
   `compileStage0` (or any `MirBody`) to appear in the proof.
2. **In-Lean optimizations (`theory/Anneal/Compiler/Peephole.lean`) cannot be
   reflected in `Prog.s`:** `Peephole.lean` defines
   `optimizePeephole : X86Body → X86Body` and proves `optimizePeephole_sound`.
   Because `.anneal/Mir.lean` and `.anneal/Prog.s` are emitted by
   `anneal-rustc-capture` before Lean runs, applying `optimizePeephole` inside
   Lean causes `optimizePeephole (compileStage0 ...)` to no longer be
   definitionally equal to the unoptimized `Mir.<fn>_body` in `Mir.lean`, while
   `.anneal/Prog.s` remains unoptimized.
3. **`Peephole.lean` uses `WellFounded.fix` recursion that blocks kernel `rfl`
   reduction:** In `theory/Anneal/Compiler/Peephole.lean:18-26`,
   `peepholeInstrs` recurses on `peepholeInstrs (i1 :: rest)` and
   `peepholeInstrs (i2 :: rest)`. Executing this pattern in Lean `v4.34.1`
   compiles via `WellFounded.fix`, which hits `maximum recursion depth has been
   reached` when reduced by `rfl`. Rewriting `peepholeInstrs` via
   `List.foldr peepholeStep []` (lines 229–240 of
   `support/artifact_binding_probe/SingleSourceCodegen.lean`) uses primitive
   structural recursion (`List.rec`) and reduces by `rfl` inside the Lean
   kernel.

#### 4. Single-Source Artifact Binding Architecture and Prototype Evaluation

`Basis: source + execution + derived`

To eliminate both the shadow-artifact gap between `Mir.lean` and `Prog.s` and
the unverified Rust MIR-to-x86 lowering, two candidate single-source artifact
binding mechanisms were evaluated:

- **Mechanism (i) — In-Lean Total Deterministic `.s` Serializer
  (`Trusted.emitX86CrateAsm : X86Crate → String`) + Kernel/Auditor Binding:**
  1. `anneal-rustc-capture` emits **only** captured `MirBody` definitions into
     `.anneal/Mir.lean` (`Mir.crate : Trusted.MirCrate`). All Rust-side x86
     lowering (`lower_block`, `lower_rvalue`, `render_x86_assembly`) is deleted
     from `trusted/rustc-capture`.
  2. In `theory/Anneal/Compiler/`, Lean functions compile and optimize
     `Mir.crate` into `Prog.x86Crate : Trusted.X86Crate`
     (`compileAndOptimizeCrate Mir.crate`).
  3. `trusted/lean/Trusted/X86Emit.lean` defines a pure, total, structural
     serializer `Trusted.emitX86CrateAsm : Trusted.X86Crate → String`.
  4. During build and verification, Lean writes `.anneal/Prog.s` by evaluating
     `Trusted.emitX86CrateAsm Prog.x86Crate`.
  5. During `anneal-audit`, `TrustedBoundary.lean` enforces byte-for-byte
     identity between the kernel-verified `Prog.x86Crate` and `.anneal/Prog.s`
     on disk via one of two sub-variants:
     - **Sub-variant (i-a) (`CrateTheorem` `rfl` commitment + `.olean` string
       literal check):** `Trusted.CrateTheorem mc xc asmText` includes the
       field `asm_eq : Trusted.emitX86CrateAsm xc = asmText`, which the Lean 4
       kernel verifies by `rfl` during `Environment.replay`.
       `TrustedBoundary.lean` then inspects `env.find? ``Prog.asmText`, checks
       that its value is a raw string literal
       `Lean.Expr.lit (.strVal committedAsm)`, and verifies
       `committedAsm == (← IO.FS.readFile progSPath)`.
     - **Sub-variant (i-b) (Post-replay `X86Crate` AST decoding in
       `TrustedBoundary.lean`):** After `Environment.replay` verifies
       `Proof.verify_crate : Trusted.CrateTheorem Mir.crate Prog.x86Crate`,
       `TrustedBoundary.lean` decodes the closed `X86Crate` term from the
       replayed kernel `Environment` (extending `checkTargetConstants` at
       `TrustedBoundary.lean:622-720`), evaluates
       `Trusted.emitX86CrateAsm decodedCrate` directly inside the auditor, and
       verifies
       `Trusted.emitX86CrateAsm decodedCrate == (← IO.FS.readFile progSPath)`.
- **Mechanism (ii) — Rust-Side `.s` Emitter with `.olean` AST Round-Trip
  Check:**
  `anneal-rustc-capture` continues to emit `.anneal/Prog.s` in Rust, and
  `anneal-audit` reconstructs the `X86Crate` AST from `.olean` in Rust (or
  parses `.anneal/Prog.s` back into `X86Crate`) to check equivalence.

| Evaluation Criterion | Mechanism (i-a): In-Lean `emitX86CrateAsm` + Kernel `rfl` on `Prog.asmText` | Mechanism (i-b): In-Lean `emitX86CrateAsm` + Auditor AST Evaluation | Mechanism (ii): Rust Emitter + `.olean` AST Round-Trip Check |
| :--- | :--- | :--- | :--- |
| **Number of `.s` assembly printers in repository** | **1** (`Trusted/X86Emit.lean`) | **1** (`Trusted/X86Emit.lean`) | **2** (one in Rust `rustc-capture`, one in Lean/Rust auditor) |
| **Supports in-Lean verified optimization passes (`Peephole.lean`) without Rust duplication** | **Yes** (`Prog.x86Crate := compileAndOptimizeCrate Mir.crate`) | **Yes** (if `Prog.x86Crate` is stored as a concrete AST or reduced in auditor) | **No** (unless every Lean optimization pass is duplicated in Rust `rustc-capture`) |
| **New lines of code in `trusted/audit/TrustedBoundary.lean`** | **~15 LOC** (match `Expr.lit (.strVal committedAsm)` on `Prog.asmText` and compare to `IO.FS.readFile`) | **~90 LOC** (structural `Expr` decoders for `X86Crate`, `X86Body`, `X86Instr`, `X86Term`) | **~250+ LOC** (full `X86Body` binary `.olean` decoder or `.s` assembly parser in `trusted/audit/src/lib.rs`) |
| **Kernel reduction scaling on large crates** | In Lean `v4.34.1`, `String` is `ByteArray` (`List UInt8`); `rfl` on a single `N`-byte `String` takes `~2N` defeq steps (requiring `set_option maxRecDepth` or per-function/per-line `List String` equality for large functions). | **O(1) in kernel** (no `String` equality inside the kernel; `TrustedBoundary.lean` runs compiled `Trusted.emitX86CrateAsm` in native code after `replay`). | **O(1) in kernel**, but shifts complexity into effectful Rust `.olean` parsing. |

Mechanism (i) establishes `Trusted.emitX86CrateAsm : Trusted.X86Crate → String`
in `trusted/lean/Trusted/` as the single assembly emitter in Anneal. Sub-variant
(i-a) is mechanized end-to-end in
`support/artifact_binding_probe/SingleSourceCodegen.lean` and
`support/artifact_binding_probe/AuditMain.lean`: `SingleSourceCodegen.lean`
compiles a `MirCrate` to `X86Crate`, runs `optimizePeephole`, proves
`CrateTheorem Mir.crate Prog.x86Crate Prog.asmText` with
`-Ddebug.skipKernelTC=false`, emits `Prog.s`, verifies acceptance of genuine
`Prog.s` and rejection of tampered `Prog_tampered.s`, and executes the
assembled function on the x86-64 CPU.

## Boundaries

### Part I — Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Call Verification

1. **Trait implementations of exported/foreign traits on completely unexposed
   private types (Category 4d) — conservative over-approximation:**
   Rule 4 of `is_external_entry_fn` marks `<UnexportedPrivStruct as
   PubTrait>::cat4_trait_req` as an external entry point whenever `PubTrait` is
   foreign or `Level::Reachable`, even if `UnexportedPrivStruct` is never
   returned via `impl PubTrait`, coerced to `dyn PubTrait`, or passed to a
   generic function. Excluding such dead trait `impl`s would require whole-crate
   MIR scanning for `PointerCoercion::Unsize` and generic instantiations;
   treating every implementation of a public or foreign trait as a public
   contract obligation is sound and conservative.
2. **Closures escaping via function-pointer or `dyn Fn` coercion — not covered
   by `Level::ReachableThroughImplTrait` alone:**
   Rule 5 of `is_external_entry_fn` identifies closures that escape via RPIT
   (`impl Fn(...)`) using `Level::ReachableThroughImplTrait` gated by
   `is_external_entry_fn(tcx, root_owner)`. If a closure inside a public
   function escapes instead by coercion to a bare `fn(...)` pointer or `&dyn
   Fn(...)` trait object without an `OpaqueTy` in the return signature, its
   `FnOnce::call_once` / `Fn::call` body is reached via vtable or indirect
   function-pointer call rather than `Level::ReachableThroughImplTrait`.
   Indirect and dynamic-dispatch calls (`TerminatorKind::Call` where `func` is a
   non-constant `Operand` or a `Virtual` instance) are **not examined** in
   `support/InterproceduralConditionalMir.lean`, which resolves static callee names in
   `CrateEnv`.
3. **Fuel-bounded recursion and mutual recursion in `CompileAdmitted` and Mode A
   inlining:**
   Both `CompileAdmitted env fuel body` and Mode A `computePlan` use explicit
   `Nat` fuel bounds. For non-recursive call graphs (DAGs), finite fuel is
   exact; for recursive or mutually recursive functions, Mode A symbolic
   inlining cannot unroll unboundedly and must yield to Mode B modular
   summaries (`callFuel = 0`) paired with an inductive termination or rank
   argument.

### Part II — Exhaustive rustc Obligation Inventory and Single-Source x86-64 Artifact Binding

- **Known not to apply:**
  - `ty::Instance::resolve_drop_glue(tcx, ty)` is **known not to apply** to
    uninstantiated polymorphic `Ty<'tcx>` values (`requires_monomorphization`):
    `rustc` asserts monomorphic types inside `resolve_drop_glue`
    (`compiler/rustc_middle/src/ty/instance.rs:168-170`).
  - `tcx.mir_for_ctfe(def_id)` is **known not to apply** to trivial constants
    where `tcx.is_trivial_const(local_def_id)` is `true`
    (`compiler/rustc_mir_transform/src/lib.rs:493`); callers must branch on
    `tcx.is_trivial_const` and use `tcx.trivial_const(local_def_id)` first.
  - `body.mentioned_items()` is **known not to apply** to `mir_for_ctfe` bodies
    (`Const`, `AssocConst`, `Static`, `AnonConst`) because the `MentionedItems`
    pass runs only inside `inner_optimized_mir`
    (`compiler/rustc_mir_transform/src/lib.rs:810`).
- **Unsupported:**
  - Both examined Anneal revisions (`5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`
    and `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`) leave `unsafeImpls`
    **unsupported** in `trusted/rustc-capture/src/lib.rs`, emitting `[]` by
    default.
- **Not examined:**
  - Polymorphic drop-shim extraction via
    `rustc_mir_transform::build_drop_shim`
    (`compiler/rustc_mir_transform/src/lib.rs:56`) versus post-monomorphization
    reachability traversal for generic ADTs was **not examined** experimentally
    in `support/obligation_inventory_probe/`.
  - Migrating `Trusted/X86Semantics.lean` from unbounded `Nat` arithmetic to
    64-bit modular `UInt64` / `BitVec 64` across the full `MirLemmas.lean` and
    `NaiveCodegen.lean` proof suite was **not examined** beyond the standalone
    `UInt64` mechanization in
    `support/artifact_binding_probe/SingleSourceCodegen.lean`.

## Evidence

### Part I — Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Call Verification

#### Preserved Package Artifacts

- **[`support/ConditionalCrateVerification.lean`](support/ConditionalCrateVerification.lean)**
  (`3,517` lines, SHA-256
  `7ca6ddc28189eb03fa389526114e11705f2cbf755888498ce905e990d09af2f4`):
  Standalone Lean `v4.34.1` mechanization of the 3-level calling-condition
  taxonomy (`initMirState`, `MirLang.SpecOn`, `MirLang.WellFormedOn`),
  impossibility of unconditional `MirLang.Spec` (`not_le_spec_of_not_defined`,
  `addBody_not_le_spec`), conditional `FunctionalTranslation` bridges
  (`funcSem_le_specOn`, `π_func_specOn_le`), spine-preserving `evalPureCallee2`,
  `CalleeSummaryVerified`, multi-function crates (`prove_guarded_crate`,
  `prove_mixed_crate`), and Mode 2 unwinding semantics (`MirLangUnwind`,
  `addBody_satisfies_ensuresUnwind`, `addBody_satisfies_wellFormedUnwind`).
- **[`support/InterproceduralConditionalMir.lean`](support/InterproceduralConditionalMir.lean)**
  (`4,149` lines, SHA-256
  `b09d995045d58b9f91f30838364bb82adffa995e84b7a2641ff5f1d68c2d8374`):
  Standalone Lean `v4.34.1` mechanization of call-stack `Terminator.call` and
  `Terminator.return_` over `CrateEnv` and `MirState.frames : List CallFrame`,
  Layer 1B structural health theorems (`mirMachine_totalStep`,
  `mirMachine_inhabitedDemonic`, `mirMachine_non_vacuity_at_every_depth`),
  transitive `CompileAdmitted` and executable `checkCompileAdmitted` over
  `requiredConsts` and `mentionedItems`
  (`compileAdmitted_of_checkCompileAdmitted`), dead-branch PME negative control
  (`deadBranchBadCaller_not_compileAdmitted`,
  `deadBranchBadCaller_runtime_verified`), and unified dual-mode symbolic
  evaluation (`evalSymState_sound`, `ReturnCont`, Mode A
  `prove_guarded_crate_modeA`, Mode B `prove_modular_crate_modeB`, and
  `evalSymState_doubleGuarded_modeA_eq_modeB`).
- **[`support/vis_probe/src/lib.rs`](support/vis_probe/src/lib.rs)** (`261` lines, SHA-256
  `87769081314d234bc7d4034833a11ab87eb0d7b9d36502cc205c6189a33ddbb0`):
  7-category Rust visibility test fixture covering top-level items, private and
  re-exported modules, inherent methods on public/private/leaked structs, trait
  implementations (direct, RPIT `impl Trait`, `&'static dyn Trait`, unexported
  private structs, private traits), generic functions and private helpers called
  by generics, FFI roots (`#[no_mangle]`, `#[export_name]`, `main`), and
  closures.
- **[`support/vis_probe/driver.rs`](support/vis_probe/driver.rs)** (`183` lines, SHA-256
  `3df79cd45b7506cf9f2c2d01995687805b74026d2a21716b1d81278d8279789e`):
  In-process `rustc_driver` probe inspecting `tcx.mir_keys(())`,
  `tcx.hir_body_owners()`, `tcx.local_visibility`,
  `tcx.effective_visibilities(())` at all four `Level`s,
  `tcx.reachable_set(())`, `tcx.codegen_fn_attrs`, `tcx.entry_fn(())`, and
  `tcx.collect_and_partition_mono_items(())`.
- **[`support/vis_probe/driver_lib.txt`](support/vis_probe/driver_lib.txt)** (`71` lines,
  SHA-256
  `6e0931ebef4b4ea6899b608c4ea2a63dfa305d46f074ad63ae0e06cd5e43a136`) and
  **[`support/vis_probe/driver_bin.txt`](support/vis_probe/driver_bin.txt)** (`71` lines,
  SHA-256
  `d5fc8856f5d2c123623adf75484f8c3d97615f2c3ce17592c33cc34dfe2aacbf`):
  Recorded outputs of `support/vis_probe/driver.rs` on `support/vis_probe/src/lib.rs` with
  `--crate-type=lib` and `--crate-type=bin`.

#### Primary Upstream Sources

- **`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`:**
  - [`compiler/rustc_mir_transform/src/lib.rs (lines 325-358)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs):
    `mir_keys` query implementation.
  - [`compiler/rustc_middle/src/hir/mod.rs (lines 37-115)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/mod.rs)
    and
    [`compiler/rustc_middle/src/hir/map.rs (lines 1265-1324)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/hir/map.rs):
    `ModuleItems`, `hir_body_owners`, and `local_visibility`.
  - [`compiler/rustc_middle/src/middle/privacy.rs (lines 20-289)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/middle/privacy.rs),
    [`compiler/rustc_resolve/src/effective_visibilities.rs (lines 27-202)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_resolve/src/effective_visibilities.rs),
    and
    [`compiler/rustc_privacy/src/lib.rs (lines 510-828)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs),
    [` (lines 1809-1855)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_privacy/src/lib.rs):
    `EffectiveVisibilities`, `Level`, `EmbargoVisitor`, and the
    `krate.opaques()` `FIXME` at ` (lines 1841-1846)`.
  - [`compiler/rustc_passes/src/reachable.rs (lines 177-209)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs)
    and
    [` (lines 411-524)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_passes/src/reachable.rs):
    `reachable_set` implementation.
  - [`compiler/rustc_monomorphize/src/collector.rs (lines 1364-1389)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs)
    and
    [` (lines 1751-1778)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs):
    `collect_items_of_instance` (`required_consts`, `mentioned_items`) and
    `RootCollector::is_root`.
  - [`compiler/rustc_middle/src/mir/pretty.rs (lines 326-329)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs),
    [` (lines 679-722)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs),
    and
    [`compiler/rustc_middle/src/mir/syntax.rs (lines 696-784)`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs):
    `write_mir_pretty`, `write_mir_sig`, `TerminatorKind::Call`, and
    `TerminatorKind::Return`.

### Part II — Exhaustive rustc Obligation Inventory and Single-Source x86-64 Artifact Binding

#### Primary Git and Toolchain Sources

- **`joshlf/anneal` at `5fc1139f2208b3c9cfb513573c4a731cc32bb457 (with `StepResult` / `MirSemantics` prototype definitions inlined above and preserved in `support/`)`:**
  - `trusted/rustc-capture/src/lib.rs`: lines 399–550
    (`capture_crate_with_options`, `parse_source_metadata`), lines 568–863
    (`parse_emitted_mir_with_metadata`, `parse_fn_header`, `NonZeroUsize`
    hardcoding), lines 1062–1071 (`pme_assert_const` hardcoding), and lines
    1250–1315 (`render_mir_lean_with_metadata`, omission of `unsafeImpls`).
  - `trusted/rustc-capture/src/proof_gen.rs`: lines 51–132
    (`render_proof_lean`, fixed 1/2/3-function template dispatch).
  - `trusted/lean/Trusted/MirSemantics.lean`: lines 768–845 (`FnKind`,
    `AdmissibleAdtInv`, `UnsafeImplObligation`, `Crate`, `CrateTheorem`).
- **`joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f (evaluating the MIR-to-x86-64 codegen prototype preserved in `support/`)`:**
  - `trusted/rustc-capture/src/lib.rs`: lines 334–465
    (`CapturedFunction::to_lean`), lines 577–680 (`capture_crate_with_options`
    dual emission of `Mir.lean` and `Prog.s`), lines 745–795
    (`parse_source_metadata`), lines 1123–1433 (unverified Rust MIR-to-x86
    lowering), lines 1435–1561 (`render_mir_lean_with_metadata`), and lines
    1589–1820 (`render_x86_assembly`, specifically lines 1756–1758 for
    `Panic => ud2`, lines 1773–1780 for `CallSizeOf => 8`, and lines 1782–1796
    for `CallTransmuteCopy => 8-byte mov`).
  - `trusted/rustc-capture/src/proof_gen.rs`: lines 42–201
    (`render_single_fn_proof_term`, `render_proof_lean` emitting
    `theorem verify_crate : Trusted.CrateTheorem Mir.crate` with no binding to
    `.anneal/Prog.s`).
  - `trusted/lean/Trusted/X86Semantics.lean`: lines 207–216 (`evalX86BinOp` on
    `Nat`), lines 408–448 (`execTerm` for `abortPanic`, `movSizeOfJmp`,
    `repMovsbJmp`), and lines 706–875 (`TargetArtifact`, `opaque assemble`,
    `CrateTheorem`).
  - `trusted/audit/TrustedBoundary.lean`: lines 622–720
    (`checkTargetConstants`) and lines 900–974 (`runAudit`).
  - `trusted/audit/src/lib.rs`: lines 1494–1658 (`run_audit`).
  - `theory/Anneal/Compiler/NaiveCodegen.lean`: lines 201–209
    (`compileStage0`).
  - `theory/Anneal/Compiler/Peephole.lean`: lines 18–30 (`peepholeInstrs`) and
    lines 84–140 (`optimizePeephole`, `optimizePeephole_sound`).
  - `theory/Anneal/MirLemmas.lean`: lines 448 and 761 (`idCopyBody`,
    `binOpBody`).
- **`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc
  1.99.1`):**
  - `compiler/rustc_hir/src/def.rs`: lines 100–204 (`DefKind`).
  - `compiler/rustc_middle/src/ty/mod.rs`: lines 298–305 (`ImplTraitHeader`).
  - `compiler/rustc_middle/src/ty/generics.rs`: lines 121–382 (`Generics`) and
    lines 385–460 (`GenericClauses`, `tcx.clauses_of`).
  - `compiler/rustc_middle/src/ty/instance.rs`: lines 33–198 (`Instance`,
    `InstanceKind`, `ShimKind`) and lines 562–851 (`Instance::try_resolve`,
    `Instance::resolve_drop_glue`, `Instance::fn_once_adapter_instance`).
  - `compiler/rustc_middle/src/mir/mod.rs`: lines 265–285 (`required_consts`,
    `mentioned_items`) and lines 717–750 (`Body::required_consts`,
    `Body::mentioned_items`).
  - `compiler/rustc_mir_transform/src/lib.rs`: lines 327–358 (`mir_keys`),
    lines 432–532 (`mir_promoted`, `mir_for_ctfe`), lines 537–685
    (`mir_drops_elaborated_and_const_checked`,
    `run_analysis_to_runtime_passes`), and lines 778–824 (`optimized_mir`,
    `MentionedItems`).
  - `compiler/rustc_interface/src/passes.rs`: lines 1154–1282
    (`run_required_analyses`, `analysis`).

#### Preserved Package Support Artifacts

All executable probes and golden outputs are preserved under `support/` inside
this package directory (observed on `2026-10-31`):

| Package Relative Path | Lines | SHA-256 Digest | Role |
| :--- | ---: | :--- | :--- |
| `support/obligation_inventory_probe/driver.rs` | 344 | `c57203d0d5a407d764b5bccaa4ef44ab61b888e4ae7a1eab5568e608c2952109` | `rustc_driver` `Callbacks` harness querying `TyCtxt` in `rustc 1.99.1` |
| `support/obligation_inventory_probe/src/lib.rs` | 241 | `56608b737fce68d485cacc62a611db230f7291f68cf6b9407fbc658743114c6b` | Target Rust crate exercising all five obligation categories (a)–(e) |
| `support/obligation_inventory_probe/output.txt` | 124 | `98476f987b2c323d1425cb781f0e0fc92ae6b65e2805de04fa22bc7707b10269` | Captured stdout of `obligation_inventory_probe` on `src/lib.rs` |
| `support/artifact_binding_probe/SingleSourceCodegen.lean` | 309 | `2180538f940e3ad65200ad48cbb6b605da161246105ffb88b5c4fc146d4ff972` | Lean 4 (`v4.34.1`) mechanization of `MirCrate → X86Crate → emitX86CrateAsm` and `Proof.verify_crate` |
| `support/artifact_binding_probe/AuditMain.lean` | 64 | `32ab7bca619bb5a4162dacdc11d3454855c347e6adc407b08ae42f8bf8e5c071` | `.olean` environment inspector verifying `Proof.verify_crate` and `Prog.asmText == diskAsm` |
| `support/artifact_binding_probe/main.c` | 21 | `51b03421d87457ebd41a20a0dfcf169f7e57c720f648d1a5af774ba8370845cc` | C test harness calling `anneal_double_u64` in `Prog.s` |
| `support/artifact_binding_probe/run_probe.sh` | 41 | `aca8ce388b30a0e3aa46881fbe3642b1363afe93c2c08b942fad08b14e0a4580` | End-to-end verification, tamper-rejection, assembly, and CPU execution script |
| `support/artifact_binding_probe/Prog.s` | 20 | `43004780607d2288338789a217ec11edf96a2b8ded5bbb7dbb76b7a1841cc3a1` | x86-64 assembly emitted by `Trusted.emitX86CrateAsm Prog.x86Crate` |
| `support/artifact_binding_probe/output.txt` | 10 | `e72e34a962e649521d2a6b0cba52a6da308347a703b4b3bfe71f86751c93ebb3` | Captured stdout of `run_probe.sh` |

## Revalidation

### Part I — Public MIR Discovery, Conditional Specifications, and Dual-Mode Interprocedural Call Verification

1. **Revalidating the Lean `v4.34.1` Mechanizations:**
   Run the Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel
   with asynchronous elaboration and kernel type-checking skip disabled on both
   preserved files from the package directory:

   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/ConditionalCrateVerification.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/InterproceduralConditionalMir.lean
   ```

   Both commands must exit with status `0`, zero warnings, and `#print axioms`
   outputs depending only on subsets of `{propext, Quot.sound}` (with zero
   `sorryAx`, zero `Lean.ofReduceBool`, and zero `Classical.choice`).

2. **Revalidating the `rustc_driver` Visibility Probe on a Newer Rust
   Toolchain:**
   Compile [`support/vis_probe/driver.rs`](support/vis_probe/driver.rs) against the target
   toolchain's `rustc_private` sysroot and execute it on
   [`support/vis_probe/src/lib.rs`](support/vis_probe/src/lib.rs) in both library and binary
   modes:

   ```console
   SYSROOT=$(rustc --print sysroot)
   rustc --edition=2021 support/vis_probe/driver.rs \
     --sysroot "$SYSROOT" \
     -L "$SYSROOT/lib" \
     -o ./vis_probe_driver
   LD_LIBRARY_PATH="$SYSROOT/lib" ./vis_probe_driver \
     --edition=2021 --crate-type=lib support/vis_probe/src/lib.rs > ./driver_lib.txt
   LD_LIBRARY_PATH="$SYSROOT/lib" ./vis_probe_driver \
     --edition=2021 --crate-type=bin support/vis_probe/src/lib.rs > ./driver_bin.txt
   diff -u support/vis_probe/driver_lib.txt ./driver_lib.txt
   diff -u support/vis_probe/driver_bin.txt ./driver_bin.txt
   ```

   Also inspect `compiler/rustc_privacy/src/lib.rs` around `krate.opaques()` to
   check whether the upstream `FIXME` on `Level::ReachableThroughImplTrait` or
   trait-impl visibility propagation in `EmbargoVisitor` has changed.

### Part II — Exhaustive rustc Obligation Inventory and Single-Source x86-64 Artifact Binding

Revalidate this report's claims whenever:

1. Anneal updates its pinned `rustc` toolchain from `1.99.1`
   (`58cf8f9c35b355199727627d07ae34a4e2846d67`), which may alter internal
   `rustc_middle::ty` or `rustc_mir_transform` query signatures (`clauses_of`,
   `impl_trait_header`, `Instance::resolve_drop_glue`,
   `mir_drops_elaborated_and_const_checked`).
2. Anneal updates its pinned Lean 4 toolchain from `v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`), which may change `String` /
   `ByteArray` kernel reduction behavior or `Lean.Environment` constant
   representations.
3. `trusted/rustc-capture`, `trusted/lean/Trusted/`, or
   `trusted/audit/TrustedBoundary.lean` is modified.

To rerun both preserved probes from this package directory:

```bash
  # 1. Re-run the rustc_driver obligation inventory probe
SYSROOT="$(rustc +stable --print sysroot)"
RUSTC_BOOTSTRAP=1 rustc +stable --edition=2021 \
  support/obligation_inventory_probe/driver.rs \
  -o ./obligation_inventory_driver \
  -C link-args="-Wl,-rpath,$SYSROOT/lib"
RUSTC_BOOTSTRAP=1 ./obligation_inventory_driver \
  --crate-type=lib --edition=2024 \
  support/obligation_inventory_probe/src/lib.rs
rm -f ./obligation_inventory_driver

  # 2. Re-run the Lean 4 + x86-64 single-source artifact binding probe
LEAN="${LEAN:-lean}" ./support/artifact_binding_probe/run_probe.sh
```
