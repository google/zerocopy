# Certificate-Checked CFG Structuring via Beyond Relooper and SESE Trees, and Rust `Runtime(PostCleanup)` MIR Idiom Resugaring

## Summary

Verifying idiomatic Rust inside Anneal's zero-TCB `theory/` layer (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) hits two bottlenecks on `MirPhase::Runtime(RuntimePhase::PostCleanup)` MIR:

1. **Unstructured CFGs under Strict Pass-1 Lean Rules:** Rust `?` early returns, pattern matches, drop elaboration, and `for` loops expand into flat `Trusted.MirAst.Body.basicBlocks` graphs (10–35 blocks) linked by `TerminatorKind.{goto, switchInt, call, assert, unwindResume}`. On `c131b320eeeb...`, `Anneal.PureLift.MirBridge.liftStraightLineMir` handles only single-block bodies (`theory/Anneal/PureLift/MirBridge.lean#L63-L79`), while `Anneal.PureLift.BlockCfg` (`theory/Anneal/PureLift/BlockCfg.lean#L25-L34, #L155-L199`) demands raw `BasicBlockId` VCs or manual `FlowPlan.whileLoop` plans. Simultaneously, `trusted/audit/TrustedBoundary.lean#L442-L596, #L1108-L1153` restricts `theory/` to `prelude` + 51 `Init.*` modules, forbids `partial`, `unsafe`, `termination_by`, and metaprogramming, and rejects compiler-emitted `._unsafe_rec` helpers (`Trusted/MirAst.lean#L77-L82`), ruling out in-Lean dominator computation.
2. **Pre-Optimization Desugaring in `Runtime(PostCleanup)`:** `compiler/rustc_mir_transform/src/lib.rs#L605-L720` in `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) shows that **`Inline` and `ForceInline` have not yet run at `Runtime(PostCleanup)`** (they execute later in `run_optimization_passes`). Thus `?` and `for` stay explicit multi-block `Call` + `SwitchInt` idioms paired with `ElaborateDrops` boolean drop-flag ladders (`DropStyle::{Dead, Static, Conditional, Open}`).

Four findings resolve both bottlenecks at zero TCB cost:

- **Decoupled Certificate-Checked `CfgTree`:** Dominator-tree structuring (Norman Ramsey's *Beyond Relooper*, ICFP 2022, DOI `10.1145/3547621`) and SESE / Program Structure Tree (PST) decomposition (Johnson, Pearson, and Pingali, PLDI 1994, DOI `10.1145/178243.178258`) run outside Lean. Inside `theory/`, a single-pass `@CfgTree.rec` validator checks exact CFG bisimulation (`validateCfg`) with loop-head invariant/rank cutpoints, keeping `Trusted.*` untouched under Statement-Origin Separation.
- **Hybrid Scope Geometry:** Pure SESE hammocks isolate single-entry/single-exit frames (`P2`), yet early `?` returns and `UnwindAction::Cleanup` edges pierce SESE exits and coarsen regions. Beyond Relooper eliminates code duplication on reducible multi-exit CFGs via De Bruijn `seq`/`loop`/`br` scopes sorted by reverse postorder (`rpnum`), while nested `seseRegion` nodes bound pure 1-entry/1-exit hammocks.
- **`ControlFlow` Variant Inversion & Drop Flags:** `library/core/src/ops/control_flow.rs#L89-L101` declares `Continue` at `VariantIdx(0)` and `Break` at `VariantIdx(1)` (opposite `<B, C>`), making `Result::branch` discriminant-preserving while inverting `Option` (`None` 0 $\to$ `Break` 1, `Some` 1 $\to$ `Continue` 0). Dynamic `bool` drop flags are allocated iff `maybe_init && maybe_uninit` hold at a `Drop` (`elaborate_drops.rs#L303-L315`), initialized `false` at `Location::START`, set post-call under `Cleanup` vs pre-call otherwise, and never reset along `is_cleanup` paths (`elaborate_drop.rs#L1544-L1548`).
- **Anti-Laundering Guards & `Trusted.*` Gaps:** Backward transport (`Safe(Resugared) ⟹ Safe(MIR)`) must enforce guards ($\Phi_{\text{no-erased-UB}}$) preserving `Operand.move` deinitialization (`deinitMovedPlace = true`), drop-flag definiteness, unwind edges, and valid tags before `Downcast`. On `joshlf/anneal@c131b320eeeb...`, full `?`/iterator/drop resugaring exposes four concrete `Trusted.*` gaps: payload ADTs/`Downcast`/`SetDiscriminant`, `Call`/`Assert`/`UnwindResume`, `Drop`, and non-empty `CallerMemory`.

## Applicability

This report covers eight durable primary sources:

1. **Anneal & Lean 4 — `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `main`) on `leanprover/lean4` (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`):** Pass-1 rules (`TrustedBoundary.lean`), `Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`, and `Anneal.PureLift` apply directly to this commit.
2. **`rustc` MIR & Drop Elaboration — `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd` vs. `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `1.98.0-nightly 2026-05-30`) & `rust-lang/reference` (`a286e1ecb8ce193d50056e4bb042eea9b23876ef`):** Commit `8144389c` is `vendor/lean-miri`'s upstream pin; `f8a08b68` is `anneal-rustc-capture`'s compiler pin. The `run_analysis_to_runtime_passes` pipeline, `lower_expr_try`, `lower_expr_for`, `Try`/`ControlFlow`, iterators, and `drop_ladder` match across both commits, with **one documented delta** in `elaborate_drops.rs`: `f8a08b68` adds **`.include_inactive_in_otherwise()`** to `MaybeUninitializedPlaces::new` (`#L61-L65`), pairing with `MaybeInitializedPlaces::exclude_inactive_in_otherwise()` so inactive enum variant subpaths entering `SwitchInt` `otherwise` arms become maybe-uninitialized—turning `(true, false)` (`DropStyle::Static`, `#L186`) into `(true, true, false)` (`DropStyle::Conditional`, `#L187`) with an explicit `bool` drop flag. `f8a08b68` also adds `ElaborateDropsCtxt::terminator_loc` and `MirPass::is_required`.
3. **CFG Structuring — Ramsey (ICFP 2022, DOI `10.1145/3547621`), `ghc/ghc` (`83038fbee5efea8e3ebd5090b2ff5537462e169d`, `FromCmm.hs`), and Johnson, Pearson, & Pingali (PLDI 1994, DOI `10.1145/178243.178258`):** Applies to reducible CFGs; irreducible CFGs require external node splitting beforehand.

Lean 4 listings are derived from `TrustedBoundary.lean` syntax rules without live compilation (`--workload light`).

## Findings

### 1. Beyond Relooper Dominator-Tree Structuring vs. SESE / PST Hammock Decomposition

`Basis: documentation + source + derived`

#### 1.1 Norman Ramsey's Beyond Relooper Algorithm (`GHC.Wasm.ControlFlow.FromCmm`)

Classic CFG structuring either duplicates blocks when untangling multi-exit graphs (Emscripten Relooper, 2011) or interleaves three graph-rewriting passes (Peterson, Kasami, and Tokura, 1973). Ramsey (*Beyond Relooper*, PACMPL Vol. 6, Issue ICFP, Art. 121, pp. 1–22, 2022) shows that for any reducible CFG, a single recursive traversal over the **dominator tree** ordered by **reverse postorder numbers (`rpnum`)** suffices without code duplication.

Direct inspection of GHC's implementation in `compiler/GHC/Wasm/ControlFlow/FromCmm.hs` (`ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d`, `#L89-L312`) fixes the exact data structures and predicates:

1. **De Bruijn Context Stack (`ContainingSyntax` and `Context`, `#L89-L104`):**
   `ContainingSyntax` has three frames: `BlockFollowedBy Label` (forward jump target following a lexical block), `LoopHeadedBy Label` (backward jump target at loop entry), and `IfThenElse (Maybe Label)` (optional continuation label after an `if`). `index lbl (enclosing context)` (`#L302-L306`) computes the zero-based De Bruijn break depth to the innermost matching frame, while `fallthrough : Maybe Label` records whether normal sequential completion reaches the next block directly (`#L118, #L212`).
2. **Exact RPO & Dominator Predicates (`#L262-L300`):**
   - **Backward edge (`isBackward`, `#L265-L266`):** `rpnum to <= rpnum from` (self-edges are backward).
   - **Merge node (`isMergeLabel`, `#L274-L293`):** A reachable node entered by **at least two forward edges** (`forwardPreds` excludes every edge satisfying `isBackward from to`). A loop header entered once from outside and once via a back-edge is therefore *not* a merge node unless two forward paths enter it.
   - **Loop header (`isLoopHeader`, `#L294-L300`):** A block `h` targeted by some reachable block edge `b -> h` where `h` dominates `b`.
3. **RPO-Sorted Dominator-Tree Traversal (`sortTree`, `doTree`, `nodeWithin`, `doBranch`, `#L153-L234`):**
   - `sortTree` (`#L230-L234`) orders each dominator node's children in **descending `rpnum` order** (`sortBy (flip compare `on` rpnum)`), placing the *latest* blocks in execution order at the head of the child list.
   - `doTree (Node x children) context` (`#L163-L174`) keeps merge-node children (`filter hasMergeRoot children`, or all children on `CmmSwitch`). When `isLoopHeader x` holds, it emits `WasmLoop` after pushing `LoopHeadedBy (entry x)` onto `enclosing`, ensuring backward jumps (`br d`) restart the header.
   - `nodeWithin x (y_n : ys) maybeMarks context` (`#L176-L186`) wraps `maybeMarks = Just zlabel` in `BlockFollowedBy zlabel`, then splits `y_n` (highest remaining `rpnum`, executed *after* `x` and `ys`) into `Seq (nodeWithin x ys (Just (entry y_n)) (context `withFallthrough` (entry y_n))) (doTree y_n context)`. Every jump to `y_n` inside `x` or earlier merge siblings `ys` now resolves to a valid forward `BlockFollowedBy` break depth!
   - `doBranch from to context` (`#L211-L219`) maps edge `from -> to` deterministically:
     1. `to == fallthrough` (empty stack) $\implies$ `Fallthrough` (no-op);
     2. `isBackward from to` $\implies$ `Br (index to context)` (targets `LoopHeadedBy to`);
     3. `isMergeLabel to` $\implies$ `Br (index to context)` (targets `BlockFollowedBy to`);
     4. Otherwise (`to` has a unique forward predecessor `from` immediately dominating `to`) $\implies$ `doTree (subtreeAt to) context` (**unique-parent subtree inlining**, zero duplication).

#### 1.2 SESE / Program Structure Tree (PST) Decomposition (Johnson, Pearson, & Pingali, PLDI 1994)

In *The Program Structure Tree: Computing Control Regions in Linear Time* (PLDI 1994, DOI `10.1145/178243.178258`), two edges $(a, b)$ in the exit-augmented CFG $G' = G \cup \{(\text{exit} \to \text{entry})\}$ bound a canonical **Single-Entry Single-Exit (SESE)** region iff $a$ dominates $b$, $b$ postdominates $a$, and $(a, b)$ are **cycle-equivalent** (every cycle in $G'$ traverses either both edges or neither). Adjacent edges within each cycle-equivalence class form a nested PST in $O(|V| + |E|)$ time.

| Dimension | Beyond Relooper (`FromCmm`) | SESE / PST (`Johnson-Pearson-Pingali`) | Hybrid SESE-Annotated `CfgTree` (Recommended) |
| :--- | :--- | :--- | :--- |
| **Multi-exit `?` / `break` / `Unwind`** | **Native:** De Bruijn `block`/`loop`/`br d` encodes arbitrary forward exits without duplication. | **Coarse:** Any `?` early return or `Cleanup` edge breaks postdomination, collapsing enclosing PST regions up to the function root. | **Optimal:** Uses Beyond Relooper `seq`/`br` on early-exit spines and tags 1-entry/1-exit hammocks as closed `seseRegion` nodes. |
| **Day-2 Local Framing (`P2`)** | Open `BlockFollowedBy` targets carry continuation frames unless bounded at cutpoints. | **Optimal:** Each SESE region has one entry edge and one exit edge, permitting frame separation of untouched locals. | **Optimal where applicable:** `seseRegion` scopes frame untouched locals cleanly inside multi-exit bodies. |
| **Complexity & TCB Cost** | Dominators + RPO + recursive pass (runs externally); linear certificate validation in Lean. | $O(|V| + |E|)$ undirected DFS bracket sweep (runs externally). | External synthesis; **$O(|\text{CfgTree}|)$ single-pass `@CfgTree.rec` check in 0-TCB `theory/`**. |

---

### 2. Single-Pass Pass-1 Lean 4 Bisimulation Validator Over Unstructured MIR CFGs

`Basis: source + derived`

In `trusted/audit/TrustedBoundary.lean`, `allowedDeclarationKinds` (`#L458-L462`), `allowedCommandSyntaxKinds` (`#L464-L485`), and `validateRepoConstant` (`#L1117-L1152`) forbid `partial`, `unsafe`, `coinductive`, `terminationBy`, `deriving BEq`, and compiler-generated `._unsafe_rec` helpers (`Trusted/MirAst.lean#L77-L82`). Running dominator discovery inside Pass-1 `prelude` Lean would require explicit fuel threading and graph termination proofs.

Instead, **certificate-checked CFG structuring** computes a single-inductive `CfgTree` externally and checks graph bisimulation in **one structural pass** via `@CfgTree.rec` (no `mutual` block or `._unsafe_rec` required):

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.CfgStructure

/-- Minimal `BasicBlock` view mirrored from `Trusted.MirAst` for Pass-1 validation. -/
inductive MirTerm where
  | goto (target : Nat)
  | switchInt (branches : List (Nat × Nat)) (otherwise : Nat)
  | return_
  | unreachable
  | unwindResume

structure MirBlock where
  stmtCount : Nat
  term      : MirTerm

/-- Single non-nested inductive `CfgTree` certificate (Beyond Relooper + SESE tags).
    Matching `FromCmm.hs#L169-L171`, `switchStep` jumps solely to enclosing `seq`/`loopHdr` targets. -/
inductive CfgTree where
  | gotoStep (bb : Nat) (sub : CfgTree)
  | ifStep (bb : Nat) (thenSub elseSub : CfgTree)
  | switchStep (bb : Nat) (arms : List (Nat × Nat × Nat)) (defDepth defBb : Nat)
  | retLeaf (bb : Nat)
  | unreachLeaf (bb : Nat)
  | unwindLeaf (bb : Nat)
  | seq (first : CfgTree) (contBb : Nat) (second : CfgTree)
  | loopHdr (hdrBb : Nat) (body : CfgTree)
  | br (depth : Nat) (targetBb : Nat)
  | fallthrough (expectedBb : Nat)
  | seseRegion (entryBb exitBb : Nat) (inner : CfgTree)

inductive ExitTarget where
  | blockFollow (bb : Nat)
  | loopHead (bb : Nat)

def ExitTarget.bb : ExitTarget → Nat
  | .blockFollow b => b
  | .loopHead b    => b

/-- Total list lookup via `List.foldr` (zero `._unsafe_rec`, kernel `rfl`-reducible). -/
def listGet? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  xs.foldr (fun x ih k => match k with | 0 => some x | k' + 1 => ih k') (fun _ => none) idx

def optNatEq : Option Nat → Option Nat → Bool
  | none, none     => true
  | some a, some b => Nat.beq a b
  | _, _           => false

def CfgTree.entryBb? : CfgTree → Option Nat
  | .gotoStep bb _       => some bb
  | .ifStep bb _ _       => some bb
  | .switchStep bb _ _ _ => some bb
  | .retLeaf bb          => some bb
  | .unreachLeaf bb      => some bb
  | .unwindLeaf bb       => some bb
  | .seq first _ _       => CfgTree.entryBb? first
  | .loopHdr hdrBb _     => some hdrBb
  | .br _ targetBb       => some targetBb
  | .fallthrough expBb   => some expBb
  | .seseRegion ent _ _  => some ent

def checkBr (ctx : List ExitTarget) (depth targetBb : Nat) : Bool :=
  match listGet? ctx depth with
  | some tgt => Nat.beq tgt.bb targetBb
  | none     => false

def checkTargetEdge (targetBb : Nat) (ctx : List ExitTarget) (ft : Option Nat)
    (sub : CfgTree) (subOk : List ExitTarget → Option Nat → Bool) : Bool :=
  match sub with
  | .fallthrough expected => Nat.beq targetBb expected && optNatEq ft (some expected)
  | .br depth certBb      => Nat.beq certBb targetBb && checkBr ctx depth targetBb
  | _                     => optNatEq (CfgTree.entryBb? sub) (some targetBb) && subOk ctx ft

def checkSwitchArms (ctx : List ExitTarget)
    (arms : List (Nat × Nat × Nat)) (mBranches : List (Nat × Nat)) : Bool :=
  arms.foldr
    (fun (cv, d, tb) ih mb =>
      match mb with
      | [] => false
      | (mv, mt) :: rest => Nat.beq cv mv && Nat.beq tb mt && checkBr ctx d tb && ih rest)
    (fun mb => match mb with | [] => true | _ => false)
    mBranches

/-- Single-pass structural CFG bisimulation checker (`@CfgTree.rec`, zero `._unsafe_rec`). -/
def validateCfg (blocks : List MirBlock) (t : CfgTree)
    (ctx : List ExitTarget) (ft : Option Nat) : Bool :=
  @CfgTree.rec (fun _ => List ExitTarget → Option Nat → Bool)
    (fun bb sub ihSub c f =>
      match listGet? blocks bb with
      | some ⟨_, .goto tgt⟩ => checkTargetEdge tgt c f sub ihSub
      | _ => false)
    (fun bb tSub fSub ihT ihF c f =>
      match listGet? blocks bb with
      | some ⟨_, .switchInt [(0, fBb)] tBb⟩ | some ⟨_, .switchInt [(1, tBb)] fBb⟩ =>
        checkTargetEdge tBb c f tSub ihT && checkTargetEdge fBb c f fSub ihF
      | _ => false)
    (fun bb arms defD defBb c _ =>
      match listGet? blocks bb with
      | some ⟨_, .switchInt mBranches mDef⟩ =>
        Nat.beq defBb mDef && checkBr c defD mDef && checkSwitchArms c arms mBranches
      | _ => false)
    (fun bb _ _ => match listGet? blocks bb with | some ⟨_, .return_⟩ => true | _ => false)
    (fun bb _ _ => match listGet? blocks bb with | some ⟨_, .unreachable⟩ => true | _ => false)
    (fun bb _ _ => match listGet? blocks bb with | some ⟨_, .unwindResume⟩ => true | _ => false)
    (fun _ contBb second ihFirst ihSecond c f =>
      ihFirst (.blockFollow contBb :: c) (some contBb) &&
      optNatEq (CfgTree.entryBb? second) (some contBb) && ihSecond c f)
    (fun hdrBb _ ihBody c _ => ihBody (.loopHead hdrBb :: c) none)
    (fun depth targetBb c _ => checkBr c depth targetBb)
    (fun expBb _ f => optNatEq f (some expBb))
    (fun ent _ inner ihInner c f =>
      optNatEq (CfgTree.entryBb? inner) (some ent) && ihInner c f)
    t ctx ft

end Anneal.CfgStructure
```

**Soundness Bridge to `Trusted.MirSemantics`:** Because every `CfgTree` node executes `body.basicBlocks[bb]` in lockstep—never eliding `Assert`, `StorageLive`/`StorageDead`, or `Operand.move`—a structured WP `wpCfgTree` (discharging `.loopHdr` via cutpoint invariant `Inv` and decreasing `rank : State → Nat`, matching `Anneal.PureLift.BlockCfg.runWhileFlowSteps_cutpoint_sound` at `BlockCfg.lean#L75-L152`) proves `validateCfg body.basicBlocks tree [] none = true → wpCfgTree body tree Q s₀ → Anneal.MirWp.wpOutcomeState p Q (fun _ => False) fuel s₀` with zero `Anneal.*` symbols in locked theorem statements.

---

### 3. Exact `Runtime(PostCleanup)` MIR Desugaring Anatomy in `rustc`

`Basis: source`

#### 3.1 Compiler Phase Boundary (`compiler/rustc_mir_transform/src/lib.rs#L605-L720`)

At `run_analysis_to_runtime_passes` (`#L605-L634`), `rustc` transforms `MirPhase::Analysis(Initial)` through:
1. `run_analysis_cleanup_passes` (`#L639-L649`): `ImpossibleClauses`, `CleanupPostBorrowck`, `RemoveNoopLandingPads`, `SimplifyCfg::PostAnalysis`, `Derefer` $\to$ `Analysis(PostCleanup)`.
2. `run_runtime_lowering_passes` (`#L652-L676`): `CriticalCallEdges`, `PostAnalysisNormalize`, `Subtyper`, `ElaborateDrops`, `CheckDropRecursion`, `AbortUnwindingCalls`, `AddMovesForPackedDrops`, `EraseDerefTemps`, `ElaborateBoxDerefs`, `StateTransform`, `KnownPanicsLint` $\to$ `Runtime(Initial)`.
3. `run_runtime_cleanup_passes` (`#L679-L693`): `LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`, clearing `local_info` $\to$ **`Runtime(PostCleanup)`**.

Importantly, `run_optimization_passes` (`#L695-L720`) runs **afterward**: `CheckAlignment`/`CheckNull`/`CheckEnums`, `LowerSliceLenCalls`, `InstSimplify::BeforeInline`, **`ForceInline`**, and **`Inline`** have **not yet executed** in `Runtime(PostCleanup)`.

#### 3.2 `Try::branch` / `?` / `ControlFlow` / `FromResidual` Desugaring

Inspection of `compiler/rustc_ast_lowering/src/expr.rs#L1933-L2020`, `library/core/src/ops/control_flow.rs#L89-L120`, `try_trait.rs#L130-L390`, `option.rs#L2865-L2894`, and `result.rs#L2171-L2208` fixes the exact MIR lowering of `<expr>?`:

1. **AST Lowering (`expr.rs#L1934-L2015`):** Outside `try {}` blocks (`TryBlockScope::Function`), `<expr>?` lowers to `match Try::branch(<expr>) { ControlFlow::Continue(val) => val, ControlFlow::Break(residual) => return FromResidual::from_residual(residual) }`. Inside homogeneous `try {}` blocks, `Break` calls `LangItem::ResidualIntoTryType` (`residual_into_try_type`) and breaks to `'catch_target`.
2. **Variant-Index Asymmetry (`control_flow.rs#L89-L101`):** `pub enum ControlFlow<B, C = ()> { Continue(C), Break(B) }` places **`Continue` at `VariantIdx(0)` and `Break` at `VariantIdx(1)`** specifically so `Result<T, E>` (`Ok = 0`, `Err = 1`) maps to `ControlFlow<Result<!, E>, T>` without discriminant retagging. By contrast, `Option<T>` (`None = 0`, `Some = 1`) **inverts** variant indices across `<Option<T> as Try>::branch` (`Some(v) (1) -> Continue(v) (0)`, `None (0) -> Break(None) (1)`), and residuals `Option<!>` / `Result<!, E>` carry uninhabited `!` (`MirTy.never`) so the `FromResidual::from_residual` branch handles only the error/none variant.
3. **Resulting 6-Block `Runtime(PostCleanup)` Subgraph:**
   `bb_call`: `Call(Try::branch, [move _tmp], dst: _cf, target: Some(bb_sw), unwind: cleanup)` $\to$ `bb_sw`: `StorageDead(_tmp); _d = Discriminant(_cf); SwitchInt(move _d) [0 -> bb_cont, 1 -> bb_brk, otherwise -> bb_unreach]` $\to$ `bb_cont`: `x = move ((_cf as Continue).0); StorageDead(_cf)` vs. `bb_brk`: `_r = move ((_cf as Break).0); StorageDead(_cf); Call(FromResidual::from_residual, [move _r], dst: _0, target: Some(bb_drops), unwind: cleanup)` $\to$ `bb_ret`.

#### 3.3 Drop Elaboration and Boolean Drop Flags (`ElaborateDrops`)

Inspection of `compiler/rustc_mir_transform/src/elaborate_drops.rs#L51-L523` and `elaborate_drop.rs#L21-L950, #L1178-L1621` establishes the complete drop-flag state machine:

- **Allocation Condition (`elaborate_drops.rs#L60-L75, #L267-L335`):** `MoveData::gather_moves` tracks only `ty.needs_drop(...)` places. `create_drop_flag` allocates a synthetic `bool` temporary (`patch.new_temp(tcx.types.bool, span)`) at a `Drop` terminator iff **both `maybe_init && maybe_uninit` hold** along reaching paths (`#L312-L314`).
- **Flag Update Rules (`#L418-L521`):** All drop flags initialize to `false` (`Absent`) at `Location::START` (`drop_flags_on_init`); entry parameter flags set `true` (`drop_flags_for_args`); moves clear flags to `false`; assignments set flags to `true`. On `Call` terminators with `UnwindAction::Cleanup(_)`, the destination flag sets `true` at `tgt.start_location()` (normal return only); when `unwind` is `Continue | Unreachable | Terminate`, `rustc` sets the flag `true` **pre-call** (`#L502-L520`). On `unwind.is_cleanup()` paths, `drop_flag_reset_block` omits resetting the flag (`elaborate_drop.rs#L1544-L1548`).
- **Four `DropStyle` Expansions (`elaborate_drops.rs#L184-L189`, `elaborate_drop.rs#L733-L750, #L879-L950, #L1178-L1334`):**
  1. `Dead` (`!maybe_init`) $\to$ `TerminatorKind::Goto(succ)`.
  2. `Static` (`maybe_init && !maybe_uninit`) $\to$ unconditional `TerminatorKind::Drop`.
  3. `Conditional` (`maybe_init && maybe_uninit && !multipart`) $\to$ `drop_flag_test_block` (`SwitchInt(copy flag) [0 -> succ, otherwise -> drop_block]`).
  4. `Open` (`multipart`) $\to$ paired mainline and `is_cleanup` **drop ladders** (`drop_ladder`, `#L879-L950`). Enum drops test the master drop flag *before* reading `Rvalue::Discriminant(place)` (`adt_switch_block`, `#L1178-L1210`) so invalidated discriminants are never inspected; slice/unsplit array drops emit a `cur == len` `drop_loop` with `&raw mut P[cur]` and `Drop(*ptr)` (`#L1260-L1334`).

#### 3.4 `for` Loops, `slice::Iter`, `ops::Range`, and Discriminant Tagging

- **`for` Lowering (`expr.rs#L1769-L1931`):** `for pat in head { body }` lowers inside `expr_drop_temps_mut` to `IntoIterator::into_iter(head)` followed by a single-header `loop { match Iterator::next(&mut iter) { None => break, Some(pat) => body } }`. Beyond Relooper classifies `bb_hdr` (calling `Iterator::next`) as a clean 1-back-edge loop header whose exit is the `None => break` arm! Inside core stdlib callees (not inlined at `Runtime(PostCleanup)`), `Range<T>::spec_next` (`iter/range.rs#L1100-L1111`) checks `self.start < self.end` and steps via `Step::forward_unchecked`, while `slice::Iter::next` (`slice/iter/macros.rs#L157-L192`) branches on `T::IS_ZST` (pointer bump `ptr.add(1)` vs `without_provenance_mut(len.unchecked_sub(1))`).
- **`Option`/`Result` Discriminant Tagging (`Trusted/MirAst.lean#L189-L250, #L600-L656`, `Trusted/MirSemantics.lean#L463-L547`):** Construction writes variant fields under `PlaceElem::Downcast(_, v_idx)` followed by `StatementKind::SetDiscriminant`; matching evaluates `Rvalue::Discriminant(place)` (`Variants::Single` ZST `0`, `TagEncoding::Direct` via `tagBitsToDiscrBits`, or `TagEncoding::Niche` such as `Option<&T>`/`Option<NonZeroU32>`) followed by `SwitchInt` and `Downcast`.

---

### 4. Certified Idiom Resugaring Rules and Anti-Laundering Guards

`Basis: derived`

Backward VC transport (`Safe(Resugared) ⟹ Safe(MIR)`) requires **safety-reflecting guards ($\Phi_{\text{no-erased-UB}}$)** so folding administrative MIR steps never masks a source-level `.undefined` or `.unsupported` fault:

| Rule ID | Matched `CfgTree` + MIR Pattern | Resugared Combinator | Safety-Reflection Guard $\Phi_{\text{no-erased-UB}}$ | Fuel Slack |
| :--- | :--- | :--- | :--- | :--- |
| **`RESUGAR-TRY`** | `Call(Try::branch)` $\to$ `Discriminant` $\to$ `SwitchInt [0 -> cont, 1 -> brk]` $\to$ `Call(FromResidual)` + exit | Monadic `Except Res Out` bind | `_cf` has exact `ControlFlow` layout; `Continue` moves `_cf.0` once and calls `StorageDead(_cf)`; `Break` preserves `FromResidual` + outer cleanup drops; `otherwise` is `Unreachable`. | Exact branch slack $\Delta_{\text{try}}$ |
| **`RESUGAR-DROP-FLAG-CONST`** | Static `bool` drop flag `_f` test `SwitchInt(_f)` dominated by definite `true`/`false` writes | Eliminates dynamic branch into static `Drop` or `goto` | `_f` is non-address-taken (`&`/`&raw`); on **every** normal and cleanup path reaching `SwitchInt(_f)`, `_f` is `.live (some (.bool b))` (never uninit/`.dead`) and agrees with target init state. | `-2` to `-3` steps/branch |
| **`RESUGAR-DROP-TRIVIAL-LADDER`** | `ElaborateDrops` normal + `is_cleanup` half-ladders with `!needs_drop` or `.dead` subpaths | Direct sequential fallthrough (`seq`) | Every elided subpath is statically `.dead`/no-op and unwind edges bypass no live initialized sibling drops. | Collapses $2k$ blocks to `1` edge |
| **`RESUGAR-FOR-RANGE`** | `Call(IntoIter)` $\to$ `loopHdr` (`Call(Iterator::next(&mut iter))` $\to$ `SwitchInt`) | `natFold` / slice-cursor fold over `[lo, hi)` | `iter` is unaliased outside `&mut iter`; `body` never mutates `iter` or escapes borrows across iterations; `Step` bounds hold; post-loop `Drop(iter)` preserved. | $k_{\text{mir}} \le c_1(\text{len}+1)+c_2$ |
| **`RESUGAR-ENUM-MATCH`** | `_d = Discriminant(p); SwitchInt(_d)` + `Downcast` | Total sum-type `match` eliminator | `p` is live, not previously moved (`deinitMovedPlace = true`), and holds valid tag; `SwitchInt` arms cover all valid variants; `otherwise` is `Unreachable`. | `+1` (`Discriminant`) |

---

### 5. Evaluation Against the Anneal Theory Rubric `(T1, P1–P5, C1–C2)`

`Basis: source + derived`

| Rubric Dimension | Grade | Assessment & Concrete `Trusted.*` Delta on `joshlf/anneal@c131b320...` |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **S** (CFG) / **G** (`Trusted.*` gaps) | **0-TCB CFG Validation:** `CfgTree` + `validateCfg` compile strictly in Pass-1 `theory/` (`prelude` + `Init.*`), proving `BodyVerified` via Statement-Origin Separation with zero `Trusted.*` edits. **Exposes 4 concrete `Trusted.*` gaps for full idiom resugaring on `c131b320eeeb...`:** `Trusted.MirAst` and `Trusted.MirSemantics` currently fail closed (`.fault .unsupported`) on: (a) payload-carrying `enum` ADTs (`Option`/`Result`/`ControlFlow`), `PlaceElem.downcast`, and `StatementKind.setDiscriminant` (`MirAst.lean#L613-L656`); (b) `TerminatorKind.call` (`MirSemantics.lean#L1568, #L1691-L1694`) needed to specify `Try::branch`, `FromResidual`, and `Iterator::next`; (c) `TerminatorKind.drop` (`MirAst.lean#L783`) and `Assert`/`UnwindResume` (`MirSemantics.lean#L1568`); and (d) non-empty `CallerMemory` (`MirSemantics.lean#L803-L804`) required for `&[T]`/`&mut iter`. |
| **(P1) Human Spec Auditability** | **S** | Internal to `theory/` proof terms (`ConstantInfo.value?`). Human-reviewed Rust specs never reference `CfgTree`, `ExitTarget`, or drop flags. |
| **(P2) Authoring & Day-2 Locality** | **S** | Eliminates manual `BasicBlockId` tracking: inserting blocks or `?` returns shifts numeric block IDs without breaking proof structure; nested `seseRegion` tags isolate unchanged blocks. |
| **(P3) Lean 4 Kernel & LSP Scaling** | **S** | Single-pass `@CfgTree.rec` runs in $O(|V| + |E|)$; loop invariants break symbolic MIR unrolling at `.loopHdr` boundaries. |
| **(P4) Heterogeneous Composability** | **M** | `CfgTree` handles pure branches, `unsafe` raw-pointer blocks, and cleanup pads uniformly. `RESUGAR-FOR-RANGE` assumes unique `iter` ownership; `&mut`-yielding iterators need prophecy/lens composition. |
| **(P5) Failure Legibility** | **S** | Failed loop/resugar checks report structured `loopHdr hdrBb`, `seseRegion entryBb exitBb`, or specific missing `FromResidual` edges instead of raw `evalStep` states. |
| **(C1–C2) Conceptual Minimality** | **S** | Consolidates `BlockCfg`, forwarder elimination, straight-line `MirBridge`, and manual `whileLoop` plans into two orthogonal 0-TCB primitives: `(1)` `CfgTree` bisimulation checking and `(2)` guarded idiom resugaring. |

## Boundaries

1. **Irreducible Multi-Entry Loops (`unsupported` without node splitting; `known not to apply` to standard safe Rust lowering):** Beyond Relooper assumes a reducible CFG (`FromCmm.hs#L147` invokes `asReducible`). While standard `rustc_ast_lowering` structured loops/matches/`?` yield reducible CFGs, jump-threaded or custom MIR containing multi-entry cycles requires external node splitting prior to emitting `CfgTree`.
2. **Unmodeled `Trusted.MirAst` Constructs on `joshlf/anneal@c131b320...` (`unsupported`):** `SetDiscriminant`, payload-carrying ADTs/`Downcast`, `TerminatorKind.drop`, reachable `Call`, `Assert`, `UnwindResume`, and non-empty `CallerMemory` all step fail-closed to `FaultKind.unsupported` (`MirAst.lean#L612-L656, #L782-L795`; `MirSemantics.lean#L803-L804, #L1568`). Thus `CfgTree` applies immediately on `c131b320...` to scalar/boolean/fieldless-enum branches and loops (`Goto`, `SwitchInt`, `Return`, `Unreachable`), while full `RESUGAR-TRY`/`FOR`/`DROP` end-to-end proofs depend on those TCB extensions.
3. **Unguarded Drop-Flag or Discriminant Elision (`known not to apply`):** Eliding `SwitchInt(_drop_flag)` or `Discriminant(p)` without checking definite initialization and non-moved liveness (`deinitMovedPlace = true`) is unsound for backward safety transport whenever raw MIR could step to `FaultKind.undefined`.
4. **Coroutine `StateTransform` and `async_drop` Poll-Yield Loops (`not examined`):** Async drop lowering (`elaborate_drop.rs#L227-L320, #L637-L712`) and coroutine `Yield` terminators were not analyzed and are `unsupported` in `Trusted.MirAst`.
5. **Optimal Tie-Breaking Across RPO-Incomparable `SwitchInt` Children (`unknown`):** Whether a tie-breaking heuristic over incomparable RPO dominator children minimizes nested `CfgTree.seq` depth on large dense `SwitchInt` jump tables was not empirically measured (`unknown`).

## Evidence

| Subject | Immutable Identity / DOI | Inspected Path & Exact Symbols / Line Ranges |
| :--- | :--- | :--- |
| **Anneal `TrustedBoundary`, `MirAst`, `MirSemantics`, `PureLift`** | `joshlf/anneal` `@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main`) | `trusted/audit/TrustedBoundary.lean#L442-L596, #L1108-L1153`; `trusted/lean/Trusted/MirAst.lean#L75-L92, #L189-L250, #L600-L796`; `trusted/lean/Trusted/MirSemantics.lean#L463-L547, #L800-L830, #L1537-L1614, #L1685-L1760`; `theory/Anneal/PureLift/Lens.lean#L41-L65`; `theory/Anneal/PureLift/BlockCfg.lean#L25-L199`; `theory/Anneal/PureLift/MirBridge.lean#L30-L100` |
| **Lean 4 Foundation** | `leanprover/lean4` `@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `trusted/lean/lean-toolchain`, `trusted/lean/foundation-lock.json` (`51` `Init.*` modules) |
| **`rustc` MIR & Drop Elaboration (Miri Pin)** | `rust-lang/rust` `@8144389c895da997dbdecaa635e41d6a50be6ffd` | `compiler/rustc_mir_transform/src/lib.rs#L605-L720`; `compiler/rustc_ast_lowering/src/expr.rs#L1769-L2020`; `compiler/rustc_mir_transform/src/elaborate_drops.rs#L49-L523`; `compiler/rustc_mir_transform/src/elaborate_drop.rs#L21-L950, #L1178-L1621`; `library/core/src/ops/control_flow.rs#L89-L120`; `library/core/src/ops/try_trait.rs#L130-L390`; `library/core/src/option.rs#L2865-L2894`; `library/core/src/result.rs#L2171-L2208`; `library/core/src/slice/iter/macros.rs#L10-L192`; `library/core/src/iter/range.rs#L1019-L1150` |
| **`rustc` 1.98.0-nightly Delta** | `rust-lang/rust` `@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly 2026-05-30`) | `compiler/rustc_mir_transform/src/elaborate_drops.rs#L61-L80, #L162-L170` (`.include_inactive_in_otherwise()`, `terminator_loc`, `is_required`); `compiler/rustc_mir_transform/src/lib.rs#L20-L55` |
| **The Rust Reference** | `rust-lang/reference` `@a286e1ecb8ce193d50056e4bb042eea9b23876ef` | `src/items/enumerations.md`, `src/behavior-considered-undefined.md` |
| **Beyond Relooper** | DOI `10.1145/3547621` | Norman Ramsey, *Beyond Relooper: Recursive Translation of Unstructured Control Flow to Structured Control Flow*, PACMPL 6(ICFP), Art. 121, pp. 1–22 (2022) |
| **GHC `FromCmm.hs`** | `ghc/ghc` `@83038fbee5efea8e3ebd5090b2ff5537462e169d` | `compiler/GHC/Wasm/ControlFlow.hs#L23-L46`; `compiler/GHC/Wasm/ControlFlow/FromCmm.hs#L89-L315` (`ContainingSyntax`, `doTree`, `nodeWithin`, `doBranch`, `isMergeLabel`, `isLoopHeader`, `isBackward`, `sortTree`, `index`) |
| **Program Structure Tree** | DOI `10.1145/178243.178258` | Richard Johnson, David Pearson, and Keshav Pingali, *The Program Structure Tree: Computing Control Regions in Linear Time*, PLDI 1994 |

## Revalidation

1. **Diff `rustc` Pipeline & `ElaborateDrops` Across Compiler Revisions:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/lib.rs -o /tmp/rustc_lib_old.rs
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/<NEW_RUSTC_SHA>/compiler/rustc_mir_transform/src/lib.rs -o /tmp/rustc_lib_new.rs
   diff -u /tmp/rustc_lib_old.rs /tmp/rustc_lib_new.rs
   ```
   Verify `run_analysis_to_runtime_passes`, `run_runtime_lowering_passes`, `run_runtime_cleanup_passes`, and `elaborate_drops.rs` flags.
2. **Verify `ControlFlow` Variant Layout & `?` Lowering:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/<NEW_RUSTC_SHA>/library/core/src/ops/control_flow.rs | grep -n -A 10 "pub enum ControlFlow"
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/<NEW_RUSTC_SHA>/compiler/rustc_ast_lowering/src/expr.rs | grep -n -A 25 "fn lower_expr_try("
   ```
3. **Check `Anneal.CfgStructure` Under Pass-1 Lean `v4.34.1`:**
   Save the Pass-1 `prelude` `Anneal.CfgStructure` listing from Findings §2 to `/tmp/cfg_probe.lean` and run `anneal-lean-run lean /tmp/cfg_probe.lean`, followed by `TrustedBoundary` preflight/audit to verify zero `._unsafe_rec` helpers and empty (`[]`) axiom closure. Passing confirms Pass-1 admissibility only; MIR soundness requires instantiating against `Trusted.MirSemantics.evalStep`.
