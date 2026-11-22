/-
Kernel-checked Lean v4.34.1 formalization of rustc's Try Trait v2 (`?`),
three-scope `try {}` / `try bikeshed Ty {}` / `do yeet` AST-to-HIR lowering,
`#[track_caller]` caller-location forwarding (`Body::caller_location_span`),
Edition 2021 vs. Edition 2024 `Try::from_output` tail drop scopes, and
uninhabited-residual (`Infallible` / `!`) dead-arm MIR elimination soundness.

Constructive kernel-pure formalization: all value definitions are marked
`noncomputable def`, with no derived instances, no partial definitions, and no
classical or native-evaluation axioms.
-/

namespace TryTraitResidualCallerAndDropSoundness

-- ============================================================================
-- Section 1: Three-Scope AST-to-HIR Lowering (`TryBlockScope`),
--            Type-Inference Determinacy, Heterogeneous `From` Conversion,
--            and `Infallible = !` Coercion Boundaries
-- ============================================================================

/-- Mirrors `rustc_ast_lowering::TryBlockScope`
(`compiler/rustc_ast_lowering/src/lib.rs:610-619`). -/
inductive TryBlockScope : Type where
  | fnScope
  | homogeneous (blockId : Nat)
  | heterogeneous (blockId : Nat)

/-- Surface control-flow operations lowered against `TryBlockScope`. -/
inductive SurfaceOp : Type where
  | qmark
  | yeet

/-- Target lang-item constructor emitted by AST-to-HIR lowering
(`compiler/rustc_ast_lowering/src/expr.rs:1992-2008, 2056-2061`). -/
inductive DesugarLangItem : Type where
  | fromResidual
  | residualIntoTryType
  | fromYeet

/-- Control-flow exit emitted by AST-to-HIR lowering. -/
inductive ExitTarget : Type where
  | returnFn
  | breakBlock (blockId : Nat)

/-- Result of lowering `?` or `do yeet` in a given `TryBlockScope`. -/
structure DesugaringResult : Type where
  langItem : DesugarLangItem
  exit : ExitTarget

/-- Exact AST-to-HIR dispatch of `lower_expr_try` (`expr.rs:1992-2020`) and
`lower_expr_yeet` (`expr.rs:2056-2071`). Note that `lower_expr_yeet` emits
`LangItem::TryTraitFromYeet` (`fromYeet`) even inside `TryBlockScope.homogeneous`,
bypassing `LangItem::ResidualIntoTryType`. -/
noncomputable def lowerSurfaceOp (scope : TryBlockScope) (op : SurfaceOp) : DesugaringResult :=
  match scope, op with
  | .fnScope, .qmark => { langItem := .fromResidual, exit := .returnFn }
  | .homogeneous bid, .qmark => { langItem := .residualIntoTryType, exit := .breakBlock bid }
  | .heterogeneous bid, .qmark => { langItem := .fromResidual, exit := .breakBlock bid }
  | .fnScope, .yeet => { langItem := .fromYeet, exit := .returnFn }
  | .homogeneous bid, .yeet => { langItem := .fromYeet, exit := .breakBlock bid }
  | .heterogeneous bid, .yeet => { langItem := .fromYeet, exit := .breakBlock bid }

/-- Abstract trait environment for `Try`, `FromResidual`, `Residual`, and `Yeet`.
`residualTryType R O T` asserts `<R as Residual<O>>::TryType = T`, which is a
partial function of `(R, O)` by Rust trait coherence (`residual_functional`). -/
structure TryEnv (Ty : Type) : Type 1 where
  fromResidual : Ty → Ty → Prop
  residualTryType : Ty → Ty → Ty → Prop
  yeetWrap : Ty → Ty
  residual_functional :
    ∀ {r o t₁ t₂ : Ty}, residualTryType r o t₁ → residualTryType r o t₂ → t₁ = t₂
  residual_implies_fromResidual :
    ∀ {r o t : Ty}, residualTryType r o t → fromResidual t r

/-- Admissibility of target return type `targetTy` for the lang-item call
emitted by lowering an operation with residual/yeeted payload `inputTy` inside a
body whose success output type is `outTy`. -/
noncomputable def AdmissibleTarget {Ty : Type} (env : TryEnv Ty)
    (item : DesugarLangItem) (inputTy outTy targetTy : Ty) : Prop :=
  match item with
  | .fromResidual => env.fromResidual targetTy inputTy
  | .residualIntoTryType => env.residualTryType inputTy outTy targetTy
  | .fromYeet => env.fromResidual targetTy (env.yeetWrap inputTy)

/-- Unannotated type inference determinacy: at most one target type `T` satisfies
the lowered lang-item constraint from `(inputTy, outTy)` alone. -/
noncomputable def UniquelyDeterminesTarget {Ty : Type} (env : TryEnv Ty)
    (scope : TryBlockScope) (op : SurfaceOp) (inputTy outTy : Ty) : Prop :=
  ∀ t₁ t₂ : Ty,
    AdmissibleTarget env (lowerSurfaceOp scope op).langItem inputTy outTy t₁ →
    AdmissibleTarget env (lowerSurfaceOp scope op).langItem inputTy outTy t₂ →
    t₁ = t₂

/-- Heterogeneous conversion witness: two distinct target types (`canonicalTy ≠
convertedTy`) are both admissible for the lowered lang-item constraint. -/
noncomputable def AdmitsHeterogeneousConversion {Ty : Type} (env : TryEnv Ty)
    (scope : TryBlockScope) (op : SurfaceOp)
    (inputTy outTy canonicalTy convertedTy : Ty) : Prop :=
  canonicalTy ≠ convertedTy ∧
  AdmissibleTarget env (lowerSurfaceOp scope op).langItem inputTy outTy canonicalTy ∧
  AdmissibleTarget env (lowerSurfaceOp scope op).langItem inputTy outTy convertedTy

theorem homogeneous_qmark_determines_target {Ty : Type} (env : TryEnv Ty)
    (bid : Nat) (r o : Ty) :
    UniquelyDeterminesTarget env (.homogeneous bid) .qmark r o := by
  intro t₁ t₂ h₁ h₂
  exact env.residual_functional h₁ h₂

theorem homogeneous_qmark_rejects_heterogeneous_conversion {Ty : Type} (env : TryEnv Ty)
    (bid : Nat) (r o t₁ t₂ : Ty) :
    ¬ AdmitsHeterogeneousConversion env (.homogeneous bid) .qmark r o t₁ t₂ := by
  intro h
  exact h.1 (env.residual_functional h.2.1 h.2.2)

theorem fromResidual_scopes_admit_conversion_and_break_unannotated_inference
    {Ty : Type} (env : TryEnv Ty) (bid : Nat) (r o t₁ t₂ : Ty)
    (hne : t₁ ≠ t₂)
    (h₁ : env.fromResidual t₁ r) (h₂ : env.fromResidual t₂ r) :
    AdmitsHeterogeneousConversion env .fnScope .qmark r o t₁ t₂ ∧
    AdmitsHeterogeneousConversion env (.heterogeneous bid) .qmark r o t₁ t₂ ∧
    ¬ UniquelyDeterminesTarget env .fnScope .qmark r o ∧
    ¬ UniquelyDeterminesTarget env (.heterogeneous bid) .qmark r o := by
  refine ⟨⟨hne, h₁, h₂⟩, ⟨hne, h₁, h₂⟩, ?_, ?_⟩
  · intro hUniq
    exact hne (hUniq t₁ t₂ h₁ h₂)
  · intro hUniq
    exact hne (hUniq t₁ t₂ h₁ h₂)

theorem yeet_bypasses_homogeneous_restriction {Ty : Type} (env : TryEnv Ty)
    (scope : TryBlockScope) (y o t₁ t₂ : Ty)
    (hne : t₁ ≠ t₂)
    (h₁ : env.fromResidual t₁ (env.yeetWrap y))
    (h₂ : env.fromResidual t₂ (env.yeetWrap y)) :
    (lowerSurfaceOp scope .yeet).langItem = .fromYeet ∧
    AdmitsHeterogeneousConversion env scope .yeet y o t₁ t₂ ∧
    ¬ UniquelyDeterminesTarget env scope .yeet y o := by
  cases scope with
  | fnScope =>
    refine ⟨rfl, ⟨hne, h₁, h₂⟩, ?_⟩
    intro hUniq
    exact hne (hUniq t₁ t₂ h₁ h₂)
  | homogeneous bid =>
    refine ⟨rfl, ⟨hne, h₁, h₂⟩, ?_⟩
    intro hUniq
    exact hne (hUniq t₁ t₂ h₁ h₂)
  | heterogeneous bid =>
    refine ⟨rfl, ⟨hne, h₁, h₂⟩, ?_⟩
    intro hUniq
    exact hne (hUniq t₁ t₂ h₁ h₂)

/-- Main Theorem 1: Complete three-scope desugaring characterization separating
`Function`, `Homogeneous`, and `Heterogeneous` scopes across `?` and `do yeet`. -/
theorem try_scope_conversion_and_inference_characterization
    {Ty : Type} (env : TryEnv Ty) (bid : Nat) (r y o tSame tSuper : Ty)
    (hne : tSame ≠ tSuper)
    (hResSame : env.fromResidual tSame r)
    (hResSuper : env.fromResidual tSuper r)
    (hYeetSame : env.fromResidual tSame (env.yeetWrap y))
    (hYeetSuper : env.fromResidual tSuper (env.yeetWrap y)) :
    -- (a) Homogeneous `?` uniquely fixes `<R as Residual<O>>::TryType` and rejects
    --     heterogeneous `From` widening (`E0308`).
    (UniquelyDeterminesTarget env (.homogeneous bid) .qmark r o ∧
     ¬ AdmitsHeterogeneousConversion env (.homogeneous bid) .qmark r o tSame tSuper) ∧
    -- (b) Function `?` and Heterogeneous `try bikeshed Ty {}` `?` both admit
    --     heterogeneous conversion and require contextual/explicit return types.
    (AdmitsHeterogeneousConversion env .fnScope .qmark r o tSame tSuper ∧
     AdmitsHeterogeneousConversion env (.heterogeneous bid) .qmark r o tSame tSuper ∧
     ¬ UniquelyDeterminesTarget env .fnScope .qmark r o ∧
     ¬ UniquelyDeterminesTarget env (.heterogeneous bid) .qmark r o) ∧
    -- (c) `do yeet` inside Homogeneous `try {}` bypasses `ResidualIntoTryType`,
    --     admitting `From` conversion while rejecting unannotated blocks (`E0283`).
    ((lowerSurfaceOp (.homogeneous bid) .yeet).langItem = .fromYeet ∧
     AdmitsHeterogeneousConversion env (.homogeneous bid) .yeet y o tSame tSuper ∧
     ¬ UniquelyDeterminesTarget env (.homogeneous bid) .yeet y o) ∧
    -- (d) Exit control separation: `fnScope` returns; both try-block scopes break.
    ((lowerSurfaceOp .fnScope .qmark).exit = .returnFn ∧
     (lowerSurfaceOp (.homogeneous bid) .qmark).exit = .breakBlock bid ∧
     (lowerSurfaceOp (.heterogeneous bid) .qmark).exit = .breakBlock bid ∧
     (lowerSurfaceOp (.homogeneous bid) .yeet).exit = .breakBlock bid) := by
  refine ⟨⟨homogeneous_qmark_determines_target env bid r o,
           homogeneous_qmark_rejects_heterogeneous_conversion env bid r o tSame tSuper⟩,
          fromResidual_scopes_admit_conversion_and_break_unannotated_inference
            env bid r o tSame tSuper hne hResSame hResSuper,
          yeet_bypasses_homogeneous_restriction
            env (.homogeneous bid) y o tSame tSuper hne hYeetSame hYeetSuper,
          ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Boundary lemma for `pub type Infallible = !` without blanket `impl<T> From<!> for T`:
because `<Result<T, F> as FromResidual<Result<!, E>>>` requires `F: From<E>`,
the absence of `From<!>` for `u32` makes `?` on `Result<u64, Infallible>` into
`Result<u64, u32>` inadmissible (`E0277`) despite `Infallible` being uninhabited. -/
theorem infallible_qmark_requires_from_witness
    {Ty : Type} (hasFrom : Ty → Ty → Prop) (env : TryEnv Ty)
    (resTy : Ty → Ty → Ty) (neverTy outTy targetErrTy : Ty)
    (hResultImpl :
      ∀ e f, env.fromResidual (resTy outTy f) (resTy neverTy e) ↔ hasFrom e f)
    (hNoBlanketFrom : ¬ hasFrom neverTy targetErrTy) :
    ¬ AdmissibleTarget env (lowerSurfaceOp .fnScope .qmark).langItem
        (resTy neverTy neverTy) outTy (resTy outTy targetErrTy) := by
  intro hAdm
  exact hNoBlanketFrom ((hResultImpl neverTy targetErrTy).mp hAdm)

-- ============================================================================
-- Section 2: `#[track_caller]` Caller-Location Forwarding Chain Invariant
--            (`Body::caller_location_span` vs. Runtime / Miri Call Stack)
-- ============================================================================

/-- One intermediate wrapper frame between the user's `?` / `do yeet` site and
the leaf `Location::caller()` invocation.
- `trackCaller = true` iff `InstanceKind::requires_caller_location(tcx) = true`.
- `innerCallSite` is the source location inside this wrapper where it calls the
  next inner frame (e.g., `try_trait.rs:384` inside `residual_into_try_type`, or
  `result.rs:2206` inside `<Result as FromResidual<Yeet<E>>>::from_residual`). -/
structure WrapperFrame (Loc : Type) : Type where
  trackCaller : Bool
  innerCallSite : Loc

/-- Top-down runtime / uninlined Miri call-stack evaluation (`outerToInner` order,
starting from the user call site `curLoc` and descending toward `Location::caller()`). -/
noncomputable def evalCallStackLoc {Loc : Type} (curLoc : Loc) :
    List (WrapperFrame Loc) → Loc
  | [] => curLoc
  | w :: rest =>
    evalCallStackLoc (match w.trackCaller with | true => curLoc | false => w.innerCallSite) rest

/-- Bottom-up MIR inlined-scope walk mirroring `Body::caller_location_span`
(`compiler/rustc_middle/src/mir/mod.rs:685-713`, `innerToOuter` order): stops
at the innermost wrapper with `trackCaller = false` and returns its
`innerCallSite`, falling back to `userSite` only if every wrapper forwards. -/
noncomputable def resolveInlinedScopeLoc {Loc : Type} :
    List (WrapperFrame Loc) → Loc → Loc
  | [], userSite => userSite
  | w :: rest, userSite =>
    match w.trackCaller with
    | true => resolveInlinedScopeLoc rest userSite
    | false => w.innerCallSite

/-- Structural helper: appending a single outermost wrapper at the end of an
inner-to-outer chain corresponds to updating the incoming location before the
remaining inner frames execute. -/
theorem resolveInlinedScopeLoc_append {Loc : Type}
    (inner : List (WrapperFrame Loc)) (wOuter : WrapperFrame Loc) (userSite : Loc) :
    resolveInlinedScopeLoc (inner ++ [wOuter]) userSite =
    resolveInlinedScopeLoc inner
      (match wOuter.trackCaller with | true => userSite | false => wOuter.innerCallSite) := by
  induction inner with
  | nil =>
    cases h : wOuter.trackCaller <;>
      simp only [List.nil_append, resolveInlinedScopeLoc, h]
  | cons w rest ih =>
    cases htc : w.trackCaller with
    | false =>
      simp only [List.cons_append, resolveInlinedScopeLoc, htc]
    | true =>
      simp only [List.cons_append, resolveInlinedScopeLoc, htc]
      exact ih

/-- Equivalence of top-down runtime/Miri stack propagation (`-O0`, Miri) and
bottom-up MIR `SourceScope.inlined` traversal (`-O2` inlined release builds). -/
theorem evalCallStackLoc_eq_resolveInlinedScopeLoc {Loc : Type}
    (outerToInner : List (WrapperFrame Loc)) (userSite : Loc) :
    evalCallStackLoc userSite outerToInner =
    resolveInlinedScopeLoc outerToInner.reverse userSite := by
  induction outerToInner generalizing userSite with
  | nil => rfl
  | cons w rest ih =>
    rw [List.reverse_cons, resolveInlinedScopeLoc_append]
    exact ih (match w.trackCaller with | true => userSite | false => w.innerCallSite)

/-- Universal wrapper-list predicate (`AllTrackCaller`). -/
noncomputable def AllTrackCaller {Loc : Type} : List (WrapperFrame Loc) → Prop
  | [] => True
  | w :: rest => w.trackCaller = true ∧ AllTrackCaller rest

theorem allTrackCaller_iff_forall {Loc : Type} (ws : List (WrapperFrame Loc)) :
    AllTrackCaller ws ↔ ∀ w, w ∈ ws → w.trackCaller = true := by
  induction ws with
  | nil =>
    constructor
    · intro _ w hw
      cases hw
    · intro _
      trivial
  | cons hd tl ih =>
    constructor
    · intro h w hw
      cases hw with
      | head => exact h.1
      | tail _ hmem => exact ih.mp h.2 w hmem
    · intro hall
      refine ⟨hall hd (List.Mem.head tl), ih.mpr ?_⟩
      intro w hw
      exact hall w (List.Mem.tail hd hw)

theorem allTrackCaller_reverse_iff {Loc : Type} (ws : List (WrapperFrame Loc)) :
    AllTrackCaller ws.reverse ↔ AllTrackCaller ws := by
  rw [allTrackCaller_iff_forall, allTrackCaller_iff_forall]
  constructor
  · intro h w hw
    exact h w (List.mem_reverse.mpr hw)
  · intro h w hw
    exact h w (List.mem_reverse.mp hw)

theorem resolveInlinedScopeLoc_of_allTrackCaller {Loc : Type}
    (innerToOuter : List (WrapperFrame Loc)) (userSite : Loc)
    (hall : AllTrackCaller innerToOuter) :
    resolveInlinedScopeLoc innerToOuter userSite = userSite := by
  induction innerToOuter with
  | nil => rfl
  | cons w rest ih =>
    simp only [resolveInlinedScopeLoc, hall.1]
    exact ih hall.2

theorem resolveInlinedScopeLoc_eq_user_implies_allTrackCaller {Loc : Type}
    (innerToOuter : List (WrapperFrame Loc)) (userSite : Loc)
    (hDistinct : ∀ w, w ∈ innerToOuter → w.innerCallSite ≠ userSite)
    (hEq : resolveInlinedScopeLoc innerToOuter userSite = userSite) :
    AllTrackCaller innerToOuter := by
  induction innerToOuter with
  | nil => trivial
  | cons w rest ih =>
    cases htc : w.trackCaller with
    | false =>
      simp only [resolveInlinedScopeLoc, htc] at hEq
      exact False.elim (hDistinct w (List.Mem.head rest) hEq)
    | true =>
      simp only [resolveInlinedScopeLoc, htc] at hEq
      refine ⟨htc, ih ?_ hEq⟩
      intro w' hw'
      exact hDistinct w' (List.Mem.tail w hw')

/-- Main Theorem 2: Caller-Location Forwarding Chain Invariant.
Assuming internal library wrapper call-sites are distinct from the user's site,
BOTH runtime/Miri stack forwarding and inlined MIR `Body::caller_location_span`
preserve `userSite` IF AND ONLY IF every intermediate wrapper in the chain carries
`#[track_caller]`. -/
theorem caller_location_preserved_iff_all_wrappers_track_caller
    {Loc : Type} (outerToInner : List (WrapperFrame Loc)) (userSite : Loc)
    (hDistinct : ∀ w, w ∈ outerToInner → w.innerCallSite ≠ userSite) :
    (evalCallStackLoc userSite outerToInner = userSite ∧
     resolveInlinedScopeLoc outerToInner.reverse userSite = userSite) ↔
    (∀ w, w ∈ outerToInner → w.trackCaller = true) := by
  rw [evalCallStackLoc_eq_resolveInlinedScopeLoc]
  rw [← allTrackCaller_iff_forall]
  constructor
  · intro hBoth
    have hDistRev : ∀ w, w ∈ outerToInner.reverse → w.innerCallSite ≠ userSite := by
      intro w hw
      exact hDistinct w (List.mem_reverse.mp hw)
    have hAllRev :=
      resolveInlinedScopeLoc_eq_user_implies_allTrackCaller
        outerToInner.reverse userSite hDistRev hBoth.1
    exact (allTrackCaller_reverse_iff outerToInner).mp hAllRev
  · intro hAll
    have hAllRev := (allTrackCaller_reverse_iff outerToInner).mpr hAll
    have hEq := resolveInlinedScopeLoc_of_allTrackCaller outerToInner.reverse userSite hAllRev
    exact ⟨hEq, hEq⟩

-- ============================================================================
-- Section 3: Edition 2021 vs. 2024 `Try::from_output` Tail Drop-Scope Flip
--            & Uninhabited Residual (`Infallible` / `!`) Dead-Arm Elimination
-- ============================================================================

/-- Rust edition selector for `rustc_hir_analysis::check::region::resolve_block`
(`compiler/rustc_hir_analysis/src/check/region.rs:145-162`). -/
inductive Edition : Type where
  | ed2021
  | ed2024

/-- Predicate stating that `a` appears strictly before `b` in a drop trace
(constructed inductively without arithmetic tactics). -/
inductive DropsBefore {Tag : Type} (a b : Tag) : List Tag → Prop where
  | head {tl : List Tag} (hb : b ∈ tl) : DropsBefore a b (a :: tl)
  | tail {x : Tag} {tl : List Tag} (h : DropsBefore a b tl) : DropsBefore a b (x :: tl)

theorem dropsBefore_append_right {Tag : Type} {a b : Tag} {xs ys : List Tag}
    (h : DropsBefore a b xs) : DropsBefore a b (xs ++ ys) := by
  induction h with
  | head hb =>
    exact DropsBefore.head (List.mem_append_left ys hb)
  | tail _ ih =>
    exact DropsBefore.tail ih

theorem dropsBefore_append_left {Tag : Type} {a b : Tag} {xs ys : List Tag}
    (h : DropsBefore a b ys) : DropsBefore a b (xs ++ ys) := by
  induction xs with
  | nil => exact h
  | cons x rest ih => exact DropsBefore.tail ih

theorem dropsBefore_cross_append {Tag : Type} {a b : Tag} {xs ys : List Tag}
    (ha : a ∈ xs) (hb : b ∈ ys) : DropsBefore a b (xs ++ ys) := by
  induction xs with
  | nil => cases ha
  | cons x rest ih =>
    cases ha with
    | head =>
      exact DropsBefore.head (List.mem_append_right rest hb)
    | tail _ hmem =>
      exact DropsBefore.tail (ih hmem)

/-- Drop trace emitted on normal exit of a `try { <stmts>; <tail> }` (or
`try bikeshed Ty { <stmts>; <tail> }`) block whose tail expression is desugared
to `Try::from_output(<tail>)` (`expr.rs:763-768`, `region.rs:145-162`):
- `stmtDropTrace`: drops from prior statements inside the block (always
  terminating scopes in both editions, `region.rs:243`).
- `blkLocals`: block-local `let` bindings in declaration order (dropped in
  reverse declaration order at block exit).
- `tailTemps`: temporaries created while evaluating `Try::from_output(<tail>)`
  in creation order (dropped in reverse creation order at their terminating scope).
In Edition 2021 (`terminating = false`), `blkLocals` drop before `tailTemps`;
in Edition 2024 (`terminating = true`), `tailTemps` drop before `blkLocals`. -/
noncomputable def tryBlockTailDropOrder {Tag : Type} (ed : Edition)
    (stmtDropTrace blkLocals tailTemps : List Tag) : List Tag :=
  match ed with
  | .ed2021 => stmtDropTrace ++ blkLocals.reverse ++ tailTemps.reverse
  | .ed2024 => stmtDropTrace ++ tailTemps.reverse ++ blkLocals.reverse

/-- Drop trace for statement-level `let x = scrut? + rhs;` (`Match` scrutinee
is not a terminating scope in either Edition 2021 or Edition 2024,
`region.rs:252-396`), preserving statement-LIFO `[rhsTmp, scrutTmp, fnLocal]` on
`Ok` and `[scrutTmp, fnLocal]` on `Err` across both editions. -/
noncomputable def subexprQmarkBinopDropOrder {Tag : Type} (_ed : Edition)
    (isOk : Bool) (scrutTmp rhsTmp fnLocal : Tag) : List Tag :=
  if isOk then [rhsTmp, scrutTmp, fnLocal] else [scrutTmp, fnLocal]

theorem subexprQmarkBinopDropOrder_edition_invariant {Tag : Type}
    (isOk : Bool) (scrutTmp rhsTmp fnLocal : Tag) :
    subexprQmarkBinopDropOrder .ed2021 isOk scrutTmp rhsTmp fnLocal =
    subexprQmarkBinopDropOrder .ed2024 isOk scrutTmp rhsTmp fnLocal := by
  rfl

theorem edition2024_drops_all_tail_temps_before_block_locals {Tag : Type}
    (stmtDropTrace blkLocals tailTemps : List Tag)
    (t l : Tag) (ht : t ∈ tailTemps) (hl : l ∈ blkLocals) :
    DropsBefore t l (tryBlockTailDropOrder .ed2024 stmtDropTrace blkLocals tailTemps) := by
  dsimp only [tryBlockTailDropOrder]
  rw [List.append_assoc]
  exact @dropsBefore_append_left Tag t l stmtDropTrace (tailTemps.reverse ++ blkLocals.reverse)
    (dropsBefore_cross_append (List.mem_reverse.mpr ht) (List.mem_reverse.mpr hl))

/-- `ControlFlow` value model mirroring `core::ops::ControlFlow<B, C>`. -/
inductive ControlFlowVal (R O : Type) : Type where
  | continue_ (val : O)
  | break_ (res : R)

/-- `Result` value model mirroring `core::result::Result<T, E>`. -/
inductive ResultVal (T E : Type) : Type where
  | ok (val : T)
  | err (err : E)

/-- Exact model of `<Result<T, E> as Try>::branch` (`library/core/src/result.rs:2181-2186`). -/
noncomputable def resultBranch {T E : Type} :
    ResultVal T E → ControlFlowVal (ResultVal Empty E) T
  | .ok v => .continue_ v
  | .err e => .break_ (.err e)

/-- Exact model of `Runtime(PostCleanup)` MIR for `fn f(r: Result<T, E>) -> Result<U, F> { let v = r?; Ok(k(v)) }`:
calls `Try::branch`, switches on `ControlFlow`, calls `FromResidual::from_residual` on `Break`,
and wraps `k(v)` in `Try::from_output` (`ResultVal.ok`) on `Continue`. -/
noncomputable def qmarkMirPostCleanup {T E U F : Type}
    (fromResidual : ResultVal Empty E → ResultVal U F)
    (k : T → U)
    (r : ResultVal T E) : ResultVal U F :=
  match resultBranch r with
  | .continue_ v => .ok (k v)
  | .break_ res => fromResidual res

/-- Exact model of `Runtime(Optimized)` 1-BB MIR for `qmark_infallible` when `E`
is uninhabited (`uninhab : E → Empty`): zero `SwitchInt`, zero `Unreachable`,
zero `from_residual` calls—direct payload extraction and `Ok(k(v))` construction. -/
noncomputable def qmarkMirOptimizedInfallible {T E U F : Type}
    (uninhab : E → Empty)
    (k : T → U)
    (r : ResultVal T E) : ResultVal U F :=
  match r with
  | .ok v => .ok (k v)
  | .err e => Empty.elim (uninhab e)

theorem qmark_infallible_branch_elim_sound {T E U F : Type}
    (uninhab : E → Empty)
    (fromResidual : ResultVal Empty E → ResultVal U F)
    (k : T → U)
    (r : ResultVal T E) :
    qmarkMirPostCleanup fromResidual k r = qmarkMirOptimizedInfallible uninhab k r := by
  cases r with
  | ok v => rfl
  | err e => exact Empty.elim (uninhab e)

/-- Main Theorem 3: Joint soundness of Edition 2024 `Try::from_output` tail
drop-scope ordering (every tail borrow-guard temporary drops before every block
local, while sub-expression `scrut? + rhs` remains edition-invariant) AND
uninhabited-residual (`Infallible` / `!`) dead-arm elimination from
`PostCleanup` MIR to single-block `Optimized` MIR. -/
theorem edition2024_try_tail_drop_and_infallible_branch_elim_sound
    {Tag T E U F : Type}
    (stmtDropTrace blkLocals tailTemps : List Tag)
    (scrutTmp rhsTmp fnLocal : Tag)
    (uninhab : E → Empty)
    (fromResidual : ResultVal Empty E → ResultVal U F)
    (k : T → U) :
    -- (a) In Edition 2024, every `Try::from_output` tail temporary drops strictly
    --     before every block-local binding (borrow-safe for `RefCell::borrow()`).
    (∀ t l, t ∈ tailTemps → l ∈ blkLocals →
      DropsBefore t l (tryBlockTailDropOrder .ed2024 stmtDropTrace blkLocals tailTemps)) ∧
    -- (b) Statement-level `scrut? + rhs` temporary drop order is edition-invariant.
    (∀ isOk, subexprQmarkBinopDropOrder .ed2021 isOk scrutTmp rhsTmp fnLocal =
             subexprQmarkBinopDropOrder .ed2024 isOk scrutTmp rhsTmp fnLocal) ∧
    -- (c) Eliminating the `ControlFlow::Break` switch arm and `from_residual` call
    --     for any uninhabited error type `E` preserves exact MIR semantics.
    (∀ r : ResultVal T E,
      qmarkMirPostCleanup fromResidual k r = qmarkMirOptimizedInfallible uninhab k r) := by
  refine ⟨fun t l ht hl =>
            edition2024_drops_all_tail_temps_before_block_locals
              stmtDropTrace blkLocals tailTemps t l ht hl,
          fun isOk => subexprQmarkBinopDropOrder_edition_invariant isOk scrutTmp rhsTmp fnLocal,
          fun r => qmark_infallible_branch_elim_sound uninhab fromResidual k r⟩

-- ============================================================================
-- Section 4: Constructive Sharpness Counterexamples (Exact Live `libcore` Bugs
--            and Edition 2021 Borrow-Checker Failure)
-- ============================================================================

/-- Concrete source-location witnesses matching the audited `libcore` lines and
user probe sites (zero collision between library internals and user lines). -/
inductive ConcreteLoc : Type where
  | userHomoQmarkLine101
  | userResultYeetLine119
  | coreTryTraitLine349_fromYeet
  | coreTryTraitLine384_residualIntoTryType
  | coreResultLine2206_yeetFromResidual
  | userMyTryLine52_fromResidual
  | userTrackedErrLine19_from

/-- Helper proving `DropsBefore` irreflexivity on two-element reversed traces. -/
theorem not_dropsBefore_reversed_pair {Tag : Type} {a b : Tag} (hne : a ≠ b) :
    ¬ DropsBefore b a [a, b] := by
  intro h
  cases h with
  | head _ =>
    exact hne rfl
  | tail h' =>
    cases h' with
    | head hb =>
      cases hb
    | tail h'' =>
      cases h''

/-- Constructive Sharpness Counterexample 1 (Live Bug 1: `try_trait.rs:381`):
Because `core::ops::try_trait::residual_into_try_type` omits `#[track_caller]`,
homogeneous `try { mk_my_err()? }` reports `library/core/src/ops/try_trait.rs:384`
in BOTH uninlined (`-O0`/Miri) and inlined (`-O2`) modes, whereas adding
`#[track_caller]` to `residual_into_try_type` (or using `try bikeshed`) restores
exact user line preservation. -/
theorem ce1_residual_into_try_type_drops_caller_location :
    let buggyChain : List (WrapperFrame ConcreteLoc) :=
      [ { trackCaller := false, innerCallSite := .coreTryTraitLine384_residualIntoTryType }
      , { trackCaller := true,  innerCallSite := .userMyTryLine52_fromResidual }
      ]
    let fixedChain : List (WrapperFrame ConcreteLoc) :=
      [ { trackCaller := true,  innerCallSite := .coreTryTraitLine384_residualIntoTryType }
      , { trackCaller := true,  innerCallSite := .userMyTryLine52_fromResidual }
      ]
    evalCallStackLoc .userHomoQmarkLine101 buggyChain =
      .coreTryTraitLine384_residualIntoTryType ∧
    resolveInlinedScopeLoc buggyChain.reverse .userHomoQmarkLine101 =
      .coreTryTraitLine384_residualIntoTryType ∧
    evalCallStackLoc .userHomoQmarkLine101 buggyChain ≠ .userHomoQmarkLine101 ∧
    evalCallStackLoc .userHomoQmarkLine101 fixedChain = .userHomoQmarkLine101 ∧
    resolveInlinedScopeLoc fixedChain.reverse .userHomoQmarkLine101 = .userHomoQmarkLine101 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  intro h
  cases h

/-- Constructive Sharpness Counterexample 2 (Live Bug 2: `result.rs:2203-2208`):
Even though `core::ops::try_trait::from_yeet` carries `#[track_caller]`,
`<Result<T, F> as FromResidual<Yeet<E>>>::from_residual` omits `#[track_caller]`,
so `do yeet e` into `Result` reports `library/core/src/result.rs:2206` in BOTH
uninlined and inlined modes, whereas adding `#[track_caller]` to `Result`'s
`FromResidual<Yeet<E>>` impl (matching custom `FromResidual<Yeet<E>>` impls)
restores exact user line preservation. -/
theorem ce2_result_yeet_impl_drops_caller_location :
    let buggyChain : List (WrapperFrame ConcreteLoc) :=
      [ { trackCaller := true,  innerCallSite := .coreTryTraitLine349_fromYeet }
      , { trackCaller := false, innerCallSite := .coreResultLine2206_yeetFromResidual }
      , { trackCaller := true,  innerCallSite := .userTrackedErrLine19_from }
      ]
    let fixedChain : List (WrapperFrame ConcreteLoc) :=
      [ { trackCaller := true,  innerCallSite := .coreTryTraitLine349_fromYeet }
      , { trackCaller := true,  innerCallSite := .coreResultLine2206_yeetFromResidual }
      , { trackCaller := true,  innerCallSite := .userTrackedErrLine19_from }
      ]
    evalCallStackLoc .userResultYeetLine119 buggyChain =
      .coreResultLine2206_yeetFromResidual ∧
    resolveInlinedScopeLoc buggyChain.reverse .userResultYeetLine119 =
      .coreResultLine2206_yeetFromResidual ∧
    evalCallStackLoc .userResultYeetLine119 buggyChain ≠ .userResultYeetLine119 ∧
    evalCallStackLoc .userResultYeetLine119 fixedChain = .userResultYeetLine119 ∧
    resolveInlinedScopeLoc fixedChain.reverse .userResultYeetLine119 = .userResultYeetLine119 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  intro h
  cases h

/-- Drop tags for `try { let c = RefCell::new(41); *c.borrow() + 1 }`. -/
inductive RefCellDropTag : Type where
  | localC
  | borrowGuardTemp

/-- Constructive Sharpness Counterexample 3 (Edition 2021 `E0597` vs. Edition 2024):
In `try { let c = RefCell::new(41); *c.borrow() + 1 }`, Edition 2021 drops the
owned local `c` BEFORE the `Ref<'_, u32>` tail temporary (`DropsBefore localC
borrowGuardTemp` and `¬ DropsBefore borrowGuardTemp localC`), causing `E0597`,
whereas Edition 2024 drops `borrowGuardTemp` strictly BEFORE `localC`. -/
theorem ce3_edition2021_try_tail_drops_local_before_borrow_temp :
    tryBlockTailDropOrder .ed2021 ([] : List RefCellDropTag)
      [.localC] [.borrowGuardTemp] = [.localC, .borrowGuardTemp] ∧
    DropsBefore RefCellDropTag.localC RefCellDropTag.borrowGuardTemp
      (tryBlockTailDropOrder .ed2021 [] [.localC] [.borrowGuardTemp]) ∧
    ¬ DropsBefore RefCellDropTag.borrowGuardTemp RefCellDropTag.localC
      (tryBlockTailDropOrder .ed2021 [] [.localC] [.borrowGuardTemp]) ∧
    tryBlockTailDropOrder .ed2024 ([] : List RefCellDropTag)
      [.localC] [.borrowGuardTemp] = [.borrowGuardTemp, .localC] ∧
    DropsBefore RefCellDropTag.borrowGuardTemp RefCellDropTag.localC
      (tryBlockTailDropOrder .ed2024 [] [.localC] [.borrowGuardTemp]) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩
  · exact DropsBefore.head (List.Mem.head [])
  · apply not_dropsBefore_reversed_pair
    intro h
    cases h
  · exact DropsBefore.head (List.Mem.head [])

end TryTraitResidualCallerAndDropSoundness
