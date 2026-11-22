/-!
# Soundness of `rustc` GCA `const` Item Definitional Normalization, Acyclic `is_trivial_const`
# Termination, and Constructive Sharpness Counterexamples Against `generic_const_exprs`

Standalone, zero-import, axiom-free Lean `v4.34.1` formalization grounded in:
- `compiler/rustc_middle/src/ty/context.rs` (`TyCtxt::next_trait_solver_globally`)
- `compiler/rustc_ast_passes/src/feature_gate.rs` (`warn_next_solver_and_gce`,
  `check_features_requiring_new_solver`)
- `compiler/rustc_mir_transform/src/trivial_const.rs` (`trivial_const`)
- `compiler/rustc_hir_analysis/src/collect.rs` (`const_of_item`)
- `compiler/rustc_next_trait_solver/src/solve/normalizes_to.rs` (`ProjectionConst`)
- `compiler/rustc_next_trait_solver/src/solve/project_goals/{free_alias,inherent,anon_const}.rs`
- `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs` (`evaluate_const`)
- `compiler/rustc_middle/src/ty/relate.rs` (`Relate for ty::Expr`)
- `compiler/rustc_trait_selection/src/traits/const_evaluatable.rs` (`is_const_evaluatable`)
- `compiler/rustc_trait_selection/src/traits/fulfill.rs` (`PredicateKind::ConstEquate`)

TCB discipline:
- `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`,
  `0` `partial def`, `0` `._unsafe_rec` (every recursive or dependent value definition carries
  explicit `noncomputable def` without `noncomputable section`, matching Anneal's
  `Trusted.MirAst` declaration hygiene).
-/

namespace GcaTrivialConstNormalizationSoundness

/-! ## Section 1: Solver Mode and Feature Gate Interaction (`#160895` / `gca_const_items`) -/

inductive CliNextSolver where
  | coherence
  | globally

inductive EffectiveSolver where
  | oldCoherence
  | nextGlobally

structure CrateFeatureConfig where
  cliNextSolver : CliNextSolver
  higherRankedAssumptions : Bool
  genericConstExprs : Bool
  gcaMinConstItems : Bool
  gcaConstItems : Bool

noncomputable def CliNextSolver.beq : CliNextSolver → CliNextSolver → Bool
  | .coherence, .coherence => true
  | .globally, .globally => true
  | _, _ => false

noncomputable def EffectiveSolver.beq : EffectiveSolver → EffectiveSolver → Bool
  | .oldCoherence, .oldCoherence => true
  | .nextGlobally, .nextGlobally => true
  | _, _ => false

/-- Mirrors `TyCtxt::next_trait_solver_globally`
(`compiler/rustc_middle/src/ty/context.rs:3150-3154`). -/
noncomputable def effectiveSolverMode (cfg : CrateFeatureConfig) : EffectiveSolver :=
  match cfg.cliNextSolver with
  | .globally =>
      match cfg.higherRankedAssumptions, cfg.genericConstExprs with
      | false, false => .nextGlobally
      | _, _ => .oldCoherence
  | .coherence => .oldCoherence

/-- Mirrors `check_features_requiring_new_solver`
(`compiler/rustc_ast_passes/src/feature_gate.rs:763-783`) and
`DEPENDENT_FEATURES` (`compiler/rustc_feature/src/unstable.rs:907`). -/
noncomputable def gcaConstItemsEffectiveAllowed (cfg : CrateFeatureConfig) : Bool :=
  cfg.gcaMinConstItems && EffectiveSolver.beq (effectiveSolverMode cfg) .nextGlobally

/-- Mirrors `warn_next_solver_and_gce`
(`compiler/rustc_ast_passes/src/feature_gate.rs:735-751`). -/
noncomputable def emitsGceDowngradeWarning (cfg : CrateFeatureConfig) : Bool :=
  CliNextSolver.beq cfg.cliNextSolver .globally && cfg.genericConstExprs

theorem gce_reverts_default_next_solver (cfg : CrateFeatureConfig)
    (h_gce : cfg.genericConstExprs = true) :
    effectiveSolverMode cfg = .oldCoherence := by
  unfold effectiveSolverMode
  cases cfg.cliNextSolver with
  | coherence => rfl
  | globally =>
      rw [h_gce]
      cases cfg.higherRankedAssumptions <;> rfl

theorem gce_emits_warning_under_nightly_default (cfg : CrateFeatureConfig)
    (h_cli : cfg.cliNextSolver = .globally)
    (h_gce : cfg.genericConstExprs = true) :
    emitsGceDowngradeWarning cfg = true := by
  unfold emitsGceDowngradeWarning
  rw [h_cli, h_gce]
  rfl

theorem gce_disables_effective_gca_const_items (cfg : CrateFeatureConfig)
    (h_gce : cfg.genericConstExprs = true) :
    gcaConstItemsEffectiveAllowed cfg = false := by
  unfold gcaConstItemsEffectiveAllowed
  rw [gce_reverts_default_next_solver cfg h_gce]
  cases cfg.gcaMinConstItems <;> rfl

theorem gca_preserves_next_solver_globally (cfg : CrateFeatureConfig)
    (h_cli : cfg.cliNextSolver = .globally)
    (h_no_hra : cfg.higherRankedAssumptions = false)
    (h_no_gce : cfg.genericConstExprs = false)
    (h_min : cfg.gcaMinConstItems = true) :
    effectiveSolverMode cfg = .nextGlobally ∧
    gcaConstItemsEffectiveAllowed cfg = true ∧
    emitsGceDowngradeWarning cfg = false := by
  have h_eff : effectiveSolverMode cfg = .nextGlobally := by
    unfold effectiveSolverMode
    rw [h_cli, h_no_hra, h_no_gce]
  have h_allow : gcaConstItemsEffectiveAllowed cfg = true := by
    unfold gcaConstItemsEffectiveAllowed
    rw [h_min, h_eff]
    rfl
  have h_warn : emitsGceDowngradeWarning cfg = false := by
    unfold emitsGceDowngradeWarning
    rw [h_cli, h_no_gce]
    rfl
  exact ⟨h_eff, h_allow, h_warn⟩

/-! ## Section 2: `is_trivial_const` Graph, Acyclicity, Total Termination, and `E0391` Cycle Detection -/

abbrev ConstId := Nat

/-- Abstracted single-block MIR shape inspected by `trivial_const`
(`compiler/rustc_mir_transform/src/trivial_const.rs:79-113`). -/
inductive TrivialConstDef where
  /-- Single BB, `_0 = const Val(v); return;` (`Const::Val`). -/
  | lit (v : Nat)
  /-- Single BB, `_0 = const Unevaluated(target, []); return;` (`Const::Unevaluated` with empty args). -/
  | alias (target : ConstId)
  /-- Non-trivial body (non-empty generic args, multiple BBs, arithmetic/assert, opaque types, etc.). -/
  | nonTrivial

abbrev TrivialEnv := ConstId → TrivialConstDef

inductive TrivialOutcome where
  | ok (v : Nat)
  | cycleDetected
  | nonTrivial
  | outOfFuel

/-- Structural membership test on `List ConstId` (explicit `noncomputable def` -> 0 `._unsafe_rec`). -/
noncomputable def containsId (x : ConstId) : List ConstId → Bool
  | [] => false
  | y :: ys =>
      match Nat.beq x y with
      | true => true
      | false => containsId x ys

/-- Fuel-bounded traversal of `trivial_const` chains without visited tracking. -/
noncomputable def evalTrivialFuel (env : TrivialEnv) : Nat → ConstId → TrivialOutcome
  | 0, _ => .outOfFuel
  | fuel + 1, id =>
      match env id with
      | .lit v => .ok v
      | .alias tgt => evalTrivialFuel env fuel tgt
      | .nonTrivial => .nonTrivial

/-- Query-stack cycle-detecting traversal mirroring `trivial_const(A) -> mir_built(A) -> trivial_const(B)`
and `rustc`'s `E0391` active-query stack check. -/
noncomputable def evalTrivialVisited (env : TrivialEnv) :
    Nat → List ConstId → ConstId → TrivialOutcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, visited, id =>
      match containsId id visited with
      | true => .cycleDetected
      | false =>
          match env id with
          | .lit v => .ok v
          | .alias tgt => evalTrivialVisited env fuel (id :: visited) tgt
          | .nonTrivial => .nonTrivial

/-- A rank-witnessed acyclic `TrivialConst` environment: every `id` is either a literal or an
alias pointing strictly downward in `rank` (so no cycles and no `nonTrivial` nodes exist). -/
structure AcyclicTrivialEnv (env : TrivialEnv) (rank : ConstId → Nat) : Prop where
  no_nonTrivial : ∀ id, env id ≠ .nonTrivial
  rank_decreases : ∀ id tgt, env id = .alias tgt → rank tgt < rank id

/-- Helper: `containsId x xs = false` whenever every element in `xs` differs from `x`. -/
theorem containsId_false_of_forall_ne {x : ConstId} {xs : List ConstId}
    (h : ∀ y, y ∈ xs → x ≠ y) : containsId x xs = false := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      unfold containsId
      have hne : x ≠ y := h y (List.Mem.head ys)
      have hbeq : Nat.beq x y = false := by
        cases hq : Nat.beq x y with
        | false => rfl
        | true => exact False.elim (hne (Nat.eq_of_beq_eq_true hq))
      rw [hbeq]
      exact ih (fun z hz => h z (List.Mem.tail y hz))

/-- Arithmetic helper without `omega`: `a < b → b ≤ n → a ≤ n - 1` phrased via `b ≤ n + 1 → a ≤ n`. -/
theorem nat_le_of_lt_of_le_succ {a b n : Nat} (hlt : a < b) (hle : b ≤ n + 1) : a ≤ n :=
  Nat.le_of_succ_le_succ (Nat.le_trans hlt hle)

/-- Core termination theorem: in any `AcyclicTrivialEnv`, every `id` with `rank id ≤ b`
evaluates to `.ok v` in at most `b + 1` steps. -/
theorem evalTrivialFuel_total_of_rank {env : TrivialEnv} {rank : ConstId → Nat}
    (hAcyc : AcyclicTrivialEnv env rank) :
    ∀ (b : Nat) (id : ConstId) (fuel : Nat),
      rank id ≤ b → b + 1 ≤ fuel →
      ∃ v, evalTrivialFuel env fuel id = .ok v := by
  intro b
  induction b with
  | zero =>
      intro id fuel hle hfuel
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero 0 hfuel)
      | succ f =>
          unfold evalTrivialFuel
          cases hdef : env id with
          | lit v => exact ⟨v, rfl⟩
          | nonTrivial => exact False.elim (hAcyc.no_nonTrivial id hdef)
          | alias tgt =>
              have hlt : rank tgt < rank id := hAcyc.rank_decreases id tgt hdef
              have hlt0 : rank tgt < 0 := Nat.lt_of_lt_of_le hlt hle
              exact False.elim (Nat.not_lt_zero (rank tgt) hlt0)
  | succ b ih =>
      intro id fuel hle hfuel
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero (b + 1) hfuel)
      | succ f =>
          unfold evalTrivialFuel
          cases hdef : env id with
          | lit v => exact ⟨v, rfl⟩
          | nonTrivial => exact False.elim (hAcyc.no_nonTrivial id hdef)
          | alias tgt =>
              have hlt : rank tgt < rank id := hAcyc.rank_decreases id tgt hdef
              have htgt_le : rank tgt ≤ b := nat_le_of_lt_of_le_succ hlt hle
              have hf_ge : b + 1 ≤ f := Nat.le_of_succ_le_succ hfuel
              exact ih tgt f htgt_le hf_ge

/-- Fuel monotonicity / confluence: once `evalTrivialFuel` reaches `.ok v`, any larger fuel
yields the identical value `.ok v`. -/
theorem evalTrivialFuel_monotone {env : TrivialEnv} :
    ∀ (k k' : Nat) (id : ConstId) (v : Nat),
      evalTrivialFuel env k id = .ok v → k ≤ k' →
      evalTrivialFuel env k' id = .ok v := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ h _
      cases h
  | succ k ih =>
      intro k' id v h hk
      cases k' with
      | zero => exact False.elim (Nat.not_succ_le_zero k hk)
      | succ k' =>
          unfold evalTrivialFuel at h ⊢
          cases hdef : env id with
          | lit w =>
              rw [hdef] at h
              exact h
          | nonTrivial =>
              rw [hdef] at h
              cases h
          | alias tgt =>
              rw [hdef] at h
              exact ih k' tgt v h (Nat.le_of_succ_le_succ hk)

/-- Cycle-checked DFS agrees identically with fuel evaluation on every acyclic graph whenever
the active query stack strictly dominates `rank id` (in particular, when `visited = []`). -/
theorem evalTrivialVisited_eq_fuel_of_acyclic {env : TrivialEnv} {rank : ConstId → Nat}
    (hAcyc : AcyclicTrivialEnv env rank) :
    ∀ (fuel : Nat) (visited : List ConstId) (id : ConstId),
      (∀ y, y ∈ visited → rank id < rank y) →
      evalTrivialVisited env fuel visited id = evalTrivialFuel env fuel id := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ _
      rfl
  | succ f ih =>
      intro visited id hdom
      unfold evalTrivialVisited evalTrivialFuel
      have hnotmem : containsId id visited = false := by
        apply containsId_false_of_forall_ne
        intro y hy heq
        have hlt : rank id < rank y := hdom y hy
        rw [heq] at hlt
        exact Nat.lt_irrefl (rank y) hlt
      rw [hnotmem]
      cases hdef : env id with
      | lit v => rfl
      | nonTrivial => rfl
      | alias tgt =>
          have hlt : rank tgt < rank id := hAcyc.rank_decreases id tgt hdef
          apply ih (id :: visited) tgt
          intro y hy
          cases hy with
          | head => exact hlt
          | tail _ htail => exact Nat.lt_trans hlt (hdom y htail)

/-- Monomorphization substitution mapping const-generic parameter slots to concrete `usize` values.
Because `trivial_const` rejects non-empty generic args (`trivial_const.rs:106-108`) and accepts
only already-computed `Const::Val` or parameterless `Const::Unevaluated` chains, monomorphizing
an acyclic `TrivialConst` under ANY substitution `σ` is invariant and total (zero `E0080` fault). -/
abbrev MonoSubst := Nat → Nat

noncomputable def evalTrivialAtMono (env : TrivialEnv) (_σ : MonoSubst)
    (fuel : Nat) (id : ConstId) : TrivialOutcome :=
  evalTrivialVisited env fuel [] id

/-- **Theorem 1 (`acyclicTrivialConst_norm_total_no_post_mono_fault`)**:
In any rank-witnessed acyclic `TrivialConst` graph (`AcyclicTrivialEnv env rank`), for every
constant `id`, there exists a unique concrete value `v : Nat` such that for EVERY fuel
`fuel ≥ rank id + 1` and EVERY monomorphization substitution `σ : MonoSubst`:
1. Cycle-checked evaluation terminates with `.ok v` (never `.cycleDetected`, `.nonTrivial`,
   or `.outOfFuel`);
2. The result is independent of `fuel` (confluence) and independent of `σ` (total across all
   monomorphizations with zero post-monomorphization `E0080` faults). -/
theorem acyclicTrivialConst_norm_total_no_post_mono_fault
    {env : TrivialEnv} {rank : ConstId → Nat}
    (hAcyc : AcyclicTrivialEnv env rank)
    (id : ConstId) :
    ∃ v : Nat, ∀ (fuel : Nat) (σ : MonoSubst),
      rank id + 1 ≤ fuel →
      evalTrivialAtMono env σ fuel id = .ok v ∧
      evalTrivialAtMono env σ fuel id ≠ .cycleDetected ∧
      evalTrivialAtMono env σ fuel id ≠ .nonTrivial ∧
      evalTrivialAtMono env σ fuel id ≠ .outOfFuel := by
  have hbase := evalTrivialFuel_total_of_rank hAcyc (rank id) id (rank id + 1)
    (Nat.le_refl (rank id)) (Nat.le_refl (rank id + 1))
  cases hbase with
  | intro v hv =>
      refine ⟨v, ?_⟩
      intro fuel σ hfuel
      have hmono : evalTrivialFuel env fuel id = .ok v :=
        evalTrivialFuel_monotone (rank id + 1) fuel id v hv hfuel
      have hvis : evalTrivialVisited env fuel [] id = evalTrivialFuel env fuel id :=
        evalTrivialVisited_eq_fuel_of_acyclic hAcyc fuel [] id (fun _ h => nomatch h)
      have heq : evalTrivialAtMono env σ fuel id = .ok v := by
        unfold evalTrivialAtMono
        rw [hvis, hmono]
      refine ⟨heq, ?_, ?_, ?_⟩
      · rw [heq]; intro h; cases h
      · rw [heq]; intro h; cases h
      · rw [heq]; intro h; cases h

/-! ## Section 3: GCA Definitional Projection Normalization Under `-Znext-solver=globally` -/

abbrev TyParamId := Nat
abbrev ImplTyId := Nat
abbrev TraitId := Nat
abbrev AssocId := Nat

/-- Type-level self type for `<Self as Trait>::ASSOC` projections. -/
inductive SelfTy where
  | param (p : TyParamId)
  | concrete (c : ImplTyId)

/-- Mirrors `rustc_type_ir::const_kind::ConstKind` + `AliasConstKind` for GCA direct consts. -/
inductive GcaConstTerm where
  | lit (n : Nat)
  | constParam (p : Nat)
  | freeAlias (id : ConstId)
  | projAlias (selfTy : SelfTy) (tr : TraitId) (assoc : AssocId)

/-- Normalized constant terms produced by `rustc_next_trait_solver::solve::normalizes_to`
and `eval_ctxt::evaluate_const`. Rigid aliases represent un-evaluable generic items under
`gca_const_items` (`IsRigid::Yes`, `eval_ctxt/mod.rs:1690-1695`). -/
inductive GcaNormConst where
  | val (n : Nat)
  | rigidParam (p : Nat)
  | rigidFree (id : ConstId)
  | rigidProj (selfTy : SelfTy) (tr : TraitId) (assoc : AssocId)
  | err

/-- Array / primitive types parameterized by a GCA const term. -/
inductive GcaTy where
  | u8
  | array (elem : GcaTy) (len : GcaConstTerm)

/-- Normalized types whose array lengths have been reduced to `GcaNormConst`. -/
inductive GcaNormTy where
  | u8
  | array (elem : GcaNormTy) (len : GcaNormConst)

/-- Mirrors `const_of_item` (`compiler/rustc_hir_analysis/src/collect.rs:1844-1879`):
returns `some rhs` iff the const item was defined with `core::gca!(rhs)` (`ConstItemRhs::Direct`). -/
structure DirectConstTable where
  freeDef : ConstId → Option GcaConstTerm
  projDef : ImplTyId → TraitId → AssocId → Option GcaConstTerm

/-- Mirrors `normalizes_to.rs:464-486` (`ProjectionConst`), `free_alias.rs:36-53` (`FreeConst`),
and `eval_ctxt/mod.rs:1677-1695` (`IsRigid::Yes` fallback for generic items under `gca_const_items`).
Notice that **no `where [(); ...]:` (`ConstEvaluatable`) table is queried** under GCA. -/
noncomputable def normalizeGcaConst (tbl : DirectConstTable) (cfg : CrateFeatureConfig) :
    Nat → GcaConstTerm → GcaNormConst
  | 0, _ => .err
  | fuel + 1, term =>
      match gcaConstItemsEffectiveAllowed cfg with
      | true =>
          match term with
          | .lit n => .val n
          | .constParam p => .rigidParam p
          | .freeAlias id =>
              match tbl.freeDef id with
              | some rhs => normalizeGcaConst tbl cfg fuel rhs
              | none => .rigidFree id
          | .projAlias selfTy tr assoc =>
              match selfTy with
              | .concrete c =>
                  match tbl.projDef c tr assoc with
                  | some rhs => normalizeGcaConst tbl cfg fuel rhs
                  | none => .rigidProj (.concrete c) tr assoc
              | .param p => .rigidProj (.param p) tr assoc
      | false => .err

noncomputable def normalizeGcaTy (tbl : DirectConstTable) (cfg : CrateFeatureConfig) (fuel : Nat) :
    GcaTy → GcaNormTy
  | .u8 => .u8
  | .array elem len =>
      .array (normalizeGcaTy tbl cfg fuel elem) (normalizeGcaConst tbl cfg fuel len)

/-- Explicit structural equality on `SelfTy` (pure kernel `Bool`, zero `._unsafe_rec`). -/
noncomputable def SelfTy.beq : SelfTy → SelfTy → Bool
  | .param a, .param b => Nat.beq a b
  | .concrete a, .concrete b => Nat.beq a b
  | _, _ => false

theorem SelfTy.beq_refl (s : SelfTy) : SelfTy.beq s s = true := by
  cases s with
  | param a => exact Nat.beq_refl a
  | concrete a => exact Nat.beq_refl a

/-- Definitional unification of normalized types under `-Znext-solver=globally`
(structural equality after normalization, with `.err` failing closed). -/
noncomputable def unifyGcaNormConst : GcaNormConst → GcaNormConst → Bool
  | .val a, .val b => Nat.beq a b
  | .rigidParam a, .rigidParam b => Nat.beq a b
  | .rigidFree a, .rigidFree b => Nat.beq a b
  | .rigidProj s1 t1 a1, .rigidProj s2 t2 a2 =>
      SelfTy.beq s1 s2 && Nat.beq t1 t2 && Nat.beq a1 a2
  | _, _ => false

theorem unifyGcaNormConst_refl_nonErr {c : GcaNormConst} (hne : c ≠ .err) :
    unifyGcaNormConst c c = true := by
  cases c with
  | val a => exact Nat.beq_refl a
  | rigidParam a => exact Nat.beq_refl a
  | rigidFree a => exact Nat.beq_refl a
  | rigidProj s t a =>
      dsimp only [unifyGcaNormConst]
      rw [SelfTy.beq_refl s, Nat.beq_refl t, Nat.beq_refl a]
      rfl
  | err => exact False.elim (hne rfl)

noncomputable def unifyGcaNormTy : GcaNormTy → GcaNormTy → Bool
  | .u8, .u8 => true
  | .array e1 l1, .array e2 l2 => unifyGcaNormTy e1 e2 && unifyGcaNormConst l1 l2
  | _, _ => false

/-- Type-parameter substitution `T ↦ concrete implId` on `GcaConstTerm` and `GcaTy`. -/
noncomputable def substSelfTy (p : TyParamId) (c : ImplTyId) : SelfTy → SelfTy
  | .param q =>
      match Nat.beq p q with
      | true => .concrete c
      | false => .param q
  | .concrete d => .concrete d

noncomputable def substGcaConst (p : TyParamId) (c : ImplTyId) : GcaConstTerm → GcaConstTerm
  | .lit n => .lit n
  | .constParam k => .constParam k
  | .freeAlias id => .freeAlias id
  | .projAlias s tr assoc => .projAlias (substSelfTy p c s) tr assoc

noncomputable def substGcaTy (p : TyParamId) (c : ImplTyId) : GcaTy → GcaTy
  | .u8 => .u8
  | .array elem len => .array (substGcaTy p c elem) (substGcaConst p c len)

/-- **Theorem 2 (`gca_assoc_const_unifies_with_literal`)**:
Under default `-Znext-solver=globally` with `gca_min_const_items = true`, `generic_const_exprs = false`,
and `higher_ranked_assumptions = false` — and with **zero `where [(); ...]:` bounds** — whenever an
impl `c` defines `const ASSOC: usize = core::gca!(n)` (`tbl.projDef c tr assoc = some (.lit n)`),
the array type `[u8; core::gca!(<c as Tr>::ASSOC)]` normalizes definitionally to `[u8; n]` and
unifies cleanly with `[u8; n]` for every `fuel ≥ 2`. -/
theorem gca_assoc_const_unifies_with_literal
    (tbl : DirectConstTable) (cfg : CrateFeatureConfig)
    (c : ImplTyId) (tr : TraitId) (assoc : AssocId) (n fuel : Nat)
    (h_cli : cfg.cliNextSolver = .globally)
    (h_no_hra : cfg.higherRankedAssumptions = false)
    (h_no_gce : cfg.genericConstExprs = false)
    (h_min : cfg.gcaMinConstItems = true)
    (h_impl : tbl.projDef c tr assoc = some (.lit n))
    (h_fuel : 2 ≤ fuel) :
    let lhs := normalizeGcaTy tbl cfg fuel (.array .u8 (.projAlias (.concrete c) tr assoc))
    let rhs := normalizeGcaTy tbl cfg fuel (.array .u8 (.lit n))
    lhs = .array .u8 (.val n) ∧
    rhs = .array .u8 (.val n) ∧
    unifyGcaNormTy lhs rhs = true := by
  have h_ok : gcaConstItemsEffectiveAllowed cfg = true :=
    (gca_preserves_next_solver_globally cfg h_cli h_no_hra h_no_gce h_min).2.1
  cases fuel with
  | zero => exact False.elim (Nat.not_succ_le_zero 1 h_fuel)
  | succ f1 =>
      cases f1 with
      | zero => exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ h_fuel))
      | succ f2 =>
          have h_lhs :
              normalizeGcaTy tbl cfg (f2 + 2) (.array .u8 (.projAlias (.concrete c) tr assoc)) =
              .array .u8 (.val n) := by
            dsimp only [normalizeGcaTy, normalizeGcaConst]
            rw [h_ok]
            dsimp only
            rw [h_impl]
          have h_rhs :
              normalizeGcaTy tbl cfg (f2 + 2) (.array .u8 (.lit n)) =
              .array .u8 (.val n) := by
            dsimp only [normalizeGcaTy, normalizeGcaConst]
            rw [h_ok]
          refine ⟨h_lhs, h_rhs, ?_⟩
          rw [h_lhs, h_rhs]
          dsimp only [unifyGcaNormTy, unifyGcaNormConst]
          rw [Nat.beq_refl n]
          rfl

/-- Multi-hop definitional normalization corollary: `<c as Tr>::ASSOC` defined as
`core::gca!(FREE_CONST)` where `FREE_CONST = core::gca!(n)` also unifies definitionally with
`[u8; n]` in `fuel ≥ 3` without any `where [(); ...]:` bound. -/
theorem gca_chained_assoc_to_free_const_unifies_with_literal
    (tbl : DirectConstTable) (cfg : CrateFeatureConfig)
    (c : ImplTyId) (tr : TraitId) (assoc : AssocId) (fid : ConstId) (n fuel : Nat)
    (h_cli : cfg.cliNextSolver = .globally)
    (h_no_hra : cfg.higherRankedAssumptions = false)
    (h_no_gce : cfg.genericConstExprs = false)
    (h_min : cfg.gcaMinConstItems = true)
    (h_impl : tbl.projDef c tr assoc = some (.freeAlias fid))
    (h_free : tbl.freeDef fid = some (.lit n))
    (h_fuel : 3 ≤ fuel) :
    let lhs := normalizeGcaTy tbl cfg fuel (.array .u8 (.projAlias (.concrete c) tr assoc))
    let rhs := normalizeGcaTy tbl cfg fuel (.array .u8 (.lit n))
    unifyGcaNormTy lhs rhs = true := by
  have h_ok : gcaConstItemsEffectiveAllowed cfg = true :=
    (gca_preserves_next_solver_globally cfg h_cli h_no_hra h_no_gce h_min).2.1
  cases fuel with
  | zero => exact False.elim (Nat.not_succ_le_zero 2 h_fuel)
  | succ f1 =>
      cases f1 with
      | zero => exact False.elim (Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ h_fuel))
      | succ f2 =>
          cases f2 with
          | zero =>
              exact False.elim
                (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h_fuel)))
          | succ f3 =>
              have h_lhs :
                  normalizeGcaTy tbl cfg (f3 + 3) (.array .u8 (.projAlias (.concrete c) tr assoc)) =
                  .array .u8 (.val n) := by
                dsimp only [normalizeGcaTy, normalizeGcaConst]
                rw [h_ok]
                dsimp only
                rw [h_impl]
                dsimp only [normalizeGcaConst]
                rw [h_free]
              have h_rhs :
                  normalizeGcaTy tbl cfg (f3 + 3) (.array .u8 (.lit n)) =
                  .array .u8 (.val n) := by
                dsimp only [normalizeGcaTy, normalizeGcaConst]
                rw [h_ok]
              rw [h_lhs, h_rhs]
              dsimp only [unifyGcaNormTy, unifyGcaNormConst]
              rw [Nat.beq_refl n]
              rfl

/-- Generic `<T as Tr>::SIZE` normalizes to a rigid alias (`rigidProj`) that unifies with itself
at definition site (no `where [(); ...]:` bound), and under instantiation `T := concrete c`
with `projDef c tr assoc = some (.lit n)` normalizes to `[u8; n]`. -/
theorem gca_generic_proj_rigid_and_instantiation_sound
    (tbl : DirectConstTable) (cfg : CrateFeatureConfig)
    (p : TyParamId) (c : ImplTyId) (tr : TraitId) (assoc : AssocId) (n fuel : Nat)
    (h_cli : cfg.cliNextSolver = .globally)
    (h_no_hra : cfg.higherRankedAssumptions = false)
    (h_no_gce : cfg.genericConstExprs = false)
    (h_min : cfg.gcaMinConstItems = true)
    (h_impl : tbl.projDef c tr assoc = some (.lit n))
    (h_fuel : 2 ≤ fuel) :
    let genTy := GcaTy.array .u8 (.projAlias (.param p) tr assoc)
    let genNorm := normalizeGcaTy tbl cfg fuel genTy
    let instNorm := normalizeGcaTy tbl cfg fuel (substGcaTy p c genTy)
    unifyGcaNormTy genNorm genNorm = true ∧
    unifyGcaNormTy instNorm (normalizeGcaTy tbl cfg fuel (.array .u8 (.lit n))) = true := by
  have h_ok : gcaConstItemsEffectiveAllowed cfg = true :=
    (gca_preserves_next_solver_globally cfg h_cli h_no_hra h_no_gce h_min).2.1
  have h_gen :
      normalizeGcaTy tbl cfg fuel (.array .u8 (.projAlias (.param p) tr assoc)) =
      .array .u8 (.rigidProj (.param p) tr assoc) := by
    cases fuel with
    | zero => exact False.elim (Nat.not_succ_le_zero 1 h_fuel)
    | succ f =>
        dsimp only [normalizeGcaTy, normalizeGcaConst]
        rw [h_ok]
  have h_subst :
      substGcaTy p c (.array .u8 (.projAlias (.param p) tr assoc)) =
      .array .u8 (.projAlias (.concrete c) tr assoc) := by
    dsimp only [substGcaTy, substGcaConst, substSelfTy]
    rw [Nat.beq_refl p]
  constructor
  · rw [h_gen]
    dsimp only [unifyGcaNormTy]
    rw [unifyGcaNormConst_refl_nonErr (fun h => by cases h)]
    rfl
  · rw [h_subst]
    exact (gca_assoc_const_unifies_with_literal tbl cfg c tr assoc n fuel
      h_cli h_no_hra h_no_gce h_min h_impl h_fuel).2.2

/-! ## Section 4: GCE `AbstractConst` (`ConstKind::Expr`) & Constructive Sharpness Counterexamples -/

abbrev AnonDefId := Nat

/-- Mirrors `ty::ExprKind::Binop` (`compiler/rustc_middle/src/ty/consts/kind.rs:13-18`). -/
inductive GceBinOp where
  | add
  | sub

noncomputable def GceBinOp.beq : GceBinOp → GceBinOp → Bool
  | .add, .add => true
  | .sub, .sub => true
  | _, _ => false

/-- Mirrors GCE `AbstractConst` / `ConstKind::Expr`
(`compiler/rustc_middle/src/ty/consts/kind.rs:21-46`, `abstract_const.rs`). -/
inductive GceExpr where
  | lit (n : Nat)
  | param (p : Nat)
  | binop (op : GceBinOp) (lhs rhs : GceExpr)

/-- Mirrors GCE `AnonConst` table mapping each syntactic `AnonConst` `DefId` to its
`thir_abstract_const` expansion (`compiler/rustc_middle/src/ty/abstract_const.rs:63-71`). -/
abbrev AnonConstTable := AnonDefId → Option GceExpr

/-- Mirrors `impl Relate for ty::Expr` (`compiler/rustc_middle/src/ty/relate.rs:101-124`):
strictly positional operator and `(lhs, rhs)` structural comparison with zero algebraic
commutativity or associativity rules. -/
noncomputable def gceExprStructuralEq : GceExpr → GceExpr → Bool
  | .lit a, .lit b => Nat.beq a b
  | .param a, .param b => Nat.beq a b
  | .binop op1 l1 r1, .binop op2 l2 r2 =>
      GceBinOp.beq op1 op2 && gceExprStructuralEq l1 l2 && gceExprStructuralEq r1 r2
  | _, _ => false

/-- Mirrors `fulfill.rs:717-760` (`ConstEquate` via `expand_abstract_consts` + structural `eq`):
if either `AnonConst` fails to expand, unification falls back to raw `AnonDefId` equality;
if both expand, unification requires strict positional `gceExprStructuralEq`. -/
noncomputable def gceAnonConstUnify (tbl : AnonConstTable) (d1 d2 : AnonDefId) : Bool :=
  match Nat.beq d1 d2 with
  | true => true
  | false =>
      match tbl d1, tbl d2 with
      | some e1, some e2 => gceExprStructuralEq e1 e2
      | _, _ => false

/-- Mirrors `is_const_evaluatable` -> `satisfied_from_param_env`
(`compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:51-54, 159-229`):
at definition site, a generic GCE expression is accepted solely because a matching
`where [(); expr]:` (`ClauseKind::ConstEvaluatable`) clause exists in `caller_bounds`. -/
noncomputable def gceDefSiteEvaluatable (whereBounds : List GceExpr) (target : GceExpr) : Bool :=
  match whereBounds with
  | [] => false
  | b :: bs =>
      match gceExprStructuralEq b target with
      | true => true
      | false => gceDefSiteEvaluatable bs target

/-- Result of checked `usize` CTFE evaluation at monomorphization (`E0080` on underflow). -/
inductive CtfeResult where
  | ok (v : Nat)
  | overflowErr

/-- Checked `usize` evaluation of a `GceExpr` for a single `const N: usize = nVal`.
Subtraction underflows (`lhs < rhs`) into `.overflowErr`, modeling `E0080`. -/
noncomputable def evalGceChecked (nVal : Nat) : GceExpr → CtfeResult
  | .lit k => .ok k
  | .param _ => .ok nVal
  | .binop .add l r =>
      match evalGceChecked nVal l, evalGceChecked nVal r with
      | .ok vl, .ok vr => .ok (vl + vr)
      | _, _ => .overflowErr
  | .binop .sub l r =>
      match evalGceChecked nVal l, evalGceChecked nVal r with
      | .ok vl, .ok vr =>
          match Nat.ble vr vl with
          | true => .ok (vl - vr)
          | false => .overflowErr
      | _, _ => .overflowErr

/-- **Sharpness Counterexample 1 (`ce1_anonConst_defId_unification_rejects_commuted_add`)**:
`N + 1` (AnonConst `DefId` `10`) and `1 + N` (AnonConst `DefId` `11`) are semantically equal
for EVERY `usize` instantiation `n : Nat`, yet BOTH raw `AnonConst` `DefId` unification and
expanded `AbstractConst` (`Relate for ty::Expr`) unification REJECT them (`E0308`), whereas
identical syntactic order `N + 1` vs `N + 1` succeeds. -/
theorem ce1_anonConst_defId_unification_rejects_commuted_add :
    let eNPlus1 : GceExpr := .binop .add (.param 0) (.lit 1)
    let e1PlusN : GceExpr := .binop .add (.lit 1) (.param 0)
    let tbl : AnonConstTable := fun d =>
      if Nat.beq d 10 then some eNPlus1
      else if Nat.beq d 11 then some e1PlusN
      else if Nat.beq d 12 then some eNPlus1
      else none
    (∀ n : Nat, evalGceChecked n eNPlus1 = evalGceChecked n e1PlusN) ∧
    gceExprStructuralEq eNPlus1 e1PlusN = false ∧
    gceAnonConstUnify tbl 10 11 = false ∧
    gceAnonConstUnify tbl 10 12 = true := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro n
  dsimp only [evalGceChecked]
  rw [Nat.add_comm]

/-- **Sharpness Counterexample 2 (`ce2_gce_unchecked_sub_passes_def_faults_at_zero_instantiation`)**:
Under `generic_const_exprs`, `fn sub_one<const N: usize>() -> [u8; N - 1] where [(); N - 1]:`
PASSES definition-site checking (`gceDefSiteEvaluatable = true`, `rc = 0` when uncalled), yet
call-site monomorphization at `N = 0` FAULTS with `.overflowErr` (`E0080: attempt to compute
0_usize - 1_usize, which would overflow`), while `N = 1` succeeds with `.ok 0`. -/
theorem ce2_gce_unchecked_sub_passes_def_faults_at_zero_instantiation :
    let eSubOne : GceExpr := .binop .sub (.param 0) (.lit 1)
    let whereBounds : List GceExpr := [eSubOne]
    gceDefSiteEvaluatable whereBounds eSubOne = true ∧
    evalGceChecked 0 eSubOne = .overflowErr ∧
    evalGceChecked 1 eSubOne = .ok 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Sharpness Counterexample 3 (`ce3_cyclic_trivial_const_detected`)**:
The mutual constant cycle `pub const A: usize = B; pub const B: usize = A;` (`0 ↦ alias 1`,
`1 ↦ alias 0`) is rejected by the cycle-checked `trivial_const` traversal with `.cycleDetected`
(`E0391`) and admits NO `AcyclicTrivialEnv` rank witness. -/
theorem ce3_cyclic_trivial_const_detected :
    let envAB : TrivialEnv := fun id =>
      if Nat.beq id 0 then .alias 1
      else if Nat.beq id 1 then .alias 0
      else .lit 0
    evalTrivialVisited envAB 4 [] 0 = .cycleDetected ∧
    evalTrivialVisited envAB 4 [] 1 = .cycleDetected ∧
    (¬ ∃ rank : ConstId → Nat, AcyclicTrivialEnv envAB rank) := by
  refine ⟨rfl, rfl, ?_⟩
  intro hex
  cases hex with
  | intro rank hAcyc =>
      have h0 : rank 1 < rank 0 := hAcyc.rank_decreases 0 1 rfl
      have h1 : rank 0 < rank 1 := hAcyc.rank_decreases 1 0 rfl
      exact Nat.lt_asymm h0 h1

/-! ## Section 5: Kernel Axiom Audit -/

#print axioms gce_reverts_default_next_solver
#print axioms gce_disables_effective_gca_const_items
#print axioms gca_preserves_next_solver_globally
#print axioms acyclicTrivialConst_norm_total_no_post_mono_fault
#print axioms gca_assoc_const_unifies_with_literal
#print axioms gca_chained_assoc_to_free_const_unifies_with_literal
#print axioms gca_generic_proj_rigid_and_instantiation_sound
#print axioms ce1_anonConst_defId_unification_rejects_commuted_add
#print axioms ce2_gce_unchecked_sub_passes_def_faults_at_zero_instantiation
#print axioms ce3_cyclic_trivial_const_detected

end GcaTrivialConstNormalizationSoundness
