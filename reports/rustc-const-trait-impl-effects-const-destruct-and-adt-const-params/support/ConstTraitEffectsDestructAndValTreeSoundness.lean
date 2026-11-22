/-
  ConstTraitEffectsDestructAndValTreeSoundness.lean

  Kernel-checked Lean 4 (v4.34.1) mechanization of:
    1. The 3-point `BoundConstness` effect semilattice (`Always <= Maybe <= Normal`),
       its faithful lowering to `rustc_type_ir::BoundConstness` (`HostEffectClause`),
       and context-monotone generic substitution soundness (plus old-solver vs.
       next-solver equivalence under coherence).
    2. Single-impl coherence implying CTFE-vs.-runtime observational confluence
       (`coherentConstImpl_ctfe_eq_runtime`) across single dispatches and
       expression trees, and `[const] Destruct` structural drop-safety
       (`constDestruct_drop_safety`, `constDestruct_subst_soundness`,
       `manuallyDrop_shields_nonConstDrop`).
    3. `ValTree` structural-equality substitution invariance
       (`valTree_eq_iff_type_eq`, `valTree_leibniz_substitutivity`,
       `unsized_str_valtree_length_reconstruction`) and the necessity of an
       equivalence-relation, canonical, deterministic equality domain.
    4. Four constructive sharpness counterexamples:
       - `ce1_dual_const_runtime_impl_breaks_ctfe_confluence`
       - `ce2_missing_const_destruct_executes_nonconst_drop_in_ctfe`
       - `ce3_float_neg_zero_breaks_type_substitutivity`
       - `ce4_ctfe_ptr_comparison_nondeterministic`

  Purity invariants:
    * Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
      zero `native_decide`, zero `partial def`, zero `unsafe`, zero `._unsafe_rec`.
    * No `deriving` clauses on any inductive type; all recursion uses pure
      structural recursion over mutual inductives (`DropTy`/`DropTyList`,
      `ValTree`/`ValTreeList`, `ValTreeTy`/`ValTreeTyList`) or `Prop` inductives.
-/

namespace Anneal.ConstTraitAndValTreeSoundness

/-! ## Section 1: Identifiers and Constructive `Nat`/`Bool` Helpers -/

abbrev TraitId := Nat
abbrev ParamId := Nat
abbrev ImplId := Nat
abbrev TypeConId := Nat
abbrev AllocId := Nat

theorem nat_ne_of_lt {a b : Nat} (h : a < b) : a ≠ b := by
  intro heq
  subst heq
  exact Nat.lt_irrefl a h

theorem bool_true_ne_false : (true : Bool) ≠ false := by
  intro h
  cases h

theorem bool_false_ne_true : (false : Bool) ≠ true := by
  intro h
  cases h

/-! ## Section 2: 3-Point `BoundConstness` Effect Semilattice & Lowering -/

/--
  Three-point effect-constness semilattice corresponding to surface/HIR
  `ast::BoundConstness` / `hir::BoundConstness`:
    * `always`  (`T: const Trait`)   -- unconditionally const, even in runtime `fn`
    * `maybe`   (`T: [const] Trait`) -- conditionally const, polymorphic over caller context
    * `normal`  (`T: Trait`)         -- runtime-only bound (no `HostEffectClause` emitted)

  Ordering: `always <= maybe <= normal`.
  Smaller means *stronger* const capability (satisfies stricter demands).
-/
inductive BoundConstness where
  | always
  | maybe
  | normal

/--
  Two-variant middle-IR constness corresponding to `rustc_type_ir::BoundConstness`
  carried inside `ty::HostEffectClause` (1.102-nightly / HEAD) and
  `ty::HostEffectPredicate` (1.98-nightly).
-/
inductive HostEffectConstness where
  | const
  | maybe

/--
  Exact lowering from HIR `BoundConstness` to `Option HostEffectConstness`,
  modeling `HirTyLowerer::lower_poly_trait_ref`:
    * `Always` emits `HostEffectClause { constness: Const }`
    * `Maybe`  is collected by `const_conditions` as `HostEffectClause { constness: Maybe }`
    * `Never` (`normal`) emits only a base `TraitClause` and `none` for `HostEffectClause`.
-/
def lowerToHostEffect (b : BoundConstness) : Option HostEffectConstness :=
  match b with
  | .always => some .const
  | .maybe  => some .maybe
  | .normal => none

/-- Exact mirror of `rustc_type_ir::BoundConstness::satisfies(self, goal)`. -/
def HostEffectConstness.satisfies (assumption goal : HostEffectConstness) : Bool :=
  match assumption, goal with
  | .const, .const => true
  | .const, .maybe => true
  | .maybe, .maybe => true
  | .maybe, .const => false

/--
  Partial order `a <= b` on `BoundConstness`:
  `always <= maybe <= normal`.
  Semantically, `a <= b` holds iff an assumption of constness `a` satisfies a
  requirement of constness `b`.
-/
def BoundConstness.le (a b : BoundConstness) : Prop :=
  match a, b with
  | .always, _       => True
  | .maybe,  .always => False
  | .maybe,  .maybe  => True
  | .maybe,  .normal => True
  | .normal, .always => False
  | .normal, .maybe  => False
  | .normal, .normal => True

/-- Computable decision procedure for `BoundConstness.le`. -/
def BoundConstness.leBool (a b : BoundConstness) : Bool :=
  match a, b with
  | .always, _       => true
  | .maybe,  .always => false
  | .maybe,  .maybe  => true
  | .maybe,  .normal => true
  | .normal, .always => false
  | .normal, .maybe  => false
  | .normal, .normal => true

/-- Least upper bound (`join`, weaker capability): `always ⊔ x = x`, `normal ⊔ x = normal`. -/
def BoundConstness.join (a b : BoundConstness) : BoundConstness :=
  match a, b with
  | .normal, _       => .normal
  | _,       .normal => .normal
  | .maybe,  _       => .maybe
  | _,       .maybe  => .maybe
  | .always, .always => .always

/-- Greatest lower bound (`meet`, stronger requirement): `always ⊓ x = always`, `normal ⊓ x = x`. -/
def BoundConstness.meet (a b : BoundConstness) : BoundConstness :=
  match a, b with
  | .always, _       => .always
  | _,       .always => .always
  | .maybe,  _       => .maybe
  | _,       .maybe  => .maybe
  | .normal, .normal => .normal

theorem BoundConstness.leBool_eq_true_iff (a b : BoundConstness) :
    BoundConstness.leBool a b = true ↔ BoundConstness.le a b := by
  cases a <;> cases b <;> constructor <;> intro h
  all_goals first | exact trivial | rfl | cases h

theorem BoundConstness.le_refl (a : BoundConstness) : BoundConstness.le a a := by
  cases a <;> exact trivial

theorem BoundConstness.le_trans {a b c : BoundConstness}
    (h1 : BoundConstness.le a b) (h2 : BoundConstness.le b c) :
    BoundConstness.le a c := by
  cases a <;> cases b <;> cases c
  all_goals first | exact trivial | exact False.elim h1 | exact False.elim h2

theorem BoundConstness.le_antisymm {a b : BoundConstness}
    (h1 : BoundConstness.le a b) (h2 : BoundConstness.le b a) : a = b := by
  cases a <;> cases b
  all_goals first | rfl | exact False.elim h1 | exact False.elim h2

theorem BoundConstness.le_total (a b : BoundConstness) :
    BoundConstness.le a b ∨ BoundConstness.le b a := by
  cases a <;> cases b
  all_goals first | exact Or.inl trivial | exact Or.inr trivial

theorem BoundConstness.always_le (a : BoundConstness) : BoundConstness.le .always a := by
  cases a <;> exact trivial

theorem BoundConstness.le_normal (a : BoundConstness) : BoundConstness.le a .normal := by
  cases a <;> exact trivial

theorem BoundConstness.always_le_maybe : BoundConstness.le .always .maybe := trivial
theorem BoundConstness.maybe_le_normal : BoundConstness.le .maybe .normal := trivial
theorem BoundConstness.not_maybe_le_always : ¬ BoundConstness.le .maybe .always := fun h => h
theorem BoundConstness.not_normal_le_maybe : ¬ BoundConstness.le .normal .maybe := fun h => h
theorem BoundConstness.not_normal_le_always : ¬ BoundConstness.le .normal .always := fun h => h

theorem BoundConstness.join_comm (a b : BoundConstness) :
    BoundConstness.join a b = BoundConstness.join b a := by
  cases a <;> cases b <;> rfl

theorem BoundConstness.join_assoc (a b c : BoundConstness) :
    BoundConstness.join (BoundConstness.join a b) c =
    BoundConstness.join a (BoundConstness.join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem BoundConstness.join_idem (a : BoundConstness) :
    BoundConstness.join a a = a := by
  cases a <;> rfl

theorem BoundConstness.le_join_left (a b : BoundConstness) :
    BoundConstness.le a (BoundConstness.join a b) := by
  cases a <;> cases b <;> exact trivial

theorem BoundConstness.le_join_right (a b : BoundConstness) :
    BoundConstness.le b (BoundConstness.join a b) := by
  cases a <;> cases b <;> exact trivial

theorem BoundConstness.join_le {a b c : BoundConstness}
    (ha : BoundConstness.le a c) (hb : BoundConstness.le b c) :
    BoundConstness.le (BoundConstness.join a b) c := by
  cases a <;> cases b <;> cases c
  all_goals first | exact trivial | exact False.elim ha | exact False.elim hb

theorem BoundConstness.le_iff_join_eq_right (a b : BoundConstness) :
    BoundConstness.le a b ↔ BoundConstness.join a b = b := by
  cases a <;> cases b <;> constructor <;> intro h
  all_goals first | rfl | exact trivial | cases h

theorem BoundConstness.meet_comm (a b : BoundConstness) :
    BoundConstness.meet a b = BoundConstness.meet b a := by
  cases a <;> cases b <;> rfl

theorem BoundConstness.meet_assoc (a b c : BoundConstness) :
    BoundConstness.meet (BoundConstness.meet a b) c =
    BoundConstness.meet a (BoundConstness.meet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem BoundConstness.meet_idem (a : BoundConstness) :
    BoundConstness.meet a a = a := by
  cases a <;> rfl

theorem BoundConstness.meet_le_left (a b : BoundConstness) :
    BoundConstness.le (BoundConstness.meet a b) a := by
  cases a <;> cases b <;> exact trivial

theorem BoundConstness.meet_le_right (a b : BoundConstness) :
    BoundConstness.le (BoundConstness.meet a b) b := by
  cases a <;> cases b <;> exact trivial

theorem BoundConstness.le_meet {a b c : BoundConstness}
    (ha : BoundConstness.le c a) (hb : BoundConstness.le c b) :
    BoundConstness.le c (BoundConstness.meet a b) := by
  cases a <;> cases b <;> cases c
  all_goals first | exact trivial | exact False.elim ha | exact False.elim hb

theorem BoundConstness.absorb_join_meet (a b : BoundConstness) :
    BoundConstness.join a (BoundConstness.meet a b) = a := by
  cases a <;> cases b <;> rfl

theorem BoundConstness.absorb_meet_join (a b : BoundConstness) :
    BoundConstness.meet a (BoundConstness.join a b) = a := by
  cases a <;> cases b <;> rfl

/--
  Faithfulness theorem: when both HIR bounds lower to `HostEffectClause`s,
  `rustc_type_ir::BoundConstness::satisfies` coincides exactly with the
  semilattice order `BoundConstness.le`.
-/
theorem lowerToHostEffect_satisfies_iff_le (a b : BoundConstness)
    (ha : HostEffectConstness) (hb : HostEffectConstness)
    (hLowerA : lowerToHostEffect a = some ha)
    (hLowerB : lowerToHostEffect b = some hb) :
    HostEffectConstness.satisfies ha hb = true ↔ BoundConstness.le a b := by
  cases a <;> cases b
  all_goals
    first
    | cases hLowerA
    | cases hLowerB
  all_goals
    first
    | cases hLowerB
    | skip
  all_goals
    first
    | exact ⟨fun _ => trivial, fun _ => rfl⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => False.elim h⟩

/-! ## Section 3: Evaluation Contexts & Context-Monotone Substitution Soundness -/

/--
  Evaluation context mirroring `hir::ConstContext` in
  `compiler/rustc_hir_typeck/src/callee.rs:1172-1178` and
  `compiler/rustc_const_eval/src/check_consts/qualifs.rs:199-203`.
-/
inductive EvalCtx where
  | constItem  -- `const C: T = ...`, `static S: T = ...`, `const { ... }`
  | constFn    -- body of `const fn f(...)`
  | runtimeFn  -- ordinary runtime `fn`

/-- Required host effect polarity of a context. -/
def ctxPolarity (ctx : EvalCtx) : BoundConstness :=
  match ctx with
  | .constItem => .always
  | .constFn   => .maybe
  | .runtimeFn => .normal

/--
  Instantiating a callee's bound `b` at a call site inside context `ctx`:
    * `T: const Trait`   (`always`) remains `always` even in `runtimeFn`
    * `T: [const] Trait` (`maybe`)  specializes to `ctxPolarity ctx`
    * `T: Trait`         (`normal`) remains `normal` even in `constItem`
-/
def instBound (ctx : EvalCtx) (b : BoundConstness) : BoundConstness :=
  match b with
  | .always => .always
  | .maybe  => ctxPolarity ctx
  | .normal => .normal

theorem instBound_mono_ctx {ctx₁ ctx₂ : EvalCtx} (b : BoundConstness)
    (hctx : BoundConstness.le (ctxPolarity ctx₁) (ctxPolarity ctx₂)) :
    BoundConstness.le (instBound ctx₁ b) (instBound ctx₂ b) := by
  cases b with
  | always => exact trivial
  | maybe  => exact hctx
  | normal => exact trivial

theorem instBound_mono_bound (ctx : EvalCtx) {b₁ b₂ : BoundConstness}
    (hb : BoundConstness.le b₁ b₂) :
    BoundConstness.le (instBound ctx b₁) (instBound ctx b₂) := by
  cases b₁ <;> cases b₂ <;> cases ctx
  all_goals first | exact trivial | exact False.elim hb

/-- Instantiating `[const]` inside `constItem` demands `always` (`const`). -/
theorem instBound_constItem_maybe : instBound .constItem .maybe = .always := rfl

/-- Instantiating `[const]` inside `runtimeFn` relaxes to `normal`. -/
theorem instBound_runtimeFn_maybe : instBound .runtimeFn .maybe = .normal := rfl

/-- Instantiating `const` (`always`) inside `runtimeFn` STILL demands `always`. -/
theorem instBound_runtimeFn_always : instBound .runtimeFn .always = .always := rfl

/-- Simple concrete type identifiers for trait resolution and substitution. -/
abbrev ConcreteTy := Nat

/-- Generic type expression: either a concrete type or a type parameter. -/
inductive GenTy where
  | concrete (ty : ConcreteTy)
  | param    (pid : ParamId)

/-- Apply a concrete type substitution `σ` to a `GenTy`. -/
def substGenTy (σ : ParamId → ConcreteTy) (g : GenTy) : ConcreteTy :=
  match g with
  | .concrete t => t
  | .param pid  => σ pid

/-- A trait bound clause `SelfTy: <constness> Trait`. -/
structure TraitClause where
  selfTy    : GenTy
  traitId   : TraitId
  constness : BoundConstness

/-- Concrete trait-impl entry in a crate's registry. -/
structure ImplEntry where
  implId    : ImplId
  traitId   : TraitId
  targetTy  : ConcreteTy
  isConst   : Bool
  semantics : Nat → Nat

/-- Effective capability level of a concrete impl (`const impl` -> `always`, `impl` -> `normal`). -/
def ImplEntry.capability (e : ImplEntry) : BoundConstness :=
  match e.isConst with
  | true  => .always
  | false => .normal

/-- Non-nested list of impl entries (avoids `List` deriving/codegen issues). -/
inductive ImplList where
  | nil
  | cons (head : ImplEntry) (tail : ImplList)

/-- Structural membership in an `ImplList`. -/
inductive ImplMem (e : ImplEntry) : ImplList → Prop where
  | here  {t : ImplList} : ImplMem e (.cons e t)
  | there {h : ImplEntry} {t : ImplList} : ImplMem e t → ImplMem e (.cons h t)

/-- Concrete goal satisfaction in an `ImplList` (concrete impl must exist and be strong enough). -/
def ConcreteSat (reg : ImplList) (tr : TraitId) (ty : ConcreteTy) (req : BoundConstness) : Prop :=
  ∃ e : ImplEntry,
    ImplMem e reg ∧
    e.traitId = tr ∧
    e.targetTy = ty ∧
    BoundConstness.le e.capability req

/--
  Generic environment: maps `(ParamId, TraitId)` to an optional declared bound
  constness (`none` = no bound assumed).
-/
abbrev ParamEnv := ParamId → TraitId → Option BoundConstness

/--
  Generic goal entailment inside a polymorphic `const fn` body:
    * For a concrete self type, discharged directly by `reg`.
    * For a type parameter `pid`, discharged by an in-scope `ParamEnv` bound `b`
      satisfying `b <= req` (mirroring `fast_reject_assumption` in `effect_goals.rs:59`).
-/
def GenericSat (reg : ImplList) (env : ParamEnv) (g : GenTy)
    (tr : TraitId) (req : BoundConstness) : Prop :=
  match g with
  | .concrete ty => ConcreteSat reg tr ty req
  | .param pid   =>
      ∃ b : BoundConstness, env pid tr = some b ∧ BoundConstness.le b req

/--
  Substitution validity at caller context `ctx`: every declared parameter bound
  `env pid tr = some b` is satisfied after instantiating `b` at `ctx` for `σ pid`.
-/
def ValidSubst (reg : ImplList) (env : ParamEnv) (ctx : EvalCtx)
    (σ : ParamId → ConcreteTy) : Prop :=
  ∀ (pid : ParamId) (tr : TraitId) (b : BoundConstness),
    env pid tr = some b →
    ConcreteSat reg tr (σ pid) (instBound ctx b)

/--
  Core Context-Monotone Substitution Soundness Theorem:
  If a polymorphic `const fn` body proves a trait goal `g: req Trait` under `env`,
  and a caller in context `ctx` supplies a valid substitution `σ` satisfying all
  instantiated bounds of `env` at `ctx`, then the substituted concrete goal
  `substGenTy σ g : (instBound ctx req) Trait` holds in `reg`.
-/
theorem const_subst_soundness
    {reg : ImplList} {env : ParamEnv} {ctx : EvalCtx}
    {σ : ParamId → ConcreteTy} {g : GenTy} {tr : TraitId} {req : BoundConstness}
    (hValid : ValidSubst reg env ctx σ)
    (hGoal : GenericSat reg env g tr req) :
    ConcreteSat reg tr (substGenTy σ g) (instBound ctx req) := by
  cases g with
  | concrete ty =>
    rcases hGoal with ⟨e, hmem, htr, hty, hcap⟩
    refine ⟨e, hmem, htr, hty, ?_⟩
    cases hce : e.isConst <;> cases req <;> cases ctx
    all_goals
      simp only [ImplEntry.capability, hce, instBound, ctxPolarity] at hcap ⊢
      first | exact trivial | exact False.elim hcap
  | param pid =>
    rcases hGoal with ⟨b, henv, hle⟩
    have hSub := hValid pid tr b henv
    rcases hSub with ⟨e, hmem, htr, hty, hcap⟩
    refine ⟨e, hmem, htr, hty, ?_⟩
    exact BoundConstness.le_trans hcap (instBound_mono_bound ctx hle)

/--
  Context Weakening Theorem: any substitution valid in `constItem` (CTFE) is
  automatically valid in `runtimeFn`, and any substitution valid in `ctx₁` is
  valid in any weaker context `ctx₂` (`ctxPolarity ctx₁ <= ctxPolarity ctx₂`).
-/
theorem validSubst_mono_ctx
    {reg : ImplList} {env : ParamEnv} {ctx₁ ctx₂ : EvalCtx}
    {σ : ParamId → ConcreteTy}
    (hctx : BoundConstness.le (ctxPolarity ctx₁) (ctxPolarity ctx₂))
    (hValid : ValidSubst reg env ctx₁ σ) :
    ValidSubst reg env ctx₂ σ := by
  intro pid tr b henv
  rcases hValid pid tr b henv with ⟨e, hmem, htr, hty, hcap⟩
  exact ⟨e, hmem, htr, hty, BoundConstness.le_trans hcap (instBound_mono_ctx b hctx)⟩

theorem validSubst_constItem_to_runtimeFn
    {reg : ImplList} {env : ParamEnv} {σ : ParamId → ConcreteTy}
    (hValid : ValidSubst reg env .constItem σ) :
    ValidSubst reg env .runtimeFn σ :=
  validSubst_mono_ctx (ctx₁ := .constItem) (ctx₂ := .runtimeFn) trivial hValid

/-! ## Section 4: Single-Impl Coherence & CTFE-vs.-Runtime Confluence -/

/--
  Trait-impl coherence (`compiler/rustc_trait_selection/src/traits/coherence.rs:112-134`
  and `specialization_graph.rs:140-160`):
  Overlap checking compares `(traitId, targetTy)` while IGNORING `isConst`.
  Therefore, a coherent registry contains at most one impl per `(traitId, targetTy)` pair.
-/
def Coherent (reg : ImplList) : Prop :=
  ∀ e₁ e₂ : ImplEntry,
    ImplMem e₁ reg →
    ImplMem e₂ reg →
    e₁.traitId = e₂.traitId →
    e₁.targetTy = e₂.targetTy →
    e₁ = e₂

/--
  Old-solver host-effect resolution (`compiler/rustc_trait_selection/src/traits/effects.rs:597-654`):
  selects a base trait impl candidate and then checks `impl_trait_header.constness`.
-/
def OldSolverHostEffect (reg : ImplList) (tr : TraitId) (ty : ConcreteTy)
    (hc : HostEffectConstness) : Prop :=
  ∃ e : ImplEntry,
    ImplMem e reg ∧
    e.traitId = tr ∧
    e.targetTy = ty ∧
    e.isConst = true ∧
    HostEffectConstness.satisfies .const hc = true

/--
  Next-solver host-effect resolution (`compiler/rustc_next_trait_solver/src/solve/effect_goals.rs:152-213,504-519`):
  first probes the base `TraitClause` goal (`compute_trait_goal`), then requires
  an impl candidate passing `cx.impl_is_const(impl_def_id)`.
-/
def NextSolverHostEffect (reg : ImplList) (tr : TraitId) (ty : ConcreteTy)
    (hc : HostEffectConstness) : Prop :=
  (∃ eBase : ImplEntry, ImplMem eBase reg ∧ eBase.traitId = tr ∧ eBase.targetTy = ty) ∧
  (∃ eConst : ImplEntry,
    ImplMem eConst reg ∧
    eConst.traitId = tr ∧
    eConst.targetTy = ty ∧
    eConst.isConst = true ∧
    HostEffectConstness.satisfies .const hc = true)

/-- Exact solver equivalence theorem between `-Z next-solver=no` and `-Z next-solver=globally`. -/
theorem oldSolver_iff_nextSolver (reg : ImplList) (tr : TraitId) (ty : ConcreteTy)
    (hc : HostEffectConstness) :
    OldSolverHostEffect reg tr ty hc ↔ NextSolverHostEffect reg tr ty hc := by
  constructor
  · intro h
    rcases h with ⟨e, hmem, htr, hty, hcst, hsat⟩
    exact ⟨⟨e, hmem, htr, hty⟩, ⟨e, hmem, htr, hty, hcst, hsat⟩⟩
  · intro h
    exact h.2

/-- CTFE trait dispatch: requires a `const impl` (`isConst = true`). -/
def EvalCtfeDispatch (reg : ImplList) (tr : TraitId) (ty : ConcreteTy)
    (arg out : Nat) : Prop :=
  ∃ e : ImplEntry,
    ImplMem e reg ∧
    e.traitId = tr ∧
    e.targetTy = ty ∧
    e.isConst = true ∧
    e.semantics arg = out

/-- Runtime trait dispatch: accepts any matching impl (whether `const impl` or `impl`). -/
def EvalRuntimeDispatch (reg : ImplList) (tr : TraitId) (ty : ConcreteTy)
    (arg out : Nat) : Prop :=
  ∃ e : ImplEntry,
    ImplMem e reg ∧
    e.traitId = tr ∧
    e.targetTy = ty ∧
    e.semantics arg = out

/--
  Core Theorem `coherentConstImpl_ctfe_eq_runtime`:
  Under single-impl coherence (which rejects overlapping `const impl` and `impl`
  for the same `(Trait, Self)` with `E0119`), CTFE evaluation and runtime
  evaluation of any trait call are strictly confluent: they produce the exact
  same output value.
-/
theorem coherentConstImpl_ctfe_eq_runtime
    {reg : ImplList} (hCoh : Coherent reg)
    {tr : TraitId} {ty : ConcreteTy} {arg outCtfe outRt : Nat}
    (hCtfe : EvalCtfeDispatch reg tr ty arg outCtfe)
    (hRt   : EvalRuntimeDispatch reg tr ty arg outRt) :
    outCtfe = outRt := by
  rcases hCtfe with ⟨e₁, hmem₁, htr₁, hty₁, _, hsem₁⟩
  rcases hRt   with ⟨e₂, hmem₂, htr₂, hty₂, hsem₂⟩
  have heq : e₁ = e₂ := hCoh e₁ e₂ hmem₁ hmem₂ (Eq.trans htr₁ htr₂.symm) (Eq.trans hty₁ hty₂.symm)
  subst heq
  exact Eq.trans hsem₁.symm hsem₂

/-- Every CTFE-evaluable dispatch is also runtime-evaluable with identical result. -/
theorem coherentConstImpl_ctfe_implies_runtime
    {reg : ImplList} {tr : TraitId} {ty : ConcreteTy} {arg out : Nat}
    (hCtfe : EvalCtfeDispatch reg tr ty arg out) :
    EvalRuntimeDispatch reg tr ty arg out := by
  rcases hCtfe with ⟨e, hmem, htr, hty, _, hsem⟩
  exact ⟨e, hmem, htr, hty, hsem⟩

/-- Multi-step expression language with literals, addition, and trait-method dispatch. -/
inductive TraitExpr where
  | lit      (n : Nat)
  | add      (a b : TraitExpr)
  | call     (tr : TraitId) (ty : ConcreteTy) (arg : TraitExpr)

/-- Big-step CTFE evaluation of `TraitExpr`. -/
inductive EvalCtfeExpr (reg : ImplList) : TraitExpr → Nat → Prop where
  | lit (n : Nat) : EvalCtfeExpr reg (.lit n) n
  | add {a b : TraitExpr} {va vb : Nat} :
      EvalCtfeExpr reg a va →
      EvalCtfeExpr reg b vb →
      EvalCtfeExpr reg (.add a b) (va + vb)
  | call {tr : TraitId} {ty : ConcreteTy} {arg : TraitExpr} {varg vout : Nat} :
      EvalCtfeExpr reg arg varg →
      EvalCtfeDispatch reg tr ty varg vout →
      EvalCtfeExpr reg (.call tr ty arg) vout

/-- Big-step runtime evaluation of `TraitExpr`. -/
inductive EvalRuntimeExpr (reg : ImplList) : TraitExpr → Nat → Prop where
  | lit (n : Nat) : EvalRuntimeExpr reg (.lit n) n
  | add {a b : TraitExpr} {va vb : Nat} :
      EvalRuntimeExpr reg a va →
      EvalRuntimeExpr reg b vb →
      EvalRuntimeExpr reg (.add a b) (va + vb)
  | call {tr : TraitId} {ty : ConcreteTy} {arg : TraitExpr} {varg vout : Nat} :
      EvalRuntimeExpr reg arg varg →
      EvalRuntimeDispatch reg tr ty varg vout →
      EvalRuntimeExpr reg (.call tr ty arg) vout

/-- Compositional CTFE-vs.-runtime confluence over arbitrary expression trees. -/
theorem coherentConstImpl_expr_ctfe_eq_runtime
    {reg : ImplList} (hCoh : Coherent reg)
    {e : TraitExpr} {vCtfe vRt : Nat}
    (hCtfe : EvalCtfeExpr reg e vCtfe)
    (hRt   : EvalRuntimeExpr reg e vRt) :
    vCtfe = vRt := by
  induction hCtfe generalizing vRt with
  | lit n =>
    cases hRt
    rfl
  | add _ _ iha ihb =>
    cases hRt with
    | add ha hb =>
      have ea := iha ha
      have eb := ihb hb
      rw [ea, eb]
  | call _ hdisp ih =>
    cases hRt with
    | call harg hdispRt =>
      have earg := ih harg
      subst earg
      exact coherentConstImpl_ctfe_eq_runtime hCoh hdisp hdispRt

/-- Every expression evaluating in CTFE also evaluates at runtime to the exact same value. -/
theorem ctfe_expr_implies_runtime_expr
    {reg : ImplList} {e : TraitExpr} {v : Nat}
    (hCtfe : EvalCtfeExpr reg e v) :
    EvalRuntimeExpr reg e v := by
  induction hCtfe with
  | lit n => exact .lit n
  | add _ _ iha ihb => exact .add iha ihb
  | call _ hdisp ih => exact .call ih (coherentConstImpl_ctfe_implies_runtime hdisp)

/-! ## Section 5: `[const] Destruct` Structural Drop-Safety -/

/-- Destructor classification mirroring `AdtDestructorKind` in `structural_traits.rs:806-817`. -/
inductive DtorKind where
  | none
  | constDrop    (delta : Nat)  -- `const impl Drop` with deterministic CTFE effect
  | nonConstDrop (delta : Nat)  -- runtime-only `impl Drop`

/-
  Mutual inductive representation of Rust types relevant to `const_conditions_for_destruct`
  (`structural_traits.rs:787-872`) and `evaluate_host_effect_for_destruct_goal`
  (`effects.rs:449-548`). Uses a custom `DropTyList` to avoid nested `List` recursion.
-/
mutual
  inductive DropTy where
    | prim
    | manuallyDrop (inner : DropTy)
    | array        (elem : DropTy) (len : Nat)
    | tuple        (fields : DropTyList)
    | adt          (fields : DropTyList) (dtor : DtorKind)
    | param        (pid : ParamId)
    | dynTrait
    | coroutine

  inductive DropTyList where
    | nil
    | cons (head : DropTy) (tail : DropTyList)
end

/-- Destruct-bound environment mapping type parameter IDs to their `Destruct` bound strength. -/
abbrev DestructEnv := ParamId → BoundConstness

/-- Empty environment (unbounded type parameters default to `.normal`, i.e., runtime-only `Destruct`). -/
def emptyDestructEnv : DestructEnv := fun _ => .normal

/-
  Structural `[const] Destruct` predicate parameterized by `DestructEnv` and `EvalCtx`,
  directly mirroring `const_conditions_for_destruct` (`structural_traits.rs:787-872`)
  and `NeedsNonConstDrop::in_any_value_of_ty` (`qualifs.rs:178-207`).
-/
mutual
  noncomputable def ConstDestruct (env : DestructEnv) (ctx : EvalCtx) : DropTy → Prop
    | .prim              => True
    | .manuallyDrop _    => True
    | .array elem _      => ConstDestruct env ctx elem
    | .tuple fields      => ConstDestructList env ctx fields
    | .adt fields dtor   =>
        ConstDestructList env ctx fields ∧
        match dtor with
        | .none           => True
        | .constDrop _    => True
        | .nonConstDrop _ => ctx = .runtimeFn
    | .param pid         => BoundConstness.le (env pid) (ctxPolarity ctx)
    | .dynTrait          => ctx = .runtimeFn
    | .coroutine         => ctx = .runtimeFn

  noncomputable def ConstDestructList (env : DestructEnv) (ctx : EvalCtx) : DropTyList → Prop
    | .nil             => True
    | .cons head tail  => ConstDestruct env ctx head ∧ ConstDestructList env ctx tail
end

/- Whether a concrete (parameter-free) type's drop glue ever invokes a `nonConstDrop`. -/
mutual
  noncomputable def DropHitsNonConst : DropTy → Prop
    | .prim              => False
    | .manuallyDrop _    => False
    | .array elem _      => DropHitsNonConst elem
    | .tuple fields      => DropListHitsNonConst fields
    | .adt fields dtor   =>
        DropListHitsNonConst fields ∨
        match dtor with
        | .none           => False
        | .constDrop _    => False
        | .nonConstDrop _ => True
    | .param _           => True
    | .dynTrait          => True
    | .coroutine         => True

  noncomputable def DropListHitsNonConst : DropTyList → Prop
    | .nil            => False
    | .cons head tail => DropHitsNonConst head ∨ DropListHitsNonConst tail
end

/-
  Accumulated drop-effect trace (`Option Nat`):
    * `runDropCtfe` returns `none` iff dropping hits a non-const destructor / dynamic / unresolved type.
    * `runDropRuntime` executes all destructors (both `constDrop` and `nonConstDrop`) in order.
-/
mutual
  noncomputable def runDropCtfe : DropTy → Option Nat
    | .prim            => some 0
    | .manuallyDrop _  => some 0
    | .array elem len  =>
        match runDropCtfe elem with
        | some d => some (len * d)
        | none   => none
    | .tuple fields    => runDropCtfeList fields
    | .adt fields dtor =>
        match dtor with
        | .none => runDropCtfeList fields
        | .constDrop d =>
            match runDropCtfeList fields with
            | some f => some (d + f)
            | none   => none
        | .nonConstDrop _ => none
    | .param _         => none
    | .dynTrait        => none
    | .coroutine       => none

  noncomputable def runDropCtfeList : DropTyList → Option Nat
    | .nil => some 0
    | .cons head tail =>
        match runDropCtfe head, runDropCtfeList tail with
        | some h, some t => some (h + t)
        | _,      _      => none
end

mutual
  noncomputable def runDropRuntime : DropTy → Option Nat
    | .prim            => some 0
    | .manuallyDrop _  => some 0
    | .array elem len  =>
        match runDropRuntime elem with
        | some d => some (len * d)
        | none   => none
    | .tuple fields    => runDropRuntimeList fields
    | .adt fields dtor =>
        match dtor with
        | .none => runDropRuntimeList fields
        | .constDrop d =>
            match runDropRuntimeList fields with
            | some f => some (d + f)
            | none   => none
        | .nonConstDrop d =>
            match runDropRuntimeList fields with
            | some f => some (d + f)
            | none   => none
    | .param _         => none
    | .dynTrait        => none
    | .coroutine       => none

  noncomputable def runDropRuntimeList : DropTyList → Option Nat
    | .nil => some 0
    | .cons head tail =>
        match runDropRuntime head, runDropRuntimeList tail with
        | some h, some t => some (h + t)
        | _,      _      => none
end

/- Structural proof that `ConstDestruct emptyDestructEnv .constItem ty` rules out `DropHitsNonConst`. -/
mutual
  theorem constDestruct_drop_safety (ty : DropTy)
      (h : ConstDestruct emptyDestructEnv .constItem ty) :
      ¬ DropHitsNonConst ty := by
    cases ty with
    | prim => intro hhit; exact hhit
    | manuallyDrop inner => intro hhit; exact hhit
    | array elem len => exact constDestruct_drop_safety elem h
    | tuple fields => exact constDestructList_drop_safety fields h
    | adt fields dtor =>
      rcases h with ⟨hfields, hdtor⟩
      intro hhit
      cases hhit with
      | inl hf => exact constDestructList_drop_safety fields hfields hf
      | inr hd =>
        cases dtor with
        | none => exact hd
        | constDrop _ => exact hd
        | nonConstDrop _ => cases hdtor
    | param pid => exact False.elim h
    | dynTrait => cases h
    | coroutine => cases h

  theorem constDestructList_drop_safety (tys : DropTyList)
      (h : ConstDestructList emptyDestructEnv .constItem tys) :
      ¬ DropListHitsNonConst tys := by
    cases tys with
    | nil => intro hhit; exact hhit
    | cons head tail =>
      rcases h with ⟨hh, ht⟩
      intro hhit
      cases hhit with
      | inl h1 => exact constDestruct_drop_safety head hh h1
      | inr h2 => exact constDestructList_drop_safety tail ht h2
end

/-
  CTFE-vs.-Runtime Drop Confluence Theorem:
  Whenever `ConstDestruct emptyDestructEnv .constItem ty` holds, CTFE drop glue
  succeeds (`∃ n, runDropCtfe ty = some n`) and agrees exactly with runtime drop
  glue (`runDropCtfe ty = runDropRuntime ty`).
-/
mutual
  theorem ctfe_drop_eq_runtime_drop (ty : DropTy)
      (h : ConstDestruct emptyDestructEnv .constItem ty) :
      (∃ n : Nat, runDropCtfe ty = some n) ∧ runDropCtfe ty = runDropRuntime ty := by
    cases ty with
    | prim => exact ⟨⟨0, rfl⟩, rfl⟩
    | manuallyDrop inner => exact ⟨⟨0, rfl⟩, rfl⟩
    | array elem len =>
      rcases ctfe_drop_eq_runtime_drop elem h with ⟨⟨n, hn⟩, heq⟩
      constructor
      · refine ⟨len * n, ?_⟩
        simp only [runDropCtfe, hn]
      · simp only [runDropCtfe, runDropRuntime, ← heq]
    | tuple fields =>
      exact ctfe_drop_list_eq_runtime_drop fields h
    | adt fields dtor =>
      rcases h with ⟨hfields, hdtor⟩
      rcases ctfe_drop_list_eq_runtime_drop fields hfields with ⟨⟨f, hf⟩, heqf⟩
      cases dtor with
      | none =>
        exact ⟨⟨f, hf⟩, heqf⟩
      | constDrop d =>
        constructor
        · refine ⟨d + f, ?_⟩
          simp only [runDropCtfe, hf]
        · simp only [runDropCtfe, runDropRuntime, ← heqf]
      | nonConstDrop _ =>
        cases hdtor
    | param pid => exact False.elim h
    | dynTrait => cases h
    | coroutine => cases h

  theorem ctfe_drop_list_eq_runtime_drop (tys : DropTyList)
      (h : ConstDestructList emptyDestructEnv .constItem tys) :
      (∃ n : Nat, runDropCtfeList tys = some n) ∧ runDropCtfeList tys = runDropRuntimeList tys := by
    cases tys with
    | nil => exact ⟨⟨0, rfl⟩, rfl⟩
    | cons head tail =>
      rcases h with ⟨hh, ht⟩
      rcases ctfe_drop_eq_runtime_drop head hh with ⟨⟨nh, hnh⟩, heqh⟩
      rcases ctfe_drop_list_eq_runtime_drop tail ht with ⟨⟨nt, hnt⟩, heqt⟩
      constructor
      · refine ⟨nh + nt, ?_⟩
        simp only [runDropCtfeList, hnh, hnt]
      · simp only [runDropCtfeList, runDropRuntimeList, ← heqh, ← heqt]
end

/- Generic type substitution over `DropTy`. -/
mutual
  noncomputable def substDropTy (σ : ParamId → DropTy) : DropTy → DropTy
    | .prim              => .prim
    | .manuallyDrop x    => .manuallyDrop (substDropTy σ x)
    | .array elem len    => .array (substDropTy σ elem) len
    | .tuple fields      => .tuple (substDropTyList σ fields)
    | .adt fields dtor   => .adt (substDropTyList σ fields) dtor
    | .param pid         => σ pid
    | .dynTrait          => .dynTrait
    | .coroutine         => .coroutine

  noncomputable def substDropTyList (σ : ParamId → DropTy) : DropTyList → DropTyList
    | .nil             => .nil
    | .cons head tail  => .cons (substDropTy σ head) (substDropTyList σ tail)
end

/-
  Polymorphic `[const] Destruct` Substitution Soundness:
  If a generic `const fn` body establishes `ConstDestruct env .constFn ty`,
  then for ANY concrete call-site context `ctx` (`constItem` or `runtimeFn`) and
  substitution `σ` whose concrete types satisfy every `[const]`/`const` `Destruct`
  bound in `env` at `ctx`, the instantiated type satisfies `ConstDestruct emptyDestructEnv ctx`.
-/
mutual
  theorem constDestruct_subst_soundness
      {env : DestructEnv} {ctx : EvalCtx} {σ : ParamId → DropTy}
      (hSubst : ∀ pid : ParamId,
        BoundConstness.le (env pid) .maybe →
        ConstDestruct emptyDestructEnv ctx (σ pid))
      (ty : DropTy)
      (h : ConstDestruct env .constFn ty) :
      ConstDestruct emptyDestructEnv ctx (substDropTy σ ty) := by
    cases ty with
    | prim => exact trivial
    | manuallyDrop inner => exact trivial
    | array elem len => exact constDestruct_subst_soundness hSubst elem h
    | tuple fields => exact constDestructList_subst_soundness hSubst fields h
    | adt fields dtor =>
      rcases h with ⟨hfields, hdtor⟩
      refine ⟨constDestructList_subst_soundness hSubst fields hfields, ?_⟩
      cases dtor with
      | none => exact trivial
      | constDrop _ => exact trivial
      | nonConstDrop _ => cases hdtor
    | param pid => exact hSubst pid h
    | dynTrait => cases h
    | coroutine => cases h

  theorem constDestructList_subst_soundness
      {env : DestructEnv} {ctx : EvalCtx} {σ : ParamId → DropTy}
      (hSubst : ∀ pid : ParamId,
        BoundConstness.le (env pid) .maybe →
        ConstDestruct emptyDestructEnv ctx (σ pid))
      (tys : DropTyList)
      (h : ConstDestructList env .constFn tys) :
      ConstDestructList emptyDestructEnv ctx (substDropTyList σ tys) := by
    cases tys with
    | nil => exact trivial
    | cons head tail =>
      rcases h with ⟨hh, ht⟩
      exact ⟨constDestruct_subst_soundness hSubst head hh,
             constDestructList_subst_soundness hSubst tail ht⟩
end

/- Runtime polymorphism: every `DropTy` without unresolved parameters is `ConstDestruct` at `.runtimeFn`. -/
mutual
  theorem constDestruct_runtime_universal (ty : DropTy) :
      ConstDestruct emptyDestructEnv .runtimeFn ty := by
    cases ty with
    | prim => exact trivial
    | manuallyDrop _ => exact trivial
    | array elem _ => exact constDestruct_runtime_universal elem
    | tuple fields => exact constDestructList_runtime_universal fields
    | adt fields dtor =>
      refine ⟨constDestructList_runtime_universal fields, ?_⟩
      cases dtor with
      | none => exact trivial
      | constDrop _ => exact trivial
      | nonConstDrop _ => rfl
    | param _ => exact trivial
    | dynTrait => rfl
    | coroutine => rfl

  theorem constDestructList_runtime_universal (tys : DropTyList) :
      ConstDestructList emptyDestructEnv .runtimeFn tys := by
    cases tys with
    | nil => exact trivial
    | cons head tail =>
      exact ⟨constDestruct_runtime_universal head, constDestructList_runtime_universal tail⟩
end

/-- `ManuallyDrop<T>` is unconditionally `[const] Destruct` even when `T` has a non-const `Drop`. -/
theorem manuallyDrop_shields_nonConstDrop (d : Nat) :
    ConstDestruct emptyDestructEnv .constItem (.manuallyDrop (.adt .nil (.nonConstDrop d))) ∧
    runDropCtfe (.manuallyDrop (.adt .nil (.nonConstDrop d))) = some 0 :=
  ⟨trivial, rfl⟩

/-! ## Section 6: `ValTree` Structural-Equality Substitution Invariance -/

/-
  Canonical `ValTree` representation mirroring `rustc_middle::ty::ValTreeKind`
  (`compiler/rustc_middle/src/ty/consts/valtree.rs:33` and
  `compiler/rustc_const_eval/src/const_eval/valtrees.rs:21-190`):
    * `leaf bits sizeBytes` models `ValTreeKind::Leaf(ScalarInt)`
    * `branch children`     models `ValTreeKind::Branch(&[ty::Const])`
      (including ZST `branch .nil`, enums with prepended `u32` variant-index leaf,
      struct/tuple fields, arrays, slices, and `&'static str` UTF-8 byte branches).
-/
mutual
  inductive ValTree where
    | leaf   (bits : Nat) (sizeBytes : Nat)
    | branch (children : ValTreeList)

  inductive ValTreeList where
    | nil
    | cons (head : ValTree) (tail : ValTreeList)
end

/-- Length of a `ValTreeList` (models `reconstruct_place_meta` slice/str element count). -/
noncomputable def ValTreeList.length : ValTreeList → Nat
  | .nil => 0
  | .cons _ tail => Nat.succ (ValTreeList.length tail)

/- Structural Boolean equality on `ValTree` (pure structural recursion, zero `._unsafe_rec`). -/
mutual
  noncomputable def ValTree.beq : ValTree → ValTree → Bool
    | .leaf b₁ s₁, .leaf b₂ s₂ => Nat.beq b₁ b₂ && Nat.beq s₁ s₂
    | .branch c₁,  .branch c₂  => ValTreeList.beq c₁ c₂
    | _,           _           => false

  noncomputable def ValTreeList.beq : ValTreeList → ValTreeList → Bool
    | .nil,          .nil          => true
    | .cons h₁ t₁,   .cons h₂ t₂   => ValTree.beq h₁ h₂ && ValTreeList.beq t₁ t₂
    | _,             _             => false
end

theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => constructor <;> intro _ <;> rfl
    | succ b' =>
      constructor <;> intro h <;> cases h
  | succ a' ih =>
    cases b with
    | zero =>
      constructor <;> intro h <;> cases h
    | succ b' =>
      have h := ih b'
      constructor
      · intro hbeq
        exact congrArg Nat.succ (h.mp hbeq)
      · intro heq
        injection heq with h'
        exact h.mpr h'

theorem bool_and_eq_true_iff (a b : Bool) : (a && b) = true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h.1⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h.1⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h.2⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/- Structural equality reflection: `ValTree.beq v₁ v₂ = true ↔ v₁ = v₂`. -/
mutual
  theorem ValTree.beq_eq_true_iff (v₁ v₂ : ValTree) :
      ValTree.beq v₁ v₂ = true ↔ v₁ = v₂ := by
    cases v₁ with
    | leaf b₁ s₁ =>
      cases v₂ with
      | leaf b₂ s₂ =>
        constructor
        · intro h
          have hand := (bool_and_eq_true_iff _ _).mp h
          have hb := (nat_beq_true_iff b₁ b₂).mp hand.1
          have hs := (nat_beq_true_iff s₁ s₂).mp hand.2
          subst hb; subst hs; rfl
        · intro heq
          injection heq with hb hs
          subst hb; subst hs
          exact (bool_and_eq_true_iff _ _).mpr ⟨(nat_beq_true_iff b₁ b₁).mpr rfl,
                                                (nat_beq_true_iff s₁ s₁).mpr rfl⟩
      | branch _ =>
        constructor <;> intro h <;> cases h
    | branch c₁ =>
      cases v₂ with
      | leaf _ _ =>
        constructor <;> intro h <;> cases h
      | branch c₂ =>
        have ih := ValTreeList.beq_eq_true_iff c₁ c₂
        constructor
        · intro h
          exact congrArg ValTree.branch (ih.mp h)
        · intro heq
          injection heq with hc
          exact ih.mpr hc

  theorem ValTreeList.beq_eq_true_iff (c₁ c₂ : ValTreeList) :
      ValTreeList.beq c₁ c₂ = true ↔ c₁ = c₂ := by
    cases c₁ with
    | nil =>
      cases c₂ with
      | nil => constructor <;> intro _ <;> rfl
      | cons _ _ => constructor <;> intro h <;> cases h
    | cons h₁ t₁ =>
      cases c₂ with
      | nil => constructor <;> intro h <;> cases h
      | cons h₂ t₂ =>
        have ihh := ValTree.beq_eq_true_iff h₁ h₂
        have iht := ValTreeList.beq_eq_true_iff t₁ t₂
        constructor
        · intro h
          have hand := (bool_and_eq_true_iff _ _).mp h
          rw [ihh.mp hand.1, iht.mp hand.2]
        · intro heq
          injection heq with hh ht
          exact (bool_and_eq_true_iff _ _).mpr ⟨ihh.mpr hh, iht.mpr ht⟩
end

/-- Semantic structural equality on canonical `ValTree`s. -/
def StructEq (v₁ v₂ : ValTree) : Prop := ValTree.beq v₁ v₂ = true

theorem structEq_iff_eq (v₁ v₂ : ValTree) : StructEq v₁ v₂ ↔ v₁ = v₂ :=
  ValTree.beq_eq_true_iff v₁ v₂

theorem structEq_refl (v : ValTree) : StructEq v v :=
  (structEq_iff_eq v v).mpr rfl

theorem structEq_symm {v₁ v₂ : ValTree} (h : StructEq v₁ v₂) : StructEq v₂ v₁ :=
  (structEq_iff_eq v₂ v₁).mpr ((structEq_iff_eq v₁ v₂).mp h).symm

theorem structEq_trans {v₁ v₂ v₃ : ValTree}
    (h1 : StructEq v₁ v₂) (h2 : StructEq v₂ v₃) : StructEq v₁ v₃ :=
  (structEq_iff_eq v₁ v₃).mpr (Eq.trans ((structEq_iff_eq v₁ v₂).mp h1) ((structEq_iff_eq v₂ v₃).mp h2))

/--
  Type constructor application parameterized by a canonical `ValTree` const
  generic argument, modeling `Foo<const C: T>` (`Ty::new_adt(def, [Const::Value(v)])`).
-/
structure TyApp where
  typeCon : TypeConId
  arg     : ValTree

/--
  Core Theorem `valTree_eq_iff_type_eq`:
  Two instantiations of a const-generic type constructor `TyApp base v₁` and
  `TyApp base v₂` are identical types iff their `ValTree` arguments are
  structurally equal (`StructEq v₁ v₂`).
-/
theorem valTree_eq_iff_type_eq (base : TypeConId) (v₁ v₂ : ValTree) :
    StructEq v₁ v₂ ↔ TyApp.mk base v₁ = TyApp.mk base v₂ := by
  constructor
  · intro h
    have hv : v₁ = v₂ := (structEq_iff_eq v₁ v₂).mp h
    subst hv
    rfl
  · intro hty
    injection hty with _ hv
    exact (structEq_iff_eq v₁ v₂).mpr hv

/--
  Leibniz Substitutivity for `ValTree`-indexed types:
  Any type-level property `P : TyApp → Prop` (trait impl membership, layout,
  associated type projection, borrowck invariance) is strictly invariant under
  `StructEq`.
-/
theorem valTree_leibniz_substitutivity (base : TypeConId) (P : TyApp → Prop)
    {v₁ v₂ : ValTree} (h : StructEq v₁ v₂) :
    P (TyApp.mk base v₁) ↔ P (TyApp.mk base v₂) := by
  have hty : TyApp.mk base v₁ = TyApp.mk base v₂ := (valTree_eq_iff_type_eq base v₁ v₂).mp h
  rw [hty]

/--
  Unsized `ValTree` length reconstruction (`reconstruct_place_meta`, `valtrees.rs:223-255`):
  Equal `&'static str` / `&[u8]` branch `ValTree`s necessarily reconstruct the
  exact same slice length metadata (`Route<PATH>::len()`).
-/
theorem unsized_str_valtree_length_reconstruction {c₁ c₂ : ValTreeList}
    (h : StructEq (.branch c₁) (.branch c₂)) :
    ValTreeList.length c₁ = ValTreeList.length c₂ := by
  have heq : ValTree.branch c₁ = ValTree.branch c₂ := (structEq_iff_eq _ _).mp h
  injection heq with hc
  rw [hc]

/-
  Types classified by `ConstParamTy_` (`library/core/src/marker.rs:1109-1145` and
  `compiler/rustc_trait_selection/src/traits/misc.rs:92-201`).
-/
mutual
  inductive ValTreeTy where
    | uint      (sizeBytes : Nat)
    | boolTy
    | charTy
    | unitTy
    | array     (elem : ValTreeTy) (len : Nat)
    | slice     (elem : ValTreeTy)
    | strTy
    | sharedRef (inner : ValTreeTy)
    | adtStruct (fields : ValTreeTyList)
    | adtEnum   (variants : ValTreeTyList) -- representative field-list per variant
    | float32
    | rawPtr
    | unionTy

  inductive ValTreeTyList where
    | nil
    | cons (head : ValTreeTy) (tail : ValTreeTyList)
end

/-
  Exact admissibility gate for `ConstParamTy_` parameterized by whether
  `#![feature(unsized_const_params)]` is enabled (`allowUnsized : Bool`).
  Mirrors `type_allowed_to_implement_const_param_ty` (`misc.rs:92-201`).
-/
mutual
  noncomputable def ConstParamTyAdmissible (allowUnsized : Bool) : ValTreeTy → Prop
    | .uint _           => True
    | .boolTy           => True
    | .charTy           => True
    | .unitTy           => True
    | .array elem _     => ConstParamTyAdmissible allowUnsized elem
    | .slice elem       => allowUnsized = true ∧ ConstParamTyAdmissible allowUnsized elem
    | .strTy            => allowUnsized = true
    | .sharedRef inner  => allowUnsized = true ∧ ConstParamTyAdmissible allowUnsized inner
    | .adtStruct fields => ConstParamTyListAdmissible allowUnsized fields
    | .adtEnum vars     => ConstParamTyListAdmissible allowUnsized vars
    | .float32          => False
    | .rawPtr           => False
    | .unionTy          => False

  noncomputable def ConstParamTyListAdmissible (allowUnsized : Bool) : ValTreeTyList → Prop
    | .nil             => True
    | .cons head tail  =>
        ConstParamTyAdmissible allowUnsized head ∧
        ConstParamTyListAdmissible allowUnsized tail
end

/-- `f32` is rejected by `ConstParamTy_` even with `unsized_const_params` enabled (`ct_07`). -/
theorem float32_rejected_by_constParamTy (allowUnsized : Bool) :
    ¬ ConstParamTyAdmissible allowUnsized .float32 := fun h => h

/-- `*const T` is rejected by `ConstParamTy_` even with `unsized_const_params` enabled (`ct_08`). -/
theorem rawPtr_rejected_by_constParamTy (allowUnsized : Bool) :
    ¬ ConstParamTyAdmissible allowUnsized .rawPtr := fun h => h

/-- `union` is rejected by `ConstParamTy_` (`misc.rs:122,150`, `valtrees.rs:174`). -/
theorem union_rejected_by_constParamTy (allowUnsized : Bool) :
    ¬ ConstParamTyAdmissible allowUnsized .unionTy := fun h => h

/-- `&'static str` requires `unsized_const_params` (`ct_09`): rejected when `false`, accepted when `true`. -/
theorem ref_str_requires_unsized_const_params :
    ¬ ConstParamTyAdmissible false (.sharedRef .strTy) ∧
    ConstParamTyAdmissible true (.sharedRef .strTy) := by
  refine ⟨?_, ⟨rfl, rfl⟩⟩
  intro h
  cases h.1

/-- Struct containing an `f32` or `*const u8` field is rejected recursively (`all_fields_implement_trait`). -/
theorem struct_with_float_rejected (allowUnsized : Bool) :
    ¬ ConstParamTyAdmissible allowUnsized (.adtStruct (.cons .float32 .nil)) := by
  intro h
  exact h.1

theorem struct_with_rawPtr_rejected (allowUnsized : Bool) :
    ¬ ConstParamTyAdmissible allowUnsized (.adtStruct (.cons .rawPtr .nil)) := by
  intro h
  exact h.1

/--
  Abstract Necessity Theorem for Leibniz Substitutivity:
  Suppose a const-generic type system embeds values of domain `α` (equipped with
  a semantic equality relation `R : α → α → Prop`) into canonical `ValTree`s via
  an encoding `enc : α → ValTree` and equates types by `TyApp base (enc x) = TyApp base (enc y)`.
  Then `R` agrees with type-level Leibniz substitutivity (`∀ P, R x y ↔ (P (TyApp base (enc x)) ↔ P (TyApp base (enc y)))`)
  ONLY IF `R` is an equivalence relation AND `enc` collapses `R`-equal elements (`R x y ↔ enc x = enc y`).
-/
theorem leibniz_substitutivity_requires_equiv_and_canonical
    {α : Type} (R : α → α → Prop) (enc : α → ValTree) (base : TypeConId)
    (hAgree : ∀ x y : α, R x y ↔ TyApp.mk base (enc x) = TyApp.mk base (enc y)) :
    (∀ x : α, R x x) ∧
    (∀ x y : α, R x y → R y x) ∧
    (∀ x y z : α, R x y → R y z → R x z) ∧
    (∀ x y : α, R x y ↔ enc x = enc y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact (hAgree x x).mpr rfl
  · intro x y hxy
    exact (hAgree y x).mpr ((hAgree x y).mp hxy).symm
  · intro x y z hxy hyz
    exact (hAgree x z).mpr (Eq.trans ((hAgree x y).mp hxy) ((hAgree y z).mp hyz))
  · intro x y
    constructor
    · intro hxy
      have hty := (hAgree x y).mp hxy
      exact congrArg TyApp.arg hty
    · intro henc
      exact (hAgree x y).mpr (congrArg (TyApp.mk base) henc)

/-! ## Section 7: Four Constructive Sharpness Counterexamples -/

/-- Trait ID and type ID for Counterexample 1 (mirrors `ct_05`). -/
def myOpTraitId : TraitId := 10
def u32TyId : ConcreteTy := 32

/-- `const impl MyOp for u32 { fn op(self) -> u32 { 1 } }`. -/
def myOpConstImpl : ImplEntry where
  implId    := 1
  traitId   := myOpTraitId
  targetTy  := u32TyId
  isConst   := true
  semantics := fun _ => 1

/-- `impl MyOp for u32 { fn op(self) -> u32 { 2 } }`. -/
def myOpRuntimeImpl : ImplEntry where
  implId    := 2
  traitId   := myOpTraitId
  targetTy  := u32TyId
  isConst   := false
  semantics := fun _ => 2

/-- Hypothetical incoherent registry permitting both `const impl` and `impl` for `(MyOp, u32)`. -/
def incoherentDualRegistry : ImplList :=
  .cons myOpConstImpl (.cons myOpRuntimeImpl .nil)

/--
  Counterexample 1 (`ce1_dual_const_runtime_impl_breaks_ctfe_confluence`):
  Relaxing single-impl coherence to allow overlapping `const impl MyOp for u32`
  (returning `1`) and `impl MyOp for u32` (returning `2`) destroys CTFE-vs.-runtime
  observational confluence: the same call evaluates to `1` in CTFE and `2` at runtime (`1 ≠ 2`).
-/
theorem ce1_dual_const_runtime_impl_breaks_ctfe_confluence :
    ¬ Coherent incoherentDualRegistry ∧
    ∃ (outCtfe outRt : Nat),
      EvalCtfeDispatch incoherentDualRegistry myOpTraitId u32TyId 0 outCtfe ∧
      EvalRuntimeDispatch incoherentDualRegistry myOpTraitId u32TyId 0 outRt ∧
      outCtfe ≠ outRt := by
  constructor
  · intro hCoh
    have heq : myOpConstImpl = myOpRuntimeImpl :=
      hCoh myOpConstImpl myOpRuntimeImpl .here (.there .here) rfl rfl
    have h12 : (1 : Nat) = 2 := congrArg ImplEntry.implId heq
    cases h12
  · refine ⟨1, 2, ?_, ?_, ?_⟩
    · exact ⟨myOpConstImpl, .here, rfl, rfl, rfl, rfl⟩
    · exact ⟨myOpRuntimeImpl, .there .here, rfl, rfl, rfl⟩
    · intro h
      cases h

/-- Concrete non-const `Drop` type for Counterexample 2 (mirrors `ct_03` / `ct_13`). -/
def nonConstDropAdt : DropTy := .adt .nil (.nonConstDrop 99)

/--
  Counterexample 2 (`ce2_missing_const_destruct_executes_nonconst_drop_in_ctfe`):
  In `const fn drop_generic<T>(_x: T)` without `T: [const] Destruct`, `T` has
  only the default `.normal` destruct capability (`emptyDestructEnv 0 = .normal`),
  so:
    1. `ConstDestruct emptyDestructEnv .constFn (.param 0)` is FALSE (`E0493`),
    2. If that check were omitted, instantiating `T := NonConstDrop` yields a
       type that violates `ConstDestruct emptyDestructEnv .constItem`, triggers
       `DropHitsNonConst`, and gets stuck (`runDropCtfe = none`) in CTFE while
       executing cleanly (`runDropRuntime = some 99`) at runtime.
-/
theorem ce2_missing_const_destruct_executes_nonconst_drop_in_ctfe :
    ¬ ConstDestruct emptyDestructEnv .constFn (.param 0) ∧
    ¬ ConstDestruct emptyDestructEnv .constItem (substDropTy (fun _ => nonConstDropAdt) (.param 0)) ∧
    DropHitsNonConst (substDropTy (fun _ => nonConstDropAdt) (.param 0)) ∧
    runDropCtfe (substDropTy (fun _ => nonConstDropAdt) (.param 0)) = none ∧
    runDropRuntime (substDropTy (fun _ => nonConstDropAdt) (.param 0)) = some 99 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro h
    exact h
  · intro h
    cases h.2
  · exact Or.inr trivial

/-- IEEE-754 binary32 bit encodings (matching live probe `ct_17`). -/
def posZeroF32Bits : Nat := 0x00000000
def negZeroF32Bits : Nat := 0x80000000
def qNaNF32Bits    : Nat := 0x7fc00000

/--
  Minimal IEEE-754 `f32` equality model over the three distinguishing bit patterns
  (`+0.0`, `-0.0`, `qNaN`, plus normal finite bit patterns):
    * `qNaN == _` and `_ == qNaN` are `false` (irreflexive on `NaN`)
    * `+0.0 == -0.0` and `-0.0 == +0.0` are `true` despite distinct bit patterns
    * Otherwise bit-pattern equality.
-/
def ieeeF32Eq (a b : Nat) : Bool :=
  if Nat.beq a qNaNF32Bits || Nat.beq b qNaNF32Bits then
    false
  else if (Nat.beq a posZeroF32Bits && Nat.beq b negZeroF32Bits) ||
          (Nat.beq a negZeroF32Bits && Nat.beq b posZeroF32Bits) then
    true
  else
    Nat.beq a b

/-- Canonical bit-level `ValTree` leaf encoding of an `f32` (as in `valtrees.rs:113-118`). -/
def f32ToValTree (bits : Nat) : ValTree := .leaf bits 4

/-- Type-level predicate inspecting whether a `TyApp`'s `ValTree` leaf has sign bit 0 (`posZero`). -/
def isPosZeroTy (t : TyApp) : Prop :=
  t.arg = f32ToValTree posZeroF32Bits

/--
  Counterexample 3 (`ce3_float_neg_zero_breaks_type_substitutivity`):
  IEEE-754 `f32` violates BOTH prerequisites of `leibniz_substitutivity_requires_equiv_and_canonical`:
    1. Signed-zero non-canonicity: `ieeeF32Eq (+0.0) (-0.0) = true`, yet their
       canonical `ValTree` leaves are unequal (`0x00000000 ≠ 0x80000000`),
       so the concrete type predicate `isPosZeroTy` holds of `TyApp 0 (valtree +0.0)`
       and FAILS of `TyApp 0 (valtree -0.0)` — breaking Leibniz substitutivity!
    2. NaN non-reflexivity: `ieeeF32Eq qNaN qNaN = false`, yet
       `TyApp 0 (valtree qNaN) = TyApp 0 (valtree qNaN)`, refuting any agreement
       between IEEE-754 `PartialEq` and type equality!
-/
theorem ce3_float_neg_zero_breaks_type_substitutivity :
    ieeeF32Eq posZeroF32Bits negZeroF32Bits = true ∧
    ¬ StructEq (f32ToValTree posZeroF32Bits) (f32ToValTree negZeroF32Bits) ∧
    isPosZeroTy (TyApp.mk 0 (f32ToValTree posZeroF32Bits)) ∧
    ¬ isPosZeroTy (TyApp.mk 0 (f32ToValTree negZeroF32Bits)) ∧
    ieeeF32Eq qNaNF32Bits qNaNF32Bits = false ∧
    (¬ ∃ base : TypeConId, ∀ x y : Nat,
        (ieeeF32Eq x y = true) ↔ TyApp.mk base (f32ToValTree x) = TyApp.mk base (f32ToValTree y)) := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_⟩
  · intro h
    have heq := (structEq_iff_eq _ _).mp h
    injection heq with hbits _
    have hne : posZeroF32Bits ≠ negZeroF32Bits := by
      intro h0
      have hb : Nat.beq posZeroF32Bits negZeroF32Bits = true := (nat_beq_true_iff _ _).mpr h0
      cases hb
    exact hne hbits
  · intro h
    change f32ToValTree negZeroF32Bits = f32ToValTree posZeroF32Bits at h
    injection h with hbits _
    have hb : Nat.beq negZeroF32Bits posZeroF32Bits = true := (nat_beq_true_iff _ _).mpr hbits
    cases hb
  · intro hex
    rcases hex with ⟨base, hAgree⟩
    have hRefl := (leibniz_substitutivity_requires_equiv_and_canonical
      (fun x y => ieeeF32Eq x y = true) f32ToValTree base hAgree).1 qNaNF32Bits
    cases hRefl

/-- Abstract CTFE pointer carrying provenance (`AllocId`) and byte offset. -/
structure CtfePtr where
  alloc  : AllocId
  offset : Nat

/-- Tri-state return value of `ptr_guaranteed_cmp` (`machine.rs:273-365`): 0=neq, 1=eq, 2=unknown. -/
inductive GuaranteedCmpResult where
  | guaranteedNeq
  | guaranteedEq
  | unknown

/--
  CTFE `guaranteed_cmp` on two pointers to immutable constant allocations
  (not guaranteed-disjoint statics): same `AllocId` + same offset => `guaranteedEq`,
  different `AllocId`s => `unknown` (code `2`, because the linker/ICF may merge
  or separate immutable constants at runtime).
-/
def ctfeConstPtrCmp (p q : CtfePtr) : GuaranteedCmpResult :=
  if Nat.beq p.alloc q.alloc then
    if Nat.beq p.offset q.offset then .guaranteedEq else .guaranteedNeq
  else
    .unknown

/-- Concrete runtime address assignment mapping each `AllocId` to a base address. -/
abbrev AddressLayout := AllocId → Nat

/-- Concrete runtime pointer equality under a given linker/ASLR `AddressLayout`. -/
def runtimePtrEq (layout : AddressLayout) (p q : CtfePtr) : Bool :=
  Nat.beq (layout p.alloc + p.offset) (layout q.alloc + q.offset)

/-- Two distinct immutable constant allocations `allocA = 1`, `allocB = 2` at offset 0. -/
def ptrConstA : CtfePtr := { alloc := 1, offset := 0 }
def ptrConstB : CtfePtr := { alloc := 2, offset := 0 }

/-- Linker layout with ICF/rodata deduplication: both constants share base address `0x1000`. -/
def layoutMerged : AddressLayout := fun _ => 0x1000

/-- Linker layout without merging: distinct base addresses `0x1000` and `0x2000`. -/
def layoutDistinct : AddressLayout := fun aid =>
  match aid with
  | 1 => 0x1000
  | _ => 0x2000

/--
  Counterexample 4 (`ce4_ctfe_ptr_comparison_nondeterministic`):
  For two distinct immutable constant allocations `ptrConstA` and `ptrConstB`:
    1. CTFE `ctfeConstPtrCmp` returns `.unknown` (corresponding to `ptr_guaranteed_cmp`
       returning `2`, and `binary_ptr_op` rejecting comparison at compile time),
    2. Under `layoutMerged`, `runtimePtrEq` is `true`; under `layoutDistinct`,
       `runtimePtrEq` is `false`,
    3. Therefore NO layout-independent Boolean equality oracle `oracle : CtfePtr → CtfePtr → Bool`
       can agree with runtime pointer equality across all valid linker layouts —
       refuting deterministic `ValTree` canonicalization of provenance-bearing raw pointers!
-/
theorem ce4_ctfe_ptr_comparison_nondeterministic :
    ctfeConstPtrCmp ptrConstA ptrConstB = .unknown ∧
    runtimePtrEq layoutMerged ptrConstA ptrConstB = true ∧
    runtimePtrEq layoutDistinct ptrConstA ptrConstB = false ∧
    runtimePtrEq layoutMerged ptrConstA ptrConstB ≠ runtimePtrEq layoutDistinct ptrConstA ptrConstB ∧
    (¬ ∃ oracle : CtfePtr → CtfePtr → Bool,
        ∀ layout : AddressLayout, ∀ p q : CtfePtr, oracle p q = runtimePtrEq layout p q) := by
  refine ⟨rfl, rfl, rfl, bool_true_ne_false, ?_⟩
  intro hex
  rcases hex with ⟨oracle, hAgree⟩
  have h1 : oracle ptrConstA ptrConstB = true := hAgree layoutMerged ptrConstA ptrConstB
  have h2 : oracle ptrConstA ptrConstB = false := hAgree layoutDistinct ptrConstA ptrConstB
  have htf : (true : Bool) = false := Eq.trans h1.symm h2
  exact bool_true_ne_false htf

/-! ## Section 8: Integrated End-to-End Witnesses Matching Live `rustc` Probes -/

/-- Concrete trait & type IDs matching live probes `ct_01` / `ct_02` / `ct_11` / `ct_12`. -/
def combineTraitId : TraitId := 1
def constValTyId   : ConcreteTy := 100
def nonConstTyId   : ConcreteTy := 101

def combineConstValImpl : ImplEntry where
  implId    := 100
  traitId   := combineTraitId
  targetTy  := constValTyId
  isConst   := true
  semantics := fun x => x + 22

def combineNonConstImpl : ImplEntry where
  implId    := 101
  traitId   := combineTraitId
  targetTy  := nonConstTyId
  isConst   := false
  semantics := fun x => x + 22

def combineRegistry : ImplList :=
  .cons combineConstValImpl (.cons combineNonConstImpl .nil)

theorem combineRegistry_coherent : Coherent combineRegistry := by
  intro e₁ e₂ h₁ h₂ _ hty
  cases h₁ with
  | here =>
    cases h₂ with
    | here => rfl
    | there h₂' =>
      cases h₂' with
      | here =>
        have hb : Nat.beq 100 101 = true := (nat_beq_true_iff 100 101).mpr hty
        cases hb
      | there h₂'' => cases h₂''
  | there h₁' =>
    cases h₁' with
    | here =>
      cases h₂ with
      | here =>
        have hb : Nat.beq 101 100 = true := (nat_beq_true_iff 101 100).mpr hty
        cases hb
      | there h₂' =>
        cases h₂' with
        | here => rfl
        | there h₂'' => cases h₂''
    | there h₁'' => cases h₁''

/-- Environment for `const fn apply<T: [const] Combine>(a: T, b: T) -> T` (`ct_01`, `ct_02`). -/
def applyEnv : ParamEnv := fun pid tr =>
  if Nat.beq pid 0 && Nat.beq tr combineTraitId then some .maybe else none

/--
  Live-probe witness matching `ct_01` and `ct_02`:
    * `ConstVal` satisfies `applyEnv` in BOTH `constItem` and `runtimeFn`, and
      evaluates confluently to `42` on input `20`.
    * `NonConst` satisfies `applyEnv` in `runtimeFn` (evaluates to `42`),
      but FAILS `applyEnv` in `constItem` (`E0277`)!
-/
theorem witness_ct01_ct02_apply_confluence_and_rejection :
    ValidSubst combineRegistry applyEnv .constItem (fun _ => constValTyId) ∧
    ValidSubst combineRegistry applyEnv .runtimeFn (fun _ => constValTyId) ∧
    ValidSubst combineRegistry applyEnv .runtimeFn (fun _ => nonConstTyId) ∧
    ¬ ValidSubst combineRegistry applyEnv .constItem (fun _ => nonConstTyId) ∧
    EvalCtfeDispatch combineRegistry combineTraitId constValTyId 20 42 ∧
    EvalRuntimeDispatch combineRegistry combineTraitId constValTyId 20 42 := by
  refine ⟨?_, ?_, ?_, ?_, ⟨combineConstValImpl, .here, rfl, rfl, rfl, rfl⟩,
          ⟨combineConstValImpl, .here, rfl, rfl, rfl⟩⟩
  · intro pid tr b henv
    cases pid with
    | zero =>
      cases tr with
      | zero => cases henv
      | succ tr' =>
        cases tr' with
        | zero =>
          simp only [applyEnv] at henv
          injection henv with hb
          subst hb
          exact ⟨combineConstValImpl, .here, rfl, rfl, trivial⟩
        | succ _ => cases henv
    | succ _ => cases henv
  · intro pid tr b henv
    cases pid with
    | zero =>
      cases tr with
      | zero => cases henv
      | succ tr' =>
        cases tr' with
        | zero =>
          simp only [applyEnv] at henv
          injection henv with hb
          subst hb
          exact ⟨combineConstValImpl, .here, rfl, rfl, trivial⟩
        | succ _ => cases henv
    | succ _ => cases henv
  · intro pid tr b henv
    cases pid with
    | zero =>
      cases tr with
      | zero => cases henv
      | succ tr' =>
        cases tr' with
        | zero =>
          simp only [applyEnv] at henv
          injection henv with hb
          subst hb
          exact ⟨combineNonConstImpl, .there .here, rfl, rfl, trivial⟩
        | succ _ => cases henv
    | succ _ => cases henv
  · intro hBad
    have hSat := hBad 0 combineTraitId .maybe rfl
    rcases hSat with ⟨e, hmem, _, hty, hcap⟩
    cases hmem with
    | here =>
      have hb : Nat.beq 100 101 = true := (nat_beq_true_iff 100 101).mpr hty
      cases hb
    | there hmem' =>
      cases hmem' with
      | here => exact False.elim hcap
      | there hmem'' => cases hmem''

/--
  Live-probe witness matching `ct_04`, `ct_13`, and `ct_14`:
  With `T: [const] Destruct`, a `const impl Drop` ADT (`delta = 57`) passes CTFE
  drop checking and evaluates confluently in CTFE and runtime (`57`), while a
  non-const `Drop` ADT is admitted at runtime and rejected in `constItem`.
-/
def constDropEnv : DestructEnv := fun pid =>
  match pid with
  | 0 => .maybe
  | _ => .normal

def dropMutAdt : DropTy := .adt (.cons .prim .nil) (.constDrop 57)

theorem witness_ct04_ct13_ct14_const_destruct :
    ConstDestruct constDropEnv .constFn (.param 0) ∧
    ConstDestruct emptyDestructEnv .constItem dropMutAdt ∧
    runDropCtfe dropMutAdt = some 57 ∧
    runDropRuntime dropMutAdt = some 57 ∧
    ConstDestruct emptyDestructEnv .runtimeFn nonConstDropAdt ∧
    ¬ ConstDestruct emptyDestructEnv .constItem nonConstDropAdt := by
  refine ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩, rfl, rfl, ⟨trivial, rfl⟩, ?_⟩
  intro h
  cases h.2

/--
  Live-probe witness matching `ct_06` and `ct_09`:
  Struct `Config { mode: Mode, stride: u8 }` is admissible under `min_adt_const_params`
  (`allowUnsized = false`), its two distinct configurations (`FAST_CFG` vs `CHECKED_CFG`)
  yield distinct `ValTree`s and distinct types, and `Route<"/api/v1/x">` vs `Route<"/">`
  reconstruct distinct slice lengths (`9 ≠ 1`).
-/
def configTy : ValTreeTy :=
  .adtStruct (.cons (.adtEnum (.cons .unitTy (.cons .unitTy .nil))) (.cons (.uint 1) .nil))

def fastCfgValTree : ValTree :=
  .branch (.cons (.branch (.cons (.leaf 0 4) .nil)) (.cons (.leaf 4 1) .nil))

def checkedCfgValTree : ValTree :=
  .branch (.cons (.branch (.cons (.leaf 1 4) .nil)) (.cons (.leaf 1 1) .nil))

def routeApiChildren : ValTreeList :=
  .cons (.leaf 47 1) (.cons (.leaf 97 1) (.cons (.leaf 112 1) (.cons (.leaf 105 1)
    (.cons (.leaf 47 1) (.cons (.leaf 118 1) (.cons (.leaf 49 1)
      (.cons (.leaf 47 1) (.cons (.leaf 120 1) .nil))))))))

def routeRootChildren : ValTreeList :=
  .cons (.leaf 47 1) .nil

theorem witness_ct06_ct09_adt_and_str_valtree :
    ConstParamTyAdmissible false configTy ∧
    TyApp.mk 60 fastCfgValTree ≠ TyApp.mk 60 checkedCfgValTree ∧
    ValTreeList.length routeApiChildren = 9 ∧
    ValTreeList.length routeRootChildren = 1 ∧
    TyApp.mk 90 (.branch routeApiChildren) ≠ TyApp.mk 90 (.branch routeRootChildren) := by
  refine ⟨⟨⟨trivial, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩, ?_, rfl, rfl, ?_⟩
  · intro hty
    have hs := (valTree_eq_iff_type_eq 60 fastCfgValTree checkedCfgValTree).mpr hty
    cases hs
  · intro hty
    have hs := (valTree_eq_iff_type_eq 90 (.branch routeApiChildren) (.branch routeRootChildren)).mpr hty
    have hlen := unsized_str_valtree_length_reconstruction hs
    cases hlen

end Anneal.ConstTraitAndValTreeSoundness
