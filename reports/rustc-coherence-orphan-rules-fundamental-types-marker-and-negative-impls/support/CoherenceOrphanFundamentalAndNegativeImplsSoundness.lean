/-!
# Soundness Model: `rustc` Coherence, Covered-Type Orphan Checking (`E0117`/`E0210`),
# `#[fundamental]` Types & Traits, `#[marker]` Impls (`E0714`/`E0715`), Negative Coherence
# (`with_negative_coherence`, `impl !Trait`), and `zerocopy` Reason-Marker Coherence

Standalone kernel-checked Lean `v4.34.1` formalization companion to the reference package
`rustc-coherence-orphan-rules-fundamental-types-marker-and-negative-impls`.

Purity & TCB guarantees (verified against the Lean `v4.34.1` kernel):
- Zero `sorry`, zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool`,
  zero `Lean.trustCompiler`, zero `omega`, zero `bv_decide`, zero `native_decide`,
  zero `partial def`, zero `unsafe`, and zero `._unsafe_rec` auxiliary constants.
- Every `def` carries `noncomputable` explicitly (no `noncomputable section`, no
  `deriving DecidableEq`/`Repr` on recursive inductives), suppressing compiler
  `._unsafe_rec` synthesis while keeping every definition and theorem constructive.
-/

namespace RustcCoherence

/-!
## Part 1: Multi-Crate Dependency DAG, Type Grammar, Fundamental Constructors, and Substitutions
-/

/-- Crate identifier in a multi-crate compilation graph (`0` = `core`/`alloc`). -/
abbrev CrateId := Nat

/-- Trait identifier. -/
abbrev TraitId := Nat

/-- Nominal ADT (`struct` / `enum` / `union`) identifier. -/
abbrev AdtId := Nat

/-- Impl-header generic type variable identifier (`ty::Param` / `ty::Infer`). -/
abbrev TyVar := Nat

/-- Impl block identifier. -/
abbrev ImplId := Nat

/-- Associated item identifier (`const` / `fn` / `type`). -/
abbrev AssocItemId := Nat

/-- Constructive `Bool` negation helper (avoids stdlib dependency surprises). -/
noncomputable def boolNot : Bool → Bool
  | true => false
  | false => true

/-- Constructive `Nat` equality refl helper. -/
private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

/-- Constructive inversion for `Nat.beq m n = true`. -/
private theorem nat_beq_true_eq {m n : Nat} (h : Nat.beq m n = true) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ _ => cases h
  | succ m ih =>
    cases n with
    | zero => cases h
    | succ n =>
      have hmn : m = n := ih h
      rw [hmn]

/-- Constructive completeness for `Nat.beq m n = false` when `m ≠ n`. -/
private theorem nat_beq_false_of_ne {m n : Nat} (hne : m ≠ n) : Nat.beq m n = false := by
  cases h : Nat.beq m n with
  | false => rfl
  | true =>
    exact False.elim (hne (nat_beq_true_eq h))

/-- Constructive `Nat` inequality `n + 1 ≠ n` without `omega`. -/
private theorem nat_succ_ne_self (n : Nat) : n + 1 ≠ n := by
  induction n with
  | zero =>
    intro h
    cases h
  | succ k ih =>
    intro h
    injection h with h'
    exact ih h'

/-- Constructive list membership predicate (`Mem x xs`). -/
inductive Mem {α : Type} (x : α) : List α → Prop where
  | head {xs : List α} : Mem x (x :: xs)
  | tail {y : α} {xs : List α} : Mem x xs → Mem x (y :: xs)

/-- Constructive negative list membership predicate (`NoMem x xs`). -/
inductive NoMem {α : Type} (x : α) : List α → Prop where
  | nil : NoMem x []
  | cons {y : α} {xs : List α} : y ≠ x → NoMem x xs → NoMem x (y :: xs)

private theorem noMem_append {α : Type} {x : α} {xs ys : List α}
    (hx : NoMem x xs) (hy : NoMem x ys) : NoMem x (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons hne _ ih => exact .cons hne ih

private theorem mem_and_noMem_false {α : Type} {x : α} {xs : List α}
    (hm : Mem x xs) (hn : NoMem x xs) : False := by
  induction hm with
  | head =>
    cases hn with
    | cons hne _ => exact hne rfl
  | tail _ ih =>
    cases hn with
    | cons _ hns => exact ih hns

/-- Directed dependency relation `DependsOn` between crates in a multi-crate DAG.
`DirectDep c parent` means crate `c` depends directly on upstream crate `parent`. -/
structure CrateDAG where
  directDeps : CrateId → List CrateId
  traitOwner : TraitId → CrateId
  adtOwner : AdtId → CrateId
  isFundamentalAdt : AdtId → Bool
  isFundamentalTrait : TraitId → Bool
  isAutoTrait : TraitId → Bool
  isMarkerTrait : TraitId → Bool

/-- Reflexive-transitive upstream dependency reachability (`UpstreamOf dag parent child`
holds when `parent` is reachable upstream from `child`, i.e., `child` can name items
defined in `parent`). -/
inductive UpstreamOf (dag : CrateDAG) : CrateId → CrateId → Prop where
  | refl (c : CrateId) : UpstreamOf dag c c
  | step {mid child : CrateId} (parent : CrateId) :
      Mem mid (dag.directDeps child) →
      UpstreamOf dag parent mid →
      UpstreamOf dag parent child

/-- Strict upstream relation (`StrictUpstream dag u c`): `u ≠ c` and `c` depends
transitively on `u`. -/
noncomputable def StrictUpstream (dag : CrateDAG) (u c : CrateId) : Prop :=
  u ≠ c ∧ UpstreamOf dag u c

/-- Two crates `c₁` and `c₂` are mutually unrelated (neither depends on the other)
when neither appears in the transitive dependency closure of the other. -/
noncomputable def UnrelatedCrates (dag : CrateDAG) (c₁ c₂ : CrateId) : Prop :=
  c₁ ≠ c₂ ∧ ¬ UpstreamOf dag c₁ c₂ ∧ ¬ UpstreamOf dag c₂ c₁

/-- Modeling `Box<T, A>` orphan-traversal mode across `rustc` revisions:
- `allArgs` (`rustc 1.98.0-nightly`, `14210df0e`): `def.is_fundamental()` visits all `Box` args `[T, A]`.
- `elemOnly` (`rust-lang/rust` `main`, `0259d5e9a`, post-`allocator_api`): `SolverAdtLangItem::OwnedBox`
  visits `args.type_at(0)` (`T`) only, ignoring allocator `A`. -/
inductive BoxMode where
  | allArgs
  | elemOnly

/-- Surface/impl-header Rust type AST covering variables, primitives (`core`), built-in
references (`&T`, `&mut T`), `Box<T, A>`, `Pin<P>`, non-fundamental containers (`Vec<T>`,
tuples), and arbitrary nominal ADTs. -/
inductive Ty where
  | var (v : TyVar)
  | prim (p : Nat)
  | refShared (inner : Ty)
  | refMut (inner : Ty)
  | boxTy (elem alloc : Ty)
  | pinTy (ptr : Ty)
  | vecTy (elem : Ty)
  | tuple (fst snd : Ty)
  | adt (id : AdtId) (args : List Ty)

/-- Ground Rust types (no type variables `Ty.var`). -/
inductive GroundTy where
  | prim (p : Nat)
  | refShared (inner : GroundTy)
  | refMut (inner : GroundTy)
  | boxTy (elem alloc : GroundTy)
  | pinTy (ptr : GroundTy)
  | vecTy (elem : GroundTy)
  | tuple (fst snd : GroundTy)
  | adt (id : AdtId) (args : List GroundTy)

/-- Trait reference `[Self, T1, ..., Tn]` with `Self` strictly at head (`selfTy :: traitArgs`). -/
structure TraitRef where
  traitId : TraitId
  selfTy : Ty
  traitArgs : List Ty

/-- Linearized input type vector `[Self, T1, ..., Tn]` matching `TraitRef`'s traversal order
in `rustc_next_trait_solver::coherence::orphan_check_trait_ref`. -/
noncomputable def TraitRef.inputs (tr : TraitRef) : List Ty :=
  tr.selfTy :: tr.traitArgs

/-- Ground trait reference after substituting all impl generic parameters. -/
structure GroundTraitRef where
  traitId : TraitId
  selfTy : GroundTy
  traitArgs : List GroundTy

/-- Linearized input type vector of a ground trait reference. -/
noncomputable def GroundTraitRef.inputs (tr : GroundTraitRef) : List GroundTy :=
  tr.selfTy :: tr.traitArgs

/-- Grounding substitution mapping impl generic variables to ground types. -/
abbrev GroundSubst := TyVar → GroundTy

mutual
  /-- Apply a ground substitution `σ` to a type `Ty`. -/
  noncomputable def instTy (σ : GroundSubst) : Ty → GroundTy
    | .var v => σ v
    | .prim p => .prim p
    | .refShared t => .refShared (instTy σ t)
    | .refMut t => .refMut (instTy σ t)
    | .boxTy elem alloc => .boxTy (instTy σ elem) (instTy σ alloc)
    | .pinTy p => .pinTy (instTy σ p)
    | .vecTy e => .vecTy (instTy σ e)
    | .tuple a b => .tuple (instTy σ a) (instTy σ b)
    | .adt id args => .adt id (instTyList σ args)

  /-- Elementwise ground substitution on a list of types. -/
  noncomputable def instTyList (σ : GroundSubst) : List Ty → List GroundTy
    | [] => []
    | t :: ts => instTy σ t :: instTyList σ ts
end

/-- Instantiate a trait reference `TraitRef` with ground substitution `σ`. -/
noncomputable def instTraitRef (σ : GroundSubst) (tr : TraitRef) : GroundTraitRef :=
  { traitId := tr.traitId
    selfTy := instTy σ tr.selfTy
    traitArgs := instTyList σ tr.traitArgs }

private theorem instTraitRef_inputs (σ : GroundSubst) (tr : TraitRef) :
    (instTraitRef σ tr).inputs = instTyList σ tr.inputs :=
  rfl

/-- General (possibly non-ground) type substitution `Subst := TyVar → Ty`. -/
abbrev TySubst := TyVar → Ty

mutual
  /-- Apply a non-ground type substitution `σ` to `Ty`. -/
  noncomputable def substTy (σ : TySubst) : Ty → Ty
    | .var v => σ v
    | .prim p => .prim p
    | .refShared t => .refShared (substTy σ t)
    | .refMut t => .refMut (substTy σ t)
    | .boxTy elem alloc => .boxTy (substTy σ elem) (substTy σ alloc)
    | .pinTy p => .pinTy (substTy σ p)
    | .vecTy e => .vecTy (substTy σ e)
    | .tuple a b => .tuple (substTy σ a) (substTy σ b)
    | .adt id args => .adt id (substTyList σ args)

  /-- Elementwise non-ground type substitution on `List Ty`. -/
  noncomputable def substTyList (σ : TySubst) : List Ty → List Ty
    | [] => []
    | t :: ts => substTy σ t :: substTyList σ ts
end

/- Embed a ground type back into `Ty`. -/
mutual
  noncomputable def GroundTy.toTy : GroundTy → Ty
    | .prim p => .prim p
    | .refShared t => .refShared (GroundTy.toTy t)
    | .refMut t => .refMut (GroundTy.toTy t)
    | .boxTy elem alloc => .boxTy (GroundTy.toTy elem) (GroundTy.toTy alloc)
    | .pinTy p => .pinTy (GroundTy.toTy p)
    | .vecTy e => .vecTy (GroundTy.toTy e)
    | .tuple a b => .tuple (GroundTy.toTy a) (GroundTy.toTy b)
    | .adt id args => .adt id (groundTyListToTy args)

  noncomputable def groundTyListToTy : List GroundTy → List Ty
    | [] => []
    | t :: ts => GroundTy.toTy t :: groundTyListToTy ts
end

/-!
## Part 2: `rustc_next_trait_solver` Covered-Type Orphan Checker (`orphan_check_trait_ref`)
and Multi-Crate Separation Theorems
-/

/-- Early-exit result of `OrphanChecker::visit_ty` (`compiler/rustc_next_trait_solver/src/coherence.rs`). -/
inductive OrphanOutcome where
  | localTy
  | uncoveredParam
  | nonLocalInput

/-- Left-to-right combination rule for `OrphanChecker`:
if the prefix already settled on `localTy` or `uncoveredParam`, short-circuit (`ControlFlow::Break`);
only `nonLocalInput` (`ControlFlow::Continue(())`) proceeds to subsequent arguments. -/
noncomputable def combineOutcome (o₁ o₂ : OrphanOutcome) : OrphanOutcome :=
  match o₁ with
  | .localTy => .localTy
  | .uncoveredParam => .uncoveredParam
  | .nonLocalInput => o₂

mutual
  /-- Exact structural mirror of `OrphanChecker::visit_ty` in
  `compiler/rustc_next_trait_solver/src/coherence.rs` (`L325-458`):
  - `var` -> `uncoveredParam` (`InCrate::Local` mode)
  - `prim`, `vecTy`, `tuple` -> `nonLocalInput` (never descends into `Vec`/`tuple` args!)
  - `refShared`, `refMut`, `pinTy` -> transparently unwrap fundamental wrapper
  - `boxTy` -> unwrap `elem` (`elemOnly`, `0259d5e9a`) or `[elem, alloc]` (`allArgs`, `14210df0e`)
  - `adt id args` -> if `adtOwner id == crate` then `localTy`, else if `isFundamentalAdt id`
    then visit `args`, else `nonLocalInput` cutoff. -/
  noncomputable def visitTy (dag : CrateDAG) (boxMode : BoxMode) (crate : CrateId) :
      Ty → OrphanOutcome
    | .var _ => .uncoveredParam
    | .prim _ => .nonLocalInput
    | .refShared inner => visitTy dag boxMode crate inner
    | .refMut inner => visitTy dag boxMode crate inner
    | .boxTy elem alloc =>
      match boxMode with
      | .elemOnly => visitTy dag boxMode crate elem
      | .allArgs =>
        combineOutcome (visitTy dag boxMode crate elem) (visitTy dag boxMode crate alloc)
    | .pinTy ptr => visitTy dag boxMode crate ptr
    | .vecTy _ => .nonLocalInput
    | .tuple _ _ => .nonLocalInput
    | .adt id args =>
      match Nat.beq (dag.adtOwner id) crate with
      | true => .localTy
      | false =>
        match dag.isFundamentalAdt id with
        | true => visitTyList dag boxMode crate args
        | false => .nonLocalInput

  /-- Left-to-right traversal across `[Self, T1, ..., Tn]` or fundamental ADT arguments. -/
  noncomputable def visitTyList (dag : CrateDAG) (boxMode : BoxMode) (crate : CrateId) :
      List Ty → OrphanOutcome
    | [] => .nonLocalInput
    | t :: ts => combineOutcome (visitTy dag boxMode crate t) (visitTyList dag boxMode crate ts)
end

/-- `orphanCheck` succeeds for crate `c` implementing `tr` iff either:
1. `tr.traitId` is owned by `c` (`trait_ref.def_id.is_local()`), OR
2. `visitTyList dag boxMode c tr.inputs = .localTy` (a `c`-local nominal type is reached
   through only fundamental constructors before any uncovered generic type parameter). -/
noncomputable def orphanCheck (dag : CrateDAG) (boxMode : BoxMode) (c : CrateId) (tr : TraitRef) :
    Bool :=
  if Nat.beq (dag.traitOwner tr.traitId) c then
    true
  else
    match visitTyList dag boxMode c tr.inputs with
    | .localTy => true
    | _ => false

/-- Proposition that an impl in crate `c` passes `orphanCheck`. -/
noncomputable def OrphanPasses (dag : CrateDAG) (boxMode : BoxMode) (c : CrateId) (tr : TraitRef) :
    Prop :=
  orphanCheck dag boxMode c tr = true

/- Crate visibility well-scopedness: crate `c` can only mention traits and ADTs owned by
crates in its upstream transitive closure (`UpstreamOf dag owner c`). -/
mutual
  noncomputable def TyScopedInCrate (dag : CrateDAG) (c : CrateId) : Ty → Prop
    | .var _ => True
    | .prim _ => True
    | .refShared inner => TyScopedInCrate dag c inner
    | .refMut inner => TyScopedInCrate dag c inner
    | .boxTy elem alloc => TyScopedInCrate dag c elem ∧ TyScopedInCrate dag c alloc
    | .pinTy ptr => TyScopedInCrate dag c ptr
    | .vecTy elem => TyScopedInCrate dag c elem
    | .tuple a b => TyScopedInCrate dag c a ∧ TyScopedInCrate dag c b
    | .adt id args => UpstreamOf dag (dag.adtOwner id) c ∧ TyListScopedInCrate dag c args

  noncomputable def TyListScopedInCrate (dag : CrateDAG) (c : CrateId) : List Ty → Prop
    | [] => True
    | t :: ts => TyScopedInCrate dag c t ∧ TyListScopedInCrate dag c ts
end

noncomputable def TraitRefScopedInCrate (dag : CrateDAG) (c : CrateId) (tr : TraitRef) : Prop :=
  UpstreamOf dag (dag.traitOwner tr.traitId) c ∧
  TyScopedInCrate dag c tr.selfTy ∧
  TyListScopedInCrate dag c tr.traitArgs

/- Avoidance predicate: `TyAvoidsCrate dag k t` holds whenever no nominal ADT in `t` has
owner `k`. -/
mutual
  noncomputable def TyAvoidsCrate (dag : CrateDAG) (k : CrateId) : Ty → Prop
    | .var _ => True
    | .prim _ => True
    | .refShared inner => TyAvoidsCrate dag k inner
    | .refMut inner => TyAvoidsCrate dag k inner
    | .boxTy elem alloc => TyAvoidsCrate dag k elem ∧ TyAvoidsCrate dag k alloc
    | .pinTy ptr => TyAvoidsCrate dag k ptr
    | .vecTy elem => TyAvoidsCrate dag k elem
    | .tuple a b => TyAvoidsCrate dag k a ∧ TyAvoidsCrate dag k b
    | .adt id args => dag.adtOwner id ≠ k ∧ TyListAvoidsCrate dag k args

  noncomputable def TyListAvoidsCrate (dag : CrateDAG) (k : CrateId) : List Ty → Prop
    | [] => True
    | t :: ts => TyAvoidsCrate dag k t ∧ TyListAvoidsCrate dag k ts
end

noncomputable def TraitRefAvoidsCrate (dag : CrateDAG) (k : CrateId) (tr : TraitRef) : Prop :=
  dag.traitOwner tr.traitId ≠ k ∧
  TyAvoidsCrate dag k tr.selfTy ∧
  TyListAvoidsCrate dag k tr.traitArgs

mutual
  private theorem scoped_unrelated_avoids_ty (dag : CrateDAG) (c k : CrateId)
      (hNotUp : ¬ UpstreamOf dag k c) (t : Ty) (hSc : TyScopedInCrate dag c t) :
      TyAvoidsCrate dag k t := by
    cases t with
    | var _ => trivial
    | prim _ => trivial
    | refShared inner => exact scoped_unrelated_avoids_ty dag c k hNotUp inner hSc
    | refMut inner => exact scoped_unrelated_avoids_ty dag c k hNotUp inner hSc
    | boxTy elem alloc =>
      exact ⟨scoped_unrelated_avoids_ty dag c k hNotUp elem hSc.1,
             scoped_unrelated_avoids_ty dag c k hNotUp alloc hSc.2⟩
    | pinTy ptr => exact scoped_unrelated_avoids_ty dag c k hNotUp ptr hSc
    | vecTy elem => exact scoped_unrelated_avoids_ty dag c k hNotUp elem hSc
    | tuple a b =>
      exact ⟨scoped_unrelated_avoids_ty dag c k hNotUp a hSc.1,
             scoped_unrelated_avoids_ty dag c k hNotUp b hSc.2⟩
    | adt id args =>
      dsimp only [TyScopedInCrate] at hSc
      refine ⟨?_, scoped_unrelated_avoids_list dag c k hNotUp args hSc.2⟩
      intro hEq
      rw [hEq] at hSc
      exact hNotUp hSc.1

  private theorem scoped_unrelated_avoids_list (dag : CrateDAG) (c k : CrateId)
      (hNotUp : ¬ UpstreamOf dag k c) (ts : List Ty) (hSc : TyListScopedInCrate dag c ts) :
      TyListAvoidsCrate dag k ts := by
    cases ts with
    | nil => trivial
    | cons t ts =>
      exact ⟨scoped_unrelated_avoids_ty dag c k hNotUp t hSc.1,
             scoped_unrelated_avoids_list dag c k hNotUp ts hSc.2⟩
end

theorem scoped_unrelated_avoids_traitRef (dag : CrateDAG) (c k : CrateId)
    (hNotUp : ¬ UpstreamOf dag k c) (tr : TraitRef) (hSc : TraitRefScopedInCrate dag c tr) :
    TraitRefAvoidsCrate dag k tr := by
  dsimp only [TraitRefScopedInCrate] at hSc
  refine ⟨?_, scoped_unrelated_avoids_ty dag c k hNotUp tr.selfTy hSc.2.1,
             scoped_unrelated_avoids_list dag c k hNotUp tr.traitArgs hSc.2.2⟩
  intro hEq
  rw [hEq] at hSc
  exact hNotUp hSc.1

/- Fundamental-spine owner sequence of a ground type:
collects every nominal ADT owner encountered before hitting a non-fundamental cutoff
(including the first non-fundamental ADT itself, matching `OrphanChecker` stopping at
non-fundamental wrappers like `Vec` or opaque foreign ADTs). -/
mutual
  noncomputable def fundOwners (dag : CrateDAG) (boxMode : BoxMode) : GroundTy → List CrateId
    | .prim _ => []
    | .refShared inner => fundOwners dag boxMode inner
    | .refMut inner => fundOwners dag boxMode inner
    | .boxTy elem alloc =>
      match boxMode with
      | .elemOnly => fundOwners dag boxMode elem
      | .allArgs => fundOwners dag boxMode elem ++ fundOwners dag boxMode alloc
    | .pinTy ptr => fundOwners dag boxMode ptr
    | .vecTy _ => []
    | .tuple _ _ => []
    | .adt id args =>
      match dag.isFundamentalAdt id with
      | true => dag.adtOwner id :: fundOwnersList dag boxMode args
      | false => [dag.adtOwner id]

  noncomputable def fundOwnersList (dag : CrateDAG) (boxMode : BoxMode) :
      List GroundTy → List CrateId
    | [] => []
    | t :: ts => fundOwners dag boxMode t ++ fundOwnersList dag boxMode ts
end

/-- `AppearsBefore a b xs` holds iff crate `a` appears in `xs` strictly before any
occurrence of crate `b`. -/
inductive AppearsBefore (a b : CrateId) : List CrateId → Prop where
  | here {xs : List CrateId} : AppearsBefore a b (a :: xs)
  | skip {x : CrateId} {xs : List CrateId} : x ≠ b → AppearsBefore a b xs → AppearsBefore a b (x :: xs)

private theorem appearsBefore_append_right {a b : CrateId} {xs ys : List CrateId}
    (hx : AppearsBefore a b xs) : AppearsBefore a b (xs ++ ys) := by
  induction hx with
  | here => exact .here
  | skip hne _ ih => exact .skip hne ih

private theorem appearsBefore_append_left {a b : CrateId} {xs ys : List CrateId}
    (hx : NoMem b xs) (hy : AppearsBefore a b ys) : AppearsBefore a b (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons hne _ ih => exact .skip hne ih

private theorem appearsBefore_asymm {a b : CrateId} {xs : List CrateId}
    (hne : a ≠ b) (hab : AppearsBefore a b xs) (hba : AppearsBefore b a xs) : False := by
  induction hab with
  | here =>
    cases hba with
    | here => exact hne rfl
    | skip hne' _ => exact hne' rfl
  | skip hxb _ ih =>
    cases hba with
    | here => exact hxb rfl
    | skip _ hba' => exact ih hba'

mutual
  /-- Key Lemma 1 (Non-Local Prefix Preservation):
  If `visitTy dag boxMode c₁ t = .nonLocalInput` and `t` avoids crate `c₂`, then NO
  substitution `σ` can introduce `c₂` into `fundOwners (instTy σ t)`.
  Notice that `Ty.var` returns `.uncoveredParam` (contradiction), while `Vec` and `tuple`
  cut off traversal at `[]` regardless of any `Ty.var` inside them (RFC 2451!). -/
  private theorem visit_nonLocal_no_foreign_owner
      (dag : CrateDAG) (boxMode : BoxMode) (c₁ c₂ : CrateId) (σ : GroundSubst) (t : Ty)
      (hVis : visitTy dag boxMode c₁ t = .nonLocalInput)
      (hAvoid : TyAvoidsCrate dag c₂ t) :
      NoMem c₂ (fundOwners dag boxMode (instTy σ t)) := by
    cases t with
    | var _ => cases hVis
    | prim _ => exact .nil
    | refShared inner =>
      exact visit_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ inner hVis hAvoid
    | refMut inner =>
      exact visit_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ inner hVis hAvoid
    | boxTy elem alloc =>
      dsimp only [visitTy] at hVis
      dsimp only [instTy, fundOwners]
      cases boxMode with
      | elemOnly =>
        exact visit_nonLocal_no_foreign_owner dag .elemOnly c₁ c₂ σ elem hVis hAvoid.1
      | allArgs =>
        dsimp only [combineOutcome] at hVis
        cases he : visitTy dag .allArgs c₁ elem with
        | localTy => rw [he] at hVis; cases hVis
        | uncoveredParam => rw [he] at hVis; cases hVis
        | nonLocalInput =>
          rw [he] at hVis
          exact noMem_append
            (visit_nonLocal_no_foreign_owner dag .allArgs c₁ c₂ σ elem he hAvoid.1)
            (visit_nonLocal_no_foreign_owner dag .allArgs c₁ c₂ σ alloc hVis hAvoid.2)
    | pinTy ptr =>
      exact visit_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ ptr hVis hAvoid
    | vecTy _ => exact .nil
    | tuple _ _ => exact .nil
    | adt id args =>
      dsimp only [visitTy] at hVis
      dsimp only [instTy, fundOwners]
      cases hEq : Nat.beq (dag.adtOwner id) c₁ with
      | true =>
        rw [hEq] at hVis
        cases hVis
      | false =>
        rw [hEq] at hVis
        cases hFund : dag.isFundamentalAdt id with
        | false =>
          exact .cons hAvoid.1 .nil
        | true =>
          rw [hFund] at hVis
          exact .cons hAvoid.1
            (visitList_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ args hVis hAvoid.2)

  private theorem visitList_nonLocal_no_foreign_owner
      (dag : CrateDAG) (boxMode : BoxMode) (c₁ c₂ : CrateId) (σ : GroundSubst) (ts : List Ty)
      (hVis : visitTyList dag boxMode c₁ ts = .nonLocalInput)
      (hAvoid : TyListAvoidsCrate dag c₂ ts) :
      NoMem c₂ (fundOwnersList dag boxMode (instTyList σ ts)) := by
    cases ts with
    | nil => exact .nil
    | cons t ts =>
      dsimp only [visitTyList, combineOutcome] at hVis
      cases ht : visitTy dag boxMode c₁ t with
      | localTy => rw [ht] at hVis; cases hVis
      | uncoveredParam => rw [ht] at hVis; cases hVis
      | nonLocalInput =>
        rw [ht] at hVis
        exact noMem_append
          (visit_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ t ht hAvoid.1)
          (visitList_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ ts hVis hAvoid.2)
end

mutual
  /-- Key Lemma 2 (Local Fundamental-Leaf Precedence):
  If `visitTy dag boxMode c₁ t = .localTy` and `t` avoids `c₂`, then for EVERY ground
  substitution `σ`, crate `c₁` appears in `fundOwners (instTy σ t)` strictly before any `c₂`. -/
  private theorem visit_localTy_appearsBefore
      (dag : CrateDAG) (boxMode : BoxMode) (c₁ c₂ : CrateId) (σ : GroundSubst) (t : Ty)
      (hVis : visitTy dag boxMode c₁ t = .localTy)
      (hAvoid : TyAvoidsCrate dag c₂ t) :
      AppearsBefore c₁ c₂ (fundOwners dag boxMode (instTy σ t)) := by
    cases t with
    | var _ => cases hVis
    | prim _ => cases hVis
    | refShared inner =>
      exact visit_localTy_appearsBefore dag boxMode c₁ c₂ σ inner hVis hAvoid
    | refMut inner =>
      exact visit_localTy_appearsBefore dag boxMode c₁ c₂ σ inner hVis hAvoid
    | boxTy elem alloc =>
      dsimp only [visitTy] at hVis
      dsimp only [instTy, fundOwners]
      cases boxMode with
      | elemOnly =>
        exact visit_localTy_appearsBefore dag .elemOnly c₁ c₂ σ elem hVis hAvoid.1
      | allArgs =>
        dsimp only [combineOutcome] at hVis
        cases he : visitTy dag .allArgs c₁ elem with
        | localTy =>
          exact appearsBefore_append_right
            (visit_localTy_appearsBefore dag .allArgs c₁ c₂ σ elem he hAvoid.1)
        | uncoveredParam => rw [he] at hVis; cases hVis
        | nonLocalInput =>
          rw [he] at hVis
          exact appearsBefore_append_left
            (visit_nonLocal_no_foreign_owner dag .allArgs c₁ c₂ σ elem he hAvoid.1)
            (visit_localTy_appearsBefore dag .allArgs c₁ c₂ σ alloc hVis hAvoid.2)
    | pinTy ptr =>
      exact visit_localTy_appearsBefore dag boxMode c₁ c₂ σ ptr hVis hAvoid
    | vecTy _ => cases hVis
    | tuple _ _ => cases hVis
    | adt id args =>
      dsimp only [visitTy] at hVis
      dsimp only [instTy, fundOwners]
      cases hEq : Nat.beq (dag.adtOwner id) c₁ with
      | true =>
        have hOwn : dag.adtOwner id = c₁ := nat_beq_true_eq hEq
        cases hFund : dag.isFundamentalAdt id with
        | false =>
          rw [hOwn]
          exact .here
        | true =>
          rw [hOwn]
          exact .here
      | false =>
        rw [hEq] at hVis
        cases hFund : dag.isFundamentalAdt id with
        | false =>
          rw [hFund] at hVis
          cases hVis
        | true =>
          rw [hFund] at hVis
          exact .skip hAvoid.1
            (visitList_localTy_appearsBefore dag boxMode c₁ c₂ σ args hVis hAvoid.2)

  private theorem visitList_localTy_appearsBefore
      (dag : CrateDAG) (boxMode : BoxMode) (c₁ c₂ : CrateId) (σ : GroundSubst) (ts : List Ty)
      (hVis : visitTyList dag boxMode c₁ ts = .localTy)
      (hAvoid : TyListAvoidsCrate dag c₂ ts) :
      AppearsBefore c₁ c₂ (fundOwnersList dag boxMode (instTyList σ ts)) := by
    cases ts with
    | nil => cases hVis
    | cons t ts =>
      dsimp only [visitTyList, combineOutcome] at hVis
      cases ht : visitTy dag boxMode c₁ t with
      | localTy =>
        exact appearsBefore_append_right
          (visit_localTy_appearsBefore dag boxMode c₁ c₂ σ t ht hAvoid.1)
      | uncoveredParam => rw [ht] at hVis; cases hVis
      | nonLocalInput =>
        rw [ht] at hVis
        exact appearsBefore_append_left
          (visit_nonLocal_no_foreign_owner dag boxMode c₁ c₂ σ t ht hAvoid.1)
          (visitList_localTy_appearsBefore dag boxMode c₁ c₂ σ ts hVis hAvoid.2)
end

/-- **Theorem 1A (Cross-Crate Orphan Separation Theorem — Avoidance Form):**
Let `c₁ ≠ c₂` be two crates such that neither impl header names items owned by the other
(`TraitRefAvoidsCrate dag c₂ tr₁` and `TraitRefAvoidsCrate dag c₁ tr₂`). If both impls
pass `orphanCheck`, then NO pair of ground substitutions `(σ₁, σ₂)` can produce identical
ground trait references (`instTraitRef σ₁ tr₁ = instTraitRef σ₂ tr₂`). Holds identically for
both `BoxMode.allArgs` (`14210df0e`) and `BoxMode.elemOnly` (`0259d5e9a`). -/
theorem orphan_check_cross_crate_disjoint
    (dag : CrateDAG) (boxMode : BoxMode)
    (c₁ c₂ : CrateId) (hNe : c₁ ≠ c₂)
    (tr₁ tr₂ : TraitRef)
    (hOrph₁ : OrphanPasses dag boxMode c₁ tr₁)
    (hOrph₂ : OrphanPasses dag boxMode c₂ tr₂)
    (hAvoid₁ : TraitRefAvoidsCrate dag c₂ tr₁)
    (hAvoid₂ : TraitRefAvoidsCrate dag c₁ tr₂)
    (σ₁ σ₂ : GroundSubst)
    (hEq : instTraitRef σ₁ tr₁ = instTraitRef σ₂ tr₂) :
    False := by
  have hTraitEq : tr₁.traitId = tr₂.traitId := congrArg GroundTraitRef.traitId hEq
  have hInputsEq : instTyList σ₁ tr₁.inputs = instTyList σ₂ tr₂.inputs :=
    congrArg GroundTraitRef.inputs hEq
  dsimp only [OrphanPasses, orphanCheck] at hOrph₁ hOrph₂
  cases hOwn₁ : Nat.beq (dag.traitOwner tr₁.traitId) c₁ with
  | true =>
    have hT₁ : dag.traitOwner tr₁.traitId = c₁ := nat_beq_true_eq hOwn₁
    rw [hTraitEq] at hT₁
    exact hAvoid₂.1 hT₁
  | false =>
    rw [hOwn₁] at hOrph₁
    cases hVis₁ : visitTyList dag boxMode c₁ tr₁.inputs with
    | nonLocalInput => rw [hVis₁] at hOrph₁; cases hOrph₁
    | uncoveredParam => rw [hVis₁] at hOrph₁; cases hOrph₁
    | localTy =>
      cases hOwn₂ : Nat.beq (dag.traitOwner tr₂.traitId) c₂ with
      | true =>
        have hT₂ : dag.traitOwner tr₂.traitId = c₂ := nat_beq_true_eq hOwn₂
        rw [← hTraitEq] at hT₂
        exact hAvoid₁.1 hT₂
      | false =>
        rw [hOwn₂] at hOrph₂
        cases hVis₂ : visitTyList dag boxMode c₂ tr₂.inputs with
        | nonLocalInput => rw [hVis₂] at hOrph₂; cases hOrph₂
        | uncoveredParam => rw [hVis₂] at hOrph₂; cases hOrph₂
        | localTy =>
          have hBef₁ : AppearsBefore c₁ c₂ (fundOwnersList dag boxMode (instTyList σ₁ tr₁.inputs)) :=
            visitList_localTy_appearsBefore dag boxMode c₁ c₂ σ₁ tr₁.inputs hVis₁
              ⟨hAvoid₁.2.1, hAvoid₁.2.2⟩
          have hBef₂ : AppearsBefore c₂ c₁ (fundOwnersList dag boxMode (instTyList σ₂ tr₂.inputs)) :=
            visitList_localTy_appearsBefore dag boxMode c₂ c₁ σ₂ tr₂.inputs hVis₂
              ⟨hAvoid₂.2.1, hAvoid₂.2.2⟩
          rw [hInputsEq] at hBef₁
          exact appearsBefore_asymm hNe hBef₁ hBef₂

/-- **Theorem 1B (Crate-DAG Unrelated Crates Separation):**
When two crates `c₁` and `c₂` are unrelated in `CrateDAG` (`UnrelatedCrates dag c₁ c₂`)
and each impl header is well-scoped in its own crate (`TraitRefScopedInCrate`), `orphanCheck`
guarantees zero conflicting ground instances across `c₁` and `c₂`. -/
theorem orphan_dag_unrelated_crates_disjoint
    (dag : CrateDAG) (boxMode : BoxMode)
    (c₁ c₂ : CrateId) (hUnrel : UnrelatedCrates dag c₁ c₂)
    (tr₁ tr₂ : TraitRef)
    (hSc₁ : TraitRefScopedInCrate dag c₁ tr₁)
    (hSc₂ : TraitRefScopedInCrate dag c₂ tr₂)
    (hOrph₁ : OrphanPasses dag boxMode c₁ tr₁)
    (hOrph₂ : OrphanPasses dag boxMode c₂ tr₂)
    (σ₁ σ₂ : GroundSubst)
    (hEq : instTraitRef σ₁ tr₁ = instTraitRef σ₂ tr₂) :
    False := by
  exact orphan_check_cross_crate_disjoint dag boxMode c₁ c₂ hUnrel.1 tr₁ tr₂ hOrph₁ hOrph₂
    (scoped_unrelated_avoids_traitRef dag c₁ c₂ hUnrel.2.2 tr₁ hSc₁)
    (scoped_unrelated_avoids_traitRef dag c₂ c₁ hUnrel.2.1 tr₂ hSc₂)
    σ₁ σ₂ hEq

/-!
## Part 3: Fundamental Unwrapping, Non-Fundamental `E0117`/`E0210` Counterexamples,
and `OwnedBox` Revision Delta (`14210df0e` vs `0259d5e9a`)
-/

/-- Canonical 3-crate DAG used in concrete witnesses:
- Crate `0`: `core`/`alloc` (owns `ForeignWrapper` ADT `0`, `LocalAlloc` trait/types not here)
- Crate `1`: `up` (owns `ForeignTrait` `10` and `ForeignWrapper` `20`)
- Crate `2`: `down` (depends on `0` and `1`; owns `LocalType` `30` and `LocalAlloc` `31`) -/
noncomputable def exampleDag : CrateDAG :=
  { directDeps := fun c => if Nat.beq c 2 then [0, 1] else []
    traitOwner := fun tid => if Nat.beq tid 10 then 1 else 0
    adtOwner := fun aid =>
      if Nat.beq aid 30 then 2
      else if Nat.beq aid 31 then 2
      else if Nat.beq aid 20 then 1
      else 0
    isFundamentalAdt := fun _ => false
    isFundamentalTrait := fun _ => false
    isAutoTrait := fun _ => false
    isMarkerTrait := fun _ => false }

/-- Fundamental-unwrapping soundness witness:
`impl ForeignTrait for Pin<Box<&mut &LocalType>>` passes `orphanCheck` in `down` (`crate 2`)
under both `BoxMode.allArgs` and `BoxMode.elemOnly`. -/
theorem pin_box_mut_shared_ref_local_passes (bm : BoxMode) :
    OrphanPasses exampleDag bm 2
      { traitId := 10
        selfTy := .pinTy (.boxTy (.refMut (.refShared (.adt 30 []))) (.prim 0))
        traitArgs := [] } := by
  cases bm <;> rfl

/-- Non-fundamental `E0117` blocking witness:
`impl ForeignTrait for Vec<LocalType>` fails `orphanCheck` (`nonLocalInput`) because `Vec` is
non-fundamental and stops traversal before inspecting `LocalType`. -/
theorem vec_local_blocked_e0117 (bm : BoxMode) :
    ¬ OrphanPasses exampleDag bm 2
      { traitId := 10
        selfTy := .vecTy (.adt 30 [])
        traitArgs := [] } := by
  intro h
  cases bm <;> cases h

/-- Non-fundamental `E0117` foreign ADT wrapper witness:
`impl ForeignTrait for up::ForeignWrapper<LocalType>` also fails `orphanCheck` (`nonLocalInput`). -/
theorem foreign_wrapper_local_blocked_e0117 (bm : BoxMode) :
    ¬ OrphanPasses exampleDag bm 2
      { traitId := 10
        selfTy := .adt 20 [.adt 30 []]
        traitArgs := [] } := by
  intro h
  cases bm <;> cases h

/-- Counterexample showing WHY `Vec<LocalType>` must be blocked (`E0117`):
Because `alloc` (`crate 0`) owns `Vec`, `impl<T> ForeignTrait for Vec<T>` legitimately passes
`orphanCheck` in `crate 0` (Wait: `Vec<T>` has `Self = Vec<T>` which is owned by `crate 0`,
modeled via `adt 1` owned by `0` with `isFundamentalAdt 1 = false`!), so admitting
`impl ForeignTrait for Vec<LocalType>` in `crate 2` would immediately collide on `Vec<LocalType>`. -/
theorem ce_vec_local_collides_with_alloc_blanket :
    let vecAdtId : AdtId := 1
    let localAdtId : AdtId := 30
    let trAlloc : TraitRef := { traitId := 10, selfTy := .adt vecAdtId [.var 0], traitArgs := [] }
    let trDown : TraitRef := { traitId := 10, selfTy := .adt vecAdtId [.adt localAdtId []], traitArgs := [] }
    let σAlloc : GroundSubst := fun _ => .adt localAdtId []
    let σDown : GroundSubst := fun _ => .prim 0
    OrphanPasses exampleDag .elemOnly 0 trAlloc ∧
    ¬ OrphanPasses exampleDag .elemOnly 2 trDown ∧
    instTraitRef σAlloc trAlloc = instTraitRef σDown trDown := by
  refine ⟨rfl, ?_, rfl⟩
  intro h
  cases h

/-- RFC 2451 covered-parameter admission witness:
`impl<T> ForeignTrait<LocalType> for Vec<T>` passes `orphanCheck` in `crate 2`, because `Vec<T>`
covers `T` (returning `.nonLocalInput`) before traversal reaches `LocalType` in `traitArgs`. -/
theorem rfc2451_vec_t_before_local_arg_passes (bm : BoxMode) :
    OrphanPasses exampleDag bm 2
      { traitId := 10
        selfTy := .vecTy (.var 0)
        traitArgs := [.adt 30 []] } := by
  cases bm <;> rfl

/-- `E0210` uncovered type-parameter rejection witnesses:
Both `impl<T> ForeignTrait<LocalType> for T` and `impl<T> ForeignTrait<LocalType> for Box<T>`
halt with `.uncoveredParam` before reaching `LocalType` (`Box` does NOT cover `T`). -/
theorem uncovered_t_and_box_t_rejected_e0210 (bm : BoxMode) :
    visitTyList exampleDag bm 2 [.var 0, .adt 30 []] = .uncoveredParam ∧
    visitTyList exampleDag bm 2 [.boxTy (.var 0) (.prim 0), .adt 30 []] = .uncoveredParam := by
  cases bm <;> exact ⟨rfl, rfl⟩

/-- Counterexample showing WHY `impl<T> ForeignTrait<LocalA> for T` (`E0210`) must be rejected:
Sibling crate `2` (`LocalA`) implementing `ForeignTrait<LocalA> for T` and sibling crate `3`
(`LocalB`) implementing `ForeignTrait<U> for LocalB` would collide on `ForeignTrait<LocalA> for LocalB`. -/
theorem ce_uncovered_t_collides_with_sibling :
    let localA : AdtId := 30
    let localB : AdtId := 40
    let dag4 : CrateDAG :=
      { exampleDag with
        adtOwner := fun aid =>
          if Nat.beq aid 30 then 2
          else if Nat.beq aid 40 then 3
          else 0 }
    let trA : TraitRef := { traitId := 10, selfTy := .var 0, traitArgs := [.adt localA []] }
    let trB : TraitRef := { traitId := 10, selfTy := .adt localB [], traitArgs := [.var 0] }
    let σA : GroundSubst := fun _ => .adt localB []
    let σB : GroundSubst := fun _ => .adt localA []
    ¬ OrphanPasses dag4 .elemOnly 2 trA ∧
    OrphanPasses dag4 .elemOnly 3 trB ∧
    instTraitRef σA trA = instTraitRef σB trB := by
  refine ⟨?_, rfl, rfl⟩
  intro h
  cases h

/-- Covered parameter *after* local `Self` (`impl<T> ForeignTrait<T> for Box<LocalType>`)
succeeds because traversal returns `.localTy` at `Self` before visiting `traitArgs`. -/
theorem covered_t_after_box_local_passes (bm : BoxMode) :
    OrphanPasses exampleDag bm 2
      { traitId := 10
        selfTy := .boxTy (.adt 30 []) (.prim 0)
        traitArgs := [.var 0] } := by
  cases bm <;> rfl

/-- Exact `rustc 1.98.0-nightly` (`14210df0e`) vs `rust-lang/rust` `main` (`0259d5e9a`)
`OwnedBox` allocator-parameter delta:
`impl ForeignTrait for Box<u32, LocalAlloc>` passes under `BoxMode.allArgs` (`14210df0e`)
but fails `E0117` under `BoxMode.elemOnly` (`0259d5e9a`, `args.type_at(0)`). -/
theorem owned_box_allocator_revision_delta :
    let boxAllocTr : TraitRef :=
      { traitId := 10, selfTy := .boxTy (.prim 1) (.adt 31 []), traitArgs := [] }
    OrphanPasses exampleDag .allArgs 2 boxAllocTr ∧
    ¬ OrphanPasses exampleDag .elemOnly 2 boxAllocTr := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-!
## Part 4: Negative Impls, `OverlapMode` (`Stable` vs `WithNegative`), `trait_ref_is_knowable`,
and Upstream SemVer Monotonicity
-/

/-- Coherence overlap mode (`compiler/rustc_middle/src/traits/specialization_graph.rs`). -/
inductive OverlapMode where
  | stable
  | withNegative
  | strict

noncomputable def OverlapMode.useNegativeImpl : OverlapMode → Bool
  | .stable => false
  | .withNegative => true
  | .strict => true

noncomputable def OverlapMode.useImplicitNegative : OverlapMode → Bool
  | .stable => true
  | .withNegative => true
  | .strict => false

/-- Ground satisfaction predicate `SatTrait` for traits in a compiled crate world:
an explicit `NegImpl` rules out satisfaction (`PosNegConsistent` forbids both `impl Trait for Ty`
and `impl !Trait for Ty` simultaneously — `E0751`). -/
structure TraitWorld where
  dag : CrateDAG
  hasPositiveImpl : TraitId → GroundTy → Prop
  hasExplicitNegImpl : TraitId → GroundTy → Prop
  /-- `E0751` invariant (`NegativePositiveConflict`): no ground type has both a positive
  implementation and an explicit negative implementation of the same trait. -/
  posNegDisjoint : ∀ tid ty, ¬ (hasPositiveImpl tid ty ∧ hasExplicitNegImpl tid ty)

/-- Polarity-aware satisfaction of a single trait bound `tid` at ground type `g`. -/
noncomputable def SatisfiesBound (w : TraitWorld) (tid : TraitId) (g : GroundTy) : Prop :=
  w.hasPositiveImpl tid g

/-- Explicit negative-impl proof obligation (`impl_intersection_has_negative_obligation`):
there exists an explicit `impl !tid for g` in the dependency DAG. -/
noncomputable def ProvesNegative (w : TraitWorld) (tid : TraitId) (g : GroundTy) : Prop :=
  w.hasExplicitNegImpl tid g

/-- A `with_negative_coherence` impl pair on a target trait:
- `impl₁` is a conditional blanket impl `impl<T: reqTrait> Target for T`
- `impl₂` is a specific impl `impl Target for specTy` (or `impl<T> Target for specPat(T)`). -/
structure DisjointPairSpec where
  reqTrait : TraitId
  specPat : Ty

/-- Ground intersection condition: a ground type `g` triggers overlap iff `g` matches
`specPat` AND satisfies `reqTrait` in world `w`. -/
noncomputable def MatchesGround (pat : Ty) (g : GroundTy) : Prop :=
  ∃ σ : GroundSubst, instTy σ pat = g

/-- Soundness of explicit negative-impl mutual exclusion (`OverlapMode.WithNegative` /
`impl_intersection_has_negative_obligation`):
If every ground instance `g` of `pair.specPat` carries an explicit negative impl
`ProvesNegative w pair.reqTrait g`, then NO ground type `g` satisfies both the conditional
blanket impl (`SatisfiesBound w pair.reqTrait g`) and `MatchesGround pair.specPat g`. -/
theorem neg_impl_disjoint_sound
    (w : TraitWorld) (pair : DisjointPairSpec)
    (hNeg : ∀ g : GroundTy, MatchesGround pair.specPat g → ProvesNegative w pair.reqTrait g) :
    ∀ g : GroundTy, ¬ (SatisfiesBound w pair.reqTrait g ∧ MatchesGround pair.specPat g) := by
  intro g ⟨hPos, hMatch⟩
  exact w.posNegDisjoint pair.reqTrait g ⟨hPos, hNeg g hMatch⟩

/-- Valid upstream SemVer extension of a `TraitWorld` (`SemVerExtension w₁ w₂`):
Upstream crates may add new positive or negative impls, preserving existing negative impls
and upholding `E0751` (`posNegDisjoint`) in `w₂`. (An upstream crate CANNOT add `impl T for X`
where `impl !T for X` already existed without breaking `E0751` / major SemVer!) -/
structure SemVerExtension (w₁ w₂ : TraitWorld) : Prop where
  dagEq : w₁.dag = w₂.dag
  negPreserved : ∀ tid g, w₁.hasExplicitNegImpl tid g → w₂.hasExplicitNegImpl tid g

/-- **Theorem 3 (Negative-Impl SemVer Monotonicity Theorem):**
Disjointness justified by an explicit negative impl (`impl !reqTrait for specPat`) remains
invariant across EVERY valid upstream SemVer extension `w₁ ↦ w₂`: upstream cannot retroactively
create an overlap with the downstream conditional blanket impl without violating `E0751`. -/
theorem neg_impl_semver_monotone
    (w₁ w₂ : TraitWorld) (hExt : SemVerExtension w₁ w₂) (pair : DisjointPairSpec)
    (hNeg₁ : ∀ g : GroundTy, MatchesGround pair.specPat g → ProvesNegative w₁ pair.reqTrait g) :
    ∀ g : GroundTy, ¬ (SatisfiesBound w₂ pair.reqTrait g ∧ MatchesGround pair.specPat g) := by
  intro g ⟨hPos₂, hMatch⟩
  have hNeg₂ : w₂.hasExplicitNegImpl pair.reqTrait g :=
    hExt.negPreserved pair.reqTrait g (hNeg₁ g hMatch)
  exact w₂.posNegDisjoint pair.reqTrait g ⟨hPos₂, hNeg₂⟩

/-- Abstract `knowable` judgment for unary trait obligation `T: tid` inside crate `c`
(modeling `compiler/rustc_next_trait_solver/src/coherence.rs::trait_ref_is_knowable`):
- If `tid` is local to `c`, OR `tid` is `#[fundamental]` (like `FnMut`), OR `pat` is anchored
  by a `c`-local nominal type through fundamental constructors (`visitTy ... c pat = .localTy`),
  AND `pat` has no uncovered type parameter at the root (`visitTy ... c pat ≠ .uncoveredParam`,
  so downstream crates cannot instantiate it with their own local type!), then no other
  crate can future-compatibly add `impl tid for pat`. -/
noncomputable def UnaryKnowableInCrate (dag : CrateDAG) (boxMode : BoxMode) (c : CrateId)
    (tid : TraitId) (pat : Ty) : Bool :=
  let noRemoteParam :=
    match visitTy dag boxMode c pat with
    | .uncoveredParam => false
    | _ => true
  let localOrFundTrait := Nat.beq (dag.traitOwner tid) c || dag.isFundamentalTrait tid
  let localOwner :=
    match visitTy dag boxMode c pat with
    | .localTy => true
    | _ => false
  noRemoteParam && (localOrFundTrait || localOwner)

/-- Coherence overlap decision for `impl<T: reqTrait> Target for T` vs `impl Target for pat`
in crate `c` under `mode`:
- Returns `true` (disjoint / admitted) iff EITHER:
  (a) `mode.useNegativeImpl && hasExplicitNeg`, OR
  (b) `mode.useImplicitNegative && noPositiveImpl && UnaryKnowableInCrate`. -/
noncomputable def CoherenceProvesDisjoint
    (dag : CrateDAG) (boxMode : BoxMode) (mode : OverlapMode) (c : CrateId)
    (reqTrait : TraitId) (pat : Ty)
    (hasExplicitNeg : Bool) (noPositiveImpl : Bool) : Bool :=
  (mode.useNegativeImpl && hasExplicitNeg) ||
  (mode.useImplicitNegative && noPositiveImpl && UnaryKnowableInCrate dag boxMode c reqTrait pat)

/-- **Discrimination Theorem (`Stable` vs `WithNegative` across `Local`, `Rc<T>`, `FnMut`):**
1. Local `!Send` (`c02`): `Local` is local to `crate 2`, so `UnaryKnowableInCrate` is `true`;
   admitted even in `OverlapMode.stable`!
2. Foreign `Rc<T>` (`c07` vs `c08`): `Rc` is owned by `crate 0` (non-local, non-fundamental) and
   `Send` is non-fundamental, so `UnaryKnowableInCrate` is `false`; REJECTED under
   `OverlapMode.stable` (upstream conflict `E0119`), ADMITTED under `OverlapMode.withNegative`
   via `alloc`'s explicit `impl !Send for Rc<T>`!
3. Foreign `#[fundamental]` trait `FnMut` on `&str` (`a17` vs `a18`): `&str` (`prim`) is non-local,
   yet `isFundamentalTrait fnMut = true` makes `UnaryKnowableInCrate = true`, admitting
   `impl<F: FnMut> Pattern for F` + `impl Pattern for &str` even in `OverlapMode.stable`, whereas
   a non-fundamental foreign trait (`ForeignBlanketTrait`) fails `E0119`! -/
theorem stable_vs_with_negative_and_fundamental_trait_discrimination :
    let sendTrait : TraitId := 1
    let fnMutTrait : TraitId := 2
    let foreignBlanketTrait : TraitId := 3
    let localTy : Ty := .adt 30 []
    let rcTy : Ty := .adt 5 [.var 0]
    let strRefTy : Ty := .refShared (.prim 9)
    let dagNeg : CrateDAG :=
      { exampleDag with
        traitOwner := fun tid =>
          if Nat.beq tid sendTrait then 0
          else if Nat.beq tid fnMutTrait then 0
          else 1
        isFundamentalTrait := fun tid => Nat.beq tid fnMutTrait }
    -- (1) Local: !Send admitted even under OverlapMode.stable
    CoherenceProvesDisjoint dagNeg .elemOnly .stable 2 sendTrait localTy true true = true ∧
    -- (2a) Foreign Rc<T>: !Send rejected under OverlapMode.stable
    CoherenceProvesDisjoint dagNeg .elemOnly .stable 2 sendTrait rcTy true true = false ∧
    -- (2b) Foreign Rc<T>: !Send admitted under OverlapMode.withNegative
    CoherenceProvesDisjoint dagNeg .elemOnly .withNegative 2 sendTrait rcTy true true = true ∧
    -- (3a) Fundamental trait FnMut on &str admitted under OverlapMode.stable
    CoherenceProvesDisjoint dagNeg .elemOnly .stable 2 fnMutTrait strRefTy false true = true ∧
    -- (3b) Non-fundamental foreign trait on &str rejected under OverlapMode.stable
    CoherenceProvesDisjoint dagNeg .elemOnly .stable 2 foreignBlanketTrait strRefTy false true = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Formal model of `check_negative_auto_trait_impl` (`E0366` / `E0749` / `E0751`):
- Negative impls cannot contain associated items (`E0749`).
- Negative auto-trait impls cannot specialize ADT type parameters (`E0366` — parameters must
  be unique variables, not concrete types like `impl !Send for Wrap<u32>`). -/
inductive NegImplWfErr where
  | ok
  | e0749HasItems
  | e0366SpecializedAutoTrait

noncomputable def checkNegImplWf (isAutoTrait : Bool) (itemCount : Nat) (headerArgsAreDistinctVars : Bool) :
    NegImplWfErr :=
  match itemCount with
  | _ + 1 => .e0749HasItems
  | 0 =>
    if isAutoTrait && boolNot headerArgsAreDistinctVars then
      .e0366SpecializedAutoTrait
    else
      .ok

theorem neg_impl_wf_checks :
    checkNegImplWf true 1 true = .e0749HasItems ∧
    checkNegImplWf true 0 false = .e0366SpecializedAutoTrait ∧
    checkNegImplWf true 0 true = .ok :=
  ⟨rfl, rfl, rfl⟩

/-!
## Part 5: `#[marker]` Item-Free Soundness (`E0714`/`E0715`) & Inherent Impl Overlap (`E0592`)
-/

/-- Associated-item signature declaration on a trait. -/
structure TraitDecl (AssocVal : Type) where
  traitId : TraitId
  isMarker : Bool
  assocItems : List AssocItemId

/-- An impl block for a trait carries an application predicate `applies : GroundTy → Prop`
and an associated-item resolution table `resolve : AssocItemId → Option AssocVal`. -/
structure TraitImplEntry (AssocVal : Type) where
  implId : ImplId
  traitId : TraitId
  applies : GroundTy → Prop
  resolve : AssocItemId → Option AssocVal

/-- Compiler enforcement of `E0714` (`wfcheck::check_trait`) and `E0715`
(`coherence::enforce_empty_impls_for_marker_traits`):
every `#[marker]` trait has `assocItems = []` and every impl for it defines no items. -/
noncomputable def MarkerZeroItemsWf {AssocVal : Type} (td : TraitDecl AssocVal) : Prop :=
  td.isMarker = true → td.assocItems = []

noncomputable def ImplRespectsTraitItems {AssocVal : Type} (td : TraitDecl AssocVal)
    (implEntry : TraitImplEntry AssocVal) : Prop :=
  implEntry.traitId = td.traitId ∧
  ∀ itemId : AssocItemId, implEntry.resolve itemId ≠ none → Mem itemId td.assocItems

/-- Coherent associated-item resolution: whenever two applicable impls exist for the same
ground type `g`, they agree on every associated item declared by the trait (no dispatch
ambiguity). -/
noncomputable def CoherentItemResolution {AssocVal : Type} (td : TraitDecl AssocVal)
    (i₁ i₂ : TraitImplEntry AssocVal) : Prop :=
  ∀ (g : GroundTy) (itemId : AssocItemId),
    Mem itemId td.assocItems →
    i₁.applies g →
    i₂.applies g →
    i₁.resolve itemId = i₂.resolve itemId

/-- **Theorem 4A (`#[marker]` Item-Free Soundness Theorem):**
Because `E0714` (`wfcheck.rs`) and `E0715` (`coherence/mod.rs`) enforce `td.assocItems = []`
for every `#[marker]` trait, overlapping `#[marker]` impls (`impls_are_allowed_to_overlap`
returning `ImplOverlapKind::Permitted { marker: true }`) satisfy `CoherentItemResolution`
for EVERY pair of overlapping impls and EVERY ground type `g` without specialization ordering
or disambiguation. -/
theorem marker_item_free_coherent {AssocVal : Type}
    (td : TraitDecl AssocVal)
    (hMarker : td.isMarker = true)
    (hE0714 : MarkerZeroItemsWf td)
    (i₁ i₂ : TraitImplEntry AssocVal) :
    CoherentItemResolution td i₁ i₂ := by
  intro g itemId hMem _ _
  have hEmpty : td.assocItems = [] := hE0714 hMarker
  rw [hEmpty] at hMem
  cases hMem

/-- Propositional equivalence witness for overlapping `#[marker]` blanket impls:
given `impl<T: Copy> Mark for T` and `impl<T: Clone> Mark for T`, trait satisfaction
`∃ i, i.applies g` is purely boolean/propositional and deterministic regardless of which
candidate is picked. -/
noncomputable def MarkerSat {AssocVal : Type} (impls : List (TraitImplEntry AssocVal))
    (g : GroundTy) : Prop :=
  ∃ i : TraitImplEntry AssocVal, Mem i impls ∧ i.applies g

theorem marker_selection_order_independent {AssocVal : Type}
    (i₁ i₂ : TraitImplEntry AssocVal) (g : GroundTy)
    (h₁ : i₁.applies g) (h₂ : i₂.applies g) :
    MarkerSat [i₁, i₂] g ∧ MarkerSat [i₂, i₁] g :=
  ⟨⟨i₁, .head, h₁⟩, ⟨i₂, .head, h₂⟩⟩

/-- **Counterexample (`ce_marker_with_assoc_item_incoherent`):**
If `E0714`/`E0715` were omitted on a `#[marker]` trait containing `const X: u32` (`itemId = 0`),
overlapping blanket impls (`impl<T: Copy> M for T { const X = 1 }` vs
`impl<T: Clone> M for T { const X = 2 }`) both apply to `u32` yet resolve `X` differently,
violating `CoherentItemResolution`. -/
theorem ce_marker_with_assoc_item_incoherent :
    let td : TraitDecl Nat := { traitId := 99, isMarker := true, assocItems := [0] }
    let iCopy : TraitImplEntry Nat :=
      { implId := 1, traitId := 99, applies := fun g => g = .prim 1, resolve := fun _ => some 1 }
    let iClone : TraitImplEntry Nat :=
      { implId := 2, traitId := 99, applies := fun g => g = .prim 1 ∨ g = .prim 2, resolve := fun _ => some 2 }
    ¬ MarkerZeroItemsWf td ∧ ¬ CoherentItemResolution td iCopy iClone := by
  refine ⟨?_, ?_⟩
  · intro h
    have hEq := h rfl
    cases hEq
  · intro hCoh
    have hRes := hCoh (.prim 1) 0 .head rfl (Or.inl rfl)
    cases hRes

/-- Inherent implementation block on a local nominal ADT (`inherent_impls_overlap.rs`):
`check_for_common_items_in_impls` checks overlapping `selfPat` ONLY when the two inherent
impls share a hygienically equal item identifier (`itemNames`). -/
abbrev ItemNameId := Nat

structure InherentImplEntry where
  adtId : AdtId
  selfPat : Ty
  itemNames : List ItemNameId

/-- Two inherent impls on the same ADT are disjoint (no `E0592`) if either:
1. They define disjoint item names (`NoCommonItem`), OR
2. Their `Self` types have no common ground instance (`∀ σ₁ σ₂, instTy σ₁ i₁.selfPat ≠ instTy σ₂ i₂.selfPat`). -/
noncomputable def InherentNoCollision (i₁ i₂ : InherentImplEntry) : Prop :=
  ∀ (g : GroundTy) (name : ItemNameId),
    ¬ (MatchesGround i₁.selfPat g ∧ Mem name i₁.itemNames ∧
       MatchesGround i₂.selfPat g ∧ Mem name i₂.itemNames)

theorem inherent_disjoint_names_sound (i₁ i₂ : InherentImplEntry)
    (hNames : ∀ n, Mem n i₁.itemNames → NoMem n i₂.itemNames) :
    InherentNoCollision i₁ i₂ := by
  intro g name ⟨_, hm₁, _, hm₂⟩
  exact mem_and_noMem_false hm₂ (hNames name hm₁)

theorem inherent_disjoint_self_types_sound (i₁ i₂ : InherentImplEntry)
    (hDisj : ∀ σ₁ σ₂, instTy σ₁ i₁.selfPat ≠ instTy σ₂ i₂.selfPat) :
    InherentNoCollision i₁ i₂ := by
  intro g name ⟨⟨σ₁, h₁⟩, _, ⟨σ₂, h₂⟩, _⟩
  exact hDisj σ₁ σ₂ (h₁.trans h₂.symm)

/-- Concrete witness of disjoint inherent impls (`impl Wrap<u32> { fn get }` vs
`impl Wrap<i32> { fn get }`) passing `inherent_impls_overlap.rs` without `E0592`. -/
theorem inherent_u32_vs_i32_disjoint :
    let i₁ : InherentImplEntry := { adtId := 30, selfPat := .adt 30 [.prim 1], itemNames := [1] }
    let i₂ : InherentImplEntry := { adtId := 30, selfPat := .adt 30 [.prim 2], itemNames := [1] }
    InherentNoCollision i₁ i₂ := by
  apply inherent_disjoint_self_types_sound
  intro σ₁ σ₂ h
  cases h

/-!
## Part 6: Real `zerocopy` Coherence Patterns (`TryTransmuteFromPtr`, `MutationCompatible`,
`SharedCompatible`, `Read<A, R>`)
-/

/-- Phantom reason-marker types used by `google/zerocopy` (`zerocopy/src/pointer/transmute.rs`,
`zerocopy/src/pointer/invariant.rs`) to partition overlapping generic blanket impls on stable Rust
without `#[marker]` or specialization. -/
inductive ZcReason where
  | becauseImmutable
  | becauseExclusive
  | becauseRead (inner : ZcReason)
  | becauseSharedCompatible
  | becauseMutationCompatible (inner : ZcReason)
  | var (v : TyVar)

/-- Ground reason marker after instantiating `R`. -/
inductive GroundZcReason where
  | becauseImmutable
  | becauseExclusive
  | becauseRead (inner : GroundZcReason)
  | becauseSharedCompatible
  | becauseMutationCompatible (inner : GroundZcReason)

noncomputable def instZcReason (σ : TyVar → GroundZcReason) : ZcReason → GroundZcReason
  | .becauseImmutable => .becauseImmutable
  | .becauseExclusive => .becauseExclusive
  | .becauseRead r => .becauseRead (instZcReason σ r)
  | .becauseSharedCompatible => .becauseSharedCompatible
  | .becauseMutationCompatible r => .becauseMutationCompatible (instZcReason σ r)
  | .var v => σ v

/-- `zerocopy` referent type patterns (`T`, `ManuallyDrop<T>`, `Unalign<T>`, `Wrapping<T>`). -/
inductive ZcTy where
  | prim (p : Nat)
  | var (v : TyVar)
  | manuallyDrop (inner : ZcTy)
  | unalign (inner : ZcTy)
  | wrapping (inner : ZcTy)
  | pair (fst snd : ZcTy)

inductive GroundZcTy where
  | prim (p : Nat)
  | manuallyDrop (inner : GroundZcTy)
  | unalign (inner : GroundZcTy)
  | wrapping (inner : GroundZcTy)
  | pair (fst snd : GroundZcTy)

/-- Structural AST size of `GroundZcTy` (`+ 1` on right so every constructor adds `Nat.succ`). -/
noncomputable def groundZcTySize : GroundZcTy → Nat
  | .prim _ => 1
  | .manuallyDrop t => groundZcTySize t + 1
  | .unalign t => groundZcTySize t + 1
  | .wrapping t => groundZcTySize t + 1
  | .pair a b => groundZcTySize a + groundZcTySize b + 1

noncomputable def instZcTy (σ : TyVar → GroundZcTy) : ZcTy → GroundZcTy
  | .prim p => .prim p
  | .var v => σ v
  | .manuallyDrop t => .manuallyDrop (instZcTy σ t)
  | .unalign t => .unalign (instZcTy σ t)
  | .wrapping t => .wrapping (instZcTy σ t)
  | .pair a b => .pair (instZcTy σ a) (instZcTy σ b)

/-- **Theorem 5A (`zerocopy` Phantom Reason-Marker Disjointness):**
1. `Read<A, BecauseImmutable>` and `Read<Exclusive, BecauseExclusive>` have disjoint reason
   headers (`BecauseImmutable ≠ BecauseExclusive`).
2. `MutationCompatible<..., (BecauseRead, R)>` and `MutationCompatible<..., BecauseSharedCompatible>`
   have disjoint reason headers for ALL `R`.
3. `TryTransmuteFromPtr<..., (BecauseMutationCompatible, R)>` and
   `TryTransmuteFromPtr<..., BecauseImmutable>` have disjoint reason headers for ALL `R`. -/
theorem zc_reason_marker_disjointness (σ₁ σ₂ : TyVar → GroundZcReason) :
    instZcReason σ₁ .becauseImmutable ≠ instZcReason σ₂ .becauseExclusive ∧
    instZcReason σ₁ (.becauseRead (.var 0)) ≠ instZcReason σ₂ .becauseSharedCompatible ∧
    instZcReason σ₁ (.becauseMutationCompatible (.var 0)) ≠ instZcReason σ₂ .becauseImmutable := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- **Theorem 5B (`zerocopy` `SharedCompatible` Occurs-Check Non-Overlap):**
The three `SharedCompatible` blanket impls (`transmute.rs:219,258,260`):
- `I₀`: `impl<T> SharedCompatible<T> for T` (`(T, T)`)
- `I₁`: `impl<T> SharedCompatible<T> for ManuallyDrop<T>` (`(T, ManuallyDrop<T>)`)
- `I₂`: `impl<T> SharedCompatible<ManuallyDrop<T>> for T` (`(ManuallyDrop<T>, T)`)
are pairwise disjoint across ALL ground instantiations `(σ₁, σ₂)`.
Proof uses structural size (`nat_succ_ne_self`), matching `rustc`'s occurs check! -/
theorem zc_shared_compatible_occurs_check_disjoint (σ₁ σ₂ : TyVar → GroundZcTy) :
    (instZcTy σ₁ (.var 0), instZcTy σ₁ (.var 0)) ≠
      (instZcTy σ₂ (.var 0), instZcTy σ₂ (.manuallyDrop (.var 0))) ∧
    (instZcTy σ₁ (.var 0), instZcTy σ₁ (.var 0)) ≠
      (instZcTy σ₂ (.manuallyDrop (.var 0)), instZcTy σ₂ (.var 0)) ∧
    (instZcTy σ₁ (.var 0), instZcTy σ₁ (.manuallyDrop (.var 0))) ≠
      (instZcTy σ₂ (.manuallyDrop (.var 0)), instZcTy σ₂ (.var 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    injection h with hL hR
    dsimp only [instZcTy] at hL hR
    have hEq : σ₂ 0 = .manuallyDrop (σ₂ 0) := hL.symm.trans hR
    have hSize : groundZcTySize (σ₂ 0) = groundZcTySize (σ₂ 0) + 1 :=
      congrArg groundZcTySize hEq
    exact nat_succ_ne_self (groundZcTySize (σ₂ 0)) hSize.symm
  · intro h
    injection h with hL hR
    dsimp only [instZcTy] at hL hR
    have hEq : .manuallyDrop (σ₂ 0) = σ₂ 0 := hL.symm.trans hR
    have hSize : groundZcTySize (σ₂ 0) + 1 = groundZcTySize (σ₂ 0) :=
      congrArg groundZcTySize hEq
    exact nat_succ_ne_self (groundZcTySize (σ₂ 0)) hSize
  · intro h
    injection h with hL hR
    dsimp only [instZcTy] at hL hR
    have hSub : GroundZcTy.manuallyDrop (GroundZcTy.manuallyDrop (σ₂ 0)) = σ₂ 0 := by
      rw [← hL]
      exact hR
    have hSize : groundZcTySize (σ₂ 0) + 1 + 1 = groundZcTySize (σ₂ 0) :=
      congrArg groundZcTySize hSub
    have hNe : ∀ k : Nat, k + 1 + 1 ≠ k := by
      intro k hk
      induction k with
      | zero => cases hk
      | succ m ih =>
        injection hk with hk'
        exact ih hk'
    exact hNe (groundZcTySize (σ₂ 0)) hSize

/-- Symmetric `Unalign<T>` / `Wrapping<T>` occurs-check disjointness (`transmute.rs:411,444`):
no ground pair satisfies both `SharedCompatible<T> for Unalign<T>` and
`SharedCompatible<T> for Wrapping<T>` or `SharedCompatible<T> for T`. -/
theorem zc_unalign_wrapping_shared_compatible_disjoint (σ₁ σ₂ : TyVar → GroundZcTy) :
    (instZcTy σ₁ (.var 0), instZcTy σ₁ (.unalign (.var 0))) ≠
      (instZcTy σ₂ (.var 0), instZcTy σ₂ (.wrapping (.var 0))) ∧
    (instZcTy σ₁ (.var 0), instZcTy σ₁ (.var 0)) ≠
      (instZcTy σ₂ (.var 0), instZcTy σ₂ (.unalign (.var 0))) ∧
    (instZcTy σ₁ (.var 0), instZcTy σ₁ (.var 0)) ≠
      (instZcTy σ₂ (.var 0), instZcTy σ₂ (.wrapping (.var 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    injection h with hL hR
    dsimp only [instZcTy] at hL hR
    rw [hL] at hR
    cases hR
  · intro h
    injection h with hL hR
    dsimp only [instZcTy] at hL hR
    have hEq : σ₂ 0 = .unalign (σ₂ 0) := hL.symm.trans hR
    exact nat_succ_ne_self (groundZcTySize (σ₂ 0)) (congrArg groundZcTySize hEq).symm
  · intro h
    injection h with hL hR
    dsimp only [instZcTy] at hL hR
    have hEq : σ₂ 0 = .wrapping (σ₂ 0) := hL.symm.trans hR
    exact nat_succ_ne_self (groundZcTySize (σ₂ 0)) (congrArg groundZcTySize hEq).symm

/-- **Counterexample (`ce_zc_without_reason_marker_overlaps`):**
If `MutationCompatible<Src, A, SV, DV, R>` dropped its phantom reason parameter `R`
(retaining only `(Src, Dst, A, SV, DV)`), the two blanket impls (`Read` vs `SharedCompatible`)
would immediately unify on `(u32, u32, Shared, Safe, Safe)`, triggering `E0119`. -/
theorem ce_zc_without_reason_marker_overlaps :
    ∃ (σ₁ σ₂ : TyVar → GroundZcTy),
      (instZcTy σ₁ (.var 0), instZcTy σ₁ (.var 1)) =
      (instZcTy σ₂ (.var 0), instZcTy σ₂ (.var 1)) := by
  exact ⟨fun _ => .prim 1, fun _ => .prim 1, rfl⟩

/-!
## Part 7: End-to-End Coherence Composition & Multi-Crate Link-Safety Synthesis
-/

/-- Unified trait-system coherence certificate for a crate `c` inside a `TraitWorld`:
combines (1) `orphanCheck` across all foreign-trait impls, (2) same-crate overlap rejection
except item-free `#[marker]` traits (`E0714`/`E0715`) or negative-impl disjointness (`OverlapMode`),
and (3) `InherentNoCollision` across local nominal ADTs. -/
structure CrateCoherenceCert (AssocVal : Type) where
  world : TraitWorld
  boxMode : BoxMode
  overlapMode : OverlapMode
  crateId : CrateId
  traitDecls : List (TraitDecl AssocVal)
  traitImpls : List (TraitImplEntry AssocVal)
  inherentImpls : List InherentImplEntry

/-- Ground ambiguity absence for non-marker traits vs vacuous item-agreement for marker traits. -/
noncomputable def NonMarkerUnique {AssocVal : Type} (td : TraitDecl AssocVal)
    (i₁ i₂ : TraitImplEntry AssocVal) : Prop :=
  td.isMarker = false →
  i₁.implId ≠ i₂.implId →
  ∀ g : GroundTy, ¬ (i₁.applies g ∧ i₂.applies g)

/-- **Master Coherence Safety Theorem (`crate_coherence_all_items_deterministic`):**
Given two crates `c₁ ≠ c₂` unrelated in `CrateDAG` whose trait impl headers pass `orphanCheck`
with disjoint cross-crate scopes (`TraitRefAvoidsCrate`), AND whose intra-crate non-marker impls
are mutually exclusive (either structurally or via `NegImpl` disjointness) while overlapping
`#[marker]` impls obey `E0714`/`E0715` (`MarkerZeroItemsWf`):
1. No ground foreign-trait instance can be simultaneously implemented by `c₁` and `c₂`.
2. Every trait impl pair within either crate either has disjoint applicability on ground types OR
   targets an item-free `#[marker]` trait with `CoherentItemResolution`. -/
theorem master_coherence_safety {AssocVal : Type}
    (dag : CrateDAG) (boxMode : BoxMode) (c₁ c₂ : CrateId)
    (hUnrel : UnrelatedCrates dag c₁ c₂)
    (tr₁ tr₂ : TraitRef)
    (hSc₁ : TraitRefScopedInCrate dag c₁ tr₁)
    (hSc₂ : TraitRefScopedInCrate dag c₂ tr₂)
    (hOrph₁ : OrphanPasses dag boxMode c₁ tr₁)
    (hOrph₂ : OrphanPasses dag boxMode c₂ tr₂)
    (td : TraitDecl AssocVal)
    (hE0714 : MarkerZeroItemsWf td)
    (i₁ i₂ : TraitImplEntry AssocVal)
    (hNonMarker : NonMarkerUnique td i₁ i₂)
    (hNeImpl : i₁.implId ≠ i₂.implId) :
    (∀ σ₁ σ₂ : GroundSubst, instTraitRef σ₁ tr₁ ≠ instTraitRef σ₂ tr₂) ∧
    (∀ g : GroundTy, i₁.applies g → i₂.applies g →
      ∀ itemId : AssocItemId, Mem itemId td.assocItems → i₁.resolve itemId = i₂.resolve itemId) := by
  refine ⟨?_, ?_⟩
  · intro σ₁ σ₂ hEq
    exact orphan_dag_unrelated_crates_disjoint dag boxMode c₁ c₂ hUnrel tr₁ tr₂ hSc₁ hSc₂ hOrph₁ hOrph₂ σ₁ σ₂ hEq
  · intro g ha₁ ha₂ itemId hMem
    cases hM : td.isMarker with
    | true =>
      exact marker_item_free_coherent td hM hE0714 i₁ i₂ g itemId hMem ha₁ ha₂
    | false =>
      exact False.elim (hNonMarker hM hNeImpl g ⟨ha₁, ha₂⟩)

/- Explicit structural equality on `GroundTy` (marked `noncomputable` so zero `._unsafe_rec`
helpers are emitted by Lean's compiler). -/
mutual
  noncomputable def GroundTy.beq : GroundTy → GroundTy → Bool
    | .prim a, .prim b => Nat.beq a b
    | .refShared a, .refShared b => GroundTy.beq a b
    | .refMut a, .refMut b => GroundTy.beq a b
    | .boxTy e₁ a₁, .boxTy e₂ a₂ => GroundTy.beq e₁ e₂ && GroundTy.beq a₁ a₂
    | .pinTy a, .pinTy b => GroundTy.beq a b
    | .vecTy a, .vecTy b => GroundTy.beq a b
    | .tuple a₁ b₁, .tuple a₂ b₂ => GroundTy.beq a₁ a₂ && GroundTy.beq b₁ b₂
    | .adt id₁ args₁, .adt id₂ args₂ => Nat.beq id₁ id₂ && groundTyListBeq args₁ args₂
    | _, _ => false

  noncomputable def groundTyListBeq : List GroundTy → List GroundTy → Bool
    | [], [] => true
    | x :: xs, y :: ys => GroundTy.beq x y && groundTyListBeq xs ys
    | _, _ => false
end

mutual
  private theorem groundTy_beq_refl (g : GroundTy) : GroundTy.beq g g = true := by
    cases g with
    | prim p => exact nat_beq_refl p
    | refShared t => exact groundTy_beq_refl t
    | refMut t => exact groundTy_beq_refl t
    | boxTy e a =>
      dsimp only [GroundTy.beq]
      rw [groundTy_beq_refl e, groundTy_beq_refl a]
      rfl
    | pinTy p => exact groundTy_beq_refl p
    | vecTy e => exact groundTy_beq_refl e
    | tuple a b =>
      dsimp only [GroundTy.beq]
      rw [groundTy_beq_refl a, groundTy_beq_refl b]
      rfl
    | adt id args =>
      dsimp only [GroundTy.beq]
      rw [nat_beq_refl id, groundTyList_beq_refl args]
      rfl

  private theorem groundTyList_beq_refl (gs : List GroundTy) : groundTyListBeq gs gs = true := by
    cases gs with
    | nil => rfl
    | cons g gs =>
      dsimp only [groundTyListBeq]
      rw [groundTy_beq_refl g, groundTyList_beq_refl gs]
      rfl
end

private theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

mutual
  private theorem groundTy_beq_eq :
      ∀ {g₁ g₂ : GroundTy}, GroundTy.beq g₁ g₂ = true → g₁ = g₂
    | .prim a, .prim b, h => by rw [nat_beq_true_eq h]
    | .refShared a, .refShared b, h => by
      dsimp only [GroundTy.beq] at h
      rw [@groundTy_beq_eq a b h]
    | .refMut a, .refMut b, h => by
      dsimp only [GroundTy.beq] at h
      rw [@groundTy_beq_eq a b h]
    | .boxTy e₁ a₁, .boxTy e₂ a₂, h => by
      dsimp only [GroundTy.beq] at h
      have ⟨he, ha⟩ := bool_and_true h
      rw [@groundTy_beq_eq e₁ e₂ he, @groundTy_beq_eq a₁ a₂ ha]
    | .pinTy a, .pinTy b, h => by
      dsimp only [GroundTy.beq] at h
      rw [@groundTy_beq_eq a b h]
    | .vecTy a, .vecTy b, h => by
      dsimp only [GroundTy.beq] at h
      rw [@groundTy_beq_eq a b h]
    | .tuple a₁ b₁, .tuple a₂ b₂, h => by
      dsimp only [GroundTy.beq] at h
      have ⟨ha, hb⟩ := bool_and_true h
      rw [@groundTy_beq_eq a₁ a₂ ha, @groundTy_beq_eq b₁ b₂ hb]
    | .adt id₁ args₁, .adt id₂ args₂, h => by
      dsimp only [GroundTy.beq] at h
      have ⟨hid, hargs⟩ := bool_and_true h
      rw [nat_beq_true_eq hid, @groundTyList_beq_eq args₁ args₂ hargs]
    | .prim _, .refShared _, h => by cases h
    | .prim _, .refMut _, h => by cases h
    | .prim _, .boxTy _ _, h => by cases h
    | .prim _, .pinTy _, h => by cases h
    | .prim _, .vecTy _, h => by cases h
    | .prim _, .tuple _ _, h => by cases h
    | .prim _, .adt _ _, h => by cases h
    | .refShared _, .prim _, h => by cases h
    | .refShared _, .refMut _, h => by cases h
    | .refShared _, .boxTy _ _, h => by cases h
    | .refShared _, .pinTy _, h => by cases h
    | .refShared _, .vecTy _, h => by cases h
    | .refShared _, .tuple _ _, h => by cases h
    | .refShared _, .adt _ _, h => by cases h
    | .refMut _, .prim _, h => by cases h
    | .refMut _, .refShared _, h => by cases h
    | .refMut _, .boxTy _ _, h => by cases h
    | .refMut _, .pinTy _, h => by cases h
    | .refMut _, .vecTy _, h => by cases h
    | .refMut _, .tuple _ _, h => by cases h
    | .refMut _, .adt _ _, h => by cases h
    | .boxTy _ _, .prim _, h => by cases h
    | .boxTy _ _, .refShared _, h => by cases h
    | .boxTy _ _, .refMut _, h => by cases h
    | .boxTy _ _, .pinTy _, h => by cases h
    | .boxTy _ _, .vecTy _, h => by cases h
    | .boxTy _ _, .tuple _ _, h => by cases h
    | .boxTy _ _, .adt _ _, h => by cases h
    | .pinTy _, .prim _, h => by cases h
    | .pinTy _, .refShared _, h => by cases h
    | .pinTy _, .refMut _, h => by cases h
    | .pinTy _, .boxTy _ _, h => by cases h
    | .pinTy _, .vecTy _, h => by cases h
    | .pinTy _, .tuple _ _, h => by cases h
    | .pinTy _, .adt _ _, h => by cases h
    | .vecTy _, .prim _, h => by cases h
    | .vecTy _, .refShared _, h => by cases h
    | .vecTy _, .refMut _, h => by cases h
    | .vecTy _, .boxTy _ _, h => by cases h
    | .vecTy _, .pinTy _, h => by cases h
    | .vecTy _, .tuple _ _, h => by cases h
    | .vecTy _, .adt _ _, h => by cases h
    | .tuple _ _, .prim _, h => by cases h
    | .tuple _ _, .refShared _, h => by cases h
    | .tuple _ _, .refMut _, h => by cases h
    | .tuple _ _, .boxTy _ _, h => by cases h
    | .tuple _ _, .pinTy _, h => by cases h
    | .tuple _ _, .vecTy _, h => by cases h
    | .tuple _ _, .adt _ _, h => by cases h
    | .adt _ _, .prim _, h => by cases h
    | .adt _ _, .refShared _, h => by cases h
    | .adt _ _, .refMut _, h => by cases h
    | .adt _ _, .boxTy _ _, h => by cases h
    | .adt _ _, .pinTy _, h => by cases h
    | .adt _ _, .vecTy _, h => by cases h
    | .adt _ _, .tuple _ _, h => by cases h
  termination_by g₁ _ _ => sizeOf g₁

  private theorem groundTyList_beq_eq :
      ∀ {gs₁ gs₂ : List GroundTy}, groundTyListBeq gs₁ gs₂ = true → gs₁ = gs₂
    | [], [], _ => rfl
    | _ :: _, [], h => by cases h
    | [], _ :: _, h => by cases h
    | x :: xs, y :: ys, h => by
      dsimp only [groundTyListBeq] at h
      have ⟨hx, hxs⟩ := bool_and_true h
      rw [@groundTy_beq_eq x y hx, @groundTyList_beq_eq xs ys hxs]
  termination_by gs₁ _ _ => sizeOf gs₁
end

/-- Concrete `TraitWorld` witnessing `with_negative_coherence` disjointness for `Rc<T>` vs `Send`,
and its preservation under a concrete upstream `SemVerExtension` adding `impl Send for NewUpStruct`. -/
noncomputable def concreteRcWorldV1 : TraitWorld :=
  { dag := exampleDag
    hasPositiveImpl := fun tid g =>
      Nat.beq tid 1 = true ∧ GroundTy.beq g (.prim 1) = true
    hasExplicitNegImpl := fun tid g =>
      Nat.beq tid 1 = true ∧ ∃ elem : GroundTy, g = .adt 5 [elem]
    posNegDisjoint := by
      intro tid g ⟨⟨_, hPrim⟩, ⟨_, elem, hRc⟩⟩
      rw [hRc] at hPrim
      cases hPrim }

noncomputable def concreteRcWorldV2 : TraitWorld :=
  { dag := exampleDag
    hasPositiveImpl := fun tid g =>
      Nat.beq tid 1 = true ∧ (GroundTy.beq g (.prim 1) = true ∨ GroundTy.beq g (.prim 2) = true)
    hasExplicitNegImpl := fun tid g =>
      Nat.beq tid 1 = true ∧ ∃ elem : GroundTy, g = .adt 5 [elem]
    posNegDisjoint := by
      intro tid g ⟨⟨_, hPrim⟩, ⟨_, elem, hRc⟩⟩
      rw [hRc] at hPrim
      cases hPrim with
      | inl h => cases h
      | inr h => cases h }

theorem concrete_rc_semver_extension_valid :
    SemVerExtension concreteRcWorldV1 concreteRcWorldV2 :=
  { dagEq := rfl
    negPreserved := fun _ _ h => h }

theorem concrete_rc_disjoint_across_semver :
    let rcDisjointPair : DisjointPairSpec := { reqTrait := 1, specPat := .adt 5 [.var 0] }
    ∀ g : GroundTy,
      ¬ (SatisfiesBound concreteRcWorldV2 rcDisjointPair.reqTrait g ∧
         MatchesGround rcDisjointPair.specPat g) := by
  apply neg_impl_semver_monotone concreteRcWorldV1 concreteRcWorldV2 concrete_rc_semver_extension_valid
  intro g ⟨σ, hEq⟩
  refine ⟨rfl, σ 0, ?_⟩
  exact hEq.symm

/-!
## Part 8: Built-in Coherence Guards (`Drop`, `Copy`, `dyn Trait` Object Overlap `E0371`,
and Foreign Auto-Trait `E0321`)
-/

/-- Formal model of `coherence/builtin.rs` (`visit_implementation_of_drop`,
`visit_implementation_of_copy`), `coherence/mod.rs` (`check_object_overlap`, `E0371`),
and `coherence/orphan.rs` (`NonlocalImpl`, `E0321`). -/
inductive BuiltinCoherenceOutcome where
  | admitted
  | e0120DropOnNonLocalAdt
  | e0206CopyOnNonAdt
  | e0371ObjectSupertraitOverlap
  | e0321AutoTraitNonLocalNominal

/-- `Drop` and `Copy` built-in coherence checks (`coherence/builtin.rs` L62-131):
`Drop` requires `Self` to be a local ADT; `Copy` requires `Self` to be an ADT (and no `Drop`). -/
noncomputable def checkBuiltinDropOrCopy (dag : CrateDAG) (c : CrateId) (isDrop : Bool)
    (selfTy : Ty) : BuiltinCoherenceOutcome :=
  match selfTy with
  | .adt id _ =>
    if isDrop then
      if Nat.beq (dag.adtOwner id) c then .admitted else .e0120DropOnNonLocalAdt
    else
      .admitted
  | _ =>
    if isDrop then .e0120DropOnNonLocalAdt else .e0206CopyOnNonAdt

/-- Foreign auto-trait orphan check (`coherence/orphan.rs` L99-288, `E0321`):
unlike ordinary traits, foreign auto traits do NOT unwrap `#[fundamental]` wrappers (`Box`, `&`,
`Pin`) and require `Self` to be directly a `c`-local nominal ADT! -/
noncomputable def checkAutoTraitOrphan (dag : CrateDAG) (c : CrateId) (traitId : TraitId)
    (selfTy : Ty) : BuiltinCoherenceOutcome :=
  if Nat.beq (dag.traitOwner traitId) c then
    .admitted
  else
    match selfTy with
    | .adt id _ =>
      if Nat.beq (dag.adtOwner id) c then .admitted else .e0321AutoTraitNonLocalNominal
    | _ => .e0321AutoTraitNonLocalNominal

/-- `check_object_overlap` (`coherence/mod.rs` L192-248, `E0371`):
implementing a supertrait `Sup` directly for `dyn Sub` where `Sup` is a supertrait of `Sub`
collides with the compiler-synthesized object implementation. -/
noncomputable def checkObjectOverlap (isSupertrait : TraitId → TraitId → Bool)
    (implTrait principalTrait : TraitId) : BuiltinCoherenceOutcome :=
  if isSupertrait implTrait principalTrait then .e0371ObjectSupertraitOverlap else .admitted

theorem builtin_coherence_witnesses :
    -- `Box<Local>` passes general orphan check (`a02`), yet fails `E0321` for foreign `Send` (`a16`)
    OrphanPasses exampleDag .elemOnly 2 { traitId := 10, selfTy := .boxTy (.adt 30 []) (.prim 0), traitArgs := [] } ∧
    checkAutoTraitOrphan exampleDag 2 10 (.boxTy (.adt 30 []) (.prim 0)) = .e0321AutoTraitNonLocalNominal ∧
    -- `Drop` on foreign wrapper or `&mut Local` fails; `Drop` on `Local` succeeds
    checkBuiltinDropOrCopy exampleDag 2 true (.adt 30 []) = .admitted ∧
    checkBuiltinDropOrCopy exampleDag 2 true (.boxTy (.adt 30 []) (.prim 0)) = .e0120DropOnNonLocalAdt ∧
    -- `Copy` on `&mut Local` (non-ADT) fails `E0206`
    checkBuiltinDropOrCopy exampleDag 2 false (.refMut (.adt 30 [])) = .e0206CopyOnNonAdt ∧
    -- `impl Sup for dyn Sub` triggers `E0371`
    checkObjectOverlap (fun s p => Nat.beq s 1 && Nat.beq p 2) 1 2 = .e0371ObjectSupertraitOverlap := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-!
## Part 9: Constructive Verification of `TraitRef` & Uncovered-Param Deciders
-/

/- Explicit structural equality on `Ty` (`noncomputable` to keep 0 `._unsafe_rec`). -/
mutual
  noncomputable def Ty.beq : Ty → Ty → Bool
    | .var a, .var b => Nat.beq a b
    | .prim a, .prim b => Nat.beq a b
    | .refShared a, .refShared b => Ty.beq a b
    | .refMut a, .refMut b => Ty.beq a b
    | .boxTy e₁ a₁, .boxTy e₂ a₂ => Ty.beq e₁ e₂ && Ty.beq a₁ a₂
    | .pinTy a, .pinTy b => Ty.beq a b
    | .vecTy a, .vecTy b => Ty.beq a b
    | .tuple a₁ b₁, .tuple a₂ b₂ => Ty.beq a₁ a₂ && Ty.beq b₁ b₂
    | .adt id₁ args₁, .adt id₂ args₂ => Nat.beq id₁ id₂ && tyListBeq args₁ args₂
    | _, _ => false

  noncomputable def tyListBeq : List Ty → List Ty → Bool
    | [], [] => true
    | x :: xs, y :: ys => Ty.beq x y && tyListBeq xs ys
    | _, _ => false
end

/-- `GroundTy.beq` soundness + reflexivity check on `Box<Local>` and `Vec<Local>`. -/
theorem groundTy_beq_decides_distinct_wrappers :
    GroundTy.beq (.boxTy (.adt 30 []) (.prim 0)) (.boxTy (.adt 30 []) (.prim 0)) = true ∧
    GroundTy.beq (.boxTy (.adt 30 []) (.prim 0)) (.vecTy (.adt 30 [])) = false :=
  ⟨rfl, rfl⟩

/-- `Ty.beq` check on `TraitRef` input ordering (`[Self, T1]` vs `[T1, Self]`). -/
theorem traitRef_input_order_matters :
    let trPass : TraitRef := { traitId := 10, selfTy := .vecTy (.var 0), traitArgs := [.adt 30 []] }
    let trFail : TraitRef := { traitId := 10, selfTy := .var 0, traitArgs := [.adt 30 []] }
    OrphanPasses exampleDag .elemOnly 2 trPass ∧
    ¬ OrphanPasses exampleDag .elemOnly 2 trFail := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-- Tuple cutoff witness (`a19`): `(LocalType, u32)` returns `.nonLocalInput`, failing `E0117`
because `OrphanChecker` treats `ty::Tuple(..)` as an opaque non-local cutoff rather than
descending into tuple fields. -/
theorem tuple_with_local_field_blocked_e0117 (bm : BoxMode) :
    ¬ OrphanPasses exampleDag bm 2
      { traitId := 10
        selfTy := .tuple (.adt 30 []) (.prim 1)
        traitArgs := [] } := by
  intro h
  cases bm <;> cases h

/- Verify `instTy` preserves ground types (`instTy σ (GroundTy.toTy g) = g`). -/
mutual
  theorem instTy_ground_roundtrip (σ : GroundSubst) (g : GroundTy) :
      instTy σ (GroundTy.toTy g) = g := by
    cases g with
    | prim _ => rfl
    | refShared t =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTy_ground_roundtrip σ t]
    | refMut t =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTy_ground_roundtrip σ t]
    | boxTy e a =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTy_ground_roundtrip σ e, instTy_ground_roundtrip σ a]
    | pinTy p =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTy_ground_roundtrip σ p]
    | vecTy e =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTy_ground_roundtrip σ e]
    | tuple a b =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTy_ground_roundtrip σ a, instTy_ground_roundtrip σ b]
    | adt id args =>
      dsimp only [GroundTy.toTy, instTy]
      rw [instTyList_ground_roundtrip σ args]

  theorem instTyList_ground_roundtrip (σ : GroundSubst) (gs : List GroundTy) :
      instTyList σ (groundTyListToTy gs) = gs := by
    cases gs with
    | nil => rfl
    | cons g gs =>
      dsimp only [groundTyListToTy, instTyList]
      rw [instTy_ground_roundtrip σ g, instTyList_ground_roundtrip σ gs]
end

/-- `GroundTy` embedded via `GroundTy.toTy` cannot contain `Ty.var` and matches itself under
every substitution `σ`. -/
theorem groundTy_matches_self (σ : GroundSubst) (g : GroundTy) :
    MatchesGround (GroundTy.toTy g) g :=
  ⟨σ, instTy_ground_roundtrip σ g⟩

end RustcCoherence
