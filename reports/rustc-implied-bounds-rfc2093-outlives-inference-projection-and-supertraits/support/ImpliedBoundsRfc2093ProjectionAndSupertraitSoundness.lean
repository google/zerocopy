/-!
# Implied Bounds, RFC 2093 Outlives Inference, WF Checking, Supertrait Elaboration, and Projection Normalization Soundness

Standalone Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)
mechanization corresponding to `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
and `058c701055c4b6f60f622d616afc0349911c38c3`):
- `compiler/rustc_hir_analysis/src/outlives/{mod.rs, implicit_infer.rs, utils.rs}`
- `compiler/rustc_hir_analysis/src/check/wfcheck.rs`
- `compiler/rustc_ty_utils/src/implied_bounds.rs`
- `compiler/rustc_trait_selection/src/traits/{outlives_bounds.rs, implied_outlives_bounds.rs, project.rs, wf.rs}`
- `compiler/rustc_type_ir/src/{elaborate.rs, outlives.rs}`

## Purity Discipline
- Zero imports beyond Lean `Init`.
- Every `def` carries explicit `noncomputable def` (no `noncomputable section`, no `partial def`,
  no `deriving DecidableEq/Repr`, and zero equation-compiler self-recursion — guaranteeing
  zero `._unsafe_rec` constants).
- Zero `sorry`, zero `admit`, zero `axiom`, zero `opaque`, zero `unsafe`, zero `Classical.choice`,
  zero `omega`, zero `bv_decide`, zero `native_decide`.
-/

namespace ImpliedBoundsRfc2093

/-! ## Part 1: Regions, Types, Outlives Targets, Equality, and Finite-Domain Utilities -/

/-- Lifetime/region AST corresponding to `ty::RegionKind` slots relevant to
RFC 2093 outlives inference and implied bounds:
- `.static` corresponds to `ty::ReStatic` (`'static`).
- `.early idx` corresponds to `ty::ReEarlyParam` (named lifetime parameter `'a` on item header).
- `.late idx` corresponds to `ty::ReBound` (higher-ranked `for<'b>` bound lifetime). -/
inductive Region where
  | static
  | early (idx : Nat)
  | late (idx : Nat)

noncomputable def Region.beq : Region → Region → Bool
  | .static, .static => true
  | .early a, .early b => Nat.beq a b
  | .late a, .late b => Nat.beq a b
  | _, _ => false

theorem region_beq_refl (r : Region) : Region.beq r r = true := by
  cases r with
  | static => rfl
  | early idx => exact Nat.beq_refl idx
  | late idx => exact Nat.beq_refl idx

theorem region_beq_eq {r1 r2 : Region} (h : Region.beq r1 r2 = true) : r1 = r2 := by
  cases r1 <;> cases r2
  · rfl
  · cases h
  · cases h
  · cases h
  · exact congrArg Region.early (Nat.eq_of_beq_eq_true h)
  · cases h
  · cases h
  · cases h
  · exact congrArg Region.late (Nat.eq_of_beq_eq_true h)

theorem region_beq_iff (r1 r2 : Region) : Region.beq r1 r2 = true ↔ r1 = r2 :=
  ⟨region_beq_eq, fun h => by subst h; exact region_beq_refl r1⟩

noncomputable def regionListBeq : List Region → List Region → Bool :=
  @List.rec Region (fun _ => List Region → Bool)
    (fun ys => match ys with | [] => true | _ :: _ => false)
    (fun x _ ih ys => match ys with | [] => false | y :: yt => Region.beq x y && ih yt)

theorem regionListBeq_cons (x : Region) (xt : List Region) (y : Region) (yt : List Region) :
    regionListBeq (x :: xt) (y :: yt) = (Region.beq x y && regionListBeq xt yt) := rfl

theorem regionListBeq_refl (xs : List Region) : regionListBeq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xt ih =>
    rw [regionListBeq_cons, region_beq_refl x, ih]
    rfl

theorem congrArg2 {α β γ : Type} (f : α → β → γ) {a1 a2 : α} {b1 b2 : β}
    (ha : a1 = a2) (hb : b1 = b2) : f a1 b1 = f a2 b2 := by
  subst ha; subst hb; rfl

theorem regionListBeq_eq {xs ys : List Region} (h : regionListBeq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xt ih =>
    cases ys with
    | nil => cases h
    | cons y yt =>
      rw [regionListBeq_cons] at h
      cases h1 : Region.beq x y <;> cases h2 : regionListBeq xt yt
      · rw [h1] at h; cases h
      · rw [h1] at h; cases h
      · rw [h1, h2] at h; cases h
      · exact congrArg2 List.cons (region_beq_eq h1) (ih h2)

mutual
  /-- Structural type AST capturing primitives, type parameters, references, pairs/tuples,
  nominal ADTs (`struct`/`enum`/`union`), associated-type projections, higher-ranked `fn`
  binders, and trait objects (`dyn Trait + 'r`). -/
  inductive Ty where
    | prim
    | param (idx : Nat)
    | ref (r : Region) (pointee : Ty)
    | pair (fst snd : Ty)
    | adt (id : Nat) (rArgs : List Region) (tArgs : TyArgs)
    | proj (selfTy : Ty) (traitId : Nat) (assocId : Nat) (rArgs : List Region)
    | fnBinder (arg ret : Ty)
    | dynObj (traitId : Nat) (rArgs : List Region) (boundR : Region)

  inductive TyArgs where
    | nil
    | cons (hd : Ty) (tl : TyArgs)
end

noncomputable def tyArgsToList : TyArgs → List Ty :=
  @TyArgs.rec (fun _ => Unit) (fun _ => List Ty)
    () (fun _ => ()) (fun _ _ _ => ()) (fun _ _ _ _ => ())
    (fun _ _ _ _ => ()) (fun _ _ _ _ _ => ()) (fun _ _ _ _ => ()) (fun _ _ _ => ())
    [] (fun hd _ _ tl => hd :: tl)

noncomputable def listToTyArgs : List Ty → TyArgs :=
  List.foldr TyArgs.cons TyArgs.nil

noncomputable def tySize : Ty → Nat :=
  @Ty.rec (fun _ => Nat) (fun _ => Nat)
    1
    (fun _ => 1)
    (fun _ _ n => n + 1)
    (fun _ _ n1 n2 => n1 + n2 + 1)
    (fun _ _ _ n => n + 1)
    (fun _ _ _ _ n => n + 1)
    (fun _ _ n1 n2 => n1 + n2 + 1)
    (fun _ _ _ => 1)
    0
    (fun _ _ nh nt => nh + nt)

noncomputable def tyArgsSize : TyArgs → Nat :=
  @TyArgs.rec (fun _ => Nat) (fun _ => Nat)
    1
    (fun _ => 1)
    (fun _ _ n => n + 1)
    (fun _ _ n1 n2 => n1 + n2 + 1)
    (fun _ _ _ n => n + 1)
    (fun _ _ _ _ n => n + 1)
    (fun _ _ n1 n2 => n1 + n2 + 1)
    (fun _ _ _ => 1)
    0
    (fun _ _ nh nt => nh + nt)

noncomputable def tyBeq : Ty → Ty → Bool :=
  @Ty.rec (fun _ => Ty → Bool) (fun _ => TyArgs → Bool)
    (fun t2 => match t2 with | .prim => true | _ => false)
    (fun i1 t2 => match t2 with | .param i2 => Nat.beq i1 i2 | _ => false)
    (fun r1 _ ih t2 => match t2 with | .ref r2 p2 => Region.beq r1 r2 && ih p2 | _ => false)
    (fun _ _ ih1 ih2 t2 => match t2 with | .pair a2 b2 => ih1 a2 && ih2 b2 | _ => false)
    (fun id1 rs1 _ ihArgs t2 =>
      match t2 with
      | .adt id2 rs2 ts2 => Nat.beq id1 id2 && regionListBeq rs1 rs2 && ihArgs ts2
      | _ => false)
    (fun _ tr1 as1 rs1 ihS t2 =>
      match t2 with
      | .proj s2 tr2 as2 rs2 =>
        ihS s2 && Nat.beq tr1 tr2 && Nat.beq as1 as2 && regionListBeq rs1 rs2
      | _ => false)
    (fun _ _ ihA ihR t2 => match t2 with | .fnBinder a2 r2 => ihA a2 && ihR r2 | _ => false)
    (fun tr1 rs1 b1 t2 =>
      match t2 with
      | .dynObj tr2 rs2 b2 => Nat.beq tr1 tr2 && regionListBeq rs1 rs2 && Region.beq b1 b2
      | _ => false)
    (fun ts2 => match ts2 with | .nil => true | _ => false)
    (fun _ _ ihH ihT ts2 => match ts2 with | .cons h2 t2 => ihH h2 && ihT t2 | _ => false)

noncomputable def tyArgsBeq : TyArgs → TyArgs → Bool :=
  @TyArgs.rec (fun _ => Ty → Bool) (fun _ => TyArgs → Bool)
    (fun t2 => match t2 with | .prim => true | _ => false)
    (fun i1 t2 => match t2 with | .param i2 => Nat.beq i1 i2 | _ => false)
    (fun r1 _ ih t2 => match t2 with | .ref r2 p2 => Region.beq r1 r2 && ih p2 | _ => false)
    (fun _ _ ih1 ih2 t2 => match t2 with | .pair a2 b2 => ih1 a2 && ih2 b2 | _ => false)
    (fun id1 rs1 _ ihArgs t2 =>
      match t2 with
      | .adt id2 rs2 ts2 => Nat.beq id1 id2 && regionListBeq rs1 rs2 && ihArgs ts2
      | _ => false)
    (fun _ tr1 as1 rs1 ihS t2 =>
      match t2 with
      | .proj s2 tr2 as2 rs2 =>
        ihS s2 && Nat.beq tr1 tr2 && Nat.beq as1 as2 && regionListBeq rs1 rs2
      | _ => false)
    (fun _ _ ihA ihR t2 => match t2 with | .fnBinder a2 r2 => ihA a2 && ihR r2 | _ => false)
    (fun tr1 rs1 b1 t2 =>
      match t2 with
      | .dynObj tr2 rs2 b2 => Nat.beq tr1 tr2 && regionListBeq rs1 rs2 && Region.beq b1 b2
      | _ => false)
    (fun ts2 => match ts2 with | .nil => true | _ => false)
    (fun _ _ ihH ihT ts2 => match ts2 with | .cons h2 t2 => ihH h2 && ihT t2 | _ => false)

theorem bool_and_eq_true {a b : Bool} : (a && b) = true → a = true ∧ b = true := by
  cases a <;> cases b <;> intro h
  · cases h
  · cases h
  · cases h
  · exact ⟨rfl, rfl⟩

theorem ty_rec_pair (P : Ty → Prop) (Q : TyArgs → Prop)
    (hprim : P .prim)
    (hparam : ∀ idx, P (.param idx))
    (href : ∀ r p, P p → P (.ref r p))
    (hpair : ∀ a b, P a → P b → P (.pair a b))
    (hadt : ∀ id rs ts, Q ts → P (.adt id rs ts))
    (hproj : ∀ s tr as rs, P s → P (.proj s tr as rs))
    (hfn : ∀ a b, P a → P b → P (.fnBinder a b))
    (hdyn : ∀ tr rs b, P (.dynObj tr rs b))
    (hnil : Q .nil)
    (hcons : ∀ hd tl, P hd → Q tl → Q (.cons hd tl)) :
    (∀ t, P t) ∧ (∀ ts, Q ts) :=
  ⟨@Ty.rec P Q hprim hparam href hpair hadt hproj hfn hdyn hnil hcons,
   @TyArgs.rec P Q hprim hparam href hpair hadt hproj hfn hdyn hnil hcons⟩

theorem tyBeq_refl_both :
    (∀ t : Ty, tyBeq t t = true) ∧ (∀ ts : TyArgs, tyArgsBeq ts ts = true) := by
  apply ty_rec_pair
    (fun t => tyBeq t t = true)
    (fun ts => tyArgsBeq ts ts = true)
  · rfl
  · intro idx; exact Nat.beq_refl idx
  · intro r p ih
    change (Region.beq r r && tyBeq p p) = true
    rw [region_beq_refl r, ih]; rfl
  · intro a b ih1 ih2
    change (tyBeq a a && tyBeq b b) = true
    rw [ih1, ih2]; rfl
  · intro id rs ts ihArgs
    change ((Nat.beq id id && regionListBeq rs rs) && tyArgsBeq ts ts) = true
    rw [Nat.beq_refl id, regionListBeq_refl rs, ihArgs]; rfl
  · intro s tr as rs ihS
    change (((tyBeq s s && Nat.beq tr tr) && Nat.beq as as) && regionListBeq rs rs) = true
    rw [ihS, Nat.beq_refl tr, Nat.beq_refl as, regionListBeq_refl rs]; rfl
  · intro a b ihA ihR
    change (tyBeq a a && tyBeq b b) = true
    rw [ihA, ihR]; rfl
  · intro tr rs b
    change ((Nat.beq tr tr && regionListBeq rs rs) && Region.beq b b) = true
    rw [Nat.beq_refl tr, regionListBeq_refl rs, region_beq_refl b]; rfl
  · rfl
  · intro h t ihH ihT
    change (tyBeq h h && tyArgsBeq t t) = true
    rw [ihH, ihT]; rfl

theorem tyBeq_refl (t : Ty) : tyBeq t t = true := tyBeq_refl_both.1 t
theorem tyArgsBeq_refl (ts : TyArgs) : tyArgsBeq ts ts = true := tyBeq_refl_both.2 ts

theorem tyBeq_eq_both :
    (∀ t1 t2 : Ty, tyBeq t1 t2 = true → t1 = t2) ∧
    (∀ ts1 ts2 : TyArgs, tyArgsBeq ts1 ts2 = true → ts1 = ts2) := by
  apply ty_rec_pair
    (fun t1 => ∀ t2, tyBeq t1 t2 = true → t1 = t2)
    (fun ts1 => ∀ ts2, tyArgsBeq ts1 ts2 = true → ts1 = ts2)
  · intro t2 h; cases t2 <;> first | rfl | cases h
  · intro i1 t2 h
    cases t2 with
    | param i2 => exact congrArg Ty.param (Nat.eq_of_beq_eq_true h)
    | _ => cases h
  · intro r1 p1 ih t2 h
    cases t2 with
    | ref r2 p2 =>
      have h' := bool_and_eq_true h
      exact congrArg2 Ty.ref (region_beq_eq h'.1) (ih p2 h'.2)
    | _ => cases h
  · intro a1 b1 ih1 ih2 t2 h
    cases t2 with
    | pair a2 b2 =>
      have h' := bool_and_eq_true h
      exact congrArg2 Ty.pair (ih1 a2 h'.1) (ih2 b2 h'.2)
    | _ => cases h
  · intro id1 rs1 ts1 ihArgs t2 h
    cases t2 with
    | adt id2 rs2 ts2 =>
      have h12 := bool_and_eq_true h
      have h1 := bool_and_eq_true h12.1
      have hid := Nat.eq_of_beq_eq_true h1.1
      have hrs := regionListBeq_eq h1.2
      have hts := ihArgs ts2 h12.2
      subst hid; subst hrs; subst hts; rfl
    | _ => cases h
  · intro s1 tr1 as1 rs1 ihS t2 h
    cases t2 with
    | proj s2 tr2 as2 rs2 =>
      have h1 := bool_and_eq_true h
      have h2 := bool_and_eq_true h1.1
      have h3 := bool_and_eq_true h2.1
      have hs := ihS s2 h3.1
      have htr := Nat.eq_of_beq_eq_true h3.2
      have has := Nat.eq_of_beq_eq_true h2.2
      have hrs := regionListBeq_eq h1.2
      subst hs; subst htr; subst has; subst hrs; rfl
    | _ => cases h
  · intro a1 r1 ihA ihR t2 h
    cases t2 with
    | fnBinder a2 r2 =>
      have h' := bool_and_eq_true h
      exact congrArg2 Ty.fnBinder (ihA a2 h'.1) (ihR r2 h'.2)
    | _ => cases h
  · intro tr1 rs1 b1 t2 h
    cases t2 with
    | dynObj tr2 rs2 b2 =>
      have h1 := bool_and_eq_true h
      have h2 := bool_and_eq_true h1.1
      have htr := Nat.eq_of_beq_eq_true h2.1
      have hrs := regionListBeq_eq h2.2
      have hb := region_beq_eq h1.2
      subst htr; subst hrs; subst hb; rfl
    | _ => cases h
  · intro ts2 h; cases ts2 <;> first | rfl | cases h
  · intro h1 t1 ihH ihT ts2 h
    cases ts2 with
    | cons h2 t2 =>
      have h' := bool_and_eq_true h
      exact congrArg2 TyArgs.cons (ihH h2 h'.1) (ihT t2 h'.2)
    | _ => cases h

theorem tyBeq_eq {t1 t2 : Ty} (h : tyBeq t1 t2 = true) : t1 = t2 := tyBeq_eq_both.1 t1 t2 h
theorem tyBeq_iff (t1 t2 : Ty) : tyBeq t1 t2 = true ↔ t1 = t2 :=
  ⟨tyBeq_eq, fun h => by subst h; exact tyBeq_refl t1⟩

/-- Left-hand side of an inferred or explicit outlives clause (`'a: 'b`, `T: 'a`,
or `<T as Trait>::Assoc: 'a`), matching `rustc_hir_analysis::outlives::utils::RequiredClauses`. -/
inductive OutlivesTarget where
  | region (r : Region)
  | param (idx : Nat)
  | proj (selfTy : Ty) (traitId : Nat) (assocId : Nat) (rArgs : List Region)

noncomputable def OutlivesTarget.beq : OutlivesTarget → OutlivesTarget → Bool
  | .region r1, .region r2 => Region.beq r1 r2
  | .param i1, .param i2 => Nat.beq i1 i2
  | .proj s1 tr1 as1 rs1, .proj s2 tr2 as2 rs2 =>
    tyBeq s1 s2 && Nat.beq tr1 tr2 && Nat.beq as1 as2 && regionListBeq rs1 rs2
  | _, _ => false

theorem target_beq_refl (t : OutlivesTarget) : OutlivesTarget.beq t t = true := by
  cases t with
  | region r => exact region_beq_refl r
  | param idx => exact Nat.beq_refl idx
  | proj s tr as rs =>
    change (((tyBeq s s && Nat.beq tr tr) && Nat.beq as as) && regionListBeq rs rs) = true
    rw [tyBeq_refl s, Nat.beq_refl tr, Nat.beq_refl as, regionListBeq_refl rs]; rfl

theorem target_beq_eq {t1 t2 : OutlivesTarget} (h : OutlivesTarget.beq t1 t2 = true) : t1 = t2 := by
  cases t1 <;> cases t2
  · exact congrArg OutlivesTarget.region (region_beq_eq h)
  · cases h
  · cases h
  · cases h
  · exact congrArg OutlivesTarget.param (Nat.eq_of_beq_eq_true h)
  · cases h
  · cases h
  · cases h
  · have h1 := bool_and_eq_true h
    have h2 := bool_and_eq_true h1.1
    have h3 := bool_and_eq_true h2.1
    have hs := tyBeq_eq h3.1
    have htr := Nat.eq_of_beq_eq_true h3.2
    have has := Nat.eq_of_beq_eq_true h2.2
    have hrs := regionListBeq_eq h1.2
    subst hs; subst htr; subst has; subst hrs; rfl

/-- An outlives clause `lhs : rhs`. -/
structure OutlivesBound where
  lhs : OutlivesTarget
  rhs : Region

noncomputable def OutlivesBound.beq (b1 b2 : OutlivesBound) : Bool :=
  OutlivesTarget.beq b1.lhs b2.lhs && Region.beq b1.rhs b2.rhs

theorem bound_beq_refl (b : OutlivesBound) : OutlivesBound.beq b b = true := by
  unfold OutlivesBound.beq
  rw [target_beq_refl b.lhs, region_beq_refl b.rhs]; rfl

theorem bound_beq_eq {b1 b2 : OutlivesBound} (h : OutlivesBound.beq b1 b2 = true) : b1 = b2 := by
  cases b1 with | mk l1 r1 =>
  cases b2 with | mk l2 r2 =>
  have h' := bool_and_eq_true h
  have hl := target_beq_eq h'.1
  have hr := region_beq_eq h'.2
  subst hl; subst hr; rfl

/-- Crate-level table entry tagging an inferred or explicit outlives clause with its owning ADT ID. -/
structure TaggedBound where
  adtId : Nat
  bound : OutlivesBound

noncomputable def TaggedBound.beq (t1 t2 : TaggedBound) : Bool :=
  Nat.beq t1.adtId t2.adtId && OutlivesBound.beq t1.bound t2.bound

theorem tagged_beq_refl (t : TaggedBound) : TaggedBound.beq t t = true := by
  unfold TaggedBound.beq
  rw [Nat.beq_refl t.adtId, bound_beq_refl t.bound]; rfl

theorem tagged_beq_eq {t1 t2 : TaggedBound} (h : TaggedBound.beq t1 t2 = true) : t1 = t2 := by
  cases t1 with | mk i1 b1 =>
  cases t2 with | mk i2 b2 =>
  have h' := bool_and_eq_true h
  have hi := Nat.eq_of_beq_eq_true h'.1
  have hb := bound_beq_eq h'.2
  subst hi; subst hb; rfl

/-! ### List Membership, Subset, Union, and `filterScore` Termination Machinery (Zero `omega`) -/

noncomputable def listMem {α : Type} (eq : α → α → Bool) (x : α) (xs : List α) : Bool :=
  xs.any (fun y => eq x y)

theorem listMem_spec {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (x : α) (xs : List α) : listMem eq x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    change (eq x y || listMem eq x ys) = true ↔ x ∈ y :: ys
    constructor
    · intro h
      cases h1 : eq x y
      · rw [h1] at h
        have hmem : x ∈ ys := ih.mp h
        exact List.mem_cons_of_mem y hmem
      · have hxy := heq h1
        subst hxy
        exact List.mem_cons_self
    · intro h
      cases h with
      | head =>
        rw [hrefl x]; rfl
      | tail _ hmem =>
        have h2 := ih.mpr hmem
        cases eq x y <;> simp [h2]

noncomputable def dedupList {α : Type} (eq : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (fun x acc => if listMem eq x acc then acc else x :: acc) []

theorem mem_dedupList_iff {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (x : α) (xs : List α) : x ∈ dedupList eq xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => exact Iff.rfl
  | cons y ys ih =>
    change x ∈ (if listMem eq y (dedupList eq ys) then dedupList eq ys else y :: dedupList eq ys) ↔
      x ∈ y :: ys
    cases hy : listMem eq y (dedupList eq ys)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h
        cases h with
        | head => exact List.mem_cons_self
        | tail _ hm => exact List.mem_cons_of_mem y ((ih x).mp hm)
      · intro h
        cases h with
        | head => exact List.mem_cons_self
        | tail _ hm => exact List.mem_cons_of_mem y ((ih x).mpr hm)
    · simp only [↓reduceIte]
      have hyIn : y ∈ ys := (ih y).mp ((listMem_spec eq hrefl heq y (dedupList eq ys)).mp hy)
      constructor
      · intro h; exact List.mem_cons_of_mem y ((ih x).mp h)
      · intro h
        cases h with
        | head => exact (ih y).mpr hyIn
        | tail _ hm => exact (ih x).mpr hm

noncomputable def ListSubset {α : Type} (xs ys : List α) : Prop :=
  ∀ x, x ∈ xs → x ∈ ys

theorem listSubset_refl {α : Type} (xs : List α) : ListSubset xs xs :=
  fun _ h => h

theorem listSubset_trans {α : Type} {xs ys zs : List α}
    (h1 : ListSubset xs ys) (h2 : ListSubset ys zs) : ListSubset xs zs :=
  fun x hx => h2 x (h1 x hx)

noncomputable def filterScore {α : Type} (eq : α → α → Bool) (univ xs : List α) : Nat :=
  (univ.filter (fun u => listMem eq u xs)).length

theorem filterScore_le_length {α : Type} (eq : α → α → Bool) (univ xs : List α) :
    filterScore eq univ xs ≤ univ.length := by
  induction univ with
  | nil => exact Nat.le_refl 0
  | cons u us ih =>
    unfold filterScore
    change (List.filter (fun u0 => listMem eq u0 xs) (u :: us)).length ≤ (u :: us).length
    rw [List.filter_cons]
    cases listMem eq u xs
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.le_trans ih (Nat.le_succ _)
    · simp only [↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ ih

theorem filterScore_mono {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (univ : List α) {xs ys : List α} (hsub : ListSubset xs ys) :
    filterScore eq univ xs ≤ filterScore eq univ ys := by
  induction univ with
  | nil => exact Nat.le_refl 0
  | cons u us ih =>
    unfold filterScore
    change (List.filter (fun u0 => listMem eq u0 xs) (u :: us)).length ≤
      (List.filter (fun u0 => listMem eq u0 ys) (u :: us)).length
    rw [List.filter_cons, List.filter_cons]
    cases hx : listMem eq u xs
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases listMem eq u ys
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih
      · simp only [↓reduceIte, List.length_cons]; exact Nat.le_trans ih (Nat.le_succ _)
    · have hu_x : u ∈ xs := (listMem_spec eq hrefl heq u xs).mp hx
      have hu_y : u ∈ ys := hsub u hu_x
      have hy : listMem eq u ys = true := (listMem_spec eq hrefl heq u ys).mpr hu_y
      rw [hy]
      simp only [↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ ih

theorem filterScore_strict_of_witness {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (univ : List α) {xs ys : List α} (hsub : ListSubset xs ys)
    {w : α} (hwU : w ∈ univ) (hwNotX : ¬ (w ∈ xs)) (hwY : w ∈ ys) :
    Nat.succ (filterScore eq univ xs) ≤ filterScore eq univ ys := by
  induction univ with
  | nil => cases hwU
  | cons u us ih =>
    unfold filterScore
    change Nat.succ (List.filter (fun u0 => listMem eq u0 xs) (u :: us)).length ≤
      (List.filter (fun u0 => listMem eq u0 ys) (u :: us)).length
    rw [List.filter_cons, List.filter_cons]
    cases hwU with
    | head =>
      have hx : listMem eq w xs = false := by
        cases hx0 : listMem eq w xs
        · rfl
        · exact False.elim (hwNotX ((listMem_spec eq hrefl heq w xs).mp hx0))
      have hy : listMem eq w ys = true := (listMem_spec eq hrefl heq w ys).mpr hwY
      rw [hx, hy]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ (filterScore_mono eq hrefl heq us hsub)
    | tail _ hmem =>
      have ih' := ih hmem
      cases hx : listMem eq u xs
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases listMem eq u ys
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih'
        · simp only [↓reduceIte, List.length_cons]; exact Nat.le_trans ih' (Nat.le_succ _)
      · have hu_y : u ∈ ys := hsub u ((listMem_spec eq hrefl heq u xs).mp hx)
        have hy : listMem eq u ys = true := (listMem_spec eq hrefl heq u ys).mpr hu_y
        rw [hy]
        simp only [↓reduceIte, List.length_cons]
        exact Nat.succ_le_succ ih'

noncomputable def iterFn {α : Type} (f : α → α) (n : Nat) (x : α) : α :=
  @Nat.rec (fun _ => α) x (fun _ acc => f acc) n

theorem iterFn_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iterFn f (Nat.succ n) x = f (iterFn f n x) := rfl

theorem iterFn_mono {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true) (heq : ∀ {a b}, eq a b = true → a = b)
    (F : List α → List α)
    (hBase : ∀ x, x ∈ F [] → x ∈ F [])
    (hMono : ∀ {s1 s2}, ListSubset s1 s2 → ListSubset (F s1) (F s2)) :
    ∀ n : Nat, ListSubset (iterFn F n []) (iterFn F (Nat.succ n) []) := by
  let _ := eq
  let _ := hrefl
  let _ := @heq
  let _ := hBase
  intro n
  induction n with
  | zero =>
    intro x hx
    cases hx
  | succ k ih =>
    exact hMono ih

/-- General finite-universe fixed-point termination theorem (with zero `omega` and
zero `Classical.choice`): if `F` is monotone and always stays inside `univ`, then
iterating `F` from `[]` reaches a post-fixed point (`ListSubset (F (iterFn F k [])) (iterFn F k [])`)
within `k ≤ univ.length` rounds. -/
theorem finite_universe_fixpoint_terminates {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (F : List α → List α)
    (univ : List α)
    (hInUniv : ∀ s, ListSubset s univ → ListSubset (F s) univ)
    (hMono : ∀ {s1 s2}, ListSubset s1 s2 → ListSubset (F s1) (F s2)) :
    ∀ n : Nat,
      (∀ k : Nat, k ≤ n → ListSubset (iterFn F (Nat.succ k) []) (iterFn F k []) → False) →
      n + 1 ≤ filterScore eq univ (iterFn F (Nat.succ n) []) := by
  intro n hNoFix
  have hIterInUniv : ∀ m : Nat, ListSubset (iterFn F m []) univ := by
    intro m
    induction m with
    | zero => intro _ hx; cases hx
    | succ k ih => exact hInUniv _ ih
  induction n with
  | zero =>
    have h0NotFix : ¬ ListSubset (iterFn F 1 []) (iterFn F 0 []) :=
      fun h => hNoFix 0 (Nat.le_refl 0) h
    have hSub : ListSubset (iterFn F 0 []) (iterFn F 1 []) :=
      iterFn_mono eq hrefl @heq F (fun _ hx => hx) hMono 0
    -- Inspect F [] directly against univ
    have hInF1 : ListSubset (F []) univ := hIterInUniv 1
    cases hF1 : F [] with
    | nil =>
      exact False.elim (h0NotFix (fun x hx => by change x ∈ F [] at hx; rw [hF1] at hx; cases hx))
    | cons w ws =>
      have hw1 : w ∈ iterFn F 1 [] := by change w ∈ F []; rw [hF1]; exact List.mem_cons_self
      have hwU : w ∈ univ := hInF1 w (by rw [hF1]; exact List.mem_cons_self)
      have hwNot0 : ¬ (w ∈ iterFn F 0 []) := fun hm => by cases hm
      have hStrict := filterScore_strict_of_witness eq hrefl @heq univ hSub hwU hwNot0 hw1
      exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hStrict
  | succ m ih =>
    have hmNoFix : ∀ k, k ≤ m → ListSubset (iterFn F (Nat.succ k) []) (iterFn F k []) → False :=
      fun k hk => hNoFix k (Nat.le_trans hk (Nat.le_succ m))
    have ihScore := ih hmNoFix
    have hStepNotFix : ¬ ListSubset (iterFn F (Nat.succ (Nat.succ m)) []) (iterFn F (Nat.succ m) []) :=
      fun h => hNoFix (Nat.succ m) (Nat.le_refl (Nat.succ m)) h
    let nextS := iterFn F (Nat.succ (Nat.succ m)) []
    let curS := iterFn F (Nat.succ m) []
    have hAll : ∀ l : List α, ListSubset l nextS →
        (∀ x, x ∈ l → x ∈ curS) ∨ (∃ w, w ∈ nextS ∧ ¬ (w ∈ curS)) := by
      intro l hl
      induction l with
      | nil => exact Or.inl (fun _ hx => by cases hx)
      | cons a as iha =>
        cases haIn : listMem eq a curS
        · exact Or.inr ⟨a, hl a List.mem_cons_self,
            fun h => by rw [(listMem_spec eq hrefl @heq a curS).mpr h] at haIn; cases haIn⟩
        · cases iha (fun x hx => hl x (List.mem_cons_of_mem a hx)) with
          | inl hRest =>
            exact Or.inl (fun x hx => by
              cases hx with
              | head => exact (listMem_spec eq hrefl @heq a curS).mp haIn
              | tail _ hm => exact hRest x hm)
          | inr hWit => exact Or.inr hWit
    cases hAll nextS (listSubset_refl nextS) with
    | inl hSub => exact False.elim (hStepNotFix hSub)
    | inr hWit =>
      obtain ⟨w, hwNext, hwNotCur⟩ := hWit
      have hwU := hIterInUniv (Nat.succ (Nat.succ m)) w hwNext
      have hSubStep : ListSubset curS nextS := iterFn_mono eq hrefl @heq F (fun _ hx => hx) hMono (Nat.succ m)
      have hStrict := filterScore_strict_of_witness eq hrefl @heq univ hSubStep hwU hwNotCur hwNext
      exact Nat.le_trans (Nat.succ_le_succ ihScore) hStrict

/-- Constructive computable scan checking whether every element of `F (iterFn F k [])`
is already in `iterFn F k []`. -/
noncomputable def isFixpointStep {α : Type} (eq : α → α → Bool) (F : List α → List α)
    (k : Nat) : Bool :=
  (F (iterFn F k [])).all (fun x => listMem eq x (iterFn F k []))

theorem isFixpointStep_sound {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (F : List α → List α) (k : Nat)
    (h : isFixpointStep eq F k = true) :
    ListSubset (iterFn F (Nat.succ k) []) (iterFn F k []) := by
  intro x hx
  unfold isFixpointStep at h
  rw [List.all_eq_true] at h
  exact (listMem_spec eq hrefl heq x (iterFn F k [])).mp (h x hx)

noncomputable def firstFixpointFuel {α : Type} (eq : α → α → Bool) (F : List α → List α)
    (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldr (fun k acc => if isFixpointStep eq F k then k else acc) limit

theorem firstFixpointFuel_terminates {α : Type} (eq : α → α → Bool)
    (hrefl : ∀ a, eq a a = true)
    (heq : ∀ {a b}, eq a b = true → a = b)
    (F : List α → List α) (univ : List α)
    (hInUniv : ∀ s, ListSubset s univ → ListSubset (F s) univ)
    (hMono : ∀ {s1 s2}, ListSubset s1 s2 → ListSubset (F s1) (F s2)) :
    ∃ k : Nat, k ≤ univ.length ∧ ListSubset (iterFn F (Nat.succ k) []) (iterFn F k []) := by
  -- Decidably scan k ∈ [0 .. univ.length] using Bool decidability
  have hCheck : ∀ ms : List Nat,
      (∃ k, k ∈ ms ∧ isFixpointStep eq F k = true) ∨
      (∀ k, k ∈ ms → isFixpointStep eq F k = false) := by
    intro ms
    induction ms with
    | nil => exact Or.inr (fun _ hk => by cases hk)
    | cons m mst ihm =>
      cases hm : isFixpointStep eq F m
      · cases ihm with
        | inl h => obtain ⟨k, hkm, hk⟩ := h; exact Or.inl ⟨k, List.mem_cons_of_mem m hkm, hk⟩
        | inr h =>
          exact Or.inr (fun k hk => by
            cases hk with
            | head => exact hm
            | tail _ hkm => exact h k hkm)
      · exact Or.inl ⟨m, List.mem_cons_self, hm⟩
  cases hCheck (List.range (univ.length + 1)) with
  | inl h =>
    obtain ⟨k, hkMem, hkFix⟩ := h
    rw [List.mem_range] at hkMem
    exact ⟨k, Nat.le_of_lt_succ hkMem, isFixpointStep_sound eq hrefl @heq F k hkFix⟩
  | inr hAllFalse =>
    have hBound := finite_universe_fixpoint_terminates eq hrefl @heq F univ hInUniv hMono univ.length
      (fun k hk hSub => by
        have hkMem : k ∈ List.range (univ.length + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hk)
        have hf := hAllFalse k hkMem
        have hTrue : isFixpointStep eq F k = true := by
          unfold isFixpointStep
          rw [List.all_eq_true]
          intro x hx
          exact (listMem_spec eq hrefl @heq x (iterFn F k [])).mpr (hSub x hx)
        rw [hTrue] at hf; cases hf)
    have hLe := filterScore_le_length eq univ (iterFn F (Nat.succ univ.length) [])
    exact False.elim (Nat.not_succ_le_self univ.length (Nat.le_trans hBound hLe))

/-! ## Part 2: Substitutions, `pushOutlivesComponents`, and Syntactic WF/Outlives Semantics -/

noncomputable def getRegionOr (rs : List Region) (idx : Nat) : Region :=
  (rs.drop idx).head?.getD .static

noncomputable def getTyArgOr (ts : TyArgs) (idx : Nat) : Ty :=
  ((tyArgsToList ts).drop idx).head?.getD .prim

noncomputable def substRegion (rEnv : List Region) : Region → Region
  | .static => .static
  | .early i => getRegionOr rEnv i
  | .late k => .late k

theorem substRegion_static (rEnv : List Region) : substRegion rEnv .static = .static := rfl
theorem substRegion_late (rEnv : List Region) (k : Nat) : substRegion rEnv (.late k) = .late k := rfl
theorem substRegion_early (rEnv : List Region) (i : Nat) :
    substRegion rEnv (.early i) = getRegionOr rEnv i := rfl

noncomputable def substTy (rEnv : List Region) (tEnv : TyArgs) : Ty → Ty :=
  @Ty.rec (fun _ => Ty) (fun _ => TyArgs)
    .prim
    (fun idx => getTyArgOr tEnv idx)
    (fun r _ ih => .ref (substRegion rEnv r) ih)
    (fun _ _ ih1 ih2 => .pair ih1 ih2)
    (fun id rs _ ihArgs => .adt id (rs.map (substRegion rEnv)) ihArgs)
    (fun _ tr as rs ihS => .proj ihS tr as (rs.map (substRegion rEnv)))
    (fun _ _ ihA ihR => .fnBinder ihA ihR)
    (fun tr rs b => .dynObj tr (rs.map (substRegion rEnv)) (substRegion rEnv b))
    .nil
    (fun _ _ ihH ihT => .cons ihH ihT)

noncomputable def substTyArgs (rEnv : List Region) (tEnv : TyArgs) : TyArgs → TyArgs :=
  @TyArgs.rec (fun _ => Ty) (fun _ => TyArgs)
    .prim
    (fun idx => getTyArgOr tEnv idx)
    (fun r _ ih => .ref (substRegion rEnv r) ih)
    (fun _ _ ih1 ih2 => .pair ih1 ih2)
    (fun id rs _ ihArgs => .adt id (rs.map (substRegion rEnv)) ihArgs)
    (fun _ tr as rs ihS => .proj ihS tr as (rs.map (substRegion rEnv)))
    (fun _ _ ihA ihR => .fnBinder ihA ihR)
    (fun tr rs b => .dynObj tr (rs.map (substRegion rEnv)) (substRegion rEnv b))
    .nil
    (fun _ _ ihH ihT => .cons ihH ihT)

noncomputable def substTarget (rEnv : List Region) (tEnv : TyArgs) : OutlivesTarget → OutlivesTarget
  | .region r => .region (substRegion rEnv r)
  | .param idx =>
    match getTyArgOr tEnv idx with
    | .param j => .param j
    | .ref r _ => .region r
    | .proj s tr as rs => .proj s tr as rs
    | _ => .region .static
  | .proj s tr as rs => .proj (substTy rEnv tEnv s) tr as (rs.map (substRegion rEnv))

noncomputable def substBound (rEnv : List Region) (tEnv : TyArgs) (b : OutlivesBound) : OutlivesBound :=
  { lhs := substTarget rEnv tEnv b.lhs, rhs := substRegion rEnv b.rhs }

noncomputable def regionIsLate : Region → Bool
  | .late _ => true
  | _ => false

noncomputable def tyHasLate : Ty → Bool :=
  @Ty.rec (fun _ => Bool) (fun _ => Bool)
    false
    (fun _ => false)
    (fun r _ ih => regionIsLate r || ih)
    (fun _ _ ih1 ih2 => ih1 || ih2)
    (fun _ rs _ ihArgs => rs.any regionIsLate || ihArgs)
    (fun _ _ _ rs ihS => ihS || rs.any regionIsLate)
    (fun _ _ ihA ihR => ihA || ihR)
    (fun _ rs b => rs.any regionIsLate || regionIsLate b)
    false
    (fun _ _ ihH ihT => ihH || ihT)

/-- Models `rustc_type_ir::outlives::Component`. -/
inductive Component where
  | region (r : Region)
  | param (idx : Nat)
  | alias (selfTy : Ty) (traitId : Nat) (assocId : Nat) (rArgs : List Region)
  | escapingAlias (sub : List Component)

/-- Models `rustc_type_ir::outlives::push_outlives_components`:
- ignores bound regions (`Region.late`) when pushing `Region` components (`if !lt.is_bound()`)
- pushes `Component.alias` and stops descent when a projection has no escaping late-bound regions
- falls back to `Component.escapingAlias` over projection arguments when late-bound regions appear. -/
noncomputable def pushOutlivesComponents : Ty → List Component :=
  @Ty.rec (fun _ => List Component) (fun _ => List Component)
    []
    (fun idx => [Component.param idx])
    (fun r _ ih => (if regionIsLate r then [] else [Component.region r]) ++ ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun _ rs _ ihArgs =>
      (rs.filter (fun r => !regionIsLate r)).map Component.region ++ ihArgs)
    (fun s tr as rs ihS =>
      if tyHasLate s || rs.any regionIsLate then
        [Component.escapingAlias (ihS ++ (rs.filter (fun r => !regionIsLate r)).map Component.region)]
      else
        [Component.alias s tr as rs])
    (fun _ _ ihA ihR => ihA ++ ihR)
    (fun _ rs b =>
      (rs.filter (fun r => !regionIsLate r)).map Component.region ++
      (if regionIsLate b then [] else [Component.region b]))
    []
    (fun _ _ ihH ihT => ihH ++ ihT)

/-- Declarative semantic outlives relation `env ⊢ target : rhs`. -/
inductive OutlivesHolds (env : List OutlivesBound) : OutlivesTarget → Region → Prop where
  | refl (r : Region) : OutlivesHolds env (.region r) r
  | staticTop (t : OutlivesTarget) (r : Region) :
      OutlivesHolds env t .static → OutlivesHolds env t r
  | staticOutlives (r : Region) : OutlivesHolds env (.region .static) r
  | assume (b : OutlivesBound) : b ∈ env → OutlivesHolds env b.lhs b.rhs
  | trans {t : OutlivesTarget} {r1 r2 : Region} :
      OutlivesHolds env t r1 → OutlivesHolds env (.region r1) r2 → OutlivesHolds env t r2

theorem outlivesHolds_weaken {e1 e2 : List OutlivesBound} (hsub : ListSubset e1 e2)
    {t : OutlivesTarget} {r : Region} (h : OutlivesHolds e1 t r) : OutlivesHolds e2 t r := by
  induction h with
  | refl r0 => exact OutlivesHolds.refl r0
  | staticTop t0 r0 _ ih => exact OutlivesHolds.staticTop t0 r0 ih
  | staticOutlives r0 => exact OutlivesHolds.staticOutlives r0
  | assume b hb => exact OutlivesHolds.assume b (hsub b hb)
  | trans _ _ ih1 ih2 => exact OutlivesHolds.trans ih1 ih2

/-- Declarative syntactic type-outlives judgment `env ⊢ ty : rhs` (RFC 1214). -/
inductive TyOutlivesHolds (env : List OutlivesBound) : Ty → Region → Prop where
  | prim (r : Region) : TyOutlivesHolds env .prim r
  | param (idx : Nat) (r : Region) :
      OutlivesHolds env (.param idx) r → TyOutlivesHolds env (.param idx) r
  | ref (rx r : Region) (pointee : Ty) :
      OutlivesHolds env (.region rx) r → TyOutlivesHolds env pointee r →
      TyOutlivesHolds env (.ref rx pointee) r
  | pair (a b : Ty) (r : Region) :
      TyOutlivesHolds env a r → TyOutlivesHolds env b r → TyOutlivesHolds env (.pair a b) r
  | adt (id : Nat) (rs : List Region) (ts : TyArgs) (r : Region) :
      (∀ rx, rx ∈ rs → OutlivesHolds env (.region rx) r) →
      (∀ t, t ∈ tyArgsToList ts → TyOutlivesHolds env t r) →
      TyOutlivesHolds env (.adt id rs ts) r
  | projEnv (s : Ty) (tr as : Nat) (rs : List Region) (r : Region) :
      OutlivesHolds env (.proj s tr as rs) r →
      TyOutlivesHolds env (.proj s tr as rs) r
  | projComponents (s : Ty) (tr as : Nat) (rs : List Region) (r : Region) :
      TyOutlivesHolds env s r →
      (∀ rx, rx ∈ rs → OutlivesHolds env (.region rx) r) →
      TyOutlivesHolds env (.proj s tr as rs) r
  | fnBinder (a b : Ty) (r : Region) :
      TyOutlivesHolds env a r → TyOutlivesHolds env b r → TyOutlivesHolds env (.fnBinder a b) r
  | dynObj (tr : Nat) (rs : List Region) (b r : Region) :
      OutlivesHolds env (.region b) r →
      (∀ rx, rx ∈ rs → OutlivesHolds env (.region rx) r) →
      TyOutlivesHolds env (.dynObj tr rs b) r

/-- Declarative well-formedness judgment `adtClauses, traitClauses, env ⊢ ty WF`. -/
inductive TyWF (adtClauses : Nat → List OutlivesBound) (traitClauses : Nat → List OutlivesBound)
    (env : List OutlivesBound) : Ty → Prop where
  | prim : TyWF adtClauses traitClauses env .prim
  | param (idx : Nat) : TyWF adtClauses traitClauses env (.param idx)
  | ref (r : Region) (t : Ty) :
      TyWF adtClauses traitClauses env t →
      TyOutlivesHolds env t r →
      TyWF adtClauses traitClauses env (.ref r t)
  | pair (a b : Ty) :
      TyWF adtClauses traitClauses env a →
      TyWF adtClauses traitClauses env b →
      TyWF adtClauses traitClauses env (.pair a b)
  | adt (id : Nat) (rs : List Region) (ts : TyArgs) :
      (∀ t, t ∈ tyArgsToList ts → TyWF adtClauses traitClauses env t) →
      (∀ b, b ∈ adtClauses id →
        OutlivesHolds env (substTarget rs ts b.lhs) (substRegion rs b.rhs)) →
      TyWF adtClauses traitClauses env (.adt id rs ts)
  | proj (s : Ty) (tr as : Nat) (rs : List Region) :
      TyWF adtClauses traitClauses env s →
      (∀ b, b ∈ traitClauses tr →
        OutlivesHolds env (substTarget rs (.cons s .nil) b.lhs) (substRegion rs b.rhs)) →
      TyWF adtClauses traitClauses env (.proj s tr as rs)
  | fnBinder (a b : Ty) :
      TyWF adtClauses traitClauses env (.fnBinder a b)
  | dynObj (tr : Nat) (rs : List Region) (b : Region) :
      (∀ rx, rx ∈ rs → OutlivesHolds env (.region b) rx) →
      TyWF adtClauses traitClauses env (.dynObj tr rs b)

/-! ## Part 3: RFC 2093 `inferredOutlivesOf` Fixed-Point Algorithm & Theorems -/

/-- Parameterized free-region filter corresponding to `rustc_hir_analysis::outlives::utils::is_free_region`. -/
noncomputable def rfc2093IsFreeRegion : Region → Bool
  | .early _ => true
  | .static => false
  | .late _ => false

/-- Counterfactual filter where `'static` is treated as inferable (`true`), isolating
the exact `E0310` boundary at `outlives/utils.rs:164`. -/
noncomputable def altIsFreeWithStatic : Region → Bool
  | .early _ => true
  | .static => true
  | .late _ => false

structure AdtDecl where
  id : Nat
  explicitOutlives : List OutlivesBound
  fields : List Ty

/-- Models `rustc_hir_analysis::outlives::utils::insert_outlives_clause`. -/
noncomputable def insertOutlivesClause (isFree : Region → Bool)
    (lhs : OutlivesTarget) (rhs : Region) : List OutlivesBound :=
  match isFree rhs with
  | false => []
  | true =>
    match lhs with
    | .region r =>
      match isFree r with
      | true => [{ lhs := .region r, rhs := rhs }]
      | false => []
    | .param i => [{ lhs := .param i, rhs := rhs }]
    | .proj s tr as rs => [{ lhs := .proj s tr as rs, rhs := rhs }]

/-- Component-decomposition wrapper matching `insert_outlives_clause` for `GenericArgKind::Type`. -/
noncomputable def insertOutlivesTy (isFree : Region → Bool)
    (ty : Ty) (rhs : Region) : List OutlivesBound :=
  match isFree rhs with
  | false => []
  | true =>
    (pushOutlivesComponents ty).flatMap fun c =>
      match c with
      | .region r => insertOutlivesClause isFree (.region r) rhs
      | .param i => [{ lhs := .param i, rhs := rhs }]
      | .alias s tr as rs => [{ lhs := .proj s tr as rs, rhs := rhs }]
      | .escapingAlias _ => []

theorem insertOutlivesClause_mem_iff (isFree : Region → Bool)
    (lhs : OutlivesTarget) (rhs : Region) (b : OutlivesBound) :
    b ∈ insertOutlivesClause isFree lhs rhs ↔
      isFree rhs = true ∧
      b = { lhs := lhs, rhs := rhs } ∧
      (∀ r, lhs = .region r → isFree r = true) := by
  unfold insertOutlivesClause
  cases hFree : isFree rhs
  · constructor
    · intro h; cases h
    · intro h; cases h.1
  · cases lhs with
    | region r =>
      change b ∈ (match isFree r with | true => ([{ lhs := .region r, rhs := rhs }] : List OutlivesBound) | false => []) ↔ _
      cases hL : isFree r
      · constructor
        · intro h; cases h
        · intro h; have h2 := h.2.2 r rfl; rw [hL] at h2; cases h2
      · constructor
        · intro h
          cases h with
          | head => exact ⟨rfl, rfl, fun _ he => by cases he; exact hL⟩
          | tail _ h1 => cases h1
        · intro h
          rw [h.2.1]
          exact List.mem_cons_self
    | param i =>
      constructor
      · intro h
        cases h with
        | head => exact ⟨rfl, rfl, fun _ he => by cases he⟩
        | tail _ h1 => cases h1
      · intro h
        rw [h.2.1]
        exact List.mem_cons_self
    | proj s tr as rs =>
      constructor
      · intro h
        cases h with
        | head => exact ⟨rfl, rfl, fun _ he => by cases he⟩
        | tail _ h1 => cases h1
      · intro h
        rw [h.2.1]
        exact List.mem_cons_self

noncomputable def lookupAdtBounds (table : List TaggedBound) (adtId : Nat) : List OutlivesBound :=
  (table.filter (fun tb => Nat.beq tb.adtId adtId)).map (fun tb => tb.bound)

theorem lookupAdtBounds_mono {t1 t2 : List TaggedBound} (hsub : ListSubset t1 t2) (id : Nat) :
    ListSubset (lookupAdtBounds t1 id) (lookupAdtBounds t2 id) := by
  intro b hb
  unfold lookupAdtBounds at hb ⊢
  rw [List.mem_map] at hb ⊢
  obtain ⟨tb, htb, hEq⟩ := hb
  rw [List.mem_filter] at htb
  refine ⟨tb, ?_, hEq⟩
  rw [List.mem_filter]
  exact ⟨hsub tb htb.1, htb.2⟩

noncomputable def checkExplicitBounds (isFree : Region → Bool)
    (rArgs : List Region) (tArgs : TyArgs) (bounds : List OutlivesBound) : List OutlivesBound :=
  bounds.flatMap fun b =>
    let b' := substBound rArgs tArgs b
    insertOutlivesClause isFree b'.lhs b'.rhs

noncomputable def checkInferredBounds (isFree : Region → Bool)
    (table : List TaggedBound) (defId : Nat) (rArgs : List Region) (tArgs : TyArgs) :
    List OutlivesBound :=
  (lookupAdtBounds table defId).flatMap fun b =>
    let b' := substBound rArgs tArgs b
    insertOutlivesClause isFree b'.lhs b'.rhs

theorem checkInferredBounds_mono (isFree : Region → Bool) {t1 t2 : List TaggedBound}
    (hsub : ListSubset t1 t2) (id : Nat) (rs : List Region) (ts : TyArgs) :
    ListSubset (checkInferredBounds isFree t1 id rs ts) (checkInferredBounds isFree t2 id rs ts) := by
  intro b hb
  unfold checkInferredBounds at hb ⊢
  rw [List.mem_flatMap] at hb ⊢
  obtain ⟨x, hx, hbx⟩ := hb
  exact ⟨x, lookupAdtBounds_mono hsub id x hx, hbx⟩

/-- Models `rustc_hir_analysis::outlives::implicit_infer::insert_required_clauses_to_be_wf`.
Notice that:
- `.ref r pointee` calls `insertOutlivesTy` for `pointee: r` AND walks `pointee`
- `.adt id rArgs tArgs` checks BOTH `inferred` clauses from `table` and explicit ADT clauses, plus walks `tArgs`
- `.proj selfTy tr _ rArgs` checks explicit trait bounds only (no impl normalization!) plus walks `selfTy`
- `.dynObj tr rArgs boundR` checks non-Self trait bounds (`IgnoreClausesReferencingSelf::Yes`)
- `.fnBinder arg ret` walks `arg` and `ret` (`isFree (.late _) = false` stops bound lifetimes from leaking). -/
noncomputable def walkTyForClauses (isFree : Region → Bool)
    (table : List TaggedBound) (adtExplicit : Nat → List OutlivesBound)
    (traitExplicit : Nat → List OutlivesBound) : Ty → List OutlivesBound :=
  @Ty.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
    []
    (fun _ => [])
    (fun r p ih => insertOutlivesTy isFree p r ++ ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun id rs ts ihArgs =>
      checkInferredBounds isFree table id rs ts ++
      checkExplicitBounds isFree rs ts (adtExplicit id) ++
      ihArgs)
    (fun s tr _ rs ihS =>
      checkExplicitBounds isFree rs (.cons s .nil) (traitExplicit tr) ++ ihS)
    (fun _ _ ihA ihR => ihA ++ ihR)
    (fun tr rs _ =>
      let nonSelf := (traitExplicit tr).filter fun b =>
        match b.lhs with
        | .param 0 => false
        | _ => true
      checkExplicitBounds isFree rs .nil nonSelf)
    []
    (fun _ _ ihH ihT => ihH ++ ihT)

theorem walkTyForClauses_mono (isFree : Region → Bool)
    (adtExp traitExp : Nat → List OutlivesBound)
    {t1 t2 : List TaggedBound} (hsub : ListSubset t1 t2) :
    (∀ ty : Ty, ListSubset (walkTyForClauses isFree t1 adtExp traitExp ty)
                           (walkTyForClauses isFree t2 adtExp traitExp ty)) := by
  have hBoth :
      (∀ ty : Ty, ListSubset (walkTyForClauses isFree t1 adtExp traitExp ty)
                             (walkTyForClauses isFree t2 adtExp traitExp ty)) ∧
      (∀ ts : TyArgs, ListSubset
        (@TyArgs.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
          [] (fun _ => []) (fun r p ih => insertOutlivesTy isFree p r ++ ih)
          (fun _ _ ih1 ih2 => ih1 ++ ih2)
          (fun id rs ts ihArgs =>
            checkInferredBounds isFree t1 id rs ts ++
            checkExplicitBounds isFree rs ts (adtExp id) ++ ihArgs)
          (fun s tr _ rs ihS => checkExplicitBounds isFree rs (.cons s .nil) (traitExp tr) ++ ihS)
          (fun _ _ ihA ihR => ihA ++ ihR)
          (fun tr rs _ =>
            let nonSelf := (traitExp tr).filter fun b => match b.lhs with | .param 0 => false | _ => true
            checkExplicitBounds isFree rs .nil nonSelf)
          [] (fun _ _ ihH ihT => ihH ++ ihT) ts)
        (@TyArgs.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
          [] (fun _ => []) (fun r p ih => insertOutlivesTy isFree p r ++ ih)
          (fun _ _ ih1 ih2 => ih1 ++ ih2)
          (fun id rs ts ihArgs =>
            checkInferredBounds isFree t2 id rs ts ++
            checkExplicitBounds isFree rs ts (adtExp id) ++ ihArgs)
          (fun s tr _ rs ihS => checkExplicitBounds isFree rs (.cons s .nil) (traitExp tr) ++ ihS)
          (fun _ _ ihA ihR => ihA ++ ihR)
          (fun tr rs _ =>
            let nonSelf := (traitExp tr).filter fun b => match b.lhs with | .param 0 => false | _ => true
            checkExplicitBounds isFree rs .nil nonSelf)
          [] (fun _ _ ihH ihT => ihH ++ ihT) ts)) := by
    apply ty_rec_pair
      (fun ty => ListSubset (walkTyForClauses isFree t1 adtExp traitExp ty)
                             (walkTyForClauses isFree t2 adtExp traitExp ty))
      (fun ts => ListSubset
        (@TyArgs.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
          [] (fun _ => []) (fun r p ih => insertOutlivesTy isFree p r ++ ih)
          (fun _ _ ih1 ih2 => ih1 ++ ih2)
          (fun id rs ts ihArgs =>
            checkInferredBounds isFree t1 id rs ts ++
            checkExplicitBounds isFree rs ts (adtExp id) ++ ihArgs)
          (fun s tr _ rs ihS => checkExplicitBounds isFree rs (.cons s .nil) (traitExp tr) ++ ihS)
          (fun _ _ ihA ihR => ihA ++ ihR)
          (fun tr rs _ =>
            let nonSelf := (traitExp tr).filter fun b => match b.lhs with | .param 0 => false | _ => true
            checkExplicitBounds isFree rs .nil nonSelf)
          [] (fun _ _ ihH ihT => ihH ++ ihT) ts)
        (@TyArgs.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
          [] (fun _ => []) (fun r p ih => insertOutlivesTy isFree p r ++ ih)
          (fun _ _ ih1 ih2 => ih1 ++ ih2)
          (fun id rs ts ihArgs =>
            checkInferredBounds isFree t2 id rs ts ++
            checkExplicitBounds isFree rs ts (adtExp id) ++ ihArgs)
          (fun s tr _ rs ihS => checkExplicitBounds isFree rs (.cons s .nil) (traitExp tr) ++ ihS)
          (fun _ _ ihA ihR => ihA ++ ihR)
          (fun tr rs _ =>
            let nonSelf := (traitExp tr).filter fun b => match b.lhs with | .param 0 => false | _ => true
            checkExplicitBounds isFree rs .nil nonSelf)
          [] (fun _ _ ihH ihT => ihH ++ ihT) ts))
    · exact listSubset_refl _
    · intro idx; exact listSubset_refl _
    · intro r p ih b hb
      change b ∈ insertOutlivesTy isFree p r ++ _ at hb ⊢
      rw [List.mem_append] at hb ⊢
      cases hb with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (ih b h)
    · intro a b ih1 ih2 x hx
      change x ∈ _ ++ _ at hx ⊢
      rw [List.mem_append] at hx ⊢
      cases hx with
      | inl h => exact Or.inl (ih1 x h)
      | inr h => exact Or.inr (ih2 x h)
    · intro id rs ts ihArgs x hx
      change x ∈ checkInferredBounds isFree t1 id rs ts ++
        checkExplicitBounds isFree rs ts (adtExp id) ++ _ at hx
      change x ∈ checkInferredBounds isFree t2 id rs ts ++
        checkExplicitBounds isFree rs ts (adtExp id) ++ _
      rw [List.mem_append] at hx ⊢
      cases hx with
      | inl h1 =>
        rw [List.mem_append] at h1
        cases h1 with
        | inl hinf => exact Or.inl (List.mem_append.mpr (Or.inl (checkInferredBounds_mono isFree hsub id rs ts x hinf)))
        | inr hexp => exact Or.inl (List.mem_append.mpr (Or.inr hexp))
      | inr h2 => exact Or.inr (ihArgs x h2)
    · intro s tr as rs ihS x hx
      change x ∈ checkExplicitBounds isFree rs (.cons s .nil) (traitExp tr) ++ _ at hx ⊢
      rw [List.mem_append] at hx ⊢
      cases hx with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (ihS x h)
    · intro a b ihA ihR x hx
      change x ∈ _ ++ _ at hx ⊢
      rw [List.mem_append] at hx ⊢
      cases hx with
      | inl h => exact Or.inl (ihA x h)
      | inr h => exact Or.inr (ihR x h)
    · intro tr rs b; exact listSubset_refl _
    · exact listSubset_refl _
    · intro h t ihH ihT x hx
      change x ∈ _ ++ _ at hx ⊢
      rw [List.mem_append] at hx ⊢
      cases hx with
      | inl h => exact Or.inl (ihH x h)
      | inr h => exact Or.inr (ihT x h)
  exact hBoth.1

noncomputable def inferAdtStep (isFree : Region → Bool)
    (adtExp traitExp : Nat → List OutlivesBound)
    (table : List TaggedBound) (d : AdtDecl) : List TaggedBound :=
  let fieldBounds := d.fields.flatMap (walkTyForClauses isFree table adtExp traitExp)
  dedupList TaggedBound.beq (fieldBounds.map (fun b => { adtId := d.id, bound := b }))

noncomputable def inferRound (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound)
    (table : List TaggedBound) : List TaggedBound :=
  dedupList TaggedBound.beq (adts.flatMap (inferAdtStep isFree adtExp traitExp table))

noncomputable def inferredOutlivesOf (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound)
    (fuel : Nat) : List TaggedBound :=
  iterFn (inferRound isFree adts adtExp traitExp) fuel []

theorem inferRound_mono (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound)
    {t1 t2 : List TaggedBound} (hsub : ListSubset t1 t2) :
    ListSubset (inferRound isFree adts adtExp traitExp t1)
               (inferRound isFree adts adtExp traitExp t2) := by
  intro tb htb
  unfold inferRound at htb ⊢
  rw [mem_dedupList_iff TaggedBound.beq tagged_beq_refl tagged_beq_eq] at htb ⊢
  rw [List.mem_flatMap] at htb ⊢
  obtain ⟨d, hd, hStep⟩ := htb
  refine ⟨d, hd, ?_⟩
  unfold inferAdtStep at hStep ⊢
  rw [mem_dedupList_iff TaggedBound.beq tagged_beq_refl tagged_beq_eq] at hStep ⊢
  rw [List.mem_map] at hStep ⊢
  obtain ⟨b, hb, hEq⟩ := hStep
  rw [List.mem_flatMap] at hb
  obtain ⟨f, hf, hbf⟩ := hb
  exact ⟨b, List.mem_flatMap.mpr ⟨f, hf, walkTyForClauses_mono isFree adtExp traitExp hsub f b hbf⟩, hEq⟩

theorem inferredOutlivesOf_mono (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound) :
    ∀ m n : Nat, m ≤ n →
      ListSubset (inferredOutlivesOf isFree adts adtExp traitExp m)
                 (inferredOutlivesOf isFree adts adtExp traitExp n) := by
  intro m n hle
  induction hle with
  | refl => exact listSubset_refl _
  | step _ ih =>
    refine listSubset_trans ih ?_
    exact iterFn_mono TaggedBound.beq tagged_beq_refl tagged_beq_eq
      (inferRound isFree adts adtExp traitExp) (fun _ hx => hx)
      (fun h => inferRound_mono isFree adts adtExp traitExp h) _

/-- **Theorem (RFC 2093 Finite-Universe Termination):** Whenever every inferred bound
across `adts` remains inside a finite syntactic universe `univ : List TaggedBound`,
`inferredOutlivesOf` reaches an exact fixed point within `k ≤ univ.length` iterations. -/
theorem rfc2093_fixpoint_terminates (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound)
    (univ : List TaggedBound)
    (hClosed : ∀ s, ListSubset s univ → ListSubset (inferRound isFree adts adtExp traitExp s) univ) :
    ∃ k : Nat, k ≤ univ.length ∧
      ListSubset (inferredOutlivesOf isFree adts adtExp traitExp (Nat.succ k))
                 (inferredOutlivesOf isFree adts adtExp traitExp k) :=
  firstFixpointFuel_terminates TaggedBound.beq tagged_beq_refl tagged_beq_eq
    (inferRound isFree adts adtExp traitExp) univ hClosed
    (fun h => inferRound_mono isFree adts adtExp traitExp h)

/-- **Theorem (RFC 2093 Least Fixed Point):** Any post-fixed point `fp` of `inferRound`
contains `inferredOutlivesOf ... fuel` for every `fuel : Nat`. -/
theorem rfc2093_least_fixpoint (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound)
    (fp : List TaggedBound)
    (hPost : ListSubset (inferRound isFree adts adtExp traitExp fp) fp) :
    ∀ fuel : Nat, ListSubset (inferredOutlivesOf isFree adts adtExp traitExp fuel) fp := by
  intro fuel
  induction fuel with
  | zero => intro _ hx; cases hx
  | succ k ih =>
    exact listSubset_trans (inferRound_mono isFree adts adtExp traitExp ih) hPost

/-- Syntactic completeness invariant for an ADT field w.r.t. inferred free-region clauses:
if `fp` is a fixed point (`inferRound fp ⊆ fp`), then for every `d ∈ adts` and `f ∈ d.fields`,
every clause produced by `walkTyForClauses` (direct `&'r T` fields, transitive ADT fields,
projection trait clauses, and non-`Self` dyn bounds) is already stored in `lookupAdtBounds fp d.id`. -/
theorem rfc2093_fixpoint_field_complete (isFree : Region → Bool)
    (adts : List AdtDecl) (adtExp traitExp : Nat → List OutlivesBound)
    (fp : List TaggedBound)
    (hFix : ListSubset (inferRound isFree adts adtExp traitExp fp) fp) :
    ∀ d, d ∈ adts → ∀ f, f ∈ d.fields →
      ∀ b, b ∈ walkTyForClauses isFree fp adtExp traitExp f →
        b ∈ lookupAdtBounds fp d.id := by
  intro d hd f hf b hb
  have hTagInRound : { adtId := d.id, bound := b } ∈ inferRound isFree adts adtExp traitExp fp := by
    unfold inferRound
    rw [mem_dedupList_iff TaggedBound.beq tagged_beq_refl tagged_beq_eq]
    rw [List.mem_flatMap]
    refine ⟨d, hd, ?_⟩
    unfold inferAdtStep
    rw [mem_dedupList_iff TaggedBound.beq tagged_beq_refl tagged_beq_eq]
    rw [List.mem_map]
    exact ⟨b, List.mem_flatMap.mpr ⟨f, hf, hb⟩, rfl⟩
  have hTagInFp : { adtId := d.id, bound := b } ∈ fp := hFix _ hTagInRound
  unfold lookupAdtBounds
  rw [List.mem_map]
  refine ⟨{ adtId := d.id, bound := b }, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hTagInFp, Nat.beq_refl d.id⟩

/-- Unbounded growth witness explaining why `rustc_hir_analysis::outlives::implicit_infer`
guards `infer_predicates` with `tcx.recursion_limit()` (`implicit_infer.rs:92-104`):
iterating type wrapper `Ty.ref (.early 0)` adds `+1` to `tySize` at every step. -/
noncomputable def nestedRefChain (n : Nat) : Ty :=
  @Nat.rec (fun _ => Ty) (.param 0) (fun _ acc => .ref (.early 0) acc) n

theorem nestedRefChain_size (n : Nat) : tySize (nestedRefChain n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change tySize (nestedRefChain k) + 1 = Nat.succ k + 1
    rw [ih]

/-! ## Part 4: `ReStatic` Exclusion Separation (`E0310`) & Projection vs. Param Separation (`E0309`) -/

theorem insertOutlivesClause_rfc2093_static_empty (lhs : OutlivesTarget) :
    insertOutlivesClause rfc2093IsFreeRegion lhs .static = [] := rfl

theorem insertOutlivesTy_rfc2093_static_empty (ty : Ty) :
    insertOutlivesTy rfc2093IsFreeRegion ty .static = [] := rfl

theorem rfc2093_never_emits_static_rhs (lhs : OutlivesTarget) (rhs : Region) (b : OutlivesBound) :
    b ∈ insertOutlivesClause rfc2093IsFreeRegion lhs rhs → b.rhs ≠ .static := by
  intro hb hStat
  rw [insertOutlivesClause_mem_iff] at hb
  rcases hb with ⟨hFree, hEq, _⟩
  rw [hEq] at hStat
  have hStat' : rhs = .static := hStat
  rw [hStat'] at hFree
  cases hFree

/-- Witness ADT for `struct StaticRef<T>(&'static T)` (no explicit bounds). -/
noncomputable def staticRefAdt : AdtDecl :=
  { id := 1, explicitOutlives := [], fields := [.ref .static (.param 0)] }

/-- Witness ADT for `struct StaticRef<T: 'static>(&'static T)`. -/
noncomputable def staticRefExplicitBounds : Nat → List OutlivesBound
  | 1 => [{ lhs := .param 0, rhs := .static }]
  | _ => []

theorem staticRef_inferred_empty_all_fuel (fuel : Nat) :
    inferredOutlivesOf rfc2093IsFreeRegion [staticRefAdt] (fun _ => []) (fun _ => []) fuel = [] := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    change inferRound rfc2093IsFreeRegion [staticRefAdt] (fun _ => []) (fun _ => [])
      (inferredOutlivesOf rfc2093IsFreeRegion [staticRefAdt] (fun _ => []) (fun _ => []) k) = []
    rw [ih]
    rfl

theorem outlivesHolds_nonregion_in_env {env : List OutlivesBound} {t : OutlivesTarget} {r : Region}
    (h : OutlivesHolds env t r) :
    (∃ rk, t = .region rk) ∨ (∃ b, b ∈ env ∧ b.lhs = t) := by
  induction h with
  | refl r0 => exact Or.inl ⟨r0, rfl⟩
  | staticTop _ _ _ ih => exact ih
  | staticOutlives _ => exact Or.inl ⟨.static, rfl⟩
  | assume b hb => exact Or.inr ⟨b, hb, rfl⟩
  | trans _ _ ih1 _ => exact ih1

theorem empty_env_no_param_outlives (idx : Nat) (r : Region) :
    ¬ OutlivesHolds [] (.param idx) r := by
  intro h
  cases outlivesHolds_nonregion_in_env h with
  | inl hr => obtain ⟨_, he⟩ := hr; cases he
  | inr hb => obtain ⟨_, hmem, _⟩ := hb; cases hmem

theorem empty_env_no_proj_outlives (s : Ty) (tr as : Nat) (rs : List Region) (r : Region) :
    ¬ OutlivesHolds [] (.proj s tr as rs) r := by
  intro h
  cases outlivesHolds_nonregion_in_env h with
  | inl hr => obtain ⟨_, he⟩ := hr; cases he
  | inr hb => obtain ⟨_, hmem, _⟩ := hb; cases hmem

theorem staticRef_wf_fails_without_explicit_e0310 :
    ¬ TyWF (fun _ => []) (fun _ => []) [] (.ref .static (.param 0)) := by
  intro hwf
  cases hwf with
  | ref _ _ _ hOut =>
    cases hOut with
    | param _ _ hParam => exact empty_env_no_param_outlives 0 .static hParam

theorem staticRef_explicit_wf_ok :
    TyWF staticRefExplicitBounds (fun _ => [])
      (staticRefExplicitBounds 1) (.ref .static (.param 0)) := by
  apply TyWF.ref
  · exact TyWF.param 0
  · apply TyOutlivesHolds.param
    exact OutlivesHolds.assume { lhs := .param 0, rhs := .static } List.mem_cons_self

theorem staticRef_inferred_when_static_is_free :
    inferredOutlivesOf altIsFreeWithStatic [staticRefAdt] (fun _ => []) (fun _ => []) 1 =
      [{ adtId := 1, bound := { lhs := .param 0, rhs := .static } }] := rfl

/-- Witness ADT for `struct FnHolder<T>(for<'b> fn(&'b T))`. -/
noncomputable def fnHolderAdt : AdtDecl :=
  { id := 2, explicitOutlives := [], fields := [.fnBinder (.ref (.late 0) (.param 0)) .prim] }

theorem fnHolder_inferred_empty_all_fuel (fuel : Nat) :
    inferredOutlivesOf rfc2093IsFreeRegion [fnHolderAdt] (fun _ => []) (fun _ => []) fuel = [] := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    change inferRound rfc2093IsFreeRegion [fnHolderAdt] (fun _ => []) (fun _ => [])
      (inferredOutlivesOf rfc2093IsFreeRegion [fnHolderAdt] (fun _ => []) (fun _ => []) k) = []
    rw [ih]
    rfl

/-- Escaping late-bound projection falls back to `Component.escapingAlias`. -/
theorem pushOutlivesComponents_late_proj_escaping :
    pushOutlivesComponents (.proj (.ref (.late 0) (.param 0)) 10 0 [.early 0]) =
      [Component.escapingAlias [Component.param 0, Component.region (.early 0)]] := rfl

/-- Witness ADT for `struct Wrap<'a, T: Id>(&'a <T as Id>::Out)`. -/
noncomputable def wrapProjAdt : AdtDecl :=
  { id := 3, explicitOutlives := [], fields := [.ref (.early 0) (.proj (.param 0) 10 0 [])] }

theorem wrapProj_inferred_proj_only (fuel : Nat) :
    inferredOutlivesOf rfc2093IsFreeRegion [wrapProjAdt] (fun _ => []) (fun _ => []) (Nat.succ fuel) =
      [{ adtId := 3, bound := { lhs := .proj (.param 0) 10 0 [], rhs := .early 0 } }] := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    change inferRound rfc2093IsFreeRegion [wrapProjAdt] (fun _ => []) (fun _ => [])
      (inferredOutlivesOf rfc2093IsFreeRegion [wrapProjAdt] (fun _ => []) (fun _ => []) (Nat.succ k)) =
      [{ adtId := 3, bound := { lhs := .proj (.param 0) 10 0 [], rhs := .early 0 } }]
    rw [ih]
    rfl

theorem wrapProj_never_infers_param_e0309 :
    ¬ OutlivesHolds
        (lookupAdtBounds
          (inferredOutlivesOf rfc2093IsFreeRegion [wrapProjAdt] (fun _ => []) (fun _ => []) 1) 3)
        (.param 0) (.early 0) := by
  intro h
  have hin : lookupAdtBounds
      (inferredOutlivesOf rfc2093IsFreeRegion [wrapProjAdt] (fun _ => []) (fun _ => []) 1) 3 =
      [{ lhs := .proj (.param 0) 10 0 [], rhs := .early 0 }] := rfl
  rw [hin] at h
  cases outlivesHolds_nonregion_in_env h with
  | inl hr => obtain ⟨_, he⟩ := hr; cases he
  | inr hb =>
    obtain ⟨b, hm, hlhs⟩ := hb
    cases hm with
    | head => cases hlhs
    | tail _ hnil => cases hnil

/-- Witness ADT for `struct Holder<'a, T>(<Vec<T> as MakeRef<'a>>::Type)` (RFC 2093 Example 4):
without explicit trait outlives on `MakeRef`, projection is never normalized through trait impls. -/
noncomputable def holderProjAdt : AdtDecl :=
  { id := 4
    explicitOutlives := []
    fields := [.proj (.adt 99 [] (.cons (.param 0) .nil)) 11 0 [.early 0]] }

theorem holderProj_no_impl_norm_empty_all_fuel (fuel : Nat) :
    inferredOutlivesOf rfc2093IsFreeRegion [holderProjAdt] (fun _ => []) (fun _ => []) fuel = [] := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    change inferRound rfc2093IsFreeRegion [holderProjAdt] (fun _ => []) (fun _ => [])
      (inferredOutlivesOf rfc2093IsFreeRegion [holderProjAdt] (fun _ => []) (fun _ => []) k) = []
    rw [ih]
    rfl

/-- Mutually / transitively nested ADTs `Outer<'a, T>(Mid<'a, T>)`, `Mid<'a, T>(Leaf<'a, T>)`,
`Leaf<'a, T>(&'a T)` converge to a fixed point by step 3 (`step 4 = step 3`). -/
noncomputable def nestedAdts : List AdtDecl :=
  [ { id := 10, explicitOutlives := [], fields := [.adt 11 [.early 0] (.cons (.param 0) .nil)] }
  , { id := 11, explicitOutlives := [], fields := [.adt 12 [.early 0] (.cons (.param 0) .nil)] }
  , { id := 12, explicitOutlives := [], fields := [.ref (.early 0) (.param 0)] } ]

theorem nestedAdts_converge_at_three :
    inferredOutlivesOf rfc2093IsFreeRegion nestedAdts (fun _ => []) (fun _ => []) 4 =
      inferredOutlivesOf rfc2093IsFreeRegion nestedAdts (fun _ => []) (fun _ => []) 3 := rfl

theorem nestedAdts_outer_receives_leaf_bound :
    { adtId := 10, bound := { lhs := .param 0, rhs := .early 0 } } ∈
      inferredOutlivesOf rfc2093IsFreeRegion nestedAdts (fun _ => []) (fun _ => []) 3 := by
  exact List.mem_cons_self

/-! ## Part 5: Signature `assumed_wf_types`, Implied Outlives Environment, and Soundness Partition -/

/-- Item-kind partition matching `rustc_ty_utils::implied_bounds::assumed_wf_types`.
Critically, `fnDef` assumes all signature input+output types, `traitImpl` assumes `Self` + trait
type arguments, `inherentImpl` assumes `Self`, while `assocTy` only assumes parent impl types
(NEVER its own RHS) and `adtItem` / `traitDef` assume nothing (`[]`). -/
inductive ItemKind where
  | fnDef (inputsAndOutput : List Ty)
  | traitImpl (selfTy : Ty) (traitArgs : List Ty)
  | inherentImpl (selfTy : Ty)
  | assocTy (parentAssumedWf : List Ty) (rhsTy : Ty)
  | adtItem (fields : List Ty)
  | traitDef (params : List Ty)

noncomputable def assumedWfTypes : ItemKind → List Ty
  | .fnDef sigTys => sigTys
  | .traitImpl selfTy traitArgs => selfTy :: traitArgs
  | .inherentImpl selfTy => [selfTy]
  | .assocTy parentTys _ => parentTys
  | .adtItem _ => []
  | .traitDef _ => []

/-- Auxiliary trait predicate representation modeling `ClauseKind::Trait` obligations on types
which are checked by WF (`wfcheck`) yet NEVER added by `compute_implied_outlives_bounds_inner`. -/
structure TraitObligation where
  ty : Ty
  traitId : Nat

/-- Syntactic outlives extraction matching `compute_implied_outlives_bounds_inner` / `TypeOutlives`
across `Ty` and `TyArgs`. Notice NO `rfc2093IsFreeRegion` filter is applied here: both `'early`
and `'static` outlives bounds are extracted from assumed-WF types (`fn_static` works!). -/
noncomputable def extractTypeOutlives (ty : Ty) (r : Region) : List OutlivesBound :=
  @Ty.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
    []
    (fun idx => [{ lhs := .param idx, rhs := r }])
    (fun rx _ ih => { lhs := .region rx, rhs := r } :: ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun _ rs _ ihArgs => rs.map (fun rx => { lhs := .region rx, rhs := r }) ++ ihArgs)
    (fun s tr as rs ihS =>
      match tyHasLate s || rs.any regionIsLate with
      | true => ihS ++ rs.map (fun rx => { lhs := .region rx, rhs := r })
      | false => [{ lhs := .proj s tr as rs, rhs := r }])
    (fun _ _ ihA ihR => ihA ++ ihR)
    (fun _ rs b => { lhs := .region b, rhs := r } :: rs.map (fun rx => { lhs := .region rx, rhs := r }))
    []
    (fun _ _ ihH ihT => ihH ++ ihT)
    ty

noncomputable def extractTypeOutlivesArgs (ts : TyArgs) (r : Region) : List OutlivesBound :=
  @TyArgs.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
    []
    (fun idx => [{ lhs := .param idx, rhs := r }])
    (fun rx _ ih => { lhs := .region rx, rhs := r } :: ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun _ rs _ ihArgs => rs.map (fun rx => { lhs := .region rx, rhs := r }) ++ ihArgs)
    (fun s tr as rs ihS =>
      match tyHasLate s || rs.any regionIsLate with
      | true => ihS ++ rs.map (fun rx => { lhs := .region rx, rhs := r })
      | false => [{ lhs := .proj s tr as rs, rhs := r }])
    (fun _ _ ihA ihR => ihA ++ ihR)
    (fun _ rs b => { lhs := .region b, rhs := r } :: rs.map (fun rx => { lhs := .region rx, rhs := r }))
    []
    (fun _ _ ihH ihT => ihH ++ ihT)
    ts

/-- Soundness of `extractTypeOutlives`: whenever an environment `env` satisfies every bound in
`extractTypeOutlives ty r`, `TyOutlivesHolds env ty r` holds declaratively. -/
theorem extractTypeOutlives_sound (env : List OutlivesBound) (r : Region) :
    (∀ ty : Ty, (∀ b, b ∈ extractTypeOutlives ty r → b ∈ env) → TyOutlivesHolds env ty r) ∧
    (∀ ts : TyArgs, (∀ b, b ∈ extractTypeOutlivesArgs ts r → b ∈ env) →
      ∀ t, t ∈ tyArgsToList ts → TyOutlivesHolds env t r) := by
  apply ty_rec_pair
    (fun ty => (∀ b, b ∈ extractTypeOutlives ty r → b ∈ env) → TyOutlivesHolds env ty r)
    (fun ts => (∀ b, b ∈ extractTypeOutlivesArgs ts r → b ∈ env) →
      ∀ t, t ∈ tyArgsToList ts → TyOutlivesHolds env t r)
  · intro _; exact TyOutlivesHolds.prim r
  · intro idx h
    apply TyOutlivesHolds.param
    exact OutlivesHolds.assume { lhs := .param idx, rhs := r } (h _ List.mem_cons_self)
  · intro rx p ih h
    apply TyOutlivesHolds.ref
    · exact OutlivesHolds.assume { lhs := .region rx, rhs := r } (h _ List.mem_cons_self)
    · exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
  · intro a b ihA ihB h
    apply TyOutlivesHolds.pair
    · exact ihA (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
    · exact ihB (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
  · intro id rs ts ihArgs h
    apply TyOutlivesHolds.adt
    · intro rx hrx
      exact OutlivesHolds.assume { lhs := .region rx, rhs := r }
        (h _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨rx, hrx, rfl⟩))))
    · exact ihArgs (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
  · intro s tr as rs ihS h
    change (∀ b, b ∈ (match tyHasLate s || rs.any regionIsLate with
      | true => (extractTypeOutlives s r ++ rs.map (fun rx => ({ lhs := .region rx, rhs := r } : OutlivesBound)) : List OutlivesBound)
      | false => ([{ lhs := .proj s tr as rs, rhs := r }] : List OutlivesBound)) → b ∈ env) at h
    cases hLate : (tyHasLate s || rs.any regionIsLate)
    · rw [hLate] at h
      apply TyOutlivesHolds.projEnv
      exact OutlivesHolds.assume { lhs := .proj s tr as rs, rhs := r } (h _ List.mem_cons_self)
    · rw [hLate] at h
      apply TyOutlivesHolds.projComponents
      · exact ihS (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
      · intro rx hrx
        exact OutlivesHolds.assume { lhs := .region rx, rhs := r }
          (h _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨rx, hrx, rfl⟩))))
  · intro a b ihA ihB h
    apply TyOutlivesHolds.fnBinder
    · exact ihA (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
    · exact ihB (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
  · intro tr rs b h
    apply TyOutlivesHolds.dynObj
    · exact OutlivesHolds.assume { lhs := .region b, rhs := r } (h _ List.mem_cons_self)
    · intro rx hrx
      exact OutlivesHolds.assume { lhs := .region rx, rhs := r }
        (h _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨rx, hrx, rfl⟩)))
  · intro _ _ ht; cases ht
  · intro hd tl ihH ihT h t ht
    change t ∈ hd :: tyArgsToList tl at ht
    cases ht with
    | head => exact ihH (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
    | tail _ htl => exact ihT (fun x hx => h x (List.mem_append.mpr (Or.inr hx))) t htl

/-- Collects all outlives obligations required for `TyWF` of an assumed-WF type (`wfcheck` +
`compute_implied_outlives_bounds_inner`), excluding `ClauseKind::Trait`. -/
noncomputable def wfImpliedOutlives (adtClauses traitClauses : Nat → List OutlivesBound)
    (ty : Ty) : List OutlivesBound :=
  @Ty.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
    []
    (fun _ => [])
    (fun r p ih => extractTypeOutlives p r ++ ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun id rs _ ihArgs => (adtClauses id).map (substBound rs .nil) ++ ihArgs)
    (fun s tr _ rs ihS => (traitClauses tr).map (substBound rs (.cons s .nil)) ++ ihS)
    (fun _ _ _ _ => [])
    (fun _ rs b => rs.map (fun rx => { lhs := .region b, rhs := rx }))
    []
    (fun _ _ ihH ihT => ihH ++ ihT)
    ty

-- Note: For ADT args `ts` inside `.adt id rs ts`, pass `ts` cleanly in `substBound rs ts`:
noncomputable def wfImpliedOutlivesFull (adtClauses traitClauses : Nat → List OutlivesBound)
    (ty : Ty) : List OutlivesBound :=
  @Ty.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
    []
    (fun _ => [])
    (fun r p ih => extractTypeOutlives p r ++ ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun id rs ts ihArgs => (adtClauses id).map (substBound rs ts) ++ ihArgs)
    (fun s tr _ rs ihS => (traitClauses tr).map (substBound rs (.cons s .nil)) ++ ihS)
    (fun _ _ _ _ => [])
    (fun _ rs b => rs.map (fun rx => { lhs := .region b, rhs := rx }))
    []
    (fun _ _ ihH ihT => ihH ++ ihT)
    ty

noncomputable def wfImpliedOutlivesArgs (adtClauses traitClauses : Nat → List OutlivesBound)
    (ts : TyArgs) : List OutlivesBound :=
  @TyArgs.rec (fun _ => List OutlivesBound) (fun _ => List OutlivesBound)
    []
    (fun _ => [])
    (fun r p ih => extractTypeOutlives p r ++ ih)
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun id rs ts0 ihArgs => (adtClauses id).map (substBound rs ts0) ++ ihArgs)
    (fun s tr _ rs ihS => (traitClauses tr).map (substBound rs (.cons s .nil)) ++ ihS)
    (fun _ _ _ _ => [])
    (fun _ rs b => rs.map (fun rx => { lhs := .region b, rhs := rx }))
    []
    (fun _ _ ihH ihT => ihH ++ ihT)
    ts

/-- Soundness of `wfImpliedOutlivesFull`: if `env` contains every outlives bound extracted by
`wfImpliedOutlivesFull`, then `TyWF` holds declaratively for `ty`. -/
theorem wfImpliedOutlivesFull_sound (adtClauses traitClauses : Nat → List OutlivesBound)
    (env : List OutlivesBound) :
    (∀ ty : Ty, (∀ b, b ∈ wfImpliedOutlivesFull adtClauses traitClauses ty → b ∈ env) →
      TyWF adtClauses traitClauses env ty) ∧
    (∀ ts : TyArgs, (∀ b, b ∈ wfImpliedOutlivesArgs adtClauses traitClauses ts → b ∈ env) →
      ∀ t, t ∈ tyArgsToList ts → TyWF adtClauses traitClauses env t) := by
  apply ty_rec_pair
    (fun ty => (∀ b, b ∈ wfImpliedOutlivesFull adtClauses traitClauses ty → b ∈ env) →
      TyWF adtClauses traitClauses env ty)
    (fun ts => (∀ b, b ∈ wfImpliedOutlivesArgs adtClauses traitClauses ts → b ∈ env) →
      ∀ t, t ∈ tyArgsToList ts → TyWF adtClauses traitClauses env t)
  · intro _; exact TyWF.prim
  · intro idx _; exact TyWF.param idx
  · intro r p ih h
    apply TyWF.ref
    · exact ih (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
    · exact (extractTypeOutlives_sound env r).1 p (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
  · intro a b ihA ihB h
    apply TyWF.pair
    · exact ihA (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
    · exact ihB (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
  · intro id rs ts ihArgs h
    apply TyWF.adt
    · exact ihArgs (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
    · intro b hb
      have hin := h (substBound rs ts b) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨b, hb, rfl⟩)))
      exact OutlivesHolds.assume (substBound rs ts b) hin
  · intro s tr as rs ihS h
    apply TyWF.proj
    · exact ihS (fun x hx => h x (List.mem_append.mpr (Or.inr hx)))
    · intro b hb
      have hin := h (substBound rs (.cons s .nil) b)
        (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨b, hb, rfl⟩)))
      exact OutlivesHolds.assume (substBound rs (.cons s .nil) b) hin
  · intro a b _ _ _; exact TyWF.fnBinder a b
  · intro tr rs b h
    apply TyWF.dynObj
    intro rx hrx
    exact OutlivesHolds.assume { lhs := .region b, rhs := rx } (h _ (List.mem_map.mpr ⟨rx, hrx, rfl⟩))
  · intro _ _ ht; cases ht
  · intro hd tl ihH ihT h t ht
    change t ∈ hd :: tyArgsToList tl at ht
    cases ht with
    | head => exact ihH (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
    | tail _ htl => exact ihT (fun x hx => h x (List.mem_append.mpr (Or.inr hx))) t htl

noncomputable def computeImpliedOutlivesEnv (adtClauses traitClauses : Nat → List OutlivesBound)
    (item : ItemKind) : List OutlivesBound :=
  (assumedWfTypes item).flatMap (wfImpliedOutlivesFull adtClauses traitClauses)

/-- **Theorem (Implied-Bounds Soundness):** Assuming WF of an item's `assumed_wf_types` safely
implies `TyWF` for every type in `assumed_wf_types` inside `computeImpliedOutlivesEnv`. -/
theorem implied_bounds_soundness (adtClauses traitClauses : Nat → List OutlivesBound)
    (item : ItemKind) :
    ∀ ty, ty ∈ assumedWfTypes item →
      TyWF adtClauses traitClauses (computeImpliedOutlivesEnv adtClauses traitClauses item) ty := by
  intro ty hty
  apply (wfImpliedOutlivesFull_sound adtClauses traitClauses
    (computeImpliedOutlivesEnv adtClauses traitClauses item)).1 ty
  intro b hb
  unfold computeImpliedOutlivesEnv
  exact List.mem_flatMap.mpr ⟨ty, hty, hb⟩

/-- Every required outlives obligation of an assumed-WF type is discharged inside the caller/impl env. -/
theorem callee_outlives_discharged (adtClauses traitClauses : Nat → List OutlivesBound)
    (item : ItemKind) (ty : Ty) (hty : ty ∈ assumedWfTypes item) :
    ∀ b, b ∈ wfImpliedOutlivesFull adtClauses traitClauses ty →
      OutlivesHolds (computeImpliedOutlivesEnv adtClauses traitClauses item) b.lhs b.rhs := by
  intro b hb
  apply OutlivesHolds.assume b
  unfold computeImpliedOutlivesEnv
  exact List.mem_flatMap.mpr ⟨ty, hty, hb⟩

/-- Witness 1 (`fn f<T>(&'static T) { need_static::<T>(); }`): succeeds (`'static` IS implied)! -/
theorem fn_static_ref_implies_param_static :
    OutlivesHolds
      (computeImpliedOutlivesEnv (fun _ => []) (fun _ => [])
        (.fnDef [.ref .static (.param 0)]))
      (.param 0) .static := by
  apply OutlivesHolds.assume { lhs := .param 0, rhs := .static }
  exact List.mem_cons_self

/-- Witness 2 (`impl<T> Tr for &'static T`): succeeds (`trait_ref.args.types()` includes `&'static T`)! -/
theorem trait_impl_static_ref_implies_param_static :
    OutlivesHolds
      (computeImpliedOutlivesEnv (fun _ => []) (fun _ => [])
        (.traitImpl (.ref .static (.param 0)) []))
      (.param 0) .static := by
  apply OutlivesHolds.assume { lhs := .param 0, rhs := .static }
  exact List.mem_cons_self

/-- Witness 3 (`impl<'a, T> Ref<'a, T>`): inherent impl inherits RFC 2093 inferred `T: 'a`. -/
noncomputable def refInferredClauses : Nat → List OutlivesBound
  | 1 => [{ lhs := .param 0, rhs := .early 0 }]
  | _ => []

theorem inherent_impl_ref_inherits_rfc2093 :
    OutlivesHolds
      (computeImpliedOutlivesEnv refInferredClauses (fun _ => [])
        (.inherentImpl (.adt 1 [.early 0] (.cons (.param 0) .nil))))
      (.param 0) (.early 0) := by
  apply OutlivesHolds.assume { lhs := .param 0, rhs := .early 0 }
  exact List.mem_cons_self

/-- Witness 4 (`impl<'a, T> Assoc<'a, T> for S { type Out = &'a T; }`): `assumed_wf_types(assocTy)`
ONLY checks parent types (`[S] = [.prim]`), excluding RHS `&'a T`, leaving `T: 'a` unprovable (`E0309`). -/
theorem assoc_ty_rhs_not_assumed_wf_e0309 :
    ¬ TyWF (fun _ => []) (fun _ => [])
        (computeImpliedOutlivesEnv (fun _ => []) (fun _ => [])
          (.assocTy [.prim] (.ref (.early 0) (.param 0))))
        (.ref (.early 0) (.param 0)) := by
  have he : computeImpliedOutlivesEnv (fun _ => []) (fun _ => [])
      (.assocTy [.prim] (.ref (.early 0) (.param 0))) = [] := rfl
  rw [he]
  intro hwf
  cases hwf with
  | ref _ _ _ hOut =>
    cases hOut with
    | param _ _ hParam => exact empty_env_no_param_outlives 0 (.early 0) hParam

/-- Witness 5 (`struct NeedEq<T: PartialEq>(T); impl<T> NeedEq<T>`): trait obligations on ADTs
are NOT outlives clauses, so `computeImpliedOutlivesEnv` is empty (`[]`), forcing `E0277`. -/
noncomputable def needEqTraitObligations : Nat → List TraitObligation
  | 20 => [{ ty := .param 0, traitId := 500 }]
  | _ => []

theorem struct_where_trait_bound_not_in_implied_env_e0277 :
    computeImpliedOutlivesEnv (fun _ => []) (fun _ => [])
      (.inherentImpl (.adt 20 [] (.cons (.param 0) .nil))) = [] ∧
    (needEqTraitObligations 20).length = 1 := ⟨rfl, rfl⟩

/-! ## Part 6: Supertrait Elaboration & `PredicateFilter::SelfAndAssociatedTypeBounds` Asymmetry -/

/-- Positive clauses processed by `rustc_type_ir::elaborate::Elaborator`. -/
inductive Clause where
  | trait (traitId : Nat) (selfTy : Ty) (rArgs : List Region) (tArgs : TyArgs)
  | outlives (bound : OutlivesBound)
  | projEq (selfTy : Ty) (traitId : Nat) (assocId : Nat) (rArgs : List Region) (rhs : Ty)

noncomputable def Clause.beq : Clause → Clause → Bool
  | .trait tr1 s1 rs1 ts1, .trait tr2 s2 rs2 ts2 =>
    Nat.beq tr1 tr2 && tyBeq s1 s2 && regionListBeq rs1 rs2 && tyArgsBeq ts1 ts2
  | .outlives b1, .outlives b2 => OutlivesBound.beq b1 b2
  | .projEq s1 tr1 as1 rs1 rhs1, .projEq s2 tr2 as2 rs2 rhs2 =>
    tyBeq s1 s2 && Nat.beq tr1 tr2 && Nat.beq as1 as2 && regionListBeq rs1 rs2 && tyBeq rhs1 rhs2
  | _, _ => false

theorem clause_beq_refl (c : Clause) : Clause.beq c c = true := by
  cases c with
  | trait tr s rs ts =>
    change (((Nat.beq tr tr && tyBeq s s) && regionListBeq rs rs) && tyArgsBeq ts ts) = true
    rw [Nat.beq_refl tr, tyBeq_refl s, regionListBeq_refl rs, tyArgsBeq_refl ts]; rfl
  | outlives b => exact bound_beq_refl b
  | projEq s tr as rs rhs =>
    change ((((tyBeq s s && Nat.beq tr tr) && Nat.beq as as) && regionListBeq rs rs) && tyBeq rhs rhs) = true
    rw [tyBeq_refl s, Nat.beq_refl tr, Nat.beq_refl as, regionListBeq_refl rs, tyBeq_refl rhs]; rfl

theorem clause_beq_eq {c1 c2 : Clause} (h : Clause.beq c1 c2 = true) : c1 = c2 := by
  cases c1 <;> cases c2
  · have h1 := bool_and_eq_true h
    have h2 := bool_and_eq_true h1.1
    have h3 := bool_and_eq_true h2.1
    have htr := Nat.eq_of_beq_eq_true h3.1
    have hs := tyBeq_eq h3.2
    have hrs := regionListBeq_eq h2.2
    have hts := tyBeq_eq_both.2 _ _ h1.2
    subst htr; subst hs; subst hrs; subst hts; rfl
  · cases h
  · cases h
  · cases h
  · exact congrArg Clause.outlives (bound_beq_eq h)
  · cases h
  · cases h
  · cases h
  · have h1 := bool_and_eq_true h
    have h2 := bool_and_eq_true h1.1
    have h3 := bool_and_eq_true h2.1
    have h4 := bool_and_eq_true h3.1
    have hs := tyBeq_eq h4.1
    have htr := Nat.eq_of_beq_eq_true h4.2
    have has := Nat.eq_of_beq_eq_true h3.2
    have hrs := regionListBeq_eq h2.2
    have hrhs := tyBeq_eq h1.2
    subst hs; subst htr; subst has; subst hrs; subst hrhs; rfl

noncomputable def substClause (rEnv : List Region) (tEnv : TyArgs) : Clause → Clause
  | .trait tr s rs ts => .trait tr (substTy rEnv tEnv s) (rs.map (substRegion rEnv)) (substTyArgs rEnv tEnv ts)
  | .outlives b => .outlives (substBound rEnv tEnv b)
  | .projEq s tr as rs rhs =>
    .projEq (substTy rEnv tEnv s) tr as (rs.map (substRegion rEnv)) (substTy rEnv tEnv rhs)

/-- Models `rustc_hir_analysis::collect::predicates_of::PredicateFilter` / `ClauseFilter`:
- `onlySelf`: supertrait bounds on `Self` (`Param 0`) only
- `selfAndAssoc`: traits use `SelfAndAssociatedTypeBounds`, including `Self` and `Self::Assoc`
  while EXCLUDING other type parameters `T` (`Param 1`, etc.)
- `all`: trait aliases use `All`, including `T: 'a` bounds on non-`Self` parameters. -/
inductive ElabFilter where
  | onlySelf
  | selfAndAssoc
  | all

noncomputable def targetIsSelf : OutlivesTarget → Bool
  | .param 0 => true
  | _ => false

noncomputable def targetIsSelfOrAssoc : OutlivesTarget → Bool
  | .param 0 => true
  | .proj (.param 0) _ _ _ => true
  | _ => false

noncomputable def clauseMatchesFilter (f : ElabFilter) (c : Clause) : Bool :=
  match f with
  | .all => true
  | .onlySelf =>
    match c with
    | .trait _ (.param 0) _ _ => true
    | .outlives b => targetIsSelf b.lhs
    | .projEq (.param 0) _ _ _ _ => true
    | _ => false
  | .selfAndAssoc =>
    match c with
    | .trait _ (.param 0) _ _ => true
    | .outlives b => targetIsSelfOrAssoc b.lhs
    | .projEq (.param 0) _ _ _ _ => true
    | _ => false

noncomputable def expandClause (traitSupers : Nat → List Clause) (f : ElabFilter) : Clause → List Clause
  | .trait tr s rs ts =>
    ((traitSupers tr).filter (clauseMatchesFilter f)).map (substClause rs (.cons s ts))
  | _ => []

noncomputable def elabRound (traitSupers : Nat → List Clause) (f : ElabFilter)
    (roots cur : List Clause) : List Clause :=
  dedupList Clause.beq (roots ++ cur ++ cur.flatMap (expandClause traitSupers f))

noncomputable def elaborate (traitSupers : Nat → List Clause) (f : ElabFilter)
    (roots : List Clause) (fuel : Nat) : List Clause :=
  iterFn (elabRound traitSupers f roots) fuel []

theorem elabRound_mono (traitSupers : Nat → List Clause) (f : ElabFilter) (roots : List Clause)
    {s1 s2 : List Clause} (hsub : ListSubset s1 s2) :
    ListSubset (elabRound traitSupers f roots s1) (elabRound traitSupers f roots s2) := by
  intro c hc
  unfold elabRound at hc ⊢
  rw [mem_dedupList_iff Clause.beq clause_beq_refl clause_beq_eq] at hc ⊢
  rw [List.mem_append, List.mem_append] at hc ⊢
  cases hc with
  | inl h1 =>
    cases h1 with
    | inl hroot => exact Or.inl (Or.inl hroot)
    | inr hcur => exact Or.inl (Or.inr (hsub c hcur))
  | inr hexp =>
    rw [List.mem_flatMap] at hexp
    obtain ⟨c0, hc0, hcc⟩ := hexp
    exact Or.inr (List.mem_flatMap.mpr ⟨c0, hsub c0 hc0, hcc⟩)

theorem elaborate_contains_roots (traitSupers : Nat → List Clause) (f : ElabFilter)
    (roots : List Clause) (fuel : Nat) :
    ListSubset roots (elaborate traitSupers f roots (Nat.succ fuel)) := by
  intro c hc
  change c ∈ elabRound traitSupers f roots (elaborate traitSupers f roots fuel)
  unfold elabRound
  rw [mem_dedupList_iff Clause.beq clause_beq_refl clause_beq_eq]
  rw [List.mem_append, List.mem_append]
  exact Or.inl (Or.inl hc)

theorem elaborate_mono (traitSupers : Nat → List Clause) (f : ElabFilter) (roots : List Clause) :
    ∀ m n : Nat, m ≤ n →
      ListSubset (elaborate traitSupers f roots m) (elaborate traitSupers f roots n) := by
  intro m n hle
  induction hle with
  | refl => exact listSubset_refl _
  | step _ ih =>
    refine listSubset_trans ih ?_
    exact iterFn_mono Clause.beq clause_beq_refl clause_beq_eq
      (elabRound traitSupers f roots) (fun _ hx => hx)
      (fun h => elabRound_mono traitSupers f roots h) _

/-- Declarative entailment closure corresponding to `Elaborator` expansion. -/
inductive ElabEntails (traitSupers : Nat → List Clause) (f : ElabFilter) (roots : List Clause) :
    Clause → Prop where
  | root (c : Clause) : c ∈ roots → ElabEntails traitSupers f roots c
  | super (tr : Nat) (s : Ty) (rs : List Region) (ts : TyArgs) (c0 : Clause) :
      ElabEntails traitSupers f roots (.trait tr s rs ts) →
      c0 ∈ traitSupers tr →
      clauseMatchesFilter f c0 = true →
      ElabEntails traitSupers f roots (substClause rs (.cons s ts) c0)

/-- **Theorem (Supertrait Elaboration Soundness):** Every clause materialized by `elaborate`
is declaratively entailed by `ElabEntails`. -/
theorem elaborate_sound (traitSupers : Nat → List Clause) (f : ElabFilter) (roots : List Clause) :
    ∀ fuel c, c ∈ elaborate traitSupers f roots fuel → ElabEntails traitSupers f roots c := by
  intro fuel
  induction fuel with
  | zero => intro _ hc; cases hc
  | succ k ih =>
    intro c hc
    change c ∈ elabRound traitSupers f roots (elaborate traitSupers f roots k) at hc
    unfold elabRound at hc
    rw [mem_dedupList_iff Clause.beq clause_beq_refl clause_beq_eq] at hc
    rw [List.mem_append, List.mem_append] at hc
    cases hc with
    | inl h1 =>
      cases h1 with
      | inl hroot => exact ElabEntails.root c hroot
      | inr hprev => exact ih c hprev
    | inr hexp =>
      rw [List.mem_flatMap] at hexp
      obtain ⟨parent, hparent, hchild⟩ := hexp
      cases parent with
      | outlives _ => cases hchild
      | projEq _ _ _ _ _ => cases hchild
      | trait tr s rs ts =>
        change c ∈ ((traitSupers tr).filter (clauseMatchesFilter f)).map (substClause rs (.cons s ts)) at hchild
        rw [List.mem_map] at hchild
        obtain ⟨c0, hc0f, hEq⟩ := hchild
        rw [List.mem_filter] at hc0f
        rw [← hEq]
        exact ElabEntails.super tr s rs ts c0 (ih _ hparent) hc0f.1 hc0f.2

/-- Transitive chain predicate for arbitrary-depth positive supertrait paths. -/
inductive ElabPath (traitSupers : Nat → List Clause) (f : ElabFilter) (roots : List Clause) :
    Nat → Clause → Prop where
  | base (c : Clause) : c ∈ roots → ElabPath traitSupers f roots 0 c
  | step (n : Nat) (parent child : Clause) :
      ElabPath traitSupers f roots n parent →
      child ∈ expandClause traitSupers f parent →
      ElabPath traitSupers f roots (Nat.succ n) child

/-- **Theorem (Supertrait Elaboration Transitivity Completeness):** Every `k`-hop positive
supertrait / projection / outlives path from `roots` is materialized in `elaborate` at fuel `k + 1`. -/
theorem elaborate_transitivity_chain (traitSupers : Nat → List Clause) (f : ElabFilter)
    (roots : List Clause) (k : Nat) (c : Clause)
    (hpath : ElabPath traitSupers f roots k c) :
    c ∈ elaborate traitSupers f roots (Nat.succ k) := by
  induction hpath with
  | base c0 hc0 => exact elaborate_contains_roots traitSupers f roots 0 c0 hc0
  | step m parent child _ hstep ih =>
    change child ∈ elabRound traitSupers f roots (elaborate traitSupers f roots (Nat.succ m))
    unfold elabRound
    rw [mem_dedupList_iff Clause.beq clause_beq_refl clause_beq_eq]
    rw [List.mem_append, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨parent, ih, hstep⟩)

/-- **Theorem (`PredicateFilter` Trait vs. Trait-Alias Asymmetry):**
For `trait Tr<'a, T: 'a> { type Assoc: 'a; }: 'a` (trait ID `100`):
1. `Self: 'a` and `Self::Assoc: 'a` pass `.selfAndAssoc` and elaborate on `<X: Tr<'a, T>>`.
2. `T: 'a` (`Param 1: 'a`) is **FILTERED OUT** by `.selfAndAssoc` for ALL elaboration fuel (`E0309`),
   whereas trait aliases (`ElabFilter.all`) DO elaborate `T: 'a` at fuel 2. -/
noncomputable def trMixedSupers : Nat → List Clause
  | 100 =>
    [ .outlives { lhs := .param 0, rhs := .early 0 }
    , .outlives { lhs := .proj (.param 0) 100 0 [.early 0], rhs := .early 0 }
    , .outlives { lhs := .param 1, rhs := .early 0 } ]
  | _ => []

noncomputable def trRoot : List Clause :=
  [.trait 100 (.param 9) [.early 0] (.cons (.param 1) .nil)]

theorem trait_self_and_assoc_elaborates :
    .outlives { lhs := .param 9, rhs := .early 0 } ∈
      elaborate trMixedSupers .selfAndAssoc trRoot 2 ∧
    .outlives { lhs := .proj (.param 9) 100 0 [.early 0], rhs := .early 0 } ∈
      elaborate trMixedSupers .selfAndAssoc trRoot 2 :=
  ⟨ (listMem_spec Clause.beq clause_beq_refl clause_beq_eq
      (.outlives { lhs := .param 9, rhs := .early 0 })
      (elaborate trMixedSupers .selfAndAssoc trRoot 2)).mp rfl
  , (listMem_spec Clause.beq clause_beq_refl clause_beq_eq
      (.outlives { lhs := .proj (.param 9) 100 0 [.early 0], rhs := .early 0 })
      (elaborate trMixedSupers .selfAndAssoc trRoot 2)).mp rfl ⟩

theorem trait_alias_all_elaborates_param_bound :
    .outlives { lhs := .param 1, rhs := .early 0 } ∈
      elaborate trMixedSupers .all trRoot 2 :=
  (listMem_spec Clause.beq clause_beq_refl clause_beq_eq
    (.outlives { lhs := .param 1, rhs := .early 0 })
    (elaborate trMixedSupers .all trRoot 2)).mp rfl

theorem elabEntails_trMixed_selfAndAssoc_char (c : Clause)
    (h : ElabEntails trMixedSupers .selfAndAssoc trRoot c) :
    c = .trait 100 (.param 9) [.early 0] (.cons (.param 1) .nil) ∨
    c = .outlives { lhs := .param 9, rhs := .early 0 } ∨
    c = .outlives { lhs := .proj (.param 9) 100 0 [.early 0], rhs := .early 0 } := by
  induction h with
  | root c0 hr =>
    cases hr with
    | head => exact Or.inl rfl
    | tail _ ht => cases ht
  | super tr s rs ts c0 _ hc0 hfilt ih =>
    cases ih with
    | inl hRoot =>
      cases hRoot
      change c0 ∈ trMixedSupers 100 at hc0
      cases hc0 with
      | head => exact Or.inr (Or.inl rfl)
      | tail _ ht1 =>
        cases ht1 with
        | head => exact Or.inr (Or.inr rfl)
        | tail _ ht2 =>
          cases ht2 with
          | head => cases hfilt
          | tail _ ht3 => cases ht3
    | inr hOut =>
      cases hOut with
      | inl hEq => cases hEq
      | inr hEq => cases hEq

theorem trait_param_bound_excluded_by_selfAndAssoc_e0309 (fuel : Nat) :
    ¬ (.outlives { lhs := .param 1, rhs := .early 0 } ∈
        elaborate trMixedSupers .selfAndAssoc trRoot fuel) := by
  intro hin
  have hent := elaborate_sound trMixedSupers .selfAndAssoc trRoot fuel _ hin
  cases elabEntails_trMixed_selfAndAssoc_char _ hent with
  | inl h => cases h
  | inr h =>
    cases h with
    | inl h1 => cases h1
    | inr h2 => cases h2

/-! ## Part 7: Associated-Type Projection Candidate Precedence & Church-Rosser Confluence -/

/-- Models `rustc_trait_selection::traits::project::ProjectionCandidateSet` (`project.rs:103-138`):
- `empty`: no candidate matches
- `single rhs`: unique candidate (or multiple syntactically equal deduplicated candidates!)
- `ambiguous`: conflicting unequal candidates (`if current != &candidate`) -> `E0284`. -/
inductive CandidateSet where
  | empty
  | single (rhs : Ty)
  | ambiguous

noncomputable def pushCandidate : CandidateSet → Ty → CandidateSet
  | .empty, cand => .single cand
  | .single prev, cand =>
    match tyBeq prev cand with
    | true => .single prev
    | false => .ambiguous
  | .ambiguous, _ => .ambiguous

noncomputable def assembleCandidates (paramSet traitDefSet objectSet implSet : CandidateSet) :
    CandidateSet :=
  match paramSet with
  | .empty =>
    match traitDefSet with
    | .empty =>
      match objectSet with
      | .empty => implSet
      | _ => objectSet
    | _ => traitDefSet
  | _ => paramSet

theorem pushCandidate_consistent_diamond (t : Ty) :
    pushCandidate (pushCandidate .empty t) t = .single t := by
  change (match tyBeq t t with | true => CandidateSet.single t | false => CandidateSet.ambiguous) =
    CandidateSet.single t
  rw [tyBeq_refl t]

theorem pushCandidate_conflict_ambiguous {t1 t2 : Ty} (hne : t1 ≠ t2) :
    pushCandidate (pushCandidate .empty t1) t2 = .ambiguous := by
  change (match tyBeq t1 t2 with | true => CandidateSet.single t1 | false => CandidateSet.ambiguous) =
    CandidateSet.ambiguous
  cases h : tyBeq t1 t2
  · rfl
  · exact False.elim (hne (tyBeq_eq h))

theorem diamond_consistent_resolves_u32 :
    pushCandidate (pushCandidate .empty .prim) .prim = .single .prim :=
  pushCandidate_consistent_diamond .prim

theorem diamond_conflict_yields_ambiguous_e0284 :
    pushCandidate (pushCandidate .empty .prim) (.param 0) = .ambiguous :=
  pushCandidate_conflict_ambiguous (fun h => by cases h)

/-- **Theorem (`ParamEnv` Precedence over `Impl`):** Whenever `ParamEnv` uniquely resolves an
associated-type projection (`paramSet = .single rhs`), `assembleCandidates` strictly returns
`.single rhs` before inspecting `TraitDef`, `Object`, or `Impl` candidates. -/
theorem paramEnv_beats_impl (rhs : Ty) (traitDefSet objectSet implSet : CandidateSet) :
    assembleCandidates (.single rhs) traitDefSet objectSet implSet = .single rhs := rfl

structure ProjRule where
  selfPat : Ty
  traitId : Nat
  assocId : Nat
  rArgs : List Region
  rhs : Ty

noncomputable def lookupProj (rules : List ProjRule) (s : Ty) (tr as : Nat) (rs : List Region) :
    Option Ty :=
  (rules.find? (fun r =>
    tyBeq r.selfPat s && Nat.beq r.traitId tr && Nat.beq r.assocId as && regionListBeq r.rArgs rs)).map
    (fun r => r.rhs)

theorem lookupProj_deterministic {rules : List ProjRule} {s : Ty} {tr as : Nat} {rs : List Region}
    {r1 r2 : Ty}
    (h1 : lookupProj rules s tr as rs = some r1)
    (h2 : lookupProj rules s tr as rs = some r2) : r1 = r2 := by
  rw [h1] at h2
  cases h2
  rfl

mutual
  inductive NormStep (rules : List ProjRule) : Ty → Ty → Prop where
    | ref (r : Region) {p p' : Ty} : NormStep rules p p' → NormStep rules (.ref r p) (.ref r p')
    | pairL {a a' : Ty} (b : Ty) : NormStep rules a a' → NormStep rules (.pair a b) (.pair a' b)
    | pairR (a : Ty) {b b' : Ty} : NormStep rules b b' → NormStep rules (.pair a b) (.pair a b')
    | adt (id : Nat) (rs : List Region) {ts ts' : TyArgs} :
        NormStepArgs rules ts ts' → NormStep rules (.adt id rs ts) (.adt id rs ts')
    | projSelf {s s' : Ty} (tr as : Nat) (rs : List Region) :
        NormStep rules s s' → NormStep rules (.proj s tr as rs) (.proj s' tr as rs)
    | projRule (s : Ty) (tr as : Nat) (rs : List Region) (rhs : Ty) :
        lookupProj rules s tr as rs = some rhs → NormStep rules (.proj s tr as rs) rhs
    | fnArg {a a' : Ty} (r : Ty) : NormStep rules a a' → NormStep rules (.fnBinder a r) (.fnBinder a' r)
    | fnRet (a : Ty) {r r' : Ty} : NormStep rules r r' → NormStep rules (.fnBinder a r) (.fnBinder a r')

  inductive NormStepArgs (rules : List ProjRule) : TyArgs → TyArgs → Prop where
    | head {h h' : Ty} (t : TyArgs) :
        NormStep rules h h' → NormStepArgs rules (.cons h t) (.cons h' t)
    | tail (h : Ty) {t t' : TyArgs} :
        NormStepArgs rules t t' → NormStepArgs rules (.cons h t) (.cons h t')
end

inductive NormStar (rules : List ProjRule) : Ty → Ty → Prop where
  | refl (t : Ty) : NormStar rules t t
  | step {a b c : Ty} : NormStep rules a b → NormStar rules b c → NormStar rules a c

inductive NormStarArgs (rules : List ProjRule) : TyArgs → TyArgs → Prop where
  | refl (ts : TyArgs) : NormStarArgs rules ts ts
  | step {a b c : TyArgs} : NormStepArgs rules a b → NormStarArgs rules b c → NormStarArgs rules a c

theorem normStar_one {rules : List ProjRule} {a b : Ty} (h : NormStep rules a b) :
    NormStar rules a b :=
  NormStar.step h (NormStar.refl b)

theorem normStar_trans {rules : List ProjRule} {a b c : Ty}
    (h1 : NormStar rules a b) (h2 : NormStar rules b c) : NormStar rules a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact NormStar.step hs (ih h2)

theorem normStarArgs_trans {rules : List ProjRule} {a b c : TyArgs}
    (h1 : NormStarArgs rules a b) (h2 : NormStarArgs rules b c) : NormStarArgs rules a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact NormStarArgs.step hs (ih h2)

theorem normStar_ref {rules : List ProjRule} (r : Region) {p p' : Ty}
    (h : NormStar rules p p') : NormStar rules (.ref r p) (.ref r p') := by
  induction h with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.ref r hs) ih

theorem normStar_pairL {rules : List ProjRule} {a a' : Ty} (b : Ty)
    (ha : NormStar rules a a') : NormStar rules (.pair a b) (.pair a' b) := by
  induction ha with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.pairL b hs) ih

theorem normStar_pairR {rules : List ProjRule} (a : Ty) {b b' : Ty}
    (hb : NormStar rules b b') : NormStar rules (.pair a b) (.pair a b') := by
  induction hb with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.pairR a hs) ih

theorem normStar_pair {rules : List ProjRule} {a a' b b' : Ty}
    (ha : NormStar rules a a') (hb : NormStar rules b b') :
    NormStar rules (.pair a b) (.pair a' b') :=
  normStar_trans (normStar_pairL b ha) (normStar_pairR a' hb)

theorem normStar_adt {rules : List ProjRule} (id : Nat) (rs : List Region) {ts ts' : TyArgs}
    (h : NormStarArgs rules ts ts') : NormStar rules (.adt id rs ts) (.adt id rs ts') := by
  induction h with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.adt id rs hs) ih

theorem normStar_proj {rules : List ProjRule} {s s' : Ty} (tr as : Nat) (rs : List Region)
    (h : NormStar rules s s') : NormStar rules (.proj s tr as rs) (.proj s' tr as rs) := by
  induction h with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.projSelf tr as rs hs) ih

theorem normStar_fnArg {rules : List ProjRule} {a a' : Ty} (r : Ty)
    (ha : NormStar rules a a') : NormStar rules (.fnBinder a r) (.fnBinder a' r) := by
  induction ha with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.fnArg r hs) ih

theorem normStar_fnRet {rules : List ProjRule} (a : Ty) {r r' : Ty}
    (hr : NormStar rules r r') : NormStar rules (.fnBinder a r) (.fnBinder a r') := by
  induction hr with
  | refl => exact NormStar.refl _
  | step hs _ ih => exact NormStar.step (NormStep.fnRet a hs) ih

theorem normStar_fnBinder {rules : List ProjRule} {a a' r r' : Ty}
    (ha : NormStar rules a a') (hr : NormStar rules r r') :
    NormStar rules (.fnBinder a r) (.fnBinder a' r') :=
  normStar_trans (normStar_fnArg r ha) (normStar_fnRet a' hr)

theorem normStarArgs_head {rules : List ProjRule} {h h' : Ty} (t : TyArgs)
    (hh : NormStar rules h h') : NormStarArgs rules (.cons h t) (.cons h' t) := by
  induction hh with
  | refl => exact NormStarArgs.refl _
  | step hs _ ih => exact NormStarArgs.step (NormStepArgs.head t hs) ih

theorem normStarArgs_tail {rules : List ProjRule} (h : Ty) {t t' : TyArgs}
    (ht : NormStarArgs rules t t') : NormStarArgs rules (.cons h t) (.cons h t') := by
  induction ht with
  | refl => exact NormStarArgs.refl _
  | step hs _ ih => exact NormStarArgs.step (NormStepArgs.tail h hs) ih

theorem normStarArgs_cons {rules : List ProjRule} {h h' : Ty} {t t' : TyArgs}
    (hh : NormStar rules h h') (ht : NormStarArgs rules t t') :
    NormStarArgs rules (.cons h t) (.cons h' t') :=
  normStarArgs_trans (normStarArgs_head t hh) (normStarArgs_tail h' ht)

noncomputable def IsNormal (rules : List ProjRule) (t : Ty) : Prop :=
  ∀ t', ¬ NormStep rules t t'

theorem normStar_normal_eq {rules : List ProjRule} {s s' : Ty}
    (hNorm : IsNormal rules s) (h : NormStar rules s s') : s' = s := by
  cases h with
  | refl => rfl
  | step hs _ => exact False.elim (hNorm _ hs)

mutual
  inductive ParNorm (rules : List ProjRule) : Ty → Ty → Prop where
    | prim : ParNorm rules .prim .prim
    | param (i : Nat) : ParNorm rules (.param i) (.param i)
    | ref (r : Region) {p p' : Ty} : ParNorm rules p p' → ParNorm rules (.ref r p) (.ref r p')
    | pair {a a' b b' : Ty} :
        ParNorm rules a a' → ParNorm rules b b' → ParNorm rules (.pair a b) (.pair a' b')
    | adt (id : Nat) (rs : List Region) {ts ts' : TyArgs} :
        ParNormArgs rules ts ts' → ParNorm rules (.adt id rs ts) (.adt id rs ts')
    | proj {s s' : Ty} (tr as : Nat) (rs : List Region) :
        ParNorm rules s s' → ParNorm rules (.proj s tr as rs) (.proj s' tr as rs)
    | rule (s : Ty) (tr as : Nat) (rs : List Region) (rhs : Ty) :
        lookupProj rules s tr as rs = some rhs → ParNorm rules (.proj s tr as rs) rhs
    | fnBinder {a a' r r' : Ty} :
        ParNorm rules a a' → ParNorm rules r r' → ParNorm rules (.fnBinder a r) (.fnBinder a' r')
    | dynObj (tr : Nat) (rs : List Region) (b : Region) :
        ParNorm rules (.dynObj tr rs b) (.dynObj tr rs b)

  inductive ParNormArgs (rules : List ProjRule) : TyArgs → TyArgs → Prop where
    | nil : ParNormArgs rules .nil .nil
    | cons {h h' : Ty} {t t' : TyArgs} :
        ParNorm rules h h' → ParNormArgs rules t t' → ParNormArgs rules (.cons h t) (.cons h' t')
end

theorem parNorm_refl_both (rules : List ProjRule) :
    (∀ t : Ty, ParNorm rules t t) ∧ (∀ ts : TyArgs, ParNormArgs rules ts ts) := by
  apply ty_rec_pair (fun t => ParNorm rules t t) (fun ts => ParNormArgs rules ts ts)
  · exact ParNorm.prim
  · intro i; exact ParNorm.param i
  · intro r _ ih; exact ParNorm.ref r ih
  · intro _ _ ih1 ih2; exact ParNorm.pair ih1 ih2
  · intro id rs _ ihArgs; exact ParNorm.adt id rs ihArgs
  · intro _ tr as rs ihS; exact ParNorm.proj tr as rs ihS
  · intro _ _ ihA ihR; exact ParNorm.fnBinder ihA ihR
  · intro tr rs b; exact ParNorm.dynObj tr rs b
  · exact ParNormArgs.nil
  · intro _ _ ihH ihT; exact ParNormArgs.cons ihH ihT

theorem normStep_to_parNorm (rules : List ProjRule) :
    (∀ a b : Ty, NormStep rules a b → ParNorm rules a b) ∧
    (∀ as bs : TyArgs, NormStepArgs rules as bs → ParNormArgs rules as bs) :=
  ⟨ @NormStep.rec rules (fun a b _ => ParNorm rules a b) (fun as bs _ => ParNormArgs rules as bs)
      (fun r {_ _} _ ih => ParNorm.ref r ih)
      (fun {_ _} b _ ih => ParNorm.pair ih ((parNorm_refl_both rules).1 b))
      (fun a {_ _} _ ih => ParNorm.pair ((parNorm_refl_both rules).1 a) ih)
      (fun id rs {_ _} _ ih => ParNorm.adt id rs ih)
      (fun {_ _} tr as rs _ ih => ParNorm.proj tr as rs ih)
      (fun s tr as rs rhs h => ParNorm.rule s tr as rs rhs h)
      (fun {_ _} r _ ih => ParNorm.fnBinder ih ((parNorm_refl_both rules).1 r))
      (fun a {_ _} _ ih => ParNorm.fnBinder ((parNorm_refl_both rules).1 a) ih)
      (fun {_ _} t _ ih => ParNormArgs.cons ih ((parNorm_refl_both rules).2 t))
      (fun h {_ _} _ ih => ParNormArgs.cons ((parNorm_refl_both rules).1 h) ih)
  , @NormStepArgs.rec rules (fun a b _ => ParNorm rules a b) (fun as bs _ => ParNormArgs rules as bs)
      (fun r {_ _} _ ih => ParNorm.ref r ih)
      (fun {_ _} b _ ih => ParNorm.pair ih ((parNorm_refl_both rules).1 b))
      (fun a {_ _} _ ih => ParNorm.pair ((parNorm_refl_both rules).1 a) ih)
      (fun id rs {_ _} _ ih => ParNorm.adt id rs ih)
      (fun {_ _} tr as rs _ ih => ParNorm.proj tr as rs ih)
      (fun s tr as rs rhs h => ParNorm.rule s tr as rs rhs h)
      (fun {_ _} r _ ih => ParNorm.fnBinder ih ((parNorm_refl_both rules).1 r))
      (fun a {_ _} _ ih => ParNorm.fnBinder ((parNorm_refl_both rules).1 a) ih)
      (fun {_ _} t _ ih => ParNormArgs.cons ih ((parNorm_refl_both rules).2 t))
      (fun h {_ _} _ ih => ParNormArgs.cons ((parNorm_refl_both rules).1 h) ih) ⟩

theorem parNorm_to_normStar (rules : List ProjRule) :
    (∀ a b : Ty, ParNorm rules a b → NormStar rules a b) ∧
    (∀ as bs : TyArgs, ParNormArgs rules as bs → NormStarArgs rules as bs) :=
  ⟨ @ParNorm.rec rules (fun a b _ => NormStar rules a b) (fun as bs _ => NormStarArgs rules as bs)
      (NormStar.refl .prim)
      (fun i => NormStar.refl (.param i))
      (fun r {_ _} _ ih => normStar_ref r ih)
      (fun {_ _ _ _} _ _ ih1 ih2 => normStar_pair ih1 ih2)
      (fun id rs {_ _} _ ih => normStar_adt id rs ih)
      (fun {_ _} tr as rs _ ih => normStar_proj tr as rs ih)
      (fun s tr as rs rhs h => normStar_one (NormStep.projRule s tr as rs rhs h))
      (fun {_ _ _ _} _ _ ih1 ih2 => normStar_fnBinder ih1 ih2)
      (fun tr rs b => NormStar.refl (.dynObj tr rs b))
      (NormStarArgs.refl .nil)
      (fun {_ _ _ _} _ _ ih1 ih2 => normStarArgs_cons ih1 ih2)
  , @ParNormArgs.rec rules (fun a b _ => NormStar rules a b) (fun as bs _ => NormStarArgs rules as bs)
      (NormStar.refl .prim)
      (fun i => NormStar.refl (.param i))
      (fun r {_ _} _ ih => normStar_ref r ih)
      (fun {_ _ _ _} _ _ ih1 ih2 => normStar_pair ih1 ih2)
      (fun id rs {_ _} _ ih => normStar_adt id rs ih)
      (fun {_ _} tr as rs _ ih => normStar_proj tr as rs ih)
      (fun s tr as rs rhs h => normStar_one (NormStep.projRule s tr as rs rhs h))
      (fun {_ _ _ _} _ _ ih1 ih2 => normStar_fnBinder ih1 ih2)
      (fun tr rs b => NormStar.refl (.dynObj tr rs b))
      (NormStarArgs.refl .nil)
      (fun {_ _ _ _} _ _ ih1 ih2 => normStarArgs_cons ih1 ih2) ⟩

theorem parNorm_normal_eq {rules : List ProjRule} {s s' : Ty}
    (hNorm : IsNormal rules s) (h : ParNorm rules s s') : s' = s :=
  normStar_normal_eq hNorm ((parNorm_to_normStar rules).1 s s' h)

/-- Ground-head / normalized-self hypothesis modeling resolved trait impl & `ParamEnv` heads
whose `selfPat` contains no further unnormalized projection redexes. -/
noncomputable def GroundHeadRules (rules : List ProjRule) : Prop :=
  ∀ s tr as rs rhs, lookupProj rules s tr as rs = some rhs → IsNormal rules s

theorem parNorm_rec_pair (rules : List ProjRule)
    (P : ∀ {a b : Ty}, ParNorm rules a b → Prop)
    (Q : ∀ {as bs : TyArgs}, ParNormArgs rules as bs → Prop)
    (hprim : P ParNorm.prim)
    (hparam : ∀ i, P (ParNorm.param i))
    (href : ∀ r {p p'} (hp : ParNorm rules p p'), P hp → P (ParNorm.ref r hp))
    (hpair : ∀ {a a' b b'} (ha : ParNorm rules a a') (hb : ParNorm rules b b'),
      P ha → P hb → P (ParNorm.pair ha hb))
    (hadt : ∀ id rs {ts ts'} (hts : ParNormArgs rules ts ts'), Q hts → P (ParNorm.adt id rs hts))
    (hproj : ∀ {s s'} tr as rs (hs : ParNorm rules s s'), P hs → P (ParNorm.proj tr as rs hs))
    (hrule : ∀ s tr as rs rhs (hl : lookupProj rules s tr as rs = some rhs),
      P (ParNorm.rule s tr as rs rhs hl))
    (hfn : ∀ {a a' r r'} (ha : ParNorm rules a a') (hr : ParNorm rules r r'),
      P ha → P hr → P (ParNorm.fnBinder ha hr))
    (hdyn : ∀ tr rs b, P (ParNorm.dynObj tr rs b))
    (hnil : Q ParNormArgs.nil)
    (hcons : ∀ {h h' t t'} (hh : ParNorm rules h h') (ht : ParNormArgs rules t t'),
      P hh → Q ht → Q (ParNormArgs.cons hh ht)) :
    (∀ {a b} (hab : ParNorm rules a b), P hab) ∧
    (∀ {as bs} (habs : ParNormArgs rules as bs), Q habs) :=
  ⟨ fun {a b} hab => @ParNorm.rec rules (fun _ _ h => P h) (fun _ _ h => Q h)
      hprim hparam (fun r {_ _} hp ih => href r hp ih)
      (fun {_ _ _ _} ha hb iha ihb => hpair ha hb iha ihb)
      (fun id rs {_ _} hts ih => hadt id rs hts ih)
      (fun {_ _} tr as rs hs ih => hproj tr as rs hs ih)
      hrule
      (fun {_ _ _ _} ha hr iha ihr => hfn ha hr iha ihr)
      hdyn hnil (fun {_ _ _ _} hh ht ihh iht => hcons hh ht ihh iht) a b hab
  , fun {as bs} habs => @ParNormArgs.rec rules (fun _ _ h => P h) (fun _ _ h => Q h)
      hprim hparam (fun r {_ _} hp ih => href r hp ih)
      (fun {_ _ _ _} ha hb iha ihb => hpair ha hb iha ihb)
      (fun id rs {_ _} hts ih => hadt id rs hts ih)
      (fun {_ _} tr as rs hs ih => hproj tr as rs hs ih)
      hrule
      (fun {_ _ _ _} ha hr iha ihr => hfn ha hr iha ihr)
      hdyn hnil (fun {_ _ _ _} hh ht ihh iht => hcons hh ht ihh iht) as bs habs ⟩

theorem parNorm_proj_inv {rules : List ProjRule} {s : Ty} {tr as : Nat} {rs : List Region}
    {u : Ty} (h : ParNorm rules (.proj s tr as rs) u) :
    (∃ s', u = .proj s' tr as rs ∧ ParNorm rules s s') ∨
    (lookupProj rules s tr as rs = some u) := by
  cases h <;> first | exact Or.inr ‹_› | exact Or.inl ⟨_, rfl, ‹_›⟩

/-- **Theorem (Parallel Projection Normalization Diamond):** Under deterministic ground-head rules,
`ParNorm` satisfies the strong one-step diamond property. -/
theorem parNorm_diamond (rules : List ProjRule) (hGround : GroundHeadRules rules) :
    (∀ {t u1 : Ty}, ParNorm rules t u1 → ∀ {u2 : Ty}, ParNorm rules t u2 →
      ∃ w : Ty, ParNorm rules u1 w ∧ ParNorm rules u2 w) ∧
    (∀ {ts us1 : TyArgs}, ParNormArgs rules ts us1 → ∀ {us2 : TyArgs}, ParNormArgs rules ts us2 →
      ∃ ws : TyArgs, ParNormArgs rules us1 ws ∧ ParNormArgs rules us2 ws) := by
  apply parNorm_rec_pair rules
    (fun {t u1} _ => ∀ {u2 : Ty}, ParNorm rules t u2 → ∃ w : Ty, ParNorm rules u1 w ∧ ParNorm rules u2 w)
    (fun {ts us1} _ => ∀ {us2 : TyArgs}, ParNormArgs rules ts us2 →
      ∃ ws : TyArgs, ParNormArgs rules us1 ws ∧ ParNormArgs rules us2 ws)
  · intro u2 h2; cases h2; exact ⟨.prim, ParNorm.prim, ParNorm.prim⟩
  · intro i u2 h2; cases h2; exact ⟨.param i, ParNorm.param i, ParNorm.param i⟩
  · intro r p p1 hp ih u2 h2
    cases h2 with
    | ref _ hp2 =>
      obtain ⟨w, hw1, hw2⟩ := ih hp2
      exact ⟨.ref r w, ParNorm.ref r hw1, ParNorm.ref r hw2⟩
  · intro a a1 b b1 ha hb iha ihb u2 h2
    cases h2 with
    | pair ha2 hb2 =>
      obtain ⟨wa, hwa1, hwa2⟩ := iha ha2
      obtain ⟨wb, hwb1, hwb2⟩ := ihb hb2
      exact ⟨.pair wa wb, ParNorm.pair hwa1 hwb1, ParNorm.pair hwa2 hwb2⟩
  · intro id rs ts ts1 hts ihts u2 h2
    cases h2 with
    | adt _ _ hts2 =>
      obtain ⟨ws, hws1, hws2⟩ := ihts hts2
      exact ⟨.adt id rs ws, ParNorm.adt id rs hws1, ParNorm.adt id rs hws2⟩
  · intro s s1 tr as rs hs ihs u2 h2
    cases parNorm_proj_inv h2 with
    | inl hp =>
      obtain ⟨s2, hu2, hs2⟩ := hp
      obtain ⟨ws, hws1, hws2⟩ := ihs hs2
      rw [hu2]
      exact ⟨.proj ws tr as rs, ParNorm.proj tr as rs hws1, ParNorm.proj tr as rs hws2⟩
    | inr hLook =>
      have hEq : s1 = s := parNorm_normal_eq (hGround s tr as rs u2 hLook) hs
      rw [hEq]
      exact ⟨u2, ParNorm.rule s tr as rs u2 hLook, (parNorm_refl_both rules).1 u2⟩
  · intro s tr as rs rhs hLook u2 h2
    cases parNorm_proj_inv h2 with
    | inl hp =>
      obtain ⟨s2, hu2, hs2⟩ := hp
      have hEq := parNorm_normal_eq (hGround s tr as rs rhs hLook) hs2
      rw [hu2, hEq]
      exact ⟨rhs, (parNorm_refl_both rules).1 rhs, ParNorm.rule s tr as rs rhs hLook⟩
    | inr hLook2 =>
      have hEq := lookupProj_deterministic hLook hLook2
      rw [← hEq]
      exact ⟨rhs, (parNorm_refl_both rules).1 rhs, (parNorm_refl_both rules).1 rhs⟩
  · intro a a1 r r1 ha hr iha ihr u2 h2
    cases h2 with
    | fnBinder ha2 hr2 =>
      obtain ⟨wa, hwa1, hwa2⟩ := iha ha2
      obtain ⟨wr, hwr1, hwr2⟩ := ihr hr2
      exact ⟨.fnBinder wa wr, ParNorm.fnBinder hwa1 hwr1, ParNorm.fnBinder hwa2 hwr2⟩
  · intro tr rs b u2 h2; cases h2; exact ⟨.dynObj tr rs b, ParNorm.dynObj tr rs b, ParNorm.dynObj tr rs b⟩
  · intro us2 h2; cases h2; exact ⟨.nil, ParNormArgs.nil, ParNormArgs.nil⟩
  · intro h h1 t t1 hh ht ihh iht us2 h2
    cases h2 with
    | cons hh2 ht2 =>
      obtain ⟨wh, hwh1, hwh2⟩ := ihh hh2
      obtain ⟨wt, hwt1, hwt2⟩ := iht ht2
      exact ⟨.cons wh wt, ParNormArgs.cons hwh1 hwt1, ParNormArgs.cons hwh2 hwt2⟩

inductive ParStar (rules : List ProjRule) : Ty → Ty → Prop where
  | refl (t : Ty) : ParStar rules t t
  | step {a b c : Ty} : ParNorm rules a b → ParStar rules b c → ParStar rules a c

theorem parStar_trans {rules : List ProjRule} {a b c : Ty}
    (h1 : ParStar rules a b) (h2 : ParStar rules b c) : ParStar rules a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact ParStar.step hs (ih h2)

theorem normStar_to_parStar {rules : List ProjRule} {a b : Ty}
    (h : NormStar rules a b) : ParStar rules a b := by
  induction h with
  | refl t => exact ParStar.refl t
  | step hs _ ih => exact ParStar.step ((normStep_to_parNorm rules).1 _ _ hs) ih

theorem parStar_to_normStar {rules : List ProjRule} {a b : Ty}
    (h : ParStar rules a b) : NormStar rules a b := by
  induction h with
  | refl t => exact NormStar.refl t
  | step hp _ ih => exact normStar_trans ((parNorm_to_normStar rules).1 _ _ hp) ih

theorem parStar_strip (rules : List ProjRule) (hGround : GroundHeadRules rules)
    {a b c : Ty} (hab : ParNorm rules a b) (hac : ParStar rules a c) :
    ∃ w : Ty, ParStar rules b w ∧ ParNorm rules c w := by
  induction hac generalizing b with
  | refl => exact ⟨b, ParStar.refl b, hab⟩
  | step hxy _ ih =>
    obtain ⟨m, hbm, hym⟩ := (parNorm_diamond rules hGround).1 hab hxy
    obtain ⟨w, hmw, hzw⟩ := ih hym
    exact ⟨w, ParStar.step hbm hmw, hzw⟩

theorem parStar_confluent (rules : List ProjRule) (hGround : GroundHeadRules rules)
    {a b c : Ty} (hab : ParStar rules a b) (hac : ParStar rules a c) :
    ∃ w : Ty, ParStar rules b w ∧ ParStar rules c w := by
  induction hab generalizing c with
  | refl => exact ⟨c, hac, ParStar.refl c⟩
  | step hxy _ ih =>
    obtain ⟨m, hym, hcm⟩ := parStar_strip rules hGround hxy hac
    obtain ⟨w, hzw, hmw⟩ := ih hym
    exact ⟨w, hzw, ParStar.step hcm hmw⟩

/-- **Theorem (Associated-Type Projection Normalization Church-Rosser Confluence):**
Under deterministic ground-head normalization rules (`ParamEnv > TraitDef > Object > Impl`),
arbitrary normalization paths `a ->* b` and `a ->* c` always reconverge (`∃ w, b ->* w ∧ c ->* w`). -/
theorem normStar_confluent (rules : List ProjRule) (hGround : GroundHeadRules rules)
    {a b c : Ty} (hab : NormStar rules a b) (hac : NormStar rules a c) :
    ∃ w : Ty, NormStar rules b w ∧ NormStar rules c w := by
  obtain ⟨w, hbw, hcw⟩ := parStar_confluent rules hGround (normStar_to_parStar hab) (normStar_to_parStar hac)
  exact ⟨w, parStar_to_normStar hbw, parStar_to_normStar hcw⟩

/-- **Theorem (Projection Normal Form Uniqueness):** Two normal forms reachable from the same
type `t` must be syntactically identical. -/
theorem normal_form_unique (rules : List ProjRule) (hGround : GroundHeadRules rules)
    {t n1 n2 : Ty} (hn1 : IsNormal rules n1) (hn2 : IsNormal rules n2)
    (h1 : NormStar rules t n1) (h2 : NormStar rules t n2) : n1 = n2 := by
  obtain ⟨w, hw1, hw2⟩ := normStar_confluent rules hGround h1 h2
  have ew1 : w = n1 := normStar_normal_eq hn1 hw1
  have ew2 : w = n2 := normStar_normal_eq hn2 hw2
  rw [← ew1, ew2]

end ImpliedBoundsRfc2093
