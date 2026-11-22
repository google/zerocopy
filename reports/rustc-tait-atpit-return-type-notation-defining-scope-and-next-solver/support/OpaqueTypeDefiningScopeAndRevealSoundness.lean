/-
  OpaqueTypeDefiningScopeAndRevealSoundness.lean

  Kernel-checked Lean 4 (v4.34.1) mechanization of rustc opaque types:
    * TAIT (`#![feature(type_alias_impl_trait)]` + `#[define_opaque(...)]`)
    * ATPIT (`#![feature(impl_trait_in_assoc_type)]`)
    * RPITIT & RTN (`#![feature(return_type_notation)]`)
    * Three-phase visibility: `Reveal::UserFacing` (`TypingMode::Typeck` outside defining scope),
      auto-trait leakage (`Send` / `Sync` / `Unpin`), and `Reveal::All` (`TypingMode::PostAnalysis`
      / `TypingMode::Codegen` layout and ABI transparency)
    * `-Z next-solver=globally` vs. `-Z next-solver=no` defining-use and cycle semantics
    * Four constructive sharpness counterexamples (`ce1`..`ce4`)

  Purity invariants:
    * Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
      zero `native_decide`, zero `partial def`, zero `._unsafe_rec` constants.
    * Uses only pure structural induction and mutual inductives (`Ty` / `TyList`).
-/

namespace Anneal.OpaqueTypeSoundness

/-! ## Section 1: Identifiers, Traits, Primitives, and Layout Algebra -/

abbrev OpaqueId := Nat
abbrev ParamId := Nat
abbrev TraitId := Nat
abbrev ItemId := Nat
abbrev AssocMethodId := Nat

/- Built-in auto-traits that leak through opaque witnesses outside defining scopes. -/
inductive AutoTrait where
  | send
  | sync
  | unpin

/-- Concrete primitive Rust types modeled with 64-bit ABI layout and auto-trait polarity. -/
inductive PrimTy where
  | unit
  | bool
  | u16
  | u32
  | u64
  | rcU32

/-- Concrete ABI size and alignment in bytes. -/
structure Layout where
  size : Nat
  align : Nat

/-- Constructive `Nat` helper lemmas proved without `omega`. -/
theorem nat_ne_of_lt {a b : Nat} (h : a < b) : a ≠ b := by
  intro heq
  subst heq
  exact Nat.lt_irrefl a h

theorem nat_le_trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

theorem nat_max_ge_left (a b : Nat) : a ≤ Nat.max a b := Nat.le_max_left a b

theorem nat_max_ge_right (a b : Nat) : b ≤ Nat.max a b := Nat.le_max_right a b

theorem nat_add_eq_zero_left {a b : Nat} (h : a + b = 0) : a = 0 :=
  (Nat.add_eq_zero_iff.mp h).1

theorem nat_le_or_ge (a b : Nat) : a ≤ b ∨ b ≤ a := Nat.le_total a b

/-- Round `offset` up to the next multiple of `align` (for positive `align`). -/
def alignUp (offset align : Nat) : Nat :=
  match align with
  | 0 => offset
  | a + 1 =>
    let rem := offset % (a + 1)
    match rem with
    | 0 => offset
    | _ => offset + ((a + 1) - rem)

/-- Concrete ABI layout of primitive Rust types on `x86_64-unknown-linux-gnu`. -/
def primLayout : PrimTy → Layout
  | .unit  => { size := 0, align := 1 }
  | .bool  => { size := 1, align := 1 }
  | .u16   => { size := 2, align := 2 }
  | .u32   => { size := 4, align := 4 }
  | .u64   => { size := 8, align := 8 }
  | .rcU32 => { size := 8, align := 8 }

/-- Layout of a 2-tuple `(lhs, rhs)` with standard alignment padding. -/
def pairLayout (l r : Layout) : Layout :=
  let a := Nat.max l.align r.align
  let offR := alignUp l.size r.align
  { size := alignUp (offR + r.size) a, align := a }

/-- Layout of a homogeneous array `[T; n]`. -/
def arrayLayout (elem : Layout) (len : Nat) : Layout :=
  { size := elem.size * len, align := elem.align }

/-- Pointer-sized layout of `Box<T>` and niche-optimized `Option<Box<T>>` (8 B, align 8). -/
def ptrLayout : Layout := { size := 8, align := 8 }

/-- Auto-trait truth table on primitive Rust types:
    `Rc<u32>` is neither `Send` nor `Sync`, while remaining `Unpin`. -/
def primAutoTrait : AutoTrait → PrimTy → Prop
  | .send,  .rcU32 => False
  | .sync,  .rcU32 => False
  | .unpin, .rcU32 => True
  | _,      _      => True

/-! ## Section 2: Mutual Inductive Type Language, Substitutions, and Depth -/

mutual
  /-- Polymorphic Rust type AST supporting primitives, generic parameters, composites,
      niche `Option<Box<T>>`, arrays, async coroutine futures, and opaque aliases. -/
  inductive Ty where
    | prim (p : PrimTy)
    | param (i : ParamId)
    | pair (lhs rhs : Ty)
    | boxPtr (inner : Ty)
    | optBox (inner : Ty)
    | arr (elem : Ty) (len : Nat)
    | coroutine (output : Ty) (captured : TyList) (acrossAwait : TyList)
    | opaqueTy (id : OpaqueId) (args : TyList)

  /-- Structural list of types keeping all recursion strictly structural (zero `_unsafe_rec`). -/
  inductive TyList where
    | nil
    | cons (hd : Ty) (tl : TyList)
end

/-- Non-recursive structural fold combinators directly over kernel `Ty.rec` / `TyList.rec`
    so zero `._unsafe_rec` compiler helpers are ever generated in `env.constants`. -/
noncomputable def foldTy {α β : Type}
    (fPrim : PrimTy → α)
    (fParam : ParamId → α)
    (fPair : Ty → Ty → α → α → α)
    (fBox : Ty → α → α)
    (fOpt : Ty → α → α)
    (fArr : Ty → Nat → α → α)
    (fCoro : Ty → TyList → TyList → α → β → β → α)
    (fOpaq : OpaqueId → TyList → β → α)
    (fNil : β)
    (fCons : Ty → TyList → α → β → β) : Ty → α :=
  @Ty.rec (fun _ => α) (fun _ => β)
    fPrim fParam fPair fBox fOpt fArr fCoro fOpaq fNil fCons

noncomputable def foldTyList {α β : Type}
    (fPrim : PrimTy → α)
    (fParam : ParamId → α)
    (fPair : Ty → Ty → α → α → α)
    (fBox : Ty → α → α)
    (fOpt : Ty → α → α)
    (fArr : Ty → Nat → α → α)
    (fCoro : Ty → TyList → TyList → α → β → β → α)
    (fOpaq : OpaqueId → TyList → β → α)
    (fNil : β)
    (fCons : Ty → TyList → α → β → β) : TyList → β :=
  @TyList.rec (fun _ => α) (fun _ => β)
    fPrim fParam fPair fBox fOpt fArr fCoro fOpaq fNil fCons

def foldTyProp
    (fPrim : PrimTy → Prop)
    (fParam : ParamId → Prop)
    (fPair : Ty → Ty → Prop → Prop → Prop)
    (fBox : Ty → Prop → Prop)
    (fOpt : Ty → Prop → Prop)
    (fArr : Ty → Nat → Prop → Prop)
    (fCoro : Ty → TyList → TyList → Prop → Prop → Prop → Prop)
    (fOpaq : OpaqueId → TyList → Prop → Prop)
    (fNil : Prop)
    (fCons : Ty → TyList → Prop → Prop → Prop) : Ty → Prop :=
  @Ty.rec (fun _ => Prop) (fun _ => Prop)
    fPrim fParam fPair fBox fOpt fArr fCoro fOpaq fNil fCons

def foldTyListProp
    (fPrim : PrimTy → Prop)
    (fParam : ParamId → Prop)
    (fPair : Ty → Ty → Prop → Prop → Prop)
    (fBox : Ty → Prop → Prop)
    (fOpt : Ty → Prop → Prop)
    (fArr : Ty → Nat → Prop → Prop)
    (fCoro : Ty → TyList → TyList → Prop → Prop → Prop → Prop)
    (fOpaq : OpaqueId → TyList → Prop → Prop)
    (fNil : Prop)
    (fCons : Ty → TyList → Prop → Prop → Prop) : TyList → Prop :=
  @TyList.rec (fun _ => Prop) (fun _ => Prop)
    fPrim fParam fPair fBox fOpt fArr fCoro fOpaq fNil fCons

/-- Length of a `TyList` (pure kernel recursor, zero `._unsafe_rec`). -/
noncomputable def TyList.length : TyList → Nat :=
  foldTyList (fun _ => ()) (fun _ => ()) (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ => ())
    (fun _ _ _ => ()) (fun _ _ _ _ _ _ => ()) (fun _ _ _ => ()) 0 (fun _ _ _ ih => Nat.succ ih)

/-- 0-based positional lookup into a `TyList` (pure kernel recursor, zero `._unsafe_rec`). -/
noncomputable def TyList.get? : TyList → Nat → Option Ty :=
  foldTyList (fun _ => ()) (fun _ => ()) (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ => ())
    (fun _ _ _ => ()) (fun _ _ _ _ _ _ => ()) (fun _ _ _ => ())
    (fun _ => none)
    (fun hd _ _ ih n => match n with | 0 => some hd | n' + 1 => ih n')

/-- Structural AST depth of a `Ty` (used for cycle-impossibility sharpness proof `ce3`). -/
noncomputable def tyDepth : Ty → Nat :=
  foldTy
    (fun _ => 0) (fun _ => 0)
    (fun _ _ dl dr => Nat.succ (Nat.max dl dr))
    (fun _ d => Nat.succ d) (fun _ d => Nat.succ d) (fun _ _ d => Nat.succ d)
    (fun _ _ _ do_ dc da => Nat.succ (Nat.max do_ (Nat.max dc da)))
    (fun _ _ da => Nat.succ da)
    0 (fun _ _ dh dt => Nat.max dh dt)

noncomputable def tyListDepth : TyList → Nat :=
  foldTyList
    (fun _ => 0) (fun _ => 0)
    (fun _ _ dl dr => Nat.succ (Nat.max dl dr))
    (fun _ d => Nat.succ d) (fun _ d => Nat.succ d) (fun _ _ d => Nat.succ d)
    (fun _ _ _ do_ dc da => Nat.succ (Nat.max do_ (Nat.max dc da)))
    (fun _ _ da => Nat.succ da)
    0 (fun _ _ dh dt => Nat.max dh dt)

/-- Structural type substitution `ParamId → Ty`. -/
abbrev Subst := ParamId → Ty

def idSubst : Subst := fun i => Ty.param i

noncomputable def substTy (σ : Subst) : Ty → Ty :=
  foldTy
    (fun p => .prim p) (fun i => σ i)
    (fun _ _ l r => .pair l r)
    (fun _ inner => .boxPtr inner) (fun _ inner => .optBox inner)
    (fun _ n elem => .arr elem n)
    (fun _ _ _ out cap aw => .coroutine out cap aw)
    (fun id _ args => .opaqueTy id args)
    .nil (fun _ _ hd tl => .cons hd tl)

noncomputable def substTyList (σ : Subst) : TyList → TyList :=
  foldTyList
    (fun p => .prim p) (fun i => σ i)
    (fun _ _ l r => .pair l r)
    (fun _ inner => .boxPtr inner) (fun _ inner => .optBox inner)
    (fun _ n elem => .arr elem n)
    (fun _ _ _ out cap aw => .coroutine out cap aw)
    (fun id _ args => .opaqueTy id args)
    .nil (fun _ _ hd tl => .cons hd tl)

noncomputable def substComp (σ τ : Subst) : Subst := fun i => substTy σ (τ i)

/-- Substitution induced by a positional argument list `[a_0, ..., a_{k-1}]`. -/
noncomputable def argsSubst (args : TyList) : Subst :=
  fun i =>
    match TyList.get? args i with
    | some t => t
    | none => Ty.prim .unit

/-- Instantiate a declaration-site body `body` (with parameters `0..arity-1`) at `args`. -/
noncomputable def instantiate (body : Ty) (args : TyList) : Ty :=
  substTy (argsSubst args) body

theorem substTyList_length (σ : Subst) : ∀ xs : TyList, (substTyList σ xs).length = xs.length
  | .nil => rfl
  | .cons _ tl => congrArg Nat.succ (substTyList_length σ tl)

theorem substTyList_get? (σ : Subst) :
    ∀ (xs : TyList) (i : Nat),
      TyList.get? (substTyList σ xs) i =
        match TyList.get? xs i with
        | some t => some (substTy σ t)
        | none => none
  | .nil, _ => rfl
  | .cons _ _, 0 => rfl
  | .cons _ tl, i + 1 => substTyList_get? σ tl i

mutual
  theorem substTy_id : ∀ t : Ty, substTy idSubst t = t
    | .prim _ => rfl
    | .param _ => rfl
    | .pair l r => by
      change Ty.pair (substTy idSubst l) (substTy idSubst r) = Ty.pair l r
      rw [substTy_id l, substTy_id r]
    | .boxPtr inner => by
      change Ty.boxPtr (substTy idSubst inner) = Ty.boxPtr inner
      rw [substTy_id inner]
    | .optBox inner => by
      change Ty.optBox (substTy idSubst inner) = Ty.optBox inner
      rw [substTy_id inner]
    | .arr elem n => by
      change Ty.arr (substTy idSubst elem) n = Ty.arr elem n
      rw [substTy_id elem]
    | .coroutine out cap aw => by
      change Ty.coroutine (substTy idSubst out) (substTyList idSubst cap) (substTyList idSubst aw) =
        Ty.coroutine out cap aw
      rw [substTy_id out, substTyList_id cap, substTyList_id aw]
    | .opaqueTy id args => by
      change Ty.opaqueTy id (substTyList idSubst args) = Ty.opaqueTy id args
      rw [substTyList_id args]

  theorem substTyList_id : ∀ xs : TyList, substTyList idSubst xs = xs
    | .nil => rfl
    | .cons hd tl => by
      change TyList.cons (substTy idSubst hd) (substTyList idSubst tl) = TyList.cons hd tl
      rw [substTy_id hd, substTyList_id tl]
end

mutual
  theorem substTy_comp (σ τ : Subst) :
      ∀ t : Ty, substTy σ (substTy τ t) = substTy (substComp σ τ) t
    | .prim _ => rfl
    | .param _ => rfl
    | .pair l r => by
      change Ty.pair (substTy σ (substTy τ l)) (substTy σ (substTy τ r)) =
        Ty.pair (substTy (substComp σ τ) l) (substTy (substComp σ τ) r)
      rw [substTy_comp σ τ l, substTy_comp σ τ r]
    | .boxPtr inner => by
      change Ty.boxPtr (substTy σ (substTy τ inner)) = Ty.boxPtr (substTy (substComp σ τ) inner)
      rw [substTy_comp σ τ inner]
    | .optBox inner => by
      change Ty.optBox (substTy σ (substTy τ inner)) = Ty.optBox (substTy (substComp σ τ) inner)
      rw [substTy_comp σ τ inner]
    | .arr elem n => by
      change Ty.arr (substTy σ (substTy τ elem)) n = Ty.arr (substTy (substComp σ τ) elem) n
      rw [substTy_comp σ τ elem]
    | .coroutine out cap aw => by
      change Ty.coroutine (substTy σ (substTy τ out))
          (substTyList σ (substTyList τ cap)) (substTyList σ (substTyList τ aw)) =
        Ty.coroutine (substTy (substComp σ τ) out)
          (substTyList (substComp σ τ) cap) (substTyList (substComp σ τ) aw)
      rw [substTy_comp σ τ out, substTyList_comp σ τ cap, substTyList_comp σ τ aw]
    | .opaqueTy id args => by
      change Ty.opaqueTy id (substTyList σ (substTyList τ args)) =
        Ty.opaqueTy id (substTyList (substComp σ τ) args)
      rw [substTyList_comp σ τ args]

  theorem substTyList_comp (σ τ : Subst) :
      ∀ xs : TyList, substTyList σ (substTyList τ xs) = substTyList (substComp σ τ) xs
    | .nil => rfl
    | .cons hd tl => by
      change TyList.cons (substTy σ (substTy τ hd)) (substTyList σ (substTyList τ tl)) =
        TyList.cons (substTy (substComp σ τ) hd) (substTyList (substComp σ τ) tl)
      rw [substTy_comp σ τ hd, substTyList_comp σ τ tl]
end

/-- Free parameter occurrence predicate (pure kernel recursor, zero `._unsafe_rec`). -/
def HasParam (p : ParamId) : Ty → Prop :=
  foldTyProp
    (fun _ => False) (fun i => i = p)
    (fun _ _ l r => l ∨ r)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∨ c ∨ a)
    (fun _ _ a => a)
    False (fun _ _ h t => h ∨ t)

def HasParamList (p : ParamId) : TyList → Prop :=
  foldTyListProp
    (fun _ => False) (fun i => i = p)
    (fun _ _ l r => l ∨ r)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∨ c ∨ a)
    (fun _ _ a => a)
    False (fun _ _ h t => h ∨ t)

mutual
  theorem substTy_congr {σ τ : Subst} :
      ∀ (t : Ty), (∀ p, HasParam p t → σ p = τ p) → substTy σ t = substTy τ t
    | .prim _, _ => rfl
    | .param i, h => h i rfl
    | .pair l r, h => by
      change Ty.pair (substTy σ l) (substTy σ r) = Ty.pair (substTy τ l) (substTy τ r)
      rw [substTy_congr l (fun p hp => h p (Or.inl hp)),
          substTy_congr r (fun p hp => h p (Or.inr hp))]
    | .boxPtr inner, h => by
      change Ty.boxPtr (substTy σ inner) = Ty.boxPtr (substTy τ inner)
      rw [substTy_congr inner h]
    | .optBox inner, h => by
      change Ty.optBox (substTy σ inner) = Ty.optBox (substTy τ inner)
      rw [substTy_congr inner h]
    | .arr elem n, h => by
      change Ty.arr (substTy σ elem) n = Ty.arr (substTy τ elem) n
      rw [substTy_congr elem h]
    | .coroutine out cap aw, h => by
      change Ty.coroutine (substTy σ out) (substTyList σ cap) (substTyList σ aw) =
        Ty.coroutine (substTy τ out) (substTyList τ cap) (substTyList τ aw)
      rw [substTy_congr out (fun p hp => h p (Or.inl hp)),
          substTyList_congr cap (fun p hp => h p (Or.inr (Or.inl hp))),
          substTyList_congr aw (fun p hp => h p (Or.inr (Or.inr hp)))]
    | .opaqueTy id args, h => by
      change Ty.opaqueTy id (substTyList σ args) = Ty.opaqueTy id (substTyList τ args)
      rw [substTyList_congr args h]

  theorem substTyList_congr {σ τ : Subst} :
      ∀ (xs : TyList), (∀ p, HasParamList p xs → σ p = τ p) → substTyList σ xs = substTyList τ xs
    | .nil, _ => rfl
    | .cons hd tl, h => by
      change TyList.cons (substTy σ hd) (substTyList σ tl) =
        TyList.cons (substTy τ hd) (substTyList τ tl)
      rw [substTy_congr hd (fun p hp => h p (Or.inl hp)),
          substTyList_congr tl (fun p hp => h p (Or.inr hp))]
end

/- Well-kindedness of a declaration-site hidden witness: every free parameter index is `< arity`. -/
def TyVarsIn (arity : Nat) (t : Ty) : Prop :=
  ∀ p, HasParam p t → p < arity

/-- A type contains no opaque aliases anywhere in its AST. -/
def IsConcrete : Ty → Prop :=
  foldTyProp
    (fun _ => True) (fun _ => True)
    (fun _ _ l r => l ∧ r)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∧ c ∧ a)
    (fun _ _ _ => False)
    True (fun _ _ h t => h ∧ t)

def IsConcreteList : TyList → Prop :=
  foldTyListProp
    (fun _ => True) (fun _ => True)
    (fun _ _ l r => l ∧ r)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∧ c ∧ a)
    (fun _ _ _ => False)
    True (fun _ _ h t => h ∧ t)

mutual
  theorem isConcrete_substTy (σ : Subst) (hσ : ∀ p, IsConcrete (σ p)) :
      ∀ t : Ty, IsConcrete t → IsConcrete (substTy σ t)
    | .prim _, _ => trivial
    | .param i, _ => hσ i
    | .pair l r, h => ⟨isConcrete_substTy σ hσ l h.1, isConcrete_substTy σ hσ r h.2⟩
    | .boxPtr inner, h => isConcrete_substTy σ hσ inner h
    | .optBox inner, h => isConcrete_substTy σ hσ inner h
    | .arr elem _, h => isConcrete_substTy σ hσ elem h
    | .coroutine out cap aw, h =>
      ⟨isConcrete_substTy σ hσ out h.1,
       isConcreteList_substTyList σ hσ cap h.2.1,
       isConcreteList_substTyList σ hσ aw h.2.2⟩
    | .opaqueTy _ _, h => False.elim h

  theorem isConcreteList_substTyList (σ : Subst) (hσ : ∀ p, IsConcrete (σ p)) :
      ∀ xs : TyList, IsConcreteList xs → IsConcreteList (substTyList σ xs)
    | .nil, _ => trivial
    | .cons hd tl, h =>
      ⟨isConcrete_substTy σ hσ hd h.1, isConcreteList_substTyList σ hσ tl h.2⟩
end

theorem tyList_get?_isConcrete :
    ∀ (xs : TyList) (i : Nat) (t : Ty),
      IsConcreteList xs → TyList.get? xs i = some t → IsConcrete t
  | .nil, _, _, _, hget => nomatch hget
  | .cons _ _, 0, _, h, hget => by cases hget; exact h.1
  | .cons _ tl, i + 1, t, h, hget => tyList_get?_isConcrete tl i t h.2 hget

theorem isConcrete_instantiate (body : Ty) (args : TyList)
    (hb : IsConcrete body) (ha : IsConcreteList args) :
    IsConcrete (instantiate body args) := by
  apply isConcrete_substTy (argsSubst args) _ body hb
  intro p
  unfold argsSubst
  cases hget : TyList.get? args p with
  | none => trivial
  | some a => exact tyList_get?_isConcrete args p a ha hget

/-- Membership of an opaque identifier in a type AST (`HasRecursiveOpaque` visitor model). -/
def MentionsOpaque (oid : OpaqueId) : Ty → Prop :=
  foldTyProp
    (fun _ => False) (fun _ => False)
    (fun _ _ l r => l ∨ r)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∨ c ∨ a)
    (fun id _ a => id = oid ∨ a)
    False (fun _ _ h t => h ∨ t)

def MentionsOpaqueList (oid : OpaqueId) : TyList → Prop :=
  foldTyListProp
    (fun _ => False) (fun _ => False)
    (fun _ _ l r => l ∨ r)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∨ c ∨ a)
    (fun id _ a => id = oid ∨ a)
    False (fun _ _ h t => h ∨ t)

/-- Stratified rank bound: every opaque mentioned inside `t` has rank `< r`. -/
def OpaqueRankLt (rank : OpaqueId → Nat) (r : Nat) : Ty → Prop :=
  foldTyProp
    (fun _ => True) (fun _ => True)
    (fun _ _ l rt => l ∧ rt)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∧ c ∧ a)
    (fun id _ a => rank id < r ∧ a)
    True (fun _ _ h t => h ∧ t)

def OpaqueRankLtList (rank : OpaqueId → Nat) (r : Nat) : TyList → Prop :=
  foldTyListProp
    (fun _ => True) (fun _ => True)
    (fun _ _ l rt => l ∧ rt)
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ _ o c a => o ∧ c ∧ a)
    (fun id _ a => rank id < r ∧ a)
    True (fun _ _ h t => h ∧ t)

mutual
  theorem opaqueRankLt_zero_isConcrete (rank : OpaqueId → Nat) :
      ∀ t : Ty, OpaqueRankLt rank 0 t → IsConcrete t
    | .prim _, _ => trivial
    | .param _, _ => trivial
    | .pair l r, h => ⟨opaqueRankLt_zero_isConcrete rank l h.1,
                       opaqueRankLt_zero_isConcrete rank r h.2⟩
    | .boxPtr inner, h => opaqueRankLt_zero_isConcrete rank inner h
    | .optBox inner, h => opaqueRankLt_zero_isConcrete rank inner h
    | .arr elem _, h => opaqueRankLt_zero_isConcrete rank elem h
    | .coroutine out cap aw, h =>
      ⟨opaqueRankLt_zero_isConcrete rank out h.1,
       opaqueRankLtList_zero_isConcrete rank cap h.2.1,
       opaqueRankLtList_zero_isConcrete rank aw h.2.2⟩
    | .opaqueTy id _, h => False.elim (Nat.not_lt_zero (rank id) h.1)

  theorem opaqueRankLtList_zero_isConcrete (rank : OpaqueId → Nat) :
      ∀ xs : TyList, OpaqueRankLtList rank 0 xs → IsConcreteList xs
    | .nil, _ => trivial
    | .cons hd tl, h => ⟨opaqueRankLt_zero_isConcrete rank hd h.1,
                         opaqueRankLtList_zero_isConcrete rank tl h.2⟩
end

mutual
  theorem opaqueRankLt_mono (rank : OpaqueId → Nat) {r1 r2 : Nat} (hle : r1 ≤ r2) :
      ∀ t : Ty, OpaqueRankLt rank r1 t → OpaqueRankLt rank r2 t
    | .prim _, _ => trivial
    | .param _, _ => trivial
    | .pair l r, h => ⟨opaqueRankLt_mono rank hle l h.1, opaqueRankLt_mono rank hle r h.2⟩
    | .boxPtr inner, h => opaqueRankLt_mono rank hle inner h
    | .optBox inner, h => opaqueRankLt_mono rank hle inner h
    | .arr elem _, h => opaqueRankLt_mono rank hle elem h
    | .coroutine out cap aw, h =>
      ⟨opaqueRankLt_mono rank hle out h.1,
       opaqueRankLtList_mono rank hle cap h.2.1,
       opaqueRankLtList_mono rank hle aw h.2.2⟩
    | .opaqueTy _id args, h =>
      ⟨Nat.lt_of_lt_of_le h.1 hle, opaqueRankLtList_mono rank hle args h.2⟩

  theorem opaqueRankLtList_mono (rank : OpaqueId → Nat) {r1 r2 : Nat} (hle : r1 ≤ r2) :
      ∀ xs : TyList, OpaqueRankLtList rank r1 xs → OpaqueRankLtList rank r2 xs
    | .nil, _ => trivial
    | .cons hd tl, h =>
      ⟨opaqueRankLt_mono rank hle hd h.1, opaqueRankLtList_mono rank hle tl h.2⟩
end

/-! ## Section 3: Defining Scopes (`#[define_opaque]`, ATPIT, RPIT) and Bijective Unification -/

/- Mirrors `rustc_hir::OpaqueTyOrigin` (`FnReturn`, `AsyncFn`, `TyAlias { in_assoc_ty }`). -/
inductive OpaqueOrigin where
  | rpit (ownerItem : ItemId)
  | atpit (implBlock : ItemId) (isFinal : Bool)
  | tait

/-- Mirrors `OpaqueTypeCollector` metadata on a candidate defining item
    (`compiler/rustc_ty_utils/src/opaque_types.rs:16-50, 175-196`). -/
structure ItemMeta where
  itemId : ItemId
  implBlock : Option ItemId
  hasDefineOpaqueAttr : Bool
  defineOpaqueTargets : List OpaqueId

/-- Membership in a plain `List Nat` (pure kernel `List.rec`, zero `._unsafe_rec`). -/
def listMem (x : Nat) (xs : List Nat) : Prop :=
  List.rec False (fun hd _ ih => x = hd ∨ ih) xs

/-- Defining-scope authorization matching `OpaqueTypeCollector::visit_opaque_ty` and
    `collect_taits_from_defines_attr` (`rustc_ty_utils/src/opaque_types.rs:102-196`). -/
def canDefine (item : ItemMeta) (oid : OpaqueId) (origin : OpaqueOrigin) : Prop :=
  match origin with
  | .rpit owner => item.itemId = owner
  | .atpit blk isFinal =>
      isFinal = true ∧ item.implBlock = some blk ∧ item.hasDefineOpaqueAttr = false
  | .tait =>
      item.hasDefineOpaqueAttr = true ∧ listMem oid item.defineOpaqueTargets

/-- Unmarked free functions (`hasDefineOpaqueAttr = false`) CANNOT define a TAIT. -/
theorem unmarked_item_cannot_define_tait (item : ItemMeta) (oid : OpaqueId)
    (h : item.hasDefineOpaqueAttr = false) :
    ¬ canDefine item oid .tait := by
  intro hdef
  have htrue : item.hasDefineOpaqueAttr = true := hdef.1
  rw [h] at htrue
  cases htrue

/-- Empty `#[define_opaque()]` on an impl method suppresses implicit ATPIT defining authority. -/
theorem empty_define_opaque_suppresses_atpit (item : ItemMeta) (oid : OpaqueId) (blk : ItemId)
    (h : item.hasDefineOpaqueAttr = true) :
    ¬ canDefine item oid (.atpit blk true) := by
  intro hdef
  have hfalse : item.hasDefineOpaqueAttr = false := hdef.2.2
  rw [h] at hfalse
  cases hfalse

/-- A recorded use of `opaque oid args := rhs` inside item `item`. -/
structure OpaqueUse where
  item : ItemMeta
  oid : OpaqueId
  args : TyList
  rhs : Ty

/-- Higher-order pattern condition (`opaque_type_has_defining_use_args`):
    `args` has length `arity`, every argument is a universal `Ty.param`, and distinct
    argument positions carry distinct parameters (`fwd : Fin arity ↪ ParamId` with left inverse `inv`). -/
structure BijectiveArgs (arity : Nat) (args : TyList) where
  lenEq : args.length = arity
  fwd : Nat → ParamId
  inv : ParamId → Nat
  atIdx : ∀ k, k < arity → TyList.get? args k = some (Ty.param (fwd k))
  leftInv : ∀ k, k < arity → inv (fwd k) = k

/-- Every parameter appearing in `rhs` must lie in the image of `fwd` (`ReverseMapper` soundness). -/
def CapturedByBijection {arity : Nat} {args : TyList}
    (bij : BijectiveArgs arity args) (rhs : Ty) : Prop :=
  ∀ p, HasParam p rhs → ∃ k, k < arity ∧ bij.fwd k = p

/-- `ReverseMapper` transformation mapping caller parameters back to declaration parameters `0..arity-1`. -/
noncomputable def reverseMap {arity : Nat} {args : TyList} (bij : BijectiveArgs arity args) (rhs : Ty) : Ty :=
  substTy (fun p => Ty.param (bij.inv p)) rhs

/-- `reverseMap` always yields a well-kinded declaration-site witness (`TyVarsIn arity`). -/
theorem reverseMap_wellKinded {arity : Nat} {args : TyList}
    (bij : BijectiveArgs arity args) (rhs : Ty)
    (hcap : CapturedByBijection bij rhs) :
    TyVarsIn arity (reverseMap bij rhs) := by
  intro q hq
  exact go rhs hcap q hq
where
  go : ∀ (t : Ty), CapturedByBijection bij t →
       ∀ q, HasParam q (substTy (fun p => Ty.param (bij.inv p)) t) → q < arity
    | .prim _, _, _, hq => False.elim hq
    | .param p, hc, q, hq => by
      have hqp : bij.inv p = q := hq
      rcases hc p rfl with ⟨k, hk, hfk⟩
      rw [← hqp, ← hfk, bij.leftInv k hk]
      exact hk
    | .pair l r, hc, q, hq =>
      match hq with
      | Or.inl hl => go l (fun p hp => hc p (Or.inl hp)) q hl
      | Or.inr hr => go r (fun p hp => hc p (Or.inr hp)) q hr
    | .boxPtr inner, hc, q, hq => go inner hc q hq
    | .optBox inner, hc, q, hq => go inner hc q hq
    | .arr elem _, hc, q, hq => go elem hc q hq
    | .coroutine out cap aw, hc, q, hq =>
      match hq with
      | Or.inl ho => go out (fun p hp => hc p (Or.inl hp)) q ho
      | Or.inr (Or.inl hcap') =>
        goList cap (fun p hp => hc p (Or.inr (Or.inl hp))) q hcap'
      | Or.inr (Or.inr haw') =>
        goList aw (fun p hp => hc p (Or.inr (Or.inr hp))) q haw'
    | .opaqueTy _ as_, hc, q, hq => goList as_ hc q hq
  goList : ∀ (xs : TyList), (∀ p, HasParamList p xs → ∃ k, k < arity ∧ bij.fwd k = p) →
           ∀ q, HasParamList q (substTyList (fun p => Ty.param (bij.inv p)) xs) → q < arity
    | .nil, _, _, hq => False.elim hq
    | .cons hd tl, hc, q, hq =>
      match hq with
      | Or.inl hh => go hd (fun p hp => hc p (Or.inl hp)) q hh
      | Or.inr ht => goList tl (fun p hp => hc p (Or.inr hp)) q ht

/-- Instantiating `reverseMap bij rhs` with `args` recovers `rhs` identically. -/
theorem instantiate_reverseMap_eq {arity : Nat} {args : TyList}
    (bij : BijectiveArgs arity args) (rhs : Ty)
    (hcap : CapturedByBijection bij rhs) :
    instantiate (reverseMap bij rhs) args = rhs := by
  unfold instantiate reverseMap
  rw [substTy_comp]
  have hcongr :
      substTy (substComp (argsSubst args) (fun p => Ty.param (bij.inv p))) rhs =
      substTy idSubst rhs := by
    apply substTy_congr
    intro p hp
    rcases hcap p hp with ⟨k, hk, hfk⟩
    unfold substComp argsSubst idSubst
    change (match TyList.get? args (bij.inv p) with | some t => t | none => Ty.prim .unit) =
      Ty.param p
    rw [← hfk, bij.leftInv k hk, bij.atIdx k hk]
  rw [hcongr, substTy_id]

/-- Applying `reverseMap` to an instantiated well-kinded witness recovers the exact witness. -/
theorem reverseMap_instantiate_eq {arity : Nat} {args : TyList}
    (bij : BijectiveArgs arity args) (w : Ty) (hw : TyVarsIn arity w) :
    reverseMap bij (instantiate w args) = w := by
  unfold reverseMap instantiate
  rw [substTy_comp]
  have hcongr :
      substTy (substComp (fun p => Ty.param (bij.inv p)) (argsSubst args)) w =
      substTy idSubst w := by
    apply substTy_congr
    intro k hk
    have hlt : k < arity := hw k hk
    unfold substComp argsSubst idSubst
    change substTy (fun p => Ty.param (bij.inv p))
      (match TyList.get? args k with | some t => t | none => Ty.prim .unit) = Ty.param k
    rw [bij.atIdx k hlt]
    change Ty.param (bij.inv (bij.fwd k)) = Ty.param k
    rw [bij.leftInv k hlt]
  rw [hcongr, substTy_id]

/-- **Injectivity of Bijective Instantiation**: two well-kinded declaration-site witnesses
    that instantiate identically under one bijective defining use MUST be syntactically equal. -/
theorem witness_unique_of_bijective_inst {arity : Nat} {args : TyList}
    (bij : BijectiveArgs arity args) {w1 w2 : Ty}
    (hw1 : TyVarsIn arity w1) (hw2 : TyVarsIn arity w2)
    (heq : instantiate w1 args = instantiate w2 args) :
    w1 = w2 := by
  have h1 := reverseMap_instantiate_eq bij w1 hw1
  have h2 := reverseMap_instantiate_eq bij w2 hw2
  rw [← h1, heq, h2]

/-- Certified defining use carrying scope authorization, bijective argument map, and capture proof. -/
structure ValidDefiningUse (oid : OpaqueId) (arity : Nat) (origin : OpaqueOrigin) where
  use : OpaqueUse
  idEq : use.oid = oid
  authorized : canDefine use.item oid origin
  bij : BijectiveArgs arity use.args
  captured : CapturedByBijection bij use.rhs

/-- Coherence across all defining uses of an opaque declaration:
    at least one defining use exists (not unconstrained), and all defining uses agree
    after `ReverseMapper` normalization (`add_hidden_type` / `TaitConstraintLocator::insert_found`). -/
structure CoherentDefiningUses (oid : OpaqueId) (arity : Nat) (origin : OpaqueOrigin) where
  uses : List (ValidDefiningUse oid arity origin)
  nonempty : ∃ u, u ∈ uses
  pairwiseAgree : ∀ u1 u2, u1 ∈ uses → u2 ∈ uses →
    reverseMap u1.bij u1.use.rhs = reverseMap u2.bij u2.use.rhs

/-- **Main Theorem 1 (`coherentDefiningUses_unique_concrete_witness`)**:
    Bijective parameter instantiation + consistent `#[define_opaque]` / ATPIT / RPIT defining uses
    uniquely determine a well-kinded declaration-site witness `w` (`TyVarsIn arity w`) that:
      1. Instantiates to `u.use.rhs` at EVERY defining use `u`,
      2. Commutes with EVERY monomorphization substitution `σ` (`Reveal::All`), and
      3. Is strictly unique among all well-kinded witnesses agreeing with the defining uses. -/
theorem coherentDefiningUses_unique_concrete_witness
    {oid : OpaqueId} {arity : Nat} {origin : OpaqueOrigin}
    (coh : CoherentDefiningUses oid arity origin) :
    ∃ w : Ty,
      TyVarsIn arity w ∧
      (∀ u, u ∈ coh.uses → instantiate w u.use.args = u.use.rhs) ∧
      (∀ u σ, u ∈ coh.uses → substTy σ (instantiate w u.use.args) = substTy σ u.use.rhs) ∧
      (∀ w', TyVarsIn arity w' →
        (∀ u, u ∈ coh.uses → instantiate w' u.use.args = u.use.rhs) → w' = w) := by
  rcases coh.nonempty with ⟨u0, hu0⟩
  let w := reverseMap u0.bij u0.use.rhs
  refine ⟨w, reverseMap_wellKinded u0.bij u0.use.rhs u0.captured, ?_, ?_, ?_⟩
  · intro u hu
    have hEq : w = reverseMap u.bij u.use.rhs := coh.pairwiseAgree u0 u hu0 hu
    rw [hEq]
    exact instantiate_reverseMap_eq u.bij u.use.rhs u.captured
  · intro u σ hu
    have hEq : w = reverseMap u.bij u.use.rhs := coh.pairwiseAgree u0 u hu0 hu
    rw [hEq, instantiate_reverseMap_eq u.bij u.use.rhs u.captured]
  · intro w' hw' hinst
    have h0 : instantiate w' u0.use.args = u0.use.rhs := hinst u0 hu0
    have hw0 : instantiate w u0.use.args = u0.use.rhs :=
      instantiate_reverseMap_eq u0.bij u0.use.rhs u0.captured
    exact witness_unique_of_bijective_inst u0.bij hw'
      (reverseMap_wellKinded u0.bij u0.use.rhs u0.captured) (Eq.trans h0 hw0.symm)

/-! ## Section 4: Stratified `Reveal::All` Erasure, Three-Phase Visibility, Auto-Traits, and RTN -/

/-- Three visibility regimes modeling `TypingMode` transitions in rustc. -/
inductive RevealTier where
  | userFacing
  | definingScope (defined : OpaqueId → Prop)
  | revealAll

/-- Declaration of an opaque type with arity, origin, explicit item trait bounds,
    explicit auto-trait bounds, and its coherent declaration-site hidden witness. -/
structure OpaqueDecl where
  arity : Nat
  origin : OpaqueOrigin
  itemTraitBounds : TraitId → Prop
  itemAutoBounds : AutoTrait → Prop
  witness : Ty

/-- Stratified opaque table + trait implementation relation + RPITIT coroutine table. -/
structure World where
  decls : OpaqueId → OpaqueDecl
  rank : OpaqueId → Nat
  stratified : ∀ oid, OpaqueRankLt rank (rank oid) (decls oid).witness
  witnessWellKinded : ∀ oid, TyVarsIn (decls oid).arity (decls oid).witness
  /-- Concrete trait implementation relation on fully erased (opaque-free) types. -/
  concreteTrait : TraitId → Ty → Prop
  /-- Synthetic RPITIT coroutine future returned by `<SelfTy as Trait>::method(..)`. -/
  rpititFuture : Ty → AssocMethodId → Ty

/-- Strictly structural rank-indexed opaque erasure (`Reveal::All` / `TypingMode::PostAnalysis` /
    `TypingMode::Codegen`). Uses pure kernel `Nat.rec` + `Ty.rec` / `TyList.rec` (zero `._unsafe_rec`). -/
noncomputable def eraseRank.eraseRankStep (world : World) (recPrev : Ty → Ty) : Ty → Ty :=
  foldTy
    (fun p => .prim p) (fun i => .param i)
    (fun _ _ l rt => .pair l rt)
    (fun _ inner => .boxPtr inner) (fun _ inner => .optBox inner)
    (fun _ n elem => .arr elem n)
    (fun _ _ _ out cap aw => .coroutine out cap aw)
    (fun oid _ eArgs => instantiate (recPrev (world.decls oid).witness) eArgs)
    .nil (fun _ _ hd tl => .cons hd tl)

noncomputable def eraseRank.eraseRankStepList (world : World) (recPrev : Ty → Ty) : TyList → TyList :=
  foldTyList
    (fun p => .prim p) (fun i => .param i)
    (fun _ _ l rt => .pair l rt)
    (fun _ inner => .boxPtr inner) (fun _ inner => .optBox inner)
    (fun _ n elem => .arr elem n)
    (fun _ _ _ out cap aw => .coroutine out cap aw)
    (fun oid _ eArgs => instantiate (recPrev (world.decls oid).witness) eArgs)
    .nil (fun _ _ hd tl => .cons hd tl)

noncomputable def eraseRank (world : World) (r : Nat) : Ty → Ty :=
  Nat.rec (fun t => t) (fun _ prev t => eraseRank.eraseRankStep world prev t) r

noncomputable def eraseRankList (world : World) : Nat → TyList → TyList
  | 0, xs => xs
  | r + 1, xs => eraseRank.eraseRankStepList world (eraseRank world r) xs

/-- Exact upper bound on opaque ranks occurring in `t` (pure kernel recursor, zero `._unsafe_rec`). -/
noncomputable def maxRankBound (rank : OpaqueId → Nat) : Ty → Nat :=
  foldTy
    (fun _ => 0) (fun _ => 0)
    (fun _ _ l r => Nat.max l r)
    (fun _ inner => inner) (fun _ inner => inner) (fun _ _ elem => elem)
    (fun _ _ _ out cap aw => Nat.max out (Nat.max cap aw))
    (fun oid _ args => Nat.max (Nat.succ (rank oid)) args)
    0 (fun _ _ hd tl => Nat.max hd tl)

noncomputable def maxRankBoundList (rank : OpaqueId → Nat) : TyList → Nat :=
  foldTyList
    (fun _ => 0) (fun _ => 0)
    (fun _ _ l r => Nat.max l r)
    (fun _ inner => inner) (fun _ inner => inner) (fun _ _ elem => elem)
    (fun _ _ _ out cap aw => Nat.max out (Nat.max cap aw))
    (fun oid _ args => Nat.max (Nat.succ (rank oid)) args)
    0 (fun _ _ hd tl => Nat.max hd tl)

mutual
  theorem opaqueRankLt_maxRankBound (rank : OpaqueId → Nat) :
      ∀ t : Ty, OpaqueRankLt rank (maxRankBound rank t) t
    | .prim _ => trivial
    | .param _ => trivial
    | .pair l r =>
      ⟨opaqueRankLt_mono rank (nat_max_ge_left _ _) l (opaqueRankLt_maxRankBound rank l),
       opaqueRankLt_mono rank (nat_max_ge_right _ _) r (opaqueRankLt_maxRankBound rank r)⟩
    | .boxPtr inner => opaqueRankLt_maxRankBound rank inner
    | .optBox inner => opaqueRankLt_maxRankBound rank inner
    | .arr elem _ => opaqueRankLt_maxRankBound rank elem
    | .coroutine out cap aw =>
      let mInner := Nat.max (maxRankBoundList rank cap) (maxRankBoundList rank aw)
      ⟨opaqueRankLt_mono rank (nat_max_ge_left (maxRankBound rank out) mInner)
         out (opaqueRankLt_maxRankBound rank out),
       opaqueRankLtList_mono rank
         (nat_le_trans (nat_max_ge_left _ _) (nat_max_ge_right (maxRankBound rank out) mInner))
         cap (opaqueRankLtList_maxRankBound rank cap),
       opaqueRankLtList_mono rank
         (nat_le_trans (nat_max_ge_right _ _) (nat_max_ge_right (maxRankBound rank out) mInner))
         aw (opaqueRankLtList_maxRankBound rank aw)⟩
    | .opaqueTy oid args =>
      ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self (rank oid)) (nat_max_ge_left _ _),
       opaqueRankLtList_mono rank (nat_max_ge_right _ _) args (opaqueRankLtList_maxRankBound rank args)⟩

  theorem opaqueRankLtList_maxRankBound (rank : OpaqueId → Nat) :
      ∀ xs : TyList, OpaqueRankLtList rank (maxRankBoundList rank xs) xs
    | .nil => trivial
    | .cons hd tl =>
      ⟨opaqueRankLt_mono rank (nat_max_ge_left _ _) hd (opaqueRankLt_maxRankBound rank hd),
       opaqueRankLtList_mono rank (nat_max_ge_right _ _) tl (opaqueRankLtList_maxRankBound rank tl)⟩
end

/- `eraseRank world r t` produces a completely concrete type whenever `OpaqueRankLt world.rank r t`. -/
theorem eraseRank_isConcrete (world : World) :
    ∀ (r : Nat) (t : Ty), OpaqueRankLt world.rank r t → IsConcrete (eraseRank world r t) := by
  intro r
  induction r with
  | zero =>
    intro t h
    exact opaqueRankLt_zero_isConcrete world.rank t h
  | succ k ih =>
    exact go k ih
where
  go (k : Nat) (ih : ∀ t, OpaqueRankLt world.rank k t → IsConcrete (eraseRank world k t)) :
      ∀ t : Ty, OpaqueRankLt world.rank (k + 1) t → IsConcrete (eraseRank world (k + 1) t)
    | .prim _, _ => trivial
    | .param _, _ => trivial
    | .pair l r, h => ⟨go k ih l h.1, go k ih r h.2⟩
    | .boxPtr inner, h => go k ih inner h
    | .optBox inner, h => go k ih inner h
    | .arr elem _, h => go k ih elem h
    | .coroutine out cap aw, h =>
      ⟨go k ih out h.1, goList k ih cap h.2.1, goList k ih aw h.2.2⟩
    | .opaqueTy oid args, h => by
      change IsConcrete (instantiate (eraseRank world k (world.decls oid).witness)
        (eraseRank.eraseRankStepList world (eraseRank world k) args))
      have hRankLe : world.rank oid ≤ k := Nat.le_of_lt_succ h.1
      have hWitConc : IsConcrete (eraseRank world k (world.decls oid).witness) :=
        ih _ (opaqueRankLt_mono world.rank hRankLe _ (world.stratified oid))
      have hArgsConc : IsConcreteList (eraseRank.eraseRankStepList world (eraseRank world k) args) :=
        goList k ih args h.2
      exact isConcrete_instantiate _ _ hWitConc hArgsConc
  goList (k : Nat) (ih : ∀ t, OpaqueRankLt world.rank k t → IsConcrete (eraseRank world k t)) :
      ∀ xs : TyList, OpaqueRankLtList world.rank (k + 1) xs →
        IsConcreteList (eraseRank.eraseRankStepList world (eraseRank world k) xs)
    | .nil, _ => trivial
    | .cons hd tl, h => ⟨go k ih hd h.1, goList k ih tl h.2⟩

/-- `eraseRank` stabilizes immediately once `r` exceeds the rank of all opaques in `t`. -/
theorem eraseRank_succ_eq (world : World) :
    ∀ (r : Nat) (t : Ty), OpaqueRankLt world.rank r t →
      eraseRank world (r + 1) t = eraseRank world r t := by
  intro r
  induction r with
  | zero =>
    intro t h
    exact zeroStep t (opaqueRankLt_zero_isConcrete world.rank t h)
  | succ k ih =>
    exact stepEq k ih
where
  zeroStep : ∀ t : Ty, IsConcrete t → eraseRank world 1 t = t
    | .prim _, _ => rfl
    | .param _, _ => rfl
    | .pair l r, h => by
      change Ty.pair (eraseRank world 1 l) (eraseRank world 1 r) = Ty.pair l r
      rw [zeroStep l h.1, zeroStep r h.2]
    | .boxPtr inner, h => by
      change Ty.boxPtr (eraseRank world 1 inner) = Ty.boxPtr inner
      rw [zeroStep inner h]
    | .optBox inner, h => by
      change Ty.optBox (eraseRank world 1 inner) = Ty.optBox inner
      rw [zeroStep inner h]
    | .arr elem n, h => by
      change Ty.arr (eraseRank world 1 elem) n = Ty.arr elem n
      rw [zeroStep elem h]
    | .coroutine out cap aw, h => by
      change Ty.coroutine (eraseRank world 1 out)
        (eraseRank.eraseRankStepList world (eraseRank world 0) cap)
        (eraseRank.eraseRankStepList world (eraseRank world 0) aw) =
        Ty.coroutine out cap aw
      rw [zeroStep out h.1, zeroStepList cap h.2.1, zeroStepList aw h.2.2]
    | .opaqueTy _ _, h => False.elim h
  zeroStepList : ∀ xs : TyList, IsConcreteList xs →
      eraseRank.eraseRankStepList world (eraseRank world 0) xs = xs
    | .nil, _ => rfl
    | .cons hd tl, h => by
      change TyList.cons (eraseRank world 1 hd)
        (eraseRank.eraseRankStepList world (eraseRank world 0) tl) = TyList.cons hd tl
      rw [zeroStep hd h.1, zeroStepList tl h.2]
  stepEq (k : Nat)
      (ih : ∀ t, OpaqueRankLt world.rank k t → eraseRank world (k + 1) t = eraseRank world k t) :
      ∀ t : Ty, OpaqueRankLt world.rank (k + 1) t →
        eraseRank world (k + 2) t = eraseRank world (k + 1) t
    | .prim _, _ => rfl
    | .param _, _ => rfl
    | .pair l r, h => by
      change Ty.pair (eraseRank world (k + 2) l) (eraseRank world (k + 2) r) =
        Ty.pair (eraseRank world (k + 1) l) (eraseRank world (k + 1) r)
      rw [stepEq k ih l h.1, stepEq k ih r h.2]
    | .boxPtr inner, h => by
      change Ty.boxPtr (eraseRank world (k + 2) inner) = Ty.boxPtr (eraseRank world (k + 1) inner)
      rw [stepEq k ih inner h]
    | .optBox inner, h => by
      change Ty.optBox (eraseRank world (k + 2) inner) = Ty.optBox (eraseRank world (k + 1) inner)
      rw [stepEq k ih inner h]
    | .arr elem n, h => by
      change Ty.arr (eraseRank world (k + 2) elem) n = Ty.arr (eraseRank world (k + 1) elem) n
      rw [stepEq k ih elem h]
    | .coroutine out cap aw, h => by
      change Ty.coroutine (eraseRank world (k + 2) out)
        (eraseRank.eraseRankStepList world (eraseRank world (k + 1)) cap)
        (eraseRank.eraseRankStepList world (eraseRank world (k + 1)) aw) =
        Ty.coroutine (eraseRank world (k + 1) out)
          (eraseRank.eraseRankStepList world (eraseRank world k) cap)
          (eraseRank.eraseRankStepList world (eraseRank world k) aw)
      rw [stepEq k ih out h.1, stepEqList k ih cap h.2.1, stepEqList k ih aw h.2.2]
    | .opaqueTy oid args, h => by
      change instantiate (eraseRank world (k + 1) (world.decls oid).witness)
          (eraseRank.eraseRankStepList world (eraseRank world (k + 1)) args) =
        instantiate (eraseRank world k (world.decls oid).witness)
          (eraseRank.eraseRankStepList world (eraseRank world k) args)
      have hRankLe : world.rank oid ≤ k := Nat.le_of_lt_succ h.1
      have hWit : eraseRank world (k + 1) (world.decls oid).witness =
          eraseRank world k (world.decls oid).witness :=
        ih _ (opaqueRankLt_mono world.rank hRankLe _ (world.stratified oid))
      rw [hWit, stepEqList k ih args h.2]
  stepEqList (k : Nat)
      (ih : ∀ t, OpaqueRankLt world.rank k t → eraseRank world (k + 1) t = eraseRank world k t) :
      ∀ xs : TyList, OpaqueRankLtList world.rank (k + 1) xs →
        eraseRank.eraseRankStepList world (eraseRank world (k + 1)) xs =
        eraseRank.eraseRankStepList world (eraseRank world k) xs
    | .nil, _ => rfl
    | .cons hd tl, h => by
      change TyList.cons (eraseRank world (k + 2) hd)
          (eraseRank.eraseRankStepList world (eraseRank world (k + 1)) tl) =
        TyList.cons (eraseRank world (k + 1) hd)
          (eraseRank.eraseRankStepList world (eraseRank world k) tl)
      rw [stepEq k ih hd h.1, stepEqList k ih tl h.2]

theorem eraseRank_ge_eq (world : World) (r : Nat) (t : Ty) (h : OpaqueRankLt world.rank r t) :
    ∀ d : Nat, eraseRank world (r + d) t = eraseRank world r t
  | 0 => rfl
  | d + 1 => by
    have hprev := eraseRank_ge_eq world r t h d
    have hlt : OpaqueRankLt world.rank (r + d) t :=
      opaqueRankLt_mono world.rank (Nat.le_add_right r d) t h
    have hstep := eraseRank_succ_eq world (r + d) t hlt
    exact Eq.trans hstep hprev

/-- Fuel-independent total opaque erasure (`Reveal::All` / `TypingMode::PostAnalysis`). -/
noncomputable def eraseAll (world : World) (t : Ty) : Ty :=
  eraseRank world (maxRankBound world.rank t) t

noncomputable def eraseAllList (world : World) : TyList → TyList :=
  foldTyList (fun _ => ()) (fun _ => ()) (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ => ())
    (fun _ _ _ => ()) (fun _ _ _ _ _ _ => ()) (fun _ _ _ => ())
    .nil (fun hd _ _ tl => .cons (eraseAll world hd) tl)

theorem eraseRank_eq_eraseAll (world : World) (r : Nat) (t : Ty)
    (h : OpaqueRankLt world.rank r t) :
    eraseRank world r t = eraseAll world t := by
  unfold eraseAll
  let k := maxRankBound world.rank t
  have hk : OpaqueRankLt world.rank k t := opaqueRankLt_maxRankBound world.rank t
  match nat_le_or_ge r k with
  | Or.inl hle =>
    have heq : r + (k - r) = k := Nat.add_sub_of_le hle
    have h1 := eraseRank_ge_eq world r t h (k - r)
    rw [heq] at h1
    exact h1.symm
  | Or.inr hge =>
    have heq : k + (r - k) = r := Nat.add_sub_of_le hge
    have h1 := eraseRank_ge_eq world k t hk (r - k)
    rw [heq] at h1
    exact h1

theorem eraseRankList_eq_eraseAllList (world : World) (r : Nat) :
    ∀ xs : TyList, OpaqueRankLtList world.rank r xs →
      eraseRank.eraseRankStepList world (eraseRank world r) xs = eraseAllList world xs
  | .nil, _ => rfl
  | .cons hd tl, h => by
    change TyList.cons (eraseRank world (r + 1) hd)
      (eraseRank.eraseRankStepList world (eraseRank world r) tl) =
      TyList.cons (eraseAll world hd) (eraseAllList world tl)
    have hhd : eraseRank world (r + 1) hd = eraseAll world hd :=
      eraseRank_eq_eraseAll world (r + 1) hd
        (opaqueRankLt_mono world.rank (Nat.le_succ r) hd h.1)
    rw [hhd, eraseRankList_eq_eraseAllList world r tl h.2]

theorem eraseAll_isConcrete (world : World) (t : Ty) : IsConcrete (eraseAll world t) :=
  eraseRank_isConcrete world (maxRankBound world.rank t) t (opaqueRankLt_maxRankBound world.rank t)

theorem eraseAll_of_isConcrete (world : World) (t : Ty) (hc : IsConcrete t) :
    eraseAll world t = t := by
  have h0 : OpaqueRankLt world.rank 0 t := go t hc
  exact (eraseRank_eq_eraseAll world 0 t h0).symm
where
  go : ∀ t : Ty, IsConcrete t → OpaqueRankLt world.rank 0 t
    | .prim _, _ => trivial
    | .param _, _ => trivial
    | .pair l r, h => ⟨go l h.1, go r h.2⟩
    | .boxPtr inner, h => go inner h
    | .optBox inner, h => go inner h
    | .arr elem _, h => go elem h
    | .coroutine out cap aw, h => ⟨go out h.1, goList cap h.2.1, goList aw h.2.2⟩
    | .opaqueTy _ _, h => False.elim h
  goList : ∀ xs : TyList, IsConcreteList xs → OpaqueRankLtList world.rank 0 xs
    | .nil, _ => trivial
    | .cons hd tl, h => ⟨go hd h.1, goList tl h.2⟩

theorem eraseAll_idempotent (world : World) (t : Ty) :
    eraseAll world (eraseAll world t) = eraseAll world t :=
  eraseAll_of_isConcrete world (eraseAll world t) (eraseAll_isConcrete world t)

/-- `eraseAll` distributes over every concrete type constructor and reveals opaque aliases. -/
theorem eraseAll_opaque (world : World) (oid : OpaqueId) (args : TyList) :
    eraseAll world (.opaqueTy oid args) =
      instantiate (eraseAll world (world.decls oid).witness) (eraseAllList world args) := by
  let r := Nat.max (world.rank oid) (maxRankBoundList world.rank args)
  have hrank : OpaqueRankLt world.rank (r + 1) (.opaqueTy oid args) := by
    refine ⟨Nat.lt_succ_of_le (nat_max_ge_left _ _), ?_⟩
    exact opaqueRankLtList_mono world.rank
      (nat_le_trans (nat_max_ge_right _ _) (Nat.le_succ r))
      args (opaqueRankLtList_maxRankBound world.rank args)
  have heq := (eraseRank_eq_eraseAll world (r + 1) (.opaqueTy oid args) hrank).symm
  rw [heq]
  change instantiate (eraseRank world r (world.decls oid).witness)
    (eraseRank.eraseRankStepList world (eraseRank world r) args) =
    instantiate (eraseAll world (world.decls oid).witness) (eraseAllList world args)
  have hw : eraseRank world r (world.decls oid).witness =
      eraseAll world (world.decls oid).witness :=
    eraseRank_eq_eraseAll world r _
      (opaqueRankLt_mono world.rank (nat_max_ge_left _ _) _ (world.stratified oid))
  have ha : eraseRank.eraseRankStepList world (eraseRank world r) args = eraseAllList world args :=
    eraseRankList_eq_eraseAllList world r args
      (opaqueRankLtList_mono world.rank (nat_max_ge_right _ _) args
        (opaqueRankLtList_maxRankBound world.rank args))
  rw [hw, ha]

/-- `eraseRank` preserves `substTy` composition with erased substitution images. -/
theorem eraseRank_substTy (world : World) :
    ∀ (r : Nat) (t : Ty) (σ : Subst),
      OpaqueRankLt world.rank r t →
      eraseAll world (substTy σ t) =
        substTy (fun p => eraseAll world (σ p)) (eraseRank world r t) := by
  intro r
  induction r with
  | zero =>
    intro t σ h
    exact baseStep t σ (opaqueRankLt_zero_isConcrete world.rank t h)
  | succ k ih =>
    exact indStep k ih
where
  eraseAll_pair (l rt : Ty) :
      eraseAll world (.pair l rt) = .pair (eraseAll world l) (eraseAll world rt) := by
    let m := Nat.max (maxRankBound world.rank l) (maxRankBound world.rank rt)
    have h : OpaqueRankLt world.rank (m + 1) (.pair l rt) :=
      ⟨opaqueRankLt_mono world.rank (nat_le_trans (nat_max_ge_left _ _) (Nat.le_succ m))
         l (opaqueRankLt_maxRankBound world.rank l),
       opaqueRankLt_mono world.rank (nat_le_trans (nat_max_ge_right _ _) (Nat.le_succ m))
         rt (opaqueRankLt_maxRankBound world.rank rt)⟩
    rw [← eraseRank_eq_eraseAll world (m + 1) (.pair l rt) h]
    change Ty.pair (eraseRank world (m + 1) l) (eraseRank world (m + 1) rt) =
      Ty.pair (eraseAll world l) (eraseAll world rt)
    rw [eraseRank_eq_eraseAll world (m + 1) l h.1,
        eraseRank_eq_eraseAll world (m + 1) rt h.2]
  eraseAll_boxPtr (inner : Ty) :
      eraseAll world (.boxPtr inner) = .boxPtr (eraseAll world inner) := by
    let m := maxRankBound world.rank inner
    have h : OpaqueRankLt world.rank (m + 1) (.boxPtr inner) :=
      opaqueRankLt_mono world.rank (Nat.le_succ m) inner (opaqueRankLt_maxRankBound world.rank inner)
    rw [← eraseRank_eq_eraseAll world (m + 1) (.boxPtr inner) h]
    change Ty.boxPtr (eraseRank world (m + 1) inner) = Ty.boxPtr (eraseAll world inner)
    rw [eraseRank_eq_eraseAll world (m + 1) inner h]
  eraseAll_optBox (inner : Ty) :
      eraseAll world (.optBox inner) = .optBox (eraseAll world inner) := by
    let m := maxRankBound world.rank inner
    have h : OpaqueRankLt world.rank (m + 1) (.optBox inner) :=
      opaqueRankLt_mono world.rank (Nat.le_succ m) inner (opaqueRankLt_maxRankBound world.rank inner)
    rw [← eraseRank_eq_eraseAll world (m + 1) (.optBox inner) h]
    change Ty.optBox (eraseRank world (m + 1) inner) = Ty.optBox (eraseAll world inner)
    rw [eraseRank_eq_eraseAll world (m + 1) inner h]
  eraseAll_arr (elem : Ty) (n : Nat) :
      eraseAll world (.arr elem n) = .arr (eraseAll world elem) n := by
    let m := maxRankBound world.rank elem
    have h : OpaqueRankLt world.rank (m + 1) (.arr elem n) :=
      opaqueRankLt_mono world.rank (Nat.le_succ m) elem (opaqueRankLt_maxRankBound world.rank elem)
    rw [← eraseRank_eq_eraseAll world (m + 1) (.arr elem n) h]
    change Ty.arr (eraseRank world (m + 1) elem) n = Ty.arr (eraseAll world elem) n
    rw [eraseRank_eq_eraseAll world (m + 1) elem h]
  eraseAll_coroutine (out : Ty) (cap aw : TyList) :
      eraseAll world (.coroutine out cap aw) =
        .coroutine (eraseAll world out) (eraseAllList world cap) (eraseAllList world aw) := by
    let m := Nat.max (maxRankBound world.rank out)
      (Nat.max (maxRankBoundList world.rank cap) (maxRankBoundList world.rank aw))
    have hout : OpaqueRankLt world.rank m out :=
      opaqueRankLt_mono world.rank (nat_max_ge_left _ _) out (opaqueRankLt_maxRankBound world.rank out)
    have hcap : OpaqueRankLtList world.rank m cap :=
      opaqueRankLtList_mono world.rank
        (nat_le_trans (nat_max_ge_left _ _) (nat_max_ge_right _ _))
        cap (opaqueRankLtList_maxRankBound world.rank cap)
    have haw : OpaqueRankLtList world.rank m aw :=
      opaqueRankLtList_mono world.rank
        (nat_le_trans (nat_max_ge_right _ _) (nat_max_ge_right _ _))
        aw (opaqueRankLtList_maxRankBound world.rank aw)
    have h : OpaqueRankLt world.rank (m + 1) (.coroutine out cap aw) :=
      ⟨opaqueRankLt_mono world.rank (Nat.le_succ m) out hout,
       opaqueRankLtList_mono world.rank (Nat.le_succ m) cap hcap,
       opaqueRankLtList_mono world.rank (Nat.le_succ m) aw haw⟩
    rw [← eraseRank_eq_eraseAll world (m + 1) (.coroutine out cap aw) h]
    change Ty.coroutine (eraseRank world (m + 1) out)
      (eraseRank.eraseRankStepList world (eraseRank world m) cap)
      (eraseRank.eraseRankStepList world (eraseRank world m) aw) =
      Ty.coroutine (eraseAll world out) (eraseAllList world cap) (eraseAllList world aw)
    rw [eraseRank_eq_eraseAll world (m + 1) out h.1,
        eraseRankList_eq_eraseAllList world m cap hcap,
        eraseRankList_eq_eraseAllList world m aw haw]
  baseStep : ∀ (t : Ty) (σ : Subst), IsConcrete t →
      eraseAll world (substTy σ t) = substTy (fun p => eraseAll world (σ p)) t
    | .prim p, _, _ => eraseAll_of_isConcrete world (.prim p) trivial
    | .param _, _, _ => rfl
    | .pair l rt, σ, h => by
      change eraseAll world (.pair (substTy σ l) (substTy σ rt)) =
        .pair (substTy (fun p => eraseAll world (σ p)) l) (substTy (fun p => eraseAll world (σ p)) rt)
      rw [eraseAll_pair, baseStep l σ h.1, baseStep rt σ h.2]
    | .boxPtr inner, σ, h => by
      change eraseAll world (.boxPtr (substTy σ inner)) =
        .boxPtr (substTy (fun p => eraseAll world (σ p)) inner)
      rw [eraseAll_boxPtr, baseStep inner σ h]
    | .optBox inner, σ, h => by
      change eraseAll world (.optBox (substTy σ inner)) =
        .optBox (substTy (fun p => eraseAll world (σ p)) inner)
      rw [eraseAll_optBox, baseStep inner σ h]
    | .arr elem n, σ, h => by
      change eraseAll world (.arr (substTy σ elem) n) =
        .arr (substTy (fun p => eraseAll world (σ p)) elem) n
      rw [eraseAll_arr, baseStep elem σ h]
    | .coroutine out cap aw, σ, h => by
      change eraseAll world (.coroutine (substTy σ out) (substTyList σ cap) (substTyList σ aw)) =
        .coroutine (substTy (fun p => eraseAll world (σ p)) out)
          (substTyList (fun p => eraseAll world (σ p)) cap)
          (substTyList (fun p => eraseAll world (σ p)) aw)
      rw [eraseAll_coroutine, baseStep out σ h.1, baseStepList cap σ h.2.1, baseStepList aw σ h.2.2]
    | .opaqueTy _ _, _, h => False.elim h
  baseStepList : ∀ (xs : TyList) (σ : Subst), IsConcreteList xs →
      eraseAllList world (substTyList σ xs) = substTyList (fun p => eraseAll world (σ p)) xs
    | .nil, _, _ => rfl
    | .cons hd tl, σ, h => by
      change TyList.cons (eraseAll world (substTy σ hd)) (eraseAllList world (substTyList σ tl)) =
        TyList.cons (substTy (fun p => eraseAll world (σ p)) hd)
          (substTyList (fun p => eraseAll world (σ p)) tl)
      rw [baseStep hd σ h.1, baseStepList tl σ h.2]
  indStep (k : Nat)
      (ih : ∀ (t : Ty) (σ : Subst), OpaqueRankLt world.rank k t →
        eraseAll world (substTy σ t) = substTy (fun p => eraseAll world (σ p)) (eraseRank world k t)) :
      ∀ (t : Ty) (σ : Subst), OpaqueRankLt world.rank (k + 1) t →
        eraseAll world (substTy σ t) =
          substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) t)
    | .prim p, _, _ => eraseAll_of_isConcrete world (.prim p) trivial
    | .param _, _, _ => rfl
    | .pair l rt, σ, h => by
      change eraseAll world (.pair (substTy σ l) (substTy σ rt)) =
        .pair (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) l))
              (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) rt))
      rw [eraseAll_pair, indStep k ih l σ h.1, indStep k ih rt σ h.2]
    | .boxPtr inner, σ, h => by
      change eraseAll world (.boxPtr (substTy σ inner)) =
        .boxPtr (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) inner))
      rw [eraseAll_boxPtr, indStep k ih inner σ h]
    | .optBox inner, σ, h => by
      change eraseAll world (.optBox (substTy σ inner)) =
        .optBox (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) inner))
      rw [eraseAll_optBox, indStep k ih inner σ h]
    | .arr elem n, σ, h => by
      change eraseAll world (.arr (substTy σ elem) n) =
        .arr (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) elem)) n
      rw [eraseAll_arr, indStep k ih elem σ h]
    | .coroutine out cap aw, σ, h => by
      change eraseAll world (.coroutine (substTy σ out) (substTyList σ cap) (substTyList σ aw)) =
        .coroutine
          (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) out))
          (substTyList (fun p => eraseAll world (σ p))
            (eraseRank.eraseRankStepList world (eraseRank world k) cap))
          (substTyList (fun p => eraseAll world (σ p))
            (eraseRank.eraseRankStepList world (eraseRank world k) aw))
      rw [eraseAll_coroutine, indStep k ih out σ h.1,
          indStepList k ih cap σ h.2.1, indStepList k ih aw σ h.2.2]
    | .opaqueTy oid args, σ, h => by
      change eraseAll world (.opaqueTy oid (substTyList σ args)) =
        substTy (fun p => eraseAll world (σ p))
          (instantiate (eraseRank world k (world.decls oid).witness)
            (eraseRank.eraseRankStepList world (eraseRank world k) args))
      rw [eraseAll_opaque]
      have hRankLe : world.rank oid ≤ k := Nat.le_of_lt_succ h.1
      have hWitRank : OpaqueRankLt world.rank k (world.decls oid).witness :=
        opaqueRankLt_mono world.rank hRankLe _ (world.stratified oid)
      have hWitEq : eraseAll world (world.decls oid).witness =
          eraseRank world k (world.decls oid).witness :=
        (eraseRank_eq_eraseAll world k _ hWitRank).symm
      rw [hWitEq]
      have hArgsEq : eraseAllList world (substTyList σ args) =
          substTyList (fun p => eraseAll world (σ p))
            (eraseRank.eraseRankStepList world (eraseRank world k) args) :=
        indStepList k ih args σ h.2
      rw [hArgsEq]
      unfold instantiate
      rw [substTy_comp]
      apply substTy_congr
      intro p _
      unfold substComp argsSubst
      rw [substTyList_get?]
      cases TyList.get? (eraseRank.eraseRankStepList world (eraseRank world k) args) p with
      | some a => rfl
      | none => rfl
  indStepList (k : Nat)
      (ih : ∀ (t : Ty) (σ : Subst), OpaqueRankLt world.rank k t →
        eraseAll world (substTy σ t) = substTy (fun p => eraseAll world (σ p)) (eraseRank world k t)) :
      ∀ (xs : TyList) (σ : Subst), OpaqueRankLtList world.rank (k + 1) xs →
        eraseAllList world (substTyList σ xs) =
          substTyList (fun p => eraseAll world (σ p))
            (eraseRank.eraseRankStepList world (eraseRank world k) xs)
    | .nil, _, _ => rfl
    | .cons hd tl, σ, h => by
      change TyList.cons (eraseAll world (substTy σ hd)) (eraseAllList world (substTyList σ tl)) =
        TyList.cons
          (substTy (fun p => eraseAll world (σ p)) (eraseRank world (k + 1) hd))
          (substTyList (fun p => eraseAll world (σ p))
            (eraseRank.eraseRankStepList world (eraseRank world k) tl))
      rw [indStep k ih hd σ h.1, indStepList k ih tl σ h.2]

/-- **Opaque Unfolding Equation for `eraseAll`**:
    Erasing `.opaqueTy oid args` produces the exact same concrete type as erasing the
    instantiated hidden witness `instantiate (world.decls oid).witness args`. -/
theorem eraseAll_opaque_eq_witness (world : World) (oid : OpaqueId) (args : TyList) :
    eraseAll world (.opaqueTy oid args) =
      eraseAll world (instantiate (world.decls oid).witness args) := by
  rw [eraseAll_opaque]
  unfold instantiate
  let r := maxRankBound world.rank (world.decls oid).witness
  have hsub := eraseRank_substTy world r (world.decls oid).witness (argsSubst args)
    (opaqueRankLt_maxRankBound world.rank _)
  rw [hsub]
  change substTy (argsSubst (eraseAllList world args)) (eraseAll world (world.decls oid).witness) =
    substTy (fun p => eraseAll world (argsSubst args p)) (eraseAll world (world.decls oid).witness)
  apply substTy_congr
  intro p _
  unfold argsSubst
  rw [get?_eraseAllList args p]
  cases TyList.get? args p with
  | some t => rfl
  | none => exact (eraseAll_of_isConcrete world (Ty.prim .unit) trivial).symm
where
  get?_eraseAllList : ∀ (xs : TyList) (i : Nat),
      TyList.get? (eraseAllList world xs) i =
        match TyList.get? xs i with
        | some t => some (eraseAll world t)
        | none => none
    | .nil, _ => rfl
    | .cons _ _, 0 => rfl
    | .cons _ tl, i + 1 => get?_eraseAllList tl i

/-- Concrete auto-trait judgment on fully erased (opaque-free) types.
    Mirrors `rustc_trait_selection/src/traits/select/candidate_assembly.rs:816-891`
    and `rustc_next_trait_solver/src/solve/trait_goals.rs:194-260`. -/
def AutoTraitConcrete (atr : AutoTrait) : Ty → Prop :=
  foldTyProp
    (fun p => primAutoTrait atr p)
    (fun _ => False)
    (fun _ _ l r => l ∧ r)
    (fun _ inner => inner) (fun _ inner => inner) (fun _ _ elem => elem)
    (fun _ _ _ _ cap aw =>
      match atr with
      | .unpin => False
      | .send  => cap ∧ aw
      | .sync  => cap ∧ aw)
    (fun _ _ _ => False)
    True (fun _ _ hd tl => hd ∧ tl)

def AutoTraitConcreteList (atr : AutoTrait) : TyList → Prop :=
  foldTyListProp
    (fun p => primAutoTrait atr p)
    (fun _ => False)
    (fun _ _ l r => l ∧ r)
    (fun _ inner => inner) (fun _ inner => inner) (fun _ _ elem => elem)
    (fun _ _ _ _ cap aw =>
      match atr with
      | .unpin => False
      | .send  => cap ∧ aw
      | .sync  => cap ∧ aw)
    (fun _ _ _ => False)
    True (fun _ _ hd tl => hd ∧ tl)

/-- Concrete ABI layout calculation on fully erased concrete types (`layout_of_uncached`). -/
noncomputable def layoutOfConcrete : Ty → Option Layout :=
  foldTy
    (fun p => some (primLayout p))
    (fun _ => none)
    (fun _ _ ol or_ =>
      match ol, or_ with
      | some ll, some lr => some (pairLayout ll lr)
      | _, _ => none)
    (fun _ _ => some ptrLayout)
    (fun _ _ => some ptrLayout)
    (fun _ n oe =>
      match oe with
      | some le => some (arrayLayout le n)
      | none => none)
    (fun _ _ _ _ _ _ => some { size := 16, align := 8 })
    (fun _ _ _ => none)
    () (fun _ _ _ _ => ())

/-- A `World` is sound when every opaque declaration's explicit item bounds (`itemTraitBounds`
    and `itemAutoBounds`) genuinely hold on its erased concrete witness for every instantiation. -/
structure SoundWorld (world : World) : Prop where
  itemTraitsSound :
    ∀ oid tr args,
      (world.decls oid).itemTraitBounds tr →
      world.concreteTrait tr (eraseAll world (instantiate (world.decls oid).witness args))
  itemAutosSound :
    ∀ oid atr args,
      (world.decls oid).itemAutoBounds atr →
      AutoTraitConcrete atr (eraseAll world (instantiate (world.decls oid).witness args))

/-- Verification obligations tested across the three visibility tiers. -/
inductive Obligation where
  | userTrait (tr : TraitId) (ty : Ty)
  | autoTrait (atr : AutoTrait) (ty : Ty)
  | tyEq (t1 t2 : Ty)
  | hasLayout (ty : Ty) (lay : Layout)
  | rtnBound (implTy : Ty) (m : AssocMethodId) (atr : AutoTrait)

/-- User-facing trait satisfaction (`Reveal::UserFacing` / `TypingMode::Typeck` outside defining
    scope): an opaque type satisfies ONLY its explicitly declared `itemTraitBounds` (never
    unexposed concrete traits such as `Add<u32>` on `impl Copy`), whereas non-opaque types
    fall back to concrete trait checking when concrete. -/
def UserFacingTrait (world : World) (tr : TraitId) : Ty → Prop
  | .opaqueTy oid _ => (world.decls oid).itemTraitBounds tr
  | t => IsConcrete t ∧ world.concreteTrait tr t

/-- Auto-trait satisfaction under `Reveal::UserFacing` (`consider_auto_trait_candidate_for_opaque_ty`,
    `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:1321-1390`):
    an opaque type satisfies auto-trait `at` via EITHER an explicit `itemAutoBounds` bound OR
    auto-trait leakage through its instantiated hidden witness (without exposing concrete type
    equality or non-auto traits). -/
def UserFacingAutoTrait (world : World) (atr : AutoTrait) : Ty → Prop
  | .opaqueTy oid args =>
    (world.decls oid).itemAutoBounds atr ∨
    AutoTraitConcrete atr (eraseAll world (instantiate (world.decls oid).witness args))
  | t => AutoTraitConcrete atr (eraseAll world t)

/-- Three-phase entailment relation modeling `Reveal::UserFacing`, `definingScope`, and `Reveal::All`. -/
def Entails (world : World) (tier : RevealTier) (ob : Obligation) : Prop :=
  match tier with
  | .userFacing =>
    match ob with
    | .userTrait tr ty => UserFacingTrait world tr ty
    | .autoTrait atr ty => UserFacingAutoTrait world atr ty
    | .tyEq t1 t2 => t1 = t2
    | .hasLayout ty lay =>
      -- `rustc_ty_utils::layout::layout_of` upgrades to `TypingMode::PostAnalysis` (`Reveal::All`)!
      layoutOfConcrete (eraseAll world ty) = some lay
    | .rtnBound implTy m atr =>
      -- `lower_return_type_notation_ty` lowers `W::m(..): Send` to auto-trait bound on RPITIT future
      UserFacingAutoTrait world atr (world.rpititFuture implTy m)
  | .definingScope defined =>
    match ob with
    | .userTrait tr ty =>
      match ty with
      | .opaqueTy oid args =>
        (world.decls oid).itemTraitBounds tr ∨
        (defined oid ∧ world.concreteTrait tr (eraseAll world (instantiate (world.decls oid).witness args)))
      | _ => IsConcrete ty ∧ world.concreteTrait tr ty
    | .autoTrait atr ty => UserFacingAutoTrait world atr ty
    | .tyEq t1 t2 =>
      t1 = t2 ∨
      (match t1 with
       | .opaqueTy oid args => defined oid ∧ instantiate (world.decls oid).witness args = t2
       | _ => False)
    | .hasLayout ty lay => layoutOfConcrete (eraseAll world ty) = some lay
    | .rtnBound implTy m atr => UserFacingAutoTrait world atr (world.rpititFuture implTy m)
  | .revealAll =>
    match ob with
    | .userTrait tr ty => world.concreteTrait tr (eraseAll world ty)
    | .autoTrait atr ty => AutoTraitConcrete atr (eraseAll world ty)
    | .tyEq t1 t2 => eraseAll world t1 = eraseAll world t2
    | .hasLayout ty lay => layoutOfConcrete (eraseAll world ty) = some lay
    | .rtnBound implTy m atr => AutoTraitConcrete atr (eraseAll world (world.rpititFuture implTy m))

/-- **Main Theorem 2 (`userFacing_refines_revealAll`)**:
    In any sound stratified world, EVERY obligation discharged under `Reveal::UserFacing`
    (`TypingMode::Typeck` outside defining scope) remains valid after `Reveal::All`
    (`TypingMode::PostAnalysis` / `TypingMode::Codegen`) opaque erasure. -/
theorem userFacing_refines_revealAll (world : World) (hs : SoundWorld world) (ob : Obligation) :
    Entails world .userFacing ob → Entails world .revealAll ob := by
  cases ob with
  | userTrait tr ty =>
    intro h
    cases ty with
    | opaqueTy oid args =>
      change world.concreteTrait tr (eraseAll world (.opaqueTy oid args))
      rw [eraseAll_opaque_eq_witness]
      exact hs.itemTraitsSound oid tr args h
    | prim p =>
      change world.concreteTrait tr (eraseAll world (.prim p))
      rw [eraseAll_of_isConcrete world (.prim p) h.1]
      exact h.2
    | param i =>
      change world.concreteTrait tr (eraseAll world (.param i))
      rw [eraseAll_of_isConcrete world (.param i) h.1]
      exact h.2
    | pair l r =>
      change world.concreteTrait tr (eraseAll world (.pair l r))
      rw [eraseAll_of_isConcrete world (.pair l r) h.1]
      exact h.2
    | boxPtr inner =>
      change world.concreteTrait tr (eraseAll world (.boxPtr inner))
      rw [eraseAll_of_isConcrete world (.boxPtr inner) h.1]
      exact h.2
    | optBox inner =>
      change world.concreteTrait tr (eraseAll world (.optBox inner))
      rw [eraseAll_of_isConcrete world (.optBox inner) h.1]
      exact h.2
    | arr elem n =>
      change world.concreteTrait tr (eraseAll world (.arr elem n))
      rw [eraseAll_of_isConcrete world (.arr elem n) h.1]
      exact h.2
    | coroutine out cap aw =>
      change world.concreteTrait tr (eraseAll world (.coroutine out cap aw))
      rw [eraseAll_of_isConcrete world (.coroutine out cap aw) h.1]
      exact h.2
  | autoTrait atr ty =>
    intro h
    cases ty with
    | opaqueTy oid args =>
      change AutoTraitConcrete atr (eraseAll world (.opaqueTy oid args))
      rw [eraseAll_opaque_eq_witness]
      match h with
      | Or.inl hbound => exact hs.itemAutosSound oid atr args hbound
      | Or.inr hleak  => exact hleak
    | prim _ => exact h
    | param _ => exact h
    | pair _ _ => exact h
    | boxPtr _ => exact h
    | optBox _ => exact h
    | arr _ _ => exact h
    | coroutine _ _ _ => exact h
  | tyEq t1 t2 =>
    intro h
    exact congrArg (eraseAll world) h
  | hasLayout ty lay =>
    intro h
    exact h
  | rtnBound implTy m atr =>
    intro h
    change UserFacingAutoTrait world atr (world.rpititFuture implTy m) at h
    change AutoTraitConcrete atr (eraseAll world (world.rpititFuture implTy m))
    cases hfut : world.rpititFuture implTy m with
    | opaqueTy oid args =>
      rw [hfut] at h
      rw [eraseAll_opaque_eq_witness]
      match h with
      | Or.inl hbound => exact hs.itemAutosSound oid atr args hbound
      | Or.inr hleak  => exact hleak
    | prim _ => rw [hfut] at h; exact h
    | param _ => rw [hfut] at h; exact h
    | pair _ _ => rw [hfut] at h; exact h
    | boxPtr _ => rw [hfut] at h; exact h
    | optBox _ => rw [hfut] at h; exact h
    | arr _ _ => rw [hfut] at h; exact h
    | coroutine _ _ _ => rw [hfut] at h; exact h

/-- Monotonicity also holds across the intermediate `definingScope` tier! -/
theorem definingScope_refines_revealAll (world : World) (hs : SoundWorld world)
    (defined : OpaqueId → Prop) (ob : Obligation) :
    Entails world (.definingScope defined) ob → Entails world .revealAll ob := by
  cases ob with
  | userTrait tr ty =>
    intro h
    cases ty with
    | opaqueTy oid args =>
      change world.concreteTrait tr (eraseAll world (.opaqueTy oid args))
      rw [eraseAll_opaque_eq_witness]
      match h with
      | Or.inl hb => exact hs.itemTraitsSound oid tr args hb
      | Or.inr hd => exact hd.2
    | prim p =>
      change world.concreteTrait tr (eraseAll world (.prim p))
      rw [eraseAll_of_isConcrete world (.prim p) h.1]
      exact h.2
    | param i =>
      change world.concreteTrait tr (eraseAll world (.param i))
      rw [eraseAll_of_isConcrete world (.param i) h.1]
      exact h.2
    | pair l r =>
      change world.concreteTrait tr (eraseAll world (.pair l r))
      rw [eraseAll_of_isConcrete world (.pair l r) h.1]
      exact h.2
    | boxPtr inner =>
      change world.concreteTrait tr (eraseAll world (.boxPtr inner))
      rw [eraseAll_of_isConcrete world (.boxPtr inner) h.1]
      exact h.2
    | optBox inner =>
      change world.concreteTrait tr (eraseAll world (.optBox inner))
      rw [eraseAll_of_isConcrete world (.optBox inner) h.1]
      exact h.2
    | arr elem n =>
      change world.concreteTrait tr (eraseAll world (.arr elem n))
      rw [eraseAll_of_isConcrete world (.arr elem n) h.1]
      exact h.2
    | coroutine out cap aw =>
      change world.concreteTrait tr (eraseAll world (.coroutine out cap aw))
      rw [eraseAll_of_isConcrete world (.coroutine out cap aw) h.1]
      exact h.2
  | autoTrait atr ty =>
    exact userFacing_refines_revealAll world hs (.autoTrait atr ty)
  | tyEq t1 t2 =>
    intro h
    match h with
    | Or.inl heq => exact congrArg (eraseAll world) heq
    | Or.inr hdef =>
      cases t1 with
      | opaqueTy oid args =>
        change eraseAll world (.opaqueTy oid args) = eraseAll world t2
        rw [eraseAll_opaque_eq_witness, hdef.2]
      | prim _ => exact False.elim hdef
      | param _ => exact False.elim hdef
      | pair _ _ => exact False.elim hdef
      | boxPtr _ => exact False.elim hdef
      | optBox _ => exact False.elim hdef
      | arr _ _ => exact False.elim hdef
      | coroutine _ _ _ => exact False.elim hdef
  | hasLayout ty lay => intro h; exact h
  | rtnBound implTy m atr =>
    exact userFacing_refines_revealAll world hs (.rtnBound implTy m atr)

/-- **Main Theorem 3 (`autoTrait_leakage_sound_iff_witness`)**:
    In any sound stratified world, an auto-trait obligation (`Send` / `Sync` / `Unpin`) holds on
    an opaque type `.opaqueTy oid args` under `Reveal::UserFacing` IF AND ONLY IF it holds on the
    fully revealed concrete witness `eraseAll world (instantiate (world.decls oid).witness args)`. -/
theorem autoTrait_leakage_sound_iff_witness (world : World) (hs : SoundWorld world)
    (oid : OpaqueId) (args : TyList) (atr : AutoTrait) :
    Entails world .userFacing (.autoTrait atr (.opaqueTy oid args)) ↔
      AutoTraitConcrete atr (eraseAll world (instantiate (world.decls oid).witness args)) := by
  constructor
  · intro h
    match h with
    | Or.inl hbound => exact hs.itemAutosSound oid atr args hbound
    | Or.inr hleak  => exact hleak
  · intro hw
    exact Or.inr hw

/-- Corollary: `Reveal::All` layout transparency holds identically under `Reveal::UserFacing`
    for any non-coroutine opaque type, matching `rustc_ty_utils::layout::layout_of`. -/
theorem layout_transparent_across_tiers (world : World) (oid : OpaqueId) (args : TyList)
    (lay : Layout) :
    Entails world .userFacing (.hasLayout (.opaqueTy oid args) lay) ↔
      layoutOfConcrete (eraseAll world (instantiate (world.decls oid).witness args)) = some lay := by
  change (layoutOfConcrete (eraseAll world (.opaqueTy oid args)) = some lay) ↔ _
  rw [eraseAll_opaque_eq_witness]

/-- Corollary: RTN `W::m(..): Send` holds iff every captured upvar and every local live across
    `.await` inside the concrete lowered RPITIT coroutine future is `Send`. -/
theorem rtn_send_iff_coroutine_locals_send (world : World) (hs : SoundWorld world)
    (implTy : Ty) (m : AssocMethodId) (out : Ty) (cap aw : TyList)
    (hfut : eraseAll world (world.rpititFuture implTy m) = .coroutine out cap aw) :
    Entails world .userFacing (.rtnBound implTy m .send) ↔
      (AutoTraitConcreteList .send cap ∧ AutoTraitConcreteList .send aw) := by
  constructor
  · intro h
    have hr := userFacing_refines_revealAll world hs (.rtnBound implTy m .send) h
    change AutoTraitConcrete .send (eraseAll world (world.rpititFuture implTy m)) at hr
    rw [hfut] at hr
    exact hr
  · intro h
    change UserFacingAutoTrait world .send (world.rpititFuture implTy m)
    cases hwf : world.rpititFuture implTy m with
    | opaqueTy oid args =>
      rw [hwf, eraseAll_opaque_eq_witness] at hfut
      exact Or.inr (by rw [hfut]; exact h)
    | prim _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h
    | param _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h
    | pair _ _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h
    | boxPtr _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h
    | optBox _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h
    | arr _ _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h
    | coroutine _ _ _ => rw [hwf] at hfut; change AutoTraitConcrete .send (eraseAll world _); rw [hfut]; exact h

/-! ## Section 5: Solver Divergence Model (`-Z next-solver=globally` vs. `-Z next-solver=no`) -/

/-- Outcome of checking a list of opaque uses in one defining scope under old vs. next solver. -/
inductive DefiningUseOutcome where
  | accepted (witness : Ty)
  | rejectedE0792NonParam
  | rejectedDuplicateParam
  | rejectedItemDoesNotConstrain

/-- Classify one use's argument list for a unary (`arity = 1`) opaque `GenOpaque<T>`. -/
def isUnaryParamArg : TyList → Option ParamId
  | .cons (.param p) .nil => some p
  | _ => none

/-- Old solver (`-Z next-solver=no`, `writeback.rs:595-605`):
    eagerly rejects ANY non-defining use in the defining scope with `E0792`, even when
    another defining use exists in the same body. -/
noncomputable def oldSolverCheckUnary (uses : List (TyList × Ty)) : DefiningUseOutcome :=
  let step : (TyList × Ty) → (Option Ty → DefiningUseOutcome) → Option Ty → DefiningUseOutcome :=
    fun entry k acc =>
      match isUnaryParamArg entry.1 with
      | none => .rejectedE0792NonParam
      | some p =>
        let w := substTy (fun q => if q == p then Ty.param 0 else Ty.param q) entry.2
        k (match acc with | some prev => some prev | none => some w)
  let base : Option Ty → DefiningUseOutcome := fun acc =>
    match acc with
    | some w => .accepted w
    | none => .rejectedItemDoesNotConstrain
  List.foldr step base uses none

/-- Next solver (`-Z next-solver=globally`, `rustc_hir_typeck/src/opaque_types.rs:125-182`):
    skips non-defining uses (`UsageKind::NonDefiningUse`) while searching for a defining use;
    accepts if a defining use exists and matches all non-defining uses, or emits the unnumbered
    `item does not constrain` diagnostic if no defining use exists. -/
noncomputable def nextSolverCheckUnary (uses : List (TyList × Ty)) : DefiningUseOutcome :=
  let findDefining : Option Ty :=
    List.foldr
      (fun (entry : TyList × Ty) (rest : Option Ty) =>
        match isUnaryParamArg entry.1 with
        | some p => some (substTy (fun q => if q == p then Ty.param 0 else Ty.param q) entry.2)
        | none => rest)
      none
      uses
  match findDefining with
  | some w => .accepted w
  | none => .rejectedItemDoesNotConstrain

/-- Exact mechanized reproduction of the two `GenOpaque` solver divergences observed live
    (`tait_10` diagnostic divergence and `tait_12` accept-vs-reject divergence). -/
theorem solver_divergence_tait10_and_tait12 :
    let loneBad : List (TyList × Ty) := [(.cons (.prim .u32) .nil, .prim .u32)]
    let definingAndNonDef : List (TyList × Ty) :=
      [(.cons (.param 0) .nil, .param 0), (.cons (.prim .u32) .nil, .prim .u32)]
    (oldSolverCheckUnary loneBad = .rejectedE0792NonParam ∧
     nextSolverCheckUnary loneBad = .rejectedItemDoesNotConstrain) ∧
    (oldSolverCheckUnary definingAndNonDef = .rejectedE0792NonParam ∧
     nextSolverCheckUnary definingAndNonDef = .accepted (.param 0)) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## Section 6: Four Constructive Sharpness Counterexamples -/

/-- **Counterexample 1 (`ce1_conflicting_definers_break_transitivity_unsound`)**:
    Admitting two conflicting `#[define_opaque(Hidden)]` witnesses (`def_u32 : Hidden = u32`
    and `def_u64 : Hidden = u64`, `tait_04`) collapses type-equality transitivity and
    produces an absurd ABI layout equality (`4 = 8`), deriving `False`. -/
theorem ce1_conflicting_definers_break_transitivity_unsound :
    ¬ ∃ (hiddenWitness : Ty),
        hiddenWitness = Ty.prim .u32 ∧
        hiddenWitness = Ty.prim .u64 ∧
        layoutOfConcrete (Ty.prim .u32) = some { size := 4, align := 4 } ∧
        layoutOfConcrete (Ty.prim .u64) = some { size := 8, align := 8 } := by
  rintro ⟨w, h1, h2, _, _⟩
  have h32eq64 : Ty.prim .u32 = Ty.prim .u64 := Eq.trans h1.symm h2
  cases h32eq64

/-- Sharpness corollary for CE1: any unchecked congruence admitting both `Hidden = u32` and
    `Hidden = u64` forces `primLayout .u32 = primLayout .u64` (`4 = 8`), which is uninhabited. -/
theorem ce1_conflicting_definers_break_layout_soundness :
    ∀ (equiv : Ty → Ty → Prop),
      (∀ a b c, equiv a b → equiv b c → equiv a c) →
      (∀ a b, equiv a b → equiv b a) →
      (∀ a b, equiv a b → layoutOfConcrete a = layoutOfConcrete b) →
      equiv (.opaqueTy 0 .nil) (.prim .u32) →
      equiv (.opaqueTy 0 .nil) (.prim .u64) →
      False := by
  intro equiv htrans hsymm hlay h32 h64
  have heq : equiv (.prim .u32) (.prim .u64) := htrans _ _ _ (hsymm _ _ h32) h64
  have hl := hlay _ _ heq
  have h4eq8 : (4 : Nat) = 8 := by
    have hsome : some ({ size := 4, align := 4 } : Layout) = some { size := 8, align := 8 } := hl
    injection hsome with hstruct
    exact congrArg Layout.size hstruct
  cases h4eq8

/-- **Counterexample 2 (`ce2_non_injective_param_instantiation_breaks_coherence`)**:
    Relaxing the bijective-parameter requirement allows BOTH:
      (a) Duplicate generic parameters `GenPair<T, T> = (T, T)` (`tait_11`): TWO distinct
          well-kinded declaration-site witnesses `w1 = (A, B)` and `w2 = (A, A)` both
          instantiate to `(T, T)`, yet diverge in type and ABI layout at `GenPair<u32, u64>`
          (`pairLayout u32 u64 = 16 B` vs. `pairLayout u32 u32 = 8 B`).
      (b) Concrete non-parameter instantiation `GenOpaque<u32> = u32` (`tait_10`): TWO distinct
          well-kinded witnesses `w1 = T` and `w2 = u32` both instantiate to `u32`, yet diverge
          at `GenOpaque<u64>` (`8 B` vs. `4 B`). -/
theorem ce2_non_injective_param_instantiation_breaks_coherence :
    (∃ w1 w2 : Ty,
      TyVarsIn 2 w1 ∧ TyVarsIn 2 w2 ∧ w1 ≠ w2 ∧
      instantiate w1 (.cons (.param 0) (.cons (.param 0) .nil)) =
        instantiate w2 (.cons (.param 0) (.cons (.param 0) .nil)) ∧
      layoutOfConcrete (instantiate w1 (.cons (.prim .u32) (.cons (.prim .u64) .nil))) ≠
        layoutOfConcrete (instantiate w2 (.cons (.prim .u32) (.cons (.prim .u64) .nil)))) ∧
    (∃ w1 w2 : Ty,
      TyVarsIn 1 w1 ∧ TyVarsIn 1 w2 ∧ w1 ≠ w2 ∧
      instantiate w1 (.cons (.prim .u32) .nil) =
        instantiate w2 (.cons (.prim .u32) .nil) ∧
      layoutOfConcrete (instantiate w1 (.cons (.prim .u64) .nil)) ≠
        layoutOfConcrete (instantiate w2 (.cons (.prim .u64) .nil))) := by
  constructor
  · refine ⟨.pair (.param 0) (.param 1), .pair (.param 0) (.param 0), ?_, ?_, ?_, rfl, ?_⟩
    · intro p hp
      match hp with
      | Or.inl h0 => rw [← h0]; exact Nat.zero_lt_succ 1
      | Or.inr h1 => rw [← h1]; exact Nat.lt_succ_self 1
    · intro p hp
      match hp with
      | Or.inl h0 => rw [← h0]; exact Nat.zero_lt_succ 1
      | Or.inr h0 => rw [← h0]; exact Nat.zero_lt_succ 1
    · intro heq
      injection heq with _ hr
      injection hr with h01
      cases h01
    · intro hlay
      have h16eq8 : (16 : Nat) = 8 := by
        have hsome : some ({ size := 16, align := 8 } : Layout) = some { size := 8, align := 4 } := hlay
        injection hsome with hstruct
        exact congrArg Layout.size hstruct
      cases h16eq8
  · refine ⟨.param 0, .prim .u32, ?_, ?_, ?_, rfl, ?_⟩
    · intro p hp
      rw [← hp]
      exact Nat.zero_lt_succ 0
    · intro _ hp
      exact False.elim hp
    · intro heq
      cases heq
    · intro hlay
      have h8eq4 : (8 : Nat) = 4 := by
        have hsome : some ({ size := 8, align := 8 } : Layout) = some { size := 4, align := 4 } := hlay
        injection hsome with hstruct
        exact congrArg Layout.size hstruct
      cases h8eq4

/-- One-step recursive unfolding of `type Rec = impl Sized; fn make_rec(b: Option<Box<Rec>>) -> Rec { (1u32, b) }`
    (`tait_08`). -/
def expandRecStep (t : Ty) : Ty :=
  Ty.pair (.prim .u32) (.optBox t)

/-- `n`-step expansion of `Rec` starting from base type `seed` (models `-Z next-solver=globally`
    unrolling `(u32, Option<Box<...>>)` up to `recursion_limit`). -/
def expandRecN (n : Nat) (seed : Ty) : Ty :=
  Nat.rec seed (fun _ acc => expandRecStep acc) n

/-- Depth grows strictly at every expansion step (`tyDepth (expandRecStep t) = tyDepth t + 2`). -/
theorem tyDepth_expandRecStep (t : Ty) :
    tyDepth (expandRecStep t) = Nat.succ (Nat.succ (tyDepth t)) := by
  have hmax : Nat.max 0 (Nat.succ (tyDepth t)) = Nat.succ (tyDepth t) := by
    unfold Nat.max
    exact Nat.zero_max (Nat.succ (tyDepth t))
  change Nat.succ (Nat.max 0 (Nat.succ (tyDepth t))) = Nat.succ (Nat.succ (tyDepth t))
  rw [hmax]

theorem tyDepth_expandRecN_ge (seed : Ty) :
    ∀ n : Nat, n ≤ tyDepth (expandRecN n seed)
  | 0 => Nat.zero_le _
  | n + 1 => by
    change n + 1 ≤ tyDepth (expandRecStep (expandRecN n seed))
    rw [tyDepth_expandRecStep]
    exact nat_le_trans (Nat.succ_le_succ (tyDepth_expandRecN_ge seed n)) (Nat.le_succ _)

/-- Bounded-fuel cycle check vs. recursion-limit overflow model for `tait_08` (pure `Nat.rec`,
    zero `._unsafe_rec`):
    * `oldSolverCycleCheck` (`HasRecursiveOpaque`) flags the cycle immediately (`true` -> `E0720`).
    * `nextSolverUnrollRec` exhausts ANY finite recursion limit `limit` without reaching a concrete
      fixpoint (`none` -> `E0275` overflow in 1.102-nightly / `E0282` infer failure in 1.98-nightly). -/
def nextSolverUnrollRec (recId : OpaqueId) (fuel : Nat) : Ty → Option Ty :=
  Nat.rec (fun _ => none) (fun _ recNext t =>
    match t with
    | .opaqueTy id _ =>
      match Nat.beq id recId with
      | true => recNext (expandRecStep (.opaqueTy recId .nil))
      | false => some t
    | .pair l r =>
      match recNext l, recNext r with
      | some l', some r' => some (.pair l' r')
      | _, _ => none
    | .optBox inner =>
      match recNext inner with
      | some inner' => some (.optBox inner')
      | none => none
    | other => some other) fuel

theorem nextSolverUnrollRec_always_overflows (recId : OpaqueId) :
    ∀ fuel : Nat, nextSolverUnrollRec recId fuel (.opaqueTy recId .nil) = none
  | 0 => rfl
  | 1 => by
    change (match Nat.beq recId recId with
            | true => nextSolverUnrollRec recId 0 (expandRecStep (.opaqueTy recId .nil))
            | false => some (.opaqueTy recId .nil)) = none
    rw [Nat.beq_refl recId]
    rfl
  | 2 => by
    change (match Nat.beq recId recId with
            | true => nextSolverUnrollRec recId 1 (expandRecStep (.opaqueTy recId .nil))
            | false => some (.opaqueTy recId .nil)) = none
    rw [Nat.beq_refl recId]
    rfl
  | fuel + 3 => by
    have ih := nextSolverUnrollRec_always_overflows recId fuel
    change (match Nat.beq recId recId with
            | true => nextSolverUnrollRec recId (fuel + 2) (expandRecStep (.opaqueTy recId .nil))
            | false => some (.opaqueTy recId .nil)) = none
    rw [Nat.beq_refl recId]
    change (match nextSolverUnrollRec recId (fuel + 1) (.prim .u32),
                  nextSolverUnrollRec recId (fuel + 1) (.optBox (.opaqueTy recId .nil)) with
            | some l', some r' => some (Ty.pair l' r')
            | _, _ => none) = none
    have hopt : nextSolverUnrollRec recId (fuel + 1) (.optBox (.opaqueTy recId .nil)) = none := by
      change (match nextSolverUnrollRec recId fuel (.opaqueTy recId .nil) with
              | some inner' => some (Ty.optBox inner')
              | none => none) = none
      rw [ih]
    rw [hopt]
    rfl

/-- **Counterexample 3 (`ce3_self_referential_opaque_cycle_diverges_without_inductive_guard`)**:
    For the self-referential TAIT `Rec = (u32, Option<Box<Rec>>)` (`tait_08`):
      1. `HasRecursiveOpaque` (`MentionsOpaque recId`) holds directly on its body (`E0720`),
      2. No finite concrete `Ty` can be a fixpoint `t = (u32, Option<Box<t>>)` (strict AST depth
         increase `tyDepth t < tyDepth t + 2`),
      3. `n`-step expansion has unbounded AST depth `≥ n`, and
      4. Bounded-fuel unrolling overflows (`none`) at EVERY finite recursion limit `L : Nat`. -/
theorem ce3_self_referential_opaque_cycle_diverges_without_inductive_guard (recId : OpaqueId) :
    MentionsOpaque recId (expandRecStep (.opaqueTy recId .nil)) ∧
    (∀ t : Ty, t ≠ expandRecStep t) ∧
    (∀ n : Nat, n ≤ tyDepth (expandRecN n (.opaqueTy recId .nil))) ∧
    (∀ limit : Nat, nextSolverUnrollRec recId limit (.opaqueTy recId .nil) = none) := by
  refine ⟨Or.inr (Or.inl rfl), ?_, ?_, nextSolverUnrollRec_always_overflows recId⟩
  · intro t heq
    have hd : tyDepth t = tyDepth (expandRecStep t) := congrArg tyDepth heq
    rw [tyDepth_expandRecStep] at hd
    have hlt : tyDepth t < Nat.succ (Nat.succ (tyDepth t)) :=
      Nat.lt_trans (Nat.lt_succ_self (tyDepth t)) (Nat.lt_succ_self _)
    exact nat_ne_of_lt hlt hd
  · intro n
    exact tyDepth_expandRecN_ge (.opaqueTy recId .nil) n

/-- Concrete `World` modeling `rtn_01` (`PureWorker`) vs. `rtn_02` (`RcWorker`) where
    `Worker::run(..)` desugars to a hidden RPITIT coroutine future:
      * `PureWorker` (`Ty.prim .u32`): captures `&PureWorker` (`u64`), holds nothing non-`Send` across `.await`.
      * `RcWorker` (`Ty.prim .unit`): holds `Rc<u32>` (`PrimTy.rcU32`) across `.await`. -/
def pureWorkerTy : Ty := .prim .u32
def rcWorkerTy : Ty := .prim .unit
def runMethodId : AssocMethodId := 0
def pureFutureOpaqueId : OpaqueId := 10
def rcFutureOpaqueId : OpaqueId := 11

def rtnWorldDecls : OpaqueId → OpaqueDecl
  | 10 =>
    { arity := 0
      origin := .rpit 100
      itemTraitBounds := fun _ => False
      itemAutoBounds := fun _ => False
      witness := .coroutine (.prim .u32) (.cons (.prim .u64) .nil) .nil }
  | 11 =>
    { arity := 0
      origin := .rpit 101
      itemTraitBounds := fun _ => False
      itemAutoBounds := fun _ => False
      witness := .coroutine (.prim .u32) .nil (.cons (.prim .rcU32) .nil) }
  | _ =>
    { arity := 0
      origin := .tait
      itemTraitBounds := fun _ => False
      itemAutoBounds := fun _ => False
      witness := .prim .unit }

def rtnWorld : World where
  decls := rtnWorldDecls
  rank := fun _ => 0
  stratified := by
    intro oid
    match oid with
    | 10 => exact ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
    | 11 => exact ⟨trivial, trivial, ⟨trivial, trivial⟩⟩
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | _ + 12 => exact trivial
  witnessWellKinded := by
    intro oid p hp
    match oid with
    | 10 =>
      rcases hp with h1 | h2 | h3
      · exact False.elim h1
      · rcases h2 with h2a | h2b
        · exact False.elim h2a
        · exact False.elim h2b
      · exact False.elim h3
    | 11 =>
      rcases hp with h1 | h2 | h3
      · exact False.elim h1
      · exact False.elim h2
      · rcases h3 with h3a | h3b
        · exact False.elim h3a
        · exact False.elim h3b
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | _ + 12 => exact False.elim hp
  concreteTrait := fun _ _ => True
  rpititFuture := fun implTy _ =>
    match implTy with
    | .prim .u32  => .opaqueTy pureFutureOpaqueId .nil
    | .prim .unit => .opaqueTy rcFutureOpaqueId .nil
    | _ => .prim .unit

theorem rtnWorld_sound : SoundWorld rtnWorld where
  itemTraitsSound := by
    intro oid _ _ hb
    match oid with
    | 10 => exact False.elim hb
    | 11 => exact False.elim hb
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | _ + 12 => exact False.elim hb
  itemAutosSound := by
    intro oid _ _ hb
    match oid with
    | 10 => exact False.elim hb
    | 11 => exact False.elim hb
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | _ + 12 => exact False.elim hb

/-- **Counterexample 4 (`ce4_rtn_rc_across_await_violates_send`)**:
    Under `Reveal::UserFacing`, the RTN bound `W: Worker<run(..): Send>` (lowered to an
    auto-trait obligation on the hidden RPITIT coroutine future):
      1. HOLDS for `PureWorker` (`rtn_01`: captures `u64`, zero non-`Send` locals across `.await`),
      2. FAILS for `RcWorker` (`rtn_02`: holds `Rc<u32>` across `.await`, violating `Send`), and
      3. FAILS `Unpin` even for `PureWorker` (immovable async coroutine future). -/
theorem ce4_rtn_rc_across_await_violates_send :
    Entails rtnWorld .userFacing (.rtnBound pureWorkerTy runMethodId .send) ∧
    ¬ Entails rtnWorld .userFacing (.rtnBound rcWorkerTy runMethodId .send) ∧
    ¬ Entails rtnWorld .userFacing (.rtnBound pureWorkerTy runMethodId .unpin) := by
  refine ⟨?_, ?_, ?_⟩
  · change UserFacingAutoTrait rtnWorld .send (.opaqueTy pureFutureOpaqueId .nil)
    refine Or.inr ?_
    have hconc : eraseAll rtnWorld (instantiate (rtnWorld.decls pureFutureOpaqueId).witness .nil) =
        .coroutine (.prim .u32) (.cons (.prim .u64) .nil) .nil :=
      eraseAll_of_isConcrete rtnWorld _ ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
    rw [hconc]
    exact ⟨⟨trivial, trivial⟩, trivial⟩
  · intro h
    have hr := userFacing_refines_revealAll rtnWorld rtnWorld_sound
      (.rtnBound rcWorkerTy runMethodId .send) h
    change AutoTraitConcrete .send (eraseAll rtnWorld (.opaqueTy rcFutureOpaqueId .nil)) at hr
    rw [eraseAll_opaque_eq_witness] at hr
    have hconc : eraseAll rtnWorld (instantiate (rtnWorld.decls rcFutureOpaqueId).witness .nil) =
        .coroutine (.prim .u32) .nil (.cons (.prim .rcU32) .nil) :=
      eraseAll_of_isConcrete rtnWorld _ ⟨trivial, trivial, ⟨trivial, trivial⟩⟩
    rw [hconc] at hr
    exact hr.2.1
  · intro h
    have hr := userFacing_refines_revealAll rtnWorld rtnWorld_sound
      (.rtnBound pureWorkerTy runMethodId .unpin) h
    change AutoTraitConcrete .unpin (eraseAll rtnWorld (.opaqueTy pureFutureOpaqueId .nil)) at hr
    rw [eraseAll_opaque_eq_witness] at hr
    have hconc : eraseAll rtnWorld (instantiate (rtnWorld.decls pureFutureOpaqueId).witness .nil) =
        .coroutine (.prim .u32) (.cons (.prim .u64) .nil) .nil :=
      eraseAll_of_isConcrete rtnWorld _ ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
    rw [hconc] at hr
    exact hr

/-- Concrete cross-crate TAIT witness (`tait_13`: `Secret = [u64; 3]`, `Copy` exposed,
    `Index`/`Add` hidden) showing STRICTNESS of `userFacing_refines_revealAll`:
      * `Secret` satisfies `Copy` (`tr = 0`) and `Send` + `Sync` + `Unpin` under `userFacing`,
      * `Secret` exposes exact `[u64; 3]` layout `{ size := 24, align := 8 }` under `userFacing`
        via `layout_of` -> `Reveal::All`,
      * `Secret` DOES NOT satisfy unexposed `Index` (`tr = 1`) or `Secret = [u64; 3]` under
        `userFacing`, while BOTH hold under `revealAll`. -/
def traitCopyId : TraitId := 0
def traitIndexId : TraitId := 1
def secretOpaqueId : OpaqueId := 20

def secretWorld : World where
  decls := fun oid =>
    match oid with
    | 20 =>
      { arity := 0
        origin := .tait
        itemTraitBounds := fun tr => tr = traitCopyId
        itemAutoBounds := fun _ => False
        witness := .arr (.prim .u64) 3 }
    | _ =>
      { arity := 0
        origin := .tait
        itemTraitBounds := fun _ => False
        itemAutoBounds := fun _ => False
        witness := .prim .unit }
  rank := fun _ => 0
  stratified := by
    intro oid
    match oid with
    | 20 => exact trivial
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
    | _ + 21 => exact trivial
  witnessWellKinded := by
    intro oid _ hp
    match oid with
    | 20 => exact False.elim hp
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
    | _ + 21 => exact False.elim hp
  concreteTrait := fun tr t =>
    (tr = traitCopyId ∧ t = .arr (.prim .u64) 3) ∨
    (tr = traitIndexId ∧ t = .arr (.prim .u64) 3)
  rpititFuture := fun _ _ => .prim .unit

theorem secretWorld_sound : SoundWorld secretWorld where
  itemTraitsSound := by
    intro oid tr args hb
    match oid with
    | 20 =>
      have htr : tr = traitCopyId := hb
      have hconc : eraseAll secretWorld (instantiate (secretWorld.decls 20).witness args) =
          .arr (.prim .u64) 3 :=
        eraseAll_of_isConcrete secretWorld _ trivial
      rw [hconc]
      exact Or.inl ⟨htr, rfl⟩
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
    | _ + 21 => exact False.elim hb
  itemAutosSound := by
    intro oid _ _ hb
    match oid with
    | 20 => exact False.elim hb
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
    | _ + 21 => exact False.elim hb

theorem three_phase_visibility_strict_separation :
    Entails secretWorld .userFacing (.userTrait traitCopyId (.opaqueTy secretOpaqueId .nil)) ∧
    ¬ Entails secretWorld .userFacing (.userTrait traitIndexId (.opaqueTy secretOpaqueId .nil)) ∧
    Entails secretWorld .revealAll (.userTrait traitIndexId (.opaqueTy secretOpaqueId .nil)) ∧
    ¬ Entails secretWorld .userFacing (.tyEq (.opaqueTy secretOpaqueId .nil) (.arr (.prim .u64) 3)) ∧
    Entails secretWorld .revealAll (.tyEq (.opaqueTy secretOpaqueId .nil) (.arr (.prim .u64) 3)) ∧
    Entails secretWorld .userFacing (.autoTrait .send (.opaqueTy secretOpaqueId .nil)) ∧
    Entails secretWorld .userFacing (.hasLayout (.opaqueTy secretOpaqueId .nil) { size := 24, align := 8 }) := by
  have herase : eraseAll secretWorld (.opaqueTy secretOpaqueId .nil) = .arr (.prim .u64) 3 := by
    rw [eraseAll_opaque_eq_witness]
    exact eraseAll_of_isConcrete secretWorld _ trivial
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h10 : (1 : Nat) = 0 := h
    cases h10
  · change secretWorld.concreteTrait traitIndexId (eraseAll secretWorld (.opaqueTy secretOpaqueId .nil))
    rw [herase]
    exact Or.inr ⟨rfl, rfl⟩
  · intro heq
    cases heq
  · change eraseAll secretWorld (.opaqueTy secretOpaqueId .nil) = eraseAll secretWorld (.arr (.prim .u64) 3)
    rw [herase, eraseAll_of_isConcrete secretWorld (.arr (.prim .u64) 3) trivial]
  · refine Or.inr ?_
    have hw : eraseAll secretWorld (instantiate (secretWorld.decls secretOpaqueId).witness .nil) =
        .arr (.prim .u64) 3 := eraseAll_of_isConcrete secretWorld _ trivial
    rw [hw]
    trivial
  · change layoutOfConcrete (eraseAll secretWorld (.opaqueTy secretOpaqueId .nil)) =
      some { size := 24, align := 8 }
    rw [herase]
    rfl

end Anneal.OpaqueTypeSoundness
