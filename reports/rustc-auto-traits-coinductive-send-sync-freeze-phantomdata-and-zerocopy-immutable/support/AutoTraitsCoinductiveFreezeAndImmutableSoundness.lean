/-!
# Soundness Model: Coinductive Auto-Trait Selection (`Send`/`Sync`/`Unpin`/`Freeze`),
# the `PhantomData<UnsafeCell<u32>>` Four-Way Asymmetry, Async Coroutine Cross-`.await`
# `Send` Leaks, and `zerocopy::Immutable` Byte-Level Interior-Mutability Freedom

Standalone kernel-checked Lean `v4.34.1` formalization companion to the reference report
`rustc-auto-traits-coinductive-send-sync-freeze-phantomdata-and-zerocopy-immutable`.

Design and TCB purity invariants verified by the Lean kernel:
- Zero `sorry`, zero `Classical.choice`, zero `Quot.sound`, zero `omega`,
  zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
- Every `def` is marked `noncomputable def` (with no `noncomputable section` and no
  `deriving` clauses) so Lean never synthesizes `._unsafe_rec` codegen helpers,
  while every proof remains purely constructive.
-/

namespace AutoTraitsCoinductiveImmutable

/-!
## Part 1: Trait Predicates, Finite Type Graphs, and Structural List Primitives
-/

/-- The four language auto traits modeled directly from `library/core/src/marker.rs`. -/
inductive AutoTrait where
  | send
  | sync
  | unpin
  | freeze

/-- Unified predicate language combining the four coinductive `rustc` auto traits
and the non-coinductive user unsafe marker trait `zerocopy::Immutable`. -/
inductive TraitPred where
  | auto (a : AutoTrait)
  | immutable

/-- Whether a `TraitPred` is coinductive (`tcx.trait_is_coinductive`).
Auto traits (`Send`, `Sync`, `Unpin`, `Freeze`) are coinductive; `zerocopy::Immutable`
is a regular unsafe trait (inductive unless a concrete impl avoids cycles). -/
noncomputable def isCoinductivePred : TraitPred → Bool
  | .auto _ => true
  | .immutable => false

/-- Unsafe auto traits (`Send`, `Sync`, `Freeze`) are suppressed by `rustc` on ADTs
that declare `unsafe` fields (`self_ty.has_unsafe_fields()`), whereas safe `Unpin` is not. -/
noncomputable def isUnsafeAuto : AutoTrait → Bool
  | .send => true
  | .sync => true
  | .unpin => false
  | .freeze => true

/-- Structural boolean equality for `AutoTrait`. -/
noncomputable def AutoTrait.beq : AutoTrait → AutoTrait → Bool
  | .send, .send => true
  | .sync, .sync => true
  | .unpin, .unpin => true
  | .freeze, .freeze => true
  | _, _ => false

theorem AutoTrait.beq_refl (a : AutoTrait) : AutoTrait.beq a a = true := by
  cases a <;> rfl

theorem AutoTrait.eq_of_beq {a b : AutoTrait} (h : AutoTrait.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem AutoTrait.beq_iff (a b : AutoTrait) : AutoTrait.beq a b = true ↔ a = b := by
  constructor
  · exact AutoTrait.eq_of_beq
  · intro h; subst h; exact AutoTrait.beq_refl a

/-- Structural boolean equality for `TraitPred`. -/
noncomputable def TraitPred.beq : TraitPred → TraitPred → Bool
  | .auto a, .auto b => AutoTrait.beq a b
  | .immutable, .immutable => true
  | _, _ => false

theorem TraitPred.beq_refl (p : TraitPred) : TraitPred.beq p p = true := by
  cases p with
  | auto a => exact AutoTrait.beq_refl a
  | immutable => rfl

theorem TraitPred.eq_of_beq {p q : TraitPred} (h : TraitPred.beq p q = true) : p = q := by
  cases p <;> cases q
  case auto.auto a b =>
    have hab : a = b := AutoTrait.eq_of_beq h
    subst hab
    rfl
  case immutable.immutable => rfl
  case auto.immutable => cases h
  case immutable.auto => cases h

theorem TraitPred.beq_iff (p q : TraitPred) : TraitPred.beq p q = true ↔ p = q := by
  constructor
  · exact TraitPred.eq_of_beq
  · intro h; subst h; exact TraitPred.beq_refl p

/-- Graph vertex identifiers representing Rust types in a finite type graph. -/
abbrev NodeId := Nat

/-- Structural boolean equality on `(TraitPred, NodeId)` stack entries. -/
noncomputable def pairPredNodeBeq (x y : TraitPred × NodeId) : Bool :=
  TraitPred.beq x.1 y.1 && Nat.beq x.2 y.2

theorem pairPredNodeBeq_refl (x : TraitPred × NodeId) : pairPredNodeBeq x x = true := by
  cases x with
  | mk p n =>
    dsimp [pairPredNodeBeq]
    rw [TraitPred.beq_refl p]
    exact Nat.beq_refl n

theorem pairPredNode_eq_of_beq {x y : TraitPred × NodeId}
    (h : pairPredNodeBeq x y = true) : x = y := by
  cases x with
  | mk px nx =>
    cases y with
    | mk py ny =>
      dsimp [pairPredNodeBeq] at h
      cases hp : TraitPred.beq px py
      · rw [hp] at h; cases h
      · rw [hp] at h
        have h1 : px = py := TraitPred.eq_of_beq hp
        have h2 : nx = ny := Nat.eq_of_beq_eq_true h
        subst h1
        subst h2
        rfl

/-- Kind of type node inside a finite type graph. -/
inductive NodeKind where
  | prim (byteSize : Nat)
  | rawPtr (pointee : NodeId)
  | refShared (pointee : NodeId)
  | refMut (pointee : NodeId)
  | boxPtr (pointee : NodeId)
  | rcPtr (pointee : NodeId)
  | unsafeCell (inner : NodeId) (byteSize : Nat)
  | phantomData (inner : NodeId)
  | phantomPinned
  | adtStruct (fields : List NodeId) (hasUnsafeField : Bool)
      (negAuto : AutoTrait → Bool) (immImpl : Bool)
  | rpitOpaque (hidden : NodeId)
  | dynObj (declared : List AutoTrait)

/-- Finite type graph modeling `rustc` ADTs, pointers, `PhantomData`, `UnsafeCell`,
opaque return types, trait objects, and `zerocopy::Immutable` size-gated impls. -/
structure TypeGraph where
  bound : Nat
  kindOf : NodeId → NodeKind
  boxSized : NodeId → Bool

/-- Constructive inductive list membership predicate. -/
inductive Mem {α : Type} (x : α) : List α → Prop where
  | head {xs : List α} : Mem x (x :: xs)
  | tail {y : α} {xs : List α} : Mem x xs → Mem x (y :: xs)

/-- Constructive universal quantification over list elements. -/
inductive AllProp {α : Type} (P : α → Prop) : List α → Prop where
  | nil : AllProp P []
  | cons {x : α} {xs : List α} : P x → AllProp P xs → AllProp P (x :: xs)

theorem AllProp_mono {α : Type} {P Q : α → Prop}
    (hPQ : ∀ x, P x → Q x) {xs : List α} (h : AllProp P xs) : AllProp Q xs := by
  induction h with
  | nil => exact AllProp.nil
  | cons hp _ ih => exact AllProp.cons (hPQ _ hp) ih

theorem AllProp_mem {α : Type} {P : α → Prop} {xs : List α}
    (hAll : AllProp P xs) {x : α} (hMem : Mem x xs) : P x := by
  induction hAll with
  | nil => cases hMem
  | cons hp _ ih =>
    cases hMem with
    | head => exact hp
    | tail hm => exact ih hm

theorem AllProp_of_forall {α : Type} {P : α → Prop} {xs : List α}
    (h : ∀ x, Mem x xs → P x) : AllProp P xs := by
  induction xs with
  | nil => exact AllProp.nil
  | cons y ys ih =>
    apply AllProp.cons
    · exact h y Mem.head
    · exact ih (fun x hx => h x (Mem.tail hx))

theorem AllProp_append {α : Type} {P : α → Prop} {xs ys : List α}
    (hx : AllProp P xs) (hy : AllProp P ys) : AllProp P (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons h1 _ ih => exact AllProp.cons h1 ih

theorem Mem_append_left {α : Type} {x : α} {xs ys : List α}
    (h : Mem x xs) : Mem x (xs ++ ys) := by
  induction h with
  | head => exact Mem.head
  | tail _ ih => exact Mem.tail ih

theorem Mem_append_right {α : Type} {x : α} (xs : List α) {ys : List α}
    (h : Mem x ys) : Mem x (xs ++ ys) := by
  induction xs with
  | nil => exact h
  | cons _ _ ih => exact Mem.tail ih

theorem Mem_split_append {α : Type} {x : α} {xs ys : List α}
    (h : Mem x (xs ++ ys)) : Mem x xs ∨ Mem x ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons z zs ih =>
    cases h with
    | head => exact Or.inl Mem.head
    | tail ht =>
      cases ih ht with
      | inl hzs => exact Or.inl (Mem.tail hzs)
      | inr hys => exact Or.inr hys

/-- Subset inclusion on constructive lists. -/
abbrev SubList {α : Type} (xs ys : List α) : Prop :=
  ∀ x, Mem x xs → Mem x ys

theorem SubList_refl {α : Type} (xs : List α) : SubList xs xs :=
  fun _ h => h

theorem SubList_cons {α : Type} (a : α) (xs : List α) : SubList xs (a :: xs) :=
  fun _ h => Mem.tail h

/-- Boolean membership over `AutoTrait` lists. -/
noncomputable def memAutoBool (a : AutoTrait) : List AutoTrait → Bool
  | [] => false
  | x :: xs => AutoTrait.beq a x || memAutoBool a xs

theorem memAutoBool_iff (a : AutoTrait) (xs : List AutoTrait) :
    memAutoBool a xs = true ↔ Mem a xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    dsimp [memAutoBool]
    cases hb : AutoTrait.beq a y
    · constructor
      · intro h
        exact Mem.tail ((ih).mp h)
      · intro h
        cases h with
        | head =>
          rw [AutoTrait.beq_refl a] at hb
          cases hb
        | tail ht =>
          exact (ih).mpr ht
    · constructor
      · intro _
        have hEq : a = y := AutoTrait.eq_of_beq hb
        subst hEq
        exact Mem.head
      · intro _
        rfl

/-- Boolean membership over `(TraitPred × NodeId)` lists. -/
noncomputable def memPairBool (x : TraitPred × NodeId) : List (TraitPred × NodeId) → Bool
  | [] => false
  | y :: ys => pairPredNodeBeq x y || memPairBool x ys

theorem memPairBool_iff (x : TraitPred × NodeId) (xs : List (TraitPred × NodeId)) :
    memPairBool x xs = true ↔ Mem x xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    dsimp [memPairBool]
    cases hb : pairPredNodeBeq x y
    · constructor
      · intro h
        exact Mem.tail ((ih).mp h)
      · intro h
        cases h with
        | head =>
          rw [pairPredNodeBeq_refl x] at hb
          cases hb
        | tail ht =>
          exact (ih).mpr ht
    · constructor
      · intro _
        have hEq : x = y := pairPredNode_eq_of_beq hb
        subst hEq
        exact Mem.head
      · intro _
        rfl

/-- Universal boolean check over a list. -/
noncomputable def allBool {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allBool p xs

theorem allBool_iff {α : Type} (p : α → Bool) (xs : List α) :
    allBool p xs = true ↔ AllProp (fun x => p x = true) xs := by
  induction xs with
  | nil =>
    constructor
    · intro _; exact AllProp.nil
    · intro _; rfl
  | cons y ys ih =>
    dsimp [allBool]
    cases hp : p y
    · constructor
      · intro h; cases h
      · intro h
        cases h with
        | cons hy _ => rw [hy] at hp; cases hp
    · constructor
      · intro h
        exact AllProp.cons hp ((ih).mp h)
      · intro h
        cases h with
        | cons _ hys => exact (ih).mpr hys

/-- Boolean range check `[0, ..., k - 1]` for finite graph fixed-point verification. -/
noncomputable def allBelowBool (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => p k && allBelowBool p k

theorem allBelowBool_iff (p : Nat → Bool) (k : Nat) :
    allBelowBool p k = true ↔ ∀ n, n < k → p n = true := by
  induction k with
  | zero =>
    constructor
    · intro _ n hn; cases hn
    · intro _; rfl
  | succ k ih =>
    dsimp [allBelowBool]
    cases hpk : p k
    · constructor
      · intro h; cases h
      · intro h
        have hk : p k = true := h k (Nat.lt_succ_self k)
        rw [hk] at hpk
        cases hpk
    · constructor
      · intro h n hn
        cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with
        | inl hEq =>
          subst hEq
          exact hpk
        | inr hlt =>
          exact (ih).mp h n hlt
      · intro h
        exact (ih).mpr (fun n hn => h n (Nat.lt_trans hn (Nat.lt_succ_self k)))

/-!
## Part 2: Monotone One-Step Trait Operator `StepF` and Tarski Greatest Fixpoint `CoindSat`
-/

/-- One-step monotone semantic operator `StepF g S tr n` matching `rustc`'s
`assemble_candidates_from_auto_impls`, `constituent_types_for_auto_trait`,
`library/core/src/marker.rs`, and `google/zerocopy`'s `Immutable` impls:
- `rawPtr`: `!Send`, `!Sync`, `+Unpin`, `+Freeze`, `+Immutable`.
- `refShared p`: `Send ↔ p: Sync`, `Sync ↔ p: Sync`, `+Unpin`, `+Freeze`, `+Immutable`.
- `refMut p`: `Send ↔ p: Send`, `Sync ↔ p: Sync`, `+Unpin`, `+Freeze`, `+Immutable`.
- `boxPtr p`: `Send ↔ p: Send`, `Sync ↔ p: Sync`, `+Unpin`, `+Freeze`, `Immutable ↔ boxSized p`.
- `rcPtr`: `!Send`, `!Sync`, `+Unpin`, `+Freeze`, `!Immutable`.
- `unsafeCell inner _`: `Send ↔ inner: Send`, `!Sync`, `Unpin ↔ inner: Unpin`, `!Freeze`, `!Immutable`.
- `phantomData inner`: **explicit `+Freeze` and `+Immutable` overrides**, while
  `Send`/`Sync`/`Unpin` pass `[inner]` through `constituent_types_for_auto_trait`.
- `phantomPinned`: `+Send`, `+Sync`, `!Unpin`, `+Freeze`, `+Immutable`.
- `adtStruct`: explicit `negAuto` + unsafe-field guard (`hasUnsafeField`) + field conjunction;
  `Immutable` requires `immImpl = true` and field conjunction.
- `rpitOpaque`: leaks auto traits of `hidden`; does not synthesize non-auto `Immutable`.
- `dynObj`: auto traits hold iff explicitly declared; does not satisfy `Immutable`.
-/
noncomputable def StepF (g : TypeGraph) (S : TraitPred → NodeId → Prop)
    (tr : TraitPred) (n : NodeId) : Prop :=
  match tr, g.kindOf n with
  | .auto a, .prim _ =>
    match a with
    | .send => True
    | .sync => True
    | .unpin => True
    | .freeze => True
  | .auto a, .rawPtr _ =>
    match a with
    | .send => False
    | .sync => False
    | .unpin => True
    | .freeze => True
  | .auto a, .refShared p =>
    match a with
    | .send => S (.auto .sync) p
    | .sync => S (.auto .sync) p
    | .unpin => True
    | .freeze => True
  | .auto a, .refMut p =>
    match a with
    | .send => S (.auto .send) p
    | .sync => S (.auto .sync) p
    | .unpin => True
    | .freeze => True
  | .auto a, .boxPtr p =>
    match a with
    | .send => S (.auto .send) p
    | .sync => S (.auto .sync) p
    | .unpin => True
    | .freeze => True
  | .auto a, .rcPtr _ =>
    match a with
    | .send => False
    | .sync => False
    | .unpin => True
    | .freeze => True
  | .auto a, .unsafeCell inner _ =>
    match a with
    | .send => S (.auto .send) inner
    | .sync => False
    | .unpin => S (.auto .unpin) inner
    | .freeze => False
  | .auto a, .phantomData inner =>
    match a with
    | .send => S (.auto .send) inner
    | .sync => S (.auto .sync) inner
    | .unpin => S (.auto .unpin) inner
    | .freeze => True
  | .auto a, .phantomPinned =>
    match a with
    | .send => True
    | .sync => True
    | .unpin => False
    | .freeze => True
  | .auto a, .adtStruct fields hasUnsafe negAuto _ =>
    negAuto a = false ∧
    (isUnsafeAuto a = true → hasUnsafe = false) ∧
    AllProp (fun f => S (.auto a) f) fields
  | .auto a, .rpitOpaque hidden =>
    S (.auto a) hidden
  | .auto a, .dynObj declared =>
    Mem a declared
  | .immutable, .prim _ => True
  | .immutable, .rawPtr _ => True
  | .immutable, .refShared _ => True
  | .immutable, .refMut _ => True
  | .immutable, .boxPtr p => g.boxSized p = true
  | .immutable, .rcPtr _ => False
  | .immutable, .unsafeCell _ _ => False
  | .immutable, .phantomData _ => True
  | .immutable, .phantomPinned => True
  | .immutable, .adtStruct fields _ _ immImpl =>
    immImpl = true ∧ AllProp (fun f => S .immutable f) fields
  | .immutable, .rpitOpaque _ => False
  | .immutable, .dynObj _ => False

/-- Monotonicity of `StepF` with respect to predicate implication. -/
theorem StepF_mono (g : TypeGraph) {P Q : TraitPred → NodeId → Prop}
    (hPQ : ∀ tr n, P tr n → Q tr n) :
    ∀ tr n, StepF g P tr n → StepF g Q tr n := by
  intro tr n hP
  cases tr with
  | auto a =>
    dsimp [StepF] at hP ⊢
    revert hP
    cases g.kindOf n with
    | prim _ => exact id
    | rawPtr _ => exact id
    | refShared p =>
      intro hP
      cases a <;> first | exact hP | exact hPQ _ _ hP
    | refMut p =>
      intro hP
      cases a <;> first | exact hP | exact hPQ _ _ hP
    | boxPtr p =>
      intro hP
      cases a <;> first | exact hP | exact hPQ _ _ hP
    | rcPtr _ => exact id
    | unsafeCell inner _ =>
      intro hP
      cases a <;> first | exact hP | exact hPQ _ _ hP
    | phantomData inner =>
      intro hP
      cases a <;> first | exact hP | exact hPQ _ _ hP
    | phantomPinned => exact id
    | adtStruct fields hasUnsafe negAuto immImpl =>
      intro hP
      rcases hP with ⟨hNeg, hUns, hAll⟩
      exact ⟨hNeg, hUns, AllProp_mono (fun f hf => hPQ (.auto a) f hf) hAll⟩
    | rpitOpaque hidden =>
      intro hP
      exact hPQ (.auto a) hidden hP
    | dynObj declared => exact id
  | immutable =>
    dsimp [StepF] at hP ⊢
    revert hP
    cases g.kindOf n with
    | adtStruct fields hasUnsafe negAuto immImpl =>
      intro hP
      rcases hP with ⟨hImm, hAll⟩
      exact ⟨hImm, AllProp_mono (fun f hf => hPQ .immutable f hf) hAll⟩
    | prim _ => exact id
    | rawPtr _ => exact id
    | refShared _ => exact id
    | refMut _ => exact id
    | boxPtr _ => exact id
    | rcPtr _ => exact id
    | unsafeCell _ _ => exact id
    | phantomData _ => exact id
    | phantomPinned => exact id
    | rpitOpaque _ => exact id
    | dynObj _ => exact id

/-- Post-fixed invariant predicate (`P ⊆ StepF g P`), i.e., a coinductively consistent
set of trait judgments. -/
abbrev IsPostFixed (g : TypeGraph) (P : TraitPred → NodeId → Prop) : Prop :=
  ∀ tr n, P tr n → StepF g P tr n

/-- Tarski greatest fixpoint (impredicative coinductive satisfaction) of `StepF g`.
Requires zero classical axioms (`Prop`-level existential over post-fixed invariants). -/
inductive CoindSat (g : TypeGraph) (tr : TraitPred) (n : NodeId) : Prop where
  | intro (P : TraitPred → NodeId → Prop) (hPost : IsPostFixed g P) (hMem : P tr n) :
      CoindSat g tr n

/-- Coinduction principle: to establish `CoindSat g tr n`, exhibit any post-fixed
invariant `P` containing `(tr, n)`. -/
theorem coind_principle (g : TypeGraph) (P : TraitPred → NodeId → Prop)
    (hPost : IsPostFixed g P) {tr : TraitPred} {n : NodeId} (hMem : P tr n) :
    CoindSat g tr n :=
  CoindSat.intro P hPost hMem

/-- Every coinductive witness `P` is pointwise contained in `CoindSat g`. -/
theorem coindSat_greatest {g : TypeGraph} {P : TraitPred → NodeId → Prop}
    (hPost : IsPostFixed g P) : ∀ tr n, P tr n → CoindSat g tr n :=
  fun _ _ h => CoindSat.intro P hPost h

/-- Unrolling lemma (`CoindSat g tr n → StepF g (CoindSat g) tr n`). -/
theorem coindSat_unfold {g : TypeGraph} {tr : TraitPred} {n : NodeId}
    (h : CoindSat g tr n) : StepF g (CoindSat g) tr n := by
  cases h with
  | intro P hPost hMem =>
    have hStepP : StepF g P tr n := hPost tr n hMem
    exact StepF_mono g (coindSat_greatest hPost) tr n hStepP

/-- `CoindSat g` is itself post-fixed. -/
theorem coindSat_isPostFixed (g : TypeGraph) : IsPostFixed g (CoindSat g) :=
  fun _ _ h => coindSat_unfold h

/-- Folding lemma (`StepF g (CoindSat g) tr n → CoindSat g tr n`). -/
theorem coindSat_fold {g : TypeGraph} {tr : TraitPred} {n : NodeId}
    (h : StepF g (CoindSat g) tr n) : CoindSat g tr n := by
  let Q : TraitPred → NodeId → Prop := fun t m => CoindSat g t m ∨ StepF g (CoindSat g) t m
  have hQ : IsPostFixed g Q := by
    intro t m hm
    have hStepCoind : StepF g (CoindSat g) t m := by
      cases hm with
      | inl hc => exact coindSat_unfold hc
      | inr hs => exact hs
    exact StepF_mono g (fun _ _ hsat => Or.inl hsat) t m hStepCoind
  exact CoindSat.intro Q hQ (Or.inr h)

/-- Full fixpoint equation for `CoindSat g`. -/
theorem coindSat_iff_step (g : TypeGraph) (tr : TraitPred) (n : NodeId) :
    CoindSat g tr n ↔ StepF g (CoindSat g) tr n :=
  ⟨coindSat_unfold, coindSat_fold⟩

/-- Specialization: `PhantomData<T>` unconditionally satisfies `Freeze`. -/
theorem coindSat_phantomData_freeze {g : TypeGraph} {n inner : NodeId}
    (hk : g.kindOf n = .phantomData inner) : CoindSat g (.auto .freeze) n := by
  apply coindSat_fold
  dsimp [StepF]
  rw [hk]
  trivial

/-- Specialization: `PhantomData<T>` unconditionally satisfies `zerocopy::Immutable`. -/
theorem coindSat_phantomData_immutable {g : TypeGraph} {n inner : NodeId}
    (hk : g.kindOf n = .phantomData inner) : CoindSat g .immutable n := by
  apply coindSat_fold
  dsimp [StepF]
  rw [hk]
  trivial

/-- Specialization: `PhantomData<T>` delegates `Send`/`Sync`/`Unpin` to `T`. -/
theorem coindSat_phantomData_sync_iff {g : TypeGraph} {n inner : NodeId}
    (hk : g.kindOf n = .phantomData inner) :
    CoindSat g (.auto .sync) n ↔ CoindSat g (.auto .sync) inner := by
  constructor
  · intro h
    have hs := coindSat_unfold h
    dsimp [StepF] at hs
    rw [hk] at hs
    exact hs
  · intro h
    apply coindSat_fold
    dsimp [StepF]
    rw [hk]
    exact h

/-- Specialization: `UnsafeCell<T>` never satisfies `Sync`, `Freeze`, or `Immutable`. -/
theorem coindSat_unsafeCell_not_sync {g : TypeGraph} {n inner sz : NodeId}
    (hk : g.kindOf n = .unsafeCell inner sz) : ¬ CoindSat g (.auto .sync) n := by
  intro h
  have hs := coindSat_unfold h
  dsimp [StepF] at hs
  rw [hk] at hs
  exact hs

theorem coindSat_unsafeCell_not_freeze {g : TypeGraph} {n inner sz : NodeId}
    (hk : g.kindOf n = .unsafeCell inner sz) : ¬ CoindSat g (.auto .freeze) n := by
  intro h
  have hs := coindSat_unfold h
  dsimp [StepF] at hs
  rw [hk] at hs
  exact hs

theorem coindSat_unsafeCell_not_immutable {g : TypeGraph} {n inner sz : NodeId}
    (hk : g.kindOf n = .unsafeCell inner sz) : ¬ CoindSat g .immutable n := by
  intro h
  have hs := coindSat_unfold h
  dsimp [StepF] at hs
  rw [hk] at hs
  exact hs

/-!
## Part 3: Reachable Negative-Leaf Rejection, Visited-Stack DFS Checker, and Kleene GFP
-/

/-- One-step constituent obligation edge `(a, src) ↦ (a', dst)` extracted from `StepF`.
Notice that positive overrides (`PhantomData` for `.freeze`, indirections for `.freeze`/`.unpin`)
emit NO outgoing edge, capturing exact override cutoffs. -/
inductive AutoConstituentStep (g : TypeGraph) :
    AutoTrait → NodeId → AutoTrait → NodeId → Prop where
  | refSharedSend {src p : NodeId} :
      g.kindOf src = .refShared p → AutoConstituentStep g .send src .sync p
  | refSharedSync {src p : NodeId} :
      g.kindOf src = .refShared p → AutoConstituentStep g .sync src .sync p
  | refMutSend {src p : NodeId} :
      g.kindOf src = .refMut p → AutoConstituentStep g .send src .send p
  | refMutSync {src p : NodeId} :
      g.kindOf src = .refMut p → AutoConstituentStep g .sync src .sync p
  | boxPtrSend {src p : NodeId} :
      g.kindOf src = .boxPtr p → AutoConstituentStep g .send src .send p
  | boxPtrSync {src p : NodeId} :
      g.kindOf src = .boxPtr p → AutoConstituentStep g .sync src .sync p
  | unsafeCellSend {src inner sz : NodeId} :
      g.kindOf src = .unsafeCell inner sz → AutoConstituentStep g .send src .send inner
  | unsafeCellUnpin {src inner sz : NodeId} :
      g.kindOf src = .unsafeCell inner sz → AutoConstituentStep g .unpin src .unpin inner
  | phantomSend {src inner : NodeId} :
      g.kindOf src = .phantomData inner → AutoConstituentStep g .send src .send inner
  | phantomSync {src inner : NodeId} :
      g.kindOf src = .phantomData inner → AutoConstituentStep g .sync src .sync inner
  | phantomUnpin {src inner : NodeId} :
      g.kindOf src = .phantomData inner → AutoConstituentStep g .unpin src .unpin inner
  | adtField {src dst : NodeId} {a : AutoTrait} {fields : List NodeId}
      {hasUnsafe : Bool} {negAuto : AutoTrait → Bool} {immImpl : Bool} :
      g.kindOf src = .adtStruct fields hasUnsafe negAuto immImpl →
      negAuto a = false →
      (isUnsafeAuto a = true → hasUnsafe = false) →
      Mem dst fields →
      AutoConstituentStep g a src a dst
  | rpitStep {src hidden : NodeId} {a : AutoTrait} :
      g.kindOf src = .rpitOpaque hidden → AutoConstituentStep g a src a hidden

/-- Multi-step constituent obligation reachability. -/
inductive AutoReach (g : TypeGraph) :
    AutoTrait → NodeId → AutoTrait → NodeId → Prop where
  | refl (a : AutoTrait) (n : NodeId) : AutoReach g a n a n
  | step {a₀ a₁ a₂ : AutoTrait} {n₀ n₁ n₂ : NodeId} :
      AutoConstituentStep g a₀ n₀ a₁ n₁ →
      AutoReach g a₁ n₁ a₂ n₂ →
      AutoReach g a₀ n₀ a₂ n₂

/-- Unoverridden negative auto-trait leaves. -/
inductive IsDirectNegativeAuto (g : TypeGraph) : AutoTrait → NodeId → Prop where
  | rawSend {n p : NodeId} : g.kindOf n = .rawPtr p → IsDirectNegativeAuto g .send n
  | rawSync {n p : NodeId} : g.kindOf n = .rawPtr p → IsDirectNegativeAuto g .sync n
  | rcSend {n p : NodeId} : g.kindOf n = .rcPtr p → IsDirectNegativeAuto g .send n
  | rcSync {n p : NodeId} : g.kindOf n = .rcPtr p → IsDirectNegativeAuto g .sync n
  | cellSync {n inner sz : NodeId} :
      g.kindOf n = .unsafeCell inner sz → IsDirectNegativeAuto g .sync n
  | cellFreeze {n inner sz : NodeId} :
      g.kindOf n = .unsafeCell inner sz → IsDirectNegativeAuto g .freeze n
  | pinnedUnpin {n : NodeId} : g.kindOf n = .phantomPinned → IsDirectNegativeAuto g .unpin n
  | adtNegImpl {n : NodeId} {a : AutoTrait} {fields : List NodeId}
      {hasUnsafe : Bool} {negAuto : AutoTrait → Bool} {immImpl : Bool} :
      g.kindOf n = .adtStruct fields hasUnsafe negAuto immImpl →
      negAuto a = true →
      IsDirectNegativeAuto g a n
  | adtUnsafeField {n : NodeId} {a : AutoTrait} {fields : List NodeId}
      {negAuto : AutoTrait → Bool} {immImpl : Bool} :
      g.kindOf n = .adtStruct fields true negAuto immImpl →
      isUnsafeAuto a = true →
      IsDirectNegativeAuto g a n
  | dynMissing {n : NodeId} {a : AutoTrait} {declared : List AutoTrait} :
      g.kindOf n = .dynObj declared →
      ¬ Mem a declared →
      IsDirectNegativeAuto g a n

theorem coindSat_auto_step {g : TypeGraph} {a a' : AutoTrait} {src dst : NodeId}
    (hStep : AutoConstituentStep g a src a' dst)
    (hSat : CoindSat g (.auto a) src) :
    CoindSat g (.auto a') dst := by
  have hs := coindSat_unfold hSat
  dsimp [StepF] at hs
  cases hStep with
  | refSharedSend hk => rw [hk] at hs; exact hs
  | refSharedSync hk => rw [hk] at hs; exact hs
  | refMutSend hk => rw [hk] at hs; exact hs
  | refMutSync hk => rw [hk] at hs; exact hs
  | boxPtrSend hk => rw [hk] at hs; exact hs
  | boxPtrSync hk => rw [hk] at hs; exact hs
  | unsafeCellSend hk => rw [hk] at hs; exact hs
  | unsafeCellUnpin hk => rw [hk] at hs; exact hs
  | phantomSend hk => rw [hk] at hs; exact hs
  | phantomSync hk => rw [hk] at hs; exact hs
  | phantomUnpin hk => rw [hk] at hs; exact hs
  | adtField hk _ _ hmem =>
    rw [hk] at hs
    exact AllProp_mem hs.2.2 hmem
  | rpitStep hk => rw [hk] at hs; exact hs

theorem direct_negative_auto_not_coindSat {g : TypeGraph} {a : AutoTrait} {n : NodeId}
    (hNeg : IsDirectNegativeAuto g a n) : ¬ CoindSat g (.auto a) n := by
  intro hSat
  have hs := coindSat_unfold hSat
  dsimp [StepF] at hs
  cases hNeg with
  | rawSend hk => rw [hk] at hs; exact hs
  | rawSync hk => rw [hk] at hs; exact hs
  | rcSend hk => rw [hk] at hs; exact hs
  | rcSync hk => rw [hk] at hs; exact hs
  | cellSync hk => rw [hk] at hs; exact hs
  | cellFreeze hk => rw [hk] at hs; exact hs
  | pinnedUnpin hk => rw [hk] at hs; exact hs
  | adtNegImpl hk hTrue =>
    rw [hk] at hs
    dsimp at hs
    rw [hTrue] at hs
    cases hs.1
  | adtUnsafeField hk hUns =>
    rw [hk] at hs
    have hc : true = false := hs.2.1 hUns
    cases hc
  | dynMissing hk hNotMem =>
    rw [hk] at hs
    exact hNotMem hs

/-- **Theorem 1a (Reachable Negative-Leaf Rejection):** For any finite or cyclic `TypeGraph`,
if an unoverridden negative leaf `(a₁, leaf)` is reachable from `(a₀, root)` along constituent
auto-trait edges, then `CoindSat g (.auto a₀) root` is false—regardless of any cycles elsewhere
in the graph (e.g. `BadNode(Option<Box<BadNode>>, *const u8)`). -/
theorem coindSat_rejects_reachable_negative_leaf {g : TypeGraph}
    {a₀ a₁ : AutoTrait} {root leaf : NodeId}
    (hReach : AutoReach g a₀ root a₁ leaf)
    (hNeg : IsDirectNegativeAuto g a₁ leaf) :
    ¬ CoindSat g (.auto a₀) root := by
  intro hSat
  induction hReach with
  | refl => exact direct_negative_auto_not_coindSat hNeg hSat
  | step hStep _ ih =>
    exact ih hNeg (coindSat_auto_step hStep hSat)

/-- Direct constituent dependencies for a `(TraitPred, NodeId)` pair:
returns `none` when immediately refuted by a negative impl / unsafe field / missing impl,
or `some deps` listing all sub-obligations required by `StepF`. -/
noncomputable def directDeps (g : TypeGraph) (tr : TraitPred) (n : NodeId) :
    Option (List (TraitPred × NodeId)) :=
  match tr, g.kindOf n with
  | .auto _, .prim _ => some []
  | .auto .send, .rawPtr _ => none
  | .auto .sync, .rawPtr _ => none
  | .auto .unpin, .rawPtr _ => some []
  | .auto .freeze, .rawPtr _ => some []
  | .auto .send, .refShared p => some [(.auto .sync, p)]
  | .auto .sync, .refShared p => some [(.auto .sync, p)]
  | .auto .unpin, .refShared _ => some []
  | .auto .freeze, .refShared _ => some []
  | .auto .send, .refMut p => some [(.auto .send, p)]
  | .auto .sync, .refMut p => some [(.auto .sync, p)]
  | .auto .unpin, .refMut _ => some []
  | .auto .freeze, .refMut _ => some []
  | .auto .send, .boxPtr p => some [(.auto .send, p)]
  | .auto .sync, .boxPtr p => some [(.auto .sync, p)]
  | .auto .unpin, .boxPtr _ => some []
  | .auto .freeze, .boxPtr _ => some []
  | .auto .send, .rcPtr _ => none
  | .auto .sync, .rcPtr _ => none
  | .auto .unpin, .rcPtr _ => some []
  | .auto .freeze, .rcPtr _ => some []
  | .auto .send, .unsafeCell inner _ => some [(.auto .send, inner)]
  | .auto .sync, .unsafeCell _ _ => none
  | .auto .unpin, .unsafeCell inner _ => some [(.auto .unpin, inner)]
  | .auto .freeze, .unsafeCell _ _ => none
  | .auto .send, .phantomData inner => some [(.auto .send, inner)]
  | .auto .sync, .phantomData inner => some [(.auto .sync, inner)]
  | .auto .unpin, .phantomData inner => some [(.auto .unpin, inner)]
  | .auto .freeze, .phantomData _ => some []
  | .auto .send, .phantomPinned => some []
  | .auto .sync, .phantomPinned => some []
  | .auto .unpin, .phantomPinned => none
  | .auto .freeze, .phantomPinned => some []
  | .auto a, .adtStruct fields hasUnsafe negAuto _ =>
    match negAuto a with
    | true => none
    | false =>
      match isUnsafeAuto a && hasUnsafe with
      | true => none
      | false => some (fields.map (fun f => (.auto a, f)))
  | .auto a, .rpitOpaque hidden => some [(.auto a, hidden)]
  | .auto a, .dynObj declared =>
    match memAutoBool a declared with
    | true => some []
    | false => none
  | .immutable, .prim _ => some []
  | .immutable, .rawPtr _ => some []
  | .immutable, .refShared _ => some []
  | .immutable, .refMut _ => some []
  | .immutable, .boxPtr p =>
    match g.boxSized p with
    | true => some []
    | false => none
  | .immutable, .rcPtr _ => none
  | .immutable, .unsafeCell _ _ => none
  | .immutable, .phantomData _ => some []
  | .immutable, .phantomPinned => some []
  | .immutable, .adtStruct fields _ _ immImpl =>
    match immImpl with
    | true => some (fields.map (fun f => (.immutable, f)))
    | false => none
  | .immutable, .rpitOpaque _ => none
  | .immutable, .dynObj _ => none

theorem AllProp_map_pair {α β : Type} (f : α → β) (P : β → Prop) (xs : List α) :
    AllProp P (xs.map f) ↔ AllProp (fun x => P (f x)) xs := by
  induction xs with
  | nil =>
    constructor
    · intro _; exact AllProp.nil
    · intro _; exact AllProp.nil
  | cons y ys ih =>
    constructor
    · intro h
      cases h with
      | cons hy hys => exact AllProp.cons hy ((ih).mp hys)
    · intro h
      cases h with
      | cons hy hys => exact AllProp.cons hy ((ih).mpr hys)

theorem directDeps_sound_stepF (g : TypeGraph) (S : TraitPred → NodeId → Prop)
    (tr : TraitPred) (n : NodeId) (deps : List (TraitPred × NodeId))
    (hDeps : directDeps g tr n = some deps)
    (hAll : AllProp (fun p => S p.1 p.2) deps) :
    StepF g S tr n := by
  cases tr with
  | auto a =>
    dsimp [directDeps] at hDeps
    dsimp [StepF]
    revert hDeps
    cases g.kindOf n with
    | prim _ => intro _; cases a <;> trivial
    | rawPtr _ =>
      intro hDeps
      cases a with
      | send => cases hDeps
      | sync => cases hDeps
      | unpin => trivial
      | freeze => trivial
    | refShared p =>
      intro hDeps
      cases a with
      | send => cases hDeps; cases hAll with | cons hp _ => exact hp
      | sync => cases hDeps; cases hAll with | cons hp _ => exact hp
      | unpin => trivial
      | freeze => trivial
    | refMut p =>
      intro hDeps
      cases a with
      | send => cases hDeps; cases hAll with | cons hp _ => exact hp
      | sync => cases hDeps; cases hAll with | cons hp _ => exact hp
      | unpin => trivial
      | freeze => trivial
    | boxPtr p =>
      intro hDeps
      cases a with
      | send => cases hDeps; cases hAll with | cons hp _ => exact hp
      | sync => cases hDeps; cases hAll with | cons hp _ => exact hp
      | unpin => trivial
      | freeze => trivial
    | rcPtr _ =>
      intro hDeps
      cases a with
      | send => cases hDeps
      | sync => cases hDeps
      | unpin => trivial
      | freeze => trivial
    | unsafeCell inner _ =>
      intro hDeps
      cases a with
      | send => cases hDeps; cases hAll with | cons hp _ => exact hp
      | sync => cases hDeps
      | unpin => cases hDeps; cases hAll with | cons hp _ => exact hp
      | freeze => cases hDeps
    | phantomData inner =>
      intro hDeps
      cases a with
      | send => cases hDeps; cases hAll with | cons hp _ => exact hp
      | sync => cases hDeps; cases hAll with | cons hp _ => exact hp
      | unpin => cases hDeps; cases hAll with | cons hp _ => exact hp
      | freeze => trivial
    | phantomPinned =>
      intro hDeps
      cases a with
      | send => trivial
      | sync => trivial
      | unpin => cases hDeps
      | freeze => trivial
    | adtStruct fields hasUnsafe negAuto immImpl =>
      intro hDeps
      dsimp at hDeps ⊢
      revert hDeps
      cases negAuto a with
      | true => intro hDeps; cases hDeps
      | false =>
        intro hDeps
        revert hDeps
        cases hUns : (isUnsafeAuto a && hasUnsafe) with
        | true => intro hDeps; cases hDeps
        | false =>
          intro hDeps
          cases hDeps
          refine ⟨rfl, ?_, ?_⟩
          · intro hIsUns
            cases hasUnsafe with
            | false => rfl
            | true =>
              rw [hIsUns] at hUns
              cases hUns
          · exact (AllProp_map_pair (fun f => (.auto a, f)) (fun p => S p.1 p.2) fields).mp hAll
    | rpitOpaque hidden =>
      intro hDeps
      cases hDeps
      cases hAll with | cons hp _ => exact hp
    | dynObj declared =>
      intro hDeps
      dsimp at hDeps ⊢
      revert hDeps
      cases hMem : memAutoBool a declared with
      | false => intro hDeps; cases hDeps
      | true => intro _; exact (memAutoBool_iff a declared).mp hMem
  | immutable =>
    dsimp [directDeps] at hDeps
    dsimp [StepF]
    revert hDeps
    cases g.kindOf n with
    | prim _ => intro _; trivial
    | rawPtr _ => intro _; trivial
    | refShared _ => intro _; trivial
    | refMut _ => intro _; trivial
    | boxPtr p =>
      intro hDeps
      dsimp at hDeps ⊢
      revert hDeps
      cases g.boxSized p with
      | false => intro hDeps; cases hDeps
      | true => intro _; rfl
    | rcPtr _ => intro hDeps; cases hDeps
    | unsafeCell _ _ => intro hDeps; cases hDeps
    | phantomData _ => intro _; trivial
    | phantomPinned => intro _; trivial
    | adtStruct fields hasUnsafe negAuto immImpl =>
      intro hDeps
      revert hDeps
      cases immImpl with
      | false => intro hDeps; cases hDeps
      | true =>
        intro hDeps
        cases hDeps
        refine ⟨rfl, ?_⟩
        exact (AllProp_map_pair (fun f => (.immutable, f)) (fun p => S p.1 p.2) fields).mp hAll
    | rpitOpaque _ => intro hDeps; cases hDeps
    | dynObj _ => intro hDeps; cases hDeps

theorem stepF_implies_directDeps_some (g : TypeGraph) (S : TraitPred → NodeId → Prop)
    (tr : TraitPred) (n : NodeId) (h : StepF g S tr n) :
    ∃ deps, directDeps g tr n = some deps ∧ AllProp (fun p => S p.1 p.2) deps := by
  cases tr with
  | auto a =>
    dsimp [StepF] at h
    dsimp [directDeps]
    revert h
    cases g.kindOf n with
    | prim _ => intro _; refine ⟨[], rfl, AllProp.nil⟩
    | rawPtr _ =>
      intro h
      cases a with
      | send => cases h
      | sync => cases h
      | unpin => exact ⟨[], rfl, AllProp.nil⟩
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | refShared p =>
      intro h
      cases a with
      | send => exact ⟨[(.auto .sync, p)], rfl, AllProp.cons h AllProp.nil⟩
      | sync => exact ⟨[(.auto .sync, p)], rfl, AllProp.cons h AllProp.nil⟩
      | unpin => exact ⟨[], rfl, AllProp.nil⟩
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | refMut p =>
      intro h
      cases a with
      | send => exact ⟨[(.auto .send, p)], rfl, AllProp.cons h AllProp.nil⟩
      | sync => exact ⟨[(.auto .sync, p)], rfl, AllProp.cons h AllProp.nil⟩
      | unpin => exact ⟨[], rfl, AllProp.nil⟩
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | boxPtr p =>
      intro h
      cases a with
      | send => exact ⟨[(.auto .send, p)], rfl, AllProp.cons h AllProp.nil⟩
      | sync => exact ⟨[(.auto .sync, p)], rfl, AllProp.cons h AllProp.nil⟩
      | unpin => exact ⟨[], rfl, AllProp.nil⟩
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | rcPtr _ =>
      intro h
      cases a with
      | send => cases h
      | sync => cases h
      | unpin => exact ⟨[], rfl, AllProp.nil⟩
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | unsafeCell inner _ =>
      intro h
      cases a with
      | send => exact ⟨[(.auto .send, inner)], rfl, AllProp.cons h AllProp.nil⟩
      | sync => cases h
      | unpin => exact ⟨[(.auto .unpin, inner)], rfl, AllProp.cons h AllProp.nil⟩
      | freeze => cases h
    | phantomData inner =>
      intro h
      cases a with
      | send => exact ⟨[(.auto .send, inner)], rfl, AllProp.cons h AllProp.nil⟩
      | sync => exact ⟨[(.auto .sync, inner)], rfl, AllProp.cons h AllProp.nil⟩
      | unpin => exact ⟨[(.auto .unpin, inner)], rfl, AllProp.cons h AllProp.nil⟩
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | phantomPinned =>
      intro h
      cases a with
      | send => exact ⟨[], rfl, AllProp.nil⟩
      | sync => exact ⟨[], rfl, AllProp.nil⟩
      | unpin => cases h
      | freeze => exact ⟨[], rfl, AllProp.nil⟩
    | adtStruct fields hasUnsafe negAuto immImpl =>
      intro h
      dsimp at h ⊢
      rcases h with ⟨hNeg, hUns, hAll⟩
      rw [hNeg]
      have hFlag : (isUnsafeAuto a && hasUnsafe) = false := by
        cases hU : isUnsafeAuto a
        · rfl
        · rw [hUns hU]; rfl
      rw [hFlag]
      refine ⟨fields.map (fun f => (.auto a, f)), rfl, ?_⟩
      exact (AllProp_map_pair (fun f => (.auto a, f)) (fun p => S p.1 p.2) fields).mpr hAll
    | rpitOpaque hidden =>
      intro h
      exact ⟨[(.auto a, hidden)], rfl, AllProp.cons h AllProp.nil⟩
    | dynObj declared =>
      intro h
      dsimp at h ⊢
      have hB : memAutoBool a declared = true := (memAutoBool_iff a declared).mpr h
      rw [hB]
      exact ⟨[], rfl, AllProp.nil⟩
  | immutable =>
    dsimp [StepF] at h
    dsimp [directDeps]
    revert h
    cases g.kindOf n with
    | prim _ => intro _; exact ⟨[], rfl, AllProp.nil⟩
    | rawPtr _ => intro _; exact ⟨[], rfl, AllProp.nil⟩
    | refShared _ => intro _; exact ⟨[], rfl, AllProp.nil⟩
    | refMut _ => intro _; exact ⟨[], rfl, AllProp.nil⟩
    | boxPtr p =>
      intro h
      dsimp at h ⊢
      rw [h]
      exact ⟨[], rfl, AllProp.nil⟩
    | rcPtr _ => intro h; cases h
    | unsafeCell _ _ => intro h; cases h
    | phantomData _ => intro _; exact ⟨[], rfl, AllProp.nil⟩
    | phantomPinned => intro _; exact ⟨[], rfl, AllProp.nil⟩
    | adtStruct fields hasUnsafe negAuto immImpl =>
      intro h
      dsimp at h ⊢
      rcases h with ⟨hImm, hAll⟩
      rw [hImm]
      refine ⟨fields.map (fun f => (.immutable, f)), rfl, ?_⟩
      exact (AllProp_map_pair (fun f => (.immutable, f)) (fun p => S p.1 p.2) fields).mpr hAll
    | rpitOpaque _ => intro h; cases h
    | dynObj _ => intro h; cases h

/-- Fuel-bounded visited-stack DFS solver modeling `rustc_trait_selection`'s
`evaluate_stack` + `coinductive_match`:
- If `(tr, n)` is already on `visited`, returns `isCoinductivePred tr` (`true` for auto traits,
  `false` for inductive traits such as `Immutable`).
- Otherwise unfolds `directDeps g tr n` and checks all sub-obligations with `(tr, n) :: visited`. -/
noncomputable def checkWithStack (g : TypeGraph) :
    Nat → List (TraitPred × NodeId) → TraitPred → NodeId → Bool
  | 0, visited, tr, n =>
    match memPairBool (tr, n) visited with
    | true => isCoinductivePred tr
    | false => false
  | fuel' + 1, visited, tr, n =>
    match memPairBool (tr, n) visited with
    | true => isCoinductivePred tr
    | false =>
      match directDeps g tr n with
      | none => false
      | some deps => allBool (fun p => checkWithStack g fuel' ((tr, n) :: visited) p.1 p.2) deps

theorem allBool_congr {α : Type} {f h : α → Bool} (xs : List α)
    (hc : ∀ x, f x = h x) : allBool f xs = allBool h xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp [allBool]
    rw [hc x, ih]

/-- List-structural traversal helper for witness collection, keeping outer `Nat`
structural recursion strictly independent of inner `List` recursion. -/
noncomputable def checkListWithStep
    (stepOne : List (TraitPred × NodeId) → TraitPred → NodeId → Option (List (TraitPred × NodeId)))
    (visited : List (TraitPred × NodeId)) :
    List (TraitPred × NodeId) → Option (List (TraitPred × NodeId))
  | [] => some []
  | p :: ps =>
    match memPairBool p visited with
    | true =>
      match isCoinductivePred p.1 with
      | true => checkListWithStep stepOne visited ps
      | false => none
    | false =>
      match stepOne visited p.1 p.2 with
      | none => none
      | some acc1 =>
        match checkListWithStep stepOne visited ps with
        | none => none
        | some acc2 => some (p :: (acc1 ++ acc2))

/-- Proof-witness-accumulating twin of `checkWithStack` returning the closed
post-fixed vertex list verified across all DFS branches. -/
noncomputable def checkAndCollectList (g : TypeGraph) :
    Nat → List (TraitPred × NodeId) → List (TraitPred × NodeId) → Option (List (TraitPred × NodeId))
  | 0, visited, ps => checkListWithStep (fun _ _ _ => none) visited ps
  | fuel' + 1, visited, ps =>
    checkListWithStep
      (fun vis tr n =>
        match directDeps g tr n with
        | none => none
        | some deps => checkAndCollectList g fuel' ((tr, n) :: vis) deps)
      visited ps

/-- Single-goal wrapper around `checkAndCollectList`. -/
noncomputable def checkAndCollect (g : TypeGraph) (fuel : Nat)
    (visited : List (TraitPred × NodeId)) (tr : TraitPred) (n : NodeId) :
    Option (List (TraitPred × NodeId)) :=
  checkAndCollectList g fuel visited [(tr, n)]

theorem checkListWithStep_isSome_eq
    (stepOne : List (TraitPred × NodeId) → TraitPred → NodeId → Option (List (TraitPred × NodeId)))
    (stepBoolFn : TraitPred → NodeId → Bool)
    (visited : List (TraitPred × NodeId))
    (hStep : ∀ tr n, (stepOne visited tr n).isSome = stepBoolFn tr n) :
    ∀ ps,
      (checkListWithStep stepOne visited ps).isSome =
      allBool (fun p =>
        match memPairBool p visited with
        | true => isCoinductivePred p.1
        | false => stepBoolFn p.1 p.2) ps := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    dsimp [checkListWithStep, allBool]
    cases memPairBool p visited with
    | false =>
      cases h1 : stepOne visited p.1 p.2 with
      | none =>
        have hs := hStep p.1 p.2
        rw [h1] at hs
        rw [← hs]
        rfl
      | some _ =>
        have hs := hStep p.1 p.2
        rw [h1] at hs
        have hTrue : stepBoolFn p.1 p.2 = true := by rw [← hs]; rfl
        rw [hTrue, Bool.true_and]
        revert ih
        cases checkListWithStep stepOne visited ps with
        | none => intro ih; exact ih
        | some _ => intro ih; exact ih
    | true =>
      cases isCoinductivePred p.1 with
      | false => rfl
      | true => exact ih

theorem checkAndCollectList_isSome_eq (g : TypeGraph) (fuel : Nat) :
    ∀ visited ps,
      (checkAndCollectList g fuel visited ps).isSome =
      allBool (fun p => checkWithStack g fuel visited p.1 p.2) ps := by
  induction fuel with
  | zero =>
    intro visited ps
    dsimp [checkAndCollectList]
    rw [checkListWithStep_isSome_eq (fun _ _ _ => none) (fun _ _ => false) visited
      (fun _ _ => rfl) ps]
    exact allBool_congr ps (fun _ => rfl)
  | succ f ih =>
    intro visited ps
    dsimp [checkAndCollectList]
    let stepOneFn : List (TraitPred × NodeId) → TraitPred → NodeId → Option (List (TraitPred × NodeId)) :=
      fun vis tr n =>
        match directDeps g tr n with
        | none => none
        | some deps => checkAndCollectList g f ((tr, n) :: vis) deps
    let stepBoolFn : TraitPred → NodeId → Bool :=
      fun tr n =>
        match directDeps g tr n with
        | none => false
        | some deps => allBool (fun p => checkWithStack g f ((tr, n) :: visited) p.1 p.2) deps
    have hStep : ∀ tr n, (stepOneFn visited tr n).isSome = stepBoolFn tr n := by
      intro tr n
      dsimp [stepOneFn, stepBoolFn]
      cases directDeps g tr n with
      | none => rfl
      | some deps => exact ih ((tr, n) :: visited) deps
    rw [checkListWithStep_isSome_eq stepOneFn stepBoolFn visited hStep ps]
    exact allBool_congr ps (fun _ => rfl)

theorem checkAndCollect_isSome_eq (g : TypeGraph) (fuel : Nat)
    (visited : List (TraitPred × NodeId)) (tr : TraitPred) (n : NodeId) :
    (checkAndCollect g fuel visited tr n).isSome = checkWithStack g fuel visited tr n := by
  have h := checkAndCollectList_isSome_eq g fuel visited [(tr, n)]
  dsimp [checkAndCollect]
  rw [h]
  dsimp [allBool]
  cases checkWithStack g fuel visited tr n <;> rfl

theorem checkListWithStep_sound_inv (g : TypeGraph)
    (stepOne : List (TraitPred × NodeId) → TraitPred → NodeId → Option (List (TraitPred × NodeId)))
    (visited : List (TraitPred × NodeId))
    (hStep : ∀ p acc1, stepOne visited p.1 p.2 = some acc1 →
      StepF g (fun t m => Mem (t, m) (visited ++ p :: acc1)) p.1 p.2 ∧
      ∀ q, Mem q acc1 → StepF g (fun t m => Mem (t, m) (visited ++ p :: acc1)) q.1 q.2) :
    ∀ ps acc,
      checkListWithStep stepOne visited ps = some acc →
      (∀ p, Mem p ps → Mem p (visited ++ acc)) ∧
      (∀ q, Mem q acc → StepF g (fun t m => Mem (t, m) (visited ++ acc)) q.1 q.2) := by
  intro ps
  induction ps with
  | nil =>
    intro acc hRes
    dsimp [checkListWithStep] at hRes
    cases hRes
    constructor
    · intro p hp; cases hp
    · intro q hq; cases hq
  | cons p ps ihPs =>
    intro acc hRes
    dsimp [checkListWithStep] at hRes
    revert hRes
    cases hm : memPairBool p visited with
    | false =>
      intro hRes
      revert hRes
      cases h1 : stepOne visited p.1 p.2 with
      | none => intro hRes; cases hRes
      | some acc1 =>
        intro hRes
        revert hRes
        cases h2 : checkListWithStep stepOne visited ps with
        | none => intro hRes; cases hRes
        | some acc2 =>
          intro hRes
          cases hRes
          have ⟨hRoot, hSub1⟩ := hStep p acc1 h1
          have hSub2 := ihPs acc2 h2
          have hLift1 : ∀ x, Mem x (visited ++ p :: acc1) →
              Mem x (visited ++ p :: (acc1 ++ acc2)) := by
            intro x hx
            cases Mem_split_append hx with
            | inl hv => exact Mem_append_left hv
            | inr hp1 =>
              cases hp1 with
              | head => exact Mem_append_right visited Mem.head
              | tail ha1 => exact Mem_append_right visited (Mem.tail (Mem_append_left ha1))
          have hLift2 : ∀ x, Mem x (visited ++ acc2) →
              Mem x (visited ++ p :: (acc1 ++ acc2)) := by
            intro x hx
            cases Mem_split_append hx with
            | inl hv => exact Mem_append_left hv
            | inr ha2 => exact Mem_append_right visited (Mem.tail (Mem_append_right acc1 ha2))
          constructor
          · intro x hx
            cases hx with
            | head => exact Mem_append_right visited Mem.head
            | tail hxt => exact hLift2 x (hSub2.1 x hxt)
          · intro q hq
            cases hq with
            | head =>
              exact StepF_mono g (fun t m hm' => hLift1 (t, m) hm') p.1 p.2 hRoot
            | tail hqt =>
              cases Mem_split_append hqt with
              | inl hq1 =>
                exact StepF_mono g (fun t m hm' => hLift1 (t, m) hm') q.1 q.2 (hSub1 q hq1)
              | inr hq2 =>
                exact StepF_mono g (fun t m hm' => hLift2 (t, m) hm') q.1 q.2 (hSub2.2 q hq2)
    | true =>
      intro hRes
      revert hRes
      cases isCoinductivePred p.1 with
      | false => intro hRes; cases hRes
      | true =>
        intro hRes
        have hSub := ihPs acc hRes
        constructor
        · intro x hx
          cases hx with
          | head => exact Mem_append_left ((memPairBool_iff p visited).mp hm)
          | tail hxt => exact hSub.1 x hxt
        · exact hSub.2

/-- Core DFS coinductive invariant: if `checkAndCollectList g fuel visited ps = some acc`,
then:
1. every goal in `ps` either already lies in `visited` (as a coinductive goal!) or lies in `acc`, AND
2. every vertex in `acc` satisfies `StepF g (in (visited ++ acc))`. -/
theorem checkAndCollectList_sound_inv (g : TypeGraph) (fuel : Nat) :
    ∀ visited ps acc,
      checkAndCollectList g fuel visited ps = some acc →
      (∀ p, Mem p ps → Mem p (visited ++ acc)) ∧
      (∀ q, Mem q acc → StepF g (fun t m => Mem (t, m) (visited ++ acc)) q.1 q.2) := by
  induction fuel with
  | zero =>
    intro visited ps acc hRes
    dsimp [checkAndCollectList] at hRes
    apply checkListWithStep_sound_inv g (fun _ _ _ => none) visited _ ps acc hRes
    intro p acc1 hNone
    cases hNone
  | succ f ih =>
    intro visited ps acc hRes
    dsimp [checkAndCollectList] at hRes
    let stepOneFn : List (TraitPred × NodeId) → TraitPred → NodeId → Option (List (TraitPred × NodeId)) :=
      fun vis tr n =>
        match directDeps g tr n with
        | none => none
        | some deps => checkAndCollectList g f ((tr, n) :: vis) deps
    apply checkListWithStep_sound_inv g stepOneFn visited _ ps acc hRes
    intro p acc1 hSome
    dsimp [stepOneFn] at hSome
    cases hd : directDeps g p.1 p.2 with
    | none => rw [hd] at hSome; cases hSome
    | some deps =>
      rw [hd] at hSome
      dsimp at hSome
      have hSub := ih (p :: visited) deps acc1 hSome
      have hLift : ∀ x, Mem x ((p :: visited) ++ acc1) → Mem x (visited ++ p :: acc1) := by
        intro x hx
        cases Mem_split_append hx with
        | inl hpv =>
          cases hpv with
          | head => exact Mem_append_right visited Mem.head
          | tail hv => exact Mem_append_left hv
        | inr ha1 => exact Mem_append_right visited (Mem.tail ha1)
      constructor
      · apply directDeps_sound_stepF g _ p.1 p.2 deps hd
        exact AllProp_of_forall (fun d hdMem => hLift d (hSub.1 d hdMem))
      · intro q hq
        exact StepF_mono g (fun t m hm' => hLift (t, m) hm') q.1 q.2 (hSub.2 q hq)

/-- **Theorem 1b (Soundness of `rustc`-Style Coinductive DFS Solver):**
Whenever `checkWithStack g fuel [] tr n = true`, `CoindSat g tr n` holds in the Tarski
greatest fixpoint (with zero classical axioms). -/
theorem checkWithStack_sound {g : TypeGraph} {fuel : Nat} {tr : TraitPred} {n : NodeId}
    (h : checkWithStack g fuel [] tr n = true) : CoindSat g tr n := by
  have hIsSome : (checkAndCollect g fuel [] tr n).isSome = true := by
    rw [checkAndCollect_isSome_eq]
    exact h
  cases hOpt : checkAndCollect g fuel [] tr n with
  | none => rw [hOpt] at hIsSome; cases hIsSome
  | some acc =>
    have hInv := checkAndCollectList_sound_inv g fuel [] [(tr, n)] acc hOpt
    let P : TraitPred → NodeId → Prop := fun t m => Mem (t, m) acc
    have hPost : IsPostFixed g P := fun t m hm => hInv.2 (t, m) hm
    have hMem : P tr n := hInv.1 (tr, n) Mem.head
    exact CoindSat.intro P hPost hMem

/-- Fuel-explicit convenience wrapper around `checkWithStack_sound` for concrete `rfl` witnesses. -/
theorem checkWithStack_sound_fuel (fuel : Nat) {g : TypeGraph} {tr : TraitPred} {n : NodeId}
    (h : checkWithStack g fuel [] tr n = true) : CoindSat g tr n :=
  checkWithStack_sound h

/-- **Theorem 1c (Inductive Cycle Rejection):** Any visited cycle whose head is non-coinductive
(`isCoinductivePred tr = false`, i.e., `tr = .immutable`) immediately fails `checkWithStack`. -/
theorem checkWithStack_inductive_cycle_fails (g : TypeGraph) (fuel : Nat)
    (visited : List (TraitPred × NodeId)) (n : NodeId)
    (hMem : Mem (.immutable, n) visited) :
    checkWithStack g fuel visited .immutable n = false := by
  have hB : memPairBool (.immutable, n) visited = true := (memPairBool_iff _ _).mpr hMem
  cases fuel with
  | zero =>
    dsimp [checkWithStack]
    rw [hB]
    rfl
  | succ f =>
    dsimp [checkWithStack]
    rw [hB]
    rfl

/-- Finite-graph boolean step operator for Kleene GFP iteration. -/
noncomputable def stepBool (g : TypeGraph) (cur : TraitPred → NodeId → Bool)
    (tr : TraitPred) (n : NodeId) : Bool :=
  match directDeps g tr n with
  | none => false
  | some deps => allBool (fun p => cur p.1 p.2) deps

theorem stepBool_eq_true_iff (g : TypeGraph) (cur : TraitPred → NodeId → Bool)
    (tr : TraitPred) (n : NodeId) :
    stepBool g cur tr n = true ↔ StepF g (fun t m => cur t m = true) tr n := by
  constructor
  · intro h
    dsimp [stepBool] at h
    cases hd : directDeps g tr n with
    | none => rw [hd] at h; cases h
    | some deps =>
      rw [hd] at h
      exact directDeps_sound_stepF g _ tr n deps hd ((allBool_iff _ deps).mp h)
  · intro h
    obtain ⟨deps, hd, hAll⟩ := stepF_implies_directDeps_some g _ tr n h
    dsimp [stepBool]
    rw [hd]
    exact (allBool_iff _ deps).mpr hAll

/-- Kleene greatest-fixpoint iterator starting from `⊤ := fun _ _ => true`. -/
noncomputable def kleeneGfp (g : TypeGraph) : Nat → TraitPred → NodeId → Bool
  | 0, _, _ => true
  | k + 1, tr, n => stepBool g (kleeneGfp g k) tr n

/-- Completeness of every Kleene iterate: every coinductively valid node stays `true`
at every iteration `k`. -/
theorem coindSat_implies_kleeneGfp (g : TypeGraph) :
    ∀ k tr n, CoindSat g tr n → kleeneGfp g k tr n = true := by
  intro k
  induction k with
  | zero => intro _ _ _; rfl
  | succ k ih =>
    intro tr n hSat
    dsimp [kleeneGfp]
    rw [stepBool_eq_true_iff]
    exact StepF_mono g (fun t m hm => ih t m hm) tr n (coindSat_unfold hSat)

/-- Closedness of a finite `TypeGraph`: every constituent dependency of an in-bounds node
stays strictly below `g.bound`. -/
abbrev ClosedGraph (g : TypeGraph) : Prop :=
  ∀ tr n deps p, n < g.bound → directDeps g tr n = some deps → Mem p deps → p.2 < g.bound

/-- Boolean equivalence helper without relying on `Init` `Bool` extensions. -/
noncomputable def boolEqv : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Decidable fixpoint convergence test across all 5 `TraitPred`s and all `n < g.bound`. -/
noncomputable def graphFixpointEq (g : TypeGraph) (cur : TraitPred → NodeId → Bool) : Bool :=
  allBelowBool (fun n =>
    boolEqv (cur (.auto .send) n) (stepBool g cur (.auto .send) n) &&
    boolEqv (cur (.auto .sync) n) (stepBool g cur (.auto .sync) n) &&
    boolEqv (cur (.auto .unpin) n) (stepBool g cur (.auto .unpin) n) &&
    boolEqv (cur (.auto .freeze) n) (stepBool g cur (.auto .freeze) n) &&
    boolEqv (cur .immutable n) (stepBool g cur .immutable n)
  ) g.bound

theorem bool_eqv_true_eq {a b : Bool} (h : boolEqv a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem graphFixpointEq_sound (g : TypeGraph) (cur : TraitPred → NodeId → Bool)
    (hFix : graphFixpointEq g cur = true) :
    ∀ tr n, n < g.bound → cur tr n = stepBool g cur tr n := by
  intro tr n hn
  have hAll := (allBelowBool_iff _ g.bound).mp hFix n hn
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hAll
  rcases hAll with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  cases tr with
  | auto a =>
    cases a with
    | send => exact bool_eqv_true_eq h1
    | sync => exact bool_eqv_true_eq h2
    | unpin => exact bool_eqv_true_eq h3
    | freeze => exact bool_eqv_true_eq h4
  | immutable => exact bool_eqv_true_eq h5

/-- **Kleene Finite-Graph Fixpoint Soundness & Completeness (`kleeneGfp_iff_coindSat`):**
On any closed finite graph where `kleeneGfp g k` has converged, `kleeneGfp g k tr n = true`
holds if and only if `CoindSat g tr n` holds. -/
theorem kleeneGfp_fixpoint_implies_coindSat {g : TypeGraph} (hClosed : ClosedGraph g)
    {k : Nat} (hFix : graphFixpointEq g (kleeneGfp g k) = true)
    {tr : TraitPred} {n : NodeId} (hn : n < g.bound)
    (hk : kleeneGfp g k tr n = true) : CoindSat g tr n := by
  let P : TraitPred → NodeId → Prop := fun t m => m < g.bound ∧ kleeneGfp g k t m = true
  have hPost : IsPostFixed g P := by
    intro t m ⟨hmBound, hmTrue⟩
    have hEq : kleeneGfp g k t m = stepBool g (kleeneGfp g k) t m :=
      graphFixpointEq_sound g (kleeneGfp g k) hFix t m hmBound
    have hStepB : stepBool g (kleeneGfp g k) t m = true := hEq.symm.trans hmTrue
    dsimp [stepBool] at hStepB
    revert hStepB
    cases hd : directDeps g t m with
    | none => intro hStepB; cases hStepB
    | some deps =>
      intro hStepB
      have hAllDeps := (allBool_iff _ deps).mp hStepB
      apply directDeps_sound_stepF g P t m deps hd
      apply AllProp_of_forall
      intro p hpMem
      exact ⟨hClosed t m deps p hmBound hd hpMem, AllProp_mem hAllDeps hpMem⟩
  exact CoindSat.intro P hPost ⟨hn, hk⟩

theorem kleeneGfp_iff_coindSat {g : TypeGraph} (hClosed : ClosedGraph g)
    {k : Nat} (hFix : graphFixpointEq g (kleeneGfp g k) = true)
    {tr : TraitPred} {n : NodeId} (hn : n < g.bound) :
    kleeneGfp g k tr n = true ↔ CoindSat g tr n :=
  ⟨kleeneGfp_fixpoint_implies_coindSat hClosed hFix hn, coindSat_implies_kleeneGfp g k tr n⟩

/-!
## Part 4: Concrete Coinductive Cycle Graphs & Four-Way `PhantomData<UnsafeCell<u32>>` Separation
-/

noncomputable def noNeg (_ : AutoTrait) : Bool := false

/-- Node IDs for the recursive coinductive ADT test graph `nodeGraph`:
- `0`: `u32` (`prim 4`)
- `1`: `Box<Node>` (`boxPtr 2`)
- `2`: `Node { val: u32, next: Box<Node> }` (models `Node(Option<Box<Node>>)` cyclic field)
- `3`: `Box<CycleB>` (`boxPtr 5`)
- `4`: `CycleA(Box<CycleB>)` (`adtStruct [3]`)
- `5`: `CycleB(Box<CycleA>)` (`adtStruct [13]`)
- `6`: `*const u8` (`rawPtr 0`)
- `7`: `BadNode { next: Box<BadNode>, raw: *const u8 }` (cycle + unoverridden negative leaf)
- `8`: `Box<BadNode>` (`boxPtr 7`)
- `9`: `UnsafeCell<u32>` (`unsafeCell 0 4`)
- `10`: `CellNode { cell: UnsafeCell<u32>, next: Box<CellNode> }`
- `11`: `Box<CellNode>` (`boxPtr 10`)
- `12`: `LoopImmStruct(LoopImmStruct)` (direct non-`Box` self-cycle to test inductive `Immutable` rejection)
- `13`: `Box<CycleA>` (`boxPtr 4`)
-/
noncomputable def nodeGraph : TypeGraph where
  bound := 13
  boxSized := fun _ => true
  kindOf := fun n =>
    match n with
    | 0 => .prim 4
    | 1 => .boxPtr 2
    | 2 => .adtStruct [0, 1] false noNeg true
    | 3 => .boxPtr 5
    | 4 => .adtStruct [3] false noNeg true
    | 5 => .adtStruct [13] false noNeg true
    | 6 => .rawPtr 0
    | 7 => .adtStruct [8, 6] false noNeg true
    | 8 => .boxPtr 7
    | 9 => .unsafeCell 0 4
    | 10 => .adtStruct [9, 11] false noNeg false
    | 11 => .boxPtr 10
    | 12 => .adtStruct [12] false noNeg true
    | 13 => .boxPtr 4
    | _ => .prim 0

/-- Corrected bound for `nodeGraph` including vertex `13` (`Box<CycleA>`). -/
noncomputable def cycleGraph : TypeGraph where
  bound := 14
  boxSized := fun _ => true
  kindOf := nodeGraph.kindOf

/-- **Coinductive Cycle Acceptance (`Node`):** `Node(Option<Box<Node>>)` satisfies all four
auto traits (`Send`, `Sync`, `Unpin`, `Freeze`) plus `zerocopy::Immutable`, verified both
by executable DFS (`checkWithStack`) and kernel `CoindSat`. -/
theorem node_cycle_check_all_auto_true :
    checkWithStack cycleGraph 16 [] (.auto .send) 2 = true ∧
    checkWithStack cycleGraph 16 [] (.auto .sync) 2 = true ∧
    checkWithStack cycleGraph 16 [] (.auto .unpin) 2 = true ∧
    checkWithStack cycleGraph 16 [] (.auto .freeze) 2 = true ∧
    checkWithStack cycleGraph 16 [] .immutable 2 = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem node_cycle_coindSat_all :
    CoindSat cycleGraph (.auto .send) 2 ∧
    CoindSat cycleGraph (.auto .sync) 2 ∧
    CoindSat cycleGraph (.auto .unpin) 2 ∧
    CoindSat cycleGraph (.auto .freeze) 2 ∧
    CoindSat cycleGraph .immutable 2 := by
  have h := node_cycle_check_all_auto_true
  exact ⟨
    checkWithStack_sound h.1,
    checkWithStack_sound h.2.1,
    checkWithStack_sound h.2.2.1,
    checkWithStack_sound h.2.2.2.1,
    checkWithStack_sound h.2.2.2.2
  ⟩

/-- Mutual coinductive cycle `CycleA <-> Box<CycleB> -> CycleB -> Box<CycleA>` also succeeds
for `Send`, `Sync`, `Unpin`, `Freeze`, and `Immutable`. -/
theorem mutual_cycle_coindSat_send_sync :
    CoindSat cycleGraph (.auto .send) 4 ∧
    CoindSat cycleGraph (.auto .sync) 4 ∧
    CoindSat cycleGraph (.auto .freeze) 4 := by
  refine ⟨checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl⟩

/-- `BadNode` combines a valid `Box<BadNode>` cycle with a sibling `*const u8` field:
coinduction does NOT accept unsound cycles when an unoverridden negative leaf is reachable. -/
theorem bad_node_cycle_rejects_send_and_sync :
    ¬ CoindSat cycleGraph (.auto .send) 7 ∧
    ¬ CoindSat cycleGraph (.auto .sync) 7 ∧
    checkWithStack cycleGraph 16 [] (.auto .send) 7 = false ∧
    checkWithStack cycleGraph 16 [] (.auto .sync) 7 = false := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.adtField rfl rfl (fun _ => rfl) (Mem.tail Mem.head))
        (AutoReach.refl .send 6))
      (IsDirectNegativeAuto.rawSend rfl)
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.adtField rfl rfl (fun _ => rfl) (Mem.tail Mem.head))
        (AutoReach.refl .sync 6))
      (IsDirectNegativeAuto.rawSync rfl)

/-- `CellNode` holds `UnsafeCell<u32>` alongside a recursive `Box<CellNode>` cycle:
it is `Send` (via coinductive cycle + `UnsafeCell<u32>: Send`) yet neither `Sync` nor `Freeze`. -/
theorem cell_node_send_yet_not_sync_not_freeze :
    CoindSat cycleGraph (.auto .send) 10 ∧
    ¬ CoindSat cycleGraph (.auto .sync) 10 ∧
    ¬ CoindSat cycleGraph (.auto .freeze) 10 := by
  refine ⟨checkWithStack_sound_fuel 16 rfl, ?_, ?_⟩
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.adtField rfl rfl (fun _ => rfl) Mem.head)
        (AutoReach.refl .sync 9))
      (IsDirectNegativeAuto.cellSync rfl)
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.adtField rfl rfl (fun _ => rfl) Mem.head)
        (AutoReach.refl .freeze 9))
      (IsDirectNegativeAuto.cellFreeze rfl)

/-- Direct self-referential struct `LoopImmStruct` (`12`) is accepted by coinduction for
`Send` (`AutoTrait`), yet rejected by `checkWithStack` for non-coinductive `Immutable`. -/
theorem loop_imm_rejected_by_dfs_stack :
    checkWithStack cycleGraph 16 [] .immutable 12 = false := rfl

/-- Asymmetric separation graph covering all key Rust/zerocopy type constructors:
- `0`: `u32` (`prim 4`)
- `1`: `*const u8` (`rawPtr 0`)
- `2`: `UnsafeCell<u32>` (`unsafeCell 0 4`)
- `3`: `PhantomData<UnsafeCell<u32>>` (`phantomData 2`)
- `4`: `PhantomData<*const u8>` (`phantomData 1`)
- `5`: `Rc<u32>` (`rcPtr 0`)
- `6`: `Box<UnsafeCell<u32>>` (`boxPtr 2`, `boxSized 2 = true`)
- `7`: `[UnsafeCell<u32>]` (unsized slice modeled as `unsafeCell 0 4`)
- `8`: `Box<[UnsafeCell<u32>]>` (`boxPtr 7`, `boxSized 7 = false`)
- `9`: `HasPhantomCell { val: u32, _marker: PhantomData<UnsafeCell<u32>> }` (`adtStruct [0, 3] false noNeg true`)
- `10`: `PhantomPinned` (`phantomPinned`)
- `11`: `WithUnsafeField { unsafe x: u32 }` (`adtStruct [0] true noNeg false`)
- `12`: `NegSendStruct(u32)` (`impl !Send for NegSendStruct`, `immImpl = true`)
- `13`: `&UnsafeCell<u32>` (`refShared 2`)
- `14`: `&PhantomData<UnsafeCell<u32>>` (`refShared 3`)
- `15`: `ZeroUnsafeCell(())` (`unsafeCell 16 0`)
- `16`: `()` (`prim 0`)
- `17`: `ManuallyDrop<UnsafeCell<u32>>` (`adtStruct [2] false noNeg false`)
-/
noncomputable def asymmetryGraph : TypeGraph where
  bound := 18
  boxSized := fun n =>
    match n with
    | 7 => false
    | _ => true
  kindOf := fun n =>
    match n with
    | 0 => .prim 4
    | 1 => .rawPtr 0
    | 2 => .unsafeCell 0 4
    | 3 => .phantomData 2
    | 4 => .phantomData 1
    | 5 => .rcPtr 0
    | 6 => .boxPtr 2
    | 7 => .unsafeCell 0 4
    | 8 => .boxPtr 7
    | 9 => .adtStruct [0, 3] false noNeg true
    | 10 => .phantomPinned
    | 11 => .adtStruct [0] true noNeg false
    | 12 => .adtStruct [0] false (fun a => match a with | .send => true | _ => false) true
    | 13 => .refShared 2
    | 14 => .refShared 3
    | 15 => .unsafeCell 16 0
    | 16 => .prim 0
    | 17 => .adtStruct [2] false noNeg false
    | _ => .prim 0

/-- **Theorem 2a (Four-Way `PhantomData<UnsafeCell<u32>>` Separation Theorem):**
Bare `PhantomData<UnsafeCell<u32>>` (node `3`) satisfies `Send`, `Freeze`, and
`zerocopy::Immutable`, yet violates `Sync`! -/
theorem phantom_unsafecell_four_way_separation :
    CoindSat asymmetryGraph (.auto .send) 3 ∧
    CoindSat asymmetryGraph (.auto .freeze) 3 ∧
    CoindSat asymmetryGraph .immutable 3 ∧
    ¬ CoindSat asymmetryGraph (.auto .sync) 3 := by
  refine ⟨checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, ?_⟩
  exact coindSat_rejects_reachable_negative_leaf
    (AutoReach.step (AutoConstituentStep.phantomSync rfl) (AutoReach.refl .sync 2))
    (IsDirectNegativeAuto.cellSync rfl)

/-- **Theorem 2b (Four-Way `HasPhantomCell` Struct Separation Theorem):**
A derived struct `HasPhantomCell { val: u32, _marker: PhantomData<UnsafeCell<u32>> }` (node `9`)
inherits `Send`, `Freeze`, and `zerocopy::Immutable` yet fails `Sync`. -/
theorem has_phantom_cell_four_way_separation :
    CoindSat asymmetryGraph (.auto .send) 9 ∧
    CoindSat asymmetryGraph (.auto .freeze) 9 ∧
    CoindSat asymmetryGraph .immutable 9 ∧
    ¬ CoindSat asymmetryGraph (.auto .sync) 9 := by
  refine ⟨checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, ?_⟩
  exact coindSat_rejects_reachable_negative_leaf
    (AutoReach.step (AutoConstituentStep.adtField rfl rfl (fun _ => rfl) (Mem.tail Mem.head))
      (AutoReach.step (AutoConstituentStep.phantomSync rfl) (AutoReach.refl .sync 2)))
    (IsDirectNegativeAuto.cellSync rfl)

/-- `UnsafeCell<u32>` itself (`2`) separates sharply from `PhantomData<UnsafeCell<u32>>`:
`Send` holds, while `Sync`, `Freeze`, and `zerocopy::Immutable` all fail. -/
theorem unsafecell_matrix_row :
    CoindSat asymmetryGraph (.auto .send) 2 ∧
    ¬ CoindSat asymmetryGraph (.auto .sync) 2 ∧
    ¬ CoindSat asymmetryGraph (.auto .freeze) 2 ∧
    ¬ CoindSat asymmetryGraph .immutable 2 := by
  refine ⟨checkWithStack_sound_fuel 16 rfl, ?_, ?_, ?_⟩
  · exact coindSat_unsafeCell_not_sync rfl
  · exact coindSat_unsafeCell_not_freeze rfl
  · exact coindSat_unsafeCell_not_immutable rfl

/-- `*const u8` (`1`) and `PhantomData<*const u8>` (`4`) are `Freeze` + `Immutable` yet `!Send` + `!Sync`. -/
theorem raw_ptr_and_phantom_raw_matrix_rows :
    (¬ CoindSat asymmetryGraph (.auto .send) 1 ∧
     ¬ CoindSat asymmetryGraph (.auto .sync) 1 ∧
     CoindSat asymmetryGraph (.auto .freeze) 1 ∧
     CoindSat asymmetryGraph .immutable 1) ∧
    (¬ CoindSat asymmetryGraph (.auto .send) 4 ∧
     ¬ CoindSat asymmetryGraph (.auto .sync) 4 ∧
     CoindSat asymmetryGraph (.auto .freeze) 4 ∧
     CoindSat asymmetryGraph .immutable 4) := by
  refine ⟨⟨?_, ?_, checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl⟩,
          ⟨?_, ?_, checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl⟩⟩
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .send 1)
      (IsDirectNegativeAuto.rawSend rfl)
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .sync 1)
      (IsDirectNegativeAuto.rawSync rfl)
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.phantomSend rfl) (AutoReach.refl .send 1))
      (IsDirectNegativeAuto.rawSend rfl)
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.phantomSync rfl) (AutoReach.refl .sync 1))
      (IsDirectNegativeAuto.rawSync rfl)

/-- `Rc<u32>` (`5`) is `Freeze` (`!Send`, `!Sync`, `!Immutable`). -/
theorem rc_matrix_row :
    ¬ CoindSat asymmetryGraph (.auto .send) 5 ∧
    ¬ CoindSat asymmetryGraph (.auto .sync) 5 ∧
    CoindSat asymmetryGraph (.auto .freeze) 5 ∧
    ¬ CoindSat asymmetryGraph .immutable 5 := by
  refine ⟨?_, ?_, checkWithStack_sound_fuel 16 rfl, ?_⟩
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .send 5)
      (IsDirectNegativeAuto.rcSend rfl)
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .sync 5)
      (IsDirectNegativeAuto.rcSync rfl)
  · intro h
    have hs := coindSat_unfold h
    exact hs

/-- `Box<UnsafeCell<u32>>` (`6`, `boxSized = true`) implements `Send + Freeze + Immutable` yet `!Sync`,
while `Box<[UnsafeCell<u32>]>` (`8`, `boxSized = false`) fails `Immutable`. -/
theorem box_sized_vs_unsized_unsafecell :
    (CoindSat asymmetryGraph (.auto .send) 6 ∧
     CoindSat asymmetryGraph (.auto .freeze) 6 ∧
     CoindSat asymmetryGraph .immutable 6 ∧
     ¬ CoindSat asymmetryGraph (.auto .sync) 6) ∧
    ¬ CoindSat asymmetryGraph .immutable 8 := by
  refine ⟨⟨checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, checkWithStack_sound_fuel 16 rfl, ?_⟩, ?_⟩
  · exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.boxPtrSync rfl) (AutoReach.refl .sync 2))
      (IsDirectNegativeAuto.cellSync rfl)
  · intro h
    have hs := coindSat_unfold h
    dsimp [StepF, asymmetryGraph] at hs
    cases hs

/-- `WithUnsafeField` (`11`) suppresses unsafe auto traits (`Send`, `Sync`, `Freeze`)
while permitting safe `Unpin`. `NegSendStruct` (`12`) blocks `Send` via explicit `impl !Send`. -/
theorem unsafe_field_and_negative_impl_discrimination :
    (¬ CoindSat asymmetryGraph (.auto .send) 11 ∧
     ¬ CoindSat asymmetryGraph (.auto .sync) 11 ∧
     ¬ CoindSat asymmetryGraph (.auto .freeze) 11 ∧
     CoindSat asymmetryGraph (.auto .unpin) 11) ∧
    (¬ CoindSat asymmetryGraph (.auto .send) 12 ∧
     CoindSat asymmetryGraph (.auto .sync) 12) := by
  refine ⟨⟨?_, ?_, ?_, checkWithStack_sound_fuel 16 rfl⟩, ⟨?_, checkWithStack_sound_fuel 16 rfl⟩⟩
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .send 11)
      (IsDirectNegativeAuto.adtUnsafeField rfl rfl)
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .sync 11)
      (IsDirectNegativeAuto.adtUnsafeField rfl rfl)
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .freeze 11)
      (IsDirectNegativeAuto.adtUnsafeField rfl rfl)
  · exact coindSat_rejects_reachable_negative_leaf (AutoReach.refl .send 12)
      (IsDirectNegativeAuto.adtNegImpl rfl rfl)

/-- Kleene GFP convergence check on `asymmetryGraph`: step `4` equals step `3` across
every `(TraitPred, n < 18)`, proving full decidable soundness & completeness. -/
theorem asymmetry_kleene_converges_at_3 :
    graphFixpointEq asymmetryGraph (kleeneGfp asymmetryGraph 3) = true := rfl

/-!
## Part 5: Byte-Level Interior-Mutability Freedom (`zerocopy::Immutable` Soundness)
-/

/-- Mutability classification of an individual runtime byte owned inline by a value. -/
inductive ByteCellKind where
  | immutableByte
  | interiorMutByte

/-- Structural equality on `ByteCellKind`. -/
noncomputable def ByteCellKind.beq : ByteCellKind → ByteCellKind → Bool
  | .immutableByte, .immutableByte => true
  | .interiorMutByte, .interiorMutByte => true
  | _, _ => false

/-- Repeat a byte classification `count` times. -/
noncomputable def repeatByte (k : ByteCellKind) : Nat → List ByteCellKind
  | 0 => []
  | m + 1 => k :: repeatByte k m

theorem repeatByte_all_imm (m : Nat) :
    AllProp (fun b => b = .immutableByte) (repeatByte .immutableByte m) := by
  induction m with
  | zero => exact AllProp.nil
  | succ k ih => exact AllProp.cons rfl ih

/-- Count `.interiorMutByte` entries in a byte list. -/
noncomputable def countMutBytes : List ByteCellKind → Nat
  | [] => 0
  | .immutableByte :: bs => countMutBytes bs
  | .interiorMutByte :: bs => 1 + countMutBytes bs

theorem countMutBytes_zero_of_all_imm {bs : List ByteCellKind}
    (h : AllProp (fun b => b = .immutableByte) bs) : countMutBytes bs = 0 := by
  induction h with
  | nil => rfl
  | cons hb _ ih =>
    subst hb
    exact ih

theorem countMutBytes_append (xs ys : List ByteCellKind) :
    countMutBytes (xs ++ ys) = countMutBytes xs + countMutBytes ys := by
  induction xs with
  | nil =>
    dsimp [countMutBytes]
    rw [Nat.zero_add]
  | cons b bs ih =>
    cases b with
    | immutableByte =>
      dsimp [countMutBytes]
      exact ih
    | interiorMutByte =>
      dsimp [countMutBytes]
      rw [ih, Nat.add_assoc]

/-- Concatenate byte footprints of a list of inline ADT fields. -/
noncomputable def concatFieldBytes (f : NodeId → List ByteCellKind) :
    List NodeId → List ByteCellKind
  | [] => []
  | x :: xs => f x ++ concatFieldBytes f xs

/-- Runtime inline byte footprint of node `n` bounded by inline layout depth `depth`.
- `prim sz`: `sz` immutable bytes.
- Indirections (`rawPtr`, `refShared`, `refMut`, `boxPtr`, `rcPtr`): 8 immutable pointer bytes.
- `phantomData _`, `phantomPinned`: `[]` (`0` runtime bytes!).
- `unsafeCell _ sz`: `sz` `interiorMutByte` entries.
- `adtStruct fields`: inline concatenation of all `fields`. -/
noncomputable def ownedFootprint (g : TypeGraph) : Nat → NodeId → List ByteCellKind
  | 0, _ => []
  | depth + 1, n =>
    match g.kindOf n with
    | .prim sz => repeatByte .immutableByte sz
    | .rawPtr _ => repeatByte .immutableByte 8
    | .refShared _ => repeatByte .immutableByte 8
    | .refMut _ => repeatByte .immutableByte 8
    | .boxPtr _ => repeatByte .immutableByte 8
    | .rcPtr _ => repeatByte .immutableByte 8
    | .unsafeCell _ sz => repeatByte .interiorMutByte sz
    | .phantomData _ => []
    | .phantomPinned => []
    | .adtStruct fields _ _ _ => concatFieldBytes (ownedFootprint g depth) fields
    | .rpitOpaque hidden => ownedFootprint g depth hidden
    | .dynObj _ => []

/-- Number of owned inline `UnsafeCell` bytes in node `n` at depth `depth`. -/
noncomputable def unsafeCellByteCount (g : TypeGraph) (depth : Nat) (n : NodeId) : Nat :=
  countMutBytes (ownedFootprint g depth n)

/-- Finite inline layout depth judgment (mirroring Rust's `E0072` rule that inline fields
cannot cycle without an indirection such as `Box`, `&`, `*const`, or `PhantomData`). -/
noncomputable def HasFiniteInlineLayout (g : TypeGraph) : NodeId → Nat → Prop
  | _, 0 => False
  | n, d + 1 =>
    match g.kindOf n with
    | .prim _ => True
    | .rawPtr _ => True
    | .refShared _ => True
    | .refMut _ => True
    | .boxPtr _ => True
    | .rcPtr _ => True
    | .unsafeCell _ _ => True
    | .phantomData _ => True
    | .phantomPinned => True
    | .adtStruct fields _ _ _ => AllProp (fun f => HasFiniteInlineLayout g f d) fields
    | .rpitOpaque _ => False
    | .dynObj _ => False

theorem AllProp_concatFieldBytes {f : NodeId → List ByteCellKind} {P : ByteCellKind → Prop} :
    ∀ fields : List NodeId,
      AllProp (fun id => AllProp P (f id)) fields →
      AllProp P (concatFieldBytes f fields) := by
  intro fields hAll
  induction hAll with
  | nil => exact AllProp.nil
  | cons hf _ ih =>
    dsimp [concatFieldBytes]
    exact AllProp_append hf ih

/-- Reachability of an inline `UnsafeCell` (including zero-sized `UnsafeCell<()>`) through
non-indirection, non-`PhantomData` inline structural fields. -/
inductive ReachableInlineUnsafeCell (g : TypeGraph) : NodeId → Prop where
  | direct {n inner sz : NodeId} :
      g.kindOf n = .unsafeCell inner sz → ReachableInlineUnsafeCell g n
  | adtField {n f : NodeId} {fields : List NodeId} {hasUnsafe : Bool}
      {negAuto : AutoTrait → Bool} {immImpl : Bool} :
      g.kindOf n = .adtStruct fields hasUnsafe negAuto immImpl →
      Mem f fields →
      ReachableInlineUnsafeCell g f →
      ReachableInlineUnsafeCell g n

/-- **Theorem 3a (Inline `UnsafeCell` Exclusion for `zerocopy::Immutable`):**
Even for zero-sized `UnsafeCell<()>`, `CoindSat g .immutable n` guarantees that NO
`UnsafeCell` is reachable along any inline structural field path (`PhantomData` and
pointer indirections stop inline reachability because they carry zero owned `UnsafeCell`
state). -/
theorem coindSat_immutable_implies_no_inline_unsafecell {g : TypeGraph} {n : NodeId}
    (hImm : CoindSat g .immutable n) : ¬ ReachableInlineUnsafeCell g n := by
  intro hReach
  induction hReach with
  | direct hk =>
    exact coindSat_unsafeCell_not_immutable hk hImm
  | adtField hk hMem _ ih =>
    have hs := coindSat_unfold hImm
    dsimp [StepF] at hs
    rw [hk] at hs
    exact ih (AllProp_mem hs.2 hMem)

/-- **Theorem 3b (Byte-Level Interior-Mutability Freedom):**
For every `n` with a finite inline layout (`HasFiniteInlineLayout g n depth`),
`CoindSat g .immutable n` implies that **every** inline byte owned by `n` is `.immutableByte`
and `unsafeCellByteCount g depth n = 0`. -/
theorem coindSat_immutable_implies_all_bytes_immutable {g : TypeGraph} :
    ∀ depth n,
      HasFiniteInlineLayout g n depth →
      CoindSat g .immutable n →
      AllProp (fun b => b = .immutableByte) (ownedFootprint g depth n) := by
  intro depth
  induction depth with
  | zero =>
    intro n hLay _
    exact False.elim hLay
  | succ d ih =>
    intro n hLay hImm
    dsimp [HasFiniteInlineLayout] at hLay
    dsimp [ownedFootprint]
    have hs := coindSat_unfold hImm
    dsimp [StepF] at hs
    revert hLay hs
    cases hk : g.kindOf n with
    | prim _ => intro _ _; exact repeatByte_all_imm _
    | rawPtr _ => intro _ _; exact repeatByte_all_imm 8
    | refShared _ => intro _ _; exact repeatByte_all_imm 8
    | refMut _ => intro _ _; exact repeatByte_all_imm 8
    | boxPtr _ => intro _ _; exact repeatByte_all_imm 8
    | rcPtr _ => intro _ hs; cases hs
    | unsafeCell _ _ =>
      intro _ _
      exact False.elim (coindSat_unsafeCell_not_immutable hk hImm)
    | phantomData _ => intro _ _; exact AllProp.nil
    | phantomPinned => intro _ _; exact AllProp.nil
    | adtStruct fields _ _ _ =>
      intro hLay hs
      dsimp at hLay hs
      have hSub := hs.2
      clear hk hs hImm
      apply AllProp_concatFieldBytes
      apply AllProp_of_forall
      intro f hf
      exact ih f (AllProp_mem hLay hf) (AllProp_mem hSub hf)
    | rpitOpaque _ => intro hLay _; cases hLay
    | dynObj _ => intro hLay _; cases hLay

theorem coindSat_immutable_implies_zero_unsafecell_bytes {g : TypeGraph} {depth n : Nat}
    (hLay : HasFiniteInlineLayout g n depth) (hImm : CoindSat g .immutable n) :
    unsafeCellByteCount g depth n = 0 :=
  countMutBytes_zero_of_all_imm (coindSat_immutable_implies_all_bytes_immutable depth n hLay hImm)

/-- Concrete byte-level witnesses:
1. Recursive `Node(Option<Box<Node>>)` has a finite depth-2 inline layout (`12` immutable bytes, `0` mutable bytes).
2. `PhantomData<UnsafeCell<u32>>` owns `0` runtime bytes (`[]`) and zero inline `UnsafeCell`s.
3. `HasPhantomCell { val: u32, _marker: PhantomData<UnsafeCell<u32>> }` owns `4` immutable bytes and `0` mutable bytes.
4. `UnsafeCell<u32>` owns `4` interior-mutable bytes (`≠ 0`), blocking `Immutable`. -/
theorem concrete_byte_level_immutable_witnesses :
    HasFiniteInlineLayout cycleGraph 2 2 ∧
    unsafeCellByteCount cycleGraph 2 2 = 0 ∧
    ownedFootprint asymmetryGraph 2 3 = [] ∧
    unsafeCellByteCount asymmetryGraph 2 3 = 0 ∧
    HasFiniteInlineLayout asymmetryGraph 9 3 ∧
    unsafeCellByteCount asymmetryGraph 3 9 = 0 ∧
    unsafeCellByteCount asymmetryGraph 2 2 = 4 := by
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
  · exact AllProp.cons trivial (AllProp.cons trivial AllProp.nil)
  · exact AllProp.cons trivial (AllProp.cons trivial AllProp.nil)

/-- Even zero-sized `UnsafeCell<()>` (`15` in `asymmetryGraph`) fails `Immutable`
(despite having `0` bytes), contrasting with `PhantomData<UnsafeCell<u32>>` (`3`). -/
theorem zst_unsafecell_fails_immutable_while_phantom_passes :
    unsafeCellByteCount asymmetryGraph 2 15 = 0 ∧
    ReachableInlineUnsafeCell asymmetryGraph 15 ∧
    ¬ CoindSat asymmetryGraph .immutable 15 ∧
    ¬ ReachableInlineUnsafeCell asymmetryGraph 3 ∧
    CoindSat asymmetryGraph .immutable 3 := by
  refine ⟨rfl, ReachableInlineUnsafeCell.direct rfl, ?_, ?_, checkWithStack_sound_fuel 16 rfl⟩
  · exact coindSat_unsafeCell_not_immutable rfl
  · exact coindSat_immutable_implies_no_inline_unsafecell (checkWithStack_sound_fuel 16 rfl)

/-!
## Part 6: Async Coroutine Suspend-Live Auto-Trait Preservation
-/

/-- A local variable declared inside an `async fn` / coroutine MIR body, reflecting
`compiler/rustc_mir_transform/src/coroutine/layout.rs` (`locals_live_across_suspend_points`,
`ignore_for_traits`) and `compiler/rustc_traits/src/coroutine_witnesses.rs`
(`coroutine_hidden_types`). -/
structure CoroutineLocal where
  localId : Nat
  tyNode : NodeId
  liveAcrossAnyAwait : Bool
  ignoreForTraits : Bool

/-- Coroutine state machine type summary (`ty::Coroutine` + `ty::CoroutineWitness`). -/
structure CoroutineBody where
  upvarNodes : List NodeId
  locals : List CoroutineLocal
  movable : Bool

/-- Locals included in the coroutine witness for trait evaluation (`coroutine_hidden_types`:
`liveAcrossAnyAwait = true ∧ ignoreForTraits = false`). -/
noncomputable def witnessLocals : List CoroutineLocal → List CoroutineLocal
  | [] => []
  | l :: ls =>
    match l.liveAcrossAnyAwait && !l.ignoreForTraits with
    | true => l :: witnessLocals ls
    | false => witnessLocals ls

theorem mem_witnessLocals_iff (l : CoroutineLocal) (ls : List CoroutineLocal) :
    Mem l (witnessLocals ls) ↔
      (Mem l ls ∧ l.liveAcrossAnyAwait = true ∧ l.ignoreForTraits = false) := by
  induction ls with
  | nil =>
    dsimp [witnessLocals]
    constructor
    · intro h; cases h
    · intro h; cases h.1
  | cons x xs ih =>
    dsimp [witnessLocals]
    cases hx : (x.liveAcrossAnyAwait && !x.ignoreForTraits)
    · constructor
      · intro h
        rcases (ih).mp h with ⟨hm, hl, hi⟩
        exact ⟨Mem.tail hm, hl, hi⟩
      · intro ⟨hm, hl, hi⟩
        cases hm with
        | head =>
          rw [hl, hi] at hx
          cases hx
        | tail hxt =>
          exact (ih).mpr ⟨hxt, hl, hi⟩
    · have hxLive : x.liveAcrossAnyAwait = true := by
        revert hx
        cases x.liveAcrossAnyAwait with
        | true => intro _; rfl
        | false => intro hx; cases hx
      have hxIgn : x.ignoreForTraits = false := by
        revert hx
        rw [hxLive]
        cases x.ignoreForTraits with
        | false => intro _; rfl
        | true => intro hx; cases hx
      constructor
      · intro h
        cases h with
        | head => exact ⟨Mem.head, hxLive, hxIgn⟩
        | tail ht =>
          rcases (ih).mp ht with ⟨hm, hl, hi⟩
          exact ⟨Mem.tail hm, hl, hi⟩
      · intro ⟨hm, hl, hi⟩
        cases hm with
        | head => exact Mem.head
        | tail hxt => exact Mem.tail ((ih).mpr ⟨hxt, hl, hi⟩)

/-- Auto-trait implementation judgment for `ty::Coroutine(def_id, args)` matching
`candidate_assembly.rs`:
- `Unpin` holds iff `c.movable = true` (`Movability::Movable` vs `Movability::Static`).
- Other auto traits (`Send`, `Sync`, `Freeze`) hold iff every upvar in `c.upvarNodes`
  and every live-across-`.await` non-ignored witness local in `c.locals` satisfies
  `CoindSat g (.auto a)`. -/
noncomputable def CoroutineImplementsAuto (g : TypeGraph) (c : CoroutineBody) :
    AutoTrait → Prop
  | .unpin => c.movable = true
  | a =>
    AllProp (fun u => CoindSat g (.auto a) u) c.upvarNodes ∧
    AllProp (fun l => CoindSat g (.auto a) l.tyNode) (witnessLocals c.locals)

/-- Executable checker for `CoroutineImplementsAuto g c .send` using `checkWithStack`. -/
noncomputable def isCoroutineSendBool (g : TypeGraph) (fuel : Nat) (c : CoroutineBody) : Bool :=
  allBool (fun u => checkWithStack g fuel [] (.auto .send) u) c.upvarNodes &&
  allBool (fun l => checkWithStack g fuel [] (.auto .send) l.tyNode) (witnessLocals c.locals)

theorem isCoroutineSendBool_sound {g : TypeGraph} {fuel : Nat} {c : CoroutineBody}
    (h : isCoroutineSendBool g fuel c = true) :
    CoroutineImplementsAuto g c .send := by
  dsimp [isCoroutineSendBool] at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hu, hw⟩
  have hUpvars := (allBool_iff _ c.upvarNodes).mp hu
  have hWits := (allBool_iff _ (witnessLocals c.locals)).mp hw
  exact ⟨
    AllProp_mono (fun _ hx => checkWithStack_sound hx) hUpvars,
    AllProp_mono (fun _ hx => checkWithStack_sound hx) hWits
  ⟩

/-- Fuel-explicit wrapper around `isCoroutineSendBool_sound`. -/
theorem isCoroutineSendBool_sound_fuel (fuel : Nat) {g : TypeGraph} {c : CoroutineBody}
    (h : isCoroutineSendBool g fuel c = true) :
    CoroutineImplementsAuto g c .send :=
  isCoroutineSendBool_sound h

/-- **Theorem 4a (Async Coroutine Suspend-Live Auto-Trait Preservation):**
For any `async fn` coroutine whose upvars are `Send`, the coroutine future is `Send`
if and only if every non-ignored local live across a suspension point (`.await`) is `Send`. -/
theorem async_coroutine_send_iff_live_across_await_send (g : TypeGraph) (c : CoroutineBody)
    (hUpvars : AllProp (fun u => CoindSat g (.auto .send) u) c.upvarNodes) :
    CoroutineImplementsAuto g c .send ↔
      (∀ l : CoroutineLocal,
        Mem l c.locals →
        l.liveAcrossAnyAwait = true →
        l.ignoreForTraits = false →
        CoindSat g (.auto .send) l.tyNode) := by
  constructor
  · intro hCoro l hl hLive hIgn
    have hWits := hCoro.2
    have hInW : Mem l (witnessLocals c.locals) :=
      (mem_witnessLocals_iff l c.locals).mpr ⟨hl, hLive, hIgn⟩
    exact AllProp_mem hWits hInW
  · intro hAll
    refine ⟨hUpvars, ?_⟩
    apply AllProp_of_forall
    intro l hlW
    rcases (mem_witnessLocals_iff l c.locals).mp hlW with ⟨hl, hLive, hIgn⟩
    exact hAll l hl hLive hIgn

/-- **Theorem 4b (Dead-Before-`.await` Non-`Send` Immunity):**
Holding a `!Send` local (`Rc<u32>`) that is dropped before `.await` (`liveAcrossAnyAwait = false`)
preserves `Send` of the coroutine future. -/
theorem async_dead_non_send_local_preserves_send {g : TypeGraph} {c : CoroutineBody}
    (hSend : CoroutineImplementsAuto g c .send) (rcLocalId : Nat) (rcTyNode : NodeId) :
    let deadRc : CoroutineLocal :=
      { localId := rcLocalId, tyNode := rcTyNode, liveAcrossAnyAwait := false, ignoreForTraits := false }
    CoroutineImplementsAuto g { c with locals := deadRc :: c.locals } .send := by
  dsimp [CoroutineImplementsAuto, witnessLocals]
  exact hSend

/-- **Theorem 4c (Live-Across-`.await` `Rc` Leak Rejection):**
If any non-ignored `Rc<u32>` local is live across `.await`, the coroutine is NOT `Send`. -/
theorem async_live_rc_across_await_breaks_send {c : CoroutineBody} {l : CoroutineLocal}
    (hMem : Mem l c.locals) (hLive : l.liveAcrossAnyAwait = true)
    (hIgn : l.ignoreForTraits = false) (hRc : l.tyNode = 5) :
    ¬ CoroutineImplementsAuto asymmetryGraph c .send := by
  intro hSend
  have hRcSend : CoindSat asymmetryGraph (.auto .send) 5 := by
    rw [← hRc]
    exact AllProp_mem hSend.2 ((mem_witnessLocals_iff l c.locals).mpr ⟨hMem, hLive, hIgn⟩)
  exact rc_matrix_row.1 hRcSend

/-- **Theorem 4d (Value vs. Shared-Reference Asymmetry Across `.await`):**
1. Holding `UnsafeCell<u32>` (`2`) or `PhantomData<UnsafeCell<u32>>` (`3`) by value across
   `.await` yields a `Send` future.
2. Holding `&UnsafeCell<u32>` (`13`) or `&PhantomData<UnsafeCell<u32>>` (`14`) across
   `.await` breaks `Send`, because `&T: Send ↔ T: Sync` and both underlying types are `!Sync`. -/
theorem async_unsafecell_value_send_vs_ref_not_send :
    let cellByValCoro : CoroutineBody :=
      { upvarNodes := []
        locals :=
          [ { localId := 1, tyNode := 2, liveAcrossAnyAwait := true, ignoreForTraits := false }
          , { localId := 2, tyNode := 3, liveAcrossAnyAwait := true, ignoreForTraits := false }
          , { localId := 3, tyNode := 5, liveAcrossAnyAwait := false, ignoreForTraits := false } ]
        movable := false }
    let refCellCoro : CoroutineBody :=
      { upvarNodes := []
        locals :=
          [ { localId := 1, tyNode := 13, liveAcrossAnyAwait := true, ignoreForTraits := false } ]
        movable := false }
    let refPhantomCoro : CoroutineBody :=
      { upvarNodes := []
        locals :=
          [ { localId := 1, tyNode := 14, liveAcrossAnyAwait := true, ignoreForTraits := false } ]
        movable := false }
    CoroutineImplementsAuto asymmetryGraph cellByValCoro .send ∧
    ¬ CoroutineImplementsAuto asymmetryGraph refCellCoro .send ∧
    ¬ CoroutineImplementsAuto asymmetryGraph refPhantomCoro .send := by
  refine ⟨isCoroutineSendBool_sound_fuel 16 rfl, ?_, ?_⟩
  · intro hSend
    have h13 : CoindSat asymmetryGraph (.auto .send) 13 :=
      AllProp_mem hSend.2 Mem.head
    exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.refSharedSend rfl) (AutoReach.refl .sync 2))
      (IsDirectNegativeAuto.cellSync rfl)
      h13
  · intro hSend
    have h14 : CoindSat asymmetryGraph (.auto .send) 14 :=
      AllProp_mem hSend.2 Mem.head
    exact coindSat_rejects_reachable_negative_leaf
      (AutoReach.step (AutoConstituentStep.refSharedSend rfl)
        (AutoReach.step (AutoConstituentStep.phantomSync rfl) (AutoReach.refl .sync 2)))
      (IsDirectNegativeAuto.cellSync rfl)
      h14

/-- **Theorem 4e (Static `async fn` Immovability):**
Every `async fn` (`movable = false`) rejects `Unpin` regardless of its captured upvars or
witness locals (`candidate_assembly.rs` `Movability::Static` suppression). -/
theorem async_static_not_unpin (g : TypeGraph) (c : CoroutineBody)
    (hStat : c.movable = false) : ¬ CoroutineImplementsAuto g c .unpin := by
  intro hUnpin
  dsimp [CoroutineImplementsAuto] at hUnpin
  rw [hUnpin] at hStat
  cases hStat

end AutoTraitsCoinductiveImmutable
