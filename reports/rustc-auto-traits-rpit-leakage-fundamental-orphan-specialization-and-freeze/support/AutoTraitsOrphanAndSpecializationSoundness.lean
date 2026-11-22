/-!
# Soundness Model: Rust Auto-Trait Synthesis & RPIT Leakage, `#[fundamental]` Orphan
# Coherence, `min_specialization` Region-Erasure Determinism, `#[marker]` Overlap,
# Negative Impls, and `Freeze` vs. `UnsafeCell` Placement

Standalone kernel-checked Lean v4.34.1 formalization companion to the reference report
`rustc-auto-traits-rpit-leakage-fundamental-orphan-specialization-and-freeze`.

Design constraints verified by the Lean kernel:
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`, zero `partial def`, zero `._unsafe_rec` auxiliary constants.
- Every recursive term definition carries `noncomputable` so the Lean compiler does
  not synthesize `partial` `._unsafe_rec` codegen helpers, while keeping all kernel
  terms purely constructive (no classical axioms).
-/

namespace AutoTraitsOrphanSpecialization

/-!
## Part 1: Structural Auto-Trait Synthesis, Negative Impls, RPIT Leakage, `dyn` Erasure,
## and the `Freeze` / `UnsafeCell` Barrier
-/

/-- The four core language auto traits modeled in this study. -/
inductive AutoTrait where
  | send
  | sync
  | unpin
  | freeze

/-- Abstract Rust type expressions capturing primitives, interior mutability
(`UnsafeCell`), immovable markers (`PhantomPinned`), reference-counted pointers
(`Rc`), shared/mutable references, raw pointers, `PhantomData`, `Box`, binary
products, nominal ADTs with explicit negative-impl overrides, return-position
`impl Trait` (`rpitOpaque`), and trait objects (`dynObj`). -/
inductive TyExpr where
  | prim
  | unsafeCell (inner : TyExpr)
  | phantomPinned
  | rc (inner : TyExpr)
  | refShared (inner : TyExpr)
  | refMut (inner : TyExpr)
  | rawPtr (inner : TyExpr)
  | phantomData (inner : TyExpr)
  | boxTy (inner : TyExpr)
  | pair (fst snd : TyExpr)
  | namedAdt (adtId : Nat) (fields : List TyExpr)
  | rpitOpaque (hidden : TyExpr)
  | dynObj (declaredAuto : List AutoTrait)

/-- An explicit negative-impl environment mapping `(adtId, autoTrait)` to `true`
when `impl !<autoTrait> for Adt<adtId> {}` is declared. -/
abbrev NegImplEnv := Nat → AutoTrait → Bool

/-- List membership predicate over `List α` (inductive, avoiding classical helpers). -/
inductive Mem {α : Type} (x : α) : List α → Prop where
  | head {xs : List α} : Mem x (x :: xs)
  | tail {y : α} {xs : List α} : Mem x xs → Mem x (y :: xs)

mutual
  /-- Structural auto-trait derivation modeling `rustc_trait_selection`'s
  `assemble_candidates_from_auto_impls`, `constituent_types_for_auto_trait`,
  `assemble_candidates_from_object_ty`, and `core::marker` manual positive/negative
  impls:
  - `UnsafeCell<T>`: `!Sync`, `!Freeze`, `Send` iff `T: Send`, `Unpin` iff `T: Unpin`.
  - `PhantomPinned`: `!Unpin`, always `Send + Sync + Freeze`.
  - `Rc<T>`: `!Send`, `!Sync`, always `Unpin + Freeze` (pointer indirection).
  - `&T`: `Send ↔ T: Sync`, `Sync ↔ T: Sync`, always `Unpin + Freeze`.
  - `&mut T`: `Send ↔ T: Send`, `Sync ↔ T: Sync`, always `Unpin + Freeze`.
  - `*const T` / `*mut T`: `!Send`, `!Sync`, always `Unpin + Freeze`.
  - `PhantomData<T>`: always `Freeze`; `Send`/`Sync`/`Unpin` delegate to `T`.
  - `Box<T>`: always `Unpin + Freeze` (heap pointer indirection); `Send`/`Sync` delegate to `T`.
  - `rpitOpaque hidden`: transparently leaks auto traits of `hidden`.
  - `dynObj declared`: opaque erasure; holds iff `a` is explicitly listed in `declared`.
  - `namedAdt id fields`: blocked when `neg id a = true`; otherwise structural over `fields`. -/
  inductive ImplementsAuto (neg : NegImplEnv) : AutoTrait → TyExpr → Prop where
    | prim (a : AutoTrait) :
        ImplementsAuto neg a .prim
    | unsafeCellSend {t : TyExpr} :
        ImplementsAuto neg .send t →
        ImplementsAuto neg .send (.unsafeCell t)
    | unsafeCellUnpin {t : TyExpr} :
        ImplementsAuto neg .unpin t →
        ImplementsAuto neg .unpin (.unsafeCell t)
    | phantomPinnedSend :
        ImplementsAuto neg .send .phantomPinned
    | phantomPinnedSync :
        ImplementsAuto neg .sync .phantomPinned
    | phantomPinnedFreeze :
        ImplementsAuto neg .freeze .phantomPinned
    | rcUnpin (t : TyExpr) :
        ImplementsAuto neg .unpin (.rc t)
    | rcFreeze (t : TyExpr) :
        ImplementsAuto neg .freeze (.rc t)
    | refSharedSend {t : TyExpr} :
        ImplementsAuto neg .sync t →
        ImplementsAuto neg .send (.refShared t)
    | refSharedSync {t : TyExpr} :
        ImplementsAuto neg .sync t →
        ImplementsAuto neg .sync (.refShared t)
    | refSharedUnpin (t : TyExpr) :
        ImplementsAuto neg .unpin (.refShared t)
    | refSharedFreeze (t : TyExpr) :
        ImplementsAuto neg .freeze (.refShared t)
    | refMutSend {t : TyExpr} :
        ImplementsAuto neg .send t →
        ImplementsAuto neg .send (.refMut t)
    | refMutSync {t : TyExpr} :
        ImplementsAuto neg .sync t →
        ImplementsAuto neg .sync (.refMut t)
    | refMutUnpin (t : TyExpr) :
        ImplementsAuto neg .unpin (.refMut t)
    | refMutFreeze (t : TyExpr) :
        ImplementsAuto neg .freeze (.refMut t)
    | rawPtrUnpin (t : TyExpr) :
        ImplementsAuto neg .unpin (.rawPtr t)
    | rawPtrFreeze (t : TyExpr) :
        ImplementsAuto neg .freeze (.rawPtr t)
    | phantomDataSend {t : TyExpr} :
        ImplementsAuto neg .send t →
        ImplementsAuto neg .send (.phantomData t)
    | phantomDataSync {t : TyExpr} :
        ImplementsAuto neg .sync t →
        ImplementsAuto neg .sync (.phantomData t)
    | phantomDataUnpin {t : TyExpr} :
        ImplementsAuto neg .unpin t →
        ImplementsAuto neg .unpin (.phantomData t)
    | phantomDataFreeze (t : TyExpr) :
        ImplementsAuto neg .freeze (.phantomData t)
    | boxSend {t : TyExpr} :
        ImplementsAuto neg .send t →
        ImplementsAuto neg .send (.boxTy t)
    | boxSync {t : TyExpr} :
        ImplementsAuto neg .sync t →
        ImplementsAuto neg .sync (.boxTy t)
    | boxUnpin (t : TyExpr) :
        ImplementsAuto neg .unpin (.boxTy t)
    | boxFreeze (t : TyExpr) :
        ImplementsAuto neg .freeze (.boxTy t)
    | pair {a : AutoTrait} {t₁ t₂ : TyExpr} :
        ImplementsAuto neg a t₁ →
        ImplementsAuto neg a t₂ →
        ImplementsAuto neg a (.pair t₁ t₂)
    | namedAdt {a : AutoTrait} {id : Nat} {fields : List TyExpr} :
        neg id a = false →
        ImplementsAutoList neg a fields →
        ImplementsAuto neg a (.namedAdt id fields)
    | rpitOpaque {a : AutoTrait} {hidden : TyExpr} :
        ImplementsAuto neg a hidden →
        ImplementsAuto neg a (.rpitOpaque hidden)
    | dynObj {a : AutoTrait} {declared : List AutoTrait} :
        Mem a declared →
        ImplementsAuto neg a (.dynObj declared)

  /-- Elementwise `ImplementsAuto` across ADT field lists. -/
  inductive ImplementsAutoList (neg : NegImplEnv) : AutoTrait → List TyExpr → Prop where
    | nil (a : AutoTrait) :
        ImplementsAutoList neg a []
    | cons {a : AutoTrait} {x : TyExpr} {xs : List TyExpr} :
        ImplementsAuto neg a x →
        ImplementsAutoList neg a xs →
        ImplementsAutoList neg a (x :: xs)
end

/-- `ContainsDirectUnsafeCell ty` holds iff `ty` contains an `UnsafeCell` directly
in its inline representation (crossing products, nominal ADT fields, and transparent
RPIT hidden types, but not indirections `&T`, `&mut T`, `*const T`, `Box<T>`, `Rc<T>`,
zero-sized `PhantomData<T>`, or erased `dyn Trait`). -/
inductive ContainsDirectUnsafeCell : TyExpr → Prop where
  | here (t : TyExpr) :
      ContainsDirectUnsafeCell (.unsafeCell t)
  | pairFst {t₁ t₂ : TyExpr} :
      ContainsDirectUnsafeCell t₁ →
      ContainsDirectUnsafeCell (.pair t₁ t₂)
  | pairSnd {t₁ t₂ : TyExpr} :
      ContainsDirectUnsafeCell t₂ →
      ContainsDirectUnsafeCell (.pair t₁ t₂)
  | adtField {id : Nat} {f : TyExpr} {fields : List TyExpr} :
      Mem f fields →
      ContainsDirectUnsafeCell f →
      ContainsDirectUnsafeCell (.namedAdt id fields)
  | rpitHidden {hidden : TyExpr} :
      ContainsDirectUnsafeCell hidden →
      ContainsDirectUnsafeCell (.rpitOpaque hidden)

private theorem implementsAutoList_mem {neg : NegImplEnv} {a : AutoTrait}
    {x : TyExpr} {xs : List TyExpr}
    (hall : ImplementsAutoList neg a xs) (hmem : Mem x xs) :
    ImplementsAuto neg a x := by
  induction hmem with
  | head =>
    cases hall with
    | cons hx _ => exact hx
  | tail _ ih =>
    cases hall with
    | cons _ hxs => exact ih hxs

/-- **Theorem 1 (Auto-Trait Soundness & `UnsafeCell` `Freeze` Barrier):**
Any type `ty` that derives `Freeze` cannot contain a direct (non-indirected)
`UnsafeCell` anywhere in its inline structure (including inside products, nominal
ADTs, and RPIT hidden types). -/
theorem freeze_implies_no_unsafe_cell
    (neg : NegImplEnv) (ty : TyExpr)
    (hFreeze : ImplementsAuto neg .freeze ty) :
    ¬ ContainsDirectUnsafeCell ty := by
  intro hCell
  induction hCell with
  | here t =>
    cases hFreeze
  | pairFst _ ih =>
    cases hFreeze with
    | pair h₁ _ => exact ih h₁
  | pairSnd _ ih =>
    cases hFreeze with
    | pair _ h₂ => exact ih h₂
  | adtField hMem _ ih =>
    cases hFreeze with
    | namedAdt _ hFields =>
      exact ih (implementsAutoList_mem hFields hMem)
  | rpitHidden _ ih =>
    cases hFreeze with
    | rpitOpaque hHidden => exact ih hHidden

/-- ELF section placement for a `static` item (`InternKind::Static(Mutability::Not)`
in `rustc_const_eval/src/interpret/intern.rs` forwarded to `llvm::set_global_constant`
in `rustc_codegen_llvm/src/consts.rs`). -/
inductive ElfSectionPlacement where
  /-- Read-only allocation (`.rodata.*`, `PROGBITS`, flags `A`). -/
  | rodataReadOnly
  /-- Writable allocation (`.data.*` `PROGBITS` or `.bss.*` `NOBITS`, flags `WA`). -/
  | dataWritable

/-- A static's ELF placement is sound when every read-only `.rodata` (`A`) static
is guaranteed free of direct inline `UnsafeCell` bytes. -/
def StaticSectionSound (ty : TyExpr) (sec : ElfSectionPlacement) : Prop :=
  sec = .rodataReadOnly → ¬ ContainsDirectUnsafeCell ty

/-- Placing a `static` in `.rodata` (`A`) only when `ImplementsAuto neg .freeze ty`
preserves read-only section soundness. -/
theorem freeze_rodata_placement_sound
    (neg : NegImplEnv) (ty : TyExpr)
    (hRule : ImplementsAuto neg .freeze ty) :
    StaticSectionSound ty .rodataReadOnly := by
  intro _
  exact freeze_implies_no_unsafe_cell neg ty hRule

/-- Conversely, an inline `UnsafeCell` static can never satisfy `Freeze`, forcing
`.data`/`.bss` (`WA`) placement. -/
theorem unsafe_cell_not_freeze (neg : NegImplEnv) (t : TyExpr) :
    ¬ ImplementsAuto neg .freeze (.unsafeCell t) := by
  intro h
  exact freeze_implies_no_unsafe_cell neg (.unsafeCell t) h (.here t)

/-- RPIT auto-trait leakage positive witness: `impl Debug` hiding `u32` leaks
`Send`, `Sync`, `Unpin`, and `Freeze`. -/
theorem rpit_u32_leaks_all (neg : NegImplEnv) :
    ImplementsAuto neg .send (.rpitOpaque .prim) ∧
    ImplementsAuto neg .sync (.rpitOpaque .prim) ∧
    ImplementsAuto neg .unpin (.rpitOpaque .prim) ∧
    ImplementsAuto neg .freeze (.rpitOpaque .prim) :=
  ⟨.rpitOpaque (.prim .send),
   .rpitOpaque (.prim .sync),
   .rpitOpaque (.prim .unpin),
   .rpitOpaque (.prim .freeze)⟩

/-- RPIT auto-trait leakage negative witness: `impl Debug` hiding `Rc<u32>` blocks `Send`. -/
theorem rpit_rc_not_send (neg : NegImplEnv) :
    ¬ ImplementsAuto neg .send (.rpitOpaque (.rc .prim)) := by
  intro h
  cases h with
  | rpitOpaque hInner => cases hInner

/-- RPIT auto-trait leakage mixed witness: `impl Debug` hiding `Cell<u32>` (`UnsafeCell<u32>`)
leaks `Send` while blocking `Sync` and `Freeze`. -/
theorem rpit_cell_send_not_sync_not_freeze (neg : NegImplEnv) :
    ImplementsAuto neg .send (.rpitOpaque (.unsafeCell .prim)) ∧
    ¬ ImplementsAuto neg .sync (.rpitOpaque (.unsafeCell .prim)) ∧
    ¬ ImplementsAuto neg .freeze (.rpitOpaque (.unsafeCell .prim)) := by
  refine ⟨.rpitOpaque (.unsafeCellSend (.prim .send)), ?_, ?_⟩
  · intro h
    cases h with
    | rpitOpaque hInner => cases hInner
  · intro h
    cases h with
    | rpitOpaque hInner => cases hInner

/-- RPIT auto-trait leakage negative witness: `impl Debug` hiding `PhantomPinned`
blocks `Unpin`. -/
theorem rpit_phantom_pinned_not_unpin (neg : NegImplEnv) :
    ¬ ImplementsAuto neg .unpin (.rpitOpaque .phantomPinned) := by
  intro h
  cases h with
  | rpitOpaque hInner => cases hInner

/-- `dyn Trait` erasure witness: `Box<dyn Debug>` (`declaredAuto = []`) blocks `Send`,
in contrast to `impl Debug` hiding `u32`. -/
theorem dyn_debug_does_not_leak_send (neg : NegImplEnv) :
    ¬ ImplementsAuto neg .send (.boxTy (.dynObj [])) := by
  intro h
  cases h with
  | boxSend hDyn =>
    cases hDyn with
    | dynObj hMem => cases hMem

/-- `PhantomData<UnsafeCell<u32>>` satisfies `Freeze` while still failing `Sync`,
matching `library/core/src/marker.rs` (`marker_impls! { unsafe Freeze for PhantomData<T> }`). -/
theorem phantom_unsafe_cell_freeze_not_sync (neg : NegImplEnv) :
    ImplementsAuto neg .freeze (.phantomData (.unsafeCell .prim)) ∧
    ¬ ImplementsAuto neg .sync (.phantomData (.unsafeCell .prim)) := by
  refine ⟨.phantomDataFreeze (.unsafeCell .prim), ?_⟩
  intro h
  cases h with
  | phantomDataSync hCell => cases hCell

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

/-- Explicit negative impl `impl !Send for NoSend {}` overrides structural synthesis
even when all fields of `NoSend` (`[u32]`) are `Send`. -/
theorem negative_impl_blocks_send (id : Nat) :
    let neg : NegImplEnv := fun i a =>
      match Nat.beq i id, a with
      | true, .send => true
      | _, _ => false
    ¬ ImplementsAuto neg .send (.namedAdt id [.prim]) := by
  intro neg h
  cases h with
  | namedAdt hNeg _ =>
    change (match Nat.beq id id, AutoTrait.send with
            | true, .send => true
            | _, _ => false) = false at hNeg
    rw [nat_beq_refl id] at hNeg
    cases hNeg

/-!
## Part 2: Crate-Local Orphan Rules (`#[fundamental]` Unwrapping & Uncovered Params)
## and Global Coherence Preservation
-/

/-- Crate identifier in a multi-crate compilation graph. -/
abbrev CrateId := Nat

/-- Whether an ADT carries `#[fundamental]` (`Box`, `Pin`) or is an ordinary
non-fundamental wrapper (`Vec`, `Option`, user structs). -/
inductive WrapperKind where
  | fundamental
  | nonFundamental

/-- Monomorphized ground type (no type variables). -/
inductive GroundTy where
  | prim (primId : Nat)
  | refTy (isMut : Bool) (inner : GroundTy)
  | adt (owner : CrateId) (adtId : Nat) (kind : WrapperKind) (args : List GroundTy)

/-- Trait-impl type pattern (may contain generic type parameters `var v`). -/
inductive TyPat where
  | var (varId : Nat)
  | prim (primId : Nat)
  | refTy (isMut : Bool) (inner : TyPat)
  | adt (owner : CrateId) (adtId : Nat) (kind : WrapperKind) (args : List TyPat)

/-- A trait impl header pattern `impl<...> Trait<T₁..Tₙ> for T₀`, where `inputs`
lists `[T₀, T₁, ..., Tₙ]` in `rustc_next_trait_solver/src/coherence.rs` order. -/
structure TraitRefPat where
  traitOwner : CrateId
  traitId : Nat
  inputs : List TyPat

/-- A ground trait reference `<G₀ as Trait<G₁..Gₙ>>`. -/
structure GroundTraitRef where
  traitOwner : CrateId
  traitId : Nat
  inputs : List GroundTy

mutual
  /-- Instantiate a `TyPat` with a ground substitution `σ`. -/
  noncomputable def instantiateTy (σ : Nat → GroundTy) : TyPat → GroundTy
    | .var v => σ v
    | .prim p => .prim p
    | .refTy m inner => .refTy m (instantiateTy σ inner)
    | .adt owner id k args => .adt owner id k (instantiateTyList σ args)

  /-- Elementwise instantiation over `List TyPat`. -/
  noncomputable def instantiateTyList (σ : Nat → GroundTy) : List TyPat → List GroundTy
    | [] => []
    | p :: ps => instantiateTy σ p :: instantiateTyList σ ps
end

/-- Instantiate a trait reference pattern to a ground trait reference. -/
noncomputable def instantiateTraitRef (σ : Nat → GroundTy) (tr : TraitRefPat) : GroundTraitRef :=
  { traitOwner := tr.traitOwner
    traitId := tr.traitId
    inputs := instantiateTyList σ tr.inputs }

/-- Result of `OrphanChecker::visit_ty` scanning type arguments left-to-right
(`compiler/rustc_next_trait_solver/src/coherence.rs:237-255, 306-449`). -/
inductive OrphanScanResult where
  | nonLocal
  | localFound
  | uncoveredParam

mutual
  /-- Left-to-right orphan scan of one `TyPat` in crate `c`.
  - `&T` / `&mut T` (`refTy`) are built-in fundamental and recurse into `inner`.
  - Local ADTs (`owner == c`) immediately succeed (`localFound`).
  - Foreign `#[fundamental]` ADTs recurse left-to-right into `args`.
  - Foreign `nonFundamental` ADTs (`Vec`, `Option`) stop recursion (`nonLocal`).
  - Generic type variables (`var`) encountered before a local type fail (`uncoveredParam`). -/
  noncomputable def orphanScanTy (c : CrateId) : TyPat → OrphanScanResult
    | .var _ => .uncoveredParam
    | .prim _ => .nonLocal
    | .refTy _ inner => orphanScanTy c inner
    | .adt owner _ kind args =>
      if Nat.beq owner c then
        .localFound
      else
        match kind with
        | .fundamental => orphanScanList c args
        | .nonFundamental => .nonLocal

  /-- Left-to-right orphan scan over a list of type patterns, aborting immediately
  on the first `localFound` or `uncoveredParam`. -/
  noncomputable def orphanScanList (c : CrateId) : List TyPat → OrphanScanResult
    | [] => .nonLocal
    | p :: ps =>
      match orphanScanTy c p with
      | .nonLocal => orphanScanList c ps
      | .localFound => .localFound
      | .uncoveredParam => .uncoveredParam
end

/-- Crate `c` may declare `impl tr` under the Rust orphan rules iff either the trait
is local (`tr.traitOwner = c`) or the left-to-right fundamental-unwrapping scan
reaches a `c`-local type before any uncovered type parameter. -/
def OrphanAdmissible (c : CrateId) (tr : TraitRefPat) : Prop :=
  tr.traitOwner = c ∨ orphanScanList c tr.inputs = .localFound

mutual
  /-- Syntactic crate-visibility invariant: a pattern authored in crate `c` cannot
  name any ADT owned by an unknown crate `other`. -/
  noncomputable def TyPatAvoidsCrate (other : CrateId) : TyPat → Prop
    | .var _ => True
    | .prim _ => True
    | .refTy _ inner => TyPatAvoidsCrate other inner
    | .adt owner _ _ args => owner ≠ other ∧ TyPatListAvoidsCrate other args

  /-- Elementwise crate-avoidance over a pattern list. -/
  noncomputable def TyPatListAvoidsCrate (other : CrateId) : List TyPat → Prop
    | [] => True
    | p :: ps => TyPatAvoidsCrate other p ∧ TyPatListAvoidsCrate other ps
end

/-- A trait impl header written in a crate that cannot see crate `other` mentions
neither a trait owned by `other` nor any ADT owned by `other`. -/
def TraitRefAvoidsCrate (other : CrateId) (tr : TraitRefPat) : Prop :=
  tr.traitOwner ≠ other ∧ TyPatListAvoidsCrate other tr.inputs

mutual
  /-- The ordered sequence of crate owners reachable from a ground type through
  built-in `&`/`&mut` and `#[fundamental]` wrappers, stopping at non-fundamental ADTs. -/
  noncomputable def fundOwners : GroundTy → List CrateId
    | .prim _ => []
    | .refTy _ inner => fundOwners inner
    | .adt owner _ .nonFundamental _ => [owner]
    | .adt owner _ .fundamental args => owner :: fundOwnersList args

  /-- Concatenated `fundOwners` across a list of ground types in left-to-right order. -/
  noncomputable def fundOwnersList : List GroundTy → List CrateId
    | [] => []
    | g :: gs => fundOwners g ++ fundOwnersList gs
end

/-- `AppearsBefore a b xs` holds iff `a` appears in `xs` strictly before any
occurrence of `b` (including when `b` does not occur at all). -/
inductive AppearsBefore (a b : CrateId) : List CrateId → Prop where
  | here {xs : List CrateId} : AppearsBefore a b (a :: xs)
  | skip {x : CrateId} {xs : List CrateId} :
      x ≠ b → AppearsBefore a b xs → AppearsBefore a b (x :: xs)

/-- `NoMem b xs` holds iff `b` does not occur in `xs`. -/
inductive NoMem (b : CrateId) : List CrateId → Prop where
  | nil : NoMem b []
  | cons {x : CrateId} {xs : List CrateId} : x ≠ b → NoMem b xs → NoMem b (x :: xs)

private theorem noMem_append {b : CrateId} {xs ys : List CrateId}
    (hx : NoMem b xs) (hy : NoMem b ys) : NoMem b (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons hne _ ih => exact .cons hne ih

private theorem appearsBefore_append_right {a b : CrateId} {xs ys : List CrateId}
    (h : AppearsBefore a b xs) : AppearsBefore a b (xs ++ ys) := by
  induction h with
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

mutual
  /-- Key Lemma A: If `orphanScanTy c₁ pat = .nonLocal` and `pat` avoids `c₂`, then
  NO substitution `σ` can introduce a `c₂`-owned fundamental leaf. Crucially,
  `nonFundamental` wrappers (`Vec`, `Option`) stop traversal even over `var` args,
  and bare `var` is excluded because `orphanScanTy c₁ (.var _) = .uncoveredParam`. -/
  private theorem scan_nonLocal_no_foreign_owner
      (c₁ c₂ : CrateId) (σ : Nat → GroundTy) (pat : TyPat)
      (hScan : orphanScanTy c₁ pat = .nonLocal)
      (hAvoid : TyPatAvoidsCrate c₂ pat) :
      NoMem c₂ (fundOwners (instantiateTy σ pat)) := by
    cases pat with
    | var v =>
      cases hScan
    | prim p =>
      exact .nil
    | refTy m inner =>
      exact scan_nonLocal_no_foreign_owner c₁ c₂ σ inner hScan hAvoid
    | adt owner id kind args =>
      dsimp only [orphanScanTy] at hScan
      cases hEq : Nat.beq owner c₁ with
      | true =>
        rw [hEq] at hScan
        cases hScan
      | false =>
        rw [hEq] at hScan
        cases kind with
        | nonFundamental =>
          exact .cons hAvoid.1 .nil
        | fundamental =>
          exact .cons hAvoid.1 (scanList_nonLocal_no_foreign_owner c₁ c₂ σ args hScan hAvoid.2)

  private theorem scanList_nonLocal_no_foreign_owner
      (c₁ c₂ : CrateId) (σ : Nat → GroundTy) (pats : List TyPat)
      (hScan : orphanScanList c₁ pats = .nonLocal)
      (hAvoid : TyPatListAvoidsCrate c₂ pats) :
      NoMem c₂ (fundOwnersList (instantiateTyList σ pats)) := by
    cases pats with
    | nil => exact .nil
    | cons p ps =>
      dsimp only [orphanScanList] at hScan
      cases hp : orphanScanTy c₁ p with
      | nonLocal =>
        rw [hp] at hScan
        exact noMem_append
          (scan_nonLocal_no_foreign_owner c₁ c₂ σ p hp hAvoid.1)
          (scanList_nonLocal_no_foreign_owner c₁ c₂ σ ps hScan hAvoid.2)
      | localFound =>
        rw [hp] at hScan
        cases hScan
      | uncoveredParam =>
        rw [hp] at hScan
        cases hScan
end

mutual
  /-- Key Lemma B: If `orphanScanTy c₁ pat = .localFound` and `pat` avoids `c₂`, then
  for EVERY ground substitution `σ`, crate `c₁` appears in `fundOwners (instantiateTy σ pat)`
  strictly before any occurrence of `c₂`. -/
  private theorem scan_localFound_appearsBefore
      (c₁ c₂ : CrateId) (σ : Nat → GroundTy) (pat : TyPat)
      (hScan : orphanScanTy c₁ pat = .localFound)
      (hAvoid : TyPatAvoidsCrate c₂ pat) :
      AppearsBefore c₁ c₂ (fundOwners (instantiateTy σ pat)) := by
    cases pat with
    | var v =>
      cases hScan
    | prim p =>
      cases hScan
    | refTy m inner =>
      exact scan_localFound_appearsBefore c₁ c₂ σ inner hScan hAvoid
    | adt owner id kind args =>
      dsimp only [orphanScanTy] at hScan
      cases hEq : Nat.beq owner c₁ with
      | true =>
        have hOwn : owner = c₁ := nat_beq_true_eq hEq
        subst hOwn
        cases kind with
        | nonFundamental => exact .here
        | fundamental => exact .here
      | false =>
        rw [hEq] at hScan
        cases kind with
        | nonFundamental =>
          cases hScan
        | fundamental =>
          exact .skip hAvoid.1 (scanList_localFound_appearsBefore c₁ c₂ σ args hScan hAvoid.2)

  private theorem scanList_localFound_appearsBefore
      (c₁ c₂ : CrateId) (σ : Nat → GroundTy) (pats : List TyPat)
      (hScan : orphanScanList c₁ pats = .localFound)
      (hAvoid : TyPatListAvoidsCrate c₂ pats) :
      AppearsBefore c₁ c₂ (fundOwnersList (instantiateTyList σ pats)) := by
    cases pats with
    | nil => cases hScan
    | cons p ps =>
      dsimp only [orphanScanList] at hScan
      cases hp : orphanScanTy c₁ p with
      | nonLocal =>
        rw [hp] at hScan
        exact appearsBefore_append_left
          (scan_nonLocal_no_foreign_owner c₁ c₂ σ p hp hAvoid.1)
          (scanList_localFound_appearsBefore c₁ c₂ σ ps hScan hAvoid.2)
      | localFound =>
        exact appearsBefore_append_right
          (scan_localFound_appearsBefore c₁ c₂ σ p hp hAvoid.1)
      | uncoveredParam =>
        rw [hp] at hScan
        cases hScan
end

/-- **Theorem 2 (Orphan-Rule Global Coherence Preservation / Link-Safety):**
Let `c₁ ≠ c₂` be two mutually unknowing crates (`tr₁` authored in `c₁` cannot name
`c₂`-owned items; `tr₂` authored in `c₂` cannot name `c₁`-owned items). If both
impl headers satisfy `OrphanAdmissible`, then no pair of ground substitutions
`(σ₁, σ₂)` can instantiate them to the same ground trait reference. -/
theorem orphan_check_prevents_cross_crate_overlap
    (c₁ c₂ : CrateId) (hNe : c₁ ≠ c₂)
    (tr₁ tr₂ : TraitRefPat)
    (hAdm₁ : OrphanAdmissible c₁ tr₁)
    (hAdm₂ : OrphanAdmissible c₂ tr₂)
    (hAvoid₁ : TraitRefAvoidsCrate c₂ tr₁)
    (hAvoid₂ : TraitRefAvoidsCrate c₁ tr₂)
    (σ₁ σ₂ : Nat → GroundTy)
    (hOverlap : instantiateTraitRef σ₁ tr₁ = instantiateTraitRef σ₂ tr₂) :
    False := by
  have hTraitOwnerEq : tr₁.traitOwner = tr₂.traitOwner :=
    congrArg GroundTraitRef.traitOwner hOverlap
  have hInputsEq : instantiateTyList σ₁ tr₁.inputs = instantiateTyList σ₂ tr₂.inputs :=
    congrArg GroundTraitRef.inputs hOverlap
  cases hAdm₁ with
  | inl hLocalTrait₁ =>
    have : tr₂.traitOwner = c₁ := hTraitOwnerEq.symm.trans hLocalTrait₁
    exact hAvoid₂.1 this
  | inr hScan₁ =>
    cases hAdm₂ with
    | inl hLocalTrait₂ =>
      have : tr₁.traitOwner = c₂ := hTraitOwnerEq.trans hLocalTrait₂
      exact hAvoid₁.1 this
    | inr hScan₂ =>
      have hBef₁ : AppearsBefore c₁ c₂ (fundOwnersList (instantiateTyList σ₁ tr₁.inputs)) :=
        scanList_localFound_appearsBefore c₁ c₂ σ₁ tr₁.inputs hScan₁ hAvoid₁.2
      have hBef₂ : AppearsBefore c₂ c₁ (fundOwnersList (instantiateTyList σ₂ tr₂.inputs)) :=
        scanList_localFound_appearsBefore c₂ c₁ σ₂ tr₂.inputs hScan₂ hAvoid₂.2
      rw [hInputsEq] at hBef₁
      exact appearsBefore_asymm hNe hBef₁ hBef₂

/-- Concrete witness: `Pin<Box<Local>>` (`Pin` and `Box` both `#[fundamental]`,
`Local` owned by crate 2, trait `ForeignTr` owned by crate 1) passes `OrphanAdmissible`. -/
theorem pin_box_local_orphan_admissible :
    OrphanAdmissible 2
      { traitOwner := 1
        traitId := 1
        inputs := [.adt 0 2 .fundamental [.adt 0 1 .fundamental [.adt 2 10 .nonFundamental []]]] } := by
  right
  rfl

/-- Concrete witness: `&mut Local` passes `OrphanAdmissible`. -/
theorem ref_mut_local_orphan_admissible :
    OrphanAdmissible 2
      { traitOwner := 1
        traitId := 1
        inputs := [.refTy true (.adt 2 10 .nonFundamental [])] } := by
  right
  rfl

/-- Concrete witness: `Vec<Local>` (`Vec` is `nonFundamental`, owned by crate 0)
is rejected by `OrphanAdmissible` (E0117). -/
theorem vec_local_orphan_rejected :
    ¬ OrphanAdmissible 2
      { traitOwner := 1
        traitId := 1
        inputs := [.adt 0 3 .nonFundamental [.adt 2 10 .nonFundamental []]] } := by
  intro h
  cases h with
  | inl hEq => cases hEq
  | inr hScan => cases hScan

/-- Concrete witness: `impl<T> ForeignTr for Box<T>` fails with `.uncoveredParam` (E0210). -/
theorem box_uncovered_param_rejected :
    orphanScanList 2 [.adt 0 1 .fundamental [.var 0]] = .uncoveredParam :=
  rfl

/-- **Counterexample 2 (`ce2_non_fundamental_wrapper_orphan_conflict`):**
Suppose a broken orphan checker ignores `WrapperKind.nonFundamental` (recursing into
`Vec<Local>` as if `Vec` were fundamental). Because the stdlib crate (`crate 0`) owns
`Vec` and therefore legitimately passes `OrphanAdmissible 0` for
`impl<T> ForeignTr for Vec<T>`, admitting `impl ForeignTr for Vec<Local>` in `crate 2`
produces a direct cross-crate overlap on the ground trait ref `ForeignTr for Vec<Local>`. -/
theorem ce2_non_fundamental_wrapper_orphan_conflict :
    ∃ (stdCrate localCrate foreignCrate : CrateId)
      (trStd trLocal : TraitRefPat)
      (σStd σLocal : Nat → GroundTy),
      stdCrate ≠ localCrate ∧
      trStd.traitOwner = foreignCrate ∧
      trLocal.traitOwner = foreignCrate ∧
      OrphanAdmissible stdCrate trStd ∧
      ¬ OrphanAdmissible localCrate trLocal ∧
      instantiateTraitRef σStd trStd = instantiateTraitRef σLocal trLocal := by
  refine ⟨0, 2, 1,
          { traitOwner := 1, traitId := 7, inputs := [.adt 0 3 .nonFundamental [.var 0]] },
          { traitOwner := 1, traitId := 7, inputs := [.adt 0 3 .nonFundamental [.adt 2 10 .nonFundamental []]] },
          (fun _ => .adt 2 10 .nonFundamental []),
          (fun _ => .adt 2 10 .nonFundamental []),
          ?_, rfl, rfl, ?_, ?_, rfl⟩
  · intro h; cases h
  · right; rfl
  · intro h
    cases h with
    | inl hEq => cases hEq
    | inr hScan => cases hScan

/-!
## Part 3: Lifetime-Erasure-Invariant Specialization Soundness (`min_specialization`),
## `#[marker]` Empty-Item Coherence, and Negative-Coherence Disjointness
-/

/-- Region identifiers in surface Rust types (`'static` vs. local/non-static lifetimes). -/
inductive Region where
  | staticR
  | local (id : Nat)

/-- Explicit structural equality on `Region` (avoiding `deriving DecidableEq` so
zero `._unsafe_rec` compiler helpers are synthesized). -/
noncomputable def Region.beq : Region → Region → Bool
  | .staticR, .staticR => true
  | .local a, .local b => Nat.beq a b
  | _, _ => false

/-- Surface Rust types carrying explicit region annotations prior to monomorphization. -/
inductive RegionTy where
  | u8Ty
  | u32Ty
  | refTy (r : Region) (inner : RegionTy)
  | pair (fst snd : RegionTy)

/-- Region-erased MIR/monomorphization types (`Trusted.MirAst.MirTy` erases regions). -/
inductive ErasedTy where
  | u8Ty
  | u32Ty
  | refTy (inner : ErasedTy)
  | pair (fst snd : ErasedTy)

/-- Region erasure homomorphism from surface types to monomorphized types. -/
noncomputable def eraseRegions : RegionTy → ErasedTy
  | .u8Ty => .u8Ty
  | .u32Ty => .u32Ty
  | .refTy _ inner => .refTy (eraseRegions inner)
  | .pair a b => .pair (eraseRegions a) (eraseRegions b)

/-- Implementation identifier returned by trait selection / monomorphization dispatch. -/
abbrev ImplId := Nat

/-- Surface-level specialization rule (may inspect surface regions if unchecked). -/
structure SurfaceSpecRule where
  implId : ImplId
  matchTy : RegionTy → Bool

/-- Select the first (most specific, ordered child-before-parent) matching impl from
a specialization chain, falling back to `defaultImpl`. -/
noncomputable def selectSurface (rules : List SurfaceSpecRule) (defaultImpl : ImplId) (t : RegionTy) : ImplId :=
  match rules with
  | [] => defaultImpl
  | r :: rs => if r.matchTy t then r.implId else selectSurface rs defaultImpl t

/-- Erased-type linear pattern representing `min_specialization`-admissible concrete
or wildcard specialization headers (no `'static`, no region equality, no repeated
type parameters). -/
inductive ErasedSpecPat where
  | any
  | u8Ty
  | u32Ty
  | refTy (inner : ErasedSpecPat)
  | pair (fst snd : ErasedSpecPat)

/-- Matching a lifetime-free `ErasedSpecPat` against a region-erased type. -/
noncomputable def matchErasedPat : ErasedSpecPat → ErasedTy → Bool
  | .any, _ => true
  | .u8Ty, .u8Ty => true
  | .u32Ty, .u32Ty => true
  | .refTy p, .refTy t => matchErasedPat p t
  | .pair p₁ p₂, .pair t₁ t₂ => matchErasedPat p₁ t₁ && matchErasedPat p₂ t₂
  | _, _ => false

/-- A `min_specialization`-admissible rule matches solely via `ErasedSpecPat`. -/
structure MinSpecRule where
  implId : ImplId
  pat : ErasedSpecPat

/-- Compile a `MinSpecRule` into its surface matcher by erasing regions first. -/
noncomputable def MinSpecRule.toSurface (r : MinSpecRule) : SurfaceSpecRule :=
  { implId := r.implId, matchTy := fun t => matchErasedPat r.pat (eraseRegions t) }

/-- Map a list of `MinSpecRule`s to surface rules without calling library `List.map`
(keeping zero auxiliary `._unsafe_rec` helpers). -/
noncomputable def toSurfaceRules : List MinSpecRule → List SurfaceSpecRule
  | [] => []
  | r :: rs => r.toSurface :: toSurfaceRules rs

/-- Post-erasure monomorphization dispatch operating strictly on `ErasedTy`. -/
noncomputable def selectErased (rules : List MinSpecRule) (defaultImpl : ImplId) (et : ErasedTy) : ImplId :=
  match rules with
  | [] => defaultImpl
  | r :: rs => if matchErasedPat r.pat et then r.implId else selectErased rs defaultImpl et

/-- **Theorem 3 (Lifetime-Free Specialization Determinism Under Region Erasure):**
For every `min_specialization`-admissible specialization chain `rules`, surface-level
dispatch commutes identically with region erasure into post-erasure monomorphization
dispatch. -/
theorem lifetime_free_specialization_commutes_with_erasure
    (rules : List MinSpecRule) (defaultImpl : ImplId) (t : RegionTy) :
    selectSurface (toSurfaceRules rules) defaultImpl t =
      selectErased rules defaultImpl (eraseRegions t) := by
  induction rules with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [toSurfaceRules, selectSurface, selectErased, MinSpecRule.toSurface]
    rw [ih]

/-- Corollary: any two surface types with the same region-erased monomorphized type
dispatch to the exact same implementation under `min_specialization`. -/
theorem min_specialization_monomorphization_deterministic
    (rules : List MinSpecRule) (defaultImpl : ImplId) (t₁ t₂ : RegionTy)
    (hErase : eraseRegions t₁ = eraseRegions t₂) :
    selectSurface (toSurfaceRules rules) defaultImpl t₁ =
      selectSurface (toSurfaceRules rules) defaultImpl t₂ := by
  rw [lifetime_free_specialization_commutes_with_erasure,
      lifetime_free_specialization_commutes_with_erasure,
      hErase]

/-- **Counterexample 1 (`ce1_lifetime_specialization_unsound_after_region_erasure`):**
Specializing on `'static` (`impl<T> BadSpec for T` overridden by
`impl<T: 'static> BadSpec for T`, modeled via `&'static u8` vs. `&'local u8`) produces
two surface types with identical region-erased representations that select different
implementations; therefore NO post-erasure monomorphization selector `f : ErasedTy → ImplId`
can soundly implement surface dispatch. -/
theorem ce1_lifetime_specialization_unsound_after_region_erasure :
    let badStaticRule : SurfaceSpecRule :=
      { implId := 1
        matchTy := fun t =>
          match t with
          | .refTy .staticR _ => true
          | _ => false }
    let tStatic : RegionTy := .refTy .staticR .u8Ty
    let tLocal : RegionTy := .refTy (.local 0) .u8Ty
    eraseRegions tStatic = eraseRegions tLocal ∧
    selectSurface [badStaticRule] 0 tStatic ≠ selectSurface [badStaticRule] 0 tLocal ∧
    ¬ ∃ f : ErasedTy → ImplId, ∀ t : RegionTy, f (eraseRegions t) = selectSurface [badStaticRule] 0 t := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h; cases h
  · rintro ⟨f, hf⟩
    have h₁ : f (.refTy .u8Ty) = 1 := hf (.refTy .staticR .u8Ty)
    have h₂ : f (.refTy .u8Ty) = 0 := hf (.refTy (.local 0) .u8Ty)
    have hEq : (1 : ImplId) = 0 := h₁.symm.trans h₂
    cases hEq

/-- Companion to Counterexample 1: equal-lifetime specialization
(`impl<'a> SameLt for (&'a u8, &'a u8)` over `impl<'a, 'b> SameLt for (&'a u8, &'b u8)`)
likewise fails to factor through region erasure. -/
theorem ce1b_equal_lifetime_specialization_unsound_after_region_erasure :
    let sameLtRule : SurfaceSpecRule :=
      { implId := 1
        matchTy := fun t =>
          match t with
          | .pair (.refTy r₁ .u8Ty) (.refTy r₂ .u8Ty) => Region.beq r₁ r₂
          | _ => false }
    let pSame : RegionTy := .pair (.refTy (.local 0) .u8Ty) (.refTy (.local 0) .u8Ty)
    let pDiff : RegionTy := .pair (.refTy (.local 0) .u8Ty) (.refTy (.local 1) .u8Ty)
    eraseRegions pSame = eraseRegions pDiff ∧
    selectSurface [sameLtRule] 0 pSame ≠ selectSurface [sameLtRule] 0 pDiff ∧
    ¬ ∃ f : ErasedTy → ImplId, ∀ t : RegionTy, f (eraseRegions t) = selectSurface [sameLtRule] 0 t := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h; cases h
  · rintro ⟨f, hf⟩
    have h₁ : f (.pair (.refTy .u8Ty) (.refTy .u8Ty)) = 1 :=
      hf (.pair (.refTy (.local 0) .u8Ty) (.refTy (.local 0) .u8Ty))
    have h₂ : f (.pair (.refTy .u8Ty) (.refTy .u8Ty)) = 0 :=
      hf (.pair (.refTy (.local 0) .u8Ty) (.refTy (.local 1) .u8Ty))
    have hEq : (1 : ImplId) = 0 := h₁.symm.trans h₂
    cases hEq

/-- Trait implementation model for `#[marker]` traits carrying an associated item
payload of type `ItemPayload` (`Unit` when zero associated items, `Nat` when an
associated constant `const X: u32` is illicitly permitted). -/
structure MarkerImpl (Ty : Type) (ItemPayload : Type) where
  applies : Ty → Prop
  itemVal : ItemPayload

/-- When a `#[marker]` trait obeys E0714 (zero associated items, modeled by `Unit`),
overlapping blanket impls are trivially coherent: any two applicable impls agree on
every observable associated item value. -/
theorem marker_empty_overlap_coherent {Ty : Type}
    (i₁ i₂ : MarkerImpl Ty Unit) (t : Ty)
    (_h₁ : i₁.applies t) (_h₂ : i₂.applies t) :
    i₁.itemVal = i₂.itemVal := by
  cases i₁.itemVal
  cases i₂.itemVal
  rfl

/-- **Counterexample 3 (`ce3_marker_trait_with_assoc_const_ambiguous_dispatch`):**
If a `#[marker]` trait permits an associated constant (`const X: u32`, violating
`E0714`), overlapping blanket impls (`Copy` returning `1` and `Clone` returning `2`)
both apply to `u32` yet assign distinct values, breaking coherent associated-item
dispatch. -/
theorem ce3_marker_trait_with_assoc_const_ambiguous_dispatch :
    let isCopy : ErasedTy → Prop := fun t => t = .u32Ty ∨ t = .u8Ty
    let isClone : ErasedTy → Prop := fun t => t = .u32Ty ∨ t = .u8Ty ∨ t = .refTy .u8Ty
    let implCopy : MarkerImpl ErasedTy Nat := { applies := isCopy, itemVal := 1 }
    let implClone : MarkerImpl ErasedTy Nat := { applies := isClone, itemVal := 2 }
    ∃ t : ErasedTy,
      implCopy.applies t ∧ implClone.applies t ∧ implCopy.itemVal ≠ implClone.itemVal := by
  refine ⟨.u32Ty, Or.inl rfl, Or.inl rfl, ?_⟩
  intro h
  cases h

/-- Negative-coherence disjointness lemma (`with_negative_coherence`):
If `impl₁` requires `ImplementsAuto neg .send t` and `impl₂` applies only to
`NoSend` (which carries `neg noSendId .send = true`), then no type `t` satisfies both
implementations simultaneously. -/
theorem negative_coherence_disjoint_impls (noSendId : Nat) :
    let neg : NegImplEnv := fun i a =>
      match Nat.beq i noSendId, a with
      | true, .send => true
      | _, _ => false
    let implSend : TyExpr → Prop := fun t => ImplementsAuto neg .send t
    let implNoSend : TyExpr → Prop := fun t => t = .namedAdt noSendId [.prim]
    ∀ t : TyExpr, ¬ (implSend t ∧ implNoSend t) := by
  intro neg implSend implNoSend t ⟨hSend, hEq⟩
  rw [hEq] at hSend
  exact negative_impl_blocks_send noSendId hSend

end AutoTraitsOrphanSpecialization
