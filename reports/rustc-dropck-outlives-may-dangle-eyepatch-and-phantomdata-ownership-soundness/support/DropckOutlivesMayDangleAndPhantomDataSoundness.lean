/-
Kernel-checked Lean v4.34.1 mechanization of:
  1. `rustc_traits::dropck_outlives::adt_dtorck_constraint` (including `dedup_dtorck_constraint`),
     `TyCtxt::destructor_constraints` (`compiler/rustc_middle/src/ty/util.rs`),
     `trivial_dropck_outlives` & `compute_dropck_outlives_with_errors`
     (`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs`), and
     borrowck drop-liveness (`compiler/rustc_borrowck/src/type_check/liveness/trace.rs`).
  2. `#[may_dangle]` (`dropck_eyepatch`, `pure_wrt_drop`) soundness obligations vs.
     missing-`PhantomData<T>` use-after-free (`UAF`) and variance-only marker gaps.
  3. `Vec<T, A>` / `RawVec<T, A>` / `PhantomData<T>` drop-check restoration and
     allocator-parameter (`A`) vs. element-parameter (`T`) eyepatch separation.
  4. Strict inclusion between conservative RFC 1238 dropck and RFC 1327
     eyepatch + `PhantomData` dropck, plus `ManuallyDrop<T>` triviality boundaries.

Purity & TCB invariants enforced across this module:
  - Pure core Lean 4.34.1 (zero Mathlib, zero external imports).
  - Every `def` is explicitly `noncomputable def` (zero recursive plain `def`,
    zero `noncomputable section`, zero `deriving` clauses on inductives/structures,
    guaranteeing zero `._unsafe_rec` constants).
  - Zero `sorry`, zero `partial def`, zero `omega`, zero `bv_decide`,
    zero `native_decide`, zero `Classical.choice`, zero `Decidable` `ite` branching.
-/

namespace RustcDropckMayDanglePhantomData

/-! ## Section 1: Pure Core Primitives, Region, Type, and Variance Syntax -/

/-- Pure definitional boolean branch without `Decidable` instance synthesis.
`bIf true x y` reduces to `x` and `bIf false x y` reduces to `y` by `rfl`. -/
noncomputable def bIf {α : Sort u} : Bool → α → α → α
  | true, x, _ => x
  | false, _, y => y

/-- A lifetime region modeled at lexical scope level:
- `.rStatic` represents `'static` (live across all stack slots);
- `.rSlot s` represents a region tied to stack slot `s` (dies at `StorageDead(s)`). -/
inductive Region where
  | rStatic : Region
  | rSlot (slot : Nat) : Region

/-- Structural equality on `Nat` without `DecidableEq` deriving. -/
noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => natEq a b
  | _, _ => false

/-- Strict less-than on `Nat` without `Decidable` synthesis. -/
noncomputable def natLt : Nat → Nat → Bool
  | _, 0 => false
  | 0, Nat.succ _ => true
  | Nat.succ a, Nat.succ b => natLt a b

/-- Less-than-or-equal on `Nat` without `Decidable` synthesis. -/
noncomputable def natLe : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLe a b

/-- Structural equality on `Bool`. -/
noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Structural equality on `Region`. -/
noncomputable def regionEq : Region → Region → Bool
  | .rStatic, .rStatic => true
  | .rSlot a, .rSlot b => natEq a b
  | _, _ => false

/-- Unary ADT constructors modeling single-parameter containers and wrappers. -/
inductive Adt1Id where
  | boxed         -- `struct Boxed<T>(T); impl<T> Drop for Boxed<T>` (conservative)
  | plainBox      -- `struct PlainBox<T>(T);` (no `Drop` impl)
  | plainDropRaw  -- `struct PlainDropRaw<T>(*mut T, PhantomData<T>); impl<T> Drop`
  | rawBoxNoPh    -- `struct RawBoxNoPhantom<T>(*mut T); unsafe impl<#[may_dangle] T> Drop`
  | rawBoxFnPh    -- `struct RawBoxFn<T>(*mut T, PhantomData<fn() -> T>); unsafe impl<#[may_dangle] T> Drop`
  | rawBoxWithPh  -- `struct RawBox<T>(*mut T, PhantomData<T>); unsafe impl<#[may_dangle] T> Drop`
  | liarBoxWithPh -- `struct LiarBox<T>(*mut T, PhantomData<T>);` (`#[may_dangle] T` lies and reads `T`)

/-- Binary ADT constructors modeling `(T, A)` generic containers (`Vec`, `RawVec`, `Box`, `BTreeMap`). -/
inductive Adt2Id where
  | rawVec   -- `RawVec<T, A>`: `NonNull<u8>` + `A` + `PhantomData<T>`, `#[may_dangle] T`, impure `A`
  | vec      -- `Vec<T, A>`: `RawVec<T, A>` + `len`, `#[may_dangle] T`, impure `A`
  | stdBox   -- `Box<T, A>`: `NonNull<T>` + `PhantomData<T>` + `A`, `#[may_dangle] T`, impure `A`
  | btreeMap -- `BTreeMap<K, A>`: `ManuallyDrop<A>` + `PhantomData<Box<(K, A)>>`, `#[may_dangle] K`, impure `A`

/-- Region-parameterized ADT constructors (`Inspector<'a>`, `ArenaAlloc<'a>`, `CycleNode<'a>`). -/
inductive RegionAdtId where
  | inspector -- `struct Inspector<'a>(&'a Cell<u32>); impl Drop` (reads `&'a Cell<u32>` in `drop`)
  | arenaRef  -- `struct ArenaAlloc<'a>(&'a Cell<u32>);` (allocator reference used in `Drop` of `Vec<T, A>`)
  | cycleNode -- `struct CycleNode<'a>(&'a Cell<u32>);` (no `Drop` impl)

/-- Core Rust types modeled for dropck, variance, and stack-drop execution.
Every constructor has fixed arity (no nested `List Ty`) so all recursions
compile purely structurally via `Ty.rec` with zero `WellFounded.fix` or `_unsafe_rec`. -/
inductive Ty where
  | prim : Ty
  | cellU32 : Ty
  | ref (r : Region) (isMut : Bool) (pointee : Ty) : Ty
  | rawPtr (isMut : Bool) (pointee : Ty) : Ty
  | fnPtr (arg : Ty) (ret : Ty) : Ty
  | array0 (elem : Ty) : Ty
  | arrayPos (elem : Ty) : Ty
  | pair (fst : Ty) (snd : Ty) : Ty
  | manuallyDrop (inner : Ty) : Ty
  | phantomData (inner : Ty) : Ty
  | adt1 (id : Adt1Id) (elem : Ty) : Ty
  | adt2 (id : Adt2Id) (elem : Ty) (alloc : Ty) : Ty
  | regAdt (id : RegionAdtId) (r : Region) : Ty

/-- The 4-element `rustc_type_ir::Variance` lattice. -/
inductive Variance where
  | bivariant
  | covariant
  | contravariant
  | invariant

/-- Structural equality on `Variance`. -/
noncomputable def varianceEq : Variance → Variance → Bool
  | .bivariant, .bivariant => true
  | .covariant, .covariant => true
  | .contravariant, .contravariant => true
  | .invariant, .invariant => true
  | _, _ => false

/-- `Variance::xform` composition (`compiler/rustc_type_ir/src/lib.rs`). -/
noncomputable def Variance.xform : Variance → Variance → Variance
  | .bivariant, _ => .bivariant
  | .covariant, v => v
  | .contravariant, .bivariant => .bivariant
  | .contravariant, .covariant => .contravariant
  | .contravariant, .contravariant => .covariant
  | .contravariant, .invariant => .invariant
  | .invariant, _ => .invariant

/-- `fn glb` in `compiler/rustc_hir_analysis/src/variance/solve.rs`. -/
noncomputable def Variance.glb : Variance → Variance → Variance
  | .bivariant, v => v
  | v, .bivariant => v
  | .covariant, .covariant => .covariant
  | .contravariant, .contravariant => .contravariant
  | _, _ => .invariant

/-- Type-parameter variance induced by unary wrappers, demonstrating that
`PhantomData<T>` and `PhantomData<fn() -> T>` share identical `.covariant` variance. -/
noncomputable def unaryMarkerVariance : Adt1Id → Variance
  | .boxed => .covariant
  | .plainBox => .covariant
  | .plainDropRaw => .covariant
  | .rawBoxNoPh => .invariant
  | .rawBoxFnPh => .covariant
  | .rawBoxWithPh => .covariant
  | .liarBoxWithPh => .covariant

/-! ## Section 2: `rustc` Drop-Check Model (`destructor_constraints`, `trivial_dropck_outlives`, `adt_dtorck_constraint`) -/

/-- Specification of an ADT's `Drop` implementation and parameter purity (`#[may_dangle]`).
Matches `TyCtxt::destructor_constraints` (`compiler/rustc_middle/src/ty/util.rs:466-538`). -/
structure DropImplMeta where
  hasDrop : Bool
  isUnsafeDropImpl : Bool
  pureWrtDrop0 : Bool  -- `impl_generics.param(0).pure_wrt_drop` (`#[may_dangle]` on param 0)
  pureWrtDrop1 : Bool  -- `impl_generics.param(1).pure_wrt_drop` (`#[may_dangle]` on param 1)

/-- Field-level dropck exposure of an ADT (abstracting `def.all_fields()`). -/
structure AdtFieldMeta where
  hasDirectParam0 : Bool     -- e.g., `struct Boxed<T>(T)`
  hasRawPtrParam0 : Bool     -- e.g., `*mut T` / `NonNull<T>`
  hasPhantomParam0 : Bool    -- e.g., `_marker: PhantomData<T>`
  hasPhantomFnParam0 : Bool  -- e.g., `_marker: PhantomData<fn() -> T>`
  hasDirectParam1 : Bool     -- e.g., `alloc: A` in `RawVec<T, A>`
  hasManuallyDrop1 : Bool    -- e.g., `ManuallyDrop<A>` in `BTreeMap`
  hasPhantomBoxPair : Bool   -- e.g., `PhantomData<Box<(T, A)>>` in `BTreeMap`
  hasDirectRegionRef : Bool  -- e.g., `&'a Cell<u32>` in `Inspector<'a>`

/-- Runtime destructor action independent of static declarations (`DropImplMeta`),
allowing faithful modeling of honest vs. unsound `unsafe impl<#[may_dangle] T> Drop`. -/
structure RuntimeDropAction where
  dropsParam0Elements : Bool   -- calls `ptr::drop_in_place` on owned `T` values
  readsParam0DuringDrop : Bool -- directly reads/dereferences `T` inside `Drop::drop`
  readsParam1DuringDrop : Bool -- invokes/reads `A` (e.g., allocator dealloc) inside `Drop::drop`
  dropsParam1Elements : Bool   -- drops owned `A` values
  readsRegionDirect : Bool     -- dereferences `&'a Cell<u32>` inside its own `Drop::drop`

/-- Complete ADT descriptor combining `DropImplMeta`, `AdtFieldMeta`, and `RuntimeDropAction`. -/
structure AdtDescriptor where
  implMeta : DropImplMeta
  fieldMeta : AdtFieldMeta
  runtime : RuntimeDropAction

/-- Canonical metadata for unary ADTs `Adt1Id`. -/
noncomputable def adt1Descriptor : Adt1Id → AdtDescriptor
  | .boxed => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := false, pureWrtDrop0 := false, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := true, hasRawPtrParam0 := false, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }
  | .plainBox => {
      implMeta := { hasDrop := false, isUnsafeDropImpl := false, pureWrtDrop0 := false, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := true, hasRawPtrParam0 := false, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }
  | .plainDropRaw => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := false, pureWrtDrop0 := false, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := true, hasPhantomParam0 := true,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }
  | .rawBoxNoPh => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := true, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }
  | .rawBoxFnPh => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := true, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := true, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }
  | .rawBoxWithPh => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := true, hasPhantomParam0 := true,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }
  | .liarBoxWithPh => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := true, hasPhantomParam0 := true,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := true, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }

/-- Canonical metadata for binary ADTs `Adt2Id` (`library/alloc/src/{raw_vec,vec,boxed,collections/btree}`). -/
noncomputable def adt2Descriptor : Adt2Id → AdtDescriptor
  | .rawVec => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := false, hasPhantomParam0 := true,
                     hasPhantomFnParam0 := false, hasDirectParam1 := true, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := false, readsParam0DuringDrop := false, readsParam1DuringDrop := true,
                   dropsParam1Elements := true, readsRegionDirect := false }
    }
  | .vec => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := false, hasPhantomParam0 := true,
                     hasPhantomFnParam0 := false, hasDirectParam1 := true, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := true,
                   dropsParam1Elements := true, readsRegionDirect := false }
    }
  | .stdBox => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := true, hasPhantomParam0 := true,
                     hasPhantomFnParam0 := false, hasDirectParam1 := true, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := true,
                   dropsParam1Elements := true, readsRegionDirect := false }
    }
  | .btreeMap => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := true, pureWrtDrop0 := true, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := false, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := true,
                     hasPhantomBoxPair := true, hasDirectRegionRef := false },
      runtime := { dropsParam0Elements := true, readsParam0DuringDrop := false, readsParam1DuringDrop := true,
                   dropsParam1Elements := true, readsRegionDirect := false }
    }

/-- Canonical metadata for region-parameterized ADTs `RegionAdtId`. -/
noncomputable def regAdtDescriptor : RegionAdtId → AdtDescriptor
  | .inspector => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := false, pureWrtDrop0 := false, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := false, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := true },
      runtime := { dropsParam0Elements := false, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := true }
    }
  | .arenaRef => {
      implMeta := { hasDrop := true, isUnsafeDropImpl := false, pureWrtDrop0 := false, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := false, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := true },
      runtime := { dropsParam0Elements := false, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := true }
    }
  | .cycleNode => {
      implMeta := { hasDrop := false, isUnsafeDropImpl := false, pureWrtDrop0 := false, pureWrtDrop1 := false },
      fieldMeta := { hasDirectParam0 := false, hasRawPtrParam0 := false, hasPhantomParam0 := false,
                     hasPhantomFnParam0 := false, hasDirectParam1 := false, hasManuallyDrop1 := false,
                     hasPhantomBoxPair := false, hasDirectRegionRef := true },
      runtime := { dropsParam0Elements := false, readsParam0DuringDrop := false, readsParam1DuringDrop := false,
                   dropsParam1Elements := false, readsRegionDirect := false }
    }

/-- Exact mirror of `rustc_trait_selection::traits::query::dropck_outlives::trivial_dropck_outlives`
(`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:28-95`).
Key distinction: `PhantomData<T>` returns `false` (non-trivial, owns `T`), whereas
`ManuallyDrop<T>`, `&'a T`, `*const T`, `*mut T`, `fn(A) -> R`, and `[T; 0]` return `true`. -/
noncomputable def trivialDropckOutlives : Ty → Bool
  | .prim => true
  | .cellU32 => true
  | .ref _ _ _ => true
  | .rawPtr _ _ => true
  | .fnPtr _ _ => true
  | .array0 _ => true
  | .arrayPos elem => trivialDropckOutlives elem
  | .pair a b => trivialDropckOutlives a && trivialDropckOutlives b
  | .manuallyDrop _ => true
  | .phantomData _ => false
  | .adt1 _ _ => false
  | .adt2 _ _ _ => false
  | .regAdt _ _ => false

/-- Output of `adt_dtorck_constraint` / `dtorck_constraint_for_ty_inner`, splitting
unconditional `outlives` constraints from recursive `dtorckTypes` obligations. -/
structure DropckObligation where
  outlivesRegions : List Region
  dtorckTypes : List Ty

/-- Extract ALL regions syntactically appearing in a `Ty` (used when a type enters `outlives`). -/
noncomputable def collectAllRegions : Ty → List Region
  | .prim => []
  | .cellU32 => []
  | .ref r _ pointee => r :: collectAllRegions pointee
  | .rawPtr _ pointee => collectAllRegions pointee
  | .fnPtr arg ret => collectAllRegions arg ++ collectAllRegions ret
  | .array0 elem => collectAllRegions elem
  | .arrayPos elem => collectAllRegions elem
  | .pair a b => collectAllRegions a ++ collectAllRegions b
  | .manuallyDrop inner => collectAllRegions inner
  | .phantomData inner => collectAllRegions inner
  | .adt1 _ elem => collectAllRegions elem
  | .adt2 _ elem alloc => collectAllRegions elem ++ collectAllRegions alloc
  | .regAdt _ r => [r]

/-- Exact mirror of `TyCtxt::destructor_constraints` (`compiler/rustc_middle/src/ty/util.rs:466-538`).
If `hasDrop = false`, returns `[]`. Otherwise returns every generic parameter NOT marked
`pureWrtDrop` (`#[may_dangle]`). When `ignoreEyepatch = true`, enforces RFC 1238 conservative mode. -/
noncomputable def destructorConstraintRegions
    (ignoreEyepatch : Bool) (dropMeta : DropImplMeta) (args : List Ty) (regArgs : List Region) : List Region :=
  bIf (!dropMeta.hasDrop) []
    (let r0 :=
      match args with
      | a0 :: _ => bIf (ignoreEyepatch || !dropMeta.pureWrtDrop0) (collectAllRegions a0) []
      | [] => []
     let r1 :=
      match args with
      | _ :: a1 :: _ => bIf (ignoreEyepatch || !dropMeta.pureWrtDrop1) (collectAllRegions a1) []
      | _ => []
     let rr :=
      match regArgs with
      | r :: _ => bIf (ignoreEyepatch || !dropMeta.pureWrtDrop0) [r] []
      | [] => []
     r0 ++ r1 ++ rr)

/-- Exact mirror of `adt_dtorck_constraint` (`compiler/rustc_traits/src/dropck_outlives.rs:32-65`)
composed with `dtorck_constraint_for_ty_inner` (`query/dropck_outlives.rs:258-427`) on one unary ADT step. -/
noncomputable def adt1DtorckConstraint (ignoreEyepatch : Bool) (id : Adt1Id) (elem : Ty) : DropckObligation :=
  let desc := adt1Descriptor id
  let fieldDtorck : List Ty :=
    bIf desc.fieldMeta.hasDirectParam0 [elem] [] ++
    bIf desc.fieldMeta.hasRawPtrParam0 [.rawPtr true elem] [] ++
    bIf desc.fieldMeta.hasPhantomParam0 [.phantomData elem] [] ++
    bIf desc.fieldMeta.hasPhantomFnParam0 [.phantomData (.fnPtr .prim elem)] []
  let dtorOutlives := destructorConstraintRegions ignoreEyepatch desc.implMeta [elem] []
  { outlivesRegions := dtorOutlives, dtorckTypes := fieldDtorck }

/-- `adt_dtorck_constraint` for binary ADTs (`Vec<T, A>`, `RawVec<T, A>`, `Box<T, A>`, `BTreeMap<K, A>`). -/
noncomputable def adt2DtorckConstraint (ignoreEyepatch : Bool) (id : Adt2Id) (elem alloc : Ty) : DropckObligation :=
  let desc := adt2Descriptor id
  let fieldDtorck : List Ty :=
    bIf desc.fieldMeta.hasRawPtrParam0 [.rawPtr true elem] [] ++
    bIf desc.fieldMeta.hasPhantomParam0 [.phantomData elem] [] ++
    bIf desc.fieldMeta.hasDirectParam1 [alloc] [] ++
    bIf desc.fieldMeta.hasManuallyDrop1 [.manuallyDrop alloc] [] ++
    bIf desc.fieldMeta.hasPhantomBoxPair [.phantomData (.pair elem alloc)] []
  let dtorOutlives := destructorConstraintRegions ignoreEyepatch desc.implMeta [elem, alloc] []
  { outlivesRegions := dtorOutlives, dtorckTypes := fieldDtorck }

/-- `adt_dtorck_constraint` for region-parameterized ADTs (`Inspector<'a>`, `ArenaAlloc<'a>`, `CycleNode<'a>`). -/
noncomputable def regAdtDtorckConstraint (ignoreEyepatch : Bool) (id : RegionAdtId) (r : Region) : DropckObligation :=
  let desc := regAdtDescriptor id
  let fieldDtorck : List Ty :=
    bIf desc.fieldMeta.hasDirectRegionRef [.ref r false .cellU32] []
  let dtorOutlives := destructorConstraintRegions ignoreEyepatch desc.implMeta [] [r]
  { outlivesRegions := dtorOutlives, dtorckTypes := fieldDtorck }

/-- Single-step `dtorck_constraint_for_ty_inner` (`query/dropck_outlives.rs:258-427`),
including `adt_dtorck_constraint` handling of `PhantomData<T>` (`traits/dropck_outlives.rs:40-52`). -/
noncomputable def tyDtorckStep (ignoreEyepatch : Bool) (t : Ty) : DropckObligation :=
  bIf (trivialDropckOutlives t)
    { outlivesRegions := [], dtorckTypes := [] }
    (match t with
     | .arrayPos elem => { outlivesRegions := [], dtorckTypes := [elem] }
     | .pair a b => { outlivesRegions := [], dtorckTypes := [a, b] }
     | .phantomData inner => { outlivesRegions := [], dtorckTypes := [inner] }
     | .adt1 id elem => adt1DtorckConstraint ignoreEyepatch id elem
     | .adt2 id elem alloc => adt2DtorckConstraint ignoreEyepatch id elem alloc
     | .regAdt id r => regAdtDtorckConstraint ignoreEyepatch id r
     | _ => { outlivesRegions := [], dtorckTypes := [] })

/-- Region-liveness predicate over an explicit `List Region`. -/
noncomputable def allRegionsLive (regionLive : Region → Bool) : List Region → Bool
  | [] => true
  | r :: rs => regionLive r && allRegionsLive regionLive rs

/-- Region membership check (mirrors `FxHashSet` membership in `dedup_dtorck_constraint`). -/
noncomputable def regionInList (r : Region) : List Region → Bool
  | [] => false
  | x :: xs => regionEq r x || regionInList r xs

/-- Order-preserving deduplication of regions (mirrors `dedup_dtorck_constraint`,
`compiler/rustc_traits/src/dropck_outlives.rs:67-73`). -/
noncomputable def dedupRegionsAcc (seen : List Region) : List Region → List Region
  | [] => []
  | r :: rs =>
    bIf (regionInList r seen)
      (dedupRegionsAcc seen rs)
      (r :: dedupRegionsAcc (r :: seen) rs)

noncomputable def dedupRegions (rs : List Region) : List Region :=
  dedupRegionsAcc [] rs

/-- Exact structural recursive evaluation of `DropckOutlives(t)` at a drop point:
1. If `trivialDropckOutlives t` is `true`, returns `true` (zero obligations).
2. Otherwise requires `destructorConstraints` (`outlivesRegions`) to be live AND
   recursively checks every type pushed onto `dtorckTypes`. -/
noncomputable def dropckTyAccepts (ignoreEyepatch : Bool) (regionLive : Region → Bool) : Ty → Bool
  | .prim => true
  | .cellU32 => true
  | .ref _ _ _ => true
  | .rawPtr _ _ => true
  | .fnPtr _ _ => true
  | .array0 _ => true
  | .arrayPos elem => dropckTyAccepts ignoreEyepatch regionLive elem
  | .pair a b =>
    dropckTyAccepts ignoreEyepatch regionLive a &&
    dropckTyAccepts ignoreEyepatch regionLive b
  | .manuallyDrop _ => true
  | .phantomData inner => dropckTyAccepts ignoreEyepatch regionLive inner
  | .adt1 id elem =>
    let desc := adt1Descriptor id
    let outlivesOk :=
      allRegionsLive regionLive (destructorConstraintRegions ignoreEyepatch desc.implMeta [elem] [])
    let directOk := bIf desc.fieldMeta.hasDirectParam0 (dropckTyAccepts ignoreEyepatch regionLive elem) true
    let phOk := bIf desc.fieldMeta.hasPhantomParam0 (dropckTyAccepts ignoreEyepatch regionLive elem) true
    outlivesOk && directOk && phOk
  | .adt2 id elem alloc =>
    let desc := adt2Descriptor id
    let outlivesOk :=
      allRegionsLive regionLive (destructorConstraintRegions ignoreEyepatch desc.implMeta [elem, alloc] [])
    let phOk := bIf desc.fieldMeta.hasPhantomParam0 (dropckTyAccepts ignoreEyepatch regionLive elem) true
    let allocOk := bIf desc.fieldMeta.hasDirectParam1 (dropckTyAccepts ignoreEyepatch regionLive alloc) true
    let phPairOk :=
      bIf desc.fieldMeta.hasPhantomBoxPair
        (dropckTyAccepts ignoreEyepatch regionLive elem && dropckTyAccepts ignoreEyepatch regionLive alloc)
        true
    outlivesOk && phOk && allocOk && phPairOk
  | .regAdt id r =>
    let desc := regAdtDescriptor id
    allRegionsLive regionLive (destructorConstraintRegions ignoreEyepatch desc.implMeta [] [r])

/-- Worklist-style `compute_dropck_outlives` (`query/dropck_outlives.rs:108-253`) using explicit
step list evaluation on `List Ty` (structurally bounded by `fuel` and deduplicated). -/
noncomputable def collectObligationsRaw (ignoreEyepatch : Bool) (fuel : Nat) : List Ty → List Region
  | [] => []
  | t :: ts =>
    match fuel with
    | 0 => []
    | Nat.succ fuel' =>
      let ob := tyDtorckStep ignoreEyepatch t
      ob.outlivesRegions ++ collectObligationsRaw ignoreEyepatch fuel' (ob.dtorckTypes ++ ts)

noncomputable def collectObligationsList (ignoreEyepatch : Bool) (fuel : Nat) (ts : List Ty) : List Region :=
  dedupRegions (collectObligationsRaw ignoreEyepatch fuel ts)

/-! ## Section 3: Stack-Scope Operational Semantics (`StorageDead` Before Reverse `Drop`) -/

/-- A runtime value held in a stack slot or heap allocation. -/
inductive RVal where
  | scalar (n : Nat) : RVal
  | cell (n : Nat) : RVal
  | slotRef (target : Nat) : RVal
  | rawPtrTo (target : Nat) : RVal
  | fnPtrVal : RVal
  | array0Val : RVal
  | arrayPosVal (elem : RVal) : RVal
  | pairVal (fst : RVal) (snd : RVal) : RVal
  | manuallyDropVal (inner : RVal) : RVal
  | phantomVal : RVal
  | boxVal (id : Adt1Id) (payload : RVal) : RVal
  | container2Val (id : Adt2Id) (elemPayload : RVal) (allocPayload : RVal) : RVal
  | regObj (id : RegionAdtId) (target : Nat) : RVal

/-- Result of executing a drop or scope teardown. -/
inductive DropOutcome where
  | ok : DropOutcome
  | ubDanglingRead (deadSlot : Nat) : DropOutcome

/-- Combine two sequential drop outcomes (preserving the first UAF witness). -/
noncomputable def seqOutcome : DropOutcome → DropOutcome → DropOutcome
  | .ok, o2 => o2
  | .ubDanglingRead s, _ => .ubDanglingRead s

/-- Structural equality on `DropOutcome`. -/
noncomputable def outcomeEq : DropOutcome → DropOutcome → Bool
  | .ok, .ok => true
  | .ubDanglingRead a, .ubDanglingRead b => natEq a b
  | _, _ => false

/-- Observe (dereference/read) a runtime value while `live : Nat → Bool` tracks
which stack slots have NOT yet executed `StorageDead`. -/
noncomputable def observeRVal (live : Nat → Bool) : RVal → DropOutcome
  | .scalar _ => .ok
  | .cell _ => .ok
  | .slotRef target => bIf (live target) .ok (.ubDanglingRead target)
  | .rawPtrTo _ => .ok
  | .fnPtrVal => .ok
  | .array0Val => .ok
  | .arrayPosVal e => observeRVal live e
  | .pairVal a b => seqOutcome (observeRVal live a) (observeRVal live b)
  | .manuallyDropVal _ => .ok
  | .phantomVal => .ok
  | .boxVal _ payload => observeRVal live payload
  | .container2Val _ elem alloc => seqOutcome (observeRVal live elem) (observeRVal live alloc)
  | .regObj _ target => bIf (live target) .ok (.ubDanglingRead target)

/-- Execute runtime `Drop::drop` + structural field drop glue on a single `RVal` under slot
liveness map `live : Nat → Bool`. -/
noncomputable def dropRVal (live : Nat → Bool) : RVal → DropOutcome
  | .scalar _ => .ok
  | .cell _ => .ok
  | .slotRef _ => .ok
  | .rawPtrTo _ => .ok
  | .fnPtrVal => .ok
  | .array0Val => .ok
  | .arrayPosVal e => dropRVal live e
  | .pairVal a b => seqOutcome (dropRVal live a) (dropRVal live b)
  | .manuallyDropVal _ => .ok
  | .phantomVal => .ok
  | .boxVal id payload =>
    let desc := adt1Descriptor id
    let readStep := bIf desc.runtime.readsParam0DuringDrop (observeRVal live payload) .ok
    let elemDropStep := bIf desc.runtime.dropsParam0Elements (dropRVal live payload) .ok
    seqOutcome readStep elemDropStep
  | .container2Val id elem alloc =>
    let desc := adt2Descriptor id
    let read0 := bIf desc.runtime.readsParam0DuringDrop (observeRVal live elem) .ok
    let read1 := bIf desc.runtime.readsParam1DuringDrop (observeRVal live alloc) .ok
    let drop0 := bIf desc.runtime.dropsParam0Elements (dropRVal live elem) .ok
    let drop1 := bIf desc.runtime.dropsParam1Elements (dropRVal live alloc) .ok
    seqOutcome (seqOutcome read0 read1) (seqOutcome drop0 drop1)
  | .regObj id target =>
    let desc := regAdtDescriptor id
    bIf desc.runtime.readsRegionDirect
      (bIf (live target) .ok (.ubDanglingRead target))
      .ok

/-- A lexical scope slot binding `declIdx` with static type `ty` and runtime value `val`. -/
structure ScopeSlot where
  ty : Ty
  val : RVal

/-- Region liveness at the drop point of stack slot `k`. -/
noncomputable def regionLiveAtDrop (k : Nat) : Region → Bool
  | .rStatic => true
  | .rSlot target => natLt target k

/-- Runtime slot liveness right before `drop(slot k)` runs (`StorageDead(j)` has already
fired for every `j > k`, and self-borrows cannot be read once `k` enters drop). -/
noncomputable def slotLiveDuringDrop (k : Nat) (target : Nat) : Bool :=
  natLt target k

/-- Lookup element `k` in a `List ScopeSlot`. -/
noncomputable def getSlot? : List ScopeSlot → Nat → Option ScopeSlot
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: ss, Nat.succ k => getSlot? ss k

/-- Execute reverse-declaration-order drops for slots `[n-1, n-2, ..., 0]`. -/
noncomputable def execReverseFrom (slots : List ScopeSlot) : Nat → DropOutcome
  | 0 => .ok
  | Nat.succ k =>
    let stepOutcome :=
      match getSlot? slots k with
      | none => .ok
      | some slot => dropRVal (slotLiveDuringDrop k) slot.val
    seqOutcome stepOutcome (execReverseFrom slots k)

/-- Run full scope teardown for `slots` in Rust reverse declaration order. -/
noncomputable def execReverseScope (slots : List ScopeSlot) : DropOutcome :=
  execReverseFrom slots slots.length

/-- Run `rustc` dropck across all slots `0 .. slots.length - 1`. -/
noncomputable def checkDropckFrom (ignoreEyepatch : Bool) (slots : List ScopeSlot) : Nat → Bool
  | 0 => true
  | Nat.succ k =>
    let slotOk :=
      match getSlot? slots k with
      | none => true
      | some slot => dropckTyAccepts ignoreEyepatch (regionLiveAtDrop k) slot.ty
    slotOk && checkDropckFrom ignoreEyepatch slots k

/-- Top-level dropck verdict for a scope under either RFC 1327 (`ignoreEyepatch = false`)
or conservative RFC 1238 (`ignoreEyepatch = true`). -/
noncomputable def dropckAcceptsScope (ignoreEyepatch : Bool) (slots : List ScopeSlot) : Bool :=
  checkDropckFrom ignoreEyepatch slots slots.length

/-! ## Section 4: Type-Value Compatibility & Soundness Conditions -/

/-- Well-typedness relation linking runtime values `RVal` to static stack-slot types `Ty`. -/
inductive ValTyped : RVal → Ty → Prop where
  | scalar : ∀ n, ValTyped (.scalar n) .prim
  | cell : ∀ n, ValTyped (.cell n) .cellU32
  | refSlot : ∀ target m inner, ValTyped (.slotRef target) (.ref (.rSlot target) m inner)
  | rawPtr : ∀ target m inner, ValTyped (.rawPtrTo target) (.rawPtr m inner)
  | fnPtr : ∀ a r, ValTyped .fnPtrVal (.fnPtr a r)
  | array0 : ∀ e, ValTyped .array0Val (.array0 e)
  | arrayPos : ∀ v e, ValTyped v e → ValTyped (.arrayPosVal v) (.arrayPos e)
  | pair : ∀ v1 v2 t1 t2, ValTyped v1 t1 → ValTyped v2 t2 → ValTyped (.pairVal v1 v2) (.pair t1 t2)
  | manuallyDrop : ∀ v t, ValTyped v t → ValTyped (.manuallyDropVal v) (.manuallyDrop t)
  | phantom : ∀ t, ValTyped .phantomVal (.phantomData t)
  | adt1 : ∀ id v elem, ValTyped v elem → ValTyped (.boxVal id v) (.adt1 id elem)
  | adt2 : ∀ id v1 v2 t1 t2, ValTyped v1 t1 → ValTyped v2 t2 → ValTyped (.container2Val id v1 v2) (.adt2 id t1 t2)
  | regAdt : ∀ id target, ValTyped (.regObj id target) (.regAdt id (.rSlot target))

/-- A unary ADT `id` satisfies `PureWrtDrop` and `PhantomData` ownership honesty. -/
noncomputable def adt1HonestB (id : Adt1Id) : Bool :=
  let d := adt1Descriptor id
  let pureOk :=
    bIf (!d.implMeta.hasDrop || d.implMeta.pureWrtDrop0) (!d.runtime.readsParam0DuringDrop) true
  let ownOk :=
    bIf d.runtime.dropsParam0Elements
      ((!d.implMeta.hasDrop && d.fieldMeta.hasDirectParam0) ||
       (d.implMeta.hasDrop && (!d.implMeta.pureWrtDrop0 || d.fieldMeta.hasDirectParam0 || d.fieldMeta.hasPhantomParam0)))
      true
  pureOk && ownOk

/-- Binary ADT honesty (`Adt2Honest id`), checking both `T` (`param 0`) and `A` (`param 1`). -/
noncomputable def adt2HonestB (id : Adt2Id) : Bool :=
  let d := adt2Descriptor id
  let pure0Ok :=
    bIf (!d.implMeta.hasDrop || d.implMeta.pureWrtDrop0) (!d.runtime.readsParam0DuringDrop) true
  let pure1Ok :=
    bIf (!d.implMeta.hasDrop || d.implMeta.pureWrtDrop1) (!d.runtime.readsParam1DuringDrop) true
  let own0Ok :=
    bIf d.runtime.dropsParam0Elements
      (d.implMeta.hasDrop && (!d.implMeta.pureWrtDrop0 || d.fieldMeta.hasPhantomParam0 || d.fieldMeta.hasPhantomBoxPair))
      true
  let own1Ok :=
    bIf d.runtime.dropsParam1Elements
      (d.implMeta.hasDrop && (!d.implMeta.pureWrtDrop1 || d.fieldMeta.hasDirectParam1 || d.fieldMeta.hasPhantomBoxPair))
      true
  pure0Ok && pure1Ok && own0Ok && own1Ok

/-- Region ADT honesty (`RegAdtHonest id`). -/
noncomputable def regAdtHonestB (id : RegionAdtId) : Bool :=
  let d := regAdtDescriptor id
  bIf d.runtime.readsRegionDirect (d.implMeta.hasDrop && !d.implMeta.pureWrtDrop0) true

/-- Predicate: every ADT constructor occurring inside a type `t` satisfies honesty. -/
noncomputable def tyAdtsHonest : Ty → Bool
  | .prim => true
  | .cellU32 => true
  | .ref _ _ p => tyAdtsHonest p
  | .rawPtr _ p => tyAdtsHonest p
  | .fnPtr a r => tyAdtsHonest a && tyAdtsHonest r
  | .array0 e => tyAdtsHonest e
  | .arrayPos e => tyAdtsHonest e
  | .pair a b => tyAdtsHonest a && tyAdtsHonest b
  | .manuallyDrop _ => true
  | .phantomData i => tyAdtsHonest i
  | .adt1 id e => adt1HonestB id && tyAdtsHonest e
  | .adt2 id e a => adt2HonestB id && tyAdtsHonest e && tyAdtsHonest a
  | .regAdt id _ => regAdtHonestB id

/-- Scope-level well-typedness and honesty invariant across all slots. -/
noncomputable def ScopeWellFormed (slots : List ScopeSlot) : Prop :=
  ∀ k s, getSlot? slots k = some s → ValTyped s.val s.ty ∧ tyAdtsHonest s.ty = true

/-- Scope-level well-typedness alone (even when dishonest `#[may_dangle]` ADTs appear). -/
noncomputable def ScopeTypedOnly (slots : List ScopeSlot) : Prop :=
  ∀ k s, getSlot? slots k = some s → ValTyped s.val s.ty

/-! ## Section 5: Core Structural & Soundness Proofs -/

/-- Helper lemma: `seqOutcome o1 o2 = .ok` iff `o1 = .ok ∧ o2 = .ok`. -/
theorem seqOutcome_eq_ok (o1 o2 : DropOutcome) :
    seqOutcome o1 o2 = .ok ↔ o1 = .ok ∧ o2 = .ok := by
  cases o1 with
  | ok =>
    constructor
    · intro h
      exact ⟨rfl, h⟩
    · intro h
      exact h.2
  | ubDanglingRead s =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.1

/-- Constructive boolean-and characterization without `Classical`. -/
theorem and_eq_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a with
  | false =>
    cases b with
    | false =>
      constructor
      · intro h; cases h
      · intro h; cases h.1
    | true =>
      constructor
      · intro h; cases h
      · intro h; cases h.1
  | true =>
    cases b with
    | false =>
      constructor
      · intro h; cases h
      · intro h; cases h.2
    | true =>
      constructor
      · intro _; exact ⟨rfl, rfl⟩
      · intro _; rfl

/-- Constructive list-append split for `allRegionsLive`. -/
theorem allRegionsLive_append (live : Region → Bool) (xs ys : List Region) :
    allRegionsLive live (xs ++ ys) = true ↔
      allRegionsLive live xs = true ∧ allRegionsLive live ys = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact ⟨rfl, h⟩
    · intro h; exact h.2
  | cons x xs' ih =>
    constructor
    · intro h
      change (live x && allRegionsLive live (xs' ++ ys)) = true at h
      have h1 := (and_eq_true_iff _ _).mp h
      have h2 := ih.mp h1.2
      have hx : allRegionsLive live (x :: xs') = true := by
        change (live x && allRegionsLive live xs') = true
        exact (and_eq_true_iff _ _).mpr ⟨h1.1, h2.1⟩
      exact ⟨hx, h2.2⟩
    · intro h
      have hx := h.1
      change (live x && allRegionsLive live xs') = true at hx
      have h1 := (and_eq_true_iff _ _).mp hx
      have hxy := ih.mpr ⟨h1.2, h.2⟩
      change (live x && allRegionsLive live (xs' ++ ys)) = true
      exact (and_eq_true_iff _ _).mpr ⟨h1.1, hxy⟩

/-- Helper lemma: if `allRegionsLive live (collectAllRegions t) = true`, then
`observeRVal slotLive v = .ok` whenever `ValTyped v t`. -/
theorem observe_ok_of_allRegionsLive (live : Region → Bool) (slotLive : Nat → Bool)
    (h_agree : ∀ s, live (.rSlot s) = true → slotLive s = true)
    (v : RVal) (t : Ty) (ht : ValTyped v t)
    (hl : allRegionsLive live (collectAllRegions t) = true) :
    observeRVal slotLive v = .ok := by
  induction ht with
  | scalar _ => rfl
  | cell _ => rfl
  | refSlot target m inner =>
    have hreg : live (.rSlot target) = true := by
      cases hl1 : live (.rSlot target) with
      | true => rfl
      | false =>
        have hfalse : allRegionsLive live (.rSlot target :: collectAllRegions inner) = false := by
          change (live (.rSlot target) && allRegionsLive live (collectAllRegions inner)) = false
          rw [hl1]
          rfl
        change allRegionsLive live (.rSlot target :: collectAllRegions inner) = true at hl
        rw [hfalse] at hl
        cases hl
    have hslot := h_agree target hreg
    change bIf (slotLive target) DropOutcome.ok (DropOutcome.ubDanglingRead target) = DropOutcome.ok
    rw [hslot]
    rfl
  | rawPtr _ _ _ => rfl
  | fnPtr _ _ => rfl
  | array0 _ => rfl
  | arrayPos v e _ ih => exact ih hl
  | pair v1 v2 t1 t2 _ _ ih1 ih2 =>
    have hsplit := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp hl
    exact (seqOutcome_eq_ok _ _).mpr ⟨ih1 hsplit.1, ih2 hsplit.2⟩
  | manuallyDrop _ _ _ => rfl
  | phantom _ => rfl
  | adt1 id v elem _ ih => exact ih hl
  | adt2 id v1 v2 t1 t2 _ _ ih1 ih2 =>
    have hsplit := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp hl
    exact (seqOutcome_eq_ok _ _).mpr ⟨ih1 hsplit.1, ih2 hsplit.2⟩
  | regAdt id target =>
    change (live (.rSlot target) && true) = true at hl
    have hreg := ((and_eq_true_iff _ _).mp hl).1
    have hslot := h_agree target hreg
    change bIf (slotLive target) DropOutcome.ok (DropOutcome.ubDanglingRead target) = DropOutcome.ok
    rw [hslot]
    rfl

/-- **Theorem 1a (Single-Value Drop-Check No-Dangling-Read Soundness)**:
For any `ignoreEyepatch : Bool`, if `ValTyped v t`, `tyAdtsHonest t = true`, and
`dropckTyAccepts ignoreEyepatch live t = true`, then `dropRVal slotLive v = .ok`. -/
theorem dropRVal_ok_of_dropckAccepts
    (ignoreEyepatch : Bool)
    (live : Region → Bool) (slotLive : Nat → Bool)
    (h_agree : ∀ s, live (.rSlot s) = true → slotLive s = true)
    (v : RVal) (t : Ty) (ht : ValTyped v t)
    (hhon : tyAdtsHonest t = true)
    (hacc : dropckTyAccepts ignoreEyepatch live t = true) :
    dropRVal slotLive v = .ok := by
  induction ht with
  | scalar _ => rfl
  | cell _ => rfl
  | refSlot _ _ _ => rfl
  | rawPtr _ _ _ => rfl
  | fnPtr _ _ => rfl
  | array0 _ => rfl
  | arrayPos v e _ ih => exact ih hhon hacc
  | pair v1 v2 t1 t2 _ _ ih1 ih2 =>
    have hh := (and_eq_true_iff _ _).mp hhon
    have ha := (and_eq_true_iff _ _).mp hacc
    exact (seqOutcome_eq_ok _ _).mpr ⟨ih1 hh.1 ha.1, ih2 hh.2 ha.2⟩
  | manuallyDrop _ _ _ => rfl
  | phantom _ => rfl
  | adt1 id v elem hv ih =>
    have hh := (and_eq_true_iff _ _).mp hhon
    have h_adt := hh.1
    have h_elem_hon := hh.2
    cases id with
    | boxed =>
      cases ignoreEyepatch with
      | false =>
        dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        exact ih h_elem_hon ha2.2
      | true =>
        dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        exact ih h_elem_hon ha2.2
    | plainBox =>
      dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      exact ih h_elem_hon ha2.2
    | plainDropRaw =>
      cases ignoreEyepatch with
      | false =>
        dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        exact ih h_elem_hon ha1.2
      | true =>
        dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        exact ih h_elem_hon ha1.2
    | rawBoxNoPh => cases h_adt
    | rawBoxFnPh => cases h_adt
    | rawBoxWithPh =>
      cases ignoreEyepatch with
      | false =>
        dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        exact ih h_elem_hon ha1.2
      | true =>
        dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        exact ih h_elem_hon ha1.2
    | liarBoxWithPh => cases h_adt
  | adt2 id v1 v2 t1 t2 hv1 hv2 ih1 ih2 =>
    have hh1 := (and_eq_true_iff _ _).mp hhon
    have hh_l := (and_eq_true_iff _ _).mp hh1.1
    have h_e_hon := hh_l.2
    have h_a_hon := hh1.2
    cases id with
    | rawVec =>
      cases ignoreEyepatch with
      | false =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.false_or, List.nil_append, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 ha3.1
        have h_drop_a := ih2 h_a_hon ha2.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, h_drop_a⟩
      | true =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2
        have h_drop_a := ih2 h_a_hon ha2.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, h_drop_a⟩
    | vec =>
      cases ignoreEyepatch with
      | false =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.false_or, List.nil_append, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 ha3.1
        have h_drop_e := ih1 h_e_hon ha3.2
        have h_drop_a := ih2 h_a_hon ha2.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, (seqOutcome_eq_ok _ _).mpr ⟨h_drop_e, h_drop_a⟩⟩
      | true =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2
        have h_drop_e := ih1 h_e_hon ha3.2
        have h_drop_a := ih2 h_a_hon ha2.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, (seqOutcome_eq_ok _ _).mpr ⟨h_drop_e, h_drop_a⟩⟩
    | stdBox =>
      cases ignoreEyepatch with
      | false =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.false_or, List.nil_append, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 ha3.1
        have h_drop_e := ih1 h_e_hon ha3.2
        have h_drop_a := ih2 h_a_hon ha2.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, (seqOutcome_eq_ok _ _).mpr ⟨h_drop_e, h_drop_a⟩⟩
      | true =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2
        have h_drop_e := ih1 h_e_hon ha3.2
        have h_drop_a := ih2 h_a_hon ha2.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, (seqOutcome_eq_ok _ _).mpr ⟨h_drop_e, h_drop_a⟩⟩
    | btreeMap =>
      cases ignoreEyepatch with
      | false =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.false_or, List.nil_append, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have hp := (and_eq_true_iff _ _).mp ha1.2
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 ha3.1
        have h_drop_e := ih1 h_e_hon hp.1
        have h_drop_a := ih2 h_a_hon hp.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, (seqOutcome_eq_ok _ _).mpr ⟨h_drop_e, h_drop_a⟩⟩
      | true =>
        simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
          Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
        have ha1 := (and_eq_true_iff _ _).mp hacc
        have ha2 := (and_eq_true_iff _ _).mp ha1.1
        have ha3 := (and_eq_true_iff _ _).mp ha2.1
        have hp := (and_eq_true_iff _ _).mp ha1.2
        have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
        have h_obs_a := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2
        have h_drop_e := ih1 h_e_hon hp.1
        have h_drop_a := ih2 h_a_hon hp.2
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs_a, (seqOutcome_eq_ok _ _).mpr ⟨h_drop_e, h_drop_a⟩⟩
  | regAdt id target =>
    cases id with
    | inspector =>
      cases ignoreEyepatch <;>
      · dsimp only [dropckTyAccepts, regAdtDescriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
        have ha := (and_eq_true_iff _ _).mp hacc
        have hslot := h_agree target ha.1
        dsimp only [dropRVal, regAdtDescriptor, bIf]
        rw [hslot]
    | arenaRef =>
      cases ignoreEyepatch <;>
      · dsimp only [dropckTyAccepts, regAdtDescriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
        have ha := (and_eq_true_iff _ _).mp hacc
        have hslot := h_agree target ha.1
        dsimp only [dropRVal, regAdtDescriptor, bIf]
        rw [hslot]
    | cycleNode => rfl

/-- Helper lemma: if `allRegionsLive live (collectAllRegions t) = true`, then
`dropRVal slotLive v = .ok` for EVERY well-typed `ValTyped v t` (even with dishonest `#[may_dangle]` ADTs!). -/
theorem dropRVal_ok_of_allRegionsLive (live : Region → Bool) (slotLive : Nat → Bool)
    (h_agree : ∀ s, live (.rSlot s) = true → slotLive s = true)
    (v : RVal) (t : Ty) (ht : ValTyped v t)
    (hl : allRegionsLive live (collectAllRegions t) = true) :
    dropRVal slotLive v = .ok := by
  induction ht with
  | scalar _ => rfl
  | cell _ => rfl
  | refSlot _ _ _ => rfl
  | rawPtr _ _ _ => rfl
  | fnPtr _ _ => rfl
  | array0 _ => rfl
  | arrayPos v e _ ih => exact ih hl
  | pair v1 v2 t1 t2 _ _ ih1 ih2 =>
    have hsplit := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp hl
    exact (seqOutcome_eq_ok _ _).mpr ⟨ih1 hsplit.1, ih2 hsplit.2⟩
  | manuallyDrop _ _ _ => rfl
  | phantom _ => rfl
  | adt1 id v elem hv ih =>
    have h_obs := observe_ok_of_allRegionsLive live slotLive h_agree v elem hv hl
    have h_drop := ih hl
    dsimp only [dropRVal, bIf]
    cases id <;>
    · dsimp only [adt1Descriptor, bIf]
      first | rfl | exact h_drop | exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs, h_drop⟩
  | adt2 id v1 v2 t1 t2 hv1 hv2 ih1 ih2 =>
    have hsplit := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp hl
    have h_obs2 := observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hsplit.2
    have h_drop1 := ih1 hsplit.1
    have h_drop2 := ih2 hsplit.2
    dsimp only [dropRVal, bIf]
    cases id with
    | rawVec =>
      dsimp only [adt2Descriptor, bIf]
      exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs2, h_drop2⟩
    | vec =>
      dsimp only [adt2Descriptor, bIf]
      exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs2, (seqOutcome_eq_ok _ _).mpr ⟨h_drop1, h_drop2⟩⟩
    | stdBox =>
      dsimp only [adt2Descriptor, bIf]
      exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs2, (seqOutcome_eq_ok _ _).mpr ⟨h_drop1, h_drop2⟩⟩
    | btreeMap =>
      dsimp only [adt2Descriptor, bIf]
      exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs2, (seqOutcome_eq_ok _ _).mpr ⟨h_drop1, h_drop2⟩⟩
  | regAdt id target =>
    change (live (.rSlot target) && true) = true at hl
    have hreg := ((and_eq_true_iff _ _).mp hl).1
    have hslot := h_agree target hreg
    dsimp only [dropRVal, bIf]
    cases id with
    | inspector =>
      dsimp only [regAdtDescriptor, bIf]
      rw [hslot]
    | arenaRef =>
      dsimp only [regAdtDescriptor, bIf]
      rw [hslot]
    | cycleNode =>
      dsimp only [regAdtDescriptor, bIf]

/-- **Theorem 1b (Conservative Dropck Protection Even Without `#[may_dangle]` Honesty)**:
Under conservative dropck (`ignoreEyepatch = true`), EVERY ADT with `hasDrop = true` is
checked against `collectAllRegions`, so `dropckTyAccepts true live t = true` implies
`dropRVal slotLive v = .ok` for ALL `ValTyped v t` (even dishonest `#[may_dangle]` impls!). -/
theorem conservative_dropck_protects_even_dishonest_may_dangle
    (live : Region → Bool) (slotLive : Nat → Bool)
    (h_agree : ∀ s, live (.rSlot s) = true → slotLive s = true)
    (v : RVal) (t : Ty) (ht : ValTyped v t)
    (hacc : dropckTyAccepts true live t = true) :
    dropRVal slotLive v = .ok := by
  induction ht with
  | scalar _ => rfl
  | cell _ => rfl
  | refSlot _ _ _ => rfl
  | rawPtr _ _ _ => rfl
  | fnPtr _ _ => rfl
  | array0 _ => rfl
  | arrayPos v e _ ih => exact ih hacc
  | pair v1 v2 t1 t2 _ _ ih1 ih2 =>
    have ha := (and_eq_true_iff _ _).mp hacc
    exact (seqOutcome_eq_ok _ _).mpr ⟨ih1 ha.1, ih2 ha.2⟩
  | manuallyDrop _ _ _ => rfl
  | phantom _ => rfl
  | adt1 id v elem hv ih =>
    cases id with
    | boxed =>
      dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      exact ih ha2.2
    | plainBox =>
      dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      exact ih ha2.2
    | plainDropRaw =>
      dsimp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      exact ih ha1.2
    | rawBoxNoPh =>
      simp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      exact dropRVal_ok_of_allRegionsLive live slotLive h_agree v elem hv ha2.1
    | rawBoxFnPh =>
      simp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      exact dropRVal_ok_of_allRegionsLive live slotLive h_agree v elem hv ha2.1
    | rawBoxWithPh =>
      simp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      exact ih ha1.2
    | liarBoxWithPh =>
      simp only [dropckTyAccepts, adt1Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      have h_obs := observe_ok_of_allRegionsLive live slotLive h_agree v elem hv ha2.1
      have h_drop := dropRVal_ok_of_allRegionsLive live slotLive h_agree v elem hv ha2.1
      exact (seqOutcome_eq_ok _ _).mpr ⟨h_obs, h_drop⟩
  | adt2 id v1 v2 t1 t2 hv1 hv2 ih1 ih2 =>
    cases id with
    | rawVec =>
      simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      have ha3 := (and_eq_true_iff _ _).mp ha2.1
      have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
      exact (seqOutcome_eq_ok _ _).mpr
        ⟨observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2, ih2 ha2.2⟩
    | vec =>
      simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      have ha3 := (and_eq_true_iff _ _).mp ha2.1
      have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
      exact (seqOutcome_eq_ok _ _).mpr
        ⟨observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2,
         (seqOutcome_eq_ok _ _).mpr ⟨ih1 ha3.2, ih2 ha2.2⟩⟩
    | stdBox =>
      simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      have ha3 := (and_eq_true_iff _ _).mp ha2.1
      have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
      exact (seqOutcome_eq_ok _ _).mpr
        ⟨observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2,
         (seqOutcome_eq_ok _ _).mpr ⟨ih1 ha3.2, ih2 ha2.2⟩⟩
    | btreeMap =>
      simp only [dropckTyAccepts, adt2Descriptor, destructorConstraintRegions, bIf,
        Bool.not_true, Bool.not_false, Bool.true_or, List.append_nil] at hacc
      have ha1 := (and_eq_true_iff _ _).mp hacc
      have ha2 := (and_eq_true_iff _ _).mp ha1.1
      have ha3 := (and_eq_true_iff _ _).mp ha2.1
      have hp := (and_eq_true_iff _ _).mp ha1.2
      have hreg := (allRegionsLive_append live (collectAllRegions t1) (collectAllRegions t2)).mp ha3.1
      exact (seqOutcome_eq_ok _ _).mpr
        ⟨observe_ok_of_allRegionsLive live slotLive h_agree v2 t2 hv2 hreg.2,
         (seqOutcome_eq_ok _ _).mpr ⟨ih1 hp.1, ih2 hp.2⟩⟩
  | regAdt id target =>
    cases id with
    | inspector =>
      dsimp only [dropckTyAccepts, regAdtDescriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
      have ha := (and_eq_true_iff _ _).mp hacc
      have hslot := h_agree target ha.1
      dsimp only [dropRVal, regAdtDescriptor, bIf]
      rw [hslot]
    | arenaRef =>
      dsimp only [dropckTyAccepts, regAdtDescriptor, destructorConstraintRegions, allRegionsLive, bIf] at hacc
      have ha := (and_eq_true_iff _ _).mp hacc
      have hslot := h_agree target ha.1
      dsimp only [dropRVal, regAdtDescriptor, bIf]
      rw [hslot]
    | cycleNode => rfl

/-- **Theorem 1c (Full Stack-Scope Drop-Check No-Dangling-Read Theorem)**:
If a lexical stack scope `slots` is well-typed and every `#[may_dangle]` `Drop` impl
satisfies `PureWrtDrop` and declares `PhantomData<T>` for owned dropped `T` (`ScopeWellFormed slots`),
and `dropckAcceptsScope ignoreEyepatch slots = true`, then reverse-declaration-order
execution across the entire scope returns `DropOutcome.ok` (never reads a deallocated stack slot). -/
theorem dropck_accepts_scope_implies_no_dangling_read
    (ignoreEyepatch : Bool) (slots : List ScopeSlot)
    (hwf : ScopeWellFormed slots)
    (hacc : dropckAcceptsScope ignoreEyepatch slots = true) :
    execReverseScope slots = .ok := by
  have helper : ∀ (n : Nat), checkDropckFrom ignoreEyepatch slots n = true →
      execReverseFrom slots n = .ok := by
    intro n hn
    induction n with
    | zero => rfl
    | succ k ih =>
      dsimp only [checkDropckFrom] at hn
      have ha := (and_eq_true_iff _ _).mp hn
      have h_rest := ih ha.2
      dsimp only [execReverseFrom]
      cases hs : getSlot? slots k with
      | none => exact h_rest
      | some slot =>
        have h_ty_hon := hwf k slot hs
        have hk_acc : dropckTyAccepts ignoreEyepatch (regionLiveAtDrop k) slot.ty = true := by
          have ha1 := ha.1
          rw [hs] at ha1
          exact ha1
        have h_agree : ∀ s, regionLiveAtDrop k (.rSlot s) = true → slotLiveDuringDrop k s = true := by
          intro s hs_live
          exact hs_live
        have h_step : dropRVal (slotLiveDuringDrop k) slot.val = .ok :=
          dropRVal_ok_of_dropckAccepts ignoreEyepatch (regionLiveAtDrop k) (slotLiveDuringDrop k)
            h_agree slot.val slot.ty h_ty_hon.1 h_ty_hon.2 hk_acc
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_step, h_rest⟩
  exact helper slots.length hacc

/-- **Theorem 1d (Conservative Scope Corollary without Honesty)**:
Under `ignoreEyepatch = true`, `ScopeTypedOnly slots` + `dropckAcceptsScope true slots = true`
unconditionally implies `execReverseScope slots = .ok`. -/
theorem conservative_dropck_scope_implies_no_dangling_read
    (slots : List ScopeSlot)
    (htyped : ScopeTypedOnly slots)
    (hacc : dropckAcceptsScope true slots = true) :
    execReverseScope slots = .ok := by
  have helper : ∀ (n : Nat), checkDropckFrom true slots n = true →
      execReverseFrom slots n = .ok := by
    intro n hn
    induction n with
    | zero => rfl
    | succ k ih =>
      dsimp only [checkDropckFrom] at hn
      have ha := (and_eq_true_iff _ _).mp hn
      have h_rest := ih ha.2
      dsimp only [execReverseFrom]
      cases hs : getSlot? slots k with
      | none => exact h_rest
      | some slot =>
        have hk_acc : dropckTyAccepts true (regionLiveAtDrop k) slot.ty = true := by
          have ha1 := ha.1
          rw [hs] at ha1
          exact ha1
        have h_agree : ∀ s, regionLiveAtDrop k (.rSlot s) = true → slotLiveDuringDrop k s = true := by
          intro s hs_live
          exact hs_live
        have h_step : dropRVal (slotLiveDuringDrop k) slot.val = .ok :=
          conservative_dropck_protects_even_dishonest_may_dangle
            (regionLiveAtDrop k) (slotLiveDuringDrop k) h_agree slot.val slot.ty (htyped k slot hs) hk_acc
        exact (seqOutcome_eq_ok _ _).mpr ⟨h_step, h_rest⟩
  exact helper slots.length hacc

/-! ## Section 6: Missing-`PhantomData`, Variance-Only Marker, and Liar `#[may_dangle]` UAF Witnesses -/

/-- Scope A1 (Conservative Dropck Rejection):
Slot 0 = `Boxed<&'1 Cell<u32>>`, Slot 1 = `Cell<u32>`. -/
noncomputable def scopeBoxedAfterCell : List ScopeSlot :=
  [ { ty := .adt1 .boxed (.ref (.rSlot 1) false .cellU32),
      val := .boxVal .boxed (.slotRef 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope A2 (Safe Order Control):
Slot 0 = `Cell<u32>`, Slot 1 = `Boxed<&'0 Cell<u32>>`. -/
noncomputable def scopeBoxedBeforeCell : List ScopeSlot :=
  [ { ty := .cellU32, val := .cell 1 },
    { ty := .adt1 .boxed (.ref (.rSlot 0) false .cellU32),
      val := .boxVal .boxed (.slotRef 0) } ]

/-- Scope A3 (No-`Drop` `PlainBox<&'1 Cell<u32>>` Safe Cyclic Order):
Slot 0 = `PlainBox<&'1 Cell<u32>>`, Slot 1 = `Cell<u32>`. -/
noncomputable def scopePlainBoxAfterCell : List ScopeSlot :=
  [ { ty := .adt1 .plainBox (.ref (.rSlot 1) false .cellU32),
      val := .boxVal .plainBox (.slotRef 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope B1 (Missing-`PhantomData<T>` Miri UAF Witness):
Slot 0 = `RawBoxNoPhantom<Inspector<'1>>`, Slot 1 = `Cell<u32>`.
At scope exit, `StorageDead(1)` runs BEFORE `drop(slot 0)`, causing `<Inspector<'_> as Drop>::drop`
to read deallocated slot 1! -/
noncomputable def scopeRawBoxNoPhInspector : List ScopeSlot :=
  [ { ty := .adt1 .rawBoxNoPh (.regAdt .inspector (.rSlot 1)),
      val := .boxVal .rawBoxNoPh (.regObj .inspector 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope B2 (Variance-Only `PhantomData<fn() -> T>` Miri UAF Witness):
Identical `.covariant` variance to `PhantomData<T>`, yet `trivial_dropck_outlives(fn() -> T) = true`. -/
noncomputable def scopeRawBoxFnPhInspector : List ScopeSlot :=
  [ { ty := .adt1 .rawBoxFnPh (.regAdt .inspector (.rSlot 1)),
      val := .boxVal .rawBoxFnPh (.regObj .inspector 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope B3 (`PhantomData<T>` Restores `E0597` Rejection):
`struct RawBox<T>(*mut T, PhantomData<T>); unsafe impl<#[may_dangle] T> Drop`. -/
noncomputable def scopeRawBoxWithPhInspector : List ScopeSlot :=
  [ { ty := .adt1 .rawBoxWithPh (.regAdt .inspector (.rSlot 1)),
      val := .boxVal .rawBoxWithPh (.regObj .inspector 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope B4 (Untruthful `pure_wrt_drop` WITH `PhantomData<T>` on `T = &'1 Cell<u32>`):
`LiarBox` declares `PhantomData<T>` and `#[may_dangle] T`, yet dereferences `T` in `Drop::drop`. -/
noncomputable def scopeLiarBoxWithPhRef : List ScopeSlot :=
  [ { ty := .adt1 .liarBoxWithPh (.ref (.rSlot 1) false .cellU32),
      val := .boxVal .liarBoxWithPh (.slotRef 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- **Theorem 2a**: Plain `impl<T> Drop for Boxed<T>` rejects `scopeBoxedAfterCell` (`E0597`),
accepts/executes `scopeBoxedBeforeCell` cleanly, and `PlainBox` without `Drop` allows `scopePlainBoxAfterCell`. -/
theorem boxed_dropck_rejects_after_accepts_before :
    dropckAcceptsScope false scopeBoxedAfterCell = false ∧
    dropckAcceptsScope false scopeBoxedBeforeCell = true ∧
    execReverseScope scopeBoxedBeforeCell = .ok ∧
    dropckAcceptsScope false scopePlainBoxAfterCell = true ∧
    execReverseScope scopePlainBoxAfterCell = .ok := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 2b (Missing-`PhantomData` Unsoundness Witness)**:
Under `#[may_dangle]` without `PhantomData<T>`, `rustc` dropck ACCEPTS `RawBoxNoPhantom<Inspector<'1>>`
(`collectObligationsList` returns `[]` and `dropckAcceptsScope false scopeRawBoxNoPhInspector = true`),
yet reverse-order scope execution reads deallocated slot 1 (`execReverseScope ... = .ubDanglingRead 1`). -/
theorem missing_phantom_eyepatch_unsound_witness :
    collectObligationsList false 16 [.adt1 .rawBoxNoPh (.regAdt .inspector (.rSlot 1))] = [] ∧
    dropckAcceptsScope false scopeRawBoxNoPhInspector = true ∧
    execReverseScope scopeRawBoxNoPhInspector = .ubDanglingRead 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem 2c (Variance-Only Marker `PhantomData<fn() -> T>` Unsoundness Witness)**:
`RawBoxFn<T>` (`PhantomData<fn() -> T>`) has the EXACT same `.covariant` variance as `RawBox<T>`
(`PhantomData<T>`), yet `trivialDropckOutlives (.fnPtr .prim ...) = true` leaves `dtorck_types` empty,
so `dropckAcceptsScope` returns `true` and `execReverseScope` hits `.ubDanglingRead 1`. -/
theorem phantom_fn_ptr_same_variance_still_unsound_witness :
    unaryMarkerVariance .rawBoxFnPh = unaryMarkerVariance .rawBoxWithPh ∧
    collectObligationsList false 16 [.adt1 .rawBoxFnPh (.regAdt .inspector (.rSlot 1))] = [] ∧
    dropckAcceptsScope false scopeRawBoxFnPhInspector = true ∧
    execReverseScope scopeRawBoxFnPhInspector = .ubDanglingRead 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem 2d (`PhantomData<T>` Restores `E0597` Rejection)**:
Adding `PhantomData<T>` pushes `Inspector<'1>` into `dtorck_types`, yielding `[.rSlot 1]`
in `collectObligationsList` and rejecting `scopeRawBoxWithPhInspector` (`dropckAcceptsScope = false`). -/
theorem phantom_data_restores_rejection_for_inspector :
    collectObligationsList false 16 [.adt1 .rawBoxWithPh (.regAdt .inspector (.rSlot 1))] = [.rSlot 1] ∧
    dropckAcceptsScope false scopeRawBoxWithPhInspector = false := by
  exact ⟨rfl, rfl⟩

/-- **Theorem 2e (Untruthful `#[may_dangle]` Bypasses Even `PhantomData<T>`)**:
When `T = &'1 Cell<u32>` (`trivialDropckOutlives = true`), `PhantomData<T>` drops out of `dtorck_types`,
so if `Drop::drop` violates `pure_wrt_drop` (`LiarBox`), dropck accepts (`true`) yet execution UAFs on slot 1. -/
theorem pure_wrt_drop_liar_with_phantom_unsound_witness :
    collectObligationsList false 16 [.adt1 .liarBoxWithPh (.ref (.rSlot 1) false .cellU32)] = [] ∧
    dropckAcceptsScope false scopeLiarBoxWithPhRef = true ∧
    execReverseScope scopeLiarBoxWithPhRef = .ubDanglingRead 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem 2f (Conservative Mode Catches All Three Eyepatch Holes)**:
When `ignoreEyepatch = true`, `destructorConstraintRegions` ignores `pureWrtDrop` and rejects
all three unsound scopes (`dropckAcceptsScope true ... = false`). -/
theorem conservative_dropck_rejects_all_three_eyepatch_holes :
    dropckAcceptsScope true scopeRawBoxNoPhInspector = false ∧
    dropckAcceptsScope true scopeRawBoxFnPhInspector = false ∧
    dropckAcceptsScope true scopeLiarBoxWithPhRef = false := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 7: `trivial_dropck_outlives` Soundness & `Vec<T, A>` / `RawBox<T>` Restoration -/

/-- **Theorem 3a (General `trivial_dropck_outlives` Drop-Safety Theorem)**:
For ANY type `t : Ty` with `trivialDropckOutlives t = true`, ANY well-typed value `ValTyped v t`,
and ANY runtime slot-liveness function `slotLive : Nat → Bool` (even `fun _ => false` where every
referenced slot has already executed `StorageDead`), `dropRVal slotLive v = .ok`. -/
theorem trivialDropckOutlives_implies_dropRVal_ok
    (slotLive : Nat → Bool) (v : RVal) (t : Ty)
    (ht : ValTyped v t) (htriv : trivialDropckOutlives t = true) :
    dropRVal slotLive v = .ok := by
  induction ht with
  | scalar _ => rfl
  | cell _ => rfl
  | refSlot _ _ _ => rfl
  | rawPtr _ _ _ => rfl
  | fnPtr _ _ => rfl
  | array0 _ => rfl
  | arrayPos v e _ ih => exact ih htriv
  | pair v1 v2 t1 t2 _ _ ih1 ih2 =>
    have hp := (and_eq_true_iff _ _).mp htriv
    exact (seqOutcome_eq_ok _ _).mpr ⟨ih1 hp.1, ih2 hp.2⟩
  | manuallyDrop _ _ _ => rfl
  | phantom _ => cases htriv
  | adt1 _ _ _ _ => cases htriv
  | adt2 _ _ _ _ _ _ _ => cases htriv
  | regAdt _ _ => cases htriv

/-- **Theorem 3b (`&'a Cell<u32>` Triviality Specialization)**:
For every region `r`, mutability `isMut`, and pointee `p`, `trivialDropckOutlives (.ref r isMut p) = true`
and dropping `.slotRef target` returns `.ok` regardless of `slotLive target`. -/
theorem trivial_dropck_outlives_ref_sound (r : Region) (isMut : Bool) (p : Ty)
    (slotLive : Nat → Bool) (target : Nat) :
    trivialDropckOutlives (.ref r isMut p) = true ∧
    dropRVal slotLive (.slotRef target) = .ok := by
  exact ⟨rfl, rfl⟩

/-- Scope C1 (`DROPCK_SAFE=2`: `Vec<&'2 Cell<u32>, Global>` + `RawBox<&'2 Cell<u32>>`):
- Slot 0: `Vec<&'2 Cell<u32>, Global>` (`prim` stands in for stateless `Global` ZST allocator)
- Slot 1: `RawBox<&'2 Cell<u32>>` (`#[may_dangle] T` + `PhantomData<T>`)
- Slot 2: `Cell<u32>` (dropped FIRST at scope exit via `StorageDead(2)`) -/
noncomputable def scopeVecAndRawBoxCellRef : List ScopeSlot :=
  [ { ty := .adt2 .vec (.ref (.rSlot 2) false .cellU32) .prim,
      val := .container2Val .vec (.slotRef 2) (.scalar 0) },
    { ty := .adt1 .rawBoxWithPh (.ref (.rSlot 2) false .cellU32),
      val := .boxVal .rawBoxWithPh (.slotRef 2) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope C2 (`ManuallyDrop<Inspector<'1>>` declared before `Cell`):
`ManuallyDrop<T>` satisfies `trivialDropckOutlives = true` (`query/dropck_outlives.rs:70-72`). -/
noncomputable def scopeManuallyDropInspector : List ScopeSlot :=
  [ { ty := .manuallyDrop (.regAdt .inspector (.rSlot 1)),
      val := .manuallyDropVal (.regObj .inspector 1) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope C3 (RFC 1327 Allocator `A` Un-Eyepatched Rejection Witness):
`Vec<&'1 Cell<u32>, ArenaAlloc<'2>>` where `ArenaAlloc<'2>` borrows `cell_arena` declared AFTER `Vec`. -/
noncomputable def scopeVecBorrowedArenaBefore : List ScopeSlot :=
  [ { ty := .adt2 .vec (.ref (.rSlot 1) false .cellU32) (.regAdt .arenaRef (.rSlot 2)),
      val := .container2Val .vec (.slotRef 1) (.regObj .arenaRef 2) },
    { ty := .cellU32, val := .cell 1 },
    { ty := .cellU32, val := .cell 99 } ]

/-- Scope C4 (RFC 1327 Allocator `A` Declared Before `Vec`, Element `&'2 Cell<u32>` Declared After `Vec`):
`slot 0` = `arena_cell`, `slot 1` = `Vec<&'2 Cell<u32>, ArenaAlloc<'0>>`, `slot 2` = `elem_cell`. -/
noncomputable def scopeVecArenaBeforeElemAfter : List ScopeSlot :=
  [ { ty := .cellU32, val := .cell 99 },
    { ty := .adt2 .vec (.ref (.rSlot 2) false .cellU32) (.regAdt .arenaRef (.rSlot 0)),
      val := .container2Val .vec (.slotRef 2) (.regObj .arenaRef 0) },
    { ty := .cellU32, val := .cell 1 } ]

/-- Scope C5 (`BTreeMap` `ManuallyDrop<A>` + `PhantomData<Box<(K, A)>>` Witness):
`A` is inside `ManuallyDrop<A>` (trivial!) yet protected by `!pureWrtDrop1` + `PhantomData<Box<(K, A)>>`. -/
noncomputable def scopeBTreeArenaAfter : List ScopeSlot :=
  [ { ty := .adt2 .btreeMap (.ref (.rSlot 1) false .cellU32) (.regAdt .arenaRef (.rSlot 2)),
      val := .container2Val .btreeMap (.slotRef 1) (.regObj .arenaRef 2) },
    { ty := .cellU32, val := .cell 1 },
    { ty := .cellU32, val := .cell 99 } ]

noncomputable def scopeBTreeArenaBeforeElemAfter : List ScopeSlot :=
  [ { ty := .cellU32, val := .cell 99 },
    { ty := .adt2 .btreeMap (.ref (.rSlot 2) false .cellU32) (.regAdt .arenaRef (.rSlot 0)),
      val := .container2Val .btreeMap (.slotRef 2) (.regObj .arenaRef 0) },
    { ty := .cellU32, val := .cell 1 } ]

/-- **Theorem 3c (`Vec` + `RawBox + PhantomData` Dangling `&Cell<u32>` Restoration)**:
Both `Vec<&'2 Cell<u32>, Global>` and `RawBox<&'2 Cell<u32>>` are accepted by `dropckAcceptsScope false`,
collect zero obligations (`[]`), and execute cleanly (`execReverseScope = .ok`). -/
theorem vec_and_rawbox_phantom_allow_dangling_cell_ref_sound :
    collectObligationsList false 16 [.adt2 .vec (.ref (.rSlot 2) false .cellU32) .prim] = [] ∧
    collectObligationsList false 16 [.adt1 .rawBoxWithPh (.ref (.rSlot 2) false .cellU32)] = [] ∧
    dropckAcceptsScope false scopeVecAndRawBoxCellRef = true ∧
    execReverseScope scopeVecAndRawBoxCellRef = .ok := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem 3d (`ManuallyDrop<Inspector<'1>>` Triviality Boundary)**:
`ManuallyDrop` short-circuits `trivialDropckOutlives` to `true`, so `dropck` accepts it and
no destructor runs on `Inspector`. -/
theorem manuallyDrop_inspector_trivial_dropck_sound :
    trivialDropckOutlives (.manuallyDrop (.regAdt .inspector (.rSlot 1))) = true ∧
    dropckAcceptsScope false scopeManuallyDropInspector = true ∧
    execReverseScope scopeManuallyDropInspector = .ok := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem 3e (RFC 1327 Asymmetric `#[may_dangle] T, A: Allocator` Separation)**:
- When `ArenaAlloc<'2>` outlives `Vec` (`scopeVecBorrowedArenaBefore` fails), `Vec`'s un-eyepatched `A`
  emits `[.rSlot 2]` (deduplicated via `dedupRegions`) and rejects the scope (`false`).
- When `ArenaAlloc<'0>` is declared BEFORE `Vec` while `&'2 Cell<u32>` is declared AFTER `Vec`
  (`scopeVecArenaBeforeElemAfter`), `Vec` accepts (`true`) and executes without UAF (`.ok`).
- Identical discipline holds for `BTreeMap` (`ManuallyDrop<A>` + un-eyepatched `A`). -/
theorem vec_and_btree_allocator_eyepatch_asymmetry :
    collectObligationsList false 16 [.adt2 .vec (.ref (.rSlot 1) false .cellU32) (.regAdt .arenaRef (.rSlot 2))] = [.rSlot 2] ∧
    dropckAcceptsScope false scopeVecBorrowedArenaBefore = false ∧
    dropckAcceptsScope false scopeVecArenaBeforeElemAfter = true ∧
    execReverseScope scopeVecArenaBeforeElemAfter = .ok ∧
    dropckAcceptsScope false scopeBTreeArenaAfter = false ∧
    dropckAcceptsScope false scopeBTreeArenaBeforeElemAfter = true ∧
    execReverseScope scopeBTreeArenaBeforeElemAfter = .ok := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 8: Strict Inclusion Theorems (Conservative RFC 1238 ⊊ Eyepatch + `PhantomData`) -/

/-- Monotonicity helper: `destructorConstraintRegions false` is a subset of
`destructorConstraintRegions true` (whenever `allRegionsLive` accepts conservative `outlives`,
it also accepts eyepatched `outlives`). -/
theorem allRegionsLive_destructor_mono
    (live : Region → Bool) (dropMeta : DropImplMeta) (args : List Ty) (regArgs : List Region)
    (h : allRegionsLive live (destructorConstraintRegions true dropMeta args regArgs) = true) :
    allRegionsLive live (destructorConstraintRegions false dropMeta args regArgs) = true := by
  rcases dropMeta with ⟨hasDrop, isUnsafe, pure0, pure1⟩
  cases hasDrop with
  | false => exact rfl
  | true =>
    cases pure0 <;> cases pure1 <;>
    · dsimp only [destructorConstraintRegions, bIf] at h ⊢
      have h12 := (allRegionsLive_append live _ _).mp h
      have h1 := (allRegionsLive_append live _ _).mp h12.1
      apply (allRegionsLive_append live _ _).mpr
      constructor
      · apply (allRegionsLive_append live _ _).mpr
        constructor
        · cases args with
          | nil => rfl
          | cons _ _ => first | rfl | exact h1.1
        · cases args with
          | nil => rfl
          | cons _ rest =>
            cases rest with
            | nil => rfl
            | cons _ _ => first | rfl | exact h1.2
      · cases regArgs with
        | nil => rfl
        | cons _ _ => first | rfl | exact h12.2

/-- **Theorem 4a (General Type-Level Inclusion: Conservative ⊆ Eyepatch + `PhantomData`)**:
For EVERY region-liveness map `live : Region → Bool` and EVERY type `t : Ty`,
acceptance under conservative RFC 1238 dropck (`dropckTyAccepts true live t = true`)
implies acceptance under RFC 1327 eyepatch + `PhantomData` (`dropckTyAccepts false live t = true`). -/
theorem conservative_implies_eyepatch_phantom_ty
    (live : Region → Bool) (t : Ty)
    (h : dropckTyAccepts true live t = true) :
    dropckTyAccepts false live t = true := by
  induction t with
  | prim => rfl
  | cellU32 => rfl
  | ref _ _ _ => rfl
  | rawPtr _ _ => rfl
  | fnPtr _ _ => rfl
  | array0 _ => rfl
  | arrayPos elem ih => exact ih h
  | pair a b iha ihb =>
    have ha := (and_eq_true_iff _ _).mp h
    exact (and_eq_true_iff _ _).mpr ⟨iha ha.1, ihb ha.2⟩
  | manuallyDrop _ => rfl
  | phantomData inner ih => exact ih h
  | adt1 id elem ih =>
    dsimp only [dropckTyAccepts] at h ⊢
    have ha1 := (and_eq_true_iff _ _).mp h
    have ha2 := (and_eq_true_iff _ _).mp ha1.1
    have hout := allRegionsLive_destructor_mono live (adt1Descriptor id).implMeta [elem] [] ha2.1
    apply (and_eq_true_iff _ _).mpr
    constructor
    · apply (and_eq_true_iff _ _).mpr
      constructor
      · exact hout
      · cases hfd : (adt1Descriptor id).fieldMeta.hasDirectParam0 with
        | false => rfl
        | true =>
          have h22 := ha2.2
          rw [hfd] at h22
          exact ih h22
    · cases hfp : (adt1Descriptor id).fieldMeta.hasPhantomParam0 with
      | false => rfl
      | true =>
        have h12 := ha1.2
        rw [hfp] at h12
        exact ih h12
  | adt2 id elem alloc ihe iha =>
    dsimp only [dropckTyAccepts] at h ⊢
    have ha1 := (and_eq_true_iff _ _).mp h
    have ha2 := (and_eq_true_iff _ _).mp ha1.1
    have ha3 := (and_eq_true_iff _ _).mp ha2.1
    have hout := allRegionsLive_destructor_mono live (adt2Descriptor id).implMeta [elem, alloc] [] ha3.1
    apply (and_eq_true_iff _ _).mpr
    constructor
    · apply (and_eq_true_iff _ _).mpr
      constructor
      · apply (and_eq_true_iff _ _).mpr
        constructor
        · exact hout
        · cases hfp : (adt2Descriptor id).fieldMeta.hasPhantomParam0 with
          | false => rfl
          | true =>
            have h32 := ha3.2
            rw [hfp] at h32
            exact ihe h32
      · cases hfd : (adt2Descriptor id).fieldMeta.hasDirectParam1 with
        | false => rfl
        | true =>
          have h22 := ha2.2
          rw [hfd] at h22
          exact iha h22
    · cases hfb : (adt2Descriptor id).fieldMeta.hasPhantomBoxPair with
      | false => rfl
      | true =>
        have h12 := ha1.2
        rw [hfb] at h12
        have hp := (and_eq_true_iff _ _).mp h12
        exact (and_eq_true_iff _ _).mpr ⟨ihe hp.1, iha hp.2⟩
  | regAdt id r =>
    dsimp only [dropckTyAccepts] at h ⊢
    exact allRegionsLive_destructor_mono live (regAdtDescriptor id).implMeta [] [r] h

/-- **Theorem 4b (Scope-Level Inclusion: Conservative ⊆ Eyepatch + `PhantomData`)**:
Every lexical scope accepted by conservative dropck (`dropckAcceptsScope true slots = true`)
is also accepted by eyepatch + `PhantomData` dropck (`dropckAcceptsScope false slots = true`). -/
theorem conservative_implies_eyepatch_phantom_scope (slots : List ScopeSlot)
    (h : dropckAcceptsScope true slots = true) :
    dropckAcceptsScope false slots = true := by
  have helper : ∀ (n : Nat), checkDropckFrom true slots n = true →
      checkDropckFrom false slots n = true := by
    intro n hn
    induction n with
    | zero => rfl
    | succ k ih =>
      dsimp only [checkDropckFrom] at hn ⊢
      have ha := (and_eq_true_iff _ _).mp hn
      apply (and_eq_true_iff _ _).mpr
      constructor
      · cases hs : getSlot? slots k with
        | none => rfl
        | some slot =>
          have h1 := ha.1
          rw [hs] at h1
          exact conservative_implies_eyepatch_phantom_ty (regionLiveAtDrop k) slot.ty h1
      · exact ih ha.2
  exact helper slots.length h

/-- **Theorem 4c (Strict Separation Witness: Eyepatch + `PhantomData` ⊋ Conservative)**:
`scopeVecAndRawBoxCellRef` is sound and accepted under `#[may_dangle]` + `PhantomData<T>`,
yet strictly REJECTED under conservative dropck (`dropckAcceptsScope true = false`).
Additionally, `scopeRawBoxWithPhInspector` vs `scopeRawBoxNoPhInspector` strictly separates
eyepatch-with-`PhantomData` from unsound eyepatch-without-`PhantomData`. -/
theorem strict_inclusion_between_dropck_regimes :
    (∀ slots, dropckAcceptsScope true slots = true → dropckAcceptsScope false slots = true) ∧
    (dropckAcceptsScope false scopeVecAndRawBoxCellRef = true ∧
     dropckAcceptsScope true scopeVecAndRawBoxCellRef = false ∧
     execReverseScope scopeVecAndRawBoxCellRef = .ok) ∧
    (dropckAcceptsScope false scopeRawBoxWithPhInspector = false ∧
     dropckAcceptsScope false scopeRawBoxNoPhInspector = true ∧
     execReverseScope scopeRawBoxNoPhInspector = .ubDanglingRead 1) := by
  refine ⟨conservative_implies_eyepatch_phantom_scope, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-! ## Section 9: Variance Algebra & Orthogonal `PhantomData` Marker Separation -/

/-- `Variance.xform` associativity (`compiler/rustc_type_ir/src/lib.rs`). -/
theorem xform_assoc (a b c : Variance) :
    (a.xform b).xform c = a.xform (b.xform c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `Variance.covariant` is the two-sided identity for `Variance.xform`. -/
theorem xform_cov_identity (v : Variance) :
    Variance.covariant.xform v = v ∧ v.xform Variance.covariant = v := by
  cases v <;> exact ⟨rfl, rfl⟩

/-- `Variance.contravariant` is an involution under `Variance.xform`. -/
theorem xform_contra_involutive (v : Variance) :
    Variance.contravariant.xform (Variance.contravariant.xform v) = v := by
  cases v <;> rfl

/-- `Variance.glb` commutativity and idempotence (`variance/solve.rs`). -/
theorem glb_comm_idem (a b : Variance) :
    a.glb b = b.glb a ∧ a.glb a = a := by
  cases a <;> cases b <;> exact ⟨rfl, rfl⟩

/-- **Theorem 5 (Orthogonality of Subtyping Variance and `dropck` Ownership)**:
`RawBox<T>` (with `PhantomData<T>`) and `RawBoxFn<T>` (with `PhantomData<fn() -> T>`)
induce identical `.covariant` variance on `T`, yet `RawBox` rejects dangling `Inspector<'1>`
while `RawBoxFn` admits `Inspector<'1>` into an immediate use-after-free. -/
theorem variance_orthogonal_to_dropck_ownership :
    unaryMarkerVariance .rawBoxWithPh = .covariant ∧
    unaryMarkerVariance .rawBoxFnPh = .covariant ∧
    dropckAcceptsScope false scopeRawBoxWithPhInspector = false ∧
    dropckAcceptsScope false scopeRawBoxFnPhInspector = true ∧
    execReverseScope scopeRawBoxFnPhInspector = .ubDanglingRead 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RustcDropckMayDanglePhantomData
