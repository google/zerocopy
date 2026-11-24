/-
Copyright 2026 The Fuchsia Authors

Licensed under the BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# System V AMD64 Eightbyte Classification, `PassMode` Lowering, Register-Bank
# Exhaustion Rollback, and `i128` Alignment Soundness (Lean v4.34.1)

Self-contained kernel-checked formalization of the `x86_64-unknown-linux-gnu`
System V AMD64 `extern "C"` ABI pipeline in `rust-lang/rust`:
- `compiler/rustc_target/src/callconv/x86_64.rs`
- `compiler/rustc_target/src/callconv/mod.rs`
- `compiler/rustc_codegen_llvm/src/abi.rs`
- `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs`
- `compiler/rustc_abi/src/{lib.rs, layout.rs}`

## Purity and Trust-Boundary Guarantees
- Standalone Lean v4.34.1 module (`Init` only; zero external dependencies).
- Every `def` carries explicit `noncomputable def` (no `noncomputable section`,
  no `partial def`, no `deriving` clauses, zero `._unsafe_rec` helpers).
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`.
-/

namespace SysvX8664Abi

/-! ## Section 1: SysV AMD64 Eightbyte Classification Semilattice -/

/-- System V AMD64 ABI §3.2.3 eightbyte register classes ordered in the
join-semilattice `NoClass < Sse < Int < Memory`. -/
inductive Class where
  | NoClass
  | Sse
  | Int
  | Memory

/-- `rustc_target::callconv::x86_64::Class` in `1.98.0-nightly` / `1.102.0`,
where `Option RustClass` represents `None` (no class yet) and `Int < Sse < SseUp`. -/
inductive RustClass where
  | Int
  | Sse
  | SseUp

/-- `rustc_target::callconv::x86_64::Class` on `rust-lang/rust` `main`,
extended with `X87` / `X87Up` and explicit `Sse`/`X87` conflict -> `Memory`. -/
inductive RustMainClass where
  | Int
  | Sse
  | SseUp
  | X87
  | X87Up

/-- Symmetric join on the SysV eightbyte semilattice `NoClass < Sse < Int < Memory`.
Matches AMD64 psABI §3.2.3p2 rule 4 and Clang `X86_64ABIInfo::merge`. -/
noncomputable def mergeClass (a b : Class) : Class :=
  match a, b with
  | .Memory, _ => .Memory
  | _, .Memory => .Memory
  | .NoClass, x => x
  | x, .NoClass => x
  | .Int, _ => .Int
  | _, .Int => .Int
  | .Sse, .Sse => .Sse

/-- Numeric rank witnessing the total chain `NoClass (0) < Sse (1) < Int (2) < Memory (3)`. -/
noncomputable def classRank : Class → Nat
  | .NoClass => 0
  | .Sse => 1
  | .Int => 2
  | .Memory => 3

/-- Semilattice partial (and total) order on `Class`. -/
noncomputable def classLe (a b : Class) : Prop :=
  classRank a ≤ classRank b

/-- Boolean equality on `Class` without `deriving DecidableEq`. -/
noncomputable def classEq (a b : Class) : Bool :=
  match a, b with
  | .NoClass, .NoClass => true
  | .Sse, .Sse => true
  | .Int, .Int => true
  | .Memory, .Memory => true
  | _, _ => false

theorem classEq_iff (a b : Class) : classEq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

theorem classEq_refl (a : Class) : classEq a a = true := by
  cases a <;> rfl

theorem mergeClass_comm (a b : Class) : mergeClass a b = mergeClass b a := by
  cases a <;> cases b <;> rfl

theorem mergeClass_assoc (a b c : Class) :
    mergeClass (mergeClass a b) c = mergeClass a (mergeClass b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mergeClass_idem (a : Class) : mergeClass a a = a := by
  cases a <;> rfl

theorem mergeClass_noClass_left (a : Class) : mergeClass .NoClass a = a := by
  cases a <;> rfl

theorem mergeClass_noClass_right (a : Class) : mergeClass a .NoClass = a := by
  cases a <;> rfl

theorem mergeClass_memory_left (a : Class) : mergeClass .Memory a = .Memory := by
  cases a <;> rfl

theorem mergeClass_memory_right (a : Class) : mergeClass a .Memory = .Memory := by
  cases a <;> rfl

theorem mergeClass_int_sse : mergeClass .Int .Sse = .Int := rfl

theorem mergeClass_sse_int : mergeClass .Sse .Int = .Int := rfl

theorem classLe_refl (a : Class) : classLe a a :=
  Nat.le_refl (classRank a)

theorem classLe_trans {a b c : Class} (hab : classLe a b) (hbc : classLe b c) :
    classLe a c :=
  Nat.le_trans hab hbc

theorem classLe_antisymm {a b : Class} (hab : classLe a b) (hba : classLe b a) :
    a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd (Nat.le_antisymm hab hba) (fun h => by cases h)

theorem classLe_total (a b : Class) : classLe a b ∨ classLe b a := by
  cases a <;> cases b <;> first
    | exact Or.inl (Nat.le_refl _)
    | exact Or.inl (Nat.zero_le _)
    | exact Or.inr (Nat.zero_le _)
    | exact Or.inl (Nat.le_succ _)
    | exact Or.inr (Nat.le_succ _)
    | exact Or.inl (Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2))
    | exact Or.inr (Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2))

theorem classLe_noClass_bottom (a : Class) : classLe .NoClass a :=
  Nat.zero_le (classRank a)

theorem classLe_memory_top (a : Class) : classLe a .Memory := by
  cases a <;> first
    | exact Nat.le_refl 3
    | exact Nat.le_succ 2
    | exact Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2)
    | exact Nat.zero_le 3

theorem mergeClass_le_left (a b : Class) : classLe a (mergeClass a b) := by
  cases a <;> cases b <;> first
    | exact classLe_refl _
    | exact classLe_noClass_bottom _
    | exact classLe_memory_top _
    | exact Nat.le_succ _

theorem mergeClass_le_right (a b : Class) : classLe b (mergeClass a b) := by
  rw [mergeClass_comm]
  exact mergeClass_le_left b a

theorem mergeClass_lub {a b c : Class} (ha : classLe a c) (hb : classLe b c) :
    classLe (mergeClass a b) c := by
  cases a <;> cases b <;> first
    | exact ha
    | exact hb

theorem mergeClass_eq_right_iff_le (a b : Class) :
    mergeClass a b = b ↔ classLe a b := by
  constructor
  · intro h
    rw [← h]
    exact mergeClass_le_left a b
  · intro h
    exact classLe_antisymm (mergeClass_lub h (classLe_refl b)) (mergeClass_le_right a b)

theorem mergeClass_eq_left_iff_le (a b : Class) :
    mergeClass a b = a ↔ classLe b a := by
  rw [mergeClass_comm]
  exact mergeClass_eq_right_iff_le b a

/-- `rustc_target::callconv::x86_64::Class` minimum (`Int < Sse < SseUp`). -/
noncomputable def rustClassMin (a b : RustClass) : RustClass :=
  match a, b with
  | .Int, _ => .Int
  | _, .Int => .Int
  | .Sse, _ => .Sse
  | _, .Sse => .Sse
  | .SseUp, .SseUp => .SseUp

/-- `rustc` `cls.map_or(c, |old| old.min(c))` at `x86_64.rs:88`. -/
noncomputable def unifyRustOpt (old : Option RustClass) (c : RustClass) : Option RustClass :=
  match old with
  | none => some c
  | some prev => some (rustClassMin prev c)

/-- Collapses `RustClass` (`SseUp` collapses to `Sse` per `x86_64.rs:117-118` for <=16B)
into SysV `Class`. -/
noncomputable def toSysvClass : Option RustClass → Class
  | none => .NoClass
  | some .Int => .Int
  | some .Sse => .Sse
  | some .SseUp => .Sse

theorem toSysvClass_unify_commutes (old : Option RustClass) (c : RustClass) :
    toSysvClass (unifyRustOpt old c) = mergeClass (toSysvClass old) (toSysvClass (some c)) := by
  cases old with
  | none => cases c <;> rfl
  | some prev => cases prev <;> cases c <;> rfl

/-- `rust-lang/rust` `main` `Class::merge` returning `none` for `Memory` on X87/SSE conflict. -/
noncomputable def mergeRustMain (a b : RustMainClass) : Option RustMainClass :=
  match a, b with
  | .X87, .Sse | .X87, .SseUp | .X87Up, .Sse | .X87Up, .SseUp => none
  | .Sse, .X87 | .Sse, .X87Up | .SseUp, .X87 | .SseUp, .X87Up => none
  | .Int, _ | _, .Int => some .Int
  | .Sse, _ | _, .Sse => some .Sse
  | .SseUp, _ => some .SseUp
  | .X87, _ | _, .X87 => some .X87
  | .X87Up, .X87Up => some .X87Up

theorem mergeRustMain_x87_sse_conflict :
    mergeRustMain .X87 .Sse = none ∧
    mergeRustMain .X87 .SseUp = none ∧
    mergeRustMain .Sse .X87 = none ∧
    mergeRustMain .SseUp .X87Up = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Fold `mergeClass` over a list of field eightbyte contributions. -/
noncomputable def mergeList : List Class → Class
  | [] => .NoClass
  | c :: cs => mergeClass c (mergeList cs)

theorem mergeList_nil : mergeList [] = .NoClass := rfl

theorem mergeList_cons (c : Class) (cs : List Class) :
    mergeList (c :: cs) = mergeClass c (mergeList cs) := rfl

theorem mergeList_append (xs ys : List Class) :
    mergeList (xs ++ ys) = mergeClass (mergeList xs) (mergeList ys) := by
  induction xs with
  | nil =>
    rw [List.nil_append, mergeList_nil, mergeClass_noClass_left]
  | cons x xs ih =>
    rw [List.cons_append, mergeList_cons, mergeList_cons, ih, mergeClass_assoc]

theorem mergeList_memory_absorbs {xs : List Class} (h : .Memory ∈ xs) :
    mergeList xs = .Memory := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rw [mergeList_cons]
    cases h with
    | head _ => rw [mergeClass_memory_left]
    | tail _ hmem =>
      rw [ih hmem, mergeClass_memory_right]

theorem mergeList_no_memory_ne_memory {xs : List Class}
    (hno : ∀ c, c ∈ xs → c ≠ .Memory) :
    mergeList xs ≠ .Memory := by
  induction xs with
  | nil =>
    intro heq
    cases heq
  | cons x xs ih =>
    rw [mergeList_cons]
    have hx : x ≠ .Memory := hno x (List.Mem.head xs)
    have hxs : mergeList xs ≠ .Memory := ih (fun c hc => hno c (List.Mem.tail x hc))
    cases x with
    | Memory => exact absurd rfl hx
    | NoClass =>
      rw [mergeClass_noClass_left]
      exact hxs
    | Sse =>
      cases hrem : mergeList xs with
      | Memory => exact absurd hrem hxs
      | NoClass => intro h; cases h
      | Sse => intro h; cases h
      | Int => intro h; cases h
    | Int =>
      cases hrem : mergeList xs with
      | Memory => exact absurd hrem hxs
      | NoClass => intro h; cases h
      | Sse => intro h; cases h
      | Int => intro h; cases h

theorem mergeList_int_dominates {xs : List Class} (hint : .Int ∈ xs)
    (hnomem : ∀ c, c ∈ xs → c ≠ .Memory) :
    mergeList xs = .Int := by
  induction xs with
  | nil => cases hint
  | cons x xs ih =>
    have htail_nomem : ∀ c, c ∈ xs → c ≠ .Memory := fun c hc => hnomem c (List.Mem.tail x hc)
    have htail_ne_mem : mergeList xs ≠ .Memory := mergeList_no_memory_ne_memory htail_nomem
    rw [mergeList_cons]
    cases hint with
    | head _ =>
      cases hrem : mergeList xs with
      | Memory => exact absurd hrem htail_ne_mem
      | NoClass => rfl
      | Sse => rfl
      | Int => rfl
    | tail _ hin =>
      have hih : mergeList xs = .Int := ih hin htail_nomem
      rw [hih]
      have hx : x ≠ .Memory := hnomem x (List.Mem.head xs)
      cases x with
      | Memory => exact absurd rfl hx
      | NoClass => rfl
      | Sse => rfl
      | Int => rfl

theorem mergeList_all_noClass {xs : List Class} (hall : ∀ c, c ∈ xs → c = .NoClass) :
    mergeList xs = .NoClass := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mergeList_cons]
    have hx : x = .NoClass := hall x (List.Mem.head xs)
    have hxs : mergeList xs = .NoClass := ih (fun c hc => hall c (List.Mem.tail x hc))
    rw [hx, hxs]
    rfl

theorem mergeList_swap_head (a b : Class) (xs : List Class) :
    mergeList (a :: b :: xs) = mergeList (b :: a :: xs) := by
  rw [mergeList_cons, mergeList_cons, mergeList_cons, mergeList_cons]
  rw [← mergeClass_assoc, mergeClass_comm a b, mergeClass_assoc]

theorem mergeList_idem_head (a : Class) (xs : List Class) :
    mergeList (a :: a :: xs) = mergeList (a :: xs) := by
  rw [mergeList_cons, mergeList_cons, ← mergeClass_assoc, mergeClass_idem]

/-! ## Section 2: Field Layout, Eightbyte Partitioning, 16-Byte Cutoff & `Ignore` -/

/-- Scalar primitive categories mapped in `x86_64.rs:55-58` (and `058c7010` `76-80`). -/
inductive PrimKind where
  | pBool
  | pInt8
  | pInt16
  | pInt32
  | pInt64
  | pInt128
  | pPtr
  | pF32
  | pF64
  | pX87F80

/-- Rust representation attributes affecting `inhibit_newtype_abi_optimization()`. -/
inductive ReprAttr where
  | reprRust
  | reprC
  | reprTransparent

/-- `rustc_abi::BackendRepr` (`compiler/rustc_abi/src/lib.rs`). -/
inductive BackendRepr where
  | brScalar
  | brScalarPair
  | brMemory

/-- Flattened scalar/leaf field descriptor within an aggregate layout. -/
structure FieldDesc where
  offsetBytes : Nat
  sizeBytes : Nat
  alignBytes : Nat
  prim : PrimKind

/-- Self-contained ABI layout descriptor modeling `TyAndLayout` for x86_64 SysV. -/
structure AbiStructDesc where
  sizeBytes : Nat
  alignBytes : Nat
  backendRepr : BackendRepr
  reprAttr : ReprAttr
  isVector : Bool
  fields : List FieldDesc

/-- Maps a primitive scalar kind to its SysV eightbyte class. -/
noncomputable def primClass : PrimKind → Class
  | .pBool | .pInt8 | .pInt16 | .pInt32 | .pInt64 | .pInt128 | .pPtr => .Int
  | .pF32 | .pF64 => .Sse
  | .pX87F80 => .Memory

/-- Number of eightbytes (`sizeBytes.div_ceil 8` at `x86_64.rs:100`). -/
noncomputable def eightbyteCount (sizeBytes : Nat) : Nat :=
  (sizeBytes + 7) / 8

/-- True iff field `f` is non-empty and its byte span overlaps eightbyte index `ebIdx`. -/
noncomputable def spansEightbyte (ebIdx : Nat) (f : FieldDesc) : Bool :=
  if Nat.blt 0 f.sizeBytes then
    let first := f.offsetBytes / 8
    let last := (f.offsetBytes + f.sizeBytes - 1) / 8
    Nat.ble first ebIdx && Nat.ble ebIdx last
  else
    false

/-- Alignment check from `x86_64.rs:47-52` (`!off.is_aligned(layout.align.abi)`). -/
noncomputable def fieldAligned (f : FieldDesc) : Bool :=
  if Nat.beq f.sizeBytes 0 then true
  else if Nat.beq f.alignBytes 0 then false
  else Nat.beq (f.offsetBytes % f.alignBytes) 0

/-- Single field's contribution to eightbyte `ebIdx` (`Memory` if unaligned). -/
noncomputable def fieldContribAt (ebIdx : Nat) (f : FieldDesc) : Class :=
  if fieldAligned f then
    if spansEightbyte ebIdx f then primClass f.prim else .NoClass
  else
    .Memory

/-- Classifies eightbyte `ebIdx` by merging all field contributions. -/
noncomputable def classifyEightbyte (ebIdx : Nat) (fields : List FieldDesc) : Class :=
  mergeList (fields.map (fieldContribAt ebIdx))

/-- True iff all non-ZST fields satisfy their natural ABI alignment. -/
noncomputable def allFieldsAligned : List FieldDesc → Bool
  | [] => true
  | f :: fs => fieldAligned f && allFieldsAligned fs

/-- Result of SysV AMD64 eightbyte classification (`<= 16 B` register vs memory vs ignore). -/
inductive ArgClassification where
  | clIgnore
  | clMemory
  | clRegs (eb0 : Class) (eb1 : Class)

/-- Top-level SysV AMD64 classification (`x86_64.rs:100-130`) for non-SIMD and
scalar/aggregate types. -/
noncomputable def classifyType (ty : AbiStructDesc) : ArgClassification :=
  if Nat.beq ty.sizeBytes 0 then
    .clIgnore
  else if Nat.blt 16 ty.sizeBytes && !ty.isVector then
    .clMemory
  else if !allFieldsAligned ty.fields then
    .clMemory
  else
    let c0 := classifyEightbyte 0 ty.fields
    let c1 := classifyEightbyte 1 ty.fields
    if classEq c0 .Memory || classEq c1 .Memory then
      .clMemory
    else if classEq c0 .NoClass && classEq c1 .NoClass then
      .clIgnore
    else
      .clRegs c0 c1

/-- Helper arithmetic lemma without `omega`: `Nat.blt a b = true ↔ a < b`. -/
theorem nat_blt_true_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  unfold Nat.blt
  exact iff_of_eq Nat.ble_eq

/-- Helper arithmetic lemma without `omega`: `Nat.ble a b = true ↔ a ≤ b`. -/
theorem nat_ble_true_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b :=
  iff_of_eq Nat.ble_eq

/-- Helper arithmetic lemma without `omega`: `Nat.beq a b = true ↔ a = b`. -/
theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  iff_of_eq Nat.beq_eq

/-- Helper arithmetic lemma: `eightbyteCount sz > 2` iff `16 < sz` (pure `Nat`, no `omega`). -/
theorem eightbyteCount_gt_two_iff (sz : Nat) :
    2 < eightbyteCount sz ↔ 16 < sz := by
  unfold eightbyteCount
  constructor
  · intro h
    have hmul : 3 * 8 ≤ (sz + 7) := by
      have h3 : 3 ≤ (sz + 7) / 8 := h
      exact Nat.le_trans (Nat.mul_le_mul_right 8 h3) (Nat.div_mul_le_self (sz + 7) 8)
    have h17 : 17 + 7 ≤ sz + 7 := hmul
    exact Nat.le_of_add_le_add_right h17
  · intro h
    have h24 : 3 * 8 ≤ sz + 7 := Nat.add_le_add_right h 7
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr h24

/-- Theorem: any zero-sized type lowers to `.clIgnore` (ZST `PassMode::Ignore`). -/
theorem zero_size_gives_ignore (ty : AbiStructDesc) (hz : ty.sizeBytes = 0) :
    classifyType ty = .clIgnore := by
  unfold classifyType
  have hbeq : Nat.beq ty.sizeBytes 0 = true := (nat_beq_true_iff ty.sizeBytes 0).mpr hz
  rw [hbeq]
  rfl

/-- Theorem: any non-vector aggregate larger than 16 bytes (`n > 2`) classifies as `.clMemory`. -/
theorem size_over_16B_non_vector_gives_memory (ty : AbiStructDesc)
    (hsz : 16 < ty.sizeBytes) (hnv : ty.isVector = false) :
    classifyType ty = .clMemory := by
  unfold classifyType
  have hne0 : ty.sizeBytes ≠ 0 := by
    intro hz
    rw [hz] at hsz
    exact absurd hsz (fun h => by cases h)
  have hbeq : Nat.beq ty.sizeBytes 0 = false := by
    cases h : Nat.beq ty.sizeBytes 0 with
    | false => rfl
    | true => exact absurd ((nat_beq_true_iff _ _).mp h) hne0
  have hblt : Nat.blt 16 ty.sizeBytes = true := (nat_blt_true_iff 16 ty.sizeBytes).mpr hsz
  rw [hbeq, hblt, hnv]
  rfl

/-- Lemma: if `f ∈ fs` has `fieldAligned f = false`, then `allFieldsAligned fs = false`. -/
theorem not_allFieldsAligned_of_mem {f : FieldDesc} {fs : List FieldDesc}
    (hmem : f ∈ fs) (hun : fieldAligned f = false) :
    allFieldsAligned fs = false := by
  induction fs with
  | nil => cases hmem
  | cons x xs ih =>
    unfold allFieldsAligned
    cases hmem with
    | head _ =>
      rw [hun]
      rfl
    | tail _ htail =>
      rw [ih htail, Bool.and_false]

/-- Lemma: if `allFieldsAligned fs = true` and `f ∈ fs`, then `fieldAligned f = true`. -/
theorem fieldAligned_of_allFieldsAligned {f : FieldDesc} {fs : List FieldDesc}
    (hal : allFieldsAligned fs = true) (hmem : f ∈ fs) :
    fieldAligned f = true := by
  induction fs with
  | nil => cases hmem
  | cons x xs ih =>
    unfold allFieldsAligned at hal
    cases hmem with
    | head _ =>
      cases hfx : fieldAligned f with
      | true => rfl
      | false => rw [hfx] at hal; cases hal
    | tail _ htl =>
      apply ih
      · cases hxa : fieldAligned x with
        | true => rw [hxa] at hal; exact hal
        | false => rw [hxa] at hal; cases hal
      · exact htl

/-- Theorem: any non-empty type containing an unaligned non-ZST field classifies as `.clMemory`. -/
theorem unaligned_non_zst_field_forces_memory (ty : AbiStructDesc) {f : FieldDesc}
    (hpos : 0 < ty.sizeBytes) (hmem : f ∈ ty.fields) (hun : fieldAligned f = false) :
    classifyType ty = .clMemory := by
  unfold classifyType
  have hne0 : ty.sizeBytes ≠ 0 := by
    intro hz
    rw [hz] at hpos
    exact absurd hpos (fun h => by cases h)
  have hbeq : Nat.beq ty.sizeBytes 0 = false := by
    cases h : Nat.beq ty.sizeBytes 0 with
    | false => rfl
    | true => exact absurd ((nat_beq_true_iff _ _).mp h) hne0
  rw [hbeq]
  cases hcut : Nat.blt 16 ty.sizeBytes && !ty.isVector with
  | true => rfl
  | false =>
    have hall : allFieldsAligned ty.fields = false := not_allFieldsAligned_of_mem hmem hun
    rw [hall]
    rfl

theorem classifyEightbyte_cons (ebIdx : Nat) (f : FieldDesc) (fs : List FieldDesc) :
    classifyEightbyte ebIdx (f :: fs) =
      mergeClass (fieldContribAt ebIdx f) (classifyEightbyte ebIdx fs) :=
  rfl

/-- Theorem: any aligned `Int`-class field spanning eightbyte `ebIdx` dominates that
eightbyte (unless another field introduces `Memory`, e.g. `X87F80`). -/
theorem classifyEightbyte_aligned_int_dominates {ebIdx : Nat} {f : FieldDesc}
    {fs : List FieldDesc} (hmem : f ∈ fs) (hal : allFieldsAligned fs = true)
    (hspan : spansEightbyte ebIdx f = true) (hprim : primClass f.prim = .Int)
    (hnomem : ∀ g, g ∈ fs → primClass g.prim ≠ .Memory) :
    classifyEightbyte ebIdx fs = .Int := by
  unfold classifyEightbyte
  apply mergeList_int_dominates
  · have hf_al : fieldAligned f = true := fieldAligned_of_allFieldsAligned hal hmem
    have hcontrib : fieldContribAt ebIdx f = .Int := by
      unfold fieldContribAt
      rw [hf_al, hspan, hprim]
      rfl
    rw [← hcontrib]
    exact List.mem_map_of_mem hmem
  · intro c hc
    have ⟨g, hgmem, hgcontrib⟩ := List.mem_map.mp hc
    have hg_al : fieldAligned g = true := fieldAligned_of_allFieldsAligned hal hgmem
    rw [← hgcontrib]
    unfold fieldContribAt
    rw [hg_al]
    cases spansEightbyte ebIdx g with
    | false => intro h; cases h
    | true => exact hnomem g hgmem

/-- Theorem: a 16-byte `u128`/`i128` scalar at offset 0 spans both eightbyte 0 and eightbyte 1. -/
theorem scalar_128_spans_both_eightbytes :
    let f128 : FieldDesc := ⟨0, 16, 16, .pInt128⟩
    spansEightbyte 0 f128 = true ∧ spansEightbyte 1 f128 = true :=
  ⟨rfl, rfl⟩

/-! ## Section 3: `PassMode` Lowering & LLVM IR Signature Mapping -/

/-- `rustc_abi::Reg` subset materialized by SysV `x86_64.rs:133-159`. -/
inductive RegKind where
  | rInt (bits : Nat)
  | rF32
  | rF64

/-- `rustc_target::callconv::CastTarget` subset (`single` vs `pair`). -/
inductive CastTarget where
  | ctSingle (r : RegKind)
  | ctPair (lo hi : RegKind)

/-- `rustc_target::callconv::PassMode` (`compiler/rustc_target/src/callconv/mod.rs:39-74`). -/
inductive PassMode where
  | pmIgnore
  | pmDirect (bits : Nat) (noundef : Bool)
  | pmPair
  | pmCast (ct : CastTarget)
  | pmIndirect (sizeBytes alignBytes : Nat) (onStack : Bool)

/-- LLVM IR type and attribute projection modeled after `rustc_codegen_llvm/src/abi.rs`. -/
inductive LlvmSigTy where
  | llVoid
  | llInt (bits : Nat) (noundef : Bool)
  | llF32
  | llF64
  | llStructPair (a b : LlvmSigTy)
  | llPtrSret (sizeBytes alignBytes : Nat)
  | llPtrByVal (sizeBytes alignBytes : Nat)

/-- `TyAndLayout::is_aggregate()` combined with `ReprOptions::inhibit_newtype_abi_optimization()`
(`compiler/rustc_abi/src/layout.rs:1329-1358`). `#[repr(C)]` prevents unpacking a
single-field scalar (`I128Struct { x: u128 }`, `S1 { x: u64 }`) into `BackendRepr::Scalar`,
whereas bare `u128` and `#[repr(transparent)]` preserve `BackendRepr::Scalar` (`false`). -/
noncomputable def effectiveIsAggregate (ty : AbiStructDesc) : Bool :=
  match ty.reprAttr with
  | .reprC => Nat.blt 0 ty.sizeBytes
  | .reprTransparent | .reprRust =>
    match ty.backendRepr with
    | .brScalar => false
    | .brScalarPair | .brMemory => true

/-- `x86_64.rs:133-159`: converts one eightbyte class + remaining byte count into `RegKind`.
Crucially, `Class.Sse` with `vec_len == 1` maps `4` bytes -> `rF32` (`float`) and ANY
other size (e.g. `8` bytes for `PairF32 { a: f32, b: f32 }`) -> `rF64` (`double`)! -/
noncomputable def regComponent (c : Class) (remBytes : Nat) : Option RegKind :=
  match c with
  | .NoClass => none
  | .Int =>
    if Nat.blt remBytes 8 then some (.rInt (remBytes * 8)) else some (.rInt 64)
  | .Sse =>
    if Nat.beq remBytes 4 then some .rF32 else some .rF64
  | .Memory => none

/-- `x86_64.rs:161-173`: builds `CastTarget` from `(eb0, eb1)` and aggregate `sizeBytes`. -/
noncomputable def castTargetOf (c0 c1 : Class) (sizeBytes : Nat) : Option CastTarget :=
  match regComponent c0 sizeBytes with
  | none => none
  | some lo =>
    if Nat.blt 8 sizeBytes then
      match regComponent c1 (sizeBytes - 8) with
      | none => some (.ctSingle lo)
      | some hi => some (.ctPair lo hi)
    else
      some (.ctSingle lo)

/-- Models `ArgAbi::mode` for a single argument or return under SysV x86_64 `compute_abi_info`
(before register-bank exhaustion rollback). -/
noncomputable def lowerClassifiedMode (ty : AbiStructDesc) (isArg : Bool) (optimize : Bool) : PassMode :=
  match classifyType ty with
  | .clIgnore => .pmIgnore
  | .clMemory => .pmIndirect ty.sizeBytes ty.alignBytes isArg
  | .clRegs c0 c1 =>
    if effectiveIsAggregate ty then
      match castTargetOf c0 c1 ty.sizeBytes with
      | some ct => .pmCast ct
      | none => .pmIndirect ty.sizeBytes ty.alignBytes isArg
    else
      .pmDirect (ty.sizeBytes * 8) optimize

/-- `LlvmType for Reg` (`compiler/rustc_codegen_llvm/src/abi.rs:130-140`). -/
noncomputable def regToLlvm : RegKind → LlvmSigTy
  | .rInt bits => .llInt bits false
  | .rF32 => .llF32
  | .rF64 => .llF64

/-- `LlvmType for CastTarget` + `FnAbiExt::llvm_type` + `apply_attrs_llfn`
(`compiler/rustc_codegen_llvm/src/abi.rs:170-208, 361-420, 483-583`). -/
noncomputable def passModeToLlvm : PassMode → LlvmSigTy
  | .pmIgnore => .llVoid
  | .pmDirect bits noundef => .llInt bits noundef
  | .pmPair => .llStructPair (.llInt 64 false) (.llInt 64 false)
  | .pmCast (.ctSingle r) => regToLlvm r
  | .pmCast (.ctPair lo hi) => .llStructPair (regToLlvm lo) (regToLlvm hi)
  | .pmIndirect sz al true => .llPtrByVal sz al
  | .pmIndirect sz al false => .llPtrSret sz al

/-- Number of GP and XMM registers consumed by a `PassMode` (for non-exhausted slots). -/
noncomputable def regUsageOfClass : Class → Nat × Nat
  | .NoClass => (0, 0)
  | .Sse => (0, 1)
  | .Int => (1, 0)
  | .Memory => (0, 0)

noncomputable def neededRegsForClasses (c0 c1 : Class) : Nat × Nat :=
  let (g0, x0) := regUsageOfClass c0
  let (g1, x1) := regUsageOfClass c1
  (g0 + g1, x0 + x1)

/-! ## Section 4: Register-Bank Budget (`6` GP + `8` XMM) & Rollback Soundness -/

/-- The 6 System V AMD64 GP argument registers (`x86_64.rs:175`). -/
inductive GPReg where
  | rdi | rsi | rdx | rcx | r8 | r9

/-- The 8 System V AMD64 XMM argument registers (`x86_64.rs:176`). -/
inductive XMMReg where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7

/-- Remaining free registers in each bank (`gpFree ≤ 6`, `xmmFree ≤ 8`). -/
structure RegBudget where
  gpFree : Nat
  xmmFree : Nat

/-- Initial parameter budget at function entry (`x86_64.rs:183-184`). -/
noncomputable def initRegBudget : RegBudget :=
  ⟨6, 8⟩

/-- Ordered bank of GP registers. -/
noncomputable def allGPRegs : List GPReg :=
  [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- Ordered bank of XMM registers. -/
noncomputable def allXMMRegs : List XMMReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

/-- Slices the next `count` registers starting at index `bankSize - freeCount`. -/
noncomputable def takeNextGP (gpFree count : Nat) : List GPReg :=
  (allGPRegs.drop (6 - gpFree)).take count

noncomputable def takeNextXMM (xmmFree count : Nat) : List XMMReg :=
  (allXMMRegs.drop (8 - xmmFree)).take count

/-- Physical SysV parameter placement produced after bank-budget checking. -/
inductive ParamPlacement where
  | plIgnore
  | plRegs (gps : List GPReg) (xmms : List XMMReg)
  | plStackByVal (sizeBytes alignBytes : Nat)
  | plStackScalar (bits : Nat)

/-- Result of placing one argument against `budget`. -/
structure ParamStepResult where
  placement : ParamPlacement
  nextBudget : RegBudget
  loweredMode : PassMode

/-- Models return-value ABI adjustment (`x86_64.rs:234-241, 255-257`).
Return is processed FIRST; `sret` (`Err(Memory)`) consumes 1 GP register (`%rdi`),
leaving `5` GP registers and `8` XMM registers for arguments. -/
noncomputable def assignReturnAbi (retTy : AbiStructDesc) (optimize : Bool) :
    PassMode × RegBudget :=
  let mode := lowerClassifiedMode retTy false optimize
  match mode with
  | .pmIndirect _ _ false => (mode, ⟨initRegBudget.gpFree - 1, initRegBudget.xmmFree⟩)
  | _ => (mode, initRegBudget)

/-- Models argument ABI adjustment with all-or-nothing register-bank rollback
(`x86_64.rs:197-252` and AMD64 psABI §3.2.3p3).
If `needGp ≤ budget.gpFree` and `needXmm ≤ budget.xmmFree`, both banks decrement
atomically and registers are assigned; otherwise **neither** bank changes and
the entire argument falls back to stack (`byval` for aggregates, stack slot for
immediates). -/
noncomputable def assignArg (budget : RegBudget) (ty : AbiStructDesc) (optimize : Bool) :
    ParamStepResult :=
  match classifyType ty with
  | .clIgnore =>
    ⟨.plIgnore, budget, .pmIgnore⟩
  | .clMemory =>
    ⟨.plStackByVal ty.sizeBytes ty.alignBytes, budget, .pmIndirect ty.sizeBytes ty.alignBytes true⟩
  | .clRegs c0 c1 =>
    if Nat.ble (neededRegsForClasses c0 c1).1 budget.gpFree &&
       Nat.ble (neededRegsForClasses c0 c1).2 budget.xmmFree then
      ⟨.plRegs
          (takeNextGP budget.gpFree (neededRegsForClasses c0 c1).1)
          (takeNextXMM budget.xmmFree (neededRegsForClasses c0 c1).2),
       ⟨budget.gpFree - (neededRegsForClasses c0 c1).1,
        budget.xmmFree - (neededRegsForClasses c0 c1).2⟩,
       lowerClassifiedMode ty true optimize⟩
    else
      if effectiveIsAggregate ty then
        ⟨.plStackByVal ty.sizeBytes ty.alignBytes, budget, .pmIndirect ty.sizeBytes ty.alignBytes true⟩
      else
        ⟨.plStackScalar (ty.sizeBytes * 8), budget, .pmDirect (ty.sizeBytes * 8) optimize⟩

/-- Processes all arguments left-to-right starting from `budget`. -/
noncomputable def assignArgList (budget : RegBudget) (args : List AbiStructDesc) (optimize : Bool) :
    List ParamStepResult × RegBudget :=
  match args with
  | [] => ([], budget)
  | ty :: rest =>
    let step := assignArg budget ty optimize
    let (tailSteps, finalBudget) := assignArgList step.nextBudget rest optimize
    (step :: tailSteps, finalBudget)

/-- Full function ABI assignment (`ret` first, then left-to-right `args`). -/
noncomputable def assignFnAbi (retTy : AbiStructDesc) (args : List AbiStructDesc) (optimize : Bool) :
    PassMode × List ParamStepResult × RegBudget :=
  let (retMode, postRetBudget) := assignReturnAbi retTy optimize
  let (argSteps, finalBudget) := assignArgList postRetBudget args optimize
  (retMode, argSteps, finalBudget)

/-- Theorem: `sret` return (`TripleI` or any `> 16 B` return) consumes `%rdi`, leaving
`5` GP registers and `8` XMM registers for arguments (`x86_64.rs:236-240`). -/
theorem ret_sret_leaves_5_gp_regs (retTy : AbiStructDesc) (optimize : Bool)
    (hsz : 16 < retTy.sizeBytes) (hnv : retTy.isVector = false) :
    (assignReturnAbi retTy optimize).2 = ⟨5, 8⟩ := by
  unfold assignReturnAbi lowerClassifiedMode
  rw [size_over_16B_non_vector_gives_memory retTy hsz hnv]
  rfl

/-- Theorem (All-or-Nothing Rollback on GP Exhaustion): If `ty` classifies as
`clRegs c0 c1` needing `needGp` GP registers and `budget.gpFree < needGp`,
then `assignArg` preserves `budget` completely untouched (`gpFree` and `xmmFree`
unchanged!) and places the entire argument on the stack (no partial register split). -/
theorem assignArg_all_or_nothing_gp_insufficient (budget : RegBudget) (ty : AbiStructDesc)
    (optimize : Bool) {c0 c1 : Class}
    (hcls : classifyType ty = .clRegs c0 c1)
    (hgp : budget.gpFree < (neededRegsForClasses c0 c1).1) :
    (assignArg budget ty optimize).nextBudget = budget ∧
    (match (assignArg budget ty optimize).placement with
     | .plStackByVal _ _ => True
     | .plStackScalar _ => True
     | _ => False) := by
  unfold assignArg
  rw [hcls]
  dsimp only
  have hble : Nat.ble (neededRegsForClasses c0 c1).1 budget.gpFree = false := by
    cases h : Nat.ble (neededRegsForClasses c0 c1).1 budget.gpFree with
    | false => rfl
    | true =>
      have hle : (neededRegsForClasses c0 c1).1 ≤ budget.gpFree := (nat_ble_true_iff _ _).mp h
      exact absurd (Nat.lt_of_le_of_lt hle hgp) (Nat.lt_irrefl _)
  rw [hble, Bool.false_and]
  cases effectiveIsAggregate ty with
  | true => exact ⟨rfl, trivial⟩
  | false => exact ⟨rfl, trivial⟩

/-- Theorem (All-or-Nothing Rollback on XMM Exhaustion): If `budget.xmmFree < needXmm`,
`assignArg` preserves `budget` completely untouched (even if GP registers are still free!)
and places the entire argument on the stack. -/
theorem assignArg_all_or_nothing_xmm_insufficient (budget : RegBudget) (ty : AbiStructDesc)
    (optimize : Bool) {c0 c1 : Class}
    (hcls : classifyType ty = .clRegs c0 c1)
    (hxmm : budget.xmmFree < (neededRegsForClasses c0 c1).2) :
    (assignArg budget ty optimize).nextBudget = budget ∧
    (match (assignArg budget ty optimize).placement with
     | .plStackByVal _ _ => True
     | .plStackScalar _ => True
     | _ => False) := by
  unfold assignArg
  rw [hcls]
  dsimp only
  have hble : Nat.ble (neededRegsForClasses c0 c1).2 budget.xmmFree = false := by
    cases h : Nat.ble (neededRegsForClasses c0 c1).2 budget.xmmFree with
    | false => rfl
    | true =>
      have hle : (neededRegsForClasses c0 c1).2 ≤ budget.xmmFree := (nat_ble_true_iff _ _).mp h
      exact absurd (Nat.lt_of_le_of_lt hle hxmm) (Nat.lt_irrefl _)
  rw [hble, Bool.and_false]
  cases effectiveIsAggregate ty with
  | true => exact ⟨rfl, trivial⟩
  | false => exact ⟨rfl, trivial⟩

/-- Theorem (No Partial Register/Stack Split on 2-Eightbyte Types): Whenever `c0 ≠ .NoClass`
and `c1 ≠ .NoClass` (and neither is `.Memory`), `assignArg` either assigns BOTH eightbytes
to registers (`gps.length + xmms.length = 2`) or assigns ZERO registers (`plStackByVal`/`plStackScalar`). -/
theorem regUsageOfClass_non_empty {c : Class} (hne : c ≠ .NoClass) (hnm : c ≠ .Memory) :
    (regUsageOfClass c).1 + (regUsageOfClass c).2 = 1 := by
  cases c with
  | NoClass => exact absurd rfl hne
  | Memory => exact absurd rfl hnm
  | Sse => rfl
  | Int => rfl

theorem takeNextGP_length {gpFree count : Nat}
    (hb : gpFree ≤ 6) (hc : count ≤ gpFree) :
    (takeNextGP gpFree count).length = count := by
  unfold takeNextGP allGPRegs
  have hdrop : (([GPReg.rdi, .rsi, .rdx, .rcx, .r8, .r9].drop (6 - gpFree)).length) = gpFree := by
    rw [List.length_drop]
    change 6 - (6 - gpFree) = gpFree
    exact Nat.sub_sub_self hb
  rw [List.length_take, hdrop]
  exact Nat.min_eq_left hc

theorem takeNextXMM_length {xmmFree count : Nat}
    (hb : xmmFree ≤ 8) (hc : count ≤ xmmFree) :
    (takeNextXMM xmmFree count).length = count := by
  unfold takeNextXMM allXMMRegs
  have hdrop : (([XMMReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7].drop (8 - xmmFree)).length) = xmmFree := by
    rw [List.length_drop]
    change 8 - (8 - xmmFree) = xmmFree
    exact Nat.sub_sub_self hb
  rw [List.length_take, hdrop]
  exact Nat.min_eq_left hc

theorem assignArg_budget_monotone {budget : RegBudget} {ty : AbiStructDesc} {optimize : Bool}
    (hgp_b : budget.gpFree ≤ 6) (hxmm_b : budget.xmmFree ≤ 8) :
    (assignArg budget ty optimize).nextBudget.gpFree ≤ budget.gpFree ∧
    (assignArg budget ty optimize).nextBudget.xmmFree ≤ budget.xmmFree ∧
    (assignArg budget ty optimize).nextBudget.gpFree ≤ 6 ∧
    (assignArg budget ty optimize).nextBudget.xmmFree ≤ 8 := by
  unfold assignArg
  cases classifyType ty with
  | clIgnore =>
    exact ⟨Nat.le_refl _, Nat.le_refl _, hgp_b, hxmm_b⟩
  | clMemory =>
    exact ⟨Nat.le_refl _, Nat.le_refl _, hgp_b, hxmm_b⟩
  | clRegs c0 c1 =>
    dsimp only
    cases Nat.ble (neededRegsForClasses c0 c1).1 budget.gpFree &&
         Nat.ble (neededRegsForClasses c0 c1).2 budget.xmmFree with
    | false =>
      cases effectiveIsAggregate ty with
      | true => exact ⟨Nat.le_refl _, Nat.le_refl _, hgp_b, hxmm_b⟩
      | false => exact ⟨Nat.le_refl _, Nat.le_refl _, hgp_b, hxmm_b⟩
    | true =>
      have hsub_gp : budget.gpFree - (neededRegsForClasses c0 c1).1 ≤ budget.gpFree :=
        Nat.sub_le _ _
      have hsub_xmm : budget.xmmFree - (neededRegsForClasses c0 c1).2 ≤ budget.xmmFree :=
        Nat.sub_le _ _
      exact ⟨hsub_gp, hsub_xmm, Nat.le_trans hsub_gp hgp_b, Nat.le_trans hsub_xmm hxmm_b⟩

/-- Helper: count of GP registers placed by one step. -/
noncomputable def stepGPCount (step : ParamStepResult) : Nat :=
  match step.placement with
  | .plRegs gps _ => gps.length
  | _ => 0

/-- Helper: count of XMM registers placed by one step. -/
noncomputable def stepXMMCount (step : ParamStepResult) : Nat :=
  match step.placement with
  | .plRegs _ xmms => xmms.length
  | _ => 0

theorem assignArg_conserves_registers {budget : RegBudget} {ty : AbiStructDesc} {optimize : Bool}
    (hgp_b : budget.gpFree ≤ 6) (hxmm_b : budget.xmmFree ≤ 8) :
    stepGPCount (assignArg budget ty optimize) + (assignArg budget ty optimize).nextBudget.gpFree = budget.gpFree ∧
    stepXMMCount (assignArg budget ty optimize) + (assignArg budget ty optimize).nextBudget.xmmFree = budget.xmmFree := by
  unfold assignArg
  cases classifyType ty with
  | clIgnore => exact ⟨Nat.zero_add _, Nat.zero_add _⟩
  | clMemory => exact ⟨Nat.zero_add _, Nat.zero_add _⟩
  | clRegs c0 c1 =>
    dsimp only
    cases hgp : Nat.ble (neededRegsForClasses c0 c1).1 budget.gpFree with
    | false =>
      rw [Bool.false_and]
      cases effectiveIsAggregate ty <;> exact ⟨Nat.zero_add _, Nat.zero_add _⟩
    | true =>
      cases hxmm : Nat.ble (neededRegsForClasses c0 c1).2 budget.xmmFree with
      | false =>
        rw [Bool.and_false]
        cases effectiveIsAggregate ty <;> exact ⟨Nat.zero_add _, Nat.zero_add _⟩
      | true =>
        rw [Bool.and_self]
        have hgp_le : (neededRegsForClasses c0 c1).1 ≤ budget.gpFree := (nat_ble_true_iff _ _).mp hgp
        have hxmm_le : (neededRegsForClasses c0 c1).2 ≤ budget.xmmFree := (nat_ble_true_iff _ _).mp hxmm
        constructor
        · unfold stepGPCount
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
          dsimp only
          rw [takeNextGP_length hgp_b hgp_le]
          exact Nat.add_sub_of_le hgp_le
        · unfold stepXMMCount
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
          dsimp only
          rw [takeNextXMM_length hxmm_b hxmm_le]
          exact Nat.add_sub_of_le hxmm_le

theorem assignArg_no_partial_split_two_eb (budget : RegBudget) (ty : AbiStructDesc)
    (optimize : Bool) {c0 c1 : Class}
    (hcls : classifyType ty = .clRegs c0 c1)
    (hc0_ne : c0 ≠ .NoClass) (hc0_nm : c0 ≠ .Memory)
    (hc1_ne : c1 ≠ .NoClass) (hc1_nm : c1 ≠ .Memory)
    (hgp_b : budget.gpFree ≤ 6) (hxmm_b : budget.xmmFree ≤ 8) :
    match (assignArg budget ty optimize).placement with
    | .plRegs gps xmms => gps.length + xmms.length = 2
    | .plStackByVal _ _ => True
    | .plStackScalar _ => True
    | .plIgnore => False := by
  unfold assignArg
  rw [hcls]
  dsimp only
  cases hgp : Nat.ble (neededRegsForClasses c0 c1).1 budget.gpFree with
  | false =>
    rw [Bool.false_and]
    cases effectiveIsAggregate ty <;> exact trivial
  | true =>
    cases hxmm : Nat.ble (neededRegsForClasses c0 c1).2 budget.xmmFree with
    | false =>
      rw [Bool.and_false]
      cases effectiveIsAggregate ty <;> exact trivial
    | true =>
      rw [Bool.and_self, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      dsimp only
      have hgp_le : (neededRegsForClasses c0 c1).1 ≤ budget.gpFree := (nat_ble_true_iff _ _).mp hgp
      have hxmm_le : (neededRegsForClasses c0 c1).2 ≤ budget.xmmFree := (nat_ble_true_iff _ _).mp hxmm
      rw [takeNextGP_length hgp_b hgp_le, takeNextXMM_length hxmm_b hxmm_le]
      have h0 : (regUsageOfClass c0).1 + (regUsageOfClass c0).2 = 1 :=
        regUsageOfClass_non_empty hc0_ne hc0_nm
      have h1 : (regUsageOfClass c1).1 + (regUsageOfClass c1).2 = 1 :=
        regUsageOfClass_non_empty hc1_ne hc1_nm
      unfold neededRegsForClasses
      rw [Nat.add_assoc, Nat.add_left_comm (regUsageOfClass c1).1 (regUsageOfClass c0).2 (regUsageOfClass c1).2]
      rw [← Nat.add_assoc (regUsageOfClass c0).1 (regUsageOfClass c0).2 _]
      rw [h0, h1]

/-- Helper: extracts all assigned `GPReg`s in a parameter placement list. -/
noncomputable def collectGPRegs : List ParamStepResult → List GPReg
  | [] => []
  | s :: rest =>
    match s.placement with
    | .plRegs gps _ => gps ++ collectGPRegs rest
    | _ => collectGPRegs rest

/-- Helper: extracts all assigned `XMMReg`s in a parameter placement list. -/
noncomputable def collectXMMRegs : List ParamStepResult → List XMMReg
  | [] => []
  | s :: rest =>
    match s.placement with
    | .plRegs _ xmms => xmms ++ collectXMMRegs rest
    | _ => collectXMMRegs rest

/-- Theorem: every assigned GP register is drawn strictly from the prefix
`allGPRegs.drop (6 - budget.gpFree)` and the total count across `assignArgList`
equals `budget.gpFree - finalBudget.gpFree`, guaranteeing no GP register is
consumed past `0` or duplicated after rollback. -/
theorem assignArgList_gp_conservation {budget : RegBudget} {args : List AbiStructDesc}
    {optimize : Bool} (hgp_b : budget.gpFree ≤ 6) (hxmm_b : budget.xmmFree ≤ 8) :
    let res := assignArgList budget args optimize
    (collectGPRegs res.1).length + res.2.gpFree = budget.gpFree ∧
    (collectXMMRegs res.1).length + res.2.xmmFree = budget.xmmFree := by
  induction args generalizing budget with
  | nil =>
    exact ⟨Nat.zero_add _, Nat.zero_add _⟩
  | cons ty rest ih =>
    have hmon := assignArg_budget_monotone hgp_b hxmm_b (ty := ty) (optimize := optimize)
    have hcon := assignArg_conserves_registers hgp_b hxmm_b (ty := ty) (optimize := optimize)
    have htail := ih hmon.2.2.1 hmon.2.2.2
    unfold assignArgList
    dsimp only
    constructor
    · unfold collectGPRegs
      cases hpl : (assignArg budget ty optimize).placement with
      | plRegs gps _ =>
        rw [List.length_append, Nat.add_assoc, htail.1]
        have hstep : stepGPCount (assignArg budget ty optimize) = gps.length := by
          unfold stepGPCount; rw [hpl]
        rw [← hstep]
        exact hcon.1
      | plIgnore =>
        have hstep : stepGPCount (assignArg budget ty optimize) = 0 := by
          unfold stepGPCount; rw [hpl]
        rw [htail.1, ← Nat.zero_add ((assignArg budget ty optimize).nextBudget.gpFree), ← hstep]
        exact hcon.1
      | plStackByVal _ _ =>
        have hstep : stepGPCount (assignArg budget ty optimize) = 0 := by
          unfold stepGPCount; rw [hpl]
        rw [htail.1, ← Nat.zero_add ((assignArg budget ty optimize).nextBudget.gpFree), ← hstep]
        exact hcon.1
      | plStackScalar _ =>
        have hstep : stepGPCount (assignArg budget ty optimize) = 0 := by
          unfold stepGPCount; rw [hpl]
        rw [htail.1, ← Nat.zero_add ((assignArg budget ty optimize).nextBudget.gpFree), ← hstep]
        exact hcon.1
    · unfold collectXMMRegs
      cases hpl : (assignArg budget ty optimize).placement with
      | plRegs _ xmms =>
        rw [List.length_append, Nat.add_assoc, htail.2]
        have hstep : stepXMMCount (assignArg budget ty optimize) = xmms.length := by
          unfold stepXMMCount; rw [hpl]
        rw [← hstep]
        exact hcon.2
      | plIgnore =>
        have hstep : stepXMMCount (assignArg budget ty optimize) = 0 := by
          unfold stepXMMCount; rw [hpl]
        rw [htail.2, ← Nat.zero_add ((assignArg budget ty optimize).nextBudget.xmmFree), ← hstep]
        exact hcon.2
      | plStackByVal _ _ =>
        have hstep : stepXMMCount (assignArg budget ty optimize) = 0 := by
          unfold stepXMMCount; rw [hpl]
        rw [htail.2, ← Nat.zero_add ((assignArg budget ty optimize).nextBudget.xmmFree), ← hstep]
        exact hcon.2
      | plStackScalar _ =>
        have hstep : stepXMMCount (assignArg budget ty optimize) = 0 := by
          unfold stepXMMCount; rw [hpl]
        rw [htail.2, ← Nat.zero_add ((assignArg budget ty optimize).nextBudget.xmmFree), ← hstep]
        exact hcon.2

/-! ## Section 5: Bit-Exact Serialization Round-Trips (Eightbyte, `PairF32`, `Mixed`, `I128`, `TripleI`) -/

noncomputable def pow2_8 : Nat := 256
noncomputable def pow2_16 : Nat := 65536
noncomputable def pow2_24 : Nat := 16777216
noncomputable def pow2_32 : Nat := 4294967296
noncomputable def pow2_64 : Nat := 18446744073709551616
noncomputable def pow2_128 : Nat := 340282366920938463463374607431768211456

/-- Universal base-`B` packing/unpacking round-trip theorem (pure `Nat`, 0 axioms beyond `[propext]`). -/
theorem pack2_mod_div (a b base : Nat) (ha : a < base) (hb : 0 < base) :
    (a + base * b) % base = a ∧ (a + base * b) / base = b := by
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]

theorem pack2_lt_mul {a b baseA baseB : Nat} (ha : a < baseA) (hb : b < baseB) :
    a + baseA * b < baseA * baseB := by
  have hb_succ : b + 1 ≤ baseB := hb
  have hmul : baseA * (b + 1) ≤ baseA * baseB := Nat.mul_le_mul_left baseA hb_succ
  have hlt : a + baseA * b < baseA + baseA * b := Nat.add_lt_add_right ha (baseA * b)
  rw [Nat.add_comm baseA (baseA * b), ← Nat.mul_succ baseA b] at hlt
  exact Nat.lt_of_lt_of_le hlt hmul

/-- 3-byte aggregate modeling `#[repr(C)] struct Arr3U8([u8; 3])`. -/
structure Byte3 where
  b0 : Nat
  b1 : Nat
  b2 : Nat

noncomputable def Byte3.Valid (x : Byte3) : Prop :=
  x.b0 < 256 ∧ x.b1 < 256 ∧ x.b2 < 256

/-- Packs `Arr3U8` little-endian into 24-bit LLVM `i24` / `%edi`. -/
noncomputable def packArr3U8 (x : Byte3) : Nat :=
  x.b0 + 256 * (x.b1 + 256 * x.b2)

/-- Unpacks 24-bit `i24` / `%eax` back into `Arr3U8` bytes. -/
noncomputable def unpackArr3U8 (w : Nat) : Byte3 :=
  ⟨w % 256, (w / 256) % 256, (w / 65536) % 256⟩

theorem arr3U8_pack_lt_pow2_24 {x : Byte3} (hv : x.Valid) :
    packArr3U8 x < pow2_24 := by
  unfold packArr3U8 pow2_24
  have h12 : x.b1 + 256 * x.b2 < 256 * 256 := pack2_lt_mul hv.2.1 hv.2.2
  exact pack2_lt_mul hv.1 h12

theorem arr3U8_pack_unpack_roundtrip {x : Byte3} (hv : x.Valid) :
    unpackArr3U8 (packArr3U8 x) = x := by
  unfold unpackArr3U8 packArr3U8
  have h0 := pack2_mod_div x.b0 (x.b1 + 256 * x.b2) 256 hv.1 (by decide)
  have h1 := pack2_mod_div x.b1 x.b2 256 hv.2.1 (by decide)
  have hdiv : (x.b0 + 256 * (x.b1 + 256 * x.b2)) / 65536 = x.b2 := by
    change (x.b0 + 256 * (x.b1 + 256 * x.b2)) / (256 * 256) = x.b2
    rw [← Nat.div_div_eq_div_mul, h0.2, h1.2]
  rw [h0.1, h0.2, h1.1, hdiv, Nat.mod_eq_of_lt hv.2.2]

/-- Two 32-bit IEEE-754 float payloads in `#[repr(C)] struct PairF32 { a: f32, b: f32 }`. -/
structure PairF32Bits where
  aBits : Nat
  bBits : Nat

noncomputable def PairF32Bits.Valid (p : PairF32Bits) : Prop :=
  p.aBits < pow2_32 ∧ p.bBits < pow2_32

/-- Packs `PairF32` into the 64-bit `Reg::f64()` (`double` / `%xmm0[63:0]`) payload:
`a` occupies `[31:0]` and `b` occupies `[63:32]`. -/
noncomputable def packPairF32ToF64Bits (p : PairF32Bits) : Nat :=
  p.aBits + pow2_32 * p.bBits

/-- Extracts the low/high 32-bit `f32` payloads from the 64-bit `double` / `%xmm0[63:0]`. -/
noncomputable def unpackPairF32FromF64Bits (w : Nat) : PairF32Bits :=
  ⟨w % pow2_32, (w / pow2_32) % pow2_32⟩

theorem pairF32_pack_lt_pow2_64 {p : PairF32Bits} (hv : p.Valid) :
    packPairF32ToF64Bits p < pow2_64 := by
  unfold packPairF32ToF64Bits pow2_64
  exact pack2_lt_mul hv.1 hv.2

theorem pairF32_pack_unpack_roundtrip {p : PairF32Bits} (hv : p.Valid) :
    unpackPairF32FromF64Bits (packPairF32ToF64Bits p) = p := by
  unfold unpackPairF32FromF64Bits packPairF32ToF64Bits
  have h := pack2_mod_div p.aBits p.bBits pow2_32 hv.1 (by unfold pow2_32; decide)
  rw [h.1, h.2, Nat.mod_eq_of_lt hv.2]

/-- Concrete witness: `PairF32 { a: -0.0f (0x80000000), b: qNaN payload (0x7FC01234) }`
survives bit-exact `Reg::f64()` (`double`) packing without canonicalizing `-0.0` or NaN bits. -/
theorem pairF32_preserves_neg_zero_and_nan :
    let p : PairF32Bits := ⟨0x80000000, 0x7FC01234⟩
    unpackPairF32FromF64Bits (packPairF32ToF64Bits p) = p := by
  apply pairF32_pack_unpack_roundtrip
  exact ⟨by unfold pow2_32; decide, by unfold pow2_32; decide⟩

/-- Full 8-byte little-endian eightbyte representation. -/
structure Byte8 where
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  b5 : Nat
  b6 : Nat
  b7 : Nat

noncomputable def Byte8.Valid (x : Byte8) : Prop :=
  x.b0 < 256 ∧ x.b1 < 256 ∧ x.b2 < 256 ∧ x.b3 < 256 ∧
  x.b4 < 256 ∧ x.b5 < 256 ∧ x.b6 < 256 ∧ x.b7 < 256

/-- Packs 8 bytes little-endian into a 64-bit register word. -/
noncomputable def packByte8 (x : Byte8) : Nat :=
  let lo32 := x.b0 + 256 * (x.b1 + 256 * (x.b2 + 256 * x.b3))
  let hi32 := x.b4 + 256 * (x.b5 + 256 * (x.b6 + 256 * x.b7))
  lo32 + pow2_32 * hi32

/-- Unpacks a 64-bit register word into 8 little-endian bytes. -/
noncomputable def unpackByte8 (w : Nat) : Byte8 :=
  let lo32 := w % pow2_32
  let hi32 := (w / pow2_32) % pow2_32
  ⟨lo32 % 256, (lo32 / 256) % 256, (lo32 / 65536) % 256, (lo32 / 16777216) % 256,
   hi32 % 256, (hi32 / 256) % 256, (hi32 / 65536) % 256, (hi32 / 16777216) % 256⟩

theorem pack4_lt_pow2_32 {a b c d : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    a + 256 * (b + 256 * (c + 256 * d)) < pow2_32 := by
  unfold pow2_32
  have hcd : c + 256 * d < 256 * 256 := pack2_lt_mul hc hd
  have hbcd : b + 256 * (c + 256 * d) < 256 * (256 * 256) := pack2_lt_mul hb hcd
  exact pack2_lt_mul ha hbcd

theorem unpack_pack4_bytes {a b c d : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    let w := a + 256 * (b + 256 * (c + 256 * d))
    w % 256 = a ∧ (w / 256) % 256 = b ∧ (w / 65536) % 256 = c ∧ (w / 16777216) % 256 = d := by
  have h0 := pack2_mod_div a (b + 256 * (c + 256 * d)) 256 ha (by decide)
  have h1 := pack2_mod_div b (c + 256 * d) 256 hb (by decide)
  have h2 := pack2_mod_div c d 256 hc (by decide)
  have hd2 : (a + 256 * (b + 256 * (c + 256 * d))) / 65536 = c + 256 * d := by
    change (a + 256 * (b + 256 * (c + 256 * d))) / (256 * 256) = c + 256 * d
    rw [← Nat.div_div_eq_div_mul, h0.2, h1.2]
  have hd3 : (a + 256 * (b + 256 * (c + 256 * d))) / 16777216 = d := by
    change (a + 256 * (b + 256 * (c + 256 * d))) / (65536 * 256) = d
    rw [← Nat.div_div_eq_div_mul, hd2, h2.2]
  refine ⟨h0.1, ?_, ?_, ?_⟩
  · rw [h0.2, h1.1]
  · rw [hd2, h2.1]
  · rw [hd3, Nat.mod_eq_of_lt hd]

theorem byte8_pack_lt_pow2_64 {x : Byte8} (hv : x.Valid) :
    packByte8 x < pow2_64 := by
  unfold packByte8 pow2_64
  have hlo := pack4_lt_pow2_32 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
  have hhi := pack4_lt_pow2_32 hv.2.2.2.2.1 hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2
  exact pack2_lt_mul hlo hhi

theorem byte8_pack_unpack_roundtrip {x : Byte8} (hv : x.Valid) :
    unpackByte8 (packByte8 x) = x := by
  unfold unpackByte8 packByte8
  have hlo := pack4_lt_pow2_32 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
  have hhi := pack4_lt_pow2_32 hv.2.2.2.2.1 hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2
  have hsplit := pack2_mod_div
    (x.b0 + 256 * (x.b1 + 256 * (x.b2 + 256 * x.b3)))
    (x.b4 + 256 * (x.b5 + 256 * (x.b6 + 256 * x.b7)))
    pow2_32 hlo (by unfold pow2_32; decide)
  have ulo := unpack_pack4_bytes hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
  have uhi := unpack_pack4_bytes hv.2.2.2.2.1 hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2
  dsimp only
  rw [hsplit.1, hsplit.2, Nat.mod_eq_of_lt hhi]
  rw [ulo.1, ulo.2.1, ulo.2.2.1, ulo.2.2.2]
  rw [uhi.1, uhi.2.1, uhi.2.2.1, uhi.2.2.2]

/-- Memory representation of `#[repr(C)] struct Mixed { a: u8, b: u16, c: f64 }` (`16 B`),
explicitly modeling uninitialized padding byte `pad1` (offset `1`) and tail padding
bytes `pad4..pad7` (offsets `4..7`) in the low eightbyte! -/
structure MixedMem where
  a : Nat
  pad1 : Nat
  bLo : Nat
  bHi : Nat
  pad4 : Nat
  pad5 : Nat
  pad6 : Nat
  pad7 : Nat
  cBits : Nat

noncomputable def MixedMem.Valid (m : MixedMem) : Prop :=
  m.a < 256 ∧ m.pad1 < 256 ∧ m.bLo < 256 ∧ m.bHi < 256 ∧
  m.pad4 < 256 ∧ m.pad5 < 256 ∧ m.pad6 < 256 ∧ m.pad7 < 256 ∧ m.cBits < pow2_64

/-- Logical value of `Mixed` excluding padding bytes. -/
structure MixedVal where
  a : Nat
  b : Nat
  cBits : Nat

/-- Packs `MixedMem` into `{ i64, double }` (`(gp64, xmm64)`). -/
noncomputable def packMixedToRegPair (m : MixedMem) : Nat × Nat :=
  let eb0 : Byte8 := ⟨m.a, m.pad1, m.bLo, m.bHi, m.pad4, m.pad5, m.pad6, m.pad7⟩
  (packByte8 eb0, m.cBits)

/-- Unpacks `(gp64, xmm64)` back to logical `MixedVal`, ignoring padding bytes. -/
noncomputable def unpackMixedFromRegPair (regs : Nat × Nat) : MixedVal :=
  let eb0 := unpackByte8 regs.1
  ⟨eb0.b0, eb0.b2 + 256 * eb0.b3, regs.2⟩

/-- Theorem (Padding Invariance & Round-Trip): Unpacking `{ i64, double }` after packing
`Mixed` recovers exact `(a, bLo + 256 * bHi, cBits)` regardless of arbitrary uninitialized
padding bytes `pad1, pad4, pad5, pad6, pad7 < 256`! -/
theorem mixed_pack_unpack_padding_invariant (m : MixedMem) (hv : m.Valid) :
    unpackMixedFromRegPair (packMixedToRegPair m) =
      ⟨m.a, m.bLo + 256 * m.bHi, m.cBits⟩ := by
  unfold unpackMixedFromRegPair packMixedToRegPair
  have hv8 : Byte8.Valid ⟨m.a, m.pad1, m.bLo, m.bHi, m.pad4, m.pad5, m.pad6, m.pad7⟩ :=
    ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1⟩
  rw [byte8_pack_unpack_roundtrip hv8]

/-- 16-byte integer struct `#[repr(C)] struct PairI { a: u64, b: u64 }` / `{ i64, i64 }`. -/
structure PairIBits where
  a64 : Nat
  b64 : Nat

noncomputable def PairIBits.Valid (p : PairIBits) : Prop :=
  p.a64 < pow2_64 ∧ p.b64 < pow2_64

/-- Packs `PairI` into `(gp0, gp1)` `{ i64, i64 }` (canonicalizing each 64-bit register). -/
noncomputable def packPairIRegs (p : PairIBits) : Nat × Nat :=
  (p.a64 % pow2_64, p.b64 % pow2_64)

noncomputable def unpackPairIRegs (regs : Nat × Nat) : PairIBits :=
  ⟨regs.1 % pow2_64, regs.2 % pow2_64⟩

theorem pairI_pack_unpack_roundtrip {p : PairIBits} (hv : p.Valid) :
    unpackPairIRegs (packPairIRegs p) = p := by
  unfold unpackPairIRegs packPairIRegs
  rw [Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2]

/-- `I128` (`PassMode::Direct i128`) <-> `I128Struct` (`PassMode::Cast { i64, i64 }`)
split and reassembly equivalence. -/
noncomputable def splitU128ToPairI64 (x : Nat) : Nat × Nat :=
  (x % pow2_64, x / pow2_64)

noncomputable def joinPairI64ToU128 (pair : Nat × Nat) : Nat :=
  pair.1 + pow2_64 * pair.2

theorem i128_split_join_roundtrip {x : Nat} (hx : x < pow2_128) :
    joinPairI64ToU128 (splitU128ToPairI64 x) = x ∧
    (splitU128ToPairI64 x).1 < pow2_64 ∧
    (splitU128ToPairI64 x).2 < pow2_64 := by
  unfold joinPairI64ToU128 splitU128ToPairI64
  have hp64_pos : 0 < pow2_64 := by unfold pow2_64; decide
  have hdiv_lt : x / pow2_64 < pow2_64 := by
    have hmul : x < pow2_64 * pow2_64 := by
      change x < pow2_128
      exact hx
    exact (Nat.div_lt_iff_lt_mul hp64_pos).mpr hmul
  refine ⟨?_, Nat.mod_lt x hp64_pos, hdiv_lt⟩
  rw [Nat.add_comm]
  exact Nat.div_add_mod x pow2_64

theorem i128_join_split_roundtrip {lo hi : Nat} (hlo : lo < pow2_64) (hhi : hi < pow2_64) :
    splitU128ToPairI64 (joinPairI64ToU128 (lo, hi)) = (lo, hi) ∧
    joinPairI64ToU128 (lo, hi) < pow2_128 := by
  unfold splitU128ToPairI64 joinPairI64ToU128 pow2_128
  have hp64_pos : 0 < pow2_64 := by unfold pow2_64; decide
  have h := pack2_mod_div lo hi pow2_64 hlo hp64_pos
  have hlt := pack2_lt_mul hlo hhi
  change (if true then ((lo + pow2_64 * hi) % pow2_64, (lo + pow2_64 * hi) / pow2_64) else (0, 0)) = (lo, hi) ∧
    lo + pow2_64 * hi < pow2_64 * pow2_64
  rw [h.1, h.2]
  exact ⟨rfl, hlt⟩

/-- 24-byte `TripleI` stack buffer modeling `byval([24 x i8])` -> `sret([24 x i8])`. -/
structure TripleIBits where
  a64 : Nat
  b64 : Nat
  c64 : Nat

noncomputable def TripleIBits.Valid (t : TripleIBits) : Prop :=
  t.a64 < pow2_64 ∧ t.b64 < pow2_64 ∧ t.c64 < pow2_64

/-- Serializes `TripleI` into a contiguous 24-byte (192-bit) little-endian stack slice. -/
noncomputable def packTripleIStack (t : TripleIBits) : Nat :=
  t.a64 + pow2_64 * (t.b64 + pow2_64 * t.c64)

/-- Reads `TripleI` back from a 24-byte `byval` / `sret` memory slice. -/
noncomputable def unpackTripleIStack (buf : Nat) : TripleIBits :=
  ⟨buf % pow2_64, (buf / pow2_64) % pow2_64, (buf / pow2_128) % pow2_64⟩

theorem tripleI_stack_pack_unpack_roundtrip {t : TripleIBits} (hv : t.Valid) :
    unpackTripleIStack (packTripleIStack t) = t := by
  unfold unpackTripleIStack packTripleIStack
  have hp64_pos : 0 < pow2_64 := by unfold pow2_64; decide
  have h0 := pack2_mod_div t.a64 (t.b64 + pow2_64 * t.c64) pow2_64 hv.1 hp64_pos
  have h1 := pack2_mod_div t.b64 t.c64 pow2_64 hv.2.1 hp64_pos
  have hdiv : (t.a64 + pow2_64 * (t.b64 + pow2_64 * t.c64)) / pow2_128 = t.c64 := by
    change (t.a64 + pow2_64 * (t.b64 + pow2_64 * t.c64)) / (pow2_64 * pow2_64) = t.c64
    rw [← Nat.div_div_eq_div_mul, h0.2, h1.2]
  rw [h0.1, h0.2, h1.1, hdiv, Nat.mod_eq_of_lt hv.2.2]

/-! ## Section 6: Concrete Verified Corpus Instances (`rustc` + `gcc` Witness Checks) -/

noncomputable def tyEmpty : AbiStructDesc :=
  ⟨0, 1, .brMemory, .reprC, false, []⟩

noncomputable def tyS1 : AbiStructDesc :=
  ⟨8, 8, .brMemory, .reprC, false, [⟨0, 8, 8, .pInt64⟩]⟩

noncomputable def tyPairI : AbiStructDesc :=
  ⟨16, 8, .brMemory, .reprC, false, [⟨0, 8, 8, .pInt64⟩, ⟨8, 8, 8, .pInt64⟩]⟩

noncomputable def tyTripleI : AbiStructDesc :=
  ⟨24, 8, .brMemory, .reprC, false, [⟨0, 8, 8, .pInt64⟩, ⟨8, 8, 8, .pInt64⟩, ⟨16, 8, 8, .pInt64⟩]⟩

noncomputable def tyPairF32 : AbiStructDesc :=
  ⟨8, 4, .brMemory, .reprC, false, [⟨0, 4, 4, .pF32⟩, ⟨4, 4, 4, .pF32⟩]⟩

noncomputable def tyMixed : AbiStructDesc :=
  ⟨16, 8, .brMemory, .reprC, false, [⟨0, 1, 1, .pInt8⟩, ⟨2, 2, 2, .pInt16⟩, ⟨8, 8, 8, .pF64⟩]⟩

noncomputable def tyArr3U8 : AbiStructDesc :=
  ⟨3, 1, .brMemory, .reprC, false, [⟨0, 1, 1, .pInt8⟩, ⟨1, 1, 1, .pInt8⟩, ⟨2, 1, 1, .pInt8⟩]⟩

noncomputable def tyI128Struct : AbiStructDesc :=
  ⟨16, 16, .brMemory, .reprC, false, [⟨0, 16, 16, .pInt128⟩]⟩

noncomputable def tyBareU128 : AbiStructDesc :=
  ⟨16, 16, .brScalar, .reprRust, false, [⟨0, 16, 16, .pInt128⟩]⟩

noncomputable def tyTransparentU128 : AbiStructDesc :=
  ⟨16, 16, .brScalar, .reprTransparent, false, [⟨0, 16, 16, .pInt128⟩]⟩

noncomputable def tyPairU8F32 : AbiStructDesc :=
  ⟨8, 4, .brMemory, .reprC, false, [⟨0, 1, 1, .pInt8⟩, ⟨4, 4, 4, .pF32⟩]⟩

noncomputable def tyUnalignedPacked9 : AbiStructDesc :=
  ⟨9, 1, .brMemory, .reprC, false, [⟨0, 1, 1, .pInt8⟩, ⟨1, 8, 8, .pInt64⟩]⟩

noncomputable def tyPairF64 : AbiStructDesc :=
  ⟨16, 8, .brMemory, .reprC, false, [⟨0, 8, 8, .pF64⟩, ⟨8, 8, 8, .pF64⟩]⟩

noncomputable def tyScalarU64 : AbiStructDesc :=
  ⟨8, 8, .brScalar, .reprRust, false, [⟨0, 8, 8, .pInt64⟩]⟩

noncomputable def tyScalarF64 : AbiStructDesc :=
  ⟨8, 8, .brScalar, .reprRust, false, [⟨0, 8, 8, .pF64⟩]⟩

theorem witness_empty_ignore :
    passModeToLlvm (lowerClassifiedMode tyEmpty true true) = .llVoid ∧
    passModeToLlvm (lowerClassifiedMode tyEmpty false true) = .llVoid :=
  ⟨rfl, rfl⟩

theorem witness_s1_cast_i64 :
    lowerClassifiedMode tyS1 true true = .pmCast (.ctSingle (.rInt 64)) ∧
    passModeToLlvm (lowerClassifiedMode tyS1 true true) = .llInt 64 false :=
  ⟨rfl, rfl⟩

theorem witness_pairI_cast_pair_i64 :
    lowerClassifiedMode tyPairI true true = .pmCast (.ctPair (.rInt 64) (.rInt 64)) ∧
    passModeToLlvm (lowerClassifiedMode tyPairI true true) = .llStructPair (.llInt 64 false) (.llInt 64 false) :=
  ⟨rfl, rfl⟩

theorem witness_tripleI_sret_byval :
    lowerClassifiedMode tyTripleI false true = .pmIndirect 24 8 false ∧
    lowerClassifiedMode tyTripleI true true = .pmIndirect 24 8 true ∧
    passModeToLlvm (lowerClassifiedMode tyTripleI false true) = .llPtrSret 24 8 ∧
    passModeToLlvm (lowerClassifiedMode tyTripleI true true) = .llPtrByVal 24 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem witness_pairF32_cast_f64_double :
    lowerClassifiedMode tyPairF32 true true = .pmCast (.ctSingle .rF64) ∧
    passModeToLlvm (lowerClassifiedMode tyPairF32 true true) = .llF64 :=
  ⟨rfl, rfl⟩

theorem witness_mixed_cast_i64_f64 :
    lowerClassifiedMode tyMixed true true = .pmCast (.ctPair (.rInt 64) .rF64) ∧
    passModeToLlvm (lowerClassifiedMode tyMixed true true) = .llStructPair (.llInt 64 false) .llF64 :=
  ⟨rfl, rfl⟩

theorem witness_arr3U8_cast_i24 :
    lowerClassifiedMode tyArr3U8 true true = .pmCast (.ctSingle (.rInt 24)) ∧
    passModeToLlvm (lowerClassifiedMode tyArr3U8 true true) = .llInt 24 false :=
  ⟨rfl, rfl⟩

theorem witness_pairU8F32_int_dominates_to_i64 :
    lowerClassifiedMode tyPairU8F32 true true = .pmCast (.ctSingle (.rInt 64)) ∧
    passModeToLlvm (lowerClassifiedMode tyPairU8F32 true true) = .llInt 64 false :=
  ⟨rfl, rfl⟩

theorem witness_unalignedPacked9_sret_byval :
    lowerClassifiedMode tyUnalignedPacked9 false true = .pmIndirect 9 1 false ∧
    lowerClassifiedMode tyUnalignedPacked9 true true = .pmIndirect 9 1 true ∧
    passModeToLlvm (lowerClassifiedMode tyUnalignedPacked9 false true) = .llPtrSret 9 1 ∧
    passModeToLlvm (lowerClassifiedMode tyUnalignedPacked9 true true) = .llPtrByVal 9 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem witness_i128Struct_vs_bare_u128_and_transparent :
    lowerClassifiedMode tyI128Struct true true = .pmCast (.ctPair (.rInt 64) (.rInt 64)) ∧
    passModeToLlvm (lowerClassifiedMode tyI128Struct true true) = .llStructPair (.llInt 64 false) (.llInt 64 false) ∧
    lowerClassifiedMode tyBareU128 true true = .pmDirect 128 true ∧
    passModeToLlvm (lowerClassifiedMode tyBareU128 true true) = .llInt 128 true ∧
    lowerClassifiedMode tyTransparentU128 true true = .pmDirect 128 true ∧
    passModeToLlvm (lowerClassifiedMode tyTransparentU128 true true) = .llInt 128 true ∧
    neededRegsForClasses .Int .Int = (2, 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete kernel check reproducing `abi_gp_exhaust_rollback`:
5 GP scalars (`rdi..r8`), then `PairI` (needs 2 GP, only `r9` left -> rolls back to `byval([16 x i8])`),
then `backfill_r9` occupies `%r9`! -/
theorem witness_gp_exhaust_rollback_and_backfill_r9 :
    let fnRes := assignFnAbi tyScalarU64
      [tyScalarU64, tyScalarU64, tyScalarU64, tyScalarU64, tyScalarU64, tyPairI, tyScalarU64] true
    let steps := fnRes.2.1
    let finalBudget := fnRes.2.2
    (steps.map ParamStepResult.placement) =
      [.plRegs [.rdi] [], .plRegs [.rsi] [], .plRegs [.rdx] [], .plRegs [.rcx] [], .plRegs [.r8] [],
       .plStackByVal 16 8, .plRegs [.r9] []] ∧
    finalBudget = ⟨0, 8⟩ :=
  ⟨rfl, rfl⟩

/-- Concrete kernel check reproducing `abi_xmm_exhaust_rollback`:
7 `f64` scalars (`xmm0..xmm6`), then `PairF64` (needs 2 XMM, only `xmm7` left -> rolls back to `byval`),
then `backfill_xmm7` occupies `%xmm7`! -/
theorem witness_xmm_exhaust_rollback_and_backfill_xmm7 :
    let fnRes := assignFnAbi tyScalarF64
      [tyScalarF64, tyScalarF64, tyScalarF64, tyScalarF64, tyScalarF64, tyScalarF64, tyScalarF64,
       tyPairF64, tyScalarF64] true
    let steps := fnRes.2.1
    let finalBudget := fnRes.2.2
    (steps.map ParamStepResult.placement) =
      [.plRegs [] [.xmm0], .plRegs [] [.xmm1], .plRegs [] [.xmm2], .plRegs [] [.xmm3],
       .plRegs [] [.xmm4], .plRegs [] [.xmm5], .plRegs [] [.xmm6],
       .plStackByVal 16 8, .plRegs [] [.xmm7]] ∧
    finalBudget = ⟨6, 0⟩ :=
  ⟨rfl, rfl⟩

/-- Concrete kernel check reproducing `abi_mixed_gp_exhaust_rollback`:
6 GP scalars exhaust `rdi..r9` (`gpFree = 0, xmmFree = 8`), then `Mixed` (`Int, Sse`)
needs `(1 GP, 1 XMM)` -> rolls back completely to `byval` WITHOUT touching `xmmFree`,
so `backfill_xmm0` receives `%xmm0`! -/
theorem witness_mixed_gp_exhaust_rollback_and_backfill_xmm0 :
    let fnRes := assignFnAbi tyScalarF64
      [tyScalarU64, tyScalarU64, tyScalarU64, tyScalarU64, tyScalarU64, tyScalarU64,
       tyMixed, tyScalarF64] true
    let steps := fnRes.2.1
    let finalBudget := fnRes.2.2
    (steps.map ParamStepResult.placement) =
      [.plRegs [.rdi] [], .plRegs [.rsi] [], .plRegs [.rdx] [], .plRegs [.rcx] [],
       .plRegs [.r8] [], .plRegs [.r9] [],
       .plStackByVal 16 8, .plRegs [] [.xmm0]] ∧
    finalBudget = ⟨0, 7⟩ :=
  ⟨rfl, rfl⟩

end SysvX8664Abi
