/-!
# Sizedness hierarchy, `extern type` tail offsets, and retag range independence

A self-contained Lean 4 model (core library only, no imports) of four facts about
Rust's `Sized < MetaSized < PointeeSized` hierarchy and `extern type` tails:

1. `metaSized_implies_total_runtime_layout`: the runtime size/alignment function
   (`size_and_align_from_meta` in the interpreter, `size_and_align_of_dst` in
   codegen) is total on `MetaSized` types, and returns nothing on every other
   type, so desugaring `?Sized` to `MetaSized` makes `size_of_val` total.
2. `extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization` and its
   generalisation `extern_tail_offset_static_iff`: the byte offset of an
   `extern type` tail is independent of the unknown foreign alignment exactly
   when the static prefix offset is `0` or the struct is `packed(N)` with `N`
   dividing that offset (`N = 1` always qualifies).  The projection implemented
   by the compiler takes the static path only for offset `0`.
3. `tree_borrows_reborrow_sound_without_pointee_size`: a Tree Borrows retag of a
   reference whose pointee has an `extern type` tail assigns, byte for byte, the
   location state that a retag knowing the true extent would assign.
4. Sharpness counterexamples `ce1_…`, `ce2_…`, `ce3_…`.

The file uses no proof holes, no classical axioms, no arithmetic decision
procedures, no bit-blasting, no compiled evaluation, and no general recursion:
recursive functions over the recursive type `Ty` are structural and marked
`noncomputable`, and no instance is derived for `Ty`.
-/

namespace SizedHierarchyAndExternTailSoundness

/-! ## 0. Two rewriting lemmas for `if` -/

theorem ite_of_pos {α : Type} {c : Prop} [inst : Decidable c] (t e : α) (hc : c) :
    (if c then t else e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd hc hn

theorem ite_of_neg {α : Type} {c : Prop} [inst : Decidable c] (t e : α) (hc : ¬ c) :
    (if c then t else e) = e := by
  cases inst with
  | isTrue h => exact absurd h hc
  | isFalse _ => rfl

/-! ## 1. Sizedness traits, tiers, and types -/

/-- The three sizedness traits.  `Sized: MetaSized` and `MetaSized: PointeeSized`
are supertrait edges. -/
inductive SizedTrait where
  | sized
  | metaSized
  | pointeeSized

/-- The strongest sizedness trait a concrete type implements. -/
inductive Tier where
  | sized
  | metaSized
  | pointeeSizedOnly

/-- Builtin implementations: which trait each tier satisfies. -/
def Tier.implements : Tier → SizedTrait → Bool
  | .sized, _ => true
  | .metaSized, .sized => false
  | .metaSized, _ => true
  | .pointeeSizedOnly, .pointeeSized => true
  | .pointeeSizedOnly, _ => false

/-- Types of the modelled fragment.

* `scalar size align`: any `Sized` type, by its static size and alignment.
* `slice elemSize elemAlign`: `[T]` / `str`; pointer metadata is a length.
* `dyn`: `dyn Trait`; pointer metadata is a vtable carrying size and alignment.
* `foreign`: an `extern type`; pointer metadata is `()` and nothing is known.
* `adt pack tailOffset prefixAlign tail`: a struct (or tuple) whose last field has
  type `tail`.  `tailOffset` is the static offset the layout assigns to that
  field *before* any adjustment to the tail's dynamic alignment, `prefixAlign`
  is the static alignment of the type, and `pack` is `some N` for `packed(N)`. -/
inductive Ty where
  | scalar (size align : Nat)
  | slice (elemSize elemAlign : Nat)
  | dyn
  | foreign
  | adt (pack : Option Nat) (tailOffset prefixAlign : Nat) (tail : Ty)

/-- The tier of a type is the tier of its struct tail. -/
noncomputable def Ty.tier : Ty → Tier
  | .scalar _ _ => .sized
  | .slice _ _ => .metaSized
  | .dyn => .metaSized
  | .foreign => .pointeeSizedOnly
  | .adt _ _ _ tail => tail.tier

/-- `ty: tr` holds. -/
def Implements (ty : Ty) (tr : SizedTrait) : Prop :=
  ty.tier.implements tr = true

theorem Tier.sized_implies_metaSized (t : Tier) :
    t.implements .sized = true → t.implements .metaSized = true := by
  cases t
  · intro _; rfl
  · intro h; cases h
  · intro h; cases h

theorem Tier.metaSized_implies_pointeeSized (t : Tier) :
    t.implements .metaSized = true → t.implements .pointeeSized = true := by
  cases t
  · intro _; rfl
  · intro _; rfl
  · intro h; cases h

/-- Supertrait edge `Sized: MetaSized`. -/
theorem sized_implies_metaSized (ty : Ty) :
    Implements ty .sized → Implements ty .metaSized :=
  Tier.sized_implies_metaSized ty.tier

/-- Supertrait edge `MetaSized: PointeeSized`. -/
theorem metaSized_implies_pointeeSized (ty : Ty) :
    Implements ty .metaSized → Implements ty .pointeeSized :=
  Tier.metaSized_implies_pointeeSized ty.tier

/-- `PointeeSized` is the top of the hierarchy: every type implements it. -/
theorem every_type_is_pointeeSized (ty : Ty) : Implements ty .pointeeSized := by
  unfold Implements
  cases ty.tier <;> rfl

/-- The hierarchy is strict at the first edge: a slice is `MetaSized`, not `Sized`. -/
theorem slice_is_metaSized_not_sized (es ea : Nat) :
    Implements (.slice es ea) .metaSized ∧ ¬ Implements (.slice es ea) .sized :=
  ⟨rfl, fun h => (by cases h)⟩

/-- The hierarchy is strict at the second edge: an `extern type` is
`PointeeSized`, not `MetaSized`. -/
theorem foreign_is_pointeeSized_not_metaSized :
    Implements .foreign .pointeeSized ∧ ¬ Implements .foreign .metaSized :=
  ⟨rfl, fun h => (by cases h)⟩

/-- A struct inherits the tier of its tail: with an `extern type` tail it is not
`MetaSized`, whatever its prefix and `repr`. -/
theorem adt_with_foreign_tail_not_metaSized (pack : Option Nat) (off pa : Nat) :
    ¬ Implements (.adt pack off pa .foreign) .metaSized :=
  fun h => by cases h

/-! ### Surface bounds -/

/-- A sizedness bound as written on a type parameter. -/
inductive Bound where
  /-- No sizedness bound written. -/
  | implicitDefault
  /-- `?Sized`. -/
  | questionSized
  /-- An explicit `Sized`, `MetaSized` or `PointeeSized` bound. -/
  | explicit (tr : SizedTrait)

/-- The trait obligation a written bound lowers to: a parameter without a
sizedness bound gets `Sized`, and `?Sized` is equivalent to `MetaSized`. -/
def Bound.desugar : Bound → SizedTrait
  | .implicitDefault => .sized
  | .questionSized => .metaSized
  | .explicit tr => tr

/-- The counterfactual reading in which `?Sized` removes every sizedness
obligation (the only reading available before the hierarchy existed). -/
def Bound.desugarWithoutHierarchy : Bound → SizedTrait
  | .implicitDefault => .sized
  | .questionSized => .pointeeSized
  | .explicit tr => tr

/-- `?Sized` rejects `extern type`s and every struct ending in one. -/
theorem questionSized_rejects_foreign_tails (pack : Option Nat) (off pa : Nat) :
    ¬ Implements .foreign (Bound.desugar .questionSized) ∧
    ¬ Implements (.adt pack off pa .foreign) (Bound.desugar .questionSized) :=
  ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-! ## 2. Pointer metadata and pointer width -/

/-- Pointer metadata values. -/
inductive Meta where
  | unit
  | length (n : Nat)
  | vtable (size align : Nat)

/-- Kinds of pointer metadata. -/
inductive MetaKind where
  | thin
  | length
  | vtable

def Meta.kind : Meta → MetaKind
  | .unit => .thin
  | .length _ => .length
  | .vtable _ _ => .vtable

/-- Metadata kind of a pointee type: that of its struct tail; `()` for `Sized`
types and for `extern type`s. -/
noncomputable def Ty.metaKind : Ty → MetaKind
  | .scalar _ _ => .thin
  | .slice _ _ => .length
  | .dyn => .vtable
  | .foreign => .thin
  | .adt _ _ _ tail => tail.metaKind

/-- Width of a pointer to the type, in machine words. -/
noncomputable def Ty.ptrWords (ty : Ty) : Nat :=
  match ty.metaKind with
  | .thin => 1
  | .length => 2
  | .vtable => 2

/-- Metadata `m` is well-typed for pointee `ty`. -/
def MetaFor (ty : Ty) (m : Meta) : Prop :=
  m.kind = ty.metaKind

/-- A pointer is thin exactly when its pointee is *not* in the middle tier:
`Sized` types and `extern type` tails both give one-word pointers, so pointer
width cannot tell a `Sized` pointee from a `PointeeSized`-only one. -/
theorem thin_pointer_iff_not_strictly_metaSized (ty : Ty) :
    ty.ptrWords = 1 ↔ ty.tier.implements .metaSized = ty.tier.implements .sized := by
  induction ty with
  | scalar s a => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | slice es ea =>
    show (2 : Nat) = 1 ↔ true = false
    exact ⟨fun h => absurd h (by decide), fun h => (by cases h)⟩
  | dyn =>
    show (2 : Nat) = 1 ↔ true = false
    exact ⟨fun h => absurd h (by decide), fun h => (by cases h)⟩
  | foreign => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | adt pack off pa tail ih => exact ih

/-- Concrete instance: both ends of the hierarchy have thin pointers, the middle
tier has wide pointers. -/
theorem pointer_width_examples (pack : Option Nat) (off pa : Nat) :
    (Ty.scalar 4 4).ptrWords = 1 ∧ Ty.foreign.ptrWords = 1 ∧
    (Ty.adt pack off pa .foreign).ptrWords = 1 ∧
    (Ty.slice 4 4).ptrWords = 2 ∧ Ty.dyn.ptrWords = 2 ∧
    (Ty.adt pack off pa (.slice 4 4)).ptrWords = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Runtime layout from metadata -/

/-- Round `off` up to the next multiple of `a` (for `a > 0`). -/
def alignUp (off a : Nat) : Nat :=
  if off % a = 0 then off else off + (a - off % a)

/-- Alignment cap applied to the unsized field of a `packed(N)` struct. -/
def capAlign (pack : Option Nat) (a : Nat) : Nat :=
  match pack with
  | none => a
  | some p => min a p

/-- Dynamic size and alignment of a value from its pointer metadata.  Returns
`none` when an `extern type` is reached (or the metadata is ill-typed). -/
noncomputable def Ty.sizeAlign : Ty → Meta → Option (Nat × Nat)
  | .scalar s a, _ => some (s, a)
  | .slice es ea, .length n => some (n * es, ea)
  | .slice _ _, _ => none
  | .dyn, .vtable s a => some (s, a)
  | .dyn, _ => none
  | .foreign, _ => none
  | .adt pack off pa tail, m =>
    match tail.sizeAlign m with
    | none => none
    | some (ts, ta) =>
      some (alignUp (alignUp off (capAlign pack ta) + ts) (max pa (capAlign pack ta)),
            max pa (capAlign pack ta))

/-- **Totality on `MetaSized`.**  Every `MetaSized` type has a runtime size and
alignment for every well-typed metadata value. -/
theorem metaSized_implies_total_runtime_layout (ty : Ty) (m : Meta)
    (hTier : Implements ty .metaSized) (hMeta : MetaFor ty m) :
    ∃ sa, ty.sizeAlign m = some sa := by
  induction ty with
  | scalar s a => exact ⟨(s, a), rfl⟩
  | slice es ea =>
    cases m with
    | unit => cases hMeta
    | length n => exact ⟨(n * es, ea), rfl⟩
    | vtable s a => cases hMeta
  | dyn =>
    cases m with
    | unit => cases hMeta
    | length n => cases hMeta
    | vtable s a => exact ⟨(s, a), rfl⟩
  | foreign => cases hTier
  | adt pack off pa tail ih =>
    cases ih hTier hMeta with
    | intro sa h =>
      cases sa with
      | mk ts ta =>
        exact ⟨(alignUp (alignUp off (capAlign pack ta) + ts) (max pa (capAlign pack ta)),
                max pa (capAlign pack ta)), by simp only [Ty.sizeAlign, h]⟩

/-- **No layout outside `MetaSized`.**  A type that is not `MetaSized` has no
runtime size or alignment for any metadata value. -/
theorem not_metaSized_implies_no_runtime_layout (ty : Ty) (m : Meta)
    (hTier : ¬ Implements ty .metaSized) : ty.sizeAlign m = none := by
  induction ty with
  | scalar s a => exact absurd rfl hTier
  | slice es ea => exact absurd rfl hTier
  | dyn => exact absurd rfl hTier
  | foreign => rfl
  | adt pack off pa tail ih =>
    have h : tail.sizeAlign m = none := ih hTier
    simp only [Ty.sizeAlign, h]

/-- Some well-typed metadata exists for every type. -/
noncomputable def Ty.someMeta : Ty → Meta
  | .scalar _ _ => .unit
  | .slice _ _ => .length 0
  | .dyn => .vtable 0 1
  | .foreign => .unit
  | .adt _ _ _ tail => tail.someMeta

theorem Ty.someMeta_wellTyped (ty : Ty) : MetaFor ty ty.someMeta := by
  induction ty with
  | scalar s a => rfl
  | slice es ea => rfl
  | dyn => rfl
  | foreign => rfl
  | adt pack off pa tail ih => exact ih

/-- `MetaSized` is exactly the class of types whose runtime layout is total. -/
theorem runtime_layout_total_iff_metaSized (ty : Ty) :
    (∀ m, MetaFor ty m → ∃ sa, ty.sizeAlign m = some sa) ↔ Implements ty .metaSized := by
  constructor
  · intro h
    cases hb : ty.tier.implements .metaSized with
    | true => exact hb
    | false =>
      have hNot : ¬ Implements ty .metaSized := by
        intro hi
        unfold Implements at hi
        rw [hb] at hi
        cases hi
      have hNone := not_metaSized_implies_no_runtime_layout ty ty.someMeta hNot
      cases h ty.someMeta ty.someMeta_wellTyped with
      | intro sa hsa =>
        rw [hNone] at hsa
        cases hsa
  · intro hTier m hMeta
    exact metaSized_implies_total_runtime_layout ty m hTier hMeta

/-! ### `size_of_val` -/

/-- Result of an operation that the compiler may refuse at run time. -/
inductive Outcome (α : Type) where
  /-- The operation produced a value. -/
  | value (a : α)
  /-- Compiled code: a non-unwinding panic, i.e. a process abort. -/
  | panicNounwind
  /-- Interpreter: an "unsupported operation" error. -/
  | unsupported

/-- `size_of_val` as compiled: reaching an `extern type` emits a call to the
non-unwinding panic entry point. -/
noncomputable def sizeOfValRuntime (ty : Ty) (m : Meta) : Outcome Nat :=
  match ty.sizeAlign m with
  | some (s, _) => .value s
  | none => .panicNounwind

/-- With `?Sized` lowered to `MetaSized`, every type accepted by
`fn size_of_val<T: ?Sized>` yields a value. -/
theorem size_of_val_total_under_questionSized (ty : Ty) (m : Meta)
    (hBound : Implements ty (Bound.desugar .questionSized)) (hMeta : MetaFor ty m) :
    ∃ s, sizeOfValRuntime ty m = .value s := by
  cases metaSized_implies_total_runtime_layout ty m hBound hMeta with
  | intro sa h =>
    cases sa with
    | mk s a => exact ⟨s, by simp only [sizeOfValRuntime, h]⟩

/-- **Counterexample 1.**  If `?Sized` admitted every `PointeeSized` type, an
`extern type` (and a struct ending in one) would satisfy the bound of
`size_of_val` with well-typed metadata and the call would abort. -/
theorem ce1_question_sized_as_pointee_sized_panics_size_of_val :
    (Implements .foreign (Bound.desugarWithoutHierarchy .questionSized) ∧
      MetaFor .foreign .unit ∧
      sizeOfValRuntime .foreign .unit = .panicNounwind) ∧
    (∀ (pack : Option Nat) (off pa : Nat),
      Implements (.adt pack off pa .foreign) (Bound.desugarWithoutHierarchy .questionSized) ∧
      MetaFor (.adt pack off pa .foreign) .unit ∧
      sizeOfValRuntime (.adt pack off pa .foreign) .unit = .panicNounwind) :=
  ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

/-! ## 4. Offset of an `extern type` tail -/

/-- Admissible alignments are powers of two. -/
def IsPow2 (a : Nat) : Prop :=
  ∃ k, a = 2 ^ k

theorem IsPow2.pos {a : Nat} (h : IsPow2 a) : 0 < a := by
  cases h with
  | intro k hk =>
    rw [hk]
    exact Nat.pow_pos (by decide)

theorem isPow2_one : IsPow2 1 :=
  ⟨0, rfl⟩

/-- Byte offset of the unsized tail when its actual alignment is `tailAlign`:
the static offset rounded up to the (pack-capped) alignment. -/
def tailOffset (off : Nat) (pack : Option Nat) (tailAlign : Nat) : Nat :=
  alignUp off (capAlign pack tailAlign)

/-- The tail offset is *static*: every admissible alignment of the foreign type
gives the same offset, so it can be computed without knowing that alignment. -/
def OffsetStatic (off : Nat) (pack : Option Nat) : Prop :=
  ∀ a b, IsPow2 a → IsPow2 b → tailOffset off pack a = tailOffset off pack b

theorem alignUp_of_mod_eq_zero {off a : Nat} (h : off % a = 0) : alignUp off a = off := by
  unfold alignUp
  rw [ite_of_pos _ _ h]

theorem alignUp_zero (a : Nat) : alignUp 0 a = 0 :=
  alignUp_of_mod_eq_zero (Nat.zero_mod a)

theorem alignUp_one (off : Nat) : alignUp off 1 = off :=
  alignUp_of_mod_eq_zero (Nat.mod_one off)

theorem mod_eq_zero_of_alignUp_eq_self {off a : Nat} (ha : 0 < a) (h : alignUp off a = off) :
    off % a = 0 := by
  unfold alignUp at h
  cases Nat.decEq (off % a) 0 with
  | isTrue hz => exact hz
  | isFalse hnz =>
    rw [ite_of_neg _ _ hnz] at h
    have hlt : off % a < a := Nat.mod_lt off ha
    have hpos : 0 < a - off % a := Nat.sub_pos_of_lt hlt
    have hgt : off < off + (a - off % a) := Nat.lt_add_of_pos_right hpos
    rw [h] at hgt
    exact absurd hgt (Nat.lt_irrefl off)

/-- Rounding a positive offset up to a strictly larger alignment lands on that
alignment. -/
theorem alignUp_of_pos_of_lt {off a : Nat} (hpos : 0 < off) (hlt : off < a) :
    alignUp off a = a := by
  unfold alignUp
  have hmod : off % a = off := Nat.mod_eq_of_lt hlt
  have hne : ¬ off % a = 0 := by
    rw [hmod]
    exact Nat.ne_of_gt hpos
  rw [ite_of_neg _ _ hne, hmod]
  exact Nat.add_sub_cancel' (Nat.le_of_lt hlt)

theorem two_pow_lt_two_pow_succ (j : Nat) : 2 ^ j < 2 ^ (j + 1) := by
  rw [Nat.pow_succ, Nat.mul_two]
  exact Nat.lt_add_of_pos_right (Nat.pow_pos (by decide))

/-- Powers of two are ordered like their exponents (proved directly; the
library lemma for this fact is not choice-free). -/
theorem le_of_two_pow_le {i j : Nat} (h : 2 ^ i ≤ 2 ^ j) : i ≤ j := by
  cases Nat.lt_or_ge j i with
  | inl hlt =>
    have h1 : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hlt
    have h2 : 2 ^ (j + 1) ≤ 2 ^ j := Nat.le_trans h1 h
    exact absurd (Nat.lt_of_lt_of_le (two_pow_lt_two_pow_succ j) h2) (Nat.lt_irrefl _)
  | inr hge => exact hge

/-- The smaller of two powers of two divides the second. -/
theorem min_pow2_dvd {a p : Nat} (ha : IsPow2 a) (hp : IsPow2 p) : min a p ∣ p := by
  cases ha with
  | intro i hi =>
    cases hp with
    | intro j hj =>
      rw [hi, hj]
      cases Nat.le_total (2 ^ i) (2 ^ j) with
      | inl hle =>
        rw [Nat.min_eq_left hle]
        exact Nat.pow_dvd_pow 2 (le_of_two_pow_le hle)
      | inr hge =>
        rw [Nat.min_eq_right hge]
        exact Nat.dvd_refl _

theorem min_one_pow2 {p : Nat} (hp : IsPow2 p) : min 1 p = 1 :=
  Nat.min_eq_left hp.pos

/-- **Tail-offset computability, general form.**  With `packed(N)` restricted to
powers of two, the offset of an `extern type` tail is static exactly when the
static prefix offset is `0`, or the struct is `packed(N)` and `N` divides the
static prefix offset. -/
theorem extern_tail_offset_static_iff (off : Nat) (pack : Option Nat)
    (hpack : ∀ p, pack = some p → IsPow2 p) :
    OffsetStatic off pack ↔ (off = 0 ∨ ∃ p, pack = some p ∧ off % p = 0) := by
  constructor
  · intro hstat
    cases pack with
    | none =>
      cases off with
      | zero => exact Or.inl rfl
      | succ n =>
        have h := hstat 1 (2 ^ (n + 1)) isPow2_one ⟨n + 1, rfl⟩
        have h1 : tailOffset (n + 1) none 1 = n + 1 := alignUp_one (n + 1)
        have h2 : tailOffset (n + 1) none (2 ^ (n + 1)) = 2 ^ (n + 1) :=
          alignUp_of_pos_of_lt (Nat.succ_pos n) Nat.lt_two_pow_self
        rw [h1, h2] at h
        have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
        rw [← h] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
    | some p =>
      have hp : IsPow2 p := hpack p rfl
      have h := hstat 1 p isPow2_one hp
      have h1 : tailOffset off (some p) 1 = off := by
        show alignUp off (min 1 p) = off
        rw [min_one_pow2 hp]
        exact alignUp_one off
      have h2 : tailOffset off (some p) p = alignUp off p := by
        show alignUp off (min p p) = alignUp off p
        rw [Nat.min_self]
      rw [h1, h2] at h
      exact Or.inr ⟨p, rfl, mod_eq_zero_of_alignUp_eq_self hp.pos h.symm⟩
  · intro h a b ha hb
    cases h with
    | inl hz =>
      rw [hz]
      show alignUp 0 _ = alignUp 0 _
      rw [alignUp_zero, alignUp_zero]
    | inr hex =>
      cases hex with
      | intro p hp =>
        cases hp with
        | intro hpk hmod =>
          have hp2 : IsPow2 p := hpack p hpk
          have key : ∀ c, IsPow2 c → tailOffset off pack c = off := by
            intro c hc
            rw [hpk]
            show alignUp off (min c p) = off
            have hdvd : min c p ∣ off :=
              Nat.dvd_trans (min_pow2_dvd hc hp2) (Nat.dvd_of_mod_eq_zero hmod)
            exact alignUp_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd hdvd)
          rw [key a ha, key b hb]

/-- **Tail-offset computability for the two layouts a static fast path can key
on.**  For an unpacked or a `packed(1)` struct, the offset of an `extern type`
tail is static exactly when the static prefix offset is `0` or the struct is
`packed(1)`. -/
theorem extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization
    (off : Nat) (pack : Option Nat) (hrepr : pack = none ∨ pack = some 1) :
    OffsetStatic off pack ↔ (off = 0 ∨ pack = some 1) := by
  have hpack : ∀ p, pack = some p → IsPow2 p := by
    intro p hp
    cases hrepr with
    | inl hn => rw [hn] at hp; cases hp
    | inr h1 =>
      rw [h1] at hp
      cases hp
      exact isPow2_one
  rw [extern_tail_offset_static_iff off pack hpack]
  constructor
  · intro h
    cases h with
    | inl hz => exact Or.inl hz
    | inr hex =>
      cases hex with
      | intro p hp =>
        cases hrepr with
        | inl hn => rw [hn] at hp; cases hp.1
        | inr h1 => exact Or.inr h1
  · intro h
    cases h with
    | inl hz => exact Or.inl hz
    | inr h1 => exact Or.inr ⟨1, h1, Nat.mod_one off⟩

/-- `packed(1)` always gives a static tail offset, equal to the static offset. -/
theorem packed1_tail_offset_static (off : Nat) : OffsetStatic off (some 1) :=
  (extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization off (some 1)
    (Or.inr rfl)).mpr (Or.inr rfl)

/-- An unpacked struct has a static tail offset only at offset `0`. -/
theorem unpacked_tail_offset_static_iff_zero (off : Nat) : OffsetStatic off none ↔ off = 0 := by
  rw [extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization off none (Or.inl rfl)]
  constructor
  · intro h
    cases h with
    | inl hz => exact hz
    | inr hp => cases hp
  · intro hz
    exact Or.inl hz

/-- The dichotomy "offset `0` or `packed(1)`" is not the whole story for
`packed(N)` with `N > 1`: offset `4` under `packed(2)` is static, offset `6`
under `packed(4)` is not. -/
theorem packedN_examples :
    OffsetStatic 4 (some 2) ∧ ¬ OffsetStatic 6 (some 4) := by
  have hp2 : ∀ p, some 2 = some p → IsPow2 p := by
    intro p hp
    cases hp
    exact ⟨1, rfl⟩
  have hp4 : ∀ p, some 4 = some p → IsPow2 p := by
    intro p hp
    cases hp
    exact ⟨2, rfl⟩
  constructor
  · exact (extern_tail_offset_static_iff 4 (some 2) hp2).mpr (Or.inr ⟨2, rfl, by decide⟩)
  · intro h
    cases (extern_tail_offset_static_iff 6 (some 4) hp4).mp h with
    | inl hz => cases hz
    | inr hex =>
      cases hex with
      | intro p hp =>
        cases hp with
        | intro hpk hmod =>
          cases hpk
          revert hmod
          decide

/-! ### The projections the compiler implements -/

/-- Field projection to the unsized tail as compiled.  Sized, slice and `str`
tails, and any tail at static offset `0`, take the static path; every other
tail first asks for the tail's dynamic alignment, which for an `extern type`
is a call to the non-unwinding panic entry point. -/
noncomputable def codegenProjectTail (off : Nat) (pack : Option Nat) (tail : Ty) (m : Meta) :
    Outcome Nat :=
  match tail with
  | .scalar _ _ => .value off
  | .slice _ _ => .value off
  | .dyn | .foreign | .adt _ _ _ _ =>
    if off = 0 then .value 0
    else
      match tail.sizeAlign m with
      | none => .panicNounwind
      | some (_, a) => .value (alignUp off (capAlign pack a))

/-- Field projection to the unsized tail as interpreted.  A tail with no dynamic
alignment is projected only at static offset `0`. -/
noncomputable def interpProjectTail (off : Nat) (pack : Option Nat) (tail : Ty) (m : Meta) :
    Outcome Nat :=
  match tail with
  | .scalar _ _ => .value off
  | .slice _ _ | .dyn | .foreign | .adt _ _ _ _ =>
    match tail.sizeAlign m with
    | some (_, a) => .value (alignUp off (capAlign pack a))
    | none => if off = 0 then .value 0 else .unsupported

/-- Compiled projection to an `extern type` tail: a value at offset `0`. -/
theorem codegen_foreign_tail_zero_offset (pack : Option Nat) (m : Meta) :
    codegenProjectTail 0 pack .foreign m = .value 0 :=
  rfl

/-- Compiled projection to an `extern type` tail: an abort at every non-zero
static offset, for every `repr`. -/
theorem codegen_foreign_tail_nonzero_offset_aborts (off : Nat) (pack : Option Nat) (m : Meta)
    (h : off ≠ 0) : codegenProjectTail off pack .foreign m = .panicNounwind := by
  show (if off = 0 then Outcome.value 0 else Outcome.panicNounwind) = Outcome.panicNounwind
  rw [ite_of_neg _ _ h]

/-- Interpreted projection to an `extern type` tail: unsupported at every
non-zero static offset, for every `repr`. -/
theorem interp_foreign_tail_nonzero_offset_unsupported (off : Nat) (pack : Option Nat) (m : Meta)
    (h : off ≠ 0) : interpProjectTail off pack .foreign m = .unsupported := by
  show (if off = 0 then Outcome.value 0 else Outcome.unsupported) = Outcome.unsupported
  rw [ite_of_neg _ _ h]

theorem interp_foreign_tail_zero_offset (pack : Option Nat) (m : Meta) :
    interpProjectTail 0 pack .foreign m = .value 0 :=
  rfl

/-- The compiled projection aborts on an `extern type` tail exactly at non-zero
static offsets. -/
theorem codegen_foreign_tail_aborts_iff_nonzero_offset (off : Nat) (pack : Option Nat)
    (m : Meta) : codegenProjectTail off pack .foreign m = .panicNounwind ↔ off ≠ 0 := by
  constructor
  · intro h hz
    rw [hz, codegen_foreign_tail_zero_offset] at h
    cases h
  · exact codegen_foreign_tail_nonzero_offset_aborts off pack m

/-- **Soundness of the compiled projection on `extern type` tails.**  Whenever
it returns an offset, that offset is the true one for every admissible
alignment of the foreign type. -/
theorem codegen_foreign_tail_value_is_true_offset (off : Nat) (pack : Option Nat) (m : Meta)
    (n : Nat) (h : codegenProjectTail off pack .foreign m = .value n) :
    ∀ a, tailOffset off pack a = n := by
  intro a
  cases Nat.decEq off 0 with
  | isTrue hz =>
    rw [hz, codegen_foreign_tail_zero_offset] at h
    cases h
    rw [hz]
    exact alignUp_zero _
  | isFalse hnz =>
    rw [codegen_foreign_tail_nonzero_offset_aborts off pack m hnz] at h
    cases h

/-- **Unpacked structs: the abort is exactly the uncomputable case.** -/
theorem unpacked_foreign_tail_aborts_iff_not_static (off : Nat) (m : Meta) :
    codegenProjectTail off none .foreign m = .panicNounwind ↔ ¬ OffsetStatic off none := by
  rw [codegen_foreign_tail_aborts_iff_nonzero_offset, unpacked_tail_offset_static_iff_zero]

theorem min_pow2_one {a : Nat} (ha : IsPow2 a) : min a 1 = 1 :=
  Nat.min_eq_right ha.pos

/-- **`packed(1)` structs: the abort is not forced.**  At every non-zero static
offset the tail offset is static and equal to the static offset, yet the
compiled projection aborts and the interpreted one reports an unsupported
operation. -/
theorem packed1_foreign_tail_static_but_refused (off : Nat) (m : Meta) (h : off ≠ 0) :
    OffsetStatic off (some 1) ∧
    (∀ a, IsPow2 a → tailOffset off (some 1) a = off) ∧
    codegenProjectTail off (some 1) .foreign m = .panicNounwind ∧
    interpProjectTail off (some 1) .foreign m = .unsupported := by
  refine ⟨packed1_tail_offset_static off, ?_, ?_, ?_⟩
  · intro a ha
    show alignUp off (min a 1) = off
    rw [min_pow2_one ha]
    exact alignUp_one off
  · exact codegen_foreign_tail_nonzero_offset_aborts off (some 1) m h
  · exact interp_foreign_tail_nonzero_offset_unsupported off (some 1) m h

/-- Whether `packed(N)` makes the static offset exact. -/
def packDivides (pack : Option Nat) (off : Nat) : Bool :=
  match pack with
  | none => false
  | some p => decide (off % p = 0)

/-- A projection with the missing static fast path added: static offset `0`, or
`packed(N)` with `N` dividing the static offset. -/
def specializedProjectForeignTail (off : Nat) (pack : Option Nat) : Outcome Nat :=
  if off = 0 then .value 0
  else if packDivides pack off = true then .value off
  else .panicNounwind

theorem packDivides_iff (pack : Option Nat) (off : Nat) :
    packDivides pack off = true ↔ ∃ p, pack = some p ∧ off % p = 0 := by
  cases pack with
  | none =>
    constructor
    · intro h; cases h
    · intro h
      cases h with
      | intro p hp => cases hp.1
  | some p =>
    constructor
    · intro h
      exact ⟨p, rfl, of_decide_eq_true h⟩
    · intro h
      cases h with
      | intro q hq =>
        cases hq with
        | intro hpk hmod =>
          cases hpk
          exact decide_eq_true hmod

/-- **The specialised projection is sound and complete**: it returns the true
offset whenever the offset is static, and refuses exactly when it is not. -/
theorem specialized_projection_sound_and_complete (off : Nat) (pack : Option Nat)
    (hpack : ∀ p, pack = some p → IsPow2 p) :
    (∀ n, specializedProjectForeignTail off pack = .value n →
        ∀ a, IsPow2 a → tailOffset off pack a = n) ∧
    (specializedProjectForeignTail off pack = .panicNounwind ↔ ¬ OffsetStatic off pack) := by
  have hiff := extern_tail_offset_static_iff off pack hpack
  cases Nat.decEq off 0 with
  | isTrue hzero =>
    have hval : specializedProjectForeignTail off pack = .value 0 := by
      unfold specializedProjectForeignTail
      rw [ite_of_pos _ _ hzero]
    constructor
    · intro n hn a _
      rw [hval] at hn
      cases hn
      rw [hzero]
      exact alignUp_zero _
    · constructor
      · intro h
        rw [hval] at h
        cases h
      · intro h
        exact absurd (hiff.mpr (Or.inl hzero)) h
  | isFalse hnz =>
    cases hd : packDivides pack off with
    | true =>
      have hval : specializedProjectForeignTail off pack = .value off := by
        unfold specializedProjectForeignTail
        rw [ite_of_neg _ _ hnz, ite_of_pos _ _ hd]
      have hstat : OffsetStatic off pack := hiff.mpr (Or.inr ((packDivides_iff pack off).mp hd))
      constructor
      · intro n hn a ha
        rw [hval] at hn
        cases hn
        cases (packDivides_iff pack off).mp hd with
        | intro p hp =>
          cases hp with
          | intro hpk hmod =>
            have hp2 : IsPow2 p := hpack p hpk
            rw [hpk]
            show alignUp off (min a p) = off
            exact alignUp_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd
              (Nat.dvd_trans (min_pow2_dvd ha hp2) (Nat.dvd_of_mod_eq_zero hmod)))
      · constructor
        · intro h
          rw [hval] at h
          cases h
        · intro h
          exact absurd hstat h
    | false =>
      have hval : specializedProjectForeignTail off pack = .panicNounwind := by
        unfold specializedProjectForeignTail
        rw [ite_of_neg _ _ hnz, hd]
        rfl
      constructor
      · intro n hn
        rw [hval] at hn
        cases hn
      · constructor
        · intro _ hstat
          cases hiff.mp hstat with
          | inl h0 => exact hnz h0
          | inr hex =>
            have ht := (packDivides_iff pack off).mpr hex
            rw [hd] at ht
            cases ht
        · intro _
          exact hval

/-- **Counterexample 2.**  A header whose `extern type` tail sits at static
offset `6` (a `u32` then a `u16`, unpacked): foreign alignments `2`, `4` and
`16` put the tail at offsets `6`, `8` and `16`, so no single offset is correct
and the projection cannot be computed without the unknown alignment. -/
theorem ce2_nonzero_prefix_extern_tail_requires_unknown_align :
    tailOffset 6 none 2 = 6 ∧ tailOffset 6 none 4 = 8 ∧ tailOffset 6 none 16 = 16 ∧
    ¬ OffsetStatic 6 none ∧
    ¬ ∃ n, ∀ a, IsPow2 a → tailOffset 6 none a = n := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro h
    have h6 : (6 : Nat) = 0 := (unpacked_tail_offset_static_iff_zero 6).mp h
    cases h6
  · intro h
    cases h with
    | intro n hn =>
      have h2 : tailOffset 6 none 2 = n := hn 2 ⟨1, rfl⟩
      have h4 : tailOffset 6 none 4 = n := hn 4 ⟨2, rfl⟩
      have e2 : tailOffset 6 none 2 = 6 := by decide
      have e4 : tailOffset 6 none 4 = 8 := by decide
      rw [e2] at h2
      rw [e4, ← h2] at h4
      cases h4

/-! ## 5. Retagging a reference whose pointee has an `extern type` tail -/

/-- Kind of pointer being retagged. -/
inductive RefKind where
  | shared
  | mutable
  | box

/-- Which bytes a permission is being chosen for. -/
inductive Part where
  | insideFrozen
  | insideUnsafeCell
  | outside

/-- Tree Borrows permissions that a retag can create. -/
inductive Perm where
  | frozen
  | cell
  | unique
  | reservedFrz
  | reservedIm

/-- Facts about the pointee type and the retag that the permission choice reads. -/
structure RetagCtx where
  /-- The whole pointee type is `Freeze`. -/
  tyIsFreeze : Bool
  /-- The pointee type is `Unpin` (and `UnsafeUnpin`). -/
  tyIsUnpin : Bool
  /-- The retag is a function-entry retag. -/
  isProtected : Bool
  /-- The implicit-writes option is on and not locally disabled. -/
  implicitWritesFlag : Bool

/-- Implicit writes are only considered for protected references. -/
def RetagCtx.implicitWrites (c : RetagCtx) : Bool :=
  c.isProtected && c.implicitWritesFlag

def Part.isOutside : Part → Bool
  | .outside => true
  | _ => false

/-- A byte counts as frozen if it is known to be outside every `UnsafeCell`;
bytes outside the retagged range are frozen only if the whole type is. -/
def Part.frozen (c : RetagCtx) : Part → Bool
  | .insideFrozen => true
  | .insideUnsafeCell => false
  | .outside => c.tyIsFreeze

/-- The permission chosen for one part of the pointee. -/
def permOfPart (kind : RefKind) (c : RetagCtx) (part : Part) : Perm :=
  match kind with
  | .shared => if part.frozen c then .frozen else .cell
  | .mutable =>
    if c.implicitWrites && !part.isOutside then .unique
    else if c.isProtected || part.frozen c then .reservedFrz
    else .reservedIm
  | .box =>
    if c.implicitWrites && !part.isOutside then .unique
    else if c.isProtected || part.frozen c then .reservedFrz
    else .reservedIm

/-- The three permissions a retag installs. -/
structure NewPermission where
  freezePerm : Perm
  nonfreezePerm : Perm
  outsidePerm : Perm

/-- Permission choice for a retag; `none` means the retag is a no-op (mutable
references and boxes to types that are not `Unpin`). -/
def newPermission (kind : RefKind) (c : RetagCtx) : Option NewPermission :=
  match kind, c.tyIsUnpin with
  | .mutable, false => none
  | .box, false => none
  | _, _ =>
    some { freezePerm := permOfPart kind c .insideFrozen
           nonfreezePerm := permOfPart kind c .insideUnsafeCell
           outsidePerm := permOfPart kind c .outside }

/-- The access to the parent that creating a permission implies. -/
inductive Access where
  | read
  | write

def Perm.associatedAccess : Perm → Option Access
  | .cell => none
  | .unique => some .write
  | .frozen => some .read
  | .reservedFrz => some .read
  | .reservedIm => some .read

/-- Per-byte state after a retag. -/
structure LocState where
  perm : Perm
  /-- The retag itself performed an access to this byte. -/
  accessed : Bool

/-- State of a byte inside the eagerly retagged range. -/
def locStateInside (p : Perm) : LocState :=
  { perm := p, accessed := p.associatedAccess.isSome }

/-- State of a byte outside the range: installed lazily, never accessed by the
retag. -/
def locStateOutside (p : Perm) : LocState :=
  { perm := p, accessed := false }

/-- Size of the eagerly retagged range: the dynamic size when it exists, else the
size of the statically known prefix. -/
def tbReborrowSize (dynSize : Option Nat) (knownPrefix : Nat) : Nat :=
  match dynSize with
  | some n => n
  | none => knownPrefix

/-- State of byte `i` of the pointee after a Tree Borrows retag whose eager
range is `[0, size)`.  Bytes of the known prefix use the per-byte map
`frozenAt`; bytes of the foreign tail are not known to be outside an
`UnsafeCell` and get the non-frozen permission. -/
def tbRetagState (np : NewPermission) (frozenAt : Nat → Bool) (knownPrefix size i : Nat) :
    LocState :=
  if i < size then
    if i < knownPrefix then
      locStateInside (if frozenAt i = true then np.freezePerm else np.nonfreezePerm)
    else locStateInside np.nonfreezePerm
  else locStateOutside np.outsidePerm

/-- For a pointee that is neither `Freeze` nor `Unpin` (every type with an
`extern type` tail), retagging a mutable reference or a box is a no-op. -/
theorem tree_borrows_extern_mut_and_box_retag_is_nop (c : RetagCtx) (h : c.tyIsUnpin = false) :
    newPermission .mutable c = none ∧ newPermission .box c = none := by
  unfold newPermission
  rw [h]
  exact ⟨rfl, rfl⟩

/-- For such a pointee the only permission triple a retag can install is the
shared one, with the `cell` permission both for non-frozen bytes and outside
the range. -/
theorem tree_borrows_extern_new_permission (kind : RefKind) (c : RetagCtx) (np : NewPermission)
    (hFreeze : c.tyIsFreeze = false) (hUnpin : c.tyIsUnpin = false)
    (hnp : newPermission kind c = some np) :
    np.nonfreezePerm = .cell ∧ np.outsidePerm = .cell := by
  cases kind with
  | shared =>
    unfold newPermission at hnp
    rw [hUnpin] at hnp
    cases hnp
    show permOfPart .shared c .insideUnsafeCell = .cell ∧ permOfPart .shared c .outside = .cell
    unfold permOfPart Part.frozen
    rw [hFreeze]
    exact ⟨rfl, rfl⟩
  | mutable =>
    rw [(tree_borrows_extern_mut_and_box_retag_is_nop c hUnpin).1] at hnp
    cases hnp
  | box =>
    rw [(tree_borrows_extern_mut_and_box_retag_is_nop c hUnpin).2] at hnp
    cases hnp

theorem tbRetagState_prefix (np : NewPermission) (frozenAt : Nat → Bool)
    (knownPrefix size i : Nat) (h1 : i < size) (h2 : i < knownPrefix) :
    tbRetagState np frozenAt knownPrefix size i
      = locStateInside (if frozenAt i = true then np.freezePerm else np.nonfreezePerm) := by
  unfold tbRetagState
  rw [ite_of_pos _ _ h1, ite_of_pos _ _ h2]

theorem tbRetagState_tail (np : NewPermission) (frozenAt : Nat → Bool)
    (knownPrefix size i : Nat) (h1 : i < size) (h2 : ¬ i < knownPrefix) :
    tbRetagState np frozenAt knownPrefix size i = locStateInside np.nonfreezePerm := by
  unfold tbRetagState
  rw [ite_of_pos _ _ h1, ite_of_neg _ _ h2]

theorem tbRetagState_outside (np : NewPermission) (frozenAt : Nat → Bool)
    (knownPrefix size i : Nat) (h1 : ¬ i < size) :
    tbRetagState np frozenAt knownPrefix size i = locStateOutside np.outsidePerm := by
  unfold tbRetagState
  rw [ite_of_neg _ _ h1]

/-- **Retag range independence.**  Let the pointee have an `extern type` tail
(so it is neither `Freeze` nor `Unpin`), statically known prefix size
`knownPrefix`, and unknown true size `trueSize ≥ knownPrefix`.  The Tree
Borrows retag that only knows the prefix leaves every byte `i` in exactly the
state (permission and accessed flag) that a retag over the true extent would. -/
theorem tree_borrows_reborrow_sound_without_pointee_size
    (kind : RefKind) (c : RetagCtx) (np : NewPermission)
    (hFreeze : c.tyIsFreeze = false) (hUnpin : c.tyIsUnpin = false)
    (hnp : newPermission kind c = some np)
    (frozenAt : Nat → Bool) (knownPrefix trueSize : Nat) (hsize : knownPrefix ≤ trueSize)
    (i : Nat) :
    tbRetagState np frozenAt knownPrefix (tbReborrowSize none knownPrefix) i
      = tbRetagState np frozenAt knownPrefix trueSize i := by
  have hperm := tree_borrows_extern_new_permission kind c np hFreeze hUnpin hnp
  show tbRetagState np frozenAt knownPrefix knownPrefix i
      = tbRetagState np frozenAt knownPrefix trueSize i
  cases Nat.lt_or_ge i knownPrefix with
  | inl hlt =>
    rw [tbRetagState_prefix np frozenAt knownPrefix knownPrefix i hlt hlt,
        tbRetagState_prefix np frozenAt knownPrefix trueSize i (Nat.lt_of_lt_of_le hlt hsize) hlt]
  | inr hge =>
    have hnlt : ¬ i < knownPrefix := Nat.not_lt.mpr hge
    rw [tbRetagState_outside np frozenAt knownPrefix knownPrefix i hnlt]
    cases Nat.lt_or_ge i trueSize with
    | inl hlt' =>
      rw [tbRetagState_tail np frozenAt knownPrefix trueSize i hlt' hnlt, hperm.1, hperm.2]
      rfl
    | inr hge' =>
      rw [tbRetagState_outside np frozenAt knownPrefix trueSize i (Nat.not_lt.mpr hge')]

/-- Without the `Unpin` early exit, the *permission* of every byte still agrees
as long as the pointee is not `Freeze` and implicit writes are off; only the
accessed flag of bytes beyond the prefix can differ. -/
theorem tree_borrows_lazy_permission_matches_true_extent
    (kind : RefKind) (c : RetagCtx)
    (hFreeze : c.tyIsFreeze = false) (hImplicit : c.implicitWrites = false) :
    permOfPart kind c .outside = permOfPart kind c .insideUnsafeCell := by
  cases kind with
  | shared =>
    unfold permOfPart Part.frozen
    rw [hFreeze]
  | mutable =>
    unfold permOfPart Part.frozen Part.isOutside
    rw [hFreeze, hImplicit]
    rfl
  | box =>
    unfold permOfPart Part.frozen Part.isOutside
    rw [hFreeze, hImplicit]
    rfl

/-- The implicit-writes hypothesis is needed: for a protected mutable reference
with implicit writes on, bytes inside the range get `unique` and bytes outside
get `reservedFrz`. -/
theorem implicit_writes_separate_inside_from_outside :
    permOfPart .mutable
        { tyIsFreeze := false, tyIsUnpin := true, isProtected := true, implicitWritesFlag := true }
        .insideUnsafeCell = .unique ∧
    permOfPart .mutable
        { tyIsFreeze := false, tyIsUnpin := true, isProtected := true, implicitWritesFlag := true }
        .outside = .reservedFrz :=
  ⟨rfl, rfl⟩

/-! ### Stacked Borrows -/

/-- Outcome of a Stacked Borrows retag. -/
inductive SbRetag where
  /-- The dynamic size is unknown: no new tag is created and a diagnostic is
  emitted once. -/
  | skippedWithWarning
  /-- A fresh tag is pushed on the stacks of exactly the bytes `[0, size)`. -/
  | retagged (size : Nat)

/-- A Stacked Borrows retag needs the dynamic size of the pointee. -/
def sbRetag (dynSize : Option Nat) : SbRetag :=
  match dynSize with
  | none => .skippedWithWarning
  | some n => .retagged n

/-- Whether the fresh tag is on the borrow stack of byte `i` afterwards. -/
def SbRetag.grants : SbRetag → Nat → Bool
  | .skippedWithWarning, _ => false
  | .retagged n, i => decide (i < n)

/-- **Counterexample 3.**  An eager Stacked Borrows retag is a function of the
pointee's byte span: (a) two different spans grant the fresh tag on different
byte sets, so (b) no span-oblivious result agrees with all of them, and (c) the
fallback used when the span is unknown differs from the retag for every
non-empty span. -/
theorem ce3_stacked_borrows_eager_retag_requires_byte_span :
    (∀ n n', n < n' →
        (sbRetag (some n)).grants n = false ∧ (sbRetag (some n')).grants n = true) ∧
    (¬ ∃ g : Nat → Bool, ∀ n i, (sbRetag (some n)).grants i = g i) ∧
    (∀ n, 0 < n → (sbRetag none).grants 0 = false ∧ (sbRetag (some n)).grants 0 = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n n' hlt
    exact ⟨decide_eq_false (Nat.lt_irrefl n), decide_eq_true hlt⟩
  · intro h
    cases h with
    | intro g hg =>
      have h0 : (sbRetag (some 0)).grants 0 = g 0 := hg 0 0
      have h1 : (sbRetag (some 1)).grants 0 = g 0 := hg 1 0
      have e0 : (sbRetag (some 0)).grants 0 = false := rfl
      have e1 : (sbRetag (some 1)).grants 0 = true := rfl
      rw [e0] at h0
      rw [e1, ← h0] at h1
      cases h1
  · intro n hn
    exact ⟨rfl, decide_eq_true hn⟩

/-- Stacked Borrows cannot retag a pointee with an `extern type` tail: its
dynamic size does not exist, so the retag is skipped. -/
theorem stacked_borrows_skips_non_metaSized_pointee (ty : Ty) (m : Meta)
    (hTier : ¬ Implements ty .metaSized) :
    sbRetag ((ty.sizeAlign m).map Prod.fst) = .skippedWithWarning := by
  rw [not_metaSized_implies_no_runtime_layout ty m hTier]
  rfl

/-- Tree Borrows retags the same pointee over its statically known prefix. -/
theorem tree_borrows_retags_known_prefix_of_non_metaSized_pointee (ty : Ty) (m : Meta)
    (knownPrefix : Nat) (hTier : ¬ Implements ty .metaSized) :
    tbReborrowSize ((ty.sizeAlign m).map Prod.fst) knownPrefix = knownPrefix := by
  rw [not_metaSized_implies_no_runtime_layout ty m hTier]
  rfl

/-! ### The precise interior-mutability walk -/

/-- Outcome of a Tree Borrows retag of a reference to a struct with an
`extern type` tail at static offset `off`.  With precise interior-mutability
tracking the retag walks the fields of the non-`Freeze` pointee, which
projects to the tail; without it the type is treated as one `UnsafeCell`. -/
noncomputable def tbRetagHeaderOutcome (precise : Bool) (off : Nat) (pack : Option Nat)
    (m : Meta) : Outcome Unit :=
  match precise with
  | false => .value ()
  | true =>
    match interpProjectTail off pack .foreign m with
    | .value _ => .value ()
    | .panicNounwind => .panicNounwind
    | .unsupported => .unsupported

/-- With precise tracking, creating the reference is unsupported exactly when
the `extern type` tail sits at a non-zero static offset. -/
theorem precise_tree_borrows_header_retag_unsupported_iff_nonzero_offset
    (off : Nat) (pack : Option Nat) (m : Meta) :
    tbRetagHeaderOutcome true off pack m = .unsupported ↔ off ≠ 0 := by
  constructor
  · intro h hz
    rw [hz] at h
    have e : tbRetagHeaderOutcome true 0 pack m = .value () := rfl
    rw [e] at h
    cases h
  · intro h
    show (match interpProjectTail off pack .foreign m with
      | .value _ => Outcome.value ()
      | .panicNounwind => Outcome.panicNounwind
      | .unsupported => Outcome.unsupported) = Outcome.unsupported
    rw [interp_foreign_tail_nonzero_offset_unsupported off pack m h]

/-- Without precise tracking, the reference is always created. -/
theorem imprecise_tree_borrows_header_retag_supported (off : Nat) (pack : Option Nat)
    (m : Meta) : tbRetagHeaderOutcome false off pack m = .value () :=
  rfl

end SizedHierarchyAndExternTailSoundness
