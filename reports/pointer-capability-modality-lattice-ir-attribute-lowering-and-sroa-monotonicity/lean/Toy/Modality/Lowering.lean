/-
Toy.Modality.Lowering
=====================

IR parameter attributes, their toy meanings at argument and at return
position (each violation is undefined behaviour), the lowering `lower` from
modalities to attribute sets, its soundness, and the characterization of
`lower s pos m` as the largest sound attribute set.

Program points.  Every modality `m : Mod` describes promises about one pointer
value that exists at call entry: promises at call entry (`aligned`, `nonnull`,
`derefEntry`) and promises about the call's execution (`derefWhole`, `frozen`,
`unique`, `bounded`).  `lower s .arg m` is the set of argument attributes
(`dereferenceable` evaluated at call entry; `noalias`, `nofree` and `readonly`
over the call) that every trace of `⟦m⟧` satisfies.  `lower s .ret m` is the
set of return-value attributes, evaluated at the return point, that every trace
of `⟦m⟧` satisfies: the return-position attributes to which a pointer carrying
the call-entry modality `m` is entitled when it is returned (for example an
argument returned unchanged).  It is not a lowering of the validity invariant
that a returned value has at the return point; the toy has no modality for
that, and allocations created during the call are not represented.

The pair `alphaSet s pos` / `gammaDual s pos` is the polarity Galois
connection induced by the relation `attrSat s pos` (every relation induces one,
`polarity_galois`); `lower s pos` itself has no left adjoint on modalities, and
`lower s .arg` has no right adjoint
(`lower_no_left_adjoint_and_arg_no_right_adjoint`); `lower s .ret` has a right
adjoint when the alignment exceeds `1` and none when it is `1`
(`lower_ret_right_adjoint_of_alignLog_ne_zero`,
`lower_ret_no_right_adjoint_of_alignLog_eq_zero`).
-/
import Toy.Modality.Types
import Toy.Modality.Imported

namespace Toy.Modality

/-! ## Attributes -/

/-- IR parameter attributes (LLVM LangRef names). -/
inductive Attr
  | align
  | nonnull
  | dereferenceable
  | dereferenceableOrNull
  | noalias
  | nofree
  | readonly
  deriving DecidableEq, Repr

/-- An attribute set, one membership bit per attribute. -/
structure AttrSet where
  align : Bool
  nonnull : Bool
  dereferenceable : Bool
  dereferenceableOrNull : Bool
  noalias : Bool
  nofree : Bool
  readonly : Bool
  deriving DecidableEq, Repr

/-- Membership of an attribute. -/
def AttrSet.has (A : AttrSet) : Attr → Bool
  | .align => A.align
  | .nonnull => A.nonnull
  | .dereferenceable => A.dereferenceable
  | .dereferenceableOrNull => A.dereferenceableOrNull
  | .noalias => A.noalias
  | .nofree => A.nofree
  | .readonly => A.readonly

/-- Inclusion of attribute sets. -/
instance : LE AttrSet := ⟨fun A B => ∀ a, A.has a = true → B.has a = true⟩

/-- `A` with attribute `a` added. -/
def AttrSet.insert (A : AttrSet) : Attr → AttrSet
  | .align => { A with align := true }
  | .nonnull => { A with nonnull := true }
  | .dereferenceable => { A with dereferenceable := true }
  | .dereferenceableOrNull => { A with dereferenceableOrNull := true }
  | .noalias => { A with noalias := true }
  | .nofree => { A with nofree := true }
  | .readonly => { A with readonly := true }

theorem AttrSet.has_insert_self (A : AttrSet) (a : Attr) : (A.insert a).has a = true := by
  cases a <;> rfl

theorem AttrSet.ext_has {A B : AttrSet} (h : ∀ a, A.has a = B.has a) : A = B := by
  cases A; cases B
  have h1 := h .align; have h2 := h .nonnull; have h3 := h .dereferenceable
  have h4 := h .dereferenceableOrNull; have h5 := h .noalias; have h6 := h .nofree
  have h7 := h .readonly
  simp only [AttrSet.has] at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7; rfl

/-- Position of the pointer: function argument or return value. -/
inductive Pos
  | arg
  | ret
  deriving DecidableEq, Repr

/-- Toy meaning of `dereferenceable` for a return value, evaluated at the
return point on a trace of a pointer that exists at call entry: the pointee
bytes are inside an allocation live at call entry, and no allocation
containing the address is freed during the call.  It is definitionally the
atom `derefWhole` (`dereferenceableAtReturn_iff_atomSat_derefWhole`).
Allocations created during the call are not represented, so a freshly
allocated return value is not expressible; nor is the validity invariant of a
returned value at the return point, for which the toy has no modality. -/
def DereferenceableAtReturn (s : Shape) (t : Trace) : Prop :=
  Dereferenceable s t ∧ NotFreedDuring t

/-- Toy LangRef-style meaning of each attribute; a trace violating it is
undefined behaviour.  (`align` and `nonnull` produce poison in LLVM; the toy
treats them as they behave together with `noundef`.)

* `align`, `nonnull`: the same at both positions.
* `dereferenceable(size)`, `dereferenceable_or_null(size)`: at the point of the
  attribute, i.e. call entry for an argument (`Dereferenceable`) and the
  return point for a return value (`DereferenceableAtReturn`).
* argument `noalias`: no address that is accessed through an argument-derived
  pointer and written during the call is also accessed through an unrelated
  pointer during the call;
* argument `nofree`: no allocation containing the address is freed through an
  argument-derived pointer during the call;
* argument `readonly`: no write through an argument-derived pointer during the
  call;
* return `noalias` (toy reading of the allocation-like return semantics): no
  pointee byte is accessed through an unrelated pointer after the return;
* return `nofree` and return `readonly`: never satisfied (LangRef states that
  `nofree` is not valid for return values and phrases `readonly` for pointer
  arguments; an attribute set containing either is never sound at return
  position). -/
def attrSat (s : Shape) : Pos → Attr → Trace → Prop
  | _, .align, t => t.addr % s.align = 0
  | _, .nonnull, t => t.addr ≠ 0
  | .arg, .dereferenceable, t => Dereferenceable s t
  | .ret, .dereferenceable, t => DereferenceableAtReturn s t
  | .arg, .dereferenceableOrNull, t => t.addr = 0 ∨ Dereferenceable s t
  | .ret, .dereferenceableOrNull, t => t.addr = 0 ∨ DereferenceableAtReturn s t
  | .arg, .noalias, t =>
      ∀ x, AccessedBy t.during .arg x → Written t.during x → ¬ AccessedBy t.during .other x
  | .arg, .nofree, t => ∀ al ∈ t.live, al.contains t.addr → Event.free .arg al.id ∉ t.during
  | .arg, .readonly, t => ∀ x, Event.write .arg x ∉ t.during
  | .ret, .noalias, t => ∀ x, InRange s t.addr x → ¬ AccessedBy t.after .other x
  | .ret, .nofree, _ => False
  | .ret, .readonly, _ => False

/-- `γ`: the traces satisfying every attribute of `A` at position `pos`. -/
def gammaSet (s : Shape) (pos : Pos) (A : AttrSet) (t : Trace) : Prop :=
  ∀ a, A.has a = true → attrSat s pos a t

/-- Whether the position is an argument. -/
def Pos.isArg : Pos → Bool
  | .arg => true
  | .ret => false

/-- The lowering `α`: computed from the closure `c = cl s m` of a call-entry
modality `m`.  `align` from `aligned`; `nonnull` from `nonnull`;
`dereferenceable` and `dereferenceable_or_null` from `derefEntry` at argument
position (evaluated at call entry) and from `derefWhole` at return position
(evaluated at the return point, after the call has run); and at argument
position only, `noalias` from `bounded` together with `frozen` or `unique`,
`nofree` from `derefWhole`, `readonly` from `bounded` together with `frozen`.
At return position the result is the set of return-value attributes to which
a pointer carrying the call-entry modality `m` is entitled when it is
returned; it is not a lowering of a returned value's own validity invariant
at the return point, which the toy does not represent. -/
def lower (s : Shape) (pos : Pos) (m : Mod) : AttrSet :=
  let c := cl s m
  let d := if pos.isArg then c.derefEntry else c.derefWhole
  ⟨c.aligned, c.nonnull, d, d,
   pos.isArg && c.bounded && (c.frozen || c.unique), pos.isArg && c.derefWhole,
   pos.isArg && c.bounded && c.frozen⟩

/-- The toy's return-point dereferenceability is definitionally the atom
`derefWhole`: covered at call entry and not freed during the call. -/
theorem dereferenceableAtReturn_iff_atomSat_derefWhole (s : Shape) (t : Trace) :
    DereferenceableAtReturn s t ↔ atomSat s .derefWhole t :=
  Iff.rfl

/-- Which closure atom of the call-entry modality decides `dereferenceable` at
each position: `derefEntry` at argument position and `derefWhole` at return
position. -/
theorem lower_dereferenceable_eq (s : Shape) (m : Mod) :
    (lower s .arg m).dereferenceable = (cl s m).derefEntry ∧
    (lower s .ret m).dereferenceable = (cl s m).derefWhole :=
  ⟨rfl, rfl⟩

/-! ## Witness traces for attributes -/

/-- Live; the argument writes and an unrelated pointer reads the first pointee
byte during the call. -/
def tConflict (s : Shape) : Trace :=
  ⟨s.align, [wAlloc s s.align], [.write .arg s.align, .read .other s.align], []⟩

/-- Like `tStar`, with an unrelated read of the first pointee byte after the
return. -/
def tReadAfter (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [], [.read .other s.align]⟩

theorem den_tReadAfter (s : Shape) (m : Mod) : den s m (tReadAfter s) := by
  intro a _
  have := atomSat_tStar s a
  cases a <;> exact this

theorem not_ret_noalias_tReadAfter (s : Shape) : ¬ attrSat s .ret .noalias (tReadAfter s) :=
  fun hc => hc s.align (inRange_self s _) (Or.inl (by simp [tReadAfter]))

theorem atomSat_tConflict (s : Shape) (a : Atom) (ha : a ≠ .frozen ∧ a ≠ .unique) :
    atomSat s a (tConflict s) := by
  have hp := s.align_pos
  cases a
  · exact align_mod_align s
  · show s.align ≠ 0; omega
  · exact dereferenceable_wAlloc s hp _ rfl (by simp [tConflict])
  · refine ⟨dereferenceable_wAlloc s hp _ rfl (by simp [tConflict]), ?_⟩
    intro al _ _ tg h; simp [tConflict] at h
  · exact absurd rfl ha.1
  · exact absurd rfl ha.2
  · intro x hx
    simp [tConflict, AccessedBy] at hx
    subst hx
    exact inRange_self s _

theorem not_noalias_tConflict (s : Shape) : ¬ attrSat s .arg .noalias (tConflict s) := by
  intro h
  exact h s.align (Or.inr (by simp [tConflict])) ⟨.arg, by simp [tConflict]⟩
    (Or.inl (by simp [tConflict]))

theorem not_noalias_tOutOfRange (s : Shape) : ¬ attrSat s .arg .noalias (tOutOfRange s) := by
  intro h
  exact h (s.align + s.size) (Or.inr (by simp [tOutOfRange])) ⟨.arg, by simp [tOutOfRange]⟩
    (Or.inl (by simp [tOutOfRange]))

theorem not_readonly_tOutOfRange (s : Shape) : ¬ attrSat s .arg .readonly (tOutOfRange s) :=
  fun h => h (s.align + s.size) (by simp [tOutOfRange])

theorem not_nofree_tFreed (s : Shape) : ¬ attrSat s .arg .nofree (tFreed s) := by
  have hs := s.size_pos
  have hp := s.align_pos
  intro hc
  exact hc (wAlloc s s.align) (by simp [tFreed]) ⟨hp, by simp [wAlloc, tFreed],
    by simp [wAlloc, tFreed]; omega⟩ (by simp [tFreed, wAlloc])

theorem den_tDangling_of (s : Shape) (m : Mod) (h1 : m.derefEntry = false)
    (h2 : m.derefWhole = false) : den s m (tDangling s) := by
  refine fun a ha => atomSat_tDangling s a ?_
  cases a <;> simp_all [Mod.has]

theorem den_tFreed_of (s : Shape) (m : Mod) (h : m.derefWhole = false) : den s m (tFreed s) :=
  fun b hb => atomSat_tFreed s b (by rintro rfl; simp_all [Mod.has])

/-- For every attribute outside `lower s pos m` there is a trace in `⟦m⟧` that
violates it (helper for the best-abstraction result). -/
theorem exists_den_not_attrSat_of_not_has_lower (s : Shape) (pos : Pos) (m : Mod) (a : Attr)
    (h : (lower s pos m).has a = false) : ∃ t, den s m t ∧ ¬ attrSat s pos a t := by
  have hp := s.align_pos
  cases a
  · obtain ⟨t, ht, hn⟩ := exists_den_not_atomSat_of_not_has_cl s m .aligned h
    exact ⟨t, ht, by cases pos <;> exact hn⟩
  · obtain ⟨t, ht, hn⟩ := exists_den_not_atomSat_of_not_has_cl s m .nonnull h
    exact ⟨t, ht, by cases pos <;> exact hn⟩
  · cases pos
    · obtain ⟨t, ht, hn⟩ := exists_den_not_atomSat_of_not_has_cl s m .derefEntry h
      exact ⟨t, ht, hn⟩
    · obtain ⟨t, ht, hn⟩ := exists_den_not_atomSat_of_not_has_cl s m .derefWhole h
      exact ⟨t, ht, hn⟩
  · have hnd := not_dereferenceable_of_live_nil s (tDangling s) rfl
    cases pos
    · simp only [AttrSet.has, lower, cl, Pos.isArg, ↓reduceIte, Bool.or_eq_false_iff] at h
      refine ⟨tDangling s, den_tDangling_of s m h.1 h.2, ?_⟩
      intro hc; rcases hc with hc | hc
      · simp [tDangling] at hc; omega
      · exact hnd hc
    · simp only [AttrSet.has, lower, cl, Pos.isArg, Bool.false_eq_true, ↓reduceIte] at h
      cases hE : m.derefEntry
      · refine ⟨tDangling s, den_tDangling_of s m hE h, ?_⟩
        intro hc; rcases hc with hc | hc
        · simp [tDangling] at hc; omega
        · exact hnd hc.1
      · refine ⟨tFreed s, den_tFreed_of s m h, ?_⟩
        intro hc; rcases hc with hc | hc
        · simp [tFreed] at hc; omega
        · exact not_notFreedDuring_tFreed s hc.2
  · cases pos
    · simp only [AttrSet.has, lower, cl, Pos.isArg, Bool.true_and, Bool.and_eq_false_imp,
        Bool.or_eq_false_iff] at h
      cases hb : m.bounded
      · refine ⟨tOutOfRange s, fun b hb' => atomSat_tOutOfRange s b ?_,
          not_noalias_tOutOfRange s⟩
        rintro rfl; simp_all [Mod.has]
      · have h' := h hb
        refine ⟨tConflict s, fun b hb' => atomSat_tConflict s b ?_, not_noalias_tConflict s⟩
        constructor <;> rintro rfl <;> simp_all [Mod.has]
    · exact ⟨tReadAfter s, den_tReadAfter s m, not_ret_noalias_tReadAfter s⟩
  · cases pos
    · simp only [AttrSet.has, lower, cl, Pos.isArg, Bool.true_and] at h
      exact ⟨tFreed s, den_tFreed_of s m h, not_nofree_tFreed s⟩
    · exact ⟨tStar s, den_tStar s m, fun h => h⟩
  · cases pos
    · simp only [AttrSet.has, lower, cl, Pos.isArg, Bool.true_and, Bool.and_eq_false_imp] at h
      cases hb : m.bounded
      · refine ⟨tOutOfRange s, fun b hb' => atomSat_tOutOfRange s b ?_,
          not_readonly_tOutOfRange s⟩
        rintro rfl; simp_all [Mod.has]
      · have h' := h hb
        refine ⟨tArgWrite s, fun b hb' => atomSat_tArgWrite s b ?_, ?_⟩
        · rintro rfl; simp_all [Mod.has]
        · intro hc; exact hc s.align (by simp [tArgWrite])
    · exact ⟨tStar s, den_tStar s m, fun h => h⟩

/-! ## Results -/

/-- **Soundness of the lowering.**  For every shape `s`, position `pos`,
modality `m` and trace `t` with `t ∈ ⟦m⟧`, `t` satisfies every attribute of
`lower s pos m` at `pos` (`⟦m⟧ ⊆ γ(α m)`).  Here `m` is a call-entry modality
of a pointer that exists at call entry; at `pos = .ret` the attributes are
evaluated at the return point for that pointer when it is returned. -/
theorem lower_sound (s : Shape) (pos : Pos) (m : Mod) (t : Trace) (ht : den s m t) :
    gammaSet s pos (lower s pos m) t := by
  have hat : ∀ a, (cl s m).has a = true → atomSat s a t := (den_cl_iff s m t).2 ht
  intro a ha
  cases a
  · cases pos <;> exact hat .aligned ha
  · cases pos <;> exact hat .nonnull ha
  · cases pos
    · exact hat .derefEntry ha
    · exact hat .derefWhole ha
  · cases pos
    · exact Or.inr (hat .derefEntry ha)
    · exact Or.inr (hat .derefWhole ha)
  · cases pos
    · simp only [AttrSet.has, lower, Pos.isArg, Bool.true_and, Bool.and_eq_true,
        Bool.or_eq_true] at ha
      obtain ⟨hb, ha⟩ := ha
      intro x hxa hxw hxo
      have hr : InRange s t.addr x := hat .bounded hb x hxa
      rcases ha with ha | ha
      · exact hat .frozen ha x hr hxw
      · exact hat .unique ha x hr hxo
    · simp [AttrSet.has, lower, Pos.isArg] at ha
  · cases pos
    · simp only [AttrSet.has, lower, Pos.isArg, Bool.true_and] at ha
      intro al hal hc' hf
      exact (hat .derefWhole ha).2 al hal hc' .arg hf
    · simp [AttrSet.has, lower, Pos.isArg] at ha
  · cases pos
    · simp only [AttrSet.has, lower, Pos.isArg, Bool.true_and, Bool.and_eq_true] at ha
      intro x hx
      exact hat .frozen ha.2 x (hat .bounded ha.1 x (Or.inr hx)) ⟨.arg, hx⟩
    · simp [AttrSet.has, lower, Pos.isArg] at ha

/-- **The lowering is the largest sound attribute set.**  For every shape `s`,
position `pos`, modality `m` and attribute set `A`: every trace of `⟦m⟧`
satisfies `A` at `pos` iff `A ≤ lower s pos m`.  As in `lower_sound`, `m` is a
call-entry modality; at `pos = .ret` this characterizes the return-point
attributes that the call-entry modality `m` alone justifies. -/
theorem lower_best_iff (s : Shape) (pos : Pos) (m : Mod) (A : AttrSet) :
    (∀ t, den s m t → gammaSet s pos A t) ↔ A ≤ lower s pos m := by
  constructor
  · intro h a ha
    cases hl : (lower s pos m).has a
    · obtain ⟨t, ht, hn⟩ := exists_den_not_attrSat_of_not_has_lower s pos m a hl
      exact absurd (h t ht a ha) hn
    · rfl
  · intro h t ht a ha
    exact lower_sound s pos m t ht a (h a ha)

/-- **Uniqueness of the best lowering.**  If an attribute set `A` is sound for
`⟦m⟧` at `pos` and contains every sound attribute set, then
`A = lower s pos m`. -/
theorem lower_unique (s : Shape) (pos : Pos) (m : Mod) (A : AttrSet)
    (hs : ∀ t, den s m t → gammaSet s pos A t)
    (hb : ∀ B : AttrSet, (∀ t, den s m t → gammaSet s pos B t) → B ≤ A) :
    A = lower s pos m := by
  have h1 : A ≤ lower s pos m := (lower_best_iff s pos m A).1 hs
  have h2 : lower s pos m ≤ A := hb _ (lower_sound s pos m)
  apply AttrSet.ext_has
  intro a
  have := h1 a; have := h2 a
  cases hA : A.has a <;> cases hL : (lower s pos m).has a <;> simp_all

/-! ## Galois connection (imported definition) -/

/-- Attribute sets ordered by *reverse* inclusion (more attributes = lower =
more precise), the abstract domain of the Galois connection. -/
structure AttrDual where
  val : AttrSet

instance : LE AttrDual := ⟨fun A B => B.val ≤ A.val⟩

/-- The reverse-inclusion order on `AttrDual` is reflexive and transitive. -/
theorem attrDual_le_refl_trans :
    (∀ A : AttrDual, A ≤ A) ∧ (∀ A B C : AttrDual, A ≤ B → B ≤ C → A ≤ C) :=
  ⟨fun _ _ h => h, fun _ _ _ h₁ h₂ a h => h₁ a (h₂ a h)⟩

open Classical in
/-- Abstraction induced by a relation `P` between attributes and traces: the
set of all attributes that every trace of `X` satisfies. -/
noncomputable def alphaOf (P : Attr → Trace → Prop) (X : Imported.Pred Trace) : AttrDual :=
  ⟨⟨decide (∀ t, X t → P .align t),
    decide (∀ t, X t → P .nonnull t),
    decide (∀ t, X t → P .dereferenceable t),
    decide (∀ t, X t → P .dereferenceableOrNull t),
    decide (∀ t, X t → P .noalias t),
    decide (∀ t, X t → P .nofree t),
    decide (∀ t, X t → P .readonly t)⟩⟩

/-- Concretization induced by a relation `P`: the traces satisfying every
attribute of `A`. -/
def gammaOf (P : Attr → Trace → Prop) (A : AttrDual) : Imported.Pred Trace :=
  fun t => ∀ a, A.val.has a = true → P a t

/-- Abstraction of a set of traces at `pos`: `alphaOf (attrSat s pos)`. -/
noncomputable def alphaSet (s : Shape) (pos : Pos) (X : Imported.Pred Trace) : AttrDual :=
  alphaOf (attrSat s pos) X

/-- Concretization of an attribute set at `pos`: `gammaOf (attrSat s pos)`,
i.e. `gammaSet s pos`. -/
def gammaDual (s : Shape) (pos : Pos) (A : AttrDual) : Imported.Pred Trace :=
  gammaOf (attrSat s pos) A

/-- `⟦m⟧` viewed as an element of the imported concrete domain. -/
def denP (s : Shape) (m : Mod) : Imported.Pred Trace := fun t => den s m t

open Classical in
theorem alphaOf_has (P : Attr → Trace → Prop) (X : Imported.Pred Trace) (a : Attr) :
    (alphaOf P X).val.has a = decide (∀ t, X t → P a t) := by
  cases a <;> rfl

open Classical in
theorem alphaSet_has (s : Shape) (pos : Pos) (X : Imported.Pred Trace) (a : Attr) :
    (alphaSet s pos X).val.has a = decide (∀ t, X t → attrSat s pos a t) :=
  alphaOf_has _ X a

open Classical in
/-- **Polarity Galois connection.**  For every relation `P` between attributes
and traces, `alphaOf P` and `gammaOf P` form a Galois connection (imported
definition, reverse-inclusion order on attribute sets). -/
theorem polarity_galois (P : Attr → Trace → Prop) :
    Imported.GaloisConnection (alphaOf P) (gammaOf P) := by
  intro X A
  show A.val ≤ (alphaOf P X).val ↔ ∀ t, X t → ∀ a, A.val.has a = true → P a t
  constructor
  · intro h t ht a ha
    have := h a ha
    rw [alphaOf_has] at this
    exact (of_decide_eq_true this) t ht
  · intro h a ha
    rw [alphaOf_has]
    exact decide_eq_true (fun t ht => h t ht a ha)

open Classical in
/-- **The lowering is the polarity abstraction of the trace semantics.**  For
every shape `s` and position `pos`, `alphaSet s pos` and `gammaDual s pos` form
a Galois connection (an instance of `polarity_galois`), and for every modality
`m`, `lower s pos m = (alphaSet s pos (denP s m)).val`. -/
theorem alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den (s : Shape) (pos : Pos) :
    Imported.GaloisConnection (alphaSet s pos) (gammaDual s pos) ∧
    ∀ m, lower s pos m = (alphaSet s pos (denP s m)).val := by
  refine ⟨polarity_galois (attrSat s pos), ?_⟩
  intro m
  apply AttrSet.ext_has
  intro a
  rw [alphaSet_has]
  cases hl : (lower s pos m).has a
  · symm
    apply decide_eq_false
    intro hall
    obtain ⟨t, ht, hn⟩ := exists_den_not_attrSat_of_not_has_lower s pos m a hl
    exact hn (hall t ht)
  · symm
    apply decide_eq_true
    intro t ht
    exact lower_sound s pos m t ht a hl

/-- The attribute set `{noalias}`. -/
def attrsNoalias : AttrSet := ⟨false, false, false, false, true, false, false⟩

/-- `{frozen, bounded}`. -/
def modFrozenBounded : Mod := ⟨false, false, false, false, true, false, true⟩

/-- `{unique, bounded}`. -/
def modUniqueBounded : Mod := ⟨false, false, false, false, false, true, true⟩

/-- **The lowering has no left adjoint, and the argument lowering has no right
adjoint.**  For every shape `s` and position `pos`, there is no function `u`
assigning to each attribute set `A` a least modality whose lowering contains
`A` (`A ≤ lower s pos m ↔ u A ≤ m` for all `m`), neither over all modalities
nor over `s`-closed modalities; and at argument position there is no right
adjoint (`lower s .arg m ≤ A ↔ m ≤ u A` for all `m`, `A`).  For right adjoints
over `s`-closed modalities and at return position see
`lower_arg_no_right_adjoint_on_closed`,
`lower_ret_right_adjoint_of_alignLog_ne_zero` and
`lower_ret_no_right_adjoint_of_alignLog_eq_zero`. -/
theorem lower_no_left_adjoint_and_arg_no_right_adjoint (s : Shape) (pos : Pos) :
    (¬ ∃ u : AttrSet → Mod, ∀ (m : Mod) (A : AttrSet), A ≤ lower s pos m ↔ u A ≤ m) ∧
    (¬ ∃ u : AttrSet → {m : Mod // Closed s m}, ∀ (m : {m : Mod // Closed s m}) (A : AttrSet),
      A ≤ lower s pos m.1 ↔ (u A).1 ≤ m.1) ∧
    (¬ ∃ u : AttrSet → Mod, ∀ (m : Mod) (A : AttrSet), lower s .arg m ≤ A ↔ m ≤ u A) := by
  have hcl := cl_closure_operator_and_closed_sublattice s
  have hna : ∀ m : Mod, attrsNoalias ≤ lower s .arg m ↔ (lower s .arg m).noalias = true := by
    intro m; constructor
    · intro h; exact h .noalias rfl
    · intro h a ha; cases a <;> simp [attrsNoalias, AttrSet.has] at ha; exact h
  have hnr : ∀ m : Mod, ¬ attrsNoalias ≤ lower s .ret m := fun m h => by
    have := h .noalias rfl; simp [lower, AttrSet.has, Pos.isArg] at this
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    cases pos
    · have h1 : u attrsNoalias ≤ modFrozenBounded := (hu _ _).1 ((hna _).2 (by
        simp [lower, cl, modFrozenBounded, Pos.isArg]))
      have h2 : u attrsNoalias ≤ modUniqueBounded := (hu _ _).1 ((hna _).2 (by
        simp [lower, cl, modUniqueBounded, Pos.isArg]))
      have h3 := mod_bounded_lattice.2.2.2.2.1 _ _ _ h1 h2
      have h4 := (hna _).1 ((hu _ _).2 h3)
      simp [lower, cl, Mod.inf, modFrozenBounded, modUniqueBounded, Pos.isArg] at h4
    · exact hnr Mod.top ((hu _ _).2 (mod_bounded_lattice.2.2.2.2.2.2.2 _).2)
  · rintro ⟨u, hu⟩
    cases pos
    · let mf : {m : Mod // Closed s m} := ⟨cl s modFrozenBounded, hcl.2.2.2.1 _⟩
      let mu : {m : Mod // Closed s m} := ⟨cl s modUniqueBounded, hcl.2.2.2.1 _⟩
      let mb : {m : Mod // Closed s m} := ⟨Mod.inf mf.1 mu.1, hcl.2.2.2.2.1 _ _ mf.2 mu.2⟩
      have h1 : (u attrsNoalias).1 ≤ mf.1 := (hu mf _).1 ((hna _).2 (by
        simp [mf, lower, cl, modFrozenBounded, Pos.isArg]))
      have h2 : (u attrsNoalias).1 ≤ mu.1 := (hu mu _).1 ((hna _).2 (by
        simp [mu, lower, cl, modUniqueBounded, Pos.isArg]))
      have h3 : (u attrsNoalias).1 ≤ mb.1 := mod_bounded_lattice.2.2.2.2.1 _ _ _ h1 h2
      have h4 := (hna _).1 ((hu mb _).2 h3)
      simp [mb, mf, mu, lower, cl, Mod.inf, modFrozenBounded, modUniqueBounded, Pos.isArg] at h4
    · let mt : {m : Mod // Closed s m} := ⟨Mod.top, hcl.2.2.2.2.2.2.1⟩
      exact hnr Mod.top ((hu mt _).2 (mod_bounded_lattice.2.2.2.2.2.2.2 _).2)
  · rintro ⟨u, hu⟩
    let mF : Mod := ⟨false, false, false, false, true, false, false⟩
    let mB : Mod := ⟨false, false, false, false, false, false, true⟩
    have hF : mF ≤ u (lower s .arg Mod.bot) := (hu mF _).1 (by
      intro a ha; cases a <;> simp [mF, lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at ha ⊢ <;>
        exact ha)
    have hB : mB ≤ u (lower s .arg Mod.bot) := (hu mB _).1 (by
      intro a ha; cases a <;> simp [mB, lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at ha ⊢ <;>
        exact ha)
    have hFB := (hu _ _).2 (mod_bounded_lattice.2.2.2.2.2.2.1 _ _ _ hF hB) .noalias
      (by simp [mF, mB, Mod.sup, lower, cl, AttrSet.has, Pos.isArg])
    simp [lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at hFB

/-- `lower s .arg` has no right adjoint over `s`-closed modalities either: no
`u` with `lower s .arg m ≤ A ↔ m ≤ u A` for all `s`-closed `m` and all `A`. -/
theorem lower_arg_no_right_adjoint_on_closed (s : Shape) :
    ¬ ∃ u : AttrSet → {m : Mod // Closed s m},
      ∀ (m : {m : Mod // Closed s m}) (A : AttrSet), lower s .arg m.1 ≤ A ↔ m.1 ≤ (u A).1 := by
  rintro ⟨u, hu⟩
  have hcl := cl_closure_operator_and_closed_sublattice s
  let mF : {m : Mod // Closed s m} :=
    ⟨cl s ⟨false, false, false, false, true, false, false⟩, hcl.2.2.2.1 _⟩
  let mB : {m : Mod // Closed s m} :=
    ⟨cl s ⟨false, false, false, false, false, false, true⟩, hcl.2.2.2.1 _⟩
  let mFB : {m : Mod // Closed s m} := ⟨Mod.sup mF.1 mB.1, hcl.2.2.2.2.2.1 _ _ mF.2 mB.2⟩
  have hF : mF.1 ≤ (u (lower s .arg Mod.bot)).1 := (hu mF _).1 (by
    intro a ha; cases a <;> simp [mF, lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at ha ⊢ <;>
      exact ha)
  have hB : mB.1 ≤ (u (lower s .arg Mod.bot)).1 := (hu mB _).1 (by
    intro a ha; cases a <;> simp [mB, lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at ha ⊢ <;>
      exact ha)
  have hsup := (hu mFB _).2 (mod_bounded_lattice.2.2.2.2.2.2.1 _ _ _ hF hB) .noalias
    (by simp [mFB, mF, mB, Mod.sup, lower, cl, AttrSet.has, Pos.isArg])
  simp [lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at hsup

/-- The right adjoint of `lower s .ret` when the alignment exceeds `1`: the
largest modality whose return lowering is inside `A`. -/
def retRightAdjoint (A : AttrSet) : Mod :=
  ⟨A.align, A.nonnull, A.nonnull, A.nonnull && A.dereferenceable && A.dereferenceableOrNull,
   true, true, true⟩

/-- **Return lowering: right adjoint at alignment above `1`.**  For every
shape `s` with `s.alignLog ≠ 0`, `retRightAdjoint A` is `s`-closed for every
`A`, and `lower s .ret m ≤ A ↔ m ≤ retRightAdjoint A` for all `m` and `A`. -/
theorem lower_ret_right_adjoint_of_alignLog_ne_zero (s : Shape) (hs : s.alignLog ≠ 0) :
    (∀ A, Closed s (retRightAdjoint A)) ∧
    (∀ (m : Mod) (A : AttrSet), lower s .ret m ≤ A ↔ m ≤ retRightAdjoint A) := by
  have hbeq : (s.alignLog == 0) = false := beq_false_of_ne hs
  refine ⟨fun A => ?_, fun m A => ?_⟩
  · cases A with
    | mk a1 a2 a3 a4 a5 a6 a7 =>
      cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
        simp [Closed, cl, retRightAdjoint, hbeq]
  · constructor
    · intro h a ha
      cases a
      · exact h .align (by simp [lower, cl, AttrSet.has, Mod.has, hbeq] at ha ⊢; exact ha)
      · exact h .nonnull (by
          simp [lower, cl, AttrSet.has, Mod.has] at ha ⊢; exact Or.inl (Or.inl ha))
      · exact h .nonnull (by
          simp [lower, cl, AttrSet.has, Mod.has] at ha ⊢; exact Or.inl (Or.inr ha))
      · have hnn := h .nonnull (by
          simp [lower, cl, AttrSet.has, Mod.has] at ha ⊢; exact Or.inr ha)
        have hde := h .dereferenceable (by
          simp [lower, cl, AttrSet.has, Mod.has, Pos.isArg] at ha ⊢; exact ha)
        have hdn := h .dereferenceableOrNull (by
          simp [lower, cl, AttrSet.has, Mod.has, Pos.isArg] at ha ⊢; exact ha)
        simp [retRightAdjoint, Mod.has, AttrSet.has] at hnn hde hdn ⊢
        exact ⟨⟨hnn, hde⟩, hdn⟩
      · rfl
      · rfl
      · rfl
    · intro h a ha
      cases a
      · simp [lower, cl, AttrSet.has, hbeq] at ha
        exact h .aligned ha
      · simp [lower, cl, AttrSet.has] at ha
        rcases ha with (ha | ha) | ha
        · exact h .nonnull ha
        · exact h .derefEntry ha
        · have := h .derefWhole ha
          simp [retRightAdjoint, Mod.has] at this
          exact this.1.1
      · simp [lower, cl, AttrSet.has, Pos.isArg] at ha
        have := h .derefWhole ha
        simp [retRightAdjoint, Mod.has] at this
        exact this.1.2
      · simp [lower, cl, AttrSet.has, Pos.isArg] at ha
        have := h .derefWhole ha
        simp [retRightAdjoint, Mod.has] at this
        exact this.2
      · simp [lower, cl, AttrSet.has, Pos.isArg] at ha
      · simp [lower, cl, AttrSet.has, Pos.isArg] at ha
      · simp [lower, cl, AttrSet.has, Pos.isArg] at ha

/-- **Return lowering: no right adjoint at alignment `1`.**  For every shape
`s` with `s.alignLog = 0`, `lower s .ret` has no right adjoint, neither over
all modalities nor over `s`-closed modalities (`lower s .ret Mod.bot` contains
`align`, which every attribute set without `align` excludes). -/
theorem lower_ret_no_right_adjoint_of_alignLog_eq_zero (s : Shape) (hs : s.alignLog = 0) :
    (¬ ∃ u : AttrSet → Mod, ∀ (m : Mod) (A : AttrSet), lower s .ret m ≤ A ↔ m ≤ u A) ∧
    (¬ ∃ u : AttrSet → {m : Mod // Closed s m},
      ∀ (m : {m : Mod // Closed s m}) (A : AttrSet), lower s .ret m.1 ≤ A ↔ m.1 ≤ (u A).1) := by
  let botA : AttrSet := ⟨false, false, false, false, false, false, false⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    have h := (hu Mod.bot botA).2 (mod_bounded_lattice.2.2.2.2.2.2.2 (u botA)).1 .align
      (by simp [lower, cl, AttrSet.has, hs])
    simp [botA, AttrSet.has] at h
  · rintro ⟨u, hu⟩
    let mb : {m : Mod // Closed s m} :=
      ⟨cl s Mod.bot, (cl_closure_operator_and_closed_sublattice s).2.2.2.2.2.2.2⟩
    have hle : mb.1 ≤ (u botA).1 := by
      have h1 := (cl_closure_operator_and_closed_sublattice s).2.1 Mod.bot (u botA).1
        (mod_bounded_lattice.2.2.2.2.2.2.2 _).1
      rw [(u botA).2] at h1
      exact h1
    have h := (hu mb botA).2 hle .align (by simp [mb, lower, cl, AttrSet.has, hs])
    simp [botA, AttrSet.has] at h

/-! ## Counterexamples for stronger lowerings -/

/-- `refFull` without `bounded` (frozen but with unbounded provenance). -/
def refFullNoBounded : Mod := ⟨true, true, true, true, true, false, false⟩

/-- `mutFull` without `bounded` (unique but with unbounded provenance). -/
def mutFullNoBounded : Mod := ⟨true, true, true, true, false, true, false⟩

/-- **Stronger argument-position lowerings: counterexamples.**  For every
shape `s`, each listed attribute is outside `lower s .arg m` for the listed
`m`, and a trace of `⟦m⟧` violates `lower s .arg m` with that attribute added:
for a shared reference to a non-`Freeze` pointee (`tCell refFull`), `nofree`
(a free through the reference, `tFreed s`), `readonly` (a write through it,
`tArgWrite s`) and `noalias` (`tConflict s`); for a mutable reference to a
non-`Unpin` pointee (`tPin mutFull`), `noalias` (`tConflict s`) and `nofree`
(`tFreed s`); for a `Box` of an `Unpin` pointee (`tBox mutFull`), `nofree`
(`tFreed s`); `dereferenceable` inside a relaxing wrapper (`tRelax refFull`,
`tDangling s`); and `noalias` and `readonly` for `refFull` without `bounded`,
and `noalias` for `mutFull` without `bounded` (an access through the argument
just outside the pointee, `tOutOfRange s`). -/
theorem stronger_arg_lowerings_counterexamples (s : Shape) :
    ((lower s .arg (kindBase (.shared false))).nofree = false ∧
      den s (kindBase (.shared false)) (tFreed s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.shared false))).insert .nofree) (tFreed s)) ∧
    ((lower s .arg (kindBase (.shared false))).readonly = false ∧
      den s (kindBase (.shared false)) (tArgWrite s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.shared false))).insert .readonly)
        (tArgWrite s)) ∧
    ((lower s .arg (kindBase (.shared false))).noalias = false ∧
      den s (kindBase (.shared false)) (tConflict s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.shared false))).insert .noalias)
        (tConflict s)) ∧
    ((lower s .arg (kindBase (.mutRef false))).noalias = false ∧
      den s (kindBase (.mutRef false)) (tConflict s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.mutRef false))).insert .noalias)
        (tConflict s)) ∧
    ((lower s .arg (kindBase (.mutRef false))).nofree = false ∧
      den s (kindBase (.mutRef false)) (tFreed s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.mutRef false))).insert .nofree) (tFreed s)) ∧
    ((lower s .arg (kindBase (.box true))).nofree = false ∧
      den s (kindBase (.box true)) (tFreed s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.box true))).insert .nofree) (tFreed s)) ∧
    ((lower s .arg (tRelax refFull)).dereferenceable = false ∧
      den s (tRelax refFull) (tDangling s) ∧
      ¬ gammaSet s .arg ((lower s .arg (tRelax refFull)).insert .dereferenceable)
        (tDangling s)) ∧
    ((lower s .arg refFullNoBounded).noalias = false ∧
      (lower s .arg refFullNoBounded).readonly = false ∧
      den s refFullNoBounded (tOutOfRange s) ∧
      ¬ gammaSet s .arg ((lower s .arg refFullNoBounded).insert .noalias) (tOutOfRange s) ∧
      ¬ gammaSet s .arg ((lower s .arg refFullNoBounded).insert .readonly) (tOutOfRange s)) ∧
    ((lower s .arg mutFullNoBounded).noalias = false ∧
      den s mutFullNoBounded (tOutOfRange s) ∧
      ¬ gammaSet s .arg ((lower s .arg mutFullNoBounded).insert .noalias) (tOutOfRange s)) := by
  have hro : ¬ attrSat s .arg .readonly (tArgWrite s) := fun hc =>
    hc s.align (by simp [tArgWrite])
  have hder : ¬ attrSat s .arg .dereferenceable (tDangling s) :=
    not_dereferenceable_of_live_nil s _ rfl
  have hins : ∀ (A : AttrSet) (a : Attr) (t : Trace), ¬ attrSat s .arg a t →
      ¬ gammaSet s .arg (A.insert a) t := fun A a t hn hg => hn (hg a (A.has_insert_self a))
  have dWrite : ∀ m : Mod, m.frozen = false → den s m (tArgWrite s) := fun m hm =>
    fun b hb => atomSat_tArgWrite s b (by rintro rfl; simp_all [Mod.has])
  have dConf : ∀ m : Mod, m.frozen = false → m.unique = false → den s m (tConflict s) :=
    fun m h1 h2 b hb => atomSat_tConflict s b (by
      constructor <;> rintro rfl <;> simp_all [Mod.has])
  have dOut : ∀ m : Mod, m.bounded = false → den s m (tOutOfRange s) := fun m hm =>
    fun b hb => atomSat_tOutOfRange s b (by rintro rfl; simp_all [Mod.has])
  refine ⟨⟨rfl, den_tFreed_of s _ rfl, hins _ _ _ (not_nofree_tFreed s)⟩,
    ⟨rfl, dWrite _ rfl, hins _ _ _ hro⟩,
    ⟨rfl, dConf _ rfl rfl, hins _ _ _ (not_noalias_tConflict s)⟩,
    ⟨rfl, dConf _ rfl rfl, hins _ _ _ (not_noalias_tConflict s)⟩,
    ⟨rfl, den_tFreed_of s _ rfl, hins _ _ _ (not_nofree_tFreed s)⟩,
    ⟨rfl, den_tFreed_of s _ rfl, hins _ _ _ (not_nofree_tFreed s)⟩,
    ⟨rfl, den_tRelax_tDangling s _, hins _ _ _ hder⟩,
    ⟨rfl, rfl, dOut _ rfl, hins _ _ _ (not_noalias_tOutOfRange s),
      hins _ _ _ (not_readonly_tOutOfRange s)⟩,
    ⟨rfl, dOut _ rfl, hins _ _ _ (not_noalias_tOutOfRange s)⟩⟩

/-! ## Position dependence -/

/-- **The argument lowering of `refFull` is not sound at return position**
(counterexample).  For every shape `s`: the argument-position lowering of
`refFull` contains `noalias`, `nofree` and `readonly`; the trace
`tReadAfter s` (an unrelated read of the pointee after the return) is in
`⟦m⟧` for every modality `m`, satisfies argument `noalias`, and violates
return `noalias`; hence `tReadAfter s` violates `lower s .arg refFull` at
return position.  As everywhere in the toy, `m` and `refFull` are call-entry
modalities. -/
theorem refFull_arg_lowering_not_sound_at_return (s : Shape) :
    (lower s .arg refFull).noalias = true ∧ (lower s .arg refFull).nofree = true ∧
    (lower s .arg refFull).readonly = true ∧
    (∀ m, den s m (tReadAfter s)) ∧ attrSat s .arg .noalias (tReadAfter s) ∧
    ¬ attrSat s .ret .noalias (tReadAfter s) ∧
    ¬ gammaSet s .ret (lower s .arg refFull) (tReadAfter s) := by
  refine ⟨rfl, rfl, rfl, den_tReadAfter s, ?_, not_ret_noalias_tReadAfter s, ?_⟩
  · intro x hx; simp [tReadAfter, AccessedBy] at hx
  · intro hg; exact not_ret_noalias_tReadAfter s (hg .noalias rfl)

/-- **Call-entry dereferenceability of a shared reference to a non-`Freeze`
pointee does not entitle it to return-position `dereferenceable`**
(counterexample).  For every shape `s`: the argument-position lowering of the
call-entry modality `tCell refFull` contains `dereferenceable` (evaluated at
call entry); the trace `tFreed s`, in which the pointee allocation is freed
through the pointer during the call, is in `⟦tCell refFull⟧`, satisfies
`dereferenceable` at argument position and violates the toy's return-position
`dereferenceable` (`DereferenceableAtReturn`, evaluated at the return point);
so `lower s .arg (tCell refFull)` is not sound at return position.  This is a
statement about a pointer that carries the call-entry modality
`tCell refFull` and is returned after the call has run; it is not a statement
about the validity invariant of a value returned at type `&UnsafeCell<T>`,
which the toy does not represent. -/
theorem entry_deref_of_tCell_refFull_not_sound_at_return (s : Shape) :
    (lower s .arg (tCell refFull)).dereferenceable = true ∧
    den s (tCell refFull) (tFreed s) ∧ attrSat s .arg .dereferenceable (tFreed s) ∧
    ¬ attrSat s .ret .dereferenceable (tFreed s) ∧
    ¬ gammaSet s .ret (lower s .arg (tCell refFull)) (tFreed s) := by
  have hn : ¬ attrSat s .ret .dereferenceable (tFreed s) :=
    fun h => not_notFreedDuring_tFreed s h.2
  exact ⟨rfl, den_tFreed_of s _ rfl, atomSat_tFreed s .derefEntry (by decide), hn,
    fun hg => hn (hg .dereferenceable rfl)⟩

/-- **Relaxed pointers lower the same at both positions** (positive control
for position dependence).  For every shape `s` and modality `m`,
`lower s .arg (tRelax m) = lower s .ret (tRelax m)`; hence (`lower_sound`) the
argument lowering of a relaxed pointer is sound at return position. -/
theorem tRelax_arg_lowering_eq_ret_lowering (s : Shape) (m : Mod) :
    lower s .arg (tRelax m) = lower s .ret (tRelax m) := by
  simp [lower, cl, tRelax, clDeref, Mod.bot, Pos.isArg]

/-- **Return-point lowering of the call-entry base modalities: which kinds
keep `dereferenceable`.**  For every shape `s`: for the pointer kinds
`.shared false`, `.mutRef false`, `.box true` and `.box false`, the
argument-position lowering of the call-entry modality `kindBase k` contains
`dereferenceable` and `dereferenceable_or_null` and its return-position
lowering contains neither (the closure lacks `derefWhole`); for `.shared true`
and `.mutRef true` the return-position lowering contains both.  The
return-position lowering is computed from call-entry modalities (see
`lower`); this is not a statement about the validity invariant of a value of
the corresponding Rust type at the return point. -/
theorem kindBase_ret_lowering_dereferenceable_by_kind (s : Shape) :
    (∀ k ∈ [PtrKind.shared false, PtrKind.mutRef false, PtrKind.box true, PtrKind.box false],
      (lower s .arg (kindBase k)).dereferenceable = true ∧
      (lower s .arg (kindBase k)).dereferenceableOrNull = true ∧
      (lower s .ret (kindBase k)).dereferenceable = false ∧
      (lower s .ret (kindBase k)).dereferenceableOrNull = false) ∧
    (∀ k ∈ [PtrKind.shared true, PtrKind.mutRef true],
      (lower s .ret (kindBase k)).dereferenceable = true ∧
      (lower s .ret (kindBase k)).dereferenceableOrNull = true) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact ⟨rfl, rfl⟩

end Toy.Modality
