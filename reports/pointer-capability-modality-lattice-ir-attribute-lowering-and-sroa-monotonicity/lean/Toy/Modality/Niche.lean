/-
Toy.Modality.Niche
==================

Lifting a pointer's attributes through an `Option`-like enum whose `None` is
encoded as a pointer value `v`.  When the value is `None`, nothing is read,
written or freed through an argument-derived pointer during the call
(`NoArgEvents`).  Whether `v` is a niche of the payload, i.e. no trace of the
payload modality has address `v`, is the separate predicate `IsNiche`.

The lifted lowering `liftOpt` keeps the argument-position lowering of the
payload except `nonnull` and `dereferenceable`; `dereferenceable_or_null`
stays when the payload lowering has it.
-/
import Toy.Modality.Lowering

namespace Toy.Modality

/-- Nothing is read, written or freed through an argument-derived pointer
during the call. -/
def NoArgEvents (t : Trace) : Prop :=
  ∀ x, Event.read .arg x ∉ t.during ∧ Event.write .arg x ∉ t.during ∧
    Event.free .arg x ∉ t.during

/-- `v` is a niche of the payload modality `m` at shape `s`: no trace of `⟦m⟧`
has address `v`. -/
def IsNiche (s : Shape) (m : Mod) (v : Nat) : Prop :=
  ∀ t, den s m t → t.addr ≠ v

/-- Traces of an `Option`-like value over a pointer leaf with base modality `m`
whose `None` is encoded as the pointer value `v`: either the value is `v` and
nothing is done through argument-derived pointers, or the value is a pointer
satisfying `⟦m⟧`.  (`v` is not required to be a niche of `m`; see `IsNiche`.) -/
def denOpt (s : Shape) (v : Nat) (m : Mod) (t : Trace) : Prop :=
  (t.addr = v ∧ NoArgEvents t) ∨ den s m t

/-- Lifted lowering for the `Option`-like value: the argument-position lowering
of the payload without `nonnull` and `dereferenceable`. -/
def liftOpt (s : Shape) (m : Mod) : AttrSet :=
  { lower s .arg m with nonnull := false, dereferenceable := false }

/-- The value `v` with no allocation and no events. -/
def tAt (v : Nat) : Trace := ⟨v, [], [], []⟩

theorem noArgEvents_tAt (v : Nat) : NoArgEvents (tAt v) := by
  intro x; simp [tAt]

/-- Argument `nofree` holds on every trace whose address is `0` (no allocation
contains address `0`). -/
theorem arg_nofree_of_addr_zero (s : Shape) (t : Trace) (h0 : t.addr = 0) :
    attrSat s .arg .nofree t := by
  intro al _ ⟨hpos, hle, _⟩
  omega

/-- **Non-zero niches come from misalignment.**  For every shape `s`,
modality `m` and value `v ≠ 0` that is a niche of `m`: `m` contains `aligned`,
the alignment exceeds `1` (`s.alignLog ≠ 0`), and `v` is not a multiple of
`s.align`.  (Addresses are unbounded natural numbers, and every positive
address carries a one-allocation trace satisfying every atom other than
`aligned`, so no other atom yields a non-zero niche.) -/
theorem aligned_and_misaligned_of_nonzero_niche (s : Shape) (m : Mod) (v : Nat)
    (hv : IsNiche s m v) (hv0 : v ≠ 0) :
    m.aligned = true ∧ s.alignLog ≠ 0 ∧ ¬ (v % s.align = 0) := by
  have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
  let t : Trace := ⟨v, [wAlloc s v], [], []⟩
  have hnot : ¬ den s m t := fun hd => hv t hd rfl
  have h1 : m.aligned = true ∧ ¬ (v % s.align = 0) := by
    apply Classical.byContradiction
    intro hno
    apply hnot
    intro a ha
    cases a
    · exact Classical.byContradiction (fun hrem => hno ⟨ha, hrem⟩)
    · exact hv0
    · exact dereferenceable_wAlloc s hvpos t rfl (by simp [t])
    · refine ⟨dereferenceable_wAlloc s hvpos t rfl (by simp [t]), ?_⟩
      intro al _ _ tg hmem; simp [t] at hmem
    · intro x _ ⟨tg, hw⟩; simp [t] at hw
    · intro x _ hacc; simp [t, AccessedBy] at hacc
    · exact argInRange_of_no_arg_access s _ (fun x => by simp [t, AccessedBy])
  refine ⟨h1.1, ?_, h1.2⟩
  intro hz
  exact h1.2 (mod_align_of_alignLog_eq_zero hz v)

/-! ## Results -/

/-- **Lifting through a null niche is sound.**  For every shape `s`, payload
modality `m` and trace `t`: if `t` is a trace of the `Option`-like value whose
`None` is the null value (`denOpt s 0 m t`), then `t` satisfies every attribute
of `liftOpt s m`.  Each of these attributes (`align`,
`dereferenceable_or_null`, `noalias`, `nofree`, `readonly`) is present exactly
when `lower s .arg m` has it.  Null is aligned for every alignment
(`0 % align = 0`). -/
theorem liftOpt_sound_of_noneVal_zero (s : Shape) (m : Mod) (t : Trace)
    (ht : denOpt s 0 m t) : gammaSet s .arg (liftOpt s m) t := by
  rcases ht with ⟨h0, hn⟩ | ht
  · intro a ha
    cases a
    · show t.addr % s.align = 0; rw [h0]; exact zero_mod_align s
    · simp [liftOpt, AttrSet.has] at ha
    · simp [liftOpt, AttrSet.has] at ha
    · exact Or.inl h0
    · intro x hx; rcases hx with hx | hx
      · exact absurd hx (hn x).1
      · exact absurd hx (hn x).2.1
    · exact arg_nofree_of_addr_zero s t h0
    · intro x hx; exact (hn x).2.1 hx
  · intro a ha
    have hl := lower_sound s .arg m t ht
    cases a
    · exact hl .align ha
    · simp [liftOpt, AttrSet.has] at ha
    · simp [liftOpt, AttrSet.has] at ha
    · exact hl .dereferenceableOrNull ha
    · exact hl .noalias ha
    · exact hl .nofree ha
    · exact hl .readonly ha

/-- **`liftOpt` is the largest sound attribute set for the null niche.**  For
every shape `s`, payload modality `m` and attribute set `A`: every trace of
`denOpt s 0 m` satisfies `A` at argument position iff `A ≤ liftOpt s m`. -/
theorem liftOpt_best_iff (s : Shape) (m : Mod) (A : AttrSet) :
    (∀ t, denOpt s 0 m t → gammaSet s .arg A t) ↔ A ≤ liftOpt s m := by
  constructor
  · intro h a ha
    have hl := (lower_best_iff s .arg m A).1 (fun t ht => h t (Or.inr ht)) a ha
    have hnone := h (tAt 0) (Or.inl ⟨rfl, noArgEvents_tAt 0⟩) a ha
    cases a
    · exact hl
    · exact absurd rfl hnone
    · exact absurd hnone (not_dereferenceable_of_live_nil s _ rfl)
    · exact hl
    · exact hl
    · exact hl
    · exact hl
  · intro h t ht a ha
    exact liftOpt_sound_of_noneVal_zero s m t ht a (h a ha)

/-- **For a genuine niche, lifting is sound exactly for the null niche.**  For
every shape `s`, payload modality `m` and value `v` that is a niche of `m`
(`IsNiche s m v`): every trace of `denOpt s v m` satisfies `liftOpt s m` iff
`v = 0`. -/
theorem liftOpt_sound_iff_noneVal_eq_zero_of_isNiche (s : Shape) (m : Mod) (v : Nat)
    (hv : IsNiche s m v) :
    (∀ t, denOpt s v m t → gammaSet s .arg (liftOpt s m) t) ↔ v = 0 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hv0
    have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
    let t : Trace := ⟨v, [wAlloc s v], [], []⟩
    have hnot : ¬ den s m t := fun hd => hv t hd rfl
    have hmod : m.aligned = true ∧ ¬ (v % s.align = 0) := by
      apply Classical.byContradiction
      intro hno
      apply hnot
      intro a ha
      cases a
      · apply Classical.byContradiction
        intro hrem
        exact hno ⟨ha, hrem⟩
      · exact hv0
      · exact dereferenceable_wAlloc s hvpos t rfl (by simp [t])
      · refine ⟨dereferenceable_wAlloc s hvpos t rfl (by simp [t]), ?_⟩
        intro al _ _ tg hmem; simp [t] at hmem
      · intro x _ ⟨tg, hw⟩; simp [t] at hw
      · intro x _ hacc; simp [t, AccessedBy] at hacc
      · exact argInRange_of_no_arg_access s _ (fun x => by simp [t, AccessedBy])
    have halign : (liftOpt s m).align = true := by
      simp [liftOpt, lower, cl, hmod.1]
    have hsat := h (tAt v) (Or.inl ⟨rfl, noArgEvents_tAt v⟩) .align halign
    exact hmod.2 hsat
  · rintro rfl
    exact liftOpt_sound_of_noneVal_zero s m

/-- **Lifting through a non-zero niche is unsound** (counterexample).  For the
two-byte, two-aligned shape `s2` and the payload modality `refFull`, the value
`1` is a niche of `refFull`, and with `None` encoded at `1` (a counterfactual
encoding), `liftOpt s2 refFull` contains `dereferenceable_or_null` and
`align`, and the `None` trace `tAt 1` violates both. -/
theorem liftOpt_unsound_at_niche_one :
    IsNiche s2 refFull 1 ∧
    (liftOpt s2 refFull).dereferenceableOrNull = true ∧ (liftOpt s2 refFull).align = true ∧
    denOpt s2 1 refFull (tAt 1) ∧
    ¬ attrSat s2 .arg .dereferenceableOrNull (tAt 1) ∧ ¬ attrSat s2 .arg .align (tAt 1) := by
  refine ⟨?_, rfl, rfl, Or.inl ⟨rfl, noArgEvents_tAt 1⟩, ?_, ?_⟩
  · intro t ht haddr
    have ha : t.addr % s2.align = 0 := ht .aligned rfl
    rw [haddr] at ha
    exact absurd ha (by decide)
  · rintro (h | h)
    · simp [tAt] at h
    · exact not_dereferenceable_of_live_nil s2 _ rfl h
  · show ¬ (1 % s2.align = 0); decide

/-- **`nonnull` and `dereferenceable` must not be lifted** (counterexample).
For every shape `s` and payload modality `m`, the null `None` trace `tNull` is a
trace of `denOpt s 0 m` and violates `nonnull` and `dereferenceable`. -/
theorem lift_nonnull_dereferenceable_unsound_at_null (s : Shape) (m : Mod) :
    denOpt s 0 m tNull ∧ ¬ attrSat s .arg .nonnull tNull ∧
    ¬ attrSat s .arg .dereferenceable tNull := by
  refine ⟨Or.inl ⟨rfl, ?_⟩, fun h => h rfl, not_dereferenceable_of_live_nil s _ rfl⟩
  intro x; simp [tNull]

/-- **Without the niche condition the exactness result fails**
(counterexample).  For the one-byte, alignment-1 shape `s1`, payload modality
`Mod.bot` and value `1`: `1` is not a niche of `Mod.bot`, every trace of
`denOpt s1 1 Mod.bot` satisfies `liftOpt s1 Mod.bot` (which is `{align}`,
trivially true at alignment 1), and `1 ≠ 0`. -/
theorem liftOpt_sound_at_non_niche_one :
    ¬ IsNiche s1 Mod.bot 1 ∧
    (∀ t, denOpt s1 1 Mod.bot t → gammaSet s1 .arg (liftOpt s1 Mod.bot) t) ∧ (1 : Nat) ≠ 0 := by
  refine ⟨fun h => h (tAt 1) (den_bot s1 _) rfl, fun t _ a ha => ?_, by decide⟩
  cases a <;> simp [liftOpt, lower, cl, Mod.bot, AttrSet.has, s1, Pos.isArg] at ha
  exact mod_align_of_alignLog_eq_zero rfl _

end Toy.Modality
