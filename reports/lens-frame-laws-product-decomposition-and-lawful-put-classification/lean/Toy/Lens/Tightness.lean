/-
Toy.Lens.Tightness
==================

Everything in this file is **fully proved**.

**F4 — tightness witnesses.**  For every hypothesis labelled `tight` in the
cards of F1, F1-inverse, F1-laws, F2, F2-laws, F3, F3-sharp, F3-fiber and
F3-pair, a concrete instance in canonical form: every *other* hypothesis
holds, the dropped hypothesis fails, and the conclusion fails.

Witnesses for F1 (`isProductDecomposition_of_putGet_putIndep_jointExt_imp_nonempty`):

  hypothesis dropped                   | witness                         | theorem
  -------------------------------------+---------------------------------+---------------------------------
  `PutGet l₁`                          | read-only first field           | `ignorePut_tight_putGet_left`
  `PutGet l₂`                          | read-only second field          | `ignorePutSnd_tight_putGet_right`
  `PutIndep l₁ l₂`                     | state-twisting setter           | `twist_tight_putIndep_left`
                                       | XOR-entangled view              | `xorView_tight_putIndep_left`
  `PutIndep l₂ l₁`                     | state-twisting setter (swapped) | `twist_tight_putIndep_right`
                                       | XOR-entangled view (swapped)    | `xorView_tight_putIndep_right`
  `JointExt l₁ l₂`                     | ghost component                 | `ghost_tight_jointExt`
  `Nonempty (A × B) → Nonempty S`      | empty state type                | `empty_tight_nonempty`

The remaining witnesses are grouped by the result they target.
-/
import Toy.Lens.Complement

namespace Toy

namespace Lens

universe u

/-! ## Monomorphic abbreviations on `Bool × Bool` -/

/-- `fst` on `Bool × Bool`. -/
abbrev fstB : Lens (Bool × Bool) Bool := fst

/-- `snd` on `Bool × Bool`. -/
abbrev sndB : Lens (Bool × Bool) Bool := snd

/-- A read-only *second* field: the setter ignores the written value. -/
def ignorePutSnd : Lens (Bool × Bool) Bool where
  get p := p.2
  put p _ := p

/-- The identity lens on `Bool`: the whole state is the view. -/
def idB : Lens Bool Bool where
  get s := s
  put _ a := a

/-- The only lens on the empty state type (with view `Unit`). -/
def emptyLens : Lens Empty Unit where
  get _ := ()
  put s _ := s

/-! ## Dropping `PutGet l₁` -/

/-- **F4, `PutGet l₁`.**  A read-only first field next to an honest second
field: all other hypotheses of F1 hold, the conclusion fails. -/
theorem ignorePut_tight_putGet_left :
    ¬ ignorePut.PutGet ∧
    sndB.PutGet ∧
    PutIndep ignorePut sndB ∧
    PutIndep sndB ignorePut ∧
    JointExt ignorePut sndB ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsProductDecomposition ignorePut sndB := by
  refine ⟨ignorePut_not_putGet, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_,
    fun h => h, ?_⟩
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro h
    exact absurd (h.intertwines_fst.put_eq (false, false) true) (by decide)

/-- The same witness also satisfies every *derived* law except `PutGet`:
`GetPut`, `PutPut` for both lenses and commuting puts.  So `PutGet` is not
recoverable from any combination of the other laws considered here. -/
theorem ignorePut_satisfies_all_other_laws :
    ignorePut.GetPut ∧ ignorePut.PutPut ∧ sndB.VeryWellBehaved ∧ PutComm ignorePut sndB :=
  ⟨ignorePut_getPut, ignorePut_putPut, snd_veryWellBehaved, fun _ _ _ => rfl⟩

/-! ## Dropping `PutGet l₂` -/

/-- **F4, `PutGet l₂`.**  The mirror image of `ignorePut_tight_putGet_left`. -/
theorem ignorePutSnd_tight_putGet_right :
    fstB.PutGet ∧
    ¬ ignorePutSnd.PutGet ∧
    PutIndep fstB ignorePutSnd ∧
    PutIndep ignorePutSnd fstB ∧
    JointExt fstB ignorePutSnd ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsProductDecomposition fstB ignorePutSnd := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl, ?_, fun h => h, ?_⟩
  · intro h
    exact absurd (h (false, false) true) (by decide)
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro h
    exact absurd (h.intertwines_snd.put_eq (false, false) true) (by decide)

/-! ## Dropping `PutIndep l₁ l₂` -/

/-- **F4, `PutIndep l₁ l₂` (state-twisting setter).**  `twist` and `snd` are
both very well-behaved, `snd` does not disturb `twist`, the pair is jointly
extensional — but `twist.put` changes the second field, so the conclusion of
F1 fails. -/
theorem twist_tight_putIndep_left :
    twist.PutGet ∧
    sndB.PutGet ∧
    ¬ PutIndep twist sndB ∧
    PutIndep sndB twist ∧
    JointExt twist sndB ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsProductDecomposition twist sndB := by
  refine ⟨twist_veryWellBehaved.2.1, fun _ _ => rfl, twist_snd_not_putIndep, fun _ _ => rfl, ?_,
    fun h => h, ?_⟩
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro h
    exact absurd (h.intertwines_fst.put_eq (false, false) true) (by decide)

/-- The state-twisting witness is as lawful as a single lens can be: both
lenses are very well-behaved.  (Their puts do not commute.) -/
theorem twist_snd_veryWellBehaved_not_putComm :
    twist.VeryWellBehaved ∧ sndB.VeryWellBehaved ∧ ¬ PutComm twist sndB :=
  ⟨twist_veryWellBehaved, snd_veryWellBehaved, twist_snd_not_putComm⟩

/-- **F4, `PutIndep l₁ l₂` (XOR-entangled views).**  `fst` and the XOR view
are both very well-behaved, writing the XOR view does not disturb `fst`, the
pair is jointly extensional — but writing `fst` changes the XOR view. -/
theorem xorView_tight_putIndep_left :
    fstB.PutGet ∧
    xorView.PutGet ∧
    ¬ PutIndep fstB xorView ∧
    PutIndep xorView fstB ∧
    JointExt fstB xorView ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsProductDecomposition fstB xorView := by
  refine ⟨fun _ _ => rfl, xorView_veryWellBehaved.2.1, fst_xorView_not_putIndep,
    xorView_fst_putIndep, ?_, fun h => h, ?_⟩
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro h
    exact absurd (h.intertwines_fst.put_eq (false, false) true) (by decide)

/-- In the XOR-entangled witness the pairing map *is* a bijection, with the
explicit inverse `pairPut`; what fails is only that `fst.put` is a coordinate
update.  This is the instance behind the remark that the bijection half of F1
needs just one direction of cross-independence. -/
theorem xorView_pairGet_bijective_but_not_decomposition :
    Function.LeftInverse (pairPut fstB xorView (false, false)) (pairGet fstB xorView) ∧
    Function.RightInverse (pairPut fstB xorView (false, false)) (pairGet fstB xorView) ∧
    ¬ IsProductDecomposition fstB xorView := by
  refine ⟨?_, ?_, xorView_tight_putIndep_left.2.2.2.2.2.2⟩
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl

/-- The XOR-entangled witness and the state-twisting witness are the *same*
instance up to a change of coordinates: the bijection
`(a, b) ↦ (a, a xor b)` carries `fst` to `twist` and the XOR view to `snd`. -/
theorem xorView_witness_is_twist_witness_up_to_iso :
    Intertwines (fun p : Bool × Bool => (p.1, xor p.1 p.2)) fstB twist ∧
    Intertwines (fun p : Bool × Bool => (p.1, xor p.1 p.2)) xorView sndB ∧
    Function.LeftInverse (fun p : Bool × Bool => (p.1, xor p.1 p.2))
      (fun p : Bool × Bool => (p.1, xor p.1 p.2)) := by
  refine ⟨⟨fun _ => rfl, ?_⟩, ⟨fun _ => rfl, ?_⟩, ?_⟩
  · intro ⟨a, b⟩ a'
    cases a <;> cases b <;> cases a' <;> rfl
  · intro ⟨a, b⟩ v
    cases a <;> cases b <;> cases v <;> rfl
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl

/-! ## Dropping `PutIndep l₂ l₁` -/

/-- **F4, `PutIndep l₂ l₁` (state-twisting setter, swapped).** -/
theorem twist_tight_putIndep_right :
    sndB.PutGet ∧
    twist.PutGet ∧
    PutIndep sndB twist ∧
    ¬ PutIndep twist sndB ∧
    JointExt sndB twist ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsProductDecomposition sndB twist := by
  refine ⟨fun _ _ => rfl, twist_veryWellBehaved.2.1, fun _ _ => rfl, twist_snd_not_putIndep, ?_,
    fun h => h, ?_⟩
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro h
    exact absurd (h.intertwines_snd.put_eq (false, false) true) (by decide)

/-- **F4, `PutIndep l₂ l₁` (XOR-entangled views, swapped).** -/
theorem xorView_tight_putIndep_right :
    xorView.PutGet ∧
    fstB.PutGet ∧
    PutIndep xorView fstB ∧
    ¬ PutIndep fstB xorView ∧
    JointExt xorView fstB ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsProductDecomposition xorView fstB := by
  refine ⟨xorView_veryWellBehaved.2.1, fun _ _ => rfl, xorView_fst_putIndep,
    fst_xorView_not_putIndep, ?_, fun h => h, ?_⟩
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro h
    exact absurd (h.intertwines_snd.put_eq (false, false) true) (by decide)

/-! ## Dropping `JointExt l₁ l₂` -/

/-- **F4, `JointExt` (ghost component).**  Two honest fields of a record that
also has a third, unprojected component: every other hypothesis of F1 holds,
but the pairing map is not injective. -/
theorem ghost_tight_jointExt :
    (ghostFst : Lens (Bool × Bool × Bool) Bool).PutGet ∧
    (ghostSnd : Lens (Bool × Bool × Bool) Bool).PutGet ∧
    PutIndep (ghostFst : Lens (Bool × Bool × Bool) Bool)
      (ghostSnd : Lens (Bool × Bool × Bool) Bool) ∧
    PutIndep (ghostSnd : Lens (Bool × Bool × Bool) Bool)
      (ghostFst : Lens (Bool × Bool × Bool) Bool) ∧
    ¬ JointExt (ghostFst : Lens (Bool × Bool × Bool) Bool)
      (ghostSnd : Lens (Bool × Bool × Bool) Bool) ∧
    (Nonempty (Bool × Bool) → Nonempty (Bool × Bool × Bool)) ∧
    ¬ IsProductDecomposition (ghostFst : Lens (Bool × Bool × Bool) Bool)
      (ghostSnd : Lens (Bool × Bool × Bool) Bool) := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    ghostFst_ghostSnd_not_jointExt, fun _ => ⟨(false, false, false)⟩, ?_⟩
  intro h
  have h' : ((false, false, false) : Bool × Bool × Bool) = (false, false, true) :=
    h.injective rfl
  exact absurd h' (by decide)

/-- The ghost witness is as lawful as two lenses can be short of joint
extensionality: both are very well-behaved and their puts commute. -/
theorem ghost_veryWellBehaved_putComm :
    (ghostFst : Lens (Bool × Bool × Bool) Bool).VeryWellBehaved ∧
    (ghostSnd : Lens (Bool × Bool × Bool) Bool).VeryWellBehaved ∧
    PutComm (ghostFst : Lens (Bool × Bool × Bool) Bool)
      (ghostSnd : Lens (Bool × Bool × Bool) Bool) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩,
   ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩,
   fun _ _ _ => rfl⟩

/-! ## Dropping the nonemptiness condition -/

/-- **F4, `Nonempty (A × B) → Nonempty S` (empty state type).**  On the empty
state type with one-point views every law holds vacuously, the views are
inhabited while the state type is not, and the pairing map
`Empty → Unit × Unit` is not surjective. -/
theorem empty_tight_nonempty :
    emptyLens.PutGet ∧
    emptyLens.PutGet ∧
    PutIndep emptyLens emptyLens ∧
    PutIndep emptyLens emptyLens ∧
    JointExt emptyLens emptyLens ∧
    ¬ (Nonempty (Unit × Unit) → Nonempty Empty) ∧
    ¬ IsProductDecomposition emptyLens emptyLens := by
  refine ⟨fun s => s.elim, fun s => s.elim, fun s => s.elim, fun s => s.elim, fun s => s.elim,
    fun h => match h ⟨((), ())⟩ with | ⟨s⟩ => s.elim, ?_⟩
  intro h
  obtain ⟨s, _⟩ := h.surjective ((), ())
  exact s.elim

/-- The lens on the empty state type with an *empty* view. -/
def emptyViewLens : Lens Empty Empty where
  get s := s
  put s _ := s

/-- **`Nonempty S` is not necessary when `A × B` is empty.**  On the empty
state type with an empty first view the conclusion of F1 holds although the
state type is empty; the conditional hypothesis
`Nonempty (A × B) → Nonempty S` of F1 holds there.  This is why F1 uses the
conditional form rather than `Nonempty S`. -/
theorem emptyView_isProductDecomposition_without_nonempty :
    IsProductDecomposition emptyViewLens emptyLens ∧ ¬ Nonempty Empty ∧
    (Nonempty (Empty × Unit) → Nonempty Empty) :=
  ⟨⟨fun s => s.elim, fun p => p.1.elim, ⟨fun s => s.elim, fun s => s.elim⟩,
      ⟨fun s => s.elim, fun s => s.elim⟩⟩,
    fun ⟨s⟩ => s.elim, fun ⟨p⟩ => p.1.elim⟩

/-- **Non-vacuity of F1 (ground instance).**  `fst` and `snd` on `Bool × Bool`
satisfy every hypothesis of F1. -/
theorem f1_nonvacuity_bool :
    fstB.PutGet ∧ sndB.PutGet ∧ PutIndep fstB sndB ∧ PutIndep sndB fstB ∧
    JointExt fstB sndB ∧ (Nonempty (Bool × Bool) → Nonempty (Bool × Bool)) :=
  fst_snd_satisfy_f1_hypotheses

/-! ## Aliasing: both directions of `PutIndep` fail at once -/

/-- **Aliasing.**  Two copies of the identity lens on `Bool` satisfy `PutGet`
and joint extensionality, on a nonempty state type, but violate
cross-independence (in both directions at once, the two lenses being equal),
and the conclusion of F1 fails.

This is *not* a single-hypothesis witness: it drops `PutIndep l₁ l₂` and
`PutIndep l₂ l₁` together. -/
theorem aliasing_fails_putIndep_both_directions :
    idB.PutGet ∧
    JointExt idB idB ∧
    (Nonempty (Bool × Bool) → Nonempty Bool) ∧
    ¬ PutIndep idB idB ∧
    ¬ IsProductDecomposition idB idB := by
  refine ⟨fun _ _ => rfl, fun _ _ h _ => h, fun _ => ⟨false⟩, ?_, ?_⟩
  · intro h
    exact absurd (h false true) (by decide)
  · intro h
    obtain ⟨s, hs⟩ := h.surjective (false, true)
    have h₁ : s = false := congrArg Prod.fst hs
    have h₂ : s = true := congrArg Prod.snd hs
    rw [h₁] at h₂
    exact absurd h₂ (by decide)

/-- **Aliasing is excluded by `PutGet`** on an inhabited state type as soon as
the view type has two distinct values: a lens satisfying `PutGet` cannot be
cross-independent of itself. -/
theorem not_putIndep_self_of_putGet {S : Type _} {A : Type _} (l : Lens S A)
    (h : l.PutGet) (s₀ : S) {a a' : A} (hne : a ≠ a') :
    ¬ PutIndep l l := by
  intro hind
  have e₁ : a = l.get s₀ := (h s₀ a).symm.trans (hind s₀ a)
  have e₂ : a' = l.get s₀ := (h s₀ a').symm.trans (hind s₀ a')
  exact hne (e₁.trans e₂.symm)

/-- **Non-vacuity of `not_putIndep_self_of_putGet` (ground instance).**  `fst`
on `Bool × Bool` satisfies `PutGet`, the state type is inhabited, and the view
type has two distinct values. -/
theorem aliasing_nonvacuity_bool :
    fstB.PutGet ∧ Nonempty (Bool × Bool) ∧ (false ≠ true) :=
  ⟨fst_putGet, ⟨(false, false)⟩, by decide⟩

/-- The lens on the empty state type with view `Bool`. -/
def emptyBoolLens : Lens Empty Bool where
  get s := s.elim
  put s _ := s

/-- The trivial lens with a one-point view on `Bool × Bool`: it sees nothing
and writes nothing. -/
def unitLensB : Lens (Bool × Bool) Unit where
  get _ := ()
  put s _ := s

/-- **The three escape hatches of `not_putIndep_self_of_putGet`.**  Each
instance keeps all but one hypothesis and the conclusion fails (the lens *is*
cross-independent of itself):

1. dropping `PutGet`: the read-only field `ignorePut`;
2. dropping inhabitedness of `S`: the lens on `Empty` with view `Bool`;
3. dropping two distinct views: the one-point view `unitLensB`.

The third instance is also the positive control: a lens with `PutGet` on an
inhabited state type that is cross-independent of itself. -/
theorem not_putIndep_self_tight :
    (¬ ignorePut.PutGet ∧ Nonempty (Bool × Bool) ∧ (false ≠ true) ∧ PutIndep ignorePut ignorePut) ∧
    (emptyBoolLens.PutGet ∧ ¬ Nonempty Empty ∧ (false ≠ true) ∧
      PutIndep emptyBoolLens emptyBoolLens) ∧
    (unitLensB.PutGet ∧ Nonempty (Bool × Bool) ∧ ¬ (∃ a a' : Unit, a ≠ a') ∧
      PutIndep unitLensB unitLensB) :=
  ⟨⟨ignorePut_not_putGet, ⟨(false, false)⟩, by decide, fun _ _ => rfl⟩,
   ⟨fun s => s.elim, fun ⟨s⟩ => s.elim, by decide, fun s => s.elim⟩,
   ⟨fun _ _ => rfl, ⟨(false, false)⟩, fun ⟨(), (), h⟩ => h rfl, fun _ _ => rfl⟩⟩

/-! ## Tightness of the derived-law lemmas

The derived-law lemmas of `Toy.Lens.Decomposition` obtain `GetPut`, `PutPut`
and `PutComm` from `PutGet`, cross-independence and joint extensionality.  For
each lemma, three instances show that each of its hypotheses is needed.  The
"drop `JointExt`" instances all hide the damage in a ghost component.
-/

/-- `ghostFst` on `Bool × Bool × Bool`. -/
abbrev ghostFstB : Lens (Bool × Bool × Bool) Bool := ghostFst

/-- `ghostSnd` on `Bool × Bool × Bool`. -/
abbrev ghostSndB : Lens (Bool × Bool × Bool) Bool := ghostSnd

/-- A setter that flips the first field, whatever value is written. -/
def flipPut : Lens (Bool × Bool) Bool where
  get p := p.1
  put p _ := (!p.1, p.2)

/-- A setter that ignores the written value and copies the sibling field into
the first field. -/
def copySibling : Lens (Bool × Bool) Bool where
  get p := p.1
  put p _ := (p.2, p.2)

/-- First field of a record with a ghost bit; every write clears the ghost. -/
def ghostReset : Lens (Bool × Bool × Bool) Bool where
  get s := s.1
  put s a := (a, s.2.1, false)

/-- First field of a record with a ghost bit used as a dirty flag. -/
def ghostDirty : Lens (Bool × Bool × Bool) Bool where
  get s := s.1
  put s a := if s.1 = a then s else (a, s.2.1, true)

/-- Second field of a record with a ghost bit; a write that changes the field
flips the ghost when the *first* field is `true`. -/
def ghostTwistSnd : Lens (Bool × Bool × Bool) Bool where
  get s := s.2.1
  put s b := (s.1, b, xor s.2.2 (s.1 && xor s.2.1 b))

/-- The trivial lens with a one-point view: it sees nothing and writes
nothing. -/
def unitLens {S : Type _} : Lens S Unit where
  get _ := ()
  put s _ := s

/-- **Derived law 1 (`GetPut`) is tight**: dropping `PutGet l₁`, or
`PutIndep l₁ l₂`, or `JointExt l₁ l₂` makes `GetPut l₁` fail. -/
theorem derived_getPut_tight :
    (¬ flipPut.PutGet ∧ PutIndep flipPut sndB ∧ JointExt flipPut sndB ∧ ¬ flipPut.GetPut) ∧
    (resetSibling.PutGet ∧ ¬ PutIndep resetSibling sndB ∧ JointExt resetSibling sndB ∧
      ¬ resetSibling.GetPut) ∧
    (ghostReset.PutGet ∧ PutIndep ghostReset ghostSndB ∧ ¬ JointExt ghostReset ghostSndB ∧
      ¬ ghostReset.GetPut) := by
  refine ⟨⟨?_, fun _ _ => rfl, ?_, ?_⟩, ⟨fun _ _ => rfl, ?_, ?_, resetSibling_not_getPut⟩,
    ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩⟩
  · exact fun h => absurd (h (false, false) false) (by decide)
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · exact fun h => absurd (h (false, false)) (by decide)
  · exact fun h => absurd (h (false, true) false) (by decide)
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · exact fun h => absurd (h (false, false, false) (false, false, true) rfl rfl) (by decide)
  · exact fun h => absurd (h (false, false, true)) (by decide)

/-- **Derived law 2 (`PutPut`) is tight**: dropping `PutGet l₁`, or
`PutIndep l₁ l₂`, or `JointExt l₁ l₂` makes `PutPut l₁` fail. -/
theorem derived_putPut_tight :
    (¬ flipPut.PutGet ∧ PutIndep flipPut sndB ∧ JointExt flipPut sndB ∧ ¬ flipPut.PutPut) ∧
    (dirtyFlag.PutGet ∧ ¬ PutIndep dirtyFlag sndB ∧ JointExt dirtyFlag sndB ∧
      ¬ dirtyFlag.PutPut) ∧
    (ghostDirty.PutGet ∧ PutIndep ghostDirty ghostSndB ∧ ¬ JointExt ghostDirty ghostSndB ∧
      ¬ ghostDirty.PutPut) := by
  refine ⟨⟨?_, fun _ _ => rfl, ?_, ?_⟩, ⟨dirtyFlag_putGet, ?_, ?_, dirtyFlag_not_putPut⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · exact fun h => absurd (h (false, false) false) (by decide)
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · exact fun h => absurd (h (false, false) false false) (by decide)
  · exact fun h => absurd (h (false, false) true) (by decide)
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · intro ⟨a, b, g⟩ a'
    cases a <;> cases b <;> cases g <;> cases a' <;> rfl
  · intro ⟨a, b, g⟩ a'
    cases a <;> cases b <;> cases g <;> cases a' <;> rfl
  · exact fun h => absurd (h (false, false, false) (false, false, true) rfl rfl) (by decide)
  · exact fun h => absurd (h (false, false, false) true false) (by decide)

/-- **Derived law 3 (`PutComm`) is tight**: dropping `PutGet l₁`, or
`PutIndep l₁ l₂`, or `JointExt l₁ l₂` makes `PutComm l₁ l₂` fail.  (The cases
`PutGet l₂` and `PutIndep l₂ l₁` are the mirror images.)

The third instance is the notable one: `ghostFst` and `ghostTwistSnd` are both
very well-behaved and cross-independent in both directions, yet their puts do
not commute.  So **without joint extensionality, commuting puts is an
independent law** — it is not implied by very-well-behavedness plus two-way
cross-independence. -/
theorem derived_putComm_tight :
    (¬ copySibling.PutGet ∧ sndB.PutGet ∧ PutIndep copySibling sndB ∧
      PutIndep sndB copySibling ∧ JointExt copySibling sndB ∧ ¬ PutComm copySibling sndB) ∧
    (twist.PutGet ∧ sndB.PutGet ∧ ¬ PutIndep twist sndB ∧ PutIndep sndB twist ∧
      JointExt twist sndB ∧ ¬ PutComm twist sndB) ∧
    (ghostFstB.VeryWellBehaved ∧ ghostTwistSnd.VeryWellBehaved ∧
      PutIndep ghostFstB ghostTwistSnd ∧ PutIndep ghostTwistSnd ghostFstB ∧
      ¬ JointExt ghostFstB ghostTwistSnd ∧ ¬ PutComm ghostFstB ghostTwistSnd) := by
  refine ⟨⟨?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩,
    ⟨twist_tight_putIndep_left.1, fun _ _ => rfl, twist_snd_not_putIndep, fun _ _ => rfl,
      twist_tight_putIndep_left.2.2.2.2.1, twist_snd_not_putComm⟩,
    ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩, ⟨?_, ?_, ?_⟩, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_⟩⟩
  · exact fun h => absurd (h (false, false) true) (by decide)
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)
  · exact fun h => absurd (h (false, false) false true) (by decide)
  · intro ⟨a, b, g⟩
    cases a <;> cases b <;> cases g <;> rfl
  · intro ⟨a, b, g⟩ b'
    rfl
  · intro ⟨a, b, g⟩ b' b''
    cases a <;> cases b <;> cases g <;> cases b' <;> cases b'' <;> rfl
  · exact fun h => absurd (h (false, false, false) (false, false, true) rfl rfl) (by decide)
  · exact fun h => absurd (h (false, false, false) true true) (by decide)

/-- **Derived law 3, mirror cases.**  Dropping `PutGet l₂`, or
`PutIndep l₂ l₁`, makes `PutComm l₁ l₂` fail while the other four laws of the
component lemma hold. -/
theorem derived_putComm_tight_mirror :
    (sndB.PutGet ∧ ¬ copySibling.PutGet ∧ PutIndep sndB copySibling ∧
      PutIndep copySibling sndB ∧ JointExt sndB copySibling ∧ ¬ PutComm sndB copySibling) ∧
    (sndB.PutGet ∧ twist.PutGet ∧ PutIndep sndB twist ∧ ¬ PutIndep twist sndB ∧
      JointExt sndB twist ∧ ¬ PutComm sndB twist) := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, ⟨t1, t2, t3, t4, t5, t6⟩, _⟩ := derived_putComm_tight
  exact ⟨⟨c2, c1, c4, c3, c5.symm, fun h => c6 h.symm⟩,
    ⟨t2, t1, t4, t3, t5.symm, fun h => t6 h.symm⟩⟩

/-- **The bundled derived-law lemma is tight in each of its five
hypotheses.**  Each instance keeps four of the five laws of
`veryWellBehaved_and_putComm_of_putGet_putIndep_jointExt` and its conclusion
fails. -/
theorem f1_laws_bundled_tight :
    (¬ flipPut.PutGet ∧ sndB.PutGet ∧ PutIndep flipPut sndB ∧ PutIndep sndB flipPut ∧
      JointExt flipPut sndB ∧
      ¬ (flipPut.VeryWellBehaved ∧ sndB.VeryWellBehaved ∧ PutComm flipPut sndB)) ∧
    (sndB.PutGet ∧ ¬ flipPut.PutGet ∧ PutIndep sndB flipPut ∧ PutIndep flipPut sndB ∧
      JointExt sndB flipPut ∧
      ¬ (sndB.VeryWellBehaved ∧ flipPut.VeryWellBehaved ∧ PutComm sndB flipPut)) ∧
    (resetSibling.PutGet ∧ sndB.PutGet ∧ ¬ PutIndep resetSibling sndB ∧
      PutIndep sndB resetSibling ∧ JointExt resetSibling sndB ∧
      ¬ (resetSibling.VeryWellBehaved ∧ sndB.VeryWellBehaved ∧ PutComm resetSibling sndB)) ∧
    (sndB.PutGet ∧ resetSibling.PutGet ∧ PutIndep sndB resetSibling ∧
      ¬ PutIndep resetSibling sndB ∧ JointExt sndB resetSibling ∧
      ¬ (sndB.VeryWellBehaved ∧ resetSibling.VeryWellBehaved ∧ PutComm sndB resetSibling)) ∧
    (ghostFstB.PutGet ∧ ghostTwistSnd.PutGet ∧ PutIndep ghostFstB ghostTwistSnd ∧
      PutIndep ghostTwistSnd ghostFstB ∧ ¬ JointExt ghostFstB ghostTwistSnd ∧
      ¬ (ghostFstB.VeryWellBehaved ∧ ghostTwistSnd.VeryWellBehaved ∧
          PutComm ghostFstB ghostTwistSnd)) :=
  ⟨⟨derived_getPut_tight.1.1, snd_putGet, derived_getPut_tight.1.2.1, fun _ _ => rfl,
    derived_getPut_tight.1.2.2.1, fun h => derived_getPut_tight.1.2.2.2 h.1.1⟩,
   ⟨snd_putGet, derived_getPut_tight.1.1, fun _ _ => rfl, derived_getPut_tight.1.2.1,
    derived_getPut_tight.1.2.2.1.symm, fun h => derived_getPut_tight.1.2.2.2 h.2.1.1⟩,
   ⟨resetSibling_putGet, snd_putGet, derived_getPut_tight.2.1.2.1, fun _ _ => rfl,
    derived_getPut_tight.2.1.2.2.1, fun h => resetSibling_not_getPut h.1.1⟩,
   ⟨snd_putGet, resetSibling_putGet, fun _ _ => rfl, derived_getPut_tight.2.1.2.1,
    derived_getPut_tight.2.1.2.2.1.symm, fun h => resetSibling_not_getPut h.2.1.1⟩,
   ⟨fun _ _ => rfl, derived_putComm_tight.2.2.2.1.2.1, derived_putComm_tight.2.2.2.2.1,
    derived_putComm_tight.2.2.2.2.2.1, derived_putComm_tight.2.2.2.2.2.2.1,
    fun h => derived_putComm_tight.2.2.2.2.2.2.2 h.2.2⟩⟩

/-- **The forced-witness lemma `eq_pairGet_of_get_eq` needs its first
compatibility hypothesis.**  On `Bool × Bool` with `fst`/`snd`, the map
`p ↦ (!p.1, p.2)` satisfies the second hypothesis, violates the first, and is
not the pairing map. -/
theorem eq_pairGet_tight_left :
    ¬ (∀ p : Bool × Bool, ((!p.1, p.2)).1 = fstB.get p) ∧
    (∀ p : Bool × Bool, ((!p.1, p.2)).2 = sndB.get p) ∧
    (fun p : Bool × Bool => (!p.1, p.2)) ≠ pairGet fstB sndB :=
  ⟨fun h => absurd (h (false, false)) (by decide),
   fun _ => rfl,
   fun h => absurd (congrArg Prod.fst (congrFun h (false, false))) (by decide)⟩

/-- **The forced-witness lemma needs its second compatibility hypothesis.** -/
theorem eq_pairGet_tight_right :
    (∀ p : Bool × Bool, ((p.1, !p.2)).1 = fstB.get p) ∧
    ¬ (∀ p : Bool × Bool, ((p.1, !p.2)).2 = sndB.get p) ∧
    (fun p : Bool × Bool => (p.1, !p.2)) ≠ pairGet fstB sndB :=
  ⟨fun _ => rfl,
   fun h => absurd (h (false, false)) (by decide),
   fun h => absurd (congrArg Prod.snd (congrFun h (false, false))) (by decide)⟩

/-- **F3-pair: each law on the left-hand side is needed.**  Each instance
keeps all other laws of the left-hand side of
`veryWellBehaved_and_putComm_iff_hasGhostComplement`, violates one, and has no
ghost complement.  Next to the trivial lens `unitLensB` (very well-behaved,
commuting with everything), `resetSibling` fails only `GetPut`, `ignorePut`
only `PutGet` and `dirtyFlag` only `PutPut`, in either position; two copies of
`fst` are very well-behaved but do not commute. -/
theorem ghostComplement_laws_tight :
    -- the laws of `l₁`
    (¬ resetSibling.GetPut ∧ resetSibling.PutGet ∧ resetSibling.PutPut ∧
      unitLensB.VeryWellBehaved ∧ PutComm resetSibling unitLensB ∧
      ¬ HasGhostComplement resetSibling unitLensB) ∧
    (ignorePut.GetPut ∧ ¬ ignorePut.PutGet ∧ ignorePut.PutPut ∧
      unitLensB.VeryWellBehaved ∧ PutComm ignorePut unitLensB ∧
      ¬ HasGhostComplement ignorePut unitLensB) ∧
    (dirtyFlag.GetPut ∧ dirtyFlag.PutGet ∧ ¬ dirtyFlag.PutPut ∧
      unitLensB.VeryWellBehaved ∧ PutComm dirtyFlag unitLensB ∧
      ¬ HasGhostComplement dirtyFlag unitLensB) ∧
    -- the laws of `l₂`
    (unitLensB.VeryWellBehaved ∧ ¬ resetSibling.GetPut ∧ resetSibling.PutGet ∧
      resetSibling.PutPut ∧ PutComm unitLensB resetSibling ∧
      ¬ HasGhostComplement unitLensB resetSibling) ∧
    (unitLensB.VeryWellBehaved ∧ ignorePut.GetPut ∧ ¬ ignorePut.PutGet ∧
      ignorePut.PutPut ∧ PutComm unitLensB ignorePut ∧
      ¬ HasGhostComplement unitLensB ignorePut) ∧
    (unitLensB.VeryWellBehaved ∧ dirtyFlag.GetPut ∧ dirtyFlag.PutGet ∧
      ¬ dirtyFlag.PutPut ∧ PutComm unitLensB dirtyFlag ∧
      ¬ HasGhostComplement unitLensB dirtyFlag) ∧
    -- commuting puts
    (fstB.VeryWellBehaved ∧ fstB.VeryWellBehaved ∧ ¬ PutComm fstB fstB ∧
      ¬ HasGhostComplement fstB fstB) := by
  have hu : unitLensB.VeryWellBehaved := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  exact
  ⟨⟨resetSibling_not_getPut, resetSibling_putGet, resetSibling_putPut, hu, fun _ _ _ => rfl,
     fun h => resetSibling_not_hasConstantComplement
       (hasConstantComplement_left_of_hasGhostComplement h)⟩,
   ⟨ignorePut_getPut, ignorePut_not_putGet, ignorePut_putPut, hu, fun _ _ _ => rfl,
     fun h => ignorePut_not_hasConstantComplement
       (hasConstantComplement_left_of_hasGhostComplement h)⟩,
   ⟨dirtyFlag_getPut, dirtyFlag_putGet, dirtyFlag_not_putPut, hu, fun _ _ _ => rfl,
     fun h => dirtyFlag_not_hasConstantComplement
       (hasConstantComplement_left_of_hasGhostComplement h)⟩,
   ⟨hu, resetSibling_not_getPut, resetSibling_putGet, resetSibling_putPut, fun _ _ _ => rfl,
     fun h => resetSibling_not_hasConstantComplement
       (hasConstantComplement_right_of_hasGhostComplement h)⟩,
   ⟨hu, ignorePut_getPut, ignorePut_not_putGet, ignorePut_putPut, fun _ _ _ => rfl,
     fun h => ignorePut_not_hasConstantComplement
       (hasConstantComplement_right_of_hasGhostComplement h)⟩,
   ⟨hu, dirtyFlag_getPut, dirtyFlag_putGet, dirtyFlag_not_putPut, fun _ _ _ => rfl,
     fun h => dirtyFlag_not_hasConstantComplement
       (hasConstantComplement_right_of_hasGhostComplement h)⟩,
   ⟨fst_veryWellBehaved, fst_veryWellBehaved, fst_fst_not_putComm,
     fstB_fstB_not_hasGhostComplement⟩⟩

/-- **An empty ghost is not a product decomposition.**  On the empty state type
with one-point views, the two (vacuous) lenses have a ghost complement with an
*empty* ghost, while the pairing map is not surjective.  So F1 corresponds to a
one-point ghost, not to an arbitrary "trivial" one. -/
theorem emptyGhost_hasGhostComplement_not_isProductDecomposition :
    HasGhostComplement emptyLens emptyLens ∧ ¬ IsProductDecomposition emptyLens emptyLens :=
  ⟨⟨Empty, ⟨fun s => s.elim, fun q => q.2.2.elim, fun s => s.elim, fun q => q.2.2.elim⟩,
     ⟨fun s => s.elim, fun s => s.elim⟩, ⟨fun s => s.elim, fun s => s.elim⟩⟩,
   empty_tight_nonempty.2.2.2.2.2.2⟩

/-- **With an empty view every type is a constant complement.**  For the lens
on the empty state type with the empty view, any `C` serves. -/
theorem emptyView_hasConstantComplement_any (C : Type) :
    ∃ e : Equiv Empty (Empty × C), Intertwines e.toFun emptyViewLens (fst : Lens (Empty × C) Empty) :=
  ⟨⟨fun s => s.elim, fun q => q.1.elim, fun s => s.elim, fun q => q.1.elim⟩,
   ⟨fun s => s.elim, fun s => s.elim⟩⟩

/-- **Non-vacuity of F3-pair (ground instance).**  `fst` and `snd` on
`Bool × Bool` satisfy the left-hand side (and the right-hand side). -/
theorem f3_pair_nonvacuity_bool :
    fstB.VeryWellBehaved ∧ sndB.VeryWellBehaved ∧ PutComm fstB sndB ∧
    HasGhostComplement fstB sndB :=
  ⟨fst_veryWellBehaved, snd_veryWellBehaved, fun _ _ _ => rfl, fst_snd_hasGhostComplement⟩

/-- **The explicit-inverse form of F1 is tight.**  Each instance keeps three of
the four hypotheses of `pairPut_leftInverse_rightInverse_of_putGet_putIndep_jointExt`
(for the base state `(false, false)` resp. `(false, false, false)`) and its
conclusion fails.  Dropping `PutGet l₁`, `PutGet l₂` or `PutIndep l₂ l₁` breaks
the right-inverse half; dropping `JointExt` breaks the left-inverse half.  In
the first three instances `pairGet` itself is still a bijection
(`pairGet_bijective_in_inverse_witnesses`): what fails is the formula
`pairPut`. -/
theorem pairPut_inverse_tight :
    (¬ ignorePut.PutGet ∧ sndB.PutGet ∧ PutIndep sndB ignorePut ∧ JointExt ignorePut sndB ∧
      ¬ (Function.LeftInverse (pairPut ignorePut sndB (false, false)) (pairGet ignorePut sndB) ∧
         Function.RightInverse (pairPut ignorePut sndB (false, false)) (pairGet ignorePut sndB))) ∧
    (fstB.PutGet ∧ ¬ ignorePutSnd.PutGet ∧ PutIndep ignorePutSnd fstB ∧
      JointExt fstB ignorePutSnd ∧
      ¬ (Function.LeftInverse (pairPut fstB ignorePutSnd (false, false))
            (pairGet fstB ignorePutSnd) ∧
         Function.RightInverse (pairPut fstB ignorePutSnd (false, false))
            (pairGet fstB ignorePutSnd))) ∧
    (sndB.PutGet ∧ twist.PutGet ∧ ¬ PutIndep twist sndB ∧ JointExt sndB twist ∧
      ¬ (Function.LeftInverse (pairPut sndB twist (false, false)) (pairGet sndB twist) ∧
         Function.RightInverse (pairPut sndB twist (false, false)) (pairGet sndB twist))) ∧
    (ghostFstB.PutGet ∧ ghostSndB.PutGet ∧ PutIndep ghostSndB ghostFstB ∧
      ¬ JointExt ghostFstB ghostSndB ∧
      ¬ (Function.LeftInverse (pairPut ghostFstB ghostSndB (false, false, false))
            (pairGet ghostFstB ghostSndB) ∧
         Function.RightInverse (pairPut ghostFstB ghostSndB (false, false, false))
            (pairGet ghostFstB ghostSndB))) :=
  ⟨⟨ignorePut_not_putGet, snd_putGet, fun _ _ => rfl, ignorePut_tight_putGet_left.2.2.2.2.1,
    fun h => absurd (h.2 (true, false)) (by decide)⟩,
   ⟨fst_putGet, ignorePutSnd_tight_putGet_right.2.1, fun _ _ => rfl,
    ignorePutSnd_tight_putGet_right.2.2.2.2.1, fun h => absurd (h.2 (false, true)) (by decide)⟩,
   ⟨snd_putGet, twist_veryWellBehaved.2.1, twist_snd_not_putIndep,
    twist_tight_putIndep_right.2.2.2.2.1, fun h => absurd (h.2 (false, true)) (by decide)⟩,
   ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ghostFst_ghostSnd_not_jointExt,
    fun h => absurd (h.1 (false, false, true)) (by decide)⟩⟩

/-- In three of the four witnesses of `pairPut_inverse_tight` the pairing map is
still injective and surjective (it is the identity or the swap on
`Bool × Bool`): dropping `PutGet` or `PutIndep l₂ l₁` breaks the formula
`pairPut`, not necessarily the bijectivity of `pairGet`. -/
theorem pairGet_bijective_in_inverse_witnesses :
    (Function.Injective (pairGet ignorePut sndB) ∧ Function.Surjective (pairGet ignorePut sndB)) ∧
    (Function.Injective (pairGet fstB ignorePutSnd) ∧
      Function.Surjective (pairGet fstB ignorePutSnd)) ∧
    (Function.Injective (pairGet sndB twist) ∧ Function.Surjective (pairGet sndB twist)) :=
  ⟨⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩,
   ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩,
   ⟨fun _ _ h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h),
    fun p => ⟨(p.2, p.1), rfl⟩⟩⟩

/-- **Non-vacuity of F1-inverse (ground instance).**  `fst` and the XOR view
satisfy every hypothesis of F1-inverse, although they violate
`PutIndep fst xorView`: the hypotheses of F1-inverse are strictly weaker than
those of F1. -/
theorem f1_inverse_nonvacuity_bool :
    fstB.PutGet ∧ xorView.PutGet ∧ PutIndep xorView fstB ∧ JointExt fstB xorView ∧
    ¬ PutIndep fstB xorView :=
  ⟨fst_putGet, xorView_veryWellBehaved.2.1, xorView_fst_putIndep,
   xorView_tight_putIndep_left.2.2.2.2.1, fst_xorView_not_putIndep⟩

/-- **The hypotheses of F1-inverse do not give the other laws.**
`(resetSibling, snd)` satisfies all hypotheses of F1-inverse and `pairPut` is a
two-sided inverse of `pairGet` there, yet `resetSibling` violates `GetPut` and
does not commute with `snd`; `(dirtyFlag, snd)` satisfies all hypotheses and
`dirtyFlag` violates `PutPut`. -/
theorem f1_inverse_hypotheses_do_not_imply_laws :
    (resetSibling.PutGet ∧ sndB.PutGet ∧ PutIndep sndB resetSibling ∧
      JointExt resetSibling sndB ∧
      Function.LeftInverse (pairPut resetSibling sndB (false, false)) (pairGet resetSibling sndB) ∧
      Function.RightInverse (pairPut resetSibling sndB (false, false))
        (pairGet resetSibling sndB) ∧
      ¬ resetSibling.GetPut ∧ ¬ PutComm resetSibling sndB) ∧
    (dirtyFlag.PutGet ∧ sndB.PutGet ∧ PutIndep sndB dirtyFlag ∧ JointExt dirtyFlag sndB ∧
      ¬ dirtyFlag.PutPut) := by
  refine ⟨⟨resetSibling_putGet, snd_putGet, fun _ _ => rfl,
    f1_laws_bundled_tight.2.2.1.2.2.2.2.1, ?_, ?_, resetSibling_not_getPut, ?_⟩,
    ⟨dirtyFlag_putGet, snd_putGet, fun _ _ => rfl, derived_putPut_tight.2.1.2.2.1,
      dirtyFlag_not_putPut⟩⟩
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · exact fun h => absurd (h (false, false) false true) (by decide)

/-- **The sharp "complement ⇒ laws" direction of F3 needs injectivity.**  The
map that forgets the dirty flag carries `dirtyFlag` to the first-projection
lens on `Bool × Unit`, but it is not injective, and `dirtyFlag` is not very
well-behaved. -/
theorem dirtyFlag_intertwines_fst_noninjective :
    Intertwines (fun p : Bool × Bool => (p.1, ())) dirtyFlag (fst : Lens (Bool × Unit) Bool) ∧
    ¬ Function.Injective (fun p : Bool × Bool => (p.1, ())) ∧
    ¬ dirtyFlag.VeryWellBehaved := by
  refine ⟨⟨fun _ => rfl, ?_⟩, ?_, dirtyFlag_not_veryWellBehaved⟩
  · intro ⟨a, d⟩ a'
    cases a <;> cases d <;> cases a' <;> rfl
  · intro h
    have h' : ((false, false) : Bool × Bool) = (false, true) := h rfl
    exact absurd h' (by decide)

/-- **F3-sharp needs `Intertwines`.**  The identity map is injective but does
not carry `dirtyFlag` to the first-projection lens, and `dirtyFlag` is not very
well-behaved. -/
theorem f3_sharp_intertwines_tight :
    Function.Injective (fun p : Bool × Bool => p) ∧
    ¬ Intertwines (fun p : Bool × Bool => p) dirtyFlag (fst : Lens (Bool × Bool) Bool) ∧
    ¬ dirtyFlag.VeryWellBehaved :=
  ⟨fun _ _ h => h,
   fun h => absurd (h.put_eq (false, false) true) (by decide),
   dirtyFlag_not_veryWellBehaved⟩

/-- **Non-vacuity of F3-sharp (ground instance).**  The identity map is
injective and carries `fst` on `Bool × Bool` to itself. -/
theorem f3_sharp_nonvacuity_bool :
    Function.Injective (fun p : Bool × Bool => p) ∧
    Intertwines (fun p : Bool × Bool => p) fstB (fst : Lens (Bool × Bool) Bool) :=
  ⟨fun _ _ h => h, intertwines_id fstB⟩

/-- **F3 and F3-fiber: each single-lens law is needed.**  `resetSibling`
(fails only `GetPut`), `ignorePut` (fails only `PutGet`) and `dirtyFlag` (fails
only `PutPut`) have no constant complement, and for the base view `false` the
conclusion of `fiber_isConstantComplement_of_veryWellBehaved` fails for each
of them. -/
theorem f3_laws_tight :
    (¬ resetSibling.GetPut ∧ resetSibling.PutGet ∧ resetSibling.PutPut ∧
      ¬ HasConstantComplement resetSibling ∧
      ¬ ∃ e : Equiv (Bool × Bool) (Bool × Fiber resetSibling false),
          Intertwines e.toFun resetSibling (fst : Lens (Bool × Fiber resetSibling false) Bool) ∧
          (∀ s, ((e.toFun s).2).1 = resetSibling.put s false) ∧
          (∀ (a : Bool) (c : Fiber resetSibling false), e.invFun (a, c) = resetSibling.put c.1 a)) ∧
    (ignorePut.GetPut ∧ ¬ ignorePut.PutGet ∧ ignorePut.PutPut ∧
      ¬ HasConstantComplement ignorePut ∧
      ¬ ∃ e : Equiv (Bool × Bool) (Bool × Fiber ignorePut false),
          Intertwines e.toFun ignorePut (fst : Lens (Bool × Fiber ignorePut false) Bool) ∧
          (∀ s, ((e.toFun s).2).1 = ignorePut.put s false) ∧
          (∀ (a : Bool) (c : Fiber ignorePut false), e.invFun (a, c) = ignorePut.put c.1 a)) ∧
    (dirtyFlag.GetPut ∧ dirtyFlag.PutGet ∧ ¬ dirtyFlag.PutPut ∧
      ¬ HasConstantComplement dirtyFlag ∧
      ¬ ∃ e : Equiv (Bool × Bool) (Bool × Fiber dirtyFlag false),
          Intertwines e.toFun dirtyFlag (fst : Lens (Bool × Fiber dirtyFlag false) Bool) ∧
          (∀ s, ((e.toFun s).2).1 = dirtyFlag.put s false) ∧
          (∀ (a : Bool) (c : Fiber dirtyFlag false), e.invFun (a, c) = dirtyFlag.put c.1 a)) :=
  ⟨⟨resetSibling_not_getPut, resetSibling_putGet, resetSibling_putPut,
    resetSibling_not_hasConstantComplement,
    fun ⟨e, h, _⟩ => resetSibling_not_hasConstantComplement ⟨_, e, h⟩⟩,
   ⟨ignorePut_getPut, ignorePut_not_putGet, ignorePut_putPut,
    ignorePut_not_hasConstantComplement,
    fun ⟨e, h, _⟩ => ignorePut_not_hasConstantComplement ⟨_, e, h⟩⟩,
   ⟨dirtyFlag_getPut, dirtyFlag_putGet, dirtyFlag_not_putPut,
    dirtyFlag_not_hasConstantComplement,
    fun ⟨e, h, _⟩ => dirtyFlag_not_hasConstantComplement ⟨_, e, h⟩⟩⟩

/-- **Non-vacuity of F3 and F3-fiber (ground instance).**  `fst` on
`Bool × Bool` is very well-behaved, has a constant complement, and `false` is a
base view. -/
theorem f3_nonvacuity_bool :
    fstB.VeryWellBehaved ∧ HasConstantComplement fstB ∧ Nonempty Bool :=
  ⟨fst_veryWellBehaved, fst_hasConstantComplement, ⟨false⟩⟩

/-! ## F2: every hypothesis is tight

The F1 witnesses, repackaged as `Bool`-indexed families, plus the empty state
type and (below) the finitely-supported sequences.
-/

/-- Two lenses with the same view type, as a `Bool`-indexed family
(`false ↦ l₁`, `true ↦ l₂`). -/
def fam2 {S : Type _} {A : Type _} (l₁ l₂ : Lens S A) : (i : Bool) → Lens S A
  | false => l₁
  | true => l₂

/-- **F2, `PutGet`.**  The read-only first field next to an honest second
field, as a `Bool`-indexed family. -/
theorem fam2_ignorePut_tight_putGet :
    ¬ (∀ i, (fam2 ignorePut sndB i).PutGet) ∧
    PairwiseIndep (fam2 ignorePut sndB) ∧
    FamJointExt (fam2 ignorePut sndB) ∧
    (∀ i : Bool, i ∈ [false, true]) ∧
    (Nonempty (Bool → Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsPiDecomposition (fam2 ignorePut sndB) := by
  refine ⟨fun h => ignorePut_not_putGet (h false), ?_, ?_, ?_, fun _ => ⟨(false, false)⟩, ?_⟩
  · intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
    · exact absurd rfl hij
  · intro s t h
    exact ignorePut_tight_putGet_left.2.2.2.2.1 s t (h false) (h true)
  · intro i
    cases i <;> simp
  · intro h
    have e := congrFun ((h.intertwines false).put_eq (false, false) true) false
    exact absurd e (by decide)

/-- **F2, `PairwiseIndep`.**  The state-twisting setter next to an honest
second field, as a `Bool`-indexed family. -/
theorem fam2_twist_tight_pairwiseIndep :
    (∀ i, (fam2 twist sndB i).PutGet) ∧
    ¬ PairwiseIndep (fam2 twist sndB) ∧
    FamJointExt (fam2 twist sndB) ∧
    (∀ i : Bool, i ∈ [false, true]) ∧
    (Nonempty (Bool → Bool) → Nonempty (Bool × Bool)) ∧
    ¬ IsPiDecomposition (fam2 twist sndB) := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => ⟨(false, false)⟩, ?_⟩
  · intro i
    cases i
    · exact twist_veryWellBehaved.2.1
    · exact fun _ _ => rfl
  · intro h
    exact twist_snd_not_putIndep (h false true (by decide))
  · intro s t h
    exact twist_tight_putIndep_left.2.2.2.2.1 s t (h false) (h true)
  · intro i
    cases i <;> simp
  · intro h
    have e := congrFun ((h.intertwines false).put_eq (false, false) true) true
    exact absurd e (by decide)

/-- **F2, `FamJointExt`.**  The two visible fields of a record with a ghost
component, as a `Bool`-indexed family. -/
theorem ghostFam_tight_famJointExt :
    (∀ i, (ghostFam i).PutGet) ∧
    PairwiseIndep ghostFam ∧
    ¬ FamJointExt ghostFam ∧
    (∀ i : Bool, i ∈ [false, true]) ∧
    (Nonempty (Bool → Bool) → Nonempty (Bool × Bool × Bool)) ∧
    ¬ IsPiDecomposition ghostFam := by
  refine ⟨?_, ?_, ghostFam_not_famJointExt, ?_, fun _ => ⟨(false, false, false)⟩,
    ghostFam_not_isPiDecomposition⟩
  · intro i
    cases i <;> exact fun _ _ => rfl
  · intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
    · exact absurd rfl hij
  · intro i
    cases i <;> simp

/-- **F2, the nonemptiness condition.**  The one-lens family on the empty state
type: the product of the views is inhabited, the state type is not. -/
theorem emptyFam_tight_nonempty :
    (∀ i : Unit, ((fun _ : Unit => emptyLens) i).PutGet) ∧
    PairwiseIndep (fun _ : Unit => emptyLens) ∧
    FamJointExt (fun _ : Unit => emptyLens) ∧
    (∀ i : Unit, i ∈ [()]) ∧
    ¬ (Nonempty (Unit → Unit) → Nonempty Empty) ∧
    ¬ IsPiDecomposition (fun _ : Unit => emptyLens) := by
  refine ⟨fun _ s => s.elim, fun _ _ _ s => s.elim, fun s => s.elim, fun _ => List.Mem.head _,
    fun h => match h ⟨fun _ => ()⟩ with | ⟨s⟩ => s.elim, ?_⟩
  intro h
  obtain ⟨s, _⟩ := h.surjective (fun _ => ())
  exact s.elim

/-! ## F2-laws: every hypothesis of the derived-law lemmas for families is tight

The witnesses are the F1-laws witnesses packaged as `Bool`-indexed families,
at the index `false` (and `true` for the second index of `PutComm`).
-/

/-- A ghost record whose first field clears the ghost bit, as a family. -/
abbrev ghostResetFam : (i : Bool) → Lens (Bool × Bool × Bool) Bool := fam2 ghostReset ghostSndB

/-- A ghost record whose first field keeps a dirty flag in the ghost bit, as a
family. -/
abbrev ghostDirtyFam : (i : Bool) → Lens (Bool × Bool × Bool) Bool := fam2 ghostDirty ghostSndB

/-- `ghostFst` next to the ghost-twisting second field, as a family. -/
abbrev ghostTwistFam : (i : Bool) → Lens (Bool × Bool × Bool) Bool :=
  fam2 ghostFstB ghostTwistSnd

theorem fam2_jointExt {S : Type _} {A : Type _} {l₁ l₂ : Lens S A} (h : JointExt l₁ l₂) :
    FamJointExt (fam2 l₁ l₂) :=
  fun s t hst => h s t (hst false) (hst true)

theorem fam2_not_jointExt {S : Type _} {A : Type _} {l₁ l₂ : Lens S A} (h : ¬ JointExt l₁ l₂) :
    ¬ FamJointExt (fam2 l₁ l₂) :=
  fun hf => h fun s t h₁ h₂ => hf s t fun i => by cases i; exact h₁; exact h₂

/-- **Derived law 1 (family) is tight** in each of its three hypotheses
(index `i = false`). -/
theorem f2_getPut_tight :
    (¬ (fam2 flipPut sndB false).PutGet ∧
      (∀ j, false ≠ j → PutIndep (fam2 flipPut sndB false) (fam2 flipPut sndB j)) ∧
      FamJointExt (fam2 flipPut sndB) ∧ ¬ (fam2 flipPut sndB false).GetPut) ∧
    ((fam2 resetSibling sndB false).PutGet ∧
      ¬ (∀ j, false ≠ j → PutIndep (fam2 resetSibling sndB false) (fam2 resetSibling sndB j)) ∧
      FamJointExt (fam2 resetSibling sndB) ∧ ¬ (fam2 resetSibling sndB false).GetPut) ∧
    ((ghostResetFam false).PutGet ∧
      (∀ j, false ≠ j → PutIndep (ghostResetFam false) (ghostResetFam j)) ∧
      ¬ FamJointExt ghostResetFam ∧ ¬ (ghostResetFam false).GetPut) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩⟩ := derived_getPut_tight
  refine ⟨⟨a1, ?_, fam2_jointExt a3, a4⟩, ⟨b1, ?_, fam2_jointExt b3, b4⟩,
    ⟨c1, ?_, fam2_not_jointExt c3, c4⟩⟩
  · intro j hj; cases j; exact absurd rfl hj; exact a2
  · exact fun h => b2 (h true (by decide))
  · intro j hj; cases j; exact absurd rfl hj; exact c2

/-- **Derived law 2 (family) is tight** in each of its three hypotheses
(index `i = false`). -/
theorem f2_putPut_tight :
    (¬ (fam2 flipPut sndB false).PutGet ∧
      (∀ j, false ≠ j → PutIndep (fam2 flipPut sndB false) (fam2 flipPut sndB j)) ∧
      FamJointExt (fam2 flipPut sndB) ∧ ¬ (fam2 flipPut sndB false).PutPut) ∧
    ((fam2 dirtyFlag sndB false).PutGet ∧
      ¬ (∀ j, false ≠ j → PutIndep (fam2 dirtyFlag sndB false) (fam2 dirtyFlag sndB j)) ∧
      FamJointExt (fam2 dirtyFlag sndB) ∧ ¬ (fam2 dirtyFlag sndB false).PutPut) ∧
    ((ghostDirtyFam false).PutGet ∧
      (∀ j, false ≠ j → PutIndep (ghostDirtyFam false) (ghostDirtyFam j)) ∧
      ¬ FamJointExt ghostDirtyFam ∧ ¬ (ghostDirtyFam false).PutPut) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩⟩ := derived_putPut_tight
  refine ⟨⟨a1, ?_, fam2_jointExt a3, a4⟩, ⟨b1, ?_, fam2_jointExt b3, b4⟩,
    ⟨c1, ?_, fam2_not_jointExt c3, c4⟩⟩
  · intro j hj; cases j; exact absurd rfl hj; exact a2
  · exact fun h => b2 (h true (by decide))
  · intro j hj; cases j; exact absurd rfl hj; exact c2

/-- **Derived law 3 (family) is tight** in each of its six hypotheses
(indices `i = false`, `j = true`; for `i ≠ j`, a one-lens family indexed by
`Unit`). -/
theorem f2_putComm_tight :
    -- dropping `i ≠ j`
    (¬ ((): Unit) ≠ () ∧ idB.PutGet ∧ idB.PutGet ∧
      (∀ k : Unit, () ≠ k → PutIndep ((fun _ : Unit => idB) ()) ((fun _ : Unit => idB) k)) ∧
      (∀ k : Unit, () ≠ k → PutIndep ((fun _ : Unit => idB) ()) ((fun _ : Unit => idB) k)) ∧
      FamJointExt (fun _ : Unit => idB) ∧ ¬ PutComm idB idB) ∧
    -- dropping `PutGet (l i)`
    (¬ (fam2 copySibling sndB false).PutGet ∧ (fam2 copySibling sndB true).PutGet ∧
      (∀ k, false ≠ k → PutIndep (fam2 copySibling sndB false) (fam2 copySibling sndB k)) ∧
      (∀ k, true ≠ k → PutIndep (fam2 copySibling sndB true) (fam2 copySibling sndB k)) ∧
      FamJointExt (fam2 copySibling sndB) ∧
      ¬ PutComm (fam2 copySibling sndB false) (fam2 copySibling sndB true)) ∧
    -- dropping `PutGet (l j)`
    ((fam2 sndB copySibling false).PutGet ∧ ¬ (fam2 sndB copySibling true).PutGet ∧
      (∀ k, false ≠ k → PutIndep (fam2 sndB copySibling false) (fam2 sndB copySibling k)) ∧
      (∀ k, true ≠ k → PutIndep (fam2 sndB copySibling true) (fam2 sndB copySibling k)) ∧
      FamJointExt (fam2 sndB copySibling) ∧
      ¬ PutComm (fam2 sndB copySibling false) (fam2 sndB copySibling true)) ∧
    -- dropping the frame law at `i`
    ((fam2 twist sndB false).PutGet ∧ (fam2 twist sndB true).PutGet ∧
      ¬ (∀ k, false ≠ k → PutIndep (fam2 twist sndB false) (fam2 twist sndB k)) ∧
      (∀ k, true ≠ k → PutIndep (fam2 twist sndB true) (fam2 twist sndB k)) ∧
      FamJointExt (fam2 twist sndB) ∧
      ¬ PutComm (fam2 twist sndB false) (fam2 twist sndB true)) ∧
    -- dropping the frame law at `j`
    ((fam2 sndB twist false).PutGet ∧ (fam2 sndB twist true).PutGet ∧
      (∀ k, false ≠ k → PutIndep (fam2 sndB twist false) (fam2 sndB twist k)) ∧
      ¬ (∀ k, true ≠ k → PutIndep (fam2 sndB twist true) (fam2 sndB twist k)) ∧
      FamJointExt (fam2 sndB twist) ∧
      ¬ PutComm (fam2 sndB twist false) (fam2 sndB twist true)) ∧
    -- dropping `FamJointExt`
    ((ghostTwistFam false).PutGet ∧ (ghostTwistFam true).PutGet ∧
      (∀ k, false ≠ k → PutIndep (ghostTwistFam false) (ghostTwistFam k)) ∧
      (∀ k, true ≠ k → PutIndep (ghostTwistFam true) (ghostTwistFam k)) ∧
      ¬ FamJointExt ghostTwistFam ∧
      ¬ PutComm (ghostTwistFam false) (ghostTwistFam true)) := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, ⟨t1, t2, t3, t4, t5, t6⟩,
    ⟨⟨_, g1, _⟩, ⟨_, g2, _⟩, g3, g4, g5, g6⟩⟩ := derived_putComm_tight
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, ⟨n1, n2, n3, n4, n5, n6⟩⟩ := derived_putComm_tight_mirror
  refine ⟨⟨fun h => h rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, fun _ _ h => h (),
      fun h => absurd (h false false true) (by decide)⟩,
    ⟨c1, c2, ?_, ?_, fam2_jointExt c5, c6⟩,
    ⟨m1, m2, ?_, ?_, fam2_jointExt m5, m6⟩,
    ⟨t1, t2, fun h => t3 (h true (by decide)), ?_, fam2_jointExt t5, t6⟩,
    ⟨n1, n2, ?_, fun h => n4 (h false (by decide)), fam2_jointExt n5, n6⟩,
    ⟨g1, g2, ?_, ?_, fam2_not_jointExt g5, g6⟩⟩
  · intro k hk; exact absurd rfl hk
  · intro k hk; exact absurd rfl hk
  · intro k hk; cases k; exact absurd rfl hk; exact c3
  · intro k hk; cases k; exact c4; exact absurd rfl hk
  · intro k hk; cases k; exact absurd rfl hk; exact m3
  · intro k hk; cases k; exact m4; exact absurd rfl hk
  · intro k hk; cases k; exact t4; exact absurd rfl hk
  · intro k hk; cases k; exact absurd rfl hk; exact n3
  · intro k hk; cases k; exact absurd rfl hk; exact g3
  · intro k hk; cases k; exact g4; exact absurd rfl hk

/-- **Non-vacuity of F2-laws (ground instance).**  The coordinate lenses on
`Bool → Bool` satisfy every hypothesis of the three derived-law lemmas for
families, at the distinct indices `false` and `true`. -/
theorem f2_laws_nonvacuity_bool :
    (coord (A := fun _ : Bool => Bool) false).PutGet ∧
    (coord (A := fun _ : Bool => Bool) true).PutGet ∧
    (∀ k, false ≠ k → PutIndep (coord (A := fun _ : Bool => Bool) false)
      (coord (A := fun _ : Bool => Bool) k)) ∧
    (∀ k, true ≠ k → PutIndep (coord (A := fun _ : Bool => Bool) true)
      (coord (A := fun _ : Bool => Bool) k)) ∧
    FamJointExt (fun i : Bool => coord (A := fun _ : Bool => Bool) i) ∧
    (false : Bool) ≠ true :=
  ⟨coord_putGet false, coord_putGet true, coord_pairwiseIndep false, coord_pairwiseIndep true,
   coord_famJointExt, by decide⟩

/-! ## Why the witness must be exposed

A weaker conclusion asserting only that *some* bijection `S ≃ A × B` exists
cannot express "no ghost state": the ghost record `Nat × Nat × Bool` with its
two `Nat` fields *does* admit a bijection onto `Nat × Nat` — one that has
nothing to do with the two getters.
-/

/-- A bijection `Nat × Nat × Bool ≃ Nat × Nat` that folds the ghost bit into
the parity of the first number. -/
def ghostEquiv : Equiv (Nat × Nat × Bool) (Nat × Nat) where
  toFun s := (2 * s.1 + (if s.2.2 then 1 else 0), s.2.1)
  invFun p := (p.1 / 2, p.2, p.1 % 2 == 1)
  left_inv := by
    intro ⟨a, b, g⟩
    cases g
    · simp
    · have h₁ : (2 * a + 1) / 2 = a := by omega
      have h₂ : (2 * a + 1) % 2 = 1 := by omega
      simp [h₁, h₂]
  right_inv := by
    intro ⟨n, b⟩
    have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
    cases h with
    | inl h =>
      have h₁ : 2 * (n / 2) + 0 = n := by omega
      simp [h, h₁]
    | inr h =>
      have h₁ : 2 * (n / 2) + 1 = n := by omega
      simp [h, h₁]

/-- **A bare bijection does not exclude ghosts.**  The ghost record
`Nat × Nat × Bool` is in bijection with `Nat × Nat`, although its two field
lenses are not jointly extensional and do not form a product decomposition.
Hence a conclusion of the form "there exists a bijection `S ≃ A × B`" is too
weak to state F1; the specific map `pairGet` has to appear in the statement. -/
theorem ghost_admits_unrelated_bijection :
    Nonempty (Equiv (Nat × Nat × Bool) (Nat × Nat)) ∧
    ¬ JointExt (ghostFst : Lens (Nat × Nat × Bool) Nat) (ghostSnd : Lens (Nat × Nat × Bool) Nat) ∧
    ¬ IsProductDecomposition (ghostFst : Lens (Nat × Nat × Bool) Nat)
      (ghostSnd : Lens (Nat × Nat × Bool) Nat) := by
  have hext : ¬ JointExt (ghostFst : Lens (Nat × Nat × Bool) Nat)
      (ghostSnd : Lens (Nat × Nat × Bool) Nat) :=
    fun h => absurd (h (0, 0, false) (0, 0, true) rfl rfl) (by decide)
  refine ⟨⟨ghostEquiv⟩, hext, fun h => hext ?_⟩
  intro s t h₁ h₂
  apply h.injective
  show (s.1, s.2.1) = (t.1, t.2.1)
  have e₁ : s.1 = t.1 := h₁
  have e₂ : s.2.1 = t.2.1 := h₂
  rw [e₁, e₂]

/-! ## F2: the finiteness hypothesis is tight -/

/-- Boolean sequences that are eventually `false` ("finitely supported"). -/
def EvFalse : Type :=
  { f : Nat → Bool // ∃ N, ∀ n, N ≤ n → f n = false }

/-- The `i`-th coordinate lens on eventually-`false` sequences. -/
def evCoord (i : Nat) : Lens EvFalse Bool where
  get f := f.1 i
  put f a :=
    ⟨update (A := fun _ => Bool) f.1 i a, by
      obtain ⟨N, hN⟩ := f.2
      refine ⟨N + i + 1, fun n hn => ?_⟩
      have hne : n ≠ i := by omega
      rw [update_of_ne _ hne]
      exact hN n (by omega)⟩

/-- Every element of a list of naturals is at most the sum of the list. -/
theorem le_foldr_add_of_mem : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr (· + ·) 0
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    cases h with
    | head => simp only [List.foldr]; omega
    | tail _ h' =>
      have := le_foldr_add_of_mem ys x h'
      simp only [List.foldr]
      omega

/-- `Nat` is not enumerated by any list. -/
theorem not_finite_nat : ¬ ∃ elems : List Nat, ∀ i, i ∈ elems := by
  intro ⟨elems, h⟩
  have := le_foldr_add_of_mem elems _ (h (elems.foldr (· + ·) 0 + 1))
  omega

/-- **F2, finiteness of the index type.**  The coordinate lenses on
eventually-`false` Boolean sequences, indexed by `Nat`, satisfy every
hypothesis of F2 except finiteness of the index type, and the conclusion
fails: the constant-`true` sequence is not in the image of `famGet`. -/
theorem evCoord_tight_finite_index :
    (∀ i, (evCoord i).PutGet) ∧
    PairwiseIndep evCoord ∧
    FamJointExt evCoord ∧
    ¬ (∃ elems : List Nat, ∀ i, i ∈ elems) ∧
    (Nonempty (Nat → Bool) → Nonempty EvFalse) ∧
    ¬ Function.Surjective (famGet evCoord) ∧
    ¬ IsPiDecomposition evCoord := by
  have hsurj : ¬ Function.Surjective (famGet evCoord) := by
    intro h
    obtain ⟨s, hs⟩ := h (fun _ => true)
    obtain ⟨N, hN⟩ := s.2
    have h₁ : s.1 N = true := congrFun hs N
    rw [hN N (Nat.le_refl N)] at h₁
    exact absurd h₁ (by decide)
  refine ⟨?_, ?_, ?_, not_finite_nat, fun _ => ⟨⟨fun _ => false, 0, fun _ _ => rfl⟩⟩, hsurj,
    fun h => hsurj h.surjective⟩
  · intro i f a
    exact update_same (A := fun _ => Bool) f.1 i a
  · intro i j hij f a
    exact update_of_ne (A := fun _ => Bool) f.1 (fun h => hij h.symm) a
  · intro s t h
    exact Subtype.ext (funext h)

/-- **The pair form of F3 does not extend to infinite families.**  The
coordinate lenses on eventually-`false` sequences are very well-behaved and
pairwise commuting, yet no bijection `EvFalse ≃ (Nat → Bool) × G` (for any `G`)
turns every getter into the corresponding coordinate of the first component. -/
theorem evCoord_veryWellBehaved_putComm_no_pi_complement :
    (∀ i, (evCoord i).VeryWellBehaved) ∧
    (∀ i j, i ≠ j → PutComm (evCoord i) (evCoord j)) ∧
    ¬ ∃ (G : Type u) (e : Equiv EvFalse ((Nat → Bool) × G)),
        ∀ s i, (e.toFun s).1 i = (evCoord i).get s := by
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f
    apply Subtype.ext
    funext j
    show update (A := fun _ => Bool) f.1 i (f.1 i) j = f.1 j
    by_cases h : j = i
    · subst h; exact update_same (A := fun _ => Bool) f.1 j (f.1 j)
    · exact update_of_ne (A := fun _ => Bool) f.1 h (f.1 i)
  · intro f a
    exact update_same (A := fun _ => Bool) f.1 i a
  · intro f a a'
    apply Subtype.ext
    funext j
    show update (A := fun _ => Bool) (update (A := fun _ => Bool) f.1 i a) i a' j =
      update (A := fun _ => Bool) f.1 i a' j
    by_cases h : j = i
    · subst h; rw [update_same, update_same]
    · rw [update_of_ne _ h, update_of_ne _ h, update_of_ne _ h]
  · intro i j hij f a b
    apply Subtype.ext
    funext k
    show update (A := fun _ => Bool) (update (A := fun _ => Bool) f.1 i a) j b k =
      update (A := fun _ => Bool) (update (A := fun _ => Bool) f.1 j b) i a k
    by_cases hk : k = j
    · subst hk
      rw [update_same, update_of_ne _ (fun h => hij h.symm), update_same]
    · by_cases hi : k = i
      · subst hi
        rw [update_of_ne _ hk, update_same, update_same]
      · rw [update_of_ne _ hk, update_of_ne _ hi, update_of_ne _ hi, update_of_ne _ hk]
  · intro ⟨G, e, he⟩
    let s₀ : EvFalse := ⟨fun _ => false, 0, fun _ _ => rfl⟩
    let s : EvFalse := e.invFun (fun _ => true, (e.toFun s₀).2)
    have hs : ∀ i, s.1 i = true := fun i =>
      (he s i).symm.trans (congrArg (fun q => q.1 i) (e.right_inv (fun _ => true, (e.toFun s₀).2)))
    obtain ⟨N, hN⟩ := s.2
    have h₁ := hs N
    rw [hN N (Nat.le_refl N)] at h₁
    exact absurd h₁ (by decide)

end Lens

end Toy

