import ToyTransmute.Tools

/-!
# Main results

Notation used in the comments: `T ⊆ U` is `Includes T U`; `T ≡ U` is `ValidityEq T U`;
"satisfiable" is `Satisfiable`; `T ⊓ U` and `T ⊔ U` are `Validity.meet` and `Validity.join`.
Every statement relates two types of the same size `n` whose views cover one and the same
`n`-byte region.

* R1  value transmute:            sound ↔ `T ⊆ U`.
* R2  shared cast (no interior mutability): sound ↔ `T ⊆ U`.
* R3  mutable cast:               sound ↔ `T ⊆ U ∧ (T satisfiable → U ⊆ T)`;
                                  for satisfiable `T`: sound ↔ `T ≡ U`.
* R4  shared cast with interior mutability, write flags `(srcWrites, dstWrites)`:
                                  sound ↔ `T ⊆ U ∧ (dstWrites → T satisfiable → U ⊆ T)`.
                                  Source-side writes add no validity requirement.
* R5  composition and the hierarchy mutable ⇒ shared ⇔ value.
* R7  validity as a lattice (meet = intersection, join = union).
* R8  casts checked once at cast time (`CheckedSound`): value and shared casts are always
      sound; a checked mutable cast is sound ↔ `(T ⊓ U satisfiable → U ⊆ T)`; a checked
      shared cast with interior mutability is sound ↔
      `(T ⊓ U satisfiable → (srcWrites → T ⊆ U) ∧ (dstWrites → U ⊆ T))`.
-/

namespace Toy.Transmute

variable {B : Type} {n : Nat}

/-! ## Two necessity lemmas used below -/

/-- Soundness of a discipline that permits the run `readDst` gives `T ⊆ U`. -/
theorem includes_of_sound_readDst {P : Protocol B n} {T U : Validity B n} (hP : P readDst)
    (h : Sound P T U) : Includes T U :=
  fun m hm => (h m hm readDst hP readDst_wellTyped).1

/-- Soundness of a discipline that permits every run `writeDstReadSrc u` gives
`T satisfiable → U ⊆ T`. -/
theorem includes_rev_of_sound_writeDstReadSrc {P : Protocol B n} {T U : Validity B n}
    (hP : ∀ u, P (writeDstReadSrc u)) (h : Sound P T U) : Satisfiable T → Includes U T := by
  rintro ⟨m, hm⟩ u hu
  exact (h m hm _ (hP u) (writeDstReadSrc_wellTyped hu)).1

/-! ## R1. Value transmute -/

/-- **R1.** A value transmute from `T` to `U` (equal sizes by construction) is sound, in the
sense that no permitted, well-typed use of the destination value ever reads bytes invalid
at `U`, iff every `T`-valid byte sequence is `U`-valid. -/
theorem valueSound_iff_includes (T U : Validity B n) :
    ValueSound T U ↔ Includes T U := by
  constructor
  · exact includes_of_sound_readDst valueProtocol_readDst
  · intro h
    exact valueSound_of_invariant U h (fun _ hm => hm) (fun _ hv => hv)

/-! ## R2. Shared-reference cast without interior mutability -/

/-- **R2.** A shared-reference cast from `T` to `U` with no writes through either reference
is sound iff every `T`-valid byte sequence is `U`-valid. -/
theorem sharedSound_iff_includes (T U : Validity B n) :
    SharedSound T U ↔ Includes T U := by
  constructor
  · exact includes_of_sound_readDst sharedProtocol_readDst
  · intro h
    exact sharedSound_of_invariant T (fun _ hm => hm) (fun _ hm => hm) h

/-! ## R3. Mutable-reference cast -/

/-- **R3 (exact).** A mutable-reference cast from `T` to `U` is sound iff `T ⊆ U` (needed by
reads through the cast reference) and, when `T` is satisfiable, `U ⊆ T` (needed because a
`U`-valid value written through the cast reference is later read at `T` by the owner). When
`T` is unsatisfiable the cast is vacuously sound. -/
theorem mutSound_iff_includes_and_satisfiable_imp_includes_rev (T U : Validity B n) :
    MutSound T U ↔ Includes T U ∧ (Satisfiable T → Includes U T) := by
  constructor
  · intro h
    exact ⟨includes_of_sound_readDst mutProtocol_readDst h,
      includes_rev_of_sound_writeDstReadSrc mutProtocol_writeDstReadSrc h⟩
  · rintro ⟨h₁, h₂⟩ m hm
    exact sound_of_validityEq mutProtocol (fun x => ⟨h₁ x, h₂ ⟨m, hm⟩ x⟩) m hm

/-- **R3 (equality form).** For a satisfiable source type `T`, a mutable-reference cast from
`T` to `U` is sound iff `T` and `U` have exactly the same valid byte sequences. -/
theorem mutSound_iff_validityEq_of_satisfiable {T U : Validity B n} (hT : Satisfiable T) :
    MutSound T U ↔ ValidityEq T U := by
  rw [mutSound_iff_includes_and_satisfiable_imp_includes_rev]
  constructor
  · rintro ⟨h₁, h₂⟩ x
    exact ⟨h₁ x, h₂ hT x⟩
  · intro h
    exact ⟨fun x => (h x).1, fun _ x => (h x).2⟩

/-- **R3 (impossibility form).** No unchecked mutable-reference cast from a satisfiable `T` to
a `U` with different validity is sound. (A cast checked at cast time is a different
discipline; see R8.) -/
theorem not_mutSound_of_satisfiable_of_not_validityEq {T U : Validity B n}
    (hT : Satisfiable T) (hne : ¬ ValidityEq T U) : ¬ MutSound T U := by
  intro h
  exact hne ((mutSound_iff_validityEq_of_satisfiable hT).1 h)

/-! ## R4. Shared-reference cast with interior mutability -/

/-- **R4 (exact).** A shared-reference cast from `T` to `U` in which both references stay
live, the source side may write iff `srcWrites` and the destination side may write iff
`dstWrites`, is sound for bit validity iff `T ⊆ U` and, if the destination side may write
and `T` is satisfiable, `U ⊆ T`. The flag `srcWrites` does not appear on the right-hand
side. Aliasing rules of a real language are not modelled. -/
theorem sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev
    (srcWrites dstWrites : Bool) (T U : Validity B n) :
    SharedIMSound srcWrites dstWrites T U ↔
      Includes T U ∧ (dstWrites = true → Satisfiable T → Includes U T) := by
  constructor
  · intro h
    refine ⟨includes_of_sound_readDst (sharedIMProtocol_readDst srcWrites dstWrites) h, ?_⟩
    intro hd
    subst hd
    exact includes_rev_of_sound_writeDstReadSrc (sharedIMProtocol_writeDstReadSrc srcWrites) h
  · rintro ⟨h₁, h₂⟩
    cases dstWrites with
    | false =>
      exact sharedIMSound_of_invariant T (fun _ hm => hm) (fun _ hm => hm) h₁
        (fun _ _ hv => hv) (fun hd => absurd hd Bool.false_ne_true)
    | true =>
      intro m hm
      exact sound_of_validityEq _ (fun x => ⟨h₁ x, h₂ rfl ⟨m, hm⟩ x⟩) m hm

/-- **R4 (equality form).** If the destination side may write and `T` is satisfiable, a
shared cast with interior mutability from `T` to `U` is sound for bit validity iff `T ≡ U`,
whatever the source side may do. -/
theorem sharedIMSound_dstWrites_iff_validityEq_of_satisfiable (srcWrites : Bool)
    {T U : Validity B n} (hT : Satisfiable T) :
    SharedIMSound srcWrites true T U ↔ ValidityEq T U := by
  rw [sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev]
  constructor
  · rintro ⟨h₁, h₂⟩ x
    exact ⟨h₁ x, h₂ rfl hT x⟩
  · intro h
    exact ⟨fun x => (h x).1, fun _ _ x => (h x).2⟩

/-- **R4 (source-only writes).** If the destination side may not write, a shared cast with
interior mutability from `T` to `U` is sound for bit validity iff `T ⊆ U`, even if the source
side writes. -/
theorem sharedIMSound_noDstWrites_iff_includes (srcWrites : Bool) (T U : Validity B n) :
    SharedIMSound srcWrites false T U ↔ Includes T U := by
  rw [sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev]
  exact ⟨fun h => h.1, fun h => ⟨h, fun hd => absurd hd Bool.false_ne_true⟩⟩

/-- **R4 (coincidence with mutable casts).** Soundness of a mutable-reference cast coincides
with soundness of a shared cast with interior mutability in which the destination side may
write (for either value of the source flag). -/
theorem mutSound_iff_sharedIMSound_dstWrites (srcWrites : Bool) (T U : Validity B n) :
    MutSound T U ↔ SharedIMSound srcWrites true T U := by
  rw [mutSound_iff_includes_and_satisfiable_imp_includes_rev,
    sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev]
  exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 rfl⟩⟩

/-! ## R5. Composition and hierarchy -/

/-- **R5.** Value-transmute soundness composes. -/
theorem valueSound_trans {T U V : Validity B n} (h₁ : ValueSound T U) (h₂ : ValueSound U V) :
    ValueSound T V := by
  have a₁ := (valueSound_iff_includes T U).1 h₁
  have a₂ := (valueSound_iff_includes U V).1 h₂
  exact (valueSound_iff_includes T V).2 (fun m hm => a₂ m (a₁ m hm))

/-- **R5.** Shared-cast soundness composes. -/
theorem sharedSound_trans {T U V : Validity B n} (h₁ : SharedSound T U)
    (h₂ : SharedSound U V) : SharedSound T V := by
  have a₁ := (sharedSound_iff_includes T U).1 h₁
  have a₂ := (sharedSound_iff_includes U V).1 h₂
  exact (sharedSound_iff_includes T V).2 (fun m hm => a₂ m (a₁ m hm))

/-- **R5.** Mutable-cast soundness composes (including chains that start at an unsatisfiable
type). -/
theorem mutSound_trans {T U V : Validity B n} (h₁ : MutSound T U) (h₂ : MutSound U V) :
    MutSound T V := by
  obtain ⟨a₁, b₁⟩ := (mutSound_iff_includes_and_satisfiable_imp_includes_rev T U).1 h₁
  obtain ⟨a₂, b₂⟩ := (mutSound_iff_includes_and_satisfiable_imp_includes_rev U V).1 h₂
  refine (mutSound_iff_includes_and_satisfiable_imp_includes_rev T V).2
    ⟨fun m hm => a₂ m (a₁ m hm), ?_⟩
  rintro ⟨m, hm⟩ x hx
  exact b₁ ⟨m, hm⟩ x (b₂ ⟨m, a₁ m hm⟩ x hx)

/-- **R5.** Soundness of shared casts with interior mutability composes, for fixed write
flags. -/
theorem sharedIMSound_trans (srcWrites dstWrites : Bool) {T U V : Validity B n}
    (h₁ : SharedIMSound srcWrites dstWrites T U) (h₂ : SharedIMSound srcWrites dstWrites U V) :
    SharedIMSound srcWrites dstWrites T V := by
  obtain ⟨a₁, b₁⟩ :=
    (sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev
      srcWrites dstWrites T U).1 h₁
  obtain ⟨a₂, b₂⟩ :=
    (sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev
      srcWrites dstWrites U V).1 h₂
  refine (sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev
    srcWrites dstWrites T V).2 ⟨fun m hm => a₂ m (a₁ m hm), ?_⟩
  rintro hd ⟨m, hm⟩ x hx
  exact b₁ hd ⟨m, hm⟩ x (b₂ hd ⟨m, a₁ m hm⟩ x hx)

/-- **R5.** Shared-cast soundness implies value-transmute soundness. -/
theorem valueSound_of_sharedSound {T U : Validity B n} (h : SharedSound T U) :
    ValueSound T U := by
  exact (valueSound_iff_includes T U).2 ((sharedSound_iff_includes T U).1 h)

/-- **R5.** In this model value-transmute soundness also implies shared-cast soundness (the
two coincide; this does not transfer to real reference casts, which also involve alignment,
size relations and aliasing rules). -/
theorem sharedSound_of_valueSound {T U : Validity B n} (h : ValueSound T U) :
    SharedSound T U := by
  exact (sharedSound_iff_includes T U).2 ((valueSound_iff_includes T U).1 h)

/-- **R5.** Mutable-cast soundness implies shared-cast soundness. -/
theorem sharedSound_of_mutSound {T U : Validity B n} (h : MutSound T U) :
    SharedSound T U := by
  exact (sharedSound_iff_includes T U).2
    ((mutSound_iff_includes_and_satisfiable_imp_includes_rev T U).1 h).1

/-- **R5.** A sound mutable cast from a satisfiable source can be reversed. This is a one-way
implication: the biconditional `MutSound T U ↔ MutSound U T` can fail when `U` is
unsatisfiable (see `mutSound_not_iff_symm_of_satisfiable_left`). -/
theorem mutSound_symm_of_satisfiable {T U : Validity B n} (hT : Satisfiable T)
    (h : MutSound T U) : MutSound U T := by
  have he := (mutSound_iff_validityEq_of_satisfiable hT).1 h
  exact sound_of_validityEq _ (fun x => (he x).symm)

/-! ## R7. Validity as a lattice -/

/-- **R7.** Shared casts into a join are sound: `T → T ⊔ U`. -/
theorem sharedSound_to_join_left (T U : Validity B n) : SharedSound T (T.join U) := by
  exact (sharedSound_iff_includes _ _).2 (fun _ hm => Or.inl hm)

/-- **R7.** Shared casts into a join are sound: `U → T ⊔ U`. -/
theorem sharedSound_to_join_right (T U : Validity B n) : SharedSound U (T.join U) := by
  exact (sharedSound_iff_includes _ _).2 (fun _ hm => Or.inr hm)

/-- **R7.** Shared casts out of a meet are sound: `T ⊓ U → T`. -/
theorem sharedSound_from_meet_left (T U : Validity B n) : SharedSound (T.meet U) T := by
  exact (sharedSound_iff_includes _ _).2 (fun _ hm => hm.1)

/-- **R7.** Shared casts out of a meet are sound: `T ⊓ U → U`. -/
theorem sharedSound_from_meet_right (T U : Validity B n) : SharedSound (T.meet U) U := by
  exact (sharedSound_iff_includes _ _).2 (fun _ hm => hm.2)

/-- **R7.** A shared cast out of the join `T ⊔ U` into `V` is sound iff the shared casts
`T → V` and `U → V` are both sound (the join is a least upper bound for shared
castability). -/
theorem sharedSound_join_iff (T U V : Validity B n) :
    SharedSound (T.join U) V ↔ SharedSound T V ∧ SharedSound U V := by
  rw [sharedSound_iff_includes, sharedSound_iff_includes, sharedSound_iff_includes]
  constructor
  · intro h
    exact ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩
  · rintro ⟨h₁, h₂⟩ m hm
    rcases hm with hm | hm
    · exact h₁ m hm
    · exact h₂ m hm

/-- **R7.** Dually, a shared cast from `V` into the meet `T ⊓ U` is sound iff the shared
casts `V → T` and `V → U` are both sound (the meet is a greatest lower bound). -/
theorem sharedSound_meet_iff (T U V : Validity B n) :
    SharedSound V (T.meet U) ↔ SharedSound V T ∧ SharedSound V U := by
  rw [sharedSound_iff_includes, sharedSound_iff_includes, sharedSound_iff_includes]
  constructor
  · intro h
    exact ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩
  · rintro ⟨h₁, h₂⟩ m hm
    exact And.intro (h₁ m hm) (h₂ m hm)

/-- **R7.** For satisfiable `T`, a mutable cast into the join `T ⊔ U` is sound iff the join
adds nothing, that is iff `U ⊆ T` (the reverse inclusion `Includes U T`): writing an
alternative that is only `U`-valid and reading it back at `T` breaks it. -/
theorem mutSound_to_join_left_iff_includes_rev_of_satisfiable {T U : Validity B n}
    (hT : Satisfiable T) : MutSound T (T.join U) ↔ Includes U T := by
  rw [mutSound_iff_validityEq_of_satisfiable hT]
  constructor
  · intro h m hm
    exact (h m).2 (Or.inr hm)
  · intro h m
    exact ⟨Or.inl, fun hm => hm.elim id (h m)⟩

/-- **R7.** If the meet `T ⊓ U` is satisfiable (some byte sequence is valid at both `T` and
`U`; satisfiability of `T` and of `U` separately is not enough), a mutable cast out of the
meet into `T` is sound iff the meet removes nothing from `T` (`T ⊆ U`). -/
theorem mutSound_from_meet_left_iff_includes_of_satisfiable_meet {T U : Validity B n}
    (h : Satisfiable (T.meet U)) : MutSound (T.meet U) T ↔ Includes T U := by
  rw [mutSound_iff_validityEq_of_satisfiable h]
  constructor
  · intro he m hm
    exact ((he m).2 hm).2
  · intro hi m
    exact ⟨fun hm => hm.1, fun hm => And.intro hm (hi m hm)⟩

/-! ## R8. Casts checked once at cast time -/

/-- **R8 (value).** A value transmute checked once at cast time (it goes ahead only when the
bytes are valid at `U`) is sound for every pair of equal-size types. -/
theorem checkedSound_valueProtocol (T U : Validity B n) :
    CheckedSound valueProtocol T U := by
  exact checkedSound_value_of_invariant U (fun _ _ hU => hU) (fun _ h => h) (fun _ h => h)

/-- **R8 (shared, no interior mutability).** A shared-reference cast checked once at cast time
is sound for every pair of equal-size types: nobody writes after the check. -/
theorem checkedSound_sharedProtocol (T U : Validity B n) :
    CheckedSound sharedProtocol T U := by
  exact checkedSound_shared_of_invariant (fun m => T m ∧ U m) (fun _ hT hU => ⟨hT, hU⟩)
    (fun _ h => h.1) (fun _ h => h.2)

/-- **R8 (mutable).** A mutable-reference cast checked once at cast time is sound iff, provided
some byte sequence is valid at both `T` and `U` (otherwise the check never succeeds), every
`U`-valid byte sequence is `T`-valid. The read-side condition `T ⊆ U` of R3 is not needed:
the check discharges it for the initial contents, and later contents are written at `U`. -/
theorem checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev (T U : Validity B n) :
    CheckedSound mutProtocol T U ↔ (Satisfiable (T.meet U) → Includes U T) := by
  constructor
  · rintro h ⟨m, hT, hU⟩ u hu
    exact (h m hT hU _ (mutProtocol_writeDstReadSrc u) (writeDstReadSrc_wellTyped hu)).1
  · intro hc m hT hU
    have hrev := hc ⟨m, hT, hU⟩
    exact checkedSound_mut_of_invariants U T (fun _ _ h => h) hrev (fun _ h => h)
      (fun _ h => h) (fun _ h => h) (fun _ h => h) m hT hU

/-- **R8 (shared with interior mutability).** A shared-reference cast with interior mutability
checked once at cast time is sound for bit validity iff, provided some byte sequence is valid
at both `T` and `U`, source-side writes require `T ⊆ U` and destination-side writes require
`U ⊆ T`. Unlike the unchecked case (R4), source-side writes do matter: they happen after the
check. -/
theorem checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev
    (srcWrites dstWrites : Bool) (T U : Validity B n) :
    CheckedSound (sharedIMProtocol srcWrites dstWrites) T U ↔
      (Satisfiable (T.meet U) →
        (srcWrites = true → Includes T U) ∧ (dstWrites = true → Includes U T)) := by
  constructor
  · rintro h ⟨m, hT, hU⟩
    constructor
    · intro hs
      subst hs
      intro v hv
      exact (h m hT hU _ (sharedIMProtocol_writeSrcReadDst dstWrites v)
        (writeSrcReadDst_wellTyped hv)).1
    · intro hd
      subst hd
      intro u hu
      exact (h m hT hU _ (sharedIMProtocol_writeDstReadSrc srcWrites u)
        (writeDstReadSrc_wellTyped hu)).1
  · intro hc m hT hU
    obtain ⟨hs, hd⟩ := hc ⟨m, hT, hU⟩
    exact checkedSound_sharedIM_of_invariant (fun x => T x ∧ U x) (fun _ a b => ⟨a, b⟩)
      (fun _ h => h.1) (fun _ h => h.2) (fun e v hv => ⟨hv, hs e v hv⟩)
      (fun e v hv => ⟨hd e v hv, hv⟩) m hT hU

end Toy.Transmute
