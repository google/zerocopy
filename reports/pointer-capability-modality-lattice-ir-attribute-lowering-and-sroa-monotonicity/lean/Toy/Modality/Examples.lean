/-
Toy.Modality.Examples
=====================

Definition examples (an intended instance each definition admits and one it
rejects), non-vacuity instances for the main results, and canonical-form
counterexamples for hypotheses ("the hypothesis fails, all other hypotheses
hold, and the conclusion fails").
-/
import Toy.Modality.SROA

namespace Toy.Modality

/-! ## Shapes and modalities -/

/-- `Shape`: the one-byte shape `s1` exists (positive); no shape has size `0`
(negative). -/
theorem ex_shape : s1.size = 1 ∧ s1.align = 1 ∧ s2.align = 2 ∧ ¬ ∃ s : Shape, s.size = 0 :=
  ⟨rfl, rfl, rfl, fun ⟨s, h⟩ => by have := s.size_pos; omega⟩

/-- `Mod` order: `refFull ≤ Mod.top` (positive); `¬ Mod.top ≤ refFull` (negative). -/
theorem ex_mod_le : refFull ≤ Mod.top ∧ ¬ Mod.top ≤ refFull := by decide

/-- `Mod.inf`/`Mod.sup`: the meet of `refFull` and `mutFull` is
`{aligned, nonnull, derefEntry, derefWhole, bounded}` and their join is
`Mod.top`; the meet is not `refFull`. -/
theorem ex_mod_inf_sup :
    Mod.inf refFull mutFull = ⟨true, true, true, true, false, false, true⟩ ∧
    Mod.sup refFull mutFull = Mod.top ∧ Mod.inf refFull mutFull ≠ refFull := by decide

/-- `Closed`: `refFull` is closed for `s1` (positive); `{derefEntry}` is not
(negative: closure adds `nonnull`, and `aligned` at alignment 1); `Mod.bot` is
closed for `s2` but not for `s1`. -/
theorem ex_closed :
    Closed s1 refFull ∧ ¬ Closed s1 ⟨false, false, true, false, false, false, false⟩ ∧
    Closed s2 Mod.bot ∧ ¬ Closed s1 Mod.bot := by decide

/-- `cl`: the closure of `{derefWhole}` for `s2` is
`{nonnull, derefEntry, derefWhole}`, and it is not `{derefWhole}`. -/
theorem ex_cl :
    cl s2 ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, true, true, false, false, false⟩ ∧
    cl s2 ⟨false, false, false, true, false, false, false⟩ ≠
      ⟨false, false, false, true, false, false, false⟩ := by
  decide

/-! ## Trace predicates -/

/-- `ArgInRange`: `tArgWrite s1` satisfies it (positive); a write through the
argument outside the pointee during the call does not (negative); accesses
after the return are not constrained (positive). -/
theorem ex_argInRange :
    ArgInRange s1 (tArgWrite s1) ∧ ¬ ArgInRange s1 ⟨1, [], [.write .arg 5], []⟩ ∧
    ArgInRange s1 ⟨1, [], [], [.write .arg 5]⟩ := by
  refine ⟨argInRange_tArgWrite s1, fun h => ?_, fun x hx => by simp [AccessedBy] at hx⟩
  have := h 5 (Or.inr (by simp))
  simp [InRange, s1] at this

/-- `Dereferenceable`: `tStar s1` (positive); `tDangling s1` (negative); an
allocation at base `0` covers nothing (negative). -/
theorem ex_dereferenceable :
    Dereferenceable s1 (tStar s1) ∧ ¬ Dereferenceable s1 (tDangling s1) ∧
    ¬ Dereferenceable s1 ⟨0, [⟨0, 0, 4⟩], [], []⟩ := by
  refine ⟨atomSat_tStar s1 .derefEntry, not_dereferenceable_of_live_nil s1 _ rfl, ?_⟩
  rintro ⟨al, hal, h1, _⟩
  simp at hal; subst hal; simp at h1

/-- `NotFreedDuring`: `tStar s1` (positive); `tFreed s1` (negative). -/
theorem ex_notFreedDuring : NotFreedDuring (tStar s1) ∧ ¬ NotFreedDuring (tFreed s1) :=
  ⟨(atomSat_tStar s1 .derefWhole).2, not_notFreedDuring_tFreed s1⟩

/-- `atomSat`: each atom holds on `tStar s2` (positive) and fails on a specific
witness (negative). -/
theorem ex_atomSat :
    (∀ a, atomSat s2 a (tStar s2)) ∧
    ¬ atomSat s2 .aligned (tMis s2) ∧ ¬ atomSat s2 .nonnull tNull ∧
    ¬ atomSat s2 .derefEntry (tDangling s2) ∧ ¬ atomSat s2 .derefWhole (tFreed s2) ∧
    ¬ atomSat s2 .frozen (tArgWrite s2) ∧ ¬ atomSat s2 .unique (tForeignRead s2) ∧
    ¬ atomSat s2 .bounded (tOutOfRange s2) :=
  ⟨atomSat_tStar s2, not_atomSat_tMis_aligned s2 (by decide), fun h => h rfl,
   not_dereferenceable_of_live_nil s2 _ rfl, fun h => not_notFreedDuring_tFreed s2 h.2,
   not_atomSat_tArgWrite_frozen s2, not_atomSat_tForeignRead_unique s2,
   not_atomSat_tOutOfRange_bounded s2⟩

/-- `den`: `tStar s1 ∈ ⟦Mod.top⟧` and `tOutOfRange s1 ∈ ⟦Mod.bot⟧` (positive);
`tFreed s1 ∉ ⟦refFull⟧` and `tOutOfRange s1 ∉ ⟦refFull⟧` (negative). -/
theorem ex_den :
    den s1 Mod.top (tStar s1) ∧ den s1 Mod.bot (tOutOfRange s1) ∧
    ¬ den s1 refFull (tFreed s1) ∧ ¬ den s1 refFull (tOutOfRange s1) :=
  ⟨den_tStar s1 _, den_bot s1 _, fun h => not_notFreedDuring_tFreed s1 (h .derefWhole rfl).2,
   fun h => not_atomSat_tOutOfRange_bounded s1 (h .bounded rfl)⟩

/-! ## Transformers and rules -/

/-- Transformers: values on `refFull` and `mutFull` (positive), each removes a
specific atom (negative), and dropping `derefWhole` keeps the atoms it implied
(`tRelax` and `tBox` of `{derefWhole}`). -/
theorem ex_transformers :
    tRelax refFull = ⟨true, true, false, false, false, false, false⟩ ∧
    tCell refFull = ⟨true, true, true, false, false, false, true⟩ ∧
    tPin mutFull = ⟨true, true, true, false, false, false, true⟩ ∧
    tBox mutFull = ⟨true, true, true, false, false, true, true⟩ ∧
    tRelax ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, false, false, false, false, false⟩ ∧
    tBox ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, true, false, false, false, false⟩ ∧
    tRelax refFull ≠ refFull ∧ tCell refFull ≠ refFull ∧ tPin mutFull ≠ mutFull ∧
    tBox mutFull ≠ mutFull := by decide

/-- `clDeref`: adds `derefEntry` and `nonnull` to `{derefWhole}` (positive);
leaves `{aligned}` unchanged (negative: it never adds `aligned`). -/
theorem ex_clDeref :
    clDeref ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, true, true, false, false, false⟩ ∧
    clDeref ⟨true, false, false, false, false, false, false⟩ =
      ⟨true, false, false, false, false, false, false⟩ := by decide

/-- `kindBase`: base modalities of each pointer kind (positive), distinct where
the pointee predicate differs (negative). -/
theorem ex_kindBase :
    kindBase (.shared true) = refFull ∧ kindBase (.mutRef true) = mutFull ∧
    kindBase (.box true) = ⟨true, true, true, false, false, true, true⟩ ∧
    kindBase .raw = Mod.bot ∧
    kindBase (.shared false) ≠ kindBase (.shared true) ∧
    kindBase (.box false) ≠ kindBase (.box true) := by decide

/-- Three pointer kinds get the same base modality
`{aligned, nonnull, derefEntry, bounded}`: shared references to non-`Freeze`
pointees, mutable references to non-`Unpin` pointees, and boxes of
non-`Unpin` pointees. -/
theorem kindBase_three_kinds_coincide :
    kindBase (.shared false) = ⟨true, true, true, false, false, false, true⟩ ∧
    kindBase (.mutRef false) = kindBase (.shared false) ∧
    kindBase (.box false) = kindBase (.shared false) := by decide

/-- `kindRule`: `tStar s1` is permitted for a `Freeze` shared reference
(positive); `tArgWrite s1` and `tOutOfRange s1` are not (negative); a
non-`Freeze` shared reference permits `tArgWrite s1`, and a raw pointer permits
`tOutOfRange s1`. -/
theorem ex_kindRule :
    kindRule s1 (.shared true) (tStar s1) ∧ ¬ kindRule s1 (.shared true) (tArgWrite s1) ∧
    ¬ kindRule s1 (.shared true) (tOutOfRange s1) ∧
    kindRule s1 (.shared false) (tArgWrite s1) ∧ kindRule s1 .raw (tOutOfRange s1) := by
  refine ⟨(kindRule_iff_den s1 _ _).2 (den_tStar s1 _), fun h => ?_, fun h => ?_,
    (transformer_dropped_atoms_can_fail s1).2.2.2.2.1.1, trivial⟩
  · exact not_atomSat_tArgWrite_frozen s1 h.2.2.2.2.1
  · exact not_atomSat_tOutOfRange_bounded s1 h.2.2.2.2.2

/-- `relaxRule`: `tDangling s1` is permitted inside a relaxing wrapper
(positive); `tNull` is not, for a base modality promising `nonnull`
(negative). -/
theorem ex_relaxRule : relaxRule s1 refFull (tDangling s1) ∧ ¬ relaxRule s1 refFull tNull :=
  ⟨(transformer_dropped_atoms_can_fail s1).1.1, fun h => h.2 rfl rfl⟩

/-! ## Types and the bottom-up computation -/

/-- `Wrap.relaxes`: `maybeDangling` and `manuallyDrop` relax; `unsafeCell` does
not. -/
theorem ex_wrap_relaxes :
    Wrap.maybeDangling.relaxes = true ∧ Wrap.manuallyDrop.relaxes = true ∧
    Wrap.unsafeCell.relaxes = false := ⟨rfl, rfl, rfl⟩

/-- `Ty.freeze` / `Ty.unpin`: a pair of scalars is both (positive); an
`UnsafeCell` is not `Freeze`, and an `UnsafePinned` is not `Unpin` (negative);
an `UnsafeCell` is still `Unpin`. -/
theorem ex_freeze_unpin :
    (Ty.pair .scalar .scalar).freeze = true ∧ (Ty.pair .scalar .scalar).unpin = true ∧
    (Ty.wrap .unsafeCell .scalar).freeze = false ∧
    (Ty.wrap .unsafePinned .scalar).unpin = false ∧
    (Ty.wrap .unsafeCell .scalar).unpin = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Smart constructors: `&UnsafeCell<T>` gets `tCell refFull`, `&mut` of an
`UnsafePinned` gets `tPin mutFull`, `Box` of an `UnsafePinned` gets
`tBox (tPin mutFull)`, a raw pointer gets `Mod.bot`, and `UnsafeCell<&T>` by
value keeps `refFull`. -/
theorem ex_pointer_constructors :
    refTy s1 (.wrap .unsafeCell .scalar) = .ptr s1 (tCell refFull) ∧
    mutRefTy s1 (.wrap .unsafePinned .scalar) = .ptr s1 (tPin mutFull) ∧
    boxTy s1 (.wrap .unsafePinned .scalar) = .ptr s1 (tBox (tPin mutFull)) ∧
    boxTy s1 .scalar = .ptr s1 (tBox mutFull) ∧
    rawTy s1 = .ptr s1 Mod.bot ∧
    modAt (.wrap .unsafeCell (refTy s1 .scalar)) [.inner] = some (s1, refFull) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `leafAt` / `relaxedOn`: the nested leaf of `tyNestedMD s1` exists and is
relaxed (positive); the path `[.inner]` is not a leaf, and a pair's components
are not relaxed (negative). -/
theorem ex_leafAt_relaxedOn :
    leafAt (tyNestedMD s1) pathNestedMD = some (s1, mutFull) ∧
    relaxedOn (tyNestedMD s1) pathNestedMD = true ∧
    leafAt (tyNestedMD s1) [.inner] = none ∧
    relaxedOn (.pair (refTy s1 .scalar) .scalar) [.fst] = false := ⟨rfl, rfl, rfl, rfl⟩

/-- `comp` / `req`: deep and shallow computations agree on a directly wrapped
pointer (positive) and differ on the nested one (negative). -/
theorem ex_comp_req :
    comp tRelax true (.wrap .maybeDangling (refTy s1 .scalar)) [.inner] =
      some (s1, tRelax refFull) ∧
    comp tRelax false (.wrap .maybeDangling (refTy s1 .scalar)) [.inner] =
      some (s1, tRelax refFull) ∧
    comp tRelax true (tyNestedMD s1) pathNestedMD ≠
      comp tRelax false (tyNestedMD s1) pathNestedMD ∧
    req (tyNestedMD s1) pathNestedMD = some (s1, tRelax mutFull) := by
  refine ⟨rfl, rfl, fun h => ?_, rfl⟩
  have h' : some (s1, tRelax mutFull) = some (s1, mutFull) := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h'
  exact absurd h' (by decide)

/-- `TransformerSound`: `tRelax` is sound (positive); the identity is not
(negative, witnessed by `tDangling s1` for `refFull`). -/
theorem ex_transformerSound : TransformerSound tRelax ∧ ¬ TransformerSound id := by
  refine ⟨fun _ _ _ h => h, fun h => ?_⟩
  have := h s1 refFull (tDangling s1) (den_tRelax_tDangling s1 _)
  exact not_dereferenceable_of_live_nil s1 _ rfl (this .derefEntry rfl)

/-- Closing for the two-aligned shape `s2` before relaxing gives the same
modality as relaxing directly, so this relaxer is sound. -/
theorem transformerSound_tRelax_comp_cl_s2 :
    (∀ m, tRelax (cl s2 m) = tRelax m) ∧ TransformerSound (fun m => tRelax (cl s2 m)) := by
  have h : ∀ m, tRelax (cl s2 m) = tRelax m := by
    intro m
    cases m with
    | mk a b c d e f g =>
      cases a <;> cases b <;> cases c <;> cases d <;> simp [tRelax, cl, clDeref, s2, Mod.bot]
  refine ⟨h, fun s m t ht => ?_⟩
  show den s (tRelax (cl s2 m)) t
  rw [h m]; exact ht

/-- `CompSound`: deep `tRelax` is sound (positive); shallow `tRelax` is not
(negative). -/
theorem ex_compSound : CompSound tRelax true ∧ ¬ CompSound tRelax false :=
  ⟨(compSound_iff_transformerSound_and_deep _ _).2 ⟨ex_transformerSound.1, rfl⟩,
   fun h => by simpa using ((compSound_iff_transformerSound_and_deep _ _).1 h).2⟩

/-- Soundness is not precision: the transformer that forgets every atom is
sound, its deep computation is sound, and it differs from `tRelax` on
`refFull`. -/
theorem compSound_const_bot :
    TransformerSound (fun _ => Mod.bot) ∧ CompSound (fun _ => Mod.bot) true ∧
    (fun _ => Mod.bot) refFull ≠ tRelax refFull := by
  have hT : TransformerSound (fun _ => Mod.bot) := fun s _ t _ => den_bot s t
  exact ⟨hT, (compSound_iff_transformerSound_and_deep _ _).2 ⟨hT, rfl⟩, by decide⟩

/-- `DocTy`: `refTy s1 .scalar` and `MaybeDangling<(&mut T, u8)>` are built by
documented constructors (positive); a pointer leaf with modality
`modFrozenOnly` is not (negative). -/
theorem ex_docTy :
    DocTy (refTy s1 .scalar) ∧ DocTy (tyNestedMD s1) ∧ ¬ DocTy (.ptr s1 modFrozenOnly) := by
  refine ⟨.ref s1 .scalar, .wrap _ (.pair (.wrap _ (.mutRef s1 .scalar)) .scalar), fun h => ?_⟩
  obtain ⟨k, hk⟩ := h.leaf_kindBase [] s1 modFrozenOnly rfl
  cases k with
  | shared f => cases f <;> exact absurd hk (by decide)
  | mutRef u => cases u <;> exact absurd hk (by decide)
  | box u => cases u <;> exact absurd hk (by decide)
  | raw => exact absurd hk (by decide)

/-! ## Attributes and lowering -/

/-- `attrSat`: `tStar s1` satisfies every attribute at argument position and
`noalias` at return position (positive); specific traces violate each
argument attribute; `tFreed s1` satisfies `dereferenceable` at argument
position but not at return position; `nofree` and `readonly` are never
satisfied at return position (negative). -/
theorem ex_attrSat :
    (∀ a, attrSat s1 .arg a (tStar s1)) ∧ attrSat s1 .ret .noalias (tStar s1) ∧
    ¬ attrSat s1 .arg .nonnull tNull ∧ ¬ attrSat s1 .arg .dereferenceable (tDangling s1) ∧
    ¬ attrSat s1 .arg .dereferenceableOrNull (tDangling s1) ∧
    ¬ attrSat s1 .arg .noalias (tConflict s1) ∧ ¬ attrSat s1 .arg .nofree (tFreed s1) ∧
    ¬ attrSat s1 .arg .readonly (tArgWrite s1) ∧ ¬ attrSat s2 .arg .align (tMis s2) ∧
    attrSat s1 .arg .dereferenceable (tFreed s1) ∧ ¬ attrSat s1 .ret .dereferenceable (tFreed s1) ∧
    ¬ attrSat s1 .ret .nofree (tStar s1) ∧ ¬ attrSat s1 .ret .readonly (tStar s1) := by
  have hnd := not_dereferenceable_of_live_nil s1 (tDangling s1) rfl
  refine ⟨fun a => ?_, ?_, fun h => h rfl, hnd, ?_, not_noalias_tConflict s1,
    not_nofree_tFreed s1, fun h => h s1.align (by simp [tArgWrite]),
    not_atomSat_tMis_aligned s2 (by decide), atomSat_tFreed s1 .derefEntry (by decide),
    fun h => not_notFreedDuring_tFreed s1 h.2, fun h => h, fun h => h⟩
  · exact lower_sound s1 .arg Mod.top (tStar s1) (den_tStar s1 _) a (by cases a <;> rfl)
  · intro x _ h; simp [tStar, AccessedBy] at h
  · rintro (h | h)
    · simp [tDangling, s1, Shape.align] at h
    · exact hnd h

/-- `gammaSet`: `tStar s1` satisfies the full argument lowering of `refFull`
(positive); `tFreed s1` violates it (negative). -/
theorem ex_gammaSet :
    gammaSet s1 .arg (lower s1 .arg refFull) (tStar s1) ∧
    ¬ gammaSet s1 .arg (lower s1 .arg refFull) (tFreed s1) :=
  ⟨lower_sound s1 .arg refFull _ (den_tStar s1 _),
   fun h => not_nofree_tFreed s1 (h .nofree rfl)⟩

/-- `lower`: the lowerings of the documented base modalities at both positions
(`u16`-like shape `s2`), of `refFull` without `bounded`, and the dependence on
the shape at alignment 1.  All modalities here are call-entry modalities; the
`.ret` entries are the return-point attributes to which a pointer carrying
that call-entry modality is entitled when it is returned (for example
`tCell refFull` loses `dereferenceable` because its pointee may be freed during
the call), not lowerings of a returned value's validity invariant. -/
theorem ex_lower :
    lower s2 .arg refFull = ⟨true, true, true, true, true, true, true⟩ ∧
    lower s2 .arg (tCell refFull) = ⟨true, true, true, true, false, false, false⟩ ∧
    lower s2 .arg mutFull = ⟨true, true, true, true, true, true, false⟩ ∧
    lower s2 .arg (tBox mutFull) = ⟨true, true, true, true, true, false, false⟩ ∧
    lower s2 .arg (tRelax refFull) = ⟨true, true, false, false, false, false, false⟩ ∧
    lower s2 .arg Mod.bot = ⟨false, false, false, false, false, false, false⟩ ∧
    lower s2 .arg refFullNoBounded = ⟨true, true, true, true, false, true, false⟩ ∧
    lower s2 .ret refFull = ⟨true, true, true, true, false, false, false⟩ ∧
    lower s2 .ret (tCell refFull) = ⟨true, true, false, false, false, false, false⟩ ∧
    lower s1 .arg Mod.bot ≠ lower s2 .arg Mod.bot := by decide

/-- `AttrDual`, `alphaSet`, `gammaDual`, `denP`: the reverse-inclusion order
puts the larger set `lower s1 .arg refFull` below `lower s1 .arg Mod.bot`
(positive) and not conversely (negative); `gammaDual` of the argument lowering
of `refFull` contains `tStar s1` and not `tFreed s1`; `denP s1 refFull`
contains `tStar s1` and not `tFreed s1`; `alphaSet` of `denP s1 refFull` is the
argument lowering of `refFull`. -/
theorem ex_galois_defs :
    (⟨lower s1 .arg refFull⟩ : AttrDual) ≤ ⟨lower s1 .arg Mod.bot⟩ ∧
    ¬ (⟨lower s1 .arg Mod.bot⟩ : AttrDual) ≤ ⟨lower s1 .arg refFull⟩ ∧
    gammaDual s1 .arg ⟨lower s1 .arg refFull⟩ (tStar s1) ∧
    ¬ gammaDual s1 .arg ⟨lower s1 .arg refFull⟩ (tFreed s1) ∧
    denP s1 refFull (tStar s1) ∧ ¬ denP s1 refFull (tFreed s1) ∧
    (alphaSet s1 .arg (denP s1 refFull)).val = lower s1 .arg refFull := by
  refine ⟨fun a h => ?_, fun h => ?_, ex_gammaSet.1, ex_gammaSet.2, den_tStar s1 _,
    fun h => not_notFreedDuring_tFreed s1 (h .derefWhole rfl).2,
    ((alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den s1 .arg).2 refFull).symm⟩
  · cases a <;> simp [lower, cl, Mod.bot, AttrSet.has, s1, Pos.isArg] at h ⊢
  · have := h .nofree rfl
    simp [lower, cl, Mod.bot, AttrSet.has, Pos.isArg] at this

/-! ## Niche lifting -/

/-- `NoArgEvents`: `tNull` (positive); `tArgWrite s1` (negative). -/
theorem ex_noArgEvents : NoArgEvents tNull ∧ ¬ NoArgEvents (tArgWrite s1) := by
  refine ⟨fun x => by simp [tNull], fun h => (h s1.align).2.1 (by simp [tArgWrite])⟩

/-- `IsNiche`: `1` is a niche of `refFull` and of `tRelax refFull` at the
two-aligned shape `s2` (positive); `1` is not a niche of `Mod.bot` at `s1`, and
`2` is not a niche of `tRelax refFull` at `s2`, witnessed by `tDangling s2`
(negative). -/
theorem ex_isNiche :
    IsNiche s2 refFull 1 ∧ IsNiche s2 (tRelax refFull) 1 ∧ ¬ IsNiche s1 Mod.bot 1 ∧
    ¬ IsNiche s2 (tRelax refFull) 2 := by
  refine ⟨liftOpt_unsound_at_niche_one.1, ?_, liftOpt_sound_at_non_niche_one.1,
    fun h => h (tDangling s2) (den_tRelax_tDangling s2 refFull) rfl⟩
  intro t ht haddr
  have ha : t.addr % s2.align = 0 := ht .aligned rfl
  rw [haddr] at ha
  exact absurd ha (by decide)

/-- `denOpt`: the null `None` and `tStar s1` are traces of the null-niche
option (positive); the null address with an access through the argument is
not (negative). -/
theorem ex_denOpt :
    denOpt s1 0 refFull tNull ∧ denOpt s1 0 refFull (tStar s1) ∧
    ¬ denOpt s1 0 refFull ⟨0, [], [.read .arg 0], []⟩ := by
  refine ⟨(lift_nonnull_dereferenceable_unsound_at_null s1 refFull).1, Or.inr (den_tStar s1 _),
    ?_⟩
  rintro (⟨_, h⟩ | h)
  · exact (h 0).1 (by simp)
  · exact (h .nonnull rfl) rfl

/-- `liftOpt`: for `refFull` the lifted set drops `nonnull` and
`dereferenceable` and keeps the rest (positive); for `Mod.bot` at `s2` it is
empty (negative). -/
theorem ex_liftOpt :
    liftOpt s2 refFull = ⟨true, false, false, true, true, true, true⟩ ∧
    liftOpt s2 refFull ≠ lower s2 .arg refFull ∧
    liftOpt s2 Mod.bot = ⟨false, false, false, false, false, false, false⟩ := by decide

/-! ## SROA -/

/-- `fieldTy` / `posTrans`: in `tyMDPair s1` the field `[.inner, .fst]` has
declared type `mutRefTy s1 .scalar` and position transformer `tRelax`
(positive); `[.fst]` is not a field (negative). -/
theorem ex_fieldTy_posTrans :
    fieldTy (tyMDPair s1) [.inner, .fst] = some (mutRefTy s1 .scalar) ∧
    posTrans (tyMDPair s1) [.inner, .fst] mutFull = tRelax mutFull ∧
    fieldTy (tyMDPair s1) [.fst] = none ∧
    posTrans (.pair (mutRefTy s1 .scalar) .scalar) [.fst] mutFull = mutFull := ⟨rfl, rfl, rfl, rfl⟩

/-- `(&mut T, u8)`, a pair with no relaxing wrapper. -/
def tyPlainPair (s : Shape) : Ty := .pair (mutRefTy s .scalar) .scalar

/-- `Refines`: scalarizing `(&mut T, u8)` is a refinement (positive);
scalarizing `ManuallyDrop<(&mut T, u8)>` through the wrapper is not
(negative). -/
theorem ex_refines :
    Refines (tyPlainPair s1) (scalarize (tyPlainPair s1) [[.fst], [.snd]]) ∧
    ¬ Refines (tyMDPair s1) (scalarize (tyMDPair s1) qsMDPair) :=
  ⟨refines_scalarize_of_not_relaxedOn _ _ (by decide),
   (sroa_hoist_out_of_manuallyDrop_counterexample s1).2.2.2.2.2.1⟩

/-- `SrcSafe` / `TgtSafe`: the program asserting nothing is safe on both sides
(positive); `progDangling s1` is source-safe but not target-safe for the
headline scalarization (negative). -/
theorem ex_safe :
    SrcSafe (tyMDPair s1) ⟨fun _ => false, fun _ => tNull⟩ ∧
    TgtSafe (scalarize (tyMDPair s1) qsMDPair) ⟨fun _ => false, fun _ => tNull⟩ ∧
    SrcSafe (tyMDPair s1) (progDangling s1) ∧
    ¬ TgtSafe (scalarize (tyMDPair s1) qsMDPair) (progDangling s1) := by
  refine ⟨fun _ _ _ _ h => by simp at h, fun _ _ _ _ _ _ _ h => by simp at h,
    (sroa_hoist_out_of_manuallyDrop_counterexample s1).2.2.2.1,
    (sroa_hoist_out_of_manuallyDrop_counterexample s1).2.2.2.2.1⟩

/-- `containsRelaxer` / `relaxAll` / `retype`: positive and negative instances. -/
theorem ex_repair_helpers :
    containsRelaxer (tyMDPair s1) = true ∧ containsRelaxer (tyPlainPair s1) = false ∧
    relaxAll (mutRefTy s1 .scalar) = .ptr s1 (tRelax mutFull) ∧
    retype (tyMDPair s1) [.inner, .fst] (mutRefTy s1 .scalar) = .ptr s1 (tRelax mutFull) ∧
    retype (tyPlainPair s1) [.fst] (mutRefTy s1 .scalar) = mutRefTy s1 .scalar :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `PolicySound` / `PolicyExact`: the retyping policy is sound and exact
(positive); the unrepaired policy is not sound, and the policy returning no
locals is sound but not exact (negative). -/
theorem ex_policy :
    PolicySound repairRetype ∧ PolicyExact repairRetype ∧ ¬ PolicySound naivePolicy ∧
    PolicySound (fun _ _ => some []) ∧ ¬ PolicyExact (fun _ _ => some []) :=
  ⟨repairs_sound.2.1, repairs_exact_and_retype_total.2.1, repairs_sound.2.2.2,
   policySound_degenerate.2.1, policySound_degenerate.2.2⟩

/-! ## Non-vacuity instances -/

/-- Non-vacuity of `den_antitone`: `refFull ≤ Mod.top` and `tStar s1 ∈ ⟦Mod.top⟧`. -/
theorem nv_den_antitone : refFull ≤ Mod.top ∧ den s1 Mod.top (tStar s1) :=
  ⟨by decide, den_tStar s1 _⟩

/-- `{derefWhole}`, a modality that is not closed for any shape. -/
def modDerefWholeOnly : Mod := ⟨false, false, false, true, false, false, false⟩

/-- Instance of `den_cl_iff` at a non-closed modality: `{derefWhole}` is not
closed for `s1`, `tStar s1` is in both `⟦{derefWhole}⟧` and its closure's
semantics, and `tNull` is in neither. -/
theorem nv_den_cl :
    ¬ Closed s1 modDerefWholeOnly ∧
    den s1 modDerefWholeOnly (tStar s1) ∧ den s1 (cl s1 modDerefWholeOnly) (tStar s1) ∧
    ¬ den s1 modDerefWholeOnly tNull ∧ ¬ den s1 (cl s1 modDerefWholeOnly) tNull := by
  refine ⟨by decide, den_tStar s1 _, den_tStar s1 _, fun h => ?_, fun h => h .nonnull rfl rfl⟩
  exact not_dereferenceable_of_live_nil s1 _ rfl (h .derefWhole rfl).1

/-- Non-vacuity of the order-embedding results: `refFull` is closed for `s1`,
and both sides of the equivalence hold for `m₂ = tRelax refFull`. -/
theorem nv_den_subset :
    Closed s1 refFull ∧ (∀ t, den s1 refFull t → den s1 (tRelax refFull) t) ∧
    tRelax refFull ≤ refFull :=
  ⟨by decide, (den_subset_iff_le_of_closed s1 (by decide) _).2 (by decide), by decide⟩

/-- Non-vacuity of `kindBase_best` and `tRelax_best`: their right-hand sides hold
at `m' = kindBase k`, resp. `m' = tRelax m`, and every rule permits `tStar s1`. -/
theorem nv_transformers_best :
    (∀ k, ∀ t, kindRule s1 k t → den s1 (kindBase k) t) ∧
    (∀ m, ∀ t, relaxRule s1 m t → den s1 (tRelax m) t) ∧
    (∀ k, kindRule s1 k (tStar s1)) :=
  ⟨fun k => (kindBase_best s1 k _).2 ((cl_closure_operator_and_closed_sublattice s1).1 _),
   fun m => (tRelax_best s1 m _).2 ((cl_closure_operator_and_closed_sublattice s1).1 _),
   fun k => (kindRule_iff_den s1 k _).2 (den_tStar s1 _)⟩

/-- Non-vacuity of `transformers_respect_den`: the distinct modalities
`{derefWhole}` and its closure for `s2` have the same semantics. -/
theorem nv_transformers_respect :
    modDerefWholeOnly ≠ cl s2 modDerefWholeOnly ∧
    (∀ t, den s2 modDerefWholeOnly t ↔ den s2 (cl s2 modDerefWholeOnly) t) :=
  ⟨by decide, fun t => (den_cl_iff s2 _ t).symm⟩

/-- Non-vacuity of `compSound_iff_transformerSound_and_deep`: both sides hold for
`tRelax` with `deep = true`. -/
theorem nv_compSound : CompSound tRelax true ∧ TransformerSound tRelax ∧ true = true :=
  ⟨ex_compSound.1, ex_transformerSound.1, rfl⟩

/-- Non-vacuity of `lower_sound`, `lower_best_iff`, `lower_unique`: `tStar s1 ∈
⟦refFull⟧`, and `A = lower s1 .arg refFull` satisfies both hypotheses of
`lower_unique`. -/
theorem nv_lower :
    den s1 refFull (tStar s1) ∧
    (∀ t, den s1 refFull t → gammaSet s1 .arg (lower s1 .arg refFull) t) ∧
    (∀ B : AttrSet, (∀ t, den s1 refFull t → gammaSet s1 .arg B t) → B ≤ lower s1 .arg refFull) :=
  ⟨den_tStar s1 _, lower_sound s1 .arg refFull, fun B hB => (lower_best_iff s1 .arg refFull B).1 hB⟩

/-- Non-vacuity of the niche results: the null `None` trace is a trace of
`denOpt s1 0 refFull`, and `1` is a niche of `refFull` at `s2`. -/
theorem nv_niche : denOpt s1 0 refFull tNull ∧ IsNiche s2 refFull 1 :=
  ⟨(lift_nonnull_dereferenceable_unsound_at_null s1 refFull).1, liftOpt_unsound_at_niche_one.1⟩

/-- Non-vacuity of the niche characterization at `v = 0`: `0` is a niche of
`refFull` at the one-byte shape `s1` (and at `s2`), the case in which both sides
of `liftOpt_sound_iff_noneVal_eq_zero_of_isNiche` hold. -/
theorem nv_niche_zero : IsNiche s1 refFull 0 ∧ IsNiche s2 refFull 0 :=
  ⟨fun _ ht h0 => ht .nonnull rfl h0, fun _ ht h0 => ht .nonnull rfl h0⟩

/-- Non-vacuity of the SROA characterization: for `(&mut T, u8)` both sides hold. -/
theorem nv_sroa :
    Refines (tyPlainPair s1) (scalarize (tyPlainPair s1) [[.fst], [.snd]]) ∧
    (∀ q ∈ ([[.fst], [.snd]] : List Path), ∀ σ, fieldTy (tyPlainPair s1) q = some σ →
      ∀ p' s m, modAt σ p' = some (s, m) → m ≤ posTrans (tyPlainPair s1) q m) :=
  ⟨ex_refines.1, (scalarize_refines_iff_declared_le_posMod _ _).1 ex_refines.1⟩

/-- Non-vacuity of the repair results: all three repair policies return a
scalarization of `(&mut T, u8)`, and the retyping policy returns one for the
headline type `ManuallyDrop<(&mut T, u8)>`. -/
theorem nv_repairs :
    (repairExclude (tyPlainPair s1) [[.fst], [.snd]]).isSome = true ∧
    (repairStopAtRelaxer (tyPlainPair s1) [[.fst], [.snd]]).isSome = true ∧
    (repairRetype (tyPlainPair s1) [[.fst], [.snd]]).isSome = true ∧
    (repairRetype (tyMDPair s1) qsMDPair).isSome = true := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Canonical-form counterexamples for hypotheses -/

/-- `den_antitone` needs `h : m₁ ≤ m₂`: with `m₁ = Mod.top`, `m₂ = Mod.bot`,
the order fails, the trace `tNull` is in `⟦m₂⟧` (other hypothesis), and it is
not in `⟦m₁⟧`. -/
theorem cex_den_antitone_le :
    ¬ Mod.top ≤ Mod.bot ∧ den s1 Mod.bot tNull ∧ ¬ den s1 Mod.top tNull :=
  ⟨by decide, den_bot s1 _, fun h => (h .nonnull rfl) rfl⟩

/-- `den_antitone` needs `ht : den s m₂ t`: with `m₁ = refFull`, `m₂ = Mod.top`
(other hypothesis `m₁ ≤ m₂` holds), the trace `tNull` is not in `⟦m₂⟧`, and it is
not in `⟦m₁⟧`. -/
theorem cex_den_antitone_ht :
    refFull ≤ Mod.top ∧ ¬ den s1 Mod.top tNull ∧ ¬ den s1 refFull tNull :=
  ⟨by decide, fun h => h .nonnull rfl rfl, fun h => h .nonnull rfl rfl⟩

/-- `den_subset_iff_le_of_closed` needs `Closed s m₁`: for `s1`,
`m₁ = {derefEntry}` (not closed) and `m₂ = {nonnull}`, the equivalence fails. -/
theorem cex_den_subset_closed :
    ¬ Closed s1 ⟨false, false, true, false, false, false, false⟩ ∧
    ¬ ((∀ t, den s1 ⟨false, false, true, false, false, false, false⟩ t →
          den s1 ⟨false, true, false, false, false, false, false⟩ t) ↔
        (⟨false, true, false, false, false, false, false⟩ : Mod) ≤
          ⟨false, false, true, false, false, false, false⟩) := by
  refine ⟨by decide, fun h => ?_⟩
  have hsub := (den_subset_iff_le_cl s1 ⟨false, false, true, false, false, false, false⟩
    ⟨false, true, false, false, false, false, false⟩).2 (by decide)
  exact absurd (h.1 hsub) (by decide)

/-- `transformers_respect_den` needs `h : ⟦m₁⟧ = ⟦m₂⟧`: for `s1`,
`m₁ = Mod.bot` and `m₂ = refFull` have different semantics (`tNull`), and
`⟦tRelax m₁⟧ ≠ ⟦tRelax m₂⟧` (`tNull`). -/
theorem cex_transformers_respect_h :
    ¬ (∀ t, den s1 Mod.bot t ↔ den s1 refFull t) ∧
    ¬ (∀ t, den s1 (tRelax Mod.bot) t ↔ den s1 (tRelax refFull) t) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ((h tNull).1 (den_bot s1 _)) .nonnull rfl rfl
  · have h1 : den s1 (tRelax Mod.bot) tNull := fun a ha => by
      cases a <;> simp [tRelax, clDeref, Mod.bot, Mod.has] at ha
    exact ((h tNull).1 h1) .nonnull rfl rfl

/-- `lower_sound` needs `ht : den s m t`: for `s1` and `m = refFull`, the trace
`tFreed s1` is not in `⟦refFull⟧` and violates `lower s1 .arg refFull`. -/
theorem cex_lower_sound_ht :
    ¬ den s1 refFull (tFreed s1) ∧ ¬ gammaSet s1 .arg (lower s1 .arg refFull) (tFreed s1) :=
  ⟨ex_den.2.2.1, ex_gammaSet.2⟩

/-- `lower_unique` needs soundness `hs`: for `s1` and `m = tCell refFull`, the
set `A` of all seven attributes is not sound (`hs` fails), every attribute set
is `≤ A` (`hb` holds), and `A ≠ lower s1 .arg (tCell refFull)`. -/
theorem cex_lower_unique_sound :
    ¬ (∀ t, den s1 (tCell refFull) t →
        gammaSet s1 .arg ⟨true, true, true, true, true, true, true⟩ t) ∧
    (∀ B : AttrSet, (∀ t, den s1 (tCell refFull) t → gammaSet s1 .arg B t) →
      B ≤ ⟨true, true, true, true, true, true, true⟩) ∧
    (⟨true, true, true, true, true, true, true⟩ : AttrSet) ≠ lower s1 .arg (tCell refFull) := by
  refine ⟨fun h => ?_, fun B _ a _ => by cases a <;> rfl, by decide⟩
  exact not_nofree_tFreed s1 (h (tFreed s1) (den_tFreed_of s1 _ rfl) .nofree rfl)

/-- `lower_unique` needs maximality `hb`: for `s1` and `m = refFull`, the empty
attribute set is sound (`hs` holds), the sound set `lower s1 .arg refFull` is
not `≤` it (`hb` fails), and it is not `lower s1 .arg refFull`. -/
theorem cex_lower_unique_best :
    (∀ t, den s1 refFull t →
      gammaSet s1 .arg ⟨false, false, false, false, false, false, false⟩ t) ∧
    ¬ (∀ B : AttrSet, (∀ t, den s1 refFull t → gammaSet s1 .arg B t) →
      B ≤ ⟨false, false, false, false, false, false, false⟩) ∧
    (⟨false, false, false, false, false, false, false⟩ : AttrSet) ≠ lower s1 .arg refFull := by
  refine ⟨fun _ _ a h => by cases a <;> simp [AttrSet.has] at h, fun h => ?_, by decide⟩
  have := h _ (lower_sound s1 .arg refFull) .align rfl
  simp [AttrSet.has] at this

/-- The transformer-soundness condition of
`compSound_iff_transformerSound_and_deep` is needed: with `deep = true` (the
other condition), the identity transformer is not sound and the computation is
not sound. -/
theorem cex_comp_transformer :
    ¬ TransformerSound id ∧ ¬ CompSound id true := by
  refine ⟨ex_transformerSound.2, fun h => ?_⟩
  exact ex_transformerSound.2 ((compSound_iff_transformerSound_and_deep _ _).1 h).1

/-- The deep-propagation condition of `compSound_iff_transformerSound_and_deep`
is needed: the sound transformer `tRelax` (other condition) with `deep = false`
gives an unsound computation. -/
theorem cex_comp_deep : TransformerSound tRelax ∧ ¬ CompSound tRelax false :=
  ⟨ex_transformerSound.1, ex_compSound.2⟩

/-- `liftOpt_sound_iff_noneVal_eq_zero_of_isNiche` needs `hv : IsNiche s m v`:
for `s1`, `Mod.bot` and `v = 1`, `1` is not a niche and the equivalence fails. -/
theorem cex_liftOpt_iff_isNiche :
    ¬ IsNiche s1 Mod.bot 1 ∧
    ¬ ((∀ t, denOpt s1 1 Mod.bot t → gammaSet s1 .arg (liftOpt s1 Mod.bot) t) ↔ (1 : Nat) = 0) := by
  obtain ⟨h0, h1, h2⟩ := liftOpt_sound_at_non_niche_one
  exact ⟨h0, fun h => h2 (h.1 h1)⟩

/-- `liftOpt_sound_of_noneVal_zero` needs `ht : denOpt s 0 m t`: for `s2` and
`refFull`, the trace `tAt 1` is not in `denOpt s2 0 refFull` (it is the `None`
trace of `denOpt s2 1 refFull`) and violates `liftOpt s2 refFull`. -/
theorem cex_liftOpt_noneVal :
    ¬ denOpt s2 0 refFull (tAt 1) ∧ denOpt s2 1 refFull (tAt 1) ∧
    ¬ gammaSet s2 .arg (liftOpt s2 refFull) (tAt 1) := by
  obtain ⟨-, hd, -, hden, hn, -⟩ := liftOpt_unsound_at_niche_one
  refine ⟨?_, hden, fun h => hn (h .dereferenceableOrNull hd)⟩
  rintro (⟨h0, _⟩ | h)
  · simp [tAt] at h0
  · exact not_dereferenceable_of_live_nil s2 _ rfl (h .derefEntry rfl)

end Toy.Modality
