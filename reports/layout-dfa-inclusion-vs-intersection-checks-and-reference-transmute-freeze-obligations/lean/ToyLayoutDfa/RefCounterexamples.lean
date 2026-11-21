import ToyLayoutDfa.RefExamples
import ToyLayoutDfa.Counterexamples2

/-!
# Reference obligation matrix: counterexamples, positive controls and non-vacuity witnesses

All fully proved. Conventions as in `ToyLayoutDfa.Counterexamples`.
-/

namespace Toy.LayoutDfa

open Layout

/-! ### The headline counterexample -/

/-- The obligation matrix without the source-side `Freeze` obligation admits
`& Cell<u8> → & u8`, which is unsound in the toy, although the two validities are equal in
both directions. The failing run is exposed: from contents `[0]`, writing `[1]` through
the source view is permitted (the source referent is not `Freeze`), but the `frozen`
assertion of the live `&u8` view is in force, so the run violates an assertion. The full
matrix rejects the cast, and accepts `& u8 → & u8`, which is sound. -/
theorem cellByte_to_byte_admitted_without_srcFreeze :
    MatrixOKNoSrcFreeze .shared .shared cellByteRef byteRef ∧
    Includes cellByteRef byteRef ∧ Includes byteRef cellByteRef ∧
    ¬ Sound .shared .shared cellByteRef byteRef ∧
    Permitted .shared .shared cellByteRef byteRef (.write .src [Sym.byte 1]) ∧
    FrozenDuring .shared .shared cellByteRef byteRef ∧
    ¬ RunOK .shared .shared cellByteRef byteRef [Sym.byte 0] [.write .src [Sym.byte 1]] ∧
    ¬ MatrixOK .shared .shared cellByteRef byteRef ∧
    MatrixOK .shared .shared byteRef byteRef ∧ Sound .shared .shared byteRef byteRef :=
  ⟨⟨cellByteRef_includes_byteRef, rfl⟩, cellByteRef_includes_byteRef,
    byteRef_includes_cellByteRef, not_sound_shared_shared_cell_byte,
    ⟨rfl, rfl, cellByteRef_valid 1⟩, Or.inr ⟨rfl, rfl⟩, fun h => h.1.1 (Or.inr ⟨rfl, rfl⟩),
    fun h => absurd h.2.2 (by decide), ⟨fun _ h => h, rfl, rfl⟩, sound_shared_shared_byte_byte⟩

/-! ### Cell characterizations: the satisfiability hypothesis -/

theorem sharedShared_sound_iff_needs_satisfiable :
    ¬ Satisfiable neverRef ∧
    ¬ (Sound .shared .shared neverRef cellByteRef ↔
      Includes neverRef cellByteRef ∧ neverRef.freeze = cellByteRef.freeze ∧
        (cellByteRef.freeze = false → Includes cellByteRef neverRef)) :=
  ⟨neverRef_not_satisfiable,
    fun h => absurd (h.mp (sound_of_neverRef _ _ _)).2.1 (by decide)⟩

theorem mutShared_sound_iff_needs_satisfiable :
    ¬ Satisfiable neverRef ∧
    ¬ (Sound .mutable .shared neverRef cellByteRef ↔
      Includes neverRef cellByteRef ∧
        (cellByteRef.freeze = false → Includes cellByteRef neverRef)) :=
  ⟨neverRef_not_satisfiable,
    fun h => not_includes_cellByteRef_neverRef ((h.mp (sound_of_neverRef _ _ _)).2 rfl)⟩

theorem mutMut_sound_iff_needs_satisfiable :
    ¬ Satisfiable neverRef ∧
    ¬ (Sound .mutable .mutable neverRef byteRef ↔ Includes neverRef byteRef ∧ Includes byteRef neverRef) :=
  ⟨neverRef_not_satisfiable,
    fun h => not_includes_byteRef_neverRef (h.mp (sound_of_neverRef _ _ _)).2⟩

/-- Dropping satisfiability, `& never → &mut u8` is vacuously sound. -/
theorem sharedMut_not_sound_needs_satisfiable :
    ¬ Satisfiable neverRef ∧ Sound .shared .mutable neverRef byteRef :=
  ⟨neverRef_not_satisfiable, sound_of_neverRef _ _ _⟩

/-- Positive control for `sharedMut_not_sound`: changing the source reference to `&mut`,
or the destination reference to `&`, gives a sound cast between the same referents. -/
theorem sharedMut_positive_control :
    Sound .mutable .mutable byteRef byteRef ∧ Sound .shared .shared byteRef byteRef :=
  ⟨sound_mut_mut_byte_byte, sound_shared_shared_byte_byte⟩

/-! ### The matrix characterization -/

theorem matrixOK_iff_sound_needs_satisfiable :
    ¬ Satisfiable neverRef ∧ (Mode.mutable = Mode.shared → byteRef.freeze = true) ∧
    ¬ (MatrixOK .shared .mutable neverRef byteRef ↔ Sound .shared .mutable neverRef byteRef) :=
  ⟨neverRef_not_satisfiable, fun h => absurd h (by decide),
    fun h => h.mpr (sound_of_neverRef _ _ _)⟩

/-- Dropping "a shared destination referent is `Freeze`": `& Cell<u8> → & Cell<u8>` and
`&mut Cell<u8> → & Cell<u8>` (destination not `Freeze`, equal validities) are sound in the
toy but rejected by the matrix. -/
theorem matrixOK_iff_sound_needs_sharedDst_freeze :
    Satisfiable cellByteRef ∧ ¬ (Mode.shared = Mode.shared → cellByteRef.freeze = true) ∧
    ¬ (MatrixOK .shared .shared cellByteRef cellByteRef ↔
      Sound .shared .shared cellByteRef cellByteRef) ∧
    ¬ (MatrixOK .mutable .shared cellByteRef cellByteRef ↔
      Sound .mutable .shared cellByteRef cellByteRef) :=
  ⟨cellByteRef_satisfiable, fun h => absurd (h rfl) (by decide),
    fun h => absurd (h.mpr sound_shared_shared_cell_cell).2.1 (by decide),
    fun h => absurd (h.mpr sound_mut_shared_cell_cell).2 (by decide)⟩

/-! ### `refCheck` -/

/-- Dropping the common size for the source: `& () → & {[uninit]}`, both `Freeze`. The
universal check accepts by extension, but reading the empty region through the
destination view is invalid. -/
theorem refCheck_sound_needs_fixedSize_src :
    uL.FixedSize 1 ∧ ¬ unitL.FixedSize 1 ∧ refCheck .shared .shared unitL true uL true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout unitL true) (RefTy.ofLayout uL true) := by
  refine ⟨uL_fixedSize, unitL_not_fixedSize_one, by decide, fun h => ?_⟩
  have := h [] (by decide) [.read .dst]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      trivial)
  exact absurd (show uL.Lang [] from this.1.1) (by decide)

/-- Dropping the common size for the destination: `& {[0]} → & ()`, both `Freeze`. The
universal check accepts by truncation, but the destination view's type does not accept
the source's byte string `[0]`. -/
theorem refCheck_sound_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ ¬ unitL.FixedSize 1 ∧ refCheck .shared .shared b0L true unitL true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout b0L true) (RefTy.ofLayout unitL true) := by
  refine ⟨b0L_fixedSize, unitL_not_fixedSize_one, by decide, fun h => ?_⟩
  have := h [Sym.byte 0] (by decide) [.read .dst]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      trivial)
  exact absurd (show unitL.Lang [Sym.byte 0] from this.1.1) (by decide)

/-- The same failure in the `&mut → &mut` cell: `&mut () → &mut {[uninit]}` passes both
inclusion checks (by extension and by truncation) but reading the empty region through the
destination view is invalid. -/
theorem refCheck_mutMut_needs_eq_fixedSize :
    unitL.FixedSize 0 ∧ uL.FixedSize 1 ∧
    refCheck .mutable .mutable unitL true uL true = true ∧
    ¬ Sound .mutable .mutable (RefTy.ofLayout unitL true) (RefTy.ofLayout uL true) := by
  refine ⟨unitL_fixedSize, uL_fixedSize, by decide, fun h => ?_⟩
  have := h [] (by decide) [.read .dst]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      trivial)
  exact absurd (show uL.Lang [] from this.1.1) (by decide)

theorem mu8L_fixedSize : mu8L.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide +kernel) rfl

theorem mu8L_deterministic : mu8L.Deterministic := by
  intro e₁ h₁ e₂ h₂ _ _
  simp only [mu8L, anyEdges, List.mem_map] at h₁ h₂
  obtain ⟨_, _, rfl⟩ := h₁
  obtain ⟨_, _, rfl⟩ := h₂
  rfl

/-- The source-size counterexamples persist for an initialisation-monotone destination:
`mu8L` (`MaybeUninit<u8>`, all 257 symbols) instead of the `uninit`-only `uL`. With the
source `()`, the universal and existential checks accept by extension although `[]` is
not a valid `mu8L` word, and `refCheck` accepts an unsound `& () → & MaybeUninit<u8>`. -/
theorem fixedSize_src_counterexamples_hold_for_mu8L :
    mu8L.FixedSize 1 ∧ mu8L.Deterministic ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
    ¬ (forallCheck unitL mu8L = true ↔ Subset unitL mu8L) ∧
    ¬ (existsCheck unitL mu8L = true ↔ Meets unitL mu8L) ∧
    refCheck .shared .shared unitL true mu8L true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout unitL true) (RefTy.ofLayout mu8L true) := by
  refine ⟨mu8L_fixedSize, mu8L_deterministic, unitL_live, unitL_not_fixedSize_one,
    fun h => absurd (h.mp (by decide +kernel) [] (by decide)) (by decide),
    fun h => ?_, by decide +kernel, fun h => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := h.mp (by decide +kernel)
    have h0 := unitL_fixedSize s hs
    have h1 := mu8L_fixedSize s hs'
    omega
  · have := h [] (by decide) [.read .dst]
      (by
        intro op hop
        simp only [List.mem_singleton] at hop
        subst hop
        trivial)
    exact absurd (show mu8L.Lang [] from this.1.1) (by decide)

/-! ### Non-vacuity witnesses -/

theorem sharedShared_sound_iff_nonvacuous :
    Satisfiable boolRef ∧ Sound .shared .shared boolRef byteRef ∧
    Satisfiable cellByteRef ∧ ¬ Sound .shared .shared cellByteRef byteRef ∧
    Sound .shared .shared cellByteRef cellByteRef :=
  ⟨boolRef_satisfiable, sound_shared_shared_bool_byte, cellByteRef_satisfiable,
    not_sound_shared_shared_cell_byte, sound_shared_shared_cell_cell⟩

theorem mutShared_sound_iff_nonvacuous :
    Satisfiable boolRef ∧ Sound .mutable .shared boolRef byteRef ∧
    Satisfiable byteRef ∧ ¬ Sound .mutable .shared byteRef boolRef ∧
    Sound .mutable .shared cellByteRef cellByteRef :=
  ⟨boolRef_satisfiable, sound_mut_shared_bool_byte, byteRef_satisfiable,
    not_sound_mut_shared_byte_bool, sound_mut_shared_cell_cell⟩

theorem mutMut_sound_iff_nonvacuous :
    Satisfiable byteRef ∧ Sound .mutable .mutable byteRef byteRef ∧
    Satisfiable boolRef ∧ ¬ Sound .mutable .mutable boolRef byteRef :=
  ⟨byteRef_satisfiable, sound_mut_mut_byte_byte, boolRef_satisfiable,
    not_sound_mut_mut_bool_byte⟩

theorem sharedMut_not_sound_nonvacuous :
    Satisfiable byteRef ∧ ¬ Sound .shared .mutable byteRef byteRef :=
  ⟨byteRef_satisfiable, not_sound_shared_mut_byte_byte⟩

theorem sound_of_matrixOK_nonvacuous :
    MatrixOK .shared .shared boolRef byteRef ∧ MatrixOK .mutable .shared boolRef byteRef ∧
    MatrixOK .mutable .mutable byteRef byteRef :=
  ⟨⟨boolRef_includes_byteRef, rfl, rfl⟩, ⟨boolRef_includes_byteRef, rfl⟩,
    ⟨fun _ h => h, fun _ h => h⟩⟩

/-- Both truth values occur under all hypotheses: `& bool → & u8` (accepted by the matrix,
sound) and `& Cell<u8> → & u8` (rejected, unsound). -/
theorem matrixOK_iff_sound_nonvacuous :
    (Satisfiable boolRef ∧ (Mode.shared = Mode.shared → byteRef.freeze = true) ∧
      MatrixOK .shared .shared boolRef byteRef ∧ Sound .shared .shared boolRef byteRef) ∧
    (Satisfiable cellByteRef ∧ (Mode.shared = Mode.shared → byteRef.freeze = true) ∧
      ¬ MatrixOK .shared .shared cellByteRef byteRef ∧
      ¬ Sound .shared .shared cellByteRef byteRef) :=
  ⟨⟨boolRef_satisfiable, fun _ => rfl, ⟨boolRef_includes_byteRef, rfl, rfl⟩,
      sound_shared_shared_bool_byte⟩,
    ⟨cellByteRef_satisfiable, fun _ => rfl, fun h => absurd h.2.2 (by decide),
      not_sound_shared_shared_cell_byte⟩⟩

theorem refCheck_sound_nonvacuous :
    boolL.FixedSize 1 ∧ u8L.FixedSize 1 ∧ refCheck .shared .shared boolL true u8L true = true ∧
    refCheck .mutable .shared boolL true u8L true = true ∧
    refCheck .mutable .mutable u8L true u8L true = true := by
  refine ⟨boolL_fixedSize, u8L_fixedSize, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

end Toy.LayoutDfa
