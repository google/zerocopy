import ToyLayoutDfa.Counterexamples

/-!
# Reference model: definition examples, counterexamples and non-vacuity witnesses

All fully proved. Conventions as in `ToyLayoutDfa.Counterexamples`.
-/

namespace Toy.LayoutDfa

open Layout

/-! ### Basic facts about the fixtures -/

theorem boolRef_includes_byteRef : Includes boolRef byteRef :=
  forall_lang_of_wordsFrom (P := fun s => u8L.Lang s) boolL_fixedSize (by decide +kernel)

theorem byteRef_includes_cellByteRef : Includes byteRef cellByteRef := fun _ h => h
theorem cellByteRef_includes_byteRef : Includes cellByteRef byteRef := fun _ h => h

theorem byteRef_satisfiable : Satisfiable byteRef := ⟨_, byteRef_valid 0⟩
theorem cellByteRef_satisfiable : Satisfiable cellByteRef := ⟨_, cellByteRef_valid 0⟩
theorem boolRef_satisfiable : Satisfiable boolRef := ⟨[Sym.byte 0], by decide⟩

theorem not_includes_byteRef_boolRef : ¬ Includes byteRef boolRef :=
  fun h => absurd (h _ (byteRef_valid 2)) (by decide)

theorem not_includes_cellByteRef_neverRef : ¬ Includes cellByteRef neverRef :=
  fun h => h _ (cellByteRef_valid 0)

theorem not_includes_byteRef_neverRef : ¬ Includes byteRef neverRef :=
  fun h => h _ (byteRef_valid 0)

/-! ### Soundness proofs for fixture casts (via `sound_of_invariant`) -/

/-- `& bool → & u8`, both `Freeze`: sound. -/
theorem sound_shared_shared_bool_byte : Sound .shared .shared boolRef byteRef := by
  refine sound_of_invariant boolRef.valid (fun _ h => h) ?_ (fun _ h => h)
  intro m op hm hp
  cases op with
  | read v =>
    cases v
    · exact ⟨⟨hm, by decide⟩, hm⟩
    · exact ⟨⟨boolRef_includes_byteRef m hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.2.1 (by decide)
    · exact absurd hp.1 (by decide)

/-- `& u8 → & u8`, both `Freeze`: sound. -/
theorem sound_shared_shared_byte_byte : Sound .shared .shared byteRef byteRef := by
  refine sound_of_invariant byteRef.valid (fun _ h => h) ?_ (fun _ h => h)
  intro m op hm hp
  cases op with
  | read v => cases v <;> exact ⟨⟨hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.2.1 (by decide)
    · exact absurd hp.1 (by decide)

/-- `& Cell<u8> → & Cell<u8>` (neither `Freeze`, equal validity): sound in the toy. -/
theorem sound_shared_shared_cell_cell : Sound .shared .shared cellByteRef cellByteRef := by
  refine sound_of_invariant cellByteRef.valid (fun _ h => h) ?_ (fun _ h => h)
  intro m op hm hp
  have hfr : ¬ FrozenDuring .shared .shared cellByteRef cellByteRef := by
    simp [FrozenDuring, cellByteRef, RefTy.ofLayout]
  cases op with
  | read v => cases v <;> exact ⟨⟨hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact ⟨⟨hfr, by decide⟩, hp.2.2⟩
    · exact ⟨⟨hfr, by decide⟩, hp.2⟩

/-- `&mut bool → & u8` (`u8` is `Freeze`): sound. -/
theorem sound_mut_shared_bool_byte : Sound .mutable .shared boolRef byteRef := by
  refine sound_of_invariant boolRef.valid (fun _ h => h) ?_ (fun _ h => h)
  intro m op hm hp
  cases op with
  | read v =>
    cases v
    · exact absurd (show Mode.mutable = Mode.shared from hp) (by decide)
    · exact ⟨⟨boolRef_includes_byteRef m hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.1 (by decide)
    · exact absurd hp.1 (by decide)

/-- `&mut Cell<u8> → & Cell<u8>` (destination not `Freeze`, equal validity): sound in the
toy. -/
theorem sound_mut_shared_cell_cell : Sound .mutable .shared cellByteRef cellByteRef := by
  refine sound_of_invariant cellByteRef.valid (fun _ h => h) ?_ (fun _ h => h)
  intro m op hm hp
  have hfr : ¬ FrozenDuring .mutable .shared cellByteRef cellByteRef := by
    simp [FrozenDuring, cellByteRef, RefTy.ofLayout]
  cases op with
  | read v =>
    cases v
    · exact absurd (show Mode.mutable = Mode.shared from hp) (by decide)
    · exact ⟨⟨hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.1 (by decide)
    · exact ⟨⟨hfr, by decide⟩, hp.2⟩

/-- `&mut u8 → &mut u8`: sound. -/
theorem sound_mut_mut_byte_byte : Sound .mutable .mutable byteRef byteRef := by
  refine sound_of_invariant byteRef.valid (fun _ h => h) ?_ (fun _ h => h)
  intro m op hm hp
  have hfr : ¬ FrozenDuring .mutable .mutable byteRef byteRef := by
    simp [FrozenDuring]
  cases op with
  | read v =>
    cases v
    · exact absurd (show Mode.mutable = Mode.shared from hp) (by decide)
    · exact ⟨⟨hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.1 (by decide)
    · exact ⟨⟨hfr, by decide⟩, hp.2⟩

/-- Every cast from the uninhabited referent is vacuously sound. -/
theorem sound_of_neverRef (ms md : Mode) (D : RefTy) : Sound ms md neverRef D :=
  fun _ hm => absurd hm id

/-! ### Unsoundness proofs for fixture casts (explicit runs) -/

/-- `&mut bool → &mut u8`: write byte 2 through the `u8` view; the owner then reads an
invalid `bool`. -/
theorem not_sound_mut_mut_bool_byte : ¬ Sound .mutable .mutable boolRef byteRef := by
  intro h
  have := h [Sym.byte 0] (by decide) [.write .dst [Sym.byte 2]]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      exact ⟨Or.inl rfl, byteRef_valid 2⟩)
  exact absurd (show boolL.Lang [Sym.byte 2] from this.2) (by decide)

/-- `&mut u8 → & bool`: reading through the `bool` view sees byte 2. -/
theorem not_sound_mut_shared_byte_bool : ¬ Sound .mutable .shared byteRef boolRef := by
  intro h
  have := h [Sym.byte 2] (byteRef_valid 2) [.read .dst]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      trivial)
  exact absurd (show boolL.Lang [Sym.byte 2] from this.1.1) (by decide)

/-- The headline run: `& Cell<u8> → & u8`. Writing byte 1 through the `Cell` view while the
`&u8` is live violates the `frozen` assertion of the `&u8` (no read sees invalid bytes:
the two validities are equal). -/
theorem not_sound_shared_shared_cell_byte : ¬ Sound .shared .shared cellByteRef byteRef := by
  intro h
  have := h [Sym.byte 0] (cellByteRef_valid 0) [.write .src [Sym.byte 1]]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      exact ⟨rfl, rfl, cellByteRef_valid 1⟩)
  exact this.1.1 (Or.inr ⟨rfl, rfl⟩)

/-- `& u8 → &mut u8`: the original shared reference reads while the `&mut` is live,
violating the `unique` assertion. -/
theorem not_sound_shared_mut_byte_byte : ¬ Sound .shared .mutable byteRef byteRef := by
  intro h
  have := h [Sym.byte 0] (byteRef_valid 0) [.read .src]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      rfl)
  exact this.1.2 ⟨rfl, rfl⟩

/-! ### Definition examples -/

theorem ex_includes : Includes boolRef byteRef ∧ ¬ Includes byteRef boolRef :=
  ⟨boolRef_includes_byteRef, not_includes_byteRef_boolRef⟩

theorem ex_satisfiable : Satisfiable byteRef ∧ ¬ Satisfiable neverRef :=
  ⟨byteRef_satisfiable, neverRef_not_satisfiable⟩

theorem ex_permitted :
    Permitted .mutable .shared byteRef byteRef (.read .dst) ∧
    ¬ Permitted .mutable .shared byteRef byteRef (.read .src) ∧
    Permitted .shared .shared cellByteRef byteRef (.write .src [Sym.byte 5]) ∧
    ¬ Permitted .shared .shared byteRef byteRef (.write .src [Sym.byte 5]) ∧
    Permitted .mutable .mutable byteRef byteRef (.write .dst [Sym.byte 5]) ∧
    ¬ Permitted .mutable .shared byteRef byteRef (.write .dst [Sym.byte 5]) :=
  ⟨trivial, fun h => absurd (show Mode.mutable = Mode.shared from h) (by decide), ⟨rfl, rfl, cellByteRef_valid 5⟩, fun h => absurd h.2.1 (by decide),
    ⟨Or.inl rfl, byteRef_valid 5⟩, fun h => absurd h.1 (by decide)⟩

theorem ex_frozenDuring :
    FrozenDuring .shared .shared cellByteRef byteRef ∧
    ¬ FrozenDuring .mutable .shared byteRef cellByteRef ∧
    ¬ FrozenDuring .mutable .mutable byteRef byteRef := by
  refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩ <;> simp [FrozenDuring, cellByteRef, RefTy.ofLayout]

theorem ex_opOK :
    OpOK .shared .shared cellByteRef byteRef [Sym.byte 0] (.read .dst) ∧
    ¬ OpOK .shared .shared cellByteRef byteRef [Sym.byte 0] (.write .src [Sym.byte 1]) ∧
    ¬ OpOK .shared .mutable byteRef byteRef [Sym.byte 0] (.read .src) :=
  ⟨⟨byteRef_valid 0, by decide⟩, fun h => h.1 (Or.inr ⟨rfl, rfl⟩), fun h => h.2 ⟨rfl, rfl⟩⟩

theorem ex_runOK :
    RunOK .mutable .mutable byteRef byteRef [Sym.byte 0] [.write .dst [Sym.byte 1], .read .dst] ∧
    ¬ RunOK .mutable .mutable boolRef byteRef [Sym.byte 0] [.write .dst [Sym.byte 2]] := by
  refine ⟨⟨⟨by simp [FrozenDuring], by decide⟩, ⟨byteRef_valid 1, by decide⟩, byteRef_valid 1⟩,
    fun h => absurd (show boolL.Lang [Sym.byte 2] from h.2) (by decide)⟩

theorem ex_sound : Sound .shared .shared boolRef byteRef ∧ Sound .mutable .mutable byteRef byteRef :=
  ⟨sound_shared_shared_bool_byte, sound_mut_mut_byte_byte⟩

theorem ex_not_sound : ¬ Sound .mutable .mutable boolRef byteRef ∧
    ¬ Sound .mutable .shared byteRef boolRef :=
  ⟨not_sound_mut_mut_bool_byte, not_sound_mut_shared_byte_bool⟩

theorem ex_matrixOK :
    MatrixOK .shared .shared boolRef byteRef ∧ ¬ MatrixOK .shared .shared cellByteRef byteRef ∧
    ¬ MatrixOK .shared .mutable byteRef byteRef :=
  ⟨⟨boolRef_includes_byteRef, rfl, rfl⟩, fun h => absurd h.2.2 (by decide), id⟩

theorem ex_matrixOKNoSrcFreeze :
    MatrixOKNoSrcFreeze .shared .shared cellByteRef byteRef ∧
    ¬ MatrixOKNoSrcFreeze .shared .shared cellByteRef cellByteRef :=
  ⟨⟨cellByteRef_includes_byteRef, rfl⟩, fun h => absurd h.2 (by decide)⟩

theorem ex_refCheck :
    refCheck .shared .shared boolL true u8L true = true ∧
    refCheck .shared .shared u8L false u8L true = false ∧
    refCheck .shared .mutable u8L true u8L true = false := by
  refine ⟨by decide +kernel, by decide +kernel, rfl⟩

end Toy.LayoutDfa
