import ToyTransmute.Examples

/-!
# Counterexamples, non-vacuity witnesses and positive controls (all fully proved)

**Canonical form.** A counterexample for a hypothesis `h` of a result is a theorem stating
that a concrete instance satisfies every *other* hypothesis of the result and that the
result's conclusion fails there; where useful it also records that `h` itself fails.

**Non-vacuity.** A non-vacuity theorem exhibits a concrete instance satisfying every
hypothesis of a result. For an `↔` result it exhibits instances on which both sides are
true and, where informative, instances on which both sides are false.

This module does not import the main-results module, so no counterexample, witness or
positive control depends on a main result; each is proved directly from the definitions and
the proof tools.
-/

namespace Toy.Transmute

/-! ## The `bool`/byte family of counterexamples -/

/-- **C1.** `bool → byte`: the value transmute and the shared cast are sound. -/
theorem boolV_to_byteV_value_and_shared_sound :
    Includes boolV byteV ∧ ValueSound boolV byteV ∧ SharedSound boolV byteV :=
  ⟨includes_boolV_byteV, valueSound_boolV_byteV, sharedSound_boolV_byteV⟩

/-- **C2 (explicit violating run).** `&mut bool → &mut byte`: from the valid `bool` `0`,
writing the byte `2` through the byte view (a well-typed write) and then reading through the
`bool` view observes an invalid `bool`; the run is permitted by the mutable discipline. -/
theorem boolV_to_byteV_mut_violating_run :
    (mutProtocol : Protocol (Fin 256) 1) (writeDstReadSrc (byteSeq 2)) ∧
    (∀ op ∈ (writeDstReadSrc (byteSeq 2) : List (Op (Fin 256) 1)),
      op.WellTyped boolV byteV) ∧
    boolV (byteSeq 0) ∧
    ¬ NoInvalidRead boolV byteV (byteSeq 0) (writeDstReadSrc (byteSeq 2)) :=
  ⟨mutProtocol_writeDstReadSrc _, writeDstReadSrc_wellTyped trivial, boolV_byteSeq_zero,
    writeDstReadSrc_violates _ not_boolV_byteSeq_two⟩

/-- **C2 (canonical, for R3 exact).** The read-side condition `T ⊆ U` alone does not make a
mutable cast sound: for `bool → byte`, `T ⊆ U` holds and `T` is satisfiable, the write-side
condition `U ⊆ T` fails, and the mutable cast is unsound. -/
theorem mutSound_needs_includes_rev :
    Includes boolV byteV ∧ Satisfiable boolV ∧ ¬ Includes byteV boolV ∧
      ¬ MutSound boolV byteV :=
  ⟨includes_boolV_byteV, satisfiable_boolV, not_includes_byteV_boolV,
    not_mutSound_boolV_byteV⟩

/-- **C3 (canonical, for R1, R2 and R3 exact).** `byte → bool` is unsound even by value. The
write-side condition of R3 holds (`bool ⊆ byte`), the read-side condition fails, and all
three disciplines are unsound. -/
theorem byteV_to_boolV_unsound_even_by_value :
    (Satisfiable byteV → Includes boolV byteV) ∧ ¬ Includes byteV boolV ∧
      ¬ ValueSound byteV boolV ∧ ¬ SharedSound byteV boolV ∧ ¬ MutSound byteV boolV :=
  ⟨fun _ => includes_boolV_byteV, not_includes_byteV_boolV, not_valueSound_byteV_boolV,
    not_sharedSound_byteV_boolV, not_mutSound_byteV_boolV⟩

/-- **C4.** An interior-mutability cast that is fine without writes but unsound once the
destination side can write: `bool → byte`. -/
theorem boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes :
    SharedSound boolV byteV ∧ SharedIMSound false false boolV byteV ∧
      ¬ SharedIMSound false true boolV byteV ∧ ¬ SharedIMSound true true boolV byteV :=
  ⟨sharedSound_boolV_byteV,
    sharedIMSound_of_invariant boolV (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)),
    not_sharedIMSound_dst_boolV_byteV false, not_sharedIMSound_dst_boolV_byteV true⟩

/-- **C5 (canonical, for R4 equality form: the destination-writes hypothesis).** Writes on
the source side only do not force validity equality: `bool → byte` with only the source side
writable satisfies every other hypothesis (`bool` satisfiable), is sound, but the validities
differ, so "sound ↔ equal" fails. This refutes the reading "shared casts where *either* side
can write need equality". -/
theorem sharedIMSound_eq_needs_dstWrites :
    Satisfiable boolV ∧ SharedIMSound true false boolV byteV ∧ ¬ ValidityEq boolV byteV ∧
      ¬ (SharedIMSound true false boolV byteV ↔ ValidityEq boolV byteV) :=
  ⟨satisfiable_boolV, sharedIMSound_true_false_boolV_byteV, not_validityEq_boolV_byteV,
    fun h => not_validityEq_boolV_byteV (h.1 sharedIMSound_true_false_boolV_byteV)⟩

/-- **C6 (canonical, for R3 equality form: the satisfiability hypothesis).** From the
uninhabited type, the mutable cast to a raw byte is (vacuously) sound although the
validities differ, so "sound ↔ equal" fails without satisfiability. -/
theorem mutSound_eq_needs_satisfiable :
    ¬ Satisfiable neverV ∧ MutSound neverV byteV ∧ ¬ ValidityEq neverV byteV ∧
      ¬ (MutSound neverV byteV ↔ ValidityEq neverV byteV) := by
  have hs : MutSound neverV byteV := sound_of_not_satisfiable _ not_satisfiable_neverV _
  have hne : ¬ ValidityEq neverV byteV := fun h => (h (byteSeq 0)).2 trivial
  exact ⟨not_satisfiable_neverV, hs, hne, fun h => hne (h.1 hs)⟩

/-- **C6' (canonical, for R4 equality form: the satisfiability hypothesis).** -/
theorem sharedIMSound_eq_needs_satisfiable :
    ¬ Satisfiable neverV ∧ SharedIMSound true true neverV byteV ∧
      ¬ (SharedIMSound true true neverV byteV ↔ ValidityEq neverV byteV) := by
  have hs : SharedIMSound true true neverV byteV :=
    sound_of_not_satisfiable _ not_satisfiable_neverV _
  have hne : ¬ ValidityEq neverV byteV := fun h => (h (byteSeq 0)).2 trivial
  exact ⟨not_satisfiable_neverV, hs, fun h => hne (h.1 hs)⟩

/-! ## Non-vacuity of R1–R4 -/

/-- **R1 non-vacuity.** Both sides true (`bool → byte`) and both sides false
(`byte → bool`). -/
theorem valueSound_iff_includes_nonvacuous :
    (ValueSound boolV byteV ∧ Includes boolV byteV) ∧
      (¬ ValueSound byteV boolV ∧ ¬ Includes byteV boolV) :=
  ⟨⟨valueSound_boolV_byteV, includes_boolV_byteV⟩,
    ⟨not_valueSound_byteV_boolV, not_includes_byteV_boolV⟩⟩

/-- **R2 non-vacuity.** -/
theorem sharedSound_iff_includes_nonvacuous :
    (SharedSound boolV byteV ∧ Includes boolV byteV) ∧
      (¬ SharedSound byteV boolV ∧ ¬ Includes byteV boolV) :=
  ⟨⟨sharedSound_boolV_byteV, includes_boolV_byteV⟩,
    ⟨not_sharedSound_byteV_boolV, not_includes_byteV_boolV⟩⟩

/-- **R3 exact, non-vacuity.** Both sides true for `bool → bool'`, both false for
`bool → byte`. -/
theorem mutSound_exact_nonvacuous :
    (MutSound boolV boolV' ∧ Includes boolV boolV' ∧ (Satisfiable boolV → Includes boolV' boolV)) ∧
      (¬ MutSound boolV byteV ∧
        ¬ (Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV))) :=
  ⟨⟨mutSound_boolV_boolV', fun m => (validityEq_boolV_boolV' m).1,
      fun _ m => (validityEq_boolV_boolV' m).2⟩,
    ⟨not_mutSound_boolV_byteV, fun h => not_includes_byteV_boolV (h.2 satisfiable_boolV)⟩⟩

/-- **R3 equality form, non-vacuity.** -/
theorem mutSound_eq_nonvacuous :
    Satisfiable boolV ∧ MutSound boolV boolV' ∧ ValidityEq boolV boolV' :=
  ⟨satisfiable_boolV, mutSound_boolV_boolV', validityEq_boolV_boolV'⟩

/-- **R3 impossibility form, non-vacuity.** Both hypotheses hold for `bool → byte` (and the
conclusion is confirmed there directly). -/
theorem not_mutSound_nonvacuous :
    Satisfiable boolV ∧ ¬ ValidityEq boolV byteV ∧ ¬ MutSound boolV byteV :=
  ⟨satisfiable_boolV, not_validityEq_boolV_byteV, not_mutSound_boolV_byteV⟩

/-- **R3 impossibility form, positive control (weakening the cast kind).** For the same
`bool → byte` pair with both hypotheses holding, the value transmute, the shared cast, and
the shared cast where only the source side writes are all sound. -/
theorem not_mutSound_positive_control_weaker_casts :
    Satisfiable boolV ∧ ¬ ValidityEq boolV byteV ∧
      ValueSound boolV byteV ∧ SharedSound boolV byteV ∧ SharedIMSound true false boolV byteV :=
  ⟨satisfiable_boolV, not_validityEq_boolV_byteV, valueSound_boolV_byteV,
    sharedSound_boolV_byteV, sharedIMSound_true_false_boolV_byteV⟩

/-- **R3 impossibility form, positive control / counterexample (dropping satisfiability).**
`never → byte`: validities differ and the mutable cast is sound. -/
theorem not_mutSound_needs_satisfiable :
    ¬ Satisfiable neverV ∧ ¬ ValidityEq neverV byteV ∧ MutSound neverV byteV :=
  ⟨not_satisfiable_neverV, fun h => (h (byteSeq 0)).2 trivial,
    sound_of_not_satisfiable _ not_satisfiable_neverV _⟩

/-- **R3 impossibility form, counterexample (dropping `¬ T ≡ U`).** -/
theorem not_mutSound_needs_not_validityEq :
    Satisfiable boolV ∧ ValidityEq boolV boolV' ∧ MutSound boolV boolV' :=
  ⟨satisfiable_boolV, validityEq_boolV_boolV', mutSound_boolV_boolV'⟩

/-- **R4 exact, non-vacuity.** Both sides true with both flags set (`bool → bool'`) and with
only the source flag set (`bool → byte`); both sides false with the destination flag set
(`bool → byte`). -/
theorem sharedIMSound_exact_nonvacuous :
    (SharedIMSound true true boolV boolV' ∧ Includes boolV boolV' ∧
        (true = true → Satisfiable boolV → Includes boolV' boolV)) ∧
      (SharedIMSound true false boolV byteV ∧ Includes boolV byteV) ∧
      (¬ SharedIMSound true true boolV byteV ∧
        ¬ (Includes boolV byteV ∧ (true = true → Satisfiable boolV → Includes byteV boolV))) :=
  ⟨⟨sharedIMSound_boolV_boolV' true true, fun m => (validityEq_boolV_boolV' m).1,
      fun _ _ m => (validityEq_boolV_boolV' m).2⟩,
    ⟨sharedIMSound_true_false_boolV_byteV, includes_boolV_byteV⟩,
    ⟨not_sharedIMSound_dst_boolV_byteV true,
      fun h => not_includes_byteV_boolV (h.2 rfl satisfiable_boolV)⟩⟩

/-- **R4 exact, condition tightness (reads).** For every pair of flags, `byte → bool` is
unsound: the read-side condition `T ⊆ U` cannot be dropped, whatever the write flags. -/
theorem sharedIMSound_needs_includes (srcWrites dstWrites : Bool) :
    ¬ Includes byteV boolV ∧ ¬ SharedIMSound srcWrites dstWrites byteV boolV :=
  ⟨not_includes_byteV_boolV,
    not_sound_of_read_dst (sharedIMProtocol_readDst srcWrites dstWrites) (m := byteSeq 2)
      trivial not_boolV_byteSeq_two⟩

/-- **R4 equality form, non-vacuity.** -/
theorem sharedIMSound_eq_nonvacuous :
    Satisfiable boolV ∧ SharedIMSound true true boolV boolV' ∧ ValidityEq boolV boolV' :=
  ⟨satisfiable_boolV, sharedIMSound_boolV_boolV' true true, validityEq_boolV_boolV'⟩

/-- **R4 source-only writes, non-vacuity.** -/
theorem sharedIMSound_noDst_nonvacuous :
    SharedIMSound true false boolV byteV ∧ Includes boolV byteV :=
  ⟨sharedIMSound_true_false_boolV_byteV, includes_boolV_byteV⟩

/-- **R4 source-only writes, counterexample (setting the destination flag).** With the
destination flag set, `T ⊆ U` holds for `bool → byte` but the cast is unsound. -/
theorem sharedIMSound_noDst_needs_noDstWrites :
    Includes boolV byteV ∧ ¬ SharedIMSound true true boolV byteV :=
  ⟨includes_boolV_byteV, not_sharedIMSound_dst_boolV_byteV true⟩

/-- **R4 coincidence with mutable casts, non-vacuity.** -/
theorem mutSound_iff_sharedIM_nonvacuous :
    MutSound boolV boolV' ∧ SharedIMSound false true boolV boolV' ∧
      SharedIMSound true true boolV boolV' :=
  ⟨mutSound_boolV_boolV', sharedIMSound_boolV_boolV' false true,
    sharedIMSound_boolV_boolV' true true⟩

/-- **R4 coincidence with mutable casts, counterexample (destination flag unset).** Mutable
soundness does not coincide with shared soundness when only the source side writes. -/
theorem mutSound_iff_sharedIM_needs_dstWrites :
    ¬ MutSound boolV byteV ∧ SharedIMSound true false boolV byteV ∧
      ¬ (MutSound boolV byteV ↔ SharedIMSound true false boolV byteV) :=
  ⟨not_mutSound_boolV_byteV, sharedIMSound_true_false_boolV_byteV,
    fun h => not_mutSound_boolV_byteV (h.2 sharedIMSound_true_false_boolV_byteV)⟩

/-! ## R5. Composition and hierarchy -/

/-- Generic transitivity counterexample (dropping the first hypothesis): with
`(T, U, V) = (byte, bool, bool)`, the second hypothesis `Sound P bool bool` holds and the
conclusion `Sound P byte bool` fails, for any discipline permitting `readDst`. -/
theorem sound_trans_counterexample_first {P : Protocol (Fin 256) 1} (hP : P readDst) :
    Sound P boolV boolV ∧ ¬ Sound P byteV boolV :=
  ⟨sound_refl P boolV, not_sound_of_read_dst hP (m := byteSeq 2) trivial not_boolV_byteSeq_two⟩

/-- Generic transitivity counterexample (dropping the second hypothesis): with
`(T, U, V) = (byte, byte, bool)`, the first hypothesis `Sound P byte byte` holds and the
conclusion `Sound P byte bool` fails. -/
theorem sound_trans_counterexample_second {P : Protocol (Fin 256) 1} (hP : P readDst) :
    Sound P byteV byteV ∧ ¬ Sound P byteV boolV :=
  ⟨sound_refl P byteV, not_sound_of_read_dst hP (m := byteSeq 2) trivial not_boolV_byteSeq_two⟩

theorem valueSound_trans_needs_first : ValueSound boolV boolV ∧ ¬ ValueSound byteV boolV :=
  sound_trans_counterexample_first valueProtocol_readDst

theorem valueSound_trans_needs_second : ValueSound byteV byteV ∧ ¬ ValueSound byteV boolV :=
  sound_trans_counterexample_second valueProtocol_readDst

theorem sharedSound_trans_needs_first : SharedSound boolV boolV ∧ ¬ SharedSound byteV boolV :=
  sound_trans_counterexample_first sharedProtocol_readDst

theorem sharedSound_trans_needs_second :
    SharedSound byteV byteV ∧ ¬ SharedSound byteV boolV :=
  sound_trans_counterexample_second sharedProtocol_readDst

theorem mutSound_trans_needs_first : MutSound boolV boolV ∧ ¬ MutSound byteV boolV :=
  sound_trans_counterexample_first mutProtocol_readDst

theorem mutSound_trans_needs_second : MutSound byteV byteV ∧ ¬ MutSound byteV boolV :=
  sound_trans_counterexample_second mutProtocol_readDst

theorem sharedIMSound_trans_needs_first (srcWrites dstWrites : Bool) :
    SharedIMSound srcWrites dstWrites boolV boolV ∧
      ¬ SharedIMSound srcWrites dstWrites byteV boolV :=
  sound_trans_counterexample_first (sharedIMProtocol_readDst srcWrites dstWrites)

theorem sharedIMSound_trans_needs_second (srcWrites dstWrites : Bool) :
    SharedIMSound srcWrites dstWrites byteV byteV ∧
      ¬ SharedIMSound srcWrites dstWrites byteV boolV :=
  sound_trans_counterexample_second (sharedIMProtocol_readDst srcWrites dstWrites)

/-- **R5 non-vacuity (value).** A strict chain `zero-only → bool → byte`. -/
theorem valueSound_trans_nonvacuous : ValueSound zeroV boolV ∧ ValueSound boolV byteV :=
  ⟨valueSound_of_invariant boolV (fun _ h => Or.inl h) (fun _ h => h) (fun _ h => h),
    valueSound_boolV_byteV⟩

/-- **R5 non-vacuity (shared).** -/
theorem sharedSound_trans_nonvacuous : SharedSound zeroV boolV ∧ SharedSound boolV byteV :=
  ⟨sharedSound_of_invariant zeroV (fun _ h => h) (fun _ h => h) (fun _ h => Or.inl h),
    sharedSound_boolV_byteV⟩

/-- `bool ⊔ zero-only` accepts exactly the `bool` bytes. -/
theorem validityEq_boolV_join_zeroV : ValidityEq boolV (boolV.join zeroV) :=
  fun _ => ⟨Or.inl, fun h => h.elim id Or.inl⟩

/-- **R5 non-vacuity (mutable), satisfiable chain.** Three syntactically different predicates
`bool' → bool → bool ⊔ zero-only`. For a satisfiable source every sound mutable chain consists
of extensionally equal validities (R3), so no satisfiable chain with `T ≢ V` exists; the
chain with `T ≢ V` starts at an unsatisfiable type (`mutSound_trans_uninhabited_nonvacuous`). -/
theorem mutSound_trans_nonvacuous :
    MutSound boolV' boolV ∧ MutSound boolV (boolV.join zeroV) :=
  ⟨mutSound_boolV'_boolV, sound_of_validityEq _ validityEq_boolV_join_zeroV⟩

/-- **R5 non-vacuity (mutable), chain from an unsatisfiable type.** `never → bool → bool'`:
both legs are sound, the end points have different validities. -/
theorem mutSound_trans_uninhabited_nonvacuous :
    ¬ Satisfiable neverV ∧ Satisfiable boolV ∧ ¬ ValidityEq neverV boolV' ∧
      MutSound neverV boolV ∧ MutSound boolV boolV' :=
  ⟨not_satisfiable_neverV, satisfiable_boolV,
    fun h => (h (byteSeq 1)).2 boolV'_byteSeq_one,
    sound_of_not_satisfiable _ not_satisfiable_neverV _,
    mutSound_boolV_boolV'⟩

/-- **R5 non-vacuity (interior mutability), for every pair of flags.** The satisfiable chain
`bool' → bool → bool ⊔ zero-only`. -/
theorem sharedIMSound_trans_nonvacuous (srcWrites dstWrites : Bool) :
    SharedIMSound srcWrites dstWrites boolV' boolV ∧
      SharedIMSound srcWrites dstWrites boolV (boolV.join zeroV) :=
  ⟨sound_of_validityEq _ (fun m => (validityEq_boolV_boolV' m).symm),
    sound_of_validityEq _ validityEq_boolV_join_zeroV⟩

/-- **R5 non-vacuity (interior mutability), chain from an unsatisfiable type**, for every pair
of flags: `never → bool → bool'`. -/
theorem sharedIMSound_trans_uninhabited_nonvacuous (srcWrites dstWrites : Bool) :
    ¬ Satisfiable neverV ∧ ¬ ValidityEq neverV boolV' ∧
      SharedIMSound srcWrites dstWrites neverV boolV ∧
      SharedIMSound srcWrites dstWrites boolV boolV' :=
  ⟨not_satisfiable_neverV, fun h => (h (byteSeq 1)).2 boolV'_byteSeq_one,
    sound_of_not_satisfiable _ not_satisfiable_neverV _,
    sharedIMSound_boolV_boolV' srcWrites dstWrites⟩

/-- **R5 non-vacuity (interior mutability without destination writes), strict chain**, for
either source flag: `zero-only → bool → byte`, pairwise different validities. -/
theorem sharedIMSound_noDst_trans_strict_nonvacuous (srcWrites : Bool) :
    ¬ ValidityEq zeroV boolV ∧ ¬ ValidityEq boolV byteV ∧ ¬ ValidityEq zeroV byteV ∧
      SharedIMSound srcWrites false zeroV boolV ∧
      SharedIMSound srcWrites false boolV byteV := by
  have hne01 : ¬ ValidityEq zeroV boolV :=
    fun h => not_zeroV_byteSeq_one ((h (byteSeq 1)).2 boolV_byteSeq_one)
  have hne02 : ¬ ValidityEq zeroV byteV :=
    fun h => not_zeroV_byteSeq_one ((h (byteSeq 1)).2 trivial)
  have hs01 : SharedIMSound srcWrites false zeroV boolV :=
    sharedIMSound_of_invariant zeroV (fun _ h => h) (fun _ h => h) (fun _ h => Or.inl h)
      (fun _ _ h => h) (fun h => Bool.noConfusion h)
  have hs12 : SharedIMSound srcWrites false boolV byteV :=
    sharedIMSound_of_invariant boolV (fun _ h => h) (fun _ h => h) includes_boolV_byteV
      (fun _ _ h => h) (fun h => Bool.noConfusion h)
  exact ⟨hne01, not_validityEq_boolV_byteV, hne02, hs01, hs12⟩

/-- **R5 hierarchy, strictness (positive control).** Shared soundness does not imply mutable
soundness: `bool → byte`. -/
theorem sharedSound_not_imp_mutSound :
    SharedSound boolV byteV ∧ ¬ MutSound boolV byteV :=
  ⟨sharedSound_boolV_byteV, not_mutSound_boolV_byteV⟩

/-- **R5 symmetry, counterexample (dropping satisfiability).** `never → byte` is a sound
mutable cast whose reverse `byte → never` is unsound. -/
theorem mutSound_symm_needs_satisfiable :
    ¬ Satisfiable neverV ∧ MutSound neverV byteV ∧ ¬ MutSound byteV neverV :=
  ⟨not_satisfiable_neverV, sound_of_not_satisfiable _ not_satisfiable_neverV _,
    not_sound_of_read_dst mutProtocol_readDst (m := byteSeq 0) trivial id⟩

/-- **R5 symmetry, counterexample (dropping the soundness hypothesis).** With
`(T, U) = (bool, byte)`: `bool` is satisfiable, the hypothesis fails, and the conclusion
`MutSound byte bool` fails. -/
theorem mutSound_symm_needs_mutSound :
    Satisfiable boolV ∧ ¬ MutSound boolV byteV ∧ ¬ MutSound byteV boolV :=
  ⟨satisfiable_boolV, not_mutSound_boolV_byteV, not_mutSound_byteV_boolV⟩

/-- **R5 symmetry, non-vacuity.** -/
theorem mutSound_symm_nonvacuous : Satisfiable boolV ∧ MutSound boolV boolV' :=
  ⟨satisfiable_boolV, mutSound_boolV_boolV'⟩

/-! ## R7. Lattice -/

/-- **R7 non-vacuity (into a join).** The join strictly enlarges `bool` and the shared cast
into it is sound. -/
theorem sharedSound_to_join_left_nonvacuous :
    SharedSound boolV (boolV.join twoV) ∧ ¬ Includes (boolV.join twoV) boolV :=
  ⟨sharedSound_of_invariant boolV (fun _ h => h) (fun _ h => h) (fun _ h => Or.inl h),
    fun h => not_boolV_byteSeq_two (h _ join_boolV_twoV_two)⟩

/-- **R7 positive control (which casts survive a join).** The shared cast `bool → bool ⊔ two`
is sound but the mutable cast is not: write `2` through the join view, read the `bool`. -/
theorem mutSound_to_join_fails_example :
    SharedSound boolV (boolV.join twoV) ∧ ¬ MutSound boolV (boolV.join twoV) :=
  ⟨sharedSound_to_join_left_nonvacuous.1,
    not_sound_of_write_dst_read_src (mutProtocol_writeDstReadSrc (byteSeq 2)) (m := byteSeq 0)
      boolV_byteSeq_zero join_boolV_twoV_two not_boolV_byteSeq_two⟩

/-- **R7 non-vacuity (out of a meet).** The meet strictly shrinks `bool` and the shared cast
out of it is sound. -/
theorem sharedSound_from_meet_left_nonvacuous :
    SharedSound (boolV.meet zeroV) boolV ∧ ¬ Includes boolV (boolV.meet zeroV) :=
  ⟨sharedSound_of_invariant (boolV.meet zeroV) (fun _ h => h) (fun _ h => h)
      (fun _ h => h.1),
    fun h => not_meet_boolV_zeroV_one (h _ boolV_byteSeq_one)⟩

/-- **R7 non-vacuity (join characterization).** Both sides true into `byte`; both sides false
into `bool`. -/
theorem sharedSound_join_iff_nonvacuous :
    (SharedSound (boolV.join twoV) byteV ∧ SharedSound boolV byteV ∧ SharedSound twoV byteV) ∧
      (¬ SharedSound (boolV.join twoV) boolV ∧ ¬ SharedSound twoV boolV) :=
  ⟨⟨sharedSound_of_invariant (boolV.join twoV) (fun _ h => h) (fun _ h => h)
        (fun _ _ => trivial),
      sharedSound_boolV_byteV,
      sharedSound_of_invariant twoV (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)⟩,
    ⟨not_sound_of_read_dst sharedProtocol_readDst (m := byteSeq 2) join_boolV_twoV_two
        not_boolV_byteSeq_two,
      not_sound_of_read_dst sharedProtocol_readDst (m := byteSeq 2) twoV_byteSeq_two
        not_boolV_byteSeq_two⟩⟩

/-- **R7 non-vacuity (meet characterization).** Both sides true with three pairwise
different types (`V = zero-only`, `T = bool`, `U = zero-only ⊔ two`), and both sides false
(`V = bool`, `T = byte`, `U = zero-only`). -/
theorem sharedSound_meet_iff_nonvacuous :
    (¬ ValidityEq zeroV boolV ∧ ¬ ValidityEq zeroV (zeroV.join twoV) ∧
      SharedSound zeroV (boolV.meet (zeroV.join twoV)) ∧
      SharedSound zeroV boolV ∧ SharedSound zeroV (zeroV.join twoV)) ∧
    (¬ SharedSound boolV (byteV.meet zeroV) ∧
      SharedSound boolV byteV ∧ ¬ SharedSound boolV zeroV) := by
  have hne1 : ¬ ValidityEq zeroV boolV :=
    fun h => not_zeroV_byteSeq_one ((h (byteSeq 1)).2 boolV_byteSeq_one)
  have hne2 : ¬ ValidityEq zeroV (zeroV.join twoV) :=
    fun h => not_twoV_byteSeq_zero (((h (byteSeq 2)).2 (Or.inr twoV_byteSeq_two)).symm ▸ rfl)
  refine ⟨⟨hne1, hne2,
    sharedSound_of_invariant zeroV (fun _ h => h) (fun _ h => h)
      (fun _ h => ⟨Or.inl h, Or.inl h⟩),
    sharedSound_of_invariant zeroV (fun _ h => h) (fun _ h => h) (fun _ h => Or.inl h),
    sharedSound_of_invariant zeroV (fun _ h => h) (fun _ h => h) (fun _ h => Or.inl h)⟩, ?_⟩
  exact ⟨not_sound_of_read_dst sharedProtocol_readDst boolV_byteSeq_one
      (fun h => not_zeroV_byteSeq_one h.2),
    sharedSound_boolV_byteV,
    not_sound_of_read_dst sharedProtocol_readDst boolV_byteSeq_one not_zeroV_byteSeq_one⟩

/-- **R7 non-vacuity (into a join, right operand).** The join strictly enlarges the two-only
type and the shared cast into it is sound. -/
theorem sharedSound_to_join_right_nonvacuous :
    SharedSound twoV (boolV.join twoV) ∧ ¬ Includes (boolV.join twoV) twoV :=
  ⟨sharedSound_of_invariant twoV (fun _ h => h) (fun _ h => h) (fun _ h => Or.inr h),
    fun h => not_twoV_byteSeq_zero (h _ (Or.inl boolV_byteSeq_zero))⟩

/-- **R7 non-vacuity (out of a meet, right operand).** The meet of zero-only and `bool` is
strictly smaller than `bool` and the shared cast out of it into `bool` is sound. -/
theorem sharedSound_from_meet_right_nonvacuous :
    SharedSound (zeroV.meet boolV) boolV ∧ ¬ Includes boolV (zeroV.meet boolV) :=
  ⟨sharedSound_of_invariant (zeroV.meet boolV) (fun _ h => h) (fun _ h => h)
      (fun _ h => h.2),
    fun h => not_zeroV_byteSeq_one (h _ boolV_byteSeq_one).1⟩

/-- **R7 join characterization, tightness of the first right-hand conjunct** (`T → V`):
`(T, U, V) = (two-only, bool, bool)`. The other conjunct `U → V` holds, `T → V` fails, and the
join cast fails, so the equivalence with only the other conjunct fails. -/
theorem sharedSound_join_iff_needs_left :
    SharedSound boolV boolV ∧ ¬ SharedSound twoV boolV ∧
      ¬ SharedSound (twoV.join boolV) boolV ∧
      ¬ (SharedSound (twoV.join boolV) boolV ↔ SharedSound boolV boolV) := by
  have hns : ¬ SharedSound (twoV.join boolV) boolV :=
    not_sound_of_read_dst sharedProtocol_readDst (m := byteSeq 2) (Or.inl twoV_byteSeq_two)
      not_boolV_byteSeq_two
  have hnt : ¬ SharedSound twoV boolV :=
    not_sound_of_read_dst sharedProtocol_readDst twoV_byteSeq_two not_boolV_byteSeq_two
  exact ⟨sound_refl _ boolV, hnt, hns, fun h => hns (h.2 (sound_refl _ boolV))⟩

/-- **R7 join characterization, tightness of the second right-hand conjunct** (`U → V`):
`(T, U, V) = (bool, two-only, bool)`. -/
theorem sharedSound_join_iff_needs_right :
    SharedSound boolV boolV ∧ ¬ SharedSound twoV boolV ∧
      ¬ SharedSound (boolV.join twoV) boolV ∧
      ¬ (SharedSound (boolV.join twoV) boolV ↔ SharedSound boolV boolV) := by
  have hns : ¬ SharedSound (boolV.join twoV) boolV :=
    not_sound_of_read_dst sharedProtocol_readDst join_boolV_twoV_two not_boolV_byteSeq_two
  have hnt : ¬ SharedSound twoV boolV :=
    not_sound_of_read_dst sharedProtocol_readDst twoV_byteSeq_two not_boolV_byteSeq_two
  exact ⟨sound_refl _ boolV, hnt, hns, fun h => hns (h.2 (sound_refl _ boolV))⟩

/-- **R7 meet characterization, tightness of the first right-hand conjunct** (`V → T`):
`(T, U, V) = (zero-only, byte, bool)`. -/
theorem sharedSound_meet_iff_needs_left :
    SharedSound boolV byteV ∧ ¬ SharedSound boolV zeroV ∧
      ¬ SharedSound boolV (zeroV.meet byteV) ∧
      ¬ (SharedSound boolV (zeroV.meet byteV) ↔ SharedSound boolV byteV) := by
  have hnm : ¬ (zeroV.meet byteV) (byteSeq 1) := fun h => not_zeroV_byteSeq_one h.1
  have hns : ¬ SharedSound boolV (zeroV.meet byteV) :=
    not_sound_of_read_dst sharedProtocol_readDst boolV_byteSeq_one hnm
  have hnz : ¬ SharedSound boolV zeroV :=
    not_sound_of_read_dst sharedProtocol_readDst boolV_byteSeq_one not_zeroV_byteSeq_one
  exact ⟨sharedSound_boolV_byteV, hnz, hns, fun h => hns (h.2 sharedSound_boolV_byteV)⟩

/-- **R7 meet characterization, tightness of the second right-hand conjunct** (`V → U`):
`(T, U, V) = (byte, zero-only, bool)`. -/
theorem sharedSound_meet_iff_needs_right :
    SharedSound boolV byteV ∧ ¬ SharedSound boolV zeroV ∧
      ¬ SharedSound boolV (byteV.meet zeroV) ∧
      ¬ (SharedSound boolV (byteV.meet zeroV) ↔ SharedSound boolV byteV) := by
  have hnm : ¬ (byteV.meet zeroV) (byteSeq 1) := fun h => not_zeroV_byteSeq_one h.2
  have hns : ¬ SharedSound boolV (byteV.meet zeroV) :=
    not_sound_of_read_dst sharedProtocol_readDst boolV_byteSeq_one hnm
  have hnz : ¬ SharedSound boolV zeroV :=
    not_sound_of_read_dst sharedProtocol_readDst boolV_byteSeq_one not_zeroV_byteSeq_one
  exact ⟨sharedSound_boolV_byteV, hnz, hns, fun h => hns (h.2 sharedSound_boolV_byteV)⟩

/-- **R7 non-vacuity (mutable cast into a join).** `bool ⊔ zero-only` adds nothing to `bool`,
and the mutable cast into it is sound. The right-hand side is the reverse inclusion
`Includes U T` (`zero-only ⊆ bool`); the forward inclusion `Includes T U` (`bool ⊆ zero-only`)
fails here. -/
theorem mutSound_to_join_nonvacuous :
    Satisfiable boolV ∧ MutSound boolV (boolV.join zeroV) ∧ Includes zeroV boolV ∧
      ¬ Includes boolV zeroV :=
  ⟨satisfiable_boolV,
    sound_of_validityEq _ validityEq_boolV_join_zeroV,
    fun _ h => Or.inl h,
    fun h => not_zeroV_byteSeq_one (h (byteSeq 1) boolV_byteSeq_one)⟩

/-- **R7 mutable cast into a join, tightness of the right-hand side `Includes U T`.** For
`bool → bool ⊔ two-only`, `bool` is satisfiable, `two-only ⊄ bool`, and the mutable cast is
unsound (write `2` through the join view, read the `bool`). -/
theorem mutSound_to_join_needs_includes_rev :
    Satisfiable boolV ∧ ¬ Includes twoV boolV ∧ ¬ MutSound boolV (boolV.join twoV) :=
  ⟨satisfiable_boolV,
    fun h => not_boolV_byteSeq_two (h (byteSeq 2) twoV_byteSeq_two),
    not_sound_of_write_dst_read_src (mutProtocol_writeDstReadSrc (byteSeq 2)) (m := byteSeq 0)
      boolV_byteSeq_zero join_boolV_twoV_two not_boolV_byteSeq_two⟩

/-- **R7 counterexample (mutable cast into a join, dropping satisfiability).** -/
theorem mutSound_to_join_needs_satisfiable :
    ¬ Satisfiable neverV ∧ MutSound neverV (neverV.join byteV) ∧ ¬ Includes byteV neverV ∧
      ¬ (MutSound neverV (neverV.join byteV) ↔ Includes byteV neverV) := by
  have hs : MutSound neverV (neverV.join byteV) :=
    sound_of_not_satisfiable _ not_satisfiable_neverV _
  have hni : ¬ Includes byteV neverV := fun h => h (byteSeq 0) trivial
  exact ⟨not_satisfiable_neverV, hs, hni, fun h => hni (h.1 hs)⟩

/-- **R7 non-vacuity (mutable cast out of a meet).** `(T, U) = (zero-only, bool)`: the meet is
satisfiable, `U` is strictly larger than `T`, the meet removes nothing from `T`, and the
mutable cast is sound. -/
theorem mutSound_from_meet_nonvacuous :
    Satisfiable (zeroV.meet boolV) ∧ ¬ ValidityEq zeroV boolV ∧
      MutSound (zeroV.meet boolV) zeroV ∧ Includes zeroV boolV :=
  ⟨⟨byteSeq 0, zeroV_byteSeq_zero, boolV_byteSeq_zero⟩,
    fun h => not_zeroV_byteSeq_one ((h (byteSeq 1)).2 boolV_byteSeq_one),
    sound_of_validityEq _ (fun _ => ⟨And.left, fun hz => ⟨hz, Or.inl hz⟩⟩),
    fun _ hz => Or.inl hz⟩

/-- **R7 counterexample (mutable cast out of a meet): satisfiability of `T` and of `U` separately
does not replace satisfiability of the meet.** `(T, U) = (zero-only, two-only)`: both are
satisfiable, the meet is empty, the mutable cast out of it is (vacuously) sound, `T ⊄ U`. -/
theorem mutSound_from_meet_needs_joint_satisfiable :
    Satisfiable zeroV ∧ Satisfiable twoV ∧ ¬ Satisfiable (zeroV.meet twoV) ∧
      MutSound (zeroV.meet twoV) zeroV ∧ ¬ Includes zeroV twoV ∧
      ¬ (MutSound (zeroV.meet twoV) zeroV ↔ Includes zeroV twoV) := by
  have hns : ¬ Satisfiable (zeroV.meet twoV) := by
    rintro ⟨m, hm0, hm2⟩
    unfold zeroV at hm0
    unfold twoV at hm2
    rw [hm0] at hm2
    exact absurd hm2 (by decide)
  have hs : MutSound (zeroV.meet twoV) zeroV := sound_of_not_satisfiable _ hns _
  have hni : ¬ Includes zeroV twoV :=
    fun h => not_twoV_byteSeq_zero (h (byteSeq 0) zeroV_byteSeq_zero)
  exact ⟨⟨byteSeq 0, zeroV_byteSeq_zero⟩, ⟨byteSeq 2, twoV_byteSeq_two⟩,
    hns, hs, hni, fun h => hni (h.1 hs)⟩

/-- **R7 counterexample (mutable cast out of a meet, dropping satisfiability of the meet).** -/
theorem mutSound_from_meet_needs_satisfiable :
    ¬ Satisfiable (byteV.meet neverV) ∧ MutSound (byteV.meet neverV) byteV ∧
      ¬ Includes byteV neverV ∧
      ¬ (MutSound (byteV.meet neverV) byteV ↔ Includes byteV neverV) := by
  have hns : ¬ Satisfiable (byteV.meet neverV) := fun ⟨_, h⟩ => h.2
  have hs : MutSound (byteV.meet neverV) byteV := sound_of_not_satisfiable _ hns _
  have hni : ¬ Includes byteV neverV := fun h => h (byteSeq 0) trivial
  exact ⟨hns, hs, hni, fun h => hni (h.1 hs)⟩

/-- **R7 counterexample (mutable cast out of a meet, the conclusion's condition).** When
`T ⊆ U` fails (`bool` vs zero-only), the mutable cast `bool ⊓ zero → bool` is unsound even
though the meet is satisfiable: write `1` through the `bool` view, read at the meet. -/
theorem mutSound_from_meet_fails_example :
    Satisfiable (boolV.meet zeroV) ∧ ¬ Includes boolV zeroV ∧ ¬ MutSound (boolV.meet zeroV) boolV :=
  ⟨⟨byteSeq 0, meet_boolV_zeroV_zero⟩, fun h => not_zeroV_byteSeq_one (h _ boolV_byteSeq_one),
    not_sound_of_write_dst_read_src (mutProtocol_writeDstReadSrc (byteSeq 1)) (m := byteSeq 0)
      meet_boolV_zeroV_zero boolV_byteSeq_one not_meet_boolV_zeroV_one⟩

/-! ## Tightness of the generic witness lemmas -/

/-- The discipline that permits only the empty run (a test fixture). -/
def emptyProtocol {B : Type} {n : Nat} : Protocol B n := fun tr => tr = []

/-- Positive example: `emptyProtocol` permits the empty run. -/
theorem emptyProtocol_nil : (emptyProtocol : Protocol (Fin 256) 1) [] := rfl

/-- Negative example: `emptyProtocol` does not permit `readDst`. -/
theorem not_emptyProtocol_readDst : ¬ (emptyProtocol : Protocol (Fin 256) 1) readDst := by
  intro h; simp [emptyProtocol, readDst] at h

/-- `emptyProtocol` is sound for every pair of types. -/
theorem sound_emptyProtocol {B : Type} {n : Nat} (T U : Validity B n) :
    Sound emptyProtocol T U := by
  intro _ _ tr htr _
  subst htr
  trivial

/-- `not_sound_of_read_dst`, dropping the permission hypothesis: `byte → bool` with the byte
`2` satisfies the other hypotheses, and the discipline permitting only the empty run is
sound. -/
theorem not_sound_of_read_dst_needs_permission :
    ¬ (emptyProtocol : Protocol (Fin 256) 1) readDst ∧ byteV (byteSeq 2) ∧
      ¬ boolV (byteSeq 2) ∧ Sound emptyProtocol byteV boolV :=
  ⟨not_emptyProtocol_readDst, trivial, not_boolV_byteSeq_two, sound_emptyProtocol _ _⟩

/-- `not_sound_of_read_dst`, dropping the valid-initial-value hypothesis: with source `never`
and the byte `2`, the other hypotheses hold and the value transmute is (vacuously) sound. -/
theorem not_sound_of_read_dst_needs_valid_initial :
    (valueProtocol : Protocol (Fin 256) 1) readDst ∧ ¬ neverV (byteSeq 2) ∧
      ¬ boolV (byteSeq 2) ∧ ValueSound neverV boolV :=
  ⟨valueProtocol_readDst, id, not_boolV_byteSeq_two,
    sound_of_not_satisfiable _ not_satisfiable_neverV _⟩

/-- `not_sound_of_read_dst`, dropping the invalid-at-`U` hypothesis: `bool → bool` with the
byte `0`. -/
theorem not_sound_of_read_dst_needs_invalid :
    (valueProtocol : Protocol (Fin 256) 1) readDst ∧ boolV (byteSeq 0) ∧
      boolV (byteSeq 0) ∧ ValueSound boolV boolV :=
  ⟨valueProtocol_readDst, boolV_byteSeq_zero, boolV_byteSeq_zero, sound_refl _ _⟩

/-- `not_sound_of_write_dst_read_src`, dropping the permission hypothesis. -/
theorem not_sound_of_write_dst_read_src_needs_permission :
    ¬ (emptyProtocol : Protocol (Fin 256) 1) (writeDstReadSrc (byteSeq 2)) ∧
      boolV (byteSeq 0) ∧ byteV (byteSeq 2) ∧ ¬ boolV (byteSeq 2) ∧
      Sound emptyProtocol boolV byteV :=
  ⟨(fun h => by simp [emptyProtocol, writeDstReadSrc] at h), boolV_byteSeq_zero, trivial,
    not_boolV_byteSeq_two,
    sound_emptyProtocol _ _⟩

/-- `not_sound_of_write_dst_read_src`, dropping the valid-initial-value hypothesis: source
`never`, written value `2`. -/
theorem not_sound_of_write_dst_read_src_needs_valid_initial :
    (mutProtocol : Protocol (Fin 256) 1) (writeDstReadSrc (byteSeq 2)) ∧
      ¬ neverV (byteSeq 0) ∧ byteV (byteSeq 2) ∧ ¬ neverV (byteSeq 2) ∧ MutSound neverV byteV :=
  ⟨mutProtocol_writeDstReadSrc _, id, trivial, id,
    sound_of_not_satisfiable _ not_satisfiable_neverV _⟩

/-- `not_sound_of_write_dst_read_src`, dropping the written-value-valid-at-`U` hypothesis:
`bool → bool`, written value `2` (not `bool`-valid, hence not a well-typed write). -/
theorem not_sound_of_write_dst_read_src_needs_wellTyped_write :
    (mutProtocol : Protocol (Fin 256) 1) (writeDstReadSrc (byteSeq 2)) ∧
      boolV (byteSeq 0) ∧ ¬ boolV (byteSeq 2) ∧ ¬ boolV (byteSeq 2) ∧ MutSound boolV boolV :=
  ⟨mutProtocol_writeDstReadSrc _, boolV_byteSeq_zero, not_boolV_byteSeq_two,
    not_boolV_byteSeq_two, sound_refl _ _⟩

/-- `not_sound_of_write_dst_read_src`, dropping the written-value-invalid-at-`T` hypothesis:
`bool → bool`, written value `1`. -/
theorem not_sound_of_write_dst_read_src_needs_invalid :
    (mutProtocol : Protocol (Fin 256) 1) (writeDstReadSrc (byteSeq 1)) ∧
      boolV (byteSeq 0) ∧ boolV (byteSeq 1) ∧ boolV (byteSeq 1) ∧ MutSound boolV boolV :=
  ⟨mutProtocol_writeDstReadSrc _, boolV_byteSeq_zero, boolV_byteSeq_one, boolV_byteSeq_one,
    sound_refl _ _⟩

/-- Hypothesis witness for `not_sound_of_read_dst`: the value-transmute discipline permits
`readDst`, the byte `2` is a valid byte and not a valid `bool`. -/
theorem not_sound_of_read_dst_nonvacuous :
    (valueProtocol : Protocol (Fin 256) 1) readDst ∧ byteV (byteSeq 2) ∧ ¬ boolV (byteSeq 2) :=
  ⟨valueProtocol_readDst, trivial, not_boolV_byteSeq_two⟩

/-- Hypothesis witness for `not_sound_of_write_dst_read_src`: the mutable discipline permits
`writeDstReadSrc (byteSeq 2)`, `0` is a valid `bool`, `2` is a valid byte and not a valid
`bool`. -/
theorem not_sound_of_write_dst_read_src_nonvacuous :
    (mutProtocol : Protocol (Fin 256) 1) (writeDstReadSrc (byteSeq 2)) ∧
      boolV (byteSeq 0) ∧ byteV (byteSeq 2) ∧ ¬ boolV (byteSeq 2) :=
  ⟨mutProtocol_writeDstReadSrc (byteSeq 2), boolV_byteSeq_zero, trivial, not_boolV_byteSeq_two⟩

/-! ## Canonical tightness of the right-hand sides of R3 and R4 -/

/-- **R3 exact, tightness of the guard `Satisfiable T →`.** Without the guard the right-hand
side would read `T ⊆ U ∧ U ⊆ T`. For `never → byte` the mutable cast is (vacuously) sound and
`T ⊆ U` holds, but `U ⊆ T` fails, so the unguarded equivalence fails. -/
theorem mutSound_rhs_needs_satisfiable_guard :
    ¬ Satisfiable neverV ∧ MutSound neverV byteV ∧ Includes neverV byteV ∧
      ¬ Includes byteV neverV ∧
      ¬ (MutSound neverV byteV ↔ Includes neverV byteV ∧ Includes byteV neverV) := by
  have hs : MutSound neverV byteV := sound_of_not_satisfiable _ not_satisfiable_neverV _
  have hni : ¬ Includes byteV neverV := fun h => h (byteSeq 0) trivial
  exact ⟨not_satisfiable_neverV, hs, fun _ _ => trivial, hni, fun h => hni (h.1 hs).2⟩

/-- **R4 exact, tightness of the conjunct `Includes T U`**, for every pair of flags. For
`byte → bool` the other conjunct (`dstWrites = true → Satisfiable T → U ⊆ T`) holds,
`T ⊆ U` fails, and the cast is unsound, so the equivalence with only the other conjunct
fails. -/
theorem sharedIMSound_needs_includes_canonical (srcWrites dstWrites : Bool) :
    (dstWrites = true → Satisfiable byteV → Includes boolV byteV) ∧
      ¬ Includes byteV boolV ∧
      ¬ SharedIMSound srcWrites dstWrites byteV boolV ∧
      ¬ (SharedIMSound srcWrites dstWrites byteV boolV ↔
          (dstWrites = true → Satisfiable byteV → Includes boolV byteV)) := by
  have hother : dstWrites = true → Satisfiable byteV → Includes boolV byteV :=
    fun _ _ => includes_boolV_byteV
  have hns : ¬ SharedIMSound srcWrites dstWrites byteV boolV :=
    (sharedIMSound_needs_includes srcWrites dstWrites).2
  exact ⟨hother, not_includes_byteV_boolV, hns, fun h => hns (h.2 hother)⟩

/-- **R4 exact, tightness of the conjunct `dstWrites = true → Satisfiable T → U ⊆ T`**, for
either source flag (destination flag set). For `bool → byte`, `T ⊆ U` holds, `T` is
satisfiable, `U ⊆ T` fails, and the cast is unsound. -/
theorem sharedIMSound_needs_includes_rev_canonical (srcWrites : Bool) :
    Includes boolV byteV ∧ Satisfiable boolV ∧ ¬ Includes byteV boolV ∧
      ¬ SharedIMSound srcWrites true boolV byteV ∧
      ¬ (SharedIMSound srcWrites true boolV byteV ↔ Includes boolV byteV) :=
  ⟨includes_boolV_byteV, satisfiable_boolV, not_includes_byteV_boolV,
    not_sharedIMSound_dst_boolV_byteV srcWrites,
    fun h => not_sharedIMSound_dst_boolV_byteV srcWrites (h.2 includes_boolV_byteV)⟩

/-- **R4 exact, tightness of the guard `dstWrites = true →`**, for either source flag. Without
the guard the right-hand side would read `T ⊆ U ∧ (Satisfiable T → U ⊆ T)`; for `bool → byte`
without destination writes the cast is sound but that right-hand side is false. -/
theorem sharedIMSound_rhs_needs_dstWrites_guard (srcWrites : Bool) :
    SharedIMSound srcWrites false boolV byteV ∧
      ¬ (Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV)) ∧
      ¬ (SharedIMSound srcWrites false boolV byteV ↔
          Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV)) := by
  have hs : SharedIMSound srcWrites false boolV byteV :=
    sharedIMSound_of_invariant boolV (fun _ h => h) (fun _ h => h) includes_boolV_byteV
      (fun _ _ h => h) (fun h => Bool.noConfusion h)
  have hnrhs : ¬ (Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV)) :=
    fun h => not_includes_byteV_boolV (h.2 satisfiable_boolV)
  exact ⟨hs, hnrhs, fun h => hnrhs (h.1 hs)⟩

/-- **R4 exact, tightness of the guard `Satisfiable T →`**, for either source flag
(destination flag set). For `never → byte` the cast is (vacuously) sound but the unguarded
right-hand side is false. -/
theorem sharedIMSound_rhs_needs_satisfiable_guard (srcWrites : Bool) :
    ¬ Satisfiable neverV ∧
      SharedIMSound srcWrites true neverV byteV ∧
      ¬ (Includes neverV byteV ∧ (true = true → Includes byteV neverV)) ∧
      ¬ (SharedIMSound srcWrites true neverV byteV ↔
          Includes neverV byteV ∧ (true = true → Includes byteV neverV)) := by
  have hs : SharedIMSound srcWrites true neverV byteV :=
    sound_of_not_satisfiable _ not_satisfiable_neverV _
  have hnrhs : ¬ (Includes neverV byteV ∧ (true = true → Includes byteV neverV)) :=
    fun h => h.2 rfl (byteSeq 0) trivial
  exact ⟨not_satisfiable_neverV, hs, hnrhs, fun h => hnrhs (h.1 hs)⟩

/-! ## R5 symmetry is one-way -/

/-- `Satisfiable T` gives the one-way implication `MutSound T U → MutSound U T`, not the
biconditional: for `(T, U) = (byte, never)`, `byte` is satisfiable, `never → byte` is
(vacuously) sound, and `byte → never` is not. -/
theorem mutSound_not_iff_symm_of_satisfiable_left :
    Satisfiable byteV ∧ ¬ MutSound byteV neverV ∧ MutSound neverV byteV ∧
      ¬ (MutSound byteV neverV ↔ MutSound neverV byteV) := by
  have hsat : Satisfiable byteV := ⟨byteSeq 0, trivial⟩
  have hfwd : ¬ MutSound byteV neverV :=
    not_sound_of_read_dst mutProtocol_readDst (m := byteSeq 0) trivial id
  have hrev : MutSound neverV byteV := sound_of_not_satisfiable _ not_satisfiable_neverV _
  exact ⟨hsat, hfwd, hrev, fun h => hfwd (h.2 hrev)⟩

/-! ## R8. Casts checked once at cast time -/

/-- Some byte sequence (`0`) is valid both as a raw byte and as a `bool`. -/
theorem satisfiable_byteV_meet_boolV : Satisfiable (byteV.meet boolV) :=
  ⟨byteSeq 0, trivial, boolV_byteSeq_zero⟩

/-- Some byte sequence (`0`) is valid both as a `bool` and as a raw byte. -/
theorem satisfiable_boolV_meet_byteV : Satisfiable (boolV.meet byteV) :=
  ⟨byteSeq 0, boolV_byteSeq_zero, trivial⟩

/-- The zero-only and two-only types have no byte sequence in common. -/
theorem not_satisfiable_zeroV_meet_twoV : ¬ Satisfiable (zeroV.meet twoV) := by
  rintro ⟨m, hm0, hm2⟩
  unfold zeroV at hm0
  unfold twoV at hm2
  rw [hm0] at hm2
  exact absurd hm2 (by decide)

/-- **R8 (value), non-vacuity and contrast with R1.** For `byte → bool`, some contents pass the
check, the checked value transmute is sound, and the unchecked one is not. -/
theorem checkedSound_valueProtocol_nonvacuous :
    Satisfiable (byteV.meet boolV) ∧ CheckedSound valueProtocol byteV boolV ∧
      ¬ ValueSound byteV boolV :=
  ⟨satisfiable_byteV_meet_boolV,
    checkedSound_value_of_invariant boolV (fun _ _ h => h) (fun _ h => h) (fun _ h => h),
    not_valueSound_byteV_boolV⟩

/-- **R8 (shared), non-vacuity and contrast with R2.** For `byte → bool`, some contents pass
the check, the checked shared cast is sound, and the unchecked one is not. -/
theorem checkedSound_sharedProtocol_nonvacuous :
    Satisfiable (byteV.meet boolV) ∧ CheckedSound sharedProtocol byteV boolV ∧
      ¬ SharedSound byteV boolV :=
  ⟨satisfiable_byteV_meet_boolV,
    checkedSound_shared_of_invariant boolV (fun _ _ h => h) (fun _ _ => trivial) (fun _ h => h),
    not_sharedSound_byteV_boolV⟩

/-- **R8 (mutable), non-vacuity.** Both sides true for `byte → bool` (the meet is satisfiable,
`bool ⊆ byte`, the checked cast is sound); both sides false for `bool → byte` (the meet is
satisfiable, `byte ⊄ bool`, the checked cast is unsound). -/
theorem checkedSound_mut_nonvacuous :
    (Satisfiable (byteV.meet boolV) ∧ CheckedSound mutProtocol byteV boolV ∧
        Includes boolV byteV) ∧
      (Satisfiable (boolV.meet byteV) ∧ ¬ CheckedSound mutProtocol boolV byteV ∧
        ¬ Includes byteV boolV) :=
  ⟨⟨satisfiable_byteV_meet_boolV, checkedSound_mut_byteV_boolV, includes_boolV_byteV⟩,
    ⟨satisfiable_boolV_meet_byteV, not_checkedSound_mut_boolV_byteV,
      not_includes_byteV_boolV⟩⟩

/-- **R8 (mutable), tightness of the right-hand side `Includes U T`.** A check at cast time does
not remove the write-side requirement: for `bool → byte` the meet is satisfiable,
`byte ⊄ bool`, and the checked mutable cast is unsound. -/
theorem checkedSound_mut_needs_includes_rev :
    Satisfiable (boolV.meet byteV) ∧ ¬ Includes byteV boolV ∧
      ¬ CheckedSound mutProtocol boolV byteV :=
  ⟨satisfiable_boolV_meet_byteV, not_includes_byteV_boolV, not_checkedSound_mut_boolV_byteV⟩

/-- **R8 (mutable), tightness of the guard `Satisfiable (T ⊓ U) →`.** For
`(T, U) = (zero-only, two-only)` both types are satisfiable but the check never succeeds, so
the checked cast is vacuously sound although `U ⊄ T`. The guard can therefore be neither
dropped nor weakened to satisfiability of `T` (or of `T` and `U` separately). -/
theorem checkedSound_mut_rhs_needs_satisfiable_meet_guard :
    Satisfiable zeroV ∧ Satisfiable twoV ∧ ¬ Satisfiable (zeroV.meet twoV) ∧
      CheckedSound mutProtocol zeroV twoV ∧ ¬ Includes twoV zeroV ∧
      ¬ (CheckedSound mutProtocol zeroV twoV ↔ Includes twoV zeroV) := by
  have hs : CheckedSound mutProtocol zeroV twoV :=
    checkedSound_of_not_satisfiable_meet _ not_satisfiable_zeroV_meet_twoV
  have hni : ¬ Includes twoV zeroV := by
    intro h
    have hz : zeroV (byteSeq 2) := h (byteSeq 2) twoV_byteSeq_two
    unfold zeroV byteSeq at hz
    exact absurd hz (by decide)
  exact ⟨⟨byteSeq 0, zeroV_byteSeq_zero⟩, ⟨byteSeq 2, twoV_byteSeq_two⟩,
    not_satisfiable_zeroV_meet_twoV, hs, hni, fun h => hni (h.1 hs)⟩

/-- **R3 impossibility form, positive control (checking at cast time).** For `byte → bool`,
`byte` is satisfiable and the validities differ, so the unchecked mutable cast is unsound
(R3-imp), but the same cast checked once at cast time is sound. -/
theorem checkedSound_mut_escapes_impossibility :
    Satisfiable byteV ∧ ¬ ValidityEq byteV boolV ∧ ¬ MutSound byteV boolV ∧
      CheckedSound mutProtocol byteV boolV :=
  ⟨⟨byteSeq 0, trivial⟩, fun h => not_boolV_byteSeq_two ((h (byteSeq 2)).1 trivial),
    not_mutSound_byteV_boolV, checkedSound_mut_byteV_boolV⟩

/-- **R8 (interior mutability), non-vacuity.** Both sides true: both flags with
`bool → bool'`; destination-only writes with `byte → bool`; source-only writes with
`bool → byte`. Both sides false: source-only writes with `byte → bool`. -/
theorem checkedSound_sharedIM_nonvacuous :
    (CheckedSound (sharedIMProtocol true true) boolV boolV' ∧ Includes boolV boolV' ∧
        Includes boolV' boolV) ∧
      (CheckedSound (sharedIMProtocol false true) byteV boolV ∧ Includes boolV byteV) ∧
      (CheckedSound (sharedIMProtocol true false) boolV byteV ∧ Includes boolV byteV) ∧
      (Satisfiable (byteV.meet boolV) ∧
        ¬ CheckedSound (sharedIMProtocol true false) byteV boolV ∧ ¬ Includes byteV boolV) :=
  ⟨⟨checkedSound_of_sound (sharedIMSound_boolV_boolV' true true),
      fun m => (validityEq_boolV_boolV' m).1, fun m => (validityEq_boolV_boolV' m).2⟩,
    ⟨checkedSound_sharedIM_of_invariant boolV (fun _ _ h => h) (fun _ _ => trivial)
        (fun _ h => h) (fun h => Bool.noConfusion h) (fun _ _ h => h),
      includes_boolV_byteV⟩,
    ⟨checkedSound_of_sound sharedIMSound_true_false_boolV_byteV, includes_boolV_byteV⟩,
    ⟨satisfiable_byteV_meet_boolV,
      not_checkedSound_of_write_src_read_dst (sharedIMProtocol_writeSrcReadDst false (byteSeq 2))
        (m := byteSeq 0) trivial boolV_byteSeq_zero trivial not_boolV_byteSeq_two,
      not_includes_byteV_boolV⟩⟩

/-- **R8 (interior mutability), tightness of `srcWrites = true → Includes T U`.** With both
flags set, for `byte → bool` the meet is satisfiable, the other conjunct (`bool ⊆ byte`)
holds, `byte ⊄ bool`, and the checked cast is unsound: write `2` through the byte view after
the check, then read the `bool`. -/
theorem checkedSound_sharedIM_needs_srcWrites_includes :
    Satisfiable (byteV.meet boolV) ∧ Includes boolV byteV ∧ ¬ Includes byteV boolV ∧
      ¬ CheckedSound (sharedIMProtocol true true) byteV boolV :=
  ⟨satisfiable_byteV_meet_boolV, includes_boolV_byteV, not_includes_byteV_boolV,
    not_checkedSound_of_write_src_read_dst (sharedIMProtocol_writeSrcReadDst true (byteSeq 2))
      (m := byteSeq 0) trivial boolV_byteSeq_zero trivial not_boolV_byteSeq_two⟩

/-- **R8 (interior mutability), tightness of `dstWrites = true → Includes U T`.** With both
flags set, for `bool → byte` the meet is satisfiable, the other conjunct (`bool ⊆ byte`)
holds, `byte ⊄ bool`, and the checked cast is unsound. -/
theorem checkedSound_sharedIM_needs_dstWrites_includes_rev :
    Satisfiable (boolV.meet byteV) ∧ Includes boolV byteV ∧ ¬ Includes byteV boolV ∧
      ¬ CheckedSound (sharedIMProtocol true true) boolV byteV :=
  ⟨satisfiable_boolV_meet_byteV, includes_boolV_byteV, not_includes_byteV_boolV,
    not_checkedSound_of_write_dst_read_src (sharedIMProtocol_writeDstReadSrc true (byteSeq 2))
      (m := byteSeq 0) boolV_byteSeq_zero trivial trivial not_boolV_byteSeq_two⟩

/-- **R8 (interior mutability), tightness of the guard `Satisfiable (T ⊓ U) →`.** With both
flags set, for `(T, U) = (zero-only, two-only)` both types are satisfiable, the check never
succeeds, the checked cast is vacuously sound, and the unguarded right-hand side is false. -/
theorem checkedSound_sharedIM_rhs_needs_satisfiable_meet_guard :
    Satisfiable zeroV ∧ Satisfiable twoV ∧ ¬ Satisfiable (zeroV.meet twoV) ∧
      CheckedSound (sharedIMProtocol true true) zeroV twoV ∧
      ¬ ((true = true → Includes zeroV twoV) ∧ (true = true → Includes twoV zeroV)) := by
  have hs : CheckedSound (sharedIMProtocol true true) zeroV twoV :=
    checkedSound_of_not_satisfiable_meet _ not_satisfiable_zeroV_meet_twoV
  have hni : ¬ Includes zeroV twoV :=
    fun h => not_twoV_byteSeq_zero (h (byteSeq 0) zeroV_byteSeq_zero)
  exact ⟨⟨byteSeq 0, zeroV_byteSeq_zero⟩, ⟨byteSeq 2, twoV_byteSeq_two⟩,
    not_satisfiable_zeroV_meet_twoV, hs, fun h => hni (h.1 rfl)⟩

/-- **R8 (interior mutability), tightness of the inner guard `srcWrites = true →`.** Without
the guard the right-hand side would read `Satisfiable (T ⊓ U) → T ⊆ U ∧ (dstWrites = true →
U ⊆ T)`. For `byte → bool` with only the destination side writable, the meet is satisfiable,
`bool ⊆ byte`, and the checked cast is sound, but `byte ⊄ bool`, so that right-hand side is
false and the unguarded equivalence fails. -/
theorem checkedSound_sharedIM_rhs_needs_srcWrites_guard :
    CheckedSound (sharedIMProtocol false true) byteV boolV ∧
      Satisfiable (byteV.meet boolV) ∧ Includes boolV byteV ∧ ¬ Includes byteV boolV ∧
      ¬ (Satisfiable (byteV.meet boolV) →
          Includes byteV boolV ∧ (true = true → Includes boolV byteV)) ∧
      ¬ (CheckedSound (sharedIMProtocol false true) byteV boolV ↔
          (Satisfiable (byteV.meet boolV) →
            Includes byteV boolV ∧ (true = true → Includes boolV byteV))) := by
  have hs : CheckedSound (sharedIMProtocol false true) byteV boolV :=
    checkedSound_sharedIM_of_invariant boolV (fun _ _ h => h) (fun _ _ => trivial)
      (fun _ h => h) (fun h => Bool.noConfusion h) (fun _ _ h => h)
  have hnrhs : ¬ (Satisfiable (byteV.meet boolV) →
      Includes byteV boolV ∧ (true = true → Includes boolV byteV)) :=
    fun h => not_includes_byteV_boolV (h satisfiable_byteV_meet_boolV).1
  exact ⟨hs, satisfiable_byteV_meet_boolV, includes_boolV_byteV, not_includes_byteV_boolV,
    hnrhs, fun h => hnrhs (h.1 hs)⟩

/-- **R8 (interior mutability), tightness of the inner guard `dstWrites = true →`.** Without
the guard the right-hand side would read `Satisfiable (T ⊓ U) → (srcWrites = true → T ⊆ U) ∧
U ⊆ T`. For `bool → byte` with only the source side writable, the meet is satisfiable,
`bool ⊆ byte`, and the checked cast is sound, but `byte ⊄ bool`, so that right-hand side is
false and the unguarded equivalence fails. -/
theorem checkedSound_sharedIM_rhs_needs_dstWrites_guard :
    CheckedSound (sharedIMProtocol true false) boolV byteV ∧
      Satisfiable (boolV.meet byteV) ∧ Includes boolV byteV ∧ ¬ Includes byteV boolV ∧
      ¬ (Satisfiable (boolV.meet byteV) →
          (true = true → Includes boolV byteV) ∧ Includes byteV boolV) ∧
      ¬ (CheckedSound (sharedIMProtocol true false) boolV byteV ↔
          (Satisfiable (boolV.meet byteV) →
            (true = true → Includes boolV byteV) ∧ Includes byteV boolV)) := by
  have hs : CheckedSound (sharedIMProtocol true false) boolV byteV :=
    checkedSound_of_sound sharedIMSound_true_false_boolV_byteV
  have hnrhs : ¬ (Satisfiable (boolV.meet byteV) →
      (true = true → Includes boolV byteV) ∧ Includes byteV boolV) :=
    fun h => not_includes_byteV_boolV (h satisfiable_boolV_meet_byteV).2
  exact ⟨hs, satisfiable_boolV_meet_byteV, includes_boolV_byteV, not_includes_byteV_boolV,
    hnrhs, fun h => hnrhs (h.1 hs)⟩

end Toy.Transmute
