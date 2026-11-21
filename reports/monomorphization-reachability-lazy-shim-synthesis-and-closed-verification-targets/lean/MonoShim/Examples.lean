import MonoShim.Termination

/-!
# Positive and negative examples for the core definitions
-/

namespace Toy.MonoShim

/-! ## Keys and types -/

theorem isShim_pos_example : (Key.dropGlue (.base 0)).isShim = true ∧
    (Key.reifyShim 1 []).isShim = true := by decide
theorem isShim_neg_example : (Key.inst 0 []).isShim = false ∧ (Key.userDrop 0).isShim = false := by
  decide

/-- Normalization replaces a projection that has an `assoc` entry and keeps one that has none. -/
theorem norm_pos_example : (Key.inst 2 [.proj 0 (.base 0)]).norm P6 = .inst 2 [.base 1] := by decide
theorem norm_neg_example : (Key.inst 2 [.proj 1 (.base 0)]).norm P6 = .inst 2 [.proj 1 (.base 0)] ∧
    (Key.inst 2 [.proj 0 (.base 7)]).norm P6 = .inst 2 [.proj 0 (.base 7)] := by decide

theorem cloneKey_examples : cloneKey (.base 3) = .userClone 3 ∧
    cloneKey (.pair (.base 0) (.base 1)) = .cloneShim (.pair (.base 0) (.base 1)) := by decide

theorem reifyKey_examples : reifyKey P2d.sig 1 [] = .reifyShim 1 [] ∧
    reifyKey P2c.sig 1 [] = .inst 1 [] := by decide

/-! ## Runtime references -/

/-- Unsizing references every trait method at the type, plus the type's drop glue. -/
theorem refs_pos_example :
    refs P2b.sig (.unsize 0 (.base 2) 0) = [.meth 0 0 (.base 2), .dropGlue (.base 2)] ∧
    refs P2a.sig (.onUnwind (.call 1 []) (.drop (.base 1))) = [.inst 1 [], .dropGlue (.base 1)] := by
  decide
/-- Calls through a pointer or a trait object reference nothing statically: their targets were
recorded where the pointer or vtable was created. -/
theorem refs_neg_example : refs P2b.sig (.callDyn 0 0) = [] ∧ refs P2c.sig (.callPtr 0) = [] := by
  decide

/-! ## Source semantics and the synthesizer -/

/-- Source drop glue for a pair drops the fields in declaration order, with the second field also
dropped on the unwind path of the first. -/
theorem glueSrc_pos_example :
    glueSrc P4a (.pair (.base 0) (.base 1)) =
      some (.seq (.onUnwind (.drop (.base 0)) (.drop (.base 1))) (.drop (.base 1))) := by
  decide

/-- `base 0`'s destructor panics and `base 1`'s emits 20; `main` drops a `pair (base 0) (base 1)`. -/
def PdropUnwind : Program where
  fns := [⟨false, .drop (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .panic), (1, .emit 20)]
  cloneImpls := []
  assoc := []

/-- As `PdropUnwind`, but `base 1`'s destructor panics as well. -/
def PdropAbort : Program where
  fns := [⟨false, .drop (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .panic), (1, .panic)]
  cloneImpls := []
  assoc := []

/-- If dropping the first field unwinds, the second field is still dropped (event 20) and the
drop keeps unwinding; if that cleanup drop panics too, the run aborts. -/
theorem glue_pair_unwind_drops_remaining_field_example :
    runS PdropUnwind 4 (.inst 0 []) st0 = (.unwind, ⟨[20], 0⟩) ∧
    runS PdropAbort 4 (.inst 0 []) st0 = (.abort, st0) := by
  decide
/-- Trait objects, parameters and projections have no glue of their own. -/
theorem glueSrc_neg_example : glueSrc P4a (.dyn 0) = none ∧ glueSrc P4a (.param 0) = none ∧
    glueSrc P4a (.proj 0 (.base 0)) = none := by decide

theorem srcDef_pos_example : srcDef P6 (.inst 2 [.proj 0 (.base 0)]) = some (.emit 9) ∧
    srcDef P6 (.inst 1 [.base 0]) = some (.call 2 [.base 1]) := by decide
theorem srcDef_neg_example : srcDef P6 (.inst 7 []) = none := by decide

theorem synthStd_pos_example :
    synthStd P3 (.cloneShim (.pair (.base 0) (.base 1))) = some (ladder [.base 0, .base 1]) := by
  decide
theorem synthStd_neg_example : synthStd P3 (.cloneShim (.base 0)) = none ∧
    synthStd P3 (.inst 0 []) = none := by decide

theorem ladder_shape_example : ladder [.base 0, .base 1] =
    .seq (.clone (.base 0)) (.onUnwind (.seq (.clone (.base 1)) (.onUnwind .skip (.drop (.base 1))))
      (.drop (.base 0))) := rfl

/-! ## Collection -/

theorem reach_pos_example : Reach (edgesM P2a (stdCfg P2a)) [.inst 0 []] (.userDrop 1) :=
  (collect_mem_iff_reach _ fifo fifo_ok _ 10 _ full_edges_close_missing_edge_examples.1 _).mp
    (by decide)
theorem reach_neg_example : ¬ Reach (edgesM P2a (stdCfg P2a)) [.inst 0 []] (.inst 5 []) := by
  intro h
  have := (collect_mem_iff_reach _ fifo fifo_ok _ 10 _ full_edges_close_missing_edge_examples.1 _).mpr h
  revert this; decide

theorem schedOK_pos_example : SchedOK fifo ∧ SchedOK lifo := ⟨fifo_ok, lifo_ok⟩
/-- A scheduler that discards newly found keys is not admissible. -/
theorem schedOK_neg_example : ¬ SchedOK (fun w _ => w) := by
  intro h
  have := (h [] [.inst 0 []] (.inst 0 [])).mpr (Or.inr (by simp))
  simp at this

theorem edgesIn_examples : EdgesIn (edgesM P2c (stdCfg P2c)) [.inst 1 [], .inst 0 []] ∧
    ¬ EdgesIn (edgesM P2c (stdCfg P2c)) [.inst 0 []] := by decide

theorem rootsIn_examples : RootsIn [.inst 0 []] [.inst 1 [], .inst 0 []] ∧
    ¬ RootsIn [.inst 0 []] [.inst 1 []] := by decide

theorem closed_examples :
    Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 1 [], .inst 0 []]) [.inst 1 [], .inst 0 []] ∧
    ¬ Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) [.inst 0 []] := by decide

/-! ## Hypotheses -/

theorem coversRefs_pos_example (P : Program) : CoversRefs P.sig (refs P.sig) := fun _ _ h => h
theorem coversRefs_neg_example : ¬ CoversRefs P2a.sig (refsNoCleanup P2a.sig) :=
  cleanup_edges_missing_break_closure.1

theorem bodyEquiv_pos_example (sig : Sig) : BodyEquiv sig (ladder [.base 0, .base 1])
    (.cloneAgg [.base 0, .base 1]) := ladder_bodyEquiv_cloneAgg sig _
theorem bodyEquiv_neg_example :
    ¬ BodyEquiv P3.sig (ladderNoCleanup [.base 0, .base 1]) (.cloneAgg [.base 0, .base 1]) := by
  intro h
  have := h (runKey P3.sig (srcDef P3) 5) st0
  revert this; decide

theorem synthAgrees_pos_example : SynthAgrees P4a (stdCfg P4a) T4a := synthStd_agrees P4a T4a
theorem synthAgrees_neg_example : ¬ SynthAgrees P4a (cfgRev P4a) T4a :=
  synth_disagreement_breaks_adequacy.2.2.2.1

theorem canonical_pos_example : CanonicalKeys P6 T6 ∧ CanonicalRefs P6 (stdCfg P6) T6 := by decide
theorem canonical_neg_example : ¬ CanonicalRefs P6chain (stdCfg P6chain) T6 ∧
    ¬ CanonicalKeys Pnc [.dropGlue (.proj 0 (.base 0))] := by decide

/-- A table whose outputs are normal passes `assocNormal`; a chained or self-referential table
does not, and on the chained table one normalization pass is not idempotent. -/
theorem assocNormal_examples :
    assocNormal P6 = true ∧ assocNormal P6chain = false ∧ assocNormal P9assoc = false ∧
    (Ty.proj 0 (.base 0)).norm P6chain.assoc = .proj 1 (.base 0) ∧
    ((Ty.proj 0 (.base 0)).norm P6chain.assoc).norm P6chain.assoc = .base 1 := by
  decide

theorem instDefined_examples : InstDefined P2c [.inst 1 [], .inst 0 []] ∧
    ¬ InstDefined Pundef [.inst 5 [], .inst 0 []] := by decide

theorem synthTotal_examples : SynthTotal (stdCfg P2a) [.dropGlue (.base 1)] ∧
    ¬ SynthTotal (cfgNoSynth P2a) [.dropGlue (.base 1)] := by decide

/-! ## Specifications -/

theorem verifiedBody_pos_example : VerifiedBody P4b.sig Q4b (.emit 1) (appends [1]) :=
  verified_emit _ _ 1
/-- A body emitting 2 does not verify against "emits exactly 1". -/
theorem verifiedBody_neg_example : ¬ VerifiedBody P4b.sig Q4b (.emit 2) (appends [1]) := by
  intro h
  have := h (fun _ st => (.ok, st)) (by simp [refs]) st0
  simp [SatOut, appends, execS, st0] at this

theorem specs_pos_example : GenericVerified P4b Q4b ∧ ImplsConform P4a Q4a T4a ∧
    SynthVerified P4a (stdCfg P4a) Q4a T4a :=
  ⟨P4b_generic_verified, P4a_impls_conform, P4a_synthStd_verified⟩
theorem specs_neg_example : ¬ ImplsConform P4b Q4b T4b ∧ ¬ SynthVerified P4a (cfgRev P4a) Q4a T4a :=
  ⟨generic_verified_wrong_at_nonconforming_impl.2.2.2.2.1,
    source_defs_verified_yet_program_violates_spec_under_reverse_glue.2.2.2.1⟩

/-- A generic body that ignores the trait spec is not generically verified. -/
def P4bad : Program where
  fns := [⟨false, .emit 2⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

theorem genericVerified_neg_example : ¬ GenericVerified P4bad Q4b := by
  intro h
  have := h 0 ⟨false, .emit 2⟩ [] rfl (fun _ st => (.ok, st)) (by simp [Stmt.subst, Stmt.norm, refs]) st0
  simp [SatOut, Q4b, appends, execS, Stmt.subst, Stmt.norm, st0] at this

theorem meetsAt_examples :
    MeetsAt P4a.sig (tableM P4a (stdCfg P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) ∧
    ¬ MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) :=
  ⟨P4a_std_meets_specs.2.2.2.2 _ (by simp [T4a]),
    source_defs_verified_yet_program_violates_spec_under_reverse_glue.2.2.2.2.2.1⟩

theorem deterministicUnits_examples :
    DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthStd P4a)] ∧
    ¬ DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthRev P4a)] :=
  ⟨deterministic_units_example.1, nondeterministic_units_link_order_matters.1⟩

theorem rankCheck_examples : rankCheck P5ok rank5ok = true ∧ rankCheck P5 rank5ok = false :=
  ⟨P5ok_rankCheck_and_collects.1, P5_fails_rankCheck _⟩

/-- `Ty.grows`: a bare parameter and a closed type do not grow; a parameter under `box`, `pair`
or `proj` does. -/
theorem grows_examples :
    Ty.grows (.param 0) = false ∧ Ty.grows (.base 3) = false ∧ Ty.grows (.box (.param 0)) = true ∧
    Ty.grows (.pair (.base 0) (.param 1)) = true ∧ Ty.grows (.proj 0 (.param 0)) = true := by
  decide

end Toy.MonoShim
