import MonoShim.MoreTightness

/-!
# Spec transfer to the source semantics: tightness and non-vacuity

Witnesses for the six hypotheses of `closed_target_meets_specs_in_source_semantics`. Each
tightness witness states that the other five hypotheses hold, that the targeted one fails, and that
the conclusion (every key of the target meets its spec in the source resolver `srcDef`) fails.
-/

namespace Toy.MonoShim

/-- Specs demanding "free before release": `main` and the pair's glue must emit `[20, 10]`. -/
def Q4aRev : Key → Spec
  | .inst 0 [] => appends [20, 10]
  | .dropGlue (.pair (.base 0) (.base 1)) => appends [20, 10]
  | .dropGlue (.base 0) => appends [10]
  | .dropGlue (.base 1) => appends [20]
  | .userDrop 0 => appends [10]
  | .userDrop 1 => appends [20]
  | _ => fun _ _ => True

theorem P4a_generic_verified_rev : GenericVerified P4a Q4aRev := by
  intro f fd τs h
  match f, h with
  | 0, h =>
    have e : P4a.fns[0]? = some ⟨false, .drop (.pair (.base 0) (.base 1))⟩ := rfl
    rw [e] at h; cases h
    cases τs with
    | nil =>
      exact verified_single_call _ _ [20, 10] (.dropGlue (.pair (.base 0) (.base 1))) _
        (fun _ _ _ => rfl) (by decide) rfl
    | cons _ _ => intro _ _ _; right; trivial

theorem P4a_impls_conform_rev : ImplsConform P4a Q4aRev T4a := by
  intro k hk hi b hb
  simp [T4a] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Key.isImpl] at hi
  · have e : srcDef0 P4a (.userDrop 1) = some (.emit 20) := rfl
    rw [e] at hb; simp at hb; subst hb; exact verified_emit _ _ 20
  · have e : srcDef0 P4a (.userDrop 0) = some (.emit 10) := rfl
    rw [e] at hb; simp at hb; subst hb; exact verified_emit _ _ 10

theorem P4a_synthRev_verified_rev : SynthVerified P4a (cfgRev P4a) Q4aRev T4a := by
  intro k hk hs b hb
  simp [T4a] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Key.isShim] at hs
  · have e : (cfgRev P4a).synth (.dropGlue (.base 1)) = some (.invoke (.userDrop 1)) := rfl
    rw [e] at hb; simp at hb; subst hb
    exact verified_single_call _ _ _ (.userDrop 1) _ (fun _ _ _ => rfl) (by simp [refs]) rfl
  · have e : (cfgRev P4a).synth (.dropGlue (.base 0)) = some (.invoke (.userDrop 0)) := rfl
    rw [e] at hb; simp at hb; subst hb
    exact verified_single_call _ _ _ (.userDrop 0) _ (fun _ _ _ => rfl) (by simp [refs]) rfl
  · have e : (cfgRev P4a).synth (.dropGlue (.pair (.base 0) (.base 1))) =
        some (.seq (.onUnwind (.drop (.base 1)) (.drop (.base 0))) (.drop (.base 0))) := rfl
    rw [e] at hb; simp at hb; subst hb
    exact verified_glue_pair _ _ (.base 1) (.base 0) [20] [10] rfl rfl

/-- In the source semantics `main` of `P4a` emits "release" (10) before "free" (20). -/
theorem P4a_runS_main : runKey P4a.sig (srcDef P4a) 4 (.inst 0 []) st0 = (.ok, ⟨[10, 20], 0⟩) := by
  decide

theorem P4a_main_violates_Q4aRev_in_source :
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
  intro h
  have h0 := h (.inst 0 []) (by simp [T4a]) 4 st0
  rw [P4a_runS_main] at h0
  simp [SatOut, Q4aRev, appends, st0] at h0

/-- **Non-vacuity of the source-transfer theorem.** On `P4a` with the standard configuration and
the specs `Q4a`, all six hypotheses of `closed_target_meets_specs_in_source_semantics` hold, and
every key of `T4a` meets its spec in the source semantics. -/
theorem P4a_std_meets_specs_in_source_semantics :
    Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a ∧
    GenericVerified P4a Q4a ∧ ImplsConform P4a Q4a T4a ∧
    SynthVerified P4a (stdCfg P4a) Q4a T4a ∧
    SynthAgrees P4a (stdCfg P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    ∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4a k) k := by
  have hC : Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a := by decide
  have h2 : SynthAgrees P4a (stdCfg P4a) T4a := synthStd_agrees P4a T4a
  have h3a : CanonicalKeys P4a T4a := by decide
  exact ⟨hC, P4a_generic_verified, P4a_impls_conform, P4a_synthStd_verified, h2, h3a,
    closed_target_meets_specs_in_source_semantics P4a (stdCfg P4a) T4a Q4a
      hC P4a_generic_verified P4a_impls_conform P4a_synthStd_verified h2 h3a⟩

/-- **Tightness of closedness for the source-transfer theorem.** On `P4a` with the standard
configuration, the specs `Q4aRev` and the target `[main]`, generic verification, impl conformance,
synthesizer verification, (H2) and (H3a) hold (the last four vacuously or trivially, since `main`
is neither an impl nor a shim key), the target is not closed, and `main` violates its spec in the
source semantics (it emits `[10, 20]`). -/
theorem nonclosed_target_breaks_source_transfer :
    ¬ Closed P4a.sig (tableM P4a (stdCfg P4a) [.inst 0 []]) [.inst 0 []] ∧
    GenericVerified P4a Q4aRev ∧ ImplsConform P4a Q4aRev [.inst 0 []] ∧
    SynthVerified P4a (stdCfg P4a) Q4aRev [.inst 0 []] ∧
    SynthAgrees P4a (stdCfg P4a) [.inst 0 []] ∧ CanonicalKeys P4a [.inst 0 []] ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
  refine ⟨by decide, P4a_generic_verified_rev, ?_, ?_, synthStd_agrees P4a _, by decide, ?_⟩
  · intro k hk hi; simp at hk; subst hk; simp [Key.isImpl] at hi
  · intro k hk hs; simp at hk; subst hk; simp [Key.isShim] at hs
  · intro h
    have h0 := h (.inst 0 []) (by simp) 4 st0
    rw [P4a_runS_main] at h0
    simp [SatOut, Q4aRev, appends, st0] at h0

/-- **Tightness of generic verification for the source-transfer theorem.** `P4bad`'s generic body
ignores its spec; the target `[main]` is closed, impl conformance, synthesizer verification, (H2)
and (H3a) hold, and `main` violates its spec in the source semantics (it emits `[2]`). -/
theorem unverified_generic_body_breaks_source_transfer :
    Closed P4bad.sig (tableM P4bad (stdCfg P4bad) [.inst 0 []]) [.inst 0 []] ∧
    ¬ GenericVerified P4bad Q4b ∧ ImplsConform P4bad Q4b [.inst 0 []] ∧
    SynthVerified P4bad (stdCfg P4bad) Q4b [.inst 0 []] ∧
    SynthAgrees P4bad (stdCfg P4bad) [.inst 0 []] ∧ CanonicalKeys P4bad [.inst 0 []] ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P4bad.sig (srcDef P4bad) (Q4b k) k) := by
  obtain ⟨hC, hG, hI, hS, _, _⟩ := unverified_generic_body_breaks_spec_transfer
  refine ⟨hC, hG, hI, hS, synthStd_agrees P4bad _, by decide, ?_⟩
  intro h
  have h0 := h (.inst 0 []) (by simp) 2 st0
  have hrun : runKey P4bad.sig (srcDef P4bad) 2 (.inst 0 []) st0 = (.ok, ⟨[2], 0⟩) := by decide
  rw [hrun] at h0
  simp [SatOut, Q4b, appends, st0] at h0

/-- **Tightness of impl conformance for the source-transfer theorem.** On `P4b` at `base 1` the
target is closed, the generic body is verified, the synthesizer is (vacuously) verified, (H2) and
(H3a) hold, the impl for `base 1` violates the trait-method spec, and the instance violates its
spec in the source semantics (it emits `[2]`). -/
theorem nonconforming_impl_breaks_source_transfer :
    Closed P4b.sig (tableM P4b (stdCfg P4b) T4b) T4b ∧ GenericVerified P4b Q4b ∧
    ¬ ImplsConform P4b Q4b T4b ∧ SynthVerified P4b (stdCfg P4b) Q4b T4b ∧
    SynthAgrees P4b (stdCfg P4b) T4b ∧ CanonicalKeys P4b T4b ∧
    ¬ (∀ k ∈ T4b, MeetsAt P4b.sig (srcDef P4b) (Q4b k) k) := by
  obtain ⟨_, hC, hG, hS, hI, _⟩ := generic_verified_wrong_at_nonconforming_impl
  refine ⟨hC, hG, hI, hS, synthStd_agrees P4b _, by decide, ?_⟩
  intro h
  have h0 := h (.inst 0 [.base 1]) (by simp [T4b]) 2 st0
  have hrun : runKey P4b.sig (srcDef P4b) 2 (.inst 0 [.base 1]) st0 = (.ok, ⟨[2], 0⟩) := by
    decide
  rw [hrun] at h0
  simp [SatOut, Q4b, appends, st0] at h0

/-- **Tightness of synthesizer verification for the source-transfer theorem.** On `P4a` with the
standard configuration and the specs `Q4aRev`, the target is closed, generic verification, impl
conformance, (H2) and (H3a) hold, the standard glue for the pair does not verify against the
"free before release" spec, and `main` violates its spec in the source semantics. -/
theorem unverified_synth_breaks_source_transfer :
    Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a ∧ GenericVerified P4a Q4aRev ∧
    ImplsConform P4a Q4aRev T4a ∧ ¬ SynthVerified P4a (stdCfg P4a) Q4aRev T4a ∧
    SynthAgrees P4a (stdCfg P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
  have hC : Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a := by decide
  have h2 : SynthAgrees P4a (stdCfg P4a) T4a := synthStd_agrees P4a T4a
  have h3a : CanonicalKeys P4a T4a := by decide
  refine ⟨hC, P4a_generic_verified_rev, P4a_impls_conform_rev, ?_, h2, h3a,
    P4a_main_violates_Q4aRev_in_source⟩
  intro hS
  exact P4a_main_violates_Q4aRev_in_source
    (closed_target_meets_specs_in_source_semantics P4a (stdCfg P4a) T4a Q4aRev hC
      P4a_generic_verified_rev P4a_impls_conform_rev hS h2 h3a)

/-- **Tightness of (H2) for the source-transfer theorem.** On `P4a` with the reverse-glue
configuration and the specs `Q4aRev`, the target is closed, generic verification, impl conformance,
synthesizer verification and (H3a) hold, (H2) fails, every key of `T4a` meets its spec in the
monomorphic table, and yet `main` violates its spec in the source semantics. -/
theorem synth_disagreement_breaks_source_transfer :
    Closed P4a.sig (tableM P4a (cfgRev P4a) T4a) T4a ∧ GenericVerified P4a Q4aRev ∧
    ImplsConform P4a Q4aRev T4a ∧ SynthVerified P4a (cfgRev P4a) Q4aRev T4a ∧
    ¬ SynthAgrees P4a (cfgRev P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    (∀ k ∈ T4a, MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4aRev k) k) ∧
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
  have hC : Closed P4a.sig (tableM P4a (cfgRev P4a) T4a) T4a := by decide
  refine ⟨hC, P4a_generic_verified_rev, P4a_impls_conform_rev, P4a_synthRev_verified_rev,
    synth_disagreement_breaks_adequacy.2.2.2.1, by decide,
    closed_target_meets_specs_of_generic_impl_synth_verified P4a (cfgRev P4a) T4a Q4aRev hC
      P4a_generic_verified_rev P4a_impls_conform_rev P4a_synthRev_verified_rev,
    P4a_main_violates_Q4aRev_in_source⟩

/-- A program whose method table is keyed by a non-normal type: the impl of method 0 of trait 0
at `<base 0 as 0>::Out` emits 1, while the impl at its normal form `base 1` emits 2. -/
def PncMeth : Program where
  fns := []
  methods := [(0, [0])]
  impls := [⟨0, 0, .proj 0 (.base 0), .emit 1⟩, ⟨0, 0, .base 1, .emit 2⟩]
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]

def TncMeth : List Key := [.meth 0 0 (.proj 0 (.base 0))]

/-- **Tightness of (H3a) for the source-transfer theorem.** The target consists of the non-normal
method key `meth 0 0 (<base 0 as 0>::Out)`; it is closed, generic verification, impl conformance,
synthesizer verification and (H2) hold, (H3a) fails, and the key violates its spec in the source
semantics, which normalizes the key and runs the impl at `base 1` (emitting `[2]`). -/
theorem noncanonical_key_breaks_source_transfer :
    Closed PncMeth.sig (tableM PncMeth (stdCfg PncMeth) TncMeth) TncMeth ∧
    GenericVerified PncMeth Q4b ∧ ImplsConform PncMeth Q4b TncMeth ∧
    SynthVerified PncMeth (stdCfg PncMeth) Q4b TncMeth ∧
    SynthAgrees PncMeth (stdCfg PncMeth) TncMeth ∧ ¬ CanonicalKeys PncMeth TncMeth ∧
    ¬ (∀ k ∈ TncMeth, MeetsAt PncMeth.sig (srcDef PncMeth) (Q4b k) k) := by
  have hG : GenericVerified PncMeth Q4b := by
    intro f fd τs h; simp [PncMeth] at h
  have hI : ImplsConform PncMeth Q4b TncMeth := by
    intro k hk _ b hb
    simp [TncMeth] at hk; subst hk
    have e : srcDef0 PncMeth (.meth 0 0 (.proj 0 (.base 0))) = some (.emit 1) := by decide
    rw [e] at hb; simp at hb; subst hb
    exact verified_emit _ _ 1
  have hS : SynthVerified PncMeth (stdCfg PncMeth) Q4b TncMeth := by
    intro k hk hs; simp [TncMeth] at hk; subst hk; simp [Key.isShim] at hs
  refine ⟨by decide, hG, hI, hS, synthStd_agrees PncMeth TncMeth, by decide, ?_⟩
  intro h
  have h0 := h (.meth 0 0 (.proj 0 (.base 0))) (by simp [TncMeth]) 2 st0
  have hrun : runKey PncMeth.sig (srcDef PncMeth) 2 (.meth 0 0 (.proj 0 (.base 0))) st0 =
      (.ok, ⟨[2], 0⟩) := by decide
  rw [hrun] at h0
  simp [SatOut, Q4b, appends, st0] at h0

/-- A configuration whose edge function ignores every body and returns the key `inst 99 []`. -/
def cfgJunkEdges (P : Program) : MonoCfg := ⟨fun _ => [.inst 99 []], synthStd P⟩

/-- The source-transfer theorem does not use the edge function: on `P4a` with `cfgJunkEdges`,
(H1) and edge-closure both fail, the six hypotheses of
`closed_target_meets_specs_in_source_semantics` hold, and every key of `T4a` meets its spec in the
source semantics. -/
theorem source_transfer_without_covering_or_edge_closure :
    ¬ CoversRefs P4a.sig (cfgJunkEdges P4a).E ∧
    ¬ EdgesIn (edgesM P4a (cfgJunkEdges P4a)) T4a ∧
    Closed P4a.sig (tableM P4a (cfgJunkEdges P4a) T4a) T4a ∧
    GenericVerified P4a Q4a ∧ ImplsConform P4a Q4a T4a ∧
    SynthVerified P4a (cfgJunkEdges P4a) Q4a T4a ∧
    SynthAgrees P4a (cfgJunkEdges P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    ∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4a k) k := by
  have hC : Closed P4a.sig (tableM P4a (cfgJunkEdges P4a) T4a) T4a := by decide
  have hS : SynthVerified P4a (cfgJunkEdges P4a) Q4a T4a := P4a_synthStd_verified
  have h2 : SynthAgrees P4a (cfgJunkEdges P4a) T4a := synthStd_agrees P4a T4a
  have h3a : CanonicalKeys P4a T4a := by decide
  have hnot1 : ¬ CoversRefs P4a.sig (cfgJunkEdges P4a).E := by
    intro h
    have := h (.call 0 []) (.inst 0 []) (by decide)
    revert this; decide
  have hnotE : ¬ EdgesIn (edgesM P4a (cfgJunkEdges P4a)) T4a := by decide
  exact ⟨hnot1, hnotE, hC, P4a_generic_verified, P4a_impls_conform, hS, h2, h3a,
    closed_target_meets_specs_in_source_semantics P4a (cfgJunkEdges P4a) T4a Q4a
      hC P4a_generic_verified P4a_impls_conform hS h2 h3a⟩

end Toy.MonoShim
