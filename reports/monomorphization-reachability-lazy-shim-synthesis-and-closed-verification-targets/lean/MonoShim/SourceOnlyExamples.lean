import MonoShim.LadderExamples

/-!
# Source-only verification: counterexamples and a non-vacuity witness
-/

namespace Toy.MonoShim

/-- The spec "completes normally, appending exactly the events `l`". -/
def appends (l : List Nat) : Spec := fun st o => o = (.ok, { st with evs := st.evs ++ l })

/-! ## (a) Drop-glue order decides a whole-program spec -/

/-- `base 0` is a guard whose destructor emits 10 ("release"); `base 1` is data whose destructor
emits 20 ("free"). `main` drops a `pair (base 0) (base 1)`. -/
def P4a : Program where
  fns := [⟨false, .drop (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .emit 10), (1, .emit 20)]
  cloneImpls := []
  assoc := []

/-- A plausible synthesizer variant: drop glue for a pair drops the fields in reverse
declaration order (the order used for local variables), with the same unwind ladder. -/
def synthRev (P : Program) : Key → Option Stmt
  | .dropGlue (.pair a b) => some (.seq (.onUnwind (.drop b) (.drop a)) (.drop a))
  | k => synthStd P k

def cfgRev (P : Program) : MonoCfg := ⟨refs P.sig, synthRev P⟩

/-- Specs: `main` and the pair's glue must emit "release" before "free". -/
def Q4a : Key → Spec
  | .inst 0 [] => appends [10, 20]
  | .dropGlue (.pair (.base 0) (.base 1)) => appends [10, 20]
  | .dropGlue (.base 0) => appends [10]
  | .dropGlue (.base 1) => appends [20]
  | .userDrop 0 => appends [10]
  | .userDrop 1 => appends [20]
  | _ => fun _ _ => True

def T4a : List Key :=
  [.userDrop 1, .userDrop 0, .dropGlue (.base 1), .dropGlue (.base 0),
    .dropGlue (.pair (.base 0) (.base 1)), .inst 0 []]

theorem T4a_collected :
    collect (edgesM P4a (stdCfg P4a)) fifo [.inst 0 []] 20 = some T4a ∧
    collect (edgesM P4a (cfgRev P4a)) fifo [.inst 0 []] 20 =
      some [.userDrop 0, .userDrop 1, .dropGlue (.base 0), .dropGlue (.base 1),
        .dropGlue (.pair (.base 0) (.base 1)), .inst 0 []] := by
  decide

/-- A single call satisfies `appends l` when its oracle answer does. -/
theorem verified_single_call (sig : Sig) (A : Key → Spec) (l : List Nat) (k : Key) (s : Stmt)
    (hs : ∀ c fr st, execS sig c s fr st = ((c k st).1, fr, (c k st).2))
    (hr : k ∈ refs sig s) (hA : A k = appends l) : VerifiedBody sig A s (appends l) := by
  intro c hc st
  have := hc k hr st
  rw [hA] at this
  simpa [hs] using this

theorem P4a_generic_verified : GenericVerified P4a Q4a := by
  intro f fd τs h
  match f, h with
  | 0, h =>
    have e : P4a.fns[0]? = some ⟨false, .drop (.pair (.base 0) (.base 1))⟩ := rfl
    rw [e] at h
    cases h
    cases τs with
    | nil =>
      exact verified_single_call _ _ [10, 20] (.dropGlue (.pair (.base 0) (.base 1))) _
        (fun _ _ _ => rfl) (by decide) rfl
    | cons t ts => intro c _ st; right; trivial

theorem verified_emit (sig : Sig) (A : Key → Spec) (e : Nat) :
    VerifiedBody sig A (.emit e) (appends [e]) := by
  intro c _ st
  right; rfl

theorem P4a_impls_conform : ImplsConform P4a Q4a T4a := by
  intro k hk hi b hb
  simp [T4a] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Key.isImpl] at hi
  · have e : srcDef0 P4a (.userDrop 1) = some (.emit 20) := rfl
    rw [e] at hb; simp at hb; subst hb; exact verified_emit _ _ 20
  · have e : srcDef0 P4a (.userDrop 0) = some (.emit 10) := rfl
    rw [e] at hb; simp at hb; subst hb; exact verified_emit _ _ 10

/-- The two-field drop ladder `seq (onUnwind (drop a) (drop b)) (drop b)` appends the events of
both drops when each drop is verified to append its events. -/
theorem verified_glue_pair (sig : Sig) (A : Key → Spec) (a b : Ty) (la lb : List Nat)
    (ha : A (.dropGlue a) = appends la) (hb : A (.dropGlue b) = appends lb) :
    VerifiedBody sig A (.seq (.onUnwind (.drop a) (.drop b)) (.drop b)) (appends (la ++ lb)) := by
  intro c hc st
  have h1 := hc (.dropGlue a) (by simp [refs]) st
  rw [ha] at h1
  rcases h1 with h1 | h1
  · left; simp [execS]; rcases hca : c (.dropGlue a) st with ⟨r, st'⟩; rw [hca] at h1
    simp at h1; subst h1; rfl
  · simp only [appends] at h1
    have h2 := hc (.dropGlue b) (by simp [refs]) { st with evs := st.evs ++ la }
    rw [hb] at h2
    rcases h2 with h2 | h2
    · left; simp [execS, h1]; rcases hcb : c (.dropGlue b) { st with evs := st.evs ++ la } with ⟨r, st'⟩
      rw [hcb] at h2; simp at h2; subst h2; rfl
    · right; simp only [appends] at h2; simp [execS, h1, h2, appends]

theorem P4a_synthStd_verified : SynthVerified P4a (stdCfg P4a) Q4a T4a := by
  intro k hk hs b hb
  simp [T4a] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Key.isShim] at hs
  · have e : (stdCfg P4a).synth (.dropGlue (.base 1)) = some (.invoke (.userDrop 1)) := rfl
    rw [e] at hb; simp at hb; subst hb
    exact verified_single_call _ _ _ (.userDrop 1) _ (fun _ _ _ => rfl) (by simp [refs]) rfl
  · have e : (stdCfg P4a).synth (.dropGlue (.base 0)) = some (.invoke (.userDrop 0)) := rfl
    rw [e] at hb; simp at hb; subst hb
    exact verified_single_call _ _ _ (.userDrop 0) _ (fun _ _ _ => rfl) (by simp [refs]) rfl
  · have e : (stdCfg P4a).synth (.dropGlue (.pair (.base 0) (.base 1))) =
        some (.seq (.onUnwind (.drop (.base 0)) (.drop (.base 1))) (.drop (.base 1))) := rfl
    rw [e] at hb; simp at hb; subst hb
    exact verified_glue_pair _ _ (.base 0) (.base 1) [10] [20] rfl rfl

/-- **Non-vacuity of the positive theorem, and the outcome with declaration-order glue.** With the
standard synthesizer all hypotheses hold, so every key of the target meets its spec; in
particular `main` emits "release" before "free". -/
theorem P4a_std_meets_specs :
    Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a ∧ GenericVerified P4a Q4a ∧
    ImplsConform P4a Q4a T4a ∧ SynthVerified P4a (stdCfg P4a) Q4a T4a ∧
    ∀ k ∈ T4a, MeetsAt P4a.sig (tableM P4a (stdCfg P4a) T4a) (Q4a k) k := by
  have hC : Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a := by decide
  exact ⟨hC, P4a_generic_verified, P4a_impls_conform, P4a_synthStd_verified,
    closed_target_meets_specs_of_generic_impl_synth_verified P4a (stdCfg P4a) T4a Q4a hC
      P4a_generic_verified P4a_impls_conform P4a_synthStd_verified⟩

/-- **Headline counterexample (a): every source definition meets its spec, yet the whole program
violates its drop-event spec under the reverse-declaration-order glue variant.** The target is
closed, generic verification and impl conformance hold, and the run of `main` emits "free"
before "release". (This is also the tightness witness for the verified-synthesizer
hypothesis of the positive theorem.) -/
theorem source_defs_verified_yet_program_violates_spec_under_reverse_glue :
    Closed P4a.sig (tableM P4a (cfgRev P4a) T4a) T4a ∧ GenericVerified P4a Q4a ∧
    ImplsConform P4a Q4a T4a ∧ ¬ SynthVerified P4a (cfgRev P4a) Q4a T4a ∧
    runM P4a (cfgRev P4a) T4a 4 (.inst 0 []) st0 = (.ok, ⟨[20, 10], 0⟩) ∧
    ¬ MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) ∧
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a k) k) := by
  have hrun : runM P4a (cfgRev P4a) T4a 4 (.inst 0 []) st0 = (.ok, ⟨[20, 10], 0⟩) := by decide
  have hnot : ¬ MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) := by
    intro h
    have := h 4 st0
    unfold runM at hrun
    rw [hrun] at this
    simp [SatOut, Q4a, appends, st0] at this
  refine ⟨by decide, P4a_generic_verified, P4a_impls_conform, ?_, hrun, hnot,
    fun h => hnot (h _ (by simp [T4a]))⟩
  intro hS
  exact hnot (closed_target_meets_specs_of_generic_impl_synth_verified P4a (cfgRev P4a) T4a Q4a
    (by decide) P4a_generic_verified P4a_impls_conform hS _ (by simp [T4a]))

/-- **No verdict determined by the program and its specs alone is correct for every synthesizer.**
For every Boolean verdict `V` on (program, spec assignment) there is a configuration with the full
edge function — the standard one or the reverse-glue variant — such that the target `T4a` is
closed, every generic body of `P4a` is verified and every user impl in `T4a` conforms, and yet
`V P4a Q4a` differs from whether `main` meets its spec in the table compiled with that
configuration. The two configurations differ only in the synthesized glue of the pair; the
reverse-glue variant violates (H2) there (`synth_disagreement_breaks_adequacy`). -/
theorem no_source_only_verdict_correct_for_every_synthesizer (V : Program → (Key → Spec) → Bool) :
    GenericVerified P4a Q4a ∧ ImplsConform P4a Q4a T4a ∧
    ∃ cfg : MonoCfg, (cfg = stdCfg P4a ∨ cfg = cfgRev P4a) ∧
      Closed P4a.sig (tableM P4a cfg T4a) T4a ∧
      ¬ (V P4a Q4a = true ↔
          MeetsAt P4a.sig (tableM P4a cfg T4a) (Q4a (.inst 0 [])) (.inst 0 [])) := by
  refine ⟨P4a_generic_verified, P4a_impls_conform, ?_⟩
  have hstd := P4a_std_meets_specs.2.2.2.2 (.inst 0 []) (by simp [T4a])
  have hrev := source_defs_verified_yet_program_violates_spec_under_reverse_glue.2.2.2.2.2.1
  cases hV : V P4a Q4a with
  | true =>
    refine ⟨cfgRev P4a, Or.inr rfl, by decide, ?_⟩
    intro h; exact hrev (h.mp rfl)
  | false =>
    refine ⟨stdCfg P4a, Or.inl rfl, by decide, ?_⟩
    intro h; exact Bool.false_ne_true (h.mpr hstd)

/-- The verdict "the root `main` meets its spec in the source semantics `runS`": a function of the
program and its specs alone; noncomputable (a classical indicator), not a decision procedure. -/
noncomputable def srcVerdict (P : Program) (Q : Key → Spec) : Bool :=
  @decide (MeetsAt P.sig (srcDef P) (Q (.inst 0 [])) (.inst 0 [])) (Classical.propDecidable _)

/-- **Escape hatch (positive control for the impossibility).** For every program, spec assignment,
configuration and target that satisfy the hypotheses of the adequacy theorem with roots `[main]` —
in particular (H2), synthesizer agreement with the source rules `glueSrc`/`cloneSrc` — the
source-only verdict `srcVerdict` is correct. -/
theorem srcVerdict_correct_of_adequacy (P : Program) (cfg : MonoCfg) (T : List Key)
    (Q : Key → Spec) (hR : RootsIn [.inst 0 []] T) (hE : EdgesIn (edgesM P cfg) T)
    (h1 : CoversRefs P.sig cfg.E) (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T)
    (h3b : CanonicalRefs P cfg T) :
    srcVerdict P Q = true ↔ MeetsAt P.sig (tableM P cfg T) (Q (.inst 0 [])) (.inst 0 []) := by
  rw [meetsAt_tableM_iff_srcDef_of_adequacy P cfg T hE h1 h2 h3a h3b _ _ (hR _ (by simp))]
  simp [srcVerdict]

/-- The escape hatch is not vacuous: on `P4a` the standard configuration satisfies every
hypothesis of `srcVerdict_correct_of_adequacy`, and `srcVerdict P4a Q4a = true`. -/
theorem srcVerdict_correct_example :
    RootsIn [.inst 0 []] T4a ∧ EdgesIn (edgesM P4a (stdCfg P4a)) T4a ∧
    CoversRefs P4a.sig (stdCfg P4a).E ∧ SynthAgrees P4a (stdCfg P4a) T4a ∧
    CanonicalKeys P4a T4a ∧ CanonicalRefs P4a (stdCfg P4a) T4a ∧ srcVerdict P4a Q4a = true := by
  have hR : RootsIn [.inst 0 []] T4a := by decide
  have hE : EdgesIn (edgesM P4a (stdCfg P4a)) T4a := by decide
  have h1 : CoversRefs P4a.sig (stdCfg P4a).E := fun _ _ h => h
  have h2 : SynthAgrees P4a (stdCfg P4a) T4a := synthStd_agrees P4a T4a
  have h3a : CanonicalKeys P4a T4a := by decide
  have h3b : CanonicalRefs P4a (stdCfg P4a) T4a := by decide
  refine ⟨hR, hE, h1, h2, h3a, h3b, ?_⟩
  exact (srcVerdict_correct_of_adequacy P4a (stdCfg P4a) T4a Q4a hR hE h1 h2 h3a h3b).mpr
    (P4a_std_meets_specs.2.2.2.2 (.inst 0 []) (by simp [T4a]))

/-! ## (b) A generic body verified against a trait-method spec, wrong at a bad impl -/

/-- Function 0 is generic: it calls method 0 of trait 0 on its type parameter. The trait-method
spec says the method emits 1; the impl for `base 0` does, the impl for `base 1` emits 2. -/
def P4b : Program where
  fns := [⟨false, .mcall 0 0 (.param 0)⟩]
  methods := [(0, [0])]
  impls := [⟨0, 0, .base 0, .emit 1⟩, ⟨0, 0, .base 1, .emit 2⟩]
  dropImpls := []
  cloneImpls := []
  assoc := []

/-- Every key gets the spec "emits exactly 1": for method keys this is the trait-method spec. -/
def Q4b : Key → Spec := fun _ => appends [1]

def T4b : List Key := [.meth 0 0 (.base 1), .inst 0 [.base 1]]

theorem P4b_generic_verified : GenericVerified P4b Q4b := by
  intro f fd τs h
  match f, h with
  | 0, h =>
    have e : P4b.fns[0]? = some ⟨false, .mcall 0 0 (.param 0)⟩ := rfl
    rw [e] at h
    cases h
    exact verified_single_call _ _ _ (.meth 0 0 (((Ty.param 0).subst τs).norm P4b.assoc)) _
      (fun _ _ _ => rfl) (by simp [Stmt.subst, Stmt.norm, refs]) rfl

/-- **Counterexample (b), and tightness of impl conformance in the positive theorem.** The target
is closed, the generic body is verified against the trait-method spec, the synthesizer is
(vacuously) verified, but the instance at `base 1` violates its spec because the resolved impl
violates the trait-method spec. -/
theorem generic_verified_wrong_at_nonconforming_impl :
    collect (edgesM P4b (stdCfg P4b)) fifo [.inst 0 [.base 1]] 10 = some T4b ∧
    Closed P4b.sig (tableM P4b (stdCfg P4b) T4b) T4b ∧ GenericVerified P4b Q4b ∧
    SynthVerified P4b (stdCfg P4b) Q4b T4b ∧ ¬ ImplsConform P4b Q4b T4b ∧
    runM P4b (stdCfg P4b) T4b 2 (.inst 0 [.base 1]) st0 = (.ok, ⟨[2], 0⟩) ∧
    ¬ MeetsAt P4b.sig (tableM P4b (stdCfg P4b) T4b) (Q4b (.inst 0 [.base 1])) (.inst 0 [.base 1]) ∧
    ¬ (∀ k ∈ T4b, MeetsAt P4b.sig (tableM P4b (stdCfg P4b) T4b) (Q4b k) k) := by
  have hrun : runM P4b (stdCfg P4b) T4b 2 (.inst 0 [.base 1]) st0 = (.ok, ⟨[2], 0⟩) := by decide
  have hnot : ¬ MeetsAt P4b.sig (tableM P4b (stdCfg P4b) T4b) (Q4b (.inst 0 [.base 1]))
      (.inst 0 [.base 1]) := by
    intro h
    have := h 2 st0
    unfold runM at hrun
    rw [hrun] at this
    simp [SatOut, Q4b, appends, st0] at this
  have hS : SynthVerified P4b (stdCfg P4b) Q4b T4b := by
    intro k hk hs
    simp [T4b] at hk
    rcases hk with rfl | rfl <;> simp [Key.isShim] at hs
  refine ⟨by decide, by decide, P4b_generic_verified, hS, ?_, hrun, hnot,
    fun h => hnot (h _ (by simp [T4b]))⟩
  intro hI
  exact hnot (closed_target_meets_specs_of_generic_impl_synth_verified P4b (stdCfg P4b) T4b Q4b
    (by decide) P4b_generic_verified hI hS _ (by simp [T4b]))

/-- Positive control for (b): at `base 0`, whose impl conforms, the same generic body meets its
spec. -/
theorem generic_verified_right_at_conforming_impl :
    ∀ k ∈ [.meth 0 0 (.base 0), .inst 0 [.base 0]],
      MeetsAt P4b.sig (tableM P4b (stdCfg P4b) [.meth 0 0 (.base 0), .inst 0 [.base 0]]) (Q4b k) k := by
  apply closed_target_meets_specs_of_generic_impl_synth_verified
  · decide
  · exact P4b_generic_verified
  · intro k hk hi b hb
    simp at hk
    rcases hk with rfl | rfl
    · have e : srcDef0 P4b (.meth 0 0 (.base 0)) = some (.emit 1) := rfl
      rw [e] at hb; simp at hb; subst hb; exact verified_emit _ _ 1
    · simp [Key.isImpl] at hi
  · intro k hk hs
    simp at hk
    rcases hk with rfl | rfl <;> simp [Key.isShim] at hs

end Toy.MonoShim
