import MonoShim.Examples

/-!
# Further tightness witnesses
-/

namespace Toy.MonoShim

/-! ## Spec transfer -/

/-- Every key of `P2c` gets the spec "emits exactly 3". -/
def Q2c : Key → Spec := fun _ => appends [3]

theorem P2c_main_exec (c : Call) (st : St) :
    execS P2c.sig c (.seq (.reify 0 1 []) (.callPtr 0)) [] st =
      ((c (.inst 1 []) st).1, [(0, .fn (.inst 1 []))], (c (.inst 1 []) st).2) := rfl

theorem P2c_generic_verified : GenericVerified P2c Q2c := by
  intro f fd τs h
  match f, h with
  | 0, h =>
    have e : P2c.fns[0]? = some ⟨false, .seq (.reify 0 1 []) (.callPtr 0)⟩ := rfl
    rw [e] at h
    cases h
    show VerifiedBody P2c.sig Q2c (.seq (.reify 0 1 []) (.callPtr 0)) (appends [3])
    intro c hc st
    have := hc (.inst 1 []) (by decide) st
    show SatOut (appends [3]) st
      ((execS P2c.sig c (.seq (.reify 0 1 []) (.callPtr 0)) [] st).1,
       (execS P2c.sig c (.seq (.reify 0 1 []) (.callPtr 0)) [] st).2.2)
    rw [P2c_main_exec]
    exact this
  | 1, h =>
    have e : P2c.fns[1]? = some ⟨false, .emit 3⟩ := rfl
    rw [e] at h
    cases h
    exact verified_emit _ _ 3

/-- Tightness of closedness in the positive theorem: the generic bodies are verified, impl
conformance and synthesizer verification hold vacuously, but the target stops at `main`, so the
run is a link error and violates the spec. -/
theorem nonclosed_target_breaks_spec_transfer :
    ¬ Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) [.inst 0 []] ∧
    GenericVerified P2c Q2c ∧ ImplsConform P2c Q2c [.inst 0 []] ∧
    SynthVerified P2c (stdCfg P2c) Q2c [.inst 0 []] ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) (Q2c k) k) := by
  refine ⟨by decide, P2c_generic_verified, ?_, ?_, ?_⟩
  · intro k hk hi; simp at hk; subst hk; simp [Key.isImpl] at hi
  · intro k hk hs; simp at hk; subst hk; simp [Key.isShim] at hs
  · intro h'
    have h := h' (.inst 0 []) (by simp)
    have := h 3 st0
    have hrun : runKey P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) 3 (.inst 0 []) st0 =
        (.link (.inst 1 []), st0) := by decide
    rw [hrun] at this
    simp [SatOut, Q2c, appends] at this

/-- Tightness of generic verification in the positive theorem: a generic body that ignores its
spec. The target is closed and the other hypotheses hold vacuously. -/
theorem unverified_generic_body_breaks_spec_transfer :
    Closed P4bad.sig (tableM P4bad (stdCfg P4bad) [.inst 0 []]) [.inst 0 []] ∧
    ¬ GenericVerified P4bad Q4b ∧ ImplsConform P4bad Q4b [.inst 0 []] ∧
    SynthVerified P4bad (stdCfg P4bad) Q4b [.inst 0 []] ∧
    runM P4bad (stdCfg P4bad) [.inst 0 []] 2 (.inst 0 []) st0 = (.ok, ⟨[2], 0⟩) ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P4bad.sig (tableM P4bad (stdCfg P4bad) [.inst 0 []]) (Q4b k) k) := by
  have hrun : runM P4bad (stdCfg P4bad) [.inst 0 []] 2 (.inst 0 []) st0 = (.ok, ⟨[2], 0⟩) := by decide
  refine ⟨by decide, genericVerified_neg_example, ?_, ?_, hrun, ?_⟩
  · intro k hk hi; simp at hk; subst hk; simp [Key.isImpl] at hi
  · intro k hk hs; simp at hk; subst hk; simp [Key.isShim] at hs
  · intro h'
    have h := h' (.inst 0 []) (by simp)
    have := h 2 st0
    unfold runM at hrun
    rw [hrun] at this
    simp [SatOut, Q4b, appends, st0] at this

/-! ## Collection -/

/-- A scheduler that discards newly found keys. -/
def schedDrop (w _ : List Key) : List Key := w

/-- Tightness of scheduler admissibility: a scheduler that loses entries terminates with a set
that misses reachable keys. -/
theorem inadmissible_scheduler_misses_keys :
    ¬ SchedOK schedDrop ∧
    collect (edgesM P2c (stdCfg P2c)) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    Reach (edgesM P2c (stdCfg P2c)) [.inst 0 []] (.inst 1 []) ∧ Key.inst 1 [] ∉ [Key.inst 0 []] ∧
    ¬ (∀ k, k ∈ [Key.inst 0 []] ↔ Reach (edgesM P2c (stdCfg P2c)) [.inst 0 []] k) := by
  have hr : Reach (edgesM P2c (stdCfg P2c)) [.inst 0 []] (.inst 1 []) :=
    Reach.step (k := .inst 0 []) (Reach.root (by simp)) (by decide)
  refine ⟨schedOK_neg_example, by decide, hr, by decide, ?_⟩
  intro h
  have := (h (.inst 1 [])).mpr hr
  revert this; decide

/-- Tightness of scheduler admissibility for the divergence statement: a scheduler that discards
new keys terminates on the polymorphic-recursion program. -/
theorem polyrec_inadmissible_scheduler_terminates :
    ¬ SchedOK schedDrop ∧ collect (edgesM P5 (stdCfg P5)) schedDrop [.inst 0 []] 5 = some [.inst 0 []] :=
  ⟨schedOK_neg_example, by decide⟩

/-- A table precomputed from the standard synthesizer on the collected shim keys of `P2a`. -/
def pre2a : List (Key × Stmt) := [(.dropGlue (.base 1), .invoke (.userDrop 1))]

/-- Non-vacuity of the precomputed-synthesis theorem: on `P2a` with `pre2a`, FIFO on the
on-demand side and LIFO on the precomputed side, every hypothesis holds. -/
theorem precomputed_example :
    SchedOK fifo ∧ SchedOK lifo ∧
    (∀ k, Reach (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) [.inst 0 []] k → k.isShim = true →
      pre2a.lookup k = synthStd P2a k) ∧
    collect (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    collect (edgesM P2a (preCfg (refs P2a.sig) pre2a)) lifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] := by
  have h1 : collect (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] := by decide
  refine ⟨fifo_ok, lifo_ok, ?_, h1, by decide⟩
  intro k hr hs
  have hmem := (collect_mem_iff_reach _ fifo fifo_ok _ 10 _ h1 k).mpr hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> simp [Key.isShim] at hs
  rfl

/-- Tightness of the agreement hypothesis for precomputed synthesis: with the empty precomputed
table (which disagrees with the synthesizer on the reachable shim key `dropGlue (base 1)`), both
schedulers admissible and both collectors returning sets, the collected sets differ (the user
destructor reached through the glue is missing). -/
theorem stale_precomputed_table_changes_target :
    SchedOK fifo ∧
    ¬ (∀ k, Reach (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) [.inst 0 []] k → k.isShim = true →
        (pre2a.drop 1).lookup k = synthStd P2a k) ∧
    collect (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    collect (edgesM P2a (preCfg (refs P2a.sig) (pre2a.drop 1))) fifo [.inst 0 []] 10 =
      some [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    ¬ ((∀ k, k ∈ ([.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] : List Key) ↔
          k ∈ ([.dropGlue (.base 1), .inst 1 [], .inst 0 []] : List Key)) ∧
       ∀ k, tableM P2a ⟨refs P2a.sig, synthStd P2a⟩
              [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] k =
            tableM P2a (preCfg (refs P2a.sig) (pre2a.drop 1))
              [.dropGlue (.base 1), .inst 1 [], .inst 0 []] k) := by
  have h1 : collect (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] := by decide
  refine ⟨fifo_ok, ?_, h1, by decide, ?_⟩
  · intro h
    have hr : Reach (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) [.inst 0 []] (.dropGlue (.base 1)) :=
      (collect_mem_iff_reach _ fifo fifo_ok _ 10 _ h1 _).mp (by decide)
    have := h _ hr rfl
    revert this; decide
  · rintro ⟨h, _⟩
    have := (h (.userDrop 1)).mp (by decide)
    revert this; decide

/-- Non-vacuity of order independence: FIFO and LIFO are admissible and collect the same keys for
`Pall`, in different orders. -/
theorem fifo_lifo_same_set_example :
    SchedOK fifo ∧ SchedOK lifo ∧
    collect (edgesM Pall (stdCfg Pall)) fifo [.inst 0 []] 40 = some Tall ∧
    collect (edgesM Pall (stdCfg Pall)) lifo [.inst 0 []] 40 =
      some [.userDrop 0, .dropGlue (.base 0), .dropGlue (.base 3), .userClone 3, .userClone 0,
        .cloneShim (.pair (.base 0) (.base 3)), .cloneShim .fnPtr, .inst 1 [], .reifyShim 1 [],
        .userDrop 2, .dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []] := by
  exact ⟨fifo_ok, lifo_ok, by decide, by decide⟩

/-- Tightness of scheduler admissibility for the precomputed-synthesis theorem: on `P2c` (no shim
keys, so the empty precomputed table agrees on every reachable shim key), FIFO on the on-demand
side, and the inadmissible `schedDrop` on the precomputed side, the collected sets differ. -/
theorem inadmissible_scheduler_breaks_precomputed_equality :
    SchedOK fifo ∧ ¬ SchedOK schedDrop ∧
    (∀ k, Reach (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) [.inst 0 []] k → k.isShim = true →
      ([] : List (Key × Stmt)).lookup k = synthStd P2c k) ∧
    collect (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    collect (edgesM P2c (preCfg (refs P2c.sig) [])) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    ¬ ((∀ k, k ∈ ([.inst 1 [], .inst 0 []] : List Key) ↔ k ∈ ([.inst 0 []] : List Key)) ∧
       ∀ k, tableM P2c ⟨refs P2c.sig, synthStd P2c⟩ [.inst 1 [], .inst 0 []] k =
            tableM P2c (preCfg (refs P2c.sig) []) [.inst 0 []] k) := by
  have hT : collect (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) fifo [.inst 0 []] 10 =
      some [.inst 1 [], .inst 0 []] := by decide
  refine ⟨fifo_ok, schedOK_neg_example, ?_, hT, by decide, ?_⟩
  · intro k hk hs
    have hm := (collect_mem_iff_reach _ fifo fifo_ok _ 10 _ hT k).mpr hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl <;> simp [Key.isShim] at hs
  · rintro ⟨h, _⟩
    have := (h (.inst 1 [])).mp (by decide)
    revert this; decide

/-! ## Per-unit linking -/

/-- Tightness of determinism: the units cover `T4a`, unit B's synthesizer disagrees with the
standard one on the pair's glue, and with B linked first the linked table differs from the
single-target table there. -/
theorem nondeterministic_units_break_link_equality :
    ¬ DeterministicUnits (synthStd P4a) [unitB (synthRev P4a), unitA (synthStd P4a)] ∧
    UnitsCover [unitB (synthRev P4a), unitA (synthStd P4a)] T4a ∧
    linkUnits P4a (refs P4a.sig) [unitB (synthRev P4a), unitA (synthStd P4a)] glueKey4a ≠
      tableM P4a (stdCfg P4a) T4a glueKey4a ∧
    ¬ (∀ k, linkUnits P4a (refs P4a.sig) [unitB (synthRev P4a), unitA (synthStd P4a)] k =
      tableM P4a ⟨refs P4a.sig, synthStd P4a⟩ T4a k) := by
  have hne : linkUnits P4a (refs P4a.sig) [unitB (synthRev P4a), unitA (synthStd P4a)] glueKey4a ≠
      tableM P4a (stdCfg P4a) T4a glueKey4a := by decide
  refine ⟨?_, ?_, hne, fun h => hne (h glueKey4a)⟩
  · intro h
    have := h (unitB (synthRev P4a)) (by simp) glueKey4a (by simp [unitB]) rfl
    revert this; decide
  · intro k
    rw [deterministic_units_example.2.1 k]
    constructor
    · rintro ⟨u, hu, hk⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨unitA (synthStd P4a), by simp, hk⟩
      · exact ⟨unitB (synthRev P4a), by simp, hk⟩
    · rintro ⟨u, hu, hk⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨unitB (synthStd P4a), by simp, hk⟩
      · exact ⟨unitA (synthStd P4a), by simp, hk⟩

/-- Tightness of coverage: if unit B is missing, the linked table lacks keys of `T4a`. -/
theorem uncovering_units_break_link_equality :
    DeterministicUnits (synthStd P4a) [unitA (synthStd P4a)] ∧
    ¬ UnitsCover [unitA (synthStd P4a)] T4a ∧
    linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a)] (.dropGlue (.base 0)) ≠
      tableM P4a (stdCfg P4a) T4a (.dropGlue (.base 0)) ∧
    ¬ (∀ k, linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a)] k =
      tableM P4a ⟨refs P4a.sig, synthStd P4a⟩ T4a k) := by
  have hne : linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a)] (.dropGlue (.base 0)) ≠
      tableM P4a (stdCfg P4a) T4a (.dropGlue (.base 0)) := by decide
  refine ⟨?_, ?_, hne, fun h => hne (h _)⟩
  · intro u hu k _ _
    simp at hu; subst hu; rfl
  · intro h
    have := (h (.dropGlue (.base 0))).mp (by decide)
    obtain ⟨u, hu, hk⟩ := this
    simp at hu; subst hu
    revert hk; decide

/-! ## Scheduler admissibility on either side -/

/-- Tightness of the first scheduler's admissibility for order independence: on `P2c`, the
inadmissible `schedDrop` as the first scheduler and FIFO as the second, both collectors return
sets, and the sets differ in membership. -/
theorem inadmissible_first_scheduler_breaks_order_independence :
    ¬ SchedOK schedDrop ∧ SchedOK fifo ∧
    collect (edgesM P2c (stdCfg P2c)) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    collect (edgesM P2c (stdCfg P2c)) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    ¬ (∀ k, k ∈ ([.inst 0 []] : List Key) ↔ k ∈ ([.inst 1 [], .inst 0 []] : List Key)) := by
  refine ⟨schedOK_neg_example, fifo_ok, by decide, by decide, ?_⟩
  intro h
  have := (h (.inst 1 [])).mpr (by decide)
  revert this; decide

/-- Tightness of the second scheduler's admissibility for order independence: the same instance
with the schedulers swapped. -/
theorem inadmissible_second_scheduler_breaks_order_independence :
    SchedOK fifo ∧ ¬ SchedOK schedDrop ∧
    collect (edgesM P2c (stdCfg P2c)) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    collect (edgesM P2c (stdCfg P2c)) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    ¬ (∀ k, k ∈ ([.inst 1 [], .inst 0 []] : List Key) ↔ k ∈ ([.inst 0 []] : List Key)) := by
  refine ⟨fifo_ok, schedOK_neg_example, by decide, by decide, ?_⟩
  intro h
  have := (h (.inst 1 [])).mp (by decide)
  revert this; decide

/-- Tightness of the on-demand side's scheduler admissibility for the precomputed-synthesis
theorem: on `P2c` (no shim keys, so the empty precomputed table agrees on every reachable shim
key), the inadmissible `schedDrop` on the on-demand side and FIFO on the precomputed side, the
collected sets differ. -/
theorem inadmissible_on_demand_scheduler_breaks_precomputed_equality :
    ¬ SchedOK schedDrop ∧ SchedOK fifo ∧
    (∀ k, Reach (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) [.inst 0 []] k → k.isShim = true →
      ([] : List (Key × Stmt)).lookup k = synthStd P2c k) ∧
    collect (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    collect (edgesM P2c (preCfg (refs P2c.sig) [])) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    ¬ ((∀ k, k ∈ ([.inst 0 []] : List Key) ↔ k ∈ ([.inst 1 [], .inst 0 []] : List Key)) ∧
       ∀ k, tableM P2c ⟨refs P2c.sig, synthStd P2c⟩ [.inst 0 []] k =
            tableM P2c (preCfg (refs P2c.sig) []) [.inst 1 [], .inst 0 []] k) := by
  refine ⟨schedOK_neg_example, fifo_ok, inadmissible_scheduler_breaks_precomputed_equality.2.2.1,
    by decide, by decide, ?_⟩
  rintro ⟨h, _⟩
  have := (h (.inst 1 [])).mpr (by decide)
  revert this; decide

end Toy.MonoShim
