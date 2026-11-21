import MonoShim.Relativity

/-!
# Non-vacuity and tightness witnesses for the closure and adequacy theorems
-/

namespace Toy.MonoShim

/-- A program exercising every statement form that creates a reference: `main` unsizes a `base 2`
to `dyn 0`, calls its method through the trait object, calls the same method directly, and drops
the trait object through its vtable (the destructor of `base 2` emits 6); it reifies the
`trackCaller` function 1 and calls through the pointer; it clones a function pointer (the builtin
`Copy` clone); and it clones a `pair (base 0) (base 3)` (whose second clone panics, so the first
clone is dropped by the ladder); the resulting unwind is caught by an `onUnwind` whose cleanup
drops a `base 0`. Synthesized bodies add `invoke` (drop glue calling a user `Drop::drop`); the
source clone of the pair is the aggregate `cloneAgg`. -/
def Pall : Program where
  fns := [⟨false,
      .seq (.unsize 0 (.base 2) 0) (.seq (.callDyn 0 0) (.seq (.mcall 0 0 (.base 2))
        (.seq (.dropDyn 0) (.seq (.reify 1 1 []) (.seq (.callPtr 1) (.seq (.clone .fnPtr)
          (.onUnwind (.clone (.pair (.base 0) (.base 3))) (.drop (.base 0))))))))) ⟩,
    ⟨true, .emit 4⟩]
  methods := [(0, [0])]
  impls := [⟨0, 0, .base 2, .emit 5⟩]
  dropImpls := [(0, .emit 2), (2, .emit 6)]
  cloneImpls := [(0, .emit 1), (3, .panic)]
  assoc := []

def Tall : List Key :=
  [.userDrop 0, .dropGlue (.base 3), .userClone 3, .userClone 0, .inst 1 [], .userDrop 2,
    .dropGlue (.base 0), .cloneShim (.pair (.base 0) (.base 3)), .cloneShim .fnPtr, .reifyShim 1 [],
    .dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []]

/-- **Non-vacuity of closure and adequacy.** On `Pall` with the standard pipeline, every
hypothesis of both theorems holds; the run from `main` emits 5 (call through the trait object),
5 (direct method call), 6 (drop through the vtable), 4 (through the reify shim), 1 (first clone),
2 (ladder cleanup), 2 (`onUnwind` cleanup), then unwinds. -/
theorem Pall_all_hypotheses_hold :
    collect (edgesM Pall (stdCfg Pall)) fifo [.inst 0 []] 40 = some Tall ∧
    RootsIn [.inst 0 []] Tall ∧ EdgesIn (edgesM Pall (stdCfg Pall)) Tall ∧
    CoversRefs Pall.sig (stdCfg Pall).E ∧ SynthAgrees Pall (stdCfg Pall) Tall ∧
    SynthTotal (stdCfg Pall) Tall ∧ InstDefined Pall Tall ∧
    CanonicalKeys Pall Tall ∧ CanonicalRefs Pall (stdCfg Pall) Tall ∧
    Closed Pall.sig (tableM Pall (stdCfg Pall) Tall) Tall ∧
    runM Pall (stdCfg Pall) Tall 5 (.inst 0 []) st0 = (.unwind, ⟨[5, 5, 6, 4, 1, 2, 2], 0⟩) ∧
    runS Pall 5 (.inst 0 []) st0 = (.unwind, ⟨[5, 5, 6, 4, 1, 2, 2], 0⟩) := by
  exact ⟨by decide, by decide, by decide, stdCfg_covers Pall, synthStd_agrees Pall Tall, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Tightness of (H2) for adequacy: with the reverse-declaration-order glue variant, every other
hypothesis holds on `P4a`, but the mono and source runs differ. -/
theorem synth_disagreement_breaks_adequacy :
    RootsIn [.inst 0 []] T4a ∧ EdgesIn (edgesM P4a (cfgRev P4a)) T4a ∧
    CoversRefs P4a.sig (cfgRev P4a).E ∧ ¬ SynthAgrees P4a (cfgRev P4a) T4a ∧
    CanonicalKeys P4a T4a ∧ CanonicalRefs P4a (cfgRev P4a) T4a ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P4a (cfgRev P4a) T4a n r st = runS P4a n r st) ∧
    runM P4a (cfgRev P4a) T4a 4 (.inst 0 []) st0 = (.ok, ⟨[20, 10], 0⟩) ∧
    runS P4a 4 (.inst 0 []) st0 = (.ok, ⟨[10, 20], 0⟩) := by
  refine ⟨by decide, by decide, fun _ _ h => h, ?_, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 4) (st := st0) (by decide), by decide, by decide⟩
  intro h
  have := h glueKey4a (by decide) rfl (runKey P4a.sig (srcDef P4a) 3) st0
  revert this; decide

/-- `base 0` with `<base 0 as 0>::Out = base 1`, and `base 1` has a destructor emitting 8. -/
def Pnc : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := [(1, .emit 8)]
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]

/-- Tightness of (H3a) for adequacy: a non-canonical root key. Every other hypothesis holds,
but the table is keyed by the unnormalized type while the source normalizes it. -/
theorem noncanonical_root_breaks_adequacy :
    RootsIn [.dropGlue (.proj 0 (.base 0))] [.dropGlue (.proj 0 (.base 0))] ∧
    EdgesIn (edgesM Pnc (stdCfg Pnc)) [.dropGlue (.proj 0 (.base 0))] ∧
    CoversRefs Pnc.sig (stdCfg Pnc).E ∧ SynthAgrees Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] ∧
    ¬ CanonicalKeys Pnc [.dropGlue (.proj 0 (.base 0))] ∧
    CanonicalRefs Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] ∧
    ¬ (∀ r ∈ [.dropGlue (.proj 0 (.base 0))], ∀ (n : Nat) (st : St),
      runM Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] n r st = runS Pnc n r st) ∧
    runM Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] 3 (.dropGlue (.proj 0 (.base 0))) st0
      = (.link (.dropGlue (.proj 0 (.base 0))), st0) ∧
    runS Pnc 3 (.dropGlue (.proj 0 (.base 0))) st0 = (.ok, ⟨[8], 0⟩) := by
  exact ⟨by decide, by decide, stdCfg_covers Pnc, synthStd_agrees Pnc _, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩

/-- Tightness of the roots hypothesis: with the empty target every other hypothesis holds
vacuously, and the root is a link error. -/
theorem root_outside_target_breaks_adequacy :
    ¬ RootsIn [.inst 0 []] [] ∧ EdgesIn (edgesM P2c (stdCfg P2c)) [] ∧
    CoversRefs P2c.sig (stdCfg P2c).E ∧ SynthAgrees P2c (stdCfg P2c) [] ∧
    CanonicalKeys P2c [] ∧ CanonicalRefs P2c (stdCfg P2c) [] ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St), runM P2c (stdCfg P2c) [] n r st = runS P2c n r st) ∧
    runM P2c (stdCfg P2c) [] 3 (.inst 0 []) st0 = (.link (.inst 0 []), st0) ∧
    runS P2c 3 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) := by
  exact ⟨by decide, by decide, stdCfg_covers P2c, synthStd_agrees P2c _, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩

/-- Tightness of edge-closure (for both theorems): a target that stops at the root. -/
theorem target_not_edge_closed_breaks_closure_and_adequacy :
    RootsIn [.inst 0 []] [.inst 0 []] ∧ ¬ EdgesIn (edgesM P2c (stdCfg P2c)) [.inst 0 []] ∧
    CoversRefs P2c.sig (stdCfg P2c).E ∧ SynthAgrees P2c (stdCfg P2c) [.inst 0 []] ∧
    SynthTotal (stdCfg P2c) [.inst 0 []] ∧ InstDefined P2c [.inst 0 []] ∧
    CanonicalKeys P2c [.inst 0 []] ∧ CanonicalRefs P2c (stdCfg P2c) [.inst 0 []] ∧
    ¬ Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) [.inst 0 []] ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2c (stdCfg P2c) [.inst 0 []] n r st = runS P2c n r st) ∧
    runM P2c (stdCfg P2c) [.inst 0 []] 3 (.inst 0 []) st0 = (.link (.inst 1 []), st0) ∧
    runS P2c 3 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) := by
  exact ⟨by decide, by decide, stdCfg_covers P2c, synthStd_agrees P2c _, by decide, by decide,
    by decide, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩

/-- `main` calls function 5, which the program does not define. -/
def Pundef : Program where
  fns := [⟨false, .call 5 []⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

/-- Tightness of (H0) for closure: the target contains a call to an undefined function. -/
theorem undefined_instance_breaks_closure :
    EdgesIn (edgesM Pundef (stdCfg Pundef)) [.inst 5 [], .inst 0 []] ∧
    CoversRefs Pundef.sig (stdCfg Pundef).E ∧ SynthTotal (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    CanonicalRefs Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    ¬ InstDefined Pundef [.inst 5 [], .inst 0 []] ∧
    ¬ Closed Pundef.sig (tableM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []]) [.inst 5 [], .inst 0 []] := by
  exact ⟨by decide, stdCfg_covers Pundef, by decide, by decide, by decide, by decide⟩

/-- The adequacy theorem does not assume closedness: on `Pundef` every hypothesis of the adequacy
theorem holds for a target that is not closed, and the mono and source runs agree by both ending
in the same link error. -/
theorem adequacy_holds_on_nonclosed_target :
    ¬ Closed Pundef.sig (tableM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []])
        [.inst 5 [], .inst 0 []] ∧
    RootsIn [.inst 0 []] [.inst 5 [], .inst 0 []] ∧
    EdgesIn (edgesM Pundef (stdCfg Pundef)) [.inst 5 [], .inst 0 []] ∧
    CoversRefs Pundef.sig (stdCfg Pundef).E ∧
    SynthAgrees Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    CanonicalKeys Pundef [.inst 5 [], .inst 0 []] ∧
    CanonicalRefs Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] n r st = runS Pundef n r st) ∧
    runM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] 3 (.inst 0 []) st0
      = (.link (.inst 5 []), st0) ∧
    runS Pundef 3 (.inst 0 []) st0 = (.link (.inst 5 []), st0) := by
  refine ⟨by decide, by decide, by decide, stdCfg_covers Pundef, synthStd_agrees Pundef _,
    by decide, by decide, ?_, by decide, by decide⟩
  exact runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical Pundef (stdCfg Pundef)
    [.inst 0 []] [.inst 5 [], .inst 0 []]
    (by decide) (by decide) (stdCfg_covers Pundef) (synthStd_agrees Pundef _) (by decide) (by decide)

/-- A synthesizer that synthesizes nothing. -/
def cfgNoSynth (P : Program) : MonoCfg := ⟨refs P.sig, fun _ => none⟩

/-- Tightness of (H2t) for closure: a synthesizer that is not total on the shim keys of the
target. -/
theorem partial_synth_breaks_closure :
    collect (edgesM P2a (cfgNoSynth P2a)) fifo [.inst 0 []] 10 =
      some [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    EdgesIn (edgesM P2a (cfgNoSynth P2a)) [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    CoversRefs P2a.sig (cfgNoSynth P2a).E ∧
    ¬ SynthTotal (cfgNoSynth P2a) [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    CanonicalRefs P2a (cfgNoSynth P2a) [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    InstDefined P2a [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    ¬ Closed P2a.sig (tableM P2a (cfgNoSynth P2a) [.dropGlue (.base 1), .inst 1 [], .inst 0 []])
      [.dropGlue (.base 1), .inst 1 [], .inst 0 []] := by
  exact ⟨by decide, by decide, fun _ _ h => h, by decide, by decide, by decide, by decide⟩

/-- (H2t) is derivable from (H2) when the source defines the shim keys of `T`; it is stated
separately because closure does not need the equivalence part of (H2). -/
theorem synthTotal_of_synthAgrees (P : Program) (cfg : MonoCfg) (T : List Key)
    (h2 : SynthAgrees P cfg T) (hdef : ∀ k ∈ T, k.isShim = true → (srcDef0 P k).isSome) :
    SynthTotal cfg T := by
  intro k hk hs
  have h := h2 k hk hs
  have hd := hdef k hk hs
  rcases hsy : cfg.synth k with _ | b <;> rcases hsd : srcDef0 P k with _ | b' <;>
    simp_all [OptEquiv]

end Toy.MonoShim
