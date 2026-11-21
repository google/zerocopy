import MonoShim.SourceOnlyExamples

/-!
# Canonical keys and per-unit synthesis
-/

namespace Toy.MonoShim

/-- `main` calls `g::<base 0>`; the generic `g<T>` calls `h::<<T as 0>::Out>`; `h` emits 9; and
`<base 0 as 0>::Out = base 1`. Instantiating `g` at `base 0` normalizes its reference to
`h::<base 1>`, the key the collector records. -/
def P6 : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.proj 0 (.param 0)]⟩, ⟨false, .emit 9⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]

def T6 : List Key := [.inst 2 [.base 1], .inst 1 [.base 0], .inst 0 []]

theorem stdCfg_covers (P : Program) : CoversRefs P.sig (stdCfg P).E := fun _ _ h => h

/-! ## Normal forms are preserved by the standard pipeline -/

theorem key_norm_idem_of_assocNormal (P : Program) (h : assocNormal P = true) :
    ∀ k : Key, (k.norm P).norm P = k.norm P := by
  intro k
  cases k <;> simp [Key.norm, List.map_map, Function.comp_def, ty_norm_idem_of_assocNormal P h]

theorem cloneKey_norm_of_norm (P : Program) (t : Ty) (ht : t.norm P.assoc = t) :
    (cloneKey t).norm P = cloneKey t := by
  cases t <;> simp_all [cloneKey, Key.norm]

theorem reifyKey_norm_of_norm (P : Program) (sig : Sig) (f : Nat) (τs : List Ty)
    (hτ : τs.map (Ty.norm P.assoc) = τs) : (reifyKey sig f τs).norm P = reifyKey sig f τs := by
  unfold reifyKey
  split <;> simp [Key.norm, hτ]

/-- Under `assocNormal`, every runtime reference of a normalized statement is in normal form. -/
theorem refs_norm_canonical (P : Program) (h : assocNormal P = true) :
    ∀ s : Stmt, ∀ k' ∈ refs P.sig (s.norm P), k'.norm P = k' := by
  have hT := ty_norm_idem_of_assocNormal P h
  have hL : ∀ τs : List Ty, (τs.map (Ty.norm P.assoc)).map (Ty.norm P.assoc) =
      τs.map (Ty.norm P.assoc) := by
    intro τs; simp [List.map_map, Function.comp_def, hT]
  intro s
  induction s with
  | seq a b iha ihb =>
    intro k' hk'; simp only [Stmt.norm, refs, List.mem_append] at hk'
    rcases hk' with hk' | hk'; exact iha k' hk'; exact ihb k' hk'
  | onUnwind a b iha ihb =>
    intro k' hk'; simp only [Stmt.norm, refs, List.mem_append] at hk'
    rcases hk' with hk' | hk'; exact iha k' hk'; exact ihb k' hk'
  | guard s ih => intro k' hk'; exact ih k' (by simpa [Stmt.norm, refs] using hk')
  | call f τs => intro k' hk'; simp [Stmt.norm, refs] at hk'; subst hk'; simp [Key.norm, hL]
  | invoke k =>
    intro k' hk'; simp [Stmt.norm, refs] at hk'; subst hk'
    exact key_norm_idem_of_assocNormal P h k
  | mcall tr m t => intro k' hk'; simp [Stmt.norm, refs] at hk'; subst hk'; simp [Key.norm, hT]
  | drop t => intro k' hk'; simp [Stmt.norm, refs] at hk'; subst hk'; simp [Key.norm, hT]
  | clone t =>
    intro k' hk'; simp [Stmt.norm, refs] at hk'; subst hk'
    exact cloneKey_norm_of_norm P _ (hT t)
  | reify j f τs =>
    intro k' hk'; simp [Stmt.norm, refs] at hk'; subst hk'
    exact reifyKey_norm_of_norm P _ f _ (hL τs)
  | unsize j t tr =>
    intro k' hk'
    simp only [Stmt.norm, refs, vtEntries, List.map_map, List.mem_append, List.mem_map,
      List.mem_singleton, Function.comp_def] at hk'
    rcases hk' with ⟨m, _, rfl⟩ | rfl <;> simp [Key.norm, hT]
  | cloneAgg ts =>
    intro k' hk'
    simp only [Stmt.norm, refs, List.map_map, List.mem_append, List.mem_map,
      Function.comp_def] at hk'
    rcases hk' with ⟨t, _, rfl⟩ | ⟨t, _, rfl⟩
    · exact cloneKey_norm_of_norm P _ (hT t)
    · simp [Key.norm, hT]
  | skip => intro k' hk'; simp [Stmt.norm, refs] at hk'
  | emit _ => intro k' hk'; simp [Stmt.norm, refs] at hk'
  | panic => intro k' hk'; simp [Stmt.norm, refs] at hk'
  | callPtr _ => intro k' hk'; simp [Stmt.norm, refs] at hk'
  | callDyn _ _ => intro k' hk'; simp [Stmt.norm, refs] at hk'
  | dropDyn _ => intro k' hk'; simp [Stmt.norm, refs] at hk'

theorem norm_box_inv (A : List (Nat × Ty × Ty)) (t : Ty) (h : (Ty.box t).norm A = .box t) :
    t.norm A = t := by
  simpa [Ty.norm] using h

theorem norm_pair_inv (A : List (Nat × Ty × Ty)) (a b : Ty) (h : (Ty.pair a b).norm A = .pair a b) :
    a.norm A = a ∧ b.norm A = b := by
  simpa [Ty.norm] using h

/-- **(H3b) for the standard pipeline.** If every right-hand side of `P.assoc` is in normal form
(`assocNormal`) and every key of `T` is in normal form (H3a), then every key referenced by a body
the standard pipeline emits for a key of `T` is in normal form. -/
theorem canonicalRefs_stdCfg_of_assocNormal (P : Program) (T : List Key)
    (hA : assocNormal P = true) (h3a : CanonicalKeys P T) : CanonicalRefs P (stdCfg P) T := by
  intro k hk b hb k' hk'
  have hkn := h3a k hk
  have hR := refs_norm_canonical P hA
  cases k with
  | inst f τs =>
    simp only [bodyM, Key.isShim, Bool.false_eq_true, ite_false, srcDef0] at hb
    rcases hf : P.fns[f]? with _ | fd <;> rw [hf] at hb <;> simp at hb
    subst hb; exact hR _ k' hk'
  | meth tr m t =>
    simp only [bodyM, Key.isShim, Bool.false_eq_true, ite_false, srcDef0] at hb
    rcases hl : implLookup P tr m t with _ | b0 <;> rw [hl] at hb <;> simp at hb
    subst hb; exact hR _ k' hk'
  | userDrop n =>
    simp only [bodyM, Key.isShim, Bool.false_eq_true, ite_false, srcDef0] at hb
    rcases hl : natLookup P.dropImpls n with _ | b0 <;> rw [hl] at hb <;> simp at hb
    subst hb; exact hR _ k' hk'
  | userClone n =>
    simp only [bodyM, Key.isShim, Bool.false_eq_true, ite_false, srcDef0] at hb
    rcases hl : natLookup P.cloneImpls n with _ | b0 <;> rw [hl] at hb <;> simp at hb
    subst hb; exact hR _ k' hk'
  | dropGlue t =>
    simp only [bodyM, Key.isShim, ite_true, stdCfg, synthStd] at hb
    have ht : t.norm P.assoc = t := by simpa [Key.norm] using hkn
    cases t with
    | base n =>
      simp only [glueSrc] at hb
      split at hb <;> simp at hb <;> subst hb <;> simp [refs] at hk'
      subst hk'; rfl
    | box t0 =>
      simp only [glueSrc] at hb; simp at hb; subst hb
      simp [refs] at hk'; subst hk'; simp [Key.norm, norm_box_inv _ _ ht]
    | pair a0 b0 =>
      simp only [glueSrc] at hb; simp at hb; subst hb
      have hab := norm_pair_inv _ _ _ ht
      simp [refs] at hk'
      rcases hk' with rfl | rfl | rfl <;> simp [Key.norm, hab.1, hab.2]
    | fnPtr => simp only [glueSrc] at hb; simp at hb; subst hb; simp [refs] at hk'
    | dyn _ => simp [glueSrc] at hb
    | param _ => simp [glueSrc] at hb
    | proj _ _ => simp [glueSrc] at hb
  | cloneShim t =>
    simp only [bodyM, Key.isShim, ite_true, stdCfg] at hb
    have ht : t.norm P.assoc = t := by simpa [Key.norm] using hkn
    cases t with
    | pair a0 b0 =>
      simp only [synthStd] at hb; simp at hb; subst hb
      have hab := norm_pair_inv _ _ _ ht
      simp [ladder, refs] at hk'
      rcases hk' with rfl | rfl | rfl | rfl
      · exact cloneKey_norm_of_norm P _ hab.1
      · exact cloneKey_norm_of_norm P _ hab.2
      · simp [Key.norm, hab.2]
      · simp [Key.norm, hab.1]
    | fnPtr => simp only [synthStd] at hb; simp at hb; subst hb; simp [refs] at hk'
    | base _ => simp [synthStd] at hb
    | box _ => simp [synthStd] at hb
    | dyn _ => simp [synthStd] at hb
    | param _ => simp [synthStd] at hb
    | proj _ _ => simp [synthStd] at hb
  | reifyShim f τs =>
    simp only [bodyM, Key.isShim, ite_true, stdCfg, synthStd] at hb
    have hτ : τs.map (Ty.norm P.assoc) = τs := by simpa [Key.norm] using hkn
    rcases hf : P.fns[f]? with _ | fd <;> rw [hf] at hb <;> simp at hb
    subst hb; simp [refs] at hk'; subst hk'; simp [Key.norm, hτ]

/-- Under `assocNormal`, every key the collector records along an edge is in normal form; hence a
target that the collector returns, when run with an admissible scheduler from canonical roots, satisfies (H3a). -/
theorem collect_canonicalKeys_of_assocNormal (P : Program) (cfg : MonoCfg)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key)
    (fuel : Nat) (T : List Key) (hc : collect (edgesM P cfg) sched roots fuel = some T)
    (hA : assocNormal P = true) (hR : CanonicalKeys P roots) : CanonicalKeys P T := by
  intro k hk
  have hr := (collect_mem_iff_reach _ sched hs roots fuel T hc k).mp hk
  induction hr with
  | root h => exact hR _ h
  | step _ he _ =>
    simp only [edgesM] at he
    split at he
    · obtain ⟨k0, _, rfl⟩ := List.mem_map.mp he
      exact key_norm_idem_of_assocNormal P hA k0
    · simp at he

/-- **End-to-end: the standard pipeline from canonical roots.** If `P.assoc` is normal
(`assocNormal`), the roots are in normal form, the standard collector (with an admissible
scheduler) returns `T`, the standard synthesizer is defined on the shim keys of `T` (H2t) and the
source defines its other keys (H0), then the table restricted to `T` is closed and agrees with the
source semantics on every run from every root. -/
theorem collect_stdCfg_closed_and_adequate_of_assocNormal (P : Program)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key)
    (fuel : Nat) (T : List Key) (hc : collect (edgesM P (stdCfg P)) sched roots fuel = some T)
    (hA : assocNormal P = true) (hR : CanonicalKeys P roots) (h2t : SynthTotal (stdCfg P) T)
    (h0 : InstDefined P T) :
    Closed P.sig (tableM P (stdCfg P) T) T ∧
      ∀ r ∈ roots, ∀ (n : Nat) (st : St), runM P (stdCfg P) T n r st = runS P n r st := by
  obtain ⟨hRin, hE⟩ := collect_rootsIn_edgesIn _ sched hs roots fuel T hc
  have h3a := collect_canonicalKeys_of_assocNormal P (stdCfg P) sched hs roots fuel T hc hA hR
  have h3b := canonicalRefs_stdCfg_of_assocNormal P T hA h3a
  exact ⟨closed_of_edgesIn_covering_total_canonicalRefs_instDefined P (stdCfg P) T hE
      (stdCfg_covers P) h2t h3b h0,
    runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical P (stdCfg P) roots T hRin hE
      (stdCfg_covers P) (synthStd_agrees P T) h3a h3b⟩

/-! ## A chained table, on which one normalization pass is not idempotent, can break closure -/

/-- As `P6`, but the associated-type table is chained: `<base 0 as 0>::Out = <base 0 as 1>::Out`
and `<base 0 as 1>::Out = base 1`. One normalization pass turns `<base 0 as 0>::Out` into
`<base 0 as 1>::Out`, which is not in normal form (`assocNormal P6chain = false`). -/
def P6chain : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.proj 0 (.param 0)]⟩, ⟨false, .emit 9⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .proj 1 (.base 0)), (1, .base 0, .base 1)]

/-- **A chained table, on which one normalization pass is not idempotent, can break closure** (tightness witness for H3b). Every other
hypothesis of the closure and adequacy theorems holds, but the instantiated body of `g::<base 0>`
references the once-normalized key `h::<<base 0 as 1>::Out>`, while the collector records the
twice-normalized key `h::<base 1>`. -/
theorem noncanonical_refs_break_closure :
    assocNormal P6chain = false ∧
    collect (edgesM P6chain (stdCfg P6chain)) fifo [.inst 0 []] 10 = some T6 ∧
    CoversRefs P6chain.sig (stdCfg P6chain).E ∧ RootsIn [.inst 0 []] T6 ∧
    EdgesIn (edgesM P6chain (stdCfg P6chain)) T6 ∧
    SynthAgrees P6chain (stdCfg P6chain) T6 ∧ SynthTotal (stdCfg P6chain) T6 ∧
    InstDefined P6chain T6 ∧ CanonicalKeys P6chain T6 ∧ ¬ CanonicalRefs P6chain (stdCfg P6chain) T6 ∧
    ¬ Closed P6chain.sig (tableM P6chain (stdCfg P6chain) T6) T6 ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P6chain (stdCfg P6chain) T6 n r st = runS P6chain n r st) ∧
    runM P6chain (stdCfg P6chain) T6 4 (.inst 0 []) st0 =
      (.link (.inst 2 [.proj 1 (.base 0)]), st0) ∧
    runS P6chain 4 (.inst 0 []) st0 = (.ok, ⟨[9], 0⟩) := by
  exact ⟨by decide, by decide, stdCfg_covers P6chain, by decide, by decide,
    synthStd_agrees P6chain T6, by decide, by decide, by decide, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 4) (st := st0) (by decide), by decide, by decide⟩

/-- Positive control: on `P6` itself (whose table is normal) the standard pipeline collects a
closed target on which the mono and source semantics agree at every fuel and state. -/
theorem canonical_refs_close_positive_control :
    assocNormal P6 = true ∧
    collect (edgesM P6 (stdCfg P6)) fifo [.inst 0 []] 10 = some T6 ∧
    CanonicalKeys P6 T6 ∧ CanonicalRefs P6 (stdCfg P6) T6 ∧
    Closed P6.sig (tableM P6 (stdCfg P6) T6) T6 ∧
    ∀ (n : Nat) (st : St), runM P6 (stdCfg P6) T6 n (.inst 0 []) st = runS P6 n (.inst 0 []) st := by
  have hc : collect (edgesM P6 (stdCfg P6)) fifo [.inst 0 []] 10 = some T6 := by decide
  have hA : assocNormal P6 = true := by decide
  obtain ⟨hC, hrun⟩ := collect_stdCfg_closed_and_adequate_of_assocNormal P6 fifo fifo_ok
    [.inst 0 []] 10 T6 hc hA (by decide) (by decide) (by decide)
  exact ⟨hA, hc, by decide, by decide, hC, fun n st => hrun _ (by simp) n st⟩

/-- `<base 0 as 0>::Out = base 1` (a normal table); no functions. -/
def Pnc0 : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]

/-- Tightness of (H3a) for `canonicalRefs_stdCfg_of_assocNormal`: the table is normal, but the
target key `dropGlue (Box<<base 0 as 0>::Out>)` is not in normal form, and its glue references the
unnormalized key `dropGlue (<base 0 as 0>::Out)`. -/
theorem noncanonical_key_breaks_canonicalRefs :
    assocNormal Pnc0 = true ∧ ¬ CanonicalKeys Pnc0 [.dropGlue (.box (.proj 0 (.base 0)))] ∧
    ¬ CanonicalRefs Pnc0 (stdCfg Pnc0) [.dropGlue (.box (.proj 0 (.base 0)))] := by
  decide

/-! ## Per-unit synthesis -/

def glueKey4a : Key := .dropGlue (.pair (.base 0) (.base 1))

/-- Two codegen units for `P4a`: unit A emits `main` and its own copy of the pair's glue with the
standard synthesizer; unit B emits the remaining glue and user drops, plus another copy of the
pair's glue. -/
def unitA (sy : Key → Option Stmt) : List Key × (Key → Option Stmt) := ([.inst 0 [], glueKey4a], sy)
def unitB (sy : Key → Option Stmt) : List Key × (Key → Option Stmt) :=
  ([glueKey4a, .dropGlue (.base 0), .dropGlue (.base 1), .userDrop 0, .userDrop 1], sy)

/-- Non-vacuity of the per-unit theorem: with the standard synthesizer in both units, the units
are deterministic and cover `T4a`, so the linked table equals the single-target table. -/
theorem deterministic_units_example :
    DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthStd P4a)] ∧
    UnitsCover [unitA (synthStd P4a), unitB (synthStd P4a)] T4a ∧
    ∀ k, linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a), unitB (synthStd P4a)] k =
      tableM P4a (stdCfg P4a) T4a k := by
  have hdet : DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthStd P4a)] := by
    intro u hu k _ _
    simp at hu
    rcases hu with rfl | rfl <;> rfl
  have hcov : UnitsCover [unitA (synthStd P4a), unitB (synthStd P4a)] T4a := by
    intro k
    constructor
    · intro h
      simp only [T4a, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨unitB (synthStd P4a), by simp, by decide⟩
      · exact ⟨unitB (synthStd P4a), by simp, by decide⟩
      · exact ⟨unitB (synthStd P4a), by simp, by decide⟩
      · exact ⟨unitB (synthStd P4a), by simp, by decide⟩
      · exact ⟨unitA (synthStd P4a), by simp, by decide⟩
      · exact ⟨unitA (synthStd P4a), by simp, by decide⟩
    · rintro ⟨u, hu, hk⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · simp only [unitA, glueKey4a, List.mem_cons, List.mem_nil_iff, or_false] at hk
        rcases hk with rfl | rfl <;> decide
      · simp only [unitB, glueKey4a, List.mem_cons, List.mem_nil_iff, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨hdet, hcov, linkUnits_eq_tableM_of_deterministic P4a (refs P4a.sig) (synthStd P4a) T4a _ hdet hcov⟩

/-- **Non-deterministic per-unit synthesis makes the linked program depend on link order**
(tightness witness for the determinism hypothesis): if unit B synthesizes the pair's glue in
reverse declaration order, linking A before B and B before A give different event traces. -/
theorem nondeterministic_units_link_order_matters :
    ¬ DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthRev P4a)] ∧
    runKey P4a.sig (linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a), unitB (synthRev P4a)])
      4 (.inst 0 []) st0 = (.ok, ⟨[10, 20], 0⟩) ∧
    runKey P4a.sig (linkUnits P4a (refs P4a.sig) [unitB (synthRev P4a), unitA (synthStd P4a)])
      4 (.inst 0 []) st0 = (.ok, ⟨[20, 10], 0⟩) := by
  refine ⟨?_, by decide, by decide⟩
  intro h
  have := h (unitB (synthRev P4a)) (by simp) glueKey4a (by simp [unitB]) rfl
  revert this; decide

end Toy.MonoShim
