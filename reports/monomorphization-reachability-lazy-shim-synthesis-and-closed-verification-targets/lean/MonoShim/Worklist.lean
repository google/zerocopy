import MonoShim.Adequacy

/-!
# Worklist collection: least fixpoint, order independence, on-demand synthesis, per-unit linking
-/

namespace Toy.MonoShim

theorem collectGo_sound (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (hs : SchedOK sched) (R : Key → Prop) (hR : ∀ k, R k → ∀ k' ∈ edges k, R k') :
    ∀ (n : Nat) (work done T : List Key), collectGo edges sched n work done = some T →
      (∀ k ∈ work, R k) → (∀ k ∈ done, R k) → ∀ k ∈ T, R k := by
  intro n
  induction n with
  | zero => intro work done T h; simp [collectGo] at h
  | succ n ih =>
    intro work done T h hw hd
    cases work with
    | nil => simp [collectGo] at h; subst h; exact hd
    | cons k work =>
      simp only [collectGo] at h
      by_cases hk : k ∈ done
      · simp only [hk, ite_true] at h
        exact ih work done T h (fun k' h' => hw k' (by simp [h'])) hd
      · simp only [hk, ite_false] at h
        apply ih _ _ T h
        · intro k' h'
          rcases (hs work (edges k) k').mp h' with h' | h'
          · exact hw k' (by simp [h'])
          · exact hR k (hw k (by simp)) k' h'
        · intro k' h'
          rcases List.mem_cons.mp h' with rfl | h'
          · exact hw _ (by simp)
          · exact hd k' h'

theorem collectGo_complete (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (hs : SchedOK sched) :
    ∀ (n : Nat) (work done T : List Key), collectGo edges sched n work done = some T →
      (∀ k ∈ done, ∀ k' ∈ edges k, k' ∈ work ∨ k' ∈ done) →
      (∀ k ∈ done, k ∈ T) ∧ (∀ k ∈ work, k ∈ T) ∧ (∀ k ∈ T, ∀ k' ∈ edges k, k' ∈ T) := by
  intro n
  induction n with
  | zero => intro work done T h; simp [collectGo] at h
  | succ n ih =>
    intro work done T h hinv
    cases work with
    | nil =>
      simp [collectGo] at h; subst h
      refine ⟨fun k hk => hk, by simp, ?_⟩
      intro k hk k' hk'
      rcases hinv k hk k' hk' with h | h
      · simp at h
      · exact h
    | cons k work =>
      simp only [collectGo] at h
      by_cases hk : k ∈ done
      · simp only [hk, ite_true] at h
        have hinv' : ∀ k0 ∈ done, ∀ k' ∈ edges k0, k' ∈ work ∨ k' ∈ done := by
          intro k0 hk0 k' hk'
          rcases hinv k0 hk0 k' hk' with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr hk
            · exact Or.inl h
          · exact Or.inr h
        obtain ⟨h1, h2, h3⟩ := ih work done T h hinv'
        refine ⟨h1, ?_, h3⟩
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact h1 _ hk
        · exact h2 k' hk'
      · simp only [hk, ite_false] at h
        have hinv' : ∀ k0 ∈ k :: done, ∀ k' ∈ edges k0,
            k' ∈ sched work (edges k) ∨ k' ∈ k :: done := by
          intro k0 hk0 k' hk'
          rcases List.mem_cons.mp hk0 with rfl | hk0
          · exact Or.inl ((hs work (edges k0) k').mpr (Or.inr hk'))
          · rcases hinv k0 hk0 k' hk' with h | h
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr (by simp)
              · exact Or.inl ((hs work (edges k) k').mpr (Or.inl h))
            · exact Or.inr (List.mem_cons_of_mem _ h)
        obtain ⟨h1, h2, h3⟩ := ih _ _ T h hinv'
        refine ⟨fun k' hk' => h1 k' (List.mem_cons_of_mem _ hk'), ?_, h3⟩
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact h1 _ (by simp)
        · exact h2 k' ((hs work (edges k) k').mpr (Or.inl hk'))

/-- **Least fixpoint, any order.** For every admissible scheduler, if the worklist collector
terminates with `T`, then `T` has exactly the keys reachable from the roots. -/
theorem collect_mem_iff_reach (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (hs : SchedOK sched) (roots : List Key) (fuel : Nat) (T : List Key)
    (h : collect edges sched roots fuel = some T) :
    ∀ k, k ∈ T ↔ Reach edges roots k := by
  intro k
  constructor
  · intro hk
    refine collectGo_sound edges sched hs (Reach edges roots) ?_ fuel roots [] T h ?_ (by simp) k hk
    · intro k hk k' hk'; exact Reach.step hk hk'
    · intro k hk; exact Reach.root hk
  · intro hr
    obtain ⟨_, h2, h3⟩ := collectGo_complete edges sched hs fuel roots [] T h (by simp)
    induction hr with
    | root h => exact h2 _ h
    | step _ he ih => exact h3 _ ih _ he

/-- With an admissible scheduler, the collector's output satisfies the root and edge-closure
hypotheses of the adequacy theorem. -/
theorem collect_rootsIn_edgesIn (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (hs : SchedOK sched) (roots : List Key) (fuel : Nat) (T : List Key)
    (h : collect edges sched roots fuel = some T) : RootsIn roots T ∧ EdgesIn edges T := by
  obtain ⟨_, h2, h3⟩ := collectGo_complete edges sched hs fuel roots [] T h (by simp)
  exact ⟨h2, h3⟩

theorem fifo_ok : SchedOK fifo := by intro w n x; simp [fifo]
theorem lifo_ok : SchedOK lifo := by intro w n x; simp [lifo, or_comm]

/-- **Order independence.** Two admissible schedulers that both terminate collect the same key
set. -/
theorem collect_order_independent (edges : Key → List Key) (s1 s2 : List Key → List Key → List Key)
    (hs1 : SchedOK s1) (hs2 : SchedOK s2) (roots : List Key) (n1 n2 : Nat) (T1 T2 : List Key)
    (h1 : collect edges s1 roots n1 = some T1) (h2 : collect edges s2 roots n2 = some T2) :
    ∀ k, k ∈ T1 ↔ k ∈ T2 := by
  intro k
  rw [collect_mem_iff_reach edges s1 hs1 roots n1 T1 h1, collect_mem_iff_reach edges s2 hs2 roots n2 T2 h2]

/-- Reachability depends only on the edge function at reachable keys. -/
theorem reach_congr (e1 e2 : Key → List Key) (roots : List Key)
    (h : ∀ k, Reach e1 roots k → e1 k = e2 k) : ∀ k, Reach e1 roots k ↔ Reach e2 roots k := by
  intro k
  constructor
  · intro hr
    induction hr with
    | root h => exact Reach.root h
    | step hr he ih => exact Reach.step ih (by rw [← h _ hr]; exact he)
  · intro hr
    induction hr with
    | root h => exact Reach.root h
    | step _ he ih => exact Reach.step ih (by rw [h _ ih]; exact he)

/-- A precomputed shim table, consulted instead of calling the synthesizer on demand. -/
def preCfg (E : Stmt → List Key) (pre : List (Key × Stmt)) : MonoCfg := ⟨E, fun k => pre.lookup k⟩

/-- **Precomputed and on-demand synthesis collect the same key set.** If a precomputed shim
table agrees with the synthesizer on every shim key reachable under the on-demand pipeline, then (for any admissible
schedulers that terminate) both pipelines collect the same keys and emit the same table. -/
theorem precomputed_and_on_demand_synthesis_same_target (P : Program) (E : Stmt → List Key)
    (synth : Key → Option Stmt) (pre : List (Key × Stmt)) (roots : List Key)
    (s1 s2 : List Key → List Key → List Key) (hs1 : SchedOK s1) (hs2 : SchedOK s2)
    (n1 n2 : Nat) (T1 T2 : List Key)
    (hpre : ∀ k, Reach (edgesM P ⟨E, synth⟩) roots k → k.isShim = true → pre.lookup k = synth k)
    (c1 : collect (edgesM P ⟨E, synth⟩) s1 roots n1 = some T1)
    (c2 : collect (edgesM P (preCfg E pre)) s2 roots n2 = some T2) :
    (∀ k, k ∈ T1 ↔ k ∈ T2) ∧ ∀ k, tableM P ⟨E, synth⟩ T1 k = tableM P (preCfg E pre) T2 k := by
  have hbody : ∀ k, Reach (edgesM P ⟨E, synth⟩) roots k →
      bodyM P ⟨E, synth⟩ k = bodyM P (preCfg E pre) k := by
    intro k hk
    by_cases hs : k.isShim = true
    · simp [bodyM, hs, preCfg, hpre k hk hs]
    · simp [bodyM, hs]
  have hedge : ∀ k, Reach (edgesM P ⟨E, synth⟩) roots k →
      edgesM P ⟨E, synth⟩ k = edgesM P (preCfg E pre) k := by
    intro k hk
    simp only [edgesM, hbody k hk]
    rfl
  have hmem : ∀ k, k ∈ T1 ↔ k ∈ T2 := by
    intro k
    rw [collect_mem_iff_reach _ s1 hs1 roots n1 T1 c1, collect_mem_iff_reach _ s2 hs2 roots n2 T2 c2]
    exact reach_congr _ _ roots hedge k
  refine ⟨hmem, ?_⟩
  intro k
  by_cases hk : k ∈ T1
  · have hr := (collect_mem_iff_reach _ s1 hs1 roots n1 T1 c1 k).mp hk
    simp [tableM, hk, (hmem k).mp hk, hbody k hr]
  · have hk2 : k ∉ T2 := fun h => hk ((hmem k).mpr h)
    simp [tableM, hk, hk2]

/-- Linking codegen units: each unit lists the keys it emits and carries the synthesizer it
uses; the linked table answers a key from the first unit that lists it. The edge-function
argument `E` does not affect the result (`bodyM` ignores `cfg.E`); it is present so that each unit
is a `MonoCfg`. Function-pointer or vtable addresses, symbol visibility and linker duplicate-symbol
errors are not modelled. -/
def linkUnits (P : Program) (E : Stmt → List Key) :
    List (List Key × (Key → Option Stmt)) → Key → Option Stmt
  | [], _ => none
  | (ks, sy) :: us, k => if k ∈ ks then bodyM P ⟨E, sy⟩ k else linkUnits P E us k

/-- Deterministic per-unit synthesis: every unit's synthesizer agrees with `synth` on the shim
keys that unit lists. -/
def DeterministicUnits (synth : Key → Option Stmt) (units : List (List Key × (Key → Option Stmt))) :
    Prop :=
  ∀ u ∈ units, ∀ k ∈ u.1, k.isShim = true → u.2 k = synth k

/-- The units together list exactly the keys of `T` (shim keys may be listed by several units). -/
def UnitsCover (units : List (List Key × (Key → Option Stmt))) (T : List Key) : Prop :=
  ∀ k, k ∈ T ↔ ∃ u ∈ units, k ∈ u.1

/-- **Per-unit duplication is harmless with deterministic synthesis.** If every unit's
synthesizer agrees with `synth` on the shim keys it lists, and the units together list exactly
`T`, the linked table equals the single-target table on `T`. -/
theorem linkUnits_eq_tableM_of_deterministic (P : Program) (E : Stmt → List Key)
    (synth : Key → Option Stmt) (T : List Key) (units : List (List Key × (Key → Option Stmt)))
    (hdet : DeterministicUnits synth units) (hcov : UnitsCover units T) :
    ∀ k, linkUnits P E units k = tableM P ⟨E, synth⟩ T k := by
  have key : ∀ (us : List (List Key × (Key → Option Stmt))), (∀ u ∈ us, u ∈ units) →
      ∀ k, linkUnits P E us k = if (∃ u ∈ us, k ∈ u.1) then bodyM P ⟨E, synth⟩ k else none := by
    intro us
    induction us with
    | nil => intro _ k; simp [linkUnits]
    | cons u us ih =>
      intro hsub k
      rcases u with ⟨ks, sy⟩
      by_cases hk : k ∈ ks
      · have hb : bodyM P ⟨E, sy⟩ k = bodyM P ⟨E, synth⟩ k := by
          by_cases hs : k.isShim = true
          · have hd : sy k = synth k := hdet (ks, sy) (hsub _ (by simp)) k hk hs
            simp [bodyM, hs, hd]
          · simp [bodyM, hs]
        have hex : ∃ u ∈ (ks, sy) :: us, k ∈ u.1 := ⟨(ks, sy), by simp, hk⟩
        simp [linkUnits, hk, hb]
      · rw [show linkUnits P E ((ks, sy) :: us) k = linkUnits P E us k by simp [linkUnits, hk]]
        rw [ih (fun u hu => hsub u (List.mem_cons_of_mem _ hu)) k]
        have e : (∃ u ∈ (ks, sy) :: us, k ∈ u.1) ↔ (∃ u ∈ us, k ∈ u.1) := by
          constructor
          · rintro ⟨u, hu, hku⟩
            rcases List.mem_cons.mp hu with rfl | hu
            · exact absurd hku hk
            · exact ⟨u, hu, hku⟩
          · rintro ⟨u, hu, hku⟩; exact ⟨u, List.mem_cons_of_mem _ hu, hku⟩
        simp only [e]
  intro k
  rw [key units (fun u hu => hu) k]
  by_cases h : ∃ u ∈ units, k ∈ u.1
  · simp [h, tableM, (hcov k).mpr h]
  · have : k ∉ T := fun hk => h ((hcov k).mp hk)
    simp only [h, ite_false, tableM, this]

end Toy.MonoShim
