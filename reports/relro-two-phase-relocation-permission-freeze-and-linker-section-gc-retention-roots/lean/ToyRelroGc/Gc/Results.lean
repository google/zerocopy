import ToyRelroGc.Gc.Model

/-!
Results 6 (GC soundness and granularity), 7 (start/stop registries) and 8 (two-stage
retention).
-/
namespace Toy.RelroGc

/-! ## Auxiliary lemmas -/

/-- Closed-set principle: a set containing the roots and closed under the edges contains every
reachable node. -/
theorem reach_closed (E : List (Nat × Nat)) (R S : Nat → Prop) (hR : ∀ i, R i → S i)
    (hE : ∀ e ∈ E, S e.1 → S e.2) : ∀ j, Reach E R j → S j := by
  intro j h
  induction h with
  | root hr => exact hR _ hr
  | step _ he ih => exact hE _ he ih

theorem isRootB_eq_false_of_ge (g : GcIn) (i : Nat) (h : g.secs.length ≤ i) :
    g.isRootB i = false := by
  simp [GcIn.isRootB, List.getElem?_eq_none h]

/-- Bounded closed-set check for GC liveness (used with `decide` on concrete inputs). -/
theorem live_closed (g : GcIn) (pol : SSPolicy) (S : Nat → Bool)
    (hR : ∀ i < g.secs.length, g.isRootB i = true → S i = true)
    (hE : ∀ e ∈ g.edges ++ g.ssEdges pol, S e.1 = true → S e.2 = true) :
    ∀ j, g.Live pol j → S j = true := by
  apply reach_closed _ _ (fun j => S j = true) _ hE
  intro i hi
  by_cases h : i < g.secs.length
  · exact hR i h hi
  · rw [GcIn.IsRoot, isRootB_eq_false_of_ge g i (by omega)] at hi
    exact absurd hi (by simp)

theorem mem_ssEdges_conservative (g : GcIn) (i j : Nat) :
    (i, j) ∈ g.ssEdges .conservative ↔
      ∃ X, (i, X) ∈ g.ss ∧ j < g.secs.length ∧ g.nameOf j = some X := by
  simp only [GcIn.ssEdges, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨i', X⟩, hss, j', ⟨hj, hn⟩, rfl, rfl⟩
    exact ⟨X, hss, hj, hn⟩
  · rintro ⟨X, hss, hj, hn⟩
    exact ⟨⟨i, X⟩, hss, j, ⟨hj, hn⟩, rfl, rfl⟩

theorem lt_of_nameOf_eq_some (g : GcIn) (j X : Nat) (h : g.nameOf j = some X) :
    j < g.secs.length := by
  unfold GcIn.nameOf at h
  cases hj : g.secs[j]? with
  | none => simp [hj] at h
  | some s => exact (List.getElem?_eq_some_iff.mp hj).1

/-- Accessed sections are kept, by strong induction on the access position. -/
theorem reach_of_access (g : GcIn) (pol : SSPolicy) (run : List Acc)
    (h1 : EdgeAccessesFollowEdges g.edges g.IsRoot run)
    (h2 : ImplicitAccessesHitRoots g.IsRoot run) (h3 : BoundsAccessesRetained g pol run) :
    ∀ (k : Nat) (a : Acc), run[k]? = some a → g.Live pol a.dst := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have src : ∀ i, ReachedBefore g.IsRoot run k i → g.Live pol i := by
      rintro i (hr | ⟨k', hk', a', ha', hd⟩)
      · exact Reach.root hr
      · have := ih k' hk' a' ha'
        rw [hd] at this
        exact this
    intro a ha
    cases a with
    | implicit j => exact Reach.root (h2 k j ha)
    | edge i j =>
      obtain ⟨he, hsrc⟩ := h1 k i j ha
      exact Reach.step (src i hsrc) (List.mem_append_left _ he)
    | bounds i X j =>
      obtain ⟨hss, hn, hsrc, hpol⟩ := h3 k i X j ha
      rcases hpol with rfl | hr
      · exact Reach.step (src i hsrc) (List.mem_append_right _
          ((mem_ssEdges_conservative g i j).mpr ⟨X, hss, lt_of_nameOf_eq_some g j X hn, hn⟩))
      · exact Reach.root hr

/-! ## Result 6: GC soundness and granularity monotonicity -/

/-- **GC soundness under access completeness.** If (A1) every edge access of a run follows a
relocation edge from a root or from a section reached earlier in the run, (A2) every implicit
access reaches a root, and (A3) every bounds access comes from a root or an earlier-reached
section that references the bounds of `X`, reaches a section named `X`, and is retained by the
start/stop rule (conservative policy) or reaches a root, then every section the run accesses is
kept by GC. -/
theorem runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained
    (g : GcIn) (pol : SSPolicy) (run : List Acc)
    (h1 : EdgeAccessesFollowEdges g.edges g.IsRoot run)
    (h2 : ImplicitAccessesHitRoots g.IsRoot run)
    (h3 : BoundsAccessesRetained g pol run) : RunPreserved g pol run := by
  intro a ha
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
  exact reach_of_access g pol run h1 h2 h3 k a hk

theorem getElem?_append_singleton_cases {α : Type} (run : List α) (x : α) (k : Nat) (a : α)
    (h : (run ++ [x])[k]? = some a) :
    (k < run.length ∧ run[k]? = some a) ∨ (k = run.length ∧ a = x) := by
  by_cases hlt : k < run.length
  · rw [List.getElem?_append_left hlt] at h
    exact Or.inl ⟨hlt, h⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at h
    cases hsub : k - run.length with
    | zero =>
      rw [hsub] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact Or.inr ⟨by omega, h.symm⟩
    | succ m =>
      rw [hsub] at h
      simp at h

theorem reachedBefore_append (R : Nat → Prop) (run : List Acc) (x : Acc) (k i : Nat)
    (hk : k ≤ run.length) (h : ReachedBefore R run k i) : ReachedBefore R (run ++ [x]) k i := by
  rcases h with hr | ⟨k', hk', a, ha, hd⟩
  · exact Or.inl hr
  · exact Or.inr ⟨k', hk', a, by rw [List.getElem?_append_left (by omega)]; exact ha, hd⟩

theorem reachedBefore_append_end (R : Nat → Prop) (run : List Acc) (x : Acc) (i : Nat)
    (h : ∃ a ∈ run, a.dst = i) : ReachedBefore R (run ++ [x]) run.length i := by
  obtain ⟨a, ha, hd⟩ := h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
  have hlt : k < run.length := (List.getElem?_eq_some_iff.mp hk).1
  exact Or.inr ⟨k, hlt, a, by rw [List.getElem?_append_left hlt]; exact hk, hd⟩

/-- Every kept section is accessed by some run satisfying (A1)–(A3): a derivation of `Live`
linearizes into such a run (roots as implicit accesses, relocation edges as edge accesses, and
conservative start/stop edges as bounds accesses). -/
theorem exists_valid_run_of_live (g : GcIn) (pol : SSPolicy) (j : Nat) (h : g.Live pol j) :
    ∃ run : List Acc, EdgeAccessesFollowEdges g.edges g.IsRoot run ∧
      ImplicitAccessesHitRoots g.IsRoot run ∧ BoundsAccessesRetained g pol run ∧
      ∃ a ∈ run, a.dst = j := by
  unfold GcIn.Live at h
  induction h with
  | @root i hi =>
    refine ⟨[.implicit i], ?_, ?_, ?_, .implicit i, by simp, rfl⟩
    · intro k u v hk
      cases k <;> simp at hk
    · intro k v hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Acc.implicit.injEq] at hk
        subst hk; exact hi
      | succ n => simp at hk
    · intro k u X v hk
      cases k <;> simp at hk
  | @step i j _ he ih =>
    obtain ⟨run, h1, h2, h3, hreach⟩ := ih
    have keep2 : ∀ x : Acc, (∀ v, x ≠ Acc.implicit v) →
        ImplicitAccessesHitRoots g.IsRoot (run ++ [x]) := by
      intro x hx k v hk
      rcases getElem?_append_singleton_cases run x k _ hk with ⟨_, hk⟩ | ⟨_, hxe⟩
      · exact h2 k v hk
      · exact absurd hxe.symm (hx v)
    rcases List.mem_append.mp he with he | he
    · refine ⟨run ++ [.edge i j], ?_, keep2 _ (fun v h => by cases h), ?_, .edge i j, by simp,
        rfl⟩
      · intro k u v hk
        rcases getElem?_append_singleton_cases run _ k _ hk with ⟨hlt, hk⟩ | ⟨rfl, hx⟩
        · obtain ⟨he', hs⟩ := h1 k u v hk
          exact ⟨he', reachedBefore_append _ run _ k u (Nat.le_of_lt hlt) hs⟩
        · cases hx
          exact ⟨he, reachedBefore_append_end _ run _ i hreach⟩
      · intro k u X v hk
        rcases getElem?_append_singleton_cases run _ k _ hk with ⟨hlt, hk⟩ | ⟨_, hx⟩
        · obtain ⟨a1, a2, a3, a4⟩ := h3 k u X v hk
          exact ⟨a1, a2, reachedBefore_append _ run _ k u (Nat.le_of_lt hlt) a3, a4⟩
        · cases hx
    · cases pol with
      | precise => simp [GcIn.ssEdges] at he
      | conservative =>
        obtain ⟨X, hss, _, hn⟩ := (mem_ssEdges_conservative g i j).mp he
        refine ⟨run ++ [.bounds i X j], ?_, keep2 _ (fun v h => by cases h), ?_, .bounds i X j,
          by simp, rfl⟩
        · intro k u v hk
          rcases getElem?_append_singleton_cases run _ k _ hk with ⟨hlt, hk⟩ | ⟨_, hx⟩
          · obtain ⟨he', hs⟩ := h1 k u v hk
            exact ⟨he', reachedBefore_append _ run _ k u (Nat.le_of_lt hlt) hs⟩
          · cases hx
        · intro k u X' v hk
          rcases getElem?_append_singleton_cases run _ k _ hk with ⟨hlt, hk⟩ | ⟨rfl, hx⟩
          · obtain ⟨a1, a2, a3, a4⟩ := h3 k u X' v hk
            exact ⟨a1, a2, reachedBefore_append _ run _ k u (Nat.le_of_lt hlt) a3, a4⟩
          · cases hx
            exact ⟨hss, hn, reachedBefore_append_end _ run _ i hreach, Or.inl rfl⟩

/-- Liveness is exactly accessibility by a run satisfying (A1)–(A3): the converse of
`runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained`
is `exists_valid_run_of_live`. -/
theorem live_iff_exists_valid_run (g : GcIn) (pol : SSPolicy) (j : Nat) :
    g.Live pol j ↔
      ∃ run : List Acc, EdgeAccessesFollowEdges g.edges g.IsRoot run ∧
        ImplicitAccessesHitRoots g.IsRoot run ∧ BoundsAccessesRetained g pol run ∧
        ∃ a ∈ run, a.dst = j := by
  constructor
  · exact exists_valid_run_of_live g pol j
  · rintro ⟨run, h1, h2, h3, a, ha, rfl⟩
    exact runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained
      g pol run h1 h2 h3 a ha

/-- An entry section (root, name 0) and a plain section (name 1); `edges` given. -/
def gcPair (edges : List (Nat × Nat)) : GcIn where
  secs := [⟨0, true, false, false, false⟩, ⟨1, false, false, false, false⟩]
  edges := edges
  ss := []

instance (g : GcIn) (i : Nat) : Decidable (g.IsRoot i) :=
  inferInstanceAs (Decidable (g.isRootB i = true))

/-- Instance of result 6 (relocation edges): with edge `0 → 1`, the run "reach the entry, then
follow the edge" satisfies (A1), (A2) and (A3) under either policy. -/
theorem gcSoundness_nonvacuity (pol : SSPolicy) :
    EdgeAccessesFollowEdges (gcPair [(0, 1)]).edges (gcPair [(0, 1)]).IsRoot
        [.implicit 0, .edge 0 1] ∧
      ImplicitAccessesHitRoots (gcPair [(0, 1)]).IsRoot [.implicit 0, .edge 0 1] ∧
      BoundsAccessesRetained (gcPair [(0, 1)]) pol [.implicit 0, .edge 0 1] := by
  refine ⟨?_, ?_, ?_⟩
  · intro k i j hk
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Acc.edge.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨by simp [gcPair], Or.inl (by decide)⟩
    | n + 2, hk => simp at hk
  · intro k j hk
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Acc.implicit.injEq] at hk
      subst hk
      decide
    | 1, hk => simp at hk
    | n + 2, hk => simp at hk
  · intro k i X j hk
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk => simp at hk
    | n + 2, hk => simp at hk

theorem gcPair_not_live_one (pol : SSPolicy) : ¬ (gcPair []).Live pol 1 := by
  intro h
  have := live_closed (gcPair []) pol (fun i => i == 0) (by decide)
    (by cases pol <;> decide) 1 h
  exact absurd this (by decide)

/-- (A2) is tight: no edges, the run accesses the non-root section 1 implicitly; (A1) and (A3)
hold and section 1 is removed. -/
theorem gcSoundness_cex_implicit_access_to_nonroot (pol : SSPolicy) :
    EdgeAccessesFollowEdges (gcPair []).edges (gcPair []).IsRoot [.implicit 1] ∧
      ¬ ImplicitAccessesHitRoots (gcPair []).IsRoot [.implicit 1] ∧
      BoundsAccessesRetained (gcPair []) pol [.implicit 1] ∧
      ¬ RunPreserved (gcPair []) pol [.implicit 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k i j hk
    match k, hk with
    | 0, hk => simp at hk
    | n + 1, hk => simp at hk
  · intro h
    exact absurd (h 0 1 rfl) (by decide)
  · intro k i X j hk
    match k, hk with
    | 0, hk => simp at hk
    | n + 1, hk => simp at hk
  · intro h
    exact gcPair_not_live_one pol (h _ (List.mem_singleton_self _))

/-- (A1) is tight: no edges, the run reaches the entry and then accesses section 1 "through" a
non-existent edge `0 → 1`; (A2) and (A3) hold and section 1 is removed. -/
theorem gcSoundness_cex_edge_access_without_edge (pol : SSPolicy) :
    ¬ EdgeAccessesFollowEdges (gcPair []).edges (gcPair []).IsRoot [.implicit 0, .edge 0 1] ∧
      ImplicitAccessesHitRoots (gcPair []).IsRoot [.implicit 0, .edge 0 1] ∧
      BoundsAccessesRetained (gcPair []) pol [.implicit 0, .edge 0 1] ∧
      ¬ RunPreserved (gcPair []) pol [.implicit 0, .edge 0 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := (h 1 0 1 rfl).1
    simp [gcPair] at this
  · intro k j hk
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Acc.implicit.injEq] at hk
      subst hk
      decide
    | 1, hk => simp at hk
    | n + 2, hk => simp at hk
  · intro k i X j hk
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk => simp at hk
    | n + 2, hk => simp at hk
  · intro h
    exact gcPair_not_live_one pol (h (.edge 0 1) (by simp))

/-- Section reachability transfers along any map of sections. -/
theorem reach_secEdges_map (E : List (Nat × Nat)) (R : Nat → Prop) (sec f : Nat → Nat) :
    ∀ s, Reach (secEdges sec E) (secRoot sec R) s →
      Reach (secEdges (fun i => f (sec i)) E) (secRoot (fun i => f (sec i)) R) (f s) := by
  intro s h
  induction h with
  | root hr =>
    obtain ⟨i, hi, rfl⟩ := hr
    exact Reach.root ⟨i, hi, rfl⟩
  | step _ he ih =>
    refine Reach.step ih ?_
    simp only [secEdges, List.mem_map] at he ⊢
    obtain ⟨e, he, heq⟩ := he
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨e, he, rfl⟩

/-- **Coarsening never shrinks the kept item set.** If the section assignment `sec'` factors
through `sec` (`sec' i = f (sec i)` for a map `f` that merges sections), then every item kept
under `sec` is kept under `sec'`. -/
theorem keptItem_of_keptItem_of_coarsening (E : List (Nat × Nat)) (R : Nat → Prop)
    (sec sec' f : Nat → Nat) (hc : ∀ i, sec' i = f (sec i)) (i : Nat)
    (h : KeptItem sec E R i) : KeptItem sec' E R i := by
  have e : sec' = fun i => f (sec i) := funext hc
  subst e
  exact reach_secEdges_map E R sec f (sec i) h

/-- Items: 0 is the entry (root), 1 is referenced by 0, 2 is referenced by nothing. -/
def itemEdges : List (Nat × Nat) := [(0, 1)]

/-- Root items: only the entry item 0. -/
def itemRoot (i : Nat) : Prop := i = 0

/-- One item per section. -/
def secFine (i : Nat) : Nat := i

/-- Items 1 and 2 share section 1. -/
def secShared (i : Nat) : Nat := if i = 2 then 1 else i

/-- **"GC removes every unreferenced function" is false.** Item 2 is not referenced and not a
root; with its own section it is removed, but when it shares a section with the referenced
item 1 it is kept. This is also the counterexample showing that refining (as opposed to
coarsening) the partition can shrink the kept set. -/
theorem unreferenced_item_kept_when_sharing_live_section :
    (∀ e ∈ itemEdges, e.2 ≠ 2) ∧ ¬ itemRoot 2 ∧ KeptItem secShared itemEdges itemRoot 2 ∧
      ¬ KeptItem secFine itemEdges itemRoot 2 ∧ ¬ ∃ f : Nat → Nat, ∀ i, secFine i = f (secShared i) := by
  refine ⟨by decide, by simp [itemRoot], ?_, ?_, ?_⟩
  · show Reach _ _ (secShared 2)
    refine Reach.step (i := 0) (Reach.root ⟨0, rfl, rfl⟩) ?_
    simp [secEdges, itemEdges, secShared]
  · intro h
    have := reach_closed (secEdges secFine itemEdges) (secRoot secFine itemRoot)
      (fun s => s ≠ 2) (by rintro s ⟨i, hi, rfl⟩; simp [itemRoot] at hi; simp [hi, secFine])
      (by intro e he; simp [secEdges, itemEdges, secFine] at he; subst he; simp) _ h
    exact this rfl
  · rintro ⟨f, hf⟩
    have h1 := hf 1
    have h2 := hf 2
    simp [secFine, secShared] at h1 h2
    omega

/-- Instance of the coarsening result: `secShared` factors through `secFine` and item 1 is
kept under `secFine`. -/
theorem coarsening_nonvacuity :
    (∀ i, secShared i = secShared (secFine i)) ∧ KeptItem secFine itemEdges itemRoot 1 :=
  ⟨fun _ => rfl, Reach.step (i := 0) (Reach.root ⟨0, rfl, rfl⟩) (by simp [secEdges, itemEdges, secFine])⟩

/-! ## Result 7: implicit access and the start/stop rule -/

/-- **Precise start/stop policy drops unrooted registry entries.** If no relocation edge
reaches a section named `X` and no section named `X` is a root, then under the precise policy
no section named `X` is kept; if moreover a kept section references the bounds of `X`, the
bounds are undefined (link failure in the toy). -/
theorem precise_drops_unrooted_entries_of_noEdgeIntoName (g : GcIn) (X : Nat)
    (hN : NoEdgeIntoName g X) (hU : ∀ j, g.nameOf j = some X → ¬ g.IsRoot j) :
    (∀ j, g.nameOf j = some X → ¬ g.Live .precise j) ∧
      ((∃ i, g.Live .precise i ∧ (i, X) ∈ g.ss) → StartStopUndefined g .precise X) := by
  have key : ∀ j, g.Live .precise j → g.nameOf j ≠ some X := by
    apply reach_closed _ _ (fun j => g.nameOf j ≠ some X)
    · intro i hi hn
      exact hU i hn hi
    · intro e he
      simp only [GcIn.ssEdges, List.append_nil] at he
      intro _
      exact hN e he
  refine ⟨fun j hj hl => key j hl hj, fun href => ⟨href, fun j hj hl => key j hl hj⟩⟩

/-- **Conservative policy keeps the whole registry.** Under the conservative policy, if a kept
section references the bounds of `X`, every section named `X` is kept. -/
theorem conservative_registryKept_of_live_reference (g : GcIn) (X i : Nat)
    (hi : g.Live .conservative i) (hss : (i, X) ∈ g.ss) : RegistryKept g .conservative X := by
  intro j hj
  refine Reach.step hi (List.mem_append_right _ ?_)
  exact (mem_ssEdges_conservative g i j).mpr ⟨X, hss, lt_of_nameOf_eq_some g j X hj, hj⟩

/-- **Rooted registry entries are kept under either policy** (for instance when every entry
is matched by `KEEP` or carries the retain flag). -/
theorem registryKept_of_entries_rooted (g : GcIn) (pol : SSPolicy) (X : Nat)
    (h : ∀ j, g.nameOf j = some X → g.IsRoot j) : RegistryKept g pol X :=
  fun j hj => Reach.root (h j hj)

/-- **Characterization of a registry entry's survival.** If no relocation edge reaches a
section named `X` and section `j` is named `X`, then `j` is kept iff it is a root, or the policy
is conservative and some kept section references the bounds of `X`. -/
theorem live_iff_root_or_conservative_reference_of_noEdgeIntoName (g : GcIn) (pol : SSPolicy)
    (X j : Nat) (hN : NoEdgeIntoName g X) (hj : g.nameOf j = some X) :
    g.Live pol j ↔ g.IsRoot j ∨ (pol = .conservative ∧ ∃ i, g.Live pol i ∧ (i, X) ∈ g.ss) := by
  constructor
  · intro h
    unfold GcIn.Live at h
    cases h with
    | root hr => exact Or.inl hr
    | @step i _ hi he =>
      rcases List.mem_append.mp he with he | he
      · exact absurd hj (hN _ he)
      · cases pol with
        | precise => simp [GcIn.ssEdges] at he
        | conservative =>
          obtain ⟨X', hss, _, hn⟩ := (mem_ssEdges_conservative g i j).mp he
          rw [hj] at hn
          cases hn
          exact Or.inr ⟨rfl, i, hi, hss⟩
  · rintro (hr | ⟨rfl, i, hi, hss⟩)
    · exact Reach.root hr
    · exact conservative_registryKept_of_live_reference g X i hi hss j hj

/-- **GC keeps the whole registry iff every entry is rooted or covered by the conservative
rule.** If no relocation edge reaches a section named `X`, then every section named `X` is kept
iff, for every section `j` named `X`, either `j` is a root, or the policy is conservative and
some kept section references the bounds of `X`. -/
theorem registryKept_iff_of_noEdgeIntoName (g : GcIn) (pol : SSPolicy) (X : Nat)
    (hN : NoEdgeIntoName g X) :
    RegistryKept g pol X ↔
      ∀ j, g.nameOf j = some X →
        g.IsRoot j ∨ (pol = .conservative ∧ ∃ i, g.Live pol i ∧ (i, X) ∈ g.ss) := by
  constructor
  · intro h j hj
    exact (live_iff_root_or_conservative_reference_of_noEdgeIntoName g pol X j hN hj).mp (h j hj)
  · intro h j hj
    exact (live_iff_root_or_conservative_reference_of_noEdgeIntoName g pol X j hN hj).mpr (h j hj)

/-- **Registry scans and runs.** The run `registryScan g i X`, in which section `i` iterates the
bounds of `X` and reaches every section named `X`, is preserved by GC iff every section named
`X` is kept. -/
theorem runPreserved_registryScan_iff_registryKept (g : GcIn) (pol : SSPolicy) (i X : Nat) :
    RunPreserved g pol (registryScan g i X) ↔ RegistryKept g pol X := by
  unfold RunPreserved RegistryKept registryScan
  constructor
  · intro h j hj
    have hmem : Acc.bounds i X j ∈
        ((List.range g.secs.length).filter fun j => g.nameOf j == some X).map (Acc.bounds i X) := by
      simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨j, ⟨lt_of_nameOf_eq_some g j X hj, hj⟩, rfl⟩
    exact h _ hmem
  · intro h a ha
    simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq] at ha
    obtain ⟨j, ⟨_, hj⟩, rfl⟩ := ha
    exact h j hj

/-- A section record. -/
def mkSec (name : Nat) (entry keep retain : Bool) : Sec := ⟨name, entry, false, keep, retain⟩

/-- Registry `X = 7` with two entries (sections 1, 2), reached only through the bounds, which
the entry section 0 references; `edges` and entry flags given. -/
def gcReg (edges : List (Nat × Nat)) (keep retain : Bool) : GcIn where
  secs := [mkSec 0 true false false, mkSec 7 false keep retain, mkSec 7 false keep retain]
  edges := edges
  ss := [(0, 7)]

instance (g : GcIn) (X : Nat) : Decidable (NoEdgeIntoName g X) :=
  inferInstanceAs (Decidable (∀ e ∈ g.edges, g.nameOf e.2 ≠ some X))

theorem nameOf_gcReg_eq (edges : List (Nat × Nat)) (k r : Bool) (j : Nat)
    (h : (gcReg edges k r).nameOf j = some 7) : j = 1 ∨ j = 2 := by
  match j, h with
  | 0, h => simp [GcIn.nameOf, gcReg, mkSec] at h
  | 1, _ => exact Or.inl rfl
  | 2, _ => exact Or.inr rfl
  | n + 3, h => simp [GcIn.nameOf, gcReg] at h

/-- **Link failure under the precise policy.** Without per-entry edges or roots, the precise
policy removes both entries and the bounds of `7` are undefined; the conservative policy keeps
both. -/
theorem registry_precise_link_failure_conservative_kept :
    StartStopUndefined (gcReg [] false false) .precise 7 ∧
      RegistryKept (gcReg [] false false) .conservative 7 := by
  have hroot0 : (gcReg [] false false).IsRoot 0 := by decide
  refine ⟨?_, conservative_registryKept_of_live_reference _ 7 0 (Reach.root hroot0) (by simp [gcReg])⟩
  have hN : NoEdgeIntoName (gcReg [] false false) 7 := by decide
  have hU : ∀ j, (gcReg [] false false).nameOf j = some 7 → ¬ (gcReg [] false false).IsRoot j := by
    intro j hj
    rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl <;> decide
  exact (precise_drops_unrooted_entries_of_noEdgeIntoName _ 7 hN hU).2
    ⟨0, Reach.root hroot0, by simp [gcReg]⟩

/-- **Silent shrinking under the precise policy.** If the entry section also references entry
1 directly, the precise policy keeps entry 1 and removes entry 2: the registry shrinks while
the bounds stay defined. The conservative policy keeps both. -/
theorem registry_precise_silent_shrink :
    (gcReg [(0, 1)] false false).Live .precise 1 ∧
      ¬ (gcReg [(0, 1)] false false).Live .precise 2 ∧
      ¬ RegistryKept (gcReg [(0, 1)] false false) .precise 7 ∧
      ¬ StartStopUndefined (gcReg [(0, 1)] false false) .precise 7 ∧
      RegistryKept (gcReg [(0, 1)] false false) .conservative 7 := by
  have hroot0 : (gcReg [(0, 1)] false false).IsRoot 0 := by decide
  have h1 : (gcReg [(0, 1)] false false).Live .precise 1 :=
    Reach.step (Reach.root hroot0) (by simp [gcReg])
  have h2 : ¬ (gcReg [(0, 1)] false false).Live .precise 2 := by
    intro h
    have := live_closed (gcReg [(0, 1)] false false) .precise (fun i => i != 2) (by decide)
      (by decide) 2 h
    exact absurd this (by decide)
  refine ⟨h1, h2, fun h => h2 (h 2 rfl), fun h => h.2 1 rfl h1, ?_⟩
  exact conservative_registryKept_of_live_reference _ 7 0 (Reach.root hroot0) (by simp [gcReg])

/-- **`KEEP` or the retain flag on each entry restores the registry under the precise
policy.** -/
theorem registry_keep_or_retain_kept_precise :
    RegistryKept (gcReg [] true false) .precise 7 ∧
      RegistryKept (gcReg [] false true) .precise 7 := by
  constructor
  · apply registryKept_of_entries_rooted
    intro j hj
    rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl <;> decide
  · apply registryKept_of_entries_rooted
    intro j hj
    rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl <;> decide

/-- `live_iff_root_or_conservative_reference_of_noEdgeIntoName`: the no-edge hypothesis is
tight (entry 1 is reached by a relocation edge, is kept under the precise policy, and is
neither a root nor covered by the conservative rule). -/
theorem registry_iff_cex_edge_into_entry :
    ¬ NoEdgeIntoName (gcReg [(0, 1)] false false) 7 ∧
      (gcReg [(0, 1)] false false).nameOf 1 = some 7 ∧
      ¬ ((gcReg [(0, 1)] false false).Live .precise 1 ↔
        (gcReg [(0, 1)] false false).IsRoot 1 ∨
          ((SSPolicy.precise : SSPolicy) = .conservative ∧
            ∃ i, (gcReg [(0, 1)] false false).Live .precise i ∧
              (i, 7) ∈ (gcReg [(0, 1)] false false).ss)) := by
  refine ⟨by decide, rfl, fun h => ?_⟩
  rcases h.mp registry_precise_silent_shrink.1 with h' | ⟨h', _⟩
  · exact absurd h' (by decide)
  · cases h'

/-- Instance of the registry results: `gcReg [] false false` satisfies the no-edge hypothesis;
section 1 is named `7`. -/
theorem registry_nonvacuity :
    NoEdgeIntoName (gcReg [] false false) 7 ∧ (gcReg [] false false).nameOf 1 = some 7 ∧
      (∀ j, (gcReg [] false false).nameOf j = some 7 → ¬ (gcReg [] false false).IsRoot j) := by
  refine ⟨by decide, rfl, ?_⟩
  intro j hj
  rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl <;> decide

/-! ## Result 8: two-stage retention is a conjunction -/

theorem compiled_of_linkReach (p : Prog2) (i : Nat) (h : p.LinkReach i) : p.compiled i = true := by
  induction h with
  | root hr => exact hr.1
  | step _ he _ =>
    simp only [Prog2.objEdges, List.mem_filter, Bool.and_eq_true] at he
    exact he.2.2

/-- End-to-end survival coincides with link-time reachability in the object the compiler
produced: every root and every edge of that object already lies on statics the compiler keeps
(`compiled_of_linkReach`). -/
theorem survives_iff_linkReach (p : Prog2) (i : Nat) : p.Survives i ↔ p.LinkReach i :=
  ⟨fun h => h.2, fun h => ⟨compiled_of_linkReach p i h, h⟩⟩

/-- **End-to-end survival is reachability through compiler-kept statics.** Static `i` survives
the compiler stage and linker GC iff there is a path in the source-level link graph `p.ledges`
from a static whose section is a link root or retained to `i`, every static of which (the start
and `i` included) the compiler keeps. -/
theorem survives_iff_compiledPath (p : Prog2) (i : Nat) :
    p.Survives i ↔ p.CompiledPath i := by
  rw [survives_iff_linkReach]
  constructor
  · intro h
    induction h with
    | @root i hr =>
      obtain ⟨hc, s, hs, hlr⟩ := hr
      have hck : compileKeeps s = true := by simpa [Prog2.compiled, hs] using hc
      exact Prog2.CompiledPath.root hs hck hlr
    | @step i j _ he ih =>
      simp only [Prog2.objEdges, List.mem_filter, Bool.and_eq_true] at he
      obtain ⟨hedge, _, hc2⟩ := he
      unfold Prog2.compiled at hc2
      cases hsj : p.statics[j]? with
      | none => simp [hsj] at hc2
      | some sj =>
        simp only [hsj] at hc2
        exact Prog2.CompiledPath.step ih hedge hsj hc2
  · intro h
    induction h with
    | @root i s hs hck hlr =>
      exact Reach.root ⟨by simp [Prog2.compiled, hs, hck], s, hs, hlr⟩
    | @step i j sj _ hedge hsj hck ih =>
      have hc1 : p.compiled i = true := compiled_of_linkReach p i ih
      have hc2 : p.compiled j = true := by simp [Prog2.compiled, hsj, hck]
      exact Reach.step ih (by simp [Prog2.objEdges, hedge, hc1, hc2])

/-- **Conjunction form (definitional).** For static `i` with record `s`: it survives
compilation and linker GC iff (it is referenced at compile time or compiler-used) and (it is
reachable at link time in the object the compiler produced, or it carries the retain flag). By
`survives_iff_linkReach`, the left conjunct and the `retain` disjunct are both implied by
`p.LinkReach i`, so this is a restatement of the definitions. -/
theorem survives_iff_compileKept_and_linkReach_or_retain (p : Prog2) (i : Nat) (s : Static)
    (hs : p.statics[i]? = some s) :
    p.Survives i ↔ (s.cref = true ∨ s.cused = true) ∧ (p.LinkReach i ∨ s.retain = true) := by
  have hc : p.compiled i = (s.cref || s.cused) := by simp [Prog2.compiled, hs, compileKeeps]
  unfold Prog2.Survives
  rw [hc, Bool.or_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · refine ⟨h1, Reach.root ⟨?_, s, hs, by simp [h2]⟩⟩
      rw [hc, Bool.or_eq_true]
      exact h1

/-- Boolean form of `Prog2.objRoot` for concrete checks. -/
def Prog2.objRootB (p : Prog2) (i : Nat) : Bool :=
  p.compiled i && match p.statics[i]? with
    | some s => s.lroot || s.retain
    | none => false

theorem linkReach_closed (p : Prog2) (S : Nat → Bool)
    (hR : ∀ i < p.statics.length, p.objRootB i = true → S i = true)
    (hE : ∀ e ∈ p.objEdges, S e.1 = true → S e.2 = true) :
    ∀ j, p.LinkReach j → S j = true := by
  apply reach_closed _ _ (fun j => S j = true) _ hE
  rintro i ⟨hc, s, hs, hr⟩
  have hi : i < p.statics.length := (List.getElem?_eq_some_iff.mp hs).1
  exact hR i hi (by simp [Prog2.objRootB, hc, hs, hr])

/-- The entry static: referenced at compile time, a link root. -/
def stMain : Static := ⟨true, false, false, true⟩
/-- A compiler-used static, not retained, not referenced. -/
def stUsedOnly : Static := ⟨false, true, false, false⟩
/-- A retained static, neither referenced at compile time nor compiler-used. -/
def stRetainOnly : Static := ⟨false, false, true, false⟩
/-- A static both compiler-used and retained. -/
def stUsedRetained : Static := ⟨false, true, true, false⟩

/-- **Counterexample 1: compiler-used is not linker-retained.** A compiler-used static in its
own section, not retained and not reachable at link time, survives the compiler stage and is
removed by linker GC. -/
theorem compilerUsed_unretained_unreachable_removed :
    (Prog2.mk [stMain, stUsedOnly] []).compiled 1 = true ∧
      ¬ (Prog2.mk [stMain, stUsedOnly] []).Survives 1 := by
  refine ⟨rfl, fun ⟨_, h⟩ => ?_⟩
  have := linkReach_closed (Prog2.mk [stMain, stUsedOnly] []) (fun i => i != 1) (by decide)
    (by decide) 1 h
  exact absurd this (by decide)

/-- **Counterexample 2: the retain flag does not survive a compiler-stage drop.** A retained
static that is neither referenced at compile time nor compiler-used is dropped by the compiler
stage, so it does not survive end-to-end. -/
theorem retained_but_compiler_dropped :
    stRetainOnly.retain = true ∧ (Prog2.mk [stMain, stRetainOnly] []).compiled 1 = false ∧
      ¬ (Prog2.mk [stMain, stRetainOnly] []).Survives 1 := by
  refine ⟨rfl, rfl, fun ⟨h, _⟩ => ?_⟩
  exact absurd h (by decide)

/-- Source-level link reachability: reachability over all link edges from link roots,
ignoring the compiler stage. -/
def Prog2.SrcReach (p : Prog2) (i : Nat) : Prop :=
  Reach p.ledges (fun j => ∃ s, p.statics[j]? = some s ∧ (s.lroot || s.retain) = true) i

/-- A static with no flag set: not referenced by compiler-kept code, not compiler-used, not
retained, not a link root. -/
def stPlain : Static := ⟨false, false, false, false⟩

/-- **Compiler-kept plus source-level reachability does not imply survival.** Static 2 is
compiler-used and reachable from the entry static 0 in the source-level link graph, but only
through static 1, which the compiler drops; static 2 does not survive. -/
theorem compileKept_and_srcReach_not_sufficient :
    (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).compiled 2 = true ∧
      (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).SrcReach 2 ∧
      ¬ (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).Survives 2 := by
  refine ⟨rfl, ?_, fun ⟨_, h⟩ => ?_⟩
  · exact Reach.step (i := 1) (Reach.step (i := 0) (Reach.root ⟨stMain, rfl, rfl⟩) (by simp))
      (by simp)
  · have := linkReach_closed (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)])
      (fun i => i == 0) (by decide) (by decide) 2 h
    exact absurd this (by decide)

/-- `Prog2.SrcReach`: static 1 is source-reachable when the entry references it, and not
otherwise. -/
theorem srcReach_examples :
    (Prog2.mk [stMain, stPlain] [(0, 1)]).SrcReach 1 ∧
      ¬ (Prog2.mk [stMain, stPlain] []).SrcReach 1 := by
  refine ⟨Reach.step (i := 0) (Reach.root ⟨stMain, rfl, rfl⟩) (by simp), fun h => ?_⟩
  have := reach_closed (Prog2.mk [stMain, stPlain] []).ledges _ (fun j => j = 0)
    (by
      rintro j ⟨s, hs, hr⟩
      match j, hs with
      | 0, _ => rfl
      | 1, hs =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
        subst hs; simp [stPlain] at hr
      | n + 2, hs => simp at hs)
    (by intro e he; simp at he) 1 h
  exact absurd this (by decide)

/-- Instance of result 8: a compiler-used, retained static survives and has a compiler-kept
path; the entry survives. -/
theorem twoStage_nonvacuity :
    (Prog2.mk [stMain, stUsedRetained] []).statics[1]? = some stUsedRetained ∧
      (Prog2.mk [stMain, stUsedRetained] []).Survives 1 ∧
      (Prog2.mk [stMain, stUsedRetained] []).CompiledPath 1 ∧
      (Prog2.mk [stMain, stUsedRetained] []).Survives 0 :=
  ⟨rfl, ⟨rfl, Reach.root ⟨rfl, stUsedRetained, rfl, rfl⟩⟩,
    Prog2.CompiledPath.root (s := stUsedRetained) rfl rfl rfl,
    ⟨rfl, Reach.root ⟨rfl, stMain, rfl, rfl⟩⟩⟩

/-- The lookup binding of the conjunction form is tight: with no static at index 0, the record
`stUsedRetained` satisfies the right-hand side, but nothing survives. -/
theorem survives_conjunction_cex_without_lookup :
    (Prog2.mk [] []).statics[0]? ≠ some stUsedRetained ∧
      ¬ ((Prog2.mk [] []).Survives 0 ↔
        (stUsedRetained.cref = true ∨ stUsedRetained.cused = true) ∧
          ((Prog2.mk [] []).LinkReach 0 ∨ stUsedRetained.retain = true)) := by
  refine ⟨by simp, fun h => ?_⟩
  have hs : (Prog2.mk [] []).Survives 0 := h.mpr ⟨Or.inr rfl, Or.inr rfl⟩
  have hc := hs.1
  simp [Prog2.compiled] at hc

end Toy.RelroGc
