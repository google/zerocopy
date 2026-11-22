/-
Exhaustiveness preservation under freezing disciplines: static freezing, per-guard freezing with
well-typed guards, and shallow freezing for deref-free matches.
-/
import ToyMatchGuard.Match

namespace Toy.MatchGuard

/-! ### Invariants used by the proofs -/

/-- Recorded switch results that are consistent with memory `v`. -/
def MemoOK (v : Val) (m : Memo) : Prop := ∀ p r, memoFind m p = some r → headAt v p = r

/-- Two memories agree on the heads at the places `S` and on the whole values at the places `D`. -/
def AgreeOn (S D : List Place) (v v' : Val) : Prop :=
  (∀ p ∈ S, headAt v p = headAt v' p) ∧ (∀ p ∈ D, lookup v p = lookup v' p)

theorem AgreeOn.refl (S D : List Place) (v : Val) : AgreeOn S D v v :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem AgreeOn.trans {S D : List Place} {u v w : Val} (h1 : AgreeOn S D u v)
    (h2 : AgreeOn S D v w) : AgreeOn S D u w :=
  ⟨fun p hp => (h1.1 p hp).trans (h2.1 p hp), fun p hp => (h1.2 p hp).trans (h2.2 p hp)⟩

theorem AgreeOn.mono {S D S' D' : List Place} {v w : Val} (h : AgreeOn S D v w)
    (hS : ∀ p ∈ S', p ∈ S) (hD : ∀ p ∈ D', p ∈ D) : AgreeOn S' D' v w :=
  ⟨fun p hp => h.1 p (hS p hp), fun p hp => h.2 p (hD p hp)⟩

theorem memoFind_mem : ∀ {m : Memo} {p : Place} {r : Option Head},
    memoFind m p = some r → p ∈ m.map Prod.fst
  | [], _, _, h => by simp [memoFind] at h
  | (q, r') :: m, p, r, h => by
    simp only [memoFind] at h
    split at h
    · rename_i hq; subst hq; simp
    · exact List.mem_cons_of_mem _ (memoFind_mem h)

theorem MemoOK.transfer {v v' : Val} {m : Memo} (h : MemoOK v m)
    (hagree : ∀ p ∈ m.map Prod.fst, headAt v' p = headAt v p) : MemoOK v' m := by
  intro p r hp
  rw [hagree p (memoFind_mem hp)]
  exact h p r hp

theorem MemoOK.nil (v : Val) : MemoOK v [] := by
  intro p r h; simp [memoFind] at h

/-- Lowered evaluation of a list of tests with consistent recorded results computes the direct
result, keeps the recorded results consistent, and records only places switched on by the tests. -/
theorem evalTests_spec (v : Val) : ∀ (ts : List Test) (m : Memo), MemoOK v m →
    (evalTests v m ts).1 = ts.all (Test.holds v) ∧ MemoOK v (evalTests v m ts).2 ∧
      (∀ p ∈ (evalTests v m ts).2.map Prod.fst,
        p ∈ m.map Prod.fst ∨ p ∈ ts.filterMap Test.switchPlace?) := by
  intro ts
  induction ts with
  | nil => intro m hm; simp [evalTests, hm]
  | cons t ts ih =>
    intro m hm
    -- one step
    have step1 : ∃ m', evalTest v m t = (t.holds v, m') ∧ MemoOK v m' ∧
        (∀ p ∈ m'.map Prod.fst, p ∈ m.map Prod.fst ∨ t.switchPlace? = some p) := by
      cases t with
      | switch p h =>
        cases hf : memoFind m p with
        | some r =>
          refine ⟨m, ?_, hm, fun q hq => Or.inl hq⟩
          simp [evalTest, hf, Test.holds, hm p r hf]
        | none =>
          refine ⟨(p, headAt v p) :: m, ?_, ?_, ?_⟩
          · simp [evalTest, hf, Test.holds]
          · intro q r hq
            simp only [memoFind] at hq
            split at hq
            · rename_i hpq; subst hpq; simp at hq; exact hq
            · exact hm q r hq
          · intro q hq
            simp at hq
            rcases hq with rfl | ⟨r, hr⟩
            · exact Or.inr rfl
            · exact Or.inl (by simp; exact ⟨r, hr⟩)
      | derefSwitch p q h =>
        exact ⟨m, by simp [evalTest, Test.holds], hm, fun r hr => Or.inl hr⟩
    obtain ⟨m', he, hm', hpl⟩ := step1
    cases hb : t.holds v with
    | true =>
      have e : evalTests v m (t :: ts) = evalTests v m' ts := by
        simp only [evalTests, he, hb]
      rw [e]
      obtain ⟨h1, h2, h3⟩ := ih m' hm'
      refine ⟨by simp [h1, hb], h2, ?_⟩
      intro p hp
      rcases h3 p hp with h | h
      · rcases hpl p h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by simp [h'])
      · exact Or.inr (by
          rw [List.filterMap_cons]
          split <;> simp_all)
    | false =>
      have e : evalTests v m (t :: ts) = (false, m') := by
        simp only [evalTests, he, hb]
      rw [e]
      refine ⟨by simp [hb], hm', ?_⟩
      intro p hp
      rcases hpl p hp with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp [h'])

theorem derefHead_congr {v v' : Val} {p : Place} (q : Place) (h : lookup v p = lookup v' p) :
    derefHead v p q = derefHead v' p q := by
  simp only [derefHead, h]

theorem Test.holds_congr {S D : List Place} {v v' : Val} (hag : AgreeOn S D v v') (t : Test)
    (hS : ∀ p, t.switchPlace? = some p → p ∈ S) (hD : ∀ p, t.derefScrutinee? = some p → p ∈ D) :
    t.holds v = t.holds v' := by
  cases t with
  | switch p h => simp [Test.holds, hag.1 p (hS p rfl)]
  | derefSwitch p q h => simp [Test.holds, derefHead_congr q (hag.2 p (hD p rfl))]

/-- Direct matching of an arm depends only on the heads at its switched places and on the
values at its deref-pattern scrutinees. -/
theorem Arm.matchesDirect_congr {S D : List Place} {v v' : Val} (hag : AgreeOn S D v v')
    (a : Arm) (hS : ∀ p ∈ a.switchPlaces, p ∈ S) (hD : ∀ p ∈ a.derefScrutinees, p ∈ D) :
    a.matchesDirect v = a.matchesDirect v' := by
  unfold Arm.matchesDirect
  unfold Arm.switchPlaces at hS
  unfold Arm.derefScrutinees at hD
  generalize a.tests = ts at hS hD
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.all_cons]
    rw [Test.holds_congr hag t
      (fun p hp => hS p (by rw [List.filterMap_cons, hp]; simp))
      (fun p hp => hD p (by rw [List.filterMap_cons, hp]; simp))]
    rw [ih (fun p hp => hS p (by rw [List.filterMap_cons]; split <;> simp_all))
      (fun p hp => hD p (by rw [List.filterMap_cons]; split <;> simp_all))]

theorem headAt_runWrites_of_not_prefix (p : Place) (env : Env) :
    ∀ (ws : List (Place × (Env → Val → Val))) (v : Val), (∀ w ∈ ws.map Prod.fst, ¬ w <+: p) →
      headAt (runWrites env v ws) p = headAt v p := by
  intro ws
  induction ws with
  | nil => intro v _; rfl
  | cons wx ws ih =>
    intro v h
    obtain ⟨w, f⟩ := wx
    simp only [runWrites]
    rw [ih _ (fun w' hw' => h w' (by simp at hw' ⊢; exact Or.inr hw'))]
    exact headAt_writeOrSkip_of_not_prefix w v (f env v) p (h w (by simp))

theorem lookup_runWrites_of_disjoint (p : Place) (env : Env) :
    ∀ (ws : List (Place × (Env → Val → Val))) (v : Val),
      (∀ w ∈ ws.map Prod.fst, ¬ w <+: p ∧ ¬ p <+: w) →
      lookup (runWrites env v ws) p = lookup v p := by
  intro ws
  induction ws with
  | nil => intro v _; rfl
  | cons wx ws ih =>
    intro v h
    obtain ⟨w, f⟩ := wx
    simp only [runWrites]
    rw [ih _ (fun w' hw' => h w' (by simp at hw' ⊢; exact Or.inr hw'))]
    have := h w (by simp)
    exact lookup_writeOrSkip_of_disjoint w v (f env v) p this.1 this.2

/-- Guard writes that neither shallow-conflict with the places `S` nor deep-conflict with the
places `D` leave the memory agreeing with the original on `S` (heads) and `D` (values). -/
theorem agreeOn_runWrites {S D : List Place} (env : Env) (v : Val)
    (ws : List (Place × (Env → Val → Val)))
    (hS : ∀ w ∈ ws.map Prod.fst, ∀ p ∈ S, ¬ ShallowConflict w p)
    (hD : ∀ w ∈ ws.map Prod.fst, ∀ p ∈ D, ¬ DeepConflict w p) :
    AgreeOn S D (runWrites env v ws) v := by
  constructor
  · intro p hp
    exact headAt_runWrites_of_not_prefix p env ws v (fun w hw => hS w hw p hp)
  · intro p hp
    apply lookup_runWrites_of_disjoint p env ws v
    intro w hw
    have := hD w hw p hp
    simp only [DeepConflict, not_or] at this
    exact this

theorem guardWrites_some {a : Arm} {g : Guard} (hg : a.guard = some g) :
    a.guardWrites = g.writes.map Prod.fst := by
  simp [Arm.guardWrites, hg]

/-! ### Static freezing (one fake-borrow set for the whole match) -/

/-- Core invariant for static freezing: if the lowered procedure reaches `Unreachable`, no
unguarded arm matches the initial value `v0` directly. -/
theorem runArms_unreachable_static (S D : List Place) (v0 : Val) :
    ∀ (as : List Arm) (v : Val) (m : Memo) (i : Nat) (vf : Val),
      MemoOK v m → (∀ p ∈ m.map Prod.fst, p ∈ S) → AgreeOn S D v v0 →
      (∀ a ∈ as, ∀ p ∈ a.switchPlaces, p ∈ S) → (∀ a ∈ as, ∀ p ∈ a.derefScrutinees, p ∈ D) →
      (∀ a ∈ as, ∀ w ∈ a.guardWrites, ∀ p ∈ S, ¬ ShallowConflict w p) →
      (∀ a ∈ as, ∀ w ∈ a.guardWrites, ∀ p ∈ D, ¬ DeepConflict w p) →
      runArms v m i as = .unreachable vf →
      ∀ a ∈ as, a.guard = none → a.matchesDirect v0 = false := by
  intro as
  induction as with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ a ha; simp at ha
  | cons a as ih =>
    intro v m i vf hm hmS hag hSa hDa hWS hWD hrun
    obtain ⟨hres, hm', hpl⟩ := evalTests_spec v a.tests m hm
    have hdir : (evalTests v m a.tests).1 = a.matchesDirect v0 := by
      rw [hres]
      have := Arm.matchesDirect_congr hag a (hSa a (by simp)) (hDa a (by simp))
      simpa [Arm.matchesDirect] using this
    have hmS' : ∀ p ∈ (evalTests v m a.tests).2.map Prod.fst, p ∈ S := by
      intro p hp
      rcases hpl p hp with h | h
      · exact hmS p h
      · exact hSa a (by simp) p h
    have ihas := fun v' m' => ih v' m' (i + 1) vf
    simp only [runArms] at hrun
    revert hrun
    generalize hev : evalTests v m a.tests = r
    obtain ⟨b, m'⟩ := r
    rw [hev] at hdir hm' hmS'
    simp only at hdir hm' hmS'
    cases b with
    | false =>
      intro hrun
      have hrest := ihas v m' hm' hmS' hag (fun a' ha' => hSa a' (by simp [ha']))
        (fun a' ha' => hDa a' (by simp [ha'])) (fun a' ha' => hWS a' (by simp [ha']))
        (fun a' ha' => hWD a' (by simp [ha'])) hrun
      intro a' ha' hg
      simp at ha'
      rcases ha' with rfl | ha'
      · exact hdir.symm
      · exact hrest a' ha' hg
    | true =>
      cases hga : a.guard with
      | none => intro hrun; simp at hrun
      | some g =>
        intro hrun
        simp only at hrun
        split at hrun
        · simp at hrun
        · have hagw : AgreeOn S D (runWrites (bindEnv v a.binds) v g.writes) v :=
            agreeOn_runWrites (bindEnv v a.binds) v g.writes
              (by rw [← guardWrites_some hga]; exact hWS a (by simp))
              (by rw [← guardWrites_some hga]; exact hWD a (by simp))
          have hm'' : MemoOK (runWrites (bindEnv v a.binds) v g.writes) m' :=
            hm'.transfer (fun p hp => hagw.1 p (hmS' p hp))
          have hrest := ihas (runWrites (bindEnv v a.binds) v g.writes) m' hm'' hmS' (hagw.trans hag)
            (fun a' ha' => hSa a' (by simp [ha'])) (fun a' ha' => hDa a' (by simp [ha']))
            (fun a' ha' => hWS a' (by simp [ha'])) (fun a' ha' => hWD a' (by simp [ha'])) hrun
          intro a' ha' hg
          simp at ha'
          rcases ha' with rfl | ha'
          · rw [hga] at hg; cases hg
          · exact hrest a' ha' hg

/-- **Exhaustiveness preservation under static freezing.** For every value domain `Dom`,
every arm list `arms` that is exhaustive on `Dom`, such that no guard write shallow-conflicts
with any switched place of any arm (`ShallowFrozenAll`) and no guard write deep-conflicts with
any deref-pattern scrutinee of any arm (`DeepFrozenAll`), and every `v` in `Dom`, the lowered
execution `runMatch arms v` does not reach `Unreachable`. -/
theorem runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll
    (Dom : Val → Prop) (arms : List Arm) (hex : Exhaustive Dom arms)
    (hs : ShallowFrozenAll arms) (hd : DeepFrozenAll arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := by
  cases hr : runMatch arms v with
  | arm => rfl
  | unreachable vf =>
    exfalso
    have key := runArms_unreachable_static (arms.flatMap Arm.switchPlaces)
      (arms.flatMap Arm.derefScrutinees) v arms v [] 0 vf (MemoOK.nil v) (by simp)
      (AgreeOn.refl _ _ v)
      (fun a ha p hp => List.mem_flatMap.mpr ⟨a, ha, hp⟩)
      (fun a ha p hp => List.mem_flatMap.mpr ⟨a, ha, hp⟩)
      (fun a ha w hw p hp => by
        obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
        exact hs a ha w hw b hb p hp)
      (fun a ha w hw p hp => by
        obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
        exact hd a ha w hw b hb p hp)
      hr
    obtain ⟨a, ha, hg, hm⟩ := hex v hv
    rw [key a ha hg] at hm
    cases hm

/-! ### Per-guard freezing with well-typed guards -/

/-- Core invariant for per-guard freezing: if the lowered procedure reaches `Unreachable` with
final memory `vf`, then `vf` is in `Dom`, no unguarded remaining arm matches `vf` directly, and
`vf` agrees with the current memory on the places frozen so far. -/
theorem runArms_unreachable_frozenBefore (Dom : Val → Prop) :
    ∀ (as : List Arm) (seenS seenD : List Place) (v : Val) (m : Memo) (i : Nat) (vf : Val),
      MemoOK v m → (∀ p ∈ m.map Prod.fst, p ∈ seenS) →
      ShallowFrozenBeforeAux seenS as → DeepFrozenBeforeAux seenD as →
      GuardsPreserveDom Dom as → Dom v →
      runArms v m i as = .unreachable vf →
      Dom vf ∧ (∀ a ∈ as, a.guard = none → a.matchesDirect vf = false) ∧
        AgreeOn seenS seenD vf v := by
  intro as
  induction as with
  | nil =>
    intro seenS seenD v m i vf _ _ _ _ _ hv hrun
    simp [runArms] at hrun
    subst hrun
    exact ⟨hv, by simp, AgreeOn.refl _ _ _⟩
  | cons a as ih =>
    intro seenS seenD v m i vf hm hmS hs hd hdom hv hrun
    obtain ⟨hsa, hs'⟩ := hs
    obtain ⟨hda, hd'⟩ := hd
    obtain ⟨hres, hm', hpl⟩ := evalTests_spec v a.tests m hm
    have hmS' : ∀ p ∈ (evalTests v m a.tests).2.map Prod.fst, p ∈ seenS ++ a.switchPlaces := by
      intro p hp
      rcases hpl p hp with h | h
      · exact List.mem_append_left _ (hmS p h)
      · exact List.mem_append_right _ h
    have hdom' : GuardsPreserveDom Dom as := fun a' ha' => hdom a' (by simp [ha'])
    simp only [runArms] at hrun
    revert hrun
    generalize hev : evalTests v m a.tests = r
    obtain ⟨b, m'⟩ := r
    rw [hev] at hres hm' hmS'
    simp only at hres hm' hmS'
    cases b with
    | false =>
      intro hrun
      obtain ⟨hvf, hrest, hagf⟩ := ih (seenS ++ a.switchPlaces) (seenD ++ a.derefScrutinees)
        v m' (i + 1) vf hm' hmS' hs' hd' hdom' hv hrun
      refine ⟨hvf, ?_, hagf.mono (fun p hp => List.mem_append_left _ hp)
        (fun p hp => List.mem_append_left _ hp)⟩
      intro a' ha' hg
      simp at ha'
      rcases ha' with rfl | ha'
      · rw [Arm.matchesDirect_congr hagf a' (fun p hp => List.mem_append_right _ hp)
          (fun p hp => List.mem_append_right _ hp)]
        simpa [Arm.matchesDirect] using hres.symm
      · exact hrest a' ha' hg
    | true =>
      cases hga : a.guard with
      | none => intro hrun; simp at hrun
      | some g =>
        intro hrun
        simp only at hrun
        split at hrun
        · simp at hrun
        · have hagw : AgreeOn (seenS ++ a.switchPlaces) (seenD ++ a.derefScrutinees)
              (runWrites (bindEnv v a.binds) v g.writes) v :=
            agreeOn_runWrites (bindEnv v a.binds) v g.writes
              (by rw [← guardWrites_some hga]; exact hsa)
              (by rw [← guardWrites_some hga]; exact hda)
          have hm'' : MemoOK (runWrites (bindEnv v a.binds) v g.writes) m' :=
            hm'.transfer (fun p hp => hagw.1 p (hmS' p hp))
          have hmatch : a.matchesDirect v = true := by simpa [Arm.matchesDirect] using hres.symm
          have hv' : Dom (runWrites (bindEnv v a.binds) v g.writes) :=
            hdom a (by simp) g hga v hv hmatch
          obtain ⟨hvf, hrest, hagf⟩ := ih (seenS ++ a.switchPlaces) (seenD ++ a.derefScrutinees)
            (runWrites (bindEnv v a.binds) v g.writes) m' (i + 1) vf hm'' hmS' hs' hd' hdom' hv' hrun
          refine ⟨hvf, ?_, (hagf.trans hagw).mono (fun p hp => List.mem_append_left _ hp)
            (fun p hp => List.mem_append_left _ hp)⟩
          intro a' ha' hg
          simp at ha'
          rcases ha' with rfl | ha'
          · rw [hga] at hg; cases hg
          · exact hrest a' ha' hg

/-- **Exhaustiveness preservation under per-guard freezing, for well-typed guards.** For every
value domain `Dom`, every arm list `arms` that is exhaustive on `Dom`, whose guards keep memory
inside `Dom` when run from a memory in `Dom` on which their arm matches directly
(`GuardsPreserveDom`), such that each guard write shallow-conflicts with no place
switched on by its own arm or an earlier arm (`ShallowFrozenBefore`) and deep-conflicts with no
deref-pattern scrutinee of its own arm or an earlier arm (`DeepFrozenBefore`), and every `v` in
`Dom`, the lowered execution `runMatch arms v` does not reach `Unreachable`. -/
theorem runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore
    (Dom : Val → Prop) (arms : List Arm) (hex : Exhaustive Dom arms)
    (hdom : GuardsPreserveDom Dom arms) (hs : ShallowFrozenBefore arms)
    (hd : DeepFrozenBefore arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := by
  cases hr : runMatch arms v with
  | arm => rfl
  | unreachable vf =>
    exfalso
    obtain ⟨hvf, hrest, _⟩ := runArms_unreachable_frozenBefore Dom arms [] [] v [] 0 vf
      (MemoOK.nil v) (by simp) hs hd hdom hv hr
    obtain ⟨a, ha, hg, hm⟩ := hex vf hvf
    rw [hrest a ha hg] at hm
    cases hm

/-! ### Shallow freezing for deref-free matches -/

/-- **Shallow freezing suffices without deref patterns.** For every value domain `Dom` and every
arm list `arms` with no deref-pattern test (`NoDerefPatterns`), exhaustive on `Dom`, such that
no guard write shallow-conflicts with any switched place of any arm (`ShallowFrozenAll`), and
every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`. -/
theorem runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll
    (Dom : Val → Prop) (arms : List Arm) (hnd : NoDerefPatterns arms)
    (hex : Exhaustive Dom arms) (hs : ShallowFrozenAll arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := by
  apply runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll Dom arms
    hex hs _ v hv
  intro a _ w _ b hb p hp
  rw [hnd b hb] at hp
  simp at hp

/-- Deep freezing of the switched places implies shallow freezing of them (every shallow conflict
is a deep conflict). -/
theorem shallowFrozenAll_of_deepFrozenSwitchAll (arms : List Arm)
    (h : DeepFrozenSwitchAll arms) : ShallowFrozenAll arms := by
  intro a ha w hw b hb p hp hc
  exact h a ha w hw b hb p hp (Or.inl hc)

end Toy.MatchGuard
