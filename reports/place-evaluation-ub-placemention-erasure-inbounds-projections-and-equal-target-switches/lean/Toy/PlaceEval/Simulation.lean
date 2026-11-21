import Toy.PlaceEval.RunLemmas

/-!
# A generic simulation argument for refinement

A relation `R` between source and target configurations is a simulation (`IsSim`) if every
target step from related configurations is matched by one or more source steps emitting the
same events, or by no source step at all while a measure `μ` on target configurations
decreases (`μ` is bounded by `B` on related configurations), or the source reaches UB without
emitting further events. A simulation from the initial configurations gives a refinement
(`refinesAcross_of_sim`). The section `BlockEdits` instantiates the argument for programs
that differ in one block only.
-/

namespace Toy.PlaceEval

/-! ## Runs: composition and traces -/

/-- Prepend a trace to an outcome. -/
def Outcome.app (t : List Nat) : Outcome → Outcome
  | .done u s => .done (t ++ u) s
  | .ub u => .ub (t ++ u)
  | .running c u => .running c (t ++ u)
  | .blocked => .blocked

theorem Outcome.cons_eq_app (ev : Option Nat) (o : Outcome) : o.cons ev = o.app ev.toList := by
  cases o <;> rfl

theorem Outcome.app_nil (o : Outcome) : o.app [] = o := by
  cases o <;> rfl

theorem Outcome.app_app (t u : List Nat) (o : Outcome) : (o.app u).app t = o.app (t ++ u) := by
  cases o <;> simp [Outcome.app]

/-- Running `a` steps to a running configuration and then `b` more steps. -/
theorem run_add_running {mode : AllocMode} {P : Prog} :
    ∀ (a b : Nat) (c c' : Cfg) (t : List Nat), run mode P a c = .running c' t →
      run mode P (a + b) c = (run mode P b c').app t
  | 0, b, c, c', t, h => by
    simp only [run] at h
    cases h
    simp [Outcome.app_nil]
  | a + 1, b, c, c', t, h => by
    rw [Nat.add_right_comm]
    cases hs : step mode P c with
    | next ev c1 =>
      rw [run_succ_next _ hs] at h ⊢
      cases hr : run mode P a c1 with
      | running c2 t2 =>
        rw [hr] at h
        simp only [Outcome.cons, Outcome.running.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [run_add_running a b c1 c2 t2 hr, Outcome.cons_eq_app, Outcome.app_app]
      | done t2 s => rw [hr] at h; simp [Outcome.cons] at h
      | ub t2 => rw [hr] at h; simp [Outcome.cons] at h
      | blocked => rw [hr] at h; simp [Outcome.cons] at h
    | halt s => rw [run_succ_halt _ hs] at h; cases h
    | ub => rw [run_succ_ub _ hs] at h; cases h
    | block => rw [run_succ_block _ hs] at h; cases h

/-- One more step after a running configuration. -/
theorem run_succ_of_running {mode : AllocMode} {P : Prog} {n : Nat} {c0 c c' : Cfg}
    {t : List Nat} {ev : Option Nat} (h : run mode P n c0 = .running c t)
    (hs : step mode P c = .next ev c') :
    run mode P (n + 1) c0 = .running c' (t ++ ev.toList) := by
  rw [run_add_running n 1 c0 c t h, run_succ_next 0 hs]
  simp [run, Outcome.cons, Outcome.app]

/-- Traces of running outcomes grow with fuel. -/
theorem run_running_prefix {mode : AllocMode} {P : Prog} {a b : Nat} {c c1 c2 : Cfg}
    {t1 t2 : List Nat} (h1 : run mode P a c = .running c1 t1) (h2 : run mode P b c = .running c2 t2)
    (hab : a ≤ b) : t1 <+: t2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [run_add_running a k c c1 t1 h1] at h2
  cases hr : run mode P k c1 with
  | running c3 t3 =>
    rw [hr] at h2
    simp only [Outcome.app, Outcome.running.injEq] at h2
    exact ⟨t3, h2.2⟩
  | done t3 s => rw [hr] at h2; simp [Outcome.app] at h2
  | ub t3 => rw [hr] at h2; simp [Outcome.app] at h2
  | blocked => rw [hr] at h2; simp [Outcome.app] at h2

/-- A run that is running with more fuel was running with less fuel. -/
theorem run_isRunning_of_le {mode : AllocMode} {P : Prog} {a b : Nat} {c : Cfg}
    (h : (run mode P b c).isRunning = true) (hab : a ≤ b) : (run mode P a c).isRunning = true := by
  cases ho : (run mode P a c).isRunning
  · have := run_finished_mono ho rfl hab
    rw [this, ho] at h
    exact h
  · rfl

theorem isRunning_iff {o : Outcome} : o.isRunning = true ↔ ∃ c t, o = .running c t := by
  cases o <;> simp [Outcome.isRunning]

/-- `u` is a prefix of the first `L` values of `f` iff it is the first `u.length` values. -/
theorem eq_prefixOf_of_prefix {f : Nat → Nat} {u : List Nat} {L : Nat} (h : u <+: prefixOf f L) :
    u = prefixOf f u.length := by
  have hlen : u.length ≤ L := by
    have := h.length_le
    simpa [prefixOf] using this
  rw [List.prefix_iff_eq_take] at h
  rw [h]
  simp only [prefixOf, List.length_take, List.length_map, List.length_range]
  rw [← List.map_take, List.take_range]

/-! ## Simulations -/

/-- The source run from `cs` reaches UB without emitting an event. -/
def SrcUB (ms : AllocMode) (Ps : Prog) (cs : Cfg) : Prop := ∃ k, run ms Ps k cs = .ub []

/-- The source run from `cs` reaches UB after a prefix of `t`. -/
def SrcUBPre (ms : AllocMode) (Ps : Prog) (cs : Cfg) (t : List Nat) : Prop :=
  ∃ m u, run ms Ps m cs = .ub u ∧ u <+: t

/-- One target step from `ct` is matched from `cs`: the source reaches UB silently, or every
target step `next ev ct'` is matched by `k + 1` source steps emitting `ev` (to a configuration
related to `ct'`) or by no source step (silent target step, `μ` decreases, `cs` related to
`ct'`); a target `halt` is matched by a source `halt`; the target does not reach UB. -/
def StepSim (ms : AllocMode) (Ps : Prog) (mt : AllocMode) (Pt : Prog) (R : Cfg → Cfg → Prop)
    (μ : Cfg → Nat) (cs ct : Cfg) : Prop :=
  SrcUB ms Ps cs ∨
  ((∀ ev ct', step mt Pt ct = .next ev ct' →
      (∃ k cs', run ms Ps (k + 1) cs = .running cs' ev.toList ∧ R cs' ct') ∨
      (ev = none ∧ μ ct' < μ ct ∧ R cs ct')) ∧
   (∀ st, step mt Pt ct = .halt st → ∃ k st', run ms Ps k cs = .done [] st') ∧
   step mt Pt ct ≠ .ub)

/-- `R` is a simulation with measure `μ` bounded by `B`. -/
structure IsSim (ms : AllocMode) (Ps : Prog) (mt : AllocMode) (Pt : Prog) (R : Cfg → Cfg → Prop)
    (μ : Cfg → Nat) (B : Nat) : Prop where
  bound : ∀ cs ct, R cs ct → μ ct ≤ B
  step : ∀ cs ct, R cs ct → StepSim ms Ps mt Pt R μ cs ct

/-- What a target outcome after `n` steps from `ct` is matched by, from `cs`. -/
def Matched (ms : AllocMode) (Ps : Prog) (R : Cfg → Cfg → Prop) (μ : Cfg → Nat) (B n : Nat)
    (cs ct : Cfg) : Outcome → Prop
  | .done t _ => (∃ m st', run ms Ps m cs = .done t st') ∨ SrcUBPre ms Ps cs t
  | .ub t => SrcUBPre ms Ps cs t
  | .running ct' t =>
      (∃ m cs', run ms Ps m cs = .running cs' t ∧ R cs' ct' ∧ n + μ ct' ≤ (B + 1) * m + μ ct) ∨
      SrcUBPre ms Ps cs t
  | .blocked => True

theorem srcUBPre_app {ms : AllocMode} {Ps : Prog} {cs cs' : Cfg} {a : Nat} {e t : List Nat}
    (ha : run ms Ps a cs = .running cs' e) (h : SrcUBPre ms Ps cs' t) :
    SrcUBPre ms Ps cs (e ++ t) := by
  obtain ⟨m, u, hm, hu⟩ := h
  refine ⟨a + m, e ++ u, ?_, List.prefix_append_right_inj e |>.2 hu⟩
  rw [run_add_running a m cs cs' e ha, hm]
  rfl

theorem srcUBPre_of_srcUB {ms : AllocMode} {Ps : Prog} {cs : Cfg} (h : SrcUB ms Ps cs)
    (t : List Nat) : SrcUBPre ms Ps cs t := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, [], hk, List.nil_prefix⟩

theorem matched_of_srcUB {ms : AllocMode} {Ps : Prog} {R : Cfg → Cfg → Prop} {μ : Cfg → Nat}
    {B n : Nat} {cs ct : Cfg} (h : SrcUB ms Ps cs) (o : Outcome) :
    Matched ms Ps R μ B n cs ct o := by
  cases o with
  | done t s => exact Or.inr (srcUBPre_of_srcUB h t)
  | ub t => exact srcUBPre_of_srcUB h t
  | running c t => exact Or.inr (srcUBPre_of_srcUB h t)
  | blocked => trivial

theorem mul_succ_add_le (B k m : Nat) : (B + 1) * m + (B + 1) ≤ (B + 1) * (k + 1 + m) := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have : 0 ≤ (B + 1) * k := Nat.zero_le _
  omega

/-- The simulation lemma for runs. -/
theorem IsSim.matched {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {B : Nat} (h : IsSim ms Ps mt Pt R μ B) :
    ∀ (n : Nat) (cs ct : Cfg), R cs ct → Matched ms Ps R μ B n cs ct (run mt Pt n ct)
  | 0, cs, ct, hR => Or.inl ⟨0, cs, rfl, hR, by simp⟩
  | n + 1, cs, ct, hR => by
    rcases h.step cs ct hR with hub | ⟨hnext, hhalt, hnub⟩
    · exact matched_of_srcUB hub _
    cases hs : Toy.PlaceEval.step mt Pt ct with
    | next ev ct' =>
      rw [run_succ_next _ hs, Outcome.cons_eq_app]
      rcases hnext ev ct' hs with ⟨k, cs', hk, hR'⟩ | ⟨rfl, hμ, hR'⟩
      · have ih := h.matched n cs' ct' hR'
        have hb := h.bound cs' ct' hR'
        cases hr : run mt Pt n ct' with
        | done t st =>
          rw [hr] at ih
          rcases ih with ⟨m, st', hm⟩ | hpre
          · refine Or.inl ⟨k + 1 + m, st', ?_⟩
            rw [run_add_running (k + 1) m cs cs' _ hk, hm]; rfl
          · exact Or.inr (srcUBPre_app hk hpre)
        | ub t =>
          rw [hr] at ih
          exact srcUBPre_app hk ih
        | running ct'' t =>
          rw [hr] at ih
          rcases ih with ⟨m, cs'', hm, hR'', hle⟩ | hpre
          · refine Or.inl ⟨k + 1 + m, cs'', ?_, hR'', ?_⟩
            · rw [run_add_running (k + 1) m cs cs' _ hk, hm]; rfl
            · have := mul_succ_add_le B k m
              omega
          · exact Or.inr (srcUBPre_app hk hpre)
        | blocked => trivial
      · have ih := h.matched n cs ct' hR'
        simp only [Option.toList, Outcome.app_nil]
        cases hr : run mt Pt n ct' with
        | done t st => rw [hr] at ih; exact ih
        | ub t => rw [hr] at ih; exact ih
        | running ct'' t =>
          rw [hr] at ih
          rcases ih with ⟨m, cs'', hm, hR'', hle⟩ | hpre
          · exact Or.inl ⟨m, cs'', hm, hR'', by omega⟩
          · exact Or.inr hpre
        | blocked => trivial
    | halt st =>
      rw [run_succ_halt _ hs]
      obtain ⟨k, st', hk⟩ := hhalt st hs
      exact Or.inl ⟨k, st', hk⟩
    | ub => exact absurd hs hnub
    | block => rw [run_succ_block _ hs]; trivial

/-- In a reactive behaviour every trace of the run is a prefix of the reactive sequence. -/
theorem react_trace {mode : AllocMode} {P : Prog} {c : Cfg} {f : Nat → Nat}
    (hrun : ∀ n, (run mode P n c).isRunning = true)
    (hpre : ∀ k, ∃ n, (run mode P n c).trace = prefixOf f k) (n : Nat) :
    (run mode P n c).trace = prefixOf f (run mode P n c).trace.length := by
  obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun n)
  obtain ⟨n', hn'⟩ := hpre t1.length
  obtain ⟨c2, t2, h2⟩ := isRunning_iff.1 (hrun n')
  rw [h2] at hn'
  simp only [Outcome.trace] at hn'
  rw [h1]
  simp only [Outcome.trace]
  have hlen : t2.length = t1.length := by rw [hn']; simp [prefixOf]
  rcases Nat.le_total n n' with hle | hle
  · have hp := run_running_prefix h1 h2 hle
    have := hp.eq_of_length hlen.symm
    rw [this, hn']
    simp [prefixOf]
  · have hp := run_running_prefix h2 h1 hle
    have := hp.eq_of_length hlen
    rw [← this, hn']
    simp [prefixOf]

/-- The simulation lemma for behaviours: every target behaviour from `ct` improves a source
behaviour from `cs`. -/
theorem IsSim.improves {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {B : Nat} (h : IsSim ms Ps mt Pt R μ B)
    {cs ct : Cfg} (hR : R cs ct) (bt : Beh) (hbt : HasBehFrom mt Pt ct bt) :
    ∃ bs, HasBehFrom ms Ps cs bs ∧ ImprovesPP bt bs := by
  have hμ0 := h.bound cs ct hR
  cases bt with
  | term t =>
    obtain ⟨n, s, hn⟩ := hbt
    have hm := h.matched n cs ct hR
    rw [hn] at hm
    rcases hm with ⟨m, st', hm⟩ | ⟨m, u, hm, hu⟩
    · exact ⟨.term t, ⟨m, st', hm⟩, improvesPP_refl _⟩
    · exact ⟨.wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, hu⟩⟩
  | wrong t =>
    obtain ⟨n, hn⟩ := hbt
    have hm := h.matched n cs ct hR
    rw [hn] at hm
    obtain ⟨m, u, hm, hu⟩ := hm
    exact ⟨.wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, hu⟩⟩
  | div t =>
    obtain ⟨hrun, N, hN⟩ := hbt
    by_cases hub : ∃ n, SrcUBPre ms Ps cs (run mt Pt n ct).trace
    · obtain ⟨n, m, u, hm, hu⟩ := hub
      refine ⟨.wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, ?_⟩⟩
      show u <+: t
      obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun n)
      obtain ⟨c2, t2, h2⟩ := isRunning_iff.1 (hrun (max n N))
      have e2 := hN (max n N) (Nat.le_max_right _ _)
      rw [h2] at e2
      rw [h1] at hu
      simp only [Outcome.trace] at hu e2
      subst e2
      exact hu.trans (run_running_prefix h1 h2 (Nat.le_max_left _ _))
    · have hsrc : ∀ n, ∃ m cs', run ms Ps m cs = .running cs' (run mt Pt n ct).trace ∧
          n ≤ (B + 1) * m + B := by
        intro n
        obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun n)
        have hm := h.matched n cs ct hR
        rw [h1] at hm
        rcases hm with ⟨m, cs', hm, _, hle⟩ | hpre
        · refine ⟨m, cs', ?_, by omega⟩
          rw [h1]; exact hm
        · exact absurd ⟨n, by rw [h1]; exact hpre⟩ hub
      have hsrun : ∀ m, (run ms Ps m cs).isRunning = true := by
        intro m
        obtain ⟨m', cs', hm', hle⟩ := hsrc ((B + 1) * m + B)
        have : m ≤ m' := Nat.le_of_mul_le_mul_left (c := B + 1) (by omega) (by omega)
        exact run_isRunning_of_le (by rw [hm']; rfl) this
      obtain ⟨mN, csN, hmN, _⟩ := hsrc N
      have htN := hN N (Nat.le_refl _)
      rw [htN] at hmN
      refine ⟨.div t, ⟨hsrun, mN, fun m hm => ?_⟩, improvesPP_refl _⟩
      obtain ⟨m', cs', hm', hle⟩ := hsrc ((B + 1) * m + B + N)
      have hle' : m ≤ m' := Nat.le_of_mul_le_mul_left (c := B + 1) (by omega) (by omega)
      rw [hN _ (by omega)] at hm'
      obtain ⟨c3, t3, h3⟩ := isRunning_iff.1 (hsrun m)
      rw [h3]
      have p1 := run_running_prefix hmN h3 hm
      have p2 := run_running_prefix h3 hm' hle'
      exact (p2.eq_of_length (Nat.le_antisymm p2.length_le p1.length_le)).symm ▸ rfl
  | react f =>
    obtain ⟨hrun, hpre⟩ := hbt
    by_cases hub : ∃ n, SrcUBPre ms Ps cs (run mt Pt n ct).trace
    · obtain ⟨n, m, u, hm, hu⟩ := hub
      refine ⟨.wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, ?_⟩⟩
      show u = prefixOf f u.length
      rw [react_trace hrun hpre n] at hu
      exact eq_prefixOf_of_prefix hu
    · have hsrc : ∀ n, ∃ m cs', run ms Ps m cs = .running cs' (run mt Pt n ct).trace ∧
          n ≤ (B + 1) * m + B := by
        intro n
        obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun n)
        have hm := h.matched n cs ct hR
        rw [h1] at hm
        rcases hm with ⟨m, cs', hm, _, hle⟩ | hpre
        · refine ⟨m, cs', ?_, by omega⟩
          rw [h1]; exact hm
        · exact absurd ⟨n, by rw [h1]; exact hpre⟩ hub
      have hsrun : ∀ m, (run ms Ps m cs).isRunning = true := by
        intro m
        obtain ⟨m', cs', hm', hle⟩ := hsrc ((B + 1) * m + B)
        have : m ≤ m' := Nat.le_of_mul_le_mul_left (c := B + 1) (by omega) (by omega)
        exact run_isRunning_of_le (by rw [hm']; rfl) this
      refine ⟨.react f, ⟨hsrun, fun k => ?_⟩, improvesPP_refl _⟩
      obtain ⟨n, hn⟩ := hpre k
      obtain ⟨m, cs', hm, _⟩ := hsrc n
      exact ⟨m, by rw [hm, hn]; rfl⟩

/-- **Refinement from a simulation.** If for every target oracle whose entry allocations
succeed there is a source oracle whose entry allocations succeed and a simulation relating the
initial configurations, the target refines the source. -/
theorem refinesAcross_of_sim {Ss St : Sem} {Ps Pt : Prog}
    (h : ∀ ωt st0t, Pt.initState (St.mode ωt) = some st0t →
      ∃ ωs st0s R μ B, Ps.initState (Ss.mode ωs) = some st0s ∧
        IsSim (Ss.mode ωs) Ps (St.mode ωt) Pt R μ B ∧ R (Ps.entry 0 st0s) (Pt.entry 0 st0t)) :
    RefinesAcross Ss Ps St Pt := by
  rintro bt ⟨ωt, st0t, h0, hb⟩
  obtain ⟨ωs, st0s, R, μ, B, h0s, hsim, hR⟩ := h ωt st0t h0
  obtain ⟨bs, hbs, himp⟩ := hsim.improves hR bt hb
  exact ⟨bs, ⟨ωs, st0s, h0s, hbs⟩, himp⟩

/-- A simulation for reaching configurations (target UB, halt and block are ignored). -/
theorem reach_of_sim {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop}
    (h : ∀ cs ct, R cs ct → ∀ ev ct', step mt Pt ct = .next ev ct' →
      (∃ k cs', run ms Ps (k + 1) cs = .running cs' ev.toList ∧ R cs' ct') ∨
      (ev = none ∧ R cs ct')) :
    ∀ (n : Nat) (cs ct ct' : Cfg) (t : List Nat), R cs ct → run mt Pt n ct = .running ct' t →
      ∃ m cs', run ms Ps m cs = .running cs' t ∧ R cs' ct'
  | 0, cs, ct, ct', t, hR, hr => by
    simp only [run, Outcome.running.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨0, cs, rfl, hR⟩
  | n + 1, cs, ct, ct', t, hR, hr => by
    cases hs : step mt Pt ct with
    | next ev c1 =>
      rw [run_succ_next _ hs, Outcome.cons_eq_app] at hr
      cases hr1 : run mt Pt n c1 with
      | running c2 t2 =>
        rw [hr1] at hr
        simp only [Outcome.app, Outcome.running.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        rcases h cs ct hR ev c1 hs with ⟨k, cs1, hk, hR1⟩ | ⟨rfl, hR1⟩
        · obtain ⟨m, cs2, hm, hR2⟩ := reach_of_sim h n cs1 c1 c2 t2 hR1 hr1
          refine ⟨k + 1 + m, cs2, ?_, hR2⟩
          rw [run_add_running (k + 1) m cs cs1 _ hk, hm]; rfl
        · obtain ⟨m, cs2, hm, hR2⟩ := reach_of_sim h n cs c1 c2 t2 hR1 hr1
          exact ⟨m, cs2, by simpa using hm, hR2⟩
      | done t2 s => rw [hr1] at hr; simp [Outcome.app] at hr
      | ub t2 => rw [hr1] at hr; simp [Outcome.app] at hr
      | blocked => rw [hr1] at hr; simp [Outcome.app] at hr
    | halt s => rw [run_succ_halt _ hs] at hr; cases hr
    | ub => rw [run_succ_ub _ hs] at hr; cases hr
    | block => rw [run_succ_block _ hs] at hr; cases hr

/-- The configuration `c` is reached from `c0`. -/
def Reach (mode : AllocMode) (P : Prog) (c0 c : Cfg) : Prop := ∃ n t, run mode P n c0 = .running c t

/-- Adding target reachability to a simulation relation. -/
theorem IsSim.withReach {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {B : Nat} (c0 : Cfg)
    (hb : ∀ cs ct, R cs ct → μ ct ≤ B)
    (hs : ∀ cs ct, R cs ct → Reach mt Pt c0 ct → StepSim ms Ps mt Pt R μ cs ct) :
    IsSim ms Ps mt Pt (fun cs ct => R cs ct ∧ Reach mt Pt c0 ct) μ B := by
  refine ⟨fun cs ct h => hb cs ct h.1, fun cs ct ⟨hR, hreach⟩ => ?_⟩
  obtain ⟨n, t, hn⟩ := hreach
  rcases hs cs ct hR ⟨n, t, hn⟩ with hub | ⟨hnext, hhalt, hnub⟩
  · exact Or.inl hub
  refine Or.inr ⟨fun ev ct' hst => ?_, hhalt, hnub⟩
  have hr' : Reach mt Pt c0 ct' := ⟨n + 1, _, run_succ_of_running hn hst⟩
  rcases hnext ev ct' hst with ⟨k, cs', hk, hR'⟩ | ⟨hev, hμ, hR'⟩
  · exact Or.inl ⟨k, cs', hk, hR', hr'⟩
  · exact Or.inr ⟨hev, hμ, hR', hr'⟩

/-! ## Step matching with an explicit exception for target UB -/

/-- Like `StepSim`, but every target step `next` is matched without source UB, and a target
UB step is matched by source UB unless the pair satisfies the exception predicate `U`. -/
def StepSimU (ms : AllocMode) (Ps : Prog) (mt : AllocMode) (Pt : Prog) (R : Cfg → Cfg → Prop)
    (μ : Cfg → Nat) (U : Cfg → Cfg → Prop) (cs ct : Cfg) : Prop :=
  (∀ ev ct', step mt Pt ct = .next ev ct' →
      (∃ k cs', run ms Ps (k + 1) cs = .running cs' ev.toList ∧ R cs' ct') ∨
      (ev = none ∧ μ ct' < μ ct ∧ R cs ct')) ∧
  (∀ st, step mt Pt ct = .halt st → ∃ k st', run ms Ps k cs = .done [] st') ∧
  (step mt Pt ct = .ub → U cs ct ∨ SrcUB ms Ps cs)

theorem StepSimU.toStepSim {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {U : Cfg → Cfg → Prop} {cs ct : Cfg}
    (h : StepSimU ms Ps mt Pt R μ U cs ct) (hU : U cs ct → SrcUB ms Ps cs) :
    StepSim ms Ps mt Pt R μ cs ct := by
  obtain ⟨hn, hh, hu⟩ := h
  by_cases hs : Toy.PlaceEval.step mt Pt ct = .ub
  · rcases hu hs with h | h
    · exact Or.inl (hU h)
    · exact Or.inl h
  · exact Or.inr ⟨hn, hh, hs⟩

/-- `reach_of_sim` from the `next` part of `StepSimU`. -/
theorem reach_of_simU {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {U : Cfg → Cfg → Prop}
    (h : ∀ cs ct, R cs ct → StepSimU ms Ps mt Pt R μ U cs ct) :
    ∀ (n : Nat) (cs ct ct' : Cfg) (t : List Nat), R cs ct → run mt Pt n ct = .running ct' t →
      ∃ m cs', run ms Ps m cs = .running cs' t ∧ R cs' ct' :=
  reach_of_sim fun cs ct hR ev ct' hs => by
    rcases (h cs ct hR).1 ev ct' hs with h1 | ⟨h2, _, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h2, h3⟩

theorem run_one_next {mode : AllocMode} {P : Prog} {c c' : Cfg} {ev : Option Nat}
    (h : step mode P c = .next ev c') : run mode P 1 c = .running c' ev.toList := by
  rw [run_succ_next 0 h]; simp [run, Outcome.cons]

theorem srcUB_of_step_ub {mode : AllocMode} {P : Prog} {c : Cfg} (h : step mode P c = .ub) :
    SrcUB mode P c := ⟨1, run_succ_ub 0 h⟩

theorem srcUB_of_silent {mode : AllocMode} {P : Prog} {c c' : Cfg}
    (h : step mode P c = .next none c') (h' : SrcUB mode P c') : SrcUB mode P c := by
  obtain ⟨k, hk⟩ := h'
  exact ⟨k + 1, by rw [run_succ_next k h, hk]; rfl⟩

/-- A silent source step in front of a matched step. -/
theorem stepSim_of_silent {ms : AllocMode} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {cs cs1 ct : Cfg}
    (h1 : step ms Ps cs = .next none cs1) (h : StepSim ms Ps mt Pt R μ cs1 ct) :
    StepSim ms Ps mt Pt R μ cs ct := by
  rcases h with hub | ⟨hnext, hhalt, hnub⟩
  · exact Or.inl (srcUB_of_silent h1 hub)
  refine Or.inr ⟨fun ev ct' hst => ?_, fun st hst => ?_, hnub⟩
  · rcases hnext ev ct' hst with ⟨k, cs', hk, hR⟩ | ⟨rfl, _, hR⟩
    · exact Or.inl ⟨k + 1, cs', by rw [run_succ_next _ h1, hk]; rfl, hR⟩
    · exact Or.inl ⟨0, cs1, run_one_next h1, hR⟩
  · obtain ⟨k, st', hk⟩ := hhalt st hst
    exact ⟨k + 1, st', by rw [run_succ_next _ h1, hk]; rfl⟩

/-! ## Programs that differ in one block -/

theorem execStmt_congr {mode : AllocMode} {P P' : Prog} (h : P'.locals = P.locals)
    (st : State) (s : Stmt) : execStmt mode P' st s = execStmt mode P st s := by
  cases s <;> simp [execStmt, Prog.layout, h]

/-- Lockstep matching of one statement executed from the same state. -/
theorem stepSimU_cons {ms : AllocMode} {Ps Pt : Prog} {R : Cfg → Cfg → Prop} {μ : Cfg → Nat}
    {U : Cfg → Cfg → Prop} (hloc : Pt.locals = Ps.locals) (lbl : Label) (s : Stmt)
    (rs rt : List Stmt) (st : State) (hnext : ∀ st', R ⟨lbl, rs, st'⟩ ⟨lbl, rt, st'⟩) :
    StepSimU ms Ps ms Pt R μ U ⟨lbl, s :: rs, st⟩ ⟨lbl, s :: rt, st⟩ := by
  have ht : ∀ r, step ms Pt ⟨lbl, s :: r, st⟩ = step ms Ps ⟨lbl, s :: r, st⟩ := by
    intro r; simp only [step, execStmt_congr hloc]
  unfold StepSimU
  rw [ht]
  cases he : execStmt ms Ps st s with
  | ok ev st' =>
    have hsrc : step ms Ps ⟨lbl, s :: rs, st⟩ = .next ev ⟨lbl, rs, st'⟩ := by simp [step, he]
    have htgt : step ms Ps ⟨lbl, s :: rt, st⟩ = .next ev ⟨lbl, rt, st'⟩ := by simp [step, he]
    rw [htgt]
    refine ⟨fun ev' ct' hst => ?_, (fun st'' hst => by cases hst), (fun hst => by cases hst)⟩
    cases hst
    exact Or.inl ⟨0, _, run_one_next hsrc, hnext st'⟩
  | ub =>
    have hsrc : step ms Ps ⟨lbl, s :: rs, st⟩ = .ub := by simp [step, he]
    have htgt : step ms Ps ⟨lbl, s :: rt, st⟩ = .ub := by simp [step, he]
    rw [htgt]
    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun _ => Or.inr (srcUB_of_step_ub hsrc))⟩
  | block =>
    have htgt : step ms Ps ⟨lbl, s :: rt, st⟩ = .block := by simp [step, he]
    rw [htgt]
    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩

/-- Lockstep matching of a terminator that is the same in both programs. -/
theorem stepSimU_nil {ms : AllocMode} {Ps Pt : Prog} {R : Cfg → Cfg → Prop} {μ : Cfg → Nat}
    {U : Cfg → Cfg → Prop} (lbl : Label) (st : State)
    (hterm : (Pt.blk lbl).term = (Ps.blk lbl).term)
    (hentry : ∀ b, R (Ps.entry b st) (Pt.entry b st)) :
    StepSimU ms Ps ms Pt R μ U ⟨lbl, [], st⟩ ⟨lbl, [], st⟩ := by
  have hs : ∀ (P : Prog), step ms P ⟨lbl, [], st⟩ = match (P.blk lbl).term with
      | .goto b => .next none (P.entry b st)
      | .switchInt o arms ow =>
        match o.evalInt st with
        | some n => .next none (P.entry (selectTarget arms ow n) st)
        | none => .ub
      | .halt => .halt st
      | .unreachable => .ub := fun P => rfl
  unfold StepSimU
  rw [hs Pt, hterm]
  have hsrc := hs Ps
  cases ht : (Ps.blk lbl).term with
  | goto b =>
    rw [ht] at hsrc
    refine ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
    cases hst
    exact Or.inl ⟨0, _, run_one_next hsrc, hentry b⟩
  | switchInt o arms ow =>
    rw [ht] at hsrc
    cases hv : o.evalInt st with
    | some n =>
      simp only [hv] at hsrc ⊢
      refine ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
      cases hst
      exact Or.inl ⟨0, _, run_one_next hsrc, hentry _⟩
    | none =>
      simp only [hv] at hsrc ⊢
      exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h),
        (fun _ => Or.inr (srcUB_of_step_ub hsrc))⟩
  | halt =>
    rw [ht] at hsrc
    refine ⟨(fun _ _ h => by cases h), (fun st' hst => ?_), (fun h => by cases h)⟩
    cases hst
    exact ⟨1, st, run_succ_halt 0 hsrc⟩
  | unreachable =>
    rw [ht] at hsrc
    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h),
      (fun _ => Or.inr (srcUB_of_step_ub hsrc))⟩

/-- Lockstep matching of two statements with the same execution result. -/
theorem stepSimU_cons2 {ms : AllocMode} {Ps Pt : Prog} {R : Cfg → Cfg → Prop} {μ : Cfg → Nat}
    {U : Cfg → Cfg → Prop} (lbl : Label) (s t : Stmt) (rs rt : List Stmt) (st : State)
    (hexec : execStmt ms Pt st t = execStmt ms Ps st s)
    (hnext : ∀ st', R ⟨lbl, rs, st'⟩ ⟨lbl, rt, st'⟩) :
    StepSimU ms Ps ms Pt R μ U ⟨lbl, s :: rs, st⟩ ⟨lbl, t :: rt, st⟩ := by
  unfold StepSimU
  cases he : execStmt ms Ps st s with
  | ok ev st' =>
    have hsrc : step ms Ps ⟨lbl, s :: rs, st⟩ = .next ev ⟨lbl, rs, st'⟩ := by simp [step, he]
    have htgt : step ms Pt ⟨lbl, t :: rt, st⟩ = .next ev ⟨lbl, rt, st'⟩ := by
      simp [step, hexec, he]
    rw [htgt]
    refine ⟨fun ev' ct' hst => ?_, (fun st'' hst => by cases hst), (fun hst => by cases hst)⟩
    cases hst
    exact Or.inl ⟨0, _, run_one_next hsrc, hnext st'⟩
  | ub =>
    have hsrc : step ms Ps ⟨lbl, s :: rs, st⟩ = .ub := by simp [step, he]
    have htgt : step ms Pt ⟨lbl, t :: rt, st⟩ = .ub := by simp [step, hexec, he]
    rw [htgt]
    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h),
      (fun _ => Or.inr (srcUB_of_step_ub hsrc))⟩
  | block =>
    have htgt : step ms Pt ⟨lbl, t :: rt, st⟩ = .block := by simp [step, hexec, he]
    rw [htgt]
    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩

/-- A UB outcome after a running prefix: if the run from `c0` reaches `c` with trace `t` and
reaches UB after a prefix of `t`, then the run from `c` reaches UB without further events. -/
theorem srcUB_of_ub_prefix {mode : AllocMode} {P : Prog} {c0 c : Cfg} {m m' : Nat}
    {t u : List Nat} (hm : run mode P m c0 = .running c t) (hm' : run mode P m' c0 = .ub u)
    (hu : u <+: t) : SrcUB mode P c := by
  have hlt : m < m' := by
    refine Nat.lt_of_not_le fun hle => ?_
    have := run_finished_mono rfl hm' hle
    rw [hm] at this
    cases this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  rw [Nat.add_assoc, run_add_running m (k + 1) c0 c t hm] at hm'
  cases hr : run mode P (k + 1) c with
  | ub v =>
    rw [hr] at hm'
    simp only [Outcome.app, Outcome.ub.injEq] at hm'
    subst hm'
    have := hu.length_le
    simp only [List.length_append] at this
    have hv : v = [] := List.length_eq_zero_iff.1 (by omega)
    subst hv
    exact ⟨k + 1, hr⟩
  | done v s => rw [hr] at hm'; simp [Outcome.app] at hm'
  | running c' v => rw [hr] at hm'; simp [Outcome.app] at hm'
  | blocked => rw [hr] at hm'; simp [Outcome.app] at hm'

/-- Relation for programs differing in block `l`: same state and label; outside block `l` the
same remaining statements; inside block `l` remaining statements related by `Rl`. -/
def BRel (l : Label) (Rl : List Stmt → List Stmt → Prop) (cs ct : Cfg) : Prop :=
  cs.st = ct.st ∧ cs.lbl = ct.lbl ∧ (cs.lbl ≠ l → cs.rest = ct.rest) ∧
    (cs.lbl = l → Rl cs.rest ct.rest)

theorem bRel_entry {Ps Pt : Prog} {l : Label} {Rl : List Stmt → List Stmt → Prop}
    (hout : ∀ l', l' ≠ l → Pt.blk l' = Ps.blk l') (hl : Rl (Ps.blk l).stmts (Pt.blk l).stmts)
    (b : Label) (st : State) : BRel l Rl (Ps.entry b st) (Pt.entry b st) := by
  refine ⟨rfl, rfl, fun hb => ?_, fun hb => ?_⟩
  · simp [Prog.entry, hout b hb]
  · subst hb; exact hl

/-- Outside block `l`, related configurations are matched in lockstep. -/
theorem bRel_stepSimU_out {ms : AllocMode} {Ps Pt : Prog} {l : Label}
    {Rl : List Stmt → List Stmt → Prop} {μ : Cfg → Nat} {U : Cfg → Cfg → Prop}
    (hloc : Pt.locals = Ps.locals) (hout : ∀ l', l' ≠ l → Pt.blk l' = Ps.blk l')
    (hl : Rl (Ps.blk l).stmts (Pt.blk l).stmts) (lbl : Label) (hne : lbl ≠ l)
    (r : List Stmt) (st : State) :
    StepSimU ms Ps ms Pt (BRel l Rl) μ U ⟨lbl, r, st⟩ ⟨lbl, r, st⟩ := by
  cases r with
  | cons s r =>
    exact stepSimU_cons hloc lbl s r r st fun st' =>
      ⟨rfl, rfl, fun _ => rfl, fun h => absurd h hne⟩
  | nil => exact stepSimU_nil lbl st (by rw [hout lbl hne]) (fun b => bRel_entry hout hl b st)

/-! ### Facts about `Prog.setBlk` -/

theorem blk_setBlk_ne (P : Prog) {l l' : Label} (B : Block) (h : l' ≠ l) :
    (P.setBlk l B).blk l' = P.blk l' := by
  simp only [Prog.blk, Prog.setBlk, List.getD_eq_getElem?_getD, List.getElem?_set]
  split
  · exact absurd (Eq.symm ‹_›) h
  · rfl

theorem blk_setBlk_self (P : Prog) {l : Label} (B : Block) (hl : l < P.blocks.length) :
    (P.setBlk l B).blk l = B := by
  simp [Prog.blk, Prog.setBlk, List.getD_eq_getElem?_getD, hl]

theorem blk_eq_getElem {P : Prog} {l : Label} (hl : l < P.blocks.length) :
    P.blk l = P.blocks[l] := by
  simp [Prog.blk, List.getD_eq_getElem?_getD, hl]

theorem lt_length_of_stmt {P : Prog} {l : Label} {i : Nat} {s : Stmt}
    (h : (P.blk l).stmts[i]? = some s) : l < P.blocks.length := by
  refine Nat.lt_of_not_le fun hl' => ?_
  have hl : ¬ l < P.blocks.length := Nat.not_lt_of_le hl'
  have : P.blk l = Block.unreach := by
    simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  rw [this] at h
  simp [Block.unreach] at h

theorem lt_length_of_term {P : Prog} {l : Label} {o : Operand} {arms : List (Nat × Label)}
    {b : Label} (h : (P.blk l).term = .switchInt o arms b) : l < P.blocks.length := by
  refine Nat.lt_of_not_le fun hl' => ?_
  have hl : ¬ l < P.blocks.length := Nat.not_lt_of_le hl'
  have : P.blk l = Block.unreach := by
    simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  rw [this] at h
  simp [Block.unreach] at h

theorem hasMarkers_setBlk (P : Prog) (l : Label) (B : Block) (x : Local)
    (h : B.stmts.any (Stmt.isMarkerOf x) = (P.blk l).stmts.any (Stmt.isMarkerOf x)) :
    (P.setBlk l B).hasMarkers x = P.hasMarkers x := by
  by_cases hl : l < P.blocks.length
  · have e1 : P.blocks = P.blocks.take l ++ P.blocks[l] :: P.blocks.drop (l + 1) := by
      rw [← List.drop_eq_getElem_cons hl, List.take_append_drop]
    have e2 : P.blocks.set l B = P.blocks.take l ++ B :: P.blocks.drop (l + 1) := by
      simp [List.set_eq_take_append_cons_drop, hl]
    rw [blk_eq_getElem hl] at h
    simp only [Prog.hasMarkers, Prog.setBlk]
    rw [e2]
    conv => rhs; rw [e1]
    simp only [List.any_append, List.any_cons, h]
  · simp only [Prog.hasMarkers, Prog.setBlk]
    rw [List.set_eq_of_length_le (Nat.le_of_not_lt hl)]

theorem allocEntry_congr {mode : AllocMode} {P P' : Prog} (hl : P'.locals = P.locals)
    (hm : ∀ x, P'.hasMarkers x = P.hasMarkers x) :
    ∀ (xs : List Local) (st : State), allocEntry mode P' xs st = allocEntry mode P xs st
  | [], _ => rfl
  | x :: xs, st => by
    have ih : allocEntry mode P' xs = allocEntry mode P xs := funext (allocEntry_congr hl hm xs)
    simp only [allocEntry, hm x, Prog.layout, hl, ih]

theorem initState_congr {mode : AllocMode} {P P' : Prog} (hl : P'.locals = P.locals)
    (hm : ∀ x, P'.hasMarkers x = P.hasMarkers x) : P'.initState mode = P.initState mode := by
  simp only [Prog.initState, hl]
  exact allocEntry_congr hl hm _ _

end Toy.PlaceEval
