import Toy.ZstAssume.Examples

/-!
# Generic simulation infrastructure

Run algebra, totality and uniqueness of behaviours, and a forward simulation between a
left program `L` and a right program `Rt` with stuttering bounded by a measure. A
simulation may stop at configurations satisfying a predicate `Stop`; when every stop
makes `L` go wrong, the simulation yields prefix-preserving improvement.
-/

namespace Toy.ZstAssume

/-! ### Run algebra -/

/-- Prepend a finite trace to the trace of an outcome. -/
def Outcome.prepend (u : List Int) : Outcome → Outcome
  | .done t s => .done (u ++ t) s
  | .ub t => .ub (u ++ t)
  | .running c t => .running c (u ++ t)

@[simp] theorem Outcome.prepend_nil (r : Outcome) : r.prepend [] = r := by
  cases r <;> rfl

theorem Outcome.prepend_prepend (r : Outcome) (u v : List Int) :
    (r.prepend v).prepend u = r.prepend (u ++ v) := by
  cases r <;> simp [Outcome.prepend]

theorem Outcome.cons_eq_prepend (o : Option Int) (r : Outcome) :
    r.cons o = r.prepend o.toList := by
  cases r <;> rfl

@[simp] theorem Outcome.trace_prepend (r : Outcome) (u : List Int) :
    (r.prepend u).trace = u ++ r.trace := by
  cases r <;> rfl

@[simp] theorem Outcome.isRunning_prepend (r : Outcome) (u : List Int) :
    (r.prepend u).isRunning = r.isRunning := by
  cases r <;> rfl

theorem Outcome.prepend_eq_running {r : Outcome} {u t : List Int} {d : Cfg}
    (h : r.prepend u = .running d t) : ∃ t', r = .running d t' ∧ t = u ++ t' := by
  cases r with
  | done _ _ => cases h
  | ub _ => cases h
  | running d' t' => cases h; exact ⟨t', rfl, rfl⟩

theorem Outcome.prepend_eq_ub {r : Outcome} {u t : List Int}
    (h : r.prepend u = .ub t) : ∃ t', r = .ub t' ∧ t = u ++ t' := by
  cases r with
  | done _ _ => cases h
  | ub t' => cases h; exact ⟨t', rfl, rfl⟩
  | running _ _ => cases h

theorem Outcome.prepend_eq_done {r : Outcome} {u t : List Int} {s : State}
    (h : r.prepend u = .done t s) : ∃ t', r = .done t' s ∧ t = u ++ t' := by
  cases r with
  | done t' _ => cases h; exact ⟨t', rfl, rfl⟩
  | ub _ => cases h
  | running _ _ => cases h

/-- Running `n` steps to a running configuration and then `k` more steps. -/
theorem run_add_running {K : ZContract} {P : Prog} :
    ∀ (n k : Nat) (c d : Cfg) (t : List Int),
      run K P n c = .running d t → run K P (n + k) c = (run K P k d).prepend t
  | 0, k, c, d, t, h => by
    rw [run_zero] at h
    cases h
    simp
  | n + 1, k, c, d, t, h => by
    rw [Nat.add_right_comm]
    cases hs : step K P c with
    | next o c' =>
      rw [run_succ_next _ hs] at h ⊢
      rw [Outcome.cons_eq_prepend] at h
      obtain ⟨t', hr, rfl⟩ := Outcome.prepend_eq_running h
      rw [run_add_running n k c' d t' hr, Outcome.cons_eq_prepend, Outcome.prepend_prepend]
    | halt s => rw [run_succ_halt _ hs] at h; cases h
    | ub => rw [run_succ_ub _ hs] at h; cases h

theorem run_le_running {K : ZContract} {P : Prog} {n m : Nat} {c d : Cfg} {t : List Int}
    (h : run K P n c = .running d t) (hnm : n ≤ m) :
    run K P m c = (run K P (m - n) d).prepend t := by
  have := run_add_running (K := K) (P := P) n (m - n) c d t h
  rwa [Nat.add_sub_cancel' hnm] at this

/-- Traces grow monotonically with the fuel. -/
theorem run_trace_mono {K : ZContract} {P : Prog} {c : Cfg} {n m : Nat} (h : n ≤ m) :
    (run K P n c).trace <+: (run K P m c).trace := by
  cases hr : run K P n c with
  | done t s => rw [run_done_mono hr h]; exact List.prefix_refl _
  | ub t => rw [run_ub_mono hr h]; exact List.prefix_refl _
  | running d t =>
    rw [run_le_running hr h, Outcome.trace_prepend]
    exact List.prefix_append _ _

/-- Any two traces of the same run are comparable. -/
theorem run_trace_chain {K : ZContract} {P : Prog} {c : Cfg} (n m : Nat) :
    (run K P n c).trace <+: (run K P m c).trace ∨ (run K P m c).trace <+: (run K P n c).trace := by
  rcases Nat.le_total n m with h | h
  · exact Or.inl (run_trace_mono h)
  · exact Or.inr (run_trace_mono h)

theorem prefix_eq_of_chain {a b : List Int} (h : a <+: b ∨ b <+: a) (hl : a.length = b.length) :
    a = b := by
  rcases h with h | h
  · exact h.eq_of_length hl
  · exact (h.eq_of_length hl.symm).symm

theorem prefix_antisymm {a b : List Int} (h₁ : a <+: b) (h₂ : b <+: a) : a = b :=
  h₁.eq_of_length (Nat.le_antisymm h₁.length_le h₂.length_le)

theorem isRunning_of_le {K : ZContract} {P : Prog} {c : Cfg} {n m : Nat} (h : n ≤ m)
    (hm : (run K P m c).isRunning = true) : (run K P n c).isRunning = true := by
  cases hr : run K P n c with
  | done t s => rw [run_done_mono hr h] at hm; cases hm
  | ub t => rw [run_ub_mono hr h] at hm; cases hm
  | running _ _ => rfl

/-- Each step emits at most one value. -/
theorem run_succ_trace_length {K : ZContract} {P : Prog} :
    ∀ (n : Nat) (c : Cfg),
      (run K P (n + 1) c).trace.length ≤ (run K P n c).trace.length + 1
  | 0, c => by
    cases hs : step K P c with
    | next o c' =>
      rw [run_succ_next _ hs, Outcome.cons_eq_prepend]
      cases o <;> simp [run, Outcome.trace, Outcome.prepend]
    | halt s => rw [run_succ_halt _ hs]; simp [Outcome.trace]
    | ub => rw [run_succ_ub _ hs]; simp [Outcome.trace]
  | n + 1, c => by
    cases hs : step K P c with
    | next o c' =>
      rw [run_succ_next _ hs, run_succ_next _ hs, Outcome.cons_eq_prepend,
        Outcome.cons_eq_prepend, Outcome.trace_prepend, Outcome.trace_prepend,
        List.length_append, List.length_append]
      have := run_succ_trace_length (K := K) (P := P) n c'
      omega
    | halt s => rw [run_succ_halt _ hs, run_succ_halt _ hs]; simp
    | ub => rw [run_succ_ub _ hs, run_succ_ub _ hs]; simp

/-! ### Totality and uniqueness of behaviours -/

theorem exists_max_of_bdd (f : Nat → Nat) :
    ∀ N, (∀ n, f n ≤ N) → ∃ n₀, ∀ n, f n ≤ f n₀
  | 0, h => ⟨0, fun n => by have := h n; omega⟩
  | N + 1, h => by
    by_cases hx : ∃ n, f n = N + 1
    · obtain ⟨n₀, hn₀⟩ := hx
      exact ⟨n₀, fun n => by have := h n; omega⟩
    · refine exists_max_of_bdd f N (fun n => ?_)
      have h₁ := h n
      have h₂ : f n ≠ N + 1 := fun e => hx ⟨n, e⟩
      omega

/-- Discrete intermediate values of trace lengths. -/
theorem exists_trace_length_eq {K : ZContract} {P : Prog} {c : Cfg} (k : Nat) :
    ∀ M, k ≤ (run K P M c).trace.length → ∃ n, (run K P n c).trace.length = k
  | 0, h => ⟨0, by simp [run, Outcome.trace] at h ⊢; omega⟩
  | M + 1, h => by
    by_cases hk : k ≤ (run K P M c).trace.length
    · exact exists_trace_length_eq k M hk
    · have := run_succ_trace_length (K := K) (P := P) M c
      exact ⟨M + 1, by omega⟩

/-- Every configuration has a behaviour. -/
theorem hasBehFrom_exists (K : ZContract) (P : Prog) (c : Cfg) : ∃ b, HasBehFrom K P c b := by
  classical
  by_cases hfin : ∃ n, (run K P n c).isRunning = false
  · obtain ⟨n, hn⟩ := hfin
    cases hr : run K P n c with
    | done t s => exact ⟨.term t, n, s, hr⟩
    | ub t => exact ⟨.wrong t, n, hr⟩
    | running d t => rw [hr] at hn; cases hn
  · have hrun : ∀ n, (run K P n c).isRunning = true := by
      intro n
      cases h : (run K P n c).isRunning
      · exact absurd ⟨n, h⟩ hfin
      · rfl
    by_cases hbdd : ∃ N, ∀ n, (run K P n c).trace.length ≤ N
    · obtain ⟨N, hN⟩ := hbdd
      obtain ⟨n₀, hn₀⟩ := exists_max_of_bdd (fun n => (run K P n c).trace.length) N hN
      refine ⟨.div (run K P n₀ c).trace, hrun, n₀, fun n hn => ?_⟩
      have hp := run_trace_mono (K := K) (P := P) (c := c) hn
      exact (hp.eq_of_length (Nat.le_antisymm hp.length_le (hn₀ n))).symm
    · have hunb : ∀ i, ∃ n, i < (run K P n c).trace.length := by
        intro i
        refine Classical.byContradiction fun hne => hbdd ⟨i, fun n => ?_⟩
        exact Nat.le_of_not_lt fun hlt => hne ⟨n, hlt⟩
      let g : Nat → Nat := fun i => Classical.choose (hunb i)
      have hg : ∀ i, i < (run K P (g i) c).trace.length := fun i => Classical.choose_spec (hunb i)
      let f : Nat → Int := fun i => (run K P (g i) c).trace.getD i 0
      refine ⟨.react f, hrun, fun k => ?_⟩
      obtain ⟨M, hM⟩ := hunb k
      obtain ⟨n, hn⟩ := exists_trace_length_eq (K := K) (P := P) (c := c) k M (Nat.le_of_lt hM)
      refine ⟨n, List.ext_getElem (by simp [prefixOf, hn]) fun i h₁ h₂ => ?_⟩
      simp only [prefixOf, List.getElem_map, List.getElem_range, f, List.getD_eq_getElem?_getD]
      have hi := hg i
      rcases run_trace_chain (K := K) (P := P) (c := c) n (g i) with hp | hp
      · rw [hp.getElem h₁, List.getElem?_eq_getElem hi]
        rfl
      · rw [← hp.getElem hi, List.getElem?_eq_getElem hi]
        rfl

theorem div_react_absurd {K : ZContract} {P : Prog} {c : Cfg} {t : List Int} {f : Nat → Int}
    (hd : HasBehFrom K P c (.div t)) (hr : HasBehFrom K P c (.react f)) : False := by
  obtain ⟨N, hN⟩ := hd.2
  obtain ⟨n, hn⟩ := hr.2 (t.length + 1)
  have hp := run_trace_mono (K := K) (P := P) (c := c) (Nat.le_max_left n N)
  rw [hn, hN _ (Nat.le_max_right n N)] at hp
  have := hp.length_le
  simp [prefixOf] at this
  omega

/-- Behaviours are unique. -/
theorem hasBehFrom_unique {K : ZContract} {P : Prog} {c : Cfg} {b b' : Beh}
    (h : HasBehFrom K P c b) (h' : HasBehFrom K P c b') : b = b' := by
  cases b with
  | term t =>
    obtain ⟨n, s, hn⟩ := h
    exact ((hasBehFrom_iff_of_run_done hn b').1 h').symm
  | wrong t =>
    obtain ⟨n, hn⟩ := h
    exact ((hasBehFrom_iff_of_run_ub hn b').1 h').symm
  | div t =>
    cases b' with
    | term t' =>
      obtain ⟨n, s, hn⟩ := h'
      exact (hasBehFrom_iff_of_run_done hn _).1 h
    | wrong t' =>
      obtain ⟨n, hn⟩ := h'
      exact (hasBehFrom_iff_of_run_ub hn _).1 h
    | div t' =>
      obtain ⟨N, hN⟩ := h.2
      obtain ⟨N', hN'⟩ := h'.2
      rw [← hN (max N N') (Nat.le_max_left _ _), ← hN' (max N N') (Nat.le_max_right _ _)]
    | react f => exact (div_react_absurd h h').elim
  | react f =>
    cases b' with
    | term t' =>
      obtain ⟨n, s, hn⟩ := h'
      exact (hasBehFrom_iff_of_run_done hn _).1 h
    | wrong t' =>
      obtain ⟨n, hn⟩ := h'
      exact (hasBehFrom_iff_of_run_ub hn _).1 h
    | div t' => exact (div_react_absurd h' h).elim
    | react g =>
      congr 1
      funext i
      obtain ⟨n, hn⟩ := h.2 (i + 1)
      obtain ⟨n', hn'⟩ := h'.2 (i + 1)
      have he := prefix_eq_of_chain (run_trace_chain (K := K) (P := P) (c := c) n n')
        (by rw [hn, hn']; simp [prefixOf])
      rw [hn, hn'] at he
      have := congrArg (fun l => l[i]?) he
      simpa [prefixOf] using this

/-! ### Prefixes of behaviours -/

theorem hasPrefix_react_iff (f : Nat → Int) (t : List Int) :
    (Beh.react f).HasPrefix t ↔ ∀ i (h : i < t.length), t[i] = f i := by
  simp only [Beh.HasPrefix]
  constructor
  · intro h i hi
    have : t[i] = (prefixOf f t.length)[i]'(by simp [prefixOf]; exact hi) := by
      congr 1
    rw [this]
    simp [prefixOf]
  · intro h
    exact List.ext_getElem (by simp [prefixOf]) fun i h₁ _ => by simp [prefixOf, h i h₁]

theorem Beh.HasPrefix.of_prefix {b : Beh} {t t' : List Int} (h : b.HasPrefix t)
    (h' : t' <+: t) : b.HasPrefix t' := by
  cases b with
  | term u => exact h'.trans h
  | wrong u => exact h'.trans h
  | div u => exact h'.trans h
  | react f =>
    rw [hasPrefix_react_iff] at h ⊢
    intro i hi
    rw [h'.getElem hi]
    exact h i _

/-- Every finite trace of the run is a prefix of the behaviour. -/
theorem hasPrefix_trace {K : ZContract} {P : Prog} {c : Cfg} {b : Beh}
    (hb : HasBehFrom K P c b) (n : Nat) : b.HasPrefix (run K P n c).trace := by
  cases b with
  | term u =>
    obtain ⟨m, s, hm⟩ := hb
    have hp := run_trace_mono (K := K) (P := P) (c := c) (Nat.le_max_left n m)
    rwa [run_done_mono hm (Nat.le_max_right n m)] at hp
  | wrong u =>
    obtain ⟨m, hm⟩ := hb
    have hp := run_trace_mono (K := K) (P := P) (c := c) (Nat.le_max_left n m)
    rwa [run_ub_mono hm (Nat.le_max_right n m)] at hp
  | div u =>
    obtain ⟨N, hN⟩ := hb.2
    have hp := run_trace_mono (K := K) (P := P) (c := c) (Nat.le_max_left n N)
    rwa [hN _ (Nat.le_max_right n N)] at hp
  | react f =>
    obtain ⟨m, hm⟩ := hb.2 (run K P n c).trace.length
    show _ = _
    have := prefix_eq_of_chain (run_trace_chain (K := K) (P := P) (c := c) n m)
      (by rw [hm]; simp [prefixOf])
    rw [this, hm]
    simp [prefixOf]

theorem hasPrefix_of_running {K : ZContract} {P : Prog} {c d : Cfg} {n : Nat} {t : List Int}
    {b : Beh} (hb : HasBehFrom K P c b) (h : run K P n c = .running d t) : b.HasPrefix t := by
  have := hasPrefix_trace hb n
  rwa [h] at this

/-- A run that passes `d` with trace `t` and goes wrong after `w` goes wrong from `d`. -/
theorem goesWrong_suffix {K : ZContract} {P : Prog} {c d : Cfg} {n : Nat} {t w : List Int}
    (h : run K P n c = .running d t) (hw : HasBehFrom K P c (.wrong w)) :
    ∃ u, w = t ++ u ∧ GoesWrongFrom K P d u := by
  obtain ⟨N, hN⟩ := hw
  rcases Nat.lt_or_ge N n with hlt | hge
  · rw [run_ub_mono hN (Nat.le_of_lt hlt)] at h
    cases h
  · rw [run_le_running h hge] at hN
    obtain ⟨u, hu, rfl⟩ := Outcome.prepend_eq_ub hN
    exact ⟨u, rfl, N - n, hu⟩

/-- A run that passes `d` with trace `t` and goes wrong after a prefix of `t` goes wrong from
`d` without further events. -/
theorem goesWrong_nil_of_prefix {K : ZContract} {P : Prog} {c d : Cfg} {n : Nat}
    {t w : List Int} (h : run K P n c = .running d t) (hw : HasBehFrom K P c (.wrong w))
    (hwt : w <+: t) : GoesWrongFrom K P d [] := by
  obtain ⟨u, rfl, hu⟩ := goesWrong_suffix h hw
  have := hwt.length_le
  simp at this
  have hu0 : u.length = 0 := by omega
  rw [List.length_eq_zero_iff] at hu0
  subst hu0
  exact hu

theorem goesWrong_prepend {K : ZContract} {P : Prog} {c d : Cfg} {n : Nat} {t u : List Int}
    (h : run K P n c = .running d t) (hu : GoesWrongFrom K P d u) :
    GoesWrongFrom K P c (t ++ u) := by
  obtain ⟨m, hm⟩ := hu
  exact ⟨n + m, by rw [run_add_running n m c d t h, hm]; rfl⟩

theorem run_done_prepend {K : ZContract} {P : Prog} {c d : Cfg} {n m : Nat} {t u : List Int}
    {s : State} (h : run K P n c = .running d t) (hm : run K P m d = .done u s) :
    run K P (n + m) c = .done (t ++ u) s := by
  rw [run_add_running n m c d t h, hm]; rfl

theorem goesWrong_of_step_ub {K : ZContract} {P : Prog} {c : Cfg} (h : step K P c = .ub) :
    GoesWrongFrom K P c [] :=
  ⟨1, run_succ_ub 0 h⟩

theorem run_succ_ub_of_running {K : ZContract} {P : Prog} {c d : Cfg} {k : Nat}
    {t : List Int} (h : run K P k c = .running d t) (hd : step K P d = .ub) :
    run K P (k + 1) c = .ub t := by
  rw [run_add_running k 1 c d t h, run_succ_ub 0 hd]; simp [Outcome.prepend]

/-- Determinism: a terminating run does not go wrong. -/
theorem not_goesWrong_of_done {K : ZContract} {P : Prog} {c : Cfg} {n : Nat} {t u : List Int}
    {s : State} (h : run K P n c = .done t s) : ¬ GoesWrongFrom K P c u := by
  intro hw
  have := (hasBehFrom_iff_of_run_done h (.wrong u)).1 hw
  cases this

/-! ### Refinement from per-input improvement -/

theorem refinesPP_of_improves {K : ZContract} {src tgt : Prog}
    (h : ∀ σ bs bt, HasBeh K src σ bs → HasBeh K tgt σ bt → ImprovesPP bt bs) :
    RefinesPP K src tgt := by
  intro σ bt hbt
  obtain ⟨bs, hbs⟩ := hasBehFrom_exists K src (src.init σ)
  exact ⟨bs, hbs, h σ bs bt hbs hbt⟩

theorem refinesWT_of_improves {K : ZContract} {src tgt : Prog}
    (h : ∀ σ bs bt, HasBeh K src σ bs → HasBeh K tgt σ bt → ImprovesWT bt bs) :
    RefinesWT K src tgt := by
  intro σ bt hbt
  obtain ⟨bs, hbs⟩ := hasBehFrom_exists K src (src.init σ)
  exact ⟨bs, hbs, h σ bs bt hbs hbt⟩

theorem RefinesPP.improves {K : ZContract} {src tgt : Prog} (h : RefinesPP K src tgt)
    {σ : State} {bs bt : Beh} (hbs : HasBeh K src σ bs) (hbt : HasBeh K tgt σ bt) :
    ImprovesPP bt bs := by
  obtain ⟨bs', hbs', himp⟩ := h σ bt hbt
  rwa [hasBehFrom_unique hbs hbs']

theorem RefinesWT.improves {K : ZContract} {src tgt : Prog} (h : RefinesWT K src tgt)
    {σ : State} {bs bt : Beh} (hbs : HasBeh K src σ bs) (hbt : HasBeh K tgt σ bt) :
    ImprovesWT bt bs := by
  obtain ⟨bs', hbs', himp⟩ := h σ bt hbt
  rwa [hasBehFrom_unique hbs hbs']

/-- If the source passes `c` with trace `t` and goes wrong from there silently, and the
target refines the source (prefix-preserving) while passing `d` with the same trace, then
the target goes wrong from `d` silently. -/
theorem goesWrong_nil_of_refinesPP {K : ZContract} {src tgt : Prog} {σ : State}
    (href : RefinesPP K tgt src) {n m : Nat} {c d : Cfg} {t : List Int}
    (hc : run K src n (src.init σ) = .running c t) (hcw : GoesWrongFrom K src c [])
    (hd : run K tgt m (tgt.init σ) = .running d t) : GoesWrongFrom K tgt d [] := by
  have hw : HasBeh K src σ (.wrong t) := by
    have := goesWrong_prepend hc hcw
    rwa [List.append_nil] at this
  obtain ⟨bt, hbt, himp⟩ := href σ _ hw
  have hp := hasPrefix_of_running hbt hd
  rcases himp with h | ⟨t', ht', hpre⟩
  · subst h
    exact goesWrong_nil_of_prefix hd hbt (List.prefix_refl _)
  · subst ht'
    simp only [Beh.HasPrefix] at hp hpre
    exact goesWrong_nil_of_prefix hd hbt hpre

/-- Whole-trace version of `goesWrong_nil_of_refinesPP`. -/
theorem goesWrong_of_refinesWT {K : ZContract} {src tgt : Prog} {σ : State}
    (href : RefinesWT K tgt src) {n m : Nat} {c d : Cfg} {t u : List Int}
    (hc : run K src n (src.init σ) = .running c t) (hcw : GoesWrongFrom K src c u)
    (hd : run K tgt m (tgt.init σ) = .running d t) : ∃ u', GoesWrongFrom K tgt d u' := by
  obtain ⟨bt, hbt, himp⟩ := href σ (.wrong (t ++ u))
    (show HasBeh K src σ (.wrong (t ++ u)) from goesWrong_prepend hc hcw)
  rcases himp with h | ⟨t', rfl⟩
  · rw [← h] at hbt
    obtain ⟨u', -, hu'⟩ := goesWrong_suffix hd hbt
    exact ⟨u', hu'⟩
  · obtain ⟨u', -, hu'⟩ := goesWrong_suffix hd hbt
    exact ⟨u', hu'⟩

/-! ### Forward simulation with stuttering -/

/-- Reachability of a configuration from the initial configuration of some input. -/
def Reach (K : ZContract) (P : Prog) (c : Cfg) : Prop :=
  ∃ σ n t, run K P n (P.init σ) = .running c t

theorem reach_init (K : ZContract) (P : Prog) (σ : State) : Reach K P (P.init σ) :=
  ⟨σ, 0, [], rfl⟩

theorem reach_run {K : ZContract} {P : Prog} {c d : Cfg} {k : Nat} {u : List Int}
    (hc : Reach K P c) (h : run K P k c = .running d u) : Reach K P d := by
  obtain ⟨σ, n, t, hn⟩ := hc
  exact ⟨σ, n + k, t ++ u, by rw [run_add_running n k _ c t hn, h]; rfl⟩

theorem reach_step {K : ZContract} {P : Prog} {c c' : Cfg} {o : Option Int}
    (hc : Reach K P c) (h : step K P c = .next o c') : Reach K P c' :=
  reach_run (k := 1) hc (by rw [run_succ_next 0 h]; rfl)

theorem reachableAt_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat) (st : State) :
    ReachableAt K P l i st ↔ Reach K P (P.at l i st) := Iff.rfl

/-- One simulation step from related configurations `c` (of `L`) and `d` (of `Rt`): either
`c` is a stop, or `L` halts and `Rt` halts in the same state without emitting, or `L`
steps and `Rt` follows in `k` steps with the same emitted value to a related configuration,
the measure decreasing when `Rt` does not move. -/
def SimStep (K : ZContract) (L Rt : Prog) (R : Cfg → Cfg → Prop) (μ : Cfg → Cfg → Nat)
    (Stop : Cfg → Prop) (c d : Cfg) : Prop :=
  Stop c ∨
    (∃ s, step K L c = .halt s ∧ ∃ k, run K Rt k d = .done [] s) ∨
    ∃ o c', step K L c = .next o c' ∧ ∃ k d', run K Rt k d = .running d' o.toList ∧ R c' d' ∧
      (k = 0 → μ c' d' < μ c d)

/-- A simulation of `L` by `Rt` with relation `R`, measure `μ` bounded by `B`, and stops. -/
structure IsSim (K : ZContract) (L Rt : Prog) (R : Cfg → Cfg → Prop) (μ : Cfg → Cfg → Nat)
    (Stop : Cfg → Prop) (B : Nat) : Prop where
  bound : ∀ c d, μ c d ≤ B
  step : ∀ c d, R c d → SimStep K L Rt R μ Stop c d

/-- Within `n` steps from `c`, `L` reaches a stop `c'` with trace `t` while `Rt`, from `d`,
reaches a configuration related to `c'` with the same trace. -/
def StopBy (K : ZContract) (L Rt : Prog) (R : Cfg → Cfg → Prop) (Stop : Cfg → Prop)
    (c d : Cfg) (n : Nat) (t : List Int) : Prop :=
  ∃ k, k ≤ n ∧ ∃ c' m d', run K L k c = .running c' t ∧ Stop c' ∧
    run K Rt m d = .running d' t ∧ R c' d'

/-- What the right program matches of an outcome of the left program. -/
def SimOut (K : ZContract) (Rt : Prog) (R : Cfg → Cfg → Prop) (μ : Cfg → Cfg → Nat) (B n : Nat)
    (d : Cfg) (μ₀ : Nat) : Outcome → Prop
  | .done t s => ∃ m, run K Rt m d = .done t s
  | .ub _ => False
  | .running c' t => ∃ m d', run K Rt m d = .running d' t ∧ R c' d' ∧
      n + μ c' d' ≤ (B + 1) * m + μ₀

/-- The run lemma of a simulation. -/
theorem sim_run {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop} {μ : Cfg → Cfg → Nat}
    {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B) :
    ∀ n c d, R c d →
      (∃ t', t' <+: (run K L n c).trace ∧ StopBy K L Rt R Stop c d n t') ∨
        SimOut K Rt R μ B n d (μ c d) (run K L n c)
  | 0, c, d, hR => Or.inr ⟨0, d, rfl, hR, by simp⟩
  | n + 1, c, d, hR => by
    rcases hS.step c d hR with hstop | ⟨s, hs, k, hk⟩ | ⟨o, c', hs, k, d', hk, hR', hμ⟩
    · exact Or.inl ⟨[], List.nil_prefix, 0, Nat.zero_le _, c, 0, d, rfl, hstop, rfl, hR⟩
    · rw [run_succ_halt _ hs]
      exact Or.inr ⟨k, hk⟩
    · rw [run_succ_next _ hs, Outcome.cons_eq_prepend]
      rcases sim_run hS n c' d' hR' with ⟨t', ht', k', hk', c'', m', d'', h1, hst, h2, hR''⟩ | hout
      · refine Or.inl ⟨o.toList ++ t', ?_, k' + 1, by omega, c'', k + m', d'', ?_, hst, ?_, hR''⟩
        · rw [Outcome.trace_prepend]
          exact (List.prefix_append_right_inj _).2 ht'
        · rw [run_succ_next _ hs, h1]; rfl
        · rw [run_add_running k m' d d' _ hk, h2]; rfl
      · right
        cases hr : run K L n c' with
        | done t s =>
          rw [hr] at hout
          obtain ⟨m, hm⟩ := hout
          exact ⟨k + m, by rw [run_add_running k m d d' _ hk, hm]; rfl⟩
        | ub t => rw [hr] at hout; exact hout.elim
        | running c'' t =>
          rw [hr] at hout
          obtain ⟨m, d'', hm, hR'', hpot⟩ := hout
          refine ⟨k + m, d'', by rw [run_add_running k m d d' _ hk, hm]; rfl, hR'', ?_⟩
          have hb := hS.bound c' d'
          rw [Nat.mul_add]
          rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · have := hμ rfl
            simp only [Nat.mul_zero, Nat.zero_add]
            omega
          · have : B + 1 ≤ (B + 1) * k := Nat.le_mul_of_pos_right _ hkpos
            generalize (B + 1) * k = X at *
            generalize (B + 1) * m = Y at *
            omega

/-- If `L` runs forever and `Rt` tracks its traces at unboundedly many fuels, `Rt` has
every (necessarily diverging) behaviour of `L`. -/
theorem hasBehFrom_of_tracking {K : ZContract} {L Rt : Prog} {c d : Cfg}
    (hL : ∀ n, (run K L n c).isRunning = true) (g : Nat → Nat)
    (hg : ∀ n, ∃ d', run K Rt (g n) d = .running d' (run K L n c).trace)
    (hunb : ∀ M, ∃ n, M ≤ g n) {b : Beh} (hb : HasBehFrom K L c b) : HasBehFrom K Rt d b := by
  have hRt : ∀ M, (run K Rt M d).isRunning = true := by
    intro M
    obtain ⟨n, hn⟩ := hunb M
    obtain ⟨d', hd'⟩ := hg n
    exact isRunning_of_le hn (by rw [hd']; rfl)
  have htr : ∀ n, (run K Rt (g n) d).trace = (run K L n c).trace := by
    intro n
    obtain ⟨d', hd'⟩ := hg n
    rw [hd']; rfl
  cases b with
  | term t =>
    obtain ⟨n, s, hn⟩ := hb
    have := hL n
    rw [hn] at this
    cases this
  | wrong t =>
    obtain ⟨n, hn⟩ := hb
    have := hL n
    rw [hn] at this
    cases this
  | div t =>
    obtain ⟨N, hN⟩ := hb.2
    refine ⟨hRt, g N, fun M hM => ?_⟩
    have h₁ : t <+: (run K Rt M d).trace := by
      rw [← hN N (Nat.le_refl N), ← htr N]
      exact run_trace_mono hM
    obtain ⟨n₁, hn₁⟩ := hunb M
    have h₂ : (run K Rt M d).trace <+: t := by
      refine (run_trace_mono hn₁).trans ?_
      rw [htr n₁, ← hN (max n₁ N) (Nat.le_max_right _ _)]
      exact run_trace_mono (Nat.le_max_left _ _)
    exact prefix_antisymm h₂ h₁
  | react f =>
    refine ⟨hRt, fun k => ?_⟩
    obtain ⟨n, hn⟩ := hb.2 k
    exact ⟨g n, by rw [htr n, hn]⟩

/-- Behaviour transfer: `Rt` has the behaviour of `L`, or `L` reaches a stop along a prefix
of its behaviour. -/
theorem sim_transfer {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B)
    {c d : Cfg} (hR : R c d) {b : Beh} (hb : HasBehFrom K L c b) :
    HasBehFrom K Rt d b ∨ ∃ n t, b.HasPrefix t ∧ StopBy K L Rt R Stop c d n t := by
  classical
  by_cases hstop : ∃ n t, t <+: (run K L n c).trace ∧ StopBy K L Rt R Stop c d n t
  · obtain ⟨n, t, ht, hst⟩ := hstop
    exact Or.inr ⟨n, t, (hasPrefix_trace hb n).of_prefix ht, hst⟩
  · left
    have hout : ∀ n, SimOut K Rt R μ B n d (μ c d) (run K L n c) := by
      intro n
      rcases sim_run hS n c d hR with ⟨t, ht, hst⟩ | h
      · exact absurd ⟨n, t, ht, hst⟩ hstop
      · exact h
    cases b with
    | term t =>
      obtain ⟨n, s, hn⟩ := hb
      have := hout n
      rw [hn] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, s, hm⟩
    | wrong t =>
      obtain ⟨n, hn⟩ := hb
      have := hout n
      rw [hn] at this
      exact this.elim
    | div t =>
      have hL := hb.1
      have hg : ∀ n, ∃ m d', run K Rt m d = .running d' (run K L n c).trace ∧
          n ≤ (B + 1) * m + B := by
        intro n
        have h := hout n
        cases hr : run K L n c with
        | done _ _ => have := hL n; rw [hr] at this; cases this
        | ub _ => have := hL n; rw [hr] at this; cases this
        | running c' t =>
          rw [hr] at h
          obtain ⟨m, d', hm, -, hpot⟩ := h
          have := hS.bound c d
          exact ⟨m, d', hm, by omega⟩
      let g : Nat → Nat := fun n => Classical.choose (hg n)
      have hgs : ∀ n, ∃ d', run K Rt (g n) d = .running d' (run K L n c).trace ∧
          n ≤ (B + 1) * g n + B := fun n => Classical.choose_spec (hg n)
      refine hasBehFrom_of_tracking hL g (fun n => ?_) (fun M => ?_) hb
      · obtain ⟨d', hd', -⟩ := hgs n
        exact ⟨d', hd'⟩
      refine ⟨(B + 1) * M + B + 1, Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left (a := B + 1) ?_)⟩
      obtain ⟨-, -, this⟩ := hgs ((B + 1) * M + B + 1)
      generalize (B + 1) * g ((B + 1) * M + B + 1) = X at *
      generalize (B + 1) * M = Y at *
      omega
    | react f =>
      have hL := hb.1
      have hg : ∀ n, ∃ m d', run K Rt m d = .running d' (run K L n c).trace ∧
          n ≤ (B + 1) * m + B := by
        intro n
        have h := hout n
        cases hr : run K L n c with
        | done _ _ => have := hL n; rw [hr] at this; cases this
        | ub _ => have := hL n; rw [hr] at this; cases this
        | running c' t =>
          rw [hr] at h
          obtain ⟨m, d', hm, -, hpot⟩ := h
          have := hS.bound c d
          exact ⟨m, d', hm, by omega⟩
      let g : Nat → Nat := fun n => Classical.choose (hg n)
      have hgs : ∀ n, ∃ d', run K Rt (g n) d = .running d' (run K L n c).trace ∧
          n ≤ (B + 1) * g n + B := fun n => Classical.choose_spec (hg n)
      refine hasBehFrom_of_tracking hL g (fun n => ?_) (fun M => ?_) hb
      · obtain ⟨d', hd', -⟩ := hgs n
        exact ⟨d', hd'⟩
      refine ⟨(B + 1) * M + B + 1, Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left (a := B + 1) ?_)⟩
      obtain ⟨-, -, this⟩ := hgs ((B + 1) * M + B + 1)
      generalize (B + 1) * g ((B + 1) * M + B + 1) = X at *
      generalize (B + 1) * M = Y at *
      omega

/-- A stop reached by `L` from which `L` goes wrong makes `L` go wrong. -/
theorem stopBy_goesWrong {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {Stop : Cfg → Prop} (hStop : ∀ c, Stop c → ∃ u, GoesWrongFrom K L c u) {c d : Cfg}
    {n : Nat} {t : List Int} (h : StopBy K L Rt R Stop c d n t) :
    ∃ u, HasBehFrom K L c (.wrong (t ++ u)) := by
  obtain ⟨k, -, c', m, d', h1, hst, -, -⟩ := h
  obtain ⟨u, hu⟩ := hStop c' hst
  exact ⟨u, goesWrong_prepend h1 hu⟩

/-- Prefix-preserving improvement from a simulation whose stops make `L` go wrong
silently. -/
theorem sim_improvesPP {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B)
    (hStop : ∀ c, Stop c → GoesWrongFrom K L c []) {c d : Cfg} (hR : R c d) {bs bt : Beh}
    (hbs : HasBehFrom K L c bs) (hbt : HasBehFrom K Rt d bt) : ImprovesPP bt bs := by
  rcases sim_transfer hS hR hbs with h | ⟨n, t, -, k, -, c', m, d', h1, hst, h2, -⟩
  · exact Or.inl (hasBehFrom_unique hbt h)
  · have hw : HasBehFrom K L c (.wrong (t ++ [])) := goesWrong_prepend h1 (hStop c' hst)
    rw [List.append_nil] at hw
    rw [hasBehFrom_unique hbs hw]
    exact Or.inr ⟨t, rfl, hasPrefix_of_running hbt h2⟩

/-- A non-wrong behaviour of `L` transfers to `Rt` when every stop makes `L` go wrong. -/
theorem sim_beh_of_not_wrong {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B)
    (hStop : ∀ c, Stop c → ∃ u, GoesWrongFrom K L c u) {c d : Cfg} (hR : R c d) {b : Beh}
    (hb : HasBehFrom K L c b) (hnw : ∀ t, b ≠ .wrong t) : HasBehFrom K Rt d b := by
  rcases sim_transfer hS hR hb with h | ⟨n, t, -, hst⟩
  · exact h
  · obtain ⟨u, hu⟩ := stopBy_goesWrong hStop hst
    exact absurd (hasBehFrom_unique hb hu) (hnw _)

/-- Termination with a final state transfers when every stop makes `L` go wrong. -/
theorem sim_done {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B)
    (hStop : ∀ c, Stop c → ∃ u, GoesWrongFrom K L c u) {c d : Cfg} (hR : R c d) {n : Nat}
    {t : List Int} {s : State} (h : run K L n c = .done t s) : ∃ m, run K Rt m d = .done t s := by
  rcases sim_run hS n c d hR with ⟨t', -, hst⟩ | hout
  · obtain ⟨u, hu⟩ := stopBy_goesWrong hStop hst
    exact (not_goesWrong_of_done h hu).elim
  · rw [h] at hout
    exact hout

/-- `L` reaching `c'` is matched by `Rt` reaching a related configuration with the same
trace, provided no stop leads back to `c'` in one or more steps. -/
theorem sim_reach {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B)
    {c d c' : Cfg} (hR : R c d) {n : Nat} {t : List Int} (h : run K L n c = .running c' t)
    (hiso : ∀ c₀, Stop c₀ → ∀ j u, run K L (j + 1) c₀ ≠ .running c' u) :
    ∃ m d', run K Rt m d = .running d' t ∧ R c' d' := by
  rcases sim_run hS n c d hR with ⟨t', -, k, hk, c'', m, d'', h1, hst, h2, hR''⟩ | hout
  · rcases Nat.lt_or_ge k n with hlt | hge
    · exfalso
      rw [run_le_running h1 (Nat.le_of_lt hlt)] at h
      obtain ⟨u, hu, -⟩ := Outcome.prepend_eq_running h
      obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
      rw [hj] at hu
      exact hiso c'' hst j u hu
    · have hkn : k = n := Nat.le_antisymm hk hge
      subst hkn
      rw [h1] at h
      cases h
      exact ⟨m, d'', h2, hR''⟩
  · rw [h] at hout
    obtain ⟨m, d', hm, hR', -⟩ := hout
    exact ⟨m, d', hm, hR'⟩

theorem iso_of_step_ub {K : ZContract} {L : Prog} {c₀ : Cfg} (h : step K L c₀ = .ub) (c' : Cfg)
    (j : Nat) (u : List Int) : run K L (j + 1) c₀ ≠ .running c' u := by
  rw [run_succ_ub j h]
  intro e
  cases e

/-- Suppose every stop is an actual UB step of `L` or satisfies `Special`, and `Rt` goes
wrong silently from every configuration related to a `Special` one. If `L` reaches a
`Special` configuration `c'` with trace `t`, then `Rt` goes wrong after a prefix of `t`. -/
theorem sim_necessity {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K L Rt R μ Stop B)
    {Special : Cfg → Prop}
    (hStop : ∀ c, Stop c → step K L c = .ub ∨ Special c)
    (hSp : ∀ c d, Special c → R c d → GoesWrongFrom K Rt d [])
    {σ : State} (hR : R (L.init σ) (Rt.init σ)) {n : Nat} {c' : Cfg} {t : List Int}
    (h : run K L n (L.init σ) = .running c' t) (hc' : Special c') :
    ∃ t', t' <+: t ∧ HasBeh K Rt σ (.wrong t') := by
  rcases sim_run hS n _ _ hR with ⟨t', ht', k, hk, c'', m, d'', h1, hst, h2, hR''⟩ | hout
  · rw [h] at ht'
    rcases hStop c'' hst with hub | hsp
    · rcases Nat.lt_or_ge k n with hlt | hge
      · rw [run_ub_mono (run_succ_ub_of_running h1 hub) (by omega : k + 1 ≤ n)] at h
        cases h
      · have hkn : k = n := Nat.le_antisymm hk hge
        subst hkn
        rw [h1] at h
        cases h
        have := goesWrong_prepend h2 (hSp _ _ hc' hR'')
        rw [List.append_nil] at this
        exact ⟨_, ht', this⟩
    · have := goesWrong_prepend h2 (hSp _ _ hsp hR'')
      rw [List.append_nil] at this
      exact ⟨t', ht', this⟩
  · rw [h] at hout
    obtain ⟨m, d', hm, hR', -⟩ := hout
    have := goesWrong_prepend hm (hSp _ _ hc' hR')
    rw [List.append_nil] at this
    exact ⟨t, List.prefix_refl _, this⟩

/-! ### Refinement, equivalence and `wp` from simulations -/

theorem refinesPP_of_sim {K : ZContract} {src tgt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K src tgt R μ Stop B)
    (hStop : ∀ c, Stop c → GoesWrongFrom K src c [])
    (hinit : ∀ σ, R (src.init σ) (tgt.init σ)) : RefinesPP K src tgt :=
  refinesPP_of_improves fun σ _ _ hbs hbt => sim_improvesPP hS hStop (hinit σ) hbs hbt

theorem refinesWT_of_sim {K : ZContract} {src tgt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K src tgt R μ Stop B)
    (hStop : ∀ c, Stop c → ∃ u, GoesWrongFrom K src c u)
    (hinit : ∀ σ, R (src.init σ) (tgt.init σ)) : RefinesWT K src tgt := by
  refine refinesWT_of_improves fun σ bs bt hbs hbt => ?_
  by_cases hw : ∃ t, bs = .wrong t
  · obtain ⟨t, rfl⟩ := hw
    exact Or.inr ⟨t, rfl⟩
  · exact Or.inl (hasBehFrom_unique hbt
      (sim_beh_of_not_wrong hS hStop (hinit σ) hbs fun t h => hw ⟨t, h⟩))

theorem wp_of_sim {K : ZContract} {src tgt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {B : Nat} (hS : IsSim K src tgt R μ Stop B)
    (hStop : ∀ c, Stop c → ∃ u, GoesWrongFrom K src c u)
    (hinit : ∀ σ, R (src.init σ) (tgt.init σ)) (Q : List Int → State → Prop) (σ : State) :
    wp K src Q σ → wp K tgt Q σ := by
  rintro ⟨n, t, s, hn, hq⟩
  obtain ⟨m, hm⟩ := sim_done hS hStop (hinit σ) hn
  exact ⟨m, t, s, hm, hq⟩

/-- Necessity of the silent-UB condition, prefix-preserving form: if `Rt` refines `L` and
the simulation stops at a reachable `Special` configuration `c'` of `L` (where `Rt` goes
wrong silently from every related configuration), then `L` goes wrong silently from
`c'`. -/
theorem goesWrong_nil_of_sim_necessity {K : ZContract} {L Rt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Cfg → Nat} {Stop Special : Cfg → Prop} {B : Nat}
    (hS : IsSim K L Rt R μ Stop B) (hStop : ∀ c, Stop c → step K L c = .ub ∨ Special c)
    (hSp : ∀ c d, Special c → R c d → GoesWrongFrom K Rt d [])
    (hinit : ∀ σ, R (L.init σ) (Rt.init σ)) (href : RefinesPP K L Rt) {c' : Cfg}
    (hreach : Reach K L c') (hc' : Special c') : GoesWrongFrom K L c' [] := by
  obtain ⟨σ, n, t, hn⟩ := hreach
  obtain ⟨t', ht', hw⟩ := sim_necessity hS hStop hSp (hinit σ) hn hc'
  obtain ⟨bs, hbs, himp⟩ := href σ _ hw
  rcases himp with h | ⟨t₃, rfl, hp⟩
  · subst h
    exact goesWrong_nil_of_prefix hn hbs ht'
  · exact goesWrong_nil_of_prefix hn hbs (List.IsPrefix.trans hp ht')

/-- Whole-trace form of `goesWrong_nil_of_sim_necessity`. -/
theorem goesWrong_of_sim_necessity {K : ZContract} {L Rt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Cfg → Nat} {Stop Special : Cfg → Prop} {B : Nat}
    (hS : IsSim K L Rt R μ Stop B) (hStop : ∀ c, Stop c → step K L c = .ub ∨ Special c)
    (hSp : ∀ c d, Special c → R c d → GoesWrongFrom K Rt d [])
    (hinit : ∀ σ, R (L.init σ) (Rt.init σ)) (href : RefinesWT K L Rt) {c' : Cfg}
    (hreach : Reach K L c') (hc' : Special c') : ∃ u, GoesWrongFrom K L c' u := by
  obtain ⟨σ, n, t, hn⟩ := hreach
  obtain ⟨t', -, hw⟩ := sim_necessity hS hStop hSp (hinit σ) hn hc'
  obtain ⟨bs, hbs, himp⟩ := href σ _ hw
  rcases himp with h | ⟨t₃, rfl⟩
  · subst h
    obtain ⟨u, -, hu⟩ := goesWrong_suffix hn hbs
    exact ⟨u, hu⟩
  · obtain ⟨u, -, hu⟩ := goesWrong_suffix hn hbs
    exact ⟨u, hu⟩

/-! ### Local simulation steps -/

theorem step_cons_none {K : ZContract} {P : Prog} {l : Label} {a : Stmt} {r : List Stmt}
    {st : State} (h : execStmt K a st = none) : step K P ⟨l, a :: r, st⟩ = .ub := by
  simp [step, h]

theorem step_cons_some {K : ZContract} {P : Prog} {l : Label} {a : Stmt} {r : List Stmt}
    {st st' : State} {o : Option Int} (h : execStmt K a st = some (o, st')) :
    step K P ⟨l, a :: r, st⟩ = .next o ⟨l, r, st'⟩ := by
  simp [step, h]

theorem simStep_head {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} (l : Label) (a : Stmt) (r₁ r₂ : List Stmt)
    (st : State) (hgen : step K L ⟨l, a :: r₁, st⟩ = .ub → Stop ⟨l, a :: r₁, st⟩)
    (hnext : ∀ st', R ⟨l, r₁, st'⟩ ⟨l, r₂, st'⟩) :
    SimStep K L Rt R μ Stop ⟨l, a :: r₁, st⟩ ⟨l, a :: r₂, st⟩ := by
  cases he : execStmt K a st with
  | none => exact Or.inl (hgen (step_cons_none he))
  | some p =>
    obtain ⟨o, s'⟩ := p
    refine Or.inr (Or.inr ⟨o, ⟨l, r₁, s'⟩, step_cons_some he, 1, ⟨l, r₂, s'⟩, ?_, hnext s',
      by simp⟩)
    rw [run_succ_next 0 (step_cons_some he)]
    simp [run, Outcome.cons]

theorem simStep_target {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {c d : Cfg} (b : Label) (st : State)
    (hL : step K L c = .next none (L.entry b st)) (hRt : step K Rt d = .next none (Rt.entry b st))
    (hR : R (L.entry b st) (Rt.entry b st)) : SimStep K L Rt R μ Stop c d :=
  Or.inr (Or.inr ⟨none, _, hL, 1, _, by rw [run_succ_next 0 hRt]; rfl, hR, by simp⟩)

theorem simStep_term {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} (l : Label) (st : State)
    (hterm : (L.blk l).term = (Rt.blk l).term)
    (hgen : step K L ⟨l, [], st⟩ = .ub → Stop ⟨l, [], st⟩)
    (hentry : ∀ b, R (L.entry b st) (Rt.entry b st)) :
    SimStep K L Rt R μ Stop ⟨l, [], st⟩ ⟨l, [], st⟩ := by
  cases ht : (L.blk l).term with
  | goto b =>
    exact simStep_target b st (by simp [step, ht]) (by simp [step, ← hterm, ht]) (hentry b)
  | switch x arms ow =>
    exact simStep_target (selectTarget arms ow (st.locals x)) st (by simp [step, ht])
      (by simp [step, ← hterm, ht]) (hentry _)
  | unreachable => exact Or.inl (hgen (by simp [step, ht]))
  | halt =>
    exact Or.inr (Or.inl ⟨st, by simp [step, ht], 1,
      run_succ_halt 0 (by simp [step, ← hterm, ht])⟩)

theorem simStep_same {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} (l : Label) (r : List Stmt) (st : State)
    (hterm : (L.blk l).term = (Rt.blk l).term) (hgen : ∀ c, step K L c = .ub → Stop c)
    (hnext : ∀ a r' st', r = a :: r' → R ⟨l, r', st'⟩ ⟨l, r', st'⟩)
    (hentry : ∀ b st', R (L.entry b st') (Rt.entry b st')) :
    SimStep K L Rt R μ Stop ⟨l, r, st⟩ ⟨l, r, st⟩ := by
  cases r with
  | cons a r' => exact simStep_head l a r' r' st (hgen _) (fun st' => hnext a r' st' rfl)
  | nil => exact simStep_term l st hterm (hgen _) (fun b => hentry b st)

/-- Measure for one stutter step: `1` when the left configuration has more remaining
statements than the right one. -/
def stutterμ (c d : Cfg) : Nat := if d.rest.length < c.rest.length then 1 else 0

theorem stutterμ_le (c d : Cfg) : stutterμ c d ≤ 1 := by
  unfold stutterμ
  split <;> omega

/-- `L` executes a silent statement that does not change the state while `Rt` stays. -/
theorem simStep_stutter {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {Stop : Cfg → Prop} (l : Label) (a : Stmt) (r : List Stmt) (st : State) (d : Cfg)
    (ha : execStmt K a st = some (none, st) ∨ execStmt K a st = none)
    (hgen : step K L ⟨l, a :: r, st⟩ = .ub → Stop ⟨l, a :: r, st⟩)
    (hR : execStmt K a st = some (none, st) → R ⟨l, r, st⟩ d) (hd : d.rest = r) :
    SimStep K L Rt R stutterμ Stop ⟨l, a :: r, st⟩ d := by
  rcases ha with ha | ha
  · refine Or.inr (Or.inr ⟨none, ⟨l, r, st⟩, step_cons_some ha, 0, d, rfl, hR ha, fun _ => ?_⟩)
    simp [stutterμ, hd]
  · exact Or.inl (hgen (step_cons_none ha))

/-- `Rt` first takes a silent step. -/
theorem simStep_pre_silent {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {c d d₀ : Cfg}
    (h₀ : step K Rt d₀ = .next none d) (h : SimStep K L Rt R μ Stop c d) :
    SimStep K L Rt R μ Stop c d₀ := by
  rcases h with h | ⟨s, hs, k, hk⟩ | ⟨o, c', hs, k, d', hk, hR, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨s, hs, k + 1, by rw [run_succ_next k h₀, cons_none, hk]⟩)
  · exact Or.inr (Or.inr ⟨o, c', hs, k + 1, d', by rw [run_succ_next k h₀, cons_none, hk], hR,
      fun h => absurd h (Nat.succ_ne_zero k)⟩)

/-! ### Simulations for programs that differ in one block -/

/-- Configurations of two programs that agree outside block `l`: same label and state,
the same remaining statements outside block `l`, and remaining statements related by `ρ`
inside block `l`. -/
def BlockRel (l : Label) (ρ : List Stmt → List Stmt → State → Prop) (c d : Cfg) : Prop :=
  c.lbl = d.lbl ∧ c.st = d.st ∧ (c.lbl = l → ρ c.rest d.rest c.st) ∧
    (c.lbl ≠ l → c.rest = d.rest)

/-- A relation strengthened by reachability of both configurations. -/
def RelR (K : ZContract) (L Rt : Prog) (R : Cfg → Cfg → Prop) (c d : Cfg) : Prop :=
  R c d ∧ Reach K L c ∧ Reach K Rt d

theorem blockRel_entry {L Rt : Prog} {l : Label} {ρ : List Stmt → List Stmt → State → Prop}
    (hblk : ∀ l', l' ≠ l → L.blk l' = Rt.blk l')
    (hent : ∀ st, ρ (L.blk l).stmts (Rt.blk l).stmts st) (b : Label) (st : State) :
    BlockRel l ρ (L.entry b st) (Rt.entry b st) := by
  refine ⟨rfl, rfl, fun h => ?_, fun h => ?_⟩
  · simp only [Prog.entry] at h ⊢
    subst h
    exact hent st
  · simp only [Prog.entry] at h ⊢
    rw [hblk b h]

theorem blockRel_same {l : Label} {ρ : List Stmt → List Stmt → State → Prop} {lbl : Label}
    (h : lbl ≠ l) (r : List Stmt) (st : State) : BlockRel l ρ ⟨lbl, r, st⟩ ⟨lbl, r, st⟩ :=
  ⟨rfl, rfl, fun e => absurd e h, fun _ => rfl⟩

theorem blockRel_in {l : Label} {ρ : List Stmt → List Stmt → State → Prop}
    {r₁ r₂ : List Stmt} {st : State} (h : ρ r₁ r₂ st) : BlockRel l ρ ⟨l, r₁, st⟩ ⟨l, r₂, st⟩ :=
  ⟨rfl, rfl, fun _ => h, fun e => absurd rfl e⟩

theorem blockRel_inv {l : Label} {ρ : List Stmt → List Stmt → State → Prop}
    {r₁ : List Stmt} {st : State} {d : Cfg} (h : BlockRel l ρ ⟨l, r₁, st⟩ d) :
    ∃ r, d = ⟨l, r, st⟩ ∧ ρ r₁ r st := by
  rcases d with ⟨l', r', st'⟩
  obtain ⟨h1, h2, h3, -⟩ := h
  dsimp only at h1 h2
  subst h1 h2
  exact ⟨r', rfl, h3 rfl⟩

theorem blockRel_inv_ne {l : Label} {ρ : List Stmt → List Stmt → State → Prop}
    {c d : Cfg} (h : BlockRel l ρ c d) (hl : c.lbl ≠ l) : d = c := by
  obtain ⟨h1, h2, -, h4⟩ := h
  have h4' := h4 hl
  rcases c with ⟨l₁, r₁, s₁⟩
  rcases d with ⟨l₂, r₂, s₂⟩
  dsimp only at h1 h2 h4'
  subst h1 h2 h4'
  rfl

theorem simStep_reach {K : ZContract} {L Rt : Prog} {R : Cfg → Cfg → Prop}
    {μ : Cfg → Cfg → Nat} {Stop : Cfg → Prop} {c d : Cfg} (h : SimStep K L Rt R μ Stop c d)
    (hc : Reach K L c) (hd : Reach K Rt d) : SimStep K L Rt (RelR K L Rt R) μ Stop c d := by
  rcases h with h | h | ⟨o, c', hs, k, d', hk, hR, hμ⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨o, c', hs, k, d', hk, ⟨hR, reach_step hc hs, reach_run hd hk⟩, hμ⟩)

/-- A simulation between programs that agree outside block `l`, from the obligations inside
block `l` (where both configurations are reachable). -/
theorem blockSim {K : ZContract} {L Rt : Prog} {l : Label}
    {ρ : List Stmt → List Stmt → State → Prop} {μ : Cfg → Cfg → Nat} {B : Nat}
    {Stop : Cfg → Prop}
    (hblk : ∀ l', l' ≠ l → L.blk l' = Rt.blk l')
    (hent : ∀ st, ρ (L.blk l).stmts (Rt.blk l).stmts st)
    (hμ : ∀ c d, μ c d ≤ B)
    (hgen : ∀ c, step K L c = .ub → Stop c)
    (hloc : ∀ r₁ r₂ st, ρ r₁ r₂ st → Reach K L ⟨l, r₁, st⟩ → Reach K Rt ⟨l, r₂, st⟩ →
      SimStep K L Rt (BlockRel l ρ) μ Stop ⟨l, r₁, st⟩ ⟨l, r₂, st⟩) :
    IsSim K L Rt (RelR K L Rt (BlockRel l ρ)) μ Stop B := by
  refine ⟨hμ, fun c d ⟨hR, hc, hd⟩ => simStep_reach ?_ hc hd⟩
  rcases c with ⟨lbl, r₁, st⟩
  rcases d with ⟨lbl', r₂, st'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hR
  simp only at h1 h2 h3 h4
  subst h1 h2
  by_cases hl : lbl = l
  · subst hl
    exact hloc r₁ r₂ st (h3 rfl) hc hd
  · have := h4 hl
    subst this
    exact simStep_same lbl r₁ st (by rw [hblk lbl hl]) hgen
      (fun _ r' st' _ => blockRel_same hl r' st') (blockRel_entry hblk hent)

theorem blockSim_init {K : ZContract} {L Rt : Prog} {l : Label}
    {ρ : List Stmt → List Stmt → State → Prop}
    (hblk : ∀ l', l' ≠ l → L.blk l' = Rt.blk l')
    (hent : ∀ st, ρ (L.blk l).stmts (Rt.blk l).stmts st) (σ : State) :
    RelR K L Rt (BlockRel l ρ) (L.init σ) (Rt.init σ) :=
  ⟨blockRel_entry hblk hent 0 σ, reach_init K L σ, reach_init K Rt σ⟩

/-! ### Blocks of edited programs -/

theorem blk_set_self {P : Prog} {l : Label} (h : l < P.length) (b : Block) :
    Prog.blk (P.set l b) l = b := by
  simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem blk_set_ne {P : Prog} {l l' : Label} (h : l' ≠ l) (b : Block) :
    Prog.blk (P.set l b) l' = P.blk l' := by
  simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem blk_of_length_le {P : Prog} {l : Label} (h : P.length ≤ l) : P.blk l = Block.unreach := by
  simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem length_of_blk_ne_unreach {P : Prog} {l : Label} (h : P.blk l ≠ Block.unreach) :
    l < P.length :=
  Nat.lt_of_not_le fun hle => h (blk_of_length_le hle)

theorem execStmt_zeroSize (K : ZContract) {s : Stmt} (hz : IsZeroSizeAccess s) (st : State) :
    execStmt K s st = if s.zeroPre K st = true then some (none, st) else none := by
  rw [← pre_eq_zeroPre_of_isZeroSize K st s hz]
  cases s <;> first | rfl | (simp [IsZeroSizeAccess] at hz)

theorem execStmt_zeroSize_cases (K : ZContract) {s : Stmt} (hz : IsZeroSizeAccess s)
    (st : State) : execStmt K s st = some (none, st) ∨ execStmt K s st = none := by
  rw [execStmt_zeroSize K hz]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem execStmt_zeroSize_none_iff (K : ZContract) {s : Stmt} (hz : IsZeroSizeAccess s)
    (st : State) : execStmt K s st = none ↔ s.zeroPre K st = false := by
  rw [execStmt_zeroSize K hz]
  cases s.zeroPre K st <;> simp

theorem execStmt_assume (K : ZContract) (c : Cond) (st : State) :
    execStmt K (.assume c) st = if c.eval st = true then some (none, st) else none := rfl

theorem execStmt_assume_cases (K : ZContract) (c : Cond) (st : State) :
    execStmt K (.assume c) st = some (none, st) ∨ execStmt K (.assume c) st = none := by
  rw [execStmt_assume]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end Toy.ZstAssume
