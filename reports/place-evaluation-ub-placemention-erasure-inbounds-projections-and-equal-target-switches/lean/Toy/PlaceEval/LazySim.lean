import Toy.PlaceEval.Simulation

/-!
# Simulations with a lazily chosen source oracle

Under fresh addresses the `k`-th allocation of a run uses the oracle value `ω k`, and the
run from a configuration `c` consults the oracle only at indices `≥` the number of
allocations already made in `c`. This file shows that a simulation in which every target
step is matched under *some* source oracle (chosen per step) yields a refinement: the
per-step oracles are combined into a single oracle for the whole source run.
-/

namespace Toy.PlaceEval

theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- The number of allocations made so far in a configuration's state. -/
def Cfg.nAlloc (c : Cfg) : Nat := c.st.mem.allocs.length

/-- `ω` and `ω'` agree on the indices `lo ≤ k < hi`. -/
def OAgree (ω ω' : Nat → Nat) (lo hi : Nat) : Prop := ∀ k, lo ≤ k → k < hi → ω k = ω' k

/-- Use `ω₁` below `n` and `ω₂` from `n` on. -/
def ocomb (n : Nat) (ω₁ ω₂ : Nat → Nat) : Nat → Nat := fun k => if k < n then ω₁ k else ω₂ k

theorem deallocate_allocs_length (st : State) (x : Local) :
    (deallocate st x).mem.allocs.length = st.mem.allocs.length := by
  unfold deallocate
  split <;> simp

theorem allocate_some {mode : AllocMode} {st st' : State} {x : Local} {L : Layout}
    (h : allocate mode st x L = some st') :
    ∃ a, st' = { mem := { allocs := st.mem.allocs ++ [⟨a, L.size, true⟩],
                          cells := placeCells a (List.replicate L.size .uninit) ++ st.mem.cells },
                 frame := st.frame.set x (some st.mem.allocs.length) } := by
  cases mode with
  | fresh ω =>
    unfold allocate at h
    simp only at h
    split at h
    · exact ⟨_, (Option.some.inj h).symm⟩
    · cases h
  | slots s =>
    unfold allocate at h
    simp only [ite_true] at h
    exact ⟨_, (Option.some.inj h).symm⟩

theorem allocate_allocs_length {mode : AllocMode} {st st' : State} {x : Local} {L : Layout}
    (h : allocate mode st x L = some st') : st'.mem.allocs.length = st.mem.allocs.length + 1 := by
  obtain ⟨a, rfl⟩ := allocate_some h
  simp

theorem allocate_mode_congr {Ss : Sem} {ω ω' : Nat → Nat} (st : State) (x : Local) (L : Layout)
    (h : ω st.mem.allocs.length = ω' st.mem.allocs.length) :
    allocate (Ss.mode ω) st x L = allocate (Ss.mode ω') st x L := by
  cases Ss with
  | fresh => simp only [Sem.mode, allocate, h]; congr
  | slots s => rfl

theorem execStmt_mode_congr {Ss : Sem} {ω ω' : Nat → Nat} (P : Prog) (st : State) (s : Stmt)
    (h : ω st.mem.allocs.length = ω' st.mem.allocs.length) :
    execStmt (Ss.mode ω) P st s = execStmt (Ss.mode ω') P st s := by
  cases s with
  | storageLive y =>
    have h' : ω (deallocate st y).mem.allocs.length = ω' (deallocate st y).mem.allocs.length := by
      rw [deallocate_allocs_length]; exact h
    simp only [execStmt]
    rw [allocate_mode_congr (Ss := Ss) (deallocate st y) y (P.layout y) h']
  | _ => rfl

theorem execStmt_allocs_length {mode : AllocMode} {P : Prog} {st st' : State} {s : Stmt}
    {ev : Option Nat} (h : execStmt mode P st s = .ok ev st') :
    st'.mem.allocs.length = st.mem.allocs.length ∨
      st'.mem.allocs.length = st.mem.allocs.length + 1 := by
  cases s with
  | placeMention p =>
    simp only [execStmt] at h
    split at h
    · cases h; exact Or.inl rfl
    · cases h
  | assign dst τ rv =>
    simp only [execStmt] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          left
          rename_i m hm
          simp only [Mem.store] at hm
          split at hm
          · cases hm; rfl
          · cases hm
        · cases h
  | emit rv =>
    simp only [execStmt] at h
    split at h
    · cases h; exact Or.inl rfl
    · cases h
  | storageLive y =>
    simp only [execStmt] at h
    split at h
    · rename_i st'' hst
      cases h
      right
      rw [allocate_allocs_length hst, deallocate_allocs_length]
    · cases h
  | storageDead y =>
    simp only [execStmt] at h
    cases h
    exact Or.inl (deallocate_allocs_length _ _)

/-- A successful statement that makes no allocation does not consult the oracle. -/
theorem execStmt_mode_indep {mode mode' : AllocMode} {P : Prog} {st st' : State} {s : Stmt}
    {ev : Option Nat} (h : execStmt mode P st s = .ok ev st')
    (hl : st'.mem.allocs.length = st.mem.allocs.length) : execStmt mode' P st s = .ok ev st' := by
  cases s with
  | storageLive y =>
    simp only [execStmt] at h
    split at h
    · rename_i st'' hst
      cases h
      rw [allocate_allocs_length hst, deallocate_allocs_length] at hl
      omega
    · cases h
  | _ => exact h

theorem step_mode_congr {Ss : Sem} {ω ω' : Nat → Nat} (P : Prog) (c : Cfg)
    (h : ω c.nAlloc = ω' c.nAlloc) : step (Ss.mode ω) P c = step (Ss.mode ω') P c := by
  unfold step
  split
  · rw [execStmt_mode_congr P c.st _ h]
  · rfl

theorem step_nAlloc {mode : AllocMode} {P : Prog} {c c' : Cfg} {ev : Option Nat}
    (h : step mode P c = .next ev c') : c'.nAlloc = c.nAlloc ∨ c'.nAlloc = c.nAlloc + 1 := by
  unfold step at h
  split at h
  · split at h
    · rename_i _ _ _ ev' st' he
      cases h
      exact execStmt_allocs_length he
    · cases h
    · cases h
  · split at h
    · cases h; exact Or.inl rfl
    · split at h
      · cases h; exact Or.inl rfl
      · cases h
    · cases h
    · cases h

theorem step_mode_indep {mode mode' : AllocMode} {P : Prog} {c c' : Cfg} {ev : Option Nat}
    (h : step mode P c = .next ev c') (hl : c'.nAlloc = c.nAlloc) :
    step mode' P c = .next ev c' := by
  unfold step at h ⊢
  split at h
  · split at h
    · rename_i ev' st' he
      cases h
      rw [execStmt_mode_indep he hl]
    · cases h
    · cases h
  · exact h

/-- A successful step depends on the oracle only at the indices of the allocations it makes. -/
theorem step_local {Ss : Sem} {ω ω' : Nat → Nat} {P : Prog} {c c' : Cfg} {ev : Option Nat}
    (h : step (Ss.mode ω) P c = .next ev c') (ha : OAgree ω ω' c.nAlloc c'.nAlloc) :
    step (Ss.mode ω') P c = .next ev c' := by
  rcases step_nAlloc h with he | he
  · exact step_mode_indep h he
  · rw [← step_mode_congr P c (ha _ (Nat.le_refl _) (by omega))]
    exact h

theorem run_nAlloc_mono {mode : AllocMode} {P : Prog} :
    ∀ (n : Nat) (c c' : Cfg) (t : List Nat), run mode P n c = .running c' t → c.nAlloc ≤ c'.nAlloc
  | 0, c, c', t, h => by
    simp only [run, Outcome.running.injEq] at h
    rw [h.1]; exact Nat.le_refl _
  | n + 1, c, c', t, h => by
    cases hs : step mode P c with
    | next ev c1 =>
      rw [run_succ_next _ hs] at h
      cases hr : run mode P n c1 with
      | running c2 t2 =>
        rw [hr] at h
        simp only [Outcome.cons, Outcome.running.injEq] at h
        rw [← h.1]
        have := run_nAlloc_mono n c1 c2 t2 hr
        rcases step_nAlloc hs with e | e <;> omega
      | done _ _ => rw [hr] at h; simp [Outcome.cons] at h
      | ub _ => rw [hr] at h; simp [Outcome.cons] at h
      | blocked => rw [hr] at h; simp [Outcome.cons] at h
    | halt s => rw [run_succ_halt _ hs] at h; cases h
    | ub => rw [run_succ_ub _ hs] at h; cases h
    | block => rw [run_succ_block _ hs] at h; cases h

/-- A run depends on the oracle only at indices from the current allocation count on. -/
theorem run_local_ge {Ss : Sem} {ω ω' : Nat → Nat} {P : Prog} :
    ∀ (n : Nat) (c : Cfg), (∀ k, c.nAlloc ≤ k → ω k = ω' k) →
      run (Ss.mode ω) P n c = run (Ss.mode ω') P n c
  | 0, c, _ => rfl
  | n + 1, c, h => by
    have hst := step_mode_congr (Ss := Ss) (ω := ω) (ω' := ω') P c (h _ (Nat.le_refl _))
    cases hs : step (Ss.mode ω) P c with
    | next ev c1 =>
      rw [run_succ_next _ hs, run_succ_next _ (hst.symm.trans hs),
        run_local_ge n c1 fun k hk => h k (by rcases step_nAlloc hs with e | e <;> omega)]
    | halt s => rw [run_succ_halt _ hs, run_succ_halt _ (hst.symm.trans hs)]
    | ub => rw [run_succ_ub _ hs, run_succ_ub _ (hst.symm.trans hs)]
    | block => rw [run_succ_block _ hs, run_succ_block _ (hst.symm.trans hs)]

/-- A run that is still running depends on the oracle only at the indices of the allocations
it makes. -/
theorem run_local_running {Ss : Sem} {ω ω' : Nat → Nat} {P : Prog} :
    ∀ (n : Nat) (c c' : Cfg) (t : List Nat), run (Ss.mode ω) P n c = .running c' t →
      OAgree ω ω' c.nAlloc c'.nAlloc → run (Ss.mode ω') P n c = .running c' t
  | 0, c, c', t, h, _ => h
  | n + 1, c, c', t, h, ha => by
    cases hs : step (Ss.mode ω) P c with
    | next ev c1 =>
      rw [run_succ_next _ hs] at h
      cases hr : run (Ss.mode ω) P n c1 with
      | running c2 t2 =>
        rw [hr] at h
        simp only [Outcome.cons, Outcome.running.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have m1 := run_nAlloc_mono n c1 c2 t2 hr
        have m0 := step_nAlloc hs
        have hs' : step (Ss.mode ω') P c = .next ev c1 :=
          step_local hs fun k h1 h2 => ha k h1 (by rcases m0 with e | e <;> omega)
        rw [run_succ_next _ hs',
          run_local_running n c1 c2 t2 hr fun k h1 h2 =>
            ha k (by rcases m0 with e | e <;> omega) h2]
        rfl
      | done _ _ => rw [hr] at h; simp [Outcome.cons] at h
      | ub _ => rw [hr] at h; simp [Outcome.cons] at h
      | blocked => rw [hr] at h; simp [Outcome.cons] at h
    | halt s => rw [run_succ_halt _ hs] at h; cases h
    | ub => rw [run_succ_ub _ hs] at h; cases h
    | block => rw [run_succ_block _ hs] at h; cases h

theorem hasBehFrom_local_ge {Ss : Sem} {ω ω' : Nat → Nat} {P : Prog} {c : Cfg}
    (h : ∀ k, c.nAlloc ≤ k → ω k = ω' k) (b : Beh) :
    HasBehFrom (Ss.mode ω) P c b ↔ HasBehFrom (Ss.mode ω') P c b := by
  have e : ∀ n, run (Ss.mode ω) P n c = run (Ss.mode ω') P n c := fun n => run_local_ge n c h
  cases b <;> simp only [HasBehFrom, e]

/-- Running `k` steps under `ω₁` to `cs'` and then under `ω₂`. -/
theorem run_ocomb {Ss : Sem} {ω₁ ω₂ : Nat → Nat} {P : Prog} {cs cs' : Cfg} {k : Nat}
    {e : List Nat} (h : run (Ss.mode ω₁) P k cs = .running cs' e) (m : Nat) :
    run (Ss.mode (ocomb cs'.nAlloc ω₁ ω₂)) P (k + m) cs = (run (Ss.mode ω₂) P m cs').app e := by
  have h1 : run (Ss.mode (ocomb cs'.nAlloc ω₁ ω₂)) P k cs = .running cs' e :=
    run_local_running k cs cs' e h fun j _ hj => by simp [ocomb, hj]
  rw [run_add_running k m cs cs' e h1,
    run_local_ge (ω := ocomb cs'.nAlloc ω₁ ω₂) (ω' := ω₂) m cs' fun j hj => by
      simp [ocomb, Nat.not_lt.2 hj]]

theorem run_ocomb_running {Ss : Sem} {ω₁ ω₂ : Nat → Nat} {P : Prog} {cs cs' : Cfg} {k : Nat}
    {e : List Nat} (h : run (Ss.mode ω₁) P k cs = .running cs' e) :
    run (Ss.mode (ocomb cs'.nAlloc ω₁ ω₂)) P k cs = .running cs' e :=
  run_local_running k cs cs' e h fun j _ hj => by simp [ocomb, hj]

/-! ## Lazy simulations -/

/-- Step matching in which the source oracle may be chosen for this step. -/
def LStepSim (Ss : Sem) (Ps : Prog) (mt : AllocMode) (Pt : Prog) (R : Cfg → Cfg → Prop)
    (μ : Cfg → Nat) (cs ct : Cfg) : Prop :=
  (∃ ω, SrcUB (Ss.mode ω) Ps cs) ∨
  ((∀ ev ct', step mt Pt ct = .next ev ct' →
      (∃ ω k cs', run (Ss.mode ω) Ps (k + 1) cs = .running cs' ev.toList ∧ R cs' ct') ∨
      (ev = none ∧ μ ct' < μ ct ∧ R cs ct')) ∧
   (∀ st, step mt Pt ct = .halt st → ∃ ω k st', run (Ss.mode ω) Ps k cs = .done [] st') ∧
   step mt Pt ct ≠ .ub)

/-- A lazy simulation with measure `μ` bounded by `B`. -/
structure LIsSim (Ss : Sem) (Ps : Prog) (mt : AllocMode) (Pt : Prog) (R : Cfg → Cfg → Prop)
    (μ : Cfg → Nat) (B : Nat) : Prop where
  bound : ∀ cs ct, R cs ct → μ ct ≤ B
  step : ∀ cs ct, R cs ct → LStepSim Ss Ps mt Pt R μ cs ct

/-- What a target outcome after `n` steps is matched by, under some source oracle. -/
def LMatched (Ss : Sem) (Ps : Prog) (R : Cfg → Cfg → Prop) (μ : Cfg → Nat) (B n : Nat)
    (cs ct : Cfg) : Outcome → Prop
  | .done t _ => ∃ ω, (∃ m st', run (Ss.mode ω) Ps m cs = .done t st') ∨ SrcUBPre (Ss.mode ω) Ps cs t
  | .ub t => ∃ ω, SrcUBPre (Ss.mode ω) Ps cs t
  | .running ct' t => ∃ ω, (∃ m cs', run (Ss.mode ω) Ps m cs = .running cs' t ∧ R cs' ct' ∧
        n + μ ct' ≤ (B + 1) * m + μ ct) ∨ SrcUBPre (Ss.mode ω) Ps cs t
  | .blocked => True

theorem srcUBPre_ocomb {Ss : Sem} {ω₁ ω₂ : Nat → Nat} {Ps : Prog} {cs cs' : Cfg} {a : Nat}
    {e t : List Nat} (ha : run (Ss.mode ω₁) Ps a cs = .running cs' e)
    (h : SrcUBPre (Ss.mode ω₂) Ps cs' t) :
    SrcUBPre (Ss.mode (ocomb cs'.nAlloc ω₁ ω₂)) Ps cs (e ++ t) := by
  obtain ⟨m, u, hm, hu⟩ := h
  refine ⟨a + m, e ++ u, ?_, List.prefix_append_right_inj e |>.2 hu⟩
  rw [run_ocomb ha m, hm]
  rfl

theorem LIsSim.lmatched {Ss : Sem} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {B : Nat} (h : LIsSim Ss Ps mt Pt R μ B) :
    ∀ (n : Nat) (cs ct : Cfg), R cs ct → LMatched Ss Ps R μ B n cs ct (run mt Pt n ct)
  | 0, cs, ct, hR => ⟨fun _ => 0, Or.inl ⟨0, cs, rfl, hR, by simp⟩⟩
  | n + 1, cs, ct, hR => by
    rcases h.step cs ct hR with ⟨ω, hub⟩ | ⟨hnext, hhalt, hnub⟩
    · cases run mt Pt (n + 1) ct with
      | done t s => exact ⟨ω, Or.inr (srcUBPre_of_srcUB hub t)⟩
      | ub t => exact ⟨ω, srcUBPre_of_srcUB hub t⟩
      | running c t => exact ⟨ω, Or.inr (srcUBPre_of_srcUB hub t)⟩
      | blocked => trivial
    cases hs : Toy.PlaceEval.step mt Pt ct with
    | next ev ct' =>
      rw [run_succ_next _ hs, Outcome.cons_eq_app]
      rcases hnext ev ct' hs with ⟨ω₁, k, cs', hk, hR'⟩ | ⟨rfl, hμ, hR'⟩
      · have ih := h.lmatched n cs' ct' hR'
        have hb := h.bound cs' ct' hR'
        cases hr : run mt Pt n ct' with
        | done t st =>
          rw [hr] at ih
          obtain ⟨ω₂, ⟨m, st', hm⟩ | hpre⟩ := ih
          · refine ⟨ocomb cs'.nAlloc ω₁ ω₂, Or.inl ⟨k + 1 + m, st', ?_⟩⟩
            rw [run_ocomb hk m, hm]; rfl
          · exact ⟨_, Or.inr (srcUBPre_ocomb hk hpre)⟩
        | ub t =>
          rw [hr] at ih
          obtain ⟨ω₂, hpre⟩ := ih
          exact ⟨_, srcUBPre_ocomb hk hpre⟩
        | running ct'' t =>
          rw [hr] at ih
          obtain ⟨ω₂, ⟨m, cs'', hm, hR'', hle⟩ | hpre⟩ := ih
          · refine ⟨ocomb cs'.nAlloc ω₁ ω₂, Or.inl ⟨k + 1 + m, cs'', ?_, hR'', ?_⟩⟩
            · rw [run_ocomb hk m, hm]; rfl
            · have := mul_succ_add_le B k m
              omega
          · exact ⟨_, Or.inr (srcUBPre_ocomb hk hpre)⟩
        | blocked => trivial
      · have ih := h.lmatched n cs ct' hR'
        simp only [Option.toList, Outcome.app_nil]
        cases hr : run mt Pt n ct' with
        | done t st => rw [hr] at ih; exact ih
        | ub t => rw [hr] at ih; exact ih
        | running ct'' t =>
          rw [hr] at ih
          obtain ⟨ω₂, ⟨m, cs'', hm, hR'', hle⟩ | hpre⟩ := ih
          · exact ⟨ω₂, Or.inl ⟨m, cs'', hm, hR'', by omega⟩⟩
          · exact ⟨ω₂, Or.inr hpre⟩
        | blocked => trivial
    | halt st =>
      rw [run_succ_halt _ hs]
      obtain ⟨ω, k, st', hk⟩ := hhalt st hs
      exact ⟨ω, Or.inl ⟨k, st', hk⟩⟩
    | ub => exact absurd hs hnub
    | block => rw [run_succ_block _ hs]; trivial

/-! ## The paired run for infinite target runs -/

section Seq

variable (Ss : Sem) (Ps : Prog) (mt : AllocMode) (Pt : Prog) (R : Cfg → Cfg → Prop)

/-- Matching data for one target step: a source oracle, a step count and a configuration. -/
def LMatch (cs : Cfg) (ev : Option Nat) (ct' : Cfg) (p : (Nat → Nat) × Nat × Cfg) : Prop :=
  run (Ss.mode p.1) Ps (p.2.1 + 1) cs = .running p.2.2 ev.toList ∧ R p.2.2 ct'

open Classical in
/-- One stage of the paired run: the next source and target configurations and the oracle
used by the source for this stage. -/
noncomputable def lnext (cs ct : Cfg) : Cfg × Cfg × (Nat → Nat) :=
  match step mt Pt ct with
  | .next ev ct' =>
    if h : ∃ p, LMatch Ss Ps R cs ev ct' p then
      ((Classical.choose h).2.2, ct', (Classical.choose h).1)
    else (cs, ct', fun _ => 0)
  | _ => (cs, ct, fun _ => 0)

/-- The paired run. -/
noncomputable def lseq (cs0 ct0 : Cfg) : Nat → Cfg × Cfg
  | 0 => (cs0, ct0)
  | i + 1 => ((lnext Ss Ps mt Pt R (lseq cs0 ct0 i).1 (lseq cs0 ct0 i).2).1,
              (lnext Ss Ps mt Pt R (lseq cs0 ct0 i).1 (lseq cs0 ct0 i).2).2.1)

/-- The oracle used at stage `i`. -/
noncomputable def lorc (cs0 ct0 : Cfg) (i : Nat) : Nat → Nat :=
  (lnext Ss Ps mt Pt R (lseq Ss Ps mt Pt R cs0 ct0 i).1 (lseq Ss Ps mt Pt R cs0 ct0 i).2).2.2

theorem lnext_mono (cs ct : Cfg) : cs.nAlloc ≤ (lnext Ss Ps mt Pt R cs ct).1.nAlloc := by
  unfold lnext
  split
  · split
    · rename_i h
      exact run_nAlloc_mono _ _ _ _ (Classical.choose_spec h).1
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem lseq_mono (cs0 ct0 : Cfg) {i j : Nat} (hij : i ≤ j) :
    (lseq Ss Ps mt Pt R cs0 ct0 i).1.nAlloc ≤ (lseq Ss Ps mt Pt R cs0 ct0 j).1.nAlloc := by
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (lnext_mono Ss Ps mt Pt R _ _)

open Classical in
/-- The combined oracle: at index `k` it is the oracle of the stage whose allocations include
the `k`-th one. -/
noncomputable def lomega (cs0 ct0 : Cfg) (k : Nat) : Nat :=
  if h : ∃ i, (lseq Ss Ps mt Pt R cs0 ct0 i).1.nAlloc ≤ k ∧
      k < (lseq Ss Ps mt Pt R cs0 ct0 (i + 1)).1.nAlloc then
    lorc Ss Ps mt Pt R cs0 ct0 (Classical.choose h) k
  else 0

theorem lomega_agree (cs0 ct0 : Cfg) (i : Nat) :
    OAgree (lorc Ss Ps mt Pt R cs0 ct0 i) (lomega Ss Ps mt Pt R cs0 ct0)
      (lseq Ss Ps mt Pt R cs0 ct0 i).1.nAlloc (lseq Ss Ps mt Pt R cs0 ct0 (i + 1)).1.nAlloc := by
  intro k h1 h2
  have hex : ∃ i, (lseq Ss Ps mt Pt R cs0 ct0 i).1.nAlloc ≤ k ∧
      k < (lseq Ss Ps mt Pt R cs0 ct0 (i + 1)).1.nAlloc := ⟨i, h1, h2⟩
  unfold lomega
  split
  case isFalse hn => exact absurd hex hn
  rename_i hex'
  have hs := Classical.choose_spec hex'
  generalize Classical.choose hex' = j at hs ⊢
  have e : j = i := by
    rcases Nat.lt_trichotomy j i with hl | he | hl
    · have := lseq_mono Ss Ps mt Pt R cs0 ct0 (show j + 1 ≤ i by omega); omega
    · exact he
    · have := lseq_mono Ss Ps mt Pt R cs0 ct0 (show i + 1 ≤ j by omega); omega
  rw [e]

end Seq

/-- Lazy simulations give refinement of behaviours from related configurations. -/
theorem LIsSim.improves {Ss : Sem} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {B : Nat} (h : LIsSim Ss Ps mt Pt R μ B)
    {cs ct : Cfg} (hR : R cs ct) (bt : Beh) (hbt : HasBehFrom mt Pt ct bt) :
    ∃ ω bs, HasBehFrom (Ss.mode ω) Ps cs bs ∧ ImprovesPP bt bs := by
  cases bt with
  | term t =>
    obtain ⟨n, s, hn⟩ := hbt
    have hm := h.lmatched n cs ct hR
    rw [hn] at hm
    obtain ⟨ω, ⟨m, st', hm⟩ | ⟨m, u, hm, hu⟩⟩ := hm
    · exact ⟨ω, .term t, ⟨m, st', hm⟩, improvesPP_refl _⟩
    · exact ⟨ω, .wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, hu⟩⟩
  | wrong t =>
    obtain ⟨n, hn⟩ := hbt
    have hm := h.lmatched n cs ct hR
    rw [hn] at hm
    obtain ⟨ω, m, u, hm, hu⟩ := hm
    exact ⟨ω, .wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, hu⟩⟩
  | div t =>
    by_cases hub : ∃ n ω, SrcUBPre (Ss.mode ω) Ps cs (run mt Pt n ct).trace
    · obtain ⟨n, ω, m, u, hm, hu⟩ := hub
      obtain ⟨hrun, N, hN⟩ := hbt
      refine ⟨ω, .wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, ?_⟩⟩
      show u <+: t
      obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun n)
      obtain ⟨c2, t2, h2⟩ := isRunning_iff.1 (hrun (max n N))
      have e2 := hN (max n N) (Nat.le_max_right _ _)
      rw [h2] at e2
      rw [h1] at hu
      simp only [Outcome.trace] at hu e2
      subst e2
      exact hu.trans (run_running_prefix h1 h2 (Nat.le_max_left _ _))
    · exact lsim_inf h hR hbt.1 hub _ hbt
  | react f =>
    by_cases hub : ∃ n ω, SrcUBPre (Ss.mode ω) Ps cs (run mt Pt n ct).trace
    · obtain ⟨n, ω, m, u, hm, hu⟩ := hub
      obtain ⟨hrun, hpre⟩ := hbt
      refine ⟨ω, .wrong u, ⟨m, hm⟩, Or.inr ⟨u, rfl, ?_⟩⟩
      show u = prefixOf f u.length
      rw [react_trace hrun hpre n] at hu
      exact eq_prefixOf_of_prefix hu
    · exact lsim_inf h hR hbt.1 hub _ hbt
where
  /-- For a target run that never stops and a source that cannot go wrong after any prefix,
  the paired run gives a simulation under one oracle. -/
  lsim_inf {Ss : Sem} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
      {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {B : Nat} (h : LIsSim Ss Ps mt Pt R μ B)
      {cs ct : Cfg} (hR : R cs ct) (hrun : ∀ n, (run mt Pt n ct).isRunning = true)
      (hub : ¬ ∃ n ω, SrcUBPre (Ss.mode ω) Ps cs (run mt Pt n ct).trace) (bt : Beh)
      (hbt : HasBehFrom mt Pt ct bt) :
      ∃ ω bs, HasBehFrom (Ss.mode ω) Ps cs bs ∧ ImprovesPP bt bs := by
    -- Invariant of the paired run.
    have inv : ∀ i, R (lseq Ss Ps mt Pt R cs ct i).1 (lseq Ss Ps mt Pt R cs ct i).2 ∧
        ∃ t ω m, run mt Pt i ct = .running (lseq Ss Ps mt Pt R cs ct i).2 t ∧
          run (Ss.mode ω) Ps m cs = .running (lseq Ss Ps mt Pt R cs ct i).1 t := by
      intro i
      induction i with
      | zero => exact ⟨hR, [], fun _ => 0, 0, rfl, rfl⟩
      | succ i ih =>
        obtain ⟨hRi, t, ω, m, hti, hsi⟩ := ih
        generalize hq : lseq Ss Ps mt Pt R cs ct i = q at hRi hti hsi
        obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun (i + 1))
        have hst : ∃ ev ct', Toy.PlaceEval.step mt Pt q.2 = .next ev ct' := by
          cases hs : Toy.PlaceEval.step mt Pt q.2 with
          | next ev ct' => exact ⟨ev, ct', rfl⟩
          | halt s =>
            rw [run_add_running i 1 ct q.2 t hti, run_succ_halt 0 hs] at h1; cases h1
          | ub => rw [run_add_running i 1 ct q.2 t hti, run_succ_ub 0 hs] at h1; cases h1
          | block => rw [run_add_running i 1 ct q.2 t hti, run_succ_block 0 hs] at h1; cases h1
        obtain ⟨ev, ct', hs⟩ := hst
        have hti' : run mt Pt (i + 1) ct = .running ct' (t ++ ev.toList) :=
          run_succ_of_running hti hs
        have hseq : lseq Ss Ps mt Pt R cs ct (i + 1) =
            ((lnext Ss Ps mt Pt R q.1 q.2).1, (lnext Ss Ps mt Pt R q.1 q.2).2.1) := by
          simp only [lseq, hq]
        rcases h.step q.1 q.2 hRi with ⟨ω', hub'⟩ | ⟨hnext, _, _⟩
        · exact absurd ⟨i, ocomb q.1.nAlloc ω ω', by
            rw [hti]
            have := srcUBPre_ocomb (ω₂ := ω') hsi (srcUBPre_of_srcUB hub' [])
            simpa [Outcome.trace] using this⟩ hub
        rw [hseq]
        simp only [lnext, hs]
        split
        · rename_i hex
          have hc := Classical.choose_spec hex
          refine ⟨hc.2, t ++ ev.toList, ocomb q.1.nAlloc ω (Classical.choose hex).1,
            m + ((Classical.choose hex).2.1 + 1), hti', ?_⟩
          rw [run_add_running m _ cs q.1 t (run_ocomb_running hsi)]
          rw [run_local_ge (ω := ocomb q.1.nAlloc ω (Classical.choose hex).1)
            (ω' := (Classical.choose hex).1) _ q.1 fun j hj => by simp [ocomb, Nat.not_lt.2 hj], hc.1]
          rfl
        · rename_i hex
          rcases hnext ev ct' hs with ⟨ω'', k, cs', hk, hR'⟩ | ⟨rfl, _, hR'⟩
          · exact absurd ⟨(ω'', k, cs'), hk, hR'⟩ hex
          · exact ⟨hR', t, ω, m, by simpa using hti', hsi⟩
    -- The paired run is a simulation under the combined oracle.
    let Ω := lomega Ss Ps mt Pt R cs ct
    let R' : Cfg → Cfg → Prop := fun cs' ct' => ∃ i, lseq Ss Ps mt Pt R cs ct i = (cs', ct')
    have hsim : IsSim (Ss.mode Ω) Ps mt Pt R' μ B := by
      refine ⟨fun cs' ct' ⟨i, hi⟩ => ?_, fun cs' ct' ⟨i, hi⟩ => ?_⟩
      · have := (inv i).1
        rw [hi] at this
        exact h.bound _ _ this
      · obtain ⟨hRi, t, ω, m, hti, hsi⟩ := inv i
        rw [hi] at hRi hti hsi
        obtain ⟨c1, t1, h1⟩ := isRunning_iff.1 (hrun (i + 1))
        have hst : ∃ ev ct'', Toy.PlaceEval.step mt Pt ct' = .next ev ct'' := by
          cases hs : Toy.PlaceEval.step mt Pt ct' with
          | next ev ct'' => exact ⟨ev, ct'', rfl⟩
          | halt s =>
            rw [run_add_running i 1 ct ct' t hti, run_succ_halt 0 hs] at h1; cases h1
          | ub => rw [run_add_running i 1 ct ct' t hti, run_succ_ub 0 hs] at h1; cases h1
          | block => rw [run_add_running i 1 ct ct' t hti, run_succ_block 0 hs] at h1; cases h1
        obtain ⟨ev, ct'', hs⟩ := hst
        refine Or.inr ⟨fun ev' ct''' hs' => ?_, fun st hs' => (by rw [hs] at hs'; cases hs'),
          (by rw [hs]; exact fun h => by cases h)⟩
        rw [hs] at hs'
        cases hs'
        have hagree := lomega_agree Ss Ps mt Pt R cs ct i
        have hseq : lseq Ss Ps mt Pt R cs ct (i + 1) =
            ((lnext Ss Ps mt Pt R cs' ct').1, (lnext Ss Ps mt Pt R cs' ct').2.1) := by
          simp only [lseq, hi]
        have horc : lorc Ss Ps mt Pt R cs ct i = (lnext Ss Ps mt Pt R cs' ct').2.2 := by
          simp only [lorc, hi]
        rw [hseq, horc, hi] at hagree
        simp only at hagree
        revert hagree hseq
        simp only [lnext, hs]
        split
        · rename_i hex
          intro hagree hseq
          have hc := Classical.choose_spec hex
          exact Or.inl ⟨(Classical.choose hex).2.1, (Classical.choose hex).2.2,
            run_local_running _ _ _ _ hc.1 hagree, i + 1, hseq⟩
        · rename_i hex
          intro _ hseq
          rcases (h.step cs' ct' hRi) with ⟨ω', hub'⟩ | ⟨hnext, _, _⟩
          · exact absurd ⟨i, ocomb cs'.nAlloc ω ω', by
              rw [hti]
              have := srcUBPre_ocomb (ω₂ := ω') hsi (srcUBPre_of_srcUB hub' [])
              simpa [Outcome.trace] using this⟩ hub
          rcases hnext ev ct'' hs with ⟨ω'', k, cs'', hk, hR'⟩ | ⟨rfl, hμ, _⟩
          · exact absurd ⟨(ω'', k, cs''), hk, hR'⟩ hex
          · exact Or.inr ⟨rfl, hμ, i + 1, hseq⟩
    obtain ⟨bs, hbs, himp⟩ := hsim.improves (cs := cs) (ct := ct) ⟨0, rfl⟩ bt hbt
    exact ⟨Ω, bs, hbs, himp⟩

end Toy.PlaceEval
