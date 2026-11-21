import Toy.PlaceEval.Transforms

/-!
# Basic facts about `run`, behaviours and refinement

Fully proved helper lemmas used by the examples, counterexamples, non-vacuity theorems
and positive controls.
-/

namespace Toy.PlaceEval

theorem run_succ_next {mode : AllocMode} {P : Prog} {c c' : Cfg} {ev : Option Nat} (n : Nat)
    (h : step mode P c = .next ev c') : run mode P (n + 1) c = (run mode P n c').cons ev := by
  simp [run, h]

theorem run_succ_halt {mode : AllocMode} {P : Prog} {c : Cfg} {s : State} (n : Nat)
    (h : step mode P c = .halt s) : run mode P (n + 1) c = .done [] s := by
  simp [run, h]

theorem run_succ_ub {mode : AllocMode} {P : Prog} {c : Cfg} (n : Nat)
    (h : step mode P c = .ub) : run mode P (n + 1) c = .ub [] := by
  simp [run, h]

theorem run_succ_block {mode : AllocMode} {P : Prog} {c : Cfg} (n : Nat)
    (h : step mode P c = .block) : run mode P (n + 1) c = .blocked := by
  simp [run, h]

/-- A finished outcome (`done`, `ub` or `blocked`) is stable under more fuel. -/
theorem run_finished_add {mode : AllocMode} {P : Prog} :
    ∀ (n k : Nat) (c : Cfg) (o : Outcome), o.isRunning = false →
      run mode P n c = o → run mode P (n + k) c = o
  | 0, _, _, o, ho, h => by subst h; simp [run, Outcome.isRunning] at ho
  | n + 1, k, c, o, ho, h => by
    rw [Nat.add_right_comm]
    cases hs : step mode P c with
    | next ev c' =>
      rw [run_succ_next _ hs] at h ⊢
      cases hr : run mode P n c' with
      | done t' s' =>
        rw [run_finished_add n k c' _ rfl hr]; rw [hr] at h; exact h
      | ub t' =>
        rw [run_finished_add n k c' _ rfl hr]; rw [hr] at h; exact h
      | blocked =>
        rw [run_finished_add n k c' _ rfl hr]; rw [hr] at h; exact h
      | running c'' t' =>
        rw [hr] at h; subst h; simp [Outcome.cons, Outcome.isRunning] at ho
    | halt s' => rw [run_succ_halt _ hs] at h ⊢; exact h
    | ub => rw [run_succ_ub _ hs] at h ⊢; exact h
    | block => rw [run_succ_block _ hs] at h ⊢; exact h

theorem run_finished_mono {mode : AllocMode} {P : Prog} {n m : Nat} {c : Cfg} {o : Outcome}
    (ho : o.isRunning = false) (h : run mode P n c = o) (hnm : n ≤ m) : run mode P m c = o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact run_finished_add n k c o ho h

/-- A run that finishes with outcome `o` (not running) determines the behaviours: a
terminating run gives `term`, a UB run gives `wrong`, a blocked run gives none. -/
theorem hasBehFrom_iff_of_run_done {mode : AllocMode} {P : Prog} {c : Cfg} {n : Nat}
    {t : List Nat} {s : State} (h : run mode P n c = .done t s) (b : Beh) :
    HasBehFrom mode P c b ↔ b = .term t := by
  constructor
  · intro hb
    cases b with
    | term t' =>
      obtain ⟨m, s', hm⟩ := hb
      have e₁ := run_finished_mono rfl h (Nat.le_max_left n m)
      have e₂ := run_finished_mono rfl hm (Nat.le_max_right n m)
      rw [e₁] at e₂; cases e₂; rfl
    | wrong t' =>
      obtain ⟨m, hm⟩ := hb
      have e₁ := run_finished_mono rfl h (Nat.le_max_left n m)
      have e₂ := run_finished_mono rfl hm (Nat.le_max_right n m)
      rw [e₁] at e₂; cases e₂
    | div t' => have := hb.1 n; rw [h] at this; simp [Outcome.isRunning] at this
    | react f => have := hb.1 n; rw [h] at this; simp [Outcome.isRunning] at this
  · rintro rfl; exact ⟨n, s, h⟩

theorem hasBehFrom_iff_of_run_ub {mode : AllocMode} {P : Prog} {c : Cfg} {n : Nat}
    {t : List Nat} (h : run mode P n c = .ub t) (b : Beh) :
    HasBehFrom mode P c b ↔ b = .wrong t := by
  constructor
  · intro hb
    cases b with
    | term t' =>
      obtain ⟨m, s', hm⟩ := hb
      have e₁ := run_finished_mono rfl h (Nat.le_max_left n m)
      have e₂ := run_finished_mono rfl hm (Nat.le_max_right n m)
      rw [e₁] at e₂; cases e₂
    | wrong t' =>
      obtain ⟨m, hm⟩ := hb
      have e₁ := run_finished_mono rfl h (Nat.le_max_left n m)
      have e₂ := run_finished_mono rfl hm (Nat.le_max_right n m)
      rw [e₁] at e₂; cases e₂; rfl
    | div t' => have := hb.1 n; rw [h] at this; simp [Outcome.isRunning] at this
    | react f => have := hb.1 n; rw [h] at this; simp [Outcome.isRunning] at this
  · rintro rfl; exact ⟨n, h⟩

theorem not_hasBehFrom_of_run_blocked {mode : AllocMode} {P : Prog} {c : Cfg} {n : Nat}
    (h : run mode P n c = .blocked) (b : Beh) : ¬ HasBehFrom mode P c b := by
  intro hb
  cases b with
  | term t' =>
    obtain ⟨m, s', hm⟩ := hb
    have e₁ := run_finished_mono rfl h (Nat.le_max_left n m)
    have e₂ := run_finished_mono rfl hm (Nat.le_max_right n m)
    rw [e₁] at e₂; cases e₂
  | wrong t' =>
    obtain ⟨m, hm⟩ := hb
    have e₁ := run_finished_mono rfl h (Nat.le_max_left n m)
    have e₂ := run_finished_mono rfl hm (Nat.le_max_right n m)
    rw [e₁] at e₂; cases e₂
  | div t' => have := hb.1 n; rw [h] at this; simp [Outcome.isRunning] at this
  | react f => have := hb.1 n; rw [h] at this; simp [Outcome.isRunning] at this

/-- Under a static slot assignment the oracle is irrelevant. -/
theorem hasBeh_slots_iff (s : Local → Nat) (P : Prog) (b : Beh) :
    HasBeh (.slots s) P b ↔ HasBehIn (.slots s) P b :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun _ => 0, h⟩⟩

/-- Behaviours of a program whose (deterministic) run terminates. -/
theorem hasBehIn_iff_of_done {mode : AllocMode} {P : Prog} {st0 : State} {n : Nat}
    {t : List Nat} {s : State} (h0 : P.initState mode = some st0)
    (h : run mode P n (P.entry 0 st0) = .done t s) (b : Beh) :
    HasBehIn mode P b ↔ b = .term t := by
  unfold HasBehIn
  rw [h0]
  constructor
  · rintro ⟨st, hst, hb⟩
    cases hst
    exact (hasBehFrom_iff_of_run_done h b).1 hb
  · intro hb
    exact ⟨st0, rfl, (hasBehFrom_iff_of_run_done h b).2 hb⟩

/-- Behaviours of a program whose (deterministic) run reaches UB. -/
theorem hasBehIn_iff_of_ub {mode : AllocMode} {P : Prog} {st0 : State} {n : Nat}
    {t : List Nat} (h0 : P.initState mode = some st0)
    (h : run mode P n (P.entry 0 st0) = .ub t) (b : Beh) :
    HasBehIn mode P b ↔ b = .wrong t := by
  unfold HasBehIn
  rw [h0]
  constructor
  · rintro ⟨st, hst, hb⟩
    cases hst
    exact (hasBehFrom_iff_of_run_ub h b).1 hb
  · intro hb
    exact ⟨st0, rfl, (hasBehFrom_iff_of_run_ub h b).2 hb⟩

/-- No behaviours when the run blocks. -/
theorem not_hasBehIn_of_blocked {mode : AllocMode} {P : Prog} {st0 : State} {n : Nat}
    (h0 : P.initState mode = some st0) (h : run mode P n (P.entry 0 st0) = .blocked)
    (b : Beh) : ¬ HasBehIn mode P b := by
  rintro ⟨st, hst, hb⟩
  rw [h0] at hst
  cases hst
  exact not_hasBehFrom_of_run_blocked h b hb

theorem improvesPP_refl (b : Beh) : ImprovesPP b b := Or.inl rfl

theorem prefix_nil (u : List Nat) : [] <+: u := ⟨u, rfl⟩

theorem hasPrefix_nil (b : Beh) : b.HasPrefix [] := by
  cases b <;> simp [Beh.HasPrefix, prefixOf]

/-- Every behaviour improves `wrong []`. -/
theorem improvesPP_wrong_nil (b : Beh) : ImprovesPP b (.wrong []) :=
  Or.inr ⟨[], rfl, hasPrefix_nil b⟩

/-- `wrong []` improves only `wrong []`. -/
theorem improvesPP_wrong_nil_iff (bs : Beh) : ImprovesPP (.wrong []) bs ↔ bs = .wrong [] := by
  constructor
  · rintro (h | ⟨t, rfl, ht⟩)
    · exact h.symm
    · simp only [Beh.HasPrefix] at ht
      obtain ⟨u, hu⟩ := ht
      have : t = [] := by
        cases t with
        | nil => rfl
        | cons a t => simp at hu
      rw [this]
  · rintro rfl; exact improvesPP_refl _

/-- A terminating behaviour improves `bs` iff `bs` is the same behaviour or UB after a
prefix of its trace. -/
theorem improvesPP_term_iff (t : List Nat) (bs : Beh) :
    ImprovesPP (.term t) bs ↔ bs = .term t ∨ ∃ u, bs = .wrong u ∧ u <+: t := by
  constructor
  · rintro (h | ⟨u, rfl, hu⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨u, rfl, hu⟩
  · rintro (rfl | ⟨u, rfl, hu⟩)
    · exact improvesPP_refl _
    · exact Or.inr ⟨u, rfl, hu⟩

/-- Distinct terminating behaviours do not improve each other. -/
theorem not_improvesPP_term_term {t u : List Nat} (h : t ≠ u) :
    ¬ ImprovesPP (.term t) (.term u) := by
  rintro (e | ⟨v, e, _⟩)
  · cases e; exact h rfl
  · cases e

theorem refinesPP_refl (S : Sem) (P : Prog) : RefinesPP S P P :=
  fun bt h => ⟨bt, h, improvesPP_refl bt⟩

theorem improvesPP_trans {b₁ b₂ b₃ : Beh} (h₁₂ : ImprovesPP b₁ b₂) (h₂₃ : ImprovesPP b₂ b₃) :
    ImprovesPP b₁ b₃ := by
  rcases h₂₃ with rfl | ⟨t, rfl, ht⟩
  · exact h₁₂
  · rcases h₁₂ with rfl | ⟨u, rfl, hu⟩
    · exact Or.inr ⟨t, rfl, ht⟩
    · refine Or.inr ⟨t, rfl, ?_⟩
      simp only [Beh.HasPrefix] at ht
      cases b₁ with
      | term v => exact List.IsPrefix.trans ht hu
      | wrong v => exact List.IsPrefix.trans ht hu
      | div v => exact List.IsPrefix.trans ht hu
      | react f =>
        simp only [Beh.HasPrefix] at hu ⊢
        obtain ⟨w, rfl⟩ := ht
        have hlen : (t ++ w).length = t.length + w.length := List.length_append
        rw [hlen] at hu
        have e : prefixOf f (t.length + w.length) = prefixOf f t.length ++
            (List.range' t.length w.length).map f := by
          simp [prefixOf, List.range_add, List.map_append, List.range'_eq_map_range]
        rw [e] at hu
        exact (List.append_inj hu (by simp [prefixOf])).1

/-- Refinement composes. -/
theorem refinesAcross_trans {S₁ S₂ S₃ : Sem} {P₁ P₂ P₃ : Prog}
    (h₁₂ : RefinesAcross S₁ P₁ S₂ P₂) (h₂₃ : RefinesAcross S₂ P₂ S₃ P₃) :
    RefinesAcross S₁ P₁ S₃ P₃ := by
  intro b₃ hb₃
  obtain ⟨b₂, hb₂, i₃₂⟩ := h₂₃ b₃ hb₃
  obtain ⟨b₁, hb₁, i₂₁⟩ := h₁₂ b₂ hb₂
  exact ⟨b₁, hb₁, improvesPP_trans i₃₂ i₂₁⟩

/-- If the target refines the source in the reverse direction (as in an equivalence),
UB-freedom of the target implies UB-freedom of the source. -/
theorem ubFree_of_refinesPP_rev {S : Sem} {src tgt : Prog} (hrev : RefinesPP S tgt src)
    (htgt : UBFree S tgt) : UBFree S src := by
  intro t hs
  obtain ⟨bs, hbs, himp⟩ := hrev _ hs
  rcases himp with rfl | ⟨u, rfl, _⟩
  · exact htgt t hbs
  · exact htgt u hbs

/-- An exact UB checker exists (noncomputably), so statements quantifying over exact
checkers are not vacuous. -/
theorem exactUBChecker_exists (S : Sem) : ∃ chk, ExactUBChecker S chk := by
  classical
  exact ⟨fun P => decide (UBFree S P), fun P => by simp⟩

/-- The run of `P` from its initial state (`blocked` if the entry allocations are
refused). -/
def runFromInit (mode : AllocMode) (P : Prog) (n : Nat) : Outcome :=
  match P.initState mode with
  | some st0 => run mode P n (P.entry 0 st0)
  | none => .blocked

/-- The behaviour a finished outcome determines (`none` for `blocked` or `running`). -/
def Outcome.toBeh? : Outcome → Option Beh
  | .done t _ => some (.term t)
  | .ub t => some (.wrong t)
  | _ => none

/-- If the run from the initial state has finished within `n` steps, the behaviours under
that allocation mode are exactly the one its outcome determines (none if blocked). -/
theorem hasBehIn_iff_toBeh {mode : AllocMode} {P : Prog} {n : Nat}
    (hfin : (runFromInit mode P n).isRunning = false) (b : Beh) :
    HasBehIn mode P b ↔ (runFromInit mode P n).toBeh? = some b := by
  unfold runFromInit at hfin ⊢
  cases h0 : P.initState mode with
  | none =>
    simp only [Outcome.toBeh?, reduceCtorEq, iff_false]
    rintro ⟨st, hst, _⟩
    rw [h0] at hst
    cases hst
  | some st0 =>
    simp only [h0] at hfin ⊢
    cases hr : run mode P n (P.entry 0 st0) with
    | done t s =>
      rw [hasBehIn_iff_of_done h0 hr]
      simp only [Outcome.toBeh?, Option.some.injEq]
      exact eq_comm
    | ub t =>
      rw [hasBehIn_iff_of_ub h0 hr]
      simp only [Outcome.toBeh?, Option.some.injEq]
      exact eq_comm
    | blocked =>
      simp only [Outcome.toBeh?, reduceCtorEq, iff_false]
      exact not_hasBehIn_of_blocked h0 hr b
    | running c t => rw [hr] at hfin; simp [Outcome.isRunning] at hfin

/-- The same, for the deterministic `slots` semantics. -/
theorem hasBeh_slots_iff_toBeh {s : Local → Nat} {P : Prog} {n : Nat}
    (hfin : (runFromInit (.slots s) P n).isRunning = false) (b : Beh) :
    HasBeh (.slots s) P b ↔ (runFromInit (.slots s) P n).toBeh? = some b := by
  rw [hasBeh_slots_iff]
  exact hasBehIn_iff_toBeh hfin b

/-- A finished deterministic run determines the behaviour set. -/
theorem beh_slots_eq {s : Local → Nat} {P : Prog} {n : Nat} {o : Beh}
    (hfin : (runFromInit (.slots s) P n).isRunning = false)
    (ho : (runFromInit (.slots s) P n).toBeh? = some o) (b : Beh) :
    HasBeh (.slots s) P b ↔ b = o := by
  rw [hasBeh_slots_iff_toBeh hfin, ho, Option.some.injEq]
  exact eq_comm

/-- Refinement between programs with singleton behaviour sets. -/
theorem refinesAcross_iff_of_beh {Ss St : Sem} {src tgt : Prog} {bs bt : Beh}
    (hs : ∀ b, HasBeh Ss src b ↔ b = bs) (ht : ∀ b, HasBeh St tgt b ↔ b = bt) :
    RefinesAcross Ss src St tgt ↔ ImprovesPP bt bs := by
  constructor
  · intro h
    obtain ⟨b, hb, himp⟩ := h bt ((ht bt).2 rfl)
    rw [(hs b).1 hb] at himp
    exact himp
  · intro himp b hb
    rw [(ht b).1 hb]
    exact ⟨bs, (hs bs).2 rfl, himp⟩

/-- `RefinesPP` between programs with singleton behaviour sets. -/
theorem refinesPP_iff_of_beh {S : Sem} {src tgt : Prog} {bs bt : Beh}
    (hs : ∀ b, HasBeh S src b ↔ b = bs) (ht : ∀ b, HasBeh S tgt b ↔ b = bt) :
    RefinesPP S src tgt ↔ ImprovesPP bt bs :=
  refinesAcross_iff_of_beh hs ht

/-- Refinement when the target's behaviours all improve one source behaviour. -/
theorem refinesAcross_of_src_beh {Ss St : Sem} {src tgt : Prog} {bs : Beh}
    (hs : HasBeh Ss src bs) (h : ∀ b, HasBeh St tgt b → ImprovesPP b bs) :
    RefinesAcross Ss src St tgt :=
  fun b hb => ⟨bs, hs, h b hb⟩

/-- The configurations reached within `N` steps from the initial state (a finite list,
used to decide statements about all reachable states of a terminating deterministic
run). -/
def reachCfgs (mode : AllocMode) (P : Prog) : Nat → List Cfg
  | 0 => []
  | n + 1 => reachCfgs mode P n ++
      (match runFromInit mode P n with
       | .running c _ => [c]
       | _ => [])

theorem mem_reachCfgs {mode : AllocMode} {P : Prog} {c : Cfg} {t : List Nat} :
    ∀ {n N : Nat}, n < N → runFromInit mode P n = .running c t → c ∈ reachCfgs mode P N
  | _, 0, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n, N + 1, hn, h => by
    simp only [reachCfgs, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | rfl
    · exact Or.inl (mem_reachCfgs hlt h)
    · right; rw [h]; simp

/-- Under a static slot assignment, if the run has finished within `N` steps, every
reachable configuration is among `reachCfgs _ P N`. -/
theorem reachableAt_slots_mem {s : Local → Nat} {P : Prog} {l : Label} {i : Nat} {st : State}
    {N : Nat} (hN : (runFromInit (.slots s) P N).isRunning = false)
    (h : ReachableAt (.slots s) P l i st) : P.at l i st ∈ reachCfgs (.slots s) P N := by
  obtain ⟨ω, st0, n, t, h0, hr⟩ := h
  simp only [Sem.mode] at h0 hr
  have hr' : runFromInit (.slots s) P n = .running (P.at l i st) t := by
    simp only [runFromInit, h0]; exact hr
  by_cases hn : n < N
  · exact mem_reachCfgs hn hr'
  · exfalso
    have hN' := hN
    simp only [runFromInit, h0] at hN'
    have e := run_finished_mono hN' rfl (Nat.le_of_not_lt hn)
    rw [hr] at e
    rw [← e] at hN'
    simp [Outcome.isRunning] at hN'

/-- Symbolic evaluation of runs of concrete programs (also for a symbolic fresh-address
oracle): unfold the semantics with `simp`. -/
syntax "simp_run" ("[" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| simp_run $[[$xs,*]]? $[$loc]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp [runFromInit, Prog.initState, allocEntry, Prog.hasMarkers, allocate,
      deallocate, Prog.layout, run, step, execStmt, Prog.entry, Prog.blk, evalPlace,
      State.basePtr, State.allocOf, Mem.store, Mem.dereferenceable, Mem.inBounds, Rvalue.eval,
      Operand.eval, Operand.evalInt, Mem.load, Mem.loadPtr, aligned, Stmt.isMarkerOf,
      Mem.writeCells, placeCells, Mem.readCells, Mem.get, Ty.decode, Ty.size, Ty.align,
      Val.encode, encodeLE, decodeLE, decodePtr, Outcome.cons, evalProjs, projStep,
      Mem.offsetInbounds, Ptr.offset, Nat.mod_one, Outcome.trace, Outcome.toBeh?,
      Outcome.isRunning, Option.getD, selectTarget, eraseMarkers, deleteStmt,
      setTerm, setStmt, Prog.setBlk, ptrSize, ptrAlign, Sem.mode, List.range_succ, List.range_zero,
      Nat.mul_mod_right, $xs,*] $[$loc]?)

end Toy.PlaceEval
