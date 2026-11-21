import Toy.ZstAssume.Examples
import Toy.ZstAssume.EditSim

/-!
# Zero-size accesses and zero-count copies: elimination, introduction, checking

Deleting and inserting zero-size accesses (exact conditions and sufficient
conditions), concrete UB-erasing and UB-introducing instances, and checking optimized
programs for UB.
-/

namespace Toy.ZstAssume

/-- Unfold one concrete run. -/
syntax "simp_run" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| simp_run) => `(tactic| simp [run, step, execStmt, Stmt.pre, accessOK,
      ZContract.holds, Prog.init, Prog.entry, Prog.blk, Expr.eval, Cond.eval, Outcome.cons,
      selectTarget, State.set, mkState, Block.unreach])
  | `(tactic| simp_run [$ts,*]) => `(tactic| simp [run, step, execStmt, Stmt.pre, accessOK,
      ZContract.holds, Prog.init, Prog.entry, Prog.blk, Expr.eval, Cond.eval, Outcome.cons,
      selectTarget, State.set, mkState, Block.unreach, $ts,*])

/-- Unfold one concrete run in a hypothesis. -/
syntax "simp_run" "[" Lean.Parser.Tactic.simpLemma,* "]" "at" ident : tactic
macro_rules
  | `(tactic| simp_run [$ts,*] at $h:ident) => `(tactic| simp [run, step, execStmt, Stmt.pre,
      accessOK, ZContract.holds, Prog.init, Prog.entry, Prog.blk, Expr.eval, Cond.eval,
      Outcome.cons, selectTarget, State.set, mkState, Block.unreach, $ts,*] at $h:ident)

/-! ### Shared helpers (fully proved) -/

/-- Refinement from per-input run facts: on every input the target terminates with some
trace `t`, and the source terminates with `t` or reaches UB after a prefix of `t`. -/
theorem refinesPP_of_tgt_done {K : ZContract} {src tgt : Prog}
    (h : ∀ σ, ∃ n t s, run K tgt n (tgt.init σ) = .done t s ∧
      ((∃ m s', run K src m (src.init σ) = .done t s') ∨
        ∃ m t', run K src m (src.init σ) = .ub t' ∧ t' <+: t)) :
    RefinesPP K src tgt := by
  intro σ bt hbt
  obtain ⟨n, t, s, hn, hsrc⟩ := h σ
  have := (hasBehFrom_iff_of_run_done hn bt).1 hbt
  subst this
  rcases hsrc with ⟨m, s', hm⟩ | ⟨m, t', hm, ht'⟩
  · exact ⟨.term t, ⟨m, s', hm⟩, Or.inl rfl⟩
  · exact ⟨.wrong t', ⟨m, hm⟩, Or.inr ⟨t', rfl, ht'⟩⟩

/-- Two programs with the same behaviours on every input are equivalent under the
prefix-preserving discipline. -/
theorem equivPP_of_sameBeh {K : ZContract} {p q : Prog}
    (h : ∀ σ b, HasBeh K p σ b ↔ HasBeh K q σ b) : EquivPP K p q :=
  ⟨fun σ bt hbt => ⟨bt, (h σ bt).2 hbt, Or.inl rfl⟩,
   fun σ bt hbt => ⟨bt, (h σ bt).1 hbt, Or.inl rfl⟩⟩

/-- If on some input the source terminates and the target reaches UB, the target does
not refine the source, even under the whole-trace discipline. -/
theorem not_refinesWT_of_term_wrong {K : ZContract} {src tgt : Prog} {σ : State}
    {u t : List Int} (hs : HasBeh K src σ (.term u)) (ht : HasBeh K tgt σ (.wrong t)) :
    ¬ RefinesWT K src tgt := by
  intro h
  obtain ⟨bs, hbs, himp⟩ := h σ _ ht
  obtain ⟨n, s, hn⟩ := hs
  have := (hasBehFrom_iff_of_run_done hn bs).1 hbs
  subst this
  rcases himp with h' | ⟨t', ht'⟩
  · cases h'
  · cases ht'

/-! ### Per-input helpers (fully proved) -/

/-- Per-input refinement when the target terminates. -/
theorem refinesPPAt_of_tgt_done {K : ZContract} {src tgt : Prog} {σ : State} {n : Nat}
    {t : List Int} {s : State} (hn : run K tgt n (tgt.init σ) = .done t s)
    (hsrc : (∃ m s', run K src m (src.init σ) = .done t s') ∨
      ∃ m t', run K src m (src.init σ) = .ub t' ∧ t' <+: t) :
    ∀ bt, HasBeh K tgt σ bt → ∃ bs, HasBeh K src σ bs ∧ ImprovesPP bt bs := by
  intro bt hbt
  have := (hasBehFrom_iff_of_run_done hn bt).1 hbt
  subst this
  rcases hsrc with ⟨m, s', hm⟩ | ⟨m, t', hm, ht'⟩
  · exact ⟨.term t, ⟨m, s', hm⟩, Or.inl rfl⟩
  · exact ⟨.wrong t', ⟨m, hm⟩, Or.inr ⟨t', rfl, ht'⟩⟩

/-- Per-input refinement when the target reaches UB. -/
theorem refinesPPAt_of_tgt_ub {K : ZContract} {src tgt : Prog} {σ : State} {n m : Nat}
    {t t' : List Int} (hn : run K tgt n (tgt.init σ) = .ub t)
    (hm : run K src m (src.init σ) = .ub t') (ht' : t' <+: t) :
    ∀ bt, HasBeh K tgt σ bt → ∃ bs, HasBeh K src σ bs ∧ ImprovesPP bt bs := by
  intro bt hbt
  have := (hasBehFrom_iff_of_run_ub hn bt).1 hbt
  subst this
  exact ⟨.wrong t', ⟨m, hm⟩, Or.inr ⟨t', rfl, ht'⟩⟩

/-- Different terminating traces on one input refute refinement. -/
theorem not_refinesWT_of_term_term {K : ZContract} {src tgt : Prog} {σ : State}
    {u u' : List Int} (hs : HasBeh K src σ (.term u)) (ht : HasBeh K tgt σ (.term u'))
    (hne : u ≠ u') : ¬ RefinesWT K src tgt := by
  intro h
  obtain ⟨bs, hbs, himp⟩ := h σ _ ht
  obtain ⟨n, s, hn⟩ := hs
  have := (hasBehFrom_iff_of_run_done hn bs).1 hbs
  subst this
  rcases himp with h' | ⟨t', ht'⟩
  · cases h'; exact hne rfl
  · cases ht'

/-- Same behaviour from per-input runs to the same terminal outcome. -/
theorem hasBeh_iff_of_runs_done {K : ZContract} {p q : Prog} {σ : State} {n m : Nat}
    {t : List Int} {s s' : State} (hp : run K p n (p.init σ) = .done t s)
    (hq : run K q m (q.init σ) = .done t s') (b : Beh) : HasBeh K p σ b ↔ HasBeh K q σ b := by
  unfold HasBeh
  rw [hasBehFrom_iff_of_run_done hp, hasBehFrom_iff_of_run_done hq]

theorem hasBeh_iff_of_runs_ub {K : ZContract} {p q : Prog} {σ : State} {n m : Nat}
    {t : List Int} (hp : run K p n (p.init σ) = .ub t) (hq : run K q m (q.init σ) = .ub t)
    (b : Beh) : HasBeh K p σ b ↔ HasBeh K q σ b := by
  unfold HasBeh
  rw [hasBehFrom_iff_of_run_ub hp, hasBehFrom_iff_of_run_ub hq]

/-! ### Deleting a zero-size access -/

/-- **Deletion refines.** Deleting a zero-size `read`/`write`, or a `copy` of
`τ.size * n = 0` bytes, at point `(l, i)` gives a prefix-preserving refinement of the
source, for every zero-size contract `K`. -/
theorem deleteZeroSizeAccess_refinesPP (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    RefinesPP K P (deleteStmt P l i) := by
  exact del_refinesPP hs hz

/-- **Exact condition for equivalence (prefix-preserving).** Deleting a zero-size access
at `(l, i)` is a prefix-preserving equivalence iff, for every reachable state at
`(l, i)` in which `pre₀` fails, the target run from the point after the deleted
statement reaches UB before emitting any event. -/
theorem deleteZeroSizeAccess_equivPP_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivPP K P (deleteStmt P l i) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        GoesWrongFrom K (deleteStmt P l i) ((deleteStmt P l i).at l i st) [] := by
  exact del_equivPP_iff hs hz

/-- **Exact condition for equivalence (whole-trace).** Deleting a zero-size access at
`(l, i)` is a whole-trace equivalence iff, for every reachable state at `(l, i)` in
which `pre₀` fails, the target run from the point after the deleted statement reaches
UB (possibly after emitting events). -/
theorem deleteZeroSizeAccess_equivWT_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivWT K P (deleteStmt P l i) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        ∃ t, GoesWrongFrom K (deleteStmt P l i) ((deleteStmt P l i).at l i st) t := by
  exact del_equivWT_iff hs hz

/-- **Sufficient condition.** If `pre₀` holds on every reachable state at `(l, i)`,
deleting the zero-size access there is a prefix-preserving equivalence. -/
theorem deleteZeroSizeAccess_equivPP_of_zeroPre_reachable (K : ZContract) (P : Prog)
    (l : Label) (i : Nat) (s : Stmt) (hs : (P.blk l).stmts[i]? = some s)
    (hz : IsZeroSizeAccess s) (hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true) :
    EquivPP K P (deleteStmt P l i) := by
  exact del_equivPP_of_zeroPre hs hz hpre

/-- **Corollary: permissive contract.** Under the contract `pre₀ = True`, deleting a
zero-size access is a prefix-preserving equivalence. -/
theorem deleteZeroSizeAccess_equivPP_of_anyPtr (P : Prog) (l : Label) (i : Nat) (s : Stmt)
    (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivPP .anyPtr P (deleteStmt P l i) := by
  exact deleteZeroSizeAccess_equivPP_of_zeroPre_reachable .anyPtr P l i s hs hz
    fun st _ => zeroPre_anyPtr s st

/-- **Corollary: alignment one, null permitted.** If the contract is not
`nonnullAligned` and the accessed type has alignment `1`, deleting a zero-size access
is a prefix-preserving equivalence. -/
theorem deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted (K : ZContract)
    (P : Prog) (l : Label) (i : Nat) (s : Stmt) (hs : (P.blk l).stmts[i]? = some s)
    (hz : IsZeroSizeAccess s) (hK : K ≠ .nonnullAligned)
    (ha : ∀ τ, s.accessTy? = some τ → τ.align = 1) :
    EquivPP K P (deleteStmt P l i) := by
  exact deleteZeroSizeAccess_equivPP_of_zeroPre_reachable K P l i s hs hz
    fun st _ => zeroPre_of_align_one hK s st ha

/-- **Counterexample for the hypothesis `hz` of the deletion results.** In `pEmit7`,
position `(0, 0)` holds `emit 7`, which is not a zero-size access. Every other
hypothesis of the deletion results holds for it (it has no accessed type and its
`zeroPre` is `true` in every state), yet deleting it is not a whole-trace refinement,
and both characterizations fail (their left-hand sides are false, their right-hand
sides hold vacuously). -/
theorem deleteStmt_hz_counterexample (K : ZContract) :
    (pEmit7.blk 0).stmts[0]? = some (.emit (.const 7)) ∧
      ¬ IsZeroSizeAccess (.emit (.const 7)) ∧
      (∀ τ, (Stmt.emit (.const 7)).accessTy? = some τ → τ.align = 1) ∧
      (∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.emit (.const 7)).zeroPre K st = true) ∧
      ¬ RefinesWT K pEmit7 (deleteStmt pEmit7 0 0) ∧
      ¬ (EquivPP K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.emit (.const 7)).zeroPre K st = false →
          GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) []) ∧
      ¬ (EquivWT K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.emit (.const 7)).zeroPre K st = false →
          ∃ t, GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) t) := by
  have hd : deleteStmt pEmit7 0 0 = pHalt := by decide
  have hn : ¬ RefinesWT K pEmit7 pHalt :=
    not_refinesWT_of_term_term (σ := mkState []) (hasBeh_emit7 K _) ⟨1, _, rfl⟩ (by decide)
  rw [hd]
  refine ⟨by decide, by decide, fun τ h => by simp [Stmt.accessTy?] at h, fun _ _ => rfl, hn,
    fun h => ?_, fun h => ?_⟩
  · exact hn (refinesWT_of_refinesPP (h.2 fun _ _ hf => by simp [Stmt.zeroPre] at hf).1)
  · exact hn (h.2 fun _ _ hf => by simp [Stmt.zeroPre] at hf).1

/-- **Counterexample for the hypothesis `hs` of the deletion results.** For every
contract that permits null, the zero-size read `read (var 0) ⟨0, 1⟩` (alignment `1`)
satisfies every other hypothesis of the deletion results (its `zeroPre` is `true` in
every state), but position `(0, 0)` of `pEmit7` holds `emit 7`; deleting that
statement is not a whole-trace refinement, and both characterizations fail. -/
theorem deleteStmt_hs_counterexample (K : ZContract) (hK : K ≠ .nonnullAligned) :
    (pEmit7.blk 0).stmts[0]? ≠ some (.read (.var 0) ⟨0, 1⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 1⟩) ∧
      (∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1) ∧
      (∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = true) ∧
      ¬ RefinesWT K pEmit7 (deleteStmt pEmit7 0 0) ∧
      ¬ (EquivPP K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st →
          (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = false →
          GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) []) ∧
      ¬ (EquivWT K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st →
          (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = false →
          ∃ t, GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) t) := by
  have hd : deleteStmt pEmit7 0 0 = pHalt := by decide
  have hn : ¬ RefinesWT K pEmit7 pHalt :=
    not_refinesWT_of_term_term (σ := mkState []) (hasBeh_emit7 K _) ⟨1, _, rfl⟩ (by decide)
  have ha : ∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1 := by
    intro τ h
    simp only [Stmt.accessTy?, Option.some.injEq] at h
    subst h
    rfl
  have hpre : ∀ st, (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = true :=
    fun st => zeroPre_of_align_one hK _ st ha
  rw [hd]
  refine ⟨by decide, by decide, ha, fun st _ => hpre st, hn, fun h => ?_, fun h => ?_⟩
  · refine hn (refinesWT_of_refinesPP (h.2 fun st _ hf => ?_).1)
    rw [hpre st] at hf
    cases hf
  · refine hn (h.2 fun st _ hf => ?_).1
    rw [hpre st] at hf
    cases hf

/-! #### `pre₀` may fail on a reachable state while deletion is still an equivalence
(fully proved) -/

/-- Two identical zero-size reads through local `0` at alignment `4`. -/
def pTwoZstReads : Prog := [⟨[.read (.var 0) ⟨0, 4⟩, .read (.var 0) ⟨0, 4⟩], .halt⟩]

/-- Non-vacuity of `deleteZeroSizeAccess_equivPP_iff` and
`deleteZeroSizeAccess_equivWT_iff`: `pTwoZstReads` satisfies `hs` and `hz` at `(0, 0)`. -/
theorem deleteZeroSizeAccess_iff_nonvacuous :
    (pTwoZstReads.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 4⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) := by decide

/-- **Counterexample to "equivalence requires `pre₀` on every reachable state".**
In `pTwoZstReads` under the `aligned` contract, `pre₀` of the first read fails at a
reachable state (local `0` equal to `1`) and the target run from the point after the
deleted read reaches UB with empty trace, so deleting the first read is a
prefix-preserving equivalence: the second read reaches the same UB at the same trace. -/
theorem deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure :
    ReachableAt .aligned pTwoZstReads 0 0 (mkState [1]) ∧
      (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [1]) = false ∧
      GoesWrongFrom .aligned (deleteStmt pTwoZstReads 0 0)
        ((deleteStmt pTwoZstReads 0 0).at 0 0 (mkState [1])) [] ∧
      EquivPP .aligned pTwoZstReads (deleteStmt pTwoZstReads 0 0) := by
  have hd : deleteStmt pTwoZstReads 0 0 = [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩] := by decide
  rw [hd]
  refine ⟨reachableAt_entry _ _ _, by decide, ⟨1, rfl⟩, equivPP_of_sameBeh fun σ b => ?_⟩
  by_cases h : aligned 4 (σ.locals 0) = true
  · have h₁ : run .aligned pTwoZstReads 3 (pTwoZstReads.init σ) = .done [] σ := by
      simp [run, step, execStmt, Stmt.pre, accessOK, ZContract.holds, Prog.init, Prog.entry,
        Prog.blk, pTwoZstReads, Expr.eval, h, Outcome.cons]
    have h₂ : run .aligned [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩] 2
        (Prog.init [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩] σ) = .done [] σ := by
      simp [run, step, execStmt, Stmt.pre, accessOK, ZContract.holds, Prog.init, Prog.entry,
        Prog.blk, Expr.eval, h, Outcome.cons]
    unfold HasBeh
    rw [hasBehFrom_iff_of_run_done h₁, hasBehFrom_iff_of_run_done h₂]
  · have h₁ : run .aligned pTwoZstReads 1 (pTwoZstReads.init σ) = .ub [] := by
      simp [run, step, execStmt, Stmt.pre, accessOK, ZContract.holds, Prog.init, Prog.entry,
        Prog.blk, pTwoZstReads, Expr.eval, h]
    have h₂ : run .aligned [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩] 1
        (Prog.init [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩] σ) = .ub [] := by
      simp [run, step, execStmt, Stmt.pre, accessOK, ZContract.holds, Prog.init, Prog.entry,
        Prog.blk, Expr.eval, h]
    unfold HasBeh
    rw [hasBehFrom_iff_of_run_ub h₁, hasBehFrom_iff_of_run_ub h₂]

/-! ### UB-erasing deletions (fully proved counterexamples) -/

/-- A zero-size read through local `0` at alignment `4`, then `halt`. -/
def pReadZst4 : Prog := [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩]

/-- A zero-size read through local `0` at alignment `1`, then `halt`. -/
def pReadZst1 : Prog := [⟨[.read (.var 0) ⟨0, 1⟩], .halt⟩]

/-- `copy (var 0) (var 1) ⟨4, 4⟩ 0`, then `halt`: a zero-count copy of a 4-byte,
4-aligned element type. -/
def pCopy0 : Prog := copyProg 0 1 ⟨4, 4⟩ 0

theorem deleteStmt_pReadZst4 : deleteStmt pReadZst4 0 0 = pHalt := by decide
theorem deleteStmt_pReadZst1 : deleteStmt pReadZst1 0 0 = pHalt := by decide
theorem deleteStmt_pCopy0 : deleteStmt pCopy0 0 0 = pHalt := by decide

theorem run_pHalt (K : ZContract) (σ : State) : run K pHalt 1 (pHalt.init σ) = .done [] σ :=
  rfl

/-- **Zero-size read through a misaligned pointer.** Under the `aligned` contract, the
source `pReadZst4` reaches UB on the input with local `0 = 1` (not a multiple of `4`);
after deleting the read the program terminates there. Deletion is a prefix-preserving
refinement but not even a whole-trace equivalence. -/
theorem zstRead_misaligned_deletion_erases_ub :
    HasBeh .aligned pReadZst4 (mkState [1]) (.wrong []) ∧
      HasBeh .aligned (deleteStmt pReadZst4 0 0) (mkState [1]) (.term []) ∧
      RefinesPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) ∧
      ¬ EquivWT .aligned pReadZst4 (deleteStmt pReadZst4 0 0) := by
  rw [deleteStmt_pReadZst4]
  have hw : HasBeh .aligned pReadZst4 (mkState [1]) (.wrong []) := ⟨1, rfl⟩
  have ht : HasBeh .aligned pHalt (mkState [1]) (.term []) := ⟨1, _, rfl⟩
  refine ⟨hw, ht, refinesPP_of_tgt_done fun σ => ⟨1, [], σ, rfl, ?_⟩,
    fun h => not_refinesWT_of_term_wrong ht hw h.2⟩
  by_cases h : aligned 4 (σ.locals 0) = true
  · exact Or.inl ⟨2, σ, by simp_run [pReadZst4, h]⟩
  · exact Or.inr ⟨1, [], by simp_run [pReadZst4, h], prefix_nil _⟩

/-- **Zero-count copy with a misaligned source.** Under the `aligned` contract,
`copy src dst ⟨4, 4⟩ 0` with `src = 1`, `dst = 8` is UB; after deletion the program
terminates. Deletion is a prefix-preserving refinement but not a whole-trace
equivalence. -/
theorem zeroCountCopy_misalignedSrc_deletion_erases_ub :
    HasBeh .aligned pCopy0 (mkState [1, 8]) (.wrong []) ∧
      HasBeh .aligned (deleteStmt pCopy0 0 0) (mkState [1, 8]) (.term []) ∧
      RefinesPP .aligned pCopy0 (deleteStmt pCopy0 0 0) ∧
      ¬ EquivWT .aligned pCopy0 (deleteStmt pCopy0 0 0) := by
  rw [deleteStmt_pCopy0]
  have hw : HasBeh .aligned pCopy0 (mkState [1, 8]) (.wrong []) := ⟨1, rfl⟩
  have ht : HasBeh .aligned pHalt (mkState [1, 8]) (.term []) := ⟨1, _, rfl⟩
  refine ⟨hw, ht, refinesPP_of_tgt_done fun σ => ⟨1, [], σ, rfl, ?_⟩,
    fun h => not_refinesWT_of_term_wrong ht hw h.2⟩
  by_cases h : (aligned 4 (σ.locals 0) && aligned 4 (σ.locals 1)) = true
  · exact Or.inl ⟨2, σ, by simp_run [pCopy0, copyProg, h]⟩
  · exact Or.inr ⟨1, [], by simp_run [pCopy0, copyProg, h], prefix_nil _⟩

/-- **Null under a non-null contract.** Under `nonnullAligned`, a zero-size read through
null (local `0 = 0`, alignment `1`) is UB; after deletion the program terminates.
Deletion is a prefix-preserving refinement but not a whole-trace equivalence. -/
theorem zstRead_null_nonnullContract_deletion_erases_ub :
    HasBeh .nonnullAligned pReadZst1 (mkState [0]) (.wrong []) ∧
      HasBeh .nonnullAligned (deleteStmt pReadZst1 0 0) (mkState [0]) (.term []) ∧
      RefinesPP .nonnullAligned pReadZst1 (deleteStmt pReadZst1 0 0) ∧
      ¬ EquivWT .nonnullAligned pReadZst1 (deleteStmt pReadZst1 0 0) := by
  rw [deleteStmt_pReadZst1]
  have hw : HasBeh .nonnullAligned pReadZst1 (mkState [0]) (.wrong []) := ⟨1, rfl⟩
  have ht : HasBeh .nonnullAligned pHalt (mkState [0]) (.term []) := ⟨1, _, rfl⟩
  refine ⟨hw, ht, refinesPP_of_tgt_done fun σ => ⟨1, [], σ, rfl, ?_⟩,
    fun h => not_refinesWT_of_term_wrong ht hw h.2⟩
  by_cases h : σ.locals 0 = 0
  · exact Or.inr ⟨1, [], by simp_run [pReadZst1, h, aligned], prefix_nil _⟩
  · exact Or.inl ⟨2, σ, by simp_run [pReadZst1, h, aligned]⟩

/-- Non-vacuity of `deleteZeroSizeAccess_refinesPP`: `pReadZst4` satisfies `hs` and `hz`
at `(0, 0)`. -/
theorem deleteZeroSizeAccess_refinesPP_nonvacuous :
    (pReadZst4.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 4⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) := by decide

/-- Non-vacuity of the sufficient conditions: `pReadZst1` (alignment `1`) under `aligned`
satisfies every hypothesis of `deleteZeroSizeAccess_equivPP_of_zeroPre_reachable` and of
`deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted`, and the hypotheses `hs`,
`hz` of `deleteZeroSizeAccess_equivPP_of_anyPtr`. -/
theorem deleteZeroSizeAccess_sufficient_nonvacuous :
    (pReadZst1.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 1⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 1⟩) ∧
      (∀ st, ReachableAt .aligned pReadZst1 0 0 st →
        (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre .aligned st = true) ∧
      ZContract.aligned ≠ .nonnullAligned ∧
      (∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1) := by
  have ha : ∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1 := by
    intro τ h
    simp only [Stmt.accessTy?, Option.some.injEq] at h
    subst h
    rfl
  exact ⟨by decide, by decide, fun st _ => zeroPre_of_align_one (by decide) _ st ha,
    by decide, ha⟩

/-- **Counterexample for `hpre`, for `K = .anyPtr` and for `ha` in the sufficient
conditions for an equivalent deletion.** Deleting the zero-size read at alignment `4`
of `pReadZst4` under `aligned`: the statement is at `(0, 0)` and is a zero-size access,
the contract permits null and is not `anyPtr`, `pre₀` fails at a reachable state, the
alignment is not `1`, and the deletion is not a prefix-preserving equivalence. -/
theorem deleteZeroSizeAccess_pReadZst4_counterexample :
    (pReadZst4.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 4⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ZContract.aligned ≠ .nonnullAligned ∧ ZContract.aligned ≠ .anyPtr ∧
      ¬ (∀ st, ReachableAt .aligned pReadZst4 0 0 st →
        (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned st = true) ∧
      ¬ (∀ τ, (Stmt.read (.var 0) ⟨0, 4⟩).accessTy? = some τ → τ.align = 1) ∧
      ¬ EquivPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) := by
  refine ⟨by decide, by decide, by decide, by decide, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := h (mkState [1]) (reachableAt_entry _ _ _)
    exact absurd this (by decide)
  · have : (4 : Nat) = 1 := h ⟨0, 4⟩ rfl
    exact absurd this (by decide)
  · exact zstRead_misaligned_deletion_erases_ub.2.2.2 (equivWT_of_equivPP h)

/-- **Counterexample for `hK` in `deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted`.**
The zero-size read at alignment `1` of `pReadZst1` under `nonnullAligned`: `hs`, `hz`
and `ha` hold, the contract is `nonnullAligned`, and the deletion is not a
prefix-preserving equivalence. -/
theorem deleteZeroSizeAccess_pReadZst1_nonnull_counterexample :
    (pReadZst1.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 1⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 1⟩) ∧
      (∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1) ∧
      ¬ (ZContract.nonnullAligned ≠ .nonnullAligned) ∧
      ¬ EquivPP .nonnullAligned pReadZst1 (deleteStmt pReadZst1 0 0) := by
  refine ⟨by decide, by decide, fun τ h => ?_, fun h => h rfl, fun h => ?_⟩
  · simp only [Stmt.accessTy?, Option.some.injEq] at h
    subst h
    rfl
  · exact zstRead_null_nonnullContract_deletion_erases_ub.2.2.2 (equivWT_of_equivPP h)

/-- **Contrast: null permitted.** Under the `aligned` contract the same zero-size read
at alignment `1` never reaches UB, and its deletion is a prefix-preserving
equivalence. -/
theorem zstRead_align_one_alignedContract_deletion_equivPP :
    EquivPP .aligned pReadZst1 (deleteStmt pReadZst1 0 0) := by
  rw [deleteStmt_pReadZst1]
  refine equivPP_of_sameBeh fun σ b => ?_
  have h₁ : run .aligned pReadZst1 2 (pReadZst1.init σ) = .done [] σ := by
    simp_run [pReadZst1, aligned]
  unfold HasBeh
  rw [hasBehFrom_iff_of_run_done h₁, hasBehFrom_iff_of_run_done (run_pHalt _ σ)]

/-- **Element-loop lowering erases the same UB.** Lowering the zero-count copy `pCopy0`
to the element loop `copyLoopProg 0 1 2 ⟨4, 4⟩ 0` (counter in local `2`) gives a
program that terminates on the input with `src = 1`, `dst = 8`, where the source
reaches UB. The lowering is a prefix-preserving refinement but not a whole-trace
equivalence. -/
theorem copyLoopLowering_zeroCount_erases_ub :
    HasBeh .aligned pCopy0 (mkState [1, 8]) (.wrong []) ∧
      HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (mkState [1, 8]) (.term []) ∧
      RefinesPP .aligned pCopy0 (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) ∧
      ¬ EquivWT .aligned pCopy0 (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) := by
  have hloop : ∀ σ, run .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) 4
      ((copyLoopProg 0 1 2 ⟨4, 4⟩ 0).init σ) = .done [] (σ.set 2 0) := by
    intro σ
    simp_run [copyLoopProg]
  have hw : HasBeh .aligned pCopy0 (mkState [1, 8]) (.wrong []) := ⟨1, rfl⟩
  have ht : HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (mkState [1, 8]) (.term []) :=
    ⟨4, _, hloop _⟩
  refine ⟨hw, ht, refinesPP_of_tgt_done fun σ => ⟨4, [], _, hloop σ, ?_⟩,
    fun h => not_refinesWT_of_term_wrong ht hw h.2⟩
  by_cases h : (aligned 4 (σ.locals 0) && aligned 4 (σ.locals 1)) = true
  · exact Or.inl ⟨2, σ, by simp_run [pCopy0, copyProg, h]⟩
  · exact Or.inr ⟨1, [], by simp_run [pCopy0, copyProg, h], prefix_nil _⟩

/-- **The element-loop lowering overwrites its counter local.** On the input with
locals `8, 8, 42` (aligned pointers), the zero-count copy `pCopy0` terminates with
local `2` still equal to `42`, so it satisfies `wp` for "local `2` is `42`"; the lowering
`copyLoopProg 0 1 2 ⟨4, 4⟩ 0` sets local `2` to `0` and does not. Behaviours, and hence
`RefinesPP`, ignore final states; `wp` observes them. -/
theorem copyLoopLowering_zeroCount_clobbers_counter :
    wp .aligned pCopy0 (fun _ s => s.locals 2 = 42) (mkState [8, 8, 42]) ∧
      ¬ wp .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (fun _ s => s.locals 2 = 42)
        (mkState [8, 8, 42]) := by
  refine ⟨⟨2, [], mkState [8, 8, 42], by simp_run [pCopy0, copyProg, aligned], rfl⟩, ?_⟩
  rintro ⟨n, t, s, hn, hq⟩
  have h4 : run .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) 4
      ((copyLoopProg 0 1 2 ⟨4, 4⟩ 0).init (mkState [8, 8, 42])) =
      .done [] ((mkState [8, 8, 42]).set 2 0) := by
    simp_run [copyLoopProg]
  have e := run_done_mono hn (Nat.le_max_left n 4)
  rw [run_done_mono h4 (Nat.le_max_right n 4)] at e
  cases e
  simp [State.set, mkState] at hq

/-! ### Introducing (materializing or hoisting) a zero-size access -/

/-- **Exact condition for introduction (prefix-preserving).** Inserting a zero-size
access `s` at point `(l, i)` is a prefix-preserving refinement iff, for every
reachable state at `(l, i)` in which `pre₀` fails, the source run from `(l, i)`
reaches UB before emitting any event. -/
theorem insertZeroSizeAccess_refinesPP_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hz : IsZeroSizeAccess s) :
    RefinesPP K P (insertStmt P l i s) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        GoesWrongFrom K P (P.at l i st) [] := by
  exact ins_refinesPP_iff hz

/-- **Exact condition for introduction (whole-trace).** Inserting a zero-size access
`s` at `(l, i)` is a whole-trace refinement iff, for every reachable state at `(l, i)`
in which `pre₀` fails, the source run from `(l, i)` reaches UB (possibly after
emitting events). -/
theorem insertZeroSizeAccess_refinesWT_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hz : IsZeroSizeAccess s) :
    RefinesWT K P (insertStmt P l i s) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        ∃ t, GoesWrongFrom K P (P.at l i st) t := by
  exact ins_refinesWT_iff hz

/-- **Sufficient condition for introduction.** If `pre₀` of `s` holds on every
reachable state at `(l, i)`, inserting the zero-size access `s` there is a
prefix-preserving equivalence (in particular a refinement). -/
theorem insertZeroSizeAccess_equivPP_of_zeroPre_reachable (K : ZContract) (P : Prog)
    (l : Label) (i : Nat) (s : Stmt) (hz : IsZeroSizeAccess s)
    (hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true) :
    EquivPP K P (insertStmt P l i s) := by
  exact ins_equivPP_of_zeroPre hz hpre

/-- **Counterexample for the hypothesis `hz` of the insertion results.** `emit 1` is not
a zero-size access, and its `zeroPre` is `true` in every state (so `hpre` holds);
inserting it into `halt` is not a whole-trace refinement, and both characterizations
fail (their left-hand sides are false, their right-hand sides hold vacuously). -/
theorem insertEmit_counterexample (K : ZContract) :
    ¬ IsZeroSizeAccess (.emit (.const 1)) ∧
      (∀ st, ReachableAt K pHalt 0 0 st → (Stmt.emit (.const 1)).zeroPre K st = true) ∧
      ¬ RefinesWT K pHalt (insertStmt pHalt 0 0 (.emit (.const 1))) ∧
      ¬ (RefinesPP K pHalt (insertStmt pHalt 0 0 (.emit (.const 1))) ↔
        ∀ st, ReachableAt K pHalt 0 0 st → (Stmt.emit (.const 1)).zeroPre K st = false →
          GoesWrongFrom K pHalt (pHalt.at 0 0 st) []) ∧
      ¬ (RefinesWT K pHalt (insertStmt pHalt 0 0 (.emit (.const 1))) ↔
        ∀ st, ReachableAt K pHalt 0 0 st → (Stmt.emit (.const 1)).zeroPre K st = false →
          ∃ t, GoesWrongFrom K pHalt (pHalt.at 0 0 st) t) := by
  have hi : insertStmt pHalt 0 0 (.emit (.const 1)) = [⟨[.emit (.const 1)], .halt⟩] := by decide
  have hn : ¬ RefinesWT K pHalt [⟨[.emit (.const 1)], .halt⟩] :=
    not_refinesWT_of_term_term (σ := mkState []) ⟨1, _, rfl⟩ ⟨2, _, rfl⟩ (by decide)
  rw [hi]
  refine ⟨by decide, fun _ _ => rfl, hn, fun h => ?_, fun h => ?_⟩
  · exact hn (refinesWT_of_refinesPP (h.2 fun _ _ hf => by simp [Stmt.zeroPre] at hf))
  · exact hn (h.2 fun _ _ hf => by simp [Stmt.zeroPre] at hf)

/-- **Non-vacuity of the insertion characterizations, with `pre₀` failing.** Inserting
the zero-size read at alignment `4` in front of the identical read of `pReadZst4` under
`aligned`: `hz` holds, `pre₀` fails at a reachable state of the insertion point, the
source run from that point reaches UB with empty trace, and the insertion is a
prefix-preserving refinement. -/
theorem insertZstRead_before_failing_read_refinesPP :
    IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ReachableAt .aligned pReadZst4 0 0 (mkState [1]) ∧
      (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [1]) = false ∧
      GoesWrongFrom .aligned pReadZst4 (pReadZst4.at 0 0 (mkState [1])) [] ∧
      RefinesPP .aligned pReadZst4 (insertStmt pReadZst4 0 0 (.read (.var 0) ⟨0, 4⟩)) := by
  have hi : insertStmt pReadZst4 0 0 (.read (.var 0) ⟨0, 4⟩) = pTwoZstReads := by decide
  have hd : deleteStmt pTwoZstReads 0 0 = pReadZst4 := by decide
  have he := deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure.2.2.2
  rw [hd] at he
  rw [hi]
  exact ⟨by decide, reachableAt_entry _ _ _, by decide, ⟨1, rfl⟩, he.2⟩

/-- Non-vacuity of `insertZeroSizeAccess_equivPP_of_zeroPre_reachable`: inserting a
zero-size read into `pHalt` under `anyPtr` satisfies both hypotheses. -/
theorem insertZeroSizeAccess_anyPtr_nonvacuous :
    IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ∀ st, ReachableAt .anyPtr pHalt 0 0 st → (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .anyPtr st = true :=
  ⟨by decide, fun _ _ => rfl⟩

/-- **Materializing introduces UB.** Under the `aligned` contract, inserting a
zero-size read at alignment `4` through local `0` into `halt` is not even a whole-trace
refinement: on the input with local `0 = 1` the source terminates and the target
reaches UB. -/
theorem insertZstRead_misaligned_not_refinesWT :
    HasBeh .aligned pHalt (mkState [1]) (.term []) ∧
      HasBeh .aligned (insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩)) (mkState [1]) (.wrong []) ∧
      ¬ RefinesWT .aligned pHalt (insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩)) := by
  have hi : insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩) = pReadZst4 := by decide
  rw [hi]
  have hw : HasBeh .aligned pReadZst4 (mkState [1]) (.wrong []) := ⟨1, rfl⟩
  have ht : HasBeh .aligned pHalt (mkState [1]) (.term []) := ⟨1, _, rfl⟩
  exact ⟨ht, hw, not_refinesWT_of_term_wrong ht hw⟩

/-- **Counterexample for the hypothesis `hpre` of
`insertZeroSizeAccess_equivPP_of_zeroPre_reachable`.** Inserting the zero-size read at
alignment `4` into `halt` under `aligned`: `hz` holds, `pre₀` fails at a reachable
state, and the insertion is not a prefix-preserving equivalence. -/
theorem insertZeroSizeAccess_hpre_counterexample :
    IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ¬ (∀ st, ReachableAt .aligned pHalt 0 0 st →
        (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned st = true) ∧
      ¬ EquivPP .aligned pHalt (insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩)) := by
  refine ⟨by decide, fun h => ?_, fun h => ?_⟩
  · have := h (mkState [1]) (reachableAt_entry _ _ _)
    exact absurd this (by decide)
  · exact insertZstRead_misaligned_not_refinesWT.2.2 (refinesWT_of_refinesPP h.1)

/-- A branch on local `0`: value `0` goes to block `1`, which performs a zero-size
read at alignment `4` through local `1` and halts; otherwise block `2` halts. -/
def pBranchRead : Prog :=
  [⟨[], .switch 0 [(0, 1)] 2⟩, ⟨[.read (.var 1) ⟨0, 4⟩], .halt⟩, ⟨[], .halt⟩]

/-- `pBranchRead` with the read hoisted out of block `1` to the start of block `0`. -/
def pBranchReadHoisted : Prog :=
  deleteStmt (insertStmt pBranchRead 0 0 (.read (.var 1) ⟨0, 4⟩)) 1 0

theorem pBranchReadHoisted_eq :
    pBranchReadHoisted =
      [⟨[.read (.var 1) ⟨0, 4⟩], .switch 0 [(0, 1)] 2⟩, ⟨[], .halt⟩, ⟨[], .halt⟩] := by
  decide

/-- **Hoisting introduces UB.** Under the `aligned` contract, hoisting the zero-size
read of `pBranchRead` above the branch is not a whole-trace refinement: on the input
with locals `0 ↦ 5`, `1 ↦ 1` the source takes the other branch and terminates, while
the hoisted read through the misaligned pointer is UB. -/
theorem hoistZstRead_out_of_branch_not_refinesWT :
    HasBeh .aligned pBranchRead (mkState [5, 1]) (.term []) ∧
      HasBeh .aligned pBranchReadHoisted (mkState [5, 1]) (.wrong []) ∧
      ¬ RefinesWT .aligned pBranchRead pBranchReadHoisted := by
  have ht : HasBeh .aligned pBranchRead (mkState [5, 1]) (.term []) := ⟨2, _, rfl⟩
  have hw : HasBeh .aligned pBranchReadHoisted (mkState [5, 1]) (.wrong []) := by
    rw [pBranchReadHoisted_eq]
    exact ⟨1, rfl⟩
  exact ⟨ht, hw, not_refinesWT_of_term_wrong ht hw⟩

/-- **Positive control for hoisting: the same hoist is an equivalence under `anyPtr`.**
Under the contract `pre₀ = True` the hoisted zero-size read can never fail, and hoisting
it out of the branch of `pBranchRead` is a prefix-preserving equivalence. -/
theorem hoistZstRead_anyPtr_equivPP : EquivPP .anyPtr pBranchRead pBranchReadHoisted := by
  rw [pBranchReadHoisted_eq]
  refine equivPP_of_sameBeh fun σ b => ?_
  by_cases h : σ.locals 0 = 0
  · exact hasBeh_iff_of_runs_done (n := 3) (m := 3) (t := []) (s := σ) (s' := σ)
      (by simp_run [pBranchRead, h]) (by simp_run [h]) b
  · exact hasBeh_iff_of_runs_done (n := 2) (m := 3) (t := []) (s := σ) (s' := σ)
      (by simp_run [pBranchRead, h]) (by simp_run [h]) b

/-! ### Checking optimized programs for UB -/

/-- `ExactUBChecker K chk`: the Boolean verdict `chk P` is `true` exactly for the
programs that are `UBFree` under contract `K` (a perfect checker; the verdict and the
semantic property are distinct notions). -/
def ExactUBChecker (K : ZContract) (chk : Prog → Bool) : Prop :=
  ∀ P, chk P = true ↔ UBFree K P

/-- An exact checker exists (noncomputably), so statements quantifying over exact
checkers are not vacuous. -/
theorem exactUBChecker_exists (K : ZContract) : ∃ chk, ExactUBChecker K chk := by
  classical
  exact ⟨fun P => decide (UBFree K P), fun P => by simp⟩

/-- The constant-`true` checker is not exact. -/
theorem not_exactUBChecker_const_true (K : ZContract) : ¬ ExactUBChecker K (fun _ => true) :=
  fun h => not_ubFree_unreach K ((h pUnreach).1 rfl)

/-- **Checking the optimized program is incomplete for source UB.** The deletion pass
of `zstRead_misaligned_deletion_erases_ub` is a prefix-preserving refinement, and
every exact UB checker accepts its output, yet the source is not `UBFree`. -/
theorem ubCheck_of_output_misses_source_ub :
    RefinesPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) ∧
      ∀ chk, ExactUBChecker .aligned chk →
        chk (deleteStmt pReadZst4 0 0) = true ∧ ¬ UBFree .aligned pReadZst4 := by
  refine ⟨zstRead_misaligned_deletion_erases_ub.2.2.1, fun chk hchk => ⟨?_, ?_⟩⟩
  · rw [hchk, deleteStmt_pReadZst4]
    exact ubFree_halt _
  · intro h
    exact h _ _ zstRead_misaligned_deletion_erases_ub.1

/-- **UB found in the output of a refinement is UB of the source.** If the output
whole-trace-refines the source and the output is not `UBFree`, the source is not
`UBFree` (on the same input). This is the soundness half that the incompleteness of
`ubCheck_of_output_misses_source_ub` leaves intact. -/
theorem not_ubFree_src_of_not_ubFree_tgt_of_refinesWT (K : ZContract) (src tgt : Prog)
    (h : RefinesWT K src tgt) (htgt : ¬ UBFree K tgt) : ¬ UBFree K src := by
  intro hsrc
  apply htgt
  intro σ t ht
  obtain ⟨bs, hbs, himp⟩ := h σ _ ht
  rcases himp with h' | ⟨t', rfl⟩
  · exact hsrc σ t (h' ▸ hbs)
  · exact hsrc σ t' hbs

/-- **Positive control: a pass whose output the source refines.** If the source
whole-trace-refines the output (the reverse direction of the pass's refinement, as
in any whole-trace equivalence), then `UBFree` of the output implies `UBFree` of the
source. -/
theorem ubFree_src_of_ubFree_tgt_of_refinesWT_rev (K : ZContract) (src tgt : Prog)
    (hrev : RefinesWT K tgt src) (htgt : UBFree K tgt) : UBFree K src := by
  intro σ t hs
  obtain ⟨bt, hbt, himp⟩ := hrev σ _ hs
  rcases himp with h | ⟨t', rfl⟩
  · subst h
    exact htgt σ t hbt
  · exact htgt σ t' hbt

/-- A pipeline `P → Q₁ → … → Qₖ` in which every pass's input whole-trace-refines its
output (as for whole-trace equivalences). The empty list is the pipeline that runs no
pass. -/
def RevChainWT (K : ZContract) : Prog → List Prog → Prop
  | _, [] => True
  | P, Q :: Qs => RefinesWT K Q P ∧ RevChainWT K Q Qs

/-- The empty pipeline is a `RevChainWT`; a pass from `pUnreach` to `pHalt` is not (the
source `pUnreach` does not whole-trace-refine the output `pHalt`). -/
theorem revChainWT_examples (K : ZContract) :
    RevChainWT K pHalt [] ∧ ¬ RevChainWT K pUnreach [pHalt] :=
  ⟨trivial, fun h => not_refinesWT_halt_unreach K h.1⟩

/-- The empty pipeline is a `RevChainWT` from every program. -/
theorem revChainWT_nil (K : ZContract) (P : Prog) : RevChainWT K P [] := trivial

/-- A pass from `pUnreach` to `pHalt` is not a `RevChainWT`. -/
theorem not_revChainWT_unreach_halt (K : ZContract) : ¬ RevChainWT K pUnreach [pHalt] :=
  fun h => not_refinesWT_halt_unreach K h.1

/-- **Positive control for pipelines.** Along a pipeline in which each pass's input
whole-trace-refines its output (including the empty pipeline), `UBFree` of the final
output implies `UBFree` of the source. -/
theorem ubFree_src_of_ubFree_output_of_revChainWT (K : ZContract) :
    ∀ (P : Prog) (Qs : List Prog), RevChainWT K P Qs →
      UBFree K ((P :: Qs).getLast (List.cons_ne_nil _ _)) → UBFree K P := by
  intro P Qs
  induction Qs generalizing P with
  | nil => exact fun _ h => h
  | cons Q Qs ih =>
    intro hc h
    exact ubFree_src_of_ubFree_tgt_of_refinesWT_rev K P Q hc.1 (ih Q hc.2 h)

/-- **Reverse refinement does not make a pass a refinement.** The UB-introducing pass from
`pHalt` to `pUnreach` satisfies the reverse refinement hypothesis of the positive
controls (the source `pHalt` whole-trace-refines the output `pUnreach`), but the output
does not refine the source. -/
theorem revRefinement_admits_ub_introduction (K : ZContract) :
    RefinesWT K pUnreach pHalt ∧ ¬ RefinesWT K pHalt pUnreach :=
  ⟨refinesWT_of_refinesPP (refinesPP_of_src_unreach K pHalt), not_refinesWT_halt_unreach K⟩

/-- Corollary of the positive control for a prefix-preserving equivalence. -/
theorem ubFree_src_of_ubFree_tgt_of_equivPP (K : ZContract) (src tgt : Prog)
    (h : EquivPP K src tgt) (htgt : UBFree K tgt) : UBFree K src :=
  ubFree_src_of_ubFree_tgt_of_refinesWT_rev K src tgt (refinesWT_of_refinesPP h.2) htgt

/-- **Counterexample for the `UBFree` hypotheses of the three positive controls.** With
source and output both `pUnreach` (and for the empty pipeline from `pUnreach`), the
reverse refinement, the pipeline condition and the equivalence hold, but the output is
not `UBFree`, and neither is the source. -/
theorem ubFree_output_hypothesis_counterexample (K : ZContract) :
    RefinesWT K pUnreach pUnreach ∧ RevChainWT K pUnreach [] ∧ EquivPP K pUnreach pUnreach ∧
      ¬ UBFree K (([pUnreach] : List Prog).getLast (List.cons_ne_nil _ _)) ∧
      ¬ UBFree K pUnreach :=
  ⟨refinesWT_refl K pUnreach, trivial, ⟨refinesPP_refl K pUnreach, refinesPP_refl K pUnreach⟩,
    not_ubFree_unreach K, not_ubFree_unreach K⟩

/-- **Counterexample for the refinement hypotheses of the three positive controls.** For
the UB-erasing deletion of `zstRead_misaligned_deletion_erases_ub`, the output is
`UBFree` (also as the last program of the one-pass pipeline), but the source does not
whole-trace-refine the output, the one-pass pipeline is not a `RevChainWT`, the pass is
not a prefix-preserving equivalence, and the source is not `UBFree`. -/
theorem ubCheck_pReadZst4_hypotheses_counterexample :
    ¬ RefinesWT .aligned (deleteStmt pReadZst4 0 0) pReadZst4 ∧
      ¬ RevChainWT .aligned pReadZst4 [deleteStmt pReadZst4 0 0] ∧
      ¬ EquivPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) ∧
      UBFree .aligned (deleteStmt pReadZst4 0 0) ∧
      UBFree .aligned ((pReadZst4 :: [deleteStmt pReadZst4 0 0]).getLast (List.cons_ne_nil _ _)) ∧
      ¬ UBFree .aligned pReadZst4 := by
  have hneg := zstRead_misaligned_deletion_erases_ub
  have hrev : ¬ RefinesWT .aligned (deleteStmt pReadZst4 0 0) pReadZst4 :=
    not_refinesWT_of_term_wrong hneg.2.1 hneg.1
  have hout : UBFree .aligned (deleteStmt pReadZst4 0 0) := by
    rw [deleteStmt_pReadZst4]; exact ubFree_halt _
  exact ⟨hrev, fun h => hrev h.1, fun h => hneg.2.2.2 (equivWT_of_equivPP h), hout, hout,
    fun h => h _ _ hneg.1⟩

/-- An instance of the positive control: the `aligned`-contract deletion of the
alignment-`1` read is an equivalence with a `UBFree` output, and the source is
`UBFree`. -/
theorem ubFree_positive_control_instance :
    EquivPP .aligned pReadZst1 (deleteStmt pReadZst1 0 0) ∧
      UBFree .aligned (deleteStmt pReadZst1 0 0) ∧ UBFree .aligned pReadZst1 := by
  have he := zstRead_align_one_alignedContract_deletion_equivPP
  have ho : UBFree .aligned (deleteStmt pReadZst1 0 0) := by
    rw [deleteStmt_pReadZst1]; exact ubFree_halt _
  exact ⟨he, ho, ubFree_src_of_ubFree_tgt_of_equivPP _ _ _ he ho⟩

/-- Non-vacuity of the three positive controls: for the `aligned`-contract deletion of
the alignment-`1` read of `pReadZst1`, the source whole-trace-refines the output, the
one-pass pipeline is a `RevChainWT`, the pass is a prefix-preserving equivalence, and
the output is `UBFree` (also as the last program of the pipeline). -/
theorem ubFree_src_of_ubFree_tgt_nonvacuous :
    RefinesWT .aligned (deleteStmt pReadZst1 0 0) pReadZst1 ∧
      RevChainWT .aligned pReadZst1 [deleteStmt pReadZst1 0 0] ∧
      EquivPP .aligned pReadZst1 (deleteStmt pReadZst1 0 0) ∧
      UBFree .aligned (deleteStmt pReadZst1 0 0) ∧
      UBFree .aligned ((pReadZst1 :: [deleteStmt pReadZst1 0 0]).getLast (List.cons_ne_nil _ _)) := by
  have hpos := ubFree_positive_control_instance
  have hrev : RefinesWT .aligned (deleteStmt pReadZst1 0 0) pReadZst1 :=
    refinesWT_of_refinesPP hpos.1.2
  exact ⟨hrev, ⟨hrev, trivial⟩, hpos.1, hpos.2.1, hpos.2.1⟩

end Toy.ZstAssume
