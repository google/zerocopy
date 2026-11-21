import Toy.PlaceEval.Examples
import Toy.PlaceEval.EditSim

/-!
# Place computations are not free; erasing `placeMention`; equal-target `switchInt`;
`&raw` versus `&`

Concrete instances run under the deterministic example semantics `SEx`.
-/

namespace Toy.PlaceEval

/-! ## Behaviour sets of the concrete programs (all proved by evaluation) -/

theorem pDerefUninit_beh (b : Beh) : HasBeh SEx pDerefUninit b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pDerefUninit_erased_beh (b : Beh) :
    HasBeh SEx (deleteStmt pDerefUninit 0 2) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pDanglingRaw_two_beh (b : Beh) : HasBeh SEx (pDanglingRaw 2) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pDanglingRaw_zero_beh (b : Beh) : HasBeh SEx (pDanglingRaw 0) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pDanglingMention_two_beh (b : Beh) : HasBeh SEx (pDanglingMention 2) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pDanglingMention_two_erased_beh (b : Beh) :
    HasBeh SEx (deleteStmt (pDanglingMention 2) 0 3) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pDanglingMention_zero_beh (b : Beh) : HasBeh SEx (pDanglingMention 0) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pNull_zero_beh (b : Beh) : HasBeh SEx (pNull 0) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pNull_two_beh (b : Beh) : HasBeh SEx (pNull 2) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pMisaligned_beh (b : Beh) : HasBeh SEx pMisaligned b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pTwoMentions_beh (b : Beh) : HasBeh SEx pTwoMentions b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pTwoMentions_erased_beh (b : Beh) :
    HasBeh SEx (deleteStmt pTwoMentions 0 2) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwUninit_beh (b : Beh) : HasBeh SEx pSwUninit b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwUninit_goto_beh (b : Beh) : HasBeh SEx (setTerm pSwUninit 0 (.goto 1)) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwTag_two_beh (b : Beh) : HasBeh SEx (pSwTag 2) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwTag_two_goto_beh (b : Beh) :
    HasBeh SEx (setTerm (pSwTag 2) 0 (.goto 1)) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwTag_one_beh (b : Beh) : HasBeh SEx (pSwTag 1) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwTag_one_goto_beh (b : Beh) :
    HasBeh SEx (setTerm (pSwTag 1) 0 (.goto 1)) b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pRawDangling_beh (b : Beh) : HasBeh SEx pRawDangling b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pRefDangling_beh (b : Beh) : HasBeh SEx pRefDangling b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pRawPacked_beh (b : Beh) : HasBeh SEx pRawPacked b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pRawPacked_ref_beh (b : Beh) :
    HasBeh SEx (setStmt pRawPacked 0 0 refPackedStmt) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

theorem setStmt_pRawDangling_ref : setStmt pRawDangling 0 3 refDerefStmt = pRefDangling := by
  decide
theorem setStmt_pRefDangling_raw : setStmt pRefDangling 0 3 rawDerefStmt = pRawDangling := by
  decide

/-! ## Place computations are not free -/

/-- **Place computation can be UB.** Under `SEx`: `placeMention (*(*pp))` with `*pp`
uninitialized is UB (the intermediate `deref` load); `r := &raw (*p).field 2` with `p`
dangling (freed allocation) is UB (a non-zero offset not in bounds); and
`r := &raw (*p).field 2` with `p` null is UB. -/
theorem place_computation_not_free :
    (∀ b, HasBeh SEx pDerefUninit b ↔ b = .wrong []) ∧
    (∀ b, HasBeh SEx (pDanglingRaw 2) b ↔ b = .wrong []) ∧
    (∀ b, HasBeh SEx (pNull 2) b ↔ b = .wrong []) :=
  ⟨pDerefUninit_beh, pDanglingRaw_two_beh, pNull_two_beh⟩

/-- **Positive control (zero offset, bare `deref`).** Under `SEx`: `r := &raw (*p).field 0`
and `placeMention ((*p).field 0)` are UB-free for a dangling `p`; `placeMention (*p)` and
`r := &raw (*p).field 0` are UB-free for a null `p` and for a misaligned `p` with
provenance. -/
theorem place_computation_zero_offset_and_bare_deref_ok :
    (∀ b, HasBeh SEx (pDanglingRaw 0) b ↔ b = .term []) ∧
    (∀ b, HasBeh SEx (pDanglingMention 0) b ↔ b = .term []) ∧
    (∀ b, HasBeh SEx (pNull 0) b ↔ b = .term []) ∧
    (∀ b, HasBeh SEx pMisaligned b ↔ b = .term []) :=
  ⟨pDanglingRaw_zero_beh, pDanglingMention_zero_beh, pNull_zero_beh, pMisaligned_beh⟩

/-! ## Erasing `placeMention` -/

/-- **`placeMention` erasure refines.** Deleting a `placeMention p` statement (at block
`l`, index `i`) gives a prefix-preserving refinement of the source, under every semantics
`S` (fresh addresses or any static slot assignment). -/
theorem erasePlaceMention_refinesPP (S : Sem) (P : Prog) (l : Label) (i : Nat) (p : Place)
    (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    RefinesPP S P (deleteStmt P l i) :=
  deleteStmt_refinesPP S hs

/-- **Sufficient condition for equivalence.** If evaluating `p` succeeds in every state in
which `(l, i)` is reachable, deleting `placeMention p` there is a prefix-preserving
equivalence, under every semantics `S`. -/
theorem erasePlaceMention_equivPP_of_evalPlace_reachable (S : Sem) (P : Prog) (l : Label)
    (i : Nat) (p : Place) (hs : (P.blk l).stmts[i]? = some (.placeMention p))
    (hok : ∀ st, ReachableAt S P l i st → (evalPlace st p).isSome = true) :
    EquivPP S P (deleteStmt P l i) :=
  ⟨deleteStmt_refinesPP S hs, deleteStmt_rev_refinesPP S hs fun ω st0 st h0 ⟨n, t, hn⟩ hnone => by
    have := hok st ⟨ω, st0, n, t, h0, hn⟩
    rw [hnone] at this
    cases this⟩

/-- **Exact condition for equivalence (static slot assignment).** Under the deterministic
semantics `slots s`, deleting `placeMention p` at `(l, i)` is a prefix-preserving
equivalence iff for every reachable state at `(l, i)` in which evaluating `p` is UB, the
target run from the point after the deleted statement reaches UB before emitting any
event. -/
theorem erasePlaceMention_equivPP_iff_slots (s : Local → Nat) (P : Prog) (l : Label)
    (i : Nat) (p : Place) (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    EquivPP (.slots s) P (deleteStmt P l i) ↔
      ∀ st, ReachableAt (.slots s) P l i st → evalPlace st p = none →
        GoesWrongFrom (.slots s) (deleteStmt P l i) ((deleteStmt P l i).at l i st) [] := by
  obtain ⟨_, hdrop, _, hout, hloc, hmark⟩ := deleteStmt_facts hs
  constructor
  · intro hEq st hreach hnone
    obtain ⟨ω, st0, n, t, h0, hrun⟩ := hreach
    simp only [Sem.mode] at h0 hrun
    have hstepP : step (.slots s) P (P.at l i st) = .ub := by
      simp only [Prog.at]; rw [hdrop]; simp [step, execStmt, hnone]
    have hPub : run (.slots s) P (n + 1) (P.entry 0 st0) = .ub t := by
      rw [run_add_running n 1 _ _ t hrun, run_succ_ub 0 hstepP]; simp [Outcome.app]
    obtain ⟨bs, ⟨ω', st0', h0', hbs⟩, himp⟩ := hEq.2 (.wrong t) ⟨ω, st0, h0, n + 1, hPub⟩
    have hu : ∃ u, bs = .wrong u ∧ u <+: t := by
      rcases himp with rfl | ⟨u, rfl, hu⟩
      · exact ⟨t, rfl, List.prefix_refl t⟩
      · exact ⟨u, rfl, hu⟩
    obtain ⟨u, rfl, hu⟩ := hu
    obtain ⟨m', hm'⟩ := hbs
    simp only [Sem.mode] at h0' hm'
    rw [initState_congr hloc hmark, h0] at h0'
    cases h0'
    obtain ⟨m, cs', hm, hR⟩ := reach_of_simU (deleteStmt_rev_stepSimU (.slots s) hs) n _ _ _ t
      (bRel_entry (fun l' h => (hout l' h).symm) (deleteStmt_entryRel hs) 0 st0) hrun
    have hcs := deleteStmt_rev_at hs hR
    subst hcs
    rw [deleteStmt_at hs]
    obtain ⟨k, hk⟩ := srcUB_of_ub_prefix hm hm' hu
    exact ⟨ω, k, hk⟩
  · intro hc
    refine ⟨deleteStmt_refinesPP _ hs,
      deleteStmt_rev_refinesPP _ hs fun ω st0 st h0 ⟨n, t, hn⟩ hnone => ?_⟩
    obtain ⟨ω', k, hk⟩ := hc st ⟨ω, st0, n, t, h0, hn⟩ hnone
    rw [deleteStmt_at hs] at hk
    exact ⟨k, hk⟩

/-- The initial state of `P` under `SEx` (a dummy state if the entry allocations were
refused, which never happens under `slots`). -/
def initEx (P : Prog) : State := (P.initState (.slots sEx)).getD ⟨⟨[], []⟩, []⟩

/-- The state reached in `pTwoMentions` before its first `placeMention`. -/
def stTwoMentions : State :=
  match runFromInit (.slots sEx) pTwoMentions 2 with
  | .running c _ => c.st
  | _ => ⟨⟨[], []⟩, []⟩

/-- **The UB-freedom condition is not necessary for equivalence.** In `pTwoMentions`
(two identical `placeMention (*(*pp))` with `*pp` uninitialized), evaluation of the first
fails at a reachable state, yet deleting it is an equivalence under `SEx`: the second
reaches the same UB with the same (empty) trace. -/
theorem erasePlaceMention_equivPP_despite_reachable_failure :
    (∃ st, ReachableAt SEx pTwoMentions 0 2 st ∧ evalPlace st ⟨0, [.deref, .deref]⟩ = none) ∧
      EquivPP SEx pTwoMentions (deleteStmt pTwoMentions 0 2) := by
  refine ⟨⟨stTwoMentions, ⟨fun _ => 0, initEx pTwoMentions, 2, [], by decide, by decide⟩, by decide⟩, ?_, ?_⟩
  · exact (refinesAcross_iff_of_beh pTwoMentions_beh pTwoMentions_erased_beh).2
      (improvesPP_refl _)
  · exact (refinesAcross_iff_of_beh pTwoMentions_erased_beh pTwoMentions_beh).2
      (improvesPP_refl _)

/-- **Erasure erases place-evaluation UB.** Under `SEx`, deleting the failing
`placeMention (*(*pp))` of `pDerefUninit`, and the failing `placeMention ((*p).field 2)` of
`pDanglingMention 2`, each gives a refinement that is not an equivalence: the source is UB,
the target terminates. -/
theorem erasePlaceMention_erases_place_ub :
    ((pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) ∧
      RefinesPP SEx pDerefUninit (deleteStmt pDerefUninit 0 2) ∧
      ¬ RefinesPP SEx (deleteStmt pDerefUninit 0 2) pDerefUninit) ∧
    (((pDanglingMention 2).blk 0).stmts[3]? = some (.placeMention ⟨0, [.deref, .field 2]⟩) ∧
      RefinesPP SEx (pDanglingMention 2) (deleteStmt (pDanglingMention 2) 0 3) ∧
      ¬ RefinesPP SEx (deleteStmt (pDanglingMention 2) 0 3) (pDanglingMention 2)) := by
  refine ⟨⟨by decide, ?_, ?_⟩, by decide, ?_, ?_⟩
  · exact (refinesAcross_iff_of_beh pDerefUninit_beh pDerefUninit_erased_beh).2
      (improvesPP_wrong_nil _)
  · rw [refinesPP_iff_of_beh pDerefUninit_erased_beh pDerefUninit_beh]
    exact improvesPP_ex_neg_ub
  · exact (refinesAcross_iff_of_beh pDanglingMention_two_beh pDanglingMention_two_erased_beh).2
      (improvesPP_wrong_nil _)
  · rw [refinesPP_iff_of_beh pDanglingMention_two_erased_beh pDanglingMention_two_beh]
    exact improvesPP_ex_neg_ub

/-- **A UB check after erasure misses place-evaluation UB.** Every exact UB checker
(for `SEx`) accepts the erased `pDerefUninit`, although the source is not UB-free. -/
theorem ubCheck_after_erasePlaceMention_misses_place_ub :
    (pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) ∧
      UBFree SEx (deleteStmt pDerefUninit 0 2) ∧ ¬ UBFree SEx pDerefUninit ∧
      ∀ chk, ExactUBChecker SEx chk → chk (deleteStmt pDerefUninit 0 2) = true := by
  have hfree : UBFree SEx (deleteStmt pDerefUninit 0 2) := by
    intro t ht
    have := (pDerefUninit_erased_beh _).1 ht
    cases this
  exact ⟨by decide, hfree, fun h => h [] ((pDerefUninit_beh _).2 rfl),
    fun chk hchk => (hchk _).2 hfree⟩

/-- **Outside place-evaluation UB at the erased statement, the check is complete.** If
evaluating `p` succeeds at every reachable state at `(l, i)`, UB-freedom of the program with
`placeMention p` deleted implies UB-freedom of the source. -/
theorem ubFree_of_ubFree_erasePlaceMention_of_evalPlace_reachable (S : Sem) (P : Prog)
    (l : Label) (i : Nat) (p : Place) (hs : (P.blk l).stmts[i]? = some (.placeMention p))
    (hok : ∀ st, ReachableAt S P l i st → (evalPlace st p).isSome = true)
    (htgt : UBFree S (deleteStmt P l i)) : UBFree S P :=
  ubFree_of_refinesPP_rev (erasePlaceMention_equivPP_of_evalPlace_reachable S P l i p hs hok).2
    htgt

/-! ## Erasing an equal-target `switchInt` -/

/-- Decoding at an integer type yields `n` iff the cells are bytes encoding `n`. -/
theorem decode_int_eq_some_iff (s a : Nat) (cs : List Cell) (n : Nat) :
    (Ty.int s a).decode cs = some (.int n) ↔ decodeLE cs = some n := by
  simp only [Ty.decode]
  cases decodeLE cs <;> simp

/-- Decoding at an enum type yields `n` iff the cells are bytes encoding `n` and `n` is a
valid tag. -/
theorem decode_enum_eq_some_iff (s a : Nat) (valid : List Nat) (cs : List Cell) (n : Nat) :
    (Ty.enum s a valid).decode cs = some (.int n) ↔ decodeLE cs = some n ∧ n ∈ valid := by
  simp only [Ty.decode]
  cases h : decodeLE cs with
  | none => simp
  | some m =>
    simp only [Option.some.injEq]
    constructor
    · intro h2
      by_cases hm : m ∈ valid
      · simp only [hm, ↓reduceIte, Option.some.injEq, Val.int.injEq] at h2
        exact ⟨h2, h2 ▸ hm⟩
      · simp only [hm, ↓reduceIte, reduceCtorEq] at h2
    · rintro ⟨rfl, hm⟩
      simp [hm]

/-- **UB conditions of the switch operand.** Evaluating `copy p τ` to an integer fails iff
place evaluation fails (`evalPlace_eq_none_iff`), or the resulting pointer `q` is not dereferenceable for
`τ.size` bytes, or not aligned for `τ.align`, or the cells do not decode to an integer at
`τ` (for an integer type: some byte uninitialized or a pointer fragment; for an enum: that,
or a tag outside `valid`, by `decode_enum_eq_some_iff`). -/
theorem evalInt_copy_eq_none_iff (st : State) (p : Place) (τ : Ty) :
    (Operand.copy p τ).evalInt st = none ↔
      evalPlace st p = none ∨
        ∃ q, evalPlace st p = some q ∧
          (st.mem.dereferenceable q τ.size = false ∨ aligned τ.align q.addr = false ∨
            ∀ n, τ.decode (st.mem.readCells q.addr τ.size) ≠ some (.int n)) := by
  simp only [Operand.evalInt, Operand.eval]
  cases hp : evalPlace st p with
  | none => simp
  | some q =>
    simp only [Option.bind_some, reduceCtorEq, false_or, Option.some.injEq, exists_eq_left']
    unfold Mem.load
    by_cases hd : st.mem.dereferenceable q τ.size = true
    · by_cases ha : aligned τ.align q.addr = true
      · simp only [hd, ha, Bool.and_self, ↓reduceIte, Bool.true_eq_false, false_or]
        cases hdec : τ.decode (st.mem.readCells q.addr τ.size) with
        | none => simp
        | some v =>
          cases v with
          | int n => simp
          | ptr r => simp
      · simp [hd, ha]
    · simp [hd]

/-- **Equal-target switch erasure refines.** Replacing a `switchInt o arms b` whose arms
all target `b` (the `otherwise` label is `b` too) by `goto b` gives a prefix-preserving
refinement, under every semantics `S`. -/
theorem switchToGoto_refinesPP (S : Sem) (P : Prog) (l : Label) (o : Operand)
    (arms : List (Nat × Label)) (b : Label) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b) :
    RefinesPP S P (setTerm P l (.goto b)) :=
  setTerm_refinesPP S ht hall

/-- **Sufficient condition for equivalence.** If the operand evaluates to an integer in
every reachable state at the switch, the replacement is a prefix-preserving equivalence,
under every semantics `S`. -/
theorem switchToGoto_equivPP_of_operand_reachable (S : Sem) (P : Prog) (l : Label)
    (o : Operand) (arms : List (Nat × Label)) (b : Label)
    (ht : (P.blk l).term = .switchInt o arms b) (hall : ∀ a ∈ arms, a.2 = b)
    (hok : ∀ st, ReachableAt S P l (P.blk l).stmts.length st → (o.evalInt st).isSome = true) :
    EquivPP S P (setTerm P l (.goto b)) :=
  ⟨setTerm_refinesPP S ht hall, setTerm_rev_refinesPP S ht hall fun ω st0 st h0 ⟨n, t, hn⟩ hnone => by
    have := hok st ⟨ω, st0, n, t, h0, by simp only [Prog.at, List.drop_length]; exact hn⟩
    rw [hnone] at this
    cases this⟩

/-- **Exact condition for equivalence (static slot assignment).** Under `slots s`, the
replacement is a prefix-preserving equivalence iff for every reachable state at the
switch in which the operand does not evaluate to an integer, the target run from the entry
of `b` reaches UB before emitting any event. -/
theorem switchToGoto_equivPP_iff_slots (s : Local → Nat) (P : Prog) (l : Label)
    (o : Operand) (arms : List (Nat × Label)) (b : Label)
    (ht : (P.blk l).term = .switchInt o arms b) (hall : ∀ a ∈ arms, a.2 = b) :
    EquivPP (.slots s) P (setTerm P l (.goto b)) ↔
      ∀ st, ReachableAt (.slots s) P l (P.blk l).stmts.length st → o.evalInt st = none →
        GoesWrongFrom (.slots s) (setTerm P l (.goto b)) ((setTerm P l (.goto b)).entry b st) [] := by
  obtain ⟨hblk, hout, hloc, hmark⟩ := setTerm_facts ht
  constructor
  · intro hEq st hreach hnone
    obtain ⟨ω, st0, n, t, h0, hrun⟩ := hreach
    simp only [Sem.mode, Prog.at, List.drop_length] at h0 hrun
    have hstepP : step (.slots s) P ⟨l, [], st⟩ = .ub := by simp [step, ht, hnone]
    have hPub : run (.slots s) P (n + 1) (P.entry 0 st0) = .ub t := by
      rw [run_add_running n 1 _ _ t hrun, run_succ_ub 0 hstepP]; simp [Outcome.app]
    obtain ⟨bs, ⟨ω', st0', h0', hbs⟩, himp⟩ := hEq.2 (.wrong t) ⟨ω, st0, h0, n + 1, hPub⟩
    have hu : ∃ u, bs = .wrong u ∧ u <+: t := by
      rcases himp with rfl | ⟨u, rfl, hu⟩
      · exact ⟨t, rfl, List.prefix_refl t⟩
      · exact ⟨u, rfl, hu⟩
    obtain ⟨u, rfl, hu⟩ := hu
    obtain ⟨m', hm'⟩ := hbs
    simp only [Sem.mode] at h0' hm'
    rw [initState_congr hloc hmark, h0] at h0'
    cases h0'
    obtain ⟨m, cs', hm, hR⟩ := reach_of_simU (setTerm_rev_stepSimU (.slots s) ht hall) n _ _ _ t
      (bRel_entry (fun l' h => (hout l' h).symm) (by simp only [hblk]) 0 st0) hrun
    have hcs : cs' = ⟨l, [], st⟩ := by
      obtain ⟨lbl, r, st'⟩ := cs'
      obtain ⟨h1, h2, _, h4⟩ := hR
      simp only at h1 h2 h4
      subst h1 h2
      rw [h4 rfl]
    subst hcs
    have hstepP' : step (.slots s) (setTerm P l (.goto b)) ⟨l, [], st⟩ =
        .next none ((setTerm P l (.goto b)).entry b st) := by simp [step, hblk]
    have hm1 := run_succ_of_running hm hstepP'
    simp only [Option.toList, List.append_nil] at hm1
    obtain ⟨k, hk⟩ := srcUB_of_ub_prefix hm1 hm' hu
    exact ⟨ω, k, hk⟩
  · intro hc
    refine ⟨setTerm_refinesPP _ ht hall,
      setTerm_rev_refinesPP _ ht hall fun ω st0 st h0 ⟨n, t, hn⟩ hnone => ?_⟩
    obtain ⟨ω', k, hk⟩ := hc st ⟨ω, st0, n, t, h0, by simp only [Prog.at, List.drop_length]; exact hn⟩
      hnone
    exact ⟨k, hk⟩

/-- **Switch erasure erases operand UB.** Under `SEx`, replacing the equal-target switch by
`goto 1` in `pSwUninit` (operand uninitialized) and in `pSwTag 2` (operand holds the
invalid tag `2` of `bool2`) gives a refinement that is not an equivalence. -/
theorem switchToGoto_erases_operand_ub :
    ((pSwUninit.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1 ∧
      RefinesPP SEx pSwUninit (setTerm pSwUninit 0 (.goto 1)) ∧
      ¬ RefinesPP SEx (setTerm pSwUninit 0 (.goto 1)) pSwUninit) ∧
    (((pSwTag 2).blk 0).term = .switchInt (.copy ⟨0, []⟩ bool2) [(0, 1)] 1 ∧
      RefinesPP SEx (pSwTag 2) (setTerm (pSwTag 2) 0 (.goto 1)) ∧
      ¬ RefinesPP SEx (setTerm (pSwTag 2) 0 (.goto 1)) (pSwTag 2)) ∧
    (∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1) := by
  refine ⟨⟨by decide, ?_, ?_⟩, ⟨by decide, ?_, ?_⟩, by decide⟩
  · exact (refinesAcross_iff_of_beh pSwUninit_beh pSwUninit_goto_beh).2 (improvesPP_wrong_nil _)
  · rw [refinesPP_iff_of_beh pSwUninit_goto_beh pSwUninit_beh]
    exact improvesPP_ex_neg_ub
  · exact (refinesAcross_iff_of_beh pSwTag_two_beh pSwTag_two_goto_beh).2 (improvesPP_wrong_nil _)
  · rw [refinesPP_iff_of_beh pSwTag_two_goto_beh pSwTag_two_beh]
    exact improvesPP_ex_neg_ub

/-- **Positive control: a valid tag.** For `pSwTag 1` (tag `1` is valid) the replacement is
an equivalence under `SEx`. -/
theorem switchToGoto_validTag_equivPP : EquivPP SEx (pSwTag 1) (setTerm (pSwTag 1) 0 (.goto 1)) :=
  ⟨(refinesAcross_iff_of_beh pSwTag_one_beh pSwTag_one_goto_beh).2 (improvesPP_refl _),
   (refinesAcross_iff_of_beh pSwTag_one_goto_beh pSwTag_one_beh).2 (improvesPP_refl _)⟩

/-! ## `&raw` versus `&` -/

/-- **`&raw p` is UB exactly when evaluating `p` is.** -/
theorem rawRef_eval_eq_none_iff (st : State) (p : Place) :
    (Rvalue.rawRef p).eval st = none ↔ evalPlace st p = none := by
  simp [Rvalue.eval]

/-- **`&p` additionally requires `RefOk`.** `&p` (pointee layout `L`) is UB exactly when
evaluating `p` is UB, or the resulting pointer is null, misaligned for `L.align`, or not
dereferenceable for `L.size` bytes. -/
theorem ref_eval_eq_none_iff (st : State) (p : Place) (L : Layout) :
    (Rvalue.ref p L).eval st = none ↔
      evalPlace st p = none ∨ ∃ q, evalPlace st p = some q ∧ ¬ RefOk st.mem q L := by
  simp only [Rvalue.eval]
  cases evalPlace st p with
  | none => simp
  | some q =>
    by_cases h : RefOk st.mem q L <;> simp [h]

/-- **Rewriting `&` to `&raw` refines.** Replacing a statement `dst := &p` (pointee layout
`L`) by `dst := &raw p` gives a prefix-preserving refinement, under every semantics `S`. -/
theorem refToRaw_refinesPP (S : Sem) (P : Prog) (l : Label) (i : Nat) (dst : Place) (τ : Ty)
    (p : Place) (L : Layout) (hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))) :
    RefinesPP S P (setStmt P l i (.assign dst τ (.rawRef p))) :=
  setStmt_ref_refinesPP S hs

/-- **Neither rewrite is an equivalence.** Under `SEx`: rewriting `&raw (*p)` to `&(*p)` for
a dangling `p`, and `&raw (s.b)` to `&(s.b)` for an under-aligned packed field, are not
refinements (they introduce UB); rewriting `&(*p)` to `&raw (*p)` for a dangling `p` is a
refinement but not an equivalence (it erases UB). -/
theorem raw_ref_rewrites_not_equivalences :
    ¬ RefinesPP SEx pRawDangling (setStmt pRawDangling 0 3 refDerefStmt) ∧
    ¬ RefinesPP SEx pRawPacked (setStmt pRawPacked 0 0 refPackedStmt) ∧
    RefinesPP SEx pRefDangling (setStmt pRefDangling 0 3 rawDerefStmt) ∧
    ¬ RefinesPP SEx (setStmt pRefDangling 0 3 rawDerefStmt) pRefDangling := by
  rw [setStmt_pRawDangling_ref, setStmt_pRefDangling_raw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [refinesPP_iff_of_beh pRawDangling_beh pRefDangling_beh]
    rintro (h | ⟨t, h, _⟩) <;> cases h
  · rw [refinesPP_iff_of_beh pRawPacked_beh pRawPacked_ref_beh]
    rintro (h | ⟨t, h, _⟩) <;> cases h
  · exact (refinesAcross_iff_of_beh pRefDangling_beh pRawDangling_beh).2 (improvesPP_wrong_nil _)
  · rw [refinesPP_iff_of_beh pRawDangling_beh pRefDangling_beh]
    rintro (h | ⟨t, h, _⟩) <;> cases h

end Toy.PlaceEval
