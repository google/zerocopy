import ToyTailCall.Machine
import ToyTailCall.Borrow
import ToyTailCall.Inline
import ToyTailCall.Layout
import ToyTailCall.Examples

/-!
# Counterexamples, non-vacuity witnesses and positive controls (all fully proved)
-/

namespace Toy.TailCall

/-! ### Frame reuse versus call-then-return and pre-jump finalization -/

/-- Even with `NoStackBorrow`, `frameReuse` does not refine `callReturn`: in `dtorProg` the
caller's local is dropped after the callee's event under `callReturn` and before it under
`frameReuse`. -/
theorem frameReuse_ne_callReturn_dtorProg :
    NoStackBorrow dtorProg ∧
      Observes .callReturn none dtorProg (.returned 0) [.out 1, .drop 7] ∧
      Observes .frameReuse none dtorProg (.returned 0) [.drop 7, .out 1] ∧
      ¬ Observes .frameReuse none dtorProg (.returned 0) [.out 1, .drop 7] :=
  ⟨noStackBorrow_dtorProg, ⟨_, dtorProg_callReturn, rfl, rfl⟩, ⟨_, dtorProg_frameReuse, rfl, rfl⟩,
    not_observes_dtorProg_frameReuse_callReturnTrace⟩

theorem borrowProg_preJump : RunsTo .preJump none borrowProg ⟨.returned 5, [], 3, 1⟩ :=
  ⟨20, by decide⟩

theorem borrowProg_frameReuse : RunsTo .frameReuse none borrowProg ⟨.ub, [], 2, 1⟩ :=
  ⟨20, by decide⟩

/-- Without `NoStackBorrow` the equivalence fails: `become reader(&local)` loads through a
popped slot (`ub`) under `frameReuse` and returns `5` under `preJump`. -/
theorem frameReuse_iff_preJump_fails_borrowProg :
    ¬ NoStackBorrow borrowProg ∧
      Observes .preJump none borrowProg (.returned 5) [] ∧
      Observes .frameReuse none borrowProg .ub [] ∧
      ¬ (∀ o es, Observes .frameReuse none borrowProg o es ↔ Observes .preJump none borrowProg o es) := by
  refine ⟨not_noStackBorrow_borrowProg, ⟨_, borrowProg_preJump, rfl, rfl⟩,
    ⟨_, borrowProg_frameReuse, rfl, rfl⟩, fun h => ?_⟩
  have h1 := (h (.returned 5) []).2 ⟨_, borrowProg_preJump, rfl, rfl⟩
  rw [observes_iff_of_runsTo borrowProg_frameReuse] at h1
  exact absurd h1.1 (by decide)

theorem ignorePtrProg_frameReuse : RunsTo .frameReuse none ignorePtrProg ⟨.returned 0, [], 2, 1⟩ :=
  ⟨20, by decide⟩

theorem ignorePtrProg_preJump : RunsTo .preJump none ignorePtrProg ⟨.returned 0, [], 3, 1⟩ :=
  ⟨20, by decide⟩

/-- `NoStackBorrow` is sufficient but not necessary for the equivalence: `ignorePtrProg` passes
a pointer into the current frame (so `NoStackBorrow` fails), but the callee never loads
through it, and the two semantics have the same outcomes and traces. -/
theorem noStackBorrow_not_necessary_ignorePtrProg :
    ¬ NoStackBorrow ignorePtrProg ∧
      ∀ o es, Observes .frameReuse none ignorePtrProg o es ↔ Observes .preJump none ignorePtrProg o es := by
  refine ⟨fun h => ?_, fun o es => ?_⟩
  · have h2 := h 2 _ rfl
    revert h2
    decide
  · rw [observes_iff_of_runsTo ignorePtrProg_frameReuse, observes_iff_of_runsTo ignorePtrProg_preJump]

/-- Without `NoStackBorrow` the bounded transfer fails (here with `D = none`). -/
theorem frameReuse_of_preJump_fails_borrowProg :
    ¬ NoStackBorrow borrowProg ∧ (.returned 5 : Outcome) ≠ .stackOverflow ∧
      Observes .preJump none borrowProg (.returned 5) [] ∧
      ¬ Observes .frameReuse none borrowProg (.returned 5) [] := by
  refine ⟨not_noStackBorrow_borrowProg, by decide, ⟨_, borrowProg_preJump, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo borrowProg_frameReuse]
  decide

theorem noStackBorrow_countUp3 : NoStackBorrow (countUp 3) :=
  noStackBorrow_of_allRunning _ 40 (by decide)

theorem countUp3_bound4_preJump : RunsTo .preJump (some 4) (countUp 3)
    ⟨.stackOverflow, [.drop 0, .drop 1, .drop 2], 4, 2⟩ := ⟨40, by decide⟩

theorem countUp3_bound4_frameReuse : RunsTo .frameReuse (some 4) (countUp 3)
    ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 2, 3⟩ := ⟨40, by decide⟩

/-- The non-overflow restriction of the bounded transfer is needed: with bound `4`,
`countUp 3` overflows under `preJump` (after finalizing three frames) but returns under
`frameReuse`. -/
theorem frameReuse_of_preJump_fails_for_overflow_countUp3 :
    NoStackBorrow (countUp 3) ∧
      Observes .preJump (some 4) (countUp 3) .stackOverflow [.drop 0, .drop 1, .drop 2] ∧
      ¬ Observes .frameReuse (some 4) (countUp 3) .stackOverflow [.drop 0, .drop 1, .drop 2] := by
  refine ⟨noStackBorrow_countUp3, ⟨_, countUp3_bound4_preJump, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo countUp3_bound4_frameReuse]
  decide

/-- With bound `0` the initial push of `countUp 3` already overflows. -/
theorem countUp3_bound0_overflows :
    RunsTo .preJump (some 0) (countUp 3) ⟨.stackOverflow, [], 0, 0⟩ ∧
      RunsTo .frameReuse (some 0) (countUp 3) ⟨.stackOverflow, [], 0, 0⟩ :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

/-- With bound `0`, for every program satisfying `EntryOk` (the entry function exists and takes
no parameters) and under every semantics, the initial push overflows: the run halts with
`stackOverflow`, an empty trace and depth `0`. So for such programs the bounded transfer has no
premise with an outcome other than `stackOverflow`. -/
theorem runsTo_bound0_of_entryOk (sem : Sem) (p : Prog) (h : EntryOk p) :
    RunsTo sem (some 0) p ⟨.stackOverflow, [], 0, 0⟩ := by
  obtain ⟨fn, hfn, hnp⟩ := h
  exact ⟨0, by simp [run, start, push, hfn, hnp, overflows, State.empty, State.halt]⟩

/-- Without `EntryOk`, a bound of `0` need not produce `stackOverflow`: the entry function of
`paramEntryProg` takes one parameter, so `push` halts with `ub` (arity is checked before the
bound) under both semantics. -/
theorem paramEntryProg_bound0_ub :
    Observes .preJump (some 0) paramEntryProg .ub [] ∧
      Observes .frameReuse (some 0) paramEntryProg .ub [] :=
  ⟨⟨⟨.ub, [], 0, 0⟩, ⟨1, by decide⟩, rfl, rfl⟩, ⟨⟨.ub, [], 0, 0⟩, ⟨1, by decide⟩, rfl, rfl⟩⟩

/-- Non-vacuity of the bounded transfer: all hypotheses and its premise hold for `countUp 3`
with bound `5`. -/
theorem frameReuse_of_preJump_nonvacuous_countUp3 :
    NoStackBorrow (countUp 3) ∧ (.returned 0 : Outcome) ≠ .stackOverflow ∧
      Observes .preJump (some 5) (countUp 3) (.returned 0) [.drop 0, .drop 1, .drop 2] :=
  ⟨noStackBorrow_countUp3, by decide,
    ⟨⟨.returned 0, [.drop 0, .drop 1, .drop 2], 5, 3⟩, ⟨40, by decide⟩, rfl, rfl⟩⟩

/-- Non-vacuity of the unbounded equivalence: `dtorProg` satisfies `NoStackBorrow` and both
semantics produce the same outcome and trace. -/
theorem frameReuse_iff_preJump_nonvacuous_dtorProg :
    NoStackBorrow dtorProg ∧
      Observes .frameReuse none dtorProg (.returned 0) [.drop 7, .out 1] ∧
      Observes .preJump none dtorProg (.returned 0) [.drop 7, .out 1] :=
  ⟨noStackBorrow_dtorProg, ⟨_, dtorProg_frameReuse, rfl, rfl⟩, ⟨_, dtorProg_preJump, rfl, rfl⟩⟩

/-! ### Self-tail-recursion instances (`N = 3`) -/

theorem countUp3_frameReuse : RunsTo .frameReuse none (countUp 3)
    ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 2, 3⟩ := ⟨16, by decide⟩

theorem countUp3_preJump : RunsTo .preJump none (countUp 3)
    ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 5, 3⟩ := ⟨19, by decide⟩

theorem countUp3_callReturn : RunsTo .callReturn none (countUp 3)
    ⟨.returned 0, [.drop 2, .drop 1, .drop 0], 5, 3⟩ := ⟨19, by decide⟩

/-- Pre-jump finalization order in a full run: locals `14`, `12` (slot `13` was moved into the
argument), then parameters `11`, `10`, all before the callee's `out 99`; the moved value is
dropped by the callee. -/
theorem orderDemo_frameReuse : RunsTo .frameReuse none orderDemo
    ⟨.returned 0, [.drop 14, .drop 12, .drop 11, .drop 10, .out 99, .drop 13], 2, 1⟩ :=
  ⟨20, by decide⟩

/-! ### Call-free chains -/

theorem chain3_frameReuse : RunsTo .frameReuse none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ :=
  ⟨20, by decide⟩

theorem chain3_preJump : RunsTo .preJump none chain3 ⟨.returned 0, [.out 1], 3, 2⟩ :=
  ⟨20, by decide⟩

/-- Non-vacuity for both call-free depth equations. -/
theorem callFree_nonvacuous_chain3 :
    CallFree chain3 = true ∧ EntryOk chain3 ∧
      RunsTo .frameReuse none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ ∧
      RunsTo .preJump none chain3 ⟨.returned 0, [.out 1], 3, 2⟩ :=
  ⟨callFree_chain3, entryOk_chain3, chain3_frameReuse, chain3_preJump⟩

/-- `CallFree` is needed for the `frameReuse` depth equation: `countUp 3` (whose entry calls
`rec`) is not call-free, satisfies `EntryOk`, and reaches depth `2`. -/
theorem callFree_needed_frameReuse_countUp3 :
    CallFree (countUp 3) = false ∧ EntryOk (countUp 3) ∧ RunsTo .frameReuse none (countUp 3)
      ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 2, 3⟩ ∧ (2 : Nat) ≠ 1 :=
  ⟨by decide, ⟨_, rfl, rfl⟩, countUp3_frameReuse, by decide⟩

/-- `CallFree` is needed for the `preJump` depth equation: `countUp 3` is not call-free,
satisfies `EntryOk`, and reaches depth `5` with `3` jumps. -/
theorem callFree_needed_preJump_countUp3 :
    CallFree (countUp 3) = false ∧ EntryOk (countUp 3) ∧ RunsTo .preJump none (countUp 3)
      ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 5, 3⟩ ∧ (5 : Nat) ≠ 3 + 1 :=
  ⟨by decide, ⟨_, rfl, rfl⟩, countUp3_preJump, by decide⟩

/-- `EntryOk` is needed for both depth equations (missing entry function): the empty program
is call-free, fails `EntryOk`, and halts with `ub` at depth `0`. -/
theorem entryOk_needed_emptyProg :
    CallFree emptyProg = true ∧ ¬ EntryOk emptyProg ∧
      RunsTo .frameReuse none emptyProg ⟨.ub, [], 0, 0⟩ ∧
      RunsTo .preJump none emptyProg ⟨.ub, [], 0, 0⟩ ∧ (0 : Nat) ≠ 1 ∧ (0 : Nat) ≠ 0 + 1 :=
  ⟨by decide, not_entryOk_emptyProg, ⟨1, by decide⟩, ⟨1, by decide⟩, by decide, by decide⟩

/-- `EntryOk` is needed for both depth equations (entry function with a parameter): the
program is call-free, its entry function exists but takes one parameter, and both runs halt
with `ub` at depth `0`. -/
theorem entryOk_needed_paramEntryProg :
    CallFree paramEntryProg = true ∧ (∃ fn, paramEntryProg.fns[0]? = some fn) ∧
      ¬ EntryOk paramEntryProg ∧
      RunsTo .frameReuse none paramEntryProg ⟨.ub, [], 0, 0⟩ ∧
      RunsTo .preJump none paramEntryProg ⟨.ub, [], 0, 0⟩ ∧ (0 : Nat) ≠ 1 ∧ (0 : Nat) ≠ 0 + 1 := by
  refine ⟨by decide, ⟨_, rfl⟩, ?_, ⟨1, by decide⟩, ⟨1, by decide⟩, by decide, by decide⟩
  rintro ⟨fn, hfn, hnp⟩
  simp [paramEntryProg] at hfn
  subst hfn
  simp at hnp

/-! ### The escape check -/

/-- The acceptance hypothesis of escape-check soundness is needed: the check rejects
`borrowProg`, which does not satisfy `NoStackBorrow`. -/
theorem escapeCheck_needed_borrowProg :
    EscapeCheckAccepts borrowProg = false ∧ ¬ NoStackBorrow borrowProg :=
  ⟨escapeCheck_rejects_borrowProg, not_noStackBorrow_borrowProg⟩

/-- The escape check is incomplete: it rejects `deadEscape` (an address is stored and then
overwritten before the tail call), although `deadEscape` satisfies `NoStackBorrow`. -/
theorem escapeCheck_incomplete_deadEscape :
    EscapeCheckAccepts deadEscape = false ∧ NoStackBorrow deadEscape :=
  ⟨by decide, noStackBorrow_deadEscape⟩

/-! ### Inlining -/

theorem inlEx_frameReuse : RunsTo .frameReuse none inlEx
    ⟨.returned 0, [.out 1, .out 2, .drop 9], 2, 1⟩ := ⟨20, by decide⟩

theorem inlEx_naive_frameReuse : RunsTo .frameReuse none (inlineCallSite .naive inlEx 0 1)
    ⟨.returned 0, [.drop 9, .out 1], 1, 1⟩ := ⟨20, by decide⟩

/-- The naive splice (keeping the callee's `tailCall`) changes behaviour: executed in `main`'s
frame, it finalizes `main`'s own local and pops `main`, so `main`'s continuation `out 2` never
runs and `drop 9` moves before `out 1`. -/
theorem naiveSplice_changes_events_inlEx :
    Observes .frameReuse none inlEx (.returned 0) [.out 1, .out 2, .drop 9] ∧
      Observes .frameReuse none (inlineCallSite .naive inlEx 0 1) (.returned 0) [.drop 9, .out 1] ∧
      ¬ Observes .frameReuse none (inlineCallSite .naive inlEx 0 1) (.returned 0)
          [.out 1, .out 2, .drop 9] := by
  refine ⟨⟨_, inlEx_frameReuse, rfl, rfl⟩, ⟨_, inlEx_naive_frameReuse, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo inlEx_naive_frameReuse]
  decide

/-- Non-vacuity of the corrected call-site splice (unbounded and bound `2`): `inlEx2`, where the
callee has a parameter moved into the tail call and a local with a destructor. The outcome is
neither `ub` nor `stackOverflow`, the splice changes the program, and the spliced program has
the same outcome and trace under both bounds. -/
theorem correctedSplice_nonvacuous_inlEx2 :
    (.returned 4 : Outcome) ≠ .ub ∧ (.returned 4 : Outcome) ≠ .stackOverflow ∧
      inlineCallSite .corrected inlEx2 0 1 ≠ inlEx2 ∧
      Observes .frameReuse none inlEx2 (.returned 4) [.out 3, .drop 5, .out 1, .out 2, .drop 9] ∧
      Observes .frameReuse (some 2) inlEx2 (.returned 4)
        [.out 3, .drop 5, .out 1, .out 2, .drop 9] ∧
      Observes .frameReuse none (inlineCallSite .corrected inlEx2 0 1) (.returned 4)
        [.out 3, .drop 5, .out 1, .out 2, .drop 9] ∧
      Observes .frameReuse (some 2) (inlineCallSite .corrected inlEx2 0 1) (.returned 4)
        [.out 3, .drop 5, .out 1, .out 2, .drop 9] :=
  ⟨by decide, by decide, by decide,
    ⟨⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 1⟩, ⟨40, by decide⟩, rfl, rfl⟩,
    ⟨⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 1⟩, ⟨40, by decide⟩, rfl, rfl⟩,
    ⟨⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 0⟩, ⟨40, by decide⟩, rfl, rfl⟩,
    ⟨⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 0⟩, ⟨40, by decide⟩, rfl, rfl⟩⟩

/-- The corrected splice does not preserve the tail-call counter: the unbounded run of `inlEx2`
executes one tail-call jump, that of the spliced program none (outcome, trace and maximum depth
agree; `Observes` ignores the counter). -/
theorem correctedSplice_tailCalls_differ_inlEx2 :
    RunsTo .frameReuse none inlEx2
      ⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 1⟩ ∧
      RunsTo .frameReuse none (inlineCallSite .corrected inlEx2 0 1)
        ⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 0⟩ :=
  ⟨⟨40, by decide⟩, ⟨40, by decide⟩⟩

/-- `o ≠ ub` is needed: `g` returns the address of its own local; after `g` returns, the load
is `ub` in the original, but in the inlined program `g`'s slot lives in `main`'s frame. -/
theorem correctedSplice_ub_not_preserved_danglingRet :
    Observes .frameReuse none danglingRet .ub [] ∧
      ¬ Observes .frameReuse none (inlineCallSite .corrected danglingRet 0 0) .ub [] := by
  have h1 : RunsTo .frameReuse none danglingRet ⟨.ub, [], 2, 0⟩ := ⟨20, by decide⟩
  have h2 : RunsTo .frameReuse none (inlineCallSite .corrected danglingRet 0 0)
      ⟨.returned 5, [], 1, 0⟩ := ⟨20, by decide⟩
  refine ⟨⟨_, h1, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo h2]
  decide

/-- `o ≠ stackOverflow` is needed: with bound `1`, the original overflows at the call, the
inlined program does not push a frame. -/
theorem correctedSplice_overflow_not_preserved_plainCall :
    Observes .frameReuse (some 1) plainCall .stackOverflow [] ∧
      ¬ Observes .frameReuse (some 1) (inlineCallSite .corrected plainCall 0 0) .stackOverflow [] := by
  have h1 : RunsTo .frameReuse (some 1) plainCall ⟨.stackOverflow, [], 1, 0⟩ := ⟨20, by decide⟩
  have h2 : RunsTo .frameReuse (some 1) (inlineCallSite .corrected plainCall 0 0)
      ⟨.returned 0, [.out 1], 1, 0⟩ := ⟨20, by decide⟩
  refine ⟨⟨_, h1, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo h2]
  decide

/-- `o ≠ ub` excludes more than dangling returns: when the callee's own tail call passes a
pointer into the callee's frame (`borrowProg`, a `ub` load under `frameReuse`), the corrected
splice runs the callee's slots in `main`'s frame and the load returns `5`. -/
theorem correctedSplice_masks_borrow_ub_borrowProg :
    Observes .frameReuse none borrowProg .ub [] ∧
      Observes .frameReuse none (inlineCallSite .corrected borrowProg 0 0) (.returned 5) [] :=
  ⟨⟨_, borrowProg_frameReuse, rfl, rfl⟩, ⟨⟨.returned 5, [], 2, 0⟩, ⟨40, by decide⟩, rfl, rfl⟩⟩

/-- `Observes` sees values only through `Val.obs`, which maps pointers to `0`: in `ptrRetProg` the
pointer that `main` holds after the call is `ptr 1 0` (slot `0` of frame `1`) before the
corrected splice and `ptr 0 1` (slot `1` of `main`'s own frame) after it, and both programs
observe as returning `0` with an empty trace. -/
theorem correctedSplice_raw_values_differ_ptrRetProg :
    (match run .frameReuse none ptrRetProg 3 (start none ptrRetProg) with
     | .running st => st.stack.head?.map (fun fr => fr.get 0)
     | _ => none) = some (.ptr 1 0) ∧
    (match run .frameReuse none (inlineCallSite .corrected ptrRetProg 0 0) 6
        (start none (inlineCallSite .corrected ptrRetProg 0 0)) with
     | .running st => st.stack.head?.map (fun fr => fr.get 0)
     | _ => none) = some (.ptr 0 1) ∧
    Observes .frameReuse none ptrRetProg (.returned 0) [] ∧
    Observes .frameReuse none (inlineCallSite .corrected ptrRetProg 0 0) (.returned 0) [] :=
  ⟨by decide, by decide, ⟨⟨.returned 0, [], 2, 0⟩, ⟨20, by decide⟩, rfl, rfl⟩,
   ⟨⟨.returned 0, [], 1, 0⟩, ⟨20, by decide⟩, rfl, rfl⟩⟩

theorem mutualRec3_frameReuse_bound3 : RunsTo .frameReuse (some 3) (mutualRec 3)
    ⟨.returned 0, [], 2, 6⟩ := ⟨60, by decide⟩

theorem mutualRec3_correctedTailSite_bound3 :
    RunsTo .frameReuse (some 3) (inlineTailSite .corrected (mutualRec 3) 1 1)
      ⟨.stackOverflow, [], 3, 0⟩ := ⟨60, by decide⟩

/-- At a tail site the corrected splice does not preserve the stack bound: with bound `3`,
`mutualRec 3` returns, but after splicing `g` into `c`'s tail site it overflows. -/
theorem correctedTailSiteSplice_overflows_mutualRec3 :
    Observes .frameReuse (some 3) (mutualRec 3) (.returned 0) [] ∧
      Observes .frameReuse (some 3) (inlineTailSite .corrected (mutualRec 3) 1 1) .stackOverflow [] ∧
      ¬ Observes .frameReuse (some 3) (inlineTailSite .corrected (mutualRec 3) 1 1) (.returned 0) [] := by
  refine ⟨⟨_, mutualRec3_frameReuse_bound3, rfl, rfl⟩,
    ⟨_, mutualRec3_correctedTailSite_bound3, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo mutualRec3_correctedTailSite_bound3]
  decide

/-- Instance `N = 3` of the tail-site depth equations (unbounded). -/
theorem correctedTailSiteSplice_mutualRec3 :
    RunsTo .frameReuse none (mutualRec 3) ⟨.returned 0, [], 2, 6⟩ ∧
      RunsTo .frameReuse none (inlineTailSite .corrected (mutualRec 3) 1 1)
        ⟨.returned 0, [], 5, 0⟩ :=
  ⟨⟨60, by decide⟩, ⟨60, by decide⟩⟩

/-- A concrete comparison (one instance, not a general claim): at the same tail site, the
splice that keeps `g`'s `tailCall` stays within bound `3`. -/
theorem naiveTailSiteSplice_within_bound_mutualRec3 :
    RunsTo .frameReuse (some 3) (inlineTailSite .naive (mutualRec 3) 1 1)
      ⟨.returned 0, [], 2, 3⟩ := ⟨60, by decide⟩

/-! ### Finalization, panics and unwinding -/

/-- Non-vacuity of `dropList_clears_pending_of_ne_abort`: an all-quiet frame with three pending
slots; finalizing them does not abort. -/
theorem dropList_clears_pending_nonvacuous :
    let fn : Fn := ⟨0, [.quiet, .quiet, .quiet], []⟩
    let fr : Frame := ⟨1, 1, 3, [.int 1, .int 2, .int 3], [true, true, true], .thenReturn, none⟩
    pendingDrops fn fr = [2, 1, 0] ∧ (dropList fn fr (pendingDrops fn fr) false).2.2 ≠ .abort := by
  decide

/-- The non-abort hypothesis is needed: two panicking destructors abort the finalization and
leave slot `0` pending. -/
theorem dropList_abort_leaves_pending :
    let fn : Fn := ⟨0, [.quiet, .panics, .panics], []⟩
    let fr : Frame := ⟨1, 1, 3, [.int 1, .int 2, .int 3], [true, true, true], .thenReturn, none⟩
    (dropList fn fr (pendingDrops fn fr) false).2.2 = .abort ∧
      pendingDrops fn (dropList fn fr (pendingDrops fn fr) false).1 = [0] := by decide

/-- The function `t` of `panicFin d0 d1 d2`. -/
def panicFinT (d0 d1 d2 : DtorKind) : Fn :=
  ⟨0, [d0, d1, d2], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2, .assign 2 (.const 3) 3,
    .tailCall 2 []]⟩

/-- `t`'s frame just before its tail call: three owned locals holding `1`, `2`, `3`. -/
def panicFinFrame : Frame :=
  ⟨1, 1, 3, [.int 1, .int 2, .int 3], [true, true, true], .thenReturn, none⟩

/-- The frames below `t`: `main`, which owns `50` and waits for `t`'s result. -/
def panicFinRest : List Frame := [⟨0, 0, 1, [.int 50, .undef], [true, false], .store 1 2, none⟩]

/-- The state of `panicFin d0 d1 d2` just before `t`'s tail call. -/
def panicFinState : State := ⟨panicFinFrame :: panicFinRest, 2, [], 2, 0, false⟩

theorem panicFinState_reached (d0 d1 d2 : DtorKind) :
    run .frameReuse none (panicFin d0 d1 d2) 5 (start none (panicFin d0 d1 d2)) =
      .running panicFinState := by
  cases d0 <;> cases d1 <;> cases d2 <;> decide

/-- Positive example for `AtTailCall`. -/
theorem atTailCall_panicFin (d0 d1 d2 : DtorKind) :
    AtTailCall (panicFin d0 d1 d2) panicFinState (panicFinT d0 d1 d2) panicFinFrame panicFinRest
      2 [] [] panicFinFrame :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Negative example for `AtTailCall`: the same state, paired with a function whose
instruction at `pc 3` is not a `tailCall`, is not at a tail call. -/
theorem not_atTailCall_wrongInstr :
    ¬ AtTailCall ⟨[⟨0, [], []⟩, ⟨0, [.quiet, .quiet, .quiet], [.panic, .panic, .panic, .panic]⟩]⟩
      panicFinState ⟨0, [.quiet, .quiet, .quiet], [.panic, .panic, .panic, .panic]⟩
      panicFinFrame panicFinRest 2 [] [] panicFinFrame := by
  intro h
  have := h.instr_eq
  simp [panicFinFrame] at this

/-- Non-vacuity of the no-panic finalization theorem: all destructors quiet, three pending
drops. -/
theorem finalizes_then_push_nonvacuous :
    AtTailCall (panicFin .quiet .quiet .quiet) panicFinState (panicFinT .quiet .quiet .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrame = [] ∧
      finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrame =
        [.drop 3, .drop 2, .drop 1] :=
  ⟨atTailCall_panicFin _ _ _, by decide, by decide⟩

/-- The no-panic hypothesis is needed: with one panicking destructor the step does not push
the callee. -/
theorem finalizes_then_push_fails_with_panic :
    AtTailCall (panicFin .quiet .panics .quiet) panicFinState (panicFinT .quiet .panics .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      panickingPending (panicFinT .quiet .panics .quiet) panicFinFrame ≠ [] ∧
      step .frameReuse none (panicFin .quiet .panics .quiet) panicFinState ≠
        bumpTail (push none (panicFin .quiet .panics .quiet)
          { panicFinState with
            events := panicFinState.events ++
              finalizationEvents (panicFinT .quiet .panics .quiet) panicFinFrame }
          panicFinRest 2 []) :=
  ⟨atTailCall_panicFin _ _ _, by decide, by decide⟩

/-- The field `not_unwinding` of `AtTailCall` is needed (no-panic theorem): in the same state
with a panic already propagating, every other field holds and no destructor panics, but the
step unwinds instead of pushing the callee. -/
theorem finalizes_then_push_fails_when_unwinding :
    let st : State := { panicFinState with unwinding := true }
    st.stack = panicFinFrame :: panicFinRest ∧ st.unwinding = true ∧
      panicFinFrame.pendingRet = none ∧
      (panicFin .quiet .quiet .quiet).fns[panicFinFrame.fn]? = some (panicFinT .quiet .quiet .quiet) ∧
      (panicFinT .quiet .quiet .quiet).code[panicFinFrame.pc]? = some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrame = [] ∧
      step .frameReuse none (panicFin .quiet .quiet .quiet) st ≠
        bumpTail (push none (panicFin .quiet .quiet .quiet)
          { st with
              events := st.events ++
                finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrame }
          panicFinRest 2 []) := by
  decide

/-- The frame of `panicFinFrame` with a pending return value. -/
def panicFinFrameRet : Frame := { panicFinFrame with pendingRet := some (.int 99) }

/-- The field `no_pendingRet` of `AtTailCall` is needed (no-panic theorem): with a pending
return value, every other field holds and no destructor panics, but the step returns instead
of pushing the callee. -/
theorem finalizes_then_push_fails_with_pendingRet :
    let st : State := ⟨panicFinFrameRet :: panicFinRest, 2, [], 2, 0, false⟩
    st.stack = panicFinFrameRet :: panicFinRest ∧ st.unwinding = false ∧
      panicFinFrameRet.pendingRet ≠ none ∧
      (panicFin .quiet .quiet .quiet).fns[panicFinFrameRet.fn]? = some (panicFinT .quiet .quiet .quiet) ∧
      (panicFinT .quiet .quiet .quiet).code[panicFinFrameRet.pc]? = some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrameRet [] = some ([], panicFinFrameRet) ∧
      panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrameRet = [] ∧
      step .frameReuse none (panicFin .quiet .quiet .quiet) st ≠
        bumpTail (push none (panicFin .quiet .quiet .quiet)
          { st with
              events := st.events ++
                finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrameRet }
          panicFinRest 2 []) := by
  decide

/-- `main` owns `7` (destructor kind `d`) and tail-calls with argument `deref 0`, a load
through an integer slot: argument evaluation is `ub`. -/
def badArgTailProg (d : DtorKind) : Prog :=
  ⟨[ ⟨0, [d], [.assign 0 (.const 7) 1, .tailCall 1 [.deref 0]]⟩,
     ⟨1, [.none], [.ret (.copy 0)]⟩ ]⟩

/-- The frame of `badArgTailProg` just before its tail call. -/
def badArgTailFrame : Frame := ⟨0, 0, 1, [.int 7], [true], .thenReturn, none⟩

/-- The state of `badArgTailProg` just before its tail call. -/
def badArgTailState : State := ⟨[badArgTailFrame], 1, [], 1, 0, false⟩

/-- The field `args_eq` of `AtTailCall` is needed (no-panic theorem): argument evaluation is
`ub`, every other field holds, no destructor panics (taking the frame after evaluation to be
the unchanged frame and the argument values to be `[]`), and the step halts with `ub` and no
`drop` event. -/
theorem finalizes_then_push_fails_when_args_ub :
    let fn : Fn := ⟨0, [.quiet], [.assign 0 (.const 7) 1, .tailCall 1 [.deref 0]]⟩
    badArgTailState.stack = badArgTailFrame :: [] ∧ badArgTailState.unwinding = false ∧
      badArgTailFrame.pendingRet = none ∧
      (badArgTailProg .quiet).fns[badArgTailFrame.fn]? = some fn ∧
      fn.code[badArgTailFrame.pc]? = some (.tailCall 1 [.deref 0]) ∧
      evalOps [] badArgTailFrame [.deref 0] = none ∧
      panickingPending fn badArgTailFrame = [] ∧
      step .frameReuse none (badArgTailProg .quiet) badArgTailState = .halted ⟨.ub, [], 1, 0⟩ ∧
      step .frameReuse none (badArgTailProg .quiet) badArgTailState ≠
        bumpTail (push none (badArgTailProg .quiet)
          { badArgTailState with
            events := badArgTailState.events ++ finalizationEvents fn badArgTailFrame } [] 1 []) := by
  decide

/-- The function `t` of `panicFin`, with a `panic` instead of the tail call at `pc 3`. -/
def panicFinTNoTail : Fn :=
  ⟨0, [.quiet, .quiet, .quiet], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
    .assign 2 (.const 3) 3, .panic]⟩

/-- `panicFin .quiet .quiet .quiet` with `t`'s tail call replaced by `panic`. -/
def panicFinNoTail : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     panicFinTNoTail,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- The field `instr_eq` of `AtTailCall` is needed (no-panic finalization theorem; the fields
`stack_eq` and `fn_eq` only name the frame and function that `instr_eq` constrains): at an
instruction that is not a tail call, every other field holds (with no arguments), no
destructor panics, and the step neither pushes the callee nor unwinds below the frame. -/
theorem finalization_fails_at_other_instr :
    panicFinState.stack = panicFinFrame :: panicFinRest ∧ panicFinState.unwinding = false ∧
      panicFinFrame.pendingRet = none ∧
      panicFinNoTail.fns[panicFinFrame.fn]? = some panicFinTNoTail ∧
      panicFinTNoTail.code[panicFinFrame.pc]? ≠ some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      panickingPending panicFinTNoTail panicFinFrame = [] ∧
      step .frameReuse none panicFinNoTail panicFinState ≠
        bumpTail (push none panicFinNoTail
          { panicFinState with
              events := panicFinState.events ++
                finalizationEvents panicFinTNoTail panicFinFrame } panicFinRest 2 []) ∧
      step .frameReuse none panicFinNoTail panicFinState ≠
        unwindBelow { panicFinState with
              events := panicFinState.events ++
                finalizationEvents panicFinTNoTail panicFinFrame } panicFinRest := by
  decide

/-- Non-vacuity of the panic-during-finalization theorem: exactly one panicking destructor. -/
theorem panic_drops_rest_nonvacuous :
    AtTailCall (panicFin .quiet .panics .quiet) panicFinState (panicFinT .quiet .panics .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      (panickingPending (panicFinT .quiet .panics .quiet) panicFinFrame).length = 1 ∧
      finalizationEvents (panicFinT .quiet .panics .quiet) panicFinFrame =
        [.drop 3, .drop 2, .drop 1] :=
  ⟨atTailCall_panicFin _ _ _, by decide, by decide⟩

/-- "Exactly one panicking destructor" is needed (upper side): with two, the second panic
(while unwinding) aborts, and the slot holding `1` is never dropped. -/
theorem panic_drops_rest_fails_with_two_panics :
    AtTailCall (panicFin .quiet .panics .panics) panicFinState (panicFinT .quiet .panics .panics)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      (panickingPending (panicFinT .quiet .panics .panics) panicFinFrame).length = 2 ∧
      step .frameReuse none (panicFin .quiet .panics .panics) panicFinState =
        .halted ⟨.aborted, [.drop 3, .drop 2], 2, 0⟩ ∧
      step .frameReuse none (panicFin .quiet .panics .panics) panicFinState ≠
        unwindBelow { panicFinState with
            events := panicFinState.events ++
              finalizationEvents (panicFinT .quiet .panics .panics) panicFinFrame }
          panicFinRest :=
  ⟨atTailCall_panicFin _ _ _, by decide, by decide, by decide⟩

/-- "Exactly one panicking destructor" is needed (lower side): with none, the step pushes the
callee instead of unwinding. -/
theorem panic_drops_rest_fails_with_zero_panics :
    AtTailCall (panicFin .quiet .quiet .quiet) panicFinState (panicFinT .quiet .quiet .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      (panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrame).length = 0 ∧
      step .frameReuse none (panicFin .quiet .quiet .quiet) panicFinState ≠
        unwindBelow { panicFinState with
            events := panicFinState.events ++
              finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrame }
          panicFinRest :=
  ⟨atTailCall_panicFin _ _ _, by decide, by decide⟩

/-- The field `not_unwinding` of `AtTailCall` is needed (panic theorem): with a panic already
propagating, every other field holds and exactly one pending destructor panics, but the panic
aborts after two drops instead of dropping the rest and unwinding. -/
theorem panic_drops_rest_fails_when_unwinding :
    let st : State := { panicFinState with unwinding := true }
    st.stack = panicFinFrame :: panicFinRest ∧ st.unwinding = true ∧
      panicFinFrame.pendingRet = none ∧
      (panicFin .quiet .panics .quiet).fns[panicFinFrame.fn]? = some (panicFinT .quiet .panics .quiet) ∧
      (panicFinT .quiet .panics .quiet).code[panicFinFrame.pc]? = some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      (panickingPending (panicFinT .quiet .panics .quiet) panicFinFrame).length = 1 ∧
      step .frameReuse none (panicFin .quiet .panics .quiet) st =
        .halted ⟨.aborted, [.drop 3, .drop 2], 2, 0⟩ ∧
      step .frameReuse none (panicFin .quiet .panics .quiet) st ≠
        unwindBelow { st with
            events := st.events ++
              finalizationEvents (panicFinT .quiet .panics .quiet) panicFinFrame } panicFinRest := by
  decide

/-- `t` owns locals holding `1`, `2`, `3` (destructor kinds quiet, panicking, quiet) and
tail-calls `h (move local0)`. -/
def panicMoveT : Fn :=
  ⟨0, [.quiet, .panics, .quiet], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
    .assign 2 (.const 3) 3, .tailCall 2 [.move 0]]⟩

/-- `main` owns `50` and calls `panicMoveT`; `h` takes one parameter. -/
def panicMoveProg : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     panicMoveT,
     ⟨1, [.none], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- The field `no_pendingRet` of `AtTailCall` is needed (panic theorem): with a pending return
value, every other field holds (the argument `move 0` evaluates to `1` and clears slot `0`'s
drop flag) and exactly one pending destructor of the evaluated frame panics, but the step is
a return: it also drops the moved-from slot, so its trace differs from the conclusion's. -/
theorem panic_drops_rest_fails_with_pendingRet :
    let st : State := ⟨panicFinFrameRet :: panicFinRest, 2, [], 2, 0, false⟩
    st.stack = panicFinFrameRet :: panicFinRest ∧ st.unwinding = false ∧
      panicFinFrameRet.pendingRet ≠ none ∧
      panicMoveProg.fns[panicFinFrameRet.fn]? = some panicMoveT ∧
      panicMoveT.code[panicFinFrameRet.pc]? = some (.tailCall 2 [.move 0]) ∧
      evalOps panicFinRest panicFinFrameRet [.move 0] =
        some ([.int 1], panicFinFrameRet.kill 0) ∧
      (panickingPending panicMoveT (panicFinFrameRet.kill 0)).length = 1 ∧
      step .frameReuse none panicMoveProg st ≠
        unwindBelow { st with
            events := st.events ++ finalizationEvents panicMoveT (panicFinFrameRet.kill 0) }
          panicFinRest := by
  decide

/-- The field `args_eq` of `AtTailCall` is needed (panic theorem): argument evaluation is `ub`,
every other field holds, exactly one pending destructor panics (taking the frame after
evaluation to be the unchanged frame), and the step halts with `ub` and no `drop` event. -/
theorem panic_drops_rest_fails_when_args_ub :
    let fn : Fn := ⟨0, [.panics], [.assign 0 (.const 7) 1, .tailCall 1 [.deref 0]]⟩
    badArgTailState.stack = badArgTailFrame :: [] ∧ badArgTailState.unwinding = false ∧
      badArgTailFrame.pendingRet = none ∧
      (badArgTailProg .panics).fns[badArgTailFrame.fn]? = some fn ∧
      fn.code[badArgTailFrame.pc]? = some (.tailCall 1 [.deref 0]) ∧
      evalOps [] badArgTailFrame [.deref 0] = none ∧
      (panickingPending fn badArgTailFrame).length = 1 ∧
      step .frameReuse none (badArgTailProg .panics) badArgTailState = .halted ⟨.ub, [], 1, 0⟩ ∧
      step .frameReuse none (badArgTailProg .panics) badArgTailState ≠
        unwindBelow { badArgTailState with
            events := badArgTailState.events ++ finalizationEvents fn badArgTailFrame } [] := by
  decide

/-- The function `t` of `panicFin .quiet .panics .quiet`, with a `panic` instead of the tail
call at `pc 3`. -/
def panicFinTOnePanicNoTail : Fn :=
  ⟨0, [.quiet, .panics, .quiet], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
    .assign 2 (.const 3) 3, .panic]⟩

/-- `panicFin .quiet .panics .quiet` with `t`'s tail call replaced by `panic`. -/
def panicFinOnePanicNoTail : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     panicFinTOnePanicNoTail,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- The field `instr_eq` of `AtTailCall` is needed (panic theorem; the fields `stack_eq` and
`fn_eq` only name the frame and function that `instr_eq` constrains): at an instruction that is
not a tail call, every other field holds (with no arguments), exactly one pending destructor
panics, and the step does not unwind below the frame. -/
theorem panic_drops_rest_fails_at_other_instr :
    panicFinState.stack = panicFinFrame :: panicFinRest ∧ panicFinState.unwinding = false ∧
      panicFinFrame.pendingRet = none ∧
      panicFinOnePanicNoTail.fns[panicFinFrame.fn]? = some panicFinTOnePanicNoTail ∧
      panicFinTOnePanicNoTail.code[panicFinFrame.pc]? ≠ some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      (panickingPending panicFinTOnePanicNoTail panicFinFrame).length = 1 ∧
      step .frameReuse none panicFinOnePanicNoTail panicFinState ≠
        unwindBelow { panicFinState with
            events := panicFinState.events ++
              finalizationEvents panicFinTOnePanicNoTail panicFinFrame } panicFinRest := by
  decide

theorem panicFin_frameReuse : RunsTo .frameReuse none (panicFin .quiet .panics .quiet)
    ⟨.panicked, [.drop 3, .drop 2, .drop 1, .drop 50], 2, 0⟩ := ⟨20, by decide⟩

/-- Popping the frame before its pending destructors run makes running them `ub`: each
destructor reaches its slot through the frame's identity (as a `deref` does), and the frame is
no longer on the stack. In `dtorProg`, `frameReuse` returns `0` with trace `[drop 7, out 1]`,
while `popFirst` halts with `ub` before any event. -/
theorem popFirst_ub_with_pending_drop_dtorProg :
    Observes .frameReuse none dtorProg (.returned 0) [.drop 7, .out 1] ∧
      Observes .popFirst none dtorProg .ub [] ∧
      ¬ Observes .popFirst none dtorProg (.returned 0) [.drop 7, .out 1] := by
  refine ⟨⟨_, dtorProg_frameReuse, rfl, rfl⟩, ⟨_, dtorProg_popFirst, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo dtorProg_popFirst]
  decide

theorem chain3_popFirst : RunsTo .popFirst none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ :=
  ⟨20, by decide⟩

/-- Positive control: when no destructor is pending at any tail call (`chain3` has no
destructors), `popFirst` and `frameReuse` produce the same result. -/
theorem popFirst_agrees_without_pending_drops_chain3 :
    RunsTo .popFirst none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ ∧
      RunsTo .frameReuse none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ :=
  ⟨chain3_popFirst, chain3_frameReuse⟩

end Toy.TailCall

namespace Toy.TailCall.Layout

/-- Comparing explicit parameters is not enough: a callee with a hidden caller-location
parameter that the current function lacks has a larger area, so frame reuse is unsound under
either cleanup convention. -/
theorem sigCheckExplicit_insufficient_calleeLoc :
    sigCheckExplicit ⟨[1], false⟩ ⟨[1], true⟩ = true ∧
      sigCheckFull ⟨[1], false⟩ ⟨[1], true⟩ = false ∧
      ¬ ReuseSound .callerPops (Sig.areaSize ⟨[1], false⟩) (Sig.areaSize ⟨[1], true⟩) ∧
      ¬ ReuseSound .calleePops (Sig.areaSize ⟨[1], false⟩) (Sig.areaSize ⟨[1], true⟩) := by
  refine ⟨by decide, by decide, not_reuseSound_callerPops_1_2, ?_⟩
  intro h
  have h1 := (h (fun _ => 0) 0 [5, 5] rfl).2.2
  simp [spAfterReturn, Sig.areaSize] at h1

/-- The converse mismatch depends on the cleanup convention: when the current function has
the hidden parameter and the callee lacks it, the callee's area fits, so frame reuse is sound
under caller cleanup and unsound under callee cleanup. -/
theorem sigCheckExplicit_callerLoc_depends_on_cleanup :
    sigCheckExplicit ⟨[1], true⟩ ⟨[1], false⟩ = true ∧
      sigCheckFull ⟨[1], true⟩ ⟨[1], false⟩ = false ∧
      ReuseSound .callerPops (Sig.areaSize ⟨[1], true⟩) (Sig.areaSize ⟨[1], false⟩) ∧
      ¬ ReuseSound .calleePops (Sig.areaSize ⟨[1], true⟩) (Sig.areaSize ⟨[1], false⟩) :=
  ⟨by decide, by decide, reuseSound_callerPops_2_1, not_reuseSound_calleePops_2_1⟩

/-- Non-vacuity of the signature-equality theorem. -/
theorem sigCheckFull_nonvacuous : sigCheckFull ⟨[1, 2], true⟩ ⟨[1, 2], true⟩ = true := by decide

/-- Equal areas: frame reuse at the fixed boundary is sound under either convention. -/
theorem reuseSound_of_eq (cl : Cleanup) (n : Nat) : ReuseSound cl n n := by
  intro m b args hlen
  refine ⟨fun x hx => writeArgs_eq_of_lt m (b - n) args x hx, readArgs_reuseWrite m b n args hlen, ?_⟩
  cases cl <;> rfl

/-- `sigCheckFull` is sufficient but not necessary, also under callee cleanup: `⟨[2], false⟩`
and `⟨[1], true⟩` differ (in explicit parameters too) but have equal areas. -/
theorem reuseSound_calleePops_without_sigCheck :
    sigCheckFull ⟨[2], false⟩ ⟨[1], true⟩ = false ∧
      sigCheckExplicit ⟨[2], false⟩ ⟨[1], true⟩ = false ∧
      ReuseSound .calleePops (Sig.areaSize ⟨[2], false⟩) (Sig.areaSize ⟨[1], true⟩) :=
  ⟨by decide, by decide, reuseSound_of_eq .calleePops 2⟩

/-- Non-vacuity of the relocation characterization: under callee cleanup a callee area of two
cells after a current area of one cell is unsound at the fixed boundary and sound with the
boundary moved by one cell. -/
theorem reuseSoundAt_calleePops_nonvacuous :
    ¬ ReuseSound .calleePops 1 2 ∧ ReuseSoundAt .calleePops 1 1 2 := by
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := (h (fun _ => 0) 0 [5, 5] rfl).2.2
    simp [spAfterReturn] at h1
  · intro m b args hlen
    refine ⟨fun x hx => writeArgs_eq_of_lt m _ args x (by omega), ?_, ?_⟩
    · exact readArgs_reuseWriteAt m b 1 2 args hlen
    · simp only [spAfterReturnAt]
      omega

/-- Non-vacuity of the caller-cleanup half of the relocation characterization. -/
theorem reuseSoundAt_callerPops_nonvacuous : ReuseSoundAt .callerPops 0 2 1 := by
  intro m b args hlen
  refine ⟨fun x hx => writeArgs_eq_of_lt m _ args x (by omega), ?_, ?_⟩
  · exact readArgs_reuseWriteAt m b 0 1 args hlen
  · simp only [spAfterReturnAt]
    omega

/-- The pair of card R13 (`⟨[1], true⟩` current, `⟨[1], false⟩` callee), unsound under callee
cleanup at the fixed boundary, is sound under callee cleanup with the boundary moved by `-1`
cells. -/
theorem reuseSoundAt_calleePops_callerLoc_relocated :
    ReuseSoundAt .calleePops (-1) (Sig.areaSize ⟨[1], true⟩) (Sig.areaSize ⟨[1], false⟩) := by
  intro m b args hlen
  simp only [Sig.areaSize] at hlen ⊢
  refine ⟨fun x hx => writeArgs_eq_of_lt m _ args x (by simp at hx ⊢; omega), ?_, ?_⟩
  · exact readArgs_reuseWriteAt m b (-1) _ args hlen
  · simp only [spAfterReturnAt]
    simp
    omega

end Toy.TailCall.Layout
