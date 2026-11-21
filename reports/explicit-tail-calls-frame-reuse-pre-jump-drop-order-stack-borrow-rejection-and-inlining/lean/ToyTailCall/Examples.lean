import ToyTailCall.Machine
import ToyTailCall.Borrow
import ToyTailCall.Inline
import ToyTailCall.Layout

/-!
# Example programs and definition examples

Every example here is fully proved (by evaluation in the kernel).
-/

namespace Toy.TailCall

/-! ### Programs -/

/-- Self-tail-recursion counting up (the shape of `tail_recursive` in the `drop-order` test):
`main` calls `rec 0`; `rec n` returns if `n ≥ N`, else creates a local `_local := n` whose
destructor emits `drop n`, and tail-calls `rec (n + 1)`.
Slots of `rec`: `0` = `n` (parameter), `1` = `_local` (destructor), `2` = temporary. -/
def countUp (N : Nat) : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩,
     ⟨1, [.none, .quiet, .none],
       [.branchLt 0 N 1 4, .assign 1 (.copy 0) 2, .assign 2 (.succ 0) 3,
        .tailCall 1 [.move 2], .ret (.const 0)]⟩ ]⟩

/-- `main` calls `t`; `t` owns a local with value `7` (destructor) and tail-calls `h`,
which emits `out 1` and returns. -/
def dtorProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.quiet], [.assign 0 (.const 7) 1, .tailCall 2 []]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- `t` passes the address of its own local (value `5`, no destructor) to `reader`, which
loads through it: `become reader(&local)`. -/
def borrowProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .tailCall 2 [.addrOf 0]]⟩,
     ⟨1, [.none], [.ret (.deref 0)]⟩ ]⟩

/-- A dead escape: `t` stores `&local` into slot `1`, overwrites slot `1` with `0`, and then
tail-calls with `copy 1` (an integer at run time). -/
def deadEscape : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.none, .none], [.assign 0 (.const 5) 1, .assign 1 (.addrOf 0) 2,
        .assign 1 (.const 0) 3, .tailCall 2 [.copy 1]]⟩,
     ⟨1, [.none], [.ret (.copy 0)]⟩ ]⟩

/-- Pre-jump finalization order: `t` has parameters `10`, `11` and locals `12`, `13`, `14`
(all with destructors) and tail-calls `sink(move local13)`. -/
def orderDemo : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 10, .const 11] 0 1, .ret (.move 0)]⟩,
     ⟨2, [.quiet, .quiet, .quiet, .quiet, .quiet],
       [.assign 2 (.const 12) 1, .assign 3 (.const 13) 2, .assign 4 (.const 14) 3,
        .tailCall 2 [.move 3]]⟩,
     ⟨1, [.quiet], [.emit 99 1, .ret (.const 0)]⟩ ]⟩

/-- `main` owns `50` (destructor) and calls `t`; `t` owns locals `1`, `2`, `3` with
destructor kinds `d0`, `d1`, `d2` and tail-calls `h`. -/
def panicFin (d0 d1 d2 : DtorKind) : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     ⟨0, [d0, d1, d2], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
        .assign 2 (.const 3) 3, .tailCall 2 []]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- `main` owns `9` (destructor), calls `g` at `pc 1`, then emits `out 2`; `g` tail-calls
`h`, which emits `out 1`. -/
def inlEx : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 9) 1, .call 1 [] 1 2, .emit 2 3, .ret (.move 1)]⟩,
     ⟨0, [], [.tailCall 2 []]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- A richer inlining instance: `main` owns `9`, calls `g 4` at `pc 1`, then emits `out 2`;
`g x` owns a local `5`, emits `out 3`, and tail-calls `h (move x)`; `h y` emits `out 1` and
returns `y`. Slots of `g`: `0` = `x` (destructor), `1` = local (destructor). -/
def inlEx2 : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 9) 1, .call 1 [.const 4] 1 2, .emit 2 3,
        .ret (.move 1)]⟩,
     ⟨1, [.quiet, .quiet], [.assign 1 (.const 5) 1, .emit 3 2, .tailCall 2 [.move 0]]⟩,
     ⟨1, [.none], [.emit 1 1, .ret (.move 0)]⟩ ]⟩

/-- Mutual tail recursion `c ↔ g`: `main` calls `c 0`; `c n` returns if `n ≥ N`, else
`become g(n)`; `g n` does `become c(n + 1)`. The tail site is `pc 1` of `c` (function `1`). -/
def mutualRec (N : Nat) : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩,
     ⟨1, [.none], [.branchLt 0 N 1 2, .tailCall 2 [.copy 0], .ret (.const 0)]⟩,
     ⟨1, [.none, .none], [.assign 1 (.succ 0) 1, .tailCall 1 [.move 1]]⟩ ]⟩

/-- `g` returns the address of its own local; `main` loads through it after `g` returned. -/
def danglingRet : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.deref 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .ret (.addrOf 0)]⟩ ]⟩

/-- `main` calls `g` (no tail call), which emits `out 1` and returns `0`. -/
def plainCall : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩

/-- A call-free chain `main → f₁ → f₂` of two tail calls. -/
def chain3 : Prog :=
  ⟨[ ⟨0, [], [.tailCall 1 []]⟩,
     ⟨0, [], [.emit 1 1, .tailCall 2 []]⟩,
     ⟨0, [], [.ret (.const 0)]⟩ ]⟩

/-- The empty program (no entry function). -/
def emptyProg : Prog := ⟨[]⟩

/-- `main` calls `rec 0`; `rec x` calls itself with a non-tail `call` (a self-call site for
the inliner, never run in a result). -/
def selfCallProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩,
     ⟨1, [.none], [.call 1 [.copy 0] 0 1, .ret (.move 0)]⟩ ]⟩

/-- `t` passes the address of its own local to `h`, which ignores its argument and returns
`0`: a stack borrow is passed but never loaded through. -/
def ignorePtrProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .tailCall 2 [.addrOf 0]]⟩,
     ⟨1, [.none], [.ret (.const 0)]⟩ ]⟩

/-- `g` returns the address of its own local; `main` returns that pointer without loading
through it. -/
def ptrRetProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.copy 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .ret (.addrOf 0)]⟩ ]⟩

/-- An entry function that exists but takes one parameter. -/
def paramEntryProg : Prog := ⟨[⟨1, [.none], [.ret (.const 0)]⟩]⟩

/-! ### Semantics: one program under the four readings of `tailCall` -/

theorem dtorProg_callReturn : RunsTo .callReturn none dtorProg
    ⟨.returned 0, [.out 1, .drop 7], 3, 1⟩ := ⟨20, by decide⟩

theorem dtorProg_preJump : RunsTo .preJump none dtorProg
    ⟨.returned 0, [.drop 7, .out 1], 3, 1⟩ := ⟨20, by decide⟩

theorem dtorProg_frameReuse : RunsTo .frameReuse none dtorProg
    ⟨.returned 0, [.drop 7, .out 1], 2, 1⟩ := ⟨20, by decide⟩

/-- Under `popFirst` the pending destructor of `t`'s local would reach its slot after `t`'s
frame is gone: `ub`, before any event. -/
theorem dtorProg_popFirst : RunsTo .popFirst none dtorProg ⟨.ub, [], 2, 0⟩ := ⟨20, by decide⟩

/-- `Observes` rejects a trace the run does not produce. -/
theorem not_observes_dtorProg_frameReuse_callReturnTrace :
    ¬ Observes .frameReuse none dtorProg (.returned 0) [.out 1, .drop 7] := by
  rw [observes_iff_of_runsTo dtorProg_frameReuse]
  decide

/-! ### `pendingDrops`: reverse declaration order, moved-from and destructor-less slots skipped -/

/-- Positive: the frame of `orderDemo`'s `t` just before its tail call, after `move 3` has
been evaluated: slots `4, 2, 1, 0` are pending (locals before parameters). -/
theorem pendingDrops_orderDemo :
    pendingDrops ⟨2, [.quiet, .quiet, .quiet, .quiet, .quiet], []⟩
      ⟨1, 1, 3, [.int 10, .int 11, .int 12, .int 13, .int 14],
        [true, true, true, false, true], .thenReturn, none⟩ = [4, 2, 1, 0] := by decide

/-- Negative: a live slot without a destructor is never pending. -/
theorem pendingDrops_skips_no_dtor :
    pendingDrops ⟨0, [.none, .quiet], []⟩ ⟨0, 0, 0, [.int 1, .int 2], [true, false], .thenReturn, none⟩
      = [] := by decide

/-! ### `NoStackBorrow` -/

theorem noStackBorrow_dtorProg : NoStackBorrow dtorProg :=
  noStackBorrow_of_allRunning _ 20 (by decide)

theorem noStackBorrow_deadEscape : NoStackBorrow deadEscape :=
  noStackBorrow_of_allRunning _ 20 (by decide)

theorem not_noStackBorrow_borrowProg : ¬ NoStackBorrow borrowProg := fun h => by
  have h2 := h 2 _ rfl
  revert h2
  decide

/-! ### `EscapeCheckAccepts` -/

theorem escapeCheck_accepts_dtorProg : EscapeCheckAccepts dtorProg = true := by decide

theorem escapeCheck_accepts_countUp3 : EscapeCheckAccepts (countUp 3) = true := by decide

theorem escapeCheck_rejects_borrowProg : EscapeCheckAccepts borrowProg = false := by decide

/-! ### `CallFree` and `EntryOk` -/

theorem callFree_chain3 : CallFree chain3 = true := by decide

theorem not_callFree_countUp3 : CallFree (countUp 3) = false := by decide

theorem entryOk_chain3 : EntryOk chain3 := ⟨_, rfl, rfl⟩

theorem not_entryOk_emptyProg : ¬ EntryOk emptyProg := by
  rintro ⟨fn, h, _⟩
  cases h

/-! ### `inlineCallSite` -/

/-- Positive: the corrected splice of `inlEx` at `main`'s `pc 1`. -/
theorem inlineCallSite_corrected_inlEx :
    (inlineCallSite .corrected inlEx 0 1).fns[0]? = some
      ⟨0, [.quiet, .none, .none],
       [.assign 0 (.const 9) 1, .goto 4, .emit 2 3, .ret (.move 1),
        .reset [2] 5, .dropSlots [] 6, .call 2 [] 1 2, .panic]⟩ := by decide

/-- Negative: a site that is not a `call` leaves the program unchanged. -/
theorem inlineCallSite_nonCall_unchanged : inlineCallSite .corrected inlEx 0 0 = inlEx := by
  decide

/-- Negative: a well-formed non-tail call of a function to itself is not inlined. The site is
a `call` whose argument count, parameter count, slot count and destination pass every other
check of `inlineCallSite`, so the program is unchanged because of the self-call test. -/
theorem inlineCallSite_self_unchanged :
    (selfCallProg.fns[1]?.bind fun fn => fn.code[0]?) = some (.call 1 [.copy 0] 0 1) ∧
      (∃ c, selfCallProg.fns[1]? = some c ∧
        [Operand.copy 0].length = c.nParams ∧ c.nParams ≤ c.nSlots ∧ 0 < c.nSlots) ∧
      inlineCallSite .corrected selfCallProg 1 0 = selfCallProg :=
  ⟨by decide, ⟨_, rfl, by decide, by decide, by decide⟩, by decide⟩

/-- Negative: `inlineTailSite` leaves a site that is not a `tailCall` unchanged. -/
theorem inlineTailSite_nonTail_unchanged :
    inlineTailSite .corrected (mutualRec 3) 1 0 = mutualRec 3 := by decide

/-- Positive: `desugarTailSite` at `c`'s tail site of `mutualRec 3` (pre-jump reading as code). -/
theorem desugarTailSite_mutualRec3 :
    (desugarTailSite (mutualRec 3) 1 1).fns[1]? = some
      ⟨1, [.none, .none, .none],
       [.branchLt 0 3 1 2, .goto 3, .ret (.const 0), .assign 1 (.copy 0) 4, .dropSlots [0] 5,
        .call 2 [.move 1] 2 6, .ret (.move 2)]⟩ := by decide

end Toy.TailCall

namespace Toy.TailCall.Layout

/-! ### `ReuseSound`, `Sig.areaSize`, signature checks -/

/-- Positive: a callee area of one cell fits in a current area of two (caller cleanup). -/
theorem reuseSound_callerPops_2_1 : ReuseSound .callerPops 2 1 := by
  intro m b args hlen
  match args, hlen with
  | [v], _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      show (if x = b - ((1 : Nat) : Int) then v else m x) = m x
      split
      · omega
      · rfl
    · simp [readArgs, reuseWrite, writeArgs]
    · rfl

/-- Positive: equal areas of one cell (callee cleanup). -/
theorem reuseSound_calleePops_1_1 : ReuseSound .calleePops 1 1 := by
  intro m b args hlen
  match args, hlen with
  | [v], _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      show (if x = b - ((1 : Nat) : Int) then v else m x) = m x
      split
      · omega
      · rfl
    · simp [readArgs, reuseWrite, writeArgs]
    · rfl

/-- Negative: a callee area of two cells overwrites the caller's frame when the current
area has one cell. -/
theorem not_reuseSound_callerPops_1_2 : ¬ ReuseSound .callerPops 1 2 := by
  intro h
  have h1 := (h (fun _ => 0) 0 [5, 5] rfl).1 (-2) (by decide)
  simp [reuseWrite, writeArgs] at h1

/-- Negative: under callee cleanup a smaller callee area leaves the caller's stack pointer
wrong. -/
theorem not_reuseSound_calleePops_2_1 : ¬ ReuseSound .calleePops 2 1 := by
  intro h
  have h1 := (h (fun _ => 0) 0 [5] rfl).2.2
  simp [spAfterReturn] at h1

theorem areaSize_examples :
    Sig.areaSize ⟨[1, 2], false⟩ = 3 ∧ Sig.areaSize ⟨[1, 2], true⟩ = 4 := by decide

theorem sigCheckFull_examples :
    sigCheckFull ⟨[1], true⟩ ⟨[1], true⟩ = true ∧ sigCheckFull ⟨[1], true⟩ ⟨[1], false⟩ = false := by
  decide

theorem sigCheckExplicit_examples :
    sigCheckExplicit ⟨[1], true⟩ ⟨[1], false⟩ = true ∧
      sigCheckExplicit ⟨[1], true⟩ ⟨[2], true⟩ = false := by decide

end Toy.TailCall.Layout
