import ToyCoalesce.Refuted

/-!
# Further tightness witnesses

* `cex_vc_backward_needs_forestWF`: the well-formedness hypothesis of the backward
  verification-condition transfer cannot be dropped (merging a callee parameter).
* `cex_classAddrDisjoint_of_classAddrDisjointW_needs_h`: the hypothesis of
  `classAddrDisjoint_of_classAddrDisjointW` cannot be dropped (the merge of `p3`).
-/

namespace Toy.Coalesce

/-- `x` (local 0) := 1 and `y` (local 1) := 2; `y` is passed by `move` to a callee with parameter
local 2 that prints its parameter. Merging the parameter into `x` (`single 2 0 0`) violates
`ForestWF` (a callee parameter is in a class). -/
def pBackHwf : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.lit 2], .call 0 (.move ⟨1, 0, 1⟩)]
  dtors := []
  fns := [⟨2, [.out (.copy ⟨2, 0, 1⟩)]⟩]

theorem pBackHwf_outcome (A : Layout) :
    outcome semI pBackHwf A = .done [.vals [.int 2]] ∨ outcome semI pBackHwf A = .badLayout := by
  simp only [pBackHwf]; run_eval

theorem pBackHwf_coalesced_outcome (A : Layout) :
    outcome semI (coalesce (single 2 0 0) pBackHwf) A = .done [.vals [.int 1]] ∨
    outcome semI (coalesce (single 2 0 0) pBackHwf) A = .badLayout := by
  simp only [pBackHwf]; coalesce_simp; run_eval

/-- The well-formedness hypothesis of `vc_backward_addrFree_of_noValueClobber_of_ubFree` is needed:
under `MoveSem.inPlaceCall` and atomic assignments, for `pBackHwf` and the merge `single 2 0 0`,
every other hypothesis holds (`NoValueClobberStmt`, `UBFree`, `AddrFree` of the postcondition, and
validity of the postcondition for the coalesced program), the forest is not well formed, and the
postcondition is not valid for the source. -/
theorem cex_vc_backward_needs_forestWF :
    ¬ ForestWF pBackHwf (single 2 0 0) ∧
    NoValueClobberStmt .inPlaceCall (single 2 0 0) pBackHwf ∧
    UBFree semI pBackHwf ∧
    AddrFree (erasedIs [.vals [.int 1]]) ∧
    Valid semI (coalesce (single 2 0 0) pBackHwf) (erasedIs [.vals [.int 1]]) ∧
    ¬ Valid semI pBackHwf (erasedIs [.vals [.int 1]]) := by
  refine ⟨by decide, ?_, ?_, erasedIs_addrFree _, ?_, ?_⟩
  · intro A _ _; simp only [pBackHwf]; log_eval
  · intro ⟨A, hA, _⟩
    rcases pBackHwf_outcome A with h | h <;> rw [h] at hA <;> cases hA
  · intro o ⟨A, hA, hb⟩
    rcases pBackHwf_coalesced_outcome A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, hp⟩ := hv _ ⟨A0, rfl, by decide⟩
    have h2 : outcome semI pBackHwf A0 = .done [.vals [.int 2]] := by decide
    rw [h2] at ht; cases ht; revert hp; decide

/-- The hypothesis of `classAddrDisjoint_of_classAddrDisjointW` is needed: for `p3` and the merge
`single 0 1 0`, the conclusion `ClassAddrDisjoint` fails (and so does `ClassAddrDisjointW`). -/
theorem cex_classAddrDisjoint_of_classAddrDisjointW_needs_h :
    ¬ ClassAddrDisjointW p3 (single 0 1 0) ∧ ¬ ClassAddrDisjoint p3 (single 0 1 0) := by
  decide

/-- Non-vacuity of `classAddrDisjoint_of_classAddrDisjointW`: its hypothesis holds for `pChainOk`
and the forest `μChain`. -/
theorem nonvacuous_classAddrDisjoint_of_classAddrDisjointW : ClassAddrDisjointW pChainOk μChain := by
  decide

end Toy.Coalesce
