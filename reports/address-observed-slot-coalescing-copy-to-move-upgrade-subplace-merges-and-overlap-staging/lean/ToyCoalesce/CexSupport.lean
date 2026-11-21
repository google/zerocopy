import ToyCoalesce.CexAdj

/-!
# Supporting witnesses in canonical form

Each statement below follows from counterexamples, positive controls and outcome lemmas proved
in `CexMerge.lean`, `CexExtra.lean` and `CexUpgrade.lean`; it restates them in the form used by
the hypothesis ledgers (every other hypothesis holds and the hypothesis or the conclusion fails),
or records an outcome that a card states in prose.
-/

namespace Toy.Coalesce

/-! ## Lifetime policies -/

/-- Non-vacuity of `not_policySound_of_precise_for_addrTaken`: the precise-everywhere policy
satisfies its hypothesis (and is not sound). -/
theorem nonvacuous_not_policySound_of_precise_for_addrTaken :
    (fun _ => Notion.precise : Policy) true = .precise ∧ ¬ PolicySound (fun _ => .precise) :=
  ⟨rfl, not_policySound_of_precise_for_addrTaken _ rfl⟩

/-- Tightness of the hypothesis of `not_policySound_of_precise_for_addrTaken`: the mixed policy
(lexical intervals for address-taken locals, precise intervals for the other locals) does not
satisfy it, and it is sound. -/
theorem cex_not_policySound_of_precise_needs_h :
    (fun b => if b then Notion.lexical else .precise : Policy) true ≠ .precise ∧
    PolicySound (fun b => if b then .lexical else .precise) :=
  ⟨by decide, policySound_of_lexical_for_addrTaken _ rfl⟩

/-- The `CallsInBounds` clause of `ForestWF` cannot be dropped from `PolicySound`: for every
policy, `pOobCall` with the merge `1 ↦ 0.0` satisfies `ForestWFNoCallCheck` (`ForestWF` without
`CallsInBounds`) and the policy check, so with `ForestWFNoCallCheck` in place of `ForestWF` the
policy is not sound. -/
theorem not_policySoundWith_noCallCheck (pol : Policy) :
    ForestWFNoCallCheck pOobCall (single 1 0 0) ∧ PolicyCheck pol pOobCall (single 1 0 0) ∧
    ¬ PolicySoundWith ForestWFNoCallCheck PolicyCheck pol := by
  have c := cex_coalesce_needs_callsInBounds .deinit
  refine ⟨by decide, c.2.2.2.2.2.1 pol, fun h => ?_⟩
  exact c.2.2.2.2.2.2.2.2.2.2.2.2.1
    (h .deinit pOobCall (single 1 0 0) (by decide) (c.2.2.2.2.2.1 pol))

/-! ## Overlap created by coalescing -/

/-- The merge `y' ↦ y.0` turns the assignment `y' := (y.1, y.0)` of `pSwap` into the overlapping
assignment `y := (y.1, y.0)`. -/
theorem coalesce_pSwap_contains_overlap :
    Stmt.assign ⟨0, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩] ∈
      (coalesce (single 1 0 0) pSwap).body := by
  decide

/-- Under in-order field writes and every `move` semantics, every non-excluded run of the coalesced
`pSwap` prints `(2, 2)` (the source prints `(2, 1)`, `pSwap_outcome`). -/
theorem coalesce_pSwap_outcome_inOrder (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A = .done [.vals [.int 2, .int 2]] ∨
      outcome ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A = .badLayout := by
  cases ms <;> simp only [pSwap] <;> coalesce_simp <;> run_eval

/-! ## Verification-condition transfer -/

/-- Tightness of `NoValueClobberStmt` for `vc_forward_of_noValueClobber_of_classAddrDisjoint`, in
canonical form (`pClobber`, merge `x ↦ y.0`, no address-taken local): the forest is well formed,
the root-level check holds, `NoValueClobberStmt` fails, and an address-free postcondition valid for
the source is not valid for the coalesced program. -/
theorem cex_vc_forward_needs_noValueClobber_classAddrDisjoint :
    ForestWF pClobber (single 0 1 0) ∧ ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    ClassAddrDisjoint pClobber (single 0 1 0) ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    Valid semD pClobber (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    ¬ Valid semD (coalesce (single 0 1 0) pClobber)
      (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) := by
  have h := cex_vc_forward_addrFree_needs_noValueClobber
  exact ⟨h.1, h.2.1, (cex_coalesce_single_valueClobber .deinit).2.2.1, h.2.2⟩

/-- Tightness of the `CallsInBounds` clause of `ForestWF` for the forward transfer theorems, in
canonical form (`pOobCall`, merge `1 ↦ 0.0`): `ForestWF` fails, `NoValueClobberStmt` and the
root-level check hold, the trivial postcondition is address-free and valid for the source, and it
is not valid for the coalesced program. -/
theorem cex_vc_forward_needs_callsInBounds (ms : MoveSem) :
    ¬ ForestWF pOobCall (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pOobCall ∧
    ClassAddrDisjoint pOobCall (single 1 0 0) ∧ AddrFree (fun _ => True) ∧
    Valid ⟨ms, .atomic⟩ pOobCall (fun _ => True) ∧
    ¬ Valid ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) (fun _ => True) := by
  obtain ⟨_, h2, h3, _, h5, _, _, _, _, _, h11, _, _, _, _, h16⟩ :=
    cex_coalesce_needs_callsInBounds ms
  exact ⟨h2, h3, h5, fun _ _ _ => Iff.rfl, h11, h16⟩

/-! ## In-place call arguments -/

/-- Canonical form of the tightness of (a) for the in-place theorem: for `pIPAfter` at call site 4
the source run on `A0` completes, so the hypothesis "no read of `q` after the call on every layout
whose source run is neither undefined nor excluded" fails. -/
theorem pIPAfter_violates_noReadAfterCall :
    outcome semI pIPAfter A0 = .done [.vals [.int 1]] ∧
    ¬ (∀ A, outcome semI pIPAfter A ≠ .ub → outcome semI pIPAfter A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPAfter A).log 4 false qx) := by
  have h0 : outcome semI pIPAfter A0 = .done [.vals [.int 1]] := by decide
  refine ⟨h0, fun h => ?_⟩
  exact cex_upgrade_moveInPlaceCall_noReadAfterCall.2.2.2.1
    (h A0 (by rw [h0]; decide) (by rw [h0]; decide))

/-- Canonical form of the tightness of (b) for the in-place theorem: for `pIPStore` at call site 4
the source run on `A0` completes, so the hypothesis "the callee accesses no cell of `q` on every
layout whose source run is neither undefined nor excluded" fails. -/
theorem pIPStore_violates_calleeAvoids :
    outcome semI pIPStore A0 = .done [.vals [.int 1]] ∧
    ¬ (∀ A, outcome semI pIPStore A ≠ .ub → outcome semI pIPStore A ≠ .badLayout →
      CalleeAvoids (run semI pIPStore A).log 4 qx) := by
  have h0 : outcome semI pIPStore A0 = .done [.vals [.int 1]] := by decide
  refine ⟨h0, fun h => ?_⟩
  exact cex_upgrade_moveInPlaceCall_calleeAvoids.2.2.2.1
    (h A0 (by rw [h0]; decide) (by rw [h0]; decide))

end Toy.Coalesce
