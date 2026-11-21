import ToyCoalesce.PfLicensed
import ToyCoalesce.PfUF
import ToyCoalesce.PfStage
import ToyCoalesce.PfPolicy

/-!
# Compositions of the main results
-/

namespace Toy.Coalesce

/-- Sufficiency for the single merge `x ↦ y.f` under atomic assignments and any `move` semantics:
if the forest is well formed, `NoValueClobberStmt` holds, and, if `x` and `y` are both
address-taken, they are never lexically allocated during a common tick, then the coalesced
program refines the source (a specialization of the forest theorem). -/
theorem coalesce_single_refines_of_noValueClobber_of_lexDisjoint_addrTaken (ms : MoveSem)
    (P : Prog) (x y f : Nat) (hwf : ForestWF P (single x y f))
    (hi : NoValueClobberStmt ms (single x y f) P)
    (hii : AddrTaken P x → AddrTaken P y → ¬ LexOverlap P x y) :
    Refines ⟨ms, .atomic⟩ (coalesce (single x y f) P) ⟨ms, .atomic⟩ P :=
  coalesce_refines_of_noValueClobber_of_classAddrDisjoint ms P (single x y f) hwf hi
    (classAddrDisjoint_single_of_lexDisjoint P x y f hii)

/-- The coalesce-then-stage pipeline under in-order field writes: a well-formed forest,
`NoValueClobberStmt`, the root-level address check, no assignment of the source needing staging,
no callee assignment of the coalesced program needing staging, and every callee parameter local
existing give a refinement of the source under in-order field writes. -/
theorem stage_coalesce_refines_inOrder (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hii : ClassAddrDisjoint P μ)
    (hns : NoStagingNeeded P) (hc : CalleesNoStaging (coalesce μ P)) (hp : ParamsInRange P) :
    Refines ⟨ms, .inOrder⟩ (stage (coalesce μ P)) ⟨ms, .inOrder⟩ P :=
  Refines.trans (stage_inOrder_refines_atomic ms (coalesce μ P) hc (paramsInRange_coalesce μ P hp))
    (Refines.trans (coalesce_refines_of_noValueClobber_of_classAddrDisjoint ms P μ hwf hi hii)
      (refines_of_outcome_eq fun A => (outcome_inOrder_eq_atomic_of_noStagingNeeded ms P hns A).symm))

/-- A coalescer that respects the no-overlap constraint (no assignment of the coalesced program
needs staging) needs no staging pass: for a well-formed forest with `NoValueClobberStmt` and the
root-level address check, the coalesced program refines the source under in-order field writes. -/
theorem coalesce_refines_inOrder_of_noStagingNeeded (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hii : ClassAddrDisjoint P μ)
    (hnc : NoStagingNeeded (coalesce μ P)) :
    Refines ⟨ms, .inOrder⟩ (coalesce μ P) ⟨ms, .inOrder⟩ P :=
  Refines.trans
    (refines_of_outcome_eq fun A => outcome_inOrder_eq_atomic_of_noStagingNeeded ms _ hnc A)
    (Refines.trans (coalesce_refines_of_noValueClobber_of_classAddrDisjoint ms P μ hwf hi hii)
      (refines_of_outcome_eq fun A =>
        (outcome_inOrder_eq_atomic_of_noStagingNeeded ms P
          (noStagingNeeded_of_noStagingNeeded_coalesce P μ hwf hnc) A).symm))

/-- Arbitrary (possibly address-mentioning) postconditions, original to coalesced:
`NoValueClobberStmt` and the root-level address check `ClassAddrDisjoint` transfer validity
forward (through the refinement of the forest theorem). -/
theorem vc_forward_of_noValueClobber_of_classAddrDisjoint (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hii : ClassAddrDisjoint P μ)
    (Post : List Event → Prop) (hv : Valid ⟨ms, .atomic⟩ P Post) :
    Valid ⟨ms, .atomic⟩ (coalesce μ P) Post :=
  valid_of_refines (coalesce_refines_of_noValueClobber_of_classAddrDisjoint ms P μ hwf hi hii) hv

end Toy.Coalesce
