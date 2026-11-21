import ToyCoalesce.Staging

/-!
# Transfer of verification conditions across coalescing

A postcondition is a predicate on the event trace. `Valid sem P Post` is total correctness over
all non-excluded runs: no undefined behaviour, and every completed trace satisfies `Post`.
A postcondition is *address-free* if it gives the same verdict on traces that agree after erasing printed
addresses and pointer-comparison results.
-/

namespace Toy.Coalesce

/-- Every non-excluded run of `P` completes without undefined behaviour and its trace satisfies
`Post`. -/
def Valid (sem : Sem) (P : Prog) (Post : List Event → Prop) : Prop :=
  ∀ o, Beh sem P o → ∃ t, o = .done t ∧ Post t

/-- Erase the address-dependent parts of an event: printed addresses become `0`, comparison
results become `false`. -/
def Event.erase : Event → Event
  | .vals vs => .vals (vs.map fun v => match v with | .int n => .int n | .addr _ => .addr 0)
  | .cmp _ => .cmp false

/-- `Post` does not mention addresses or pointer-comparison results. -/
def AddrFree (Post : List Event → Prop) : Prop :=
  ∀ t t', t.map Event.erase = t'.map Event.erase → (Post t ↔ Post t')

/-- `P` has no undefined behaviour on any non-excluded run. -/
def UBFree (sem : Sem) (P : Prog) : Prop := ¬ Beh sem P .ub

/-! ## Main statements -/

/-- Validity transfers forward along any refinement. -/
theorem valid_of_refines {semT semS : Sem} {T S : Prog} {Post : List Event → Prop}
    (h : Refines semT T semS S) (hv : Valid semS S Post) : Valid semT T Post := by
  intro o ho
  rcases h o ho with hub | hS
  · obtain ⟨t, ht, _⟩ := hv .ub hub
    cases ht
  · exact hv o hS

end Toy.Coalesce
