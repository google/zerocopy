/- A standalone Lean axiom-collector probe, not an ISA model or Sail theorem. -/
namespace AnnealAuditProbe
axiom opaqueHook : Nat → Nat

def dispatch (useHook : Bool) (n : Nat) : Nat :=
  if useHook then opaqueHook n else n + 1

theorem selected_branch (n : Nat) : dispatch false n = n + 1 := by rfl

-- Explicit hook parameters let the theorem quantify over every hook.
def parametricDispatch (hook : Nat → Nat) (useHook : Bool) (n : Nat) : Nat :=
  if useHook then hook n else n + 1

theorem parametric_branch (hook : Nat → Nat) (n : Nat) :
    parametricDispatch hook false n = n + 1 := by rfl

#print selected_branch
#print axioms selected_branch
#print parametric_branch
#print axioms parametric_branch
end AnnealAuditProbe
