import Lean
import DropElaborationRefinement

/-!
# Audit of `DropElaborationRefinement`

Run after compiling `DropElaborationRefinement.lean` to an `.olean` (see `check_lean.py`).
It inspects every constant that the module itself declares and fails if any of them

* is an axiom, an `opaque` constant, or a definition whose safety is not `safe` (which covers
  non-terminating and non-kernel-checked definitions and the compiler helpers named
  `_unsafe_rec`);
* has a name containing `_unsafe_rec`;
* is a theorem whose proof depends on an axiom other than `propext` and `Quot.sound`
  (so the placeholder axiom, the choice axiom and the native-evaluation axiom are all rejected).

On success it prints one JSON object with the counts.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_drop_elaboration" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `DropElaborationRefinement
    | throwError "module DropElaborationRefinement is not imported"
  let mut theorems := 0
  let mut definitions := 0
  let mut inductives := 0
  let mut constructors := 0
  let mut recursors := 0
  let mut total := 0
  let mut violations : Array String := #[]
  let mut axiomsSeen : Array Name := #[]
  let mut axiomFree := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some modIdx then continue
    total := total + 1
    if (n.toString.splitOn "_unsafe_rec").length > 1 then
      violations := violations.push s!"unsafe_rec helper: {n}"
    match ci with
    | .axiomInfo _ => violations := violations.push s!"axiom: {n}"
    | .opaqueInfo _ => violations := violations.push s!"opaque constant: {n}"
    | .quotInfo _ => violations := violations.push s!"quot constant: {n}"
    | .defnInfo d =>
      definitions := definitions + 1
      if d.safety != .safe then violations := violations.push s!"non-safe definition: {n}"
    | .thmInfo _ =>
      theorems := theorems + 1
      let axs ← collectAxioms n
      if axs.isEmpty then axiomFree := axiomFree + 1
      for a in axs do
        if !axiomsSeen.contains a then axiomsSeen := axiomsSeen.push a
        if !allowedAxioms.contains a then
          violations := violations.push s!"theorem {n} depends on axiom {a}"
    | .inductInfo _ => inductives := inductives + 1
    | .ctorInfo _ => constructors := constructors + 1
    | .recInfo _ => recursors := recursors + 1
  let axiomNames := axiomsSeen.toList.map (fun a => s!"\"{a}\"")
  let json := "{" ++ s!"\"constants\": {total}, \"theorems\": {theorems}, " ++
    s!"\"theorems_without_axioms\": {axiomFree}, \"definitions\": {definitions}, " ++
    s!"\"inductive_types\": {inductives}, \"constructors\": {constructors}, " ++
    s!"\"recursors\": {recursors}, \"axioms_used\": [{", ".intercalate axiomNames}], " ++
    s!"\"violations\": {violations.size}" ++ "}"
  logInfo m!"AUDIT {json}"
  unless violations.isEmpty do
    throwError "audit failed:\n{"\n".intercalate violations.toList}"

#audit_drop_elaboration

#print axioms DropElab.elaborate_refines
#print axioms DropElab.elaborate_refines_blind
#print axioms DropElab.elaborate_no_double_drop
#print axioms DropElab.elaborate_no_leak
#print axioms DropElab.double_panic_aborts
#print axioms DropElab.no_flagFree_ladder_is_conditional
#print axioms DropElab.Example.ce1_no_flag_always_drop_double_drop
#print axioms DropElab.Example.ce1_no_flag_never_drop_leak
#print axioms DropElab.Example.ce2_continue_lowering_unwinds
#print axioms DropElab.Example.ce2_continue_is_not_a_refinement
#print axioms DropElab.Example.staleFlagJoin_double_drop
#print axioms DropElab.Example.trace_before_abort_depends_on_certificate
