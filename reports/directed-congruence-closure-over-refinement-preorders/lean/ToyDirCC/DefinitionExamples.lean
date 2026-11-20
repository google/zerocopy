import ToyDirCC.NonVacuity

/-!
# Direct examples for `PolicySound`

`PolicySound Op P pol` says that every certificate accepted by the checker under policy
`pol` proves a true refinement in every model satisfying `LeRefl`, `LeTrans`, `MonoAt P`
and `KerAt P`. These examples state its intended positive and negative instances directly
on `PolicySound` (rather than on `Policy.AdmissibleFor`).
-/

namespace Toy.DirCC

/-- Positive example (`PolicySound`): the standard policy (one-sided congruence only at
`mono` positions, two-sided congruence only at `mono` and `eqOnly` positions) is sound for
the outcome profile `oProfile`. -/
theorem policySound_standard_oProfile : PolicySound OOp oProfile Policy.standard :=
  (policySound_iff_admissibleFor oProfile Policy.standard).mpr
    (Policy.standard_admissibleFor oProfile)

/-- Negative example (`PolicySound`): the permissive policy (congruence of both kinds at
every position) is not sound for `oProfile`, which has `eqOnly` and `opaqueArg` positions. -/
theorem not_policySound_permissive_oProfile : ¬ PolicySound OOp oProfile Policy.permissive :=
  fun h => policySound_nonvacuous.2
    ((policySound_iff_admissibleFor oProfile Policy.permissive).mp h)

/-- Edge case (`PolicySound`): over an operator type with no operators, every policy is
sound, the permissive one included; soundness of a policy depends on the profile. -/
theorem policySound_permissive_of_empty_op :
    PolicySound Empty (fun f => Empty.elim f) Policy.permissive :=
  (policySound_iff_admissibleFor _ _).mpr ⟨fun f => Empty.elim f, fun f => Empty.elim f⟩

end Toy.DirCC
