/-
Revalidation audit for the `ToyRice` library (not part of the library target; run with
`lake env lean RevalidationAudit.lean` after `lake build`).

For every Lean name referenced by `results.json` it prints one line

  STMT {"name": ..., "axioms": [...], "type_repr": ..., "closure": [...]}

where `axioms` is the result of `Lean.collectAxioms`, `type_repr` is `repr` of the declaration's
type, and `closure` lists, sorted, `<name> : <repr of type>` (followed by ` := <repr of value>` for
non-theorems) for every `ToyRice` constant reachable from the statement through types, definition
values and inductive constructors (theorem bodies are not followed). The SHA-256 of `type_repr` and
of the newline-joined `closure` are the statement and closure hashes recorded in
`audit/statements.json`. A final line `DECLS <n> OUTSIDE_ALLOWED <m>` reports how many `ToyRice`
declarations were audited and how many depend on an axiom other than `propext`,
`Classical.choice`, `Quot.sound`.
-/
import Lean
import ToyRice
open Lean Elab Command

private def auditRoots : List Name := [`ToyRice]
private def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]
private def cardNames : List Name := [
  `Toy.Rice.Controls.allAdm_nonvacuous,
  `Toy.Rice.Controls.allAdm_tight_nonempty,
  `Toy.Rice.Controls.cantor_nonvacuous,
  `Toy.Rice.Controls.cantor_tight_surjective,
  `Toy.Rice.Controls.converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided,
  `Toy.Rice.Controls.incompleteAll_nonvacuous,
  `Toy.Rice.Controls.incompleteAll_tight_extensional,
  `Toy.Rice.Controls.incompleteAll_tight_fixpointPrinciple,
  `Toy.Rice.Controls.incompleteAll_tight_sound,
  `Toy.Rice.Controls.incompleteAll_tight_switchAdmissible,
  `Toy.Rice.Controls.incompleteAll_tight_violated,
  `Toy.Rice.Controls.rejectAll_nonvacuous,
  `Toy.Rice.Controls.rejectAll_tight_constClosed,
  `Toy.Rice.Controls.restrict_nonvacuous,
  `Toy.Rice.Controls.restrict_tight_eqTestClosed,
  `Toy.Rice.Controls.restrict_tight_extensional,
  `Toy.Rice.Controls.restrict_tight_extensionalFragment,
  `Toy.Rice.Controls.restrict_tight_fixpointPrinciple,
  `Toy.Rice.Controls.restrict_tight_hasMember,
  `Toy.Rice.Controls.restrict_tight_hasNonMember,
  `Toy.Rice.Controls.riceChar_nonvacuous,
  `Toy.Rice.Controls.riceChar_tight_constClosed,
  `Toy.Rice.Controls.riceChar_tight_extensional,
  `Toy.Rice.Controls.riceChar_tight_fixpointPrinciple,
  `Toy.Rice.Controls.riceSharp_nonvacuous,
  `Toy.Rice.Controls.riceSharp_tight_decides,
  `Toy.Rice.Controls.riceSharp_tight_extensional,
  `Toy.Rice.Controls.riceSharp_tight_fixpointPrinciple,
  `Toy.Rice.Controls.riceSharp_tight_member,
  `Toy.Rice.Controls.riceSharp_tight_nonmember,
  `Toy.Rice.Controls.rice_nonvacuous,
  `Toy.Rice.Controls.rice_tight_extensional,
  `Toy.Rice.Controls.rice_tight_fixpointPrinciple,
  `Toy.Rice.Controls.rice_tight_nontrivial_hasMember,
  `Toy.Rice.Controls.rice_tight_nontrivial_hasNonMember,
  `Toy.Rice.Controls.semConst_nonvacuous,
  `Toy.Rice.Controls.semConst_tight_allSwitches,
  `Toy.Rice.Controls.semConst_tight_fixpointPrinciple,
  `Toy.Rice.Controls.soundSplit_nonvacuous,
  `Toy.Rice.Controls.soundSplit_tight_accepts,
  `Toy.Rice.Controls.soundSplit_tight_extensional,
  `Toy.Rice.Controls.soundSplit_tight_fixpointPrinciple,
  `Toy.Rice.Controls.soundSplit_tight_rejects,
  `Toy.Rice.Controls.soundSplit_tight_sound,
  `Toy.Rice.Controls.soundSplit_tight_switchAdmissible,
  `Toy.Rice.Controls.splitAll_nonvacuous,
  `Toy.Rice.Controls.splitAll_tight_fixpointPrinciple,
  `Toy.Rice.Controls.splitAll_tight_switchAdmissible,
  `Toy.Rice.Flat.flat_fixpointPrinciple_and_halts_not_decidedInside,
  `Toy.Rice.Flat.halts_unswappedSwitch_admissible_not_decidedInside,
  `Toy.Rice.Lifted.lifted_haltsZero_decidedInside_haltingFragment_not_full,
  `Toy.Rice.Models.kleene_nonvacuous,
  `Toy.Rice.Models.kleene_tight_diagonal,
  `Toy.Rice.Models.kleene_tight_precompClosed,
  `Toy.Rice.Models.kleene_tight_represents,
  `Toy.Rice.Models.lawvere_nonvacuous,
  `Toy.Rice.Models.lawvere_tight_diagonal,
  `Toy.Rice.Models.lawvere_tight_represents,
  `Toy.Rice.Padded.padded_fixpointPrinciple_and_evenPad_decidedInside,
  `Toy.Rice.Padded.padded_litTrueCheck_sound_infinite_incomplete,
  `Toy.Rice.Tables.tables_no_fixpointPrinciple_and_isZeroFn_decidedInside,
  `Toy.Rice.decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional,
  `Toy.Rice.diagonalFixedPoint_of_represents_diagonal_precompClosed,
  `Toy.Rice.exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible,
  `Toy.Rice.exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible,
  `Toy.Rice.fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty,
  `Toy.Rice.forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible,
  `Toy.Rice.lawvere_fixedPoint_of_represents_diagonal,
  `Toy.Rice.nonempty_subsingleton_of_weaklyPointSurjective,
  `Toy.Rice.not_decidedInside_of_fixpointPrinciple_extensional_nontrivial,
  `Toy.Rice.not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial,
  `Toy.Rice.rejectAll_sound_switchAdmissible_of_constClosed,
  `Toy.Rice.sem_constant_of_fixpointPrinciple_allSwitchesAdmissible,
  `Toy.Rice.swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides
]

private def inLibrary (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => auditRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def closureOf (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLibrary env n then closureOf env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closureOf env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closureOf env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in cardNames do
    match env.find? n with
    | none => IO.println ("MISSING " ++ n.toString)
    | some ci =>
      let axs ← collectAxioms n
      let cl := closureOf env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println ("STMT " ++ (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString)),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))]).compress)
  let mut total := 0
  let mut outside := 0
  for (n, _) in env.constants.toList do
    if inLibrary env n && !n.isInternal then
      total := total + 1
      let axs ← collectAxioms n
      if axs.any (fun a => !allowedAxioms.contains a) then
        outside := outside + 1
        IO.println ("OUTSIDE_ALLOWED " ++ n.toString ++ " " ++ toString (axs.toList))
  IO.println ("DECLS " ++ toString total ++ " OUTSIDE_ALLOWED " ++ toString outside)
