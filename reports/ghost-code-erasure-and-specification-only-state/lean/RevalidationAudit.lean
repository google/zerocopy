/-
Revalidation audit for the `ToyGhost` library. This file is not part of the library target;
run it after `lake build` with

    lake env lean RevalidationAudit.lean

It prints one line per package declaration

    AXIOMS {"name": ..., "axioms": [...]}

(the axioms each declaration depends on, computed with `Lean.collectAxioms`, the same
computation as `#print axioms`), and one line per Lean name referenced by `results.json`

    STATEMENT {"name": ..., "type_repr": ..., "closure": [...]}

where `type_repr` is `repr` of the declaration's type and `closure` lists, sorted, one
entry `c : <repr of type>` (followed by ` := <repr of value>` unless `c` is a theorem) for
every constant of the `ToyGhost` modules reachable from the statement through types,
definition values and inductive constructors. Theorem bodies are excluded, so proofs can
change without changing either hash. The statement hash is the SHA-256 of `type_repr`;
the closure hash is the SHA-256 of the closure entries joined by newlines.
-/
import Lean
import ToyGhost
open Lean Elab Command

private def pkgRoots : List Name := [`ToyGhost]
private def cardNames : List Name := [
  `Toy.Ghost.dataFlow_breaks_erasure,
  `Toy.Ghost.demo_satisfies_erasure_hypotheses,
  `Toy.Ghost.demo_satisfies_global_erasure_hypotheses,
  `Toy.Ghost.erase_rbehaves_iff_needs_ghostNoDivergeFrom,
  `Toy.Ghost.erase_rbehaves_iff_needs_ghostNoFailFrom,
  `Toy.Ghost.erase_rbehaves_iff_needs_ghostWritesGhost,
  `Toy.Ghost.erase_rbehaves_iff_needs_realReadsReal,
  `Toy.Ghost.erase_rbehaves_iff_needs_same_realPart,
  `Toy.Ghost.erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom,
  `Toy.Ghost.erase_refinesUpTo_abortBot_needs_ghostWritesGhost,
  `Toy.Ghost.erase_refinesUpTo_abortBot_needs_realReadsReal,
  `Toy.Ghost.erase_refinesUpTo_abortBot_needs_same_realPart,
  `Toy.Ghost.erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal,
  `Toy.Ghost.erase_refinesUpTo_divBot_needs_ghostNoFailFrom,
  `Toy.Ghost.erase_refinesUpTo_divBot_needs_ghostWritesGhost,
  `Toy.Ghost.erase_refinesUpTo_divBot_needs_realReadsReal,
  `Toy.Ghost.erase_refinesUpTo_divBot_needs_same_realPart,
  `Toy.Ghost.erase_refinesUpTo_divBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoFailFrom,
  `Toy.Ghost.erase_refinesUpTo_failBot_needs_ghostNoDivergeFrom,
  `Toy.Ghost.erase_refinesUpTo_failBot_needs_ghostWritesGhost,
  `Toy.Ghost.erase_refinesUpTo_failBot_needs_realReadsReal,
  `Toy.Ghost.erase_refinesUpTo_failBot_needs_same_realPart,
  `Toy.Ghost.erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom,
  `Toy.Ghost.erasureAgrees_not_sufficient_for_erasureExact,
  `Toy.Ghost.erasureExact_iff_erasureAgrees_needs_realReadsReal,
  `Toy.Ghost.erasureExact_iff_erasureAgrees_of_realReadsReal,
  `Toy.Ghost.erasureExact_iff_ghostToRealNI_and_erasureAgrees,
  `Toy.Ghost.erasureExact_needs_ghostNoDivergeFrom,
  `Toy.Ghost.erasureExact_needs_ghostNoFailFrom,
  `Toy.Ghost.erasureExact_needs_ghostWritesGhost,
  `Toy.Ghost.erasureExact_needs_realReadsReal,
  `Toy.Ghost.erasureExact_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom,
  `Toy.Ghost.ghostDivergence_breaks_erasure,
  `Toy.Ghost.ghostFailure_breaks_erasure,
  `Toy.Ghost.ghostSpinOnX_ghostToRealNI_not_erasureExact,
  `Toy.Ghost.ghostThenRealFail_satisfies_erasure_hypotheses,
  `Toy.Ghost.ghostThenSpin_satisfies_erasure_hypotheses,
  `Toy.Ghost.ghostToRealNI_abortInsensitive_ghostSpinOnG,
  `Toy.Ghost.ghostToRealNI_abortInsensitive_needs_ghostWritesGhost,
  `Toy.Ghost.ghostToRealNI_abortInsensitive_needs_realReadsReal,
  `Toy.Ghost.ghostToRealNI_abortInsensitive_of_ghostWritesGhost_of_realReadsReal,
  `Toy.Ghost.ghostToRealNI_needs_ghostNoDivergeFrom,
  `Toy.Ghost.ghostToRealNI_needs_ghostNoFailFrom,
  `Toy.Ghost.ghostToRealNI_needs_ghostWritesGhost,
  `Toy.Ghost.ghostToRealNI_needs_realReadsReal,
  `Toy.Ghost.ghostToRealNI_not_sufficient_for_erasureExact,
  `Toy.Ghost.ghostToRealNI_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom,
  `Toy.Ghost.ghostWriteToReal_breaks_erasure,
  `Toy.Ghost.ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI,
  `Toy.Ghost.implicitFlow_breaks_erasure,
  `Toy.Ghost.loopDemo_satisfies_global_erasure_hypotheses,
  `Toy.Ghost.pcGhostPassingAssert_erasureExact,
  `Toy.Ghost.pcGhostTerminatingLoop_erasureExact,
  `Toy.Ghost.pcGhostWritesGhost_erasureExact,
  `Toy.Ghost.pcGhostWritesGhost_realReadsReal_erasureAgrees_erasureExact,
  `Toy.Ghost.pcRealBranch_erasureExact,
  `Toy.Ghost.pcRealDataFlow_erasureExact,
  `Toy.Ghost.safePartialTriple_erase_hypotheses_satisfiable,
  `Toy.Ghost.safePartialTriple_erase_needs_ghostNoDivergeFrom,
  `Toy.Ghost.safePartialTriple_erase_needs_ghostWritesGhost,
  `Toy.Ghost.safePartialTriple_erase_needs_realReadsReal,
  `Toy.Ghost.safePartialTriple_erase_needs_safePartialTriple,
  `Toy.Ghost.safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom,
  `Toy.Ghost.safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom,
  `Toy.Ghost.totalTriple_erase_hypotheses_satisfiable,
  `Toy.Ghost.totalTriple_erase_needs_ghostWritesGhost,
  `Toy.Ghost.totalTriple_erase_needs_realReadsReal,
  `Toy.Ghost.totalTriple_erase_needs_totalTriple,
  `Toy.Ghost.totalTriple_erase_of_ghostWritesGhost_of_realReadsReal,
  `Toy.Ghost.weakPartialTriple_erase_hypotheses_satisfiable,
  `Toy.Ghost.weakPartialTriple_erase_needs_ghostNoDivergeFrom,
  `Toy.Ghost.weakPartialTriple_erase_needs_ghostNoFailFrom,
  `Toy.Ghost.weakPartialTriple_erase_needs_ghostWritesGhost,
  `Toy.Ghost.weakPartialTriple_erase_needs_realReadsReal,
  `Toy.Ghost.weakPartialTriple_erase_needs_weakPartialTriple,
  `Toy.Ghost.weakPartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom_ghostNoFailFrom]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => pkgRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      IO.println ("AXIOMS " ++ (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson ((axs.map Name.toString).qsort (· < ·)))]).compress)
  for n in cardNames do
    match env.find? n with
    | none => IO.println ("STATEMENT " ++ (Json.mkObj [("name", toJson n.toString),
        ("missing", toJson true)]).compress)
    | some ci =>
      let cl := closure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println ("STATEMENT " ++ (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))]).compress)
