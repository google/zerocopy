/-
Library-scale "print, re-parse, re-elaborate, compare terms" probe.

For every theorem declared in a module whose name starts with a given prefix
(default `Init`), the probe:
  1. pretty-prints the theorem's type with default `pp` options in the root
     namespace with no `open` declarations (string S1);
  2. parses S1 as a `term` with the environment's own parser tables;
  3. elaborates the syntax as a type, with the theorem's universe parameter
     names in scope, and instantiates metavariables (term E2);
  4. compares E2 with the stored type E1:
       exact    : `E2 == E1` (Lean's `Expr.eqv`: alpha-equivalence; binder
                  names and binder annotations ignored)
       defeq    : not exact, but `Meta.isDefEq E2 E1` at default transparency
       differ   : `isDefEq` returned false
       mvar     : E2 still contains (expression or universe) metavariables
       elabfail : elaboration threw an error
       parsefail: S1 did not parse
  5. pretty-prints E2 again (string S2) and records whether S1 = S2, i.e. the
     verdict of a purely textual print/re-parse/print round trip.

Output: one TSV row per theorem on stdout, then summary lines prefixed `#`.
Usage:  lean --run ReelabProbe.lean [modulePrefix] [limit]
-/
import Lean
open Lean Meta Elab

structure Row where
  name     : Name
  modName  : Name
  status   : String
  textSame : String
  nsPP     : Nat
  nsParse  : Nat
  nsElab   : Nat
  nsCmp    : Nat
  len      : Nat
  detail   : String

def clean (s : String) : String :=
  (s.replace "\t" " ").replace "\n" " "

def takeS (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

def runCore {α} (env : Environment) (x : CoreM α) (opts : Options := {}) : IO (Except String α) := do
  let ctx : Core.Context := {
    fileName := "<reelab-probe>", fileMap := default, options := opts,
    maxHeartbeats := 200000 * 1000 }
  let st : Core.State := { env := env }
  try
    let (a, _) ← x.toIO ctx st
    return .ok a
  catch e =>
    return .error (toString e)

def ppStr (e : Expr) : MetaM String := do
  let f ← ppExpr e
  return f.pretty 1000000

def nowNs : IO Nat := IO.monoNanosNow

/-- Remove all metadata nodes, so that `==` compares only logical structure. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- Locate the first pair of differing subterms (function part before argument). -/
partial def firstDiff (a b : Expr) : Option (Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app f1 x1, .app f2 x2 =>
    if f1 == f2 then firstDiff x1 x2
    else match firstDiff f1 f2 with
      | some d => some d
      | none => firstDiff x1 x2
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
    if t1 == t2 then firstDiff b1 b2 else firstDiff t1 t2
  | .lam _ t1 b1 _, .lam _ t2 b2 _ =>
    if t1 == t2 then firstDiff b1 b2 else firstDiff t1 t2
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    if t1 != t2 then firstDiff t1 t2 else if v1 != v2 then firstDiff v1 v2 else firstDiff b1 b2
  | .proj _ i1 x1, .proj _ i2 x2 => if i1 == i2 then firstDiff x1 x2 else some (a, b)
  | _, _ => some (a, b)

def showDiff (a b : Expr) : String :=
  match firstDiff a b with
  | some (x, y) => s!"DIFF[{takeS (toString x) 160} ~~ {takeS (toString y) 160}]"
  | none => "DIFF[none]"

def ppOptions (mode : String) : Options :=
  match mode with
  | "proofs"   => ({} : Options).setBool `pp.proofs true
  | "explicit" => (({} : Options).setBool `pp.explicit true).setBool `pp.proofs true
  | "targeted" => ((({} : Options).setBool `pp.proofs true).setBool `pp.numericTypes true).setBool `pp.funBinderTypes true
  | _          => {}

def probeOne (env : Environment) (mode : String) (modName : Name) (ci : ConstantInfo) : IO Row := do
  let n := ci.name
  let t1 := ci.type
  -- 1. print
  let a0 ← nowNs
  let s1? ← runCore env (MetaM.run' (ppStr t1)) (ppOptions mode)
  let a1 ← nowNs
  match s1? with
  | .error msg =>
    return { name := n, modName, status := "ppfail", textSame := "na", nsPP := a1 - a0,
             nsParse := 0, nsElab := 0, nsCmp := 0, len := 0, detail := clean (takeS msg 200) }
  | .ok s1 =>
  -- 2. parse
  let b0 ← nowNs
  let stx? := Parser.runParserCategory env `term s1
  let b1 ← nowNs
  match stx? with
  | .error msg =>
    return { name := n, modName, status := "parsefail", textSame := "na", nsPP := a1 - a0,
             nsParse := b1 - b0, nsElab := 0, nsCmp := 0, len := s1.length,
             detail := clean (takeS msg 200) ++ " || " ++ clean (takeS s1 300) }
  | .ok stx =>
  -- 3. elaborate, then 4./5. compare and re-print, all in one metavariable context
  let res? ← runCore (opts := ppOptions mode) env <| MetaM.run' <| Term.TermElabM.run' do
    let c0 ← IO.monoNanosNow
    let e2? ← try
        let e ← Term.withoutErrToSorry <| Term.withLevelNames ci.levelParams do
          let e ← Term.elabType stx
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        pure (Except.ok e)
      catch ex => pure (Except.error (← ex.toMessageData.toString))
    let c1 ← IO.monoNanosNow
    match e2? with
    | .error msg => return (c1 - c0, 0, "elabfail", "na", clean (takeS msg 200) ++ " || " ++ clean (takeS s1 300))
    | .ok e2 =>
      let s2 ← ppStr e2
      let st ← if e2.hasMVar || e2.hasLevelMVar then pure "mvar"
        else if stripMData e2 == stripMData t1 then pure "exact"
        else do
          let ok ← withTransparency .default (isDefEq e2 t1)
          pure (if ok then "defeq" else "differ")
      let d1 ← IO.monoNanosNow
      let same := if s1 == s2 then "same" else "changed"
      let dd := if st == "defeq" || st == "differ" then showDiff (stripMData e2) (stripMData t1) else ""
      let det := if st == "exact" && same == "same" then "" else
        clean dd ++ " || " ++ clean (takeS s1 300) ++ " ==> " ++ clean (takeS s2 300)
      return (c1 - c0, d1 - c1, st, same, det)
  match res? with
  | .error msg =>
    return { name := n, modName, status := "cmpfail", textSame := "na", nsPP := a1 - a0,
             nsParse := b1 - b0, nsElab := 0, nsCmp := 0, len := s1.length,
             detail := clean (takeS msg 200) ++ " || " ++ clean (takeS s1 300) }
  | .ok (te, tc, st, same, det) =>
    return { name := n, modName, status := st, textSame := same, nsPP := a1 - a0,
             nsParse := b1 - b0, nsElab := te, nsCmp := tc, len := s1.length, detail := det }

unsafe def main (args : List String) : IO UInt32 := do
  let pfx := (args.getD 0 "Init")
  let limit := (args.getD 1 "0").toNat!
  let mode := (args.getD 2 "default")
  IO.println s!"# mode\t{mode}"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← nowNs
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let t1 ← nowNs
  IO.println s!"# import_ms\t{(t1 - t0) / 1000000}"
  let pfxName := pfx.toName
  -- collect candidate theorems
  let mut cands : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    match ci with
    | .thmInfo _ =>
      if n.isInternal || isPrivateName n then continue
      match env.getModuleIdxFor? n with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        if pfxName.isPrefixOf m then
          cands := cands.push (m, ci)
      | none => pure ()
    | _ => pure ()
  cands := cands.qsort (fun a b => Name.quickLt a.2.name b.2.name)
  if limit > 0 then cands := cands.extract 0 limit
  IO.println s!"# candidates\t{cands.size}"
  IO.println "name\tmodule\tstatus\ttext_roundtrip\tns_pp\tns_parse\tns_elab\tns_cmp\tlen\tdetail"
  let mut counts : Std.HashMap String Nat := {}
  let mut cross : Std.HashMap String Nat := {}
  let mut totPP := 0
  let mut totParse := 0
  let mut totElab := 0
  let mut totCmp := 0
  let w0 ← nowNs
  for (m, ci) in cands do
    let r ← probeOne env mode m ci
    IO.println s!"{r.name}\t{r.modName}\t{r.status}\t{r.textSame}\t{r.nsPP}\t{r.nsParse}\t{r.nsElab}\t{r.nsCmp}\t{r.len}\t{r.detail}"
    counts := counts.insert r.status (counts.getD r.status 0 + 1)
    let k := r.status ++ "/" ++ r.textSame
    cross := cross.insert k (cross.getD k 0 + 1)
    totPP := totPP + r.nsPP
    totParse := totParse + r.nsParse
    totElab := totElab + r.nsElab
    totCmp := totCmp + r.nsCmp
  let w1 ← nowNs
  for (k, v) in counts.toList do
    IO.println s!"# status\t{k}\t{v}"
  for (k, v) in cross.toList do
    IO.println s!"# cross\t{k}\t{v}"
  IO.println s!"# total_ms\tpp={totPP / 1000000}\tparse={totParse / 1000000}\telab={totElab / 1000000}\tcmp={totCmp / 1000000}\twall={(w1 - w0) / 1000000}"
  return 0
