/-
Print / re-parse / re-elaborate / compare probe for theorem statements.

For every theorem whose defining module is in the selected module prefixes,
the probe:
  1. delaborates and formats the statement (`ConstantInfo.type`) with the
     pretty-printer options of the selected variant;
  2. re-parses the printed string as a `term` with `Parser.runParserCategory`;
  3. re-elaborates it with `Term.elabType` (autoImplicit disabled, the
     declaration's universe parameters in scope, root namespace, no `open`s);
  4. compares the result with the original statement.

Outcome classes (first failing stage wins):
  delabErr   the delaborator/formatter threw
  omission   printed text contains the elision token `⋯`
  parseErr   the printed text does not parse as a term
  elabErr    elaboration threw, logged an error, or left `sorry`/mvars
  notDefEq   elaborated term is not definitionally equal (default transparency)
  defEqOnly  definitionally equal but not alpha-equivalent (`Expr.eqv`)
  eqvOnly    alpha-equivalent but binder annotations differ (`Expr.equal` after
             erasing binder names)
  exact      alpha-equivalent with identical binder annotations
Every stage runs under a fresh heartbeat budget (maxHeartbeats 200000); a
heartbeat or recursion limit counts as an error at the stage where it happened.
The full elaborator state is saved before and restored after each theorem, so
no metavariables, postponed constraints, or auxiliary declarations leak from
one theorem's round trip into the next.
-/
import Lean
open Lean Elab Term Meta Command

namespace RTProbe

inductive Outcome where
  | delabErr | omission | parseErr | elabErr | notDefEq | defEqOnly | mdataOnly | eqvOnly | exact
  deriving Inhabited, BEq, Repr

def Outcome.idx : Outcome → Nat
  | .delabErr => 0 | .omission => 1 | .parseErr => 2 | .elabErr => 3
  | .notDefEq => 4 | .defEqOnly => 5 | .mdataOnly => 6 | .eqvOnly => 7 | .exact => 8

def Outcome.name : Outcome → String
  | .delabErr => "delabErr" | .omission => "omission" | .parseErr => "parseErr"
  | .elabErr => "elabErr" | .notDefEq => "notDefEq" | .defEqOnly => "defEqOnly"
  | .mdataOnly => "mdataOnly" | .eqvOnly => "eqvOnly" | .exact => "exact"

def allOutcomes : List Outcome :=
  [.delabErr, .omission, .parseErr, .elabErr, .notDefEq, .defEqOnly, .mdataOnly, .eqvOnly, .exact]

/-- Replace every binder name by `_` so that `Expr.equal` compares binder
annotations but not names. -/
partial def eraseBinderNames : Expr → Expr
  | .forallE _ t b bi => .forallE `_ (eraseBinderNames t) (eraseBinderNames b) bi
  | .lam _ t b bi     => .lam `_ (eraseBinderNames t) (eraseBinderNames b) bi
  | .letE _ t v b nd  => .letE `_ (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nd
  | .app f a          => .app (eraseBinderNames f) (eraseBinderNames a)
  | .mdata _ e        => eraseBinderNames e
  | .proj s i e       => .proj s i (eraseBinderNames e)
  | e                 => e

/-- Remove every `Expr.mdata` node. -/
partial def stripMData : Expr → Expr
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .lam n t b bi     => .lam n (stripMData t) (stripMData b) bi
  | .letE n t v b nd  => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .app f a          => .app (stripMData f) (stripMData a)
  | .mdata _ e        => stripMData e
  | .proj s i e       => .proj s i (stripMData e)
  | e                 => e

/-- First pair of corresponding subterms that are not alpha-equivalent. -/
partial def firstDiff (a b : Expr) : Expr × Expr :=
  match a, b with
  | .app f x, .app g y =>
    if !f.eqv g then firstDiff f g else if !x.eqv y then firstDiff x y else (a, b)
  | .forallE _ t c _, .forallE _ u d _ =>
    if !t.eqv u then firstDiff t u else if !c.eqv d then firstDiff c d else (a, b)
  | .lam _ t c _, .lam _ u d _ =>
    if !t.eqv u then firstDiff t u else if !c.eqv d then firstDiff c d else (a, b)
  | .mdata d x, y => if (stripMData x).eqv (stripMData y) then (.mdata d (mkConst `MDATA_ONLY_IN_ORIGINAL), y) else firstDiff x y
  | x, .mdata d y => if (stripMData x).eqv (stripMData y) then (x, .mdata d (mkConst `MDATA_ONLY_IN_REELAB)) else firstDiff x y
  | _, _ => (a, b)

def trunc (s : String) (n : Nat := 160) : String :=
  if s.length > n then (s.take n).toString ++ "…" else s

def oneLine (s : String) : String := " ".intercalate (s.splitOn "\n")

def containsOmission (s : String) : Bool := (s.splitOn "⋯").length > 1

/-- Run `x`, converting every exception (including heartbeat / recursion
runtime exceptions) into `Except.error msg`. -/
def guarded {α} (x : TermElabM α) : TermElabM (Except String α) := do
  tryCatchRuntimeEx (.ok <$> withCurrHeartbeats x)
    (fun ex => do return .error (oneLine (← ex.toMessageData.toString)))

def roundTrip (ci : ConstantInfo) : TermElabM (Outcome × String × String) := do
  let e := ci.type
  -- 1. print
  let s ← match ← guarded (do let fmt ← PrettyPrinter.ppExpr e; pure (fmt.pretty 1000000)) with
    | .ok s => pure s
    | .error m => return (.delabErr, "", m)
  if containsOmission s then return (.omission, s, "")
  -- 2. parse
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term s "<roundtrip>" with
    | .ok stx => pure stx
    | .error m => return (.parseErr, s, oneLine m)
  -- 3. elaborate (errors may be thrown or merely logged; check both)
  let msgsBefore := (← Core.getMessageLog)
  Core.resetMessageLog
  let r ← guarded (Term.withoutErrToSorry <| Term.withLevelNames ci.levelParams do
      let e' ← Term.elabType stx
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e')
  let log := (← Core.getMessageLog)
  let loggedMsg ← match log.toList.find? (·.severity == .error) with
    | some m => pure (some (oneLine (← m.data.toString)))
    | none => pure none
  Core.setMessageLog msgsBefore
  let e' ← match r with
    | .ok e' => pure e'
    | .error m => return (.elabErr, s, m)
  if let some m := loggedMsg then return (.elabErr, s, m)
  if e'.hasMVar || e'.hasLevelMVar then return (.elabErr, s, "residual metavariables")
  if e'.hasSorry then return (.elabErr, s, "residual sorry")
  -- 4. compare
  if e'.eqv e then
    if (eraseBinderNames e').equal (eraseBinderNames e) then return (.exact, s, "")
    else return (.eqvOnly, s, "binder annotations differ")
  let (d1, d2) := firstDiff e e'
  let diff := s!"orig: {trunc d1.dbgToString} | reelab: {trunc d2.dbgToString}"
  if (stripMData e').eqv (stripMData e) then return (.mdataOnly, s, diff)
  match ← guarded (withTransparency .default <| isDefEq e e') with
  | .ok true => return (.defEqOnly, s, diff)
  | _ => return (.notDefEq, s, diff)

/-- Name components that mark compiler- or command-generated theorems. -/
def generatedSuffix (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s ∈ ["induct", "mutual_induct", "induct_unfolding", "fun_cases", "eq_def", "congr_simp",
         "injEq", "inj", "sizeOf_spec", "eq_unfold", "below", "brecOn"] ||
    s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_"
  | _ => false

/-- Theorems defined in modules whose name starts with one of `prefixes`,
excluding private, internal-detail, and macro-scoped names; optionally
excluding generated theorems (see `generatedSuffix`). -/
def selectTheorems (prefixes : List Name) (excludeGenerated : Bool) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    let .thmInfo _ := ci | continue
    if isPrivateName n || n.isInternalDetail || n.hasMacroScopes then continue
    if excludeGenerated && generatedSuffix n then continue
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    if prefixes.any (fun p => p.isPrefixOf modName) then
      out := out.push ci
  return out.qsort (fun a b => a.name.toString < b.name.toString)

def headKey (m : String) : String :=
  -- normalize a message to a coarse category key: first 48 chars, digits elided
  let m := String.ofList (m.toList.map fun c => if c.isDigit then '9' else c)
  (m.take 48).toString

def run (variant : String) (opts : List (Name × DataValue)) (prefixes : List Name)
    (stride : Nat := 1) (excludeGenerated : Bool := false) (examples : Nat := 4) : CommandElabM Unit := do
  let base : Options :=
    ({} : Options)
      |>.setBool `autoImplicit false
      |>.setBool `relaxedAutoImplicit false
      |>.insert `maxHeartbeats (.ofNat 200000)
  let o := opts.foldl (fun o (k, v) => o.insert k v) base
  withScope (fun sc => { sc with opts := o, currNamespace := .anonymous, openDecls := [] }) do
  liftTermElabM do
    let thms ← selectTheorems prefixes excludeGenerated
    let thms := (List.range ((thms.size + stride - 1) / stride)).toArray.map (fun i => thms[i * stride]!)
    let mut counts : Array Nat := .replicate 9 0
    let mut samples : Array (Array (Name × String × String)) := .replicate 9 #[]
    let mut keys : Std.HashMap String Nat := {}
    let mut printedChars := 0
    let t0 ← IO.monoNanosNow
    for ci in thms do
      -- isolate every theorem: restore the full elaborator state (metavariable
      -- context, postponed universe constraints, auxiliary declarations such as
      -- generated `match_` definitions) after each round trip
      let saved ← saveState
      let (oc, s, d) ← roundTrip ci
      saved.restore
      printedChars := printedChars + s.length
      counts := counts.modify oc.idx (· + 1)
      if oc == .elabErr || oc == .parseErr || oc == .delabErr then
        let k := oc.name ++ " :: " ++ headKey d
        keys := keys.insert k (keys.getD k 0 + 1)
      if samples[oc.idx]!.size < examples then
        samples := samples.modify oc.idx (·.push (ci.name, s, d))
    let t1 ← IO.monoNanosNow
    let n := thms.size
    IO.println s!"VARIANT {variant} prefixes={prefixes} stride={stride} excludeGenerated={excludeGenerated} theorems={n} wall_ms={(t1 - t0) / 1000000} us_per_thm={if n == 0 then 0 else (t1 - t0) / 1000 / n} printed_chars={printedChars}"
    for oc in allOutcomes do
      IO.println s!"  {oc.name}: {counts[oc.idx]!}"
    let top := keys.toArray.qsort (fun a b => a.2 > b.2)
    for (k, c) in top.toList.take 15 do
      IO.println s!"  category {c} {k}"
    for oc in allOutcomes do
      for (nm, s, d) in samples[oc.idx]! do
        IO.println s!"  example {oc.name} {nm}: {trunc s 240} {if d.isEmpty then "" else "## " ++ trunc d 300}"

end RTProbe

namespace RTProbe
def catalog (prefixes : List Name) : CommandElabM Unit := do
  let base : Options :=
    ({} : Options) |>.setBool `autoImplicit false |>.setBool `relaxedAutoImplicit false
      |>.insert `maxHeartbeats (.ofNat 200000)
  withScope (fun sc => { sc with opts := base, currNamespace := .anonymous, openDecls := [] }) do
  liftTermElabM do
    let thms ← selectTheorems prefixes false
    let mut firstOf : Std.HashMap String (Name × String × String) := {}
    let mut cnt : Std.HashMap String Nat := {}
    for ci in thms do
      let saved ← saveState
      let (oc, s, d) ← roundTrip ci
      saved.restore
      if oc == .parseErr || oc == .elabErr || oc == .notDefEq then
        let k := oc.name ++ " :: " ++ headKey d
        cnt := cnt.insert k (cnt.getD k 0 + 1)
        unless firstOf.contains k do firstOf := firstOf.insert k (ci.name, s, d)
    let top := cnt.toArray.qsort (fun a b => a.2 > b.2)
    for (k, c) in top.toList.take 40 do
      let (nm, s, d) := firstOf.get! k
      IO.println s!"CAT {c} [{k}] e.g. {nm}: {trunc (oneLine s) 260} ## {trunc d 220}"
end RTProbe

