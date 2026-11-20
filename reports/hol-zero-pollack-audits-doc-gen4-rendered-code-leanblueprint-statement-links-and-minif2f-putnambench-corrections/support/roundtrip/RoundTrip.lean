/-
Print / re-parse / re-elaborate / compare probe over the theorem statements of a
published Lean library (here: the `Init` and `Std` modules shipped with a Lean
toolchain).

For every selected theorem `n : T`:
  1. delaborate and format `T` with a chosen set of `pp.*` options (`ppExpr`);
  2. parse the printed string as a `term`;
  3. elaborate it as a type (`elabType`) with the theorem's universe names in
     scope, `errToSorry := false`, then synthesize pending mvars;
  4. compare the result `T'` with the kernel type `T`:
       exact      : `T' == T` after stripping `mdata` (alpha-equivalence; binder
                    annotations ignored, as in `Expr.eqv`)
       defeq_red  : `isDefEq T' T` at reducible transparency
       defeq_def  : `isDefEq T' T` at default transparency
       MISMATCH   : elaborated, closed, but not defeq at default transparency
  Failure classes: parse_fail, elab_fail, elab_mvars (unassigned mvars remain),
  timeout (heartbeat limit), pp_fail.

Usage: RT_HEARTBEATS=<n> lean --run RoundTrip.lean <variant> <limit|0> <out.jsonl> [modulePrefix ...]
(RT_HEARTBEATS uses `set_option maxHeartbeats` units; default 200000 = Lean's default)
variant ∈ {default, explicit, all, numerals, coe, proofs, ppexplicit, coetypes, numcoetypes, docgenopts}
-/
import Lean
open Lean Meta Elab Term

def variantOptions (v : String) : Options :=
  let o : Options := {}
  match v with
  | "explicit" =>
    o |>.setBool `pp.proofs true
      |>.setBool `pp.numericTypes true
      |>.setBool `pp.coercions false
      |>.setBool `pp.funBinderTypes true
      |>.setBool `pp.letVarTypes true
  | "all" => o |>.setBool `pp.all true
  | "numerals" => o |>.setBool `pp.numericTypes true
  | "coe" => o |>.setBool `pp.coercions false
  | "proofs" => o |>.setBool `pp.proofs true
  | "ppexplicit" => o |>.setBool `pp.explicit true
  | "coetypes" => o |>.setBool `pp.coercions.types true
  | "docgenopts" => o |>.setBool `pp.tagAppFns true |>.setBool `pp.funBinderTypes true
  | "numcoetypes" => o |>.setBool `pp.numericTypes true |>.setBool `pp.coercions.types true
  | _ => o

partial def stripMData : Expr → Expr
  | .mdata _ b => stripMData b
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n t b bi => .lam n (stripMData t) (stripMData b) bi
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i e => .proj s i (stripMData e)
  | e => e

def isGenerated (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isPrivateName n || isAuxRecursor env n || isNoConfusion env n
  || (match n with
      | .str _ s => s == "eq_def" || s.startsWith "eq_" || s == "sizeOf_spec"
                     || s == "injEq" || s == "inj" || s.startsWith "_"
      | _ => false)

def nowNs : IO Nat := IO.monoNanosNow

def sanitize (s : String) : String :=
  let s := s.replace "\n" " "
  if s.length > 400 then (s.take 400).copy ++ "…" else s

structure Row where
  name : Name
  module : Name
  status : String
  ppNs : Nat := 0
  parseNs : Nat := 0
  elabNs : Nat := 0
  cmpNs : Nat := 0
  ppLen : Nat := 0
  printed : String := ""
  msg : String := ""

def Row.json (r : Row) : Json :=
  Json.mkObj [("name", toJson r.name.toString), ("module", toJson r.module.toString),
    ("status", toJson r.status), ("pp_ns", toJson r.ppNs), ("parse_ns", toJson r.parseNs),
    ("elab_ns", toJson r.elabNs), ("cmp_ns", toJson r.cmpNs), ("pp_len", toJson r.ppLen),
    ("printed", toJson r.printed), ("msg", toJson r.msg)]

def roundTrip (opts : Options) (n : Name) (modName : Name) (ci : ConstantInfo) : MetaM Row := do
  let T := ci.type
  let base : Row := { name := n, module := modName, status := "?" }
  let t0 ← nowNs
  let fmt? ← tryCatchRuntimeEx (some <$> withOptions (fun _ => opts) (ppExpr T))
      (fun _ => pure none)
  let t1 ← nowNs
  let some fmt := fmt? | return { base with status := "pp_fail", ppNs := t1 - t0 }
  let s := fmt.pretty 100
  let r := { base with ppNs := t1 - t0, ppLen := s.length, printed := sanitize s }
  match Parser.runParserCategory (← getEnv) `term s with
  | .error e =>
    let t2 ← nowNs
    return { r with status := "parse_fail", parseNs := t2 - t1, msg := sanitize e }
  | .ok stx =>
    let t2 ← nowNs
    let r := { r with parseNs := t2 - t1 }
    let elabRes ← tryCatchRuntimeEx
      (do
        let e ← (Term.withLevelNames ci.levelParams do
            let e ← Term.elabType stx
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e).run' (ctx := { errToSorry := false })
        pure (Except.ok e))
      (fun ex => do
        let m ← ex.toMessageData.toString
        let tag := if ex.isMaxHeartbeat then "timeout" else "elab_fail"
        pure (Except.error (tag, m)))
    let t3 ← nowNs
    match elabRes with
    | .error (tag, m) => return { r with status := tag, elabNs := t3 - t2, msg := sanitize m }
    | .ok e =>
      let r := { r with elabNs := t3 - t2 }
      if e.hasMVar then
        return { r with status := "elab_mvars", msg := sanitize (toString e) }
      if e.hasSyntheticSorry || e.hasSorry then
        return { r with status := "elab_fail", msg := "sorry in result" }
      let e' := stripMData e
      let T' := stripMData T
      if e' == T' then
        let t4 ← nowNs
        return { r with status := "exact", cmpNs := t4 - t3 }
      let cmp ← tryCatchRuntimeEx
        (do
          if (← withTransparency .reducible (isDefEq e' T')) then pure "defeq_red"
          else if (← withTransparency .default (isDefEq e' T')) then pure "defeq_def"
          else pure "MISMATCH")
        (fun ex => pure (if ex.isMaxHeartbeat then "cmp_timeout" else "cmp_fail"))
      let t4 ← nowNs
      let m ← if cmp == "MISMATCH" || cmp == "defeq_def" || cmp == "defeq_red" then
          (do let f ← ppExpr e; pure s!"reelab: {f.pretty 100}")
        else pure ""
      return { r with status := cmp, cmpNs := t4 - t3, msg := sanitize m }

unsafe def main (args : List String) : IO UInt32 := do
  let variant := args.getD 0 "default"
  let limit := (args.getD 1 "0").toNat!
  let out := args.getD 2 "/tmp/roundtrip.jsonl"
  let prefixes : List Name :=
    match args.drop 3 with
    | [] => [`Init, `Std]
    | ps => ps.map String.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let tImp0 ← nowNs
  let env ← importModules #[{ module := `Std }] {} (loadExts := true)
  let tImp1 ← nowNs
  IO.eprintln s!"imported Std in {(tImp1 - tImp0) / 1000000} ms"
  let opts := variantOptions variant
  -- heartbeat budget per declaration, in the same units as `set_option maxHeartbeats`
  let hb := ((← IO.getEnv "RT_HEARTBEATS").getD "200000").toNat!
  IO.eprintln s!"maxHeartbeats={hb}"
  -- collect candidate theorems
  let mut cands : Array (Name × Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if isGenerated env n then continue
      let some idx := env.getModuleIdxFor? n | continue
      let modName := env.header.moduleNames[idx.toNat]!
      if prefixes.any (fun p => p.isPrefixOf modName) then
        cands := cands.push (n, modName, ci)
  -- deterministic order
  cands := cands.qsort (fun a b => Name.lt a.1 b.1)
  if limit > 0 then cands := cands.extract 0 limit
  IO.eprintln s!"variant={variant} candidates={cands.size}"
  let h ← IO.FS.Handle.mk out .write
  let ctx : Core.Context := {
    fileName := "<roundtrip>", fileMap := default, options := opts,
    maxHeartbeats := hb * 1000 }
  let mut st : Core.State := { env }
  let mut i := 0
  let tAll0 ← nowNs
  for (n, modName, ci) in cands do
    let act : CoreM Row := withCurrHeartbeats do
      (roundTrip opts n modName ci).run' {} {}
    let res ← (act.toIO ctx st).toBaseIO
    match res with
    | .ok (row, st') =>
      -- keep env unchanged; drop accumulated caches/messages to bound memory
      st := { st with env := st'.env.setMainModule env.mainModule, nextMacroScope := st'.nextMacroScope,
                      ngen := st'.ngen }
      st := { st with env := env }
      h.putStrLn (row.json.compress)
    | .error e =>
      h.putStrLn ((Row.json { name := n, module := modName, status := "core_error",
                                msg := sanitize (toString e) }).compress)
    i := i + 1
    if i % 2000 == 0 then IO.eprintln s!"{i}/{cands.size}"
  let tAll1 ← nowNs
  IO.eprintln s!"done {i} in {(tAll1 - tAll0) / 1000000} ms"
  h.flush
  let status ← IO.FS.readFile "/proc/self/status"
  for l in status.splitOn "\n" do
    if l.startsWith "VmHWM" || l.startsWith "VmRSS" then IO.eprintln l
  return 0
