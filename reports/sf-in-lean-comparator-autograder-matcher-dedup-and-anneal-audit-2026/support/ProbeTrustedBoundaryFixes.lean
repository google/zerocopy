-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Elab.Import
import Lean.Parser.Tactic
import Lean.Replay

/-!
# Probe: Anneal `TrustedBoundary.lean` (`f938c18db`) Defects and Verified Fixes

Self-contained Lean `v4.34.1` executable probe (`lean --run`) that reproduces
and verifies fixes for three boundary-auditing defects in Anneal's
`trusted/audit/TrustedBoundary.lean` (at commit
`f938c18db56c49e82dde95506894a9b58b76b227`) on Lean `v4.34.1`:

1. **Triple-compounding `.match_1` contamination across `@[candidate]` and
   `@[vetted]` / `@[candidate <feat2>]` declarations (`lines 658–1305`):**
   - `declarationEdges ci` (`line 919`) includes the self-edge `ci.all =
     [cName]`, causing `allVetted` and `onlyAllowedNonVetted` (`lines
     1137–1143`) to evaluate to `false` on `dep = cName` whenever `cName` is
     owned by a `@[candidate]` function, leaving `autoHelpers` empty even for
     extensible inductives (`candExtFn.match_1`).
   - Non-extensible `.match_1` splitters (`candFn.match_1`, `touchesExtInduct ==
     false`) are excluded from `autoHelpers`, and `statusMap` retains
     `"candidate:mir_semantics"`, causing `line 1191` to reject `vetFn`,
     `candFn2`, `vetExtFn`, and `candExtFn2`.
   - `collectActiveCandidateFeatures` (`line 1280`) checks
     `status.startsWith "candidate:"` before `else if autoHelpers.contains n`
     (`line 1289`), falsely activating `"mir_semantics"` on `vetExtFn` even if
     `candExtFn.match_1` is inserted into `autoHelpers`.
   - Verifies that `isPureVettedMatcher` (filtering out `dep != cName && dep !=
     parentName`, covering both extensible and non-extensible inductives, and
     overriding `statusMap` to `"vetted"`) eliminates all four false rejections
     and false feature activations while still rejecting genuinely contaminated
     `@[vetted]` declarations (`badVetFn`).
2. **Cross-boundary `Trusted.*` `realizeConst` rejection in
   `verifyAndCollectLocals` (`lines 1346–1356`) and Phase 1 `Trusted` namespace
   enforcement (`lines 422–528`):**
   - When untrusted modules (`TheoryA` and `TheoryB`) run `simp` and `fun_cases`
     on a `Trusted.*` function, Lean's on-demand `realizeConst` serializes 8
     constants under the `Trusted` user-name root into `TheoryA.olean` and
     `TheoryB.olean`.
   - Demonstrates that `_private.<Mod>.0.Trusted.<fn>.match_1.splitter` is a
     `.defnInfo` (`isTheorem == false`) and that `Lean.isReservedName` returns
     `false` on all 5 matcher-attached realized constants when `loadExts :=
     false`.
   - Verifies that Phase 1 `inspectCommand` blocks untrusted `Trusted`
     declarations and Phase 2 `isRealizedCompilerConstant` +
     `sameRealizedThmHeader` admits and kernel-replays all 19 unique constants.
3. **Phase 1 `decide` `optConfig` rejection (`line 366`):**
   - In Lean `v4.34.1`, `s[1]` of `Lean.Parser.Tactic.decide` is an `optConfig`
     node with one `null` child `s[1][0]`. Verifies that `s[1].getArgs.isEmpty`
     falsely rejects bare `by decide`, whereas `s[1][0].getArgs.isEmpty` admits
     bare `by decide` and rejects `by decide +native` and `by decide +kernel`.
-/

open Lean

namespace ProbeTrustedBoundaryFixes

/-- Fails the probe immediately if `cond` is false. -/
def assertTrue (label : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"assertion failed: {label}"

-- ============================================================================
-- Exact definitions from `trusted/audit/TrustedBoundary.lean` (`f938c18db`)
-- ============================================================================

def fail (message : String) : IO α := throw <| IO.userError s!"policy:{message}"

def commandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

def atomWithin (s : Syntax) (value : String) : Bool :=
  (s.find? fun x => x.isAtom && x.getAtomVal == value).isSome

def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

def validCandidateFeatures : List Name := [
  `refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

structure ParseTrustState where
  scopes : List (Bool × Name) := []
  trustDeclarations : Array (String × String) := #[]

def currentNamespace (st : ParseTrustState) : Name :=
  st.scopes.foldl (init := .anonymous) fun acc (isNs, n) =>
    if isNs then acc ++ n else acc

def inspectAttrInstance (allowTrustAttrs : Bool) (allowMacroAttr : Bool)
    (elem : Syntax) : IO (Option String) := do
  unless elem.getArgs.size == 2 do fail "unsupported attribute-operation shape"
  if atomWithin elem[0] "scoped" || atomWithin elem[0] "local" then
    fail "scoped/local attribute modifiers are unsupported"
  let attr := elem[1]
  let k := attr.getKind
  if k == ``Parser.Attr.simple then
    let attrName := attr[0].getId
    let extraArgs := attr[1].getArgs
    if attrName == `vetted then
      unless allowTrustAttrs do
        fail "trust attribute @[vetted] is only allowed in Trusted modules"
      unless extraArgs.isEmpty do fail "@[vetted] does not accept arguments"
      return some "vetted"
    else if attrName == `candidate then
      unless allowTrustAttrs do
        fail "trust attribute @[candidate] is only allowed in Trusted modules"
      unless extraArgs.size == 1 && extraArgs[0]!.isIdent do
        fail "@[candidate] requires a single feature identifier"
      let feat := extraArgs[0]!.getId
      unless validCandidateFeatures.contains feat do
        fail s!"unknown candidate feature {feat}"
      return some s!"candidate:{feat}"
    else
      unless allowedAttributeNames.contains attrName do
        fail s!"unsupported attribute {attrName}"
      unless extraArgs.isEmpty do
        fail s!"unsupported arguments on attribute {attrName}"
      return none
  else if k == `Lean.Parser.Attr.macro then
    unless allowTrustAttrs && allowMacroAttr &&
        (attr[1].getId == ``Parser.Command.declaration ||
         attr[1].getId == ``Parser.Command.mutual) do
      fail "unsupported macro attribute"
    return some "vetted"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    return none
  else
    fail s!"unsupported attribute form {k}"

def extractTrustModifier (isTrustedModule : Bool) (allowMacroAttr : Bool)
    (mods : Syntax) : IO (Option String) := do
  let attrsOpt := mods[1]
  if attrsOpt.getArgs.isEmpty then return none
  let attrs := attrsOpt[0]
  let mut trustStatus? : Option String := none
  let mut sawMacroAttr := false
  for elem in attrs[1].getArgs do
    if elem.getKind == ``Parser.Term.attrInstance then
      let isMacro :=
        elem.getArgs.size == 2 && elem[1].getKind == `Lean.Parser.Attr.macro
      if let some st ← inspectAttrInstance isTrustedModule allowMacroAttr elem then
        if trustStatus?.isSome &&
            !(isMacro && sawMacroAttr && trustStatus? == some "vetted") then
          fail "multiple trust attributes on a single declaration"
        if isMacro then sawMacroAttr := true
        trustStatus? := some st
  return trustStatus?

def isReservedHelperComponent (s : String) : Bool :=
  s.isEmpty || s.startsWith "_" || s.startsWith "match_" ||
    s.startsWith "eq_" ||
    ["rec", "recOn", "casesOn", "ctorIdx", "ctorElim", "ctorElimType",
     "noConfusion", "noConfusionType"].contains s

def validateUserDeclIdent (context : String) (id : Name) : IO Unit := do
  if id.isAnonymous || id.components.any (fun c =>
      match c with
      | .str .anonymous s => c == `_root_ || isReservedHelperComponent s
      | _ => true) then
    fail s!"invalid or reserved {context} name {id}"

/-- Parameterized `inspectSyntax`: `fixDecideOptConfig == false` matches stock
    `TrustedBoundary.lean` line 366 (`s[1].getArgs.isEmpty`);
    `fixDecideOptConfig == true` checks `s[1][0].getArgs.isEmpty`. -/
partial def inspectSyntaxParam (fixDecideOptConfig : Bool)
    (allowTrustAttrs : Bool) (s : Syntax) : IO Unit := do
  if s.isAtom &&
      ["set_option", "rfl'", "unhygienic", "decide!", "bv_decide",
       "native_decide", "include_str", "by_elab", "run_tac",
       "with_decl_name%", "private_decl%", "decl_name%",
       "partial_fixpoint", "coinductive_fixpoint",
       "inductive_fixpoint"].contains s.getAtomVal then
    fail s!"unsupported syntax keyword {s.getAtomVal}"
  let k := s.getKind
  if [``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
      ``Parser.Command.axiom, ``Parser.Command.example,
      ``Parser.Command.coinductive, ``Parser.Command.computedFields,
      ``Parser.Command.computedField, ``Parser.Command.openScoped,
      ``Parser.Command.set_option, ``Parser.Term.set_option,
      ``Parser.Term.unsafe, ``Parser.Tactic.set_option,
      `Lean.Parser.Tactic.Grind.setOption, `Lean.byElab, `Lean.includeStr,
      `Lean.Parser.Tactic.runTac, `Lean.Parser.Tactic.nativeDecide,
      `Lean.Parser.Tactic.decideBang, `Lean.Parser.Tactic.bvDecide,
      `Lean.Parser.Tactic.rfl', `Lean.Parser.Tactic.unhygienic,
      `Lean.Parser.Tactic.sleep, `Lean.Parser.Tactic.dbgTrace,
      `Lean.Parser.Term.idbg, `Lean.Parser.Term.doIdbg,
      `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.doDbgTrace,
      `Lean.Parser.Term.withDeclName, `Lean.Parser.Term.privateDecl,
      `Lean.Parser.Term.declName, `Lean.Parser.Termination.partialFixpoint,
      `Lean.Parser.Termination.coinductiveFixpoint,
      `Lean.Parser.Termination.inductiveFixpoint].contains k then
    fail s!"unsupported source form {k}"
  if k == ``Parser.Term.attrKind then
    if atomWithin s "scoped" || atomWithin s "local" then
      fail "scoped/local attribute modifiers are unsupported"
  if k == ``Parser.Command.optDeriving ||
      k == ``Parser.Command.optDefDeriving then
    if atomWithin s "deriving" then fail "deriving clauses are unsupported"
  if k == ``Parser.Term.attrInstance then
    let _ ← inspectAttrInstance allowTrustAttrs allowTrustAttrs s
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do
      fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    if fixDecideOptConfig then
      unless s[1][0].getArgs.isEmpty do
        fail "decide configuration is unsupported"
    else
      unless s[1].getArgs.isEmpty do
        fail "decide configuration is unsupported"
  if k == `Lean.Parser.Term.letRecDecl then
    let inner := s[2][0]
    if inner.isOfKind `Lean.Parser.Term.letIdDecl ||
        inner.isOfKind `Lean.Parser.Term.letEqnsDecl then
      let idNode :=
        if inner[0].isOfKind `Lean.Parser.Term.letId then inner[0][0]
        else inner[0]
      validateUserDeclIdent "local recursive/where" idNode.getId
    else
      fail "pattern bindings in local recursive/where declarations are unsupported"
  if k == ``Parser.Command.structCtor then
    validateUserDeclIdent "structure constructor" s[1].getId
  if k == ``Parser.Command.structSimpleBinder then
    validateUserDeclIdent "structure field" s[1].getId
  if k == ``Parser.Command.structExplicitBinder ||
      k == ``Parser.Command.structImplicitBinder ||
      k == ``Parser.Command.structInstBinder then
    for idStx in s[2].getArgs do
      validateUserDeclIdent "structure field" idStx.getId
  if k == ``Parser.Command.structParent && !s[0].getArgs.isEmpty then
    validateUserDeclIdent "structure parent projection" s[0][0].getId
  if k == ``Parser.Command.declaration then
    inspectSyntaxParam fixDecideOptConfig allowTrustAttrs s[0]
    let decl := s[1]
    if decl.getKind == ``Parser.Command.inductive ||
        decl.getKind == ``Parser.Command.classInductive then
      for i in [:decl.getArgs.size] do
        if i == 4 then
          for ctor in decl[4].getArgs do
            for j in [:ctor.getArgs.size] do
              let allow := if j == 2 then allowTrustAttrs else false
              inspectSyntaxParam fixDecideOptConfig allow ctor[j]!
        else
          inspectSyntaxParam fixDecideOptConfig false decl[i]!
    else
      inspectSyntaxParam fixDecideOptConfig false decl
  else if k == ``Parser.Command.declModifiers ||
      k == ``Parser.Term.attributes || k == `null ||
      k == ``Parser.Command.mutual || k == ``Parser.Command.in then
    for child in s.getArgs do
      inspectSyntaxParam fixDecideOptConfig allowTrustAttrs child
  else
    for child in s.getArgs do
      inspectSyntaxParam fixDecideOptConfig false child

/-- Parameterized `inspectCommand`: `checkUntrustedTrustedNs == true` adds the
    Phase 1 check rejecting `Trusted` / `Trusted.*` declarations in
    non-`Trusted` modules. -/
partial def inspectCommandParam (fixDecideOptConfig : Bool)
    (checkUntrustedTrustedNs : Bool) (isTrustedModule : Bool) (s : Syntax)
    (st : ParseTrustState) : IO ParseTrustState := do
  unless commandKinds.contains s.getKind do
    fail s!"unsupported command {s.getKind}"
  inspectSyntaxParam fixDecideOptConfig isTrustedModule s
  if s.isOfKind ``Parser.Command.namespace then
    if !s[0].getArgs.all (·.getArgs.isEmpty) ||
        atomWithin s "noncomputable" || atomWithin s "meta" ||
        atomWithin s "public" || atomWithin s "expose" then
      fail "section/namespace modifiers are unsupported"
    let nsId := s[1].getId
    validateUserDeclIdent "namespace" nsId
    let pushed := nsId.components.map (true, ·)
    let nextSt := { st with scopes := st.scopes ++ pushed }
    if checkUntrustedTrustedNs then
      let fullNs := currentNamespace nextSt
      if !isTrustedModule && (fullNs == `Trusted || fullNs.getRoot == `Trusted) then
        fail s!"non-Trusted module cannot open Trusted namespace {fullNs}"
    return nextSt
  if s.isOfKind ``Parser.Command.section then
    if !s[0].getArgs.all (·.getArgs.isEmpty) ||
        atomWithin s "noncomputable" || atomWithin s "meta" ||
        atomWithin s "public" || atomWithin s "expose" then
      fail "section/namespace modifiers are unsupported"
    let secArgs := s[2].getArgs
    let pushed ←
      if secArgs.isEmpty then
        pure [(false, .anonymous)]
      else
        let secId := secArgs[0]!.getId
        validateUserDeclIdent "section" secId
        pure (secId.components.map (false, ·))
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.end then
    let endArgs := s[1].getArgs
    let count :=
      if endArgs.isEmpty then 1 else endArgs[0]!.getId.components.length
    if st.scopes.length < count then fail "unmatched `end` command"
    if endArgs.isEmpty then
      unless st.scopes.getLast? == some (false, .anonymous) do
        fail "unnamed `end` cannot close a named namespace or section"
    else
      let endComps := endArgs[0]!.getId.components
      let popped := (st.scopes.drop (st.scopes.length - count)).map (·.2)
      unless popped == endComps do fail "mismatched `end` command"
    return { st with scopes := st.scopes.take (st.scopes.length - count) }
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    if (s.find? fun x =>
        [``Parser.Command.namespace, ``Parser.Command.section,
         ``Parser.Command.end, ``Parser.Command.mutual].contains x.getKind).isSome then
      fail "scope or mutual commands are unsupported inside `in`"
    let st1 ← inspectCommandParam fixDecideOptConfig checkUntrustedTrustedNs
      isTrustedModule s[0] st
    let st2 ← inspectCommandParam fixDecideOptConfig checkUntrustedTrustedNs
      isTrustedModule s[2] st1
    return { st2 with scopes := st.scopes }
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    let mut cur := st
    for child in s[1].getArgs do
      cur ← inspectCommandParam fixDecideOptConfig checkUntrustedTrustedNs
        isTrustedModule child cur
    return cur
  if s.isOfKind ``Parser.Command.declaration then
    let mods := s[0]
    let decl := s[1]
    unless [``Parser.Command.abbrev, ``Parser.Command.definition,
            ``Parser.Command.theorem, ``Parser.Command.opaque,
            ``Parser.Command.instance, ``Parser.Command.inductive,
            ``Parser.Command.classInductive,
            ``Parser.Command.structure].contains decl.getKind do
      fail s!"unsupported declaration kind {decl.getKind}"
    let curNs := currentNamespace st
    let relName ←
      if decl.getKind == ``Parser.Command.instance then
        if decl[3].getArgs.isEmpty then
          if isTrustedModule then
            fail s!"unnamed instance in {curNs}; Trusted instances must be named"
          else
            pure .anonymous
        else
          unless decl[3][0].isOfKind ``Parser.Command.declId &&
              decl[3][0][0].isIdent do
            fail "invalid instance declaration identifier"
          let id := decl[3][0][0].getId
          validateUserDeclIdent "declaration" id
          pure id
      else
        unless decl[1].isOfKind ``Parser.Command.declId &&
            decl[1][0].isIdent do
          fail "invalid declaration identifier"
        let id := decl[1][0].getId
        validateUserDeclIdent "declaration" id
        pure id
    let fullName := curNs ++ relName
    if checkUntrustedTrustedNs && !isTrustedModule &&
        (fullName == `Trusted || fullName.getRoot == `Trusted) then
      fail s!"non-Trusted module cannot declare {fullName} in Trusted namespace"
    let isInd :=
      decl.getKind == ``Parser.Command.inductive ||
        decl.getKind == ``Parser.Command.classInductive
    if isInd then
      for ctor in decl[4].getArgs do
        validateUserDeclIdent "constructor" ctor[3].getId
    if isTrustedModule then
      let allowMacroAttr := fullName == `Trusted.expandTrustDeclaration
      let some status ← extractTrustModifier true allowMacroAttr mods
        | fail s!"missing @[vetted] or @[candidate <feature>] attribute on Trusted declaration {fullName}"
      let mut nextSt := {
        st with
        trustDeclarations := st.trustDeclarations.push (fullName.toString, status)
      }
      if isInd then
        for ctor in decl[4].getArgs do
          let ctorFullName := fullName ++ ctor[3].getId
          let ctorStatusOpt ← extractTrustModifier true false ctor[2]
          let ctorStatus := ctorStatusOpt.getD status
          if status.startsWith "candidate:" && ctorStatus == "vetted" then
            fail s!"constructor {ctorFullName} of candidate inductive {fullName} cannot be marked @[vetted]"
          nextSt := {
            nextSt with
            trustDeclarations :=
              nextSt.trustDeclarations.push (ctorFullName.toString, ctorStatus)
          }
      return nextSt
  return st

def inspectSourceTextParam (fixDecideOptConfig : Bool)
    (checkUntrustedTrustedNs : Bool) (parserEnv : Environment)
    (moduleName : Name) (text : String) : IO ParseTrustState := do
  let ctx := Parser.mkInputContext text moduleName.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then
    fail s!"header parser error in {moduleName}"
  if Elab.HeaderSyntax.isModule header then
    fail "module headers are unsupported"
  unless atomWithin header.raw "prelude" do
    fail "explicit prelude is required"
  let isTrustedModule :=
    moduleName == `Trusted || moduleName.getRoot == `Trusted
  let mut state := initial
  let mut messages := log
  let mut trustState : ParseTrustState := {}
  repeat
    let previous := state.pos
    let (stx, next, nextMessages) :=
      Parser.parseCommand ctx {env := parserEnv, options := {}} state messages
    state := next
    messages := nextMessages
    if messages.hasErrors || state.recovering then
      fail s!"command parser error in {moduleName}"
    if stx.isOfKind ``Parser.Command.eoi then break
    if state.pos <= previous then
      throw <| IO.userError "parser made no progress"
    trustState ← inspectCommandParam fixDecideOptConfig checkUntrustedTrustedNs
      isTrustedModule stx trustState
  unless trustState.scopes.isEmpty do
    fail s!"unclosed namespace or section in {moduleName}"
  return trustState

-- ============================================================================
-- Phase 2 functions from `TrustedBoundary.lean` (`f938c18db`)
-- ============================================================================

partial def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    fail "open expression in stored declaration"
  let mut result : NameSet := {}
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      match x with
      | .const n _ => result := result.insert n
      | .lit (.natVal _) => result := result.insert `Nat
      | .lit (.strVal _) => result := result.insert `String
      | .app a b => pending := a :: b :: pending
      | .forallE _ a b _ | .lam _ a b _ => pending := a :: b :: pending
      | .letE _ t v b _ => pending := t :: v :: b :: pending
      | .proj s _ b =>
        result := result.insert s
        pending := b :: pending
      | .mdata _ b => pending := b :: pending
      | _ => pure ()
  return result

def isMatcherSplitter (u : Name) : Bool :=
  match u with
  | .str _ s => s.startsWith "match_" || s.startsWith "_sparseCasesOn_"
  | _ => false

def isUnderMatcherSplitter (u : Name) (ci : ConstantInfo) : Bool :=
  match u with
  | .str p s => ci.isTheorem && isMatcherSplitter p && s.startsWith "_proof_"
  | _ => false

def isCompilerEqThm (locals : Std.HashMap Name ConstantInfo) (cName : Name)
    (ci : ConstantInfo) : Bool :=
  let u := (privateToUserName? cName).getD cName
  match u with
  | .str p s =>
    !p.isAnonymous && (locals.contains cName.getPrefix || locals.contains p) &&
      ci.isTheorem &&
      (s.startsWith "_eq_" || s.startsWith "eq_" ||
       s.startsWith "_congr_" || s.startsWith "_unfold")
  | _ => false

def isExtensibleInductHelper (extensibleInducts : NameSet) (u : Name) : Bool :=
  match u with
  | .str p s =>
    extensibleInducts.contains p &&
      ["rec", "recOn", "casesOn", "ctorIdx", "ctorElim", "ctorElimType",
       "noConfusion", "noConfusionType", "_sizeOf_1",
       "_sizeOf_inst"].contains s
  | _ => false

def composeParamCtx (outer inner : String) : String :=
  if outer == "vetted" then inner
  else if inner == "vetted" || inner == outer then outer
  else "conflict"

def deriveEliminatorParamStatuses (locals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String) (extensibleInducts : NameSet) :
    Std.HashMap Name (Array String) := Id.run do
  let mut result : Std.HashMap Name (Array String) := {}
  for (cName, ci) in locals do
    let u := (privateToUserName? cName).getD cName
    if let .str indName suffix := u then
      if extensibleInducts.contains indName &&
          ["rec", "recOn", "casesOn"].contains suffix then
        if let some (.inductInfo iv) := locals.get? indName then
          let ctorSet : NameSet := .ofList iv.ctors
          let mut cur := ci.type
          let mut statuses : Array String := #[]
          while cur.isForall do
            let .forallE _ dom body _ := cur | break
            let retDom := dom.getForallBody
            let mut st := "vetted"
            if let some lastArg := retDom.getAppArgs.back? then
              if let .const ctorName _ := lastArg.getAppFn then
                if ctorSet.contains ctorName then
                  st := statusMap.getD ctorName "vetted"
            statuses := statuses.push st
            cur := body
          result := result.insert cName statuses
  let mut changed := true
  while changed do
    changed := false
    for (cName, ci) in locals do
      let u := (privateToUserName? cName).getD cName
      if isMatcherSplitter u && !result.contains cName then
        if let some val := ci.value? (allowOpaque := true) then
          let numParams := val.getNumHeadLambdas
          let body := val.getLambdaBody
          let mut paramStates : Array (Option String) :=
            Array.replicate numParams none
          let mut conflict : Array Bool := Array.replicate numParams false
          let mut pending : List (Nat × String × Expr) :=
            [(0, "vetted", body)]
          let mut seen : Std.HashSet (Nat × String × Expr) := {}
          while !pending.isEmpty do
            let item := pending.head!
            pending := pending.tail!
            if !seen.contains item then
              seen := seen.insert item
              let (depth, ctx, x) := item
              if let .bvar idx := x then
                if idx >= depth && idx < depth + numParams then
                  let p := numParams - 1 - (idx - depth)
                  match paramStates[p]! with
                  | none => paramStates := paramStates.set! p (some ctx)
                  | some prev =>
                    if prev != ctx then conflict := conflict.set! p true
              else
                let fn := x.getAppFn
                let args := x.getAppArgs
                let mut handledApp := false
                if !args.isEmpty then
                  if let .const target _ := fn then
                    if let .str indName "ctorElim" :=
                        (privateToUserName? target).getD target then
                      if extensibleInducts.contains indName &&
                          args.size == 5 then
                        if let some (.inductInfo iv) := locals.get? indName then
                          let idxOpt :=
                            args[2]!.rawNatLit? <|>
                              (if args[2]! == mkConst ``Nat.zero then some 0
                               else none)
                          if let some idx := idxOpt then
                            if h : idx < iv.ctors.length then
                              let ctorName := iv.ctors[idx]
                              let ctorSt := statusMap.getD ctorName "vetted"
                              handledApp := true
                              for j in [:5] do
                                let argCtx :=
                                  if j == 4 then composeParamCtx ctx ctorSt
                                  else ctx
                                pending :=
                                  (depth, argCtx, args[j]!) :: pending
                    if !handledApp then
                      if let some tStatuses := result.get? target then
                        handledApp := true
                        for j in [:args.size] do
                          let tSt :=
                            if j < tStatuses.size then tStatuses[j]!
                            else "vetted"
                          let argCtx := composeParamCtx ctx tSt
                          pending := (depth, argCtx, args[j]!) :: pending
                if !handledApp then
                  match x with
                  | .app a b =>
                    pending := (depth, ctx, a) :: (depth, ctx, b) :: pending
                  | .lam _ d b _ | .forallE _ d b _ =>
                    pending :=
                      (depth, "vetted", d) :: (depth + 1, ctx, b) :: pending
                  | .letE _ t v b _ =>
                    pending :=
                      (depth, "vetted", t) :: (depth, "vetted", v) ::
                      (depth + 1, ctx, b) :: pending
                  | .proj _ _ b | .mdata _ b =>
                    pending := (depth, ctx, b) :: pending
                  | _ => pure ()
          let mut finalStatuses : Array String :=
            Array.replicate numParams "vetted"
          let mut hasCandidate := false
          for p in [:numParams] do
            if !conflict[p]! then
              if let some st := paramStates[p]! then
                if st.startsWith "candidate:" then
                  finalStatuses := finalStatuses.set! p st
                  hasCandidate := true
          if hasCandidate then
            result := result.insert cName finalStatuses
            changed := true
  return result

inductive Scope where
  | vetted
  | minorPremise (feat : String) (outerFeat? : Option String)
  | binderDom (feat : String)
  | guarded (feat : String)
  deriving BEq, Hashable, Inhabited

def Scope.nonPremise : Scope → Scope
  | .vetted | .minorPremise _ none => .vetted
  | .guarded outer | .minorPremise _ (some outer) => .guarded outer
  | .binderDom feat => .binderDom feat

structure ScopedEdges where
  unguarded : NameSet := {}
  binderDoms : Std.HashMap String NameSet := {}
  guarded : Std.HashMap String NameSet := {}
  deferred : Array (String × Expr) := #[]

partial def extractScopedEdges
    (elimStatuses : Std.HashMap Name (Array String))
    (activeFeats : Std.HashSet String := {}) (rootExpr : Expr)
    (checkClosed : Bool := true) : IO ScopedEdges := do
  if rootExpr.hasFVar || rootExpr.hasMVar ||
      (checkClosed && rootExpr.hasLooseBVars) then
    fail "open expression in stored declaration"
  let mut edges : ScopedEdges := {}
  let recordConst (e : ScopedEdges) (sc : Scope) (n : Name) : ScopedEdges :=
    match sc with
    | .vetted | .minorPremise _ none =>
      { e with unguarded := e.unguarded.insert n }
    | .guarded outer | .minorPremise _ (some outer) =>
      let prev := e.guarded.getD outer {}
      { e with guarded := e.guarded.insert outer (prev.insert n) }
    | .binderDom feat =>
      let prev := e.binderDoms.getD feat {}
      { e with binderDoms := e.binderDoms.insert feat (prev.insert n) }
  let mut pending : List (Scope × Expr) := [(.vetted, rootExpr)]
  let mut seen : Std.HashSet (Scope × Expr) := {}
  while !pending.isEmpty do
    let item := pending.head!
    pending := pending.tail!
    if !seen.contains item then
      seen := seen.insert item
      let (sc, x) := item
      let baseSc := sc.nonPremise
      let fn := x.getAppFn
      let args := x.getAppArgs
      if fn.isConstOf `Trusted.candidate then
        unless args.size == 3 do
          fail "partially or over-applied Trusted.candidate is unsupported"
        let .lit (.strVal feat) := args[0]!
          | fail "Trusted.candidate feature argument must be a string literal"
        unless validCandidateFeatures.contains feat.toName do
          fail s!"unknown candidate feature {feat} in Trusted.candidate"
        let outerFeat? ←
          match sc with
          | .minorPremise expectedFeat outer? =>
            unless expectedFeat == feat do
              fail s!"Trusted.candidate \"{feat}\" is only permitted inside a candidate:{feat} eliminator minor premise (found in candidate:{expectedFeat} scope)"
            pure outer?
          | _ =>
            fail s!"Trusted.candidate \"{feat}\" is only permitted inside a candidate:{feat} eliminator minor premise"
        edges :=
          recordConst (recordConst edges baseSc `Trusted.candidate)
            baseSc `String
        let prev := edges.guarded.getD feat {}
        edges := { edges with guarded := edges.guarded.insert feat prev }
        if outerFeat?.isNone && activeFeats.contains feat then
          pending := (.vetted, args[1]!) :: (.vetted, args[2]!) :: pending
        else
          if outerFeat?.isNone then
            edges := {
              edges with
              deferred :=
                (edges.deferred.push (feat, args[1]!)).push (feat, args[2]!)
            }
          pending :=
            (.guarded feat, args[1]!) :: (.guarded feat, args[2]!) :: pending
      else
        let mut handledElim := false
        if !args.isEmpty then
          if let .const cName _ := fn then
            if !(sc matches .binderDom _) then
              if let some paramStatuses := elimStatuses.get? cName then
                handledElim := true
                edges := recordConst edges baseSc cName
                let outerFeat? :=
                  match baseSc with
                  | .guarded outer => some outer
                  | _ => none
                for j in [:args.size] do
                  let pStatus :=
                    if j < paramStatuses.size then paramStatuses[j]!
                    else "vetted"
                  let childScope :=
                    if pStatus.startsWith "candidate:" then
                      .minorPremise (pStatus.drop 10).toString outerFeat?
                    else
                      baseSc
                  pending := (childScope, args[j]!) :: pending
        if !handledElim then
          match x with
          | .const n _ => edges := recordConst edges sc n
          | .lit (.natVal _) => edges := recordConst edges sc `Nat
          | .lit (.strVal _) => edges := recordConst edges sc `String
          | .app a b | .forallE _ a b _ =>
            pending := (baseSc, a) :: (baseSc, b) :: pending
          | .lam _ d b _ =>
            match sc with
            | .minorPremise feat outerFeat? =>
              if outerFeat?.isNone && activeFeats.contains feat then
                pending := (.vetted, d) :: (sc, b) :: pending
              else
                if outerFeat?.isNone then
                  edges := {
                    edges with deferred := edges.deferred.push (feat, d)
                  }
                pending := (.binderDom feat, d) :: (sc, b) :: pending
            | _ =>
              pending := (baseSc, d) :: (baseSc, b) :: pending
          | .letE _ t v b _ =>
            pending := (baseSc, t) :: (baseSc, v) :: (sc, b) :: pending
          | .proj s _ b =>
            edges := recordConst edges sc s
            pending := (baseSc, b) :: pending
          | .mdata _ b =>
            pending := (sc, b) :: pending
          | _ => pure ()
  return edges

def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let mut result ← expressionEdges ci.type
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ (← expressionEdges value)
  result := result ++ .ofList ci.all
  match ci with
  | .inductInfo v => result := result ++ .ofList v.ctors
  | .ctorInfo v => result := result.insert v.induct
  | .recInfo v =>
    result := result ++ .ofList v.all
    for rule in v.rules do
      result := (result.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | _ => pure ()
  return result

def hasNonVettedLetE (statusMap : Std.HashMap Name String) (rootExpr : Expr) :
    IO Bool := do
  let mut pending := [rootExpr]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      match x with
      | .app a b | .forallE _ a b _ | .lam _ a b _ =>
        pending := a :: b :: pending
      | .letE _ t v b _ =>
        for dep in (← expressionEdges t) ++ (← expressionEdges v) do
          if (statusMap.getD dep "vetted") != "vetted" then
            return true
        pending := t :: v :: b :: pending
      | .proj _ _ b | .mdata _ b => pending := b :: pending
      | _ => pure ()
  return false

def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n
    | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]?
    | fail s!"invalid module index: {n}"
  return mod.module

def classifyTrustedConstant (declMap : Std.HashMap Name String) (cName : Name) :
    IO (String × Name) := do
  let userName := (privateToUserName? cName).getD cName
  let mut cur := userName
  while !cur.isAnonymous do
    if let some status := declMap.get? cur then
      return (status, cur)
    cur := cur.getPrefix
  fail s!"unclassified Trusted constant {cName}"

/-- Stock `checkTrustedNonContamination` from `TrustedBoundary.lean`
    (`f938c18db`), collecting policy rejection messages for inspection. -/
def checkTrustedNonContaminationStock
    (locals : Std.HashMap Name ConstantInfo)
    (trustedLocals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name) :
    IO (Array String × NameSet × NameSet × Std.HashMap Name (Array String) ×
        Std.HashMap Name ScopedEdges) := do
  let mut errors : Array String := #[]
  let mut extensibleInducts : NameSet := {}
  let mut allowedInInductHelperOwners : NameSet := {}
  for (cName, ci) in trustedLocals do
    if let .ctorInfo v := ci then
      let _ ← extractScopedEdges {} {} ci.type
      if statusMap.get? v.induct == some "vetted" then
        let ctorStatus := statusMap.getD cName "vetted"
        if ctorStatus.startsWith "candidate:" then
          extensibleInducts := extensibleInducts.insert v.induct
          allowedInInductHelperOwners :=
            allowedInInductHelperOwners.insert cName
          for dep in (← expressionEdges ci.type) do
            if let some depStatus := statusMap.get? dep then
              if depStatus != "vetted" && depStatus != ctorStatus then
                errors := errors.push
                  s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references {dep} ({depStatus}) in its type"
              if depStatus == ctorStatus then
                let depOwner := ownerMap.getD dep dep
                match trustedLocals.get? depOwner with
                | some (.inductInfo iv) =>
                  allowedInInductHelperOwners :=
                    allowedInInductHelperOwners.insert depOwner
                  for ctor in iv.ctors do
                    allowedInInductHelperOwners :=
                      allowedInInductHelperOwners.insert ctor
                | some (.ctorInfo cv) =>
                  allowedInInductHelperOwners :=
                    (allowedInInductHelperOwners.insert depOwner).insert
                      cv.induct
                | _ =>
                  errors := errors.push
                    s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references non-inductive declaration {dep} in its type"
  let elimStatuses :=
    deriveEliminatorParamStatuses locals statusMap extensibleInducts
  let mut autoHelpers : NameSet := {}
  let mut scopedMap : Std.HashMap Name ScopedEdges := {}
  let mut ownerGuardedFeats : Std.HashMap Name (Std.HashSet String) := {}
  for (cName, ci) in locals do
    let userName := (privateToUserName? cName).getD cName
    let isInductOrRec :=
      (ci.isInductive && extensibleInducts.contains cName) ||
        isExtensibleInductHelper extensibleInducts userName
    let mut isExtSplitter := false
    if !isInductOrRec &&
        (isMatcherSplitter userName || isUnderMatcherSplitter userName ci) then
      let deps ← declarationEdges ci
      let parentName :=
        if isUnderMatcherSplitter userName ci then cName.getPrefix else cName
      let parentDeps ←
        if isUnderMatcherSplitter userName ci then
          if let some pCi := locals.get? parentName then
            declarationEdges pCi
          else
            pure {}
        else
          pure deps
      let touchesExtInduct :=
        (deps ++ parentDeps).toList.any (extensibleInducts.contains ·)
      let allVetted :=
        deps.toList.all fun dep => (statusMap.getD dep "vetted") == "vetted"
      let onlyAllowedNonVetted :=
        allVetted ||
          (elimStatuses.contains parentName &&
            deps.toList.all fun dep =>
              (statusMap.getD dep "vetted") == "vetted" ||
                allowedInInductHelperOwners.contains (ownerMap.getD dep dep))
      let badTypeLet ← hasNonVettedLetE statusMap ci.type
      let badValLet ←
        match ci.value? (allowOpaque := true) with
        | some val => hasNonVettedLetE statusMap val
        | none => pure false
      if touchesExtInduct && onlyAllowedNonVetted &&
          !badTypeLet && !badValLet then
        isExtSplitter := true
    if isInductOrRec || isExtSplitter then
      autoHelpers := autoHelpers.insert cName
      let _ ← extractScopedEdges {} {} ci.type
      if let some val := ci.value? (allowOpaque := true) then
        let _ ← extractScopedEdges {} {} val
      if let some selfStatus := statusMap.get? cName then
        for dep in (← declarationEdges ci) do
          if let some depStatus := statusMap.get? dep then
            let depOwner := ownerMap.getD dep dep
            if depStatus != "vetted" && depStatus != selfStatus &&
                !(selfStatus == "vetted" &&
                  allowedInInductHelperOwners.contains depOwner) then
              errors := errors.push
                s!"{selfStatus} helper {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
    else if !isCompilerEqThm locals cName ci then
      let typeEdges ← extractScopedEdges {} {} ci.type
      let valEdges ←
        match ci.value? (allowOpaque := true) with
        | some val => extractScopedEdges elimStatuses {} val
        | none => pure {}
      for (feat, domDeps) in valEdges.binderDoms do
        let expectedStatus := s!"candidate:{feat}"
        for dep in domDeps do
          if let some depStatus := statusMap.get? dep then
            let depOwner := ownerMap.getD dep dep
            if depStatus != "vetted" &&
                !(depStatus == expectedStatus &&
                  allowedInInductHelperOwners.contains depOwner) then
              errors := errors.push
                s!"declaration {cName} references {dep} ({depStatus}) in minor-premise binder domain"
      for (feat, bodyDeps) in valEdges.guarded do
        let expectedStatus := s!"candidate:{feat}"
        for dep in bodyDeps do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != expectedStatus then
              errors := errors.push
                s!"Trusted.candidate \"{feat}\" branch in {cName} references {dep} ({depStatus})"
      if let some selfStatus := statusMap.get? cName then
        for dep in typeEdges.unguarded do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != selfStatus then
              errors := errors.push
                s!"{selfStatus} declaration {cName} references {depStatus} declaration {dep} in its type"
        for dep in valEdges.unguarded ++ NameSet.ofList ci.all do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != selfStatus then
              errors := errors.push
                s!"{selfStatus} declaration {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
      let owner := ownerMap.getD cName userName
      let mut guardedFeats := ownerGuardedFeats.getD owner {}
      for (feat, _) in valEdges.guarded do
        guardedFeats := guardedFeats.insert feat
      ownerGuardedFeats := ownerGuardedFeats.insert owner guardedFeats
      let extraDeps ←
        if (ci.value? (allowOpaque := true)).isSome then
          pure (NameSet.ofList ci.all)
        else
          declarationEdges ci
      scopedMap := scopedMap.insert cName {
        valEdges with
        unguarded := typeEdges.unguarded ++ valEdges.unguarded ++ extraDeps
      }
  return (errors, autoHelpers, allowedInInductHelperOwners, elimStatuses,
    scopedMap)

/-- Fixed `isPureVettedMatcher`: returns `true` when `cName` is a
    compiler-generated `.match_N` / `._sparseCasesOn_N` splitter (or `_proof_N`
    theorem underneath it) whose non-self dependencies are all `"vetted"` (or,
    for an extensible-inductive splitter in `elimStatuses`, in
    `allowedInInductHelperOwners`) and whose type and body contain no
    non-`"vetted"` `.letE` bindings. -/
def isPureVettedMatcher (locals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name)
    (extensibleInducts : NameSet)
    (allowedInInductHelperOwners : NameSet)
    (elimStatuses : Std.HashMap Name (Array String))
    (cName : Name) (ci : ConstantInfo) : IO Bool := do
  let userName := (privateToUserName? cName).getD cName
  unless isMatcherSplitter userName || isUnderMatcherSplitter userName ci do
    return false
  let deps ← declarationEdges ci
  let parentName :=
    if isUnderMatcherSplitter userName ci then cName.getPrefix else cName
  let parentDeps ←
    if isUnderMatcherSplitter userName ci then
      if let some pCi := locals.get? parentName then
        declarationEdges pCi
      else
        pure {}
    else
      pure deps
  let touchesExtInduct :=
    (deps ++ parentDeps).toList.any (extensibleInducts.contains ·)
  let nonSelfDeps :=
    deps.toList.filter fun dep => dep != cName && dep != parentName
  let allVetted :=
    nonSelfDeps.all fun dep => (statusMap.getD dep "vetted") == "vetted"
  let onlyAllowedNonVetted :=
    allVetted ||
      (touchesExtInduct && elimStatuses.contains parentName &&
        nonSelfDeps.all fun dep =>
          (statusMap.getD dep "vetted") == "vetted" ||
            allowedInInductHelperOwners.contains (ownerMap.getD dep dep))
  let badTypeLet ← hasNonVettedLetE statusMap ci.type
  let badValLet ←
    match ci.value? (allowOpaque := true) with
    | some val => hasNonVettedLetE statusMap val
    | none => pure false
  return onlyAllowedNonVetted && !badTypeLet && !badValLet

/-- Fixed `checkTrustedNonContaminationFixed`: classifies pure vetted matchers
    into `autoHelpers` and overrides their `statusMap` status to `"vetted"`. -/
def checkTrustedNonContaminationFixed
    (locals : Std.HashMap Name ConstantInfo)
    (trustedLocals : Std.HashMap Name ConstantInfo)
    (initialStatusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name) :
    IO (Std.HashMap Name String × NameSet × NameSet ×
        Std.HashMap Name (Array String) × Std.HashMap Name ScopedEdges) := do
  let mut statusMap := initialStatusMap
  let mut extensibleInducts : NameSet := {}
  let mut allowedInInductHelperOwners : NameSet := {}
  for (cName, ci) in trustedLocals do
    if let .ctorInfo v := ci then
      let _ ← extractScopedEdges {} {} ci.type
      if statusMap.get? v.induct == some "vetted" then
        let ctorStatus := statusMap.getD cName "vetted"
        if ctorStatus.startsWith "candidate:" then
          extensibleInducts := extensibleInducts.insert v.induct
          allowedInInductHelperOwners :=
            allowedInInductHelperOwners.insert cName
          for dep in (← expressionEdges ci.type) do
            if let some depStatus := statusMap.get? dep then
              if depStatus != "vetted" && depStatus != ctorStatus then
                fail s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references {dep} ({depStatus}) in its type"
              if depStatus == ctorStatus then
                let depOwner := ownerMap.getD dep dep
                match trustedLocals.get? depOwner with
                | some (.inductInfo iv) =>
                  allowedInInductHelperOwners :=
                    allowedInInductHelperOwners.insert depOwner
                  for ctor in iv.ctors do
                    allowedInInductHelperOwners :=
                      allowedInInductHelperOwners.insert ctor
                | some (.ctorInfo cv) =>
                  allowedInInductHelperOwners :=
                    (allowedInInductHelperOwners.insert depOwner).insert
                      cv.induct
                | _ =>
                  fail s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references non-inductive declaration {dep} in its type"
  let elimStatuses :=
    deriveEliminatorParamStatuses locals statusMap extensibleInducts
  let mut autoHelpers : NameSet := {}
  for (cName, ci) in locals do
    let userName := (privateToUserName? cName).getD cName
    if (ci.isInductive && extensibleInducts.contains cName) ||
        isExtensibleInductHelper extensibleInducts userName then
      autoHelpers := autoHelpers.insert cName
  let mut changed := true
  while changed do
    changed := false
    for (cName, ci) in locals do
      if !autoHelpers.contains cName then
        if ← isPureVettedMatcher locals statusMap ownerMap extensibleInducts
            allowedInInductHelperOwners elimStatuses cName ci then
          autoHelpers := autoHelpers.insert cName
          if statusMap.contains cName then
            statusMap := statusMap.insert cName "vetted"
          changed := true
  let mut scopedMap : Std.HashMap Name ScopedEdges := {}
  let mut ownerGuardedFeats : Std.HashMap Name (Std.HashSet String) := {}
  for (cName, ci) in locals do
    let userName := (privateToUserName? cName).getD cName
    if autoHelpers.contains cName then
      let _ ← extractScopedEdges {} {} ci.type
      if let some val := ci.value? (allowOpaque := true) then
        let _ ← extractScopedEdges {} {} val
      if let some selfStatus := statusMap.get? cName then
        for dep in (← declarationEdges ci) do
          if let some depStatus := statusMap.get? dep then
            let depOwner := ownerMap.getD dep dep
            if depStatus != "vetted" && depStatus != selfStatus &&
                !(selfStatus == "vetted" &&
                  allowedInInductHelperOwners.contains depOwner) then
              fail s!"{selfStatus} helper {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
    else if !isCompilerEqThm locals cName ci then
      let typeEdges ← extractScopedEdges {} {} ci.type
      let valEdges ←
        match ci.value? (allowOpaque := true) with
        | some val => extractScopedEdges elimStatuses {} val
        | none => pure {}
      for (feat, domDeps) in valEdges.binderDoms do
        let expectedStatus := s!"candidate:{feat}"
        for dep in domDeps do
          if let some depStatus := statusMap.get? dep then
            let depOwner := ownerMap.getD dep dep
            if depStatus != "vetted" &&
                !(depStatus == expectedStatus &&
                  allowedInInductHelperOwners.contains depOwner) then
              fail s!"declaration {cName} references {dep} ({depStatus}) in minor-premise binder domain"
      for (feat, bodyDeps) in valEdges.guarded do
        let expectedStatus := s!"candidate:{feat}"
        for dep in bodyDeps do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != expectedStatus then
              fail s!"Trusted.candidate \"{feat}\" branch in {cName} references {dep} ({depStatus})"
      if let some selfStatus := statusMap.get? cName then
        for dep in typeEdges.unguarded do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != selfStatus then
              fail s!"{selfStatus} declaration {cName} references {depStatus} declaration {dep} in its type"
        for dep in valEdges.unguarded ++ NameSet.ofList ci.all do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != selfStatus then
              fail s!"{selfStatus} declaration {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
      let owner := ownerMap.getD cName userName
      let mut guardedFeats := ownerGuardedFeats.getD owner {}
      for (feat, _) in valEdges.guarded do
        guardedFeats := guardedFeats.insert feat
      ownerGuardedFeats := ownerGuardedFeats.insert owner guardedFeats
      let extraDeps ←
        if (ci.value? (allowOpaque := true)).isSome then
          pure (NameSet.ofList ci.all)
        else
          declarationEdges ci
      scopedMap := scopedMap.insert cName {
        valEdges with
        unguarded := typeEdges.unguarded ++ valEdges.unguarded ++ extraDeps
      }
  for (cName, ci) in locals do
    if isCompilerEqThm locals cName ci then
      let parentUser := (privateToUserName? cName.getPrefix).getD cName.getPrefix
      let owner := ownerMap.getD cName parentUser
      let guardedFeats := ownerGuardedFeats.getD owner {}
      let selfStatus := statusMap.getD cName "vetted"
      for dep in (← declarationEdges ci) do
        if let some depStatus := statusMap.get? dep then
          let depOwner := ownerMap.getD dep dep
          if depStatus != "vetted" && depStatus != selfStatus &&
              !allowedInInductHelperOwners.contains depOwner then
            let feat := (depStatus.drop 10).toString
            unless depStatus.startsWith "candidate:" &&
                guardedFeats.contains feat do
              fail s!"{selfStatus} equational theorem {cName} references {dep} ({depStatus})"
  return (statusMap, autoHelpers, allowedInInductHelperOwners, elimStatuses,
    scopedMap)

def collectActiveCandidateFeatures (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (trusted : Array Name)
    (statusMap : Std.HashMap Name String) (ownerMap : Std.HashMap Name Name)
    (autoHelpers : NameSet) (allowedInInductHelperOwners : NameSet)
    (elimStatuses : Std.HashMap Name (Array String))
    (scopedMap : Std.HashMap Name ScopedEdges)
    (roots : Array Name) : IO (Array String) := do
  let mut pending := roots.toList
  let mut pendingExprs : List Expr := []
  let mut visited : NameSet := {}
  let mut activeFeats : Std.HashSet String := {}
  let mut deferred : Std.HashMap String (Array Expr) := {}
  while !pending.isEmpty || !pendingExprs.isEmpty do
    while !pendingExprs.isEmpty do
      let e := pendingExprs.head!
      pendingExprs := pendingExprs.tail!
      let edges ←
        extractScopedEdges elimStatuses activeFeats e (checkClosed := false)
      pending := edges.unguarded.toList ++ pending
      for (feat, subExpr) in edges.deferred do
        if activeFeats.contains feat then
          pendingExprs := subExpr :: pendingExprs
        else
          let prev := deferred.getD feat #[]
          deferred := deferred.insert feat (prev.push subExpr)
    if !pending.isEmpty then
      let n := pending.head!
      pending := pending.tail!
      if !visited.contains n then
        visited := visited.insert n
        let m ← provenance n
        let ci ← lookup n
        let status :=
          if trusted.contains m then statusMap.getD n "vetted" else "vetted"
        if status.startsWith "candidate:" then
          let feat := (status.drop 10).toString
          if !activeFeats.contains feat then
            activeFeats := activeFeats.insert feat
            if let some bodies := deferred.get? feat then
              deferred := deferred.erase feat
              for b in bodies do
                pendingExprs := b :: pendingExprs
          pending := (← declarationEdges ci).toList ++ pending
        else if autoHelpers.contains n then
          for dep in (← declarationEdges ci) do
            if !allowedInInductHelperOwners.contains (ownerMap.getD dep dep) then
              pending := dep :: pending
        else if let some edges := scopedMap.get? n then
          pending := edges.unguarded.toList ++ pending
          for (feat, subExpr) in edges.deferred do
            if activeFeats.contains feat then
              pendingExprs := subExpr :: pendingExprs
            else
              let prev := deferred.getD feat #[]
              deferred := deferred.insert feat (prev.push subExpr)
        else
          for dep in (← declarationEdges ci) do
            if !allowedInInductHelperOwners.contains (ownerMap.getD dep dep) then
              pending := dep :: pending
  return activeFeats.toArray.qsort (· < ·)

-- ============================================================================
-- Stock vs. Fixed `verifyAndCollectLocals` (`TrustedBoundary.lean:1341-1365`)
-- ============================================================================

def verifyAndCollectLocalsStock (env : Environment) (foundation : NameSet)
    (trusted : Array Name) (targetMods : Array Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  let mut locals : Std.HashMap Name ConstantInfo := {}
  for m in env.header.modules, data in env.header.moduleData do
    if targetMods.contains m.module then
      for ci in data.constants do
        let orig ← origin env ci.name
        if locals.contains ci.name then fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
        let some stored := env.checked.get.find? ci.name
          | fail s!"missing stored declaration {ci.name}"
        unless stored.type == ci.type &&
            stored.value? true == ci.value? true do
          fail s!"stored declaration differs from inventory {ci.name}"
        if !foundation.contains m.module then
          let isTrusted := trusted.contains m.module
          if !isTrusted then
            let userName := (privateToUserName? ci.name).getD ci.name
            if userName == `Trusted || userName.getRoot == `Trusted then
              fail s!"non-Trusted module {m.module} cannot declare constant {ci.name} in Trusted namespace"
          if ci.isUnsafe || ci.isPartial then
            fail s!"unsafe/partial declaration {ci.name} in {m.module}"
          if ci.isAxiom then
            fail s!"strict axiom declaration {ci.name} in {m.module}"
          locals := locals.insert ci.name ci
  return locals

/-- Structural predicate for constants generated on demand via `realizeConst`
    for an already-admitted declaration in `locals` (works under
    `loadExts := false` and handles both realized theorems and
    `_private.<Mod>.0.<matcher>.splitter` definitions). -/
def isRealizedCompilerConstant (env : Environment)
    (locals : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : Bool :=
  let u := (privateToUserName? ci.name).getD ci.name
  match u with
  | .str p s =>
    !p.isAnonymous && (locals.contains ci.name.getPrefix || locals.contains p) &&
      ((ci.isTheorem &&
        (Lean.isReservedName env ci.name ||
         s == "eq_def" || s == "eq_unfold" || s == "unfold" || s == "else_eq" ||
         s == "fun_cases" || s == "fun_cases_unfolding" ||
         s == "induct" || s == "induct_unfolding" ||
         s == "mutual_induct" || s == "mutual_induct_unfolding" ||
         s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
         s.startsWith "eq_" || s.startsWith "_eq_" ||
         s.startsWith "congr_" || s.startsWith "_congr_")) ||
       ((ci matches .defnInfo _) && s == "splitter" && isMatcherSplitter p &&
        (privateToUserName? ci.name).isSome))
  | _ => false

def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  a.isTheorem && b.isTheorem && a.name == b.name &&
    a.levelParams == b.levelParams && a.type == b.type

def verifyAndCollectLocalsFixed (env : Environment) (foundation : NameSet)
    (trusted : Array Name) (targetMods : Array Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  let mut locals : Std.HashMap Name ConstantInfo := {}
  for m in env.header.modules, data in env.header.moduleData do
    if targetMods.contains m.module then
      for ci in data.constants do
        let orig ← origin env ci.name
        let some stored := env.checked.get.find? ci.name
          | fail s!"missing stored declaration {ci.name}"
        let isRealized := isRealizedCompilerConstant env locals ci
        if let some prev := locals.get? ci.name then
          unless isRealized && sameRealizedThmHeader prev ci &&
              sameRealizedThmHeader stored ci do
            fail s!"duplicate declaration {ci.name}"
        else
          unless orig == m.module do
            fail s!"inventory origin mismatch {ci.name}"
        unless stored.type == ci.type &&
            (stored.value? true == ci.value? true ||
             (isRealized && sameRealizedThmHeader stored ci)) do
          fail s!"stored declaration differs from inventory {ci.name}"
        if !foundation.contains m.module then
          let isTrusted := trusted.contains m.module
          if !isTrusted then
            let userName := (privateToUserName? ci.name).getD ci.name
            if userName == `Trusted || userName.getRoot == `Trusted then
              unless isRealized do
                fail s!"non-Trusted module {m.module} cannot declare constant {ci.name} in Trusted namespace"
          if ci.isUnsafe || ci.isPartial then
            fail s!"unsafe/partial declaration {ci.name} in {m.module}"
          if ci.isAxiom then
            fail s!"strict axiom declaration {ci.name} in {m.module}"
          locals := locals.insert ci.name stored
  return locals

-- ============================================================================
-- Embedded Probe Module Sources
-- ============================================================================

def compileLeanModule (leanExe : System.FilePath) (tmpDir : System.FilePath)
    (relModPath : String) (src : String) : IO System.FilePath := do
  let leanFile := tmpDir / s!"{relModPath}.lean"
  let oleanFile := tmpDir / s!"{relModPath}.olean"
  if let some parent := leanFile.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile leanFile src
  let out ← IO.Process.output {
    cmd := leanExe.toString
    args := #["-DElab.async=false", "-o", oleanFile.toString, leanFile.toString]
    cwd := some tmpDir
    env := #[("LEAN_PATH", some tmpDir.toString)]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"failed to compile {relModPath}:\n{out.stdout}\n{out.stderr}"
  return oleanFile

def trustedMatchProbeSrc : String :=
  "prelude\n" ++
  "import Init\n" ++
  "namespace Trusted\n" ++
  "def candidate (_feat : String) {α : Sort u} (body : α) : α := body\n" ++
  "namespace MatchProbe\n" ++
  "inductive PureInd : Type where\n" ++
  "  | a : PureInd\n" ++
  "  | b (n : Nat) : PureInd\n" ++
  "def candFn (x : PureInd) : Bool :=\n" ++
  "  match x with\n" ++
  "  | .a => true\n" ++
  "  | .b _ => false\n" ++
  "def vetFn (x : PureInd) : Bool :=\n" ++
  "  match x with\n" ++
  "  | .a => false\n" ++
  "  | .b _ => true\n" ++
  "def candFn2 (x : PureInd) : Bool :=\n" ++
  "  match x with\n" ++
  "  | .a => true\n" ++
  "  | .b _ => true\n" ++
  "inductive ExtInd : Type where\n" ++
  "  | v1 : ExtInd\n" ++
  "  | v2 : ExtInd\n" ++
  "  | c1 (n : Nat) : ExtInd\n" ++
  "def candExtFn (x : ExtInd) : Bool :=\n" ++
  "  match x with\n" ++
  "  | .v1 => true\n" ++
  "  | .v2 => false\n" ++
  "  | .c1 _ => true\n" ++
  "def vetExtFn (x : ExtInd) : Bool :=\n" ++
  "  match x with\n" ++
  "  | .v1 => false\n" ++
  "  | .v2 => true\n" ++
  "  | .c1 _ => Trusted.candidate \"mir_semantics\" false\n" ++
  "def candExtFn2 (x : ExtInd) : Bool :=\n" ++
  "  match x with\n" ++
  "  | .v1 => true\n" ++
  "  | .v2 => true\n" ++
  "  | .c1 _ => Trusted.candidate \"mir_semantics\" false\n" ++
  "def badVetFn (x : PureInd) : Bool := candFn x\n" ++
  "end MatchProbe\n" ++
  "end Trusted\n"

def trustedRealizeProbeSrc : String :=
  "prelude\n" ++
  "import Init\n" ++
  "namespace Trusted.RealizeProbe\n" ++
  "def stepOpt (x : Option Nat) : Nat :=\n" ++
  "  match x with\n" ++
  "  | none => 0\n" ++
  "  | some n => n + 1\n" ++
  "end Trusted.RealizeProbe\n"

def theoryASrc : String :=
  "prelude\n" ++
  "import Init\n" ++
  "import Trusted.RealizeProbe\n" ++
  "namespace TheoryA\n" ++
  "theorem stepOpt_none_and_some (n : Nat) :\n" ++
  "    Trusted.RealizeProbe.stepOpt none = 0 ∧\n" ++
  "    Trusted.RealizeProbe.stepOpt (some n) = n + 1 := by\n" ++
  "  simp [Trusted.RealizeProbe.stepOpt]\n" ++
  "theorem stepOpt_cases (x : Option Nat) :\n" ++
  "    Trusted.RealizeProbe.stepOpt x = 0 ∨\n" ++
  "    ∃ n, Trusted.RealizeProbe.stepOpt x = n + 1 := by\n" ++
  "  fun_cases Trusted.RealizeProbe.stepOpt x\n" ++
  "  · exact Or.inl rfl\n" ++
  "  · rename_i n\n" ++
  "    exact Or.inr ⟨n, rfl⟩\n" ++
  "theorem decide_bare_example : (2 + 2 == 4) = true := by\n" ++
  "  decide\n" ++
  "end TheoryA\n"

def theoryBSrc : String :=
  "prelude\n" ++
  "import Init\n" ++
  "import Trusted.RealizeProbe\n" ++
  "namespace TheoryB\n" ++
  "theorem stepOpt_pos_of_some (n : Nat) :\n" ++
  "    0 < Trusted.RealizeProbe.stepOpt (some n) := by\n" ++
  "  simp [Trusted.RealizeProbe.stepOpt]\n" ++
  "theorem stepOpt_nonneg (x : Option Nat) :\n" ++
  "    0 ≤ Trusted.RealizeProbe.stepOpt x := by\n" ++
  "  fun_cases Trusted.RealizeProbe.stepOpt x <;> simp\n" ++
  "end TheoryB\n"

def main : IO UInt32 := do
  let leanExe ← IO.appPath
  let sysroot ← Lean.findSysroot leanExe.toString
  IO.FS.withTempDir fun tmpDir => do
    let _ ← compileLeanModule leanExe tmpDir "Trusted/MatchProbe"
      trustedMatchProbeSrc
    let _ ← compileLeanModule leanExe tmpDir "Trusted/RealizeProbe"
      trustedRealizeProbeSrc
    let _ ← compileLeanModule leanExe tmpDir "TheoryA" theoryASrc
    let _ ← compileLeanModule leanExe tmpDir "TheoryB" theoryBSrc

    initSearchPath sysroot [tmpDir]

    -- ========================================================================
    -- 1. Triple-Compounding `.match_1` Contamination & `isPureVettedMatcher`
    -- ========================================================================
    IO.println "=== 1. Triple-Compounding `.match_1` Contamination in `TrustedBoundary.lean` ==="
    let envMatch ← importModules #[{ module := `Trusted.MatchProbe }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let envMatch := envMatch.setExporting false
    let mut localsMatch : Std.HashMap Name ConstantInfo := {}
    for m in envMatch.header.modules, data in envMatch.header.moduleData do
      if m.module == `Trusted.MatchProbe then
        for ci in data.constants do
          if ci.name != `Trusted.MatchProbe.badVetFn then
            localsMatch := localsMatch.insert ci.name ci

    let declList : List (Name × String) := [
      (`Trusted.candidate, "vetted"),
      (`Trusted.MatchProbe.PureInd, "vetted"),
      (`Trusted.MatchProbe.PureInd.a, "vetted"),
      (`Trusted.MatchProbe.PureInd.b, "vetted"),
      (`Trusted.MatchProbe.candFn, "candidate:mir_semantics"),
      (`Trusted.MatchProbe.vetFn, "vetted"),
      (`Trusted.MatchProbe.candFn2, "candidate:memory"),
      (`Trusted.MatchProbe.ExtInd, "vetted"),
      (`Trusted.MatchProbe.ExtInd.v1, "vetted"),
      (`Trusted.MatchProbe.ExtInd.v2, "vetted"),
      (`Trusted.MatchProbe.ExtInd.c1, "candidate:mir_semantics"),
      (`Trusted.MatchProbe.candExtFn, "candidate:mir_semantics"),
      (`Trusted.MatchProbe.vetExtFn, "vetted"),
      (`Trusted.MatchProbe.candExtFn2, "candidate:memory"),
      (`Trusted.MatchProbe.badVetFn, "vetted")
    ]
    let mut declMap : Std.HashMap Name String := {}
    for (k, v) in declList do
      declMap := declMap.insert k v

    let mut statusMap : Std.HashMap Name String := {}
    let mut ownerMap : Std.HashMap Name Name := {}
    for (cName, _) in localsMatch do
      let (st, ow) ← classifyTrustedConstant declMap cName
      statusMap := statusMap.insert cName st
      ownerMap := ownerMap.insert cName ow

    let (stockErrors, stockAutoHelpers, stockAllowedOwners, stockElimStatuses,
         stockScopedMap) ←
      checkTrustedNonContaminationStock localsMatch localsMatch statusMap
        ownerMap

    IO.println s!"  Stock autoHelpers contains `candFn.match_1`:    {stockAutoHelpers.contains `Trusted.MatchProbe.candFn.match_1}"
    IO.println s!"  Stock autoHelpers contains `candExtFn.match_1`: {stockAutoHelpers.contains `Trusted.MatchProbe.candExtFn.match_1}"
    IO.println s!"  Stock policy rejections count:                  {stockErrors.size}"
    for err in stockErrors do
      IO.println s!"    - policy:{err}"

    assertTrue "Stock autoHelpers omits candFn.match_1"
      (!stockAutoHelpers.contains `Trusted.MatchProbe.candFn.match_1)
    assertTrue "Stock autoHelpers omits candExtFn.match_1 due to ci.all self-edge"
      (!stockAutoHelpers.contains `Trusted.MatchProbe.candExtFn.match_1)
    assertTrue "Stock checkTrustedNonContamination produces 4 false rejections"
      (stockErrors.size == 4)

    let lookupMatch (n : Name) : IO ConstantInfo :=
      match envMatch.checked.get.find? n with
      | some ci => pure ci
      | none => fail s!"missing {n}"
    let stockFeatsNonExt ← collectActiveCandidateFeatures lookupMatch
      (origin envMatch) #[`Trusted.MatchProbe] statusMap ownerMap
      stockAutoHelpers stockAllowedOwners stockElimStatuses stockScopedMap
      #[`Trusted.MatchProbe.vetFn]
    let stockFeatsExt ← collectActiveCandidateFeatures lookupMatch
      (origin envMatch) #[`Trusted.MatchProbe] statusMap ownerMap
      (stockAutoHelpers.insert `Trusted.MatchProbe.candExtFn.match_1)
      stockAllowedOwners stockElimStatuses stockScopedMap
      #[`Trusted.MatchProbe.vetExtFn]

    IO.println s!"  Stock active features on `#[vetFn]`:            {stockFeatsNonExt}"
    IO.println s!"  Stock active features on `#[vetExtFn]` (even with candExtFn.match_1 in autoHelpers): {stockFeatsExt}"
    assertTrue "Stock collectActiveCandidateFeatures falsely activates mir_semantics on vetFn"
      (stockFeatsNonExt == #["mir_semantics"])
    assertTrue "Stock collectActiveCandidateFeatures falsely activates mir_semantics on vetExtFn"
      (stockFeatsExt == #["mir_semantics"])

    let (fixedStatusMap, fixedAutoHelpers, fixedAllowedOwners,
         fixedElimStatuses, fixedScopedMap) ←
      checkTrustedNonContaminationFixed localsMatch localsMatch statusMap
        ownerMap
    let fixedFeatsVetted ← collectActiveCandidateFeatures lookupMatch
      (origin envMatch) #[`Trusted.MatchProbe] fixedStatusMap ownerMap
      fixedAutoHelpers fixedAllowedOwners fixedElimStatuses fixedScopedMap
      #[`Trusted.MatchProbe.vetFn, `Trusted.MatchProbe.vetExtFn]
    let fixedFeatsCand1 ← collectActiveCandidateFeatures lookupMatch
      (origin envMatch) #[`Trusted.MatchProbe] fixedStatusMap ownerMap
      fixedAutoHelpers fixedAllowedOwners fixedElimStatuses fixedScopedMap
      #[`Trusted.MatchProbe.candFn]
    let fixedFeatsCand2 ← collectActiveCandidateFeatures lookupMatch
      (origin envMatch) #[`Trusted.MatchProbe] fixedStatusMap ownerMap
      fixedAutoHelpers fixedAllowedOwners fixedElimStatuses fixedScopedMap
      #[`Trusted.MatchProbe.candFn2, `Trusted.MatchProbe.candExtFn2]

    IO.println s!"  Fixed autoHelpers contains both `.match_1`s:    {fixedAutoHelpers.contains `Trusted.MatchProbe.candFn.match_1 && fixedAutoHelpers.contains `Trusted.MatchProbe.candExtFn.match_1}"
    IO.println s!"  Fixed active features on `#[vetFn, vetExtFn]`:  {fixedFeatsVetted}"
    IO.println s!"  Fixed active features on `#[candFn]`:           {fixedFeatsCand1}"
    IO.println s!"  Fixed active features on `#[candFn2, candExtFn2]`: {fixedFeatsCand2}"

    assertTrue "Fixed autoHelpers contains candFn.match_1"
      (fixedAutoHelpers.contains `Trusted.MatchProbe.candFn.match_1)
    assertTrue "Fixed autoHelpers contains candExtFn.match_1"
      (fixedAutoHelpers.contains `Trusted.MatchProbe.candExtFn.match_1)
    assertTrue "Fixed active features on vetted declarations is empty"
      fixedFeatsVetted.isEmpty
    assertTrue "Fixed active features on candFn is #[mir_semantics]"
      (fixedFeatsCand1 == #["mir_semantics"])
    assertTrue "Fixed active features on candFn2/candExtFn2 is #[memory]"
      (fixedFeatsCand2 == #["memory"])

    let badCi :=
      envMatch.checked.get.find? `Trusted.MatchProbe.badVetFn |>.get!
    let localsWithBad :=
      localsMatch.insert `Trusted.MatchProbe.badVetFn badCi
    let statusWithBad :=
      statusMap.insert `Trusted.MatchProbe.badVetFn "vetted"
    let ownerWithBad :=
      ownerMap.insert `Trusted.MatchProbe.badVetFn `Trusted.MatchProbe.badVetFn
    let badRes ←
      try
        let _ ← checkTrustedNonContaminationFixed localsWithBad localsWithBad
          statusWithBad ownerWithBad
        pure "UNEXPECTED_PASS"
      catch e => pure e.toString
    IO.println s!"  Fixed check on genuinely contaminated `badVetFn`: {badRes}"
    assertTrue "Fixed check rejects badVetFn"
      (badRes != "UNEXPECTED_PASS")

    -- ========================================================================
    -- 2. Cross-Boundary `Trusted.*` `realizeConst` & Phase 1/2 Verification
    -- ========================================================================
    IO.println "\n=== 2. Cross-Boundary `Trusted.*` `realizeConst` & `loadExts := false` ==="
    unsafe enableInitializersExecution
    let parserEnv ← importModules #[{ module := `Init }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)

    let forgedNsSrc :=
      "prelude\nimport Init\nnamespace Trusted\ndef forged : Nat := 42\nend Trusted\n"
    let forgedDeclSrc :=
      "prelude\nimport Init\ndef Trusted.forged : Nat := 42\n"
    let resForgedNs ←
      try
        let _ ← inspectSourceTextParam true true parserEnv `TheoryForge
          forgedNsSrc
        pure "UNEXPECTED_PASS"
      catch e => pure e.toString
    let resForgedDecl ←
      try
        let _ ← inspectSourceTextParam true true parserEnv `TheoryForge
          forgedDeclSrc
        pure "UNEXPECTED_PASS"
      catch e => pure e.toString
    IO.println s!"  Phase 1 untrusted `namespace Trusted`: {resForgedNs}"
    IO.println s!"  Phase 1 untrusted `def Trusted.forged`: {resForgedDecl}"
    assertTrue "Phase 1 blocks untrusted namespace Trusted"
      (resForgedNs ==
        "policy:non-Trusted module cannot open Trusted namespace Trusted")
    assertTrue "Phase 1 blocks untrusted def Trusted.forged"
      (resForgedDecl ==
        "policy:non-Trusted module cannot declare Trusted.forged in Trusted namespace")

    let envRealizeNoExts ← importModules
      #[{ module := `Trusted.RealizeProbe }, { module := `TheoryA },
        { module := `TheoryB }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let envRealizeNoExts := envRealizeNoExts.setExporting false
    unsafe enableInitializersExecution
    let envRealizeWithExts ← importModules
      #[{ module := `Trusted.RealizeProbe }, { module := `TheoryA },
        { module := `TheoryB }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
    let envRealizeWithExts := envRealizeWithExts.setExporting false

    let mut splitterFound := false
    let mut matcherAttachedCount := 0
    for m in envRealizeNoExts.header.modules,
        data in envRealizeNoExts.header.moduleData do
      if m.module == `TheoryA then
        for ci in data.constants do
          let u := (privateToUserName? ci.name).getD ci.name
          let resNoExts := Lean.isReservedName envRealizeNoExts ci.name
          let resWithExts := Lean.isReservedName envRealizeWithExts ci.name
          if u == `Trusted.RealizeProbe.stepOpt.match_1.splitter then
            splitterFound := true
            assertTrue ".splitter is defnInfo, not theorem"
              ((ci matches .defnInfo _) && !ci.isTheorem)
          if let .str p _ := u then
            if p == `Trusted.RealizeProbe.stepOpt.match_1 then
              matcherAttachedCount := matcherAttachedCount + 1
              assertTrue "isReservedName is false under loadExts=false on matcher-attached constant"
                (!resNoExts && resWithExts)

    assertTrue "Found _private.TheoryA.0.Trusted.RealizeProbe.stepOpt.match_1.splitter"
      splitterFound
    assertTrue "Found all 5 matcher-attached realized constants in TheoryA.olean"
      (matcherAttachedCount == 5)

    let stockRealizeRes ←
      try
        let _ ← verifyAndCollectLocalsStock envRealizeNoExts {}
          #[`Trusted.RealizeProbe]
          #[`Trusted.RealizeProbe, `TheoryA, `TheoryB]
        pure "UNEXPECTED_PASS"
      catch e => pure e.toString
    IO.println s!"  Stock `verifyAndCollectLocals`: {stockRealizeRes}"
    assertTrue "Stock verifyAndCollectLocals rejects TheoryA realized constant"
      (stockRealizeRes != "UNEXPECTED_PASS")

    let localsFixed ← verifyAndCollectLocalsFixed envRealizeNoExts {}
      #[`Trusted.RealizeProbe] #[`Trusted.RealizeProbe, `TheoryA, `TheoryB]
    let baseEnv ← importModules #[{ module := `Init }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    let _ ← baseEnv.toKernelEnv.replay localsFixed
    IO.println s!"  Fixed `verifyAndCollectLocalsFixed` + `Kernel.Environment.replay` ({localsFixed.size} constants): PASS"
    assertTrue "Fixed verifyAndCollectLocals collects 19 unique constants"
      (localsFixed.size == 19)

    -- ========================================================================
    -- 3. Phase 1 `decide` `optConfig` Check (`TrustedBoundary.lean:366`)
    -- ========================================================================
    IO.println "\n=== 3. Phase 1 `decide` `optConfig` Check (`TrustedBoundary.lean:366`) ==="
    let decideBareSrc :=
      "prelude\nimport Init\ntheorem t : (2 + 2 == 4) = true := by decide\n"
    let decideNativeSrc :=
      "prelude\nimport Init\ntheorem t : (2 + 2 == 4) = true := by decide +native\n"
    let decideKernelSrc :=
      "prelude\nimport Init\ntheorem t : (2 + 2 == 4) = true := by decide +kernel\n"
    let stockDecideBare ←
      try
        let _ ← inspectSourceTextParam false true parserEnv `TheoryA
          decideBareSrc
        pure "PASS"
      catch e => pure e.toString
    let fixedDecideBare ←
      try
        let _ ← inspectSourceTextParam true true parserEnv `TheoryA
          decideBareSrc
        pure "PASS"
      catch e => pure e.toString
    let fixedDecideNative ←
      try
        let _ ← inspectSourceTextParam true true parserEnv `TheoryA
          decideNativeSrc
        pure "UNEXPECTED_PASS"
      catch e => pure e.toString
    let fixedDecideKernel ←
      try
        let _ ← inspectSourceTextParam true true parserEnv `TheoryA
          decideKernelSrc
        pure "UNEXPECTED_PASS"
      catch e => pure e.toString

    IO.println s!"  Stock (`s[1].getArgs.isEmpty`) on bare `by decide`:       {stockDecideBare}"
    IO.println s!"  Fixed (`s[1][0].getArgs.isEmpty`) on bare `by decide`:    {fixedDecideBare}"
    IO.println s!"  Fixed (`s[1][0].getArgs.isEmpty`) on `by decide +native`: {fixedDecideNative}"
    IO.println s!"  Fixed (`s[1][0].getArgs.isEmpty`) on `by decide +kernel`: {fixedDecideKernel}"

    assertTrue "Stock decide check rejects bare by decide"
      (stockDecideBare == "policy:decide configuration is unsupported")
    assertTrue "Fixed decide check admits bare by decide"
      (fixedDecideBare == "PASS")
    assertTrue "Fixed decide check rejects by decide +native"
      (fixedDecideNative == "policy:decide configuration is unsupported")
    assertTrue "Fixed decide check rejects by decide +kernel"
      (fixedDecideKernel == "policy:decide configuration is unsupported")

    IO.println "\nAll ProbeTrustedBoundaryFixes assertions passed."
    return 0

end ProbeTrustedBoundaryFixes

def main : IO UInt32 := ProbeTrustedBoundaryFixes.main
