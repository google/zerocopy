-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay

open Lean

/-!
# Building Block A Prototype: `PureMacroAudit.lean`

Pinned to Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

Demonstrates how a verifier can safely admit pure `syntax`, `notation`, `infixl`,
`macro`, and `macro_rules` declarations in `Theory.lean` without OS sandboxing by
combining three complementary checks:

1. **Check 1 — Macro-Definition Purity Check (`checkMacroDefinitionPurity`)**:
   Every `@[macro]` `meta def` (and auxiliary parser/unexpander/helper definition)
   generated in `Theory.lean` must have:
   - `safety == .safe` (`!ci.isUnsafe && !ci.isPartial`),
   - zero `@[implemented_by]` overrides (`Compiler.getImplementedBy? env name == none`),
   - zero `@[extern]` overrides (`!ci.isExtern env`), and
   - a transitive constant cone (`collectExprConsts`) lying strictly within
     `Init.*`, `Trusted.*`, and already-verified `Theory.*` constants, excluding
     effectful/escape primitives (`dbgTrace`, `dbgSleep`, `dbgStackTrace`,
     `dbgTraceIfShared`, `unsafeIO`, `unsafeBaseIO`, `unsafeEIO`, `sorryAx`,
     and `ST.Prim.*` / `IO.Prim.*`).

2. **Check 2 — Post-Expansion Syntax Audit (`expandAndAuditCommand`)**:
   Before any non-macro command in `Theory.lean` or `Proof.lean` is passed to
   `Command.elabCommand`, a recursive `MacroM` pass (`expandUserMacrosRec`) expands
   all user-defined macros and notations using `Macro.expandMacro?` and validates
   the resulting expanded `Syntax` tree against `allowedTheorySyntaxKinds`
   (`inspectSyntax`). Any Trojan macro expanding into `by_elab`, `include_str`,
   `#eval`, `run_cmd`, `native_decide`, or `sorry` is caught and rejected in pure
   `MacroM` *before* `CommandElabM` or `TermElabM` executes.

3. **Check 3 — Namespace-Component & Kernel Statement-Identity Verification**:
   - **(3a) Namespace-Component Check**: No non-`Trusted` module (`Theory` or
     `Proof`) may declare a constant whose user name components contain `` `Trusted ``
     (`(privateToUserName ci.name).components.contains `Trusted`), closing the
     `Proof.Trusted.CrateTheorem` enclosing-namespace shadowing bypass from
     .
   - **(3b) Kernel Statement-Identity Check**: After replaying all non-foundation
     constants through `Kernel.Environment.replay` at `trustLevel := 0`, the
     replayed `Proof.verify_crate` theorem in `Kernel.Environment` must have
     `ci.type == mkApp (mkConst ``Trusted.CrateTheorem) (mkConst targetCrateConst)`
     with zero `.theory` constants in `ci.type` and zero unapproved axioms.
-/

namespace PureMacroAudit

/-! ## 1. Syntax Allowlists (from `TrustedBoundary.lean`, plus macro-definition commands in `Theory`) -/

def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.prelude, ``Parser.Module.import]

def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

/-- Metaprogramming declaration commands permitted in `Theory.lean` only (subject to
    Check 1 Macro-Definition Purity immediately after elaboration). -/
def allowedTheoryMacroDefCommandKinds : List Name := [
  ``Parser.Command.syntax,
  ``Parser.Command.notation,
  ``Parser.Command.mixfix,
  ``Parser.Command.macro,
  ``Parser.Command.macro_rules]

def allowedDeclarationKinds : List Name := [
  ``Parser.Command.abbrev, ``Parser.Command.definition,
  ``Parser.Command.theorem, ``Parser.Command.opaque,
  ``Parser.Command.instance, ``Parser.Command.inductive,
  ``Parser.Command.classInductive, ``Parser.Command.structure]

def allowedCommandSyntaxKinds : List Name := [
  ``Parser.Command.declModifiers, ``Parser.Command.declId,
  ``Parser.Command.declSig, ``Parser.Command.optDeclSig,
  ``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
  ``Parser.Command.whereStructInst, ``Parser.Command.docComment,
  ``Parser.Command.private, ``Parser.Command.protected,
  ``Parser.Command.noncomputable, ``Parser.Command.openSimple,
  ``Parser.Command.sectionHeader, ``Parser.Command.eraseAttr,
  ``Parser.Command.ctor, ``Parser.Command.optDeriving,
  ``Parser.Command.optDefDeriving, ``Parser.Command.classTk,
  ``Parser.Command.structureTk, ``Parser.Command.extends,
  ``Parser.Command.structCtor, ``Parser.Command.structFields,
  ``Parser.Command.structSimpleBinder, ``Parser.Command.structExplicitBinder,
  ``Parser.Command.structImplicitBinder, ``Parser.Command.structInstBinder,
  ``Parser.Command.structParent, ``Parser.Termination.suffix,
  ``Lean.binderIdent, ``Lean.explicitBinders,
  ``Lean.bracketedExplicitBinders, ``Lean.unbracketedExplicitBinders]

def allowedTermSyntaxKinds : List Name := [
  ``Parser.Term.anonymousCtor, ``Parser.Term.app, ``Parser.Term.arrow,
  ``Parser.Term.attrInstance, ``Parser.Term.attrKind,
  ``Parser.Term.attributes, ``Parser.Term.basicFun,
  ``Parser.Term.binderDefault, ``Parser.Term.cdot, ``Parser.Term.dotIdent,
  ``Parser.Term.explicit, ``Parser.Term.explicitBinder,
  ``Parser.Term.forall, ``Parser.Term.fromTerm, ``Parser.Term.fun,
  ``Parser.Term.have, `Lean.Parser.Term.haveDecl, `Lean.Parser.Term.haveId,
  `Lean.Parser.Term.haveIdDecl, `Lean.Parser.Term.haveIdLhs, ``Parser.Term.hole,
  ``Parser.Term.hygienicLParen, ``Parser.Term.implicitBinder,
  ``Parser.Term.instBinder, ``Parser.Term.let, ``Parser.Term.letConfig,
  ``Parser.Term.letDecl, ``Parser.Term.letId, ``Parser.Term.letIdDecl,
  ``Parser.Term.letPatDecl, ``Parser.Term.match, ``Parser.Term.matchAlt,
  ``Parser.Term.matchAlts, ``Parser.Term.matchAltsWhereDecls,
  ``Parser.Term.matchDiscr, ``Parser.Term.namedArgument,
  ``Parser.Term.nomatch, ``Parser.Term.optEllipsis, ``Parser.Term.paren,
  ``Parser.Term.proj, ``Parser.Term.prop, ``Parser.Term.show,
  ``Parser.Term.sort, ``Parser.Term.strictImplicitBinder,
  ``Parser.Term.structInst, ``Parser.Term.structInstField,
  ``Parser.Term.structInstFieldDef, ``Parser.Term.structInstFieldEqns,
  ``Parser.Term.structInstFields, ``Parser.Term.structInstLVal,
  ``Parser.Term.subst, ``Parser.Term.syntheticHole, ``Parser.Term.tuple,
  ``Parser.Term.type, ``Parser.Term.typeAscription, ``Parser.Term.typeSpec,
  ``Parser.Attr.simple, ``Parser.Attr.instance, `Lean.Parser.Attr.simp,
  `fieldIdx, `group, `hygieneInfo, `num, `str, `char, `scientific]

def allowedNotationSyntaxKinds : List Name := [
  `term!_, `termIfThenElse, `termDepIfThenElse, `«term[_]»,
  `«term_&&_», `«term_||_», `«term_+_», `«term_-_», `«term_*_»,
  `«term_::_», `«term_++_», `«term_<_», `«term_≤_», `«term_>_»,
  `«term_≥_», `«term_==_», `«term_!=_», `«term_=_», `«term_≠_»,
  `«term__[_]_?», `«term_×_», `«term_↔_», `«term_∈_», `«term_∧_»,
  `«term_∨_», `«term¬_», `«term∃_,_», `«term‹_›», `Lean.cdot, `Lean.cdotTk]

def allowedTheoryTacticKinds : List Name := [
  ``Parser.Term.byTactic, ``Parser.Term.binderTactic,
  `Lean.Parser.Tactic.apply, `Lean.Parser.Tactic.cases,
  `Lean.Parser.Tactic.change, `Lean.Parser.Tactic.constructor,
  `Lean.Parser.Tactic.decide, `Lean.Parser.Tactic.dsimp,
  `Lean.Parser.Tactic.elimTarget, `Lean.Parser.Tactic.exact,
  `Lean.Parser.Tactic.first, `Lean.Parser.Tactic.induction,
  `Lean.Parser.Tactic.inductionAlt, `Lean.Parser.Tactic.inductionAltLHS,
  `Lean.Parser.Tactic.inductionAlts, `Lean.Parser.Tactic.injection,
  `Lean.Parser.Tactic.intro, `Lean.Parser.Tactic.left,
  `Lean.Parser.Tactic.location, `Lean.Parser.Tactic.locationHyp,
  `Lean.Parser.Tactic.optConfig, `Lean.Parser.Tactic.paren,
  `Lean.Parser.Tactic.refine, `Lean.Parser.Tactic.revert,
  `Lean.Parser.Tactic.right, `Lean.Parser.Tactic.rwRule,
  `Lean.Parser.Tactic.rwRuleSeq, `Lean.Parser.Tactic.rwSeq,
  `Lean.Parser.Tactic.simp, `Lean.Parser.Tactic.simpLemma,
  `Lean.Parser.Tactic.subst, `Lean.Parser.Tactic.tacticHave__,
  `Lean.Parser.Tactic.tacticLet__, `Lean.Parser.Tactic.«tacticNomatch_,,»,
  `Lean.Parser.Tactic.tacticRepeat_, `Lean.Parser.Tactic.tacticRfl,
  `Lean.Parser.Tactic.tacticSeq, `Lean.Parser.Tactic.tacticSeq1Indented,
  `Lean.Parser.Tactic.«tactic_<;>_», `Lean.Parser.Tactic.unfold,
  `tacticFunext___]

def allowedTrustedSyntaxKinds : NameSet :=
  .ofList <|
    allowedHeaderKinds ++
    allowedCommandKinds ++
    allowedDeclarationKinds ++
    allowedCommandSyntaxKinds ++
    allowedTermSyntaxKinds ++
    allowedNotationSyntaxKinds

def allowedTheorySyntaxKinds : NameSet :=
  allowedTrustedSyntaxKinds ++ .ofList allowedTheoryTacticKinds

def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

/-- Validate an identifier after macro expansion: hygienic macro scopes added by
    quotation expansion are stripped via `eraseMacroScopes`, and no component may
    be empty or use `_root_`. -/
def isValidExpandedIdent (id : Name) : Bool :=
  let base := id.eraseMacroScopes
  base.isAnonymous ||
    (!base.toString.isEmpty &&
     base.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

def isAllowedNestedCommand (k : SyntaxNodeKind) : Bool :=
  allowedCommandKinds.contains k &&
    ![``Parser.Command.namespace, ``Parser.Command.section,
      ``Parser.Command.end, ``Parser.Command.mutual].contains k

def inspectNodeKind (k : SyntaxNodeKind) (args : Array Syntax) : Except String Unit := do
  if k == ``Parser.Module.header then
    unless !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
      throw "policy:explicit prelude is required"
  else if k == ``Parser.Command.sectionHeader then
    unless args.all (·.getArgs.isEmpty) do
      throw "policy:section/namespace modifiers are unsupported"
  else if k == ``Parser.Command.declaration then
    let declKind := args[1]?.map Syntax.getKind |>.getD .anonymous
    unless allowedDeclarationKinds.contains declKind do
      throw s!"policy:unsupported declaration kind {declKind}"
  else if k == ``Parser.Command.mutual then
    unless args.size == 3 &&
        args[1]!.getArgs.all (isAllowedNestedCommand ·.getKind) do
      throw "policy:unsupported mutual-block shape"
  else if k == ``Parser.Command.in then
    unless args.size == 3 do throw "policy:unsupported command-wrapper shape"
    unless [``Parser.Command.open, ``Parser.Command.variable].contains
        args[0]!.getKind do
      throw "policy:only `open` and `variable` commands are permitted on the LHS of `in`"
    unless isAllowedNestedCommand args[2]!.getKind do
      throw s!"policy:unsupported command inside `in`: {args[2]!.getKind}"
  else if k == ``Parser.Attr.simple then
    let attrName := args[0]?.map Syntax.getId |>.getD .anonymous
    unless allowedAttributeNames.contains attrName do
      throw s!"policy:unsupported attribute {attrName}"
    unless (args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
      throw s!"policy:unsupported arguments on attribute {attrName}"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    unless (args.extract 1 args.size).all (·.getArgs.isEmpty) do
      throw s!"policy:unsupported arguments on attribute {k}"
  else if k == ``Parser.Command.eraseAttr then
    let attrName := args[1]?.map Syntax.getId |>.getD .anonymous
    unless allowedAttributeNames.contains attrName do
      throw s!"policy:unsupported attribute removal {attrName}"

partial def inspectSyntax (allowedKinds : NameSet) (s : Syntax) : Except String Unit := do
  match s with
  | .missing => throw "policy:unexpected missing syntax node"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidExpandedIdent val do
      throw s!"policy:invalid identifier {val}"
  | .node _ k args =>
    unless k == nullKind || allowedKinds.contains k do
      throw s!"policy:unsupported syntax kind {k}"
    inspectNodeKind k args
    for child in args do
      inspectSyntax allowedKinds child

/-! ## 2. Check 1: Macro-Definition Purity Check (`checkMacroDefinitionPurity`) -/

/-- Pure DAG traversal collecting all constants referenced in `pending`. -/
partial def collectExprConsts (pending : List Expr)
    (seen : Std.HashSet Expr := {}) (acc : NameSet := {}) : NameSet :=
  match pending with
  | [] => acc
  | x :: rest =>
    if seen.contains x then
      collectExprConsts rest seen acc
    else
      let seen := seen.insert x
      match x with
      | .const n _ => collectExprConsts rest seen (acc.insert n)
      | .lit (.natVal _) => collectExprConsts rest seen (acc.insert `Nat)
      | .lit (.strVal _) => collectExprConsts rest seen (acc.insert `String)
      | .app a b | .forallE _ a b _ | .lam _ a b _ =>
        collectExprConsts (a :: b :: rest) seen acc
      | .letE _ t v b _ =>
        collectExprConsts (t :: v :: b :: rest) seen acc
      | .proj s _ b =>
        collectExprConsts (b :: rest) seen (acc.insert s)
      | .mdata _ b =>
        collectExprConsts (b :: rest) seen acc
      | .bvar _ | .fvar _ | .mvar _ | .sort _ =>
        collectExprConsts rest seen acc

def directConstantDeps (ci : ConstantInfo) : NameSet :=
  let typeDeps := collectExprConsts [ci.type]
  let valDeps := match ci.value? (allowOpaque := true) with
    | some v => collectExprConsts [v]
    | none   => {}
  typeDeps ++ valDeps ++ .ofList ci.all

/-- Denylist of `Init.*` constants that can perform side effects, sleep, trace,
    or escape `MacroM` purity despite having pure-looking Lean types. -/
def forbiddenMacroPrimitives : NameSet := .ofList [
  `dbgTrace, `dbgTraceVal, `dbgSleep, `dbgStackTrace, `dbgTraceIfShared,
  `unsafeIO, `unsafeBaseIO, `unsafeEIO, `sorryAx, `lcErased
]

def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def isForbiddenMacroNamespace (n : Name) : Bool :=
  let u := privateToUserName n
  Name.isPrefixOf `ST.Prim u || Name.isPrefixOf `IO.Prim u || Name.isPrefixOf `BaseIO u

/-- Compute the transitive constant cone of `roots` within `env` and verify that:
    1. Every constant in the cone has `safety == .safe` (`!isUnsafe && !isPartial`),
    2. Every local constant has `Compiler.getImplementedBy? env c == none` and `!Lean.isExtern env c`,
    3. Every constant originates in `Init.*`, `Trusted.*`, `Mir.*`, or verified local `Theory` constants,
    4. No constant in the cone belongs to `forbiddenMacroPrimitives` or `ST.Prim.*`/`IO.Prim.*`. -/
partial def checkTransitivePurityCone (env : Environment) (trustedConsts : NameSet)
    (verifiedLocals : NameSet) (pending : List Name) (visited : NameSet := {}) :
    Except String NameSet := do
  match pending with
  | [] => return visited
  | c :: rest =>
    if visited.contains c then
      checkTransitivePurityCone env trustedConsts verifiedLocals rest visited
    else
      let visited := visited.insert c
      if forbiddenMacroPrimitives.contains c || isForbiddenMacroNamespace c then
        throw s!"policy:macro-purity:forbidden effectful/escape primitive `{c}` in macro cone"
      let isLocal := (env.getModuleIdxFor? c).isNone && !trustedConsts.contains c
      if isLocal then
        if let some impl := Compiler.getImplementedBy? env c then
          throw s!"policy:macro-purity:`{c}` has @[implemented_by {impl}] override"
        if Lean.isExtern env c then
          throw s!"policy:macro-purity:local constant `{c}` is @[extern]"
      let some ci := env.find? c
        | throw s!"policy:macro-purity:unknown constant `{c}`"
      if ci.isUnsafe || ci.isPartial then
        throw s!"policy:macro-purity:non-safe constant `{c}` (isUnsafe={ci.isUnsafe}, isPartial={ci.isPartial}) in macro cone"
      match env.getModuleIdxFor? c with
      | some modIdx =>
        let modName := env.header.modules[modIdx]!.module
        let root := modName.getRoot
        unless root == `Init || modName == `Trusted || modName == `Mir do
          throw s!"policy:macro-purity:constant `{c}` from unverified module `{modName}`"
        checkTransitivePurityCone env trustedConsts verifiedLocals rest visited
      | none =>
        if trustedConsts.contains c then
          checkTransitivePurityCone env trustedConsts verifiedLocals rest visited
        else
          unless verifiedLocals.contains c do
            throw s!"policy:macro-purity:unverified local constant `{c}`"
          let deps := directConstantDeps ci
          checkTransitivePurityCone env trustedConsts verifiedLocals (deps.toList ++ rest) visited

/-- Run Check 1 on all newly elaborated non-Trusted constants in `env`. -/
def checkMacroDefinitionPurity (env : Environment) (trustedConsts : NameSet) :
    Except String (Array String) := do
  let stage2 : Array (Name × ConstantInfo) :=
    env.constants.foldStage2 (fun acc n ci =>
      if trustedConsts.contains n then acc else acc.push (n, ci)) #[]
  let mut localSet : NameSet := {}
  for (n, ci) in stage2 do
    -- (3a) Namespace-component check on all Theory/Proof declarations
    if (privateToUserName n).components.contains `Trusted then
      throw s!"policy:namespace-hygiene:non-Trusted module cannot declare `{n}` containing component `Trusted"
    if ci.isUnsafe || ci.isPartial then
      throw s!"policy:macro-purity:local declaration `{n}` is unsafe/partial (isUnsafe={ci.isUnsafe}, isPartial={ci.isPartial})"
    if ci.isAxiom then
      throw s!"policy:macro-purity:local declaration `{n}` is an axiom"
    if let some impl := Compiler.getImplementedBy? env n then
      throw s!"policy:macro-purity:local declaration `{n}` has @[implemented_by {impl}]"
    if Lean.isExtern env n then
      throw s!"policy:macro-purity:local declaration `{n}` has @[extern]"
    localSet := localSet.insert n

  -- Also verify no Trusted constant was retroactively given `@[implemented_by]` or `@[extern]`
  for tc in trustedConsts do
    if let some impl := Compiler.getImplementedBy? env tc then
      throw s!"policy:macro-purity:Trusted constant `{tc}` retroactively given @[implemented_by {impl}]"
    if Lean.isExtern env tc then
      throw s!"policy:macro-purity:Trusted constant `{tc}` retroactively given @[extern]"

  let mut checkedMacros : Array String := #[]
  for (n, ci) in stage2 do
    let deps := directConstantDeps ci
    discard <| checkTransitivePurityCone env trustedConsts localSet (n :: deps.toList)
    let userN := (privateToUserName n).toString
    if hasSubstr userN "macroRules" || ci.type.isConstOf ``Lean.Macro then
      checkedMacros := checkedMacros.push userN
  return checkedMacros

/-! ## 3. Check 2: Post-Expansion Syntax Audit (`expandAndAuditSyntax`) -/

/-- Returns `true` if `k` has at least one non-foundation (user-defined in `Theory`)
    `@[macro]` entry registered in `env`.
    Note: `KeyedDeclsAttribute` sets `isBuiltin := false` for all `.olean` entries
    (including `Init.Notation`), so we check `(env.getModuleIdxFor? e.declName).isNone`
    to identify macros defined in `Theory` rather than `Init.*`. -/
def hasUserMacroForKind (env : Environment) (trustedConsts : NameSet) (k : SyntaxNodeKind) : Bool :=
  (Elab.macroAttribute.getEntries env k).any fun e =>
    (env.getModuleIdxFor? e.declName).isNone && !trustedConsts.contains e.declName

/-- Recursively expand all user-defined macros and notations in `stx` using pure
    `Macro.expandMacro?` before any `CommandElabM` or `TermElabM` elaborator runs.
    Tracks every user macro expansion performed. -/
partial def expandUserMacrosRec (env : Environment) (trustedConsts : NameSet)
    (allowedKinds : NameSet) (fuel : Nat) (stx : Syntax) :
    MacroM (Syntax × Array String) := do
  match fuel with
  | 0 => Macro.throwError "policy:macro expansion exceeded fuel limit (1024)"
  | fuel' + 1 =>
    match stx with
    | .node info k args =>
      -- Expand whenever a user macro is registered for `k` OR `k` is not in `allowedKinds`
      if hasUserMacroForKind env trustedConsts k || (k != nullKind && !allowedKinds.contains k) then
        match (← Macro.expandMacro? stx) with
        | some stx' =>
          let (res, trace) ← expandUserMacrosRec env trustedConsts allowedKinds fuel' stx'
          return (res, #[s!"{k} -> {stx'.getKind}"] ++ trace)
        | none =>
          -- No macro expanded `stx`; recurse on children (if `k` is disallowed, `inspectSyntax` will reject it)
          let mut newArgs : Array Syntax := #[]
          let mut allTraces : Array String := #[]
          for arg in args do
            let (arg', tr) ← expandUserMacrosRec env trustedConsts allowedKinds fuel' arg
            newArgs := newArgs.push arg'
            allTraces := allTraces ++ tr
          return (.node info k newArgs, allTraces)
      else
        let mut newArgs : Array Syntax := #[]
        let mut allTraces : Array String := #[]
        for arg in args do
          let (arg', tr) ← expandUserMacrosRec env trustedConsts allowedKinds fuel' arg
          newArgs := newArgs.push arg'
          allTraces := allTraces ++ tr
        return (.node info k newArgs, allTraces)
    | other => return (other, #[])

/-- Run `expandUserMacrosRec` inside pure `MacroM` and then enforce `inspectSyntax`
    on the expanded `Syntax` tree before elaboration. -/
def expandAndAuditCommand (stx : Syntax) (trustedConsts : NameSet) (allowedKinds : NameSet) :
    Elab.Command.CommandElabM (Syntax × Array String) := do
  let env ← getEnv
  let (expanded, traces) ← Elab.liftMacroM <| expandUserMacrosRec env trustedConsts allowedKinds 1024 stx
  let topKind := expanded.getKind
  unless allowedCommandKinds.contains topKind do
    throwError s!"policy:post-expansion-audit:unsupported top-level command `{topKind}`"
  match inspectSyntax allowedKinds expanded with
  | .ok () => return (expanded, traces)
  | .error err => throwError s!"policy:post-expansion-audit:{err}"

/-- Pre-check a `syntax` / `notation` / `macro` / `macro_rules` command in `Theory.lean`
    to ensure its own definition AST contains no effectful term/command syntax
    (`by_elab`, `include_str`, `#eval`, `run_cmd`, `native_decide`, `sorry`). -/
partial def checkMacroDefAstNoForbiddenNodes (s : Syntax) : Except String Unit := do
  match s with
  | .missing => throw "policy:unexpected missing syntax node in macro definition"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidExpandedIdent val do
      throw s!"policy:invalid identifier `{val}` in macro definition"
  | .node _ k args =>
    let forbiddenInMacroDef : List Name := [
      `Lean.Parser.Term.byElab, `Lean.Parser.Term.includeStr,
      `Lean.Parser.Command.eval, `Lean.Parser.Command.runCmd,
      `Lean.Parser.Tactic.nativeDecide, `Lean.Parser.Term.sorry,
      `Lean.Parser.Tactic.tacticSorry, `Lean.Parser.Term.unsafe
    ]
    if forbiddenInMacroDef.contains k then
      throw s!"policy:macro-def-ast:forbidden syntax `{k}` inside macro definition"
    for child in args do
      checkMacroDefAstNoForbiddenNodes child

/-! ## 4. Elaborate & Audit Pipeline for `Theory.lean` + `Proof.lean` -/

/-- Parse and elaborate a `Theory` or `Proof` source string command-by-command,
    enforcing Check 1 (Macro-Definition Purity) and Check 2 (Post-Expansion Syntax Audit)
    before any effectful elaborator can run. -/
def elaborateAndAuditModule (initEnv : Environment) (trustedConsts : NameSet)
    (modName : Name) (allowMacroDefs : Bool) (source : String) :
    IO (Except String (Environment × Array String × Array String)) := do
  let inputCtx := Parser.mkInputContext source s!"<{modName}>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors || parserState.recovering then
    return .error s!"policy:header parser error in {modName}"
  if let .error e := inspectSyntax allowedTheorySyntaxKinds header.raw then
    return .error e

  let cmdState0 : Elab.Command.State :=
    Elab.Command.mkState (initEnv.setMainModule modName) messages {}
  let mut parserState := parserState
  let mut cmdState := cmdState0
  let mut checkedMacros : Array String := #[]
  let mut expansionTraces : Array String := #[]

  while true do
    let scope := cmdState.scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := cmdState.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls
    }
    let (stx, nextParserState, nextMsgs) :=
      Parser.parseCommand inputCtx pmctx parserState cmdState.messages
    parserState := nextParserState
    cmdState := { cmdState with messages := nextMsgs }
    if nextMsgs.hasErrors || nextParserState.recovering then
      let errs ← (nextMsgs.toList.filter (·.severity == .error)).mapM (·.data.toString)
      return .error s!"parser error in {modName}: {String.intercalate "; " errs}"
    if stx.isOfKind ``Parser.Command.eoi then
      break

    let topKind := stx.getKind
    if allowMacroDefs && allowedTheoryMacroDefCommandKinds.contains topKind then
      -- Pre-screen the macro definition AST for forbidden syntax
      if let .error e := checkMacroDefAstNoForbiddenNodes stx then
        return .error e
      -- Elaborate the syntax/notation/macro/macro_rules command
      let ctx : Elab.Command.Context := {
        fileName := inputCtx.fileName
        fileMap := inputCtx.fileMap
        snap? := none
        cancelTk? := none
      }
      match ← (Elab.Command.elabCommandTopLevel stx).run ctx |>.run cmdState |>.toIO' with
      | .error ex =>
        return .error s!"elaboration exception in {modName}: {← ex.toMessageData.toString}"
      | .ok (_, cmdState') =>
        cmdState := cmdState'
        if cmdState.messages.hasErrors then
          let errs ← (cmdState.messages.toList.filter (·.severity == .error)).mapM (·.data.toString)
          return .error s!"elaboration error in {modName}: {String.intercalate "; " errs}"
        -- Immediately enforce Check 1 (Macro-Definition Purity Check) before the macro can be invoked!
        match checkMacroDefinitionPurity cmdState.env trustedConsts with
        | .ok macros => checkedMacros := checkedMacros ++ macros
        | .error e => return .error e
    else
      -- Standard command in Theory or Proof: run Check 2 (Post-Expansion Syntax Audit) BEFORE elabCommand!
      let ctx : Elab.Command.Context := {
        fileName := inputCtx.fileName
        fileMap := inputCtx.fileMap
        snap? := none
        cancelTk? := none
      }
      let expandAct : Elab.Command.CommandElabM (Syntax × Array String) :=
        expandAndAuditCommand stx trustedConsts allowedTheorySyntaxKinds
      match ← expandAct.run ctx |>.run cmdState |>.toIO' with
      | .error ex =>
        return .error (← ex.toMessageData.toString)
      | .ok ((expandedStx, traces), cmdStateAfterExpand) =>
        expansionTraces := expansionTraces ++ traces
        cmdState := cmdStateAfterExpand
        -- Now elaborate the ALREADY-EXPANDED and syntax-audited command!
        match ← (Elab.Command.elabCommandTopLevel expandedStx).run ctx |>.run cmdState |>.toIO' with
        | .error ex =>
          return .error s!"elaboration exception in {modName}: {← ex.toMessageData.toString}"
        | .ok (_, cmdStateAfterElab) =>
          cmdState := cmdStateAfterElab
          if cmdState.messages.hasErrors then
            let errs ← (cmdState.messages.toList.filter (·.severity == .error)).mapM (·.data.toString)
            return .error s!"elaboration error in {modName}: {String.intercalate "; " errs}"
          -- Also run Check 1 on any new declarations added by this command
          match checkMacroDefinitionPurity cmdState.env trustedConsts with
          | .ok _ => pure ()
          | .error e => return .error e

  return .ok (cmdState.env, checkedMacros, expansionTraces)

/-! ## 5. Check 3: Kernel Replay + Namespace-Component + Statement-Identity Verification -/

def verifyKernelAndStatementIdentity (baseEnv : Environment) (finalEnv : Environment)
    (trustedConsts : NameSet) (targetThmName : Name) (targetCrateConst : Name) :
    IO (Except String String) := do
  -- Collect all Stage-2 constants (Theory + Proof)
  let stage2 : Array (Name × ConstantInfo) :=
    finalEnv.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) #[]
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut theoryAndProofConsts : NameSet := {}
  for (n, ci) in stage2 do
    if !trustedConsts.contains n then
      theoryAndProofConsts := theoryAndProofConsts.insert n
      -- Check 3a: Namespace-component check (`Proof.Trusted.CrateTheorem` has component `Trusted!)
      if (privateToUserName n).components.contains `Trusted then
        return .error s!"policy:namespace-hygiene:non-Trusted constant `{n}` contains namespace component `Trusted"
    if ci.isUnsafe || ci.isPartial || ci.isAxiom then
      return .error s!"policy:kernel-audit:unsafe/partial/axiom constant `{n}`"
    replayMap := replayMap.insert n ci

  -- Replay all Stage-2 constants on `baseEnv.toKernelEnv` at trustLevel := 0
  let kenv ← try
    IO.ofExcept <| JustReplay.replay baseEnv.toKernelEnv replayMap
  catch _ =>
    try
      baseEnv.toKernelEnv.replay replayMap
    catch ex =>
      return .error s!"policy:kernel-replay-failed:{ex.toString}"

  -- Check 3b: Exact statement identity in `Kernel.Environment`
  let some kci := kenv.find? targetThmName
    | return .error s!"policy:statement-identity:missing target theorem `{targetThmName}` in Kernel.Environment"
  let expectedType := mkApp (mkConst `Trusted.CrateTheorem) (mkConst targetCrateConst)
  unless kci.type == expectedType do
    return .error s!"policy:statement-identity:`{targetThmName}` has kernel type `{kci.type}`, expected exact `{expectedType}`"

  -- Also verify that zero constants in `kci.type` come from `Theory` or `Proof`
  let stmtConsts := collectExprConsts [kci.type]
  for sc in stmtConsts do
    if theoryAndProofConsts.contains sc then
      return .error s!"policy:statement-identity:theorem statement references non-Trusted constant `{sc}`"

  return .ok s!"replayed {replayMap.size} constants; `{targetThmName} : {kci.type}` matches exact `Trusted.CrateTheorem {targetCrateConst}`"
where
  JustReplay.replay (_ : Kernel.Environment) (_ : Std.HashMap Name ConstantInfo) : Except String Kernel.Environment :=
    .error "use IO replay"

/-! ## 6. Test Suite Covering Benign + All 3 Attack Families -/

structure AuditTestCase where
  id               : String
  description      : String
  expectPass       : Bool
  expectedCheckTag : String
  targetCrateConst : Name
  theorySource     : String
  proofSource      : String

def trustedSetupSource : String :=
  "prelude\n" ++
  "import Init.Prelude\n" ++
  "import Init.Core\n" ++
  "import Init.Notation\n" ++
  "import Init.Tactics\n" ++
  "import Init.Data.Nat.Basic\n" ++
  "import Init.Util\n" ++
  "import Init.System.IO\n" ++
  "namespace Trusted\n" ++
  "structure Crate where\n" ++
  "  entryReturnVal : Nat\n" ++
  "  expectedVal    : Nat\n" ++
  "def SafeExec (c : Crate) : Bool :=\n" ++
  "  Nat.beq c.entryReturnVal c.expectedVal\n" ++
  "def CrateTheorem (c : Crate) : Prop :=\n" ++
  "  SafeExec c = true\n" ++
  "end Trusted\n" ++
  "namespace Mir\n" ++
  "def goodCrate : Trusted.Crate := { entryReturnVal := 42, expectedVal := 42 }\n" ++
  "def badCrate  : Trusted.Crate := { entryReturnVal := 0,  expectedVal := 1 }\n" ++
  "end Mir\n"

def testSuite : Array AuditTestCase := #[
  -- Test 1: Benign Theory defining custom `notation`, `infixl`, `syntax`, and `macro_rules` used in `Proof.lean`
  { id := "T1_benign_notation_and_macro_rules",
    description := "Benign Theory module defining custom notation, infixl, syntax, and macro_rules used in Proof.lean",
    expectPass := true,
    expectedCheckTag := "PASS",
    targetCrateConst := `Mir.goodCrate,
    theorySource :=
      "prelude\n" ++
      "namespace Theory\n" ++
      "notation \"CrateHolds\" c:arg => Trusted.SafeExec c = true\n" ++
      "infixl:65 \" +++ \" => Nat.add\n" ++
      "syntax \"discharge_crate\" : tactic\n" ++
      "macro_rules\n" ++
      "  | `(tactic| discharge_crate) => `(tactic| rfl)\n" ++
      "theorem add_zero_custom (n : Nat) : n +++ 0 = n := Nat.add_zero n\n" ++
      "theorem crate_lemma (c : Trusted.Crate) (h : CrateHolds c) : Trusted.CrateTheorem c := h\n" ++
      "end Theory\n",
    proofSource :=
      "prelude\n" ++
      "open Theory\n" ++
      "namespace Proof\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.goodCrate := by\n" ++
      "  apply Theory.crate_lemma\n" ++
      "  discharge_crate\n" ++
      "end Proof\n"
  },

  -- Test 2a: Malicious Theory with Trojan macro expanding to `by_elab`
  { id := "T2a_malicious_trojan_macro_by_elab",
    description := "Malicious Theory with a Trojan macro expanding into `by_elab` (rejected by Check 2 before elaboration)",
    expectPass := false,
    expectedCheckTag := "post-expansion-audit",
    targetCrateConst := `Mir.badCrate,
    theorySource :=
      "prelude\n" ++
      "namespace Theory\n" ++
      "syntax \"trojan_by_elab\" : term\n" ++
      "macro_rules\n" ++
      "  | `(trojan_by_elab) => `(by_elab Lean.Elab.Term.elabTerm (← `(True.intro)) none)\n" ++
      "theorem exploit : True := trojan_by_elab\n" ++
      "end Theory\n",
    proofSource :=
      "prelude\n" ++
      "namespace Proof\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.badCrate := rfl\n" ++
      "end Proof\n"
  },

  -- Test 2b: Malicious Theory with Trojan macro expanding to `include_str`
  { id := "T2b_malicious_trojan_macro_include_str",
    description := "Malicious Theory with a Trojan macro expanding into `include_str \"/etc/hostname\"` (rejected by Check 2 before elaboration)",
    expectPass := false,
    expectedCheckTag := "post-expansion-audit",
    targetCrateConst := `Mir.goodCrate,
    theorySource :=
      "prelude\n" ++
      "namespace Theory\n" ++
      "syntax \"exfiltrate_host\" : term\n" ++
      "macro_rules\n" ++
      "  | `(exfiltrate_host) => `(include_str \"/etc/hostname\")\n" ++
      "end Theory\n",
    proofSource :=
      "prelude\n" ++
      "open Theory\n" ++
      "namespace Proof\n" ++
      "def stolen : String := exfiltrate_host\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.goodCrate := rfl\n" ++
      "end Proof\n"
  },

  -- Test 3a: Malicious Theory with a macro calling `dbgTrace` inside `MacroM`
  { id := "T3a_malicious_macro_dbgTrace",
    description := "Malicious Theory with a macro calling `dbgTrace` in MacroM (rejected by Check 1 Macro-Definition Purity before macro invocation)",
    expectPass := false,
    expectedCheckTag := "macro-purity",
    targetCrateConst := `Mir.goodCrate,
    theorySource :=
      "prelude\n" ++
      "namespace Theory\n" ++
      "syntax \"noisy_rfl\" : tactic\n" ++
      "macro_rules\n" ++
      "  | `(tactic| noisy_rfl) => dbgTrace \"PWNED_VIA_MACROM\" fun () => `(tactic| rfl)\n" ++
      "end Theory\n",
    proofSource :=
      "prelude\n" ++
      "open Theory\n" ++
      "namespace Proof\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.goodCrate := by noisy_rfl\n" ++
      "end Proof\n"
  },

  -- Test 3b: Malicious Theory with a macro calling `unsafeIO` / `@[implemented_by]`
  { id := "T3b_malicious_macro_implemented_by_unsafeIO",
    description := "Malicious Theory attempting to define an `@[implemented_by]` / `unsafeIO` helper for a macro (rejected at syntax & Check 1 Macro-Definition Purity)",
    expectPass := false,
    expectedCheckTag := "policy:",
    targetCrateConst := `Mir.goodCrate,
    theorySource :=
      "prelude\n" ++
      "namespace Theory\n" ++
      "unsafe def evilWrite (_ : Unit) : Bool :=\n" ++
      "  match unsafeIO (IO.FS.writeFile \"/tmp/pwned_macro\" \"pwn\") with\n" ++
      "  | Except.ok _ => true\n" ++
      "  | Except.error _ => false\n" ++
      "@[implemented_by evilWrite]\n" ++
      "def pureLooking (_ : Unit) : Bool := true\n" ++
      "syntax \"imp_rfl\" : tactic\n" ++
      "macro_rules\n" ++
      "  | `(tactic| imp_rfl) => if pureLooking () then `(tactic| rfl) else `(tactic| rfl)\n" ++
      "end Theory\n",
    proofSource :=
      "prelude\n" ++
      "namespace Proof\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.goodCrate := rfl\n" ++
      "end Proof\n"
  },

  -- Test 4a: Malicious Theory spoofing `notation "Trusted.CrateTheorem"`
  { id := "T4a_malicious_spoof_notation_CrateTheorem",
    description := "Malicious Theory spoofing `notation (priority := 1000000) \"Trusted.CrateTheorem\" c => c = c` on buggy crate (rejected by Check 3b Kernel Statement-Identity)",
    expectPass := false,
    expectedCheckTag := "statement-identity",
    targetCrateConst := `Mir.badCrate,
    theorySource :=
      "prelude\n" ++
      "namespace Theory\n" ++
      "notation (priority := 1000000) \"Trusted.CrateTheorem\" c:arg => c = c\n" ++
      "end Theory\n",
    proofSource :=
      "prelude\n" ++
      "open Theory\n" ++
      "namespace Proof\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.badCrate := rfl\n" ++
      "end Proof\n"
  },

  -- Test 4b: Malicious Theory spoofing `namespace Proof.Trusted def CrateTheorem`
  { id := "T4b_malicious_spoof_namespace_Proof_Trusted",
    description := "Malicious Theory declaring `Proof.Trusted.CrateTheorem` to shadow `Trusted.CrateTheorem` inside `namespace Proof` (rejected by Check 3a Namespace-Component Check)",
    expectPass := false,
    expectedCheckTag := "namespace-hygiene",
    targetCrateConst := `Mir.badCrate,
    theorySource :=
      "prelude\n" ++
      "abbrev CrateAlias := Trusted.Crate\n" ++
      "namespace Proof.Trusted\n" ++
      "def CrateTheorem (_ : CrateAlias) : Prop := True\n" ++
      "end Proof.Trusted\n",
    proofSource :=
      "prelude\n" ++
      "namespace Proof\n" ++
      "theorem verify_crate : Trusted.CrateTheorem Mir.badCrate := True.intro\n" ++
      "end Proof\n"
  }
]

end PureMacroAudit

unsafe def main : IO UInt32 := do
  let sysroot := ((← IO.appPath).parent >>= System.FilePath.parent).getD
    ((← Lean.findSysroot))
  initSearchPath sysroot
  enableInitializersExecution

  -- 1. Build the base environment containing Init + Trusted + Mir
  let inputCtx := Parser.mkInputContext PureMacroAudit.trustedSetupSource "<TrustedSetup>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (baseFoundationEnv, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 0)
  let cmdState0 := Elab.Command.mkState baseFoundationEnv messages {}
  let ioState ← Elab.IO.processCommands inputCtx parserState cmdState0
  let trustedEnv := ioState.commandState.env
  let trustedConsts : NameSet :=
    trustedEnv.constants.foldStage2 (fun acc n _ => acc.insert n) {}

  -- Also test Check 1 directly on an environment where `@[implemented_by]` / `unsafeIO` was added
  let mut rows : Array Json := #[]
  let mut allPassedAsExpected := true

  for tc in PureMacroAudit.testSuite do
    let res : Except String (String × Array String × Array String) ← do
      match ← PureMacroAudit.elaborateAndAuditModule trustedEnv trustedConsts `Theory (allowMacroDefs := true) tc.theorySource with
      | .error err => pure (.error s!"[Theory] {err}")
      | .ok (theoryEnv, checkedMacros, theoryExpansions) =>
        match ← PureMacroAudit.elaborateAndAuditModule theoryEnv trustedConsts `Proof (allowMacroDefs := false) tc.proofSource with
        | .error err => pure (.error s!"[Proof] {err}")
        | .ok (proofEnv, _, proofExpansions) =>
          match ← PureMacroAudit.verifyKernelAndStatementIdentity
              baseFoundationEnv proofEnv trustedConsts `Proof.verify_crate tc.targetCrateConst with
          | .error err => pure (.error s!"[KernelAudit] {err}")
          | .ok summary =>
            pure (.ok (summary, checkedMacros, theoryExpansions ++ proofExpansions))

    match res with
    | .ok (summary, macros, expansions) =>
      let okMatch := tc.expectPass == true
      if !okMatch then allPassedAsExpected := false
      rows := rows.push <| Json.mkObj [
        ("id", toJson tc.id),
        ("description", toJson tc.description),
        ("expectPass", toJson tc.expectPass),
        ("actualResult", toJson "PASS"),
        ("testAssertionOk", toJson okMatch),
        ("checkedMacros", toJson macros),
        ("macroExpansionsAudited", toJson expansions),
        ("detail", toJson summary)
      ]
    | .error errMsg =>
      let okMatch := (tc.expectPass == false) && PureMacroAudit.hasSubstr errMsg tc.expectedCheckTag
      if !okMatch then allPassedAsExpected := false
      rows := rows.push <| Json.mkObj [
        ("id", toJson tc.id),
        ("description", toJson tc.description),
        ("expectPass", toJson tc.expectPass),
        ("actualResult", toJson "REJECTED"),
        ("testAssertionOk", toJson okMatch),
        ("expectedCheckTag", toJson tc.expectedCheckTag),
        ("detail", toJson errMsg)
      ]

  -- Direct unit test of Check 1 (`checkMacroDefinitionPurity`) when `@[implemented_by]` + `unsafeIO`
  -- is elaborated into `env` and inspected by `checkMacroDefinitionPurity`
  let implBySource :=
    "prelude\n" ++
    "namespace Theory\n" ++
    "unsafe def evilWrite (_ : Unit) : Bool :=\n" ++
    "  match unsafeIO (IO.FS.writeFile \"/tmp/pwned_macro\" \"pwn\") with\n" ++
    "  | Except.ok _ => true\n" ++
    "  | Except.error _ => false\n" ++
    "@[implemented_by evilWrite]\n" ++
    "def pureLooking (_ : Unit) : Bool := true\n" ++
    "syntax \"imp_rfl\" : tactic\n" ++
    "macro_rules\n" ++
    "  | `(tactic| imp_rfl) => if pureLooking () then `(tactic| rfl) else `(tactic| rfl)\n" ++
    "end Theory\n"
  let implInputCtx := Parser.mkInputContext implBySource "<ImplByDirectTest>"
  let (_, implParserState, implMsgs) ← Parser.parseHeader implInputCtx
  let implCmdState0 := Elab.Command.mkState trustedEnv implMsgs {}
  let implIoState ← Elab.IO.processCommands implInputCtx implParserState implCmdState0
  match PureMacroAudit.checkMacroDefinitionPurity implIoState.commandState.env trustedConsts with
  | .error errMsg =>
    let okMatch := PureMacroAudit.hasSubstr errMsg "macro-purity"
    if !okMatch then allPassedAsExpected := false
    rows := rows.push <| Json.mkObj [
      ("id", toJson "T3c_direct_check1_implemented_by_unsafeIO"),
      ("description", toJson "Direct test of Check 1 (`checkMacroDefinitionPurity`) on environment with `@[implemented_by]` + `unsafeIO` macro helper"),
      ("expectPass", toJson false),
      ("actualResult", toJson "REJECTED"),
      ("testAssertionOk", toJson okMatch),
      ("expectedCheckTag", toJson "macro-purity"),
      ("detail", toJson errMsg)
    ]
  | .ok _ =>
    allPassedAsExpected := false

  let outJson := Json.mkObj [
    ("leanVersion", toJson Lean.versionString),
    ("allAssertionsPassed", toJson allPassedAsExpected),
    ("results", Json.arr rows)
  ]
  IO.println outJson.pretty
  return if allPassedAsExpected then 0 else 1
