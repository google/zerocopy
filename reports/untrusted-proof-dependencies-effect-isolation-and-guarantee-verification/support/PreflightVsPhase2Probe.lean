-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Init.Omega
import Init.Grind

open Lean

namespace Track5PreflightAudit

-- Exact copy of TrustedBoundary.lean (joshlf/anneal@60ebdec0a8ef9e91d31863e3d8e8a7f4762b3db7)
-- Phase 1 syntax allowlists and validators.

def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.prelude, ``Parser.Module.import]

def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

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

def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
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
    unless isValidSourceIdent val do
      throw s!"policy:invalid identifier {val}"
  | .node _ k args =>
    unless k == nullKind || allowedKinds.contains k do
      throw s!"policy:unsupported syntax kind {k}"
    inspectNodeKind k args
    for child in args do
      inspectSyntax allowedKinds child

def checkCommandString (parserEnv : Environment) (snippet : String) : Except String SyntaxNodeKind := do
  let ctx := Parser.mkInputContext snippet "<probe>"
  let pmctx : Parser.ParserModuleContext := { env := parserEnv, options := {} }
  let s0 : Parser.ModuleParserState := {}
  let msgs0 : MessageLog := {}
  let (stx, s1, msgs1) := Parser.parseCommand ctx pmctx s0 msgs0
  if msgs1.hasErrors || s1.recovering then
    throw s!"parser error: {msgs1.toList.map (·.data) |>.length} errors"
  let topKind := stx.getKind
  unless allowedCommandKinds.contains topKind do
    throw s!"policy:unsupported command {topKind}"
  inspectSyntax allowedTheorySyntaxKinds stx
  return topKind

structure ProbeCase where
  category : String
  feature  : String
  snippet  : String

def testCases : Array ProbeCase := #[
  -- 1. Metaprogramming & Notation Commands
  { category := "Metaprogramming/Notation", feature := "macro",
    snippet := "macro \"my_rfl\" : tactic => `(tactic| rfl)" },
  { category := "Metaprogramming/Notation", feature := "macro_rules",
    snippet := "macro_rules | `(tactic| rfl) => `(tactic| rfl)" },
  { category := "Metaprogramming/Notation", feature := "syntax",
    snippet := "syntax \"my_tac\" : tactic" },
  { category := "Metaprogramming/Notation", feature := "elab",
    snippet := "elab \"my_elab\" : tactic => pure ()" },
  { category := "Metaprogramming/Notation", feature := "elab_rules",
    snippet := "elab_rules : tactic | `(tactic| rfl) => pure ()" },
  { category := "Metaprogramming/Notation", feature := "notation",
    snippet := "notation \"Nat0\" => Nat" },
  { category := "Metaprogramming/Notation", feature := "infixl",
    snippet := "infixl:65 \" +++ \" => Nat.add" },
  { category := "Metaprogramming/Notation", feature := "prefix",
    snippet := "prefix:100 \"!!\" => Bool.not" },

  -- 2. Options & Section/Command Wrappers
  { category := "Options/Commands", feature := "set_option (command)",
    snippet := "set_option maxHeartbeats 400000" },
  { category := "Options/Commands", feature := "set_option ... in (command)",
    snippet := "set_option maxHeartbeats 400000 in theorem t : True := True.intro" },
  { category := "Options/Commands", feature := "set_option ... in (term)",
    snippet := "def f : Nat := set_option pp.all true in 0" },
  { category := "Options/Commands", feature := "noncomputable section",
    snippet := "noncomputable section" },
  { category := "Options/Commands", feature := "example",
    snippet := "example : 1 = 1 := rfl" },
  { category := "Options/Commands", feature := "open scoped",
    snippet := "open scoped Classical" },
  { category := "Options/Commands", feature := "open ... (only)",
    snippet := "open Nat (add mul)" },
  { category := "Options/Commands", feature := "open ... hiding",
    snippet := "open Nat hiding add" },
  { category := "Options/Commands", feature := "open ... renaming",
    snippet := "open Nat renaming add -> plus" },

  -- 3. Deriving & Termination / Recursion
  { category := "Deriving/Recursion", feature := "deriving on inductive",
    snippet := "inductive Color where | r | g deriving DecidableEq, Repr" },
  { category := "Deriving/Recursion", feature := "deriving instance (standalone)",
    snippet := "deriving instance Repr for Nat" },
  { category := "Deriving/Recursion", feature := "termination_by",
    snippet := "def countDown (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => countDown k termination_by n" },
  { category := "Deriving/Recursion", feature := "decreasing_by",
    snippet := "def countDown (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => countDown k termination_by n decreasing_by simp_wf" },
  { category := "Deriving/Recursion", feature := "where helper on def",
    snippet := "def f (x : Nat) : Nat := g x where g (y : Nat) : Nat := y" },
  { category := "Deriving/Recursion", feature := "let rec in term",
    snippet := "def f (x : Nat) : Nat := let rec loop (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => loop k; loop x" },

  -- 4. Attributes & Scopes
  { category := "Attributes/Idents", feature := "local attribute",
    snippet := "attribute [local simp] Nat.add_zero" },
  { category := "Attributes/Idents", feature := "scoped attribute",
    snippet := "attribute [scoped simp] Nat.add_zero" },
  { category := "Attributes/Idents", feature := "@[simp ←] / @[simp high]",
    snippet := "@[simp high] theorem t : 0 = 0 := rfl" },
  { category := "Attributes/Idents", feature := "@[ext] attribute",
    snippet := "@[ext] structure Point where x : Nat" },
  { category := "Attributes/Idents", feature := "@[inline] attribute",
    snippet := "@[inline] def idNat (x : Nat) : Nat := x" },
  { category := "Attributes/Idents", feature := "_root_ identifier prefix",
    snippet := "def f (x : _root_.Nat) : _root_.Nat := x" },

  -- 5. Proof Automation & Standard Tactics
  { category := "Tactics", feature := "omega",
    snippet := "theorem t (x : Nat) : x + 1 > x := by omega" },
  { category := "Tactics", feature := "grind",
    snippet := "theorem t (x : Nat) : x = x := by grind" },
  { category := "Tactics", feature := "simp config (+arith / (config := ...))",
    snippet := "theorem t (x : Nat) : x + 0 = x := by simp +arith" },
  { category := "Tactics", feature := "simp_all",
    snippet := "theorem t (p : Prop) (h : p) : p := by simp_all" },
  { category := "Tactics", feature := "simp only (control check)",
    snippet := "theorem t (x : Nat) : x + 0 = x := by simp only [Nat.add_zero]" },
  { category := "Tactics", feature := "ext",
    snippet := "theorem t (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by ext x; exact h x" },
  { category := "Tactics", feature := "rcases",
    snippet := "theorem t (h : True ∧ True) : True := by rcases h with ⟨h1, _⟩; exact h1" },
  { category := "Tactics", feature := "obtain",
    snippet := "theorem t (h : ∃ x : Nat, x = 0) : True := by obtain ⟨x, hx⟩ := h; exact True.intro" },
  { category := "Tactics", feature := "congr",
    snippet := "theorem t (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by congr" },
  { category := "Tactics", feature := "split",
    snippet := "theorem t (b : Bool) : (if b then 1 else 1) = 1 := by split <;> rfl" },
  { category := "Tactics", feature := "rename_i",
    snippet := "theorem t : Nat → True := by intro _; rename_i x; exact True.intro" },
  { category := "Tactics", feature := "by_cases",
    snippet := "theorem t (p : Prop) : True := by by_cases h : p <;> exact True.intro" },
  { category := "Tactics", feature := "contradiction",
    snippet := "theorem t (h : False) : 1 = 2 := by contradiction" },
  { category := "Tactics", feature := "trivial / assumption",
    snippet := "theorem t (h : True) : True := by assumption" },
  { category := "Tactics", feature := "decide +kernel",
    snippet := "theorem t : 1 + 1 = 2 := by decide +kernel" },
  { category := "Tactics", feature := "calc (tactic/term)",
    snippet := "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := calc a = b := h1\n  _ = c := h2" },
  { category := "Tactics", feature := "conv",
    snippet := "theorem t (a : Nat) : a + 0 = a := by conv => lhs; rw [Nat.add_zero]" },
  { category := "Tactics", feature := "focused dot (· rfl)",
    snippet := "theorem t : True ∧ True := by constructor\n  · exact True.intro\n  · exact True.intro" },
  { category := "Tactics", feature := "all_goals / try",
    snippet := "theorem t : True ∧ True := by constructor; all_goals try exact True.intro" },
  { category := "Tactics", feature := "clear / generalize / specialize",
    snippet := "theorem t (h : True) : True := by clear h; exact True.intro" },

  -- 6. Pure Term Sugar (do notation, if let, string interpolation, Additional notations)
  { category := "Term Sugar", feature := "do notation (Id.run do)",
    snippet := "def sumTo (n : Nat) : Nat := Id.run do let mut s := 0; return s" },
  { category := "Term Sugar", feature := "if let pattern",
    snippet := "def getOrZero (o : Option Nat) : Nat := if let some x := o then x else 0" },
  { category := "Term Sugar", feature := "string interpolation s!\"...\"",
    snippet := "def msg (n : Nat) : String := s!\"val={n}\"" },
  { category := "Term Sugar", feature := "⟨...⟩ vs [a, b, c] list literal",
    snippet := "def xs : List Nat := [1, 2, 3]" }
]

end Track5PreflightAudit

unsafe def main : IO UInt32 := do
  let sysroot := ((← IO.appPath).parent >>= System.FilePath.parent).getD
    ((← Lean.findSysroot))
  initSearchPath sysroot
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }, { module := `Init.Omega }, { module := `Init.Grind }] {}
    (trustLevel := 0) (loadExts := true)
  let mut rows : Array Json := #[]
  for tc in Track5PreflightAudit.testCases do
    match Track5PreflightAudit.checkCommandString env tc.snippet with
    | .ok kind =>
      rows := rows.push <| Json.mkObj [
        ("category", toJson tc.category),
        ("feature", toJson tc.feature),
        ("status", toJson "ALLOWED"),
        ("reason", toJson s!"admitted ({kind})")
      ]
    | .error err =>
      rows := rows.push <| Json.mkObj [
        ("category", toJson tc.category),
        ("feature", toJson tc.feature),
        ("status", toJson "BLOCKED"),
        ("reason", toJson err)
      ]
  IO.println (Json.arr rows).pretty
  return 0
