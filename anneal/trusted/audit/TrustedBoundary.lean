-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean.Elab.Import
import Lean.Parser.Tactic
import Lean.Replay

/-!
# Trusted Boundary and Kernel Environment Inspector (`TrustedBoundary.lean`)

Pinned to Lean 4.34.1, commit
`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`. `trusted/audit`
invokes this file in three phases over JSON IPC (`run` and `main`):

- **`"preflight"` (purely syntactic admission before elaboration):**
  Lean elaboration is Turing-complete and effectful: commands such as `#eval`
  and tactics/terms such as `run_tac`, `by_elab`, `native_decide`, and
  `include_str` can execute arbitrary code or read host files during
  compilation, while attributes such as `@[implemented_by]` and `@[extern]`
  alter code generation without appearing in kernel proof terms. `"preflight"`
  therefore parses every non-foundation `.lean` file using `Parser.parseHeader`
  and `Parser.parseCommand`—which never invoke the elaborator—against the locked
  foundation parser environment only. Rather than maintaining an open-ended
  block-list of dangerous Lean features, `"preflight"` enforces a closed,
  role-aware `SyntaxNodeKind` allow-list (`allowedTrustedSyntaxKinds` for
  tactic-free `trusted/lean/` specifications and `allowedTheorySyntaxKinds` for
  `theory/` proofs) together with closed attribute and identifier grammars, and
  extracts each `Trusted` module's `-- anneal-trust-tier: <tier>` directive
  before `lean` compiles any file.
- **`"audit"` (kernel `.olean` inspection and replay):**
  Loads the compiled `.olean` files with `trustLevel := 0`, `plugins := #[]`,
  and `loadExts := false` (so no `[init]` initializers or persistent environment
  extensions from audited modules are deserialized or executed). It verifies
  module-level trust-tier separation, `Trusted` namespace hygiene, the
  foundation axiom allowlist, Pass 1 `Anneal.MirWp` non-backsliding theorem and
  canary checks, and a full kernel replay of every non-foundation constant
  against the foundation environment (`base.toKernelEnv.replay`).
- **`"correspondence-audit"` (`lean-miri` closure audit):**
  Loads the 160-module `Miri.Interpreter.ExecutionMachine` closure at
  `trustLevel := 0` with `plugins := #[]` and `loadExts := false` (optional
  `corrTrusted`/`corrTheory` module lists are currently passed empty by
  `anneal-audit`, as `trusted/correspondence/` and `correspondence/` are not
  yet scanned at this commit). It classifies every loaded module into a closed
  5-role partition (`CorrModuleRole`), validates inventory integrity across
  `.vendorMiri`, `.trusted`, and `.theory` declarations, rejects any
  `.vendorMiri` or `.sysrootFoundation` declaration in the reserved `Trusted`
  or `Anneal` namespaces, rejects any `axiom`, `unsafe`, quotient primitive,
  `sorryAx`, or compiler-reflection primitive (`Lean.ofReduceBool`,
  `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool`,
  `Lean.reduceNat`) in any `.vendorMiri` module, replays every non-`isPartial`
  `.vendorMiri` declaration from scratch through the standalone Lean kernel
  onto the authenticated `.foundation`/`.sysrootFoundation` base on every run
  (cold build and cache hit alike), and checks that every constant transitively
  reachable from the 21 `Miri.Interpreter.ExecutionMachine` cone roots is free
  of `unsafe`, `partial`, `.vendorMiri` `opaque` declarations, and unapproved
  axioms.

## Module roles and trust tiers

Every admitted module in the environment is classified into a single
`ModuleRole`:

| `ModuleRole` | Directory / Source | Meaning |
| :--- | :--- | :--- |
| `.foundation` | Toolchain `Init.*` (`foundation-lock.json`) | Pinned Lean 4 standard prelude and core types |
| `.trusted .vetted` | `trusted/lean/` (`-- anneal-trust-tier: vetted`) | Human-audited TCB definitions |
| `.trusted (.candidate f)` | `trusted/lean/` (`-- anneal-trust-tier: candidate:<f>`) | Alpha TCB definitions gated behind opt-in feature `f` |
| `.theory` | `theory/` (`Anneal.*`) | Untrusted proof automation checked by the kernel |

Every kernel constant `c` has a unique defining module (`origin env c`, read
directly from `env.getModuleIdxFor? c` in the `.olean`), and therefore a unique
`ModuleRole`. This includes compiler-generated constants such as constructors,
recursors (`rec`, `casesOn`, `recOn`, `noConfusion`, `below`, `brecOn`),
structure projections, pattern matchers (`match_1`), equation lemmas (`eq_1`),
and `where`/`private` helpers, all of which are compiled into the same `.olean`
and inherit their defining module's `ModuleRole` without surface-syntax name
prediction or suffix heuristics.

On every kernel dependency edge `c → dep` (`declarationEdges`),
`checkTierReferences` enforces two rules:

- **Origin rule:** a `.trusted _` constant may only reference `.foundation` or
  `.trusted _` constants (never `.theory`).
- **Vetted rule:** a `.trusted .vetted` constant may only reference
  `.foundation` or `.trusted .vetted` constants (never
  `.trusted (.candidate _)`).
-/

open Lean

namespace TrustedBoundary

/-! ## Domain types: `TrustTier` and `ModuleRole` -/

/-- Closed set of subsystem feature identifiers allowed in
`-- anneal-trust-tier: candidate:<feature>`. -/
def validCandidateFeatures : List Name :=
  [`refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

/-- Module-level trust tier declared by a `Trusted` module via its
`-- anneal-trust-tier:` directive. -/
inductive TrustTier where
  | vetted
  | candidate (feature : Name)
  deriving BEq, DecidableEq

namespace TrustTier

/-- Render a `TrustTier` in its canonical wire format (`"vetted"` or
`"candidate:<feature>"`). -/
def render : TrustTier → String
  | .vetted => "vetted"
  | .candidate feat => s!"candidate:{feat}"

/-- Parse `"vetted"` or `"candidate:<feature>"` when `<feature>` belongs to
`validCandidateFeatures`. -/
def parse? (raw : String) : Option TrustTier :=
  if raw == "vetted" then
    some .vetted
  else if let some rest := raw.dropPrefix? "candidate:" then
    let feat := rest.toString.toName
    if validCandidateFeatures.contains feat then
      some (.candidate feat)
    else
      none
  else
    none

end TrustTier

/-- Role of a repository `.lean` source module inspected during `"preflight"`.
Every `Trusted` module carries its required `TrustTier`, while `theory/`
modules carry none; illegal combinations (a `Trusted` module without a tier
or a `theory/` module with one) are unrepresentable. -/
inductive SourceRole where
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

/-- Partition of every admitted module in the kernel environment into its
repository role. Representing these three roles as mutually exclusive
constructors of one sum type makes overlapping or missing module classifications
unrepresentable. -/
inductive ModuleRole where
  | foundation
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

/-! ## JSON IPC and environment-loading helpers -/

/-- Throw a policy-rejection error prefixed with `"policy:"` (exit code 1). -/
def fail (message : String) : IO α :=
  throw <| IO.userError s!"policy:{message}"

/-- Extract and deserialize required field `key` from JSON object `j`. -/
def field [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

/-- Extract an array of dot-separated Lean `Name`s from JSON field `key`. -/
def names (j : Json) (key : String) : IO (Array Name) := do
  return (← field (α := Array String) j key).map String.toName

/-- Build the explicit module-to-artifact map (`NameMap ImportArtifacts`) from
`"artifacts"`, rejecting duplicate module entries. -/
def artifacts (j : Json) : IO (NameMap ImportArtifacts) := do
  let entries ← field (α := Array (String × Array (Array String))) j "artifacts"
  entries.foldlM (init := {}) fun acc (n, parts) => do
    let modName := n.toName
    if (acc.find? modName).isSome then
      fail s!"duplicate artifact module {n}"
    return acc.insert modName
      (.ofArrays (parts.map (·.map System.FilePath.mk)))

/-- Serialize the compiled module header import DAG of `env` as JSON. -/
def graph (env : Environment) : Json :=
  Json.mkObj <|
    (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)

/-- Import `roots` from the explicit artifact map in `j` at `trustLevel := 0`
with `level := .private`.
- In `"preflight"`, `extensions := true` loads the locked `Init.*` parser
  extensions so `Parser.parseCommand` can parse standard Lean syntax.
- In `"audit"`, `extensions := false` disables loading persistent environment
  extensions or `[init]` initializers from compiled `.olean` files. -/
def importEnv (j : Json) (roots : Array Name)
    (extensions := false) : IO Environment := do
  let arts ← artifacts j
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

/-- Verify that the import DAG recorded in the `.olean` headers of `env` is
identical to the admitted `"graph"` from `"preflight"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do
    fail "compiled module/import DAG differs from admitted DAG"

/-! ## Phase 1: source preflight -/

/-- Closed allowlist of module header syntax kinds permitted in source files.
Module-system and import modifiers (`moduleTk`, `public`, `meta`, `all`) are
excluded so any header modifier is rejected by `SyntaxNodeKind` alone. -/
def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.prelude, ``Parser.Module.import]

/-- Closed allowlist of top-level command syntax kinds permitted in source
files. Commands such as `#eval`, `#check`, `macro`, `syntax`, `elab`,
`notation`, `infix`, `initialize`, `set_option`, and `axiom` are excluded. -/
def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

/-- Closed allowlist of declaration syntax kinds permitted inside
`Parser.Command.declaration`. `axiom`, `example`, and `coinductive` are
excluded. -/
def allowedDeclarationKinds : List Name := [
  ``Parser.Command.abbrev, ``Parser.Command.definition,
  ``Parser.Command.theorem, ``Parser.Command.opaque,
  ``Parser.Command.instance, ``Parser.Command.inductive,
  ``Parser.Command.classInductive, ``Parser.Command.structure]

/-- Closed allowlist of command and declaration structural sub-node kinds.
Excludes `unsafe`, `partial`, `meta`, `nonrec`, `openScoped`, `derivingClass`,
`computedFields`, and termination/fixpoint clauses (`terminationBy`,
`decreasingBy`, `partialFixpoint`, `coinductiveFixpoint`,
`inductiveFixpoint`). -/
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

/-- Closed allowlist of pure term, binder, pattern-matching, structure-instance,
literal, and attribute-application syntax kinds permitted in both `Trusted` and
`theory/` modules. Excludes `byTactic` (permitted only in `theory/`), `sorry`,
`unsafe`, `byElab`, `includeStr`, `set_option`, `scoped`/`local` attribute
kinds, `do` notation, string interpolation, quotations, and reflection macros
(`decl_name%`, `with_decl_name%`, `private_decl%`). -/
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

/-- Closed allowlist of standard `Init.*` notation syntax kinds expanded by the
locked foundation parser. -/
def allowedNotationSyntaxKinds : List Name := [
  `term!_, `termIfThenElse, `termDepIfThenElse, `«term[_]»,
  `«term_&&_», `«term_||_», `«term_+_», `«term_-_», `«term_*_»,
  `«term_::_», `«term_++_», `«term_<_», `«term_≤_», `«term_>_»,
  `«term_≥_», `«term_==_», `«term_!=_», `«term_=_», `«term_≠_»,
  `«term__[_]_?», `«term_×_», `«term_↔_», `«term_∈_», `«term_∧_»,
  `«term_∨_», `«term¬_», `«term∃_,_», `«term‹_›», `Lean.cdot, `Lean.cdotTk]

/-- Closed allowlist of tactic syntax kinds permitted in `SourceRole.theory`
(`theory/`) modules only. `Trusted` modules are tactic-free (`byTactic` is
excluded from `allowedTrustedSyntaxKinds`). Even in `theory/`, effectful or
trust-bypassing tactics (`native_decide`, `decide!`, `bv_decide`, `rfl'`,
`sorry`, `run_tac`, `sleep`, `dbg_trace`, `unhygienic`, `grind`) and tactic
configuration items (`+native`, `+kernel`, etc., which parse as
`Parser.Tactic.configItem`) are excluded. -/
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

/-- Syntax node kinds permitted in `SourceRole.trusted` (`trusted/lean/`)
modules: pure declarations, types, and term-mode proofs only. -/
def allowedTrustedSyntaxKinds : NameSet :=
  .ofList <|
    allowedHeaderKinds ++
    allowedCommandKinds ++
    allowedDeclarationKinds ++
    allowedCommandSyntaxKinds ++
    allowedTermSyntaxKinds ++
    allowedNotationSyntaxKinds

/-- Syntax node kinds permitted in `SourceRole.theory` (`theory/`) modules:
`allowedTrustedSyntaxKinds` extended with `allowedTheoryTacticKinds`. -/
def allowedTheorySyntaxKinds : NameSet :=
  allowedTrustedSyntaxKinds ++ .ofList allowedTheoryTacticKinds

namespace SourceRole

/-- The closed `SyntaxNodeKind` allowlist for a source module's role. -/
def allowedSyntaxKinds : SourceRole → NameSet
  | .trusted _ => allowedTrustedSyntaxKinds
  | .theory => allowedTheorySyntaxKinds

/-- Render the optional `"trustTier"` JSON wire value for a source module. -/
def renderTier? : SourceRole → Option String
  | .trusted tier => some tier.render
  | .theory => none

end SourceRole

/-- Closed allowlist of attributes permitted on declarations. Compiler-override
and metaprogramming attributes (`extern`, `implemented_by`, `csimp`, `init`,
`macro`, `elab_as_elim`, etc.) are excluded. -/
def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

/-- Return `true` if `id` is a valid user-written identifier with non-empty
string components, no macro scopes, and no `_root_` namespace escape. -/
def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

/-- Determine the `SourceRole` of `moduleName` from its name and `--
anneal-trust-tier: <tier>` directive in `text`. Every `Trusted` module must
declare a single valid `TrustTier`, and non-`Trusted` (`theory/`) modules may
not declare one. -/
def extractSourceRole (moduleName : Name) (text : String) : IO SourceRole := do
  let isTrustedModule :=
    moduleName == `Trusted || moduleName.getRoot == `Trusted
  let directives := (text.splitOn "\n").filterMap fun rawLine =>
    (rawLine.trimAscii.toString.dropPrefix? "-- anneal-trust-tier:").map
      (·.trimAscii.toString)
  match isTrustedModule, directives with
  | false, [] => pure .theory
  | false, _ :: _ =>
    fail s!"trust tier directive is only allowed in Trusted modules ({moduleName})"
  | true, [] =>
    fail s!"missing `-- anneal-trust-tier: vetted` or `-- anneal-trust-tier: candidate:<feature>` in {moduleName}"
  | true, [rawTier] =>
    match TrustTier.parse? rawTier with
    | some tier => pure (.trusted tier)
    | none => fail s!"invalid trust tier {rawTier} in {moduleName}"
  | true, _ :: _ :: _ =>
    fail s!"multiple trust tier directives in {moduleName}"

/-- Return `true` if `k` is a command permitted inside a `mutual` block or on
the RHS of an `in` command (any command in `allowedCommandKinds` except scope
and `mutual` commands). -/
def isAllowedNestedCommand (k : SyntaxNodeKind) : Bool :=
  allowedCommandKinds.contains k &&
    ![``Parser.Command.namespace, ``Parser.Command.section,
      ``Parser.Command.end, ``Parser.Command.mutual].contains k

/-- Enforce per-node structural invariants on a `Syntax.node` whose kind `k` has
already been admitted by `allowedKinds`:
- `Parser.Module.header`: an explicit `prelude` child (`args[1]`) is mandatory
  (omitting `prelude` produces an empty `null` node rather than a distinct
  `SyntaxNodeKind`).
- `Parser.Command.sectionHeader`: `section` and `namespace` headers may not
  carry modifiers (`noncomputable section`, `@[attr] section`, etc.).
- `Parser.Command.declaration`: the inner declaration body (`args[1]`) must be
  one of `allowedDeclarationKinds`.
- `Parser.Command.mutual`: every element inside `mutual ... end` (`args[1]`)
  must satisfy `isAllowedNestedCommand`.
- `Parser.Command.in`: only `open` and `variable` may appear on the LHS
  (`args[0]`), and the RHS (`args[2]`) must satisfy `isAllowedNestedCommand`.
- `Parser.Attr.simple`, `Parser.Attr.instance`, `Parser.Attr.simp`, and
  `Parser.Command.eraseAttr`: attribute names must belong to
  `allowedAttributeNames` and carry no arguments or priority overrides. -/
def inspectNodeKind (k : SyntaxNodeKind) (args : Array Syntax) : IO Unit := do
  if k == ``Parser.Module.header then
    unless !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
      fail "explicit prelude is required"
  else if k == ``Parser.Command.sectionHeader then
    unless args.all (·.getArgs.isEmpty) do
      fail "section/namespace modifiers are unsupported"
  else if k == ``Parser.Command.declaration then
    let declKind := args[1]?.map Syntax.getKind |>.getD .anonymous
    unless allowedDeclarationKinds.contains declKind do
      fail s!"unsupported declaration kind {declKind}"
  else if k == ``Parser.Command.mutual then
    unless args.size == 3 &&
        args[1]!.getArgs.all (isAllowedNestedCommand ·.getKind) do
      fail "unsupported mutual-block shape"
  else if k == ``Parser.Command.in then
    unless args.size == 3 do fail "unsupported command-wrapper shape"
    unless [``Parser.Command.open, ``Parser.Command.variable].contains
        args[0]!.getKind do
      fail "only `open` and `variable` commands are permitted on the LHS of `in`"
    unless isAllowedNestedCommand args[2]!.getKind do
      fail s!"unsupported command inside `in`: {args[2]!.getKind}"
  else if k == ``Parser.Attr.simple then
    let attrName := args[0]?.map Syntax.getId |>.getD .anonymous
    unless allowedAttributeNames.contains attrName do
      fail s!"unsupported attribute {attrName}"
    unless (args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
      fail s!"unsupported arguments on attribute {attrName}"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    unless (args.extract 1 args.size).all (·.getArgs.isEmpty) do
      fail s!"unsupported arguments on attribute {k}"
  else if k == ``Parser.Command.eraseAttr then
    let attrName := args[1]?.map Syntax.getId |>.getD .anonymous
    unless allowedAttributeNames.contains attrName do
      fail s!"unsupported attribute removal {attrName}"

/-- Recursively validate syntax tree `s` in a single top-down pass against the
closed `allowedKinds` allowlist during `"preflight"`. Pattern-matching
exhaustively on `Syntax` rejects recovery placeholders (`.missing`), validates
every identifier with `isValidSourceIdent`, and requires every non-`null`
`Syntax.node` kind to belong to `allowedKinds` and satisfy `inspectNodeKind`. -/
partial def inspectSyntax (allowedKinds : NameSet) (s : Syntax) : IO Unit := do
  match s with
  | .missing => fail "unexpected missing syntax node"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do
      fail s!"invalid identifier {val}"
  | .node _ k args =>
    unless k == nullKind || allowedKinds.contains k do
      fail s!"unsupported syntax kind {k}"
    inspectNodeKind k args
    for child in args do
      inspectSyntax allowedKinds child

/-- Parse and validate all commands in `ctx` starting from `initial` and `log`
using the pure foundation `parserEnv` and the role's `allowedKinds`. -/
partial def parseAndInspectCommands (ctx : Parser.InputContext)
    (parserEnv : Environment) (moduleName : Name) (allowedKinds : NameSet)
    (state : Parser.ModuleParserState) (messages : MessageLog) : IO Unit := do
  let previous := state.pos
  let (stx, nextState, nextMessages) :=
    Parser.parseCommand ctx { env := parserEnv, options := {} } state messages
  if nextMessages.hasErrors || nextState.recovering then
    fail s!"command parser error in {moduleName}"
  if stx.isOfKind ``Parser.Command.eoi then
    return ()
  if nextState.pos <= previous then
    throw <| IO.userError "parser made no progress"
  unless allowedCommandKinds.contains stx.getKind do
    fail s!"unsupported command {stx.getKind}"
  inspectSyntax allowedKinds stx
  parseAndInspectCommands ctx parserEnv moduleName allowedKinds nextState
    nextMessages

/-- Parse and validate a single `.lean` source file during `"preflight"`. -/
def inspectSource (parserEnv : Environment) (moduleName : Name)
    (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let role ← extractSourceRole moduleName text
  let allowedKinds := role.allowedSyntaxKinds
  let ctx := Parser.mkInputContext text path.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then
    fail s!"header parser error in {moduleName}"
  inspectSyntax allowedKinds header.raw
  let imports := Elab.HeaderSyntax.imports header
  for imp in imports do
    if imp.importAll || imp.isMeta || !imp.isExported then
      fail "import modifiers are unsupported"
  parseAndInspectCommands ctx parserEnv moduleName allowedKinds initial log
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("trustTier", toJson role.renderTier?)]

/-! ## Phase 2: kernel environment audit -/

/-- Pure DAG traversal collecting every constant referenced inside `pending`.
Uses `seen` to avoid re-traversing shared DAG subterms in kernel `Expr`s. -/
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

/-- Verify that `e` contains no free variables, metavariables, or loose bound
variables, and return the set of all constants referenced inside `e`. -/
def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    fail "open expression in stored declaration"
  return collectExprConsts [e]

/-- The kernel dependency edges of `ci`: every constant in its type and value,
the other members of its mutual block, and its inductive structure
(constructors of an inductive, the inductive of a constructor, and the
constructors and rule right-hand sides of a recursor). -/
def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let typeEdges ← expressionEdges ci.type
  let valEdges ← match ci.value? (allowOpaque := true) with
    | some value => expressionEdges value
    | none => pure {}
  let baseEdges := typeEdges ++ valEdges ++ .ofList ci.all
  match ci with
  | .inductInfo v => return baseEdges ++ .ofList v.ctors
  | .ctorInfo v => return baseEdges.insert v.induct
  | .recInfo v =>
    v.rules.foldlM (init := baseEdges ++ .ofList v.all) fun acc rule => do
      return (acc.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .quotInfo _ =>
    return baseEdges

/-- Human-readable kind tag for a kernel `ConstantInfo`. -/
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Return the defining module name for kernel constant `n` in `env`. -/
def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n
    | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]?
    | fail s!"invalid module index: {n}"
  return mod.module

/-- Return the defining module name and `ModuleRole` for constant `n` in
`env`. -/
def constProvenance (env : Environment)
    (roles : Std.HashMap Name ModuleRole) (n : Name) :
    IO (Name × ModuleRole) := do
  let orig ← origin env n
  let some role := roles.get? orig
    | fail s!"foreign module {orig} for {n}"
  return (orig, role)

/-- Compute the transitive kernel dependency closure of `pending`, verify that
every reachable axiom belongs to `axioms`, and return the sorted reached
axioms and the set of reached constants. -/
partial def closure (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (axioms : Array (String × String))
    (pending : List Name) (visited : NameSet := {})
    (reachedAxioms : NameSet := {}) : IO (Array Name × NameSet) := do
  match pending with
  | [] => return (reachedAxioms.toArray.qsort Name.lt, visited)
  | n :: rest =>
    if visited.contains n then
      closure lookup provenance axioms rest visited reachedAxioms
    else
      let visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      let reachedAxioms ← if ci.isAxiom then do
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        pure (reachedAxioms.insert n)
      else
        pure reachedAxioms
      let deps ← declarationEdges ci
      closure lookup provenance axioms (deps.toList ++ rest) visited
        reachedAxioms

/-- Build the complete map from module name to `ModuleRole`, verifying that
`foundation`, `trusted`, and `theory` are pairwise disjoint and that every
`Trusted` module has a valid `TrustTier`. -/
def buildModuleRoles (j : Json) (foundation trusted theory : Array Name) :
    IO (Std.HashMap Name ModuleRole) := do
  let tierEntries ← field (α := Array (String × String)) j "moduleTiers"
  let tierMap ← tierEntries.foldlM (init := ({} : Std.HashMap Name TrustTier))
    fun acc (mStr, rawTier) => do
      let m := mStr.toName
      if acc.contains m then fail s!"duplicate module tier for {m}"
      unless trusted.contains m do
        fail s!"trust tier declared for non-Trusted module {m}"
      let some tier := TrustTier.parse? rawTier
        | fail s!"invalid trust tier {rawTier} for {m}"
      return acc.insert m tier
  let roles0 := foundation.foldl (init := ({} : Std.HashMap Name ModuleRole))
    fun acc m => acc.insert m .foundation
  let roles1 ← trusted.foldlM (init := roles0) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    let some tier := tierMap.get? m
      | fail s!"missing trust tier for Trusted module {m}"
    return acc.insert m (.trusted tier)
  theory.foldlM (init := roles1) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    return acc.insert m .theory

/-- Enforce per-constant policy invariants on a non-foundation constant `ci`
defined in module `m` with `role`:
- Non-`Trusted` modules cannot declare constants in the `Trusted` root
  namespace (`privateToUserName` strips any `_private.<mod>.0` prefix first so
  `private` declarations inside `namespace Trusted` are also caught).
- Non-`Trusted` modules cannot declare `opaque` constants.
- No non-foundation module may declare `unsafe`, `partial`, `axiom`, or `quot`
  constants, or omit a definition body. -/
def validateLocalConstant (m : Name) (role : ModuleRole)
    (ci : ConstantInfo) : IO Unit := do
  let isTrusted := role matches .trusted _
  if !isTrusted && (privateToUserName ci.name).getRoot == `Trusted then
    fail s!"non-Trusted module {m} cannot declare constant {ci.name} in Trusted namespace"
  if !isTrusted && (ci matches .opaqueInfo _) then
    fail s!"opaque declaration {ci.name} in {m} is not allowed outside Trusted"
  if ci.isUnsafe || ci.isPartial then
    fail (if isTrusted then
      s!"unsafe/partial Trusted declaration {ci.name}"
    else
      s!"unsafe/partial declaration {ci.name} in {m}")
  if ci.isAxiom then
    fail (if isTrusted then
      s!"Trusted axiom {ci.name}"
    else
      s!"strict axiom declaration {ci.name} in {m}")
  if ci matches .quotInfo _ then
    fail s!"unexpected quotient primitive {ci.name} in {m}"
  if ci.hasValue true && (ci.value? true).isNone then
    fail s!"missing stored body {ci.name}"

/-- Verify module allowlists, declaration provenance, `Trusted` namespace
hygiene, and the absence of axioms and `unsafe`/`partial` declarations across
all loaded modules. Return every non-foundation constant and the compiler-only
(IR) names of `Trusted` modules. -/
def verifyAndCollectLocals (env : Environment)
    (roles : Std.HashMap Name ModuleRole) :
    IO (Std.HashMap Name ConstantInfo × NameSet) := do
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for (reqMod, _) in roles do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod}"
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut extraNames : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    let some role := roles.get? m.module
      | fail s!"foreign module {m.module}"
    for ci in data.constants do
      let (orig, origRole) ← constProvenance env roles ci.name
      match role with
      | .foundation =>
        unless origRole == .foundation do
          fail s!"inventory origin mismatch {ci.name}"
      | .trusted _ | .theory =>
        if locals.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      unless stored.type == ci.type && stored.value? true == ci.value? true do
        fail s!"stored declaration differs from inventory {ci.name}"
      if role != .foundation then
        validateLocalConstant m.module role ci
        locals := locals.insert ci.name ci
    for n in data.extraConstNames do
      let (orig, origRole) ← constProvenance env roles n
      match role with
      | .foundation =>
        unless origRole == .foundation do
          fail s!"IR helper provenance mismatch {n}"
      | .trusted _ | .theory =>
        unless orig == m.module do
          fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n do
            fail s!"uninventoried kernel compiler helper {n}"
        else if role matches .trusted _ then
          extraNames := extraNames.insert n
  for (n, _) in env.checked.get.constants do
    let (_, origRole) ← constProvenance env roles n
    if origRole != .foundation && !locals.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, extraNames)

/-- Enforce the origin rule and the vetted rule on every `Trusted` constant:
- **Origin rule:** a `.trusted _` constant may only reference `.foundation` or
  `.trusted _` constants (never `.theory`).
- **Vetted rule:** a `.trusted .vetted` constant may only reference
  `.foundation` or `.trusted .vetted` constants (never
  `.trusted (.candidate _)`). -/
def checkTierReferences (env : Environment)
    (roles : Std.HashMap Name ModuleRole)
    (locals : Std.HashMap Name ConstantInfo) : IO Unit := do
  for (cName, ci) in locals do
    let (_, cRole) ← constProvenance env roles cName
    if let .trusted tier := cRole then
      for dep in ← declarationEdges ci do
        let (depOrigin, depRole) ← constProvenance env roles dep
        match depRole with
        | .foundation => pure ()
        | .trusted depTier =>
          if tier == .vetted && depTier != .vetted then
            fail s!"vetted constant {cName} references {depTier.render} constant {dep}"
        | .theory =>
          fail s!"Trusted constant {cName} references {dep} from non-Trusted module {depOrigin}"

/-- Verify that `claimName` is a `.defnInfo` definition in `expectedClaimMod`
with type `Prop` (`claimCi.type == .sort .zero`) referencing every constant in
`reqConsts`, and that `proofName` is a `.thmInfo` theorem in
`expectedProofMod` whose type is exactly `Expr.const claimName []`. -/
def requireExactClaimProof (env : Environment)
    (locals : Std.HashMap Name ConstantInfo)
    (expectedClaimMod expectedProofMod claimName proofName : Name)
    (reqConsts : List Name := []) : IO Unit := do
  let some claimCi := locals.get? claimName
    | fail s!"missing required claim {claimName}"
  unless claimCi matches .defnInfo _ do
    fail s!"expected {claimName} to be a definition"
  let claimOrig ← origin env claimName
  unless claimOrig == expectedClaimMod do
    fail (s!"expected {claimName} to be defined in " ++
      s!"{expectedClaimMod}, found {claimOrig}")
  unless claimCi.type == .sort .zero do
    fail s!"expected {claimName} to have type Prop"
  let some claimVal := claimCi.value? true
    | fail s!"missing definition body for {claimName}"
  let valConsts ← expressionEdges claimVal
  for req in reqConsts do
    unless valConsts.contains req do
      fail s!"claim {claimName} body must reference {req}"
  let some proofCi := locals.get? proofName
    | fail s!"missing required theorem {proofName}"
  unless proofCi matches .thmInfo _ do
    fail s!"expected {proofName} to be a theorem"
  let proofOrig ← origin env proofName
  unless proofOrig == expectedProofMod do
    fail (s!"expected {proofName} to be defined in " ++
      s!"{expectedProofMod}, found {proofOrig}")
  unless proofCi.type == .const claimName [] do
    fail s!"theorem {proofName} must prove {claimName} directly"

/-- Verify that `proofName` is a `.thmInfo` theorem in `expectedProofMod` whose
type is `Expr.app (Expr.const claimName []) (Expr.const argName [])`, where
`claimName` is a `.defnInfo` definition in `expectedClaimMod` referencing every
constant in `reqConsts`. -/
def requireParamClaimProof (env : Environment)
    (locals : Std.HashMap Name ConstantInfo)
    (expectedClaimMod expectedProofMod claimName argName proofName : Name)
    (reqConsts : List Name) : IO Unit := do
  let some proofCi := locals.get? proofName
    | fail s!"missing required theorem {proofName}"
  unless proofCi matches .thmInfo _ do
    fail s!"expected {proofName} to be a theorem"
  let proofOrig ← origin env proofName
  unless proofOrig == expectedProofMod do
    fail (s!"expected {proofName} to be defined in " ++
      s!"{expectedProofMod}, found {proofOrig}")
  unless proofCi.type == .app (.const claimName []) (.const argName []) do
    fail s!"theorem {proofName} must prove {claimName} {argName} directly"
  let some claimCi := locals.get? claimName
    | fail s!"missing required claim {claimName}"
  unless claimCi matches .defnInfo _ do
    fail s!"expected {claimName} to be a definition"
  let claimOrig ← origin env claimName
  unless claimOrig == expectedClaimMod do
    fail (s!"expected {claimName} to be defined in " ++
      s!"{expectedClaimMod}, found {claimOrig}")
  let some claimVal := claimCi.value? true
    | fail s!"missing definition body for {claimName}"
  let valConsts ← expressionEdges claimVal
  for req in reqConsts do
    unless valConsts.contains req do
      fail s!"claim {claimName} body must reference {req}"

/-- Verify that `Trusted.MirAst` and `Trusted.MirSemantics` are loaded as
`.trusted` modules and `Anneal.MirWp` is loaded as a `.theory` module (whenever
`requireMirWp` is `true` or any MIR/`PureLift` module is loaded), and that the
core weakest-precondition adequacy and fault-characterization theorems and all
15 non-vacuity and parameter-boundary canaries in `Anneal.MirWp` prove the
exact `*Claim` propositions defined in `Trusted.MirSemantics`. -/
def verifyMirWpCoreTheorems (env : Environment)
    (roles : Std.HashMap Name ModuleRole)
    (locals : Std.HashMap Name ConstantInfo)
    (requireMirWp : Bool) : IO Unit := do
  if requireMirWp || roles.contains `Anneal.PureLift ||
      roles.contains `Trusted.MirAst ||
      roles.contains `Trusted.MirSemantics || roles.contains `Anneal.MirWp then
    unless roles.get? `Trusted.MirAst matches some (.trusted _) do
      fail "missing required trusted module Trusted.MirAst"
    unless roles.get? `Trusted.MirSemantics matches some (.trusted _) do
      fail "missing required trusted module Trusted.MirSemantics"
    unless roles.get? `Anneal.MirWp matches some .theory do
      fail "missing required theory module Anneal.MirWp"
    let semMod := `Trusted.MirSemantics
    let wpMod := `Anneal.MirWp
    requireParamClaimProof env locals semMod wpMod
      `Trusted.MirSemantics.WpSoundnessClaim
      `Anneal.MirWp.wpProg
      `Anneal.MirWp.wellFormed_and_spec_of_wp
      [`Trusted.MirSemantics.SatisfiesPost, `Trusted.MirSemantics.Diverges,
        `Trusted.MirSemantics.Behavior]
    requireParamClaimProof env locals semMod wpMod
      `Trusted.MirSemantics.WpFaultSoundnessClaim
      `Anneal.MirWp.wpFaultProg
      `Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault
      [`Trusted.MirSemantics.ReachesResult, `Trusted.MirSemantics.Diverges,
        `Trusted.MirSemantics.WellFormed]
    let posClaim := `Trusted.MirSemantics.PositiveCanaryClaim
    let negClaim := `Trusted.MirSemantics.NegativeCanaryClaim
    let widthClaim := `Trusted.MirSemantics.IntWidthBoundaryCanary
    for (claimName, proofName, reqConsts) in [
        (`Trusted.MirSemantics.CanaryPositiveAddAnnealClaim,
          `Anneal.MirWp.canary_positive_add_anneal, [posClaim]),
        (`Trusted.MirSemantics.CanaryPositiveEmptyUnitFnClaim,
          `Anneal.MirWp.canary_positive_empty_unit_fn, [posClaim]),
        (`Trusted.MirSemantics.CanaryPositiveStmtsAndCfAnnealClaim,
          `Anneal.MirWp.canary_positive_stmts_and_cf_anneal, [posClaim]),
        (`Trusted.MirSemantics.CanaryPositiveUnopAnnealClaim,
          `Anneal.MirWp.canary_positive_unop_anneal, [posClaim]),
        (`Trusted.MirSemantics.CanaryPositiveAllBinopsAnnealClaim,
          `Anneal.MirWp.canary_positive_all_binops_anneal, [posClaim]),
        (`Trusted.MirSemantics.CanaryPositiveAllIntWidthsAnnealClaim,
          `Anneal.MirWp.canary_positive_all_int_widths_anneal, [widthClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbDivZeroAnnealClaim,
          `Anneal.MirWp.canary_negative_ub_div_zero_anneal, [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbSignedRemOverflowI8Claim,
          `Anneal.MirWp.canary_negative_ub_signed_rem_overflow_i8, [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUnsupportedAnnealClaim,
          `Anneal.MirWp.canary_negative_unsupported_anneal, [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbAddUncheckedOverflowU32Claim,
          `Anneal.MirWp.canary_negative_ub_add_unchecked_overflow_u32,
          [negClaim, posClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim,
          `Anneal.MirWp.canary_negative_ub_shift_unchecked_at_bitwidth_anneal,
          [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbStorageDeadReadAnnealClaim,
          `Anneal.MirWp.canary_negative_ub_storage_dead_read_anneal,
          [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim,
          `Anneal.MirWp.canary_negative_ub_storage_dead_return_place_anneal,
          [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUbUnreachableAnnealClaim,
          `Anneal.MirWp.canary_negative_ub_unreachable_anneal, [negClaim]),
        (`Trusted.MirSemantics.CanaryNegativeUnsupportedUnsignedNegAnnealClaim,
          `Anneal.MirWp.canary_negative_unsupported_unsigned_neg_anneal,
          [negClaim])] do
      requireExactClaimProof env locals semMod wpMod claimName proofName
        reqConsts

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let roles ← buildModuleRoles j foundation trusted theory
  let (locals, extraNames) ← verifyAndCollectLocals env roles
  let lookup n :=
    match env.checked.get.find? n with
    | some ci => pure ci
    | none => fail s!"missing dependency declaration {n}"
  checkTierReferences env roles locals
  let requireMirWp := (j.getObjValAs? Bool "requireMirWp").toOption.getD true
  verifyMirWpCoreTheorems env roles locals requireMirWp
  let inventory ← locals.foldM (init := #[]) fun acc cName ci => do
    let (orig, cRole) ← constProvenance env roles cName
    match cRole with
    | .trusted tier =>
      let deps := (← declarationEdges ci).toArray.qsort Name.lt
      return acc.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig),
        ("kind", toJson (kind ci)), ("trustStatus", toJson tier.render),
        ("dependencies", toJson deps)]
    | .foundation | .theory => return acc
  let allLocalRoots := locals.fold (init := []) fun acc n _ => n :: acc
  let (allAxioms, allVisited) ←
    closure lookup (origin env) axiomPolicy allLocalRoots
  -- Replay every non-foundation constant from scratch through the Lean kernel
  -- against the locked foundation environment (`loadExts := false`).
  let base ← importEnv j foundation
  discard <| base.toKernelEnv.replay locals
  return Json.mkObj [
    ("graph", graph env), ("declarations", .arr inventory),
    ("kernelDeclarations", toJson inventory.size),
    ("replayedDeclarations", toJson locals.size),
    ("compilerOnlyNames", toJson extraNames.size),
    ("reachableDeclarations", toJson allVisited.size),
    ("axioms", toJson allAxioms), ("replay", toJson true)]

/-! ## Phase 3: `lean-miri` closure and Pass 2 correspondence audit -/

/-- Closed 5-role partition of every module loaded in the
`"correspondence-audit"` environment. -/
inductive CorrModuleRole where
  | foundation
  | sysrootFoundation
  | vendorMiri
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

/-- Import `roots` at `trustLevel := 0` with `plugins := #[]`,
`loadExts := false`, and `level := .private` using the configured search
path. -/
def importCorrEnv (roots : Array Name) : IO Environment := do
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

/-- Classify every loaded module in `env.header.modules` into one of the five
mutually exclusive `CorrModuleRole`s, verifying that `foundation`,
`sysrootFoundation`, `trusted`, `theory`, and `vendorMiri` are pairwise
disjoint, that all required modules (`foundation`, `trusted`, `theory`, and
`vendorMiri`) are loaded, and that any additional sysroot `Init.*`, `Std.*`, or
`Lean.*` module imported by `vendorMiri` belongs to the `sysrootFoundation`
allowlist whose `.olean*` artifacts `anneal-audit` verified against
`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`.

The `Lean.*` root must be admitted as a whole: several modules in the
`Miri.Interpreter.ExecutionMachine` closure (for example
`Miri.Memory.InitMask` and `Miri.TreeBorrows.TreeState`) `import Lean`, which
loads the entire `Lean` package from the pinned toolchain. Admission only
classifies these modules; `closureCorr` still rejects any `unsafe` or
`partial` constant that the interpreter or correspondence cone reaches, and
`verifyAndCollectCorrLocals` rejects any of their constants in the reserved
`Trusted` or `Anneal` namespaces. -/
def classifyCorrModules (j : Json) (env : Environment)
    (foundation trusted theory vendorMiri : Array Name) :
    IO (Std.HashMap Name CorrModuleRole) := do
  let sysrootFoundation ← names j "sysrootFoundation"
  let tierEntries ← field (α := Array (String × String)) j "moduleTiers"
  let tierMap ← tierEntries.foldlM (init := ({} : Std.HashMap Name TrustTier))
    fun acc (mStr, rawTier) => do
      let m := mStr.toName
      if acc.contains m then fail s!"duplicate module tier for {m}"
      unless trusted.contains m do
        fail s!"trust tier declared for non-Trusted module {m}"
      let some tier := TrustTier.parse? rawTier
        | fail s!"invalid trust tier {rawTier} for {m}"
      return acc.insert m tier
  let roles0 :=
    foundation.foldl (init := ({} : Std.HashMap Name CorrModuleRole))
      fun acc m => acc.insert m .foundation
  let roles1 ← trusted.foldlM (init := roles0) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    let some tier := tierMap.get? m
      | fail s!"missing trust tier for Trusted module {m}"
    return acc.insert m (.trusted tier)
  let roles2 ← theory.foldlM (init := roles1) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    return acc.insert m .theory
  let roles3 ← vendorMiri.foldlM (init := roles2) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    return acc.insert m .vendorMiri
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for (reqMod, _) in roles3 do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod} in correspondence environment"
  let roles4 ← sysrootFoundation.foldlM (init := roles3) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    return acc.insert m .sysrootFoundation
  for m in env.header.modules do
    unless roles4.contains m.module do
      fail s!"foreign module {m.module} in correspondence environment"
  return roles4

/-- Return the defining module name and `CorrModuleRole` for constant `n` in
`env`. -/
def corrConstProvenance (env : Environment)
    (roles : Std.HashMap Name CorrModuleRole) (n : Name) :
    IO (Name × CorrModuleRole) := do
  let orig ← origin env n
  let some role := roles.get? orig
    | fail s!"foreign module {orig} for {n}"
  return (orig, role)

/-- Return `true` if `ci`'s type, value (including `opaque` definitions), or
recursor rules directly reference `sorryAx`. -/
def constantHasSorry (ci : ConstantInfo) : Bool :=
  ci.type.hasSorry ||
    (ci.value? (allowOpaque := true)).any Expr.hasSorry ||
    match ci with
    | .recInfo v => v.rules.any (·.rhs.hasSorry)
    | _ => false

/-- Compiler-reflection primitives in `Init.Core` whose use trusts the Lean
compiler and runtime interpreter instead of the standalone kernel. -/
def forbiddenVendorCompilerRefs : List Name :=
  [`Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler,
   `Lean.reduceBool, `Lean.reduceNat]

/-- Return the first constant name in `targets` directly referenced in `ci`'s
type, value (including `opaque` definitions), or recursor rules, if any. -/
def constantFindRef? (ci : ConstantInfo) (targets : List Name) : Option Name :=
  let findInExpr (e : Expr) : Option Name :=
    match e.find? fun
      | .const n _ => targets.contains n
      | _ => false with
    | some (.const n _) => some n
    | _ => none
  match findInExpr ci.type with
  | some n => some n
  | none =>
    match (ci.value? (allowOpaque := true)).bind findInExpr with
    | some n => some n
    | none =>
      match ci with
      | .recInfo v => v.rules.findSome? fun r => findInExpr r.rhs
      | _ => none

/-- Validate all `.trusted`, `.theory`, `.vendorMiri`, and `.sysrootFoundation`
declarations in the environment and return `(repoLocals, corrLocals,
vendorLocals)`.

`.vendorMiri` and `.sysrootFoundation` modules are outside the repository's
source-role checks, so this rejects any constant they declare in the reserved
`Trusted` or `Anneal` root namespaces (after stripping private prefixes). For
every `.vendorMiri` constant, it also checks inventory and origin integrity,
rejects `axiom` (including any declaration whose body was stripped into an
axiom), `unsafe`, quotient primitives, direct `sorryAx` references, and direct
compiler-reflection references (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
`Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`), and collects the
unique vendored declarations for standalone kernel replay. Identical
sibling-module `.thmInfo` duplicates (lazily synthesized equation or
`congr_simp` lemmas) are permitted; any other duplicate is rejected. Other
unapproved axioms are rejected anywhere transitively reachable from the 21
`Miri.Interpreter.ExecutionMachine` cone roots by `closureCorr`. -/
def verifyAndCollectCorrLocals (env : Environment)
    (roles : Std.HashMap Name CorrModuleRole) (corrModules : NameSet) :
    IO (Std.HashMap Name ConstantInfo × Std.HashMap Name ConstantInfo ×
      Std.HashMap Name ConstantInfo) := do
  let mut repoLocals : Std.HashMap Name ConstantInfo := {}
  let mut corrLocals : Std.HashMap Name ConstantInfo := {}
  let mut vendorLocals : Std.HashMap Name ConstantInfo := {}
  let mut vendorOrigSeen : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    let some role := roles.get? m.module
      | fail s!"foreign module {m.module}"
    match role with
    | .foundation => pure ()
    | .sysrootFoundation =>
      for ci in data.constants do
        let root := (privateToUserName ci.name).getRoot
        if root == `Trusted || root == `Anneal then
          fail (s!"external module {m.module} cannot declare constant " ++
            s!"{ci.name} in reserved {root} namespace")
    | .vendorMiri =>
      let mut modSeen : NameSet := {}
      for ci in data.constants do
        if modSeen.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        modSeen := modSeen.insert ci.name
        let root := (privateToUserName ci.name).getRoot
        if root == `Trusted || root == `Anneal then
          fail (s!"external module {m.module} cannot declare constant " ++
            s!"{ci.name} in reserved {root} namespace")
        let (orig, origRole) ← corrConstProvenance env roles ci.name
        unless origRole == .vendorMiri do
          fail s!"inventory origin mismatch {ci.name}"
        let some stored := env.checked.get.find? ci.name
          | fail s!"missing stored declaration {ci.name}"
        unless kind stored == kind ci && stored.isUnsafe == ci.isUnsafe &&
            stored.isPartial == ci.isPartial && stored.type == ci.type &&
            stored.value? true == ci.value? true &&
            stored.levelParams == ci.levelParams do
          fail s!"stored declaration differs from inventory {ci.name}"
        if ci.isAxiom then
          fail (s!"vendor Miri module {m.module} cannot declare axiom " ++
            s!"{ci.name}")
        if ci.isUnsafe then
          fail (s!"vendor Miri module {m.module} cannot declare unsafe " ++
            s!"constant {ci.name}")
        if ci matches .quotInfo _ then
          fail s!"unexpected quotient primitive {ci.name} in {m.module}"
        -- Defensive invariant check: on Lean 4.34.1 `hasValue true` holds iff
        -- `(value? true).isSome`, and stripped bodies become axioms rejected
        -- by `ci.isAxiom` above.
        if ci.hasValue true && (ci.value? true).isNone then
          fail s!"missing stored body {ci.name}"
        if constantHasSorry ci then
          fail (s!"vendor Miri module {m.module} constant {ci.name} " ++
            "references sorryAx")
        if let some badRef :=
            constantFindRef? ci forbiddenVendorCompilerRefs then
          fail (s!"vendor Miri module {m.module} constant {ci.name} " ++
            s!"references forbidden compiler primitive {badRef}")
        if orig == m.module then
          vendorOrigSeen := vendorOrigSeen.insert ci.name
        match vendorLocals.get? ci.name with
        | some prev =>
          -- Sibling vendor modules can independently synthesize identical
          -- equation (`*.eq_1`) or `congr_simp` theorems on demand; reject any
          -- non-theorem or non-identical duplicate.
          unless (ci matches .thmInfo _) && (prev matches .thmInfo _) &&
              prev.type == ci.type && prev.value? true == ci.value? true &&
              prev.levelParams == ci.levelParams do
            fail s!"duplicate declaration {ci.name}"
        | none =>
          vendorLocals := vendorLocals.insert ci.name ci
    | .trusted tier =>
      for ci in data.constants do
        if repoLocals.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        let orig ← origin env ci.name
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
        let some stored := env.checked.get.find? ci.name
          | fail s!"missing stored declaration {ci.name}"
        unless stored.type == ci.type && stored.value? true == ci.value? true do
          fail s!"stored declaration differs from inventory {ci.name}"
        validateLocalConstant m.module (.trusted tier) ci
        repoLocals := repoLocals.insert ci.name ci
        if corrModules.contains m.module then
          corrLocals := corrLocals.insert ci.name ci
    | .theory =>
      for ci in data.constants do
        if repoLocals.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        let orig ← origin env ci.name
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
        let some stored := env.checked.get.find? ci.name
          | fail s!"missing stored declaration {ci.name}"
        unless stored.type == ci.type && stored.value? true == ci.value? true do
          fail s!"stored declaration differs from inventory {ci.name}"
        validateLocalConstant m.module .theory ci
        repoLocals := repoLocals.insert ci.name ci
        if corrModules.contains m.module then
          corrLocals := corrLocals.insert ci.name ci
  for (n, _) in vendorLocals do
    unless vendorOrigSeen.contains n do
      fail s!"inventory origin mismatch {n}"
  for (n, _) in env.checked.get.constants do
    let (_, origRole) ← corrConstProvenance env roles n
    match origRole with
    | .foundation | .sysrootFoundation => pure ()
    | .vendorMiri =>
      unless vendorLocals.contains n do
        fail s!"uninventoried vendor Miri constant {n}"
    | .trusted _ | .theory =>
      unless repoLocals.contains n do
        fail s!"uninventoried constant {n}"
  return (repoLocals, corrLocals, vendorLocals)

/-- Enforce trust-tier separation across all `.trusted` constants:
- A `.trusted .vetted` constant may only reference `.foundation` or
  `.trusted .vetted` constants (never `.sysrootFoundation`, `.vendorMiri`, or
  `.trusted (.candidate _)`).
- A `.trusted (.candidate _)` constant may reference `.foundation`,
  `.sysrootFoundation`, `.vendorMiri`, or `.trusted _` constants (never
  `.theory`). -/
def checkCorrTierReferences (env : Environment)
    (roles : Std.HashMap Name CorrModuleRole)
    (repoLocals : Std.HashMap Name ConstantInfo) : IO Unit := do
  for (cName, ci) in repoLocals do
    let (_, cRole) ← corrConstProvenance env roles cName
    if let .trusted tier := cRole then
      for dep in ← declarationEdges ci do
        let (depOrigin, depRole) ← corrConstProvenance env roles dep
        match depRole with
        | .foundation => pure ()
        | .sysrootFoundation | .vendorMiri =>
          if tier == .vetted then
            fail (s!"vetted constant {cName} references non-foundation " ++
              s!"constant {dep} from {depOrigin}")
        | .trusted depTier =>
          if tier == .vetted && depTier != .vetted then
            fail (s!"vetted constant {cName} references " ++
              s!"{depTier.render} constant {dep}")
        | .theory =>
          fail (s!"Trusted constant {cName} references {dep} from " ++
            s!"non-Trusted module {depOrigin}")

/-- Traverse the transitive constant-level dependency cone starting from
`pending`, verifying that:
- No reachable constant is `unsafe` or `isPartial`.
- No reachable `.vendorMiri` constant is `.opaqueInfo` (guaranteeing that none
  of the 24 `partial def` JSON parser helpers in `Miri.Input.*` is reachable).
- Every reachable axiom belongs to `axioms`. -/
partial def closureCorr (env : Environment)
    (roles : Std.HashMap Name CorrModuleRole)
    (axioms : Array (String × String))
    (pending : List Name) (visited : NameSet := {})
    (reachedAxioms : NameSet := {}) : IO (Array Name × NameSet) := do
  match pending with
  | [] => return (reachedAxioms.toArray.qsort Name.lt, visited)
  | n :: rest =>
    if visited.contains n then
      closureCorr env roles axioms rest visited reachedAxioms
    else
      let visited := visited.insert n
      let (m, role) ← corrConstProvenance env roles n
      let some ci := env.checked.get.find? n
        | fail s!"missing dependency declaration {n}"
      if ci.isUnsafe || ci.isPartial then
        fail (s!"unsafe/partial constant {n} from {m} in correspondence " ++
          "dependency cone")
      if role == .vendorMiri && (ci matches .opaqueInfo _) then
        fail (s!"opaque/partial vendor Miri constant {n} from {m} in " ++
          "correspondence dependency cone")
      let reachedAxioms ← if ci.isAxiom then do
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        pure (reachedAxioms.insert n)
      else
        pure reachedAxioms
      let deps ← declarationEdges ci
      closureCorr env roles axioms (deps.toList ++ rest) visited reachedAxioms

/-- Verify that the `Miri.Interpreter.ExecutionMachine` interpreter cone is
free of `unsafe`, `partial`, `.vendorMiri` `opaque` declarations, and
unapproved axioms. -/
def verifyMiriExecutionMachineCone (env : Environment)
    (roles : Std.HashMap Name CorrModuleRole)
    (axiomPolicy : Array (String × String)) : IO (Array Name × NameSet) :=
  closureCorr env roles axiomPolicy [
    `Miri.Interpreter.ExecutionMachine.step,
    `Miri.Interpreter.ExecutionMachine.withValidation,
    `Miri.Interpreter.ExecutionMachine.operandHooks,
    `Miri.Interpreter.IntegerOps.binary,
    `Miri.Interpreter.IntegerOps.binaryBool,
    `Miri.Interpreter.IntegerOps.unary,
    `Miri.Memory.ScalarInt.truncateFromUInt,
    `Miri.Memory.ScalarInt.tryFromUInt,
    `Miri.Memory.ScalarInt.tryToBool,
    `Miri.Interpreter.evalOperand,
    `Miri.Interpreter.evalPlaceToOp,
    `Miri.Interpreter.localToOp,
    `Miri.Interpreter.placeWriteLocalImmediate,
    `Miri.Interpreter.evalRvalueIntoPlace,
    `Miri.Interpreter.runRvalue,
    `Miri.Interpreter.Step.evalStatement,
    `Miri.Interpreter.Frame.storageLive,
    `Miri.Interpreter.Frame.storageDead,
    `Miri.Interpreter.ControlFlow.goToBlock,
    `Miri.Interpreter.ControlFlow.evalTerminator,
    `Miri.Interpreter.ControlFlow.returnFromCurrentFrame]

/-- Execute Phase 3 (`"correspondence-audit"`) on the `lean-miri` closure
environment, including standalone kernel replay of every non-`isPartial`
`.vendorMiri` declaration onto the authenticated `.foundation` and
`.sysrootFoundation` base on every run (cold build and cache hit alike). -/
def auditCorrespondence (j : Json) (sysrootStr : String)
    (foundation : Array Name) : IO Json := do
  let baseTrusted ← names j "trusted"
  let corrTrusted ← names j "corrTrusted"
  let baseTheory ← names j "theory"
  let corrTheory ← names j "corrTheory"
  let vendorMiri ← names j "vendorMiri"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let allTrusted := baseTrusted ++ corrTrusted
  let allTheory := baseTheory ++ corrTheory
  let corrModSet : NameSet := .ofList (corrTrusted.toList ++ corrTheory.toList)
  let env ← importCorrEnv (foundation ++ allTrusted ++ allTheory ++ vendorMiri)
  let roles ← classifyCorrModules j env foundation allTrusted
    allTheory vendorMiri
  let (repoLocals, _, vendorLocals) ←
    verifyAndCollectCorrLocals env roles corrModSet
  checkCorrTierReferences env roles repoLocals
  -- Build a clean replay base containing strictly the authenticated
  -- `.foundation` and `.sysrootFoundation` modules from the pinned sysroot
  -- (dropping repository and vendor directories from the search path), then
  -- replay every non-`isPartial` `.vendorMiri` declaration from scratch
  -- through the standalone Lean kernel. Compiler-generated `isPartial`
  -- (`*._unsafe_rec`) codegen helpers are omitted from the replay map
  -- (matching `Kernel.Environment.replay`), so any reference to them from a
  -- replayed declaration fails kernel replay with `unknown constant`.
  let sysrootBaseMods := env.header.modules.filterMap fun m =>
    match roles.get? m.module with
    | some .foundation | some .sysrootFoundation => some m.module
    | _ => none
  let vendorReplayLocals :=
    vendorLocals.fold (init := ({} : Std.HashMap Name ConstantInfo))
      fun acc n ci =>
        if ci.isPartial then acc else acc.insert n ci
  initSearchPath sysrootStr
  let baseEnv ← importCorrEnv sysrootBaseMods
  for m in baseEnv.header.modules do
    match roles.get? m.module with
    | some .foundation | some .sysrootFoundation => pure ()
    | _ =>
      fail s!"unexpected non-sysroot module {m.module} in vendor replay base"
  for (n, _) in vendorReplayLocals do
    if (baseEnv.checked.get.find? n).isSome then
      fail s!"vendor Miri constant {n} shadows sysroot declaration"
  try
    discard <| baseEnv.toKernelEnv.replay vendorReplayLocals
  catch err =>
    fail s!"vendor Miri kernel replay failed: {err}"
  let (miriAxioms, miriVisited) ←
    verifyMiriExecutionMachineCone env roles axiomPolicy
  return Json.mkObj [
    ("miriReplay", toJson true),
    ("miriReplayedDeclarations", toJson vendorReplayLocals.size),
    ("miriClosureReachableDeclarations", toJson miriVisited.size),
    ("miriClosureAxioms", toJson miriAxioms)]

/-- Dispatch `"preflight"`, `"audit"`, or `"correspondence-audit"` from the
JSON request `j`. -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  let sysrootStr ← field (α := String) j "sysroot"
  let foundation ← names j "foundation"
  match mode with
  | "preflight" =>
    initSearchPath sysrootStr
    let env ← importEnv j foundation true
    validateGraph j env
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  | "audit" =>
    initSearchPath sysrootStr
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let env ← importEnv j (foundation ++ trusted ++ theory)
    audit j env foundation trusted theory
  | "correspondence-audit" =>
    let spRaw ← field (α := Array String) j "searchPath"
    initSearchPath sysrootStr (spRaw.toList.map System.FilePath.mk)
    auditCorrespondence j sysrootStr foundation
  | _ => throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

/-- CLI entry point invoked via `lean --run TrustedBoundary.lean <req.json>
<res.json>`. -/
def main (args : List String) : IO UInt32 := do
  let [request, output] := args
    | IO.eprintln "expected request and result files"; return 2
  try
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
    let result ← TrustedBoundary.run j
    IO.FS.writeFile output <|
      (Json.mkObj [("ok", toJson true), ("result", result)]).pretty
    return 0
  catch error =>
    let message := error.toString
    let category :=
      if message.startsWith "policy:" then "policy" else "operational"
    IO.FS.writeFile output <|
      (Json.mkObj [
        ("ok", toJson false), ("category", toJson category),
        ("message", toJson message)]).pretty
    IO.eprintln message
    return if category == "policy" then 1 else 2
