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
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr

/-!
# Trusted Boundary and Kernel Environment Inspector (`TrustedBoundary.lean`)

Pinned to Lean 4.34.1, commit
`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`. `trusted/audit`
invokes this file in two phases over JSON IPC (`run` and `main`):

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
  foundation axiom allowlist, and a full kernel replay of every non-foundation
  constant against the foundation environment (`base.toKernelEnv.replay`).

## Module roles and trust tiers

Every admitted module in the environment is classified into a single
`ModuleRole`:

| `ModuleRole` | Directory / Source | Meaning |
| :--- | :--- | :--- |
| `.foundation` | Toolchain `Init.*` (`foundation-lock.json`) | Pinned Lean 4 standard prelude and core types |
| `.library` | Toolchain math (`trusted/audit/library-lock.json`) | Authenticated declarations replayed when logically reached |
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
  [`refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture, `mvp]

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
repository role. Representing these roles as mutually exclusive
constructors of one sum type makes overlapping or missing module classifications
unrepresentable. -/
inductive ModuleRole where
  | foundation
  | library
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
  let libraries ← names j "libraries"
  let roles0 ← libraries.foldlM (init := roles0) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    return acc.insert m .library
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
    IO (Std.HashMap Name ConstantInfo × NameSet × Array ConstantInfo) := do
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for (reqMod, _) in roles do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod}"
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut extraNames : NameSet := {}
  let mut alternateProofs : Array ConstantInfo := #[]
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    let some role := roles.get? m.module
      | fail s!"foreign module {m.module}"
    for ci in data.constants do
      let (orig, origRole) ← constProvenance env roles ci.name
      match role with
      | .foundation | .library =>
        unless origRole == .foundation || origRole == .library do
          fail s!"inventory origin mismatch {ci.name}"
      | .trusted _ | .theory =>
        if locals.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      unless stored.type == ci.type do
        fail s!"stored declaration type differs from inventory {ci.name}"
      if stored.value? true != ci.value? true then
        -- Pinned modules can export the same theorem with different proofs.
        -- Both bodies must be checked: retain every alternate body here and
        -- validate it after replaying its complete dependency closure below.
        -- Never apply this rule to source declarations or definition bodies.
        match role, stored, ci with
        | .foundation, .thmInfo a, .thmInfo b
        | .library, .thmInfo a, .thmInfo b =>
          unless a.levelParams == b.levelParams && a.all == b.all do
            fail s!"inconsistent pinned theorem metadata {ci.name}"
          -- Replay can also skip the selected body when the original base
          -- already has this theorem. Freshly check both selected and alternate
          -- bodies, rather than relying on replay's duplicate optimization.
          alternateProofs := (alternateProofs.push stored).push ci
        | _, _, _ =>
          fail s!"stored declaration differs from inventory {ci.name}"
      if role != .foundation && role != .library then
        validateLocalConstant m.module role ci
        locals := locals.insert ci.name ci
    for n in data.extraConstNames do
      let (orig, origRole) ← constProvenance env roles n
      match role with
      | .foundation | .library =>
        unless origRole == .foundation || origRole == .library do
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
    if origRole != .foundation && origRole != .library && !locals.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, extraNames, alternateProofs)

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
        | .foundation | .library => pure ()
        | .trusted depTier =>
          if tier == .vetted && depTier != .vetted then
            fail s!"vetted constant {cName} references {depTier.render} constant {dep}"
        | .theory =>
          fail s!"Trusted constant {cName} references {dep} from non-Trusted module {depOrigin}"

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let roles ← buildModuleRoles j foundation trusted theory
  let (locals, extraNames, alternateProofs) ← verifyAndCollectLocals env roles
  let lookup n :=
    match env.checked.get.find? n with
    | some ci => pure ci
    | none => fail s!"missing dependency declaration {n}"
  checkTierReferences env roles locals
  let inventory ← locals.foldM (init := #[]) fun acc cName ci => do
    let (orig, cRole) ← constProvenance env roles cName
    match cRole with
    | .trusted tier =>
      let deps := (← declarationEdges ci).toArray.qsort Name.lt
      return acc.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig),
        ("kind", toJson (kind ci)), ("trustStatus", toJson tier.render),
        ("dependencies", toJson deps)]
    | .foundation | .library | .theory => return acc
  let mut allLocalRoots := locals.fold (init := []) fun acc n _ => n :: acc
  for ci in alternateProofs do
    allLocalRoots := ci.name :: (← declarationEdges ci).toList ++ allLocalRoots
  let (allAxioms, allVisited) ←
    closure lookup (origin env) axiomPolicy allLocalRoots
  -- Replay every non-foundation constant from scratch through the Lean kernel
  -- against the locked foundation environment (`loadExts := false`).
  let base ← importEnv j foundation
  let mut replayMap := locals
  for n in allVisited do
    if (← origin env n) ∈ (← names j "libraries") then
      let ci ← lookup n
      if ci.isUnsafe || ci.isPartial then
        fail s!"unsafe/partial logical library dependency {n}"
      if ci matches .quotInfo _ then fail s!"unexpected quotient primitive {n}"
      if ci.hasValue true && (ci.value? true).isNone then
        fail s!"missing stored body {n}"
      replayMap := replayMap.insert n ci
  let replayed ← base.toKernelEnv.replay replayMap
  -- Replay may reuse an existing theorem of the same type by proof
  -- irrelevance. Add each alternative under a fresh name so the kernel must
  -- check that body, including its declared universes, against the same type.
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L88-L101
  let checkedEnv := Environment.ofKernelEnv replayed
  let mut freshIndex := 0
  for ci in alternateProofs do
    let .thmInfo info := ci | fail "non-theorem alternate inventory body"
    let typeOfType ← match Kernel.check checkedEnv {} info.type with
      | .ok t => pure t
      | .error _ => fail s!"invalid alternate theorem type {ci.name}"
    unless Kernel.isDefEqGuarded checkedEnv {} typeOfType (.sort .zero) do
      fail s!"alternate theorem is not a proposition {ci.name}"
    let mut fresh := Name.num `_anneal_checked_alternate freshIndex
    while (replayed.find? fresh).isSome do
      freshIndex := freshIndex + 1
      fresh := Name.num `_anneal_checked_alternate freshIndex
    freshIndex := freshIndex + 1
    match replayed.addDeclCore 0 0 (.thmDecl { info with name := fresh })
        (cancelTk? := none) with
    | .ok _ => pure ()
    | .error _ => fail s!"alternate pinned theorem proof rejected {ci.name}"
  return Json.mkObj [
    ("graph", graph env), ("declarations", .arr inventory),
    ("kernelDeclarations", toJson inventory.size),
    ("replayedDeclarations", toJson replayMap.size),
    ("checkedAlternateProofs", toJson alternateProofs.size),
    ("compilerOnlyNames", toJson extraNames.size),
    ("reachableDeclarations", toJson allVisited.size),
    ("axioms", toJson allAxioms), ("replay", toJson true)]

/-- Read only a source header. Target elaboration is deliberately separate from
repository command admission: authored macros and tactics may use arbitrary
syntax, while their final logical dependencies must pass kernel replay. -/
def inspectHeader (moduleName : Name) (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, state, messages) ← Parser.parseHeader ctx
  if messages.hasErrors || state.recovering then
    fail s!"header parser error in {moduleName}"
  return Json.mkObj [("module", toJson moduleName),
    ("imports", toJson (Elab.HeaderSyntax.imports header))]

/-- Authority of an authenticated target source, independent of its namespace. -/
inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq

instance : ToString TargetRole where
  toString
    | .model => "model"
    | .specification => "specification"
    | .capture => "capture"
    | .expected => "expected"
    | .proof => "proof"

/-- Parse the closed role vocabulary shared with the Rust runner. -/
def targetRole (raw : String) : IO TargetRole :=
  match raw with
  | "model" => pure .model
  | "specification" => pure .specification
  | "capture" => pure .capture
  | "expected" => pure .expected
  | "proof" => pure .proof
  | _ => fail s!"unknown target role {raw}"

/-- Model and specification meanings cannot depend on unreviewed proof helpers.
Capture is independent of specifications, and Expected may use all reviewed
roles. The same rule is enforced on imports by the Rust runner. -/
def TargetRole.allows (role dep : TargetRole) : Bool :=
  match role with
  | .model => dep == .model
  | .specification => dep == .model || dep == .specification
  | .capture => dep == .model || dep == .capture
  | .expected => dep != .proof
  | .proof => true

/-- Module origins partition foundation, checked libraries and target sources. -/
inductive TargetOrigin where
  | foundation | library | source (role : TargetRole)

/-- Target auditing checks actual stored declarations, including private helpers
and generated inductive members. It imports no unvalidated declaration into the
replay base. Metadata loading below is target-only and subject to the same
experimental intact-host assumption as arbitrary target elaboration. -/
def targetAudit (j : Json) (foundation : Array Name) : IO Json := do
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let mut roles : Std.HashMap Name TargetOrigin := {}
  for m in foundation do roles := roles.insert m .foundation
  for m in libraries do
    if roles.contains m then fail s!"overlapping target module {m}"
    roles := roles.insert m .library
  let mut roots := foundation ++ libraries
  for item in modules do
    let m := (← field (α := String) item "module").toName
    let role ← targetRole (← field item "role")
    if roles.contains m then fail s!"overlapping target module {m}"
    roles := roles.insert m (.source role)
    roots := roots.push m
  let env ← importEnv j roots
  validateGraph j env
  let provenance n := do
    let m ← origin env n
    let some role := roles.get? m | fail s!"foreign target module {m}"
    return (m, role)
  let lookup n := do
    let some ci := env.checked.get.find? n
      | fail s!"missing target dependency {n}"
    return ci
  -- Cross-check source inventory and the environment's actual stored values.
  -- Library declarations are checked when reached, so irrelevant metaprogram
  -- implementation constants do not become restrictions on authored proofs.
  let mut sourceInventory : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | fail s!"foreign target module {m.module}"
    for imp in data.imports do
      let some impRole := roles.get? imp.module
        | fail s!"foreign target module {imp.module}"
      match role, impRole with
      | .source r, .source d =>
        unless r.allows d do
          fail s!"target import authority violation {m.module} ({r}) imports {imp.module} ({d})"
      | .library, .source _ =>
        fail s!"installed library {m.module} imports target source {imp.module}"
      | .foundation, .library | .foundation, .source _ =>
        fail s!"foundation module {m.module} imports non-foundation {imp.module}"
      | _, _ => pure ()
    if let .source _ := role then
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target inventory {m.module}"
      for ci in data.constants do
        if sourceInventory.contains ci.name then
          fail s!"duplicate target declaration {ci.name}"
        unless (← origin env ci.name) == m.module do
          fail s!"target inventory origin mismatch {ci.name}"
        let stored ← lookup ci.name
        unless stored.type == ci.type && stored.value? true == ci.value? true do
          fail s!"stored target declaration differs {ci.name}"
        sourceInventory := sourceInventory.insert ci.name
  let theoremName := (← field (α := String) target "theoremName").toName
  let theoremModule := (← field (α := String) target "theoremModule").toName
  let expectedName := (← field (α := String) target "expectedDeclaration").toName
  let expectedModule := (← field (α := String) target "expectedModule").toName
  match roles.get? theoremModule, roles.get? expectedModule with
  | some (.source .proof), some (.source .expected) => pure ()
  | _, _ => fail "incorrect target/expected authority roles"
  let theoremInfo ← lookup theoremName
  let expectedInfo ← lookup expectedName
  unless (← origin env theoremName) == theoremModule &&
      (← origin env expectedName) == expectedModule do
    fail "incorrect target/expected declaration origin"
  unless theoremInfo matches .thmInfo _ do fail "target root must be a theorem"
  unless expectedInfo matches .defnInfo _ do fail "Expected must be a definition"
  unless theoremInfo.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
    fail "target and Expected must have no universe parameters"
  unless expectedInfo.type == .sort .zero do fail "Expected must have type Prop"
  let canonicalRoot := (← field (α := String) target "canonicalRoot").toName
  let subjectName := (← field (α := String) target "subjectDeclaration").toName
  let specName := (← field (α := String) target "specificationDeclaration").toName
  for (n, requiredRole) in [(canonicalRoot, TargetRole.model),
      (subjectName, TargetRole.capture), (specName, TargetRole.specification)] do
    let (_, role) ← provenance n
    match role with
    | .source actual =>
      unless actual == requiredRole do fail s!"incorrect canonical input origin {n}"
    | _ => fail s!"incorrect canonical input origin {n}"
    unless (← lookup n).levelParams.isEmpty do
      fail s!"canonical input has universe parameters {n}"
  -- Build the proposition directly from authenticated kernel names. Imported
  -- syntax, namespaces and elaborators may change the compiled Expected body;
  -- that convenience definition is therefore checked against this expression.
  let canonical := mkApp2 (mkConst canonicalRoot) (mkConst subjectName) (mkConst specName)
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  unless axiomPolicy == #[("Classical.choice", "Init.Prelude"),
      ("Quot.sound", "Init.Prelude"), ("propext", "Init.Core")] do
    fail "target axiom policy differs from the original foundation"
  let (axioms, reached) ← closure lookup (origin env) axiomPolicy
    [theoremName, expectedName, canonicalRoot, subjectName, specName]
  let (_, expectedReached) ← closure lookup (origin env) axiomPolicy
    [canonicalRoot, subjectName, specName]
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut modelRoots : List Name := []
  let mut specRoots : List Name := []
  for n in reached do
    let ci ← lookup n
    let (_, role) ← provenance n
    match role with
    | .foundation => pure ()
    | .library | .source _ =>
      if ci.isUnsafe || ci.isPartial then
        fail s!"unsafe/partial logical dependency {n}"
      if ci matches .quotInfo _ then fail s!"unexpected quotient primitive {n}"
      if ci.hasValue true && (ci.value? true).isNone then
        fail s!"missing stored body {n}"
      if let .source _ := role then
        unless sourceInventory.contains n do
          fail s!"uninventoried target dependency {n}"
      for dep in ← declarationEdges ci do
        let (_, depRole) ← provenance dep
        match role, depRole with
        | .source r, .source d =>
          unless r.allows d do fail s!"target authority violation {n} references {dep}"
        | .library, .source _ =>
          fail s!"installed library {n} references target source {dep}"
        | _, _ => pure ()
      replayMap := replayMap.insert n ci
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()
  -- Lean 4.34.1 replay skips unsafe and partial declarations; the explicit
  -- checks above are necessary before handing this complete map to replay.
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L176-L185
  let base ← importEnv j foundation
  let replayed ← try base.toKernelEnv.replay replayMap
    catch error => fail s!"kernel replay rejected target dependency: {error}"
  let checkedEnv := Environment.ofKernelEnv replayed
  unless (Kernel.check checkedEnv {} canonical).toOption == some (.sort .zero) do
    fail "canonical root application must have type Prop"
  let some expectedBody := expectedInfo.value? true
    | fail "Expected has no stored body"
  unless Kernel.isDefEqGuarded checkedEnv {} expectedBody canonical do
    fail "compiled Expected body differs from the canonical root"
  match Kernel.isDefEq checkedEnv {} theoremInfo.type canonical with
  | .ok true => pure ()
  | .ok false => fail "target theorem type differs from Expected"
  | .error _ => fail "kernel could not compare target theorem type"
  -- Compiler replacement attributes do not affect logical reduction. Reject
  -- authored changes nevertheless, including changes to an imported helper.
  -- Compare against authenticated toolchain metadata so ordinary pinned extern
  -- implementations of Nat/BitVec operations remain available. These metadata
  -- imports execute only under the target's declared intact-host assumption;
  -- the repository audit continues to load no non-foundation extensions.
  let fixedMetadata ← importEnv j (foundation ++ libraries) true
  let targetMetadata ← importEnv j roots true
  for n in reached do
    unless Compiler.getImplementedBy? fixedMetadata n ==
        Compiler.getImplementedBy? targetMetadata n &&
        getExternAttrData? fixedMetadata n == getExternAttrData? targetMetadata n do
      fail s!"unchecked compiler override on logical dependency {n}"
    let replacement (metadata : Environment) :=
      (Compiler.CSimp.ext.getState metadata).map.find? n |>.map fun e =>
        (e.toDeclName, e.thmName)
    unless replacement fixedMetadata == replacement targetMetadata do
      fail s!"authored compiler replacement on logical dependency {n}"
  let (_, modelClosure) ← closure lookup (origin env) axiomPolicy modelRoots
  let (_, specClosure) ← closure lookup (origin env) axiomPolicy specRoots
  let describe (nodes : NameSet) := nodes.toArray.qsort Name.lt |>.mapM fun n => do
    return Json.mkObj [("name", toJson n), ("module", toJson (← origin env n))]
  return Json.mkObj [("theorem", toJson theoremName),
    ("canonicalRoot", toJson canonicalRoot), ("subject", toJson subjectName),
    ("specification", toJson specName), ("graph", graph env),
    ("expected", toJson expectedName), ("axioms", toJson axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson replayMap.size),
    ("modelClosure", .arr (← describe modelClosure)),
    ("specificationClosure", .arr (← describe specClosure))]

/-- Dispatch a repository or target inspection request. -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  initSearchPath (← field (α := String) j "sysroot")
  let foundation ← names j "foundation"
  match mode with
  | "headers" =>
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n,p) => inspectHeader n.toName p
    return Json.mkObj [("headers", .arr headers)]
  | "preflight" =>
    let libraries ← names j "libraries"
    let env ← importEnv j (foundation ++ libraries) true
    validateGraph j env
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  | "audit" =>
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let libraries ← names j "libraries"
    let env ← importEnv j (foundation ++ libraries ++ trusted ++ theory)
    audit j env foundation trusted theory
  | "target-audit" => targetAudit j foundation
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
