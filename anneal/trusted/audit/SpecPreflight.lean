-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean.Elab.Import
import Lean.Parser.Tactic
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr

/-!
# Runtime Target Preflight and Module Index (`SpecPreflight.lean`)

Provides the minimal runtime Lean surface needed by `cargo-anneal` on Lean
`v4.35.0+` (where target theorem auditing runs exclusively through the
pure-Rust Universal NDJSON Comparator `5a`/`5b`/`5c` backed by `nanoda_bin` and
`con-ron`, so no Lean process ever produces the verdict and no `Proof` `.olean`
is ever loaded outside the sandboxed `5b` exporter):

- **`"headers"` (target import discovery before elaboration):**
  Parses only module `prelude`/`module`/`import` headers via
  `Parser.parseHeader`, admitting Lean 4 `module`-system headers across target
  roles (`import all` confined to `Anneal.*` on `Init.Data.Nat.Bitwise.Basic`)
  and rejecting `Lean.*`/`Lake.*` and disallowed `meta` imports.
- **`"spec-preflight"` (target specification syntactic admission):**
  Parses every `TargetRole::Specification` source against the authenticated
  `Init` + `Std` parser environment (`trustLevel := 0`, `plugins := #[]`,
  `extensions := true` for foundation parser tables, zero target `.olean`s
  loaded, zero command elaboration), enforcing a closed 14-command allowlist,
  arity-independent fail-closed modifiers, resolved lexical scope tracking
  across all five `open` forms, closed attributes, deriving, `set_option`, and
  declaration-root rules, a dynamic fail-closed pure-spec tactic allowlist,
  and exact term/quotation guards.
- **`"resolve-imports"` (unpinned sysroot import-DAG discovery):**
  Imports requested `Init`/`Std` sysroot modules with `trustLevel := 0`,
  `plugins := #[]`, and `loadExts := false` and emits the sorted compiled
  `.olean` import DAG for unpinned host admission.
- **`"sysroot-consts"` (authenticated sysroot constant-to-module index):**
  Imports the already-admitted `Init`/`Std` sysroot closure with
  `trustLevel := 0`, `plugins := #[]`, and `loadExts := false` (zero target
  `.olean`s loaded) and emits `[moduleName, [constName, ...]]` entries for
  pure-Rust Action `5c` `moduleIdentities` provenance and the clean-sysroot
  content pinning of every sysroot-named constant.
- **`"target-consts"` (retained non-`Proof` target module index):**
  Imports the admitted sysroot closure plus the compiled `Model`, `Capture`,
  `Specification`, and `Expected` `.olean`s (never a `Proof` `.olean`) with
  `trustLevel := 0`, `plugins := #[]`, and `loadExts := false` after
  validating each target `.olean` before import, and emits each target
  module's exact constant inventory from its own `ModuleData` (so Action `5c`
  attributes compiler-generated constants to their defining module), plus its
  `@[implemented_by]`, `@[extern]`, and `@[csimp]` subjects.

Repository Pass 1 (`"preflight"`, `"audit"`) and Pass 2 (`lean-miri`
`"correspondence-preflight"`, `"correspondence-audit"`) offline checks remain
isolated in `trusted/audit/TrustedBoundary.lean` and are never compiled or
executed during `v4.35.0+` target verification.
-/

open Lean

namespace SpecPreflight

/-! ## JSON IPC and sysroot parser-environment helpers -/

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

/-- Verify module/data header alignment on an imported `Environment` and disable
exporting. -/
def finalizeImportedEnv (env : Environment) : IO Environment := do
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

/-- Import `roots` from the explicit artifact map in `j` at `trustLevel := 0`
with `plugins := #[]` and `level := .private`.

- In `"spec-preflight"`, `extensions := true` loads the authenticated `Init` +
  `Std` sysroot's parser extensions and initializers (`trustLevel := 0`, zero
  target `.olean`s). Parsing specification commands never elaborates them,
  and this imported sysroot parser code is trusted.
- In `"sysroot-consts"` and `"target-consts"`, `extensions := false` skips
  module initializers and extension callbacks so only compiled `.olean`
  headers and constant-to-module indices are read.
  https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Environment.lean -/
def importEnv (j : Json) (roots : Array Name)
    (extensions := false) : IO Environment := do
  let arts ← artifacts j
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  finalizeImportedEnv env

/-- Import `roots` at `trustLevel := 0` with `plugins := #[]` and
`loadExts := false` using the configured sysroot search path
(`"resolve-imports"`). -/
def importSysrootEnv (roots : Array Name) : IO Environment := do
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false)
    (level := .private)
  finalizeImportedEnv env

/-- Verify that the import DAG recorded in the `.olean` headers of `env` is
identical to the admitted `"graph"` from `"headers"` or `"resolve-imports"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do
    fail "compiled module/import DAG differs from admitted DAG"

/-- Initialize `Lean.searchPathRef` from `leanSysroot` and explicit staged
directories `sp`, ignoring ambient `LEAN_PATH` (which is used only to bootstrap
the precompiled `SpecPreflight.olean` module). -/
def initHermeticSearchPath (leanSysroot : System.FilePath)
    (sp : SearchPath := ∅) : IO Unit := do
  searchPathRef.set (sp ++ (← getBuiltinSearchPath leanSysroot))

/-! ## Header and specification syntactic preflight -/

/-- Lists the module header syntax kinds permitted in target source files.
`moduleTk`, `public`, and `all` are permitted syntactically so `inspectHeader`
and `validateTargetImports` can enforce role-scoped module and import-modifier
policies (`meta` remains excluded at the syntax-kind level). -/
def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.moduleTk, ``Parser.Module.prelude,
  ``Parser.Module.import, ``Parser.Module.public, ``Parser.Module.all]

/-- Lists the base pure tactic syntax kinds inherited by
`allowedSpecTacticKinds`. -/
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

/-- Return `true` if `id` is a valid user-written identifier with non-empty
string components, no macro scopes, and no `_root_` namespace escape. -/
def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

/-- Validate a parsed module header syntax tree against `allowedHeaderKinds`
without allowing missing recovery placeholders or malformed identifiers. -/
partial def inspectHeaderSyntax (s : Syntax) (requirePrelude := false) :
    IO Unit := do
  match s with
  | .missing => fail "unexpected missing syntax node"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do
      fail s!"invalid identifier {val}"
  | .node _ k args =>
    unless k == nullKind || allowedHeaderKinds.contains k do
      fail s!"unsupported syntax kind {k}"
    -- `Parser.Module.header` is `$[module]? $[prelude]? $imports*`, so
    -- `args[1]` is the optional `prelude` wrapped in a `nullKind` node.
    if requirePrelude && k == ``Parser.Module.header then
      unless !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
        fail "missing explicit `prelude` in module header"
    for child in args do
      inspectHeaderSyntax child requirePrelude


/-- Return all candidate namespaces that `open <id>` can resolve to from
`(currNs, openDecls)`.

Checking every candidate—instead of stopping at the innermost existing
namespace in the union `parserEnv` as `resolveNamespaceUsingScope?` does—closes
decoy-namespace shadowing when an unimported module declares a namespace with
the same suffix as a forbidden namespace. -/
def candidateOpenNamespaces (currNs : Name) (openDecls : List OpenDecl)
    (id : Name) : List Name :=
  let rec scopeCandidates : Name → List Name
    | .anonymous => [id.replacePrefix rootNamespace .anonymous]
    | ns@(.str p _) => (ns ++ id) :: scopeCandidates p
    | _ => []
  let openCandidates := openDecls.filterMap fun
    | OpenDecl.simple ns _ => some (ns ++ id)
    | _ => none
  (scopeCandidates currNs ++ openCandidates).eraseDups

/-- Lexical scope frame tracked by `parseAndInspectCommands`, mirroring Lean's
`Elab.Command.Scope` (`header`, `currNamespace`, `openDecls`) so
`Parser.parseCommand` sees the same lexical namespace and `open` context as
compilation while preflight rejects activating any namespace in
`scopedNamespaces`. -/
structure ParseScope where
  header : String
  currNamespace : Name
  openDecls : List OpenDecl
  deriving Inhabited

/-- Compose the names of up to the innermost `n` scopes in `ss`, truncating at
an unnamed scope, matching `Lean.Elab.Command.nameOfScopes`. -/
def nameOfParseScopes : List ParseScope → Nat → Name
  | _, 0 => .anonymous
  | [], _ => .anonymous
  | s :: ss, n + 1 =>
    if s.header == "" then .anonymous
    else .str (nameOfParseScopes ss n) s.header

/-- Extract the user-supplied declaration identifier from an allowlisted
`Parser.Command.declaration` syntax node, if present. -/
def declarationIdent? (stx : Syntax) : Option Name :=
  let decl := stx[1]
  if decl.getKind == ``Parser.Command.instance then
    if decl[3].isNone then none else some decl[3][0][0].getId
  else
    some decl[1][0].getId

/-- Return `true` iff `moduleName` belongs to the `Trusted` root namespace. -/
def isTrustedModuleName (moduleName : Name) : Bool :=
  moduleName == `Trusted || moduleName.getRoot == `Trusted

/-- Return `true` iff `moduleName` belongs to the bundled `Anneal` theory
namespace (`Anneal` or `Anneal.*`). -/
def isAnnealModuleName (moduleName : Name) : Bool :=
  moduleName == `Anneal || moduleName.getRoot == `Anneal

/-- Foundation modules that bundled `Anneal.*` `module`-system theory files may
open via `import all`. -/
def allowedTheoryImportAllModules : List Name :=
  [`Init.Data.Nat.Bitwise.Basic]

/-- Pure-signature debug, dynamic-library loading, and file-embedding
identifiers rejected explicitly in `"spec-preflight"`, closing
`Init/Util.lean`'s
`lean_dbg_*` externs, `Lean.LoadDynlib` / `loadDynlib` / `loadPlugin`, and
`includeStr`. -/
def forbiddenPureIdentifiers : List Name := [
  `dbgTrace, `dbgTraceVal, `dbgTraceIfShared,
  `dbgStackTrace, `dbgStackTraceIf, `dbgSleep,
  `lean_dbg_trace, `lean_dbg_trace_if_shared,
  `lean_dbg_stack_trace, `lean_dbg_sleep,
  `loadDynlib, `loadPlugin,
  `lean_load_dynlib, `lean_load_plugin,
  `lean_dynlib_load, `lean_dynlib_get, `lean_dynlib_symbol_run_as_init,
  `includeStr]

/-- Root namespaces forbidden in pure source preflight and specifications (`IO`,
`BaseIO`, `EIO`, `EST`, `ST`, `Task`, `System`, `Lake`, plus `Lean` in
specifications). -/
def forbiddenPureRootNamespaces : List Name := [
  `Lake, `IO, `BaseIO, `EIO, `EST, `ST, `Task, `System]

/-- Sub-namespaces exposing filesystem, system, UV event-loop, or dynamic
library loading primitives beneath otherwise-admitted roots (`Init`, `Std`,
`Lean`). -/
def forbiddenSysUvPrefixes : List Name := [
  `Init.System, `Std.Internal.UV, `Internal.UV,
  `Lean.LoadDynlib, `Lean.loadDynlib, `Lean.loadPlugin, `Lean.Dynlib,
  `Dynlib]

/-- Return `true` when `n` (ignoring `_root_`) matches or is nested beneath a
forbidden I/O, `Init.System.*`, `Std.Internal.UV.*`, `Lean.LoadDynlib`, or
effectful root namespace. -/
def isForbiddenPureNamespace (n : Name) (banLeanRoot : Bool := false) : Bool :=
  let u := n.replacePrefix rootNamespace .anonymous
  let r := u.getRoot
  forbiddenPureRootNamespaces.contains r ||
    (banLeanRoot && r == `Lean) ||
    forbiddenSysUvPrefixes.any fun pre => u == pre || pre.isPrefixOf u

/-- Return `true` when imported module `m` belongs to `Lean.*`, `Lake.*`,
`Init.System.*`, or `Std.Internal.UV.*`. -/
def isForbiddenPureImport (m : Name) : Bool :=
  let r := m.getRoot
  r == `Lean || r == `Lake ||
    m == `Init.System || (`Init.System).isPrefixOf m ||
    m == `Std.Internal.UV || (`Std.Internal.UV).isPrefixOf m

/-- Validate target module import edges (`"headers"` and `"spec-preflight"`):
- Non-module targets (`allowModule = false`) reject `import all` and
  non-exported imports unconditionally.
- Lean 4 `module` targets (`allowModule = true`) allow private
  (non-exported) imports across target roles, and permit `import all`
  strictly when `allowTheoryImportAll = true` (bundled `Anneal.*` modules)
  and the imported module is in `allowedTheoryImportAllModules`.
- Every target rejects `Lean.*`/`Lake.*`, `Init.System.*`, and
  `Std.Internal.UV.*` imports, and any `isMeta` edge other than Lean 4's
  synthetic `!hasPrelude` `Init(isMeta = true)` paired with a non-meta
  `Init` edge. -/
def validateTargetImports (context : String) (imports : Array Import)
    (allowModule : Bool := false) (allowTheoryImportAll : Bool := false) :
    IO Unit := do
  let hasNonMetaInit := imports.any fun imp =>
    imp.module == `Init && !imp.isMeta
  for imp in imports do
    if imp.importAll then
      let ok := allowModule && allowTheoryImportAll &&
        allowedTheoryImportAllModules.contains imp.module
      unless ok do
        fail s!"import modifiers are unsupported in {context}"
    if !imp.isExported && !allowModule then
      fail s!"import modifiers are unsupported in {context}"
    if imp.isMeta then
      unless imp.module == `Init && hasNonMetaInit do
        fail s!"meta import {imp.module} is unsupported in {context}"
    if isForbiddenPureImport imp.module then
      fail s!"disallowed sysroot import {imp.module} in {context}"

/-- Read and validate a target source header (`"headers"`), admitting Lean 4
`module`-system headers across target modules while keeping `import all`
confined strictly to bundled `Anneal.*` runtime modules. -/
def inspectHeader (moduleName : Name) (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, state, messages) ← Parser.parseHeader ctx
  if messages.hasErrors || state.recovering then
    fail s!"header parser error in {moduleName}"
  let isModule := Elab.HeaderSyntax.isModule header
  inspectHeaderSyntax header.raw (requirePrelude := false)
  let imports := Elab.HeaderSyntax.imports header
  validateTargetImports moduleName.toString imports
    (allowModule := isModule)
    (allowTheoryImportAll := isAnnealModuleName moduleName)
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("isModule", toJson isModule)]

/-! ## Phase 1b: Specification syntactic preflight (`"spec-preflight"`) -/

/-- Closed 14-command allowlist permitted in `TargetRole::Specification`
modules. -/
def allowedSpecCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end,
  ``Parser.Command.universe, ``Parser.Command.variable,
  ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in,
  ``Parser.Command.attribute, ``Parser.Command.deriving,
  ``Parser.Command.set_option, ``Parser.Command.moduleDoc]

/-- Commands allowed on the left-hand side of `Command.in` inside a target
specification. -/
def allowedSpecInLhsKinds : List Name := [
  ``Parser.Command.open, ``Parser.Command.variable,
  ``Parser.Command.universe, ``Parser.Command.set_option,
  ``Parser.Command.attribute]

/-- Return `true` when `k` is allowed inside a `mutual` block or on the RHS of
`Command.in` inside a specification (the 14-command allowlist minus scoping and
nested `mutual`). -/
def isAllowedSpecNestedCommand (k : SyntaxNodeKind) : Bool :=
  allowedSpecCommandKinds.contains k &&
    ![``Parser.Command.namespace, ``Parser.Command.section,
      ``Parser.Command.end, ``Parser.Command.mutual].contains k

/-- Closed 7-declaration allowlist permitted inside `Parser.Command.declaration`
in specifications (`opaque`, `axiom`, `example`, and `coinductive` excluded). -/
def allowedSpecDeclarationKinds : List Name := [
  ``Parser.Command.definition, ``Parser.Command.abbrev,
  ``Parser.Command.theorem, ``Parser.Command.structure,
  ``Parser.Command.inductive, ``Parser.Command.classInductive,
  ``Parser.Command.instance]

/-- Non-empty modifier kinds permitted inside `Parser.Command.declModifiers`
in specifications (arity-independent fail-closed check). -/
def allowedSpecDeclModifierKinds : List Name := [
  ``Parser.Command.docComment, ``Parser.Term.attributes,
  ``Parser.Command.private, ``Parser.Command.protected,
  ``Parser.Command.noncomputable]

/-- Return `true` iff modifier kind `k` is allowed inside
`Parser.Command.declModifiers` for a specification (`isModule` additionally
permits `Parser.Command.public`). -/
def isAllowedSpecDeclModifierKind (isModule : Bool) (k : Name) : Bool :=
  allowedSpecDeclModifierKinds.contains k ||
    (isModule && k == ``Parser.Command.public)

/-- Modifier and fixpoint kinds unconditionally rejected anywhere in a
specification AST (`Parser.Term.scoped` closes `scoped instance` as well as
`@[scoped ...]`; `Parser.Command.public` is rejected in non-`module`
specifications by `inspectSpecSyntax` and declaration modifier checks). -/
def forbiddenSpecModifierKinds : List Name := [
  ``Parser.Command.meta, ``Parser.Command.unsafe,
  ``Parser.Command.partial,
  ``Parser.Term.unsafe, ``Parser.Term.scoped,
  `Lean.Parser.Termination.partialFixpoint,
  `Lean.Parser.Termination.coinductiveFixpoint,
  `Lean.Parser.Termination.inductiveFixpoint]

/-- Root namespaces forbidden in specification lexical scopes and references
(except `System.Platform.{numBits, getNumBits, numBits_eq}`). -/
def forbiddenSpecRootNamespaces : List Name :=
  `Lean :: forbiddenPureRootNamespaces

/-- Top-level namespaces reserved for the Lean kernel, standard library,
bundled model, and proof modules (`forbiddenSpecRootNamespaces` plus `Trusted`,
`Anneal`, `Proof`, and every `reservedKernelRoots` root, including `Init` and
`Std`). Target specifications may reference standard types (`Nat`, `String`,
etc.) in terms, but may never open `namespace <Root>` or declare constants
beneath them. -/
def forbiddenSpecDeclRootNamespaces : List Name :=
  forbiddenSpecRootNamespaces ++ [
    `Trusted, `Anneal, `Proof, `Init, `Std,
    `Nat, `String, `Char, `Bool, `Int, `Int8, `Int16, `Int32, `Int64, `ISize,
    `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Float, `Float32,
    `ByteArray, `Subarray, `Array, `List, `Option, `Sum, `Prod, `Fin, `Subtype,
    `Eq, `HEq, `Quot, `Classical, `LeanExport, `LeanIR, `Thunk, `Unit, `PUnit,
    `Empty, `PEmpty, `True, `False, `And, `Or, `Not, `Iff, `Exists, `Sigma,
    `PSigma, `Decidable, `Nonempty, `Ordering, `Rat, `Except, `EStateM, `StateM]

/-- Identifier components forbidden anywhere in specification references,
dot-projections, `open`, and `export` declarations (`autoParam` evaluates a
stored `Lean.Syntax` tactic script during elaboration, bypassing syntactic
tactic inspection; `panic*`/`outOfBounds`/`sliceOrPanic` carry runtime panic
side effects; `repeatM` implements partial unbounded `while`/`repeat`
loops). -/
def forbiddenSpecIdentifierComponents : List String := [
  "autoParam", "panic", "panicCore", "panicWithPos", "panicWithPosWithDecl",
  "outOfBounds", "repeatM", "sliceOrPanic"]

/-- Root-level and extern identifiers forbidden in specifications (`autoParam`
evaluates a stored `Lean.Syntax` tactic script during elaboration, bypassing
syntactic tactic inspection; `panic*` constants carry runtime panic side
effects; and `forbiddenPureIdentifiers` covers debug, dynamic-library, and
`includeStr` externs). -/
def forbiddenSpecIdentifiers : List Name :=
  [`autoParam, `panic, `panicCore, `panicWithPos, `panicWithPosWithDecl] ++
    forbiddenPureIdentifiers

/-- Exact `System.Platform` declarations admitted in target specifications. -/
def allowedSystemPlatformDecls : List Name := [
  `System.Platform.numBits,
  `System.Platform.getNumBits,
  `System.Platform.numBits_eq]

/-- Simple attributes permitted inside `@[...]` in target specifications. -/
def allowedSpecSimpleAttrs : List Name := [
  `reducible, `semireducible, `irreducible, `inline, `match_pattern]

/-- Attribute names permitted in `attribute [-attr]` inside specifications. -/
def allowedSpecEraseAttrs : List Name := [
  `simp, `instance, `ext, `specialize,
  `reducible, `semireducible, `irreducible, `inline, `match_pattern]

/-- Typeclasses permitted in `deriving` clauses and `deriving instance` commands
inside target specifications. -/
def allowedSpecDerivingClasses : List Name := [
  `BEq, `DecidableEq, `Repr, `Inhabited, `Ord, `Hashable, `Nonempty]

/-- Pure non-tactic parser categories in `Init`/`Std`. Every other category
registered in `Parser.parserExtension` (including `tactic`, `conv`, `grind*`,
`sym_*`, `m*Pat`, `vcgenDischarge`, `stx`, `rawStx`, and future solver
categories) is treated as tactic-like and gated by `allowedSpecTacticKinds`. -/
def nonTacticSpecCategories : List Name := [
  `attr, `binderPred, `command, `doElem, `level, `prec, `prio,
  `structInstFieldDecl, `term]

/-- Pure `Init` specification, proof, and termination tactics permitted inside
`TargetRole::Specification` modules. Excludes `bv_decide`, `bv_check`,
`native_decide`, `decide_cbv`, `cbv`, `grind`, `rfl'`, `sorry`, `admit`,
`run_tac`, `sleep`, `dbg_trace`, `Tactic.{open,set_option}`, `conv`, `sym`,
`mvcgen`, and interactive suggestion tactics. -/
def allowedSpecTacticKinds : NameSet :=
  .ofList <| allowedTheoryTacticKinds ++ [
    `Lean.cdot, `Lean.calcTactic,
    `Lean.Parser.Tactic.tacticSeqBracketed,
    `Lean.Parser.Tactic.nestedTactic,
    `Lean.Parser.Tactic.focus, `Lean.Parser.Tactic.case,
    `Lean.Parser.Tactic.case', `Lean.Parser.Tactic.caseArg,
    `Lean.Parser.Tactic.«tacticNext_=>_»,
    `Lean.Parser.Tactic.allGoals, `Lean.Parser.Tactic.anyGoals,
    `Lean.Parser.Tactic.skip, `Lean.Parser.Tactic.done,
    `Lean.Parser.Tactic.tacticTry_, `Lean.Parser.Tactic.tacticIterate____,
    `Lean.Parser.Tactic.repeat', `Lean.Parser.Tactic.repeat1',
    `Lean.Parser.Tactic.tacIfThenElse, `Lean.Parser.Tactic.tacDepIfThenElse,
    `Lean.Parser.Tactic.rotateLeft, `Lean.Parser.Tactic.rotateRight,
    `Lean.Parser.Tactic.assumption, `Lean.Parser.Tactic.contradiction,
    `Lean.Parser.Tactic.tacticTrivial, `Lean.Parser.Tactic.tacticExfalso,
    `Lean.Parser.Tactic.tacticNofun, `Lean.Parser.Tactic.eqRefl,
    `Lean.Parser.Tactic.acRfl, `Lean.Parser.Tactic.applyRfl,
    `Lean.Parser.Tactic.symm, `Lean.Parser.Tactic.congr,
    `Lean.Parser.Tactic.split, `Lean.Parser.Tactic.clear,
    `Lean.Parser.Tactic.clearValue, `Lean.Parser.Tactic.generalize,
    `Lean.Parser.Tactic.rename, `Lean.Parser.Tactic.renameI,
    `Lean.Parser.Tactic.replace, `Lean.Parser.Tactic.specialize,
    `Lean.Parser.Tactic.intros, `Lean.Parser.Tactic.introMatch,
    `Lean.Parser.Tactic.injections, `Lean.Parser.Tactic.substEqs,
    `Lean.Parser.Tactic.substVars, `Lean.Parser.Tactic.delta,
    `Lean.Parser.Tactic.rewriteSeq, `Lean.Parser.Tactic.tacticErw___,
    `Lean.Parser.Tactic.tacticRwa__, `Lean.Parser.Tactic.show,
    `Lean.Parser.Tactic.tacticSuffices_, `Lean.Parser.Tactic.«tacticExists_,,»,
    `Lean.Parser.Tactic.tacticAnd_intros, `Lean.Parser.Tactic.tacticHave',
    `Lean.Parser.Tactic.tacticHaveI__, `Lean.Parser.Tactic.tacticLet'__,
    `Lean.Parser.Tactic.tacticLetI__, `Lean.Parser.Tactic.letToHave,
    `Lean.Parser.Tactic.tacticInfer_instance, `Lean.Parser.Tactic.refine',
    `Lean.Parser.Tactic.falseOrByContra, `Lean.Parser.Tactic.classical,
    `Lean.Parser.Tactic.match, `«tacticBy_cases_:_»,
    `Lean.Parser.Tactic.simpAll, `Lean.Parser.Tactic.simpArith,
    `Lean.Parser.Tactic.simpAllArith, `Lean.Parser.Tactic.simpa,
    `Lean.Parser.Tactic.simpaArgsRest, `Lean.Parser.Tactic.tacticSimpa!_,
    `Lean.Parser.Tactic.tacticSimpa!__1, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.locationType,
    `Lean.Parser.Tactic.locationWildcard, `Lean.Parser.Tactic.discharger,
    `Lean.Parser.Tactic.configItem, `Lean.Parser.Tactic.posConfigItem,
    `Lean.Parser.Tactic.negConfigItem,
    `Lean.Parser.Tactic.omega, `Lean.Parser.Tactic.tacticBv_omega,
    `tacticDecreasing_tactic, `tacticDecreasing_trivial,
    `tacticDecreasing_trivial_pre_omega, `tacticDecreasing_with_,
    `tacticSimp_wf, `tacticClean_wf,
    `tacticGet_elem_tactic, `tacticGet_elem_tactic_trivial,
    `Array.tacticArray_get_dec, `Array.tacticArray_mem_dec,
    `List.tacticSizeOf_list_dec,
    `Lean.Parser.Tactic.funCases, `Lean.Parser.Tactic.funInduction,
    `Lean.Parser.Tactic.rcases, `Lean.Parser.Tactic.rintro,
    `Lean.Parser.Tactic.obtain,
    `Lean.Parser.Tactic.rcasesPatLo, `Lean.Parser.Tactic.rcasesPatMed,
    `Lean.Parser.Tactic.rcasesPat.ignore, `Lean.Parser.Tactic.rcasesPat.paren,
    `Lean.Parser.Tactic.rcasesPat.clear, `Lean.Parser.Tactic.rcasesPat.explicit,
    `Lean.Parser.Tactic.rcasesPat.tuple, `Lean.Parser.Tactic.rcasesPat.one,
    `Lean.Parser.Tactic.rintroPat.one, `Lean.Parser.Tactic.rintroPat.binder]

/-- Term, `doElem`, and declaration-value meta/debug/panic/contract/quotation
syntax kinds rejected anywhere in a target specification.

`Lean.includeStr` and `Lean.byElab` use double-backtick resolution so renames
in `Init` fail inspector compilation. This denylist is an interim guard pending
migration of specification term/`doElem` inspection to a closed allowlist
mirroring Pass 1 (`allowedTrustedSyntaxKinds`). -/
def forbiddenSpecTermKinds : NameSet := .ofList [
  ``Lean.includeStr, ``Lean.byElab,
  ``Parser.Term.sorry, ``Parser.Term.unsafe,
  ``Parser.Term.quotedName, ``Parser.Term.doubleQuotedName,
  ``Parser.Term.binderTactic,
  `Lean.modCast,
  `Lean.Parser.Term.panic, `Lean.Parser.Term.unreachable,
  `Lean.Parser.Term.assert, `Lean.Parser.Term.debugAssert,
  `Lean.Parser.Term.doAssert, `Lean.Parser.Term.doAssertion,
  `Lean.Parser.Term.doDebugAssert,
  `«term__[_]_!»,
  `Lean.Parser.Term.doWhile, `Lean.Parser.Term.doRepeat,
  `Lean.Parser.Term.doRepeatUntil,
  `Lean.Parser.Command.contractDeclVal,
  `Lean.Parser.Command.requiresClause,
  `Lean.Parser.Command.ensuresClause,
  `«term∎»,
  `Std.DTreeMap.Internal.Impl.«term✓»,
  `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.idbg,
  `Lean.Parser.Term.doDbgTrace, `Lean.Parser.Term.doIdbg,
  `Lean.Parser.Term.matchExpr, `Lean.Parser.Term.letExpr,
  `Lean.Parser.Term.doMatchExpr, `Lean.Parser.Term.doLetExpr,
  `Lean.Parser.Term.doLetMetaExpr, `Lean.Parser.Term.showTermElabImpl,
  `Lean.Parser.Tactic.showTermElab, `Lean.Parser.Term.declName,
  `Lean.Parser.Term.withDeclName, `Lean.Parser.Term.privateDecl,
  `Lean.Parser.Term.leading_parser, `Lean.Parser.Term.trailing_parser,
  `Lean.Parser.Term.elabToSyntax, `Lean.«termMacro.trace[_]_»,
  `Lean.Parser.Syntax.exact?, `Lean.termEval_prec_, `Lean.termEval_prio_,
  `termPrintln!__, `Lean.Parser.Term.dynamicQuot,
  `Lean.Parser.Term.precheckedQuot,
  `Lean.Parser.Term.logNamedErrorMacro,
  `Lean.Parser.Term.logNamedErrorAtMacro,
  `Lean.Parser.Term.logNamedWarningMacro,
  `Lean.Parser.Term.logNamedWarningAtMacro,
  `Lean.Parser.Term.throwNamedErrorMacro,
  `Lean.Parser.Term.throwNamedErrorAtMacro]

/-- Return `true` when `k` is a syntax quotation node (`*.quot`/`*.quotSeq`). -/
def isQuotationKind (k : SyntaxNodeKind) : Bool :=
  match k with
  | .str _ "quot" | .str _ "quotSeq" => true
  | _ => false

/-- Return `true` when any component of `id` is `"_unsafe_rec"`. -/
def hasUnsafeRecComponent (id : Name) : Bool :=
  id.components.any fun
    | .str .anonymous seg => seg == "_unsafe_rec"
    | _ => false

/-- Return `true` when any string component of `id` contains `'!'` (blocking
panicking partial helpers such as `head!`, `get!`, `getElem!`, `back!`,
`getLast!`, `tail!`, `get!Internal`, etc.). -/
def hasBangComponent (id : Name) : Bool :=
  id.components.any fun
    | .str .anonymous seg => seg.contains '!'
    | _ => false

/-- Return `true` when any string component of `id` belongs to
`forbiddenSpecIdentifierComponents` (catching bare references, qualified
paths, dot-projections such as `pos.sliceOrPanic`, and `open`/`export`
items). -/
def hasForbiddenSpecIdentComponent (id : Name) : Bool :=
  id.components.any fun
    | .str .anonymous seg => forbiddenSpecIdentifierComponents.contains seg
    | _ => false

/-- Extract `(commandLikeKinds, tacticLikeKinds)` dynamically from
`Parser.parserExtension` on `env`. -/
def collectSpecParserSets (env : Environment) : IO (NameSet × NameSet) := do
  let cats := (Parser.parserExtension.getState env).categories
  let some cmdCat := cats.find? `command
    | throw <| IO.userError "missing command parser category"
  let commandLikeKinds : NameSet :=
    cmdCat.kinds.foldl (init := {}) fun acc k _ => acc.insert k
  let tacticLikeKinds : NameSet :=
    cats.foldl (init := {}) fun acc catName cat =>
      if nonTacticSpecCategories.contains catName then acc
      else cat.kinds.foldl (init := acc) fun inner k _ => inner.insert k
  return (commandLikeKinds, tacticLikeKinds)

/-- Return `true` if `s` is an empty `null` node or a single priority literal
(`num`, `prioHigh`, `prioLow`, `prioDefault`, `prioMid`). -/
def isSpecPrioOpt (s : Syntax) : Bool :=
  if s.isOfKind nullKind && s.getArgs.isEmpty then true
  else if s.isOfKind nullKind && s.getArgs.size == 1 then
    let k := s.getArgs[0]!.getKind
    k == numLitKind ||
      [`prioHigh, `prioLow, `prioDefault, `prioMid].contains k
  else false

/-- Validate a `Parser.Term.attrInstance` node inside a target specification:
permit only empty or `local` `attrKind` (never `scoped`), permit global
`@[expose]` strictly in `module` mode, and dispatch strictly over the allowed
attribute kinds. -/
def validateSpecAttrInstance (args : Array Syntax) (isModule : Bool := false) :
    IO Unit := do
  unless args.size == 2 do
    fail "unsupported attribute instance shape in specification"
  let attrKind := args[0]!
  unless attrKind.isOfKind ``Parser.Term.attrKind &&
      attrKind.getArgs.size == 1 do
    fail "unsupported attribute kind in specification"
  let kindOpt := attrKind.getArgs[0]!
  unless kindOpt.isOfKind nullKind &&
      (kindOpt.getArgs.isEmpty ||
        (kindOpt.getArgs.size == 1 &&
          kindOpt.getArgs[0]!.isOfKind ``Parser.Term.local)) do
    fail "only global or local attributes are allowed in specification"
  let attr := args[1]!
  let ak := attr.getKind
  if ak == ``Parser.Attr.simple then
    let attrName := attr[0].getId
    let ok := allowedSpecSimpleAttrs.contains attrName ||
      (isModule && attrName == `expose && kindOpt.getArgs.isEmpty)
    unless ok do
      fail s!"unsupported attribute {attrName} in specification"
    unless attr[1].isOfKind nullKind && attr[1].getArgs.isEmpty do
      fail s!"unsupported arguments on attribute {attrName} in specification"
  else if ak == `Lean.Parser.Attr.simp then
    let aArgs := attr.getArgs
    unless aArgs.size == 4 do
      fail "unsupported simp attribute shape in specification"
    let okPost := aArgs[1]!.isOfKind nullKind &&
      (aArgs[1]!.getArgs.isEmpty ||
        (aArgs[1]!.getArgs.size == 1 &&
          match aArgs[1]!.getArgs[0]! with
          | .atom _ "↓" | .atom _ "↑" => true
          | _ => false))
    let okInv := aArgs[2]!.isOfKind nullKind &&
      (aArgs[2]!.getArgs.isEmpty ||
        (aArgs[2]!.getArgs.size == 1 &&
          match aArgs[2]!.getArgs[0]! with
          | .atom _ "←" | .atom _ "<-" => true
          | _ => false))
    unless okPost && okInv && isSpecPrioOpt aArgs[3]! do
      fail "unsupported arguments on simp attribute in specification"
  else if ak == ``Parser.Attr.instance then
    unless attr.getArgs.size == 2 && isSpecPrioOpt attr[1] do
      fail "unsupported arguments on instance attribute in specification"
  else if ak == ``Parser.Attr.ext then
    let aArgs := attr.getArgs
    unless aArgs.size >= 1 &&
        (aArgs.extract 1 aArgs.size).all fun c =>
          isSpecPrioOpt c ||
            (c.isOfKind nullKind && c.getArgs.size == 1 &&
              match c.getArgs[0]! with
              | .atom _ "flat" => true
              | _ => false) do
      fail "unsupported arguments on ext attribute in specification"
  else if ak == ``Parser.Attr.specialize then
    unless attr.getArgs.size == 2 && attr[1].isOfKind nullKind &&
        attr[1].getArgs.all fun c =>
          c.isOfKind numLitKind ||
            (c.isIdent && isValidSourceIdent c.getId &&
              !hasUnsafeRecComponent c.getId &&
              !hasBangComponent c.getId &&
              !hasForbiddenSpecIdentComponent c.getId &&
              !forbiddenSpecRootNamespaces.contains c.getId.getRoot) do
      fail "unsupported arguments on specialize attribute in specification"
  else
    fail s!"unsupported attribute kind {ak} in specification"

/-- Validate a `Parser.Command.sectionHeader` arity-independently: in
non-`module` specifications every child must be `null #[]` or
`null #[atom "noncomputable"]`; `module`-mode specifications additionally admit
`public` and `@[expose]`. -/
def validateSpecSectionHeader (args : Array Syntax)
    (isModule : Bool := false) : IO Unit := do
  for child in args do
    let ok := child.isOfKind nullKind &&
      (child.getArgs.isEmpty ||
        (child.getArgs.size == 1 &&
          match child.getArgs[0]! with
          | .atom _ "noncomputable" => true
          | .atom _ "public" => isModule
          | _ => false) ||
        (isModule && child.getArgs.size == 3 &&
          match child.getArgs[0]!, child.getArgs[1]!, child.getArgs[2]! with
          | .atom _ "@[", .atom _ "expose", .atom _ "]" => true
          | _, _, _ => false))
    unless ok do
      fail "unsupported section/namespace modifier in specification"

/-- Validate `Command.set_option` (`args.size == 4`) or `Term.set_option`
(`args.size == 6`) against the closed specification option policy. -/
def validateSpecSetOption (args : Array Syntax) : IO Unit := do
  unless args.size == 4 || args.size == 6 do
    fail "unsupported set_option shape in specification"
  unless args[2]!.isOfKind nullKind && args[2]!.getArgs.isEmpty do
    fail "unsupported set_option shape in specification"
  let optName := args[1]!.getId
  let valStx := args[3]!
  if optName == `maxHeartbeats || optName == `maxRecDepth then
    unless valStx.isOfKind numLitKind do
      fail s!"option {optName} requires a numeric literal in specification"
  else if (`linter).isPrefixOf optName then
    let isBoolLit := match valStx with
      | .atom _ "true" | .atom _ "false" => true
      | .ident _ _ `true _ | .ident _ _ `false _ => true
      | _ => false
    unless isBoolLit do
      fail s!"option {optName} requires a boolean literal in specification"
  else
    fail s!"unsupported option {optName} in specification"

/-- Validate `Lean.Parser.Tactic.decide` config items: admit bare `decide` or
only `+kernel`, `-kernel`, `+revert`, and `-revert` (rejecting `+native`,
`-native`, and `(config := ...)`). -/
def validateSpecDecideTactic (args : Array Syntax) : IO Unit := do
  unless args.size == 2 && args[1]!.isOfKind `Lean.Parser.Tactic.optConfig &&
      args[1]!.getArgs.size == 1 do
    fail "unsupported decide tactic shape in specification"
  for item in args[1]![0].getArgs do
    unless item.isOfKind `Lean.Parser.Tactic.configItem &&
        item.getArgs.size == 1 do
      fail "unsupported decide config item in specification"
    let inner := item[0]
    let ik := inner.getKind
    unless (ik == `Lean.Parser.Tactic.posConfigItem ||
        ik == `Lean.Parser.Tactic.negConfigItem) && inner.getArgs.size == 2 do
      fail "unsupported decide config modifier in specification"
    let opt := inner[1].getId
    unless opt == `kernel || opt == `revert do
      fail s!"unsupported decide config option {opt} in specification"

/-- Reject `ns` if its root belongs to `forbiddenSpecRootNamespaces` or is a
forbidden `Init.System.*` / `Std.Internal.UV.*` / `Lean.LoadDynlib`
sub-scope. -/
def rejectForbiddenSpecNamespace (how : String) (ns : Name) : IO Unit := do
  if isForbiddenPureNamespace ns (banLeanRoot := true) then
    fail s!"cannot {how} forbidden namespace {ns} in specification"

/-- Reject `ns` whenever `rejectForbiddenSpecNamespace` rejects it (forbidden
pure roots, `Lean`, and `forbiddenSysUvPrefixes` sub-scopes such as
`Init.System` or `Internal.UV`), or when its root belongs to
`forbiddenSpecDeclRootNamespaces`. Both checks strip a leading `_root_`. -/
def rejectForbiddenSpecDeclNamespace (how : String) (ns : Name) : IO Unit := do
  rejectForbiddenSpecNamespace how ns
  let u := ns.replacePrefix rootNamespace .anonymous
  if forbiddenSpecDeclRootNamespaces.contains u.getRoot then
    fail s!"cannot {how} reserved namespace {ns} in specification"

/-- Validate an `open` declaration node (`openSimple`, `openOnly`, `openHiding`,
`openRenaming`, `openScoped`) against `forbiddenSpecRootNamespaces`, allowing
`open System.Platform (numBits ...)` strictly for `allowedSystemPlatformDecls`,
and return the updated `(parserEnv, openDecls)`. -/
def validateSpecOpenDecl (currNs : Name) (openDecls : List OpenDecl)
    (parserEnv : Environment) (openDecl : Syntax) :
    IO (Environment × List OpenDecl) := do
  let hasSimple (ods : List OpenDecl) (ns : Name) : Bool :=
    ods.any fun
      | OpenDecl.simple existing _ => existing == ns
      | _ => false
  let addSimple (ods : List OpenDecl) (ns : Name) : List OpenDecl :=
    if hasSimple ods ns then ods else OpenDecl.simple ns [] :: ods
  let k := openDecl.getKind
  if k == ``Parser.Command.openSimple then
    let mut env := parserEnv
    let mut ods := openDecls
    for idStx in openDecl[0].getArgs do
      let id := idStx.getId
      unless isValidSourceIdent id && !hasUnsafeRecComponent id do
        fail s!"invalid open identifier {id} in specification"
      let candidates := candidateOpenNamespaces currNs ods id
      let mut added := false
      for ns in candidates do
        rejectForbiddenSpecNamespace "open" ns
        if env.isNamespace ns then
          ods := addSimple ods ns
          env := Parser.parserExtension.activateScoped env ns
          added := true
      if !added then
        let stripped := id.replacePrefix rootNamespace .anonymous
        rejectForbiddenSpecNamespace "open" stripped
        ods := addSimple ods stripped
    return (env, ods)
  else if k == ``Parser.Command.openOnly then
    let nsId := openDecl[0].getId
    unless isValidSourceIdent nsId && !hasUnsafeRecComponent nsId do
      fail s!"invalid open namespace {nsId} in specification"
    let itemIds := openDecl[2].getArgs.map Syntax.getId
    for itemId in itemIds do
      unless isValidSourceIdent itemId && !hasUnsafeRecComponent itemId &&
          !hasBangComponent itemId &&
          !hasForbiddenSpecIdentComponent itemId do
        fail s!"invalid open item {itemId} in specification"
    let candidates := candidateOpenNamespaces currNs openDecls nsId
    let mut ods := openDecls
    for ns in candidates do
      if ns == `System.Platform then
        if itemIds.isEmpty then
          fail "cannot open System.Platform without explicit allowed items"
        for itemId in itemIds do
          let full := ns ++ itemId
          unless allowedSystemPlatformDecls.contains full do
            fail s!"disallowed open item {full} in specification"
          ods := OpenDecl.explicit itemId full :: ods
      else
        rejectForbiddenSpecNamespace "open" ns
        for itemId in itemIds do
          ods := OpenDecl.explicit itemId (ns ++ itemId) :: ods
    return (parserEnv, ods)
  else if k == ``Parser.Command.openHiding ||
      k == ``Parser.Command.openRenaming then
    let nsId := openDecl[0].getId
    unless isValidSourceIdent nsId && !hasUnsafeRecComponent nsId do
      fail s!"invalid open namespace {nsId} in specification"
    if k == ``Parser.Command.openHiding then
      for idStx in openDecl[2].getArgs do
        let hid := idStx.getId
        unless isValidSourceIdent hid && !hasUnsafeRecComponent hid do
          fail s!"invalid open hiding identifier {hid} in specification"
    else
      for itemStx in openDecl[2].getArgs do
        let fromId := itemStx[0].getId
        let toId := itemStx[2].getId
        unless isValidSourceIdent fromId && !hasUnsafeRecComponent fromId &&
            !hasBangComponent fromId &&
            !hasForbiddenSpecIdentComponent fromId &&
            isValidSourceIdent toId && !hasUnsafeRecComponent toId &&
            !hasBangComponent toId &&
            !hasForbiddenSpecIdentComponent toId do
          fail (s!"invalid open renaming item {fromId} -> {toId} " ++
            "in specification")
    let candidates := candidateOpenNamespaces currNs openDecls nsId
    let mut env := parserEnv
    let mut ods := openDecls
    let mut added := false
    for ns in candidates do
      rejectForbiddenSpecNamespace "open" ns
      if env.isNamespace ns then
        ods := addSimple ods ns
        if k == ``Parser.Command.openHiding then
          env := Parser.parserExtension.activateScoped env ns
        added := true
    if !added then
      let stripped := nsId.replacePrefix rootNamespace .anonymous
      rejectForbiddenSpecNamespace "open" stripped
      ods := addSimple ods stripped
    return (env, ods)
  else if k == ``Parser.Command.openScoped then
    let mut env := parserEnv
    for idStx in openDecl[1].getArgs do
      let id := idStx.getId
      unless isValidSourceIdent id && !hasUnsafeRecComponent id do
        fail s!"invalid open scoped identifier {id} in specification"
      let candidates := candidateOpenNamespaces currNs openDecls id
      for ns in candidates do
        rejectForbiddenSpecNamespace "open scoped" ns
        if env.isNamespace ns then
          env := Parser.parserExtension.activateScoped env ns
    return (env, openDecls)
  else
    fail s!"unsupported open form {k} in specification"

/-- Validate `export ns (id1 ...)` in a specification using the same namespace
and `System.Platform` policy as `openOnly`. -/
def validateSpecExport (currNs : Name) (openDecls : List OpenDecl)
    (args : Array Syntax) : IO Unit := do
  unless args.size == 5 do
    fail "unsupported export shape in specification"
  let nsId := args[1]!.getId
  unless isValidSourceIdent nsId && !hasUnsafeRecComponent nsId do
    fail s!"invalid export namespace {nsId} in specification"
  let itemIds := args[3]!.getArgs.map Syntax.getId
  for itemId in itemIds do
    unless isValidSourceIdent itemId && !hasUnsafeRecComponent itemId &&
        !hasBangComponent itemId &&
        !hasForbiddenSpecIdentComponent itemId do
      fail s!"invalid export item {itemId} in specification"
  for ns in candidateOpenNamespaces currNs openDecls nsId do
    if ns == `System.Platform then
      if itemIds.isEmpty then
        fail "cannot export System.Platform without explicit allowed items"
      for itemId in itemIds do
        let full := ns ++ itemId
        unless allowedSystemPlatformDecls.contains full do
          fail s!"disallowed export item {full} in specification"
    else
      rejectForbiddenSpecNamespace "export" ns

/-- Push `namespace`/`section` scopes for `"spec-preflight"`, rejecting every
namespace refused by `rejectForbiddenSpecDeclNamespace` and activating scoped
parser extensions when entering an existing (non-reserved) namespace. -/
def pushSpecScopes (isNewNamespace : Bool) (header : Name)
    (parserEnv : Environment) (scopes : List ParseScope) :
    IO (Environment × List ParseScope) := do
  match header with
  | .anonymous => return (parserEnv, scopes)
  | .str p seg =>
    let (parserEnv, scopes) ←
      pushSpecScopes isNewNamespace p parserEnv scopes
    let top := scopes.head!
    let newNs := if isNewNamespace then Name.mkStr top.currNamespace seg
      else top.currNamespace
    if isNewNamespace then
      rejectForbiddenSpecDeclNamespace "enter" newNs
    let mut env := parserEnv.registerNamespace newNs
    env := Parser.parserExtension.pushScope env
    if isNewNamespace && parserEnv.isNamespace newNs then
      env := Parser.parserExtension.activateScoped env newNs
    let newScope : ParseScope :=
      { top with header := seg, currNamespace := newNs }
    return (env, newScope :: scopes)
  | _ => fail s!"invalid scope name {header}"

/-- Check that declaration identifier `id` and every namespace prefix of `id`
pass `rejectForbiddenSpecDeclNamespace`, and register each prefix in
`parserEnv`. -/
def checkSpecDeclNamespace (currNs : Name) (id : Name)
    (parserEnv : Environment) : IO Environment := do
  if (`_root_).isPrefixOf id then
    fail s!"invalid _root_ declaration identifier {id} in specification"
  let rec walkPrefix (ns : Name) (env : Environment) :
      IO (Name × Environment) := do
    match ns with
    | .anonymous => return (currNs, env)
    | .str p seg =>
      let (base, env) ← walkPrefix p env
      let full := Name.mkStr base seg
      rejectForbiddenSpecDeclNamespace "declare in" full
      return (full, env.registerNamespace full)
    | _ => fail s!"invalid declaration namespace {id} in specification"
  match id with
  | .str .anonymous seg =>
    rejectForbiddenSpecDeclNamespace "declare" (Name.mkStr currNs seg)
    return parserEnv
  | .str pre _ =>
    let (_, env) ← walkPrefix pre parserEnv
    return env
  | _ => return parserEnv

/-- Return `true` if `openDecl` activates scoped parser extensions in Lean 4
(`open N`, `open N hiding ...`, and `open scoped N`). -/
def openActivatesScoped (openDecl : Syntax) : Bool :=
  openDecl.isOfKind ``Parser.Command.openSimple ||
    openDecl.isOfKind ``Parser.Command.openHiding ||
    openDecl.isOfKind ``Parser.Command.openScoped

/-- Recursively validate a specification AST node `s` under lexical scope
`(currNs, openDecls)` and dynamic `(commandLikeKinds, tacticLikeKinds)`. -/
partial def inspectSpecSyntax (commandLikeKinds tacticLikeKinds : NameSet)
    (parserEnv : Environment) (currNs : Name) (openDecls : List OpenDecl)
    (s : Syntax) (isModule : Bool := false) : IO Unit := do
  match s with
  | .missing => fail "unexpected missing syntax node in specification"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do
      fail s!"invalid identifier {val} in specification"
    if hasUnsafeRecComponent val then
      fail s!"disallowed _unsafe_rec identifier {val} in specification"
    let checkSpecIdent (cand : Name) : IO Unit := do
      if hasForbiddenSpecIdentComponent cand || hasBangComponent cand then
        fail s!"disallowed identifier {val} in specification"
      if forbiddenSpecIdentifiers.contains cand then
        fail s!"disallowed identifier {val} in specification"
      if isForbiddenPureNamespace cand (banLeanRoot := true) then
        unless allowedSystemPlatformDecls.contains cand do
          fail s!"disallowed reference {val} in specification"
    checkSpecIdent val
    for cand in candidateOpenNamespaces currNs openDecls val do
      checkSpecIdent cand
  | .node _ k args =>
    if k != nullKind then
      if forbiddenSpecModifierKinds.contains k ||
          (!isModule && k == ``Parser.Command.public) then
        fail s!"disallowed modifier {k} in specification"
      if forbiddenSpecTermKinds.contains k || isQuotationKind k then
        fail s!"disallowed syntax {k} in specification"
      if commandLikeKinds.contains k then
        unless allowedSpecCommandKinds.contains k do
          fail s!"unsupported command {k} in specification"
      if tacticLikeKinds.contains k || (`Lean.Parser.Tactic).isPrefixOf k then
        unless allowedSpecTacticKinds.contains k do
          fail s!"unsupported tactic {k} in specification"
    -- Structural checks and scope-aware subtrees.
    if k == ``Parser.Command.sectionHeader then
      validateSpecSectionHeader args isModule
    else if k == ``Parser.Command.declModifiers then
      for child in args do
        unless child.isOfKind nullKind && child.getArgs.isEmpty do
          let ck := child.getKind
          if ck == nullKind then
            for inner in child.getArgs do
              unless isAllowedSpecDeclModifierKind isModule inner.getKind do
                fail (s!"unsupported declaration modifier {inner.getKind} " ++
                  "in specification")
              inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
                currNs openDecls inner isModule
          else
            unless isAllowedSpecDeclModifierKind isModule ck do
              fail s!"unsupported declaration modifier {ck} in specification"
            inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
              currNs openDecls child isModule
    else if k == ``Parser.Command.declaration then
      unless args.size == 2 &&
          args[0]!.isOfKind ``Parser.Command.declModifiers do
        fail "unsupported declaration shape in specification"
      let declKind := args[1]!.getKind
      unless allowedSpecDeclarationKinds.contains declKind do
        fail s!"unsupported declaration kind {declKind} in specification"
      if let some id := declarationIdent? s then
        if hasUnsafeRecComponent id then
          fail s!"disallowed _unsafe_rec declaration {id} in specification"
        discard <| checkSpecDeclNamespace currNs id parserEnv
      for child in args do
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls child isModule
    else if k == ``Parser.Command.mutual then
      unless args.size == 3 &&
          args[1]!.getArgs.all (isAllowedSpecNestedCommand ·.getKind) do
        fail "unsupported mutual-block shape in specification"
      let mut mutEnv := parserEnv
      let mut mutOpen := openDecls
      let mut mutCmds := commandLikeKinds
      let mut mutTacs := tacticLikeKinds
      for child in args[1]!.getArgs do
        inspectSpecSyntax mutCmds mutTacs mutEnv currNs mutOpen child isModule
        if child.isOfKind ``Parser.Command.open then
          let (nextEnv, nextOpen) ←
            validateSpecOpenDecl currNs mutOpen mutEnv child[1]
          mutEnv := nextEnv
          mutOpen := nextOpen
          if openActivatesScoped child[1] then
            let (nc, nt) ← collectSpecParserSets mutEnv
            mutCmds := nc
            mutTacs := nt
    else if k == ``Parser.Command.in then
      unless args.size == 3 do
        fail "unsupported command-wrapper shape in specification"
      unless allowedSpecInLhsKinds.contains args[0]!.getKind do
        fail s!"unsupported command on LHS of `in`: {args[0]!.getKind}"
      unless isAllowedSpecNestedCommand args[2]!.getKind do
        fail s!"unsupported command inside `in`: {args[2]!.getKind}"
      inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
        currNs openDecls args[0]! isModule
      let (tmpEnv, tmpOpen) ←
        if args[0]!.isOfKind ``Parser.Command.open then
          validateSpecOpenDecl currNs openDecls parserEnv args[0]![1]
        else
          pure (parserEnv, openDecls)
      let (tmpCmds, tmpTacs) ←
        if args[0]!.isOfKind ``Parser.Command.open &&
            openActivatesScoped args[0]![1] then
          collectSpecParserSets tmpEnv
        else
          pure (commandLikeKinds, tacticLikeKinds)
      inspectSpecSyntax tmpCmds tmpTacs tmpEnv currNs tmpOpen args[2]! isModule
    else if k == ``Parser.Command.open then
      unless args.size == 2 do
        fail "unsupported open command shape in specification"
      discard <| validateSpecOpenDecl currNs openDecls parserEnv args[1]!
    else if k == ``Parser.Term.open then
      unless args.size == 4 do
        fail "unsupported term open shape in specification"
      let (tmpEnv, tmpOpen) ←
        validateSpecOpenDecl currNs openDecls parserEnv args[1]!
      let (tmpCmds, tmpTacs) ←
        if openActivatesScoped args[1]! then
          collectSpecParserSets tmpEnv
        else
          pure (commandLikeKinds, tacticLikeKinds)
      inspectSpecSyntax tmpCmds tmpTacs tmpEnv currNs tmpOpen args[3]! isModule
    else if k == ``Parser.Command.export then
      validateSpecExport currNs openDecls args
    else if k == ``Parser.Term.attrInstance then
      validateSpecAttrInstance args isModule
    else if k == ``Parser.Command.eraseAttr then
      let attrName := args[1]?.map Syntax.getId |>.getD .anonymous
      unless allowedSpecEraseAttrs.contains attrName do
        fail s!"unsupported attribute removal {attrName} in specification"
    else if k == ``Parser.Command.deriving then
      unless args.size == 6 && args[1]!.isOfKind nullKind &&
          args[1]!.getArgs.isEmpty do
        fail "unsupported deriving command modifier in specification"
      for child in args do
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls child isModule
    else if k == ``Parser.Command.derivingClass then
      unless args.size == 2 && args[0]!.isOfKind nullKind &&
          args[0]!.getArgs.isEmpty do
        fail "unsupported deriving modifier in specification"
      let cls := args[1]!.getId
      unless allowedSpecDerivingClasses.contains cls do
        fail s!"unsupported deriving class {cls} in specification"
    else if k == ``Parser.Command.set_option then
      validateSpecSetOption args
    else if k == ``Parser.Term.set_option then
      validateSpecSetOption args
      inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
        currNs openDecls args[5]! isModule
    else if k == `Lean.Parser.Tactic.decide then
      validateSpecDecideTactic args
    else
      for child in args do
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls child isModule

/-- Update lexical scope state `(parserEnv, scopes)` after validating a
specification command `stx`. -/
partial def applySpecScope (parserEnv : Environment)
    (scopes : List ParseScope) (stx : Syntax) :
    IO (Environment × List ParseScope) := do
  let k := stx.getKind
  if k == ``Parser.Command.namespace then
    pushSpecScopes true stx[1].getId parserEnv scopes
  else if k == ``Parser.Command.section then
    if stx[2].isNone then
      let top := scopes.head!
      let parserEnv := Parser.parserExtension.pushScope parserEnv
      return (parserEnv, { top with header := "" } :: scopes)
    else
      pushSpecScopes false stx[2][0].getId parserEnv scopes
  else if k == ``Parser.Command.end then
    let header? := if stx[1].isNone then none else some stx[1][0].getId
    let endSize := match header? with
      | none => 1
      | some n => n.getNumParts
    if scopes.length <= 1 then
      fail "unexpected `end` command with no active scope"
    match header? with
    | none =>
      if scopes.head!.header != "" then
        fail s!"missing scope name `{scopes.head!.header}` after `end`"
    | some header =>
      if endSize >= scopes.length then
        fail s!"`end {header}` closes more scopes than are open"
      let expected := nameOfParseScopes scopes endSize
      if expected != header then
        fail s!"mismatched `end {header}` (expected `{expected}`)"
    let mut env := parserEnv
    for _ in [:endSize] do
      env := Parser.parserExtension.popScope env
    return (env, scopes.drop endSize)
  else if k == ``Parser.Command.open then
    let top := scopes.head!
    let (nextEnv, nextOpen) ←
      validateSpecOpenDecl top.currNamespace top.openDecls parserEnv stx[1]
    return (nextEnv, { top with openDecls := nextOpen } :: scopes.tail!)
  else if k == ``Parser.Command.in then
    let top := scopes.head!
    let tmpEnv := Parser.parserExtension.pushScope parserEnv
    let (tmpEnv, tmpScopes) ← applySpecScope tmpEnv (top :: scopes) stx[0]
    let (tmpEnv, _) ← applySpecScope tmpEnv tmpScopes stx[2]
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.mutual then
    let top := scopes.head!
    let mut tmpEnv := Parser.parserExtension.pushScope parserEnv
    let mut tmpScopes := top :: scopes
    for child in stx[1].getArgs do
      (tmpEnv, tmpScopes) ← applySpecScope tmpEnv tmpScopes child
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.declaration then
    match declarationIdent? stx with
    | some id =>
      let env ← checkSpecDeclNamespace scopes.head!.currNamespace id parserEnv
      return (env, scopes)
    | none => return (parserEnv, scopes)
  else
    return (parserEnv, scopes)

/-- Encode a `Name` unambiguously for `"sysroot-consts"` and `"target-consts"`
(`#<num>` for numeric components; `\\` escapes `\\`, `.`, and `#` inside
string components). -/
def encodeCanonName : Name → String
  | .anonymous => ""
  | .str p s =>
    let esc := s.foldl (init := "") fun acc c =>
      if c == '\\' || c == '.' || c == '#' then
        (acc.push '\\').push c
      else acc.push c
    match p with
    | .anonymous => esc
    | _ => s!"{encodeCanonName p}.{esc}"
  | .num p i =>
    match p with
    | .anonymous => s!"#{i}"
    | _ => s!"{encodeCanonName p}.#{i}"

/-- Parse and validate all commands in a `TargetRole::Specification` module
against the authenticated `Init`/`Std` parser environment without elaborating
any command. -/
partial def parseAndInspectSpecCommands (ctx : Parser.InputContext)
    (commandLikeKinds tacticLikeKinds : NameSet) (parserEnv : Environment)
    (scopes : List ParseScope) (moduleName : Name)
    (state : Parser.ModuleParserState) (messages : MessageLog)
    (isModule : Bool := false) : IO Unit := do
  let previous := state.pos
  let top := scopes.head!
  let pmctx : Parser.ParserModuleContext := {
    env := parserEnv
    options := {}
    currNamespace := top.currNamespace
    openDecls := top.openDecls
  }
  let (stx, nextState, nextMessages) :=
    Parser.parseCommand ctx pmctx state messages
  if nextMessages.hasErrors || nextState.recovering then
    fail s!"command parser error in specification {moduleName}"
  if stx.isOfKind ``Parser.Command.eoi then
    return ()
  if nextState.pos <= previous then
    throw <| IO.userError "parser made no progress"
  unless allowedSpecCommandKinds.contains stx.getKind do
    fail s!"unsupported command {stx.getKind} in specification {moduleName}"
  inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
    top.currNamespace top.openDecls stx isModule
  let (nextEnv, nextScopes) ← applySpecScope parserEnv scopes stx
  let (nextCmds, nextTacs) ←
    if stx.isOfKind ``Parser.Command.namespace ||
        stx.isOfKind ``Parser.Command.end ||
        (stx.isOfKind ``Parser.Command.open &&
          openActivatesScoped stx[1]) then
      collectSpecParserSets nextEnv
    else
      pure (commandLikeKinds, tacticLikeKinds)
  parseAndInspectSpecCommands ctx nextCmds nextTacs nextEnv nextScopes
    moduleName nextState nextMessages isModule

/-- Execute batched fail-closed `"spec-preflight"` across all
`TargetRole::Specification` modules against the authenticated `Init` + `Std`
parser environment (`extensions := true`, zero target `.olean`s loaded). -/
def preflightSpecs (j : Json) (foundation : Array Name) : IO Json := do
  let libraries ← names j "libraries"
  let sources ← field (α := Array (String × String)) j "sources"
  let env ← importEnv j (foundation ++ libraries) true
  validateGraph j env
  let (commandLikeKinds, tacticLikeKinds) ← collectSpecParserSets env
  let mut checked : Array Json := #[]
  for (modStr, pathStr) in sources do
    let moduleName := modStr.toName
    let text ← IO.FS.readFile pathStr
    let ctx := Parser.mkInputContext text pathStr
    let (header, initial, log) ← Parser.parseHeader ctx
    if log.hasErrors || initial.recovering then
      fail s!"header parser error in specification {moduleName}"
    let isModule := Elab.HeaderSyntax.isModule header
    inspectHeaderSyntax header.raw (requirePrelude := false)
    let imports := Elab.HeaderSyntax.imports header
    validateTargetImports moduleName.toString imports (allowModule := isModule)
    let rootScope : ParseScope :=
      { header := "", currNamespace := .anonymous, openDecls := [] }
    parseAndInspectSpecCommands ctx commandLikeKinds tacticLikeKinds env
      [rootScope] moduleName initial log (isModule := isModule)
    checked := checked.push (toJson moduleName)
  return Json.mkObj [("checked", .arr checked)]

/-- Collect `[moduleName, [encodedConstName, ...]]` mappings across the
authenticated `Init`/`Std` sysroot closure (`loadExts := false`, zero target
`.olean`s loaded). -/
def collectSysrootConsts (j : Json) (foundation : Array Name) : IO Json := do
  let libraries ← names j "libraries"
  let env ← importEnv j (foundation ++ libraries) false
  validateGraph j env
  let mut byModule : Std.HashMap String (Array String) := {}
  for (constName, _) in env.constants do
    if let some idx := env.getModuleIdxFor? constName then
      if let some modName := env.header.moduleNames[idx.toNat]? then
        let modStr := modName.toString
        let arr := byModule.getD modStr #[]
        byModule :=
          byModule.insert modStr (arr.push (encodeCanonName constName))
  let entries := byModule.toArray.qsort (fun (a, _) (b, _) => a < b)
  let jsonEntries := entries.map fun (modStr, consts) =>
    Json.arr #[toJson modStr, toJson consts]
  return Json.mkObj [("sysrootConsts", .arr jsonEntries)]

/-- Return `true` when `ci` is the safe `partial` compiler auxiliary
`p._unsafe_rec` that Lean pairs with a well-founded definition `p`: a
`.defnInfo` with `isPartial` and not `isUnsafe`, whose parent `p` is a safe,
non-`partial` `.defnInfo` declared in the same module `m` (mirroring
`TrustedBoundary.pairedSpecUnsafeRecParent?`). -/
def isPairedUnsafeRec (env : Environment) (m : Name) (ci : ConstantInfo) :
    Bool :=
  if !ci.isPartial || ci.isUnsafe || !(ci matches .defnInfo _) then false
  else match ci.name with
    | .str parent "_unsafe_rec" =>
      match env.find? parent, env.getModuleIdxFor? parent with
      | some parentCi@(.defnInfo _), some idx =>
        env.header.moduleNames[idx.toNat]? == some m &&
          !parentCi.isUnsafe && !parentCi.isPartial
      | _, _ => false
    | _ => false

/-- Fail closed when module `m`'s compiled `isModule` header flag `actual`
differs from the `"isModule"` expectation `expected` that `cargo-anneal`
derived from the staged source header. -/
private def validateTargetModuleIsModuleConsistency (m : Name)
    (actual expected : Bool) : IO Unit := do
  if !expected && actual then
    fail s!"module-system artifact unsupported in {m}"
  else if expected && !actual then
    fail s!"non-module artifact mismatch in {m}"

private def oleanHeaderSize : Nat := 88

private def readUInt64LE (bytes : ByteArray) (off : Nat) : Nat :=
  (bytes.get! off).toNat +
  ((bytes.get! (off + 1)).toNat <<< 8) +
  ((bytes.get! (off + 2)).toNat <<< 16) +
  ((bytes.get! (off + 3)).toNat <<< 24) +
  ((bytes.get! (off + 4)).toNat <<< 32) +
  ((bytes.get! (off + 5)).toNat <<< 40) +
  ((bytes.get! (off + 6)).toNat <<< 48) +
  ((bytes.get! (off + 7)).toNat <<< 56)

private def alignUp64K (n : Nat) : Nat :=
  ((n + 65535) / 65536) * 65536

/-- Pure, bounds-checked read of `ModuleData.isModule` from the root object of
a primary `.olean` v2 file without invoking `CompactedRegion.read` or `mmap`. -/
private def parsePrimaryOleanIsModule (m : Name) (bytes : ByteArray)
    (baseAddr : Nat) : IO Bool := do
  if bytes.size < oleanHeaderSize + 8 then
    fail s!"truncated olean root pointer in {m}"
  let rootPtr := readUInt64LE bytes oleanHeaderSize
  if rootPtr < baseAddr then
    fail s!"invalid olean root pointer in {m}"
  let rootOff := rootPtr - baseAddr
  if rootOff < oleanHeaderSize + 8 || rootOff + 8 > bytes.size then
    fail s!"out-of-bounds olean root object in {m}"
  let numObjs := (bytes.get! (rootOff + 6)).toNat
  let tag := (bytes.get! (rootOff + 7)).toNat
  let scalarOff := rootOff + 8 + numObjs * 8
  if tag != 0 || numObjs != 5 || scalarOff >= bytes.size then
    fail s!"invalid olean ModuleData layout in {m}"
  let flag := bytes.get! scalarOff
  if flag == 0 then
    return false
  else if flag == 1 then
    return true
  else
    fail s!"invalid olean isModule flag in {m}"

/-- Validate `.olean*` / `.ir` artifact part counts for a target module `m`:
non-module targets accept a single monolithic `.olean`, while Lean 4 `module`
targets accept `.olean` plus optional `.olean.server` / `.olean.private`
sidecars (never `.ir`). -/
def validateTargetArtifactParts (m : Name) (oleanPartCount : Nat)
    (irEmpty isModuleArtifact : Bool) : IO Unit := do
  let partsOk :=
    if isModuleArtifact then
      oleanPartCount >= 1 && oleanPartCount <= 3 && irEmpty
    else
      oleanPartCount == 1 && irEmpty
  unless partsOk do
    fail s!"companion artifact parts unsupported in {m}"

/-- Validate `.olean*` binary headers, companion base-address chaining, and
primary-part `isModule` policy before `importEnv` mmaps `.olean.server` or
`.olean.private` companion regions via `CompactedRegion.read`. -/
def validateTargetArtifactPreImport (m : Name) (art : ImportArtifacts)
    (expectedIsModule : Bool) : IO Unit := do
  let parts := art.oleanParts true
  validateTargetArtifactParts m parts.size art.irParts.isEmpty expectedIsModule
  let mut prefix0 : Option ByteArray := none
  let mut prevEndAligned : Option Nat := none
  let mut primaryIsMod : Option Bool := none
  for partPath in parts do
    let bytes ← try
      IO.FS.readBinFile partPath
    catch e =>
      throw <| IO.userError
        s!"missing or unreadable artifact part {partPath} for {m}: {e}"
    if bytes.size < oleanHeaderSize then
      fail s!"truncated olean header in {m}"
    let magicOk :=
      bytes.get! 0 == 'o'.toNat.toUInt8 &&
      bytes.get! 1 == 'l'.toNat.toUInt8 &&
      bytes.get! 2 == 'e'.toNat.toUInt8 &&
      bytes.get! 3 == 'a'.toNat.toUInt8 &&
      bytes.get! 4 == 'n'.toNat.toUInt8 &&
      bytes.get! 5 == 2
    unless magicOk do
      fail s!"invalid olean v2 header in {m}"
    let hdrPrefix := bytes.extract 0 80
    let baseAddr := readUInt64LE bytes 80
    match prefix0, prevEndAligned with
    | none, _ =>
      let isMod ← parsePrimaryOleanIsModule m bytes baseAddr
      primaryIsMod := some isMod
      prefix0 := some hdrPrefix
      prevEndAligned := some (alignUp64K (baseAddr + bytes.size))
    | some expectedPrefix, some expectedBase =>
      unless hdrPrefix == expectedPrefix do
        fail s!"mismatched olean companion header in {m}"
      unless baseAddr == expectedBase do
        fail s!"mismatched olean companion base address in {m}"
      prevEndAligned := some (alignUp64K (baseAddr + bytes.size))
    | _, _ =>
      fail s!"inconsistent olean companion sequence in {m}"
  let some isMod := primaryIsMod
    | fail s!"missing primary olean artifact for {m}"
  validateTargetModuleIsModuleConsistency m isMod expectedIsModule
  validateTargetArtifactParts m parts.size art.irParts.isEmpty isMod

/-- Return `true` when `a` and `b` agree on kind, name, universe parameters,
type, mutual block, safety, and value (including theorem proofs and `opaque`
bodies), which covers every pair of declarations Lean's import admits under
one name (theorems and axioms). Lean 4.34.1's `ConstantInfo` has no `BEq`. -/
def sameConstantInfo (a b : ConstantInfo) : Bool :=
  let kind : ConstantInfo → Nat
    | .axiomInfo _ => 0 | .defnInfo _ => 1 | .thmInfo _ => 2
    | .opaqueInfo _ => 3 | .quotInfo _ => 4 | .inductInfo _ => 5
    | .ctorInfo _ => 6 | .recInfo _ => 7
  kind a == kind b && a.name == b.name && a.levelParams == b.levelParams &&
    a.type == b.type && a.all == b.all && a.isUnsafe == b.isUnsafe &&
    a.isPartial == b.isPartial &&
    a.value? (allowOpaque := true) == b.value? (allowOpaque := true)

/-- Return `true` when `n`'s last component is a suffix Lean uses for lazily
realized equation-style theorems (`eq_<n>`, `eq_def`, `eq_unfold`,
`else_eq`, `induct`, `induct_unfolding`, `fun_cases`, `fun_cases_unfolding`,
`congr_simp`, `hinj`, `hcongr_<n>`, `congr_eq_<n>`), which independent modules
may each realize with an identical header. -/
def isRealizedTheoremName (n : Name) : Bool :=
  match n with
  | .str _ s =>
    let digitsAfter (pfx : String) : Bool :=
      match s.dropPrefix? pfx with
      | some rest => !rest.isEmpty && rest.all Char.isDigit
      | none => false
    ["eq_def", "eq_unfold", "else_eq", "induct", "induct_unfolding",
      "fun_cases", "fun_cases_unfolding", "congr_simp", "hinj"].contains s ||
      digitsAfter "eq_" || digitsAfter "hcongr_" || digitsAfter "congr_eq_"
  | _ => false

/-- Collect, for every retained non-`Proof` target module in `"targets"`
(`[moduleName, isModule]` pairs), `[moduleName, [encodedConstName, ...],
[encodedPairedName, ...], [encodedOverrideName, ...]]` (`"target-consts"`).

Before importing, each target's `.olean*` parts pass
`validateTargetArtifactPreImport` against the `isModule` expectation that
`cargo-anneal` derived from the staged header. The request's `"artifacts"`
name only the admitted foundation and library `.olean`s plus the compiled
`Model`, `Capture`, `Specification`, and `Expected` `.olean`s; `Proof`
`.olean`s are never listed or mounted. `loadExts := false` skips module
initializers and extension callbacks.

Each inventory comes from the module's own `ModuleData` (`constNames` must
equal `constants.map ConstantInfo.name` without duplicates), so
compiler-generated constants (anonymous and `deriving` instances, structure
constructors/projections, `where`/`let rec` auxiliaries, matchers, and
`private` declarations) are attributed to their defining module. Lean's
import admits two modules declaring theorems with equal headers and then
keeps the later module's proof under the earlier module's index. Every
target constant must therefore equal the stored constant, and a target
constant whose name another loaded module also declares is rejected unless
it is a lazily realized equation-style theorem (`isRealizedTheoremName`)
equal to the owning module's, which is then reported under the owning
module only. Any `unsafe` target constant is
rejected. The second list names paired `p._unsafe_rec` auxiliaries
(`isPairedUnsafeRec`), which are `partial`; the third names the module's
`@[implemented_by]`, `@[extern]`, and `@[csimp]` subjects, read from
`finalizeImport`-populated module entries as `"target-audit"` does. -/
def collectTargetConsts (j : Json) (foundation : Array Name) : IO Json := do
  let libraries ← names j "libraries"
  let targetPairs ← field (α := Array (String × Bool)) j "targets"
  let targets := targetPairs.map (·.1.toName)
  if targets.isEmpty then
    fail "target-consts requires at least one target module"
  let targetSet : NameSet :=
    targets.foldl (init := {}) fun acc t => acc.insert t
  unless targetSet.size == targets.size do
    fail "duplicate target-consts module"
  for t in targets do
    if foundation.contains t || libraries.contains t then
      fail s!"target-consts module {t} collides with sysroot module"
  let arts ← artifacts j
  for (tStr, expectedIsModule) in targetPairs do
    let t := tStr.toName
    let some art := arts.find? t
      | fail s!"missing target artifacts for {t}"
    validateTargetArtifactPreImport t art expectedIsModule
  let env ← importEnv j (foundation ++ libraries ++ targets) false
  validateGraph j env
  let mut entries : Array Json := #[]
  for t in targets do
    let some idx := env.header.moduleNames.idxOf? t
      | fail s!"target module {t} missing from imported environment"
    let some data := env.header.moduleData[idx]?
      | throw <| IO.userError s!"module data index out of range for {t}"
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid target inventory {t}"
    let mut seen : NameSet := {}
    let mut all : Array String := #[]
    let mut paired : Array String := #[]
    for ci in data.constants do
      if seen.contains ci.name then
        fail s!"duplicate target declaration {ci.name}"
      seen := seen.insert ci.name
      if ci.isUnsafe then
        fail s!"target module {t} declares unsafe constant {ci.name}"
      -- A later equal-header theorem replaces the stored constant while
      -- `const2ModIdx` keeps the first module, so the stored constant must
      -- be exactly `ci`, and an admitted collision must equal the owner's.
      unless (env.find? ci.name).any (sameConstantInfo ci) do
        fail s!"target constant {ci.name} of {t} differs from the stored one"
      let owner := env.getModuleIdxFor? ci.name |>.map (·.toNat)
      if owner != some idx then
        let other := owner.bind (env.header.moduleNames[·]?)
        let ownerCi := owner.bind (env.header.moduleData[·]?) |>.bind
          fun d => d.constants.find? (·.name == ci.name)
        unless isRealizedTheoremName ci.name && (ci matches .thmInfo _) &&
            ownerCi.any (sameConstantInfo ci) do
          fail s!"constant {ci.name} declared by {t} and {other}"
        continue
      let enc := encodeCanonName ci.name
      all := all.push enc
      if isPairedUnsafeRec env t ci then
        paired := paired.push enc
    let mut overrides : Array String := #[]
    for (declName, _) in
        Compiler.implementedByAttr.ext.getModuleEntries env idx do
      overrides := overrides.push (encodeCanonName declName)
    for (declName, _) in externAttr.ext.getModuleEntries env idx do
      overrides := overrides.push (encodeCanonName declName)
    for entry in Compiler.CSimp.ext.ext.getModuleEntries env idx do
      let e := match entry with
        | .global e | .scoped _ e => e
      overrides := overrides.push (encodeCanonName e.fromDeclName)
    entries := entries.push <| Json.arr #[toJson t.toString,
      toJson (all.qsort (· < ·)), toJson (paired.qsort (· < ·)),
      toJson (overrides.qsort (· < ·))]
  return Json.mkObj [("targetConsts", .arr entries)]

/-- Dispatch a runtime preflight request (`"headers"`, `"spec-preflight"`,
`"resolve-imports"`, `"sysroot-consts"`, or `"target-consts"`). -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  let sysrootStr ← field (α := String) j "sysroot"
  match mode with
  | "headers" =>
    initHermeticSearchPath sysrootStr
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectHeader n.toName p
    return Json.mkObj [("headers", .arr headers)]
  | "spec-preflight" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    preflightSpecs j foundation
  | "resolve-imports" =>
    initHermeticSearchPath sysrootStr
    let mods ← names j "modules"
    let env ← importSysrootEnv mods
    let entries := (env.header.modules.zip env.header.moduleData).qsort
      fun (m₁, _) (m₂, _) => m₁.module.toString < m₂.module.toString
    let sortedGraph := Json.mkObj <| entries.toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)
    return Json.mkObj [("graph", sortedGraph)]
  | "sysroot-consts" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    collectSysrootConsts j foundation
  | "target-consts" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    collectTargetConsts j foundation
  | _ => throw <| IO.userError s!"unknown spec-preflight mode {mode}"

end SpecPreflight

/-- Run the runtime preflight inspector via `lean --run`, writing a JSON
envelope to `<res.json>` and returning exit code `0` (success), `1` (policy
rejection), or `2` (operational failure). -/
def main (args : List String) : IO UInt32 := do
  let [request, output] := args
    | IO.eprintln "expected request and result files"; return 2
  try
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
    let result ← SpecPreflight.run j
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
