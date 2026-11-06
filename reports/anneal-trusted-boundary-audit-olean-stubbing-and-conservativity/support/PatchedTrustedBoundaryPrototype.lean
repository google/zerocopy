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

Pinned to Lean 4.34.1. This file implements the Lean side of Anneal's
mechanical trust-boundary enforcement, paired with the Rust orchestrator in
`trusted/cargo-anneal/src/audit.rs`.

## Security Model and Trust Tiers

Anneal's soundness promise is that `cargo anneal verify` and
`cargo anneal audit-repo` never report that a crate or repository is verified
unless the Lean 4 kernel has checked a proof of `Trusted.CrateTheorem Mir.crate`
that depends only on sound axioms (`{Classical.choice, Quot.sound, propext}`)
and on TCB components permitted by the active release channel and crate trust
policy.

Code in an Anneal verification run falls into four categories:

1. **Foundation (`Init.*` locked by `trusted/lean/foundation-lock.json`):**
   The pinned Lean 4.34.1 prelude and core library modules, together with any
   admitted `toolchainLibrary` (`Init.*` and `Std.*`) modules from the locked
   toolchain. Only the three standard axioms listed in `foundation-lock.json`
   are permitted; `sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceBool`, and
   `Lean.ofReduceNat` are excluded from the axiom allowlist.
2. **Vetted TCB (`trusted/lean/`, marked `@[vetted]`):**
   Primitive semantic definitions and theorem envelopes audited against the
   Rust Reference and enabled on both `alpha` and `stable` release channels.
3. **Candidate-Trusted TCB (`trusted/lean/`, marked `@[candidate <feature>]`):**
   TCB definitions (and the `rustc_capture` lowering constructors) that could
   cause a false verification result if buggy, but have not yet completed
   line-by-line Rust Reference auditing. Candidate features are disabled by
   default (`VettedOnly`), unconditionally forbidden on the `stable` release
   channel, and usable on `alpha` only when the target crate explicitly opts in.
4. **Untrusted (`theory/` and `.anneal/Proof.lean`):**
   Derived lemmas, simulation proofs, the plan-guided symbolic evaluator
   (`Anneal.FunctionalTranslation`), and synthesized per-crate proof scripts.
   Bugs in untrusted code must never cause a false positive.

## Threat Model and Two-Phase Enforcement (`"preflight"` and `"audit"`)

Lean's elaborator is not a sandbox: elaborating an arbitrary `.lean` file can
execute `IO` side effects (`#eval`, `run_tac`, `by_elab`), register parser or
elaborator extensions, disable kernel typechecking (`set_option
debug.skipKernelTC true`), attach compiler overrides (`@[extern]`,
`@[implemented_by]`, `@[csimp]`), or use `unsafe t` inside a safe definition
(which elaborates to a safe `opaque` auxiliary constant backed by an unchecked
`@[implemented_by]` hook). Moreover, even in a pure environment with zero
custom axioms, an untrusted proof script could prove a trivial theorem (such as
`theorem verify_crate : True := trivial`) or redefine `Mir.crate` unless
module-origin boundaries and exact theorem types are checked in the compiled
`.olean` environment.

To close both elaboration-time and post-elaboration threat vectors, this
inspector operates in two isolated phases:

- **Phase 1 (`"preflight"`):** Runs *before* Lean compiles any project or crate
  `.lean` file. The inspector loads only `foundation ++ toolchainLibrary` so
  project files cannot inject syntax or macro extensions, parses each `.lean`
  source file with `Parser.parseHeader` and `Parser.parseCommand`, rejects any
  command, term, tactic, or attribute outside a closed pure allowlist, and
  extracts the file's declared imports and `@[vetted]` /
  `@[candidate <feature>]` declaration table.
- **Phase 2 (`"audit"`):** Runs *after* `audit.rs` compiles the admitted
  modules in topological order with `-DElab.async=false` and
  `-Ddebug.skipKernelTC=false`. The inspector loads all compiled `.olean`
  artifacts with `trustLevel := 0`, `plugins := #[]`, `loadExts := false` (so
  no `[init]` extensions execute), and `level := .private` (so `private`
  declarations are visible), and verifies five properties:
  1. **Inventory completeness and provenance (`verifyAndCollectLocals`):**
     Every constant in `env.checked` belongs to an admitted module's
     inventory, matches its stored declaration (or `sameRealizedThmHeader` for
     duplicate on-demand `.thmInfo` declarations across diamond imports), and—
     for all non-base modules—is neither `isUnsafe`, `isAxiom`, nor an
     unverified `isPartial` declaration (permitting only `<base>._unsafe_rec`
     compiler companions whose `<base>` in the same module is a `.defnInfo`
     with `safety == .safe`).
  2. **Vetted vs. candidate non-contamination
     (`checkTrustedNonContamination`):**
     `@[vetted]` types never reference `@[candidate]` constants, and
     `@[vetted]` bodies reference `@[candidate <feat>]` constants only inside
     `Trusted.candidate "<feat>" (...)` branch guards coupled one-to-one with
     pattern-matching on a `@[vetted]` inductive's `@[candidate <feat>]`
     constructors.
  3. **Crate theorem envelope and axiom closure (`closure`):**
     - When auditing crate targets (`crates`), `<mirMod>.crate : Trusted.Crate`
       is a definition originating in `<mirMod>` and `<proofMod>.verify_crate :
       Trusted.CrateTheorem <mirMod>.crate` is a theorem originating in
       `<proofMod>`.
     - Every reachable axiom across all non-base declarations belongs to the
       locked `foundation` axiom allowlist (`{Classical.choice, Quot.sound,
       propext}`).
  4. **Active candidate feature reachability
     (`collectActiveCandidateFeatures`):**
     Traverses the crate's dependency closure (`Mir` and `Proof`), releasing a
     `Trusted.candidate "<feat>"` branch if and only if a `candidate:<feat>`
     constant or constructor is reached, and reports the active candidate
     features for policy enforcement by `audit.rs`.
  5. **Independent kernel replay (`base.toKernelEnv.replay replayLocals`):**
     Replays the reachable non-base declaration closure from scratch through
     Lean's kernel typechecker on top of a freshly imported
     `foundation ++ toolchainLibrary` environment.
-/

open Lean

namespace TrustedBoundary

/-- Throw a policy-rejection error prefixed with `"policy:"` so `main` and
    `audit.rs` distinguish policy violations (exit code 1) from operational or
    I/O failures (exit code 2). -/
def fail (message : String) : IO α := throw <| IO.userError s!"policy:{message}"

/-- Extract and deserialize required field `key` from JSON object `j`. -/
def field [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

/-- Extract an array of dot-separated Lean `Name`s from JSON field `key`. -/
def names (j : Json) (key : String) : IO (Array Name) := do
  return (← field (α := Array String) key (j := j)).map String.toName

/-- Extract an optional array of dot-separated Lean `Name`s from JSON field
    `key`, defaulting to `#[]` when `key` is omitted. -/
def namesOpt (j : Json) (key : String) : IO (Array Name) := do
  match j.getObjValAs? (Array String) key with
  | .ok arr => return arr.map String.toName
  | .error _ => return #[]

/-- Extract the target `(mirModule, proofModule)` pairs from `j`.
    Supports both the multi-crate `"crates": [["Upstream.Mir",
    "Upstream.Proof"], ...]` field and the single-crate `"hasCrate": Bool`
    field (`#[(`Mir, `Proof)]`). -/
def crateTargets (j : Json) : IO (Array (Name × Name)) := do
  match j.getObjValAs? (Array (String × String)) "crates" with
  | .ok pairs => return pairs.map fun (m, p) => (m.toName, p.toName)
  | .error _ =>
    let hasCrate ← field (α := Bool) j "hasCrate"
    return if hasCrate then #[(`Mir, `Proof)] else #[]

/-- Build the explicit module-to-artifact map (`NameMap ImportArtifacts`) from
    the runner's `"artifacts"` table, rejecting duplicate module entries so
    `importModules` resolves every module to the exact runner-admitted `.olean`
    paths without consulting ambient search paths. -/
def artifacts (j : Json) : IO (NameMap ImportArtifacts) := do
  let entries ← field (α := Array (String × Array (Array String))) j "artifacts"
  let mut result := {}
  for (n, parts) in entries do
    if (result.find? n.toName).isSome then fail s!"duplicate artifact module {n}"
    result := result.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  return result

/-- Serialize the compiled module header import DAG of `env` as a JSON object
    mapping each module name to its array of `Import` edges. -/
def graph (env : Environment) : Json :=
  Json.mkObj <| (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
    (m.module.toString, toJson d.imports)

/-- Import `roots` from the explicit artifact map in `j` at `trustLevel := 0`.

    - `extensions` is `true` only during `"preflight"` when importing the
      locked `foundation` (`Init.*`) and `toolchainLibrary` modules, because
      Lean's built-in command and tactic parsers are registered as environment
      extensions in `Init` and `Std`. During `"audit"`, `extensions` is `false`
      (`loadExts := false`), ensuring that project `.olean` files cannot
      execute `[init]` initializers or mutate environment extensions when
      loaded.
    - `level := .private` and `env.setExporting false` load and expose private
      declarations (such as compiler-generated `_match_1` splitters and
      `private` helpers) so they cannot hide from inventory, axiom, or
      non-contamination checks. -/
def importEnv (j : Json) (roots : Array Name) (extensions := false) : IO Environment := do
  let arts ← artifacts j
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => {module := n}) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

/-- Verify that the import DAG recorded inside the loaded `.olean` headers of
    `env` exactly matches the `"graph"` admitted by `audit.rs` during
    `"preflight"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do fail "compiled module/import DAG differs from admitted DAG"

/-- Verify during `"preflight"` that every `foundation` module in `env` matches
    the locked `"graph"` from `foundation-lock.json`, and that every loaded
    module in `env` belongs to `baseMods` (`foundation ++ toolchainLibrary`). -/
def validatePreflightGraph (j : Json) (env : Environment)
    (foundation : Array Name) (baseMods : Array Name) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  let actual := graph env
  if baseMods.size == foundation.size then
    unless actual == expected do fail "compiled module/import DAG differs from admitted DAG"
  else
    let baseSet : NameSet := .ofList baseMods.toList
    for m in env.header.modules, d in env.header.moduleData do
      unless baseSet.contains m.module do fail s!"foreign toolchain module {m.module}"
      for imp in d.imports do
        unless baseSet.contains imp.module do
          fail s!"foreign toolchain import {imp.module} in {m.module}"
    for fMod in foundation do
      let expImps ← field (α := Json) expected fMod.toString
      let actImps ← field (α := Json) actual fMod.toString
      unless actImps == expImps do
        fail s!"compiled foundation module {fMod} import DAG differs from admitted DAG"

/-- Closed allowlist of top-level command syntax kinds permitted in any
    non-foundation `.lean` source file (`Trusted`, `Anneal`, `Mir`, `Proof`).
    Commands that execute code or extend the parser/elaborator (`#eval`,
    `#check`, `macro`, `elab`, `syntax`, `initialize`, `builtin_initialize`,
    `notation`, `infix`, etc.) are excluded; the single surface macro
    `Trusted.expandTrustDeclaration` is admitted via its `@[macro ...]`
    attribute on a standard `Parser.Command.declaration`. -/
def commandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.section,
  ``Parser.Command.end, ``Parser.Command.universe, ``Parser.Command.variable,
  ``Parser.Command.open, ``Parser.Command.export, ``Parser.Command.mutual,
  ``Parser.Command.in, ``Parser.Command.attribute, ``Parser.Command.moduleDoc]

/-- Return `true` if `s` or any syntax descendant is an atom equal to
    `value`. -/
def atomWithin (s : Syntax) (value : String) : Bool :=
  (s.find? fun x => x.isAtom && x.getAtomVal == value).isSome

/-- Return `true` if `s` or any syntax descendant is an identifier equal to
    `value`. -/
def identWithin (s : Syntax) (value : Name) : Bool :=
  (s.find? fun x => x.isIdent && x.getId == value).isSome

/-- Closed allowlist of non-trust attributes permitted on declarations.
    Compiler-override and metaprogramming attributes (`@[extern]`,
    `@[implemented_by]`, `@[csimp]`, `@[init]`, `@[app_unexpander]`, etc.) are
    rejected because they can alter runtime or elaboration behavior outside the
    kernel. -/
def allowedAttributeNames : List Name := [
  `simp, `instance, `reducible, `semireducible, `irreducible]

/-- Closed set of subsystem feature identifiers allowed in
    `@[candidate <feature>]` attributes and `Trusted.candidate "<feature>"`
    term guards. Must match `VALID_CANDIDATE_FEATURES` in `audit.rs`. -/
def validCandidateFeatures : List Name := [
  `refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

/-- Parser state threaded across commands in `inspectSource` to track open
    `namespace`/`section` scopes and record the trust classification
    (`"vetted"` or `"candidate:<feature>"`) of every declaration in
    `Trusted.*`. -/
structure ParseTrustState where
  /-- Stack of open scopes: `(true, name)` for a `namespace` component (which
      contributes to qualified declaration names) and `(false, name)` for a
      `section` scope (which does not). -/
  scopes : List (Bool × Name) := []
  /-- Pairs `(fullDeclarationName, trustStatus)` collected from `Trusted.*`. -/
  trustDeclarations : Array (String × String) := #[]

/-- Reconstruct the active Lean namespace from `st.scopes`. -/
def currentNamespace (st : ParseTrustState) : Name :=
  st.scopes.foldl (init := .anonymous) fun acc (isNs, n) =>
    if isNs then acc ++ n else acc

/-- Validate a single `Parser.Term.attrInstance` syntax node `elem` and return
    `some "vetted"` or `some "candidate:<feature>"` if `elem` is a trust
    attribute, or `none` if `elem` is an ordinary allowed attribute.

    - `allowTrustAttrs` is `true` only on top-level declarations and inductive
      constructors inside `Trusted.*` modules; trust attributes in `theory/`,
      `Mir`, `Proof`, or nested inside terms are rejected.
    - `allowMacroAttr` is `true` during `inspectSyntax` on `Trusted.*`
      declaration modifiers and during `extractTrustModifier` on
      `Trusted.expandTrustDeclaration` in `Trusted/Refinement.lean`, which
      carries `@[macro Lean.Parser.Command.declaration, macro
      Lean.Parser.Command.mutual]` so Lean strips `@[vetted]` and
      `@[candidate <feature>]` during elaboration after `"preflight"` has
      recorded them. -/
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
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp
      || (!allowTrustAttrs && k == `Lean.Parser.Attr.grind) then
    return none
  else
    fail s!"unsupported attribute form {k}"

/-- Extract the unique trust classification (`"vetted"` or
    `"candidate:<feature>"`) from a `Parser.Command.declModifiers` node `mods`,
    rejecting declarations that combine multiple trust attributes. -/
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

/-- Recursively validate syntax node `s` during `"preflight"`.

    Why source-syntax inspection is needed in addition to `.olean` kernel
    checks:
    1. Elaboration-time tactics and terms (`by_elab`, `run_tac`,
       `native_decide`, `decide +native`) can execute arbitrary code or bypass
       kernel proof construction during compilation.
    2. `set_option` (at command, term, or tactic level) can set
       `debug.skipKernelTC true` or alter elaborator soundness flags.
    3. A term `unsafe t` inside a safe definition elaborates into a *safe*
       `opaque` auxiliary constant with an `@[implemented_by]` override;
       checking `ConstantInfo.isUnsafe` on the top-level definition does not
       catch it.
    4. `deriving` handlers can synthesize instances via arbitrary
       metaprograms. -/
partial def inspectSyntax (allowTrustAttrs : Bool) (s : Syntax) : IO Unit := do
  let k := s.getKind
  if [``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
      ``Parser.Command.axiom, ``Parser.Command.example, ``Parser.Command.coinductive,
      ``Parser.Command.openScoped, ``Parser.Command.set_option,
      ``Parser.Term.set_option, ``Parser.Term.unsafe, ``Parser.Tactic.set_option,
      `Lean.byElab, `Lean.Parser.Tactic.runTac,
      `Lean.Parser.Tactic.nativeDecide].contains k then
    fail s!"unsupported source form {k}"
  if k == ``Parser.Command.optDeriving || k == ``Parser.Command.optDefDeriving then
    if atomWithin s "deriving" then fail "deriving clauses are unsupported"
  if k == ``Parser.Term.attrInstance then
    let _ ← inspectAttrInstance allowTrustAttrs allowTrustAttrs s
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do
      fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    if identWithin s `native || atomWithin s "native" then
      fail "native decide configuration is unsupported"
  if k == ``Parser.Command.declaration then
    -- Allow trust attributes on the declaration's outer `declModifiers`
    -- (`s[0]`) and on each inductive constructor's `declModifiers`
    -- (`ctor[2]`), but forbid them everywhere else inside the declaration's
    -- signature or body.
    inspectSyntax allowTrustAttrs s[0]
    let decl := s[1]
    if decl.getKind == ``Parser.Command.inductive then
      for i in [:decl.getArgs.size] do
        if i == 4 then
          for ctor in decl[4].getArgs do
            for j in [:ctor.getArgs.size] do
              inspectSyntax (if j == 2 then allowTrustAttrs else false) ctor[j]!
        else
          inspectSyntax false decl[i]!
    else
      inspectSyntax false decl
  else if k == ``Parser.Command.declModifiers ||
      k == ``Parser.Term.attributes || k == `null ||
      k == ``Parser.Command.mutual || k == ``Parser.Command.in then
    for child in s.getArgs do inspectSyntax allowTrustAttrs child
  else
    for child in s.getArgs do inspectSyntax false child

/-- Validate a top-level command `s` and update `st` with any namespace/section
    scope changes and (when `isTrustedModule` is `true`) the trust
    classifications of all declared constants and inductive constructors.

    Every declaration in a `Trusted.*` module must carry an explicit `@[vetted]`
    or `@[candidate <feature>]` attribute, and every `instance` in `Trusted.*`
    must be explicitly named so its preflight name matches its `.olean`
    `ConstantInfo.name` without running the elaborator's instance-naming
    heuristic. Constructors of an inductive `I` inherit `I`'s trust status by
    default; a `@[vetted]` inductive may mark individual constructors as
    `@[candidate <feature>]` (for incremental language/TCB extensions), whereas
    a `@[candidate <feature>]` inductive is forbidden from marking any of its
    constructors `@[vetted]`. -/
partial def inspectCommand (isTrustedModule : Bool) (s : Syntax)
    (st : ParseTrustState) : IO ParseTrustState := do
  unless commandKinds.contains s.getKind do fail s!"unsupported command {s.getKind}"
  inspectSyntax isTrustedModule s
  if s.isOfKind ``Parser.Command.namespace then
    let pushed := s[1].getId.components.map (true, ·)
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.section then
    let secArgs := s[2].getArgs
    let pushed :=
      if secArgs.isEmpty then [(false, .anonymous)]
      else secArgs[0]!.getId.components.map (false, ·)
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.end then
    let endArgs := s[1].getArgs
    let count :=
      if endArgs.isEmpty then 1 else endArgs[0]!.getId.components.length
    if st.scopes.length < count then fail "unmatched `end` command"
    return { st with scopes := st.scopes.take (st.scopes.length - count) }
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    let st1 ← inspectCommand isTrustedModule s[0] st
    return ← inspectCommand isTrustedModule s[2] st1
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    let mut cur := st
    for child in s[1].getArgs do
      cur ← inspectCommand isTrustedModule child cur
    return cur
  if s.isOfKind ``Parser.Command.declaration && isTrustedModule then
    let mods := s[0]
    let decl := s[1]
    let curNs := currentNamespace st
    let relName ←
      if decl.getKind == ``Parser.Command.instance then
        if decl[3].getArgs.isEmpty then
          fail s!"unnamed instance in {curNs}; Trusted instances must be named"
        else
          pure decl[3][0][0].getId
      else
        pure decl[1][0].getId
    let fullName := curNs ++ relName
    -- Only `Trusted.expandTrustDeclaration` itself may carry `@[macro ...]`.
    let allowMacroAttr := fullName == `Trusted.expandTrustDeclaration
    let some status ← extractTrustModifier true allowMacroAttr mods
      | fail s!"missing @[vetted] or @[candidate <feature>] attribute on Trusted declaration {fullName}"
    let mut nextSt :=
      { st with trustDeclarations := st.trustDeclarations.push (fullName.toString, status) }
    if decl.getKind == ``Parser.Command.inductive then
      for ctor in decl[4].getArgs do
        let ctorFullName := fullName ++ ctor[3].getId
        let ctorStatusOpt ← extractTrustModifier true false ctor[2]
        let ctorStatus := ctorStatusOpt.getD status
        -- A candidate inductive cannot contain a vetted constructor because
        -- constructing or eliminating the inductive requires the candidate
        -- type.
        if status.startsWith "candidate:" && ctorStatus == "vetted" then
          fail s!"constructor {ctorFullName} of candidate inductive {fullName} cannot be marked @[vetted]"
        nextSt :=
          { nextSt with trustDeclarations := nextSt.trustDeclarations.push (ctorFullName.toString, ctorStatus) }
    return nextSt
  return st

/-- Parse and validate a single `.lean` source file during `"preflight"` using
    only the `foundation ++ toolchainLibrary` parser environment `parserEnv`.

    Requires an explicit `prelude` header so Lean never injects an implicit
    `import Init` edge outside the admitted module subset, and rejects
    `module`, `public`, `meta`, and `import all` header modifiers. -/
def inspectSource (parserEnv : Environment) (moduleName : Name)
    (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then
    fail s!"header parser error in {moduleName}"
  if Elab.HeaderSyntax.isModule header then fail "module headers are unsupported"
  unless atomWithin header.raw "prelude" do fail "explicit prelude is required"
  if atomWithin header.raw "public" || atomWithin header.raw "meta" ||
      atomWithin header.raw "all" then
    fail "explicit import modifiers are unsupported"
  let imports := Elab.HeaderSyntax.imports header
  for imp in imports do
    if imp.importAll || imp.isMeta || !imp.isExported then
      fail "import modifiers are unsupported"
  let isTrustedModule := moduleName == `Trusted || moduleName.getRoot == `Trusted
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
    if state.pos <= previous then throw <| IO.userError "parser made no progress"
    trustState ← inspectCommand isTrustedModule stx trustState
  unless trustState.scopes.isEmpty do
    fail s!"unclosed namespace or section in {moduleName}"
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("trustDeclarations", toJson trustState.trustDeclarations)]

/-- Traverse a kernel `Expr` `e` and return `(unguardedConstants,
    guardedBranches)`.

    Unlike `ConstantInfo.getUsedConstantsAsSet`, this traversal records
    primitive literal types (`Nat` and `String`) and structure-projection type
    names (`.proj s _ b`), and rejects open expressions containing free
    variables, metavariables, or loose bound variables.

    When `splitCandidateGuards` is `true`, any subexpression of the form
    `@Trusted.candidate "<feat>" α body extraArgs...` is split at the guard
    boundary:
    - `Trusted.candidate`, `String`, the type argument `α` (`args[1]`), and any
       trailing arguments `args[3..]` are traversed as unguarded edges.
    - The guarded branch `body` (`args[2]`) is *not* traversed as an unguarded
      edge; instead, `(feat, body)` is pushed onto `guardedBranches` so
      `checkTrustedNonContamination` can verify that `body` uses only `vetted`
      and `candidate:<feat>` declarations, and `collectActiveCandidateFeatures`
      can defer traversing `body` until `candidate:<feat>` is reached. -/
partial def exprEdges (splitCandidateGuards : Bool) (e : Expr) :
    IO (NameSet × Array (String × Expr)) := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    fail "open expression in stored declaration"
  let mut result : NameSet := {}
  let mut guarded : Array (String × Expr) := #[]
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      if splitCandidateGuards && x.getAppFn.isConstOf `Trusted.candidate then
        let args := x.getAppArgs
        if args.size < 3 then
          fail "partially applied Trusted.candidate is unsupported"
        let .lit (.strVal feat) := args[0]!
          | fail "Trusted.candidate feature argument must be a string literal"
        unless validCandidateFeatures.contains feat.toName do
          fail s!"unknown candidate feature {feat} in Trusted.candidate"
        result := result.insert `Trusted.candidate
        result := result.insert `String
        pending := args[1]! :: (args.extract 3 args.size).toList ++ pending
        guarded := guarded.push (feat, args[2]!)
      else
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
  return (result, guarded)

/-- Collect all constant names referenced anywhere inside `e` without splitting
    `Trusted.candidate` guards. -/
def expressionEdges (e : Expr) : IO NameSet := do
  return (← exprEdges false e).1

/-- Collect the complete set of direct kernel constant dependencies of `ci`,
    including its type, its value (with `allowOpaque := true` so `opaque`
    definitions cannot conceal dependencies), mutual-block peers (`v.all`),
    inductive constructors (`v.ctors`), constructor parent inductives
    (`v.induct`), and recursor reduction rule RHS expressions (`rule.rhs`). -/
def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let mut result ← expressionEdges ci.type
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ (← expressionEdges value)
  match ci with
  | .defnInfo v => result := result ++ .ofList v.all
  | .thmInfo v => result := result ++ .ofList v.all
  | .opaqueInfo v => result := result ++ .ofList v.all
  | .inductInfo v => result := result ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => result := result.insert v.induct
  | .recInfo v =>
    result := result ++ .ofList v.all
    for rule in v.rules do
      result := (result.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | _ => pure ()
  return result

/-- Human-readable kind tag for a kernel `ConstantInfo`. -/
def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- Return the defining module name for kernel constant `n` in `env`. -/
def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]? | fail s!"invalid module index: {n}"
  return mod.module

/-- Compute the transitive kernel dependency closure of `roots` and verify that
    every reachable axiom `n` (`ci.isAxiom`) with defining module `m ←
    provenance n` appears in the locked `foundation` axiom allowlist `axioms`
    (`{Classical.choice, Quot.sound, propext}`). -/
def closure (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (axioms : Array (String × String)) (roots : Array Name) : IO (Array Name × Nat) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut reachedAxioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      if ci.isAxiom then
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n
      pending := (← declarationEdges ci).toList ++ pending
  return (reachedAxioms.toArray.qsort Name.lt, visited.size)

/-- Parse the `"trustDeclarations"` table produced by `"preflight"` into a map
    from `Name` to trust status (`"vetted"` or `"candidate:<feature>"`). -/
def parseTrustMap (j : Json) : IO (Std.HashMap Name String) := do
  let decls ← field (α := Array (String × String)) j "trustDeclarations"
  let mut declMap : Std.HashMap Name String := {}
  for (n, status) in decls do
    declMap := declMap.insert n.toName status
  return declMap

/-- Classify a compiled `Trusted.*` kernel constant `cName` by stripping any
    `_private.<module>.0.` prefix (`privateToUserName?`) and walking its name
    prefixes from longest to shortest until an explicit entry in `declMap` is
    found.

    Returning `(status, ownerUserName)` maps both user-written declarations
    (and constructors) to their exact preflight entry and compiler-generated
    auxiliary constants (such as `Foo.rec`, `Foo.casesOn`, `bar.match_1`,
    `bar._eq_1`, or structure field projections) to the trust status and name
    of the owning declaration (`ownerUserName`). Fails closed if `cName` does
    not belong to any classified declaration in `declMap`. -/
def classifyTrustedConstant (declMap : Std.HashMap Name String)
    (cName : Name) : IO (String × Name) := do
  let userName := (privateToUserName? cName).getD cName
  let mut cur := userName
  while !cur.isAnonymous do
    if let some status := declMap.get? cur then
      return (status, cur)
    cur := cur.getPrefix
  fail s!"unclassified Trusted constant {cName}"

/-- Enforce the two-color non-contamination boundary between `@[vetted]` and
    `@[candidate <feature>]` declarations inside `Trusted.*`.

    A `@[vetted]` declaration must be sound and self-contained when all
    candidate features are disabled (`VettedOnly`). However, Anneal allows a
    `@[vetted]` inductive type (such as an AST or `TCBItem` sum type) to have
    individual constructors marked `@[candidate <feat>]` so new language
    constructs can be staged in place without duplicating the inductive type.

    To make extensible `@[vetted]` inductives sound without allowing silent
    candidate contamination, this function enforces three rules:

    1. **Candidate constructors of `@[vetted]` inductives:**
       If constructor `cName` of a `@[vetted]` inductive `v.induct` has status
       `candidate:<feat>`, its field types (`ci.type`) may reference only
       `vetted` or `candidate:<feat>` declarations (never a different candidate
       feature). `cName` and any `candidate:<feat>` types appearing in its
       signature are added to `allowedInMatcherHelper`, because Lean's
       compiler-generated `_match_1` / `casesOn` helper for a function matching
       on `v.induct` must mention `cName`'s field types in its type signature.
    2. **Top-level `@[vetted]` declarations (`userName == owner`):**
       - **Type purity:** `ci.type` may reference only `vetted` declarations.
       - **Unguarded body purity:** Outside `Trusted.candidate "<feat>" (...)`
         subexpressions, `ci.value?` (`unguardedEdges`) may reference only
         `vetted` declarations.
       - **Guarded branch isolation:** Inside each `Trusted.candidate "<feat>"
         body` branch (including nested guards), `body` may reference only
         `vetted` or `candidate:<feat>` declarations.
       - **Bidirectional guard-dispatch coupling:** The set of candidate
         features guarded by `Trusted.candidate "<feat>"` in `cName`
         (`guardedFeats`) must exactly equal the set of candidate features
         (`dispatchedCandidateFeats`) of `@[vetted]` inductives whose
         constructors/recursors are dispatched by `cName` (or its auxiliary
         matcher helpers):
         * Every dispatched `candidate:<feat>` constructor must have a matching
           `Trusted.candidate "<feat>"` guard, so a `@[vetted]` function cannot
           match on a candidate constructor and silently return a trivial
           `vetted` result without recording the feature dependency.
         * Every `Trusted.candidate "<feat>"` guard must correspond to a
           dispatched `candidate:<feat>` constructor, so a `@[vetted]` function
           cannot wrap an unconditional call to `candidate:<feat>` code inside a
           guard that executes even when no `candidate:<feat>` constructor is
           present in the input.
    3. **Compiler-generated helpers of `@[vetted]` definitions
       (`userName != owner && !isInductOwner`):**
       Their unguarded expressions may reference only `vetted` declarations or
       types in `allowedInMatcherHelper`. -/
def checkTrustedNonContamination (locals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name) : IO Unit := do
  -- Pass 1: Index `@[candidate <feat>]` constructors of `@[vetted]` inductives
  -- and validate that their field types do not cross-contaminate features.
  let mut vettedInductCandidateCtors : Std.HashMap Name (Array (Name × String)) := {}
  let mut allowedInMatcherHelper : NameSet := {}
  for (cName, ci) in locals do
    if let .ctorInfo v := ci then
      if statusMap.get? v.induct == some "vetted" then
        let ctorStatus := statusMap.getD cName "vetted"
        if ctorStatus.startsWith "candidate:" then
          let feat := (ctorStatus.drop 10).toString
          let prev := vettedInductCandidateCtors.getD v.induct #[]
          vettedInductCandidateCtors :=
            vettedInductCandidateCtors.insert v.induct (prev.push (cName, feat))
          allowedInMatcherHelper := allowedInMatcherHelper.insert cName
          for dep in (← expressionEdges ci.type) do
            if let some depStatus := statusMap.get? dep then
              if depStatus.startsWith "candidate:" && depStatus != ctorStatus then
                fail s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references {dep} ({depStatus}) in its type"
              if depStatus == ctorStatus then
                allowedInMatcherHelper := allowedInMatcherHelper.insert dep
  -- Pass 2: Verify every `@[vetted]` declaration and its compiler helpers.
  for (cName, ci) in locals do
    if statusMap.get? cName == some "vetted" then
      let userName := (privateToUserName? cName).getD cName
      let owner := ownerMap.getD cName userName
      let isInductOwner :=
        match locals.get? owner with | some (.inductInfo _) => true | _ => false
      if userName == owner then
        for dep in (← expressionEdges ci.type) do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" then
              fail s!"vetted declaration {cName} references {depStatus} declaration {dep} in its type"
        if let some val := ci.value? (allowOpaque := true) then
          let (unguardedEdges, guardedBranches) ← exprEdges true val
          for dep in unguardedEdges do
            if let some depStatus := statusMap.get? dep then
              if depStatus != "vetted" then
                fail s!"vetted declaration {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
          let mut guardedFeats : Std.HashSet String := {}
          let mut pendingGuarded := guardedBranches.toList
          while !pendingGuarded.isEmpty do
            let (feat, body) := pendingGuarded.head!
            pendingGuarded := pendingGuarded.tail!
            guardedFeats := guardedFeats.insert feat
            let expectedStatus := s!"candidate:{feat}"
            let (bodyEdges, innerGuarded) ← exprEdges true body
            for dep in bodyEdges do
              if let some depStatus := statusMap.get? dep then
                if depStatus != "vetted" && depStatus != expectedStatus then
                  fail s!"Trusted.candidate \"{feat}\" branch in {cName} references {dep} ({depStatus})"
            pendingGuarded := innerGuarded.toList ++ pendingGuarded
          -- Union the direct dependencies of `cName` and its compiler-generated
          -- `_match` / equation helpers to check guard-dispatch coupling.
          let mut directDeps ← declarationEdges ci
          for (hName, hCi) in locals do
            if hName != cName && ownerMap.get? hName == some owner then
              directDeps := directDeps ++ (← declarationEdges hCi)
          let mut dispatchedCandidateFeats : Std.HashSet String := {}
          for dep in directDeps do
            let depOwner := ownerMap.getD dep dep
            if let some ctors := vettedInductCandidateCtors.get? depOwner then
              for (ctorName, feat) in ctors do
                dispatchedCandidateFeats := dispatchedCandidateFeats.insert feat
                unless guardedFeats.contains feat do
                  fail s!"vetted declaration {cName} matches on candidate constructor {ctorName} (candidate:{feat}) without a Trusted.candidate \"{feat}\" guard"
          for feat in guardedFeats do
            unless dispatchedCandidateFeats.contains feat do
              fail s!"vetted declaration {cName} uses Trusted.candidate \"{feat}\" without matching on a vetted inductive with a candidate:{feat} constructor"
      else if !isInductOwner then
        if let some val := ci.value? (allowOpaque := true) then
          let (unguardedEdges, _) ← exprEdges true val
          for dep in unguardedEdges do
            if let some depStatus := statusMap.get? dep then
              if depStatus != "vetted" && !allowedInMatcherHelper.contains dep then
                fail s!"vetted helper {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"

/-- Compute the sorted list of candidate-trusted features (`@[candidate
    <feat>]`) actively reached by a crate's verification closure (`roots`,
    comprising all declarations in `Mir` and `Proof`).

    Why reachability is demand-driven across `Trusted.candidate "<feat>"`
    guards:
    - A `@[vetted]` interpreter or theorem envelope may pattern-match on a
      `@[vetted]` inductive that has both `@[vetted]` constructors and
      `@[candidate <feat>]` constructors (with the latter arms wrapped in
      `Trusted.candidate "<feat>" body`).
    - When `collectActiveCandidateFeatures` visits a top-level `@[vetted]`
      definition, it immediately traverses the definition's type and unguarded
      body edges, but *defers* traversing `body` inside `Trusted.candidate
      "<feat>" body` unless `<feat>` is in `activeFeats`. Also, when visiting a
      `@[vetted]` inductive, recursor, or matcher helper (`!isTopLevelDef`), it
      follows only `vetted` edges so that merely mentioning the inductive type
      does not activate its candidate constructors.
    - If `Mir`, `Proof`, or any already-active dependency directly references a
      `candidate:<feat>` constructor or declaration, `<feat>` is inserted into
      `activeFeats`, releasing all deferred `<feat>` branch bodies into
      `pending` so any transitive candidate dependencies inside those branches
      are discovered as well. -/
def collectActiveCandidateFeatures (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (trusted : Array Name)
    (statusMap : Std.HashMap Name String) (ownerMap : Std.HashMap Name Name)
    (roots : Array Name) : IO (Array String) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut activeFeats : Std.HashSet String := {}
  let mut deferred : Std.HashMap String (Array Expr) := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      if trusted.contains m then
        let status := statusMap.getD n "vetted"
        if status.startsWith "candidate:" then
          let feat := (status.drop 10).toString
          if !activeFeats.contains feat then
            activeFeats := activeFeats.insert feat
            -- Release any `Trusted.candidate "<feat>"` branches encountered
            -- earlier in `@[vetted]` definitions now that `<feat>` is active.
            if let some bodies := deferred.get? feat then
              deferred := deferred.erase feat
              for b in bodies do
                pending := (← expressionEdges b).toList ++ pending
          pending := (← declarationEdges ci).toList ++ pending
        else
          let userName := (privateToUserName? n).getD n
          let owner := ownerMap.getD n userName
          let isTopLevelDef :=
            userName == owner &&
            (match ci with
             | .inductInfo _ | .recInfo _ | .ctorInfo _ => false
             | _ => true)
          if isTopLevelDef then
            pending := (← expressionEdges ci.type).toList ++ pending
            if let some val := ci.value? (allowOpaque := true) then
              let (unguarded, guarded) ← exprEdges true val
              pending := unguarded.toList ++ pending
              for (feat, body) in guarded do
                if activeFeats.contains feat then
                  pending := (← expressionEdges body).toList ++ pending
                else
                  let prev := deferred.getD feat #[]
                  deferred := deferred.insert feat (prev.push body)
          else
            -- For `@[vetted]` inductives, recursors, and matcher helpers, do
            -- not traverse into `@[candidate]` constructors unless those
            -- constructors are explicitly referenced elsewhere in the closure.
            for dep in (← declarationEdges ci) do
              if (statusMap.getD dep "vetted") == "vetted" then
                pending := dep :: pending
      else
        pending := (← declarationEdges ci).toList ++ pending
  return activeFeats.toArray.qsort (· < ·)

/-- Return `true` when `a` and `b` are both kernel theorems (`.thmInfo`) with
    identical name, universe parameters, proposition type, and mutual-group
    membership (`all`).

    In Lean 4.34.1, on-demand theorem realization
    (`Lean.Environment.realizeConst` in
    `src/lean/Lean/Environment.lean:2709-2783`, invoked via
    `Lean.Meta.realizeConst` in `src/lean/Lean/Meta/Basic.lean:2727-2765` at
    commit `5045d0056413266e57c625dcd7c365b10e377c52`) generates equation and
    congruence theorems (such as `<fn>.eq_def`, `<fn>.eq_1`, `<fn>.congr_simp`,
    and `<fn>.induct_unfolding`) inside the realizing module's stage-2 kernel
    constant map (`kenv.constants.foldStage2` in `mkModuleData`,
    `Lean/Environment.lean:1868-1872`). When two incomparable modules `M₁` and
    `M₂` in a diamond import graph both realize the same theorem `c` for an
    upstream definition, `finalizeImport` (`Lean/Environment.lean:2268-2283`,
    `2332-2348`) checks `subsumesInfo`, retains `M₁` in `const2ModIdx`
    (`env.getModuleIdxFor?`), and overwrites `privateConstantMap[c]`
    (`env.checked`) with `M₂`'s `ConstantInfo`. Similarly,
    `Lean.Kernel.Environment.replay'` (`src/lean/Lean/Replay.lean:89-96`) skips
    re-adding a `.thmInfo` when an identical theorem header already exists in
    the kernel environment. -/
def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    ta.name == tb.name &&
    ta.type == tb.type &&
    ta.levelParams == tb.levelParams &&
    ta.all == tb.all
  | _, _ => false

/-- Collect the subset of `locals` transitively reachable from `roots` via
    `declarationEdges` (which includes expression references in types and
    bodies, mutual-block peers `v.all`, inductive constructors `v.ctors`, parent
    inductives `v.induct`, and recursor reduction rules `rule.rhs`). -/
def collectLocalClosure (locals : Std.HashMap Name ConstantInfo)
    (roots : Array Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut pending := roots.toList
  let mut result : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !result.contains n then
      if let some ci := locals.get? n then
        result := result.insert n ci
        for dep in (← declarationEdges ci) do
          if !result.contains dep && locals.contains dep then
            pending := dep :: pending
  return result

/-- Verify module allowlists, declaration provenance, and the absence of axioms
    and `unsafe`/user-`partial` declarations across all loaded modules,
    returning `(locals, extraNames)` where `locals` maps every non-base logical
    constant (`!ci.isUnsafe && !ci.isPartial`, matching `ConstantInfo.isCEnv` in
    `src/lean/Lean/Replay.lean:181-196`) to its `ConstantInfo` for
    `base.toKernelEnv.replay`.

    Specifically checks that:
    1. Every module in `allowedAll` is loaded in `env.header.modules`, and every
       loaded module belongs to `allowedAll`.
    2. Each module's `constNames` array matches `constants.map
       ConstantInfo.name`, and every constant's `origin` matches its module
       (`baseMods` for `foundation` and `toolchainLibrary` modules; exact
       `m.module` with no duplicate names for local modules, except for
       realized `.thmInfo` declarations satisfying
       `sameRealizedThmHeader stored ci`).
    3. Every constant in `data.constants` is present in `env.checked` with the
       exact same `type` and `value? (allowOpaque := true)` (or
       `sameRealizedThmHeader stored ci` for duplicate realized theorems across
       incomparable diamond modules).
    4. No non-base constant (`Trusted`, `Anneal`, `Mir`, `Proof`) is `isUnsafe`
       or `isAxiom`, or lacks a body when `ci.hasValue true`—even if that
       constant is never referenced by a theorem. Any `isPartial` declaration
       must be a compiler-generated `<base>._unsafe_rec` companion
       (`Lean.Compiler.isUnsafeRecName?`) whose `<base>` declaration in the same
       module is a safe `.defnInfo` (`baseVal.safety == .safe`), rejecting
       user-written `partial def` declarations (whose `<base>` is
       `.opaqueInfo`).
    5. Every compiler-only IR helper (`data.extraConstNames`) has matching
       module provenance, and no non-base constant exists in `env.checked`
       outside `locals ∪ partialCompanions`. -/
def verifyAndCollectLocals (env : Environment) (baseMods : Array Name)
    (trusted : Array Name) (allowedAll : Array Name) :
    IO (Std.HashMap Name ConstantInfo × NameSet) := do
  let loadedMods : NameSet := .ofList (env.header.modules.toList.map (·.module))
  for reqMod in allowedAll do
    unless loadedMods.contains reqMod do fail s!"missing required module {reqMod}"
  let baseSet : NameSet := .ofList baseMods.toList
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut partialCompanions : NameSet := {}
  let mut pendingPartials : Array (Name × Name × Bool) := #[]
  let mut extraNames : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    for ci in data.constants do
      let orig ← origin env ci.name
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      let exactValueMatch :=
        stored.type == ci.type && stored.value? true == ci.value? true
      let isRealizedThmDup := sameRealizedThmHeader stored ci
      unless exactValueMatch || isRealizedThmDup do
        fail s!"stored declaration differs from inventory {ci.name}"
      if baseSet.contains m.module then
        unless baseSet.contains orig do
          fail s!"inventory origin mismatch {ci.name}"
      else
        let isTrusted := trusted.contains m.module
        if ci.isUnsafe then
          fail (if isTrusted then s!"unsafe/partial Trusted declaration {ci.name}"
                else s!"unsafe/partial declaration {ci.name} in {m.module}")
        if ci.isAxiom then
          fail (if isTrusted then s!"Trusted axiom {ci.name}"
                else s!"strict axiom declaration {ci.name} in {m.module}")
        if ci.isPartial then
          partialCompanions := partialCompanions.insert ci.name
          pendingPartials := pendingPartials.push (ci.name, m.module, isTrusted)
        else
          if ci.hasValue true && (ci.value? true).isNone then
            fail s!"missing stored body {ci.name}"
          if baseSet.contains orig then
            unless isRealizedThmDup do
              fail s!"inventory origin mismatch {ci.name}"
          else if orig != m.module || locals.contains ci.name then
            unless isRealizedThmDup do
              if locals.contains ci.name then
                fail s!"duplicate declaration {ci.name}"
              else
                fail s!"inventory origin mismatch {ci.name}"
            locals := locals.insert ci.name stored
          else
            locals := locals.insert ci.name stored
    for n in data.extraConstNames do
      if !baseSet.contains m.module then
        unless (← origin env n) == m.module do
          fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n || partialCompanions.contains n do
            fail s!"uninventoried kernel compiler helper {n}"
        else if trusted.contains m.module then
          extraNames := extraNames.insert n
      else
        unless baseSet.contains (← origin env n) do
          fail s!"IR helper provenance mismatch {n}"
  for (cName, modName, isTrusted) in pendingPartials do
    let errMsg :=
      if isTrusted then s!"unsafe/partial Trusted declaration {cName}"
      else s!"unsafe/partial declaration {cName} in {modName}"
    let some baseName := Compiler.isUnsafeRecName? cName | fail errMsg
    let some (.defnInfo baseVal) := locals.get? baseName | fail errMsg
    unless baseVal.safety == .safe && (← origin env baseName) == modName do
      fail errMsg
  for (n, _) in env.checked.get.constants do
    if !baseSet.contains (← origin env n) &&
        !locals.contains n && !partialCompanions.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, extraNames)

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`.

    When `crates` is empty (`cargo anneal audit-repo`), audits the
    repository's `trusted/lean/` (`trusted`) and `theory/` (`theory`) modules.
    When `crates` is non-empty (`cargo anneal verify`), additionally audits each
    target crate's `(mirMod, proofMod)` pair:

    - **Why `<mirMod>.crate` and `<proofMod>.verify_crate` are checked by module
      origin, kind, and exact kernel `Expr` equality:**
      `<mirMod>.crate` represents the lowered Rust crate and its specifications
      as a `Trusted.Crate` definition in `mirMod` (which `audit.rs` and
      `validateGraph` restrict to importing only `foundation ++ trusted`).
      Checking `proofCi.type == Expr.app (Expr.const ``Trusted.CrateTheorem [])
      (Expr.const mirCrateName [])` guarantees that the theorem proved by the
      untrusted `proofMod` module is literally `Trusted.CrateTheorem
      <mirMod>.crate`—not `True` or a spoofed predicate from `theory/`—while
      allowing `proofMod`'s proof term (`ci.value?`) to use arbitrary pure
      lemmas and evaluators from `theory/` and `toolchainLibrary`.
    - **Why `base.toKernelEnv.replay replayLocals` runs at the end:**
      Importing `.olean` files into `Environment` trusts the serialized
      `.olean` constant table. Replaying `replayLocals` (all `locals` in
      `audit-repo` mode, or the transitive local dependency closure of every
      `<proofMod>.verify_crate` in `verify` mode) into a fresh
      `foundation ++ toolchainLibrary` `Kernel.Environment` forces Lean's kernel
      typechecker to re-verify every local definition and theorem body from
      scratch. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (toolchainLib : Array Name) (trusted : Array Name) (theory : Array Name)
    (crates : Array (Name × Name)) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let declMap ← parseTrustMap j
  let baseMods := foundation ++ toolchainLib
  let crateModules : Array Name :=
    crates.foldl (fun acc (m, p) => acc.push m |>.push p) #[]
  let crateModSet : NameSet := .ofList crateModules.toList
  let allowedAll := baseMods ++ trusted ++ theory ++ crateModules
  let (locals, extraNames) ←
    verifyAndCollectLocals env baseMods trusted allowedAll
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let mut trustedLocals : Std.HashMap Name ConstantInfo := {}
  let mut statusMap : Std.HashMap Name String := {}
  let mut ownerMap : Std.HashMap Name Name := {}
  let mut inventory := #[]
  let mut trustedRoots : Array Name := #[]
  let mut allLocalRoots : Array Name := #[]
  let mut crateRoots : Array Name := #[]
  for (cName, ci) in locals do
    allLocalRoots := allLocalRoots.push cName
    let orig ← origin env cName
    if trusted.contains orig then
      let (trustStatus, ownerName) ← classifyTrustedConstant declMap cName
      trustedLocals := trustedLocals.insert cName ci
      statusMap := statusMap.insert cName trustStatus
      ownerMap := ownerMap.insert cName ownerName
      trustedRoots := trustedRoots.push cName
      inventory := inventory.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig), ("kind", toJson (kind ci)),
        ("trustStatus", toJson trustStatus),
        ("dependencies", toJson ((← declarationEdges ci).toArray.qsort Name.lt))]
    else if crateModSet.contains orig then
      crateRoots := crateRoots.push cName
  checkTrustedNonContamination trustedLocals statusMap ownerMap
  let _ ← closure lookup (origin env) axiomPolicy allLocalRoots
  let (report, replayLocals) ←
    if crates.isEmpty then
      let (trustedAxioms, trustedVisited) ←
        closure lookup (origin env) axiomPolicy trustedRoots
      let rep := Json.mkObj [
        ("graph", graph env), ("declarations", .arr inventory),
        ("kernelDeclarations", toJson trustedLocals.size),
        ("replayedDeclarations", toJson locals.size),
        ("compilerOnlyNames", toJson extraNames.size),
        ("reachableDeclarations", toJson trustedVisited),
        ("axioms", toJson trustedAxioms), ("replay", toJson true)]
      pure (rep, locals)
    else
      let mut verifyRoots : Array Name := #[]
      for (mirMod, proofMod) in crates do
        let mirCrateName := mirMod ++ `crate
        let verifyCrateName := proofMod ++ `verify_crate
        let some mirCrateCi := env.checked.get.find? mirCrateName
          | fail s!"missing required declaration {mirCrateName} in {mirMod}"
        unless (← origin env mirCrateName) == mirMod do
          fail s!"{mirCrateName} must originate in module {mirMod}"
        unless kind mirCrateCi == "definition" do
          fail s!"{mirCrateName} must be a definition, found {kind mirCrateCi}"
        let expectedCrateType := Expr.const `Trusted.Crate []
        unless mirCrateCi.type == expectedCrateType do
          fail s!"{mirCrateName} has type {mirCrateCi.type}, expected Trusted.Crate"
        let some proofCi := env.checked.get.find? verifyCrateName
          | fail s!"missing required theorem {verifyCrateName} in {proofMod}"
        unless (← origin env verifyCrateName) == proofMod do
          fail s!"{verifyCrateName} must originate in module {proofMod}"
        unless kind proofCi == "theorem" do
          fail s!"{verifyCrateName} must be a theorem, found {kind proofCi}"
        let expectedTheoremType :=
          Expr.app (Expr.const `Trusted.CrateTheorem []) (Expr.const mirCrateName [])
        unless proofCi.type == expectedTheoremType do
          fail s!"{verifyCrateName} has type {proofCi.type}, expected Trusted.CrateTheorem {mirCrateName}"
        verifyRoots := verifyRoots.push verifyCrateName
      let (crateAxioms, crateVisited) ←
        closure lookup (origin env) axiomPolicy verifyRoots
      let candidateFeatures ←
        collectActiveCandidateFeatures lookup (origin env) trusted statusMap ownerMap crateRoots
      let closureLocals ← collectLocalClosure locals verifyRoots
      let (lastMir, lastProof) := crates.back!
      let rep := Json.mkObj [
        ("verifiedTheorem", toJson (lastProof ++ `verify_crate).toString),
        ("expectedType", toJson s!"Trusted.CrateTheorem {lastMir ++ `crate}"),
        ("verifiedTheorems", toJson (verifyRoots.map Name.toString)),
        ("replayedDeclarations", toJson closureLocals.size),
        ("totalLocalDeclarations", toJson locals.size),
        ("reachableDeclarations", toJson crateVisited),
        ("axioms", toJson crateAxioms),
        ("candidateFeatures", toJson candidateFeatures),
        ("replay", toJson true)]
      pure (rep, closureLocals)
  -- Replay `replayLocals` from scratch in a clean kernel environment
  -- containing only `foundation ++ toolchainLib` (`Init.*` and `Std.*`).
  let base ← importEnv j baseMods
  let _ ← base.toKernelEnv.replay replayLocals
  return report

/-- Dispatch `"preflight"` or `"audit"` from the JSON request `j`. -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  initSearchPath (← field (α := String) j "sysroot")
  let foundation ← names j "foundation"
  let toolchainLib ← namesOpt j "toolchainLibrary"
  let baseMods := foundation ++ toolchainLib
  if mode == "preflight" then
    let env ← importEnv j baseMods true
    validatePreflightGraph j env foundation baseMods
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  if mode == "audit" then
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let crates ← crateTargets j
    let crateModules : Array Name :=
      crates.foldl (fun acc (m, p) => acc.push m |>.push p) #[]
    let env ← importEnv j (baseMods ++ trusted ++ theory ++ crateModules)
    return ← audit j env foundation toolchainLib trusted theory crates
  throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

/-- CLI entry point invoked by `audit.rs` via `lean --run TrustedBoundary.lean
    <request.json> <result.json>`. Exit code 0 indicates success, 1 indicates a
    policy rejection (`"policy:..."`), and 2 indicates an operational
    failure. -/
def main (args : List String) : IO UInt32 := do
  let [request, output] := args | IO.eprintln "expected request and result files"; return 2
  try
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
    let result ← TrustedBoundary.run j
    IO.FS.writeFile output <| (Json.mkObj [("ok", toJson true), ("result", result)]).pretty
    return 0
  catch error =>
    let message := error.toString
    let category := if message.startsWith "policy:" then "policy" else "operational"
    IO.FS.writeFile output <| (Json.mkObj [
      ("ok", toJson false), ("category", toJson category), ("message", toJson message)]).pretty
    IO.eprintln message
    return if category == "policy" then 1 else 2
