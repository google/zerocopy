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
`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`. `anneal-audit`
(`trusted/audit/`) and `cargo-anneal verify` (`trusted/cargo-anneal/`) invoke
this file across six JSON IPC modes (`run` and `main`):

- **`"headers"` (target import discovery before elaboration):**
  Parses only module `prelude`/`import` headers via `Parser.parseHeader` so
  `cargo-anneal verify` can validate target module roles, admit the requested
  `library-lock.json` closure, and reject import cycles before compiling any
  target source.
- **`"preflight"` (foundation-parser syntactic admission before compilation):**
  Lean elaboration is Turing-complete and effectful: commands such as `#eval`
  and tactics/terms such as `run_tac`, `by_elab`, `native_decide`, and
  `include_str` can execute arbitrary code or read host files during
  compilation, while attributes such as `@[implemented_by]` and `@[extern]`
  alter code generation without appearing in kernel proof terms. `"preflight"`
  parses every Anneal repository `.lean` source using `Parser.parseHeader` and
  `Parser.parseCommand`—without elaborating the inspected commands—against the
  authenticated `foundation-lock.json` parser environment. Building this
  environment executes authenticated foundation initializers and parser
  extensions, which belong to the runtime TCB. Preflight enforces a closed,
  role-aware `SyntaxNodeKind` allowlist (`allowedTrustedSyntaxKinds` for
  tactic-free `trusted/` specifications and `allowedTheorySyntaxKinds` for
  `theory/` and `correspondence/` proofs) together with closed attribute and
  identifier grammars, and extracts each `Trusted` module's
  `-- anneal-trust-tier: <tier>` directive before `lean` compiles any file.
- **`"correspondence-preflight"` (Pass 2 compile-environment syntactic
  admission):**
  Pass 2 modules (`trusted/correspondence/` and `correspondence/`) compile
  against `vendor/lean-miri`, which transitively imports `Lean` and `Std` and
  registers additional parser syntax (for example `throwError` ->
  `Lean.termThrowError__`, `m!` -> `Lean.termM!_`, and vendor tactic `elab`s)
  that would parse as ordinary function applications under the foundation-only
  parser. Before compiling any Pass 2 module, `"correspondence-preflight"`
  loads the Pass 2 union compile environment (authenticated `foundation`, Pass
  1 `trusted/`, compiled untrusted Pass 1 `theory/`, and SHA-256-pinned
  `vendorMiri`, with `loadExts := true`, `level := .private`, and
  `enableInitializersExecution`), checks closed `CorrOrigin` module
  classification, and parses every Pass 2 source file against that parser
  environment under the same closed
  `allowedTrustedSyntaxKinds`/`allowedTheorySyntaxKinds` allowlists. Because
  `level := .private` enables runtime `[init]` phases and `loadExts := true`
  runs `finalizePersistentExtensions` -> `runInitAttrs` and
  `KeyedDeclsAttribute.ofOLeanEntry` (`evalConstCheck`), importing this
  environment executes pinned vendored `[init]` initializers (which can also
  register user-defined environment extensions), evaluates pinned vendored
  tactic `elab`s, and deserializes compiled Pass 1 `theory/` extension data
  inside the inspector process. `anneal-audit` executes
  `"correspondence-preflight"` inside an isolated OS-level `bwrap` sandbox
  (read-only toolchain, staged sources, and compiled libraries, with writes
  restricted to an isolated per-request output directory) alongside human
  review of pinned vendored and patched compile-time code against vendored
  compile-time and preflight side effects, while Pass 1's closed attribute
  allowlist restricts `theory/` `.olean`s to plain-data extension entries. Both
  `"preflight"` and `"correspondence-preflight"` track lexical
  `namespace`/`section`/`end`/`open` scopes and fail closed if any `namespace`
  or namespaced declaration enters—or any `open` has any candidate resolution
  (across every prefix of `currNamespace` including root and every
  conservatively tracked open namespace, regardless of whether an unimported
  decoy namespace exists in the union parser environment) matching—a namespace
  registering scoped entries in any `ScopedEnvExtension` (including scoped
  syntax, notations, macros, elaborators, instances, and attributes).
- **`"audit"` (Pass 1 repository `.olean` inspection and kernel replay):**
  Loads the compiled `trusted/lean/` and `theory/` `.olean` files with
  `trustLevel := 0`, `plugins := #[]`, and `loadExts := false` (skipping module
  initializers and persistent extension-state reconstruction callbacks). It
  partitions all loaded modules into `RepoOrigin` (`.foundation | .repo role`),
  verifies `.olean` header imports (`RepoOrigin.importViolation?`) and kernel
  declaration edges (`RepoOrigin.edgeViolation?`), `Trusted` namespace hygiene,
  the foundation axiom allowlist, core weakest-precondition and canary theorem
  non-backsliding (`verifyMirWpCoreTheorems`), and fresh kernel replay of every
  repository constant against `foundation-lock.json`
  (`base.toKernelEnv.replay`).
- **`"correspondence-audit"` (Pass 2 MIR correspondence and `lean-miri` full
  standalone kernel replay and cone audit):**
  Loads `Trusted.Correspondence`, `Anneal.MirCorrespondenceProof`, and the
  160-module `Miri.Interpreter.ExecutionMachine` closure at `trustLevel := 0`
  with `plugins := #[]` and `loadExts := false`. It classifies every loaded
  module into a closed partition (`CorrOrigin`), validates `.vendorMiri` and
  `.repo` inventory/origin integrity, enforces `Trusted`/`Anneal` namespace
  isolation and `CorrOrigin` import/edge separation, rejects any `axiom`,
  `unsafe`, quotient primitive, missing body, direct `sorryAx`, or direct
  compiler-reflection reference (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
  `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`) in `.vendorMiri`,
  replays EVERY non-`isPartial` `.vendorMiri` declaration from scratch through
  the standalone Lean kernel onto the authenticated `.foundation` and
  `.sysrootFoundation` base on every run (cold build and cache hit alike),
  replays all repository declarations (including `trusted/correspondence/` and
  `correspondence/`) directly on top of that replayed vendor kernel
  environment, checks that the 36-root `Miri.Interpreter.ExecutionMachine` cone
  and correspondence cone are free of `unsafe`, `partial`, `.vendorMiri`
  `opaque`, and unapproved axioms, and verifies all 34 Pass 2 correspondence,
  wiring, and canary claims plus reference-evaluator independence checks.
- **`"target-audit"` (external target crate verification):**
  Loads compiled target `.olean` artifacts (`TargetOrigin`: `.foundation`,
  `.library` from `library-lock.json`, and `.source role` across `TargetRole`:
  `.model`, `.specification`, `.capture`, `.expected`, `.proof`) with
  `trustLevel := 0`, `plugins := #[]`, and `loadExts := false` for every
  import, and it never calls `enableInitializersExecution`. Therefore no
  imported `[init]` declaration (such as a target `initialize` block) or
  extension import callback runs inside the inspector. It verifies
  `TargetOrigin.allows` over compiled declaration edges, reconciles diamond
  theorem exports across `library-lock.json`, replays all logically reached
  declarations and alternate proofs onto `foundation-lock.json`, checks
  definitional equality of both `Expected` and the submitted proof theorem
  against the canonical `CrateTheorem`/`UnitTheorem` kernel application, and
  rejects `@[implemented_by]`, `@[extern]`, and `@[csimp]` metadata on logically
  reached declarations that differs from the authenticated foundation and
  library metadata. Those comparisons read serialized attribute entries, which
  the importer attaches even without `loadExts`: `getParam?` for
  `@[implemented_by]` and `@[extern]`, and `csimpEntries` for `@[csimp]`.

## Module origin partitions and authority relations

Every kernel constant `c` has a unique defining module (`origin env c`, read
directly from `env.getModuleIdxFor? c` in the `.olean`), including
compiler-generated constructors, recursors (`rec`, `casesOn`, `recOn`,
`noConfusion`, `below`, `brecOn`), projections, pattern matchers (`match_1`),
equation lemmas (`eq_1`), and `where`/`private` helpers. Each audit pass maps
defining modules into a closed origin sum type equipped with an explicit, total,
pure authority check over kernel declaration edges (`RepoOrigin.edgeViolation?`,
`CorrOrigin.edgeViolation?`, and `TargetOrigin.edgeViolation?`). The repository
passes also check compiled `.olean` header imports with
`RepoOrigin.importViolation?` and `CorrOrigin.importViolation?`:

- **Pass 1 (`RepoOrigin`):** `.foundation` (`foundation-lock.json`) and
  `.repo (.trusted .vetted | .trusted (.candidate f) | .theory)`.
  `library-lock.json` is never admitted in repository audits.
- **Pass 2 (`CorrOrigin`):** `.foundation`, `.sysrootFoundation` (authenticated
  sysroot `{Init,Std,Lean}*`), `.vendorMiri` (`UPSTREAM_PIN.json`), and
  `.repo role`.
- **Target Pass (`TargetOrigin`):** `.foundation`, `.library`
  (`library-lock.json`, replayed onto `foundation` when logically reached), and
  `.source role` (`TargetRole`).
-/

open Lean

namespace TrustedBoundary

/-! ## Domain types and per-pass authority lattices -/

/-- Lists the closed set of subsystem feature identifiers allowed in
`-- anneal-trust-tier: candidate:<feature>`. -/
def validCandidateFeatures : List Name :=
  [`refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

/-- Represents the module-level trust tier declared by a `Trusted` module via
its `-- anneal-trust-tier:` directive. -/
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

/-- Classifies a first-party Anneal repository `.lean` module (`trusted/` vs.
`theory/` and `correspondence/`). Every `Trusted` module carries its required
`TrustTier`, while proof/theory modules carry none; illegal combinations (a
`Trusted` module without a tier or a `theory/` module with one) are
unrepresentable. -/
inductive SourceRole where
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

/-- Partitions every loaded module in Pass 1 (`"audit"`). `library-lock.json`
applies exclusively to `targetAudit`, making `.library`, `.sysrootFoundation`,
and `.vendorMiri` unrepresentable in Pass 1. -/
inductive RepoOrigin where
  | foundation
  | repo (role : SourceRole)
  deriving BEq, DecidableEq

/-- Return `none` when Pass 1 permits a constant `cName` in `src` to reference
`dep` in module `depOrigin` (`dst`), or `some message` when forbidden:

- **Origin rule:** `.trusted _` constants may reference only `.foundation` or
  `.trusted _` constants (never `.theory`).
- **Vetted rule:** `.trusted .vetted` constants may reference only `.foundation`
  or `.trusted .vetted` constants (never `.trusted (.candidate _)`). -/
def RepoOrigin.edgeViolation? (cName : Name) (src : RepoOrigin)
    (dep depOrigin : Name) (dst : RepoOrigin) : Option String :=
  match src, dst with
  | .foundation, .foundation => none
  | .foundation, .repo _ =>
    some s!"authority violation: {cName} references {dep} from {depOrigin}"
  | .repo (.trusted .vetted), .foundation
  | .repo (.trusted .vetted), .repo (.trusted .vetted) => none
  | .repo (.trusted .vetted), .repo (.trusted depTier) =>
    some s!"vetted constant {cName} references {depTier.render} constant {dep}"
  | .repo (.trusted _), .repo .theory =>
    some (s!"Trusted constant {cName} references {dep} from " ++
      s!"non-Trusted module {depOrigin}")
  | .repo (.trusted (.candidate _)), .foundation
  | .repo (.trusted (.candidate _)), .repo (.trusted _) => none
  | .repo .theory, .foundation | .repo .theory, .repo _ => none

/-- Return `none` when the compiled `.olean` header of Pass 1 module `m` in
`src` may import module `imp` in `dst`, or `some message` when forbidden.

Module imports are coarser than constant references: the `vetted` umbrella
`Trusted.lean` imports `candidate:<feature>` modules without referencing their
constants, and `edgeViolation?` separately checks every constant reference.
Imports still preserve origin separation:

- `.foundation` modules import only `.foundation` modules.
- `.trusted _` modules never import `.theory` modules. -/
def RepoOrigin.importViolation? (m : Name) (src : RepoOrigin) (imp : Name)
    (dst : RepoOrigin) : Option String :=
  match src, dst with
  | .foundation, .foundation => none
  | .foundation, .repo _ =>
    some s!"foundation module {m} cannot import {imp}"
  | .repo (.trusted _), .repo .theory =>
    some s!"Trusted module {m} cannot import non-Trusted module {imp}"
  | .repo (.trusted _), .foundation | .repo (.trusted _), .repo (.trusted _) =>
    none
  | .repo .theory, .foundation | .repo .theory, .repo _ => none

/-- Partitions every loaded module in Pass 2 (`"correspondence-audit"`). -/
inductive CorrOrigin where
  | foundation
  | sysrootFoundation
  | vendorMiri
  | repo (role : SourceRole)
  deriving BEq, DecidableEq

/-- Return `none` when Pass 2 permits a constant `cName` in `src` to reference
`dep` in module `depOrigin` (`dst`), or `some message` when forbidden:

- External foundation/vendor origins never reference repository declarations,
  and `.foundation` never references `.sysrootFoundation` or `.vendorMiri`.
- `.trusted .vetted` constants remain isolated to `.foundation` and
  `.trusted .vetted` (never `.sysrootFoundation`, `.vendorMiri`, or
  `.trusted (.candidate _)`).
- `.trusted (.candidate _)` constants (such as `Trusted.Correspondence`) may
  reference `.foundation`, `.sysrootFoundation`, `.vendorMiri`, or
  `.trusted _`, never `.theory`. -/
def CorrOrigin.edgeViolation? (cName : Name) (src : CorrOrigin)
    (dep depOrigin : Name) (dst : CorrOrigin) : Option String :=
  match src, dst with
  | .foundation, .foundation => none
  | .foundation, .sysrootFoundation | .foundation, .vendorMiri
  | .foundation, .repo _ =>
    some s!"authority violation: {cName} references {dep} from {depOrigin}"
  | .sysrootFoundation, .foundation | .sysrootFoundation, .sysrootFoundation =>
    none
  | .sysrootFoundation, .vendorMiri | .sysrootFoundation, .repo _ =>
    some s!"authority violation: {cName} references {dep} from {depOrigin}"
  | .vendorMiri, .foundation | .vendorMiri, .sysrootFoundation
  | .vendorMiri, .vendorMiri => none
  | .vendorMiri, .repo _ =>
    some s!"authority violation: {cName} references {dep} from {depOrigin}"
  | .repo (.trusted .vetted), .foundation
  | .repo (.trusted .vetted), .repo (.trusted .vetted) => none
  | .repo (.trusted .vetted), .sysrootFoundation
  | .repo (.trusted .vetted), .vendorMiri =>
    some (s!"vetted constant {cName} references non-foundation " ++
      s!"constant {dep} from {depOrigin}")
  | .repo (.trusted .vetted), .repo (.trusted depTier) =>
    some s!"vetted constant {cName} references {depTier.render} constant {dep}"
  | .repo (.trusted _), .repo .theory =>
    some (s!"Trusted constant {cName} references {dep} from " ++
      s!"non-Trusted module {depOrigin}")
  | .repo (.trusted (.candidate _)), .foundation
  | .repo (.trusted (.candidate _)), .sysrootFoundation
  | .repo (.trusted (.candidate _)), .vendorMiri
  | .repo (.trusted (.candidate _)), .repo (.trusted _) => none
  | .repo .theory, .foundation | .repo .theory, .sysrootFoundation
  | .repo .theory, .vendorMiri | .repo .theory, .repo _ => none

/-- Return `none` when the compiled `.olean` header of Pass 2 module `m` in
`src` may import module `imp` in `dst`, or `some message` when forbidden:

- External origins never import repository modules: `.foundation` imports only
  `.foundation`, `.sysrootFoundation` imports only `.foundation` and
  `.sysrootFoundation`, and `.vendorMiri` imports no `.repo _` module.
- `.trusted _` modules never import `.theory` modules (including `theory/`
  modules such as `Anneal.MirWp` and every `correspondence/` module).

As in `RepoOrigin.importViolation?`, `edgeViolation?` separately checks every
constant reference across an admitted import. -/
def CorrOrigin.importViolation? (m : Name) (src : CorrOrigin) (imp : Name)
    (dst : CorrOrigin) : Option String :=
  match src, dst with
  | .foundation, .foundation => none
  | .foundation, .sysrootFoundation | .foundation, .vendorMiri
  | .foundation, .repo _ =>
    some s!"foundation module {m} cannot import {imp}"
  | .sysrootFoundation, .foundation | .sysrootFoundation, .sysrootFoundation =>
    none
  | .sysrootFoundation, .vendorMiri | .sysrootFoundation, .repo _ =>
    some s!"sysroot module {m} cannot import {imp}"
  | .vendorMiri, .foundation | .vendorMiri, .sysrootFoundation
  | .vendorMiri, .vendorMiri => none
  | .vendorMiri, .repo _ =>
    some s!"vendor Miri module {m} cannot import {imp}"
  | .repo (.trusted _), .repo .theory =>
    some s!"Trusted module {m} cannot import non-Trusted module {imp}"
  | .repo (.trusted _), .foundation | .repo (.trusted _), .sysrootFoundation
  | .repo (.trusted _), .vendorMiri | .repo (.trusted _), .repo (.trusted _) =>
    none
  | .repo .theory, .foundation | .repo .theory, .sysrootFoundation
  | .repo .theory, .vendorMiri | .repo .theory, .repo _ => none

/-- Represents the authority of an authenticated target source, independent of
its namespace. -/
inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq, DecidableEq

/-- Parse the closed role vocabulary shared with the Rust runner. -/
def TargetRole.parse? : String → Option TargetRole
  | "model" => some .model
  | "specification" => some .specification
  | "capture" => some .capture
  | "expected" => some .expected
  | "proof" => some .proof
  | _ => none

/-- Return `true` when a target source with `role` may depend on a source with
role `dep`. Model and specification meanings cannot depend on unreviewed proof
helpers. Capture is independent of specifications, and Expected may use all
reviewed roles. The Rust runner enforces the same rule on parsed imports. -/
def TargetRole.allows (role dep : TargetRole) : Bool :=
  match role with
  | .model => dep == .model
  | .specification => dep == .model || dep == .specification
  | .capture => dep == .model || dep == .capture
  | .expected => dep != .proof
  | .proof => true

/-- Partitions every loaded module during external target verification
(`"target-audit"`): foundation, checked libraries, and target sources. -/
inductive TargetOrigin where
  | foundation | library | source (role : TargetRole)
  deriving BEq, DecidableEq

/-- Return `none` when Target Pass permits a constant `cName` in `src` to
reference `dep` in `dst`, or `some message` when forbidden. Installed libraries
never reference target sources, and target sources obey `TargetRole.allows`. -/
def TargetOrigin.edgeViolation? (cName : Name) (src : TargetOrigin)
    (dep : Name) (dst : TargetOrigin) : Option String :=
  match src, dst with
  | .foundation, .foundation => none
  | .foundation, .library | .foundation, .source _ =>
    some s!"target authority violation {cName} references {dep}"
  | .library, .source _ =>
    some s!"installed library {cName} references target source {dep}"
  | .library, .foundation | .library, .library => none
  | .source r, .source d =>
    if r.allows d then none
    else some s!"target authority violation {cName} references {dep}"
  | .source _, .foundation | .source _, .library => none

/-- Return `true` when Target Pass permits a constant in `src` to reference
`dst`. -/
def TargetOrigin.allows (src dst : TargetOrigin) : Bool :=
  (src.edgeViolation? .anonymous .anonymous dst).isNone

/-! ## JSON IPC and environment-loading helpers -/

/-- Throw a policy-rejection error prefixed with `"policy:"` (exit code 1). -/
def fail (message : String) : IO α :=
  throw <| IO.userError s!"policy:{message}"

/-- Preserve the kernel's result/error distinction in inspector reporting.
The pinned API calls these "Exceptions that can be raised by the kernel when
type checking new declarations" and includes resource and internal failures.
Treat the entire exception channel conservatively as operational, including
validation errors on deliberately malformed serialized proofs. All still reject;
only a completed comparison or an explicit policy check justifies policy:.
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean#L259-L279
-/
def kernelResult (operation : String) (result : Except Kernel.Exception α) :
    IO α := do
  match result with
  | .ok value => return value
  | .error error =>
    let detail ← (error.toMessageData {}).toString
    -- Keep a fixed operational prefix even if diagnostic names contain policy:.
    throw <| IO.userError s!"kernel operation failed ({operation}): {detail}"

/-- A completed false comparison is a policy mismatch; an exception is not.
The pinned isDefEqGuarded uses "else false" for errors, so it erases precisely
this reporting distinction. Call the unguarded Except API at each equality gate.
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean#L2795-L2799
-/
def requireKernelEquality (operation mismatch : String)
    (result : Except Kernel.Exception Bool) : IO Unit := do
  unless (← kernelResult operation result) do fail mismatch

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
with `level := .private`.

- In `"preflight"`, `extensions := true` loads the authenticated foundation's
  parser extensions and initializers. Parsing source commands does not elaborate
  them, but this imported runtime code is trusted.
- In `"audit"` and `"target-audit"`, `extensions := false` skips module
  initializers and persistent extension-state reconstruction callbacks. Raw
  serialized extension entries remain in module data; logically reached
  declarations still undergo kernel replay.
- `"target-audit"` must never pass `extensions := true`; its compiler-attribute
  checks read those raw entries. The pinned `finalizeImport` attaches each
  module's serialized entries to every registered extension before, and
  regardless of, its `loadExts` branch. That branch calls each extension's
  import callback and requires `enableInitializersExecution` to run every
  imported `[init]` declaration, such as a target `initialize` block.
  https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean#L2376-L2404

The pinned importer warns that loading extensions "may use the interpreter"
and requires `enableInitializersExecution`. These are runtime effects, distinct
from checking declarations in a kernel environment.
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean#L2427-L2431 -/
def importEnv (j : Json) (roots : Array Name)
    (extensions := false) : IO Environment := do
  let arts ← artifacts j
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  finalizeImportedEnv env

/-- Import `roots` at `trustLevel := 0` with `plugins := #[]` and
`level := .private` using the configured search path.

- In `"correspondence-preflight"`, `extensions := true` (with
  `level := .private` and `enableInitializersExecution`) loads the Pass 2 union
  compile environment (`foundation`, Pass 1 `trusted/`, compiled untrusted Pass
  1 `theory/`, and pinned `vendorMiri`) so `Parser.parseCommand` sees unscoped
  syntax visible to `lean` during Pass 2 compilation and
  `collectScopedExtensionNamespaces` sees every namespace with scoped
  extensions. Doing so runs pinned vendored `[init]` initializers (via
  `finalizePersistentExtensions` -> `runInitAttrs`, which can register
  user-defined environment extensions), evaluates pinned vendored tactic
  `elab`s (via `KeyedDeclsAttribute.ofOLeanEntry` / `evalConstCheck`), and
  deserializes compiled Pass 1 `theory/` extension entries (limited to
  plain-data entries by Pass 1's closed attribute allowlist) inside the
  inspector process. Human review of pinned vendored compile-time code is the
  security control against vendored side effects.
- In `"correspondence-audit"`, `extensions := false` skips module initializers
  and persistent extension-state reconstruction callbacks. -/
def importCorrEnv (roots : Array Name) (extensions := false) :
    IO Environment := do
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private)
  finalizeImportedEnv env

/-- Verify that the import DAG recorded in the `.olean` headers of `env` is
identical to the admitted `"graph"` from `"preflight"` or `"headers"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do
    fail "compiled module/import DAG differs from admitted DAG"

/-! ## Phase 1: syntactic header and source preflight -/

/-- Lists the module header syntax kinds permitted in source files.
Module-system and import modifiers (`moduleTk`, `public`, `meta`, `all`) are
excluded, so the `SyntaxNodeKind` check alone rejects every header modifier. -/
def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.prelude, ``Parser.Module.import]

/-- Lists the top-level command syntax kinds permitted in source files.
Commands such as `#eval`, `#check`, `macro`, `syntax`, `elab`, `notation`,
`infix`, `initialize`, `set_option`, and `axiom` are excluded. -/
def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

/-- Lists the declaration syntax kinds permitted inside
`Parser.Command.declaration`. The `axiom`, `example`, and `coinductive` kinds
are excluded. -/
def allowedDeclarationKinds : List Name := [
  ``Parser.Command.abbrev, ``Parser.Command.definition,
  ``Parser.Command.theorem, ``Parser.Command.opaque,
  ``Parser.Command.instance, ``Parser.Command.inductive,
  ``Parser.Command.classInductive, ``Parser.Command.structure]

/-- Lists the command and declaration structural sub-node kinds permitted in
source files. The list excludes `unsafe`, `partial`, `meta`, `nonrec`,
`openScoped`, `derivingClass`, `computedFields`, and termination or fixpoint
clauses (`terminationBy`, `decreasingBy`, `partialFixpoint`,
`coinductiveFixpoint`, and `inductiveFixpoint`). -/
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

/-- Lists the pure term, binder, pattern-matching, structure-instance, literal,
and attribute-application syntax kinds permitted in both `Trusted` and `theory/`
modules. The list excludes `byTactic` (permitted only in `theory/`), `sorry`,
`unsafe`, `byElab`, `includeStr`, `set_option`, `scoped` and `local` attribute
kinds, `do` notation, string interpolation, quotations, and reflection macros
(`decl_name%`, `with_decl_name%`, and `private_decl%`). -/
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

/-- Lists the standard `Init.*` notation syntax kinds admitted from the
authenticated foundation parser environment. -/
def allowedNotationSyntaxKinds : List Name := [
  `term!_, `termIfThenElse, `termDepIfThenElse, `«term[_]»,
  `«term_&&_», `«term_||_», `«term_+_», `«term_-_», `«term_*_»,
  `«term_::_», `«term_++_», `«term_<_», `«term_≤_», `«term_>_»,
  `«term_≥_», `«term_==_», `«term_!=_», `«term_=_», `«term_≠_»,
  `«term__[_]_?», `«term_×_», `«term_↔_», `«term_∈_», `«term_∧_»,
  `«term_∨_», `«term¬_», `«term∃_,_», `«term‹_›», `Lean.cdot, `Lean.cdotTk]

/-- Lists the tactic syntax kinds permitted only in `SourceRole.theory`
(`theory/` and `correspondence/`) modules. `Trusted` modules are tactic-free
(`byTactic` is excluded from `allowedTrustedSyntaxKinds`). Even in `theory/`,
the list excludes effectful or trust-bypassing tactics (`native_decide`,
`decide!`, `bv_decide`, `rfl'`, `sorry`, `run_tac`, `sleep`, `dbg_trace`,
`unhygienic`, and `grind`) and tactic configuration items such as `+native` and
`+kernel`, which parse as `Parser.Tactic.configItem`. -/
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

/-- Defines the syntax node kinds permitted in `SourceRole.trusted` (`trusted/`)
modules: pure declarations, types, and term-mode proofs only. -/
def allowedTrustedSyntaxKinds : NameSet :=
  .ofList <|
    allowedHeaderKinds ++
    allowedCommandKinds ++
    allowedDeclarationKinds ++
    allowedCommandSyntaxKinds ++
    allowedTermSyntaxKinds ++
    allowedNotationSyntaxKinds

/-- Defines the syntax node kinds permitted in `SourceRole.theory` (`theory/`
and `correspondence/`) modules (`allowedTrustedSyntaxKinds` extended with
`allowedTheoryTacticKinds`). -/
def allowedTheorySyntaxKinds : NameSet :=
  allowedTrustedSyntaxKinds ++ .ofList allowedTheoryTacticKinds

namespace SourceRole

/-- Return the closed `SyntaxNodeKind` allowlist for a repository source
module's role. -/
def allowedSyntaxKinds : SourceRole → NameSet
  | .trusted _ => allowedTrustedSyntaxKinds
  | .theory => allowedTheorySyntaxKinds

/-- Render the optional `"trustTier"` JSON wire value for a source module. -/
def renderTier? : SourceRole → Option String
  | .trusted tier => some tier.render
  | .theory => none

end SourceRole

/-- Lists the attributes permitted on declarations. Compiler-override and
metaprogramming attributes (such as `extern`, `implemented_by`, `csimp`, `init`,
`macro`, and `elab_as_elim`) are excluded. -/
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

/-- Determine the `SourceRole` of `moduleName` from its name and the
`-- anneal-trust-tier: <tier>` directive in `text`. Every `Trusted` module must
declare a single valid `TrustTier`, and non-`Trusted` (`theory/` and
`correspondence/`) modules may not declare one. -/
def extractSourceRole (moduleName : Name) (text : String) : IO SourceRole := do
  let isTrustedModule :=
    moduleName == `Trusted || moduleName.getRoot == `Trusted
  let directives := (text.splitOn "\n").filterMap fun rawLine =>
    (rawLine.trimAscii.toString.dropPrefix? "-- anneal-trust-tier:").map
      (·.trimAscii.toString)
  match isTrustedModule, directives with
  | false, [] => pure .theory
  | false, _ :: _ =>
    fail (s!"trust tier directive is only allowed in Trusted modules " ++
      s!"({moduleName})")
  | true, [] =>
    fail ("missing `-- anneal-trust-tier: vetted` or " ++
      s!"`-- anneal-trust-tier: candidate:<feature>` in {moduleName}")
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
      fail ("only `open` and `variable` commands are permitted on the " ++
        "LHS of `in`")
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

/-- Collect every namespace that registers at least one scoped entry in any
registered `ScopedEnvExtension` of `env` (including
`Lean.Parser.parserExtension` scoped syntax/notations,
`Lean.Elab.macroAttribute` scoped macros, scoped elaborators, scoped
attributes, scoped instances, and any custom vendor `ScopedEnvExtension`). -/
def collectScopedExtensionNamespaces (env : Environment) : IO NameSet := do
  let exts ← scopedEnvExtensionsRef.get
  let mut acc : NameSet := {}
  for ext in exts do
    for (ns, _) in (ext.ext.getState env).scopedEntries.map do
      acc := acc.insert ns
  return acc

/-- Collect every non-empty strict prefix of every namespace in
`scopedNamespaces`. Retaining prefixes alongside existing namespaces in
`openDecls` ensures multi-step relative `open` chains (such as `open Miri`
followed by `open ScopedSyntax`) cannot evade `scopedNamespaces` even when a
decoy namespace exists in the union `parserEnv`. -/
def collectScopedNamespacePrefixes (scopedNamespaces : NameSet) : NameSet :=
  let rec insertPrefixes (acc : NameSet) : Name → NameSet
    | .anonymous => acc
    | ns@(.str p _) => insertPrefixes (acc.insert ns) p
    | _ => acc
  scopedNamespaces.foldl (init := {}) fun acc ns =>
    match ns with
    | .str p _ => insertPrefixes acc p
    | _ => acc

/-- Enumerate every namespace that `Lean.ResolveName.resolveNamespace` could
resolve `id` to under *any* sub-environment of `parserEnv` given lexical
namespace `currNs` and conservative `openDecls`:
- every non-empty prefix `p` of `currNs` with `id` appended (`p ++ id`),
- the root candidate `id.replacePrefix rootNamespace .anonymous`, and
- every `ns ++ id` for each `OpenDecl.simple ns _` in `openDecls`.

Checking every candidate—instead of stopping at the innermost existing
namespace in the union `parserEnv` as `resolveNamespaceUsingScope?` does—closes
decoy-namespace shadowing when an unimported module declares a namespace with
the same suffix as a real scoped namespace. -/
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

/-- Reject `ns` if it registers any scoped entry in `scopedNamespaces`. -/
def rejectScopedNamespace (scopedNamespaces : NameSet) (how : String)
    (ns : Name) : IO Unit := do
  if scopedNamespaces.contains ns then
    fail s!"cannot {how} namespace {ns} with scoped syntax or extensions"

/-- Push each component of `header` as a lexical `namespace` or `section` scope
onto `(parserEnv, scopes)`, rejecting any newly entered namespace present in
`scopedNamespaces` and registering namespaces in `parserEnv` (matching
`Lean.Elab.Command.addScopes`). -/
def pushParseScopes (scopedNamespaces : NameSet) (isNewNamespace : Bool)
    (header : Name) (parserEnv : Environment) (scopes : List ParseScope) :
    IO (Environment × List ParseScope) := do
  match header with
  | .anonymous => return (parserEnv, scopes)
  | .str p seg =>
    let (parserEnv, scopes) ←
      pushParseScopes scopedNamespaces isNewNamespace p parserEnv scopes
    let top := scopes.head!
    let newNs := if isNewNamespace then Name.mkStr top.currNamespace seg
      else top.currNamespace
    if isNewNamespace then
      rejectScopedNamespace scopedNamespaces "enter" newNs
    let parserEnv := parserEnv.registerNamespace newNs
    let parserEnv := Parser.parserExtension.pushScope parserEnv
    let newScope : ParseScope :=
      { top with header := seg, currNamespace := newNs }
    return (parserEnv, newScope :: scopes)
  | _ => fail s!"invalid scope name {header}"

/-- Check that every namespace prefix opened by `expandNamespacedDeclaration`
for declaration identifier `id` (excluding `_root_`-prefixed names, matching
`Lean.Elab.Command.expandDeclNamespace?`) is absent from `scopedNamespaces`,
and register each prefix namespace in `parserEnv`. -/
def checkDeclNamespacePrefixes (scopedNamespaces : NameSet) (currNs : Name)
    (id : Name) (parserEnv : Environment) : IO Environment := do
  if (`_root_).isPrefixOf id then
    return parserEnv
  let rec walkPrefix (ns : Name) (env : Environment) :
      IO (Name × Environment) := do
    match ns with
    | .anonymous => return (currNs, env)
    | .str p seg =>
      let (base, env) ← walkPrefix p env
      let full := Name.mkStr base seg
      rejectScopedNamespace scopedNamespaces "declare in" full
      return (full, env.registerNamespace full)
    | _ => fail s!"invalid declaration namespace {id}"
  match id with
  | .str .anonymous _ => return parserEnv
  | .str pre _ =>
    let (_, env) ← walkPrefix pre parserEnv
    return env
  | _ => return parserEnv

/-- Extract the user-supplied declaration identifier from an allowlisted
`Parser.Command.declaration` syntax node, if present. -/
def declarationIdent? (stx : Syntax) : Option Name :=
  let decl := stx[1]
  if decl.getKind == ``Parser.Command.instance then
    if decl[3].isNone then none else some decl[3][0][0].getId
  else
    some decl[1][0].getId

/-- Update lexical scope state `(parserEnv, scopes)` for a validated command
`stx`, rejecting any `open`, `open ... in`, `mutual` preamble, `namespace`, or
multi-component declaration whose entered namespace or candidate `open`
resolution belongs to `scopedNamespaces`. -/
partial def applyCommandScope (scopedNamespaces scopedPrefixes : NameSet)
    (parserEnv : Environment) (scopes : List ParseScope) (stx : Syntax) :
    IO (Environment × List ParseScope) := do
  let k := stx.getKind
  if k == ``Parser.Command.namespace then
    pushParseScopes scopedNamespaces true stx[1].getId parserEnv scopes
  else if k == ``Parser.Command.section then
    if stx[2].isNone then
      let top := scopes.head!
      let parserEnv := Parser.parserExtension.pushScope parserEnv
      return (parserEnv, { top with header := "" } :: scopes)
    else
      pushParseScopes scopedNamespaces false stx[2][0].getId parserEnv scopes
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
    let mut openDecls := top.openDecls
    let openDecl := stx[1]
    unless openDecl.isOfKind ``Parser.Command.openSimple do
      fail s!"unsupported open command {openDecl.getKind}"
    let hasOpenDecl (ods : List OpenDecl) (ns : Name) : Bool :=
      ods.any fun
        | OpenDecl.simple existing _ => existing == ns
        | _ => false
    for idStx in openDecl[0].getArgs do
      let id := idStx.getId
      let candidates :=
        candidateOpenNamespaces top.currNamespace openDecls id
      let mut added := false
      for ns in candidates do
        rejectScopedNamespace scopedNamespaces "open" ns
        if parserEnv.isNamespace ns || scopedPrefixes.contains ns then
          if !hasOpenDecl openDecls ns then
            openDecls := OpenDecl.simple ns [] :: openDecls
          added := true
      if !added then
        let stripped := id.replacePrefix rootNamespace .anonymous
        if !hasOpenDecl openDecls stripped then
          openDecls := OpenDecl.simple stripped [] :: openDecls
    return (parserEnv, { top with openDecls := openDecls } :: scopes.tail!)
  else if k == ``Parser.Command.in then
    let top := scopes.head!
    let tmpEnv := Parser.parserExtension.pushScope parserEnv
    let (tmpEnv, tmpScopes) ←
      applyCommandScope scopedNamespaces scopedPrefixes tmpEnv (top :: scopes)
        stx[0]
    let (tmpEnv, _) ←
      applyCommandScope scopedNamespaces scopedPrefixes tmpEnv tmpScopes stx[2]
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.mutual then
    let top := scopes.head!
    let mut tmpEnv := Parser.parserExtension.pushScope parserEnv
    let mut tmpScopes := top :: scopes
    for child in stx[1].getArgs do
      (tmpEnv, tmpScopes) ←
        applyCommandScope scopedNamespaces scopedPrefixes tmpEnv tmpScopes child
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.declaration then
    match declarationIdent? stx with
    | some id =>
      let env ← checkDeclNamespacePrefixes scopedNamespaces
        scopes.head!.currNamespace id parserEnv
      return (env, scopes)
    | none => return (parserEnv, scopes)
  else
    return (parserEnv, scopes)

/-- Parse and validate all commands in `ctx` starting from `state` and
`messages` using the authenticated `parserEnv`, lexical scope stack `scopes`,
`scopedNamespaces`, `scopedPrefixes`, and the role's `allowedKinds`, without
elaborating the inspected commands. -/
partial def parseAndInspectCommands (ctx : Parser.InputContext)
    (scopedNamespaces scopedPrefixes : NameSet) (parserEnv : Environment)
    (scopes : List ParseScope) (moduleName : Name) (allowedKinds : NameSet)
    (state : Parser.ModuleParserState) (messages : MessageLog) : IO Unit := do
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
    fail s!"command parser error in {moduleName}"
  if stx.isOfKind ``Parser.Command.eoi then
    return ()
  if nextState.pos <= previous then
    throw <| IO.userError "parser made no progress"
  unless allowedCommandKinds.contains stx.getKind do
    fail s!"unsupported command {stx.getKind}"
  inspectSyntax allowedKinds stx
  let (nextEnv, nextScopes) ←
    applyCommandScope scopedNamespaces scopedPrefixes parserEnv scopes stx
  parseAndInspectCommands ctx scopedNamespaces scopedPrefixes nextEnv nextScopes
    moduleName allowedKinds nextState nextMessages

/-- Parse and validate a single repository `.lean` source file during
`"preflight"` or `"correspondence-preflight"`. -/
def inspectSource (scopedNamespaces scopedPrefixes : NameSet)
    (parserEnv : Environment) (moduleName : Name)
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
  let rootScope : ParseScope :=
    { header := "", currNamespace := .anonymous, openDecls := [] }
  parseAndInspectCommands ctx scopedNamespaces scopedPrefixes parserEnv
    [rootScope] moduleName allowedKinds initial log
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("trustTier", toJson role.renderTier?)]

/-- Read only a source header (`"headers"`). Target elaboration is deliberately
separate from repository command admission: authored macros and tactics may use
arbitrary syntax, while their final logical dependencies must pass kernel
replay. -/
def inspectHeader (moduleName : Name) (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, state, messages) ← Parser.parseHeader ctx
  if messages.hasErrors || state.recovering then
    fail s!"header parser error in {moduleName}"
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson (Elab.HeaderSyntax.imports header))]

/-! ## Shared kernel-environment combinators -/

/-- Collect every constant referenced inside `pending` with a pure DAG
traversal. The `seen` set avoids re-traversing shared subterms of kernel
`Expr`s. -/
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

/-- Return the kernel dependency edges of `ci`: every constant in its type and
value, the other members of its mutual block, and its inductive structure
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

/-- Return the human-readable kind tag for a kernel `ConstantInfo`. -/
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Look up kernel constant `n` in `env.checked`. -/
def lookupConst (env : Environment) (n : Name)
    (label : String := "dependency declaration") : IO ConstantInfo := do
  let some ci := env.checked.get.find? n
    | fail s!"missing {label} {n}"
  return ci

/-- Return the defining module name for kernel constant `n` in `env`. -/
def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n
    | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]?
    | fail s!"invalid module index: {n}"
  return mod.module

/-- Return the defining module name and origin classification `ρ` for constant
`n` in `env`, rejecting constants from any module outside `roles`. -/
def constProvenance (env : Environment) (roles : Std.HashMap Name ρ)
    (n : Name) (foreignKind : String := "module") : IO (Name × ρ) := do
  let orig ← origin env n
  let some role := roles.get? orig
    | fail s!"foreign {foreignKind} {orig} for {n}"
  return (orig, role)

/-- Insert `m ↦ role` into `roles`, rejecting overlapping role assignments. -/
def insertRole (roles : Std.HashMap Name ρ) (m : Name) (role : ρ)
    (dupPrefix : String := "overlapping module role for") :
    IO (Std.HashMap Name ρ) := do
  if roles.contains m then fail s!"{dupPrefix} {m}"
  return roles.insert m role

/-- Parse `"moduleTiers"` and verify that every entry names a distinct module in
`trusted` with a valid `TrustTier`. -/
def parseModuleTiers (j : Json) (trusted : Array Name) :
    IO (Std.HashMap Name TrustTier) := do
  let tierEntries ← field (α := Array (String × String)) j "moduleTiers"
  tierEntries.foldlM (init := ({} : Std.HashMap Name TrustTier))
    fun acc (mStr, rawTier) => do
      let m := mStr.toName
      if acc.contains m then fail s!"duplicate module tier for {m}"
      unless trusted.contains m do
        fail s!"trust tier declared for non-Trusted module {m}"
      let some tier := TrustTier.parse? rawTier
        | fail s!"invalid trust tier {rawTier} for {m}"
      return acc.insert m tier

/-- Enforce the logical safety preconditions required before passing any
non-foundation `ConstantInfo` to `Kernel.Environment.replay`: no `unsafe` or
`partial` modifiers, no quotient primitives, and a stored body whenever
`hasValue true`.

The pinned replay never sends `unsafe` or `partial` declarations to the kernel
("We skip unsafe constants, and also partial constants."), so replay alone
would accept them without checking them:
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L176-L185 -/
def ensureReplayableConstant (unsafeLabel : String) (ctxSuffix : String)
    (ci : ConstantInfo) : IO Unit := do
  if ci.isUnsafe || ci.isPartial then
    fail s!"unsafe/partial {unsafeLabel} {ci.name}{ctxSuffix}"
  if ci matches .quotInfo _ then
    fail s!"unexpected quotient primitive {ci.name}{ctxSuffix}"
  if ci.hasValue true && (ci.value? true).isNone then
    fail s!"missing stored body {ci.name}"

/-- Enforce per-constant policy invariants on a constant `ci` defined in Anneal
repository module `m` with `SourceRole` `role` (shared across Pass 1 and
Pass 2):

- Non-`Trusted` modules cannot declare constants in the `Trusted` root
  namespace (`privateToUserName` strips any `_private.<mod>.0` prefix first so
  `private` declarations inside `namespace Trusted` are also caught).
- Non-`Trusted` modules cannot declare `opaque` constants.
- No repository module may declare `unsafe`, `partial`, `axiom`, or `quot`
  constants, or omit a definition body. -/
def validateRepoConstant (m : Name) (role : SourceRole)
    (ci : ConstantInfo) : IO Unit := do
  let isTrusted := role matches .trusted _
  if !isTrusted && (privateToUserName ci.name).getRoot == `Trusted then
    fail (s!"non-Trusted module {m} cannot declare constant {ci.name} " ++
      "in Trusted namespace")
  if !isTrusted && (ci matches .opaqueInfo _) then
    fail s!"opaque declaration {ci.name} in {m} is not allowed outside Trusted"
  if ci.isAxiom then
    fail (if isTrusted then
      s!"Trusted axiom {ci.name}"
    else
      s!"strict axiom declaration {ci.name} in {m}")
  if isTrusted then
    ensureReplayableConstant "Trusted declaration" "" ci
  else
    ensureReplayableConstant "declaration" s!" in {m}" ci

/-- Enforce `violation?` across every kernel dependency edge of `locals`. -/
def checkDeclarationEdges (env : Environment) (roles : Std.HashMap Name ρ)
    (locals : Std.HashMap Name ConstantInfo)
    (violation? : Name → ρ → Name → Name → ρ → Option String) :
    IO Unit := do
  for (cName, ci) in locals do
    let (_, cRole) ← constProvenance env roles cName
    for dep in ← declarationEdges ci do
      let (depOrigin, depRole) ← constProvenance env roles dep
      if let some msg := violation? cName cRole dep depOrigin depRole then
        fail msg

/-- Enforce `violation?` on every import recorded in the compiled `.olean`
header (`data.imports`) of module `m` with origin `role`, rejecting imports of
modules outside `roles`. -/
def checkHeaderImports (roles : Std.HashMap Name ρ) (m : Name) (role : ρ)
    (data : ModuleData) (violation? : Name → ρ → Name → ρ → Option String) :
    IO Unit := do
  for imp in data.imports do
    let some impRole := roles.get? imp.module
      | fail s!"foreign import {imp.module} in {m}"
    if let some msg := violation? m role imp.module impRole then
      fail msg

/-- Compute the transitive kernel dependency closure of `pending`, run optional
per-constant `onVisit` checks, verify that every reachable axiom belongs to
`axioms`, and return the sorted reached axioms and the set of reached
constants. -/
partial def closure (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO (Name × ρ)) (axioms : Array (String × String))
    (pending : List Name)
    (onVisit : Name → Name → ρ → ConstantInfo → IO Unit :=
      fun _ _ _ _ => pure ())
    (visited : NameSet := {})
    (reachedAxioms : NameSet := {}) : IO (Array Name × NameSet) := do
  match pending with
  | [] => return (reachedAxioms.toArray.qsort Name.lt, visited)
  | n :: rest =>
    if visited.contains n then
      closure lookup provenance axioms rest onVisit visited reachedAxioms
    else
      let visited := visited.insert n
      let (m, role) ← provenance n
      let ci ← lookup n
      onVisit n m role ci
      let reachedAxioms ← if ci.isAxiom then do
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        pure (reachedAxioms.insert n)
      else
        pure reachedAxioms
      let deps ← declarationEdges ci
      closure lookup provenance axioms (deps.toList ++ rest) onVisit visited
        reachedAxioms

/-- Reconcile one serialized inventory value with the selected declaration.
Pinned modules may repeat a theorem with another proof of the same proposition;
every such proof still needs its own dependency closure and fresh kernel check.
Definitions and source declarations cannot change their stored meaning. -/
def inventoryAlternates (stored ci : ConstantInfo) (pinned : Bool) :
    IO (Array ConstantInfo) := do
  unless stored.type == ci.type do
    fail s!"stored declaration type differs from inventory {ci.name}"
  -- Equal proof expressions do not establish equal universes or mutual-block
  -- dependencies: declarationEdges also follows ci.all. Check this metadata
  -- before the equal-value fast path, so it cannot discard an unexamined edge.
  -- The pinned importer also requires matching levelParams and all, while
  -- saying "we do not check whether the theorem `value` field match". Preserve
  -- that distinction locally rather than relying on an earlier import check.
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean#L2261-L2278
  match pinned, stored, ci with
  | true, .thmInfo a, .thmInfo b =>
    unless a.levelParams == b.levelParams && a.all == b.all do
      fail s!"inconsistent pinned theorem metadata {ci.name}"
  | _, _, _ => pure ()
  if stored.value? true == ci.value? true then return #[]
  match pinned, stored, ci with
  | true, .thmInfo _, .thmInfo _ =>
    -- Replay may reuse a selected theorem already in its foundation base.
    -- Retain both values so that optimization cannot hide either proof body.
    return #[stored, ci]
  | _, _, _ => fail s!"stored declaration differs from inventory {ci.name}"

/-- Validate and record the `.olean` inventory (`constants` and
`extraConstNames`) of one Anneal repository module `mName` (`srcRole`) across
Pass 1 and Pass 2. -/
def collectRepoModuleConstants (env : Environment) (roles : Std.HashMap Name ρ)
    (mName : Name) (srcRole : SourceRole) (data : ModuleData)
    (locals : Std.HashMap Name ConstantInfo) (extraNames : NameSet) :
    IO (Std.HashMap Name ConstantInfo × NameSet) := do
  let mut locals := locals
  let mut extraNames := extraNames
  for ci in data.constants do
    if locals.contains ci.name then
      fail s!"duplicate declaration {ci.name}"
    let (orig, _) ← constProvenance env roles ci.name
    unless orig == mName do
      fail s!"inventory origin mismatch {ci.name}"
    let stored ← lookupConst env ci.name "stored declaration"
    discard <| inventoryAlternates stored ci false
    validateRepoConstant mName srcRole ci
    locals := locals.insert ci.name ci
  for n in data.extraConstNames do
    let (orig, _) ← constProvenance env roles n
    unless orig == mName do
      fail s!"IR helper provenance mismatch {n}"
    if (env.checked.get.find? n).isSome then
      unless locals.contains n do
        fail s!"uninventoried kernel compiler helper {n}"
    else if srcRole matches .trusted _ then
      extraNames := extraNames.insert n
  return (locals, extraNames)

/-- Check each alternate under a fresh name, bypassing replay's duplicate
optimization while preserving the declaration's type and universe parameters.
The pinned replay rule says "Ignore duplicate theorems" after comparing their
metadata; it does not check the duplicate proof value:
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L85-L97
-/
def checkAlternateProofs (replayed : Kernel.Environment)
    (alternateProofs : Array ConstantInfo) : IO Unit := do
  let checkedEnv := Environment.ofKernelEnv replayed
  let mut freshIndex := 0
  for ci in alternateProofs do
    let .thmInfo info := ci | fail "non-theorem alternate inventory body"
    let typeOfType ← kernelResult s!"alternate theorem type check {ci.name}"
      (Kernel.check checkedEnv {} info.type)
    requireKernelEquality s!"alternate theorem proposition comparison {ci.name}"
      s!"alternate theorem is not a proposition {ci.name}"
      (Kernel.isDefEq checkedEnv {} typeOfType (.sort .zero))
    let mut fresh := Name.num `_anneal_checked_alternate freshIndex
    while (replayed.find? fresh).isSome do
      freshIndex := freshIndex + 1
      fresh := Name.num `_anneal_checked_alternate freshIndex
    freshIndex := freshIndex + 1
    discard <| kernelResult s!"alternate pinned theorem proof check {ci.name}"
      (replayed.addDeclCore 0 0 (.thmDecl { info with name := fresh })
        (cancelTk? := none))

/-- Replay `replayMap` onto `base` with a fixed operational error prefix (so
`Lean.Replay`'s stringified `Kernel.Exception` cannot spoof `"policy:"`).
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L54-L63
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L135-L136
-/
def replayKernelEnv (base : Kernel.Environment)
    (replayMap : Std.HashMap Name ConstantInfo)
    (errPrefix : String := "kernel replay failed") :
    IO Kernel.Environment := do
  try base.replay replayMap
  catch error => throw <| IO.userError s!"{errPrefix}: {error}"

/-- Replay `replayMap` onto `base.toKernelEnv` and check all `alternateProofs`
under fresh names. -/
def replayOntoBase (base : Environment)
    (replayMap : Std.HashMap Name ConstantInfo)
    (alternateProofs : Array ConstantInfo := #[])
    (errPrefix : String := "kernel replay failed") :
    IO Kernel.Environment := do
  let replayed ← replayKernelEnv base.toKernelEnv replayMap errPrefix
  checkAlternateProofs replayed alternateProofs
  return replayed

/-- Verify that `claimName` is a universe-monomorphic `.defnInfo` definition in
`expectedClaimMod` referencing every constant in the non-empty `reqConsts`
list, and that `proofName` is a universe-monomorphic `.thmInfo` theorem in
`expectedProofMod` whose type is either `Expr.const claimName []` (when
`argName? == none`, with `claimCi.type == .sort .zero`) or
`Expr.app (Expr.const claimName []) (Expr.const argName [])` (when
`argName? == some argName`). -/
def requireClaimProof (env : Environment)
    (locals : Std.HashMap Name ConstantInfo)
    (expectedClaimMod expectedProofMod claimName : Name)
    (argName? : Option Name) (proofName : Name)
    (reqConsts : List Name) : IO Unit := do
  if reqConsts.isEmpty then
    fail s!"claim {claimName} requires a non-empty required-constants list"
  let some claimCi := locals.get? claimName
    | fail s!"missing required claim {claimName}"
  unless claimCi matches .defnInfo _ do
    fail s!"expected {claimName} to be a definition"
  unless claimCi.levelParams.isEmpty do
    fail s!"claim {claimName} must have no universe parameters"
  let claimOrig ← origin env claimName
  unless claimOrig == expectedClaimMod do
    fail (s!"expected {claimName} to be defined in " ++
      s!"{expectedClaimMod}, found {claimOrig}")
  if argName?.isNone then
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
  unless proofCi.levelParams.isEmpty do
    fail s!"theorem {proofName} must have no universe parameters"
  let proofOrig ← origin env proofName
  unless proofOrig == expectedProofMod do
    fail (s!"expected {proofName} to be defined in " ++
      s!"{expectedProofMod}, found {proofOrig}")
  match argName? with
  | none =>
    unless proofCi.type == .const claimName [] do
      fail s!"theorem {proofName} must prove {claimName} directly"
  | some argName =>
    unless proofCi.type == .app (.const claimName []) (.const argName []) do
      fail s!"theorem {proofName} must prove {claimName} {argName} directly"

/-! ## Phase 2: Pass 1 repository audit (`"audit"`) -/

/-- Build the complete map from module name to `RepoOrigin`, verifying that the
foundation, trusted, and theory module sets are pairwise disjoint and every
`Trusted` module has a valid `TrustTier`. -/
def buildRepoOrigins (j : Json) (foundation trusted theory : Array Name) :
    IO (Std.HashMap Name RepoOrigin) := do
  let tierMap ← parseModuleTiers j trusted
  let roles0 := foundation.foldl (init := ({} : Std.HashMap Name RepoOrigin))
    fun acc m => acc.insert m .foundation
  let roles1 ← trusted.foldlM (init := roles0) fun acc m => do
    let some tier := tierMap.get? m
      | fail s!"missing trust tier for Trusted module {m}"
    insertRole acc m (.repo (.trusted tier))
  theory.foldlM (init := roles1) fun acc m =>
    insertRole acc m (.repo .theory)

/-- Verify admitted Pass 1 module inventories, `.olean` header imports
(`RepoOrigin.importViolation?`), and declaration origins, and apply namespace
and logical-admission rules to repository declarations. Return all repository
constants, the compiler-only (IR) names of `Trusted` modules, and any alternate
serialized foundation theorem proofs for replay checking. -/
def verifyAndCollectLocals (env : Environment)
    (roles : Std.HashMap Name RepoOrigin) :
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
    checkHeaderImports roles m.module role data RepoOrigin.importViolation?
    match role with
    | .foundation =>
      for ci in data.constants do
        let (_, origRole) ← constProvenance env roles ci.name
        let stored ← lookupConst env ci.name "stored declaration"
        unless origRole == .foundation do
          fail s!"inventory origin mismatch {ci.name}"
        alternateProofs := alternateProofs ++
          (← inventoryAlternates stored ci true)
      for n in data.extraConstNames do
        let (_, origRole) ← constProvenance env roles n
        unless origRole == .foundation do
          fail s!"IR helper provenance mismatch {n}"
    | .repo srcRole =>
      let (nextLocals, nextExtras) ←
        collectRepoModuleConstants env roles m.module srcRole data locals
          extraNames
      locals := nextLocals
      extraNames := nextExtras
  for (n, _) in env.checked.get.constants do
    let (_, origRole) ← constProvenance env roles n
    if origRole != .foundation && !locals.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, extraNames, alternateProofs)

/-- Verify that `Trusted.MirAst` and `Trusted.MirSemantics` are loaded as
`.repo (.trusted _)` modules and `Anneal.MirWp` is loaded as a `.repo .theory`
module (whenever `requireMirWp` is `true` or any MIR/`PureLift` module is
loaded), and that the core weakest-precondition adequacy and
fault-characterization theorems and all 20 non-vacuity and parameter-boundary
canaries in `Anneal.MirWp` prove the exact `*Claim` propositions defined in
`Trusted.MirSemantics`. -/
def verifyMirWpCoreTheorems (env : Environment)
    (roles : Std.HashMap Name RepoOrigin)
    (locals : Std.HashMap Name ConstantInfo)
    (requireMirWp : Bool) : IO Unit := do
  if requireMirWp || roles.contains `Anneal.PureLift ||
      roles.contains `Trusted.MirAst ||
      roles.contains `Trusted.MirSemantics || roles.contains `Anneal.MirWp then
    unless roles.get? `Trusted.MirAst matches some (.repo (.trusted _)) do
      fail "missing required trusted module Trusted.MirAst"
    unless roles.get? `Trusted.MirSemantics matches some (.repo (.trusted _)) do
      fail "missing required trusted module Trusted.MirSemantics"
    unless roles.get? `Anneal.MirWp matches some (.repo .theory) do
      fail "missing required theory module Anneal.MirWp"
    let semMod := `Trusted.MirSemantics
    let wpMod := `Anneal.MirWp
    requireClaimProof env locals semMod wpMod
      `Trusted.MirSemantics.WpSoundnessClaim
      (some `Anneal.MirWp.wpProg)
      `Anneal.MirWp.wellFormed_and_spec_of_wp
      [`Trusted.MirSemantics.SatisfiesPost, `Trusted.MirSemantics.Diverges,
        `Trusted.MirSemantics.Behavior]
    requireClaimProof env locals semMod wpMod
      `Trusted.MirSemantics.WpFaultSoundnessClaim
      (some `Anneal.MirWp.wpFaultProg)
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
          [negClaim]),
        (`Trusted.MirSemantics.CanaryPositiveEnumExplicitReprAnnealClaim,
          `Anneal.MirWp.canary_positive_enum_explicit_repr_anneal,
          [posClaim]),
        (`Trusted.MirSemantics.CanaryPositiveZstSingleEnumAnnealClaim,
          `Anneal.MirWp.canary_positive_zst_single_enum_anneal, [posClaim]),
        (
       `Trusted.MirSemantics.CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim,
          `Anneal.MirWp.canary_negative_ub_enum_invalid_tag_and_uninit_anneal,
          [negClaim]),
        (`Trusted.MirSemantics.CanaryCrateAndBodyVerifiedAnnealClaim,
          `Anneal.MirWp.canary_crate_and_body_verified_anneal,
          [`Trusted.MirSemantics.CrateTheorem,
            `Trusted.MirSemantics.UnitTheorem,
            `Trusted.MirSemantics.BodyVerified]),
        (`Trusted.MirSemantics.CanaryMemoryLifecycleAnnealClaim,
          `Anneal.MirWp.canary_memory_lifecycle_anneal,
          [posClaim, `Trusted.MirSemantics.initState,
            `Trusted.MirSemantics.evalStep,
            `Trusted.MirSemantics.forceAllocation,
            `Trusted.MirSemantics.readBytes])] do
      requireClaimProof env locals semMod wpMod claimName none proofName
        reqConsts

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let roles ← buildRepoOrigins j foundation trusted theory
  let (locals, extraNames, alternateProofs) ← verifyAndCollectLocals env roles
  checkDeclarationEdges env roles locals RepoOrigin.edgeViolation?
  let requireMirWp := (j.getObjValAs? Bool "requireMirWp").toOption.getD true
  verifyMirWpCoreTheorems env roles locals requireMirWp
  let inventory ← locals.foldM (init := #[]) fun acc cName ci => do
    let (orig, cRole) ← constProvenance env roles cName
    match cRole with
    | .repo (.trusted tier) =>
      let deps := (← declarationEdges ci).toArray.qsort Name.lt
      return acc.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig),
        ("kind", toJson (kind ci)), ("trustStatus", toJson tier.render),
        ("dependencies", toJson deps)]
    | .foundation | .repo .theory => return acc
  let mut allLocalRoots := locals.fold (init := []) fun acc n _ => n :: acc
  for ci in alternateProofs do
    allLocalRoots := ci.name :: (← declarationEdges ci).toList ++ allLocalRoots
  let provenance := constProvenance env roles
  let (allAxioms, allVisited) ←
    closure (lookupConst env) provenance axiomPolicy allLocalRoots
  -- Replay repository constants through the kernel against only the locked
  -- foundation (`loadExts := false`).
  let base ← importEnv j foundation
  discard <| replayOntoBase base locals alternateProofs
  return Json.mkObj [
    ("graph", graph env), ("declarations", .arr inventory),
    ("kernelDeclarations", toJson inventory.size),
    ("replayedDeclarations", toJson locals.size),
    ("checkedAlternateProofs", toJson alternateProofs.size),
    ("compilerOnlyNames", toJson extraNames.size),
    ("reachableDeclarations", toJson allVisited.size),
    ("axioms", toJson allAxioms), ("replay", toJson true)]

/-! ## Phase 3: Pass 2 MIR correspondence and `lean-miri` cone audit -/

/-- Classify every loaded module in `env.header.modules` into `CorrOrigin`,
verifying that `foundation`, `sysrootFoundation`, `trusted`, `theory`, and
`vendorMiri` are pairwise disjoint, that all required modules (`foundation`,
`trusted`, `theory`, and `vendorMiri`) are loaded, and that any additional
sysroot `Init.*`, `Std.*`, or `Lean.*` module imported by `vendorMiri` belongs
to the `sysrootFoundation` allowlist whose `.olean*` artifacts `anneal-audit`
verified against `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`.

The `Lean.*` root must be admitted as a whole: several modules in the
`Miri.Interpreter.ExecutionMachine` closure (for example `Miri.Memory.InitMask`
and `Miri.TreeBorrows.TreeState`) `import Lean`, which loads the entire `Lean`
package from the pinned toolchain. Admission only classifies these modules;
`closureCorr` rejects any `unsafe` or `partial` constant that the
correspondence cone reaches, and `verifyAndCollectCorrLocals` rejects any of
their constants in the reserved `Trusted` or `Anneal` namespaces. -/
def classifyCorrModules (j : Json) (env : Environment)
    (foundation trusted theory vendorMiri : Array Name) :
    IO (Std.HashMap Name CorrOrigin) := do
  let sysrootFoundation ← names j "sysrootFoundation"
  let tierMap ← parseModuleTiers j trusted
  let roles0 := foundation.foldl (init := ({} : Std.HashMap Name CorrOrigin))
    fun acc m => acc.insert m .foundation
  let roles1 ← trusted.foldlM (init := roles0) fun acc m => do
    let some tier := tierMap.get? m
      | fail s!"missing trust tier for Trusted module {m}"
    insertRole acc m (.repo (.trusted tier))
  let roles2 ← theory.foldlM (init := roles1) fun acc m =>
    insertRole acc m (.repo .theory)
  let roles3 ← vendorMiri.foldlM (init := roles2) fun acc m =>
    insertRole acc m .vendorMiri
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for (reqMod, _) in roles3 do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod} in correspondence environment"
  let roles4 ← sysrootFoundation.foldlM (init := roles3) fun acc m =>
    insertRole acc m .sysrootFoundation
  for m in env.header.modules do
    unless roles4.contains m.module do
      fail s!"foreign module {m.module} in correspondence environment"
  return roles4

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
def constantFindRef? (ci : ConstantInfo) (targets : List Name) :
    Option Name :=
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

/-- Reject any external (`.sysrootFoundation` or `.vendorMiri`) constant `n`
declared in the reserved `Trusted` or `Anneal` root namespaces (after stripping
private prefixes). -/
def validateExternalNamespace (modName : Name) (n : Name) : IO Unit := do
  let root := (privateToUserName n).getRoot
  if root == `Trusted || root == `Anneal then
    fail (s!"external module {modName} cannot declare constant " ++
      s!"{n} in reserved {root} namespace")

/-- Validate `.olean` header imports (`CorrOrigin.importViolation?`), `.repo`
declarations, and `.vendorMiri` / `.sysrootFoundation` declarations in the
correspondence environment, returning `(repoLocals, corrLocals, vendorLocals)`.

- `repoLocals` contains all constants from Pass 1 and Pass 2 `.repo` modules.
- `corrLocals` contains the subset defined in `corrModules`
  (`trusted/correspondence/` and `correspondence/`).
- `vendorLocals` contains all unique `.vendorMiri` declarations for standalone
  kernel replay.

`.vendorMiri` and `.sysrootFoundation` modules are outside repository
`"preflight"`, so this rejects any constant they declare in the reserved
`Trusted` or `Anneal` root namespaces. For every `.vendorMiri` constant, it
also checks inventory and origin integrity, rejects `axiom`, `unsafe`, quotient
primitives, missing bodies, direct `sorryAx` references, and direct
compiler-reflection references (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
`Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`), permits identical
sibling-module `.thmInfo` duplicates (lazily synthesized equation or
`congr_simp` lemmas), and verifies completeness across
`env.checked.get.constants`. -/
def verifyAndCollectCorrLocals (env : Environment)
    (roles : Std.HashMap Name CorrOrigin) (corrModules : NameSet) :
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
    checkHeaderImports roles m.module role data CorrOrigin.importViolation?
    match role with
    | .foundation => pure ()
    | .sysrootFoundation =>
      for ci in data.constants do
        validateExternalNamespace m.module ci.name
    | .vendorMiri =>
      let mut modSeen : NameSet := {}
      for ci in data.constants do
        if modSeen.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        modSeen := modSeen.insert ci.name
        validateExternalNamespace m.module ci.name
        let (orig, origRole) ← constProvenance env roles ci.name
        unless origRole == .vendorMiri do
          fail s!"inventory origin mismatch {ci.name}"
        let stored ← lookupConst env ci.name "stored declaration"
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
    | .repo srcRole =>
      let (nextLocals, _) ←
        collectRepoModuleConstants env roles m.module srcRole data repoLocals {}
      repoLocals := nextLocals
      if corrModules.contains m.module then
        for ci in data.constants do
          corrLocals := corrLocals.insert ci.name ci
  for (n, _) in vendorLocals do
    unless vendorOrigSeen.contains n do
      fail s!"inventory origin mismatch {n}"
  for (n, _) in env.checked.get.constants do
    let (orig, origRole) ← constProvenance env roles n
    match origRole with
    | .foundation => pure ()
    | .sysrootFoundation =>
      validateExternalNamespace orig n
    | .vendorMiri =>
      unless vendorLocals.contains n do
        fail s!"uninventoried vendor Miri constant {n}"
    | .repo _ =>
      unless repoLocals.contains n do
        fail s!"uninventoried constant {n}"
  return (repoLocals, corrLocals, vendorLocals)

/-- Traverse the transitive constant-level dependency cone starting from
`pending` in the Pass 2 environment, verifying via `closure` that:

- No reachable constant is `unsafe` or `isPartial`.
- No reachable `.vendorMiri` constant is `.opaqueInfo` (guaranteeing that none
  of the 24 `partial def` JSON parser helpers in `Miri.Input.*` is reachable).
- Every reachable axiom belongs to `axioms`. -/
def closureCorr (env : Environment)
    (roles : Std.HashMap Name CorrOrigin)
    (axioms : Array (String × String))
    (pending : List Name) : IO (Array Name × NameSet) := do
  let provenance := constProvenance env roles
  let onVisit (n m : Name) (role : CorrOrigin) (ci : ConstantInfo) :
      IO Unit := do
    if ci.isUnsafe || ci.isPartial then
      fail (s!"unsafe/partial constant {n} from {m} in correspondence " ++
        "dependency cone")
    if role == .vendorMiri && (ci matches .opaqueInfo _) then
      fail (s!"opaque/partial vendor Miri constant {n} from {m} in " ++
        "correspondence dependency cone")
  closure (lookupConst env) provenance axioms pending onVisit

/-- Verify the 36-root `Miri.Interpreter.ExecutionMachine` transitive
dependency cone under `closureCorr`, starting with
`Miri.Interpreter.ExecutionMachine.step` and
`Miri.Interpreter.ExecutionMachine.AllowedStep`. -/
def verifyMiriExecutionMachineCone (env : Environment)
    (roles : Std.HashMap Name CorrOrigin)
    (axiomPolicy : Array (String × String)) : IO (Array Name × NameSet) :=
  closureCorr env roles axiomPolicy [
    `Miri.Interpreter.ExecutionMachine.step,
    `Miri.Interpreter.ExecutionMachine.AllowedStep,
    `Miri.Interpreter.ExecutionMachine.withValidation,
    `Miri.Interpreter.ExecutionMachine.stepHooks,
    `Miri.Interpreter.ExecutionMachine.rvalueHooks,
    `Miri.Interpreter.ExecutionMachine.operandHooks,
    `Miri.Interpreter.ExecutionMachine.projectionHooks,
    `Miri.Interpreter.ExecutionMachine.discriminantHooks,
    `Miri.Interpreter.ExecutionMachine.scalarHooks,
    `Miri.Interpreter.Step.step,
    `Miri.Interpreter.Step.evalStatement,
    `Miri.Interpreter.ControlFlow.goToBlock,
    `Miri.Interpreter.ControlFlow.evalTerminator,
    `Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
    `Miri.Interpreter.ExecutionControl.hooks,
    `Miri.Interpreter.MachineHooks.storageLiveDyn,
    `Miri.Interpreter.MachineHooks.storageDead,
    `Miri.Interpreter.OperandMachine.evalOperand,
    `Miri.Interpreter.OperandMachine.evalPlaceToOp,
    `Miri.Interpreter.PlaceMachine.readImmediate,
    `Miri.Interpreter.PlaceMachine.writeMemory,
    `Miri.Interpreter.ValidityVisitor.validatePlace,
    `Miri.Interpreter.ValidityMemory.bind,
    `Miri.Interpreter.evalRvalueIntoPlace,
    `Miri.Interpreter.TerminatorMachine.beforeTerminatorWithChoice,
    `Miri.Interpreter.ScalarOps.binary,
    `Miri.Interpreter.ScalarOps.unary,
    `Miri.Interpreter.IntegerOps.binary,
    `Miri.Interpreter.IntegerOps.binaryBool,
    `Miri.Interpreter.IntegerOps.unary,
    `Miri.Interpreter.Discriminant.readDiscriminant,
    `Miri.Interpreter.Discriminant.discriminantForVariant,
    `Miri.Memory.ScalarInt.truncateFromUInt,
    `Miri.Memory.ScalarInt.tryFromUInt,
    `Miri.Memory.ScalarInt.tryToBool,
    `Miri.Interpreter.evalOperand]

/-- Verify that `claimName` is a `Prop` definition in `Trusted.Correspondence`
referencing every constant in the non-empty `reqConsts` list, and that
`proofName` is a `.thmInfo` theorem in `Anneal.MirCorrespondenceProof` whose
type is `Expr.const claimName []`. -/
def requireCorrClaimProof (env : Environment)
    (corrLocals : Std.HashMap Name ConstantInfo)
    (claimName proofName : Name) (reqConsts : List Name) : IO Unit :=
  requireClaimProof env corrLocals `Trusted.Correspondence
    `Anneal.MirCorrespondenceProof claimName none proofName reqConsts

/-- Verify that all 34 Pass 2 correspondence, choice-coupled, wiring,
`AllowedStep` soundness, byte-codec, and canary (`D6`–`D13`) claims—covering
aggregate and choice-coupled correspondence and fault equivalence,
`ExecutionMachine.step` / `OperandMachine.evalOperand` /
`LocalAccess.evalOperand` `deinitMovedPlace` wiring, `RefStep` soundness for
`RefAllowedStep`, codec round-trip, constructor preservation, uniqueness,
simulation, `Trusted.MirSemantics` byte encoding against `lean-miri`
`Allocation` scalar accesses, and canaries—are present in
`Trusted.Correspondence`, reference their required semantic definitions (so
replacing any claim with `True` fails CI), and are proved with exact claim-type
equality in `Anneal.MirCorrespondenceProof`. -/
def verifyCorrespondenceClaims (env : Environment)
    (corrLocals : Std.HashMap Name ConstantInfo) : IO Unit := do
  requireCorrClaimProof env corrLocals
    `Trusted.Correspondence.CorrespondenceClaim
    `Anneal.MirCorrespondenceProof.correspondence_claim_holds
    [ `Trusted.MirSemantics.WellFormed,
      `Trusted.Correspondence.RefWellFormed,
      `Trusted.MirSemantics.Behavior,
      `Trusted.Correspondence.RefBehavior,
      `Trusted.MirSemantics.Diverges,
      `Trusted.Correspondence.RefDiverges,
      `Trusted.Correspondence.encodeProg ]
  requireCorrClaimProof env corrLocals
    `Trusted.Correspondence.FaultEquivalenceClaim
    `Anneal.MirCorrespondenceProof.fault_equivalence_claim_holds
    [ `Trusted.MirSemantics.ReachesResult,
      `Trusted.Correspondence.RefReachesOutcome,
      `Trusted.Correspondence.faultToRefOutcome,
      `Trusted.Correspondence.encodeProg ]
  requireCorrClaimProof env corrLocals
    `Trusted.Correspondence.CorrespondenceAtChoicesClaim
    `Anneal.MirCorrespondenceProof.correspondence_at_choices_claim_holds
    [ `Trusted.MirSemantics.WellFormed,
      `Trusted.Correspondence.RefWellFormed,
      `Trusted.Correspondence.RefValidPrefixAtChoices,
      `Trusted.MirSemantics.ValidPrefixAtChoices,
      `Trusted.Correspondence.RefBehaviorAtChoices,
      `Trusted.MirSemantics.BehaviorAtChoices,
      `Trusted.Correspondence.RefDivergesAtChoices,
      `Trusted.MirSemantics.DivergesAtChoices,
      `Trusted.Correspondence.encodeProg ]
  requireCorrClaimProof env corrLocals
    `Trusted.Correspondence.FaultEquivalenceAtChoicesClaim
    `Anneal.MirCorrespondenceProof.fault_equivalence_at_choices_claim_holds
    [ `Trusted.MirSemantics.ReachesResultAtChoices,
      `Trusted.Correspondence.RefReachesOutcomeAtChoices,
      `Trusted.Correspondence.faultToRefOutcome,
      `Trusted.Correspondence.encodeProg ]
  requireCorrClaimProof env corrLocals
    `Trusted.Correspondence.MiriMoveDeinitWiringClaim
    `Anneal.MirCorrespondenceProof.miri_move_deinit_wiring_claim_holds
    [ `Miri.Interpreter.ExecutionMachine.step,
      `Miri.Interpreter.ExecutionMachine.stepHooks,
      `Miri.Interpreter.Step.step,
      `Miri.Interpreter.ExecutionMachine.withValidation,
      `Miri.Interpreter.ExecutionMachine.operandHooks,
      `Miri.Interpreter.OperandMachine.evalOperand,
      `Miri.Interpreter.OperandMachine.evalPlaceToOp,
      `Miri.Interpreter.evalOperand,
      `Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit,
      `Miri.Interpreter.MachineHooks.recordPendingMoveDeinit,
      `Miri.Interpreter.FnArg.copyFnArg,
      `Miri.Interpreter.Call.deinitInPlaceArg ]
  for (claimName, proofName, reqConsts) in [
      (`Trusted.Correspondence.DecodeProgEncodeProgClaim,
        `Anneal.MirCorrespondenceProof.decodeProg_encodeProg,
        [`Trusted.Correspondence.decodeProg,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.EncodeProgTypesCanonicalClaim,
        `Anneal.MirCorrespondenceProof.encodeProg_types_canonical,
        [`Trusted.Correspondence.typesAreCanonical,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.EncodeStmtNoDormantNoopsClaim,
        `Anneal.MirCorrespondenceProof.encodeStmt_no_dormant_noops,
        [`Trusted.Correspondence.encodeStmt]),
      (`Trusted.Correspondence.EncodeRvalueBinaryOpIffClaim,
        `Anneal.MirCorrespondenceProof.encodeRvalue_binaryOp_iff,
        [`Trusted.Correspondence.encodeRvalue,
          `Trusted.Correspondence.encodeOperand]),
      (`Trusted.Correspondence.EncodeRvalueUnaryOpIffClaim,
        `Anneal.MirCorrespondenceProof.encodeRvalue_unaryOp_iff,
        [`Trusted.Correspondence.encodeRvalue,
          `Trusted.Correspondence.encodeOperand]),
      (`Trusted.Correspondence.EncodeStmtAssignIffClaim,
        `Anneal.MirCorrespondenceProof.encodeStmt_assign_iff,
        [`Trusted.Correspondence.encodeStmt,
          `Trusted.Correspondence.encodePlace,
          `Trusted.Correspondence.encodeRvalue]),
      (`Trusted.Correspondence.StateUniqueOfSimulationInvClaim,
        `Anneal.MirCorrespondenceProof.state_unique_of_simulationInv,
        [`Trusted.Correspondence.SimulationInv]),
      (`Trusted.Correspondence.RefStateUniqueOfSimulationInvClaim,
        `Anneal.MirCorrespondenceProof.refState_unique_of_simulationInv,
        [`Trusted.Correspondence.SimulationInv]),
      (`Trusted.Correspondence.InitRefStateSimClaim,
        `Anneal.MirCorrespondenceProof.initRefState_sim,
        [`Trusted.Correspondence.decodeProg,
          `Trusted.MirSemantics.initState,
          `Trusted.Correspondence.initRefState,
          `Trusted.Correspondence.SimulationInv]),
      (`Trusted.Correspondence.EvalRefStepEqClaim,
        `Anneal.MirCorrespondenceProof.evalRefStep_eq,
        [`Trusted.Correspondence.decodeProg,
          `Trusted.Correspondence.evalRefStep,
          `Trusted.Correspondence.stepResultToRefOutcome,
          `Trusted.Correspondence.mapStepRes,
          `Trusted.MirSemantics.evalStep]),
      (`Trusted.Correspondence.SimOfRefStepClaim,
        `Anneal.MirCorrespondenceProof.sim_of_refStep,
        [`Trusted.Correspondence.decodeProg,
          `Trusted.Correspondence.SimulationInv,
          `Trusted.Correspondence.RefStep,
          `Trusted.MirSemantics.Step]),
      (`Trusted.Correspondence.SimOfRefReachesClaim,
        `Anneal.MirCorrespondenceProof.sim_of_refReaches,
        [`Trusted.Correspondence.decodeProg,
          `Trusted.Correspondence.SimulationInv,
          `Trusted.Correspondence.RefReaches,
          `Trusted.MirSemantics.Reaches]),
      (`Trusted.Correspondence.RefWellFormedOfWellFormedClaim,
        `Anneal.MirCorrespondenceProof.refWellFormed_of_wellFormed,
        [`Trusted.MirSemantics.WellFormed,
          `Trusted.Correspondence.RefWellFormed,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.RefBehaviorOfBehaviorClaim,
        `Anneal.MirCorrespondenceProof.refBehavior_of_behavior,
        [`Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.RefBehavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.BehaviorOfRefBehaviorClaim,
        `Anneal.MirCorrespondenceProof.behavior_of_refBehavior,
        [`Trusted.Correspondence.RefBehavior,
          `Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.BehaviorIffRefBehaviorClaim,
        `Anneal.MirCorrespondenceProof.behavior_iff_refBehavior,
        [`Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.RefBehavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.DivergesIffRefDivergesClaim,
        `Anneal.MirCorrespondenceProof.diverges_iff_refDiverges,
        [`Trusted.MirSemantics.Diverges,
          `Trusted.Correspondence.RefDiverges,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD6UseAfterMoveUbClaim,
        `Anneal.MirCorrespondenceProof.canary_D6_use_after_move_ub,
        [`Trusted.Correspondence.progUseAfterMoveD6,
          `Trusted.MirSemantics.ReachesResult,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.Correspondence.RefReachesOutcome,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD7aBinopCopyThenMoveOkClaim,
        `Anneal.MirCorrespondenceProof.canary_D7a_binop_copy_then_move_ok,
        [`Trusted.Correspondence.progBinOpCopyThenMoveD7a,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.RefWellFormed,
          `Trusted.Correspondence.RefBehavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD7bBinopMoveThenCopyUbClaim,
        `Anneal.MirCorrespondenceProof.canary_D7b_binop_move_then_copy_ub,
        [`Trusted.Correspondence.progBinOpMoveThenCopyD7b,
          `Trusted.MirSemantics.ReachesResult,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.Correspondence.RefReachesOutcome,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD7cBinopMoveThenMoveUbClaim,
        `Anneal.MirCorrespondenceProof.canary_D7c_binop_move_then_move_ub,
        [`Trusted.Correspondence.progBinOpMoveThenMoveD7c,
          `Trusted.MirSemantics.ReachesResult,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.Correspondence.RefReachesOutcome,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD8SelfMoveOkClaim,
        `Anneal.MirCorrespondenceProof.canary_D8_self_move_ok,
        [`Trusted.Correspondence.progSelfMoveD8,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.RefWellFormed,
          `Trusted.Correspondence.RefBehavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD9MoveUnitZstOkClaim,
        `Anneal.MirCorrespondenceProof.canary_D9_move_unit_zst_ok,
        [`Trusted.Correspondence.progMoveUnitZstD9,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.RefWellFormed,
          `Trusted.Correspondence.RefBehavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD10AddUncheckedOverflowUbClaim,
        `Anneal.MirCorrespondenceProof.canary_D10_add_unchecked_overflow_ub,
        [`Trusted.MirSemantics.progAddUncheckedU32,
          `Trusted.MirSemantics.progAddU32,
          `Trusted.MirSemantics.ReachesResult,
          `Trusted.MirSemantics.WellFormed,
          `Trusted.Correspondence.RefReachesOutcome,
          `Trusted.MirSemantics.Behavior,
          `Trusted.Correspondence.RefBehavior,
          `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD11EnumDiscriminantAndConstOkClaim,
       `Anneal.MirCorrespondenceProof.canary_D11_enum_discriminant_and_const_ok,
       [`Trusted.MirSemantics.progEnumExplicitReprU8,
         `Trusted.MirSemantics.progEnumSignedTagIsize,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD12ZstEnumMoveAndDiscrOkClaim,
       `Anneal.MirCorrespondenceProof.canary_D12_zst_enum_move_and_discr_ok,
       [`Trusted.MirSemantics.progZstSingleEnumImplicitRet,
         `Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD13EnumInvalidTagAndUninitUbClaim,
       `Anneal.MirCorrespondenceProof.canary_D13_enum_invalid_tag_and_uninit_ub,
       [`Trusted.MirSemantics.progEnumInvalidTagConstUb,
         `Trusted.MirSemantics.progEnumUninitDiscrUb,
         `Trusted.MirSemantics.ReachesResult,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.Correspondence.RefReachesOutcome,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.RefStepSoundForAllowedStepClaim,
       `Anneal.MirCorrespondenceProof.refStep_sound_for_allowedStep_holds,
       [`Trusted.Correspondence.RefStep,
         `Trusted.Correspondence.RefAllowedStep,
         `Trusted.Correspondence.refReadReturnVal]),
      (`Trusted.Correspondence.BytesCodecMatchesMiriClaim,
       `Anneal.MirCorrespondenceProof.bytes_codec_matches_miri,
       [`Trusted.MirSemantics.encodeVal,
         `Trusted.MirSemantics.decodeVal,
         `Trusted.MirSemantics.profileTargetEndian,
         `Miri.Memory.Allocation.writeScalar,
         `Miri.Memory.Allocation.getBytesUnchecked,
         `Miri.Memory.Allocation.readScalar,
         `Miri.Memory.Allocation.writeUninit])] do
    requireCorrClaimProof env corrLocals claimName proofName reqConsts

/-- Return `true` when `modName` is an allowlisted `Trusted` module permitted in
the `M_ref` reference evaluator dependency cone (`Trusted.MirAst`,
`Trusted.MirAst.*`, `Trusted.MirModel`, `Trusted.Correspondence`, and
`Trusted.Correspondence.*`). Every other `Trusted` module—including
`Trusted.MirSemantics`, `Trusted.MirSemantics.*`, and any other sibling
`Trusted.*` module—is excluded fail-closed. -/
def isAllowedRefTrustedModule (modName : Name) : Bool :=
  (`Trusted.MirAst).isPrefixOf modName ||
  modName == `Trusted.MirModel ||
  (`Trusted.Correspondence).isPrefixOf modName

/-- Return `true` when `modName` is a `Trusted.Correspondence.*` submodule
belonging to the isolated reference-evaluator layer (every
`Trusted.Correspondence.*` module other than the umbrella
`Trusted.Correspondence` and the bridge/canary modules
`Trusted.Correspondence.{Simulation,CanaryFixtures}`). -/
def isRefEvalSubmodule (modName : Name) : Bool :=
  (`Trusted.Correspondence).isPrefixOf modName &&
  modName != `Trusted.Correspondence &&
  modName != `Trusted.Correspondence.Simulation &&
  modName != `Trusted.Correspondence.CanaryFixtures

/-- Return `true` when `modName` is an allowlisted `Trusted` module permitted in
the transitive import closure of the isolated `M_ref` evaluator submodules:
`Trusted.MirAst*`, `Trusted.MirModel`, or an isolated `Trusted.Correspondence.*`
evaluator submodule itself. Every other `Trusted` module—including `Trusted`,
`Trusted.MirSemantics*`, `Trusted.Correspondence`,
`Trusted.Correspondence.Simulation`, `Trusted.Correspondence.CanaryFixtures`,
and any sibling `Trusted.*` module—is excluded fail-closed. -/
def isAllowedRefEvalImportTrustedModule (modName : Name) : Bool :=
  (`Trusted.MirAst).isPrefixOf modName ||
  modName == `Trusted.MirModel ||
  isRefEvalSubmodule modName

/-- Verify that the reference machine `M_ref`
(`Trusted.Correspondence.evalRefStep` and `Trusted.Correspondence.initRefState`)
reaches all 34 required live `vendor/lean-miri` `ExecutionMachine` primitives
without relying on `RefAllowedStep`, that `Trusted.Correspondence.RefAllowedStep`
separately reaches `Miri.Interpreter.ExecutionMachine.AllowedStep`, that every
isolated `Trusted.Correspondence.*` evaluator submodule never directly or
transitively imports any disallowed `Trusted` module (including `Trusted`,
`Trusted.MirSemantics*`, `Trusted.Correspondence`,
`Trusted.Correspondence.Simulation`, `Trusted.Correspondence.CanaryFixtures`, or
sibling `Trusted.*` modules), that in a modular correspondence layout
`evalRefStep`, `initRefState`, and `RefAllowedStep` are all defined inside those
isolated evaluator submodules, and that both the evaluator cone and the
`RefAllowedStep` cone reference only allowlisted `Trusted` modules
(`Trusted.MirAst*`, `Trusted.MirModel`, and `Trusted.Correspondence*`)—never
`Trusted.MirSemantics`, `Trusted.MirSemantics.*`, or any other `Trusted` module.
This enforces closed module-origin isolation across the full `M_anneal`
operational-rule cone rather than a manually curated symbol denylist; human
review of `trusted/correspondence/` and `Trusted.MirModel` remains the semantic
boundary. -/
def verifyRefEvaluatorIndependence (env : Environment)
    (roles : Std.HashMap Name CorrOrigin) (corrModSet : NameSet)
    (axiomPolicy : Array (String × String)) : IO Unit := do
  let mut modIdxMap : Std.HashMap Name Nat := {}
  for i in [:env.header.moduleNames.size] do
    modIdxMap := modIdxMap.insert env.header.moduleNames[i]! i
  let evalMods := (corrModSet.toArray.filter fun modName =>
    match roles[modName]? with
    | some (CorrOrigin.repo (SourceRole.trusted _)) => isRefEvalSubmodule modName
    | _ => false).qsort Name.lt
  for rootMod in evalMods do
    unless modIdxMap.contains rootMod do
      fail s!"reference evaluator module {rootMod} missing from compiled environment"
    let mut visited : NameSet := {}
    let mut queue : List Name := [rootMod]
    while !queue.isEmpty do
      match queue with
      | [] => pure ()
      | cur :: rest =>
        queue := rest
        if !visited.contains cur then
          visited := visited.insert cur
          if let some curIdx := modIdxMap[cur]? then
            for imp in env.header.moduleData[curIdx]!.imports do
              let impMod := imp.module
              if (impMod == `Trusted || (`Trusted).isPrefixOf impMod) &&
                  !isAllowedRefEvalImportTrustedModule impMod then
                let via := if cur == rootMod then "" else s!" (via {cur})"
                fail (s!"reference evaluator module {rootMod} illegally " ++
                  s!"imports disallowed module {impMod}{via}")
              if !visited.contains impMod then
                queue := impMod :: queue
  if !evalMods.isEmpty then
    for sym in [
        `Trusted.Correspondence.evalRefStep,
        `Trusted.Correspondence.initRefState,
        `Trusted.Correspondence.RefAllowedStep] do
      let (orig, _) ← constProvenance env roles sym
      unless isRefEvalSubmodule orig do
        fail (s!"modular correspondence layout requires reference evaluator " ++
          s!"symbol {sym} to be defined in an isolated evaluator module, " ++
          s!"found {orig}")
  let (_, refCone) ← closureCorr env roles axiomPolicy
    [ `Trusted.Correspondence.evalRefStep,
      `Trusted.Correspondence.initRefState ]
  for reqMiri in [
      `Miri.Interpreter.ExecutionMachine.step,
      `Miri.Interpreter.ExecutionMachine.withValidation,
      `Miri.Interpreter.ExecutionMachine.stepHooks,
      `Miri.Interpreter.ExecutionMachine.rvalueHooks,
      `Miri.Interpreter.ExecutionMachine.operandHooks,
      `Miri.Interpreter.ExecutionMachine.projectionHooks,
      `Miri.Interpreter.ExecutionMachine.discriminantHooks,
      `Miri.Interpreter.ExecutionMachine.scalarHooks,
      `Miri.Interpreter.Step.step,
      `Miri.Interpreter.Step.evalStatement,
      `Miri.Interpreter.ControlFlow.goToBlock,
      `Miri.Interpreter.ControlFlow.evalTerminator,
      `Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
      `Miri.Interpreter.ExecutionControl.hooks,
      `Miri.Interpreter.MachineHooks.storageLiveDyn,
      `Miri.Interpreter.MachineHooks.storageDead,
      `Miri.Interpreter.OperandMachine.evalOperand,
      `Miri.Interpreter.OperandMachine.evalPlaceToOp,
      `Miri.Interpreter.PlaceMachine.readImmediate,
      `Miri.Interpreter.PlaceMachine.writeMemory,
      `Miri.Interpreter.ValidityVisitor.validatePlace,
      `Miri.Interpreter.ValidityMemory.bind,
      `Miri.Interpreter.evalRvalueIntoPlace,
      `Miri.Interpreter.TerminatorMachine.beforeTerminatorWithChoice,
      `Miri.Interpreter.ScalarOps.binary,
      `Miri.Interpreter.ScalarOps.unary,
      `Miri.Interpreter.IntegerOps.binary,
      `Miri.Interpreter.IntegerOps.binaryBool,
      `Miri.Interpreter.IntegerOps.unary,
      `Miri.Interpreter.Discriminant.readDiscriminant,
      `Miri.Interpreter.Discriminant.discriminantForVariant,
      `Miri.Memory.ScalarInt.truncateFromUInt,
      `Miri.Memory.ScalarInt.tryFromUInt,
      `Miri.Memory.ScalarInt.tryToBool] do
    unless refCone.contains reqMiri do
      fail (s!"reference evaluator cone is missing required Miri " ++
        s!"primitive {reqMiri}")
  let (_, allowedStepCone) ← closureCorr env roles axiomPolicy
    [`Trusted.Correspondence.RefAllowedStep]
  unless allowedStepCone.contains `Miri.Interpreter.ExecutionMachine.AllowedStep do
    fail ("RefAllowedStep cone is missing required Miri primitive " ++
      "Miri.Interpreter.ExecutionMachine.AllowedStep")
  let mut combinedCone := refCone
  for n in allowedStepCone.toArray do
    combinedCone := combinedCone.insert n
  let sortedRefCone := combinedCone.toArray.qsort Name.lt
  for cName in sortedRefCone do
    let (orig, role) ← constProvenance env roles cName
    match role with
    | .repo (.trusted _) =>
      unless isAllowedRefTrustedModule orig do
        fail (s!"reference evaluator cone illegally references disallowed " ++
          s!"Trusted declaration {cName} (defined in {orig})")
    | _ => pure ()

/-- Execute Pass 2 compile-environment syntactic preflight
(`"correspondence-preflight"`).

Loads the authenticated Pass 2 union compile parser environment (`foundation`,
Pass 1 `trusted`/`theory`, and pinned `vendorMiri` with `loadExts := true`),
checks that every loaded module belongs to the closed `CorrOrigin` partition,
collects every namespace with scoped `ScopedEnvExtension` entries (and all of
their strict prefixes), and parses every `trusted/correspondence/` and
`correspondence/` source file without elaborating it. Unscoped syntax and macro
extensions registered by `Miri.*`, `Lean.*`, and `Std.*` (such as `throwError`
-> `Lean.termThrowError__` and `m!` -> `Lean.termM!_`) parse into their true
`SyntaxNodeKind` and are rejected by the closed allowlist, while any
`namespace` or multi-component declaration entering—or any `open`,
`open ... in`, or `mutual` preamble `open` whose candidate resolutions (across
every prefix of `currNamespace` including root and every conservatively tracked
open namespace, resisting decoy-namespace shadowing in the union environment)
include—a namespace with scoped extensions is rejected before compilation. -/
def preflightCorrespondence (j : Json) (foundation : Array Name) : IO Json := do
  let trusted ← names j "trusted"
  let theory ← names j "theory"
  let vendorMiri ← names j "vendorMiri"
  let sources ← field (α := Array (String × String)) j "sources"
  let env ← importCorrEnv (foundation ++ trusted ++ theory ++ vendorMiri) true
  discard <| classifyCorrModules j env foundation trusted theory vendorMiri
  let scopedNamespaces ← collectScopedExtensionNamespaces env
  let scopedPrefixes := collectScopedNamespacePrefixes scopedNamespaces
  let headers ←
    sources.mapM fun (n, p) =>
      inspectSource scopedNamespaces scopedPrefixes env n.toName p
  return Json.mkObj [("headers", .arr headers)]

/-- Collect validated `.repo`, correspondence, and `.vendorMiri` inventories
from the full Pass 2 environment in a dedicated scope so `env` can be released
before constructing the clean sysroot replay base under `-M8192`. -/
def collectCorrEnv (j : Json)
    (foundation allTrusted allTheory vendorMiri : Array Name)
    (corrModSet : NameSet) :
    IO (Std.HashMap Name CorrOrigin × Std.HashMap Name ConstantInfo ×
      Std.HashMap Name ConstantInfo × Std.HashMap Name ConstantInfo ×
      Array Name) := do
  let env ← importCorrEnv (foundation ++ allTrusted ++ allTheory ++ vendorMiri)
  let roles ← classifyCorrModules j env foundation allTrusted
    allTheory vendorMiri
  let (repoLocals, corrLocals, vendorLocals) ←
    verifyAndCollectCorrLocals env roles corrModSet
  checkDeclarationEdges env roles repoLocals CorrOrigin.edgeViolation?
  let sysrootBaseMods := env.header.modules.filterMap fun m =>
    match roles.get? m.module with
    | some .foundation | some .sysrootFoundation => some m.module
    | _ => none
  let vendorReplayLocals :=
    vendorLocals.fold (init := ({} : Std.HashMap Name ConstantInfo))
      fun acc n ci =>
        if ci.isPartial then acc else acc.insert n ci
  return (roles, repoLocals, corrLocals, vendorReplayLocals, sysrootBaseMods)

/-- Initialize `Lean.searchPathRef` from `leanSysroot` and explicit staged
directories `sp`, ignoring ambient `LEAN_PATH` (which is used only to bootstrap
the precompiled `TrustedBoundary.olean` module). -/
def initHermeticSearchPath (leanSysroot : System.FilePath)
    (sp : SearchPath := ∅) : IO Unit := do
  searchPathRef.set (sp ++ (← getBuiltinSearchPath leanSysroot))

/-- Replay every non-`isPartial` `.vendorMiri` declaration from scratch onto a
clean `baseEnv` containing strictly the authenticated `.foundation` and
`.sysrootFoundation` modules (dropping repository and vendor directories from
the search path), then—whenever `replayRepo` is `true`—replay all `.repo`
declarations (Pass 1 + Pass 2 correspondence) directly onto that replayed
vendor kernel environment.

Returns `(miriReplayed, corrReplayed)`, counted from the kernel environments
that `Kernel.Environment.replay` returns rather than from the request:

- `miriReplayed` counts the `vendorReplayLocals` declarations present in the
  replayed vendor environment.
- `corrReplayed` counts the `corrLocals` declarations that were passed to the
  repository replay (through `repoLocals`) and are present in its result. It is
  `0` when `replayRepo` is `false`; otherwise it must equal `corrLocals.size`,
  so the `"correspondenceReplay"` report flag derived from it cannot claim a
  correspondence replay that never ran.

Compiler-generated `isPartial` (`*._unsafe_rec`) codegen helpers are omitted
from `vendorReplayLocals` (matching `Kernel.Environment.replay`), so any
reference to them from a replayed declaration fails kernel replay with
`unknown constant`. -/
def replayCorrAndVendor (sysrootStr : String)
    (roles : Std.HashMap Name CorrOrigin) (sysrootBaseMods : Array Name)
    (vendorReplayLocals repoLocals corrLocals : Std.HashMap Name ConstantInfo)
    (replayRepo : Bool) : IO (Nat × Nat) := do
  initHermeticSearchPath sysrootStr
  let baseEnv ← importCorrEnv sysrootBaseMods
  for m in baseEnv.header.modules do
    match roles.get? m.module with
    | some .foundation | some .sysrootFoundation => pure ()
    | _ =>
      fail s!"unexpected non-sysroot module {m.module} in vendor replay base"
  for (n, _) in vendorReplayLocals do
    if (baseEnv.checked.get.find? n).isSome then
      fail s!"vendor Miri constant {n} shadows sysroot declaration"
  let replayedVendor ← replayKernelEnv baseEnv.toKernelEnv vendorReplayLocals
    "vendor Miri kernel replay failed"
  let miriReplayed :=
    vendorReplayLocals.fold (init := (0 : Nat)) fun acc n _ =>
      if (replayedVendor.find? n).isSome then acc + 1 else acc
  if !replayRepo then
    return (miriReplayed, 0)
  for (n, _) in repoLocals do
    if (replayedVendor.find? n).isSome then
      fail s!"repository constant {n} shadows vendor/sysroot declaration"
  let replayedRepo ← replayKernelEnv replayedVendor repoLocals
    "correspondence kernel replay failed"
  let corrReplayed :=
    corrLocals.fold (init := (0 : Nat)) fun acc n _ =>
      if repoLocals.contains n && (replayedRepo.find? n).isSome then acc + 1
      else acc
  unless corrReplayed == corrLocals.size do
    fail (s!"correspondence kernel replay covered {corrReplayed} of " ++
      s!"{corrLocals.size} correspondence declarations")
  return (miriReplayed, corrReplayed)

/-- Verify the 36-root `Miri.Interpreter.ExecutionMachine` cone and—when
Pass 2 correspondence modules are present—all 34 correspondence, choice-coupled,
wiring, `AllowedStep` soundness, byte-codec, and canary claims,
reference-evaluator independence, and the correspondence dependency cone in a
dedicated scope. -/
def verifyCorrConesAndClaims
    (foundation allTrusted allTheory vendorMiri : Array Name)
    (roles : Std.HashMap Name CorrOrigin)
    (corrLocals : Std.HashMap Name ConstantInfo) (corrModSet : NameSet)
    (axiomPolicy : Array (String × String)) :
    IO (Array Name × Nat × Array Name × Nat) := do
  let env ← importCorrEnv (foundation ++ allTrusted ++ allTheory ++ vendorMiri)
  let (miriAxioms, miriVisited) ←
    verifyMiriExecutionMachineCone env roles axiomPolicy
  if corrModSet.isEmpty then
    return (miriAxioms, miriVisited.size, #[], 0)
  verifyCorrespondenceClaims env corrLocals
  verifyRefEvaluatorIndependence env roles corrModSet axiomPolicy
  let corrRoots := corrLocals.fold (init := []) fun acc n _ => n :: acc
  let (corrAxioms, corrVisited) ←
    closureCorr env roles axiomPolicy corrRoots
  return (miriAxioms, miriVisited.size, corrAxioms, corrVisited.size)

/-- Execute Phase 3 (`"correspondence-audit"`) on the Pass 2 correspondence
and `lean-miri` closure environment.

Pass 2 replays EVERY non-`isPartial` `.vendorMiri` declaration (38,718
declarations across the 160 compiled closure modules) from scratch through the
standalone Lean kernel onto the authenticated `.foundation` +
`.sysrootFoundation` base on every run (cold build and warm cache hit alike),
and then replays all repository declarations (including
`trusted/correspondence/` and `correspondence/`) directly on top of that
replayed vendor kernel environment. Only the authenticated toolchain sysroot
modules (verified against `foundation-lock.json` and
`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`) are trusted without replay.

The report derives `"miriReplayedDeclarations"`,
`"correspondenceReplayedDeclarations"`, and `"correspondenceReplay"` (`true`
iff the replayed correspondence count is positive) from the counts that
`replayCorrAndVendor` takes from the replayed kernel environments, so
`anneal-audit` can fail closed when correspondence replay is skipped. -/
def auditCorrespondence (j : Json) (sysrootStr : String)
    (spRaw : Array String) (foundation : Array Name) : IO Json := do
  let baseTrusted ← names j "trusted"
  let corrTrusted ← names j "corrTrusted"
  let baseTheory ← names j "theory"
  let corrTheory ← names j "corrTheory"
  let vendorMiri ← names j "vendorMiri"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let allTrusted := baseTrusted ++ corrTrusted
  let allTheory := baseTheory ++ corrTheory
  let corrModSet : NameSet := .ofList (corrTrusted.toList ++ corrTheory.toList)
  let (roles, repoLocals, corrLocals, vendorReplayLocals, sysrootBaseMods) ←
    collectCorrEnv j foundation allTrusted allTheory vendorMiri corrModSet
  let (miriReplayed, corrReplayed) ←
    replayCorrAndVendor sysrootStr roles sysrootBaseMods vendorReplayLocals
      repoLocals corrLocals (!corrModSet.isEmpty)
  -- Restore the Pass 2 search path dropped during sysroot-only vendor replay.
  initHermeticSearchPath sysrootStr (spRaw.toList.map System.FilePath.mk)
  let (miriAxioms, miriVisitedSize, corrAxioms, corrVisitedSize) ←
    verifyCorrConesAndClaims foundation allTrusted allTheory vendorMiri roles
      corrLocals corrModSet axiomPolicy
  return Json.mkObj [
    ("miriReplay", toJson true),
    ("miriReplayedDeclarations", toJson miriReplayed),
    ("miriClosureReachableDeclarations", toJson miriVisitedSize),
    ("miriClosureAxioms", toJson miriAxioms),
    ("correspondenceReplay", toJson (decide (corrReplayed > 0))),
    ("correspondenceDeclarations", toJson corrLocals.size),
    ("correspondenceReplayedDeclarations", toJson corrReplayed),
    ("correspondenceReachableDeclarations", toJson corrVisitedSize),
    ("correspondenceAxioms", toJson corrAxioms)]

/-! ## Phase 4: External target verification (`"target-audit"`) -/

/-- Collect every serialized `@[csimp]` entry of `env` under the declaration it
replaces, as `(scope, toDeclName, thmName)` in module and entry order. `scope`
names the namespace of a scoped entry and is `none` for a global entry.

Target-audit imports keep `loadExts := false`, so `CSimp.ext` keeps its initial
state: the pinned importer says "every extension will have its initial value
as its state". The serialized module entries remain readable. With
`loadExts := true`, the pinned import callback would map each global entry's
`fromDeclName` to its last entry and apply a scoped entry only where its
namespace is opened. Comparing every entry is stricter than comparing that map.
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean#L2427-L2431
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/ScopedEnvExtension.lean#L61-L74
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Compiler/CSimpAttr.lean#L33-L38 -/
def csimpEntries (env : Environment) :
    NameMap (Array (Option Name × Name × Name)) := Id.run do
  let mut entries : NameMap (Array (Option Name × Name × Name)) := {}
  for modIdx in Array.range env.header.moduleData.size do
    for entry in Compiler.CSimp.ext.ext.getModuleEntries env modIdx do
      let e := match entry with
        | .global e | .scoped _ e => e
      let scope : Option Name := match entry with
        | .global _ => none
        | .scoped ns _ => some ns
      let previous := (entries.find? e.fromDeclName).getD #[]
      entries := entries.insert e.fromDeclName
        (previous.push (scope, e.toDeclName, e.thmName))
  return entries

/-- Execute Phase 4 (`"target-audit"`) on compiled target artifacts.

Target auditing checks actual stored declarations, including private helpers
and generated inductive members. It imports no unvalidated declaration into the
replay base. Every import uses `loadExts := false`, including those for the
compiler-metadata comparison, so no target `[init]` declaration or extension
import callback runs in this process. -/
def targetAudit (j : Json) (foundation : Array Name) : IO Json := do
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let mut roles : Std.HashMap Name TargetOrigin := {}
  for m in foundation do roles := roles.insert m .foundation
  for m in libraries do
    roles ← insertRole roles m .library "overlapping target module"
  let mut roots := foundation ++ libraries
  for item in modules do
    let m := (← field (α := String) item "module").toName
    let rawRole ← field (α := String) item "role"
    let some role := TargetRole.parse? rawRole
      | fail s!"unknown target role {rawRole}"
    roles ← insertRole roles m (.source role) "overlapping target module"
    roots := roots.push m
  let env ← importEnv j roots
  validateGraph j env
  let provenance n := constProvenance env roles n "target module"
  let lookup n := lookupConst env n "target dependency"
  -- Cross-check source inventory and the environment's actual stored values.
  -- Library declarations are checked when reached, so irrelevant metaprogram
  -- implementation constants do not become restrictions on authored proofs.
  let mut sourceInventory : NameSet := {}
  let mut libraryInventories : Std.HashMap Name NameSet := {}
  let mut libraryExports : Std.HashMap Name (Array ConstantInfo) := {}
  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module
      | fail s!"foreign target module {m.module}"
    if let .library := role then
      -- Record all exports, including repeats whose selected origin belongs
      -- to another pinned module. Only logically reached names are compared
      -- below; unused tactic implementation constants remain unrestricted.
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target library inventory {m.module}"
      libraryInventories := libraryInventories.insert m.module
        (.ofList data.constNames.toList)
      for ci in data.constants do
        libraryExports := libraryExports.insert ci.name
          ((libraryExports.getD ci.name #[]).push ci)
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
  let expectedName :=
    (← field (α := String) target "expectedDeclaration").toName
  let expectedModule := (← field (α := String) target "expectedModule").toName
  match roles.get? theoremModule, roles.get? expectedModule with
  | some (.source .proof), some (.source .expected) => pure ()
  | _, _ => fail "incorrect target/expected authority roles"
  let theoremInfo ← lookup theoremName
  let expectedInfo ← lookup expectedName
  unless (← origin env theoremName) == theoremModule &&
      (← origin env expectedName) == expectedModule do
    fail "incorrect target/expected declaration origin"
  -- Names and namespaces do not establish authority or the kind of claim.
  -- The later canonical comparison covers the entire submitted type, including
  -- any binders, after these declarations have passed origin checks and replay.
  unless theoremInfo matches .thmInfo _ do fail "target root must be a theorem"
  unless expectedInfo matches .defnInfo _ do
    fail "Expected must be a definition"
  unless theoremInfo.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
    fail "target and Expected must have no universe parameters"
  unless expectedInfo.type == .sort .zero do fail "Expected must have type Prop"
  let canonicalRoot := (← field (α := String) target "canonicalRoot").toName
  let crateCtor : Name := `Trusted.MirSemantics.Crate.mk
  let subjectName := (← field (α := String) target "subjectDeclaration").toName
  let specName :=
    (← field (α := String) target "specificationDeclaration").toName
  for (n, requiredRole) in [(canonicalRoot, TargetRole.model),
      (crateCtor, TargetRole.model),
      (subjectName, TargetRole.capture),
      (specName, TargetRole.specification)] do
    let (_, role) ← provenance n
    match role with
    | .source actual =>
      unless actual == requiredRole do
        fail s!"incorrect canonical input origin {n}"
    | _ => fail s!"incorrect canonical input origin {n}"
    unless (← lookup n).levelParams.isEmpty do
      fail s!"canonical input has universe parameters {n}"
  -- Build the proposition directly from authenticated kernel names. Imported
  -- syntax, namespaces and elaborators may change the compiled Expected body;
  -- that convenience definition is therefore checked against this expression.
  let canonical := mkApp (mkConst canonicalRoot)
    (mkApp2 (mkConst crateCtor) (mkConst subjectName) (mkConst specName))
  -- The request cannot widen the logical foundation by listing more axioms.
  -- Checked libraries contribute replayed declarations, not new assumptions.
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  unless axiomPolicy == #[("Classical.choice", "Init.Prelude"),
      ("Quot.sound", "Init.Prelude"), ("propext", "Init.Core")] do
    fail "target axiom policy differs from the original foundation"
  -- A library name can occur in several serialized inventories while the
  -- imported environment selects only one value. Reconcile every reached
  -- variant before replay. Alternate proofs can introduce further logical
  -- dependencies, so extend the same closure until no new roots remain.
  let mut pending := [
    theoremName, expectedName, canonicalRoot, crateCtor, subjectName, specName]
  let mut axioms : Array Name := #[]
  let mut reached : NameSet := {}
  let mut alternateProofs : Array ConstantInfo := #[]
  repeat
    let previous := reached
    let (allAxioms, allReached) ← closure lookup provenance axiomPolicy
      pending (visited := reached) (reachedAxioms := .ofList axioms.toList)
    axioms := allAxioms
    reached := allReached
    pending := []
    for n in reached do
      unless previous.contains n do
        let (orig, role) ← provenance n
        if let .library := role then
          unless (libraryInventories.getD orig {}).contains n do
            fail s!"uninventoried target library dependency {n}"
        for ci in libraryExports.getD n #[] do
          match role with
          | .foundation | .library => pure ()
          | .source _ => fail s!"target library inventory origin mismatch {n}"
          let alternatives ← inventoryAlternates (← lookup n) ci true
          for proof in alternatives do
            let deps ← declarationEdges proof
            -- A discarded proof is still a library export. Its own edges
            -- cannot acquire target-source authority merely because the
            -- selected body has no such dependency.
            for dep in deps do
              let (_, depRole) ← provenance dep
              if let some msg :=
                  TargetOrigin.edgeViolation? n .library dep depRole then
                fail msg
            pending := deps.toList ++ pending
          alternateProofs := alternateProofs ++ alternatives
    if pending.isEmpty then break
  -- Meaning surfaces follow the canonical claim's dependencies, independently
  -- of which proof helpers establish it. Those helpers still belong to reached
  -- and undergo replay, but editing them must not redefine the reviewed claim.
  let (_, expectedReached) ← closure lookup provenance axiomPolicy
    [canonicalRoot, crateCtor, subjectName, specName]
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut modelRoots : List Name := []
  let mut specRoots : List Name := []
  for n in reached do
    let ci ← lookup n
    let (_, role) ← provenance n
    match role with
    | .foundation => pure ()
    | .library | .source _ =>
      ensureReplayableConstant "logical dependency" "" ci
      if let .source _ := role then
        unless sourceInventory.contains n do
          fail s!"uninventoried target dependency {n}"
      -- Parsed imports are only the early authority gate. Recheck the actual
      -- type/body edges, including private and generated helpers, so the stored
      -- declarations' meanings obey the same authority boundary.
      for dep in ← declarationEdges ci do
        let (_, depRole) ← provenance dep
        if let some msg := role.edgeViolation? n dep depRole then
          fail msg
      replayMap := replayMap.insert n ci
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()
  -- Rebuild from the original foundation before comparing the root, so neither
  -- the proof nor its specification is validated using unchecked target data.
  let base ← importEnv j foundation
  let replayed ← replayOntoBase base replayMap alternateProofs
    "kernel replay rejected target dependency"
  let checkedEnv := Environment.ofKernelEnv replayed
  let canonicalType ← kernelResult "canonical root type check"
    (Kernel.check checkedEnv {} canonical)
  unless canonicalType == .sort .zero do
    fail "canonical root application must have type Prop"
  let some expectedBody := expectedInfo.value? true
    | fail "Expected has no stored body"
  requireKernelEquality "compiled Expected comparison"
    "compiled Expected body differs from the canonical root"
    (Kernel.isDefEq checkedEnv {} expectedBody canonical)
  requireKernelEquality "target theorem type comparison"
    "target theorem type differs from Expected"
    (Kernel.isDefEq checkedEnv {} theoremInfo.type canonical)
  -- Compiler replacement attributes do not affect logical reduction. Reject
  -- authored changes nevertheless, including changes to an imported helper.
  -- Compare against authenticated toolchain metadata so ordinary pinned extern
  -- implementations of Nat/BitVec operations remain available.
  --
  -- Keep both metadata environments at loadExts := false; env is the target
  -- import above. With loadExts, the pinned importer runs every imported
  -- [init] declaration, after runInitAttrs checks that initializers are
  -- enabled: "`enableInitializersExecution` must be run before calling
  -- `importModules (loadExts := true)`". Builtin import callbacks also
  -- evaluate imported declarations; KeyedDeclsAttribute's ofOLeanEntry calls
  -- evalConstCheck. That code would run in the process whose result file the
  -- runner accepts. The implemented_by and extern lookups need no callback:
  -- the pinned ParametricAttribute import callback is
  -- `fun _ => pure ([], {})`, and getParam? reads an imported declaration's
  -- `ext.getModuleEntries env modIdx`. csimpEntries reads csimp entries the
  -- same way.
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Compiler/InitAttr.lean#L198-L203
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/KeyedDeclsAttribute.lean#L118-L127
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Attributes.lean#L263-L281
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Attributes.lean#L306-L321
  let fixedMetadata ← importEnv j (foundation ++ libraries)
  let fixedCSimp := csimpEntries fixedMetadata
  let targetCSimp := csimpEntries env
  for n in reached do
    unless Compiler.getImplementedBy? fixedMetadata n ==
        Compiler.getImplementedBy? env n &&
        getExternAttrData? fixedMetadata n == getExternAttrData? env n do
      fail s!"unchecked compiler override on logical dependency {n}"
    unless fixedCSimp.find? n == targetCSimp.find? n do
      fail s!"authored compiler replacement on logical dependency {n}"
  -- Subject helpers can determine captured program data without appearing in
  -- the model or specification. Report their own logical closure as well, so
  -- those installed artifacts receive identities without including proof-only
  -- helpers or every imported module. declarationEdges follows stored values:
  -- Lean's value? "Returns the value of a definition."
  -- https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Declaration.lean#L479-L488
  let (_, subjectClosure) ← closure lookup provenance axiomPolicy [subjectName]
  let (_, modelClosure) ← closure lookup provenance axiomPolicy modelRoots
  let (_, specClosure) ← closure lookup provenance axiomPolicy specRoots
  let describe (nodes : NameSet) :=
    nodes.toArray.qsort Name.lt |>.mapM fun n => do
      return Json.mkObj [("name", toJson n),
        ("module", toJson (← origin env n))]
  return Json.mkObj [("theorem", toJson theoremName),
    ("canonicalRoot", toJson canonicalRoot), ("subject", toJson subjectName),
    ("specification", toJson specName), ("graph", graph env),
    ("expected", toJson expectedName), ("axioms", toJson axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson replayMap.size),
    ("checkedAlternateProofs", toJson alternateProofs.size),
    ("subjectClosure", .arr (← describe subjectClosure)),
    ("modelClosure", .arr (← describe modelClosure)),
    ("specificationClosure", .arr (← describe specClosure))]

/-- Dispatch a repository or target inspection request. -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  let sysrootStr ← field (α := String) j "sysroot"
  let foundation ← names j "foundation"
  match mode with
  | "headers" =>
    initHermeticSearchPath sysrootStr
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectHeader n.toName p
    return Json.mkObj [("headers", .arr headers)]
  | "preflight" =>
    initHermeticSearchPath sysrootStr
    let env ← importEnv j foundation true
    validateGraph j env
    let scopedNamespaces ← collectScopedExtensionNamespaces env
    let scopedPrefixes := collectScopedNamespacePrefixes scopedNamespaces
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ←
      sources.mapM fun (n, p) =>
        inspectSource scopedNamespaces scopedPrefixes env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  | "correspondence-preflight" =>
    let spRaw ← field (α := Array String) j "searchPath"
    initHermeticSearchPath sysrootStr (spRaw.toList.map System.FilePath.mk)
    preflightCorrespondence j foundation
  | "audit" =>
    initHermeticSearchPath sysrootStr
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let env ← importEnv j (foundation ++ trusted ++ theory)
    audit j env foundation trusted theory
  | "target-audit" =>
    initHermeticSearchPath sysrootStr
    targetAudit j foundation
  | "correspondence-audit" =>
    let spRaw ← field (α := Array String) j "searchPath"
    initHermeticSearchPath sysrootStr (spRaw.toList.map System.FilePath.mk)
    auditCorrespondence j sysrootStr spRaw foundation
  | _ => throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

/-- Run the inspector via `lean --run` (either directly on
`TrustedBoundary.lean` or through a thin `import TrustedBoundary` runner with
precompiled `TrustedBoundary.olean`), writing a JSON envelope to `<res.json>`
and returning exit code `0` (success), `1` (policy rejection), or `2`
(operational failure). -/
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
