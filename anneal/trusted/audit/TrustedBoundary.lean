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
import Lean.Util.PtrSet
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatchEqs
import Lean.Meta.Constructions.SparseCasesOn
import Lean.Meta.Constructions.SparseCasesOnEq
import Lean.Meta.Tactic.FunInd
import Lean.Meta.CongrTheorems
import Lean.Meta.Injective
import Lean.Meta.MethodSpecs
import Lean.Compiler.Old

/-!
# Offline Repository Audit & Legacy Target Inspector (`TrustedBoundary.lean`)

Provides offline repository Pass 1 (`"preflight"`, `"audit"`), Pass 2
`lean-miri` correspondence (`"vendor-headers"`, `"correspondence-preflight"`,
`"correspondence-audit"`), and transitional legacy `v4.34.1` `"target-export"` /
`"target-audit"`.

When `cargo-anneal verify` runs on Lean `v4.35.0+` with
`--allow-unpinned-lean` and the bundled comparator binaries, it does NOT
compile or execute `TrustedBoundary.lean`. It uses
`trusted/audit/SpecPreflight.lean` instead: the parser-only `"headers"`
mode; `"spec-preflight"`, which parses specifications with the sysroot's
parser tables and loads no target `.olean`; `"resolve-imports"`, which
imports sysroot `.olean`s to emit their import graph; and `"sysroot-consts"`
and `"target-consts"`, which import the admitted sysroot and the compiled
`Model`, `Capture`, `Specification`, and `Expected` `.olean`s (never a
`Proof` `.olean`) to build constant-to-module indices. These pair with the
pure-Rust Universal NDJSON Comparator
(`trusted/cargo-anneal/src/ndjson_comparator.rs`) backed by `nanoda_bin` and
`con-ron`, so no Lean process produces the verdict. Every other run,
including every pinned Lean `v4.34.1` run, uses the `"target-export"` /
`"target-audit"` blocks below.

Pinned to Lean 4.34.1, commit
`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`. `anneal-audit`
(`trusted/audit/`) and legacy `v4.34.1` `cargo-anneal verify` invoke this file
across ten JSON IPC modes (`run` and `main`):

- **`"headers"` (target import discovery before elaboration):**
  Parses only module headers via `Parser.parseHeader`, reporting each module's
  `isModule` flag and `imports` while admitting Lean 4 module-system headers
  (`module`) across target roles (`Model`, `Capture`, `Specification`,
  `Expected`, and `Proof`), rejecting `import all` outside `Anneal.*`
  importing `Init.Data.Nat.Bitwise.Basic`, non-exported imports on non-module
  sources, `meta import` (except Lean 4's synthetic `!hasPrelude`
  `Init(isMeta = true)` paired with non-meta `Init`), and `Lean.*`/`Lake.*`
  imports so `cargo-anneal verify` can validate target module roles, admit the
  requested `library-lock.json` or unpinned `Init`/`Std` closure, and reject
  import cycles before compiling any target source.
- **`"vendor-headers"` (pinned `vendor/lean-miri` DAG discovery):**
  Parses only module `module`/`prelude`/`import` headers via
  `Parser.parseHeader` without loading `.olean` files or elaborating commands
  so `anneal-audit` can schedule cold `vendor/lean-miri` compilation along the
  full import DAG (including Lean 4 `module`-system sources and `Lean.*`
  imports validated separately by `UPSTREAM_PIN.json` and Pass 2
  `"correspondence-audit"`).
- **`"spec-preflight"` (target specification syntactic admission):**
  Parses every `TargetRole::Specification` source against the authenticated
  `Init` + `Std` parser environment only (zero target `.olean`s loaded, zero
  command elaboration, zero tactic allowlist on `proof/`), enforcing a closed
  14-command allowlist, arity-independent fail-closed modifiers, resolved
  lexical scope tracking across all five `open` forms (banning `Lean`, `Lake`,
  `IO`, `BaseIO`, `EIO`, `EST`, `ST`, `Task`, and `System` except
  `System.Platform.{numBits, getNumBits, numBits_eq}`), closed attributes,
  deriving, and `set_option` rules, a dynamic fail-closed pure-spec tactic
  allowlist, and exact term/quotation guards (`include_str`, `by_elab`,
  `sorry`, debug/meta forms, and quotations).
- **`"resolve-imports"` (unpinned sysroot import-DAG discovery):**
  Imports requested sysroot modules with `trustLevel := 0`, `plugins := #[]`,
  and `loadExts := false` (no initializers or extension callbacks) and emits
  the sorted compiled `.olean` import DAG so `cargo-anneal` can enforce
  `Init`/`Std`-only sysroot admission and partition the `{Init.Prelude,
  Init.Core}` foundation closure in unpinned host mode.
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
  `opaque`, and unapproved axioms, and verifies all 38 Pass 2 correspondence,
  wiring, and canary claims plus reference-evaluator independence checks.
- **`"target-export"` (isolated structural proof-artifact exporter):**
  Runs in a dedicated sandboxed child process with no write access to the
  verdict output of `"target-audit"`. It imports the compiled target artifacts
  at `trustLevel := 0` with `loadExts := false`, validates cached `Name.hash`,
  `Level.data`, and `Expr.data` words on every exported proof constant, and
  emits a pure structural DAG JSON stream (`names`, `levels`, `exprs`,
  `modules`, `compilerOverrides`) containing zero heap pointers and zero cached
  metadata words.
- **`"target-audit"` (external target crate verification):**
  Loads only the trusted/preflighted non-proof artifacts (`foundation`,
  `libraries`, and non-`Proof` target roles) with `trustLevel := 0`,
  `plugins := #[]`, and `loadExts := false`, never opening or mapping any
  untrusted authored `Proof` `.olean` in the verdict-producing process. Proof
  declarations are reconstructed fresh from the `"target-export"` structural
  JSON stream using safe Lean constructors (recomputing all cached metadata).
  It verifies `TargetOrigin.allows` over compiled declaration edges, reconciles
  diamond theorem exports across `library-lock.json`, validates cached
  `Name.hash`/`Level.data`/`Expr.data` words before replaying all logically
  reached declarations and alternate proofs onto `foundation-lock.json`, checks
  definitional equality of both `Expected` and the submitted proof theorem
  against the canonical `CrateTheorem`/`UnitTheorem` kernel application, and
  rejects `@[implemented_by]`, `@[extern]`, and `@[csimp]` metadata on logically
  reached declarations authored by target source modules (`Proof` overrides via
  `proofExport.overrides` and non-proof `.source` modules via
  `finalizeImport`-populated `getModuleEntries` on `env`, with `loadExts := false`
  and no separate metadata environment import).

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

Module imports mirror the `RepoOrigin.edgeViolation?` authority boundary:

- `.foundation` modules import only `.foundation` modules.
- `.trusted .vetted` modules import only `.foundation` and `.trusted .vetted`
  modules (never `.trusted (.candidate _)` or `.theory`).
- `.trusted (.candidate _)` modules import `.foundation` and `.trusted _`
  modules, never `.theory`.
- `.theory` modules may import `.foundation` or any `.repo _` module.

`edgeViolation?` separately checks every constant reference across admitted
imports as defense in depth. -/
def RepoOrigin.importViolation? (m : Name) (src : RepoOrigin) (imp : Name)
    (dst : RepoOrigin) : Option String :=
  match src, dst with
  | .foundation, .foundation => none
  | .foundation, .repo _ =>
    some s!"foundation module {m} cannot import {imp}"
  | .repo (.trusted .vetted), .foundation
  | .repo (.trusted .vetted), .repo (.trusted .vetted) => none
  | .repo (.trusted .vetted), .repo (.trusted depTier) =>
    some s!"vetted module {m} cannot import {depTier.render} module {imp}"
  | .repo (.trusted _), .repo .theory =>
    some s!"Trusted module {m} cannot import non-Trusted module {imp}"
  | .repo (.trusted (.candidate _)), .foundation
  | .repo (.trusted (.candidate _)), .repo (.trusted _) => none
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
- `.trusted .vetted` modules import only `.foundation` and `.trusted .vetted`
  modules (never `.sysrootFoundation`, `.vendorMiri`,
  `.trusted (.candidate _)`, or `.theory`).
- `.trusted (.candidate _)` modules never import `.theory` modules (including
  `theory/` modules such as `Anneal.MirWp` and every `correspondence/` module).

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
  | .repo (.trusted .vetted), .foundation
  | .repo (.trusted .vetted), .repo (.trusted .vetted) => none
  | .repo (.trusted .vetted), .sysrootFoundation
  | .repo (.trusted .vetted), .vendorMiri =>
    some s!"vetted module {m} cannot import non-foundation module {imp}"
  | .repo (.trusted .vetted), .repo (.trusted depTier) =>
    some s!"vetted module {m} cannot import {depTier.render} module {imp}"
  | .repo (.trusted _), .repo .theory =>
    some s!"Trusted module {m} cannot import non-Trusted module {imp}"
  | .repo (.trusted (.candidate _)), .foundation
  | .repo (.trusted (.candidate _)), .sysrootFoundation
  | .repo (.trusted (.candidate _)), .vendorMiri
  | .repo (.trusted (.candidate _)), .repo (.trusted _) => none
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
`moduleTk`, `public`, and `all` are permitted syntactically so `inspectSource`,
`inspectHeader`, and `validateTargetImports` can enforce role-scoped module and
import-modifier policies (`meta` remains excluded at the syntax-kind level). -/
def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.moduleTk, ``Parser.Module.prelude,
  ``Parser.Module.import, ``Parser.Module.public, ``Parser.Module.all]

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
  ``Parser.Command.public, ``Parser.Command.noncomputable,
  ``Parser.Command.openSimple,
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
`macro`, and `elab_as_elim`) are excluded. `expose` controls Lean 4 `module`
interface visibility only and introduces no compiler override or side effect. -/
def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible, `expose]

/-- Return `true` iff `moduleName` belongs to the bundled `Anneal` theory
namespace (`Anneal` or `Anneal.*`). -/
def isAnnealModuleName (moduleName : Name) : Bool :=
  moduleName == `Anneal || moduleName.getRoot == `Anneal

/-- Lists foundation modules whose internal definitions a `theory/` module may
open via `import all` in Lean 4 `module` mode.

Confined strictly to `Init.Data.Nat.Bitwise.Basic` because Lean's foundation
keeps `Nat.bitwise`, `Nat.land`, `Nat.lor`, and `Nat.xor` unexposed in `module`
mode; `Anneal.NatBitwise` opens that single module to prove public unfolding
bridges while keeping `Trusted` and all other imports closed. -/
def allowedTheoryImportAllModules : List Name :=
  [`Init.Data.Nat.Bitwise.Basic]

/-- Term, tactic, and macro syntax kinds carrying elaboration/compile-time
I/O or debug side effects, rejected explicitly in both Pass-1 `"preflight"`
and `"spec-preflight"`. -/
def forbiddenPureTermKinds : NameSet := .ofList [
  ``Lean.includeStr,
  `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.idbg,
  `Lean.Parser.Term.doDbgTrace, `Lean.Parser.Term.doIdbg,
  `Lean.Parser.Tactic.dbgTrace, `termPrintln!__]

/-- Pure-signature debug, dynamic-library loading, and file-embedding
identifiers rejected explicitly in both Pass-1 `"preflight"` and
`"spec-preflight"`, closing `Init/Util.lean`'s `lean_dbg_*` externs,
`Lean.LoadDynlib` / `loadDynlib` / `loadPlugin`, and `includeStr`. -/
def forbiddenPureIdentifiers : List Name := [
  `dbgTrace, `dbgTraceVal, `dbgTraceIfShared,
  `dbgStackTrace, `dbgStackTraceIf, `dbgSleep,
  `lean_dbg_trace, `lean_dbg_trace_if_shared,
  `lean_dbg_stack_trace, `lean_dbg_sleep,
  `loadDynlib, `loadPlugin,
  `lean_load_dynlib, `lean_load_plugin,
  `lean_dynlib_load, `lean_dynlib_get, `lean_dynlib_symbol_run_as_init,
  `includeStr]

/-- Exact `System.Platform` declarations admitted in target specifications. -/
def allowedSystemPlatformDecls : List Name := [
  `System.Platform.numBits,
  `System.Platform.getNumBits,
  `System.Platform.numBits_eq]

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

/-- Return `true` if `id` is a valid user-written identifier with non-empty
string components, no macro scopes, and no `_root_` namespace escape. -/
def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

/-- Return `true` iff `moduleName` belongs to the `Trusted` root namespace
(`Trusted` or `Trusted.*`). -/
def isTrustedModuleName (moduleName : Name) : Bool :=
  moduleName == `Trusted || moduleName.getRoot == `Trusted

/-- Determine the `SourceRole` of `moduleName` from its name and the
`-- anneal-trust-tier: <tier>` directive in `text`. Every `Trusted` module must
declare a single valid `TrustTier`, and non-`Trusted` (`theory/` and
`correspondence/`) modules may not declare one. -/
def extractSourceRole (moduleName : Name) (text : String) : IO SourceRole := do
  let isTrustedModule := isTrustedModuleName moduleName
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

/-- Validate a `Parser.Command.sectionHeader` arity-independently: permit only
empty modifier slots, `public`, and `@[expose]`, rejecting `noncomputable`,
`meta`, and any unknown modifier. -/
def validateSectionHeader (args : Array Syntax) : IO Unit := do
  for child in args do
    let ok := child.isOfKind nullKind &&
      (child.getArgs.isEmpty ||
        (child.getArgs.size == 1 &&
          match child.getArgs[0]! with
          | .atom _ "public" => true
          | _ => false) ||
        (child.getArgs.size == 3 &&
          match child.getArgs[0]!, child.getArgs[1]!, child.getArgs[2]! with
          | .atom _ "@[", .atom _ "expose", .atom _ "]" => true
          | _, _, _ => false))
    unless ok do
      fail "section/namespace modifiers are unsupported"

/-- Enforce per-node structural invariants on a `Syntax.node` whose kind `k` has
already been admitted by `allowedKinds`:

- `Parser.Module.header`: an explicit `prelude` child (`args[1]`) is mandatory
  (omitting `prelude` produces an empty `null` node rather than a distinct
  `SyntaxNodeKind`).
- `Parser.Command.sectionHeader`: `section` and `namespace` headers may carry
  only `public` and `@[expose]` visibility modifiers (`noncomputable section`,
  `meta section`, etc. remain rejected).
- `Parser.Command.declaration`: the inner declaration body (`args[1]`) must be
  one of `allowedDeclarationKinds`.
- `Parser.Command.mutual`: every element inside `mutual ... end` (`args[1]`)
  must satisfy `isAllowedNestedCommand`.
- `Parser.Command.in`: only `open` and `variable` may appear on the LHS
  (`args[0]`), and the RHS (`args[2]`) must satisfy `isAllowedNestedCommand`.
- `Parser.Attr.simple`, `Parser.Attr.instance`, `Parser.Attr.simp`, and
  `Parser.Command.eraseAttr`: attribute names must belong to
  `allowedAttributeNames` and carry no arguments or priority overrides. -/
def inspectNodeKind (k : SyntaxNodeKind) (args : Array Syntax)
    (requirePrelude : Bool := true) : IO Unit := do
  if k == ``Parser.Module.header then
    if requirePrelude then
      unless !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
        fail "explicit prelude is required"
  else if k == ``Parser.Command.sectionHeader then
    validateSectionHeader args
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

/-- Extend `openDecls` conservatively across an admitted `Parser.Command.open`
(`openSimple`) node so `Parser.Command.in` and `Parser.Command.mutual` inspect
their scoped commands under the opened namespaces without elaborating or running
parser callbacks. -/
def extendOpenDeclsForOpenCmd (currNs : Name) (openDecls : List OpenDecl)
    (openStx : Syntax) : List OpenDecl :=
  if !openStx.isOfKind ``Parser.Command.open then
    openDecls
  else
    let openDecl := openStx[1]
    if !openDecl.isOfKind ``Parser.Command.openSimple then
      openDecls
    else
      openDecl[0].getArgs.foldl (init := openDecls) fun ods idStx =>
        let id := idStx.getId
        let hasOpenDecl (ns : Name) : Bool :=
          ods.any fun
            | OpenDecl.simple existing _ => existing == ns
            | _ => false
        let cands := candidateOpenNamespaces currNs ods id
        let ods' := cands.foldl (init := ods) fun acc ns =>
          if hasOpenDecl ns then acc else OpenDecl.simple ns [] :: acc
        let stripped := id.replacePrefix rootNamespace .anonymous
        if hasOpenDecl stripped then ods'
        else OpenDecl.simple stripped [] :: ods'

/-- Recursively validate syntax tree `s` in a single top-down pass against the
closed `allowedKinds` allowlist during `"preflight"` (with `requirePrelude :=
true`) or `"headers"` (with `requirePrelude := false`). Pattern-matching
exhaustively on `Syntax` rejects recovery placeholders (`.missing`), validates
every identifier with `isValidSourceIdent`, and requires every non-`null`
`Syntax.node` kind to belong to `allowedKinds` and satisfy `inspectNodeKind`. -/
partial def inspectSyntax (allowedKinds : NameSet) (s : Syntax)
    (requirePrelude : Bool := true)
    (currNs : Name := .anonymous) (openDecls : List OpenDecl := [])
    (checkPureRefs : Bool := true) :
    IO Unit := do
  match s with
  | .missing => fail "unexpected missing syntax node"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do
      fail s!"invalid identifier {val}"
    if checkPureRefs then
      let checkPureIdent (cand : Name) : IO Unit := do
        if forbiddenPureIdentifiers.contains cand || isForbiddenPureNamespace cand then
          fail s!"disallowed reference {val}"
      checkPureIdent val
      for cand in candidateOpenNamespaces currNs openDecls val do
        checkPureIdent cand
  | .node _ k args =>
    if forbiddenPureTermKinds.contains k then
      fail s!"disallowed syntax {k}"
    unless k == nullKind || allowedKinds.contains k do
      fail s!"unsupported syntax kind {k}"
    inspectNodeKind k args requirePrelude
    if k == ``Parser.Command.in && checkPureRefs then
      inspectSyntax allowedKinds args[0]! requirePrelude currNs openDecls
        checkPureRefs
      inspectSyntax allowedKinds args[1]! requirePrelude currNs openDecls
        checkPureRefs
      let nextOpen := extendOpenDeclsForOpenCmd currNs openDecls args[0]!
      inspectSyntax allowedKinds args[2]! requirePrelude currNs nextOpen
        checkPureRefs
    else if k == ``Parser.Command.mutual && checkPureRefs then
      inspectSyntax allowedKinds args[0]! requirePrelude currNs openDecls
        checkPureRefs
      let mut mutOpen := openDecls
      for child in args[1]!.getArgs do
        inspectSyntax allowedKinds child requirePrelude currNs mutOpen
          checkPureRefs
        mutOpen := extendOpenDeclsForOpenCmd currNs mutOpen child
      inspectSyntax allowedKinds args[2]! requirePrelude currNs openDecls
        checkPureRefs
    else
      for child in args do
        inspectSyntax allowedKinds child requirePrelude currNs openDecls
          checkPureRefs

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

/-- Reject `ns` if it registers any scoped entry in `scopedNamespaces` or
belongs to a forbidden I/O, `Init.System.*`, `Std.Internal.UV.*`, or
`Lean.LoadDynlib` namespace. Scoped-extension rejection runs first so existing
diagnostics for `open Lean.PostprocessTraces` stay intact. -/
def rejectScopedNamespace (scopedNamespaces : NameSet) (how : String)
    (ns : Name) : IO Unit := do
  if scopedNamespaces.contains ns then
    fail s!"cannot {how} namespace {ns} with scoped syntax or extensions"
  if isForbiddenPureNamespace ns then
    fail s!"cannot {how} forbidden namespace {ns}"

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
        rejectScopedNamespace scopedNamespaces "open" stripped
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
  inspectSyntax allowedKinds stx true top.currNamespace top.openDecls
  let (nextEnv, nextScopes) ←
    applyCommandScope scopedNamespaces scopedPrefixes parserEnv scopes stx
  parseAndInspectCommands ctx scopedNamespaces scopedPrefixes nextEnv nextScopes
    moduleName allowedKinds nextState nextMessages

/-- Parsed header and tier metadata produced by `inspectSource` for one
repository `.lean` source file during `"preflight"` or
`"correspondence-preflight"`. -/
structure InspectedSource where
  moduleName : Name
  imports : Array Import
  isModule : Bool
  role : SourceRole

/-- Render an `InspectedSource` in the JSON wire format expected by
`anneal-audit`. -/
def InspectedSource.renderJson (s : InspectedSource) : Json :=
  Json.mkObj [
    ("module", toJson s.moduleName),
    ("imports", toJson s.imports),
    ("isModule", toJson s.isModule),
    ("trustTier", toJson s.role.renderTier?)]

/-- Enforce module-level trust-tier import isolation across preflighted sources
before compilation: reject duplicate `sources` entries and any source colliding
with `reservedModules` or `baseTiers`, then verify that every `vetted` module
imports `imp` if and only if `imp` belongs to `foundationSet` or another
`vetted` `Trusted` module (rejecting every `candidate:<feature>`,
`.repo .theory`, `.vendorMiri`, `.sysrootFoundation`, or unknown import
uniformly before compilation). -/
def checkPreflightTierImports (inspected : Array InspectedSource)
    (foundationSet : NameSet)
    (baseTiers : Std.HashMap Name TrustTier := {})
    (reservedModules : NameSet := {}) : IO Unit := do
  let mut seen : NameSet := {}
  let mut tiers := baseTiers
  for s in inspected do
    if seen.contains s.moduleName then
      fail s!"duplicate preflight source module {s.moduleName}"
    if reservedModules.contains s.moduleName ||
        baseTiers.contains s.moduleName then
      fail s!"preflight source module {s.moduleName} collides with base module"
    seen := seen.insert s.moduleName
    if let .trusted tier := s.role then
      tiers := tiers.insert s.moduleName tier
  for s in inspected do
    if s.role == .trusted .vetted then
      for imp in s.imports do
        if !foundationSet.contains imp.module then
          match tiers.get? imp.module with
          | some .vetted => pure ()
          | some depTier =>
            fail (s!"vetted module {s.moduleName} cannot import " ++
              s!"{depTier.render} module {imp.module}")
          | none =>
            fail (s!"vetted module {s.moduleName} cannot import " ++
              s!"non-foundation module {imp.module}")

/-- Parse and validate a single repository `.lean` source file during
`"preflight"` or `"correspondence-preflight"`. -/
def inspectSource (scopedNamespaces scopedPrefixes : NameSet)
    (parserEnv : Environment) (moduleName : Name)
    (path : System.FilePath) : IO InspectedSource := do
  let text ← IO.FS.readFile path
  let role ← extractSourceRole moduleName text
  let allowedKinds := role.allowedSyntaxKinds
  let ctx := Parser.mkInputContext text path.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then
    fail s!"header parser error in {moduleName}"
  inspectSyntax allowedKinds header.raw (checkPureRefs := false)
  let isModule := Elab.HeaderSyntax.isModule header
  let imports := Elab.HeaderSyntax.imports header
  for imp in imports do
    if imp.isMeta then
      fail "import modifiers are unsupported"
    if !imp.isExported && !isModule then
      fail "import modifiers are unsupported"
    if imp.importAll then
      let allowImportAll :=
        isModule && role == .theory &&
          allowedTheoryImportAllModules.contains imp.module
      unless allowImportAll do
        fail "import modifiers are unsupported"
    if isForbiddenPureImport imp.module then
      fail s!"disallowed sysroot import {imp.module} in {moduleName}"
  let rootScope : ParseScope :=
    { header := "", currNamespace := .anonymous, openDecls := [] }
  parseAndInspectCommands ctx scopedNamespaces scopedPrefixes parserEnv
    [rootScope] moduleName allowedKinds initial log
  return { moduleName, imports, isModule, role }

/-- Validate target module import edges (`"headers"`, `"spec-preflight"`, and
`"target-audit"`):

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
  inspectSyntax (.ofList allowedHeaderKinds) header.raw
    (requirePrelude := false) (checkPureRefs := false)
  let imports := Elab.HeaderSyntax.imports header
  validateTargetImports moduleName.toString imports
    (allowModule := isModule)
    (allowTheoryImportAll := isAnnealModuleName moduleName)
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("isModule", toJson isModule)]

/-- Parse only the import header of a pinned `vendor/lean-miri` source file
(`"vendor-headers"`) for parallel cold DAG scheduling in `anneal-audit`.
Unlike target `"headers"`, vendored Lean `module`-system sources may carry
`module`, `public`/`meta` import modifiers, or `Lean.*` imports that are
validated separately by `UPSTREAM_PIN.json` and Pass 2
`"correspondence-audit"`. -/
def inspectVendorHeader (moduleName : Name) (path : System.FilePath) :
    IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, state, messages) ← Parser.parseHeader ctx
  if messages.hasErrors || state.recovering then
    fail s!"header parser error in {moduleName}"
  let imports := Elab.HeaderSyntax.imports header
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports)]

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

/-- Reject `ns` if its root belongs to `forbiddenSpecRootNamespaces`. -/
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
parser environment (`loadExts := true`, zero target `.olean`s loaded). -/
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
    inspectSyntax (.ofList allowedHeaderKinds) header.raw
      (requirePrelude := false) (checkPureRefs := false)
    let imports := Elab.HeaderSyntax.imports header
    validateTargetImports moduleName.toString imports (allowModule := isModule)
    let rootScope : ParseScope :=
      { header := "", currNamespace := .anonymous, openDecls := [] }
    parseAndInspectSpecCommands ctx commandLikeKinds tacticLikeKinds env
      [rootScope] moduleName initial log (isModule := isModule)
    checked := checked.push (toJson moduleName)
  return Json.mkObj [("checked", .arr checked)]

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

/-- Validate `"moduleTiers"` entries into a deduplicated `TrustTier` map using
`validateModule` to enforce mode-specific module-name admissibility. -/
def parseTierEntries (tierEntries : Array (String × String))
    (validateModule : Name → IO Unit) :
    IO (Std.HashMap Name TrustTier) :=
  tierEntries.foldlM (init := ({} : Std.HashMap Name TrustTier))
    fun acc (mStr, rawTier) => do
      let m := mStr.toName
      if acc.contains m then fail s!"duplicate module tier for {m}"
      validateModule m
      let some tier := TrustTier.parse? rawTier
        | fail s!"invalid trust tier {rawTier} for {m}"
      return acc.insert m tier

/-- Parse `"moduleTiers"` and verify that every entry names a distinct module in
`trusted` with a valid `TrustTier`. -/
def parseModuleTiers (j : Json) (trusted : Array Name) :
    IO (Std.HashMap Name TrustTier) := do
  let tierEntries ← field (α := Array (String × String)) j "moduleTiers"
  parseTierEntries tierEntries fun m => do
    unless trusted.contains m do
      fail s!"trust tier declared for non-Trusted module {m}"

/-- Parse optional `"baseSources"` (`Array (String × String)`) passed to
`"preflight"` for already-staged Pass 1 `Trusted` modules, rejecting any
non-`Trusted`, foundation-colliding, or duplicate entry, and authenticate each
entry's syntax, header, and `-- anneal-trust-tier:` directive directly from
disk via `inspectSource`. -/
def inspectPreflightBaseSources (j : Json)
    (scopedNamespaces scopedPrefixes : NameSet)
    (parserEnv : Environment) (foundationSet : NameSet) :
    IO (Std.HashMap Name TrustTier × NameSet) := do
  match j.getObjVal? "baseSources" with
  | .error _ => return ({}, foundationSet)
  | .ok _ =>
    let entries ← field (α := Array (String × String)) j "baseSources"
    let mut baseTiers : Std.HashMap Name TrustTier := {}
    let mut reservedModules := foundationSet
    for (baseModStr, basePath) in entries do
      let m := baseModStr.toName
      unless isTrustedModuleName m do
        fail s!"non-Trusted base preflight source {m}"
      if foundationSet.contains m then
        fail s!"base preflight source {m} collides with foundation module"
      if baseTiers.contains m then
        fail s!"duplicate base preflight source module {m}"
      let baseInspected ←
        inspectSource scopedNamespaces scopedPrefixes parserEnv m basePath
      match baseInspected.role with
      | .trusted tier =>
        baseTiers := baseTiers.insert m tier
        reservedModules := reservedModules.insert m
      | .theory =>
        fail s!"non-Trusted base preflight source {m}"
    return (baseTiers, reservedModules)

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

/-- Top-level namespaces reserved for the Lean kernel and standard library.
Non-sysroot modules cannot declare definitions or arbitrary theorems under
these roots because Lean's C++ kernel accelerates primitives such as `Nat.gcd`,
`Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, and
`String.ofList` by name; shadowing an unimported kernel-accelerated name can
prove `False` with zero axioms or trigger ill-typed kernel WHNF reduction. -/
def reservedKernelRoots : List Name :=
  [`Nat, `String, `Char, `Bool, `Int, `Int8, `Int16, `Int32, `Int64, `ISize,
   `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Float, `Float32,
   `ByteArray, `Subarray, `Array, `List, `Option, `Sum, `Prod, `Fin, `Subtype,
   `Eq, `HEq, `Quot, `Classical, `Lean, `Init, `Std, `Lake, `LeanExport,
   `LeanIR, `System, `IO, `Task, `Thunk, `Unit, `PUnit, `Empty, `PEmpty, `True,
   `False, `And, `Or, `Not, `Iff, `Exists, `Sigma, `PSigma, `Decidable,
   `Nonempty, `Ordering, `Rat, `Except, `EStateM, `StateM]

/-- Kernel-accelerated constant names in Lean's C++ reducer (`reduce_nat` and
`reduce_string`). Even a `theorem` with one of these names triggers kernel WHNF
reduction, so non-sysroot modules may never declare them in any form. -/
def kernelAcceleratedNames : List Name :=
  [`Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd,
   `Nat.mod, `Nat.div, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor,
   `Nat.shiftLeft, `Nat.shiftRight, `String.ofList]

/-- Return `true` when `n` has at least two name components (not a bare root
like `Nat` or `String`). -/
def hasCompoundName : Name → Bool
  | .str .anonymous _ | .num .anonymous _ | .anonymous => false
  | _ => true

/-- Return `true` when `ci` is safe and non-partial, matching the subset of
declarations replayed by `Lean.Kernel.Environment.replay` (`!ci.isUnsafe &&
!ci.isPartial`). -/
def isCEnv (ci : ConstantInfo) : Bool :=
  !ci.isUnsafe && !ci.isPartial

/-- Return `true` when `a` and `b` are `.thmInfo` declarations matching Lean 4's
realized-theorem header-equality condition (`subsumesInfo`: equal `name`,
`type`, `levelParams`, and mutual block `all`). -/
def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    a.name == b.name && a.type == b.type &&
    a.levelParams == b.levelParams && ta.all == tb.all
  | _, _ => false

/-- Return `true` when `n` is defined in an imported module whose role in
`roles` satisfies `pred`. -/
def constHasRole (env : Environment) (roles : Std.HashMap Name ρ)
    (pred : ρ → Bool) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.modules[idx]? with
    | some mod =>
      match roles.get? mod.module with
      | some role => pred role
      | none => false
    | none => false
  | none => false

/-- Collect every pattern-matcher name recorded in `Meta.Match.Extension` across
all `.olean` modules loaded in `env` (populated by `finalizeImport` even with
`loadExts := false`). -/
def collectAllMatchers (env : Environment) : NameSet := Id.run do
  let mut matchers : NameSet := {}
  for modIdx in Array.range env.header.moduleData.size do
    for entry in
        Lean.Meta.Match.Extension.extension.getModuleEntries env modIdx do
      matchers := matchers.insert entry.name
  return matchers

/-- Return `true` when `s` is non-empty and consists strictly of `pfx`
followed by one or more ASCII decimal digits (used for `_sparseCasesOn_<N>`
inside unimported `TargetRole::Proof` modules). -/
def isDigitsAfterPrefix (pfx s : String) : Bool :=
  match s.dropPrefix? pfx with
  | some rest => !rest.isEmpty && rest.all Char.isDigit
  | none => false

/-- Return `true` when `(n, userN)` (with `userN := privateToUserName n`) is
either an imported compound declaration satisfying `isOrigin`, or an admissible
compiler-generated matcher/`splitter`/`SparseCasesOn` parent whose ancestor
chain terminates at an imported compound declaration satisfying `isOrigin`. -/
partial def isUpstreamHelperRoot (env : Environment) (allMatchers : NameSet)
    (isOrigin : Name → Bool) (allowUnimportedProofSparse : Bool)
    (n userN : Name) : Bool :=
  if hasCompoundName userN && isOrigin userN then
    true
  else
    match n, userN with
    | .str rawParent _, .str userParent "splitter" =>
      (allMatchers.contains rawParent || allMatchers.contains userParent) &&
        isUpstreamHelperRoot env allMatchers isOrigin
          allowUnimportedProofSparse rawParent userParent
    | .str rawParent _, .str userParent suffix =>
      let isKnownSparse :=
        (Lean.Meta.getSparseCasesOnInfoCore env n).isSome ||
          (Lean.Meta.getSparseCasesOnInfoCore env userN).isSome
      let isKnownMatcher := allMatchers.contains n || allMatchers.contains userN
      if isKnownSparse || isKnownMatcher then
        isUpstreamHelperRoot env allMatchers isOrigin
          allowUnimportedProofSparse rawParent userParent
      else if allowUnimportedProofSparse &&
          isDigitsAfterPrefix "_sparseCasesOn_" suffix then
        isUpstreamHelperRoot env allMatchers isOrigin
          allowUnimportedProofSparse rawParent userParent
      else
        false
    | _, _ => false

/-- Return `true` when `ci` is a Lean 4 lazily-generated helper attached to an
already-imported compound constant satisfying `isOrigin`, verified through
Lean's kernel and extension metadata (`Lean.isReservedName`,
`Meta.Match.Extension.extension`, and `Meta.getSparseCasesOnInfoCore`).
`allowUnimportedProofSparse` is enabled only for exported `TargetRole::Proof`
constants whose `.olean` is never loaded into `env`. -/
def isRealizedOrCompilerHelper (env : Environment) (allMatchers : NameSet)
    (isOrigin : Name → Bool) (ci : ConstantInfo)
    (allowUnimportedProofSparse : Bool := false) : Bool :=
  let n := ci.name
  let userN := privateToUserName n
  let hasParent :=
    isUpstreamHelperRoot env allMatchers isOrigin allowUnimportedProofSparse
  match ci, n, userN with
  | .thmInfo _, .str rawParent _, .str userParent suffix =>
    ((Lean.isReservedName env n || Lean.isReservedName env userN) &&
      hasParent rawParent userParent) ||
    ((allMatchers.contains rawParent || allMatchers.contains userParent) &&
      (suffix == "splitter" || Lean.Meta.isEqnReservedNameSuffix suffix ||
        Lean.Meta.Match.isCongrEqnReservedNameSuffix suffix) &&
      hasParent rawParent userParent) ||
    (allowUnimportedProofSparse && suffix == "else_eq" &&
      match rawParent, userParent with
      | .str gp _, .str ugp upSuffix =>
        isDigitsAfterPrefix "_sparseCasesOn_" upSuffix && hasParent gp ugp
      | _, _ => false)
  | .defnInfo _, .str rawParent _, .str userParent suffix =>
    isPrivateName n &&
      if suffix == "splitter" then
        (allMatchers.contains rawParent || allMatchers.contains userParent) &&
          hasParent rawParent userParent
      else if (Lean.Meta.getSparseCasesOnInfoCore env n).isSome ||
          (Lean.Meta.getSparseCasesOnInfoCore env userN).isSome then
        hasParent rawParent userParent
      else if allowUnimportedProofSparse &&
          isDigitsAfterPrefix "_sparseCasesOn_" suffix then
        match rawParent, userParent with
        | .str _ _, .str _ "splitter" => hasParent rawParent userParent
        | _, _ => false
      else
        false
  | _, _, _ => false

/-- Enforce per-constant policy invariants on a constant `ci` defined in Anneal
repository module `m` with `SourceRole` `role` (shared across Pass 1 and
Pass 2):

- Non-`Trusted` modules cannot declare constants in the `Trusted` root
  namespace (`privateToUserName` strips any `_private.<mod>.0` prefix first so
  `private` declarations inside `namespace Trusted` are also caught), except
  lazily-synthesized equation theorems and private matcher splitters attached
  to an already-imported compound `Trusted` constant
  (`isRealizedOrCompilerHelper env allMatchers isTrustedConst ci`).
- No repository module may declare any `kernelAcceleratedNames` constant or any
  constant (including theorems and `private` declarations) whose `userRoot`
  belongs to `reservedKernelRoots`, except lazily-synthesized equation theorems
  and private matcher splitters attached to an already-imported compound
  sysroot/foundation constant
  (`isRealizedOrCompilerHelper env allMatchers isFoundationConst ci`).
- Non-`Trusted` modules cannot declare `opaque` constants.
- No repository module may declare `unsafe`, `axiom`, or `quot` constants,
  unpaired `partial` constants, or omit a definition body. When
  `allowPairedPartial` is `true`, a safe `isPartial` `.defnInfo` matching
  `Compiler.isUnsafeRecName?` is deferred to the enclosing module's pairing
  check. -/
def validateRepoConstant (env : Environment) (allMatchers : NameSet)
    (m : Name) (role : SourceRole)
    (isTrustedConst isFoundationConst : Name → Bool)
    (ci : ConstantInfo) (allowPairedPartial : Bool := false) : IO Unit := do
  let isTrusted := role matches .trusted _
  let userName := privateToUserName ci.name
  let userRoot := userName.getRoot
  if !isTrusted && userRoot == `Trusted &&
      !isRealizedOrCompilerHelper env allMatchers isTrustedConst ci then
    fail (s!"non-Trusted module {m} cannot declare constant {ci.name} " ++
      "in Trusted namespace")
  if kernelAcceleratedNames.contains userName ||
      (reservedKernelRoots.contains userRoot &&
        !isRealizedOrCompilerHelper env allMatchers isFoundationConst ci) then
    fail (s!"repository module {m} cannot declare constant {ci.name} " ++
      s!"in reserved kernel namespace {userRoot}")
  if !isTrusted && (ci matches .opaqueInfo _) then
    fail s!"opaque declaration {ci.name} in {m} is not allowed outside Trusted"
  if ci.isAxiom then
    fail (if isTrusted then
      s!"Trusted axiom {ci.name}"
    else
      s!"strict axiom declaration {ci.name} in {m}")
  let checkReplayable :=
    if allowPairedPartial && ci.isPartial && !ci.isUnsafe &&
        (ci matches .defnInfo _) &&
        (Compiler.isUnsafeRecName? ci.name).isSome then
      if ci.hasValue true && (ci.value? true).isNone then
        fail s!"missing stored body {ci.name}"
      else
        pure ()
    else if isTrusted then
      ensureReplayableConstant "Trusted declaration" "" ci
    else
      ensureReplayableConstant "declaration" s!" in {m}" ci
  checkReplayable

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
Any module exporting a realized `.thmInfo` theorem already exported by another
module must satisfy `sameRealizedThmHeader` (`name`, `type`, `levelParams`, and
`all`), and every differing proof body is retained in `alternateProofs` for
fresh kernel verification via `checkAlternateProofs`. Non-theorem declarations
cannot change kind, safety, universe parameters, type, or value. -/
def inventoryAlternates (stored ci : ConstantInfo) :
    IO (Array ConstantInfo) := do
  unless stored.type == ci.type do
    fail s!"stored declaration type differs from inventory {ci.name}"
  match stored, ci with
  | .thmInfo a, .thmInfo b =>
    unless sameRealizedThmHeader stored ci do
      fail s!"inconsistent theorem metadata {ci.name}"
    if a.value == b.value then
      return #[]
    else
      -- Replay may reuse a selected theorem already in its base or another
      -- module. Retain both values so deduplication never hides an ill-typed
      -- proof body.
      return #[stored, ci]
  | _, _ =>
    unless kind stored == kind ci && stored.isUnsafe == ci.isUnsafe &&
        stored.isPartial == ci.isPartial &&
        stored.levelParams == ci.levelParams &&
        stored.value? true == ci.value? true do
      fail s!"stored declaration differs from inventory {ci.name}"
    return #[]

/-- Validate and record the `.olean` inventory (`constants` and
`extraConstNames`) of one Anneal repository module `mName` (`srcRole`) across
Pass 1 and Pass 2. Supports Lean 4 universal realized-theorem sharing
(`sameRealizedThmHeader` + `alternateProofs`) and 4-part `p._unsafe_rec` pairing
while excluding non-`isCEnv` helpers from replayable `locals`. -/
def collectRepoModuleConstants (env : Environment) (allMatchers : NameSet)
    (roles : Std.HashMap Name ρ)
    (isTrustedConst isFoundationConst : Name → Bool)
    (canShareRealizedFrom : ρ → Bool)
    (edgeViolation? : Name → ρ → Name → Name → ρ → Option String)
    (mName : Name) (srcRole : SourceRole) (mOriginRole : ρ) (data : ModuleData)
    (locals : Std.HashMap Name ConstantInfo)
    (pairedUnsafeRecs : Std.HashMap Name Name)
    (extraNames : NameSet) (alternateProofs : Array ConstantInfo)
    (altRoots : List Name) :
    IO (Std.HashMap Name ConstantInfo × Std.HashMap Name Name × NameSet ×
      Array ConstantInfo × List Name) := do
  let mut locals := locals
  let mut pairedUnsafeRecs := pairedUnsafeRecs
  let mut extraNames := extraNames
  let mut alternateProofs := alternateProofs
  let mut altRoots := altRoots
  let mut modSeen : NameSet := {}
  let mut modConsts : Std.HashMap Name ConstantInfo := {}
  let mut pendingUnsafeRecs : Array (ConstantInfo × Name) := #[]
  for ci in data.constants do
    if modSeen.contains ci.name then
      fail s!"duplicate declaration {ci.name}"
    modSeen := modSeen.insert ci.name
    let (orig, origRole) ← constProvenance env roles ci.name
    let stored ← lookupConst env ci.name "stored declaration"
    if orig == mName then
      if locals.contains ci.name || pairedUnsafeRecs.contains ci.name then
        fail s!"duplicate declaration {ci.name}"
      let origAlts ← inventoryAlternates stored ci
      alternateProofs := alternateProofs ++ origAlts
      for p in origAlts do
        altRoots := (← declarationEdges p).toList ++ altRoots
      validateRepoConstant env allMatchers mName srcRole isTrustedConst
        isFoundationConst ci (allowPairedPartial := true)
      modConsts := modConsts.insert ci.name ci
      if ci.isPartial then
        let some parent := Compiler.isUnsafeRecName? ci.name
          | fail s!"unsafe/partial declaration {ci.name} in {mName}"
        pendingUnsafeRecs := pendingUnsafeRecs.push (ci, parent)
      else
        locals := locals.insert ci.name ci
    else
      unless canShareRealizedFrom origRole &&
          sameRealizedThmHeader stored ci do
        fail s!"inventory origin mismatch {ci.name}"
      validateRepoConstant env allMatchers mName srcRole isTrustedConst
        isFoundationConst ci
      alternateProofs := alternateProofs ++ (← inventoryAlternates stored ci)
      let deps ← declarationEdges ci
      for dep in deps do
        let (depOrigin, depRole) ← constProvenance env roles dep
        if let some msg :=
            edgeViolation? ci.name mOriginRole dep depOrigin depRole then
          fail msg
        if pairedUnsafeRecs.contains dep then
          fail s!"paired _unsafe_rec helper {dep} cannot be referenced logically"
      altRoots := deps.toList ++ altRoots
  for (unsafeCi, parent) in pendingUnsafeRecs do
    match modConsts.get? parent with
    | some (parentCi@(.defnInfo _)) =>
      unless isCEnv parentCi do
        fail s!"unsafe/partial declaration {unsafeCi.name} in {mName}"
      pairedUnsafeRecs := pairedUnsafeRecs.insert unsafeCi.name parent
    | _ =>
      fail s!"unsafe/partial declaration {unsafeCi.name} in {mName}"
  for n in data.extraConstNames do
    let (orig, _) ← constProvenance env roles n
    unless orig == mName do
      fail s!"IR helper provenance mismatch {n}"
    if (env.checked.get.find? n).isSome then
      unless locals.contains n || pairedUnsafeRecs.contains n do
        fail s!"uninventoried kernel compiler helper {n}"
    else if srcRole matches .trusted _ then
      extraNames := extraNames.insert n
  return (locals, pairedUnsafeRecs, extraNames, alternateProofs, altRoots)

/-! ## Explicit raw-`UInt64` cached-metadata validation -/

/-- Pointer-identity memoization sets used while validating cached `Name.hash`,
`Level.data`, and `Expr.data` words.

Standard `Std.HashSet` instances hash and compare via the very cached fields
under inspection and could skip a distinct heap node whose structural twin had
valid metadata. Keying strictly on physical pointer identity (`PtrSet`) checks
every distinct deserialized object while keeping shared DAG traversal linear. -/
private unsafe structure CachedMetaMemo where
  names : PtrSet Name := mkPtrSet
  levels : PtrSet Level := mkPtrSet
  exprs : PtrSet Expr := mkPtrSet

/-- Recompute `Name.hash` from validated children and fail closed on any
raw-`UInt64` bit mismatch against the stored computed field.

The formulas mirror pinned Lean 4.34.1 `Init/Prelude.lean` (`Name.hash`). We
compare raw `UInt64` words rather than performing a structural pattern-match
rebuild because Lean's compiler can optimize non-recursive match-and-reconstruct
branches into constructor reuse (returning the original heap pointer and
preserving tampered cached words). -/
private unsafe def validateNameCachedHash (ref : IO.Ref CachedMetaMemo)
    (ctx : String) : Name → IO Unit
  | n => do
    -- Use `modifyGet` (never `ref.get` + `ref.set`) so `CachedMetaMemo` keeps
    -- reference count 1 and `PtrSet.insert` mutates in place in O(1).
    if (← ref.modifyGet fun st => (st.names.contains n, st)) then
      return ()
    let expected : UInt64 ← match n with
      | .anonymous => pure (.ofNatLT 1723 (of_decide_eq_true rfl))
      | .str p s =>
        validateNameCachedHash ref ctx p
        pure (mixHash p.hash s.hash)
      | .num p v =>
        validateNameCachedHash ref ctx p
        let vHash : UInt64 :=
          if h : v < UInt64.size then
            UInt64.ofNatLT v h
          else
            UInt64.ofNatLT 17 (of_decide_eq_true rfl)
        pure (mixHash p.hash vHash)
    unless expected == n.hash do
      throw <| IO.userError
        s!"cached metadata mismatch in {ctx}: Name.hash expected {expected}, found {n.hash}"
    ref.modify fun st => { st with names := st.names.insert n }

/-- Recompute `Level.data` from validated children and fail closed on any
raw-`UInt64` mismatch against the stored computed field (`Lean/Level.lean`). -/
private unsafe def validateLevelCachedData (ref : IO.Ref CachedMetaMemo)
    (ctx : String) : Level → IO Unit
  | l => do
    if (← ref.modifyGet fun st => (st.levels.contains l, st)) then
      return ()
    let expected : Level.Data ← match l with
      | .zero => pure (Level.mkData 2221 0 false false)
      | .mvar mvarId =>
        validateNameCachedHash ref ctx mvarId.name
        pure (Level.mkData (mixHash 2237 (hash mvarId)) 0 true false)
      | .param name =>
        validateNameCachedHash ref ctx name
        pure (Level.mkData (mixHash 2239 (hash name)) 0 false true)
      | .succ u =>
        validateLevelCachedData ref ctx u
        pure (Level.mkData (mixHash 2243 u.data.hash) (u.data.depth.toNat + 1)
          u.data.hasMVar u.data.hasParam)
      | .max u v =>
        validateLevelCachedData ref ctx u
        validateLevelCachedData ref ctx v
        pure (Level.mkData (mixHash 2251 (mixHash u.data.hash v.data.hash))
          (Nat.max u.data.depth.toNat v.data.depth.toNat + 1)
          (u.data.hasMVar || v.data.hasMVar)
          (u.data.hasParam || v.data.hasParam))
      | .imax u v =>
        validateLevelCachedData ref ctx u
        validateLevelCachedData ref ctx v
        pure (Level.mkData (mixHash 2267 (mixHash u.data.hash v.data.hash))
          (Nat.max u.data.depth.toNat v.data.depth.toNat + 1)
          (u.data.hasMVar || v.data.hasMVar)
          (u.data.hasParam || v.data.hasParam))
    let expectedBits : UInt64 := expected
    let actualBits : UInt64 := l.data
    unless expectedBits == actualBits do
      throw <| IO.userError
        s!"cached metadata mismatch in {ctx}: Level.data expected {expectedBits}, found {actualBits}"
    ref.modify fun st => { st with levels := st.levels.insert l }

/-- Validate `Name` hashes embedded in `Expr.mdata` key-value metadata. -/
private unsafe def validateMDataCachedNames (ref : IO.Ref CachedMetaMemo)
    (ctx : String) (m : MData) : IO Unit := do
  for (k, v) in m.entries do
    validateNameCachedHash ref ctx k
    if let .ofName n := v then
      validateNameCachedHash ref ctx n

/-- Recompute `Expr.data` from validated children and fail closed on any
raw-`UInt64` mismatch against the stored computed field (`Lean/Expr.lean`).

Every cached bit—32-bit hash, 8-bit `approxDepth`, `hasFVar`, `hasExprMVar`,
`hasLevelMVar`, `hasLevelParam`, and 20-bit `looseBVarRange`—is checked by
comparing the exact 64-bit `UInt64` word. -/
private unsafe def validateExprCachedData (ref : IO.Ref CachedMetaMemo)
    (ctx : String) : Expr → IO Unit
  | e => do
    if (← ref.modifyGet fun st => (st.exprs.contains e, st)) then
      return ()
    let expected : Expr.Data ← match e with
      | .const n lvls =>
        validateNameCachedHash ref ctx n
        for lvl in lvls do
          validateLevelCachedData ref ctx lvl
        pure (Expr.mkData (mixHash 5 (mixHash (hash n) (hash lvls)))
          0 0 false false (lvls.any Level.hasMVar) (lvls.any Level.hasParam))
      | .bvar idx =>
        pure (Expr.mkData (mixHash 7 (hash idx)) (idx + 1))
      | .sort lvl =>
        validateLevelCachedData ref ctx lvl
        pure (Expr.mkData (mixHash 11 (hash lvl))
          0 0 false false lvl.hasMVar lvl.hasParam)
      | .fvar fvarId =>
        validateNameCachedHash ref ctx fvarId.name
        pure (Expr.mkData (mixHash 13 (hash fvarId)) 0 0 true)
      | .mvar mvarId =>
        validateNameCachedHash ref ctx mvarId.name
        pure (Expr.mkData (mixHash 17 (hash mvarId)) 0 0 false true)
      | .mdata m body =>
        validateMDataCachedNames ref ctx m
        validateExprCachedData ref ctx body
        let d := body.data.approxDepth.toUInt32 + 1
        pure (Expr.mkData (mixHash d.toUInt64 body.data.hash)
          body.data.looseBVarRange.toNat d
          body.data.hasFVar body.data.hasExprMVar
          body.data.hasLevelMVar body.data.hasLevelParam)
      | .proj s i body =>
        validateNameCachedHash ref ctx s
        validateExprCachedData ref ctx body
        let d := body.data.approxDepth.toUInt32 + 1
        pure (Expr.mkData
          (mixHash d.toUInt64 (mixHash (hash s) (mixHash (hash i) body.data.hash)))
          body.data.looseBVarRange.toNat d
          body.data.hasFVar body.data.hasExprMVar
          body.data.hasLevelMVar body.data.hasLevelParam)
      | .app f a =>
        validateExprCachedData ref ctx f
        validateExprCachedData ref ctx a
        pure (Expr.mkAppData f.data a.data)
      | .lam n t b _ =>
        validateNameCachedHash ref ctx n
        validateExprCachedData ref ctx t
        validateExprCachedData ref ctx b
        let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
        pure (Expr.mkDataForBinder
          (mixHash d.toUInt64 (mixHash t.data.hash b.data.hash))
          (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1)) d
          (t.data.hasFVar || b.data.hasFVar)
          (t.data.hasExprMVar || b.data.hasExprMVar)
          (t.data.hasLevelMVar || b.data.hasLevelMVar)
          (t.data.hasLevelParam || b.data.hasLevelParam))
      | .forallE n t b _ =>
        validateNameCachedHash ref ctx n
        validateExprCachedData ref ctx t
        validateExprCachedData ref ctx b
        let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
        pure (Expr.mkDataForBinder
          (mixHash d.toUInt64 (mixHash t.data.hash b.data.hash))
          (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1)) d
          (t.data.hasFVar || b.data.hasFVar)
          (t.data.hasExprMVar || b.data.hasExprMVar)
          (t.data.hasLevelMVar || b.data.hasLevelMVar)
          (t.data.hasLevelParam || b.data.hasLevelParam))
      | .letE n t v b _ =>
        validateNameCachedHash ref ctx n
        validateExprCachedData ref ctx t
        validateExprCachedData ref ctx v
        validateExprCachedData ref ctx b
        let d := (max (max t.data.approxDepth.toUInt32 v.data.approxDepth.toUInt32)
          b.data.approxDepth.toUInt32) + 1
        pure (Expr.mkDataForLet
          (mixHash d.toUInt64 (mixHash t.data.hash (mixHash v.data.hash b.data.hash)))
          (max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat)
            (b.data.looseBVarRange.toNat - 1)) d
          (t.data.hasFVar || v.data.hasFVar || b.data.hasFVar)
          (t.data.hasExprMVar || v.data.hasExprMVar || b.data.hasExprMVar)
          (t.data.hasLevelMVar || v.data.hasLevelMVar || b.data.hasLevelMVar)
          (t.data.hasLevelParam || v.data.hasLevelParam || b.data.hasLevelParam))
      | .lit l =>
        pure (Expr.mkData (mixHash 3 (hash l)))
    let expectedBits : UInt64 := expected
    let actualBits : UInt64 := e.data
    unless expectedBits == actualBits do
      throw <| IO.userError
        s!"cached metadata mismatch in {ctx}: Expr.data expected {expectedBits}, found {actualBits}"
    ref.modify fun st => { st with exprs := st.exprs.insert e }

/-- Validate every cached `Name.hash`, `Level.data`, and `Expr.data` word
reachable inside a `ConstantInfo` (name, level parameters, type, value,
inductive/constructor metadata, and recursor rules). -/
private unsafe def validateConstantInfoCachedMetadata
    (ref : IO.Ref CachedMetaMemo) (ci : ConstantInfo) : IO Unit := do
  let ctx := s!"declaration {ci.name}"
  validateNameCachedHash ref ctx ci.name
  for lp in ci.levelParams do
    validateNameCachedHash ref ctx lp
  validateExprCachedData ref ctx ci.type
  match ci with
  | .defnInfo v =>
    validateExprCachedData ref ctx v.value
    for a in v.all do validateNameCachedHash ref ctx a
  | .thmInfo v =>
    validateExprCachedData ref ctx v.value
    for a in v.all do validateNameCachedHash ref ctx a
  | .opaqueInfo v =>
    validateExprCachedData ref ctx v.value
    for a in v.all do validateNameCachedHash ref ctx a
  | .inductInfo v =>
    for a in v.all do validateNameCachedHash ref ctx a
    for c in v.ctors do validateNameCachedHash ref ctx c
  | .ctorInfo v =>
    validateNameCachedHash ref ctx v.induct
  | .recInfo v =>
    for a in v.all do validateNameCachedHash ref ctx a
    for r in v.rules do
      validateNameCachedHash ref ctx r.ctor
      validateExprCachedData ref ctx r.rhs
  | .axiomInfo _ | .quotInfo _ => pure ()

private unsafe def validateConstantsCachedMetadataImpl
    (constants : Array ConstantInfo) : IO Unit := do
  let ref ← IO.mkRef ({} : CachedMetaMemo)
  for ci in constants do
    validateConstantInfoCachedMetadata ref ci

/-- Validate every cached `Name.hash`, `Level.data`, and `Expr.data` word across
`constants` using pointer-identity memoization. Fails closed on any single-bit
discrepancy before declarations reach kernel replay. -/
@[implemented_by validateConstantsCachedMetadataImpl]
def validateConstantsCachedMetadata (_constants : Array ConstantInfo) : IO Unit :=
  throw <| IO.userError
    "cached metadata validator requires runtime implementation"

/-- Check each alternate under a fresh name, bypassing replay's duplicate
optimization while preserving the declaration's type and universe parameters.
The pinned replay rule says "Ignore duplicate theorems" after comparing their
metadata; it does not check the duplicate proof value:
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L85-L97
-/
def checkAlternateProofs (replayed : Kernel.Environment)
    (alternateProofs : Array ConstantInfo) : IO Unit := do
  validateConstantsCachedMetadata alternateProofs
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

-- Lean 4.34 moved `Lean.Environment.replay` to `Lean.Kernel.Environment.replay`
-- and deprecated the old entry point; keep calling `Environment.replay` with
-- the deprecation linter disabled locally so this inspector builds cleanly with
-- `-DwarningAsError=true` across Lean 4.33 through 4.35.
set_option linter.deprecated false in
/-- Replay `replayMap` onto `base` with a fixed operational error prefix (so
`Lean.Replay`'s stringified `Kernel.Exception` cannot spoof `"policy:"`).
Validates cached `Name.hash`, `Level.data`, and `Expr.data` words across every
declaration in `replayMap` before handing objects to `Environment.replay`.
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L54-L63
https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean#L135-L136
-/
def replayKernelEnv (base : Kernel.Environment)
    (replayMap : Std.HashMap Name ConstantInfo)
    (errPrefix : String := "kernel replay failed") :
    IO Kernel.Environment := do
  validateConstantsCachedMetadata (replayMap.fold (init := #[]) fun acc _ ci => acc.push ci)
  try return (← (Environment.ofKernelEnv base).replay replayMap).toKernelEnv
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
    IO (Std.HashMap Name ConstantInfo × Std.HashMap Name Name × NameSet ×
      Array ConstantInfo × List Name) := do
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for (reqMod, _) in roles do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod}"
  let allMatchers := collectAllMatchers env
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut pairedUnsafeRecs : Std.HashMap Name Name := {}
  let mut extraNames : NameSet := {}
  let mut alternateProofs : Array ConstantInfo := #[]
  let mut altRoots : List Name := []
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    let some role := roles.get? m.module
      | fail s!"foreign module {m.module}"
    checkHeaderImports roles m.module role data RepoOrigin.importViolation?
    match role with
    | .foundation =>
      let mut modSeen : NameSet := {}
      for ci in data.constants do
        if modSeen.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        modSeen := modSeen.insert ci.name
        let (_, origRole) ← constProvenance env roles ci.name
        let stored ← lookupConst env ci.name "stored declaration"
        unless origRole == .foundation do
          fail s!"inventory origin mismatch {ci.name}"
        alternateProofs := alternateProofs ++
          (← inventoryAlternates stored ci)
      for n in data.extraConstNames do
        let (_, origRole) ← constProvenance env roles n
        unless origRole == .foundation do
          fail s!"IR helper provenance mismatch {n}"
    | .repo srcRole =>
      let isTrustedConst := constHasRole env roles
        (fun r => r matches .repo (.trusted _))
      let isFoundationConst := constHasRole env roles (· == .foundation)
      let (nextLocals, nextPaired, nextExtras, nextAlts, nextAltRoots) ←
        collectRepoModuleConstants env allMatchers roles isTrustedConst
          isFoundationConst (fun _ => true) RepoOrigin.edgeViolation?
          m.module srcRole role data locals pairedUnsafeRecs extraNames
          alternateProofs altRoots
      locals := nextLocals
      pairedUnsafeRecs := nextPaired
      extraNames := nextExtras
      alternateProofs := nextAlts
      altRoots := nextAltRoots
  for (n, _) in env.checked.get.constants do
    let (_, origRole) ← constProvenance env roles n
    if origRole != .foundation && !locals.contains n &&
        !pairedUnsafeRecs.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, pairedUnsafeRecs, extraNames, alternateProofs, altRoots)

/-- Verify that `aliasName` is a universe-monomorphic `.defnInfo` abbreviation
(`ReducibilityHints.abbrev`) in `expectedMod` whose body is directly
`Expr.const targetName []` for a repository constant `targetName`. -/
def requireMirPublicAlias (env : Environment)
    (locals : Std.HashMap Name ConstantInfo)
    (expectedMod aliasName targetName : Name) : IO Unit := do
  let some aliasCi := locals.get? aliasName
    | fail s!"missing required MIR public alias {aliasName}"
  let .defnInfo aliasDef := aliasCi
    | fail s!"expected {aliasName} to be a definition"
  unless aliasDef.hints matches .abbrev do
    fail s!"alias {aliasName} must be an abbrev (ReducibilityHints.abbrev)"
  unless aliasCi.levelParams.isEmpty do
    fail s!"alias {aliasName} must have no universe parameters"
  let aliasOrig ← origin env aliasName
  unless aliasOrig == expectedMod do
    fail (s!"expected {aliasName} to be defined in " ++
      s!"{expectedMod}, found {aliasOrig}")
  unless locals.contains targetName do
    fail s!"missing target {targetName} for alias {aliasName}"
  unless aliasCi.value? true == some (.const targetName []) do
    fail s!"alias {aliasName} must directly alias {targetName}"

/-- Verify that `Trusted.MirAst` and `Trusted.MirSemantics` are loaded as
`.repo (.trusted _)` modules and `Anneal.MirWp` and `Anneal.MirWp.Canaries`
are loaded as `.repo .theory` modules (whenever `requireMirWp` is `true` or any
MIR/`PureLift` module is loaded), that the core weakest-precondition adequacy
and fault-characterization theorems and the Profile v2 execution adequacy
theorem in `Anneal.MirWp` and all 25 non-vacuity and parameter-boundary
canaries in `Anneal.MirWp.Canaries` prove the exact `*Claim` propositions
defined in `Trusted.MirSemantics`, and that the public
`Trusted.{Crate, CrateTheorem, UnitTheorem, CrateV2, CrateTheoremV2,
UnitTheoremV2}` aliases in `Trusted.MirSemantics` directly reference their
canonical `Trusted.MirSemantics.*` declarations. -/
def verifyMirWpCoreTheorems (env : Environment)
    (roles : Std.HashMap Name RepoOrigin)
    (locals : Std.HashMap Name ConstantInfo)
    (requireMirWp : Bool) : IO Unit := do
  if requireMirWp || roles.contains `Anneal.PureLift ||
      roles.contains `Trusted.MirAst ||
      roles.contains `Trusted.MirSemantics ||
      roles.contains `Anneal.MirWp ||
      roles.contains `Anneal.MirWp.Canaries then
    unless roles.get? `Trusted.MirAst matches some (.repo (.trusted _)) do
      fail "missing required trusted module Trusted.MirAst"
    unless roles.get? `Trusted.MirSemantics matches some (.repo (.trusted _)) do
      fail "missing required trusted module Trusted.MirSemantics"
    unless roles.get? `Anneal.MirWp matches some (.repo .theory) do
      fail "missing required theory module Anneal.MirWp"
    unless roles.get? `Anneal.MirWp.Canaries matches some (.repo .theory) do
      fail "missing required theory module Anneal.MirWp.Canaries"
    let semMod := `Trusted.MirSemantics
    let wpMod := `Anneal.MirWp
    let canaryMod := `Anneal.MirWp.Canaries
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
    -- Profile v2 counterpart of `WpSoundnessClaim`: ties `BehaviorV2`,
    -- `DivergesV2`, and `SatisfiesPostV2`, which `SpecsV2.property`
    -- statements use, to the `initStateV2` / `StepV2` transition system.
    requireClaimProof env locals semMod wpMod
      `Trusted.MirSemantics.ExecSoundnessClaimV2
      (some `Anneal.MirWp.execProgV2)
      `Anneal.MirWp.wellFormed_and_spec_of_execV2
      [`Trusted.MirSemantics.SatisfiesPostV2,
        `Trusted.MirSemantics.DivergesV2,
        `Trusted.MirSemantics.BehaviorV2]
    -- Profile v2 `SafeContractV2` / `EffectMaskV2` soundness claim: roots all
    -- six `SafeContractV2` spec-vocabulary declarations in the TCB audit and
    -- ties them to `execProgV2` and `EffectMaskV2.noAbort`.
    requireClaimProof env locals semMod wpMod
      `Trusted.MirSemantics.SafeContractSoundnessClaimV2
      (some `Anneal.MirWp.execProgV2)
      `Anneal.MirWp.safeContract_soundness_of_execV2
      [`Trusted.MirSemantics.EffectMaskV2,
        `Trusted.MirSemantics.EffectMaskV2.noAbort,
        `Trusted.MirSemantics.SafeContractV2,
        `Trusted.MirSemantics.SafeContractV2.post,
        `Trusted.MirSemantics.SatisfiesSafeContractV2,
        `Trusted.MirSemantics.BodySatisfiesSafeContractV2]
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
            `Trusted.MirSemantics.readBytes]),
        (`Trusted.MirSemantics.CanaryPositiveCharAndCmpAnnealClaim,
          `Anneal.MirWp.canary_positive_char_and_cmp_anneal,
          [posClaim, `Trusted.MirSemantics.mkBinOpProg,
            `Trusted.MirAst.BinOp.cmp,
            `Trusted.MirAst.MirTy.char,
            `Trusted.MirSemantics.charVal,
            `Trusted.MirSemantics.mkCmpDiscriminantProg,
            `Trusted.MirSemantics.progCharSwitch]),
        (`Trusted.MirSemantics.CanaryNegativeCharAndCmpAnnealClaim,
          `Anneal.MirWp.canary_negative_char_and_cmp_anneal,
          [negClaim, `Trusted.MirSemantics.progInvalidCharConstUb,
            `Trusted.MirSemantics.progInvalidCharSwitchCaseUb,
            `Trusted.MirSemantics.mkBinOpProg,
            `Trusted.MirAst.BinOp.cmp,
            `Trusted.MirSemantics.mkUnOpProg]),
        (`Trusted.MirSemantics.CanaryPositiveOverflowOpsAnnealClaim,
          `Anneal.MirWp.canary_positive_overflow_ops_anneal,
          [posClaim, `Trusted.MirSemantics.mkBinOpProg,
            `Trusted.MirSemantics.overflowPairTy,
            `Trusted.MirAst.BinOp.addWithOverflow,
            `Trusted.MirAst.BinOp.subWithOverflow,
            `Trusted.MirAst.BinOp.mulWithOverflow]),
        (`Trusted.MirSemantics.CanaryPositiveIntToIntCastAnnealClaim,
          `Anneal.MirWp.canary_positive_int_to_int_cast_anneal,
          [posClaim, `Trusted.MirSemantics.mkIntToIntCastProg,
            `Trusted.MirAst.MirTy.char,
            `Trusted.MirSemantics.charVal]),
        (`Trusted.MirSemantics.CanaryNegativeIntToIntCastAnnealClaim,
          `Anneal.MirWp.canary_negative_int_to_int_cast_anneal,
          [negClaim, `Trusted.MirSemantics.mkIntToIntCastProg,
            `Trusted.MirAst.MirTy.char,
            `Trusted.MirSemantics.progCastUninitSourceUb])] do
      requireClaimProof env locals semMod canaryMod claimName none proofName
        reqConsts
    for (aliasName, targetName) in [
        (`Trusted.Crate, `Trusted.MirSemantics.Crate),
        (`Trusted.CrateTheorem, `Trusted.MirSemantics.CrateTheorem),
        (`Trusted.UnitTheorem, `Trusted.MirSemantics.UnitTheorem),
        (`Trusted.CrateV2, `Trusted.MirSemantics.CrateV2),
        (`Trusted.CrateTheoremV2, `Trusted.MirSemantics.CrateTheoremV2),
        (`Trusted.UnitTheoremV2, `Trusted.MirSemantics.UnitTheoremV2)] do
      requireMirPublicAlias env locals semMod aliasName targetName

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let roles ← buildRepoOrigins j foundation trusted theory
  let (locals, pairedUnsafeRecs, extraNames, alternateProofs, altRoots) ←
    verifyAndCollectLocals env roles
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
  let mut allLocalRoots := locals.fold (init := altRoots) fun acc n _ => n :: acc
  for ci in alternateProofs do
    allLocalRoots := ci.name :: (← declarationEdges ci).toList ++ allLocalRoots
  let provenance := constProvenance env roles
  let onVisit (n _m : Name) (_role : RepoOrigin) (ci : ConstantInfo) : IO Unit := do
    if pairedUnsafeRecs.contains n || !isCEnv ci then
      fail s!"paired _unsafe_rec helper {n} cannot be referenced logically"
  let (allAxioms, allVisited) ←
    closure (lookupConst env) provenance axiomPolicy allLocalRoots onVisit
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
def classifyCorrModulesWithTiers (j : Json) (env : Environment)
    (foundation trusted theory vendorMiri : Array Name)
    (tierMap : Std.HashMap Name TrustTier) :
    IO (Std.HashMap Name CorrOrigin) := do
  let sysrootFoundation ← names j "sysrootFoundation"
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

/-- Classify Pass 2 modules using `moduleTiers` from the compiled `.olean`
audit request (`classifyCorrModulesWithTiers`). -/
def classifyCorrModules (j : Json) (env : Environment)
    (foundation trusted theory vendorMiri : Array Name) :
    IO (Std.HashMap Name CorrOrigin) := do
  let tierMap ← parseModuleTiers j trusted
  classifyCorrModulesWithTiers j env foundation trusted theory vendorMiri tierMap

/-- Return `true` if `n` is `sorryAx` or one of the `Init.Core`
compiler-reflection primitives whose use trusts the Lean compiler and runtime
interpreter instead of the standalone kernel. -/
def isForbiddenVendorRef (n : Name) : Bool :=
  n == `sorryAx ||
  n == `Lean.ofReduceBool ||
  n == `Lean.ofReduceNat ||
  n == `Lean.trustCompiler ||
  n == `Lean.reduceBool ||
  n == `Lean.reduceNat

/-- Return the first forbidden vendor constant (`sorryAx` or a compiler
reflection primitive) directly referenced in `ci`'s type, value (including
`opaque` definitions), or recursor rules, if any. -/
def constantFindForbiddenVendorRef? (ci : ConstantInfo) : Option Name :=
  let findInExpr (e : Expr) : Option Name :=
    match e.find? fun
      | .const n _ => isForbiddenVendorRef n
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
      Std.HashMap Name ConstantInfo × Array ConstantInfo ×
      Array ConstantInfo × Std.HashMap Name Name × List Name) := do
  let allMatchers := collectAllMatchers env
  let mut repoLocals : Std.HashMap Name ConstantInfo := {}
  let mut corrLocals : Std.HashMap Name ConstantInfo := {}
  let mut vendorLocals : Std.HashMap Name ConstantInfo := {}
  let mut vendorOrigSeen : NameSet := {}
  let mut pairedUnsafeRecs : Std.HashMap Name Name := {}
  let mut alternateProofs : Array ConstantInfo := #[]
  let mut vendorAlternateProofs : Array ConstantInfo := #[]
  let mut altRoots : List Name := []
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
        if orig == m.module then
          unless kind stored == kind ci && stored.isUnsafe == ci.isUnsafe &&
              stored.isPartial == ci.isPartial && stored.type == ci.type &&
              stored.value? true == ci.value? true &&
              stored.levelParams == ci.levelParams do
            fail s!"stored declaration differs from inventory {ci.name}"
        else
          unless sameRealizedThmHeader stored ci do
            fail s!"duplicate declaration {ci.name}"
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
        if let some badRef := constantFindForbiddenVendorRef? ci then
          if badRef == `sorryAx then
            fail (s!"vendor Miri module {m.module} constant {ci.name} " ++
              "references sorryAx")
          else
            fail (s!"vendor Miri module {m.module} constant {ci.name} " ++
              s!"references forbidden compiler primitive {badRef}")
        if orig == m.module then
          vendorOrigSeen := vendorOrigSeen.insert ci.name
        match vendorLocals.get? ci.name with
        | some prev =>
          unless sameRealizedThmHeader prev ci do
            fail s!"duplicate declaration {ci.name}"
          vendorAlternateProofs := vendorAlternateProofs ++
            (← inventoryAlternates prev ci)
          for dep in ← declarationEdges ci do
            let (depOrig, depRole) ← constProvenance env roles dep
            if let some msg :=
                CorrOrigin.edgeViolation? ci.name .vendorMiri dep depOrig depRole then
              fail msg
        | none =>
          vendorLocals := vendorLocals.insert ci.name ci
    | .repo srcRole =>
      let isTrustedConst := constHasRole env roles
        (fun r => r matches .repo (.trusted _))
      let isFoundationConst := constHasRole env roles
        (fun r => r == .foundation || r == .sysrootFoundation)
      let (nextLocals, nextPaired, _, nextAlts, nextAltRoots) ←
        collectRepoModuleConstants env allMatchers roles isTrustedConst
          isFoundationConst
          (fun r => !(r matches .vendorMiri))
          CorrOrigin.edgeViolation? m.module srcRole role data repoLocals
          pairedUnsafeRecs {} alternateProofs altRoots
      repoLocals := nextLocals
      pairedUnsafeRecs := nextPaired
      alternateProofs := nextAlts
      altRoots := nextAltRoots
      if corrModules.contains m.module then
        for ci in data.constants do
          unless pairedUnsafeRecs.contains ci.name do
            if repoLocals.contains ci.name then
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
      unless repoLocals.contains n || pairedUnsafeRecs.contains n do
        fail s!"uninventoried constant {n}"
  return (repoLocals, corrLocals, vendorLocals, alternateProofs,
    vendorAlternateProofs, pairedUnsafeRecs, altRoots)

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

/-- Verify that all 38 Pass 2 correspondence, choice-coupled, wiring,
`AllowedStep` soundness, byte-codec, and canary (`D6`–`D17`) claims—covering
aggregate and choice-coupled correspondence and fault equivalence,
`ExecutionMachine.step` / `OperandMachine.evalOperand` /
`LocalAccess.evalOperand` `deinitMovedPlace` wiring, `RefStep` soundness for
`RefAllowedStep`, codec round-trip, constructor preservation, uniqueness,
simulation, `Trusted.MirSemantics` byte encoding against `lean-miri`
`Allocation` scalar accesses, and canaries (including `char` comparison,
`BinOp.cmp`, and `char` `switchInt` in `D14`, `CastKind.intToInt` in `D15`,
`BinOp.*WithOverflow` pairs in `D16`, and intra-crate `.call` + pinned
`core::num` `.sysrootCall` in `D17`)—are present in
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
         `Miri.Memory.Allocation.writeUninit]),
      (`Trusted.Correspondence.CanaryD14CharCmpAndSwitchOkClaim,
       `Anneal.MirCorrespondenceProof.canary_D14_char_cmp_and_switch_ok,
       [`Trusted.MirSemantics.mkBinOpProg,
         `Trusted.MirAst.BinOp.cmp,
         `Trusted.MirAst.MirTy.char,
         `Trusted.MirSemantics.mkCmpDiscriminantProg,
         `Trusted.MirSemantics.progCharSwitch,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD15IntToIntCastClaim,
       `Anneal.MirCorrespondenceProof.canary_D15_int_to_int_cast,
       [`Trusted.MirSemantics.mkIntToIntCastProg,
         `Trusted.MirAst.MirTy.char,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.MirSemantics.ReachesResult,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.RefReachesOutcome,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD16WithOverflowOkClaim,
       `Anneal.MirCorrespondenceProof.canary_D16_with_overflow_ok,
       [`Trusted.MirSemantics.mkBinOpProg,
         `Trusted.MirSemantics.overflowPairTy,
         `Trusted.MirAst.BinOp.addWithOverflow,
         `Trusted.MirAst.BinOp.subWithOverflow,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD17CallAndSysrootCallClaim,
       `Anneal.MirCorrespondenceProof.canary_D17_call_and_sysroot_call,
       [`Trusted.Correspondence.progDirectCallD17,
         `Trusted.Correspondence.progSysrootUncheckedAddOkD17,
         `Trusted.Correspondence.progSysrootUncheckedAddUbD17,
         `Trusted.Correspondence.queryU16_19,
         `Trusted.MirSemantics.queryEmpty,
         `Trusted.MirSemantics.scalarNatVal,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.MirSemantics.ReachesResult,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.RefReachesOutcome,
         `Trusted.Correspondence.encodeProg]),
      (`Trusted.Correspondence.CanaryD17AssertPanicAbortClaim,
       `Anneal.MirCorrespondenceProof.canary_D17_assert_panic_abort,
       [`Trusted.Correspondence.mkAssertProg,
         `Trusted.MirAst.PanicStrategy.abort,
         `Trusted.MirAst.PanicStrategy.unwind,
         `Trusted.MirAst.AssertKind.divByZero,
         `Trusted.MirAst.AssertKind.boundsCheck,
         `Trusted.MirAst.AssertKind.misalignedPtrDeref,
         `Trusted.MirAst.UnwindAction.continue_,
         `Trusted.MirAst.UnwindAction.cleanup,
         `Trusted.MirSemantics.TerminalOut.aborted,
         `Trusted.MirSemantics.WellFormed,
         `Trusted.MirSemantics.Behavior,
         `Trusted.MirSemantics.ReachesResult,
         `Trusted.Correspondence.RefWellFormed,
         `Trusted.Correspondence.RefBehavior,
         `Trusted.Correspondence.RefReachesOutcome,
         `Trusted.Correspondence.encodeProg])] do
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
reaches all 39 required live `vendor/lean-miri` `ExecutionMachine` primitives
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
      `Miri.Interpreter.IntegerOps.binaryChar,
      `Miri.Interpreter.Cast.cast,
      `Miri.Interpreter.IntegerCast.cast,
      `Miri.Interpreter.Discriminant.readDiscriminant,
      `Miri.Interpreter.Discriminant.discriminantForVariant,
      `Miri.Memory.ScalarInt.truncateFromUInt,
      `Miri.Memory.ScalarInt.tryFromUInt,
      `Miri.Memory.ScalarInt.tryToBool,
      `Miri.Memory.ScalarInt.toChar,
      `Miri.Memory.ScalarInt.ofChar] do
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
  let foundationSet : NameSet := .ofList foundation.toList
  let (baseTiers, reservedBaseModules) ← do
    let baseParserEnv ← importCorrEnv foundation true
    let baseScopedNs ← collectScopedExtensionNamespaces baseParserEnv
    let baseScopedPrefixes := collectScopedNamespacePrefixes baseScopedNs
    inspectPreflightBaseSources j baseScopedNs baseScopedPrefixes
      baseParserEnv foundationSet
  for (m, _) in baseTiers do
    unless trusted.contains m do
      fail s!"extra base preflight source {m} missing from trusted inventory"
  for m in trusted do
    unless baseTiers.contains m do
      fail s!"missing base preflight source for Trusted module {m}"
  let env ← importCorrEnv (foundation ++ trusted ++ theory ++ vendorMiri) true
  let baseRoles ← classifyCorrModulesWithTiers j env foundation trusted theory
    vendorMiri baseTiers
  let reservedModules := baseRoles.fold (init := reservedBaseModules)
    fun acc m _ => acc.insert m
  let scopedNamespaces ← collectScopedExtensionNamespaces env
  let scopedPrefixes := collectScopedNamespacePrefixes scopedNamespaces
  let inspected ←
    sources.mapM fun (n, p) =>
      inspectSource scopedNamespaces scopedPrefixes env n.toName p
  checkPreflightTierImports inspected foundationSet baseTiers reservedModules
  return Json.mkObj [("headers", .arr (inspected.map InspectedSource.renderJson))]

/-- Collect validated `.repo`, correspondence, and `.vendorMiri` inventories
from the full Pass 2 environment in a dedicated scope so `env` can be released
before constructing the clean sysroot replay base under `-M8192`. -/
def collectCorrEnv (j : Json)
    (foundation allTrusted allTheory vendorMiri : Array Name)
    (corrModSet : NameSet) :
    IO (Std.HashMap Name CorrOrigin × Std.HashMap Name ConstantInfo ×
      Std.HashMap Name ConstantInfo × Std.HashMap Name ConstantInfo ×
      Array ConstantInfo × Array ConstantInfo × Std.HashMap Name Name ×
      List Name × Array Name) := do
  let env ← importCorrEnv (foundation ++ allTrusted ++ allTheory ++ vendorMiri)
  let roles ← classifyCorrModules j env foundation allTrusted
    allTheory vendorMiri
  let (repoLocals, corrLocals, vendorLocals, repoAlternateProofs,
      vendorAlternateProofs, pairedUnsafeRecs, repoAltRoots) ←
    verifyAndCollectCorrLocals env roles corrModSet
  checkDeclarationEdges env roles repoLocals CorrOrigin.edgeViolation?
  for (_, ci) in repoLocals do
    for dep in ← declarationEdges ci do
      if pairedUnsafeRecs.contains dep then
        fail s!"paired _unsafe_rec helper {dep} cannot be referenced logically"
  for dep in repoAltRoots do
    if pairedUnsafeRecs.contains dep then
      fail s!"paired _unsafe_rec helper {dep} cannot be referenced logically"
  let sysrootBaseMods := env.header.modules.filterMap fun m =>
    match roles.get? m.module with
    | some .foundation | some .sysrootFoundation => some m.module
    | _ => none
  let vendorReplayLocals :=
    vendorLocals.fold (init := ({} : Std.HashMap Name ConstantInfo))
      fun acc n ci =>
        if ci.isPartial then acc else acc.insert n ci
  return (roles, repoLocals, corrLocals, vendorReplayLocals,
    repoAlternateProofs, vendorAlternateProofs, pairedUnsafeRecs, repoAltRoots,
    sysrootBaseMods)

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
    (vendorAlternateProofs repoAlternateProofs : Array ConstantInfo)
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
  checkAlternateProofs replayedVendor vendorAlternateProofs
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
  checkAlternateProofs replayedRepo repoAlternateProofs
  let corrReplayed :=
    corrLocals.fold (init := (0 : Nat)) fun acc n _ =>
      if repoLocals.contains n && (replayedRepo.find? n).isSome then acc + 1
      else acc
  unless corrReplayed == corrLocals.size do
    fail (s!"correspondence kernel replay covered {corrReplayed} of " ++
      s!"{corrLocals.size} correspondence declarations")
  return (miriReplayed, corrReplayed)

/-- Verify the 36-root `Miri.Interpreter.ExecutionMachine` cone and—when
Pass 2 correspondence modules are present—all 38 correspondence, choice-coupled,
wiring, `AllowedStep` soundness, byte-codec, and canary claims,
reference-evaluator independence, and the correspondence dependency cone in a
dedicated scope. -/
def verifyCorrConesAndClaims
    (foundation allTrusted allTheory vendorMiri : Array Name)
    (roles : Std.HashMap Name CorrOrigin)
    (corrLocals : Std.HashMap Name ConstantInfo) (corrModSet : NameSet)
    (repoAltRoots : List Name) (repoAlternateProofs : Array ConstantInfo)
    (axiomPolicy : Array (String × String)) :
    IO (Array Name × Nat × Array Name × Nat) := do
  let env ← importCorrEnv (foundation ++ allTrusted ++ allTheory ++ vendorMiri)
  let (miriAxioms, miriVisited) ←
    verifyMiriExecutionMachineCone env roles axiomPolicy
  if corrModSet.isEmpty then
    return (miriAxioms, miriVisited.size, #[], 0)
  verifyCorrespondenceClaims env corrLocals
  verifyRefEvaluatorIndependence env roles corrModSet axiomPolicy
  let mut corrRoots := corrLocals.fold (init := repoAltRoots) fun acc n _ => n :: acc
  for ci in repoAlternateProofs do
    corrRoots := ci.name :: (← declarationEdges ci).toList ++ corrRoots
  let (corrAxioms, corrVisited) ←
    closureCorr env roles axiomPolicy corrRoots
  return (miriAxioms, miriVisited.size, corrAxioms, corrVisited.size)

/-- Execute Phase 3 (`"correspondence-audit"`) on the Pass 2 correspondence
and `lean-miri` closure environment.

Pass 2 replays EVERY non-`isPartial` `.vendorMiri` declaration (39,088
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
  let (roles, repoLocals, corrLocals, vendorReplayLocals, repoAlternateProofs,
      vendorAlternateProofs, _pairedUnsafeRecs, repoAltRoots, sysrootBaseMods) ←
    collectCorrEnv j foundation allTrusted allTheory vendorMiri corrModSet
  let (miriReplayed, corrReplayed) ←
    replayCorrAndVendor sysrootStr roles sysrootBaseMods vendorReplayLocals
      repoLocals corrLocals vendorAlternateProofs repoAlternateProofs
      (!corrModSet.isEmpty)
  -- Restore the Pass 2 search path dropped during sysroot-only vendor replay.
  initHermeticSearchPath sysrootStr (spRaw.toList.map System.FilePath.mk)
  let (miriAxioms, miriVisitedSize, corrAxioms, corrVisitedSize) ←
    verifyCorrConesAndClaims foundation allTrusted allTheory vendorMiri roles
      corrLocals corrModSet repoAltRoots repoAlternateProofs axiomPolicy
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

/-- Return `true` when `n` (ignoring private prefixes) names `Lean.Syntax` or a
declaration beneath `Lean.Syntax`. -/
def isLeanSyntaxConst (n : Name) : Bool :=
  let u := (privateToUserName n).replacePrefix rootNamespace .anonymous
  u == `Lean.Syntax || (`Lean.Syntax).isPrefixOf u

/-- Return `true` when `n` (ignoring private prefixes) names one of Lean's
runtime panic primitives or panicking partial helpers (such as `outOfBounds`,
`GetElem?.getElem!`, `List.head!`, `Option.get!`, `Array.back!`,
`List.getLast!`, `List.tail!`, `Array.get!Internal`,
`String.Pos.sliceOrPanic`, or `String.Slice.Pos.sliceOrPanic`).

Checked directly on every `TargetRole::Specification` declaration (rather than
transitively through `Init`/`Std` library internals) because `Init.Data.String`
helpers reached by `deriving Repr` legitimately reference `panicWithPosWithDecl`
internally, whereas authored specification code must never invoke panic
primitives or panicking `!` helpers. -/
def isPanicSpecConst (n : Name) : Bool :=
  let u := (privateToUserName n).replacePrefix rootNamespace .anonymous
  [`panic, `panicCore, `panicWithPos, `panicWithPosWithDecl,
    `outOfBounds, `String.Pos.sliceOrPanic,
    `String.Slice.Pos.sliceOrPanic].contains u ||
    hasBangComponent u

/-- Narrowed transitive effect/meta/`System`/debug/unbounded-loop ban enforced
across all declarations reachable from any `TargetRole::Specification` module.
Preserves `System.Platform.{numBits, getNumBits, numBits_eq}` (and their
compiler-private proof auxiliaries). -/
def isForbiddenSpecTransitiveConst (n : Name) : Bool :=
  let u := (privateToUserName n).replacePrefix rootNamespace .anonymous
  let r := u.getRoot
  if [`IO, `BaseIO, `EIO, `EST, `ST, `Task].contains r then
    true
  else if [`Lean.Macro, `Lean.Elab, `Lean.Core, `Lean.Meta,
      `Lean.Environment, `Lean.Compiler, `Lean.Internal,
      `Lean.Loop, `repeatM,
      `Lean.LoadDynlib, `Lean.loadDynlib, `Lean.loadPlugin, `Lean.Dynlib,
      `Lean.getGithash, `Lean.version,
      `Init.System, `Std.Internal.UV, `Dynlib].any
        (fun pre => u == pre || pre.isPrefixOf u) then
    true
  else if r == `System then
    !(allowedSystemPlatformDecls.any fun ok => u == ok || ok.isPrefixOf u)
  else
    forbiddenPureIdentifiers.contains u

/-- Check the exact first three parts of the 4-part `p._unsafe_rec` pairing
invariant for a `.source .specification` constant `ci` in module `m`:
1. `ci.isPartial && !ci.isUnsafe` and `ci` is a `.defnInfo`,
2. `ci.name` has shape `p._unsafe_rec`, and
3. `p` is defined in the same specification module `m` as a total, non-opaque
   `.defnInfo`. Returns `some p` when paired, or `none` otherwise. -/
def pairedSpecUnsafeRecParent? (env : Environment) (m : Name)
    (ci : ConstantInfo) : IO (Option Name) := do
  if !ci.isPartial || ci.isUnsafe || !(ci matches .defnInfo _) then
    return none
  let some parent := Compiler.isUnsafeRecName? ci.name | return none
  let some parentCi := env.checked.get.find? parent | return none
  let parentOrig ← origin env parent
  if parentOrig == m && (parentCi matches .defnInfo _) && isCEnv parentCi then
    return some parent
  return none

/-- Mutable memoized traversal state shared across Phase 1 (claim +
specification closure) and Phase 2 (proof closure) of `"target-audit"`. -/
structure TargetClosureState where
  visited : NameSet := {}
  axioms : NameSet := {}
  sorryDecls : NameSet := {}
  alternateProofs : Array ConstantInfo := #[]
  edgesCache : Std.HashMap Name NameSet := {}

/-- Run one phase of the unified `"target-audit"` dependency closure from
`initialPending`, reusing memoized state across Phase 1 (`inPhase1 := true`)
and Phase 2 (`inPhase1 := false`).

Per-edge `sorryAx` admission runs in `parent`'s outgoing edge loop before
`visited` short-circuiting so every proof declaration referencing `sorryAx` is
recorded in `sorryDecls`, while any `sorryAx` reference from Phase 1 or from a
non-`.proof` origin fails closed even when `allowSorryInProof` is `true`. -/
def runTargetClosurePhase
    (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO (Name × TargetOrigin))
    (axiomPolicy : Array (String × String))
    (libraryInventories : Std.HashMap Name NameSet)
    (libraryExports : Std.HashMap Name (Array ConstantInfo))
    (inPhase1 : Bool) (allowSorryInProof : Bool)
    (phase1Closure : NameSet) (initialPending : List Name)
    (initState : TargetClosureState) : IO TargetClosureState := do
  let mut st := initState
  let mut pending := initialPending
  while !pending.isEmpty do
    let n :: rest := pending | break
    pending := rest
    if st.visited.contains n then
      continue
    st := { st with visited := st.visited.insert n }
    let (orig, role) ← provenance n
    let ci ← lookup n
    if ci.isAxiom then
      unless axiomPolicy.contains (n.toString, orig.toString) do
        fail s!"unapproved axiom {n} from {orig}"
      st := { st with axioms := st.axioms.insert n }
    let deps ← match st.edgesCache.get? n with
      | some cached => pure cached
      | none =>
        let computed ← declarationEdges ci
        st := { st with edgesCache := st.edgesCache.insert n computed }
        pure computed
    if role == .source .specification then
      if ci matches .opaqueInfo _ then
        fail s!"opaque declaration {n} is not allowed in specification"
      for dep in deps do
        if isLeanSyntaxConst dep || isPanicSpecConst dep then
          fail s!"specification declaration {n} cannot reference {dep}"
    for dep in deps do
      let (depMod, depRole) ← provenance dep
      if dep == `sorryAx && depMod == `Init.Prelude then
        let sorryCi ← lookup dep
        unless sorryCi.isAxiom do
          fail s!"unexpected non-axiom {dep} in {depMod}"
        if let some msg := role.edgeViolation? n dep depRole then
          fail msg
        if !inPhase1 && allowSorryInProof &&
            role == .source .proof && !phase1Closure.contains n then
          st := { st with
            sorryDecls := st.sorryDecls.insert n
            axioms := st.axioms.insert dep }
        else
          fail s!"unapproved axiom {dep} from {depMod}"
      else if !st.visited.contains dep then
        pending := dep :: pending
    if let .library := role then
      unless (libraryInventories.getD orig {}).contains n do
        fail s!"uninventoried target library dependency {n}"
    for exportedCi in libraryExports.getD n #[] do
      match role with
      | .foundation | .library => pure ()
      | .source _ => fail s!"target library inventory origin mismatch {n}"
      let alternatives ← inventoryAlternates ci exportedCi
      for proof in alternatives do
        let altDeps ← declarationEdges proof
        let merged := (st.edgesCache.getD n {}) ++ altDeps
        st := { st with edgesCache := st.edgesCache.insert n merged }
        -- A discarded proof is still a library export. Its own edges cannot
        -- acquire target-source authority or bypass the 3-axiom ceiling.
        for dep in altDeps do
          let (depMod, depRole) ← provenance dep
          if let some msg :=
              TargetOrigin.edgeViolation? n .library dep depRole then
            fail msg
          if dep == `sorryAx && depMod == `Init.Prelude then
            fail s!"unapproved axiom {dep} from {depMod}"
          if !st.visited.contains dep then
            pending := dep :: pending
      st := { st with alternateProofs := st.alternateProofs ++ alternatives }
  return st

/-! ## Isolated structural proof-module export/decode (`"target-export"`) -/

/-- Pointer-identity interning pools used by `"target-export"` to serialize
proof-module `Name`, `Level`, and `Expr` DAGs into pure structural JSON with
zero heap pointers and zero cached metadata words. -/
private unsafe structure ProofExportPool where
  nameIds : PtrMap Name Nat := mkPtrMap
  names : Array Json := #[]
  levelIds : PtrMap Level Nat := mkPtrMap
  levels : Array Json := #[]
  exprIds : PtrMap Expr Nat := mkPtrMap
  exprs : Array Json := #[]

private unsafe def internExportName (ref : IO.Ref ProofExportPool)
    (n : Name) : IO Nat := do
  -- Use `modifyGet` so `ProofExportPool` keeps reference count 1 and
  -- `PtrMap.insert` / `Array.push` stay O(1) instead of cloning the pools.
  if let some idx ← ref.modifyGet fun st => (st.nameIds.find? n, st) then
    return idx
  let encoded : Json ← match n with
    | .anonymous => pure (.arr #[toJson "a"])
    | .str pre s =>
      let preId ← internExportName ref pre
      pure (.arr #[toJson "s", toJson preId, toJson s])
    | .num pre v =>
      let preId ← internExportName ref pre
      pure (.arr #[toJson "n", toJson preId, toJson (toString v)])
  ref.modifyGet fun st =>
    let idx := st.names.size
    (idx, { st with
      nameIds := st.nameIds.insert n idx
      names := st.names.push encoded })

private unsafe def internExportLevel (ref : IO.Ref ProofExportPool)
    (l : Level) : IO Nat := do
  if let some idx ← ref.modifyGet fun st => (st.levelIds.find? l, st) then
    return idx
  let encoded : Json ← match l with
    | .zero => pure (.arr #[toJson "z"])
    | .succ u =>
      let uid ← internExportLevel ref u
      pure (.arr #[toJson "s", toJson uid])
    | .max u v =>
      let uid ← internExportLevel ref u
      let vid ← internExportLevel ref v
      pure (.arr #[toJson "m", toJson uid, toJson vid])
    | .imax u v =>
      let uid ← internExportLevel ref u
      let vid ← internExportLevel ref v
      pure (.arr #[toJson "i", toJson uid, toJson vid])
    | .param n =>
      let nid ← internExportName ref n
      pure (.arr #[toJson "p", toJson nid])
    | .mvar m =>
      let nid ← internExportName ref m.name
      pure (.arr #[toJson "v", toJson nid])
  ref.modifyGet fun st =>
    let idx := st.levels.size
    (idx, { st with
      levelIds := st.levelIds.insert l idx
      levels := st.levels.push encoded })

private def binderInfoCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

private def binderInfoOfCode? : Nat → Option BinderInfo
  | 0 => some .default
  | 1 => some .implicit
  | 2 => some .strictImplicit
  | 3 => some .instImplicit
  | _ => none

private def safetyCode : DefinitionSafety → Nat
  | .unsafe => 0
  | .safe => 1
  | .partial => 2

private def safetyOfCode? : Nat → Option DefinitionSafety
  | 0 => some .unsafe
  | 1 => some .safe
  | 2 => some .partial
  | _ => none

private def quotKindCode : QuotKind → Nat
  | .type => 0
  | .ctor => 1
  | .lift => 2
  | .ind => 3

private def quotKindOfCode? : Nat → Option QuotKind
  | 0 => some .type
  | 1 => some .ctor
  | 2 => some .lift
  | 3 => some .ind
  | _ => none

private def encodeReducibilityHints : ReducibilityHints → Json
  | .opaque => .arr #[toJson "o"]
  | .abbrev => .arr #[toJson "a"]
  | .regular h => .arr #[toJson "r", toJson h.toNat]

private def decodeReducibilityHints (j : Json) : IO ReducibilityHints := do
  let .arr elems := j
    | throw <| IO.userError "malformed proof export reducibility hints"
  let some tag := elems[0]?.bind (fun x => x.getStr?.toOption)
    | throw <| IO.userError "missing proof export reducibility hint tag"
  match tag with
  | "o" =>
    unless elems.size == 1 do
      throw <| IO.userError "malformed opaque reducibility hint"
    return .opaque
  | "a" =>
    unless elems.size == 1 do
      throw <| IO.userError "malformed abbrev reducibility hint"
    return .abbrev
  | "r" =>
    unless elems.size == 2 do
      throw <| IO.userError "malformed regular reducibility hint"
    let h ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
    unless h < UInt32.size do
      throw <| IO.userError "regular reducibility hint out of UInt32 range"
    return .regular (UInt32.ofNat h)
  | _ => throw <| IO.userError s!"unknown proof export reducibility hint {tag}"

/-- Intern an `Expr` into pure structural JSON.

`Expr.mdata` annotations are transparent to the Lean kernel and are stripped
here so the structural wire format never needs to carry elaborator `Syntax`
payloads. -/
private unsafe def internExportExpr (ref : IO.Ref ProofExportPool)
    (e : Expr) : IO Nat := do
  if let some idx ← ref.modifyGet fun st => (st.exprIds.find? e, st) then
    return idx
  if let .mdata _ body := e then
    let bodyId ← internExportExpr ref body
    ref.modify fun st => { st with exprIds := st.exprIds.insert e bodyId }
    return bodyId
  let encoded : Json ← match e with
    | .bvar idx =>
      pure (.arr #[toJson "b", toJson (toString idx)])
    | .fvar fv =>
      let nid ← internExportName ref fv.name
      pure (.arr #[toJson "f", toJson nid])
    | .mvar mv =>
      let nid ← internExportName ref mv.name
      pure (.arr #[toJson "m", toJson nid])
    | .sort lvl =>
      let lid ← internExportLevel ref lvl
      pure (.arr #[toJson "s", toJson lid])
    | .const n lvls =>
      let nid ← internExportName ref n
      let lids ← lvls.toArray.mapM (internExportLevel ref)
      pure (.arr #[toJson "c", toJson nid, toJson lids])
    | .app f a =>
      let fid ← internExportExpr ref f
      let aid ← internExportExpr ref a
      pure (.arr #[toJson "a", toJson fid, toJson aid])
    | .lam n t b bi =>
      let nid ← internExportName ref n
      let tid ← internExportExpr ref t
      let bid ← internExportExpr ref b
      pure (.arr #[toJson "l", toJson nid, toJson tid, toJson bid,
        toJson (binderInfoCode bi)])
    | .forallE n t b bi =>
      let nid ← internExportName ref n
      let tid ← internExportExpr ref t
      let bid ← internExportExpr ref b
      pure (.arr #[toJson "p", toJson nid, toJson tid, toJson bid,
        toJson (binderInfoCode bi)])
    | .letE n t v b nondep =>
      let nid ← internExportName ref n
      let tid ← internExportExpr ref t
      let vid ← internExportExpr ref v
      let bid ← internExportExpr ref b
      pure (.arr #[toJson "e", toJson nid, toJson tid, toJson vid, toJson bid,
        toJson nondep])
    | .lit (.natVal n) =>
      pure (.arr #[toJson "ln", toJson (toString n)])
    | .lit (.strVal s) =>
      pure (.arr #[toJson "ls", toJson s])
    | .proj s i body =>
      let sid ← internExportName ref s
      let bid ← internExportExpr ref body
      pure (.arr #[toJson "j", toJson sid, toJson (toString i), toJson bid])
    | .mdata _ _ => unreachable!
  ref.modifyGet fun st =>
    let idx := st.exprs.size
    (idx, { st with
      exprIds := st.exprIds.insert e idx
      exprs := st.exprs.push encoded })

private unsafe def encodeExportConstantInfo (ref : IO.Ref ProofExportPool)
    (ci : ConstantInfo) : IO Json := do
  let nid ← internExportName ref ci.name
  let lpIds ← ci.levelParams.toArray.mapM (internExportName ref)
  let tid ← internExportExpr ref ci.type
  match ci with
  | .axiomInfo v =>
    return .arr #[toJson "axiom", toJson nid, toJson lpIds, toJson tid,
      toJson v.isUnsafe]
  | .defnInfo v =>
    let vid ← internExportExpr ref v.value
    let allIds ← v.all.toArray.mapM (internExportName ref)
    return .arr #[toJson "defn", toJson nid, toJson lpIds, toJson tid,
      toJson vid, encodeReducibilityHints v.hints,
      toJson (safetyCode v.safety), toJson allIds]
  | .thmInfo v =>
    let vid ← internExportExpr ref v.value
    let allIds ← v.all.toArray.mapM (internExportName ref)
    return .arr #[toJson "thm", toJson nid, toJson lpIds, toJson tid,
      toJson vid, toJson allIds]
  | .opaqueInfo v =>
    let vid ← internExportExpr ref v.value
    let allIds ← v.all.toArray.mapM (internExportName ref)
    return .arr #[toJson "opaque", toJson nid, toJson lpIds, toJson tid,
      toJson vid, toJson v.isUnsafe, toJson allIds]
  | .quotInfo v =>
    return .arr #[toJson "quot", toJson nid, toJson lpIds, toJson tid,
      toJson (quotKindCode v.kind)]
  | .inductInfo v =>
    let allIds ← v.all.toArray.mapM (internExportName ref)
    let ctorIds ← v.ctors.toArray.mapM (internExportName ref)
    return .arr #[toJson "induct", toJson nid, toJson lpIds, toJson tid,
      toJson v.numParams, toJson v.numIndices, toJson allIds, toJson ctorIds,
      toJson v.numNested, toJson v.isRec, toJson v.isUnsafe,
      toJson v.isReflexive]
  | .ctorInfo v =>
    let indId ← internExportName ref v.induct
    return .arr #[toJson "ctor", toJson nid, toJson lpIds, toJson tid,
      toJson indId, toJson v.cidx, toJson v.numParams, toJson v.numFields,
      toJson v.isUnsafe]
  | .recInfo v =>
    let allIds ← v.all.toArray.mapM (internExportName ref)
    let rulesJson ← v.rules.toArray.mapM fun r => do
      let cid ← internExportName ref r.ctor
      let rid ← internExportExpr ref r.rhs
      return Json.arr #[toJson cid, toJson r.nfields, toJson rid]
    return .arr #[toJson "rec", toJson nid, toJson lpIds, toJson tid,
      toJson allIds, toJson v.numParams, toJson v.numIndices,
      toJson v.numMotives, toJson v.numMinors, .arr rulesJson,
      toJson v.k, toJson v.isUnsafe]

private unsafe def exportProofModulesImpl (env : Environment)
    (proofMods : NameSet) : IO Json := do
  let poolRef ← IO.mkRef ({} : ProofExportPool)
  let mut modObjs : Array Json := #[]
  let mut implByIds : Array Nat := #[]
  let mut externIds : Array Nat := #[]
  let mut csimpIds : Array Nat := #[]
  for modIdx in Array.range env.header.modules.size do
    let m := env.header.modules[modIdx]!
    let data := env.header.moduleData[modIdx]!
    if proofMods.contains m.module then
      validateConstantsCachedMetadata data.constants
      let constNameIds ← data.constNames.mapM (internExportName poolRef)
      let constantsJson ← data.constants.mapM (encodeExportConstantInfo poolRef)
      modObjs := modObjs.push <| Json.mkObj [
        ("module", toJson m.module),
        ("isModule", toJson data.isModule),
        ("imports", toJson data.imports),
        ("constNames", toJson constNameIds),
        ("constants", .arr constantsJson)]
      for (declName, _) in
          Compiler.implementedByAttr.ext.getModuleEntries env modIdx do
        implByIds := implByIds.push (← internExportName poolRef declName)
      for (declName, _) in externAttr.ext.getModuleEntries env modIdx do
        externIds := externIds.push (← internExportName poolRef declName)
      for entry in Compiler.CSimp.ext.ext.getModuleEntries env modIdx do
        let e := match entry with
          | .global e | .scoped _ e => e
        csimpIds := csimpIds.push (← internExportName poolRef e.fromDeclName)
  let pool ← poolRef.get
  return Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("names", .arr pool.names),
    ("levels", .arr pool.levels),
    ("exprs", .arr pool.exprs),
    ("modules", .arr modObjs),
    ("compilerOverrides", Json.mkObj [
      ("implementedBy", toJson implByIds),
      ("extern", toJson externIds),
      ("csimp", toJson csimpIds)])]

@[implemented_by exportProofModulesImpl]
private def exportProofModules (_env : Environment)
    (_proofMods : NameSet) : IO Json :=
  throw <| IO.userError "proof exporter requires runtime implementation"

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

/-- Execute `"target-export"` in a dedicated sandboxed child process with zero
write access to `"target-audit"`'s verdict output.

Imports target `.olean` artifacts at `trustLevel := 0` (`loadExts := false`),
validates cached metadata words on every proof constant, and emits a pure
structural DAG JSON representation of all `TargetRole::Proof` modules. -/
def targetExport (j : Json) (foundation : Array Name) : IO Json := do
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let arts ← artifacts j
  let mut roles : Std.HashMap Name TargetOrigin := {}
  for m in foundation do roles := roles.insert m .foundation
  for m in libraries do
    roles ← insertRole roles m .library "overlapping target module"
  let mut roots := foundation ++ libraries
  let mut proofMods : NameSet := {}
  let mut expectedIsMod : Std.HashMap Name Bool := {}
  for item in modules do
    let m := (← field (α := String) item "module").toName
    let rawRole ← field (α := String) item "role"
    let some role := TargetRole.parse? rawRole
      | fail s!"unknown target role {rawRole}"
    let expectedIsModule ← field (α := Bool) item "isModule"
    roles ← insertRole roles m (.source role) "overlapping target module"
    expectedIsMod := expectedIsMod.insert m expectedIsModule
    let some art := arts.find? m
      | fail s!"missing target artifacts for {m}"
    validateTargetArtifactPreImport m art expectedIsModule
    if role == .proof then
      proofMods := proofMods.insert m
    roots := roots.push m
  let env ← importEnv j roots
  -- When a caller bypasses header admission and relabels a dependency of a
  -- non-`Proof` module as `TargetRole::Proof`, report the exact declaration
  -- authority violation (or import authority violation if unused) as a policy
  -- error before `"target-audit"` excludes `Proof` `.olean`s from its import
  -- set. `"target-audit"` independently re-checks the admitted graph so it
  -- never relies on `"target-export"` for authority enforcement.
  let expProvenance n := constProvenance env roles n "target module"
  for m in env.header.modules, data in env.header.moduleData do
    if let some (.source srcRole) := roles.get? m.module then
      let some expected := expectedIsMod.get? m.module
        | fail s!"missing expected isModule for {m.module}"
      validateTargetModuleIsModuleConsistency m.module data.isModule expected
      let some art := arts.find? m.module
        | fail s!"missing target artifacts for {m.module}"
      validateTargetArtifactParts m.module (art.oleanParts true).size
        art.irParts.isEmpty data.isModule
      if srcRole != .proof then
        let importsProof := data.imports.any fun imp =>
          roles.get? imp.module == some (.source .proof)
        if importsProof then
          for ci in data.constants do
            let deps ← declarationEdges ci
            for dep in deps do
              let (_, depRole) ← expProvenance dep
              if let some msg :=
                  TargetOrigin.edgeViolation? ci.name (.source srcRole) dep depRole then
                fail msg
          for imp in data.imports do
            if roles.get? imp.module == some (.source .proof) then
              fail s!"target authority violation {m.module} imports {imp.module}"
  exportProofModules env proofMods

private structure ExportedProofModule where
  moduleName : Name
  isModule : Bool
  imports : Array Import
  constNames : Array Name
  constants : Array ConstantInfo

private structure ProofCompilerOverrides where
  implementedBy : NameSet := {}
  externDecls : NameSet := {}
  csimp : NameSet := {}

private structure DecodedProofExport where
  modules : Array ExportedProofModule
  overrides : ProofCompilerOverrides

private def parseNatString (s : String) (label : String) : IO Nat := do
  let some n := s.toNat?
    | throw <| IO.userError s!"invalid decimal Nat in proof export ({label}): {s}"
  return n

private def lookupPool (pool : Array α) (idx : Nat) (label : String) : IO α := do
  let some v := pool[idx]?
    | throw <| IO.userError
        s!"out-of-bounds proof export {label} index {idx} (pool size {pool.size})"
  return v

/-- Parse and reconstruct all proof-module declarations from the pure
structural JSON stream emitted by `"target-export"`.

Every `Name`, `Level`, and `Expr` is built sequentially via normal safe Lean
constructors (so every cached `Name.hash`, `Level.data`, and `Expr.data` word
is computed fresh inside `"target-audit"`). Strict index bounds (`idx < pool.size`
during sequential construction) prevent cycles and malformed references. -/
private def decodeProofExport (raw : Json) : IO DecodedProofExport := do
  let schemaVersion ← field (α := Nat) raw "schemaVersion"
  unless schemaVersion == 1 do
    throw <| IO.userError s!"unsupported proof export schemaVersion {schemaVersion}"
  let namesJson ← field (α := Array Json) raw "names"
  let mut namePool : Array Name := Array.mkEmpty namesJson.size
  for entry in namesJson do
    let .arr elems := entry
      | throw <| IO.userError "malformed name entry in proof export"
    let some tag := elems[0]?.bind (fun x => x.getStr?.toOption)
      | throw <| IO.userError "missing name tag in proof export"
    let decoded : Name ← match tag with
      | "a" =>
        unless elems.size == 1 do
          throw <| IO.userError "malformed anonymous name in proof export"
        pure .anonymous
      | "s" =>
        unless elems.size == 3 do
          throw <| IO.userError "malformed string name in proof export"
        let preId ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let seg ← IO.ofExcept (fromJson? (α := String) elems[2]!)
        let pre ← lookupPool namePool preId "name"
        pure (.str pre seg)
      | "n" =>
        unless elems.size == 3 do
          throw <| IO.userError "malformed numeric name in proof export"
        let preId ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let numStr ← IO.ofExcept (fromJson? (α := String) elems[2]!)
        let pre ← lookupPool namePool preId "name"
        let v ← parseNatString numStr "name"
        pure (.num pre v)
      | _ => throw <| IO.userError s!"unknown name tag {tag} in proof export"
    namePool := namePool.push decoded
  let levelsJson ← field (α := Array Json) raw "levels"
  let mut levelPool : Array Level := Array.mkEmpty levelsJson.size
  for entry in levelsJson do
    let .arr elems := entry
      | throw <| IO.userError "malformed level entry in proof export"
    let some tag := elems[0]?.bind (fun x => x.getStr?.toOption)
      | throw <| IO.userError "missing level tag in proof export"
    let decoded : Level ← match tag with
      | "z" =>
        unless elems.size == 1 do
          throw <| IO.userError "malformed zero level in proof export"
        pure .zero
      | "s" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed succ level in proof export"
        let uid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        pure (.succ (← lookupPool levelPool uid "level"))
      | "m" =>
        unless elems.size == 3 do
          throw <| IO.userError "malformed max level in proof export"
        let uid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let vid ← IO.ofExcept (fromJson? (α := Nat) elems[2]!)
        pure (.max (← lookupPool levelPool uid "level")
          (← lookupPool levelPool vid "level"))
      | "i" =>
        unless elems.size == 3 do
          throw <| IO.userError "malformed imax level in proof export"
        let uid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let vid ← IO.ofExcept (fromJson? (α := Nat) elems[2]!)
        pure (.imax (← lookupPool levelPool uid "level")
          (← lookupPool levelPool vid "level"))
      | "p" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed param level in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        pure (.param (← lookupPool namePool nid "name"))
      | "v" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed mvar level in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        pure (.mvar ⟨← lookupPool namePool nid "name"⟩)
      | _ => throw <| IO.userError s!"unknown level tag {tag} in proof export"
    levelPool := levelPool.push decoded
  let exprsJson ← field (α := Array Json) raw "exprs"
  let mut exprPool : Array Expr := Array.mkEmpty exprsJson.size
  for entry in exprsJson do
    let .arr elems := entry
      | throw <| IO.userError "malformed expr entry in proof export"
    let some tag := elems[0]?.bind (fun x => x.getStr?.toOption)
      | throw <| IO.userError "missing expr tag in proof export"
    let decoded : Expr ← match tag with
      | "b" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed bvar expr in proof export"
        let idxStr ← IO.ofExcept (fromJson? (α := String) elems[1]!)
        pure (.bvar (← parseNatString idxStr "bvar"))
      | "f" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed fvar expr in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        pure (.fvar ⟨← lookupPool namePool nid "name"⟩)
      | "m" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed mvar expr in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        pure (.mvar ⟨← lookupPool namePool nid "name"⟩)
      | "s" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed sort expr in proof export"
        let lid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        pure (.sort (← lookupPool levelPool lid "level"))
      | "c" =>
        unless elems.size == 3 do
          throw <| IO.userError "malformed const expr in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let lids ← IO.ofExcept (fromJson? (α := Array Nat) elems[2]!)
        let lvls ← lids.toList.mapM (lookupPool levelPool · "level")
        pure (.const (← lookupPool namePool nid "name") lvls)
      | "a" =>
        unless elems.size == 3 do
          throw <| IO.userError "malformed app expr in proof export"
        let fid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let aid ← IO.ofExcept (fromJson? (α := Nat) elems[2]!)
        pure (.app (← lookupPool exprPool fid "expr")
          (← lookupPool exprPool aid "expr"))
      | "l" =>
        unless elems.size == 5 do
          throw <| IO.userError "malformed lam expr in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let tid ← IO.ofExcept (fromJson? (α := Nat) elems[2]!)
        let bid ← IO.ofExcept (fromJson? (α := Nat) elems[3]!)
        let biCode ← IO.ofExcept (fromJson? (α := Nat) elems[4]!)
        let some bi := binderInfoOfCode? biCode
          | throw <| IO.userError s!"invalid binder info code {biCode}"
        pure (.lam (← lookupPool namePool nid "name")
          (← lookupPool exprPool tid "expr")
          (← lookupPool exprPool bid "expr") bi)
      | "p" =>
        unless elems.size == 5 do
          throw <| IO.userError "malformed forallE expr in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let tid ← IO.ofExcept (fromJson? (α := Nat) elems[2]!)
        let bid ← IO.ofExcept (fromJson? (α := Nat) elems[3]!)
        let biCode ← IO.ofExcept (fromJson? (α := Nat) elems[4]!)
        let some bi := binderInfoOfCode? biCode
          | throw <| IO.userError s!"invalid binder info code {biCode}"
        pure (.forallE (← lookupPool namePool nid "name")
          (← lookupPool exprPool tid "expr")
          (← lookupPool exprPool bid "expr") bi)
      | "e" =>
        unless elems.size == 6 do
          throw <| IO.userError "malformed letE expr in proof export"
        let nid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let tid ← IO.ofExcept (fromJson? (α := Nat) elems[2]!)
        let vid ← IO.ofExcept (fromJson? (α := Nat) elems[3]!)
        let bid ← IO.ofExcept (fromJson? (α := Nat) elems[4]!)
        let nondep ← IO.ofExcept (fromJson? (α := Bool) elems[5]!)
        pure (.letE (← lookupPool namePool nid "name")
          (← lookupPool exprPool tid "expr")
          (← lookupPool exprPool vid "expr")
          (← lookupPool exprPool bid "expr") nondep)
      | "ln" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed nat lit expr in proof export"
        let s ← IO.ofExcept (fromJson? (α := String) elems[1]!)
        pure (.lit (.natVal (← parseNatString s "natLit")))
      | "ls" =>
        unless elems.size == 2 do
          throw <| IO.userError "malformed str lit expr in proof export"
        let s ← IO.ofExcept (fromJson? (α := String) elems[1]!)
        pure (.lit (.strVal s))
      | "j" =>
        unless elems.size == 4 do
          throw <| IO.userError "malformed proj expr in proof export"
        let sid ← IO.ofExcept (fromJson? (α := Nat) elems[1]!)
        let idxStr ← IO.ofExcept (fromJson? (α := String) elems[2]!)
        let bid ← IO.ofExcept (fromJson? (α := Nat) elems[3]!)
        pure (.proj (← lookupPool namePool sid "name")
          (← parseNatString idxStr "proj")
          (← lookupPool exprPool bid "expr"))
      | _ => throw <| IO.userError s!"unknown expr tag {tag} in proof export"
    exprPool := exprPool.push decoded
  let decodeNameList (j : Json) : IO (List Name) := do
    let ids ← IO.ofExcept (fromJson? (α := Array Nat) j)
    ids.toList.mapM (lookupPool namePool · "name")
  let decodeConstant (j : Json) : IO ConstantInfo := do
    let .arr elems := j
      | throw <| IO.userError "malformed constant entry in proof export"
    let some tag := elems[0]?.bind (fun x => x.getStr?.toOption)
      | throw <| IO.userError "missing constant tag in proof export"
    if elems.size < 4 then
      throw <| IO.userError s!"truncated constant entry {tag} in proof export"
    let name ← lookupPool namePool (← IO.ofExcept (fromJson? (α := Nat) elems[1]!)) "name"
    let levelParams ← decodeNameList elems[2]!
    let type ← lookupPool exprPool (← IO.ofExcept (fromJson? (α := Nat) elems[3]!)) "expr"
    match tag with
    | "axiom" =>
      unless elems.size == 5 do
        throw <| IO.userError "malformed axiom entry in proof export"
      let isUnsafe ← IO.ofExcept (fromJson? (α := Bool) elems[4]!)
      return .axiomInfo { name, levelParams, type, isUnsafe }
    | "defn" =>
      unless elems.size == 8 do
        throw <| IO.userError "malformed defn entry in proof export"
      let value ← lookupPool exprPool (← IO.ofExcept (fromJson? (α := Nat) elems[4]!)) "expr"
      let hints ← decodeReducibilityHints elems[5]!
      let sCode ← IO.ofExcept (fromJson? (α := Nat) elems[6]!)
      let some safety := safetyOfCode? sCode
        | throw <| IO.userError s!"invalid safety code {sCode} in proof export"
      let all ← decodeNameList elems[7]!
      return .defnInfo { name, levelParams, type, value, hints, safety, all }
    | "thm" =>
      unless elems.size == 6 do
        throw <| IO.userError "malformed thm entry in proof export"
      let value ← lookupPool exprPool (← IO.ofExcept (fromJson? (α := Nat) elems[4]!)) "expr"
      let all ← decodeNameList elems[5]!
      return .thmInfo { name, levelParams, type, value, all }
    | "opaque" =>
      unless elems.size == 7 do
        throw <| IO.userError "malformed opaque entry in proof export"
      let value ← lookupPool exprPool (← IO.ofExcept (fromJson? (α := Nat) elems[4]!)) "expr"
      let isUnsafe ← IO.ofExcept (fromJson? (α := Bool) elems[5]!)
      let all ← decodeNameList elems[6]!
      return .opaqueInfo { name, levelParams, type, value, isUnsafe, all }
    | "quot" =>
      unless elems.size == 5 do
        throw <| IO.userError "malformed quot entry in proof export"
      let qCode ← IO.ofExcept (fromJson? (α := Nat) elems[4]!)
      let some kind := quotKindOfCode? qCode
        | throw <| IO.userError s!"invalid quot kind code {qCode} in proof export"
      return .quotInfo { name, levelParams, type, kind }
    | "induct" =>
      unless elems.size == 12 do
        throw <| IO.userError "malformed induct entry in proof export"
      let numParams ← IO.ofExcept (fromJson? (α := Nat) elems[4]!)
      let numIndices ← IO.ofExcept (fromJson? (α := Nat) elems[5]!)
      let all ← decodeNameList elems[6]!
      let ctors ← decodeNameList elems[7]!
      let numNested ← IO.ofExcept (fromJson? (α := Nat) elems[8]!)
      let isRec ← IO.ofExcept (fromJson? (α := Bool) elems[9]!)
      let isUnsafe ← IO.ofExcept (fromJson? (α := Bool) elems[10]!)
      let isReflexive ← IO.ofExcept (fromJson? (α := Bool) elems[11]!)
      return .inductInfo {
        name, levelParams, type, numParams, numIndices, all, ctors,
        numNested, isRec, isUnsafe, isReflexive }
    | "ctor" =>
      unless elems.size == 9 do
        throw <| IO.userError "malformed ctor entry in proof export"
      let induct ← lookupPool namePool (← IO.ofExcept (fromJson? (α := Nat) elems[4]!)) "name"
      let cidx ← IO.ofExcept (fromJson? (α := Nat) elems[5]!)
      let numParams ← IO.ofExcept (fromJson? (α := Nat) elems[6]!)
      let numFields ← IO.ofExcept (fromJson? (α := Nat) elems[7]!)
      let isUnsafe ← IO.ofExcept (fromJson? (α := Bool) elems[8]!)
      return .ctorInfo {
        name, levelParams, type, induct, cidx, numParams, numFields, isUnsafe }
    | "rec" =>
      unless elems.size == 12 do
        throw <| IO.userError "malformed rec entry in proof export"
      let all ← decodeNameList elems[4]!
      let numParams ← IO.ofExcept (fromJson? (α := Nat) elems[5]!)
      let numIndices ← IO.ofExcept (fromJson? (α := Nat) elems[6]!)
      let numMotives ← IO.ofExcept (fromJson? (α := Nat) elems[7]!)
      let numMinors ← IO.ofExcept (fromJson? (α := Nat) elems[8]!)
      let rulesJson ← IO.ofExcept (fromJson? (α := Array Json) elems[9]!)
      let rules ← rulesJson.toList.mapM fun rj => do
        let .arr rElems := rj
          | throw <| IO.userError "malformed recursor rule in proof export"
        unless rElems.size == 3 do
          throw <| IO.userError "malformed recursor rule arity in proof export"
        let ctor ← lookupPool namePool (← IO.ofExcept (fromJson? (α := Nat) rElems[0]!)) "name"
        let nfields ← IO.ofExcept (fromJson? (α := Nat) rElems[1]!)
        let rhs ← lookupPool exprPool (← IO.ofExcept (fromJson? (α := Nat) rElems[2]!)) "expr"
        return ({ ctor, nfields, rhs } : RecursorRule)
      let k ← IO.ofExcept (fromJson? (α := Bool) elems[10]!)
      let isUnsafe ← IO.ofExcept (fromJson? (α := Bool) elems[11]!)
      return .recInfo {
        name, levelParams, type, all, numParams, numIndices, numMotives,
        numMinors, rules, k, isUnsafe }
    | _ => throw <| IO.userError s!"unknown constant tag {tag} in proof export"
  let modsJson ← field (α := Array Json) raw "modules"
  let mut decodedMods : Array ExportedProofModule := #[]
  for mj in modsJson do
    let modName := (← field (α := String) mj "module").toName
    let isModule ← field (α := Bool) mj "isModule"
    let imports ← field (α := Array Import) mj "imports"
    let constNameIds ← field (α := Array Nat) mj "constNames"
    let constNames ← constNameIds.mapM (lookupPool namePool · "name")
    let constantsJson ← field (α := Array Json) mj "constants"
    let constants ← constantsJson.mapM decodeConstant
    decodedMods := decodedMods.push {
      moduleName := modName, isModule, imports, constNames, constants }
  let ovObj ← field (α := Json) raw "compilerOverrides"
  let decodeNameSet (key : String) : IO NameSet := do
    let ids ← field (α := Array Nat) ovObj key
    let mut s : NameSet := {}
    for id in ids do
      s := s.insert (← lookupPool namePool id "name")
    return s
  let overrides : ProofCompilerOverrides := {
    implementedBy := ← decodeNameSet "implementedBy"
    externDecls := ← decodeNameSet "extern"
    csimp := ← decodeNameSet "csimp" }
  return { modules := decodedMods, overrides }

/-! ## Anti-Vacuity Specification Linting (Advisory Quality Warnings)

These helpers detect common accidental specification mistakes (`Specs.safety`
reducing to `False`, `Specs.property` reducing to `True`, non-trivial
`Specs.property` ignoring its `Program` argument, and unused user-named
bindings in `TargetRole::Specification` definitions) and surface them via
`"specWarnings"` without blocking verification or weakening kernel checks.
Per `THREAT_MODEL.md` section 2.2, these warnings are quality aids for authors,
not security defenses against adversarial specifications. -/

/-- Single advisory anti-vacuity specification warning emitted by
`"target-audit"`. -/
structure SpecLintWarning where
  code : String
  declaration : String
  message : String
  body : Option String := none
  deriving BEq

/-- Canonical sort/dedup key for deterministic warning output. -/
def SpecLintWarning.sortKey (w : SpecLintWarning) : String :=
  w.code ++ "\x00" ++ w.declaration ++ "\x00" ++
    w.body.getD "" ++ "\x00" ++ w.message

/-- Serialize a [`SpecLintWarning`] in camelCase wire format for
`"specWarnings"`. -/
def SpecLintWarning.toJson (w : SpecLintWarning) : Json :=
  let base := [
    ("code", Json.str w.code),
    ("declaration", Json.str w.declaration),
    ("message", Json.str w.message)
  ]
  let fields := match w.body with
    | some b => base ++ [("body", Json.str b)]
    | none => base
  Json.mkObj fields

/-- Run `Kernel.whnf`, preserving `e` intact if kernel reduction raises an
exception on an out-of-fuel or unreduced subexpression. -/
def kernelWhnfSafe (env : Environment) (lctx : LocalContext)
    (e : Expr) : Expr :=
  match Kernel.whnf env lctx e with
  | .ok r => r
  | .error _ => e

/-- Recover concrete `Nat` literals (bounded recursion). -/
partial def extractNatLit? (env : Environment) (lctx : LocalContext)
    (e : Expr) (fuel : Nat := 32) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .lit (.natVal n) => some n
    | .mdata _ b => extractNatLit? env lctx b fuel
    | .const ``Nat.zero _ => some 0
    | .app (.const ``Nat.succ _) k =>
      (extractNatLit? env lctx k fuel).map (· + 1)
    | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.constName? == some ``OfNat.ofNat && args.size == 3 then
        extractNatLit? env lctx args[1]! fuel
      else
        match e with
        | .const n lvls =>
          match env.checked.get.find? n with
          | some ci =>
            if ci.levelParams.length == lvls.length then
              match ci.value? true with
              | some v =>
                extractNatLit? env lctx
                  (v.instantiateLevelParams ci.levelParams lvls) fuel
              | none => none
            else
              none
          | none => none
        | _ =>
          let e' := kernelWhnfSafe env lctx e
          if e' == e then none else extractNatLit? env lctx e' fuel

/-- Recover a `String` from a Lean `List Char` expression (such as the list
passed to `String.ofList` by `anneal-rustc-capture`), supporting balanced
`++` list concatenation and `Char.ofNat` elements. -/
def extractCharListString? (env : Environment) (lctx : LocalContext)
    (listExpr : Expr) (maxChars : Nat := 512) : Option String := Id.run do
  let mut cur := listExpr
  let mut chars : Array Char := #[]
  for _ in [0:maxChars] do
    cur := kernelWhnfSafe env lctx cur
    let fn := cur.getAppFn
    let args := cur.getAppArgs
    if fn.constName? == some ``List.nil && args.size == 1 then
      return some (String.ofList chars.toList)
    if fn.constName? == some ``List.cons && args.size == 3 then
      let head := args[1]!
      let codeOpt :=
        if head.getAppFn.constName? == some ``Char.ofNat &&
            head.getAppArgs.size == 1 then
          extractNatLit? env lctx head.getAppArgs[0]!
        else
          extractNatLit? env lctx (mkApp (mkConst ``Char.toNat) head)
      let some code := codeOpt | return none
      chars := chars.push (Char.ofNat code)
      cur := args[2]!
    else
      return none
  return none

/-- Unfold `.const` definitions shallowly and reduce via `Kernel.whnf` to
recover concrete `String` literals, `String.ofList [...]` terms, or
`Trusted.MirAst.stringAppend a b` trees (which `anneal-rustc-capture` emits
for identities longer than 16 characters) before calling `Kernel.whnf` on
compound terms. -/
partial def extractStringLit? (env : Environment) (lctx : LocalContext)
    (e : Expr) (fuel : Nat := 16) : Option String :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .lit (.strVal s) => some s
    | .mdata _ b => extractStringLit? env lctx b fuel
    | .const n lvls =>
      match env.checked.get.find? n with
      | some ci =>
        if ci.levelParams.length == lvls.length then
          match ci.value? true with
          | some v =>
            extractStringLit? env lctx
              (v.instantiateLevelParams ci.levelParams lvls) fuel
          | none => none
        else
          none
      | none => none
    | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.constName? == some ``String.ofList && args.size == 1 then
        extractCharListString? env lctx args[0]!
      else if fn.constName? == some `Trusted.MirAst.stringAppend &&
          args.size == 2 then
        match extractStringLit? env lctx args[0]! fuel,
            extractStringLit? env lctx args[1]! fuel with
        | some a, some b => some (a ++ b)
        | _, _ => none
      else
        match kernelWhnfSafe env lctx e with
        | .lit (.strVal s) => some s
        | e' =>
          let fn' := e'.getAppFn
          let args' := e'.getAppArgs
          if fn'.constName? == some ``String.ofList && args'.size == 1 then
            extractCharListString? env lctx args'[0]!
          else if e' == e then
            none
          else
            extractStringLit? env lctx e' fuel

/-- Recover concrete `Bool` literals. -/
partial def extractBoolLit? (env : Environment) (lctx : LocalContext)
    (e : Expr) (fuel : Nat := 16) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match kernelWhnfSafe env lctx e with
    | .const ``Bool.true _ => some true
    | .const ``Bool.false _ => some false
    | e' =>
      if e' == e then none
      else extractBoolLit? env lctx e' fuel

/-- Decide whether two expressions are provably equal (`some true`) or distinct
(`some false`) via literal or inductive constructor head inspection. -/
def structurallyDisjointEq? (env : Environment) (lctx : LocalContext)
    (lhs rhs : Expr) (fuel : Nat := 8) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if let (some s1, some s2) :=
        (extractStringLit? env lctx lhs, extractStringLit? env lctx rhs) then
      some (s1 == s2)
    else if let (some n1, some n2) :=
        (extractNatLit? env lctx lhs, extractNatLit? env lctx rhs) then
      some (n1 == n2)
    else if let (some b1, some b2) :=
        (extractBoolLit? env lctx lhs, extractBoolLit? env lctx rhs) then
      some (b1 == b2)
    else
      let l := kernelWhnfSafe env lctx lhs
      let r := kernelWhnfSafe env lctx rhs
      let lFn := l.getAppFn
      let rFn := r.getAppFn
      match lFn.constName?, rFn.constName? with
      | some c1, some c2 =>
        match env.checked.get.find? c1, env.checked.get.find? c2 with
        | some (.ctorInfo i1), some (.ctorInfo i2) =>
          if i1.induct == i2.induct && c1 != c2 then
            some false
          else if c1 == c2 && c1 == ``List.cons &&
              l.getAppArgs.size == 3 && r.getAppArgs.size == 3 then
            let la := l.getAppArgs
            let ra := r.getAppArgs
            match structurallyDisjointEq? env lctx la[1]! ra[1]! fuel with
            | some false => some false
            | _ => structurallyDisjointEq? env lctx la[2]! ra[2]! fuel
          else
            none
        | _, _ => none
      | _, _ => none

/-- Return `true` when `ty` WHNF-reduces to a known inhabited ground type so
`∀ (_ : ty), False` is safely identified as unsatisfiable without confusing
negations `P → False`. -/
def isKnownInhabitedDomain (env : Environment) (lctx : LocalContext)
    (ty : Expr) : Bool :=
  let ty := kernelWhnfSafe env lctx ty
  let fn := ty.getAppFn
  match fn.constName? with
  | some n =>
    n == ``Nat || n == ``String || n == ``Bool || n == ``Unit ||
      n == ``PUnit || n == ``List || n == `Trusted.MirAst.Program ||
      n == `Trusted.MirModel.Val || n == `Trusted.MirSemantics.Query ||
      n == `Trusted.MirSemantics.CallerMemory
  | none => false

mutual

/-- Return `true` when `e` reduces syntactically/structurally (under bounded
recursion) to a trivially true proposition such as `True`, `a = a`,
`False → P`, or `P ∧ Q` with both conjuncts trivially true. -/
partial def isTrivialTrueProp (env : Environment) (lctx : LocalContext)
    (nextIdx : Nat) (fuel : Nat) (e : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let e := kernelWhnfSafe env lctx e
    if e == mkConst ``True then
      true
    else
      match e with
      | .forallE n d b _ =>
        if isTrivialFalseProp env lctx nextIdx fuel d then
          true
        else
          let fv : FVarId := { name := Name.num `_anneal_lint_v nextIdx }
          let lctx' := lctx.mkLocalDecl fv n d .default .default
          isTrivialTrueProp env lctx' (nextIdx + 1) fuel
            (b.instantiate1 (.fvar fv))
      | _ =>
        let fn := e.getAppFn
        let args := e.getAppArgs
        match fn.constName?, args.size with
        | some ``Not, 1 =>
          isTrivialFalseProp env lctx nextIdx fuel args[0]!
        | some ``And, 2 =>
          isTrivialTrueProp env lctx nextIdx fuel args[0]! &&
            isTrivialTrueProp env lctx nextIdx fuel args[1]!
        | some ``Or, 2 =>
          isTrivialTrueProp env lctx nextIdx fuel args[0]! ||
            isTrivialTrueProp env lctx nextIdx fuel args[1]!
        | some ``Iff, 2 =>
          (isTrivialTrueProp env lctx nextIdx fuel args[0]! &&
            isTrivialTrueProp env lctx nextIdx fuel args[1]!) ||
          (isTrivialFalseProp env lctx nextIdx fuel args[0]! &&
            isTrivialFalseProp env lctx nextIdx fuel args[1]!) ||
          args[0]! == args[1]!
        | some ``Eq, 3 =>
          args[1]! == args[2]! ||
            structurallyDisjointEq? env lctx args[1]! args[2]! == some true ||
            (match Kernel.isDefEq env lctx args[1]! args[2]! with
            | .ok ok => ok
            | .error _ => false)
        | some ``ite, 5 =>
          isTrivialTrueProp env lctx nextIdx fuel args[3]! &&
            isTrivialTrueProp env lctx nextIdx fuel args[4]!
        | some ``dite, 5 =>
          let fvT : FVarId := { name := Name.num `_anneal_lint_v nextIdx }
          let fvE : FVarId := { name := Name.num `_anneal_lint_v (nextIdx + 1) }
          let lctxT := lctx.mkLocalDecl fvT `h args[1]! .default .default
          let lctxE := lctx.mkLocalDecl fvE `h
            (mkApp (mkConst ``Not) args[1]!) .default .default
          isTrivialTrueProp env lctxT (nextIdx + 2) fuel
            (mkApp args[3]! (.fvar fvT)) &&
          isTrivialTrueProp env lctxE (nextIdx + 2) fuel
            (mkApp args[4]! (.fvar fvE))
        | _, _ => false

/-- Return `true` when `e` reduces syntactically/structurally (under bounded
recursion) to a trivially unsatisfiable proposition such as `False`,
`¬ True`, `∃ x, False`, `0 = 1`, or `False ∧ P`. -/
partial def isTrivialFalseProp (env : Environment) (lctx : LocalContext)
    (nextIdx : Nat) (fuel : Nat) (e : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let e := kernelWhnfSafe env lctx e
    if e == mkConst ``False then
      true
    else
      match e with
      | .forallE n d b _ =>
        if isKnownInhabitedDomain env lctx d then
          let fv : FVarId := { name := Name.num `_anneal_lint_v nextIdx }
          let lctx' := lctx.mkLocalDecl fv n d .default .default
          isTrivialFalseProp env lctx' (nextIdx + 1) fuel
            (b.instantiate1 (.fvar fv))
        else
          false
      | _ =>
        let fn := e.getAppFn
        let args := e.getAppArgs
        match fn.constName?, args.size with
        | some ``Exists, 2 =>
          let fv : FVarId := { name := Name.num `_anneal_lint_v nextIdx }
          let lctx' := lctx.mkLocalDecl fv `x args[0]! .default .default
          isTrivialFalseProp env lctx' (nextIdx + 1) fuel
            (mkApp args[1]! (.fvar fv))
        | some ``Not, 1 =>
          isTrivialTrueProp env lctx nextIdx fuel args[0]!
        | some ``And, 2 =>
          isTrivialFalseProp env lctx nextIdx fuel args[0]! ||
            isTrivialFalseProp env lctx nextIdx fuel args[1]!
        | some ``Or, 2 =>
          isTrivialFalseProp env lctx nextIdx fuel args[0]! &&
            isTrivialFalseProp env lctx nextIdx fuel args[1]!
        | some ``Iff, 2 =>
          (isTrivialTrueProp env lctx nextIdx fuel args[0]! &&
            isTrivialFalseProp env lctx nextIdx fuel args[1]!) ||
          (isTrivialFalseProp env lctx nextIdx fuel args[0]! &&
            isTrivialTrueProp env lctx nextIdx fuel args[1]!)
        | some ``Eq, 3 =>
          structurallyDisjointEq? env lctx args[1]! args[2]! == some false
        | some ``ite, 5 =>
          isTrivialFalseProp env lctx nextIdx fuel args[3]! &&
            isTrivialFalseProp env lctx nextIdx fuel args[4]!
        | some ``dite, 5 =>
          let fvT : FVarId := { name := Name.num `_anneal_lint_v nextIdx }
          let fvE : FVarId := { name := Name.num `_anneal_lint_v (nextIdx + 1) }
          let lctxT := lctx.mkLocalDecl fvT `h args[1]! .default .default
          let lctxE := lctx.mkLocalDecl fvE `h
            (mkApp (mkConst ``Not) args[1]!) .default .default
          isTrivialFalseProp env lctxT (nextIdx + 2) fuel
            (mkApp args[3]! (.fvar fvT)) &&
          isTrivialFalseProp env lctxE (nextIdx + 2) fuel
            (mkApp args[4]! (.fvar fvE))
        | _, _ => false

end

/-- Summary of a captured MIR body needed for per-function `Specs.safety`
linting without reducing `locals` or `basicBlocks`. -/
structure CapturedBodySummary where
  argumentCount : Nat
  isUnsafe : Bool
  identityExpr : Expr
  identityText : Option String
  deriving Inhabited

/-- Unfold `List Body` from `Trusted.MirAst.Program` up to `maxBodies`, failing
closed if a `Trusted.MirAst.Program` value does not reduce to an 8-argument
`Trusted.MirAst.Program.mk` application. -/
def extractCapturedBodies (env : Environment) (subjectName : Name)
    (maxBodies : Nat := 256) : IO (Array CapturedBodySummary) := do
  let some subjectInfo := env.checked.get.find? subjectName | return #[]
  let progTy := mkConst `Trusted.MirAst.Program
  let isMirProg := match Kernel.isDefEq env {} subjectInfo.type progTy with
    | .ok b => b
    | .error _ => false
  if !isMirProg then
    return #[]
  let progExpr := kernelWhnfSafe env {} (mkConst subjectName)
  let progFn := progExpr.getAppFn
  let progArgs := progExpr.getAppArgs
  if progFn.constName? != some `Trusted.MirAst.Program.mk then
    fail s!"unexpected Program constructor in {subjectName}: {progFn}"
  if progArgs.size != 8 then
    fail s!"unexpected Program arity in {subjectName}: expected 8, got {progArgs.size}"
  let mut cur := progArgs[0]!
  let mut out : Array CapturedBodySummary := #[]
  for _ in [0:maxBodies] do
    cur := kernelWhnfSafe env {} cur
    let fn := cur.getAppFn
    let args := cur.getAppArgs
    if fn.constName? == some ``List.cons && args.size == 3 then
      let bodyExpr := kernelWhnfSafe env {} args[1]!
      let bFn := bodyExpr.getAppFn
      let bArgs := bodyExpr.getAppArgs
      if bFn.constName? == some `Trusted.MirAst.Body.mk &&
          bArgs.size == 5 then
        let argCount := (extractNatLit? env {} bArgs[0]!).getD 0
        let isUnsafe := (extractBoolLit? env {} bArgs[3]!).getD false
        let identityExpr := bArgs[4]!
        let identityText := extractStringLit? env {} identityExpr
        out := out.push {
          argumentCount := argCount
          isUnsafe, identityExpr, identityText }
      cur := args[2]!
    else
      break
  return out

/-- Build a Lean list expression `[e_0, ..., e_{n-1}]` of element type `elemTy`.
-/
def mkListExpr (elemTy : Expr) (elems : List Expr) : Expr :=
  elems.foldr
    (fun head tail =>
      mkApp3 (mkConst ``List.cons [Level.zero]) elemTy head tail)
    (mkApp (mkConst ``List.nil [Level.zero]) elemTy)

/-- Return `true` when `n` is an author-written variable name rather than a
wildcard, anonymous arrow domain, instance binder, or macro-hygiene name. -/
def isUserNamedBinder (n : Name) (bi : BinderInfo) : Bool :=
  !bi.isInstImplicit &&
  !n.isAnonymous &&
  !n.hasMacroScopes &&
  match n with
  | .str .anonymous s => !s.startsWith "_" && !s.endsWith "✝" && s != "this"
  | _ => false

/-- Return `true` when `ci` is a compiler-generated definition (projection,
aux recursor, matcher, splitter, noConfusion, ctorIdx, etc.) rather than an
author-written specification definition. -/
def isCompilerGeneratedSpecDef (env : Environment)
    (ci : ConstantInfo) : Bool :=
  let userName := privateToUserName ci.name
  let generatedSuffix := match userName with
    | .str _ suffix =>
      let suffixes := [
        "noConfusionType", "ctorIdx", "toCtorIdx", "splitter", "inj", "injEq"
      ]
      suffixes.contains suffix
    | _ => false
  generatedSuffix || userName.isInternalDetail ||
    isAuxRecursor env ci.name || isNoConfusion env ci.name ||
    env.isProjectionFn ci.name

/-- Collect user-named bindings (in `.lam`, `.forallE`, `.letE`) whose loose
bound variable index `0` never occurs in the body expression. -/
partial def collectUnusedBindersExpr : Expr → Array String
  | .lam n d b bi =>
    let here := if isUserNamedBinder n bi && !b.hasLooseBVar 0
      then #[n.toString] else #[]
    here ++ collectUnusedBindersExpr d ++ collectUnusedBindersExpr b
  | .forallE n d b bi =>
    let here := if isUserNamedBinder n bi && !b.hasLooseBVar 0
      then #[n.toString] else #[]
    here ++ collectUnusedBindersExpr d ++ collectUnusedBindersExpr b
  | .letE n t v b _ =>
    let here := if isUserNamedBinder n .default && !b.hasLooseBVar 0
      then #[n.toString] else #[]
    here ++ collectUnusedBindersExpr t ++ collectUnusedBindersExpr v ++
      collectUnusedBindersExpr b
  | .app f a => collectUnusedBindersExpr f ++ collectUnusedBindersExpr a
  | .mdata _ b => collectUnusedBindersExpr b
  | .proj _ _ b => collectUnusedBindersExpr b
  | _ => #[]

/-- Deduplicate strings preserving first-seen order. -/
def dedupStrings (xs : Array String) : Array String :=
  xs.foldl (init := #[]) fun acc s =>
    if acc.contains s then acc else acc.push s

/-- Extracted field constants and domain types for checking either a
`Trusted.MirSemantics.Specs` or `Trusted.MirSemantics.SpecsV2` specification.
-/
structure MirSpecShape where
  specLabel : String
  safetyField : Name
  propField : Name
  idTy : Expr
  safetyArgTy : Expr
  valTy : Expr
  callerMemTy? : Option Expr
  progTy : Expr

/-- Peel `List elemTy` element type from an expression `argsTy`. -/
def peelListElemTy? (env : Environment) (argsTy : Expr) : Option Expr :=
  let whnf := kernelWhnfSafe env {} argsTy
  match whnf.getAppFn.constName?, whnf.getAppArgs with
  | some ``List, #[elemTy] => some elemTy
  | _, _ => none

/-- Peel domain types from either `Trusted.MirSemantics.Specs` or
`Trusted.MirSemantics.SpecsV2` in `env` when `specTy` is definitionally equal
to one of them. -/
def mirSpecShape? (env : Environment) (specTy : Expr) :
    Option MirSpecShape := do
  let isType (constName : Name) : Bool :=
    match Kernel.isDefEq env {} specTy (mkConst constName) with
    | .ok b => b
    | .error _ => false
  if isType `Trusted.MirSemantics.Specs then
    let safetyInfo ← env.checked.get.find? `Trusted.MirSemantics.Specs.safety
    let .forallE _ _ (.forallE _ idTy (.forallE _ argsTy _ _) _) _ :=
      safetyInfo.type | none
    let valTy ← peelListElemTy? env argsTy
    let propInfo ← env.checked.get.find? `Trusted.MirSemantics.Specs.property
    let .forallE _ _ (.forallE _ progTy _ _) _ := propInfo.type | none
    some {
      specLabel := "Specs"
      safetyField := `Trusted.MirSemantics.Specs.safety
      propField := `Trusted.MirSemantics.Specs.property
      idTy
      safetyArgTy := argsTy
      valTy
      callerMemTy? := none
      progTy
    }
  else if isType `Trusted.MirSemantics.SpecsV2 then
    let safetyInfo ← env.checked.get.find? `Trusted.MirSemantics.SpecsV2.safety
    let .forallE _ _ (.forallE _ idTy (.forallE _ queryTy _ _) _) _ :=
      safetyInfo.type | none
    let queryMkInfo ← env.checked.get.find? `Trusted.MirSemantics.Query.mk
    let .forallE _ argsTy (.forallE _ callerMemTy _ _) _ :=
      queryMkInfo.type | none
    let valTy ← peelListElemTy? env argsTy
    let propInfo ← env.checked.get.find? `Trusted.MirSemantics.SpecsV2.property
    let .forallE _ _ (.forallE _ progTy _ _) _ := propInfo.type | none
    some {
      specLabel := "SpecsV2"
      safetyField := `Trusted.MirSemantics.SpecsV2.safety
      propField := `Trusted.MirSemantics.SpecsV2.property
      idTy
      safetyArgTy := queryTy
      valTy
      callerMemTy? := some callerMemTy
      progTy
    }
  else
    none

/-- Run advisory anti-vacuity specification linting over the replayed target
environment, returning sorted deduplicated [`SpecLintWarning`]s. -/
def inspectSpecVacuity (env : Environment) (subjectName specName : Name)
    (specAllConsts : List Name) : IO (Array SpecLintWarning) := do
  let mut warnings : Array SpecLintWarning := #[]
  let specAllSorted := specAllConsts.toArray.qsort Name.lt
  -- 1. Syntactic unused user-named bindings across author-written
  --    TargetRole::Specification definitions.
  for n in specAllSorted do
    if let some ci := env.checked.get.find? n then
      if ci matches .defnInfo _ then
        unless isCompilerGeneratedSpecDef env ci do
          if let some val := ci.value? true then
            let unused := dedupStrings (collectUnusedBindersExpr val)
            unless unused.isEmpty do
              let listStr := String.intercalate ", " unused.toList
              let declStr := (privateToUserName n).toString
              warnings := warnings.push {
                code := "unused_spec_binding"
                declaration := declStr
                message :=
                  s!"unused argument binding(s) in `{declStr}`: {listStr}"
              }
  -- 2. Semantic `Specs` / `SpecsV2` checks (skipping mock test shapes).
  let specShape? := match env.checked.get.find? specName with
    | some specInfo => mirSpecShape? env specInfo.type
    | none => none
  if let some shape := specShape? then
    let specDeclStr := (privateToUserName specName).toString
    let safetyFn := mkApp (mkConst shape.safetyField) (mkConst specName)
    let propFn := mkApp (mkConst shape.propField) (mkConst specName)
    -- 2a. Global `safety` satisfiability check with opaque `(id, query)`.
    let idFVar : FVarId := { name := `_anneal_lint_safety_id }
    let queryFVar : FVarId := { name := `_anneal_lint_safety_args }
    let lctxSafety := ({} : LocalContext)
      |>.mkLocalDecl idFVar `id shape.idTy .default .default
      |>.mkLocalDecl queryFVar `q shape.safetyArgTy .default .default
    let globalSafety := mkApp2 safetyFn (.fvar idFVar) (.fvar queryFVar)
    if isTrivialFalseProp env lctxSafety 100 16 globalSafety then
      warnings := warnings.push {
        code := "unsatisfiable_safety"
        declaration := specDeclStr
        message :=
          s!"{shape.specLabel}.safety reduces to a trivially unsatisfiable " ++
          "proposition regardless of function identity or arguments"
      }
    else
      -- 2b. Per-unsafe-body `safety` satisfiability check (catches typos
      --     or wrong argument arities on unsafe bodies).
      let bodies ← extractCapturedBodies env subjectName
      let maxCheckedArgs : Nat := 32
      for idx in [0:bodies.size] do
        if let some body := bodies[idx]? then
          if body.isUnsafe && body.argumentCount <= maxCheckedArgs then
            let mut lctxBody : LocalContext := {}
            let mut argExprs : List Expr := []
            for aIdx in [0:body.argumentCount] do
              let fv : FVarId := { name := Name.num `_anneal_lint_arg aIdx }
              lctxBody := lctxBody.mkLocalDecl fv `arg shape.valTy
                .default .default
              argExprs := argExprs ++ [.fvar fv]
            let argsListExpr := mkListExpr shape.valTy argExprs
            let (lctxQuery, safetyArgExpr) := match shape.callerMemTy? with
              | none => (lctxBody, argsListExpr)
              | some memTy =>
                let memFVar : FVarId := { name := `_anneal_lint_caller_mem }
                (lctxBody.mkLocalDecl memFVar `callerMem memTy
                  .default .default,
                 mkApp2 (mkConst `Trusted.MirSemantics.Query.mk)
                   argsListExpr (.fvar memFVar))
            let idArg := match body.identityText with
              | some s => .lit (.strVal s)
              | none => body.identityExpr
            let bodySafety := mkApp2 safetyFn idArg safetyArgExpr
            if isTrivialFalseProp env lctxQuery 100 16 bodySafety then
              let bodyLabel := body.identityText.getD s!"body#{idx}"
              warnings := warnings.push {
                code := "unsatisfiable_safety"
                declaration := specDeclStr
                body := some bodyLabel
                message :=
                  s!"{shape.specLabel}.safety reduces to a trivially " ++
                  s!"unsatisfiable proposition for unsafe body " ++
                  s!"`{bodyLabel}` ({body.argumentCount} arg(s))"
              }
    -- 2c. `property` triviality & `Program`-ignorance check.
    let progFVar : FVarId := { name := `_anneal_lint_prog }
    let lctxProp := ({} : LocalContext)
      |>.mkLocalDecl progFVar `p shape.progTy .default .default
    let propApplied := mkApp propFn (.fvar progFVar)
    let propReduced := kernelWhnfSafe env lctxProp propApplied
    if isTrivialTrueProp env lctxProp 100 16 propReduced then
      warnings := warnings.push {
        code := "trivial_property"
        declaration := specDeclStr
        message :=
          s!"{shape.specLabel}.property reduces to a trivially true " ++
          "proposition"
      }
    else if !propReduced.containsFVar progFVar then
      warnings := warnings.push {
        code := "unused_spec_binding"
        declaration := specDeclStr
        message :=
          s!"{shape.specLabel}.property ignores its `Program` argument " ++
          "(normalized body does not reference the captured program)"
      }
  -- Sort and deduplicate deterministically.
  let sorted := warnings.qsort (fun a b => a.sortKey < b.sortKey)
  return sorted.foldl (init := #[]) fun acc w =>
    if acc.contains w then acc else acc.push w

/-- Execute Phase 4 (`"target-audit"`) on compiled target artifacts.

Target auditing never opens or maps any untrusted authored `Proof` `.olean` in
the verdict-producing process: only trusted/preflighted non-proof modules
(`foundation`, `libraries`, `model`, `capture`, `specification`, `expected`)
are imported via `importEnv` (`loadExts := false`), while every `Proof` module
is reconstructed fresh from the pure structural JSON stream emitted by the
isolated `"target-export"` process. Every reached declaration then undergoes
raw-`UInt64` cached-metadata validation and fresh kernel replay onto
`foundation-lock.json`. -/
def targetAudit (j : Json) (foundation : Array Name) : IO Json := do
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let allowSorryInProof ← match target.getObjVal? "allowSorryInProof" with
    | .error _ => pure false
    | .ok val => IO.ofExcept (fromJson? (α := Bool) val)
  let proofExportPath ← field (α := String) j "proofExportPath"
  let proofExportRaw ← IO.ofExcept <| Json.parse (← IO.FS.readFile proofExportPath)
  let proofExport ← decodeProofExport proofExportRaw
  let arts ← artifacts j
  let mut roles : Std.HashMap Name TargetOrigin := {}
  for m in foundation do roles := roles.insert m .foundation
  for m in libraries do
    roles ← insertRole roles m .library "overlapping target module"
  let mut nonProofRoots := foundation ++ libraries
  let mut expectedProofMods : NameSet := {}
  let mut expectedIsMod : Std.HashMap Name Bool := {}
  for item in modules do
    let m := (← field (α := String) item "module").toName
    let rawRole ← field (α := String) item "role"
    let some role := TargetRole.parse? rawRole
      | fail s!"unknown target role {rawRole}"
    let expectedIsModule ← field (α := Bool) item "isModule"
    roles ← insertRole roles m (.source role) "overlapping target module"
    expectedIsMod := expectedIsMod.insert m expectedIsModule
    if role == .proof then
      -- Authored `Proof` `.olean`s must never be supplied to or mapped by the
      -- verdict-producing `"target-audit"` process.
      if (arts.find? m).isSome then
        throw <| IO.userError
          s!"proof module artifact {m} must not be passed to target-audit"
      expectedProofMods := expectedProofMods.insert m
    else
      -- Reject mismatched companion `.olean*` headers, invalid base-address
      -- chains, `.ir` parts, and `isModule` policy violations before
      -- `importEnv` mmaps `.olean.server` / `.olean.private`.
      let some art := arts.find? m
        | fail s!"missing target artifacts for {m}"
      validateTargetArtifactPreImport m art expectedIsModule
      nonProofRoots := nonProofRoots.push m
  -- Enforce role-graph separation against the admitted DAG before calling
  -- `importEnv` on `nonProofRoots` so a non-`Proof` module importing a
  -- `Proof` module fails closed with a policy violation rather than a missing
  -- module lookup error (and without relying on `"target-export"`).
  let expectedGraph ← field (α := Json) j "graph"
  let .obj graphObj := expectedGraph
    | throw <| IO.userError "malformed admitted graph in target-audit request"
  for (modStr, edgesJson) in graphObj.toList do
    let modName := modStr.toName
    if let some (.source srcRole) := roles.get? modName then
      if srcRole != .proof then
        let edges ← IO.ofExcept (fromJson? (α := Array Import) edgesJson)
        for imp in edges do
          if roles.get? imp.module == some (.source .proof) then
            fail s!"target authority violation {modName} imports {imp.module}"
  let env ← importEnv j nonProofRoots
  let allMatchers := collectAllMatchers env
  -- Collect all compiler overrides authored by non-proof `.source` modules
  -- directly from `finalizeImport`-populated module entries (no `loadExts`
  -- and no duplicate `foundation ++ libraries` metadata environment) together
  -- with the `Proof` overrides exported by `"target-export"`.
  let mut sourceImplementedBy := proofExport.overrides.implementedBy
  let mut sourceExternDecls := proofExport.overrides.externDecls
  let mut sourceCsimp := proofExport.overrides.csimp
  for modIdx in Array.range env.header.modules.size do
    let m := env.header.modules[modIdx]!
    if roles.get? m.module matches some (.source _) then
      for (declName, _) in
          Compiler.implementedByAttr.ext.getModuleEntries env modIdx do
        sourceImplementedBy := sourceImplementedBy.insert declName
      for (declName, _) in externAttr.ext.getModuleEntries env modIdx do
        sourceExternDecls := sourceExternDecls.insert declName
      for entry in Compiler.CSimp.ext.ext.getModuleEntries env modIdx do
        let e := match entry with
          | .global e | .scoped _ e => e
        sourceCsimp := sourceCsimp.insert e.fromDeclName
  -- Reconstruct the combined module import graph (`nonProofEnv` + exported
  -- `Proof` modules) and verify exact equality against the admitted DAG.
  let mut seenExportedProofMods : NameSet := {}
  let mut combinedGraphEntries : List (String × Json) :=
    (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)
  for pm in proofExport.modules do
    unless expectedProofMods.contains pm.moduleName do
      fail s!"foreign exported proof module {pm.moduleName}"
    if seenExportedProofMods.contains pm.moduleName then
      fail s!"duplicate exported proof module {pm.moduleName}"
    seenExportedProofMods := seenExportedProofMods.insert pm.moduleName
    combinedGraphEntries :=
      (pm.moduleName.toString, toJson pm.imports) :: combinedGraphEntries
  for m in expectedProofMods do
    unless seenExportedProofMods.contains m do
      fail s!"missing exported proof module {m}"
  let combinedGraph := Json.mkObj combinedGraphEntries
  unless combinedGraph == expectedGraph do
    fail "compiled module/import DAG differs from admitted DAG"
  let isSysrootConst := constHasRole env roles
    (fun r => r matches .foundation | .library)
  let isModelConst := constHasRole env roles
    (fun r => r matches .source .model)
  -- Cross-check non-proof source inventory and the environment's actual stored
  -- values, then incorporate reconstructed proof declarations while rejecting
  -- any shadowing or duplicate names.
  let mut sourceInventory : NameSet := {}
  let mut libraryInventories : Std.HashMap Name NameSet := {}
  let mut libraryExports : Std.HashMap Name (Array ConstantInfo) := {}
  let mut specAllConsts : List Name := []
  let mut pairedSpecUnsafeRecs : Array (Name × Name) := #[]
  let mut pendingSourceAlternates : Array (TargetRole × ConstantInfo × ConstantInfo) := #[]
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
    if let .source targetRole := role then
      if targetRole == .proof then
        fail s!"proof module {m.module} must not be imported in target-audit"
      let some expected := expectedIsMod.get? m.module
        | fail s!"missing expected isModule for {m.module}"
      validateTargetModuleIsModuleConsistency m.module data.isModule expected
      let some art := arts.find? m.module
        | fail s!"missing target artifacts for {m.module}"
      validateTargetArtifactParts m.module (art.oleanParts true).size
        art.irParts.isEmpty data.isModule
      validateTargetImports m.module.toString data.imports
        (allowModule := data.isModule)
        (allowTheoryImportAll := false)
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target inventory {m.module}"
      let mut modSeen : NameSet := {}
      for ci in data.constants do
        if modSeen.contains ci.name then
          fail s!"duplicate target declaration {ci.name}"
        modSeen := modSeen.insert ci.name
        let userRoot := (privateToUserName ci.name).getRoot
        if targetRole != .model && userRoot == `Trusted &&
            !isRealizedOrCompilerHelper env allMatchers isModelConst ci then
          fail (s!"non-model target module {m.module} cannot declare " ++
            s!"constant {ci.name} in Trusted namespace")
        if reservedKernelRoots.contains userRoot &&
            !isRealizedOrCompilerHelper env allMatchers isSysrootConst ci then
          fail (s!"target module {m.module} cannot declare constant " ++
            s!"{ci.name} in reserved kernel namespace {userRoot}")
        let actualOrig ← origin env ci.name
        let stored ← lookupConst env ci.name "target dependency"
        if actualOrig == m.module then
          if sourceInventory.contains ci.name then
            fail s!"duplicate target declaration {ci.name}"
          if !(stored.type == ci.type &&
              stored.value? true == ci.value? true &&
              kind stored == kind ci && stored.isUnsafe == ci.isUnsafe &&
              stored.isPartial == ci.isPartial &&
              stored.levelParams == ci.levelParams) then
            unless sameRealizedThmHeader stored ci do
              fail s!"stored target declaration differs {ci.name}"
            pendingSourceAlternates :=
              pendingSourceAlternates.push (targetRole, stored, ci)
          sourceInventory := sourceInventory.insert ci.name
          if targetRole == .specification then
            if let some parent ← pairedSpecUnsafeRecParent? env m.module ci then
              pairedSpecUnsafeRecs := pairedSpecUnsafeRecs.push (ci.name, parent)
            else
              specAllConsts := ci.name :: specAllConsts
        else
          unless sameRealizedThmHeader stored ci do
            fail s!"target inventory origin mismatch {ci.name}"
          pendingSourceAlternates :=
            pendingSourceAlternates.push (targetRole, stored, ci)
  let mut proofOrigins : Std.HashMap Name Name := {}
  let mut proofConsts : Std.HashMap Name ConstantInfo := {}
  for pm in proofExport.modules do
    let some expected := expectedIsMod.get? pm.moduleName
      | fail s!"missing expected isModule for {pm.moduleName}"
    validateTargetModuleIsModuleConsistency pm.moduleName pm.isModule expected
    validateTargetImports pm.moduleName.toString pm.imports
      (allowModule := pm.isModule)
      (allowTheoryImportAll := pm.isModule && isAnnealModuleName pm.moduleName)
    unless pm.constNames == pm.constants.map ConstantInfo.name do
      fail s!"invalid target inventory {pm.moduleName}"
    let mut modSeen : NameSet := {}
    for ci in pm.constants do
      if modSeen.contains ci.name then
        fail s!"duplicate target declaration {ci.name}"
      modSeen := modSeen.insert ci.name
      let userRoot := (privateToUserName ci.name).getRoot
      if userRoot == `Trusted &&
          !isRealizedOrCompilerHelper env allMatchers isModelConst ci
            (allowUnimportedProofSparse := true) then
        fail (s!"non-model target module {pm.moduleName} cannot declare " ++
          s!"constant {ci.name} in Trusted namespace")
      if reservedKernelRoots.contains userRoot &&
          !isRealizedOrCompilerHelper env allMatchers isSysrootConst ci
            (allowUnimportedProofSparse := true) then
        fail (s!"target module {pm.moduleName} cannot declare constant " ++
          s!"{ci.name} in reserved kernel namespace {userRoot}")
      if let some stored := env.checked.get.find? ci.name then
        unless sameRealizedThmHeader stored ci do
          fail s!"duplicate target declaration {ci.name}"
        pendingSourceAlternates :=
          pendingSourceAlternates.push (.proof, stored, ci)
      else if let some stored := proofConsts.get? ci.name then
        unless sameRealizedThmHeader stored ci do
          fail s!"duplicate target declaration {ci.name}"
        pendingSourceAlternates :=
          pendingSourceAlternates.push (.proof, stored, ci)
      else
        if sourceInventory.contains ci.name then
          fail s!"duplicate target declaration {ci.name}"
        sourceInventory := sourceInventory.insert ci.name
        proofOrigins := proofOrigins.insert ci.name pm.moduleName
        proofConsts := proofConsts.insert ci.name ci
  let originOf (n : Name) : IO Name := do
    if let some idx := env.getModuleIdxFor? n then
      let some modName := env.header.moduleNames[idx.toNat]?
        | throw <| IO.userError s!"module index out of range for {n}"
      return modName
    if let some modName := proofOrigins.get? n then
      return modName
    fail s!"missing origin for {n}"
  let lookup (n : Name) : IO ConstantInfo := do
    if let some ci := env.checked.get.find? n then
      return ci
    if let some ci := proofConsts.get? n then
      return ci
    fail s!"missing target dependency {n}"
  let provenance (n : Name) : IO (Name × TargetOrigin) := do
    let orig ← originOf n
    let some role := roles.get? orig
      | fail s!"foreign target module {orig}"
    return (orig, role)
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
  unless (← originOf theoremName) == theoremModule &&
      (← originOf expectedName) == expectedModule do
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
  let crateCtor : Name :=
    if canonicalRoot == `Trusted.MirSemantics.CrateTheoremV2 ||
        canonicalRoot == `Trusted.MirSemantics.UnitTheoremV2 then
      `Trusted.MirSemantics.CrateV2.mk
    else
      `Trusted.MirSemantics.Crate.mk
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
  unless canonicalRoot == `Trusted.MirSemantics.CrateTheorem ||
      canonicalRoot == `Trusted.MirSemantics.UnitTheorem ||
      canonicalRoot == `Trusted.MirSemantics.CrateTheoremV2 ||
      canonicalRoot == `Trusted.MirSemantics.UnitTheoremV2 do
    fail s!"unexpected canonical root {canonicalRoot}"
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
  -- Pre-validate alternate realizations in `.source` inventories so
  -- `.specification` alternate edges enter Phase 1 + `specQueue` (transitive
  -- ban) and every kept alternate proof's dependencies enter `phase2Roots`
  -- for kernel replay.
  let mut specAltDeps : List Name := []
  let mut phase2Roots : List Name := [theoremName]
  let mut sourceAlternateProofs : Array ConstantInfo := #[]
  for (altRole, stored, ci) in pendingSourceAlternates do
    let altDeps ← declarationEdges ci
    for dep in altDeps do
      let (depMod, depRole) ← provenance dep
      if dep == `sorryAx && depMod == `Init.Prelude then
        if !allowSorryInProof || altRole != .proof then
          fail s!"unapproved axiom {dep} from {depMod}"
      else
        if let some msg :=
            TargetOrigin.edgeViolation?
              ci.name (.source altRole) dep depRole then
          fail msg
        if altRole == .specification then
          if isLeanSyntaxConst dep || isPanicSpecConst dep then
            fail s!"specification declaration {ci.name} cannot reference {dep}"
          specAltDeps := dep :: specAltDeps
        else
          phase2Roots := dep :: phase2Roots
    let alts ← inventoryAlternates stored ci
    for idx in [:alts.size] do
      let p := alts[idx]!
      let pDeps ← declarationEdges p
      let skipSorryProof :=
        altRole == .proof && allowSorryInProof && pDeps.contains `sorryAx
      unless skipSorryProof do
        sourceAlternateProofs := sourceAlternateProofs.push p
        if idx == 0 then
          -- First entry is `stored` (matching `lookup p.name`).
          phase2Roots := p.name :: pDeps.toList ++ phase2Roots
        else
          for dep in pDeps do
            if dep == `sorryAx then
              let (depMod, _) ← provenance dep
              if depMod == `Init.Prelude then
                fail s!"unapproved axiom {dep} from {depMod}"
            phase2Roots := dep :: phase2Roots
  -- Phase 1: Claim and whole-specification closure (strict 3-axiom ceiling,
  -- zero `sorryAx`, non-opaque specs, no direct `Lean.Syntax` edges).
  let claimRoots := [
    expectedName, canonicalRoot, crateCtor, subjectName, specName]
  let phase1State ← runTargetClosurePhase lookup provenance axiomPolicy
    libraryInventories libraryExports true allowSorryInProof {}
    (claimRoots ++ specAllConsts ++ specAltDeps) {}
  let phase1Closure := phase1State.visited
  -- Narrowed transitive effect/meta/`System`/debug ban across every constant
  -- transitively reachable from any `TargetRole::Specification` declaration.
  let mut specSeen : NameSet := {}
  let mut specQueue : List Name := specAllConsts ++ specAltDeps
  while !specQueue.isEmpty do
    let n :: rest := specQueue | break
    specQueue := rest
    if specSeen.contains n then
      continue
    specSeen := specSeen.insert n
    if isForbiddenSpecTransitiveConst n then
      fail s!"specification transitively references disallowed constant {n}"
    let deps := phase1State.edgesCache.getD n {}
    for dep in deps do
      if !specSeen.contains dep then
        specQueue := dep :: specQueue
  -- Phase 2: Proof closure (`[theoremName]`), reusing memoized Phase 1 state
  -- and admitting `sorryAx` strictly on proof-only edges when requested.
  let phase2State ← runTargetClosurePhase lookup provenance axiomPolicy
    libraryInventories libraryExports false allowSorryInProof phase1Closure
    phase2Roots phase1State
  let reached := phase2State.visited
  let axioms := phase2State.axioms.toArray.qsort Name.lt
  let sorryDecls := phase2State.sorryDecls.toArray.qsort Name.lt
  let alternateProofs := phase2State.alternateProofs ++ sourceAlternateProofs
  -- Meaning surfaces follow the canonical claim's dependencies, independently
  -- of which proof helpers establish it. Those helpers still belong to reached
  -- and undergo replay, but editing them must not redefine the reviewed claim.
  let (_, expectedReached) ← closure lookup provenance axiomPolicy claimRoots
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
      if let .source targetRole := role then
        let userRoot := (privateToUserName n).getRoot
        if targetRole != .model && userRoot == `Trusted &&
            !isRealizedOrCompilerHelper env allMatchers isModelConst ci
              (allowUnimportedProofSparse := (proofConsts.get? n).isSome) then
          fail (s!"non-model target dependency {n} cannot live in " ++
            "Trusted namespace")
        if reservedKernelRoots.contains userRoot &&
            !isRealizedOrCompilerHelper env allMatchers isSysrootConst ci
              (allowUnimportedProofSparse := (proofConsts.get? n).isSome) then
          fail (s!"target dependency {n} cannot live in reserved kernel " ++
            s!"namespace {userRoot}")
        unless sourceInventory.contains n do
          fail s!"uninventoried target dependency {n}"
      -- Parsed imports are only the early authority gate. Recheck the actual
      -- type/body edges, including private and generated helpers, so the stored
      -- declarations' meanings obey the same authority boundary.
      let deps ← match phase2State.edgesCache.get? n with
        | some cached => pure cached
        | none => declarationEdges ci
      for dep in deps do
        let (_, depRole) ← provenance dep
        if let some msg := role.edgeViolation? n dep depRole then
          fail msg
      replayMap := replayMap.insert n ci
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()
  -- Final part of the 4-part `p._unsafe_rec` pairing invariant: zero
  -- references anywhere in `phase1Closure ∪ phase2Closure`, never in
  -- `replayMap`, and every paired parent `p` must be replayed.
  for (unsafeRec, parent) in pairedSpecUnsafeRecs do
    if reached.contains unsafeRec || replayMap.contains unsafeRec then
      fail (s!"paired _unsafe_rec helper {unsafeRec} cannot be " ++
        "referenced logically")
    unless replayMap.contains parent do
      fail s!"paired _unsafe_rec parent {parent} missing from replay"
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
  -- authored changes nevertheless, including any override on a logically
  -- reached declaration authored by a non-proof `.source` module (via
  -- `finalizeImport`-populated `getModuleEntries` on `env`) or by a `Proof`
  -- module (via `proofExport.overrides`), without importing a duplicate
  -- `foundation ++ libraries` metadata environment.
  for n in reached do
    if sourceImplementedBy.contains n || sourceExternDecls.contains n then
      fail s!"unchecked compiler override on logical dependency {n}"
    if sourceCsimp.contains n then
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
        ("module", toJson (← originOf n))]
  let specWarnings :=
    (← inspectSpecVacuity checkedEnv subjectName specName specAllConsts).map
      SpecLintWarning.toJson
  return Json.mkObj [("theorem", toJson theoremName),
    ("canonicalRoot", toJson canonicalRoot), ("subject", toJson subjectName),
    ("specification", toJson specName), ("graph", combinedGraph),
    ("expected", toJson expectedName), ("axioms", toJson axioms),
    ("sorryDeclarations", toJson sorryDecls),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson replayMap.size),
    ("checkedAlternateProofs", toJson alternateProofs.size),
    ("subjectClosure", .arr (← describe subjectClosure)),
    ("modelClosure", .arr (← describe modelClosure)),
    ("specificationClosure", .arr (← describe specClosure)),
    ("specWarnings", .arr specWarnings)]

/-- Dispatch a repository or target inspection request. -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  let sysrootStr ← field (α := String) j "sysroot"
  match mode with
  | "headers" =>
    initHermeticSearchPath sysrootStr
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectHeader n.toName p
    return Json.mkObj [("headers", .arr headers)]
  | "vendor-headers" =>
    initHermeticSearchPath sysrootStr
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectVendorHeader n.toName p
    return Json.mkObj [("headers", .arr headers)]
  | "spec-preflight" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    preflightSpecs j foundation
  | "resolve-imports" =>
    initHermeticSearchPath sysrootStr
    let mods ← names j "modules"
    let env ← importCorrEnv mods
    let entries := (env.header.modules.zip env.header.moduleData).qsort
      fun (m₁, _) (m₂, _) => m₁.module.toString < m₂.module.toString
    let sortedGraph := Json.mkObj <| entries.toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)
    return Json.mkObj [("graph", sortedGraph)]
  | "preflight" =>
    let foundation ← names j "foundation"
    let foundationSet : NameSet := .ofList foundation.toList
    initHermeticSearchPath sysrootStr
    let env ← importEnv j foundation true
    validateGraph j env
    let scopedNamespaces ← collectScopedExtensionNamespaces env
    let scopedPrefixes := collectScopedNamespacePrefixes scopedNamespaces
    let (baseTiers, reservedModules) ←
      inspectPreflightBaseSources j scopedNamespaces scopedPrefixes env
        foundationSet
    let sources ← field (α := Array (String × String)) j "sources"
    let inspected ←
      sources.mapM fun (n, p) =>
        inspectSource scopedNamespaces scopedPrefixes env n.toName p
    checkPreflightTierImports inspected foundationSet baseTiers reservedModules
    return Json.mkObj [
      ("headers", .arr (inspected.map InspectedSource.renderJson)),
      ("graph", graph env)]
  | "correspondence-preflight" =>
    let foundation ← names j "foundation"
    let spRaw ← field (α := Array String) j "searchPath"
    initHermeticSearchPath sysrootStr (spRaw.toList.map System.FilePath.mk)
    preflightCorrespondence j foundation
  | "audit" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let env ← importEnv j (foundation ++ trusted ++ theory)
    audit j env foundation trusted theory
  | "target-export" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    targetExport j foundation
  | "target-audit" =>
    let foundation ← names j "foundation"
    initHermeticSearchPath sysrootStr
    targetAudit j foundation
  | "correspondence-audit" =>
    let foundation ← names j "foundation"
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
    let mode := (j.getObjValAs? String "mode").toOption.getD ""
    let result ← TrustedBoundary.run j
    let payload := Json.mkObj [("ok", toJson true), ("result", result)]
    -- Use compact JSON for `"target-export"` DAG pools so large proof
    -- modules stay compact and fast across the process boundary.
    IO.FS.writeFile output <|
      if mode == "target-export" then payload.compress else payload.pretty
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
