# Lean 4 Elaboration-Time Metaprogramming & Import-Graph Isolation vs. Kernel Constant-Graph Auditing

## Summary

A Lean 4 trust auditor that inspects only the kernel constant dependency graph
(`ConstantInfo.getUsedConstantsAsSet`, wrapped as `declarationEdges` in Anneal's
`trusted/audit/TrustedBoundary.lean`) cannot detect whether an imported module
altered the elaboration of a human-reviewed specification (`Spec.lean`). In Lean
4, parsing, macro expansion, term and command elaboration, qualified-name
resolution, typeclass synthesis, structure default-field instantiation, and
pretty-printer delaboration all consult persistent environment state accumulated
from the transitive `import` closure of a module—yet their output is a kernel
`Expr` that need not reference any constant declared in the module that supplied
the rule.

Across 19 reproducible empirical probes (`support/run_taxonomy_probes.py` and
`support/taxonomy_results.json`) against pinned Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) and Anneal's `TrustedBoundary.lean`
(`2fb744d6ecb5f858677221bfd6781af2ed72c8fc`), we establish four main results:

1. **Six distinct mechanisms cross `import` boundaries with zero kernel
   constant-graph edges (`declarationEdges`) to the hijacking module**:
   - **Syntax, notations, macros, and elaborators (`A1`–`A7`)**: High-priority
     `notation`, `infix`, `macro`, and `elab` rules, as well as retroactive
     `macro_rules`, `elab_rules : term`, and `@[command_elab]` rules attached to
     existing `Init` syntax kinds (`«term_∧_»`, `Lean.Parser.Term.app`,
     `Lean.Parser.Command.declaration`), rewrite downstream `Spec.lean`
     declarations during elaboration while leaving `mentionsHijackInEdges =
     false`. Notably, `notation`, `infix`, `macro`, and `macro_rules` require
     only `Init` (`prelude` + `import Trusted`) and do not require `import
     Lean`.
   - **Retroactive typeclass, coercion, and literal priority overrides
     (`B2`–`B4`)**: While a newly declared `instance` in `Hijack` (`B1`) leaves
     its instance constant in `Spec`'s `declarationEdges`, `Lean.Meta.addInstance`
     (`Lean/Meta/Instances.lean:283-354`) and `Lean.Meta.addDefaultInstance`
     (`Lean/Meta/Instances.lean:406-426`) do **not** call
     `ensureAttrDeclIsAfter`. An imported module can therefore apply
     `attribute [instance 10000]` or `attribute [default_instance 10000]`
     retroactively to an existing `Init` or `Trusted` declaration, hijacking
     typeclass resolution, `Coe`/`CoeOut` coercions, or `OfNat` numeric literals
     in `Spec.lean` while declaring **zero constants in `Hijack.olean`**
     (`hijackConsts = []`) and leaving **zero edges to `Hijack`**.
   - **Scoped notations and zero-constant `export` aliases (`C1`–`C2`)**:
     Executing `export SomeSubNS (Safe)` inside `namespace Spec` in an imported
     module registers `(Spec.Safe, SomeSubNS.Safe)` in `Lean.aliasExtension`
     (`Lean/ResolveName.lean:60-96`). Because `ResolveName.resolveQualifiedName`
     (`Lean/ResolveName.lean:134-151`) checks enclosing namespace prefixes
     (`Spec.Safe` via `getAliases`) **before** `openDecls` (`open Trusted`), the
     imported module redirects unqualified identifiers inside `Spec.lean` while
     declaring **zero constants in `Hijack.olean`** (`hijackConsts = []`) and
     leaving **zero edges to `Hijack`**.
   - **Retroactive structure default field values (`D1`)—which bypass both
     `declarationEdges` AND `ModuleData.entries` extension diffing**: In Lean 4,
     structure field defaults are not stored in a `PersistentEnvExtension`.
     Instead, `getDefaultFnForField?` (`Lean/Structure.lean:273-319`) looks up
     `<projFn>._default` (such as `Trusted.Specs.safety._default`) by name in
     the kernel environment (`env.contains defFn`), and
     `instantiateStructDefaultValueFn?` (`Lean/Meta/Structure.lean:196-223`)
     extracts `cinfo.value!`, beta-reduces it, and **inlines the body directly
     into the structure constructor** in `Spec.lean`. Because `targetAudit` in
     `TrustedBoundary.lean` does not call `validateLocalConstant` (`Trusted`
     namespace reservation), an imported module defining
     `def Trusted.Specs.safety._default := id (fun _ => True)` injects
     `fun _ => True` into `Spec.specs` with **zero `declarationEdges` to
     `Hijack`**, **zero metaprogramming extension entries in `Hijack.olean`**,
     and default pretty-printing (`pp.structureInstances = true`) even omits the
     defaulted field (`{ property := Trusted.Valid }`).
   - **Pretty-printer delaborator spoofing (`E2`)—where `@[delab]` defeats
     `pp.all = true` and `pp.notation = false` when `loadExts := true`**: While
     `delabAppImplicitCore` (`Lean/PrettyPrinter/Delaborator/Builtins.lean:385-390`)
     skips `@[app_unexpander]` when `pp.explicit = true` or
     `pp.notation = false`, the top-level `delab` entry point
     (`Lean/PrettyPrinter/Delaborator/Basic.lean:457-458`) dispatches
     `@[delab]` handlers registered in `delabAttribute` unconditionally before
     built-in delaborators, ignoring both `pp.all = true` and
     `pp.notation = false`. Only pretty-printing in an environment loaded with
     `loadExts := false` (or dumping raw kernel `Expr` trees) prevents `@[delab]`
     from disguising `False` or `True` as `Trusted.Safe p`.
   - **Import-time code execution (`F1`)—both during target compilation and
     inside `targetAudit`**: An `initialize` / `@[init]` block in an imported
     module executes arbitrary `IO` during `lean` compilation of downstream
     modules (`Lean/Environment.lean:1990-1994`) while leaving zero edges in
     `Spec`'s constants. Furthermore, `targetAudit` in `TrustedBoundary.lean`
     (`line 1029`) invokes `importEnv j roots true` (`loadExts := true`), which
     calls `unsafe enableInitializersExecution` (`line 180`) on all target
     `roots` inside the auditor process itself.

2. **Zero-byte-modified `Spec.lean` hijack on the Starnix `apply_endianness`
   fixture (`support/run_starnix_hijack_and_defenses.py`)**:
   With `Spec.lean` **byte-for-byte unmodified** (`SHA-256`
   `6783b760927541d9990146a523b8329aaf9fcb0a3efd6b50a5ea77dcc3e3d764`), a
   single `macro_rules` declaration in `BitTheory.lean` (imported by
   `Endianness.lean`, which `Spec.lean` imports) rewrites the 4-way conjunction
   inside `Spec.specs.property` into a reflexive equality `P = P` that still
   retains `Spec.exactReversal`, `Spec.exactLittleEndian`, `Spec.involution`,
   and `Endianness.ByteReversal` in `Spec.specs`'s kernel `Expr`. A broken
   subject program (`Captured.zeroBody` / `constant_zero`, which ignores its
   arguments and always returns `0`) then passes unmodified
   `TrustedBoundary.lean` (`exit 0`, `"ok": true`) with **zero references to
   `BitTheory` in `specificationClosure`** and the **exact same
   `specificationClosure` module and declaration inventory** as the genuine
   Starnix proof—even when `BitTheory` is assigned role `"specification"` so it
   passes `target.rs`'s `TargetRole::Specification.allows` import check.

3. **Defense-in-depth synthesis**:
   None of the three candidate architectural defenses is sufficient in isolation
   if `Spec.lean` is permitted to import unreviewed helper modules, because:
   - Import-role checks (`Defense 1a`) allow `specification -> specification`
     edges if shared helper/theory modules are placed in the `specification`
     role.
   - Extension diffing on `ModuleData.entries` (`Defense 2`) catches `A1`–`A7`,
     `B2`–`B4`, `C1`–`C2`, `E1`–`E2`, and `F1`, but is bypassed by `D1`
     (`_default` structure field hooks, which use no `PersistentEnvExtension`)
     and `C3` (enclosing-namespace constant shadowing).
   - Kernel-level canonical statement printing (`Defense 3`) exposes every
     hijack in the audit output **only** if executed under `loadExts := false`
     (because `E2` `@[delab]` spoofs `pp.all = true` + `pp.notation = false`
     when `loadExts := true`), and remains a human-review aid rather than an
     automated rejection gate.
   Combining **strict `SpecDefs` import and pure-syntax isolation** (`Defense 1`:
   `checkRoleImports` on `data.imports`, `validateLocalConstant` + `._default`
   suffix ban in `targetAudit`, and running `TrustedBoundary.lean`'s existing
   pure-syntax `preflight` allowlist on `specification` modules) with
   **`ModuleData.entries` extension rejection** (`Defense 2`) and
   **`loadExts := false` canonical `Expr` printing/hashing** (`Defense 3`)
   closes every vector in the taxonomy automatically and surfaces an
   unforgeable kernel-level specification transcript for human review.

## Applicability

These findings apply to:

- **`leanprover/lean4` `v4.34.1`** at commit
  `5045d0056413266e57c625dcd7c365b10e377c52`, specifically:
  - Parser, macro, and elaborator registration and dispatch in
    `src/Lean/Elab/Notation.lean`, `src/Lean/Elab/Syntax.lean`,
    `src/Lean/Elab/MacroRules.lean`, `src/Lean/Elab/ElabRules.lean`,
    `src/Lean/Elab/Command.lean`, and `src/Lean/KeyedDeclsAttribute.lean`.
  - Scoped attributes, `instance` / `default_instance` registration, and absence
    of `ensureAttrDeclIsAfter` in `src/Lean/ScopedEnvExtension.lean` and
    `src/Lean/Meta/Instances.lean`.
  - Qualified-name resolution and `export` alias priority in
    `src/Lean/ResolveName.lean` and per-file `Command.Scope` isolation in
    `src/Lean/Elab/Command/Scope.lean`.
  - Structure default-field lookup (`<projFn>._default`) and body inlining in
    `src/Lean/Structure.lean`, `src/Lean/Meta/Structure.lean`, and
    `src/Lean/Elab/StructInst.lean`.
  - Delaborator vs. app-unexpander option gating in
    `src/Lean/PrettyPrinter/Delaborator/Basic.lean` and
    `src/Lean/PrettyPrinter/Delaborator/Builtins.lean`.
  - `.olean` module-header import and extension deserialization and `[init]`
    execution in `src/Lean/Environment.lean`.
- **`joshlf/anneal`** at commit `2fb744d6ecb5f858677221bfd6781af2ed72c8fc`
  (`joshlf-mvp` branch) and `main`, specifically:
  - `trusted/audit/TrustedBoundary.lean` (`importEnv`, `preflight`, `audit`,
    `targetAudit`, `TargetRole.allows`, `declarationEdges`, and
    `validateLocalConstant`).
  - `trusted/audit/src/target.rs` (`run_target`, `Headers` vs. `Preflight`
    dispatch, `TargetRole::allows`, and `moduleIdentities` construction).
  - `trusted/cargo-anneal/src/verify.rs` and
    `trusted/cargo-anneal/tests/fixtures/starnix/`.

## Findings

### 1. Why `ConstantInfo.getUsedConstantsAsSet` (`declarationEdges`) Is Blind to Elaboration Hijacks

In `trusted/audit/TrustedBoundary.lean:642-674`, `declarationEdges` computes the
outgoing dependency edges of a compiled declaration `ci : ConstantInfo` by
calling `ci.getUsedConstantsAsSet` (plus any constants referenced in compiler
clauses). In Lean `v4.34.1` (`src/Lean/Declaration.lean`),
`ConstantInfo.getUsedConstantsAsSet` traverses only the final kernel `Expr`s
stored in `ci.type` and `ci.value? (allowOpaque := true)`.

When `lean` compiles a downstream module `Spec.lean`, however, the transition
from surface syntax in `Spec.lean` to the final kernel `Expr` stored in
`Spec.olean` passes through six elaboration and post-processing pipelines
configured by `env.header.moduleData` (`ModuleData.entries` and
`ModuleData.constants`) of every transitively imported module:

1. **Command and term parsing** (`Lean.Parser.parserExtension`).
2. **Macro expansion** (`Lean.Elab.macroAttribute`).
3. **Command and term elaboration** (`Lean.Elab.Command.commandElabAttribute`,
   `Lean.Elab.Term.termElabAttribute`).
4. **Identifier and alias resolution** (`Lean.aliasExtension` and environment
   constant-name lookup in `Lean.ResolveName.resolveQualifiedName`).
5. **Typeclass, coercion, numeric-literal, and structure default-field
   synthesis** (`Lean.Meta.instanceExtension`,
   `Lean.Meta.defaultInstanceExtension`, and `<projFn>._default` constant body
   inlining in `Lean.Meta.instantiateStructDefaultValueFn?`).
6. **Pretty-printing / delaboration** (`Lean.PrettyPrinter.Delaborator.delabAttribute`
   and `appUnexpanderAttribute`).

Whenever an imported module `Hijack` injects a rule into pipelines 1–5 that
expands or elaborates into terms built solely from `Init.*`, `Trusted.*`, or
`Spec.*` constants, `Hijack`'s rule disappears completely before the kernel
`ConstantInfo` is constructed. As a result, `Spec`'s `declarationEdges`—and
therefore `TrustedBoundary.lean`'s `specificationClosure` (`lines 972-1041`) and
`target.rs`'s `moduleIdentities` (`lines 391-444`)—contain **zero references**
to `Hijack`.

### 2. Complete Taxonomy of Cross-Import Elaboration Constructs in Lean 4.34.1

We tested 19 concrete probes across Categories A–F using
`support/run_taxonomy_probes.py` (full machine-readable output in
`support/taxonomy_results.json`). Each probe compiles a base `Trusted.lean`
module, a `Hijack.lean` module, and an unchanged downstream `Spec.lean` module,
then inspects `Hijack.olean` and `Spec.olean` under both `loadExts := false` and
`loadExts := true`.

| Probe ID | Construct in Imported `Hijack.lean` | Requires `import Lean`? | Crosses `import`? | `Hijack` Constants (`hijackConsts`) | `Hijack` Extension Entries (`ModuleData.entries`) | Appears in `Spec` `declarationEdges`? | Hijacks `Spec` Kernel `Expr` or Audit Output? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `A1_notation_high_prio` | `notation (priority := high) "Trusted.Safe" p:max => (fun _ => True) p` | No (`Init` only) | Yes | `«termTrusted.Safe_»`, `_aux_Hijack___macroRules_...` | `parserExtension` (3), `macroAttribute` (1) | **No (`false`)** | Yes (`Spec.claim` becomes `fun p => (fun x => True) p`) |
| `A2_infix_eq_override` | `infix:50 (priority := high) " = " => fun _ _ => True` | No (`Init` only) | Yes | `«term_=__1»`, `_aux_Hijack___macroRules_...` | `parserExtension` (3), `macroAttribute` (1) | **No (`false`)** | Yes (`p.code = 42` becomes `(fun x x_1 => True) p.code 42`) |
| `A3_macro_high_prio` | `macro (priority := high) "Trusted.Valid" _p:term : term => `(True)` | No (`Init` only) | Yes | `«termTrusted.Valid_»`, `_aux_Hijack___macroRules_...` | `parserExtension` (3), `macroAttribute` (1) | **No (`false`)** | Yes (`Spec.claim` becomes `fun p => True`) |
| `A4_macro_rules_retroactive_and` | `macro_rules \| `($a ∧ $b) => `(True)` on existing `Init.Notation` kind `«term_∧_»` | No (`Init` only) | Yes | `_aux_Hijack___macroRules_term_∧__1` | `macroAttribute` (1) (**0** `parserExtension` entries) | **No (`false`)** | Yes (`Trusted.Safe p ∧ Trusted.Valid p` becomes `True`) |
| `A5_syntax_and_elab` | `elab (priority := high) "Trusted.Safe" _p:arg : term => return mkConst ``True` | Yes | Yes | `«termTrusted.Safe_»`, `_aux_Hijack___elabRules_...` | `parserExtension` (3), `termElabAttribute` (1) | **No (`false`)** | Yes (`Spec.claim` becomes `fun p => True`) |
| `A6_elab_rules_term_retroactive_app` | `elab_rules (kind := Lean.Parser.Term.app) : term` intercepting `Trusted.Safe $arg` | Yes | Yes | `_aux_Hijack___elabRules_Lean_Parser_Term_app_1` | `termElabAttribute` (1) (**0** `parserExtension` entries) | **No (`false`)** | Yes (`Spec.claim` becomes `fun p => True`) |
| `A7_elab_rules_command_declaration` | `@[command_elab Lean.Parser.Command.declaration]` intercepting `def` in `namespace Spec` | Yes | Yes | `hijackDeclElab` | `commandElabAttribute` (1) | **No (`false`)** | Yes (intercepts `def claim` and elaborates `fun p => True`) |
| `B1_new_instance_high_prio` | `instance (priority := high) hijackInst : Trusted.Checkable Trusted.Program` | No (`Init` only) | Yes | `hijackInst` | `instanceExtension` (1) | **Yes (`true`)** | Control: `hijackInst` appears in `Spec`'s `declarationEdges` |
| `B2_retroactive_attr_instance_on_trusted` | `attribute [instance 10000] Trusted.trivialCheckable` on existing `Trusted` def | No (`Init` only) | Yes | **`[]` (0 constants)** | `instanceExtension` (1) | **No (`false`)** | Yes (synthesizes `Trusted.trivialCheckable` with 0 `Hijack` constants/edges) |
| `B3_retroactive_default_instance_ofnat` | `attribute [instance 10000, default_instance 10000] Trusted.zeroOfNat` | No (`Init` only) | Yes | **`[]` (0 constants)** | `instanceExtension` (1), `defaultInstanceExtension` (1) | **No (`false`)** | Yes (`42` elaborates via `Trusted.zeroOfNat 42` to `0` with 0 `Hijack` edges) |
| `B4_retroactive_coe_instance` | `attribute [instance 10000] Trusted.forgiveInput` (`Coe RawInput Program`) | No (`Init` only) | Yes | **`[]` (0 constants)** | `instanceExtension` (1) | **No (`false`)** | Yes (`Coe.coe` uses `Trusted.forgiveInput` with 0 `Hijack` edges) |
| `C1_scoped_notation_with_open` | `scoped notation (priority := high) "Safe" p:max => (fun _ => True) p` + `open Helper` | No (`Init` only) | Yes (when opened) | `Helper.termSafe_`, `Helper._aux_Hijack___macroRules_...` | `parserExtension` (3), `macroAttribute` (1) | **No (`false`)** | Yes (`Safe p` in `Spec` expands to `(fun x => True) p`) |
| `C2_export_alias_zero_constants` | `namespace Spec` + `export Trusted.TrivialStubs (Safe)` | No (`Init` only) | Yes | **`[]` (0 constants)** | `aliasExtension` (1) | **No (`false`)** | Yes (`Safe` in `Spec` resolves to `Trusted.TrivialStubs.Safe` over `open Trusted`) |
| `C3_enclosing_namespace_shadowing` | ` @[inline] def Spec.Safe (_ : Program) : Prop := True` | No (`Init` only) | Yes | `Spec.Safe` | `declRangeExt` (1) (**0** metaprogramming extensions) | **Yes (`true`)** | `Spec.Safe` shadows `open Trusted`, but `origin env `Spec.Safe == `Hijack` |
| `C4_variable_and_autoImplicit_file_scoped` | `variable (hijackVar : Nat)` + `set_option autoImplicit true` | No (`Init` only) | **No** | **`[]` (0 constants)** | None | **No (`false`)** | Control: confined to per-file `Command.Scope`; never crosses `import` |
| `D1_structure_default_field_retroactive` | `def Trusted.Specs.safety._default : Program → Prop := id (fun _ => True)` | No (`Init` only) | Yes | `Trusted.Specs.safety._default` | **0 metaprogramming extensions** (`declRangeExt`, `exportedAxiomsExt` only) | **No (`false`)** | **Yes: body `fun _ => True` is inlined into `Spec.specs` with 0 edges AND 0 extension entries!** |
| `E1_compiler_attrs_csimp_implemented_by` | `@[csimp] theorem runtimeFlag_eq_true` + `@[implemented_by runtimeFlagTrue] Trusted.runtimeFlag` | No (`Init` only) | Yes | `runtimeFlag_eq_true`, `runtimeFlagTrue` | `Compiler.CSimp.ext` (1) (`implementedByAttr` fails across modules) | **No (`false`)** | Kernel `Expr` unchanged; `TrustedBoundary.lean:1030-1039` catches on `reached` |
| `E2_delab_vs_app_unexpander_pp_spoof` | `@[app_unexpander False]` vs. `@[delab app.False]` returning `` `(Trusted.Safe p) `` | Yes | Yes | `unexpandFalse`, `delabFalse` | `delabAttribute` (1), `appUnexpanderAttribute` (1) | **No (`false`)** | **`@[delab]` spoofs `Meta.ppExpr` even with `pp.all = true` + `pp.notation = false` when `loadExts := true`!** |
| `F1_initialize_import_time_exec` | `initialize IO.FS.writeFile ...` (`@[init]`) | No (`Init` only) | Yes | `_private.Hijack.0.initFn...` | `regularInitAttr` (1) | **No (`false`)** | **Executes arbitrary `IO` during `lean` compilation of `Spec.lean` AND inside `targetAudit` (`importEnv j roots true`)!** |

#### Key Internal Mechanisms in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)

1. **Why retroactive `macro_rules`, `elab_rules`, and `@[command_elab]` preempt
   built-in Lean syntax (`A4`, `A6`, `A7`)**:
   - In `src/Lean/Elab/MacroRules.lean:55-76`, `elabMacroRulesAux` resolves an
     existing syntax kind `k` (such as `«term_∧_»` or `«term_=_»` from
     `Init.Notation`) and registers a `@[macro k]` adapter in
     `Lean.Elab.macroAttribute` without adding any entry to
     `Lean.Parser.parserExtension`.
   - In `src/Lean/KeyedDeclsAttribute.lean:177-189`, `KeyedDeclsAttribute.getValues`
     queries `ext.getState env` (imported and local `.olean` attribute entries,
     sorted by priority and reverse registration order) and **only appends
     `builtinEntries` afterward** (`let S ← IO.Initializing.get ...`). Thus any
     imported `macro_rules`, `elab_rules (kind := Lean.Parser.Term.app) : term`,
     or `@[command_elab Lean.Parser.Command.declaration]` handler runs **before**
     Lean's built-in `elabApp` or `elabDeclaration` elaborators:

     ```lean
     -- src/Lean/KeyedDeclsAttribute.lean:177-189 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
     def getValues (attr : KeyedDeclsAttribute γ) (env : Environment) (k : Name) : List γ :=
       let s := attr.ext.getState env
       let attrs := match s.table.find? k with
         | some attrs => attrs
         | none       => []
       attrs.map (·.value)
     ```

2. **Why `attribute [instance 10000]` and `attribute [default_instance 10000]`
   work retroactively across modules (`B2`–`B4`)**:
   - Whereas `@[implemented_by]` (`src/Lean/Compiler/ImplementedByAttr.lean:24-31`)
     calls `ensureAttrDeclIsAfter` to forbid modifying a declaration from an
     earlier module, `addInstance` (`src/Lean/Meta/Instances.lean:283-354`) and
     `addDefaultInstance` (`src/Lean/Meta/Instances.lean:406-426`) call
     `ScopedEnvExtension.add` (`instanceExtension.add` /
     `defaultInstanceExtension.add`) directly without checking whether the target
     declaration belongs to the current module:

     ```lean
     -- src/Lean/Meta/Instances.lean:283-295 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
     def addInstance (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
       let c ← mkInstanceKey declName
       let keys ← DiscrTree.mkPath c.type
       instanceExtension.add { keys, val := c, prio, attrKind } attrKind
     ```

   - Consequently, an imported module can elevate a dormant or low-priority
     declaration in `Init` or `Trusted` to priority `10000` while declaring
     **zero constants of its own** (`hijackConsts = []`).

3. **Why `export` inside `namespace Spec` shadows `open Trusted` with zero
   constants (`C2`)**:
   - In `src/Lean/ResolveName.lean:60-66`, `addAliasEntry` inserts `(e.name,
     e.declName)` into `aliasExtension`.
   - In `src/Lean/ResolveName.lean:134-151`, `resolveQualifiedName` walks
     enclosing namespaces from innermost (`currNamespace = `Spec`) outward,
     calling `resolveExactName env (pfx ++ id)`—which checks `getAliases env`
     (`lines 111-118`)—**before** iterating over `openDecls` (`open Trusted` at
     `lines 152-177`). Thus `namespace Spec; export Trusted.TrivialStubs (Safe)`
     in an imported module silently redirects `Safe` inside `Spec.lean` while
     declaring zero constants in `Hijack.olean`.

4. **Why `variable` and `set_option autoImplicit` never cross `import` (`C4`)**:
   - In `src/Lean/Elab/Command/Scope.lean:23-87` and
     `src/Lean/Elab/Command.lean:141-148`, `varDecls`, `varUIds`, `opts`, and
     `openDecls` live exclusively in `Command.State.scopes : List Scope`, which
     is initialized fresh (`[{ header := "" }]`) for each file and is never
     serialized to `.olean` files.

5. **Why retroactive `<projFn>._default` (`D1`) bypasses both `declarationEdges`
   AND `ModuleData.entries` extension diffing**:
   - In `src/Lean/Structure.lean:273-319`, `getDefaultFnForField?` checks
     whether the environment contains a constant named
     `projFn ++ `_default` (or `structName ++ fieldName ++ `_default`):

     ```lean
     -- src/Lean/Structure.lean:287-291 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
     | some (.fieldInfo { projFn, .. }) =>
       let defFn := mkDefaultFnOfProjFn projFn
       if env.contains defFn then some defFn else none
     ```

   - In `src/Lean/Meta/Structure.lean:196-223`, when `Spec.lean` omits a field
     in `{ property := Trusted.Valid } : Trusted.Specs`,
     `instantiateStructDefaultValueFn?` looks up `cinfo ← getConstInfo defFn`,
     takes `cinfo.value!`, beta-reduces it, strips `id`, and returns the
     **inlined body** to `Elab.Term.StructInst` (`src/Lean/Elab/StructInst.lean:458-489`).
   - Because `cinfo.value!` is inlined directly into `Spec.specs`,
     `Trusted.Specs.safety._default` does **not** appear in `Spec.specs`'s
     `declarationEdges`. Because `getDefaultFnForField?` uses `env.contains`
     rather than a `PersistentEnvExtension`, `Hijack.olean` records **zero
     metaprogramming extension entries** in `ModuleData.entries`. And because
     `validateLocalConstant` (`TrustedBoundary.lean:727`, which forbids
     non-`Trusted` modules from declaring constants in the `Trusted` namespace)
     is called **only in repository `"audit"` mode (`line 822`) and NOT in
     `"target-audit"` (`targetAudit`, `lines 889-1052`)**, a target module can
     freely define `Trusted.Specs.safety._default`!

6. **Why `@[delab]` (`E2`) defeats `pp.all = true` and `pp.notation = false`
   when `loadExts := true`**:
   - In `src/Lean/PrettyPrinter/Delaborator/Builtins.lean:385-390`,
     `delabAppImplicitCore` guards `@[app_unexpander]` behind
     `unless (← getPPOption getPPExplicit) || !(← getPPOption getPPNotation)`.
   - By contrast, in `src/Lean/PrettyPrinter/Delaborator/Basic.lean:457-458`,
     the top-level `delab` function dispatches `delabFor k` (which queries
     `delabAttribute` in the environment) **unconditionally** before built-in
     delaborators, without checking `pp.all`, `pp.explicit`, or `pp.notation`:

     ```lean
     -- src/Lean/PrettyPrinter/Delaborator/Basic.lean:457-458 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
     def delab : Delab := do
       checkSystem "delab"
       let k ← getExprKind
       (delabFor k <|> liftM (m := MetaM) ( throwError "cannot delaborate" ))
     ```

   - In Probe `E2`, `Spec.claim` is literally `fun (_p : Trusted.Program) =>
     False`. When pretty-printed with `pp.all = true` and `pp.notation = false`
     under `loadExts := true`, `@[delab app.False]` still fires and outputs
     `"fun (_p : Trusted.Program) => Trusted.Safe✝ p✝"`. Under `loadExts :=
     false`, `delabAttribute` has no imported entries and `Meta.ppExpr`
     faithfully outputs `"fun (_p : Trusted.Program) => False"`.

### 3. End-to-End Zero-Byte-Modified `Spec.lean` Hijack on Starnix (`apply_endianness`)

In `trusted/cargo-anneal/tests/fixtures/starnix/proof/Spec.lean`, the
human-reviewed specification imports `Trusted.Mvp` and `Endianness`:

```lean
-- trusted/cargo-anneal/tests/fixtures/starnix/proof/Spec.lean (SHA-256: 6783b760...e3d764)
prelude
import Trusted.Mvp
import Endianness
...
def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program =>
      ∃ body,
        program.bodies = [body] ∧
          exactReversal body ∧
            exactLittleEndian body ∧
              involution body }
```

To test Question 2 empirically (`support/run_starnix_hijack_and_defenses.py`),
we keep `Spec.lean` **byte-for-byte unmodified** (`SHA-256`
`6783b760927541d9990146a523b8329aaf9fcb0a3efd6b50a5ea77dcc3e3d764`) and replace
the captured Starnix program in `Captured.lean` with `zeroBody`
(`constant_zero`), a 1-statement body that ignores `flag`, `width`, and `value`
and always returns `0`.

If an imported helper module (`BitTheory.lean`, imported by `Endianness.lean`)
simply rewrote `Spec.specs.property` to `True`, a reviewer inspecting
`specificationClosure` in the audit receipt would notice that
`Spec.exactReversal`, `Spec.exactLittleEndian`, `Spec.involution`, and
`Endianness.ByteReversal` disappeared from `specificationClosure`. Instead,
`BitTheory.lean` uses a 3-line `macro_rules` on `«term_∧_»` that preserves every
specification helper constant inside a reflexive equality `P = P`:

```lean
prelude
import Trusted.Mvp

namespace BitTheory

macro_rules
  | `($lhs ∧ $er:ident $b ∧ $ele:ident $b2 ∧ $inv:ident $b3) =>
    `($lhs ∧ (($er $b ∧ $ele $b2 ∧ $inv $b3) = ($er $b ∧ $ele $b2 ∧ $inv $b3)))

end BitTheory
```

Because `($er $b ∧ $ele $b2 ∧ $inv $b3) = ($er $b ∧ $ele $b2 ∧ $inv $b3)` is
definitionally provable by `rfl` for any `body` while still referencing
`Spec.exactReversal`, `Spec.exactLittleEndian`, `Spec.involution`, and
`Endianness.ByteReversal`, running unmodified `TrustedBoundary.lean`
(`2fb744d6ecb5f858677221bfd6781af2ed72c8fc`) produces (`support/starnix_hijack_and_defenses.json`):

- **`spec_lean_zero_bytes_modified`**: `true` (`SHA-256` identical to upstream
  fixture).
- **Both role configurations pass unmodified `TrustedBoundary.lean` with
  `exit_code = 0`, `"ok": true`**:
  - **Case 2A (`BitTheory` role = `"proof"`)**: Passes `TrustedBoundary.lean`
    because `targetAudit` checks `r.allows d` only on `declarationEdges ci`
    (`lines 991-998`), never on `data.imports`.
  - **Case 2B (`BitTheory` role = `"specification"`, e.g. a shared theory/helper
    module permitted in `Spec`'s import closure)**: Passes **both** `target.rs`
    (`TargetRole::Specification.allows(TargetRole::Specification) == true` at
    `trusted/audit/src/target.rs:60, 326`) **and** `TrustedBoundary.lean`!
- **Identical `specificationClosure` and `moduleIdentities`**:
  `bit_theory_in_specification_closure` is `false`, and the non-foundation
  modules in `specificationClosure` are `["Endianness", "Spec",
  "Trusted.Mvp.Semantics", "Trusted.Mvp.Syntax"]`—identical to the genuine
  Starnix proof. Because `target.rs:392-444` populates `moduleIdentities` solely
  from `modelClosure` and `specificationClosure`, `BitTheory` is omitted from
  `moduleIdentities` as well.

### 4. Architectural Defenses: Empirical Comparison & Synthesis

We implemented and empirically tested all three candidate architectural defenses
in `support/run_starnix_hijack_and_defenses.py` and across our 19-probe
taxonomy:

| Attack Vector / Probe Class | Defense 1a: Role Check on `data.imports` (`Spec -/-> Proof/Theory`) | Defense 1b: Pure-Syntax `SpecDefs` (`preflight` + `validateLocalConstant` + `._default` ban) | Defense 2: `ModuleData.entries` Extension Diffing on `Spec` Import Closure | Defense 3: Canonical Kernel Printing (`loadExts := false`, `pp.all = true`, `pp.notation = false`, raw `Expr`) |
| :--- | :--- | :--- | :--- | :--- |
| `Spec -> Proof` import with `notation`/`macro_rules` (`Case 2A`, `TrojanProof`) | **Blocks (`exit 1`)** | **Blocks (`exit 1`)** | **Blocks (`exit 1`)** | **Exposes in audit log** |
| Shared helper module in `specification` role with `notation`/`macro`/`elab`/`macro_rules` (`Case 2B`, `A1`–`A7`, `C1`) | Bypassed (if helper has `specification` role) | **Blocks (`exit 1`)** (`allowedCommandKinds` forbids `notation`, `macro`, `macro_rules`, `elab`, `syntax`) | **Blocks (`exit 1`)** (`parserExtension`, `macroAttribute`, `termElabAttribute`, `commandElabAttribute`) | **Exposes in audit log** |
| Retroactive `attribute [instance 10000]` / `[default_instance 10000]` in `specification` helper (`B2`–`B4`) | Bypassed (if helper has `specification` role) | **Blocks (`exit 1`)** (if `attribute` is restricted or `instance` priority attributes are rejected in `SpecDefs`) | **Blocks (`exit 1`)** (`instanceExtension`, `defaultInstanceExtension`) | **Exposes in audit log** (`@OfNat.ofNat ... (Trusted.zeroOfNat 42)`) |
| Zero-constant `export` alias in `specification` helper (`C2`) | Bypassed (if helper has `specification` role) | **Blocks (`exit 1`)** (if `export` is excluded in `SpecDefs` or checked) | **Blocks (`exit 1`)** (`Lean.aliasExtension`) | **Exposes in audit log** (`Trusted.TrivialStubs.Safe`) |
| Cross-module namespace shadowing (`def Spec.Safe` in helper `Hijack`, `C3`) | Bypassed (if helper has `specification` role) | **Blocks (`exit 1`)** (enforcing module-prefix namespace ownership on `SpecDefs`) | **Bypassed** (uses 0 metaprogramming extensions!) | **Exposes in audit log** (and `Hijack` appears in `specificationClosure`) |
| Retroactive structure field default (`def Trusted.Specs.safety._default`, `D1`) | Bypassed (if helper has `specification` role) | **Blocks (`exit 1`)** (`validateLocalConstant` + `hasDefaultFieldSuffix` ban) | **Bypassed** (`getDefaultFnForField?` uses `env.contains`, 0 extension entries!) | **Exposes in audit log** (`Trusted.Specs.mk (fun x => True) ...`) |
| `@[delab]` pretty-printer spoofing (`E2`) | Blocked if in `Proof`; bypassed if in `Spec` | **Blocks (`exit 1`)** (`@[delab]` forbidden in `SpecDefs`) | **Blocks (`exit 1`)** (`delabAttribute`) | **Defeated if `loadExts := true`; unforgeable if `loadExts := false`!** |
| Import-time `initialize` / `@[init]` IO execution (`F1`) | **Fires during `lean` compilation before `targetAudit` runs!** (And fires inside `targetAudit` at `line 1029` `importEnv j roots true`) | **Blocks (`exit 1`)** when `preflight` runs **before** `compile_lean_module` and `targetAudit` removes `importEnv j roots true` | **Blocks after compilation** (`regularInitAttr` / `builtinInitAttr`), too late for compile-time IO | Does not prevent IO execution |

#### Architectural Synthesis (Defense-in-Depth)

1. **Defense 1 (Strict `Spec` Import & Role Isolation + Pure-Syntax `SpecDefs`
   Separation)**:
   - **Separate `SpecDefs` from `TheoryProofs`**: Never assign general proof or
     lemma libraries (`Theory`) a role that `specification` may import. If
     `Spec.lean` needs shared pure definitions (such as `Endianness.ByteReversal`),
     place only those pure definitions in a `specification`-role module
     (`EndiannessDefs.lean`) and place all lemmas/proofs in a `proof`-role
     module (`EndiannessLemmas.lean`) that imports `EndiannessDefs.lean`.
   - **Enforce `r.allows d` on `data.imports` inside `TrustedBoundary.lean`'s
     `targetAudit`**: Closes the standalone inspector gap (`Case 2A`, rejected
     with `"policy:target import authority violation Endianness (specification)
     imports BitTheory (proof)"`).
   - **Run `preflight` (closed syntax allowlist) on all `specification`-role
     modules before compilation, and enforce `validateLocalConstant` +
     `hasDefaultFieldSuffix` in `targetAudit`**: Running `inspectSource`
     (`preflight`) on `specification` modules before `compile_lean_module`
     blocks `notation`, `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`,
     `initialize`, and `#eval` before `lean` ever elaborates them, while
     enforcing `validateLocalConstant` (`Trusted` namespace reservation) and
     rejecting `_default` / `_inherited_default` / `_autoParam` constant
     suffixes in `targetAudit` closes `D1`.
   - **Eliminate `importEnv j roots true` (`loadExts := true`) in
     `targetAudit` (`TrustedBoundary.lean:1029`)**: Instead of calling
     `importEnv j roots true` (which calls `unsafe enableInitializersExecution`
     on untrusted `Proof` `.olean` files inside the auditor), inspect
     `Compiler.implementedByAttr`, `externAttr`, and `Compiler.CSimp.ext`
     directly from the raw `ModuleData.entries` array already loaded under
     `loadExts := false` (just as `TrustedBoundary.lean:679-684` already does in
     `hasCompilerReplacementEntries` for repository `"audit"` mode!).

2. **Defense 2 (Environment Extension Diffing on `ModuleData.entries`)**:
   - In `targetAudit`, for every module `m` in the transitive `import` closure
     of `specification` (not merely `specificationClosure`), inspect
     `data.entries` and reject any module with non-empty entries in
     `forbiddenSpecExtensions` (`Lean.Parser.parserExtension`,
     `Lean.Elab.macroAttribute`, `Lean.Elab.Term.termElabAttribute`,
     `Lean.Elab.Command.commandElabAttribute`, `Lean.Meta.instanceExtension`,
     `Lean.Meta.defaultInstanceExtension`, `Lean.aliasExtension`,
     `Lean.PrettyPrinter.Delaborator.delabAttribute`,
     `Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute`,
     `Lean.Compiler.ImplementedBy.implementedByAttr`, `Lean.externAttr`,
     `Lean.Compiler.CSimp.ext`, `Lean.regularInitAttr`, and
     `Lean.builtinInitAttr`).
   - In `Case 2B` (`support/starnix_hijack_and_defenses.json`), where `BitTheory`
     is given role `"specification"`, Defense 2 immediately rejects the target
     with `"policy:forbidden environment extension Lean.Elab.macroAttribute (1
     entries) in specification module BitTheory"`.

3. **Defense 3 (Kernel-Level Canonical Statement Printing Under
   `loadExts := false`)**:
   - In `targetAudit`, format `specInfo.value? true` (and `theoremInfo.type`)
     using `Meta.ppExpr` on the `loadExts := false` `Environment` with
     `pp.all = true` and `pp.notation = false`, alongside `toString specVal`
     (raw kernel `Expr` constructor tree) and its SHA-256 digest.
   - Because `env` is loaded with `loadExts := false`, custom `@[delab]` and
     `@[app_unexpander]` extensions are absent from `env` (`Probe E2`), and
     every macro, notation, coercion, instance, alias, or inlined structure
     default is rendered in fully explicit kernel form (`support/starnix_hijack_and_defenses.json`).

## Boundaries

- **Intact-host assumption during `Proof.lean` compilation**: In `joshlf-mvp`,
  `Proof.lean` is compiled by invoking the `lean` compiler subprocess before
  `targetAudit` inspects the resulting `.olean` artifacts. If `Proof.lean` is
  permitted arbitrary syntax without running `preflight`, `Proof.lean` can still
  execute `IO` during its own compilation (`#eval`, `initialize`, `elab`). That
  compilation-time effect surface is orthogonal to `Spec.lean` semantic
  integrity and is governed by the intact-host assumption or OS sandbox around
  `lean` compilation (see sibling report
  `untrusted-proof-dependencies-effect-isolation-and-guarantee-verification`).
- **Scope of `ModuleData.entries` inspection**: `ModuleData.entries` records
  only `PersistentEnvExtension` entries (`Array (Name × Array EnvExtensionEntry)`).
  Any elaboration mechanism keyed by plain constant names in
  `ModuleData.constants`—specifically structure field defaults (`<projFn>._default`,
  `<projFn>._inherited_default`, `<projFn>._autoParam` in
  `src/Lean/Structure.lean:273-319`) and enclosing-namespace constant shadowing
  (`C3`)—does not populate `ModuleData.entries` and must be gated via
  `ModuleData.constants` checks (`validateLocalConstant`, `hasDefaultFieldSuffix`,
  and module-namespace prefix enforcement).

## Evidence

- **Primary Upstream Sources**:
  - `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):
    - `src/Lean/Elab/Notation.lean:135-162`, `src/Lean/Elab/Syntax.lean:398-452`,
      `src/Lean/Elab/MacroRules.lean:55-76`, `src/Lean/Elab/ElabRules.lean:20-112`
      (expansion of `notation`, `infix`, `macro`, `macro_rules`, `elab`, and
      `elab_rules` into `parserExtension`, `macroAttribute`,
      `termElabAttribute`, and `commandElabAttribute`).
    - `src/Lean/KeyedDeclsAttribute.lean:177-189` (`getValues` dispatching
      imported `.olean` attribute entries ahead of `builtinEntries`).
    - `src/Lean/Meta/Instances.lean:283-354, 406-426` (`addInstance` and
      `addDefaultInstance` omitting `ensureAttrDeclIsAfter`).
    - `src/Lean/ResolveName.lean:60-96, 111-177` (`aliasExtension` lookup inside
      enclosing namespaces taking precedence over `openDecls`).
    - `src/Lean/Elab/Command/Scope.lean:23-87` and
      `src/Lean/Elab/Command.lean:141-148` (per-file `Scope` isolation of
      `variable` and `autoImplicit`).
    - `src/Lean/Structure.lean:273-319`, `src/Lean/Meta/Structure.lean:196-223`,
      and `src/Lean/Elab/StructInst.lean:458-489` (`<projFn>._default` lookup by
      constant name and body inlining during structure instance elaboration).
    - `src/Lean/PrettyPrinter/Delaborator/Basic.lean:457-458` vs.
      `src/Lean/PrettyPrinter/Delaborator/Builtins.lean:385-390` (`@[delab]`
      ignoring `pp.all` / `pp.notation` vs. `@[app_unexpander]` respecting
      them).
    - `src/Lean/Environment.lean:1969-1996` (`finalizePersistentExtensions` and
      `runInitAttrs` executing `[init]` initializers when `loadExts := true`).
  - `joshlf/anneal` (`2fb744d6ecb5f858677221bfd6781af2ed72c8fc`):
    - `trusted/audit/TrustedBoundary.lean:177-194, 642-732, 873-1052`
      (`importEnv`, `declarationEdges`, `hasCompilerReplacementEntries`,
      `validateLocalConstant`, `TargetRole.allows`, and `targetAudit`).
    - `trusted/audit/src/target.rs:58-64, 293-454` (`TargetRole::allows`,
      `Headers`-only preflight on target modules, and `moduleIdentities`
      filtering by `modelClosure` / `specificationClosure`).
- **Reproducible Probe Suites & Artifacts in `support/`**:
  - `support/run_taxonomy_probes.py` and `support/taxonomy_results.json`:
    19 self-contained Lean `v4.34.1` probes (`A1`–`A7`, `B1`–`B4`, `C1`–`C4`,
    `D1`, `E1`–`E2`, `F1`) measuring `hijackConsts`, `hijackExtEntries`,
    `mentionsHijackInEdges`, `ppExtsDefault`, `ppExtsStrict_ppAll_noNotation`,
    `ppNoExtsStrict_ppAll_noNotation`, `targetRawExpr`, and
    `spec_compile_triggered_io`.
  - `support/run_starnix_hijack_and_defenses.py` and
    `support/starnix_hijack_and_defenses.json`: end-to-end Starnix
    `apply_endianness` zero-byte-modified `Spec.lean` hijack verifying broken
    `Captured.zeroBody` (`constant_zero`) against unmodified
    `TrustedBoundary.lean` (`2fb744d6ecb5`) in both `BitTheory = proof` (`2A`)
    and `BitTheory = specification` (`2B`) role configurations, followed by
    automated rejection receipts under Defense 1a, Defense 1b, and Defense 2
    and canonical statement printing receipts under Defense 3.

## Revalidation

Revalidate this report when:

1. Anneal upgrades its pinned Lean toolchain in `trusted/lean/lean-toolchain`
   and `trusted/lean/foundation-lock.json` beyond `leanprover/lean4:v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`), or Lean changes
   `KeyedDeclsAttribute`, `addInstance`, `ResolveName`, `getDefaultFnForField?`,
   or `Delaborator.delab`.
2. `trusted/audit/TrustedBoundary.lean` or `trusted/audit/src/target.rs` is
   updated to modify `TargetRole.allows`, `targetAudit`, `preflight`, or
   `importEnv`.

To rerun both empirical probe suites:

```bash
python3 reports/lean-elaboration-metaprogramming-import-isolation-and-kernel-audit/support/run_taxonomy_probes.py
python3 reports/lean-elaboration-metaprogramming-import-isolation-and-kernel-audit/support/run_starnix_hijack_and_defenses.py
```
