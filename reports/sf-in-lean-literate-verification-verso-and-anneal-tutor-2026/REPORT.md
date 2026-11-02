<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Literate Verification in `sf-in-lean`, Multi-Variant Extraction, Elaboration-Based Drift Checking, and Anneal Tutor Architecture

## Summary

`plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257`) implements a
two-tier literate verification architecture on Lean 4 (`v4.34.0`/`v4.34.1`):
`SFLMeta/` extends `Verso`, `SubVerso`, and `Illuminate` to elaborate instructor
solutions at build time while recording syntax byte ranges to extract four
standalone `.lean` variants (`student`, `solutions`, `terse`, `grading`), and
`SFLCompat/` provides standalone command elaborators (`sf_recall`,
`sf_recall_source`, `sf_experiment`, `sf_expect_failure_in`) that verify
restated declarations and roll back exploratory commands without depending on
`Verso`.

Direct source analysis and mechanized execution in Lean `v4.34.1` establish
five primary technical results:

1. **Multi-variant extraction (`SFLMeta/`):** `solution!`, `workinclass!`, and
   `suggested! default sol` elaborate the instructor solution inside the Lean
   kernel (after typechecking `default` inside `withoutModifyingState`) and
   record byte spans in `SolutionRangeExt` and `SolutionBlockExt`. At extraction
   time, `SFLMeta/Save/SourceRewrite.lean` sorts non-overlapping byte spans in
   descending (right-to-left) byte order to splice `sorry`, starter defaults, or
   `-- FILL IN HERE` without invalidating earlier offsets.
2. **Semantic declaration drift checking (`sf_recall`) and five matcher/module
   edge cases:** `sf_recall` (`SFLCompat/Recall/Check.lean`) elaborates a
   restated declaration inside a fresh hidden namespace (`_uniq.N`), rewrites
   self-references via prefix replacement (`renameBackName`), compares types,
   `def` values, inductive parameters/indices/constructors, structure field
   names, and `class` `outParam` metadata via `Meta.isDefEq`, and rolls back the
   environment (`setEnv envBefore`). However, prefix replacement in
   `renameBackName` and `Meta.whnfCore`'s refusal to unfold neutral matcher
   applications create five failure modes on pattern-matching definitions—most
   notably a cross-module crash where `Lean.Meta.Match.matcherExt` (a
   non-persistent `EnvExtension` with `asyncMode := .local`) is empty after
   importing an `.olean` module in which `laterIsNil` reused
   `earlierIsNil.match_1`, causing `sf_recall` on a byte-for-byte identical
   definition of `laterIsNil` to rewrite `_uniq.N.laterIsNil.match_1` to the
   non-existent `<Mod>.laterIsNil.match_1`. Restricting `defnInfo` renaming to
   exact constant equality (`n == chk`, `renameExact`) and unfolding matcher
   applications (`unfoldMatchersIn`) when `Meta.isDefEq` initially returns
   `false` (`sf_recall_fixed`) resolves four of the five failure modes (all
   except Lean 4.34's `_sparseCasesOn_1` wildcard encoding on $\ge 4$
   constructors, which is only propositionally equal on neutral variables).
3. **In-file state rollback (`sf_experiment`, `sf_expect_failure_in`),
   `Elab.async`, and `NameGenerator` (`ngen`) `FVarId` collisions:**
   `SFLCompat/Experiment.lean` uses a custom indentation-sensitive raw token
   parser (`rawCommandBlock`) so inner parse errors can be caught at elaboration
   time, and disables `Elab.async` (`commandWithoutAsync`) because `Elab.async =
   true` defers `theorem` proof elaboration into background `snapshotTasks`
   (leaving synchronous `messages.hasErrors == false` immediately after
   `elabCommand`). However, `withRestoringState` (`Experiment.lean:29-38`)
   preserves `infoState.trees` while resetting `Command.State.ngen` and
   `nextMacroScope` to `savedState`. Consequently, the declaration immediately
   following `sf_experiment` reuses the same `NameGenerator` counter and assigns
   identical `FVarId`s (`_uniq.N`) to its local binders, colliding in
   `SubVerso`'s `VarTypeKey.fvar` hover table. Preserving `ngen := state.ngen`
   and `nextMacroScope := state.nextMacroScope` eliminates the collision.
4. **Live declaration drift caught in Anneal Tutor (`6b7c210c`):** Auditing all
   89 fenced code blocks across `docs/tutor/*.md` on Anneal Tutor commit
   `6b7c210c6c70f2f1710424dd07b4829742ff9154` ("Port six-chapter Anneal Tutor
   to coinductive ITree and Std foundations") showed that while all 73 blocks
   managed by `<!-- tutor: ... -->` directives pass `tutor_workflow.py`, **6 of
   the 10 unmanaged Lean fenced blocks** quoting `trusted/lean/` and
   `theory/Anneal/` silently drifted and still quote deleted or superseded
   pre-`ITree`, pre-`Std` definitions and theorems (`MirNoUB.holds`,
   `ReachesPrefix`, `Preorder.refines`, `dischargeSafeRustBoundedU8`,
   `runMirStatefulBounded`). Applying `sf_recall` catches all 6 drifted blocks
   while accepting valid pedagogical reformulations (such as named structure
   fields `{ defined := safetyPre q, val := fun _ _ => True }` vs. anonymous
   constructor `⟨safetyPre q, fun _ _ => True⟩` in `Language.WellFormedOn`) that
   textual matching (`sf_recall_source` or `mode=check`) rejects.
5. **`TrustedBoundary.lean` compatibility and `tutor_workflow.py` integration:**
   `TrustedBoundary.inspectSource` (`trusted/audit/TrustedBoundary.lean:36-42,
   129-140, 533-539`) parses audited crate and workspace files under a closed
   `Init + Std` parser environment and rejects custom command syntax such as
   `sf_recall` or `sf_experiment`. However, `sf_recall`, `sf_experiment`, and
   `sf_expect_failure_in` leave zero constants in `Environment.constants.map₂`
   or `.olean` `moduleData`, and all user declarations in a module using them
   replay cleanly through `minBaseEnv.toKernelEnv.replay` (`Init + Std` only).
   Adding a `<!-- tutor: recall -->` mode to `tutor_workflow.py` that elaborates
   quoted library blocks against `Trusted` and `Anneal` in a dedicated non-audit
   check file closes the Tutor drift gap without modifying `trusted/`.

## Applicability

The findings in this report apply to the combination and comparison of:

- **`plclub/sf-in-lean`** at commit `13e9425b4647402a09316c1d39fa555e9bc3c257`
  (`SFLCompat/`, `SFLMeta/`, `Targets*.lean`, `Main*.lean`, `Website/`, and
  `scripts/`).
- **`leanprover/verso`** at commit `cad4b633e75ea769b851f12f9ca3b4f0dfcc625f`
  (`v4.34.0`), **`leanprover/subverso`** at commit
  `9b90b7f938d6169246325df002351014f49945ef`, and **`leanprover/illuminate`** at
  commit `a1a61c9678da010e958ed24cdfa6f635b85f172a`.
- **`joshlf/anneal`** at `HEAD` commit
  `f938c18db56c49e82dde95506894a9b58b76b227`
  (`trusted/audit/TrustedBoundary.lean`) and Tutor branch
  `origin/Gk6v77bigheral6sjtzyeoq6ob52xgomw` at commit
  `6b7c210c6c70f2f1710424dd07b4829742ff9154` (`docs/tutor/*.md`,
  `docs/tutor/workflow/tutor_workflow.py`, `docs/tutor/workflow/tutor.toml`,
  `trusted/lean/Trusted/*.lean`, `theory/Anneal/**/*.lean`).
- **`leanprover/lean4`** release `v4.34.1` (commit
  `5045d0056413266e57c625dcd7c365b10e377c52`, `linux-x86_64`), which executes
  both preserved support probes (`support/ProbeRecallAndMatcherExt.lean` and
  `support/ProbeExperimentAndTutorAudit.lean`).

`sf-in-lean` pins `leanprover/lean4:v4.34.0` while Anneal pins
`leanprover/lean4:v4.34.1`. The core `SFLCompat` modules (`Experiment.lean`,
`Recall/Common.lean`, `Recall/Check.lean`, and `Recall/Source.lean`) use only
`Init`, `Std`, and `Lean` (once the unused top-level `import Batteries` in
`SFLCompat.lean:1` is omitted) and elaborate identically under Lean `v4.34.1`.
Behaviors that depend on Lean's equation compiler (`Lean.Meta.Match.matcherExt`,
`_sparseCasesOn_1`), `Meta.whnfCore` smart unfolding, `Elab.async` theorem
snapshot tasks, or `Command.State.ngen` apply to Lean `v4.34.0` and `v4.34.1`
and should be revalidated via the preserved probes before assuming they hold on
later Lean 4 toolchains.

## Findings

### Finding 1: Two-Tier `SFLCompat` / `SFLMeta` Architecture, Multi-Variant Byte-Range Extraction (`student`, `solutions`, `terse`, `grading`), and `Verso` / `SubVerso` / `Illuminate` Integration

`Basis: source`

#### 1.1 Two-Tier Separation (`SFLCompat/` vs. `SFLMeta/`)

`plclub/sf-in-lean` (`lakefile.toml:1-106`) partitions its metaprogramming into
two libraries so extracted student `.lean` projects do not depend on the
documentation generator:

- **`SFLCompat/`** (`SFLCompat.lean`, `SFLCompat/Experiment.lean`,
  `SFLCompat/Recall/Common.lean`, `SFLCompat/Recall/Check.lean`,
  `SFLCompat/Recall/Source.lean`, `SFLCompat/Tag.lean`, and
  `SFLCompat/Widget.lean`):
  Provides command elaborators (`sf_recall`, `sf_recall_source`,
  `sf_experiment`, `sf_expect_failure_in`, `sf_expect_failure_in?`, `sf_tag`,
  `#sf_axes_grid`) with zero dependency on `Verso`, `SubVerso`, or `Illuminate`.
  During `.lean` tarball extraction (`SFLMeta/Save/Lean.lean:160-175`,
  `Targets.lean:31`), `SFLCompat/` is copied into the generated student Lake
  workspace (`ExtractModuleConfig.supportRoots = #[`SFLCompat]`). Although
  `SFLCompat.lean:1` writes `import Batteries` and `SFLCompat/Widget.lean:5`
  imports `Batteries.Data.String.Basic`, the recall and experiment modules
  (`Experiment.lean`, `Recall/Common.lean`, `Recall/Check.lean`,
  `Recall/Source.lean`) depend only on core `Lean`.
- **`SFLMeta/`** (`SFLMeta.lean` and 15 submodules): Extends `VersoGenreManual`
  with textbook directives, exercise/solution/grading elaborators, `Illuminate`
  animations, and the four-variant `.lean` extractor invoked by `generate-all`,
  `generate-lf`, `generate-hl`, and `generate-ts`.

| File (`plclub/sf-in-lean` `13e9425b`) | Lines | Responsibility and Core Abstractions |
| :--- | :--- | :--- |
| `SFLMeta/Basic.lean` | 1–171 | Defines Verso inline/block extensions (`comment`, `inlineNote`, `stars`, `hidden`, `exportOnly`, `manualOnly`, `rawHtmlDiv`, `theoremBlock`, `exerciseHeader`, `center`) and CSS/JS injectors. |
| `SFLMeta/Solution.lean` | 1–273 | Implements term/tactic/command `solution!`, `workinclass!`, and `suggested! default sol`, recording byte spans in `SolutionRangeExt` (`MapDeclarationExtension (Array SolutionRange)`) and `SolutionBlockExt` (`PersistentEnvExtension SolutionRange`). |
| `SFLMeta/Exercise.lean` | 1–291 | Implements `:::exercise` (`stars`, `name`, `optional`, `advanced`) and checks that the enclosing section registered at least one entry in `SolutionBlockExt`. |
| `SFLMeta/Grade.lean` | 1–354 | Implements `grade_theorem` and `autograded_hole!` (`GradeTheoremExt`, `AutogradedHoleExt`), generating `Grading.lean` with `SubVerso.Examples.Slice` checks (`ensure_type`, `check_axioms`) and `#Points` totals. |
| `SFLMeta/Todo.lean` | 1–145 | Implements `:::todo` and `{todo}` directives gated by the `verso.todo.allow` option so CI can reject unfinished authoring notes. |
| `SFLMeta/Illuminate.lean` | 1–239 | Integrates `Illuminate` interactive animations (`:::illuminate`, `:::diagramWithAlt`), requiring a nested `:::alt` ASCII fallback block for `.lean` extraction. |
| `SFLMeta/Save/CodeBlock.lean` | 1–289 | Classifies Verso `Block.other` nodes, decodes `SubVerso.Highlighting.Highlighted` JSON payloads, and applies line-marker rewrites (`-- HIDE`, `-- ...`, `-- SOLUTION`). |
| `SFLMeta/Save/SourceRewrite.lean` | 1–194 | Sorts `SolutionRange` spans in descending byte order and splices source strings to produce `student`, `solutions`, `terse`, and `grading` variants. |
| `SFLMeta/Save/Extract.lean` | 1–354 | Walks the `Part Manual` AST, converts prose into `/-- ... -/` doc comments, rewrites code blocks per variant, and builds `ExtractedChapter` outputs. |
| `SFLMeta/Save/Lean.lean` & `Project.lean` | 1–273, 1–88 | Resolves transitive local imports (`parseImports`, `bundleLoop`), copies `SFLCompat`, writes standalone `lakefile.toml` and `lean-toolchain` files, and builds `.tar.gz` archives. |

#### 1.2 Two-Phase Elaboration and Right-to-Left Byte-Span Extraction

To verify complete instructor solutions during the book build while emitting
`sorry` or starter scaffolding for students, `SFLMeta` separates kernel
elaboration from byte-level source splicing:

1. **Elaboration phase (`SFLMeta/Solution.lean:77-273`):**
   - `solution! e` and `workinclass! e` elaborate `e` via `elabTerm` or
     `Tactic.evalTactic`.
   - `suggested! default sol` (`Solution.lean:105-120`) first elaborates the
     student starter expression `default` at `expectedType?` inside
     `withoutModifyingState`—ensuring the starter template itself typechecks—and
     then elaborates and returns `sol`.
   - `recordRange` (`Solution.lean:77-94`) extracts `stx.getRange?` and records
     a `SolutionRange` (`range : Lean.Syntax.Range`, `replacement? : Option
     String`, `isWorkInClass : Bool`) in `SolutionRangeExt` (keyed by
     `Term.getDeclName?`) and `SolutionBlockExt`.
   - Command-level `solution! <cmds>` (`commandSolution`,
     `Solution.lean:180-273`) elaborates `<cmds>` into the chapter environment
     and records the command block's byte range in `SolutionBlockExt`.
2. **Extraction phase (`SFLMeta/Save/SourceRewrite.lean:60-194`,
   `Extract.lean:120-354`):**
   `SourceRewrite.lean:60-90` sorts recorded `SolutionRange` spans in
   **descending (right-to-left) byte order** before splicing into the raw block
   string so earlier byte offsets remain valid across multiple replacements:
   - **`Variant.student`:** Splices term/tactic `solution!` and `workinclass!`
     spans to `sorry`, splices `suggested! default sol` spans to `default`,
     replaces command-level `solution!` blocks with `-- FILL IN HERE`, and
     unwraps any immediately preceding `sf_experiment` starter placeholder so
     students edit the starter definition directly.
   - **`Variant.terse`:** Splices both `workinclass!` and `solution!` spans to
     `sorry` and strips narrative prose outside `:::exportOnly` blocks for live
     lecture coding (`Extract.lean:180-215`).
   - **`Variant.solutions`:** Strips `solution!`, `workinclass!`, and
     `suggested! default` wrappers to leave the clean inner `sol` text, and
     omits preceding `sf_experiment` starter placeholders.
   - **`Variant.grading` (`SFLMeta/Grade.lean:120-354`):** Emits `Grading.lean`,
     which imports the student's `Chapter.lean` and the instructor's
     `Solution.lean`, invokes `SubVerso.Examples.Slice` (`ensure_type` and
     `check_axioms`) to verify that each target theorem has the expected type
     and depends only on allowed axioms (`propext`, `Quot.sound`,
     `Classical.choice`), and prints `#Points` totals.

#### 1.3 `Verso`, `SubVerso`, and `Illuminate` Integration

- **`leanprover/verso`** (`cad4b633`,
  `src/verso-manual/VersoManual/InlineLean.lean:119-265`):
  Maintains one persistent `Command.State` (`LeanBlockState.commandState`) per
  chapter module with `infoState.enabled := true`. Every fenced
  ```` ```lean ```` block is parsed and elaborated sequentially against this
  shared state, highlighted via `SubVerso.Highlighting.Code.highlight`
  (`InlineLean.lean:212-235`), and serialized into `Block.other (Block.lean hls
  ...)`.
- **`leanprover/subverso`** (`9b90b7f9`,
  `src/SubVerso/Highlighting/Code.lean:1-620`):
  Walks the `Syntax` tree and `Command.State.infoState.trees` to produce a
  `Highlighted` AST of semantic tokens (`Kind.const`, `Kind.var`, `Kind.sort`,
  `Kind.keyword`), diagnostic spans, and before/after tactic goal states,
  caching local-variable hover strings in `HighlightState.varTypes : HashMap
  VarTypeKey (Option String)` keyed by `VarTypeKey.fvar (id : FVarId)`
  (`Code.lean:94-101, 471-505`).
- **`leanprover/illuminate`** (`a1a61c96`) and
  `SFLMeta/Illuminate.lean:145-239`:
  Compiles Lean animation specifications into interactive HTML timeline widgets,
  while `:::diagramWithAlt` enforces a mandatory `:::alt` ASCII diagram fallback
  that `Extract.lean` emits into `/-- ... -/` doc comments in extracted `.lean`
  files.

---

### Finding 2: Semantic (`sf_recall`) and Textual (`sf_recall_source`) Declaration Drift Checking, Complete Check Matrix, Five Matcher/Cross-Module Edge Cases (Including Non-Persistent `matcherExt` Cross-Module Failure), and Mechanized Fix (`sf_recall_fixed`)

`Basis: source + execution + derived`

#### 2.1 `sf_recall` and `sf_recall_source` Elaboration Mechanics

`SFLCompat/Recall` provides two complementary commands for verifying that a
declaration restated in prose has not drifted from the actual declaration in the
Lean environment:

1. **Elaboration-checked semantic recall**
   (`SFLCompat/Recall/Check.lean:325-430`):
   Supports three surface forms:
   - `sf_recall <command>`: Elaborates `<command>` and compares its full
     declaration against the original in `Environment`.
   - `sf_recall +strictUniverse <command>`: Disables monomorphic universe
     specialization when comparing universe parameters.
   - `sf_recall statement <ident> : <term>`: Elaborates `<term>` as a type via
     `Term.elabType` (`Check.lean:411-413`), enforces equal universe parameter
     counts (`stParams.size == origInfo.levelParams.length`, `Check.lean:416`),
     and checks `Meta.isDefEq t origInfo.type` (`Check.lean:420`) without
     elaborating a proof or value body.

   When `elabRecallCommand` (`Check.lean:334-390`) runs on `<command>`:
   - **Target resolution (`Common.lean:25-37`, `Check.lean:335-338`):**
     `declaredName` extracts the single `Lean.Parser.Command.declId` node
     (rejecting `mutual` blocks and anonymous commands), and
     `realizeGlobalConstNoOverloadWithInfo` resolves the target constant
     `xActual` in the current environment inside `withoutExporting`.
   - **Hidden-namespace elaboration (`Check.lean:339-388`):** It allocates a
     fresh ID via `mkFreshId` and converts it to a single `Name.str` component
     `ns := Name.mkStr1 (← liftCoreM mkFreshId).toString` (`Check.lean:357`).
     Converting `mkFreshId`'s trailing `Name.num` into a `Name.str` component is
     essential because `Lean.ResolveName.resolveUsingNamespace` only walks up
     enclosing namespace chains composed of `Name.str` components; a trailing
     `Name.num` would silently break namespace resolution inside the restated
     declaration (`Check.lean:343-356`).
   - **Prefix renaming and `InfoTree` rewriting (`Check.lean:65-110, 382`):**
     `renameBackName chk orig n` replaces prefix `chk`
     (`<currNs>._uniq.N.<decl>`) with `orig` (`xActual`) on every `.const n us`
     in the restated declaration's type, value, constructor types, and
     `InfoTree` nodes (so IDE hovers and go-to-definition point to `orig`),
     after which `finally setEnv envBefore` (`Check.lean:390`) rolls back the
     environment.
2. **Textual byte-for-byte recall (`SFLCompat/Recall/Source.lean:39-58`):**
   `sf_recall_source <command>` resolves `x` via
   `realizeGlobalConstNoOverloadWithInfo`, attaches `addConstInfo cmd x` across
   the command span, extracts the original declaration's source text via
   `sourceOf x` (`Common.lean:127-142`, using `findDeclarationRanges?`) and the
   restatement's text via `sourceOfSyntax cmd`, and checks `dedent restated ==
   dedent original` (`Source.lean:53`) **without elaborating `<command>`**.

#### 2.2 Complete Check Matrix and Docstring Discrepancy in `Check.lean`

Comparing the module docstring in `SFLCompat/Recall/Check.lean:25-32` against
the implementation of `checkMatch` and `checkMatchCore` (`Check.lean:146-317`)
and executing `support/ProbeRecallAndMatcherExt.lean` reveals a concrete
discrepancy: the docstring states that `sf_recall` compares *"a `def`'s value,
safety, and abbreviation status"* and *"a structure's fields, field defaults,
and type-class registration"*, whereas `checkMatchCore` **never inspects**
`defnInfo.safety`, `defnInfo.hints` (`ReducibilityHints.abbrev`), or structure
field default declarations (`<Struct>.<field>._default`).

| Declaration Aspect | Checked by `sf_recall`? | Implementation Mechanism (`SFLCompat/Recall/Check.lean`) & Empirical Verification |
| :--- | :--- | :--- |
| Declaration type (`ci.type`) | **Yes** (up to `Meta.isDefEq`) | `checkTypesMatch` (`Check.lean:146-166`). |
| `def` value (`defnInfo.value`) | **Yes** (up to `Meta.isDefEq`) | `checkMatchCore` (`Check.lean:222-233`). |
| `theorem` proof (`thmInfo.value`) | **No** (proof-irrelevant) | `checkMatchCore` (`Check.lean:283`). |
| `theorem` recalled as `def` | **No** (accepted, value ignored) | `.thmInfo _, .defnInfo _ => pure ()` (`Check.lean:284`). Note that the reverse (`.defnInfo _, .thmInfo _`) is rejected at `Check.lean:287-289`. |
| Binder names & implicitness (`{x}` vs. `(x)`) | **Parameter types/order checked; binder names and `BinderInfo` NOT checked** | `Meta.isDefEq` on `.forallE` and `.lam` compares domains and bodies while ignoring `binderName` and `binderInfo`. |
| Inductive `numParams` & `numIndices` | **Yes** | `orig.numParams == restated.numParams && orig.numIndices == restated.numIndices` (`Check.lean:235`). |
| Constructor count, order, names, & types | **Yes** | `Check.lean:237-259` checks `ctors.length`, suffix equality (`origCtor.actual == renamedChkCtor.actual`), and `checkTypesMatch` on each constructor pair. |
| Structure field names & order | **Yes** | `getStructureInfo?` compares `origSi.fieldNames` and `chkSi.fieldNames` (`Check.lean:264-272`). |
| `class` vs. `structure` & `outParam` positions | **Yes** | `getOutParamPositions?` (`some #[]` for `class` vs. `none` for `structure`) and `getOutLevelParamPositions?` (`Check.lean:273-275`). |
| Universe parameters (default `sf_recall`) | **Allows full monomorphic specialization** | Accepts `orig.levelParams.length == chk.levelParams.length` (`Check.lean:304`) or `!orig.levelParams.isEmpty && chk.levelParams.isEmpty` via `mkFreshLevelMVarsFor` (`Check.lean:308-315`); rejects partial specialization (`Check.lean:317`). |
| Universe parameters (`+strictUniverse` & `statement`) | **Strict equality** | Requires equal universe parameter counts (`Check.lean:154, 308, 416`). |
| `abbrev` vs. `def` (`ReducibilityHints`) | **No** (contrary to docstring at `Check.lean:28`) | `defnInfo.hints` is not inspected (`ProbeRecallAndMatcherExt.lean:458-462`). |
| `def` safety (`safe` vs. `partial` vs. `unsafe`) | **No** (contrary to docstring at `Check.lean:28`) | `defnInfo.safety` is not inspected. |
| Structure field defaults (`x : Nat := 0`) & `private` field visibility | **No** (contrary to docstring at `Check.lean:31`) | Default values live in `<Struct>.<field>._default` and `DeclId.ofActual` strips `_private` via `privateToUserName` (`Check.lean:53, 268`; `ProbeRecallAndMatcherExt.lean:464-467`). |
| Attributes (`@[simp]`, `@[ext]`, instances) | **No** | Environment extensions are not compared and are rolled back by `setEnv envBefore`. |
| Mutual declarations (`mutual ... end`) | **Unsupported** (rejected) | `declaredName` rejects commands with $>1$ `declId` (`Common.lean:32-37`). |

#### 2.3 Five Matcher and Cross-Module Edge Cases in `sf_recall` (and `sf_recall_source`)

Executing `support/ProbeRecallAndMatcherExt.lean` in Lean `v4.34.1` establishes
five distinct failure modes in `sf_recall` on pattern-matching definitions (plus
a cross-module search-path failure in `sourceOf`):

1. **Edge Case 1 — Dangling `.match_1` crash when `orig` has no matcher
   (`Check.lean:65-69`, `ProbeRecallAndMatcherExt.lean:516-525`):**
   Suppose `pairSumProj (p : Nat × Nat) : Nat := p.1 + p.2` is defined using
   projections (creating no `pairSumProj.match_1` constant in `env`) and
   recalled using pattern matching (`| (a, b) => a + b`). Elaborating the
   restatement inside `_uniq.N` generates `_uniq.N.pairSumProj.match_1` in the
   temporary environment. Because `chk` (`_uniq.N.pairSumProj`) is a prefix of
   `_uniq.N.pairSumProj.match_1`, `renameBackName` rewrites the constant inside
   `restated.value` to `<orig>.pairSumProj.match_1`, which does not exist in
   `env`, crashing `Meta.isDefEq` with:
   ```text
   Unknown constant `ProbeRecallAndMatcherExt.AnnealSample.pairSumProj.match_1`
   ```
2. **Edge Case 2 — Ill-typed `Expr` corruption when `match` arms are reordered
   (`Check.lean:65-69`, `ProbeRecallAndMatcherExt.lean:527-540`):**
   When `PrefixOutcome.isSafe` matches constructors in order `.running`,
   `.terminated _`, `.failed _`, `.stuck`, its auxiliary matcher
   `PrefixOutcome.isSafe.match_1` takes minor-premise parameters in order
   `(Unit → Prop) → (TerminationKind Val → Prop) → (FailureKind → Prop) →
   (Unit → Prop)`. If a restatement places `| .stuck => False` first,
   `_uniq.N.PrefixOutcome.isSafe.match_1` takes minor premises in order
   `(Unit → Prop) → (Unit → Prop) → (TerminationKind Val → Prop) →
   (FailureKind → Prop)`. Rewriting `_uniq.N.PrefixOutcome.isSafe.match_1` to
   `PrefixOutcome.isSafe.match_1` via `renameBackName` leaves the arguments in
   the restatement's order, passing `fun (_ : Unit) => True` into the
   `TerminationKind Val → Prop` parameter slot and constructing an ill-typed
   `Expr`.
3. **Edge Case 3 — `Meta.isDefEq` vs. `Kernel.isDefEq` on neutral matcher
   applications (`ProbeRecallAndMatcherExt.lean:542-551`):**
   Even when `_uniq.N.<decl>.match_1` is not renamed, comparing a `match`-based
   definition (`PrefixOutcome.isSafe`) against an equivalent definition written
   with `PrefixOutcome.casesOn` or reordered `match` arms fails in
   `Lean.Meta.isDefEq`. Under the lambda binder `fun (x : PrefixOutcome Val) =>
   ...`, the discriminant `x` is a free variable (`FVar`). In Lean 4's
   `Meta.whnfCore`, `isMatcherApp` reduction refuses to unfold a matcher when
   its discriminant is neutral (`x`), so `Meta.isDefEq` treats
   `PrefixOutcome.isSafe.match_1 ... x ...` and
   `_uniq.N.PrefixOutcome.isSafe.match_1 ... x ...` (or `PrefixOutcome.casesOn
   ... x ...`) as stuck applications with distinct head constants. By contrast,
   `Kernel.isDefEq` (and explicit matcher unfolding) unfolds both `.match_1`
   constants to `PrefixOutcome.casesOn` on `x` and succeeds.
4. **Edge Case 4 — Lean 4.34 `_sparseCasesOn_1` wildcard compilation on $\ge 4$
   constructors (`ProbeRecallAndMatcherExt.lean:553-564`):**
   In Lean `v4.34.1`, when a `match` on an inductive with $\ge 4$ constructors
   (`PrefixOutcome`) uses a wildcard catch-all covering multiple constructors
   (matching `.running` and `.terminated _` and writing `| _ => False` for
   `.failed _` and `.stuck`), the equation compiler generates an auxiliary
   `_sparseCasesOn_1` combinator with a higher-order motive:
   ```lean
   motive := fun t => (Nat.hasNotBit 3 t.ctorIdx → motive t) → motive t
   ```
   applied to the catch-all continuation `(fun _ => False)` *outside*
   `PrefixOutcome.rec`. Because `PrefixOutcome.rec ... t (fun _ => False)` is
   stuck on the neutral variable `t`, a commuting conversion is required to push
   `(fun _ => False)` into the constructor branches. Neither `Meta.isDefEq` nor
   `Kernel.isDefEq` performs commuting conversions on eliminators, so a
   wildcard-compressed `match` on $\ge 4$ constructors is only propositionally
   equal (`∀ x, f x = g x`), not definitionally equal, to an exhaustive
   constructor-by-constructor `match`.
5. **Edge Case 5 — Cross-module `matcherExt` non-persistence crash on
   byte-for-byte identical definitions**
   (`ProbeRecallAndMatcherExt.lean:566-636`):
   In `Lean/Meta/Match/MatcherApp/Basic.lean` and
   `Lean/Meta/Match.lean:872-890`, `Lean.Meta.Match.matcherExt` is registered
   via `registerEnvExtension (pure {}) (asyncMode := .local)`—a
   **non-persistent** environment extension that is never serialized into
   `.olean` files.
   - When a module `ModA` defines two functions `earlierIsNil` and `laterIsNil`
     with the same `match` splitter shape on `List α`, elaborating
     `earlierIsNil` creates `ModA.earlierIsNil.match_1` and records it in
     `matcherExt`. When `laterIsNil` elaborates in `ModA`,
     `mkMatcherAuxDefinition` finds `ModA.earlierIsNil.match_1` in `matcherExt`
     and reuses it; **`ModA.laterIsNil.match_1` is never created in
     `ModA.olean`**.
   - **Same-module illusion:** Calling stock `sf_recall` on `laterIsNil`
     *inside* `ModA` succeeds because `matcherExt` still holds
     `ModA.earlierIsNil.match_1`, so `_uniq.N.laterIsNil` also reuses
     `ModA.earlierIsNil.match_1` and `renameBackName` is a no-op.
   - **Cross-module crash:** When a downstream module `ModB` imports `ModA`,
     `matcherExt` starts empty. Calling stock `sf_recall` in `ModB` on the
     **exact, byte-for-byte identical** definition of `laterIsNil` elaborates a
     fresh `_uniq.N.laterIsNil.match_1`, which `renameBackName` rewrites to the
     non-existent constant `ModA.laterIsNil.match_1`, crashing `sf_recall` with:
     ```text
     Unknown constant `ProbeRecallAndMatcherExt.CrossModuleSim.laterIsNil.match_1`
     ```
6. **Cross-module `sourceOf` search-path failure under `lake build`
   (`SFLCompat/Recall/Common.lean:133-140`):**
   `sourceOf` locates imported `.lean` files via `let sp ← getSrcSearchPath` and
   `sp.findModuleWithExt "lean" modName`. Because `getSrcSearchPath` reads only
   `LEAN_SRC_PATH` and the toolchain sysroot (`lib/lean/src`), and `lake build`
   sets `LEAN_PATH` without setting `LEAN_SRC_PATH`, `sf_recall_source` on any
   imported project module fails with `"source for module '<ModName>' is not on
   the search path"` (and `sf_recall`'s `replaceWithOriginalHint` silently drops
   its code action at `Check.lean:371`) unless `System.FilePath.mk "."` is
   appended to `getSrcSearchPath`.

#### 2.4 Mechanized Fix (`sf_recall_fixed`)

Replacing prefix renaming (`chk.isPrefixOf n`) on `defnInfo` values with exact
top-level constant renaming (`renameExact`, which rewrites only `n == chk` so
recursive calls resolve to `orig` while `_uniq.N.<decl>.match_1` stays intact in
the temporary environment) and falling back to unfolding matcher applications
via `Meta.transform` + `unfoldDefinition?` (`unfoldMatchersIn`) when
`Meta.isDefEq` initially returns `false`
(`support/ProbeRecallAndMatcherExt.lean:642-725`):

```lean
def renameExact (chk orig : Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if n == chk then some (.const orig us) else none
    | _ => none

def unfoldMatchersIn (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if let .const c _ := e.getAppFn then
      if ← isMatcher c then
        if let some e' ← unfoldDefinition? e then
          return .visit e'
    return .continue)
```

resolves Edge Cases 1, 2, 3, and 5 in both same-module and cross-module
post-`.olean`-import environments (`ProbeRecallAndMatcherExt.lean:705-725`).

---

### Finding 3: In-File State Rollback (`sf_experiment`, `sf_expect_failure_in`), Custom Indentation Parsing (`rawCommandBlock`), Asynchronous Theorem Elaboration (`Elab.async`), and the `NameGenerator` (`ngen`) `FVarId` Collision Bug

`Basis: source + execution + derived`

#### 3.1 `withRestoringState` and Indentation-Sensitive `rawCommandBlock` Parsing

`SFLCompat/Experiment.lean` provides `sf_experiment`, `sf_expect_failure_in`,
and `sf_expect_failure_in?` to elaborate exploratory or intentionally failing
commands in-place and roll back their environment effects:

- **Why `rawCommandBlock` (`Experiment.lean:53-115`) parses raw lines instead of
  `many1Indent command`:** In Lean 4, command elaboration runs only after the
  outer command finishes parsing. If `sf_expect_failure_in` used `Command`
  syntax directly, any intentional parse error inside the block (such as `def :=
  :=` or an incomplete `match`) would fail the outer parse of
  `sf_expect_failure_in` before `elabExpectFailureCmd` (`Experiment.lean:175`)
  could intercept it. Instead, `rawCommandBlockFn` consumes the first line and
  all subsequent blank or deeper-indented lines (`checkColGeFn`) as raw text,
  and `runRawCmds` (`Experiment.lean:80-113`) constructs an `InputContext` slice
  and loops calling `Parser.parseCommand`, `elabCommand`, and `runLinters`
  inside `failIfSucceeds`.
- **State rollback (`withRestoringState`, `Experiment.lean:29-38`):**
  ```lean
  private def withRestoringState (keepMsgs : Bool) (m : CommandElabM Unit) :
      CommandElabM Unit := do
    let savedState ← get
    try
      m
    finally
      let state ← get
      set { savedState with
        -- Preserve the info tree
        infoState := state.infoState
        messages := if keepMsgs then state.messages else savedState.messages }
  ```
  All declarations, notations, attributes, typeclass instances, and environment
  extensions in `Command.State.env`—along with `scopes`—are restored to
  `savedState`, while `infoState` (hover and tactic goal `InfoTree`s) is kept.

#### 3.2 Why `commandWithoutAsync` (`Elab.async.set false`) Is Mandatory for Theorem Proofs

`SFLCompat/Experiment.lean:15-27` wraps both `sf_experiment` and
`sf_expect_failure_in` in `commandWithoutAsync`, which sets `Elab.async` to
`false` on the current `Scope`. Mechanized verification in
`support/ProbeExperimentAndTutorAudit.lean:269-316` demonstrates why this is
required in Lean `v4.34.1`:

- Under Lean 4's default `Elab.async = true`, `elabCommand` on `theorem
  asyncBroken : 1 = 2 := by rfl` elaborates the theorem header synchronously and
  spawns **2 background tasks** in `Command.State.snapshotTasks` to elaborate
  the proof body asynchronously. Immediately after `elabCommand` returns,
  `(← get).messages.hasErrors` is **`false`**, so `failIfSucceeds` in
  `sf_expect_failure_in` would falsely fail with `"unexpected success"` while
  the background snapshot task later reports an unhandled error outside the
  rollback window.
- Under `Elab.async = false` (`commandWithoutAsync`), `elabCommand` elaborates
  the proof body synchronously (`snapshotTasks.size == 0`,
  `messages.hasErrors == true`).

#### 3.3 The `NameGenerator` (`ngen`) Reset Bug and `FVarId` Collisions in `InfoTree`

Because `withRestoringState` (`SFLCompat/Experiment.lean:35-38`) restores
`{ savedState with infoState := state.infoState, messages := ... }`, it resets
`Command.State.ngen` (`NameGenerator`) and `nextMacroScope` back to
`savedState.ngen` and `savedState.nextMacroScope` while retaining the
`InfoTree`s generated during `m` in `state.infoState.trees`.

- While top-level constants (`_uniq.N`) created in `state.env` are discarded
  when `savedState.env` is restored, local binder `FVarId`s (`_uniq.N`)
  allocated from `ngen` during term and tactic elaboration are stored inside
  `InfoTree` nodes (`TermInfo.expr` and `MetavarContext` `LocalDecl`s) in
  `state.infoState.trees`.
- Because `ngen` is reset to `savedState.ngen`, the command elaborated
  immediately after `sf_experiment` starts from the exact same `NameGenerator`
  counter and assigns the **exact same `FVarId`s (`_uniq.N`)** to its local
  binders.
- In `VersoGenreManual` (`InlineLean.lean:133-163`), all code blocks in a
  chapter share one `Command.State` with `infoState.enabled := true`, and
  `SubVerso.Highlighting.Code.highlight`
  (`SubVerso/Highlighting/Code.lean:94-101, 471-505`) caches local variable
  hover types in `HighlightState.varTypes : HashMap VarTypeKey (Option String)`
  keyed by `VarTypeKey.fvar (id : FVarId)`. Reusing `FVarId`s across
  `InfoTree`s in the same highlighting state aliases distinct local variables
  with different types in `varTypes`.
- In `support/ProbeExperimentAndTutorAudit.lean:333-391`, elaborating `def expFn
  (a : String) : String := a` inside stock `withRestoringState` followed by `def
  nextFn (b : Bool) : Bool := b` produces **3 colliding `FVarId`s** between the
  two commands' `InfoTree`s (`stockFVarCollisions = 3`). Updating
  `withRestoringState` to preserve `ngen` and `nextMacroScope`:
  ```lean
  set { savedState with
    infoState := state.infoState
    messages := if keepMsgs then state.messages else savedState.messages
    ngen := state.ngen
    nextMacroScope := state.nextMacroScope }
  ```
  yields **0 colliding `FVarId`s** (`fixedFVarCollisions = 0`).

---

### Finding 4: Complete Audit of All 89 Fenced Code Blocks in Anneal Tutor (`6b7c210c`) and Live Detection of 6 Drifted Unmanaged Library Blocks

`Basis: source + execution`

#### 4.1 Anneal Tutor Workflow vs. `sf-in-lean`

On Anneal Tutor branch `origin/Gk6v77bigheral6sjtzyeoq6ob52xgomw` (commit
`6b7c210c6c70f2f1710424dd07b4829742ff9154`),
`docs/tutor/workflow/tutor_workflow.py` and `docs/tutor/workflow/tutor.toml`
manage fenced code blocks preceded by
`<!-- tutor: project=<name> file=<path> step=<id> [mode=replace|check] -->`:

- `mode=replace` overwrites `<file>` in a temporary copy of `examples/tutor-*`
  at each step and runs `cargo anneal verify` (or `cargo build`), checking exit
  status (`expect = "pass"` or `"fail"`) and `expect_substrings`. Steps marked
  `probe = true` in `tutor.toml` discard their file edits after the step runs.
- `mode=check` (`verify_check_snippets`, `tutor_workflow.py:310-358`) checks
  that generated `.anneal/` files from the preceding step contain each non-`--
  ...` substring chunk in order.
- However, `docs/tutor/workflow/README.md:144-147` explicitly leaves blocks that
  quote Anneal's Lean libraries (`trusted/lean/`, `theory/Anneal/`) as ordinary
  unmanaged fenced blocks.

#### 4.2 Audit of All 89 Fenced Code Blocks Across `docs/tutor/*.md` on `6b7c210c`

Across all seven Markdown files in `docs/tutor/` on `6b7c210c`, there are **89
fenced code blocks**:

- **73 managed blocks (`<!-- tutor: ... -->`):** 68 `mode=replace` blocks and 5
  `mode=check` blocks. All 73 were updated during the `6b7c210c` port to
  coinductive `ITree` and `Std` foundations and pass `tutor_workflow.py`.
- **16 unmanaged blocks (no `<!-- tutor: ... -->` directive):** 6 non-Lean
  illustrative blocks (1 ASCII directory layout, 5 Rust/shell snippets) and **10
  Lean fenced blocks** quoting declarations from `trusted/lean/`,
  `theory/Anneal/`, or `tests/refinement/`.

Auditing all 10 unmanaged Lean fenced blocks against the actual repository
declarations at `6b7c210c` (and testing them with `sf_recall` in
`support/ProbeExperimentAndTutorAudit.lean:397-615`) revealed that **6 of the 10
unmanaged Lean blocks** (plus adjacent prose in `README.md`,
`02-rust-specifications.md`, `04-manual-proof-workflow.md`, and
`05-verifying-unsafe-rust.md`) silently drifted during `6b7c210c`:

| # | Tutor File & Line Range (`6b7c210c`) | Quoted Lean Declarations | `sf_recall` Status | Exact Semantic / API Drift vs. `6b7c210c` Codebase |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `docs/tutor/README.md:40-46` | `structure Partial` | **PASS** | Matches `trusted/lean/Trusted/Refinement.lean:51-55` (`defined : Prop`, `val : defined → α`). |
| 2 | `docs/tutor/01-basic-usage-and-outputs.md:372-407` | `MirExecPartial`, `MirContractSpec` | **FAIL (Drifted)** | Quotes removed `Partial (BehaviorSet (ExecPrefix MirObs Value))`, `MirNoUB.holds (MirSem ⟨body, args⟩)`, `ReachesNormalReturn`, and `Preorder.refines`. At `6b7c210c`, `Trusted/VerificationResult.lean:89-120` uses `(mirCallTree body args).toPartial` over `Partial (BehaviorSet (List (Event MirEffect) × MirOutcome))` and `≤`. |
| 3 | `docs/tutor/02-rust-specifications.md:589-612` | `Partial.contract`, `Language.WellFormedOn`, `Language.WellFormed`, `Language.ContractSpec` | **PASS (`sf_recall`) / FAIL (`sf_recall_source`)** | `02-rust-specifications.md:597-601` writes `Language.WellFormedOn` with named structure fields `{ defined := safetyPre q, val := fun _ _ => True }`, whereas `Trusted/Refinement.lean:227-229` writes `⟨safetyPre q, fun _ _ => True⟩`. `sf_recall` accepts this via definitional equality; `sf_recall_source` rejects it. |
| 4 | `docs/tutor/02-rust-specifications.md:629-637` | `structure Compiler`, `def Compiles` | **FAIL (Drifted)** | Quotes removed `Preorder.refines (L_tgt.sem t) (π_c (L_src.sem s))` instead of `L_tgt.sem t ≤ π_c (L_src.sem s)` (`abbrev Compiles`) in `Trusted/Refinement.lean:268-281`. |
| 5 | `docs/tutor/02-rust-specifications.md:645-662` | `theorem safe_contractSpec_preserves_wellFormed`, `theorem misplaced_contractSpec_violates_wellFormed` | **FAIL (Drifted)** | Both theorems quote `Preorder.refines` instead of `≤` (`tests/refinement/ConcreteYDiagram.lean:94-105`). |
| 6 | `docs/tutor/02-rust-specifications.md:672-676` | `structure Compiler.Verified` | **FAIL (Drifted)** | Depends on drifted `Compiles` from block #4 and omits universe parameter `u` (`Compiler.Verified.{u}`). |
| 7 | `docs/tutor/02-rust-specifications.md:682-688` | `def MirContractHoldsWithSafety`, `def MirContractHolds` | **PASS (Prose at L690 drifted)** | Code block matches `Trusted/VerificationResult.lean:124-131` (`≤`), but prose at line 690 still states `"where MirContractHoldsWithSafety is Preorder.refines"`. |
| 8 | `docs/tutor/04-manual-proof-workflow.md:388-398` | `theorem dischargeSafeRustBoundedU8` | **FAIL (Deleted)** | Quotes `dischargeSafeRustBoundedU8` (and prose at `04:20, 380-405`, `02:152`, `README.md:174, 216` cites `dischargeSafeRustBoundedU8` / `dischargeRustBoundedU8`), both of which were deleted from `theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean` in favor of `dischargeSymMir`. |
| 9 | `docs/tutor/05-verifying-unsafe-rust.md:56-99` & `112-115` | `MirStatefulExecPartial`, `MirStatefulContractSpec`, `MirStatefulContractHoldsWithSafety`, `MirStatefulContractHolds` | **FAIL (Drifted)** | Quotes removed `ReachesPrefix MirMachine`, `ReachesNormalReturn`, `Partial (BehaviorSet (Value × Memory))`, and `Preorder.refines` instead of `(mirStatefulTree body args mem).toPartial` over `Partial (BehaviorSet (List (Event MirEffect) × MirOutcome))` and `≤` (`Trusted/VerificationResult.lean:164-190`). |
| 10 | `docs/tutor/05-verifying-unsafe-rust.md:374-387` | `theorem dischargeStatefulEq` | **FAIL (Drifted)** | Quotes `h_wp : WP (runMirStatefulBounded fuel c.body expectedArgs expectedMem) ...` (and prose at lines 393–394 cites `runMirStatefulBounded`), whereas `SymbolicEval.lean:2156-2172` at `6b7c210c` uses `wpMirSym fuel c.body (initMachineStateWithMemory c.body expectedArgs expectedMem) (mirNormalPost ...)`. |

Block #3 (`docs/tutor/02-rust-specifications.md:589-612`) illustrates why
elaboration-based semantic checking (`sf_recall`) is better suited to Anneal
Tutor prose than textual substring matching (`mode=check` or
`sf_recall_source`): the tutorial writes `{ defined := safetyPre q, val := fun _
_ => True }` to make the field names explicit for first-time readers, while
`Trusted/Refinement.lean:228` uses the compact anonymous constructor
`⟨safetyPre q, fun _ _ => True⟩`. Because both elaborate to the exact same
`Partial.mk` application, `sf_recall` verifies semantic equivalence without
forcing the library source and tutorial prose to use identical surface syntax.

---

### Finding 5: `TrustedBoundary.lean` Compatibility, Zero-Constant `.olean` Footprint, and `<!-- tutor: recall -->` Architecture for `tutor_workflow.py`

`Basis: source + execution + derived`

#### 5.1 Interaction with `TrustedBoundary.lean` (`f938c18db` and `6b7c210c`)

Inspecting `trusted/audit/TrustedBoundary.lean` (`f938c18db` lines 36–42,
129–140, 533–564) and executing
`support/ProbeExperimentAndTutorAudit.lean:620-745` establish two boundary
invariants governing where `SFLCompat`-style commands can and cannot appear in
Anneal:

1. **Why custom command syntax (`sf_recall`, `sf_experiment`) cannot appear in
   audited `.anneal/` crate proof files (`Proof/<item>.lean`), `trusted/lean/`,
   or `theory/Anneal/`:**
   During Phase 1 (`"preflight"` / `verifyAudit`),
   `TrustedBoundary.inspectSource` parses every source file in the audited crate
   and workspace using a **closed parser environment** initialized from `Init`
   and `Std` alone:
   ```lean
   let parserEnv ← importModules #[{ module := `Init }, { module := `Std }] {}
     (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
   ```
   and requires every command syntax node `stx.getKind` to belong to the fixed
   16-kind `commandKinds` allowlist (`declaration`, `namespace`, `section`,
   `end`, `universe`, `variable`, `open`, `openScoped`, `export`, `mutual`,
   `in`, `attribute`, `moduleDoc`, `set_option`, `notation`, `mixfix`). In
   addition, Phase 2 (`verifyAudit`) requires every module in the `.olean`
   import graph to satisfy `isFoundationMod || isTrustedMod || isTheoryMod ||
   isWorkspaceMod`. As verified in
   `support/ProbeExperimentAndTutorAudit.lean:670-690`,
   `checkClosedParserSnippet closedParserEnv` accepts pure Lean declarations
   (`Except.ok 3`) and rejects `sf_recall` with `"command parser error (custom
   syntax not in closed parserEnv)"`.
2. **Zero-constant `.olean` footprint and clean `Kernel.Environment.replay`
   outside audited crate modules:**
   In `support/ProbeExperimentAndTutorAudit.lean:650-689`, inspecting
   `env.constants.map₂` after executing `sf_recall`, `sf_experiment`, and
   `sf_expect_failure_in` confirms **zero leaked `_uniq.*` or experimental
   constants** (`recordedLeakedConsts == 0`), and all 159 declarations in
   `TutorAudit` replay cleanly through `minBaseEnv.toKernelEnv.replay` where
   `minBaseEnv` imports only `Init` and `Std` (neither `Lean` nor `SFLCompat`).

#### 5.2 `<!-- tutor: recall -->` Integration Design for `tutor_workflow.py`

Because `docs/tutor/*.md` is verified by `docs/tutor/workflow/tutor_workflow.py`
outside `.anneal/` crate packages, `tutor_workflow.py` can close the library
declaration drift gap without modifying `trusted/lean/` or
`TrustedBoundary.lean`:

1. **Non-trusted helper module (`TutorCheck.lean`):** Place the standalone
   Lean `v4.34.1` `sf_recall_fixed`, `sf_recall statement`, `sf_experiment`, and
   `sf_expect_failure_in` elaborators (including `renameExact` +
   `unfoldMatchersIn` from Finding 2.4 and `ngen`/`nextMacroScope` preservation
   from Finding 3.3) in a test/workflow support module outside `trusted/`.
2. **Directive syntax in `docs/tutor/*.md`:** Annotate library-quoting Lean
   blocks with `<!-- tutor: recall -->` (or `<!-- tutor: recall kind=statement
   -->` for theorem signatures whose proof bodies are elided in prose).
3. **Single-batch elaboration in `tutor_workflow.py check`:** Have
   `tutor_workflow.py` collect all `<!-- tutor: recall ... -->` blocks across
   `docs/tutor/*.md`, emit a single temporary `.lean` file importing `Trusted`,
   `Anneal`, and `TutorCheck`, and run one `lean` invocation. Because all
   `sf_recall_fixed` checks run in-memory via `setEnv envBefore` inside a single
   Lean process in under 3 seconds, `tutor_workflow.py check` gains fast,
   kernel-backed drift detection over every quoted `trusted/lean/` and
   `theory/Anneal/` declaration.

## Boundaries

- **Not examined — Full `Verso` HTML/JS site generation and `Illuminate` browser
  rendering:** We inspected the Lean source of `SFLMeta/Basic.lean`,
  `SFLMeta/Illuminate.lean`, `Website/Theme.lean`, and `Main*.lean`, but did not
  execute the full multi-volume `generate-all` HTML build or headless browser
  tests of `Illuminate` canvas animations, as Anneal Tutor uses standard
  Markdown rather than Verso HTML output.
- **Known not to apply — Definitional equality for Lean 4.34 `_sparseCasesOn_1`
  wildcard matches on $\ge 4$ constructors:** As established in Finding 2.3
  (Edge Case 4), `sf_recall_fixed` (`renameExact` + `unfoldMatchersIn`) does
  not make a wildcard catch-all `match` on an inductive with $\ge 4$
  constructors definitionally equal to an exhaustive constructor-by-constructor
  `match`, because Lean `v4.34.1` compiles multi-constructor wildcards via
  `_sparseCasesOn_1` with a higher-order motive `Nat.hasNotBit ... → motive t`
  that is only propositionally equal on a neutral variable `t`.
- **Unsupported — Placing `sf_recall` or `sf_experiment` directly inside
  `.anneal/` crate proof files:** As established in Finding 5.1,
  `TrustedBoundary.inspectSource` enforces a closed `Init + Std` parser
  environment and a fixed 16-command syntax allowlist on all `.anneal/`,
  `trusted/lean/`, and `theory/` files; custom elaborator commands are rejected
  by design inside those directories.

## Evidence

### Primary Git Sources Examined

- **`plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257`):**
  - `lakefile.toml:1-106` (`SFLCompat` and `SFLMeta` library targets and
    generator executables).
  - `SFLCompat.lean:1-6`, `SFLCompat/Recall/Common.lean:1-153` (`declIds`,
    `declaredName`, `dedent`, `reindent`, `stripLeadingComments`,
    `replaceWithOriginalHint`, `sourceOf`, `sourceOfSyntax`),
    `SFLCompat/Recall/Check.lean:1-709` (`DeclId`, `tempDeclId`,
    `renameBackName`, `renameBack`, `renameBackInfoTree`, `checkTypesMatch`,
    `checkMatchCore`, `checkMatch`, `elabRecallCommand`, `elabRecallStatement`),
    `SFLCompat/Recall/Source.lean:1-131` (`sf_recall_source`), and
    `SFLCompat/Experiment.lean:1-252` (`commandWithoutAsync`,
    `withRestoringState`, `rawCommandBlock`, `runRawCmds`, `sf_experiment`,
    `sf_expect_failure_in`, `sf_expect_failure_in?`).
  - `SFLMeta/Basic.lean:1-171`, `SFLMeta/Solution.lean:1-273`,
    `SFLMeta/Exercise.lean:1-291`, `SFLMeta/Grade.lean:1-354`,
    `SFLMeta/Todo.lean:1-145`, `SFLMeta/Illuminate.lean:1-239`,
    `SFLMeta/Save/CodeBlock.lean:1-289`,
    `SFLMeta/Save/SourceRewrite.lean:1-194`, `SFLMeta/Save/Extract.lean:1-354`,
    `SFLMeta/Save/Lean.lean:1-273`, `SFLMeta/Save/Project.lean:1-88`, and
    `Targets.lean:1-60`.
- **`leanprover/verso` (`cad4b633e75ea769b851f12f9ca3b4f0dfcc625f`,
  `v4.34.0`):**
  - `src/verso-manual/VersoManual/InlineLean.lean:119-265` (`LeanBlockState`,
    sequential command elaboration across chapter code blocks, and
    `SubVerso.Highlighting.Code.highlight` invocation).
- **`leanprover/subverso` (`9b90b7f938d6169246325df002351014f49945ef`):**
  - `src/SubVerso/Highlighting/Code.lean:94-101, 471-505` (`HighlightState`,
    `VarTypeKey.fvar`, and `varTypes` hover type map) and
    `src/SubVerso/Highlighting/Highlighted.lean:1-280`.
- **`leanprover/illuminate` (`a1a61c9678da010e958ed24cdfa6f635b85f172a`):**
  - Animation specification and HTML widget integration consumed by
    `SFLMeta/Illuminate.lean`.
- **`joshlf/anneal` (`f938c18db56c49e82dde95506894a9b58b76b227` and Tutor branch
  `6b7c210c6c70f2f1710424dd07b4829742ff9154`):**
  - `trusted/audit/TrustedBoundary.lean:36-42, 129-140, 533-564`
    (`commandKinds`, `inspectSource`, `verifyAudit`).
  - `docs/tutor/README.md`, `docs/tutor/01-basic-usage-and-outputs.md` through
    `docs/tutor/06-agentic-proof-workflow.md`,
    `docs/tutor/workflow/README.md:107-155`,
    `docs/tutor/workflow/tutor_workflow.py:1-365`, and
    `docs/tutor/workflow/tutor.toml:1-416` on `6b7c210c`.
  - `trusted/lean/Trusted/Refinement.lean:51-55, 227-281`,
    `trusted/lean/Trusted/VerificationResult.lean:89-190`,
    `theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean:2156-2172`, and
    `tests/refinement/ConcreteYDiagram.lean:94-105` on `6b7c210c`.

### Preserved Package Artifacts

| Path | SHA-256 | Contents |
| :--- | :--- | :--- |
| `support/ProbeRecallAndMatcherExt.lean` | `855cd6e5df5b844d228b91a0c790b9efcb62939b5bbd0db16bc214fbb442c40f` | Self-contained Lean `v4.34.1` probe embedding `SFLCompat.Recall` (`sf_recall`, `sf_recall +strictUniverse`, `sf_recall statement`), positive/negative Anneal drift checks, unchecked metadata tests, all 5 matcher/cross-module `matcherExt` edge cases, and `sf_recall_fixed` (`renameExact` + `unfoldMatchersIn`). |
| `support/ProbeExperimentAndTutorAudit.lean` | `dd71a980db642a3ef2f774abe87b4aee74688135f86a24b03607ece66004f479` | Self-contained Lean `v4.34.1` probe embedding `SFLCompat.Experiment` (`sf_experiment`, `sf_expect_failure_in`, `rawCommandBlock`), `Elab.async` `snapshotTasks` verification, `withRestoringState` `ngen` `FVarId` collision reproduction and fix, Anneal Tutor (`6b7c210c`) unmanaged block drift audit, `Kernel.Environment.replay` (`Init + Std` only), and `TrustedBoundary.inspectSource` closed-parser check. |

## Revalidation

To revalidate Findings 2, 3, 4, and 5 on Lean `v4.34.1` (or test whether they
still hold on a newer Lean 4 toolchain), run the two self-contained support
probes directly from the package directory:

```console
lean --run reports/sf-in-lean-literate-verification-verso-and-anneal-tutor-2026/support/ProbeRecallAndMatcherExt.lean
lean --run reports/sf-in-lean-literate-verification-verso-and-anneal-tutor-2026/support/ProbeExperimentAndTutorAudit.lean
```

Both commands must exit with code `0` and print:

```text
=== ProbeRecallAndMatcherExt (Lean v4.34.1) ===
1. Positive matches (`sf_recall`, `sf_recall statement`, universe specialization): PASS
2. Unchecked metadata (`abbrev` vs `def`, field defaults/visibility, `theorem` as `def`): PASS
3. Negative drift checks (ctor order, field names, class vs structure, thm hyp, +strictUniverse): PASS
4. MatcherReuse in CrossModuleSim: earlierIsNil.match_1=true, laterIsNil.match_1=false
   Edge Case 1 (dangling .match_1): Unknown constant `ProbeRecallAndMatcherExt.AnnealSample.pairSumProj.match_1`
   Edge Case 5 (cross-module empty matcherExt): Unknown constant `ProbeRecallAndMatcherExt.CrossModuleSim.laterIsNil.match_1`
5. `sf_recall_fixed` (`renameExact` + `unfoldMatchersIn`) on Edge Cases 1, 2, 3, and 5: PASS
```

and:

```text
=== ProbeExperimentAndTutorAudit (Lean v4.34.1) ===
1. Environment rollback & Kernel.Environment.replay (Init+Std only): PASS (0 leaked constants, 159 TutorAudit decls replayed)
2. `commandWithoutAsync` verification: Elab.async=true spawned 2 background tasks (sync hasErrors=false); Elab.async=false spawned 0 tasks (sync hasErrors=true)
3. `withRestoringState` `ngen` collision: stock had 3 shared FVarIds across commands; `ngen`-preserving fix had 0 shared FVarIds
4. Anneal Tutor (`6b7c210c`) unmanaged block audit: passed 3 up-to-date blocks, caught 4 representative drifted blocks
5. `TrustedBoundary.inspectSource` closed parserEnv (Init+Std): pure Lean=Except.ok 3, custom `sf_recall`=Except.error (rejected as expected)
```
