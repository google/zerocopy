# Software Foundations in Lean 4: Operational Semantics, Hoare/WP Verification Conditions, Comparator Autograding, and Literate Verification

## Summary

### Part I — Adversarial Proof Grading (`comparator-autograder`), Match Splitter Deduplication, and `.olean` Realization Auditing

This report analyzes the five-component proof-auditing and autograding stack
used by `plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257`)—built
on `plclub/comparator-autograder` (`facc6c7498298d2286f18c9fc5eb5e902551b6aa`),
`plclub/comparator-autograder-lib` (`57f6879141b701cc02fe99d7a7e834c38409a6bc`),
`xhalo32/comparator` (`a6cc98304bd7f3ad3d030fc37a75e4b872342da6`), and
`leanprover/lean4export` (`076e8e57707e813375e8f9da8bf989799ace9680`)—and
compares its kernel-level invariants against Anneal's
`trusted/audit/TrustedBoundary.lean`
(`f938c18db56c49e82dde95506894a9b58b76b227`) on Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`).

Six technical findings govern how Lean `v4.34.1` pattern-match compilation and
on-demand theorem realization interact with both proof auditors:

1. **Why `xhalo32/comparator` (`a6cc983`) diverges from upstream
   `leanprover/comparator` (`d03acab`):** `xhalo32/comparator` adds two
   commits: `aa6ce7f` (moving `Main.lean` into `Comparator/MainSupport.lean` so
   `comparator-autograder` can invoke `Comparator.M.run compareIt` in-process)
   and `d6400b2` (passing `--ignore-missing` to `lean4export` in `safeExport`).
   Without `--ignore-missing`, `lean4export` calls `panic!` whenever any target
   in `exportTargets` is absent from `Solution` (such as an unattempted student
   exercise) or from a minimal import closure, and `safeExport`'s
   `LEAN_ABORT_ON_PANIC=1` turns that panic into a `SIGABRT` crash of the
   entire grading run.
2. **Three soundness and completeness flaws in `plclub/comparator-autograder`:**
   - **Adversarial `@[autogradedHole]` inductive spoofing (unsoundness):**
     `inductiveHoleMatches` (`ComparatorAutograder/Comparator.lean:70-72`)
     compares only `toConstantVal` (`name`, `levelParams`, `type`) and
     `isUnsafe`, ignoring `ctors`, `numParams`, `numIndices`, `isRec`, and
     `isReflexive`. Furthermore, `Compare.loop` (`Comparator.lean:107-110`)
     pushes only `solutionConst.type.getUsedConstants`—never constructor
     types—onto `compareWorklist`. Unless a graded theorem's statement
     explicitly mentions the inductive's constructors, a submission can replace
     an `@[autogradedHole] inductive Even : Nat → Prop` with
     `| cheat : ∀ n, Even n` (or reference tampered helper definitions inside
     constructor types) and pass kernel replay, axiom checking, and
     `Compare.loop`.
   - **Proof-irrelevant helper theorem rejection (incompleteness):**
     `Comparator/Util.lean:27` derives syntactic `BEq` on `ConstantInfo`, which
     compares `TheoremVal.value`. If a non-hole `def` references an earlier
     student-proved helper theorem (`sorry` in `Challenge`, proved in
     `Solution`), `addRelevantConsts` pushes that theorem onto
     `compareWorklist` and `Compare.loop` rejects it with `constDoesNotMatch`
     despite kernel proof irrelevance.
   - **Cross-chapter `@[autogradedHole]` blindness under
     `AUTOGRADER_SKIP_IMPORTS=true`:** `collectAutograded`
     (`ComparatorAutograder/MainSupport.lean:31`) skips imported modules before
     reading both `@[autogradedProof]` and `@[autogradedHole]`. In a
     multi-chapter Gradescope assignment (`CHAPTER=Basics,Induction`), graded
     chapters are staged from the `grading` variant (`sorry` in holes) in
     `Challenge/`, so any theorem in chapter $B$ referencing an
     `@[autogradedHole]` definition in graded chapter $A$ fails with
     `constDoesNotMatch`.
3. **Lean `v4.34.1` compiler mechanism behind the match deduplication hazard:**
   `Lean.Meta.Match.mkMatcherAuxDefinition`
   (`Lean/Meta/Match/Match.lean:1087-1126`) caches compiled match splitters in
   `matcherExt : EnvExtension (PHashMap MatcherKey Name)` (registered with
   `asyncMode := .local`), keyed by
   `{ value := result.value, compile, isPrivate }` after
   `Closure.mkValueTypeClosure` abstracts free variables and universe levels.
   Two `def`s in the same module—even in different namespaces (`NsA` vs. `NsB`)
   and with different return sorts (`: Bool` vs. `: Prop`, because
   `Closure.mkValueTypeClosure` generalizes the motive sort to
   `Sort.{u_2}`)—share the first declaration's `.match_1` constant when their
   constructor-splitting trees coincide. Under `-DElab.async=true`, theorem
   bodies elaborate on isolated async branches where `matcherExt` updates are
   discarded; under Anneal's `-DElab.async=false`, all theorems elaborate on
   the main branch and share `.match_1` splitters across theorems.
4. **Triple-compounding `.match_1` contamination bug in Anneal's
   `TrustedBoundary.lean` (`f938c18db` lines 658–1305) and verified fix:**
   When a `@[candidate <feat1>]` declaration (`candFn` / `candExtFn`) in a
   `Trusted.*` module elaborates a `match` expression before a `@[vetted]`
   (`vetFn` / `vetExtFn`) or `@[candidate <feat2>]` (`candFn2` / `candExtFn2`)
   declaration with the same splitter shape, three bugs compound:
   (a) `declarationEdges ci` (`line 919`) includes the self-edge
   `ci.all = [cName]`, causing `allVetted` and `onlyAllowedNonVetted`
   (`lines 1137–1143`) to evaluate to `false` on `dep = cName` so `autoHelpers`
   is empty even on extensible inductives; (b) non-extensible `.match_1`
   splitters (`touchesExtInduct == false`) are excluded from `autoHelpers` and
   keep `statusMap[cName] = "candidate:<feat1>"`, causing `line 1191` to reject
   all four downstream declarations; and (c) `collectActiveCandidateFeatures`
   (`line 1280`) checks `status.startsWith "candidate:"` before
   `else if autoHelpers.contains n` (`line 1289`), falsely activating
   `"<feat1>"` on `vetExtFn`. Filtering out `dep != cName && dep != parentName`
   in `isPureVettedMatcher`, classifying all pure vetted matchers into
   `autoHelpers`, and overriding their `statusMap` entry to `"vetted"` resolves
   all three failures while still rejecting genuinely contaminated `@[vetted]`
   declarations.
5. **Cross-boundary `Trusted.*` `realizeConst` rejection in
   `TrustedBoundary.lean` (`f938c18db` lines 366, 422–528, 1341–1365) and
   verified fix:** When untrusted modules (`TheoryA`, `TheoryB`) run `simp` or
   `fun_cases` on a `Trusted.*` function, Lean's on-demand `realizeConst`
   serializes 8 constants in the `Trusted` namespace into the consumer `.olean`
   files via `kenv.constants.foldStage2`, triggering line 1356 (`"non-Trusted
   module ... cannot declare constant ... in Trusted namespace"`) and sibling
   collision errors at lines 1346–1350. Because
   `_private.<Mod>.0.Trusted.<fn>.match_1.splitter` is a `.defnInfo`
   (`isTheorem == false`) and `Lean.isReservedName` returns `false` on all 5
   matcher-attached realized constants when `loadExts := false`, fixing this
   requires pairing a Phase 1 `inspectCommand` `Trusted` namespace block with
   the structural Phase 2 predicate `isRealizedCompilerConstant` +
   `sameRealizedThmHeader` (alongside changing `s[1].getArgs.isEmpty` to
   `s[1][0].getArgs.isEmpty` at line 366 to admit bare `by decide`).
6. **Implications for Anneal's module architecture and two-stage verification:**
   Because `matcherExt` is non-persistent (`asyncMode := .local`), matcher
   deduplication never crosses `.olean` module boundaries. Keeping generated
   specifications (`Mir.lean` / `Specs.lean`) in a separate module from
   `Proof.lean` isolates specifications from proof-side matcher deduplication,
   whereas any single-module `.olean` stubbing or diffing scheme must compare
   definitions up to kernel `isDefEq` rather than syntactic `ConstantInfo`
   `BEq`.

### Part II — Literate Verification (`SFLCompat`/`SFLMeta`, `Verso`/`SubVerso`/`Illuminate`), Declaration Drift Checking (`sf_recall`), and Anneal Tutor

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
4. **Live declaration drift caught in Anneal Tutor (`the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`):** Auditing all
   89 fenced code blocks across `docs/tutor/*.md` on Anneal Tutor commit
   `f938c18db56c49e82dde95506894a9b58b76b227 (with the 6-chapter ITree/Std Tutor specimen embedded in `support/ProbeExperimentAndTutorAudit.lean`)` ("Port six-chapter Anneal Tutor
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

### Part III — Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration (`inversion`), and `Plausible` Negative Canaries

This report analyzes the operational semantics, Hoare and weakest-precondition
verification condition (VC) generators, mutable-reference store-typing models,
and custom tactic elaborators in `plclub/sf-in-lean` (commit `13e9425b4647` and
PR #449 `0f74845c92a1`), alongside the labeled transition system (LTS)
simulation hierarchy in `leanprover/cslib` (commit `f7ec4db9f911`) and the
property-based random testing and constrained-generation framework in
`leanprover-community/plausible` (`v4.34.0`, commit `118aa17ee846` and PR #56
`f48022651ffa`). Every architectural pattern is evaluated against Anneal's MIR
semantics, verification building blocks, and kernel trust boundary
(`joshlf/anneal` commits `f938c18db56c`, `the PME MIR operational semantics prototype (`support/`)`, and `the Miri differential testing prototype (`support/`)`)
using two self-contained runnable Lean `v4.34.1` probes in `support/`.

Six technical findings govern how these mechanisms map to Anneal:

1. **Operational Semantics and Refinement (`HL/Slang.lean`, `HL/Imp.lean`,
   `HL/Equiv.lean`, `TS/Smallstep.lean`, `cslib` vs. Anneal MIR):** `sf-in-lean`
   and `cslib` formalize execution over unbounded syntax trees via relational
   big-step (`CEval : Com → State → State → Prop`) or small-step (`Step :
   Tm × Store → Tm × Store → Prop`, `LTS.Tr`) relations and symmetric
   observational equivalence (`cequiv c1 c2 := ∀ st st', CEval c1 st st' ↔
   CEval c2 st st'`). Anneal's MIR evaluator (`evalBlock`, `evalCall`,
   `evalBody` in `trusted/lean/Anneal/MirSemantics.lean`) is fuel-indexed and
   computational (`Option StepResult`), and its correctness contract is
   asymmetric undefined-behavior (UB) refinement (`StepResult.refines`,
   `Compiler.Verified`), where `none` (`OutOfFuel`) and `.unreachable`
   (`UndefinedBehavior`) are refined by any outcome. Symmetric `cequiv` holds
   only for total intra-CFG expression/statement rewrites
   (`optMirConstPropStmt`); all whole-body and interprocedural transformations
   must target asymmetric `StepResult.refines` (`PassPackage.sound`).
2. **Functional Induction (`fun_induction` / `fun_cases`) vs. Structural
   Induction on AST Passes (`optimizeAExp`, `optMirConstPropStmt`):** On an
   8-constructor recursive AST pass with wildcard fallthroughs (`optimizeAExp`),
   `symm; fun_induction optimizeAExp a <;> simp_all [AExp.eval]` reduces direct
   theorem DAG size by `91.1%` (`1,126` vs. `12,665` `Expr.numObjs` nodes) and
   marginal per-theorem kernel replay time by `66.1%` (`9,270 us` vs.
   `27,315 us`) relative to structural `induction`, while on a non-recursive
   4-level nested pattern match (`optMirConstPropStmt`), `fun_cases` reduces
   direct theorem DAG size by `77.2%` (`290` vs. `1,271` nodes). However,
   `fun_induction` and `fun_cases` pull the equation compiler's `.induct` /
   `.fun_cases` principle and `.match_N.splitter` theorem (`1,744`–`4,003`
   nodes) into the module closure (`21,381` vs. `24,660` total module-closure
   objects on a single theorem), amortizing after `K >= 2` theorems over the
   same function. Furthermore, recursive functions using overlapping wildcard
   match arms in Lean `v4.34.1` compile via well-founded recursion and emit an
   auxiliary `._unsafe_rec` constant in `.olean` stage 1, which
   `TrustedBoundary.lean` rejects inside `Anneal.*` (`trusted/lean/`) but
   permits in untrusted helper modules (`theory/`).
3. **Hoare Logic vs. Sparse Weakest-Precondition VC Generation (`HL/Hoare.lean`,
   `HL/Hoare2.lean`) and Transitive Axiom Closures of `omega`, `lia`, and
   `grind`:** `HL/Hoare2.lean`'s backward weakest-precondition generator
   (`SparseAnnotations.awp` + `verificationConditions`) eliminates intermediate
   assertions at sequential compositions (`seq`) and branches (`ite`), reducing
   proof-term DAG size by `3.2x` on a diamond CFG (`504` vs. `1,620` direct
   nodes) and `3.3x` on an 8-statement straight-line block (`2,535` vs. `8,379`
   direct nodes; `6.2x` faster marginal kernel replay). Crucially, discharging
   VCs via `omega`, `lia`, or `grind` introduces axioms outside
   `TrustedBoundary.lean`'s current two-axiom allowlist (`propext`,
   `Classical.choice`): `omega` on atomic `Nat` linear arithmetic
   (`omega_nat_add`, `omega_nat_sub`, `omega_nat_sub_fn`) depends on
   `#[propext, Quot.sound]` (via `Lean.Omega.combo_sat'` -> `funext` ->
   `Quot.sound`, `0` uses of `Classical.choice`), `omega` on a conjunction goal
   (`omega_nat_conj`) adds `Classical.choice` via `Classical.propDecidable`
   (`#[propext, Quot.sound, Classical.choice]`), and `lia` / `grind`
   unconditionally depend on all three standard axioms `#[propext, Quot.sound,
   Classical.choice]` (`1,388`–`2,673` reachable declarations).
4. **Mutable References and Store Typing (`TS/References.lean`) vs. Anneal's
   Fuel-Bounded Reference Invariants (`MirVal.satisfiesInv`):**
   `TS/References.lean` models mutable heap cells (`Store := List Tm`) via an
   extrinsic store typing context (`StoreTy := List Ty`) and monotonic extension
   (`Extends δ' δ := δ.IsPrefixOf δ'`). Because typing a location
   (`HasType.loc`) inspects `δ[l]? = some τ` without re-traversing `ρ[l]`,
   `STLCRef` proves type preservation for cyclic stores
   (`cyclic_store_well_typed` in `514` direct DAG nodes) via `store_weakening`
   (`180` nodes), `store_well_typed_alloc` (`584` nodes), and
   `assign_pres_store_typing` (`543` nodes). Anneal's
   `MirVal.satisfiesInv : Nat → Memory → MirVal → TyInv → Prop` evaluates
   nested `.ref loc` invariants by structural recursion on `fuel : Nat`;
   combining `StoreTy` (`RegionEnv : Loc → Option TyInv`) with monotonic frame
   extension (`RegionEnv.Extends`) removes the `fuel` bound and supports cyclic
   or long-lived reference graphs while embedding cleanly into `SparseDCom` VCs.
5. **Custom Tactic Elaboration (`LF/CustomTactics.lean`), `sf-in-lean` Issue
   #447 / PR #449, and `TrustedBoundary.lean` Compatibility:** Built-in `cases h`
   fails on dependent inductive predicates whose index is a computed function
   application (`ShiftStep (evalShift raw) out`) because
   `Lean.Meta.Cases.unifyEqs` throws a hard error when `unifyEq?` returns
   `none`, whereas `LF/CustomTactics.lean`'s `inversion` wraps `unifyEq?` in
   `observing?` and retains unsolved index equations (`evalShift raw = 0`) as
   local hypotheses. We diagnose the two-part root cause of `sf-in-lean` Issue
   #447 and PR #449 (`0f74845c`)—right-aligned backwards `renameInaccessibles`
   binding user names to trailing `eq✝`/`heq✝` equations on `main`, versus
   pre-unification `givenNames` consumed by unified-away implicit constructor
   parameters on `NoStutter` in PR #449—and implement a complete fix
   (`inversion_fixed`, `renameInversionFieldsForward`) that renames surviving
   `.fvar` entries in `CasesSubgoal.fields` in forward order after
   `unifyCasesEqs`. We also provide the 14-pattern `TrustedBoundary.lean` +
   `foundation-lock.json` compatibility matrix and identify a 1-character AST
   indexing bug in `TrustedBoundary.lean:366` (`s[1].getArgs.isEmpty` vs.
   `s[1][0].getArgs.isEmpty`) that rejects bare `by decide`.
6. **Property-Based Negative Canaries and Pre-Proof Specification Falsification
   (`plausible` `v4.34.0` + `Chamelean` PR #56):** `plausible` (`v4.34.0`)
   provides an out-of-TCB executable falsification layer that catches semantic
   mutants (`MirBinOp.shlUnchecked` missing UB guard, `MirBinOp.subChecked`
   off-by-one underflow flag) and flawed candidate lemma specifications
   (`alignUpBitwise` missing power-of-two or `UInt8` overflow guards) in
   `0.2`–`1.6 ms` per property. When testing sparse memory-frame invariants
   (`ValidFrame`), `Plausible`'s `@[instance 2000] subtypeVarTestable`
   intercepts `∀ f : MirFrame, ValidFrame f → P f` and dispatches to a
   `Chamelean`-style constrained generator
   (`SampleableExt { f // ValidFrame f }`), finding boundary bugs in `0.27 ms`
   where naive rejection sampling (`decGuardTestable`) gives up after `500`
   discarded samples. Finally, we expose a critical sizing pitfall in
   `Plausible/Arbitrary.lean`: `UInt8`..`UInt64` and `USize` cap random
   generation at `min (← getSize) MAX` (where default `maxSize = 100`), making
   default `plausible` runs completely blind to fixed-width arithmetic overflow
   above `100` unless overridden by a boundary-weighted full-range generator
   (`FullRangeUInt8`).

## Applicability

### Part I — Adversarial Proof Grading (`comparator-autograder`), Match Splitter Deduplication, and `.olean` Realization Auditing

The findings in this report apply to the exact repository revisions and
toolchain identified in `REPORT.json`:

- **`sf-in-lean` autograding stack:** `plclub/sf-in-lean` at commit
  `13e9425b4647402a09316c1d39fa555e9bc3c257`, `plclub/comparator-autograder` at
  commit `facc6c7498298d2286f18c9fc5eb5e902551b6aa`,
  `plclub/comparator-autograder-lib` at commit
  `57f6879141b701cc02fe99d7a7e834c38409a6bc`, `xhalo32/comparator` at commit
  `a6cc98304bd7f3ad3d030fc37a75e4b872342da6` (branch `ignore-missing-4.34.0`,
  forked from `leanprover/comparator` tag `v4.34.0` at commit
  `d03acab154d269c06e60e4de7e4cc85deebff94b`), and `leanprover/lean4export` at
  commit `076e8e57707e813375e8f9da8bf989799ace9680`.
- **Anneal boundary auditor:** `joshlf/anneal` at commit
  `f938c18db56c49e82dde95506894a9b58b76b227`
  (`trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`, and
  `trusted/lean/foundation-lock.json`).
- **Lean 4 toolchain and flags:** `leanprover/lean4` release `v4.34.1` (commit
  `5045d0056413266e57c625dcd7c365b10e377c52`) on `x86_64-unknown-linux-gnu`.
  Theorem-to-theorem `.match_1` deduplication (Finding 3) depends specifically
  on `-DElab.async=false` (passed by `cargo-anneal` in
  `trusted/audit/src/lib.rs`) versus Lean's default `-DElab.async=true`.
  `Lean.isReservedName` returning `false` on matcher-attached realized
  constants (Finding 5) depends specifically on `importModules` with
  `loadExts := false` (`TrustedBoundary.lean:160`).

### Part II — Literate Verification (`SFLCompat`/`SFLMeta`, `Verso`/`SubVerso`/`Illuminate`), Declaration Drift Checking (`sf_recall`), and Anneal Tutor

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
  `f938c18db56c49e82dde95506894a9b58b76b227 (with the 6-chapter ITree/Std Tutor specimen embedded in `support/ProbeExperimentAndTutorAudit.lean`)` (`docs/tutor/*.md`,
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

### Part III — Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration (`inversion`), and `Plausible` Negative Canaries

These findings apply directly to three subsystems in `joshlf/anneal`:

- **Trusted MIR Semantics and Boundary Auditor (`trusted/lean/Anneal/`,
  `trusted/audit/TrustedBoundary.lean`,
  `trusted/cargo-anneal/foundation-lock.json`):** Governs how MIR evaluation
  (`evalStmt`, `evalTerminator`, `evalBlock`, `evalBody`) and refinement
  (`StepResult.refines`, `Compiler.Verified`) are structured, why recursive
  functions with wildcard match arms (`._unsafe_rec`) must remain outside
  `trusted/lean/`, why `TrustedBoundary.lean:15–16` must add `Quot.sound` to
  `allowedAxioms` (and `Init.Omega` / `Init.Grind` / `Init.RCases` to
  `foundation-lock.json`) before generated or manual proofs can use `omega`,
  `lia`, or `grind`, and how to fix `TrustedBoundary.lean:366` so bare
  `by decide` passes source-syntax preflight.
- **Verification Building Blocks and Proof Automation
  (`theory/Anneal/Verification/`):** Guides the evolution of
  `BuildingBlocks.lean` (`BB-1`..`BB-8`) from per-block manual stepping to a
  hybrid `SparseDCom` weakest-precondition VC generator for acyclic basic-block
  sub-DAGs combined with cut-point invariants at loop headers, plus the adoption
  of `fun_induction` / `fun_cases` for MIR pass soundness proofs
  (`optMirConstPropStmt`) and `StoreTy` (`RegionEnv`) + `Extends`
  (`store_weakening`) for mutable-reference invariant preservation.
- **Negative-Canary and Specification-Falsification Test Suite (`tests/` and
  `theory/` development workflows):** Establishes how `plausible` (`v4.34.0`)
  and `Chamelean`-style `SampleableExt { x // P x }` generators can falsify
  semantic mutants (Issue #228 / PR #82) and candidate `theory/Anneal/`
  specifications before investing in Lean kernel proofs or full Cargo/Miri
  differential builds.

### Inlined Core Anneal Refinement and MIR Semantic Definitions

To keep this reference self-contained without depending on unmerged prototype branches or external worktrees, the exact Lean 4 definitions of the core refinement, small-step machine, ADT invariant admissibility, interprocedural call, boolean AST equality, and crate-level verification judgments referenced across this report are reproduced below (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `theory/Anneal/MirLemmas.lean`):

```lean
/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` exactly when the computation exhibits undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language with program-indexed initial-state domain `dom`. -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  sem   : Prog → Behavior Query Out
  dom   : Prog → Query → Prop

/-- Domain-intersected precondition non-vacuity: some query is in `dom` *and*
satisfies `pre`. There is deliberately no "or `dom` is empty" alternative: an
empty domain is how a model limit at function entry shows up, so accepting it
would turn every such limit into vacuous verification. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against
`(pre, post)` within `prog`'s own domain `L.dom prog`. -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation with private constructor. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Obligation representing an explicit, unproved assumption (`prop := False`)
that can only be discharged when `id` appears in the crate's `waived` TCB list. -/
abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

/-- Waiver-aware verification judgment requiring distinct obligation IDs,
distinct waivers permitted by `policy`, and discharge of all unwaived obligations. -/
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))
```

```lean
/-- Admissibility of an ADT representation invariant `adtInv`
(`r[expr.struct.safety]`, `src/expressions/struct-expr.md`).
If safe code can build a struct directly (all fields public and safe), the
invariant must accept every structurally valid payload, in every state. -/
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (s : MirState) (payload : MirTy) (inner : MirVal),
      decl.payloadTy = some payload →
      inner.valid adts defaultAdtInv s 0 payload →
      adtInv decl.id inner

/-- Lowered MIR block terminators, including static single-argument calls
`Terminator.call1` referencing a `BodyId` in `Crate.bodies` (or a nested
`MirBody` in the recursive first-order variant). -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | panic
  | unwindResume
  | unwindTerminate
  | drop (place : Place) (target : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | switchIntGeneral (discr : Operand) (targets : List (Nat × BlockId))
      (otherwise : BlockId)
  | callSizeOf (dst : Place) (ty : MirTy) (target : BlockId)
  | callTransmuteCopy (dst : Place) (srcTy dstTy : MirTy) (op : Operand)
      (target : BlockId)
  | call1 (dst : Place) (callee : BodyId) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy := [])
  | call (dst : Place) (args : List Operand) (target : Option BlockId)
  | tailCall (args : List Operand)
  | yield (val : Operand) (resume : BlockId) (resumeArg : Place)
  | coroutineDrop
  | falseEdge (realTarget : BlockId) (imaginaryTarget : BlockId)
  | falseUnwind (realTarget : BlockId)
  | inlineAsm

/-- Per-function obligation inventory under `adts`, `bodies`, and `adtInv`. -/
def CapturedFn.obligations (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) : List (Obligation TCBItem) :=
  [
    Obligation.assumed (TCBItem.rustcLowering fn.name fn.bodyId),
    Obligation.wellFormedAndSpecsOn (TCBItem.fnVerified fn.name fn.bodyId)
      (MirLang adts bodies) (fn.effectivePre adts bodies adtInv)
      (fn.effectiveSpecs adts bodies adtInv) (fn.resolveBody bodies)
  ]

/-- Top-level theorem required of every verified Rust crate. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResult defaultTrustPolicy c.tcb
      (fn.obligations c.adts c.bodies c.adtInv)))
```

```lean
/-- Fuel-bounded structural boolean equality on recursive `MirBody` trees
(before flat `BodyId` indirection). -/
noncomputable def beqMirBodyFuel : Nat → MirBody → MirBody → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    listBeq beqMirTy a.argTys b.argTys &&
    beqMirTy a.retTy b.retTy &&
    a.localCount == b.localCount &&
    listBeq (beqBasicBlock (beqMirBodyFuel fuel)) a.blocks b.blocks &&
    listBeq (beqRcPair (beqMirBodyFuel fuel)) a.requiredConsts b.requiredConsts

/-- Fuel-free structural boolean equality on `MirBody`, enabled by flat `BodyId`
indirection in `Crate.bodies`. -/
def beqMirBody (a b : MirBody) : Bool :=
  listBeq beqMirTy a.argTys b.argTys &&
  beqMirTy a.retTy b.retTy &&
  a.localCount == b.localCount &&
  listBeq beqBasicBlock a.blocks b.blocks &&
  listBeq beqRcPair a.requiredConsts b.requiredConsts
```

## Findings

### Part I — Adversarial Proof Grading (`comparator-autograder`), Match Splitter Deduplication, and `.olean` Realization Auditing

#### Finding 1: Architecture of the 5-Component `sf-in-lean` Autograding Pipeline, `xhalo32/comparator` (`ignore-missing-4.34.0`) vs. Upstream `leanprover/comparator`, and `gradescope/grade.py` Dual-Tree Staging

`Basis: source + derived`

##### 1.1 Pipeline Component Roles

The `sf-in-lean` grading stack spans five repositories:

| Component | Revision | Role in Pipeline |
| :--- | :--- | :--- |
| `plclub/sf-in-lean` | `13e9425b4647402a09316c1d39fa555e9bc3c257` | Verso book source (`LF/`, `HL/`, `TS/`), variant extractor (`SFLMeta/Save/Extract.lean`), local verifier (`scripts/grading_check.py`), and Gradescope harness (`gradescope/`). |
| `plclub/comparator-autograder-lib` | `57f6879141b701cc02fe99d7a7e834c38409a6bc` | Defines `@[autogradedProof <rat>]` and `@[autogradedHole]` parametric attributes (`ComparatorAutograderLib.lean:1-48`). |
| `plclub/comparator-autograder` | `facc6c7498298d2286f18c9fc5eb5e902551b6aa` | Discovers graded attributes in `Challenge`, invokes `Comparator.M.run compareIt`, and grades each theorem independently (`ComparatorAutograder/Comparator.lean:1-185`). |
| `xhalo32/comparator` | `a6cc98304bd7f3ad3d030fc37a75e4b872342da6` | Fork of `leanprover/comparator` (`ignore-missing-4.34.0` branch) providing `landrun`-sandboxed `lake build` and `lean4export` execution plus in-process `Lean.Kernel.Environment.replay`. |
| `leanprover/lean4export` | `076e8e57707e813375e8f9da8bf989799ace9680` | Imports `.olean` modules via `Lean.importModules` and serializes target constants and their transitive closures into NDJSON (`Export.lean:1-438`). |

##### 1.2 Exact Diff in `xhalo32/comparator` (`a6cc983`) vs. Upstream `leanprover/comparator` (`d03acab`)

Comparing `xhalo32/comparator` (`a6cc98304bd7f3ad3d030fc37a75e4b872342da6`)
against upstream `leanprover/comparator`
(`d03acab154d269c06e60e4de7e4cc85deebff94b`, tag `v4.34.0`) shows that
`xhalo32/comparator` contains two non-merge commits on top of upstream
(`aa6ce7f` and `d6400b2`), merged forward into `v4.34.0-rc2` (`9da7405`) and
`v4.34.0` (`a6cc983`):

1. **Commit `aa6ce7f0216676a1c5c07f1bbdd0df0b0045a150`
   (`feat: refactor Main to MainSupport`):**
   - Moves all types and functions from `Main.lean` (`Config`, `Context`, `M`,
     `LandrunArgs`, `buildLandrunArgs`, `runSandBoxedWithStdout`,
     `runSandBoxed`, `safeLakeBuild`, `safeExport`, `runBuiltinKernel`,
     `primitiveTargets`, `builtinTargets`, `compareIt`, `M.run`) into
     `Comparator/MainSupport.lean:1-361` and re-exports `Comparator.MainSupport`
     from `Comparator.lean:1-4`.
   - Leaves a 14-line CLI wrapper in `Main.lean`, allowing
     `plclub/comparator-autograder` to `import Comparator` and call
     `Comparator.M.run compareIt` in-process (`Main.lean:21`).
2. **Commit `d6400b2df61de027dea8697508ea2eed4efcc785`
   (`Add --ignore-missing to lean4export`):**
   - In `Comparator/MainSupport.lean:131`, changes `safeExport` from upstream's
     `let baseArgs := #[module.toString, "--"]` to:
     ```lean
     let baseArgs := #["--ignore-missing", module.toString, "--"]
     ```

In `leanprover/lean4export` (`Export.lean:232-238`, added in commit
`d17578b17b86a30986e4536284c32e90b9b52812`), `dumpConstant` looks up each
requested constant `c` in `(← read).env.find? c`:

```lean
partial def dumpConstant (c : Name) : M Index :=
  mmodifyGet (·.visitedConstants) fun (c : Name) => do
    let some declar := (← read).env.find? c
      | if (← get).ignoreMissing then return 0 else panic! s!"Constant {c} not found in environment."
```

Because `safeExport` (`Comparator/MainSupport.lean:140`) runs `lean4export`
with `LEAN_ABORT_ON_PANIC=1`, any `panic!` triggers `abort()` (`SIGABRT`, exit
code 134). Both `comparator` (`Comparator/MainSupport.lean:337-340`) and
`comparator-autograder` (`ComparatorAutograder/Comparator.lean:179-181`) pass
the same `exportTargets` array to `safeExport challengeModule exportTargets`
and `safeExport solutionModule exportTargets`:

```lean
let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
  ++ (← primitiveTargets) ++ (← getDefinitionNames)
```

Without `--ignore-missing`, `lean4export` aborts the entire grading process in
two situations:

1. **Missing student declarations in `solutionModule`:** If a student omits,
   comments out, or misnames any exercise in `theoremNames` or
   `definitionNames`, `safeExport solutionModule` aborts with `SIGABRT` before
   `myVerifyMatch` can grade the remaining exercises and report
   `constNotFoundInSolution` on the missing one.
2. **Unimported primitives in `primitiveTargets` / `builtinTargets`:** Upstream
   commit `2312244ac716564a61cc0bf4e107d9abf1757a61` expanded
   `primitiveTargets` to 31 constants (including `String.ofList`, `Char.ofNat`,
   `Nat.gcd`, `eagerReduce`, `optParam`, `autoParam`, `semiOutParam`, and
   `outParam`), plus `Quot` and `Classical.choice` in `builtinTargets` /
   `legalAxioms`. Any minimal or `prelude` challenge module that does not
   transitively import all 31 constants triggers a panic in `lean4export`
   unless `--ignore-missing` is active.

When `--ignore-missing` is enabled, `dumpConstant` returns index `0` and omits
the declaration record (`#ax`/`#def`/`#thm`/`#ind`) from the NDJSON stream
while still serializing `Expr.const c us` references via `dumpName`. If a
missing constant is referenced inside a student's proof term,
`Export.parseStream` reconstructs `Expr.const c us` in the expression table
while leaving `c` absent from `solution.constMap`, so `runBuiltinKernel
solution` (`env.toKernelEnv.replay`) still rejects the proof with a kernel
`UnknownConstant` error.

##### 1.3 Attribute Extraction and Per-Theorem Grading Flow

1. `ComparatorAutograderLib.lean` (`57f6879`, lines 1–48) registers
   `autogradedProofAttr : ParametricAttribute Rat` (`@[autogradedProof ptVal]`)
   and `autogradedHoleAttr : ParametricAttribute Unit` (`@[autogradedHole]`).
   Permitted axioms are hardcoded in `comparator-autograder/Main.lean:26` as
   `#["propext", "Classical.choice", "Quot.sound"]`.
2. In `sf-in-lean`, chapters use Verso block directives
   `:::gradeTheorem <pts> <names...>` and `:::autogradedHole <names...>`
   (`SFLMeta/Grade.lean:1-110`). `SFLMeta/Save/Extract.lean` (lines 627–634 and
   691–696) extracts four Lean variants (`student`, `solutions`, `terse`,
   `grading`): `solution!` blocks become `sorry` in `student`, `terse`, and
   `grading` (since `sf-in-lean` commit `5e5b229`), and only `grading` prepends
   `import ComparatorAutograderLib` and emits the `attribute [autogradedProof
   <pts>]` and `attribute [autogradedHole]` commands.
3. `comparator-autograder` (`Main.lean:13-43`, `MainSupport.lean:23-54`) builds
   `challengeModule` under `COMPARATOR_LANDRUN`, imports it in-process, and
   collects attributes via `collectAutograded`:
   ```lean
   for (name, _) in env.constants do
     let name ← try Elab.realizeGlobalConstNoOverloadWithInfo (mkIdent name)
                catch _ => continue
     let some modIdx := env.getModuleIdxFor? name | continue
     let mod := env.allImportedModuleNames[modIdx]!
     if config.skipImports && mod != config.challengeModule.toName then continue
     if let some pts := autogradedProofAttr.getParam? env name then
       proofs := proofs.push ({ const := name, mod }, pts)
     if let some () := autogradedHoleAttr.getParam? env name then
       holes := holes.push { const := name, mod }
   ```
   *(Passing `mkIdent name` to `realizeGlobalConstNoOverloadWithInfo` in an
   empty `CoreM` namespace context works for fully qualified names, but
   silently drops any constant whose name is overloaded or cannot be resolved
   as a global identifier.)*
4. `Comparator.M.run compareIt` (`ComparatorAutograder/Comparator.lean:143-184`)
   builds and exports `challengeModule` and `solutionModule` under `landrun`,
   parses both NDJSON streams into `Export.ExportedEnv`, replays `solution` in
   `mkEmptyEnvironment` via `runBuiltinKernel solution`
   (`Comparator/MainSupport.lean:177-214`), and runs `compareTheoremAt` over
   `theoremNames`. If a theorem succeeds, `compareChecked` and `axiomsChecked`
   are cached in `st`; if it fails, `st` is rolled back to its pre-theorem
   state.

##### 1.4 Dual-Tree Staging and Per-Chapter Recovery in `gradescope/grade.py`

1. **Dual-tree namespaced staging (`package.py:115-187`,
   `grade.py:165-169`):** `package.py` constructs a single Lake workspace with
   two parallel module trees—`Challenge/<VOLUME>/<Chapter>.lean` and
   `Solution/<VOLUME>/<Chapter>.lean`—plus a shared `SFLCompat/`.
   `grade.rewrite(text, side)` rewrites `^import (LF|HL|TS).<Mod>` to
   `import Challenge.<VOL>.<Mod>` or `import Solution.<VOL>.<Mod>` without
   rewriting internal `namespace LF.<Chapter>` declarations, so both trees emit
   constants with identical Lean `Name`s (`LF.Basics.nand`, etc.) in separate
   `.olean` files. Graded chapters use `grading` on the `Challenge` side and
   `student` on the `Solution` side; ungraded chapters use `solutions` on both
   sides (`package.py:123-127`) so imported definitions match and do not
   introduce `sorryAx`.
2. **Fast-path build and per-chapter fallback (`grade.py:180-335`):**
   `grade.py` copies submitted chapters from `/autograder/submission/` into
   `Solution/<VOLUME>/<c>.lean` (ignoring unconfigured filenames) and attempts a
   combined `lake build` (`grade.py:296`). If that build fails,
   `grade.py:303-320` iterates over each graded chapter `c`: it restores the
   student's `Solution/<VOLUME>/<c>.lean`, resets all other failed chapters to
   their `template/` (`student`) skeletons, calls `clean_build_state()`
   (`grade.py:137-162`, deleting `.lake/build/lib/lean/Solution` and
   `lakefile.olean*` while preserving `Challenge`, `SFLCompat`, and
   `.lake/packages`), restricts `defaultTargets` in `lakefile.toml` to
   `["Challenge.<V>.<c>", "Solution.<V>.<c>"]`, and reruns `lake build`
   followed by `lake env comparatorautograder` with
   `AUTOGRADER_SKIP_IMPORTS=true`.

---

#### Finding 2: Three Soundness and Completeness Flaws in `plclub/comparator-autograder` (`@[autogradedHole]` Inductive Constructor Spoofing, Non-Hole Helper Theorem Rejection, and Cross-Chapter Hole Blindness Under `AUTOGRADER_SKIP_IMPORTS=true`)

`Basis: source + execution + derived`

##### 2.1 Unsoundness of `@[autogradedHole]` on `inductive` Declarations

Commit `9c9c8f8` in `plclub/comparator-autograder` added `@[autogradedHole]`
support for `inductive` declarations (upstream `leanprover/comparator` supports
only `.defnInfo` holes). In `ComparatorAutograder/Comparator.lean:70-72`,
`inductiveHoleMatches` checks only `toConstantVal` and `isUnsafe`:

```lean
def inductiveHoleMatches (challengeHole solutionHole : InductiveVal) : Bool :=
  challengeHole.toConstantVal == solutionHole.toConstantVal &&
  challengeHole.isUnsafe == solutionHole.isUnsafe
```

This check ignores `ctors`, `numParams`, `numIndices`, `isRec`, and
`isReflexive`. Furthermore, at lines 107–110 (where an inline source comment
questions whether `getUsedConstants` suffices for inductives), `Compare.loop`
pushes only `solutionConst.type.getUsedConstants` onto `compareWorklist`,
never the inductive's constructors (`iv.ctors`) or the constants referenced in
constructor types:

```lean
for c in solutionConst.type.getUsedConstants do
  addCompareWorklist c
```

As verified in `support/ProbeComparatorAndMatcherDedup.lean` (Section 2A):

- **Constructor spoofing:** For any exercise where the student fills in an
  `@[autogradedHole] inductive Even : Nat → Prop` and proves a theorem
  `theorem even_four : Even 4` whose statement does not mention `Even`'s
  constructors (such as `inductive_hole3` and `inductive_hole4` in
  `comparator-autograder`'s test suite, or relational holes in `sf-in-lean`), a
  submission can define `| cheat : ∀ n, Even n` and prove `even_four :=
  Even.cheat 4`. `inductiveHoleMatches` returns `true`, `Compare.loop` pushes
  only `#[Nat]` onto `compareWorklist`, `Axioms.loop` finds zero axioms, and
  `Kernel.Environment.replay` accepts the spoofed inductive and theorem.
- **Unchecked helper tampering inside constructor types:** Even if a constructor
  type references a non-hole helper definition `H` that the student altered in
  `Solution`, `Compare.loop` never visits `iv.ctors` and therefore never
  compares `H` against `Challenge` unless `H` is also referenced outside the
  inductive's constructors.

##### 2.2 Incompleteness on Student-Proved Helper Theorems Referenced by Non-Hole Definitions

`Comparator/Util.lean:18-30` derives syntactic `BEq` on `ConstantInfo`, under
which two `.thmInfo` constants are equal only if their proof terms
(`TheoremVal.value`) are syntactically identical. While `compareTheoremAt`
(`Comparator.lean:119-141`) pushes only a graded theorem's `type` onto
`compareWorklist`, any non-hole `def` popped by `Compare.loop`
(`Comparator.lean:111-114`) requires `challengeConst == solutionConst` and calls
`addRelevantConsts solutionConst` (`runForUsedConsts`, pushing all constants
referenced in both `type` and `value`).

As verified in `support/ProbeComparatorAndMatcherDedup.lean` (Section 2B), if a
student proves a helper theorem `helper_lemma` (`sorry` in `Challenge`, proved
in `Solution`) and a subsequent non-hole `def` references `helper_lemma` in its
body (for example, in an array-bounds or well-founded termination proof),
`Compare.loop` pushes `helper_lemma` onto `compareWorklist` and rejects it with
`constDoesNotMatch` even though Lean's kernel treats `TheoremVal` as
proof-irrelevant. Marking `helper_lemma` with `@[autogradedHole]` (as done on
three theorems in `sf-in-lean/TS/MoreStlc.lean:2967,3043,3125`) does not solve
this: if `Compare.loop` ever pops a `.thmInfo` that is in `holes`, line 102
throws `bug "Hole in challenge is neither a definition nor an inductive"`.

##### 2.3 Cross-Chapter `@[autogradedHole]` Blindness Under `AUTOGRADER_SKIP_IMPORTS=true`

`AUTOGRADER_SKIP_IMPORTS=true` restricts `collectAutograded`
(`ComparatorAutograder/MainSupport.lean:31`) so that `@[autogradedProof]` and
`@[autogradedHole]` attributes are collected only from `challengeModule`
itself, not from its transitive imports. While `Compare.loop` still walks the
full cross-module transitive closure exported by `lean4export` (catching any
tampered non-hole definition in an imported module), skipping imports before
reading `autogradedHoleAttr` breaks cross-chapter holes in multi-chapter
Gradescope assignments (`CHAPTER=Basics,Induction`): because both chapters are
staged in `Challenge/LF/` from the `grading` variant (`sorry` in holes),
grading `Challenge.LF.Induction` with `AUTOGRADER_SKIP_IMPORTS=true` omits all
`@[autogradedHole]` declarations in `Challenge.LF.Basics` from `holes` and
rejects any theorem in `Induction` that depends on a hole definition from
`Basics` with `constDoesNotMatch`.

---

#### Finding 3: Lean `v4.34.1` Compiler Mechanism Behind the Match Deduplication Hazard (`MatcherKey`, `Closure.mkValueTypeClosure`, and `matcherExt` `asyncMode := .local` Under `-DElab.async=false` vs. `true`)

`Basis: source + execution`

##### 3.1 `MatcherKey` and `Closure.mkValueTypeClosure` in `Lean/Meta/Match/Match.lean`

When Lean elaborates a `match` expression (`Lean.Elab.Term.elabMatchAux`,
`Lean/Elab/Match.lean:1158-1161`), it generates a candidate auxiliary name via
`let matcherName ← mkAuxName `match` (producing `<currentDecl>.match_1`) and
invokes `Meta.Match.mkMatcher`, which delegates matcher constant creation to
`mkMatcherAuxDefinition` (`Lean/Meta/Match/Match.lean:1074-1126`):

```lean
private structure MatcherKey where
  value : Expr
  compile : Bool
  isPrivate : Bool
  deriving BEq, Hashable

private builtin_initialize matcherExt : EnvExtension (PHashMap MatcherKey Name) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

def mkMatcherAuxDefinition (name : Name) (type : Expr) (value : Expr)
    (isSplitter := false) : MetaM (Expr × OptionMatcherInfo) := do
  let compile := !isSplitter && (← canCompile value)
  let result ← Closure.mkValueTypeClosure type value (zetaDelta := false)
  let env ← getEnv
  let mkMatcherConst name :=
    mkAppN (mkConst name (result.levelArgs.map mkLevelParam)) result.exprArgs
  let key := { value := result.value, compile,
               isPrivate := env.header.isModule && isPrivateName name }
  if let some nameNew := (matcherExt.getState env).find? key then
    return (mkMatcherConst nameNew, none)
  ...
  modifyEnv fun env => matcherExt.modifyState env (·.insert key name)
```

Four properties of `mkMatcherAuxDefinition` govern when two declarations share
a `.match_1` constant (mechanically verified in
`support/ProbeComparatorAndMatcherDedup.lean`, Sections 1A and 1B):

1. **`MatcherKey` is independent of declaration name and namespace:** `key`
   contains only `{ value := result.value, compile, isPrivate }`. The candidate
   `name` (`<currentDecl>.match_1`) is used only when `key` is absent from
   `matcherExt`. Consequently, `NsB.secondMatch` reuses
   `NsA.firstMatch.match_1` across disjoint namespaces.
2. **`Closure.mkValueTypeClosure` abstracts both parameters and motive universe
   levels:** For any inductive type in `Type u` whose `casesOn` eliminator
   targets an arbitrary universe `Sort v` (such as `List`, `Option`, `Nat`,
   `Bool`, or `Except`), `result.value` is closed over both the type parameters
   and the motive's universe level `u_2`:
   ```lean
   fun {α : Type.{u_1}} (motive : List.{u_1} α → Sort.{u_2}) (xs : List.{u_1} α)
       (h_1 : Unit → motive []) (h_2 : ∀ head tail, motive (head :: tail)) =>
     List.casesOn.{u_2, u_1} α (fun x => motive x) xs (h_1 ()) (fun head tail => h_2 head tail)
   ```
   Because `Expr` equality (`BEq`) ignores binder names (`xs` vs. `l`), any two
   `match` expressions in the same module with the same constructor-splitting
   tree over the same inductive type produce the exact same `result.value`—even
   when one `def` returns `Bool` (`Type 0`, `u_2 = 1`) and the other returns
   `Prop` (`Sort 0`, `u_2 = 0`), as demonstrated by
   `MitigationSort.firstBoolMatch` and `MitigationSort.secondPropMatch` both
   reusing `NsA.firstMatch.match_1`. By contrast, rewriting `match` as
   `if l.isEmpty then ... else ...` (`MitigationIte.firstIte`) elaborates via
   `ite` without touching `matcherExt`.
3. **`asyncMode := .local` makes theorem-to-theorem deduplication depend on
   `-DElab.async`:** Because `matcherExt` is registered with
   `asyncMode := .local` (`Lean/Environment.lean:1271-1278`), state updates on
   asynchronous environment branches (`AddConstAsyncResult.asyncEnv`) are
   discarded. Under Lean's default `-DElab.async=true`, `theorem` bodies
   elaborate on async branches and generate distinct matchers
   (`ThmVsDef.thmWithMatch.match_1_1` and `ThmVsDef.thm2WithMatch.match_1_1`).
   Under `-DElab.async=false` (used by Anneal), all `theorem` bodies elaborate
   on the main environment branch and share `ThmVsDef.thmWithMatch.match_1`.
4. **Why `sf-in-lean` fails on `List.IsNil` and `List.In`:** In `Template`
   (`grading`/`student`), `List.IsNil` is `sorry`, so `List.In` is the first
   `match` on `List α` and generates `LF.Poly.List.In.match_1` (referenced by
   `LF.Poly.List.In._f`, `_sunfold`, and `_unsafe_rec`). In `Submission`
   (`solutions`), `List.IsNil` elaborates `match l with | [] => True | _ :: _
   => False`, registering `LF.Poly.List.IsNil.match_1` in `matcherExt`; when
   `List.In` elaborates next, `mkMatcherAuxDefinition` reuses
   `LF.Poly.List.IsNil.match_1` inside `LF.Poly.List.In._f` and never creates
   `LF.Poly.List.In.match_1`. Both matchers carry `ReducibilityHints.abbrev`
   and identical types and bodies, so `Kernel.isDefEqGuarded` equates
   `Template`'s and `Submission`'s `LF.Poly.List.In._f` values (`true`), yet
   `Comparator`'s syntactic `challengeConst == solutionConst` check evaluates
   to `false` and rejects `LF.Poly.List.In._f` with `constDoesNotMatch`.

---

#### Finding 4: Triple-Compounding `.match_1` Contamination Bug in Anneal's `TrustedBoundary.lean` (`f938c18db` Lines 658–1305) Across `@[candidate]` and `@[vetted]` / `@[candidate <feat2>]` Declarations and Verified Fix (`isPureVettedMatcher`)

`Basis: source + execution`

##### 4.1 Three Compounding Bugs in `TrustedBoundary.lean` (`f938c18db`)

In `trusted/audit/TrustedBoundary.lean` (`f938c18db`, lines 1011–1018),
`classifyTrustedConstant` assigns trust status to compiler-generated helpers
(`.match_1`, `._f`, `._sunfold`) by walking name prefixes until it reaches an
explicit declaration in `declMap`. When a `@[candidate <feat1>]` declaration in
a `Trusted.*` module (`candFn` on non-extensible `PureInd`, or `candExtFn` on
extensible `ExtInd`) elaborates before a `@[vetted]` declaration (`vetFn` /
`vetExtFn`) or a `@[candidate <feat2>]` declaration (`candFn2` / `candExtFn2`)
with the same match splitter shape, Lean deduplicates the splitter under
`candFn.match_1` / `candExtFn.match_1`, which `classifyTrustedConstant` labels
`"candidate:<feat1>"`. Running stock `checkTrustedNonContamination` and
`collectActiveCandidateFeatures` (`support/ProbeTrustedBoundaryFixes.lean`,
Section 1) exposes three compounding defects:

1. **Self-edge in `declarationEdges ci` defeats `allVetted` and
   `onlyAllowedNonVetted` (`line 919` and `lines 1124–1150`):**
   `declarationEdges ci` (`line 919`) includes `result := result ++ .ofList
   ci.all`, which for any definition `cName` is `[cName]`. At lines 1136–1143,
   `checkTrustedNonContamination` computes:
   ```lean
   let allVetted :=
     deps.toList.all fun dep => (statusMap.getD dep "vetted") == "vetted"
   let onlyAllowedNonVetted :=
     allVetted ||
       (elimStatuses.contains parentName &&
         deps.toList.all fun dep =>
           (statusMap.getD dep "vetted") == "vetted" ||
             allowedInInductHelperOwners.contains (ownerMap.getD dep dep))
   ```
   When `cName = Trusted.MatchProbe.candExtFn.match_1` (owned by
   `@[candidate mir_semantics] def candExtFn`), `cName ∈ deps` has
   `statusMap[cName] = "candidate:mir_semantics"` and
   `ownerMap[cName] = Trusted.MatchProbe.candExtFn`. Because `candExtFn` is a
   function definition (`defnInfo`) rather than an inductive or constructor in
   `allowedInInductHelperOwners`, both `allVetted` and `onlyAllowedNonVetted`
   evaluate to `false` on `dep = cName` itself. Consequently, `isExtSplitter`
   is `false` and `autoHelpers` is empty even for `candExtFn.match_1` on an
   extensible inductive in `extensibleInducts`.
2. **Non-extensible splitter exclusion and un-updated `statusMap`
   (`lines 1149, 1188–1191`):** For non-extensible inductives (`PureInd`),
   `touchesExtInduct` is `false`, so `candFn.match_1` is excluded from
   `autoHelpers`. For both `PureInd` and `ExtInd`, `extractScopedEdges`
   (`lines 869, 884`) records the shared `.match_1` constant in
   `valEdges.unguarded`. Because `statusMap` still maps `candFn.match_1` and
   `candExtFn.match_1` to `"candidate:mir_semantics"`, line 1191
   (`if depStatus != "vetted" && depStatus != selfStatus`) falsely rejects all
   four downstream declarations (`vetFn`, `candFn2`, `vetExtFn`, and
   `candExtFn2`).
3. **Inverted branch order in `collectActiveCandidateFeatures`
   (`lines 1280–1292`):** Even if `candExtFn.match_1` is manually inserted into
   `autoHelpers`, `collectActiveCandidateFeatures` checks
   `if status.startsWith "candidate:"` (`line 1280`) before
   `else if autoHelpers.contains n` (`line 1289`). Reaching
   `candExtFn.match_1` from `@[vetted] vetExtFn` therefore takes the first
   branch and falsely reports `"mir_semantics"` as an active candidate feature.

##### 4.2 Verified Fix: `isPureVettedMatcher` and `statusMap` Override

As verified in `support/ProbeTrustedBoundaryFixes.lean` (Section 1), replacing
the inline `isExtSplitter` check with a fixed-point pre-pass over
`isPureVettedMatcher` that:

1. Filters out self-references (`let nonSelfDeps := deps.toList.filter fun dep
   => dep != cName && dep != parentName`) before evaluating `allVetted` and
   `onlyAllowedNonVetted`;
2. Drops the `touchesExtInduct` restriction for `allVetted` matchers while
   retaining `touchesExtInduct && elimStatuses.contains parentName` for
   extensible-inductive matchers whose dependencies are in
   `allowedInInductHelperOwners`; and
3. Inserts every `isPureVettedMatcher` constant into `autoHelpers` and
   overrides its `statusMap` entry to `"vetted"` (returning the updated
   `statusMap` to `collectActiveCandidateFeatures`)

eliminates all four false rejections (`vetFn`, `candFn2`, `vetExtFn`,
`candExtFn2`), yields `#[]` active candidate features for `#[vetFn, vetExtFn]`,
yields `#["mir_semantics"]` for `#[candFn]` and `#["memory"]` for `#[candFn2,
candExtFn2]`, and still rejects genuinely contaminated `@[vetted]` declarations
(`badVetFn`).

---

#### Finding 5: Cross-Boundary `Trusted.*` `realizeConst` Rejection in `TrustedBoundary.lean` (`f938c18db` Lines 422–528, 1341–1365), `.match_1.splitter` `.defnInfo` and `Lean.isReservedName` Behavior Under `loadExts := false`, and Verified Phase 1 + Phase 2 Fix (`isRealizedCompilerConstant` & `decide` `optConfig`)

`Basis: source + execution`

##### 5.1 On-Demand `realizeConst` Serialization into Consumer `.olean` Files

In Lean `v4.34.1`, equational theorems, congruence lemmas, functional-cases
principles, and match splitters (`<def>.eq_1`, `<def>.eq_def`,
`<def>.fun_cases_unfolding`, `<def>.match_1.congr_eq_1`,
`_private.<Consumer>.0.<def>.match_1.eq_1`,
`_private.<Consumer>.0.<def>.match_1.splitter`) are generated lazily via
`realizeConst` when a consumer module runs `simp`, `rw`, `unfold`, `split`, or
`fun_cases` and are serialized into the **consumer module's `.olean`** via
`kenv.constants.foldStage2` (`Lean/Environment.lean:1872`).

When two untrusted modules (`TheoryA` and `TheoryB`) independently run
`simp [Trusted.RealizeProbe.stepOpt]` and
`fun_cases Trusted.RealizeProbe.stepOpt x`
(`support/ProbeTrustedBoundaryFixes.lean`, Section 2), both `TheoryA.olean` and
`TheoryB.olean` serialize 8 constants whose `privateToUserName?` root is
`Trusted`:

| Constant in `TheoryA.olean` / `TheoryB.olean` | `ConstantInfo` Kind | `isTheorem` | `Lean.isReservedName` (`loadExts := false`) | `Lean.isReservedName` (`loadExts := true`) |
| :--- | :--- | :--- | :--- | :--- |
| `Trusted.RealizeProbe.stepOpt.eq_1` | `.thmInfo` | `true` | `true` | `true` |
| `Trusted.RealizeProbe.stepOpt.eq_2` | `.thmInfo` | `true` | `true` | `true` |
| `Trusted.RealizeProbe.stepOpt.eq_def` | `.thmInfo` | `true` | `true` | `true` |
| `Trusted.RealizeProbe.stepOpt.fun_cases_unfolding` | `.thmInfo` | `true` | `true` | `true` |
| `Trusted.RealizeProbe.stepOpt.match_1.congr_eq_1` | `.thmInfo` | `true` | `false` | `true` |
| `Trusted.RealizeProbe.stepOpt.match_1.congr_eq_2` | `.thmInfo` | `true` | `false` | `true` |
| `_private.<Mod>.0.Trusted.RealizeProbe.stepOpt.match_1.eq_1` | `.thmInfo` | `true` | `false` | `true` |
| `_private.<Mod>.0.Trusted.RealizeProbe.stepOpt.match_1.eq_2` | `.thmInfo` | `true` | `false` | `true` |
| `_private.<Mod>.0.Trusted.RealizeProbe.stepOpt.match_1.splitter` | `.defnInfo` | `false` | `false` | `true` |

Stock `verifyAndCollectLocals` (`TrustedBoundary.lean:1346-1356`) fails on
these `.olean` files in two ways:

1. **Cross-boundary `Trusted` namespace rejection (`line 1356`):** Because the
   `privateToUserName?` root of all 9 constants is `Trusted`, stock
   `verifyAndCollectLocals` immediately rejects `TheoryA` with:
   ```text
   policy:non-Trusted module TheoryA cannot declare constant _private.TheoryA.0.Trusted.RealizeProbe.stepOpt.match_1.eq_1 in Trusted namespace
   ```
2. **Sibling `realizeConst` collision (`lines 1346–1350`):** Both
   `TheoryA.olean` and `TheoryB.olean` serialize
   `Trusted.RealizeProbe.stepOpt.eq_def` with different proof terms (referencing
   `_private.TheoryA.0...splitter` vs. `_private.TheoryB.0...splitter`). When
   `importModules` loads both modules, `finalizeImport` merges them via
   `subsumesInfo` (`Lean/Environment.lean:2268-2344`), keeping `TheoryA` in
   `const2ModIdx` (`origin env`) while overwriting `env.checked`'s
   `ConstantInfo` with `TheoryB`'s proof body. Stock `verifyAndCollectLocals`
   then fails on `TheoryA` at line 1350 (`"stored declaration differs from
   inventory"`) and on `TheoryB` at lines 1346–1347 (`"duplicate declaration"`
   and `"inventory origin mismatch"`).

##### 5.2 Two Critical Subtleties Under `loadExts := false` and Verified Phase 1 + Phase 2 Fix

As proved by the table above (`support/ProbeTrustedBoundaryFixes.lean`,
Section 2):

1. **`_private.<Mod>.0.Trusted.<fn>.match_1.splitter` is a `.defnInfo`
   (`isTheorem == false`):** `Lean/Meta/Match/MatchEqs.lean:147-150` emits
   `.splitter` as a module-private `Declaration.defnDecl` (not a `thmDecl`) so
   the `split` tactic can be used inside computational definitions. A Phase 2
   exception that permits only `ci.isTheorem` in the `Trusted` namespace still
   rejects `.splitter`.
2. **`Lean.isReservedName env ci.name` returns `false` on all 5
   matcher-attached constants when `loadExts := false`:** Because
   `TrustedBoundary.importEnv` loads `.olean` files with `loadExts := false`
   (`line 160`) in `"audit"` mode to avoid executing arbitrary `[init]` code,
   `Match.Extension` (a `SimplePersistentEnvExtension`) is empty in `env`.
   Consequently, `isMatcherCore env p` in `MatchEqs.lean:338` returns `false`,
   causing `Lean.isReservedName` to return `false` for `match_1.eq_1`,
   `match_1.eq_2`, `match_1.splitter`, `match_1.congr_eq_1`, and
   `match_1.congr_eq_2` (while returning `true` for `stepOpt.eq_1`,
   `stepOpt.eq_2`, `stepOpt.eq_def`, and `stepOpt.fun_cases_unfolding`, whose
   handlers in `Eqns.lean:76` and `FunInd.lean:1528` only query
   `env.isSafeDefinition p`).

Combining three checks resolves both issues without enabling `loadExts := true`:

- **Phase 1 (`inspectCommand`):** Reject `namespace Trusted` and
  `def Trusted.*` in non-`Trusted` source files during `"preflight"` parsing.
- **Phase 2 (`isRealizedCompilerConstant` + `sameRealizedThmHeader`):** Require
  the parent constant `p` (where `u = .str p s` and `u = (privateToUserName?
  ci.name).getD ci.name`) to already exist in `locals` (`locals.contains
  ci.name.getPrefix || locals.contains p`), and require either `ci.isTheorem`
  with a reserved compiler theorem suffix (`eq_def`, `eq_unfold`, `unfold`,
  `else_eq`, `fun_cases`, `fun_cases_unfolding`, `induct`, `induct_unfolding`,
  `mutual_induct`, `mutual_induct_unfolding`, `inj`, `injEq`, `sizeOf_spec`,
  `eq_*`, `_eq_*`, `congr_*`, `_congr_*`) or `ci matches .defnInfo _` with
  `s == "splitter" && isMatcherSplitter p && (privateToUserName?
  ci.name).isSome`. When a sibling module re-realizes the same theorem, verify
  `sameRealizedThmHeader` (`name`, `levelParams`, `type`) and retain `stored`
  for `base.toKernelEnv.replay`.
- **Phase 1 `decide` `optConfig` fix (`TrustedBoundary.lean:366`):** In Lean
  `v4.34.1`, `s[1]` of `Lean.Parser.Tactic.decide` is an `optConfig` node that
  always has one child `s[1][0]` (the `null` node holding config items).
  Changing `unless s[1].getArgs.isEmpty` to `unless s[1][0].getArgs.isEmpty`
  admits bare `by decide` while still rejecting `by decide +native` and
  `by decide +kernel` (`support/ProbeTrustedBoundaryFixes.lean`, Section 3).

---

#### Finding 6: Architectural Comparison of `comparator` + `comparator-autograder` vs. Anneal's `TrustedBoundary.lean` and Implications for Two-Stage Verification / `.olean` Stubbing

`Basis: source + derived`

| Dimension | `xhalo32/comparator` + `plclub/comparator-autograder` | Anneal `trusted/audit/TrustedBoundary.lean` + `src/lib.rs` |
| :--- | :--- | :--- |
| **Execution & Sandbox Model** | Multi-process: runs `lake build` and `lean4export` inside Linux Landlock (`landrun`) sandboxes (`Comparator/MainSupport.lean:59-165`), serializes constants to NDJSON, parses them back in `Comparator`, and replays in `Lean.Kernel.Environment.replay`. | Single-process in-memory inspector (`lean --run TrustedBoundary.lean <req.json> <res.json>`) after `cargo-anneal` invokes `lean` with `-DElab.async=false` (`trusted/audit/src/lib.rs`). Inspects raw `.olean` `ModuleData` and `env.checked` directly without NDJSON round-tripping. |
| **Root Theorem / Specification Locking** | Dual-module diffing (`Challenge` vs. `Solution`): compares every non-hole constant reachable from a theorem's type against a reference `Challenge` build using syntactic `ConstantInfo` `BEq` (`Comparator.lean:112`). | Single-build structural verification (`TrustedBoundary.lean:1459-1482`): verifies `Mir.crate : Trusted.Crate` is an axiom-free monomorphic definition in `Mir` and `Proof.verify_crate` in `Proof` has exact kernel `Expr` type `Expr.app (Expr.const ``Trusted.CrateTheorem []) (Expr.const ``Mir.crate [])`. |
| **Handling of Mutable / Student-Supplied Definitions** | `@[autogradedHole]` allows `Solution` to replace the body of a `def` or constructors of an `inductive` (`Comparator.lean:87-103`). Unsound on `inductive` holes (`inductiveHoleMatches` ignores `ctors` and `Compare.loop` never checks constants used in constructor types). | Clean module-level separation: `Mir.lean` (generated by `anneal-rustc-capture`) may only import `foundation ++ trusted`, never `theory/` or `Proof.lean` (`validateGraph`, `TrustedBoundary.lean:725-772`). Untrusted user proofs live in `Proof.lean` and `theory/`, which cannot redefine `Trusted.*` or `Mir.crate`. |
| **Proof-Irrelevance & Helper Theorems** | Broken for helper theorems referenced in non-hole definitions: `Compare.loop` uses syntactic `ConstantInfo` `BEq` (`TheoremVal.value == TheoremVal.value`), rejecting student-proved lemmas if referenced by a non-hole `def`. | Preserved: `Proof.verify_crate`'s proof body can use arbitrary theorems and definitions in `theory/` and `Proof`; `TrustedBoundary` checks that all local constants are axiom-free, safe, non-partial, and kernel-replayed. |
| **Axiom, `unsafe`, `partial`, `opaque`, & Quotient Auditing** | Checks reachable axioms against `permitted_axioms` (`propext`, `Classical.choice`, `Quot.sound`) via `Axioms.loop` (`Comparator/Axioms.lean:38-71`), and `lean4export` rejects `unsafe`/`partial`/`opaque` constants (`Export.lean:247-252`). Does not audit unreachable declarations in the `.olean`. | Audits every constant in every non-foundation `.olean` (`verifyAndCollectLocals`, `TrustedBoundary.lean:1357-1363`), rejecting any `isUnsafe`, `isPartial`, `isAxiom`, `.quotInfo`, or bodyless `opaque` declaration even if unreachable, plus per-axiom scope policies (`closure`, lines 663–723). |
| **Candidate Feature Tracking (`@[candidate]` vs. `@[vetted]`)** | None. | Static non-contamination analysis (`checkTrustedNonContamination`, lines 1093–1222) and demand-driven active candidate feature collection across `Trusted.candidate "<feat>"` guards (`collectActiveCandidateFeatures`, lines 1244–1305), requiring `isPureVettedMatcher` (Finding 4) to handle intra-module `.match_1` deduplication. |
| **Handling of `realizeConst` (`map₁` / `map₂`)** | `lean4export` uses `Lean.importModules`, which loads `.olean` constants (including `foldStage2` realized constants) into `map₁` and merges duplicate realized theorems across modules via `subsumesInfo`. Uses `--ignore-missing` (`d6400b2`) to avoid panicking on missing `exportTargets`. | Reads `env.header.moduleData` and `env.checked` directly under `loadExts := false`, requiring `isRealizedCompilerConstant` and `sameRealizedThmHeader` (Finding 5) when consumer modules trigger on-demand `realizeConst` for imported declarations. |

##### Implications for Two-Stage Verification and `.olean` Stubbing

Because `matcherExt` is a non-persistent environment extension
(`asyncMode := .local`), matcher deduplication never crosses `.olean` module
boundaries. Placing generated specifications (`Mir.lean` or `Specs.lean`) in a
separate module from `Proof.lean` completely isolates specification constants
from proof-side matcher deduplication. Conversely, within a single module,
replacing any declaration body with `sorry` or a stub alters which `.match_1`
constants are registered in `matcherExt` and shifts the `.match_1` names
referenced by subsequent declarations in that same module. Any future stubbing
or lockfile mechanism that compares declarations across a stubbed vs.
un-stubbed build of the same module must therefore either keep specifications
and proofs in separate modules or compare definition bodies up to kernel
`isDefEq` rather than syntactic `ConstantInfo` equality.

### Part II — Literate Verification (`SFLCompat`/`SFLMeta`, `Verso`/`SubVerso`/`Illuminate`), Declaration Drift Checking (`sf_recall`), and Anneal Tutor

#### Finding 1: Two-Tier `SFLCompat` / `SFLMeta` Architecture, Multi-Variant Byte-Range Extraction (`student`, `solutions`, `terse`, `grading`), and `Verso` / `SubVerso` / `Illuminate` Integration

`Basis: source`

##### 1.1 Two-Tier Separation (`SFLCompat/` vs. `SFLMeta/`)

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

##### 1.2 Two-Phase Elaboration and Right-to-Left Byte-Span Extraction

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

##### 1.3 `Verso`, `SubVerso`, and `Illuminate` Integration

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

### Finding 4: Complete Audit of All 89 Fenced Code Blocks in Anneal Tutor (`the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`) and Live Detection of 6 Drifted Unmanaged Library Blocks

`Basis: source + execution`

#### 4.1 Anneal Tutor Workflow vs. `sf-in-lean`

On Anneal Tutor branch `origin/Gk6v77bigheral6sjtzyeoq6ob52xgomw` (commit
`f938c18db56c49e82dde95506894a9b58b76b227 (with the 6-chapter ITree/Std Tutor specimen embedded in `support/ProbeExperimentAndTutorAudit.lean`)`),
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

#### 4.2 Audit of All 89 Fenced Code Blocks Across `docs/tutor/*.md` on `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`

Across all seven Markdown files in `docs/tutor/` on `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`, there are **89
fenced code blocks**:

- **73 managed blocks (`<!-- tutor: ... -->`):** 68 `mode=replace` blocks and 5
  `mode=check` blocks. All 73 were updated during the `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)` port to
  coinductive `ITree` and `Std` foundations and pass `tutor_workflow.py`.
- **16 unmanaged blocks (no `<!-- tutor: ... -->` directive):** 6 non-Lean
  illustrative blocks (1 ASCII directory layout, 5 Rust/shell snippets) and **10
  Lean fenced blocks** quoting declarations from `trusted/lean/`,
  `theory/Anneal/`, or `tests/refinement/`.

Auditing all 10 unmanaged Lean fenced blocks against the actual repository
declarations at `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)` (and testing them with `sf_recall` in
`support/ProbeExperimentAndTutorAudit.lean:397-615`) revealed that **6 of the 10
unmanaged Lean blocks** (plus adjacent prose in `README.md`,
`02-rust-specifications.md`, `04-manual-proof-workflow.md`, and
`05-verifying-unsafe-rust.md`) silently drifted during `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`:

| # | Tutor File & Line Range (`the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`) | Quoted Lean Declarations | `sf_recall` Status | Exact Semantic / API Drift vs. `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)` Codebase |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `docs/tutor/README.md:40-46` | `structure Partial` | **PASS** | Matches `trusted/lean/Trusted/Refinement.lean:51-55` (`defined : Prop`, `val : defined → α`). |
| 2 | `docs/tutor/01-basic-usage-and-outputs.md:372-407` | `MirExecPartial`, `MirContractSpec` | **FAIL (Drifted)** | Quotes removed `Partial (BehaviorSet (ExecPrefix MirObs Value))`, `MirNoUB.holds (MirSem ⟨body, args⟩)`, `ReachesNormalReturn`, and `Preorder.refines`. At `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`, `Trusted/VerificationResult.lean:89-120` uses `(mirCallTree body args).toPartial` over `Partial (BehaviorSet (List (Event MirEffect) × MirOutcome))` and `≤`. |
| 3 | `docs/tutor/02-rust-specifications.md:589-612` | `Partial.contract`, `Language.WellFormedOn`, `Language.WellFormed`, `Language.ContractSpec` | **PASS (`sf_recall`) / FAIL (`sf_recall_source`)** | `02-rust-specifications.md:597-601` writes `Language.WellFormedOn` with named structure fields `{ defined := safetyPre q, val := fun _ _ => True }`, whereas `Trusted/Refinement.lean:227-229` writes `⟨safetyPre q, fun _ _ => True⟩`. `sf_recall` accepts this via definitional equality; `sf_recall_source` rejects it. |
| 4 | `docs/tutor/02-rust-specifications.md:629-637` | `structure Compiler`, `def Compiles` | **FAIL (Drifted)** | Quotes removed `Preorder.refines (L_tgt.sem t) (π_c (L_src.sem s))` instead of `L_tgt.sem t ≤ π_c (L_src.sem s)` (`abbrev Compiles`) in `Trusted/Refinement.lean:268-281`. |
| 5 | `docs/tutor/02-rust-specifications.md:645-662` | `theorem safe_contractSpec_preserves_wellFormed`, `theorem misplaced_contractSpec_violates_wellFormed` | **FAIL (Drifted)** | Both theorems quote `Preorder.refines` instead of `≤` (`tests/refinement/ConcreteYDiagram.lean:94-105`). |
| 6 | `docs/tutor/02-rust-specifications.md:672-676` | `structure Compiler.Verified` | **FAIL (Drifted)** | Depends on drifted `Compiles` from block #4 and omits universe parameter `u` (`Compiler.Verified.{u}`). |
| 7 | `docs/tutor/02-rust-specifications.md:682-688` | `def MirContractHoldsWithSafety`, `def MirContractHolds` | **PASS (Prose at L690 drifted)** | Code block matches `Trusted/VerificationResult.lean:124-131` (`≤`), but prose at line 690 still states `"where MirContractHoldsWithSafety is Preorder.refines"`. |
| 8 | `docs/tutor/04-manual-proof-workflow.md:388-398` | `theorem dischargeSafeRustBoundedU8` | **FAIL (Deleted)** | Quotes `dischargeSafeRustBoundedU8` (and prose at `04:20, 380-405`, `02:152`, `README.md:174, 216` cites `dischargeSafeRustBoundedU8` / `dischargeRustBoundedU8`), both of which were deleted from `theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean` in favor of `dischargeSymMir`. |
| 9 | `docs/tutor/05-verifying-unsafe-rust.md:56-99` & `112-115` | `MirStatefulExecPartial`, `MirStatefulContractSpec`, `MirStatefulContractHoldsWithSafety`, `MirStatefulContractHolds` | **FAIL (Drifted)** | Quotes removed `ReachesPrefix MirMachine`, `ReachesNormalReturn`, `Partial (BehaviorSet (Value × Memory))`, and `Preorder.refines` instead of `(mirStatefulTree body args mem).toPartial` over `Partial (BehaviorSet (List (Event MirEffect) × MirOutcome))` and `≤` (`Trusted/VerificationResult.lean:164-190`). |
| 10 | `docs/tutor/05-verifying-unsafe-rust.md:374-387` | `theorem dischargeStatefulEq` | **FAIL (Drifted)** | Quotes `h_wp : WP (runMirStatefulBounded fuel c.body expectedArgs expectedMem) ...` (and prose at lines 393–394 cites `runMirStatefulBounded`), whereas `SymbolicEval.lean:2156-2172` at `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)` uses `wpMirSym fuel c.body (initMachineStateWithMemory c.body expectedArgs expectedMem) (mirNormalPost ...)`. |

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

#### 5.1 Interaction with `TrustedBoundary.lean` (`f938c18db` and `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`)

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

### Part III — Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration (`inversion`), and `Plausible` Negative Canaries

#### Finding 1: Operational Semantics, Program Equivalence (`HL/Slang.lean`, `HL/Imp.lean`, `HL/Equiv.lean`, `TS/Smallstep.lean`), and `leanprover/cslib` (`LTS`, `Simulation`) vs. Anneal's Fuel-Indexed MIR Semantics and Asymmetric Refinement (`StepResult.refines`)

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`HL/Slang.lean:1–252`, `HL/Imp.lean:1–262`,
`HL/Equiv.lean:1–777`, `TS/Smallstep.lean:1–579`), `leanprover/cslib` commit
`f7ec4db9f911` (`Cslib/Foundations/Semantics/LTS/Basic.lean:1–230`,
`Simulation.lean:1–145`, `Bisimulation.lean:1–180`), `joshlf/anneal` commits
`f938c18db56c` and `the PME MIR operational semantics prototype (`support/`)` (`trusted/lean/Anneal/MirSemantics.lean`,
`theory/Anneal/MirPassProofs.lean`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`HoareVCProbe`,
`FunInductionProbe`).

##### 1.1 Architectural Comparison Across Semantic Encodings

The three repositories represent operational semantics and behavioral
equivalence along three distinct axes:

| Dimension | `sf-in-lean` (`HL/Slang.lean`, `HL/Imp.lean`, `HL/Equiv.lean`, `TS/Smallstep.lean`) | `leanprover/cslib` (`LTS/Basic.lean`, `Simulation.lean`, `Bisimulation.lean`) | `joshlf/anneal` (`trusted/lean/Anneal/MirSemantics.lean`, `theory/Anneal/MirPassProofs.lean`) |
| :--- | :--- | :--- | :--- |
| **Program Representation** | Deeply embedded inductive ASTs (`Com`: `skip`, `assign`, `seq`, `ite`, `while`; `Tm`: lambda + store operations) | Abstract state type `State` with labeled transition relation `Tr : State → Label → State → Prop` | Deeply embedded CFG (`Body` with indexed `List BasicBlock`, `Stmt`, `Terminator`, `Rvalue`, `Operand`) |
| **Evaluation Mode** | Big-step inductive relation `CEval : Com → State → State → Prop` (`HL/Imp.lean:155–176`) and small-step `Step : (Tm × Store) → (Tm × Store) → Prop` (`TS/References.lean:243–296`) | Relational single-step `LTS.Tr s μ s'` and multi-step `LTS.MTr s μs s'` (trace-indexed transitive closure) | Fuel-indexed total evaluator (`evalStmt`, `evalTerminator`, `evalBlock`, `evalCall`, `evalBody : Nat → ... → Option StepResult`) |
| **Nontermination & Fuel** | Big-step `CEval` omits diverging runs (`while_true_nonterm`, `HL/Equiv.lean:226–242`); small-step uses reflexive-transitive closure `Multi Step` (`TS/Smallstep.lean:180–190`) | Coinductive/relational infinite traces and divergence predicates (`LTS.Diverges`) | Explicit fuel exhaustion `none` (`OutOfFuel`), distinct from `.returned v`, `.diverged` (unwind/abort), and `.unreachable` (`UndefinedBehavior`) |
| **Equivalence / Refinement Contract** | Symmetric big-step equivalence: `cequiv c1 c2 := ∀ st st', CEval c1 st st' ↔ CEval c2 st st'` (`HL/Equiv.lean:45–47`) | Asymmetric `Simulation` (`∀ s₁ s₂ μ s₁', R s₁ s₂ → Tr s₁ μ s₁' → ∃ s₂', Tr s₂ μ s₂' ∧ R s₁' s₂'`) and symmetric `Bisimulation` | Asymmetric UB/fuel refinement: `StepResult.refines tgt src : Option StepResult → Option StepResult → Prop` (`PassPackage.sound`) |

##### 1.2 Why Symmetric `cequiv` Fails for Fuel-Indexed MIR Bodies and How Asymmetric Refinement Resolves It

In `HL/Equiv.lean:45–47`, two `Imp` commands `c1` and `c2` are behaviorally
equivalent when they relate identical initial and final states:

```lean
def cequiv (c1 c2 : Com) : Prop :=
  ∀ (st st' : State), (CEval c1 st st') ↔ (CEval c2 st st')
```

`HL/Equiv.lean` uses `cequiv` to verify recursive AST transformations such as
`fold_constants_com_sound` (`HL/Equiv.lean:511–545`) via congruence lemmas
(`CSeq_congruence`, `CIf_congruence`, `CWhile_congruence`). However, a
symmetric bi-implication `↔` cannot serve as the top-level correctness relation
for Anneal's MIR semantics (`trusted/lean/Anneal/MirSemantics.lean`) for two
fundamental reasons:

1. **Asymmetry of Undefined Behavior (`.unreachable`):** In Rust and MIR, a
   source program execution that triggers Undefined Behavior (represented by
   `some .unreachable` in `StepResult`, or `none` in partial statement helpers
   such as `evalMirStmt` in `support/ProbeHoareWpFunIndAndReferences.lean:642`)
   imposes no constraint on a transformed target program. An optimization pass
   such as dead-branch elimination or unchecked-shift folding may turn a source
   `.unreachable` execution into a defined value `some (.returned v)` without
   allowing the converse (`some (.returned v)` refined into
   `some .unreachable`).
2. **Asymmetry of Fuel Consumption (`none` / `OutOfFuel`):** Because `evalBody`
   decrements `fuel : Nat` across basic-block transitions and recursive calls,
   an optimization that eliminates basic blocks or inlines a call can succeed
   with `some (.returned v)` at fuel `N` where the unoptimized body returned
   `none` (`OutOfFuel`).

Anneal's `StepResult.refines : Option StepResult → Option StepResult → Prop`
(on branch `the PME MIR operational semantics prototype (`support/`)`, `theory/Anneal/MirPassProofs.lean`) and `cslib`'s
asymmetric `Simulation` (`Cslib/Foundations/Semantics/LTS/Simulation.lean`)
capture this directionality directly:

- When the source evaluation yields `none` (`OutOfFuel`) or
  `some .unreachable` (`UndefinedBehavior`), `StepResult.refines tgt src` holds
  trivially (`True`) for any target outcome `tgt`.
- When the source evaluation yields a defined terminal outcome
  `some (.returned v)` or `some .diverged`, the target must produce the exact
  same defined outcome (`tgt = some (.returned v)` or `tgt = some .diverged`).

Symmetric equality (`evalAExp (optimizeAExp a) st = evalAExp a st` or
`evalMirStmt (optMirConstPropStmt s) env = evalMirStmt s env`) remains the
right local lemma shape for total, fuel-free expression and single-statement
rewrites within a basic block, which then lift into asymmetric
`StepResult.refines` at the basic-block and `Body` layers via monotonic
fuel-refinement congruence lemmas.

---

#### Finding 2: Functional Induction (`symm; fun_induction <;> simp_all`) vs. Structural Induction vs. `fun_cases` on Compiler Passes (`optimizeAExp`, `optMirConstPropStmt`), Module-Closure Splitter Amortization, and Equation-Compiler `._unsafe_rec` Interaction with `TrustedBoundary.lean`

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`HL/Slang.lean:51–228`, `HL/Equiv.lean:457–545`),
`joshlf/anneal` commits `f938c18db56c` and `the PME MIR operational semantics prototype (`support/`)`
(`trusted/audit/TrustedBoundary.lean:178–202`,
`theory/Anneal/MirPassProofs.lean`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`FunInductionProbe`, lines
509–979).

##### 2.1 The Quadratic Wildcard Explosion in `HL/Slang.lean` vs. Lean 4's `fun_induction` and `fun_cases`

When an AST optimization pass matches specific multi-level constructor patterns
and falls through to a wildcard arm (`| _ => ...`), structural `induction` or
nested `cases` on the syntax tree must manually re-split every sub-expression
to prove that the wildcard arm does not overlap the specialized arms. In
`HL/Slang.lean`, `Slang` defines a 3-constructor expression AST (`num`, `id`,
`plus`) and a constant-folding pass `optimize_0plus`. Even for 3 constructors,
the manual `cases`-based proof `optimize_0plus_sound` (`HL/Slang.lean:77–139`)
requires 62 lines of nested `cases e1 <;> cases e2` splits, which
`HL/Slang.lean:216–228` replaces with a 5-line `fun_induction` script:

```lean
theorem optimize_0plus_sound'' (st : State) (e : Exp) :
    eval st (optimize_0plus e) = eval st e := by
  symm
  fun_induction optimize_0plus e <;> simp_all [eval]
```

Note the critical `symm` before `fun_induction`: in Lean 4, when an induction
hypothesis `ih1 : eval st e1 = eval st (optimize_0plus e1)` is oriented with
the unoptimized term on the left-hand side, `simp_all [eval]` rewrites
`eval st (optimize_0plus e1)` in the goal only when the goal is oriented so the
unfolded recursive call appears without creating a self-rewriting loop.

To quantify how this scales to realistic compiler ASTs, `FunInductionProbe` in
`support/ProbeHoareWpFunIndAndReferences.lean:509–979` benchmarks two passes:

1. **Recursive 8-Constructor Arithmetic Optimizer (`optimizeAExp`):** Over an
   8-constructor `AExp` (`num`, `var`, `add`, `sub`, `mul`, `shl`, `bitAnd`,
   `ite`) with three nested constant-folding match arms (`0 + e2`, `e1 + 0`,
   `1 * e2`, `e1 * 1`, `0 * e2`, `e1 * 0`, and wildcard fallthroughs),
   comparing:
   - `optimizeAExp_sound_structural`: manual structural `induction a` with
     exhaustive 8-way sub-case splits (`351` lines of proof script),
   - `optimizeAExp_sound_fun_ind_simp`: `symm; fun_induction optimizeAExp a <;>
     simp_all [AExp.eval]` (`4` lines of proof script), and
   - `optimizeAExp_sound_fun_ind_grind`: `fun_induction optimizeAExp a <;>
     grind [AExp.eval]` (`3` lines of proof script).
2. **Non-Recursive 4-Level MIR Constant-Propagation Pass
   (`optMirConstPropStmt`):** Modeling Anneal's `MirPassProofs.lean`
   (`the PME MIR operational semantics prototype (`support/`)`), which inspects a statement
   `Stmt.assign dst (.binaryOp op (.const (.int c1)) (.const (.int c2)))` across
   4 nested ADT layers (`MirStmt` -> `MirRvalue` -> `MirOperand` -> `MirConst`)
   with a wildcard fallthrough `| s => s`, comparing:
   - `evalMirStmt_optMirConstPropStmt_structural`: 4-level nested `cases` with
     `rfl` on all 18 resulting branches (`42` lines), and
   - `evalMirStmt_optMirConstPropStmt_fun_cases`: `fun_cases optMirConstPropStmt
     s <;> rfl` (`2` lines).

##### 2.2 Direct Proof-Term Size vs. Module-Closure Splitter Overhead

Running `lean --run support/ProbeHoareWpFunIndAndReferences.lean` yields the
exact DAG object counts (`Expr.numObjs` after maximal DAG sharing), auxiliary
constant counts, and 10-iteration average `Lean.Kernel.Environment.replay`
times:

| Theorem | Proof Strategy | Script Lines | Direct Proof `Expr.numObjs` | Marginal Theorem Closure (`Expr.numObjs`) | Transitive Module Closure (`Expr.numObjs`) | Module Closure Decls | `.eq_N` / `.induct` / `.match_N` / `._proof_N` | Marginal Kernel Replay (`us`) | Full Closure Kernel Replay (`us`) | Transitive Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :---: | ---: | ---: | :--- |
| `optimizeAExp_sound_structural` | Structural `induction` + 8-way `cases` | 351 | `12,665` | `12,665` | `24,660` | 30 | `11 / 0 / 4 / 0` | `27,315` | `64,675` | `#[propext]` |
| `optimizeAExp_sound_fun_ind_simp` | `symm; fun_induction <;> simp_all` | 4 | `1,126` | `1,126` | `21,381` | 40 | `11 / 1 / 7 / 0` | `9,270` | `64,840` | `#[propext]` |
| `optimizeAExp_sound_fun_ind_grind` | `fun_induction <;> grind` | 3 | `650` | `4,884` | `25,139` | 57 | `11 / 1 / 7 / 17` | `13,865` | `72,068` | `#[propext, Quot.sound, Classical.choice]` |
| `evalMirStmt_optMirConstPropStmt_structural` | 4-level nested `cases <;> rfl` | 42 | `1,271` | `1,271` | `4,581` | 15 | `1 / 0 / 2 / 0` | `3,005` | `6,466` | `#[]` |
| `evalMirStmt_optMirConstPropStmt_fun_cases` | `fun_cases <;> rfl` | 2 | `290` | `290` | `16,751` | 32 | `5 / 1 / 4 / 0` | `516` | `12,670` | `#[propext]` |

Three structural laws emerge from these measurements:

1. **Direct and Marginal Theorem Compression (`11.2x` on `optimizeAExp`, `4.4x`
   on `optMirConstPropStmt`):** `fun_induction` and `fun_cases` delegate
   wildcard disjointness to the equation compiler's pre-generated `.induct` /
   `.fun_cases` principle (`optimizeAExp.induct = 1,452` objects;
   `optMirConstPropStmt.fun_cases = 212` objects). Consequently, the theorem's
   own proof term shrinks from `12,665` to `1,126` DAG objects (`-91.1%`) on
   `optimizeAExp` and from `1,271` to `290` DAG objects (`-77.2%`) on
   `optMirConstPropStmt`, cutting marginal per-theorem kernel replay time by
   `66.1%` (`9,270 us` vs. `27,315 us`) and `82.8%` (`516 us` vs. `3,005 us`),
   respectively.
2. **Splitter Amortization Threshold ($K \ge 2$):** On a non-recursive
   function like `optMirConstPropStmt`, structural `cases <;> rfl` uses only
   `optMirConstPropStmt.eq_def` (`210` objects) and never references the
   equation compiler's `.match_1.splitter` (`1,744` objects) or `.match_1.eq_4`
   (`4,003` objects, which encodes the negated pattern assumptions of the
   wildcard branch). Calling `fun_cases` pulls `optMirConstPropStmt.fun_cases`,
   `.match_1.splitter`, and `.match_1.eq_1`..`.eq_4` (`12,170` objects of shared
   machinery) into the transitive module closure. Thus, for a single theorem
   ($K = 1$) over a non-recursive pass, nested `cases` has a smaller total
   module closure (`4,581` vs. `16,751` objects), whereas for $K \ge 2$
   theorems over the same pass—or even $K = 1$ theorem over a recursive
   multi-arm pass like `optimizeAExp` (`21,381` vs. `24,660` objects)—the
   shared `.induct`/`.fun_cases` principle amortizes and wins in both marginal
   and total DAG size.
3. **Equation-Compiler `._unsafe_rec` Emission and `TrustedBoundary.lean`:**
   In Lean `v4.34.1`, when a recursive function such as `optimizeAExp` (or
   `FullDCom.verificationConditions` / `SparseDCom.awp`) contains overlapping
   wildcard arms or mutual recursion that Lean compiles via well-founded
   recursion (`_unary`), the equation compiler also emits an auxiliary stage-1
   constant `optimizeAExp._unsafe_rec` (`ci.isUnsafe = true`). Even though the
   kernel-checked theorem `optimizeAExp_sound_fun_ind_simp` never references
   `optimizeAExp._unsafe_rec` in its proof DAG, `TrustedBoundary.lean:178–202`
   (`checkConstantInfo`) scans every constant whose name begins with `Anneal.`
   in `.olean` stage 1 and rejects any constant with `ci.isUnsafe` or
   `ci.isPartial`. Therefore:
   - Functions defined inside `trusted/lean/Anneal/` (`Anneal.*`) must use pure
     structural recursion (`fuel : Nat` or direct structural recursion without
     well-founded `_unary` compilation) so Lean never emits
     `Anneal.*._unsafe_rec`.
   - Complex recursive AST passes and VC generators should live outside
     `trusted/` in `theory/`, or if placed in `Anneal.*`, `TrustedBoundary.lean`
     must trace reachability from `Trusted.CrateTheorem` rather than rejecting
     unreferenced compiler-generated `._unsafe_rec` stage-1 siblings.

---

#### Finding 3: Hoare Logic and Weakest-Precondition VC Generation (`HL/Hoare.lean`, `HL/Hoare2.lean` `FullDCom` vs. `SparseAnnotations.awp` vs. `BuildingBlocks.lean` `BB-1`..`BB-8`), and Exact Transitive Axiom Closures of `omega`, `lia`, and `grind` in Lean `v4.34.1`

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`HL/Hoare.lean:1–777`, `HL/Hoare2.lean:1–660`), `joshlf/anneal`
commit `f938c18db56c` (`theory/Anneal/Verification/BuildingBlocks.lean`,
`trusted/audit/TrustedBoundary.lean:15–16`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`HoareVCProbe`, lines 53–507;
`AxiomClosureProbe`, lines 1267–1310).

##### 3.1 Comparing Three VC Architectures Across Diamond, 8-Statement Chain, and Loop Programs

`HL/Hoare.lean` and `HL/Hoare2.lean` implement three progressively more compact
verification architectures over `Imp`:

1. **Step-by-Step Hoare Rule Application (`HL/Hoare.lean:136–395`):** Every
   sequential composition (`hoare_seq`), conditional (`hoare_if`), loop
   (`hoare_while`), and assertion strengthening (`hoare_consequence_pre`,
   `hoare_consequence_post`) is applied explicitly in the proof script. This
   mirrors Anneal's current `BuildingBlocks.lean` (`BB-1`..`BB-8`, such as
   `evalBlock_step`, `evalBlock_goto`, `evalBlock_switchInt_true`, and
   `evalBlocks_while`), where proof authors step through basic blocks one
   statement and terminator at a time.
2. **Full Decorated Programs (`HL/Hoare2.lean:168–361`, `FullDCom`):** Every
   command node in `FullDCom` carries an explicit postcondition `Assertion`
   (`skip (Q)`, `assign x a (Q)`, `seq d1 d2`, `ite b P1 d1 P2 d2 (Q)`,
   `while b Pbody d (Qpost)`). A single meta-theorem `full_verification_correct`
   (`HL/Hoare2.lean:321–361`) proves `∀ P d, verificationConditions P d →
   HoareTriple P (erase d) (post d)`. However, for an $N$-statement basic block,
   `FullDCom` generates $N$ intermediate postcondition assertions and $N$
   implication VCs `(P_i → P_{i+1}[x ↦ a])`, growing both the AST and VC tree
   linearly with redundancy at every assignment.
3. **Sparse Annotations with Weakest Liberal Preconditions
   (`HL/Hoare2.lean:514–660`, `SparseAnnotations.SparseDCom` + `awp`):**
   `SparseDCom` removes all assertions from `skip`, `assign`, `seq`, and `ite`,
   requiring user annotations only at loop headers (`while b (Pinv : Assertion)
   (body : SparseDCom)`) and at the function's entry precondition and exit
   postcondition. The backward transformer `awp : SparseDCom → Assertion →
   Assertion` computes weakest preconditions syntactically:
   - `awp .skip Q = Q`
   - `awp (.assign x a) Q = Q[x ↦ a]` (state substitution `assn_sub`)
   - `awp (.seq d1 d2) Q = awp d1 (awp d2 Q)`
   - `awp (.ite b d1 d2) Q = fun st => (BExp.eval b st = true → awp d1 Q st) ∧
     (BExp.eval b st = false → awp d2 Q st)`
   - `awp (.while _ Pinv _) _ = Pinv`
   while `verificationConditions : Assertion → SparseDCom → Assertion → Prop`
   emits `True` on loop-free code (beyond the single entry implication
   `∀ st, P st → awp d Q st`) and emits only loop-body preservation and
   loop-exit obligations at `while` nodes.

`HoareVCProbe` in `support/ProbeHoareWpFunIndAndReferences.lean:53–507`
evaluates all three encodings on three benchmark programs:

- `diamondProg`: 2-branch conditional computing `z := (x + y) + 1` or
  `z := (x + x) + 1`, proved to satisfy `z = x + y + 1`.
- `chain8Prog`: 8-assignment straight-line basic block accumulating linear
  offsets into registers `r0`..`r3`, proved to satisfy `r3 = 2 * r0_init + 22`.
- `loopProg`: `while 0 < r0 do (r0 := r0 - 1; r2 := r2 + 1)`, proved to satisfy
  `r0 = 0 ∧ r2 = r0_init + r2_init` under invariant
  `r0 + r2 = r0_init + r2_init`.

| Benchmark Theorem | VC Architecture | Direct Proof `Expr.numObjs` | Marginal Closure (`Expr.numObjs`) | Transitive Module Closure (`Expr.numObjs`) | Marginal Kernel Replay (`us`) | Full Closure Kernel Replay (`us`) | Transitive Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `diamond_verified_hoare_rules` | Step-by-step `hoare_seq` / `hoare_if` | `1,620` | `3,128` | `4,292` | `1,920` | `4,884` | `#[propext, Quot.sound]` |
| `diamond_verified_full_dcom` | `FullDCom` (`full_verification_correct`) | `1,608` | `3,116` | `10,331` | `4,009` | `16,581` | `#[propext, Quot.sound]` |
| `diamond_verified_sparse_awp` | `SparseDCom` (`awp` + `sparse_verification_correct`) | `504` | `504` | `6,881` | `789` | `10,137` | `#[propext]` |
| `chain8_verified_hoare_rules` | Step-by-step `hoare_seq` (8 steps) | `8,379` | `9,887` | `11,051` | `4,839` | `7,940` | `#[propext, Quot.sound]` |
| `chain8_verified_full_dcom` | `FullDCom` (8 intermediate postconditions) | `10,956` | `12,464` | `19,679` | `9,367` | `21,984` | `#[propext, Quot.sound]` |
| `chain8_verified_sparse_awp` | `SparseDCom` (`awp`, 1 entry VC) | `2,535` | `2,535` | `8,912` | `775` | `10,160` | `#[propext]` |
| `loop_verified_hoare_rules` | `hoare_while` + `omega` | `583` | `985` | `2,175` | `1,546` | `4,462` | `#[propext, Quot.sound]` |
| `loop_verified_sparse_awp` | `SparseDCom` (`awp`) + `omega` on conjunction VC | `539` | `985` | `7,362` | `2,068` | `11,431` | `#[propext, Quot.sound, Classical.choice]` |
| `loop_verified_sparse_awp_constructive` | `SparseDCom` (`awp`) + `And.intro` + `Nat` lemmas | `299` | `299` | `6,676` | `901` | `10,192` | `#[propext]` |

Key engineering conclusions for Anneal's `BuildingBlocks.lean`:

1. **Loop-Free Basic-Block Sub-DAGs Collapse to a Single `awp` Obligation:**
   On both `diamondProg` and `chain8Prog`, `SparseDCom.awp` reduces the entire
   control-flow graph to a single entry implication over substituted states,
   discharged by `omega` or `simp` without `Quot.sound` or `Classical.choice`
   when simplified via `State.update` (`#[propext]`). Direct proof-term size
   drops by `3.2x` (`504` vs. `1,620` nodes on `diamondProg`) and `3.3x`
   (`2,535` vs. `8,379` nodes on `chain8Prog`), while marginal kernel replay
   time drops by `6.2x` (`775 us` vs. `4,839 us`).
2. **Amortizing `sparse_verification_correct`:** Proving the generic soundness
   theorem `sparse_verification_correct` once in `theory/Anneal/Verification/`
   adds `~6,377` shared module-closure objects (`~9.3 ms` one-time kernel
   replay). Because `chain8_verified_hoare_rules` already consumes `11,051`
   module-closure objects on a single 8-statement block (`8,912` for
   `chain8_verified_sparse_awp`), `SparseDCom` wins on total module closure
   from the very first 8-statement function ($K = 1$) and saves `~7.3k` DAG
   nodes on every subsequent function.
3. **Fuel-Accounting Extension for Anneal MIR:** Unlike relational `CEval`,
   Anneal's `evalBlocks fuel body bbIdx frames` decrements `fuel` on every
   basic-block transition (`goto`, `switchInt`, `call`, `return`). A
   `SparseDCom`-style backward WP transformer for Anneal basic-block DAGs
   therefore threads a minimum fuel requirement `reqFuel : SparseDCom → Nat`:
   - `reqFuel (.block stmts) = 1`
   - `reqFuel (.seqGoto d1 d2) = reqFuel d1 + reqFuel d2`
   - `reqFuel (.switchInt cond dTrue dFalse) =`
     `1 + max (reqFuel dTrue) (reqFuel dFalse)`
   - `reqFuel (.loop k inv body) = k * (reqFuel body + 1) + 1`
   This preserves `SparseDCom`'s elimination of intermediate state assertions
   while guaranteeing
   `fuel >= reqFuel d → evalBlocks fuel ... = some (.returned v)`.

##### 3.2 Exact Transitive Axiom Closures of `omega`, `lia`, and `grind` vs. `TrustedBoundary.lean`

In `joshlf/anneal` commit `f938c18db56c`,
`trusted/audit/TrustedBoundary.lean:15–16` defines the kernel axiom allowlist
for `Trusted.CrateTheorem` as:

```lean
def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice]
```

Wait: why did `diamond_verified_hoare_rules` and `loop_verified_hoare_rules`
pull in `Quot.sound`, and why did `loop_verified_sparse_awp` pull in
`Classical.choice` while `loop_verified_hoare_rules` did not?
`AxiomClosureProbe` in `support/ProbeHoareWpFunIndAndReferences.lean:1267–1310`
isolates 8 atomic arithmetic and propositional goals in Lean `v4.34.1` and
traces their exact transitive axiom closures and shortest dependency paths in
`Kernel.Environment`:

| Probe Theorem | Goal Shape | Tactic | Transitive Axioms | Reachable Kernel Decls | Shortest Path to `Classical.choice` | Shortest Path to `Quot.sound` |
| :--- | :--- | :--- | :--- | ---: | :--- | :--- |
| `omega_nat_add` | `a < 100 → b < 100 → a + b < 200` | `omega` | `#[propext, Quot.sound]` | `1,437` | *(none — `0` uses)* | `7` hops via `Lean.Omega.combo_sat'` $\to$ `Coeffs.combo_eq_smul_add_smul` $\to$ `IntList.combo_eq_smul_add_smul` $\to$ `funext` $\to$ `Quot.sound` |
| `omega_nat_sub` | `a + b = k ∧ 0 < a → (a - 1) + (b + 1) = k` | `omega` | `#[propext, Quot.sound]` | `1,467` | *(none — `0` uses)* | `7` hops via `Lean.Omega.combo_sat'` $\to \dots \to$ `funext` $\to$ `Quot.sound` |
| `omega_nat_sub_fn` | `st 0 + st 2 = st 3 → 0 < st 0 → (st 0 - 1) + (st 2 + 1) = st 3` | `omega` | `#[propext, Quot.sound]` | `1,467` | *(none — `0` uses)* | `7` hops via `Lean.Omega.combo_sat'` $\to \dots \to$ `funext` $\to$ `Quot.sound` |
| `omega_nat_conj` | `st 0 + st 2 = st 3 → st 0 = 0 → st 0 = 0 ∧ st 2 = st 3` | `omega` | `#[propext, Quot.sound, Classical.choice]` | `1,447` | `4` hops via `omega_nat_conj._proof_1` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `7` hops via `Classical.propDecidable` $\to$ `Classical.em` $\to$ `funext` $\to$ `Quot.sound` |
| `lia_nat_add` | `a < 100 → b < 100 → a + b < 200` | `lia` | `#[propext, Quot.sound, Classical.choice]` | `1,388` | `5` hops via `lia_nat_add._proof_1` $\to$ `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `5` hops via `Int.Internal.Linear.le_unsat` $\to$ `funext` $\to$ `Quot.sound` |
| `lia_nat_sub` | `a + b = k ∧ 0 < a → (a - 1) + (b + 1) = k` | `lia` | `#[propext, Quot.sound, Classical.choice]` | `2,083` | `5` hops via `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `5` hops via `Int.Internal.Linear.le_unsat` $\to$ `funext` $\to$ `Quot.sound` |
| `grind_nat_add` | `a < 101 → b < 101 → a + b < 202` | `grind` | `#[propext, Quot.sound, Classical.choice]` | `1,388` | `5` hops via `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `5` hops via `Int.Internal.Linear.le_unsat` $\to$ `funext` $\to$ `Quot.sound` |
| `grind_nat_sub` | `a + b = k ∧ 1 < a → (a - 2) + (b + 2) = k` | `grind` | `#[propext, Quot.sound, Classical.choice]` | `2,673` | `5` hops via `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `6` hops via `Lean.Grind.CommRing.le_norm_expr` $\to$ `Expr.denote_toPoly` $\to$ `funext` $\to$ `Quot.sound` |

This resolves three subtle audit questions for Anneal:

1. **Every `omega`, `lia`, and `grind` Proof Depends on `Quot.sound`:** Even on
   pure `Nat` addition (`omega_nat_add`), `omega`'s linear certificate checker
   (`Lean.Omega.combo_sat'`) proves linear combination equality via `funext`,
   which in Lean 4 is derived from quotient soundness (`Quot.sound`). Similarly,
   `lia` and `grind` invoke `Int.Internal.Linear.le_unsat` or
   `Lean.Grind.CommRing.le_norm_expr`, both of which depend on `funext` $\to$
   `Quot.sound`. Because `TrustedBoundary.lean:15–16` currently allows only
   `#[`propext, `Classical.choice]`, any theorem proved by `omega`, `lia`, or
   `grind`—or by `funext`—will fail the boundary audit until `` `Quot.sound ``
   is added to `allowedAxioms` (as Lean's third standard mathematical axiom; see
   also `loop_verified_sparse_awp_constructive` in
   `support/ProbeHoareWpFunIndAndReferences.lean:489–505` for how explicit
   `Nat.sub_add_cancel` / `Nat.add_assoc` lemmas avoid both `Quot.sound` and
   `Classical.choice`).
2. **Why `omega` Uses `Classical.choice` Only on Non-Atomic Propositional
   Goals:** On atomic linear arithmetic goals (`omega_nat_add`, `omega_nat_sub`,
   `omega_nat_sub_fn`), `omega` uses `Decidable.byContradiction` over decidable
   `Int` inequalities and never touches `Classical.choice`. However, when
   `omega` is invoked directly on a conjunction goal `P ∧ Q` (`omega_nat_conj`,
   as emitted by `SparseDCom.verificationConditions` on `loopProg`), `omega`'s
   front-end clausifier splits `¬ (P ∧ Q)` using `Classical.propDecidable` $\to$
   `Classical.choice`. Splitting the conjunction via `refine ⟨?_, ?_⟩` before
   calling `omega` eliminates `Classical.choice` completely.
3. **Why `lia` and `grind` Always Use `Classical.choice`:** Both `lia` and
   `grind` wrap their core refutation goal in `Classical.byContradiction`
   (5 hops to `Classical.choice`), regardless of whether the goal is an atomic
   `Nat` inequality or a propositional compound.

---

#### Finding 4: Mutable References, Store Typing (`StoreTy`), and Store Extension Monotonicity (`Extends`, `store_weakening`) in `TS/References.lean` (`STLCRef`) vs. Fuel-Bounded Reference Invariants in Anneal (`MirVal.satisfiesInv`)

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`TS/References.lean:1–777`, `TS/Stlc.lean:1–320`,
`TS/StlcProp.lean:1–450`), `joshlf/anneal` commit `the PME MIR operational semantics prototype (`support/`)`
(`theory/Anneal/MirValInv.lean`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`ReferencesProbe`, lines
981–1265).

##### 4.1 Why Naive Store-Indexed Typing Fails and How `StoreTy` + `Extends` Resolves It

When formalizing mutable references (`ref e`, `!e`, `e1 := e2`), a natural
first attempt is to parameterize value typing directly by the concrete runtime
store `ρ : Store := List Tm`, recursively checking that location `.loc l` has
type `.ref τ` whenever the stored value `ρ[l]` has type `τ`. As
`TS/References.lean:331–380` explains, this naive design fails for two reasons:

1. **Every Store Mutation Invalidates Existing Typing Derivations:** Writing to
   location `l'` (`ρ.set l' v`) changes the concrete store `ρ`, requiring every
   sub-term typing derivation in the program context to be rebuilt from scratch.
2. **Cyclic Reference Graphs Diverge:** If cell `0` contains a term referencing
   cell `1` and cell `1` contains a term referencing cell `0` (as in doubly
   linked lists, intrusive queues, or closures stored in mutable cells),
   re-typechecking `ρ[l]` at every `.loc l` lookup has no finite derivation
   without an artificial step-index fuel bound.

`TS/References.lean:383–762` resolves both problems via an extrinsic store
typing `StoreTy := List Ty` (`δ`) that assigns a fixed intended type `δ[l]?` to
each allocated cell `l : Nat`, decoupled from the cell's current runtime value:

1. **Constant-Time Location Lookup (`HasType.loc`):** `.loc l` has type `.ref τ`
   under `δ` whenever `δ[l]? = some τ`, without inspecting `ρ[l]`.
2. **Global Store Well-Typedness (`StoreWellTyped δ ρ`):** Holds when
   `δ.length = ρ.length` and every cell `l < ρ.length` satisfies
   `HasType δ ρ[l] δ[l]`.
3. **Monotonic Store Extension (`Extends δ' δ := δ.IsPrefixOf δ'`):** Because
   `STLCRef` stores are append-only on allocation (`ρ ++ [v]`) and
   type-invariant on mutation (`ρ.set l v`), `δ` only grows by appending new
   cell types (`δ ++ [τ]`).

`ReferencesProbe` in `support/ProbeHoareWpFunIndAndReferences.lean:981–1265`
mechanizes the complete `STLCRef` preservation chain and a 2-cell cyclic heap
witness (`cyclic_store_well_typed`, where cell `0` holds `!(loc 1); unit` and
cell `1` holds `!(loc 0); unit`):

| Theorem (`ReferencesProbe`) | Role in Store-Typing Architecture | Direct Proof `Expr.numObjs` | Marginal Closure (`Expr.numObjs`) | Transitive Module Closure (`Expr.numObjs`) | Marginal Kernel Replay (`us`) | Full Closure Kernel Replay (`us`) | Transitive Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `store_weakening` | `Extends δ' δ → HasType δ t τ → HasType δ' t τ` | `180` | `180` | `2,243` | `1,303` | `6,464` | `#[propext]` |
| `store_well_typed_alloc` | Allocation `ρ ++ [v]` preserves `StoreWellTyped (δ ++ [τ])` | `584` | `584` | `3,389` | `1,375` | `8,389` | `#[propext]` |
| `assign_pres_store_typing` | In-place mutation `ρ.set l v` preserves `StoreWellTyped δ` | `543` | `543` | `3,336` | `825` | `7,682` | `#[propext]` |
| `preservation` | Full small-step type + store preservation across 9 `Step` rules | `6,114` | `6,114` | `17,746` | `13,734` | `40,101` | `#[propext]` |
| `cyclic_store_well_typed` | Finite well-typedness proof for 2-cell mutually referential store | `514` | `514` | `861` | `1,664` | `3,363` | `#[propext]` |

##### 4.2 Mapping `StoreTy` and `Extends` to Anneal's `MirVal.satisfiesInv`

In Anneal (`the PME MIR operational semantics prototype (`support/`)`, `theory/Anneal/MirValInv.lean`), value invariants for
MIR references (`MirVal.ref loc`) are currently defined by recursion on a step
counter `fuel : Nat`:

```lean
def MirVal.satisfiesInv : Nat → Memory → MirVal → TyInv → Prop
  | 0, _, _, _ => False
  | fuel + 1, mem, .ref loc, .ref pointeeInv =>
      ∃ v, mem.lookup loc = some v ∧ MirVal.satisfiesInv fuel mem v pointeeInv
```

This `fuel`-indexed formulation forces every function call, loop iteration, and
dereference chain in a proof to decrement `fuel`, and cannot express cyclic
reference invariants at all. Adopting `TS/References.lean`'s `StoreTy` pattern
in `theory/Anneal/` replaces `fuel` with a region typing environment
`RegionEnv := Loc → Option TyInv` (`Δ`):

1. **Fuel-Free Value Invariant (`MirVal.satisfiesInv Δ v τ`):** For `.ref loc`
   and `.ref pointeeInv`, `MirVal.satisfiesInv Δ (.ref loc) (.ref pointeeInv)`
   Simply asserts `Δ loc = some pointeeInv` (zero `Memory` lookup, zero `fuel`
   parameter).
2. **Global Memory Well-Typedness (`Memory.WellTyped Δ mem`):** Asserts that for
   every `loc` and `inv` with `Δ loc = some inv`, there exists `v` such that
   `mem.lookup loc = some v ∧ MirVal.satisfiesInv Δ v inv`.
3. **Monotonic Allocation (`RegionEnv.Extends Δ' Δ`):** When a new stack slot or
   heap allocation is created at fresh location `loc`, `Δ' := Δ.insert loc inv`
   extends `Δ`. By the direct analogue of `store_weakening` (`180` DAG nodes),
   all existing local-variable invariants `MirVal.satisfiesInv Δ v τ` lift
   automatically to `Δ'` without re-inspecting `mem`, and in-place mutation of
   an existing `loc` with a value satisfying `Δ loc` preserves `Δ` identically
   (`assign_pres_store_typing`, `543` DAG nodes).

---

#### Finding 5: Metaprogramming Architecture of `LF/CustomTactics.lean` (`inversion`, `apply ... at ...`), Two-Part Root Cause and Fix (`inversion_fixed`) for `sf-in-lean` Issue #447 / PR #449, and the 14-Pattern `TrustedBoundary.lean` + `foundation-lock.json` Tactic Compatibility Matrix

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`LF/CustomTactics.lean:1–435`, `TS/AttributeDecls.lean:1–25`)
and PR #449 commit `0f74845c92a1`, `joshlf/anneal` commit `f938c18db56c`
(`trusted/audit/TrustedBoundary.lean:1–420`,
`trusted/cargo-anneal/foundation-lock.json`), and
`support/ProbeInversionBoundaryAndPlausible.lean` (`CustomTactics`,
`InversionProbe`, `BoundaryAuditProbe`, lines 52–875).

##### 5.1 Why Built-In `cases` Fails on Computed Index Expressions While `LF/CustomTactics.lean`'s `inversion` Succeeds

In Lean 4 (`Lean/Meta/Tactic/Cases.lean:160–277`), when `cases h` is invoked on
a hypothesis `h : I idx_1 ... idx_k` whose type is an indexed inductive family
with non-independent indices (`!hasIndepIndices ctx`), `MVarId.cases` executes:

1. `generalizeIndices goal h`: replaces each non-variable index `idx_i` with a
   fresh free variable `x_i` and introduces equality hypotheses `x_i = idx_i`
   plus `h ≍ h'`.
2. `inductionCasesOn`: eliminates `h'` into one `CasesSubgoal` per constructor.
3. `Lean.Meta.Cases.unifyCasesEqs`: calls `Lean.Meta.Cases.unifyEqs` to solve
   the index equations `ctor_idx_i = idx_i` in each constructor branch.

Crucially, `Lean.Meta.Cases.unifyEqs` calls `unifyEq?` and—if `unifyEq?` returns
`none` because one side is a non-constructor function application such as
`evalShift raw = 0`—**immediately throws a hard exception**:

```text
error: Dependent elimination failed: Failed to solve equation
  evalShift raw = 0
```

`LF/CustomTactics.lean:166–224` replaces `Lean.Meta.Cases.unifyEqs` with a
custom `Lean.Meta.unifyEqs`
(`support/ProbeInversionBoundaryAndPlausible.lean:183–194`) that wraps
`unifyEq?` in `observing?`:

```lean
let some { mvarId, subst, numNewEqs } ←
    Option.join <$> (observing? $ unifyEq? mvarId eq subst MVarId.acyclic caseName?)
  | unifyEqs eqs mvarId subst caseName?
```

When `unifyEq?` fails on `evalShift raw = 0`, `observing?` catches the failure,
leaves the unsolved index equation `heq : evalShift raw = 0` as a hypothesis in
the local context of the `zeroShift` subgoal, and continues unifying the
remaining equations (`out = x`). In `InversionProbe`
(`support/ProbeInversionBoundaryAndPlausible.lean:472–506`), `#guard_msgs`
verifies that built-in `cases h` fails on `ShiftStep (evalShift raw) out`,
whereas both `inversion +clear h` (`268` DAG nodes) and the
foundation-compatible idiom
`generalize hexp : evalShift raw = idx at h; cases h` (`313` DAG nodes)
succeed.

##### 5.2 Complete Two-Part Diagnosis and Fix (`inversion_fixed`) for `sf-in-lean` Issue #447 and PR #449 (`0f74845c`)

In `sf-in-lean` Issue #447 and open PR #449 (commit `0f74845c92a1`), users
reported that `inversion h with | ctor x y => ...` binds user-supplied variable
names to the wrong hypotheses or rejects `@ctor` syntax when constructors have
implicit parameters or unsolved index equations. By inspecting both `main`
(`13e9425b4647`) and PR #449 (`0f74845c92a1`), we identify two distinct bugs:

1. **Bug 1 on `sf-in-lean` `main` (`13e9425b4647`,
   `LF/CustomTactics.lean:245–272`):**
   - `evalInvAlt` matches only
     `` `(inductionAlt| | $tag:ident $vars* => $tactics) ``, rejecting explicit
     `@tag` patterns (`issue447_at_syntax_rejected` in
     `support/ProbeInversionBoundaryAndPlausible.lean:528–534`).
   - More importantly, `trySolveGoal` renames hypotheses by calling
     `Lean.Elab.Tactic.renameInaccessibles goal vars`. In Lean 4 core
     (`Lean/Elab/Tactic/RenameInaccessibles.lean`), `renameInaccessibles` walks
     `mvarDecl.lctx.decls.toList.reverse` **backwards from the end of the local
     context** and collects the **last** `vars.size` inaccessible hypotheses!
     When `inversion` leaves $k$ unsolved index/heterogeneous equations (`eq✝`,
     `heq✝`) at the end of `lctx` after the constructor fields (`f✝`, `hd✝`,
     `tl✝`), and a user writes `| cons a b =>` supplying fewer names than total
     inaccessibles, `renameInaccessibles` binds `a` and `b` to the **trailing
     equations** (`a : w ≍ IndexedWec.cons _ _ _`, `b : n + 1 = _`) instead of
     the first two constructor fields
     (`issue447_reverse_renaming_binds_trailing_eqs`, lines 539–547)!
2. **Bug 2 Introduced in PR #449 (`0f74845c92a1`):**
   - PR #449 attempted to fix Issue #447 by extracting `givenNames : Array
     AltVarNames` from the user's `inductionAlt` syntax and passing `givenNames`
     directly into `inductionCasesOn newGoal newTarget givenNames ctx`
     **before** `unifyCasesEqs` runs.
   - However, `inductionCasesOn` assigns user names to constructor fields
     **before index unification (`unifyCasesEqs`) eliminates fields determined
     by concrete indices**. On `NoStutter [3, 1, 1, 4]` where constructor
     `NoStutter.cons` has type `∀ {x y : Nat} {l : List Nat}, x ≠ y → NoStutter
     (y :: l) → NoStutter (x :: y :: l)`, the three implicit fields `{x y l}`
     are immediately unified with `3`, `1`, and `[1, 4]` and cleared by
     `unifyCasesEqs`. Passing `givenNames` to `inductionCasesOn` in `@cons` mode
     consumes the user's first three names on `{x, y, l}` before `unifyCasesEqs`
     deletes them from the context!

Our fix `inversion_fixed` (`renameInversionFieldsForward` in
`support/ProbeInversionBoundaryAndPlausible.lean:350–395`) solves both bugs:

- It runs **after** `unifyCasesEqs` and inspects `subgoal.fields`, where
  `unifyCasesEqs` has already applied `subst.apply`
  (`s.fields.map (subst.apply ·)`). Constructor fields that were unified with
  concrete terms (`3`, `1`, `[1, 4]`) are no longer `.fvar` expressions; only
  **surviving** constructor fields remain `.fvar`s in `subgoal.fields`.
- In default (`| tag vars* =>`) mode, it filters out surviving constructor
  fields whose constructor `BinderInfo` is non-explicit (`!bi.isExplicit`),
  while in explicit (`| @tag vars* =>`) mode it includes surviving implicit
  fields.
- Starting at the local-context index of the first surviving constructor field,
  it collects inaccessible hypotheses in **forward (left-to-right) order**,
  binding constructor fields first and trailing unsolved index equations
  afterward. Theorems `issue447_fixed_noStutter`,
  `issue447_fixed_indexedWec_forward_binding`, and
  `issue447_fixed_indexedWec_at_syntax` (lines 553–577) verify all three cases.

##### 5.3 The 14-Pattern `TrustedBoundary.lean` Preflight and `foundation-lock.json` Elaboration Matrix

Anneal enforces two orthogonal gates on Lean files:

1. **Source-Syntax Preflight (`trusted/audit/TrustedBoundary.lean`):** Applied
   only to files in the `Anneal.*` module hierarchy (`trusted/lean/`). It
   restricts top-level commands to `commandKinds`, restricts attributes to
   `allowedAttributeNames` (`simp`, `reducible`, `inline`, `specialize`), bans
   metaprogramming escape hatches (`by_elab`, `run_tac`, `eval_expr`) via
   `forbiddenSyntaxKinds`, and bans `decide +kernel` / `decide +native` via
   `inspectSyntax`.
2. **Import Closure Lock (`trusted/cargo-anneal/foundation-lock.json`):** Locks
   the transitive `.olean` module graph of `Anneal.Trusted` to 65 core `Init.*`
   modules rooted at `Init.NotationExtra` (which excludes `Init.Omega`,
   `Init.Grind`, and `Init.RCases`).

`BoundaryAuditProbe` (`support/ProbeInversionBoundaryAndPlausible.lean:625–874`)
tests 14 tactic and command snippets against both `TrustedBoundary.lean`'s
preflight parser and live elaboration under `Init.NotationExtra` vs.
`+Init.Omega/Grind/RCases`:

| # | Pattern / Tactic | `TrustedBoundary.lean` Preflight (Stock `f938c18db`) | `TrustedBoundary.lean` Preflight (With `s[1][0]` Fix) | Elaborates Under `Init.NotationExtra` (`foundation-lock.json`) | Elaborates Under `+Init.Omega/Grind/RCases` | Recommended Anneal Equivalent |
| :- | :--- | :---: | :---: | :---: | :---: | :--- |
| 1 | Custom `syntax` + `elab` (`inversion`, `apply ... at ...`) | **FAIL** (`unsupported command syntax`) | **FAIL** | PASS (if `Lean` imported) | PASS | Prohibited in `Anneal.*`; use `generalize + cases` or `replace h := f ... h` |
| 2 | Custom `macro` / `macro_rules` | **FAIL** (`unsupported command macro`) | **FAIL** | PASS | PASS | Prohibited in `Anneal.*`; expand macros in Rust generator or `theory/` |
| 3 | `register_label_attr` (`TS/AttributeDecls.lean`) | **FAIL** (`unexpected identifier`) | **FAIL** | **FAIL** (requires `Lean.LabelAttribute`) | **FAIL** | Pass explicit lemma lists: `apply_rules [lem1, lem2]` |
| 4 | Custom `@[SimpleArith]` attribute | **FAIL** (`unsupported attribute`) | **FAIL** | **FAIL** | **FAIL** | Use `@[simp]` or explicit lemma lists `[lem1, lem2]` |
| 5 | `by_elab` / `run_tac` inside `by ...` | **FAIL** (`forbidden syntax kind runTac`) | **FAIL** | **FAIL** | **FAIL** | Prohibited everywhere in Anneal |
| 6a | `native_decide` / `decide +kernel` inside `by ...` | **FAIL** (`forbidden decide configuration '+kernel'`) | **FAIL** | PASS | PASS | Prohibited (`Lean.ofReduceBool` / `Lean.trustCompiler`) |
| 6b | **Bare `by decide`** (no config flags) | **FAIL** (`forbidden decide configuration ''`) | **PASS** | **PASS** | **PASS** | Fix `TrustedBoundary.lean:366` (`s[1][0].getArgs.isEmpty`) |
| 7 | `cases` + `generalize` + `injections` + `subst_vars` | **PASS** | **PASS** | **PASS** | **PASS** | Direct drop-in replacement for `inversion` (`313` vs. `268` DAG nodes) |
| 8 | `apply_rules [lem1, lem2]` (explicit list) | **PASS** | **PASS** | **PASS** | **PASS** | Built into `Init.Tactics`; `30` DAG nodes on `EvenInd 8` |
| 9 | `solve_by_elim [lem1, lem2]` (explicit list) | **PASS** | **PASS** | **PASS** | **PASS** | Built into `Init.Tactics`; `30` DAG nodes on `EvenInd 8` |
| 10 | `fun_induction` / `fun_cases` inside `by ...` | **PASS** | **PASS** | **PASS** | **PASS** | Built into `Init.Tactics`; use in `theory/` (`#[propext]`) |
| 11 | `omega` inside `by ...` | **PASS** | **PASS** | **FAIL** (`Unknown constant Lean.Omega...`) | **PASS** | Add `Init.Omega` to imports + `` `Quot.sound `` to `allowedAxioms` |
| 12 | `lia` / `grind` inside `by ...` | **PASS** | **PASS** | **FAIL** (`Unknown constant Lean.Grind.ToInt`) | **PASS** | Add `Init.Grind` to imports + `` `Quot.sound `` to `allowedAxioms` |
| 13 | `rcases` / `obtain` inside `by ...` | **FAIL** (`unknown tactic` under `Init.NotationExtra` parser) | **FAIL** | **FAIL** | **PASS** | Use Lean 4 built-in `rcases`-free `cases` / `obtain`-free `have ⟨x, hx⟩ := h` or import `Init.RCases` |

**Diagnosis of the Bare `by decide` Bug in `TrustedBoundary.lean:366`
(Snippet 6b):** In `trusted/audit/TrustedBoundary.lean:364–367`, the auditor
checks whether `decide` or `decide!` was passed configuration flags (`+kernel`
or `+native`) by inspecting `s[1].getArgs.isEmpty`:

```lean
if (k == ``Lean.Parser.Tactic.decide || k == ``Lean.Parser.Tactic.decide!) &&
    !s[1].getArgs.isEmpty then
  throw s!"forbidden decide configuration '{s[1].reprint.getD ""}' in {modName}"
```

In Lean `v4.34.1`, `s[1]` is a `Lean.Parser.Tactic.optConfig` node whose child
array is `#[nullNode]` (size `1`), where the inner `nullNode` (`s[1][0]`) holds
the actual `configItem` arguments. Consequently, on bare `by decide`,
`s[1].getArgs.isEmpty` evaluates to `false` (because
`#[mkNullNode #[]].size == 1`), falsely rejecting every bare `by decide` with
`forbidden decide configuration ''`! Changing `!s[1].getArgs.isEmpty` to
`!s[1][0].getArgs.isEmpty` (verified in
`support/ProbeInversionBoundaryAndPlausible.lean:725–727`) accepts bare
`by decide` while continuing to reject `decide +kernel` and `decide +native`.

---

#### Finding 6: Property-Based Negative Canaries and Pre-Proof Specification Falsification with `leanprover-community/plausible` (`v4.34.0`) + `Chamelean` (PR #56), `subtypeVarTestable` Priority-2000 Constrained Sampling, and the `UInt*` / `BitVec` `maxSize = 100` Capping Pitfall

Basis: `source + execution + derived` — `leanprover-community/plausible`
`v4.34.0` commit `118aa17ee846` (`Plausible/Testable.lean:1–510`,
`Plausible/Sampleable.lean:1–180`, `Plausible/Arbitrary.lean:1–160`,
`Plausible/DeriveArbitrary.lean`) and PR #56 commit `f48022651ffa`
(`Plausible/Chamelean/`), `joshlf/anneal` commit `the Miri differential testing prototype (`support/`)` (Issue #228 /
PR #82 Miri differential testing), and
`support/ProbeInversionBoundaryAndPlausible.lean` (`PlausibleCanaryProbe`,
lines 876–1350).

##### 6.1 `Plausible` (`v4.34.0`) Architecture and `@[instance 2000] subtypeVarTestable`

`leanprover-community/plausible` (`v4.34.0`) separates random generation and
shrinking (`Arbitrary α`, `Shrinkable α`, bundled via `SampleableExt α` with an
explicit `proxy : Type` and `interp : proxy → α` for non-computable or dependent
types) from proposition evaluation (`Testable (p : Prop)`). When testing a
universally quantified implication `∀ x : α, p x → q x`,
`Plausible/Testable.lean` provides two competing typeclass instances:

1. **Naive Rejection Sampling (`decGuardTestable` at priority `500` +
   `varTestable` at priority `1000`):** Generates an unconstrained `x : α` via
   `SampleableExt α`, evaluates `decide (p x)`, and if `p x` is false, returns
   `TestResult.gaveUp 1` (retrying up to `cfg.numRetries := 10` times per
   instance).
2. **Constrained Subtype Sampling (`subtypeVarTestable` at `@[instance 2000]`,
   `Plausible/Testable.lean:448–457`):** Whenever a constrained generator
   instance `SampleableExt { x : α // p x }` (or `Arbitrary { x : α // p x }`)
   is in scope, `subtypeVarTestable` overrides `varTestable + decGuardTestable`
   at priority `2000`, rewriting `∀ x : α, p x → q x` into
   `∀ s : { x : α // p x }, q s.val`. Every sample satisfies `p x` by
   construction with zero rejected draws!

In `plausible` PR #56 (commit `f48022651ffa`), `Plausible/Chamelean/` adds
`derive_generator` and `derive_checker` macros that automatically synthesize
constrained `Arbitrary { x : α // P x }` generators and `DecOpt` checkers for
inductive relations `P x`, plugging directly into `subtypeVarTestable`.

##### 6.2 Empirical Evaluation: Negative Canaries, Sparse Preconditions, and the `UInt*` Size-Capping Pitfall

`PlausibleCanaryProbe`
(`support/ProbeInversionBoundaryAndPlausible.lean:876–1350`) runs 8 benchmarks
across three Anneal verification scenarios:

1. **Semantic Mutant Canaries (Issue #228 / PR #82 Style):** Testing a mutated
   MIR binary operator evaluator against reference semantics
   (`evalMirBinOpRef`):
   - *Canary 1a (`MirBinOp.shlUnchecked` missing `rhs >= 8` UB guard):*
     Falsified in `1.59 ms` and shrunk in `6` steps to the minimal
     counterexample `[op := .shlUnchecked, lhs := 0, rhs := 8]`.
   - *Canary 1b (`MirBinOp.subChecked` off-by-one `lhs <= rhs` underflow flag):*
     Falsified in `0.21 ms` at `[op := .subChecked, lhs := 0, rhs := 0]`.
2. **Sparse Memory-Frame Well-Formedness (`ValidFrame`) — Rejection Sampling vs.
   Constrained Subtype Generation:** Testing an off-by-one dereference-bounds
   mutant (`offset + accessLen < allocSize` instead of `≤`) under a sparse
   alignment + tight-allocation invariant (`alignExp = 4 ∧ offset % 16 = 0 ∧
   offset + accessLen = allocSize`):
   - *Canary 2a (Naive rejection sampling via `decGuardTestable`):* `GAVE UP`
     after `500` consecutive discarded precondition failures (`2.47 ms`),
     failing to test a single valid frame!
   - *Canary 2b (`Chamelean`-style constrained `Arbitrary { f : MirFrame //
     ValidFrame f }` via `subtypeVarTestable` at priority `2000`):* Falsified in
     `0.27 ms` with zero discarded samples at
     `{ allocSize := 4, alignExp := 4, offset := 0, accessLen := 4 }`.
3. **Pre-Proof Specification Falsification and the `UInt8.Arbitrary` `maxSize`
   Pitfall:** Consider a candidate alignment helper in `theory/Anneal/`:
   `alignUpBitwise (addr align : UInt8) : UInt8 :=`
   `(addr + (align - 1)) &&& ~~~(align - 1)`.
   - *Spec Falsification 3a (Missing `isPowerOfTwoU8 align` precondition on
     `align > 0 → alignUpBitwise addr align % align = 0`):* Falsified in
     `1.12 ms` and shrunk in `1` step to `[addr := 1, align := 3]`.
   - *Spec Falsification 3b-default (Testing `isPowerOfTwoU8 align = true →
     alignUpBitwise addr align >= addr` at default `maxSize := 50` or `100`):*
     **Falsely reports `SUCCESS` (`3.31 ms`)!** Why? Because in
     `Plausible/Arbitrary.lean:94–129`, the stock `Arbitrary` instances for
     `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` are implemented as:

     ```lean
     instance : Arbitrary UInt8 where
       arbitrary := do
         let d ← Gen.choose Nat 0 (min (← Gen.getSize) UInt8.size)
         return UInt8.ofNat d
     ```

     Because `Gen.getSize` is bounded by `cfg.maxSize` (default `100`), stock
     `Plausible` **never generates `UInt8` values above `100`** (or `UInt32` /
     `UInt64` / `USize` values above `100`)! Consequently, any bug or missing
     precondition triggered by fixed-width arithmetic wrapping (`addr + align -
     1 >= 256` on `UInt8`, or `>= 2^32` on `UInt32`) is completely invisible to
     default `plausible` configurations.
   - *Spec Falsification 3b-full (Overriding with boundary-weighted
     `FullRangeUInt8` that mixes corner values `#[0, 1, 127, 128, 254, 255]`
     with uniform `0..255` regardless of `maxSize`):* Falsifies the missing
     overflow guard in `0.39 ms` at `[addr := 165, align := 128]` (where
     `165 + 127 = 292 ≡ 36 (mod 256) < 165`).
   - *Spec Verification 3c (Corrected specification adding `addr.toNat +
     align.toNat - 1 < 256` with `FullRangeUInt8`):* Passes `200/200` instances
     in `8.73 ms`.

| Benchmark Case (`PlausibleCanaryProbe`) | Generator / `Testable` Path | Execution Time | Shrinking Steps | Outcome & Counterexample |
| :--- | :--- | ---: | ---: | :--- |
| **Canary 1a:** `MirBinOp.shlUnchecked` missing `rhs >= 8` UB guard | Derived `Arbitrary` + `varTestable` | `1.59 ms` | `6` | **FAILURE:** `[op := .shlUnchecked, lhs := 0, rhs := 8]` |
| **Canary 1b:** `MirBinOp.subChecked` off-by-one `lhs <= rhs` flag | Derived `Arbitrary` + `varTestable` | `0.21 ms` | `0` | **FAILURE:** `[op := .subChecked, lhs := 0, rhs := 0]` |
| **Canary 2a:** Sparse `ValidFrame` under naive rejection sampling | `decGuardTestable` (priority `500`) | `2.47 ms` | — | **GAVE UP** after `500` discarded precondition failures |
| **Canary 2b:** Sparse `ValidFrame` under constrained subtype generator | `subtypeVarTestable` (priority `2000`) | `0.27 ms` | `0` | **FAILURE:** `[{ allocSize := 4, alignExp := 4, offset := 0, accessLen := 4 }]` |
| **Spec 3a:** `alignUpBitwise` without `isPowerOfTwoU8 align` | Stock `UInt8.Arbitrary` | `1.12 ms` | `1` | **FAILURE:** `[addr := 1, align := 3]` |
| **Spec 3b-default:** `alignUpBitwise` without overflow guard (`maxSize := 50`) | Stock `UInt8.Arbitrary` (`min size 256`) | `3.31 ms` | — | **FALSE SUCCESS** (blind to `addr + align - 1 >= 256` due to `getSize` cap) |
| **Spec 3b-full:** `alignUpBitwise` without overflow guard (`FullRangeUInt8`) | Boundary-weighted `FullRangeUInt8` | `0.39 ms` | `0` | **FAILURE:** `[addr := 165, align := 128]` |
| **Spec 3c:** Corrected `alignUpBitwise` spec (`FullRangeUInt8`) | Boundary-weighted `FullRangeUInt8` | `8.73 ms` | — | **SUCCESS** (`200/200` instances passed) |

**Trust Boundary Placement for `Plausible` in Anneal:** `Plausible`'s
`plausible` tactic closes goals with `sorryAx` after random testing passes, and
its runner uses `IO` and `StdGen`. Therefore, `Plausible` must **never** be
imported into `trusted/lean/` (`Anneal.*`) or `theory/Anneal/` production proof
modules. Instead, it belongs in a dedicated non-TCB test target (e.g.,
`tests/lean-canaries/`) that imports `Anneal.MirSemantics` and `theory/Anneal/`
definitions alongside boundary-weighted `FullRangeUInt*` / `BitVec` generators
and `SampleableExt { x // Valid* x }` instances.

## Boundaries

### Part I — Adversarial Proof Grading (`comparator-autograder`), Match Splitter Deduplication, and `.olean` Realization Auditing

- **Lean toolchain version specificity:** All compiler and environment findings
  were observed on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
  Whether later Lean releases change `MatcherKey`, `matcherExt`'s `asyncMode`,
  `Lean.Parser.Tactic.decide`'s syntax tree layout, or `MatchEqs.lean`'s
  `isReservedName` implementation under `loadExts := false` was **not
  examined**.
- **Module-system `isPrivate` flag in `MatcherKey`:** In
  `mkMatcherAuxDefinition` (`Lean/Meta/Match/Match.lean:1098`), `MatcherKey`
  sets `isPrivate := env.header.isModule && isPrivateName name`. Behavior under
  Lean's experimental `module` header mode (`env.header.isModule == true`) is
  **unsupported** by Anneal (`TrustedBoundary.lean:544` explicitly rejects
  `Elab.HeaderSyntax.isModule header`) and was **not examined**.
- **Scope of `isRealizedCompilerConstant`:** The structural predicate
  `isRealizedCompilerConstant` verified in Finding 5 covers Lean `v4.34.1`'s
  built-in equation, congruence, functional-induction/cases, injection,
  `sizeOf`, and matcher `.splitter` realizations for declarations already
  admitted in `locals`. Custom user-registered `registerReservedNameAction`
  extensions cannot run when `loadExts := false` and are **known not to apply**
  under Anneal's `prelude` + `Init` foundation policy.

### Part II — Literate Verification (`SFLCompat`/`SFLMeta`, `Verso`/`SubVerso`/`Illuminate`), Declaration Drift Checking (`sf_recall`), and Anneal Tutor

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

### Part III — Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration (`inversion`), and `Plausible` Negative Canaries

The conclusions and measurements in this report are bounded by the following
scope conditions:

1. **Toolchain and Repository Versions:** All `.olean` DAG object counts
   (`Expr.numObjs`), kernel replay timings (`Lean.Kernel.Environment.replay`),
   and transitive axiom closures were measured on Lean `v4.34.1` (commit
   `5045d0056413`). Future Lean releases may alter the equation compiler's
   splitter generation, `AuxDeclCache` deduplication, or `omega`/`grind` proof
   terms.
2. **Loop-Free vs. Loop-Heavy Control Flow for `SparseDCom.awp`:** Backward
   weakest-precondition substitution (`awp`) achieves `3.2x`–`3.3x` DAG
   reductions on straight-line and moderate diamond CFGs, but nests
   exponentially on sequences of $D$ back-to-back diamond branches without
   intermediate cut-points ($O(2^D)$ duplication of the postcondition). In
   Anneal's MIR verification pipeline, join blocks shared by multiple branches
   should therefore carry cut-point assertions (hybrid `SparseDCom`) whenever a
   join block's continuation exceeds a small AST size threshold.
3. **First-Order Data vs. Higher-Order Stored Closures in `StoreTy`:**
   `TS/References.lean`'s extrinsic `StoreTy` (`RegionEnv`) eliminates fuel
   indexing for arbitrary cyclic graphs of first-order mutable references (the
   fragment relevant to safe and unsafe Rust data structures without mutable
   function-pointer/trait-object self-application through the heap).
   Higher-order self-referential code pointers stored in mutable memory
   (Landin's knot) still require step-indexed logical relations if termination
   is proved, though type and invariant safety (`StoreWellTyped`) remains
   fuel-free.
4. **`Chamelean` Generator Synthesis Scope (`plausible` PR #56):** Automated
   `derive_generator` synthesis in `Plausible/Chamelean/` currently targets
   inductive relations whose mode constraints decompose into constructor
   unification and recursive sub-generators; arithmetic bit-vector and alignment
   relations (`ValidFrame`) require either handwritten `Arbitrary { x // P x }`
   instances (12 lines in
   `support/ProbeInversionBoundaryAndPlausible.lean:1197–1211`) or SMT/interval
   combinators.

## Evidence

### Part I — Adversarial Proof Grading (`comparator-autograder`), Match Splitter Deduplication, and `.olean` Realization Auditing

- **`plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257`):**
  - `AUTOMATED-GRADING.md:1-145` (maintainer documentation of the `List.IsNil`
    / `List.In` match deduplication failure).
  - `SFLMeta/Grade.lean:1-110` and `SFLMeta/Save/Extract.lean:627-634,691-696`
    (extraction of `student`, `solutions`, `terse`, and `grading` variants).
  - `gradescope/package.py:115-187` and `gradescope/grade.py:137-335`
    (dual-tree `Challenge`/`Solution` staging and per-chapter fallback).
  - `TS/MoreStlc.lean:2967,3043,3125` (`@[autogradedHole]` annotations on
    theorems `progress`, `substitution_preserves_typing`, and `preservation`).
- **`plclub/comparator-autograder` (`facc6c7498298d2286f18c9fc5eb5e902551b6aa`)
  and `plclub/comparator-autograder-lib`
  (`57f6879141b701cc02fe99d7a7e834c38409a6bc`):**
  - `ComparatorAutograderLib.lean:1-48` (`autogradedProofAttr` and
    `autogradedHoleAttr`).
  - `ComparatorAutograder/MainSupport.lean:23-54` (`collectAutograded` and
    `AUTOGRADER_SKIP_IMPORTS`).
  - `ComparatorAutograder/Comparator.lean:70-184` (`inductiveHoleMatches`,
    `Compare.loop`, `compareTheoremAt`, and `myVerifyMatch`).
- **`xhalo32/comparator` (`a6cc98304bd7f3ad3d030fc37a75e4b872342da6`) and
  `leanprover/lean4export` (`076e8e57707e813375e8f9da8bf989799ace9680`):**
  - `Comparator/MainSupport.lean:1-361` (commits `aa6ce7f` and `d6400b2`,
    `safeExport` with `--ignore-missing` and `LEAN_ABORT_ON_PANIC=1`,
    `runBuiltinKernel`).
  - `Comparator/Util.lean:18-30` (derived syntactic `BEq` on `ConstantInfo`).
  - `Export.lean:232-252` (`dumpConstant` `--ignore-missing` handling and
    rejection of `unsafe`/`partial`/`opaque`).
- **`leanprover/lean4` (`v4.34.1`,
  `5045d0056413266e57c625dcd7c365b10e377c52`):**
  - `src/Lean/Meta/Match/Match.lean:1074-1126` (`MatcherKey`, `matcherExt` with
    `asyncMode := .local`, and `mkMatcherAuxDefinition`).
  - `src/Lean/Meta/Match/MatchEqs.lean:147-150,338` (`.splitter` emitted as
    private `.defnDecl`; `isMatcherCore` querying `Match.Extension`).
  - `src/Lean/Environment.lean:1271-1278,1872,2268-2344` (`asyncMode := .local`,
    `foldStage2` `.olean` serialization of realized constants, and
    `subsumesInfo` import merging).
- **`joshlf/anneal` (`f938c18db56c49e82dde95506894a9b58b76b227`):**
  - `trusted/audit/TrustedBoundary.lean:160,366,422-528,658-1305,1341-1482`
    (`importEnv` with `loadExts := false`, `inspectSyntax` `decide` check,
    `inspectCommand`, `declarationEdges`, `classifyTrustedConstant`,
    `checkTrustedNonContamination`, `collectActiveCandidateFeatures`, and
    `verifyAndCollectLocals`).
- **Preserved executable probes (observed `2026-11-02`):**
  - `support/ProbeComparatorAndMatcherDedup.lean` (SHA-256
    `80816e083d1d9273697f2d014a73b7c520562b84595d5cbdfb9aa6ab517dadce`).
  - `support/ProbeTrustedBoundaryFixes.lean` (SHA-256
    `7f07d9f881ac61e7170c578b8ab6295bccd0408109021a8a57bbeb46bd69a805`).

### Part II — Literate Verification (`SFLCompat`/`SFLMeta`, `Verso`/`SubVerso`/`Illuminate`), Declaration Drift Checking (`sf_recall`), and Anneal Tutor

#### Primary Git Sources Examined

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
  `f938c18db56c49e82dde95506894a9b58b76b227 (with the 6-chapter ITree/Std Tutor specimen embedded in `support/ProbeExperimentAndTutorAudit.lean`)`):**
  - `trusted/audit/TrustedBoundary.lean:36-42, 129-140, 533-564`
    (`commandKinds`, `inspectSource`, `verifyAudit`).
  - `docs/tutor/README.md`, `docs/tutor/01-basic-usage-and-outputs.md` through
    `docs/tutor/06-agentic-proof-workflow.md`,
    `docs/tutor/workflow/README.md:107-155`,
    `docs/tutor/workflow/tutor_workflow.py:1-365`, and
    `docs/tutor/workflow/tutor.toml:1-416` on `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`.
  - `trusted/lean/Trusted/Refinement.lean:51-55, 227-281`,
    `trusted/lean/Trusted/VerificationResult.lean:89-190`,
    `theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean:2156-2172`, and
    `tests/refinement/ConcreteYDiagram.lean:94-105` on `the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`.

#### Preserved Package Artifacts

| Path | SHA-256 | Contents |
| :--- | :--- | :--- |
| `support/ProbeRecallAndMatcherExt.lean` | `855cd6e5df5b844d228b91a0c790b9efcb62939b5bbd0db16bc214fbb442c40f` | Self-contained Lean `v4.34.1` probe embedding `SFLCompat.Recall` (`sf_recall`, `sf_recall +strictUniverse`, `sf_recall statement`), positive/negative Anneal drift checks, unchecked metadata tests, all 5 matcher/cross-module `matcherExt` edge cases, and `sf_recall_fixed` (`renameExact` + `unfoldMatchersIn`). |
| `support/ProbeExperimentAndTutorAudit.lean` | `dd71a980db642a3ef2f774abe87b4aee74688135f86a24b03607ece66004f479` | Self-contained Lean `v4.34.1` probe embedding `SFLCompat.Experiment` (`sf_experiment`, `sf_expect_failure_in`, `rawCommandBlock`), `Elab.async` `snapshotTasks` verification, `withRestoringState` `ngen` `FVarId` collision reproduction and fix, Anneal Tutor (`the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`) unmanaged block drift audit, `Kernel.Environment.replay` (`Init + Std` only), and `TrustedBoundary.inspectSource` closed-parser check. |

### Part III — Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration (`inversion`), and `Plausible` Negative Canaries

All claims in this report are backed by pinned upstream source files and two
self-contained runnable Lean `v4.34.1` support probes in this package:

- **Support Probes in `support/`:**
  - `support/ProbeHoareWpFunIndAndReferences.lean` (SHA-256:
    `aa086a55e108e6e6853dc5e65deda05ccd7f72219b16ac8dc822c37cd2e78065`):
    Mechanizes `HoareVCProbe` (`diamondProg`, `chain8Prog`, `loopProg` across
    Hoare rules, `FullDCom`, and `SparseDCom.awp`), `FunInductionProbe`
    (`optimizeAExp` and `optMirConstPropStmt` across structural
    `induction`/`cases`, `fun_induction`, and `fun_cases`), `ReferencesProbe`
    (`STLCRef` `Store`, `StoreTy`, `Extends`, `store_weakening`,
    `store_well_typed_alloc`, `assign_pres_store_typing`, `preservation`,
    `cyclic_store_well_typed`), `AxiomClosureProbe` (`omega_nat_add`,
    `omega_nat_sub`, `omega_nat_sub_fn`, `omega_nat_conj`, `lia_nat_add`,
    `lia_nat_sub`, `grind_nat_add`, `grind_nat_sub`), and the `ProbeHarness`
    measurement and kernel replay driver.
  - `support/ProbeInversionBoundaryAndPlausible.lean` (SHA-256:
    `b8078e5e1503c87961468156fd30e099ebe0fb4177cb4a0606eeeb001a917f14`):
    Mechanizes `CustomTactics` (`inversion`, `inversion_fixed` with
    `renameInversionFieldsForward`, `apply ... at ...`), `InversionProbe`
    (`ShiftStep`, `NoStutter`, `IndexedWec`, `#guard_msgs` proofs of Issue #447
    and PR #449 failure modes and fixes, and `Expr.numObjs` + `Kernel.check`
    comparisons), `BoundaryAuditProbe` (14-snippet `TrustedBoundary.lean`
    preflight + `s[1][0].getArgs.isEmpty` fix + `Init.NotationExtra` vs.
    `+Init.Omega/Grind/RCases` elaboration matrix), and `PlausibleCanaryProbe`
    (self-contained `Plausible` `v4.34.0` engine and 8 MIR negative-canary and
    specification-falsification benchmarks).
- **Upstream Source Code Examined:**
  - `plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257` and PR #449
    `0f74845c92a17fc896ab5893106ce2c0e3fbba3b`): `LF/CustomTactics.lean`,
    `HL/Slang.lean`, `HL/Imp.lean`, `HL/Equiv.lean`, `HL/Hoare.lean`,
    `HL/Hoare2.lean`, `TS/Smallstep.lean`, `TS/Stlc.lean`, `TS/StlcProp.lean`,
    `TS/References.lean`, `TS/AttributeDecls.lean`.
  - `leanprover-community/plausible`
    (`118aa17ee84656b8bd727fef7c458ee8c833385c`, `v4.34.0`, and PR #56
    `f48022651ffaa28b272b7328d07bf9450947c97a`): `Plausible/Testable.lean`,
    `Plausible/Sampleable.lean`, `Plausible/Arbitrary.lean`,
    `Plausible/DeriveArbitrary.lean`, `Plausible/Attr.lean`,
    `Plausible/Chamelean/`.
  - `leanprover/cslib` (`f7ec4db9f911a26c8c331fd48d1d464efde9e2a4`):
    `Cslib/Foundations/Semantics/LTS/Basic.lean`, `Simulation.lean`,
    `Bisimulation.lean`.
  - `joshlf/anneal` (`f938c18db56c49e82dde95506894a9b58b76b227`,
    `f938c18db56c49e82dde95506894a9b58b76b227 (with PME operational semantics formulation preserved in `support/`)`, and
    `f938c18db56c49e82dde95506894a9b58b76b227 (with Miri differential testing formulation preserved in `support/`)`):
    `trusted/audit/TrustedBoundary.lean`,
    `trusted/cargo-anneal/foundation-lock.json`,
    `theory/Anneal/Verification/BuildingBlocks.lean`,
    `trusted/lean/Anneal/MirSemantics.lean`, `theory/Anneal/MirPassProofs.lean`,
    `theory/Anneal/MirValInv.lean`.

## Revalidation

### Part I — Adversarial Proof Grading (`comparator-autograder`), Match Splitter Deduplication, and `.olean` Realization Auditing

Run both self-contained Lean `v4.34.1` support probes from the repository root
(or any working directory):

```console
lean --run reports/sf-in-lean-comparator-autograder-matcher-dedup-and-anneal-audit-2026/support/ProbeComparatorAndMatcherDedup.lean
lean --run reports/sf-in-lean-comparator-autograder-matcher-dedup-and-anneal-audit-2026/support/ProbeTrustedBoundaryFixes.lean
```

Each script compiles its embedded probe modules in a temporary directory,
verifies every finding via programmatic assertions, and exits with code `0`
only if all assertions hold:

1. `ProbeComparatorAndMatcherDedup.lean` checks Findings 2 and 3 (`Template`
   vs. `Submission` `.match_1` collision on `LF.Poly.List.In._f`,
   `Kernel.isDefEqGuarded` vs. `ConstantInfo` `BEq`, namespace and motive-sort
   collision invariance, `if-then-else` avoidance, `-DElab.async=true` vs.
   `-DElab.async=false` theorem matcher sharing, `inductiveHoleMatches`
   constructor spoofing via `Even.cheat`, and `.thmInfo` `BEq` rejection).
2. `ProbeTrustedBoundaryFixes.lean` checks Findings 4 and 5 (all three
   compounding `.match_1` contamination failures in stock
   `TrustedBoundary.lean` and the `isPureVettedMatcher` + `statusMap` override
   fix, `.match_1.splitter` `.defnInfo` and `Lean.isReservedName` under
   `loadExts := false`, Phase 1 + Phase 2 `isRealizedCompilerConstant` +
   `Kernel.Environment.replay` verification across sibling modules, and Phase 1
   `decide` `optConfig` handling).

### Part II — Literate Verification (`SFLCompat`/`SFLMeta`, `Verso`/`SubVerso`/`Illuminate`), Declaration Drift Checking (`sf_recall`), and Anneal Tutor

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
4. Anneal Tutor (`the ITree/Std Tutor specimen (`support/ProbeExperimentAndTutorAudit.lean`)`) unmanaged block audit: passed 3 up-to-date blocks, caught 4 representative drifted blocks
5. `TrustedBoundary.inspectSource` closed parserEnv (Init+Std): pure Lean=Except.ok 3, custom `sf_recall`=Except.error (rejected as expected)
```

### Part III — Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration (`inversion`), and `Plausible` Negative Canaries

To reproduce every measurement, proof check, `#guard_msgs` assertion, boundary
audit table, and negative-canary benchmark in this report from a clean
checkout, run the two self-contained support probes with Lean `v4.34.1`:

```bash
  # 1. Verify SHA-256 checksums of the support probes
sha256sum \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeHoareWpFunIndAndReferences.lean \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeInversionBoundaryAndPlausible.lean

  # 2. Run Probe 1: Hoare/WP VCs, fun_induction/fun_cases, STLCRef store typing,
  #    kernel replay benchmarks, and omega/lia/grind transitive axiom closures
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean --run \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeHoareWpFunIndAndReferences.lean

  # 3. Run Probe 2: LF/CustomTactics.lean (inversion, Issue #447 / PR #449 fix),
  #    14-snippet TrustedBoundary.lean preflight & foundation elaboration matrix,
  #    and Plausible v4.34.0 negative canaries & spec falsification
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean --run \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeInversionBoundaryAndPlausible.lean
```

Revalidate this report when:

- Anneal upgrades its pinned Lean toolchain beyond `v4.34.1` or modifies
  `trusted/audit/TrustedBoundary.lean` or
  `trusted/cargo-anneal/foundation-lock.json`.
- `plclub/sf-in-lean` merges PR #449 or updates `LF/CustomTactics.lean` or
  `HL/Hoare2.lean`.
- `leanprover-community/plausible` merges PR #56 (`Chamelean`) or changes the
  default `Arbitrary` instances for `UInt8`..`UInt64`, `USize`, or `BitVec` in
  `Plausible/Arbitrary.lean`.
