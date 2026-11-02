<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Adversarial Proof Grading, Match Splitter Deduplication, and `.olean` Realization Auditing in `sf-in-lean` and Anneal (`v4.34.1`)

## Summary

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

## Applicability

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

## Findings

### Finding 1: Architecture of the 5-Component `sf-in-lean` Autograding Pipeline, `xhalo32/comparator` (`ignore-missing-4.34.0`) vs. Upstream `leanprover/comparator`, and `gradescope/grade.py` Dual-Tree Staging

`Basis: source + derived`

#### 1.1 Pipeline Component Roles

The `sf-in-lean` grading stack spans five repositories:

| Component | Revision | Role in Pipeline |
| :--- | :--- | :--- |
| `plclub/sf-in-lean` | `13e9425b4647402a09316c1d39fa555e9bc3c257` | Verso book source (`LF/`, `HL/`, `TS/`), variant extractor (`SFLMeta/Save/Extract.lean`), local verifier (`scripts/grading_check.py`), and Gradescope harness (`gradescope/`). |
| `plclub/comparator-autograder-lib` | `57f6879141b701cc02fe99d7a7e834c38409a6bc` | Defines `@[autogradedProof <rat>]` and `@[autogradedHole]` parametric attributes (`ComparatorAutograderLib.lean:1-48`). |
| `plclub/comparator-autograder` | `facc6c7498298d2286f18c9fc5eb5e902551b6aa` | Discovers graded attributes in `Challenge`, invokes `Comparator.M.run compareIt`, and grades each theorem independently (`ComparatorAutograder/Comparator.lean:1-185`). |
| `xhalo32/comparator` | `a6cc98304bd7f3ad3d030fc37a75e4b872342da6` | Fork of `leanprover/comparator` (`ignore-missing-4.34.0` branch) providing `landrun`-sandboxed `lake build` and `lean4export` execution plus in-process `Lean.Kernel.Environment.replay`. |
| `leanprover/lean4export` | `076e8e57707e813375e8f9da8bf989799ace9680` | Imports `.olean` modules via `Lean.importModules` and serializes target constants and their transitive closures into NDJSON (`Export.lean:1-438`). |

#### 1.2 Exact Diff in `xhalo32/comparator` (`a6cc983`) vs. Upstream `leanprover/comparator` (`d03acab`)

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

#### 1.3 Attribute Extraction and Per-Theorem Grading Flow

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

#### 1.4 Dual-Tree Staging and Per-Chapter Recovery in `gradescope/grade.py`

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

### Finding 2: Three Soundness and Completeness Flaws in `plclub/comparator-autograder` (`@[autogradedHole]` Inductive Constructor Spoofing, Non-Hole Helper Theorem Rejection, and Cross-Chapter Hole Blindness Under `AUTOGRADER_SKIP_IMPORTS=true`)

`Basis: source + execution + derived`

#### 2.1 Unsoundness of `@[autogradedHole]` on `inductive` Declarations

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

#### 2.2 Incompleteness on Student-Proved Helper Theorems Referenced by Non-Hole Definitions

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

#### 2.3 Cross-Chapter `@[autogradedHole]` Blindness Under `AUTOGRADER_SKIP_IMPORTS=true`

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

### Finding 3: Lean `v4.34.1` Compiler Mechanism Behind the Match Deduplication Hazard (`MatcherKey`, `Closure.mkValueTypeClosure`, and `matcherExt` `asyncMode := .local` Under `-DElab.async=false` vs. `true`)

`Basis: source + execution`

#### 3.1 `MatcherKey` and `Closure.mkValueTypeClosure` in `Lean/Meta/Match/Match.lean`

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

### Finding 4: Triple-Compounding `.match_1` Contamination Bug in Anneal's `TrustedBoundary.lean` (`f938c18db` Lines 658–1305) Across `@[candidate]` and `@[vetted]` / `@[candidate <feat2>]` Declarations and Verified Fix (`isPureVettedMatcher`)

`Basis: source + execution`

#### 4.1 Three Compounding Bugs in `TrustedBoundary.lean` (`f938c18db`)

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

#### 4.2 Verified Fix: `isPureVettedMatcher` and `statusMap` Override

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

### Finding 5: Cross-Boundary `Trusted.*` `realizeConst` Rejection in `TrustedBoundary.lean` (`f938c18db` Lines 422–528, 1341–1365), `.match_1.splitter` `.defnInfo` and `Lean.isReservedName` Behavior Under `loadExts := false`, and Verified Phase 1 + Phase 2 Fix (`isRealizedCompilerConstant` & `decide` `optConfig`)

`Basis: source + execution`

#### 5.1 On-Demand `realizeConst` Serialization into Consumer `.olean` Files

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

#### 5.2 Two Critical Subtleties Under `loadExts := false` and Verified Phase 1 + Phase 2 Fix

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

### Finding 6: Architectural Comparison of `comparator` + `comparator-autograder` vs. Anneal's `TrustedBoundary.lean` and Implications for Two-Stage Verification / `.olean` Stubbing

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

#### Implications for Two-Stage Verification and `.olean` Stubbing

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

## Boundaries

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

## Evidence

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

## Revalidation

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
