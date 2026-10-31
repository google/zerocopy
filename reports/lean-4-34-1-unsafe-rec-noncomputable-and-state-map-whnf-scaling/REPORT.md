# Lean 4.34.1 `._unsafe_rec` Emission, `noncomputable` Elaboration, and State-Map WHNF Scaling

## Summary

In `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), two
kernel and elaborator mechanisms govern recursive definitions and symbolic state
evaluation in `prelude`-only verification projects such as
`joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`):

1. **`._unsafe_rec` Emission into `ModuleData.constants` and `noncomputable section` Scope Leakage:**
   Every recursive value-level declaration elaborated via `addPreDefinitions`
   (`Lean/Elab/PreDefinition/Main.lean:288-357`)—whether compiled by structural
   recursion (`brecOn`), well-founded recursion (`WellFounded.fix`), or
   `partial_fixpoint`, including lifted `where`/`let rec` helpers and `deriving
   DecidableEq` instances on recursive inductives—calls
   `addAndCompilePartialRec` (`Lean/Elab/PreDefinition/Basic.lean:280-296`)
   whenever `preDefs.all shouldGenCodeFor` is `true`. That function inserts an
   auxiliary `<fn>._unsafe_rec` declaration with `safety :=
   DefinitionSafety.partial` (`ci.isPartial = true`) directly into the kernel
   environment (`ModuleData.constants`, never `ModuleData.extraConstNames`),
   which `trusted/audit/TrustedBoundary.lean:855` rejects. Crucially, opening a
   `noncomputable section` does **not** set `modifiers.computeKind :=
   .noncomputable` in `mkDefView` (`Lean/Elab/DefView.lean:219-225`), and both
   branches of `shouldGenCodeFor` (`Basic.lean:134-141`) return
   `!preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable`. A recursive
   `def` inside `noncomputable section` without an explicit `noncomputable`
   modifier therefore still emits `<fn>._unsafe_rec` into
   `ModuleData.constants`. Marking each recursive definition `noncomputable def`
   (or expressing computable recursion through open step functions iterated with
   `Nat.repeat`, `Nat.rec`, or `List.foldr` from `foundation-lock.json`)
   produces zero `._unsafe_rec` constants while keeping the kernel
   `ConstantInfo.defnInfo` bit-for-bit identical (`UnsafeRecProbe.lean`,
   `PreludeRecProbe.lean`).
2. **Call-by-Name Kernel WHNF Spine Duplication ($O(2^K)$) and Canonical State-Map Join Merging ($O(D)$ vs $O(2^D)$):**
   Lean 4's kernel reducer (`whnf_core` in `src/kernel/type_checker.cpp`) is
   call-by-name and does not mutate constructor fields in place after reducing a
   scrutinee in `casesOn`. In recursive state containers (`CanonList`,
   `DenseList`, `SortedAList`, `BinTrie`), returning wildcard-bound child
   variables from smart constructors (`BinTrie.mkNode`, `CanonList.cons`) and
   wrapping state updates directly in `.step { s with mem := ops.set ... }`
   leaves unreduced `ops.set` redexes on the spine. Because each subsequent
   instruction references `s.mem` both to read a source operand and to write a
   destination slot, beta reduction duplicates those unreduced spine redexes at
   every step, causing $O(2^K)$ kernel reduction blowup that times out at
   $>200,000$ heartbeats by $K = 50$ instructions. Reconstructing child nodes
   from pattern-matched constructor fields in smart constructors and gating
   `.step` with a 2-line continuation-passing spine-forcing combinator `ops.seq`
   restores linear $O(K)$ scaling ($K = 500$ replays in `245.97 ms` for
   `BinTrie` and `260.34 ms` for `CanonList`, beating `FnMap` at `285.96 ms`).
   Across $D$ chained diamond control-flow graphs (`Suite 2`), canonical state
   maps (`BinTrie`, `CanonList`) merge asymmetric branch states by `rfl` at join
   blocks in $O(D)$ time (`426.2 ms` elaboration / `45.28 ms` replay at $D = 8$,
   $256$ paths), whereas `FnMap` (`Nat → Option Val`) retains path-dependent
   closure chains that cannot unify by `rfl`, growing as $O(2^D)$ (`51,728.5 ms`
   at $D = 4$, timeout at $D = 8$).

## Applicability

These findings apply to:

- **Lean 4 (`leanprover/lean4`):** Version `v4.34.1` at commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`x86_64-unknown-linux-gnu`),
  specifically its pre-definition elaborator (`Lean/Elab/PreDefinition/*`),
  LCNF compiler (`Lean/Compiler/LCNF/*`), `.olean` serializer
  (`Lean/Environment.lean`), kernel replayer (`Lean/Replay.lean`), and C++ kernel
  WHNF evaluator (`src/kernel/type_checker.cpp`).
- **Anneal (`joshlf/anneal`):** Commit
  `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86` prototype),
  specifically `trusted/audit/TrustedBoundary.lean`,
  `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/X86Semantics.lean`,
  and `theory/Anneal/`.
- **Module Configuration:** Both `prelude`-only modules (importing a subset of
  `Init.Prelude`, `Init.NotationExtra`, `Init.Data.Nat.Basic`, and
  `Init.Data.List.Basic` locked in `foundation-lock.json`) and full `Lean`
  metaprogramming scripts used to inspect `ModuleData` and `Kernel.Environment`.

## Findings

### 1. Exact Call Graph for `<fn>._unsafe_rec` and `ModuleData.constants` vs `extraConstNames`

All value-level definitions (`def`, `abbrev`, `instance`, lifted `where` / `let
rec` closures from `Lean/Elab/MutualDef.lean:1111-1137`, and `deriving`
handlers) elaborate through `addPreDefinitions`
(`Lean/Elab/PreDefinition/Main.lean:288-357`). `addPreDefinitions` partitions
declarations into strongly connected components (SCCs) via `partitionPreDefs`
(`Main.lean:43-52, 296`) and dispatches each SCC `preDefs` across four branches:

1. **Non-recursive single declaration (`preDefs.size == 1 && isNonRecursive preDefs[0]!`, `Main.lean:299-311`):**
   `isNonRecursive` (`Main.lean:38-41`) checks whether `preDef.value` contains
   any `Expr.const declName _` equal to `preDef.declName`. If
   `preDef.modifiers.isNoncomputable` is `true`, it calls `addNonRec`;
   otherwise it calls `addAndCompileNonRec` (`Basic.lean:225-228`), which runs
   `addNonRec` followed by `compileDecl`. Neither path invokes
   `addAndCompilePartialRec`, so zero `._unsafe_rec` constants are created.
2. **Explicit `unsafe` declaration (`preDefs.any (·.modifiers.isUnsafe)`, `Main.lean:312-314`):**
   Calls `addAndCompileUnsafe` (`Basic.lean:255-278`) with default `safety :=
   DefinitionSafety.unsafe`, recording `<fn>` as `.defnInfo` with `ci.isUnsafe =
   true`.
3. **Explicit `partial` declaration (`preDefs.any (·.modifiers.isPartial)`, `Main.lean:315-320, 20-36`):**
   `addAndCompilePartial` registers `<fn>` in the kernel environment as
   `ConstantInfo.opaqueInfo` (`isUnsafe = false`, `isPartial = false`) inhabited
   by `mkInhabitantFor`, and then calls `addAndCompilePartialRec`.
4. **Total recursive SCC (`Main.lean:321-340`):**
   Dispatches to `Structural.structuralRecursion`
   (`Lean/Elab/PreDefinition/Structural/Main.lean:183-217`), `WF.wfRecursion`
   (`Lean/Elab/PreDefinition/WF/Main.lean:23-99`), or `PartialFixpoint.partialFixpoint`
   (`Lean/Elab/PreDefinition/PartialFixpoint/Main.lean:76-222`). Each total
   elaborator first adds the safe kernel definition `<fn>` (`.defnInfo`, `safety
   = .safe`, built from `brecOn`, `WellFounded.fix`, or monotone fixpoint
   combinators) via `addNonRec`, and then unconditionally invokes
   `addAndCompilePartialRec docCtx preDefs` (`Structural/Main.lean:198`,
   `WF/Main.lean:83`, `PartialFixpoint/Main.lean:218`).

Inside `Lean/Elab/PreDefinition/Basic.lean:280-296`, `addAndCompilePartialRec`
checks `if preDefs.all shouldGenCodeFor then` and calls `addAndCompileUnsafe
docCtx (safety := DefinitionSafety.partial)` on a copy of `preDefs` with
`declName := Compiler.mkUnsafeRecName preDef.declName` (`<fn>._unsafe_rec`) and
recursive self-calls rewritten to `<fn>._unsafe_rec`. Inside
`addAndCompileUnsafe` (`Basic.lean:255-278`):

- `addDecl decl` (`Basic.lean:270`) calls `Kernel.Environment.addDeclCore`
  (`Lean/Environment.lean:297`), which inserts `<fn>._unsafe_rec` into the
  **kernel** constant map `env.checked.get.constants.map₂` as
  `ConstantInfo.defnInfo` with `safety = DefinitionSafety.partial` (`ci.isPartial
  = true`, `ci.isUnsafe = false`).
- `compileDecl decl` (`Basic.lean:272`) runs the LCNF compiler
  (`Lean/Compiler/LCNF/Main.lean:206`). `ToDecl.toDecl`
  (`Lean/Compiler/LCNF/ToDecl.lean:130-132`) detects `isUnsafeRecName?
  declName`, strips the `._unsafe_rec` suffix, fetches `safeInfo ← getConstInfo
  declName`, and compiles the recursive body from `<fn>._unsafe_rec` into IR
  registered under `<fn>`.

When `writeModule` serializes the `.olean` file (`Lean/Environment.lean:1858-1885`),
`ModuleData.constants` receives every kernel constant from
`env.toKernelEnv.constants.foldStage2`, including `<fn>._unsafe_rec`. By
contrast, `ModuleData.extraConstNames` (`Lean/Compiler/IR/CompilerM.lean:228-234`)
collects only IR declarations `n` in `declMapExt` where `!env.contains n` (such
as `<fn>._boxed`, `<fn>._closed_<k>`, and `<fn>._redArg`). Because
`env.contains (<fn>._unsafe_rec)` is `true`, `<fn>._unsafe_rec` always resides
in `ModuleData.constants` and never in `ModuleData.extraConstNames`, causing
`trusted/audit/TrustedBoundary.lean:851-857` (`if ci.isUnsafe || ci.isPartial`)
to reject any non-`foundation` module containing a computable recursive
definition.

| Declaration Form | `<fn>` Kernel `ConstantInfo` | Auxiliary Kernel Constants in `ModuleData.constants` | Emits `<fn>._unsafe_rec` (`isPartial = true`)? | Rejected by `TrustedBoundary.lean:855`? |
| :--- | :--- | :--- | :--- | :--- |
| Non-recursive `def` (`isNonRecursive = true`) | `.defnInfo(safety=.safe)` | Match splitters (`<fn>.match_<k>`) | No | No |
| Structural recursive `def` (even in `noncomputable section` without `noncomputable` keyword) | `.defnInfo(safety=.safe)` | `<fn>._f` (`safety=.safe`), `<fn>._sunfold` (`safety=.safe`), `<fn>._unsafe_rec` (`safety=.partial`) | Yes | Yes (`<fn>._unsafe_rec`) |
| Well-founded recursive `def` (`termination_by`) | `.defnInfo(safety=.safe)` | `<fn>._unary`/`<fn>._mutual`, `<fn>.eq_def` (`thmInfo`), `<fn>._unsafe_rec` (`safety=.partial`) | Yes | Yes (`<fn>._unsafe_rec`) |
| `partial_fixpoint` recursive `def` | `.defnInfo(safety=.safe)` | `<fn>.mutual` (if mutual), `<fn>._unsafe_rec` (`safety=.partial`) | Yes | Yes (`<fn>._unsafe_rec`) |
| Mutual recursive `def`s (`mutual ... end`) | Each `<fn_i>` is `.defnInfo(safety=.safe)` | Per-method `._f`, `._sunfold`, or `._mutual`, plus `<fn_i>._unsafe_rec` (`safety=.partial`) | Yes | Yes (all `<fn_i>._unsafe_rec`) |
| `where` / `let rec` local recursive helper inside `def <outer>` | `<outer>.<go>` is `.defnInfo(safety=.safe)` | `<outer>.<go>._f`, `<outer>.<go>._sunfold`, `<outer>.<go>._unsafe_rec` (`safety=.partial`) | Yes | Yes (`<outer>.<go>._unsafe_rec`) |
| `deriving DecidableEq` / `BEq` / `Repr` / `Ord` on recursive `inductive T` | `instDecidableEqT.decEq` is `.defnInfo(safety=.safe)` | `instDecidableEqT.decEq._f`, `._sunfold`, `instDecidableEqT.decEq._unsafe_rec` (`safety=.partial`) | Yes | Yes (`instDecidableEqT.decEq._unsafe_rec`) |
| `noncomputable def` (structural, WF, `partial_fixpoint`, or mutual) | `.defnInfo(safety=.safe)` | `<fn>._f`, `<fn>._sunfold` (or `._unary`/`._mutual`); zero `._unsafe_rec` | No | No |
| `partial def` (without `noncomputable`) | `.opaqueInfo(isUnsafe=false)` | `<fn>._unsafe_rec` (`.defnInfo`, `safety=.partial`) | Yes | Yes (`<fn>._unsafe_rec`) |
| `noncomputable partial def` | `.opaqueInfo(isUnsafe=false)` | None (`value` is `Classical.ofNonempty` inhabitant) | No | No (not kernel-reducible) |
| `unsafe def` | `.defnInfo(safety=.unsafe)` | None (`<fn>` itself has `isUnsafe = true`) | No | Yes (`<fn>` has `isUnsafe = true`) |
| Safe `def` containing `unsafe t` (`BuiltinNotation.lean:555-580`) | `.defnInfo(safety=.safe)` | `<fn>.unsafe_1` (`.defnInfo`, `safety=.unsafe`) and `<fn>.unsafe_impl_1` (`.opaqueInfo`, `isUnsafe=false`) | No | Yes (`<fn>.unsafe_1` has `isUnsafe = true`) |

Basis: **source** (`Lean/Elab/PreDefinition/{Main,Basic}.lean`,
`Lean/Elab/PreDefinition/{Structural,WF,PartialFixpoint}/Main.lean`,
`Lean/Compiler/LCNF/ToDecl.lean`, `Lean/Compiler/IR/CompilerM.lean`,
`Lean/Environment.lean`, `trusted/audit/TrustedBoundary.lean`) + **execution**
(`support/UnsafeRecProbe.lean`).

### 2. Why `noncomputable section` Does Not Suppress `<fn>._unsafe_rec`

Opening a `noncomputable section` elaborates via `Lean/Elab/Command.lean:910`,
setting `Scope.isNoncomputable := true` and populating
`Term.Context.isNoncomputableSection := scope.isNoncomputable`
(`Command.lean:337`). However:

1. `elabModifiers` (`Lean/Elab/DeclModifiers.lean:213-219`) sets
   `modifiers.computeKind := .noncomputable` only when the declaration's own
   syntax (`stx.raw[4]`) carries the `noncomputable` token.
2. In `mkDefView` (`Lean/Elab/DefView.lean:219-225`), `(← getScope).isMeta` is
   propagated into `modifiers.computeKind`, whereas `(←
   getScope).isNoncomputable` is **not** propagated into `modifiers.computeKind`.
3. In `Lean/Elab/PreDefinition/Basic.lean:134-141`, `shouldGenCodeFor` has two
   identical branches:
   ```lean
   def shouldGenCodeFor (preDef : PreDefinition) : TermElabM Bool := do
     if (← isNoncomputableSection) && !AutoLift.get (← getOptions) then
       return !preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable
     else
       return !preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable
   ```
   Because `shouldGenCodeFor` ignores `isNoncomputableSection`,
   `addAndCompilePartialRec` still executes `addDecl decl` (`Basic.lean:270`),
   inserting `<fn>._unsafe_rec` into `env.checked` before calling `compileDecl`
   (`Basic.lean:272`). Even when `<fn>` references a `noncomputable` constant so
   `CoreM.compileDecls` (`Lean/CoreM.lean:749-765`) catches the codegen failure
   and rolls back its internal `Core.saveState`, that state snapshot was taken
   after `addDecl` at `Basic.lean:270` already committed `<fn>._unsafe_rec` to
   `env.checked`.

Basis: **source** (`Lean/Elab/DefView.lean:219-225`,
`Lean/Elab/PreDefinition/Basic.lean:134-141, 255-296`,
`Lean/CoreM.lean:730-768`) + **execution** (`support/UnsafeRecProbe.lean`
Section 3).

### 3. Recursor Code Generation (`ToImpure.lowerLet`) and `._unsafe_rec`-Free Recursion in `prelude`

When a non-recursive `def` directly invokes a recursor `<Ind>.rec`:

1. `ToLCNF.visitApp` (`Lean/Compiler/LCNF/ToLCNF.lean:817-844`) first applies
   `CSimp.replaceConstant` (`Lean/Compiler/CSimpAttr.lean:83-96`) and handles
   `Quot.{lift,mk}`, `Eq.{casesOn,rec,ndrec,recOn}`, `HEq.{ndrec,rec}`,
   `And.rec`, `Iff.rec`, `False.rec`, `Empty.rec`, `lcUnreachable`, and
   `getCasesInfo?` (`<Ind>.casesOn` and constructor eliminators,
   `Lean/Meta/CasesInfo.lean:45-85`). Any other `.recInfo` constant falls
   through to `visitAppDefaultConst`.
2. During `.pure`-to-`.impure` lowering, `ToImpure.lowerLet`
   (`Lean/Compiler/LCNF/ToImpure.lean:183-184`) rejects any remaining `.recInfo`
   constant with:
   `code generator does not support recursor '<name>' yet, consider using 'match ... with' and/or structural recursion`.
3. `Nat.rec` succeeds in computable definitions because `Init.Data.Nat.Basic`
   (locked in `trusted/lean/foundation-lock.json`) registers `@[csimp] theorem
   Nat.rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled`
   (`Init/Data/Nat/Basic.lean:22-29`). Similarly, `Nat.repeat`, `List.foldr`,
   `List.foldl`, and `List.map` were already compiled inside locked `foundation`
   modules (`TrustedBoundary.lean:853` exempts `foundation.contains m.module`).
   And for `Prop`-valued or `Sort u`-valued definitions,
   `LCNF.shouldGenerateCode` (`Lean/Compiler/LCNF/Main.lean:31-50`) returns
   `false`, so a non-recursive `Prop`-valued `def` can invoke custom `<Ind>.rec`
   directly without `noncomputable` and without emitting `._unsafe_rec`.

In `support/PreludeRecProbe.lean` (compiled with only `prelude`, `import
Init.NotationExtra`, `import Init.Data.Nat.Basic`, and `import
Init.Data.List.Basic`), writing open single-step functions (`compileValStep`,
`compileStage0Step`) using `match` (`casesOn`) and iterating them with
`Nat.repeat`, `Nat.rec`, or `List.foldr` produces `732` `ModuleData.constants`
with **zero** `isUnsafe || isPartial` declarations (`replay` time `101 ms`),
while all closed-term `rfl` and `decide` theorems reduce natively in the kernel.

Furthermore, Section 6 of `support/UnsafeRecProbe.lean` verifies that between a
structural `noncomputable def evalVal` and a computable `def evalVal`, the
kernel constants `evalVal`, `evalVal._f`, and `evalVal._sunfold` in
`env.toKernelEnv` have bit-for-bit identical `type`, `value`, `hints`, and
`safety`, and `Kernel.Environment.replay` (`Lean/Replay.lean:180-183`) skips all
`ci.isUnsafe || ci.isPartial` constants anyway. Keeping
`TrustedBoundary.lean:855` strict (`if ci.isUnsafe || ci.isPartial`) and
marking recursive definitions in `theory/` as `noncomputable def` (or using
`Nat.repeat` when bytecode execution is needed) requires zero changes to the
trusted auditor.

Basis: **source** (`Lean/Compiler/LCNF/{ToLCNF,ToImpure,Main}.lean`,
`Init/Data/Nat/Basic.lean:22-29`, `Lean/Replay.lean:180-183`) + **execution**
(`support/PreludeRecProbe.lean`, `support/UnsafeRecProbe.lean`).

### 4. Call-by-Name Kernel WHNF Spine Duplication ($O(2^K)$) and Its 2-Part Cure

In `src/kernel/type_checker.cpp`, Lean 4's kernel `whnf_core` is call-by-name:
when reducing `<Ind>.casesOn scrutinee ...`, it reduces `scrutinee` to WHNF to
select the constructor branch, but does not overwrite variables bound to the
unreduced `scrutinee` expression in enclosing constructors. In recursive state
maps (`DenseList`, `CanonList`, `SortedAList`, `BinTrie`), two implementation
patterns combine to trigger $O(2^K)$ kernel reduction blowup across $K$
sequential instructions:

1. **Unreduced child bindings in smart constructors:**
   Writing a wildcard default arm in `BinTrie.mkNode`:
   ```lean
   def BinTrie.mkNode (v : Option Val) (l r : BinTrie) : BinTrie :=
     match v, l, r with
     | none, .leaf, .leaf => .leaf
     | _, _, _ => .node v l r
   ```
   causes `BinTrie.casesOn` to reduce `l = BinTrie.setBits ...` to `.node lv ll
   lr` to select the wildcard branch and then store the **unreduced**
   `BinTrie.setBits ...` term `l` inside `.node v l r`.
2. **Lazy `.step` construction:**
   Returning `.step { s with mem := ops.set s.mem dst val }` exposes `.step` in
   WHNF without reducing `s'.mem`. When the next instruction references `s'.mem`
   twice (once in `ops.get s'.mem src` and once in `ops.set s'.mem dst2 val2`),
   beta reduction duplicates the unreduced `ops.set` redex, producing $T(k+1) =
   2 \cdot T(k) = O(2^K)$ reduction work and timing out at $>200,000$ heartbeats
   by $K = 50$.

Two local definitions in `support/StateMapBenchmarks.lean` and
`support/BenchCommon.lean` eliminate the blowup completely:

1. **Reconstruct child nodes from matched constructor variables in `mkNode` / `cons`:**
   ```lean
   def BinTrie.mkNode (v : Option Val) (l r : BinTrie) : BinTrie :=
     match l, r with
     | .leaf, .leaf =>
       match v with
       | none => .leaf
       | some val => .node (some val) .leaf .leaf
     | .leaf, .node rv rl rr => .node v .leaf (.node rv rl rr)
     | .node lv ll lr, .leaf => .node v (.node lv ll lr) .leaf
     | .node lv ll lr, .node rv rl rr =>
       .node v (.node lv ll lr) (.node rv rl rr)
   ```
   Because `.node lv ll lr` uses the `casesOn`-bound variables `lv`, `ll`, `lr`
   extracted from the already-WHNF-reduced recursive call, every node along the
   modified path is reconstructed in constructor WHNF.
2. **Force the root of `mem` before exposing `.step` via CPS `seq`:**
   ```lean
   def BinTrie.seq {α : Type} (t : BinTrie) (k : BinTrie → α) : α :=
     match t with
     | .leaf => k .leaf
     | .node v l r => k (.node v l r)
   ```
   Gating `.step` with `ops.seq (ops.set ...) (fun m' => .step { mem := m', ...
   })` forces the root of `m'` to WHNF before `.step` is returned, cascading
   through `mkNode` / `CanonList.cons` along the entire modified spine. Its
   metatheorem `BinTrie.seq t k = k t` is proved in 1 line by `cases t <;> rfl`.

Additionally, replacing per-step list indexing `blk.instrs[s.ip]?` ($O(K^2)$
across $K$ instructions) with structural block traversal `evalBlock` ($O(K)$)
reduces $K = 500$ kernel replay time by 14x (from `~3.5 s` to `0.25 s`).

Basis: **source** (`src/kernel/type_checker.cpp`) + **execution** + **derived**
complexity analysis (`support/StateMapBenchmarks.lean`,
`support/BenchCommon.lean`, `support/benchmark_results.json`).

### 5. Quantitative Comparison of 5 State-Map Representations in `prelude`-Only Lean 4.34.1

We mechanized and proved the `get_set` and canonicity laws of five state-map
representations in `support/StateMapBenchmarks.lean` using only `prelude` +
`Init.NotationExtra` (including a purely structural little-endian bit encoder
`succBits` / `natToBits` / `bitsToNat` that proves `BinTrie.get_set` in 58 lines
without `Nat.div` or `Nat.mod` lemmas):

| Representation | Type in `prelude` | Disjoint Update Commutativity by `rfl` | Dead-Slot Erasure by `rfl` | Asymmetric Branch Join by `rfl` | `get_set` Proof Lines | $K=500$ `evalBlock` Elab / Replay (ms) | $D=4$ Merged Elab / Replay (ms) | $D=8$ ($256$ paths) Merged Elab / Replay (ms) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`BinTrie` (Rep 5)** | `inductive BinTrie` (`leaf \| node val l r`) | Yes | Yes (`.node none .leaf .leaf` $\mapsto$ `.leaf`) | Yes | 58 | 2329.4 / **245.97** | **261.8** / **23.38** | **426.2** / **45.28** |
| **`CanonList` (Rep 2b)** | `List (Option Val)` (trailing `none`s trimmed) | Yes | Yes (`CanonList.cons none []` $\mapsto$ `[]`) | Yes | **18** | 2798.0 / **260.34** | 281.3 / 23.42 | 469.9 / 45.74 |
| **`DenseList` (Rep 2a)** | `List (Option Val)` (fixed length $N$) | Yes | Yes (for $i < N$) | Yes (if pre-sized to $N$) | 22 | 2676.8 / 271.42 | 293.8 / 24.82 | 501.5 / 48.78 |
| **`SortedAList` (Rep 4)** | `List (Nat × Val)` (sorted by key) | Yes | Yes (`erase` removes key) | Yes | 65 | 5491.9 / 1321.25 | 286.8 / 24.71 | 475.5 / 48.41 |
| **`DenseArray` (Rep 3)** | `Array (Option Val)` | Yes | Yes (for $i < N$) | Yes (if pre-sized to $N$) | 30 | 5801.6 / 611.41 | 380.1 / 36.26 | 655.0 / 72.70 |
| **`FnMap` (Rep 1)** | `Nat → Option Val` | **No** | **No** | **No** (unmerged $O(2^D)$) | 10 | **1332.9** / 285.96 | **51,728.5\*** / **68.56** | **TIMEOUT** ($>10^7$ heartbeats) |

*\*At $D = 4$, unmerged `FnMap` (`DiamondUnmerged_FnMap_4`) exceeds the default
2,000,000 heartbeat limit, requiring `maxHeartbeats 10000000` (`51.7 s`
elaboration, `5,003` proof DAG nodes, `171.6 KB` `.olean` vs `261.8 ms`, `796`
DAG nodes, `35.8 KB` `.olean` for `DiamondMerged_BinTrie_4`). Inside the Lean
kernel, `Array α` reduces via `.toList` round-trips, making `DenseArray` 2.1x to
2.5x slower than `CanonList` and `BinTrie` across all $K$ and $D$.*

In `support/RefinementBridge.lean`, defining `MemSubsumed (bound : Nat) (t :
BinTrie X86Val) (m : Nat → Option X86Val) : Prop := ∀ i, i < bound → m i =
BinTrie.get t i` bridges the relational `initX86State` on `Trusted.X86Machine`
(`mem : Nat → Option X86Val`) to `rfl` execution on `BinTrie X86Val`, shrinking
the proof of `maxUsizeBody` from 132 lines in `MirLemmas.lean` to 14 lines
(`maxUsize_canon_verified`) and merging asymmetric diamond branches by `rfl`
(`diamondJoin_canon_verified`).

Basis: **execution** + **derived** (`support/StateMapBenchmarks.lean`,
`support/RefinementBridge.lean`, `support/MeasureKernel.lean`,
`support/benchmark_results.json`).

## Boundaries

- **Not examined:** Native C code generation (`lean -c`) or LLVM backend output
  for `<fn>._unsafe_rec` beyond LCNF/IR registration in `declMapExt`.
- **Known not to apply:** `noncomputable section` alone does not suppress
  `<fn>._unsafe_rec` emission in Lean `v4.34.1`; each recursive declaration must
  carry the `noncomputable` modifier explicitly (or avoid recursive syntax via
  `Nat.repeat` / `Nat.rec` / `List.foldr`).
- **Known not to apply:** `Array (Option Val)` does not provide $O(1)$ updates
  inside Lean 4's kernel reducer (`whnf_core`); kernel reduction unfolds `Array`
  wrappers to `List` operations.

## Evidence

- **Lean 4.34.1 source (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
  - `src/Lean/Elab/PreDefinition/Main.lean:20-52, 288-357` (`addAndCompilePartial`, `isNonRecursive`, `partitionPreDefs`, `addPreDefinitions`).
  - `src/Lean/Elab/PreDefinition/Basic.lean:134-141, 215-228, 255-296` (`shouldGenCodeFor`, `addNonRec`, `addAndCompileNonRec`, `addAndCompileUnsafe`, `addAndCompilePartialRec`).
  - `src/Lean/Elab/DefView.lean:219-225` (`mkDefView` scope modifier propagation).
  - `src/Lean/Compiler/LCNF/ToLCNF.lean:817-844` and `src/Lean/Compiler/LCNF/ToImpure.lean:125-185` (`visitApp` `@[csimp]` replacement and `lowerLet` `.recInfo` rejection).
  - `src/Lean/Compiler/LCNF/Main.lean:31-50` (`shouldGenerateCode`).
  - `src/Lean/Environment.lean:280-344, 1858-1885` and `src/Lean/Replay.lean:180-183` (`ModuleData.constants` vs `extraConstNames`, `Kernel.Environment.replay`).
- **Preserved package artifacts (`reports/lean-4-34-1-unsafe-rec-noncomputable-and-state-map-whnf-scaling/support/`):**
  - `support/PreludeRecProbe.lean` (`sha256: d9073c51de34b2fdeb14d93ca983596424837422947dd24b9a7d89ef14a0829c`)
  - `support/UnsafeRecProbe.lean` (`sha256: 3b2df1273552285e62563f939f6b1be6dca63c5cb0cb9f455702836147f8a169`)
  - `support/StateMapBenchmarks.lean` (`sha256: f7f19be1e27e3ef9d60b35f949324830423f9e77aae3348aa354e15c52f90528`)
  - `support/RefinementBridge.lean` (`sha256: 1491b69dbaaf3776558196fface01ef63e8aa99c984ccde3b12451b07bd9bc61`)
  - `support/BenchCommon.lean` (`sha256: b0e3900949b4b4732edaaa4c514e282891d0a2d1fffed99ae48019b2fc33fcea`)
  - `support/MeasureKernel.lean` (`sha256: c2215c1f1df5605e15f9b551dba137e7734fcae4e9cbc665fd68cf02832e6a66`)
  - `support/benchmark_results.json` (`sha256: ea0eb6a10bbe507722b7029107b3fc4bab4170a6f12bfe237f36c51bb4a68ab7`)

## Revalidation

Run the preserved probes directly with Lean 4.34.1:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  -o /tmp/PreludeRecProbe.olean support/PreludeRecProbe.lean
LEAN_PATH=/tmp lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/UnsafeRecProbe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/StateMapBenchmarks.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/RefinementBridge.lean
```

To check whether a newer Lean release fixes `noncomputable section` modifier
propagation or `shouldGenCodeFor`, inspect `src/Lean/Elab/DefView.lean` (`mkDefView`)
and `src/Lean/Elab/PreDefinition/Basic.lean` (`shouldGenCodeFor`), or check
whether `sec_struct_plain` in `support/UnsafeRecProbe.lean` still emits
`sec_struct_plain._unsafe_rec` into `ModuleData.constants`.
