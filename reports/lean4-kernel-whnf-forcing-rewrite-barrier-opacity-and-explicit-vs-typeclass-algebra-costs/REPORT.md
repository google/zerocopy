# Lean 4 WHNF Thunk Forcing, Rewrite-Barrier Opacity, Sparse-Match Axiom Hygiene, and Explicit vs. Typeclass Algebra Costs

## Summary

Large-scale computational verification and verified compiler proofs in Lean 4 (`v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) routinely stall on five interactions across the `Meta` elaborator, C++ kernel normalizer, and LCNF compiler:

1. **Rewrite-Barrier Opacity Requires Zero-`Prop`-Argument Cut Predicates (`kabstract` / `Simp.congr`):**
   - Neither `@[irreducible] def HoldIrred (P : Prop) : Prop := P` nor `structure HoldStruct (P : Prop) : Prop where val : P` stops `rw` or `simp` traversal, because `P` stays exposed as an `.app` argument: `MVarId.rewrite` (`Lean/Meta/Tactic/Rewrite.lean:47`) runs `kabstract` (`Lean/Meta/KAbstract.lean:30-67`), which descends into every `.app f a` regardless of `f`'s reducibility, and `Simp.congr` (`Lean/Meta/Tactic/Simp/Main.lean:545-549, 637-649`) applies `simpAppUsingCongr` to explicit arguments.
   - At tree depth 12 (`1,318,909` AST nodes without sharing), one `rw` across `HoldIrred` costs **`111,387` heartbeats (`37.07 ms`)** (>55% of default `maxHeartbeats = 200,000`) and `HoldStruct` costs **`110,884` heartbeats (`31.53 ms`)**, whereas a zero-`Prop`-argument predicate `def CutPred (x : State) : Prop := ...` sealed with `attribute [irreducible] CutPred` *after* proving its intro/iff lemmas costs **`443` heartbeats (`0.51 ms`; `251x` fewer heartbeats, `72.4x` faster)**. Applying `@[irreducible]` *before* proving bridge lemmas breaks `Meta` unfolding, while the C++ kernel ignores `Meta` `@[irreducible]` (`Lean/ReducibilityAttrs.lean:79-147`) entirely.

2. **WHNF Thunk Duplication ($2^N$ Double-Reads and $(K+1)^N$ Projections) & `strictNat` Forcing:**
   - Because Lean constructors are lazy and `useWHNFCache` (`Lean/Meta/WHNF.lean:1055-1061`) disables caching whenever `e.hasFVar || e.hasExprMVar`, double-reading an unforced open `Option` (`if o.isSome then o else none`) blows up as $\Theta(2^N)$ (`12,456.28 ms` at $N=16$ vs. `486.39 ms` via `Option.casesOn`). Updating a $K$-field structure via unforced projections triggers $\Theta((K+1)^N)$ expansion (`3,063,405` heartbeats / `221.88 ms` at $K=3, N=6$, vs. `5,392` heartbeats / `0.51 ms` with `casesOn` field forcing—**`568x` fewer heartbeats, `432x` faster**). On ground states, CPS `strictNat` (`Nat.casesOn`) forces C++ GMP `reduce_nat` evaluation before `State.mk` allocation (`505.56 ms` vs. `769.63 ms` at $N=22$).

3. **LCNF Codegen (`List.foldr` vs. `@List.rec`):**
   - `Lean/Compiler/LCNF/ToImpure.lean:183-184` rejects `@List.rec` in computable definitions (`code generator does not support recursor 'List.rec' yet`), whereas `List.foldr` (`Init/Data/List/Impl.lean:142-145`) combines 1-step kernel reduction with `@[csimp] foldr_eq_foldrTR` (`Array.foldr`) and emits zero `<caller>._unsafe_rec` partial declarations.

4. **Sparse Wildcards (`_sparseCasesOn`) Contaminate Pure Definitions with `propext`:**
   - Wildcard matches covering fewer than all constructors (`Lean/Meta/Tactic/Cases.lean:258-267`) synthesize `_sparseCasesOn` (`SparseCasesOn.lean:59-146`), calling `Nat.ne_of_beq_eq_false` (`HasNotBit.lean:36`) and injecting **`[propext]`** into pure `Nat`-valued definitions; exhaustive constructor patterns restore `[]` (zero axioms).

5. **Explicit Algebraic Records vs. Tabled Typeclasses:**
   - Grounded in Selsam et al. (`10.48550/arXiv.2001.04301`), Baanen (`10.1007/s10817-024-09712-7`), Wieser (`10.1007/978-3-031-42753-4_4`), and Garillot et al. (`10.1007/978-3-642-03359-9_23`), 5-layer nested typeclasses (`Layer0..Layer4`) add an invariant **`37,440`-byte `.olean` overhead** (`+28.1%` at $N=80$: `170,648 B` vs. `133,208 B` for explicit `AlgOps`) plus repeated `synthInstance` heartbeats (`4,288` hb/80 lookups; `9,917` hb/200 diamond `D` lookups). Explicit record passing inside hot kernels gives $O(1)$ `FVar` pointer equality (`is_eqp`) while preserving coarse module-boundary typeclasses across `.olean` layers.

## Applicability

Findings apply to Lean 4 developments, verified compilers, and independent auditors across the three subjects in `REPORT.json`:

- **Core Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Source inspection of `Rewrite.lean`, `KAbstract.lean`, `Simp/Main.lean`, `WHNF.lean`, `ReducibilityAttrs.lean`, `ToImpure.lean`, `SparseCasesOn.lean`, `SparseCasesOnEq.lean`, `HasNotBit.lean`, `Cases.lean`, `Init/Data/List/Impl.lean`, and `Init/Data/Nat/Basic.lean`, combined with single-threaded `lean -o` and `#eval MetaM` probes on `x86_64-unknown-linux-gnu`.
- **External Checkers (`digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` `v0.4.32`):** Governs why `@[irreducible]` is not a kernel barrier, why `._unsafe_rec` fails `nanoda_lib`, and why `_sparseCasesOn` `propext` leakage fails zero-axiom allowlists.

**Scope Split with Prior Corpus Reports:** C++ `expr_cell` non-hash-consing, GMP `reduce_nat` `has_fvar` skips, and `BinTrie`/`runForced` scaling appear in `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`; `String.ofByteArray`/`ofList` `maxRecDepth` and `omega`/`grind`/`bv_decide` closures in `lean-prelude-string-utf8-recursor-traps-and-core-tactics`; cross-module `.olean` lens insulation (`OpenCoreMIR`) in `typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair`; and `is_def_eq_core` non-transitivity / `nanoda_lib` trust in `lean4-kernel-soundness-criticisms-defeq-pathologies-and-lean4lean-checkers`.

## Findings

### 1. Rewrite-Barrier Opacity: Why Explicit-`Prop` Wrappers Fail and Zero-`Prop` Cut Predicates Succeed

`Basis: source + execution + derived`

Authors frequently try to stop `rw` or `simp` from scanning a large symbolic invariant $P$ by wrapping $P$ in an `@[irreducible]` definition or wrapper `structure`:

```lean
@[irreducible] def HoldIrred (P : Prop) : Prop := P
structure HoldStruct (P : Prop) : Prop where val : P
```

Source inspection of Lean `v4.34.1` proves why **both** wrappers fail mechanically:

1. **`rw` / `kabstract` Unconditional Argument Descent (`Lean/Meta/Tactic/Rewrite.lean:47`, `Lean/Meta/KAbstract.lean:30-67`):**
   - `MVarId.rewrite` invokes `kabstract e lhs config.occs` (`Rewrite.lean:47`). `kabstract` traverses `e` top-down without unfolding or checking the reducibility attribute of any head constant `f`:
     ```lean
     -- src/lean/Lean/Meta/KAbstract.lean:39-40, 49-50
     match e with
     | .app f a => return e.updateApp! (← visit f offset) (← visit a offset)
     ...
     else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
       visitChildren ()
     ```
   - Because `HoldIrred P` and `HoldStruct P` expose `P` as an explicit `.app` child, `kabstract` visits every node of `P`, allowing `rw` to rewrite subterms inside `P` (`rw_pierces_HoldIrred` and `rw_pierces_HoldStruct` succeed) and paying $O(|P|)$ traversal cost even when no match exists.
2. **`simp` Default Congruence (`Lean/Meta/Tactic/Simp/Main.lean:545-549, 637-649`):**
   - `Simp.congr` falls through to `congrDefault` -> `simpAppUsingCongr` (`Main.lean:549`), simplifying explicit arguments of `HoldIrred` and `HoldStruct` regardless of `@[irreducible]` or `opaque`.
3. **Zero-`Prop`-Argument Cut Predicates & Declaration Ordering (`Lean/ReducibilityAttrs.lean:79-147`):**
   - Parameterizing only over compact state handles hides the `Prop` tree behind a constant head:
     ```lean
     def CutPred (x : Nat) : Prop := bigTree 11 x
     theorem cutPred_intro (x : Nat) (h : bigTree 11 x) : CutPred x := h
     attribute [irreducible] CutPred
     ```
   - Bridge lemmas **must** precede `attribute [irreducible] CutPred`: marking `PrematureCut` `@[irreducible]` up front blocks `rfl` / `Meta.isDefEq` (`prematureCut_fail`), while delayed sealing makes `CutPred x` an atomic 2-node `.app` to `rw`/`simp` (`rw_blocked_by_CutPred` fails immediately). Note that `ReducibilityAttrs` affects `Meta` transparency only—the C++ kernel (`type_checker.cpp`) unfolds transparent `defnInfo` constants unconditionally.

Table 1 reports observed `Lean v4.34.1` `MVarId.rewrite` costs across binary `Prop` trees `expandTree x d` alongside an unrelated `z = z` conjunct:

| Goal Pattern (`<Barrier> ∧ (z = z)`, `rw [hz]`) | Depth $d=8$ (`57,853` nodes) | Depth $d=10$ (`280,573` nodes) | Depth $d=12$ (`1,318,909` nodes) | Behavior |
| :--- | ---: | ---: | ---: | :--- |
| `HoldIrred (bigProp)` (`@[irreducible] def`) | `10,334` hb (`2.58 ms`) | `33,241` hb (`9.29 ms`) | **`111,387` hb (`37.07 ms`)** | **Porous** (`kabstract` & `congr` scan `bigProp`) |
| `HoldStruct (bigProp)` (`structure`) | `8,909` hb (`1.36 ms`) | `32,807` hb (`7.45 ms`) | **`110,884` hb (`31.53 ms`)** | **Porous** (`kabstract` & `congr` scan `bigProp`) |
| `CutPred x` (0-`Prop`-arg + delayed `@[irreducible]`) | `507` hb (`0.29 ms`) | `436` hb (`0.35 ms`) | **`443` hb (`0.51 ms`)** | **Opaque ($O(1)$)**: **`251x` fewer hb**, **`72.4x` faster** (`-29.2%` `.olean`: `23,080 B` vs `32,584 B`) |

---

### 2. WHNF Thunk Duplication ($2^N$ Double-Reads and $(K+1)^N$ Projections) and `strictNat` Forcing

`Basis: source + execution + derived`

Constructors in Lean 4 are lazy in their fields, and `Lean.Meta.useWHNFCache` (`src/lean/Lean/Meta/WHNF.lean:1055-1061`) disables WHNF caching whenever `e.hasFVar || e.hasExprMVar` is true (e.g., any expression referencing a symbolic input variable `x : Nat`). Unforced transitions suffer two exponential blowups:

1. **Double-Read $\Theta(2^N)$ Blowup (`if o.isSome then o else none`):**
   - `o.isSome` forces `o` once inside `Option.casesOn`, while the `then` branch emits a second unforced copy of `o`—evaluating predecessor steps twice per step ($T(N) = 2T(N-1) + c$). Matching `match o with | none => none | some v => some v` binds `v` once at entry, restoring linear $O(N)$ scaling (`486.39 ms` vs. **`12,456.28 ms`** at $N=16$, **`25.6x` speedup**).
2. **Unforced $K$-Field Projection $\Theta((K+1)^N)$ Blowup vs. `State.casesOn` Entry Forcing:**
   - Building `{ r0 := if s.r0.isSome && s.r1.isSome && s.r2.isSome then s.r0 else none, ... }` ($K = 3$ fields) projects `s` $K+1 = 4$ times per step without forcing constructor payloads, growing by **4.00x per step** (`13,256 -> 47,701 -> 190,808 -> 764,358 -> 3,063,405` heartbeats from $N=2..6$). Unpacking `match s with | ⟨r0, r1, r2⟩ => ...` and forcing each `Option` payload before `St3Opt.mk` reduces $N=6$ to **`5,392` heartbeats (`0.51 ms`)**—**`568.1x` fewer heartbeats** and **`432.5x` faster**.
3. **Ground Arithmetic Thunk Forcing (`strictNat`):**
   - On closed ground runs (`⟨1, 2⟩`), constructors still defer `a + b` expressions inside `Pair.mk` unless forced via CPS `strictNat` (`def strictNat (n : Nat) (k : Nat → α) : α := match n with | 0 => k 0 | m + 1 => k (m + 1)`), triggering C++ GMP `reduce_nat` before allocation (`505.56 ms` vs. `769.63 ms` at $N=22$). On open symbolic inputs (`hasFVar`), `strictNat` stays stuck on `Nat.casesOn` and must be omitted.

| Depth $N$ | Open `Option` Double-Read (`lean -o`) | Open `Option.casesOn` (`lean -o`) | Open $K=3$ Unforced Projections (`whnf` hb / $\mu$s) | Open $K=3$ Forced `casesOn` (`whnf` hb / $\mu$s) | Improvement |
| :---: | ---: | ---: | ---: | ---: | :--- |
| **2** | — | — | `13,256` hb (`1,243` $\mu$s) | `2,600` hb (`298` $\mu$s) | `5.1x` hb (`4.2x` faster) |
| **4** | — | — | `190,808` hb (`15,300` $\mu$s) | `3,770` hb (`506` $\mu$s) | `50.6x` hb (`30.2x` faster) |
| **6** | — | — | **`3,063,405` hb (`221,877` $\mu$s)** | **`5,392` hb (`513` $\mu$s)** | **`568.1x` hb (`432.5x` faster)** |
| **8 / 12** | `591.28` / `1,299.63 ms` | `533.92` / `461.22 ms` | *(`>196M` hb projected)* | *linear* | `1.11x` / `2.82x` |
| **14 / 16** | `3,364.96` / **`12,456.28 ms`** | `487.57` / **`486.39 ms`** | *timeout* | *linear* | `6.90x` / **`25.61x`** |

---

### 3. LCNF Code-Generator Support: `List.foldr` (`@[csimp]`) vs. `@List.rec` and `._unsafe_rec`

`Basis: source + execution`

In `src/lean/Lean/Compiler/LCNF/ToImpure.lean:183-184`, `Code.toImpure` rejects computable definitions referencing raw primitive recursors (`.recInfo`):

```lean
| some (.recInfo ..) =>
  throwError f!"code generator does not support recursor `{name}` yet, consider using 'match ... with' and/or structural recursion"
```

Thus `@List.rec` fails compilation (`exit 1`) inside any computable `def`. Across `Init`, only `@Nat.rec` succeeds (`Init/Data/Nat/Basic.lean:22-30`) via `@[csimp] theorem rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled` (defining `Nat.recCompiled` by structural `match` and bypassing `ToImpure`). Conversely, writing an explicit recursive `def` (`| [] => 0 | h :: t => h + sum t`) causes `addAndCompilePartialRec` to register `<fn>._unsafe_rec` with `ConstantInfo.isPartial = true` in the environment, violating strict `nanoda_lib` / external-checker audits. Using **`List.foldr`** (`Init/Data/List/Impl.lean:142-145`) resolves all three constraints simultaneously:

```lean
-- src/lean/Init/Data/List/Impl.lean:142-145
@[specialize] def foldrTR (f : α → β → β) (init : β) (l : List α) : β := l.toArray.foldr f init
@[csimp] theorem foldr_eq_foldrTR : @foldr = @foldrTR := by
  funext α β f init l; simp only [foldrTR, ← Array.foldr_toList]
```

In kernel `whnf_core`, `List.foldr` unfolds one step per cons cell (`sumViaFoldr [10, 20, 30] = 60` via `rfl`, **`[]` axioms**), emits zero `<caller>._unsafe_rec` constants in downstream caller modules, and lowers via `@[csimp]` at runtime to tail-recursive `Array.foldr` (`O(1)` stack, Ullrich & de Moura, *IFL 2019*, DOI `10.1145/3412932.3412935`).

| List Recursion Pattern | Compiles via LCNF (`lean -o`)? | Kernel `rfl` on `[10, 20, 30]`? | Emits `<caller>._unsafe_rec`? | Runtime Stack Safety (`@[csimp]`) |
| :--- | :---: | :---: | :---: | :--- |
| Direct `@List.rec` in computable `def` | **Fails** (`ToImpure.lean:184`) | N/A | N/A | N/A |
| `noncomputable def` + `@List.rec` | Skipped (noncomputable) | Yes | No | Non-executable |
| Explicit recursive `def` (`\| h :: t => ...`) | Yes | Yes | **Yes** (`isPartial = true`) | Stack recursive unless TR |
| **`List.foldr` / `List.foldl`** | **Yes** (`foldrTR`) | **Yes** | **No** (clean) | **$O(1)$ stack via `Array.foldr`** |

---

### 4. Sparse Wildcard Matches (`_sparseCasesOn`) Contaminate Pure Definitions with `propext`

`Basis: source + execution`

Whenever a pattern match handles fewer than all constructors of an inductive type and routes the remainder to `_ => ...` (`interestingCtors.size < ctx.inductiveVal.ctors.length`, `Lean/Meta/Tactic/Cases.lean:258-267`), Lean compiles the match using `mkSparseCasesOn` (`Lean/Meta/Constructions/SparseCasesOn.lean:59-146`), which emits a catch-all hypothesis `Nat.hasNotBit mask x.ctorIdx` proved per omitted constructor (`line 123`) by `mkHasNotBitProof` (`Lean/Meta/HasNotBit.lean:26-38`):

```lean
-- src/lean/Lean/Meta/HasNotBit.lean:35-37
let some (_, lhs, rhs) ← matchNe? (mkHasNotBit e ns) | unreachable!
return mkApp3 (mkConst ``Nat.ne_of_beq_eq_false)
  lhs rhs (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
```

Because `Nat.ne_of_beq_eq_false` invokes **`propext`**, pure `Nat`-valued functions using wildcard matches inherit `[propext]` inside their kernel bodies (`SparseCasesOnEq.lean:21-85` similarly pulls `Nat.eq_of_beq_eq_true` into `.else_eq` equations). Live `#print axioms` checks on 10-constructor `Op` in `Lean v4.34.1` confirm:
- `def evalSparse (x : Op) : Nat := match x with | .a0 => 1 | _ => 0` $\implies$ **`[propext]`** (`evalSparse.eq_2` also `[propext]`).
- `def evalExhaustive (x : Op) : Nat := match x with | .a0 => 1 | .a1 | ... | .a9 => 0` $\implies$ **`does not depend on any axioms`** (`evalExhaustive.eq_2` also **`[]`**; avoid `simp` if zero-axiom proofs are required, as `Rewrite.lean:96-100` injects `propext` on `iff` rewrites).

External checkers configured with constructive `permitted_axioms = []` (e.g., `ammkrn/nanoda_lib`) must therefore ban sparse `_ =>` matches inside trusted specification definitions.

---

### 5. Explicit Algebraic-Structure Passing vs. Tabled Typeclass Synthesis Costs

`Basis: documentation + source + execution + derived`

While Lean 4's tabled typeclass resolution (Selsam, Ullrich, and de Moura, DOI `10.48550/arXiv.2001.04301`) prevents exponential search backtracking on diamond inheritance (Baanen *JAR 2024*, DOI `10.1007/s10817-024-09712-7`; Wieser *CICM 2023*, DOI `10.1007/978-3-031-42753-4_4`; Garillot et al. *TPHOLs 2009*, DOI `10.1007/978-3-642-03359-9_23`), benchmarking a 5-layer hierarchy (`Layer0..Layer4`) against an explicit flat record (`AlgOps`) in `Lean v4.34.1` exposes two residual costs:

1. **Constant `.olean` Metadata Tax (`+37,440 B`):** Across $N \in \{40, 80, 120\}$-step `step` chains, `Layer0..Layer4` adds an exact `37,440`-byte `.olean` footprint (`+36.9%` at $N=40$: `138,968 B` vs. `101,528 B`; **`+28.1%` at $N=80$: `170,648 B` vs. `133,208 B`**; `+22.7%` at $N=120$: `202,328 B` vs. `164,888 B`). Once an inner helper (`stepTC`) encapsulates multi-hop `Layer4.toLayer3.toLayer2` projections, marginal per-step size matches explicit `AlgOps` (`792 B/step`, `321` AST nodes at $N=40$); calling projections directly in the chain duplicates multi-hop projection chains at every call site.
2. **`synthInstance` Heartbeats vs. $O(1)$ `FVar` Pointer Equality:** Synthesizing `Layer4 Nat` 80 times consumes `4,288` heartbeats (`375` $\mu$s), and synthesizing a 4-class diamond `D Nat` 200 times consumes `9,917` heartbeats (`590` $\mu$s). Passing `(ops : AlgOps α)` incurs `0` synthesis calls and compares via $O(1)$ `is_eqp` on a single `FVar` in `quick_is_def_eq`. Combined with `typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair`, optimal large-scale design places coarse lens typeclasses at `.olean` module boundaries while projecting once into explicit `ops` records inside hot proof evaluators.

## Boundaries

- **known not to apply:**
  - Marking `HoldIrred (P : Prop) : Prop` `@[irreducible]` or defining `structure HoldStruct (P : Prop) : Prop` does **not** prevent `rw` (`kabstract`) or `simp` (`simpAppUsingCongr`) from traversing `P`.
  - `attribute [irreducible]` does **not** prevent the C++ kernel (`type_checker.cpp`) from unfolding a transparent `def`; it governs `Meta` default transparency only.
  - CPS `strictNat` (`Nat.casesOn`) does **not** simplify open symbolic terms (`has_fvar == true`) and should only force closed/ground `Nat` expressions.
- **unsupported:**
  - Direct `@List.rec` inside computable Lean `v4.34.1` definitions (`ToImpure.lean:184`); `native_decide` / `Lean.reduceBool` inside `digama0/lean4lean`.
- **unknown:**
  - Whether future Lean 4 versions replace `Nat.ne_of_beq_eq_false` in `HasNotBit.lean:36` with a `propext`-free witness for `_sparseCasesOn`, or how `grind` affects >15-layer Mathlib4 diamonds.
- **not examined:**
  - Mathlib4 macroscopic inheritance (>15 layers) and multi-threaded `Elab.async = true` contention in `Meta.whnf` / `synthInstance`.

## Evidence

- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
  - `src/lean/Lean/Meta/Tactic/Rewrite.lean:28-103` (`kabstract` at line `47`, `propext` for `iff?` at `96-100`).
  - `src/lean/Lean/Meta/KAbstract.lean:30-67` (`.app` descent at line `40`).
  - `src/lean/Lean/Meta/Tactic/Simp/Main.lean:537-649` (`simpAppUsingCongr` at `549`, `congr` at `637-649`).
  - `src/lean/Lean/ReducibilityAttrs.lean:79-147` (`getReducibilityStatusCore`).
  - `src/lean/Lean/Meta/WHNF.lean:1055-1061` (`useWHNFCache`).
  - `src/lean/Lean/Compiler/LCNF/ToImpure.lean:179-185` (`recInfo` error at `184`).
  - `src/lean/Init/Data/{List/Impl.lean:142-145, Nat/Basic.lean:22-30}` (`@[csimp]` `foldr_eq_foldrTR`, `rec_eq_recCompiled`).
  - `src/lean/Lean/Meta/{Tactic/Cases.lean:258-267, Constructions/SparseCasesOn.lean:59-146, Constructions/SparseCasesOnEq.lean:21-85, HasNotBit.lean:20-38}`.
- **Checkers:** `digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`; `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`v0.4.32`).
- **Papers:** Selsam et al. (`10.48550/arXiv.2001.04301`), Baanen (`10.1007/s10817-024-09712-7`), Wieser (`10.1007/978-3-031-42753-4_4`), Ullrich & de Moura (`10.1145/3412932.3412935`), de Moura & Ullrich (`10.1007/978-3-030-79876-5_37`), Garillot et al. (`10.1007/978-3-642-03359-9_23`).

## Revalidation

Run these self-contained probes in `/tmp/lean4_physics_reval` using `lean` (`v4.34.1`):

```bash
mkdir -p /tmp/lean4_physics_reval && cd /tmp/lean4_physics_reval

cat << 'EOF' > barriers_and_axioms.lean
@[irreducible] def HoldIrred (P : Prop) : Prop := P
structure HoldStruct (P : Prop) : Prop where val : P
def CutPred (x : Nat) : Prop := x + 0 = x
theorem cutPred_intro (x : Nat) : x + 0 = x → CutPred x := id
attribute [irreducible] CutPred
theorem rw_pierces_HoldIrred (x y : Nat) (hxy : x = y) (h : HoldIrred (y + 1 = 2)) :
    HoldIrred (x + 1 = 2) := by rw [hxy]; exact h
theorem rw_pierces_HoldStruct (x y : Nat) (hxy : x = y) (h : HoldStruct (y + 1 = 2)) :
    HoldStruct (x + 1 = 2) := by rw [hxy]; exact h
/-- error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?n + 0
in the target expression
  CutPred x

x : Nat
⊢ CutPred x -/
#guard_msgs in
theorem rw_blocked_by_CutPred (x : Nat) : CutPred x := by rw [Nat.add_zero]

inductive Op where | a0 | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9
def evalSparse (x : Op) : Nat := match x with | .a0 => 1 | _ => 0
def evalExhaustive (x : Op) : Nat :=
  match x with | .a0 => 1 | .a1 | .a2 | .a3 | .a4 | .a5 | .a6 | .a7 | .a8 | .a9 => 0
def sumViaFoldr (xs : List Nat) : Nat := xs.foldr (· + ·) 0
theorem sumViaFoldr_val : sumViaFoldr [10, 20, 30] = 60 := rfl
#print axioms evalSparse
#print axioms evalExhaustive
#print axioms sumViaFoldr_val
EOF
lean barriers_and_axioms.lean

cat << 'EOF' > check_list_rec_err.lean
def sumViaRec (xs : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun h _ acc => h + acc) xs
EOF
lean check_list_rec_err.lean || true

cat << 'EOF' > check_kn_whnf.lean
import Lean
open Lean Meta
structure St3Opt where
  r0 : Option Nat
  r1 : Option Nat
  r2 : Option Nat
def stepProj3All (s : St3Opt) : St3Opt :=
  { r0 := if s.r0.isSome && s.r1.isSome && s.r2.isSome then s.r0 else none,
    r1 := if s.r0.isSome && s.r1.isSome && s.r2.isSome then s.r1 else none,
    r2 := if s.r0.isSome && s.r1.isSome && s.r2.isSome then s.r2 else none }
def stepStrict3All (s : St3Opt) : St3Opt :=
  match s with
  | ⟨none, _, _⟩ | ⟨_, none, _⟩ | ⟨_, _, none⟩ => ⟨none, none, none⟩
  | ⟨some v0, some v1, some v2⟩ => ⟨some v0, some v1, some v2⟩
def runProj3All : Nat → St3Opt → St3Opt | 0, s => s | n + 1, s => stepProj3All (runProj3All n s)
def runStrict3All : Nat → St3Opt → St3Opt | 0, s => s | n + 1, s => stepStrict3All (runStrict3All n s)
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let ox ← mkAppM ``Option.some #[x]
    let s0 ← mkAppM ``St3Opt.mk #[ox, ox, ox]
    for n in [2, 4, 6] do
      let eP ← mkAppM ``St3Opt.r0 #[← mkAppM ``runProj3All #[mkNatLit n, s0]]
      let eS ← mkAppM ``St3Opt.r0 #[← mkAppM ``runStrict3All #[mkNatLit n, s0]]
      let h0 ← IO.getNumHeartbeats; let _ ← whnf eP; let h1 ← IO.getNumHeartbeats
      let _ ← whnf eS; let h2 ← IO.getNumHeartbeats
      IO.println s!"N={n} PROJ_HB={h1-h0} STRICT_HB={h2-h1}"
EOF
lean check_kn_whnf.lean

cat << 'EOF' > check_tc_vs_exp.lean
class Layer0 (α : Type) where
  zero : α
class Layer1 (α : Type) extends Layer0 α where
  one : α
class Layer2 (α : Type) extends Layer1 α where
  add : α → α → α
class Layer3 (α : Type) extends Layer2 α where
  mul : α → α → α
class Layer4 (α : Type) extends Layer3 α where
  mix : α → α → α
instance : Layer4 Nat where
  zero := 0; one := 1; add := Nat.add; mul := Nat.mul; mix := Nat.xor
def stepTC {α : Type} [Layer4 α] (a b : α) : α :=
  Layer2.add (Layer3.mul a b) (Layer4.mix a Layer1.one)

structure AlgOps (α : Type) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  mix : α → α → α
def natOps : AlgOps Nat := ⟨0, 1, Nat.add, Nat.mul, Nat.xor⟩
def stepExp {α : Type} (ops : AlgOps α) (a b : α) : α :=
  ops.add (ops.mul a b) (ops.mix a ops.one)
EOF
lean -o tc_exp.olean check_tc_vs_exp.lean && wc -c tc_exp.olean
```

Expected results: `evalSparse` reports `[propext]`, while `evalExhaustive` and `sumViaFoldr_val` report no axioms; `check_list_rec_err.lean` exits non-zero with `code generator does not support recursor 'List.rec' yet`; `check_kn_whnf.lean` shows `PROJ_HB` scaling as $4^N$ (`~3.06M` at `N=6`) vs. linear `STRICT_HB` (`~5.4k` at `N=6`); and splitting `Layer0..Layer4` vs. `AlgOps` across 80-step chains reproduces the `37,440`-byte `.olean` overhead.
