<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to those
terms. -->

# Lean 4 Libraries, Cslib, Aesop, Duper, and VC Benchmarks (2026)

## Summary

A primary-source audit of the Lean 4 external library and proof-automation
ecosystem (`Batteries`, `Mathlib4`, `Cslib`, `VerifiedAgora`, `Aesop`,
`lean-auto`, `Duper`, `lean-smt`, and `Plausible`) at Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), combined with a head-to-head
empirical benchmark across 14 representative Anneal MIR verification conditions
(Classes A–E, 41 compiled theorems and 59 timed elaboration probes), establishes
five principal findings for Anneal:

1. **Core `Init` and `Std` in Lean `v4.34.1` supersede the container and monadic
   reasoning modules that historically motivated `Batteries` or `Mathlib4`
   dependencies:** `Std.TreeMap`/`Std.TreeSet` (`Std/Data/TreeMap/`) and
   `Std.Do.Triple` (`Std/Do/Triple/`) have officially deprecated
   `Batteries.Data.RBMap` (`Batteries/Recycling/RBTree/`, 2,528 LoC) and
   `Batteries.Control.SatisfiesM` (`Batteries/Recycling/MonadSatisfying/`, 1,293
   LoC). `Batteries` (`f2effa3d803fda822b1f97b806c47cf2adfbcbc2`, 196 files,
   31,235 LoC) retains standalone value for verified heaps (`BinaryHeap`,
   `BinomialHeap`, `PairingHeap`), `UnionFind`, `AssocList`, 398 supplementary
   `List` lemmas, `#lint` drivers, and `generalize_proofs`, while `Mathlib4`
   (`d13f23b723b8a846827a245b89c10fc7d3f11612`) pulls eight transitive Lake
   packages (`batteries`, `Qq`, `aesop`, `proofwidgets`, `importGraph`,
   `LeanSearchClient`, `plausible`, `Cli`). Selective vendoring of
   self-contained definitions into `theory/` avoids multi-gigabyte cache and
   toolchain-lockstep costs.

2. **`leanprover/cslib` (`82db31eec215b6843be6df283304cc02e736ddef`, 297 files,
   47,963 LoC) provides clean design templates for labeled transition systems,
   bisimulation up-to, free monadic effect trees, and `TimeM` cost accounting,
   but is monolithically coupled to `Mathlib4` and contains no separation logic
   or low-level memory models:** Every `Cslib` file is required by
   `scripts/checkInitImports.lean` to import `Cslib.Init`, which imports
   `Mathlib.Init` and `Mathlib.Tactic.Common`. Upstream `leanprover/cslib`
   depends only on `Mathlib4` (and its eight transitive packages);
   `stagiralabs/VerifiedAgora` (`9703b9597dd37d6ec4845fc5d0480132e3db8054`) is
   an external Stagira Labs `@[target]` extraction and `SafeVerify` axiom-audit
   harness used in Agora evaluation forks (`stagiralabs/eval_Computability`)
   rather than an upstream `Cslib` dependency.

3. **Among external proof-producing tactics, `Aesop` (`v4.34.0`,
   `355695d523e41d0554926416cba2a2b3544fbbc9`) is the only lightweight,
   hermetic, proof-dependency-free addition to core `omega` and `grind`:**
   `Aesop` depends only on `Batteries`, compiles from source in `24.83 s`
   (`40.32 s` including `Batteries`), adds `16.77 MB` of `.olean` files,
   declares zero custom axioms, and extracts pure core-Lean proof terms via
   `Goal.extractProof` (`Aesop/Tree/ExtractProof.lean:105-189`) that reference
   zero `Aesop.*` or `Batteries.*` constants. By contrast, `Duper` (`v4.34.1`,
   `9e09cd05fd541d6cef4c485882b7978d32c7e0a3`) requires `lean-auto` (`v4.34.1`,
   `6b2774cde4d1cb7ac4d48ac61c34e950e0588d69`), whose `lakefile.lean` triggers a
   network `curl` download (`zipperposition.exe` `extraDepTargets` hook) unless
   pre-seeded,
   takes `127.21 s` and `414.72 MB` of `.lake/build` artifacts to compile from
   source, and embeds `Auto.Embedding.Lam` reification terms into every theorem
   closure (`36.76–63.83 ms` kernel replay, `50x–300x` slower than `Aesop` and
   `grind`).

4. **Core `omega` + `grind` + `refine ⟨_, rfl, ...⟩` + `bv_decide_kernel` solve
   all 14 benchmark verification conditions across Classes A–E without any
   external package dependency:** Across layout arithmetic (`A1`–`A3`),
   `ByteMemory` frame disjointness (`B1`–`B3`), coupled `MirLang.SpecOn`
   existentials (`C1`–`C2`), 64-bit `BitVec` overflow and bitfields (`D1`–`D3`),
   and Tree/Stacked Borrows relational obligations (`E1`–`E4`), core Lean
   tactics discharge 12 of 14 problems out-of-the-box and all 14 of 14 with
   1-line forward hints (`have h_base` on `E1`, `PermLe` constructors on `E2`).
   Notably, `grind` solves 64-bit bitfield packing/extraction (`D3`)
   out-of-the-box in `128.46 ms` elaboration with a 17-node proof term that
   replays in `14.55 ms` (`36.4x` faster kernel replay than `bv_decide_kernel`).

5. **Coupled existential witnesses (`∃ retVal, eval x = some retVal ∧ P retVal`)
   require structural `rfl` unification before calling `grind`, `omega`, or
   `duper`:** Standalone `grind`, `omega`, and `duper` cannot synthesize coupled
   witnesses across an `Option` equality and an arithmetic postcondition when
   the existential metavariable `?w` remains unassigned (`C1`, `C2`); `duper`
   also triggers an internal `Lean.Meta.whnfEasyCases` panic (`loose bvar in
   expression`) before timing out at `25,340.7 ms` on `C2`. Unifying `?w` first
   via `refine ⟨_, rfl, by grind⟩` (`4.89 ms` elaboration, `1.55 ms` replay) or
   `aesop (add safe tactic (by grind))` (`15.46 ms` elaboration, `1.70 ms`
   replay) discharges `C1` and `C2` deterministically.

## Applicability

These findings govern three subsystems of the Anneal verification stack:

- **`theory/` (`anneal` foundational library and `MirLang` semantics):**
  Determines whether Anneal should add Lake dependencies on `Batteries`,
  `Mathlib4`, `Cslib`, `Aesop`, `Duper`, `lean-auto`, or `lean-smt`, and
  identifies which `Cslib` modules (`LTS/Bisimulation.lean`,
  `Control/Monad/Free.lean`, `Algorithms/Lean/TimeM.lean`) provide clean
  patterns to adapt into `Init`/`Std`-only `theory/` modules.
- **`trusted/rustc-capture/` (automated VC proof-script generation):**
  Establishes the exact tactic dispatch order (`refine ⟨_, rfl, ...⟩`, `omega`,
  `grind`, `bv_decide_kernel`, and optional `aesop`) for discharging generated
  `MirLang.SpecOn`, layout, memory-frame, bitvector, and borrow-checker VCs.
- **`trusted/audit/` (`anneal-audit` `.olean` kernel environment verifier):**
  Quantifies the axiom footprint, `unsafe`/`partial`/`opaque` constant surface,
  transitive theorem-closure size (`Expr.numObjs`), and
  `Kernel.Environment.replay` cost of proofs generated by core and external
  tactics.

## Findings

### 1. Ecosystem Audit: `Batteries`, `Mathlib4`, `Cslib`, and `VerifiedAgora`

`Basis: primary-source inspection of leanprover-community/batteries@f2effa3d803fda822b1f97b806c47cf2adfbcbc2, leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612, leanprover/cslib@82db31eec215b6843be6df283304cc02e736ddef, and stagiralabs/VerifiedAgora@9703b9597dd37d6ec4845fc5d0480132e3db8054`

#### 1.1 `Batteries` (`v4.34.0` / `v4.34.1`) vs Core `Init` and `Std`

`leanprover-community/batteries` at `v4.34.0`
(`f2effa3d803fda822b1f97b806c47cf2adfbcbc2`, 2026-09-24; compatible with
`v4.34.1` because Lean `v4.34.1` is a patch release on the `v4.34.0` ABI, and
tracked up to `HEAD` `6d971e7e6b3f7d0a501c5418815aa9022edd3499`) has zero
external Lake dependencies (`lakefile.toml` defines `lean_lib Batteries`,
`lean_lib BatteriesTest`, and `lean_exe runLinter`) and comprises **196 `.lean`
files (31,235 LoC)** under `Batteries/`.

By Lean `v4.34.1`, the data structures and monadic verification abstractions
that previously required `Batteries` have been upstreamed into core `Init` and
`Std` (`5045d0056413266e57c625dcd7c365b10e377c52`):

- **Ordered maps and sets (`RBMap`/`RBSet` → `Std.TreeMap`/`Std.TreeSet`):**
  `Batteries.Data.RBMap` and `Batteries.Data.RBSet` have been moved to
  `Batteries/Recycling/RBTree/` (4 files, 2,528 LoC: `Basic.lean`,
  `Lemmas.lean`, `Map.lean`, `WF.lean`) and marked `@[deprecated]` in favor of
  core `Std.TreeMap`, `Std.TreeSet`, `Std.DTreeMap` (`Std/Data/TreeMap/`,
  `Std/Data/DTreeMap/`), and `Std.HashMap` (`Std/Data/HashMap/`).
- **Monadic Hoare/predicate-transformer reasoning (`SatisfiesM` → `Std.Do`):**
  `Batteries.Control.SatisfiesM` has been moved to
  `Batteries/Recycling/MonadSatisfying/` (4 files, 1,293 LoC: `Basic.lean`,
  `EStateM.lean`, `Except.lean`, `State.lean`) and deprecated in favor of core
  `Std.Do` (`Std.Do.Triple`, `Std.Do.WP`, `Std.Do.SPred`, `mvcgen`).
- **Fixed-width bitvectors and arrays (`BitVec`, `Array`, `Vector`, `List`):**
  `Batteries/Data/BitVec/Basic.lean` and `Lemmas.lean` retain only 143 LoC (9
  lemmas), because `Init.Data.BitVec.Basic`, `Lemmas`, and `Bitblast` now live
  in core `Init`.

What remains uniquely in `Batteries` falls into four categories:

| Category | Modules (`Batteries/...`) | Files / LoC | Key Declarations & Value for Anneal |
| :--- | :--- | :--- | :--- |
| **Verified Priority Queues & Disjoint Sets** | `Data/BinaryHeap.lean` (+ 2 files), `Data/BinomialHeap.lean` (+ 1 file), `Data/PairingHeap.lean`, `Data/UnionFind.lean` (+ 1 file) | 8 files / 2,950 LoC | Array-backed `BinaryHeap` (1,217 LoC), persistent `BinomialHeap` (630 LoC), `PairingHeap` (375 LoC), and `UFModel` / array-backed `UnionFind` with path compression and rank invariants (728 LoC). |
| **Association Lists, Difference Lists, & Lazy Streams** | `Data/AssocList.lean`, `Data/List/OrderedAssocList.lean`, `Data/DList/`, `Data/MLList/` | 9 files / 2,177 LoC | `AssocList` (385 LoC), verified sorted association lists `OrderedAssocList` (1,099 LoC), $O(1)$-append `DList` (151 LoC), and monadic lazy streams `MLList` (542 LoC) used by metaprogramming search tactics. |
| **Supplementary `List`, `Fin`, and `Nat` Lemmas** | `Data/List/` (15 files), `Data/Fin/Coding.lean`, `Data/Nat/Bisect.lean`, `Data/Nat/Digits.lean`, `Data/Nat/Gcd.lean` | 30 files / 10,803 LoC | 398 `List` theorems (`Perm`, `Chain`, `Scan`, `Pairwise`, `Sublist`, `EraseIdx`), finite type bijections `FinEncoding`/`IsoFin` (312 LoC), binary search `Nat/Bisect.lean` (200 LoC), and positional radix `Nat.digits` (661 LoC). |
| **Linters & Proof Maintenance Tactics** | `Tactic/Lint/` (6 files), `Tactic/GeneralizeProofs.lean`, `Tactic/Congr.lean`, `Tactic/Alias.lean`, `Tactic/OpenPrivate.lean`, `Tactic/HelpCmd.lean` | 35 files / 6,951 LoC | `#lint` and `lake exe runLinter` framework (`@[env_linter]`, `unusedArguments`, `docBlame`, `simpNF`, 1,701 LoC), `generalize_proofs` (533 LoC, abstracts proof terms in dependent indexing goals), `rcongr` (426 LoC), `open private` (255 LoC), and `#help tactic` (457 LoC). |

Because `Batteries` builds from source in `15.49 s` (`38.01 MB` `.olean`, 0
custom axioms) and its individual pure data-structure files (`UnionFind`,
`BinaryHeap`, `AssocList`) import only `Init`/`Std` plus small internal helpers,
Anneal does not need `Batteries` as a runtime dependency of `trusted/lean/` or
`theory/`, and can vendor individual data structures if needed.

#### 1.2 `Mathlib4` (`v4.34.1`) Dependency Footprint vs Selective Vendoring

`leanprover-community/mathlib4` at `v4.34.1`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`, 2026-10-16; `v4.34.0` tag
`5ed2965256430c3649e86755f9576b54eca72435`; `HEAD`
`f9738e46d32221bdd20d876adf69c619543cc523`) requires eight direct Lake packages
in `lakefile.lean` and `lake-manifest.json`:

1. `leanprover-community/batteries` (`f2effa3d803fda822b1f97b806c47cf2adfbcbc2`)
2. `leanprover-community/quote4` (`Qq`,
   `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259`)
3. `leanprover-community/aesop` (`355695d523e41d0554926416cba2a2b3544fbbc9`)
4. `leanprover-community/ProofWidgets4`
   (`106ff4fafc74ef4ac99d81dbf3ab399118f497a5`, which sets `preferReleaseBuild
   := true` for JavaScript widget bundles)
5. `leanprover-community/import-graph`
   (`e928b72544873815af278d38681b31c0293588e3`)
6. `leanprover-community/LeanSearchClient`
   (`ddf04cf3949fa556442341e87d47f9f6e6074707`)
7. `leanprover-community/plausible` (`118aa17ee84656b8bd727fef7c458ee8c833385c`)
8. `leanprover/lean4-cli` (`Cli`, `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`)

In addition, `Mathlib.Tactic.Linarith` and `Mathlib.Tactic.Polyrith` are heavily
coupled to `Mathlib.Algebra.Order.Ring.Defs`, whereas Lean `v4.34.1` ships
native `omega` and `grind` (`cutsat` + `CommRing` Groebner-basis/polynomial
normalization in `Init.Grind.Ring` and `Init.Grind.Ordered`) in core `Init`.
Adding `Mathlib4` as a dependency of `theory/` would lock Anneal's toolchain
upgrades to `Mathlib4` releases and require multi-gigabyte `lake exe cache get`
artifacts in CI. Selective vendoring of self-contained lemmas into `theory/` is
strictly preferable.

#### 1.3 `leanprover/cslib` (`82db31ee` and `v4.34.1`) Architecture & Inventory

`leanprover/cslib` at `HEAD` (`82db31eec215b6843be6df283304cc02e736ddef`,
2026-10-30, on `leanprover/lean4:v4.36.0-rc2` pinning `mathlib4` at
`69552756cd8a2d2d48763cf7279fd814d6a1224d`) and at its `v4.34.1` release tag
(`7c8f6c0f67015df29b152fdcffaf7850db2e9185`, 2026-10-16, on
`leanprover/lean4:v4.34.1` pinning `mathlib4` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`) contains **297 `.lean` files (47,963
LoC)** under `Cslib/`:

| Top-Level Directory | Files | LoC | Submodules & Formalized Results |
| :--- | ---: | ---: | :--- |
| `Cslib/Algorithms/` | 18 | 2,056 | `Lean/TimeM.lean` (154 LoC: monadic time complexity `TimeM T α`, `@[simp, grind =]` unfolding), verified insertion sort (`InsertionSort.lean`, 262 LoC) and merge sort (`MergeSort.lean`, 400 LoC) with $O(n^2)$ and $O(n \log n)$ bounds, `DecisionTree/` and `Query/` Boolean decision-tree complexity over `FreeM` (13 files, 1,240 LoC). |
| `Cslib/Computability/` | 110 | 18,125 | `Automata/` (57 files, 8,289 LoC: `DA`, `NA`, `EpsilonNA`, Thompson construction, determinization, minimization, Büchi/Muller/Rabin/Streett/parity $\omega$-automata), `Circuit/` (15 files, 2,535 LoC: Shannon/Lupanov circuit bounds), `Distributed/` (6 files, 1,750 LoC: replicated-store consistency models and FLP consensus impossibility `FLP/`), `Languages/` (12 files, 2,422 LoC: regular & $\omega$-regular languages, Kleene's theorem, pumping lemma), `Machines/` (15 files, 2,216 LoC: single/multi-tape Turing machines, `TimeM` reductions), `URM/` (5 files, 913 LoC). |
| `Cslib/Crypto/` | 15 | 1,903 | `Foundations/` (`Negligible.lean`, `PRG.lean`, `SecurityGame.lean`), `Commitments/` (`Commitment.lean`, `Pedersen.lean`), `Symmetric/` (`OneTimePad.lean`, `PerfectSecrecy.lean`), `SecretSharing/` (`Shamir.lean`). |
| `Cslib/Foundations/` | 83 | 11,719 | `Control/Monad/Free.lean` (345 LoC: `FreeM`, `liftEffect`), `Data/OmegaSequence/` (infinite streams), `Data/PFunctor/` (polynomial functors & $W$-types), `Relation/` (`Confluence.lean`, `Newman.lean`), `Semantics/LTS/` (18 files, 3,279 LoC: `Basic.lean`, `Bisimulation.lean`, `Simulation.lean`, `TraceEq.lean`), `Semantics/FLTS/` (functional LTS), `Semantics/GameSemantics/`, `Syntax/` (`HasAlphaEquiv`, `HasSubstitution`, `ScopedSyntax`). |
| `Cslib/Languages/` | 45 | 8,616 | `CCS/` (Milner's Calculus of Communicating Systems, bisimilarity congruence, vending machine HML spec), `CombinatoryLogic/` (SKI combinators and `PartrecToSKI`), `LambdaCalculus/LocallyNameless/` (`Fsub/`, `Stlc/`, `Untyped/` with $eta/\eta$ confluence and strong normalization), `Mech/` (choreographic programming). |
| `Cslib/Logics/` | 19 | 4,199 | `HML/` (Hennessy-Milner logic and characterization of bisimilarity), `LinearLogic/CLL/` (classical linear logic sequent calculus, cut elimination, phase semantics), `Modal/`, `Propositional/`. |
| `Cslib/MachineLearning/` | 4 | 1,047 | `PACLearning/` (VC dimension, Sauer-Shelah lemma, fundamental theorem of PAC learning). |
| `Cslib/Probability/` | 2 | 354 | Probability mass function (`PMF`) extensions over `Mathlib`. |
| `Cslib/Tactic/` & `Init.lean` | 2 | 46 | `Tactic/GrindAttrs.lean` (`grind` attribute registrations) and `Init.lean` (global `autoImplicit = false` and `Mathlib` root imports). |

##### Inspection of Target `Cslib` Modules for Anneal

1. **`Cslib/Foundations/Semantics/LTS/Basic.lean` (425 LoC) and
   `Bisimulation.lean` (689 LoC):**
   - `LTS State Label` wraps a ternary relation `Tr : State → Label → State →
     Prop` with scoped notation `s -[μ]-> s'`.
   - For weak transitions over `Option Label` (`none` = silent $     au$-step),
     `LTS.WeakStep` (`s -[]->* s1 -[μ]-> s2 -[]->* s'`) and `LTS.WeakTr`
     discharge silent chains via `Relation.ReflTransGen`.
   - `Bisimulation.lean` defines `LTS.IsBisimulation`, `LTS.Bisimilarity` ($s_1
     \sim s_2$, the existential join of all bisimulations),
     `LTS.BisimulationUpTo` (up-to techniques reducing proof obligations when
     showing a relation is a bisimulation), and `LTS.SWBisimilarity` (weak
     bisimilarity), and registers `Trans` instances (`trans_bisim_eq`,
     `trans_weakBisim_eq`) so relational refinement chains compose directly
     inside `calc` blocks.
   - **Applicability to Anneal:** `LTS`, `IsBisimulation`, `BisimulationUpTo`,
     and `calc` `Trans` instances provide an ideal template for Anneal's
     small-step `MirMachine` / target-ISA simulation and trace-refinement layer
     in `theory/`, and use only lightweight `Mathlib.Logic.Relation` lemmas that
     can be ported to pure `Init`/`Std` in under 300 LoC.

2. **`Cslib/Foundations/Control/Monad/Free.lean` (345 LoC) and `Effects.lean`:**
   - Defines the free monad over a polynomial functor (`PFunctor.{u, v}`):
     ```lean
     inductive FreeM (F : PFunctor.{u, v}) (α : Type w) : Type (max u v w)
       | pure (x : α) : FreeM F α
       | roll (a : F.A) (r : F.B a → FreeM F α) : FreeM F α
     ```
     together with `LawfulMonad (FreeM F)`, `liftEffect`, and `foldFreeM`
     (catamorphic interpretation into any target `Monad M`).
   - **Applicability to Anneal:** Useful if Anneal later models external/FFI I/O
     interaction trees (`ITree`-style finite fragments), though Anneal's current
     angelic/demonic `StepResult` (`trusted/lean/StepResult.lean`) is
     direct-style relational and does not require `PFunctor`.

3. **`Cslib/Algorithms/Lean/TimeM.lean` (154 LoC):**
   - Defines a lightweight Writer-style cost monad parameterized over an
     arbitrary `AddCommMonoid T`:
     ```lean
     structure TimeM (T : Type*) (α : Type*) where
       ret : α
       time : T
     ```
     with `TimeM.tick [One T] (c : T := 1) : TimeM T PUnit := ⟨(), c⟩` (scoped
     notation `✓`), `LawfulMonad`, and `@[simp, grind =]` annotations on
     `TimeM.pure`, `TimeM.bind`, `ret_pure`, `ret_bind`, `time_pure`, and
     `time_bind` so `simp` and `grind` automatically sum step costs across `do`
     blocks.
   - **Applicability to Anneal:** Directly portable to `Init`/`Std` (replacing
     `AddCommMonoid T` with `Nat`) for verified resource/fuel or worst-case
     execution-time (WCET) accounting over functional models.

4. **`Cslib/Languages/CCS/`, `LambdaCalculus/LocallyNameless/`, and
   `Logics/LinearLogic/CLL/`:**
   - `CCS` (5 files, 882 LoC) and `HML` (2 files, 381 LoC) formalize process
     calculi and modal bisimulation characterization (`s₁ ∼ s₂ ↔ ∀ φ, s₁ ⊨ φ ↔
     s₂ ⊨ φ`).
   - `LambdaCalculus/LocallyNameless/` (25 files, 4,942 LoC) formalizes Aydemir
     et al.'s cofinite locally nameless representation over `HasFresh` and
     `Finset Atom` for untyped $\lambda$-calculus, STLC, and System $F_{<:}$.
   - `Logics/LinearLogic/CLL/` (3 files, 1,929 LoC) formalizes classical
     one-sided Girard sequent calculus (`⊢ Γ`) with cut elimination
     (`CLL/CutElimination.lean`, 1,124 LoC) and phase semantics
     (`CLL/PhaseSemantics.lean`, 200 LoC).
   - **Boundary Confirmation:** `Cslib` `main` (`82db31ee`) contains **zero**
     separation logic (`sepConj`, `wand`, `pointsTo`, `Heap`, `Iris`), **zero**
     pointer/byte-memory models, and **zero** Boole/Strata imperative
     verification IR modules.

5. **Why `Cslib` Cannot Be Imported Incrementally Without `Mathlib4`, and the
   Role of `stagiralabs/VerifiedAgora`:**
   - `Cslib/Init.lean` imports `Mathlib.Init` and `Mathlib.Tactic.Common`, and
     `scripts/checkInitImports.lean` (enforced in CI) requires every `.lean`
     file in `Cslib/` to transitively import `Cslib.Init`. Furthermore, 281 of
     297 `Cslib` files directly import deeper `Mathlib.*` modules
     (`Mathlib.Data.Finset.Basic`, `Mathlib.Order.CompleteLattice`,
     `Mathlib.Logic.Relation`, `Mathlib.Algebra.Order.Ring.Nat`).
   - Throughout its entire commit history (`61f9d21` on 2025-07-04 to
     `82db31eec215b6843be6df283304cc02e736ddef` on 2026-10-30), upstream
     `leanprover/cslib`'s `lakefile.toml` and `lake-manifest.json` require only
     `leanprover-community/mathlib4` and its eight transitive packages.
   - `stagiralabs/VerifiedAgora` (`9703b9597dd37d6ec4845fc5d0480132e3db8054`,
     and `b29e0c3443416718327b9a7e9af2ee4737e6bf38` in
     `stagiralabs/eval_Computability`) is a separate Stagira Labs evaluation
     package (requiring `riyazahuja/SafeVerify`
     `5791a40d2c2a4dc8ef4ca14ae512ef846968b15a`) that registers a `@[target]`
     attribute (`VerifiedAgora/tagger.lean`), extracts tagged theorem
     declarations (`VerifiedAgora/allTargets.lean`), replays submissions in the
     kernel (`replayFileDirect` in `VerifiedAgora/getTargets.lean:16-84`), and
     audits `CollectAxioms.collect` against `AllowedAxioms := [`propext,
     `Quot.sound, `Classical.choice]` (`VerifiedAgora/Utils.lean:51-79`).

---

### 2. External Automation (`Aesop`, `Duper`, `lean-auto`, `lean-smt`)

`Basis: primary-source inspection and empirical compilation/audit probes of leanprover-community/aesop@355695d523e41d0554926416cba2a2b3544fbbc9, leanprover-community/lean-auto@6b2774cde4d1cb7ac4d48ac61c34e950e0588d69, leanprover-community/duper@9e09cd05fd541d6cef4c485882b7978d32c7e0a3, ufmg-smite/lean-smt@db545bebe2de1e06dc2df62a6ff6c20e5736bfc0 (and no_mathlib@7e54df3e5b7f78e5e6170ffab8ebe813904262b0), and leanprover-community/plausible@118aa17ee84656b8bd727fef7c458ee8c833385c`

#### 2.1 Build Time, `.olean` Footprint, and Environment Inventory (`v4.34.1`)

We compiled `Batteries`, `Aesop`, `lean-auto`, and `Duper` from source under
Lean `v4.34.1` and ran an `.olean` environment audit scanning every declaration
in the loaded package modules for `ConstantInfo.axiomInfo`, `Safety.unsafe`,
`Safety.partial`, `ConstantInfo.opaqueInfo`, `@[implemented_by]`, `@[csimp]`,
and `@[extern]`:

| Package | Pinned Revision (`v4.34.1` / `v4.34.0`) | Direct Lake Deps | Files / LoC | Source Build Wall Time (Peak RSS) | `.olean` Size (Total `.lake/build`) | Loaded Modules / Constants | Custom `axiom` Decls | `unsafe` / `partial` / `opaque` Decls | Native FFI or External Binary |
| :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **`Batteries`** | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` | *(none)* | 196 / 31,235 | `15.49 s` (`994.3 MB`) | `38.01 MB` (`95.01 MB`) | 197 / 6,999 | **0** | 16 / 169 / 111 | None |
| **`Aesop`** | `355695d523e41d0554926416cba2a2b3544fbbc9` | `Batteries` | 76 / 14,193 | `+24.83 s` (`1,105.0 MB`; `40.32 s` total) | `16.77 MB` (`51.90 MB`; `146.9 MB` w/ `Batteries`) | 132 / 6,495 | **0** | 120 / 63 / 104 | None (`precompileModules = true` C shared libs for tactic speed) |
| **`lean-auto`** (`Auto`) | `6b2774cde4d1cb7ac4d48ac61c34e950e0588d69` | *(none)* | 64 / 25,317 | `102.28 s` (`2,512.6 MB`) | `32.10 MB` (`86.58 MB`) | 71 / 12,291 | **2** (`autoSMTSorry`, `autoTPTPSorry`) | 5 / 280 / 135 | `extraDepTargets` runs `curl` to download `zipperposition.exe` unless pre-seeded |
| **`Duper`** | `9e09cd05fd541d6cef4c485882b7978d32c7e0a3` | `Batteries`, `lean-auto` | 48 / 21,981 | `+9.44 s` (`1,218.2 MB`; `127.21 s` total) | `71.30 MB` (`233.13 MB`; `414.72 MB` total) | 73 / 3,758 | **1** (`Duper.skSorryAx`) | 0 / 126 / 103 | None (`precompileModules = true`) |
| **`lean-smt`** (`main`) | `db545bebe2de1e06dc2df62a6ff6c20e5736bfc0` | `lean-cvc5`, `Mathlib4` | 94 / 22,223 | Requires `Mathlib4` + `cvc5` FFI | Depends on `Mathlib4` | — | **0** (uses open subgoals on gap) | `partial` in `Reconstruct` | Links C++ `libcvc5.so` + `libcadical.so` via `abdoo8080/lean-cvc5` |
| **`lean-smt`** (`no_mathlib`) | `7e54df3e5b7f78e5e6170ffab8ebe813904262b0` | `lean-cvc5`, `Qq` | 88 / 20,840 | Requires `cvc5` FFI (no `Mathlib4`) | Lightweight (`Qq` + `lean-cvc5`) | — | **0** (uses open subgoals on gap) | `partial` in `Reconstruct` | Links C++ `libcvc5.so` + `libcadical.so` via `abdoo8080/lean-cvc5` |
| **`Plausible`** | `118aa17ee84656b8bd727fef7c458ee8c833385c` | *(none)* | 16 / 3,776 | `<10 s` | `<15 MB` | — | **0** (emits `sorryAx` via `admitGoal`) | `partial` in generators | None |

#### 2.2 Proof-Term Extraction, Axiom Footprints, and TCB Mechanisms

1. **`Aesop` (`Aesop/Tree/ExtractProof.lean:105-189`):**
   - `Aesop` executes best-first AND/OR tree search inside `MetaM`. When the
     root `Goal` is proven, `Goal.extractProof` copies the metavariable
     assignments produced by the winning `Rapp` (rule application) nodes into
     the parent goal metavariable.
   - Because every `Rapp` applies either a core tactic (`simp`, `omega`,
     `grind`, `intros`, `cases`, `split`), a user hypothesis, or a registered
     theorem, the final proof term contains **zero** `Aesop.*` or `Batteries.*`
     constants.
   - All 120 `unsafe` and 63 `partial` definitions in `Aesop` live exclusively
     in meta-level tree search (`Aesop.Tree.*`, `Aesop.Search.*`) and never
     enter theorem closures.

2. **`Duper` (`Duper/Tactic.lean:245-261`,
   `Duper/ProofReconstruction.lean:66-92`) and `lean-auto`
   (`Auto/Tactic.lean:511-575`):**
   - **Hermeticity trap in `lean-auto`:** `lean-auto/lakefile.lean:38-78`
     attaches a `Zipperposition` download `extraDepTargets` target to `lean_lib
     Auto`. During `lake build`, `lakefile.lean:38-55` checks whether
     `.lake/build/zipperposition.exe` exists; if absent, it spawns `curl` to
     download a GitHub release binary. In a hermetic sandbox, one must
     pre-create an empty file at
     `.lake/packages/auto/.lake/build/zipperposition.exe` before `lake build`
     and set `set_option auto.tptp false` and `set_option auto.smt false`.
   - **Monomorphization and reification (`Auto.Embedding.Lam`):** `Duper`
     invokes `Auto.mono` (`Duper/Tactic.lean:295-330`) to monomorphize
     polymorphic/higher-order hypotheses into a simple type hierarchy
     (`Auto.Embedding.Lam`) and checks clause preprocessing steps via
     `LamReif.newBkts` (`Auto/Tactic.lean:558-575`). By default,
     `auto.checker.buildMode` (`Auto/Tactic.lean:31-48`) is `.indirectReduce`,
     which proves the reified checker equation by pure kernel `Eq.refl true`
     reduction (`propext`, `Quot.sound`, `Classical.choice`). If a user sets
     `set_option auto.checker.buildMode .indirectReduce_reflection`, `lean-auto`
     instead emits `Lean.ofReduceBool` (`Lean.trustCompiler`), which
     `anneal-audit` rejects.
   - **Unsound solver-trust axioms in `lean-auto`:**
     `Auto/Lib/MonadUtils.lean:31-36` declares two custom axioms:
     ```lean
     axiom autoSMTSorry .{u} (α : Sort u) : α
     axiom autoTPTPSorry .{u} (α : Sort u) : α
     ```
     used only when `auto.smt.trust true` or `auto.tptp.trust true` is enabled.
   - **Temporary Skolem axiom in `Duper`:** `Duper/SpClause.lean:34` declares:
     ```lean
     axiom skSorryAx (α : Sort u) : α
     ```
     During superposition saturation (`runProver` in
     `Duper/Tactic.lean:245-261`), `Duper` wraps saturation in
     `withoutModifyingCoreEnv` and adds temporary constants whose bodies
     reference `skSorryAx` (`Duper/ProverM.lean:393-402`). Once `emptyClause` is
     derived, `withoutModifyingCoreEnv` rolls back the environment and
     `applyProofReconstructor` (`Duper/ProofReconstruction.lean:66-92`) replaces
     every `skSorryAx` occurrence with `Duper.Skolem.some` (`Classical.choose`).
     Thus `skSorryAx` never appears in the final theorem's `#print axioms`
     footprint (`[propext, Classical.choice, Quot.sound]`).
   - **Proof-closure coupling:** Unlike `Aesop`, every theorem proved by `Duper`
     embeds `Auto.Embedding.Lam` reification terms and `Duper.Rule.*`
     reconstruction lemmas directly into the theorem's `Expr` value (87
     recursive definitions in the transitive constant closure), permanently
     coupling the resulting `.olean` artifact to `lean-auto` and `Duper`.

3. **`lean-smt` (`main` `db545bebe2de1e06dc2df62a6ff6c20e5736bfc0` and
   `no_mathlib` `7e54df3e5b7f78e5e6170ffab8ebe813904262b0`):**
   - `lean-smt` calls `cvc5` in-process via `abdoo8080/lean-cvc5`
     (`41e47796d4d15712e6064b064ca5d251a1283955`) and reconstructs `cvc5`'s CPC
     (Cooperating Proof Calculus) proof steps into Lean `Expr` proof terms using
     type-correct kernel theorems in `Smt/Reconstruct/` (`Prop`, `UF`, `Quant`,
     `Int`, `Rat`, `BitVec`, `Arith`, `Datatype`).
   - **`no_mathlib` branch (`7e54df3e5b7f78e5e6170ffab8ebe813904262b0`,
     2026-10-09):** Replaces `require mathlib` in `lakefile.toml` with `require
     Qq` (`quote4`), reimplementing `Int` and `Rat` linear/polynomial
     normalization on top of Lean 4.34's core `Init.Grind.CommRing`
     (`Smt/Reconstruct/Rat/Core.lean`). Only real-number (`Real`) reconstruction
     is omitted on `no_mathlib`.
   - **Behavior on unreconstructed CPC steps (`Smt/Reconstruct.lean:200-207`,
     `Smt/Tactic/Smt.lean:314-316`):** When `cvc5` emits a CPC rule not yet
     supported by `Smt/Reconstruct`, `reconstructProof` calls `addTrust` →
     `skipStep`, which creates a fresh open metavariable `mv`
     (`Meta.mkFreshExprMVar`) and appends it to `skippedGoals`. At tactic
     completion, `smt` calls `Tactic.replaceMainGoal mvs`, leaving any
     unreconstructed step as an **explicit unsolved Lean subgoal** for the user
     or a fallback tactic (`omega`, `grind`, `bv_decide_kernel`) to close—never
     silently injecting `sorryAx` unless the user explicitly passes `smt
     +trust`.

4. **`Plausible` (`118aa17ee84656b8bd727fef7c458ee8c833385c`):**
   - `Plausible/Tactic.lean:195-210` runs random counterexample testing via
     `Testable.checkLawful`; if no counterexample is found after `numInst`
     trials, line 206 executes `admitGoal g`, which closes the goal with
     `sorryAx`. Consequently, `plausible` is strictly an interactive
     falsification aid and is rightly rejected by `anneal-audit`.

---

### 3. Head-to-Head Benchmark Across 14 Anneal MIR VCs (Classes A–E)

`Basis: machine-checked proofs and empirical timing/closure/replay measurements in support/CoreVCTacticBenchmarkProbe.lean, support/ExternalAesopDuperBenchmarkSuite.lean, ElabProbes.lean, and RunBenchmarks.lean`

We evaluated six tactic configurations (`omega`, `grind`, `aesop`, `duper`,
`bv_decide_kernel`, and `bv_decide`) across 14 representative Anneal MIR
verification conditions in five classes:

- **Class A (`#71`, `#73` — Layout & Alignment Arithmetic):**
  - `A1`: 3-field `#[repr(C)]` struct byte-offset non-overlap (`fieldEnd`).
  - `A2`: `alignUp offset align` lower and upper bounds (`alignUpFromRem`).
  - `A3`: 64-bit power-of-two bitmask alignment `(x + 7#64) &&& ~~~7#64`.
- **Class B (`#72` — `ByteMemory` & Allocation Frame Disjointness):**
  - `B1`: Quantified byte-range disjointness (`∀ i < n, ∀ j < m, base1 + i ≠
    base2 + j`).
  - `B2`: Reading from an updated `ByteMemory` map after a disjoint 4-byte
    `writeWord32`.
  - `B3`: First-order quantified allocation-frame preservation across disjoint
    ranges.
- **Class C (`MirLang.SpecOn` — Coupled Existential Return Witness
  Obligations):**
  - `C1`: `∃ retVal : Int, evalInc (x + 1) = some retVal ∧ retVal > x`.
  - `C2`: `SimplePartial.leProp (progSem x) (specOnNonneg x)` coupled
    refinement.
- **Class D (`#71` — 64-Bit `BitVec` Overflow & Bitfield Manipulation):**
  - `D1`: `(!BitVec.uaddOverflow x y) = (x + y ≥ x)` on `BitVec 64`.
  - `D2`: Signed two's-complement addition bounds (`BitVec.saddOverflow` +
    `BitVec.sle`) on `BitVec 64`.
  - `D3`: 32-bit/64-bit bitfield pack and `extractLsb'` round-trip on `BitVec
    64`.
- **Class E (`#77` — Tree/Stacked Borrows & Higher-Order Relational
  Obligations):**
  - `E1`: Tree Borrows 3-step transitive `Parent`/`Ancestor` tag propagation.
  - `E2`: Stacked Borrows `PermLe` permission lattice transitivity + stack
    inclusion.
  - `E3`: Higher-order tag/location footprint disjointness (`proj t1 ≠ proj
    t2`).
  - `E4`: Multi-step relational witness chain (`∀ x, Valid x → R x (step x) ∧
    Valid (step x)`).

#### 3.1 Master Benchmark Matrix (Elaboration, Proof Size, Replay, and Axioms)

In the table below:
- **Elab (ms):** Median wall-clock tactic elaboration time across 5 runs in Lean
  `v4.34.1`.
- **Direct / Closure `numObjs`:** `Expr.numObjs` of the theorem's proof term and
  summed across all project-local auxiliary definitions in its transitive
  closure.
- **Kernel Replay (ms):** `Kernel.Environment.replay` time at `trustLevel := 0`.
- **Axioms:** `P` = `propext`, `C` = `Classical.choice`, `Q` = `Quot.sound`, `N`
  = `_native.bv_decide.ax_*` (rejected by `anneal-audit`).

| Problem | Tactic Configuration | Status | Elab (ms) | Direct / Closure `numObjs` | Kernel Replay (ms) | Axioms (`#print axioms`) |
| :--- | :--- | :--- | ---: | ---: | ---: | :--- |
| **`A1`** (Struct field non-overlap) | `unfold fieldEnd at *; omega` | **Solved (1-line hint)** | `3.55` | `322` / `322` | `0.36` | `{P, C, Q}` |
| **`A1`** | `grind` (unfolded hyps) / `grind` (`@[grind =]`) | **Solved (OOB / hint)** | `8.86` / `8.29` | `462` / `465` | `1.30` / `0.95` | `{P, C, Q}` |
| **`A1`** | `aesop (add safe tactic (by omega))` | **Solved (hint)** | `16.30` | `320` / `320` | `0.40` | `{P, C, Q}` |
| **`A1`** | `aesop` (OOB) / `duper [*]` | **Failed** | `5.32` / `54.73` | — | — | — |
| **`A2`** (`alignUp` bounds) | `unfold alignUpFromRem; split <;> omega` | **Solved (1-line hint)** | `5.39` | `124` / `124` | `0.49` | `{P, C, Q}` |
| **`A2`** | `grind` (inlined `ite`) / `grind` (`@[grind =]`) | **Solved (OOB / hint)** | `6.14` / `5.97` | `202` / `184` | `1.07` / `0.97` | `{P, C, Q}` |
| **`A2`** | `aesop (add safe tactic (by omega))` | **Solved (hint)** | `49.94` | `129` / `129` | `0.50` | `{P, C, Q}` |
| **`A2`** | `aesop` (OOB) / `duper [*]` | **Failed** | `7.17` / `45.36` | — | — | — |
| **`A3`** (`BitVec 64` mask align) | `bv_decide_kernel` | **Solved (OOB)** | `14.55` | `18` / `1,353` | `2,315.42` | `{P, C, Q}` |
| **`A3`** | `bv_decide` (standard) | **Solved (OOB, unsafe)** | `129.50` | `59` / `3,205` | `0.73` | `{P, C, Q, N}` |
| **`A3`** | `omega` / `grind` / `aesop` / `duper [*]` | **Failed** | `1.2–48.2` | — | — | — |
| **`B1`** (`ByteMemory` range disj) | `intro i hi j hj; omega` | **Solved (OOB)** | `1.97` | `121` / `121` | `0.19` | `{P, Q}` |
| **`B1`** | `grind` (OOB) | **Solved (OOB)** | `4.19` | `151` / `151` | `0.64` | `{P, C, Q}` |
| **`B1`** | `aesop (add safe tactic (by omega))` | **Solved (hint)** | `11.12` | `121` / `121` | `0.21` | `{P, Q}` |
| **`B1`** | `aesop` (OOB) / `duper [*]` | **Failed** | `6.45` / `35.61` | — | — | — |
| **`B2`** (Disjoint 4-byte write) | `grind [ByteMemory.writeByte]` / `grind` (`@[grind =]`) | **Solved (OOB / hint)** | `9.29` / `11.83` | `327` / `361` | `0.94` / `1.07` | `{P, C, Q}` |
| **`B2`** | `unfold ...; rw [beq_false_of_ne (by omega)...]` | **Solved (manual)** | `5.82` | `402` / `402` | `0.40` | `{P, Q}` |
| **`B2`** | `aesop` (`read_writeByte_ne` + `omega`) | **Solved (hint)** | `44.91` | `258` / `334` | `0.62` | `{P, Q}` |
| **`B2`** | `duper [*, ByteMemory.writeWord32, ...]` | **Failed** | `74.40` | — | — | — |
| **`B3`** (Quantified frame pres.) | `grind` (OOB) | **Solved (OOB)** | `5.52` | `63` / `63` | `0.38` | `{P, C, Q}` |
| **`B3`** | `aesop (add unsafe Ne.symm)` | **Solved (1-rule hint)** | `15.65` | `33` / `33` | `0.21` | `{P, C, Q}` |
| **`B3`** | `duper [*]` (OOB) | **Solved (OOB)** | `255.28` | `1,816` / `1,816` | `46.57` | `{P, C, Q}` |
| **`C1`** (`∃ retVal` `evalInc`) | `refine ⟨_, rfl, by omega⟩` | **Solved (structural)** | `1.19` | `31` / `31` | `0.95` | `{P, Q}` |
| **`C1`** | `refine ⟨_, rfl, by grind⟩` | **Solved (structural)** | `4.89` | `66` / `66` | `1.55` | `{P, C, Q}` |
| **`C1`** | `aesop (add safe tactic (by omega))` | **Solved (hint)** | `9.69` | `31` / `31` | `1.05` | `{P, Q}` |
| **`C1`** | `aesop (add safe tactic (by grind))` | **Solved (hint)** | `15.46` | `66` / `66` | `1.70` | `{P, C, Q}` |
| **`C1`** | `grind` (OOB) / `refine ⟨?w, ?h1, ?h2⟩` / `duper` | **Failed** | `3.15–38.27` | — | — | — |
| **`C2`** (`SpecOn` `SimplePartial`) | `intro h2; refine ⟨h2, fun out hout => ⟨_, rfl, by omega, by omega⟩⟩` | **Solved (structural)** | `2.45` | `118` / `118` | `0.62` | `{P, Q}` |
| **`C2`** | `intro h2; refine ⟨h2, fun out hout => ⟨_, rfl, by grind⟩⟩` | **Solved (structural)** | `5.80` | `194` / `194` | `1.10` | `{P, C, Q}` |
| **`C2`** | `aesop (rule_sets := [AnnealBench]) (add safe tactic (by omega))` | **Solved (hint)** | `25.13` | `149` / `149` | `0.78` | `{P, Q}` |
| **`C2`** | `aesop (rule_sets := [AnnealBench]) (add safe tactic (by grind))` | **Solved (hint)** | `38.67` | `233` / `233` | `1.25` | `{P, C, Q}` |
| **`C2`** | `grind` (OOB) / `duper [*]` | **Failed (`duper` PANIC)** | `3.21` / `25,340.7` | — | — | — |
| **`D1`** (`BitVec 64` `uaddOverflow`) | `bv_decide_kernel` | **Solved (OOB)** | `9.09` | `18` / `1,303` | `848.88` | `{P, C, Q}` |
| **`D1`** | `bv_decide` (standard) | **Solved (OOB, unsafe)** | `78.14` | `55` / `1,481` | `0.26` | `{P, C, Q, N}` |
| **`D1`** | `omega` / `grind` / `duper` | **Failed** | `1.18–45.7` | — | — | — |
| **`D2`** (`BitVec 64` `saddOverflow`) | `bv_decide_kernel` | **Solved (OOB)** | `14.52` | `18` / `1,488` | `9,425.66` | `{P, C, Q}` |
| **`D2`** | `bv_decide` (standard) | **Solved (OOB, unsafe)** | `100.38` | `79` / `9,040` | `1.47` | `{P, C, Q, N}` |
| **`D2`** | `omega` / `grind` | **Failed** | `1.54` / `12.69` | — | — | — |
| **`D3`** (`BitVec 64` bitfield pack) | `grind` (OOB) | **Solved (OOB)** | `128.46` | `17` / `1,158` | `14.55` | `{P, C, Q}` |
| **`D3`** | `bv_decide_kernel` | **Solved (OOB)** | `10.18` | `18` / `1,334` | `529.71` | `{P, C, Q}` |
| **`D3`** | `bv_decide` (standard) | **Solved (OOB, unsafe)** | `90.26` | `59` / `2,043` | `0.34` | `{P, C, Q, N}` |
| **`E1`** (Tree Borrows ancestry) | `have h_base := ...; grind` | **Solved (1-line hint)** | `11.92` | `66` / `66` | `0.68` | `{P, C, Q}` |
| **`E1`** | `aesop` (OOB) | **Solved (OOB)** | `462.96` | `124` / `124` | `0.20` | `{P, C, Q}` |
| **`E1`** | `duper [*]` (OOB) | **Solved (OOB)** | `553.96` | `3,230` / `3,230` | `63.83` | `{P, C, Q}` |
| **`E1`** | `grind` (OOB without `h_base`) | **Failed** | `7.15` | — | — | — |
| **`E2`** (Stacked Borrows `PermLe`) | `have h1 := ...; have h2 := ...; grind` | **Solved (2-line hint)** | `9.20` | `62` / `62` | `0.40` | `{P, C, Q}` |
| **`E2`** | `aesop (rule_sets := [AnnealBench]) (add norm ...)` | **Solved (rule-set hint)** | `36.32` | `26` / `26` | `0.16` | `{P, C, Q}` |
| **`E2`** | `duper [*, permLe_refl, permLe_trans, ...]` | **Solved (lemma list)** | `469.51` | `2,590` / `2,718` | `46.51` | `{P, C, Q}` |
| **`E3`** (Higher-order footprint) | `grind` (OOB) | **Solved (OOB)** | `4.47` | `72` / `72` | `0.55` | `{P, C, Q}` |
| **`E3`** | `aesop` (OOB) | **Solved (OOB)** | `24.80` | `172` / `172` | `0.31` | `{P, C, Q}` |
| **`E3`** | `duper [*]` (OOB) | **Solved (OOB)** | `324.49` | `1,774` / `1,774` | `42.20` | `{P, C, Q}` |
| **`E4`** (Witness chain `∃ t2`) | `grind` (OOB) | **Solved (OOB)** | `13.26` | `122` / `122` | `1.03` | `{P, C, Q}` |
| **`E4`** | `duper [*]` (OOB) | **Solved (OOB)** | `358.57` | `2,243` / `2,243` | `36.76` | `{P, C, Q}` |
| **`E4`** | `aesop` (OOB) | **Failed** | `1,839.29` | — | — | — |

#### 3.2 Key Technical Takeaways by Problem Class

1. **Why Coupled Existential Witnesses (`C1`, `C2`) Break Standalone `grind`,
   `omega`, and `duper`:**
   - In `C1` (`∃ retVal : Int, evalInc (x + 1) = some retVal ∧ retVal > x`),
     calling `grind` or `omega` directly fails (`3.15 ms`) because `grind` does
     not perform unification-driven existential witness introduction before
     running `cutsat`.
   - Even after `refine ⟨?w, ?h1, ?h2⟩`, running `grind` or `omega` on `?h1` or
     `?h2` fails (`2.16–4.59 ms`) because `grind` and `omega` treat unassigned
     term metavariables (`?w : Int`) as opaque atoms rather than assignable
     unification variables.
   - Worse, on `C2` (`SimplePartial.leProp (progSem x) (specOnNonneg x)`),
     `duper [*]` triggers an internal Lean 4.34.1 compiler/metaprogramming
     panic:
     ```text
     PANIC at Lean.Meta.whnfEasyCases Lean.Meta.WHNF:331:37: loose bvar in expression
     ```
     during Skolemization of the dependent existential `∃ h1 : p1.defined, ...`
     before timing out at `25,340.7 ms`.
   - **Solution for `anneal-rustc-capture`:** Always discharge the operational
     evaluation equation `eval ... = some ?w` **first** via `rfl` inside `refine
     ⟨_, rfl, by grind⟩` (or `by omega`), which instantiates `?w` by
     definitional equality and hands a purely ground arithmetic goal to `grind`
     or `omega` (`1.19–4.89 ms`). Alternatively, `aesop (add safe tactic (by
     grind))` automatically applies `Exists.intro`, `And.intro`, and `rfl` on
     the first conjunct before invoking `grind` on the remaining subgoal (`15.46
     ms`).

2. **64-Bit `BitVec` Trade-Offs (`A3`, `D1`, `D2`, `D3` — `bv_decide_kernel` vs
   `bv_decide` vs `grind`):**
   - Standard `bv_decide` elaborates in `78.14–129.50 ms` and replays in the
     kernel in `0.26–1.47 ms`, but every theorem depends on
     `_native.bv_decide.ax_1_5` and `Lean.ofReduceBool` (`Lean.trustCompiler`),
     which `anneal-audit` rejects.
   - `bv_decide_kernel` (`support/CoreVCTacticBenchmarkProbe.lean`) reuses
     `Std.Tactic.BVDecide`'s `Normalize.bvNormalize` and `Reflect.reflectBV`
     front-end and discharges `BVLogicalExpr.Unsat` via an in-kernel ROBDD
     evaluator (`checkBVLogicalUnsat`) and `eagerReduce`. Because it skips
     CaDiCaL and LRAT trimming/serialization, `bv_decide_kernel` elaborates
     **`6.5x–8.9x` faster** (`9.09–14.55 ms`) than standard `bv_decide` with
     zero `_native` axioms (`{propext, Classical.choice, Quot.sound}`).
   - Its cost shifts to **kernel type-checking / replay**: reducing the 64-bit
     ROBDD inside `Kernel.Environment` takes `529.71 ms` on `D3`, `848.88 ms` on
     `D1`, `2,315.42 ms` on `A3`, and `9,425.66 ms` on `D2` (two 64-bit
     variables with four signed `BitVec.sle` comparisons).
   - Crucially, on **`D3` (64-bit bitfield packing and extraction)**—which has
     no arithmetic carry chain—`grind` solves the goal out-of-the-box in `128.46
     ms` elaboration, emitting a 17-node congruence/extensionality proof that
     replays in the kernel in **`14.55 ms` (`36.4x` faster kernel replay than
     `bv_decide_kernel`)**.

3. **E-Matching Trigger Patterns vs Backward Rule Search vs Superposition on
   Borrow-Checker Relational Obligations (`E1`–`E4`):**
   - On **`E1` (Tree Borrows 3-step ancestry)**, out-of-the-box `grind` fails in
     `7.15 ms` because `h_refl : ∀ t, Ancestor t t` has the E-matching pattern
     `[Ancestor #0 #0]`, which only fires when an `Ancestor x y` term already
     exists in the E-graph, and `h_step : ∀ t1 t2 t3, Parent t1 t2 → Ancestor t2
     t3 → Ancestor t1 t3` requires both `Parent` and `Ancestor` to trigger.
     Neither rule seeds `Ancestor t3 t3` from `Parent t2 t3`. Supplying the
     1-step forward base rule `have h_base : ∀ a b, Parent a b → Ancestor a b :=
     fun a b hp => h_step a b b hp (h_refl b)` allows `grind` to solve `E1` in
     **`11.92 ms`** (`0.68 ms` kernel replay), compared to `462.96 ms` for
     `aesop` and `553.96 ms` for `duper [*]`.
   - On **`E4` (`∀ x, Valid x → R x (step x) ∧ Valid (step x)`)**, `aesop` fails
     (`1,839.29 ms`) because its backward `apply` engine cannot decompose a
     universally quantified conjunction in the conclusion of a hypothesis
     without forward-rule destructuring. Both `grind` (`13.26 ms` elab, `1.03
     ms` replay) and `duper [*]` (`358.57 ms` elab, `36.76 ms` replay)
     automatically split `∀ x, Valid x → R x (step x) ∧ Valid (step x)` into two
     Horn clauses (`Valid x → R x (step x)` and `Valid x → Valid (step x)`) and
     synthesize the witness `t2 := step (step t0)`.

---

### 4. Proof-Dependency Decoupling and Architectural Decision Matrix for Anneal

`Basis: transitive constant-closure inspection and Kernel.Environment.replay measurements across support/ExternalAesopDuperBenchmarkSuite.lean and support/CoreVCTacticBenchmarkProbe.lean`

#### 4.1 Transitive Constant-Closure Comparison (`grind` vs `aesop` vs `duper`)

Inspecting the constants referenced by compiled theorem bodies across Classes B3
and E1–E4 reveals a fundamental architectural difference between `aesop` and
`duper`:

| Metric (Classes B3, E1–E4) | Core `grind` | `Aesop` (`v4.34.0`) | `Duper` (`v4.34.1`) + `lean-auto` (`v4.34.1`) |
| :--- | :--- | :--- | :--- |
| **External packages referenced in proof term** | **0** (`Init` only) | **0** (`Init` only) | **2** (`Auto.Embedding.Lam.*`, `Duper.Rule.*`, `Duper.Skolem.*`) |
| **Direct proof DAG size (`Expr.numObjs`)** | `62–122` nodes | `26–172` nodes | `1,774–3,230` nodes (`15x–99x` larger) |
| **Recursive helper defs in transitive closure** | Core `Lean.Grind.*` only | **0** | **87** (`LamTerm.interp`, `LamWF.interp`, `LamReif.*`, etc.) |
| **`Kernel.Environment.replay` time (`trustLevel := 0`)** | `0.38–1.03 ms` | `0.16–0.31 ms` | `36.76–63.83 ms` (`50x–300x` slower) |
| **Axiom footprint (`#print axioms`)** | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` |

Because `Aesop` splices rule applications directly via `Goal.extractProof`, its
proof terms are indistinguishable from hand-written core-Lean `apply`/`intro`
proofs and replay in the kernel in `0.16–0.31 ms`. Conversely, `Duper` proof
terms embed deeply nested `Auto.Embedding.Lam` reification terms that force the
Lean kernel to unfold and reduce `LamWF.interp` and `LamReif` checker proofs
during `Kernel.Environment.replay`.

#### 4.2 Recommended Dependency and Tactic Architecture for Anneal

| Subsystem / Layer | Decision | Technical Justification |
| :--- | :--- | :--- |
| **`trusted/lean/`** | **Zero external dependencies (`Init`/`Std` only)** | Preserves minimal TCB and zero external `.olean` surface for `Trusted.CrateTheorem`. |
| **`theory/` (Foundational library)** | **Do not depend on `Mathlib4`, `Cslib`, `Duper`, `lean-auto`, or `lean-smt`; selectively vendor pure patterns** | Port `Cslib`'s `LTS`/`BisimulationUpTo` (`<300 LoC`) and `TimeM` (`<100 LoC`) directly over `Init`/`Std`. Avoids `Mathlib4`'s 8-package transitive graph and `lean-auto`'s non-hermetic `zipperposition.exe` `extraDepTargets` hook. |
| **`trusted/rustc-capture/` (VC tactic script generator)** | **Tier 1: `refine ⟨_, rfl, ...⟩` + `omega` + `grind` (`@[grind =]`, `@[grind →]`) + `bv_decide_kernel`** | Solves 100% (14/14) of benchmark VCs across Classes A–E with zero external dependencies, sub-15 ms elaboration on arithmetic/relational VCs, and sub-2 ms kernel replay on non-bitblasted VCs. |
| **Optional `Aesop` integration in `theory/`** | **Permissible if backward AND/OR tree search is desired (`v4.34.0` `355695d5`)** | Adds only `40.32 s` source build time (`Batteries` + `Aesop`), zero custom axioms, and emits `Init`-only proof terms (`0.16–0.31 ms` kernel replay). |

## Boundaries

1. **Nonlinear integer arithmetic (`x * y`, `/`, `%` with variable divisors) and
   wide bitvector arithmetic (`w > 64`):** Neither `omega` nor `grind` decides
   nonlinear integer multiplication over variables without explicit lemmas, and
   `bv_decide_kernel`'s in-kernel ROBDD reduction scales exponentially on 64-bit
   multipliers or multi-variable signed comparison chains (`9.43 s` kernel
   replay on `D2`). Bitfield and bitwise masking goals without carry chains
   (`D3`) should be routed to `grind` (`14.55 ms` replay) before falling back to
   `bv_decide_kernel`.
2. **`lean-smt` native FFI boundary:** Although `ufmg-smite/lean-smt`'s
   `no_mathlib` branch (`7e54df3e5b7f78e5e6170ffab8ebe813904262b0`) eliminates
   the `Mathlib4` dependency and produces kernel-checked `Expr` proofs (or
   explicit open subgoals via `skipStep`), its build still requires compiling
   and linking C++ `libcvc5.so` and `libcadical.so` via `abdoo8080/lean-cvc5`.
3. **Module-system (`module` + `public meta import`) requirement under strict 1
   GiB memory caps (`lean -j1 -M1024`):** Importing `Lean.Elab.Tactic.BVDecide`
   via a legacy non-`module` `import` loads the full `Lean` metaprogramming
   environment into the kernel's public constant table and exceeds `-M1024`
   during ROBDD reduction. Enabling `module` with `public meta import
   Lean.Elab.Tactic.BVDecide` and `public meta import
   Lean.Meta.Tactic.Grind.Main` keeps metaprogramming declarations out of the
   kernel's public constant table so `support/CoreVCTacticBenchmarkProbe.lean`
   compiles cleanly within `-M1024`.

## Evidence

- **[`support/CoreVCTacticBenchmarkProbe.lean`](support/CoreVCTacticBenchmarkProbe.lean)**
  (1,061 lines, SHA-256
  `47b29ea4a4cc71962637946aea0540d48f63549c209d99fe55d652f9e9b439a3`):
  Standalone, zero-dependency, zero-`sorry`, zero-warning Lean `v4.34.1` probe
  containing `KernelBVDecide` and 25 core-Lean benchmark theorems across all 14
  problems (`A1`–`A3`, `B1`–`B3`, `C1`–`C2`, `D1`–`D3`, `E1`–`E4`), with `#print
  axioms` confirming that every theorem depends only on subsets of `{propext,
  Classical.choice, Quot.sound}`.
- **[`support/ExternalAesopDuperBenchmarkSuite.lean`](support/ExternalAesopDuperBenchmarkSuite.lean)**
  (522 lines, SHA-256
  `177406f86470848b88ba4142ce7fdcd32fc3da5fbc9ff12ec8cf438e171ead86`): Complete
  multi-package (`Aesop` `v4.34.0` + `Duper` `v4.34.1` + `lean-auto` `v4.34.1` +
  `KernelBVDecide`) benchmark suite containing all 41 compiled head-to-head
  theorems across Classes A–E.
- **[`support/source-manifest.json`](support/source-manifest.json)**:
  Machine-readable manifest recording all 10 inspected upstream repositories,
  pinned 40-character commit hashes, inspected file paths, line counts, and
  SHA-256 digests.

## Revalidation

To revalidate the standalone core-Lean benchmark probe under Lean `v4.34.1` with
a single worker thread and a 1 GiB memory cap:

```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M1024 \
  reports/lean4-external-libraries-cslib-aesop-duper-and-vc-benchmarks-2026/support/CoreVCTacticBenchmarkProbe.lean
```

Every `#print axioms` line in the output must list only subsets of `[propext,
Classical.choice, Quot.sound]`, and the command must exit with status `0` and
zero warnings.

Revalidate this report when:
1. Anneal upgrades its pinned Lean toolchain beyond `leanprover/lean4:v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`).
2. `leanprover/cslib` decouples `Cslib.Foundations.Semantics.LTS` or
   `Cslib.Algorithms.Lean.TimeM` from `Cslib.Init` / `Mathlib.Init`.
3. `leanprover-community/lean-auto` removes the `zipperposition.exe`
   `extraDepTargets` download hook or reduces the `Auto.Embedding.Lam`
   reification proof footprint emitted by `Duper`.
