<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Lean `v4.34.1` Core Tactics, Kernel-Reducible `bv_decide`, `omega`/`grind`, `Std.Do`, and `Std.Data` Containers Under Strict Kernel Auditing

## Summary

Verifying systems code in Lean `v4.34.1` under an uncompromising kernel trust
boundary—one that admits only `{Classical.choice, Quot.sound, propext}`,
rejects `native_decide` and `Lean.trustCompiler`, and replays compiled `.olean`
declarations through `Kernel.Environment.replay`—requires separating tactics
and standard-library abstractions that produce pure kernel proof terms from
those that rely on native code evaluation or opaque runtime primitives:

1. **Upstream `bv_decide` vs. In-Kernel Bitvector Reflection
   ([`support/ProbeBVDecide.lean`](support/ProbeBVDecide.lean),
   [`support/DiagnoseReduce.lean`](support/DiagnoseReduce.lean)):**
   In Lean `v4.34.1`, `Lean.ofReduceBool` and `Lean.trustCompiler` are
   deprecated (`src/lean/Init/Core.lean:2337–2409`). Instead, `bv_decide` calls
   `Lean.Meta.nativeEqTrue \`bv_decide` (`src/lean/Lean/Meta/Native.lean:37–87`)
   inside `LratCert.toReflectionProof`
   (`src/lean/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26–44`), which
   evaluates `verifyBVExpr` via `unsafe evalConst Bool` and injects a fresh
   per-theorem axiom `<thm>._native.bv_decide.ax_1_5` into the kernel
   environment. Simply replacing `nativeEqTrue` with `Eq.refl true` on upstream
   `Std.Tactic.BVDecide.Reflect.verifyBVExpr` fails to reduce in the kernel
   because of seven independent reduction blockers across `Std.Sat` and
   `Std.Tactic.BVDecide`: `partial def LRAT.Parser.parseActions` and `opaque
   String.toUTF8`, `@[irreducible] Std.DHashMap.Internal.mkIdx` (plus `opaque
   System.Platform.getNumBits` and `opaque mixHash`), `BVExpr.bitblast.go`'s
   `Std.DHashMap` cache, `@[irreducible] Std.Sat.AIG.Cache`, well-founded
   `Std.Sat.AIG.denote.go` (`termination_by (x, 0)`),
   `AIG.Entrypoint.relabelNat` / `CNF.relabelFin`, and `@[irreducible]
   LRAT.Internal.DefaultClause.ofArray.folder`. However, upstream `bv_decide`'s
   normalization (`Normalize.bvNormalize`) and reflection (`Reflect.reflectBV`)
   front-end constructs a 100% kernel-checked proof of `bvExpr.Unsat → False`
   using only `{propext, Classical.choice, Quot.sound}`. Replacing only the
   final `bvExpr.Unsat` step yields two complete, zero-`_native`-axiom kernel
   reflection procedures:
   - `KernelLRAT.checkCert` (`ProbeBVDecide.lean:78–296`): a total,
     list-based Reverse Unit Propagation (RUP) checker whose soundness theorem
     `checkCert_sound` discharges unsatisfiable CNF formulas via `decide
     +kernel` in **6.21 ms** using only `[propext, Quot.sound]`.
   - `KernelBVDecide.checkBVLogicalUnsat` and `bv_decide_kernel`
     (`ProbeBVDecide.lean:307–1006`): a total, `Std.HashMap`-free Reduced
     Ordered Binary Decision Diagram (ROBDD) bitblaster using structural
     recursion (`BDD.rec`), interleaved LSB-to-MSB bit ordering, and the
     propagate-generate basis `(x_i, x_i ^^ y_i)` so that $w$-bit ripple-carry
     addition has exact linear BDD size $2w + 1$ (131 nodes at bit 64). Hooked
     into `Normalize.bvNormalize` and `Reflect.reflectBV` via `eagerReduce
     (Eq.refl true)`, `bv_decide_kernel` proves 64-bit `BitVec` and `UInt64`
     alignment, masking, and overflow obligations in **456 ms – 3.02 s** in the
     kernel using only `[propext, Classical.choice, Quot.sound]`.

2. **`omega` and `grind` Under `prelude` and `TrustedBoundary.lean`
   ([`support/ProbeGrindOmega.lean`](support/ProbeGrindOmega.lean),
   [`support/DiagnoseReduce.lean`](support/DiagnoseReduce.lean)):**
   Neither `omega` (`src/lean/Lean/Elab/Tactic/Omega/Core.lean:107, 111, 224`,
   which uses `mkDecideProof` and `mkEqReflWithExpectedType`) nor `grind`
   (`src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean:240–300`, which
   uses `eagerReflBoolTrue` = `eagerReduce (Eq.refl true)`) ever emits native
   axioms; all generated proof terms depend solely on subsets of
   `{Classical.choice, Quot.sound, propext}`. Under an explicit `prelude`
   header, `omega` requires **76** transitive `Init.*` modules (51 currently in
   Anneal's `trusted/lean/foundation-lock.json` plus 25 additional `Init.*`
   modules), minimal `grind` (`grind -lia -ring -linarith`) requires **172**
   `Init.*` modules, and full `grind` (`lia`, `ring`, `linarith`, `ToInt` over
   `Nat`, `Int`, `UInt64`, `USize`, and `BitVec`) requires **247** `Init.*`
   modules via explicit imports of `Init.Omega`, `Init.Grind`,
   `Init.GrindInstances`, and `Init.Data.Int.OfNat`. In a `prelude` file,
   `import Init.Data.Int.OfNat` is mandatory because `Init/Grind/*.lean` uses
   the `module` system and imports `Init.Data.Int.OfNat` privately, whereas
   Cutsat's `Nat` elaborator (`Lean/Meta/Tactic/Grind/Arith/Cutsat/Nat.lean:41`)
   constructs proof terms referencing `Nat.ToInt.of_le`. Expanding
   `foundation-lock.json` to either the 76-module `Init.Omega` closure or the
   247-module `Init.Grind` closure also exposes five lazy on-demand equation
   theorems (`List.drop.eq_def`, `List.takeWhile.eq_def`, `List.take.eq_def`,
   `List.eraseIdx.eq_def`, and `List.find?.eq_def`) that are realized
   independently in multiple `Init.*` modules with identical `.type` but
   distinct proof terms (`stored.value? true != ci.value? true`), requiring
   `trusted/audit/TrustedBoundary.lean:851` to scope its value-equality check
   to `orig == m.module` (or `!foundation.contains m.module`).

3. **`Std.Do` (`SPred`, `WP`, `Triple`, `mvcgen`) and `Std.Data` Containers
   ([`support/ProbeStdDoData.lean`](support/ProbeStdDoData.lean)):**
   `Std.Do` provides a universe-polymorphic weakest-precondition calculus
   (`SVal`, `SPred`, `PostShape`, `PostCond`, `PredTrans`, `WP`, `WPMonad`, and
   `Triple`) whose verification condition generator `mvcgen` discharges
   stateful and exception-raising monadic specifications (`StateM`, `EStateM`)
   via `omega` and `grind` using only `[propext, Classical.choice, Quot.sound]`.
   Admitting `mvcgen` into Anneal's strict compiler audit requires passing
   `-Dmvcgen.warning=false` (because `Lean/Elab/Tactic/Do/VCGen.lean:455–456`
   emits an unconditional experimental warning unless `mvcgen.warning` is
   `false`, tripping `-DwarningAsError=true`) and adding `` `spec `` to
   `TrustedBoundary.allowedAttributeNames`. For `Std.Data` containers, bundled
   `Std.TreeMap`, `Std.HashMap`, `Std.ExtTreeMap`, and `Std.ExtHashMap` are
   rejected by the kernel inside recursive inductive types (`(kernel)
   application type mismatch: DTreeMap.Internal.Impl.WF inner`) because the
   value type family occurs in a negative position inside
   `Impl.WF.constModify`; unbundled `Std.TreeMap.Raw` and `Std.HashMap.Raw`
   succeed inside recursive inductives. Finally, `Std.TreeMap` and
   `Std.TreeMap.Raw` reduce in the kernel (`decide +kernel` / `rfl`) with zero
   axioms (`[]` on `Std.TreeMap.Raw`), whereas `Std.HashMap` and
   `Std.HashMap.Raw` cannot reduce in the kernel even on an empty map.

## Applicability

These findings apply to the combination and interaction of the examined
subjects in `REPORT.json`:

| Subject | Repository / Path | Revision / Digest | Role in Investigation |
| :--- | :--- | :--- | :--- |
| Lean 4 toolchain, core libraries, and tactics | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Primary source and execution environment for `Init.*`, `Std.Sat`, `Std.Tactic.BVDecide`, `Init.Omega`, `Init.Grind`, `Std.Do`, and `Std.Data`. |
| Anneal boundary auditor and foundation lock | `joshlf/anneal` (`trusted/audit/`, `trusted/lean/foundation-lock.json`) | `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` | Trust-boundary policy (`TrustedBoundary.lean`), `.olean` replay checker, compiler flags (`trusted/audit/src/lib.rs`), and 51-module `Init.*` lock. |
| `support/ProbeBVDecide.lean` | Package support file | `3d2465d2cf40724556c1f14bc7f9a3375d277148d8de3f23822930341053a6f8` | Verified Lean `v4.34.1` implementation of `KernelLRAT`, `KernelBVDecide`, and `bv_decide_kernel` contrasted against standard `bv_decide`. |
| `support/ProbeGrindOmega.lean` | Package support file | `abeb3548f70a9d683b791638c6b084c050e9e780ae99d4fcacf8ec0e72c4d114` | Verified `prelude`-mode Lean `v4.34.1` probe exercising `omega` and `grind` (`lia`, `ring`, `ToInt`) under `TrustedBoundary.lean` Phase 1 and Phase 2 rules. |
| `support/ProbeStdDoData.lean` | Package support file | `1cdc3c347bde6d4f2a091b7ed374085e60b4788324998cf33cc60782ffd5bf5d` | Verified Lean `v4.34.1` probe for `Std.Do` (`mvcgen`, `@[spec]`, `StateM`, `EStateM`) and `Std.Data` (`TreeMap`, `TreeMap.Raw`, `ExtTreeMap`, `HashMap.Raw`). |
| `support/DiagnoseReduce.lean` | Package support file | `ab8544539c4a5ed319edfbed888262376cbcb6445f01d8a1f2b9b54ae2f46c42` | Verified `#guard_msgs` diagnostic isolating all 7 `verifyBVExpr` / `Std.HashMap` kernel-reduction blockers and checking `omega`/`grind` axiom footprints. |

Scope qualifications:

- All compilation timings, `#print axioms` footprints, and `#guard_msgs`
  diagnostics were observed with `leanprover/lean4:v4.34.1` (`commit
  5045d0056413266e57c625dcd7c365b10e377c52`) on `x86_64-unknown-linux-gnu`
  using single-threaded execution (`-j1`) and a 1,024 MB memory cap (`-M1024`).
- The module-closure counts (51, 76, 172, 247, 92, and 460) and duplicate
  realized `.eq_def` constants reflect the exact `.olean` import graph of Lean
  `v4.34.1`'s `Init` and `Std` libraries.

## Findings

### 1. Upstream `bv_decide` Native Axiom Injection and the Seven Kernel-Reduction Blockers in `verifyBVExpr`

`Basis: source + execution + derived`

#### 1.1 How `bv_decide` Injects Per-Theorem `_native` Axioms in Lean `v4.34.1`

In Lean `v4.34.1`, the legacy `Lean.ofReduceBool` theorem and
`Lean.trustCompiler` axiom (`src/lean/Init/Core.lean:2337–2409`) are marked
`@[deprecated]`. Instead, `bv_decide` splits its proof pipeline into two stages:

1. **Kernel-Checked Preprocessing and Reification
   (`Normalize.bvNormalize` and `Reflect.reflectBV`):**
   - `Lean/Elab/Tactic/BVDecide.lean:51–63` (`bvNormalize`) applies
     `false_or_by_contra` and normalizes `BitVec`, `UInt8`..`UInt64`, `USize`,
     `Int8`..`Int64`, `ISize`, and `Bool` hypotheses using kernel-checked
     `bv_normalize` and `seval` `simp` theorems.
   - `Lean/Meta/Tactic/BVDecide/Reflect/SatAtBVLogical.lean:32–80`
     (`Reflect.reflectBV` and `SatAtBVLogical.proveFalse`) reifies the
     normalized hypotheses into a single syntactic expression `bvExpr :
     Std.Tactic.BVDecide.BVLogicalExpr`
     (`src/lean/Std/Tactic/BVDecide/Bitblast/BVExpr/Basic.lean:166–224`) paired
     with a kernel proof term `exprSat : bvExpr.SatAssignment atomsAssignment`.
     `SatAtBVLogical.proveFalse` constructs a closure `proveFalse (unsat :
     Expr) : MetaM Expr` that takes any proof term `unsat : bvExpr.Unsat` and
     applies it to `atomsAssignment` and `exprSat` to produce a kernel-checked
     proof of `False` using only `{propext, Classical.choice, Quot.sound}`.

2. **Native Evaluation and Axiom Injection (`LratCert.toReflectionProof`):**
   - `Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26–44`
     (`LratCert.toReflectionProof`) defines two auxiliary declarations—one for
     the reflected `BVLogicalExpr` and one for the raw LRAT certificate string
     (`LratCert`)—and invokes `Lean.Meta.nativeEqTrue \`bv_decide`
     (`src/lean/Lean/Meta/Native.lean:37–87`) on the proposition:
     ```lean
     Std.Tactic.BVDecide.Reflect.verifyBVExpr <exprDef> (loadLRATProof <certDef>) = true
     ```
   - `Lean.Meta.nativeEqTrue` (`src/lean/Lean/Meta/Native.lean:64–86`) compiles
     an auxiliary boolean thunk, evaluates it in native machine code via
     `unsafe evalConst Bool auxDeclName`, and calls `addDecl (.axiomDecl ...)`
     to inject a fresh per-theorem axiom named
     `<declName>._native.bv_decide.ax_1_5` into the kernel environment.
   - Applying `Std.Tactic.BVDecide.Reflect.verifyBVExpr_bv_unsat`
     (`src/lean/Std/Tactic/BVDecide/Reflect.lean:87–95`) to that native axiom
     yields `bvExpr.Unsat`.

As verified in Section 1 of
[`support/ProbeBVDecide.lean`](support/ProbeBVDecide.lean)
(lines 31–62), every theorem proved by standard `bv_decide` depends on a
theorem-specific `_native.bv_decide.ax_1_5` axiom (for example,
`align_mask_bv64._native.bv_decide.ax_1_5`). In Anneal's audit pipeline
(`trusted/audit/TrustedBoundary.lean`), any such theorem is rejected at Phase 1
if `native_decide` or `decide +native` syntax appears (lines 318–329) and at
Phase 2 (`verifyAndCollectLocals`, lines 857–858, and `closure` axiom allowlist
check against `{Classical.choice, Quot.sound, propext}`, lines 568–570) because
the generated `.olean` contains an unauthorized axiom declaration and depends
on it in its transitive constant closure.

#### 1.2 The Seven Kernel-Reduction Blockers in Upstream `verifyBVExpr`

If `Lean.Meta.nativeEqTrue` in `LratCert.toReflectionProof` is replaced by
`mkEqRefl (toExpr true)` (or `eagerReduce (Eq.refl true)`), the Lean 4 kernel
attempts to reduce `verifyBVExpr bv (loadLRATProof cert)` via weak-head normal
form (`whnf`) and fails. Direct source inspection of `verifyBVExpr`
(`src/lean/Std/Tactic/BVDecide/Reflect.lean:60–65`) and `#guard_msgs` execution
in [`support/DiagnoseReduce.lean`](support/DiagnoseReduce.lean) (lines 29–139)
identify seven independent kernel-reduction blockers:

| # | Upstream Symbol and Source Coordinates (`leanprover/lean4` at `5045d00564`) | Reduction Blocker Mechanism | Diagnostic Witness in `support/DiagnoseReduce.lean` |
| :--- | :--- | :--- | :--- |
| 1 | `LRAT.parseLRATProof`, `LRAT.Parser.parseActions` (`src/lean/Std/Tactic/BVDecide/LRAT/Parser.lean:132, 201, 213, 279, 301`) & `String.toUTF8` (`src/lean/Init/Data/String/Bootstrap.lean:51`) | `Text.parseActions`, `Binary.parseLit`, `manyTillZero`, and `manyTillNegOrZero` are declared as `partial def`, which compile to `opaque` constants in the kernel with no equational reduction rules; `String.toUTF8` is `@[extern "lean_string_to_utf8"] opaque`. | `blocker1_lrat_parser_cannot_reduce_in_kernel` (lines 48–52) |
| 2 | `Std.DHashMap.Internal.mkIdx` (`src/lean/Std/Data/DHashMap/Internal/Index.lean:51–53`), `USize` (`src/lean/Init/Prelude.lean:2305`), & `mixHash` (`src/lean/Init/Prelude.lean:4680`) | `mkIdx` is marked `@[irreducible] def` and computes bucket indices via `USize.ofNat (hash a).toNat`, which depends on `opaque System.Platform.getNumBits : Unit → Nat` and `opaque mixHash : UInt64 → UInt64 → UInt64`. Even `(∅ : Std.HashMap Nat Nat)[0]?` cannot reduce in the kernel. | `blocker2_hashmap_empty_lookup_blocks_rfl` (lines 68–71) vs. `treeMap_empty_lookup_reduces_in_kernel` (lines 58–60) |
| 3 | `BVExpr.bitblast.go` (`src/lean/Std/Tactic/BVDecide/Bitblast/BVExpr/Circuit/Impl/Expr.lean:47–48, 87, 118`) | Threads a `BVExpr.Cache` backed by `Std.DHashMap` keyed by `BVExprWithHash` (whose hash invokes `opaque mixHash`), halting reduction on the first `BVExpr` cache lookup. | `blocker3_and_4_bitblast_aig_cache_blocks_rfl` (lines 85–88) |
| 4 | `Std.Sat.AIG.Cache` (`src/lean/Std/Sat/AIG/Basic.lean:139–159, 241–246`) | `Cache.empty`, `Cache.noUpdate`, `Cache.insert`, and `Cache.get?` are marked `@[irreducible]` and wrap `Std.HashMap (Decl α) (Nat × ...)`. Every smart gate constructor (`mkGateCached`, `mkAtomCached`, `mkConstCached`) probes `Cache.get?`. (Only `.const false` avoids probing the map because it returns index 0 immediately: `constFalse_aig_size_reduces`, lines 35–37.) | `blocker3_and_4_bitblast_aig_cache_blocks_rfl` (lines 85–88) |
| 5 | `Std.Sat.AIG.denote.go` (`src/lean/Std/Sat/AIG/Basic.lean:480–491`) | Defined by well-founded recursion with the explicit source comment `termination_by (x, 0) -- Don't allow reduction, we have large concrete gate entries`, blocking definitional unfolding of `⟦aig, assign⟧`. | `blocker5_aig_denote_wf_blocks_rfl` (lines 99–102) |
| 6 | `AIG.Entrypoint.relabelNat` (`src/lean/Std/Sat/AIG/RelabelNat.lean:162–179`) & `CNF.relabelFin` (`src/lean/Std/Sat/CNF/RelabelFin.lean:115`) | `relabelNat` inserts atoms into `Std.HashMap α Nat` (blocking reduction even on `constFalseExpr.bitblast.relabelNat`); `CNF.relabelFin` branches on an `@[no_expose] instance : Decidable (∃ v, VarMem v f)`. | `blocker6_relabelNat_blocks_rfl` (lines 114–117) |
| 7 | `LRAT.Internal.DefaultClause.ofArray.folder` (`src/lean/Std/Tactic/BVDecide/LRAT/Internal/Clause.lean:141–168`) | Marked `@[irreducible]` and folds over clause literals using `Std.HashMap (PosFin n) Bool` to deduplicate literals and detect tautologies during `LRAT.check`. | `blocker7_defaultClause_ofArray_blocks_rfl` (lines 129–134) |

---

### 2. Verified Zero-`_native`-Axiom Replacements: `KernelLRAT` and `KernelBVDecide` (`bv_decide_kernel`)

`Basis: source + execution + derived`

Because `Normalize.bvNormalize` and `Reflect.reflectBV` already reduce goal
obligations to proving `bvExpr.Unsat` (`∀ assign, bvExpr.eval assign = false`)
purely within the kernel, eliminating `bv_decide`'s native axiom requires only
a total, `Std.HashMap`-free, `@[irreducible]`-free boolean decision procedure
that reduces in the kernel (`decide +kernel` or `eagerReduce (Eq.refl true)`)
and has a mechanized soundness theorem concluding `.Unsat`.

#### 2.1 `KernelLRAT`: Total List-Based RUP Certificate Checker

Section 2 of [`support/ProbeBVDecide.lean`](support/ProbeBVDecide.lean) (lines
78–296) mechanizes `KernelLRAT`, a self-contained LRAT/RUP checker over
`Formula := List Clause` (`Clause := List (Nat × Bool)`):

- **Total Structural Operations:** `isFalsified`, `reduceClause`, `getClause`,
  `rupPropagate`, `negateClause`, `checkRupStep`, and `checkCert` (lines
  105–235) are defined by structural recursion on `List` and `Nat` without
  `Std.HashMap`, `USize`, `partial def`, or `@[irreducible]` barriers.
- **Soundness Theorem (`KernelLRAT.checkCert_sound`, lines 246–273):**
  Proves `checkCert F cert = true → F.Unsat` by induction on `cert` using
  `evalLit_false_of_isFalsified`, `evalClause_reduceClause`,
  `evalClause_of_getClause`, `rupPropagate_sound`, `consistent_negateClause`,
  `evalClause_of_checkRupStep`, and `evalFormula_append_singleton`.
- **In-Kernel Execution (`KernelLRAT.sampleCNF_unsat`, lines 291–294):**
  Proves unsatisfiability of a 6-clause 2-bit adder carry-out formula via
  `checkCert_sound sampleUnsatCNF sampleLRATCert (by decide +kernel)` in
  **6.21 ms** with axiom footprint `[propext, Quot.sound]`.

#### 2.2 `KernelBVDecide`: Linear-Size Propagate-Generate ROBDD Bitblaster (`bv_decide_kernel`)

Section 3 of [`support/ProbeBVDecide.lean`](support/ProbeBVDecide.lean) (lines
307–1006) mechanizes `KernelBVDecide` and the `bv_decide_kernel` tactic over
`Std.Tactic.BVDecide.BVLogicalExpr`. Making 64-bit `BitVec` and `UInt64`
arithmetic reduce quickly inside Lean 4's kernel `whnf` reducer without a
`Std.HashMap` DAG cache requires three algorithmic choices:

1. **Nested Structural Recursion (`BDD.rec`) Instead of Well-Founded
   Recursion:**
   Binary BDD operations (`bddAnd`, `bddOr`, `bddXor` at lines 332–382) are
   factored into an outer structural recursion on `a : BDD` and a higher-order
   inner helper (`bddAndNode`, `bddOrNode`, `bddXorNode`) that recurses
   structurally on `b : BDD` while receiving curried recursive closures
   (`bddAnd la`, `bddAnd ha`). Consequently, the Lean kernel reduces `bddAnd`,
   `bddOr`, and `bddXor` directly via `BDD.rec` with zero `WellFounded.fix` or
   lexicographic pair-packing overhead.
2. **Interleaved LSB-to-MSB Variable Ordering (`BVar.gt`, lines 311–318):**
   Decision variables `BVar := { bit : Nat, var : Nat }` are ordered first by
   bit position `bit` (from 0 up to $w - 1$) and then by variable index `var`.
   Adding or comparing two 64-bit bitvectors processes bit 0 of all operands,
   then bit 1, up to bit 63, avoiding the $2^{64}$ cross-bit path explosion of
   concatenated variable orderings.
3. **Propagate-Generate Basis `(x_i, x_i ^^ y_i)` for Ripple-Carry Addition
   (`bddVar` and `assignToBDDEnv`, lines 388–394, 540–558):**
   Without hash-consing (`Std.HashMap`), a standard ROBDD represents a tree
   unfolding of the reduced DAG. Under the naive basis `(x_i, y_i)`, the
   carry-out `c_{i+1}` of ripple-carry addition is referenced on both branches
   of `x_i` (`x_i = 0, y_i = 1` and `x_i = 1, y_i = 0`), doubling the uncached
   tree size at every bit position ($O(2^w)$). By encoding variable 1's $i$-th
   bit in `bddVar` as `x_i ^^ p_i` (where `p_i` is the propagate variable
   `var_0[i] ^^ var_1[i]`, inverted by `assignToBDDEnv` at lines 540–544), the
   ripple-carry sum bit `(x_i ^^ (x_i ^^ p_i)) ^^ c_i` simplifies by canonical
   ROBDD reduction (`mkNode`) to `p_i ^^ c_i`, and the carry-out
   `bddAtLeastTwo x_i (x_i ^^ p_i) c_i` simplifies to:
   $$\text{carry}_{i+1} = \text{ite}(p_i,\, c_i,\, x_i)$$
   Because `c_i` appears in only the `high` branch of `p_i` (and the `low`
   branch is the 1-node variable `x_i`), the uncached tree size of the carry
   ROBDD at bit $w$ is **strictly linear** ($2w + 1$, or **131 nodes** at bit
   64) without any hash table.

#### 2.3 `module` + `public meta import` Memory Isolation Under `-M1024`

In Lean `v4.34.1`, writing an unadorned `import Lean.Elab.Tactic.BVDecide` in a
file without the `module` header loads the entire `Lean.*` compiler and
elaborator `.olean` graph into the non-meta kernel environment (~950 MB of
resident heap), causing `-M1024` to fail with `(kernel) excessive memory
consumption detected` on the very first theorem. Declaring `module` at the top
of [`support/ProbeBVDecide.lean`](support/ProbeBVDecide.lean) (lines 9–15) and
importing the tactic elaborator via:

```lean
module

public import Std.Tactic.BVDecide
public meta import Lean.Elab.Tactic.BVDecide
public meta import Lean.Meta.Tactic.Grind.Main

@[expose] public section
```

isolates `Lean.Elab.Tactic.BVDecide` and `Lean.Meta.Tactic.Grind.Main` to the
`meta` phase (`meta def kernelBddProver` and `meta def bvDecideKernel`, lines
921–952), allowing all standard `bv_decide` and `bv_decide_kernel` 64-bit
proofs to compile cleanly under `lean -j1 -M1024`.

#### 2.4 Empirical Comparison: Standard `bv_decide` vs. `bv_decide_kernel`

Measured on `leanprover/lean4:v4.34.1` (`-j1 -M1024 -Dprofiler=true`):

| Obligation in `support/ProbeBVDecide.lean` | Width | Standard `bv_decide` Axiom Footprint | `bv_decide_kernel` Axiom Footprint | `bv_decide_kernel` Kernel Time |
| :--- | :--- | :--- | :--- | :--- |
| `KernelLRAT.sampleCNF_unsat` | CNF (6 clauses) | N/A | `[propext, Quot.sound]` | **6.21 ms** |
| `checked_add_no_overflow_bv8_kernel` | 8-bit | `... + _native.bv_decide.ax_1_5` | `[propext, Classical.choice, Quot.sound]` | **114 ms** |
| `checked_add_no_overflow_bv16_kernel` | 16-bit | `... + _native.bv_decide.ax_1_5` | `[propext, Classical.choice, Quot.sound]` | **274 ms** |
| `checked_add_no_overflow_bv32_kernel` | 32-bit | `... + _native.bv_decide.ax_1_5` | `[propext, Classical.choice, Quot.sound]` | **616 ms** |
| `bitwise_and_le_mask_bv64_kernel` | 64-bit | `[propext, Classical.choice, Quot.sound, bitwise_and_le_mask_bv64._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **456 ms** |
| `align_mask_bv64_kernel` | 64-bit | `[propext, Classical.choice, Quot.sound, align_mask_bv64._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **642 ms** |
| `checked_add_no_overflow_bv64_kernel` | 64-bit | `[propext, Classical.choice, Quot.sound, checked_add_no_overflow_bv64._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **1.59 s** |
| `uint64_align_roundup_kernel` | 64-bit (`UInt64`) | `[propext, Classical.choice, Quot.sound, uint64_align_roundup._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **3.02 s** |

---

### 3. `omega` and `grind` Under `prelude` and `TrustedBoundary.lean`

`Basis: source + execution + derived`

#### 3.1 Proof-Term Construction and Axiom Footprints of `omega` and `grind`

1. **`omega` (`src/lean/Init/Omega.lean`,
   `src/lean/Lean/Elab/Tactic/Omega/Core.lean`):**
   `Init/Omega.lean:9–15` exports `Init.Omega.LinearCombo`,
   `Init.Omega.IntList`, `Init.Omega.Int`, `Init.Omega.Constraint`, and
   `Init.Omega.Logic`. During elaboration
   (`Lean/Elab/Tactic/Omega/Core.lean:107, 111, 224`), `omega` constructs
   explicit `Int`/`Nat` linear-combination witness terms and discharges bounded
   decidable side-conditions using `mkDecideProof` (kernel `decide`) and
   `mkEqReflWithExpectedType` (kernel `Eq.refl`). It never calls
   `Lean.Meta.nativeEqTrue` or `Lean.ofReduceBool`. Pure `Nat` linear bounds
   proofs (`mir_slice_subslice_bounds_omega` in `ProbeGrindOmega.lean:30–35`
   and `omega_bounds_check` in `DiagnoseReduce.lean:146–154`) depend only on
   `[propext, Quot.sound]` (not even `Classical.choice`).
2. **`grind` (`src/lean/Init/Grind.lean`, `src/lean/Init/GrindInstances.lean`,
   `src/lean/Lean/Meta/Tactic/Grind/`):**
   `Init/Grind.lean:9–31` exports 22 submodules (`Norm`, `Tactics`, `Lemmas`,
   `Cases`, `Propagator`, `Util`, `Offset`, `AC`, `ToInt`, `ToIntLemmas`,
   `Ring`, `Module`, `Ordered`, `Ext`, `Injective`, `Order`, `Config`, `Lint`,
   `Annotated`, `PP`, `Homo`, `FieldNormNum`), while
   `Init/GrindInstances.lean:9–12` exports the typeclass instances connecting
   `Int`, `Nat`, `Fin`, `BitVec`, `UInt8`..`UInt64`, `USize`, `SInt`, and `Rat`
   to `Grind.ToInt`, `Grind.CommRing`, and `Grind.NatModule`. `grind`'s
   arithmetic procedures (`cutsat` / `lia`, `ring`, `linarith`) construct
   explicit polynomial and Cooper/Cutsat certificate terms and discharge
   boolean reflection steps via `eagerReflBoolTrue` =
   `mkApp2 (mkConst ``eagerReduce [0]) (mkConst ``Bool) (mkConst ``Bool.true)`
   (`src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean:240–300`). Every
   theorem proved by `grind` in
   [`support/ProbeGrindOmega.lean`](support/ProbeGrindOmega.lean) and
   [`support/DiagnoseReduce.lean`](support/DiagnoseReduce.lean) depends only on
   `[propext, Classical.choice, Quot.sound]`.

#### 3.2 `prelude` Import Closures and the Private `Init.Data.Int.OfNat` Trap

Anneal's `trusted/lean/` and `theory/` modules compile with an explicit
`prelude` header (`TrustedBoundary.lean:251–273`), and
`trusted/lean/foundation-lock.json` currently locks **51** `Init.*` modules.
Although `Init.Grind.Attr`, `Init.Grind.Interactive`, and `Init.Grind.Tactics`
are present in that 51-module lock (transitively imported via
`Init.Data.Nat.Div.Basic` → `Init.WFTactics` → `Init.WF` →
`Init.Grind.Tactics`), they provide only syntax and attribute declarations.

In a `prelude` file, enabling `grind` over `Nat`, `Int`, and fixed-width
machine integers (`UInt64`, `USize`, `BitVec`) requires four explicit imports
(`support/ProbeGrindOmega.lean:9–13`):

```lean
prelude
import Init.Omega
import Init.Grind
import Init.GrindInstances
import Init.Data.Int.OfNat
```

Why must `Init.Data.Int.OfNat` and `Init.GrindInstances` be imported explicitly
alongside `Init.Grind` in a `prelude` file?

- **Private Import of `Init.Data.Int.OfNat` Under Lean 4's `module` System:**
  The files in `src/lean/Init/Grind/*.lean` use Lean `v4.34.1`'s `module`
  header and import `Init.Data.Int.OfNat` as a private `import` rather than a
  `public import`. However, `grind`'s `Nat` Cutsat proof generator
  (`src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Nat.lean:9, 41`) constructs
  kernel proof terms that directly reference `Nat.ToInt.of_le` (defined in
  `src/lean/Init/Data/Int/OfNat.lean:388`). Without `import
  Init.Data.Int.OfNat` in a `prelude` file, `grind` fails on `Nat` linear
  arithmetic with `(kernel) unknown constant 'Nat.ToInt.of_le'`.
- **Separation of `Init.GrindInstances`:**
  `Init.Grind` defines the `Grind.ToInt` and `Grind.CommRing` classes, but the
  instances for `UInt64`, `USize`, `BitVec`, and `Int` live in
  `Init.GrindInstances` (`Init.GrindInstances.ToInt`,
  `Init.GrindInstances.Ring`, `Init.GrindInstances.Nat`).

Transitive `Init.*` module closures relative to
`trusted/lean/foundation-lock.json`:

| Tactic Capability in a `prelude` File | Minimal Explicit `import` Header | Transitive `Init.*` Closure | Modules Already in `foundation-lock.json` | Additional `Init.*` Modules Required |
| :--- | :--- | :--- | :--- | :--- |
| Current `foundation-lock.json` | (51 locked modules) | **51** | 51 | **0** |
| `omega` (`Nat` and `Int` linear integer arithmetic) | `import Init.Omega` | **76** | 51 | **25** (`Init.ByCases`, `Init.Classical`, `Init.Data.BEq`, `Init.Data.Bool`, `Init.Data.Int.DivMod.Basic`, `Init.Data.Int.DivMod.Bootstrap`, `Init.Data.Int.Lemmas`, `Init.Data.Int.Order`, `Init.Data.Nat.Dvd`, `Init.Data.Nat.Gcd`, `Init.Data.Nat.MinMax`, `Init.Data.Nat.Order`, `Init.Data.Order.Classes`, `Init.Data.Order.Factories`, `Init.Data.Order.Lemmas`, `Init.Data.ToString.Macro`, `Init.Omega`, `Init.Omega.Coeffs`, `Init.Omega.Constraint`, `Init.Omega.Int`, `Init.Omega.IntList`, `Init.Omega.LinearCombo`, `Init.Omega.Logic`, `Init.PropLemmas`, `Init.RCases`) |
| Minimal `grind` (`grind -lia -ring -linarith`: congruence closure + E-matching) | `import Init.Grind.Lemmas`<br>`import Init.Grind.Norm`<br>`import Init.Grind.Tactics` | **172** | 51 | **121** |
| Full `grind` + `omega` (`lia`, `ring`, `linarith`, `ToInt` over `Nat`, `Int`, `UInt64`, `USize`, `BitVec`) | `import Init.Omega`<br>`import Init.Grind`<br>`import Init.GrindInstances`<br>`import Init.Data.Int.OfNat` | **247** | 51 | **196** |

#### 3.3 Duplicate Realized `.eq_def` Constants Across `Init.*` vs. `TrustedBoundary.lean:851`

All six theorems in
[`support/ProbeGrindOmega.lean`](support/ProbeGrindOmega.lean)
pass `TrustedBoundary.lean` Phase 1 (`preflight`) with `"ok": true` and pass
`baseEnv.toKernelEnv.replay` across all 12 compiled declarations. However, when
`foundation-lock.json` is expanded to either the 76-module `Init.Omega` closure
or the 247-module `Init.Grind` closure, `TrustedBoundary.verifyAndCollectLocals`
(`trusted/audit/TrustedBoundary.lean:850–852`) fails at Phase 2 (`audit`) with:

```json
{"ok": false, "message": "policy:stored declaration differs from inventory List.drop.eq_def", "category": "policy"}
```

Root cause in Lean `v4.34.1`'s `module` system:

- Equation theorems (`.eq_def`) for recursive functions are realized lazily on
  demand (`realizeConst`) inside whichever module unfolds the definition.
- Across the 247 `Init.*` modules in `Init.Grind`'s transitive closure, five
  equation theorems are realized independently in more than one `Init.*`
  module:
  1. `List.drop.eq_def`: realized in both `Init.Data.Array.GetLit` (present in
     the 51-module `foundation-lock.json`) and `Init.Data.List.TakeDrop`
     (imported by `Init.Omega` and `Init.Grind`).
  2. `List.takeWhile.eq_def`: realized in `Init.Data.List.TakeDrop` and
     `Init.Data.List.Impl`.
  3. `List.take.eq_def`: realized in `Init.Data.List.TakeDrop` and
     `Init.Data.List.Impl`.
  4. `List.eraseIdx.eq_def`: realized in `Init.Data.List.Impl`,
     `Init.Data.List.Erase`, and `Init.Data.List.Nat.Basic`.
  5. `List.find?.eq_def`: realized in `Init.Data.List.Impl` and
     `Init.Data.List.ToArray`.
- For all six duplicate occurrences across those five constants,
  `stored.type == ci.type` holds (`true`), so both modules prove the identical
  theorem statement (and are equal in the logic by proof irrelevance), but
  `stored.value? true == ci.value? true` is `false` because `env.checked`
  retains only one module's realized proof term.
- `TrustedBoundary.lean:845–846` already exempts `foundation` modules from the
  single-origin check (`if foundation.contains m.module then unless
  foundation.contains orig do ...`) for this exact reason, but line 851
  (`unless stored.type == ci.type && stored.value? true == ci.value? true`)
  runs unconditionally. Scoping the value-equality check at line 851 to
  `(!foundation.contains m.module || orig == m.module)` while preserving
  `stored.type == ci.type` for every module resolves the collision.

---

### 4. `Std.Do` (`SPred`, `WP`, `Triple`, and `mvcgen`) in Lean `v4.34.1`

`Basis: source + execution + derived`

#### 4.1 Architecture of `Std.Do` and `mvcgen`

`Std.Do` (`src/lean/Std/Do.lean`) and `Std.Tactic.Do`
(`src/lean/Std/Tactic/Do.lean`) implement a foundational weakest-precondition
program logic for monadic Lean programs in four layers:

1. **State-Indexed Predicates (`SVal` and `SPred`):**
   - `abbrev SVal (σs : List (Type u)) (α : Type u) : Type u`
     (`src/lean/Std/Do/SPred/SVal.lean:30–32`) curries a state-type list:
     `SVal [] α = α` and `SVal (σ :: σs) α = σ → SVal σs α`.
   - `abbrev SPred (σs : List (Type u)) : Type u := SVal σs (ULift Prop)`
     (`src/lean/Std/Do/SPred/SPred.lean:34`) equips state-indexed propositions
     with pointwise logical connectives and entailment `P ⊢ₛ Q`
     (`SPred.entails`, lines 67–69).
2. **Effect Shapes and Multi-Barrel Postconditions (`PostShape` and
   `PostCond`):**
   - `inductive PostShape : Type (u + 1)`
     (`src/lean/Std/Do/PostCond.lean:54–66`) encodes monad transformer stacks
     using `.pure`, `.arg (σ : Type u) ps` (one state layer), and `.except
     (ε : Type u) ps` (one exception layer).
   - `Assertion` (`src/lean/Std/Do/PostCond.lean:93–94`) is defined as
     `abbrev Assertion (ps : PostShape.{u}) : Type u :=`
     `SPred (PostShape.args ps)`.
   - `PostCond` (`src/lean/Std/Do/PostCond.lean:255`) is defined as
     `def PostCond (α : Type u) (ps : PostShape.{u}) : Type u :=`
     `(α → Assertion ps) × ExceptConds ps`,
     pairing the normal-return assertion barrel with one assertion barrel per
     `.except ε` layer.
3. **Conjunctive Predicate Transformers and `WP` Instances (`PredTrans`, `WP`,
   `WPMonad`):**
   - `structure PredTrans (ps : PostShape) (α : Type u)`
     (`src/lean/Std/Do/PredTrans.lean:63–70`) bundles `trans : PostCond α ps →
     Assertion ps` with conjunctivity (`conjunctiveRaw`), from which
     monotonicity (`PredTrans.mono`, lines 88–89) is derived.
   - `class WP (m : Type u → Type v) (ps : outParam PostShape.{u})`
     (`src/lean/Std/Do/WP/Basic.lean:54–56`) and `class WPMonad`
     (`src/lean/Std/Do/WP/Monad.lean:36–41`) provide verified monad-morphism
     instances for `Id`, `StateT` / `StateM`, `ReaderT` / `ReaderM`, `ExceptT` /
     `Except`, `OptionT` / `Option`, and `EStateM`
     (`Std/Do/WP/Basic.lean:77–112`, `Std/Do/WP/Monad.lean:53–106`).
4. **Hoare Triples and Verification Condition Generation (`Triple` and
   `mvcgen`):**
   - `Triple` (`src/lean/Std/Do/Triple/Basic.lean:37–38`), denoted `⦃P⦄ x ⦃Q⦄`,
     is defined as `def Triple [WP m ps] (x : m α) (P : Assertion ps)
     (Q : PostCond α ps) : Prop := P ⊢ₛ wp⟦x⟧ Q`.
   - `mvcgen` (`src/lean/Lean/Elab/Tactic/Do/VCGen.lean:40–150, 453–489`)
     symbolically steps through `wp⟦e⟧ Q` by unfolding `let`-bindings,
     splitting `if`/`dite`/`match` branches, applying `@[spec]` theorems via
     `Triple.bind`, and running `mleave`
     (`src/lean/Std/Tactic/Do/Syntax.lean:177–221`), which simplifies `SPred`
     state projections down to pure propositions via `simp only` so `omega` or
     `grind` can close the remaining verification conditions.

#### 4.2 Axiom Footprint and Audit Integration Requirements for `Std.Do`

Section 1 of [`support/ProbeStdDoData.lean`](support/ProbeStdDoData.lean)
(lines 44–109) verifies three representative monadic specifications—single-step
bounded stack allocation (`tryBumpAlloc_spec` via `mvcgen [tryBumpAlloc] <;>
grind`), compositional two-step allocation using `@[spec]` (`allocPair_spec`
via `mvcgen [allocPair] <;> omega`), and exception-raising state transitions in
`EStateM String FrameState` (`checkedStep_spec` via `mvcgen [checkedStep] <;>
omega`). All three theorems depend only on `[propext, Classical.choice,
Quot.sound]`.

Integrating `Std.Do` and `mvcgen` under Anneal's audit boundary requires
accounting for three concrete constraints:

1. **Unconditional Experimental Warning in `mvcgen`
   (`src/lean/Lean/Elab/Tactic/Do/VCGen.lean:455–456`):**
   `elabMVCGen` executes:
   ```lean
   if mvcgen.warning.get (← getOptions) then
     logWarningAt tk "The `mvcgen` tactic is experimental and still under development. Avoid using it in production projects"
   ```
   Because `trusted/audit/src/lib.rs:1233` invokes `lean` with
   `-DwarningAsError=true` and `TrustedBoundary.lean:316` forbids `set_option`
   commands inside audited source files, `compile_lean_module` in
   `trusted/audit/src/lib.rs` must pass `-Dmvcgen.warning=false` on the command
   line whenever `mvcgen` is permitted.
2. **`@[spec]` Attribute Allowlisting
   (`trusted/audit/TrustedBoundary.lean:201`):**
   `TrustedBoundary.allowedAttributeNames` currently permits only `simp`,
   `ext`, `inline`, `always_inline`, `noinline`, `macro_inline`, `reducible`,
   `semireducible`, `irreducible`, `instance`, `default_instance`, `scoped`,
   and `local`. Using `@[spec]` in audited modules requires adding `` `spec ``
   to `allowedAttributeNames`.
3. **Import-Closure Granularity (`Std.Do.Triple.Basic` vs. `Std.Do`):**
   Importing `Std.Do.Triple.Basic` + `Std.Do.WP.Monad` directly pulls in **92**
   modules (18 in `Std.*` and 74 in `Init.*`), whereas importing top-level
   `Std.Do` pulls in `Std.Do.Triple.SpecLemmas` (**460** modules total, due to
   `Std.Data.Iterators` and slice loop specifications).

---

### 5. `Std.Data` Containers: Recursive Inductives, Kernel Reduction, and Extensionality

`Basis: source + execution + derived`

#### 5.1 Three-Tier Container Matrix in Lean `v4.34.1`

Lean `v4.34.1`'s `Std.Data` provides three tiers for both hash maps (`HashMap`
/ `DHashMap`) and size-balanced binary search trees (`TreeMap` / `DTreeMap`,
with balance parameters $\delta = 3, \text{ratio} = 2$ at
`src/lean/Std/Data/DTreeMap/Internal/Def.lean:36–41`):

| Tier | Tree-Based (`Ord` / `cmp`) | Hash-Based (`BEq` + `Hashable`) | Internal Representation & Well-Formedness | Nestable in Recursive Inductives? | Reduces in Kernel (`rfl` / `decide +kernel`)? | Extensional Equality (`m₁ = m₂ ↔ ∀ k, m₁[k]? = m₂[k]?`)? | Transitive Module Closure |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Unbundled (`.Raw`)** | `Std.TreeMap.Raw α β cmp` (`Std/Data/TreeMap/Raw/Basic.lean:65`) | `Std.HashMap.Raw α β` (`Std/Data/HashMap/Raw.lean:61`) | Pure inductive/struct data (`Impl α β` or `size × Array AssocList`); separate `Raw.WF` predicate; lookup lemmas take `(h : m.WF)`. | **Yes** (`GoodRecValue`, `ProbeStdDoData.lean:146–149`) | **`TreeMap.Raw`: Yes (`[]` axioms)**<br>`HashMap.Raw`: **No** | No (structural equality on tree/buckets) | `TreeMap.Raw.Basic`: **169** (11 `Std.*`)<br>`TreeMap.Raw` + `Lemmas`: **259** (44 `Std.*`)<br>`HashMap.Raw`: **168** (8 `Std.*`) |
| **Bundled** | `Std.TreeMap α β cmp` (`Std/Data/TreeMap/Basic.lean:67`) | `Std.HashMap α β` (`Std/Data/HashMap/Basic.lean:64`) | `{ inner : Raw, wf : inner.WF }`; lookup lemmas require no `WF` hypothesis. | **No** (`BadRecValue`, `ProbeStdDoData.lean:135–138`) | **`TreeMap`: Yes**<br>`HashMap`: **No** | No (`Equiv` relation `~m` instead of `=`) | `TreeMap` + `Lemmas`: **262** (47 `Std.*`) |
| **Extensional (`Ext*`)** | `Std.ExtTreeMap α β cmp` (`Std/Data/ExtTreeMap/Basic.lean:71`) | `Std.ExtHashMap α β` (`Std/Data/ExtHashMap/Basic.lean:61`) | `Quotient` of bundled map by `Equiv` (`~m`); requires `[TransCmp cmp]` or `[EquivBEq α] [LawfulHashable α]`. | **No** (wraps `Quotient` over bundled map) | **No** (`Quot.lift` blocks concrete `Repr`, though `@[simp, grind =]` proves symbolic lookups) | **Yes** (`@[ext] theorem ext`, proved with `ext k; grind`, `ProbeStdDoData.lean:174–177`) | `ExtTreeMap` + `Lemmas`: **268** (53 `Std.*`) |

#### 5.2 Why Bundled Maps Fail Inside Recursive Inductives and `.Raw` Succeeds

When a container appears inside a recursive inductive type (such as
`inductive BadRecValue | scalar (v : UInt64) | structFields (fields :
Std.TreeMap Nat BadRecValue)` in `support/ProbeStdDoData.lean:135–138`), Lean's
nested-inductive elaborator specializes the underlying data type
`Std.DTreeMap.Internal.Impl Nat (fun _ => BadRecValue)` into a mutually
recursive inductive `_nested.Std.DTreeMap.Internal.Impl_3`. For bundled
`Std.TreeMap` (and likewise `Std.HashMap`, `Std.ExtTreeMap`, and
`Std.ExtHashMap`), the second structure field `wf :
DTreeMap.Internal.Impl.WF inner` expects an argument of the unspecialized type
`(DTreeMap.Internal.Impl Nat fun _ => BadRecValue) → Prop`. Moreover,
`Impl.WF` (`src/lean/Std/Data/DTreeMap/Internal/WF/Defs.lean:47–53`) cannot
itself be specialized by the nested-inductive translator because its
constructor `Impl.WF.constModify` places the value type family `β` in a
negative position (`f : α → Option γ → Option γ`). The kernel therefore rejects
`BadRecValue` with:

```text
error: (kernel) application type mismatch
  DTreeMap.Internal.Impl.WF inner
argument has type
  _nested.Std.DTreeMap.Internal.Impl_3
but function has type
  (DTreeMap.Internal.Impl Nat fun x => BadRecValue) → Prop
```

Unbundling the well-formedness invariant via `Std.TreeMap.Raw` or
`Std.HashMap.Raw` (`GoodRecValue` in `support/ProbeStdDoData.lean:146–149`)
leaves only the positive data constructors (`Std.DTreeMap.Internal.Impl` or
`Array AssocList`) inside the recursive inductive type, which passes kernel
inductive translation cleanly.

#### 5.3 Why `Std.TreeMap` / `Std.TreeMap.Raw` Should Be Used Instead of `Std.HashMap` for Kernel Evaluation

Every operation on `Std.TreeMap` and `Std.TreeMap.Raw` (`empty`, `insert`,
`get?`, `contains`, `erase`, `foldl`) is pure, structurally recursive, and
transparent to the Lean 4 kernel:

- `ProbeStdData.treemap_raw_kernel_reduce`
  (`support/ProbeStdDoData.lean:157–160`) proves concrete insertions and
  lookups on `Std.TreeMap.Raw Nat Nat` via `decide +kernel` with **zero
  axioms** (`'ProbeStdData.treemap_raw_kernel_reduce' does not depend on any
  axioms`).
- Symbolic lookup proofs on `Std.TreeMap.Raw` (`treemap_raw_lookup_insert`,
  `support/ProbeStdDoData.lean:169–172`) discharge both the lookup equality and
  all intermediate `WF` side-conditions automatically in a single step via
  `grind [Std.TreeMap.Raw.WF.insert]`.
- By contrast, `Std.HashMap` and `Std.HashMap.Raw` cannot reduce in the kernel
  even on an empty map (`blocker2_hashmap_empty_lookup_blocks_rfl` in
  `support/DiagnoseReduce.lean:68–71`) because `Std.DHashMap.Internal.mkIdx` is
  `@[irreducible]` and depends on `opaque System.Platform.getNumBits` and
  `opaque mixHash`. Any MIR symbolic evaluator or layout checker in `trusted/`
  or `theory/` that must reduce in the kernel via `rfl` or `decide +kernel`
  must therefore use `Std.TreeMap` / `Std.TreeMap.Raw` (or `Array` / `List`)
  rather than `Std.HashMap` / `Std.HashMap.Raw`.

## Boundaries

- **Non-Linear Bitvector Operations in `KernelBVDecide` (`unsupported` in
  current ROBDD prototype):**
  `KernelBVDecide.blastExpr` (`support/ProbeBVDecide.lean:643–678`) implements
  `.var`, `.const`, `.extract`, `.append`, `.un .not`, `.bin .and`, `.bin .or`,
  `.bin .xor`, `.bin .add`, `.bin .eq`, and `.bin .ult`, which suffice for
  alignment, masking, and checked unsigned addition obligations. General 64-bit
  multiplication (`mul`), unsigned division/remainder (`udiv`, `umod`), and
  variable shifts (`shl`, `ushr`, `sshr`) are not implemented in `blastExpr`
  because ROBDD representations of 64-bit multipliers grow exponentially in the
  bit width. Supporting 64-bit multiplication/division without `_native` axioms
  requires pairing a `Std.HashMap`-free AIG-to-CNF bitblaster with
  `KernelLRAT.checkCert_sound` (`ProbeBVDecide.lean:246–273`) so CaDiCaL solves
  the CNF externally and the kernel checks only the polynomial-time RUP
  certificate.
- **Propagate-Generate Basis Scope (`known not to apply` to $\ge 3$ independent
  addends):**
  The `bddVar` propagate-generate transformation (`ProbeBVDecide.lean:388–394`)
  applies specifically to variable 1 relative to variable 0 (`x_i ^^ p_i`),
  giving exact $2w + 1$ tree size for two-variable 64-bit additions (`x + y`)
  and one-variable constant additions (`x + c`). Obligations summing three or
  more independent 64-bit variables without an intermediate DAG cache or LRAT
  certificate can still exhibit exponential tree growth in a pure ROBDD.
- **`Std.*` Namespace Policy in `TrustedBoundary.lean` (`unsupported` without
  policy change):**
  `trusted/audit/TrustedBoundary.lean:34, 488` currently restricts
  `foundation-lock.json` modules to the `Init.` prefix. Admitting `Std.Do` or
  `Std.Data.TreeMap` directly into `trusted/lean/` (as opposed to keeping
  `trusted/lean/` on `Init.*` and importing `Std.*` in `theory/` or expanding
  the foundation prefix policy) is not supported without updating
  `TrustedBoundary.lean`.

## Evidence

### Primary Upstream and Repository Sources

All primary source coordinates were inspected and hashed in
[`support/source-manifest.json`](support/source-manifest.json):

1. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
   (`v4.34.1`):**
   - `src/lean/Init/Core.lean:2337–2409` (deprecation of `Lean.ofReduceBool`
     and `Lean.trustCompiler`; definition of `eagerReduce`).
   - `src/lean/Lean/Meta/Native.lean:37–87` (`Lean.Meta.nativeEqTrue` and
     per-theorem `_native.<tactic>.ax_*` axiom injection).
   - `src/lean/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26–44`
     (`LratCert.toReflectionProof` calling
     `Lean.Meta.nativeEqTrue \`bv_decide`).
   - `src/lean/Lean/Meta/Tactic/BVDecide/Reflect/SatAtBVLogical.lean:32–80`
     (`Reflect.reflectBV` and `SatAtBVLogical.proveFalse`).
   - `src/lean/Std/Tactic/BVDecide/Reflect.lean:60–95` (`verifyBVExpr` and
     `verifyBVExpr_bv_unsat`).
   - `src/lean/Std/Tactic/BVDecide/LRAT/Parser.lean:132, 201, 213, 279, 301`
     (`partial def parseActions` and `parseLRATProof`).
   - `src/lean/Std/Tactic/BVDecide/LRAT/Internal/Clause.lean:141–168`
     (`@[irreducible] def DefaultClause.ofArray.folder`).
   - `src/lean/Std/Tactic/BVDecide/Bitblast/BVExpr/Circuit/Impl/Expr.lean`
     (lines 47–118: `BVExpr.bitblast.go` and `BVExpr.Cache`).
   - `src/lean/Std/Sat/AIG/Basic.lean:139–159, 241–246, 480–491`
     (`@[irreducible] AIG.Cache` and well-founded `AIG.denote.go`).
   - `src/lean/Std/Sat/AIG/RelabelNat.lean:162–179`
     (`AIG.Entrypoint.relabelNat`).
   - `src/lean/Std/Data/DHashMap/Internal/Index.lean:51–53`
     (`@[irreducible] def Std.DHashMap.Internal.mkIdx`).
   - `src/lean/Lean/Elab/Tactic/Omega/Core.lean:107, 111, 224` (`omega` proof
     construction via `mkDecideProof` and `mkEqReflWithExpectedType`).
   - `src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean:240–300` and
     `src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Nat.lean:9, 41`
     (`eagerReflBoolTrue` and `Nat.ToInt.of_le` proof references).
   - `src/lean/Std/Do/SPred/SVal.lean:30–32`, `SPred.lean:34, 67–69`,
     `PostCond.lean:54–110, 255`, `PredTrans.lean:63–89`,
     `WP/Basic.lean:54–112`, `WP/Monad.lean:36–106`, `Triple/Basic.lean:37–38`,
     and `Lean/Elab/Tactic/Do/VCGen.lean:40–150, 453–489`.
   - `src/lean/Std/Data/DTreeMap/Internal/WF/Defs.lean:47–53`,
     `TreeMap/Basic.lean:67`, `TreeMap/Raw/Basic.lean:65`,
     `ExtTreeMap/Basic.lean:71`, `HashMap/Basic.lean:64`, and
     `HashMap/Raw.lean:61`.
2. **`joshlf/anneal` at `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`:**
   - `trusted/audit/TrustedBoundary.lean:201, 316, 318–329, 568–570, 845–858`.
   - `trusted/audit/src/lib.rs:1233`.
   - `trusted/lean/foundation-lock.json:1–56`.

### Preserved Mechanized Probes in `support/`

#### 1. [`support/ProbeBVDecide.lean`](support/ProbeBVDecide.lean) (1,006 lines, SHA-256 `3d2465d2...1053a6f8`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `StandardBVDecide.align_mask_bv64` | 34–36 | 64-bit alignment mask preservation via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, align_mask_bv64._native.bv_decide.ax_1_5]` |
| `StandardBVDecide.checked_add_no_overflow_bv64` | 41–43 | 64-bit unsigned addition overflow equivalence via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, checked_add_no_overflow_bv64._native.bv_decide.ax_1_5]` |
| `StandardBVDecide.bitwise_and_le_mask_bv64` | 48–50 | 64-bit bitwise AND upper bound via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, bitwise_and_le_mask_bv64._native.bv_decide.ax_1_5]` |
| `StandardBVDecide.uint64_align_roundup` | 55–59 | 64-bit `UInt64` alignment round-up via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, uint64_align_roundup._native.bv_decide.ax_1_5]` |
| `KernelLRAT.rupPropagate_sound` | 175–197 | Soundness of unit propagation over hint indices. | `[propext, Quot.sound]` |
| `KernelLRAT.checkCert_sound` | 246–273 | Soundness of total list-based LRAT/RUP certificate checker (`checkCert F cert = true → F.Unsat`). | `[propext, Quot.sound]` |
| `KernelLRAT.sampleCNF_unsat` | 291–292 | In-kernel LRAT certificate discharge via `decide +kernel` (6.21 ms). | `[propext, Quot.sound]` |
| `KernelBVDecide.eval_bddAnd`, `eval_bddOr`, `eval_bddXor` | 446–528 | Soundness of nested structurally recursive (`BDD.rec`) ROBDD gate operations. | `[propext, Quot.sound]` |
| `KernelBVDecide.eval_bddVar` | 547–562 | Soundness of the propagate-generate basis `(x_i, x_i ^^ y_i)` under `assignToBDDEnv`. | `[propext, Quot.sound]` |
| `KernelBVDecide.eval_carryLoop`, `eval_eqLoop` | 588–642 | Soundness of ripple-carry and bit-equality ROBDD loops against `BitVec.carry` and `==`. | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.eval_blastExpr`, `eval_blastPred`, `eval_blastLogical` | 680–901 | End-to-end soundness of `Std.HashMap`-free bitblasting over `BVExpr`, `BVPred`, and `BVLogicalExpr`. | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.unsat_of_checkBVLogicalUnsat` | 908–917 | Master reflection theorem: `checkBVLogicalUnsat expr = true → expr.Unsat`. | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.align_mask_bv64_kernel` | 964–966 | 64-bit alignment mask preservation proved in-kernel via `bv_decide_kernel` (642 ms). | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.checked_add_no_overflow_bv8/16/32/64_kernel` | 972–986 | 8-, 16-, 32-, and 64-bit unsigned addition overflow equivalence proved via `bv_decide_kernel` (1.59 s at 64-bit). | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.bitwise_and_le_mask_bv64_kernel` | 991–993 | 64-bit bitwise AND upper bound proved via `bv_decide_kernel` (456 ms). | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.uint64_align_roundup_kernel` | 998–1002 | 64-bit `UInt64` alignment round-up proved via `bv_decide_kernel` (3.02 s). | `[propext, Classical.choice, Quot.sound]` |

#### 2. [`support/ProbeGrindOmega.lean`](support/ProbeGrindOmega.lean) (69 lines, SHA-256 `abeb3548...c4d114`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `test_grind_eq` | 26–27 | Congruence closure and E-matching under `prelude` via `grind`. | `[propext, Classical.choice, Quot.sound]` |
| `mir_slice_subslice_bounds_omega` | 30–35 | Subslice index bounds check under `prelude` via `omega`. | `[propext, Quot.sound]` |
| `mir_struct_field_layout_omega` | 39–47 | Struct field layout and padding offset check under `prelude` via `omega`. | `[propext, Classical.choice, Quot.sound]` |
| `mir_slice_subslice_bounds_grind` | 50–55 | Subslice index bounds check under `prelude` via `grind` (`lia`). | `[propext, Classical.choice, Quot.sound]` |
| `mir_uint64_checked_index_grind` | 59–64 | `UInt64` bounded offset addition under `prelude` via `grind` (`ToInt` + `lia`). | `[propext, Classical.choice, Quot.sound]` |
| `mir_stride_offset_ring_grind` | 67–69 | Stride offset distributivity over `Int` under `prelude` via `grind` (`ring`). | `[propext, Classical.choice, Quot.sound]` |

#### 3. [`support/ProbeStdDoData.lean`](support/ProbeStdDoData.lean) (184 lines, SHA-256 `1cdc3c34...d5bf5d`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `ProbeStdDo.tryBumpAlloc_spec` | 66–72 | `@[spec]` Hoare triple for `StateM FrameState Bool` proved via `mvcgen [tryBumpAlloc] <;> grind`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdDo.allocPair_spec` | 85–89 | Compositional Hoare triple for sequential allocations proved via `mvcgen [allocPair] <;> omega`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdDo.checkedStep_spec` | 103–108 | Multi-barrel `EStateM String FrameState Nat` Hoare triple proved via `mvcgen [checkedStep] <;> omega`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdData.BadRecValue` | 135–138 | `#guard_msgs` proof that bundled `Std.TreeMap` fails kernel nested-inductive typechecking (`Impl.WF inner`). | N/A (`#guard_msgs` expected error) |
| `ProbeStdData.GoodRecValue` | 146–149 | Recursive inductive type nesting `Std.TreeMap.Raw` and `Std.HashMap.Raw`. | `[]` |
| `ProbeStdData.treemap_kernel_reduce` | 152–155 | In-kernel reduction (`decide +kernel`) on bundled `Std.TreeMap Nat Nat`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdData.treemap_raw_kernel_reduce` | 157–160 | Zero-axiom in-kernel reduction (`decide +kernel`) on `Std.TreeMap.Raw Nat Nat`. | `[]` (zero axioms) |
| `ProbeStdData.treemap_raw_lookup_insert` | 169–172 | Symbolic `Std.TreeMap.Raw` lookup proof discharging `WF` via `grind [Std.TreeMap.Raw.WF.insert]`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdData.exttreemap_ext_insert_comm` | 174–177 | Extensional equality (`m₁ = m₂`) on `Std.ExtTreeMap Nat Nat` proved via `ext k; grind`. | `[propext, Classical.choice, Quot.sound]` |

#### 4. [`support/DiagnoseReduce.lean`](support/DiagnoseReduce.lean) (178 lines, SHA-256 `ab854453...2f46c42`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `DiagnoseReduce.constFalse_aig_size_reduces` | 35–37 | Baseline showing `BVLogicalExpr.const false` reduces in the kernel via `eagerReduce (Eq.refl 1)`. | `[]` (zero axioms) |
| `DiagnoseReduce.blocker1_lrat_parser_cannot_reduce_in_kernel` | 50–52 | `#guard_msgs` witness that `LRAT.parseLRATProof` / `String.toUTF8` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.treeMap_empty_lookup_reduces_in_kernel` | 58–60 | Baseline showing `(∅ : Std.TreeMap Nat Nat)[0]? = none` reduces via `decide +kernel`. | `[propext, Classical.choice, Quot.sound]` |
| `DiagnoseReduce.blocker2_hashmap_empty_lookup_blocks_rfl` | 68–71 | `#guard_msgs` witness that `(∅ : Std.HashMap Nat Nat)[0]?` blocks kernel `rfl` at `mkIdx`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker3_and_4_bitblast_aig_cache_blocks_rfl` | 85–88 | `#guard_msgs` witness that 1-bit `BVLogicalExpr.bitblast` blocks kernel `rfl` at `Std.DHashMap` / `AIG.Cache`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker5_aig_denote_wf_blocks_rfl` | 99–102 | `#guard_msgs` witness that well-founded `AIG.denote` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker6_relabelNat_blocks_rfl` | 114–117 | `#guard_msgs` witness that `AIG.Entrypoint.relabelNat` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker7_defaultClause_ofArray_blocks_rfl` | 129–134 | `#guard_msgs` witness that `LRAT.Internal.DefaultClause.ofArray` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.omega_bounds_check`, `grind_uint64_lia_check`, `grind_int_ring_check` | 140–176 | `#guard_msgs in #print axioms` verification of `omega` and `grind` axiom footprints. | `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]` |

## Revalidation

To revalidate all findings and preserved probes on a Lean toolchain or after a
change to `Std.Tactic.BVDecide`, `Init.Omega`, `Init.Grind`, `Std.Do`,
`Std.Data`, or `TrustedBoundary.lean`, run the four standalone probes from the
package root:

```console
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/ProbeGrindOmega.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/ProbeStdDoData.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/DiagnoseReduce.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/ProbeBVDecide.lean
```

What each probe discriminates:

1. `support/DiagnoseReduce.lean` fails if any of the seven upstream
   `verifyBVExpr` / `Std.HashMap` kernel-reduction blockers becomes reducible
   (or changes its error message) or if `omega` or `grind` changes its axiom
   footprint.
2. `support/ProbeBVDecide.lean` verifies that `KernelLRAT.checkCert_sound` and
   `KernelBVDecide.unsat_of_checkBVLogicalUnsat` (`bv_decide_kernel`) compile
   within `-M1024` and discharge 64-bit `BitVec` and `UInt64` obligations using
   only `[propext, Classical.choice, Quot.sound]`.
3. `support/ProbeGrindOmega.lean` verifies that `prelude` + `Init.Omega` +
   `Init.Grind` + `Init.GrindInstances` + `Init.Data.Int.OfNat` suffices for
   congruence closure, `omega`, `lia`, `ToInt`, and `ring` without
   `TrustedBoundary.lean` Phase 1 syntax violations.
4. `support/ProbeStdDoData.lean` verifies `Std.Do` (`mvcgen` + `@[spec]`) and
   confirms both the `BadRecValue` nested-inductive rejection on bundled
   `Std.TreeMap` and zero-axiom kernel reduction on `Std.TreeMap.Raw`.
