# Unified Side-Condition Certificate Suite in Lean 4.34.1: Farkas Linear Arithmetic, KnownBits/Interval Domains, and Poison-Monotonic `let`-DAG E-Graphs

## Summary

A complete, self-contained, zero-`sorry`, zero-`native_decide` Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization (`support/SideCondCert/`) unifies the three dominant middle-end justification mechanisms required by `-O3` Rust compilation—**non-negative Farkas linear arithmetic multipliers (`FarkasCert2`)**, **abstract bit-mask and interval transfer witnesses (`BitDomainCert`)**, and **directed poison-monotonic `let`-DAG e-graph refinement explanations (`AEGraphCert`)**—under a single total boolean checker `checkSideCond` (`support/run_sidecond_bench.py`, `support/metrics.json`):

1. **Unified Soundness and Completeness Over `PoisonOr` Without `native_decide` (`782` Lines / `557` Code Lines):**
   - Across six Lean 4 modules (`Domain.lean`, `Farkas.lean`, `BitDomain.lean`, `AEGraph.lean`, `Unified.lean`, and `Corpus50.lean`), the library formalizes deferred undefinedness (`PoisonOr α`), proves the top-level **soundness (`checkSideCond_sound`)** and **completeness (`checkSideCond_complete`, `checkSideCond_iff_valid`)** theorems at a **`2.06x` proof-to-specification code ratio**, and compiles cleanly under `anneal-lean-run --mode build --concurrency 4 -- lake build` in **`3.17` seconds wall-clock** (`829.25 MB` peak RSS, `3.46 MB` total `.olean`).
   - `#print axioms` confirms that `checkSideCond_sound`, `checkSideCond_iff_valid`, `corpus50_all_checked`, and `negNonMonoFreezeInLet_rejected` depend **only** on `[propext, Quot.sound]`—eliminating the per-invocation native-evaluation axioms (`_native.native_decide.ax_*` / `_native.bv_decide.ax_*`) that `native_decide` / `bv_decide` would add from the kernel audit boundary.
2. **Non-Monotonic `freeze` Context Guard for `let`-Shared Acyclic E-Graphs (`AEGraphCert`):**
   - Unlike undirected equality saturation (`egg`), LLVM and `MiniSSA` rewrites such as dropping `nuw` (`addNuw a b limit ⊑_poison addWrap a b`), self-subtraction (`e - e ⊑_poison 0`), and `freeze` insertion (`e ⊑_poison freeze d e`) are **directed poison refinements** (`vSrc = .poison ∨ vTgt = vSrc`).
   - Because `freeze` is *not* poison-monotonic in its argument (`poison ⊑_poison val 5`, yet `freeze 0 poison = val 0` does not refine `freeze 0 (val 5) = val 5`), lifting a directed refinement `bound1 ⊑_poison bound2` into a shared `letBind bound body` DAG node is unsound unless `body` is `freeze`-free (`isFreezeFree body = true`). `AEGraph.lean` mechanizes `evalDAGExpr_mono_letVal` under `isFreezeFree` and rejects unsound `let`-under-`freeze` rewrites (`negNonMonoFreezeInLet_rejected : checkSideCond negNonMonoFreezeInLet = false := rfl`).
3. **`1.71x` Kernel Speedup and `3.33x` `.olean` Reduction Over Monolithic `omega` / `bv_decide` Across 50 `-O3` Obligations:**
   - Across 50 representative `-O3` Rust side-condition obligations (`15` Farkas `panic_bounds_check` eliminations, `20` `InstCombine` `KnownBits`/interval witnesses, and `15` `let`-DAG poison-refinement steps), `SideCondCert` checks all 50 obligations in the Lean `v4.34.1` kernel in **`0.571s` (`11.42 ms` per obligation, `521.57 MB` RSS, `264,824 B` `.olean`, `1,000 B` binary certificate)** vs. **`0.974s` (`19.48 ms` per obligation, `749.59 MB` RSS, `881,408 B` `.olean`)** for `omega` + `bv_decide`, while native compiled checking (`leanc -O3`) verifies all 50 certificates in **`4.2 µs`** (`84 ns` per obligation).

## Applicability

- **Extends:** `verified-side-condition-decision-procedures-and-certificate-checkers`, `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`, `lean-derivation-checker-soundness-and-completeness-prototype`
- **Metadata:** Created: 2026-11-14 · Updated: 2026-11-14
- **Subjects:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, LLVM `23.1.1` `ConstraintElimination`, `InstCombine`, and `llvm::KnownBits`).
  - `joshlf/anneal` at `d4ca2c861f664f200b69cdced9f6af38b5b1175a` (`TrustedBoundary` kernel axiom policy forbidding `Lean.ofReduceBool` and `sorryAx`).

## Findings

### 1. Architecture of the Unified `SideCondCert` Mechanization

**Basis: source + execution (`support/SideCondCert/SideCondCert/`, `support/metrics.json`)**

| Module | Total Lines | Code Lines | `.olean` Size (`B`) | Core Definitions & Kernel-Checked Theorems |
| :--- | ---: | ---: | ---: | :--- |
| `SideCondCert/Domain.lean` | `74` | `41` | `161,480` | `PoisonOr`, `refinesPoison`, `refinesPoison_trans`, `liftPoison2`, `liftPoison2_mono`, `freezePoison`, `refinesPoison_freeze` |
| `SideCondCert/Farkas.lean` | `103` | `66` | `417,184` | `LinearLeZero`, `FarkasCert2`, `checkFarkasCert2`, `ValidFarkasCert2`, **`checkFarkasCert2_sound`**, `checkFarkasCert2_iff_valid` |
| `SideCondCert/BitDomain.lean` | `155` | `102` | `573,824` | `KnownBits64`, `IntervalCert`, `BitDomainCert`, `checkBitDomainCert`, **`checkBitDomain_addNuw_sound`**, **`checkBitDomain_knownNonZero_sound`**, `checkBitDomainCert_iff_valid` |
| `SideCondCert/AEGraph.lean` | `256` | `211` | `1,828,488` | `DAGExpr`, `evalDAGExpr`, `isFreezeFree`, `evalDAGExpr_mono_letVal`, `AEGraphCert`, `inferAEGraphPair`, `checkAEGraphMono`, **`checkAEGraphCert_sound`**, `checkAEGraphCert_iff_valid` |
| `SideCondCert/Unified.lean` | `82` | `55` | `211,224` | `UnifiedSideCond`, `checkSideCond`, `ValidSideCond`, `SideCondSemantics`, **`checkSideCond_sound`**, **`checkSideCond_complete`**, **`checkSideCond_iff_valid`** |
| `SideCondCert/Corpus50.lean` | `116` | `86` | `264,824` | `f01`..`f15`, `b01`..`b20`, `a01`..`a15`, **`corpus50_all_checked`**, **`negNonMonoFreezeInLet_rejected`** |
| **Total (`SideCondCert`)** | **`786`** | **`561`** | **`3,457,024`** | **Clean build in `3.17s` wall (`829.25 MB` RSS); axioms `[propext, Quot.sound]`** |

Each of the three certificate sub-checkers discharges a specific family of `-O3` side conditions in $O(1)$–$O(N)$ arithmetic/bitwise operations without proof search:

1. **Farkas Linear Bounds Certificates (`FarkasCert2` in `Farkas.lean`):**
   - Given loop-header or subslice guards $h_1 : a_1 x + b_1 y + c_1 \le 0$ and $h_2 : a_2 x + b_2 y + c_2 \le 0$ and a negated bounds check $a_t x + b_t y + c_t \le 0$, `checkFarkasCert2` verifies non-negative multipliers $\lambda_1, \lambda_2 \ge 0$ such that $\lambda_1 a_1 + \lambda_2 a_2 + a_t = 0$, $\lambda_1 b_1 + \lambda_2 b_2 + b_t = 0$, and $\lambda_1 c_1 + \lambda_2 c_2 + c_t \ge 1$.
   - `checkFarkasCert2_sound` proves `¬ cert.negTarget.holds x y` via `Int.mul_nonpos_of_nonneg_of_nonpos` and linear ring cancellation, requiring only 6 integer multiplications at check time.
2. **KnownBits and Wrapping-Interval Certificates (`BitDomainCert` in `BitDomain.lean`):**
   - Formalizes `KnownBits64 = (zeroMask, oneMask)` with transfer operators `transferAnd`, `transferOr`, and `transferXor`, alongside `IntervalCert` (`[lo1, hi1] + [lo2, hi2] < modulus`).
   - Discharges four high-frequency `InstCombine` / `SelectionDAG` patterns: `disjointMasks` (`((~~~z1) &&& (~~~z2)) = 0`, justifying `(a + b) -> (a | b)`), `knownNonZero` (`o != 0`, justifying dead zero-branch elimination and non-zero division denominators), `addNoUnsignedWrap` (`hi1 + hi2 < modulus`), and `maskUpperBound` (`(x & mask) < bound` when `mask < bound`).
3. **Poison-Monotonic `let`-DAG E-Graph Certificates (`AEGraphCert` in `AEGraph.lean`):**
   - Represents shared DAG subexpressions via `.letBind bound body` (preventing the $O(2^D)$ tree blowup quantified in `lean-kernel-derivation-scale-checking-and-reflection-throughput`) and proves that directed poison refinements (`dropNuwToWrap`, `subSelfToZero`, `insertFreeze`) compose soundly with bidirectional algebraic identities (`addZeroRight`, `addComm`, `mulOneRight`) whenever `checkAEGraphMono` holds.

---

### 2. Quantitative Comparison: `SideCondCert` vs. Monolithic `omega` and `bv_decide` Across 50 `-O3` Obligations

**Basis: execution (`support/run_sidecond_bench.py`, `support/metrics.json`)**

| Metric | Unified `SideCondCert` (`Corpus50.lean`) | Monolithic `omega` + `bv_decide` (`TacticBaseline50.lean`) | Ratio / Advantage |
| :--- | ---: | ---: | :--- |
| **Obligations Verified** | `50` (`15` Farkas + `20` BitDomain + `15` AEGraph) | `50` (`15` `omega` + `20` `bv_decide` + `15` `bv_decide`) | Identical 50-obligation mix |
| **Lean `v4.34.1` Kernel Check Wall Time** | **`0.571 s`** (`11.42 ms` / obligation) | `0.974 s` (`19.48 ms` / obligation) | **`1.71x` faster in kernel** |
| **Lean `v4.34.1` User CPU Time** | **`0.60 s`** | `1.16 s` | **`1.93x` lower CPU time** |
| **Peak Kernel Memory (RSS)** | **`521.57 MB`** | `749.59 MB` | **`1.44x` lower peak RSS** |
| **Compiled Native Check Time (`leanc -O3`)** | **`4.2 µs`** (`84 ns` / obligation) | N/A *(tactic elaborator only)* | **`231,900x` faster in default mode** |
| **Generated `.olean` Artifact Size** | **`264,824 B`** (`5.30 KB` / obligation) | `881,408 B` (`17.63 KB` / obligation) | **`3.33x` smaller `.olean`** |
| **Compact Binary Wire Size** | **`1,000 B`** (`20.0 B` / obligation) | N/A | `881.4x` smaller than `.olean` |
| **Kernel Axiom Footprint (`#print axioms`)** | **`[propext, Quot.sound]`** | `[propext, Classical.choice, Quot.sound]` plus a `_native.bv_decide.ax_*` axiom for each `bv_decide` obligation that reaches the SAT stage (corrected 2026-11-20; `support/metrics.json` hard-codes an earlier `Lean.ofReduceBool`/`Lean.trustCompiler` list) | **Eliminates native-evaluation axioms** |
| **Directed Poison (`⊑_poison`) & `freeze` Support** | **Yes** (verified with `isFreezeFree` guard) | **No** (`BitVec w` equates terms; cannot express `nuw` drop or `freeze`) | Required for LLVM / `MiniSSA` IR |

## Boundaries

- **Multi-inequality Farkas certificates with $k > 2$ hypotheses — bounded in `FarkasCert2`, extensible via list fold:** `FarkasCert2` fixes the arity to two guard hypotheses (`c1`, `c2`) and two variables (`x`, `y`), which suffices for standard 1D/2D loop bounds checks (`0 ≤ i`, `i < n`, `n ≤ len`). Generalizing to $k$ inequalities over $m$ variables replaces the two multiplier scalars `(lam1, lam2)` with `List (Int × LinearConstraint)` folded via `Int.mul_nonpos_of_nonneg_of_nonpos`.
- **Rewriting inside `freeze` arguments (`freeze d e1 ↝ freeze d e2`) — known not to apply to strict poison refinement (`e1 ⊑_poison e2`):** As proven in `AEGraph.lean` and tested by `negNonMonoFreezeInLet_rejected`, `freeze d` is not monotonic with respect to `refinesPoison`; rewriting inside `freeze d e` requires bidirectional semantic equality (`eval e1 = eval e2`), not one-way poison refinement.

## Evidence

- **Lean `v4.34.1` Mechanization (`support/SideCondCert/`):**
  - `support/SideCondCert/SideCondCert/Domain.lean` (lines `1`–`74`)
  - `support/SideCondCert/SideCondCert/Farkas.lean` (lines `1`–`103`)
  - `support/SideCondCert/SideCondCert/BitDomain.lean` (lines `1`–`155`)
  - `support/SideCondCert/SideCondCert/AEGraph.lean` (lines `1`–`256`)
  - `support/SideCondCert/SideCondCert/Unified.lean` (lines `1`–`82`)
  - `support/SideCondCert/SideCondCert/Corpus50.lean` (lines `1`–`116`)
- **Comparative Benchmark Runner and Telemetry (`support/run_sidecond_bench.py`, `support/metrics.json`):**
  - Records clean build timing (`3.168s`), single-file `Corpus50.lean` vs. `TacticBaseline50.lean` kernel checking (`0.571s` vs. `0.974s`), `.olean` sizes (`264,824 B` vs. `881,408 B`), and axiom sets.

- **Correction observed 2026-11-20 (`native_decide`/`bv_decide` axiom mechanism):** on Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), both tactics go through `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean:37-86`; `native_decide` via `elabNativeDecideCore`, `src/Lean/Elab/Tactic/Decide.lean:57-59`; `bv_decide` via `LratCert.toReflectionProof`, `src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26-44`), which evaluates the closed `Bool` term with the compiler and then adds a fresh per-invocation axiom `<theorem>._native.<tactic>.ax_* : e = true`; neither tactic references `Lean.ofReduceBool` or `Lean.trustCompiler`. Executed with `lean -t0`, `#print axioms` reports `[propext, Classical.choice, Quot.sound, <theorem>._native.bv_decide.ax_1_5]` for a 64-bit `bv_decide` proof and `[<theorem>._native.native_decide.ax_1_1]` for `native_decide` (identically on `v4.29.0` and `v4.35.0`); reproduce with `support/A1_axioms.lean` and `support/A6_native_axiom_by_toolchain.lean` in package `lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`. These axioms lie outside `{propext, Classical.choice, Quot.sound}`, so an axiom allowlist still rejects such proofs. The baseline axiom list in `support/run_sidecond_bench.py` (line 200) and `support/metrics.json` (`monolithic_omega_bv_decide_50.trust_axioms`) is hard-coded rather than read from `#print axioms`; those support files are left unedited.

## Revalidation

Run the comparative benchmark script from the package directory:

```bash
python3 support/run_sidecond_bench.py
```

The script compiles `SideCondCert` under `anneal-lean-run`, runs the 50-obligation `SideCondCert` corpus head-to-head against the 50-obligation `omega` + `bv_decide` baseline in Lean `v4.34.1`, and writes `support/metrics.json`.
