# Arbitrary $k$-Premise Sparse Linear Farkas Certificates (`FarkasCertN`) and Graduated `freeze`-Set Refinement (`⊑_freeze_set`)

## Summary

The unified side-condition certificate checker in
`reports/unified-farkas-knownbits-and-aegraph-side-condition-certificates`
discharged 2-premise slice bounds (`FarkasCert2`), `KnownBits` masks
(`BitDomainCert`), and `freeze`-free acyclic e-graph rewrites (`AEGraphCert`)
in Lean `v4.34.1` (`5045d0056413`), but had two explicit expressiveness
boundaries:
1. **`FarkasCert2` Fixed-Arity Limit ($k = 2, m = 2$):** Multi-guard subslice
   bounds (`subslice[a..b][i]` requiring `0 ≤ a`, `a ≤ b`, `b ≤ c`, `c + i < len`
   over $k = 5$ premises and $m = 5$ variables), 2D/3D tiled matrix indexing,
   and `LoopVectorize` alias separation could not be represented; and
2. **Blanket `isFreezeFree` Syntactic Block Inside `freeze`:** Because LLVM's
   `freeze` operator is non-monotonic with respect to one-way poison refinement
   (`.poison ⊑_poison .val 5`, yet `freeze 0 .poison = .val 0 ⋠_poison freeze 0 (.val 5) = .val 5`),
   `checkAEGraphMono` rejected **100% of rewrites** inside `.freeze d e` or
   across `.letBind bound body` whenever `body` contained `.freeze`.

This report resolves both boundaries in a zero-`sorry`, zero-`native_decide`
Lean `v4.34.1` mechanization (`support/K3SideCond/`, `906` total lines, `661`
code lines, `[propext, Quot.sound]` only):

1. **Arbitrary $k$-Premise, $m$-Variable Sparse Linear Farkas Certificates (`FarkasCertN`) + `BitVec`-to-`Int` No-Wrap Bridge (`BridgedFarkasCert`):**
   Represents arbitrary affine inequalities as sparse `(varId × coeff)` lists
   (`SparseLinearLeZero`), folds $k$ non-negatively scaled premises in a single
   pass (`combinePremises`), and pairs `FarkasCertN` with an interval no-wrap
   certificate (`IntervalNoWrapCert`) proving `(a * stride + b) % 2^w = a * stride + b`.
2. **Oracle-Indexed `freeze`-Set Refinement (`⊑_freeze_set`) & Graduated Context Modes (`isStrictEqCert` vs. `isGraduatedValid`):**
   Distinguishes bidirectional poison-preserving equivalences (`isStrictEqCert`,
   where `eval s = eval t` under every freeze-site oracle `oracle : Nat → Int`)
   from one-way poison-erasing refinements (`dropNuwToWrap`, `subSelfToZero`,
   `insertFreeze`). Algebraic identities with `isStrictEqCert = true` lift
   freely inside `.freeze siteId e` and across `.letBind` bodies containing
   `.freeze`, while unsound `freeze` duplications and non-monotonic `nuw`-drops
   inside `freeze` are provably rejected.

Across an 80-obligation benchmark suite (`Corpus80.lean`: `30` multi-premise
$k \in \{5, 6\}$ sparse Farkas bounds checks, `25` `BitVec`-to-`Int` bridged
bounds checks, `20` positive in-`freeze` `AEGraph` rewrites, and `5` negative
unsound `freeze` rejection checks—`0 / 75` positive obligations expressible in
the prior 2-premise/`isFreezeFree` checker), `K3SideCond` verifies **100% (`80 / 80`)**
in-kernel by `rfl` in **`8.07 ms` net kernel time per obligation** (`645.73 ms`
net across 80 obligations vs. `10.12 ms`/obligation for `omega`, with zero
`Classical.choice` or `Lean.ofReduceBool`).

## Applicability

These findings apply to:
- **Lean 4:** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
  (`v4.34.1`), specifically kernel `whnf` / `is_def_eq` reduction of `rfl`
  certificate theorems.
- **Rust & LLVM Middle-End Passes:** `rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`, bundled LLVM `23.1.1`
  at `1b9c0d5ff9bb`), specifically `ConstraintElimination`, `IndVarSimplify`,
  `InstCombine`, `EarlyCSE`, and `GVN` operating over `nuw`/`nsw`, `poison`,
  and `freeze`.
- **Anneal Trusted Boundary:** `joshlf/anneal` at
  `7abf0691c404393e3e4fc26eb3d4094e3170b5c7` (`[propext, Quot.sound]` axiom
  whitelist).

## Findings

### 1. Arbitrary $k$-Premise, $m$-Variable Sparse Farkas Certificates (`SparseFarkas.lean`)

`Basis: source + execution`

In `support/K3SideCond/K3SideCond/SparseFarkas.lean`, an affine constraint over
an unbounded variable environment `env : Nat → Int` is represented sparsely as:

```lean
structure SparseLinearLeZero where
  constTerm : Int
  terms     : List (Nat × Int)
```

with semantics `con.eval env = con.constTerm + evalTerms env con.terms ≤ 0`.
`insertTerm v c ts` merges coefficient `c` for variable `v` into `ts` and
prunes any variable whose combined coefficient reaches `0`
(`if sum = 0 then rest else (v', sum) :: rest`). We prove:

1. **`evalTerms_insertTerm` & `evalTerms_addScaledTerms`:**
   Inserting or scaling sparse term lists preserves exact affine evaluation:
   `evalTerms env (addScaledTerms lam ts acc) = lam * evalTerms env ts + evalTerms env acc`.
2. **`eval_combinePremises_le_acc`:**
   For any list of premise pairs `premises : List (Int × SparseLinearLeZero)`
   satisfying `allMultipliersNonNeg premises = true` ($\forall i,\, \lambda_i \ge 0$)
   and `AllPremisesHold env premises` ($\forall i,\, p_i(\text{env}) \le 0$),
   folding `combinePremises premises acc` satisfies:
   ```lean
   (combinePremises premises acc).eval env ≤ acc.eval env
   ```
3. **`checkFarkasCertN_sound` & `checkFarkasCertN_iff_valid`:**
   `checkFarkasCertN cert` checks `allMultipliersNonNeg cert.premises && decide (combined.terms = [] ∧ 1 ≤ combined.constTerm)`
   where `combined := combinePremises cert.premises cert.negTarget`. When
   `checkFarkasCertN cert = true`, all variable coefficients cancel to `[]`,
   yielding `1 ≤ combined.constTerm = combined.eval env ≤ cert.negTarget.eval env`,
   which contradicts `cert.negTarget.holds env` (`cert.negTarget.eval env ≤ 0`).

### 2. Modular `BitVec w` to Mathematical `Int` No-Wrap Bridge (`BitVecBridge.lean`)

`Basis: source + execution`

Because machine slice indexing operates on fixed-width `BitVec w` (`UInt32` /
`UInt64`) arithmetic modulo $2^w$, `FarkasCertN` over mathematical `Int`
requires a proof that the index computation `a * stride + b` does not wrap
modulo `modLimit = 2^w`. In `BitVecBridge.lean`:

- `checkIntervalNoWrap (c : IntervalNoWrapCert) : Bool` verifies in $O(1)$
  integer arithmetic that `0 ≤ c.loA ≤ c.hiA`, `0 ≤ c.loB ≤ c.hiB`,
  `0 ≤ c.stride`, and `c.hiA * c.stride + c.hiB < c.modLimit`.
- **`checkIntervalNoWrap_sound`** proves via `Int.mul_le_mul_of_nonneg_right`
  and `Int.emod_eq_of_lt` that for every `a ∈ [loA, hiA]` and `b ∈ [loB, hiB]`,
  `0 ≤ a * c.stride + b < c.modLimit` and
  `(a * c.stride + b) % c.modLimit = a * c.stride + b`.
- **`checkBridgedFarkasCert_sound`** composes `checkIntervalNoWrap_sound` with
  `checkFarkasCertN_sound` into a single boolean certificate checker.

### 3. Oracle-Indexed `freeze`-Set Refinement and Graduated Context Tracking (`FreezeRefinement.lean`)

`Basis: source + execution`

In LLVM IR and MiniSSA, each dynamic execution of `freeze e` resolves `.poison`
to an arbitrary nondeterministic concrete value, whereas two references to the
*same* `let`-bound variable `let x = freeze e in ...` observe the *same* frozen
value. `FreezeRefinement.lean` models this precisely by indexing each syntactic
`.freeze siteId e` node with a `siteId : Nat` and parameterizing evaluation by
a freeze-site oracle `oracle : Nat → Int`:

```lean
| .freeze siteId e =>
    match evalFreezeDAG oracle env letVal e with
    | .val v => .val v
    | .poison => .val (oracle siteId)
```

We then classify `GraduatedAEGraphCert` constructors into two decidable tiers:
- **`isStrictEqCert : GraduatedAEGraphCert → Bool` (`≡_poison`):** Returns
  `true` for exact poison-preserving identities (`refl`, `addZeroRight`,
  `subZeroRight`, `addComm`, `mulOneRight`, `doubleToMulTwo`,
  `xorSelfToSubSelf`, `elimFreezeConst`, `freezeIdem`, and their congruences).
  Theorem **`isStrictEqCert_sound`** proves that whenever
  `isStrictEqCert cert = true`,
  `evalFreezeDAG oracle env letVal src = evalFreezeDAG oracle env letVal tgt`
  holds with strict `PoisonOr Int` equality (`=`).
- **`isGraduatedValid : GraduatedAEGraphCert → Bool` (`⊑_freeze_set`):**
  1. Allows `.congFreeze siteId c` whenever `isStrictEqCert c = true`
     (unlocking all algebraic rewrites inside `freeze`, such as
     `freeze site (x + 0) ~> freeze site x` and
     `freeze site (x + x) ~> freeze site (2 * x)`), while rejecting one-way
     `poisonRefines` steps inside `.congFreeze` (such as
     `freeze site (addNuw x y 256) ~> freeze site (addWrap x y)`);
  2. Allows `.congLetBind cBound cBody` *without* requiring `isFreezeFreeDAG` on
     `cBody` whenever `isStrictEqCert cBound = true` (including
     `let x = freeze site a in x + x ~> let x = freeze site a in 2 * x`),
     requiring `isFreezeFreeDAG` only when `cBound` is a strict one-way poison
     refinement (`dropNuwToWrap`, `subSelfToZero`, `insertFreeze`).
- **Counterexample Theorems (`freeze_duplication_unsound_witness` & `dropNuw_inside_freeze_rejected`):**
  We prove in-kernel that duplicating a `let`-bound `freeze` across two
  distinct freeze sites (`let x = freeze 0 v in x - x` vs.
  `freeze 0 v - freeze 1 v`) violates `refinesPoison` under `v = .poison` and
  `oracle 0 = 10, oracle 1 = 20` (`val 0 ≠ val (-10)`), and that
  `checkAEGraphGraduated` returns `false` on all 5 negative unsound `freeze`
  test cases in `Corpus80.lean`.

### 4. 80-Obligation Benchmark & Module Summary (`Corpus80.lean`)

`Basis: execution`

| Module / Metric | Total Lines | Code Lines | `.olean` Size (Bytes) | Verified Theorems & Obligations |
| :--- | ---: | ---: | ---: | :--- |
| `SparseFarkas.lean` | `194` | `135` | `600,144` | `checkFarkasCertN_sound`, `checkFarkasCertN_iff_valid` |
| `BitVecBridge.lean` | `93` | `55` | `337,560` | `checkIntervalNoWrap_sound`, `checkBridgedFarkasCert_sound` |
| `FreezeRefinement.lean` | `431` | `350` | `2,513,656` | `isStrictEqCert_sound`, `checkAEGraphGraduated_sound`, `freeze_duplication_unsound_witness` |
| `Corpus80.lean` | `188` | `121` | `429,704` | `80` concrete obligations (`30` `FarkasCertN` + `25` `BridgedFarkasCert` + `20` pos `freeze` + `5` neg `freeze`) |
| **Total (`K3SideCond`)** | **`906`** | **`661`** | **`3,881,064`** | **Net kernel check: `645.73 ms` (`8.07 ms` / obligation), `[propext, Quot.sound]` only** |

## Boundaries

- **Non-linear polynomial inequalities (`known not to apply` to variable-times-variable products `x * y ≤ z`):**
  `SparseLinearLeZero` and `FarkasCertN` require each term to be linear in a
  single variable `v` (`c * env v`) or a constant stride (`a * c.stride + b`
  in `IntervalNoWrapCert`). General non-linear products of two dynamic loop
  variables (`i * j < n`) require upstream strength reduction (`IndVarSimplify`)
  or an auxiliary variable substitution before certificate generation.
- **Dataflow-sensitive non-poisonness inside `freeze` (`not examined` in syntactic `isStrictEqCert`):**
  `isStrictEqCert` is a purely syntactic structural check on the rewrite
  certificate. Rewriting `freeze site (addNuw x y limit) ~> freeze site (addWrap x y)`
  when an external `BitDomainCert` / `IntervalNoWrapCert` proves that `x + y < limit`
  (so `addNuw x y limit` can never evaluate to `.poison` in that basic block)
  requires passing the `IntervalNoWrapCert` witness into a conditional
  `congFreezeNonPoison` constructor.

## Evidence

- **Lean `v4.34.1` mechanization (`[propext, Quot.sound]` only, zero `sorry`, zero `native_decide`):**
  - `support/K3SideCond/K3SideCond/SparseFarkas.lean`
  - `support/K3SideCond/K3SideCond/BitVecBridge.lean`
  - `support/K3SideCond/K3SideCond/FreezeRefinement.lean`
  - `support/K3SideCond/K3SideCond/Corpus80.lean`
- **Benchmark script and recorded metrics:**
  - `support/run_k3_bench.py` and `support/k3_metrics.json`.

## Revalidation

To rebuild `K3SideCond`, audit `#print axioms` across all soundness theorems,
and rerun the 80-obligation benchmark suite:

```bash
python3 support/run_k3_bench.py
```

Verify in `support/k3_metrics.json` that `"uses_sorry_or_native_decide"` is
`false`, `"axioms"` is `["propext", "Quot.sound"]`, and
`"k3_expressible_out_of_75_positive"` is `75`.
