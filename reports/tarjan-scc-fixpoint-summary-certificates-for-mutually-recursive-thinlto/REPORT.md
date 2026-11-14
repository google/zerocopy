# Tarjan SCC Greatest-Fixpoint (`SccGfpCert`) and Lexicographic Ranking (`SccRankingCert`) Summary Certificates for Mutually Recursive ThinLTO

## Summary

Bottom-up interprocedural summary propagation over directed acyclic call graphs (`propagate_summary_attrs_sound` in `cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`) cannot infer `nounwind`, memory-effect bounds (`readnone`, `readonly`, `argmemonly`), or `willreturn` across self-recursive ($|S| = 1$ with self-loop) or mutually recursive ($|S| \ge 2$) Strongly Connected Components (SCCs) such as recursive-descent JSON/AST parsers, DOM sanitizers, state-machine dispatchers, and recursive tree/slice algorithms. Furthermore, live probing of `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) (`support/scc_thinlto_synthesizer.py`, `support/scc_summary_comparison.json`) shows that while LLVM 23.1.1's `PostOrderFunctionAttrsPass` (`llvm/lib/Transforms/IPO/FunctionAttrs.cpp`) computes `nounwind` and `memory(...)` over Tarjan SCCs, **LLVM 23.1.1 fails to infer `willreturn` on `26 / 26` (`100%` miss rate) of bounded recursive and mutually recursive Rust functions** because `FunctionAttrs.cpp` (`checkNoCycles`) unconditionally abandons `willreturn` inference whenever a call-graph SCC contains a cycle!

This report designs, synthesizes (`support/scc_thinlto_synthesizer.py`), and mechanizes in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`; `support/lean/ThinLtoSccFixpointProofs.lean`, `6` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`) two complementary Tarjan SCC summary certificate schemas for `.anneal-summary` (`AnnealModuleSummaryV1`):

1. **Greatest-Fixpoint Co-Inductive Safety & Effect Certificates (`SccGfpCert` / `scc_gfp_nounwind_and_memeffect_sound`)**:
   - Because `nounwind` and `MemEffect` (`readnone ⊑ readonly ⊑ argmemonly ⊑ readwrite`) are universal step-indexed safety properties over finite execution prefixes, we prove by induction on call-stack step fuel `fuel : Nat` that if every function $f_i \in S$ in a cyclic SCC $S$ locally satisfies `(sccEffect, sccNounwind)` under the optimistic inductive hypothesis that all intra-SCC calls $f_i \to f_j$ ($f_j \in S$) also satisfy `(sccEffect, sccNounwind)`, then every finite execution of every $f_i \in S$ satisfies `(sccEffect, sccNounwind)`—**without requiring termination (`willreturn`)**.
   - Across our 30-function recursive and mutually recursive benchmark corpus (`support/recursive_thinlto_corpus.rs`), `SccGfpCert` upgrades `nounwind` and `MemEffect` precision from **`0 / 26` (`0%`) under DAG-only propagation** to **`26 / 26` (`100%`)**, and improves slice-tuple parser memory precision (`parse_json_value <-> parse_json_array <-> parse_json_object`) from LLVM 23.1.1's `argmemonly` to exact `readonly`.
2. **Lexicographic 2D Well-Founded Ranking Certificates for `willreturn` (`SccRankingCert` / `scc_lfp_willreturn_ranking_sound`)**:
   - Because `willreturn` is a least-fixpoint termination property where optimistic co-induction is unsound (`canary_coinductive_willreturn_without_ranking_unsound`), `SccRankingSynthesizer` assigns each function $f_i \in S$ a 2D lexicographic ranking measure $\mu_i(\vec{x}) = (\text{paramMeasure}_i(\vec{x}), \text{nodeRank}_i) \in \mathbb{N} \times \{0, \dots, |S|-1\}$ linearized as $\text{linearRank}(|S|, \mu_i) = \text{paramMeasure}_i \cdot |S| + \text{nodeRank}_i$.
   - The second coordinate $\text{nodeRank}_i \in \{0, \dots, |S|-1\}$ breaks ties across zero-decrease mutual dispatcher hops (such as `eval_expr(depth, x) -> eval_term(depth, x) -> eval_factor(depth, x)` with ranks `2 > 1 > 0`) before the recursive backedge (`eval_factor(depth, x) -> eval_expr(depth - 1, x)`) strictly decreases `paramMeasure` (`FarkasCert2`).
   - Across the 30-function corpus (`19` Tarjan SCCs: `7` multi-function mutually recursive SCCs of size $2 \le |S| \le 4$ and `12` self-recursive singleton SCCs), `SccRankingSynthesizer` proves `willreturn = true` on **`26 / 26` (`100%`) of bounded recursive functions in `0.133 ms` total synthesis time** (vs. **`0 / 26` for both DAG-only summary propagation and stock LLVM 23.1.1**) while rejecting `100%` of unbounded/non-decreasing canaries (`canary_unbounded_collatz_rec`, `canary_zero_decrease_cycle_a <-> b`).
   - Certifying `willreturn + readnone + nounwind` on the mutually recursive `eval_expr <-> eval_term <-> eval_factor` SCC enables dead-call elimination (DCE) and loop-invariant code motion (LICM) at caller sites, reducing caller loop runtime from **`1,123.60` $\mu\text{s}$ to `3.31` $\mu\text{s}$ (`339.46x` speedup)**.
3. **Condensation-DAG Incremental Cache Key Soundness (`condensation_scc_cache_hit_sound`)**:
   - Extends `incremental-function-and-thinlto-summary-proof-cache-architecture`'s `AnnealCacheKey` from DAG nodes to Tarjan's condensation DAG (`CondensationSccCacheKey`), ensuring $O(|S| + |E_S|)$ local recomputation when editing a function inside SCC $S$.

## Applicability

- **Subjects**:
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
  - `joshlf/anneal` (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`)
- **Targets examined**: `x86_64-unknown-linux-gnu` (`rustc -C opt-level=3 --emit=llvm-ir`).
- **Relationship to other corpus packages**: Extends `cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`, `unified-farkas-knownbits-and-aegraph-side-condition-certificates`, and `incremental-function-and-thinlto-summary-proof-cache-architecture`.

## Findings

### 1. Why LLVM 23.1.1 `FunctionAttrs.cpp` Fails to Infer `willreturn` on Recursive SCCs

`Basis: source + execution (support/recursive_thinlto_corpus.rs, support/scc_thinlto_synthesizer.py, support/scc_summary_comparison.json)`

In LLVM 23.1.1 (`llvm/lib/Transforms/IPO/FunctionAttrs.cpp`), `PostOrderFunctionAttrsPass` traverses the LazyCallGraph in bottom-up Tarjan SCC order:
- For **memory effects** (`checkFunctionMemoryAccess`) and **`nounwind`** (`inferAttrsFromFunctionBodies`), LLVM iterates over all nodes $f \in S$ in the current SCC optimistic-co-inductively: if no instruction in any $f \in S$ unwinds or calls an external may-unwind function, every $f \in S$ receives `nounwind`.
- For **`willreturn`** (`willReturn`), however, LLVM checks two conditions: (1) the SCC must be a trivial singleton with **zero self-recursion** (`SCC.size() == 1` and no call edge $f \to f$), and (2) every internal CFG loop in $f$ must have a finite `ScalarEvolution` max backedge taken count (`checkNoCycles`). Whenever $|S| \ge 2$ or $f$ contains a recursive self-call, `PostOrderFunctionAttrsPass` unconditionally leaves `willreturn` unset!

Table 1 compares attribute inference across all 30 functions (`19` Tarjan SCCs) in `support/recursive_thinlto_corpus.rs` (`support/scc_thinlto_benchmarks.csv`):

| SCC ID & Functions ($|S|$) | Category | DAG-Only (`propagate_summary_attrs_sound`) (`nounwind` / `Mem` / `willreturn`) | LLVM 23.1.1 `-O3` (`nounwind` / `Mem` / `willreturn`) | Anneal `SccGfpCert` + `SccRankingCert` (`nounwind` / `Mem` / `willreturn`) | Synthesized 2D Lexicographic Measure $\mu_i = (\text{paramMeasure}, \text{nodeRank})$ |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `SCC 1`: `parse_json_{value, array, object}` (`3`) | Mutual JSON Parser | `false / readwrite / false` | `true / argmemonly / false` | **`true / readonly / true`** | `(buf.len(), 0)` (`-1` slice drop on every edge) |
| `SCC 2`: `eval_{expr, term, factor}` (`3`) | Mutual AST Evaluator | `false / readwrite / false` | `true / readnone / false` | **`true / readnone / true`** | `(depth, 2) -> (depth, 1) -> (depth, 0) -> (depth - 1, 2)` |
| `SCC 3`: `fsm_state_{header, length, payload, trailer}` (`4`) | 4-State Protocol FSM | `false / readwrite / false` | `true / readnone / false` | **`true / readnone / true`** | `(rem, 3) -> (rem, 2) -> (rem, 1) -> (rem, 0) -> (rem - 1, 3)` |
| `SCC 4`: `dom_visit_{element, children}` (`2`) | Mutual DOM Sanitizer | `false / readwrite / false` | `true / readonly / false` | **`true / readonly / true`** | `(nodes.len(), 0)` |
| `SCC 5`: `regex_match_{seq, alt}` (`2`) | Mutual Regex Matcher | `false / readwrite / false` | `true / readonly / false` | **`true / readonly / true`** | `(pat_fuel, 1) -> (pat_fuel, 0) -> (pat_fuel - 1, 1)` |
| `SCC 6`: `unify_type_{term, args}` (`2`) | Mutual Type Unifier | `false / readwrite / false` | `true / readnone / false` | **`true / readnone / true`** | `(fuel, 1) -> (fuel, 0) -> (fuel - 1, 1)` |
| `SCCs 7..15`: `9` Pure/Readonly Self-Recursive Fns (`1` each) | `gcd`, `bsearch`, `trie`, `bst`, `varint`, `pow_mod`, `utf8`, `leb128`, `adler32` | `false / readwrite / false` | `true / readnone..readonly / false` | **`true / readnone..readonly / true`** | `(fuel \| slice.len() \| bits(val), 0)` |
| `SCC 16`: `argmem_mutating_fill_rec` (`1`) | Slice Mutator | `false / readwrite / false` | `true / argmemonly / false` | **`true / argmemonly / true`** | `(dst.len(), 0)` |
| `SCC 17`: `canary_unbounded_collatz_rec` (`1`) | Canary (3n+1 Unbounded) | `false / readwrite / false` | `true / readnone / false` | `true / readnone /` **`false` (Rejected)** | `NONE` (`3n + 1` fails `FarkasCert2` decrease) |
| `SCC 18`: `canary_zero_decrease_cycle_{a, b}` (`2`) | Canary (Zero-Decrease Cycle) | `false / readwrite / false` | `true / readnone / false` | `true / readnone /` **`false` (Rejected)** | `NONE` (Cycle in zero-decrease subgraph) |
| `SCC 19`: `canary_panicking_recursive_walk` (`1`) | Canary (Explicit `panic!`) | `false / readwrite / false` | `false / readwrite / false` | **`false` (Rejected)** `/ readnone / false` | `(depth, 0)` (Unwinds on `x == 0xDEAD_BEEF`) |

Across the **26 bounded terminating recursive functions**:
- **DAG-only summary propagation (`propagate_summary_attrs_sound`)** proves `0 / 26` `nounwind`, `0 / 26` `readonly`/`argmemonly`, and `0 / 26` `willreturn`.
- **Stock LLVM 23.1.1 (`-O3`)** proves `26 / 26` `nounwind` and `26 / 26` `readnone`/`readonly`/`argmemonly`, but **`0 / 26` (`0.0%`) `willreturn`**.
- **Anneal `SccGfpCert` + `SccRankingCert`** proves **`26 / 26` (`100.0%`) `nounwind`, `26 / 26` (`100.0%`) `readnone`/`readonly`/`argmemonly`, and `26 / 26` (`100.0%`) `willreturn`** in `0.133 ms` total synthesis time.

---

### 2. Lean `v4.34.1` Mechanization of `SccGfpCert` and `SccRankingCert`

`Basis: source + execution (support/lean/ThinLtoSccFixpointProofs.lean)`

All 6 theorems in `support/lean/ThinLtoSccFixpointProofs.lean` check in the Lean `v4.34.1` kernel with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Mechanized Property | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `scc_gfp_nounwind_and_memeffect_sound` | By induction on call-stack depth `fuel : Nat`, if every $f \in S$ locally satisfies `sccAttrs : SafetySummaryAttrs` (`memEffect`, `nounwind`), then `execSccStep ... fuel f` satisfies `sccAttrs` for all `fuel` and all $f \in S$ regardless of cycles in `nextCallee`. | `[propext]` |
| `checkLexEdgeDec_implies_linearRank_lt` | Whenever `checkLexEdgeDec sccSize rSrc rDst = true` (`rDst.nodeRank < sccSize` and lexicographic decrease), `linearRank sccSize rDst < linearRank sccSize rSrc`. | `[propext, Quot.sound]` |
| `scc_lfp_willreturn_ranking_sound` | Under `ValidSccRankingCert`, every call `(f, arg)` in a mutually recursive SCC terminates (`evalMutualScc = true`) within `linearRank sccSize (rankOf f arg) + 1` steps. | `[propext, Quot.sound]` |
| `condensation_scc_cache_hit_sound` | Equality of `CondensationSccCacheKey = (sccMemberMirHashes, upstreamSccSummaryHash)` over Tarjan's condensation DAG preserves `SccValid`. | *(none)* |
| `canary_coinductive_willreturn_without_ranking_unsound` | Negative canary: `infLoopStep f x = some (f, x)` satisfies `LocalSccBodyValid` (`readnone`, `nounwind`) but `evalMutualScc infLoopStep 10 0 42 = false`. | *(none)* |
| `canary_zero_decrease_cycle_rejected` | Negative canary: no assignment of `(rF, rG)` can satisfy `checkLexEdgeDec 2 (n, rF) (n, rG)` and `checkLexEdgeDec 2 (n, rG) (n, rF)` simultaneously. | `[propext, Quot.sound]` |

## Boundaries

- **Data-Dependent / Non-Lexicographic Termination Measures (Ackermann, Unbounded Graph Flood-Fill)**: `SccRankingSynthesizer` restricts automatic synthesis to 2D lexicographic affine/bit-shift measures `(linear_param_measure, tie_break_node_rank)` dischargeable by `FarkasCert2` (`unified-farkas-knownbits-and-aegraph-side-condition-certificates`). Recursive functions whose termination depends on heap-allocated visited sets or higher-ordinal measures remain conservatively `willreturn = false` (while still receiving full `SccGfpCert` `nounwind` and `MemEffect` summaries!).
- **Indirect Recursion Through Function Pointers or Unresolved VTables**: Tarjan SCC decomposition operates over direct call edges and closed/devirtualized trait call edges in `.anneal-summary`; an indirect call through an unknown function pointer (`*fn_ptr`) outside a closed `ExportList` cannot be placed in a bounded SCC and is treated as a conservative external call (`readwrite`, `willreturn = false`).

## Evidence

- **Mechanized Lean `v4.34.1` proof development and 30-function SCC benchmark**:
  - `support/lean/ThinLtoSccFixpointProofs.lean` (`6` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`)
  - `support/lean/lakefile.lean`
  - `support/recursive_thinlto_corpus.rs` (`30` recursive and mutually recursive Rust functions)
  - `support/scc_thinlto_synthesizer.py`
  - `support/scc_summary_comparison.json`
  - `support/scc_thinlto_benchmarks.csv`
- **Primary upstream source citations**:
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Transforms/IPO/FunctionAttrs.cpp` (`PostOrderFunctionAttrsPass`, `ReversePostOrderFunctionAttrsPass`, `checkNoCycles`, and `thinLTOPropagateFunctionAttrs`)
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1414-1420` (`LLVMRustPrepareThinLTOResolveWeak` / `thinLTOFinalizeInModule` with `PropagateAttrs=true`)

## Revalidation

Run both the Lean `v4.34.1` kernel proof check and the 30-function Tarjan SCC synthesizer and LLVM 23.1.1 attribute comparison probe:

```bash
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean \
  reports/tarjan-scc-fixpoint-summary-certificates-for-mutually-recursive-thinlto/support/lean/ThinLtoSccFixpointProofs.lean
python3 reports/tarjan-scc-fixpoint-summary-certificates-for-mutually-recursive-thinlto/support/scc_thinlto_synthesizer.py
```

Verify that `lean` exits with status `0` and zero `sorryAx`, and that `scc_thinlto_synthesizer.py` proves `willreturn = true` on `26 / 26` bounded recursive functions (compared to `0 / 26` for LLVM 23.1.1) while rejecting all `4` negative canaries.
