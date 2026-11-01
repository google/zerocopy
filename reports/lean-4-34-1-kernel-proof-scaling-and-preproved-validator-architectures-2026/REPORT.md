# Lean 4.34.1 C++ Kernel Proof-Checking Cost Model, Pre-Proved Validator Architectures, and Incremental Shard Verification

## Summary

Checking per-crate Rust MIR verification proofs (`Proof.lean`) inside the Lean
`v4.34.1` C++ kernel (`5045d0056413266e57c625dcd7c365b10e377c52`) while keeping
Anneal's Trusted Computing Base (`trusted/lean/`) restricted to behavioral
refinement (`Trusted/Refinement.lean`) and small-step MIR semantics
(`Trusted/MirSemantics.lean`) is governed by six mechanical properties of the
Lean kernel and refinement algebra:

1. **Absence of Expression Hash-Consing and $O(N^2)$ Small-Step Scaling:**
   Lean 4 does not hash-cons `expr` allocations (`src/kernel/expr.cpp`). When a
   term has reference count `m_rc == 1` (`is_likely_unshared`,
   `src/kernel/expr.h:386-388`), `replace_rec_fn` (`src/kernel/replace_fn.cpp:34`)
   disables its substitution cache `m_cache`. Alternating `App` and `Lambda`
   binders in continuation-passing small-step proofs
   (`reachesPrefix_safeAndEnsures_of_step` in `theory/Anneal/MirLemmas.lean:58-74`)
   force `type_checker::infer_lambda` (`src/kernel/type_checker.cpp:129-142`) to
   call `instantiate_rev` on the entire remaining $(N - k)$-step proof subtree
   at every step $k$, cloning $\sum_{k=1}^N O(N - k) = O(N^2)$ unshared nodes
   (`4,715.554 ms` kernel replay at $N = 500$). Binding intermediate states in a
   single contiguous `let`-block (`type_checker::infer_let`,
   `type_checker.cpp:208-230`) and stepping by structural list suffix
   consumption (`SuffixReach`) eliminates both $O(N^2)$ terms (`78.048 ms` at
   $N = 500$, a **60.4x speedup**).
2. **C++ GMP `has_fvar` Bypass Hazard and `String.beq` Kernel Interpreter Tax:**
   `type_checker::reduce_nat` (`src/kernel/type_checker.cpp:703`) is the sole
   native arithmetic fast path in the Lean `v4.34.1` kernel, and it immediately
   aborts (`if (has_fvar(e)) return none_expr();`) before calling `whnf` on
   operands if the outer expression has `has_fvar == true`. Lazy projections out
   of a `let`-bound state `FVar` (`st_k.r0`) leave `has_fvar == true`, silently
   disabling GMP reduction and causing `Nat.shiftRight` (`>>>`), `Nat.div`,
   `Nat.mod`, `Nat.land`, `Nat.lor`, and `Nat.xor` to get permanently stuck on
   `WellFounded.fix`. Unpacking states at step entry via `State.casesOn`
   (`stepInstrStrict` / `evalStepStrict`) forces `reduce_rec`
   (`type_checker.cpp:462`) to unfold the `FVar` to a closed constructor before
   arithmetic terms are built. Furthermore, `String.beq` has no native C++
   reducer; evaluating `lookupFn prog fnName` by `rfl` steps through UTF-8 byte
   comparisons in the kernel interpreter at **`~11.5 ms` per string comparison**
   (`114.645 ms` across 10 comparisons), whereas structural `List.Mem`
   (`.tail`/`.head`) witnesses short-circuit on $O(1)$ pointer equality
   (`is_bi_equal`).
3. **Three-Layer Hybrid Pre-Proved `Theory` Architecture:**
   Across straight-line blocks ($N \in \{10..500\}$), chained CFG diamonds
   ($D \in \{2..10\}$), multi-call functions ($K \in \{2..20\}$), loops, and
   side conditions, no single homogeneous proof style is optimal everywhere.
   Combining **Layer 1** pre-proved GMP `Nat` side-condition reflection
   (**51.7x faster** than `omega`, **1,047x fewer DAG nodes** when batched),
   **Layer 2** `cv_trans` `Nat`-domain reflection (`evalCvProg_sound`, **116.6x
   faster** than continuation lambdas and **1.38x faster** than `BitVec 64`
   reflection) plus fused MIR superinstruction idioms (`step_idiom5`, **173.3x
   faster**), and **Layer 3** cut-point diamond convergence
   (`diamond_converge_step`, **201.4x faster** at $D = 10$), interprocedural
   call summaries (**62.0x faster** at $K = 20$), and inductive loop summaries
   (**625.0x faster** at $M = 100$, plus symbolic trip counts `m : Nat` in
   `0.134 ms`) achieves linear $O(N)$ scaling and constant-size block proof
   certificates (`33`–`40` DAG nodes).
4. **Hint-Driven Translation Validators (`Language.Abstracts`):**
   Emitting a pre-computed `TransPlan` witness from `anneal-rustc-capture` into
   `Proof.lean` and validating it in `theory/Anneal/` (`evalSym_sound`) avoids
   running fixed-point CFG/loop discovery (`computePlan`) inside the Lean
   kernel, shrinking proof DAGs by **11.3x** (`59` vs. `665` nodes), unshared
   expression trees by **155.6x** (`223` vs. `34,705`), and kernel replay time
   by **24.2%–26.3%** over unhinted `lowerToPure`. Pre-composing multi-pass
   chains via `Abstracts.comp` speeds up per-function pass composition by
   **3.91x** (`67 us` vs. `262 us`).
5. **Interprocedural `Call1Summary` Lifting, `MirLang.sem` Call-Table Fix, and
   Eliminating the $O(3^K)$ Record-Update Tree Blowup:**
   `Trusted/MirSemantics.lean:1794` currently hardcodes a single-entry function
   table `fns := [⟨"__entry", body⟩]` inside `MirLang.sem`, causing every call
   to any other function `fnName ≠ "__entry"` to evaluate
   `lookupFn prog fnName = none` and step to `.stuck`. Pairing `MirProg` with
   `MirBody` in `MirLang.Prog` resolves interprocedural calls through
   `MirLang.sem` while preserving `DecidableEq`. In `theory/Anneal/`, expressing
   step or summary post-states with Lean's `{ s with ... }` record-update syntax
   duplicates the state reference `s` across every unchanged field, creating an
   **$O(3^K)$ (or $O(6^K)$) unshared expression tree blowup** (`17,134,141` tree
   nodes at $K = 10$ calls); destructuring states into flat constructor tuples
   `⟨curBody, locals, blk, stmtIdx, stack⟩` references each field once,
   reducing unshared tree nodes by **1,800.8x** (`9,515` vs. `17,134,141`) and
   accelerating kernel replay by **4.66x**.
6. **Two-Stage Kernel Replay, Structural TCB Witnesses, and Incremental
   `ShardCert` Verification (`3,001.5x` End-to-End Speedup):**
   `trusted/audit/TrustedBoundary.lean:906-972` currently sets `base ← importEnv
   j foundation` and replays all of `trusted ++ theory ++ crateModules` on every
   `cargo anneal verify` invocation, negating `.olean` prefix caching. Placing
   hash-verified `trusted ++ theory` (and unchanged per-function `ShardCert`
   modules) into `base`, replacing $O(N^2 \cdot |\text{AST}|)$ `by decide` TCB
   membership lookups with structural `.tail`/`.head` witnesses (**32.4x**
   per-shard speedup), and combining all optimizations in a unified 5-stage
   benchmark (`UnifiedEndToEndStack.lean`) over a 10-function crate reduces
   full-crate Stage-2 kernel replay from **`5,042.587 ms` (`Stage 0`) to
   `157.056 ms` (`Stage 3`, `32.11x` speedup; `43.716 ms` / `115.35x` excluding
   one-time `String.beq` callee lookups)** and single-function incremental
   replay to **`1.680 ms` (`Stage 4`, `3,001.54x` speedup, range `1.680 ms`–
   `11.279 ms` across all 10 shards)** with 100% fail-closed positive and
   negative soundness canaries.

## Applicability

The findings and measurements in this report apply to the following concrete
subjects and their combinations:

1. **Lean 4 Kernel and Elaborator (`leanprover/lean4`):**
   - **Revision:** `5045d0056413266e57c625dcd7c365b10e377c52` (release tag
     `v4.34.1`, `x86_64-unknown-linux-gnu`).
   - **Scope:** C++ kernel expression representation (`src/kernel/expr.h`,
     `src/kernel/expr.cpp`), structural equality (`src/kernel/expr_eq_fn.cpp`),
     de Bruijn instantiation (`src/kernel/instantiate.cpp`,
     `src/kernel/replace_fn.cpp`), type inference and WHNF reduction
     (`src/kernel/type_checker.h`, `src/kernel/type_checker.cpp`,
     `src/kernel/inductive.cpp`), `Environment.replay` (`src/lean/Lean/Replay.lean`),
     elaborator WHNF (`src/lean/Lean/Meta/WHNF.lean`), and core library
     definitions (`Init/Prelude.lean`, `Init/Data/BitVec/Basic.lean`,
     `Init/Data/Nat/Bitwise/Lemmas.lean`).
   - **Invocation constraints:** All empirical benchmarks run with
     `-DElab.async=false -Ddebug.skipKernelTC=false` and measure standalone
     Stage-2 kernel verification via `baseEnv.toKernelEnv.replay newConsts`.
2. **Anneal Verification Stack (`joshlf/anneal`):**
   - **Revisions examined:**
     - `24367bd1a8c784f2578535954f9915e24894a56f` (`main`: `PRINCIPLES.md`,
       `AGENTS.md`).
     - `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core`, PR `#72`–`#81`:
       `trusted/lean/Trusted/Refinement.lean`,
       `trusted/lean/Trusted/MirSemantics.lean`,
       `theory/Anneal/Refinement.lean`, `theory/Anneal/MirLemmas.lean`,
       `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`,
       `trusted/rustc-capture/src/proof_gen.rs`).
     - `e75556f5767705404404c0675c6d2d9bcee41d6f` (`skeleton`, PR `#60`:
       `theory/Anneal/FunctionalTranslation.lean`).
   - **Relationship among subjects:** Anneal's per-crate proof generator
     (`proof_gen.rs`) and theory library (`theory/Anneal/`) produce Lean 4 proof
     terms (`Proof.lean`) that are elaborated by `lean` and replayed by
     `trusted/audit/TrustedBoundary.lean` inside the Lean `v4.34.1` C++ kernel.
3. **Target Rust Workload Archetypes (`google/zerocopy`):**
   - **Revision:** `1897ac488fd7bf2bc7bbe2cf7f1bfa0dcde2e1fc` (`reference`
     branch).
   - **Relationship:** Supplies the concrete `core` helper call patterns
     (`Option::unwrap_or`, `Option::is_some`, `NonZero::new`, `checked_add`,
     `wrapping_add`, `size_of`, `align_of`, `transmute_copy`, `<[T]>::len`,
     `<[T]>::get`), pointer alignment/disjointness side conditions, and
     multi-function crate structures modeled in the benchmark suites.

Exact execution timings depend on the host CPU and memory hierarchy (`Linux
x86_64`), whereas expression graph sizes (`DECLS`, `DAG_NODES`, `TREE_NODES`),
complexity classes ($O(N^2)$, $O(3^K)$, $O(2^D)$, $O(N)$, $O(1)$), and C++
kernel code paths are deterministic functions of the examined revisions. Do not
assume without revalidation (see **Revalidation**) that later Lean 4 releases
preserve the absence of native `String.beq` or `BitVec` kernel reducers or the
exact `has_fvar` guard in `type_checker::reduce_nat`.

## Findings

### Finding 1: Lean `v4.34.1` C++ Kernel Cost Model — Absence of Hash-Consing, Cache Mechanics (`m_infer_type`, `m_whnf_core`, `m_whnf`, `m_success`/`m_failure`), and the Two $O(N^2)$ Small-Step Bottlenecks (`infer_lambda` + `instantiate_rev` Cloning when `m_rc == 1` vs. Contiguous `infer_let`)

`Basis: source + execution + derived`

#### 1.1 Expression Representation, Reference Counting, and Cache Lookup Costs

In `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`):

1. **In-Memory `expr` Layout and Absence of Hash-Consing (`src/kernel/expr.h`,
   `src/kernel/expr.cpp`):**
   - Each `expr_cell` (`src/kernel/expr.h:99-145`) stores an atomic reference
     count `m_rc`, an 8-bit `m_kind`, and a 64-bit `m_data` header word packing
     a 32-bit structural hash (`hash(e)`), a 16-bit loose bound-variable range
     (`get_loose_bvar_range(e)`), and boolean flags `has_fvar`, `has_expr_mvar`,
     and `has_univ_mvar` (`src/kernel/expr.cpp:42-55, 105-126`) (`source`).
   - Lean 4 **does not hash-cons `expr` allocations**. Two structurally
     identical expressions constructed at different times occupy distinct heap
     addresses (`!is_eqp(a, b)`) unless they share the same pointer or originate
     from a deduplicated `.olean` compacted region (`source`).
   - `is_likely_unshared(expr const & e)` (`src/kernel/expr.h:386-388`) returns
     `!is_shared(e)`, i.e., `e.raw()->m_rc == 1` (`source`).

2. **Kernel Caches in `type_checker::state` (`src/kernel/type_checker.h`,
   `src/kernel/expr_maps.h`, `src/kernel/expr_eq_fn.cpp`):**
   - `type_checker::state` (`src/kernel/type_checker.h:32-44`) maintains five
     hash tables per `type_checker` instance (`source`):
     - `expr_map<expr> m_infer_type[2]`: maps an expression `e` to its inferred
       type, indexed by `bool infer_only` (`src/kernel/type_checker.cpp:250-260`).
     - `expr_map<expr> m_whnf_core`: caches `whnf_core(e, false, false)` results
       (`src/kernel/type_checker.cpp:498-549`).
     - `expr_map<expr> m_whnf`: caches full `whnf(e)` results
       (`src/kernel/type_checker.cpp:744-773`).
     - `expr_pair_set m_success` and `expr_pair_set m_failure`: cache positive
       and negative `is_def_eq(t, s)` pairs
       (`src/kernel/type_checker.cpp:941-977`).
   - Lean 3's union-find `equiv_manager` was removed in Lean 4 and replaced by
     the flat pair sets `m_success` and `m_failure` because definitional
     equality with structure projections and heuristic unfolding is
     non-transitive (`source`).
   - `expr_map<T>` (`src/kernel/expr_maps.h:15-17`) uses `expr_hash` ($O(1)$
     read of `m_data`) and `is_bi_equal` $\to$ `expr_eq_fn<false>`
     (`src/kernel/expr_eq_fn.cpp:17-58`). When two keys collide on hash:
     - If `is_eqp(a, b)` (identical pointer), `expr_eq_fn` returns `true` in
       $O(1)$ (`src/kernel/expr_eq_fn.cpp:21`) (`source`).
     - If `!is_eqp(a, b)` (distinct pointers with identical structure),
       `expr_eq_fn` recursively traverses both trees
       (`src/kernel/expr_eq_fn.cpp:26-54`), allocating a pair cache `m_cache`
       only when `is_shared(a) && is_shared(b)` and incrementing the heartbeat
       counter at every node (`source`).

3. **Why `FVar` Unfolding Bypasses `m_whnf_core` but Hits `m_whnf`:**
   In `type_checker::whnf_core` (`src/kernel/type_checker.cpp:492-508`),
   `case expr_kind::FVar:` returns `whnf_fvar(e, cheap_rec, cheap_proj)` at line
   `503` *before* the `m_st->m_whnf_core.find(e)` lookup at line `508`. Thus
   `whnf_core` never caches `FVar` unfoldings directly (`source`). However,
   `type_checker::whnf(expr const & e)` (`src/kernel/type_checker.cpp:744-773`)
   checks `m_st->m_whnf.find(e)` at line `749` before calling `whnf_core` and
   inserts `(e, r)` into `m_st->m_whnf` at line `771`. Consequently, any
   `let`-bound `FVar` (`ldecl`) passed to `whnf(e)` (such as the major premise
   of `reduce_rec` at `type_checker.cpp:462` or `reduce_proj` at
   `type_checker.cpp:447`) has its unfolded value cached in `m_st->m_whnf` and
   reused in $O(1)$ pointer-equality hits on subsequent lookups (`source`,
   `derived`).

#### 1.2 The Two $O(N^2)$ Small-Step Proof Bottlenecks vs. Contiguous `infer_let`

In `src/kernel/instantiate.cpp:15-53` (`instantiate_fn`), substituting free
variables or arguments into a binder body invokes `replace_rec_fn::operator()`
(`src/kernel/replace_fn.cpp:34-46`):

```cpp
bool shared = ! is_likely_unshared(e);
if (shared) {
    if (m_cache) {
        auto it = m_cache->find(e);
        if (it != m_cache->end())
            return it->second;
    } else {
        m_cache.reset(new expr_map<expr>());
    }
}
```

Whenever a subterm contains loose bound variables in range
(`get_loose_bvar_range(e) > s`), `instantiate_fn` allocates fresh `expr` cells
along every path to a bound variable (`src/kernel/instantiate.cpp:25-44`). Those
freshly allocated cells have reference count `m_rc == 1`
(`is_likely_unshared(e) == true`), so any subsequent `instantiate` or
`instantiate_rev` over them **disables `m_cache` completely** and allocates
another generation of fresh pointers (`source`).

This mechanism drives two independent $O(N^2)$ bottlenecks in $N$-step
small-step proofs:

1. **Pathology A — Alternating `App`/`Lambda` Continuation Chains (`Arch 1b`):**
   In `theory/Anneal/MirLemmas.lean:58-74` and
   `trusted/rustc-capture/src/proof_gen.rs:413-510`
   (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`),
   `reachesPrefix_safeAndEnsures_of_step` chains an $N$-step trace by wrapping
   the remaining $(N - k)$-step continuation in a lambda at every step:
   $$\text{safeAndEnsures\_of\_step } h_{\text{step},0}\ hr_0\ (\lambda n_1\ hr_1.\ \text{safeAndEnsures\_of\_step } h_{\text{step},1}\ hr_1\ (\lambda n_2\ hr_2.\ \dots))$$
   In `type_checker::infer_lambda` (`src/kernel/type_checker.cpp:129-142`):
   ```cpp
   while (is_lambda(e)) {
       ...
       fvars.push_back(mk_local(binding_name(e), d, binding_info(e)));
       e = binding_body(e);
   }
   expr r = infer_type_core(instantiate_rev(e, fvars.size(), fvars.data()), infer_only);
   ```
   Because `safeAndEnsures_of_step` (`App`) and `fun n_k hr_k =>` (`Lambda`)
   alternate at every step $k$, `while (is_lambda(e))` peels only 2 binders
   (`n_k`, `hr_k`) before stopping at the next `App`. It then calls
   `instantiate_rev(e, 2, fvars)` on the **entire remaining $(N - k)$-step proof
   subtree** `e`. Because `hr_k` (`BVar #0`) occurs inside step $k$, the spine
   and all enclosing lambda wrappers are cloned with `m_rc == 1` at every step
   $k = 1, \dots, N$, performing $\sum_{k=1}^N O(N - k) = O(N^2)$ allocations
   and invalidating `m_infer_type[false]` at every level (`source`, `derived`).
   At $N = 500$ instructions, this drives kernel replay to **`4,715.554 ms`**
   and elaboration to **`55,796.6 ms`** (`execution`).

2. **Pathology B — Flat `Reach.step` Chains with Global PC Indexing (`Arch 1a`):**
   Even without continuation lambdas, a flat proof chain
   `Reach.step s_0 s_1 v rfl (Reach.step s_1 s_2 v rfl ...)` checks `rfl` for
   `evalStep prog s_k = .step s_{k+1}` at each step $k$, which indexes
   `prog[s_k.pc]?` in a length-$N$ linked list `prog : List Instr`. Step $k$
   performs $k$ `List.getElem?_cons_succ` unfoldings in `whnf`
   ($\sum_{k=0}^{N-1} O(k) = O(N^2)$ total list-indexing reductions) and embeds
   each intermediate state `s_k` twice without pointer sharing, taking
   **`4,681.158 ms`** kernel replay at $N = 500$ (`source`, `execution`).

3. **Linear $O(N)$ Fix via Contiguous `infer_let` + Structural `SuffixReach`
   (`Arch 2`):**
   In `type_checker::infer_let` (`src/kernel/type_checker.cpp:208-230`):
   ```cpp
   while (is_let(e)) {
       ...
       expr val = instantiate_rev(let_value(e), fvars.size(), fvars.data());
       fvars.push_back(mk_local(let_name(e), let_type(e), val));
       e = let_body(e);
   }
   expr r = infer_type_core(instantiate_rev(e, fvars.size(), fvars.data()), infer_only);
   ```
   When all $N + 1$ intermediate states are bound in a **single contiguous
   `let`-block** (`let st_0 := ...; let st_1 := ...; ...; let st_N := ...; body`)
   where each `let_value(e)` is a closed state literal
   (`!has_loose_bvars(let_value(e))`), `instantiate_rev(let_value(e), ...)`
   returns in **$O(1)$** (`src/kernel/instantiate.cpp:60-61`), and the
   `while (is_let(e))` loop calls `instantiate_rev` on `body` **once** in
   $O(|body|) = O(N)$ time. Combined with `SuffixReach (i :: rest)` (which
   matches the head instruction `i` in $O(1)$ instead of indexing `prog[pc]?` in
   $O(k)$), kernel replay drops from `4,715.554 ms` to **`78.048 ms` at
   $N = 500$ (60.42x speedup)** (`source`, `execution`).

---

### Finding 2: Native C++ GMP Reducers (`type_checker::reduce_nat`), the `has_fvar` GMP Bypass Hazard on `let`-Bound States (`Nat.shiftRight` / `Nat.div` Stuckness and the `State.casesOn` Unpacking Fix), and the `String.beq` UTF-8 Kernel Interpreter Bottleneck (`~11.5 ms` per Comparison vs. Structural `List.Mem` and GMP `Nat.beq`)

`Basis: source + execution + derived`

#### 2.1 Complete Inventory of Native C++ Kernel Reducers (`type_checker::reduce_nat`)

In `src/kernel/type_checker.cpp:524-530` (`whnf_core`), before delta-unfolding a
constant, the C++ kernel calls `reduce_nat(e)` (`src/kernel/type_checker.cpp:702-733`).
`reduce_nat` is the **only** native arithmetic fast path in the Lean `v4.34.1`
C++ kernel; there are no native reducers for `BitVec`, `UInt64`, `Fin`, `Int`,
`ByteArray`, or `String` (`source`).

| Lean Constant | Arity | C++ Implementation (`src/kernel/type_checker.cpp`) | Preconditions & Resource Guards | Fallback When Guard / `has_fvar` Fails |
| :--- | :---: | :--- | :--- | :--- |
| `Nat.succ` | 1 | `reduce_unary_nat_op`: `a + 1` (line `706`) | `!has_fvar(e)`; `v1 = whnf(e1)` is `Nat.zero` or `natVal` | Constructor `Nat.succ e1` (stays in WHNF) |
| `Nat.add` | 2 | `reduce_bin_nat_op`: `a + b` (line `710`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Structural recursion on arg 2 (`Nat.brecOn`, $O(b)$) |
| `Nat.sub` | 2 | `reduce_bin_nat_op`: `a <= b ? 0 : a - b` (line `711`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Structural recursion on arg 2 (`Nat.brecOn`, $O(b)$) |
| `Nat.mul` | 2 | `reduce_bin_nat_op`: `a * b` (lines `667-675, 712`) | `!has_fvar(e)`; `v1.size() + v2.size() <= g_nat_max_size` (`128 MiB`) | Structural recursion on arg 2 ($O(b)$ additions) |
| `Nat.pow` | 2 | `reduce_pow`: `mpz::pow(a, b)` (lines `643-665, 713`) | `!has_fvar(e)`; `b <= UINT_MAX`; `v1.log2() * b <= g_nat_max_size * 8` | Structural recursion on exponent $b$ |
| `Nat.gcd` | 2 | `reduce_bin_nat_op`: `gcd(a, b)` (line `714`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `WellFounded.fix` (**stuck in kernel `whnf`**) |
| `Nat.mod` | 2 | `reduce_bin_nat_op`: `b == 0 ? 0 : a % b` (line `715`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.modCore` via `WellFounded.fix` (**stuck if $a \ge b$**) |
| `Nat.div` | 2 | `reduce_bin_nat_op`: `b == 0 ? 0 : a / b` (line `716`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.divCore` via `WellFounded.fix` (**stuck if $a \ge b$**) |
| `Nat.beq` | 2 | `reduce_bin_nat_pred`: `a == b` (line `717`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Mutual structural recursion ($O(\min(a, b))$) |
| `Nat.ble` | 2 | `reduce_bin_nat_pred`: `a <= b` (line `718`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | Mutual structural recursion ($O(\min(a, b))$) |
| `Nat.land` | 2 | `reduce_bin_nat_op`: `a & b` (line `719`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.bitwise and` via `WellFounded.fix` (**stuck**) |
| `Nat.lor` | 2 | `reduce_bin_nat_op`: `a \| b` (line `720`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.bitwise or` via `WellFounded.fix` (**stuck**) |
| `Nat.xor` | 2 | `reduce_bin_nat_op`: `a ^ b` (line `721`) | `!has_fvar(e)`; `v1, v2` closed `Nat` literals | `Nat.bitwise bne` via `WellFounded.fix` (**stuck**) |
| `Nat.shiftLeft` | 2 | `reduce_shift_left`: `a << b` (lines `677-686, 722`) | `!has_fvar(e)`; `b <= UINT_MAX`; `v1.size() + b/8 <= g_nat_max_size` | Structural recursion on shift count $b$ ($O(b)$) |
| `Nat.shiftRight` | 2 | `reduce_shift_right`: `a >> b` (lines `688-700, 723`) | `!has_fvar(e)`; `b <= UINT_MAX` | Structural recursion on shift count $b$ $\to$ `Nat.div 2` (**stuck if $b > 0$**) |

#### 2.2 The `has_fvar` GMP Bypass Hazard and `Nat.shiftRight` / `Nat.div` Stuckness on `let`-Bound States

Both the C++ kernel's `type_checker::reduce_nat`
(`src/kernel/type_checker.cpp:703`, `if (has_fvar(e)) return none_expr();`) and
the elaborator's `Lean.Meta.WHNF.withNatValue`
(`src/lean/Lean/Meta/WHNF.lean:994`,
`if !a.hasExprMVar && a.hasFVar then return none`) inspect the syntactic
`has_fvar` header flag on the unreduced `Nat` application **before** calling
`whnf` on its arguments (`source`).

When a proof shares intermediate cut-point states via `let st_k : State := ⟨...⟩`,
`infer_let` (`src/kernel/type_checker.cpp:208-230`) replaces `st_k` with a local
`FVar` (`ldecl`). If `stepInstr` or `evalStep` projects fields lazily out of `st_k`
(e.g., `st_k.r0` or `s.getReg src`), the resulting arithmetic application—such
as `Nat.xor (st_k.r0.toNat) (st_k.r2.toNat)` or
`Nat.shiftRight (s.getReg src).toNat 4` (`s.getReg src >>> 4`)—still contains the
un-unfolded `FVar` `st_k` inside its arguments, so `has_fvar(e) == true` (`source`).

This triggers a severe failure mode (`source`, `execution`):

1. Both `Meta.WHNF.reduceNat` and `type_checker::reduce_nat` return `none`
   immediately without calling `whnf` on the operands.
2. For `Nat.add` and `Nat.sub`, `whnf_core` delta-unfolds the definition to
   structural Peano recursion (`Nat.brecOn`), which still succeeds if the right
   operand is small, but degrades from $O(1)$ GMP to $O(b)$ unary `Nat.succ`
   steps.
3. For `Nat.xor`, `Nat.land`, `Nat.lor`, `Nat.mod`, and `Nat.div`, delta-unfolding
   exposes `WellFounded.fix`, which **cannot reduce** in `whnf` and leaves the
   term permanently stuck.
4. Even more subtly, `Nat.shiftRight` (`Init/Prelude.lean`) is defined by
   structural recursion on the shift amount (`shiftRight m (succ n) = shiftRight
   m n / 2`), so unfolding `Nat.shiftRight (s.getReg src).toNat 4` when
   `has_fvar == true` peels the shift count `4` into `((s.getReg
   src).toNat.shiftRight 3) / 2` (`Nat.div`), which still has `has_fvar == true`
   and gets permanently stuck on `WellFounded.fix`, causing `rfl` to fail in
   both elaboration and kernel replay (`execution`).

**The `State.casesOn` Unpacking Fix (`stepInstrStrict` / `evalStepStrict`):**
Wrapping `stepInstr` and `evalStep` in `State.casesOn s` at function entry
(`BenchmarkProofStrategies.lean:155-161`, `UnifiedEndToEndStack.lean:770-792`)
compiles to the eliminator `State.rec` with major premise `s`. In
`src/kernel/type_checker.cpp:462` (`reduce_rec`), the kernel **always calls
`whnf(major)` first**, which unfolds the `let`-bound `FVar` `s` to a closed
`State.mk` constructor (`has_fvar == false`, cached in `m_st->m_whnf`) *before*
the recursor rhs constructs any `Nat` operations on the unpacked fields (`source`,
`execution`).

#### 2.3 The `String.beq` Kernel Interpreter Bottleneck (`~11.5 ms` per Comparison) vs. Structural `List.Mem` and GMP `Nat.beq`

In `src/kernel/expr.cpp:427-446`, when a `String` literal (`lit_value::strVal`)
is matched against a constructor in `whnf_core` (`type_checker.cpp:504-505`) or
`reduce_rec` (`src/kernel/inductive.cpp:320-322`), `string_lit_to_constructor`
expands a $B$-byte string literal into a linked list of $B$ `UInt8.ofBitVec`
nodes wrapped in `ByteArray.mk (Array.mk [...])` (`source`). Because `String.beq`
has no native C++ reducer, evaluating `lookupFn crateProg fnName = some body` by
`rfl` forces the kernel interpreter to execute Lean 4.34.1's UTF-8
`Substring.beq` / `ByteArray` loop character-by-character across every preceding
function name in `crateProg` (`source`, `execution`):

| Callee Index in `crateProg` | Function Name (`String`) | `String.beq` Evaluations in `lookupFn` | Stage-2 Kernel Replay Time (`rfl`) |
| :---: | :--- | :---: | ---: |
| `0` | `"core::mem::size_of"` | `1` | `10.294 ms` |
| `1` | `"core::num::usize::checked_add"` | `2` | `24.244 ms` |
| `2` | `"core::num::NonZeroUsize::new"` | `3` | `35.851 ms` |
| `3` | `"core::option::Option::unwrap_or"` | `4` | `44.256 ms` |
| **Total (`0..3`)** | **4 `core` callees (`10` `String.beq` calls)** | **`10`** | **`114.645 ms` (`11.46 ms` / comparison)** |

By contrast (`source`, `execution`, `derived`):
- Proving function-table or specification-table membership via a structural
  `List.Mem` witness ($\underbrace{\texttt{.tail \_ (}\cdots}_{i\text{ times}}\texttt{ (.head \_))}$)
  checks propositional equality `fnName = fnName` via `is_def_eq`, which
  short-circuits immediately on $O(1)$ pointer/hash equality (`is_bi_equal` in
  `src/kernel/expr_eq_fn.cpp:21`) in **nanoseconds** without ever invoking
  `String.beq`.
- Alternatively, interning function identifiers to `Nat` (`FnId := Nat`) routes
  equality comparisons through `Nat.beq` in `type_checker::reduce_nat`
  (`src/kernel/type_checker.cpp:717`), which executes in C++ GMP in **`< 1 us`**
  (`>10,000x` faster than `String.beq`).

---

### Finding 3: Empirical Scaling across 6 Theorem Architectures (`Suite A` Straight-Line $N \in \{10..500\}$ and `Suite B` Chained CFG Diamonds $D \in \{2..10\}$, Multi-Call $K \in \{2..20\}$, and Symbolic/Bounded Loops) and Pre-Proved Side-Condition Reflection vs. `omega`/`decide` (`51.7x` Speedup)

`Basis: execution + derived`

#### 3.1 Suite A: Straight-Line 5-Instruction Checked-Arithmetic + Bitwise-Mix Idioms ($N \in \{10, 25, 50, 100, 250, 500\}$)

`support/BenchmarkProofStrategies.lean` and `support/run_suite_a.py` benchmark
six theorem architectures proving the identical `Trusted.VerifiedFrom prog_N
s0_N v_N` theorem over $N / 5$ repetitions of the 5-instruction checked-addition
and bitwise-mix idiom (`addCheckedImm .r0 .r0 imm`, `assertNotFlag`,
`xor .r1 .r0 .r2`, `shl .r2 .r1 3`, `add .r0 .r0 .r2`), with `Trusted` and
`Theory` precompiled in `baseEnv` (`support/suite_a_results.json`):

| $N$ | Architecture | Elab Time (ms) | Kernel Replay (ms) | Kernel Replay ($\mu$s) | `.olean` Size (Bytes) | `DECLS` | `DAG_NODES` | `TREE_NODES` | Replay Speedup vs. Arch 1b |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **10** | Arch 1a (Flat `Reach.step`) | 273.0 | 3.855 | 3,855 | 13,576 | 1 | 250 | 3,232 | 1.07x |
| **10** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 273.4 | 4.136 | 4,136 | 19,096 | 1 | 361 | 4,750 | 1.00x |
| **10** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 265.8 | 1.812 | 1,812 | 18,544 | 1 | 341 | 2,221 | 2.28x |
| **10** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 227.1 | **0.803** | **803** | 12,416 | 1 | 173 | 457 | **5.15x** |
| **10** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 221.2 | 1.446 | 1,446 | 5,912 | 1 | 40 | 52 | 2.86x |
| **10** | Arch 5 (Cut-Point Block `evalBlock_step`) | 229.7 | 2.345 | 2,345 | 12,456 | 1 | 170 | 377 | 1.76x |
| **10** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **221.1** | 1.153 | 1,153 | **5,632** | 1 | **33** | **44** | 3.59x |
| **50** | Arch 1a (Flat `Reach.step`) | 520.2 | 45.528 | 45,528 | 40,896 | 1 | 1,086 | 16,032 | 1.04x |
| **50** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 505.0 | 47.134 | 47,134 | 62,736 | 1 | 1,557 | 23,390 | 1.00x |
| **50** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 364.2 | 7.194 | 7,194 | 56,680 | 1 | 1,387 | 27,852 | 6.55x |
| **50** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 275.0 | **2.740** | **2,740** | 26,008 | 1 | 549 | 5,512 | **17.20x** |
| **50** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 234.5 | 5.676 | 5,676 | 5,912 | 1 | 40 | 52 | 8.30x |
| **50** | Arch 5 (Cut-Point Block `evalBlock_step`) | 302.1 | 9.801 | 9,801 | 27,400 | 1 | 570 | 5,102 | 4.81x |
| **50** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **232.3** | 4.324 | 4,324 | **5,632** | 1 | **33** | **44** | 10.90x |
| **100** | Arch 1a (Flat `Reach.step`) | 953.3 | 178.425 | 178,425 | 74,832 | 1 | 2,116 | 32,032 | 1.00x |
| **100** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 1,119.7 | 178.401 | 178,401 | 117,072 | 1 | 3,037 | 46,690 | 1.00x |
| **100** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 498.5 | 14.466 | 14,466 | 103,144 | 1 | 2,658 | 98,417 | 12.33x |
| **100** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 312.7 | **5.228** | **5,228** | 41,616 | 1 | 978 | 19,537 | **34.12x** |
| **100** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 272.7 | 10.988 | 10,988 | 5,920 | 1 | 40 | 52 | 16.24x |
| **100** | Arch 5 (Cut-Point Block `evalBlock_step`) | 379.7 | 19.318 | 19,318 | 45,008 | 1 | 1,039 | 18,702 | 9.23x |
| **100** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **266.5** | 8.157 | 8,157 | **5,640** | 1 | **33** | **44** | 21.87x |
| **250** | Arch 1a (Flat `Reach.step`) | 3,535.2 | 1,144.303 | 1,144,303 | 179,296 | 1 | 5,266 | 80,032 | 1.03x |
| **250** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 7,080.0 | 1,173.815 | 1,173,815 | 282,736 | 1 | 7,537 | 116,590 | 1.00x |
| **250** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 962.6 | 37.546 | 37,546 | 243,880 | 1 | 6,446 | 579,287 | 31.26x |
| **250** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 423.6 | **13.506** | **13,506** | 87,424 | 1 | 2,178 | 115,367 | **86.91x** |
| **250** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 328.5 | 27.934 | 27,934 | 5,920 | 1 | 40 | 52 | 42.02x |
| **250** | Arch 5 (Cut-Point Block `evalBlock_step`) | 586.7 | 50.413 | 50,413 | 96,112 | 1 | 2,337 | 113,317 | 23.28x |
| **250** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **313.0** | 19.896 | 19,896 | **5,640** | 1 | **33** | **44** | 59.00x |
| **500** | Arch 1a (Flat `Reach.step`) | 12,366.4 | 4,681.158 | 4,681,158 | 354,248 | 1 | 10,512 | 160,032 | 1.01x |
| **500** | Arch 1b (Cont-Lambda `safeAndEnsures_of_step`) | 55,796.6 | 4,715.554 | 4,715,554 | 559,688 | 1 | 15,033 | 233,090 | 1.00x |
| **500** | Arch 2 (`SuffixReach` + Contiguous `let`-Share) | 1,905.5 | 78.048 | 78,048 | 479,496 | 1 | 12,781 | 2,254,787 | 60.42x |
| **500** | Arch 3 (Fused 5-Instr Idiom `step_idiom5`) | 627.5 | **27.212** | **27,212** | 164,728 | 1 | 4,205 | 449,947 | **173.29x** |
| **500** | Arch 4 (Monolithic `BitVec 64` `evalProg_sound rfl`) | 423.5 | 55.694 | 55,694 | 5,920 | 1 | 40 | 52 | 84.67x |
| **500** | Arch 5 (Cut-Point Block `evalBlock_step`) | 957.4 | 103.992 | 103,992 | 182,712 | 1 | 4,542 | 445,822 | 45.35x |
| **500** | Arch 6 (`cv_trans` GMP `Nat` `evalCvProg_sound rfl`) | **383.7** | 40.446 | 40,446 | **5,640** | 1 | **33** | **44** | **116.59x** |

Key relationships from Suite A (`derived`):
- **Arch 6 (`cv_trans` `Nat`-domain reflection) vs. Arch 4 (`BitVec 64`
  reflection):** `BitVec 64` wraps `Fin (2^64)` (`Init/Prelude.lean:2379-2423`,
  `Init/Data/BitVec/Basic.lean:160-360`), so every `BitVec 64` operation
  allocates a `Fin.mk val isLt` node and computes `% 18446744073709551616` via
  GMP division (`Nat.mod`), and `is_def_eq` invokes proof irrelevance
  (`type_checker::is_def_eq_proof_irrel`, `src/kernel/type_checker.cpp:932-939`).
  In Arch 6 (`evalCvProg_sound`), `Theory.stepCvInstr` operates on flat `Nat`
  fields (`CvState`) and masks 64-bit results with
  `Nat.land _ 18446744073709551615` (`Nat.and_two_pow_sub_one_eq_mod`,
  `Init/Data/Nat/Bitwise/Lemmas.lean:537`), running **1.38x faster** in the
  kernel (`40.446 ms` vs. `55.694 ms` at $N = 500$) with a constant **33-node**
  proof DAG across all $N \in \{10..500\}$.
- **Why Arch 3 (`27.212 ms` at $N = 500$) beats even monolithic reflection on
  kernel replay time:** In `step_idiom5`, the 5-instruction idiom is
  symbolically composed once in `Theory.evalIdiom5` (`r0_4 := (r0 + imm) +
  (((r0 + imm) ^^^ r2) <<< 3)`), advancing `pc` by `+ 5` and skipping four
  intermediate `State` allocations and instruction dispatches per 5-instruction
  window.

#### 3.2 Suite B: Chained CFG Diamonds ($D \in \{2..10\}$), Multi-Call Programs ($K \in \{2..20\}$), and Bounded/Symbolic Loops (Arch 4 vs. Arch 5)

`support/run_suite_b.py` (`support/suite_b_results.json`) compares monolithic
reflection (Arch 4) against compositional cut-point reflection and summaries
(Arch 5):

| Workload | Parameter | Paths / Instrs | Architecture | Elab Time (ms) | Kernel Replay (ms) | Kernel Replay ($\mu$s) | `.olean` Size (Bytes) | `DAG_NODES` | `TREE_NODES` | Arch 5 Replay Speedup |
| :--- | ---: | ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Diamonds** | $D = 2$ | $2^2 = 4$ paths | Arch 4 ($2^D$ Path Split) | 233.3 | 4.837 | 4,837 | 13,056 | 186 | 550 | — |
| **Diamonds** | $D = 2$ | $2^2 = 4$ paths | Arch 5 ($O(D)$ `diamond_converge_step`) | 242.2 | **3.372** | **3,372** | **12,496** | **162** | **395** | **1.43x** |
| **Diamonds** | $D = 6$ | $2^6 = 64$ paths | Arch 4 ($2^D$ Path Split) | 720.3 | 122.465 | 122,465 | 97,216 | 2,474 | 12,598 | — |
| **Diamonds** | $D = 6$ | $2^6 = 64$ paths | Arch 5 ($O(D)$ `diamond_converge_step`) | **296.1** | **9.011** | **9,011** | **20,272** | **362** | **1,687** | **13.59x** |
| **Diamonds** | $D = 10$ | $2^{10} = 1,024$ paths | Arch 4 ($2^D$ Path Split) | 11,488.6 | 2,998.350 | 2,998,350 | 1,434,176 | 38,962 | 243,646 | — |
| **Diamonds** | $D = 10$ | $2^{10} = 1,024$ paths | Arch 5 ($O(D)$ `diamond_converge_step`) | **327.3** | **14.891** | **14,891** | **28,048** | **562** | **3,747** | **201.35x** |
| **Multi-Call** | $K = 2$ | 40 instrs | Arch 4 (Inlined Call `rfl`) | 247.0 | 4.496 | 4,496 | 5,944 | 40 | 52 | — |
| **Multi-Call** | $K = 2$ | 40 instrs | Arch 5 (`call_summary_sound`) | **223.1** | **0.248** | **248** | 7,160 | 60 | 98 | **18.13x** |
| **Multi-Call** | $K = 10$ | 200 instrs | Arch 4 (Inlined Call `rfl`) | 305.7 | 20.786 | 20,786 | 5,944 | 40 | 52 | — |
| **Multi-Call** | $K = 10$ | 200 instrs | Arch 5 (`call_summary_sound`) | **222.7** | **0.454** | **454** | 8,696 | 108 | 1,474 | **45.78x** |
| **Multi-Call** | $K = 20$ | 400 instrs | Arch 4 (Inlined Call `rfl`) | 377.2 | 41.406 | 41,406 | 5,944 | 40 | 52 | — |
| **Multi-Call** | $K = 20$ | 400 instrs | Arch 5 (`call_summary_sound`) | **221.9** | **0.668** | **668** | 10,616 | 168 | 5,714 | **61.99x** |
| **Loop** | $M = 10$ | 50 instrs | Arch 4 (Unrolled Loop `rfl`) | 262.6 | 7.534 | 7,534 | 5,944 | 40 | 52 | — |
| **Loop** | $M = 10$ | 50 instrs | Arch 5 (`loop_summary_sound`) | **213.3** | **0.127** | **127** | 7,128 | 48 | 68 | **59.32x** |
| **Loop** | $M = 100$ | 500 instrs | Arch 4 (Unrolled Loop `rfl`) | 527.5 | 76.251 | 76,251 | 5,944 | 40 | 52 | — |
| **Loop** | $M = 100$ | 500 instrs | Arch 5 (`loop_summary_sound`) | **218.4** | **0.122** | **122** | 7,128 | 48 | 68 | **625.01x** |
| **Loop (Symbolic)** | `m : Nat` | `5 * m` instrs | Arch 4 (Unrolled Loop `rfl`) | *Inexpressible* | *Inexpressible* | — | — | — | — | — |
| **Loop (Symbolic)** | `m : Nat` | `5 * m` instrs | Arch 5 (`loop_summary_sound`) | **217.4** | **0.134** | **134** | 8,528 | 68 | 208 | **$\infty$ (Symbolic)** |

#### 3.3 Pre-Proved `Theory` Side-Condition Reflection vs. `omega` and `decide`

`support/ProbeSideConditionReflection.lean` and `support/run_side_conditions.py`
(`support/side_condition_results.json`) evaluate 50 arithmetic and pointer
side-condition obligations (20 64-bit byte-interval disjointness obligations
`IntervalsDisjoint`, 15 power-of-two alignment round-up obligations
`AlignedRoundUp`, and 15 universally quantified symbolic-base slice subrange
obligations `SymbolicSubrange : ∀ base : Nat, base + off + sublen ≤ base +
totallen ∧ base ≤ base + off`):

| Side-Condition Strategy | Elab Time (ms) | Kernel Replay (ms) | Kernel Replay ($\mu$s) | `.olean` Size (Bytes) | `DECLS` | `DAG_NODES` | `TREE_NODES` | Replay Speedup vs. `omega` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **50 Decls: Standard `omega` Tactic** | 613.7 | 171.299 | 171,299 | 516,760 | 100 | 14,091 | 374,710 | 1.00x |
| **50 Decls: Hybrid `decide` (35) + `omega` (15)** | 483.3 | 70.361 | 70,361 | 272,728 | 65 | 7,139 | 199,040 | 2.43x |
| **50 Decls: Pre-Proved `Theory` Reflection (`rfl`)** | **327.5** | **3.312** | **3,312** | **62,856** | **50** | **1,006** | **5,500** | **51.72x** |
| **50 Bundled Intervals: `omega` Tactic** | 517.3 | 140.930 | 140,930 | 444,424 | 51 | 12,567 | 343,210 | 1.00x |
| **50 Bundled Intervals: `checkIntervalBatch_sound rfl`** | **259.8** | **3.527** | **3,527** | **3,872** | **1** | **12** | **14** | **39.96x** |

`omega` emits 50 auxiliary `_proof_i` declarations (`DECLS = 100`) and
constructs `14,091` DAG nodes (`374,710` tree nodes) of linear-combination
certificates (`171.299 ms` replay). `decide` cannot discharge universally
quantified `SymbolicSubrange` obligations and synthesizes `Decidable` typeclass
trees on ground obligations. Pre-proving `checkSymbolicSubrange_sound` (canceling
`∀ base : Nat` once in `Theory`) and expressing `checkIntervalDisjoint` and
`checkAlignedRoundUp` directly over C++ GMP primitives (`Nat.add`, `Nat.mod`,
`Nat.beq`, `Nat.ble`) reduces all 50 proofs to `rfl` (**`3.312 ms` total =
`66.2 us` per obligation**, a **51.72x speedup**), and bundling 50 intervals into
`checkIntervalBatch_sound rfl` shrinks the proof to **12 DAG nodes** and
**`3,872 B` `.olean`** (**114.8x smaller** than `omega`).

---

### Finding 4: Verified Lowering Passes (`Abstracts`) vs. Hint-Driven Translation Validators (`SymPlan` Witness Emission vs. In-Kernel `computePlan`), Pre-Composed Pass Pipelines (`Abstracts.comp`), and Cutpoint Loop Validators (`symbolicWhile_sound`)

`Basis: source + execution + derived`

#### 4.1 Total Verified Lowering Passes vs. Hint-Driven Translation Validators under `Language.Abstracts`

In `trusted/lean/Trusted/Refinement.lean:243-286` (`e6a0b2da5`),
`Language.Abstracts L_1 L_2 π_a s_1 s_2` is defined as `L_1.sem s_1 ≤ π_a (L_2.sem s_2)`,
and `Abstracts.verify` (`Trusted/Refinement.lean:264-275`) lifts any proof of
`L_2.sem s_2 ≤ sp_2` across `Abstracts` and `Compiles` to
`Verified L_1 L_tgt π_c s_1 t [π_a sp_2]`. `theory/Anneal/Refinement.lean:345-409`
proves that `Abstracts` forms a category (`Abstracts.refl`, `Abstracts.comp`,
`Abstracts.verify_chain`).

`support/ProbePreprovedPasses.lean` demonstrates that `Language.Abstracts`
supports four distinct points along the CompCert verified-pass /
translation-validation spectrum (`execution`, `derived`):

| Spectrum Point (`support/ProbePreprovedPasses.lean`) | Proof Architecture | `body4` (4 stmts) DAG / Tree / Replay | `body8` (8 stmts) DAG / Tree / Replay | `body12` (12 stmts) DAG / Tree / Replay |
| :--- | :--- | :--- | :--- | :--- |
| **Point 1: Per-Function Tactical Stepping** (`point1_tactical_bodyN`) | Steps through `evalBody` instruction-by-instruction (`SafeReturns.of_step`, matching `proof_gen.rs:429-484`) | `281` DAG / `6,209` tree / `7,328 us` | `473` DAG / `17,577` tree / `13,594 us` | `665` DAG / `34,705` tree / `21,328 us` |
| **Point 2: Unhinted Total Verified Pass** (`point2_lowerToPure_bodyN`) | Pre-proved `lowerToPure_sound`; Lean kernel runs both `computePlan` (CFG/NLL analysis) and `evalSym` via `rfl` (matching `FunctionalTranslation.lean:1821-1830`) | `60` DAG / `227` tree / `8,589 us` | `60` DAG / `227` tree / `15,402 us` | `60` DAG / `227` tree / `22,726 us` |
| **Point 3: Hint-Driven Translation Validator** (`point3_evalSym_bodyN`) | `anneal-rustc-capture` emits `planN : SymPlan` witness; Lean kernel checks `evalSym planN bodyN = some spec` (`rfl`) without running `computePlan` | **`59` DAG / `223` tree / `6,288 us`** | **`59` DAG / `223` tree / `11,632 us`** | **`59` DAG / `223` tree / `17,221 us`** |
| **Point 4a: Per-Function Pass Chaining** (`point4_unchained_body12`) | Chains `MirRaw → MirNorm → PureLang` per function in `Proof.lean` via `pass_trans` | — | — | `53` DAG / `169` tree / `262 us` |
| **Point 4b: Pre-Composed Pipeline** (`point4_preproved_pipeline_body12`) | Pre-composes `MirRaw → PureLang` once in `theory/Anneal/` (`pipeline_sound`) | — | — | **`5` DAG / `9` tree / `67 us` (`3.91x` faster)** |

Key conclusions (`derived`):
- **Why Point 3 (Hint-Driven Validation) beats Point 2 (Unhinted `lowerToPure`):**
  In `skeleton` (`theory/Anneal/FunctionalTranslation.lean:773-845, 1821-1830` @
  `e75556f57`), `lowerToPure` executes `computePlan` inside `rfl` during kernel
  typechecking, making Point 2 **7%–17% slower** than Point 1 tactical stepping
  on `body4..body12`. Having `anneal-rustc-capture` compute the `TransPlan` /
  `SymPlan` witness in native Rust and pass it as a hint to `evalSym_sound`
  (Point 3) eliminates in-kernel CFG discovery, cutting kernel replay time by
  **24.2%–26.3%** (`17,221 us` vs. `22,726 us` on `body12`) while shrinking
  proof DAGs by **11.3x** (`59` vs. `665`) and unshared trees by **155.6x**
  (`223` vs. `34,705`) compared to Point 1.
- **General Cutpoint Loop Validator (`symbolicWhile_sound`):**
  In `skeleton` (`FunctionalTranslation.lean:7510-8009`), verifying the
  unbounded symbolic loop `count_up` (`while i < n { i += 1 }`) requires ~500
  lines of bespoke manual proof. In `support/ProbePreprovedPasses.lean:395-507`,
  proving a single parameterized loop-invariant validator `symbolicWhile_sound`
  in `theory/Anneal/` discharges the symbolic loop `symCount_verified`
  (`∀ n : Nat`) in **18 lines** (`1,123` DAG nodes, `6,521 us` kernel replay)
  and bounded loops (`loopSum_verified_by_rfl`) via `rfl` in **`40` DAG nodes**
  (`195` tree nodes, `21,177 us`).

---

### Finding 5: Pre-Proved `core` / Intrinsic / Trait-Method `Call1Summary` Schemas, Fixing the `MirLang.sem` Single-Entry Call-Table Bug (`Trusted/MirSemantics.lean:1794`), and Eliminating the $O(3^K)$ `{ s with ... }` Record-Update Tree Explosion (`1,800.8x` Reduction via Flat Constructor Tuples)

`Basis: source + execution + derived`

#### 5.1 Semantic Defect in `Trusted/MirSemantics.lean:1794` (`MirLang.sem` Hardcodes a Single-Entry Function Table)

In `trusted/lean/Trusted/MirSemantics.lean:1554-1607` (`e6a0b2da5`),
`evalTerminator` evaluates `Terminator.call func args destination target` by
looking up `fnName` via `lookupFn prog fnName`. If `lookupFn prog fnName = none`,
evaluation returns `StepOut.stuck`, which violates `SafeReaches` / `runsTo`
safety (`source`).

However, in `Trusted/MirSemantics.lean:1787-1823`, `MirLang` defines
`Prog := MirBody` and constructs a single-entry `MirProg` inside `MirLang.sem`:

```lean
let prog : MirProg := { fns := [⟨"__entry", body⟩], statics := [] }
```

Because `prog.fns` contains only `"__entry"`, **every `Terminator.call` in `body`
to any function `fnName ≠ "__entry"` evaluates `lookupFn prog fnName = none` and
immediately steps to `StepOut.stuck`** (`source`, `derived`). In `skeleton`
(`FunctionalTranslation.lean:8088-8176`), the 2-function test `double_inc` only
succeeded because it proved `SafeReaches` over a custom 2-function `MirProg`
(`doubleIncProg`) outside `MirLang.sem`.

**5-Line Fix Verified in `support/UnifiedEndToEndStack.lean:397-478`:**
Changing `MirLang.Prog` from `MirBody` to `MirProg × MirBody` (the crate's
function table paired with the entry function body, both finite inductive data
types with `DecidableEq`) allows `evalStep p.1 q s` to resolve every
interprocedural call through `lookupFn p.1 fnName` directly inside `MirLang.sem`
and `Trusted.CrateTheorem` (verified by `canary4_pos_fixed_mirlang_call` and
contrasted with `canary4_neg_broken_mirlang_call_traps`, `execution`).

#### 5.2 Eliminating the $O(3^K)$ / $O(6^K)$ Record-Update (`{ s with ... }`) Tree Explosion via Flat Constructor Tuples

`support/ProbePreprovedSummaries.lean` uncovers two severe expression-tree
blowups when chaining small-step MIR transitions across $K$ calls:

1. **Unnormalized Intermediate State Closures ($O(4^K)$ Blowup):**
   Chaining `SafeReaches.of_step rfl ?_` without normalizing intermediate local
   lists to concrete values (`vOut : Val`) duplicates unreduced `updateLocal` /
   `List.set` redexes across steps: at $K = 2$ calls (`naive_inline_caller2`),
   the unshared tree size (`Expr.sizeWithoutSharing`) reaches **`36,289,487`
   nodes** (`446` DAG nodes), and at $K = 5, 10$ kernel typechecking exceeds 30
   seconds (`execution`).
2. **Lean Record-Update Syntax (`{ s with ... }`) $O(3^K)$ / $O(6^K)$ Tree
   Blowup:**
   Even when `vOut` is normalized at every call (`summary_caller10`), writing a
   step or summary lemma's post-state as
   `{ s with locals := updateLocal s.locals dst vOut, blk := retBlk, stmtIdx := 0 }`
   desugars to:
   ```lean
   MirState.mk s.curBody (updateLocal s.locals dst vOut) retBlk 0 s.stack
   ```
   Because `s` is referenced **3 times** (`s.curBody`, `s.locals`, `s.stack`) in
   a 5-field state (or **6 times** in an 8-field register state
   `State.mk s.curBody (s.pc + 1) vOut s.r1 s.r2 s.r3 false s.stack` in
   `UnifiedEndToEndStack.lean:628-633`), chaining $K$ steps multiplies the
   number of unshared paths to the initial state by $3^K$ (or $6^K$). At
   $K = 10$ calls (`summary_caller10`), `DAG_NODES` is `916`, but unshared
   `TREE_NODES` explodes to **`17,134,141`** (`execution`).
   Stating step and summary lemmas over **explicit flat constructor tuples**
   `⟨curBody, locals, blk, stmtIdx, stack⟩` (`call1_summary_flat_sound` in
   `support/ProbePreprovedSummaries.lean:243-289`) references each field
   **once**, collapsing `TREE_NODES` at $K = 10$ from `17,134,141` to **`9,515`
   (a 1,800.8x reduction)**:

| Benchmark ($K$ Calls, `support/ProbePreprovedSummaries.lean`) | Strategy | `DAG_NODES` (`numObjs`) | `TREE_NODES` (`sizeWithoutSharing`) | Kernel Replay Avg (`10` runs) | Speedup vs. Inline |
| :--- | :--- | ---: | ---: | ---: | ---: |
| `naive_inline_caller2` ($K = 2$) | Unnormalized inline `SafeReaches.of_step rfl ?_` (8 steps/call) | `446` | `36,289,487` | `5,736 us` | — ($>30\text{s}$ at $K \ge 5$) |
| `inline_caller2` ($K = 2$) | Value-normalized inline stepping (`inlineStepCall8`, 8 steps/call) | `280` | `3,157` | `6,035 us` | `1.00x` |
| `summary_caller2` ($K = 2$) | Pre-proved `call1_summary_sound` (`{ s with ... }` post-state) | `294` | `3,021` | `1,642 us` | `3.68x` |
| **`summary_flat_caller2` ($K = 2$)** | **Pre-proved `call1_summary_flat_sound` (flat constructor tuple)** | **`272`** | **`1,301`** | **`1,594 us`** | **`3.79x`** |
| `inline_caller5` ($K = 5$) | Value-normalized inline stepping (40 steps total) | `543` | `9,759` | `13,582 us` | `1.00x` |
| `summary_caller5` ($K = 5$) | Pre-proved `call1_summary_sound` (`{ s with ... }` post-state) | `529` | `71,835` | `3,357 us` | `4.05x` |
| **`summary_flat_caller5` ($K = 5$)** | **Pre-proved `call1_summary_flat_sound` (flat constructor tuple)** | **`477`** | **`3,771`** | **`3,194 us`** | **`4.25x`** |
| `inline_caller10` ($K = 10$) | Value-normalized inline stepping (80 steps total) | `999` | `25,485` | `29,765 us` | `1.00x` |
| `summary_caller10` ($K = 10$) | Pre-proved `call1_summary_sound` (`{ s with ... }` post-state) | `916` | `17,134,141` | `6,626 us` | `4.49x` |
| **`summary_flat_caller10` ($K = 10$)** | **Pre-proved `call1_summary_flat_sound` (flat constructor tuple)** | **`814`** | **`9,515`** | **`6,393 us`** | **`4.66x`** |
| **`summary_caller2_polymorphic` ($K = 2$)** | **Polymorphic summary quantified over `(ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) (x : Nat)`** | **`307`** | **`3,823`** | **`1,656 us`** | **`3.64x`** |

#### 5.3 Top-10 `core` / Intrinsic Summary Schemas Verified in `support/ProbePreprovedSummaries.lean`

`support/ProbePreprovedSummaries.lean:295-387` encodes and verifies 10 polymorphic
`Call1Summary` schemas covering the primary `core` helpers invoked across
`google/zerocopy` (`1897ac488`):
1. `core::option::Option::<T>::unwrap_or` (`optionUnwrapOrSummary_sound`)
2. `core::option::Option::<T>::is_some` / `is_none` (`optionIsSomeSummary_sound`)
3. `core::num::NonZero::<T>::new` (`nonZeroNewSummary_sound`, parameterized by
   `adtInv : AdtInv`)
4. `usize::checked_add` / `checked_mul` (`checkedAddSummary_sound`,
   parameterized by `maxUsize : Nat`)
5. `usize::wrapping_add` / `wrapping_sub` (`wrappingAddSummary_sound`,
   parameterized by `modulus : Nat`)
6. `core::mem::size_of::<T>()` (`sizeOfSummary_sound`, parameterized by
   `(layout : LayoutEnv) (ty : Ty)`)
7. `core::mem::align_of::<T>()` (`alignOfSummary_sound`, parameterized by
   `(layout : LayoutEnv) (ty : Ty)`)
8. `core::mem::transmute_copy::<Src, Dst>` (`transmuteCopySummary_sound`,
   parameterized by `LayoutEnv`, `AdtInv`, `Src`, `Dst`)
9. `<[T]>::len` / `core::ptr::metadata` (`sliceLenSummary_sound`)
10. `<[T]>::get` / `SliceIndex::get` (`sliceGetSummary_sound`)

---

### Finding 6: Source-Level `ShardCert` Contract Export, Eliminating the $O(N^2 \cdot |\text{AST}|)$ `by decide` TCB-Lookup Bottleneck via Structural `.tail`/`.head` Witnesses, and the Unified 5-Stage End-to-End Crate Verification Benchmark (`Stage 0`..`Stage 4`: `3,001.5x` Incremental Replay Speedup) with Positive & Negative Soundness Canaries

`Basis: source + execution + derived`

#### 6.1 Phase-2 Replay Audit Bottleneck in `trusted/audit/TrustedBoundary.lean:906-972`

In `trusted/audit/src/lib.rs:1676-1767` (`e6a0b2da5`), `load_or_build_verify_prefix`
compiles `Trusted.*` and `Anneal.*` into a hash-verified `.olean` prefix cache
and audits that prefix via `audit_prefix_environment`. However, when
`verify_crate_proof` (`lib.rs:1918-1928`) invokes `anneal-BoundaryCheck` on a
crate, `trusted/audit/TrustedBoundary.lean:906-912, 963-975` sets:

```lean
let allowedAll := foundation ++ trusted ++ theory ++ crateModules
let env ← importEnv j allowedAll
...
let base ← importEnv j foundation
let _ ← base.toKernelEnv.replay locals
```

Because `locals` includes every constant outside `foundation` (`Init`, `Std`,
`Lean`), **`base.toKernelEnv.replay locals` re-typechecks every constant in
`Trusted.*` and `Anneal.*` from scratch on every `cargo anneal verify` run**
(`source`). Moving hash-verified `trusted ++ theory` (and unchanged per-function
shard modules) into `base` during `hasCrate = true` runs restricts Phase-2
kernel replay strictly to the newly compiled crate or shard modules (`derived`).

#### 6.2 Source-Level `ShardCert` Export and Eliminating the $O(N^2 \cdot |\text{AST}|)$ `by decide` TCB-Lookup Bottleneck

In `trusted/lean/Trusted/Refinement.lean:456-472`, `VerificationResult c`
(`CrateTheorem c`) guarantees **target-level** refinement
`L_tgt.sem t_prog ≤ π_c sp`. Because `π_c` is not injective, callers verified in
`MirLang` cannot invert `CrateTheorem c` to recover the **source-level**
refinement `L_src.sem f.prog ≤ sp`. Defining `ShardCert c f` in
`theory/Anneal/` (`support/ProbeShardedCrateProof.lean:184-245`):

```lean
structure ShardCert (c : Crate L_src L_tgt π_c) (f : FunctionSpec L_src) : Prop where
  has_tcb : TcbAssumption.rustcLowering f.name f.prog ∈ c.tcb
  all_verified : ∀ sp, sp ∈ f.specs → L_src.sem f.prog ≤ sp ∧ f.specWellFormed sp
```

simultaneously exports `shard_i.all_verified` (`L_src.sem f_i.prog ≤ sp`) for
intra-crate and cross-crate callers and aggregates `shard_0 .. shard_{N-1}` into
`CrateTheorem c` via `verify_crate_of_shards` (`execution`).

Furthermore, discharging `has_tcb : TcbAssumption.rustcLowering f_i.name f_i.prog
∈ c.tcb` via `by decide` (as in `FunctionalTranslation.lean:8275-8293`) forces
the kernel's `Decidable.decide` reducer to compare `(f_i.name, f_i.prog)`
against all $i$ preceding entries in WHNF ($O(N^2 \cdot |\text{AST}|)$ across an
$N$-function crate). Emitting the structural `List.Mem` proof term
$\underbrace{\texttt{.tail \_ (}\cdots}_{i\text{ times}}\texttt{ (.head \_))}$
from `proof_gen.rs` eliminates kernel `DecidableEq` reduction on function names
and ASTs, speeding up 1-shard incremental replay on a 20-function crate
(`support/ProbeShardedCrateProof.lean`) by **32.4x** (`1,116 us` vs.
`36,168 us`) and **343.2x** vs. full un-cached replay (`383,030 us`):

| Replay Regime (`support/ProbeShardedCrateProof.lean`, 20-Function Crate) | Replayed Constants (`locals`) | `DAG_NODES` | `TREE_NODES` | Kernel Replay Avg (`20` runs) | Speedup vs. Regime 1 |
| :--- | :--- | ---: | ---: | ---: | ---: |
| **Regime 1: Un-cached Theory + All 20 Shards + Root** | `31` decls | `7,208` | `28,390` | `383,030 us` (`383.0 ms`) | `1.00x` |
| **Regime 2: Cached Theory in `base`, 20 Shards + Root (`by decide`)** | `21` decls | `2,570` | `10,625` | `375,035 us` (`375.0 ms`) | `1.02x` |
| **Regime 3: Cached Theory + 19 Shards in `base`, 1 Shard (`by decide`) + Root** | `2` decls | `309` | `2,816` | `36,168 us` (`36.2 ms`) | `10.59x` |
| **Regime 3b: Cached Theory + 19 Shards in `base`, 1 Structural Shard (`.tail/.head`) + Root** | `2` decls | `461` | `11,200` | **`1,116 us` (`1.12 ms`)** | **`343.22x`** |
| **Regime 4: Root Aggregator `verify_crate20` Alone (All 20 Shards in `base`)** | `1` decl | `190` | `2,405` | **`266 us` (`0.27 ms`)** | **`1,439.96x`** |
| **Regime 5: Cross-Crate Downstream Consumer (`downstream_uses_shard_19`)** | `1` decl | `67` | `157` | **`131 us` (`0.13 ms`)** | **`2,923.89x`** |

#### 6.3 Unified 5-Stage End-to-End Benchmark (`Stage 0`..`Stage 4`) over a 10-Function Crate

`support/UnifiedEndToEndStack.lean` and `support/run_unified_benchmark.py`
(`support/unified_benchmark_results.json`) integrate every mechanism above into
a single zero-`sorry`, zero-axiom stack over a 10-function crate (`crate10`)
with 20 side conditions:
- `f_0..f_3`: four 10-instruction `core` helpers (`size_of`, `checked_add`,
  `NonZeroUsize::new`, `Option::unwrap_or`).
- `f_4, f_5`: two multi-call functions (`validate_cast_layout`,
  `try_cast_into_header`) each executing 4 interprocedural calls + 4
  intra-procedural steps (`52` dynamic transitions each).
- `f_6`: 100-instruction checked-arithmetic + bitwise-mix block
  (`compute_padding_and_stride`).
- `f_7`: 100-instruction idiom-heavy block (`align_up_mask_mix`, $20 \times 5$
  instructions).
- `f_8`: $D = 5$ chained CFG diamonds (`check_enum_discriminants`, $30$
  instructions, $2^5 = 32$ paths).
- `f_9`: $M = 20$ counted loop (`validate_slice_elements_loop`, $100$
  instructions).

| Stage | Architecture & Active Optimizations | Elab Time (ms) | Elab Speedup vs. S0 | Stage-2 Kernel Replay (ms) | Replay Speedup vs. S0 | Replayed `.olean` Bytes | `.olean` Reduction vs. S0 | Replayed `DECLS` | Replayed `DAG_NODES` | `DAG` Reduction vs. S0 | Replayed `TREE_NODES` | `TREE` Reduction vs. S0 |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Stage 0** | **Baseline:** `Theory` in `locals` + continuation lambdas + `{ s with ... }` record updates + inlined calls + `omega` + `by decide` TCB lookup | `18,750.3` | `1.00x` | `5,042.587` | `1.00x` | `5,148,336` | `1.00x` | `906` | `86,385` | `1.00x` | `51,614,627` | `1.00x` |
| **Stage 1** | **+ Two-Stage Pre-Audited `Theory` in `base`:** `UnifiedEndToEndStack` in `base`; only `CrateMir + Stage0_Proof` replayed | `16,131.7` | `1.16x` | `4,787.113` | `1.05x` | `1,729,760` | `2.98x` | `151` | `33,489` | `2.58x` | `50,745,839` | `1.02x` |
| **Stage 2** | **+ Flat-Tuple & Structural Proof Hygiene:** `SuffixReach` with `State.casesOn`, contiguous `let st_k` sharing, structural `.tail`/`.head` TCB witnesses, and `checkSideCondBatch_sound rfl` | `5,593.1` | `3.35x` | `512.698` | `9.84x` | `1,301,592` | `3.96x` | `101` | `22,952` | `3.76x` | `567,704` | `90.92x` |
| **Stage 3** | **+ 3-Layer Hybrid `Theory` Validators:** `evalCvProg_sound` (`cv_trans`), `evalIdiomPlan_sound`, `diamond_converge_step`, `CalleeSummary` (`call_summary_flat_step`), and `loop_summary_sound` | `813.8` | `23.04x` | `157.056` | `32.11x` | `581,048` | `8.86x` | `73` | `2,708` | `31.90x` | `51,858` | `995.31x` |
| **Stage 4** | **+ Per-Function `ShardCert` Incremental Sharding:** 9/10 unchanged shards in `base`; re-verifying 1 modified shard (`Shard 9` loop) + `Stage4_Root` (`CrateTheorem`) | `472.7` | `39.67x` | **`1.680`** | **`3,001.54x`** | **`30,008`** | **`171.57x`** | **`3`** | **`384`** | **`224.96x`** | **`6,714`** | **`7,687.61x`** |

Across all 10 individual shards in `Stage 4` (`Stage4_Base_i -> Stage4_Root`),
incremental Stage-2 kernel replay ranges from **`1.680 ms` (`3,001.54x` speedup)
to `11.279 ms` (`447.08x` speedup)**, and the sum of all 10 shards' replay times
is **`43.716 ms` (`115.35x` faster than Stage 0)**:

| Modified Shard (`i`) | Function Name | Workload Archetype | Shard + Root Elab (ms) | Stage-2 Kernel Replay (ms) | Replay Speedup vs. Stage 0 | Replayed `.olean` Bytes | Replayed `DECLS` | Replayed `DAG_NODES` | Replayed `TREE_NODES` |
| :---: | :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Shard 0** | `core::mem::size_of` | 10-instr `core` helper (`cv_trans`) | `491.8` | `1.983` | `2,542.91x` | `26,640` | `3` | `318` | `2,418` |
| **Shard 1** | `core::num::usize::checked_add` | 10-instr `core` helper (`cv_trans`) | `459.1` | `1.966` | `2,564.90x` | `26,904` | `3` | `324` | `3,198` |
| **Shard 2** | `core::num::NonZeroUsize::new` | 10-instr `core` helper (`cv_trans`) | `459.2` | `2.001` | `2,520.03x` | `27,000` | `3` | `327` | `3,900` |
| **Shard 3** | `core::option::Option::unwrap_or` | 10-instr `core` helper (`cv_trans`) | `459.0` | `1.972` | `2,557.09x` | `27,096` | `3` | `330` | `4,524` |
| **Shard 4** | `zerocopy::util::validate_cast_layout` | 4-call caller (`Call1Summary`) | `506.9` | `3.195` | `1,578.27x` | `41,960` | `3` | `682` | `7,361` |
| **Shard 5** | `zerocopy::ptr::try_cast_into_header` | 4-call caller (`Call1Summary`) | `515.5` | `3.133` | `1,609.51x` | `42,224` | `3` | `690` | `7,829` |
| **Shard 6** | `zerocopy::layout::compute_padding_and_stride` | 100-instr block (`cv_trans`) | `512.5` | `9.414` | `535.65x` | `27,384` | `3` | `339` | `5,928` |
| **Shard 7** | `zerocopy::layout::align_up_mask_mix` | 100-instr block (`IdiomPlan`) | `517.2` | `7.093` | `710.92x` | `31,456` | `3` | `416` | `6,411` |
| **Shard 8** | `zerocopy::validity::check_enum_discriminants` | $D = 5$ diamonds (`diamond_converge_step`) | `545.3` | `11.279` | `447.08x` | `38,688` | `3` | `602` | `7,686` |
| **Shard 9** | `zerocopy::slice::validate_slice_elements_loop` | $M = 20$ loop (`loop_summary_sound`) | `472.7` | **`1.680`** | **`3,001.54x`** | `30,008` | `3` | `384` | `6,714` |

#### 6.4 Positive Boundary Canaries and Negative Soundness Canaries

`support/UnifiedEndToEndStack.lean` (`lines 1665-1765`) and
`support/run_unified_benchmark.py` (`lines 1059-1140`) verify 5 positive
boundary canaries and 5 negative soundness canaries (`execution`):

| Canary ID | Positive Boundary Canary (`UnifiedEndToEndStack.lean`, Passes) | Negative Soundness Canary (`UnifiedEndToEndStack.lean` + Standalone `.lean` File, Rejected with `rc = 1`) |
| :--- | :--- | :--- |
| **Canary 1 (`cv_trans` Overflow)** | `canary1_pos_boundary_cv`: `r0 = 7`, `imm = 2^64 - 1 - 7 = 0xFFFFFFFFFFFFFFF8#64` (`r0 + imm = 2^64 - 1`, max valid 64-bit unsigned sum) | `canary1_neg_overflow_blocked` / `NegativeCanary1_Overflow.lean` (`220.08 ms`): `r0 = 7`, `imm = 2^64 - 7 = 0xFFFFFFFFFFFFFFF9#64` (`r0 + imm = 2^64` overflows by 1 before `.assertNotFlag`; `evalCvProg` returns `none`) |
| **Canary 2 (Side Conditions)** | `canary2_pos_abutting_intervals`: abutting byte intervals `[1000, 1064)` and `[1064, 1128)` (`p1 + n1 = p2`) and exact alignment `off = 64, align = 16, out = 64` | `canary2_neg_overlap_rejected` / `NegativeCanary2_SideCondOverlap.lean` (`210.67 ms`): intervals `[100, 116)` and `[115, 131)` overlapping by 1 byte (`checkSideCondBatch` returns `false`) |
| **Canary 3 (`CalleeSummary`)** | `canary3_pos_callee_summary`: valid interprocedural call to `"core::mem::size_of"` with `r0 = 7#64` | `canary3_neg_callee_precond_violated` / `NegativeCanary3_CalleePrecond.lean` (`283.00 ms`): call to `"core::num::usize::checked_add"` (`imm1 = 4#64`) with `r0 = 0xFFFFFFFFFFFFFFFD#64` (`r0 + 4` overflows; `mkCoreCalleeSpec` returns `none`) |
| **Canary 4 (`MirLang` Call Table)** | `canary4_pos_fixed_mirlang_call`: interprocedural call to `"core::mem::size_of"` verified under fixed `MirLang` (`Prog := MirProg × List Instr`) | `canary4_neg_broken_mirlang_call_traps` / `NegativeCanary4_BrokenMirLangCall.lean` (`283.23 ms`): calling `"core::mem::size_of"` under legacy single-entry `MirLangBroken` (`fns := [("__entry", body)]`) traps in 1 step |
| **Canary 5 (Diamond Join)** | `canary5_pos_diamond_converge`: symbolic diamond converging to `r0 = 30#64, r1 = 0#64, r2 = 0#64` on both arms | `canary5_neg_diamond_arms_diverge` / `NegativeCanary5_DivergentDiamond.lean` (`259.79 ms`): diamond selecting `10#64` on true arm and `11#64` on false arm rejected at second `rfl` (`11#64 ≠ 10#64`) |

## Boundaries

1. **`trusted/` vs. `theory/` Trust Boundary (`known not to apply` to
   `trusted/lean/`):**
   None of the pre-proved theorem architectures (`SuffixReach`, `step_idiom5`,
   `evalProg_sound`, `evalCvProg_sound`, `diamond_converge_step`,
   `call_summary_flat_step`, `loop_summary_sound`), side-condition reflection
   checkers (`checkSideCondBatch_sound`), hint-driven `Abstracts` validators
   (`evalSym_sound`), or shard aggregators (`ShardCert`,
   `verify_crate_of_shards`) belong in `trusted/lean/`. They reside strictly in
   `theory/Anneal/`. Only two small changes touch `trusted/`:
   - Updating `MirLang.Prog` in `trusted/lean/Trusted/MirSemantics.lean:1787-1796`
     from `MirBody` to carry the crate's `MirProg` call table alongside the
     entry `MirBody` so interprocedural calls do not trap on `"__entry"` lookup.
   - Updating `trusted/audit/TrustedBoundary.lean:906-972` so Phase-2 kernel
     replay includes hash-verified `trusted ++ theory` (and unchanged shard
     modules) in `base`.
2. **Attractive Stronger Conclusions Not Established by the Evidence:**
   - **Monolithic `rfl` reflection (`Arch 4` / `Arch 6`) does not generalize to
     branching or looping functions without cut-point decomposition (`known not
     to apply`):** On $D = 10$ chained diamonds ($2^{10} = 1,024$ paths),
     monolithic path-splitting reflection (`Arch 4`) degrades to `2,998.350 ms`
     kernel replay and `38,962` DAG nodes (`201.35x` slower than `Arch 5`
     cut-point convergence), and monolithic `rfl` is **unsupported** for
     symbolic loop trip counts (`m : Nat`).
   - **Two-stage prefix caching (`Stage 1`) alone does not make baseline
     small-step proofs fast (`known not to apply`):** Moving `Theory` into
     `base` while keeping continuation lambdas, `{ s with ... }` record updates,
     `omega`, and `by decide` reduces 10-function crate kernel replay by only
     `1.05x` (`5,042.587 ms` $\to$ `4,787.113 ms`) because the crate proof
     itself still contains `50,745,839` unshared tree nodes.
   - **`native_decide` / `Lean.ofReduceBool` is `unsupported` by Anneal's
     soundness policy:** Although Lean 4 provides `native_decide`, it trusts the
     compiled native code generator and `lean_eval` runtime, which violates
     Anneal's kernel-only verification requirement (`PRINCIPLES.md` and
     `TrustedBoundary.lean`). All reflection results in this report use standard
     kernel `rfl` (`type_checker::is_def_eq` and `type_checker::reduce_nat`).
3. **Unexamined Scope (`not examined`):**
   - Floating-point MIR operations, inline assembly, concurrency primitives, and
     heap-allocating dynamic trait objects (`dyn Trait`) were **not examined**
     in the benchmark suites.
   - Multi-threaded C++ kernel replay across independent shard processes was
     **not examined**; all `Stage 4` measurements are single-threaded sequential
     replay latencies.

## Evidence

### Primary Repository and Source Coordinates

| Role | Repository & Revision | File Path & Lines / Symbols | What It Establishes |
| :--- | :--- | :--- | :--- |
| `source` | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `src/kernel/expr.h:99-145, 386-388`, `src/kernel/expr.cpp:42-55, 105-126, 427-446` | `expr_cell` layout (`m_rc`, `m_data`, `has_fvar`), absence of hash-consing, `is_likely_unshared` (`m_rc == 1`), and `string_lit_to_constructor` $O(B)$ list expansion. |
| `source` | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `src/kernel/type_checker.h:32-44`, `src/kernel/type_checker.cpp:129-142, 174-187, 208-230, 250-260, 447-462, 492-549, 643-773, 932-977` | Kernel caches (`m_infer_type`, `m_whnf_core`, `m_whnf`, `m_success`, `m_failure`), `infer_lambda` vs. `infer_let`, `reduce_rec` calling `whnf(major)`, and `reduce_nat` (`if (has_fvar(e)) return none_expr();` at line `703`). |
| `source` | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `src/kernel/instantiate.cpp:15-61`, `src/kernel/replace_fn.cpp:16-59`, `src/kernel/expr_eq_fn.cpp:17-58`, `src/kernel/expr_maps.h:15-17`, `src/kernel/inductive.cpp:320-322` | `instantiate_rev` allocation of `m_rc == 1` nodes, `replace_rec_fn::m_cache` bypass when `is_likely_unshared(e)`, and `is_bi_equal` pointer-equality fast path vs. recursive tree comparison. |
| `source` | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `src/lean/Lean/Meta/WHNF.lean:994`, `src/lean/Init/Prelude.lean:2379-2423`, `src/lean/Init/Data/BitVec/Basic.lean:160-360`, `src/lean/Init/Data/Nat/Bitwise/Lemmas.lean:537` | Elaborator `withNatValue` `hasFVar` guard, `Fin`/`BitVec` representation, and `Nat.and_two_pow_sub_one_eq_mod`. |
| `normative` | `joshlf/anneal` @ `24367bd1a8c784f2578535954f9915e24894a56f` | `PRINCIPLES.md`, `AGENTS.md` | Trust boundary between `trusted/` and `theory/` and kernel-only verification contract. |
| `source` | `joshlf/anneal` @ `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` | `trusted/lean/Trusted/Refinement.lean:243-286, 456-472`, `theory/Anneal/Refinement.lean:345-410` | `Language.Abstracts`, `Abstracts.verify`, `Abstracts.comp`, `Crate`, `TcbAssumption`, and `VerificationResult` (`CrateTheorem`). |
| `source` | `joshlf/anneal` @ `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` | `trusted/lean/Trusted/MirSemantics.lean:1487-1607, 1787-1823`, `theory/Anneal/MirLemmas.lean:58-74`, `trusted/rustc-capture/src/proof_gen.rs:413-510` | `evalTerminator` (`Terminator.call`), `MirLang.sem` single-entry `fns := [⟨"__entry", body⟩]` bug at line `1794`, and `reachesPrefix_safeAndEnsures_of_step` continuation-lambda chains. |
| `source` | `joshlf/anneal` @ `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` | `trusted/audit/TrustedBoundary.lean:880-975`, `trusted/audit/src/lib.rs:1676-1929` | Prefix `.olean` cache in `lib.rs` vs. `TrustedBoundary.lean:971-972` replaying all of `trusted ++ theory ++ crateModules` on top of `foundation`. |
| `source` | `joshlf/anneal` @ `e75556f5767705404404c0675c6d2d9bcee41d6f` | `theory/Anneal/FunctionalTranslation.lean:773-845, 1821-1830, 7510-8295` | `computePlan`, `evalPlan`, `lowerToPure_sound`, manual `count_up` loop proof, and `by decide` TCB membership in `verify_single_fn_crate` / `verify_two_fn_crate`. |

### Preserved Self-Contained Package Artifacts (`support/`)

All benchmark modules, probes, runner scripts, and raw JSON outputs are
preserved in `support/` (observed `2026-10-31`):

| Preserved File (`support/`) | Evidence Role | SHA-256 Digest | Description |
| :--- | :--- | :--- | :--- |
| `support/UnifiedEndToEndStack.lean` | `execution` | `5cb80e03825037ecc1177ce6cf26d4bae9c63017434ed6b5e99ff48376e200b1` | Unified `Trusted` + 3-Layer `Theory` stack, fixed `MirLang` vs. `MirLangBroken`, `ShardCert`, and 10 positive/negative soundness canaries. |
| `support/run_unified_benchmark.py` | `execution` | `75481083294165f880aa91b84d6db22bdab445d9de1cb056e64ecb28bdb7504a` | Generator and benchmark runner for `Stage 0`..`Stage 4`, all 10 per-function shards, and the 5 standalone negative canary rejection tests. |
| `support/unified_benchmark_results.json` | `execution` | `116b056204c4a91721af14ebda3626049d554d5bb9fe3f00b7468321725595d1` | Recorded JSON metrics for `Stage 0`..`Stage 4`, `Shard 0`..`Shard 9`, and negative canaries. |
| `support/BenchmarkProofStrategies.lean` | `execution` | `0e6a9f9ef904a29e53a2fff4b2446599b4d22ecee97ebc80f19417e221725a81` | Implementation of Architectures 1a, 1b, 2, 3, 4, 5, and 6 (`cv_trans`) over 64-bit register/flag states. |
| `support/ProbeSideConditionReflection.lean` | `execution` | `6f0c20ec262c0cdc604389d4d92b40331e6d3fea4d5db37fb51a9eb254e7c173` | `IntervalsDisjoint`, `AlignedRoundUp`, `SymbolicSubrange`, and pre-proved GMP `Nat` boolean batch checkers. |
| `support/MeasureKernel.lean` | `execution` | `ac90f46e0a474d7f444d08daa7a7ef0186ea1c3fc43bbace0bfca6242aac3ecc` | 7-run median `baseEnv.toKernelEnv.replay` timer and pointer-shared `DAG_NODES` / expanded `TREE_NODES` counter. |
| `support/run_suite_a.py` | `execution` | `1d9d9800835c05e755cc4542e3ba7c7518591cddefc47a79d0d5cb9d90ae3e1e` | Benchmark generator and runner for Suite A ($N \in \{10, 25, 50, 100, 250, 500\}$ across Architectures 1a–6). |
| `support/run_suite_b.py` | `execution` | `687c86b7f521c1b51a78ce535fb67d0302b4627f73dc1915e7806987a45688ed` | Benchmark generator and runner for Suite B (Chained Diamonds $D \in \{2..10\}$, Multi-Call $K \in \{2..20\}$, Bounded & Symbolic Loops). |
| `support/run_side_conditions.py` | `execution` | `8a1a6256a028619f8ff77fef67c0250a68dd1963e6667484bbae92aeb6c564ee` | Benchmark generator and runner comparing `omega`, `decide` + `omega`, and pre-proved `Theory` reflection across 50 obligations. |
| `support/suite_a_results.json` | `execution` | `defe94560343e972617ffa8f2933e3e1baaa8b5f38fe63189d5222e04f69f1b3` | Recorded JSON metrics for Suite A ($N \in \{10..500\}$). |
| `support/suite_b_results.json` | `execution` | `c29912a8a9bd0f00756d6a419c32f13f055e5153a386c420aa0f66fe9f849bdc` | Recorded JSON metrics for Suite B (Diamonds, Multi-Call, Loops). |
| `support/side_condition_results.json` | `execution` | `40b359e6eba5165fe39aa7e1609e2f18b7050da52ad9def8b818dcb9b78a6d1a` | Recorded JSON metrics for 50 side-condition obligations. |
| `support/ProbePreprovedPasses.lean` | `execution` | `f3977937f95f16ae341d0e350adedbcc1c5ceeb3268ab8077ef1a6646b2964f7` | Self-contained probe for Points 1–4 of the `Language.Abstracts` pass/validator spectrum and `symbolicWhile_sound`. |
| `support/ProbePreprovedSummaries.lean` | `execution` | `7ea6bed3f8dcb2181ba6860fa424063e027ffa56b67874f3172bf56294773792` | Self-contained probe for `call1_summary_flat_sound`, `{ s with ... }` $O(3^K)$ tree blowup, and 10 polymorphic `core` summaries. |
| `support/ProbeShardedCrateProof.lean` | `execution` | `402ec578ad1dc407312536f607182ff32e68655a43637ca5eed0585b7c12c811` | Self-contained probe for `ShardCert`, `verify_crate_of_shards`, structural `.tail`/`.head` TCB witnesses, and Regimes 1–5 incremental replay. |

## Revalidation

To revalidate the findings in this report on a newer Lean 4 toolchain or after
changes to `trusted/` or `theory/Anneal/`, run the following narrow checks from
 cleanest to broadest:

1. **Diff the C++ Kernel Reducer and Substitution Paths (~1 minute):**
   In the target `leanprover/lean4` revision, inspect:
   - `src/kernel/type_checker.cpp`: Check `reduce_nat` (`if (has_fvar(e)) return
     none_expr();`), `whnf_core` (whether `String.beq` or `BitVec` have been
     added to `reduce_nat` / native reducers), and `infer_lambda` vs.
     `infer_let`.
   - `src/kernel/replace_fn.cpp` and `src/kernel/expr.h`: Check whether
     `is_likely_unshared` (`m_rc == 1`) still bypasses `replace_rec_fn::m_cache`.
2. **Run the Three Self-Contained `#eval` Probes (~10 seconds total):**
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/ProbePreprovedPasses.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/ProbePreprovedSummaries.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/ProbeShardedCrateProof.lean
   ```
   Verify from stdout that:
   - Point 3 (`point3_evalSym_body12`) remains `59` DAG nodes / `223` tree nodes
     vs. Point 1 (`665` DAG nodes / `34,705` tree nodes).
   - `summary_flat_caller10` remains `9,515` tree nodes vs. `summary_caller10`'s
     `17,134,141` tree nodes ($O(3^K)$ `{ s with ... }` blowup).
   - Regime 3b (`shard_19_structural` + `verify_crate20`) remains `>25x` faster
     than Regime 3 (`by decide` TCB lookup) and `>250x` faster than Regime 1.
3. **Re-Run the Unified 5-Stage End-to-End Benchmark and Soundness Canaries
   (~45 seconds):**
   Copy `support/` to a temporary working directory (so generated `.olean` and
   intermediate stage files do not dirty the reference tree) and run:
   ```console
   python3 run_unified_benchmark.py
   ```
   Verify that `Stage 0` $\to$ `Stage 4` reproduces the progression from
   multi-second full replay down to sub-12ms per-shard incremental replay and
   that all 5 standalone negative canary files (`NegativeCanary1_Overflow.lean`
   through `NegativeCanary5_DivergentDiamond.lean`) fail compilation with
   `returncode == 1`.
