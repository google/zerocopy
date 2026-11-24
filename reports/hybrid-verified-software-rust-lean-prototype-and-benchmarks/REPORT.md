# Hybrid Verified Software Prototypes and Benchmarks: Safe-Rust Combinators, Verified Lean 4 Checkers, and Live Anneal Certificate Emission

## Summary

End-to-end execution of three hybrid verified software prototypes demonstrates that pairing unverified `#![forbid(unsafe_code)]` Rust producers with small certificate checkers and Lean `v4.34.1` soundness proofs achieves low-overhead verification in both runtime-checked and compile-time-checked regimes—while empirical release benchmarks confirm that net speedup flips cleanly across workload topologies. Across our measured Rust (`rustc 1.102.0-nightly`, `--release`) and Lean (`v4.34.1`) suite ([`support/wave4_measurements.json`](support/wave4_measurements.json)):

1. **Idiomatic Safe-Rust Hybrid Core (`136` SLOC):** [`support/hybrid_proto_suite/src/lib.rs`](support/hybrid_proto_suite/src/lib.rs) enforces structural containment without `unsafe` via a sealed `Certified<T>` capability type (`trust_core`), `I: Sync + RefUnwindSafe` bounds preventing interior-mutability panic leaks across `std::panic::catch_unwind`, and uniform `verify_opt` / `verify_or_fallback` / `race_or_fallback` combinators.
2. **Runtime-Checked Systems Algorithms (SSSP & Deflate LZ77/Kraft) and Topology Crossover:**
   - *Shortest paths (`sssp.rs` + `HybridSsspChecker.lean`):* A `73`-line $O(V + E)$ potential+parent+rank checker verifies an untrusted Dijkstra producer at **`10.08%–17.04%`** overhead (`22.75 us` vs `225.79 us` at `N=1,024, E=8,191`). However, topology dictates ROI: on random low-diameter graphs, early-exit Bellman-Ford already finishes in `147.81 us` (`0.65x`, negative ROI for Dijkstra+checker), whereas on high-diameter reverse-ordered chains (`N=1,024, E=2,045`), Bellman-Ford degrades to `6,916.64 us` (**`78.57x`** vs Dijkstra; **`71.08x`** net hybrid speedup including checker). Lean `v4.34.1` verifies `checkSsspWitness_sound` (exact path witness + global optimality, even with `0`-weight edges) in **`1.08 s`** (`178,524 KiB` RSS, `[propext]`).
   - *Deflate LZ77 + Kraft (`deflate.rs` + `HybridDeflateChecker.lean`):* A `46`-line zero-output-buffer cursor+Kraft checker verifies a `119`-line greedy hash-chain LZ77 + bounded-Kraft producer compressing `65,536 B` down to `739` tokens (`0.0113` tokens/byte) at **`12.72%–21.11%`** overhead (`50.93 us` vs `315.50 us`). Lean `v4.34.1` proves `checkLzReplay_sound` (`[propext]`) and `checkKraftBounds_sound` (**zero axioms `[]`**) in **`1.33 s`** (`175,100 KiB` RSS).
3. **Live Rust-to-Anneal Certificate Emission (`anneal_emit.rs` -> `Anneal.{LinearArith, BitTrieLrat}`):** An untrusted `155`-line Rust DPLL solver (`solve_unsat_emit_lrat`) proves unsatisfiability on `PHP(4, 3)` (`12` vars, `22` clauses) in **`28.79 us`** and `K_4` `3`-coloring in **`20.46 us`**, emitting `.addRup`/`.del`-pruned LRAT traces alongside Chvátal-Gomory `CutStep` certificates (`5,633` bytes in [`support/anneal_bridge/HybridBridge/GeneratedCerts.lean`](support/anneal_bridge/HybridBridge/GeneratedCerts.lean)). Unmodified upstream `Anneal.LinearArith` and `Anneal.BitTrieLrat` (`google/zerocopy@7527dd2b`) kernel-check all `4` positive theorems (`[propext]` only, `0` `sorry`) and `3` negative controls in **`2.86 s`** (`199,968 KiB` peak RSS)—avoiding implementing or trusting any SAT/cut search inside Lean.

*Model–system relation note:* `HybridSsspChecker.lean` and `HybridDeflateChecker.lean` verify functional checker soundness over `Nat` / `List`; fixed-width `u64`/`u8` overflow safety and `RefUnwindSafe` isolation in Rust are enforced in the Rust crate (`checked_add`, `checked_mul` / `usize` bounds, `#![forbid(unsafe_code)]`) rather than via Rust-to-Lean extraction (`Basis: derived (dual-artifact alignment)`).

## Applicability

- **Rust prototype & benchmark suite ([`support/hybrid_proto_suite/`](support/hybrid_proto_suite/Cargo.toml)):** Self-contained `#![forbid(unsafe_code)]` Rust 2021 crate with zero external crate dependencies; tested with `rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 2026-11-11)` on `x86_64-unknown-linux-gnu` (`--release --offline`).
- **Lean 4.34.1 checkers & bridge ([`support/lean_checkers/`](support/lean_checkers/lakefile.toml), [`support/anneal_bridge/`](support/anneal_bridge/lakefile.toml)):** Pure `prelude` + `Init.*` (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`). The Anneal bridge compiles directly against unmodified `anneal/theory/Anneal/{LinearArith,BitTrieLrat}.lean` from `google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82`.
- **Relationship to sibling corpus reports:** Completes the four-part hybrid verified software series alongside `hybrid-verified-software-contracts-fallback-and-ratcheting` (formal `Option<T>` contract & ratcheting lattice), `hybrid-verified-software-taxonomy-and-roi-boundaries` (benefit taxonomy & ROI curve), and `hybrid-verified-software-hazards-ub-toctou-and-hyperproperties` (Miri UB probes & 3-channel hyperproperty leakage). Connects directly to `anneal-mir-r3-local-compaction-fast-cert-checking-and-scc-olean-sharding`, `farkas-certificates-integer-cuts-and-bitvector-interval-transfer`, and `sat-inprocessing-drat-lrat-frat-checkers-maxsat-and-qbf-skolem-certificates`.

## Findings

### 1. Safe-Rust Hybrid Combinator Architecture (`trust_core` & `RefUnwindSafe`)

`Basis: source + execution` ([`support/hybrid_proto_suite/src/lib.rs`](support/hybrid_proto_suite/src/lib.rs), `159` raw / `136` non-blank non-comment SLOC; [`support/hybrid_proto_suite/tests/suite.rs`](support/hybrid_proto_suite/tests/suite.rs))

```
  &I (Sync + RefUnwindSafe) ──▶ catch_unwind(producer)
                                    │
                  ┌─────────────────┼─────────────────┐
                  ▼ panic           ▼ None            ▼ Some((out, witness))
            panics += 1       nones += 1        checker(&I, &(out, witness))
                  │                 │                 ├── false ─▶ rejects += 1
                  ▼                 ▼                 └── true  ─▶ Certified::new_checked(out)
         verify_opt = None    verify_opt = None
                  │ (in verify_or_fallback)
                  ▼
         fallbacks += 1 ─▶ fb = fallback(&I) ─▶ assert!(checker(&I, &fb)) ─▶ CertifiedOutcome
```

Three design constraints emerged during implementation (`suite.rs`, `4/4` tests passing under `--release --offline`):

1. **Private-module capability sealing (`trust_core::Certified<T>`):** Defining `Certified<T>` inside a child submodule with a private `value: T` field and `pub(super) fn new_checked` prevents downstream consumers or untrusted producers from constructing a forged `Certified<T>`. Even the deterministic `fallback` path in `verify_or_fallback` and `race_or_fallback` must pass `checker` before minting `Certified<T>`, making `checker` the unique trust choke point.
2. **`RefUnwindSafe` eliminates `AssertUnwindSafe`:** Requiring `I: Sync + std::panic::RefUnwindSafe` and `P: FnOnce(&I) -> Option<(T, W)> + UnwindSafe` guarantees at compile time that untrusted producers cannot mutate interior state (`Cell`, `RefCell`, `Mutex`) through shared input references prior to panicking—directly operationalizing the unwind-pollution boundary established in `hybrid-verified-software-hazards-ub-toctou-and-hyperproperties`.
3. **Adversarial mutant tests require non-vacuous targeting:** An initial `mutant_suboptimal_dist` mutated `cand.0.last_mut()`, which landed on unreachable vertex `4` (`None`) in the `5`-node canary graph and passed silently; targeting the last *reachable* non-source vertex immediately triggered deterministic checker rejection (`suite.rs:test_sssp_valid_and_adversarial_mutants`).

---

### 2. Prototype A: Verified $O(V + E)$ SSSP Checker & Topology Crossover

`Basis: execution` ([`support/hybrid_proto_suite/src/sssp.rs`](support/hybrid_proto_suite/src/sssp.rs), `297` raw / `263` SLOC; [`support/lean_checkers/HybridSsspChecker.lean`](support/lean_checkers/HybridSsspChecker.lean), `383` raw / `335` SLOC)

Untrusted Dijkstra (`52` lines) emits `(dist, SsspWitness { dist, parent, rank })`. To reject spurious self-supporting `0`-weight cycles (which pass edge-weight checks alone), the `73`-line Rust checker and `HybridSsspChecker.lean` require strictly increasing hop ranks (`rank[parent[v]] < rank[v]`) alongside triangle optimality (`dist[dst] <= dist[src] + w`, checked with `u64::checked_add`).

| Topology (`N`, `E`) | `dijkstra_producer` | `check_sssp_witness` (`%` of Dijkstra) | `bellman_ford_fallback` (`ratio` vs Dijkstra) | Net Hybrid Assessment |
| :--- | ---: | ---: | ---: | :--- |
| `random_low_diam` (`64`, `511`) | `9.80 us` | `1.67 us` (`17.04%`) | `3.71 us` (`0.38x`) | **Negative ROI** (early-exit BF `3.1x` faster) |
| `random_low_diam` (`256`, `2,047`) | `36.73 us` | `5.76 us` (`15.68%`) | `21.06 us` (`0.57x`) | **Negative ROI** (early-exit BF `2.0x` faster) |
| `random_low_diam` (`1,024`, `8,191`) | `225.79 us` | `22.75 us` (`10.08%`) | `147.81 us` (`0.65x`) | **Negative ROI** (BF `1.68x` faster than Dijkstra+check) |
| `reverse_chain` (`256`, `509`) | `21.23 us` | `2.28 us` (`10.76%`) | `274.42 us` (`12.93x`) | **`11.67x` net speedup** |
| `reverse_chain` (`512`, `1,021`) | `42.73 us` | `4.45 us` (`10.42%`) | `1,778.95 us` (`41.63x`) | **`37.70x` net speedup** |
| `reverse_chain` (`1,024`, `2,045`) | `88.03 us` | `9.28 us` (`10.54%`) | `6,916.64 us` (`78.57x`) | **`71.08x` net speedup** |

**Lean 4.34.1 soundness & adversary audit (`HybridSsspChecker.lean`, `1.08 s`, `178,524 KiB` RSS):**
- `checkSsspWitness_sound` (`[propext]` only) proves both (a) concrete `GraphPath g src v d` existence via structural induction on hop-rank bound `k` (`reach_path_by_rank`), and (b) global path lower bound `d <= w'` (`validPotentials_lower_bound`) plus unreachability (`none => False`).
- Kernel `rfl` rejects forged `0`-weight cycle (`forgedZeroCycle_rejected`), forged suboptimal distance (`forgedSuboptimal_rejected`), and hidden reachable node (`forgedUnreachable_rejected`), while Rust tests reject `4/4` adversarial mutants (`3` checker rejects + `1` caught panic) and fall back cleanly to `bellman_ford_fallback` (`42` lines).

---

### 3. Prototype B: Deflate-Style LZ77 Cursor Replay + Canonical Kraft Bounds

`Basis: execution` ([`support/hybrid_proto_suite/src/deflate.rs`](support/hybrid_proto_suite/src/deflate.rs), `248` raw / `213` SLOC; [`support/lean_checkers/HybridDeflateChecker.lean`](support/lean_checkers/HybridDeflateChecker.lean), `337` raw / `288` SLOC)

Greedy hash-chain LZ77 + depth-capped Huffman length assignment (`79 + 40 = 119` lines) returns a `DeflateCandidate`; a `46`-line zero-output-buffer cursor verifier (`check_deflate_plan`) checks Kraft's inequality ($\sum_{l > 0} 2^{L_{\max}-l} \le 2^{L_{\max}}$, $L_{\max} \le 15$) and compares back-references in-place against the input buffer, with a `9`-line `stored_literal_fallback` using uniform `8`-bit symbol lengths ($256 \cdot 2^{15-8} = 2^{15}$).

| Structured Input Bytes | Emitted Tokens (Tokens/Byte) | `greedy_lz77_huffman_producer` | `check_deflate_plan` (`%` of Producer) | `stored_literal_fallback` (Note 1) |
| ---: | ---: | ---: | ---: | ---: |
| `4,096` | `183` (`0.0447`) | `37.86 us` | `4.81 us` (`12.72%`) | `4.31 us` |
| `32,768` | `461` (`0.0141`) | `150.36 us` | `31.75 us` (`21.11%`) | `644.63 us` |
| `65,536` | `739` (`0.0113`) | `315.50 us` | `50.93 us` (`16.14%`) | `1,377.31 us` |

*Note 1:* `stored_literal_fallback` allocates `Vec<LzToken>` twice (`tokens.clone()` inside `DeflatePlan`) to satisfy the shared `DeflateCandidate` type, explaining its `1,377.31 us` allocation latency at `64 KiB` vs `315.50 us` for `739` compressed tokens; a specialized `Stored` wire framing bypasses `Vec<LzToken>` construction.

**Lean 4.34.1 proof (`HybridDeflateChecker.lean`, `1.33 s`, `175,100 KiB` RSS):**
- `checkLzReplay_sound` (`[propext]`): proves the allocation-free cursor verifier `checkLzReplay expected tokens = true` implies `decodeLzTokens tokens = some expected` (handling overlapping back-references where `len > dist`).
- `checkKraftBounds_sound` (**zero axioms `[]`**): proves symbol code length caps and scaled Kraft budget $\le 2^{\text{maxBits}}$.
- `3` negative `rfl` theorems reject mismatched overlapping replay (`forgedBadMatch_rejected`), oversubscribed Kraft trees `[1, 1, 2]` (`forgedKraftOversubscribed_rejected`), and `16`-bit symbols (`forgedMaxBitsExceeded_rejected`), matching `4/4` adversarial mutants caught in `suite.rs`.

---

### 4. Prototype C: Live Rust Solvers Emitting Certificates Checked by Upstream `Anneal`

`Basis: source + execution` ([`support/hybrid_proto_suite/src/anneal_emit.rs`](support/hybrid_proto_suite/src/anneal_emit.rs), `642` raw / `573` SLOC; [`support/anneal_bridge/HybridBridge/GeneratedCerts.lean`](support/anneal_bridge/HybridBridge/GeneratedCerts.lean), `201` raw / `176` SLOC, `5,633` bytes)

Rather than implementing SAT solving or cut-plane discovery inside Lean, `bench_and_emit` runs untrusted Rust producers that log machine-checkable witnesses and emits `GeneratedCerts.lean` importing **unmodified** `Anneal.LinearArith` (`2,061` raw / `1,884` SLOC upstream) and `Anneal.BitTrieLrat` (`1,059` raw / `951` SLOC upstream) from `google/zerocopy@7527dd2b`:

| Instance / Obligation | Untrusted Rust Producer Metric | Emitted Certificate | Lean `v4.34.1` Theorem & Axioms | Negative Control (`rfl`) |
| :--- | :--- | :--- | :--- | :--- |
| **`alignPairGoal`** (`4` vars, `2` hyps: `2*v0 <= 2*v1+1`, `2*v2+1 <= 2*v3` `|-` `v0+v2+1 <= v1+v3`) | Rational Farkas unsolvable (`v0=v1+0.5, v2=v3-0.5`) | `7` `CutStep`s (`2` `.divCut 2` cuts + `comb`) | `alignPair_verified` (`[propext]`) | `alignPair_without_divCut_rejected` (`= false`) |
| **`stripePartitionGoal`** (`6` vars, `3` hyps: `4*v0+3 <= 4*v1`, `2*v2 <= 2*v3+1`, `4*v4 <= 3` `|-` `v0+v2+v4+1 <= v1+v3+v5`) | Uses `3` integer cuts (`divCut 4`, `divCut 2`, `divCut 4`) + auto `0 <= v5` | `12` `CutStep`s | `stripePartition_verified` (`[propext]`) | `stripePartition_wrong_divisor_rejected` (`= false`) |
| **`php43Cnf`** (`PHP(4, 3)`: `12` vars, `22` clauses) | DPLL solve: **`28.79 us`**, Rust RUP pre-check **`6.28 us`** | `17` tree nodes, `25` steps (`17` `.addRup`, `8` `.del`), `depth = 7` | `php43_unsat_verified` (`[propext]`) | `php43_forged_hint_rejected` (`.errBadHint 99 999`) |
| **`k4Color3Cnf`** (`K_4` 3-coloring: `12` vars, `22` clauses) | DPLL solve: **`20.46 us`**, Rust RUP pre-check **`6.17 us`** | `17` tree nodes, `25` steps (`17` `.addRup`, `8` `.del`), `depth = 7` | `k4Color3_unsat_verified` (`[propext]`) | Same checker (`errBadHint` / `errNoConflict`) |

Lean `v4.34.1` kernel-checks the entire `5,633`-byte `GeneratedCerts.lean` module in **`2.86 s`** wall time (`199,968 KiB` peak RSS) with zero `sorryAx` and zero `Lean.ofReduceBool`. Crucially, if a future optimization upgrades `dpll_prove` in `anneal_emit.rs` to VSIDS/CDCL/watched literals or an SMT solver, **zero lines** of `Anneal.LinearArith`, `Anneal.BitTrieLrat`, or outer theorem signatures change.

## Boundaries

- **Single-threaded scaling & instance size:** Rust benchmarks evaluate synthetic graphs (`N <= 1,024`), structured `<= 64 KiB` buffers, and `12`-variable UNSAT CNFs under deterministic single-thread `-O3` release execution; multi-core contention, cache-unfriendly adversarial graphs at `N >= 10^6`, and larger (`10^4+` clause) LRAT kernel reduction scaling in Lean are **not** measured here (`unknown`).
- **Dual-artifact semantic gap:** The Rust checkers (`sssp.rs`, `deflate.rs`) and Lean 4 checkers (`HybridSsspChecker.lean`, `HybridDeflateChecker.lean`) share identical algorithmic invariants, but are written separately (`Nat`/`List` in Lean vs `u64`/`u8`/slices in Rust) rather than compiled from one source (`derived`, not formal extraction).
- **In-process Rust resource exhaustion:** `#![forbid(unsafe_code)]` with `RefUnwindSafe` prevents aliasing UB and shared-state panic corruption, but cannot contain OOM aborts or infinite loops in an untrusted producer without an external OS/Wasm process boundary (`unsupported` in-process).

## Evidence

- **Machine-readable telemetry & SHA-256 manifest:** [`support/wave4_measurements.json`](support/wave4_measurements.json).
- **Self-contained Rust prototype crate ([`support/hybrid_proto_suite/`](support/hybrid_proto_suite/Cargo.toml)):**
  - `src/lib.rs` (SHA-256 `300c6522a6b3a573a57c8bb5beb35f21860f5995f91525e5a8a8933780304165`), `src/sssp.rs` (`9a2d2984c7431de85ac4df389c54c2a4a2ef0fc9c06c08896ef89f2d14d96c50`), `src/deflate.rs` (`29edfbb4dc136c0564bd7c5dffe38072854236929a3d2d8e9164e5f98bc9ba11`), `src/anneal_emit.rs` (`eb192fe0f41f81cbeea6b55977c3f417058be579fc2ad911eab6a6597fa17fd1`), `src/bin/bench_and_emit.rs` (`8a45c43a95508a12a3e06b52e7ddcaab9f48aa6b25c7e3725d3de1b065b89594`), `tests/suite.rs` (`3505223bef719d8032e1247912906d920e8cd8d428c870a57565809645aad91b`).
  - `cargo test --release --offline -j2`: `4 passed; 0 failed` (`0.00s` test execution).
- **Standalone Lean 4.34.1 checkers ([`support/lean_checkers/`](support/lean_checkers/lakefile.toml)):**
  - `HybridSsspChecker.lean` (SHA-256 `6450acb745fbe3f1ffdfe2ba07f5cfb374d9e4b05762289e67944cf4c7773ddb`): `1.08 s` wall, `178,524 KiB` peak RSS, axioms `[propext]`.
  - `HybridDeflateChecker.lean` (SHA-256 `55ec0d956e11c97b9ebdad9b081df72ddb2af3c6a5fc5dc5db004253cca07ff6`): `1.33 s` wall, `175,100 KiB` peak RSS, axioms `[propext]` (`checkLzReplay_sound`) and `[]` (`checkKraftBounds_sound`).
- **Anneal bridge ([`support/anneal_bridge/HybridBridge/GeneratedCerts.lean`](support/anneal_bridge/HybridBridge/GeneratedCerts.lean)):**
  - SHA-256 `97837ff317b2df771bc5e0e447bf512e87a4ede433b0e53c00ab4c91c37ea133`.
  - Verified against unmodified `google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82` `Anneal.LinearArith` (SHA-256 `1b0225d32813d32eda1330c873126bfb7036d849dee5257e8a4a60165758c7e9`) and `Anneal.BitTrieLrat` (SHA-256 `1eb35e47d6ffde41c969f2c52f48467f73fb48755a50e8be26a678d0d36da98a`): `2.86 s` wall, `199,968 KiB` peak RSS, `[propext]` only, `0` warnings.

## Revalidation

From `reports/hybrid-verified-software-rust-lean-prototype-and-benchmarks/support/`:

1. Run the Rust unit tests, adversarial mutant probes, and `-O3` microbenchmarks:
   ```bash
   (cd hybrid_proto_suite && cargo test --release --offline && cargo run --release --offline --bin bench_and_emit -- /tmp/hybrid_reval)
   ```
2. Typecheck the standalone Lean `v4.34.1` certifiers:
   ```bash
   (cd lean_checkers && elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridSsspChecker.lean && elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridDeflateChecker.lean)
   ```
3. Extract unmodified `Anneal.{LinearArith,BitTrieLrat}` from `google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82` into `anneal_bridge/Anneal/`, build `Anneal`, and verify `HybridBridge/GeneratedCerts.lean`:
   ```bash
   mkdir -p anneal_bridge/Anneal
   # Copy anneal/theory/Anneal/{LinearArith,BitTrieLrat}.lean from google/zerocopy@7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82 into anneal_bridge/Anneal/
   # Update anneal_bridge/lakefile.toml if desired with `[[lean_lib]] name = "Anneal"; roots = ["Anneal.LinearArith", "Anneal.BitTrieLrat"]`
   (cd anneal_bridge && elan run leanprover/lean4:v4.34.1 lake build Anneal && LEAN_PATH=.lake/build/lib/lean elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridBridge/GeneratedCerts.lean)
   ```
