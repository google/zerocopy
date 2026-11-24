# Tarjan SCC `.olean` Sharding, `BinChunkTree` Body Resolution, and Incremental Crate Verification

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Monolithic single-module Lean verification (`Captured.lean` + `Proof.lean` over `Program.bodies : List Body`) fails at crate scale on four coupled cliffs (`e8dcb7f08edbc19485c9e7980333607ebbff5f48`):
1. **Linear `BodiesVerified` + quadratic `bodiesHaveUniqueIdentities`:** Hits `2,237.61 MiB` peak RSS at $N = 100$ and aborts at `maxRecDepth = 512` at $N = 250$ (`94.474s`).
2. **Monolithic tree elaboration heap & heartbeat cliff:** Even with `BinChunkTree`, a single `Proof.lean` reaches `1,099.48 MiB` at $N = 250$ and fails with a deterministic `whnf` heartbeat timeout (`200,000` heartbeats, `2,019.10 MiB` RSS) at $N = 500$.
3. **Root `rfl` re-unfolding across shards:** Checking `BinChunkTree.{wf,allIdx}` by `rfl` at root `Proof.lean` forces delta-unfolding of every `Captured.Shard_k.body_i` (`354.89 MiB` root RSS at $N = 50$) and breaks non-`@[expose]` Lean 4 `module` encapsulation.
4. **Quadratic `String.ofList` UTF-8 conversion:** `(_root_.String.ofList cs).toByteArray` runs `List.toByteArray.loop` (`Array.push` = `List.concat`) in $O(L^2)$ list copies at $\approx 5.3 L$ depth, tripping `maxRecDepth = 512` on single `101`-byte `zerocopy` trait-impl identities (`rust-path-v1::impls::_::<impl TryFromBytes for usize>::only_derive_is_allowed_to_implement_this_trait`).

This architecture resolves all four cliffs with **`0` LOC added to `trusted/lean/`**:
- **Deterministic Tarjan SCC call-graph condensation + Kahn lexicographic min-heap topological sorting**, packed greedily into bounded shards (`B_max = 20` bodies, `A_max = 2,500` AST nodes) with `D = 1` parallel `Captured.Shard_k` modules (`import Trusted.MirAst` only) and `capture_shards.json`.
- **Pass-1-portable `Anneal.SccSharding.BinChunkTree`** (`prelude`, `[propext]`, `0` `sorryAx`, `0` `._unsafe_rec`), providing $O(\log N)$ `DefId` lookup (`getElem?_toList_eq_get?`), parametric distributive branch combinators (`toList_branch`, `size_branch`, `wf_branch`, `allIdx_branch`) so root `Proof.lean` assembles $K = 26$ shards in `0.359s` / `197.46 MiB` at $N = 500$ without unfolding body terms, $O(N \log N)$ `ByteDecisionTree` identity uniqueness (`Proof/IdTree.lean`), and linear $O(L)$ `string_ofList_bytes_eq` (`List.flatMap String.utf8EncodeChar cs`).
- **Validated scaling & compatibility:** Passes $N = 50..500$ cyclic call-graph crates (`236.68–255.89 MiB` max shard RSS, `7.23–7.56s` $O(1)$-shard single-body incremental rebuilds), verbatim `zerocopy/src/` `50`- and `100`-body captures (`3.991s` and `7.481s`), `TrustedBoundary.lean` `"target-audit"` (`0` `Proof.*` `.olean`s in `subjectClosure`), Lean 4 `module` 3-part splits (`35.2x` smaller public `Proof.Shard_000.olean`: `9,504 B` vs. `334,464 B` `.olean.private`), and Lean `v4.35.0` `5a`/`5b`/`5c` NDJSON replay (`nanoda_bin` `0.875s` / `32.61 MiB`, `con-ron --verified` `1.663s` / `200.47 MiB`).

## Applicability

Findings characterize the `google/zerocopy` Anneal baseline at commit `e8dcb7f08edbc19485c9e7980333607ebbff5f48` (`Trusted.MirAst`, `Trusted.MirModel`, `Trusted.MirSemantics`, `TrustedBoundary.lean`, `anneal/trusted/rustc-capture`, `anneal/trusted/cargo-anneal`, `Anneal.MirWp`), Lean `v4.34.1` (`lean`, `TrustedBoundary.olean`), and Lean `v4.35.0` (`leanexport` `NDJSON 3.1.0`, `nanoda_bin`, `con-ron --verified`), composed with Lean 4 `module` compilation (`#4139` / `9c2e5ca72d`) and $\lambda$-lifted `M3` proof linking (`#4181`).

Targets with $N \le N_{\min}$ (`20` bodies by default) retain the single-file `Captured.lean` layout without sharding overhead. Classic single-`.olean` sharding runs unmodified on `e8dcb7f08edbc19485c9e7980333607ebbff5f48` `TrustedBoundary.lean`; target-level `module` mode (`isModule: true`) additionally requires `#4139` Phase-2 admission in `TrustedBoundary.lean:5615,5650`.

## Findings

### 1. Sharded Target Module Topology and `D = 1` Capture Decoupling

Basis: source + execution (`support/scc_olean_sharding_prototype.md` Partition 1 §2).

```text
  Trusted.MirAst <--- Captured.Shard_000 .. Captured.Shard_{K-1}  [Role: Capture, D = 1]
                              |
                              v
                          Captured                                [Role: Capture, O(K) root]
                              |
                              v
  Spec [Role: Spec] ----> Expected                                [Role: Expected]
      |                       |
      v                       |
  Proof.IdTree [Role: Proof]  |
      |                       |
      v                       v
  Proof.Shard_000 .. Proof.Shard_{K-1} -------------------------> Proof [Role: Proof, O(K) root]
```

Because `Trusted.MirAst.TerminatorKind.call` (`Terminators.lean:155`) encodes direct call targets by numeric `DefId : Nat` indices into `Program.bodies` rather than Lean constant references to callee `Body` terms, `Captured/Shard_k.lean` imports **only** `Trusted.MirAst` (`D = 1` full $K$-way parallelism). Callee-first ordering ensures edits to callers in `Shard_k` keep `DefId` ranges `[base_j, end_j]` of callee shards $j < k$ stable.

### 2. Deterministic Tarjan SCC Condensation, Kahn Min-Heap Ordering, and Bucket Coarsening

Basis: source + derived (`support/scc_olean_sharding_prototype.md` Partition 1 §3).

1. **Call-Graph Extraction:** Builds intra-crate digraph $G = (V, E)$ over `Body.identity` from `TerminatorKind.call` edges and indirect function-item / closure / vtable references (preserving self-loops $(u, u)$ as `is_cyclic = true` singleton SCCs).
2. **Permutation-Invariant Condensation:** Pre-sorts $V$ and each adjacency list $E(u)$ by UTF-8 byte order of `Body.identity` (deduplicating parallel edges), runs an iterative explicit-stack Tarjan pass ($O(|V| + |E|)$), sorts each SCC $C$ by `Body.identity`, and assigns canonical key $\text{key}(C) \triangleq \min_{u \in C} u.\text{identity}$. A binary min-heap Kahn topological sort over $G_{\text{SCC}}$ (keyed by $\text{key}(C)$, starting from zero-outdegree leaf SCCs) emits a unique callee-first SCC sequence $(C_0, \dots, C_{M-1})$.
3. **Contiguous Coarsening:** Greedily packs contiguous SCC runs into `Shard_000 .. Shard_{K-1}` under $(B_{\max}, A_{\max})$ (`20` bodies, `2,500` AST nodes). Any single mutually recursive SCC exceeding $(B_{\max}, A_{\max})$ is isolated into its own dedicated shard (`"oversized_scc": true` in `capture_shards.json` so cgroup governance assigns a larger memory slot) rather than splitting cycles across shards. Contiguous interval merging preserves strict inter-shard acyclicity ($j < k$ for every cross-shard call from $S_k$ to $S_j$).
4. **Manifest (`capture_shards.json`):** Written atomically alongside `capture.json` (`#[serde(deny_unknown_fields)]`, `schema_version: 1`) recording `total_bodies`, `total_sccs`, `cyclic_sccs`, `total_shards`, `is_lean_module`, `id_tree_sha256`, and per-shard `{shard_idx, capture_module, proof_module, capture_sha256, num_bodies, ast_nodes, has_cycle, oversized_scc, scc_ids, callee_shards, global_def_id_range, identities}`.

### 3. `0`-TCB `Anneal.SccSharding.BinChunkTree`, `ByteDecisionTree`, and `string_ofList_bytes_eq`

Basis: source + execution (`support/scc_olean_sharding_prototype.md` Partition 1 §4, Partition 3 §3; kernel-checked with `-Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`, `0` `._unsafe_rec`, axioms `["propext"]`).

- **Balanced `BinChunkTree α`:** Constructors `empty`, `leaf (val : α)`, and `branch (half : Nat) (left right : BinChunkTree α)`. `BinChunkTree.get?` tests `Nat.blt idx half` in $\le \lceil \log_2 N \rceil$ GMP comparisons ($9$ at $N = 500$; $13$ at $N = 4,545$). `getElem?_toList_eq_get?` proves `Trusted.MirSemantics.getElem? (toList t) idx = get? t idx` when `wf t = true`.
- **Non-Unfolding Distributive Combinators:** `Proof/Shard_k.lean` exports five closed shard theorems (`shard_bodies_eq`, `shard_size`, `shard_wf`, `shard_uniq`, `shard_verified`); root `Proof.lean` folds them over $K - 1$ internal nodes using `toList_branch`, `size_branch`, `wf_branch`, and `allIdx_branch` without unfolding `shardTree`.
- **`ByteDecisionTree` (`Proof/IdTree.lean`):** Balanced byte-splitting tree (`splitByte pos threshold ltBranch geBranch | leaf expectedDefId | fail`) mapping UTF-8 path bytes to global `DefId` in $O(\log N)$ byte comparisons (`bodiesHaveUniqueIdentities_of_decisionTree`). Depends only on item names, staying `100%` cached across implementation-body edits.
- **`string_ofList_bytes_eq`:** Proved once over `List.toByteArray.loop`, rewriting `(_root_.String.ofList cs).toByteArray.data.toList = List.flatMap String.utf8EncodeChar cs`. Used by `checkBodyIdentityAt_of_ofList` and `bodyStaticIntrinsic_of_ofList` to verify `101+`-byte verbatim `zerocopy` trait paths in `<0.05s` at default `maxRecDepth = 512`.
- **Interprocedural Proofs (`InterprocCallModel` & `#4181` `M3`):** Intra-shard mutual recursion is discharged jointly inside `Proof/Shard_k.lean` (verified on 2-cycle `even_step <-> odd_step` and 3-cycle `ring_a -> ring_b -> ring_c -> ring_a` in `InterprocCallCanary.lean`). Cross-shard DAG calls either import `Proof.Shard_j` along $G_{\text{SCC}}$ or verify against `Spec` contracts lifted by `#4181` `M3` (`Deriv.linkAxioms`) with `D = 1` parallel `Proof/Shard_*` compilation.

### 4. `TrustedBoundary.lean`, `module` Mode, and Empirical Benchmarks

Basis: source + execution (`support/scc_olean_sharding_prototype.md` Partition 1 §5–§7).

- **Role Lattice Alignment (`target.rs:75-83`, `TrustedBoundary.lean:421-428, 5613-5614, 5882-5900`):** `TargetRole::Capture` permits `Capture -> {Model, Capture}` and rejects `Proof.*` in `"target-audit"`, so `Captured.Shard_*` + `Proof.Shard_*` pass unmodified. `verify.rs:755-761` (`reserved_proof_module`) should extend prefix matching to `"Captured."` and `"Expected."` so user proof modules cannot shadow shards.
- **Crate-Scale Benchmark Matrix (`N = 50..500` cyclic call graphs, `B_max = 20`, 4 workers, `lean -j1 -t0 -DElab.async=false`):**

| $N$ | Shards ($K$) | Variant | Full Wall (s) | Max RSS (MiB) | Root `Proof` (s / MiB) | 1-Body Rebuild (s / MiB) | Status |
| :---: | :---: | :--- | :---: | :---: | :---: | :---: | :--- |
| `50` | `1` | Linear incumbent | `24.222s` | `753.15` | `23.38s / 753.15` | `24.22s / 753.15` | PASS |
| `50` | `3` | **Tarjan SCC Sharded** | `7.248s` | `236.68` | `0.149s / 171.82` | `7.466s / 240.75` (`2/3` cached) | PASS |
| `100` | `1` | Linear incumbent | `57.549s` | `2,237.61` | `56.68s / 2,237.61` | `57.55s / 2,237.61` | PASS (near OOM) |
| `100` | `6` | **Tarjan SCC Sharded** | `13.383s` | `246.76` | `0.208s / 174.78` | `7.556s / 242.76` (`5/6` cached) | PASS + `TrustedBoundary` PASS |
| `250` | `1` | Linear incumbent | `94.474s` | `546.28` | — | — | FAIL (`maxRecDepth = 512`) |
| `250` | `1` | Monolithic `BinChunkTree` | `81.239s` | `1,099.48` | `76.22s / 1,099.48` | `75.825s / 1,098.27` | PASS (`>1 GiB`) |
| `250` | `13` | **Tarjan SCC Sharded** | `24.713s` | `252.82` | `0.234s / 183.12` | `7.232s / 250.69` (`12/13` cached) | PASS (`0` `sorry`, `[propext]`) |
| `500` | `1` | Monolithic `BinChunkTree` | `144.898s` | `2,019.10` | — | — | FAIL (`whnf` timeout `200,000`) |
| `500` | `26` | **Tarjan SCC Sharded** | `43.407s` | `255.89` | `0.359s / 197.46` | `7.315s / 251.54` (`25/26` cached) | PASS (`0` `sorry`, `[propext]`) |

- **Verbatim `google/zerocopy/src/` Captures:** Incumbent linear fails at `maxRecDepth = 512` on `101`-byte `TryFromBytes` paths at both `50` (`28.316s`, `1,532.78 MiB`) and `100` (`29.209s`, `316.27 MiB`) bodies. Tarjan SCC sharding passes `50` bodies in `3.991s` (`236.99 MiB` max RSS) and `100` bodies in `7.481s` (`245.28 MiB` max RSS, `TrustedBoundary` `"target-audit"` PASS: `replay: true`, `exactType: true`, `1,325` replayed decls, `587` `subjectClosure` decls, `["propext"]`).
- **Lean 4 `module` & `v4.35.0` NDJSON (`N = 50`, `3` shards):** `Proof.Shard_000` emits `9,504 B` `.olean` vs. `334,464 B` `.olean.private` (`35.2x` smaller public header); `5a` `expected_cone.ndjson` (`2,815,045 B`, `0.624s`) + `5b` `proof_full.ndjson` (`8,907,387 B`, `0.898s`) pass `nanoda_bin` (`0.875s`, `32.61 MiB`) and `con-ron --verified` (`1.663s`, `200.47 MiB`).

### 5. Eliminated Alternatives and Open Policy Decisions

Basis: derived + execution (`support/scc_olean_sharding_prototype.md` Partition 2 & Partition 3).

- **Eliminated alternatives:** `A0` brownfield linear (`maxRecDepth` / `2.2 GiB` failure); `A1` monolithic `BinChunkTree` (`2,019 MiB` `whnf` failure at $N = 500$); `A2` arbitrary `DefId % K` / alphabetical chunking (splits cyclic SCCs); `A3` 1-body-per-`.olean` (`>3,500` processes $\times$ `150 MiB` startup overhead at `zerocopy` scale); `A4` binary `.olean` `thmInfo -> axiomInfo` patching (breaks `module` invariants and `nanoda_bin`); `A5` mandatory upfront `Program.bodies : BinChunkTree Body` TCB rewrite (unnecessary for $<256 MiB$ scaling).
- **Four open policy/staging decisions (`D1`–`D4`):** (`D1`) default budget `(N_min=20, B_max=20, A_max=2500)` + checked-in `anneal-shards.json` (`--verify-shard-plan`) for static-DAG build systems; (`D2`) ship pure `0`-TCB `Anneal.SccSharding` first with optional 3-line `Enum.lean:stringBeq` cleanup separately; (`D3`) direct acyclic `Proof.Shard_j` imports initially, upgrading to `#4181` `M3` contract linking; (`D4`) classic `.olean` sharding immediately, flipping `isModule: true` once `#4139` Phase 2 lands in `TrustedBoundary.lean`.

## Boundaries

- **not examined (full `4,545`-body `zerocopy` MIR capture end-to-end):** Verbatim `zerocopy/src/` captures exercised `100` bodies currently admitted by MIR Profile v1 (`TryFromBytes` sealing impls and `PointerMetadata`); capturing all `4,545` `zerocopy` bodies additionally requires generic/polymorphic and raw-pointer MIR capture beyond Profile v1 (`4,545` bodies $\approx 228$ shards is projected at `<260 MiB`/shard and `<3s` root `Proof`).
- **not examined (`con-leche` and `lean4lean --import` on sharded NDJSON):** Multi-kernel NDJSON execution ran `nanoda_bin` and `con-ron --verified`; `con-leche` and `lean4lean --import` consume the identical zero-custom-axiom `NDJSON 3.1.0` stream but were not directly invoked in this benchmark run.
- **unsupported (`isModule = true` on target shards at `e8dcb7f08e`):** Live `TrustedBoundary.lean:5615,5650` rejects `isModule = true` on target `Capture`/`Proof` modules (`"module-system artifact unsupported"`) until `#4139` Phase 2 lands.

## Evidence

- **Primary preserved RFC & benchmark specification:** [scc_olean_sharding_prototype.md](support/scc_olean_sharding_prototype.md) (complete 3-partition specification, `capture_shards.json` schema, Lean theorem signatures, probe matrix `P1`–`P6`, and full benchmark tables).
- **Key source anchors at `google/zerocopy@e8dcb7f08edbc19485c9e7980333607ebbff5f48`:**
  - `anneal/trusted/lean/Trusted/MirAst/{Body.lean:164,Terminators.lean:155}`
  - `anneal/trusted/lean/Trusted/MirSemantics/{Boundary.lean:198-200,209-219,267-295,Enum.lean:44-55}`
  - `anneal/trusted/lean/Trusted/MirModel/MirModel.lean:248`
  - `anneal/trusted/rustc-capture/src/{lean.rs:323,publication.rs:95-96}`
  - `anneal/trusted/cargo-anneal/src/{target.rs:62,75-83,verify.rs:755-761}`
  - `anneal/trusted/audit/TrustedBoundary.lean:421-428,5613-5615,5650,5882-5900`

## Revalidation

1. Re-run `anneal-rustc-capture` + `Anneal.SccSharding.BinChunkTree` compilation under `lean -j1 -t0 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` on a `100+`-body verbatim `zerocopy/src/` capture (including `101`-byte `impl TryFromBytes` paths) and check `TrustedBoundary.olean` `"target-audit"` with `0` `Proof.*` `.olean`s mounted.
2. Verify `TrustedBoundary.lean:5615,5650` to check whether `#4139` Phase-2 `isModule` admission has landed on `origin/main` before enabling `isModule = true` for `Captured.Shard_*` / `Proof.Shard_*`.
3. Re-measure peak child `ru_maxrss` across `N = 500` cyclic bodies (`B_max = 20`) to verify `<300 MiB` per-process RSS headroom remains intact as `Trusted.MirSemantics` evolves.
