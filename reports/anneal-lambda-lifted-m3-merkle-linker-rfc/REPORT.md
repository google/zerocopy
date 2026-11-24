# $\lambda$-Lifted Proof Linking, Merkle Constant-Cone Allowlists, Union Tarjan-SCC, and Offline Zero-Axiom Stitching (`M3`)

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Exporting and replaying the full transitive proof terms of shared `anneal/theory/Anneal/` libraries (`Anneal.LinearArith`, `Anneal.BitTrieLrat`, `Anneal.PureLift`) or verified peer-shard callee contracts on every target unit creates redundant kernel replay work. Custom-axiom stubbing (`M1`) fails against bundled `con-ron --verified` and `con-leche --verified` on Lean `v4.35.0` (which reject custom axioms with `exit 2`) and splits kernel coverage (`nanoda_bin` and `lean4lean` catch corrupted `RecursorRule.rhs` payloads where `con-ron` and `con-leche` synthesize recursors and exit `0`). Wrapper-thunk `def`/`opaque` stubbing (`M2`) either provides zero speedup or violates Anneal's `opaque` ban.

This specification defines four coupled, `#[forbid(unsafe_code)]` pure-Rust mechanisms in `cargo-anneal` (`ndjson_comparator.rs`, `stage.rs`, `target.rs`, `verify.rs`, `bundle.rs`) that eliminate redundant proof-cone replay while preserving a **single-artifact, zero-custom-axiom multi-kernel stream**:
1. **Canonical Merkle Constant-Cone Hashing (`cone_digest` vs. `decl_digest`):** Domain-separated SHA-256 over `CanonicalArena` declarations, condensing mutual/nested inductive families (`types`, `ctors`, `recs`, and `cidx`-ordered `RecursorRule`s) into atomic `CanonInductiveBlock`s and binding `ReducibilityHints`, `DefinitionSafety`, positional `NormLevel`s, structured `CanonName` segments, and implicit `NatLit`/`StrLit` primitives.
2. **Option-B Bottom-Up $\lambda$-Lifted Proof Discharge (`M3`):** Validates `Expected.claim` and pre-M3 `Proof.verify` exact types, matches allowlisted `Anneal.*` `Thm` declarations by `(name, num_level_params, cone_digest)`, $\lambda$-lifts references bottom-up across internal `Proof.*` helper `thm`s onto `Proof.verify` as `ForallE`/`Lam` binders (skipping `unliftable_decls` and `has_lifted_ref == false` sub-DAGs in $O(1)$), unions pre-recorded `used_foundation_axioms` and `model_closure` (`Trusted.*`), garbage-collects unreachable proof terms, and emits a closed `0`-custom-axiom `proof_m3.ndjson` checked by all four external kernels (`nanoda_bin`, `con-ron --verified`, `con-leche --verified`, `lean4lean --import`).
3. **Union-Graph Tarjan-SCC Modular Linker (`Tier 4`):** Enforces strict acyclicity across $G_{\text{union}} = (V, E_{\text{mir\_direct}} \cup E_{\text{indirect\_prov}} \cup E_{\text{m3\_hyps}})$ (where $E_{\text{m3\_hyps}}$ comes solely from post-M3 kernel-verified NDJSON outer binders) and enforces `"assumed_callee_contract"` taint + `AssumedContractRealizable` proof witness gating for `Total` external contracts (`Tier 4b`).
4. **Offline Zero-Axiom Stitcher (`Deriv.linkAxioms`):** Merges M3 shard exports with full `Anneal.*` proof exports, enforces `decl_digest` / `InductiveBlock` identity on shared constants, instantiates `Proof.verify` outer binders via nested `Expr::App`s (`0` helper rewrites), and emits a standalone `0`-hypothesis, `0`-custom-axiom NDJSON theorem.

## Applicability

Findings apply to `google/zerocopy` `anneal/trusted/cargo-anneal` at `origin/main` (`a68641199cdfa99f96cb62f0cde921c9d36bfb22`) and PR `#4147` (`57118044690e2026c3f29415780bd5ce75fab211`), targeting the Lean `v4.35.0` NDJSON pipeline (`5-init`, `5a`, `5b`, `5c` with `leanexport` `NDJSON 3.1.0`, `nanoda_bin 0.4.19`, `con-ron --verified`, `con-leche --verified`, `lean4lean --import`). Runtime flag `--full-theory-replay` opts out by substituting `PromotedTheoremAllowlist::empty()` in `5c`.

## Findings

### 1. Pipeline Containment & `leanexport` Literal-Root Invariants

Basis: source + execution (`support/m3_merkle_linker_architecture.md` Partition 1 §2).

- **`leanexport` `PANIC` & `.olean.private` Gate:** `leanexport` (`v4.35.0`) requires `.olean.server` + `.olean.private` companions for `module`-mode compilations and can exit `0` with `0` declarations while printing `PANIC at LeanExport.dumpConstant` on `stderr` when a root constant is absent. Both `run_sandboxed_leanexport` and allowlist builders fail closed on non-empty `PANIC` diagnostics and verify every root exists in `ExportedEnv`.
- **Literal Desugaring Root Completeness:** External kernels (`lean4lean --import`, `nanoda_bin`) desugar `StrLit` via `{String, String.ofList, Char, Char.ofNat, List, List.nil, List.cons}` and `NatLit` via `{Nat, Nat.zero, Nat.succ}`. Stage `5b` and `emit_ndjson` retain these literal-support constants whenever any `NatLit`/`StrLit` is reachable.

### 2. `CanonicalArena`, Atomic `InductiveBlock`, and Dual Merkle Digests

Basis: source + execution (`support/m3_merkle_linker_architecture.md` Partition 1 §3, Partition 2 #5–#6).

- **Cosmetic-Free `CanonExpr` & `NormLevel`:** `Lam`, `ForallE`, and `LetE` strip binder names, `BinderInfo`, `letE.nondep`, and `Expr.mdata` wrappers (`emit_ndjson` restores `"_x"`, `"default"`, and `"nondep": false` for `nanoda_bin`/`lean4lean`). Universe levels resolve `Param(name)` to 0-based `ParamIdx(j)` (failing closed on duplicate `levelParams` or unbound params) and normalize via `simplify_level` (`Succ`, `Max`, `IMax`).
- **Structured `CanonName` & `hash_expr_dag`:** `encode_canon_name` encodes `Anonymous` (`b"N:0"`), `Str` (`b"N:S" || u64_be(len) || bytes`), and `Num` (`b"N:I" || u64_be(n)`) unambiguously without dot-joining. `hash_expr_dag` hashes expressions post-order (`ememo: HashMap<CanonExprId, [u8; 32]>`, `strip_opt_params = false`) with 8-byte BE length prefixes.
- **Atomic `CanonInductiveBlock` (`types`, `ctors`, `recs`):** Any `collect_const_deps` call on one member pulls all `types`, `ctors`, and `recs` (including nested inductive auxiliaries `*.rec_1`). **`RecursorRule`s (`r.rules`) are hashed and emitted strictly in constructor-index (`cidx`) order** (`Probe 6a` showed alphabetical sorting of `Rec.rules` causes all four kernels to reject the recursor).
- **`cone_digest` vs. `decl_digest`:**
  - `cone_digest` (`DigestMode::TheoremSignatureCone`) hashes a `Thm`'s `(name, level_params.len(), H(ty))` and sorted `(dep, cone_digest(dep))` over `ext_deps(ty)` — **excluding `value`** so allowlist matching produces the same digest on a full `Thm` and an `Axiom` stub while catching any mutation in transitive `def` bodies, `ReducibilityHints`, `DefinitionSafety`, or `InductiveBlock`s.
  - `decl_digest` (`DigestMode::FullDeclaration`) additionally hashes `H(value)` and `ext_deps(value)` for offline shard constant deduplication.

### 3. `TheoryAllowlist` and Option-B $\lambda$-Lifted Discharge (`M3`)

Basis: source + execution (`support/m3_merkle_linker_architecture.md` Partition 1 §4, Partition 2 #4).

- **`PromotedTheoremAllowlist` (`theory_allowlist.json`):** Built at compile time by exporting `anneal/theory/Anneal/**`, admitting only non-`_private` `CanonConstInfo::Thm` under `Anneal.` with `0` `Opaque`/`unsafe`/`partial`/`sorryAx` dependencies and axioms $\subseteq \{\text{Classical.choice}, \text{Quot.sound}, \text{propext}\}$. Records `cone_merkle_sha256`, `used_foundation_axioms`, and `model_closure` (`Trusted.*`), parity-checked by `regenerate_bundle --check`.
- **Option-B Algorithm (`verify_ndjson_and_apply_m3`):**
  1. Run pre-M3 checks (39 `PINNED_INIT_PRIMITIVES`, `Quot` post-check, `expected_cone ⊆ proof_full`, `Expected.claim`, and **Step 6 exact pre-M3 `Proof.verify` type check**; reject all `opaque`/`unsafe`/`partial`).
  2. Compute `unliftable_decls = bfs_cone(S_seed)` from `expected_decl_id` and non-`Thm` reachable constants (excluding promoted `Axiom`s); fail closed if any promoted `Axiom` enters `unliftable_decls`, and keep any allowlisted `Thm` in `unliftable_decls` unlifted (`unliftable_kept`).
  3. Verify `A.level_params().len() == entry.num_level_params` and `compute_cone_digest == entry.cone_merkle_sha256` for every `A ∈ LiftedRoots` (`Failure::policy` on mismatch).
  4. Topologically sort internal helper `Thm`s $T_{\text{lift}}$ (`Proof.verify._proof_1`, etc.), collect sorted `(A_m, norm_us_m)` requirements (`<= 512` slots/thm), rewrite `H.ty` and `H.value` at `local_d + (k - 1 - slot_idx)` with `O(1)` skipping via `has_lifted_ref[eid] == false` (valid because closed expressions have `b < local_d`, so prepending $k$ outer binders never shifts original `BVar`s!), and wrap in $k$ `ForallE`/`Lam` binders (`arena.exprs.len() <= max(65_536, 8 * initial_exprs)`).
  5. Verify ground universe levels on `theorem_id`, garbage-collect via `bfs_cone`, assert `0` `LiftedRoots` and `0` custom axioms remain, union `used_foundation_axioms` and `model_closure` into `NdjsonAuditVerdict.axiom_promotion`, and replay `proof_m3.ndjson` across all configured external kernels inside `ExecSeal`.

### 4. Union-Graph Tarjan-SCC (`Tier 4`) and Offline Stitcher (`Deriv.linkAxioms`)

Basis: source + execution (`support/m3_merkle_linker_architecture.md` Partition 1 §5–§7).

- **`verify_modular_shard_dag` (`Tier 4`):** Resolves every non-allowlist outer binder in `m3_lifted_hypotheses` by exact `(name, cone_merkle_sha256)` to a peer `VerifiedShard { shard_id }` or `AssumedExternal` contract, runs iterative Tarjan SCC over $E_{\text{mir\_direct}} \cup E_{\text{indirect\_prov}} \cup E_{\text{m3\_hyps}}$ (rejecting $|C| > 1$ and self-loops), forces `"assumed_callee_contract"` taint + `AssumedContractRealizable` witness for `Total` external contracts (`Tier 4b`), and monotonically unions `axioms`, `sorry_declarations`, `taint_reasons`, and `model_closure` bottom-up.
- **`link_m3_shards_to_zero_axioms` (`Deriv.linkAxioms`):** Initializes `merged_env` from full `theory_env`, alpha-renames shard-local constants under `AnnealLinked.<shard_id>.<orig_name>` when $n > 1$, checks `compute_decl_digest` equality on every shared constant (`Induct`/`Ctor`/`Rec`/`Defn`/`Thm`), applies `Const(target_id, concrete_us)` outer arguments to `verify_id` (`inst_ty == domain_ty` in $O(1)$ `CanonExprId` equality, zero helper `Thm` rewrites), asserts zero custom axioms in the final cone, and emits `linked_zero_axiom.ndjson` (`<= 256 MiB`, `<= 20_000_000` lines).

### 5. Failure Matrix & Eliminated Alternatives

Basis: source + execution (`support/m3_merkle_linker_architecture.md` Partition 1 §7, Partition 2).

- All 10 failure cases (free `Type` carrier, promoted theorem inside `def`, foundation-axiom/closure laundering, `Anneal.Evil` prefix decoy, mutated `def`/`hints`/`Rec.k`/`RecursorRule.rhs`, hidden `.olean.private` `sorryAx`, uninhabited `Total` external contract, MIR/proof circularity, spoofed outer `ForallE` binders on `Proof.verify`, and shard `decl_digest` drift) fail closed (`Failure::policy`, exit `1`) or propagate taint/axioms monotonically.
- Eliminated alternatives: `M1` custom-axiom stubbing, `M2` `def`/`opaque` stubbing, post-`v4.35.0` `con-ron --compare`, Option-A target-only lifting (breaks on `_proof_N` tactic auxiliaries), alphabetical `Rec.rules` sorting (`Probe 6a` falsified across all 4 kernels), and single-digest unification of `cone_digest` + `decl_digest`.

## Boundaries

- **not examined (multi-crate CLI batch wiring):** Future ergonomic CLI flags (e.g., `--zero-axiom-link` batch release orchestration) sit atop `link_m3_shards_to_zero_axioms` and `verify_modular_shard_dag` and were not implemented in the pre-implementation RFC.
- **unsupported (computational `def` promotion & prefix wildcard allowlists):** Only `Prop`-valued `0`-`sorryAx` `Anneal.*` `Thm` declarations may enter `TheoryAllowlist`; computational `def` and `inductive` declarations always remain in `proof_full` / `proof_m3` for kernel `whnf` unfolding.
- **known not to apply (`con-ron`-only recursor validation):** `Probe 1` established that bundled `con-ron --verified` and `con-leche --verified` synthesize recursors and exit `0` on corrupted `RecursorRule.rhs` payloads; `nanoda_bin` and `lean4lean` are required in the quorum to reject `RecursorRule.rhs` corruption.

## Evidence

- **Primary preserved RFC:** [m3_merkle_linker_architecture.md](support/m3_merkle_linker_architecture.md) (complete 3-partition specification, `CanonInductiveBlock` / `PromotedTheoremAllowlist` / `AxiomPromotionReport` / `ModularShardNode` Rust types, Merkle byte encodings, Option-B rewrite algorithm, and 10-row failure matrix).
- **Inspected baselines and live kernel probes (`Probes 1–5`, `Probes 6a–6c`):**
  - `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`origin/main`) and PR `#4147` (`57118044690e2026c3f29415780bd5ce75fab211`: `anneal/trusted/cargo-anneal/src/{ndjson_comparator.rs,stage.rs,target.rs,verify.rs,bundle.rs}`).
  - Lean `v4.35.0` kernels: `nanoda_bin 0.4.19`, `con-ron --verified`, `con-leche --verified`, `lean4lean --import`, and `leanexport` (`NDJSON 3.1.0`).

## Revalidation

1. Replay `Probes 1–6c` against `ndjson_comparator.rs` and the bundled Lean `v4.35.0` quartet (`nanoda_bin`, `con-ron --verified`, `con-leche --verified`, `lean4lean --import`), verifying that `Probe 6a` (mutated `Rec.rules` order) still triggers rejection across all four kernels and `Probe 6b` (`_proof_N` helper `thm`s + `Deriv.linkAxioms`) produces a `0`-axiom linked NDJSON accepted by all four kernels.
2. Run `cargo test -p cargo-anneal` covering `cone_digest` / `decl_digest` sensitivity (`ReducibilityHints`, `Rec.k`, `RecursorRule.rhs`), `unliftable_decls` rejection, `verify_modular_shard_dag` cycle rejection, and `--full-theory-replay` parity.
