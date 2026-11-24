# Architectural Specification: $\lambda$-Lifted Proof Linking, Merkle Constant-Cone Allowlists, Union Tarjan-SCC, and Offline Zero-Axiom Stitching

**Target Repository & Subsystem:** `google/zerocopy` — `anneal/trusted/cargo-anneal` (`src/ndjson_comparator.rs`, `src/stage.rs`, `src/target.rs`, `src/verify.rs`, `src/bundle.rs`)
**Document Type:** Standalone Pre-Implementation Architectural RFC (Three-Partition Format)
**Status:** Settled Specification (`local convergence`)

---

# Partition 1 — Normative Architectural Specification

## 1. Purpose, Scope, Guarantees, and Non-Goals

### 1.1 Purpose and Scope

Anneal's NDJSON verification pipeline (`Action 5-init`, `5a`, `5b`, `5c`) isolates untrusted Lean `.olean` artifacts from the verdict-producing process by exporting kernel declarations through sandboxed `leanexport` (`NDJSON 3.1.0`) and checking the resulting stream in safe Rust (`CanonicalArena`) plus up to four independent external kernels (`nanoda_bin`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import`). When a target proof imports shared verification libraries under `anneal/theory/Anneal/` (such as `Anneal.LinearArith`, `Anneal.BitTrieLrat`, or `Anneal.PureLift`) or verified callee contracts in a multi-unit crate, raw transitive export re-emits and re-typechecks the full proof terms of those shared theorems on every target unit.

This specification defines four coupled mechanisms inside `cargo-anneal` that eliminate redundant kernel replay of pre-verified theorems while preserving a single-artifact, zero-custom-axiom multi-kernel trust boundary and deterministic full-proof reconstructibility:

1. **Canonical Merkle Constant-Cone Hashing (`cone_digest` and `decl_digest`):** Domain-separated SHA-256 digests over `CanonicalArena` declarations, condensing mutual and nested inductive families (`types`, `ctors`, `recs`, and constructor-ordered `RecursorRule`s) into atomic `InductiveBlock`s and binding every transitive computational dependency, reducibility hint, safety flag, and implicit literal primitive.
2. **Merkle-Pinned Promotion Allowlist and Option-B $\lambda$-Lifted Proof Discharge (`M3`):** In-memory transformation in `5c` that verifies pre-transformation `Proof.verify` claims, validates allowlisted theorems against their pinned `cone_digest`, $\lambda$-lifts allowlisted theorem references bottom-up across internal proof helper theorems onto `Proof.verify` as explicit `ForallE`/`Lam` binders, garbage-collects unreachable proof bodies, monotonically unions foundation axioms and `Trusted.*` module closures, and emits a single closed-axiom NDJSON stream accepted unmodified by all four external kernels.
3. **Union-Graph Tarjan-SCC Modular Shard Verification (`Tier 4`):** Pure-Rust dependency-graph validator over modular verification shards enforcing strict acyclicity across the union of direct MIR calls, conservative indirect-call provenance, and post-M3 kernel-extracted proof hypotheses, paired with constructive realizability and taint enforcement for unverified external contracts.
4. **Offline Zero-Axiom Proof Stitching (`Deriv.linkAxioms`):** Pure-Rust bottom-up NDJSON linker that merges M3 shard exports with full `Anneal.*` proof exports, enforces `decl_digest` and `InductiveBlock` identity across shared declarations, instantiates `Proof.verify`'s outer ground binders via nested `Expr::App` terms without rewriting helper theorems, and emits a closed zero-hypothesis, zero-custom-axiom theorem checkable from scratch by all four kernels.

### 1.2 Core Soundness and Security Guarantees

- **G1 — Single-Artifact Zero-Custom-Axiom Kernel Quorum:** Every post-M3 NDJSON stream handed to external kernels contains zero custom `axiom` declarations. Untainted proofs declare at most `{Classical.choice, Quot.sound, propext}` (plus `sorryAx` strictly when `--allow-sorry-in-proof` is active) and execute unmodified through `nanoda_bin` (`unpermitted_axiom_hard_error: true`), `con-ron --verified`, and under `--paranoid-quorum`, `con-leche --verified` and `lean4lean --import` inside `ExecSeal`.
- **G2 — Transitive Statement-Cone Cryptographic Integrity:** A candidate theorem $T$ matches a `PromotionAllowlist` entry only when $T$'s exact full name, universe parameter count, and transitive `cone_digest` match. Modifying any transitive `def` body, `ReducibilityHints`, `DefinitionSafety`, inductive constructor, `Rec.k` flag, or `RecursorRule.rhs` alters `cone_digest` and fails closed (`Failure::policy`, exit code `1`).
- **G3 — Statement and Computational Cone Immutability:** Pre-M3 structural verification enforces `Expected.claim` DAG identity against `5a` (`expected_cone.ndjson`) and checks `Proof.verify`'s exact monomorphic target type before M3 runs. No declaration inside `unliftable_decls` (the transitive dependency cone of `expected_declaration` and all non-`thm` declarations) is ever $\lambda$-lifted or mutated.
- **G4 — Axiom, Closure, and Taint Conservation:** Whenever M3 discharges a promoted hypothesis $A$, `5c` unions $A$'s pre-recorded `used_foundation_axioms`, `model_closure` (`Trusted.*` module attributions), `sorry_declarations`, and `taint_reasons` into the caller's `NdjsonAuditVerdict`. No foundation axiom, candidate semantic tier, or taint atom can vanish across an M3 or modular-shard boundary.
- **G5 — Circular-Proof Exclusion Across Code and Proof Edges:** Modular shard linking rejects every strongly connected component with $|C| > 1$ and every self-loop $(u, u)$ in $G_{\text{union}} = (V, E_{\text{mir\_direct}} \cup E_{\text{indirect\_prov}} \cup E_{\text{m3\_hyps}})$, where $E_{\text{m3\_hyps}}$ is derived solely from post-M3 kernel-verified NDJSON outer binders on each shard's target theorem.
- **G6 — Constructive Zero-Axiom Reducibility:** For every untainted single-unit M3 verdict or acyclic Tier-4 shard DAG backed by `Anneal.*` proofs, offline `Deriv.linkAxioms` deterministically constructs a closed `0`-hypothesis, `0`-custom-axiom NDJSON theorem proving the exact original `Expected.claim`.

### 1.3 Explicit Non-Goals

- **No `unsafe` Rust or `.olean` Deserialization in Verdict Code:** `ndjson_comparator.rs` maintains `#[forbid(unsafe_code)]` and consumes strictly UTF-8 `NDJSON 3.1.0` streams.
- **No Unverified Prefix or Namespace Allowlisting:** Wildcard namespace rules (such as trusting arbitrary `Anneal.*` constants without per-theorem `cone_digest` entries) are prohibited.
- **No Computational `def` Promotion:** Only universe-polymorphic or monomorphic `Prop`-valued `thm` declarations (`CanonConstInfo::Thm` with `0` `sorryAx` and `0` `opaque`/`unsafe`/`partial` dependencies) may enter the bundled `TheoryAllowlist`; computational `def` and `inductive` declarations remain intact in `proof_full` so kernel definitional unfolding (`whnf`) succeeds directly.
- **No Silent Taint Erasure for Unverified External Callees:** Assumed contracts for unverified external or FFI functions always taint the resulting receipt (`"assumed_callee_contract"`) and default to `Partial` termination semantics unless accompanied by a verified `AssumedContractRealizable` proof witness.

---

## 2. Trust Boundaries and Pipeline Placement

```
  [5-init: Clean Sysroot]         [5a: Isolated Trusted Mount]         [5b: Sandboxed Proof Mount]
  39 PINNED_INIT_PRIMITIVES       {Model, Capture, Spec, Expected}     Stage lib (.olean/.server/.private)
             │                                  │                                     │
             ▼                                  ▼                                     ▼
  init_primitives_cone.ndjson         expected_cone.ndjson                 proof_full.ndjson
             │                                  │                                     │
             └──────────────────────────────────┼─────────────────────────────────────┘
                                                ▼
             ┌────────────────────────────────────────────────────────────────────────┐
             │ Action 5c (Part 1): Pure Safe Rust Verifier & M3 Transformer           │
             │  1. Parse NDJSON 3.1.0 -> CanonicalArena + ExportedEnv (InductiveBlock)│
             │  2. Verify 39 Init primitives, Quot post-check, expected_cone ⊆ proof  │
             │  3. Verify Expected.claim root & PRE-M3 Proof.verify exact type        │
             │  4. Reject opaque/unsafe/partial; verify unliftable_decls cone         │
             │  5. Validate promoted candidates against PromotionAllowlist cone_digest│
             │  6. Option-B bottom-up M3 λ-lifting + GC + 0-custom-axiom invariant    │
             │  7. Union inherited axioms & model_closure; emit proof_m3.ndjson       │
             └──────────────────────────────────┬─────────────────────────────────────┘
                                                ▼
             ┌────────────────────────────────────────────────────────────────────────┐
             │ Action 5c (Part 2): External Independent Kernels inside ExecSeal       │
             │  Default:  nanoda_bin (hard_error=true) + con-ron (--verified)         │
             │  Paranoid: + con-leche (--verified) + lean4lean (--import)             │
             └──────────────────────────────────┬─────────────────────────────────────┘
                                                ▼
                     NdjsonAuditVerdict (+ #[serde(deny_unknown_fields)] axiomPromotion)
                                                │
                  ┌─────────────────────────────┴─────────────────────────────┐
                  ▼                                                           ▼
   [Tier 4: Modular Shard DAG Gate]                            [Offline Deriv.linkAxioms Stitcher]
   Tarjan SCC over E_mir ∪ E_indirect ∪ E_m3_hyps              Merges M3 NDJSONs + theory_cone.ndjson
   + Tier-4b AssumedContractRealizable & taint                 -> 0-hypothesis, 0-axiom linked.ndjson
```

### 2.1 Containment Invariants Across Stages

1. **`leanexport` Root-Presence and Panic Enforcement (`5-init`, `5a`, `5b`, and Allowlist Generation):** `leanexport` (`v4.35.0`) requires companion `.olean.server` and `.olean.private` artifacts for `module`-system compilations (exiting `1` when missing and exposing private `def`s and `sorryAx` when present), and can exit `0` with `0` exported declarations if a requested root constant name is absent while writing `PANIC at LeanExport.dumpConstant` to `stderr`. Therefore, `run_sandboxed_leanexport` and allowlist builders reject non-empty `PANIC` diagnostics on `stderr` and `verify_ndjson_structure` / `TheoryAllowlist` builders verify that every requested root constant exists in the parsed `ExportedEnv`.
2. **Literal Desugaring Root Completeness in `5b`:** External kernels (`lean4lean --import` and `nanoda_bin`) desugar `StrLit` via `String.ofList`, `Char.ofNat`, `List.cons`, and `List.nil`, and `NatLit` via `Nat.zero` and `Nat.succ`. Whenever `5b` exports `proof_full.ndjson` (or `emit_ndjson` serializes a garbage-collected `ExportedEnv`), if `PINNED_INIT_PRIMITIVES` are available in `Init`, `5b` appends the literal-support roots (`Nat`, `Nat.zero`, `Nat.succ`, `String`, `String.ofList`, `Char`, `Char.ofNat`, `List`, `List.nil`, `List.cons`) to `leanexport` arguments (or retains them from `init_env` whenever any `NatLit`/`StrLit` is reachable in the GC cone) so `lean4lean --import` never encounters a missing `String.ofList` constant on proofs containing string literals.

---

## 3. Component 1: `CanonicalArena`, Atomic `InductiveBlock`, and Merkle Digests

### 3.1 `CanonicalArena` Extensions (`ndjson_comparator.rs`)

`CanonicalArena` and `ExportedEnv` are extended with complete mutual/nested inductive block grouping and literal primitive IDs while keeping `CanonExpr` cosmetic-free:

- **`CanonExpr` Representation:** `CanonExpr::Lam { ty, body }`, `CanonExpr::ForallE { ty, body }`, and `CanonExpr::LetE { ty, value, body }` strip cosmetic binder names, `BinderInfo`, `letE.nondep`, and `Expr.mdata` wrappers during interning.
- **Atomic `CanonInductiveBlock`:**
  ```rust
  #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  pub struct CanonInductiveBlock {
      /// Mutual inductive type names in exact declaration order (`type_idx`).
      pub types: Vec<CanonNameId>,
      /// Constructor names in exact declaration order.
      pub ctors: Vec<CanonNameId>,
      /// Recursor names (including nested inductive auxiliaries `*.rec_1`) in export order.
      pub recs: Vec<CanonNameId>,
  }
  ```
  - `CanonConstInfo::Induct` gains `recs: Vec<CanonNameId>`.
  - `ExportedEnv` gains `inductive_blocks: HashMap<CanonNameId, usize>` and `blocks: Vec<CanonInductiveBlock>`, mapping every member (`Induct`, `Ctor`, and `Rec`) to its owning `CanonInductiveBlock`.
- **Mutual-Block and Implicit-Literal Dependency Closure (`collect_const_deps`):**
  - Calling `collect_const_deps` (or `collect_const_deps_in_env`) on any member of a `CanonInductiveBlock` includes all `types`, `ctors`, and `recs` of that block, ensuring `bfs_cone` visits every `Rec` and `RecursorRule.rhs` whenever any inductive type or constructor is referenced.
  - `collect_expr_consts` records `{Nat, Nat.zero, Nat.succ}` on `CanonExpr::NatLit` and `{String, String.ofList, Char, Char.ofNat, List, List.nil, List.cons}` on `CanonExpr::StrLit`.

### 3.2 Universe Level Normalization (`NormLevel`)

Within a declaration declaring `level_params = [u_0, ..., u_{r-1}]` (required pairwise distinct; duplicate `levelParams` fail closed during NDJSON parsing):

1. Every `CanonLevel::Param(name)` is resolved to its 0-based positional index `ParamIdx(j)` (`0 <= j < r`); any unbound `CanonLevel::Param` fails closed (`Failure::policy`).
2. `simplify_level` normalizes levels structurally (matching Lean kernel `Level.normalize` / `nanoda_lib` `Level::simplify`):
   - `Succ(l) -> Succ(simplify(l))`
   - `Max(a, b)`: let `a' = simplify(a)`, `b' = simplify(b)`; if `a' == Zero` return `b'`; if `b' == Zero` return `a'`; if `a' == b'` return `a'`; if `a' = Succ(x)` and `b' = Succ(y)` return `Succ(comb_max(x, y))`; else `Max(a', b')`.
   - `IMax(a, b)`: let `a' = simplify(a)`, `b' = simplify(b)`; if `b' == Zero` return `Zero`; if `a' == Zero || a' == Succ(Zero)` return `b'`; if `b' = Succ(_)` return `comb_max(a', b')`; if `a' == b'` return `a'`; else `IMax(a', b')`.

### 3.3 Domain-Separated Merkle Constant-Cone Digest (`cone_digest` vs. `decl_digest`)

All variable-length fields use 8-byte big-endian length prefixes (`u64::to_be_bytes()`).

1. **Structured Name Encoding (`encode_canon_name`):** Encodes the `CanonName` spine from root to leaf without string-dot concatenation so `"a.b"` and `"a" . "b"` or `Num(0)` and `Str("0")` cannot collide:
   - `Anonymous -> b"N:0"`
   - `Str(pre, s) -> encode_canon_name(pre) || b"N:S" || u64_be(s.len()) || s.as_bytes()`
   - `Num(pre, n) -> encode_canon_name(pre) || b"N:I" || u64_be(n)`
   Structured names also define a total canonical order `cmp_canon_name(a, b)` comparing segment sequences `(tag, payload)` lexicographically.
2. **Expression DAG Hashing (`hash_expr_dag`):** Iterative post-order traversal with `ememo: HashMap<CanonExprId, [u8; 32]>` and `strip_opt_params = false`, collecting external constant references `ext_deps` (excluding `internal_block_members`):
   - `BVar(i) -> SHA256(b"E:BV" || u64_be(i))`
   - `Sort(u) -> SHA256(b"E:SO" || encode_norm_level(u))`
   - `Const(c, us) -> SHA256(b"E:CO" || encode_canon_name(c) || u64_be(us.len()) || encode_norm_levels(us))`
   - `App(f, a) -> SHA256(b"E:AP" || H(f) || H(a))`
   - `Lam { ty, body } -> SHA256(b"E:LA" || H(ty) || H(body))`
   - `ForallE { ty, body } -> SHA256(b"E:FA" || H(ty) || H(body))`
   - `LetE { ty, value, body } -> SHA256(b"E:LE" || H(ty) || H(value) || H(body))`
   - `Proj { type_name, idx, struct_expr } -> SHA256(b"E:PR" || encode_canon_name(type_name) || u64_be(idx) || H(struct_expr))`
   - `NatLit(digits) -> SHA256(b"E:NA" || u64_be(digits.len()) || digits.as_bytes())`
   - `StrLit(s) -> SHA256(b"E:ST" || u64_be(s.len()) || s.as_bytes())`
3. **Two Digest Modes (`DigestMode::TheoremSignatureCone` vs. `DigestMode::FullDeclaration`):**
   - For `Axiom`, `Quot`, `Defn` (including `ReducibilityHints` tag+height and `DefinitionSafety`), `Opaque` (including `is_unsafe`), and `CanonInductiveBlock`: both modes hash identical payloads and recurse into `ext_deps` using the same mode (except that `TheoremSignatureCone` evaluates any transitively referenced `Thm` via `TheoremSignatureCone`, keeping computational cones proof-irrelevance-invariant).
   - **Atomic `CanonInductiveBlock` Hashing:** Condenses `members = types ∪ ctors ∪ recs` into a single SCC node (`b"D:IND_BLK"`):
     - `types` are hashed in exact declaration order (`num_params`, `num_indices`, `num_nested`, `is_rec`, `is_unsafe`, `is_reflexive`, `all`, `ctors`, `H(ty)`).
     - `ctors` are hashed in exact declaration (`cidx`) order (`name`, `induct`, `level_params.len()`, `cidx`, `num_params`, `num_fields`, `is_unsafe`, `H(ty)`).
     - `recs` are sorted canonically by `cmp_canon_name(r.name)` (`name`, `level_params.len()`, `num_params`, `num_indices`, `num_motives`, `num_minors`, `k`, `is_unsafe`, `all`, `H(ty)`), while **`r.rules` are preserved strictly in constructor-index (`cidx`) order** (`ctor`, `nfields`, `H(rhs)`).
     - External dependencies `dep ∈ ext_deps \ members` are sorted by `cmp_canon_name` and folded as `(encode_canon_name(dep), digest(dep))`; each member receives `SHA256(b"D:IND_MEM" || encode_canon_name(member) || block_digest)`.
   - **For `CanonConstInfo::Thm`:**
     - `cone_digest` (`DigestMode::TheoremSignatureCone`): hashes ONLY `b"D:THM_CONE" || encode_canon_name(name) || u64_be(level_params.len()) || H(ty)` plus sorted `(dep, cone_digest(dep))` over `ext_deps(ty)`. Proof bodies (`value`) are excluded, so `cone_digest` is identical whether $T$ appears as a full `Thm` or a signature-matching `Axiom` stub!
     - `decl_digest` (`DigestMode::FullDeclaration`): hashes `b"D:THM_FULL" || encode_canon_name(name) || u64_be(level_params.len()) || H(ty) || H(value)` plus sorted `(dep, decl_digest(dep))` over `ext_deps(ty) ∪ ext_deps(value)`.
   - Any cycle outside a `CanonInductiveBlock` fails closed (`Failure::policy`).

### 3.4 Lossless Canonical NDJSON `3.1.0` Serializer (`emit_ndjson`)

`emit_ndjson(arena, env, roots)` garbage-collects `env` from `roots` (retaining full `CanonInductiveBlock`s whenever any block member is visited, plus available `Init` literal-support constants whenever any `NatLit` or `StrLit` expression is visited) and emits deterministic `NDJSON 3.1.0`:

1. Emits `{"meta": ...}` preserving `env.meta`.
2. Assigns sequential `1`-based `"in"`, `"il"`, and `"ie"` indices on demand in topological post-order over reachable declarations:
   - `CanonExpr::Lam` and `CanonExpr::ForallE` emit `"name"` pointing to interned `"_x"` and `"binderInfo": "default"`.
   - `CanonExpr::LetE` emits `"name"` pointing to `"_x"` and `"nondep": false` (required JSON key for `nanoda_bin` and `lean4lean`).
3. Emits declarations in topological dependency order, serializing each `CanonInductiveBlock` once as `{"inductive": {"types": [...], "ctors": [...], "recs": [...]}}` with `types`, `ctors`, `recs`, and `rules` in their exact `cidx`/export order.

---

## 4. Component 2: `TheoryAllowlist` and Option-B $\lambda$-Lifted Discharge (`M3`)

### 4.1 Bundled `TheoryAllowlist` Schema and Generation Invariants

```rust
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PromotedTheoremAllowlist {
    pub schema_version: u32,
    pub theory_manifest_sha256: String,
    pub entries: BTreeMap<String, PromotedTheoremEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PromotedTheoremEntry {
    pub name: String,
    pub module: String,
    pub num_level_params: usize,
    pub cone_merkle_sha256: String,
    pub used_foundation_axioms: Vec<String>,
    pub model_closure: Vec<ClosureEntry>,
}
```

- **Build-Time Generation (`regenerate_bundle` / `theory_allowlist.json`):**
  1. Compiles and exports all `anneal/theory/Anneal/**` modules via `leanexport` (requiring `.olean.server` + `.olean.private` when `module` headers are used, closing `.olean.private` hiding).
  2. Admits **only** non-`_private` `CanonConstInfo::Thm` declarations under the `Anneal.` namespace whose full pre-M3 proof + type cone contains:
     - `0` `CanonConstInfo::Opaque`, `0` `unsafe`/`partial` declarations, and `0` `sorryAx` references;
     - `Axiom` dependencies strictly inside `STANDARD_PERMITTED_AXIOMS` (`{Classical.choice, Quot.sound, propext}`).
  3. Computes `cone_merkle_sha256 = cone_digest(theory_env, thm_id)`, `used_foundation_axioms` (sorted subset of `STANDARD_PERMITTED_AXIOMS` reachable in `thm_id`'s full proof cone), and `model_closure` (`Trusted.*` declarations reachable in `thm_id`'s full proof cone).
  4. Embeds `theory_allowlist.json` into `cargo-anneal` via `bundled_resources.rs` and `bundle.rs` (`regenerate_bundle --check` verifies byte-for-byte parity against `bundled_theory.json` `manifest_sha256`).
- **Runtime Opt-Out (`--full-theory-replay`):** `VerifyArgs` exposes `--full-theory-replay` (`Checker::set_full_theory_replay(true)`), which substitutes `PromotedTheoremAllowlist::empty()` in `5c` so zero `Anneal.*` theorems are promoted and external kernels replay the complete unpruned proof cone.

### 4.2 Unified Pre-M3 Structural Check + Option-B Topological $\lambda$-Lifting (`5c`)

Inside `verify_ndjson_and_apply_m3`:

1. **Steps 1–6 on Raw Pre-M3 `proof_full`:**
   - Execute `PINNED_INIT_PRIMITIVES` pinning, `Quot` post-check, `expected_cone ⊆ proof_full` exact DAG identity, `expected_declaration` canonical root check, statement-origin isolation, `Spec` `Lean.Syntax`/`panic*` ban, and **Step 6 exact pre-M3 `theorem_name` check** (`CanonConstInfo::Thm`, `level_params.is_empty()`, and `ty == expected_const_expr || ty == expected_body`).
   - Reject every `.opaqueInfo` and `unsafe`/`partial` declaration anywhere in `proof_full`.
2. **Identify `unliftable_decls`:**
   - Let $R$ be the raw reachable cone from `[expected_decl_id, theorem_id]` in `proof_full`.
   - Let $S_{\text{seed}} = \{\text{expected\_decl\_id}\} \cup \{c \in R \mid \neg\text{matches!}(c, \text{CanonConstInfo::Thm}\{..\}) \land \neg(c \in \text{PromotedAxioms})\}$, where `PromotedAxioms` are `CanonConstInfo::Axiom { is_unsafe: false, .. }` entries in `R` whose name appears in `allowlist`.
   - Compute `unliftable_decls = bfs_cone(proof_full, S_seed)`.
     - If any `CanonConstInfo::Axiom` in `PromotedAxioms` lies inside `unliftable_decls` (for example, referenced by a `def` or `expected_cone`), **fail closed** (`Failure::policy`), because a valueless axiom inside a computational definition cannot be $\lambda$-lifted!
     - If a `CanonConstInfo::Thm` in `allowlist` lies inside `unliftable_decls` (for example, a decidability or `Fin.mk` bound lemma inside a `def`), keep it unlifted in `unliftable_kept` so its full proof body remains intact in `proof_m3.ndjson`.
3. **Validate Promoted Candidates (`LiftedRoots`):**
   - A constant $A \in R \setminus \text{unliftable\_decls}$ is a promoted root iff `allowlist.entries.get(name(A))` exists and $A$ is either `CanonConstInfo::Thm` or `CanonConstInfo::Axiom { is_unsafe: false }`.
   - Verify `A.level_params().len() == entry.num_level_params` and **`compute_cone_digest(arena, proof_full, A)? == entry.cone_merkle_sha256`**! On any mismatch, return `Failure::policy` immediately.
4. **Option-B Bottom-Up Topological $\lambda$-Lifting Across `Thm`s:**
   - Let $T_{\text{lift}} \subseteq R \setminus (\text{unliftable\_decls} \cup \text{LiftedRoots})$ be the set of internal `CanonConstInfo::Thm` declarations (including `theorem_id`, `_proof_N` tactic helpers, and user `Proof.*` lemmas) that transitively reference at least one $A \in \text{LiftedRoots}$.
   - Topologically sort $T_{\text{lift}}$ (rejecting any `Thm` cycle fail-closed).
   - Maintain `lifted_reqs: HashMap<CanonNameId, Vec<(CanonNameId, Vec<NormLevel>)>>`:
     - Base case for $A \in \text{LiftedRoots}$ with $r$ `level_params`: `lifted_reqs[A] = vec![(A, [Param(0), ..., Param(r-1)])]`.
     - For each $H \in T_{\text{lift}}$ with `level_params` $P_H$ in bottom-up order:
       1. Scan `H.value` (note: `H.ty` cannot reference any $X \in \text{LiftedRoots} \cup T_{\text{lift}}$ with changed type; if `H.ty` references any declaration in $T_{\text{lift}}$ whose type gained binders, fail closed; references to $A \in \text{LiftedRoots}$ inside `H.ty` are impossible because `A : Prop` is proof-irrelevant unless `H.ty` depends on a proof term, in which case scan `H.ty` BEFORE `H.value` and lift across `H.ty` at depth `0..` as well!).
          - *General rule covering dependent `H.ty` too:* Collect all `Const(X, call_us)` occurrences across **both** `H.ty` and `H.value` where $X \in \text{LiftedRoots} \cup T_{\text{lift}}$. Substitute `call_us` (normalized wrt $P_H$) into `lifted_reqs[X]` to obtain deduplicated pairs `(A_m, norm_us_m)` sorted canonically by `(cmp_canon_name(A_m), norm_us_m)`.
          - Enforce `slots.len() <= MAX_LIFTED_HYPS_PER_THM` (`512`).
       2. For each slot $s \in 0..k$ with `(A_s, norm_us_s)`, materialize `concrete_us_s: Vec<CanonLevelId>` wrt `H.level_params` and instantiate `S_s = instantiate_level_params(arena, A_s.ty, A_s.level_params, &concrete_us_s)` (note `A_s.ty` is closed wrt `BVar`s, so `S_s` has zero free `BVar`s!).
       3. Rewrite `H.ty` at initial binder depth `d = k` (`new_ty_core = rewrite(H.ty, d = k)`) and wrap $k$ outer `ForallE` binders:
          `new_ty = ForallE(S_0, ForallE(S_1, ..., ForallE(S_{k-1}, new_ty_core)))`.
          *(When `H == theorem_id`, `H.ty` is `expected_const_expr` or `expected_body` in `expected_cone`, which references zero lifted roots, so `rewrite(H.ty, k) == H.ty` identically because `H.ty` is closed with zero free `BVar`s!)*
       4. Rewrite `H.value` at initial binder depth `d = k` (`new_val_core = rewrite(H.value, d = k)`) using memo table `memo: HashMap<(CanonExprId, u64), CanonExprId>` (enforcing `arena.exprs.len() <= max_m3_exprs`, where `max_m3_exprs = 65_536.max(8 * initial_exprs)`):
          - Subtrees containing zero references to $\text{LiftedRoots} \cup T_{\text{lift}}$ AND zero free `BVar(m)` with $m \ge d - k$ (specifically, every closed helper/subterm or subterm where all `BVar`s are locally bound!) — even simpler and 100% exact:
            Inside any closed input expression `root` (`H.ty` or `H.value`), at local binder depth `local_d` (`0` at `root`, `+1` under each `Lam.body`, `ForallE.body`, `LetE.body`), every original `BVar(b)` satisfies `b < local_d` (fail closed if `b >= local_d`!). Therefore **NO original `BVar(b)` ever shifts** when $k$ binders are prepended outside `root`! And a `Const(X, call_us)` at `local_d` with `lifted_reqs[X] = [(A_j, u_j)]_{j=0..m-1}`:
            - If $X \in \text{LiftedRoots}$ ($m = 1$, $A_0 = X$): rewrites to **`BVar(local_d + (k - 1 - slot_idx(X, norm(call_us))))`**.
            - If $X \in T_{\text{lift}}$ ($m \ge 1$): rewrites to **`App(...App(Const(X, call_us), BVar(local_d + (k - 1 - slot_idx_0))), ..., BVar(local_d + (k - 1 - slot_idx_{m-1})))`**.
            - Skip recursion in `O(1)` via precomputed `has_lifted_ref[eid] == false`: because original `BVar`s never shift, **any sub-DAG with `has_lifted_ref[eid] == false` returns `eid` unchanged in `O(1)` regardless of `local_d`**!
       5. Wrap `new_val_core` in $k$ outer `Lam` binders:
          `new_val = Lam(S_0, Lam(S_1, ..., Lam(S_{k-1}, new_val_core)))`.
5. **Post-M3 Garbage Collection, Zero-Custom-Axiom Gate, and Closure Union:**
   - For `theorem_id` (`level_params == []`), verify every lifted slot `(A_s, concrete_us_s)` has **closed ground universe levels** (`0` `CanonLevel::Param`).
   - Run `bfs_cone` over the M3-rewritten `ExportedEnv` from `[expected_decl_id, theorem_id]` and prune unreachable declarations (`emit_ndjson` -> `proof_m3.ndjson`).
   - Assert **zero** `LiftedRoots` remain in the post-M3 reachable cone and **every** remaining `CanonConstInfo::Axiom` is in `STANDARD_PERMITTED_AXIOMS` (plus `sorryAx` iff `allow_sorry_in_proof`).
   - Compute monotonic provenance unions over `L = lifted_reqs[theorem_id]`:
     - `axioms = post_m3_axioms ∪ ⋃_{(A, _) ∈ L} allowlist[A].used_foundation_axioms`
     - `model_closure = dedup_sort(post_m3_model_closure ∪ ⋃_{(A, _) ∈ L} allowlist[A].model_closure)`
   - Execute `nanoda_bin`, `con-ron --verified`, and (when `--paranoid-quorum`) `con-leche --verified` + `lean4lean --import` on **`proof_m3.ndjson`** inside `ExecSeal`!

### 4.3 `NdjsonAuditVerdict` Receipt Extension

`NdjsonAuditVerdict` (`#[serde(rename_all = "camelCase", deny_unknown_fields)]`) adds an optional `axiom_promotion: Option<AxiomPromotionReport>` field:

```rust
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LiftedHypothesisRecord {
    pub name: String,
    pub universe_levels: Vec<String>,
    pub cone_merkle_sha256: String,
    pub inherited_axioms: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct AxiomPromotionReport {
    pub mode: String, // "m3_lambda_lifted" | "full_theory_replay" | "none"
    pub allowlist_sha256: String,
    pub pre_m3_declarations: usize,
    pub post_m3_declarations: usize,
    pub m3_ndjson_sha256: String,
    pub lifted_hypotheses: Vec<LiftedHypothesisRecord>,
    pub unliftable_kept: Vec<String>,
}
```

---

## 5. Component 3: Union-Graph Tarjan-SCC Modular Shard Linker (`Tier 4`)

### 5.1 Shard Descriptor and Contract Realizability Lattice

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CalleeContractOrigin {
    /// Proven by peer shard `shard_id` in the same verification DAG (`Tier 4a`).
    VerifiedShard { shard_id: String },
    /// Unverified external / FFI callee contract (`Tier 4b`).
    AssumedExternal {
        total_termination: bool,
        realizability_witness_verified: bool,
    },
}

#[derive(Debug, Clone)]
pub struct ModularShardNode {
    pub shard_id: String,
    pub theorem_name: String,
    pub contract_cone_sha256: String,
    pub mir_direct_callees: BTreeSet<String>,
    pub indirect_call_provenance: BTreeSet<String>,
    /// Extracted strictly from post-M3 kernel-verified NDJSON outer binders!
    pub m3_lifted_hypotheses: Vec<LiftedHypothesisRecord>,
    pub local_axioms: BTreeSet<String>,
    pub local_sorry_declarations: BTreeSet<String>,
    pub local_taint_reasons: BTreeSet<String>,
    pub local_model_closure: Vec<ClosureEntry>,
}
```

### 5.2 Union-Graph Construction, Tarjan SCC, and Monotone Taint Propagation (`verify_modular_shard_dag`)

1. **Kernel-Authenticated Proof Dependency Extraction:** For every shard $S_i$, each lifted hypothesis $h \in S_i.\text{m3\_lifted\_hypotheses}$ NOT resolved by `TheoryAllowlist` MUST resolve by exact `(name, cone_merkle_sha256)` to either a `VerifiedShard { shard_id: S_j }` (yielding directed proof edge $S_i \to S_j \in E_{\text{m3\_hyps}}$) or a declared `AssumedExternal` contract; any unresolved or hash-mismatched hypothesis fails closed (`Failure::policy`).
2. **Union-Graph Acyclicity (Tarjan's Strongly Connected Components):**
   - Construct $E(S_i) = E_{\text{mir\_direct}}(S_i) \cup E_{\text{indirect\_prov}}(S_i) \cup E_{\text{m3\_hyps}}(S_i)$ (rejecting any dangling shard ID in $E$).
   - Run iterative/deterministic Tarjan SCC over $(V, E)$:
     - Reject any SCC $C$ with $|C| > 1$ (`Failure::policy("modular-linker", "cyclic modular shard dependency ...")`).
     - Reject any self-loop $S_i \in E(S_i)$ (`Failure::policy("modular-linker", "self-referential modular shard dependency ...")`).
3. **Tier-4b Realizability Gate (`PoC-5b` Closure):**
   - If $S_i$ lifts an `AssumedExternal` contract:
     - Unconditionally insert `"assumed_callee_contract"` into $S_i$'s propagated `taint_reasons`.
     - If `total_termination == true` and `!realizability_witness_verified`, reject fail-closed (`Failure::policy("modular-linker", "assumed Total contract lacks verified AssumedContractRealizable witness")`).
4. **Bottom-Up Semilattice Propagation:** Along reverse topological order ($S_j$ before $S_i$ whenever $S_i \to S_j \in E$), propagate:
   - $\text{axioms}(S_i) \supseteq \bigcup_{S_j \in E_{\text{m3\_hyps}}(S_i)} \text{axioms}(S_j)$
   - $\text{sorry\_declarations}(S_i) \supseteq \bigcup_{S_j \in E(S_i)} \text{sorry\_declarations}(S_j)$
   - $\text{taint\_reasons}(S_i) \supseteq \bigcup_{S_j \in E(S_i)} \text{taint\_reasons}(S_j)$
   - $\text{model\_closure}(S_i) \supseteq \bigcup_{S_j \in E(S_i)} \text{model\_closure}(S_j)$

---

## 6. Component 4: Offline Zero-Axiom Proof Stitcher (`Deriv.linkAxioms`)

### 6.1 Bottom-Up `link_m3_shards_to_zero_axioms` Algorithm

Given a base full-proof `theory_env: ExportedEnv` (exported from `anneal/theory/Anneal/**` with `0` custom axioms) and a topologically ordered slice of verified M3 shards `[Shard_0, ..., Shard_{n-1}]` (with zero `AssumedExternal` contracts):

1. **Shard-Local Namespace Disjointness & Shared-Constant `decl_digest` Gate:**
   - Initialize `merged_env` from `theory_env` inside a shared `CanonicalArena`.
   - For each `Shard_i` in topological order (`0..n`):
     - Define shard-local constants as constants belonging to `Shard_i`'s `Proof` or `Expected` modules (`belongs_to_module`). Alpha-rename shard-local constants injectively under `AnnealLinked.<shard_id>.<orig_name>` when `n > 1` (or preserve `<orig_name>` on single-unit linking when unambiguous, emitting `<theorem_name>_linked`).
     - For every non-local constant `c` in `Shard_i`:
       - If `c` is already in `merged_env`: verify `c.kind_label() == existing.kind_label()` AND **`compute_decl_digest(arena, shard_env, c)? == compute_decl_digest(arena, merged_env, c)?`** (which for any `Induct`/`Ctor`/`Rec` verifies the entire `CanonInductiveBlock` digest and identical member list!). Fail closed on any discrepancy.
       - Otherwise insert `c` (and its full `CanonInductiveBlock` if inductive) into `merged_env`.
2. **Exact Ground Application Stitching (`0` Helper Rewrites):**
   - Let `verify_id` be `Shard_i`'s M3-lifted `CanonConstInfo::Thm` in `merged_env` (`cur_ty = verify_id.ty`, `app_val = Const(verify_id, [])`).
   - For each lifted hypothesis descriptor `(hyp_name, concrete_us)` recorded on `Shard_i` in exact outer binder order `0..k`:
     - Destructure `cur_ty` as `CanonExpr::ForallE { ty: domain_ty, body: next_ty }` (fail closed if not `ForallE`, or if `domain_ty`/`next_ty` contains free `BVar(0)` since outer M3 binders are non-dependent `Prop` implications; verify `has_loose_bvar_zero(next_ty) == false`!).
     - Resolve `hyp_name` to `target_id` in `merged_env` (either a `0`-hypothesis theorem in `theory_env` or `Shard_j`'s `verify_linked` with $j < i$).
     - Instantiate `inst_ty = instantiate_level_params(arena, target_thm.ty, target_thm.level_params, &concrete_us)?` and verify **`inst_ty == domain_ty`** (`O(1)` `CanonExprId` equality in `CanonicalArena`!).
     - Advance `app_val = intern_expr(App(app_val, Const(target_id, concrete_us)))` and `cur_ty = next_ty`.
   - Verify final `cur_ty` equals `Shard_i`'s `expected_const_expr` or `expected_body`.
   - Insert `CanonConstInfo::Thm { name: linked_id, level_params: vec![], ty: cur_ty, value: app_val, all: vec![linked_id] }` into `merged_env` and bind `Shard_i`'s theorem reference in `linked_map` to `linked_id`.
3. **Final Zero-Axiom Verification & Serialization:**
   - Run `bfs_cone` from the root shard(s)' `[expected_id, linked_id]`.
   - Assert **zero** custom `CanonConstInfo::Axiom` declarations exist in the cone (strictly subset of `STANDARD_PERMITTED_AXIOMS`).
   - Emit `linked_zero_axiom.ndjson` via `emit_ndjson` (`<= MAX_NDJSON_BYTES`, `<= MAX_NDJSON_LINES`), ready for standalone replay through `nanoda_bin`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import`.

---

## 7. Failure Matrix and Verification Plan

| Threat / Boundary Case | Failing Gate & Invariant | Expected Outcome |
|---|---|---|
| Free `Type` carrier / non-theorem axiom (`(α : Type) -> Nonempty α -> False`) | Allowlist admits only `0`-`sorryAx` `CanonConstInfo::Thm` from verified `theory/` export; unallowlisted custom `Axiom` fails post-M3 zero-custom-axiom gate | `Failure::policy` (`code == 1`) |
| Promoted theorem used inside computational `def` or `Expected.claim` | `unliftable_decls` cone exclusion keeps `Thm` body unlifted; if input was a valueless `Axiom`, `PromotedAxiom ∈ unliftable_decls` check rejects | `Thm` kept & kernel-checked, or `Failure::policy` (`code == 1`) |
| Foundation axiom (`Classical.choice`) or `Trusted.*` module used only inside promoted proof body | `PromotedTheoremEntry.{used_foundation_axioms, model_closure}` monotonically unioned into `NdjsonAuditVerdict` | `Classical.choice` & `Trusted.*` preserved in verdict/receipt |
| Decoy `Anneal.Evil.forged_false` under `Anneal.` namespace prefix | Exact full-name lookup + `cone_merkle_sha256` check (zero prefix wildcards) | `Failure::policy` (`code == 1`) |
| Mutated `def` body (`UnsatCnf := False`), `ReducibilityHints`, `Rec.k`, or `RecursorRule.rhs` under identical theorem AST | Atomic `CanonInductiveBlock` + transitive `cone_digest` mismatch against `allowlist[T].cone_merkle_sha256` | `Failure::policy` (`code == 1`) |
| `module` `.olean` hiding private `def` or `sorryAx` in `.olean.private` | `leanexport` loads `.olean.private` (exiting `1` if absent) and exposes `sorryAx` to allowlist builder and `5c` | `Failure::policy` (`code == 1`) |
| Unverified external `Total` contract with uninhabited postcondition (`x < bump_id x` at `u64::MAX`) | `AssumedExternal` requires `"assumed_callee_contract"` taint + `AssumedContractRealizable` witness for `Total` | `Failure::policy` (`code == 1`) / tainted receipt |
| Direct MIR recursion (`f <-> g`), `0`-call MIR + mutual proof cycle, or indirect callback self-loop | `verify_modular_shard_dag` Tarjan SCC over $E_{\text{mir\_direct}} \cup E_{\text{indirect\_prov}} \cup E_{\text{m3\_hyps}}$ | `Failure::policy` (`code == 1`) |
| Pre-M3 `Proof.verify` spoofing extra outer `ForallE` binders | Pre-M3 Step 6 verifies `Proof.verify.ty == Expected.claim` *before* M3 runs | `Failure::policy` (`code == 1`) |
| Shared constant or `InductiveBlock` drift between shards during offline `Deriv.linkAxioms` | `compute_decl_digest` equality gate during shard ingestion | `Failure::policy` (`code == 1`) |

---

# Partition 2 — Decision Rationale and Eliminated Alternatives

1. **Elimination of Custom-Axiom Stubbing (`M1`) and Split-Kernel Execution:**
   - *Alternative:* Replace pre-verified theorems with custom `axiom` records in NDJSON and pass them via `nanoda_bin`'s `permitted_axioms` list while skipping `con-ron --verified` and `con-leche --verified`.
   - *Basis for Elimination (`C+1`, `C-2`, `PROBED`):* Bundled `con-ron --verified` and `con-leche --verified` on Lean `v4.35.0` enforce `no_False_declaration` strictly over `{propext, Quot.sound, Classical.choice}` and reject any custom `axiom` (`exit 2`). Furthermore, `Probe 1` demonstrated that `nanoda_bin` and `con-ron` catch disjoint classes of malformed NDJSON (`nanoda_bin` and `lean4lean` catch corrupted `RecursorRule.rhs` where `con-ron --verified` and `con-leche --verified` synthesize recursors and exit `0`). Preserving all four kernels on one zero-custom-axiom artifact (`M3`) is strictly stronger than any split-kernel design.
2. **Elimination of Wrapper-Thunk `def` / `opaque` Stubbing (`M2`):**
   - *Alternative:* Replace theorem proof bodies with `def` or `opaque` declarations.
   - *Basis for Elimination (`C+1`, `PROBED`):* Lean kernels typecheck `def` values identically to `thm` values (yielding zero replay speedup), while `opaque` declarations are banned across Anneal's NDJSON comparator because Lean's `CollectAxioms` skips `.opaqueInfo` bodies.
3. **Elimination of Upstream Post-`v4.35.0` `con-ron --compare` / `--modular` as Primary Mechanism:**
   - *Alternative:* Delegate modular theorem stubbing to `con-ron --compare` / `--modular`.
   - *Basis for Elimination (`C+1`, `C+2`, `PROBED`):* Bundled Lean `v4.35.0` binaries predate `--compare`/`--modular`; `nanoda_bin` and `lean4lean` have no `--compare` mode; and `con-ron --verified` does not validate exported `RecursorRule.rhs` payloads against synthesized recursors (`Probe 1`). Pure-Rust M3 + `InductiveBlock` Merkle cones work uniformly across all four existing kernels today.
4. **Selection of Option B (Bottom-Up Helper `thm` Topological $\lambda$-Lifting) over Option A (Target-Only Lifting):**
   - *Alternative:* Rewrite only `Proof.verify.value` and fail closed if any internal `Proof.*` helper `thm` references a promoted theorem.
   - *Basis for Elimination (`C+3`, `PROBED` `Probe 6b`):* Lean 4's tactic elaborator (`by`, `simp`, `abstractProof`, equation-compiler splitters) routinely extracts subproofs into auxiliary `thm` declarations (`Proof.verify._proof_1`, etc.). Option B lifts promoted hypotheses bottom-up across monomorphic and universe-polymorphic helper `thm`s in ~80 lines of safe Rust while leaving helper `thm`s as valid `0`-axiom declarations that require **zero** modification during offline `Deriv.linkAxioms` linking (`Probe 6b`).
5. **Preservation of Constructor-Index (`cidx`) Order on `RecursorRule`s (`Probe 6a`):**
   - *Alternative:* Alphabetically sort `Rec.rules` by constructor name in Merkle hashing and NDJSON emission.
   - *Basis for Elimination (`PROBED: falsified` in `Probe 6a`):* Reordering `Rec.rules` out of constructor-index (`cidx`) order causes **all four kernels** (`nanoda_bin`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import`) to reject the exported recursor. Constructor order (`cidx`) is already canonical and semantically fixed by the inductive declaration, so preserving `cidx` order in both `InductiveBlock` hashing and `emit_ndjson` is both deterministic and kernel-valid.
6. **Separation of `cone_digest` (`TheoremSignatureCone`) vs. `decl_digest` (`FullDeclaration`):**
   - *Alternative:* Use a single digest mode for both allowlist matching and offline shard constant deduplication.
   - *Basis for Elimination (`C+2`, `C+6`):* Allowlist matching must produce the same digest whether a theorem arrives as a full `Thm` (from prebuilt `.olean`s) or an `Axiom` stub (`value`-invariant `cone_digest`), whereas offline linking deduplicating shared helper `Thm` declarations across shards must verify that their proof terms (`value`) also agree (`decl_digest`).

---

# Partition 3 — Open Human Decisions, Full Contract, and Epistemic Calibration

## 1. Open Human Policy Decisions

- **Zero Blocking Policy Deficits (`0` `provisional` clauses, `0` `undecided policy values`):**
  - Default `cargo anneal verify` executes in-memory M3 $\lambda$-lifting (`--full-theory-replay` opts out to full-cone replay).
  - Resource ceilings (`MAX_NDJSON_BYTES = 256 MiB`, `MAX_NDJSON_LINES = 20_000_000`, `MAX_LIFTED_HYPS_PER_THM = 512`, `MAX_M3_EXPRS` floor `65_536` / `8x` input expressions) are strictly plumbing-invariant safety guards.
  - Future ergonomic CLI wiring for multi-crate `--zero-axiom-link` batch release workflows builds directly on the pure-Rust `link_m3_shards_to_zero_axioms` and `verify_modular_shard_dag` APIs delivered in `ndjson_comparator.rs` without altering any receipt or kernel contract.

## 2. Complete Sealed Outcome Contract `(C+, C-)`

- **`C+` (Confirmed Positive Obligations):**
  - `C+1`: Single-artifact zero-custom-axiom NDJSON output checkable unmodified by `nanoda_bin`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import` on Lean `v4.35.0`.
  - `C+2`: Canonical transitive Merkle constant-cone hashing (`cone_digest`) condensing mutual/nested `InductiveBlock`s (`types`, `ctors`, `recs`, `cidx`-ordered `rules`), `Defn.{hints,safety}`, `Rec.k`, positional `NormLevel`s, structured `CanonName` segments, and implicit literal primitives.
  - `C+3`: Pre-M3 `Proof.verify` exact-type validation, `unliftable_decls` cone exclusion, and Option-B bottom-up helper-`thm` $\lambda$-lifting with `(eid, local_d)` memoization and `has_lifted_ref` `O(1)` subtree skipping.
  - `C+4`: Monotonic union of `used_foundation_axioms` and `model_closure` (`Trusted.*` attribution), `#[serde(deny_unknown_fields)]` `axiomPromotion` receipt reporting, and `--full-theory-replay` opt-out.
  - `C+5`: Tarjan union-SCC acyclicity enforcement over $E_{\text{mir\_direct}} \cup E_{\text{indirect\_prov}} \cup E_{\text{m3\_hyps}}$ (with $E_{\text{m3\_hyps}}$ extracted from post-M3 kernel-verified NDJSON) plus Tier-4b `"assumed_callee_contract"` taint, `Partial` default, and `AssumedContractRealizable` gate for `Total`.
  - `C+6`: Pure-Rust bottom-up `Deriv.linkAxioms` stitcher reconstructing a closed `0`-hypothesis, `0`-custom-axiom NDJSON stream verified across shared `decl_digest` / `InductiveBlock` identities and exact universe arguments `us_m`.
- **`C-` (Confirmed Exclusions):**
  - `C-1`: Zero `unsafe` Rust, zero `.olean` deserialization in the verdict process, and zero new external Cargo crates.
  - `C-2`: Zero split-kernel execution or custom axioms in external kernel inputs.
  - `C-3`: Zero prefix-wildcard allowlists, zero AST-only hashing, and zero MIR-only call-graph trust for proof acyclicity.
  - `C-4`: Zero silent dropping of foundation axioms, `Trusted.*` module closures, or assumed-callee taints.

## 3. Pre-Delivery Read-Only Audit & Epistemic Calibration

- **Stopping Status & Deliverability:** `local convergence` — Settled Standalone RFC.
- **Stage 2 Mandatory Pre-Delivery Read-Only Audit:** Executed read-only over the converged Stage 4 specification; verified `(1)` direct `C+`/`C-` compliance, `(2)` zero hardcoded domain-dependent bounds, `(3)` explicit clause-to-machinery attribution, `(4)` zero unfactored runtime knobs, `(5)` zero hidden `superset-taxed boundaries`, and `(6)` zero `PROBED: falsified` claims (`Rec.rules` reordering, `con-ron`-only recursor checking, bare `leanexport` `rc == 0` trust) presented as viable.
- **Primary Evidence Basis (`PROBED` `[real measurement]` on Lean `v4.35.0`):**
  - Direct source inspection of `google/zerocopy` PR `#4147` (`57118044690e2026c3f29415780bd5ce75fab211`: `ndjson_comparator.rs`, `stage.rs`, `target.rs`, `verify.rs`, `bundle.rs`) and `origin/main` (`a68641199cdfa99f96cb62f0cde921c9d36bfb22`).
  - Eight live reproducible kernel probe suites (`Probes 1–5`, `Probes 6a–6c`) executed across `nanoda_bin 0.4.19`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import` on Lean `v4.35.0`.
- **Peer Composition Notes:** Applied structured architectural specification, conceptual model simplification, and reader-oriented clarity passes; multi-round empirical inquiry partnered with `reference-research` on Lean `v4.35.0`.

*Authored by an AI agent acting on joshlf's behalf.*
