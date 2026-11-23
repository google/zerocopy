# Lambda-Lifted NDJSON Proof Linking, Canonical Merkle Constant-Cone Allowlists, and Union-Graph Tarjan-SCC Discharge

## Summary

Split-phase checking of Lean 4 export NDJSON (`3.1.0`) streams faces a concrete compatibility and soundness constraint across independent external checkers (`nanoda_bin`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import`). Replacing pre-checked library theorems or upstream shard proofs with custom `axiom` declarations fails closed under bundled Lean `v4.35.0` `con-ron --verified` and `con-leche --verified`, which reject non-standard axioms, while `lean4lean --import` accepts arbitrary axioms without an allowlist check. In contrast, **lambda-lifted proof linking**—lifting allowlisted `Prop` theorem instantiations out of proof terms into outer universally quantified hypotheses (`ForallE` on the theorem type and `Lam` on its proof term), then discharging those hypotheses offline by application—produces **zero-custom-axiom** NDJSON artifacts accepted simultaneously by all four independent checkers.

Empirical probes against Lean `v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and all four kernels establish six concrete architectural invariants required for sound deployment:

1. **Atomic `InductiveBlock` Merkle Constant-Cone Pinning:** Pinning only a promoted theorem's syntactic type AST allows downstream definition drift to forge `False`. Moreover, live mutation probes demonstrate that `con-ron --verified` and `con-leche --verified` synthesize recursors and return `rc=0` on corrupted `RecRule.rhs` entries in NDJSON (whereas `nanoda_bin` panics with `rc=101` and `lean4lean` rejects with `rc=1`), and all four kernels accept mutating `Defn.hints` from `regular` to `opaque` (`rc=0`). A canonical Merkle cone digest must therefore condense each mutual inductive block `{types, ctors, recs}` as an atomic strongly connected node, hash structured `Name` segments (`N:ANON` / `N:STR` / `N:NUM`), apply `Level.simplify` with positional `ParamIdx(i)` alpha-renaming, include `Defn.{hints, safety}`, `Rec.k`, and `Rec.rules`, and record full implicit literal dependencies (`Nat.{zero, succ}`, `String.ofList`, `List.{nil, cons}`, `Char.ofNat`).
2. **Lossless Canonical NDJSON Re-Serialization Constraints:** `leanexport` (`Export.lean`) normalizes `letE.nondep` to `false` and hash-conses expressions via traversal-dependent `Expr.eqv`, causing cosmetic binder-name drift across separate exports of identical imports. All four kernels accept canonicalized `binderInfo = "default"`, normalized binder names (`"_x"`), and `"nondep": false` across nested (`numNested = 1`) and mutual inductives—**provided** (a) the `"nondep"` key is present (`nanoda_bin` and `lean4lean` reject its omission), (b) `Rec.rules` strictly preserves constructor-index (`cidx`) order (reversing or alphabetically sorting `rules` fails **all four kernels**, whereas reordering `recs` passes all four), and (c) surviving `in`/`il`/`ie` back-reference indices are compacted contiguously after garbage collection (`nanoda_bin` rejects sparse IDs).
3. **Bottom-Up Topological Helper-Theorem Lambda-Lifting:** Because Lean 4's elaborator extracts tactic subproofs into auxiliary theorems (`_proof_1`, universe-polymorphic helpers), lifting only the top-level target theorem rejects valid proofs. Bottom-up topological lifting across all non-`unliftable` `thm` declarations propagates universe-polymorphic hypothesis instantiations (`max v 1`) up to the monomorphic entrypoint's canonical ground binders, keeps `def`-referenced theorems intact (`unliftable_decls`), preserves DAG sharing via `(eid, depth)` memoization (`1.203x` expansion across 40 nested `let`/`lam` scopes), and allows offline zero-axiom application stitching to instantiate **only** the entrypoint without modifying helper theorems (`4/4` kernels `rc=0`).
4. **Union-Graph Tarjan-SCC Acyclicity and Offline Zero-Axiom Stitching:** Checking acyclicity over only direct program call edges misses both mutual proof-hypothesis cycles without program calls and indirect-call callback self-loops. Running Tarjan's SCC algorithm over the union graph `E_direct ∪ E_indirect_provenance ∪ E_kernel_m3_hypotheses` (extracting hypothesis edges strictly from post-lifting NDJSON rather than source annotations) rejects all cycles and self-loops (`|SCC| > 1` or `(u, u) ∈ E`). Bottom-up offline application stitching over the verified DAG—preserving exact universe argument lists `us_m`, enforcing shared-declaration Merkle equality, and alpha-renaming shard-local namespaces—recovers a single closed, zero-custom-axiom proof artifact verified by all four checkers (`4/4` `rc=0`).
5. **Lean 4 `module` Visibility Under `leanexport` and Panic Hygiene:** On Lean `v4.35.0` `module` artifacts (`.olean`, `.olean.server`, `.olean.private`), `leanexport` loads full `.private` visibility (exporting unexposed `public def` as `def` and exposing `sorryAx` in private theorem proofs) and fails closed (`rc=1`) if either `.olean.private` or `.olean.server` is missing. However, requesting a nonexistent constant name prints `PANIC at LeanExport.dumpConstant` to `stderr`, emits zero declarations, and exits **`rc=0`**, so callers must never rely on `leanexport`'s exit status alone.
6. **Monotonic Axiom/Feature Union and Assumed-Contract Realizability:** Because lambda-lifting removes lifted theorem bodies from the per-shard NDJSON stream, auditors must union each allowlisted hypothesis's pre-lifting foundation axioms (`{propext, Quot.sound, Classical.choice}`) and semantic-model feature closure into the final verdict, disallow `sorryAx` in allowlists, and gate unverified external callee contracts behind explicit tainting, `Partial` termination defaults, and constructive realizability witnesses when `Total` termination is claimed.

## Applicability

These findings apply to formal verification pipelines that export Lean 4 `3.1.0` NDJSON proof streams for multi-kernel replay, split-phase checking of pre-verified theory libraries, or modular shard-level verification of programs with an optional offline whole-program zero-axiom linker.

They extend—without duplicating—prior reference reports in this corpus:

- `reports/precompiled-theorems-split-phase-checking-and-reflective-schemas-prior-art-2026/` (cross-prover split-phase checking taxonomy and `ConservativityModel.lean` for static `.olean` stubbing).
- `reports/tarjan-scc-proof-sharding-acyclic-interface-digests-and-incremental-olean-auditing/` and `reports/merkle-bound-scc-axiom-propagation-and-balanced-chunk-trees-for-large-ast-elaboration/` (SCC sharding and `.olean`-level Merkle digests).
- `reports/lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb/` and `reports/anneal-trusted-boundary-audit-olean-stubbing-and-conservativity/` (Lean 4 external checker TCBs and `.olean` stubbing conservativity).
- `reports/lcf-abstract-kernels-dedukti-lambdapi-modulo-rewriting-and-fpc-certificates/` and `reports/metamath-zero-mm0-self-verifying-x86-bootstrap-and-machine-code-kernels/` (Dedukti/Lambdapi and MM0/MMB interface designs).

Whereas those reports analyze `.olean`-level sharding, reflective checking, and general checker TCBs, this report isolates the **NDJSON `3.1.0` expression-graph canonicalization, inductive-block hashing, topological `Prop` lambda-lifting, and offline zero-axiom application stitching** invariants, together with upstream November 2026 `con-ron --compare`/`--modular` developments.

## Findings

### 1. Canonical Merkle Transitive Constant-Cone Hashing Over Export NDJSON `3.1.0`

Hashing only a promoted theorem's syntactic type expression (`CanonExpr`) is unsound when computational definitions (`Defn`) or inductive recursors (`Induct`/`Ctor`/`Rec`) referenced by that type can vary across environments. A sound allowlist and shared-declaration deduplicator requires a cycle-safe, domain-separated Merkle SHA-256 over the full transitive constant cone.

#### 1.1 Empirical Kernel Blind Spots Motivating Atomic `InductiveBlock` Condensation

In Lean 4 export NDJSON `3.1.0` (`leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`), an inductive declaration record bundles `types`, `ctors`, and `recs` together, while internal comparator representations often index `Induct`, `Ctor`, and `Rec` separately and omit `Rec` edges when traversing from `Induct`. Mutating a single compiled `Probe1.MyNat` export stream (`33` declarations, `support/probe_ndjson_m3_merkle_linker.py`) yields four distinct kernel behaviors:

| NDJSON Mutation on `Probe1.MyNat` / `toNat` | `nanoda_bin` | `con-ron --verified` | `con-leche --verified` | `lean4lean --import` | Merkle Cone Changed |
|---|---:|---:|---:|---:|---:|
| Corrupt `MyNat.rec` `rules[1].rhs := rules[0].rhs` | `rc=101` (`src/tc.rs:955:71` panic) | **`rc=0`** (`accepted 33 declarations`) | **`rc=0`** (`accepted 33 declarations`) | `rc=1` (`Invalid recursor`) | **`true`** |
| Mutate `toNat.hints` (`regular` -> `opaque`) | **`rc=0`** | **`rc=0`** | **`rc=0`** | **`rc=0`** | **`true`** |
| Flip `MyNat.rec` `k` (`false` -> `true`) | `rc=101` (`src/inductive.rs:1330:21` panic) | `rc=1` (`not K-like`) | `rc=1` (`not K-like`) | `rc=1` (`Invalid recursor`) | **`true`** |

Because `con-ron --verified` and `con-leche --verified` synthesize recursor computation rules internally rather than checking exported `rules[].rhs`, and because all four checkers accept tightening `Defn.hints` to `opaque` (which alters downstream definitional reduction without making the mutated stream itself ill-typed), a Merkle cone digest must hash the entire mutual inductive clique `{types, ctors, recs}` atomically and include `Defn.{hints, safety}`, `Rec.k`, and every `RecRule.{ctor, nfields, rhs}`.

#### 1.2 Exact Canonicalization Rules

1. **Structured `Name` Segment Hashing:** Serialize hierarchical `Name`s segment-by-segment using explicit tags (`N:ANON`, `N:STR(len, utf8)`, `N:NUM(u64)`) rather than joining with `"."`, avoiding theoretical aliasing between `"a.b"` and `"a"."b"` or numeric segment `.0` and string `"0"`.
2. **Universe Level Canonicalization:** Apply `Level.simplify` (matching `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, `src/level.rs`: `max(0, r) = r`, `max(l, 0) = l`, `max(S(a), S(b)) = S(max(a, b))`, `max(l, l) = l`, `imax(l, 0) = 0`, `imax(l, S(r)) = max(l, S(r))`, `imax(0/1, r) = r`) and alpha-rename `Level.Param` names to positional `ParamIdx(i)` relative to the enclosing declaration's `levelParams`. Reject any unbound `Level.Param` fail-closed.
3. **Expression Normalization (`Expr.eqv` Alignment):** Separate `leanexport` invocations on identical upstream imports emit different cosmetic binder `name` IDs (observed on `outParam` and `HAdd.hAdd` across independent exports) because `lean4export` hash-conses via traversal-order-dependent `Expr.eqv`. Canonical hashing strips cosmetic binder names (`lam`, `forallE`, `letE`), `binderInfo`, `letE.nondep`, and `mdata` wrappers (`H(mdata(_, e)) = H(e)`). Dependency traversal must **never** strip `optParam`/`autoParam` arguments (`strip_opt_params = false`).
4. **Implicit Literal Dependencies:** Verified in `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`src/expr.rs:580-640`, `nat_lit_to_constructor` and `str_lit_to_constructor`), external kernels expand `NatLit` via `{Nat, Nat.zero, Nat.succ}` and `StringLit` via `{String, String.ofList, List, List.nil, List.cons, Char, Char.ofNat}` (plus `Nat.*`). Both Merkle cone dependency edges and NDJSON garbage-collection roots must include these implicit constants whenever a literal occurs.
5. **Atomic `InductiveBlock` Condensation and Two-Digest Split:** Condense all `types`, `ctors`, and `recs` of a mutual/nested inductive record into one SCC node, hash `types`, `ctors`, and each `Rec`'s `rules` in exact positional (`cidx`) order while sorting `recs` canonically by structured `Name`, collect external dependencies outside the clique in sorted `Name` order, and derive each member's digest as `H("D:IND_MEM" || segs(member) || block_digest)`. Separate **`cone_digest(thm)`** (hashes `levelParams` arity, `type`, and `type`'s transitive cone—invariant across full proof vs. lambda-lifted stub) from **`decl_digest(c)`** (hashes `thm.value` as well, for strict declaration deduplication during offline linking).

### 2. Lossless Canonical NDJSON Re-Serialization Across Four Checkers

When transforming an in-memory canonical expression arena back into NDJSON `3.1.0` for multi-kernel replay, five wire-level invariants govern acceptance across all four checkers (`Probe 2` in `support/probe_ndjson_m3_merkle_linker.py`, `78` declarations covering dependent `let x : Nat := 2; Fin (x + 1)`, non-dependent `have`, all four `binderInfo` variants, nested `Rose` with `numNested = 1`, and mutual `Even`/`Odd`):

| Re-Serialization Property | `nanoda_bin` | `con-ron --verified` | `con-leche --verified` | `lean4lean --import` | Required Emitter Rule |
|---|---:|---:|---:|---:|---|
| Canonical `binderInfo = "default"`, binder names `"_x"`, `"nondep": false`, `rules` preserved | `rc=0` | `rc=0` | `rc=0` | `rc=0` | Safe lossless round-trip across nested (`numNested=1`) and mutual inductives. |
| Flip `"nondep"` to `true` on all `11` `letE` nodes | `rc=0` | `rc=0` | `rc=0` | `rc=0` | All four kernels ignore `nondep`'s boolean value (`Export.lean:141-147` emits `false`). |
| Omit `"nondep"` key from `letE` JSON | **`rc=1`** (`missing field`) | `rc=0` | `rc=0` | **`rc=1`** (`Expr.letE invalid`) | Always serialize `"nondep": false` (arena need not store a `bool`). |
| Reverse `recs` order only (`Rose.rec_1 <-> Rose.rec`, `Even.rec <-> Odd.rec`) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | Sorting `recs` by structured `Name` is accepted by all four checkers. |
| Reverse `rules` order only (`Nat.zero <-> Nat.succ`) | **`rc=101`** (`src/inductive.rs:1315:9`) | **`rc=1`** (`reserved basis name`) | **`rc=1`** (`reserved basis name`) | **`rc=1`** (`Invalid recursor`) | **Never** sort `Rec.rules` alphabetically; preserve constructor-index (`cidx`) order. |
| Sparse `in`/`il`/`ie` IDs after GC (non-contiguous indices) | **`rc=2`** (`Back-refs must be continuous`) | `rc=0` | `rc=0` | `rc=0` | Compact surviving `in`/`il` (`1..N`) and `ie` (`0..E-1`) contiguously during GC emission. |

### 3. Soundness-Preserving Topological Lambda-Lifting (`M3`)

#### 3.1 Pre-Lifting Gate and `unliftable_decls` Exclusion

To prevent a proof script from spoofing extra leading hypotheses before lifting runs, the verifier must check that the **pre-lifting** entrypoint theorem's type matches the expected specification declaration (or its unfolded body) **before** prepending lifted `ForallE`/`Lam` binders, and require `entrypoint.levelParams.isEmpty == true`. Next, compute `unliftable_decls` as the transitive constant cone of `[expected_declaration]` union all non-`thm` declarations (`Defn`, `Opaque`, `InductiveBlock`, `Axiom`, `Quot`). Any allowlisted theorem in `unliftable_decls` (for example, a proof term referenced inside a computational `def`, such as `PolyLib.def_locked` in `Probe 3`) is never lifted; it stays in the environment intact, preserving definitional reduction and blocking type mutation of any constant reachable from the specification.

#### 3.2 Bottom-Up Topological Lifting Across Helper Theorems

Lean 4's elaborator routinely abstracts tactic subproofs into auxiliary theorems (`Proof.verify._proof_1` or user-written polymorphic helpers `poly_helper.{v}`). Processing declarations in topological bottom-up order over liftable `thm`s handles both monomorphic and universe-polymorphic helpers cleanly:

1. For each liftable theorem $T.\{v_0, \dots, v_{r-1}\}$, collect its required hypothesis set $H(T)$ as the union of:
   - direct references `(A, simp(us))` to effective allowlisted theorems `A`, and
   - for each call `Const(H, call_us)` to an already-lifted helper theorem $H$, the level-substituted hypotheses `(A, simp(subst(H.levelParams ↦ call_us, hyp_us)))` for every `(A, hyp_us) ∈ H(H)`.
2. Sort $H(T)$ canonically by `(structured_name, simplified_level_vec)` to obtain $k_T$ slots independent of proof-body traversal order.
3. Rewrite `T.value` using `(eid, depth)` memoization (incrementing `depth` inside `lam.body`, `forallE.body`, and `letE.body`, asserting every original `BVar(m)` satisfies `m < depth`):
   - `Const(A, us)` maps to `BVar(depth + (k_T - 1 - slot(A, simp(us))))`.
   - `Const(H, call_us)` maps to the iterated application `App(...App(Const(H, call_us), BVar(slot_0))..., BVar(slot_{m-1}))` passing each instantiated hypothesis of `H` in exact binder order.
4. Prepend `k_T` outer `ForallE` binders to `T.type` and `k_T` outer `Lam` binders to `T.value`, instantiating each `A.type` at `hyp_us` (which uses only `T`'s own `levelParams`).

In `Probe 3` (`support/probe_ndjson_m3_merkle_linker.py`), a two-hop universe-polymorphic chain (`sub_helper.{v}` -> `poly_helper.{v}` calling `PolyLib.poly_zero.{max v 1, 0}`), a monomorphic helper (`verify._proof_1`), and `OptBProof.verify` (calling `poly_helper.{0}`, `poly_helper.{2}`, and directly calling `PolyLib.poly_zero.{1, 0}`) deduplicated `poly_helper.{0}` and the direct `(1, 0)` call into one shared ground slot, emitted `32` declarations with **0 custom axioms**, and passed **4/4 kernels (`rc=0`)**. Across 40 nested `let`/`lam` scopes (`DagProof.verify`), `(eid, depth)` memoization expanded `541` input expressions to `651` (`1.203x`, `23` declarations, `4/4` kernels `rc=0`). Implementations must still enforce explicit fail-closed caps (`MAX_LIFTED_HYPS_PER_THM` and `MAX_M3_EXPRS`) against adversarial cross-depth sharing.

### 4. Union-Graph Tarjan-SCC Acyclicity and Offline Zero-Axiom Stitching

#### 4.1 Why Union-Graph Tarjan SCC Is Necessary

Modular callee-summary discharge is circular (and derives `False`) if cycles exist across either runtime calls or proof-level assumptions:
- Checking only direct MIR/program call edges misses mutual proof-hypothesis cycles (`F` assumes `G`'s theorem and `G` assumes `F`'s theorem with zero program calls).
- Checking only direct call edges plus explicit proof hypotheses misses indirect-call callbacks (`bad` calls `apply_cb(bad)`, creating a self-loop through closure/function-pointer/vtable provenance).

The sound acyclicity gate runs Tarjan's SCC algorithm over the **union graph** $G = (V, E_{\text{direct}} \cup E_{\text{indirect\_prov}} \cup E_{\text{m3\_hyps}})$, where $E_{\text{m3\_hyps}}$ is extracted strictly from the **post-lifting, kernel-checked NDJSON** outer binders of each shard (mapped via `cone_digest` to owning shards) rather than untrusted source annotations. Any SCC with $|C| > 1$ or any self-loop $(u, u) \in E$ is rejected fail-closed (`Probe 4`: `ACCEPT_DAG:3_shards`, `REJECT_UNION_CYCLE:F,G`, `REJECT_SELF_LOOP:bad`).

#### 4.2 Bottom-Up Offline Zero-Axiom Application Stitching

Because Option B lifting pushes all helper-theorem hypotheses up to each shard entrypoint's ground binders, offline stitching **never rewrites internal helper theorems**:
1. Traverse the Tarjan-verified shard DAG in bottom-up topological order (`BaseThm -> Shard1 -> Shard2 -> Shard3`).
2. Merge each shard's M3 NDJSON into a shared arena, alpha-renaming shard-local `Proof.*`/`Expected.*` declarations if namespaces overlap, while enforcing **strict kind equality and full Merkle `decl_digest` / `InductiveBlock` digest equality** on every already-present shared declaration (rejecting silent last-wins or first-wins deduplication).
3. For each shard entrypoint `S_i.Proof.verify`, peel its $k$ outer `ForallE` binders while applying `Const(resolved_target_m, us_m)` with the exact recorded ground universe levels `us_m` (where `resolved_target_m` is either a base zero-hypothesis theorem or an upstream `S_j.Proof.verify_linked`), assert the peeled type equals `S_i`'s expected claim, and emit `S_i.Proof.verify_linked`.
4. Garbage-collect with contiguous ID compaction from the top root(s) and replay across all four independent checkers.

Both `Probe 3` (polymorphic helpers, `35` decls) and `Probe 4` (3-shard DAG, `782` lines, `36` decls) produced closed, zero-custom-axiom streams accepted by **4/4 kernels (`rc=0`)**.

### 5. Lean 4 `module` Visibility, Monotonic Axiom Accounting, and Assumed-Contract Realizability

1. **Lean 4 `module` System (`.olean` / `.olean.server` / `.olean.private`) Under `leanexport` (`Probe 5`):** Compiling a `module` file with `public section` emits `.olean`, `.olean.server`, `.olean.private`, `.ir`, and `.ir.sig`. Under Lean `v4.35.0`, `leanexport` loads full `.private` visibility (`ModHidden.unexposed_fn` exports as `def`, not `axiom`; `ModHidden.secret_sorry` exports as `thm` exposing `axioms: ["sorryAx"]`) and **fails closed (`rc=1`)** when either `.olean.private` or `.olean.server` is deleted. Thus generating theorem allowlists from `leanexport` NDJSON closes `.olean`-only private-`sorry` hiding, whereas Lean-API inspectors using `importModules` must explicitly pass `level := .private`.
2. **`leanexport` Silent `rc=0` on Missing Constants:** Passing an absent constant name to `leanexport` writes `PANIC at LeanExport.dumpConstant LeanExport.Basic:254:48: Constant ... not found in environment.` to `stderr`, emits zero declarations, and returns **`rc=0`**. Verifiers and allowlist generators must verify that `stderr` contains no panic and every requested root constant is present in the parsed arena.
3. **Monotonic Foundation-Axiom and Model-Feature Union:** Because lambda-lifting erases lifted theorem proof bodies from per-shard streams, a theorem whose proof uses `Classical.choice` (or `Quot.sound`/`propext` or an optional semantic-model feature) only inside its proof body would disappear from per-shard kernel axiom reports. Each compiled-in allowlist entry must record `used_foundation_axioms` (`⊆ {propext, Quot.sound, Classical.choice}`, strictly `0` `sorryAx`) and its semantic-model feature closure computed from the full pre-lifting cone; the auditor monotonically unions these across every lifted hypothesis of the entrypoint.
4. **External Assumed-Contract Realizability:** Unlike proven-DAG internal shards (whose Rust MIR bodies constructively realize their contracts), unverified external callee contracts (such as FFI boundaries) can derive `False` if an uninhabited `Total` postcondition is assumed (e.g., `∀ x : BitVec 64, x < f x` at `u64::MAX`). External assumed contracts must always taint the verification receipt (`assumed_callee_contract`), default to `Partial` semantics (allowing divergence/trap), and require a kernel-checked constructive witness `∀ pre_state, pre pre_state → ∃ ret post_state, post pre_state ret post_state` (`0` `sorryAx`) before permitting `Total` lifting.

### 6. Prior Art Comparison and Upstream November 2026 Lean 4 Checker Developments

| System (Pinned Revision / DOI) | Split-Phase / Linking Architecture | Key Contrast vs. NDJSON Lambda-Lifting + Merkle Cones + Offline Stitching |
|---|---|---|
| **`leanprover/con-ron`** (`6fd8fee454dd71398ed7975ff3517058b5f5d8b6`) & **`leanprover/con-leche`** (`bc6676101c488e21ce71a317b33905534d497e14`) | Upstream Nov 2026 `--compare` (`justify::refines_b`, `hole_record` turning `sorryAx` theorems into axioms, `levels_renaming`, `IProjTable`, `cone_entry`) and `--modular` (`modular/graph.rs` Kahn rank check + isolated module workers). | Absent in bundled Lean `v4.35.0` binaries (which reject custom axioms `rc=2`). Even with upstream `--compare`, `con-ron --verified` ignores NDJSON `RecRule.rhs` (`Probe 1`), and `--compare` couples soundness to `con-ron`'s comparison driver. Lambda-lifting + offline stitching yields a single zero-axiom NDJSON certificate checkable by any independent kernel (`nanoda_bin`, `lean4lean`, `con-ron`, `con-leche`). |
| **`leanprover/lean4export`** (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`) | Topological NDJSON `3.1.0` exporter (`Export.lean`: `removeMData`, `nonDep := false`, `recursorMap`). | Traversal-dependent `Expr.eqv` hash-consing causes cross-file binder-name drift; missing constants panic to `stderr` with `rc=0`. |
| **`ammkrn/nanoda_lib`** (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`) | Minimal Rust kernel checking `RecRule.rhs` `def_eq` (`src/tc.rs:955`), `Level::simplify` (`src/level.rs`), and literal expansions (`src/expr.rs:580-640`). | Catches corrupted `RecRule.rhs` missed by `con-ron`/`con-leche`; enforces contiguous `in`/`il`/`ie` IDs and mandatory `letE.nondep` JSON keys. |
| **`CertiRocq/certirocq`** (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`; Paraskevopoulou, Li, & Appel, ICFP 2021, DOI `10.1145/3473591`) | Computational lambda-lifting over `LambdaANF` (`lambda_lifting.v`) and compositional separate-compilation linking over module environments (`pipeline.v`). | Lifts runtime computational closures; NDJSON `M3` lifts `Prop` proof hypotheses at export time so CIC proof-irrelevance handles dependent proof positions (`Fin.mk`, `letE`, `lam.type`) and offline `App` eliminates binders entirely. |
| **`Deducteam/lambdapi`** (`19fdacdfb9878e2d97a140ae839acbf8371d7183`) | `.lpo` object files strip private proofs (`compile.ml:31-125`, `Sign.strip_private`), enforce acyclic imports via `!loading` DFS guard, and link signatures via `Sign.link` (`sign.ml:239-310`). | Parallels separating theorem statement cones (`cone_digest`) from proof bodies and failing closed on import cycles; contrasts constraint-based universe checking (`Universo`) with Lean's parametric `ParamIdx` instantiation. |
| **`digama0/mm0`** (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`) | `.mmb` binary format separates `STMT_THM` statement index from optional `CMD_PROOF_THM` proof stream for $O(1)$ interface checking. | Mirrors separating per-shard `cone_digest` allowlist checks from optional offline full-proof assembly. |
| **`seL4/l4v`** (`df4f444823f8c9f99b4a9f45990001eecc820a5a`) & **`CakeML/cakeml`** (`afffa112be1e26551455023edc6b26a7c3f538b7`) | Isabelle `ROOTS` session heap DAGs (`AutoCorres`) and HOL4 sequential `Decls`/`call_main_thm1` characteristic-formula linking (`cfMainScript.sml`). | Isabelle session heaps place pickled ML heap serialization in the TCB; offline NDJSON stitching produces an unprivileged, check-from-scratch proof term with zero heap trust. |

## Boundaries

- **Toolchain Pinning:** All live kernel measurements were executed on Lean `v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) with bundled `leanexport 3.1.0`, `nanoda_bin 0.4.19`, `con-ron`, `con-leche`, and `lean4lean`. Upstream `con-ron` (`6fd8fee4...`) and `con-leche` (`bc667610...`) source files were inspected statically; their `--compare`/`--modular` CLIs were not yet present in the bundled `v4.35.0` release binaries.
- **Scale & Memory Ceilings:** Offline zero-axiom stitching (`Probe 3` at `35` decls and `Probe 4` at `782` lines / `36` decls) validates semantic soundness and wire format correctness on synthetic multi-shard DAGs; whole-crate memory and wall-clock scaling for multi-million-line linked streams depends on streaming arena compaction and remains bounded by host RAM budgets.
- **Indirect-Call Provenance:** Tarjan union-SCC soundness assumes the frontend supplies a sound conservative over-approximation for $E_{\text{indirect\_prov}}$ whenever indirect calls (`fn` pointers, closures, trait objects) are allowed to invoke promoted callee contracts; when indirect calls remain unsupported/rejected by the semantic frontend, $E_{\text{indirect\_prov}} = \emptyset$ trivially.
- **Non-`Prop` Lifting Out of Scope:** Lambda-lifting applies strictly to `CanonConstInfo::Thm` (`Prop`) declarations outside `unliftable_decls`. Lifting computational `Defn`s or `Type`-valued axioms breaks definitional equality and can introduce uninhabited-type unsoundness.

## Evidence

- **Standalone Reproducible Probe Suite:** `support/probe_ndjson_m3_merkle_linker.py` (self-contained Python 3 script, zero external library dependencies; invokes `lean`, `leanexport`, `nanoda_bin`, `con-ron --verified`, `con-leche --verified`, and `lean4lean --import` inside `tempfile.TemporaryDirectory`).
  - **Execution Receipt (`2026-11-23`, Lean `v4.35.0`):** Exited `rc=0`.
    - `probe_1_inductive_rec_hints_merkle`: `base_merkle_prefix = "2b157f31ae9ba228"`; `mut_rec_rhs` -> `nanoda` `101`, `con_ron` `0`, `con_leche` `0`, `lean4lean` `1`, `merkle_changed = true`; `mut_defn_hints` -> `4/4` `0`, `merkle_changed = true`; `mut_rec_k` -> `4/4` non-zero, `merkle_changed = true`.
    - `probe_2_canonical_reserialization`: `kernels_canon_preserve_rules` -> `4/4` `0` (`78` decls); `kernels_reversed_recs_only` -> `4/4` `0`; `kernels_reversed_rules_only` -> `4/4` fail (`nanoda` `101` `src/inductive.rs:1315:9`, `con_ron`/`con_leche`/`lean4lean` `1`); `kernels_omit_nondep_key` -> `nanoda` `1`, `lean4lean` `1`, `con_ron`/`con_leche` `0`.
    - `probe_3_option_b_and_dag_ratio`: `unliftable_kept = ["PolyLib.def_locked"]`; `m3_kernels` -> `4/4` `0` (`32` decls); `linked_kernels` -> `4/4` `0` (`35` decls); `dag_exprs_in = 541`, `dag_exprs_out = 651`, `dag_expansion_ratio = 1.203`, `dag_m3_kernels` -> `4/4` `0` (`23` decls).
    - `probe_4_multi_shard_tarjan_and_link`: `tarjan_valid = [true, "ACCEPT_DAG:3_shards"]`, `tarjan_mutual_proof_cycle = [false, "REJECT_UNION_CYCLE:F,G"]`, `tarjan_indirect_self_loop = [false, "REJECT_SELF_LOOP:bad"]`; `linked_lines = 782`, `linked_kernels` -> `4/4` `0` (`36` decls).
    - `probe_5_module_olean_private`: `full_export_rc = 0`, `full_export_kinds = {"ModHidden.unexposed_fn": "def", "ModHidden.exposed_fn": "def", "ModHidden.secret_sorry": "thm", "ModHidden.clean_thm": "thm"}`, `full_export_axioms = ["sorryAx"]`; `missing_const_rc = 0`, `missing_const_stderr_has_panic = true`; `without_private_rc = 1`; `olean_only_rc = 1`.
- **Primary Upstream Sources Audited:**
  - `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`: `Export.lean` (`removeMData` `nonDep := false`, `recursorMap`, `dumpStrDeps`) and `format_ndjson.md`.
  - `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`: `src/level.rs`, `src/expr.rs:580-640`, `src/tc.rs:955`.
  - `leanprover/con-ron@6fd8fee454dd71398ed7975ff3517058b5f5d8b6` (`OVERVIEW.md`, `crates/con-ron-core/src/arena/justify.rs`, `crates/con-ron-core/src/frontend/compare.rs`, `crates/con-ron-core/src/frontend/modular/graph.rs`) and `leanprover/con-leche@bc6676101c488e21ce71a317b33905534d497e14`.
  - `CertiRocq/certirocq@ab66e0164e7ecb63e5af95c90c8e479068bf95c2` (`theories/LambdaANF/lambda_lifting.v`, `pipeline.v`; DOI `10.1145/3473591`).
  - `Deducteam/lambdapi@19fdacdfb9878e2d97a140ae839acbf8371d7183` (`src/handle/compile.ml:31-125`, `src/core/sign.ml:239-310`).
  - `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`, `seL4/l4v@df4f444823f8c9f99b4a9f45990001eecc820a5a`, `CakeML/cakeml@afffa112be1e26551455023edc6b26a7c3f538b7` (`characteristic/cfMainScript.sml`).

## Revalidation

Re-run the standalone verification suite whenever upgrading Lean 4, `lean4export`, `nanoda_bin`, `con-ron`, `con-leche`, or `lean4lean`:

```bash
LEAN_TOOLCHAIN_DIR="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0" \
  python3 reports/lambda-lifted-ndjson-proof-linking-merkle-cones-and-tarjan-scc/support/probe_ndjson_m3_merkle_linker.py
```

Revalidate specifically if:
1. Upstream `con-ron --compare` / `--modular` ships in a release Lean toolchain and alters axiom-handling or `RecRule.rhs` validation behavior.
2. `lean4export` changes its `3.1.0` NDJSON schema (such as dropping `"nondep"`, changing `inductive` record layout, or fixing exit-code handling on missing constants).
3. Lean 4 changes `.olean.server`/`.olean.private` loading semantics for `module` files.
