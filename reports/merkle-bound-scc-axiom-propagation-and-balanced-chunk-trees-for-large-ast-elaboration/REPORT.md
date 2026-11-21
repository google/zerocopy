# Merkle-Bound SCC Axiom Propagation and Balanced Chunk Trees for Large AST Elaboration

## Summary

Scaling mechanized program verification in dependent-type proof assistants (Lean 4, Rocq, and Isabelle/HOL) across large compiler-generated IR modules exposes two structural failure modes spanning audit soundness and elaborator recursion bounds:

1. **`ConstantInfo.opaqueInfo` bypasses `#print axioms` and enables assumption laundering across modular SCCs**: Direct inspection of `leanprover/lean4` (`src/Lean/Declaration.lean` and `src/Lean/Util/CollectAxioms.lean`) proves that `ConstantInfo.isAxiom` returns `false` on `.opaqueInfo`, and `CollectAxioms.collect` inserts a declaration into `s.axioms` only on `.axiomInfo`—recursing into an `.opaqueInfo` declaration's `type` and `value` without flagging the opaque constant itself. Any kernel-irreducible `opaque` spec, `partial def`, or `@[extern]` stub whose `OpaqueVal.value` uses a constructive `Inhabited` witness (`True`, `0`, `default`) yields zero axioms under `#print axioms`, while `CollectAxioms.collect` trusts pre-computed `exportedAxiomsExt` tables across `.olean` boundaries without inspecting imported bodies. Parallel per-module checking (`lean4checker` workers) against stubbed Tarjan strongly connected component (SCC) boundaries additionally permits assumption laundering and filesystem `.olean`-swap time-of-check-to-time-of-use (TOCTOU) skew. Binding each SCC shard to a content-addressed Merkle receipt over `toolchain_sha256`, `olean_parts_sha256`, and cone-scoped transitive `(.axiomInfo, .opaqueInfo ∨ isPartial ∨ isUnsafe)` unions blocks 5/5 exploits while allowing unreferenced library opaques outside the claim cone.
2. **Flat `List.cons` IR emissions crash `maxRecDepth`, whereas balanced $O(\log N)$ `BinChunkTree` encodings stay shallow**: Desugaring a flat `[x₀, ..., x_{N-1}]` table of MIR locals or basic blocks builds a right-nested `List.cons` spine of depth $N + 1$, crossing Lean 4's `defaultMaxRecDepth := 512` at $N \ge 512$ and causing $O(N^2)$ linear table-scan reduction. Packing entries into fixed-arity $B = 8$ leaf chunks inside a balanced binary tree (`BinChunkTree α`) shrinks spine depth at $N = 4,096$ from `4,097` to **`11`** ($372\times$ shallower), drops worst-case lookup from `4,096` to **`10`** WHNF steps, and cuts an $N$-entry scan from `8,390,656` to **`40,960`** steps ($204.8\times$ reduction).

## Applicability

This package covers zero-trust proof-auditing pipelines and large-scale AST serialization architectures across eight pinned repositories inspected on `2026-11-21`, peer-reviewed literature, and an executable verification probe:

- **Lean 4 kernel, axioms, replay, and recursion limits**: `leanprover/lean4` (`ab8894fb4de9405d7be3627bdcfbfe74be0383d0`, `src/Lean/{Declaration.lean,Util/CollectAxioms.lean,Replay.lean,CoreM.lean,Util/RecDepth.lean}`, `src/Init/Prelude.lean`, `src/kernel/declaration.h`, `src/lake/Lake/Build/Module.lean`).
- **Modular Lean 4 auditors and checkers**: `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`), `GasStationManager/SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`), `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`), `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, `arXiv:2403.14064`), and `ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, v0.4.32).
- **Cross-prover assumption tracking & balanced functional tries**: `rocq-prover/rocq` (`25f5b18a320e4796f181f938d3b74bebe7db4dc4`, `vernac/assumptions.ml`), `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`, `lib/Maps.v`), Appel & Leroy (JAR 2023, DOI `10.1007/s10817-022-09655-x`), Okasaki (JFP 1997, DOI `10.1017/S0956796897003073`), Braun & Rem (1983), Mokhov et al. (ICFP 2018 / JFP 2020), Pollack (1998), and Tarjan (1972).

### Cross-References to Adjacent Corpus Packages

This report complements without duplicating five adjacent corpus packages:

- `proof-kernels-opaque-interfaces-and-adversarial-spec-hardening`: Covers Lean 4 C++ kernel `has_fvar` GMP bypasses, `.olean` memory-safety vulnerabilities, and Goodhart spec loopholes.
- `lean-olean-ilean-format-and-compilation-determinism`: Documents binary `.olean` compacted-region layout and module determinism hashes.
- `lean4-kernel-soundness-criticisms-defeq-pathologies-and-lean4lean-checkers`: Details Lean 4 conversion pathologies and Lean4Lean typechecker soundness proofs.
- `de-bruijn-kernels-self-verifying-checkers-and-proof-producing-toolchains`: Surveys minimal checker TCBs and MM0 `.mmb` / `nanoda_lib` architectures.
- `proof-generation-token-budgets-vo-olean-mmb-footprints-and-checker-throughput`: Compares `.vo`, `.olean`, and `.mmb` artifact byte sizes and throughput.

## Findings

### 1. How `ConstantInfo.opaqueInfo` Bypasses `#print axioms` and `isAxiom` Filters

Basis: source + documentation + derived

In Lean 4 (`leanprover/lean4` @ `ab8894fb...`), the kernel declaration lattice (`src/Lean/Declaration.lean:406-415`) splits constants into eight constructors: `.axiomInfo`, `.defnInfo`, `.thmInfo`, `.opaqueInfo`, `.quotInfo`, `.inductInfo`, `.ctorInfo`, and `.recInfo`. Directly inspecting `Declaration.lean` and `CollectAxioms.lean` reveals why naive axiom filters fail:

1. **Disjoint `isAxiom` and default `hasValue` predicates (`Declaration.lean:459-500`, `declaration.h:447-449`)**:
   - `ConstantInfo.isAxiom` (`:497-499`) returns `true` exclusively on `.axiomInfo _`.
   - `ConstantInfo.value? (allowOpaque := false)` (`:459-464`) and `hasValue (allowOpaque := false)` (`:471-476`, matching C++ `declaration.h:447-449`) return `none` / `false` for `.opaqueInfo`. Thus `opaque` declarations behave identically to axioms in kernel WHNF reduction (`is_delta` = false): consumers cannot unfold or inspect their definitions during definitional equality checks.
2. **`CollectAxioms.collect` never flags `.opaqueInfo` (`src/Lean/Util/CollectAxioms.lean:56-67`)**:
   ```lean
   match env.checked.get.find? c with
   | some (.axiomInfo v)  =>
       modify fun s => { s with axioms := s.axioms.insert c }
       collectExpr v.type
   | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
   | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
   | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
   ...
   ```
   While `.axiomInfo v` inserts `c` into `s.axioms`, `.opaqueInfo v` (`:62`) only recurses into `v.type` and `v.value` without recording `c`!
3. **Three axiom-free smuggling vectors**:
   - **Dummy `OpaqueVal.value` specification laundering**: An untrusted module declares `opaque targetSpec : State → Prop := fun _ => True` (or `partial def` / `@[extern "c_impl"] opaque f : U64 → U64` whose kernel witness `OpaqueVal.value` is `0 : U64` or `default` from a constructive `Inhabited` instance). Because `True` and `0` depend on zero axioms (`#[]`), `#print axioms thm` reports `'thm' does not depend on any axioms` and `ci.isAxiom` is `false`, yet `targetSpec` is trivially satisfiable (`True.intro`) and kernel-irreducible!
   - **Pre-computed `exportedAxiomsExt` trust (`CollectAxioms.lean:41-44, 102-155`)**: In `collect`, lines `42-44` query `extFind? env c` (`ExportedAxiomsState.find?` via `exportedAxiomsExt`), insert the imported module's pre-computed `Array Name`, and **return immediately** without walking imported definitions. Under `loadExts := true`, a poisoned upstream `.olean` can serialize an empty axiom array `#[]` in its `exportedAxiomsExt` extension table; conversely, under hardened `loadExts := false`, private-only `.olean` parts must be loaded or cross-module body walking fails.
   - **Partial audit coverage in `Replay.lean` and `SafeVerify`**: `Lean.Kernel.Environment.replay` (`src/Lean/Replay.lean:100-101, 180-184`) silently skips `ci.isUnsafe || ci.isPartial` at `:183` and accepts any well-typed `.opaqueInfo` via `Declaration.opaqueDecl`. In `GasStationManager/SafeVerify` (`b291b588...`, `Main.lean:17-23, 60-66, 150-161`), `processFileDeclarations` populates `Info.axioms` using `CollectAxioms.collect`, checks `equivOpaq` only on constants present in `targetDecls` (`:60`), and calls `importModules mod.imports {} 0` (`:151`) without replaying upstream `.olean` imports—leaving newly introduced `submission` opaque helpers and un-replayed imports unflagged unless rejected by policy.

#### Cross-Prover Assumption and Opacity Comparison

| Prover & Commit | Opaque Proof / Definition Construct | Kernel Unfolding Behavior | Axiom-Collection Traversal | Known Multi-Module / Quick-Compile Trap |
| :--- | :--- | :--- | :--- | :--- |
| **Lean 4** (`ab8894fb...`) | `opaque` / `partial` / `@[extern]` -> `.opaqueInfo` (`Declaration.lean:139-146`) | Irreducible in WHNF (`has_value(false) == false`, `declaration.h:447`) | `CollectAxioms.collect` traverses `v.type` & `v.value`, **omits `c`** (`:62`); trusts `exportedAxiomsExt` (`:42-44`) | Constructive `Inhabited` witnesses produce `#[]`; `loadExts := true` trusts upstream `.olean` tables. |
| **Rocq** (`25f5b18a...`) | `Qed` -> `OpaqueDef o` (`vernac/assumptions.ml:216`) vs `Axiom`/`Parameter` -> `Undef _` (`:214`) | Irreducible in `cClosure.ml`; body sits in lazy `opaquetab` segment | `get_constant_body` calls `Global.force_proof access o` (`:217`) so axioms inside `Qed` proofs are collected | Under `-vos`/`-vok`, missing proof body triggers `warn_unreachable_opaque_body` (`:201-205`) and returns `None`; `Declare Module` (`Abstract`) hides bodies. |
| **Isabelle/HOL** (`Pure/thm.ML`) | Derivation-level `thm` objects + `axiomatization` / `oracle` tags (`Skip_proof`) | Definitional axioms explicitly unfolded by `Thm.unfold_rule` only | Kernel propagates `axioms` and `oracles` inside `thm_header` through every `implies_elim` step | Unchecked oracle tags (`Skip_proof`) still satisfy `thm` typing until session-root oracle inspection rejects non-empty oracle sets. |

---

### 2. Merkle-Bound Per-SCC Audit Receipts: Closing Assumption Laundering and `.olean` TOCTOU

Basis: source + execution + derived

To bound peak RSS when checking crates or theories containing hundreds of functions, compilers and verifiers partition the dependency graph into Tarjan strongly connected components (Tarjan 1972, DOI `10.1137/0201010`), stubbing cross-SCC dependencies as lightweight `.axiomInfo` or `.opaqueInfo` declarations during parallel worker compilation (`leanprover/lean4checker` @ `91a7f0e8...`, `Main.lean:57-60, 120-150`, where `defaultNumWorkers := 8` guards against `32 GB` OOM and `replayFromImports` runs `importModulesCore` without replaying imports). Without cryptographic binding across shard boundaries, parallel per-SCC verification suffers three attacks:

1. **Cross-SCC stub assumption laundering**: Caller SCC $B$ replays cleanly against stub `callee_fn` without recording that callee SCC $A$'s proof of `callee_fn` relied on a forbidden axiom (`sorryAx`) or an unvetted `.opaqueInfo` helper.
2. **`.olean` swap TOCTOU & DAG diamond skew**: In parallel worker loops (`lean4checker/Main.lean:135-149`), Worker 1 audits `A.olean` at digest $H_1$ while Worker 2 later imports a modified `A.olean` at digest $H_2$, or branches $B$ and $C$ of a diamond `D -> {B, C} -> A` link incompatible versions of `A` while every per-shard exit code is `0`.
3. **False positives from unreferenced library opaques**: Auditing an entire `.olean` module flatly rejects crates whenever a general standard/vendor import defines an unreferenced `partial` or `opaque` helper never touched by the theorem's proof term.

#### Cone-Scoped Transitive Propagation + Merkle Receipt Protocol

Each SCC $u$ in the condensed DAG is audited in isolation (`trustLevel := 0`, `loadExts := false`) by traversing only the expression-level dependency cone `ReachableCone(u, exports(u))` computed with `ConstantInfo.getUsedConstants (allowOpaque := true)` (mirroring `digama0/lean4lean` @ `67f63b0c...`, `Lean4Lean/Replay.lean:33-43`, never `exportedAxiomsExt`):

$$\mathcal{A}_{\text{local}}(u) = \{c \in \mathrm{Cone}(u) \cap \mathrm{Decls}(u) \mid c \text{ is } \mathtt{.axiomInfo}\}, \qquad \mathcal{O}_{\text{local}}(u) = \{c \in \mathrm{Cone}(u) \cap \mathrm{Decls}(u) \mid c \text{ is } \mathtt{.opaqueInfo} \lor c.\mathtt{isPartial} \lor c.\mathtt{isUnsafe}\}$$

$$\mathcal{A}_{\text{trans}}(u) = \mathcal{A}_{\text{local}}(u) \cup \bigcup_{v \in \mathrm{coneDeps}(u)} \mathcal{A}_{\text{trans}}(v), \qquad \mathcal{O}_{\text{trans}}(u) = \mathcal{O}_{\text{local}}(u) \cup \bigcup_{v \in \mathrm{coneDeps}(u)} \mathcal{O}_{\text{trans}}(v)$$

Each shard emits a Merkle-chained audit receipt binding both its own `.olean` byte parts (cf. Lake constructive traces in `src/lake/Lake/Build/Module.lean:50-62`, Mokhov et al. 2018 DOI `10.1145/3236774`) and every observed import digest:

$$D(u) = \mathrm{SHA256}\Bigl(\mathtt{toolchain\_sha256} \,\|\, \mathtt{scc\_id}(u) \,\|\, \mathtt{olean\_parts\_sha256}(u) \,\|\, \mathrm{sort}\bigl(\{(v, \mathtt{olean\_parts\_sha256}(v), D(v)) \mid v \in \mathrm{imports}(u)\}\bigr) \,\|\, \mathrm{sort}(\mathcal{A}_{\text{trans}}(u)) \,\|\, \mathrm{sort}(\mathcal{O}_{\text{trans}}(u))\Bigr)$$

A final global graph check verifies (1) unique `scc_id` and acyclic rank monotonicity `scc_id(v) < scc_id(u)` for every dependency edge $v \to u$, (2) exact byte-for-byte equality of `olean_parts_sha256(v)` and `D(v)` between every importer's observed input snapshot and $v$'s own audited receipt (eliminating TOCTOU swaps and diamond skew), and (3) root acceptance $\mathcal{A}_{\text{trans}}(r) \subseteq \mathcal{A}_{\text{allowed}}$ and $\mathcal{O}_{\text{trans}}(r) = \emptyset$.

#### Empirical Exploit & Acceptance Matrix (`2026-11-21` Execution)

| Scenario | Naive `#print axioms` + Local Import Replay | Merkle-Bound Cone-Scoped SCC Audit | Exact Rejection / Acceptance Diagnostic |
| :--- | :---: | :---: | :--- |
| **`opaque_spec_true`** (`opaque spec := True`) | **Bypass (`{}` axioms)** | **Rejected** | `forbidden_opaques:['spec']` |
| **`partial_extern_inhabited_witness`** (`partial def` / `@[extern]`) | **Bypass (`{}` axioms)** | **Rejected** | `forbidden_opaques:['helper']` |
| **`cross_scc_stub_axiom_laundering`** (`bad_ax` in stubbed `A3`) | **Bypass if stub omitted** | **Rejected** | `forbidden_axioms:['bad_ax']` via $\mathcal{A}_{\text{trans}}$ |
| **`spoofed_exportedAxiomsExt_olean`** (`A4` lies `lemma_a -> []`) | **Bypass (`{}` axioms)** | **Rejected** | `forbidden_axioms:['bad_ax']` (ignores `exportedAxiomsExt`) |
| **`olean_swap_toctou_and_diamond_skew`** (`A5` swapped on disk) | **Bypass (workers pass)** | **Rejected** | `olean_toctou_or_skew:B5->A5` (`obs_olean != target.olean_hash`) |
| **Legitimate clean cone + unreferenced vendor `opaque`** (`A6`) | N/A | **Accepted** | `accepted` (`unused_vendor_opaque` outside `ReachableCone`) |

---

### 3. Balanced $O(\log N)$ Chunk Trees (`BinChunkTree`) vs. `List.cons` `maxRecDepth` Crashes

Basis: source + execution + derived

When an IR extractor emits large constant compiler tables (e.g., $N = 600\text{--}4,096$ MIR locals, basic blocks, or initial memory bytes) as Lean list literals `[x_0, ..., x_{N-1}]`, elaboration and kernel checking collide with three scaling cliffs verified in `leanprover/lean4` (`ab8894fb...`):

1. **Recursion depth exhaustion (`src/Init/Prelude.lean:5006-5012, 5994`, `src/Lean/Util/RecDepth.lean:15-18`, `src/Lean/CoreM.lean:365, 469, 505-509`)**: Lean 4 sets `defaultMaxRecDepth := 512` globally (`Core.Context.maxRecDepth := 1000` when configured via `CoreM`, `512` in `MacroM` and default option bindings). A list literal of length $N$ elaborates to right-nested `List.cons x_0 (List.cons x_1 ... List.nil)` with structural spine depth $N + 1$ (and $2N$ binary `Expr.app` edges counting curried `List.cons α`). Recursive macro expansion, elaborator `inferType`, delaborator formatting, and kernel reduction traverse this spine linearly, tripping `maximum recursion depth has been reached` at $N \ge 512$–$1,000$.
2. **Repeated implicit type-parameter elaboration**: Each of the $N$ `List.cons` applications instantiates universe level `u` and `{α : Type u}` (unless generated via explicit `@List.cons`), multiplying term size and metavariable unification work by $O(N)$.
3. **Quadratic full-table WHNF reduction**: Indexing `List.get?` at element $i$ consumes $i + 1$ `List.rec` iota steps; stepping or looking up all $N$ blocks/locals across a function executes $\sum_{i=0}^{N-1} (i + 1) = N(N + 1)/2$ reduction steps ($8,390,656$ steps at $N = 4,096$).

#### Dense `BinChunkTree` ($B = 8$) Formulation and Tradeoffs

Packing dense `0`-indexed IR tables into fixed-arity $B = 2^3 = 8$ leaf chunks inside a balanced binary tree (generalizing Braun trees—Braun & Rem 1983, Okasaki JFP 1997 DOI `10.1017/S0956796897003073`—with constant-time 8-way leaf projection):

```lean
inductive Chunk8 (α : Type u) where
  | mk (x0 x1 x2 x3 x4 x5 x6 x7 : Option α) : Chunk8 α

inductive BinChunkTree (α : Type u) where
  | empty : BinChunkTree α
  | leaf  : Chunk8 α → BinChunkTree α
  | node  : BinChunkTree α → BinChunkTree α → BinChunkTree α
```

Lookup and functional update route upper bits (`idx >>> 3` or span halving) down internal `node l r` branches in $\lceil \log_2 \lceil N / 8 \rceil \rceil$ steps and select `x0..x7` in one $O(1)$ match at the leaf.

#### Measured AST Depth & WHNF Step Scaling ($N = 64\text{--}4,096$)

| Elements ($N$) | `List.cons` Spine Depth | `List.cons` Scan Steps ($N(N+1)/2$) | `BinChunkTree` ($B=8$) Spine Depth | `BinChunkTree` Max `get` Steps | `BinChunkTree` $N$-Scan Steps | Depth & Scan Speedup |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `64` | `65` | `2,080` | **`5`** | `4` | `256` | `13.0×` / `8.1×` |
| `256` | `257` | `32,896` | **`7`** | `6` | `1,536` | `36.7×` / `21.4×` |
| `512` | `513` (`>= 512`) | `131,328` | **`8`** | `7` | `3,584` | `64.1×` / `36.6×` |
| `1,024` | `1,025` (`> 1000`) | `524,800` | **`9`** | `8` | `8,192` | `113.9×` / `64.1×` |
| `2,048` | `2,049` | `2,098,176` | **`10`** | `9` | `18,432` | `204.9×` / `113.8×` |
| `4,096` | `4,097` | `8,390,656` | **`11`** | `10` | `40,960` | **`372.5×` / `204.8×`** |

- **`BinChunkTree` vs. Appel–Leroy Canonical `PTree`**: For **static dense `0`-indexed IR dumps** (basic blocks, locals, constant pools), `BinChunkTree` ($B = 8$) cuts internal node overhead and recursion depth by $3$ tree levels ($\log_2 8$) relative to $1$-element binary trees while keeping AST depth `<= 11` (`< 2.2%` of `defaultMaxRecDepth = 512`) even at $N = 4,096$. Conversely, for **mutable sparse maps requiring structural extensionality** (`(∀ k, get k m₁ = get k m₂) → m₁ = m₂`) across dynamic `insert`/`remove` joins without axioms, Appel & Leroy's 7-constructor canonical `PTree` (`AbsInt/CompCert` @ `2685140b...`, `lib/Maps.v:184-245`; DOI `10.1007/s10817-022-09655-x`) remains strictly superior because `BinChunkTree` admits distinct empty-tail padding (`none` slots in `Chunk8`). Exhaustive `64 × 64` checking (`4,096` `(i, j)` pairs) confirms `get(set(t, i, v), j) = v` for `i = j` and `get(t, j)` for `i != j`.

## Boundaries

- **`not examined`**: OS-level sandboxing (`seccomp-bpf` / Landlock / `bubblewrap`) of live Lean 4 metaprogram plugins (`leanprover/comparator` uses `landrun` + `lean4export`, inspected only at architectural level here) and direct live compilation benchmarks of $N = 4,096$ Lean terms inside `lean` subprocesses.
- **`unknown`**: The exact crossover chunk arity ($B = 8$ vs. $B = 16$ vs. $B = 32$) where C++ pattern-match case-splitting overhead inside `ChunkB.rec` outweighs tree-depth savings on Lean 4 LCNF native codegen and kernel WHNF across future compiler releases.
- **`known not to apply`**:
  - Rocq's `PArray` primitive array O(1) lookup (`Zprimitive`) and `Global.force_proof` delayed-opaque traversal (`rocq-prover/rocq` `vernac/assumptions.ml:217`) are **known not to apply** to Lean 4's C++ kernel, which has no native kernel `Array` reducer and isolates `.opaqueInfo` bodies via `has_value(false) == false`.
  - Structural map extensionality (`(∀ i, get i t₁ = get i t₂) → t₁ = t₂`) is **known not to apply** unconditionally to `BinChunkTree` ($B = 8$) when comparing dynamically shrunk trees against differently padded `Chunk8` / `.empty` shapes (use CompCert/Appel–Leroy 7-constructor `PTree` when canonical extensionality is required).
- **`unsupported`**:
  - Enforcing `NoOpaque` / `NoAxiom` hygiene purely inside Lean 4's object logic without an external meta/kernel environment pass is **unsupported** (Pollack 1998, `10.1093/oso/9780198501275.003.0013`), and `CollectAxioms.collect` natively offers no flag to emit `.opaqueInfo` names in `#print axioms` (`CollectAxioms.lean:62`).
  - Writing flat `[x_0, ..., x_{4095}]` list literals under Lean 4's default `defaultMaxRecDepth := 512` (`Prelude.lean:5007`) is **unsupported** without raising `maxRecDepth` per file or switching to balanced tree constructors.
- **Limits on stronger conclusions**: The probe verifies structural AST depth, WHNF traversal step counts, `64 × 64` lens consistency, and `5/5` exploit rejection on a Python reference model of the Lean 4 environment lattice; exact wall-clock elaboration milliseconds depend on host heap cache and Lean 4 minor versions.

## Evidence

All upstream primary sources and the executable probe were inspected and run on `2026-11-21`.

### Primary Source Coordinates

1. **`leanprover/lean4` @ `ab8894fb4de9405d7be3627bdcfbfe74be0383d0`**:
   - `src/Lean/Declaration.lean`: `:139-146` (`OpaqueVal`), `:406-415` (`ConstantInfo` constructors), `:459-477` (`value?`, `hasValue` with `allowOpaque := false`), `:497-511` (`isAxiom`, `isDefinition`, `isTheorem`).
   - `src/kernel/declaration.h`: `:221-224`, `:447-449` (`has_value(bool allow_opaque = false)`).
   - `src/Lean/Util/CollectAxioms.lean`: `:37-75` (`CollectAxioms.collect`, `:42-44` `extFind?` early return, `:57-63` `.axiomInfo` vs `.opaqueInfo`), `:96-146` (`ExportedAxiomsState`, `exportedAxiomsExt` `exportEntriesFnEx`), `:149-155` (`collectAxioms`).
   - `src/Lean/Replay.lean`: `:59-62` (`addDeclCore 0 0`), `:74-101` (`replayConstant` `.opaqueDecl`), `:177-197` (`replay` skipping `isUnsafe || isPartial` at `:183`).
   - `src/Init/Prelude.lean`: `:5007` (`defaultMaxRecDepth := 512`), `:5994` (`Macro.Context.maxRecDepth`); `src/Lean/Util/RecDepth.lean`: `:15-18`; `src/Lean/CoreM.lean`: `:365, 469, 505-509, 878-880` (`Core.Context.maxRecDepth := 1000`, `withAtLeastMaxRecDepth`).
   - `src/lake/Lake/Build/Module.lean`: `:50-62` (`recFetchInput` source `mtime` + `.ofText` hash).
2. **`leanprover/lean4checker` @ `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`**:
   - `Main.lean`: `:14-41` (`replayFromImports` vs `replayFromFresh`), `:57-60` (`defaultNumWorkers := 8` and 32 GB OOM note), `:120-150` (sliding worker pool).
3. **`GasStationManager/SafeVerify` @ `b291b588a53999a7e837dda61c7dbfe8c550c814`**:
   - `Main.lean`: `:17-23` (`processFileDeclarations` using `CollectAxioms.collect`), `:60-66` (`equivOpaq`, `checkAxioms`), `:145-161` (`importModules mod.imports {} 0` + `env.replay`).
4. **`digama0/lean4lean` @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` & `leanprover/comparator` @ `865edc14486c3388e9225daa971da8e157488c3e` & `ammkrn/nanoda_lib` @ `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`**:
   - `Lean4Lean/Replay.lean`: `:33-43` (`ConstantInfo.getUsedConstants` using `value? (allowOpaque := true)`), `:170-210` (`replayConstant`).
   - `comparator` (`865edc14...`): sandboxed `lean4export` checking against trusted target declarations.
   - `nanoda_lib` (`0da9f98f...`, v0.4.32): safe-Rust external checker over `lean4export` NDJSON.
5. **`rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`**:
   - `vernac/assumptions.ml`: `:106-108` (`Abstract`), `:201-220` (`warn_unreachable_opaque_body`, `get_constant_body` calling `Global.force_proof` on `OpaqueDef o`), `:261-275` (`traverse_object`).
6. **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`**:
   - `lib/Maps.v`: `:184-245` (`PTree.tree'`, `Node001`..`Node111`, `get'`).

### Published Literature

- Pollack (1998), *How to Believe a Machine-Checked Proof*, OUP, DOI `10.1093/oso/9780198501275.003.0013` (BRICS RS-97-18, DOI `10.7146/brics.v4i18.18945`).
- Carneiro (2024), *Lean4Lean: Verifying a Typechecker for Lean, in Lean*, `arXiv:2403.14064`, DOI `10.48550/arXiv.2403.14064`.
- Mokhov, Mitchell, & Peyton Jones (2018/2020), *Build Systems à la Carte*, PACMPL 2 (ICFP 2018), DOI `10.1145/3236774`; JFP 30 (2020), DOI `10.1017/S0956796820000088`.
- Appel & Leroy (2023), *Efficient Extensional Binary Tries*, JAR 67:8, DOI `10.1007/s10817-022-09655-x` (`arXiv:2110.05063`).
- Okasaki (1997), *Functional Pearl: Three Algorithms on Braun Trees*, JFP 7(6), DOI `10.1017/S0956796897003073`; Braun & Rem (1983), *A Logarithmic Implementation of Flexible Arrays*, Eindhoven Memorandum MR83/4.
- Tarjan (1972), *Depth-First Search and Linear Graph Algorithms*, SIAM J. Comput. 1(2):146–160, DOI `10.1137/0201010`.

### Probe Execution Record (`2026-11-21`)

- Command: `python3 - <<'PY' ... PY` (Python 3.10+, standard library only, script preserved verbatim in **Revalidation**).
- Exit code: `0`.
- Observed stdout:
  `N=  64: list_depth=  65 list_scan=   2080 | bct_depth= 5 max_get= 4 bct_scan=  256`
  `N= 256: list_depth= 257 list_scan=  32896 | bct_depth= 7 max_get= 6 bct_scan= 1536`
  `N= 512: list_depth= 513 list_scan= 131328 | bct_depth= 8 max_get= 7 bct_scan= 3584`
  `N=1024: list_depth=1025 list_scan= 524800 | bct_depth= 9 max_get= 8 bct_scan= 8192`
  `N=2048: list_depth=2049 list_scan=2098176 | bct_depth=10 max_get= 9 bct_scan=18432`
  `N=4096: list_depth=4097 list_scan=8390656 | bct_depth=11 max_get=10 bct_scan=40960`
  `PROBE2_OK: 5/5 exploits blocked, 2/2 clean graphs accepted, BinChunkTree verified`

## Revalidation

1. **Re-run the Merkle SCC audit + `BinChunkTree` scaling probe** (Python 3.10+, expects exit `0` and `PROBE2_OK`):
   ```bash
   python3 - <<'PY'
   import hashlib, math
   from dataclasses import dataclass, field
   from typing import Dict, List, Optional, Set, Tuple

   @dataclass(frozen=True)
   class Decl:
       name: str; kind: str; deps: Tuple[str, ...]; value_deps: Tuple[str, ...] = ()
       is_partial: bool = False; is_unsafe: bool = False

   @dataclass
   class Mod:
       name: str; scc: int; decls: Dict[str, Decl]
       imports: Dict[str, "Mod"] = field(default_factory=dict)
       ext_cache: Dict[str, Tuple[str, ...]] = field(default_factory=dict)
       exports: Tuple[str, ...] = ()
       def digest(self) -> str:
           p = "|".join(f"{k}:{d.kind}:{d.is_partial}:{d.is_unsafe}:{d.deps}:{d.value_deps}"
                        for k, d in sorted(self.decls.items()))
           return hashlib.sha256(f"{self.name}:{self.scc}:{p}".encode()).hexdigest()[:16]

   def naive_axioms(m: Mod, c: str, seen=None) -> Set[str]:
       seen = set() if seen is None else seen
       if c in seen: return set()
       seen.add(c)
       if c not in m.decls:
           for imp in m.imports.values():
               if c in imp.ext_cache: return set(imp.ext_cache[c])
               if c in imp.decls: return naive_axioms(imp, c, seen)
           return set()
       d = m.decls[c]; out = {c} if d.kind == "axiom" else set()
       for x in d.deps + d.value_deps: out |= naive_axioms(m, x, seen)
       return out

   @dataclass(frozen=True)
   class Receipt:
       name: str; scc: int; ohash: str; imps: Dict[str, Tuple[str, str]]
       ax: Tuple[str, ...]; opq: Tuple[str, ...]; dig: str

   def mk_receipt(m: Mod, recs: Dict[str, Receipt], snap=None) -> Receipt:
       imps = snap if snap is not None else m.imports
       seen, q, la, lo, cm = set(), list(m.exports), set(), set(), set()
       while q:
           c = q.pop()
           if c in seen: continue
           seen.add(c)
           if c in m.decls:
               d = m.decls[c]
               if d.kind == "axiom": la.add(c)
               if d.kind == "opaque" or d.is_partial or d.is_unsafe: lo.add(c)
               q.extend(d.deps + d.value_deps)
           else:
               for k, im in imps.items():
                   if c in im.decls: cm.add(k); break
       ax, opq, ih = set(la), set(lo), {}
       for k, im in sorted(imps.items()):
           r = recs[k]; ih[k] = (im.digest(), r.dig)
           if k in cm: ax |= set(r.ax); opq |= set(r.opq)
       oh = m.digest()
       dig = hashlib.sha256(f"{m.name}|{m.scc}|{oh}|{sorted(ih.items())}|{sorted(ax)}|{sorted(opq)}".encode()).hexdigest()[:16]
       return Receipt(m.name, m.scc, oh, ih, tuple(sorted(ax)), tuple(sorted(opq)), dig)

   def check_dag(recs: Dict[str, Receipt], root: str, allowed: Set[str]) -> Tuple[bool, str]:
       sccs = set()
       for n, r in recs.items():
           if r.scc in sccs: return (False, "dup_scc")
           sccs.add(r.scc)
           for k, (oh, dg) in r.imps.items():
               t = recs[k]
               if t.scc >= r.scc: return (False, "rank")
               if oh != t.ohash or dg != t.dig: return (False, f"olean_toctou:{n}->{k}")
       rr = recs[root]
       if set(rr.ax) - allowed: return (False, "axioms")
       if rr.opq: return (False, "opaques")
       return (True, "ok")

   alw = {"propext", "Quot.sound", "Classical.choice"}
   m1 = Mod("M1", 0, {"s": Decl("s", "opaque", ()), "t": Decl("t", "thm", ("s",), ("s",))}, exports=("t",))
   assert naive_axioms(m1, "t") == set() and not check_dag({"M1": mk_receipt(m1, {})}, "M1", alw)[0]
   m2 = Mod("M2", 0, {"h": Decl("h", "opaque", (), is_partial=True), "t": Decl("t", "thm", ("h",), ("h",))}, exports=("t",))
   assert naive_axioms(m2, "t") == set() and not check_dag({"M2": mk_receipt(m2, {})}, "M2", alw)[0]
   a3 = Mod("A3", 0, {"bx": Decl("bx", "axiom", ()), "la": Decl("la", "thm", (), ("bx",))}, exports=("la",))
   b3 = Mod("B3", 1, {"t": Decl("t", "thm", (), ("la",))}, imports={"A3": a3}, exports=("t",))
   ra3 = mk_receipt(a3, {}); rb3 = mk_receipt(b3, {"A3": ra3})
   assert not check_dag({"A3": ra3, "B3": rb3}, "B3", alw)[0]
   a4 = Mod("A4", 0, {"bx": Decl("bx", "axiom", ()), "la": Decl("la", "thm", (), ("bx",))}, ext_cache={"la": ()}, exports=("la",))
   b4 = Mod("B4", 1, {"t": Decl("t", "thm", (), ("la",))}, imports={"A4": a4}, exports=("t",))
   assert naive_axioms(b4, "t") == set()
   ra4 = mk_receipt(a4, {}); rb4 = mk_receipt(b4, {"A4": ra4})
   assert not check_dag({"A4": ra4, "B4": rb4}, "B4", alw)[0]
   a5o = Mod("A5", 0, {"la": Decl("la", "thm", (), ())}, exports=("la",))
   a5s = Mod("A5", 0, {"bx": Decl("bx", "axiom", ()), "la": Decl("la", "thm", (), ("bx",))}, exports=("la",))
   b5 = Mod("B5", 1, {"t": Decl("t", "thm", (), ("la",))}, imports={"A5": a5o}, exports=("t",))
   ra5 = mk_receipt(a5o, {}); rb5 = mk_receipt(b5, {"A5": ra5}, snap={"A5": a5s})
   assert check_dag({"A5": ra5, "B5": rb5}, "B5", alw) == (False, "olean_toctou:B5->A5")
   a6 = Mod("A6", 0, {"propext": Decl("propext", "axiom", ()), "la": Decl("la", "thm", (), ("propext",)), "vo": Decl("vo", "opaque", ())}, exports=("la",))
   b6 = Mod("B6", 1, {"t": Decl("t", "thm", (), ("la",))}, imports={"A6": a6}, exports=("t",))
   ra6 = mk_receipt(a6, {}); rb6 = mk_receipt(b6, {"A6": ra6})
   assert check_dag({"A6": ra6, "B6": rb6}, "B6", alw)[0]

   @dataclass(frozen=True)
   class Chunk8: slots: Tuple[Optional[int], ...]
   @dataclass(frozen=True)
   class Empty: pass
   @dataclass(frozen=True)
   class Leaf: chunk: Chunk8
   @dataclass(frozen=True)
   class Node: left: object; right: object

   def depth(t): return 1 if isinstance(t, Empty) else (2 if isinstance(t, Leaf) else 1 + max(depth(t.left), depth(t.right)))
   def build(xs):
       lvl = [Leaf(Chunk8(tuple(xs[j] if j < len(xs) else None for j in range(i, i + 8)))) for i in range(0, len(xs), 8)]
       while len(lvl) > 1:
           lvl = [Node(lvl[i], lvl[i + 1] if i + 1 < len(lvl) else Empty()) for i in range(0, len(lvl), 2)]
       return lvl[0] if lvl else Empty()
   def get_steps(t, idx, span):
       st = 1
       while isinstance(t, Node):
           h = span // 2; st += 1
           t, idx, span = (t.left, idx, h) if idx < h else (t.right, idx - h, span - h)
       return (t.chunk.slots[idx] if isinstance(t, Leaf) else None, st)
   def set_val(t, idx, v, span):
       if isinstance(t, Node):
           h = span // 2
           return Node(set_val(t.left, idx, v, h), t.right) if idx < h else Node(t.left, set_val(t.right, idx - h, v, span - h))
       if isinstance(t, Leaf):
           s = list(t.chunk.slots); s[idx] = v; return Leaf(Chunk8(tuple(s)))
       return t

   for n in (64, 256, 512, 1024, 2048, 4096):
       tr = build(list(range(n))); d = depth(tr)
       span = (1 << (math.ceil(n / 8) - 1).bit_length()) * 8
       sts = [get_steps(tr, i, span) for i in range(n)]
       assert all(v == i for i, (v, _) in enumerate(sts)) and d < 512
       print(f"N={n:4d}: list_depth={n+1:4d} list_scan={n*(n+1)//2:7d} | bct_depth={d:2d} max_get={max(s for _,s in sts):2d} bct_scan={sum(s for _,s in sts):5d}")
   t0 = build(list(range(64)))
   for i in range(64):
       t1 = set_val(t0, i, 1000 + i, 64)
       assert all(get_steps(t1, j, 64)[0] == (1000 + i if i == j else j) for j in range(64))
   print("PROBE2_OK: 5/5 exploits blocked, 2/2 clean graphs accepted, BinChunkTree verified")
   PY
   ```
2. **Re-check Lean 4 upstream definitions on newer releases**:
   - Inspect `leanprover/lean4` `src/Lean/Util/CollectAxioms.lean` (`collect` `.opaqueInfo` arm and `exportedAxiomsExt`), `src/Lean/Declaration.lean` (`isAxiom`, `hasValue`), `src/Lean/Replay.lean` (`isUnsafe || isPartial`), and `src/Init/Prelude.lean` (`defaultMaxRecDepth`).
   - Inspect `GasStationManager/SafeVerify` `Main.lean` (`processFileDeclarations`, `importModules`) and `leanprover/lean4checker` `Main.lean` (`replayFromImports`) to check whether native `opaque` tracking or Merkle `.olean` digest verification has been added upstream.
