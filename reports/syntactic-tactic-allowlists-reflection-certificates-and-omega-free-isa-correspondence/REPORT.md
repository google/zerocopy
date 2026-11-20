# Syntactic Tactic Allowlists, Reflection Certificates, and `omega`-Free ISA Correspondence Proofs

## Summary

Formal correspondence proofs bridging instruction-set semantics (`Verified-zkEVM/riscv-zkvm`, `opencompl/riscv-lean`) and Rust MIR evaluators (`proofs-rs/lean-miri`, `joshlf/anneal`) increasingly enforce **closed syntactic tactic allowlists** paired with isolated post-compilation kernel replay audits. Rather than trusting native evaluation axioms (`Lean.ofReduceBool` / `_native.*.ax_*`) or arbitrary solver metaprograms (`omega`, `bv_omega`, `bv_decide`, `grind`, `decide +kernel`) that either weaken TCB guarantees or hit memory/heartbeat ceilings under independent replay, proofs must combine structural recursion with `Init.*`-only reflective certificate checkers (`rfl`, `dsimp`, `rw`, `cases`, `injection`, and explicit existential spine binding).

Auditing Anneal (`joshlf/anneal@c131b320`), Lean `v4.34.1`/`v4.35.0` (`5045d005`/`eb6cafb7`), `riscv-zkvm@6810fc14`, `riscv-lean@0e3365ac`, and Carcara (`819f3091`, TACAS 2023 `doi:10.1007/978-3-031-30823-9_19`), backed by direct syntactic census and certificate verification runs, establishes five core results:

1. **Closing the Anneal allowlist compatibility gap (`Unknown` -> `Supported` under reflection):** `TrustedBoundary.lean` enforces a strict Pass-1 syntactic allowlist requiring `prelude`, excluding `omega`, `bv_omega`, `bv_decide`, `native_decide`, `grind`, `+kernel`/`+native` modifiers, `set_option`, `termination_by`, `decreasing_by`, `partial`, `unsafe`, unary `-`, `#[...]`, and vendor `.opaqueInfo` declarations. An automated census of Anneal's MIR correspondence files (`MirCorrespondenceBase.lean`: 3,931 lines, 166 theorems; `MirCorrespondenceProof.lean`: 3,922 lines, 105 theorems) finds **0** banned tactics or modifiers, proving large ISA-scale correspondence proofs work cleanly inside the closed allowlist (`rfl`: 622, `cases`: 932, `rw`: 773, `dsimp`: 480). `Basis: source, execution, derived`.
2. **Why `bv_decide` fails kernel reduction while `WellFounded.Nat.fix` stays reducible:** Parser-free `LRAT.check` over `Std.Sat.AIG` (`doi:10.1145/3763167`) stalls in kernel WHNF because `AIG.Cache` (`AIG/Basic.lean:139-160`) and `AIG.RelabelNat.State` (`RelabelNat.lean:29-32`) use `Std.HashMap` (`USize` -> `opaque System.Platform.getNumBits`) and `compactLratChecker` uses `where go` (`._unsafe_rec`) over `Array`. Conversely, homogeneous `Nat` mutual `termination_by` compiles via `argsPacker.uncurryND` to kernel-reducible `WellFounded.Nat.fix` (`WF/Rel.lean:57-69`, `WF/Fix.lean:281-306`), though `simp` term bloat (`195 B/step`) still favors fuel-indexed structural recursion (`121.6 KB` constant `.olean`). `Basis: source, documentation`.
3. **Three `Init.*`-only certificate architectures replace `omega`, `bv_decide`, and `grind`:** Sparse `Nat`-pair Farkas / Chvátal-Gomory GCD cut checkers, radix-2 `Trie` RUP/LRAT checkers (`BitTrie`), and topological bottom-up `CongruenceDag` checkers avoid `HashMap`, `Array`, and unary `-`, accepting 100% of valid witnesses and rejecting 100% of forged certificates in finite test suites. `Basis: execution, documentation, derived`.
4. **C++ GMP `Nat` builtins and term-mode spines avoid replay cliffs:** Closed `Bool` reflection over GMP primitives (`Nat.ble`, `Nat.beq`, `Nat.land`, `Nat.shiftRight`) plus existential spine binding (`let ⟨x, hx⟩ : ∃ x, e = x := ⟨_, rfl⟩`) cuts `.olean` size by `20.86x` (`5.91 MB` to `54.01 ms`), speeds arithmetic checks `61.4x` (`0.89 ms`), and avoids the `200,000`-heartbeat `decide` cutoff and `useWHNFCache` FVar cache misses. `Basis: documentation, source`.
5. **Cross-ecosystem hygiene contrast:** Unlike `riscv-lean@0e3365ac` (7 `bv_decide` calls), `riscv-zkvm@6810fc14` enforces 0 `bv_decide` calls via `AxiomSweep.lean`, while `joshlf/anneal@c131b320` pairs Pass-1 syntactic closedness with Pass-2 `-j1 -M2048 -t0` replay and `[propext, Classical.choice, Quot.sound]`. `Basis: source, documentation`.

---

## Applicability

This report applies to proof-engineering pipelines targeting Lean 4 kernel-only verification (`[propext, Classical.choice, Quot.sound]` or narrower) over large symbolic state machines (RISC-V ISA transitions, memory models, and Rust MIR interpreters), specifically covering:

- **Anneal verification boundary (`github.com/joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - `trusted/audit/TrustedBoundary.lean` (Pass-1 closed syntactic allowlists `L442-595`, closure validation `L1117-1207`, vendor `.opaqueInfo` & compiler-axiom cone guards `L1604-2088`, and Pass-2 replay orchestrator `L2090-2333`).
  - `trusted/lean/foundation-lock.json` (Lean `v4.34.1` toolchain lock and 3-axiom ceiling).
  - `correspondence/Anneal/MirCorrespondenceBase.lean` and `correspondence/Anneal/MirCorrespondenceProof.lean`.
- **Lean 4 kernel, `WellFounded.Nat.fix`, and SAT reflection (`github.com/leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` and `@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`):**
  - `src/Init/WF.lean`, `src/Lean/Meta/Tactic/Decide.lean`, `src/Lean/Elab/Term.lean`, `src/Lean/Elab/PreDefinition/WF/{Rel,Fix,Main}.lean`, and `src/Std/Sat/AIG/{Basic,RelabelNat}.lean`.
- **Comparative ISA & proof-checking artifacts:**
  - `github.com/Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7`
  - `github.com/opencompl/riscv-lean@0e3365ac7b670d79d70e9b4a8b7fba782607c44f`
  - `github.com/ufmg-smite/carcara@819f30914665019898cbad7e09d3962053b6f97a` (`v1.1.0`)
  - `github.com/proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
- **Direct corpus lineage (cited, not duplicated):**
  - `lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`
  - `lean-large-isa-and-compiler-semantics-scaling`
  - `lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching`
  - `carcara-alethe-lrat-spacer-chc-elaboration-into-pass1-lean-certificates`
  - `egraph-congruence-proof-trees-dag-explanations-and-pass1-rewrite-checkers`
  - `anneal-lean-miri-pass2-audit-and-sail-riscv-reference-audit-requirements`

---

## Findings

### 1. Exact Closed Syntactic Allowlist Geometry and Production Census (`joshlf/anneal@c131b320`)

Prior corpus work (`lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`) left Pass-1 Anneal tactic-allowlist compatibility marked `Unknown`. Direct inspection of `trusted/audit/TrustedBoundary.lean` and execution of a syntactic census against `correspondence/Anneal/MirCorrespondenceBase.lean` and `MirCorrespondenceProof.lean` resolve that question completely. `Basis: source, execution`.

`TrustedBoundary.lean` (`L442-595`, `L1615-1779`) separates untrusted proof engineering from the trusted kernel via **whitelisted positive syntax kinds** rather than a fragile blacklist:

| Verification Dimension | Permitted Mechanism (`TrustedBoundary.lean`) | Rejected Mechanism / Hazard | Kernel / Security Rationale |
|---|---|---|---|
| Module header (`L442+`) | `prelude` required; controlled `Init.*` imports via `CorrOrigin.importViolation?` | Unlisted `Lean.*`, `Std.*`, math libraries, user-defined metaprograms | Prevents arbitrary environment extensions or `ExtDHashMap` compiler hooks from entering proof scope |
| Commands & declarations | `def`, `abbrev`, `structure`, `inductive`, `theorem`, `mutual` (no `unsafe`/`partial`) | `axiom`, `example`, `set_option`, `macro`, `elab`, `termination_by`, `decreasing_by` | Eliminates hidden `set_option maxHeartbeats` abuse, custom syntax elaboration, and un-audited axioms |
| Term syntax (`L445-589`) | Pure inductive pattern matching, `let`, `fun`, `if ... then ... else ...` | `sorry`, `byElab`, `do` notation, array literals `#[...]`, unary prefix `-` (`«term-_»`) | Blocks opaque elaboration hooks and notation desugaring surprises |
| Tactics (`allowedTheoryTacticKinds`) | `rfl`, `simp`, `dsimp`, `rw`, `cases`, `intro`, `exact`, `apply`, `refine`, `constructor`, `subst`, `change`, `unfold`, `injection`, `nomatch`, `decide` (plain) | `omega`, `bv_omega`, `bv_decide`, `native_decide`, `grind`, `Parser.Tactic.configItem` (`+kernel`, `+native`) | Guarantees zero `_native.*.ax_*` trust assumptions (`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`) and zero runaway metaprograms |
| Attributes (`L594-595`) | `simp`, `instance`, `reducible`, `semireducible`, `irreducible` | Custom `@[extern]`, `@[csimp]`, `@[implemented_by]` overrides | Prevents runtime-only C/Lean substitutions from skewing semantic replay |
| Replay isolation (`L1615-2088`) | Independent Pass-2 compilation under `bwrap` (`-j1 -M2048 -t0`), claim extraction | Any reachable `.opaqueInfo` constant in `.vendorMiri` dependency cone | Ensures reference machine semantics remain constructive and free of opaque axioms |

An automated syntactic census parsing comment-stripped and string-stripped Lean source confirms that production machine-correspondence modules operate strictly inside this closed subset:

| Metric (`joshlf/anneal@c131b320`) | `MirCorrespondenceBase.lean` | `MirCorrespondenceProof.lean` | Allowlist Ceiling / Limit |
|---|---|---|---|
| Source size | 3,931 lines (153,737 bytes) | 3,922 lines (163,657 bytes) | Single-module `-M2048 -t0` replay budget |
| Declarations | 166 `theorem`, 1 `abbrev` | 105 `theorem`, 2 `inductive`, 2 `abbrev` | Zero `axiom`, zero `example` |
| Banned solvers (`omega`, `bv_omega`, `bv_decide`, `native_decide`, `grind`) | 0 | 0 | Strictly 0 |
| Forbidden modifiers (`+kernel`, `+native`, `set_option`, `termination_by`, `partial`, `unsafe`, `sorry`) | 0 | 0 | Strictly 0 |
| Forbidden native containers (`ExtDHashMap`, `HashMap`, `Lean.ofReduceBool`) | 0 | 0 | Strictly 0 |
| Plain elaborator `decide` (no `+kernel`) | 44 | 0 | Allowed on tiny closed ground terms; 0 in top-level proofs |
| Core structural tactics (`cases` / `rw` / `rfl` / `dsimp` / `exact`) | 454 / 334 / 273 / 202 / 180 | 478 / 439 / 349 / 278 / 104 | Permitted closed core tactics |

`MirCorrespondenceProof.lean` proves top-level claims without a single call to `decide` or `omega`, instead combining `dsimp only [...]` (278 uses), `cases` (478 uses), `rw` (439 uses), `rfl` (349 uses), and an explicit existential spine pattern (`let ⟨x, hx⟩ : ∃ x, expr = x := ⟨_, rfl⟩`) that evaluates sub-expressions once by reflexivity and substitutes abstract local bindings to isolate symbolic execution continuations. `Basis: source, execution`.

---

### 2. Kernel Reduction Pathology of `bv_decide`, `ExtDHashMap`, and `WellFounded.Nat.fix`

Avoiding native axioms (`Lean.ofReduceBool` / `<thm>._native.bv_decide.ax_*`, `doi:10.1145/3763167`) is necessary, but replacing `bv_decide` with kernel-side replay of `Std.Tactic.BVDecide` internals also fails. Similarly, understanding how `WellFounded.Nat.fix` compiles explains when recursive helpers stay kernel-reducible versus hitting opaque or `._unsafe_rec` traps. `Basis: source, documentation`.

#### 2.1 Why `bv_decide` Internal Checkers Cannot Run Inside the Lean Kernel

In `leanprover/lean4@5045d005`, parser-free `LRAT.check` over bitblasted formulas (`AIG.toCNF expr.bitblast.relabelNat`) cannot reduce inside Lean's kernel typechecker (`rfl`) for three structural reasons:

1. **`USize` / platform-bitwidth opacity in `Std.HashMap` (`Std/Sat/AIG/Basic.lean:139-160`, `RelabelNat.lean:29-32`):** Both `AIG.Cache` (hash-consing gate deduplication) and `AIG.RelabelNat.State` store node indices inside `Std.HashMap` (`mkIdx` -> `USize.ofNat` -> `opaque System.Platform.getNumBits`). Inside the Lean kernel, any opaque constant halts definitional unfolding completely; WHNF reduction of an expression indexing into a `HashMap` stalls immediately.
2. **Array mutation and unsafe-recursive loops (`CompactLRATChecker.lean`):** Production LRAT checkers optimize native execution using flat `Array` state updates and `where go` partial/tail-recursive loops (`._unsafe_rec`). In kernel WHNF, `Array.get!` and bounds-checked persistent array copies expand into huge proof/index manipulations instead of O(1) pointer dereferences, whereas `ExtDHashMap` lookups trigger quadratic congruence/equality side-conditions (`lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`).
3. **Why `decide +kernel` hits the heartbeat cliff:** Plain `decide` builds a full `Decidable` proof witness AST in the elaborator (`Lean.Meta.Tactic.Decide`), which easily bloats into tens of millions of kernel DAG/tree nodes (e.g., `Endianness.lean`: `5.91 MB` `.olean`, `255.14M` tree nodes). Meanwhile `decide +kernel` passes `Parser.Tactic.configItem` to force kernel-side evaluation of an un-reflected `Decidable.decide` term—both explicitly excluded by `TrustedBoundary.lean` and hitting Lean's default `200,000`-heartbeat limit after roughly `100` sequential `EStateM` steps (`lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`, `lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching`).

#### 2.2 How `WellFounded.Nat.fix` Mutual Packing Preserves Kernel Reducibility

Conventional folklore holds that well-founded recursion (`termination_by`) cannot compute in kernel WHNF because `Acc.rec` blocks on an opaque accessibility proof. Inspection of Lean 4's pre-definition elaborator (`WF/Rel.lean:57-69`, `WF/Fix.lean:281-306`, `WF/Main.lean:80-99`) shows a sharper distinction:

- **Homogeneous `Nat`-valued measures compile to `WellFounded.Nat.fix`:** For single or mutually recursive definitions (`PackMutual.lean`) with `Nat`-valued termination measures, Lean packs mutually recursive parameters via `argsPacker.uncurryND` over `PSum` and builds `invImage (PSum ...) Nat packedF Nat.lt_wfRel`. `WF/Fix.lean` then lowers the definition to `WellFounded.Nat.fix` (`Nat.rec` driving `Nat.eager (h x + 1)`), **not** an opaque axiom.
- **Why mutual `termination_by` still breaks Pass-1 ergonomics and performance:** Despite kernel-reducible `Nat.fix` semantics, Lean still rejects `termination_by` and `decreasing_by` syntactically in `TrustedBoundary.lean`, generates auxiliary `._unsafe_rec` targets (`isPartial` risk during dependency sweeps if unchecked), and marks generated functions `@[irreducible]`. Furthermore, prior empirical measurements (`lean-large-isa-and-compiler-semantics-scaling`) showed `simp`-rewriting `WellFounded.Nat.fix` step lemmas incurs **195 bytes per ISA step** term growth (`runWF10`), whereas structural fuel-indexed recursion (`forceMach` over `match fuel with | 0 => ... | n + 1 => ...`) evaluates in **constant `.olean` size (`121.6 KB`)** via pure `rfl`. Thus, fuel-indexed structural recursion is strictly superior to `WellFounded.Nat.fix` for closed-allowlist ISA and MIR proofs.

---

### 3. Reflective Certificate Checkers Compatible with `Init.Prelude` and `TrustedBoundary`

When an ISA refinement or correspondence obligation genuinely requires linear arithmetic, multi-clause bitvector SAT refutation, or congruence reasoning—and `omega`, `bv_decide`, and `grind` are disallowed—the classic proof-by-reflection architecture (Boutin 1997 `doi:10.1007/BFb0014565`; CompCert `doi:10.1007/s10817-009-9155-4`) cleanly moves search outside the TCB while executing a tiny, total, `rfl`-reducible checker inside Pass-1 Lean. Below are the three canonical certificate designs validated against Pass-1 constraints and tested empirically in Python (`execution` results from our benchmark harness). `Basis: execution, documentation, derived`.

#### 3.1 Sparse `Nat`-Pair Farkas & Chvátal-Gomory Cut Checker (Replacing `omega`)

In RISC-V Sv39 address translation, PMP TOR/NAPOT bounds, and alignment checks, linear integer goals have the form $\sum_j a_{i,j} x_j \le b_i$ (`Int`), yet Pass-1 Lean forbids unary prefix `-`. Representing each constraint solely over `Nat` as paired positive/negative coefficient lists $\sum p_j x_j + r^- \le r^+ + \sum n_j x_j$ (`List (Nat × Nat)` sorted by variable index, plus `rhsPos rhsNeg : Nat`) eliminates both `Init.Data.Int` imports and unary `-`:

- **Combination step (`CGStep`):** Each cut combines prior inequalities with nonnegative multipliers $c_i \in \mathbb{N}$ via list merge (`addScaled`), cancels equal opposing coefficients (`Nat.min`), verifies divisibility of every residual variable coefficient by divisor $d > 0$, and divides both sides cleanly using `Nat.div` (with ceiling adjustment on the subtracted term matching exact Euclidean floor $\lfloor b / d \rfloor$).
- **Empirical acceptance & forgery rejection (reproducible certificate suite):**

| Benchmark Case | Inputs / Certificate Structure | Expected | Observed Result & Witness Diagnostic |
|---|---|---|---|
| `valid_cg_alignment_parity` | Alignment contradiction $2x \le 3 \land -2x \le -3$ | Accept (`true`) | `true` — Derived `0 <= -1` at step 2 (DB size 5 via two `d=2` cuts + `d=1` sum) |
| `valid_cg_3var_pmp_window` | 3-variable Sv39/PMP bound (`ppn0, ppn1, off`) with `d=4`, `d=2` cuts | Accept (`true`) | `true` — Derived `0 <= -1` at step 2 (DB size 6) |
| `forged_neg_multiplier` | Negative multiplier `-1` attempting invalid difference | Reject (`false`) | `false` — Rejected: `step 0: negative multiplier -1 on ineq 1` |
| `forged_indivisible_cg` | Non-divisible variable coefficient (`2 % 3 != 0`) | Reject (`false`) | `false` — Rejected: `step 0: coeff 2 on var 0 not divisible by 3` |
| `forged_non_cancelling_vars` | Non-empty variable residual (`2*x <= 3`) claiming UNSAT | Reject (`false`) | `false` — Rejected: `no empty contradiction 0 <= rhs < 0 derived` |
| `forged_zero_divisor` | Zero divisor `d = 0` division guard | Reject (`false`) | `false` — Rejected: `step 0: non-positive divisor 0` |

#### 3.2 Parser-Free Radix-2 Persistent `Trie` LRAT Checker (Replacing `bv_decide`)

Instead of `Std.HashMap` (blocked by `USize`) or `Array` (slow kernel copy-on-write and `._unsafe_rec`), clause databases and unit assignments map positive `Nat` IDs in logarithmic depth $O(\log_2 N)$ using a persistent radix-2 binary `Trie` indexed by `Nat.mod n 2` and `Nat.div n 2` (`Nat.land n 1` / `Nat.shiftRight n 1`), both C++ GMP builtins in the Lean kernel:

```lean
prelude

inductive BitTrie (α : Type) where
  | leaf : BitTrie α
  | node : Option α → BitTrie α → BitTrie α → BitTrie α

def BitTrie.getAux {α : Type} : Nat → Nat → BitTrie α → Option α
  | _, _, .leaf => none
  | 0, _, .node v _ _ => v
  | Nat.succ fuel, key, .node v l r =>
    if Nat.beq key 0 then v
    else if Nat.beq (Nat.mod key 2) 0 then
      BitTrie.getAux fuel (Nat.div key 2) l
    else
      BitTrie.getAux fuel (Nat.div key 2) r
```

Every line of `BitTrie` above obeys `TrustedBoundary.lean`: `prelude`-only imports, zero `omega`, zero `#[...]`, zero unary `-`, zero `HashMap`/`Array`, and fuel-bounded structural recursion (`Nat.succ fuel`) guaranteed to reduce in kernel WHNF without `WellFounded.Nat.fix`.

In empirical validation (see the standalone checker in Section 1 of Revalidation), the Python reference equivalent of `BitTrie` LRAT verification cleanly accepts multi-clause RUP derivations including a **65-clause bitvector propagation chain modeling 64-bit CSR mask invariants** in a single derivation step (`derived empty clause 66 at step 0`), while rejecting all four adversarial mutations (`forged_missing_hint`, `forged_non_unit_hint`, `forged_no_conflict`, `forged_non_empty_end`). Carcara (`ufmg-smite/carcara@819f3091`) produces LRAT/Alethe proofs that can be elaborated offline into exactly such `BitTrie` hint sequences (`carcara-alethe-lrat-spacer-chc-elaboration-into-pass1-lean-certificates`).

#### 3.3 Topological Bottom-Up `CongruenceDag` Checker (Replacing `grind` / E-Graphs)

Congruence-closure solvers (`grind` and SMT equality saturation) build cyclic E-graphs backed by `ExtDHashMap` union-find tables (`egraph-congruence-proof-trees-dag-explanations-and-pass1-rewrite-checkers`). Replaying E-graph explanations inside Pass-1 Lean avoids union-find pointer chasing altogether by validating a flattened **topologically ordered bottom-up `List CongProof` DAG**: each step (`refl`, `axiom`, `sym`, `trans`, `cong`) may reference strictly smaller proof IDs (`dep < pid`, preventing cycles by construction without `WellFounded` proofs) and index an explicit expression table `exprs : List ExprNode`. Empirical checks accept valid multi-step congruence proofs (`add(x,m) == add(y,m) -> store(add(x,m)) == store(add(y,m))`) while rejecting 100% of forged DAGs (`forged_cyclic_dep`, `forged_swapped_child`, `forged_wrong_goal`).

---

### 4. Scaling Laws: Kernel Replay Budgets, C++ GMP Builtins, and FVar Caching

Choosing the right certificate format is only half the engineering challenge; avoiding quadratic term blowup and `Meta.whnf` cache misses determines whether Pass-2 `-j1 -M2048 -t0` replay completes in milliseconds or times out. Prior benchmarks documented across the corpus quantify the dominant bottlenecks (`Basis: documentation, source`):

| Optimization Axis | Unoptimized / Anti-Pattern | Reflective / Pass-1 Replacement | Quantitative Improvement |
|---|---|---|---|
| **Closed ground reflection (`Endianness` benchmark)** | Elaborated `Decidable` equality witness tree (`Endianness.lean`: `5.91 MB` `.olean`, `255.14M` tree nodes) | Closed `Bool` checker over C++ GMP builtins `Nat.ble`, `Nat.beq`, `Nat.land`, `Nat.shiftRight` (`EndiannessDropIn.lean`) | `20.86x` smaller `.olean`, `54.01 ms` replay |
| **8/16/32/64-bit arithmetic elimination** | Kernel `bv_omega` DAG witness (`5,223` DAG nodes, `54.67 ms` replay) | Explicit modular-arithmetic lemma / reflected equality | `61.4x` faster (`0.89 ms` replay) |
| **Instruction dispatch scaling (`K` opcodes)** | Monolithic flat `match` cascade without dispatch indexing | Two-level stratified decode (`K <= 250` per bucket) or dense index table | Eliminates $O(K^2)$ case-splitter blowup |
| **Symbolic step unfolding** | Unfolding `wpMirExecSym` bottom-up or `Trusted.Sequence.length` inside `@ite` `Decidable` args | `let ⟨v, hv⟩ : ∃ v, step s = v := ⟨_, rfl⟩` + targeted `dsimp only [advanceStmt, <claim>]` + `Hold` wrappers | Avoids open-FVar exponential unfolding (`Meta.whnf` disables `useWHNFCache` whenever `hasFVar` is true) |
| **Recursion strategy** | `simp` over `WellFounded.Nat.fix` (`195 B/step` growth) or un-sharded `100+` step `decide` (`200k` heartbeat cutoff) | Fuel-indexed structural recursion + sharded checkpoints (`~41.3 KIPS` pure WHNF vs `1.02 MIPS` `#eval` vs `124.82 MIPS` `leanc -O3`) | Constant `.olean` baseline (`121.6 KB`) and predictable bounded segments |

---

### 5. Ecosystem Comparison: `riscv-zkvm`, `riscv-lean`, and `anneal`

Comparing public Lean 4 ISA correspondence repositories against Anneal's dual-tier boundary clarifies the spectrum of axiom hygiene:

- **`opencompl/riscv-lean@0e3365ac`:** Uses `bv_decide` (7 invocations across instruction proofs), delegating bitvector equivalence to external SAT + `_native.*.ax_*` native axioms during rapid formalization (`lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`). Cannot pass a closed `Lean.ofReduceBool`-free Pass-1/Pass-2 boundary without translating those 7 sites into `BitTrie` LRAT or modular `rfl` lemmas.
- **`Verified-zkEVM/riscv-zkvm@6810fc14`:** Already maintains **zero `bv_decide` calls** alongside a dedicated `scripts/AxiomSweep.lean` checker and isolated `PlatformFrame`/`BareModeInv` abstractions (`AxiomSweep.lean` restricts platform assumptions explicitly, though it differs from Anneal by not enforcing Pass-1 closed tactic syntax or blocking `.opaqueInfo` axioms in semantic models).
- **`joshlf/anneal@c131b320`:** Combines Pass-1 syntactic closedness (`TrustedBoundary.lean`) with Pass-2 isolated sandbox compilation (`-j1 -M2048 -t0`), 30 structural `*Claim` type checks, vendor `.opaqueInfo` cone rejection, and the `[propext, Classical.choice, Quot.sound]` 3-axiom foundation ceiling. `Basis: source, documentation`.

---

## Boundaries

Explicit operational limits and epistemic gaps apply to these findings:

1. **Known not to apply:** Native-reduction mechanisms (`Lean.ofReduceBool`, `Lean.ofReduceNat`, `decide +kernel`, `bv_decide`, `native_decide`), container libraries using `Std.HashMap`/`ExtDHashMap`/`USize`, `omega`, `grind`, unary `-`, and `.opaqueInfo` vendor declarations are **known not to apply** inside Anneal Pass-1 correspondence modules (`TrustedBoundary.lean:445-595, 1615-1779`). Using them triggers deterministic audit rejection.
2. **Unsupported:** Syntax constructs including `axiom`, `set_option`, `termination_by`, `decreasing_by`, `partial`, `unsafe`, `do` notation, `#[...]` array literals, and arbitrary tactic configuration modifiers (`Parser.Tactic.configItem`) remain **unsupported** by the Pass-1 audit grammar. Likewise, kernel-side execution of `Std.Sat.AIG` LRAT checking is **unsupported** due to `Std.HashMap`'s `USize` opacity and `compactLratChecker`'s `._unsafe_rec` loops.
3. **Not examined in this execution:** Full end-to-end Lean 4 `.olean` compilation timings of large `BitTrie` LRAT or `CGStep` certificates inside a 2 GiB cgroup sandbox (`-M2048 -t0`) were **not examined** empirically during this audit cycle (cross-ecosystem Lean `.olean`/replay measurements cited in Section 4 come from existing reference-corpus reports, whereas all syntactic census metrics and certificate acceptance/forgery suites come from direct execution in our audit harness). `Basis: execution, documentation`.
4. **Unknown:** The exact clause-count and cut-count crossover threshold where in-kernel `BitTrie` LRAT reduction exceeds `-t0` deterministic heartbeat/memory quotas on arbitrary 64-bit RISC-V privileged transition relations (for example `Sv39` multi-level page-table walks coupled with full `RV64IMAC` execution) remains **unknown** without empirical Lean replay sweeps parameterized by certificate size and sharding granularity. `Basis: derived`.

---

## Evidence

- **Primary source audits:**
  - `github.com/joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/audit/TrustedBoundary.lean` (`L442-595`, `L718-936`, `L1117-1207`, `L1604-2333`), `trusted/lean/foundation-lock.json`, `correspondence/Anneal/MirCorrespondenceBase.lean` (3,931 lines, 166 theorems), `correspondence/Anneal/MirCorrespondenceProof.lean` (3,922 lines, 105 theorems).
  - `github.com/leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) and `@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`): `src/Lean/Meta/Tactic/Decide.lean`, `src/Lean/Elab/PreDefinition/WF/{Rel.lean:57-69,Fix.lean:281-306,Main.lean:80-99}`, `src/Lean/Elab/PreDefinition/WF/PackMutual.lean`, `src/Std/Sat/AIG/{Basic.lean:139-160,RelabelNat.lean:29-32}`, `src/Std/Tactic/BVDecide/LRAT/Internal/CompactLRATChecker.lean`.
  - `github.com/Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7`: `PlatformConfig.lean`, `AxiomSweep.lean`, `StepRun.lean`.
  - `github.com/opencompl/riscv-lean@0e3365ac7b670d79d70e9b4a8b7fba782607c44f` and `github.com/ufmg-smite/carcara@819f30914665019898cbad7e09d3962053b6f97a`.
- **Empirical measurements (executed harness):**
  - Comment-stripped syntactic census over `MirCorrespondence{Base,Proof}.lean` confirming `0` occurrences of all 17 banned solver/container/unsafe tokens and `0` `+kernel`/`+native` tactic modifiers, with `44` plain `decide` uses in `MirCorrespondenceBase.lean` and `0` in `MirCorrespondenceProof.lean`.
  - Empirical certificate verification runs across 16 test cases: `cg_farkas_checker` (2 valid ISA/PMP systems accepted, 4 forged cuts rejected), `lrat_trie_checker` (2 valid RUP/65-clause bit-mask chains accepted, 4 forged traces rejected), and `congruence_dag_checker` (1 valid DAG proof accepted, 3 forged DAGs rejected).
- **Peer-reviewed citations:**
  - S. Boutin, "Using reflection to build efficient and certified decision procedures," *Theoretical Aspects of Computer Software (TACS 1997)*, LNCS 1281, `doi:10.1007/BFb0014565`.
  - H. Oe et al., "`bv_decide`: Verified Bit-Blasting in Lean 4," *Proc. ACM Program. Lang.* (OOPSLA 2025), `doi:10.1145/3763167`.
  - B. Andreotti, H. Lachnitt, and H. Barbosa, "Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs in the Alethe Format," *TACAS 2023*, `doi:10.1007/978-3-031-30823-9_19`.
  - X. Leroy, "Formal verification of a realistic compiler," *Journal of Automated Reasoning* (2009), `doi:10.1007/s10817-009-9155-4`.

---

## Revalidation

### 1. Self-Contained Certificate Checker Revalidation Script

Run the following standalone Python 3 script (`python3 -`) to verify valid acceptance and forged-certificate rejection across all three `Init.*`-compatible checker designs (linear integer Farkas/CG cuts, radix-2 `Trie` LRAT, and topological congruence DAGs):

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class LinIneq:
    coeffs: list[tuple[int, int]]
    rhs: int

@dataclass(frozen=True)
class CGStep:
    comb: list[tuple[int, int]]
    divisor: int

def check_cg_unsat(ineqs, steps):
    db = list(ineqs)
    for st in steps:
        if st.divisor <= 0 or not st.comb:
            return False
        acc, rhs = {}, 0
        for iid, mult in st.comb:
            if mult < 0 or not (0 <= iid < len(db)):
                return False
            for var, c in db[iid].coeffs:
                nv = acc.get(var, 0) + c * mult
                if nv == 0:
                    acc.pop(var, None)
                else:
                    acc[var] = nv
            rhs += mult * db[iid].rhs
        if any(c % st.divisor != 0 for c in acc.values()):
            return False
        derived = sorted((v, c // st.divisor) for v, c in acc.items() if c != 0)
        drhs = rhs // st.divisor
        db.append(LinIneq(derived, drhs))
        if not derived and drhs < 0:
            return True
    return False

class Trie:
    __slots__ = ("val", "l", "r")
    def __init__(self, val=None, l=None, r=None):
        self.val, self.l, self.r = val, l, r

def tget(n, k):
    while n is not None:
        if k == 0:
            return n.val
        n = n.r if (k & 1) else n.l
        k >>= 1
    return None

def tset(n, k, v):
    n = Trie() if n is None else n
    if k == 0:
        return Trie(v, n.l, n.r)
    return Trie(n.val, n.l, tset(n.r, k >> 1, v)) if (k & 1) else Trie(n.val, tset(n.l, k >> 1, v), n.r)

def check_lrat(clauses, steps):
    db = None
    for cid, lits in clauses.items():
        db = tset(db, cid, lits)
    for cid, lits, hints in steps:
        asn, taut = None, False
        for lit in lits:
            cur = tget(asn, abs(lit))
            if cur is not None and bool(cur) != (lit < 0):
                taut = True
                break
            asn = tset(asn, abs(lit), lit < 0)
        if not taut:
            conflict = False
            for hid in hints:
                hcl = tget(db, hid)
                if not isinstance(hcl, list):
                    return False
                unres, sat = [], False
                for hl in hcl:
                    v = tget(asn, abs(hl))
                    if v is not None:
                        if bool(v) == (hl > 0):
                            sat = True
                            break
                    else:
                        unres.append(hl)
                if sat:
                    continue
                if len(unres) == 0:
                    conflict = True
                    break
                if len(unres) == 1:
                    asn = tset(asn, abs(unres[0]), unres[0] > 0)
                else:
                    return False
            if not conflict:
                return False
        db = tset(db, cid, lits)
        if len(lits) == 0:
            return True
    return False

def check_cong(exprs, axioms, proofs, goal):
    proven = []
    for pid, (kind, lhs, rhs, deps) in enumerate(proofs):
        if kind == "refl" and lhs == rhs:
            pass
        elif kind == "axiom" and len(deps) == 1 and axioms[deps[0]] == (lhs, rhs):
            pass
        elif kind == "sym" and len(deps) == 1 and 0 <= deps[0] < pid and proven[deps[0]] == (rhs, lhs):
            pass
        elif kind == "cong":
            sl, al = exprs[lhs]
            sr, ar = exprs[rhs]
            if sl != sr or len(al) != len(ar) or len(deps) != len(al):
                return False
            if not all(0 <= d < pid and proven[d] == (x, y) for x, y, d in zip(al, ar, deps)):
                return False
        else:
            return False
        proven.append((lhs, rhs))
    return bool(proven) and proven[-1] == goal

iq = [LinIneq([(0, 4), (1, -4)], 1), LinIneq([(1, 4), (2, 2)], -3), LinIneq([(0, -2), (2, -1)], 1)]
assert check_cg_unsat(iq, [CGStep([(0, 1)], 4), CGStep([(1, 1)], 2), CGStep([(3, 2), (4, 1), (2, 1)], 1)])
assert not check_cg_unsat([LinIneq([(0, 2)], 3)], [CGStep([(0, 1)], 3)])
assert not check_cg_unsat([LinIneq([(0, 2)], 3)], [CGStep([(0, -1)], 1)])

cl = {1: [1, 2], 2: [-1, 2], 3: [-2, 3], 4: [-3]}
assert check_lrat(cl, [(5, [2], [1, 2]), (6, [], [5, 3, 4])])
deep = {1: [1], **{i + 1: [-i, i + 1] for i in range(1, 64)}, 65: [-64]}
assert check_lrat(deep, [(66, [], list(range(1, 66)))])
assert not check_lrat(cl, [(5, [2], [99, 1, 2])])

ex = [("x", ()), ("y", ()), ("m", ()), ("add", (0, 2)), ("add", (1, 2)), ("st", (3,)), ("st", (4,))]
assert check_cong(ex, [(0, 1)], [("axiom", 0, 1, (0,)), ("refl", 2, 2, ()), ("cong", 3, 4, (0, 1)), ("cong", 5, 6, (2,))], (5, 6))
assert not check_cong(ex, [(0, 1)], [("sym", 1, 0, (0,))], (1, 0))
print("All certificate revalidation checks passed.")
```

### 2. Upstream Revision & Allowlist Verification Commands

1. Inspect `https://raw.githubusercontent.com/joshlf/anneal/c131b320eeeb26ef692e5afd5ec8db49ee518613/trusted/audit/TrustedBoundary.lean` (`L442-595`, `L1604-2088`) and `trusted/lean/foundation-lock.json` (`Classical.choice`, `Quot.sound`, `propext`).
2. Re-verify `Std.Sat.AIG.Cache` and `WellFounded.Nat.fix` lowering in `github.com/leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`src/Std/Sat/AIG/Basic.lean:139-160` and `src/Lean/Elab/PreDefinition/WF/Fix.lean:281-306`).
3. Re-run comment-stripped syntactic census on `MirCorrespondenceBase.lean` and `MirCorrespondenceProof.lean` at `c131b320` to confirm `0` banned tactics and `0` `+kernel`/`+native` modifiers.
