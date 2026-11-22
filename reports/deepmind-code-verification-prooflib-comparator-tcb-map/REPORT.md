# Lean 4 Kernel-Reflective Proof Automation, Comparator Verification, and TCB Auditing in `google-deepmind/code-verification`

## Summary

`google-deepmind/code-verification` (commit `8c8d371f1962ac73435c8eb148678991f5c3470d`, Lean `v4.35.0`) combines three reusable Lean 4 verification architectures that stay strictly within the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `native_decide` or `Lean.ofReduceBool` in headline proofs:

1. **Kernel-reflective proof automation (`arm64-semantics/ProofLib/`):**
   - **Witnessed ROBDD & per-lane bit-slicing (`ProofLib/BV/ReflectROBDD.lean`):** `bv_slice` (structural `SBDD`, 20–700 ms) and `bv_robdd` (interleaved LSB-to-MSB witnessed ROBDD DAG `BinTree BDDNode` + 1024-bucket `BinTree (List GateStep)` hash table + single-pass `checkDagOrdered`, 0.06–5 s at 64-bit) discharge bitvector and ripple-carry arithmetic goals via `Eq.refl true` without invoking an external SAT solver or `Lean.ofReduceBool`.
   - **Reflective linear `BitVec` normalizer (`ProofLib/BV/Linear.lean`):** `bv_lin` normalizes linear `BitVec w` / `Nat` expressions to sorted sparse `Int` polynomials (`Lin.Poly`) in `< 1 ms` via `Eq.refl true` using purely computable definitions (no `noncomputable def`).
   - **$O(N \log N)$ reflective AC separation-logic certificates (`ProofLib/SepLogic.lean`):** `SepTree.eq_of_sortIdx` pairs a balanced Braun atom tree (`SepAtomTree`) with bottom-up merge sort (`sortIdx`).
   - **Reflective whole-block symbolic execution (`ProofLib/SepLogic/SymBlock/`):** `sym_block` uses an untrusted native advisor, cursor-based $O(1)$ fetch (`fetchCur`), single `Eq.refl` block verification, and a diff-only post-state update spine (`changedRegs`), achieving `4.0×` faster elaboration and `2.3×` faster kernel checking than per-instruction `wp_steps` on a 60-instruction benchmark.
   - **Critical Lean 4 kernel-reduction engineering trade-off:** The fastest kernel checkers in `ReflectROBDD.lean` (`getRec?`, `allRec`, `checkROBDD`) and `SepLogic.lean` (`SepAtomTree.get`, `sortIdx`) are declared `noncomputable def` because they invoke raw inductive recursors (`@BinTree.rec`, `@SepAtomTree.rec`, `@List.rec`) directly to bypass `brecOn` (`below` + `PProd`) WHNF overhead. Projects requiring compiled IR (`hasIR = true` / zero `noncomputable def`) can still adopt all non-`.rec` techniques (`cond`, GMP `Nat` bitops, CPS single-destructure combinators `unconsD`/`withCofactors`, `Lin.Poly`, cursor fetch, diff-only spines, and single-pass DAG ordering checks).
2. **Untrusted-`.olean`-free Comparator replay (`comparator/`, `leanprover/comparator@v4.35.0`, and Lean `v4.35.0` `lake comparator`):**
   - `code-verification/comparator/` pins standalone `leanprover/comparator` (`e3dcf308...`) + `lean4export` + `landrun` (Landlock LSM) with `"enable_nanoda": false`, replaying `lean4export` NDJSON through Lean's kernel without mapping untrusted `.olean`s into the judge process. However, `comparator/run.sh` prewarms both `ComparatorChallenge` and `ComparatorSolution` in a shared `.lake/` directory outside `landrun`, so true challenge-vs-solution `.olean` isolation requires running challenge and solution exports in disjoint workspaces.
   - Stock **Lean `v4.35.0`** ships `lake comparator` and `lake check` built into `Lake` (`Lake/CLI/Check.lean`, using `bwrap` instead of `landrun`), supports pre-built `--challenge-from-export <f1> --solution-from-export <f2>` (skipping `lake-manifest.json` and `lake build`), and bundles **all six** kernel/checker binaries directly in `<sysroot>/bin/`: `leanexport`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, and `con-ron`. Both standalone and core `comparator` pin **27** kernel built-in primitives plus **4** `Quot.*` constants (`primitiveTargets` + `builtinTargets`) to defend against primitive-definition substitution.
3. **Fail-closed static & kernel TCB auditing (`arm64-semantics/tools/tcb-map/`, `ProofLib/TrustedClosure.lean`, `scripts/TrustedClosure.lean`, `ProofLib/ProofTerm/`):**
   - `tcb-map` enforces exhaustive 6-bucket repository file classification, two-tier core-vs-surface TCB separation (`CoreInitOnly` vs `SurfaceMacro`), Rust-side `[tcb]` import isolation (`tcb_rust_import`), forbidden elaborator/attribute blocklists, and Lean 4 `module` visibility discipline (`public import` for specs, private `import` for proofs in `Theorems` modules).
   - `ProofLib/TrustedClosure.lean` computes bitset-indexed (`Array UInt64`) transitive statement closures with `optParam` default erasure (`stripOptParams`) and shortest-path BFS blame (`findBlamePath`).
   - `ProofLib/ProofTerm/` (`#kernel_profile`, `#kernel_hotspots`, `#kernel_lint`) times `Kernel.check`/`Kernel.isDefEq` directly on stored proof terms without re-elaboration using a `@[noinline] pick` + `IO.mkRef` anti-hoisting barrier.

## Applicability

These findings apply to:
- `google-deepmind/code-verification` at commit `8c8d371f1962ac73435c8eb148678991f5c3470d` (targeting Lean `v4.35.0`), specifically `arm64-semantics/ProofLib/`, `comparator/`, `arm64-semantics/tools/tcb-map/`, `scripts/TrustedClosure.lean`, and `Computational/docs/TRUSTED_BASE.md`.
- `leanprover/comparator` at commit `e3dcf3083fc53d44b27a4431fabf7d43181583f5` (tag `v4.35.0`), which `code-verification/comparator/install-tools.sh` pins.
- The released `leanprover/lean4:v4.35.0` Linux x86_64 toolchain (`Lake version 5.0.0-src+eb6cafb`), specifically its bundled `<sysroot>/bin/` executables and `<sysroot>/src/lean/lake/Lake/CLI/Check.lean`.

Findings compare how `code-verification`'s standalone `comparator/` setup relates to the newly built-in `lake comparator` shipped in Lean `v4.35.0`, and separate universal Lean 4 kernel-reduction techniques from `noncomputable` raw-recursor definitions that do not emit compiled IR.

## Findings

### 1. `ProofLib/` Structure, `module` Usage, and Axiom Footprint

Basis: source + execution (static scan over all 215 non-`Testing` `.lean` files under `arm64-semantics/ProofLib/`).

- **Universal Lean 4 `module` adoption:** All `215 / 215` non-`Testing` `.lean` files in `ProofLib/` begin with `module`, and `72 / 215` split pure kernel definitions (`@[expose] public section`) from elaborators/tactics (`public meta section`). Two files (`ProofLib/BV/Linear.lean:406` and `ProofLib/BV/ReflectROBDD.lean:2870`) set `set_option compiler.relaxedMetaCheck true` inside `public meta section` so `MetaM` code can invoke non-`meta` kernel checkers (`eqCheck`, `checkSlice`) prior to emitting `Eq.refl true`.
- **Zero compiler-trust / unsafe escapes in non-legacy paths:** Across all 215 files, there are `0` occurrences of `native_decide`, `decide +native`, `@[implemented_by]`, `@[extern]`, or `unsafe`. `partial def` appears in `55` files, strictly inside `public meta section` tactic/advisor code (never inside kernel proof terms).
- **Isolated legacy `bv_decide` presence:** `12` files still reference `bv_decide` (e.g., `ProofLib/SepLogic/Solver.lean:245`, `ProofLib/BV/Arith.lean:212` gated behind `register_option proofLib.bvDecideFallback : Bool := { defValue := false }`). Headline proofs never reach these theorems because `comparator` rejects `Lean.ofReduceBool`.
- **Verified `std3` axiom footprint:** Regression checks in `ProofLib/Testing/BVReflectOptionA.lean:318-364` and `ProofLib/Testing/DecompNorm.lean:732-734` (`#guard_msgs in #print axioms`) verify that theorems discharged by `bv_slice`, `bv_robdd`, `bv_lin`, and `decomp_eq` depend only on `[propext, Classical.choice, Quot.sound]`.

### 2. Kernel-Reflective Decision Procedures & Kernel-Physics Techniques

Basis: source + documentation.

#### 2.1 Witnessed ROBDD & Per-Lane Bit-Slicing (`ProofLib/BV/ReflectROBDD.lean`)
- **Backend-parametric bit-blaster (`lines 107-125, 1159-1620`):** A single `SymBool α` structure (`fFalse`, `fTrue`, `fVar`, `fNot`, `fAnd`, `fOr`, `fXor`) and `LawfulSymBool` contract decouple bit-blasting (`compileBV`, `rippleAddList`, `eqBitsList`, `ultBits`, `uleBits`, `sltBits`, `sleBits`, `symIte`) from the underlying Boolean representation. One soundness proof (`compileBV_sound`) serves both `bv_slice` and `bv_robdd`.
- **Tier 1 (`bv_slice`, `lines 1726-1995`):** Evaluates each bit lane into a structural `SBDD` tree (`leaf Bool | node Nat SBDD SBDD`) with fuel-bounded `sbddApply` (`prove_of_checkSlice` closed by `Eq.refl true`; `20–700 ms`, `BV/README.md:14`). A `preprocessMulPow2` pre-pass rewrites `x * 2^k` and `2^k * x` to `x <<< k` (`BV/README.md:53`).
- **Tier 2 (`bv_robdd`, `lines 1997-2864`):** Orders variables interleaved LSB-to-MSB so ripple-carry addition/subtraction and comparisons maintain $O(1)$ cross-section width. An untrusted `MetaM` builder emits:
  - `dag : BinTree BDDNode` (radix-2 `Nat`-indexed trie storing `(var, lo, hi)` for compound node IDs `u ≥ numVars + 2`), and
  - `claims : BinTree (List GateStep)` (1024-bucket hash table keyed by `hashGate a b := Nat.land (Nat.xor a (Nat.shiftLeft b 4)) 1023`, `line 2202`, where each `GateStep` claims `op(a, b) = u` via Shannon expansion on variable `v`).
  The kernel checks `checkROBDD = true` via `Eq.refl true` in $O(|G| \log |G|)$ steps (`0.06–5 s` at 64-bit, `BV/README.md:15`). Non-tautologies yield concrete bitvector counterexamples by tracing a path to node `0` (`Testing/BVReflectOptionA.lean:281-308`).
- **Kernel-reduction optimizations in `ReflectROBDD.lean`:**
  1. **Direct `.rec` parallel checker (`lines 2477-2840`):** `getRec?`, `allRec`, `listAllRec`, and `findInBucketRec` are written directly with `@BinTree.rec` / `@List.rec` + `Nat.casesOn` (and proved equal to their equation-compiled counterparts via `getRec?_eq`, `allRec_eq`, `listAllRec_eq`), eliminating `brecOn` (`below` + `PProd`) WHNF overhead. Because direct `.rec` calls in `Type` have no compiled IR, these functions are marked `noncomputable def`.
  2. **Single-pass DAG ordering pre-check (`checkDagOrdered`, `lines 2566-2648`):** Verifies variable monotonicity across `dag` once, allowing `expandAtOrdered` to check expandability and extract both `(lo, hi)` cofactors in one `BinTree` lookup.
  3. **Continuation-passing single-destructure combinators (`unconsD` `line 216`, `withCofactors` `line 2046`, `expandAtOrdered` `line 2594`):** Match a constructor once and pass already-reduced fields to continuation `k` so kernel WHNF never re-evaluates `headD`/`tailD` or `cofactor0`/`cofactor1`.
  4. **Zero-`Decidable` branching (`lines 62-68, 2650-2710`):** Uses `cond` + `Nat.{beq,blt,land,shiftRight,xor}` + custom `GateOp.beq` instead of `@ite`/`Decidable`.
  5. **Linear $O(w)$ list-zip combinators (`mapBits`, `zipBits`, `rippleAddList`, `eqBitsList`, `lines 240-585`):** Walk bit lists once via `unconsD` instead of $O(w^2)$ indexed `getD` lookups.

#### 2.2 Sparse Linear `BitVec` Normalizer (`ProofLib/BV/Linear.lean`) & Bound-Driven `bv_arith` (`ProofLib/BV/Arith*.lean`)
- **`bv_lin` (`BV/Linear.lean:38-401`):** Reifies linear `BitVec w` and `Nat` expressions into `Lin.Expr` / `Lin.NExpr` and normalizes them into sorted sparse `Int` polynomials `Poly := { c : Int, ts : List (Nat × Int) }` with even keys `2*i` for `BitVec` atoms and odd keys `2*i+1` for `BitVec.ofNat w` atoms. Uses `intIsZero` (`line 73`) and `cond` + `Nat.{blt,beq}` in `insertT` (`line 88`), supports both literal widths mod `2^w` (`eq_of_eqCheck_pow`, `ne_of_neCheck`) and symbolic widths (`eq_of_eqCheck_zero`), runs in `< 1 ms`, and is **100% computable (zero `noncomputable def`)**. Exposes `Lin.diffConst?` (`line 584`) to prove constant byte offsets between arbitrary linear address expressions.
- **`bv_arith` interval cache (`BV/ArithTranslate.lean:150-200`):** Indexes `Nat` relational hypotheses by LHS, RHS, and summands (`byLhs`, `byRhs`, `sumIdx`) and runs a bounded 2-step `ub`/`lb` interval analysis to emit wrap-free `toNat` node equations while withholding `% 2^w` wrapping facts (`deferred`) from the initial `omega` call.
- **Zero-`Expr`-pointer negative cache (`BV/Arith.lean:280-300`):** `CacheKey` stores only scalar fields (`propHash : UInt64`, `propDepth : UInt32`, `hypsHash`, `numHyps`, `bvDecide`, `m_objs = 0`) so inserting entries into `negCache : IO.Ref` never triggers `lean_mark_mt` traversal over live goal `Expr` graphs.

#### 2.3 $O(N \log N)$ Reflective AC Separation Logic & Frame Inference (`ProofLib/SepLogic.lean`, `Solver.lean`, `FrameInfer.lean`)
- **`SepTree.eq_of_sortIdx` (`ProofLib/SepLogic.lean:3002-3176`):**
  - Stores atoms in a balanced Braun binary tree `SepAtomTree` (index `0` at root, odd `n` left at `n / 2`, even `n > 0` right at `n / 2 - 1` → $O(\log N)$ lookup via `SepAtomTree.get`).
  - Sorts leaf index lists with bottom-up merge sort (`runs` → `mergePairs` → `mergeRounds 64` → `idxFlatten`), checking equality via `idxBEq` by `rfl`. Because `mergeRounds_perm` proves permutation preservation for any round count `n`, soundness does not depend on proving sortedness!
  - Like `ReflectROBDD`, `SepAtomTree.get`, `mergeIns`, `merge`, `mergePairs`, `mergeRounds`, `runs`, `idxBEq`, and `denoteF` are declared `noncomputable def` using raw `@SepAtomTree.rec` / `@SepTree.rec` / `@List.rec` / `@Nat.rec` / `@Option.rec` to avoid `brecOn`.
- **`FrameInfer` (`ProofLib/SepLogic/FrameInfer.lean:105-424`):** Parameterizes one frame-inference engine over three judgments (`Judg := sat m | ent P0 | eq P0`), combining canonical `(base, offset mod 2^64)` keys (`canonAddr`, `baseOff`), greedy exact cancellation, bounded DFS with metavariable backtracking (`proofLib.sepFrameMaxSteps := 4096`), automatic `memRegion_carve` splitting, and `@[sep_unfold]` / `@[expose] def` bundle unfolding.

#### 2.4 Whole-Block Reflective Execution (`SymBlock`), State Canonicalization, Bounded `omega`, & Kernel Profiling (`ProofTerm`)
- **`SymBlock` (`ProofLib/SepLogic/SymBlock/{Block,Spine,README}.lean`):** Runs an untrusted native advisor to generate cell-index and branch hints, then verifies an entire basic block with one `Eq.refl` evaluation of `run base tbl hints ss₀ = some (ssF, obl)`. Uses cursor-based $O(1)$ fetch (`fetchCur`, `Block.lean:59-62`) and diff-only post-state spine emission (`changedRegs` / `applyWrites`, `Spine.lean:32-58`). On the 60-instruction benchmark (`SymBlock/README.md:125-132`), `sym_block` reduces elaboration from `655 ms` (`wp_steps`) / `415 ms` (`wp_sym_steps`) to `162 ms`, proof DAG objects from `23,076` to `6,555`, and kernel re-check from `1.69 s` to `0.73 s`.
- **`SymWP` (`ProofLib/SepLogic/SymWP.lean:155-200`):** Caches preprocessed `execInst instExpr (.bvar 0)` and `evalAddrMode (.bvar 0) amExpr` templates across declarations in `IO.Ref`, and avoids unfolding `Arm64.State.mk` projections to prevent $O(2^N)$ `State` eta-expansion.
- **`StateNorm` (`ProofLib/SepLogic/WP/StateNorm.lean:246-300`):** Prunes shadowed register writes along `State.writeReg64` spines via `writeReg64_comm_or_same` + `writeReg64_prune_step`.
- **`OmegaBounded` (`ProofLib/SepLogic/OmegaBounded.lean:37-200`):** Because `omega`'s core loop does not poll `checkSystem`, wraps speculative calls in relevance tiers (`OmegaTier := goalOnly | strict | transitive | heavy`), a `natSubCount` exponential-split guard, and `runTacClosed` (`withoutRecover` + `.hasSorry` check so `Tactic.run` never silently admits goals).
- **`ProofTerm/{KernelProfile,Lint}` (`ProofLib/ProofTerm/{README.md,KernelProfile.lean,Lint.lean}`):** `#kernel_profile` and `#kernel_hotspots` time `Kernel.check` and `Kernel.isDefEq` directly on stored proof terms without re-elaboration, using `@[noinline] pick t e` plus an `IO.mkRef` store (`KernelProfile.lean:60-90`) so the compiler cannot hoist pure kernel calls outside `IO.monoNanosNow`. `#kernel_lint` flags `decide-on-heavy` and `cast-unfolds-heavy` sites mentioning definitions with `≥ 2000` DAG nodes within 2 unfoldings.

### 3. Comparator Replay Architecture (`code-verification/comparator/` vs. Lean `v4.35.0` `lake comparator`)

Basis: source + execution (inspection of `code-verification/comparator/*`, `leanprover/comparator@e3dcf308`, and live inspection of Lean `v4.35.0` `<sysroot>/bin/*` and `Lake/CLI/Check.lean`).

| Mechanism | `code-verification/comparator/` (uses standalone `leanprover/comparator@v4.35.0`) | Lean `v4.35.0` built-in `lake comparator` (`Lake/CLI/Check.lean`) |
|---|---|---|
| **Sandbox** | `Zouuup/landrun` (`ec104f6e`, Linux Landlock: `--ro / --rw /dev --rox <leanPrefix>`) | `bubblewrap` (`bwrap`: `--ro-bind / / --tmpfs /home /root /run/user /tmp /run /var --clearenv --unshare-all`, empty network namespace during build/export/kernels) |
| **Untrusted `.olean` isolation** | Judge never loads `.olean`s; runs `lean4export` (`5a9a355d`) inside `landrun` and parses NDJSON (`Export.parseStream`). **Caveat:** `comparator/run.sh:46-47` prewarms both `ComparatorChallenge` and `ComparatorSolution` in the same `.lake/` outside `landrun`, and standalone `comparator/Main.lean:308-314` shares `projectDir / ".lake"` across challenge and solution builds. | Judge never loads `.olean`s; uses bundled `<sysroot>/bin/leanexport`. Supports `--challenge-from-export <f1> --solution-from-export <f2>` (`Check.lean:690-744`), setting `needsProject := false` (no `lake-manifest.json` and no `lake build` required), enabling fully disjoint challenge/solution export actions! |
| **Kernels executed** | `computational.json:17` & `symbolic.json:23` set `"enable_nanoda": false`; runs only in-process `Lean.Kernel.Environment.replay` (`Main.lean:212-240`) with `ulimit -s 1048576` (`run.sh:50`, multi-hour single-threaded replay on Mathlib+VCVio+ELF closure). | Runs `<sysroot>/bin/leanchecker --silent --from-export` in a separate `bwrap` child (`Check.lean:459-461`). `--paranoid` runs all 5 bundled external checkers in `<sysroot>/bin/`: `leanchecker-paranoid`, `lean4lean` (`--import`), `nanoda_bin`, `con-leche`, and `con-ron` (`Check.lean:572-580`). |
| **`nanoda` axiom-error flag** | Sets `"unpermitted_axiom_hard_error": true` (`Main.lean:163`). | Sets `"unpermitted_axiom_hard_error": false` (`Check.lean:417`), relying on Lake's own `checkAxioms` (`Check.lean:527`). |
| **Primitive & Quotient pinning** | Pins **27** `primitiveTargets` (`Nat.add..shiftRight`, `String.ofList`, `Char.ofNat`, `List`, `eagerReduce`, `Nat`, `String`, `String.mk`, `Char`, `optParam`, `autoParam`, `semiOutParam`, `outParam`) + **4** `builtinTargets` (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` when `Quot.sound` is permitted) (`Main.lean:241-280`), plus a post-replay `Quot.*` equality check (`Main.lean:228-239`). | Identical **27** `primitiveTargets` + **4** `builtinTargets` (`Check.lean:474-513`). |

### 4. TCB Classification & Statement-Closure Auditing (`tcb-map/` & `TrustedClosure`)

Basis: source.

- **`arm64-semantics/tools/tcb-map/`** is a zero-internal-workspace-dep Rust auditor enforcing six invariants:
  1. **Exhaustive fail-closed 6-bucket path classification** (`policy.rs:191-440`): `tcb`, `case-studies-tcb`, `proof`, `testing`, `infra`, `doc`; unrecognized files fail with `[unclassified-path]`.
  2. **Two-tier Lean TCB split** (`policy.rs:98-132`): `CoreInitOnly` (semantic core, strictly `Init`-only transitively, zero `Lean`/`Std` imports) vs `SurfaceMacro` (surface DSL elaborators/barrels).
  3. **Lean 4 `module` visibility & role purity** (`lib.rs:145-288, 597-624`, `policy.rs:629-785`): `Role::Spec` contains definitions only (no `theorem`/`lemma`, no `#` commands, no custom elaborators/parsers/delaborators/unexpanders/`@[init]`/`@[csimp]` listed in `SPEC_FORBIDDEN_ATTRIBUTES`); `Role::Theorems` contains only `public theorem` declarations, must use `public import` for `Spec`/`Theorems` and private `import` (never `public import` or `meta import`) for `Proof`, and forbids `open`/`export`/`private`/`local`/`scoped` and `_`-prefixed names.
  4. **Self-contained `[tcb]` Rust crates** (`tcb_rust_import.rs:48-156`): forbids `[tcb]`/`[case-studies-tcb]` Rust files from referencing non-`tcb` workspace crates or `untrusted_*::` / `test_infra::` / `tests::` / `*_tests::` modules.
  5. **Whole-process closure exclusion** (`policy.rs:138-160`, `lib.rs:1166-1232`): ensures whole-process ELF theorem specs do not transitively import library-level Hoare/separation-logic spec modules.
  6. **Comment/string-aware Rust lexer** (`lex.rs:65-160`): strips `--`, nested `/- ... -/`, `"..."`, `r#"..."#`, and `'c'` while preserving exact byte offsets and line numbers.
- **`ProofLib/TrustedClosure.lean` (`lines 92-299, 519-665`):** Pre-indexes trusted constants into `Array UInt64` bitsets for fast transitive closure unions, strips elaboration-only `optParam α d` defaults via `stripOptParams` so default arguments do not falsely pull unused tables into theorem closures, and runs BFS `findBlamePath` on violations to print minimal `thm -> ... -> offendingConst` chains.
- **`scripts/TrustedClosure.lean` (`lines 187-565`):** Computes 5-tier per-constant statement closures (`T`, `repo`, `arm64-semantics`, `generated`, `foundations`), unioned source line counts (with/without comments), and enforces Rule 5 (zero proof-tree definitions unfolded in headline statement closures).

## Boundaries

- **Execution of `code-verification` proofs — not examined:** We did not run `lake build` or `comparator/run.sh` on `google-deepmind/code-verification` (its README reports several hours and 15–34 GiB peak RAM); benchmark numbers (`bv_slice`, `bv_robdd`, `bv_lin`, `sym_block`, `#kernel_hotspots`) are reported from upstream source/documentation (`BV/README.md`, `SymBlock/README.md`, `ProofTerm/README.md`), while file counts, grep audits, Lean `v4.35.0` bundled binaries, and `lake comparator` CLI flags were directly executed/measured.
- **Computable 1-arg recursion vs. raw `.rec` `brecOn` avoidance — not benchmarked on Lean `v4.35.0`:** While `ReflectROBDD.lean` and `SepLogic.lean` use `noncomputable def` with raw `.rec` to avoid `brecOn`, we did not empirically benchmark whether rewriting their functions into single-argument structural recursion compiles to direct `.rec` with compiled IR (`hasIR = true`) on Lean `v4.35.0`.
- **Non-Linux `lake comparator` — unsupported:** Both standalone `leanprover/comparator` (`landrun`) and Lean `v4.35.0` `lake comparator` (`bwrap`) explicitly require Linux (`Lake/CLI/Check.lean:607-609`) unless `--inadvisably-no-sandbox` is passed.
- **Additional `nanoda_lib` primitives beyond `primitiveTargets` — not exhaustively cross-checked here:** `Lake/CLI/Check.lean:474-513` pins 27 kernel built-ins plus 4 `Quot.*` constants derived from Lean's C++ kernel (`new_persistent_expr_const`); external checkers with `nat_extension`/`string_extension` may rely on additional `Init` constructors/types (such as `Bool` or `String` internals) depending on checker version, which should be verified directly against the target external checker's source.

## Evidence

- `google-deepmind/code-verification` @ `8c8d371f1962ac73435c8eb148678991f5c3470d`:
  - `lean-toolchain` (`leanprover/lean4:v4.35.0`), `README.md:99-145`
  - `comparator/{README.md,install-tools.sh,run.sh,computational.json,symbolic.json}`, `comparator/ComparatorChallenge/Computational/Main.lean:10-50`, `comparator/ComparatorSolution/Computational.lean:10-21`
  - `arm64-semantics/ProofLib/BV/{README.md,ReflectROBDD.lean,Linear.lean,Arith.lean,ArithTranslate.lean,PolyMul.lean}`
  - `arm64-semantics/ProofLib/Testing/BVReflectOptionA.lean:1-160,250-385`
  - `arm64-semantics/ProofLib/SepLogic.lean:2943-3176` (`SepTree`, `SepAtomTree`, `sortIdx`, `eq_of_sortIdx`)
  - `arm64-semantics/ProofLib/SepLogic/{README.md,Solver.lean,FrameInfer.lean,SymWP.lean,OmegaBounded.lean}`
  - `arm64-semantics/ProofLib/SepLogic/SymBlock/{README.md,Block.lean,Spine.lean}`
  - `arm64-semantics/ProofLib/SepLogic/WP/{StateNorm.lean,FrameAuto.lean}`, `arm64-semantics/ProofLib/VCGen.lean:1-250`
  - `arm64-semantics/ProofLib/ProofTerm/{README.md,KernelProfile.lean,Lint.lean}`
  - `arm64-semantics/ProofLib/TrustedClosure.lean:1-800`, `scripts/TrustedClosure.lean:1-800`, `Computational/docs/TRUSTED_BASE.md:1-340`
  - `arm64-semantics/tools/tcb-map/{README.md,src/policy.rs,src/lib.rs,src/tcb_rust_import.rs,src/lex.rs,src/discovery.rs}`
- `leanprover/comparator` @ `e3dcf3083fc53d44b27a4431fabf7d43181583f5`:
  - `Main.lean:80-374`, `Comparator/Compare.lean:1-110`, `Comparator/Axioms.lean:1-72`
- `leanprover/lean4:v4.35.0` (`Lake version 5.0.0-src+eb6cafb`, observed `2026-11-22`):
  - Live `ls -la <sysroot>/bin/`: `leanexport` (`700,728` B), `leanchecker` (`59,656` B), `leanchecker-paranoid` (`8,858,080` B), `lean4lean` (`36,897,680` B), `nanoda_bin` (`1,339,280` B), `con-leche` (`17,613,744` B), `con-ron` (`2,945,520` B).
  - Live `lake comparator --help` and `lake check --help` outputs.
  - `<sysroot>/src/lean/lake/Lake/CLI/Check.lean:1-750`.

## Revalidation

1. **Check Lean toolchain bundled checkers & `lake comparator` flags** on any newer Lean release:
   ```bash
   ls -la "$(lean --print-prefix)/bin/"
   lake comparator --help
   lake check --help
   ```
   Inspect `$(lean --print-prefix)/src/lean/lake/Lake/CLI/Check.lean` around `primitiveTargets`, `bundledKernels`, and `unpermitted_axiom_hard_error`.
2. **Re-audit `ProofLib/` construct footprint** on a newer `google-deepmind/code-verification` commit:
   Shallow-clone `https://github.com/google-deepmind/code-verification` into `/tmp`, count `^module$`, `native_decide`, `bv_decide`, `ofReduceBool`, `implemented_by`, `extern`, `unsafe`, and `noncomputable def` across `arm64-semantics/ProofLib/` (excluding `Testing/`), and diff `comparator/` to check whether it has migrated from standalone `leanprover/comparator` to `lake comparator`.
3. **Check whether single-argument structural recursion avoids `brecOn` with compiled IR:**
   Run `#print` on a 10-line Lean `v4.35.0` `BinTree.get?` definition using `match t with | .empty => fun _ => none | .node v l r => fun idx => Nat.casesOn idx v ...` and inspect whether the compiled term uses `BinTree.rec` directly without `BinTree.brecOn`.
