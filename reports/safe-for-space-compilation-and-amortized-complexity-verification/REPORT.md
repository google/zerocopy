# Safe-for-Space Compilation and Amortized Complexity Verification

## Summary

Classical verified compiler correctness—exemplified by `CompCert`'s `transf_c_program_is_refinement` (`driver/Complements.v:45–53`)—proves **extensional trace refinement**: every observable I/O trace of the compiled assembly is permitted by the source program. Because extensional traces omit stack high-water marks, live heap graphs, allocation rates, and execution step counts, a formally verified compiler is legally allowed to introduce asymptotic memory leaks, convert $O(1)$-space tail loops into $O(N)$ stack overflows, hoist pointers across loop iterations, bloat `async` state machines, or introduce timing side channels and algorithmic-complexity denial-of-service (`HashDoS`/`ReDoS`) regressions.

Closing this intensional loophole requires two coupled disciplines: **(1) Safe-for-Space compilation**, ensuring compiler lowerings and optimizations preserve asymptotic (and concrete bounded) stack and heap usage, and **(2) Formal amortized resource verification**, proving time, stack, heap, and lazy-thunk complexity bounds Compositionally. Seven load-bearing findings govern this space:

1. **Formal Space Complexity Classes & Calling-Convention Walls (`Clinger PLDI 1998`, `musttail`):** Proper tail recursion is a semantic equivalence of asymptotic space classes, not an optional peephole trick. Direct execution on `GCC 15.2.0` (`x86_64` SysV ABI) confirms that `[[gnu::musttail]]` is rejected when scope-exit cleanup runs (`error: cannot tail-call: other reasons`), warns on escaping stack locals (`-Wmusttail-local-addr`), and fails whenever the callee requires more stack argument slots than the caller (`error: cannot tail-call: callee required more stack slots than the caller`).
2. **Safe-for-Space Closure Conversion (`Shao & Appel 2000`, `CertiCoq` `Paraskevopoulou & Appel ICFP 2019`):** Capturing a shared lexical frame instead of minimal free variables pins dead sibling graphs under tracing GC (a 502× live-heap blowup on 1,000-word payloads in Probe 2B). `CertiCoq` mechanizes flat minimal-capture closure conversion (`Closure_conversion`, `project_var`, `Closure_conversion_fundefs_correct`) with GC-compatible reachable-heap bounds (`bounds.v`), proving time-and-space preservation even for diverging programs.
3. **Space-Violating Middle-End Optimizations & Stackless Coroutine Frame Bloat (`LLVM`, `GHC`, `rustc`):** Time-focused passes—`LLVM` `CSE`/`GVN`/`LICM`, `GHC` `FloatOut` (full laziness, formalized by Gustavsson & Sands), and un-zeroed register-spill GC roots—systematically extend live ranges across allocations and safepoints. Direct execution on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`--edition 2024 -O`) demonstrates a sharp MIR storage-liveness surprise: even a plain `Copy` `[u8; 4096]` array *never used after `.await`* bloats the generated `Future` to **`4099 bytes`** because `StorageDead` sits at block exit, whereas wrapping it in an explicit inner scope collapses the exact same `Future` by **1,366×** to **`3 bytes`**. Conversely, `rustc`'s `compute_layout` (`storage_conflicts`) and `LLVM CoroFrame` (`StackLifetime`) successfully overlap storage-disjoint sequential `.await` scopes (`4099 bytes` for two sequential 4,096-byte guards vs. `8194 bytes` when simultaneously live).
4. **Automatic Amortized Resource Analysis (`AARA` / `RAML`):** Attaching affine binomial-basis potential coefficients $\vec{q}$ to inductive data structures reduces worst-case multivariate polynomial (and Stirling-basis exponential) amortized bound inference to a single polynomial-time Linear Program (`LP`). Its affine sharing rule ($\Phi(x) = \Phi_1(x) + \Phi_2(x)$) aligns structurally with Rust's ownership/borrowing discipline, yet breaks on non-polynomial bounds ($O(\log n)$, $O(\alpha(n))$) and cyclic mutable aliasing.
5. **Cost-Aware Logical Frameworks (`calf` POPL 2022, `decalf` POPL 2024):** Using a synthetic phase distinction (`ext` / open modality `◯` / closed modality `●`), `calf` proves **cost noninterference by construction** (`oblivious` in `Calf/Phase/Noninterference.agda:52–59`: extensional behavior cannot depend on `step c`), while `decalf` equips types with a directed preorder (`≤⁻-ext-≡` in `Calf/Phase/Directed.agda:15–18`) to verify effectful and probabilistic expected cost bounds. Neither currently connects abstract `step` monoids to verified native machine-code backends.
6. **Separation Logic with Time Credits, Receipts, GC Space Credits, and Thunk Debits (`Iris` / `CFML`):** Time credits (`$ n`) embed amortized potentials directly into mutable pointer invariants (Union-Find $O(\alpha(n))$); time receipts (`⌛ n`) prove lower bounds and counter-overflow freedom; `SL⋄` and Moine et al. (POPL 2023) lift tracing-GC reclamation into high-level separation logic via `pointed-by` and `stackable` assertions; and Pottier et al. (POPL 2024) mechanize Okasaki's persistent lazy **thunks and debits** using monotonic ghost state so paying a shared thunk's debt benefits all persistent clones.
7. **End-to-End Stack/Heap Compilation & Intensional Security (`Stack-Aware CompCert`, `CakeML`, `SipHash`, `CT-CompCert`):** `CakeML`'s `dataSemScript.sml` tracks explicit `heap_limit`, `stack_limit`, `safe_for_space`, and `size_of` word counts through codegen; `Stack-Aware CompCert` (POPL 2019) replaces unbounded stack blocks with a finite abstract stack. At the security boundary, unseeded hash maps (`HashDoS`), backtracking regexes (`ReDoS`), and branch-introducing optimizations (`Barthe et al. POPL 2020`) are all manifestations of cost- and leakage-oblivious refinement.

## Applicability

This report covers the interaction between compiler lowering/optimization passes and formal resource-bound verification across the following pinned subjects:

- **Verified compilers and extensional vs. quantitative theorems:** `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`), `CertiCoq/certicoq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`, ICFP 2019 DOI `10.1145/3341687`), `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, OOPSLA 2020 DOI `10.1145/3428272`), plus `CompCert` stack-space and constant-time extensions (PLDI 2014 DOI `10.1145/2594291.2594301`, POPL 2019 DOI `10.1145/3290375`, POPL 2020 DOI `10.1145/3371075`).
- **Production optimizing compilers and coroutine/hash lowerings:** `llvm/llvm-project` (`507de0cc365e4c6317d21fb08e298f742256a51f`, `CoroFrame.cpp`), `rust-lang/rust` (`b0b600668bb9b4a897e2299b0a44289d42276545`, `rustc_mir_transform::coroutine` and `std::collections::HashMap`), plus executed probes on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `gcc (Debian 15.2.0-14) 15.2.0` targeting `x86_64-linux` SysV ABI.
- **Amortized cost logics and static resource analyzers:** `AARA`/`RAML` (POPL 2003, TOPLAS 2012, POPL 2017, FoSSaCS 2020), `calfproject/agda-calf` (`10f1ba616e1ade017e4048324ae894281379ce08`, POPL 2022 & POPL 2024), `CFML`/`Iris` separation logic with time credits, receipts, GC space credits, and thunk debits (JAR 2019, ESOP 2019, POPL 2022, POPL 2023, POPL 2024), and `Liquid Haskell` `Tick` refinements (POPL 2020).

The Rust coroutine size measurements apply specifically to `rustc 1.98.0-nightly` (`--edition 2024 -O`, `x86_64-unknown-linux-gnu`); exact byte counts depend on MIR `StorageLive`/`StorageDead` emission and niche/alignment layout, though the underlying `StorageDead`-at-scope-exit mechanism is architectural across `rustc`'s coroutine lowering. The `[[gnu::musttail]]` diagnostics apply specifically to `GCC 15.2.0` under x86-64 SysV AMD64 caller-cleanup calling conventions.

## Findings

### 1. The Extensional Refinement Loophole and Clinger's Proper Tail-Recursion Space Classes

Basis: source + normative + execution (`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`; Clinger PLDI 1998 DOI `10.1145/277650.277719`; `GCC 15.2.0` Probe 2A-ii)

#### Extensional Refinement in `CompCert`
In `AbsInt/CompCert` (`driver/Complements.v:45–53`), top-level compiler correctness is stated purely over `program_behaves` (`Terminates t r`, `Diverges t`, `Reacts T`, `Goes_wrong t`):

```coq
Theorem transf_c_program_is_refinement:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics p) beh -> not_wrong beh) ->
  (forall beh, program_behaves (Asm.semantics tp) beh -> program_behaves (Csem.semantics p) beh).
```

Because `program_behavior` contains only external I/O event traces (`Events.trace`) and exit codes—and baseline `CompCert` models stack frames as unbounded fresh memory blocks—any compilation pass that multiplies stack usage from $O(1)$ to $O(N)$, retains unreachable heap objects until physical OOM, or degrades $O(N)$ time to $O(N^2)$ still satisfies `transf_c_program_is_refinement`.

#### Clinger's Formal Space Complexity Classes (PLDI 1998)
William D. Clinger (PLDI 1998, DOI `10.1145/277650.277719`) formalized **proper tail recursion** as an asymptotic space-complexity class invariant across operational abstract machines (comparing CESK, stack, and heap-allocated continuation machines):
- An implementation is **properly tail-recursive** iff every tail-recursive program executes in the same asymptotic space class $O(f(n))$ as a canonical space-efficient reference machine that reclaims dead continuation frames before control transfer—ensuring mutually tail-recursive state machines, interpreters, and CPS pipelines execute in $O(1)$ stack space rather than $O(N)$.
- **Historical vs. mathematical constraint:** Retaining unbounded exact backtraces provably requires $\Omega(N)$ space; a runtime cannot simultaneously keep full call histories *and* guarantee Clinger-proper $O(1)$ tail recursion (though bounded ring-buffer traces preserve $O(1)$ space with bounded recent history).

#### Calling-Convention Barriers to Guaranteed Tail Calls (`musttail`)
Explicit tail-call annotations (`LLVM musttail`, `[[clang::musttail]]`, `[[gnu::musttail]]`, WebAssembly `return_call`, Rust's proposed `become`) turn heuristic TCO into a hard compilation contract—exposing four ABI walls under C caller-cleanup calling conventions (SysV AMD64, Win64, AAPCS64):

1. **Stack argument-area ownership:** Under SysV AMD64, the first 6 integer arguments pass in registers (`rdi, rsi, rdx, rcx, r8, r9`), and arguments 7+ pass on the caller's outgoing stack area. Because the caller owns cleanup of those slots, a function receiving $\le 6$ arguments cannot safely overwrite its own caller's stack frame to tail-call a callee taking $\ge 7$ arguments without a callee-pops convention (`tailcc` / `swiftcc`) or dynamic frame rewriting.
2. **Scope-exit destructors / `Drop` / cleanup handlers:** Any destructor or `cleanup` attribute running after the return expression breaks tail position.
3. **Address-taken stack locals (`alloca` escape):** Passing `&local` to a tail callee causes use-after-free once the caller's stack frame is recycled before the jump.
4. **Cross-ABI FFI & shadow stacks:** Hardware return-address protection (`Intel CET` shadow stacks, `ARM PAC`) and heterogeneous FFI boundaries (`tailcc` ↔ `ccc`, GC stack-map frames ↔ native C) prohibit direct frame reuse unless caller and callee share stack-frame ownership and unwinding contracts.

**Executable Probe 2A-ii (`gcc (Debian 15.2.0-14) 15.2.0 -O2 -c`, `x86_64-linux`):**
- Passing `&local` to `[[gnu::musttail]] return callee_ptr(&local);` triggers:
  `warning: address of automatic variable 'local' passed to 'musttail' call argument [-Wmusttail-local-addr]`
- Holding an `__attribute__((cleanup(cleanup_fn)))` local across `[[gnu::musttail]] return callee(n - 1);` hard-fails:
  `error: cannot tail-call: other reasons`
- Tail-calling an 8-parameter `int` callee from a 1-parameter caller (`[[gnu::musttail]] return callee_many(n,n,n,n,n,n,n,n);`) hard-fails:
  `error: cannot tail-call: callee required more stack slots than the caller`

---

### 2. Safe-for-Space Closure Conversion (`Shao & Appel`; `CertiCoq` ICFP 2019)

Basis: source + normative + execution (`CertiCoq/certicoq` @ `ab66e0164e7ecb63e5af95c90c8e479068bf95c2`, ICFP 2019 DOI `10.1145/3341687`; Shao & Appel TOPLAS 2000 DOI `10.1145/345099.345125`; `CPython 3.13.15` Probe 2B)

Under tracing garbage collection, heap liveness is determined strictly by **graph reachability from active roots**, not by undecidable future semantic use. Shao & Appel (TOPLAS 2000, DOI `10.1145/345099.345125`) proved that naive linked or shared-context closure representations violate safe-for-space: if a retained closure $f$ shares a lexical environment record with a sibling closure $g$ (or captures a parent frame pointer) referencing a large temporary buffer $B$ that $f$ never accesses, $B$ remains GC-reachable for the entire lifetime of $f$. This leak recurs across production runtimes (V8/SpiderMonkey shared `Context` objects, Java inner classes capturing implicit `this$`, and pre-RFC-2229 Rust closures capturing whole structs instead of disjoint fields).

#### Mechanized Safe-for-Space Closure Conversion in `CertiCoq`
Paraskevopoulou & Appel (ICFP 2019, DOI `10.1145/3341687`) delivered the first mechanized Coq proof inside `CertiCoq` (`CertiCoq/certicoq` @ `ab66e0164e7ecb63e5af95c90c8e479068bf95c2`) that flat closure conversion is simultaneously semantics-preserving and **safe for both time and space** (including for diverging programs):

- **Minimal free-variable projection (`theories/LambdaANF/closure_conversion.v:33–174`):** `Closure_conversion` constructs flat closure environments strictly from the exact free-variable list `FVs'` of each function bundle (`project_vars ... FVs' FVs''`), rewriting free-variable references via `project_var` projections from the closure's flat environment pointer `Γ` so no dead outer-scope pointer ever enters a closure record.
- **Step-indexed GC-compatible binary logical relation (`theories/LambdaANF/bounds.v:91–412`, `closure_conversion_correct.v:164–298`):** Rather than extensional big-step equivalence, `Closure_conversion_fundefs_correct` proves `cc_approx_exp cenv clo_tag m (boundL 0) boundG (e, rho) (C |[ e' ]|, rho')`, parameterized by quantitative local/global cost postconditions (`simple_bound`, `inline_bound`, `hoisting_bound`, `ll_bound`) that bound both execution step counts and **reachable heap graph sizes** before and after closure conversion.

#### Executable Probe 2B: Tracing-GC Live Heap Blowup (Flat vs. Shared Environment)
Simulating $N$ loop iterations allocating a 1,000-word temporary payload alongside a retained 2-word callback closure referencing only a scalar ID (`CPython 3.13.15`):

| Iterations $N$ | Flat Minimal-FV Closure (`words`) | Shared-Env Closure (`words`) | Blowup Factor |
|---:|---:|---:|---:|
| `10` | `20` | `10,040` | `502.0×` |
| `100` | `200` | `100,400` | `502.0×` |
| `1,000` | `2,000` | `1,004,000` | `502.0×` |

Across FFI boundaries (registering a managed/Rust callback as an opaque `void* user_data` or JNI global reference), un-trimmed environment pointers stay pinned for the entire foreign registration lifetime, invisible to the host compiler's escape analysis.

---

### 3. Space-Violating Optimizations and Stackless Coroutine State-Machine Lowering

Basis: source + normative + execution (`llvm/llvm-project` @ `507de0cc365e4c6317d21fb08e298f742256a51f`; `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`; Gustavsson & Sands HOOTS 1999 DOI `10.1016/S1571-0661(05)80284-1`; `rustc 1.98.0-nightly` Probe 2A)

#### Pass-by-Pass Safe-for-Space Audit Matrix

| Compiler Pass / Lowering | Time Effect | Safe-for-Space Verdict | Exact Space-Violation Mechanism | Mitigation / Required Proof Obligation |
|---|---|---|---|---|
| **Flat minimal-FV closure conversion** (`CertiCoq`) | Extra field copying at creation | **Safe** (linear factor) | Eliminates dead sibling pointers | Verified reachable-graph bound (`cc_approx_exp`) |
| **Linked / shared closure conversion** (naive / V8 `Context`) | Fewer allocations | **Unsafe** ($O(1) \to O(N)$) | Dead sibling references pinned in shared frame | Shao–Appel co-lifetime proof or flat projection |
| **`LLVM` `CSE` / `GVN` / `LICM`** | Eliminates redundant recomputation | **Unsafe** (pointers / aggregates) | Hoisting a pointer or buffer out of a loop extends its live range across all iterations & GC safepoints | Restrict hoisting to bounded scalars or emit live-range non-extension certificates |
| **`GHC` Full Laziness (`FloatOut`)** | Shares invariant subexpressions across calls | **Unsafe** ($O(1) \to O(N)$) | Floating `[1..n]` past a $\lambda$ turns a stream into a retained evaluated spine (Gustavsson–Sands) | Call-by-need space-improvement gate (`-fno-full-laziness` on streams) |
| **Inlining** | Eliminates call overhead | **Conditionally Unsafe** | Can merge disjoint stack frames into one outer frame or prolong callee-temporary lifetimes across outer recursion | Abstract-stack frame bound (`Stack-Aware CompCert`) + scoped `lifetime.end` |
| **Register Allocation / Spilling** | Minimizes reloads | **Conditionally Unsafe** | Dead spilled pointer slots left live in GC stack maps until function return | Precise liveness-trimmed safepoint stack maps + spill-slot zeroing |
| **Stackless Coroutine Lowering (`rustc`, `LLVM CoroFrame`)** | Zero per-task call stack | **Conditionally Unsafe** | Locals whose `StorageDead` / `Drop` sits after `.await` remain captured in the state struct across suspension; `CoroElide` failure forces heap allocation in C++20 | MIR `storage_conflicts` (`compute_layout`) + `LLVM StackLifetime` non-overlapping slot reuse + inner-scope drop discipline |
| **`musttail` / `return_call` Lowering** | Eliminates frame push/pop | **Safe** (enables $O(1)$) | Fails on ABI stack-slot mismatch, escaping `alloca`, or post-call `Drop` | Callee-pops ABI (`tailcc`) + static pre-tail cleanup check |

#### Coroutine Frame Lowering Internals (`rustc` and `LLVM CoroFrame`)
- **`rustc` MIR coroutine transform (`compiler/rustc_mir_transform/src/coroutine/mod.rs:64,459–518,1028–1149,1273–1331`):** `locals_live_across_suspend_points` collects every MIR local whose `StorageLive..StorageDead` interval spans a `Yield` terminator into `CoroutineSavedLocals`. `compute_layout` then uses a `storage_conflicts: &BitMatrix<CoroutineSavedLocal, CoroutineSavedLocal>` conflict matrix so locals whose storage intervals are strictly disjoint share overlapping enum variant storage.
- **`LLVM CoroFrame` (`llvm/lib/Transforms/Coroutines/CoroFrame.cpp:57–314`):** `FrameDataInfo` partitions cross-suspend SSA values (`Spills`) and stack allocations (`Allocas`). `addFieldForAllocas` (lines 217–251) runs `StackLifetime` to partition `AllocaInst`s into non-overlapping lifetime sets and place each disjoint set in a shared union-like frame slot (respecting ABI alignment). However, any missing or delayed `llvm.lifetime.end` intrinsic forces `StackLifetime` to treat the `alloca` as live across the suspend point, permanently inflating the coroutine frame.

#### Executable Probe 2A: `rustc 1.98.0-nightly` `async fn` State-Machine Size Measurement
Compiled with `rustc --edition 2024 -O` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-linux`), measuring `std::mem::size_of_val(&fut)` on five minimal `async fn` functions containing `[u8; 4096]` arrays and a `Drop`-implementing `BufGuard([u8; 4096])`:

| `async fn` Variant | Measured `size_of_val(&fut)` | Root Cause in MIR Coroutine Lowering |
|---|---:|---|
| `leaky_outer_scope()` (`Copy` `[u8; 4096]` bound before `.await`, **never read after `.await`**) | **`4,099 bytes`** | `StorageDead(buf)` is emitted at enclosing block exit (`}`), so `locals_live_across_suspend_points` saves all 4,096 dead bytes despite `Copy` + zero post-await uses! |
| `drop_held_across_await()` (`BufGuard([u8; 4096])` with `Drop`, unused after `.await`) | **`4,099 bytes`** | Lexical RAII drops `g` at `}`, keeping `g` live across `Yield`. |
| `drop_scoped_before_await()` (identical `BufGuard`, placed in `{ ... }` before `.await`) | **`3 bytes`** | `StorageDead` + `Drop` execute before `Yield`; **1,366× frame reduction**. |
| `two_disjoint_awaits_overlapping()` (two sequential `{ BufGuard; .await; }` blocks) | **`4,099 bytes`** | `compute_layout` sees disjoint `storage_conflicts` and overlaps both 4,096-byte variants in the same enum storage. |
| `two_simultaneous_awaits()` (two `BufGuard`s live across the second `.await`) | **`8,194 bytes`** | Both guards conflict at the second `Yield`, forcing additive storage (`2 × 4096 + state/padding`). |

---

### 4. Automatic Amortized Resource Analysis (`AARA` / `RAML`)

Basis: normative + execution (POPL 2003 DOI `10.1145/604131.604151`; TOPLAS 2012 DOI `10.1145/2362389.2362393`; POPL 2017 DOI `10.1145/3009837.3009842`; FoSSaCS 2020 DOI `10.1007/978-3-030-44914-8_19`; `CPython 3.13.15` Probe 2C)

`AARA` (Hofmann & Jost POPL 2003; scaled in Jan Hoffmann's `RAML` across TOPLAS 2012, POPL 2017 for OCaml, and FoSSaCS 2020 for exponential bounds) embeds Tarjan's physicist's method inside a resource-annotated affine type judgment $\Gamma \mid q \vdash e : \tau \mid q'$:

- **Binomial potential basis & LP reduction:** For a list of length $n$, polynomial potential of degree $d$ is parameterized in the binomial basis $\Phi(n; \vec{q}) = \sum_{k=1}^d q_k \binom{n}{k}$ with $q_k \ge 0$. Because Pascal's identity $\binom{n+1}{k} = \binom{n}{k} + \binom{n}{k-1}$ is **linear** in the unknown coefficients $\vec{q}$, pattern-matching a `cons` cell shifts potential linearly: $\vec{q} \mapsto \triangleleft(\vec{q})$ where $(\triangleleft q)_k = q_k + q_{k+1}$ and constant potential $q_1$ is released immediately. (Kahn & Hoffmann FoSSaCS 2020 similarly use Stirling numbers of the second kind to express $2^n$-class exponential potentials as linear constraints!) Thus inferring tight worst-case multivariate polynomial bounds reduces to solving a single **Linear Program** in milliseconds, and LP solutions can be checked independently via rational Farkas dual certificates without putting the LP solver inside the TCB.
- **Probe 2C verification:** For insertion sort (worst-case $\binom{n}{2} = n(n-1)/2$ comparisons), `Phi(n+1) = q_1 + (q_1 + q_2) C(n,1) + q_2 C(n,2)`. Inserting into a length-$n$ list costs $1 \cdot C(n,1)$, yielding linear constraints $q_2 \ge 1, q_1 \ge 0$ whose LP optimum $(q_1 = 0, q_2 = 1)$ gives exact worst-case bound $\Phi(n) = \binom{n}{2}$ (verified identically for $n \in \{0, 1, 5, 10, 100\}$).
- **Affine sharing & Rust alignment:** Duplicating a variable $x$ in an expression must *split* its potential ($\vec{q} = \vec{q}_1 + \vec{q}_2$) rather than clone it—an exact match for affine ownership types (e.g., Rust move semantics and `&mut T` reborrowing returning remaining potential on borrow expiry).
- **Hard boundaries:** Standard LP-based `AARA` cannot automatically infer logarithmic/inverse-Ackermann bounds ($O(n \log n)$, $O(\alpha(n))$), value-dependent non-structural loops (`while x < y`), or cyclic aliased mutable graphs; furthermore, compositional analysis breaks at unannotated FFI calls unless foreign signatures carry trusted potential contracts.

---

### 5. Cost-Aware Logical Frameworks (`calf` POPL 2022 and `decalf` POPL 2024)

Basis: source + normative (`calfproject/agda-calf` @ `10f1ba616e1ade017e4048324ae894281379ce08`; POPL 2022 DOI `10.1145/3498670`; POPL 2024 DOI `10.1145/3632852`)

`calf` (Niu, Sterling, Grodin, & Harper, POPL 2022) and `decalf` (Grodin, Niu, Sterling, & Harper, POPL 2024) unify functional correctness and cost analysis in a single dependent Call-By-Push-Value (CBPV) logical framework (`calfproject/agda-calf`) using a **synthetic phase distinction**:

- **Cost step effect and extensional phase collapse (`src/Calf/Step.agda:27–63`):** Parameterized by an arbitrary `CostMonoid` $(\mathbb{C}, \text{zero}, +, \le)$, the primitive effect `step : (X : tp⁻) → ℂ → cmp X → cmp X` satisfies monoid rewrite laws (`step/0`, `step/+`, `bind/step`) and the **phase-distinction law**:
  ```agda
  step/ext : (X : tp⁻) (e : cmp X) (c : ℂ) (u : ext) → step X c e ≡ e
  ```
  Under the extensional phase proposition `u : ext`, all cost annotations vanish definitionally/propositionally, allowing standard extensional equational proofs without tick-monad pollution.
- **Cost noninterference theorem (`src/Calf/Phase/Noninterference.agda:28–59`):** Using the closed intensional modality `●` and open extensional modality `◯⁺`, `calf` proves `constant` (every function `val (● A) → val (◯⁺ B)` is constant) and `oblivious`:
  ```agda
  oblivious : ∀ {A B} (f : cmp (F A) → val (◯⁺ B)) → ∀ c e → f (step (F A) c e) ≡ f e
  ```
  guaranteeing by construction that no program's extensional output can branch on its step count.
- **Directed preorder for effectful/probabilistic bounds (`decalf`, `src/Calf/Phase/Directed.agda:14–18`, `Step.agda:69–87`):** When probabilistic choice or mutable state enters, cost and output are jointly distributed and cannot split into a writer pair `(val, cost)`. `decalf` equips every type with a directed preorder `≤⁻` (`step-mono-≤⁻`) satisfying `≤⁺-ext-≡ : ext → a ≤⁺[ A ] a' → a ≡ a'`, so an upper bound on a randomized algorithm (e.g., expected comparisons of randomized Quicksort) is itself an effectful program bounding the implementation while agreeing extensionally under `ext`.
- **FFI & backend gap:** `calf`/`decalf` reason over manually placed high-level `step` annotations in Agda; lowering to native hardware requires a **verified cost-monoid homomorphism** $\phi : \mathbb{C}_{\text{src}} \to \mathbb{C}_{\text{tgt}}$ and non-interference checking that foreign calls do not read hardware timers (`rdtsc`) to alter extensional control flow.

---

### 6. Separation Logic with Time Credits, Receipts, GC Space Credits, and Lazy Thunk Debits (`Iris` / `CFML`)

Basis: normative (JAR 2019 DOI `10.1007/s10817-017-9435-6`; ESOP 2019 DOI `10.1007/978-3-030-17184-1_1`; POPL 2022 DOI `10.1145/3498672`; POPL 2023 DOI `10.1145/3571218`; POPL 2024 DOI `10.1145/3632892`)

To verify imperative, cyclic, aliased, concurrent, and lazy persistent data structures beyond `AARA`'s polynomial fragment, the `CFML`/`Iris` lineage encodes resource bounds as first-class linear/affine separation-logic assertions:

1. **Time Credits (`$ n`, Charguéraud & Pottier JAR 2019):** Each computation step consumes `$ 1`. Because `$ n` is an ordinary separation-logic resource, potential can be **stored directly inside mutable heap invariants** (e.g., Union-Find tree nodes banking credits proportional to rank difference to pay for path compression, mechanizing the $O(\alpha(n))$ amortized bound).
2. **Time Receipts (`⌛ n`, Mével, Jourdan, & Pottier ESOP 2019):** Lifted into concurrent higher-order `Iris`, time receipts are duplicable witnesses that *at least* $n$ steps have elapsed—enabling lower-bound proofs and safety proofs of practical systems invariants such as proving a 64-bit monotonic counter cannot overflow within $2^{62}$ steps.
3. **Tracing-GC Heap Space Credits (`◇ n`, Madiot & Pottier POPL 2022 $\text{SL}^\diamond$; Moine, Charguéraud, & Pottier POPL 2023):** Because tracing GC reclaims an object only when *all* paths from live roots vanish, $\text{SL}^\diamond$ pairs space credits `◇ size` with **`pointed-by` predecessor-multiset assertions** so logically deallocating an unreachable block reclaims its `◇ size`. Moine et al. (POPL 2023) lift this to a high-level call-by-value $\lambda$-calculus with closures via **`stackable` assertions** tracking stack-to-heap roots implicitly. Limitations: cyclic garbage requires proving entire SCCs have zero external incoming edges, and $\text{SL}^\diamond$ models an *ideal instantaneous collector* rather than real generational/concurrent collectors (G1, ZGC, OCaml 5) whose floating garbage and fragmentation add $1.5\times$–$4\times$ physical RAM headroom. At managed↔native FFI boundaries (`JNI`, `CAMLparam`, `Py_INCREF`), un-tracked foreign roots break `pointed-by` soundness unless modeled via scoped linear root guards.
4. **Thunks and Debits for Persistent Lazy Data Structures (`Pottier, Guéneau, Jourdan, & Mével POPL 2024`):** Standard banked credits fail for Okasaki's persistent queues because a caller can clone and force an old version arbitrarily many times (you cannot spend one linear credit twice). Pottier et al. mechanize Okasaki's **debit discipline** in `Iris` on top of time credits: each memoized thunk carries a monotonic ghost-state debt counter; paying 1 time credit permanently reduces the thunk's debt across *all* shared persistent references (including debits assigned to "future thunks" not yet allocated), and once debt reaches `0`, forcing the thunk once memoizes its result so all subsequent forces across all persistent versions cost $O(1)$. Crossing a strict FFI boundary without exposing `debt == 0` in the interface risks triggering an unexpected $O(N)$ suspension stall (or unsynchronized concurrent forcing races).

---

### 7. Resource-Verification Paradigm Comparison, End-to-End Stack/Heap Compilation, and Intensional Security

Basis: source + normative (`CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`; `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`; PLDI 2014 DOI `10.1145/2594291.2594301`; POPL 2019 DOI `10.1145/3290375`; OOPSLA 2020 DOI `10.1145/3428272`; POPL 2020 DOIs `10.1145/3371092`, `10.1145/3371075`)

#### Resource-Verification Paradigm Matrix

| Paradigm / System | Automation | Supported Complexity Classes | Mutable Aliasing / Concurrency | Tracing GC Support | Compiler Backend Preservation |
|---|---|---|---|---|---|
| **`AARA` / `RAML`** (POPL 2003–2017, FoSSaCS 2020) | **Fully automatic** (LP solver) | Linear, multivariate polynomial, Stirling exponential | Affine/owned only; breaks on arbitrary cyclic aliasing | Allocation count (no GC reclamation) | Source / functional IR (stack/heap C prototype in `Carbonneaux`) |
| **`calf` / `decalf`** (POPL 2022 / POPL 2024) | Manual proof in Agda | Arbitrary recurrences, parallel span/work, expected probabilistic cost | Pure CBPV (`calf`); effectful/probabilistic (`decalf`) | None | None (abstract `CostMonoid`, no native backend) |
| **`Iris` Time Credits & Receipts** (JAR 2019 / ESOP 2019) | Interactive Coq/Iris (`~5–15×` overhead) | Arbitrary ($O(\log n)$, $O(\alpha(n))$, lower bounds via receipts) | **Full** mutable pointer aliasing & concurrency | None (time only) | Source `HeapLang` / OCaml (`CFML`), not machine code |
| **`Iris` Thunks & Debits** (POPL 2024) | Interactive Coq/Iris | Persistent lazy amortized ($O(1)$ Okasaki queues/streams) | Sequential memoization (concurrent blackholing open) | None (time only; suspension space separate) | Source `HeapLang` |
| **`SL⋄` / Moine GC Space Logic** (POPL 2022 / POPL 2023) | Interactive Coq/Iris | Exact live-heap word bounds | Mutable heap + closures (`stackable` + `pointed-by`) | **Ideal tracing GC** (instantaneous) | Source / low-level abstract machine |
| **`Liquid Haskell` `Tick`** (POPL 2020) | High (SMT refinement types) | Polynomial, $O(n \log n)$, relational cost diffs | Pure Haskell | None | **Unsound under GHC lazy/FloatOut** unless strictness-verified |
| **`Stack-Aware CompCert`** (PLDI 2014 / POPL 2019) | Verified Coq + per-function bounds | Exact compiled x86 stack bytes | Imperative C (separate compilation) | Manual / stack only | **End-to-end verified to x86 asm** |
| **`CakeML` Space Cost Semantics** (OOPSLA 2020) | Verified HOL4 | Exact compiled heap + stack word bounds | Functional + mutable refs/arrays | **Yes** (`dataSemScript.sml` `size_of` + `limits`) | **End-to-end verified to machine code** |

#### End-to-End Compiled Stack and Heap Verification (`Stack-Aware CompCert` & `CakeML`)
Even verified source bounds miss hardware-level byte costs: register-allocator spill slots, 16-byte ABI stack alignment padding, callee-saved register saves, tagged object headers, and linker veneers.
- **`CakeML` (`compiler/backend/semantics/dataSemScript.sml:43–135`):** Explicitly models `limits = <| heap_limit : num; length_limit : num; stack_limit : num; arch_64_bit : bool; ... |>` and tracks `safe_for_space : bool`, `peak_heap_length : num`, `stack_max : num option`, and exact word-level object accounting in `size_of_def` (`Word64 _` = 3 words; `small_num` fits unboxed in `[-2^62, 2^62)` on 64-bit, else `bignum_size`). Gómez-Londoño et al. (OOPSLA 2020, DOI `10.1145/3428272`) prove that CakeML's compiler preserves these concrete space bounds down to target machine code, eliminating silent OOM traps.
- **`CompCert` Stack Extensions:** Carbonneaux et al. (PLDI 2014, DOI `10.1145/2594291.2594301`) derive verified x86 stack bounds from Clight via quantitative Hoare logic; Wang, Wilke, & Shao (POPL 2019, DOI `10.1145/3290375`) replace `CompCert`'s unbounded stack blocks with a finite **abstract stack** enabling compositional stack-finiteness proofs across separate compilation, inlining, and tail calls. Both still hit barriers on indirect calls (`dyn Fn` / function pointers without stack-bound annotations), dynamic loading (`dlopen`), and asynchronous signal handlers sharing the user stack.

#### Intensional Security: `HashDoS`, `ReDoS`, and Constant-Time Preservation (`POPL 2020`)
- **Algorithmic-Complexity DoS (`Crosby & Wallach 2003`; `SipHash`):** By the pigeonhole principle, every unseeded deterministic hash function admits precomputable collision sets turning $O(N)$ maps into $O(N^2)$ CPU exhaustion (`HashDoS`). In `rust-lang/rust` (`library/std/src/collections/hash/map.rs:11–31,222–254`), `std::collections::HashMap<K, V, S = RandomState>` defaults to per-process randomly seeded **SipHash 1-3** (Aumasson & Bernstein, INDOCRYPT 2012), explicitly warning at line 222 that swapping to `BuildHasherDefault<DefaultHasher>` (or `FxHashMap`) loses `HashDoS` resistance. Crossing FFI from Rust `SipHash` into C++ `std::unordered_map` (often unseeded identity/FNV) or backtracking PCRE regex engines (`ReDoS` $O(2^N)$ vs. Thompson-NFA $O(N)$) immediately reopens complexity DoS at the boundary.
- **Constant-Time Side-Channel Preservation (`Barthe et al. POPL 2020`, DOI `10.1145/3371075`):** Optimizing passes (`LLVM` `SimplifyCFG`, `SelectOptimize`, `InstCombine`) routinely turn branchless bitwise selects back into secret-dependent conditional branches or eliminate dead zeroing stores. Barthe et al. proved that preserving cryptographic constant-time in `CompCert` requires upgrading compiler correctness from single-trace extensional refinement to **2-safety leakage-trace preservation** (identical PC and memory-address traces for secret-equivalent inputs)—confirming that safe-for-space, worst-case complexity, and constant-time preservation are all broken by the identical extensional-refinement omission.

## Boundaries

- **Bridging `decalf` / `Iris` Time Credits through `LLVM -O2` to physical RAM under concurrent generational GCs (`unknown`):** No published system currently composes `Iris` time/space credits or `decalf` cost monoids end-to-end through an optimizing `LLVM` backend down to physical RAM bounds under real concurrent/generational/moving collectors (e.g., `MMTk`, `ZGC`, `OCaml 5` multicore GC) with verified headroom multipliers $\alpha_{\text{GC}}$.
- **Unifying `AARA` LP inference with Rust's full borrow checker (`unknown`):** While Rust's affine ownership aligns structurally with `AARA`'s potential splitting, automatic multivariate LP potential inference covering interior mutability (`RefCell`/`Mutex`), unsafe pointer aliasing, and trait objects (`dyn Trait`) remains unresolved.
- **Concurrent atomic thunk forcing + simultaneous heap-space bounds (`not examined` / open):** Pottier et al. (POPL 2024) formalize sequential memoized thunks and debits in `Iris`; combining concurrent atomic memoization (blackholing / `OnceLock`) with `Moine et al. (POPL 2023)` GC space credits in a single mechanized logic is not yet established in the examined papers.
- **Extension of `CertiCoq`'s safe-for-space proof past closure conversion through `CompCert` Cminor/Mach (`known not to apply` at examined commit):** At `CertiCoq/certicoq` commit `ab66e0164e7ecb63e5af95c90c8e479068bf95c2`, `closure_conversion_correct.v` proves space preservation on `LambdaANF` closure conversion; downstream `CompCert` passes (`driver/Complements.v`) remain extensional-only unless composed with `Stack-Aware CompCert` and a verified runtime GC space theorem.
- **`Liquid Haskell` `Tick` soundness under `GHC -O2` (`known not to apply`):** Handley et al. (POPL 2020) verify user-instrumented `Tick` counts; `GHC` call-by-need sharing and `FloatOut` optimizations can diverge from `Tick` annotations without operational strictness verification.
- **Hardware microarchitectural cycle-accurate WCET (`not examined`):** This report addresses asymptotic complexity, abstract step bounds, and exact stack/heap word/byte bounds; pipeline-level cache/branch-predictor/interconnect WCET modeling is outside scope.

## Evidence

### Primary Git Source Artifacts (Observed `2026-11-19`)
- **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`:**
  - `driver/Complements.v:31–150`: `transf_c_program_preservation`, `transf_c_program_is_refinement`, `c_program_satisfies_spec` (extensional trace refinement over `program_behaves`).
- **`CertiCoq/certicoq` @ `ab66e0164e7ecb63e5af95c90c8e479068bf95c2`:**
  - `theories/LambdaANF/closure_conversion.v:29–174`: `project_var`, `project_vars`, `Closure_conversion` flat free-variable projection.
  - `theories/LambdaANF/bounds.v:91–412`: `inline_bound`, `simple_bound`, `hoisting_bound`, `ll_bound` quantitative step/space postconditions.
  - `theories/LambdaANF/closure_conversion_correct.v:78–325`: `Closure_conversion_fundefs_correct`, `cc_approx_exp`, `cc_approx_env_P`.
- **`CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`:**
  - `compiler/backend/semantics/dataSemScript.sml:35–135`: `limits` (`heap_limit`, `stack_limit`), `state` (`stack_max`, `safe_for_space`, `peak_heap_length`), `small_num_def`, `bignum_size_def`, `size_of_def`.
- **`calfproject/agda-calf` @ `10f1ba616e1ade017e4048324ae894281379ce08`:**
  - `src/Calf/Step.agda:27–87`: `step`, `step/0`, `step/+`, `step/ext`, `bind/step`, `step-mono-≤⁻`.
  - `src/Calf/Phase/Directed.agda:14–18`: `≤⁺-ext-≡`, `≤⁻-ext-≡`.
  - `src/Calf/Phase/Noninterference.agda:20–60`: `unique`, `constant`, `optimization`, `oblivious`.
- **`llvm/llvm-project` @ `507de0cc365e4c6317d21fb08e298f742256a51f`:**
  - `llvm/lib/Transforms/Coroutines/CoroFrame.cpp:21,57–314`: `FrameDataInfo`, `StackLifetime` non-overlapping `alloca` slot sharing in `addFieldForAllocas` (L217–251).
- **`rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`:**
  - `compiler/rustc_mir_transform/src/coroutine/mod.rs:64,459–518,1028–1149,1273–1331`: `CoroutineSavedLocals`, `locals_live_across_suspend_points`, `storage_conflicts`, `compute_layout`.
  - `library/std/src/collections/hash/map.rs:11–31,222–254`: `RandomState` SipHash 1-3 default and explicit non-`HashDoS`-resistant warning for `BuildHasherDefault`.

### Peer-Reviewed Literature
- Clinger, *Proper Tail Recursion and Space Efficiency*, PLDI 1998, DOI `10.1145/277650.277719`.
- Shao & Appel, *Efficient and Safe-for-Space Closure Conversion*, ACM TOPLAS 22(1):129–161, 2000, DOI `10.1145/345099.345125`.
- Paraskevopoulou & Appel, *Closure Conversion Is Safe for Space*, ICFP 2019, DOI `10.1145/3341687`.
- Gustavsson & Sands, *A Foundation for Space-Safe Transformations of Call-by-Need Programs*, HOOTS 1999 / ENTCS 26:69–86, DOI `10.1016/S1571-0661(05)80284-1`.
- Hofmann & Jost, *Static Prediction of Heap Space Usage for First-Order Functional Programs*, POPL 2003, DOI `10.1145/604131.604151`.
- Hoffmann, Aehlig, & Hofmann, *Multivariate Amortized Resource Analysis*, ACM TOPLAS 34(3), 2012, DOI `10.1145/2362389.2362393`.
- Hoffmann, Das, & Weng, *Towards Automatic Resource Bound Analysis for OCaml* (`RAML`), POPL 2017, DOI `10.1145/3009837.3009842`.
- Kahn & Hoffmann, *Exponential Automatic Amortized Resource Analysis*, FoSSaCS 2020, DOI `10.1007/978-3-030-44914-8_19`.
- Niu, Sterling, Grodin, & Harper, *A Cost-Aware Logical Framework* (`calf`), POPL 2022, DOI `10.1145/3498670`, `arXiv:2107.04663`.
- Grodin, Niu, Sterling, & Harper, *Decalf: A Directed, Effectful Cost-Aware Logical Framework*, POPL 2024, DOI `10.1145/3632852`.
- Charguéraud & Pottier, *Verifying the Correctness and Amortized Complexity of a Union-Find Implementation in Separation Logic with Time Credits*, JAR 62(3):331–365, 2019, DOI `10.1007/s10817-017-9435-6`.
- Mével, Jourdan, & Pottier, *Time Credits and Time Receipts in Iris*, ESOP 2019, DOI `10.1007/978-3-030-17184-1_1`.
- Madiot & Pottier, *A Separation Logic for Heap Space under Garbage Collection*, POPL 2022, DOI `10.1145/3498672`.
- Moine, Charguéraud, & Pottier, *A High-Level Separation Logic for Heap Space under Garbage Collection*, POPL 2023, DOI `10.1145/3571218`.
- Pottier, Guéneau, Jourdan, & Mével, *Thunks and Debits in Separation Logic with Time Credits*, POPL 2024, DOI `10.1145/3632892`.
- Carbonneaux, Hoffmann, Ramananandro, & Shao, *End-to-End Verification of Stack-Space Bounds for C Programs*, PLDI 2014, DOI `10.1145/2594291.2594301`.
- Wang, Wilke, & Shao, *An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code*, POPL 2019, DOI `10.1145/3290375`.
- Gómez-Londoño, Pohjola, Syeda, Myreen, & Tan, *Do You Have Space for Dessert? A Verified Space Cost Semantics for CakeML Programs*, OOPSLA 2020, DOI `10.1145/3428272`.
- Handley, Vazou, & Hutton, *Liquidate Your Assets: Reasoning About Resource Usage in Liquid Haskell*, POPL 2020, DOI `10.1145/3371092`.
- Crosby & Wallach, *Denial of Service via Algorithmic Complexity Attacks*, USENIX Security 2003; Aumasson & Bernstein, *SipHash*, INDOCRYPT 2012 / IACR ePrint `2012/351`.
- Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, & Trieu, *Formal Verification of a Constant-Time Preserving C Compiler*, POPL 2020, DOI `10.1145/3371075`.

### Executable Probes (Executed `2026-11-19`, `x86_64-linux`)

#### Probe 2A: `rustc 1.98.0-nightly` `async fn` Frame Sizes
```rust
// Save to /tmp/probe_async_space.rs
// Compile & run: rustc --edition 2024 -O /tmp/probe_async_space.rs -o /tmp/probe_async_space && /tmp/probe_async_space
use std::{future::Future, mem::size_of_val, pin::Pin, task::{Context, Poll}};
struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        if self.0 { Poll::Ready(()) } else { self.0 = true; Poll::Pending }
    }
}
#[inline(never)] fn use_buf(b: &[u8; 4096]) -> u8 { std::hint::black_box(b[0]) ^ std::hint::black_box(b[4095]) }
struct BufGuard([u8; 4096]);
impl Drop for BufGuard { fn drop(&mut self) { std::hint::black_box(self.0[0]); } }

async fn leaky_outer_scope() -> u8 { let buf = [7u8; 4096]; let x = use_buf(&buf); YieldOnce(false).await; x }
async fn drop_held_across_await() -> u8 { let g = BufGuard([7u8; 4096]); let x = use_buf(&g.0); YieldOnce(false).await; x }
async fn drop_scoped_before_await() -> u8 { let x = { let g = BufGuard([7u8; 4096]); use_buf(&g.0) }; YieldOnce(false).await; x }
async fn two_disjoint_awaits_overlapping() -> u8 {
    let a = { let g1 = BufGuard([1u8; 4096]); YieldOnce(false).await; use_buf(&g1.0) };
    let b = { let g2 = BufGuard([2u8; 4096]); YieldOnce(false).await; use_buf(&g2.0) };
    a ^ b
}
async fn two_simultaneous_awaits() -> u8 {
    let g1 = BufGuard([1u8; 4096]); YieldOnce(false).await;
    let g2 = BufGuard([2u8; 4096]); YieldOnce(false).await;
    use_buf(&g1.0) ^ use_buf(&g2.0)
}
fn main() {
    println!("leaky_outer_scope={}", size_of_val(&leaky_outer_scope()));
    println!("drop_held_across_await={}", size_of_val(&drop_held_across_await()));
    println!("drop_scoped_before_await={}", size_of_val(&drop_scoped_before_await()));
    println!("two_disjoint_awaits_overlapping={}", size_of_val(&two_disjoint_awaits_overlapping()));
    println!("two_simultaneous_awaits={}", size_of_val(&two_simultaneous_awaits()));
}
```
Observed stdout on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`:
```text
leaky_outer_scope=4099
drop_held_across_await=4099
drop_scoped_before_await=3
two_disjoint_awaits_overlapping=4099
two_simultaneous_awaits=8194
```

#### Probe 2A-ii: `GCC 15.2.0` `[[gnu::musttail]]` Calling-Convention & Cleanup Rejection
```c
// Save to /tmp/probe_musttail.c and run: gcc -O2 -c /tmp/probe_musttail.c -o /tmp/probe_musttail.o
void cleanup_fn(int *p);
int callee(int n);
int caller_cleanup(int n) {
    int x __attribute__((cleanup(cleanup_fn))) = n;
    [[gnu::musttail]] return callee(n - 1);
}
int callee_many(int a, int b, int c, int d, int e, int f, int g, int h);
int caller_many(int n) {
    [[gnu::musttail]] return callee_many(n, n, n, n, n, n, n, n);
}
```
Observed stderr on `gcc (Debian 15.2.0-14) 15.2.0`:
```text
probe_musttail.c:5:30: error: cannot tail-call: other reasons
probe_musttail.c:9:30: error: cannot tail-call: callee required more stack slots than the caller
```

## Revalidation

1. **Rust coroutine storage-liveness improvements:** Re-compile and run Probe 2A against newer `rustc` toolchains (or diff `compiler/rustc_mir_transform/src/coroutine/mod.rs` and `layout.rs` in `rust-lang/rust`). If `leaky_outer_scope` shrinks from `4099` to `3` bytes, `rustc` has implemented NLL/value-based last-use `StorageDead` narrowing for `Copy` locals prior to coroutine state lowering.
2. **Rust explicit tail calls (`become`) & `LLVM musttail`:** Check Rust RFC tracking for `become` and re-run Probe 2A-ii under `clang`/`gcc` with callee-pops conventions (e.g., `[[gnu::musttail]]` + `tailcc`/preserve-none ABIs) to verify whether stack-argument-slot mismatch constraints are relaxed.
3. **`CertiCoq` & `CakeML` quantitative backends:** Diff `CertiCoq/certicoq` (`theories/LambdaANF/bounds.v`, `closure_conversion_correct.v`, and codegen bridge to `CompCert`) to check whether safe-for-space proofs extend beyond `LambdaANF` into Cminor/Asm. Diff `CakeML/cakeml` (`compiler/backend/semantics/dataSemScript.sml`) for updated GC/word-size space models.
4. **Cost-aware logical frameworks (`calf`/`decalf`):** Diff `calfproject/agda-calf` (`src/Calf/Step.agda`, `src/Calf/Phase/Directed.agda`) for verified extraction or cost-monoid homomorphisms targeting compiled runtimes.
5. **Default `HashMap` hasher:** Check `library/std/src/collections/hash/map.rs` in `rust-lang/rust` to confirm `RandomState` (`SipHash 1-3`) remains the default `HashDoS`-resistant hasher.
