# Concatenative Stack Calculi, Interaction Nets, and Mirror Reflection

## Summary

Five seemingly disparate non-mainstream paradigms—**concatenative stack calculi** (Forth, Factor, Kitten), **goal-directed evaluation** (Icon/Unicon), **first-class non-standard evaluation** (Kernel `$vau`/fexprs, R lazy promises), **capability-based mirror reflection** (Bracha–Ungar mirrors, Newspeak, Dart), and **interaction-net graph reduction** (Lafont interaction combinators, Lamping optimal sharing, HVM2, Vine)—are governed by a single compiler law: **what a callee is allowed to observe about its caller's environment, syntax, stack, metadata, or sharing topology directly determines what ahead-of-time (AOT) compilation, dead-code pruning, equational optimization, and lock-free parallelism remain sound.**

Key technical findings established from primary sources, peer-reviewed theorems, and executable probes:

- **Concatenative stack calculi make structural rules explicit and unify stack polymorphism with row polymorphism.** Forth's untyped data/return stacks and mutable `STATE` flag trade static checking for kilobyte-scale extensibility, whereas Factor (`basis/stack-checker`) checks stack heights statically across literal/`curry`/`compose` quotations (requiring `inline` for row-polymorphic combinators and a runtime-checked `call( x -- y )` escape hatch for computed quotations) and Kitten (`common.ktn`, `Kitten.Infer`) unifies stack-remainder rows `R...` with linear/effect permissions `+Fail`, `+IO` so `call<R..., S...>` denotes modus ponens. Because concatenative syntax has no named variables, `dup`, `drop`, and `swap` directly materialize linear logic's contraction, weakening, and exchange rules.
- **Icon's goal-directed evaluation generalizes expressions to `0..n` result streams compiled via four-port control flow.** Unicon/Icon (`src/runtime/interp.r` `Op_Psusp`, `Op_Efail`) replaces booleans with success/failure and generator resumption; Proebsting (PLDI 1997) lowers every expression cleanly via four ports (`start`, `resume`, `fail`, `succeed`), yet native foreign frames cannot suspend and data mutation is not automatically reversed on backtracking.
- **Unrestricted caller-scope and syntax capture collapses equational theory and defeats AOT optimization.** Kernel operatives (`klisp` `src/keval.c`, `K_TOPERATIVE`) receive unevaluated operand syntax and the caller's dynamic environment directly; Wand (1998) proved that under unrestricted fexprs, contextual equivalence collapses to syntactic $\alpha$-identity, invalidating general source-to-source optimization unless operatives are statically resolved via partial evaluation (`arXiv:2303.12254`). R's universal 3-slot lazy promises (`value`, `expression`, `environment` in `R-lang.texi`) combined with `substitute()` exhibit the exact same optimization barrier (`1 + 1` is observationally distinct from `2`), while R's C FFI (`R-exts.texi`) layers a manual `PROTECT`/`UNPROTECT` stack and `longjmp` error unwinding on top.
- **Mirrors turn ambient reflection into an unforgeable capability, exposing the closed-world AOT pruning tension.** Bracha and Ungar (OOPSLA 2004) separate meta-level authority from base-level objects via *encapsulation*, *stratification*, and *ontological correspondence*—enabling least-privilege FFI marshalers (Newspeak). Yet dynamic mirror reflection still conflicts with AOT whole-program tree shaking unless reflective reach is statically bounded, explaining why Dart deprecated `dart:mirrors` (`@deprecated`, VM-only) and why GraalVM Native Image requires explicit reachability metadata.
- **Interaction combinators buy strong confluence and lock-free parallelism, while optimal sharing hits an irreducible bookkeeping cliff.** Because every Lafont agent has exactly one principal port, active pairs never overlap, giving **strong confluence** and schedule-invariant reduction counts. HVM2 (`src/hvm.c`) implements 8 node tags in 32-bit `Port` words with lock-free atomic `VAR` linking (`vars_exchange`), but deliberately uses a **single unlabeled `DUP` tag** (`DUP ~ DUP -> ANNI`) to avoid Lamping's dynamic fan-level oracle (which Asperti and Mairson proved incurs **non-elementary worst-case bookkeeping overhead**). Executable simulation proves a sharp three-tier separation: (1) unlabeled HVM2 diverges even on disjoint Church application `c2(c2)`; (2) static-labeled combinators reduce `c3[2](c2[3]) (+1) 0` to `8` in **exactly `49` interactions across 20 random schedules**, yet **still diverge on `(λx. x x) c2`** because cloning duplicates static labels; and (3) general $\lambda$-calculus self-application mathematically requires either dynamic Lamping level-shifting or static stratification (Elementary/Light Affine Logic).

## Applicability

This report synthesizes primary source code, reference manuals, peer-reviewed theorems, and standalone Python 3 execution probes across fifteen pinned repositories (`factor/factor@f05a4e9d49d17881c65f9b21e05095d0ff3adc50`, `evincarofautumn/kitten@2bbc264d7f05c4a7d7b35d06773d1ab2f0623193`, `forthy42/gforth@15375fb0469d6590980adc2bf4cbddb241a671a6`, `uniconproject/unicon@d3df4185f1e262508bd5beda1e69bfcdac251bf9`, `dbohdan/klisp@2b3a1cf774e0ab527a561e5d93dacbfdf0b545d1`, `wch/r-source@94152790dbd49be40c28c1819f92370fb7581f0a`, `dart-lang/sdk@e1671c00019972a92e16247dc254ad3eaa48c2b6`, `newspeaklanguage/newspeak@84cc19da84aa7d4790dae155ea8f9a64c5855f87`, `HigherOrderCO/HVM@7365a56cca56a5853c979755891cb86aa343c42d`, `HigherOrderCO/HVM2@654276018084b8f44a22b562dd68ab18583bfb5b`, `HigherOrderCO/HVM3@fba2e9c82faf6e2f019c9ecea94c32f19a8b7820`, `HigherOrderCO/Bend1@814453670d0e0d6777c1313c972764dba0491b7f`, `HigherOrderCO/Bend@0e2f38f759cc830849e489307f3d256a7d148288`, `VineLang/vine@cf0c325834d5bf4c8d43aa36f7fb76faf2496988`, `inpla/inpla@864d529191ac83b776d301839c6b485c432e2725`) and the cited foundational papers.

How the subjects relate:

- **Version and lineage disambiguation in HigherOrderCO repositories:** `HigherOrderCO/HVM` (`7365a56c...`) is HVM1; `HigherOrderCO/HVM2` (`65427601...`) is the C/CUDA interaction-combinator evaluator described in the HVM2 paper; `HigherOrderCO/Bend1` (`81445367...`) is the legacy HVM2 frontend preserving `docs/dups-and-sups.md`; `HigherOrderCO/HVM3` (`fba2e9c8...`) is the WIP Interaction Calculus successor; and the current `HigherOrderCO/Bend` (`0e2f38f7...`) repository presents a distinct dependent-typed proof-oriented language rather than legacy Bend1. Findings carefully distinguish these lineages.
- **Execution scope:** Native Factor, Kitten, Gforth, Unicon, R, klisp, and HVM2/CUDA binaries were not installed in the observation container. Execution evidence (`Basis: execution`) comes from self-contained Python 3.13 reference implementations of: (a) Hindley-Milner row-polymorphic stack-effect + permission unification, (b) Icon goal-directed alternation and R 3-slot promise forcing-order / `substitute()` probes, and (c) an exact simulator of HVM2's `VAR`-substitution linking protocol (`src/hvm.c` L811–841) and 8-tag interaction rules comparing unlabeled vs. static-labeled `DUP` nodes across random schedules.

## Findings

### 1. Relocating the Environment: Unifying Concatenative Stacks, Non-Standard Evaluation, Mirrors, and Interaction Nets

Basis: derived + source + documentation

Across compilers and FFI boundaries, the primary obstacle to modular optimization, dead-code elimination, and parallel execution is **unbounded callee visibility into caller state**. Each paradigm in this report occupies an extreme point on that axis:

| Paradigm / System | Lexical Environment | Argument Evaluation | Contraction / Duplication Mechanism | AOT Compilation & Pruning Impact | Primary FFI Boundary Clash |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Forth / Factor / Kitten** | **None** (variable-free data stack) | Strict values on stack; deferred code as quotations `[ ... ]` | Explicit `dup` word (linear/affine gating on copyable types) | Single-pass linear stack checking (`Factor`, `Wasm`, `Kitten`); no variable capture | Row-polymorphic words lack a single monomorphic C ABI; return-stack tricks break native unwind/CFI |
| **Icon / Unicon** | Lexical procedure frame + suspended generator frames | Goal-directed `0..n` generators (`suspend`/`fail`) | Generator resumption re-evaluates downstream expressions | Compiles cleanly via 4-port CFG (Proebsting PLDI 1997) | Foreign C frames cannot suspend/resume; data mutation does not auto-backtrack |
| **Kernel `$vau` / R Promises** | **First-class caller environment** passed to callee | Unevaluated operand AST (`$vau`) or lazy 3-slot promise (`R`) | Memoized per promise (`R`) or arbitrary re-eval (`$vau`) | **Destroys general equational optimization** (Wand 1998) unless statically specialized | Foreign callers have no caller AST/environment; R adds manual `PROTECT` stack + `longjmp` |
| **Capability Mirrors** (`Newspeak`, `Dart`) | Stratified meta-object separate from base object | Normal call; reflection gated by mirror capability | Mirrors inspect structure without exposing hidden fields | **Conflicts with closed-world tree shaking** unless reflective reach is statically declared | Enables least-privilege FFI marshaling without ambient object introspection |
| **Interaction Nets (`HVM2`, `Vine`)** | **None** (global local-wire graph; no lexical scope boundary) | Eager parallel active-pair reduction (`CON`, `DUP`, `OPR`) | Explicit `DUP` fan nodes; requires oracle or static stratification | Strong confluence eliminates scheduler proofs; **omitting oracle breaks soundness** | No intrinsic effect sequencing (effects require data threading); foreign agents must preserve confluence |

---

### 2. Concatenative Stack-Effect and Linear Permission Calculi: Forth, Factor, Kitten, and Verified Stack Targets

#### 2.1 Forth: Two Stacks, Threaded Code, and Mutable `STATE` Staging

Basis: documentation + source

Forth (`forthy42/gforth@15375fb0469d6590980adc2bf4cbddb241a671a6`; Bell, CACM 1973; Forth 2012 Standard) executes threaded code over two explicit, untyped stacks: a **data stack** for operand passing and a **return stack** (`>R`, `R>`, `R@`) accessible directly to user programs. Stack-effect comments such as `( n1 n2 -- n3 )` are purely informal documentation; a stack depth mistake corrupts memory silently.

Forth fuses compile time and run time in the same dictionary: words marked `IMMEDIATE` execute during compilation, `CREATE ... DOES>` constructs defining words whose runtime behavior is parameterized by allocation-time data, and legacy "state-smart" words branch dynamically on the mutable global variable `STATE` to behave differently while interpreting vs. compiling—producing notorious bugs when passed via execution tokens (`'`, `EXECUTE`, `POSTPONE`). The Forth 2012 standard formally separates **interpretation semantics** from **compilation semantics** to contain state-smart ambiguity, yet the absence of explicit phase/stage types remains an irreducible hazard when compiling Forth AOT. At an FFI boundary, direct return-stack manipulation conflicts with native hardware shadow stacks, Control-Flow Integrity (CFI), and DWARF/C++ stack unwinders.

#### 2.2 Factor: Static Stack-Effect Inference and the Inline-Combinator Boundary

Basis: source + documentation

Factor (Pestov, Ehrenberg & Groff, DLS 2010, DOI `10.1145/1869631.1869637`; `factor/factor@f05a4e9d49d17881c65f9b21e05095d0ff3adc50`, `basis/stack-checker/stack-checker-docs.factor` L6–128 and `basis/stack-checker/errors/errors.factor` L6–36) remains dynamically typed for values while enforcing **static stack-height and stack-effect checking** on all compiled words (`( ..a x -- ..b y )`).

Direct inspection of `stack-checker-docs.factor` (L18–107) establishes the exact boundary of Factor's static checker:
1. **Static quotation traceability (L19–25):** To call a combinator (such as `map`, `each`, or `call`), the quotation must either be (a) a literal quotation or built solely from literal quotations via `curry` and `compose` (which `fry` and `locals` desugar to), (b) an input parameter of a word declared `inline` (forcing callers to satisfy the same condition transitively), or (c) a non-inline parameter carrying a **fixed monomorphic effect annotation** such as `: apply-one ( x quot: ( x -- y ) -- y ) call ;` (L42), which compiles to a runtime-checked call identical to `call( x -- y )`.
2. **Row-polymorphic quotations require inlining (L43):** *"Row-polymorphic quotation parameters still require inlining."* Otherwise, calling a runtime-computed quotation throws `unknown-macro-input` or `bad-macro-input` (`errors.factor` L10–12: `"Cannot apply 'call' to a run-time computed value"`).
3. **Balanced branch heights (L69–81):** Conditionals (`if`, `cond`, `case`) require every branch to leave the stack at the exact same net height delta; otherwise the checker throws `unbalanced-branches-error` (`errors.factor` L36). If balanced, the conditional's input depth is the maximum required across branches: `[ [ + ] [ drop ] if ]` has effect `( x x x -- x )` because `[ + ]` has `( x x -- x )` ($\Delta = -1$) and `[ drop ]` has `( x -- )` ($\Delta = -1$).
4. **Recursive combinators (L76–107):** Must be declared both `inline` and `recursive`, must annotate quotation inputs with nested effects (L84: `quot: ( -- )`), must have a fixed base-case stack effect, and **cannot pass a quotation on the data stack across the recursive call** (`bad` at L92 fails; `good` at L94 lifts the call via `2keep`).

#### 2.3 Kitten: Row-Polymorphic Stack Effects, Linear Permissions, and Explicit Structural Rules

Basis: source + documentation + execution

Kitten (`evincarofautumn/kitten@2bbc264d7f05c4a7d7b35d06773d1ab2f0623193`, `common.ktn` L9–20, L435–460 and `lib/Kitten/Infer.hs` L1–75) combines Hindley-Milner type inference, **stack-row polymorphism (`R...`, `S...`)**, and **effect/permission rows (`+Fail`, `+IO`, `+Unsafe`)** without requiring inlining for polymorphic combinators. Inspecting `common.ktn` L9–20 reveals the Curry-Howard interpretation directly in the standard prelude:

```text
define call<R..., S...> (R..., (R... -> S...) -> S...):
  _::kitten::call
```
> *"This denotes modus ponens: if we have a program state `'R...'`, a permission `'+P'`, and a closure `'(R... -> S... +P)'` as evidence that we can convert `'R...'` to `'S...'` given `'+P'`, then we can invoke the closure to produce the new state `'S...'`."* (`common.ktn` L16–19)

Primitive division (`common.ktn` L435–450) explicitly tracks partiality in its permission row: `trait / <T> (T, T -> T +Fail)`.

**Structural rules as words (Baker 1994; Kerby 2002):** Because concatenative calculi eliminate named variables, every use of linear logic's structural rules appears as an explicit stack combinator: **`dup` = contraction**, **`drop` = weakening**, and **`swap`/`rot` = exchange**. Gating `dup` to `Copy` types and `drop` to `Drop` types immediately yields a variable-free linear/affine core with zero variable-capture or $\alpha$-renaming proof obligations.

**Execution probe (`probe_p3.py`, Section 3A, `Basis: execution`):** Running a standalone Hindley-Milner stack-row + permission unifier verifies three exact typing behaviors:
1. Composing `dup : (R... A -> R... A A)` with `/ : (R... Int Int -> R... Int +Fail)` unifies `A = Int` and infers `(R3, Int -> R3, Int +Fail)`.
2. Unifying balanced branches `[ + ] : (R Int Int -> R Int)` and `[ drop ] : (R X -> R)` succeeds by unifying `R_drop = (Push R_plus Int)`, yielding `(R1, Int, Int -> R1, Int)`.
3. Unifying unbalanced branches `[ + ]` ($\Delta = -1$) and `[ dup ]` ($\Delta = +1$) is rejected immediately by the **row-variable occurs check** (`occurs check: R1 in ('Push', ('Push', ('RowVar', 'R1'), ('Con', 'Int')), ('Con', 'Int'))`)—confirming why stack height imbalance reduces algebraically to a cyclic row equation $R_1 = (R_1, \tau_1, \tau_2)$!

**Higher-rank and verified-target boundaries:** Standard rank-1 HM row inference rejects a word that applies a single quotation argument at two distinct stack shapes (requiring rank-2 polymorphism). At the verified target layer, **WebAssembly** (Haas et al., PLDI 2017), **Stack-Based Typed Assembly Language (STAL)** (Morrisett et al., JFP 2002—where caller-save stack polymorphism is literally row polymorphism over the call frame), and **Michelson / Mi-Cho-Coq** (Bernardo et al., FMBC 2019) exploit single-pass linear stack-effect validation, contrasting with the **Ethereum Virtual Machine (EVM)** whose untyped stack and fixed-depth `DUP1..DUP16`/`SWAP1..SWAP16` instructions produce compiler `"stack too deep"` errors.

---

### 3. Icon Goal-Directed Multi-Value Evaluation and Four-Port Translation

Basis: documentation + source + execution

In Icon and its successor Unicon (`uniconproject/unicon@d3df4185f1e262508bd5beda1e69bfcdac251bf9`, `src/runtime/interp.r` L1681–1699 `Op_Psusp` and L1907–1925 `Op_Efail`; Griswold & Griswold 1986), **every expression is a generator producing a sequence of `0..n` values** rather than a single value or boolean:
- **Failure-driven control flow:** Comparisons return their right-hand operand on success or *fail* (yielding 0 values), making chained comparisons like `1 < x < 10` fall out naturally without special syntax.
- **Alternation, suspension, and exhaustion:** `e1 | e2` concatenates result sequences; `suspend expr` in a procedure preserves its procedure frame (`Op_Psusp`) so failure downstream resumes it for the next value; `every expr` forces backtracking until exhaustion; bounded expressions delimit backtracking (analogous to Verse's `one{}` / Prolog's `once/1`); and **co-expressions** reify independent resumable evaluation stacks as first-class values.
- **Four-port compilation (Proebsting, PLDI 1997, DOI `10.1145/258916.258917`):** Proebsting demonstrated that goal-directed evaluation compiles directly without a heavy interpreter VM by translating every expression into a control-flow box with four labeled ports: **`start`** (enter forward), **`resume`** (backtrack for next result), **`succeed`** (yield value downstream), and **`fail`** (exhausted; jump to prior generator's `resume` port)—structurally isomorphic to Byrd's four-port Prolog box model and a direct lowering strategy for Mercury's `0..n` determinism lattice.

**Execution probe (`probe_p3.py`, Section 3B, `Basis: execution`):** Evaluating `every write((1 | 2 | 3) < (2 | 1))` explores all $3 \times 2 = 6$ pairs in left-to-right goal-directed order and yields `[2]` (only `1 < 2` succeeds, returning RHS `2`).

**FFI and state-backtracking boundaries:** Icon exhibits a sharp asymmetry invisible in procedure signatures: **control flow backtracks automatically, whereas ordinary variable assignment (`:=`) does NOT backtrack** (only explicit reversible assignment `<-` and reversible swap `<->` log undo entries). Across a C/Rust FFI boundary, native functions cannot execute `Op_Psusp` because their native stack frame cannot be frozen and resumed, restricting foreign callees to returning at most once (`det`/`semidet`) unless wrapped in a heap-allocated state machine.

---

### 4. Kernel `$vau` / Fexprs and R Lazy Non-Standard Evaluation: Why Caller-Scope Capture Defeats AOT Compilation

#### 4.1 Kernel `$vau` Operatives and Wand's Triviality Theorem

Basis: normative + source + documentation

In Lisp's early history, **fexprs** received their operands unevaluated and could inspect or evaluate them in the caller's environment; Pitman (1980) argued for replacing fexprs with compile-time macros to preserve compilation. **Kernel** (Shutt, WPI PhD Dissertation 2010) rehabilitates fexprs cleanly as **operatives** constructed by `$vau`—first-class combiners receiving both the unevaluated operand tree and the caller's dynamic environment—while ordinary functions (**applicatives**) are simply wrapped operatives (`wrap`).

Inspecting the C evaluator of `klisp` (`dbohdan/klisp@2b3a1cf774e0ab527a561e5d93dacbfdf0b545d1`, `src/keval.c` L85–128, L163–193) exposes the exact runtime dispatch in `do_combine_operands`:
- On `K_TAPPLICATIVE` (L86–120): copies `operands`, allocates `do_eval_ls` continuations to evaluate every argument right-to-left in `env`, then calls `tv2app(comb)->underlying` with the evaluated list.
- On `K_TOPERATIVE` (L122–124): immediately tail-calls `ktail_call_si(K, comb, operands, env, si)`, handing the callee both the **raw unevaluated `operands` syntax tree** and the **caller's live environment `env`**!

**Wand's Triviality Theorem (Wand, *The Theory of Fexprs is Trivial*, Lisp and Symbolic Computation 10(3), 1998, DOI `10.1023/A:1007743306850`):** Wand proved formally that in a calculus with unrestricted fexprs (capable of inspecting operand syntax), **contextual equivalence collapses to syntactic identity up to $\alpha$-renaming ($e_1 \cong e_2 \iff e_1 \equiv_\alpha e_2$)**. Because an unknown callee $f$ passed to `(f e)` might inspect `e`'s raw syntax tree rather than its value, *no* local compiler transformation—not constant folding (`1 + 1 -> 2`), not $\beta$-reduction, not dead-binding elimination, not inlining—is sound unless the compiler proves statically that the operator at that call site is a pure applicative (not an operative).

**Partial-evaluation recovery:** Braswell, Khan & Pande (*Practical Compilation of Fexprs Using Partial Evaluation*, `arXiv:2303.12254`, 2023) show that in a purely functional Lisp, AOT compilation of fexprs becomes practical by **partially evaluating away statically resolvable operatives at compile time**—turning fexprs into stage-polymorphic macros whenever the operator is known statically, while falling back to interpretation only when an operative flows dynamically at runtime.

#### 4.2 R Promises, Non-Standard Evaluation (`substitute`), and the Manual `PROTECT` C Interface

Basis: documentation + source + execution

GNU R (`wch/r-source@94152790dbd49be40c28c1819f92370fb7581f0a`, `doc/manual/R-lang.texi` L475–505) embeds fexpr-like syntax capture directly into every ordinary function call through **promise objects**:
- *"Promise objects are part of R's lazy evaluation mechanism. They contain three slots: a value, an expression, and an environment. When a function is called the arguments are matched and then each of the formal arguments is bound to a promise."* (`R-lang.texi` L479–486)
- *"The `substitute` function will extract the content of the expression slot. This allows the programmer to access either the value or the expression associated with the promise."* (`R-lang.texi` L495–497)
- *"There is generally no way in R code to check whether an object is a promise or not, nor is there a way to use R code to determine the environment of a promise."* (`R-lang.texi` L502–504)

Because every formal parameter in R is silently wrapped in a memoized promise carrying its AST expression and caller environment, R libraries (`lm(y ~ x)`, `dplyr::filter(df, col > 0)`) rely heavily on **Non-Standard Evaluation (NSE)**, creating severe AOT optimization and FFI obstacles empirically measured by Goel and Vitek (*On the Design, Implementation, and Use of Laziness in R*, OOPSLA 2019, DOI `10.1145/3360579`):
1. **Call-by-need forcing-order side-effect dependence:** Arguments are forced on first access inside the callee body, so swapping evaluation order changes observable side effects (`probe_p3.py` Section 3B: `force(a, b)` yields `(10, 10)` vs. `force(b, a)` yielding `(1, 10)` when `a` mutates `x <- 10` and `b` reads `x`).
2. **Equational collapse via `substitute()`:** `probe_p3.py` Section 3B confirms that `substitute(1 + 1)` returns `'1 + 1'` while `substitute(2)` returns `'2'` even though both force to `2`. Consequently, R JIT compilers must speculate that a callee neither calls `substitute()`/`match.call()` nor mutates environments reflectively, and deoptimize when NSE occurs.
3. **FFI double-entry-point tax and manual GC protection (`R-exts.texi` L12663–12689):** Foreign callers have no R AST expression or R environment to pass, forcing NSE libraries to maintain parallel standard-evaluation APIs. Worse, R's `.Call` C interface requires manual GC rooting via a stack-based **`PROTECT(SEXP)` / `UNPROTECT(n)`** protocol (`R-exts.texi` L12665–12674: *"The programmer is solely responsible for housekeeping the calls to `PROTECT`... R will warn about `'stack imbalance in .Call'` if the housekeeping is wrong"*). A missing `PROTECT` causes silent use-after-free bugs that trigger only when an intermediate R allocation invokes GC, while R error signaling uses C **`longjmp`**, bypassing C++ destructors and Rust `Drop` guards across any foreign stack frames on the stack.

---

### 5. Capability Mirrors, Intercession, and the Ahead-of-Time Closed World

Basis: normative + documentation + source

In mainstream object-oriented runtimes (Java `Object.getClass()`, Python `getattr`/`__dict__`, Ruby `instance_variable_get`), reflection is an **ambient method attached to every base object**, granting any code holding an object reference full introspective authority to bypass module encapsulation and forcing the runtime to retain complete metadata for every class and field.

#### 5.1 Bracha–Ungar Mirrors: Three Architectural Principles

Bracha and Ungar (*Mirrors: Design Principles for Meta-level Facilities of Object-Oriented Programming Languages*, OOPSLA 2004, DOI `10.1145/1028976.1029004`) replace ambient reflection with separate **mirror objects** governed by three principles:
1. **Encapsulation:** Meta-level facilities must hide their own implementation behind abstract interfaces (allowing local VM mirrors, remote debugger mirrors, and compile-time static mirrors to share one API without exposing object memory layouts).
2. **Stratification:** Meta-level functionality must be **strictly separated** from base-level functionality—base objects carry *no* reflective methods. Thus reflection is an explicit capability passed to subsystems that require it (implemented cleanly in Bracha's **Newspeak** platform, `newspeaklanguage/newspeak@84cc19da84aa7d4790dae155ea8f9a64c5855f87`, where modules receive mirror factories only as explicit platform arguments), and applications that omit mirrors can drop reflective metadata entirely.
3. **Ontological correspondence:** The mirror hierarchy must correspond directly to the language's own semantic structure (distinguishing mirrors on runtime instances/activations from mirrors on static declarations/classes).

**FFI marshaling implication (`Basis: derived`):** Cross-language serializers and FFI marshalers are the single largest consumers of runtime reflection (enumerating private fields to serialize or lay out structs). Handing a marshaler a **scoped capability mirror** covering only serializable types grants exact least-privilege access without exposing private invariants globally across the heap.

#### 5.2 The Closed-World AOT Pruning Tension: Dart `dart:mirrors` vs. GraalVM vs. Compile-Time Reflection

Stratification alone does not solve AOT dead-code elimination if a runtime mirror factory can reflect on *arbitrary* types by string name. Direct source evidence in the Dart SDK (`dart-lang/sdk@e1671c00019972a92e16247dc254ad3eaa48c2b6`, `sdk/lib/mirrors/mirrors.dart` L48–62) documents the resulting collision with AOT compilation and tree shaking:

```dart
/// ## Status: Deprecated
/// The `dart:mirrors` library is `@deprecated` and will be removed in a future
/// release. For details, see https://github.com/dart-lang/sdk/issues/44489.
/// This library is only supported by the Dart VM and only available on some platforms.
@deprecated
library dart.mirrors;
```

Ahead-of-time compilers (Dart AOT/Flutter, GraalVM Native Image for Java) require a closed-world call graph to prune unused classes and methods; GraalVM resolves this by demanding external JSON **reachability metadata** enumerating every reflectively accessed symbol. Meanwhile, mainstream systems languages are shifting introspection strictly to **compile time** (e.g., C++26's P2996 static reflection adopted June 2025) so reflective queries leave zero runtime metadata footprint.

#### 5.3 Intercession, Trustworthy Proxies, and Reflective Towers

Beyond read-only introspection, **intercession** overrides operational semantics: CLOS Metaobject Protocols (Kiczales et al. 1991) allow overriding dispatch and slot layout, JavaScript **Trustworthy Proxies** (Van Cutsem & Miller, DLS 2010 / ECOOP 2013) interpose on object traps while dynamically enforcing **invariant checks** (a proxy cannot lie about non-configurable/frozen properties or non-extensible prototypes), and reflective towers (Smith, POPL 1984) expose arbitrary levels of meta-interpreters—which **Collapsing Towers of Interpreters** (Amin & Rompf, POPL 2018) eliminate via multi-stage partial evaluation. Across an FFI boundary, unrestricted intercession invalidates static proofs unless the interface explicitly specifies which invariants remain un-interceptable.

---

### 6. Lafont Interaction Nets, Lamping Optimal Sharing, and HVM2's Atomic Reduction vs. Duplication Bookkeeping Cliffs

#### 6.1 Strong Confluence and Local Principal-Port Rewriting

Basis: normative + documentation + source

An **interaction net** (Lafont, POPL 1990, DOI `10.1145/96709.96718`) is an undirected graph of **agents** (nodes), each possessing exactly **one principal port** and $n \ge 0$ auxiliary ports, joined by linear wires (each port connects to exactly one wire endpoint). A rewrite rule fires **only** on an **active pair** where two principal ports meet directly, replacing those two nodes with a fixed local subgraph wired to their external auxiliary ports.

Because every node has at most one principal port, **no two active pairs can ever share a node**. Consequently, interaction nets satisfy the **diamond property (strong one-step confluence)**: if a net has a normal form, *every* reduction order reaches the exact same normal form in the **exact same number of interaction steps**. Lafont (*Interaction Combinators*, Information and Computation 137(1), 1997, DOI `10.1006/inco.1997.2643`) proved that just three agents—constructor ($\gamma$ / `CON`), duplicator ($\delta$ / `DUP`), and eraser ($\epsilon$ / `ERA`)—form a universal model of computation.

#### 6.2 HVM2 Architecture: 32-Bit Ports, 8×8 Interaction Table, and Lock-Free Atomic `link()`

Basis: source + documentation

Inspecting `HigherOrderCO/HVM2@654276018084b8f44a22b562dd68ab18583bfb5b` (`src/hvm.c` L48–116, L318–348, L811–841, L939–993, L1105–1107; `README.md` L48–52) reveals the concrete systems engineering of a parallel interaction-combinator runtime:

- **Compact word encoding (`src/hvm.c` L48–91):** A `Port` is a single 32-bit unsigned integer (`u32`) packing a 3-bit `Tag` and a 29-bit `Val`; a `Pair` is a 64-bit word (`u64`) packing two `Port`s. The 8 tags are `VAR (0x0)`, `REF (0x1)`, `ERA (0x2)`, `NUM (0x3)`, `CON (0x4)`, `DUP (0x5)`, `OPR (0x6)`, and `SWI (0x7)`. Native numbers (`U24`, `I24`, `F24`) are **24-bit** payloads inside a 29-bit `Numb` (`5`-bit type/operator tag + `24`-bit value).
- **The 8×8 interaction dispatch table (`src/hvm.c` L319–332):**

| Port A \ Port B | `VAR` | `REF` | `ERA` | `NUM` | `CON` | `DUP` | `OPR` | `SWI` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`VAR`** | `LINK` | `LINK` | `LINK` | `LINK` | `LINK` | `LINK` | `LINK` | `LINK` |
| **`REF`** | `LINK` | `VOID` | `VOID` | `VOID` | `CALL` | `CALL` | `CALL` | `CALL` |
| **`ERA`** | `LINK` | `VOID` | `VOID` | `VOID` | `ERAS` | `ERAS` | `ERAS` | `ERAS` |
| **`NUM`** | `LINK` | `VOID` | `VOID` | `VOID` | `ERAS` | `ERAS` | `OPER` | `SWIT` |
| **`CON`** | `LINK` | `CALL` | `ERAS` | `ERAS` | **`ANNI`** | **`COMM`** | `COMM` | `COMM` |
| **`DUP`** | `LINK` | `CALL` | `ERAS` | `ERAS` | **`COMM`** | **`ANNI`** | `COMM` | `COMM` |
| **`OPR`** | `LINK` | `CALL` | `ERAS` | `OPER` | `COMM` | `COMM` | `ANNI` | `COMM` |
| **`SWI`** | `LINK` | `CALL` | `ERAS` | `SWIT` | `COMM` | `COMM` | `COMM` | `ANNI` |

- **Lock-free atomic wire linking (`src/hvm.c` L811–841):** To link `A ~ B` concurrently across threads without global locks, `link()` normalizes so `A` is `VAR` (if both are non-`VAR` nodes, it pushes `(A, B)` to the thread's redex bag at L822). For `VAR A`, it executes an **atomic exchange** `Port A_ = vars_exchange(net, get_val(A), B);` (L831):
  - If `A_ == NONE` (L833): this thread arrived at wire `A` first, published `B`, yielded ownership of `B`, and returns immediately.
  - Otherwise (`A_ != NONE`, L838–839): the peer thread already published `A_`; this thread now exclusively owns *both* endpoints, deletes `VAR A` via `vars_take`, and loops to link `A_ ~ B`.
  - Note that `interact_anni` (L939–964) and `interact_comm` (L967–993) check `node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0` before taking nodes via `node_take`, retrying if a concurrent producer has not yet finished initializing a node's auxiliary pair.
- **Operational constraints documented upstream (`README.md` L48–52 & HVM2 paper):** HVM2's `README.md` notes that the CUDA backend has higher peak throughput but is *"less stable"* and recommends `gen-c` for production. HVM2's own paper notes ultra-eager reduction (infinite structures do not halt), baseline single-core throughput ~5× slower than GHC, and one numeric rule excluded from deterministic interaction counting to avoid non-deterministic counts.

#### 6.3 Optimal Sharing, Lamping's Oracle, the Non-Elementary Bookkeeping Cliff, and HVM's Soundness Restriction

Basis: normative + documentation + source + execution

Lévy (1980) defined **optimal $\lambda$-reduction** as never duplicating work inside a shared $\beta$-redex family. **Lamping** (POPL 1990, DOI `10.1145/96709.96736`; analyzed by Gonthier, Abadi & Lévy, POPL 1992, and Asperti & Guerrini 1998) realized optimal reduction via sharing graphs with fan (`DUP`) nodes plus dynamic **bookkeeping nodes** (**brackets** and **croissants**, collectively called **Lamping's oracle**) that track nesting levels so matching fans annihilate while distinct fans commute.

**The non-elementary complexity cliff:** Asperti and Mairson (*Parallel Beta Reduction Is Not Elementary Recursive*, POPL 1998; Information and Computation 170(1), 2001, DOI `10.1006/inco.2001.2869`) proved that the bookkeeping work hidden inside a single optimal parallel $\beta$-step **cannot be bounded by any elementary function** ($2^{2^{\cdot^{\cdot^n}}}$) in general $\lambda$-calculus—so optimal $\beta$-step count is *not* a valid asymptotic cost model! Conversely, Guerrini and Solieri (*Is the Optimal Implementation Inefficient? Elementarily Not*, FSCD 2017, DOI `10.4230/LIPIcs.FSCD.2017.17`) and Baillot, Coppola & Dal Lago (I&C 2011) show that inside stratified **Elementary / Light Affine Logic** fragments, bookkeeping overhead collapses dramatically and remains well-behaved.

**Why HVM1/HVM2 omit the oracle—and the exact silent-corruption hazard:**
Look back at HVM2's 8×8 table (`src/hvm.c` L327): **HVM2 has only ONE unlabeled `DUP` tag (`0x5`), so `DUP ~ DUP` ALWAYS triggers `ANNI` (annihilation)!**
- HVM1's `README.md` (`HigherOrderCO/HVM@7365a56c...`, L325–331) explicitly warns: *"HVM is an impementation of the bookkeeping-free version of the reduction algorithm proposed on TOIOFPL book, up to page 40. As such, it doesn't support some $\lambda$-terms, such as `(λx.(x x) λf.λx.(f (f x)))`."*
- Legacy Bend1's `docs/dups-and-sups.md` (`HigherOrderCO/Bend1@81445367...`, L33–60) documents the exact user-visible failure on higher-order duplication such as `List/map([1, 2, 3], lambda x: (+ x x))`: *"Due to how duplications are compiled, when two dups interact, they destructively interfere with each other. In this case the result doesn't follow the expected behavior (it's well defined at the HVM level, but is incorrect at a lambda-calculus level)... In this specific case, the runtime will catch it and generate an error, but at the moment that is not always the case."*
- **FFI and verification severity:** Passing an arbitrary higher-order closure across an FFI boundary into an oracle-free interaction-combinator runtime without a static stratification/linearity type check risks **silent wrong answers or non-termination** rather than a clean type error.
- **Ecosystem evolution (`HVM3`, `Bend`, `Vine`, `Inpla`):** `HigherOrderCO/HVM3` (`fba2e9c8...`, `README.md` L10–25) exposes labeled superpositions/duplications directly as the **Interaction Calculus** with affine lambdas, while `HigherOrderCO/Bend` (`0e2f38f7...`) pivoted to a dependent-typed proof language, and `VineLang/vine` (`cf0c3258...`, compiling to Ivy/IVM) and `inpla/inpla` (`864d5291...`) explore interaction-net languages with explicit imperative/functional interop.

#### 6.4 Executable Three-Tier Empirical Separation (`probe_p3_inet_eval.py`)

Basis: execution

Running our faithful simulator of HVM2's `VAR`-substitution linking protocol (`src/hvm.c` L811–841) and interaction rules on Church-numeral arithmetic applied to `(λy. y + 1)` and `NUM(0)` empirically separates **three distinct interaction-net regimes**:

| Term (Applied to `(+1) 0`) | Expected Value | Regime 1: HVM2 Unlabeled (`DUP ~ DUP -> ANNI`) | Regime 2: Static-Labeled (`DUP_a ~ DUP_b -> COMM` if `a != b`) | Root Cause Demonstrated |
| :--- | :--- | :--- | :--- | :--- |
| **`c2[2](c2[3])`** | `4` | **DIVERGES** (`halted=False`, `10000` steps, `comm=4997`, `oper=4995`) | **HALTS: `NUM(4)`** (`28` steps: `anni=14, comm=10, oper=4`) | Unlabeled `DUP ~ DUP` falsely annihilates distinct Church-numeral fans, creating an infinite feedback loop |
| **`c3[2](c2[3])`** | `8` | **DIVERGES** (`halted=False`, `10000` steps, `comm=6661`, `oper=3328`) | **HALTS: `NUM(8)`** (**`49` steps** across **all 20 random schedules!**) | Empirically verifies **Lafont strong confluence** (`{(49, 'NUM(8)')}` under 20 random schedules) when fan labels stay disjoint |
| **`(λx. x x) c2`** *(HVM1/HVM2 documented counterexample)* | `4` | **DIVERGES** (`halted=False`, `10000` steps, `comm=9994`, `left_nodes=19990`) | **STILL DIVERGES** (`halted=False`, `10000` steps, `anni=12, comm=4998`, `oper=4990`) | **Static labels alone fail!** `DUP_1` commutes through `c2`, cloning `DUP_2` into two copies that **both carry label `2`**; those clones then falsely annihilate! Dynamic Lamping level-shifting (Regime 3) is mathematically necessary for unrestricted self-application |

This execution proof sharpens a critical design boundary: merely adding static labels to `DUP` nodes fixes stratified non-self-duplicating terms (`c2(c2)`, `c3(c2)`), **but still fails silently on `(λx. x x) c2`**. Soundness for arbitrary higher-order $\lambda$-terms requires *either* Lamping's dynamic level-bookkeeping oracle (paying the Asperti–Mairson non-elementary worst-case tax) *or* a static type discipline (Elementary/Light Affine Logic) that rejects self-cloning of duplicating closures at compile time and across FFI boundaries.

## Boundaries

- **Native language toolchains not executed (`not examined`):** Native Factor, Kitten, Gforth, Unicon, klisp, GNU R, Dart VM, Newspeak, HVM2 C/CUDA, Vine, and Inpla binaries were not installed in the observation container. All execution results (`Basis: execution`) come from standalone Python 3.13 reference models matching the exact rules inspected in pinned upstream sources (`Basis: source`).
- **HVM2 / Bend performance benchmarks (`unknown` / reported as upstream claims only):** Throughput comparisons (such as HVM2's ~5× single-core gap vs. GHC, GPU speedup scaling, or Bend's type-checker benchmark claims in `HigherOrderCO/Bend` `README.md`) were not benchmarked locally and are recorded strictly as upstream project claims, not verified measurements.
- **Exact HVM2 atomic memory-ordering formalization (`unknown`):** While `HigherOrderCO/HVM2` `src/hvm.c` L811–841 implements lock-free `link()` using C11 `_Atomic` `vars_exchange`/`vars_take` and `node_load`/`node_take`, whether a formal weak-memory (C11 acquire/release/relaxed or GPU PTX) linearizability or model-checking proof exists for HVM2's C/CUDA runtime was not established by the inspected sources.
- **Forth 2012 standard full clause audit (`not examined`):** The full Forth 2012 specification text was not parsed line-by-line; interpretation vs. compilation semantics and ambiguous `STATE`-smart word behavior are summarized from secondary standards knowledge and Gforth documentation (`Basis: documentation`).
- **Compile-time reflection and proxy-membrane full-abstraction proofs (`not examined`):** Detailed C++26 P2996 compile-time reflection semantics and formal full-abstraction / object-identity theorems for cross-language proxy membranes are outside the primary focus of this report (which covers runtime capability mirrors and AOT pruning limits).
- **Kitten permission inference principality (`unknown`):** While `evincarofautumn/kitten` `common.ktn` and `lib/Kitten/Infer.hs` confirm row-polymorphic stack and permission checking, whether Kitten's full type-and-permission inference algorithm possesses a mechanized soundness or principal-typing proof was not established from the inspected files.
- **Overclaiming boundary (`known not to apply`):** Strong confluence of Lafont interaction nets (`Basis: normative + execution`) is **known not to apply** automatically when arbitrary stateful foreign agents or non-local side effects are added without verifying local diamond preservation. Similarly, adding static labels to `DUP` nodes is **known not to restore soundness** for general untyped/System-F $\lambda$-terms that clone duplicating closures (empirically refuted by `(λx. x x) c2` in `probe_p3_inet_eval.py`).

## Evidence

### Pinned Upstream Repositories and Source Citations

1. **`factor/factor`** at commit `f05a4e9d49d17881c65f9b21e05095d0ff3adc50`:
   - `basis/stack-checker/stack-checker-docs.factor`: L6–17 (`inference-simple`), L18–75 (`inference-combinators`: literal/`curry`/`compose`, `inline`, fixed monomorphic `apply-one` L42, *"Row-polymorphic quotation parameters still require inlining"* L43, `call(` escape hatch L54), L69–81 (`inference-branches`: equal height delta, `[ [ + ] [ drop ] if ]` L73), L76–107 (`inference-recursive-combinators`: `inline recursive`, no passing quotations on data stack through recursive calls L91–94).
   - `basis/stack-checker/errors/errors.factor`: L6–36 (`unknown-macro-input`, `bad-macro-input`, `unbalanced-branches-error`, `undeclared-recursion-error`, `unbalanced-recursion-error`, `diverging-recursion-error`).
2. **`evincarofautumn/kitten`** at commit `2bbc264d7f05c4a7d7b35d06773d1ab2f0623193`:
   - `common.ktn`: L9–20 (`define call<R..., S...> (R..., (R... -> S...) -> S...)`, modus ponens documentation), L435–460 (`trait / <T> (T, T -> T +Fail)`, `trait % <T> (T, T -> T +Fail)`).
   - `lib/Kitten/Infer.hs`: L1–75 (Hindley-Milner stack/permission type inference module structure).
3. **`forthy42/gforth`** at commit `15375fb0469d6590980adc2bf4cbddb241a671a6`: `README.md`.
4. **`uniconproject/unicon`** at commit `d3df4185f1e262508bd5beda1e69bfcdac251bf9`:
   - `src/runtime/interp.r`: L1681–1699 (`Op_Psusp` procedure suspension), L1907–1925 (`Op_Efail` expression failure and generator resumption dispatch).
5. **`dbohdan/klisp`** at commit `2b3a1cf774e0ab527a561e5d93dacbfdf0b545d1`:
   - `src/keval.c`: L26–69 (`do_eval_ls` right-to-left argument evaluation), L71–129 (`do_combine_operands` dispatching `K_TAPPLICATIVE` vs. `K_TOPERATIVE` passing unevaluated `operands` + `env`), L163–193 (`keval_ofn`).
6. **`wch/r-source`** at commit `94152790dbd49be40c28c1819f92370fb7581f0a`:
   - `doc/manual/R-lang.texi`: L475–505 (`@node Promise objects`: 3 slots value/expression/environment, `substitute()`, no in-language promise introspection).
   - `doc/manual/R-exts.texi`: L12663–12689 (`PROTECT`/`UNPROTECT` stack discipline, `"stack imbalance in .Call"`).
7. **`dart-lang/sdk`** at commit `e1671c00019972a92e16247dc254ad3eaa48c2b6`:
   - `sdk/lib/mirrors/mirrors.dart`: L48–62 (`@deprecated library dart.mirrors`, issue 44489, VM-only platform restriction).
8. **`newspeaklanguage/newspeak`** at commit `84cc19da84aa7d4790dae155ea8f9a64c5855f87`: `README.md`.
9. **`HigherOrderCO/HVM`** (HVM1) at commit `7365a56cca56a5853c979755891cb86aa343c42d`:
   - `README.md`: L323–345 (bookkeeping-free TOIOFPL up to page 40; explicit unsupported term `(λx.(x x) λf.λx.(f (f x)))`).
10. **`HigherOrderCO/HVM2`** at commit `654276018084b8f44a22b562dd68ab18583bfb5b`:
    - `README.md`: L40–52 (`gen-c` recommended for production; CUDA less stable).
    - `src/hvm.c`: L48–116 (`Port` 32-bit 3-bit Tag + 29-bit Val, 8 tags `VAR..SWI`, 24-bit `U24`/`I24`/`F24`), L318–348 (`get_rule` 8×8 table with single unlabeled `DUP ~ DUP -> ANNI`), L811–841 (lock-free atomic `link()` using `vars_exchange`/`vars_take`), L939–993 (`interact_anni`, `interact_comm`), L1105–1107 (interaction dispatch).
11. **`HigherOrderCO/Bend1`** at commit `814453670d0e0d6777c1313c972764dba0491b7f`:
    - `docs/dups-and-sups.md`: L33–60 (destructive interference of two `dup`s; `List/map([1, 2, 3], lambda x: (+ x x))` example; admission that runtime does not always catch violations).
12. **`HigherOrderCO/HVM3`** (`fba2e9c82faf6e2f019c9ecea94c32f19a8b7820`), **`HigherOrderCO/Bend`** (`0e2f38f759cc830849e489307f3d256a7d148288`), **`VineLang/vine`** (`cf0c325834d5bf4c8d43aa36f7fb76faf2496988`), **`inpla/inpla`** (`864d529191ac83b776d301839c6b485c432e2725`): `README.md`.

### Peer-Reviewed Literature Verified

- Bell (CACM 1973); Baker (ACM Computer Architecture News, 1994); Kerby (2002); Pestov, Ehrenberg & Groff (2010), *Factor: A Dynamic Stack-based Programming Language*, DLS 2010, DOI `10.1145/1869631.1869637`.
- Morrisett, Crary, Glew & Walker (JFP 2002); Haas, Rossberg, Schuff, Titzer et al. (PLDI 2017); Bernardo et al. (Mi-Cho-Coq, FMBC 2019).
- Griswold & Griswold (1986); Proebsting (1997), *Simple Translation of Goal-Directed Evaluation*, PLDI 1997, DOI `10.1145/258916.258917`.
- Pitman (1980); Wand (1998), *The Theory of Fexprs is Trivial*, LASC 10(3), pp. 189–199, DOI `10.1023/A:1007743306850`; Shutt (WPI PhD Dissertation, 2010); Braswell, Khan & Pande (2023), *Practical Compilation of Fexprs Using Partial Evaluation*, `arXiv:2303.12254`.
- Goel & Vitek (2019), *On the Design, Implementation, and Use of Laziness in R*, PACMPL 3(OOPSLA), DOI `10.1145/3360579`.
- Bracha & Ungar (2004), *Mirrors: Design Principles for Meta-level Facilities of Object-Oriented Programming Languages*, OOPSLA 2004, DOI `10.1145/1028976.1029004`; Kiczales et al. (1991); Van Cutsem & Miller (DLS 2010; ECOOP 2013); Smith (POPL 1984); Amin & Rompf (POPL 2018).
- Lafont (1990), *Interaction Nets*, POPL 1990, DOI `10.1145/96709.96718`; Lafont (1997), *Interaction Combinators*, Information and Computation 137(1), pp. 69–101, DOI `10.1006/inco.1997.2643`.
- Lévy (1980); Lamping (1990), *An Algorithm for Optimal Lambda Calculus Reduction*, POPL 1990, DOI `10.1145/96709.96736`; Gonthier, Abadi & Lévy (POPL 1992); Asperti & Guerrini (1998); Asperti & Mairson (POPL 1998; Information and Computation 170(1), 2001), DOI `10.1006/inco.2001.2869`; Baillot, Coppola & Dal Lago (I&C 209(2), 2011); Guerrini & Solieri (2017), *Is the Optimal Implementation Inefficient? Elementarily Not*, FSCD 2017, DOI `10.4230/LIPIcs.FSCD.2017.17`.

### Executable Reference Probe Outputs (`Basis: execution`)

Observed on Linux x86_64 with Python 3.13 (`2026-11-19`):

```text
=== 3A. Row-Polymorphic Stack Effect & Linear Permission Checker ===
  Composed (dup /): ('Push', ('RowVar', 'R3'), ('Con', 'Int')) -> ('Push', ('RowVar', 'R3'), ('Con', 'Int')) perms: ['Fail']
  Balanced branch [ + ] [ drop ] if unifies to: ('Push', ('Push', ('RowVar', 'R1'), ('Con', 'Int')), ('Con', 'Int')) -> ('Push', ('RowVar', 'R1'), ('Con', 'Int'))
  Unbalanced branch [ + ] [ dup ] if rejected: occurs check: R1 in ('Push', ('Push', ('RowVar', 'R1'), ('Con', 'Int')), ('Con', 'Int'))

=== 3B. Icon Goal-Directed 4-Port Evaluation & R Promise / Fexpr NSE ===
  Icon `every write((1|2|3) < (2|1))` yields: [2]
  R promise forcing-order sensitivity: force(a,b)=(10, 10) vs force(b,a)=(1, 10)
  R substitute() / Kernel $vau breaks beta/const-fold: substitute(1+1)='1 + 1' != substitute(2)='2' (values both 2)

=== 3C. HVM2 Unlabeled vs Static-Labeled Interaction Combinator Simulator (NUM/INC Readout) ===
--- c2(c2) (+1) 0  [expected 4] ---
  HVM2 unlabeled (DUP~DUP->ANNI)   | halted=False | steps=10000 (anni= 8, comm=4997, oper=4995) | result=NON_NUM(('VAR', 24), left_nodes=4)
  Static-labeled (DUP_a~DUP_b)     | halted=True  | steps=   28 (anni=14, comm=  10, oper= 4) | result=NUM(4)

--- c3(c2) (+1) 0  [expected 8] ---
  HVM2 unlabeled (DUP~DUP->ANNI)   | halted=False | steps=10000 (anni=11, comm=6661, oper=3328) | result=NON_NUM(('VAR', 27), left_nodes=3334)
  Static-labeled (DUP_a~DUP_b)     | halted=True  | steps=   49 (anni=21, comm=  20, oper= 8) | result=NUM(8)

--- (lam x. x x) c2 (+1) 0 [expected 4] ---
  HVM2 unlabeled (DUP~DUP->ANNI)   | halted=False | steps=10000 (anni= 6, comm=9994, oper= 0) | result=NON_NUM(('NODE', 29), left_nodes=19990)
  Static-labeled (DUP_a~DUP_b)     | halted=False | steps=10000 (anni=12, comm=4998, oper=4990) | result=NON_NUM(('VAR', 42), left_nodes=5)

Strong confluence across 20 random schedules on c3(c2) (+1) 0: {(49, 'NUM(8)')}
```

## Revalidation

1. **Diff pinned runtime and checker invariants against newer revisions:**
   - **Factor:** Check `basis/stack-checker/stack-checker-docs.factor` (`inference-combinators`) to see if row-polymorphic quotations have gained non-inline support.
   - **HVM2 / HVM3:** Inspect `src/hvm.c` `get_rule` table in `HigherOrderCO/HVM2` (confirming `table[DUP][DUP] == ANNI` and single unlabeled `DUP` tag) and `IC.md` / `HVM.md` in `HigherOrderCO/HVM3` for labeled duplication and stratification rules.
   - **Dart SDK / R:** Check `sdk/lib/mirrors/mirrors.dart` (`@deprecated` removal status) and `doc/manual/R-lang.texi` (`Promise objects`) / `R-exts.texi` (`PROTECT`).
2. **Re-run the self-contained interaction-combinator strong-confluence and duplication-interference probe:**

```bash
python3 - <<'EOF'
import random
class Net:
    def __init__(self, labeled):
        self.labeled, self.nodes, self.vars, self.redexes = labeled, {}, {}, []
        self.nid = self.vid = 1; self.root = None; self.steps = 0
    def nv(self): v = self.vid; self.vid += 1; self.vars[v] = None; return ("V", v)
    def nn(self, t, m, p1=None, p2=None):
        i = self.nid; self.nid += 1; self.nodes[i] = (t, m, p1, p2); return ("N", i)
    def ent(self, p):
        while p and p[0] == "V" and self.vars.get(p[1]) is not None: p = self.vars[p[1]]
        return p
    def link(self, a, b):
        while True:
            if a[0] != "V" and b[0] == "V": a, b = b, a
            if a[0] == "R": self.root = self.ent(b); return
            if b[0] == "R": self.root = self.ent(a); return
            if a[0] != "V": self.redexes.append((a, b)); return
            b = self.ent(b); prev = self.vars[a[1]]; self.vars[a[1]] = b
            if prev is None: return
            del self.vars[a[1]]; a = prev
    def run(self, seed=0, lim=2000):
        rng = random.Random(seed); ordm = {"NUM":0,"INC":1,"CON":2,"DUP":3}
        while self.redexes and self.steps < lim:
            pa, pb = self.redexes.pop(rng.randrange(len(self.redexes)))
            pa, pb = self.ent(pa), self.ent(pb)
            if pa[0] != "N" or pb[0] != "N": self.link(pa, pb); continue
            ta, ma, a1, a2 = self.nodes.pop(pa[1]); tb, mb, b1, b2 = self.nodes.pop(pb[1])
            if ordm[ta] > ordm[tb]: ta, ma, a1, a2, tb, mb, b1, b2 = tb, mb, b1, b2, ta, ma, a1, a2
            self.steps += 1
            if ta == "NUM" and tb == "INC": self.link(b1, self.nn("NUM", ma + 1))
            elif ta == "NUM": self.link(b1, self.nn("NUM", ma)); self.link(b2, self.nn("NUM", ma))
            elif ta == "INC" and tb == "DUP":
                v1, v2 = self.nv(), self.nv()
                self.link(a1, self.nn("DUP", mb, v1, v2)); self.link(b1, self.nn("INC", 0, v1)); self.link(b2, self.nn("INC", 0, v2))
            elif ta == tb and (not self.labeled or ta != "DUP" or ma == mb):
                self.link(a1, b1); self.link(a2, b2)
            else:
                v1, v2, v3, v4 = self.nv(), self.nv(), self.nv(), self.nv()
                self.link(self.nn(tb, mb, v1, v2), a1); self.link(self.nn(tb, mb, v3, v4), a2)
                self.link(self.nn(ta, ma, v1, v3), b1); self.link(self.nn(ta, ma, v2, v4), b2)
        return not self.redexes

def church(net, n, lbl):
    vf, vx = net.nv(), net.nv(); fs, cur = [], vf
    for _ in range(n - 1):
        a, b = net.nv(), net.nv(); net.link(cur, net.nn("DUP", lbl, a, b)); fs.append(a); cur = b
    fs.append(cur); val = vx
    for f in reversed(fs):
        r = net.nv(); net.link(f, net.nn("CON", 0, val, r)); val = r
    return net.nn("CON", 0, vf, net.nn("CON", 0, vx, val))

def eval_term(self_app, labeled, seed=0):
    net = Net(labeled)
    if not self_app:
        t = net.nv(); net.link(church(net, 2, 2), net.nn("CON", 0, church(net, 2, 3), t))
    else:
        vx, x1, x2, rxx = net.nv(), net.nv(), net.nv(), net.nv()
        net.link(vx, net.nn("DUP", 1, x1, x2)); net.link(x1, net.nn("CON", 0, x2, rxx))
        t = net.nv(); net.link(net.nn("CON", 0, vx, rxx), net.nn("CON", 0, church(net, 2, 2), t))
    vi, vo = net.nv(), net.nv(); net.link(vi, net.nn("INC", 0, vo))
    r1, r2 = net.nv(), net.nv()
    net.link(t, net.nn("CON", 0, net.nn("CON", 0, vi, vo), r1))
    net.link(r1, net.nn("CON", 0, net.nn("NUM", 0), r2)); net.link(("R", 0), r2)
    ok = net.run(seed); r = net.ent(net.root)
    return ok, net.steps, (net.nodes[r[1]][1] if ok and r[0]=="N" and net.nodes[r[1]][0]=="NUM" else None)

assert {eval_term(False, True, s) for s in range(10)} == {(True, 28, 4)}
assert eval_term(False, False)[0] is False
assert eval_term(True, True)[0] is False
print("PASS: 3-tier interaction-combinator separation and strong confluence verified")
EOF
```

3. **Live native runtime revalidation (when Factor, R, and HVM2 binaries are available):**
   - Run `(λx.(x x) λf.λx.(f (f x)))` on a pinned HVM2 release (`run`, `run-c`, `run-cu`) to confirm whether each backend diverges, returns a wrong term, or raises an error.
   - Run `[ [ + ] [ dup ] if ] infer.` in Factor to confirm `unbalanced-branches-error`, and run `f <- function(a, b) { y <- b; x <- a; c(x, y) }; z <- 1; f({z <- 10; z}, z)` in `Rscript` to verify promise forcing-order sensitivity.
