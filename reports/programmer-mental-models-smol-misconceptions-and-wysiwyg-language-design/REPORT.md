# Empirical Programmer Mental Models, SMoL Misinterpreters, Visual Semantic Projections, and WYSIWYG Language Design

## Summary

Human programmers—and LLM code/proof generators—reason about programs through an internal **notional machine** rather than the optimizing compiler's lowered IR. Whenever language syntax hides state sharing, control-flow divergence, or compiler undefined behavior behind concise notation, human mental models systematically fracture into predictable, reproducible failure classes:

1. **Empirical Misconception Taxonomy & Executable Misinterpreters (`SMoL` / `SMoL Tutor`, OOPSLA 2024):** Lu & Krishnamurthi formalize the shared 8-feature semantic core across Python, JavaScript, Java, ML, and Lisp (`shriram/smol`) alongside **15 named behavioral misconceptions** implemented as executable **misinterpreters**. Cross-institutional deployments (University 1, University 2 $p = 2.013 \times 10^{-7}$, and $N=597$ public self-learners $p < 2.2 \times 10^{-16}$) show massive misconception rates even among experienced learners: **67%** believe `defvar y x` recursively copies mutable vectors (`DefsCopyStructs`), **56%–57%** expect forward variable definitions to evaluate lazily (`Lazy‡`), **34%** fail `let`-over-`lambda` closure state (`make-counter`), **24%** think structs store variable references (`StructByRef`), and **31%** assume same-named function parameters alias caller variables (`DefByRef`/`FlatEnv`). Loop-variable capture over mutable bindings drove breaking industrial language changes in both C# 5.0 and Go 1.22.
2. **Bridging Static Types & Runtime UB (`Aquascope`, `RustViz`, `Cerberus`):** Crichton, Gray, and Krishnamurthi's `Ownership Inventory` (`OOPSLA 2023`, `cognitive-engineering-lab/aquascope`) reveals that Rust learners fail primarily at connecting *static* borrow rejections to *dynamic* memory unsafety (`58%` accuracy on defined vs. UB; `44%` on how references trigger UB; `47%` on multi-layer `Box<&Box<i32>>` dereferencing). Projecting Polonius constraints onto a 4-bit **path permissions lattice (`R/W/O/F`)** paired with concrete heap/stack diagrams raised Inventory accuracy by **+9%** ($48\% \to 57\%$, $N=177 \to 165$, Cohen's $d=0.56$, $p < 0.001$). Crucially, `aquascope` §5.1.3 found that omitting move invalidation from runtime diagrams (merely because a Rust move is physically a bitwise `memcpy`) broke reader comprehension until invalidated bindings were explicitly visualized. In C, Memarian et al.'s `Cerberus` surveys (`PLDI 2016` / `POPL 2019`, `rems-project/cerberus`) establish an analogous mismatch between systems practitioners' flat-memory mental models and ISO C11/LLVM pointer provenance and padding rules.
3. **WYSIWYG / Anti-Magic Grammar & Type Design (`Zig`, `Austral`):** Languages can eliminate invisible control-flow and precedence traps structurally at parse/type time: `ziglang/zig` (`lib/std/zig/Parse.zig:1545–1645`) ranks bitwise `&`/`^`/`|` (`prec = 40`) above comparisons (`prec = 30, Assoc.none`), bans chained `a == b == c` (`chained_comparison_operators`), rejects `&&` (`invalid_ampersand_ampersand`), flags asymmetric operator spacing (`mismatched_binary_op_whitespace`), separates trapping arithmetic (`+`) from explicit wrapping (`+%`) and saturating (`+|`), and surfaces control-flow exits via `try`/`catch`/`orelse`/`defer`. `austral/austral` (`LinearityCheck.ml`) pushes syntactic-semantic isomorphism further via strict "anti-features"—banning exceptions, destructors, implicit conversions, shadowing, macros, type inference, and operator precedence while enforcing linear resource consumption at compile time.
4. **Differential Intent Checking & Anti-Reward-Hacking Audits:** Pairing a human-scale mental-model oracle ($\mathbb{Z}$ integers, strict traps, zero UB exploitation) with an optimizing compiler (`Miri`, LLVM) or verifier immediately flags intent-breaking lowerings (such as UB-assuming `x + 1 > x -> true` folding). In recent large-scale LLM verification studies (Anthropic Frontier Red Team & Theorem, Oct 2026), differential testing a Verus-verified Rust Python-subset interpreter over **1.7 million** random programs yielded **99.95%** CPython parity while isolating spec corner cases, and behavioral-equivalence auditing (Footnote 06) became essential to block autonomous agents from "reward hacking" no-crash specs by emitting trivial early-exit stubs.

---

## Applicability

This report informs language designers, compiler diagnostic/IDE visualization engineers, verification specification authors, and differential-testing builders aligning formal execution with human mental models.

Examined subjects cover seven complementary pillars (exact SHAs, DOIs, and primary URLs in `REPORT.json` and `## Evidence`):

1. **Cross-Language Semantic Core & Misconception Benchmarks (`shriram/smol`, `brownplt/smol-translator`, Lu & Krishnamurthi `OOPSLA 2024`):** Applies to `shriram/smol` (`858d1b46...`), `brownplt/smol-translator` (`1ab5cfa7...`), and empirical SMoL Tutor studies (`10.1145/3649823`). Findings cover languages sharing eager, lexically scoped, mutable-variable + heap-reference + closure semantics (Python, JS, Java, C#, Go, Scheme/Racket); languages with pure immutability (Haskell) or dynamic scoping deviate systematically.
2. **Rust Static-Dynamic Ownership Visualization (`cognitive-engineering-lab/aquascope`, `rustviz/rustviz`, `hazelgrove/hazel`):** Applies to `aquascope` (`f2d0a060...`, `OOPSLA 2023`, `arXiv:2309.04134v1`), `rustviz` (`b8c05e06...`, `VL/HCC 2022` v1 DSL vs. v2 `rustc` HIR/MIR plugin), and `hazel` (`13ba5d13...`, `POPL 2019`). Note that `aquascope` requires a pinned `nightly-2024-12-15` `rustc_private` + `miri` setup (`README.md`), whereas `rustviz` v2 targets `nightly-2026-05-01` and emits static interactive SVGs.
3. **C Programmer Survey & Provenance Mental Models (`rems-project/cerberus`):** Applies to `cerberus` (`e29a8ec9...`) and Memarian et al. (`10.1145/2908080.2908081`, `10.1145/3290380`), characterizing ISO C11/C17 UB vs. *de facto* systems expectations (PNVI-ae-udi).
4. **WYSIWYG Systems Languages (`ziglang/zig`, `austral/austral`):** Applies to `ziglang/zig` (`738d2be9d6b6ef3ff3559130c05159ef53336224`, `lib/std/zig/Parse.zig`) and `austral/austral` (`0962d2a8a5d77f7daacd7f696819520733f4897d`, `lib/LinearityCheck.ml`, `lib/Stages.ml`). Exact precedence and linearity observations come from direct compiler source inspection.
5. **Differential Reference Execution & LLM Verification Behavior (`rust-lang/miri`, Anthropic Oct 2026):** Applies to `rust-lang/miri` (`93d13704...`) and Anthropic & Theorem's Oct 2026 formal verification study (`https://www.anthropic.com/research/formal-verification`).
6. **Standalone Micro-Probe (`probe_mental_models.py`):** Verified locally under Python 3 (`Basis: execution`), executing all 7 SMoL misinterpreters, C-vs-Zig precedence & wrapping `i8` traps, differential UB intent checking, and patch reward-hacking detection.

---

## Findings

### 1. The Standard Model of Languages (`SMoL`) and Formalizing Misconceptions as Misinterpreters

#### 1.1 The 8-Feature `SMoL` Core and Cross-Language Persistence

`Basis: normative + source + documentation`

In `shriram/smol` (`858d1b461924a7a9a37e9119faf191304dda5835`, `892` lines across `fun/semantics.rkt`, `state/semantics.rkt`, `hof/semantics.rkt`, `dyn-scope-is-bad/semantics.rkt`) and Lu & Krishnamurthi (`OOPSLA 2024`, DOI `10.1145/3649823`, `smol_oopsla24.txt:45–101`), the **Standard Model of Languages (`SMoL`)** distills the shared runtime architecture underlying Python, JavaScript, Java, C#, Ruby, Go, Scheme, and ML:
1. Lexical scope, 2. Nested scope blocks, 3. Eager evaluation, 4. Left-to-right sequential execution per thread, 5. Mutable first-order variable bindings (`set!`), 6. Mutable heap-allocated compound structures (`mvec`/`vec-set!`, `mpair`/`set-left!`), 7. First-class closures capturing lexical environments, and 8. Automatic memory management (GC).

Despite sharing this core across mainstream curricula, industrial and academic programmers persistently fail on short 4–7 line snippets. Loop-variable capture over shared mutable loop bindings (`for i in range(10): lambda: print(i)` printing `9` ten times) proved so destructive in production that C# 5.0 changed `foreach` semantics (`smol_oopsla24.txt:135`) and Go 1.22 altered `for` loop scoping (`smol_oopsla24.txt:137`).

#### 1.2 Complete Empirical Misconception Catalog and Misinterpreter Verification

`Basis: documentation + execution`

To eliminate "expert blind spots" when classifying wrong answers across 89 diagnostic tasks (`smol_oopsla24.txt:1381–1456`), Lu & Krishnamurthi encoded each misconception as an executable **misinterpreter** (a minimal definitional interpreter differing from canonical SMoL by one exact semantic rule). Running our standalone Python implementation (`probe_mental_models.py` Part 1) confirms that **7 distinct misinterpreters cleanly separate on 7 minimal benchmarks**. Combining Lu & Krishnamurthi's empirical tables (`smol_oopsla24.txt:905–1025, 1465–1850`, Tables 4, 6, 7, 8) yields:

| Misconception ID | Erroneous Mental-Model Rule | Representative Diagnostic Pattern | Observed Error Share | Canonical SMoL vs. Misinterpreter Output |
|---|---|---|---|---|
| **`DefsCopyStructs`** | `defvar y x` recursively clones mutable structs rather than copying references | `(defvar x (mvec 100)) (defvar y x) (vec-set! x 0 200) y` | **67%** (`#(100)`) | `#(200)` vs. `#(100)` |
| **`Lazy‡`** | Variable RHS expressions evaluate lazily on read rather than eagerly at definition | `(defvar y (+ x 2)) (defvar x 1) x y` | **56%–57%** (`1 3`) | `ERROR` vs. `1 3` |
| **Shared vs. Fresh Closure Env** | Calling `make-counter` twice shares one global `let` frame (or resets per call) | `f := make-counter(); g := make-counter(); f(); g(); f(); f(); g()` | **34%** (`1 1 1 1 1`) | `1 1 2 3 2` vs. `1 1 1 1 1` |
| **`StructByRef`** | Storing variable `x` inside `(mvec 1 2 x)` stores a pointer to variable `x`'s cell | `(defvar x 3) (defvar v (mvec 1 2 x)) (set! x 4) v` | **24%** (`#(1 2 4)`) | `#(1 2 3)` vs. `#(1 2 4)` |
| **`IsolatedFun`** | Functions cannot read free variables in outer lexical scopes | `(defvar y 1) (deffun (addy x) (+ x y)) (addy 2)` | **23%** (`error`) | `3` vs. `ERROR` |
| **`DefOrSet`** | `set!` creates a new binding if unbound (blurring Python-style `=` definition/assignment) | `(set! foobar 2) foobar` | **15%** (`2`) | `ERROR` vs. `2` |
| **`NoCircularity`** | Data structures cannot hold cyclic self-references | `(defvar x (mvec 1 0 2)) (vec-set! x 1 x) (vec-len x)` | **14%** (`error`, +9% OOM/∞) | `3` vs. `ERROR` |
| **`DefByRef`** | `defvar y x` aliases `y` to `x`'s mutable variable box | `(defvar x 12) (defvar y x) (set! x 0) x y` | **12%** (`0 0`) | `12` vs. `0` (for `y`) |
| **`FunNotVal`** | Functions are second-class syntactic procedures, not passable values | `(twice double 1)` | **11%** (`error`) | `4` vs. `ERROR` |
| **`DeepClosure`** | Closures snapshot free variable *values* at creation rather than closing over bindings | `(defvar x 1) (defvar f (lambda (y) (+ x y))) (set! x 2) (f x)` | **10%** (21% in Quiz 3 `lambda`, 10% in `deffun`) | `4` vs. `3` |
| **`CallByRef`** | Passing `x` to `(f y)` aliases formal parameter `y` to caller's `x` (jumps to **31%** if both named `x`!) | `(defvar x 12) (deffun (f y) (set! y 0) x) (f x)` | **10%** (31% same-name) | `12` vs. `0` |
| **`CallsCopyStructs`** | Passing mutable struct `x` copies struct contents by value | `(defvar x (mvec 1 0)) (deffun (f y) (vec-set! y 0 173)) (f x) x` | **10%** (`#(1 0)`) | `#(173 0)` vs. `#(1 0)` |
| **`NestedDef‡`** | Sequential definitions open nested blocks rather than sharing one mutually visible block | `(defvar x 1) (deffun (main) (deffun (get-x) x) (defvar x 2) (get-x))` | **8%** (`1`) | `2` vs. `1` |
| **`StructsCopyStructs`** | Mutating a vector to store another vector clones it instead of aliasing | `(defvar x (mvec 2 3)) (set-right! x x) (set-left! x x) x` | **6%** (+24% partial copy) | Cyclic vs. deep clone |
| **`FlatEnv`** | One global mutable environment instead of lexical frames (dynamic-scope variant) | `(deffun (addy x) (defvar y 200) (+ x y)) (+ (addy 2) y)` | **4%** (`402`) | `ERROR` vs. `402` |

**Generalizability & Tutoring Insight:** Cross-population rankings strongly correlate between University 1, University 2 ($p = 2.013 \times 10^{-7}$), and $N=597$ public self-learners ($p < 2.2 \times 10^{-16}$, `smol_oopsla24.txt:2161–2193`). Logistic regression on SMoL Tutor interventions (`smol_oopsla24.txt:1985–1996`) decreased errors significantly for 7/11 misconceptions, **except `DefOrSet` and `FunNotVal` actually worsened**, exposing how shared surface syntax (`=` for both bind and assign, or `def` vs `lambda`) directly induces mental-model conflation.

---

### 2. Systems-Level Mental-Model Chasms: Rust Ownership (`Aquascope`) & De Facto C (`Cerberus`)

#### 2.1 Rust's Static-Dynamic Gap and the Path Permissions Lattice (`Aquascope`)

`Basis: normative + source + documentation`

Crichton, Gray, and Krishnamurthi (`OOPSLA 2023`, `10.1145/3622841`, `arXiv:2309.04134v1`; `cognitive-engineering-lab/aquascope` @ `f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`, `12,566` lines) show that Rust learners struggle less with spotting simple move errors (`84%` accuracy) or overlapping borrows (`87%`) than with **connecting static type rejections to dynamic memory safety**:

- **Empirical Diagnostic Weaknesses (`aquascope_oopsla23.txt:2505–2547, 2767–2781`, Table 2):** Learners scored only **58%** distinguishing defined vs. undefined behavior, **44%** explaining *how* invalid references cause UB, **64%** distinguishing stack vs. heap allocation, and **47%** counting required dereferences on `Box<&Box<i32>>` (even immediately after reading a worked `&Box<i32>` example!).
- **Permissions Model (`crates/aquascope/src/analysis/permissions/{context.rs,output.rs,flow.rs}`):** Rather than exposing compiler internals (Polonius `Origin` / `Loan` outlives constraints), `Aquascope` translates Polonius `BodyWithBorrowckFacts` via Datafrog rules (`output.rs:37–155`) into **four concrete path permissions (`Read`, `Write`, `Own`, plus `Flow` lifetime flow via `RegionFlows` in `flow.rs:170–379`)** at every MIR `Point`. Every expression's `boundaries` check visually contrasts *Expected Permissions* against *Actual Permissions*, while `stepper` (`hir_steps.rs` / `segmented_mir.rs`) shows line-by-line permission diffs alongside Miri's concrete stack/heap frames (`interpreter/step.rs`).
- **Measured Effect (`aquascope_oopsla23.txt:2617–2813`, Table 3):** Deploying this permissions-based pedagogy inside *The Rust Programming Language* experiment raised `Ownership Inventory` scores from **48%** ($\sigma=16\%$, $N=177$) to **57%** ($\sigma=15\%$, $N=165$), Cohen's **$d = 0.56$ ($p < 0.001$)**—exceeding Hattie's $d = 0.40$ benchmark for noticeable real-world educational gains, with **+17%** gains on UB reasoning questions (`remove_zeros Q3`, `apply_curve Q2`).
- **Critical Notional-Machine Lesson (`aquascope_oopsla23.txt:2581–2589`):** Initially, `Aquascope`'s runtime diagram did *not* gray out moved-from variables, because dynamically a Rust move is just a bitwise byte copy. Learners protested repeatedly because hiding move-invalidation broke their mental link between runtime state and static `Own` loss—forcing the authors to render move-invalidation visually on runtime frames.

#### 2.2 De Facto C vs. ISO C11 Undefined Behavior (`Cerberus`)

`Basis: normative + documentation`

In `rems-project/cerberus` (`e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e`; Memarian et al. `PLDI 2016` DOI `10.1145/2908080.2908081` & `POPL 2019` DOI `10.1145/3290380`), surveys of 300+ practicing C programmers established widespread disagreement between human systems mental models and ISO C11 / Clang-GCC optimization assumptions:
- Programmers routinely model pointers as flat integer addresses (`uintptr_t` round-tripping), expect uninitialized struct padding reads to yield arbitrary stable bytes rather than deferred poison/UB, assume one-past-the-end pointer comparisons reflect adjacency, and expect signed arithmetic to wrap modulo $2^w$.
- Cerberus bridges this gap via an explicit **Ail -> Core** elaborator (`README.md:69–72`) paired with tunable **PNVI-ae-udi** (*Provenance Not Via Integers — Address-Exposed / User-Disambiguated*) memory semantics, directly informing Rust's Strict Provenance (`expose_provenance` / `with_addr`) APIs and MiniRust's explicit provenance model.

---

### 3. Visual Semantic Projections & Live Evaluation X-Rays (`Aquascope`, `RustViz`, `Hazel`)

`Basis: source + documentation`

| System (Pinned) | Primary Mechanism & Compiler Hook | Visual Projection Model | Strengths | Structural Blind Spots |
|---|---|---|---|---|
| **`Aquascope`** (`f2d0a060...`, 12,566 lines) | `rustc_plugin` extracting `BodyWithBorrowckFacts` (Polonius) + `miri` runtime stepper | CodeMirror decorations: stacked `R/W/O` permission icons (`boundaries`) + state-diff tables (`stepper`) + stack/heap boxes | Automatically tracks real `rustc` borrow checker + concrete Miri heap; proven $+9\%$ ($d=0.56$) Inventory gain | Tied to exact `nightly-2024-12-15` `rustc_private`; fails on macros/unsafe internals outside supported MIR subset; static stack/heap diagrams saturate above ~10–15 bindings |
| **`RustViz` v2** (`b8c05e06...`, 114,779 lines; evolved from `VL/HCC 2022`) | Custom `rustc_private` plugin (`visitor.rs`, `mir_data.rs`, `ref_flow.rs`) + static `mdbook-rustviz` | Synchronized left code pane + right vertical resource timeline SVG (owner lifetime bars, solid/hollow dot borrows, hover explanations) | **Zero client JS dependency** for embedded SVGs (`mdbook`); v2 replaces hand-authored v1 DSL with real `rustc` HIR+MIR analysis (`ref_flow.rs` call lifetime extraction, `mir_data.rs` `Box` partial moves) | Must still combine HIR + MIR (`mir_data.rs:1–8`: MIR alone hides syntactic copy/assignment distinctions); focused on single-function pedagogical snippets |
| **`Hazel`** (`13ba5d13...`, Omar et al. `POPL 2019`) | Structure editor + bidirectional type hole-filling + live evaluator around hole closures | Continuous live values displayed inline even inside incomplete ASTs containing empty/non-empty holes (`?`) | Eliminates "syntax/type error blacks out all execution feedback" barrier; preserves total evaluation around partial programs | Requires structural/projectional editing or disciplined hole recovery; harder to retrofit onto raw text-buffer Rust/C++ crates |
| **`Python Tutor` / `SMoL` Stack-Heap Views** | Bytecode/AST frame tracing + SVG box-and-pointer rendering | Explicit stack frames pointing to shared heap boxes (`mvec` / `list` / closure env) | Directly cures `DefsCopyStructs` (`67%`), `StructByRef` (`24%`), and `DeepClosure` (`21%`) by showing shared heap pointers visually | Layout collapses on large loops, deep recursion, or zero-copy byte slices without automated summarization |

---

### 4. WYSIWYG / Anti-Magic Language Design: Enforcing Syntactic-Semantic Isomorphism

`Basis: normative + source + execution + derived`

Every implicit compiler transformation creates a potential fork between *what the human reads* and *what executes*. Inspecting `ziglang/zig` (`738d2be9d6b6ef3ff3559130c05159ef53336224`) and `austral/austral` (`0962d2a8a5d77f7daacd7f696819520733f4897d`, `28,766` lines) alongside Rust and C++ reveals concrete grammatical and type-system mechanisms that enforce **syntactic-semantic isomorphism** ("no invisible control flow, no invisible allocations, no hidden precedence"):

| Hazard Class | Implicit / "Magic" Design (`C++`, `Rust`, `Python`) | WYSIWYG Enforcement (`Zig` `738d2be9...` & `Austral` `0962d2a8...`) | Verified Source / Probe Evidence & Design Trade-Off |
|---|---|---|---|
| **Operator Precedence & Visual Grouping Traps** | C/C++/Rust give `==` higher precedence than `&`/`^`/`\|` (`flags & MASK == EXPECTED` parses as `flags & (MASK == EXPECTED)`!) and allow chained `a < b < c` (evaluating `(a < b) < c` in C). | **`Zig` (`lib/std/zig/Parse.zig:1545–1645`):** `operTable` assigns `.equal_equal` **prec 30, `Assoc.none`** and `.ampersand`/`.caret`/`.pipe` **prec 40** (`L1559–1570`); `banned_prec` rejects `a == b == c` (`chained_comparison_operators`, `L1605–1607`); bans `&&` (`L1623–1626`); **warns on asymmetric whitespace around binary ops** (`L1627–1629`, catching misleading `a+b * c`)! **`Austral`:** rejects all unparenthesized mixed binary precedence altogether. | Probe Part 2 (`flags=0b0110, MASK=0b0010, EXPECTED=0b0010`): C silently yields `False`, whereas Zig evaluates `(flags & MASK) == EXPECTED == True`. Trade-off: mandatory parens in Austral add modest syntax noise in arithmetic formulas. |
| **Hidden Control Flow (Exceptions, Drop, Coercions)** | C++ constructors/exceptions, `Deref` deref-coercions, Python `__getattr__`, and Rust `Drop` inject invisible calls, panics, or `MutexGuard` temporary lifetime extension at semicolon/block boundaries. | **`Zig`:** zero exceptions, zero operator overloading, zero `Drop`/RAII destructors; every error propagation uses explicit `try`/`catch`/`orelse` (`Parse.zig:1569–1570`), and cleanup uses lexical `defer`/`errdefer`. **`Austral` (`Stages.ml`, `README.md`):** explicit "anti-features"—no exceptions, no destructors, no implicit conversions, no overloading, no macros, no shadowing (`LinearityCheck.ml:66–69`), strict left-to-right eval. | Eliminating `Drop` removes hidden temporary-lifetime deadlocks completely, **but** in Zig manual `defer` can be forgotten on non-memory handles—whereas `Austral` (`LinearityCheck.ml:18–23, 106–118`) turns missing resource cleanup into a hard compile error (`Forgot to consume a linear variable`)! |
| **Hidden Allocations & Implicit Copies** | Rust `Clone` is explicit, yet arbitrary `Copy` structs or C++ copy constructors silently `memcpy` kilobytes on assignment; `DefsCopyStructs` (`67%`) shows programmers mispredict assignment copying. | **`Zig`:** explicit `Allocator` parameter convention (`std.mem.Allocator`) at every heap-allocating call site. **`Austral`:** splits `LinearUniverse`/`TypeUniverse` from `FreeUniverse` (`LinearityCheck.ml:25–28, 71–81`); linear values cannot be implicitly duplicated or dropped (`Unconsumed -> BorrowedRead/Write -> Consumed`). | Forces explicitness of memory/capability movement in source; increases parameter plumbing (`allocator` / linear thread-through). |
| **Silent Integer Wrap, Truncation & UB** | C unsigned wraps silently while signed overflow is full UB; Rust panics on overflow in debug builds yet silently wraps in `--release`! | **`Zig` (`Parse.zig:1576–1591`):** standard `+`/`-`/`*` always panic/trap in safety-checked modes rather than silently wrapping; modular wrapping requires explicit `+%, -%, *%` (`.add_wrap`, `L1579–1589`) and saturation requires explicit `+\|, -\|, *\|` (`.add_sat`, `L1581–1590`). **`Austral`:** explicit conversion functions only; zero implicit integer widening/narrowing. | Probe Part 2 shows `(100_i8 + 100_i8) / 2` wrapping silently to **`-28`** vs. **`100`** in $\mathbb{Z}$; separating `+` vs `+%` vs `+|` exposes overflow semantics directly in syntax. |

---

### 5. Differential Intent Checking & Guarding Against Specification / Patch Reward Hacking

`Basis: documentation + execution + derived`

Even when a lower-level IR or proof checker (`rustc`/LLVM, `Miri`, Verus, Rocq) is mathematically sound relative to *its* formal IR axioms, **intent bugs** arise across two seams:

1. **Surface Mental-Model vs. Optimizing IR Divergence:** Standard optimizers exploit compiler UB (`signed i32 nsw` overflow, uninitialized padding, dead-bounds elimination) that contradicts programmers' surface mental models. As demonstrated in Probe Part 3a (`probe_mental_models.py`), differentially checking a naive mathematical-$\mathbb{Z}$ mental-model evaluator (`x + 1 > x`) against an `nsw`-optimizing IR pass (`always true`) over 10,002 sample inputs immediately flags the exact divergence point `x = 2147483647` (`INT_MAX`). Running `rust-lang/miri` (`93d13704b5e5e12dedfc54df626468000bc46262`) provides the Rust-level UB oracle catching Tree/Stacked Borrows, uninit, and alignment violations before LLVM lowers them away—while remaining blind to pre-MIR coercions or arithmetic wrap intent unless paired with a surface-level specification oracle.
2. **Large-Scale Differential Intent & Reward-Hacking Defenses (Anthropic & Theorem, Oct 2026):** In Anthropic's Oct 2026 formal verification study (`anthropic_fv.txt:116, 178`):
   - **Differential Oracle Validation (`anthropic_fv.txt:116`):** An LLM-built Rust interpreter for a large subset of Python was formally proved in **Verus** against academic CPython semantics, and then differentially tested across **1.7 million randomly generated Python programs** against CPython—establishing **99.95%** identical execution while isolating the remaining `0.05%` spec corner cases that static proofs alone did not flag.
   - **Patch Reward Hacking (`anthropic_fv.txt:178`, Footnote 06):** When agents verify and repair code against generic "no-crash" safety properties, an agent can trivially satisfy the proof obligation by rewriting a program into an early-return stub that never reaches the buggy code path! As Anthropic reports, preventing reward hacking required **penalizing patches, rewarding formal proofs of which exact inputs change behavior and how few they are, and auditing diffs**. Probe Part 3b reproduces this discriminator quantitatively: a genuine saturating boundary patch preserves **10,001 / 10,001 (100.00%)** non-crashing inputs, whereas a reward-hacking early-exit stub preserves **0 / 10,001 (0.00%)** while passing identical "no crash" safety checks.

---

### 6. Multi-Level Performance & Resource Footprint (L1–L6) and Human Comprehensibility & Model Refinement (C1–C2)

#### 6.1 Six-Level Performance & Resource Footprint Comparison (L1–L6)

`Basis: source + documentation + execution + derived`

| Tool / Language Stack (Pinned) | (L1) Human/Agent Cognitive & Authoring Cost | (L2) Toolchain Build Time & RSS | (L3) Analysis / Compile / Visualization Latency | (L4) Runtime Execution Overhead | (L5) Verification / Oracle Throughput | (L6) Disk, Binary & Artifact Footprints |
|---|---|---|---|---|---|---|
| **`SMoL` + `SMoL Tutor`** (`858d1b46...` / `1ab5cfa7...`) | **892 LoC** across entire `smol` Racket family; **9.8 min median** human study module time (`smol_oopsla24.txt:1065`) | Standard Racket `raco pkg install` (<10 s) | Interactive browser MCQ + misinterpreter classification (<10 ms per tiny snippet) | Racket bytecode/JIT (~microseconds per benchmark program) | Instantaneous exhaustive check of all 7+ misinterpreters per snippet | Minimal text/JSON/Racket files (<1 MB) |
| **`Aquascope`** (`f2d0a060...`) | **0 manual annotations** (unlike `RustViz` v1); `12,566` lines; +9% learner comprehension gain ($d=0.56$) | Heavy: full `cargo` build linking `rustc_private`, `polonius-engine`, `datafrog`, `rustc_utils` (~1–3 min, 1–3 GB RSS) | Hundreds of ms to a few seconds per snippet (Polonius Datalog + optional `miri` trace capture) | Zero runtime overhead in compiled user binaries (analysis tool only) | Deterministic Datafrog fixpoint per MIR body; scales well on functions `<200` LoC | Requires pinned `nightly-2024-12-15` + `rustc-dev` + `miri` (~1–2 GB disk); JSON visualization payloads KB-scale |
| **`RustViz` v2** (`b8c05e06...`) | **0 manual annotations** (`114,779` lines incl. tests/examples); replaces handwritten v1 timeline DSL | Heavy workspace build (`rustviz-plugin` links `rustc_private`, `nightly-2026-05-01`; `mdbook-rustviz`, Docker runner optional) | Compile-time SVG generation during `mdbook build` (~seconds per book chapter) | **Zero runtime cost** (renders static inline SVG + CSS hover highlights; zero client JS required!) | Runs `rustc` borrowck + HIR/MIR visitor (`visitor.rs`, `ref_flow.rs`) once per build | Self-contained SVGs (tens of KB per snippet); plugin + nightly toolchain ~1–2 GB |
| **`Zig`** (`738d2be9...`) | Explicit `Allocator` & `try` add slight local LoC; zero hidden macro/overload action-at-a-distance | Zig self-hosted compiler builds in ~minutes, sub-second incremental SoA compilation | Sub-second incremental AST/ZIR/AIR compilation (`Parse.zig` single-pass recursive descent + `operTable` lookup) | Zero cost for precedence/error unions; safety-checked integer ops add `jo` overflow branch in safe modes (`+%` = 0 overhead) | Compile-time parser + comptime checks run inline during `zig build` | Compact native binaries; SoA AST indices cut compiler RAM vs pointer ASTs |
| **`Austral`** (`0962d2a8...`) | **`28,766` total lines** (compiler + stdlib + tests); linearity + no type inference raises explicit annotation LoC | Pure OCaml + `dune` build (~seconds, <300 MB RSS) | Fast linear-pass `TypingPass -> LinearityCheck -> CodeGen` (`778` LoC linearity checker) -> C emission | **Zero runtime GC / RC / exception unwinding cost**; linear capabilities compile away to plain C values | Deterministic linear type checking (no SMT solver or fixpoint timeouts!) | Tiny OCaml compiler binary + clean standalone C output |
| **`Miri` / Differential Oracles** (`93d13704...`) | **0** annotation burden for default tests; differential fuzzing scales autonomously (1.7M tests in Anthropic Python study) | Full `rustc` + `miri` driver (~minutes build; packaged via `rustup component add miri`) | ~10–100x slower than native `cargo test` due to MIR interpretation + Tree/Stacked Borrows metadata tracking | Zero impact on release binary (test-time only) | Thousands of small tests/min; Verus-to-CPython differential oracle executed **1.7M programs** | High interpreter RSS per tracked allocation (per-byte provenance & borrow tags) |

#### 6.2 (C1) Human Comprehensibility & Mental-Model Ergonomics

`Basis: documentation + source + derived`

- **Working-Memory Economics & Notional Machines:** Empirical data from both `SMoL` and `Aquascope` converges on a hard cognitive limit: programmers reason reliably with **2–4 explicit runtime/permission state slots** (`Environment`, `Store/Heap`, `R/W/O` path permissions), and systematically fail when language syntax *conflates* distinct semantic operations (e.g., Python's `=` performing binding or mutation inducing `DefOrSet`, or Rust moves hiding invalidation in runtime diagrams).
- **LLM vs. Human Comprehension Asymmetry:** Humans struggle with multi-indirection pointer reasoning (`Box<&Box<i32>>` at `47%` accuracy) and hidden precedence (`flags & MASK == EXPECTED`), whereas LLMs fail at **spec-intent drift**—writing 600K-line lowered proofs or reward-hacking early-return patches unless forced to exhibit input-domain behavioral preservation. WYSIWYG grammars (`Zig`, `Austral`) simultaneously aid both human reviewers and automated spec extractors because AST topology matches execution steps 1-to-1.

#### 6.3 (C2) Simplicity, Orthogonality & Universal Model Refinement

`Basis: derived`

Evaluating mental-model designs via Felleisen's expressiveness criterion and Ousterhout's module depth distinguishes **essential unification** from **false minimalism**:
- **Universal Simplifications That Work:**
  1. **`SMoL`'s 2-Map Store Model (`Env: Id -> Loc`, `Store: Loc -> Val`):** Collapses `DefsCopyStructs`, `DefByRef`, `CallByRef`, `DeepClosure`, `StructByRef`, and `FlatEnv` into **one uniform rule**: every variable binds to a location, every compound struct lives on the heap, and every closure captures its enclosing lexical `Env`.
  2. **`Aquascope`'s `R/W/O` Permission Lattice:** Abstracts hundreds of internal Polonius Datalog tuples (`loan_live_at`, `origin_contains_loan_on_entry`) into **three intuitive operations on paths** (`Read`, `Write`, `Own`), faithfully bridging static type errors to dynamic UB without exposing SSA/region-inference plumbing.
  3. **`Zig`'s Explicit Operator Separation (`+` vs `+%` vs `+|` and `prec(bit) > prec(cmp)`):** Removes ambiguity by making wrapping/saturation/error-return explicit syntactic primitives rather than compiler-flag-dependent hidden modes.
- **Where Stripping Features Shifts Complexity Into Consumers (Ousterhout Depth Warning):**
  - `Austral`'s ban on **all** type inference, **all** arithmetic operator precedence, and **all** destructors simplifies the *compiler* (`LinearityCheck.ml` is just `778` LoC), **but pushes nontrivial mechanical boilerplate onto every call site** (manual parentheses on `a + b + c`, explicit type annotations on every temporary, and manual destruction calls for nested linear records). Similarly, omitting `Drop` in `Zig` simplifies control flow *at the cost* of human-forgotten `defer` cleanup whenever linear type enforcement is absent. The sweet spot is **selective WYSIWYG**: explicit control-flow boundaries (`try`/`?`), explicit overflow modes, non-surprising operator precedence, and structural linearity/permissions visualization.

---

## Boundaries

- **`known not to apply` — `SMoL` Misconception Frequencies to Pure Immutable or Linear Languages:** `SMoL` (`shriram/smol`) characterizes languages with mutable variables + mutable heap structures + GC (`OOPSLA 2024`); pure non-strict languages (Haskell) or strict linear systems languages without shared mutability (`Austral`) eliminate `DefsCopyStructs`, `DeepClosure`, and `StructByRef` by construction (though they introduce distinct laziness or linearity learning hurdles).
- **`known not to apply` — Single-Function Visualizers to Whole-Crate Async / Unsafe / Proc-Macro Code:** Both `Aquascope` (`f2d0a060...`) and `RustViz` v2 (`b8c05e06...`) analyze localized MIR/HIR function bodies; multi-crate `async` state-machine pinning, interior mutability (`UnsafeCell`), and unexpanded/opaque procedural macros fall outside their permission/timeline fidelity.
- **`unsupported` — Live Execution Inside Incomplete Syntax in Standard Compilers:** Unlike `Hazel` (`13ba5d13...`), production `rustc`, `zig`, `austral`, `Aquascope`, and `RustViz` cannot render live runtime step-frames on programs containing parse or type errors.
- **`unknown` — Direct Correlation Between `Ownership Inventory` Gains and Long-Term Production Rust Productivity:** Crichton et al. (`aquascope_oopsla23.txt:2881–2883`) explicitly note that correlating Inventory scores with multi-month real-world Rust engineering performance remains open future work.
- **`unknown` — Empirical Misconception Rates of Experienced Engineers on `Zig` vs. `Austral`:** Controlled multi-institution misconception studies comparable to `SMoL Tutor` ($N > 500$) or `Ownership Inventory` ($N > 160$) do not yet exist for `Zig`'s `+%`/`+|` or `Austral`'s linear capabilities.
- **`not examined` — Full Local Compilation of `Aquascope`, `RustViz`, `Hazel`, `Cerberus`, `Zig`, and `Austral`:** Repository source files, AST/parser tables, linearity checkers, and peer-reviewed empirical evaluations were directly inspected at pinned commits; the Rust/OCaml/Zig compilers were not built locally in this environment (all execution evidence derives from the self-contained Python 3 probe).

---

## Evidence

### Primary Repositories and Exact Source Citations (Observed `2026-11-19`)

- **`shriram/smol`** @ `858d1b461924a7a9a37e9119faf191304dda5835` (`892` lines; `fun/semantics.rkt` L1–97, `state/semantics.rkt`, `hof/semantics.rkt`, `dyn-scope-is-bad/semantics.rkt` L1–140 dynamic-scope `dvs` parameter misinterpreter) & **`brownplt/smol-translator`** @ `1ab5cfa769926642af80b5189552649dd89995fe`.
- **`cognitive-engineering-lab/aquascope`** @ `f2d0a06034b86765a91f10b7c8e40ec31ecb87a6` (`12,566` lines):
  - `README.md` (`nightly-2024-12-15` + `miri` setup requirement); `ARCHITECTURE.md` L16–39 (`aquascope_front`, `PermissionsCtxt`, `boundaries`, `stepper`, CodeMirror `Decoration`).
  - `crates/aquascope/src/analysis/permissions/context.rs` L42–120 (`PermissionsCtxt`, `BodyWithBorrowckFacts`, `MoveData`, `RegionFlows`).
  - `crates/aquascope/src/analysis/permissions/output.rs` L33–175 (`Output`: `never_write`, `loan_read_refined`, `loan_write_refined`, `loan_drop_refined`, `path_maybe_uninitialized_on_entry`, `move_refined`, `derive_permission_facts`).
  - `crates/aquascope/src/analysis/permissions/flow.rs` L170–379 (`RegionFlows`, `compute_flows`).
- **`rustviz/rustviz`** @ `b8c05e066bc6cf11734818aa8d8332bf7542497e` (`114,779` lines):
  - `README.md` L9–45 (`rv1-final` manual DSL vs. v2 compiler-integrated `rustc_private` plugin on `nightly-2026-05-01`).
  - `rustviz-plugin/src/mir_data.rs` L1–160 (comment L1–8 explaining HIR+MIR hybrid necessity; `BoxFieldMoves`, `BoxContentsMoves`, `KeptLoan`), `rustviz-plugin/src/ref_flow.rs` L1–160 (`callee_sig`, `impl_view_sig`, `ArgFlow`).
- **`hazelgrove/hazel`** @ `13ba5d135a4e47728f099f1eb56746e0e57f3c99` (Omar et al. `POPL 2019`, DOI `10.1145/3290329`).
- **`rems-project/cerberus`** @ `e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e` (`README.md` L55–72, `--ast=cabs`, `--ast=ail`, `--pp=core`, `--exec`).
- **`ziglang/zig`** @ `738d2be9d6b6ef3ff3559130c05159ef53336224`:
  - `lib/std/zig/Parse.zig` L1545–1645 (`OperInfo`, `operTable` with `.equal_equal` prec 30 `Assoc.none` vs `.ampersand` prec 40, `.add_wrap`/`+%`, `.add_sat`/`+|`, `.keyword_catch`/`.keyword_orelse` prec 40; `parseExprPrecedence` L1593–1644 checking `banned_prec -> .chained_comparison_operators`, `.invalid_ampersand_ampersand`, `.mismatched_binary_op_whitespace`).
- **`austral/austral`** @ `0962d2a8a5d77f7daacd7f696819520733f4897d` (`28,766` lines):
  - `lib/LinearityCheck.ml` L18–123 (`var_state`: `Unconsumed | BorrowedRead | BorrowedWrite | Consumed`, `universe_linear_ish`, `remove_entry` raising `LinearityError` `"Forgot to consume a linear variable"`).
  - `lib/Stages.ml` L12–160 (`Ast`, `Combined`, `AstLC` typed compiler stages).
- **`rust-lang/miri`** @ `93d13704b5e5e12dedfc54df626468000bc46262` (reference MIR UB interpreter).

### Peer-Reviewed Publications & Primary Engineering Reports Verified

- Lu & Krishnamurthi (2024), *Identifying and Correcting Programming Language Behavior Misconceptions*, PACMPL 8(OOPSLA1):106, DOI `10.1145/3649823`.
- Crichton, Gray & Krishnamurthi (2023), *A Grounded Conceptual Model for Ownership Types in Rust*, PACMPL 7(OOPSLA2):265, DOI `10.1145/3622841`, `arXiv:2309.04134v1`.
- Almeida, Cole, Du, Luo, Pan, Pan, Qiu, Reddy, Zhang, Zhu & Omar (2022), *RustViz: Interactively Visualizing Ownership and Borrowing*, IEEE VL/HCC 2022, DOI `10.1109/VL/HCC53370.2022.9833121`.
- Omar, Voysey, Chugh & Hammer (2019), *Live Functional Programming with Typed Holes*, PACMPL 3(POPL):14, DOI `10.1145/3290329`.
- Memarian, Matthiesen, Lingard, Nienhuis, Chisnall, Watson & Sewell (2016), *Into the Depths of C: Elaborating the De Facto Standards*, PLDI 2016, DOI `10.1145/2908080.2908081`; Memarian et al. (2019), *Exploring C Semantics and Pointer Provenance*, PACMPL 3(POPL):67, DOI `10.1145/3290380`.
- Anthropic Frontier Red Team & Theorem (Oct 2026), *LLMs are making formal software verification feasible at a much larger scale*, `https://www.anthropic.com/research/formal-verification` (1.7M-program CPython differential test at `99.95%` parity; Footnote 06 patch reward-hacking controls).

### Reproducible Execution Probe and Verbatim Output (`2026-11-19`)

Save the following standalone script to `/tmp/probe_mental_models.py` and run `python3 /tmp/probe_mental_models.py` (Python 3.10+, standard library only):

```python
#!/usr/bin/env python3
"""Micro-probe 2: SMoL misinterpreters, precedence/wrap traps, and differential intent checking."""
from dataclasses import dataclass

@dataclass
class Closure:
    params: list; body: list; env: dict

class SmolVM:
    def __init__(self, mode="canonical"):
        self.mode = mode
        self.store = {}
        self.next_loc = 1

    def alloc(self, val):
        loc = self.next_loc; self.next_loc += 1
        self.store[loc] = val
        return loc

    def clone_val(self, val):
        if isinstance(val, tuple) and val[0] == "vec_ref":
            return ("vec_ref", self.alloc(list(self.store[val[1]])))
        return val

    def run(self, stmts, env=None):
        if env is None: env = {}
        out = None
        for st in stmts:
            out = self.ev(st, env)
        return self.fmt(out)

    def fmt(self, v):
        if isinstance(v, tuple) and v[0] == "var_ref":
            return self.fmt(self.store[v[1]])
        if isinstance(v, tuple) and v[0] == "vec_ref":
            elems = self.store[v[1]]
            return f"#({ ' '.join(self.fmt(e) for e in elems) })"
        return str(v)

    def ev(self, e, env):
        if isinstance(e, int): return e
        if isinstance(e, str):
            if e not in env: return "ERROR"
            val = self.store[env[e]]
            if self.mode == "StructByRef" and isinstance(val, tuple) and val[0] == "var_ref":
                return self.store[val[1]]
            return val
        op = e[0]
        if op == "defvar":
            _, x, rhs = e
            if self.mode == "DefByRef" and isinstance(rhs, str) and rhs in env:
                env[x] = env[rhs]
                return None
            val = self.ev(rhs, env)
            if val == "ERROR": return "ERROR"
            if self.mode == "DefsCopyStructs": val = self.clone_val(val)
            env[x] = self.alloc(val)
            return None
        if op == "set!":
            _, x, rhs = e
            if x not in env: return "ERROR"
            val = self.ev(rhs, env)
            self.store[env[x]] = val
            return None
        if op == "mvec":
            elems = []
            for arg in e[1:]:
                if self.mode == "StructByRef" and isinstance(arg, str) and arg in env:
                    elems.append(("var_ref", env[arg]))
                else:
                    v = self.ev(arg, env)
                    if v == "ERROR": return "ERROR"
                    elems.append(v)
            return ("vec_ref", self.alloc(elems))
        if op == "vec-set!":
            _, vx, idx, rhs = e
            vr = self.ev(vx, env); i = self.ev(idx, env); v = self.ev(rhs, env)
            self.store[vr[1]][i] = v
            return None
        if op == "add":
            a, b = self.ev(e[1], env), self.ev(e[2], env)
            if "ERROR" in (a, b): return "ERROR"
            return a + b
        if op == "lam":
            _, params, body = e
            cap_env = dict(env)
            if self.mode == "DeepClosure":
                cap_env = {k: self.alloc(self.store[loc]) for k, loc in env.items()}
            return Closure(params, body, cap_env)
        if op == "call":
            fn = self.ev(e[1], env)
            if not isinstance(fn, Closure): return "ERROR"
            call_env = env if self.mode == "FlatEnv" else dict(fn.env)
            for p, arg in zip(fn.params, e[2:]):
                if self.mode == "CallByRef" and isinstance(arg, str) and arg in env:
                    call_env[p] = env[arg]
                else:
                    av = self.ev(arg, env)
                    if self.mode == "CallsCopyStructs": av = self.clone_val(av)
                    call_env[p] = self.alloc(av)
            res = None
            for b in fn.body:
                res = self.ev(b, call_env)
                if res == "ERROR": return "ERROR"
            return res

benchmarks = {
    "DefsCopyStructs_probe": [("defvar", "x", ("mvec", 100)), ("defvar", "y", "x"), ("vec-set!", "x", 0, 200), "y"],
    "DefByRef_probe": [("defvar", "x", 12), ("defvar", "y", "x"), ("set!", "x", 0), "y"],
    "CallByRef_probe": [("defvar", "x", 12), ("defvar", "f", ("lam", ["y"], [("set!", "y", 0), "x"])), ("call", "f", "x")],
    "CallsCopyStructs_probe": [("defvar", "x", ("mvec", 1, 0)), ("defvar", "f", ("lam", ["y"], [("vec-set!", "y", 0, 173)])), ("call", "f", "x"), "x"],
    "DeepClosure_probe": [("defvar", "x", 1), ("defvar", "f", ("lam", ["y"], [("add", "x", "y")])), ("set!", "x", 2), ("call", "f", "x")],
    "StructByRef_probe": [("defvar", "x", 3), ("defvar", "v", ("mvec", 1, 2, "x")), ("set!", "x", 4), "v"],
    "FlatEnv_probe": [("defvar", "f", ("lam", ["x"], [("defvar", "y", 200), ("add", "x", "y")])), ("add", ("call", "f", 2), "y")],
}

modes = ["canonical", "DefsCopyStructs", "DefByRef", "CallByRef", "CallsCopyStructs", "DeepClosure", "StructByRef", "FlatEnv"]
for bname, prog in benchmarks.items():
    canon = SmolVM("canonical").run(prog)
    diffs = {m: SmolVM(m).run(prog) for m in modes[1:] if SmolVM(m).run(prog) != canon}
    print(f"[1] {bname:22s}: canonical={canon:10s} | triggered={diffs}")

flags, MASK, EXPECTED = 0b0110, 0b0010, 0b0010
c_eval = bool(flags & (MASK == EXPECTED))
zig_eval = bool((flags & MASK) == EXPECTED)
def i8_wrap(n): return ((n + 128) % 256) - 128
print(f"[2] Precedence(flags&MASK==EXPECTED): C={c_eval} vs Zig={zig_eval} | Midpoint(100,100) i8_wrap={i8_wrap(100 + 100) // 2} vs Z={(100 + 100) // 2}")

def surface_mental_eval(x): return x + 1 > x
def ub_opt_ir_eval(x): return True
def target_bounds_checked(x):
    if x >= 2**31 - 1: return ("CRASH_SIGNED_OVERFLOW", None)
    return ("OK", (x + 1) > x)
def patch_genuine_saturating(x):
    return ("OK", True if x >= 2**31 - 1 else (x + 1) > x)
def patch_reward_hack_stub(x):
    return ("OK", False)

domain = list(range(-5000, 5000)) + [2**31 - 2, 2**31 - 1]
ub_mismatches = [x for x in domain if surface_mental_eval(x) != (x < 2**31 - 1 and ub_opt_ir_eval(x))]
print(f"[3a] Differential UB-folding intent check over {len(domain)} inputs: mismatches_at={ub_mismatches} (when wrapped i32: INT_MAX+1=-2147483648 < INT_MAX)")
for pname, pfn in [("genuine_saturating", patch_genuine_saturating), ("reward_hack_stub", patch_reward_hack_stub)]:
    ok_inputs = [x for x in domain if target_bounds_checked(x)[0] == "OK"]
    preserved = sum(pfn(x) == target_bounds_checked(x) for x in ok_inputs)
    print(f"[3b] PatchAudit({pname:18s}): non_crashing_intent_preserved={preserved}/{len(ok_inputs)} ({100.0*preserved/len(ok_inputs):.2f}%)")
```

Observed output (`2026-11-19`, Linux x86_64, Python 3):

```text
[1] DefsCopyStructs_probe : canonical=#(200)     | triggered={'DefsCopyStructs': '#(100)'}
[1] DefByRef_probe        : canonical=12         | triggered={'DefByRef': '0'}
[1] CallByRef_probe       : canonical=12         | triggered={'CallByRef': '0'}
[1] CallsCopyStructs_probe: canonical=#(173 0)   | triggered={'CallsCopyStructs': '#(1 0)'}
[1] DeepClosure_probe     : canonical=4          | triggered={'DeepClosure': '3'}
[1] StructByRef_probe     : canonical=#(1 2 3)   | triggered={'StructByRef': '#(1 2 4)'}
[1] FlatEnv_probe         : canonical=ERROR      | triggered={'FlatEnv': '402'}
[2] Precedence(flags&MASK==EXPECTED): C=False vs Zig=True | Midpoint(100,100) i8_wrap=-28 vs Z=100
[3a] Differential UB-folding intent check over 10002 inputs: mismatches_at=[2147483647] (when wrapped i32: INT_MAX+1=-2147483648 < INT_MAX)
[3b] PatchAudit(genuine_saturating): non_crashing_intent_preserved=10001/10001 (100.00%)
[3b] PatchAudit(reward_hack_stub  ): non_crashing_intent_preserved=0/10001 (0.00%)
```

---

## Revalidation

To confirm whether these findings still apply on newer revisions or language implementations without repeating full surveys:

1. **Zig Precedence & Safety Grammar:** Inspect `lib/std/zig/Parse.zig` around `operTable` (`ziglang/zig` vs `738d2be9...`) to verify `.equal_equal` `Assoc.none` and bitwise-over-comparison precedence remain intact.
2. **Austral Linearity & Anti-Features:** Inspect `lib/LinearityCheck.ml` (`austral/austral` vs `0962d2a8...`) for changes to `var_state` or loosening of unconsumed linear-variable errors / type inference rules.
3. **Aquascope & RustViz Compiler Hooks:** Check `rust-toolchain.toml` and `crates/aquascope/src/analysis/permissions/output.rs` (`aquascope` vs `f2d0a060...`) and `rustviz-plugin/src/ref_flow.rs` (`rustviz` vs `b8c05e06...`) for Polonius/borrow-checker API migrations.
4. **SMoL Tutor & Misinterpreters:** Check `shriram/smol` (`858d1b46...`) and `brownplt/smol-translator` (`1ab5cfa7...`) for newly added language modules or updated Python/JS syntactic translations.
5. **Re-run Micro-Probe:** Execute `python3 /tmp/probe_mental_models.py` (`< 1s`, zero external dependencies) to re-verify all 7 misinterpreter discriminators, C-vs-Zig precedence & wrapping `i8` witnesses, and patch-audit intent ratios.
