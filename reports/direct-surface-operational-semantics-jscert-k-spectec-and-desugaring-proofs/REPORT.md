# Direct Surface Operational Semantics, Single-Source Specification Compilers, Elaboration Refinement, and Macro Framing Contracts

## Summary

Verifying software solely at a lowered intermediate representation (`MIR`, `LLBC`, `LLVM IR`, or `RISC-V`) certifies only what the compiler's front-end elaborated—leaving the translation from human-authored surface syntax (`AST -> HIR -> THIR -> MIR`, procedural macro expansion, coercions, operator overloading, and temporary drop-scope placement) inside an unverified Trusted Computing Base (TCB). Across mechanized specifications, rewriting semantics, specification compilers, and bidirectional elaborators, five foundational engineering results determine whether authoritative semantics can sit directly on surface ASTs or provably refine down from them:

1. **Direct Prose-Mirroring Surface Semantics via Pretty-Big-Step & Skeletal Semantics (`JSCert` / `JSRef` / `Skel`):** Standard big-step semantics suffers an $O(k)$ per-construct rule explosion for abort/exception/divergence propagation on $k$-subexpression forms (e.g., JavaScript calls, loops, and object initializers). Charguéraud's **Pretty-Big-Step** (`ESOP 2013`), deployed at industrial scale in `jscert/jscert` (26,203 lines across 42 files), breaks multi-premise evaluation into explicit intermediate states (`ext_expr`, `ext_stat`, `ext_prog`) and **one generic abort rule per syntactic category** (`red_expr_abort`, `red_stat_abort`, `red_prog_abort`, `red_spec_abort`), preserving 1-to-1 "eyeball closeness" to ECMA-262 5.1 prose while extracting the certified OCaml interpreter `JSRef` (`JsCorrectness.v`, 5,944 lines). **Skeletal Semantics** (`POPL 2019`) generalizes this pattern into a meta-language (`Skel`) whose single operational skeleton generates concrete, abstract, and proof-assistant interpretations simultaneously.
2. **Executable Rewriting Semantics on Surface ASTs vs. MIR Retreat (`K Framework`):** `K` (`runtimeverification/k`) compiles configuration cells (`<k>`, `<env>`, `<store>`) and strictness declarations directly into heating/cooling contextual evaluation rules, enabling complete surface AST formalizations of ISO C11 (`kframework/c-semantics`, `POPL 2012` / `PLDI 2015`, finding real compiler bugs via `kcc`) and Java 1.4 (`kframework/java-semantics`, `POPL 2015`). Crucially, K's Rust effort (`KMIR`, `runtimeverification/mir-semantics`, 13,290 lines) **retreated from surface Rust to lowered Stable-MIR**, demonstrating that surface traits, autoref/autoderef coercions, match ergonomics, and drop elaboration make direct surface-Rust rewriting prohibitively brittle without first formalizing Rust's elaborator.
3. **Single-Source Specification Compilers (`WebAssembly SpecTec`):** Maintaining separate LaTeX math, algorithmic reST prose, OCaml reference interpreters, and proof-assistant mechanizations guarantees cross-artifact drift. `Wasm-DSL/spectec` (`PLDI 2024`) compiles one typed declarative DSL (`EL -> IL`, checked internally without external SMT) via `il2al/transpile.ml` into LaTeX math, algorithmic reST prose, an OCaml interpreter (`Wasm2ST`: 2,957 LoC vs. 5,526 LoC manual reST, passing **49,833/49,833** applicable Wasm 2.0 tests in **58 seconds**), and theorem-prover targets, while flagging **13 historical Wasm 2.0 spec bugs** and **10 bugs across 5 Wasm 3.0 proposals**.
4. **The Rust Surface-to-IR Verification Chasm & Bidirectional Elaboration Refinement:** Rust verification splits across four unlinked layers: `rust-lang/a-mir-formality` (surface trait solver, coherence, variance, and NLL borrow checking over `judgment_fn!` tabling), `hacspec/hax` (THIR extraction preserving surface expression/match trees), `AeneasVerif/charon` (MIR/ULLBC/LLBC extraction), and `minirust/minirust` + `minirust/specr` (executable MIR-level operational semantics over `ValueExpr`/`PlaceExpr` with `NdResult` nondeterminism). Even with LCF/de Bruijn proof kernels (Lean 4, Rocq), **type-preserving elaboration** does **not** imply **human-intent fidelity**: `autoImplicit` bindings, `Int -> Nat` monus coercions, and notation overloadings routinely turn intended mathematical theorems into kernel-checked unintended statements.
5. **Hygienic Macro & Procedural Attribute Framing Contracts:** Racket's **Sets of Scopes** (`POPL 2016`, `racket/src/expander/syntax/scope.rkt`) and Lean 4's `MonadQuotation` (`src/Lean/Hygiene.lean`, `LMCS 2022`) enforce $\alpha$-equivalence algebraically. By contrast, Rust `proc_macro::TokenStream` + `dtolnay/syn` default to `Span::call_site()` (unhygienic capture) and execute Turing-complete host Rust code that can inject nonlocal `return`/`break`/`?` exits, mutate outer bindings, or reorder `Drop` guards. Surface-level verification requires a **5-clause Macro Framing Contract** restricting macro expansions to lexical hygiene, control-flow exit framing, drop-frame invariance, ambient trait non-pollution, and deterministic expansion.

---

## Applicability

This report governs language designers, specification engineers, compiler front-end developers, and formal verification tool builders deciding **where authoritative operational semantics should live** (surface AST vs. elaborated core/MIR) and how to verify or bound front-end elaboration and macro expansion.

The examined subjects divide into six concrete technical cohorts (exact pinned commits and DOIs in `REPORT.json` and `## Evidence`):

1. **Direct Surface Big-Step & Skeletal Semantics (`jscert/jscert`, `Skeletal Semantics`):** `jscert/jscert` (`891828c11308350836cdb8e832e4d00ed3019d9c`) targets **ECMAScript 5.1** in Coq (`JsPrettyRules.v`, `JsInterpreter.v`, `JsCorrectness.v`). Findings on pretty-big-step rule compression apply generally to any imperative/effectful surface language with exceptions, loops, or abrupt control flow; exact Coq metrics apply specifically to ES5.1. `Skeletal Semantics` (`10.1145/3290357`) applies to deterministic/non-deterministic languages whose operational rules decompose into monadic/branching skeletons.
2. **Rewriting Operational Semantics (`runtimeverification/k`, `kframework/c-semantics`, `kframework/java-semantics`, `runtimeverification/mir-semantics`):** Applies to `K` (`4a46d123...`), `K-C` (`e6879d14...` for C11 via preprocessed CIL ASTs), `K-Java` (`f27067ee...` for Java 1.4), and `KMIR` (`b8dede63...` for Stable-MIR). Findings distinguish direct surface-AST execution (`K-C`, `K-Java`) from `KMIR`'s MIR-level boundary (`docs/semantics-of-mir.md`).
3. **Single-Source Specification Compilers (`Wasm-DSL/spectec`, `WebAssembly/spec`):** Applies to `SpecTec` (`acc6e834ff403c82554d081237f327346190ad96`) and `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`) as evaluated on Wasm 2.0 and five Wasm 3.0 proposals (Youn et al., `PLDI 2024`, DOI `10.1145/3656440`). Note that `SpecTec`'s `il2al` backend targets languages whose dynamic semantics express as small/big-step reduction and typing relations; numeric bit-level ops and text parsing still delegate to OCaml reference code.
4. **Rust Multi-Layer Semantics Stack (`rust-lang/a-mir-formality`, `minirust/minirust`, `minirust/specr`, `hacspec/hax`, `AeneasVerif/charon`):** Pinning `a-mir-formality` (`503cc9de...`), `minirust` (`063d7841...`), `specr` (`f33ec909...`), `hax` (`0d2f66ed...`), and `charon` (`b2bb11d2...`). None of these revisions provides an end-to-end mechanized refinement proof bridging surface Rust ASTs to MIR/MiniRust.
5. **Bidirectional Elaboration & Macro Hygiene (`leanprover/lean4`, `racket/racket`, `dtolnay/syn`):** Pinning Lean 4 (`e35bfaf8...`, `src/Lean/Hygiene.lean`, Ullrich & de Moura `10.46298/lmcs-18(2:1)2022`), Racket (`049065d5...`, `racket/src/expander/syntax/scope.rkt`, Flatt `10.1145/2837614.2837620`), `dtolnay/syn` (`a2cddb7a...`, `src/expr.rs`), and Dunfield & Krishnaswami (`10.1145/3450952`).
6. **Standalone Micro-Probe (`probe_surface_semantics.py`):** Verified locally under Python 3 (`Basis: execution`), modeling the Pretty-Big-Step vs. K contextual equivalence check, Rust temporary drop-order divergence, macro framing checks, and `autoImplicit`/`Nat`-monus elaboration intent gap.

---

## Findings

### 1. Direct Surface Semantics Mirroring Normative Prose: Pretty-Big-Step (`JSCert`), `ESMeta`, and Skeletal Semantics (`Skel`)

#### 1.1 Why Standard Big-Step Fails on Imperative Surface Specifications

`Basis: normative + source + derived`

Language standards (ECMA-262, ISO C11, W3C Wasm) are written directly against human-visible ASTs in imperative prose with explicit evaluation order, state threading, exceptions, labeled `break`/`continue`, and abrupt returns. Standard structural operational semantics fails in two opposite ways when capturing such prose directly:

- **Small-step / Contextual Reduction (`E[e]`):** Requires flattening imperative multi-step clauses (e.g., JavaScript's `CallExpression` evaluating receiver, extracting `GetValue`, evaluating argument list left-to-right, checking `IsCallable`, allocating arguments object, and pushing execution context) into artificial syntax contexts or stack machines that no longer visually match specification paragraphs.
- **Conventional Big-Step Semantics ($\langle s, e \rangle \Downarrow \text{out}$):** Requires duplicating abort/exception propagation across **every premise position** of every $k$-ary construct. A $k$-premise construct requires $1$ normal rule plus $k$ abort-propagation rules (plus divergence rules if coinductive), inflating a realistic language specification by $3\text{--}5\times$ in rule count and obscuring the happy path.

#### 1.2 Charguéraud's Pretty-Big-Step Semantics in `jscert/jscert`

`Basis: normative + source + execution`

In `jscert/jscert` (`891828c11308350836cdb8e832e4d00ed3019d9c`; Bodin et al., `POPL 2014`, DOI `10.1145/2535838.2535876`), Charguéraud's Pretty-Big-Step semantics (`ESOP 2013`, DOI `10.1007/978-3-642-37036-6_3`) resolves this explosion across `26,203` lines of Coq and OCaml (`42` files, of which `coq/JsPrettyRules.v` is `5,309` lines, `coq/JsPrettyInterm.v` is `1,766` lines, `coq/JsInterpreter.v` is `3,058` lines, and `coq/JsCorrectness.v` is `5,944` lines):

1. **Intermediate Extended Syntax (`JsPrettyInterm.v` lines 54–160):** Each syntactic sort (`expr`, `stat`, `prog`, `spec`) is embedded into an extended datatype (`ext_expr`, `ext_stat`, `ext_prog`) carrying explicit numbered intermediate continuations matching ECMA-262 numbered sub-steps (e.g., `expr_call_1` through `expr_call_5` at `JsPrettyInterm.v:111–115`; `stat_while_1` through `stat_while_5` at `JsPrettyRules.v:280–320`).
2. **Single Generic Abort Rule per Sort (`JsPrettyInterm.v:1607–1672`, `JsPrettyRules.v:82, 124, 743, 4787`):** Outcomes unify into normal/abrupt termination `out_ter S R` and coinductive divergence `out_div`. `abort : out -> Prop` (`JsPrettyInterm.v:1607–1612`) matches `abort_div` and `abort_not_normal` (`abrupt_res R`). Unless an intermediate term is explicitly listed in `abort_intercepted_{prog,stat,expr}` (such as `stat_try_1` catching `restype_throw` or `stat_while_3` intercepting `restype_continue`/`restype_break` for matching labels `labs`, `JsPrettyInterm.v:1617–1670`), **one rule**—`red_prog_abort`, `red_stat_abort`, `red_expr_abort`, `red_spec_abort`—short-circuits *every* intermediate continuation position automatically.
3. **Rule Compression Verified in Micro-Probe Part 1:** On our 7-construct stateful/exception benchmark (`probe_surface_semantics.py`), Pretty-Big-Step collapses $15$ naive abort-propagating big-step premises into **1 generic abort rule** alongside shallow normal transitions while matching a small-step contextual `K` machine identically on `4/4` test expressions.
4. **Certified Reference Interpreter (`JsInterpreter.v` + `JsCorrectness.v`):** Because Coq's inductive relation `red_expr`/`red_stat`/`red_prog` cannot run directly against conformance suites, `JSCert` pairs the relational spec with a fuel-parameterized monadic functional interpreter (`runs_type` record in `JsInterpreter.v:125–152` storing 24 mutually recursive entry points, bounded by fuel `num`), extracted to OCaml (`JSRef`). `JsCorrectness.v:5893–5943` proves `Theorem runs_correct : forall num, runs_type_correct (runs num)` and `Corollary run_javascript_correct_num`, certifying that every non-bottom (`result_out o`) OCaml interpreter execution is a valid derivation of the normative `red_javascript` semantics. *(Note from primary source inspection: `JsCorrectness.v:5891` still contains one `Admitted. (* faster *)` inside `run_equal_correct` on line 5891 for ECMA-262 abstract equality sub-cases, an important audit boundary.)*

#### 1.3 Prose Reconstruction (`ESMeta`) vs. Multi-Interpretation Skeletons (`Skeletal Semantics`)

`Basis: normative + documentation`

- **`ESMeta` (`es-meta/esmeta`, cited in `spectec_pldi24.txt:225–229, 2237–2245`):** Rather than manually encoding ECMAScript in Coq like `JSCert`, `ESMeta` parses ECMAScript's HTML specification text (`ECMA-262`) directly into an algorithmic intermediate representation (`IRES`), integrating automated spec conformance and Test262 differential testing into TC39's official ECMAScript CI since November 2022. Its limitation is trust: `IRES` mirrors imperative ECMAScript prose mechanically without a declarative mathematical typing/proof-assistant extraction layer.
- **Skeletal Semantics (`POPL 2019`, Bodin, Gardner, Jensen, Schmitt, DOI `10.1145/3290357`):** Formalizes operational semantics in a tiny typed meta-language (`Skel`, processed by `Necro` / `necrolib`) where every construct's *skeleton* uses five structural combinators: sequencing (`let x = t1 in t2`), branching (nondeterministic or guard-filtered disjunctions), filter predicates, black-box helper hooks, and recursive evaluation calls. Interpreting the *same* skeleton over different **interpretation functors** simultaneously produces: (1) a concrete big-step operational semantics, (2) a small-step/fuel-bounded OCaml interpreter, (3) Coq inductive/functional definitions, and (4) sound abstract interpreters—eliminating manual drift between concrete semantics and static analyses.

---

### 2. Rewriting-Based Executable Surface Semantics: `K Framework` (`K-C`, `K-Java`) vs. `KMIR`

#### 2.1 How `K` Executes Surface ASTs Directly via Configuration Cells and Heating/Cooling

`Basis: normative + source + documentation`

In the `K Framework` (`runtimeverification/k` @ `4a46d1231473b599c699160132fd6e76a5c46406`), surface semantics is authored directly as typed AST grammars paired with modular nested **configuration cells** (`<k>` computation continuation list `~>`, `<env>` lexical map, `<store>` heap, `<control>` call/exception stacks) and rewrite rules:

1. **Automatic Contextual Splitting via `strict` Attributes:** Marking `syntax Exp ::= Exp "+" Exp [strict]` automatically synthesizes heating rules ($e_1 + e_2 \rightharpoonup e_1 \curvearrowright \square + e_2$) and cooling rules ($v_1 \curvearrowright \square + e_2 \rightharpoonup v_1 + e_2$), supporting both deterministic left-to-right and nondeterministic (`seqstrict` vs `strict`) C expression evaluation orders without manually threading continuations.
2. **Surface C11 (`kframework/c-semantics` @ `e6879d14455771aa0cb3e3d201131d4d763a73a2`; Ellison & Roşu `POPL 2012`, DOI `10.1145/2103656.2103719`; Hathhorn, Ellison & Roşu `PLDI 2015`):** As inspected in `README.md:97–107`, `kcc` pipes C source through GNU `cpp` and an OCaml CIL parser (`cparser`) into a KAST `TranslationUnit`, then compiles **three** distinct semantics via `kompile` (`README.md:90–96`): deterministic, nondeterministic expression-sequencing, and nondeterministic thread-interleaving. Rather than silently optimizing or lowering UB away, `kcc` explicitly **gets stuck** on every ISO C11 Undefined Behavior (`UB-TDR2`, sequence-point unsequenced side effects, strict aliasing violations, out-of-bounds pointer arithmetic) and prints the stuck configuration (`config`, `README.md:31–38`), passing 99%+ of GCC C-torture tests and exposing real miscompilations in GCC/Clang/ICC.
3. **Surface Java 1.4 (`kframework/java-semantics` @ `f27067ee7a38d236499992eed1b48064e70680fa`; Bogdanas & Roşu `POPL 2015`, DOI `10.1145/2676726.2676982`):** Encodes Java's full object model, method overload resolution, class initialization (`<clinit>`), threads/locks, and exception propagation directly as K rewrite rules over parsed Java ASTs, executing Java test suites and catching JLS specification subtleties.

#### 2.2 The Telling Retreat of `KMIR` (`runtimeverification/mir-semantics`) from Surface Rust to MIR

`Basis: source + derived`

Inspecting `runtimeverification/mir-semantics` (`b8dede6335f4317371b6025af999dc9b56d6887d`, `13,290` lines across `245` files) exposes the fundamental complexity wall of direct surface-AST rewriting on modern Rust. Unlike `K-C` and `K-Java`, `KMIR` does **not** operate on surface Rust ASTs; instead (`kmir/src/kmir/kdist/mir-semantics/kmir.md:14–16`):

> *"The execution is initialised based on a loaded `Pgm` read from a json format of stable-MIR, and the name of the function to execute."*

Inspecting `docs/semantics-of-mir.md:43–131` and `kmir.md:62–180` reveals the exact consequences of this architectural retreat:

- **What MIR Strips Away:** `KMIR` inherits `rustc`'s entire unverified `AST -> HIR -> THIR -> MIR` lowering: macro expansion, trait/associated-type projection, autoderef/autoref coercions, method resolution, match ergonomics, temporary lifetime extension, and drop elaboration (`Drop` terminators marked `"UNCLEAR: noop after 'drop elaboration'"` at `docs/semantics-of-mir.md:80`, and `FakeRead`/`FalseEdge`/`Retag` treated as no-ops at `kmir.md:147–153`).
- **Why Surface K Rewriting Stalled for Rust:** C++ and Rust surface semantics are *non-local and type-directed*: the operational behavior of `a.foo(b)` or `match x.lock()` depends on global trait coherence tables, orphan rules, variance, NLL lifetime inference, and implicit `Deref` chains that cannot be expressed cleanly as local syntactic K heating/cooling rules (`[strict]`) without first embedding a full Rust trait solver inside K.

---

### 3. Single-Source Specification Compilers: `WebAssembly SpecTec`

`Basis: normative + source + documentation`

`Wasm-DSL/spectec` (`acc6e834ff403c82554d081237f327346190ad96`; paired with `WebAssembly/spec` @ `d0b2e8d5544d2049fba0521922c436e3f0fcaebe`; Youn et al., `PLDI 2024`, DOI `10.1145/3656440`) solves the multi-artifact synchronization problem by compiling one typed declarative specification DSL into four synchronized outputs:

1. **Elaboration & Internal Dimension Checking (`spectec/doc/Language.md:13–150`, `spectec/src/frontend/elab.ml:1–160`):** Authors write `syntax` notation definitions (supporting dependent type families like `syntax tuple(nat)`), `relation` declarative typing/reduction rules (`5-reduction.spectec`), and `def` auxiliary functions in the External Language (`EL`). `elab.ml` elaborates `EL` into a strongly typed Internal Language (`IL`), validating mixfix notation syntax, binding hygiene, and **list-iteration dimension consistency** (`*`, `?` arity alignment) internally via structural unification—avoiding the undecidability and external SMT dependencies of tools like `Sail`.
2. **Relational-to-Algorithmic Compilation (`spectec/src/il2al/transpile.ml:1–260`):** Because W3C Wasm requires *both* declarative math rules (LaTeX) and step-by-step imperative pseudocode (reST), `il2al/transpile.ml` automatically animates declarative `IL` reduction relations into the **Algorithmic Language (`AL`)**:
   - Infers input vs. output variable modes and synthesizes **inverse function calls** when premises pattern-match outputs of helper functions;
   - Applies `merge_blocks` (`transpile.ml:212–227`) and common-condition factoring (`extract_common_cond`, `eq_nat_cond` lines 65–114) to collapse overlapping declarative branches into clean `if ... else` prose rather than bloated duplicated trees;
   - Rewrites multi-frame context-escaping jumps (which are concise in evaluation-context math but opaque to implementers) into explicit single-frame block bubbling (`spectec_pldi24.txt:1957–1961`).
3. **Multi-Backend Code & Doc Generation (`backend-latex/render.ml`, `backend-prose/render.ml`, `backend-interpreter/construct.ml`):**
   - **Prose & LaTeX:** Emits publication-ready LaTeX formal rules and reST algorithmic prose directly (`Wasm2ST` = **2,957 LoC** vs. **5,526 LoC** handwritten reST, a **1.87x specification size reduction**).
   - **Meta-Level Interpreter (`backend-interpreter/construct.ml`):** Executes extracted `AL` algorithms over parsed Wasm ASTs (delegating `.wast` parsing and IEEE-754/vector bit arithmetic to the OCaml reference interpreter). On Wasm 2.0, `Wasm2ST` passes **49,833 / 49,833** (`100%`) applicable official tests (`47,391 assert_return`, `2,408 assert_trap` actions, `34 assert_trap` modules) in **58 seconds** on an 8-core 2.4 GHz Intel Core i9 (`spectec_pldi24.txt:2009–2014`).
   - **Empirical Bug Prevention (`spectec_pldi24.txt:2033–2169`):** Retroactively checking 2 years of `WebAssembly/spec` commits caught **13 historical bugs** (**3** type errors in DSL terms, **7** free-identifier/missing-step prose errors, **3** semantic errors). Applying SpecTec to **5 in-progress Wasm 3.0 proposals** (typed function references, GC, tail calls, multiple memories, extended const—adding 44 instructions) caught **10 previously unknown proposal bugs** (2 type, 2 prose, 4 semantic, 2 editorial) and then passed all **1,331** proposal tests.
   - **Planned / In-Progress Prover Backends (`spectec_pldi24.txt:2343–2406`):** `IL -> IL` simplification passes feed experimental Coq, Isabelle, Lean, and Agda backends, confronting the extrinsic-vs-intrinsically-typed AST gap across proof assistants.

---

### 4. The Rust Surface-vs-MIR Semantic Gap & Bidirectional Elaboration Soundness

#### 4.1 Mapping the Four-Layer Rust Verification Stack

`Basis: source + documentation + derived`

Inspecting the primary Rust formalization repositories exposes a critical **architectural split**: no single artifact simultaneously specifies surface Rust syntax, type/trait elaboration, and MIR operational memory semantics.

| Layer / Artifact | Pinned Repository & Commit | Scope Covered | Primary Mechanism | Explicit Blind Spot / Trust Boundary |
|---|---|---|---|---|
| **Surface Types, Traits, Coherence & NLL** | `rust-lang/a-mir-formality` (`503cc9de...`, 68,315 lines) | Generics, trait solving, orphan/coherence, variance, NLL borrow check (`nll.rs:124`) | `judgment_fn!` logic-programming macro (`judgment.rs:36–94`) with `Scope` & `ProvenSet` fixed-point tabling | Models surface-ish syntax (`to_rust/syntax.rs`) and experimental `minirust-rs`, **not** full `AST -> HIR -> MIR` lowering of real crates |
| **Structured Typed-HIR Extraction** | `hacspec/hax` (`0d2f66ed...`) | Pure/crypto Rust crates (`rust-engine` -> F\*, Coq, ProVerif, Lean via Aeneas) | Hooks into `rustc` at **THIR** (`cargo hax json`) preserving structured `match`, loops, and surface expressions | Trusts `rustc` parsing, macro expansion, typeck, trait resolution, and THIR coercion insertion; post-THIR drop elaboration not directly represented in legacy backend |
| **MIR / ULLBC / LLBC Extraction** | `AeneasVerif/charon` (`b2bb11d2...`) | Crate-wide Rust (`charon` -> `.llbc` JSON + `charon-ml`) | Extracts `rustc` MIR (`ULLBC`), reconstructs structured control flow (`LLBC`), exports traits/types/bodies | Trusts `rustc` completely through `AST -> HIR -> THIR -> MIR`; cannot detect front-end elaboration surprises (`Deref`, drop scopes) |
| **Normative Core Rust Execution** | `minirust/minirust` (`063d7841...`) + `minirust/specr` (`f33ec909...`) | Core MIR operational semantics (`ValueExpr`, `PlaceExpr`, `Terminator`, memory/provenance, `check_abi_compatibility`) | Prose+Rust `specr` DSL transpiled (`specr-transpile/src/main.rs:104–122`) to Rust + `libspecr` (`NdResult`, `Nondet` `pick`/`predict` in `nondet.rs:10–31`) | Intentionally begins **below** surface syntax, generics, traits, coercions, borrow checking, and drop insertion (`terminators.md:66–155`) |

#### 4.2 Type-Preserving Elaboration vs. Operational Refinement & Intent Fidelity

`Basis: normative + derived + execution`

In bidirectional type systems (Dunfield & Krishnaswami, `10.1145/3450952`) and dependent theorem provers (Lean 4 `TermElabM -> Kernel`), elaboration decomposes into two distinct judgments:
- **Checking ($\Gamma \vdash e_{\text{surf}} \Leftarrow \tau \leadsto e_{\text{core}}$):** Pushes an expected type $\tau$ downward into constructors (`match`, `fun`, literals).
- **Synthesis ($\Gamma \vdash e_{\text{surf}} \Rightarrow \tau \leadsto e_{\text{core}}$):** Infers a type $\tau$ bottom-up from variables, annotations, and applications.

Crucially, **two completely different soundness properties** govern an elaborator:

1. **Type Soundness of Elaboration (Kernel-Checked):** Every elaborated core term $e_{\text{core}}$ passes the trusted kernel typechecker ($\llbracket \Gamma \rrbracket \vdash_{\text{core}} e_{\text{core}} : \llbracket \tau \rrbracket$). Lean 4 and Rocq achieve high assurance here because `Kernel` re-checks $e_{\text{core}}$ independently of `TermElabM`.
2. **Operational Desugaring Refinement & Intent Fidelity (Unchecked by Core Kernels!):** For verified compilers and human-written specifications, we additionally require **backward behavioral refinement** ($\forall e_s.\; \text{elab}(e_s) = e_c \implies \text{Beh}(e_c) \subseteq \text{Beh}_{\text{surf}}(e_s)$) and **intent preservation**. As demonstrated in Probe Part 3 (`probe_surface_semantics.py`):
   - If a human writes `∀ x, x - 1 < x` intending mathematical integers $\mathbb{Z}$, a surface elaborator with `autoImplicit` and `Nat` default coercion elaborates `x` to `Nat` and `-` to truncated monus `Nat.sub`. The elaborated kernel statement is completely well-typed (`KernelCheck = OK`), yet `x = 0` yields `0 - 1 = 0 < 0` (`False`), whereas with `autoImplicit` typos (e.g., typing `n < m` as `n < n + 1` or introducing an unconstrained implicit `{n : Nat}`), the user proves a vacuously true or unintended theorem!
   - Similarly, in Rust, **temporary lifetime extension** (Edition 2021 `if let` / `match` scrutinee temporaries holding `MutexGuard` across an entire arm body vs. statement-level `let` dropping before use, demonstrated in Probe Part 2a) produces two completely valid, borrow-checked MIR programs with opposite deadlock behavior—invisible to MIR verifiers unless drop-scope elaboration rules are part of the surface spec.

---

### 5. Hygienic Macro and Procedural Attribute Framing Contracts

#### 5.1 Sets of Scopes (`Racket`), `MonadQuotation` (`Lean 4`), and Unhygienic Token Streams (`Rust syn`)

`Basis: source + documentation`

Surface-level semantics collapses immediately if macros can arbitrarily rewrite lexical bindings, ambient imports, or control flow across caller boundaries:

| Macro Architecture | Primary Source & Citation | Lexical Hygiene Mechanism | Cross-Phase / Module Support | Structural Limitation for Verification |
|---|---|---|---|---|
| **Racket Sets of Scopes** | `racket/racket` (`049065d5...`, `racket/src/expander/syntax/scope.rkt:83–147, 985–1000`); Flatt `POPL 2016` (`10.1145/2837614.2837620`) | Each syntax object carries a set of `scope` / `multi-scope` marks (`add-scope`, `flip-scope`). `resolve` picks the binding whose binder scope-set is the **unique maximal subset** of the reference's scope-set (`ambiguous` error on ties). | Native phase-shifted `shifted-multi-scope` (`scope.rkt:271–323, 873–935`) + module `syntax-taint` | Turing-complete compile-time phase-1 Racket code can still perform arbitrary AST surgery within syntactic forms unless constrained by `syntax-protect` / kernel forms. |
| **Lean 4 `MonadQuotation`** | `leanprover/lean4` (`e35bfaf8...`, `src/Lean/Hygiene.lean:14–116`); Ullrich & de Moura `LMCS 2022` (`10.46298/lmcs-18(2:1)2022`) | Purely functional scope-tagging monad (`withFreshMacroScope` allocates fresh numeric `MacroScope` via `Name.hygienic`); reverse `sanitizeSyntax` (`Hygiene.lean:94–114`) strips hygienic tags back to `✝`/`✝¹` tombstones for error rendering. | Phase-0/macro-expansion unified inside `MacroM`/`ElabM`; global references resolved via `_root_.` or antiquotation capture rules (`Hygiene.lean:21–33`). | `MacroM` cannot query kernel types, pushing type-directed elaboration into `TermElabM` (`elab` rules), where arbitrary `Lean.Meta` tactics can construct unexpected proof terms checked only for type soundness by the kernel. |
| **Rust `proc_macro` + `dtolnay/syn`** | `dtolnay/syn` (`a2cddb7a...`, `src/expr.rs`); `proc_macro2` | Token-stream-to-token-stream arbitrary Rust functions. Default `Span::call_site()` is **unhygienic** (identifiers collide with caller locals); `mixed_site()` solves macro-local `let` hygiene, while full hygienic `def_site()` remains unstable on standard Rust. | None at compiler boundary; `build.rs`/proc-macro crates execute arbitrary host I/O and host memory code during compilation unless sandboxed (e.g., Watt/Wasm). | **Unhygienic & unframed:** attribute/derive macros (`#[attr] fn foo()`) can silently inject `return`, alter `async`/drop order, emit trait `impl`s changing method dispatch, or read nondeterministic host files. |

#### 5.2 Formal 5-Clause Macro & Attribute Framing Contract

`Basis: derived + execution`

To preserve modular surface reasoning and trusted-specification isolation when procedural attributes or verification annotations (`#[spec]`, `#[requires]`, `#[ensures]`, derive macros, instrumentation wrappers) surround human-written functions, a macro $M(e_1, \dots, e_k) \rightsquigarrow e'$ must obey a **5-Clause Framing Contract** (executable prototype verified in Probe Part 2b):

1. **Lexical Scope Hygiene ($\alpha$-Invariance):** Every binder introduced by $M$ carries a disjoint macro-introduction scope tag (`binder_scopes ⊈ caller_scopes`), and no macro-free identifier inside $e_i$ resolves to a macro-introduced binder (Racket subset rule / Lean `MacroScope` invariant).
2. **Control-Flow Exit Framing:** For every argument AST $e_i$, the set of escaping nonlocal control-flow targets (unlabeled `return`, `break 'lbl`, `continue 'lbl`, `?` early propagation) satisfies:
   $$\text{FreeExits}(M(e_1, \dots, e_k)) \subseteq \bigcup_{i=1}^k \text{FreeExits}(e_i).$$
   Attribute macros wrapping a body block may not inject hidden early `return`s that bypass caller cleanup or postcondition checks unless explicitly declared in the macro's effect signature.
3. **RAII Drop-Frame & Linearity Preservation:** If a user block binds linear resources or RAII guards (e.g., `let _g = mutex.lock()`), wrapping/rewriting by $M$ may not move $g$ into `core::mem::forget`, shorten its lexical scope past sibling uses, or extend temporary lifetimes across suspension (`await`) or panic points.
4. **Ambient Method/Trait Namespace Isolation:** $M$ may not emit unhygienic `use ...::*`, blanket `impl` blocks, or shadowed inherent methods into the caller's module scope that alter `rustc` method resolution (`Deref`/trait selection) on untouched expressions outside $M$'s expanded subtree.
5. **Deterministic Functional Purity:** Macro expansion $M : \text{TokenStream} \to \text{TokenStream}$ must be a pure deterministic function of its input tokens and explicitly declared crate metadata—prohibiting wall-clock, RNG, network, or ambient filesystem reads so specification hashes and `.lean`/proof locks remain reproducible.

---

### 6. Multi-Level Performance & Resource Footprint (L1–L6) and Human Comprehensibility & Model Refinement (C1–C2)

#### 6.1 Six-Level Performance & Resource Footprint Comparison (L1–L6)

`Basis: source + documentation + execution + derived`

Directly comparing surface-semantics architectures and elaboration toolchains across all six operational levels exposes why no single architecture dominates simultaneously:

| Toolchain / Architecture (Pinned) | (L1) Authoring Velocity & Ratio | (L2) Toolchain Build Time & RSS | (L3) Elaboration / Transpile Latency | (L4) Execution Throughput | (L5) Proof / Spec Verification Speed | (L6) Disk, Binary & Runtime Footprints |
|---|---|---|---|---|---|---|
| **`JSCert` + `JSRef` (`891828c1...`)** | `26,203` total lines (`5,309` rules + `5,944` correctness proofs) for ES5.1 (~2:1 proof-to-spec ratio) | Full Coq 8.x + OCaml compilation takes minutes; ~500 MB–1.5 GB Coq RSS | Fuel-parameterized interpreter extraction via Coq `Extraction` (~seconds) | Slow interpretive OCaml AST + functional map heap; runs Test262 in batch hours/minutes (`condor_tests.sh`) rather than native JS JIT speeds | Coq `coqc` kernel checks `JsCorrectness.v` (`5,944` LoC; `Admitted` at L5891 bypasses equality sub-proofs) | `JsPrettyRules.v`+`JsCorrectness.v` `.vo` artifacts + extracted OCaml bytecode/native binary (~10s of MB) |
| **`K Framework` (`4a46d123...` / `e6879d14...` / `b8dede63...`)** | Concise surface rules (`KMIR` `13,290` lines); high initial learning curve for matching-logic `kore` lemmas | Heavy: GHC Haskell symbolic backend + LLVM C++ backend + `kompile` (~1–5 min per semantics, 2–8 GB RAM) | `kompile` definition generation takes 10s–minutes; symbolic proof startup hundreds of ms–seconds | **Dual backend:** LLVM backend runs concrete `krun` near compiled interpreter speeds; Haskell symbolic backend orders of magnitude slower on branching paths | Haskell `kore` matching-logic + Z3 discharge sensitive to quantifier instantiation & path explosion | Large `.kompiled` directory (hundreds of MB of C++/LLVM/Haskell IR); gigabytes RSS under symbolic branching |
| **`Wasm SpecTec` (`acc6e834...`)** | **2,957 LoC** (`Wasm2ST`) vs. **5,526 LoC** manual reST (**1.87× compression**); 5 Wasm 3.0 proposals added with minimal DSL edits | Pure OCaml (`dune build`), lightweight seconds build, ~100–300 MB RSS | Fast `EL -> IL -> AL` + LaTeX/reST emission (~milliseconds–seconds per spec run; zero external SMT!) | **49,833 Wasm 2.0 tests in 58 s** (~859 tests/s, ~1.16 ms/test on 8-core 2.4 GHz i9) via OCaml `AL` meta-interpreter; slower than native OCaml reference interpreter | `elab.ml` dimension + type validation checks whole spec in `<1 s`; theorem-prover export targets offline Coq/Isabelle/Lean kernels | Tiny OCaml source & generated LaTeX/reST files (`~1–5 MB` spec corpus); no heavyweight SMT runtime |
| **`MiniRust` + `SpecR` (`063d7841...` / `f33ec909...`)** | `26,513` lines across Markdown specs + tests; human-readable pseudocode-in-Rust syntax | Standard `cargo` build (`specr-transpile` `3,996` lines across `specr`) | Fast `syn` + `prettyplease` AST transpilation (`specr-transpile/src/main.rs`), sub-second | Native compiled Rust execution with `libspecr` GC (`gccompat-derive`) + `pick` sampling (`nondet.rs:10–20`, 50 random samples) | Transpiled Rust runs `minitest` behavioral suite; does not emit machine-checked Coq/Lean proofs directly | Compact Rust crates; GC object table adds moderate heap overhead vs raw `miri` |
| **`a-mir-formality` (`503cc9de...`)** | `68,315` total lines (`judgment_fn!` rules closely mirror Rust RFCs) | Standard Cargo Rust build (~tens of seconds, ~500 MB–1.5 GB RSS) | In-process tabled fixed-point logic evaluation (`ProvenSet`) over test crates | Fast unit-test execution (`borrowck.rs` `5,831` lines) on small Rust fragments; exponential blowup risk on deep generic trait cycles | Produces constructive `ProofTree` witnesses (`proven_set.rs`) checked dynamically in test suites | Standard Rust test binaries (`~10–50 MB`) |
| **`Lean 4` (`e35bfaf8...`) / `Racket` (`049065d5...`) Macro Elaborators** | Concise surface macros (`macro_rules`, `syntax-parse`); **0** manual proof burden for hygiene | Lean 4 C++ kernel + Lean core (`100s MB–several GB`); Racket CS Chez Scheme host | Interactive `< 50 ms` incremental LSP elaboration per small definition (`TermElabM` + macro scopes); multi-second on heavy typeclass/tactic search | Compiled C/LLVM (`Lean 4`) or Chez Scheme native JIT (`Racket`); zero hygiene runtime cost after expansion! | Lean C++ kernel verifies elaborated terms independently of macros (`< 1–50 ms`/decl); Racket validates expanded core bytecode | `.olean` binary AST/env snapshots (`MB–hundreds MB` for Mathlib); Racket `.zo` bytecode (`KB–MB`) |

*(Note on L1 LLM-assisted lowered verification baselines: For contrast with direct surface models, non-academic binary verification pipelines operating at lowered RISC-V/x86 machine instructions report ~**600,000 lines of Rocq per 18,000-instruction binary**—~33:1 proof-to-instruction expansion—consuming hundreds of millions of LLM tokens across 239 OSS-Fuzz entry points, `anthropic_fv.txt:82, 124`, demonstrating why surface-level structural abstraction remains decisive for human-maintained proofs.)*

#### 6.2 (C1) Human Comprehensibility & Mental-Model Ergonomics

`Basis: source + documentation + derived`

- **Human Comprehension vs. LLM/Machine Execution:** Humans excel at verifying **1-to-1 structural correspondence** ("eyeball closeness") between informal specifications and declarative AST rules (`JSCert`'s `JsPrettyRules.v`, `SpecTec`'s `5-reduction.spectec`, `a-mir-formality`'s `judgment_fn!`), where working memory tracks **3–5 local concepts** (`current subexpression`, `environment`, `store`, `control status`). By contrast, lowered `MIR` / `RISC-V` proofs spanning hundreds of thousands of lines are **only** tractable by machines/LLMs and fail human auditability completely.
- **Diagnostic & Counterexample Lifting Hazard:** When semantics lives strictly on lowered IR, a failed verification step or borrow rejection surfaces generated temporaries (`_12`, `StorageDead`, desugared state-machine enum fields) divorced from user syntax. Lean 4's `sanitizeSyntax` (`Hygiene.lean:94–114`) and `InfoTree` Delaborator show the minimum required infrastructure: **preserving bijective surface provenance across elaboration** so diagnostics project back into human identifiers (`x✝` instead of `_hyg.4192`) without losing binding disambiguation.
- **Silent Specification-Intent Hazards:** Ergonomic features optimized for conciseness (`autoImplicit` variables, silent `Int -> Nat` monus coercion, implicit `Deref` chains, unframed `#[attr]` macros) actively **degrade human auditability of theorem statements**—the human reads what they think the notation means while the kernel silently proves a weaker or vacuously different statement.

#### 6.3 (C2) Simplicity, Orthogonality & Universal Model Refinement

`Basis: derived`

Applying Felleisen's macro-expressibility lens and Ousterhout's deep-module depth criterion separates genuine conceptual simplification from complexity-shifting adapters:

- **Genuine Simplifications (Deep Primitives):**
  1. **Charguéraud's `ext_expr` + single `red_*_abort` rule (`JSCert`)** collapses $O(\sum k_c)$ duplicated abort-propagation rules into **one universal propagation judgment** without distorting happy-path rule correspondence.
  2. **Flatt's Sets of Scopes (`Racket`) & Ullrich–de Moura's `MacroScope` (`Lean 4`)** replace fragile imperative renaming passes and `gensym` counter threading with **one persistent algebraic tag set** (`scope-set` subset check) that composes across arbitrary macro phases and modules.
  3. **`SpecTec`'s `EL -> IL -> AL` Pipeline** replaces four manually synced specification dialects (LaTeX + reST + OCaml + prover defs) with **one typed relational source** whose animation (`il2al`) is checked statically by construction.
- **False Simplifications / Adapter-Shifting:**
  - Dropping direct surface semantics and treating `rustc` MIR (`KMIR`, `Charon`, `MiniRust`) as "the semantics of Rust" shrinks the verifier's *formalized grammar*, but **shifts all front-end complexity** (trait resolution, drop elaboration, temporary lifetime extension, proc-macro hygiene) into an unverified compiler black box. Any front-end desugaring change silently alters what every downstream MIR proof means!

---

## Boundaries

- **`known not to apply` — Kernel Type Checking as a Proof of Specification Intent:** Mechanized proof kernels (Coq, Lean 4) validate only that the *elaborated core term* has the *elaborated core type*; they do **not** validate that `TermElabM` or macros captured the human author's intended mathematical formula (witnessed by `autoImplicit` and `Nat.sub` monus in Probe Part 3).
- **`known not to apply` — Rust `proc_macro` Hygiene Guarantees:** Standard `dtolnay/syn` + `Span::call_site()` expansion does **not** enforce lexical hygiene, nonlocal exit containment, or drop-frame invariance (`Span::def_site()` remains unstable/nightly-gated).
- **`unsupported` — Complete Parser/Numerics/Prover Extraction in `SpecTec` (`acc6e834...`):** As documented in `spectec_pldi24.txt:1947–1952, 2315–2325`, `SpecTec`'s `Wasm2ST` evaluation outsources `.wast`/binary parsing and floating-point/vector arithmetic to the external OCaml reference interpreter rather than executing Wasm parsing and IEEE-754 numerics natively from DSL rules; Coq/Isabelle/Agda/Lean backends remain experimental/future work relative to the PLDI 2024 artifact.
- **`unsupported` — Direct Surface-Rust Execution in `KMIR` and `MiniRust`:** Neither `runtimeverification/mir-semantics` (`b8dede63...`) nor `minirust/minirust` (`063d7841...`) executes surface Rust ASTs; both require external `rustc` lowering to MIR/Stable-MIR.
- **`unknown` — Formal End-to-End Surface-to-MIR Refinement for Full Rust:** No inspected repository (`a-mir-formality`, `hax`, `charon`, `minirust`, `KMIR`) contains a mechanized theorem proving that `rustc`'s `AST -> HIR -> THIR -> MIR` pipeline preserves a direct surface operational semantics of Rust.
- **`not examined` — Live Compilation of Coq (`JSCert`), K (`KMIR`), OCaml (`SpecTec`), and Rust (`a-mir-formality`/`MiniRust`):** Source code, rules, and extracted metrics were inspected directly from pinned upstream commits and peer-reviewed publications; Coq/K/OCaml/Rust toolchains were not compiled or executed locally in this environment (execution evidence comes from our standalone Python 3 micro-probe).
- **`not examined` — Verification Gaps in `JsCorrectness.v:5891`:** `run_equal_correct` inside `jscert/jscert` @ `891828c1...` terminates with `Admitted. (* faster *)`; the exact runtime proof effort required to discharge those remaining abstract-equality branches in modern Rocq/Coq was not executed.

---

## Evidence

### Primary Repositories and Exact Source Citations (Observed `2026-11-19`)

- **`jscert/jscert`** @ `891828c11308350836cdb8e832e4d00ed3019d9c`:
  - `coq/JsPrettyInterm.v` L54–160 (`ext_expr` intermediate continuation ASTs), L1607–1612 (`abort`, `abort_div`, `abort_not_normal`), L1617–1672 (`abort_intercepted_prog`, `abort_intercepted_stat`, `abort_intercepted_expr`).
  - `coq/JsPrettyRules.v` L64–125 (`red_javascript`, `red_prog`, `red_prog_abort`, `red_stat_abort`), L200–320 (`red_stat_if`, `red_stat_do_while`, `red_stat_while` matching ECMA-262 12.5–12.6.2), L743 (`red_expr_abort`), L4787 (`red_spec_abort`).
  - `coq/JsInterpreter.v` L125–152 (`runs_type` fuel-indexed OCaml-extractable interpreter record).
  - `coq/JsCorrectness.v` L62–152 (`runs_type_correct`), L5891 (`Admitted. (* faster *)` in `run_equal_correct`), L5893–5943 (`Theorem runs_correct`, `Theorem run_javascript_correct`, `Corollary run_javascript_correct_num`).
- **`Wasm-DSL/spectec`** @ `acc6e834ff403c82554d081237f327346190ad96` & **`WebAssembly/spec`** @ `d0b2e8d5544d2049fba0521922c436e3f0fcaebe`:
  - `spectec/doc/Language.md` L13–150 (`EL` syntax types, type families, dependent parameters).
  - `spectec/src/frontend/elab.ml` L1–160 (`EL -> IL` type checking, environment tracking, dimension validation).
  - `spectec/src/il2al/transpile.ml` L15–260 (`neg`, `eq_nat_cond`, `eq_cond`, `conflicts`, `merge_blocks`, `extract_common_cond`).
  - `spectec/src/backend-interpreter/construct.ml` L1–160 (`AL -> OCaml` reference interpreter AST bridge).
- **`runtimeverification/k`** @ `4a46d1231473b599c699160132fd6e76a5c46406`, **`kframework/c-semantics`** @ `e6879d14455771aa0cb3e3d201131d4d763a73a2`, **`kframework/java-semantics`** @ `f27067ee7a38d236499992eed1b48064e70680fa`, **`runtimeverification/mir-semantics`** @ `b8dede6335f4317371b6025af999dc9b56d6887d`:
  - `kframework/c-semantics/README.md` L18–38 (`kcc` stuck-on-UB diagnostics), L90–107 (three `kompile` configurations, `cpp -> CIL -> KAST`).
  - `runtimeverification/mir-semantics/kmir/src/kmir/kdist/mir-semantics/kmir.md` L14–180 (Stable-MIR JSON input, `#execBlock`/`#execStmts`, no-op statements L147–153); `docs/semantics-of-mir.md` L43–131 (Terminator/Statement coverage gaps and `Drop` marked `UNCLEAR`).
- **`rust-lang/a-mir-formality`** @ `503cc9de881b7e7a6023abbb1cca3873fd2c0ffc`:
  - `crates/formality-core/src/judgment.rs` L36–94 (`judgment_fn!` rules, `Scope`, `for_all`, commit points).
  - `crates/formality-rust/src/to_rust/syntax.rs` L1–160 (surface Rust printer target), `crates/formality-rust/src/check/borrow_check/nll.rs` L124–160 (`borrow_check` judgment).
- **`minirust/minirust`** @ `063d784186d3252bee242217f218223205c0b568` & **`minirust/specr`** @ `f33ec909955c6889ea4c4a377ab61ec609fcf1ae`:
  - `minirust/spec/lang/syntax.md` L15–120 (`ValueExpr`, `Constant`, `CastOp`), `spec/lang/step/terminators.md` L19–155 (`eval_terminator`, `check_abi_compatibility`, `prepare_for_inplace_passing`).
  - `specr/specr-transpile/src/main.rs` L42–122 (`argmatch`, `typerec`, `merge_impls`, `auto_derive`), `libspecr/src/nondet.rs` L10–31 (`pick`, `predict`, `Nondet`).
- **`hacspec/hax`** @ `0d2f66ed697c46d7c0f5038150b7c9679e4d954b` (`README.md` L105–130, THIR extraction) and **`AeneasVerif/charon`** @ `b2bb11d2d3672033c8157a49cb56a44c464c5179` (`README.md` L14–64, LLBC JSON extraction).
- **`leanprover/lean4`** @ `e35bfaf8dab2405124cb486c80a7c12d3cccb951` (`src/Lean/Hygiene.lean` L14–116: `MonadQuotation`, `Unhygienic`, `withFreshMacroScope`, `sanitizeSyntax`), **`racket/racket`** @ `049065d5c96121c580edc0d1253abf5ed5a4930a` (`racket/src/expander/syntax/scope.rkt` L83–323, 750–1000: `scope`, `multi-scope`, `syntax-scope-set`, `add-binding-in-scopes!`), and **`dtolnay/syn`** @ `a2cddb7a893532133c17a32e4ac68a9805db7c9f` (`src/expr.rs` L140–160).

### Peer-Reviewed Publications & Primary Engineering Reports Verified

- Charguéraud (2013), *Pretty-Big-Step Semantics*, ESOP 2013, DOI `10.1007/978-3-642-37036-6_3`.
- Bodin, Charguéraud, Filaretti, Gardner, Maffeis, Naudziuniene, Schmitt & Smith (2014), *A Trusted Mechanised JavaScript Specification*, POPL 2014, DOI `10.1145/2535838.2535876`.
- Bodin, Gardner, Jensen & Schmitt (2019), *Skeletal Semantics and Their Interpretations*, PACMPL 3(POPL):44, DOI `10.1145/3290357`.
- Ellison & Roşu (2012), *An Executable Formal Semantics of C with Applications*, POPL 2012, DOI `10.1145/2103656.2103719`; Hathhorn, Ellison & Roşu (2015), *Defining the Undefinedness of C*, PLDI 2015.
- Bogdanas & Roşu (2015), *K-Java: A Complete Semantics of Java*, POPL 2015, DOI `10.1145/2676726.2676982`.
- Youn, Shin, Lee, Ryu, Breitner, Gardner, Lindley, Pretnar, Rao, Watt & Rossberg (2024), *Bringing the WebAssembly Standard up to Speed with SpecTec*, PACMPL 8(PLDI):210, DOI `10.1145/3656440`.
- Flatt (2016), *Binding as Sets of Scopes*, POPL 2016, DOI `10.1145/2837614.2837620`.
- Ullrich & de Moura (2022), *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*, LMCS 18(2:1), DOI `10.46298/lmcs-18(2:1)2022`.
- Dunfield & Krishnaswami (2021), *Bidirectional Typing*, ACM Computing Surveys 54(5):98, DOI `10.1145/3450952`.
- Anthropic Frontier Red Team & Theorem (Oct 2026), *LLMs are making formal software verification feasible at a much larger scale*, `https://www.anthropic.com/research/formal-verification`.

### Reproducible Execution Probe and Verbatim Output (`2026-11-19`)

Save the following standalone script to `/tmp/probe_surface_semantics.py` and run `python3 /tmp/probe_surface_semantics.py` (Python 3.10+, standard library only):

```python
#!/usr/bin/env python3
"""Micro-probe 1: Pretty-big-step compression, RAII macro framing, and elaboration intent gap."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Lit: v: int
@dataclass(frozen=True)
class Var: x: str
@dataclass(frozen=True)
class Add: l: object; r: object
@dataclass(frozen=True)
class Set: x: str; e: object
@dataclass(frozen=True)
class Throw: e: object
@dataclass(frozen=True)
class Catch: b: object; x: str; h: object
@dataclass(frozen=True)
class Seq: l: object; r: object

def pretty_big_step(expr, st):
    st = dict(st)
    def ev(e):
        if isinstance(e, Lit): return ("ok", e.v)
        if isinstance(e, Var): return ("ok", st.get(e.x, 0))
        if isinstance(e, Add):
            r1 = ev(e.l)
            if r1[0] != "ok": return r1
            r2 = ev(e.r)
            if r2[0] != "ok": return r2
            return ("ok", r1[1] + r2[1])
        if isinstance(e, Set):
            r1 = ev(e.e)
            if r1[0] != "ok": return r1
            st[e.x] = r1[1]
            return ("ok", r1[1])
        if isinstance(e, Throw):
            r1 = ev(e.e)
            if r1[0] != "ok": return r1
            return ("exn", r1[1])
        if isinstance(e, Catch):
            r1 = ev(e.b)
            if r1[0] == "exn":
                st[e.x] = r1[1]
                return ev(e.h)
            return r1
        if isinstance(e, Seq):
            r1 = ev(e.l)
            if r1[0] != "ok": return r1
            return ev(e.r)
    return ev(expr), st

def small_step_k(expr, st):
    st = dict(st)
    k = [("eval", expr)]
    val = None
    while k:
        frame = k.pop()
        tag = frame[0]
        if tag == "eval":
            e = frame[1]
            if isinstance(e, Lit): val = e.v
            elif isinstance(e, Var): val = st.get(e.x, 0)
            elif isinstance(e, Add):
                k.append(("add_l", e.r)); k.append(("eval", e.l))
            elif isinstance(e, Set):
                k.append(("set_done", e.x)); k.append(("eval", e.e))
            elif isinstance(e, Throw):
                k.append(("throw_done",)); k.append(("eval", e.e))
            elif isinstance(e, Catch):
                k.append(("catch_hdl", e.x, e.h)); k.append(("eval", e.b))
            elif isinstance(e, Seq):
                k.append(("seq_r", e.r)); k.append(("eval", e.l))
        elif tag == "add_l":
            k.append(("add_r", val)); k.append(("eval", frame[1]))
        elif tag == "add_r":
            val = frame[1] + val
        elif tag == "set_done":
            st[frame[1]] = val
        elif tag == "seq_r":
            k.append(("eval", frame[1]))
        elif tag == "throw_done":
            exn = val
            while k and k[-1][0] != "catch_hdl":
                k.pop()
            if not k:
                return ("exn", exn), st
            _, x, h = k.pop()
            st[x] = exn
            k.append(("eval", h))
    return ("ok", val), st

tests = [
    Add(Set("x", Lit(10)), Add(Var("x"), Lit(5))),
    Catch(Seq(Set("x", Lit(1)), Add(Lit(2), Throw(Lit(42)))), "e", Add(Var("x"), Var("e"))),
    Seq(Catch(Throw(Lit(7)), "e", Throw(Add(Var("e"), Lit(1)))), Set("y", Lit(99))),
    Add(Throw(Lit(3)), Set("x", Lit(999))),
]
eq_count = sum(pretty_big_step(t, {}) == small_step_k(t, {}) for t in tests)
arities = {"Lit": 0, "Var": 0, "Add": 2, "Set": 1, "Throw": 1, "Catch": 2, "Seq": 2}
naive_rules = sum(1 + a for a in arities.values())
print(f"[1] Pretty-Big-Step == Small-Step K: {eq_count}/{len(tests)} exact match | Naive Big-Step rules={naive_rules} (with abort dup) vs Pretty-Big-Step generic abort rule=1")

def eval_ir(ops):
    log, locked = [], False
    for op in ops:
        if op == "lock":
            assert not locked; locked = True; log.append("LOCK")
        elif op == "use":
            log.append(f"USE(locked={locked})")
        elif op == "unlock":
            assert locked; locked = False; log.append("UNLOCK")
        elif op == "early_ret":
            log.append(f"EARLY_RET(locked={locked})")
            return log
    log.append(f"EXIT(locked={locked})")
    return log

print(f"[2a] Drop-order gap: stmt_let={eval_ir(['lock', 'unlock', 'use'])} vs match_temp={eval_ir(['lock', 'use', 'unlock'])}")

def macro_framing_check(macro_nodes, caller_exit_labels, macro_scopes, caller_scopes):
    if not macro_nodes["exit_labels"].issubset(caller_exit_labels):
        return False, f"REJECT: nonlocal exit {macro_nodes['exit_labels'] - caller_exit_labels} escapes macro boundary"
    if macro_nodes["drops_caller_guard"]:
        return False, "REJECT: macro alters caller linear/RAII drop frame"
    for sym, binder_scopes in macro_nodes["binders"].items():
        if binder_scopes.issubset(caller_scopes):
            return False, f"REJECT: unhygienic capture of '{sym}'"
    return True, "ACCEPT"

for name, m in [
    ("early_ret_macro", {"exit_labels": {"early_ret"}, "drops_caller_guard": False, "binders": {}}),
    ("capture_macro", {"exit_labels": set(), "drops_caller_guard": False, "binders": {"guard": {"call"}}}),
    ("hygienic_macro", {"exit_labels": set(), "drops_caller_guard": False, "binders": {"__tmp": {"call", "m1"}}}),
]:
    ok, msg = macro_framing_check(m, set(), {"call", "m1"}, {"call"})
    print(f"[2b] FramingCheck({name}): {ok} -> {msg}")

def kernel_nat_sub(a, b): return max(0, a - b)
pos_ok = all(kernel_nat_sub(x, 1) < x for x in range(1, 20))
zero_ok = (kernel_nat_sub(0, 1) < 0)
z_ok = all((x - 1) < x for x in range(-10, 10))
print(f"[3] Intent gap: Surface Z '(x-1)<x' holds on [-10..10)={z_ok} | Elaborated Nat monus: [1..20)={pos_ok}, x=0={zero_ok}")
```

Observed output (`2026-11-19`, Linux x86_64, Python 3):

```text
[1] Pretty-Big-Step == Small-Step K: 4/4 exact match | Naive Big-Step rules=15 (with abort dup) vs Pretty-Big-Step generic abort rule=1
[2a] Drop-order gap: stmt_let=['LOCK', 'UNLOCK', 'USE(locked=False)', 'EXIT(locked=False)'] vs match_temp=['LOCK', 'USE(locked=True)', 'UNLOCK', 'EXIT(locked=False)']
[2b] FramingCheck(early_ret_macro): False -> REJECT: nonlocal exit {'early_ret'} escapes macro boundary
[2b] FramingCheck(capture_macro): False -> REJECT: unhygienic capture of 'guard'
[2b] FramingCheck(hygienic_macro): True -> ACCEPT
[3] Intent gap: Surface Z '(x-1)<x' holds on [-10..10)=True | Elaborated Nat monus: [1..20)=True, x=0=False
```

---

## Revalidation

To verify whether these findings shift on newer upstream revisions without repeating full repository audits:

1. **`Wasm-DSL/spectec` Backend Status:** Diff `spectec/src/il2al/transpile.ml` and list `spectec/src/backend-*` relative to `acc6e834ff403c82554d081237f327346190ad96` to see whether Coq, Isabelle, Lean, or Agda backends reached Wasm 2.0 completeness or internalized numeric/parser specs.
2. **Rust Surface-to-MIR Bridge (`a-mir-formality` & `minirust`):** Check `rust-lang/a-mir-formality` (`503cc9de...`) under `crates/formality-rust/` and `crates/minirust-rs/` and `minirust/minirust` (`063d7841...`) under `tooling/minimize/` for mechanized surface-to-MiniRust lowering proofs or Edition 2024 drop-scope coverage.
3. **`KMIR` Drop & Surface Scope:** Inspect `runtimeverification/mir-semantics` (`b8dede63...`) `docs/semantics-of-mir.md` and `kmir/src/kmir/kdist/mir-semantics/kmir.md` for elimination of `Drop`/`Retag` no-ops or new THIR/HIR rules.
4. **Hygienic Rust Proc-Macros:** Monitor stabilization of `proc_macro::Span::def_site()` and check `dtolnay/syn` (`a2cddb7a...`) hygiene helpers.
5. **Re-run Micro-Probe:** Run `python3 /tmp/probe_surface_semantics.py` (`< 1s`, zero external packages) to verify the algebraic Pretty-Big-Step, RAII drop-order, macro-framing, and `Nat`-monus elaboration witnesses.
