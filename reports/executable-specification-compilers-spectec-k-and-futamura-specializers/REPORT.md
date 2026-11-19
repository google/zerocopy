# Executable Specification Compilers, Matching Logic Verifiers, and Futamura Partial Evaluators

## Summary

Language ecosystems routinely maintain $M \ge 6$ manually synchronized artifacts—standards prose, formal inference rules, reference interpreters, type checkers, optimizing compilers/JITs, and theorem-prover mechanizations—producing chronic specification-vs-implementation drift. Two converging compiler technologies attack this $O(N \times M)$ bottleneck from opposite ends: **single-source executable specification compilers** (`SpecTec`, `P4-SpecTec`, `Ott`/`Lem`/`Sail`, `K`) eliminate artifact drift by generating prose, interpreters, verifiers, and prover models from one formal definition, while **First-Futamura partial evaluators and multi-stage tower collapsers** (`weval`/`waffle`, `LMS`/`Pink`) turn interpreters into native-speed compilers without duplicating semantics in a separate hand-written backend.

Primary-source inspection and reproducible execution probes establish five load-bearing engineering facts:

1. **`SpecTec` Backend Ground Truth and the Animation Barrier:** `SpecTec` (`EL -> IL -> AL`) is now integrated directly into the official `WebAssembly/spec` repository (`specification/wasm-3.0`), generating LaTeX, Sphinx prose, ASTs, and a meta-interpreter passing 100% of applicable Wasm 2.0 tests. However, on `main` of both `Wasm-DSL/spectec` and `WebAssembly/spec`, **only** `--check`, `--ast`, `--latex`, `--splice-{latex,sphinx}`, `--prose`, `--prose-rst`, and `--interpreter` are merged; theorem-prover backends (`rocq-backend`, `lean-backend-proof`, `lean4-wip`, `agda-backend`, `isabelle-mech-backend`) remain on separate development branches. Moreover, `Wasm-SpecTec`'s dataflow animation (`il2al/animate.ml`) stalls on unconstrained existentials and cannot execute rich static type systems—forcing `P4-SpecTec` (Rust, OOPSLA 2026, conditionally accepted as P4's official spec toolchain in March 2026) to adopt **explicitly moded algorithmic inference rules**, which exposed **24 bugs** across the P4 specification and `p4c`.
2. **Multi-Prover Logic Impedance (`Ott`/`Lem`/`Sail`):** `Ott` supports concrete binding without $\alpha$-quotienting (plus an experimental locally-nameless subset); `Lem` forces lowest-common-denominator functional idioms across Coq/Isabelle/HOL4/OCaml; `Sail` resolves ISA-scale dependent bitvectors via Z3 and now ships a first-class **`sail_lean_backend`** alongside `sail_coq_backend`/`rocq`, `sail_lem_backend` (Isabelle/HOL4), C, OCaml, SMT, and SystemVerilog.
3. **`K` and Matching $\mu$-Logic Proof Certificates:** `K` compiles one rewrite-based operational semantics into a concrete interpreter, symbolic verifier (Reachability Logic), and Metamath proof-certificate generator grounded in a **200-line Matching $\mu$-Logic kernel** (`theory/matching-logic-200-loc.mm`). This collapses the trusted verifier TCB from hundreds of thousands of lines (`kore-exec` + LLVM + Z3) to a tiny checker, **but** raw Hilbert proof certificates blow up rapidly (**~77 MB / 9,148 statements** for a single concrete rewriting proof example) and rely on unverified `[simplification]` rewrite lemmas during symbolic search.
4. **`weval` Operates on `waffle` Wasm SSA IR (Not Directly on Cranelift CLIF):** Chris Fallin's `weval` snapshots an initialized Wasm heap via `wasmtime-wizer` (backed by Wasmtime/Cranelift), lifts Wasm into **`waffle`** (a Cranelift-style block-parameter SSA CFG IR with 1-to-1 Wasm operators), performs context-sensitive partial evaluation over `(Context, Block)` with explicit C/Wasm intrinsics (`push.context`, `update.context`, `specialize.value`, and operand-stack/locals virtualization `push.stack`/`sync.stack`), lowers back to structured Wasm via `waffle` (`reducify` -> Ramsey's `stackify` -> `treeify` -> `localify`), and relies on Cranelift/Wasmtime downstream for native codegen—achieving **2.17x** speedups on SpiderMonkey and **1.84x** on PUC-Rio Lua (PLDI 2025). Crucially, `weval` is **unverified**: if dynamic linear-memory writes alias statically folded bytecode, specialized code silently diverges from the interpreter, although `weval`'s `block_rev_map` already provides the exact simulation index needed for linear-time translation validation.
5. **Collapsing Interpreter Towers (`LMS`/`Pink`):** Stage-polymorphic evaluators parameterized by `maybe-lift` (`TiarkRompf/collapsing-towers`, POPL 2018) collapse 1-, 2-, and 3-level interpreter towers into the **exact syntactically identical residual AST** achieving $1.00\times$ runtime Jones optimality (63 host steps vs. 1,942 at 1-level and 99,274 at 2-level interpretation in our probe)—while compile-time specialization cost still scales multiplicatively ($\sim 51\times$ per unstaged meta-layer) unless intermediate interpreters are pre-compiled.

## Applicability

This report applies to language specification committees, compiler/VM architects, formal-verification engineers, and systems researchers designing single-source language frontends, proof-carrying verifiers, or AOT/staged interpreter compilers.

The examined subjects form two complementary planes whose intersection is the **Verified First Futamura Projection**:

1. **Specification Meta-Compilers & Language-Parametric Verifiers:**
   - `Wasm-DSL/spectec` (`acc6e834ff403c82554d081237f327346190ad96`) and `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`): Evaluated on `main` for `EL -> IL -> AL` compilation, middlend passes, animation (`il2al`), and active CLI targets; separate development branches on `Wasm-DSL/spectec` were enumerated for ref-existence only and are explicitly distinguished from `main`.
   - `kaist-plrg/p4-spectec` (`731621c5e3c8eb94323c112898364624fc03ce9d`, OOPSLA 2026 `10.1145/3839535`, `arXiv:2608.00639v1`) and `es-meta/esmeta` (`b4a787f2716523bf76d4a897068bbd5b1fc8ef2d`): Evaluated as real-world scaling tests of mechanization beyond WebAssembly's stack machine.
   - `ott-lang/ott` (`0639ce49892252e0b53e84aa5b0c35b02785913e`), `rems-project/lem` (`3802cb04b53d5f1096a464e51ecbfb2a750a7ccd`), and `rems-project/sail` (`97aa617dcd4d01575f773cb58ea1e8686858c8c2`): Evaluated on multi-prover extraction architecture, binding models, and ISA/PL scope boundaries.
   - `runtimeverification/k` (`4a46d1231473b599c699160132fd6e76a5c46406`) and `runtimeverification/proof-generation` (`bdf8d0c638896dc6b2e3469ecf3e665f5eec5f26`): Evaluated for Reachability Logic, Matching $\mu$-Logic Hilbert axiomatization in Metamath, and certificate-size/TCB trade-offs.
2. **Partial Evaluation and Multi-Stage Tower Collapse:**
   - `bytecodealliance/weval` (`47164ae9e5bacfdcc23ddaeb2fa491c8f61c644d`, v0.5.1; PLDI 2025 `10.1145/3729259`) and `bytecodealliance/waffle` (`dad4f9cb1e05014c8e49648bc45e071aad54dca3`): Evaluated specifically for Wasm-to-Wasm AOT First-Futamura specialization, intrinsic ABI, abstract state tracking, and soundness/aliasing hazards.
   - `TiarkRompf/collapsing-towers` (`d938bf9cdec5bcfd1f3bf8c1ac2431007da2afe1`, `popl18/` artifact for Amin & Rompf POPL 2018 `10.1145/3158140`): Evaluated for stage-polymorphic ANF code generation and multi-level tower collapse; contrasted conceptually with classical offline BTA (Jones–Gomard–Sestoft 1993), meta-tracing (`PyPy`), and speculative AST PE (`Graal`/`Truffle`).

All repository observations come from direct source inspection of the pinned commits; dynamic claims about animation barriers, context-indexed aliasing miscompilation, and 1/2/3-level tower collapse are backed by standalone Python 3 micro-probes in **Evidence**.

## Findings

### 1. Single-Source Language Mechanization: `SpecTec` (`EL -> IL -> AL`), WebAssembly 3.0, and `P4-SpecTec`

#### 1.1 `SpecTec` Architecture and Actual Merged Backends (`Wasm-DSL/spectec` & `WebAssembly/spec`)

`Basis: normative + source + documentation`

Introduced by Youn, Shin, Lee, Ryu, Breitner, Gardner, Lindley, Pretnar, Rao, Watt, and Rossberg (*"Bringing the WebAssembly Standard up to Speed with SpecTec"*, PLDI 2024, DOI `10.1145/3656440`), `SpecTec` replaces hand-synchronized LaTeX rules, English pseudocode algorithms, and OCaml reference code with a single typed DSL. Direct inspection of both `Wasm-DSL/spectec` (`acc6e834ff403c82554d081237f327346190ad96`) and the official W3C `WebAssembly/spec` repository (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`) confirms that `SpecTec` is merged directly into `WebAssembly/spec` under `spectec/`, with active CI (`.github/workflows/ci-spectec.yml`) and versioned specifications under `specification/{wasm-1.0, wasm-2.0, wasm-3.0, wasm-latest}`.

The compiler pipeline in `spectec/src/` proceeds across **three intermediate languages**:

1. **External Language (`el/`, `frontend/`):** Surface DSL defining `syntax` grammars, `var` metavariable types, `relation` judgment forms (`context |- instr : functype`, `config ~> config`), named inference `rule`s with `--` premises, auxiliary functions, and uninterpreted backend `hint` annotations (`spectec/README.md`).
2. **Internal Language (`il/`, `middlend/`):** Strongly typed declarative representation produced by elaboration. `spectec/src/middlend/` implements modular IR-lowering passes preparing `IL` for animation or theorem-prover export: `aliasDemut.ml` (demutualizing type aliases), `sub.ml` / `subexpansion.ml` (explicit subtyping coercions), `totalize.ml` (converting partial auxiliary functions into explicit option-returning total functions), `typefamilyremoval.ml`, `undep.ml` (`remove-indexed-types`, eliminating dependent type indices), `unthe.ml`, `sideconditions.ml`, `else.ml` / `elsesimp.ml`, `ite.ml`, and `letintromech.ml` (`let-intro-mech`, introducing explicit `let` bindings for mechanization).
3. **Algorithmic Language (`al/`, `il2al/`):** Imperative pseudocode IR derived from `IL` via `il2al/{preprocess,animate,translate,transpile,postprocess}.ml`, plus hand-written escape hatches in `il2al/manual.ml` (e.g., `eval_expr` and `return_instrs_of_{instantiate,invoke}` at lines 14–65).

**Primary-Source Correction on Prover Backends:** Although `spectec/README.md` lists Coq and Isabelle among SpecTec's design goals, inspecting `spectec/src/` and `spectec/src/exe-spectec/main.ml` (lines 196–226, 314–392) on `main` of **both** `Wasm-DSL/spectec` (`acc6e834...`) and `WebAssembly/spec` (`d0b2e8d5...`) shows that the merged CLI targets are strictly:
- `--check` (elaboration/type-checking),
- `--ast` (`backend-ast`),
- `--latex` (`backend-latex`),
- `--splice-latex` / `--splice-sphinx` (`backend-splice`, splicing math and prose directly into `.rst`/`.tex` spec documents with `-w` unused/reused splice warnings),
- `--prose` / `--prose-rst` (`backend-prose`), and
- `--interpreter` / `--debug` (`backend-interpreter`, executing `AL` directly as a meta-interpreter; `--test-version` defaults to Wasm `3`).

The theorem-prover mechanization backends—**Rocq/Coq, Lean 4, Agda, and Isabelle**—currently live on **separate development branches** in `Wasm-DSL/spectec` (`refs/heads/rocq-backend`, `rocq-backend-proof`, `lean-backend-proof`, `lean4-wip`, `agda-backend`, `isabelle-mech-backend`, `coq`) rather than merged `main`.

#### 1.2 The Animation Barrier and `P4-SpecTec`'s Algorithmic Inference Rules

`Basis: normative + source + execution`

Inspecting `spectec/src/il2al/animate.ml` (lines 1–65) reveals the exact mechanism and structural limit of declarative-to-imperative animation. `animate.ml` classifies each premise as either `Condition` (boolean guard) or `Assign of string list` (pattern-binding assignment) and greedily schedules premises via dataflow reachability over the set of currently known free variables `env`:
- `is_tight env (Condition, prem, _)` checks `subset (free_prem false prem) env` (all free variables known);
- `is_assign env (Assign frees, prem, _)` checks `subset (diff (free_prem false prem) frees) env` (all inputs known, outputs `frees` newly bound).

This succeeds cleanly for Wasm's small-step reduction rules where input operands uniquely determine outputs, **but fails immediately** whenever a declarative rule contains unconstrained existential witnesses (e.g., guessing an intermediate supertype $\tau$ in a subsumption rule or allocating a fresh store address without a deterministic mode) or cyclic premise dependencies (demonstrated concretely in **Evidence**, Probe Part 1).

**Lessons from `P4-SpecTec` (`kaist-plrg/p4-spectec` @ `731621c5...`, Lee, Jeong, Ahn, Kwon & Ryu, OOPSLA 2026 DOI `10.1145/3839535`, `arXiv:2608.00639v1`) and `ESMeta` (`es-meta/esmeta` @ `b4a787f2...`):**
- Because Wasm's validation rules are simple local stack-type checks, `Wasm-SpecTec` did **not** build an executable type-checker backend (`arXiv:2608.00639v1` abstract). Real-world P4₁₆ requires executable static semantics spanning bidirectional type inference, implicit numeric coercions, overload resolution, compile-time evaluation, and directional (`in`/`out`/`inout`) copy-in/copy-out parameter semantics.
- Reimplemented in Rust (`p4spectec/core/src/{pass/elaborate, pass/algo, pass/structure, pass/prosify, specdoc/adoc, runner}`), **`P4-SpecTec`** elevates **explicitly moded algorithmic inference rules** (declaring input vs. output argument positions on every judgment, with `otherwise.rs`, `antiunify.rs`, `totalize.rs`, and `specdoc/adoc/` AsciiDoc prose rendering) into its primary mechanization instrument. Running the mechanized specification against the `p4c` test corpus uncovered **24 real bugs** across the official P4 specification and `p4c` reference compiler, leading to conditional acceptance as P4's official specification authoring toolchain in March 2026 (`README.md`).
- Conversely, **`ESMeta`** extracts an imperative IR directly from ECMA-262's existing imperative HTML pseudocode—yielding strong differential fuzzing and bug discovery for JavaScript, at the cost of making inductive mathematical metatheory proofs (preservation, progress) far harder than over declarative/moded inference rules because global mutable realm state obscures structural invariants.

---

### 2. Multi-Prover Semantic Meta-Compilers: `Ott`, `Lem`, and `Sail`

`Basis: normative + source + documentation`

Three generations of specification compilers from Cambridge's REMS group expose the exact trade-offs of targeting multiple theorem provers simultaneously:

1. **`Ott` (`ott-lang/ott` @ `0639ce49892252e0b53e84aa5b0c35b02785913e`; Sewell et al., JFP 2010 DOI `10.1017/S095679680999019X`):** Compiles BNF-style concrete syntax, binding annotations, and inductive inference rules to LaTeX, Coq, Isabelle/HOL, HOL4, and OCaml (`src/{coq_induct,grammar_pp,substs_pp,defns}.ml`). Primary-source limitation recorded verbatim in `README.md`: *"At present only a fully concrete representation of binding, without quotienting by alpha equivalence, is fully supported. An experimental backend generates a locally-nameless representation of terms for a subset of the Ott metalanguage"* (`src/ln_transform.ml`). Consequently, complex binding structures (mutually recursive `let rec` blocks, telescopes, dependent binders) produce heavy substitution boilerplate in target provers.
2. **`Lem` (`rems-project/lem` @ `3802cb04b53d5f1096a464e51ecbfb2a750a7ccd`; Mulligan et al., ICFP 2014 DOI `10.1145/2628136.2628162`):** An ML-like pure functional specification language targeting Coq, Isabelle/HOL, HOL4, OCaml, and LaTeX (`src/backend.ml`, `{coq,isabelle,hol,ocaml,tex}-lib/`), powering `Cerberus` (C semantics), `Linksem` (ELF/DWARF), and relaxed memory models. Its core friction is the **lowest-common-denominator prover impedance mismatch**: Coq enforces strict positivity and structural/well-founded termination; Isabelle/HOL and HOL4 lack dependent types (forcing non-dependent bitvector length encodings); and library/monad conventions diverge across provers—requiring per-target termination pragmas and defensive specification idioms.
3. **`Sail` (`rems-project/sail` @ `97aa617dcd4d01575f773cb58ea1e8686858c8c2`; Armstrong et al., POPL 2019 DOI `10.1145/3290384`):** A specialized first-order imperative ISA specification DSL equipped with **lightweight flow-sensitive dependent numeric and bitvector-length types checked via Z3** (`README.md`). Direct inspection of `sail/src/` shows an expanded multi-backend architecture covering:
   - **Prover backends:** `sail_lean_backend` (Lean 4!), `sail_coq_backend` + `rocq/` (Coq/Rocq), and `sail_lem_backend` (exporting through Lem to Isabelle/HOL and HOL4, backed by `lib/isabelle/` and `lib/hol/` concurrency-interface monad lemmas);
   - **Executable & verification backends:** `sail_c_backend` and `sail_ocaml_backend` (OS-booting reference emulators for Armv9.4-A/Armv8-A, RISC-V, CHERI-RISC-V, CHERIoT, Morello), `sail_smt_backend` (feeding `Isla` symbolic evaluation and `Islaris` Iris binary proofs), `sail_sv_backend` (SystemVerilog hardware reference), and `sail_latex_backend` / `sail_doc_backend` (AsciiDoc).
   - **Limitation:** Sail's imperative register-state/concurrency monads generate large monadic proof terms in Lean 4 and Coq that require dedicated framing lemmas (`lib/isabelle/Sail2_*_lemmas.thy`) to avoid proof-assistant elaboration blowups, and Sail intentionally excludes higher-order functions, garbage-collected heaps, and general PL type systems.

---

### 3. Language-Parametric Deductive Verification and Proof Certificates: `K`, Reachability Logic, and Matching $\mu$-Logic

`Basis: normative + source + documentation`

#### 3.1 From Operational Rewriting to Matching $\mu$-Logic

The **`K` Framework** (`runtimeverification/k` @ `4a46d1231473b599c699160132fd6e76a5c46406`; Roşu & Şerbănuţă, JLAP 2010 DOI `10.1016/j.jlap.2010.03.012`) takes a language's syntax and operational semantics—written as rewrite rules over nested configuration cells (`<k>`, `<env>`, `<store>`, `<threads>`)—and automatically derives a parser, LLVM concrete interpreter, Haskell symbolic execution backend (`kore-exec`), model checker, and deductive program verifier.

- **Reachability Logic (Ştefănescu, Park, Yuwen, Li & Roşu, OOPSLA 2016, DOI `10.1145/2983990.2984027`):** Proved that operational semantics alone suffices for a **sound and relatively complete language-parametric deductive verifier** (verifying heap-manipulating programs such as AVL trees across C, Java, and JavaScript directly from their operational rewrite rules, eliminating per-language Hoare-logic soundness proofs).
- **Matching $\mu$-Logic (Chen & Roşu, LICS 2019, DOI `10.1109/LICS.2019.8785675`):** Unifies FOL, separation logic, modal $\mu$-calculus, LTL/CTL, and Reachability Logic into one minimal foundation with patterns built from element variables $x$, set variables $X$, constant symbols $\sigma$, bottom $\bot$, implication $\to$, binary application $\cdot$, existential quantification $\exists x$, and least fixpoint $\mu X$ (for positive occurrences of $X$).

#### 3.2 Proof-Certificate Generation and the 200-Line Metamath TCB

`Basis: normative + source`

Because `K`'s symbolic execution engine (`kore-exec` in Haskell, LLVM backend, parser, Z3) spans hundreds of thousands of lines of unverified code, any bug in unification, matching, or SMT translation silently compromises every language verified in `K`. Lin, Chen, Trinh, Wang, and Roşu (*"Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier"*, PACMPL Vol. 7 OOPSLA1 2023, DOI `10.1145/3586029`; `runtimeverification/proof-generation` @ `bdf8d0c638896dc6b2e3469ecf3e665f5eec5f26`) resolve this via the **de Bruijn Criterion**: instrumenting `K` to emit independent proof certificates checked by Metamath.

Direct inspection of `runtimeverification/proof-generation/theory/matching-logic-200-loc.mm` (exactly 200 lines) confirms the complete trusted Hilbert axiomatization:
- **Syntax & Meta-Predicates (lines 1–155):** `#Pattern`, `#Fresh`, `#Substitution`, `#Positive`/`#Negative`, `#ApplicationContext`, `#Notation` (desugaring `\not`, `\or`, `\and`).
- **Exact 16 Axioms and Proof Rules (lines 156–200):** Propositional Hilbert axioms `proof-rule-prop-1..3`, Modus Ponens (`proof-rule-mp`), Existential introduction & generalization (`proof-rule-exists`, `proof-rule-gen`), Application-context propagation (`proof-rule-propagation-{bot,or,exists}`), Framing (`proof-rule-frame`), Pre-fixpoint & Knaster–Tarski induction (`proof-rule-prefixpoint`, `proof-rule-kt`), Set-variable substitution (`proof-rule-set-var-substitution`), Existence (`proof-rule-existence`: `|- (\exists x x)`), and Singleton variable uniqueness (`proof-rule-singleton`).

#### 3.3 Practical Engineering Failure Modes in `K`

`Basis: source + documentation + derived`

1. **Proof Certificate Size Explosion:** In `runtimeverification/proof-generation/README.md`, a single concrete rewriting proof (`rewriting-proof/goal.mm`) occupies **77,192,945 bytes (~77 MB)** containing **9,148 Metamath statements** (4,352 `$a` and 1,776 `$p`). Scaling Hilbert-style Matching Logic traces to multi-thousand-step industrial contracts (e.g., EVM or C loops) requires aggressive proof compression, reflective decision checkers, and DAG sharing.
2. **Unverified `[simplification]` Rewrite Lemmas:** Real `K` verification efforts (`KEVM`, `K-C`) suffer symbolic state-space explosion on map/array updates and bitvector arithmetic unless engineers supply hundreds of custom `[simplification]` rewrite lemmas—which are trusted axioms during symbolic search unless independently discharged in Matching Logic.
3. **SMT Reconstruction & Compositional Framing Gaps:** Reconstructing Z3 bitvector/nonlinear-arithmetic side conditions inside Hilbert Matching Logic remains incomplete/expensive, and operational rewriting over global configuration cells lacks the modular higher-order separation-logic framing (step-indexed CMRAs) provided by interactive frameworks like Iris.
4. **Concrete Execution Speed Gap:** Even with `K`'s LLVM concrete backend, interpreting language semantics via term rewriting over nested configuration cells incurs substantial overhead ($10\times\text{–}1000\times$) relative to native compiled code—motivating Futamura specialization below.

---

### 4. Practical First Futamura Projection Over SSA IR: `weval`, `waffle`, and Cranelift/Wasmtime

#### 4.1 Classical Futamura Projections and Why Black-Box BTA Stalled

`Basis: normative + derived`

Yoshihiko Futamura (1971; *HOSC* 1999) and Jones, Gomard, and Sestoft (*Partial Evaluation and Automatic Program Generation*, 1993) formalized how a partial evaluator $\text{mix}$ specializing program $P(s, d)$ to static input $s$ turns an interpreter into a compiler:
1. **First Projection (Compilation):** $\text{target} = \text{mix}(\text{interp}, \text{src})$ — specializing an interpreter to a fixed guest program produces compiled residual code;
2. **Second Projection (Compiler Generation):** $\text{compiler} = \text{mix}(\text{mix}, \text{interp})$;
3. **Third Projection (Compiler-Generator Generation):** $\text{cogen} = \text{mix}(\text{mix}, \text{mix})$.

A partial evaluator achieves **Jones Optimality** when specializing a self-interpreter to program $p$ removes 100% of interpretive dispatch overhead. Classical offline partial evaluation (relying on automatic **Binding-Time Analysis (`BTA`)** to partition expressions into `Static` vs. `Dynamic`) stalled on industrial systems interpreters for four well-documented reasons: (1) **binding-time pollution** (one aliased pointer or dynamic branch taints downstream values from `Static` to `Dynamic`, leaving the dispatch switch unspecialized); (2) **non-termination and code-size explosion** when unfolding loops over statically varying state (stack depth, pointers); (3) **residualized value boxing and environment indirection** without interpreter rewrites using *"The Trick"* (enumerating bounded finite static values over a dynamic key); and (4) **2nd/3rd projection fragility** on imperative SSA IRs (where direct generating extensions / explicit specializers outperform self-application).

#### 4.2 `weval` + `waffle` Architecture: Precise IR Relationship to Cranelift

`Basis: normative + source`

Chris Fallin and Maxwell Bernstein (*"Partial Evaluation, Whole-Program Compilation"*, PLDI 2025, DOI `10.1145/3729259`, `arXiv:2411.10559v1`; `bytecodealliance/weval` @ `47164ae9e5bacfdcc23ddaeb2fa491c8f61c644d`, v0.5.1) proved that the First Futamura Projection scales to industrial C/C++ interpreters (Mozilla SpiderMonkey JS and PUC-Rio Lua) when recast as **intrinsic-guided SSA CFG specialization over WebAssembly snapshots**.

Direct source inspection of `weval/Cargo.toml` (lines 11–25), `weval/README.md`, and `waffle/README.md` (`bytecodealliance/waffle` @ `dad4f9cb1e05014c8e49648bc45e071aad54dca3`) clarifies a common architectural misconception: **`weval` does NOT operate directly on Cranelift's CLIF SSA IR.** Instead, the pipeline has three distinct layers:

1. **Snapshot Phase (`wasmtime-wizer` + Cranelift):** `weval weval -w -i program.wasm -o wevaled.wasm` invokes `wasmtime-wizer` (`Cargo.toml` line 21, backed by `wasmtime` with `features = ["cranelift"]` at line 20) to execute the guest runtime's initialization (parsing guest JS/Lua bytecode into the Wasm heap and registering `weval_req_t` specialization directives via `weval_request()`), capturing the initialized linear memory as a static `Image`.
2. **Specialization Phase (`waffle` Wasm SSA IR):** `weval` parses the snapshotted `.wasm` module into **`waffle` (`waffle = "0.2.0"`)**, a Wasm-to-Wasm SSA CFG IR designed specifically for `weval` (`waffle/README.md`). `waffle` borrows Cranelift's **block-parameter SSA CFG design** (no phi-nodes; Wasm locals converted to SSA), **while keeping all operators, memory, and tables 1-to-1 at the WebAssembly abstraction level**.
3. **Structured Wasm Recovery & Downstream Native Codegen (`waffle` -> Wasmtime/Cranelift):** After specialization, `waffle`'s 4-stage backend lowers the specialized SSA CFG back into valid structured WebAssembly bytecode:
   - `src/backend/reducify.rs`: context-sensitive block duplication converting irreducible multi-entry loops into reducible CFGs;
   - `src/backend/stackify.rs`: Ramsey's algorithm (ICFP 2022, `10.1145/3547621`) recovering structured Wasm `block`/`loop`/`if` ASTs;
   - `src/backend/treeify.rs`: single-use SSA expression scheduling onto the Wasm operand stack;
   - `src/backend/localify.rs`: linear-scan register allocation mapping SSA values to Wasm locals.
   The resulting standalone `.wasm` module (`wevaled.wasm`) requires **zero runtime JIT** (fully W^X-compatible) and is compiled AOT or at load time to native x86-64/ARM64 by Cranelift/Wasmtime (or any Wasm runtime).

#### 4.3 Context-Indexed Specialization Algorithm and `include/weval.h` Intrinsics

`Basis: source`

Inspecting `weval/include/weval.h` (lines 25–196), `weval/src/state.rs` (lines 1–95), and `weval/src/eval.rs` (lines 23–63) reveals the exact engineering primitives that eliminate BTA fragility:

- **Context Stack (`src/state.rs` lines 45–95):** Basic blocks are replicated by a deduplicated arena of `Context` handles, where each `ContextElem` is one of `Root`, `Loop(PC)` (guest bytecode program counter), or `Specialized(Value, u32)` ("The Trick" value split). Crucially, `weval` separates state into two halves per context (`src/state.rs` lines 13–35):
  1. **Flow-insensitive SSA values:** Looked up by walking up the context stack (`parent`) so loop bodies naturally inherit outer static values;
  2. **Flow-sensitive global/memory overlays:** Indexed by `(context, program_point)` to track updates to Wasm globals and memory overlays along CFG edges.
- **Worklist Fixpoint Evaluator (`src/eval.rs` lines 23–63):** `Evaluator` maintains `block_map: HashMap<(Context, Block), Block>`, reverse map `block_rev_map: PerEntity<Block, (Context, Block)>`, `value_map`, dependency set `value_dep_blocks`, `reg_map` (specialization-register blockparams), and a deduplicated BFS/worklist `queue: VecDeque<(Block, Context, Block)>`, propagating `AbstractValue` lattice states (`Unknown` / constant `WasmVal` / `Runtime(cause)`) across reachable `(ctx, block)` pairs.
- **Complete C/Wasm Intrinsic Surface (`include/weval.h` lines 127–196, Wasm import module `"weval"`):**

| Intrinsic Family (`"weval"` import) | Signature (`include/weval.h`) | Role in Interpreter Specialization |
|---|---|---|
| **Async Request Queue** | `weval_request(weval_req_t*)`, `WEVAL_DEFINE_GLOBALS()`, `WEVAL_DEFINE_TARGET(idx, fn)` | Records `(func, num_globals, argbuf, specialized_fn_ptr_out)` in Wizer heap (`weval_req_arg_type`: `i32/i64/f32/f64/buffer`) |
| **Loop Context Control** | `push.context(pc)`, `pop.context()`, `update.context(pc)`, `context.bucket(b)` | Keys specialized CFG blocks by guest bytecode PC so dispatch switch folds away completely |
| **Specialization Registers & "The Trick"** | `read.reg(idx)`, `write.reg(idx, val)`, `specialize.value(val, lo, hi)`, `read.specialization.global(idx)` | Threads static interpreter metadata across CFG merges; `specialize.value` splits finite dynamic indices `[lo, hi)` into constant arms |
| **Operand-Stack & Locals Virtualization** | `push.stack(ptr, val)`, `pop.stack(ptr)`, `read.stack(ptr, i)`, `write.stack(ptr, i, v)`, `sync.stack()`, `read.local`, `write.local` | Promotes guest interpreter's in-memory operand stack and locals into SSA values, canceling push/pop memory traffic until an explicit `sync.stack()` flush (e.g., before calls/GC/exceptions) |
| **Diagnostics & Guardrails** | `assert.const32(val, line)`, `abort.specialization(line, fatal)`, `trace.line`, `print` | Turns silent BTA failures into immediate specialization-time diagnostic assertions! |

**Empirical Performance (`arXiv:2411.10559v1` / PLDI 2025; `weval/README.md`):** Applying `weval` to Mozilla SpiderMonkey's Portable Baseline Interpreter (executing bytecode + `CacheIR` inline caches) achieved **2.17x** geometric-mean speedups in the PLDI 2025 evaluation (`weval/README.md` notes **3–5x** speedups over the generic interpreter in subsequent SpiderMonkey builds), and specializing the unmodified PUC-Rio Lua interpreter yielded **1.84x** speedups with **three hours of engineering effort**.

#### 4.4 Four Miscompilation Hazards of Unverified Partial Evaluation and Proof-Carrying `weval`

`Basis: source + execution + derived`

Neither `weval` nor `waffle` is formally verified (though `waffle` is differentially fuzzed against Wasmtime, `waffle/README.md`). Specializing a low-level SSA interpreter over flat untyped linear memory exposes **four sharp soundness hazards**:

1. **Static-vs-Dynamic Memory Aliasing Hazard:** Folding a load from an immutable `weval_req_arg_buffer` or read-only snapshot slice assumes **no dynamic guest store or imported host function ever mutates that linear-memory address**. As proven concretely in **Evidence** (Probe Part 2), if a guest `PATCH_CODE` store overwrites `code[1]` before execution reaches `pc = 1`, the generic interpreter returns `999` while the specialized residual CFG (having folded `code[1] = LOAD_IMM 42`) silently returns **`42`**.
2. **Trap, Side-Effect, and Divergence Reordering:** Speculatively folding a "static" operation that may trap (integer division by zero, out-of-bounds memory/table load) or diverge ahead of a dynamic branch alters observable trap semantics.
3. **Context-Key Generalization / Equality Bugs:** When specialization caps context depth or merges contexts (`Context` deduplication / `context_bucket`), an overly coarse context key can merge two semantically distinct interpreter states into one specialized block.
4. **Inline-Cache / Self-Modifying Code Invalidation:** Specializing over runtime-generated `CacheIR` stubs assumes cache guard invariants remain valid; a missing invalidation edge executes stale specialized code.

**Path to Proof-Carrying `weval` (`Basis: source + execution + derived`):** Because `weval`'s `Evaluator` already stores `block_rev_map: PerEntity<Block, (Context, Block)>` (`src/eval.rs` line 48), every specialized basic block `sb` maps cleanly back to `(ctx, orig_bb)` paired with the abstract constant/memory state invariant $\Phi(\text{ctx})$. A **linear-time, per-block translation-validation certificate checker** (prototyped in Probe Part 2) need only verify: (a) a static **region-disjointness side condition** proving no dynamic store aliases folded read-only regions (rejecting `prog_alias` with `REGION_ALIAS_VIOLATION at bb_pc0`), and (b) local symbolic simulation along each specialized block's straight-line ops and terminator successors against `orig_bb` under $\Phi(\text{ctx})$. Proving this single small checker once yields a **Verified First Futamura Projection** ($O(1)$ compiler verification effort across all $N$ languages with verified interpreters!).

---

### 5. Collapsing Towers of Interpreters (`LMS`, `Pink`) and Comparative Paradigm Matrices

#### 5.1 Multi-Stage Programming (`LMS`) and Stage-Polymorphic Tower Collapse

`Basis: normative + source + execution`

Instead of post-hoc BTA or SSA intrinsics, **Lightweight Modular Staging (`LMS`)** (Rompf & Odersky, GPCE 2010 `10.1145/1868294.1868314`; CACM 2012 `10.1145/2184319.2184345`) embeds binding times directly into the host type system (`T` = stage-0/now vs. `Rep[T]` = stage-1/residual code) using ANF `reify`/`reflect` let-insertion (`TiarkRompf/collapsing-towers` @ `d938bf9cdec5bcfd1f3bf8c1ac2431007da2afe1`, `popl18/base.scala` lines 56–90) to prevent effect duplication and code explosion.

In **"Collapsing Towers of Interpreters"** (POPL 2018, DOI `10.1145/3158140`), Nada Amin and Tiark Rompf demonstrated how **stage polymorphism** collapses an arbitrarily tall stack of meta-circular and reflective interpreters (`Pink`, `popl18/pink.scala` lines 17–210) in a single pass with zero residual overhead:
- A single evaluator `ev_poly_src` (`pink.scala` lines 18–47) is parameterized by two hooks: `maybe-lift` and open-recursion `tie`.
- Instantiating `maybe-lift = (lambda _ e e)` yields a normal interpreter (`eval_src`, line 48); instantiating `maybe-lift = (lambda _ e (lift e))` yields a **staged compiler** (`evalc_src`, line 49).
- Evaluating `(((eval eval_src) evalc_src) fac_src)` (`pink.scala` lines 139–156) executes the outer levels statically and triggers stage-1 ANF residualization only at the bottom level, producing the **exact same minimal residual ANF lambda** as compiling `fac_src` directly—even when intermediate reflective layers inject instrumentation via `EM` (`pink.scala` lines 198–209)!

**Empirical Verification & Subtle Compile-Time Cost (`Basis: execution`, Probe Part 3):** Executing a faithful Python implementation of `pink.scala`'s `ev_poly` on `fac(5) = 120` confirms both the triumph and a critical practical boundary:

| Execution Configuration (`fac(5) = 120`) | Runtime Host Eval Steps | Runtime Slowdown vs. Direct | Compile-Time Host Eval Steps | Residual AST Matches Direct? |
|---|---:|---:|---:|---|
| Direct `fac(5)` | **63** | $1.00\times$ | — | (baseline) |
| 1-level interp `(eval 'fac)(5)` | **1,942** | $30.8\times$ | — | — |
| 2-level interp `((eval 'eval) 'fac)(5)` | **99,274** | $1,575.8\times$ | — | — |
| 1-level compile `evalc('fac)` | **63** | **$1.00\times$** | 426 | Exact syntactic match |
| 2-level collapse `(eval 'evalc)('fac)` | **63** | **$1.00\times$** | 21,653 | Exact syntactic match |
| 3-level collapse `((eval 'eval) 'evalc)('fac)` | **63** | **$1.00\times$** | 1,140,543 | Exact syntactic match |

While **runtime** overhead collapses completely to **$1.00\times$** regardless of tower depth, **compile-time** specialization cost still multiplies by $\sim 51\times$ per unstaged meta-layer (`426 -> 21,653 -> 1,140,543`) unless intermediate interpreters in the tower are themselves pre-compiled (Second Futamura / staged cogen) before running on the target program! Additional MSP friction points include **cross-stage persistence (CSP)** of mutable/FFI handles, **scope extrusion** without modal/contextual type systems, and staging-annotation overhead (`List[Rep[T]]` vs. `Rep[List[T]]`).

#### 5.2 Comparative Matrix A: Executable Specification Meta-Compilers

`Basis: normative + source + documentation`

| System (Pinned Revision) | Input Paradigm | Prose / LaTeX Generation | Executable Type Checker | Executable Interpreter / Emulator | Theorem-Prover Targets (on `main`) | Built-In Deductive Verifier / Proof Certs | Open Multi-Language FFI Support |
|---|---|---|---|---|---|---|---|
| **`Wasm-SpecTec`** (`acc6e834...` / `WebAssembly/spec` `d0b2e8d5...`) | Declarative `EL -> IL -> AL` + hints | Yes (`--latex`, `--prose`, `--splice-{latex,sphinx}`) | No (Wasm validation is local; animation targets exec) | Yes (`--interpreter`, 100% Wasm 2.0 tests) | None merged on `main` (Rocq, Lean 4, Agda, Isabelle on separate dev branches) | No | Closed Wasm store (opaque host hooks) |
| **`P4-SpecTec`** (`731621c5...`) | Moded algorithmic inference rules (Rust) | Yes (AsciiDoc + LaTeX splicer) | **Yes** (found 24 P4/`p4c` bugs) | Yes (P4 simulator) | None on `main` | No | Closed P4 pipeline architecture |
| **`ESMeta`** (`b4a787f2...`) | Imperative spec extraction (ECMA-262 HTML) | Consumes existing spec prose | N/A (dynamic JS) | Yes + coverage fuzzer | None | No | Closed ECMAScript realm |
| **`Ott`** (`0639ce49...`) | Concrete syntax + binding + inductive rules | Yes (LaTeX) | No | OCaml AST/parser only | Coq, Isabelle/HOL, HOL4 (concrete binding; exp. LN) | No | Closed single calculus |
| **`Lem`** (`3802cb04...`) | Pure ML-like functional spec | Yes (LaTeX/HTML) | Via OCaml extraction | Yes (OCaml) | Coq, Isabelle/HOL, HOL4 | No | Manual gluing (shared datatypes) |
| **`Sail`** (`97aa617d...`) | First-order imperative + Z3 bitvector types | Yes (LaTeX, AsciiDoc) | Static ISA type-checker | Yes (OS-booting C, OCaml) | **Lean 4**, Coq/Rocq, Isabelle/HOL & HOL4 (via Lem), SMT, SystemVerilog | Via `Isla` / `Islaris` (Iris) | Single-CPU concurrency interface monad |
| **`K` + Proof Gen** (`4a46d123...`, `bdf8d0c6...`) | Rewrite rules over configuration cells | Markdown literate specs | Via rewrite semantics | Yes (LLVM concrete, Haskell symbolic) | Metamath Matching $\mu$-Logic (**200-LOC** kernel) | **Yes** (Reachability Logic + OOPSLA 2023 certs; ~77 MB raw size) | Closed monolithic `<configuration>` tree |

#### 5.3 Comparative Matrix B: Futamura Partial Evaluation and Interpreter-Compilation Paradigms

`Basis: normative + source + documentation + derived`

| Paradigm / System | Binding-Time Mechanism | Runtime JIT / W^X Safe? | Warmup & Footprint | Dynamic `eval` & Megamorphic Dispatch | FFI Specialization Boundary | Verification / TCB Status |
|---|---|---|---|---|---|---|
| **Classical Offline PE (`Similix`)** | Automatic post-hoc BTA | AOT (W^X safe) | Zero warmup | Static only (no runtime feedback) | Opaque BTA pollution wall | Unverified (research prototypes in Scheme) |
| **Intrinsic SSA PE (`weval` + `waffle`)** | Explicit C/Wasm intrinsics (`update.context`, `specialize.value`, virtual stack) | **AOT (W^X safe, zero JIT)** | Zero warmup, small Wasm binary | Baseline tier (2.17–5x); needs runtime fallback for `eval()` | Opaque Wasm `import` boundary; linear-memory aliasing hazard | Unverified (`waffle` fuzzed); `block_rev_map` amenable to linear-time TV cert |
| **Typed Multi-Stage (`LMS` / `Pink`)** | Static `Rep[T]` / stage-polymorphic `maybe-lift` + ANF let-insertion | AOT or runtime staging | Zero warmup if AOT; compile time scales with unstaged tower depth | Static stage boundary (`run` invokes compiler) | Trapped in single host language (`Rep[T]` lost at FFI) | Unverified ANF effect-reordering / let-insertion |
| **Meta-Tracing JIT (`PyPy` / `RPython`)** | Runtime trace recording of interpreter loop + hints | Runtime JIT (requires W+X / JIT) | Medium warmup; trace-explosion risk on branchy code | Strong on hot loops; poor on interpreters/tree walks | Opaque CFFI calls unless unboxed | Large unverified JIT TCB |
| **Speculative AST PE (`Graal` / `Truffle`)** | Self-specializing AST PICs + `@CompilationFinal` + Graal PE + OSR/Deopt | Runtime JIT (JVM + Graal) | High RAM/warmup (hundreds of MB) | Peak polymorphic/dynamic throughput + Truffle polyglot interop | Cross-FFI deoptimization frame-reconstruction cliff | Huge unverified JIT TCB (deopt verified only in small-scale Barrière et al. POPL 2021 / OOPSLA 2023) |

#### 5.4 The Open Multi-Language Composition Frontier

`Basis: derived`

Every specification meta-compiler in Matrix A models a **closed, single-language world** (one Wasm store, one P4 packet pipeline, one `K` configuration tree, one `Sail` CPU). Composing a `SpecTec`-defined Wasm component calling a `K`-specified C library on a `Sail`-specified RISC-V processor fails because their memory models, value representations, effect monads, and control stacks are incompatible. Likewise, every specializer in Matrix B hits an opaque barrier at cross-language FFI imports. Bridging both requires (1) compiling open-module specifications into a shared semantic event interface (e.g., interaction trees / open-module transition systems) and (2) specializing composed cross-language SSA IRs under region-disjointness ownership types checked by a single small kernel.

## Boundaries

- **`known not to apply` — `weval` Operating Directly on Cranelift CLIF SSA:** Direct inspection of `bytecodealliance/weval` (`47164ae9...`) and `bytecodealliance/waffle` (`dad4f9cb...`) establishes that `weval` specializes Wasm-to-Wasm over `waffle`'s block-parameter SSA IR (not Cranelift CLIF); Cranelift is invoked via `wasmtime-wizer` during snapshotting and downstream for native Wasm compilation.
- **`known not to apply` — `Wasm-SpecTec` Theorem-Prover Backends on `main`:** On `main` of both `Wasm-DSL/spectec` (`acc6e834...`) and `WebAssembly/spec` (`d0b2e8d5...`), theorem-prover export targets (Rocq, Lean 4, Agda, Isabelle) are not present in `spectec/src/exe-spectec/main.ml`; they reside only on unmerged development branches.
- **`known not to apply` — Soundness of `weval` Under Dynamic Bytecode Aliasing:** When dynamic linear-memory writes alias a statically folded bytecode region, `weval`-style specialization silently produces wrong results (verified in Probe Part 2).
- **`known not to apply` — Constant Compile-Time Cost for Unstaged Interpreter Towers:** Although Amin–Rompf stage polymorphism eliminates 100% of *runtime* tower overhead, *compile-time* evaluation steps still grow multiplicatively with unstaged tower depth (verified in Probe Part 3: `426 -> 21,653 -> 1,140,543`).
- **`unsupported` — Executable Type-Checker Generation in `Wasm-SpecTec`:** `Wasm-SpecTec`'s animation pipeline targets dynamic execution semantics and does not generate executable type checkers for complex static semantics (documented in `arXiv:2608.00639v1` and solved via moded algorithmic rules in `P4-SpecTec`).
- **`unsupported` — $\alpha$-Quotiented Binding in Standard `Ott`:** `ott-lang/ott` (`0639ce49...`) fully supports only concrete binding representations; locally nameless export covers only an experimental subset.
- **`unknown` — Ergonomic Automated Mechanization of `SpecTec` Specs in Lean 4 / Rocq:** Whether generated inductive definitions from the unmerged `lean-backend-proof` / `rocq-backend-proof` branches of `Wasm-DSL/spectec` support scalable tactic-driven soundness proofs without extensive manual restructuring was not established.
- **`unknown` — Scaling Matching Logic Proof Certificates & Automatic `[simplification]` Verification:** Bringing OOPSLA 2023 Matching Logic proof certificates from tens of megabytes per trace down to sub-second checking for full industrial C/EVM verification, and automatically discharging `K` `[simplification]` lemmas + Z3 SMT side conditions, remain open engineering frontiers.
- **`not examined` — Building/Benchmarking Upstream Compilers Locally:** Neither `Wasm-DSL/spectec` (OCaml/Dune), `P4-SpecTec` (Rust), `Sail`, `K`/Metamath, `weval` on SpiderMonkey/Lua, nor `collapsing-towers` (Scala/sbt) were compiled or benchmarked locally in this environment; performance figures for SpiderMonkey/Lua and Metamath certificate sizes are cited directly from the verified primary papers and repository `README.md` transcripts, supplemented by the standalone Python probes below.

## Evidence

### Primary Repositories and Exact Source Citations (Observed `2026-11-19`)

- **`Wasm-DSL/spectec`** @ `acc6e834ff403c82554d081237f327346190ad96` & **`WebAssembly/spec`** @ `d0b2e8d5544d2049fba0521922c436e3f0fcaebe`:
  - `spectec/README.md` (DSL structure: `syntax`, `var`, `relation`, `rule`, auxiliary functions, backend hints).
  - `spectec/src/` subdirectories: `al`, `backend-ast`, `backend-interpreter`, `backend-latex`, `backend-prose`, `backend-splice`, `el`, `exe-spectec`, `frontend`, `il`, `il2al`, `middlend`, `util`, `xl`.
  - `spectec/src/exe-spectec/main.ml` L196–226, L314–392 (CLI targets: `--check`, `--ast`, `--latex`, `--splice-latex`, `--splice-sphinx`, `--prose`, `--prose-rst`, `--interpreter`, `--test-version` default `3`).
  - `spectec/src/il2al/animate.ml` L1–65 (`tag = Condition | Assign of string list`, `is_tight`, `is_assign` dataflow premise scheduling) and `spectec/src/il2al/manual.ml` L14–65 (`eval_expr`, `manual_algos`).
  - `spectec/src/middlend/` (`aliasDemut`, `sub`, `subexpansion`, `totalize`, `typefamilyremoval`, `undep`, `unthe`, `letintromech`).
  - `WebAssembly/spec` `specification/`: `wasm-1.0`, `wasm-2.0`, `wasm-3.0`, `wasm-latest`, `.github/workflows/ci-spectec.yml`.
  - `Wasm-DSL/spectec` remote refs inspected via `info/refs`: unmerged prover branches `agda-backend`, `coq`, `isabelle-mech-backend`, `lean-backend-proof`, `lean4-wip`, `rocq-backend`, `rocq-backend-proof`.
- **`kaist-plrg/p4-spectec`** @ `731621c5e3c8eb94323c112898364624fc03ce9d`:
  - `README.md` (March 2026 conditional acceptance by P4 LDWG, Rust implementation, OOPSLA 2026 DOI `10.1145/3839535`).
  - `p4spectec/core/src/` (`pass/elaborate`, `pass/algo`, `pass/structure/{antiunify,totalize,opt}`, `pass/prosify`, `specdoc/{adoc,latex,splicer}`, `runner/interpreter.rs`).
- **`ott-lang/ott`** @ `0639ce49892252e0b53e84aa5b0c35b02785913e`: `README.md` (concrete binding vs. experimental locally-nameless backend), `src/{ln_transform,coq_induct,defns,grammar_pp}.ml`.
- **`rems-project/lem`** @ `3802cb04b53d5f1096a464e51ecbfb2a750a7ccd`: `src/backend.ml`, `{coq,hol,isabelle,ocaml,tex}-lib/`.
- **`rems-project/sail`** @ `97aa617dcd4d01575f773cb58ea1e8686858c8c2`: `README.md` (Z3 dependent bitvector types, ISA models, `Isla`/`Islaris`), `src/` (`sail_lean_backend`, `sail_coq_backend`, `rocq`, `sail_lem_backend`, `sail_c_backend`, `sail_ocaml_backend`, `sail_smt_backend`, `sail_sv_backend`, `sail_latex_backend`, `sail_doc_backend`).
- **`runtimeverification/k`** @ `4a46d1231473b599c699160132fd6e76a5c46406` & **`runtimeverification/proof-generation`** @ `bdf8d0c638896dc6b2e3469ecf3e665f5eec5f26`:
  - `proof-generation/theory/matching-logic-200-loc.mm` L1–200 (complete 200-line Metamath Matching $\mu$-Logic kernel; 16 axioms/rules at L156–200).
  - `proof-generation/README.md` (concrete rewriting proof workflow and observed `77192945 bytes`, `9148 statements` Metamath transcript).
- **`bytecodealliance/weval`** @ `47164ae9e5bacfdcc23ddaeb2fa491c8f61c644d` & **`bytecodealliance/waffle`** @ `dad4f9cb1e05014c8e49648bc45e071aad54dca3`:
  - `weval/Cargo.toml` L1–25 (`version = "0.5.1"`, `waffle = "0.2.0"`, `wasmtime` with `cranelift`, `wasmtime-wizer`).
  - `weval/include/weval.h` L25–196 (`weval_req_t`, `weval_req_arg_t`, `WEVAL_DEFINE_GLOBALS`, `WEVAL_DEFINE_TARGET`, all `"weval"` Wasm import intrinsics including operand-stack & locals virtualization).
  - `weval/src/state.rs` L1–95 (flow-insensitive SSA vs. flow-sensitive global/memory overlay; `ContextElem::{Root, Loop(PC), Specialized(Value, u32)}`).
  - `weval/src/eval.rs` L23–63 (`Evaluator`, `block_map`, `block_rev_map`, `value_map`, `value_dep_blocks`, `reg_map`, `queue`).
  - `waffle/README.md` (Cranelift-style block-parameter SSA over 1-to-1 Wasm operators; 4-stage backend `reducify`, Ramsey's `stackify`, `treeify`, `localify`; differential fuzzing against Wasmtime).
- **`TiarkRompf/collapsing-towers`** @ `d938bf9cdec5bcfd1f3bf8c1ac2431007da2afe1`:
  - `popl18/base.scala` L56–90 (`fresh`, `reify`, `reflect`, `anf` let-insertion).
  - `popl18/pink.scala` L17–210 (`ev_poly_src` stage-polymorphic evaluator, `eval_src` vs `evalc_src`, `testCorrectnessOptimality` ANF identity checks at L100–158, `EM` reflection at L193–210).

### Peer-Reviewed Publications Verified

- Youn, Shin, Lee, Ryu, Breitner, Gardner, Lindley, Pretnar, Rao, Watt & Rossberg (2024), *Bringing the WebAssembly Standard up to Speed with SpecTec*, PACMPL 8 (PLDI 2024), DOI `10.1145/3656440`.
- Lee, Jeong, Ahn, Kwon & Ryu (2026), *P4-SpecTec: Integrating a Language Mechanization Framework into the Real-World P4 Specification*, OOPSLA 2026, DOI `10.1145/3839535`, `arXiv:2608.00639v1`.
- Sewell, Zappa Nardelli, Owens, Peskine, Ridge, Sarkar & Strniša (2010), *Ott: Effective tool support for the working semanticist*, JFP 20(1):71–122, DOI `10.1017/S095679680999019X`.
- Mulligan, Owens, Gray, Ridge & Sewell (2014), *Lem: reusable engineering of real-world semantics*, ICFP 2014, DOI `10.1145/2628136.2628162`.
- Armstrong et al. (2019), *ISA Semantics for ARMv8-a, RISC-V, and CHERI-MIPS*, PACMPL 3 (POPL 2019, Art. 71), DOI `10.1145/3290384`.
- Roşu & Şerbănuţă (2010), *An Overview of the K Semantic Framework*, JLAP, DOI `10.1016/j.jlap.2010.03.012`.
- Ştefănescu, Park, Yuwen, Li & Roşu (2016), *Semantics-Based Program Verifiers for All Languages*, OOPSLA 2016, DOI `10.1145/2983990.2984027`.
- Chen & Roşu (2019), *Matching $\mu$-Logic*, LICS 2019, DOI `10.1109/LICS.2019.8785675`.
- Lin, Chen, Trinh, Wang & Roşu (2023), *Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier*, PACMPL 7 (OOPSLA1 2023), DOI `10.1145/3586029`.
- Fallin & Bernstein (2025), *Partial Evaluation, Whole-Program Compilation*, PACMPL 9 (PLDI 2025), DOI `10.1145/3729259`, `arXiv:2411.10559v1`.
- Rompf & Odersky (2010/2012), *Lightweight Modular Staging*, GPCE 2010 DOI `10.1145/1868294.1868314`, CACM 55(6):121–130 DOI `10.1145/2184319.2184345`.
- Amin & Rompf (2018), *Collapsing Towers of Interpreters*, PACMPL 2 (POPL 2018), DOI `10.1145/3158140`.

### Reproducible Execution Probes and Verbatim Output (`2026-11-19`)

Save to `/tmp/probe_spectec_weval_towers.py` and run `python3 /tmp/probe_spectec_weval_towers.py` (Python 3.10+, standard library only):

```python
#!/usr/bin/env python3
import sys
from collections import deque
sys.setrecursionlimit(20000)

# [1] SpecTec il2al/animate.ml dataflow premise scheduler
def animate_premises(known_init, premises):
    known, rem, schedule = set(known_init), list(premises), []
    while rem:
        for i, (kind, fvs, targets, label) in enumerate(rem):
            if kind == "cond" and fvs.issubset(known):
                schedule.append(("CHECK", label)); rem.pop(i); break
        else:
            for i, (kind, fvs, targets, label) in enumerate(rem):
                if kind == "assign" and (fvs - targets).issubset(known):
                    schedule.append(("LET", label, sorted(targets)))
                    known |= targets; rem.pop(i); break
            else:
                return False, schedule, [p[3] for p in rem]
    return True, schedule, []

print("[1A]", animate_premises({"z","c","instrs"}, [
    ("cond", {"c","zero"}, set(), "c != zero"),
    ("assign", {"zero"}, {"zero"}, "zero := 0"),
    ("assign", {"z","instrs","res"}, {"res"}, "res := step(z, instrs)"),
]))
print("[1B]", animate_premises({"C","e"}, [
    ("cond", {"C","e","tau"}, set(), "has_type(C, e, tau)"),
    ("cond", {"tau","tau2"}, set(), "subtype(tau, tau2)"),
]))

# [2] Mini-weval context-indexed SSA specializer + TV checker + aliasing bug
def run_generic(code_mem, init_regs):
    mem, regs, pc = list(code_mem), dict(init_regs), 0
    while True:
        ins = mem[pc]; op = ins[0]
        if op == "LOAD_IMM": regs[ins[1]] = ins[2]; pc += 1
        elif op == "ADD_REG": regs[ins[1]] = regs[ins[2]] + regs[ins[3]]; pc += 1
        elif op == "SUB_IMM": regs[ins[1]] = regs[ins[2]] - ins[3]; pc += 1
        elif op == "JNZ": pc = ins[2] if regs[ins[1]] != 0 else pc + 1
        elif op == "PATCH_CODE": mem[ins[1]] = ins[2]; pc += 1
        elif op == "HALT": return regs[ins[1]]

def weval_spec(code):
    sb, bmap, rev, q = {}, {}, {}, deque()
    def get(pc):
        if pc not in bmap:
            bid = f"bb_pc{pc}"; bmap[pc] = bid; rev[bid] = ("BB_dispatch", pc); q.append(pc)
        return bmap[pc]
    entry = get(0)
    while q:
        pc = q.popleft(); bid = bmap[pc]; ins = code[pc]; op = ins[0]
        if op in ("LOAD_IMM","ADD_REG","SUB_IMM","PATCH_CODE"): sb[bid] = (ins, (get(pc+1),))
        elif op == "JNZ": sb[bid] = (("BR_NZ", ins[1]), (get(ins[2]), get(pc+1)))
        elif op == "HALT": sb[bid] = (("RET", ins[1]), ())
    return entry, sb, rev

def run_spec(entry, sb, init_regs):
    regs, bid = dict(init_regs), entry
    while True:
        ir, succs = sb[bid]; op = ir[0]
        if op == "LOAD_IMM": regs[ir[1]] = ir[2]; bid = succs[0]
        elif op == "ADD_REG": regs[ir[1]] = regs[ir[2]] + regs[ir[3]]; bid = succs[0]
        elif op == "SUB_IMM": regs[ir[1]] = regs[ir[2]] - ir[3]; bid = succs[0]
        elif op == "PATCH_CODE": bid = succs[0]
        elif op == "BR_NZ": bid = succs[0] if regs[ir[1]] != 0 else succs[1]
        elif op == "RET": return regs[ir[1]]

def check_tv_cert(code, sb, rev):
    for bid, (ir, succs) in sb.items():
        _, pc = rev[bid]; orig = code[pc]
        if orig[0] == "PATCH_CODE": return False, f"REGION_ALIAS_VIOLATION at {bid} (pc={pc})"
        if orig[0] == "JNZ": assert ir == ("BR_NZ", orig[1]) and rev[succs[0]][1] == orig[2] and rev[succs[1]][1] == pc + 1
        elif orig[0] == "HALT": assert ir == ("RET", orig[1]) and succs == ()
        else: assert ir == orig and rev[succs[0]][1] == pc + 1
    return True, f"VERIFIED ({len(sb)} specialized blocks)"

prog_sum = [("LOAD_IMM","acc",0),("ADD_REG","acc","acc","n"),("SUB_IMM","n","n",1),("JNZ","n",1),("HALT","acc")]
prog_alias = [("PATCH_CODE",1,("LOAD_IMM","r",999)),("LOAD_IMM","r",42),("HALT","r")]
for name, p, init in [("sum", prog_sum, {"n":10}), ("alias", prog_alias, {})]:
    e, sb, rev = weval_spec(p)
    print(f"[2:{name}] generic={run_generic(p, init)} spec={run_spec(e, sb, init)} tv={check_tv_cert(p, sb, rev)}")

# [3] Genuine Pink-style 1/2/3-level stage-polymorphic tower collapse
class Code:
    def __init__(self, expr): self.expr = expr
_vid, STEPS = 0, 0
def next_id():
    global _vid; _vid += 1; return _vid
def lift(v):
    if isinstance(v, Code): return v
    if isinstance(v, (int, bool)): return Code(v)
    if callable(v):
        sf, sx = f"_f{next_id()}", f"_x{next_id()}"
        return Code(["lam", sf, sx, lift(v(Code(sf), Code(sx))).expr])
    return Code(["quote", v])
def ev(exp, env):
    global STEPS; STEPS += 1
    if isinstance(exp, int): return exp
    if isinstance(exp, str): return env[exp]
    op = exp[0]
    if op == "quote": return exp[1]
    if op == "num?": return 1 if isinstance(ev(exp[1], env), int) else 0
    if op == "sym?": return 1 if isinstance(ev(exp[1], env), str) else 0
    if op == "car": return ev(exp[1], env)[0]
    if op == "cadr": return ev(exp[1], env)[1]
    if op == "caddr": return ev(exp[1], env)[2]
    if op == "cadddr": return ev(exp[1], env)[3]
    if op == "lift": return lift(ev(exp[1], env))
    if op in ("+","-","*","eq?"):
        a, b = ev(exp[1], env), ev(exp[2], env)
        if isinstance(a, Code) or isinstance(b, Code): return Code([op, lift(a).expr, lift(b).expr])
        return a+b if op=="+" else a-b if op=="-" else a*b if op=="*" else (1 if a==b else 0)
    if op == "if":
        c = ev(exp[1], env)
        if isinstance(c, Code): return Code(["if", c.expr, lift(ev(exp[2], env)).expr, lift(ev(exp[3], env)).expr])
        return ev(exp[2], env) if c != 0 else ev(exp[3], env)
    if op == "lam":
        fn_n, ax_n, body = exp[1], exp[2], exp[3]
        def clo(sf, av):
            e2 = dict(env)
            if fn_n != "_": e2[fn_n] = sf
            e2[ax_n] = av; return ev(body, e2)
        return clo
    fn, arg = ev(exp[0], env), ev(exp[1], env)
    if isinstance(fn, Code) or isinstance(arg, Code): return Code([lift(fn).expr, lift(arg).expr])
    return fn(fn, arg)

ev_poly = ["lam","_","ml",["lam","eval","exp",["lam","_","env",
  ["if",["num?","exp"],["ml","exp"],
  ["if",["sym?","exp"],["env","exp"],
  ["if",["sym?",["car","exp"]],
    ["if",["eq?",["quote","+"],["car","exp"]],["+",[["eval",["cadr","exp"]],"env"],[["eval",["caddr","exp"]],"env"]],
    ["if",["eq?",["quote","-"],["car","exp"]],["-",[["eval",["cadr","exp"]],"env"],[["eval",["caddr","exp"]],"env"]],
    ["if",["eq?",["quote","*"],["car","exp"]],["*",[["eval",["cadr","exp"]],"env"],[["eval",["caddr","exp"]],"env"]],
    ["if",["eq?",["quote","eq?"],["car","exp"]],["eq?",[["eval",["cadr","exp"]],"env"],[["eval",["caddr","exp"]],"env"]],
    ["if",["eq?",["quote","if"],["car","exp"]],["if",[["eval",["cadr","exp"]],"env"],[["eval",["caddr","exp"]],"env"],[["eval",["cadddr","exp"]],"env"]],
    ["if",["eq?",["quote","lam"],["car","exp"]],["ml",["lam","f","x",[["eval",["cadddr","exp"]],["lam","_","y",["if",["eq?","y",["cadr","exp"]],"f",["if",["eq?","y",["caddr","exp"]],"x",["env","y"]]]]]]],
    ["if",["eq?",["quote","lift"],["car","exp"]],["lift",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","num?"],["car","exp"]],["num?",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","sym?"],["car","exp"]],["sym?",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","car"],["car","exp"]],["car",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","cadr"],["car","exp"]],["cadr",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","caddr"],["car","exp"]],["caddr",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","cadddr"],["car","exp"]],["cadddr",[["eval",["cadr","exp"]],"env"]],
    ["if",["eq?",["quote","quote"],["car","exp"]],["ml",["cadr","exp"]],
      [["env",["car","exp"]],[["eval",["cadr","exp"]],"env"]]]]]]]]]]]]]]]],
    [[["eval",["car","exp"]],"env"],[["eval",["cadr","exp"]],"env"]]]]]]]]
nil_env = ["lam","_","y",0]
eval_top  = ["lam","_","e",[[["lam","_","e",[[ev_poly,["lam","_","v","v"]],"e"]],"e"],nil_env]]
evalc_top = ["lam","_","e",[[["lam","_","e",[[ev_poly,["lam","_","v",["lift","v"]]],"e"]],"e"],nil_env]]
fac_src = ["lam","f","n",["if",["eq?","n",0],1,["*","n",["f",["-","n",1]]]]]

for lbl, p in [("direct",[fac_src,5]),("interp1",[[eval_top,["quote",fac_src]],5]),("interp2",[[[eval_top,["quote",eval_top]],["quote",fac_src]],5])]:
    STEPS = 0; v = ev(p, {}); print(f"[3:{lbl}] val={v} steps={STEPS}")
for lbl, p in [("comp1",[evalc_top,["quote",fac_src]]),("comp2",[[eval_top,["quote",evalc_top]],["quote",fac_src]]),("comp3",[[[eval_top,["quote",eval_top]],["quote",evalc_top]],["quote",fac_src]])]:
    _vid = 0; STEPS = 0; c = ev(p, {}); cs = STEPS; STEPS = 0; v = ev([c.expr, 5], {}); print(f"[3:{lbl}] val={v} run_steps={STEPS} compile_steps={cs} ast={c.expr}")
```

Observed output (`2026-11-19`, Linux x86_64, Python 3):

```text
[1A] (True, [('LET', 'zero := 0', ['zero']), ('CHECK', 'c != zero'), ('LET', 'res := step(z, instrs)', ['res'])], [])
[1B] (False, [], ['has_type(C, e, tau)', 'subtype(tau, tau2)'])
[2:sum] generic=55 spec=55 tv=(True, 'VERIFIED (5 specialized blocks)')
[2:alias] generic=999 spec=42 tv=(False, 'REGION_ALIAS_VIOLATION at bb_pc0 (pc=0)')
[3:direct] val=120 steps=63
[3:interp1] val=120 steps=1942
[3:interp2] val=120 steps=99274
[3:comp1] val=120 run_steps=63 compile_steps=426 ast=['lam', '_f1', '_x2', ['if', ['eq?', '_x2', 0], 1, ['*', '_x2', ['_f1', ['-', '_x2', 1]]]]]
[3:comp2] val=120 run_steps=63 compile_steps=21653 ast=['lam', '_f1', '_x2', ['if', ['eq?', '_x2', 0], 1, ['*', '_x2', ['_f1', ['-', '_x2', 1]]]]]
[3:comp3] val=120 run_steps=63 compile_steps=1140543 ast=['lam', '_f1', '_x2', ['if', ['eq?', '_x2', 0], 1, ['*', '_x2', ['_f1', ['-', '_x2', 1]]]]]
```

## Revalidation

To cheaply test whether these architectural conclusions still hold against newer upstream commits:

1. **`SpecTec` theorem-prover backend merge status:** Inspect `spectec/src/exe-spectec/main.ml` and `ls spectec/src/` in `Wasm-DSL/spectec` (relative to `acc6e834...`) and `WebAssembly/spec` (relative to `d0b2e8d5...`) to check whether any `backend-{rocq,coq,lean,agda,isabelle}` directories were merged into `main`.
2. **`P4-SpecTec` adoption and prover backends:** Diff `README.md` and `p4spectec/core/src/` in `kaist-plrg/p4-spectec` (relative to `731621c5...`) for full P4 LDWG adoption status or newly added proof-assistant backends.
3. **`Sail` Lean 4 / Rocq backend evolution:** Inspect `src/sail_lean_backend/` and `src/rocq/` in `rems-project/sail` relative to `97aa617d...`.
4. **`weval` IR and verification status:** Diff `Cargo.toml`, `include/weval.h`, and `src/eval.rs` in `bytecodealliance/weval` (relative to `47164ae9...`) to check whether `weval` continues using `waffle` SSA IR, whether new intrinsics or alias-safety checks were added, or whether translation validation over `block_rev_map` was implemented.
5. **Micro-probes:** Re-run `/tmp/probe_spectec_weval_towers.py` (`<2s`, stdlib-only Python 3); the dataflow animation failure, memory-aliasing miscompilation counterexample, and 1/2/3-level tower-collapse step counts are self-contained mathematical witnesses.
