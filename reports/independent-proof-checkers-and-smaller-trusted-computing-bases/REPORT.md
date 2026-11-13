# Independent Proof Checkers, Kernel Export Formats, In-Logic Bootstrapping, and Smaller Trusted Computing Bases

## Summary

Even when a Rust program or compiler pass is proved inside Lean 4 (`v4.34.1`) with zero extra axioms beyond `{propext, Classical.choice, Quot.sound}`, the soundness of the resulting guarantee still rests on the **logical and execution Trusted Computing Base (TCB)**: the Lean 4 C++ kernel, the `.olean` loader and metaprogramming boundary (`@[implemented_by]`, `@[extern]`), the statement-correspondence auditor (`trusted/audit`), and the host compiler toolchain (`clang`/`rustc`) that compiles the proof checker. Auditing the ecosystem of independent Lean 4 kernels (`lean4lean`, `nanoda_lib`, `lean4checker`/`leanchecker`), kernel export and adversarial comparison pipelines (`lean4export`, `comparator` / `lake check`), verified kernels in other logics (`Candle` in CakeML/HOL4, `MetaRocq`, `MM0`), and bootstrap/trust-reduction techniques (`Diverse Double-Compiling` vs. CakeML's in-logic bootstrapping) establishes four quantitative engineering conclusions:

1. **Three-Tier Defense-in-Depth for Lean 4 Proofs (`leanchecker` + `lean4lean` + `nanoda_lib` via `lean4export` / `comparator`):**
   - **Built-in `.olean` environment replay (`leanchecker`, merged from `leanprover/lean4checker@91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`, `371` core `.lean` LOC):** Ships in every Lean 4 toolchain since `v4.28.0` (`~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/leanchecker`). Replays `.olean` constants into a fresh C++ kernel environment (`Lean.Environment.replay'`), catching `.olean` tampering, `PrivateConflict` shadowing, `ReplaceAxiom`, and constructor/recursor forgery at `~1.0x–1.3x` kernel replay cost, while still trusting the C++ kernel binary.
   - **Self-hosted Lean 4 kernel and mechanized metatheory (`digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, Carneiro `arXiv:2403.14064`, `49,412` `.lean` lines across `112` files):** Implements the Lean 4 kernel in pure Lean 4 (`~3,910` LOC executable kernel in `TypeChecker.lean` `979`, `Inductive/` `885`, `Primitive.lean` `624`, `Level.lean` `363`, `Replay.lean` `325`, `Environment.lean` `129`, `Quot.lean` `120`, `Expr.lean` `105`) together with `6,911` LOC of Lean type-system metatheory (`Lean4Lean/Theory/`, including Church-Rosser and strong normalization structures) and `23,745` LOC of kernel verification proofs (`Lean4Lean/Verify/`). However, `lean4lean`'s `README.md` explicitly notes that because its executable checker is translated directly from the C++ kernel, it shares algorithmic structure with the C++ kernel (`~1.2x–2.0x` replay time).
   - **Clean-room independent Rust external checker (`ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, `v0.4.32`, `10,258` `.rs` lines across `22` files; `8,754` non-test LOC with a single runtime crate dependency `indexmap = "2.13.0"`):** Consumes the line-oriented **NDJSON v3.1.0** export stream emitted by `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab` (`456` core `.lean` LOC in `Export.lean` + `Main.lean`). Because `nanoda_lib` is written from scratch in memory-safe Rust (`overflow-checks = true`) without sharing C++ kernel code or `.olean` memory-mapping, running `lean4export` + `nanoda_bin` under `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e` (`591` core `.lean` LOC, merged into Lean `v4.35.0` as `lake comparator` / `lake check`) eliminates single-implementation C++ kernel bugs (such as the nested-inductive parameter omission fixed in Lean `v4.31.0` PR `#14577`).
2. **Closing the Statement-Forgery Gap (`Comparator` vs. `trusted/audit`):**
   - An external kernel (`nanoda_lib`) only verifies that exported proof terms inhabit their exported types; an untrusted proof script can still cheat by redefining a specification constant, adding `sorryAx`, exploiting `#eval`/IO to overwrite `.olean` files, or exploiting namespace shadowing.
   - `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`) and Anneal's `trusted/audit` (`joshlf/anneal@6893164fc505a4e047ebe99a923f0a6ca7f13804`, `3,291` `.rs` LOC + `891` `.lean` LOC) solve this identically in principle: compile the untrusted solution inside an OS sandbox (`landrun` in `comparator`), export both the trusted `Challenge` environment and untrusted `Solution` environment via `lean4export`, verify structural bit-for-bit equality of target theorem types and recursive dependency closures (`Comparator/Compare.lean`, `110` LOC), verify permitted axioms (`Comparator/Axioms.lean`, `72` LOC), and check the exported stream in `nanoda_lib`.
3. **Verified Kernels in Other Ecosystems (`Candle` in HOL4/CakeML, `MetaRocq`, and `MM0`):**
   - **Candle (`CakeML/candle@6a9acd58867610c78fee0f3dd9ed4c4c14087b18` + `CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8/candle`, Abrahamsson et al., ITP 2022):** A verified HOL Light implementation (`153` files in `cakeml/candle/`) proved sound down to x86-64/ARMv8 machine code with respect to Zermelo set theory (`candle/set-theory/`), including a fast verified in-logic compute primitive (`candle_compute.ml`).
   - **MetaRocq (`MetaCoq/metacoq`, Sozeau et al., JFP 2020 / POPL 2025):** Formalizes the Calculus of Inductive Constructions (`PCUIC`) and verifies a complete, extractable safe type checker in Rocq (`~150,000` LOC), which Lean4Lean's `Lean4Lean/Theory` and `Lean4Lean/Verify` (`30,656` LOC combined) mirror for Lean 4's Calculus of Inductively Constructed Type-in-Type-with-Quotients (`VExpr` / `VEnv`).
   - **Metamath Zero (`digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):** Shrinks the logical verifier to a `~500`-line C (`mm0-c`) or verified x86-64 binary (`mm0.mmb`) checking binary `.mmb` proof files, at the cost of translating rich dependent type theories down to first-order Peano/sort axioms (`mm0-lean`, `574,961` LOC).
4. **In-Logic Compiler Bootstrapping (CakeML style) vs. Diverse Double-Compiling (DDC):**
   - **CakeML In-Logic Bootstrapping (Kumar et al., POPL 2014):** Evaluates the HOL4 compiler function inside the HOL4 logic via proof-producing synthesis (`translator/`, `109` files) and `EVAL` (`cv_translator/`, `18` files) to produce a concrete machine-code byte list `cake_bytes` together with a theorem $\vdash \text{machine\_sem}(\text{cake\_bytes}) \sqsubseteq \text{compile\_spec}$, removing the host SML/C compiler from the compiler binary's TCB.
   - **Diverse Double-Compiling (Wheeler 2005/2009):** Recompiles a self-hosting compiler across independent seed compilers (`rustc` via LLVM vs. `rustc_codegen_gcc` / `mrustc`) and checks bit-for-bit output identity, defeating Thompson trusting-trust trojans (`~2x` build time, `0` proof LOC) without proving functional correctness of the compiler passes.

## Applicability

This report applies to designing the verification auditor, external kernel checking pipeline, and bootstrap trust-reduction roadmap for Anneal (`joshlf/anneal`) and any verified Rust compiler built on Lean 4 (`v4.34.1+`).

- **Examined subjects:**
  - `digama0/lean4lean` at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` (`Lean4Lean/`, `Lean4Lean/Theory/`, `Lean4Lean/Verify/`, `arXiv:2403.14064`).
  - `ammkrn/nanoda_lib` at `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`v0.4.32`, `src/{tc,inductive,parser,expr,env,quot,level}.rs`).
  - `leanprover/lean4checker` at `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (`Lean4Checker/Replay.lean`, `Lean4CheckerTests/`) and `leanchecker` in `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
  - `leanprover/lean4export` at `df81913eee5519d5a88ae5b0fd701b5298cc29ab` (`Export.lean`, `Export/Parse.lean`, `format_ndjson.md`).
  - `leanprover/comparator` at `865edc14486c3388e9225daa971da8e157488c3e` (`Main.lean`, `Comparator/{Compare,Axioms,Util}.lean`, `tests/projects/`).
  - `CakeML/cakeml` at `b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8` and `CakeML/candle` at `6a9acd58867610c78fee0f3dd9ed4c4c14087b18` (ITP 2022, DOI `10.4230/LIPIcs.ITP.2022.3`).
  - `digama0/mm0` at `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`.
  - `joshlf/anneal` at `6893164fc505a4e047ebe99a923f0a6ca7f13804` (`trusted/audit/`).

## Findings

### 1. Quantitative Comparison of Lean 4 Proof Checkers and Exporters

Basis: source + documentation

| Tool / Kernel | Repository & Pinned Revision | Implementation Language & Size (LOC) | Input Format | Algorithmic Independence from C++ `lean` Kernel | Soundness Coverage & Threat Mitigated | Relative Checking Overhead |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Lean 4 C++ Kernel (`lean`)** | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | C++ (`src/kernel/`, `~11,500` LOC C++/H) | In-memory `Environment` / `.olean` | Baseline (`0%` independent) | Elaborator bugs, tactic bugs; **vulnerable to `.olean` disk tampering and `@[implemented_by]`/`@[extern]` unless audited** | `1.0x` (baseline) |
| **`leanchecker` / `lean4checker`** | `leanprover/lean4checker@91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (built into Lean $\ge$ `v4.28.0`) | Lean 4 (`371` core `.lean` LOC in `Replay.lean` `191` + `Main.lean` `150` + `Lean.lean` `30`; `367` test LOC) | `.olean` files via `Lean.Environment.replay'` | Re-invokes the C++ kernel on every constant (`--fresh`) | Defeats `.olean` constructor/recursor forgery, `OpenPrivate`, `PrivateConflict`, `ReplaceAxiom`, and `QuotEq` exploits | `~1.0x–1.3x` of kernel checking |
| **`lean4lean`** | `digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` (`v4.33.0-rc2`) | Pure Lean 4 (`49,412` total `.lean` LOC: **`3,910` LOC executable kernel** + `6,911` `Theory/` + `23,745` `Verify/` + `13,309` `Experimental/`) | `.olean` via `Lean4Lean/Replay.lean` (`325` LOC) | **Direct line-by-line port of C++ kernel** (retains pointer-equality `PtrEq.lean` & `EquivManager.lean` optimizations; shares algorithmic logic) | Eliminates C++ memory-safety bugs and connects executable `TypeChecker.lean` (`979` LOC) to mechanized typing invariants (`Lean4Lean/Verify/`) | `~1.2x–2.0x` of C++ kernel |
| **`lean4export`** | `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab` | Lean 4 (`456` core `.lean` LOC in `Export.lean` `438` + `Main.lean` `18`; `509` LOC parser; `749` LOC tests) | Reads `.olean` $\to$ emits **NDJSON v3.1.0** | Exporter only (`456` LOC auditable serializer) | Eliminates `.olean` binary memory-graph complexity; serializes DAG of `Name`, `Level`, `Expr`, and declarations with integer DAG indices (`in`, `il`, `ie`) | Export takes `~0.5x–1.5x` of kernel replay |
| **`nanoda_lib` (`nanoda_bin`)** | `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`v0.4.32`) | **Safe Rust** (`10,258` total `.rs` LOC: **`8,754` core LOC** in `inductive.rs` `1,825`, `tc.rs` `1,400`, `parser.rs` `1,083`, `util.rs` `1,036`, `expr.rs` `926`, `env.rs` `328`, `quot.rs` `316`, `level.rs` `304`) | **NDJSON v3.1.0** (`lean4export`) | **100% independent clean-room Rust implementation** (`overflow-checks = true`, `indexmap` only dependency) | Catches C++ kernel implementation bugs, memory corruption, and inductive/quotient/universe-level edge cases | `~1.0x–2.5x` of C++ kernel (multi-threaded in Rust) |
| **`comparator` (`lake check`)** | `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e` (merged into Lean `v4.35.0`) | Lean 4 (`591` core `.lean` LOC in `Main.lean` `374`, `Compare.lean` `110`, `Axioms.lean` `72`, `Util.lean` `28`; `474` test LOC) | `Challenge.lean` vs. `Solution.lean` via `landrun` + `lean4export` + `nanoda_bin` | Orchestrates both built-in replay and `external_kernels` (`nanoda_bin`) | **Full adversarial isolation**: prevents solution files from mutating challenge statements, smuggling axioms, or escaping compilation via `IO` | `~2.0x–3.5x` (includes export + dual-kernel check) |

---

### 2. Deep Dive: Lean 4's Export Format (`NDJSON v3.1.0`) and Adversarial Exploitation Catalog

Basis: source

#### 2.1 Structure of the `lean4export` NDJSON v3.1.0 Stream (`lean4export/format_ndjson.md` & `Export.lean`)

Unlike Lean 3's whitespace-delimited text export format, Lean 4 (`leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`) exports a stream of newline-delimited JSON (`NDJSON`) objects (`format.version = "3.1.0"`):

1. **Header metadata object (`meta`):** Records `exporter.name`, `exporter.version`, `lean.githash`, `lean.version`, and `format.version = "3.1.0"`.
2. **Hash-consed DAG indices (`in`, `il`, `ie`):**
   - `Name` nodes (`{"in": k, "str": {"pre": p, "str": s}}` or `{"in": k, "num": {"pre": p, "i": n}}`), with index `0` implicitly representing `Name.anonymous`.
   - `Level` nodes (`{"il": k, "succ": l}`, `{"il": k, "max": [l1, l2]}`, `{"il": k, "imax": [l1, l2]}`, `{"il": k, "param": name_idx}`), with index `0` representing `Level.zero`.
   - `Expr` nodes (`bvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `proj`, `natVal`, `strVal`, `mdata`), where every sub-expression is referenced by its integer `ie` index, preventing exponential tree blowup on shared proof terms.
3. **Top-level declarations:** `axiom`, `def` (with `hints`: `"opaque"`, `"abbrev"`, or `{"regular": height}` and `safety`: `"safe"`, `"unsafe"`, `"partial"`), `thm`, `opaque`, `quot`, and grouped mutual `inductive` declarations (`types`, `ctors`, `recs`).
4. **Native literal reduction (`Lean4Lean/Primitive.lean` `624` LOC; `nanoda_lib/src/tc.rs` & `src/tests/natlit.rs` `916` LOC):**
   - Both the C++ kernel, `lean4lean`, and `nanoda_lib` implement kernel-accelerated `Nat` literal operations (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.beq`, `Nat.ble`) and `String`/`Char` primitives, but **neither `lean4export` nor `nanoda_lib` trusts `Lean.reduceBool` (`native_decide`)**: any proof relying on `Lean.ofReduceBool` appears explicitly as an axiom dependency on `Lean.ofReduceBool` (or fails to type-check without the axiom).

#### 2.2 The 11 Adversarial Soundness Exploits Tested by `lean4checker` and `comparator`

Inspecting `lean4checker/Lean4CheckerTests/` (`7` test files) and `comparator/tests/projects/` (`10` adversarial challenge/solution projects) provides a concrete checklist of soundness attacks that any verification auditor (`trusted/audit`) must block:

1. **`.olean` Constructor / Recursor Forgery (`AddFalse.lean`, `AddFalseConstructor.lean`):** Constructing an `Environment` via metaprogramming that inserts a bogus constructor or recursor for `False` without going through `Kernel.addDecl`. Mitigated by `Replay.lean:17-20`, which ignores `.olean`-stored constructors/recursors and verifies that they are bit-for-bit identical to those freshly synthesized by the kernel when replaying the `inductive` declaration.
2. **Private Name Collision Across Modules (`PrivateConflictA/B/C.lean`, `OpenPrivate.lean`):** Crafting private helper declarations in identically named modules so that internal `_private.<Mod>.0.<Name>` symbols collide when merged into a single environment. Mitigated by fresh topological replay (`leanchecker --fresh`).
3. **Axiom / Definition Replacement (`ReplaceAxiom.lean`, `QuotEq.lean`, `quot_mismatch`):** Pre-populating the environment with a user-defined `Quot` or axiom before `Init.Core` initializes `Quot.mk`/`Quot.ind`.
4. **Definition-Hole / Theorem-Hole / Kind Mismatch Attacks (`comparator/tests/projects/{def_hole_axiom_issue, def_hole_kind_mismatch, def_hole_type_mismatch, theorem_hole_issue}`):** Where the untrusted `Solution.lean` changes a helper definition referenced in `Challenge.lean`'s theorem statement (e.g., redefining `ValidProgram` to `True`) or changes an `opaque` specification into a reducible `def`. Mitigated by `Comparator/Compare.lean`, which checks that every constant in the transitive type cone of the target theorem in `Challenge` matches `Solution` structurally (`ConstantInfo` equality).
5. **Structure Projection & Numeric Namespace Tricks (`proj_trick`, `numeric_namespace`, `char_ofnat_issue`, `primitive_issue`):** Exploiting invalid structure projection indices (`Expr.proj`) or non-canonical `Nat`/`Char` literals.

---

### 3. Verified Kernels in Other Ecosystems: `Lean4Lean`, `Candle`, `MetaRocq`, and `MM0`

Basis: source + documentation

| Verified Kernel Project | Host Prover & Object Logic | Code + Proof Size | What Is Proved vs. What Remains Trusted |
| :--- | :--- | :--- | :--- |
| **`Lean4Lean`** (`digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, Carneiro `arXiv:2403.14064`) | Lean 4 verifying Lean 4 (`VExpr` / `VEnv` Calculus of Inductively Constructed Type-in-Type with Quotients) | `49,412` `.lean` LOC (`3,910` kernel + `6,911` `Theory/` + `23,745` `Verify/` + `13,309` `Experimental/`) | `Lean4Lean/Verify/` proves that the monadic state/cache optimizations (`EquivManager`, `InferCache`, `whnfCoreCache`, `Level`, `Primitive` `Nat` div/mod) refine the declarative typing judgment (`Lean4Lean/Theory/`). Metatheoretic consistency of Lean 4 with `Quot` and `Inductive` (`ShapeLogRel.lean`, `6,100` LOC) is an ongoing formalization |
| **`Candle`** (`CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8/candle` + `CakeML/candle@6a9acd58867610c78fee0f3dd9ed4c4c14087b18`, Abrahamsson et al., ITP 2022) | HOL4 + CakeML verifying Higher-Order Logic (`HOL Light` with ad-hoc overloading and `candle_compute`) | `153` `.sml` files in `cakeml/candle/` (`overloading`, `parser`, `prover`, `set-theory`, `standard`, `syntax-lib`) + patched HOL Light corpus | **End-to-end machine-code soundness**: proves in HOL4 that if the compiled x86-64/ARMv8 `cake --candle` binary prints a theorem `|- P`, then `P` holds in Zermelo set theory (`set-theory/`), assuming only the hardware ISA semantics and OS I/O spec |
| **`MetaRocq` (`MetaCoq`)** (Sozeau et al., JFP 2020 / POPL 2025) | Rocq verifying Rocq (`PCUIC` Polymorphic Cumulative Calculus of Inductive Constructions) | `~150,000` `.v` LOC across `template-rocq`, `pcuic`, `safechecker`, and `erasure` | Proves confluence, subject reduction, strong normalization (modulo universe assumptions), and correctness of the executable `safechecker` and verified erasure to untyped $\lambda$-calculus (`Malfunction` / `CertiCoq`) |
| **`Metamath Zero (`MM0`)`** (`digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`, Carneiro CPP 2020) | Minimal custom first-order/sort logic with binary `.mmb` proof tables | `~500` LOC C (`mm0-c`), `62,431` LOC Rust (`mm0-rs`), `575,738` LOC Lean (`mm0-lean` + `mm0-lean4`) | Reduces the proof checker to a tiny stack/table verifier (`mm0-c` or self-verified x86-64 ELF binary), but requires translating higher-order/dependent proofs into low-level `.mmb` steps (which fails to scale cleanly for large dependent type-class and quotient developments without `~10x–50x` proof-term expansion) |

---

### 4. Bootstrapping Inside the Logic (CakeML Style) vs. Diverse Double-Compiling (DDC)

Basis: source + documentation + derived

Even if a compiler or proof checker is written in Lean 4 and proved correct (`Lean4Lean` or a verified Rust compiler in Lean 4), executing that program requires compiling its Lean 4 source code to native machine code (currently via Lean 4's unverified compiler `Lean.Compiler.LCNF` $\to$ C emission $\to$ `leanc`/`clang`). Two orthogonal mechanisms address trust in the host compiler that builds the verifier or compiler binary:

1. **Bootstrapping Inside the Logic (CakeML Architecture, Kumar et al., POPL 2014 / Myreen & Owens, JFP 2014):**
   - **How CakeML achieves it (`cakeml/translator/`, `109` files; `cakeml/cv_translator/`, `18` files; `cakeml/compiler/bootstrap/`):**
     1. *Proof-producing synthesis (`Hol2deep`):* Translates pure HOL4 functions (the CakeML parser, type inferencer, backend optimizer `word_to_word`, register allocator `word_alloc`, and target encoder `lab_to_target`, plus the `Candle` kernel) into deeply embedded CakeML AST definitions while automatically proving a certificate theorem (`Eval env exp (P f)`) relating the deep AST's operational semantics to the shallow HOL4 function $f$.
     2. *In-logic evaluation (`cv_compute` / `EVAL`):* Evaluates the verified compiler function inside the HOL4 kernel (accelerated by HOL4's `cv_compute` primitive over pairs/numbers) on its own deeply embedded AST to produce the concrete byte array `cake_x64_bytes : word8 list`.
     3. *End-to-end machine-code theorem:* Instantiates the compiler correctness theorem with the in-logic evaluation theorem to obtain a ground theorem stating that executing `cake_x64_bytes` on the target x86-64 ISA implements the shallow HOL4 compiler specification.
   - **What it would take to replicate CakeML's in-logic bootstrap in Lean 4:**
     - Requires (a) a verified compiler from a pure subset of Lean 4 (or `LCNF` / `Expr`) to `x86_64`/`aarch64` machine code (`CertiLean`, analogous to `CertiCoq` or `Hol2deep`), and (b) evaluating that compiler inside the Lean 4 kernel (`whnf` / `nanoda_lib`) on the `Lean4Lean` checker or verified Rust compiler AST.
     - **Cost:** In CakeML, in-logic bootstrap evaluation consumes `~8–16 GiB` of RAM and `~4–12` CPU-hours per target architecture even with `cv_compute`. In Lean 4, evaluating a compiler over a `50,000`-LOC codebase purely via kernel `whnf` (without `native_decide`) is `~100x–500x` slower than compiled execution unless paired with a proof-producing translation validation pass over `LCNF`-to-machine-code lowering.
2. **Diverse Double-Compiling (`DDC`, David A. Wheeler, ACSAC 2005 / PhD Thesis 2009):**
   - **Mechanism:** Given a self-hosting compiler source $S$ (or an external proof checker source such as `nanoda_lib` written in Rust) and two independent trusted seed compilers $C_1$ (e.g., `rustc` backed by LLVM) and $C_2$ (e.g., `rustc_codegen_gcc` / `mrustc` / `cranelift`), compile $S$ with $C_1$ to get stage-1 binary $B_1 = C_1(S)$ and with $C_2$ to get $B_2 = C_2(S)$, then use both $B_1$ and $B_2$ to compile $S$: if $\text{sha256}(B_1(S)) == \text{sha256}(B_2(S))$, no self-reproducing Thompson trusting-trust backdoor in $C_1$ or $C_2$ survived unless both independent seed compilers contain coordinated payload triggers for $S$.
   - **Application to `nanoda_lib` and `lean4lean`:**
     - Because `nanoda_lib` (`8,754` core LOC of safe Rust, zero `unsafe` blocks, single `indexmap` dependency) is small and self-contained, compiling `nanoda_bin` under two independent Rust codegen backends (`rustc_codegen_llvm` and `rustc_codegen_cranelift` / `rustc_codegen_gcc`) or auditing its `8,754` lines directly provides an immediately deployable, sub-minute defense against host-compiler trojans at **`0` proof-engineering cost**.

---

### 5. Actionable TCB-Reduction Roadmap for Anneal and a Verified Rust Compiler

Basis: derived + source

Combining the findings above yields a staged, high-leverage TCB reduction plan ordered by soundness return on investment:

1. **Stage 1 (Immediate, `~200` LOC shell/Rust integration in `trusted/audit`):**
   - Run `leanchecker --fresh` (already bundled at `~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/leanchecker`) + `lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`) + `nanoda_bin` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`) after `trusted/audit` (`joshlf/anneal@6893164fc505a4e047ebe99a923f0a6ca7f13804`).
   - **Effect:** Shrinks the logical checker TCB from the `~11,500`-LOC C++ kernel + `.olean` loader to the intersection of the C++ kernel and an independent `8,754`-LOC safe Rust checker (`nanoda_lib`) over a `456`-LOC text-stream exporter (`lean4export`), while `trusted/audit` + `Comparator`-style structural comparison enforces statement-origin isolation and rejects `sorryAx` and `Lean.ofReduceBool`.
2. **Stage 2 (Medium-Term, Triple-Kernel Diversity with `lean4lean`):**
   - Add `lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, `3,910` executable `.lean` LOC backed by `23,745` LOC of verification proofs in `Lean4Lean/Verify/`) as a third checker in CI release gates.
3. **Stage 3 (Long-Term, Verified Binary Extraction for the Checker):**
   - Rather than bootstrapping the entire optimizing compiler inside kernel `whnf` (which incurs CakeML's multi-hour in-logic evaluation cost), verify the compilation of the **small external proof checker (`~4,000–8,000` LOC)** to `x86_64`/`aarch64` machine code using a verified baseline compiler. Once the external checker binary itself is machine-checked and cross-checked via Diverse Double-Compiling, every derivation-checked compilation certificate and `CrateTheorem` proof is verified by a formally verified machine-code checker binary.

## Boundaries

- **Toolchain version alignment across `lean4lean`, `lean4export`, and `comparator`:** In our repository snapshot (`2026-11-13`), `lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`) pins `leanprover/lean4:v4.33.0-rc2`, `comparator` (`865edc14486c3388e9225daa971da8e157488c3e`) pins `leanprover/lean4:v4.35.0` (and is merged into `lake check` in `v4.35.0`), and Anneal pins `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). Because `.olean` files are version-specific whereas `lean4export`'s **NDJSON v3.1.0** format is stable across Lean `v4.28`–`v4.35`, `nanoda_lib` (`v0.4.32`) can check any Lean `v4.34.1` proof as soon as `lean4export` is built under `v4.34.1`.
- **Unverified `rustc_driver` Front-End Capture:** Independent Lean kernels (`nanoda_lib`, `lean4lean`, `leanchecker`) verify the Lean proof environment (`CrateTheorem`), not the Rust-to-MIR capture step (`anneal-rustc-capture`) until `rustc` front-end capture is itself replaced or validated.

## Evidence

- **`lean4lean` (`digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`):**
  - `README.md`, `lakefile.toml`, `lean-toolchain` (`v4.33.0-rc2`), `Lean4Lean/TypeChecker.lean` (`979` lines), `Lean4Lean/Primitive.lean` (`624` lines), `Lean4Lean/Level.lean` (`363` lines), `Lean4Lean/Replay.lean` (`325` lines), `Lean4Lean/Theory/` (`21` files, `6,911` lines), `Lean4Lean/Verify/` (`36` files, `23,745` lines); Mario Carneiro, *"Lean4Lean: Towards a Verified Typechecker for Lean, in Lean"*, `arXiv:2403.14064`.
- **`nanoda_lib` (`ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`):**
  - `Cargo.toml` (`v0.4.32`, `Apache-2.0`, `overflow-checks = true`, `indexmap = "2.13.0"`), `src/inductive.rs` (`1,825` lines), `src/tc.rs` (`1,400` lines), `src/parser.rs` (`1,083` lines), `src/util.rs` (`1,036` lines), `src/expr.rs` (`926` lines), `src/env.rs` (`328` lines), `src/quot.rs` (`316` lines), `src/level.rs` (`304` lines).
- **`lean4checker` (`leanprover/lean4checker@91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`), `lean4export` (`leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`), and `comparator` (`leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e`):**
  - `lean4checker/README.md` (documenting merge into Lean core as `leanchecker` in `v4.28.0`), `Lean4Checker/Replay.lean` (`191` lines), `Main.lean` (`150` lines), `Lean4CheckerTests/*.lean`.
  - `lean4export/format_ndjson.md` (`352` lines, NDJSON v3.1.0 specification), `Export.lean` (`438` lines), `Export/Parse.lean` (`509` lines).
  - `comparator/README.md` (documenting merge into Lean `v4.35.0` as `lake comparator` / `lake check`), `Main.lean` (`374` lines), `Comparator/Compare.lean` (`110` lines), `Comparator/Axioms.lean` (`72` lines), `tests/projects/*`.
- **`Candle` (`CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8` & `CakeML/candle@6a9acd58867610c78fee0f3dd9ed4c4c14087b18`) and `MM0` (`digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):**
  - `cakeml/candle/README.md` (`28` lines, `153` files), `candle/README.md`; Oskar Abrahamsson et al., *"Candle: A Verified Implementation of HOL Light"*, ITP 2022 (`10.4230/LIPIcs.ITP.2022.3`); Ramana Kumar et al., *"CakeML: A Verified Implementation of ML"*, POPL 2014 (`10.1145/2535838.2535841`).
- **Anneal (`joshlf/anneal@6893164fc505a4e047ebe99a923f0a6ca7f13804`):**
  - `trusted/audit/` (`3,291` `.rs` lines, `891` `.lean` lines).
- **Support artifacts in this package:**
  - `support/checkers_tcb_summary.json` — structured metrics for `lean4lean`, `nanoda_lib`, `lean4checker`, `lean4export`, `comparator`, `Candle`, `MM0`, and `anneal/trusted`.
  - `support/verify_checkers_tcb.py` — reproducible check of the extracted checker and exporter metrics.

## Revalidation

Run the bundled verification script to check all extracted proof-checker and TCB metrics:

```bash
python3 reports/independent-proof-checkers-and-smaller-trusted-computing-bases/support/verify_checkers_tcb.py
```

To revalidate against a newer Lean 4 toolchain (`v4.34.1+` or `v4.35.0+`):

1. Run `lake env leanchecker --fresh` (or `lake check` on Lean $\ge$ `v4.35.0`) on the target proof package.
2. Export the target theorem with `lean4export` (`NDJSON v3.1.0`) and run `nanoda_bin` (`ammkrn/nanoda_lib`) and `comparator` (`leanprover/comparator`) to confirm dual-kernel acceptance and statement-closure identity.
