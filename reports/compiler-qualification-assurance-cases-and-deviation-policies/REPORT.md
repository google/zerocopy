# Compiler Qualification, Assurance Cases, and Deviation Documentation Precedents

## Summary

Industrial safety qualification frameworks (Ferrocene under ISO 26262 TCL3 /
ASIL D, IEC 61508 T3 / SIL 4, and IEC 62304 Class C; CompCert under DO-178C /
DO-330 TQL-1 and ISO 26262 ASIL D), foundational theorem-proving projects
(`seL4`, `CakeML`, `Anneal`), and alternative Rust compiler backends
(`rustc_codegen_cranelift`, `rustc_codegen_gcc`, `gccrs`, `mrustc`) converge on
five structural mechanisms for documenting guarantees, assumptions, deviations,
and known problems:

1. **Paragraph-granular requirement traceability (`rust-lang/fls` at `1.99`):**
   Ferrocene structures the **Ferrocene Language Specification (FLS)** (`946eacae`)
   into **29 `.rst` chapters containing 4,014 unique `:dp:` (`fls_<id>`)
   normative paragraph identifiers**. Every paragraph ID is linked in a
   bidirectional traceability matrix to one or more upstream `rustc` `tests/ui/`
   test cases, and every compiler release ships a **Safety Manual** (constraining
   permitted CLI flags, target triples, and environment variables) alongside a
   machine-queryable **Known Problems Register** mapping open upstream `I-unsound`
   and `I-miscompile` issues to user-level mitigations.
2. **Explicit trust-boundary and semantic-deviation tables (CompCert 3.18):**
   CompCert (`AbsInt/CompCert` at `74cbdbf0`) separates its documentation into
   three distinct tables required by DO-330 / ISO 26262 assessors:
   - **Supported subset restrictions:** Language features rejected with a hard
     compile-time diagnostic (VLAs, `setjmp`/`longjmp`, unstructured `switch`
     such as Duff's device, `_Complex`).
   - **Semantic deviations and tightenings:** Cases where CompCert C either fixes
     ISO C implementation-defined behavior (exact bitfield layout, signed shift
     semantics) or deviates from GCC extensions.
   - **Verified vs. unverified pass inventory:** A pass-by-pass table identifying
     which stages are Coq-proved (`Clight` through `Mach`/`Asm` and the BTL
     validator) versus unverified OCaml/system components (`cparser`, `C2C`
     elaboration, `Asmexpand`, external assembler and linker).
3. **Fail-closed feature-gap reporting in alternative Rust backends:**
   Both `rustc_codegen_cranelift` (`compiler/rustc_codegen_cranelift/Readme.md`,
   125 lines at `58cf8f9c`) and `rustc_codegen_gcc`
   (`compiler/rustc_codegen_gcc/Readme.md`, 189 lines) enforce a strict
   **fail-closed deviation discipline**: unsupported MIR constructs, target
   intrinsics, inline assembly options, or unwinding modes emit a deterministic
   compile-time error (`tcx.dcx().fatal(...)`) rather than silently generating
   unverified or approximate code.
4. **Formal theorem hypotheses vs. structured assumption ledgers (`CakeML`,
   `seL4`, `Anneal`):**
   - `CakeML` (`f7318949`) encodes all environmental preconditions directly inside
     the top-level HOL4 theorem `compile_correct` (`machine_ok`, `ffi_convention`,
     `enough_space`, `code_in_memory`).
   - `seL4` (`6b4076ae`) and `Anneal` (`joshlf/anneal` at `9027a6c9`,
     `THREAT_MODEL.md`) pair their mechanized kernel theorems with an explicit
     human-auditable **Assumption Ledger** and **Goal Structuring Notation (GSN)**
     assurance structure that catalogs every hardware, boot/loader, external FFI,
     and toolchain boundary assumption outside the logic kernel.
5. **Upstream `rustc` unspecified-behavior governance:**
   `rustc` `1.99.1` (`58cf8f9c`) explicitly declines to stabilize `repr(Rust)`
   field order, stack frame layout, or symbol hashes across builds—providing
   `-Zrandomize-layout` and `-Zlayout-seed=<u64>`
   (`compiler/rustc_ty_utils/src/layout.rs`) to catch unportable code—and uses a
   two-stage governance pipeline (**49 `@future_incompatible` lints** in
   `compiler/rustc_lint_defs/src/builtin.rs` combined with ecosystem-wide
   **Crater** runs) whenever tightening soundness bugs that affect existing crates.

## Applicability

These precedents apply directly to designing the **per-build attestation report**,
**assumption ledger**, **Supported Rust / Deviation Policy**, and **Known
Problems Register** for a verified Rust compiler targeting `rustc` `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and FLS `1.99`
(`946eacae5a4a33a89af7832178504692439e7478`).

- **Standard coverage:** The qualification artifacts analyzed here cover
  automotive (**ISO 26262:2018 Part 8 Clause 11**, Tool Confidence Level TCL3 up
  to ASIL D), industrial (**IEC 61508-3:2010 Clause 7.4.4**, Offline Support Tool
  Class T3 up to SIL 4), medical (**IEC 62304** Class C), and airborne
  (**DO-178C / DO-330**, Tool Qualification Level TQL-1 / TQL-5).
- **Relation to Anneal:** Extends Anneal's `THREAT_MODEL.md` and `docs/trust-model.md`
  (`joshlf/anneal` at `9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`) from crate-level
  functional verification (`Trusted.CrateTheorem`) to whole-toolchain compilation
  certificates and deviation ledgers.

## Findings

### 1. Ferrocene Qualification Architecture (ISO 26262 / IEC 61508 / IEC 62304)

`Basis: source + normative (rust-lang/fls@946eacae5a4a33a89af7832178504692439e7478 and qualification manual structure)`

Ferrocene (now upstreamed as the official Rust Project specification baseline in
`rust-lang/fls`) qualifies a pinned `rustc` + LLVM toolchain as an **ISO 26262
TCL3 / IEC 61508 T3** compiler without modifying the middle-end optimizer, using
four linked artifacts:

1. **Ferrocene Language Specification (`rust-lang/fls` at tag `1.99`,
   `946eacae5a4a33a89af7832178504692439e7478`):**
   - Direct inspection of `src/*.rst` shows **29 chapter files** containing
     **4,014 `:dp:\`fls_...\`` dynamic paragraph IDs** (for example,
     `src/types-and-traits.rst`, `src/expressions.rst`, `src/inline-assembly.rst`,
     `src/unsafety.rst`, `src/ffi.rst`).
   - Unlike the informal Rust Reference (`rust-lang/reference`), every normative
     sentence in FLS has a permanent random alphanumeric ID (`:dp:` role) so
     that edits to surrounding paragraphs never silently shift requirement IDs.
2. **Bidirectional Requirement-to-Test Traceability Matrix:**
   - Qualification under ISO 26262 Part 8 Clause 11.4.9 (Validation of the
     Software Tool) requires demonstrating that every normative paragraph in FLS
     is exercised by passing tests on every qualified target triple.
   - Ferrocene maps each of the 4,014 `:dp:` IDs to specific tests in `tests/ui/`,
     `tests/run-make/`, and `tests/codegen-llvm/`, tracking coverage gaps via an
     automated sphinx/python traceability builder.
3. **Safety Manual (Operational Constraints & Degraded Modes):**
   - Specifies the exact **Qualified Command-Line Invocation** (approved `-C
     opt-level`, `-C panic`, `-C codegen-units`, `-C target-cpu`, and linker
     flags).
   - Flags outside the qualified envelope (such as `-Z` unstable flags, arbitrary
     procedural macros executing unverified host code, or inline assembly) shift
     the verification obligation to the end-user's application safety case.
4. **Known Problems Register:**
   - Every open upstream `rust-lang/rust` or `llvm/llvm-project` defect labeled
     `I-unsound` or `I-miscompile` is triaged into a versioned database shipped
     with each release. Each entry states: (a) problem ID and upstream issue link,
     (b) affected versions and targets, (c) trigger conditions in user code, and
     (d) mandatory workaround or lint check required before deployment.

### 2. CompCert Qualification and Deviation Documentation (DO-178C / DO-330 & ISO 26262)

`Basis: source + documentation (AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6)`

CompCert (`v3.18`, `74cbdbf0`) combines formal Coq proof with a commercial
Qualification Kit (`Valex` + Tool Operational Requirements / Tool Accomplishment
Summary) to claim **DO-178C / DO-330 credit** (eliminating object-code-to-source
structural coverage review where the compiler proof applies). Its documentation
strictly separates three categories:

| Documentation Category | Concrete CompCert Precedent | Design Rule for a Verified `rustc` Replacement |
| :--- | :--- | :--- |
| **1. Supported Language Subset (Fail-Closed Rejections)** | Rejects C99 VLAs, `setjmp`/`longjmp`, non-structured `switch` (Duff's device), and passing bitfields by address, emitting hard errors in `C2C`. | Emit a hard diagnostic (and refuse to emit an "all-verified" attestation) if a crate uses an unverified feature, unless an explicit `#[allow_unverified(...)]` or fallback flag is passed and recorded in the certificate. |
| **2. Semantic Refinements vs. Deviations** | Defines signed integer overflow as two's-complement wrap in RTL/Mach (refining ISO C UB), fixes evaluation order in specific contexts, and documents exact struct/bitfield ABI rules per target (`common/Memdata.v`). | Distinguish **sound refinements** (making `rustc` unspecified behavior deterministic, such as fixing `repr(Rust)` field order) from **deviations** (any departure from defined Rust `1.99.1` behavior, which is forbidden). |
| **3. Verified vs. Unverified Pipeline Stages** | Explicitly lists `cparser`, `C2C` elaboration, `Asmexpand` pseudo-instruction expansion, and the system assembler/linker (`as`/`ld`) as unverified components requiring traditional testing (`Valex`) or downstream binary validation. | In every attestation report, enumerate the exact compiler stages inside the Lean 4 proof boundary (`Runtime(PostCleanup)` MIR -> target machine code / object bytes) and every stage outside it (`rustc` front-end up to borrowck, external dynamic linker). |

### 3. Alternative Rust Compilers and GCC / Clang Implementation-Defined Behavior

`Basis: source (rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67 compiler/rustc_codegen_cranelift/Readme.md and compiler/rustc_codegen_gcc/Readme.md)`

1. **`rustc_codegen_cranelift` (`compiler/rustc_codegen_cranelift/Readme.md`, lines
   1–125) and `rustc_codegen_gcc` (`compiler/rustc_codegen_gcc/Readme.md`, lines
   1–189):**
   - Both in-tree backends document their exact feature matrix at the top of
     their repository documentation (for example, `cg_clif` documents missing
     stack unwinding on Windows `-pc-windows-msvc`/`-gnu`, lack of SIMD auto-vectorization,
     and fallback to scalar emulation forunsupported vendor intrinsics; `cg_gcc`
     documents supported targets, LTO status, and GCC version requirements for
     128-bit integers and target features).
   - Both maintain machine-readable CI test-exclusion lists so that every skipped
     upstream `tests/ui/` or `std` test is explicitly accounted for in version
     control.
2. **`gccrs` and `mrustc`:**
   - `gccrs` tracks compliance via a milestone matrix keyed to FLS chapters and
     upstream `rustc` test suites.
   - `mrustc` explicitly scopes its guarantee to **bootstrapping trusted source**:
     it documents that it omits borrow checking (`borrowck`) and lifetime
     validation completely, relying on downstream compiled `rustc` to re-verify
     any code built during stage0 bootstrap.
3. **GCC and Clang implementation-defined behavior catalogs:**
   - ISO/IEC 9899 (C11/C17 §J.3) requires implementations to document all
     implementation-defined behavior. GCC satisfies this via a dedicated manual
     chapter (*"C Implementation-Defined Behavior"*, organized by ISO C clause:
     translation limits, environment, identifiers, characters, integers,
     floating-point, arrays/pointers, registers, structures/unions/enumerations/bitfields,
     qualifiers, declarators, statements, preprocessing directives, and library
     functions).
   - For Rust, FLS (`rust-lang/fls` at `946eacae`) and the Rust Reference
     (`rust-lang/reference` at `bcd62f35`) separate **defined across all targets**,
     **target-qualified** (pointer width, endianness, atomic widths, calling
     convention), and **unspecified** (`repr(Rust)` field order, trait object
     vtable layout, stack frame layout).

### 4. End-to-End Assumptions in Verified Software (`seL4`, `CakeML`, `Anneal`) and GSN

`Basis: source + normative (seL4/l4v@6b4076ae, CakeML/cakeml@f7318949, joshlf/anneal@9027a6c9 THREAT_MODEL.md)`

Verified systems use two complementary notations to prevent unstated gaps between
a formal theorem and real-world execution:

1. **Syntactic Theorem Antecedents (`CakeML` `compile_correct`):**
   In `CakeML/cakeml` (`f7318949`), the end-to-end compiler correctness theorem
   states:
   $$\text{machine\_ok}(\text{mc\_conf}) \land \text{ffi\_convention}(\text{ffi}) \land \text{code\_loaded}(\text{bytes}, \text{ms}) \implies \text{evaluate\_machine}(\text{ms}) \sqsubseteq \text{evaluate\_source}(\text{prog}) \cup \{\text{Resource\_limit\_hit}\}$$
   Every assumption about the target machine config (`mc_conf`), external OS
   calls (`ffi`), and available stack/heap memory (`Resource_limit_hit`) appears
   as an explicit predicate in the HOL4 theorem statement.
2. **Structured Assumption Ledgers and Goal Structuring Notation (GSN) (`seL4` &
   `Anneal`):**
   - Because hardware, bootloaders, DMA controllers, and kernel/user boundary
     switches exist outside the theorem prover's physical execution environment,
     `seL4` (`6b4076ae`) and `Anneal` (`joshlf/anneal` at
     `9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`, `THREAT_MODEL.md`) organize their
     assurance case around an explicit **Assumption Ledger** (in GSN terminology:
     top-level **Goal** $G_0$, decomposed via **Strategy** $S_1$ into kernel-proved
     **Subgoals** $G_1 \dots G_k$, discharged by **Solutions** $Sn_i$ [`.olean`
     proof objects], and bounded by explicit **Assumptions** $A_1 \dots A_m$ and
     **Contexts** $C_1 \dots C_n$).
   - In `Anneal`, `trusted/audit/` programmatically checks the compiled `.olean`
     environment to verify that `Trusted.CrateTheorem` depends only on the
     standard Lean 4 axioms (`propext`, `Quot.sound`, `Classical.choice`) and the
     explicitly declared specification boundary, rejecting `sorryAx`,
     `Lean.ofReduceBool` (`native_decide`), and user-declared `axiom`s.

### 5. `rustc` Policy on Changing Unspecified Behavior (`@future_incompatible`, Crater, `-Zrandomize-layout`)

`Basis: source (rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67 compiler/rustc_lint_defs/src/builtin.rs and compiler/rustc_ty_utils/src/layout.rs)`

1. **Layout randomization (`-Zrandomize-layout` and `-Zlayout-seed`):**
   - In `compiler/rustc_ty_utils/src/layout.rs` (lines 1–1090 at `58cf8f9c`),
     `repr(Rust)` structs, tuples, and enums intentionally do not guarantee source
     declaration order: by default `rustc` reorders fields by alignment and niche
     availability to minimize padding, and under `-Zrandomize-layout` permutes
     field order pseudorandomly using `-Zlayout-seed`.
   - **Rule for a verified `rustc` replacement:** Any deterministic field ordering
     that satisfies alignment, size, and niche invariants is a **sound refinement**
     of the Rust language specification; when bit-identical ABI interoperability
     with `rustc`-compiled `.rlib` artifacts in the same link unit is required,
     the backend must consume the exact `TyAndLayout` computed by
     `rustc_ty_utils::layout::layout_of`.
2. **Future-incompatibility lints and Crater runs (`compiler/rustc_lint_defs/src/builtin.rs`):**
   - At `58cf8f9c` (`1.99.1`), `compiler/rustc_lint_defs/src/builtin.rs` defines
     **49 `@future_incompatible = FutureIncompatibleInfo { ... }` lints** (lines
     195–5741), each tagged with a `FutureIncompatibilityReason` (`FutureReleaseError`,
     `FutureReleaseErrorReportNow`, `EditionError`, or `EditionSemanticsChange`).
   - Whenever `rustc` fixes an unsoundness bug or tightens unspecified behavior
     that could break existing crates on `crates.io`, the Compiler and Lang Teams
     run **Crater** across all public crates and stage the change via a warn-by-default
     → deny-by-default → hard-error `@future_incompatible` transition.

## Boundaries

- **Proprietary qualification dossier templates (`not examined`):** Commercial
  TÜV SÜD / AbsInt qualification certificates and private customer safety manuals
  under NDA were not examined; all findings derive from public upstream
  repositories (`rust-lang/fls`, `rust-lang/rust`, `AbsInt/CompCert`, `seL4/l4v`,
  `CakeML/cakeml`, `joshlf/anneal`) and published standards (ISO 26262, DO-330).
- **Certification authority sign-off (`known not to apply` automatically):**
  Producing a formal Lean 4 proof and GSN attestation report provides technical
  evidence for ISO 26262 TCL3 / DO-330 TQL-1 qualification, but formal regulatory
  qualification still requires assessment of the project's quality management and
  configuration management processes by an accredited assessor.

## Evidence

1. **Ferrocene Language Specification (`rust-lang/fls` at `1.99`):**
   - Repository: `rust-lang/fls` at `946eacae5a4a33a89af7832178504692439e7478`
   - Files: `src/*.rst` (29 chapter files containing 4,014 `:dp:\`fls_...\``
     normative paragraph markers).
2. **`rustc` `1.99.1` layout randomization, future-incompatible lints, and backend READMEs:**
   - Repository: `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`
   - Files:
     - `compiler/rustc_ty_utils/src/layout.rs` (lines 1–1090, `repr(Rust)` field
       reordering and `-Zrandomize-layout`).
     - `compiler/rustc_lint_defs/src/builtin.rs` (lines 195–5741, 49
       `@future_incompatible` lint declarations).
     - `compiler/rustc_codegen_cranelift/Readme.md` (lines 1–125).
     - `compiler/rustc_codegen_gcc/Readme.md` (lines 1–189).
3. **Anneal threat model and trust-boundary audit specification:**
   - Repository: `joshlf/anneal` at `9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`
   - Files: `THREAT_MODEL.md`, `docs/trust-model.md`, and `trusted/audit/src/main.rs`.
4. **Support artifacts preserved in this package:**
   - `support/qualification_deviation_matrix.json`: Structured metrics and
     precedent comparison table.
   - `support/probe_fls_and_rustc_deviations.py`: Verification script checking
     the preserved metrics.

## Revalidation

1. **Run the preserved verification script:**
   ```bash
   python3 reports/compiler-qualification-assurance-cases-and-deviation-policies/support/probe_fls_and_rustc_deviations.py \
     --matrix reports/compiler-qualification-assurance-cases-and-deviation-policies/support/qualification_deviation_matrix.json
   ```
2. **Re-count FLS `:dp:` paragraph IDs and `rustc` `@future_incompatible` lints on newer revisions:**
   ```bash
   python3 -c '
   import pathlib
   fls = pathlib.Path("<path-to-fls>/src")
   print("FLS :dp: count:", sum(p.read_text().count(":dp:`fls_") for p in fls.glob("*.rst")))
   builtin = pathlib.Path("<path-to-rust>/compiler/rustc_lint_defs/src/builtin.rs").read_text()
   print("future_incompatible count:", builtin.count("@future_incompatible = FutureIncompatibleInfo"))
   '
   ```
