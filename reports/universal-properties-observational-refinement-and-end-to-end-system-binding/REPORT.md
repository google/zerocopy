# Universal Properties, Observational Refinement, and End-to-End System Binding

## Summary

Internal module specifications, intermediate representation (IR) semantics, calling-convention adapters, and ghost ownership algebras can be removed from the human-audited Trusted Computing Base (TCB) by anchoring verification strictly at minimal whole-system observable I/O and machine-boundary contracts. When vertical compilation passes telescope by transitivity and horizontal FFI contracts cancel under closed-program linking, the audit surface collapses to three components: the source/target boundary semantics, the ABI boundary codec, and the content-addressed build-to-binary binding.

Five architectural principles govern end-to-end observational anchoring:

1. **Vertical Telescoping Erases Intermediate IRs, While Unverified Emitters Re-Open the TCB.** CompCert (`AbsInt/CompCert`) composes 20+ relational compiler passes (`Csyntax` through `Asm`) so intermediate IR semantics (`Clight`, `C#minor`, `Cminor`, `RTL`, `LTL`, `Linear`, `Mach`) disappear from the endpoint backward simulation—yet CompCert's verified chain stops at `Asm.program`, leaving `PrintAsm` pretty-printing, external assembling, and linking outside Coq (`driver/Driver.ml`). CakeML (`CakeML/cakeml`) closes this serializer/assembler gap by verifying byte-level `lab_to_target` machine-code emission directly down to hardware ISA + `FFI_outcome` I/O traces.
2. **Horizontal Linking Cancels Internal FFI Contracts and Separation-Logic Ghost State.** Open-module frameworks—CompCertO (`CertiKOS/compcert@compcerto`), DimSum (`gitlab.mpi-sws.org/iris/dimsum`), and Conditional Contextual Refinement (`CCR-project/ccr`)—prove local module refinements using rich internal abstractions (calling-convention algebras `cc_compose`, decentralized event-emitting LTS modules, and PCM/separation-logic pre/post wrappers `HoareCall`/`HoareFun`). Upon closed-system linking, theorems such as CCR's Assumption Cancellation Theorem (`adequacy_type_arg_stb`) erase all internal pre/post contracts and ghost state (`URA.wf`), leaving pure closed-program trace inclusion `Beh(tgt) ⊆ Beh(src)`.
3. **Observable-Spine & Cartesian `FrameFiberCodec` Contracts Permit Legal Target Slack While Blocking Spoofing.** Real ABIs (such as x86-64 System V in CompCert `x86/Conventions1.v`) must permit caller-saved register clobbers (`%rax, %rcx, %rdx, %rsi, %rdi, %r8–%r11`), dead flag bits, and uninitialized stack padding without allowing rogue codecs to spoof return values or shunt queries. Requiring (i) shared ground observation-spine preservation (`decodeOut o₂ = some o₁ → obsTgt o₂ = obsSrc o₁`), (ii) a Cartesian query-frame bijection `(decodeQuery, frameOf) : Q_tgt ≃ Q_src × Frame`, and (iii) callee-saved ABI preservation (`%rbx, %rbp, %r12–%r15`) is proved linearly independent by an executable finite-state probe: dropping any single law admits a buggy implementation that still satisfies the simulation diagram.
4. **Universal Properties Pin Internal Specifications Up to Canonical Isomorphism.** Final coalgebras ($\nu F$) uniquely characterize coinductive I/O trace semantics (`CompCert` `program_behavior`, `CCR` `Tr.t`), Galois adjunctions ($c_! \dashv c^*$) uniquely determine optimal cross-language abstractions once one adjoint is fixed, Reynolds–Wadler relational parametricity yields structural pass laws directly from polymorphic types, and the categorical diagonal product lifts 1-safety refinement to 2-safety hyperproperties (`CompCert-CT`).
5. **Content-Addressed Toolchain Binding and Capability Preservation Ledgers Close the Deployment Gap.** Verified proofs mean nothing if build flags invert semantics (`CakeML --skip_type_inference=true`, `--perf_callgraph=true`; Rust `dev` vs. `release` overflow checks), if incremental caches rely on `mtime` or omit binary/environment inputs (`rust-lang/cargo` `src/compiler/fingerprint/mod.rs`), or if downstream unverified optimizers legally break security hyperproperties (e.g., Dead-Store Elimination removing secret zeroization while preserving 1-safety I/O trace refinement). Closing the deployment gap requires content-addressed digests (`NixOS/nix` `DerivationOutput`, `in-toto/attestation` `Statement/v1`) paired with an explicit **Capability Preservation Ledger** tracking which 1-safety vs. 2-safety properties survive every downstream lowering step.

## Applicability

This report synthesizes primary-source Coq/HOL4/C++/Rust inspections, peer-reviewed verification theory, and a self-contained finite-state Python micro-probe across nine durable upstream subjects pinned in `REPORT.json`:

- **Verified Compilers & Open-Module Refinement (`AbsInt/CompCert`, `CertiKOS/compcert@compcerto`, `CakeML/cakeml`, `CCR-project/ccr`, `DimSum`, `AliveToolkit/alive2`):** Examined comparatively to trace how vertical pass composition and horizontal linking eliminate intermediate IRs, calling conventions, and ghost state from the final trusted specification. Source-level symbol citations apply specifically to the pinned revisions (`2685140b...`, `87a62d95...`, `2874b664...`, `edcda8fa...`, `3bdd4f5e...`). DimSum was examined via its POPL 2023 publication (`10.1145/3571220`), Zenodo artifact (`10.5281/zenodo.7306313`), and documented GitLab module layout (`dimsum/module.v`, `dimsum/trefines.v`, `dimsum_examples/rec_to_asm.v`) rather than direct raw file checkout (noted under **Boundaries**).
- **Build Fingerprinting, Content-Addressed Derivations, and Provenance Attestation (`rust-lang/cargo`, `NixOS/nix`, `in-toto/attestation`):** Examined at pinned commits (`e3535167...`, `69653925...`, `50bf0171...`) to document concrete soundness limits of timestamp-based build caching, differences between input-addressed and content-addressed derivations, and digest-only attestation semantics.
- **Executable Micro-Probe:** Run directly in Python 3 over an exhaustive 32-state ABI model (`4 arg0 × 2 rcx × 2 rbx × 2 stack_pad`) and a 4-secret dead-store-elimination crypto model; the standalone script and verbatim outputs are preserved under **Evidence**.

The codec laws, telescopic/horizontal cancellation criteria, universal-property characterizations, and capability-preservation distinctions apply broadly to verified compilers, binary lifters, FFI verification frameworks, and safety- or security-critical Rust/C/ML build pipelines.

## Findings

### 1. Telescopic Vertical IR Erasure and the Serializer/Assembler Boundary

Basis: source + normative + documentation

A multi-stage compiler or verifier typically lowers a source program through $n$ intermediate languages:
$$L_{\text{src}} \xrightarrow{T_1} L_1 \xrightarrow{T_2} \dots \xrightarrow{T_n} L_n \xrightarrow{T_{\text{emit}}} L_{\text{ISA}}.$$
If every pass $T_i$ establishes a composable behavioral refinement $L_i \sqsupseteq L_{i+1}$ (transitivity of simulation over a shared observable event alphabet), the chain telescopes directly into $L_{\text{src}} \sqsupseteq L_{\text{ISA}}$. Crucially, **none of the intermediate language definitions $L_1, \dots, L_n$ or per-pass invariant relations appear in the final endpoint theorem statement**. Even a subtle bug in an intermediate IR semantics $L_k$ cannot break end-to-end soundness: if pass $T_k$ relies on a broken $L_k$ assumption, pass $T_{k+1}$ will fail to simulate $L_k$ into $L_{k+1}$ (unless the endpoint semantics $L_{\text{src}}$ or $L_{\text{ISA}}$ itself is defective).

#### Concrete Architecture Comparison Across Verified Compilers and Validators

| System & Pinned Revision | Observable Endpoint Contract | Intermediate Stages Erased | Residual Unverified Boundary |
| --- | --- | --- | --- |
| **CompCert** (`AbsInt/CompCert@2685140b...`) | 4-way `program_behavior` (`Terminates t r`, `Diverges t`, `Reacts T`, `Goes_wrong t`) with `behavior_improves` (`common/Behaviors.v:41–45, 81–82`) and `backward_simulation (Csem.semantics p) (Asm.semantics tp)` (`driver/Compiler.v:446–452`) | 20+ passes (`CompCert's_passes`, `Compiler.v:231–253`): `SimplExpr`, `SimplLocals`, `Cshmgen`, `Cminorgen`, `Selection`, `RTLgen`, `Tailcall`, `Inlining`, `Renumber`, `Constprop`, `CSE`, `Deadcode`, `Unusedglob`, `Allocation`, `Tunneling`, `Linearize`, `CleanupLabels`, `Debugvar`, `Stacking`, `Asmgen` | OCaml extraction, C preprocessor/parser/elaborator, `PrintAsm.print_program` (`x86/TargetPrinter.ml`, `driver/Driver.ml:71`), external assembler (`driver/Driver.ml:93`), and system linker (`driver/Driver.ml:351–353`). |
| **Stack-Aware CompCert / CompCertELF** (Wang et al., *POPL 2019*, DOI `10.1145/3290375`) | Concrete finite-stack machine code / ELF relocatable objects with compositional linking | Same CompCert pipeline plus abstract-stack-to-concrete-stack & ELF assembly/linking passes | Eliminates CompCert's infinite-stack assumption and external assembler/linker TCB for supported architectures. |
| **CakeML** (`CakeML/cakeml@2874b664...`) | `behaviour = Diverge (io_event llist) \| Terminate outcome (io_event list) \| Fail` over `ffi_state` oracle (`semantics/ffi/ffiScript.sml:47–102`), verified down to raw machine `word8 list` (`compiler/backend/backendScript.sml:34–78`) | 12 backend IR passes (`backendScript.sml:44–77`): `source_to_source`, `source_to_flat`, `flat_to_clos`, `clos_to_bvl`, `bvl_to_bvi`, `bvi_to_data`, `data_to_word`, `word_to_stack`, `stack_to_lab`, `lab_to_target` (verified GC + verified machine byte encoder) | HOL4 kernel + hardware ISA specification (`x64`/`arm8`/`riscv`/`mips`/`arm7`/`ag32`) + thin C startup/FFI harness; explicitly excludes CLI escape flags (`--skip_type_inference=true`, `--perf_callgraph=true`, `compiler/compilerScript.sml:69–72, 103–104`). |
| **Alive2** (`AliveToolkit/alive2@3bdd4f5e...`) | Per-function LLVM IR refinement (`tools/transform.cpp:506–511`): `∀I. (∀N. src_nonpoison(I,N) ∧ retval_src(I,N)==retval_src(I,0)) → (∀N. retval_tgt(I,N)==retval_tgt(I,0) ...)` plus memory & UB refinement | Validates individual LLVM optimization passes (`tv/tv.cpp:231–235`) without verifying the pass implementation itself | Unverified `llvm2alive` frontend translation, bounded loop unrolling, Z3 SMT solver, and lack of verified linking down to machine assembly (LLVM `SelectionDAG`/`GlobalISel`/MC remain unverified). |

#### Notable Primary-Source Details

- **CompCert's Two-Phase Simulation Pipeline (`AbsInt/CompCert/driver/Compiler.v:353–432`):** CompCert first composes 21 forward simulations from `Cstrategy` to `Asm` (`compose_forward_simulations`), flips that composite forward simulation into a backward simulation via `forward_to_backward_simulation` (requiring `atomic_receptive` on `Cstrategy` and `Asm.semantics_determinate`), and finally composes backward with `Cstrategy.strategy_simulation` to obtain `backward_simulation (Csem.semantics p) (Asm.semantics tp)`. Notice also lines 102–103 & 176–188: OCaml debugging printers (`print_RTL`, `print_LTL`) are proved no-ops in Coq *assuming* the extracted OCaml function returns `unit` without corrupting memory (`print_identity`).
- **CompCert Separate Compilation (`Compiler.v:466–481`):** `separate_transf_c_program_correct` uses `TransfLink` typeclasses so per-unit compilation commutes with syntactic `link_list`, yet still restricts linking to CompCert-compiled C units sharing identical syntax/memory conventions—motivating open-module frameworks (`CompCertO`, `DimSum`, `CCR`).
- **CakeML's `trace_oracle_def` (`semantics/ffi/ffiScript.sml:107–115`):** CakeML explicitly demonstrates duality between oracle-based FFI semantics (`ffi_state`) and trace-based behavioral semantics by constructing `trace_oracle` that replays a coinductive `io_event llist` and returns `Oracle_final FFI_failed` on any event mismatch.

---

### 2. Horizontal FFI & Ghost-State Cancellation (`CompCertO`, `DimSum`, `CCR`)

Basis: source + normative + documentation

Real systems link heterogeneous modules across FFI boundaries (e.g., Rust calling C, C calling hand-written assembly, or verified cryptographic kernels calling unverified OS syscalls). Monolithic whole-program refinement breaks when modules are verified separately in different languages or program logics. Three complementary Coq frameworks show how to make horizontal linking erase internal FFI contracts and separation-logic ghost state from the closed-system TCB:

#### 1. CompCertO: Language Interfaces and Calling-Convention Algebra (`CertiKOS/compcert@87a62d95...`; Koenig & Shao, *PLDI 2021*, DOI `10.1145/3453483.3454097`)

In `common/LanguageInterface.v` (lines 11–167), every open module has an incoming and outgoing `language_interface` defining its boundary `query : Type`, `reply : Type`, and `entry : query -> val`:
- Closed whole programs instantiate `li_null` (`Empty_set` outgoing, lines 25–30) and `li_wp` (`query := unit`, `reply := Integers.int` incoming, lines 37–42).
- C-like open modules use `li_c` (`c_query := { cq_vf, cq_sg, cq_args, cq_mem }`, `c_reply := { cr_retval, cr_mem }`, lines 117–136).
- Cross-language ABI and memory-injection translations are first-class **simulation conventions** `Record callconv {li1 li2}` (`LanguageInterface.v:48–64`) containing `ccworld`, `match_senv`, `match_query`, and `match_reply`, forming a category with identity `cc_id` (`1`, lines 73–83) and associative composition `cc_compose` (`@`, lines 87–111), plus a preorder algebra `ccref` / `cceqv` (`common/CallconvAlgebra.v:31–233`).
- Composing passes horizontally and vertically simplifies composite calling conventions algebraically (`cc1 @ cc2 ≡ cc_abi`) until closing the program with `li_null`/`li_wp` eliminates all intermediate Kripke worlds and CKLRs (`cc_c`).

#### 2. DimSum: Decentralized Multi-Language Semantics (Sammler et al., *POPL 2023*, DOI `10.1145/3571220`, artifact `10.5281/zenodo.7306313`)

Instead of embedding every language into a single shared "mother language" or universal memory model (which bloats the TCB with every language's features), DimSum models each module as an independent event-emitting labeled transition system (`mod_trans` in `dimsum/module.v`) communicating solely via explicit external events (`Incoming`/`Outgoing` calls, returns, and I/O).
- Refinement is defined directly on decentralized trace sets (`trefines` in `dimsum/trefines.v`), supporting both vertical transitivity and horizontal linking (`link_trans`).
- Cross-language FFI adapters (such as `rec_to_asm` in `dimsum_examples/rec_to_asm.v`, connecting a high-level recursive language `Rec` with structured heap to low-level register/memory assembly `Asm`) are ordinary **wrapper transformers** on transition systems.
- When two linked modules speak across a verified FFI adapter (e.g., `Rec` compiled to `Asm` linked with hand-written `Asm`), the wrapper invariants and language-local heap/stack abstractions **cancel out at the closed system boundary**, leaving only the external I/O event trace.

#### 3. Conditional Contextual Refinement (CCR) & the Assumption Cancellation Theorem (`CCR-project/ccr@edcda8fa...`; Song et al., *POPL 2023*, DOI `10.1145/3571232`)

CCR unifies separation-logic Hoare triples (via Iris-style Partial Commutative Monoids `URA.t` in `spc/PCM.v`) directly inside contextual refinement over Interaction-Tree Executable Module Semantics (`ems/`):

- **Coinductive Traces with Dual `ub`/`nb` (`ems/Behavior.v:11–18, 54–55`):**
  ```coq
  CoInductive t : Type :=
    | done (retv : Any.t)
    | spin
    | ub    (* demonic failure: refined by anything *)
    | nb    (* angelic magic / impossible assumption: refines anything *)
    | cons (hd : event) (tl : t).
  Definition improves (src tgt : t) : Prop := tgt <1= src.
  ```
- **Conditional Wrappers (`spc/HoareDef.v`):** Every module `SMod` is wrapped with `HoareFun` (assuming its precondition + ghost resources on entry and guaranteeing postcondition + updated ghost resources on return) and `HoareCall` (guaranteeing callee preconditions and assuming callee postconditions). Under `refines2` (`ems/ModSem.v`), conditional refinements compose both vertically (`refines2_PreOrder`) and horizontally (`refines2_add`).
- **Assumption Cancellation Theorem (`spc/Hoare.v:95–106, 164–175`, `adequacy_type_arg_stb` / `adequacy_type_arg`):** Once all modules in a program are linked together, provided the entry `main` precondition holds with well-formed initial PCM resources (`URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk)`) and `main`'s postcondition implies `ret_src = ret_tgt`, **every internal `fspec` (`precond`/`postcond`), every ghost resource (`iProp` / `URA.t`), and every intermediate abstraction layer cancels out completely**, yielding raw closed-program trace inclusion:
  ```coq
  Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt0)) <1=
  Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  ```
- **Explicit Axiom Footprint (`CCR-project/ccr/README.md:179–199`):** CCR documents its exact classical/extensionality Coq axiom set (`relational_choice`, `dependent_unique_choice`, `prop_extensionality`, `proof_irrelevance`, `functional_extensionality_dep`, `eq_rect_eq`, `constructive_definite_description`, `classic`, `bisimulation_is_eq`, plus CompCert's syscall axiom)—demonstrating good TCB hygiene by making foundational axioms transparent alongside canceled module specifications.

---

### 3. Observable-Spine Codecs and Cartesian `FrameFiberCodec` Contracts

Basis: derived + execution + source

When lifting a closed-program theorem or refining an open function across an ABI boundary (e.g., source function `f(arg0) -> (ret, io)` lowered to x86-64 assembly taking registers + stack + heap), requiring strict state equality ($Q_{\text{tgt}} = Q_{\text{src}}$, $O_{\text{tgt}} = O_{\text{src}}$) is **impossible** for real optimizing compilers.

Inspecting CompCert's x86-64 ABI definition (`AbsInt/CompCert@2685140b...`, `x86/Conventions1.v`, lines 30–70 and 138–145) makes the concrete target slack explicit:
- On 64-bit System V ELF (`Archi.ptr64 = true`, `Archi.win64 = false`), integer caller-saved registers are `AX, CX, DX, SI, DI, R8, R9, R10, R11` (`destroyed_at_call`), all 16 `X0–X15` floating-point registers are caller-saved, return values reside in `AX` or `X0` (`loc_result_64`), and callee-saved registers are strictly `BX, BP, R12, R13, R14, R15` (`int_callee_save_regs`, line 61).
- Hardware assembly also freely mutates dead `RFLAGS` condition bits, uninitialized stack-frame padding slots, and microarchitectural TSO store-buffer draining order between fences.

Conversely, allowing an **arbitrary** untrusted codec `(decodeQuery : Q_tgt → Q_src, decodeOut : O_tgt → Option O_src)` in a refinement theorem destroys soundness completely:
- A **rogue constant or affine-offset output codec** (`decodeOut(o2) = OutSrc((o2.rax - 1) mod 4, o2.io)`) makes a buggy compiler returning `(x + 2)` pass simulation against a specification returning `(x + 1)`;
- A **rogue query-shunting codec** (`decodeQuery(qt) = if qt.rcx == 1 then 0 else qt.rdi`) hides bugs on arbitrary target call contexts by mapping broken target inputs onto an easy source input;
- A **frame-blind codec** accepts assembly that clobbers callee-saved `%rbx` or caller stack frames, corrupting callers upon return.

#### The Observable-Spine + Cartesian `FrameFiberCodec` Contract

Let `SemObs` be a minimal ground observation spine shared identically between source and target (containing exact return value bits, terminal/divergent/reactive status, and external I/O or security-leakage event traces), equipped with trusted projections `obsSrc : O_src → SemObs` and `obsTgt : O_tgt → SemObs`. A boundary codec `(decodeQuery, frameOf, encodeQuery, decodeOut, encodeOut)` between `(Q_src, O_src)` and `(Q_tgt, O_tgt)` over ABI frame type `Frame` (partitioned into caller-saved slack and callee-saved invariant fields `calleeOf : Frame → CalleeState`) must satisfy three laws:

```text
Law 1 (Cartesian Frame-Fiber Bijection):
  (decodeQuery, frameOf) : Q_tgt ≃ Q_src × Frame
  i.e., ∀ qt,       encodeQuery (decodeQuery qt) (frameOf qt) = qt
        ∀ qs fr,    decodeQuery (encodeQuery qs fr) = qs
                 ∧  frameOf     (encodeQuery qs fr) = fr

Law 2 (Observable-Spine Preservation & Round-Trip):
  ∀ o2 o1,  decodeOut o2 = some o1  ==>  obsTgt o2 = obsSrc o1
  ∀ o1,     decodeOut (encodeOut o1) = some o1

Law 3 (Callee-Saved ABI Frame Preservation Across All Fibers):
  ∀ qt o2,  StepTgt(qt, o2)  ==>  calleeOf(frameOf_out o2) = calleeOf(frameOf qt)
```

Notice what this contract **permits** and what it **blocks**:
- **Permitted target slack:** Any mutation to caller-saved scratch registers (`%rcx`, `%rdx`, `%r8–%r11`), dead flags, and dead stack padding lives in the non-callee-saved component of `Frame`; neither `obsTgt` nor `calleeOf` constrains their output values, so optimizing register allocators and schedulers pass freely.
- **Blocked spoofing:** Law 1 guarantees every concrete target query state `(rdi, rcx, rbx, pad)` maps injectively and surjectively onto a unique `(Q_src, Frame)` fiber (preventing query shunting or omitting inconvenient register contexts); Law 2 locks every decoded output to the exact ground `SemObs` bytes (preventing constant, offset, or permuting output codecs); Law 3 prevents silent caller corruption across FFI/function returns.

#### Empirical Linear Independence of the Three Laws (Micro-Probe Part 1)

Basis: execution

Exhaustive evaluation across all $4 \times 2 \times 2 \times 2 = 32$ concrete target states in **Evidence** demonstrates that **every single law is independently necessary**—each adversarial variant passes raw simulation (`sim=True`) and passes two of the three laws while failing solely the law engineered to reject it:

| Configuration | Raw `sim` (`dec_o(tgt(qt)) == src(dec_q(qt))`) | Law 1 (`bij`) | Law 2 (`spine`) | Law 3 (`callee_rbx`) | Overall (`ALL`) |
| --- | --- | --- | --- | --- | --- |
| `C_good_abi` (clobbers `%rcx` & stack pad, preserves `%rbx`) | `True` | `True` | `True` | `True` | **`True`** |
| `C_rogue_offset_spoof` (buggy `x+2` masked by `rax - 1` codec) | `True` | `True` | **`False`** | `True` | **`False`** |
| `C_rogue_query_shunt` (buggy `rcx==1` masked by shunting to `arg0=0`) | `True` | **`False`** | `True` | `True` | **`False`** |
| `C_clobber_callee_rbx` (buggy code flips callee-saved `%rbx`) | `True` | `True` | `True` | **`False`** | **`False`** |

---

### 4. Universal Properties, Galois Connections, Coalgebras, and Parametricity

Basis: normative + derived

When an internal specification *must* be stated (for example, the trace domain of a new language, the abstract domain of a static analyzer, or the preservation law of a polymorphic transformation), **universal properties** eliminate arbitrary human encoding choices by characterizing the mathematical object **uniquely up to canonical isomorphism**:

1. **Final Coalgebras for Observable Trace Semantics (Rutten, *TCS 2000*, DOI `10.1016/S0304-3975(00)00056-6`):**
   An execution semantics emitting external events $E$ and terminal outcomes $R$ is an $F$-coalgebra $(S, \gamma : S \to F(S))$ for the behavior functor $F(X) = R + (E \times X) + \{\tau \cdot X\} + \{\bot\}$. The **final coalgebra** $(\nu F, \zeta)$ (whose elements are finite and infinite event traces, directly analogous to CompCert's `program_behavior` and CCR's `Tr.t`) satisfies the universal property that for *every* coalgebra $(S, \gamma)$ there exists a **unique** coalgebra homomorphism $\mathsf{beh}_\gamma : S \to \nu F$ satisfying $\zeta \circ \mathsf{beh}_\gamma = F(\mathsf{beh}_\gamma) \circ \gamma$. Two states are bisimilar if and only if they have the same image under $\mathsf{beh}_\gamma$, pinning trace equivalence canonically without ad-hoc step-counting indices.
2. **Galois Connections & Adjunctions for Sound Abstraction and Cross-Language Simulation (Cousot & Cousot, *POPL 1977*, DOI `10.1145/512950.512973`):**
   Given posets/preorders $(C, \le_C)$ (concrete semantics) and $(A, \le_A)$ (abstract semantics), a Galois connection $\alpha \dashv \gamma$ satisfies $\forall c\;a,\; \alpha(c) \le_A a \iff c \le_C \gamma(a)$. By uniqueness of adjoints, fixing the concretization map $\gamma$ **uniquely determines** the strongest abstraction $\alpha(c) = \bigwedge \{a \mid c \le_C \gamma(a)\}$ and the **best abstract transformer** $f^\sharp = \alpha \circ f \circ \gamma$. In cross-language simulation, adjoint lifts/projections ($c_! \dashv c^*$) similarly eliminate manual guesswork when translating preconditions vs. postconditions across an ABI representation change.
3. **Reynolds–Wadler Relational Parametricity ("Free Theorems"; Reynolds, *IFIP 1983*; Wadler, *FPCA 1989*, DOI `10.1145/99370.99404`):**
   For any parametrically polymorphic function $f : \forall \alpha.\; F(\alpha) \to G(\alpha)$ (such as a generic CFG reordering pass, register-renaming functor, or layout-polymorphic serializer/deserializer), relational parametricity guarantees that $f$ commutes with *every* binary relation $R \subseteq A \times B$: $(x, y) \in F(R) \implies (f_A(x), f_B(y)) \in G(R)$. Specializing $R$ to the graph of a function $h : A \to B$ gives naturality $G(h) \circ f_A = f_B \circ F(h)$ for free—constraining structural compiler passes and generic container/slice operations without trusting handwritten behavioral axioms.
4. **Categorical Diagonal Product for $k$-Safety Hyperproperties (Clarkson & Schneider, *JCS 2010*, DOI `10.3233/JCS-2009-0393`; Barthe et al., *POPL 2020*, DOI `10.1145/3371075`):**
   Standard trace refinement ($\mathsf{Beh}(P_{\text{tgt}}) \subseteq \mathsf{Beh}(P_{\text{src}})$) preserves all **1-safety / trace properties** (properties of individual executions) and strictly narrows demonic nondeterminism, **but does not preserve 2-safety hyperproperties** (relations across *pairs* of executions with different secrets, such as constant-time leakage non-interference, deterministic reproducibility, or residual-memory secret erasure). Lifting semantics via the diagonal product $\Delta(S) = S \times S$ over coupled low-equivalent inputs (`CompCert-CT`, *POPL 2020*) makes relational leakage refinement a first-class composable preservation theorem.

---

### 5. End-to-End Content-Addressed System Binding & Capability Preservation Ledger

Basis: source + normative + execution

Even a flawless machine-checked proof of `Beh(Asm) ⊆ Beh(Src)` fails in production if the artifact deployed on silicon differs from the artifact verified—either because CLI flags altered semantics, incremental caching reused a stale build, an unverified assembler/linker mutated emitted bytes, or an unverified downstream pass destroyed a security property outside the 1-safety I/O trace.

#### Concrete Binding Failure Surfaces Observed in Production Toolchains

1. **Semantic-Inverting CLI Flags & Build Profiles:**
   - **`CakeML/cakeml@2874b664...` (`compiler/compilerScript.sml:69–72, 103–104`):** Even a fully verified compiler exposes operational flags that disable verification guarantees—explicitly documenting `--skip_type_inference=true` (*"There are no guarantees of safety if the type inferencer is skipped"*) and `--perf_callgraph=true` (*"unverified: emit C-stack shadowing..."*). Any verification certificate must therefore hash the exact parsed `compiler$config` / CLI flag vector and reject unverified flags.
   - **Rust/Cargo Build Profiles (`dev` vs. `release`):** Compiling a crate under `cargo test` (`dev` profile: `overflow-checks = true`, `debug-assertions = true`, `opt-level = 0`) vs. `cargo build --release` (`overflow-checks = false`, `debug-assertions = false`, `opt-level = 3`, optional `lto = "fat"`, `panic = "abort"`) changes integer overflow from panic to two's-complement wrapping and alters `cfg!(debug_assertions)` control flow. Verifying MIR extracted under `dev` does **not** certify a `release` binary unless the exact profile, `target-cpu`, `target-feature`, and `RUSTFLAGS` are cryptographically bound.
2. **Timestamp-Based & Partial Incremental Cache Fingerprinting (`rust-lang/cargo@e3535167...`):**
   - `src/compiler/fingerprint/mod.rs` (lines 21–48, 67–115, 637–686) provides a candid primary-source inventory of Cargo's incremental cache limits:
     - Default freshness relies on **filesystem `mtime` comparison** plus non-cryptographic `u64` hashes (`Fingerprint.{rustc, target, profile, path, config, compile_kind}`), explicitly warning: *"Filesystem mtime tracking is notoriously imprecise and problematic. Only a small part of the environment is captured."*
     - Content-hash freshness (`checksum_freshness`, line 1591) requires unstable nightly `-Z checksum-freshness` + `-Z checksum-hash-algorithm`.
     - Binary dependencies are excluded from `Fingerprint` (`[^1]`, line 94); `RUSTFLAGS` and extra args are conditionally excluded from `Metadata::unit_id` when `--remap-path-prefix` is present (`[^7]`, lines 109–110); and undeclared host files or environment variables read by `build.rs` or proc-macros bypass invalidation unless explicitly reported via `cargo::rerun-if-*`.
3. **Input-Addressed vs. Content-Addressed Derivations and Digest Attestations:**
   - **`NixOS/nix@69653925...` (`src/libstore/include/nix/store/derivations.hh:44–95`):** Explicitly separates `DerivationOutput::InputAddressed` (store path derived solely from the build graph inputs—allowing bit-different rebuilds under non-determinism to share a logical derivation identity), `ContentAddressed` (`CAFixed` / `CAFloating`, binding the store path directly to the cryptographic hash of output bytes), and `Impure` (un-sandboxed).
   - **`in-toto/attestation@50bf0171...` (`spec/v1/statement.md:9–57`):** Binds immutable software artifacts in `Statement/v1` strictly via cryptographic `subject[].digest` maps (`sha256`/`sha512`) to a `predicateType` URI and `predicate` payload—while explicitly noting (lines 54–56) that *"Subject artifacts are matched purely by digest, regardless of content type"*, meaning verification policies must bind *both* artifact digests and semantic metadata (`predicateType` + verified profile/target schema) to prevent cross-context confusion.
4. **The Correctness–Security Gap & Capability Preservation Ledger:**
   - D'Silva, Payer, & Song (*IEEE S&P Workshops 2015*, DOI `10.1109/SPW.2015.33`) and Simon, Chisnall, & Anderson (*EuroS&P 2018*, DOI `10.1109/EuroSP.2018.00009`) demonstrated that standard optimizing compilers legally erase security-critical operations—most notoriously **Dead-Store Elimination (DSE)** removing `memset(secret_buf, 0, n)` right before function return, or branch-folding turning constant-time bitmasks into secret-dependent conditional jumps.
   - **Micro-Probe Part 2 (`Basis: execution`)** confirms this formally: deleting `buf = 0` at the end of `src_crypto(secret, msg)` **preserves 1-safety I/O trace refinement identically** (`Beh_IO(tgt_dse) == Beh_IO(src)` is `True`), yet flips residual-stack secret independence from `True` (`{0}`) to `False` (`{0, 1, 2, 3}`).
   - Therefore, any end-to-end verification certificate crossing unverified lowering tools (`LLVM -O3`, `as`, `ld`, or post-link binary rewriters like `BOLT` or CPU errata linker veneers) must maintain an explicit **Capability Preservation Ledger**:

| Property / Security Capability | Preserved by 1-Safety Observational Refinement (`Beh(tgt) ⊆ Beh(src)`)? | Survives Unverified Optimizing Compiler (`-O3`) / Assembler / Linker? | Required End-to-End Binding Mechanism |
| --- | --- | --- | --- |
| **Memory safety / UB freedom / Functional I/O** | **Yes** (provided source is UB-free and codec satisfies Laws 1–3) | Only if compiler & emitter are verified (`CompCert`+`CompCertELF`, `CakeML`) or binary is translation-validated | Digest-pinned source + profile + target layout + verified binary emission (or post-link binary verification) |
| **Integer overflow / panic trapping semantics** | **Yes** (if profile matches verified semantics) | **No** if `dev` vs. `release` (`-C overflow-checks`) drifts between verification and deployment | Content-addressed binding of exact `rustc` version, `Profile`, `RUSTFLAGS`, and target triple |
| **Secret zeroization (`memset` / stack scrubbing)** | **No** (dead stores before return are invisible in standard I/O traces) | **No** (DSE legally deletes non-volatile dead stores) | Volatile/explicit-barrier semantics (`explicit_bzero`) + post-codegen/binary stack-liveness verification |
| **Constant-time execution (PC + memory-address non-interference)** | **No** (2-safety hyperproperty; broken by secret-dependent branch introduction or `cmov` lowering) | **No** (`LLVM` selection/if-conversion and assembler branch-padding errata can reintroduce secret branches) | Leakage-preserving compiler (`CompCert-CT`, `Jasmin`) or binary-level relational analysis over final ELF bytes |
| **Cryptographic entropy / randomness preservation** | **No** (demonic trace refinement legally narrows `getrandom` to a constant key!) | **No** unless I/O oracle models external syscall non-malleability | Externalized syscall trace event (`IO_event "getrandom"`) locked inside `SemObs` spine |

## Boundaries

- **Direct Raw Checkout of DimSum Coq Files (`not examined`):** Because outbound HTTP access from the analysis environment was restricted to GitHub domains, `gitlab.mpi-sws.org/iris/dimsum` source files were not downloaded directly; DimSum claims rely on the peer-reviewed POPL 2023 publication (`10.1145/3571220`), its immutable Zenodo artifact record (`10.5281/zenodo.7306313`), and indexed module metadata (`dimsum/module.v`, `dimsum/trefines.v`, `dimsum_examples/rec_to_asm.v`). Exact line numbers within DimSum's `.v` files were therefore not examined.
- **Concurrent / Weak-Memory Horizontal Linking Across Heterogeneous ISAs (`not examined`):** CompCertO (`CertiKOS/compcert@87a62d95...`) and CCR (`CCR-project/ccr@edcda8fa...`) target sequential (single-threaded) open modules; extending horizontal assumption cancellation and `FrameFiberCodec` to multi-threaded C11/ARMv9-A/x86-TSO weak-memory FFI boundaries was not examined here.
- **Liveness and Fair Scheduling Under Observational Refinement (`known not to apply`):** Standard trace-inclusion refinement (`Beh(tgt) ⊆ Beh(src)`) preserves safety and silent-divergence refinement, and rules out spurious crashes, but can trivially refine a nondeterministic program with both terminating and diverging traces into a purely diverging one unless fairness or total-termination side conditions are explicitly enforced. Similarly, demonic trace refinement is known not to preserve probabilistic or cryptographic entropy unless randomness is modeled as an external observable FFI/syscall oracle rather than internal demonic choice.
- **Reproducible Binary Bit-Identity Under Cargo Default Builds (`unsupported`):** As documented in `rust-lang/cargo@e3535167...` (`src/compiler/fingerprint/mod.rs:21–48`), Cargo's default stable build pipeline does not provide full hermetic sandboxing or cryptographic input-content hashing; guaranteeing bit-reproducible artifact binding requires external hermetic build orchestration (such as `Nix` content-addressed derivations or sandboxed Bazel/in-toto pipelines) plus explicit path remapping (`--remap-path-prefix` / `trim-paths`).
- **Automated Checking of Arbitrary Unverified Linker Scripts and Dynamic Loaders (`unknown`):** While `CakeML` and `CompCertELF` close the static assembler/object-emission gap, full end-to-end verification of dynamic ELF loading (`ld-linux.so`), PLT/GOT lazy binding, `LD_PRELOAD` interposition, and post-link binary optimizers remains outside the examined verified compiler proofs.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)

- `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`:
  - `common/Behaviors.v` (lines 41–45, 81–82, 124–147): `program_behavior` (`Terminates`, `Diverges`, `Reacts`, `Goes_wrong`), `behavior_improves`, `state_behaves`, `program_behaves`.
  - `common/Smallstep.v` (lines 566–573, 1050–1065, 1289–1296, 1566, 1863–1890): `fsim_properties`, `receptive`, `determinate`, `bsim_properties`, `compose_backward_simulation`, `forward_to_backward_simulation`.
  - `driver/Compiler.v` (lines 102–103, 120–188, 231–260, 353–481): `CompCert's_passes`, `print_identity`, `cstrategy_semantic_preservation`, `c_semantic_preservation`, `transf_c_program_correct`, `separate_transf_c_program_correct`.
  - `driver/Driver.ml` (lines 60, 71, 93, 351–353): Boundary from Coq-verified `Compiler.transf_c_program` to unverified OCaml `PrintAsm.print_program`, external `assemble`, and system linker.
  - `x86/Conventions1.v` (lines 30–70, 127–145): `is_callee_save`, `int_caller_save_regs`, `int_callee_save_regs`, `float_caller_save_regs`, `destroyed_at_call`, `loc_result_64`.
- `CertiKOS/compcert` (`refs/heads/compcerto`) @ `87a62d95cd24a44e3ecd5fefddc70a969a881bcb`:
  - `common/LanguageInterface.v` (lines 11–173): `language_interface`, `li_null`, `li_wp`, `callconv`, `cc_id` (`1`), `cc_compose` (`@`), `li_c`, `cc_c`.
  - `common/CallconvAlgebra.v` (lines 31–68, 163–233): `ccref`, `cceqv`, monoid laws (`cc_compose_id_left`, `cc_compose_id_right`, `cc_compose_assoc`), and monotonicity instances.
- `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`:
  - `semantics/ffi/ffiScript.sml` (lines 15–115): `ffi_outcome`, `io_event`, `ffi_state`, `call_FFI_def`, `behaviour` (`Diverge`, `Terminate`, `Fail`), `trace_oracle_def`.
  - `compiler/compilerScript.sml` (lines 69–72, 103–104, 193–226, 242–250): CLI option warnings (`--skip_type_inference=B`, `--perf_callgraph=B`), `compile_def`, `parse_top_config_def`.
  - `compiler/backend/backendScript.sml` (lines 34–78, 173–188): 12-stage backend pipeline ending in `lab_to_target$compile` emitting raw `bytes:word8 list` + bitmaps directly.
- `CCR-project/ccr` @ `edcda8faae6580581e8e5b28050d755bcb29f55f`:
  - `README.md` (lines 98–199): Paper-to-Coq theorem mapping and complete Coq axiom inventory.
  - `ems/Behavior.v` (lines 11–18, 54–55, 185): Coinductive `Tr.t` (`done`, `spin`, `ub`, `nb`, `cons`), `Beh.improves`, `Beh.of_program`.
  - `spc/Hoare.v` (lines 95–106, 131–141, 164–175): Assumption Cancellation Theorems `adequacy_type_arg_stb`, `adequacy_type_stb`, `adequacy_type_arg`.
- `AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`:
  - `tv/tv.cpp` (lines 177–250): Per-function pass validation harness `TVLegacyPass::runOn`.
  - `tools/transform.cpp` (lines 506–511, 637–645): SMT refinement encoding for poison and `undef`.
- `rust-lang/cargo` @ `e35351676760e4c90ccad19aaf85cec75e1af8b3`:
  - `src/compiler/fingerprint/mod.rs` (lines 21–48, 67–115, 637–686, 1591): `mtime`-based freshness caveats, `Fingerprint` vs. `Metadata::unit_id` comparison matrix (including bin-dep omission `[^1]` and `--remap-path-prefix` exclusion `[^7]`), `pub struct Fingerprint`, unstable `checksum_freshness`.
- `NixOS/nix` @ `6965392507e19998de706aa15e514f81e9b7ce11`:
  - `src/libstore/include/nix/store/derivations.hh` (lines 44–95): `DerivationOutput::{InputAddressed, ContentAddressed, Impure}` variant model.
- `in-toto/attestation` @ `50bf01716982189898823e90586075f37cd9bb7d`:
  - `spec/v1/statement.md` (lines 9–57): `Statement/v1` schema (`_type`, `subject[].digest`, `predicateType`, `predicate`) and content-type-agnostic digest matching note.

### Peer-Reviewed Literature

- Leroy, *"A Formally Verified Compiler Back-end"*, JAR 2009, DOI `10.1007/s10817-009-9155-4`.
- Kumar, Myreen, Norrish, Owens, *"CakeML: A Verified Implementation of ML"*, POPL 2014, DOI `10.1145/2535838.2535841`.
- Tan, Myreen, Kumar, Fox, Owens, Norrish, *"The Verified CakeML Compiler Backend"*, JFP 2019, DOI `10.1017/S0956796818000229`.
- Abrahamsson, Myreen, Kumar, Sewell, *"Candle: A Verified Implementation of HOL Light"*, ITP 2022, DOI `10.4230/LIPIcs.ITP.2022.3`.
- Koenig & Shao, *"CompCertO: Compiling Certified Open C Components"*, PLDI 2021, DOI `10.1145/3453483.3454097`.
- Wang, Wilke, Shao, *"An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code"*, PACMPL (POPL 2019), DOI `10.1145/3290375`.
- Song, Cho, Kim, Kang, Hur, *"CompCertM: CompCert with C-Assembly Linking and Lightweight Modular Verification"*, PACMPL (POPL 2020), DOI `10.1145/3371091`.
- Sammler, Spies, Song, D'Osualdo, Krebbers, Garg, Dreyer, *"DimSum: A Decentralized Approach to Multi-Language Semantics and Verification"*, PACMPL (POPL 2023), DOI `10.1145/3571220`; artifact DOI `10.5281/zenodo.7306313`.
- Song, Cho, Lee, Hur, Sammler, Dreyer, *"Conditional Contextual Refinement"*, PACMPL Vol. 7 (POPL 2023), Article 39, DOI `10.1145/3571232`.
- Cousot & Cousot, *"Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints"*, POPL 1977, DOI `10.1145/512950.512973`.
- Reynolds, *"Types, Abstraction and Parametric Polymorphism"*, Information Processing 83 (IFIP 1983), pp. 513–523.
- Wadler, *"Theorems for Free!"*, FPCA 1989, DOI `10.1145/99370.99404`.
- Rutten, *"Universal Coalgebra: A Theory of Systems"*, Theoretical Computer Science 249(1), 2000, DOI `10.1016/S0304-3975(00)00056-6`.
- Clarkson & Schneider, *"Hyperproperties"*, Journal of Computer Security 18(6), 2010, DOI `10.3233/JCS-2009-0393`.
- Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, *"Formal Verification of a Constant-Time Preserving C Compiler"*, PACMPL (POPL 2020), DOI `10.1145/3371075`.
- D'Silva, Payer, Song, *"The Correctness-Security Gap in Compiler Optimization"*, IEEE S&P Workshops (LangSec 2015), DOI `10.1109/SPW.2015.33`.
- Simon, Chisnall, Anderson, *"What You Get is What You C: Controlling Side Effects in Mainstream C Compilers"*, IEEE EuroS&P 2018, DOI `10.1109/EuroSP.2018.00009`.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-19`)

Save the following standalone Python 3.10+ script as `/tmp/probe_codecs_refinement.py` and run `python3 /tmp/probe_codecs_refinement.py`:

```python
#!/usr/bin/env python3
from dataclasses import dataclass
from typing import Tuple

@dataclass(frozen=True)
class QSrc:
    arg0: int

@dataclass(frozen=True)
class Frame:
    rcx_caller: int
    rbx_callee: int
    stack_pad: int

@dataclass(frozen=True)
class QTgt:
    rdi_arg0: int
    rcx_caller: int
    rbx_callee: int
    stack_pad: int

@dataclass(frozen=True)
class OutSrc:
    ret: int
    io: Tuple[int, ...]

@dataclass(frozen=True)
class OutTgt:
    rax_ret: int
    rcx_caller: int
    rbx_callee: int
    stack_pad: int
    io: Tuple[int, ...]

def obs_src(o: OutSrc): return (o.ret, o.io)
def obs_tgt(o: OutTgt): return (o.rax_ret, o.io)
def run_src(q: QSrc): return OutSrc(ret=(q.arg0 + 1) % 4, io=(q.arg0,))
def run_tgt_good(q: QTgt): return OutTgt((q.rdi_arg0 + 1) % 4, q.rcx_caller ^ 1, q.rbx_callee, q.stack_pad ^ 1, (q.rdi_arg0,))
def run_tgt_shifted(q: QTgt): return OutTgt((q.rdi_arg0 + 2) % 4, q.rcx_caller ^ 1, q.rbx_callee, q.stack_pad ^ 1, (q.rdi_arg0,))
def run_tgt_shunted(q: QTgt):
    ret = 1 if q.rcx_caller == 1 else (q.rdi_arg0 + 1) % 4
    io = (0,) if q.rcx_caller == 1 else (q.rdi_arg0,)
    return OutTgt(ret, q.rcx_caller ^ 1, q.rbx_callee, q.stack_pad ^ 1, io)
def run_tgt_clobber_callee(q: QTgt): return OutTgt((q.rdi_arg0 + 1) % 4, q.rcx_caller ^ 1, q.rbx_callee ^ 1, q.stack_pad ^ 1, (q.rdi_arg0,))

all_qsrc = [QSrc(a) for a in range(4)]
all_frames = [Frame(c, b, p) for c in range(2) for b in range(2) for p in range(2)]
all_qtgt = [QTgt(a, c, b, p) for a in range(4) for c in range(2) for b in range(2) for p in range(2)]

def check_codec(name, tgt_fn, dec_q, frame_of, enc_q, dec_o):
    rt_tgt = all(enc_q(dec_q(qt), frame_of(qt)) == qt for qt in all_qtgt)
    rt_prod = all(dec_q(enc_q(qs, fr)) == qs and frame_of(enc_q(qs, fr)) == fr for qs in all_qsrc for fr in all_frames)
    bij_ok = rt_tgt and rt_prod
    spine_ok = callee_ok = sim_ok = True
    for qt in all_qtgt:
        ot = tgt_fn(qt)
        os_dec = dec_o(ot)
        if obs_tgt(ot) != obs_src(os_dec): spine_ok = False
        if ot.rbx_callee != frame_of(qt).rbx_callee: callee_ok = False
        if os_dec != run_src(dec_q(qt)): sim_ok = False
    print(f"  {name:26s}: sim={str(sim_ok):5s} | bij={str(bij_ok):5s} | spine={str(spine_ok):5s} | callee_rbx={str(callee_ok):5s} | ALL={sim_ok and bij_ok and spine_ok and callee_ok}")

print("[PART 1] Observable-Spine & Cartesian FrameFiberCodec Law Audit (32 Q_tgt states):")
id_dec_q = lambda qt: QSrc(qt.rdi_arg0)
id_frame = lambda qt: Frame(qt.rcx_caller, qt.rbx_callee, qt.stack_pad)
id_enc_q = lambda qs, fr: QTgt(qs.arg0, fr.rcx_caller, fr.rbx_callee, fr.stack_pad)
id_dec_o = lambda ot: OutSrc(ot.rax_ret, ot.io)

check_codec("C_good_abi", run_tgt_good, id_dec_q, id_frame, id_enc_q, id_dec_o)
check_codec("C_rogue_offset_spoof", run_tgt_shifted, id_dec_q, id_frame, id_enc_q, lambda ot: OutSrc((ot.rax_ret - 1) % 4, ot.io))
check_codec("C_rogue_query_shunt", run_tgt_shunted, lambda qt: QSrc(0 if qt.rcx_caller == 1 else qt.rdi_arg0), id_frame, id_enc_q, id_dec_o)
check_codec("C_clobber_callee_rbx", run_tgt_clobber_callee, id_dec_q, id_frame, id_enc_q, id_dec_o)

def src_crypto(secret: int, msg: int):
    buf = secret; mac = (buf ^ msg) & 1; buf = 0
    return {"io": (mac,), "residual_stack_byte": buf}

def tgt_dse_crypto(secret: int, msg: int):
    buf = secret; mac = (buf ^ msg) & 1
    return {"io": (mac,), "residual_stack_byte": buf}

print("\n[PART 2] 1-Safety I/O Trace Refinement vs Dead-Store Elimination (DSE) Capability Loss:")
print("  1-safety I/O trace refinement holds (Beh_IO(tgt_dse) == Beh_IO(src)):",
      all(tgt_dse_crypto(s, m)["io"] == src_crypto(s, m)["io"] for s in range(4) for m in range(2)))
print("  Residual-stack secret independence holds in src:",
      len({src_crypto(s, 0)["residual_stack_byte"] for s in range(4)}) == 1,
      f"(distinct values: {sorted({src_crypto(s, 0)['residual_stack_byte'] for s in range(4)})})")
print("  Residual-stack secret independence holds in tgt_dse:",
      len({tgt_dse_crypto(s, 0)["residual_stack_byte"] for s in range(4)}) == 1,
      f"(distinct values: {sorted({tgt_dse_crypto(s, 0)['residual_stack_byte'] for s in range(4)})})")
```

Observed output (`python3 /tmp/probe_codecs_refinement.py`, exit code `0`):

```text
[PART 1] Observable-Spine & Cartesian FrameFiberCodec Law Audit (32 Q_tgt states):
  C_good_abi                : sim=True  | bij=True  | spine=True  | callee_rbx=True  | ALL=True
  C_rogue_offset_spoof      : sim=True  | bij=True  | spine=False | callee_rbx=True  | ALL=False
  C_rogue_query_shunt       : sim=True  | bij=False | spine=True  | callee_rbx=True  | ALL=False
  C_clobber_callee_rbx      : sim=True  | bij=True  | spine=True  | callee_rbx=False | ALL=False

[PART 2] 1-Safety I/O Trace Refinement vs Dead-Store Elimination (DSE) Capability Loss:
  1-safety I/O trace refinement holds (Beh_IO(tgt_dse) == Beh_IO(src)): True
  Residual-stack secret independence holds in src: True (distinct values: [0])
  Residual-stack secret independence holds in tgt_dse: False (distinct values: [0, 1, 2, 3])
```

## Revalidation

1. **Re-run the Codec & DSE Capability Micro-Probe (Seconds):** Execute `python3 /tmp/probe_codecs_refinement.py` from **Evidence**; confirm exit code `0` and identical linear independence across `bij`, `spine`, and `callee_rbx`, plus `1-safety=True / residual_stack_independence=False` under DSE.
2. **Check Downstream Compiler & Build-System TCB Shifts:**
   - Diff `AbsInt/CompCert` `driver/Driver.ml` and `driver/Compiler.v` against `2685140bf72c959446981fb99b5e44a8975021bc` to see whether verified binary emission (`CompCertELF` / `AsmToJSON` / verified assembler) has been upstreamed into mainline CompCert.
   - Diff `rust-lang/cargo` `src/compiler/fingerprint/mod.rs` against `e35351676760e4c90ccad19aaf85cec75e1af8b3` to check whether `-Z checksum-freshness` or `trim-paths` has stabilized, eliminating `mtime`-based cache staleness or `--remap-path-prefix` metadata exclusions.
   - Diff `CakeML/cakeml` `compiler/compilerScript.sml` against `2874b664e10939a3ee462215b2e068c89c1f70eb` for any newly added unverified CLI flags alongside `--skip_type_inference` and `--perf_callgraph`.
3. **Audit Any Candidate End-to-End Verification Theorem:** Check four narrow artifacts directly: (a) that no intermediate IRs, FFI wrappers, or ghost PCM state appear in the top-level closed-program theorem statement, (b) that any target boundary codec proves Cartesian fiber bijection, `SemObs` spine preservation, and callee-saved preservation, (c) that the build provenance binds exact cryptographic digests of transitive sources, compiler version, build profile (`overflow-checks`, `opt-level`, `panic`), target layout, and output binary, and (d) that a Capability Preservation Ledger explicitly documents any 2-safety security properties crossing unverified optimizers or linkers.
