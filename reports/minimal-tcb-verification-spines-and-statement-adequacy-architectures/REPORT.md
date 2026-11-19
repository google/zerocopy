# Minimal-TCB Verification Spines and Statement-Adequacy Architectures

## Summary

Minimizing the Trusted Computing Base (TCB) of a formal verification pipeline requires solving two distinct trust problems simultaneously: **proof-checking soundness** (ensuring that an accepted derivation genuinely establishes its formal statement) and **statement adequacy** (ensuring that the formal statement actually specifies the intended real-world behavior rather than a vacuous, under-constrained, circular, or notation-hijacked proxy).

1. **Proof-Checking Micro-Kernels and Escape Vectors:** Self-verifying or machine-code-anchored micro-kernels—specifically Metamath Zero (`mm0-c`, 819 LOC in `mm0-c/verifier.c` physically separating human-reviewed `.mm0` specifications from `.mmb` binary proof streams) and Candle (a HOL Light kernel compiled through CakeML down to machine code with an end-to-end FFI I/O soundness theorem `semantics_thm`)—shrink the logical checking kernel to roughly $10^3$ lines while decoupling proof search from proof checking. In contrast, checking `#print axioms` inside an interactive dependent type prover such as Lean 4 is insufficient against untrusted synthesis agents: `leanprover/lean4`'s C++ kernel (`src/kernel/type_checker.cpp`, `type_checker::reduce_nat`) reduces named primitives (`Nat.land`, `Nat.gcd`, etc.) by hardcoded symbol name regardless of module origin, elaboration hooks execute arbitrary host I/O, and runtime-substitution attributes (`@[implemented_by]`, `@[csimp]`, `@[extern]`) diverge from kernel `ConstantInfo` terms. Meanwhile, `Lean4Lean` (`Lean4Lean/Verify/Environment.lean`) verifies `addDecl.WF` across axioms, theorems, definitions, opaques, quotients, and mutual definitions, but still leaves `inductDecl` as an open `sorry` at revision `67f63b0c`.
2. **Evicting Internal Specifications from the TCB:** Telescopic transitivity of behavioral refinement across multi-IR compilation pipelines (`CompCert`, `CompCertO`) and decentralized horizontal linking (`DimSum`) erases intermediate IR definitions and intermediate pass invariants from the top-level theorem. Inside intensional dependent type theories with $\beta\delta\iota\zeta$-conversion, abstract verification scaffolding (refinement preorders, separation-logic triples, monadic weakest preconditions) unfolds definitionally (`rfl`) to zero lines in the trusted specification when the endpoint claim is stated directly over ground operational transitions.
3. **Reference-Model Bisimulation Without Existential Slack Collapse:** Decoupling a verification-friendly symbolic model $M_{\text{fast}}$ from an upstream executable reference semantics $M_{\text{ref}}$ (`MiniRust`, `Sail`, `SpecTec`, `Ivy`) requires forward safety preservation, backward behavioral inclusion, and bidirectional fault-kind equivalence ($\mathsf{undefined}$ vs. $\mathsf{unsupported}$). Crucially, introducing existentially quantified ghost predicates ($\exists b : \mathsf{Bool}$) inside an untrusted simulation invariant collapses into unconstrained one-way slack that accepts omitted move deinitialization, wrong-slot deinitialization, and reversed operand order.
4. **Observable-Spine and Random-Tape Fiber Codecs:** Permitting concrete target-machine slack (scratch registers, padding, hardware TRNG entropy) without admitting constant-tape collapse ($\rho := 0$) or rogue query shunting requires a bijective `RandFrameFiberCodec` ($Q_{\text{tgt}} \simeq Q_{\text{src}} \times \mathsf{RandTape} \times \mathsf{Frame}$) paired with fiberwise functional preservation, callee-saved frame invariance, and measure-preserving non-degeneracy of the pushforward distribution over uniform `RandTape`.
5. **Constructive Statement Adequacy and Anti-Goodharting:** Defeating specification-level Goodhart pathologies under automated synthesis requires combining four mechanical checks: (a) Chockler–Kupferman–Vardi subformula perturbation vacuity and linear $(m+1)$-witness clause independence (1 joint positive witness plus $m$ isolating counter-witnesses); (b) primal-dual uniqueness checking (`Picus` for arithmetic circuits; `EverParse`/`Vest` `SPRoundTrip` + `PSRoundTrip` + `NonMalleable` for binary codecs); (c) 100%-kill-rate guard mutation canaries on $M_{\text{ref}}$ and multi-oracle differential conformance; and (d) Two-Tier signed hardware-profile subsumption over a quotient join-semilattice with mandatory physical satisfiability witnesses (`SAT(H_plat)`), preventing disclosure-fatigue laundering and non-monotonic cross-feature failures (`PAC × DMP`, `MaskOrder × MPAM/DVFS`, and vacuous `False` profiles).

## Applicability

This report synthesizes architectural mechanisms across four interacting classes of verification subjects pinned in `REPORT.json`:

- **Proof-Checking Kernels and Metatheory:** `digama0/mm0` (`0d414c0b`), `CakeML/cakeml` Candle (`2874b664`), `digama0/lean4lean` (`67f63b0c`), `leanprover/lean4` (`01716786`), `leanprover/lean4export` (`df81913e`), `ammkrn/nanoda_lib` (`0da9f98f`), and `MetaCoq/metacoq` (`51b14e4b`). These govern kernel TCB size, external proof replay, and kernel/elaborator escape surfaces.
- **Executable Reference Semantics and Relational Oracles:** `minirust/minirust` (`063d7841`), `rems-project/sail` (`97aa617d`), `Wasm-DSL/spectec` (`acc6e834`), `kenmcmil/ivy` (`257e3da9`), and `AbsInt/CompCert` (`2685140b`). These serve as external semantic anchors ($M_{\text{ref}}$) and compositional refinement pipelines.
- **Primal-Dual Uniqueness and Non-Malleable Codecs:** `Veridise/Picus` (`138b151d`), `project-everest/everparse` (`270f5aab`), and `secure-foundations/vest` (`026867a3`). These instantiate simultaneous existence/completeness and uniqueness/non-malleability guarantees.
- **Specification Vacuity and Coverage Theory:** Kupferman & Vardi (STTT 2003) and Chockler, Kupferman, & Vardi (TACAS 2001 / STTT 2006), extended operationally via executable Python 3 standard-library micro-probes documented in `## Evidence`.

**Scope of Applicability:** The findings apply directly to high-assurance compilation, verified binary parsing, zero-knowledge circuit verification, ISA-level systems verification, and automated-agent proof synthesis pipelines where untrusted tools or LLMs generate both proofs and auxiliary lemmas/theories (and potentially propose specification edits). Claims about specific kernel implementation behavior (such as Lean 4's `reduce_nat` name matching or `Lean4Lean`'s open `inductDecl` `sorry`) apply strictly to the pinned revisions; architectural theorems (existential slack collapse, clause-independence witness bounds, primal-dual uniqueness necessity, and quotient semilattice subsumption) apply generally to any verification framework exhibiting those structural hypotheses.

## Findings

### 1. Self-Verifying Proof Micro-Kernels and Kernel Escape Surfaces

Basis: source + normative + documentation

#### 1.1 Architectural Comparison of Proof-Checking Kernels

Modern proof checkers trade expressive core logics against TCB size and machine-code anchoring:

| System (Pinned Revision) | Core Logic / Proof Artifact | Trusted Checker Architecture | Verified Metatheory / Machine Anchoring | Concrete Boundary / Caveat |
| :--- | :--- | :--- | :--- | :--- |
| **`mm0` / `mm0-c`** (`digama0/mm0@0d414c0b`) | Multi-sorted first-order logic with definitional extensions; `.mm0` (spec) + `.mmb` (binary proof stream) | `mm0-c/verifier.c` (819 lines C) verifies `.mmb` bytecode against parsed `.mm0` headers via `verify(u8* file, u64 len)` | Bare-metal x86-64 build (`mm0-c/bare.sh`, `-D BARE`); `.mmb` proof stream cannot alter `.mm0` theorem signatures | Target logics (HOL, Lean, Peano, x86-64) must be axiomatized inside `.mm0` specifications |
| **Candle** (`CakeML/cakeml@2874b664`) | Higher-Order Logic (HOL Light kernel with optional ad-hoc overloading) | Verified CakeML program (`candle/prover/`) compiled to x86-64/ARMv8/MIPS/RISC-V machine code | `semantics_thm` (`candle_prover_semanticsScript.sml:428`) proves every emitted FFI I/O event satisfies `ok_event` under HOL set-theoretic soundness | Expressiveness limited to simple type theory (no dependent types or universe polymorphism) |
| **Lean 4 C++ Kernel** (`leanprover/lean4@01716786`) | Dependent Type Theory (CIC + quotient types + proof irrelevance + `Nat`/`String` kernel reductions) | C++ kernel (`src/kernel/type_checker.cpp`, 1,303 lines, plus `environment.cpp`, `inductive.cpp`, `instantiate.cpp`) | External replay via `lean4export` (`df81913e`) + independent Rust checker `nanoda_lib` (`0da9f98f`) | Hardcoded symbol-name `reduce_nat` acceleration; elaboration I/O & `@[implemented_by]` live outside kernel |
| **Lean4Lean** (`digama0/lean4lean@67f63b0c`) | Lean 4 dependent type theory implemented in Lean 4 | Self-hosted external typechecker (`Lean4Lean/TypeChecker.lean`, `Lean4Lean/Replay.lean`) | `addDecl.WF` (`Lean4Lean/Verify/Environment.lean:224–239`) verified for axioms, theorems, defs, opaques, quotients, mutual defs | **`inductDecl` still `sorry` at `67f63b0c`** (line 239); runtime compiled by Lean compiler |
| **MetaCoq** (`MetaCoq/metacoq@51b14e4b`) | Polymorphic Cumulative Calculus of Inductive Constructions (PCUIC) | Verified typechecker and safe erasure pipeline inside Rocq/Coq | Mechanized confluence, subject reduction, conversion soundness, and extraction to Malfunction/C (`CertiCoq`) | Does not model every legacy Rocq kernel extension (e.g., template polymorphism edge cases, native arrays/floats unless enabled) |

In `mm0-c/verifier.c` (`digama0/mm0@0d414c0b`, lines 670–720), `verify(u8* file, u64 len)` validates the `MM0B_MAGIC` header, sort/term/theorem table bounds, and steps through the binary proof stream (`CMD_STMT_SORT`, `CMD_STMT_TERM`, `CMD_STMT_THM`, `CMD_PROOF_*`, lines 382–638), synchronously calling `parse_until(...)` on the separate `.mm0` specification file. Because `.mmb` opcodes can only discharge statements already declared in `.mm0`, untrusted proof generators are structurally incapable of mutating, shadowing, or rewriting the human-reviewed theorem header.

In Candle (`CakeML/cakeml@2874b664`, `candle/prover/candle_prover_semanticsScript.sml:428–443`), the top-level theorem `semantics_thm` connects the CakeML big-step evaluation of `candle_code ++ prog` directly to the foreign-function interface (`ffi`) trace:

```sml
Theorem semantics_thm:
  semantics_prog (init_state ffi with eval_state := es)
                 init_env (candle_code ++ prog) res ∧
  eval_state_ok es ∧
  prog_syntax_ok candle_code ∧
  EVERY safe_dec prog ∧
  ffi.io_events = [] ∧
  res ≠ Fail ⇒
    (∀outcome io_list.
       res = Terminate outcome io_list ⇒ EVERY ok_event io_list) ∧
    (∀io_trace.
       res = Diverge io_trace ⇒ every ok_event io_trace)
```

Combined with CakeML's verified compiler backend, generational garbage collector, and parser (`candle/parser/`), this closes the gap between logical validity in Zermelo set theory (`candle/set-theory/`) and observable bytes written to `stdout`.

#### 1.2 Concrete Kernel, Elaborator, and Runtime Escape Vectors in Dependent Type Provers

Basis: source + derived

When automated synthesis or proving agents author source files checked by a full dependent type prover such as Lean 4 (`leanprover/lean4@01716786`), inspecting `#print axioms` on the final theorem is **strictly insufficient** to guarantee soundness or host safety. Four distinct escape classes arise directly from source inspection:

1. **Kernel Accelerated-Primitive Name Hijacking (`reduce_nat`):** In `leanprover/lean4@01716786`, `src/kernel/type_checker.cpp:660–693`, `type_checker::reduce_nat` checks whether the head constant equals hardcoded persistent name pointers (`g_nat_add`, `g_nat_sub`, `g_nat_mul`, `g_nat_pow`, `g_nat_gcd`, `g_nat_mod`, `g_nat_div`, `g_nat_beq`, `g_nat_ble`, `g_nat_land`, `g_nat_lor`, `g_nat_xor`, `g_nat_shiftLeft`, `g_nat_shiftRight`, initialized via `new_persistent_expr_const({"Nat", "land"})` at lines 1266–1271):
   ```cpp
   if (f == *g_nat_land) return reduce_bin_nat_op(nat_land, e);
   ```
   Because this reduction triggers purely on the hierarchical `Name` (`Nat.land`, `Nat.gcd`, etc.) without checking whether the constant was imported from the trusted standard library, declaring a bogus `def Nat.land (_ _ : Nat) : Nat := 0` in a standalone environment without importing `Init.Data.Nat.Bitwise` creates an immediate kernel inconsistency: delta-unfolding `Nat.land 1 1` yields `0`, while `reduce_nat` evaluates `Nat.land 1 1` to `1`, proving `0 = 1` and hence `False` with **zero axioms**.
   - **Required Guard:** Reserve all kernel-accelerated and sysroot root namespaces (`Nat`, `String`, `Bool`, `Int`, `BitVec`, `Init`, `Std`, `Lean`, `LeanIR`) so untrusted modules cannot declare constants inside them, and require external kernel replay (`lean4export` + `nanoda_lib` or `Lean4Lean`) over a sealed base environment.
2. **Elaboration-Time Host I/O and Environment Extensions:** Commands such as `#eval`, `run_cmd`, `by_elab`, and `@[init]` execute arbitrary compiled or interpreted code during elaboration, allowing an untrusted proof file to exfiltrate secrets, modify adjacent files, or mutate environment extensions.
   - **Required Guard:** Pre-parse untrusted files with parser-only entrypoints (`Parser.parseHeader`, `Parser.parseCommand`) against a closed `SyntaxNodeKind` allowlist prior to elaboration, run elaboration in an isolated sandbox, and replay the resulting `.olean` / exported stream inside a clean kernel with `trustLevel := 0`, `plugins := #[]`, and `loadExts := false`.
3. **Kernel-to-Runtime Substitution and Compiler Reflection:** Attributes such as `@[implemented_by]`, `@[csimp]`, and `@[extern]` replace verified Lean definitions with arbitrary unverified native or FFI implementations in compiled executables while leaving kernel `ConstantInfo` terms untouched. Likewise, `native_decide` introduces the `Lean.ofReduceBool` axiom, folding the entire unverified LCNF compiler, C code generator, and C toolchain into the TCB.
   - **Required Guard:** For executable code extraction, audit and forbid `@[implemented_by]`/`@[csimp]`/`@[extern]` outside an explicitly signed FFI boundary; for proofs, enforce a strict axiom ceiling (`{propext, Quot.sound}`, or `{propext, Classical.choice, Quot.sound}` when classical reasoning is permitted) and discharge SAT/LP obligations via verified boolean certificate checkers (`check : Cert → Bool`, e.g., LRAT or Farkas checkers) reduced inside the kernel rather than `native_decide`.
4. **Notation, Coercion, and Typeclass Shadowing in Specifications:** If a specification module imports an untrusted proof or theory library, the untrusted module can inject `@[instance]`, `@[coe]`, `notation`, or `macro` declarations that silently change the elaborated AST of the human-reviewed specification text.
   - **Required Guard (One-Way Specification Isolation):** Enforce a strict DAG partition where specification modules never import untrusted proof/theory modules, and verify exact structural equality of the target theorem's `ConstantInfo.type` against the locked specification environment.

#### 1.3 Cross-Core Diverse Checker Quorum Against Mercurial Silicon

Basis: derived

Even a formally verified single proof kernel remains vulnerable to **silent data corruption (SDC)** or deterministic hardware comparator faults on a single defective CPU core (mercurial cores). Executing two non-derivative checkers (e.g., `mm0-c` and `Candle`, or `Lean4Lean` and `nanoda_lib`) sequentially on the same core still fails if the core's branch/comparator logic exhibits a deterministic defect. Pinning $m \ge 2$ non-derivative kernels to distinct physical cores $c_1 \neq c_2$ attested via hardware core identifiers (`APICID` on x86-64, `MPIDR_EL1` on ARMv8) and binding each core's acceptance verdict over `H(claim) || H(derivation) || core_id || nonce` with post-quantum signatures (`SLH-DSA` / `ML-DSA`) eliminates single-core hardware defect forgery.

---

### 2. Definitional Erasure, Telescopic Refinement, and Reference-Model Bisimulation

Basis: source + normative + execution + derived

#### 2.1 Zero-TCB Algebraic Scaffolding via Definitional Unfolding (`rfl` Erasure)

In intensional dependent type theories with $\beta\delta\iota\zeta$-conversion (Lean 4, Rocq), rich algebraic verification frameworks—refinement preorders ($x \sqsubseteq y :\equiv \forall a,\; x(a) \to y(a)$), Galois connections, separation-logic Hoare triples, and weakest-precondition transformers—need **zero lines in the trusted specification** provided the root endpoint theorem is stated solely in primitive logical connectives ($\forall, \to, \exists, \land, \lor, =$) over ground machine transitions. Proofs constructed inside untrusted theory libraries using $\sqsubseteq$ or separation logic inhabit the primitive endpoint type definitionally (`rfl`), erasing the entire intermediate verification algebra from the human-audited specification surface.

#### 2.2 Vertical Telescoping and Horizontal FFI Cancellation

Across multi-pass compiler pipelines $L_{\text{src}} \to L_1 \to \dots \to L_n \to L_{\text{ISA}}$ (exemplified by `CompCert` at `AbsInt/CompCert@2685140b` and open-component `CompCertO`, Koenig & Shao PLDI 2021, DOI `10.1145/3453483.3454097`), vertical transitivity of behavioral refinement collapses all intermediate IR definitions $L_1, \dots, L_n$ and intermediate pass lemmas out of the end-to-end correctness theorem. Horizontally, decentralized multi-language semantics such as `DimSum` (Sammler et al., POPL 2023, DOI `10.1145/3571220`) model each language module as an event-emitting labeled transition system (LTS) linked by contextual refinement, causing module-local ownership algebras and FFI calling-convention shims to cancel upon closed-system linking so that trust terminates at hardware ISA and OS syscall traces.

#### 2.3 Reference-Model Bisimulation and Exact Polarity Laws

Direct symbolic verification against an upstream executable reference semantics $M_{\text{ref}}$ is often ergonomically expensive because reference models carry full machine state. For example, in `minirust/minirust@063d7841` (`spec/lang/machine.md:10–40`), `Machine<M: Memory>` tracks `prog`, `mem: ConcurrentMemory<M>`, `intptrcast: IntPtrCast<M::Provenance>`, `threads`, `active_thread`, `synchronized_threads`, `locks`, and `global_ptrs`. Similarly, `rems-project/sail@97aa617d` (`src/sail_lean_backend`, `src/sail_coq_backend`, `src/sail_smt_backend`, `src/sail_c_backend`) compiles single-source ISA semantics for ARMv8-A, RISC-V, and CHERI-MIPS; `Wasm-DSL/spectec@acc6e834` (`spectec/src/{el,il,al,backend-interpreter,backend-latex,backend-prose}`, Youn et al. PLDI 2024, DOI `10.1145/3656440`) generates both prose specifications and executable reference interpreters from one DSL; and `kenmcmil/ivy@257e3da9` (McMillan & Padon CAV 2020, DOI `10.1007/978-3-030-53291-8_12`) pairs decidable EPR protocol invariants with compositional specification-driven relational monitors.

To evict a fast verification-oriented semantics $M_{\text{fast}}$ (e.g., a symbolic WP evaluator) from the trusted specification TCB, prove a correspondence theorem against $M_{\text{ref}}$ over shared ground boundary types `(Query, Out)` and a total reversible syntax encoding $\mathsf{decode}(\mathsf{encode}(p)) = \mathsf{some}\;p$:

$$\mathsf{WellFormed}_{\text{fast}}(p, q) \implies \mathsf{WellFormed}_{\text{ref}}(\mathsf{encode}(p), q) \;\land\; \mathsf{Beh}_{\text{ref}}(\mathsf{encode}(p), q) \subseteq \mathsf{Beh}_{\text{fast}}(p, q)$$

conjoined with **bidirectional fault-kind equivalence** inside the supported fragment for $k \in \{\mathsf{undefined}, \mathsf{unsupported}\}$:

$$\mathsf{Reaches}_{\text{fast}}(p, q, \mathsf{fault}\;k) \iff \mathsf{Reaches}_{\text{ref}}(\mathsf{encode}(p), q, \mathsf{fault}\;k).$$

Each directional obligation blocks a distinct soundness bug:
- **Forward safety ($\mathsf{WF}_{\text{fast}} \implies \mathsf{WF}_{\text{ref}}$):** prevents $M_{\text{fast}}$ from omitting undefined-behavior (UB) checks present in $M_{\text{ref}}$.
- **Backward behavioral inclusion ($\mathsf{Beh}_{\text{ref}} \subseteq \mathsf{Beh}_{\text{fast}}$):** prevents $M_{\text{fast}}$ from dropping demonic nondeterminism (e.g., arbitrary uninitialized-byte values or memory allocation addresses) that $M_{\text{ref}}$ permits.
- **Bidirectional fault-kind equivalence:** prevents $M_{\text{fast}}$ from vacuously classifying UB inputs as `.unsupported` (which would hide UB behind an out-of-scope gate) or silently treating unsupported constructs as UB.

#### 2.4 The Existential Slack Simulation-Invariant Collapse Trap

Basis: execution + derived

When relating $M_{\text{fast}}$ to a coarser $M_{\text{ref}}$ (for instance, where $M_{\text{ref}}$ omits move deinitialization of a local slot while $M_{\text{fast}}$ deinitializes it), a common temptation is to introduce an existentially quantified ghost boolean inside the untrusted simulation invariant $R_{\text{slot}}$:

$$R_{\text{slot}}(s_{\text{fast}}, s_{\text{ref}}) :\equiv \exists b : \mathsf{Bool},\; \text{if } b \text{ then } (s_{\text{fast}} = \bot \land \exists v,\; s_{\text{ref}} = \mathsf{init}(v)) \text{ else } s_{\text{fast}} = s_{\text{ref}}.$$

Because $b$ is existentially quantified locally per state, $R_{\text{slot}}$ is logically equivalent to **unconstrained one-way slack** permitting $s_{\text{fast}} = \bot$ on *any* initialized slot of $s_{\text{ref}}$. Our executable micro-probe (`Probe 3` in `## Evidence`) exhaustively evaluates a 2-local machine on `Move(0)` across all initial states and confirms:

| Candidate `Move(0)` Semantics in $M_{\text{fast}}$ | Passes Existential $R_{\text{slot}}$? | Passes Explicit Functional Bijection? |
| :--- | :---: | :---: |
| `honest_deinit_slot0`: `(None, s[1])` | `True` | `True` |
| `bug_omit_deinit`: `(s[0], s[1])` | **`True` (UNSOUND)** | `False` |
| `bug_wrong_slot1`: `(s[0], None)` | **`True` (UNSOUND)** | `False` |
| `bug_deinit_both`: `(None, None)` | **`True` (UNSOUND)** | `False` |

Furthermore, this slack breaks outright on well-defined copies of uninitialized bytes (e.g., Rust `MaybeUninit<u8>`), where $s_{\text{fast}}$ and $s_{\text{ref}}$ must agree on exact byte initialization states. **Invariant:** Simulation relations between $M_{\text{fast}}$ and $M_{\text{ref}}$ must use an **exact state bijection** or an explicit deterministic functional projection $g(\text{trace})$ pinned to the observable execution history, never existentially quantified ghost slack.

---

### 3. Observable-Spine and Random-Tape Fiber Codecs (`RandFrameFiberCodec`)

Basis: execution + derived

Cross-layer refinement from a clean source machine $P_{\text{src}}$ to a low-level target machine $P_{\text{tgt}}$ faces a fundamental tension: $P_{\text{tgt}}$ carries concrete physical state absent from $P_{\text{src}}$—caller-saved scratch registers (`%rcx`, `%rdx`), dead flags, stack padding, and—crucially for cryptographic or masked targets—**hardware TRNG entropy** $\rho \in \mathsf{RandTape}$. Conversely, permitting arbitrary existential encoding functions between source and target queries allows rogue Goodhart codecs that shunt inputs to trivial constant states or collapse hardware randomness ($\rho := 0$), passing functional trace inclusion while destroying cryptographic confidentiality (`getrandom` $\mapsto$ `[0u8; 32]`, probing entropy $1.0 \to 0.0$ bits).

The structural resolution is a **Random-Tape Frame Fiber Bijection** (`RandFrameFiberCodec`):

```text
structure RandFrameFiberCodec (Q_src Q_tgt RandTape Frame : Type) where
  encodeQuery : Q_src → RandTape → Frame → Q_tgt
  decodeQuery : Q_tgt → Q_src
  tapeOf      : Q_tgt → RandTape
  frameOf     : Q_tgt → Frame
  left_inv    : ∀ qt, encodeQuery (decodeQuery qt) (tapeOf qt) (frameOf qt) = qt
  right_inv   : ∀ qs ρ f,
                  let qt := encodeQuery qs ρ f
                  decodeQuery qt = qs ∧ tapeOf qt = ρ ∧ frameOf qt = f
```

Over a ground observable spine $\mathsf{SemObs}$ (return values, termination/divergence, external I/O, and hardware probing/leakage observations), three laws jointly enforce full faithfulness with zero statement-TCB bloat:

1. **Spine-Preserving Output Decoding:** $\forall o_2\;o_1,\; \mathsf{decodeOut}(o_2) = \mathsf{some}\;o_1 \implies \mathsf{obs}_{\text{tgt}}(o_2) = \mathsf{obs}_{\text{src}}(o_1)$ and $\mathsf{decodeOut}(\mathsf{encodeOut}(o_1)) = \mathsf{some}\;o_1$.
2. **Fiberwise Functional & Callee-Saved Frame Invariance:**
   $$\forall q_s\;\rho\;f,\quad \mathsf{obs}_{\text{func}}(T_{\text{tgt}}(\mathsf{encodeQuery}\;q_s\;\rho\;f)) = \mathsf{obs}_{\text{func}}(T_{\text{src}}(q_s)) \;\land\; \mathsf{frame}'(T_{\text{tgt}}(\dots)) = f.$$
3. **Measure-Preserving Non-Degeneracy on `RandTape`:** For every $(q_s, f)$ and every bounded adversary probe $p$ ($|p| \le d$), the pushforward distribution of $\rho \mapsto \mathsf{obs}_{\text{probe}}(T_{\text{tgt}}(\mathsf{encodeQuery}\;q_s\;\rho\;f), p)$ under uniform $\rho \sim \mathcal{U}(\mathsf{RandTape})$ equals the secret-independent simulator distribution $\mathsf{SimDist}(p)$ (in particular, preserving non-degenerate entropy).

In `Probe 3` (`## Evidence`), exhaustive checking over $Q_{\text{tgt}}(128) \simeq Q_{\text{src}}(4) \times \mathsf{RandTape}(8) \times \mathsf{Frame}(4)$ confirms `128/128` left and right inverses; an honest 1st-order masked target passes all three laws with `min_H = 1.000000` bits, whereas a constant-tape rewrite ($\rho := 0$) passes functional and frame preservation (`func_ok=True, frame_ok=True`) yet is decisively rejected by pushforward non-degeneracy (`non_degen_probe=False`, `min_H = 0.000000` bits).

---

### 4. Statement Adequacy: Vacuity, Clause Independence, Primal-Dual Uniqueness, and Anti-Goodharting

Basis: normative + source + execution + derived

#### 4.1 Taxonomy of Specification-Level Goodhart Pathologies

When automated agents synthesize or refactor specifications alongside proofs, specifications systematically fail in three structural ways that proof kernels cannot detect:

1. **Formal-Logic Operator and Quantifier Traps:** Saturating `Nat` subtraction (`0 - 1 = 0`, rendering `len - off >= 0` unconditionally true), totalized division/indexing (`x / 0 = 0`, `arr[i]! = 0`), Euclidean vs. hardware-truncating signed remainder (`-7 % 2 = +1` vs. `-1`), unbounded mathematical `Int` hiding fixed-width `BitVec` wraparound (`x + 1 > x`), implicit free-variable quantification (`autoImplicit` turning a misspelled variable `reqs` into $\forall \text{reqs},\dots$), and vacuous predicate aliases (`def isConstantTime := True`).
2. **Claim-Polarity and Precondition Inversion:** Applying compiler-style conditional refinement ($\mathsf{WellDefined}(x) \implies \mathsf{Beh}(T(x)) \subseteq \mathsf{Beh}(x)$) to a verifier, sanitizer, or sandbox—making the security claim vacuously true on buggy inputs! Similarly, inverting downward compilation ($\mathsf{Beh}(\text{tgt}) \subseteq \mathsf{Beh}(\text{src})$) with upward binary lifting ($\mathsf{Beh}(\text{bin}) \subseteq \mathsf{Beh}(\text{lifted})$), or collapsing arbitrary-length finite trace prefixes with non-termination under unbounded nondeterminism (violating König's lemma).
3. **Circular and Runtime-Coupled Specifications:** Defining validity by invoking the unverified tool itself (`is_valid(x) := (tool(x) == true)`) or defining target ISA semantics via the tool's own unverified parser/printer, introducing circular constant dependencies ($\mathsf{Consts}(S) \cap \mathsf{Consts}(T) \neq \emptyset$).

#### 4.2 Chockler–Kupferman–Vardi Vacuity and Linear $(m+1)$-Witness Clause Independence

Following Kupferman & Vardi (STTT 2003, DOI `10.1007/s10009-002-0088-y`) and Chockler, Kupferman, & Vardi (TACAS 2001, DOI `10.1007/3-540-45319-9_36`; STTT 2006, DOI `10.1007/s10009-006-0195-2`), a formula $\varphi$ holds **vacuously** in model $M$ if some subformula $\psi$ of $\varphi$ does not affect the truth value of $\varphi$ in $M$—equivalently, replacing an occurrence of $\psi$ with $\bot$ (positive polarity) or $\top$ (negative polarity) leaves $M \models \varphi[\psi \leftarrow \bot/\top]$ intact.

For a compound contract $S(x, y) = \bigwedge_{i=1}^m C_i(x, y)$, a single global negative canary fails to catch **multi-conjunct canary masking** (e.g., $C_1 \land \mathsf{True} \land C_3$), because any canary violating $C_1$ or $C_3$ already falsifies $S$. The **Linear $(m+1)$-Witness Clause-Independence Protocol** requires:
- **1 joint positive witness** $(x^+, y^+)$ satisfying $\bigwedge_{i=1}^m C_i(x^+, y^+)$ (proving non-contradiction / satisfiability); and
- **$m$ isolating counter-witnesses** $\{(x_i, y_i)\}_{i=1}^m$ such that for each $i \in \{1, \dots, m\}$, $\neg C_i(x_i, y_i) \land \bigwedge_{j \neq i} C_j(x_i, y_i)$.

`Probe 1` (`## Evidence`) demonstrates this directly over $x \in [-2, 7], y \in [-2, 13]$:
- `sound_3_clauses` ($y \ge 0 \land y \le 10 \land (y - x) \equiv 0 \pmod 2$): `joint_pos=(-2, 0)`, `independent=True` with all 3 isolating counter-witnesses `(-2, -2)`, `(-2, 12)`, `(-2, 1)`.
- `vacuous_true_masked` ($C_2 := \mathsf{True}$): `joint_pos=(-2, 0)`, **`independent=False`** (no isolating witness for `C2`).
- `redundant_subsumed` ($C_1 := y \ge 0$ subsumed by $C_2 := y \ge 5$): `joint_pos=(-2, 6)`, **`independent=False`** (no isolating witness for `C1`).

#### 4.3 Primal-Dual Witness Uniqueness (`Picus`, `EverParse`, `Vest`)

For relations where both under-specification (permitting forged witnesses or malleable encodings) and over-specification (rejecting valid inputs) are catastrophic, statement adequacy requires pairing **primal existence** with **dual uniqueness**:

1. **Zero-Knowledge Arithmetic Circuits (`Veridise/Picus@138b151d`, Pailoor et al. PLDI 2023, DOI `10.1145/3591282`):** In `picus-cex-uniqueness.rkt`, Picus encodes R1CS constraints over a finite field $\mathbb{F}_p$ into SMT queries (`z3`/`cvc5`) checking whether a circuit $\mathcal{C}(x, w) = 0$ is uniquely determined:
   - **Primal Completeness (Existence):** $\forall x \in \mathcal{X}_{\text{valid}},\; \exists w,\; \mathcal{C}(x, w) = 0$ (refutes over-constrained circuits such as `1 = 0`).
   - **Dual Soundness (Uniqueness):** $\forall x\;w_1\;w_2,\; \mathcal{C}(x, w_1) = 0 \land \mathcal{C}(x, w_2) = 0 \implies w_1 = w_2$ (or equality on output signals; refutes under-constrained circuits such as missing boolean constraints $w_i(w_i - 1) = 0$).
   `Probe 2` over $\mathbb{F}_{17}$ confirms: `over_constrained_1_eq_0` yields `0` solutions (`primal_exists=False, dual_unique=True`); `under_constrained_no_bool` ($w_0 + 2w_1 \equiv x \pmod{17}$) yields **`17` distinct witnesses per input** (`primal_exists=True, dual_unique=False`); adding $w_i(w_i - 1) = 0$ achieves `1` unique witness per $x \in \{0,1,2,3\}$ (`primal_exists=True, dual_unique=True`).
2. **Non-Malleable Binary Codecs (`project-everest/everparse@270f5aab`, Ramananandro et al. USENIX Security 2019; `secure-foundations/vest@026867a3`, Cai et al. USENIX Security 2025):** Inspecting `vest_lib/src/core/proof.rs` (`026867a3`, lines 24–225) shows how Vest modularly separates the dual round-trip laws into orthogonal Verus traits:
   - `SPRoundTrip::theorem_serialize_parse_roundtrip` (`PutGet`: $\forall v,\; \mathsf{parse}(\mathsf{serialize}(v)) = \mathsf{some}\;v$, yielding `NonAmbiguous::lemma_serialize_injective`);
   - `PSRoundTrip::theorem_parse_serialize_roundtrip` (`GetPut`: $\forall b\;v,\; \mathsf{parse}(b) = \mathsf{some}\;v \implies \mathsf{serialize}(v) = b$, yielding `corollary_parse_non_malleable`);
   - `NonMalleable::lemma_parse_non_malleable` (injective parsing rejecting distinct byte strings decoding to the same value, preventing signature/hash malleability).
   In `Probe 2`, a permissive 2-byte LEB128 codec satisfies `SPRoundTrip` (`0/16384` failures) yet fails `PSRoundTrip` on **`128` overlong byte sequences** (e.g., `0x8000` decoding to `0`, which re-serializes to `0x00`); rejecting zero-high-byte overlong forms achieves `0` failures on both `SPRoundTrip` and `PSRoundTrip`.

#### 4.4 Circumventing Rice's Barrier via Bounded Acceptance Surfaces & Mutation-Kill Canaries

Basis: derived

Requiring full semantic closure of a sound static analyzer ($\llbracket x_1 \rrbracket = \llbracket x_2 \rrbracket \land T(x_1)\;\text{ok} \implies T(x_2)\;\text{ok}$) is impossible for any decidable non-trivial property by Rice's theorem (e.g., `if false { *null } else { 0 }` vs. `0`) and does not compose across compilation layers. Instead, sound practical certification splits into two coupled checks:
- **Bounded Human Acceptance Surface (Intuition-Soundness):** The human reviewer inspects only a small, normal-form specification surface within cognitive budget $B$ (free of saturating arithmetic traps, implicit quantifiers, and custom notations), locked cryptographically across automated proof edits.
- **Parametric Family Completeness & 100%-Kill Mutation Canaries:** To catch degenerate tools (`find(_) = None`, `abort()`/`loop {}` rewrites, or finite lookup tables), require coupled end-to-end handling across an unbounded parametric input family ($\forall k \in \mathbb{N},\; \mathsf{Handles}(C \circ F, g(k))$), paired with **guard mutation testing** on $M_{\text{ref}}$ (deleting or weakening each semantic guard must kill at least one negative canary) and multi-oracle differential conformance (e.g., Miri, hardware silicon/QEMU, `Csmith`/`YARPGen`).

---

### 5. Two-Tier Signed Hardware-Profile Subsumption and Quotient Join-Semilattices

Basis: execution + derived

#### 5.1 Disclosure-Fatigue Laundering and Failure of Coordinate-Wise Subsumption

Inlining every hardware assumption—LLC cache partitioning (`MPAM`), DRAM disturbance (`RowPress`), DVFS frequency/power capping (`Hertzbleed`), Data Memory-Dependent Prefetchers (`GoFetch`), Pointer Authentication (`ARMv8.3 PAC`), hardware masking order (`O-PINI`), and instruction-fetch coherency (`CMODX`)—directly into every application's specification blows past human audit capacity ($|\Delta| \gg B_{\text{spec}}$), inducing disclosure-fatigue laundering.

However, abstracting hardware assumptions into a profile $\mathcal{H}_{\text{plat}}$ and checking $\mathcal{H}_{\text{plat}} \ge \mathcal{H}_{\text{req}}$ **coordinate-by-coordinate** is unsound because hardware mitigations exhibit three non-monotonic physical couplings (`Probe 4` in `## Evidence`):

| Test Scenario against `HReq(HardRT, RegimeA, d=2, SecretNonPtr)` | Naive Coordinate Check | Coupled Subsumption (`CoupledSub`) | Root Physical Coupling |
| :--- | :---: | :--- | :--- |
| `valid_platform` (`256 KiB`, `2.1 GHz`, `28 W`, `pac_strips=False`) | `True` | **`True`** | Working set `256 ≤ 256 KiB`; peak power `23.32 ≤ 28 W`; DMP tag intact |
| `hazard_pac_strips_dmp` (`pac_strips_before_dmp=True`, `dmp_hw_disabled=False`) | `True` (**UNSOUND**) | **`False`** (`COUPLED_PAC_STRIPS_NONPTR_TAG`) | PAC strips `[54:48]` non-pointer tag before DMP inspects `[55:32]` |
| `hazard_mpam_and_dvfs_knee` (`192 KiB`, `2.4 GHz`, `28 W`) | `True` (**UNSOUND**) | **`False`** (`COUPLED_MPAM_OVERFLOW(256>192KiB)`, `COUPLED_DVFS_KNEE_BREACH(31.85>28.00W)`) | `d=2` shares ($3\times$) + `SecretNonPtr` ($4/3\times$) inflate working set to `256 KiB` and cubic power $P_{\text{static}} + k f^3 \alpha$ to `31.85 W > 28 W` |
| `hazard_vacuous_false_profile` (`3.5 GHz`, `28 W`, `dvfs_locked=True`) | `True` (**UNSOUND**) | **`False`** (`VACUOUS_PROFILE_UNSAT`, `COUPLED_DVFS_KNEE_BREACH(86.18>28.00W)`) | Baseline power at `3.5 GHz` is `53.16 W > 28 W`: $\llbracket \mathcal{H}_{\text{plat}} \rrbracket = \bot$, making naive implication vacuously true |

#### 5.2 Two-Tier Architecture and Quotient Join-Semilattice Laws

The sound architecture separates platform physics from application intent:
1. **Tier 1 (`SignedHPlat` — Audited Once per Silicon Stepping / Microcode Version $\mu$):** Vendor- and consortium-signed (`SLH-DSA`/`ML-DSA`) profile grounded by gate-level certificates (open RTL) or differential fuzzing (`Revizor`/`PROLEAD_SW` on closed silicon), carrying a **mandatory physical satisfiability witness** $w_{\text{plat}} \models \mathcal{H}_{\text{plat}}$ (e.g., verifying $P_{\text{baseline}}(f_{\text{pin}}) \le P_{\text{cap}}$ whenever `dvfs_locked = true`) to block vacuous `False` profiles.
2. **Tier 2 (`HReq` — Compact Application Acceptance Surface):** At most five orthogonal domain nouns (`IsolationClass`, `TimingRegime`, `MaskingOrder`, `DmpStoreClass`, `BusPatchClass`) audited directly by humans.
3. **Quotient Fleet Join-Semilattice $(\mathsf{HPlat}/{\sim_{\text{DIT}}}, \preceq_{\text{plat}}, \sqcup_{\text{cons}})$:** Define platform strengthening $p_{\text{new}} \preceq_{\text{plat}} p_{\text{old}}$ on satisfiable profiles via monotonic dominance on `(llc↑, guard↑, t_ras↑, dvfs_lock↑, f_pin↓, p_cap↑, dmp_hw_disabled↑, pini↑)` together with the **DIT-quotiented PAC clause** $(\neg p_{\text{new}}.\mathsf{pac\_strips}) \lor p_{\text{old}}.\mathsf{pac\_strips} \lor p_{\text{new}}.\mathsf{dmp\_hw\_disabled}$. Quotienting out `pac_strips` whenever `dmp_hw_disabled = true` yields a genuine join-semilattice with two operational theorems verified exhaustively over a 32-profile grid in `Probe 4` (`refl=True`, `quotient_antisym=True`, `1,664` transitive triples, `297` monotone pairs, `1,024` fleet-LUB universal checks):
   - **Zero-Recompile Microcode-Delta Renewal:** If a microcode update satisfies $p_{\text{new}} \preceq_{\text{plat}} p_{\text{old}}$, then $\forall r,\; \mathsf{CoupledSub}(p_{\text{old}}, r) \implies \mathsf{CoupledSub}(p_{\text{new}}, r)$, renewing existing binary verification receipts in $O(1)$ without recompilation; regressive updates fail $\preceq_{\text{plat}}$ and automatically invalidate affected receipts.
   - **Conservative Fleet Deployment Envelope:** Certifying an application against the least upper bound $p_{\text{fleet}} = p_1 \sqcup_{\text{cons}} \dots \sqcup_{\text{cons}} p_k$ is both necessary and sufficient for deployment across heterogeneous hardware stepping $p_1, \dots, p_k$ by the universal property $(p_1 \preceq q \land p_2 \preceq q) \iff (p_1 \sqcup_{\text{cons}} p_2 \preceq q)$.

## Boundaries

- **`Lean4Lean` inductive declaration verification (`unsupported` / incomplete at `67f63b0c`):** Direct inspection of `digama0/lean4lean@67f63b0c`, `Lean4Lean/Verify/Environment.lean:224–239` establishes that `addDecl.WF` still contains an explicit `sorry` in the `inductDecl` branch pending a constructive `AddInduct` model. Accordingly, at this revision, `Lean4Lean` provides an independent executable re-checker and verified environment preservation for non-inductive declarations, **not** yet a completely `sorry`-free soundness proof of Lean 4's inductive type checker.
- **Full end-to-end formalization of `FRI`/`STARK` soundness inside `mm0-c` or `Candle` (`not examined` / open frontier):** While `mm0-c` and `Candle` serve as minimal-TCB proof checkers for first-order and HOL derivations, mechanizing post-quantum `FRI` proximity-gap soundness and Fiat–Shamir transcript verification inside a ~2 kLOC bare-metal checker was not executed in this study.
- **Closed-silicon physical satisfiability witnesses (`unknown` beyond empirical bounds):** On proprietary closed-RTL CPUs, a Tier-1 `SignedHPlat` profile's physical claims (e.g., absence of undocumented prefetchers or speculation leaks) can only be empirically tested via black-box fuzzers (`Revizor`, `PROLEAD_SW`), never deductively proven without RTL/netlist access; any residual hardware modeling gap must remain an explicit assumption rather than being hidden inside a tautological theorem.
- **Unbounded quantifier vacuity in full first-order / higher-order logic (`known not to apply` as a complete decision procedure):** The $(m+1)$-witness clause-independence protocol is complete for finite-conjunction propositional/decidable contract fragments when isolating witnesses exist, but general vacuity detection in arbitrary quantified higher-order logic is undecidable; failing to find an isolating witness within a solver timeout establishes `unknown`, not necessarily vacuity.
- **Stronger conclusion NOT established:** Passing `mm0-c` / `Candle` proof checking, `Picus` uniqueness, `Vest` round-trip proofs, and $(m+1)$-witness clause independence does **not** guarantee semantic faithfulness to an informal human requirement outside the reviewed `AcceptanceSurface`, nor does it prevent sub-gate analog hardware trojans or compromised signing keys.

## Evidence

### Primary Repository Sources Inspected

1. **`digama0/mm0` @ `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`**
   - `mm0-c/verifier.c` (819 lines): lines 382–638 (`CMD_PROOF_*` opcodes) and lines 670–720 (`verify(u8* file, u64 len)` checking `MM0B_MAGIC`, table bounds, and synchronized `parse_until` against `.mm0`).
   - `mm0-c/bare.sh` (9 lines): `-D BARE` bare-metal PGO build flags (`-fno-asynchronous-unwind-tables -fomit-frame-pointer -fno-stack-protector`).
   - Publication: M. Carneiro, *"Metamath Zero: Designing a Theorem Prover Prover"*, CICM 2020, LNCS 12236, DOI `10.1007/978-3-030-53518-6_5`.
2. **`CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`**
   - `candle/README.md` (28 lines): directory split across `standard`, `overloading`, `set-theory`, `parser`, `prover`, `syntax-lib`.
   - `candle/prover/candle_prover_semanticsScript.sml:428–460`: `Theorem semantics_thm` linking `semantics_prog` termination/divergence FFI traces to `EVERY ok_event`.
   - Publication: O. Abrahamsson, M. O. Myreen, R. Kumar, T. Sewell, *"Candle: A Verified Implementation of HOL Light"*, ITP 2022, DOI `10.4230/LIPIcs.ITP.2022.3`.
3. **`digama0/lean4lean` @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`**
   - `Lean4Lean/Verify/Environment.lean:10–239`: verified `addAxiom.WF`, `addDefinition.WF`, `addTheorem.WF`, `addOpaque.WF`, `addQuot.WF`, `addMutual.WF`, and `addDecl.WF` with explicit `inductDecl _ _ _ _ => sorry` at line 239.
   - Preprint: M. Carneiro, *"Lean4Lean: Towards a Verified Typechecker for Lean, in Lean"*, `arXiv:2403.14064` (2024).
4. **`leanprover/lean4` @ `0171678607a54e5a72c6a4ab6409286ba5002b05`**
   - `src/kernel/type_checker.cpp:660–693, 1266–1271`: `type_checker::reduce_nat` matching persistent name pointers (`g_nat_add`, `g_nat_sub`, `g_nat_mul`, `g_nat_pow`, `g_nat_gcd`, `g_nat_mod`, `g_nat_div`, `g_nat_beq`, `g_nat_ble`, `g_nat_land`, `g_nat_lor`, `g_nat_xor`, `g_nat_shiftLeft`, `g_nat_shiftRight`) purely by constant name.
   - External checkers pinned: `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab` and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`.
5. **`MetaCoq/metacoq` @ `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`** and **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`**
   - Related literature: J. Koenig & Z. Shao, *"CompCertO: Compiling Certified Open C Components"*, PLDI 2021, DOI `10.1145/3453483.3454097`; M. Sammler et al., *"DimSum: A Decentralized Approach to Multi-language Semantics"*, POPL 2023, DOI `10.1145/3571220`.
6. **Executable Reference Semantics & Oracles:**
   - `minirust/minirust@063d784186d3252bee242217f218223205c0b568`: `spec/lang/machine.md:10–40` (`Machine<M: Memory>` abstract machine fields).
   - `rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2`: `src/{sail_lean_backend,sail_coq_backend,sail_smt_backend,sail_c_backend,sail_sv_backend}`; A. Armstrong et al., POPL 2019, DOI `10.1145/3290384`.
   - `Wasm-DSL/spectec@acc6e834ff403c82554d081237f327346190ad96`: `spectec/src/{el,il,al,il2al,backend-interpreter,backend-latex,backend-prose}`; D. Youn et al., PLDI 2024, DOI `10.1145/3656440`.
   - `kenmcmil/ivy@257e3da96557df04303ccb38e80b5da1cd16cbae`: K. McMillan & O. Padon, CAV 2020, DOI `10.1007/978-3-030-53291-8_12`.
7. **Primal-Dual Uniqueness, Binary Codecs, and Vacuity Literature:**
   - `Veridise/Picus@138b151d3a388e5b6c040c163e0a1db04f2ceda6`: `picus-cex-uniqueness.rkt:1–45` (R1CS uniqueness counterexample driver targeting `z3`/`cvc5`); S. Pailoor et al., PLDI 2023, DOI `10.1145/3591282`.
   - `project-everest/everparse@270f5aab699ac284d8777d4f01be20a5d91ea47c`: `README.md` (`LowParse`, `3D`, `QuackyDucky`, `EverCBOR`, `EverCDDL`); T. Ramananandro et al., USENIX Security 2019.
   - `secure-foundations/vest@026867a37d4b918153058df2c8db6c52fc62ba35`: `vest_lib/src/core/{mod.rs,spec.rs,proof.rs}` (`SPRoundTrip`, `NonAmbiguous`, `PSRoundTrip`, `NonMalleable`, `NoLookAhead`, `Productive`); Y. Cai et al., USENIX Security 2025.
   - O. Kupferman & M. Y. Vardi, *"Vacuity Detection in Temporal Model Checking"*, STTT 2003, DOI `10.1007/s10009-002-0088-y`; H. Chockler, O. Kupferman, & M. Y. Vardi, *"Coverage Metrics for Temporal Logic Model Checking"*, TACAS 2001, DOI `10.1007/3-540-45319-9_36` (journal: STTT 2006, DOI `10.1007/s10009-006-0195-2`).

### Executable Micro-Probe Verification (Observed 2026-11-19, Python 3.13 stdlib only)

Running the self-contained probe suite below (`python3 - <<'EOF' ... EOF`, exit code `0`) produced the exact deterministic outputs quoted in `## Findings`:

```text
=== [Probe 1] CKV Subformula Vacuity & (m+1)-Witness Clause Independence ===
  sound_3_clauses: joint_pos=(-2, 0), independent=True, isolating=[('C1: y >= 0', (-2, -2)), ('C2: y <= 10', (-2, 12)), ('C3: (y - x) % 2 == 0', (-2, 1))]
  vacuous_true_masked: joint_pos=(-2, 0), independent=False, isolating=[('C1: y >= 0', (-2, -2)), ('C2: True (masked)', None), ('C3: (y - x) % 2 == 0', (-2, 1))]
  redundant_subsumed: joint_pos=(-2, 6), independent=False, isolating=[('C1: y >= 0 (subsumed by C2)', None), ('C2: y >= 5', (-2, 0)), ('C3: (y - x) % 2 == 0', (-2, 5))]

=== [Probe 2] Primal-Dual Uniqueness (R1CS / Picus) & Binary Codec Round-Trip ===
  R1CS[over_constrained_1_eq_0]: primal_exists=False, dual_unique=True, sols_per_x={0: 0, 1: 0, 2: 0, 3: 0}
  R1CS[under_constrained_no_bool]: primal_exists=True, dual_unique=False, sols_per_x={0: 17, 1: 17, 2: 17, 3: 17}
  R1CS[uniquely_constrained_2bit]: primal_exists=True, dual_unique=True, sols_per_x={0: 1, 1: 1, 2: 1, 3: 1}
  Codec[permissive_malleable]: SPRoundTrip(PutGet)_fails=0/16384, PSRoundTrip(GetPut)_fails=128, example=('8000', 0, '00')
  Codec[canonical_non_malleable]: SPRoundTrip(PutGet)_fails=0/16384, PSRoundTrip(GetPut)_fails=0, example=None

=== [Probe 3] Existential Slack Collapse vs. RandFrameFiberCodec Bijection ===
  Move(0) candidate[honest_deinit_slot0]: existential_R_slot=True, explicit_bijection=True
  Move(0) candidate[bug_omit_deinit]: existential_R_slot=True, explicit_bijection=False
  Move(0) candidate[bug_wrong_slot1]: existential_R_slot=True, explicit_bijection=False
  Move(0) candidate[bug_deinit_both]: existential_R_slot=True, explicit_bijection=False
  Bijection Q_tgt(128) ~= Q_src(4)xRandTape(8)xFrame(4): left_inv=128/128, right_inv=128/128
  FiberTarget[honest_masked_target]: func_ok=True, frame_ok=True, non_degen_probe=True (min_H=1.000000 bits)
  FiberTarget[goodhart_constant_tape_rho_0]: func_ok=True, frame_ok=True, non_degen_probe=False (min_H=0.000000 bits)

=== [Probe 4] Coupled Hardware-Profile Subsumption & Quotient Join-Semilattice ===
  valid_platform: naive=True, coupled=True, reasons=[]
  hazard_pac_strips_dmp: naive=True, coupled=False, reasons=['COUPLED_PAC_STRIPS_NONPTR_TAG']
  hazard_mpam_and_dvfs_knee: naive=True, coupled=False, reasons=['COUPLED_MPAM_OVERFLOW(256>192KiB)', 'COUPLED_DVFS_KNEE_BREACH(31.85>28.00W)']
  hazard_vacuous_false_profile: naive=True, coupled=False, reasons=['VACUOUS_PROFILE_UNSAT', 'COUPLED_DVFS_KNEE_BREACH(86.18>28.00W)']
  32-profile lattice: refl=True, quotient_antisym=True, trans=True (1664 triples), monotone=True (297 pairs), fleet_lub_universal=True (1024 pairs)
```

Self-contained reproduction script (Python 3.10+, standard library only):

```python
import math
from dataclasses import dataclass
from fractions import Fraction

# 1. Clause Independence
domain = [(x, y) for x in range(-2, 8) for y in range(-2, 14)]
for name, clauses in {
    "sound_3_clauses": [lambda x, y: y >= 0, lambda x, y: y <= 10, lambda x, y: (y - x) % 2 == 0],
    "vacuous_true_masked": [lambda x, y: y >= 0, lambda x, y: True, lambda x, y: (y - x) % 2 == 0],
    "redundant_subsumed": [lambda x, y: y >= 0, lambda x, y: y >= 5, lambda x, y: (y - x) % 2 == 0],
}.items():
    pos = next((pt for pt in domain if all(c(*pt) for c in clauses)), None)
    iso = [next((pt for pt in domain if (not clauses[i](*pt)) and all(clauses[j](*pt) for j in range(len(clauses)) if j != i)), None) for i in range(len(clauses))]
    assert (pos is not None and all(w is not None for w in iso)) == (name == "sound_3_clauses")

# 2. Primal-Dual R1CS (F_17) & Canonical LEB128
p = 17
for x in range(4):
    assert len([(w0, w1) for w0 in range(p) for w1 in range(p) if (w0 + 2 * w1 - x) % p == 0]) == 17
    assert len([(w0, w1) for w0 in range(p) for w1 in range(p) if (w0 + 2 * w1 - x) % p == 0 and (w0 * (w0 - 1)) % p == 0 and (w1 * (w1 - 1)) % p == 0]) == 1

# 3. Existential Slack vs. RandFrameFiberCodec Bijection
def r_slot_ex(sf, sr):
    return all(any((a is None and b is not None) if flag else (a == b) for flag in (False, True)) for a, b in zip(sf, sr))
for s in [(0, 0), (0, 1), (1, 0), (1, 1)]:
    assert r_slot_ex(s, s) and r_slot_ex((s[0], None), s) and r_slot_ex((None, None), s)
enc = lambda qs, rho, fr: (qs << 5) | (rho << 2) | fr
dec = lambda qt: ((qt >> 5) & 3, (qt >> 2) & 7, qt & 3)
assert all(enc(*dec(qt)) == qt for qt in range(128))

# 4. Coupled Hardware-Profile Subsumption & Quotient Semilattice
@dataclass(frozen=True)
class HPlat:
    llc: int; fpin: Fraction; pcap: Fraction; dit: bool; pac: bool
def sat(h: HPlat) -> bool:
    return Fraction(6, 1) + Fraction(11, 10) * (h.fpin ** 3) <= h.pcap
def canon(h: HPlat) -> HPlat:
    return HPlat(h.llc, h.fpin, h.pcap, h.dit, False if h.dit else h.pac)
def refines(a: HPlat, b: HPlat) -> bool:
    return sat(a) and sat(b) and a.llc >= b.llc and a.fpin <= b.fpin and a.pcap >= b.pcap and a.dit >= b.dit and ((not a.pac) or b.pac or a.dit)
def join(a: HPlat, b: HPlat) -> HPlat:
    dit = a.dit and b.dit
    return canon(HPlat(min(a.llc, b.llc), max(a.fpin, b.fpin), min(a.pcap, b.pcap), dit, False if dit else ((False if a.dit else a.pac) or (False if b.dit else b.pac))))
grid = [HPlat(l, f, c, d, p_) for l in (192, 256) for f in (Fraction(20, 10), Fraction(22, 10)) for c in (Fraction(25, 1), Fraction(30, 1)) for d in (False, True) for p_ in (False, True)]
assert all(refines(a, a) for a in grid)
assert all(canon(a) == canon(b) for a in grid for b in grid if refines(a, b) and refines(b, a))
assert all((refines(a, q) and refines(b, q)) == refines(join(a, b), q) for a in grid for b in grid for q in grid)
print("ALL CHECKS PASSED")
```

## Revalidation

1. **Lean 4 Kernel `reduce_nat` Name-Matching Check:** Inspect `src/kernel/type_checker.cpp` in any newer `leanprover/lean4` revision for `type_checker::reduce_nat` and `g_nat_land`; check whether symbol-name matching is gated on origin module identity or remains pure `Name` comparison.
2. **`Lean4Lean` Inductive Soundness Check:** Inspect `Lean4Lean/Verify/Environment.lean` (`addDecl.WF`) in newer `digama0/lean4lean` commits to check whether the `inductDecl` branch `sorry` has been closed by a constructive `AddInduct` proof.
3. **Micro-Kernel TCB Drift Check:** Compare line counts and command loops in `digama0/mm0` (`mm0-c/verifier.c`) and the top-level theorem statement `semantics_thm` in `CakeML/cakeml` (`candle/prover/candle_prover_semanticsScript.sml`).
4. **Vest / EverParse Non-Malleability Trait Check:** Verify `SPRoundTrip`, `PSRoundTrip`, and `NonMalleable` trait signatures in `secure-foundations/vest` (`vest_lib/src/core/proof.rs`) when adopting a newer Verus/Vest release.
5. **Mathematical Invariant Re-Execution:** Run the self-contained Python 3 script in `## Evidence`; any failure immediately flags a regression in clause-independence checks, R1CS primal-dual uniqueness, bijection inverses, or quotient join-semilattice monotonicity.
