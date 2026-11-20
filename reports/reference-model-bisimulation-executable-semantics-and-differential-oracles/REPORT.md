# Reference-Model Bisimulation, Executable Specifications, and Differential Oracles

## Summary

Deductive and symbolic verification engines—weakest-precondition (`wp`) evaluators, separation-logic heaps, region/borrow lenses, and proof-friendly abstract IRs—need not remain inside the human-audited Trusted Computing Base (TCB). They can be moved entirely out of the TCB by proving a formal correspondence theorem against an authoritative, community-vetted executable reference semantics $M_{\text{ref}}$ (such as MiniRust, Miri-derived Lean models, Sail ISA specifications, WebAssembly SpecTec, or K Framework semantics) over identical boundary types and a total, reversible syntax codec.

Four load-bearing invariants determine whether such a correspondence architecture actually shrinks semantic risk rather than laundering specification bugs:

1. **Exact Refinement Polarity with Bidirectional Fault-Kind Equivalence.** A sound correspondence theorem between a fast verification semantics $M_{\text{fast}}$ and a reference semantics $M_{\text{ref}}$ requires forward safety ($\mathsf{WellFormed}_{\text{fast}} \implies \mathsf{WellFormed}_{\text{ref}}$), backward behavioral inclusion ($\mathsf{Beh}_{\text{ref}} \subseteq \mathsf{Beh}_{\text{fast}}$ so $M_{\text{fast}}$ never drops demonic nondeterminism), **and** bidirectional fault-kind equivalence ($\mathsf{Reaches}_{\text{fast}}(p, q, \mathsf{fault}\;k) \iff \mathsf{Reaches}_{\text{ref}}(\mathsf{encode}(p), q, \mathsf{fault}\;k)$ for $k \in \{\mathsf{undefined}, \mathsf{unsupported}\}$). Without bidirectional fault equivalence, an implementation can satisfy forward-only refinement vacuously by collapsing inputs into `.unsupported`, or silently misclassify unsupported constructs as Undefined Behavior (UB).
2. **State-Coupling Bijection vs. Existential Ghost-Flag Slack Collapse.** Introducing an existentially quantified per-slot ghost boolean inside an untrusted simulation invariant to bridge a semantic gap (such as move deinitialization present in $M_{\text{fast}}$ but omitted in $M_{\text{ref}}$) collapses logically into unconstrained one-way slack ($\exists b : \mathsf{Bool},\dots \iff s_{\text{fast}} = \mathsf{uninit} \lor s_{\text{fast}} = s_{\text{ref}}$). Exhaustive state-space probing demonstrates that this slack lets omitted deinitialization, wrong-variable deinitialization, and reversed operand evaluation order all pass forward correspondence, while breaking behavioral inclusion outright on `MaybeUninit<u8>` byte copies where reading `Uninit` is well-defined. Simulation invariants must couple machine state bijectively (or via an explicit, layout-verified memory projection) rather than via existential untrusted ghost slack.
3. **Single-Source Multi-Backend Executable Specifications.** Mature executable specification ecosystems—MiniRust (`specr`-transpiled Rust), Sail (C/OCaml emulators + Rocq/Isabelle/HOL4/Lean/SMT/SystemVerilog backends for Armv8.5-A/v9.3-A/v9.4-A and RISC-V), SpecTec (EL $\to$ IL $\to$ AL generating LaTeX, Sphinx prose, and an executable Wasm interpreter), and K Framework (LLVM concrete backend + Haskell/Kore symbolic backend)—eliminate hand-synchronized prose-vs-proof drift, but still contain explicit trust boundaries (e.g., handwritten glue in `sail-arm`, conflating stuck states with UB in `kframework/c-semantics`, or `FIXME` empty demonic choice in MiniRust `BasicMemory::allocate`).
4. **Breaking Co-Authored Common-Mode Blindness.** A deductive correspondence proof between $M_{\text{fast}}$ and $M_{\text{ref}}$ cannot detect a missing UB guard shared by both models. Eliminating common-mode defects requires combining formal correspondence with **100%-kill guard mutation testing** of $M_{\text{ref}}$ (killing every single-guard deletion or weakening mutant via 3-pole `{ok, undefined, unsupported}` canaries) and **multi-oracle differential conformance testing** against independent implementations, randomized UB-free generators (`Csmith`, `YARPGen`), and community conformance suites (`Test262`, `riscv-tests`).

## Applicability

This report synthesizes primary-source architecture inspections, formal operational definitions, published literature, and an exhaustive finite-state Python micro-probe across fourteen durable upstream subjects pinned in `REPORT.json`:

- **Rust Abstract Machine & MIR Semantics (`minirust/minirust`, `rust-lang/miri`, `proofs-rs/lean-miri`):** Examined in combination to contrast normative specification design (`MiniRust`), production UB-detecting execution (`Miri`), and mechanized Lean 4 operational safety (`lean-miri`). Findings on `Outcome` partitioning, nondeterministic address allocation, and `Move`/`Deinit` semantics apply specifically to the pinned commits (`063d7841...`, `93d13704...`, `4c80e83f...`).
- **Authoritative Hardware ISA Specifications (`rems-project/sail`, `riscv/sail-riscv`, `rems-project/sail-arm`):** Examined as a single-source multi-backend family targeting executable C/C++/Lean emulators and interactive proof assistants (Rocq/Coq, Isabelle, HOL4, Lean 4). Armv9-A findings specifically reflect the ASL-translated `arm-v9.4-a` snapshot in `rems-project/sail-arm@5416ef6b...`, while Lean emulator observations reflect `riscv/sail-riscv@dda378c6...` and `rems-project/sail@97aa617d...`.
- **Single-Source Language DSLs & Rewriting Frameworks (`Wasm-DSL/spectec`, `runtimeverification/k`, `runtimeverification/evm-semantics`, `kframework/c-semantics`):** Examined comparatively for how intermediate representations (`EL`/`IL`/`AL` in SpecTec; `KORE` LLVM vs. Haskell backends in K) separate concrete conformance speed from symbolic reasoning, and where fault-kind conflation occurs.
- **Differential Conformance Oracles (`csmith-project/csmith`, `intel/yarpgen`, `tc39/test262`):** Examined as complementary empirical grounds for defeating common-mode specification and compiler/verifier bugs (including `YARPGen`'s documented bug discoveries against `Alive2` as well as `GCC` and `Clang`).
- **Simulation-Flipping Baseline (`AbsInt/CompCert`):** Examined specifically in `common/Smallstep.v` (`2685140b...`) for the exact receptiveness and determinacy hypotheses of `forward_to_backward_simulation` and why internal demonic nondeterminism breaks forward-to-backward flipping.

The formal correspondence laws, existential slack collapse analysis, and guard mutation methodology are language-agnostic: they apply to any verification stack pairing a deductive/symbolic engine $M_{\text{fast}}$ with an operational reference model $M_{\text{ref}}$ over discrete transition systems with explicit UB and unsupported-feature outcomes. The concrete counterexamples and mutation scores were executed directly in Python 3 on a self-contained finite-state MIR operational model (preserved verbatim under **Evidence**).

## Findings

### 1. Decoupling Verification Ergonomics from Semantic Trust

Basis: normative + source + derived

Verification engines face an inherent tension between **auditability** and **proof ergonomics**. A specification designed to be read by language designers, compared against a prose standard, and executed directly on thousands of conformance tests (an executable small-step interpreter $M_{\text{ref}}$ with flat byte-level memory, explicit provenance maps, dynamic tag checks, and explicit nondeterminism) is typically too low-level for ergonomic automated or interactive proof. Conversely, a verification-oriented semantics $M_{\text{fast}}$ (weakest-precondition transformer, separation-logic heap algebra, SSA/region borrow calculus, or symbolic evaluator) enables tractable proofs but is complex, optimization-tuned, and frequently refactored.

Moving $M_{\text{fast}}$ out of the TCB requires fixing a minimal, human-reviewed semantic anchor $M_{\text{ref}}$ and proving a correspondence theorem between $M_{\text{fast}}$ and $M_{\text{ref}}$ over:

- **Shared ground boundary types** `(Query, Out)` with identity observation ($\pi = \mathrm{id}$), eliminating codec spoofing between the two models;
- **A total, reversible syntax encoding** $\mathsf{encode} : \mathsf{Prog}_{\text{fast}} \to \mathsf{Prog}_{\text{ref}}$ and $\mathsf{decode} : \mathsf{Prog}_{\text{ref}} \to \mathsf{Option}\;\mathsf{Prog}_{\text{fast}}$ satisfying $\forall p,\; \mathsf{decode}(\mathsf{encode}(p)) = \mathsf{some}\;p$ (preventing trivial syntax collapse where $\mathsf{encode}(p) = \mathsf{nop}$); and
- **A staged support gate** $\mathsf{Supported}(p)$ demarcating the syntactic fragment for which correspondence is established, so unsupported features never masquerade as UB or safe returns.

#### Exact Polarity Law and Bidirectional Fault-Kind Equivalence

Let $\mathsf{WellFormed}_M(p, q)$ hold when execution of program $p$ on query $q$ under semantics $M$ cannot reach Undefined Behavior or an unclassified dead end; let $\mathsf{Beh}_M(p, q)$ denote the set of permitted observable outcomes (including demonic nondeterminism); and let $\mathsf{Reaches}_M(p, q, \mathsf{fault}\;k)$ denote finite reachability of an explicit fault terminal of kind $k \in \{\mathsf{undefined}, \mathsf{unsupported}\}$.

For every program $p$ within the staged support gate and every input query $q$, sound and non-vacuous correspondence requires the conjunction of three obligations:

```text
(1) Forward Safety:
    WellFormed_fast(p, q)  ==>  WellFormed_ref(encode(p), q)

(2) Backward Behavioral Inclusion (Demonic Nondeterminism Preservation):
    WellFormed_fast(p, q)  ==>  Beh_ref(encode(p), q) ⊆ Beh_fast(p, q)

(3) Bidirectional Fault-Kind Equivalence (for k ∈ {undefined, unsupported}):
    Reaches_fast(p, q, fault k)  <==>  Reaches_ref(encode(p), q, fault k)
```

Each conjunct closes a distinct soundness or vacuity loophole:

| Obligation | Defect Blocked if Omitted | Concrete Failure Mode |
| --- | --- | --- |
| **(1) Forward Safety** | Missing UB check in $M_{\text{fast}}$ | $M_{\text{fast}}$ proves a program with misaligned load or signed `INT_MIN / -1` division safe, while $M_{\text{ref}}$ raises UB. |
| **(2) Backward Behavioral Inclusion** | Dropping demonic nondeterminism in $M_{\text{fast}}$ | $M_{\text{ref}}$ nondeterministically picks any non-overlapping base address (`BasicMemory::allocate`), whereas $M_{\text{fast}}$ hardcodes `addr = 0x1000`, proving a program safe only for one lucky layout. |
| **(3a) Forward Fault Equivalence ($\Rightarrow$)** | Spurious bailout / vacuous `.unsupported` collapse | $M_{\text{fast}}$ maps every input (or every hard UB case) to `.unsupported`, making `WellFormed_fast(p, q)` false so (1) and (2) hold vacuously. |
| **(3b) Backward Fault Equivalence ($\Leftarrow$)** | Misclassifying `.unsupported` as `.undefined` (or vice versa) | $M_{\text{fast}}$ reports `.undefined` on inline assembly where $M_{\text{ref}}$ reports `.unsupported`, allowing an optimizer or client proof to treat unmodeled syntax as dead UB (`False`). |

This four-way terminal taxonomy appears explicitly in `proofs-rs/lean-miri@4c80e83f...`, `Miri/OperationalSafety.lean` (lines 23–86). `Miri.OperationalSafety.Outcome` separates `.returned`, `.undefinedBehavior`, `.blocked`, and `.unsupported`, and explicitly warns in its docstrings (lines 72–85) that `NoUndefinedBehavior` alone *"does not certify semantic coverage or resolve unsupported cases"*; certified `Safe` requires **both** `CompleteFrom` (no unclassified dead ends at any finitely reachable state) **and** that every reachable terminal outcome satisfies `Outcome.isReturn`. By contrast, `kframework/c-semantics@e6879d14...` (`README.md`, lines 31–32) notes that *"if you try to run a program that is undefined (or one for which we are missing semantics), the program will get stuck"*—illustrating the exact fault-kind conflation that Obligation (3) forbids.

#### Determinism-Based Simulation Flipping (Forward to Backward)

Basis: source + normative

When proving Obligation (2) ($\mathsf{Beh}_{\text{ref}} \subseteq \mathsf{Beh}_{\text{fast}}$), direct backward simulation proofs are notoriously tedious for passes or evaluators that restructure internal steps. CompCert (`AbsInt/CompCert@2685140b...`, `common/Smallstep.v`, lines 1050–1065 and 1863–1890; Leroy, *JAR 2009*, DOI `10.1007/s10817-009-9155-4`) establishes the standard sufficient condition for flipping a forward simulation into a backward simulation via `forward_to_backward_simulation`:

- `receptive L1`: whenever $L_1$ steps on an observable trace event $t_1$, it can step on any environment-compatible trace $t_2$ (`match_traces`), and each step emits at most one event (`single_events`); and
- `determinate L2`: target transitions are deterministic modulo external environment inputs (`sd_determ`), initial states are unique (`sd_initial_determ`), and final states cannot step (`sd_final_nostep`).

Crucially, this flipping theorem **fails** when $L_2$ ($M_{\text{ref}}$) possesses **internal demonic nondeterminism**—such as MiniRust's `pick(distr, pred)` for thread scheduling (`spec/lang/machine.md`, lines 206–217) or allocation base-address selection (`spec/mem/basic.md`, lines 108–124). For nondeterministic $M_{\text{ref}}$, either (a) the simulation must be proved directly in the backward/bisimulation direction over nondeterministic choices (pairing each `pick` choice in $M_{\text{ref}}$ with a matching choice in $M_{\text{fast}}$), or (b) internal nondeterminism must be explicitly externalized as an angelic/demonic oracle input stream shared identically across both machines so both become deterministic given the same oracle schedule.

---

### 2. The Existential Ghost-Flag Slack Collapse Trap

Basis: derived + execution + source

When aligning a verification semantics $M_{\text{fast}}$ with a slightly coarser or evolving reference semantics $M_{\text{ref}}$, proof authors frequently face local feature skew. A canonical real-world instance occurs around **move deinitialization** in Rust MIR: in Rust/MiniRust, moving out of a place deinitializes its storage (`Statement::Deinit` writes `list![AbstractByte::Uninit; len.bytes()]`, `minirust/minirust@063d7841...`, `spec/lang/step/statements.md`, lines 139–156), whereas an earlier or simplified reference model $M_{\text{ref}}$ may treat `Move(x)` identically to `Copy(x)` without overwriting `x` with `Uninit`.

A tempting but **unsound** workaround is to bridge the mismatch inside the untrusted simulation invariant using an existentially quantified per-local ghost boolean `moved : LocalId → Bool`:

$$R_{\text{ghost}}(s_{\text{fast}}, s_{\text{ref}}) :\equiv \forall \ell,\; \exists b : \mathsf{Bool},\; \text{if } b \text{ then } \bigl(s_{\text{fast}}(\ell) = \mathsf{Uninit} \land \exists v,\; s_{\text{ref}}(\ell) = \mathsf{Init}(v)\bigr) \text{ else } s_{\text{fast}}(\ell) = s_{\text{ref}}(\ell).$$

#### Why Existential Ghost Slack Collapses Logically

Because $b : \mathsf{Bool}$ is existentially quantified *per slot* with no external binding to the program trace or syntax, eliminating the existential yields an exact logical equivalence (`↔`) to **unconstrained one-way uninit slack**:

$$R_{\text{ghost}}(s_{\text{fast}}, s_{\text{ref}}) \iff \forall \ell,\; \bigl(s_{\text{fast}}(\ell) = \mathsf{Uninit} \land s_{\text{ref}}(\ell) \neq \mathsf{Uninit}\bigr) \;\lor\; \bigl(s_{\text{fast}}(\ell) = s_{\text{ref}}(\ell)\bigr).$$

This collapse has two severe engineering consequences, both verified exhaustively by the finite-state micro-probe in **Evidence** (625 state pairs across 2 locals $\times$ `{Uninit, 0, 1, 2, 3}`):

1. **Silent Acceptance of Three Distinct Implementation Bugs on Typed Loads.** On typed `u8` programs (`move_x_then_read_y` and `binop_move_x_copy_x`), forward safety + value agreement under $R_{\text{ghost}}$ passes with **zero errors** for all four variants against $M_{\text{ref}}(\text{move\_deinits}=\bot)$:
   - `V0_exact_move` (correctly deinitializes `x` on `Move(x)`): passes $R_{\text{ghost}}$ (`True`), fails bijective coupling (`False`) and fails bidirectional fault equivalence (`False`);
   - `V1_omit_move` (bug: forgets to deinitialize `x`): passes $R_{\text{ghost}}$ (`True`);
   - `V2_wrong_var` (bug: deinitializes `y` instead of `x`!): passes $R_{\text{ghost}}$ (`True`) because setting *any* local to `Uninit` in $s_{\text{fast}}$ stays inside the unconstrained one-way slack;
   - `V3_reversed_eval` (bug: evaluates `BinOp(Move(x), Copy(x))` right-to-left instead of left-to-right!): passes $R_{\text{ghost}}$ (`True`) because the post-state has `x = Uninit` while $M_{\text{ref}}$ retains `x = Init(v)`.
2. **Hard Soundness Failure on `MaybeUninit<u8>` Byte Copies.** Even if one attempts to rationalize one-way slack as "conservative UB" (claiming $M_{\text{fast}}$ only raises *more* UB than $M_{\text{ref}}$), that rationalization is **false** in Rust/MiniRust whenever untyped byte reads are reachable—for instance `MaybeUninit<u8>` or union padding reads (`minirust/minirust@063d7841...`, `spec/lang/step/expressions.md`, lines 80–87, where `ValueExpr::Union` initializes unwritten bytes to `AbstractByte::Uninit`). On `move_x_then_maybeuninit_byte_copy_x` starting from `(x=3, y=0)`, `V0_exact_move` produces `Outcome(ok, val=Uninit)` while $M_{\text{ref}}(\text{move\_deinits}=\bot)$ produces `Outcome(ok, val=3)`. Both are well-defined (`ok`), yet their observable byte values disagree (`Uninit ≠ 3`), violating $\mathsf{Beh}_{\text{ref}} \subseteq \mathsf{Beh}_{\text{fast}}$.

#### Concrete Fault-Collapse Verification (Micro-Probe Part 4)

Basis: execution

Running the same probe with `move_deinits=True` in $M_{\text{ref}}$ confirms the necessity of bidirectional fault-kind equivalence:

| Variant | Forward-Only Safety + Value Agreement | Bidirectional Fault Equivalence (`ub`, `unsupported`) | Diagnosis |
| --- | --- | --- | --- |
| `V0_exact_move` | `True` | `True` | Sound, exact correspondence |
| `F1_collapse_to_unsupported` | `True` (vacuous!) | `False` | Caught only by bidirectional fault equivalence |
| `F2_conflate_ub_unsupported` | `True` | `False` | Caught only by bidirectional fault equivalence |

**Design Rule:** Simulation invariants coupling $M_{\text{fast}}$ and $M_{\text{ref}}$ must enforce **exact state bijection** ($s_{\text{fast}} \simeq s_{\text{ref}}$) or an explicitly layout-verified, deterministic memory projection—never an existentially quantified ghost flag inside an untrusted proof module. Whenever a feature gap exists (such as missing `Deinit` in $M_{\text{ref}}$), either upgrade $M_{\text{ref}}$ so both models agree exactly, or exclude the affected construct (`Move` / `Deinit`) via the explicit syntactic support gate so its exclusion is visible in the audited theorem statement.

---

### 3. Comparative Architecture of Community-Vetted Executable Specifications

Basis: source + documentation + normative

Replacing bespoke, project-local trusted semantics with community-vetted executable specifications requires understanding each ecosystem's representation, execution vs. proof split, nondeterminism handling, and residual TCB.

| Ecosystem & Pinned Revision | Specification Form | Concrete Execution Backend | Proof / Symbolic Backend | Nondeterminism & Fault Taxonomy | Known Residual TCB / Pitfalls Observed in Source |
| --- | --- | --- | --- | --- | --- |
| **MiniRust** (`minirust/minirust@063d7841...`) | Literate Rust-like Markdown transpiled by `specr` (`spec/lang/*.md`, `spec/mem/basic.md`) | `specr`-generated Rust interpreter (`Machine::step`) | Specification anchor for Rust formalizations (not yet a mechanized theorem prover kernel) | Demonic `pick(distr, pred)` for threads (`machine.md:211`) and base addresses (`basic.md:113`); explicit `throw_ub!`, `throw_deadlock!` | `BasicMemory::allocate` (`basic.md:106–107`) notes `FIXME`: OOM with no valid address currently produces "no behavior" (`nb`) rather than an OOM/abort outcome; `Statement::Assign` (`statements.md:17–19`) marks aliasing and implicit retag as `TODO`. |
| **Miri** (`rust-lang/miri@93d13704...`) | Production Rust MIR interpreter inside `rustc` (`src/machine.rs`, `src/eval.rs`, `src/diagnostics.rs`) | Native `rustc` CTFE/Miri engine; Stacked Borrows (default, `eval.rs:181`) or Tree Borrows (`-Zmiri-tree-borrows`) | None natively; serves as primary differential oracle and porting target for `lean-miri` | Seeded PRNG sampling (`-Zmiri-many-seeds`) + GenMC stateless model checking (`TerminationInfo::GenmcMoot`, `diagnostics.rs:37`); explicit `TerminationInfo` separates `StackedBorrowsUb`, `TreeBorrowsUb`, `DataRace`, `UnsupportedInIsolation`, `UnsupportedForeignItem` | Finite seed sampling cannot exhaust unbounded demonic nondeterminism; strict provenance (`Int2PtrWithStrictProvenance`) is opt-in; host-isolated shims approximate OS syscalls. |
| **lean-miri** (`proofs-rs/lean-miri@4c80e83f...`) | Port of Miri semantics to Lean 4 (`Miri/*.lean`), ingesting `rustc`-normalized MIR JSON (`exporter/`) | Native compiled Lean runner (`tools/run.sh`) emitting `finalized_exit`, `undefined_behavior`, `unsupported`, `failed`, `pending` | Direct Lean 4 proofs via `Miri.OperationalSafety.{Safe, PartialCorrect}` (`OperationalSafety.lean:83–92`) | 4-way `Outcome`: `returned`, `undefinedBehavior`, `blocked`, `unsupported`; `Safe` requires `CompleteFrom` + only `returned` | `README.md:117–119` explicitly warns that `lake build` alone does not verify correspondence with upstream Miri or exporter/decoder agreement; exporter (`rustc` frontend) remains in the extraction TCB. |
| **Sail** (`rems-project/sail@97aa617d...`, `riscv/sail-riscv@dda378c6...`, `rems-project/sail-arm@5416ef6b...`) | First-order imperative ISA DSL with Z3-checked dependent bitvector types (`mapping clause encdec`, `function clause execute`) | C/C++ emulator (`sail_c_backend`, `sail_riscv_sim`), OCaml, experimental Lean emulator (`riscv/sail-riscv/lean_emulator`) | Rocq/Coq (`sail_coq_backend`), Isabelle/HOL4 (`sail_lem_backend`), Lean 4 (`sail_lean_backend`), SMT (`sail_smt_backend` / Isla), SystemVerilog (`sail_sv_backend`) | Architectural concurrency via `isla-axiomatic` / `RMEM`; RISC-V JSON config schema validates platform-defined knobs (`sail_riscv_config_schema.json`) | `sail-arm@5416ef6b...` (`arm-v9.4-a/README.md:20–29`) notes handwritten non-ASL glue (`fetch.sail`, `impdefs.sail`, `reset.sail`, `mem.sail`, `interface.sail`, `devices.sail`) outside the official Arm ASL translation; Lean backend and SystemVerilog backend are actively evolving. |
| **WebAssembly SpecTec** (`Wasm-DSL/spectec@acc6e834...`) | Single-source mathematical ASCII DSL (`EL`) elaborated to typed `IL`, transformed by 13 middle-end passes (`main.ml:40–54`), lowered to algorithmic `AL` (`il2al`) | Executable reference interpreter (`--interpreter`) generated directly from `AL` | LaTeX (`--latex`), Sphinx prose (`--prose`, `--splice-sphinx`), and mechanization preparation passes (`LetIntroMech`, `Undep`, `Totalize`, `Sideconditions`, `Else`) | Explicit rule premises and `otherwise` elimination (`Else`, `ElseSimp` passes) | SpecTec compiler passes (`Middlend.*`) sit between human-authored `EL` and generated `AL`/prose/mechanization artifacts unless backed by proof-producing translation validation; `_skip_passes = [Unthe]` (`main.ml:39`) reflects incomplete indexed-type support for `!` elimination. |
| **K Framework** (`runtimeverification/k@4a46d123...`, `evm-semantics@fbb2edbb...`, `c-semantics@e6879d14...`) | Rewriting-logic / Matching-Logic configuration cells & rules (`.k` / literate `.md`) compiled to `KORE` | LLVM backend (`kompile --backend llvm`) for high-throughput concrete conformance (e.g., Ethereum test suite on `KEVM`) | Haskell backend (`kompile --backend haskell`) for symbolic execution & reachability logic proofs with Z3 | Built-in search/nondeterminism (`kcc` compiles 3 variants: deterministic, expression-sequencing nondet, thread-interleaving nondet; `c-semantics/README.md:90–93`) | Concrete LLVM backend and symbolic Haskell backend are separate engines interpreting `KORE` (differential skew between backends is a real risk); `kframework/c-semantics` conflates UB and missing semantics into stuck configurations (`README.md:31–32`); `k/README.md:109–113` pins Z3 `4.12.1` due to solver bugs/regressions in other versions. |

#### Deep-Dive Source Highlights Across Ecosystems

1. **MiniRust's Clean Separation of Control Stack, Byte Memory, and Explicit `Deinit`** (`minirust/minirust@063d7841...`):
   - `spec/lang/machine.md` (lines 55–75, 99–103) explicitly separates the control stack (`Thread.stack : List<StackFrame<M>>`) from data memory (`ConcurrentMemory<M>`): *"stack and memory are completely disjoint concepts in the Abstract Machine."* Every live local lives in a heap-like `Allocation` (`AllocationKind::Stack`) with `data : List<AbstractByte<Provenance<ProvExtra>>>` (`spec/mem/basic.md`, lines 26–41).
   - `spec/lang/step/expressions.md` (lines 22–28, 138–153, 246–263) cleanly isolates **place evaluation** (`eval_place`, which allows misaligned/dangling raw pointers and records `aligned : bool` without faulting immediately) from **typed loads/stores** (`place_load` / `place_store`, which check `!place.aligned` and call `throw_ub!`). This distinction is a classic correspondence trap: a naive $M_{\text{fast}}$ that eagerly rejects misaligned pointer creation (or fails to validate `AddrOf` via `check_value` + `retag_ptr`, lines 163–176) will fail bidirectional fault equivalence on `let _ = *unaligned_ptr;` (`Statement::PlaceMention`, `statements.md:44–54`).
   - `spec/lang/step/statements.md` (lines 120–130, 147–156, 166–186) encodes `Validate` (load + `retag_val` + store), `Deinit` (overwrite with `AbstractByte::Uninit`), and `StorageLive` (which explicitly calls `storage_dead` first so the same address *may* be reused).
2. **Sail's Single-Source Bidirectional `encdec` + Multi-Target Extraction** (`rems-project/sail@97aa617d...`, `riscv/sail-riscv@dda378c6...`, `rems-project/sail-arm@5416ef6b...`):
   - Sail uses bidirectional `mapping clause encdec` (`rems-project/sail/README.md:88`) to keep instruction decoding and encoding synchronized by construction, and Z3-checked dependent bitvector types (`bits(12)`, `xlenbits`) to catch width truncation errors at specification typecheck time (Armstrong et al., *POPL 2019*, DOI `10.1145/3290384`).
   - At the inspected commits, `rems-project/sail` ships both `src/sail_lean_backend/` (`sail_plugin_lean.ml`, `pretty_print_lean.ml`) and `src/sail_coq_backend/`, and `riscv/sail-riscv` provides an executable Lean emulator (`lean_emulator/README.md`) testable directly against `riscv-tests` via `ctest --test-dir build -R lean_emulator`. This makes Lean-native bisimulation proofs against a Sail-generated RISC-V model possible, but the emulator's test results do not by themselves validate a proof-oriented extraction. In `Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7` (observed 2026-11-20) — a consumer that both proves theorems against a Sail Lean extraction and runs the upstream Lean-emulator tests — the tested artifact is a separately generated *computable* extraction, while the theorem-facing extraction is `noncomputable` (so its Sail decoder "does not evaluate", `docs/validation.md:133-137`). The project explicitly does not claim "that the proof-oriented and executable backend modes are identical" (`docs/validation.md:66`). Its validation set is "all 50 selected `rv64ui-p-*` ELF tests" (`docs/validation.md:56`): user-level integer tests only, with no `rv64mi`/`rv64si` privileged tests. Conformance-suite validation of the emulator therefore says nothing about the noncomputable proof extraction, or about privileged-architecture behaviour, unless separately argued. See package `riscv-privileged-isa-model-correspondence-prior-art`.
   - `rems-project/sail-arm@5416ef6b...` covers Armv8.5-A, Armv9.3-A, and Armv9.4-A translated automatically from Arm's internal ASL snapshot via `asl_to_sail`, booting Linux over its generated C emulator while keeping handwritten platform glue (`mem.sail`, `interface.sail`, `impdefs.sail`) isolated in explicit files.
3. **SpecTec's Multi-Stage EL $\to$ IL $\to$ AL Architecture** (`Wasm-DSL/spectec@acc6e834...`; Youn et al., *PLDI 2024*, DOI `10.1145/3656440`):
   - Rather than maintaining separate LaTeX math, English prose, OCaml reference interpreter, and Coq/Lean mechanizations by hand, SpecTec parses an External Language (`EL`), elaborates it into a typed Internal Language (`IL`), runs 13 ordered middle-end lowering passes (`main.ml:40–54`: `Ite`, `LetIntroMech`, `TypeFamilyRemoval`, `Undep`, `Totalize`, `Else`, `ElseSimp`, `Uncaseremoval`, `Sideconditions`, `SubExpansion`, `Sub`, `AliasDemut`, `ImproveIds`), and lowers `IL` into an imperative Algorithmic Language (`AL`) for both English prose rendering and direct execution (`--interpreter`).
   - The explicit presence of `LetIntroMech`, `Undep` ("Transform indexed types into types with well-formedness predicates"), and `Totalize` ("Run function totalization") highlights a key architectural insight: **mechanization-friendly IRs and human-readable math specs require systematic, auditable lowering passes**, because human notation relies on partial functions (`the` / `!`), implicit subtyping, and `otherwise` catch-alls that theorem provers reject.
4. **K Framework's Dual Concrete/Symbolic Execution Split** (`runtimeverification/k@4a46d123...`, `evm-semantics@fbb2edbb...`; Roșu & Șerbănuță, *JLAP 2010*, DOI `10.1016/j.jlap.2010.03.012`; Hildenbrandt et al., *CSF 2018*, DOI `10.1109/CSF.2018.00022`):
   - `KEVM` demonstrates industrial-scale executable semantics grounded by community conformance tests: a single K definition compiles to the LLVM backend for running official Ethereum reference test suites at near-native speed, and to the Haskell backend for symbolic reachability proofs (`evm-semantics/README.md:59–60`).
   - However, because symbolic reasoning requires auxiliary abstraction lemmas (`buf.md`, `abi.md`, `hashed-locations.md`, `evm-semantics/README.md:46–49`) and a separate Haskell rewriting engine, soundness depends on ensuring that symbolic simplification rules do not diverge from the concrete LLVM backend semantics.

---

### 4. Defeating Common-Mode Bugs: 100%-Kill Guard Mutation Testing & Multi-Oracle Differential Conformance

Basis: source + execution + normative

A formal correspondence theorem $M_{\text{fast}} \approx M_{\text{ref}}$ is strictly **relative**: if the same author (or automated agent) writes both $M_{\text{fast}}$ and $M_{\text{ref}}$—or copies an omission from one into the other—then a shared missing guard (e.g., forgetting signed `i8::MIN / -1` division overflow or forgetting alignment checking on loads) will satisfy $M_{\text{fast}} \approx M_{\text{ref}}$ with a kernel-checked proof while silently making the verifier unsound relative to real Rust/C/ISA execution.

Breaking **co-authored common-mode blindness** requires two orthogonal empirical layers around $M_{\text{ref}}$:

#### Layer A: 100%-Kill Guard Mutation Testing on $M_{\text{ref}}$

Following classical mutation testing theory (Jia & Harman, *IEEE TSE 2011*, DOI `10.1109/TSE.2010.62`), treat every semantic UB guard, fault-classification branch, and side-condition predicate $G_1, \dots, G_n$ inside $M_{\text{ref}}$ as an explicit mutation target. For each guard $G_i$, generate single-order mutants:
- **Guard Deletion ($G_i \mapsto \mathsf{false}$ / bypass):** removes the UB check entirely (simulating a missing-guard omission bug);
- **Predicate Weakening / Boundary Shift:** replaces `<` with `<=`, `align` with `1`, or masks signed overflow;
- **Fault-Kind Reclassification:** mutates `throw_ub!` to `Unsupported` (or vice versa).

A test suite $T$ for $M_{\text{ref}}$ is adequate only if it achieves a **100% non-equivalent guard mutation kill rate** against an independent external oracle $O_{\text{ext}}$ (e.g., `Miri`, `sail_riscv_sim`, or real hardware): for every guard mutant $M_{\text{ref}}^{(i)}$, there exists a test $t \in T$ such that $M_{\text{ref}}(t) = O_{\text{ext}}(t)$ and $M_{\text{ref}}^{(i)}(t) \neq M_{\text{ref}}(t)$.

In **Evidence (Micro-Probe Part 5)**, a 6-guard miniature MIR interpreter (`G1_live`, `G2_align`, `G3_bounds`, `G4_init`, `G5_div0`, `G6_intmin_div`) illustrates how deceptive ordinary unit tests are:
- A naive 3-test suite (happy-path add, happy-path div, div-by-zero UB) achieves **100% statement pass rate** yet kills only **1/6 (16.7%)** of guard mutants (`G5_div0`). Five critical UB guards could be deleted simultaneously without failing a single test.
- Expanding to a **3-pole canary suite** (covering `ok`, one isolating UB trigger per guard, and an explicit `unsupported` trigger) kills **6/6 (100.0%)** of guard mutants in 9 tests—linear $O(n)$ in the number of guards.

#### Layer B: Multi-Oracle Differential Conformance Testing

Single-oracle testing against one compiler or interpreter still admits shared misunderstandings of a standard. Mature language and ISA ecosystems defeat this via **multi-oracle differential testing** combining randomized UB-free program generators with curated specification test suites:

1. **Csmith (`csmith-project/csmith@0cdc7103...`; Yang et al., *PLDI 2011*, DOI `10.1145/1993498.1993532`):** Generates random C programs guaranteed free of undefined and unspecified behavior (via runtime safe-math wrappers and static pointer/alias tracking) and hashes all live global variables into a deterministic checksum (`README.md:13–58`). Discrepancies across independent compilers (`gcc`, `clang`, `CompCert`) or optimization levels (`-O0` vs. `-O3`) pinpoint miscompilations or spec bugs—famously finding bugs in every tested C compiler, and even in early CompCert's unverified front-end/parser while zero bugs were found in CompCert's Coq-verified middle-end.
2. **YARPGen (`intel/yarpgen@1adb290f...`; Livinskii et al., *OOPSLA 2020*, DOI `10.1145/3428264`; *PLDI 2023*, DOI `10.1145/3591295`):** Advances beyond Csmith's safe-math wrappers (which inhibit vectorization and loop optimization) by tracking exact compile-time value ranges, types, and alignments during generation (`README.md:18–22`), producing UB-free scalar and loop-heavy C/C++/DPC++/ISPC programs that aggressively exercise vectorizer and loop-nest passes. Crucially, `intel/yarpgen/README.md` (lines 27–28) documents **over 260 bugs found not only in `gcc`, `clang`, `ispc`, `dpc++`, and Intel `SDE`, but also in `Alive2`**—providing direct empirical proof that randomized multi-oracle differential testing uncovers defects in formal verification tools themselves.
3. **Test262 (`tc39/test262@2e58f87d...`):** Models the complementary curated-conformance paradigm. `INTERPRETING.md` (lines 21–140) codifies strict test-harness isolation invariants—fresh ECMAScript realm per test, dual non-strict / `"use strict";` execution unless overridden by frontmatter flags, standardized host hooks (`$262.createRealm`, `$262.detachArrayBuffer`, `$262.agent.*` for `SharedArrayBuffer` concurrency), and negative-test phase/error-type classification (`parse` vs. `resolution` vs. `runtime`). Comparing an executable specification interpreter (e.g., SpecTec or JS-IR) against multiple independent engines (`V8`, `SpiderMonkey`, `JavaScriptCore`) over Test262 exposes both spec-vs-implementation drift and harness-level fault misclassification.
4. **Miri Multi-Seed & Borrowing Oracles (`rust-lang/miri@93d13704...`):** For Rust MIR reference models (`MiniRust`, `lean-miri`), differential conformance runs exported MIR programs across (a) `Miri` under multiple `-Zmiri-many-seeds` schedules and both Stacked Borrows and Tree Borrows (`src/eval.rs:100,181`; Jung et al., *POPL 2020*, DOI `10.1145/3371109`; Villani et al., *PLDI 2025*, DOI `10.1145/3735592`), (b) `Miri`'s GenMC mode for weak-memory concurrency (`src/diagnostics.rs:37`), and (c) compiled `rustc` native binaries on deterministic UB-free programs. Whenever a program triggers UB in Miri on *any* seed, $M_{\text{ref}}$ must likewise admit an `undefinedBehavior` trace (and vice versa on supported constructs), directly validating both guard completeness and nondeterminism soundness.

#### End-to-End Correspondence & Grounding Checklist

Basis: derived

| Assurance Layer | Target Risk | Required Verification Artifact |
| --- | --- | --- |
| **1. Syntax Codec** | Program erasure / syntax spoofing | Total $\mathsf{encode}$ + partial $\mathsf{decode}$ with theorem $\forall p,\; \mathsf{decode}(\mathsf{encode}(p)) = \mathsf{some}\;p$ |
| **2. State Coupling** | Existential ghost-flag slack collapse | Bijective state map $s_{\text{fast}} \simeq s_{\text{ref}}$ (or deterministic layout-verified memory projection); zero unconstrained existential slot flags |
| **3. Correspondence Theorem** | Missing UB check, dropped nondeterminism, vacuous `.unsupported` bailout | Forward safety + backward behavioral inclusion + bidirectional fault-kind equivalence (`ub`, `unsupported`) over shared `(Query, Out)` |
| **4. Guard Mutation Suite** | Unexercised or dead UB checks in $M_{\text{ref}}$ | 100% kill score over all single-guard deletion/weakening/reclassification mutants in $M_{\text{ref}}$ |
| **5. Multi-Oracle Differential Suite** | Co-authored common-mode omissions in $M_{\text{fast}}$ and $M_{\text{ref}}$ | Differential concordance of $M_{\text{ref}}$ against $\ge 2$ independent oracles (e.g., `Miri` multi-seed + native `rustc`, or `sail_riscv_sim` + QEMU/hardware + `riscv-tests`) on curated + randomized (`Csmith`/`YARPGen`-style) inputs |

## Boundaries

- **Weak-Memory Concurrency & Relaxed-Memory Bisimulation (`not examined`):** While MiniRust's interleaving thread picker (`spec/lang/machine.md`), Sail's `isla-axiomatic`/`RMEM` interfaces, and Miri's GenMC integration were noted at the architectural level, formal bisimulation laws over axiomatic/promising relaxed-memory models (C11/Rust `Acquire`/`Release`/`Relaxed` atomics and out-of-thin-air avoidance) were not examined in detail and require trace/event-graph equivalence beyond sequential small-step state coupling.
- **Proof-Producing Lowering Inside SpecTec and Sail (`unknown`):** Inspection of `Wasm-DSL/spectec@acc6e834...` (`main.ml`) and `rems-project/sail@97aa617d...` (`src/sail_lean_backend/`) confirms that both tools run complex unverified OCaml middle-end passes before emitting proof-assistant definitions; whether mechanized translation validation exists for all 13 SpecTec `Middlend` passes or for Sail's Lean 4 backend at these commits was not resolved from the inspected files.
- **Forward-to-Backward Flipping Under Internal Nondeterminism (`known not to apply`):** CompCert's `forward_to_backward_simulation` lemma (`AbsInt/CompCert/common/Smallstep.v:1863`) is known not to apply when the target/reference semantics $L_2$ has internal demonic nondeterminism (such as MiniRust's address allocation `pick` or unscheduled thread interleaving) unless all internal choices are factored into a deterministic oracle parameter.
- **Emulator Test Validation vs. Proof-Oriented Sail Extraction (`known not to apply` without a separate argument):** Passing `riscv-tests` on the computable Sail Lean emulator does not establish the fidelity of a `noncomputable` theorem-facing extraction generated in a different backend mode. In the examined consumer (`Verified-zkEVM/riscv-zkvm@6810fc14…`) the tested set is also limited to 50 `rv64ui-p-*` user-level tests (observed 2026-11-20). Upstream `riscv/sail-riscv` itself builds the two modes as separate CMake targets (`generated_lean_rv64d`, noncomputable with axioms; `generated_lean_executable_rv64d`, computable stubs); see package `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`.
- **Exhaustive Proof of Non-UB via Dynamic Testing Alone (`unsupported` / `known not to apply`):** Differential testing tools (`Miri` with `-Zmiri-many-seeds`, `Csmith`, `YARPGen`, `Test262`) sample finite inputs and schedules; passing differential suites refutes common-mode defects empirically but never establishes universal UB freedom or correspondence across unbounded input domains.
- **Aliasing Model Finality in MiniRust (`unsupported`):** At `minirust/minirust@063d7841...`, `BasicMemory` (`spec/mem/basic.md:3–6`) explicitly does not model Stacked Borrows or Tree Borrows aliasing restrictions, and `Statement::Assign` (`spec/lang/step/statements.md:17–19`) leaves assignment aliasing and implicit retag as open `TODO`s. A correspondence proof against `BasicMemory` alone therefore does not establish Rust aliasing soundness.
- **Complete Mutation Equivalence Decidability (`known not to apply`):** Achieving 100% mutation score applies strictly to *non-equivalent* guard mutants; determining whether an arbitrary mutant is semantically equivalent to the original specification is undecidable in general and requires manual or SMT-assisted equivalence auditing for redundant defensive checks.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)

- `minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`:
  - `spec/lang/machine.md` (lines 14–121, 197–239): `Machine<M>`, `StackFrame<M>` control-vs-data stack split, demonic thread `pick` in `Machine::step`.
  - `spec/lang/step/expressions.md` (lines 22–28, 80–87, 138–178, 228–263): `eval_value`, `ValueExpr::Union` (`AbstractByte::Uninit` padding), `place_load` alignment UB check, `ValueExpr::AddrOf` (`check_value` + `retag_ptr`), `eval_place` allowing misaligned raw pointers.
  - `spec/lang/step/statements.md` (lines 17–54, 120–130, 139–186): `Statement::Assign` `TODO`s, `PlaceMention`, `Validate`, `ConcurrentMemory::deinit` / `Statement::Deinit`, `StorageLive`/`StorageDead`.
  - `spec/mem/basic.md` (lines 3–6, 18–48, 92–125): `BasicMemory` (no aliasing model), `Allocation`, demonic `pick` in `allocate` with `FIXME` noting empty-choice OOM collapsing to "no behavior".
- `rust-lang/miri` @ `93d13704b5e5e12dedfc54df626468000bc46262`:
  - `src/diagnostics.rs` (lines 15–62, 70–106): `TerminationInfo` distinguishing `Exit`, `StackedBorrowsUb`, `TreeBorrowsUb`, `DataRace`, `Int2PtrWithStrictProvenance`, `GenmcMoot`, `GlobalDeadlock`, `UnsupportedInIsolation`, and `UnsupportedForeignItem`.
  - `src/eval.rs` (lines 100, 140, 181, 200): `borrow_tracker` defaulting to `StackedBorrows` (configurable to `TreeBorrows`), `provenance_mode`.
- `proofs-rs/lean-miri` @ `4c80e83f91826c785fb607de9b9f4efa4c3b87cf`:
  - `Miri/OperationalSafety.lean` (lines 23–92, 113–131, 148–160): 4-way `Outcome` (`returned`, `undefinedBehavior`, `blocked`, `unsupported`), `CompleteFrom`, `NoUndefinedBehavior` vs. `Safe`, `PartialCorrect`, `safe_of_invariant`.
  - `README.md` (lines 63–69, 116–119): Runner outcome strings (`finalized_exit`, `undefined_behavior`, `unsupported`, `failed`, `pending`) and explicit warning that `lake build` alone does not verify upstream Miri correspondence.
- `rems-project/sail` @ `97aa617dcd4d01575f773cb58ea1e8686858c8c2`:
  - `README.md` (lines 11–69, 80–106): Multi-backend Sail architecture (C/OCaml/Coq/Isabelle/HOL4/Lean/SMT/SystemVerilog), bidirectional `mapping clause encdec`.
  - `src/sail_lean_backend/sail_plugin_lean.ml`, `src/sail_lean_backend/pretty_print_lean.ml`, `src/sail_coq_backend/sail_plugin_coq.ml`: Active Lean 4 and Coq/Rocq extraction backends verified present.
- `riscv/sail-riscv` @ `dda378c60fa0ad1bf13af5929bebee344a2e0a75`:
  - `README.md` (lines 29–55, 89–101, 128–132): `sail_riscv_sim`, JSON configuration schema (`sail_riscv_config_schema.json`), `riscv-tests` integration, Lean emulator reference.
  - `lean_emulator/README.md` (lines 1–36): CMake build of `generated_lean_executable_rv64d` and `ctest --test-dir build -R lean_emulator`.
- `rems-project/sail-arm` @ `5416ef6b43e9527c38dc71fb752259c1d01a47e1`:
  - `README.md` (lines 1–15) and `arm-v9.4-a/README.md` (lines 1–40): Armv8.5-A, Armv9.3-A, and Armv9.4-A ASL-to-Sail models (`gen_c`, `gen_isa`, `gen_coq`) and explicit enumeration of handwritten non-ASL glue files (`fetch.sail`, `impdefs.sail`, `reset.sail`, `devices.sail`, `mem.sail`, `interface.sail`).
- `Wasm-DSL/spectec` @ `acc6e834ff403c82554d081237f327346190ad96`:
  - `spectec/src/exe-spectec/main.ml` (lines 9–55, 106–154, 196–250): `target` variants (`Check`, `Ast`, `Latex`, `Prose`, `Splice`, `Interpreter`), 13 ordered `Middlend` passes (`all_passes`), `_skip_passes = [Unthe]`, `EL -> IL -> AL` pipeline.
- `runtimeverification/k` @ `4a46d1231473b599c699160132fd6e76a5c46406`:
  - `README.md` (lines 10–16, 109–113): K architecture and Z3 `4.12.1` version sensitivity note.
- `runtimeverification/evm-semantics` @ `fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1`:
  - `README.md` (lines 34–61): Core semantics files, symbolic abstraction files (`buf.md`, `abi.md`, `hashed-locations.md`), and LLVM (concrete) vs. Haskell (symbolic) backend split.
- `kframework/c-semantics` @ `e6879d14455771aa0cb3e3d201131d4d763a73a2`:
  - `README.md` (lines 31–38, 90–93): Stuck-state conflation of UB and missing semantics; three `kompile` variants (deterministic, nondet sequencing, nondet threading).
- `csmith-project/csmith` @ `0cdc710315cfee9035e22ef4363ca479270d1934`:
  - `README.md` (lines 5–65): UB-free random C generation and multi-compiler checksum differential oracle workflow.
- `intel/yarpgen` @ `1adb290f453505838f3aa33dc571f292b0c1810f`:
  - `README.md` (lines 8–28): Compile-time value-range tracking without safe-math wrappers; >260 bugs found across `gcc`, `clang`, `ispc`, `dpc++`, `sde`, and `alive2`.
- `tc39/test262` @ `2e58f87d8350ad51224617a041c6e041d52f8444`:
  - `INTERPRETING.md` (lines 21–140): Realm isolation, `$262` host hooks, dual strict/non-strict execution requirements.
- `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc` (referenced for simulation flipping):
  - `common/Smallstep.v` (lines 566–573, 1050–1065, 1289–1296, 1863–1890): `fsim_properties`, `receptive`, `determinate`, `bsim_properties`, `forward_to_backward_simulation`.

### Additional Primary Source (Observed `2026-11-20`)

- `Verified-zkEVM/riscv-zkvm` @ `6810fc14d9c40373101321cefaec59df8d82e3e7` (equal to upstream `main` on 2026-11-20):
  - `docs/validation.md` line 56 ("all 50 selected `rv64ui-p-*` ELF tests passed" for the executable Lean-emulator path), line 66 (does not prove "that the proof-oriented and executable backend modes are identical"), lines 109-127 (the `riscv-tests` corpus does not run against the hand-written model; general M-mode CSR access, `mtvec` setup and `mret` are not modeled), lines 133-137 ("the proof extraction is `noncomputable`, so the Sail decoder does not evaluate").

### Peer-Reviewed Literature

- Armstrong et al., *"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS"*, PACMPL Vol. 3 (POPL 2019), Article 71, DOI `10.1145/3290384`.
- Youn, Shin, Lee, Ryu, Breitner, Gardner, Lindley, Pretnar, Rao, Watt, Rossberg, *"Bringing the WebAssembly Standard up to Speed with SpecTec"*, PACMPL (PLDI 2024), DOI `10.1145/3656440`.
- Jung, Dang, Kang, Dreyer, *"Stacked Borrows: An Aliasing Model for Rust"*, PACMPL (POPL 2020), DOI `10.1145/3371109`.
- Villani, Hostert, Dreyer, Jung, *"Tree Borrows"*, PACMPL (PLDI 2025), DOI `10.1145/3735592`.
- Roșu & Șerbănuță, *"An Overview of the K Semantic Framework"*, JLAP 2010, DOI `10.1016/j.jlap.2010.03.012`.
- Hathhorn, Ellison, Roșu, *"Defining the Undefinedness of C"*, PLDI 2015, DOI `10.1145/2737979`.
- Hildenbrandt et al., *"KEVM: A Complete Formal Semantics of the Ethereum Virtual Machine"*, IEEE CSF 2018, DOI `10.1109/CSF.2018.00022`.
- Yang, Chen, Eide, Regehr, *"Finding and Understanding Bugs in C Compilers"*, PLDI 2011, DOI `10.1145/1993498.1993532`.
- Livinskii, Babokin, Regehr, *"Random Testing for C and C++ Compilers with YARPGen"*, PACMPL (OOPSLA 2020), DOI `10.1145/3428264`; *"Fuzzing Loop Optimizations in Compilers for C++ and Data-Parallel Languages"*, PACMPL (PLDI 2023), DOI `10.1145/3591295`.
- Jia & Harman, *"An Analysis and Survey of the Development of Mutation Testing"*, IEEE TSE 2011, DOI `10.1109/TSE.2010.62`.
- Leroy, *"A Formally Verified Compiler Back-end"*, JAR 2009, DOI `10.1007/s10817-009-9155-4`.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-19`)

Save the following standalone Python 3.10+ script as `/tmp/probe_bisimulation.py` and run `python3 /tmp/probe_bisimulation.py`:

```python
#!/usr/bin/env python3
from dataclasses import dataclass
from typing import Optional, Tuple

@dataclass(frozen=True)
class Outcome:
    kind: str  # "ok", "ub", "unsupported"
    val: Optional[int] = None
    reason: str = ""

State = Tuple[Optional[int], Optional[int]]  # (x, y), None = AbstractByte::Uninit

def ref_exec(prog: str, init: State, move_deinits: bool = False) -> Tuple[Outcome, State]:
    x, y = init
    if prog == "move_x_then_read_y":
        if x is None: return Outcome("ub", reason="read_uninit_x"), (x, y)
        v = x
        if move_deinits: x = None
        if y is None: return Outcome("ub", reason="read_uninit_y"), (x, y)
        return Outcome("ok", (v + y) % 8), (x, y)
    elif prog == "binop_move_x_copy_x":
        if x is None: return Outcome("ub", reason="read_uninit_x_lhs"), (x, y)
        lhs = x
        if move_deinits: x = None
        if x is None: return Outcome("ub", reason="read_uninit_x_rhs"), (x, y)
        rhs = x
        return Outcome("ok", (lhs + rhs) % 8), (x, y)
    elif prog == "move_x_then_maybeuninit_byte_copy_x":
        if x is None: return Outcome("ub", reason="read_uninit_x"), (x, y)
        if move_deinits: x = None
        raw_byte = -1 if x is None else x
        return Outcome("ok", raw_byte), (x, y)
    elif prog == "inline_asm_unsupported":
        return Outcome("unsupported", reason="inline_asm"), (x, y)
    raise ValueError(prog)

def fast_exec(variant: str, prog: str, init: State) -> Tuple[Outcome, State]:
    x, y = init
    if prog == "inline_asm_unsupported":
        if variant == "F2_conflate_ub_unsupported":
            return Outcome("ub", reason="misclassified_unsupported"), (x, y)
        return Outcome("unsupported", reason="inline_asm"), (x, y)
    if variant == "F1_collapse_to_unsupported":
        return Outcome("unsupported", reason="vacuous_bailout"), (x, y)
    exact_like = variant in ("V0_exact_move", "F2_conflate_ub_unsupported")
    if prog == "move_x_then_read_y":
        if x is None: return Outcome("ub", reason="read_uninit_x"), (x, y)
        v = x
        if exact_like or variant == "V3_reversed_eval": x = None
        elif variant == "V1_omit_move": pass
        elif variant == "V2_wrong_var": y = None
        if y is None: return Outcome("ub", reason="read_uninit_y"), (x, y)
        return Outcome("ok", (v + y) % 8), (x, y)
    elif prog == "binop_move_x_copy_x":
        if variant == "V3_reversed_eval":
            if x is None: return Outcome("ub", reason="read_uninit_x_rhs"), (x, y)
            rhs = x; lhs = x; x = None
            return Outcome("ok", (lhs + rhs) % 8), (x, y)
        if x is None: return Outcome("ub", reason="read_uninit_x_lhs"), (x, y)
        lhs = x
        if exact_like: x = None
        elif variant == "V1_omit_move": pass
        elif variant == "V2_wrong_var": y = None
        if x is None: return Outcome("ub", reason="read_uninit_x_rhs"), (x, y)
        rhs = x
        return Outcome("ok", (lhs + rhs) % 8), (x, y)
    elif prog == "move_x_then_maybeuninit_byte_copy_x":
        if x is None: return Outcome("ub", reason="read_uninit_x"), (x, y)
        if exact_like or variant == "V3_reversed_eval": x = None
        elif variant == "V2_wrong_var": y = None
        raw_byte = -1 if x is None else x
        return Outcome("ok", raw_byte), (x, y)
    raise ValueError(prog)

def R_ghost(s_fast: State, s_ref: State) -> bool:
    return all(any((sf is None and sr is not None) if b else (sf == sr) for b in (True, False))
               for sf, sr in zip(s_fast, s_ref))

def R_oneway_slack(s_fast: State, s_ref: State) -> bool:
    return all((sf is None and sr is not None) or (sf == sr) for sf, sr in zip(s_fast, s_ref))

vals = [None, 0, 1, 2, 3]
all_states = [(a, b) for a in vals for b in vals]
print(f"[PART 1] R_ghost <-> R_oneway_slack over {len(all_states)**2} state pairs:",
      all(R_ghost(sf, sr) == R_oneway_slack(sf, sr) for sf in all_states for sr in all_states))

typed_progs = ["move_x_then_read_y", "binop_move_x_copy_x"]
print("\n[PART 2] M_ref(move_deinits=False) vs M_fast variants on typed u8 programs:")
for v in ["V0_exact_move", "V1_omit_move", "V2_wrong_var", "V3_reversed_eval"]:
    ghost_pass = bij_pass = bidir_fault_pass = True
    for prog in typed_progs:
        for st in all_states:
            o_f, sf_p = fast_exec(v, prog, st)
            o_r, sr_p = ref_exec(prog, st, move_deinits=False)
            if o_f.kind == "ok":
                if not (o_r.kind == "ok" and o_r.val == o_f.val and R_ghost(sf_p, sr_p)): ghost_pass = False
                if not (o_r.kind == "ok" and o_r.val == o_f.val and sf_p == sr_p): bij_pass = False
            for fk in ("ub", "unsupported"):
                if (o_f.kind == fk) != (o_r.kind == fk): bidir_fault_pass = False
    print(f"  {v:18s}: R_ghost_fwd_pass={str(ghost_pass):5s} | R_bijective_fwd_pass={str(bij_pass):5s} | bidir_fault_eq={bidir_fault_pass}")

o_f, sf_p = fast_exec("V0_exact_move", "move_x_then_maybeuninit_byte_copy_x", (3, 0))
o_r, sr_p = ref_exec("move_x_then_maybeuninit_byte_copy_x", (3, 0), move_deinits=False)
print("\n[PART 3] MaybeUninit<u8> byte-copy counterexample (V0_exact_move vs M_ref(move_deinits=False)):")
print(f"  init=(3,0): M_fast -> {o_f} (state={sf_p}), M_ref -> {o_r} (state={sr_p}) -> Beh_ref subset Beh_fast FAILS (3 != -1/Uninit)")

print("\n[PART 4] Fault-collapse variants (M_ref move_deinits=True):")
for v in ["V0_exact_move", "F1_collapse_to_unsupported", "F2_conflate_ub_unsupported"]:
    fwd_only_pass = bidir_fault_pass = True
    for prog in typed_progs + ["inline_asm_unsupported"]:
        for st in all_states:
            o_f, _ = fast_exec(v, prog, st)
            o_r, _ = ref_exec(prog, st, move_deinits=True)
            if o_f.kind == "ok" and not (o_r.kind == "ok" and o_r.val == o_f.val): fwd_only_pass = False
            for fk in ("ub", "unsupported"):
                if (o_f.kind == fk) != (o_r.kind == fk): bidir_fault_pass = False
    print(f"  {v:28s}: fwd_only_pass={str(fwd_only_pass):5s} | bidir_fault_eq={bidir_fault_pass}")

def eval_guarded(op, a, b, addr, align, live, init_flag, disabled_guard=None):
    if disabled_guard != "G1_live" and not live: return Outcome("ub", reason="use_after_free")
    if disabled_guard != "G2_align" and (addr % align != 0): return Outcome("ub", reason="misaligned_access")
    if disabled_guard != "G3_bounds" and not (0 <= addr <= 1020): return Outcome("ub", reason="out_of_bounds")
    if disabled_guard != "G4_init" and not init_flag: return Outcome("ub", reason="uninit_read")
    if op == "sdiv":
        if disabled_guard != "G5_div0" and b == 0: return Outcome("ub", reason="div_by_zero")
        if disabled_guard != "G6_intmin_div" and (a == -128 and b == -1): return Outcome("ub", reason="signed_div_overflow")
        if b == 0: return Outcome("ok", 0)
        return Outcome("ok", int(a / b))
    if op == "asm": return Outcome("unsupported", reason="inline_asm")
    return Outcome("ok", (a + b) & 0xff)

guards = ["G1_live", "G2_align", "G3_bounds", "G4_init", "G5_div0", "G6_intmin_div"]
naive = [("add",1,2,4,4,True,True), ("sdiv",10,2,4,4,True,True), ("sdiv",10,0,4,4,True,True)]
full = naive + [
    ("add",1,2,4,4,False,True), ("add",1,2,6,4,True,True), ("add",1,2,1024,4,True,True),
    ("add",1,2,4,4,True,False), ("sdiv",-128,-1,4,4,True,True), ("asm",0,0,4,4,True,True),
]
k_naive = [g for g in guards if any(eval_guarded(*t, g) != eval_guarded(*t) for t in naive)]
k_full = [g for g in guards if any(eval_guarded(*t, g) != eval_guarded(*t) for t in full)]
print("\n[PART 5] Guard Mutation Score:")
print(f"  Naive suite (3 tests):  {len(k_naive)}/{len(guards)} killed ({100*len(k_naive)/len(guards):.1f}%) -> killed={k_naive}")
print(f"  3-pole suite (9 tests): {len(k_full)}/{len(guards)} killed ({100*len(k_full)/len(guards):.1f}%) -> killed={k_full}")
```

Observed output (`python3 /tmp/probe_bisimulation.py`, exit code `0`):

```text
[PART 1] R_ghost <-> R_oneway_slack over 625 state pairs: True

[PART 2] M_ref(move_deinits=False) vs M_fast variants on typed u8 programs:
  V0_exact_move     : R_ghost_fwd_pass=True  | R_bijective_fwd_pass=False | bidir_fault_eq=False
  V1_omit_move      : R_ghost_fwd_pass=True  | R_bijective_fwd_pass=True  | bidir_fault_eq=True
  V2_wrong_var      : R_ghost_fwd_pass=True  | R_bijective_fwd_pass=False | bidir_fault_eq=False
  V3_reversed_eval  : R_ghost_fwd_pass=True  | R_bijective_fwd_pass=False | bidir_fault_eq=True

[PART 3] MaybeUninit<u8> byte-copy counterexample (V0_exact_move vs M_ref(move_deinits=False)):
  init=(3,0): M_fast -> Outcome(kind='ok', val=-1, reason='') (state=(None, 0)), M_ref -> Outcome(kind='ok', val=3, reason='') (state=(3, 0)) -> Beh_ref subset Beh_fast FAILS (3 != -1/Uninit)

[PART 4] Fault-collapse variants (M_ref move_deinits=True):
  V0_exact_move               : fwd_only_pass=True  | bidir_fault_eq=True
  F1_collapse_to_unsupported  : fwd_only_pass=True  | bidir_fault_eq=False
  F2_conflate_ub_unsupported  : fwd_only_pass=True  | bidir_fault_eq=False

[PART 5] Guard Mutation Score:
  Naive suite (3 tests):  1/6 killed (16.7%) -> killed=['G5_div0']
  3-pole suite (9 tests): 6/6 killed (100.0%) -> killed=['G1_live', 'G2_align', 'G3_bounds', 'G4_init', 'G5_div0', 'G6_intmin_div']
```

## Revalidation

1. **Re-check the Formal Laws & Counterexamples (Seconds):** Run `python3 /tmp/probe_bisimulation.py` from **Evidence**; expect exit code `0` with identical five-part output confirming existential slack collapse, `MaybeUninit<u8>` behavioral divergence, bidirectional fault separation, and 100% guard mutation kill rate.
2. **Track Upstream MiniRust & `lean-miri` Evolution:** Diff `minirust/minirust` `spec/mem/basic.md` and `spec/lang/step/statements.md` against `063d784186d3252bee242217f218223205c0b568` to check whether aliasing (`TreeBorrows`/`StackedBorrows`) has been merged into the default memory model or whether `BasicMemory::allocate`'s OOM `FIXME` has been resolved. Diff `proofs-rs/lean-miri` `Miri/OperationalSafety.lean` against `4c80e83f91826c785fb607de9b9f4efa4c3b87cf` to confirm whether the 4-way `Outcome` type or `Safe` definition changed.
3. **Track Sail & SpecTec Mechanization Backends:** Check `rems-project/sail` `src/sail_lean_backend/` against `97aa617dcd4d01575f773cb58ea1e8686858c8c2`, `riscv/sail-riscv/lean_emulator/` against `dda378c60fa0ad1bf13af5929bebee344a2e0a75`, and `Wasm-DSL/spectec` `spectec/src/exe-spectec/main.ml` against `acc6e834ff403c82554d081237f327346190ad96` to verify whether proof-producing translation validation or mechanized Coq/Lean backends have been added or stabilized.
4. **Audit Any Candidate Correspondence Proof:** When evaluating a new $M_{\text{fast}} \leftrightarrow M_{\text{ref}}$ proof, inspect three narrow artifacts rather than re-reading the entire proof: (a) the statement of the correspondence theorem (verify $\pi = \mathrm{id}$, reversible `encode`/`decode`, forward safety, backward behavioral inclusion, and bidirectional `ub`/`unsupported` equivalence), (b) the simulation invariant (reject existentially quantified per-slot ghost slack), and (c) the single-guard mutation report for $M_{\text{ref}}$ paired with differential test logs against $\ge 2$ independent external oracles.
