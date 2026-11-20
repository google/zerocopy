# Inductive Step Relations vs. Executable ISA Interpreters in Proof Assistants

## Summary

Formalizing a hardware Instruction Set Architecture (ISA) in an interactive proof assistant (Lean 4, Rocq/Coq, or Isabelle/HOL) requires choosing how architectural nondeterminism—weak-memory store buffers, asynchronous interrupt latency, in-flight page-table walks, speculative address-translation cache fills, and underspecified CSR or MMIO behaviors—is represented at the semantic boundary. Across ten examined upstream formalizations, four architectural patterns govern proof ergonomics and soundness:

1. **Pure Inductive Transition Relations (`StepRel : S → S → Prop`)**: Nondeterministic transitions are constructors of an inductive predicate (`CompCert` top-level `Asm.step`, `Islaris` `trace_step`/`seq_step`, `seL4` `Simulation.data_type.Step`). They express unbounded demonic choice directly without threading oracle parameters, but suffer from **silent-stuckness vacuity** when constructors or side conditions are omitted, $O(N)$ dead-constructor refutation overhead on flat $N$-instruction inductive families during symbolic execution, non-executability on conformance suites (`riscv-tests`), and failure of CompCert's `determinate`-gated forward-to-backward simulation flipping.
2. **Total Oracle-Parameterized Interpreters (`step : S → Oracle → StepOutcome S`)**: Nondeterministic environment actions are externalized into a typed `Oracle` input so single-step execution is a total deterministic function (`LNSym` `stepi` for deterministic user code; `lean-sail` `ChoiceSource`; `seL4` `getActiveIRQ` over `irq_oracle`; CakeML functional big-step clocks/oracles). They unlock kernel `whnf` evaluation, `simp`/`dsimp` equational rewriting without dependent inversion clutter, and pointwise 2-safety (noninterference) proofs by synchronizing two runs on the identical `o : Oracle`. Their primary hazard is **oracle under-parameterization**: if `Oracle` cannot witness simultaneous spec-permitted events (e.g., a speculative TLB fill followed immediately by an asynchronous interrupt before instruction fetch), the interpreter silently under-approximates hardware behavior.
3. **Propositional / Set-Valued Nondeterministic Monads (`S → Set (A × S) × Bool` or `S → (Option (A × S) → Prop)`)**: Deployed in `seL4/l4v` (`Nondet_Monad`) and `mit-plv/riscv-coq` (`OStateND`, `Post`). They preserve monadic `do`-notation compositionality across helper functions while remaining relational, but introduce the **empty-choice collapse trap**: an unguarded empty choice (`Nondet_Monad.select ∅` returning `(∅, False)`, or `∀ v, MMIOReadOK v → post v` without `∃ v, MMIOReadOK v`) satisfies arbitrary postconditions including `False` unless paired with an explicit `empty_fail` or non-emptiness witness.
4. **Two-Layer Free-Monad / Hybrid Architectures (`FreeM Outcome Unit` + Compact Relational Shell + `.interp`)**: Deployed by `mit-pdos/xv6iris` (redefining `lean-sail`'s `PreSailM` as an inductive free monad over a 17-constructor `Outcome` event type), `mit-plv/riscv-coq` (`free riscv_primitive primitive_result` interpreted into both `OState` and propositional `MinimalMMIO`), and `AbsInt/CompCert` (wrapping a total deterministic `exec_instr : ... → outcome` inside a 3-constructor `Inductive step`). Intra-instruction decode/ALU/CSR logic reduces computationally, while weak-memory, TLB, MMIO, and interrupt interleavings live in a compact (< 20 constructor) relational automaton linked to a kernel-executable interpreter by proved soundness and oracle surjectivity.

## Applicability

This report synthesizes primary-source inspections, formal metatheory, and an executable finite-state Python 3 probe across ten upstream repositories pinned in `REPORT.json`:

- **Lean 4 (`leanprover/lean4@5045d005...`, `rems-project/lean-sail@e4745c82...`, `mit-pdos/xv6iris@5cb9df99...`, `leanprover/LNSym@5c05220f...`, `Verified-zkEVM/riscv-zkvm@6810fc14...`)**: Examined for Lean `v4.34.1` kernel reduction rules (`whnf` vs `Std.ExtDHashMap` opacity), equation-compiler `noConfusion`/`casesOn` inversion scaling, `EStateM` + `ChoiceSource` vs free-monad `PreSailM` (`Outcome` tree + `.interp`), total `ArmState → ArmState` symbolic rewriting (`LNSym`), and `Option`-returning partial step vacuity (`riscv-zkvm`).
- **Rocq / Coq (`mit-plv/riscv-coq@03881b21...`, `rems-project/islaris@c978e10f...`, `AbsInt/CompCert@2685140b...`)**: Examined for abstract monadic ISA semantics (`Monad M` instantiated to `OState`, `StateND`, `OStateND`, `Post`, and `free`), Isla SMT-trace operational semantics (`trace_step`, `seq_step`, `seq_nb_state`), and CompCert's RISC-V `exec_instr` + `Inductive step` hybrid and `forward_to_backward_simulation` determinacy hypotheses.
- **Isabelle/HOL & HOL4 (`seL4/l4v@b0fe7693...`, `HOL-Theorem-Prover/HOL@0c30bdb7...`)**: Examined for `('s, 'a) nondet_monad` (`select` vs `state_select`, `empty_fail`, `no_fail`, `ignore_failure`), oracle-ized interrupt polling (`getActiveIRQ` over `irq_oracle`), lifting monadic specs into relational `Simulation.data_type` automata, and L3/CakeML functional big-step semantics.

All evidence was observed on `2026-11-20`. While RISC-V (`RV64IM_Zicsr_Zifencei`, `Sv39`) and Armv8-A serve as primary ISA exemplars, the soundness, surjectivity, progress, empty-choice, and 2-safety obligations apply to any mechanized ISA in dependent-type or HOL proof assistants. For Lean `v4.34.1` `bv_decide` axiom mechanics and `ExtDHashMap` kernel irreducibility benchmarks, see corpus package `lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`; for privileged RISC-V correspondence scope, see `riscv-privileged-isa-model-correspondence-prior-art`.

## Findings

### 1. Taxonomy of Hardware ISA Nondeterminism and Prover Representations

Basis: source + documentation + derived

Privileged and concurrent hardware ISAs introduce five sources of nondeterminism absent from user-mode ALU models: (1) asynchronous timer/external interrupt edges and bounded delivery latency; (2) weak-memory store buffers (RVWMO/TSO), incoherent instruction caches prior to `fence.i`, per-level page-walk caches (PWCs), leaf TLBs across `satp` switches prior to `sfence.vma`, and speculative page-table walks; (3) `LR`/`SC` spurious store-conditional failure; (4) WARL/WLRL CSR legalization and MMIO device reads; and (5) decomposed misaligned or page-crossing accesses that partially commit before faulting.

Inspection of the ten pinned upstream codebases maps these mechanisms onto six semantic type signatures:

| Pattern | Canonical Signature | Pinned Upstream Exemplars | Kernel Eval? | Nondeterminism Encoding |
| --- | --- | --- | --- | --- |
| **A. Inductive Relation** | `StepRel : S → Label → S → Prop` | `islaris@c978e10f` (`opsem.v:395,476` `trace_step`, `seq_step`); `l4v@b0fe7693` (`Simulation.thy:42` `Step`) | No (`Prop` / set) | Multiple matching constructors or existential premise variables. |
| **B. Pure Total Step** | `step : S → S` (errors in `S.err`) | `LNSym@5c05220f` (`Arm/Exec.lean:105` `stepi : ArmState → ArmState`) | Yes (with reducible state) | None; strictly deterministic user-mode semantics. |
| **C. Partial `Option`/`Result`** | `step : S → Option S` or `EStateM Err S Unit` | `riscv-zkvm@6810fc14` (`Execution.lean:344`); `lean-sail@e4745c82` (`ConcurrencyInterfaceV1.lean:109` with `trivialChoiceSource`) | Yes (if map/externs reducible) | None (`none` conflates traps, halts, and unmodeled ops unless refined). |
| **D. Oracle Interpreter** | `step : S → Oracle → StepOutcome S` | `lean-sail@e4745c82` (`ChoiceSource`, `L9–13`); `l4v@b0fe7693` (`MachineOps.thy:118` `irq_oracle`); CakeML/L3 clocked steps | Yes (for concrete `o`) | `∀ o : Oracle` for safety; `∃ o : Oracle` for reachability. |
| **E. Set / CPS Monad** | `S → Set (A × S) × Bool` or `S → (Option (A × S) → Prop)` | `l4v@b0fe7693` (`Nondet_Monad.thy:36`); `riscv-coq@03881b21` (`Utility/Monads.v:202,252,383` `StateND`, `OStateND`, `Post`) | No (`Prop` / sets) | Set union `f ⊓ g`, `select A`, or universal postcondition quantification. |
| **F. Hybrid Free-Monad / `exec_instr` + Relational Shell** | Pure `exec_instr` or `FreeM Outcome Unit` + compact `Inductive step` | `CompCert@2685140b` (`riscV/Asm.v:1075`); `xv6iris@5cb9df99` (`ConcurrencyInterfaceV1.lean:132`); `riscv-coq@03881b21` (`MinimalMMIO.v:96`) | Yes (via `.interp` / `exec_instr`) | Intra-instruction logic is functional; nondeterminism isolated to event handler rules. |

---

### 2. Proof-Ergonomics Trade-Offs: Inversion vs. Reduction

Basis: source + derived

#### 2.1 Concrete Machine-Code Verification: $O(1)$ Reduction vs. $O(N)$ Constructor Inversion

When stepping concrete binary code at a known PC (e.g., `0x91000400` in Armv8 or `0x00150513` in RV64):

- **Executable Evaluators (`stepi` / `exec_instr`)**: `leanprover/LNSym@5c05220f...` (`Arm/Exec.lean:171–178`) discharges fetch and decode via one equational rewrite lemma:
  ```lean
  theorem stepi_eq_of_fetch_inst_of_decode_raw_inst
      (s : ArmState) (addr : BitVec 64) (rawInst : BitVec 32) (inst : ArmInst)
      (h_err : r .ERR s = .None) (h_pc : r .PC s = addr)
      (h_fetch : fetch_inst addr s = some rawInst) (h_decode : decode_raw_inst rawInst = some inst) :
      stepi s = exec_inst inst s := by
    simp only [stepi, h_err, h_pc, h_fetch, h_decode, read_err, read_pc]
  ```
  Because `decode_raw_inst` is a pure total function over `BitVec 32`, `h_decode` closes by `rfl` (kernel `whnf`), and `exec_inst` unfolds only the single matched arm out of 41 instruction classes (`Arm/Exec.lean:12–99`). Similarly, `AbsInt/CompCert@2685140b...` (`riscV/Asm.v:1076–1082`) wraps `exec_instr f i rs m = Next rs' m'` as an equational premise of `exec_step_internal`, so `Asmgenproof` reduces `exec_instr` directly by `simpl`.
- **Flat Inductive Relations (`StepRel`)**: If `StepRel : S → S → Prop` places $N$ instruction/fault rules at the top level, proving any property of successor states `h : StepRel s s'` requires `cases h` (Lean 4), `inversion H; subst` (Rocq), or `ind_cases` (Isabelle/HOL):
  - In **Lean 4** (`leanprover/lean4@5045d005...`), `cases h` elaborates `StepRel.casesOn` + `noConfusion` discrimination across all $N$ constructors, building explicit refutation subterms for all $N - 1$ non-matching opcodes at *every instruction* of a basic block ($16,000$ dead refutations for a 200-instruction routine over an 80-rule ISA) unless factored through a proved functional characterization lemma.
  - In **Rocq**, dependent `inversion` over indexed register maps (`RegisterType : Register → Type`) introduces `existT`/`JMeq` equalities requiring `inj_pair2_eq_dec`. Notably, `rems-project/islaris@c978e10f...` (`theories/opsem.v:475–480`) avoids multi-constructor `Inductive` explosion in `seq_step` by defining a **single** constructor `SeqStep` containing an internal `match κ with ...` over `option trace_label` (noting `(* TODO: Maybe refactor this into several constructors rather than a match *)`), allowing `destruct κ` without index unification.

#### 2.2 Global Invariants and Weakest-Precondition (`wp`) Layering

Conversely, for universal architectural invariants ($\forall s, s',\; \mathrm{Inv}(s) \land \mathrm{Step}(s, s') \implies \mathrm{Inv}(s')$), inductive constructors immediately expose guard premises in context, whereas unfolding a monolithic interpreter `step(s, o)` causes exponential `split` / `destruct_one_match` branching across sequential stages (IRQ check $\to$ 3-level `Sv39` walk $\to$ PMP check $\to$ decode $\to$ execute). Mature functional/monadic developments eliminate this branch blowup via syntax-directed `wp` rules:
- `mit-plv/riscv-coq@03881b21...` (`Utility/Monads.v:125–155, 183–195, 294–323, 361–377`) maps `OState` and `OStateND` to CPS `Post` transformers via `computation_with_answer_satisfies_Bind` and `Ltac simpl_computation_with_answer_satisfies`.
- `seL4/l4v@b0fe7693...` uses `wpsimp` backward over `Nondet_Monad` `bind` chains without unfolding state records.
- `mit-pdos/xv6iris@5cb9df99...` (`README.md:138–142`) confines Sail monadic symbolic execution (`swp`) to per-step/per-instruction leaf lemmas while closing read-only decode/configuration checks by computation.

#### 2.3 Lean 4 Kernel Reducibility Constraints on Interpreter State

Basis: source

Defining `step : S → Oracle → StepOutcome S` in Lean 4 (`v4.34.1`) enables axiom-free kernel `whnf` evaluation (`rfl`, `decide +kernel`) **only** if `S` avoids kernel-opaque primitives:
- `rems-project/lean-sail@e4745c82...` (`Sail/ConcurrencyInterfaceV1.lean:101–108, 173–176`) backs `SequentialState` with `Std.ExtDHashMap` and `Std.ExtHashMap`. Because hash bucket indexing depends on `USize` (`System.Platform.getNumBits`, `opaque` in the kernel), `whnf` blocks on `s.regs.get? r`; execution works only via compiled native binaries (`main_of_sail_main`, `Sail/Sail.lean:39–52`), while proofs require `get?_insert` rewrites.
- `Verified-zkEVM/riscv-zkvm@6810fc14...` (`docs/validation.md:66, 133–137`) marks its theorem-facing Sail extraction `noncomputable` due to `axiom` platform hooks, preventing even pure Sail decoders from evaluating in-kernel.
- Kernel-evaluable ISA interpreters must store registers in fixed structures (`x1..x31`), total closures (`Reg → BitVec 64`), `Array`, or comparison-based trees (`Std.TreeMap` / `RBMap`), and express loops via structural recursion or `Nat`-measured well-founded recursion (`whileFuelM`, `Sail/Sail.lean:55–61`).

---

### 3. Vacuity Traps, Progress/Usefulness Theorems, and Empty-Choice Collapse

Basis: source + execution + derived

#### 3.1 Silent Stuckness vs. Partitioned `StepOutcome` Progress

In an inductive relation `StepRel : S → S → Prop`, accidentally omitting a constructor (e.g., forgetting illegal U-mode `SRET` when `sip.STIP = 0`) makes `StepRel s s'` `False` at that state, so trace invariants $\forall s',\; \mathsf{Star}\;\mathsf{StepRel}\;s_0\;s' \implies \mathsf{Inv}(s')$ hold **vacuously**. Likewise, encoding traps as `Option.none` in a forward success-only simulation `step_hand s = some s' → ∃ t', ...` (`Verified-zkEVM/riscv-zkvm@6810fc14...`, `Execution.lean:344–348`, `StepRun.lean:327–334`) places zero constraints on trap vectors, `scause`, `sepc`, or `stval`.

Closing both loopholes requires partitioning step results into an explicit 4-way sum—`StepOutcome S := .step S | .trap Cause Tval S | .halted Code | .archUndefined Reason`—backed by three theorems:
1. **Total Progress**: $\forall s,\; \mathsf{ArchInv}(s) \implies \exists out,\; \mathsf{StepRel}(s, out)$ (automatic for total `step : S → Oracle → StepOutcome S` when `Inhabited Oracle`).
2. **Support-Gate Adequacy**: $\forall s,\; \mathsf{ArchInv}(s) \land \mathsf{Supported}(s) \implies \forall o,\; \mathsf{step}(s, o) \neq \mathsf{archUndefined}(\_)$ (prevents routing hard valid states into `.archUndefined`).
3. **Positive Usefulness Canaries**: Existential reachability witnesses ($\exists s_0, \vec{o}, s_k$) for normal retirement, page/illegal-instruction traps, asynchronous IRQ entry, and `SRET` return. In **Probe Part 1**, omitting U-mode `SRET` lets a false invariant pass (`omitted_rel_vacuous_inv = True`), whereas total progress immediately catches the gap (`progress = False`).

#### 3.2 Empty-Choice Collapse in `seL4/l4v`, `riscv-coq`, and `Islaris`

Set-valued and CPS nondeterministic monads harbor an analogous empty-set vacuity hazard:

1. **`seL4/l4v` `select` vs. `state_select` (`seL4/l4v@b0fe7693...`, `lib/Monads/nondet/Nondet_Monad.thy:105–126`)**:
   - `select A ≡ λs. (A × {s}, False)` returns `({}, False)` when `A = {}` (*"does not fail (even if the set is empty)"*, `L101–102`). Under no-fail Hoare validity, `select {}` proves `⦃⊤⦄ select {} ⦃λ_ _. False⦄` (`select(empty) proves False postcondition = True` in **Probe Part 3**)!
   - Conversely, `state_select r ≡ λs. ((λx. ((), x)) ` {s'. (s, s') ∈ r}, ¬ (∃s'. (s, s') ∈ r))` sets `fail = True` on empty relations, satisfying `empty_fail` (`fst (m s) = {} ⟶ snd (m s)`). For unspecified hardware primitives (`sfence_impl`, `MachineOps.thy:197–223`), `MachineMonad.thy:42–55` wraps calls in `ignore_failure f ≡ λs. if fst (f s) = {} then ({((),s)}, False) else (fst (f s), False)` specifically to guarantee `empty_fail` and `no_fail ⊤` without extra axioms.
2. **`mit-plv/riscv-coq` `MinimalMMIO.nonmem_load` (`mit-plv/riscv-coq@03881b21...`, `Platform/MinimalMMIO.v:66–73, 175–201`)**:
   - Explicitly conjoins `(exists v, MMIOReadOK n (getLog mach) a (signExtendToReg v))` alongside `(forall v, MMIOReadOK ... -> post v ...)`. Without that existential witness, an unsatisfiable `MMIOReadOK` predicate collapses `forall v` vacuously to `True` and breaks `interpret_action_total`.
3. **`rems-project/islaris` `seq_nb_state` (`rems-project/islaris@c978e10f...`, `theories/opsem.v:450, 478, 489, 515–516`)**:
   - Transitions to `seq_nb_state := true` on trace assumption mismatch, halting `seq_step` (`θ.(seq_nb_state) = false → ...`) as angelically safe; premature `seq_nb_state := true` bugs silently discharge verification obligations.

---

### 4. Bridging Relational ISA Specs to Executable Evaluators and Free Monads

Basis: source + execution + derived

#### 4.1 Bidirectional Soundness and Oracle Surjectivity

Linking an auditable inductive spec `StepRel : S → StepOutcome S → Prop` to a fast executable interpreter `step : S → Oracle → StepOutcome S` requires proving the exact biconditional:
$$\forall (s : S)\;(out : \mathsf{StepOutcome}\;S),\quad \mathsf{StepRel}(s, out) \iff \exists (o : \mathsf{Oracle}),\; \mathsf{step}(s, o) = out.$$

- **Soundness ($\Leftarrow$: `∀ s o, StepRel s (step s o)`)** catches wrong state updates in `step`.
- **Oracle Surjectivity ($\Rightarrow$: `∀ s out, StepRel s out → ∃ o, step s o = out`)** catches **nondeterminism under-approximation**. In **Probe Part 2**, a mutually exclusive sum oracle allowing *either* a speculative TLB fill *or* an interrupt per step (`tag ∈ {0..3}`) satisfies Soundness (`True`) and all sequential tests, yet **fails Surjectivity (`False`)** on states where hardware speculatively fills a TLB entry while `satp` is active and immediately takes a pending timer interrupt before fetching the next U-mode instruction. Factoring `Oracle` as an orthogonal product (`spec_tlb_fill × flush_sbuf × take_irq`) restores `surjective = True` while `o_default = (False, False, False)` yields a deterministic emulator.

#### 4.2 Simulation Flipping, 2-Safety Noninterference, and Free-Monad Event Trees

Externalizing choices into `Oracle` or a `FreeM` event tree resolves three multi-layer verification bottlenecks:

1. **CompCert Forward-to-Backward Flipping (`AbsInt/CompCert@2685140b...`, `common/Smallstep.v:1050–1065, 1863–1890`)**: `forward_to_backward_simulation` requires `determinate L2` (`sd_determ`). Parameterizing transitions by `o : Oracle` makes `L2` deterministic per fixed oracle schedule `os`, flipping forward refinement into backward behavioral inclusion $\forall os,\; \mathsf{Beh}_{L_2}(os) \subseteq \mathsf{Beh}_{L_1}(os)$.
2. **2-Safety Information-Flow Proofs (`seL4/l4v@b0fe7693...`, `RISCV64/MachineOps.thy:115–126`)**: Unaligned Cartesian relational stepping fails 2-safety (`unaligned_cartesian_rel_2safety = False` in **Probe Part 4**) whenever one run takes an interrupt while the other retires an instruction. As `MachineOps.thy:115` documents (*"`getActiveIRQ` is oracle-based and deterministic to allow information flow proofs"*), shared-oracle parameterization reduces noninterference to pointwise equational reasoning: $s_1 \approx_L s_2 \implies \mathsf{step}(s_1, o) \approx_L \mathsf{step}(s_2, o)$ (`shared_oracle_pointwise_2safety = True` across all 576 low-equivalent pairs in **Probe Part 4**), provided `o` is independent of high-domain state (Murray et al., *IEEE S&P 2013*, DOI `10.1109/SP.2013.35`).
3. **Multi-Hart Intra-Instruction Interleaving via Free Monads (`mit-pdos/xv6iris@5cb9df99...`)**: When concurrent harts interleave *mid-instruction* (e.g., between `Sv39` page-walk reads `AK_ttw`), `xv6iris` (`vendor/lean-sail/Sail/ConcurrencyInterfaceV1.lean:1–19, 132–160`; `Sail.lean:44–46`) replaces `lean-sail`'s `EStateM` with `FreeM` over a 17-constructor `Outcome` type (`regRead`, `regWrite`, `memRead`, `memWrite`, `barrier`, `tlbi`, `takeException`, `choose`, ...), interpreting the **identical generated Sail model** both relationally one event at a time in `MachCSL` and executable-sequentially via `PreSailM.interp` for hardware trace conformance (`vtest-lean`, `README.md:170–174`).

## Boundaries

- **Coinductive Infinite-Trace Fairness & Liveness (`not examined`)**: Only finite-prefix safety, refinement, progress, and 2-safety were analyzed; coinductive divergence and weak/strong fairness (`ITree` `eutt` in Rocq or coinductive streams in Isabelle/HOL) were not examined.
- **Exact Compile-Time Crossover for an 800-Rule Flat Lean 4 Inductive (`unknown`)**: While linear/quadratic dead-branch refutation growth in `casesOn`/`noConfusion` is established structurally, controlled memory/heartbeat benchmarks for a full 800-instruction RV64GC+V flat inductive in Lean `v4.34.1` were not run and remain unknown.
- **Forward-to-Backward Simulation Flipping on Unparameterized Nondeterministic Targets (`known not to apply`)**: CompCert's `forward_to_backward_simulation` (`Smallstep.v:1863`) is known not to apply when `L2` has internal unlabelled nondeterminism because `sd_determ` fails directly.
- **Coarse Instruction-Atomic Oracles for Intra-Instruction Multi-Hart Races (`known not to apply` without micro-stepping)**: Instruction-atomic `step : HartState → Oracle → StepOutcome HartState` cannot capture remote stores interleaved *between* two memory sub-accesses of one instruction unless lowered to free-monad event suspensions (`FreeM Outcome`) or per-sub-access oracle snapshots.
- **Direct Kernel `whnf` Reduction of `Std.ExtDHashMap` `lean-sail` State (`unsupported`)**: Lean `v4.34.1`'s kernel explicitly does not reduce `USize`-backed `Std.ExtDHashMap`/`Std.ExtHashMap` operations (`lean-sail@e4745c82...`, `ConcurrencyInterfaceV1.lean:101–105`).

## Evidence

### Primary Git Repository Sources (Observed `2026-11-20`)

- `rems-project/lean-sail` @ `e4745c82fe329f162700020dcd31da6b342473b9`: `Sail/ConcurrencyInterfaceV1.lean:9–26, 62–70, 101–111, 132–177` (`ChoiceSource`, `Access_kind`, `ExtDHashMap`-backed `SequentialState`, `PreSailM := EStateM`); `Sail/Sail.lean:39–71` (`main_of_sail_main`, `whileFuelM`).
- `mit-pdos/xv6iris` @ `5cb9df992c45829f6210b3e4176962d7b7a4c408`: `vendor/lean-sail/Sail/ConcurrencyInterfaceV1.lean:1–19, 131–160` (17-constructor `Outcome` free monad + `PreSailM.interp`); `vendor/lean-sail/Sail/Sail.lean:44–57`; `README.md:24–47, 129–146, 170–174` (`MachCSL` per-event step, `swp` leaf lemmas, `vtest` conformance link).
- `leanprover/LNSym` @ `5c05220ff970e3bdd7813ad0c9ef3741522c8b92`: `Arm/Exec.lean:10–133, 171–178` (`exec_inst`, `stepi`, `run`, `stepi_eq_of_fetch_inst_of_decode_raw_inst`).
- `Verified-zkEVM/riscv-zkvm` @ `6810fc14d9c40373101321cefaec59df8d82e3e7`: `RiscvZkvm/Rv64/Execution.lean:344–348`, `RiscvZkvm/Rv64/SailEquiv/StepRun.lean:77–81, 327–334`, `docs/validation.md:56, 66, 109–137` (`none`-encoded traps, forward `sailStep_run_sim`, `noncomputable` proof extraction).
- `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52`: `src/Lean/Meta/Native.lean:37–86`, `src/kernel/environment.h:20–23`.
- `mit-plv/riscv-coq` @ `03881b21aa36115d436e06b9e1a40836e9b927c7`: `src/riscv/Utility/Monads.v:5–15, 88–197, 202–246, 252–407` (`OState`, `StateND`, `OStateND`, `Post`); `src/riscv/Platform/MinimalMMIO.v:66–80, 96–141, 175–201` (`nonmem_load` existential non-emptiness witness, `interpret_action_total`).
- `rems-project/islaris` @ `c978e10f50db5c40f0fdf113f5f76a779782c6f9`: `theories/opsem.v:63–99, 395–435, 446–520` (`trace_step`, single-constructor `seq_step`, `seq_nb_state`).
- `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`: `riscV/Asm.v:960–1005, 1072–1103` (`exec_instr` + 3-rule `Inductive step`); `common/Smallstep.v:1050–1065, 1863–1890` (`receptive`, `determinate`, `forward_to_backward_simulation`).
- `seL4/l4v` @ `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`: `lib/Monads/nondet/Nondet_Monad.thy:36–149` (`select` vs `state_select`); `spec/machine/MachineMonad.thy:33–78` (`ignore_failure`, `empty_fail`); `spec/machine/RISCV64/MachineOps.thy:18–27, 114–126` (`irq_oracle`-backed `getActiveIRQ`); `lib/Simulation.thy:39–153` (`data_type`, `fw_sim`).
- `HOL-Theorem-Prover/HOL` @ `0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`: `examples/l3-machine-code/riscv/src/riscv.spec`.

### Peer-Reviewed Literature

- Armstrong et al., *"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS"*, PACMPL (POPL 2019), DOI `10.1145/3290384`.
- Bourgeat et al., *"Flexible Instruction-Set Semantics via Abstract Monads (Experience Report)"*, PACMPL (ICFP 2023), DOI `10.1145/3607833`.
- Sammler et al., *"Islaris: Verification of Machine Code Against Authoritative ISA Semantics"*, PLDI 2022, DOI `10.1145/3519939.3523434`.
- Xia et al., *"Interaction Trees: Representing Recursive and Impure Programs in Coq"*, PACMPL (POPL 2020), DOI `10.1145/3371119`.
- Owens, Myreen, Kumar, Tan, *"Functional Big-Step Semantics"*, ESOP 2016 (LNCS 9632), DOI `10.1007/978-3-662-49498-1_23`.
- Cock, Klein, Sewell, *"Secure Microkernels, State Monads and Scalable Refinement"*, TPHOLs 2008 (LNCS 5170), DOI `10.1007/978-3-540-71067-7_16`.
- Klein et al., *"Comprehensive Formal Verification of an OS Microkernel"*, ACM TOCS 32(1), 2014, DOI `10.1145/2560537`.
- Murray et al., *"seL4: From General Purpose to a Proof of Information Flow Enforcement"*, IEEE S&P 2013, DOI `10.1109/SP.2013.35`.
- Pulte et al., *"Promising-ARM/RISC-V: A Simpler and Faster Operational Concurrency Model"*, PLDI 2019, DOI `10.1145/3314221.3314624`.
- Leroy, *"A Formally Verified Compiler Back-end"*, JAR 2009, DOI `10.1007/s10817-009-9155-4`.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-20`)

Save as `/tmp/probe_isa_rel_vs_oracle.py` and run `python3 /tmp/probe_isa_rel_vs_oracle.py`:

```python
#!/usr/bin/env python3
from dataclasses import dataclass
from itertools import product
from typing import FrozenSet, Optional, Set, Tuple

@dataclass(frozen=True)
class State:
    priv: str            # "U" | "S"
    pc: int              # 0 (ADD_IMM), 1 (LOAD_VA0), 2 (SRET)
    reg: int             # 0..3 (bit 0 = low/public, bit 1 = high/secret)
    sbuf: Optional[int]  # weak-memory store buffer to VA 0
    tlb0: bool           # VA 0 leaf translation cached while satp active
    stip: bool           # pending supervisor timer interrupt

@dataclass(frozen=True)
class Outcome:
    kind: str  # "step" | "trap" | "arch_undef"
    state: State
    cause: Optional[int] = None

Oracle = Tuple[bool, bool, bool]  # (spec_tlb_fill, flush_sbuf, take_irq)
ALL_ORACLES: Tuple[Oracle, ...] = tuple(product((False, True), repeat=3))

def step_oracle(s: State, o: Oracle) -> Outcome:
    spec_fill, flush_sb, take_irq = o
    s1 = State(s.priv, s.pc, s.reg, (None if flush_sb else s.sbuf), (s.tlb0 or spec_fill), s.stip)
    if s1.stip and s1.priv == "U" and take_irq:
        return Outcome("trap", State("S", 0, s1.reg, s1.sbuf, s1.tlb0, s1.stip), cause=0x80000005)
    if s1.pc == 0:
        return Outcome("step", State(s1.priv, 1, (s1.reg + 2) % 4, s1.sbuf, s1.tlb0, s1.stip))
    if s1.pc == 1:
        if not s1.tlb0:
            return Outcome("trap", State("S", 0, s1.reg, s1.sbuf, s1.tlb0, s1.stip), cause=13)
        return Outcome("step", State(s1.priv, 2, (s1.sbuf or 0), s1.sbuf, s1.tlb0, s1.stip))
    if s1.pc == 2:
        if s1.priv == "U":
            return Outcome("trap", State("S", 0, s1.reg, s1.sbuf, s1.tlb0, s1.stip), cause=2)
        return Outcome("step", State("U", 0, s1.reg, s1.sbuf, s1.tlb0, s1.stip))
    return Outcome("arch_undef", s1)

def step_oracle_underparameterized(s: State, tag: int) -> Outcome:
    m = {0: (False, False, False), 1: (True, False, False), 2: (False, True, False), 3: (False, False, True)}
    return step_oracle(s, m[tag])

def step_rel_complete(s: State) -> Set[Tuple[str, State, Optional[int]]]:
    return {(out.kind, out.state, out.cause) for o in ALL_ORACLES for out in (step_oracle(s, o),)}

def step_rel_omitted_sret_u(s: State) -> Set[Tuple[str, State, Optional[int]]]:
    return set() if (s.priv == "U" and s.pc == 2 and not s.stip) else step_rel_complete(s)

ALL_STATES = [State(p, pc, r, sb, t, i) for p in ("U", "S") for pc in (0, 1, 2)
              for r in range(4) for sb in (None, 0, 1) for t in (False, True) for i in (False, True)]

bad_inv = lambda st: not (st.priv == "S" and st.pc == 0 and not st.stip and st.reg == 3)
u_sret = State("U", 2, 3, None, True, False)
print(f"[P1.1] States={len(ALL_STATES)}: omitted_rel_vacuous_inv={all(bad_inv(ns) for (_, ns, _) in step_rel_omitted_sret_u(u_sret))} "
      f"(progress={len(step_rel_omitted_sret_u(u_sret)) > 0}) | complete_catches={not all(bad_inv(ns) for (_, ns, _) in step_rel_complete(u_sret))} "
      f"(total_progress={all(step_oracle(st, o).kind in ('step', 'trap') for st in ALL_STATES for o in ALL_ORACLES)})")

full_sound = all((out.kind, out.state, out.cause) in step_rel_complete(st) for st in ALL_STATES for o in ALL_ORACLES for out in (step_oracle(st, o),))
full_surj = all(any((out.kind, out.state, out.cause) == tgt for o in ALL_ORACLES for out in (step_oracle(st, o),)) for st in ALL_STATES for tgt in step_rel_complete(st))
under_sound = all((out.kind, out.state, out.cause) in step_rel_complete(st) for st in ALL_STATES for tg in range(4) for out in (step_oracle_underparameterized(st, tg),))
under_surj = all(any((out.kind, out.state, out.cause) == tgt for tg in range(4) for out in (step_oracle_underparameterized(st, tg),)) for st in ALL_STATES for tgt in step_rel_complete(st))
print(f"[P1.2] Product-oracle: sound={full_sound}, surjective={full_surj} | Mutually-exclusive oracle: sound={under_sound}, surjective={under_surj}")

nondet_select = lambda ch, s: ({(c, s) for c in ch}, False)
nondet_state_select = lambda ch, s: ({(c, s) for c in ch}, len(ch) == 0)
valid_nf = lambda m, s, post: (not m(s)[1]) and all(post(v, s2) for (v, s2) in m(s)[0])
empty_fail = lambda m: len(m(0)[0]) > 0 or m(0)[1]
m_vac, m_chk = (lambda s: nondet_select(frozenset(), s)), (lambda s: nondet_state_select(frozenset(), s))
print(f"[P1.3] select(empty) proves False postcondition={valid_nf(m_vac, 0, lambda v, s: False)}, empty_fail={empty_fail(m_vac)} | "
      f"state_select(empty) proves False={valid_nf(m_chk, 0, lambda v, s: False)}, empty_fail={empty_fail(m_chk)}")

low_eq = lambda a, b: (a.priv, a.pc, a.reg & 1, a.sbuf, a.tlb0, a.stip) == (b.priv, b.pc, b.reg & 1, b.sbuf, b.tlb0, b.stip)
low_pairs = [(a, b) for a in ALL_STATES for b in ALL_STATES if low_eq(a, b)]
sh_2s = all((oa := step_oracle(a, o)).kind == (ob := step_oracle(b, o)).kind and oa.cause == ob.cause and low_eq(oa.state, ob.state) for (a, b) in low_pairs for o in ALL_ORACLES)
un_2s = all(low_eq(na, nb) and ka == kb and ca == cb for (a, b) in low_pairs for (ka, na, ca) in step_rel_complete(a) for (kb, nb, cb) in step_rel_complete(b))
print(f"[P1.4] Low-eq pairs={len(low_pairs)}: shared_oracle_pointwise_2safety={sh_2s} | unaligned_cartesian_rel_2safety={un_2s}")
```

Observed output (`python3 /tmp/probe_isa_rel_vs_oracle.py`, exit code `0`):

```text
[P1.1] States=288: omitted_rel_vacuous_inv=True (progress=False) | complete_catches=True (total_progress=True)
[P1.2] Product-oracle: sound=True, surjective=True | Mutually-exclusive oracle: sound=True, surjective=False
[P1.3] select(empty) proves False postcondition=True, empty_fail=False | state_select(empty) proves False=False, empty_fail=True
[P1.4] Low-eq pairs=576: shared_oracle_pointwise_2safety=True | unaligned_cartesian_rel_2safety=False
```

## Revalidation

1. **Rerun the Equivalence & Vacuity Probe (< 1 s)**: Run `python3 /tmp/probe_isa_rel_vs_oracle.py`; expect exit code `0` and identical `[P1.1]`–`[P1.4]` lines.
2. **Diff `lean-sail` vs. `xv6iris` Free-Monad Interface**: Diff `rems-project/lean-sail` `Sail/ConcurrencyInterfaceV1.lean` (`e4745c82...`) against `mit-pdos/xv6iris` `vendor/lean-sail/Sail/ConcurrencyInterfaceV1.lean` (`5cb9df99...`) to check whether upstream `lean-sail` adopts `FreeM Outcome` or replaces `Std.ExtDHashMap` with a kernel-reducible map.
3. **Audit Any Candidate ISA Specification**: Check (a) an exhaustive `StepOutcome` sum (`.step`, `.trap`, `.halted`, `.archUndefined`), (b) total progress + no-`archUndefined` on the supported envelope + positive trap/IRQ reachability canaries, (c) `empty_fail` / non-emptiness witnesses on every set/CPS choice, and (d) both soundness ($\Leftarrow$) and oracle surjectivity ($\Rightarrow$) when bridging `StepRel` to an executable evaluator.
