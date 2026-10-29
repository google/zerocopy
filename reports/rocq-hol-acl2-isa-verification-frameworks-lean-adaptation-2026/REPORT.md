# Rocq, HOL4, Isabelle/HOL, ACL2, and F* ISA Verification Frameworks and Their Lean 4 Adaptation for Anneal

## Summary

While Lean 4 has an emerging ecosystem of native ISA models (`lean-mlir` / `LNSym` for AArch64 and `sail-riscv-lean` for RISC-V, surveyed in `reports/machine-code-foundations-and-environment-selection-2026/`), the deepest battle-tested solutions for connecting high-level systems/separation-logic specifications to multi-architecture machine code reside in five non-Lean theorem-proving ecosystems: **Rocq** (`rems-project/isla` + `islaris` + `CN2Islaris`, `mit-plv/riscv-coq` + `bedrock2`, `AbsInt/CompCert`, `jasmin-lang/jasmin`), **F\*** (`project-everest/vale`), **ACL2** (`acl2/books/projects/x86isa`), **HOL4** (`HOL/examples/l3-machine-code`, `CakeML/cakeml`, `kth-step/HolBA`), and **Isabelle/HOL** (`seL4/l4v`).

This report presents a primary-source architectural audit of fifteen repositories across those five ecosystems and pairs that audit with a standalone, zero-`sorry`, zero-custom-axiom Lean 4.34.1 mechanization (`support/islaris_trace_and_riscv_typeclass_lean_probe.lean`). Our principal findings are:

1. **Islaris's `seq_nb_state` Path-Assumption Mechanism Has an Inverted Polarity and a Trace-Completeness Soundness Boundary.** In `rems-project/islaris` (`theories/opsem.v:560-591`, `theories/lifting.v:793-832`), SMT solver path guards emitted by Isla (`Smt (Assert e)`) are lowered to `LAssert b`, which transitions to `seq_nb_state := true` when `b = false`. Because `seq_to_val` (`opsem.v:584-591`) classifies any state with `seq_nb_state = true` as a terminated value and `WPasm` (`lifting.v:87-93`) uses the trivial postcondition `{{ _, True }}`, any trace branch whose `Smt (Assert e)` guard evaluates to `false` terminates benignly and satisfies `WPasm` vacuously. Conversely, `Assume e` (`LAssume b`, emitted from `sail_assume`) is a verification obligation that gets stuck when `b = false`. Consequently, if a symbolic trace tree `tcases ts` omits a feasible execution branch of an opcode, `isla_adequacy` (`adequacy.v:91-97`) still succeeds on concrete states taking the omitted branch. Only `islaris/sail-riscv/sail_opsem.v` (`sim_implies_refines`, lines 589–650; `sim_Assert`, lines 1030–1038) closes this gap by proving refinement from a full Sail operational semantics (`step_cpu`) with `seq_nb_state = false` at instruction boundaries.
2. **`CN2Islaris` Automates Source-to-Binary Proof Generation Only Under Non-Recursive DWARF Call-Graph Bounds and Flat 64-Bit Array/Pointer Lowering.** In `rems-project/cerberus` (`branch = CN2Islaris`, `backend/cn/binaryVerification.ml:74-283`, `backend/cn/dwarfData.ml:7-75`), CN separation-logic specifications (`Owned<unsigned long>(p)` and quantified `each (integer j; ...) {Owned(...)}`) are translated into Islaris `bv_unsigned p ↦ₘ v ∗ ⌜bv_unsigned p < 2 ^ 52⌝` assertions with an 8-byte alignment side condition recovered from `IT.Good`, and discharged per function via Lithium (`liARun; Unshelve. all: prepare_sidecond. all: try bv_solve`). However, stack bounds are computed by `dwarfData.get_max_stack_depth` (`dwarfData.ml:49-71`) as `max_call_depth * 128` over a static `objdump` call graph that diverges on recursive functions.
3. **`mit-plv/riscv-coq`'s Typeclass-Parameterized Execution Monad Cleanly Decouples Instruction Semantics from Value Provenance and Memory/MMIO Models.** By separating pure decoding (`Decode.v:1483-1529`) from a monadic execution interpreter (`Execute.v`, `ExecuteI.v`) parameterized over `RiscvProgram M t`, `RiscvProgramWithLeakage M t`, and `RiscvMachine M t` (`Machine.v:35-86`) and connected to weakest preconditions via `PrimitivesParams M Machine` (`Primitives.v:27-184`), `riscv-coq` runs the exact same instruction semantics over deterministic state (`OState`), non-deterministic MMIO (`OStateND`), free-monad action traces (`MinimalMMIO.v:131-165`), and constant-time leakage accumulators (`LeakageOfInstr.v`).
4. **Across the Five Hard ISA Formalization Problems, Non-Lean Frameworks Converge on Distinct Architectural Trade-Offs.** Our comparative matrix across CompCert, Jasmin, Vale, ACL2 `x86isa`, HOL4 `L3` / `CakeML` / `HolBA`, `riscv-coq` / `bedrock2`, `Islaris`, and `seL4 l4v` isolates the exact representation choices for (i) partial registers and sub-word aliasing (`MSB_CLEAR` vs. `MSB_MERGE`), (ii) undefined status flags (`Vundef` / `rflagv.Undef` vs. opaque havoc vs. state-monadic `undef-flg` seed), (iii) block+offset provenance vs. flat byte maps (`Pallocframe` vs. linear stack region + validity predicates), (iv) instruction-cache coherence (`xAddrs` invalidation vs. `CODE_POOL` separation), and (v) system-mode page tables (`app-view` vs. `sys-view` state-mutating reads in ACL2 `x86isa`).
5. **Anneal Can Combine Both Paradigms in Lean 4 Under `Trusted/Refinement.lean`.** In `support/islaris_trace_and_riscv_typeclass_lean_probe.lean`, we mechanize a `riscv-coq`-style typeclass `IsaMachineM` instantiated over both a CompCert/Anneal-style provenance machine (`ProvMachine`) and a flat word/byte machine (`FlatMachine`), prove universal load simulation (`prov_to_flat_load64_simulation`) plus a cross-block spatial provenance negative control (`forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat`), and build an `IslaTrace`-to-`StepResult` adequacy bridge (`islaTrace_refines_stepResult`) alongside a machine-checked negative control (`incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator`) demonstrating why Anneal's trace lifter must enforce `ValidCompleteTraceAt`.

## Applicability

This report applies directly to the Anneal trusted verification kernel and its planned inline-assembly and binary-level verification pipeline in `google/zerocopy`:

| Anneal Component / Subsystem | Relevant Findings & Architectural Impact |
| :--- | :--- |
| `trusted/lean/Trusted/StepResult.lean` (`Error`, `StepResult`) & `Trusted/Refinement.lean` (`StepResult.Refines`, `Partial`, `FnSpec`) | Defines the target semantic interface into which ISA instruction steps (`stepProv`, `stepFlat`) and symbolic trace lifters (`IslaTrace`) must embed. Shows how `.failed .ub` absorbs provenance violations, uninitialized flag reads (`RFlagVal.undef`), and violated `sail_assume` obligations (`sailAssume false`), while `.failed .unsupported` models I-cache incoherence (`xAddrs` misses) without unsoundly refining arbitrary target behavior. |
| `trusted/lean/Trusted/Memory.lean` (`AllocId`, `Allocation`, `Memory.readBytes`, `Memory.writeBytes`) & `Trusted/MirSemantics.lean` | Explains how to bridge Anneal's `AllocId`-indexed MIR memory model to flat assembly addresses without adopting CompCert's synthetic `Pallocframe`/`Pfreeframe` pseudo-instructions: keep `IsaVal.ptr allocId ofs` in `ProvMachine` at the MIR-to-inline-ASM boundary and erase to `FlatMachine` via a `LoadRelated`-style block layout invariant (`prov_to_flat_load64_simulation`). |
| Multi-architecture inline assembly support (`aarch64`, `x86_64`, `riscv64`) | Provides concrete Lean 4 designs for Jasmin-style partial-register write descriptors (`MsbFlag.clear` vs. `MsbFlag.merge`), CompCert/Jasmin flag undefness (`RFlagVal.def` vs. `RFlagVal.undef`), and `riscv-coq`-style `xAddrs` instruction-cache invalidation. |
| Automated proof generation via Lithium / symbolic trace lifting | Specifies the exact Trusted Computing Base (TCB) gates required if Anneal imports Isla-generated symbolic traces or CN2Islaris-style Lithium automation: every imported trace must either be accompanied by a `sail-riscv`-style `ValidCompleteTraceAt` theorem or be generated by a verified Lean 4 symbolic evaluator over the ground ISA monad. |

## Findings

### 1. Isla, Islaris, and CN2Islaris: Symbolic Trace Lifting and Its Soundness Boundaries

#### 1.1 The Isla JIB-to-Trace Symbolic Execution Pipeline

The `rems-project/isla` symbolic executor (`e9b5d945394277656593a0d429466d7fa0a2b4b3`) does not execute raw Sail syntax directly; instead, `isla-sail/jib_ir.ml` (lines 29–105) compiles Sail specifications into a flat C-like intermediate representation called **JIB** (`instr_aux` with 14 constructors including `I_decl`, `I_init`, `I_jump`, `I_goto`, `I_copy`, `I_funcall`, `I_return`, `I_throw`, `I_try_block`, and `I_end`).

When `islaris` invokes Isla to lift an instruction opcode into Rocq (`islaris/frontend/isla_lang_if.ml:32-47`), it executes:

```text
isla-footprint -A <arch.ir> -C <config.toml> -i "<opcode_byte_pattern>" -s -x --simplify --simplify-registers --tree
```

Inside `isla/src/footprint.rs` (`isla_main`, lines 577–718), Isla initializes a symbolic machine state, looks up `zisla_footprint` (or `zisla_footprint_no_init` when `-x` / `partial-state` is enabled), spawns concurrent symbolic execution tasks (`executor::start_multi`, lines 663–674) backed by Z3 (`Solver<B129>`), collects all feasible execution paths (`EvPath`), folds them into a prefix-shared `EventTree` (`event_tree::from_shortest_prefix` when `--tree` is passed, lines 702–713), runs SMT and register-write simplifications (`simplify::simplify_event_tree`, lines 691–699), and serializes the tree in the `isla-lang` grammar (`rems-project/isla-lang`, commit `db2ba552ba4b26fabbff27d5ad806d38ecce9bd6`, `coq/isla_lang.v:139-179`):

```coq
Inductive tr : Set :=
  | TreeTrace : list event -> tr_cases -> tr
with tr_cases : Set :=
  | Cases : list tr -> tr_cases
  | End : tr_cases.
```

#### 1.2 Aggressive Event Stripping in the `islaris` OCaml Frontend

Before writing out a `.v` file, the `islaris` OCaml frontend (`rems-project/islaris`, commit `c978e10f50db5c40f0fdf113f5f76a779782c6f9`, `frontend/decomp.ml:74-88` and `frontend/isla_lang_if.ml:64-71`) applies three trace-pruning filters that are **unverified** in standard AArch64 and RISC-V Islaris workflows:

1. **Architectural Ignored Registers (`frontend/arch.ml:71-100`, `frontend/decomp.ml:74-77`):** Every `AssumeReg`, `ReadReg`, and `WriteReg` touching a register in `arch_ignored_regs` is silently deleted (`None`). On AArch64 (`arch.ml:71-90`), `arch_ignored_regs` strips 16 architectural registers: `SEE`, `__v85_implemented`, `__v83_implemented`, `__highest_el_aarch32`, `CurrentEL`, `LookUpSP_EL0`, `SPSel`, `PendingPhysicalSError`, `SCTLR_EL1`, `RVBAR_EL1`, `VBAR_EL1`, `EDSCR`, `OSLSR_EL1`, `MDSCR_EL1`, `PSTATE.D`, and `PSTATE.BTYPE`. On RISC-V (`arch.ml:94-100`), it strips `nextPC`.
2. **Concrete `ReadReg` Deletion (`frontend/decomp.ml:75`):** Any `ReadReg(r, l, v, a)` whose value `v` is concrete (`not (is_symbolic v)`) is stripped from the trace! The frontend assumes that concrete register reads were already fixed by Isla's initial `-C <config.toml>` assumptions (`frontend/isla_lang_if.ml:64-71`, which deletes the entire initial event segment up to `Cycle`).
3. **Mid-Segment `Smt (Assert _)` Deletion (`frontend/decomp.ml:79`):** Inside any `TreeTrace(es, ts)` node, `List.filteri` retains `Smt(Assert(_), _)` **only at index `i = 0`** (`| Smt(Assert(_), _) -> i = 0`) and drops any `Smt(Assert(_), _)` occurring at `i > 0`! This relies on an implicit invariant of `isla-footprint --tree` that every branch condition is hoisted to the very first event (`i = 0`) of each `Cases` child.

#### 1.3 Inverted Polarity of `Smt (Assert e)` vs. `Assume e` and the `seq_nb_state` Completeness Trap

In `islaris/theories/opsem.v` (lines 476–591) and `islaris/theories/lifting.v` (lines 87–93, 369–387, 793–832), the operational semantics of `isla-lang` traces over machine state `seq_local_state` (`record { seq_nb_state : bool; seq_regs : reg_map; seq_pc_reg : string; seq_instrs : gmap bv trace }`) gives **opposite verification polarities** to `Smt (Assert e)` and `Assume e`:

| `isla-lang` Event Constructor | `opsem.v` Label | Operational Transition (`seq_step`, `opsem.v:560-568`) | Iris WP Rule (`lifting.v:793-832`) | True Semantic Role |
| :--- | :--- | :--- | :--- | :--- |
| `Smt (Assert e) a` | `LAssert b` | `if b then mret (es, σ, []) else mret (es, set seq_nb_state (λ _, true) σ, [])` | `wp_assert`: `(⌜b = true⌝ -∗ WPasm es) ⊢ WPasm (Smt (Assert e) a :t: es)` | **Path assumption** (from SMT branch condition). False guard sets `seq_nb_state := true` and gives the prover `⌜b = true⌝` as a hypothesis. |
| `Assume e a` | `LAssume b` | `guard (b = true);; mret (es, σ, [])` | `wp_assume`: `(⌜v = Val_Bool true⌝ ∗ WPasm es) ⊢ WPasm (Assume e a :t: es)` | **Verification obligation** (from `sail_assume` constraint). False guard gets **stuck** in `seq_step` and forces the prover to prove `⌜v = Val_Bool true⌝`. |

Why does `wp_assert` allow the user to *assume* `⌜b = true⌝` when `LAssert false` steps to `seq_nb_state := true`? The mechanism is in `seq_to_val` (`islaris/theories/opsem.v:584-591`) and `wp_asm_def` (`islaris/theories/lifting.v:87-93`):

```coq
Definition seq_to_val (e : seq_expr) : option seq_val :=
  if bool_decide (e.(seq_nb_state) = true) then
    Some (HaltedVal, e.(seq_trace))
  else
    None.

Definition wp_asm_def (t : trace) : iProp Σ :=
  ∀ P, spec_trace P -∗
  WP {| seq_trace := t; seq_regs := ∅; seq_nb_state := false |} {{ _, True }}.
```

Because `seq_to_val` returns `Some (HaltedVal, ...)` as soon as `seq_nb_state = true`, Iris's adequacy theorem (`isla_adequacy` in `islaris/theories/adequacy.v:91-97`) treats any configuration with `seq_nb_state = true` as a **successfully terminated value** (`not_stuck` holds automatically for values), and `wp_asm_def` instantiates the Iris postcondition with `{{ _, True }}` (`lifting.v:376`: `by apply wp_value`).

**The Completeness Soundness Boundary:** Because `seq_nb_state = true` is treated as benign termination, `isla_adequacy` guarantees safety **only across paths that are actually present and satisfiable in the `tcases` trace tree**. If an instruction trace `tcases ts` omits a feasible execution path (for example, if Isla's `-C <config.toml>` over-constrains a register, or if a branch of `Cases` is pruned or has a contradictory `Smt (Assert e)` guard), then on a concrete machine state that takes that omitted path, every branch in `tcases` hits `LAssert false` (or `ReadReg` mismatch, `opsem.v:546-550`), transitions to `seq_nb_state = true`, and terminates benignly—satisfying `isla_adequacy` even if the real hardware executes an unverified branch or crashes!

#### 1.4 How `islaris/sail-riscv` Closes the Gap via End-to-End Sail Refinement

The only component of `islaris` that closes this trace-completeness gap in Rocq is the `sail-riscv` directory (`islaris/sail-riscv/sail_opsem.v`, lines 589–650 and 965–1120; `islaris/sail-riscv/memcpy.v`, lines 65–85; also updated on branch `sail-riscv-update` at commit `16fa62eb13253f16b0bd82e17d1a5f7da88181ec`). In `sail-riscv/sail_opsem.v`:

- `sail_module` wraps the Coq-extracted Sail RISC-V sequential operational semantics (`step_cpu` in `sail-riscv/RV64.v`).
- `sim_expr` (`sail_opsem.v:965-1002`) defines an explicit simulation relation between the Sail monad `M val` and an `isla-lang` trace `t`.
- Crucially, `sim_Assert` (`sail_opsem.v:1030-1038`) requires the Sail side to **prove** that the `Smt (Assert e)` guard evaluates to `true` on the chosen `tcases` branch:
  ```coq
  Lemma sim_Assert m e a t (H1 : eval_exp e = Some (Val_Bool true)) :
    sim_expr m t →
    sim_expr m (Smt (Assert e) a :t: t).
  ```
- And `sim_implies_refines` (`sail_opsem.v:602-650`) proves trace refinement (`trefines (sail_module instrs) (isla_Pipeline_module instrs)`) starting and ending every instruction step with `seq_nb_state := false`. Thus, any omitted branch in `tcases` makes `sim_Cases` (`sail_opsem.v:1012-1018`) unprovable.

#### 1.5 How `CN2Islaris` Translates C/CN Separation Logic to Islaris Binary Proofs

We inspected both `rems-project/CN2Islaris` (`f34f9a2f0a9b75a6b342aa966d0d14daca58c466`) and its companion Cerberus compiler backend `rems-project/cerberus` (`branch = CN2Islaris`, commit `3bdd8cb8e2805d46c22725d7651a2ed90b012837`, `backend/cn/binaryVerification.ml`, `backend/cn/binaryVerificationTypes.ml`, and `backend/cn/dwarfData.ml`):

1. **DWARF + `objdump` Binary Metadata Extraction (`cerberus/backend/cn/dwarfData.ml:7-75`):**
   - `get_function_addresses` (`dwarfData.ml:7-31`) shells out to `read-dwarf <elf_file>` to extract low/high PC addresses for each C function and to `aarch64-none-elf-objdump -d <elf_file>` to identify the return instruction address (`ret` at `high_pc - 4`).
   - `get_max_stack_depth` (`dwarfData.ml:42-71`) parses `bl <addr> <callee>` instructions from `objdump -d` to build a static call graph and recursively computes `(1 + max_callee_depth) * 128` bytes. Line 49 explicitly notes: `(* Currently non-terminating for recursive functions (as expected) *)`.
2. **CN-to-Islaris Resource and Term Lowering (`cerberus/backend/cn/binaryVerification.ml:74-283`):**
   - **Pointers and `Owned<T>` (`binaryVerification.ml:194-209`):** A CN point-to resource `P { name = Owned (_, init); pointer; iargs }` is lowered to `bv_unsigned <ptr> ↦ₘ <val> ∗ ⌜bv_unsigned <ptr> < 2 ^ 52⌝` (supporting only initialized 8-byte `unsigned long` values; uninitialized `Uninit` or struct resources raise `Failure "Translate of resource ... not yet implemented"` at line 209).
   - **8-Byte Alignment Recovery (`binaryVerification.ml:136-143`):** CN's typing/value invariant `IT.Good (Pointer _, ptr)` is translated to the bitvector divisibility proposition `(bv_unsigned <ptr> `mod` 8 = 0)%Z`.
   - **Quantified Arrays (`binaryVerification.ml:210-264`):** A CN iterated resource `Q { name = Owned (_, Init); pointer; q = (q_sym, _); step; permission; ... }` with step size `8` and bounds `0 <= j && j < N` is translated into Islaris's contiguous array points-to connective:
     ```coq
     bv_unsigned base ↦ₘ∗ xs ∗ ⌜bv_unsigned N = Z.of_nat (length xs)⌝ ∗ ⌜(bv_unsigned base + 8 * bv_unsigned N < 2 ^ 52)%Z⌝
     ```
     and index accesses `v[idx]` become `( xs !! (Z.to_nat (bv_unsigned idx)) )` (`binaryVerification.ml:85-95`).
3. **Lithium Proof Script Generation (`binaryVerification.ml:694-755` and `CN2Islaris/proofs/*/*.v`):**
   - For each function and each optimization level (`-O0`, `-O1`, `-O2` in `CN2Islaris/examples/Makefile:1-90`), `binaryVerification.ml` emits an `<fn>_spec.v` file defining the AArch64 AAPCS64 calling-convention wrapper (`reg_col := [ (cn_addr "R0" :: ... :: sys_regs_aarch64) ]`) and a `<fn>_sal.v` (or `<fn>.v`) file that unfolds instruction traces and runs Islaris's Lithium proof automation engine:
     ```coq
     liARun.
     Unshelve. all: prepare_sidecond.
     all: try bv_solve.
     ```
   - Across the six benchmark programs (`incr_unsigned.c`, `incr_decr.c`, `incr_mem_sub.c`, `conditional.c`, `array_read.c`, `array_write.c`), Lithium discharges straight-line and conditional `-O0`/`-O1`/`-O2` AArch64 assembly automatically, with manual arithmetic hints required only for signed/unsigned bitvector modulo side conditions.

---

### 2. `mit-plv/riscv-coq` and `bedrock2`: Typeclass-Parameterized Monadic ISA Architecture

We inspected `mit-plv/riscv-coq` (`45dc8dfc17c77aabb433355b9d39edc6bfd429ae`) and `mit-plv/bedrock2` (`757f17c6083bf8d43b5293a0db545c8d0aa32a13`) to analyze how a single RISC-V specification serves multiple verification backends without duplicating instruction semantics.

#### 2.1 Pure Decoding vs. Typeclass-Parameterized Monadic Execution

`riscv-coq` splits instruction processing into two strictly separated layers:

1. **Pure Bitvector Decoding (`src/riscv/Spec/Decode.v:1483-1529`):**
   `decode (iset : InstructionSet) (inst : Z) : Instruction` is a pure total function dispatching across 18 modular sub-ISA extensions (`I`, `M`, `A`, `F`, `D`, `CSR`, `Zicsr`, `Zifencei`, `I64`, `M64`, `A64`, `F64`, `D64`, plus RV32/RV64 compressed `C` extensions). If an opcode is invalid or matches multiple overlapping decoders (`length results > 1`), `decode` deterministically returns `InvalidInstruction inst` without side effects.
2. **Three-Tier Typeclass Execution Interface (`src/riscv/Spec/Machine.v:35-86`):**
   Instruction execution (`src/riscv/Spec/Execute.v` and `ExecuteI.v`) is written once as a generic monadic function `execute (inst : Instruction) : M unit` constrained only by:
   - `RiscvProgram (M : Type -> Type) (t : Type)` (`Machine.v:35-65`): provides `getRegister`, `setRegister`, `loadByte`/`loadHalf`/`loadWord`/`loadDouble`, `storeByte`/`storeHalf`/`storeWord`/`storeDouble`, `makeReservation`/`clearReservation`/`checkReservation`, `getCSRField`/`setCSRField`, `getPC`/`setPC`, `endCycleNormal`, and `endCycleEarly : forall A, M A`.
   - `RiscvProgramWithLeakage M t` (`Machine.v:69-71`, used in `Spec/LeakageOfInstr.v`): extends `RiscvProgram` with `leakEvent : option LeakageEvent -> M unit` to record branch outcomes and memory addresses for constant-time cryptography proofs without altering functional semantics.
   - `RiscvMachine M t` (`Machine.v:73-86`): extends `RiscvProgramWithLeakage` with `getPrivMode`, `setPrivMode`, `fence`, `flushTLB`, and `translate (isWrite : bool) (isExec : bool) (vaddr : t) : M t`.

#### 2.2 Pluggable Monad Instantiations and Weakest-Precondition Lifting (`Primitives.v`)

Because `Execute.v` depends only on `RiscvMachine M t`, `riscv-coq` instantiates `M` over five distinct monads in `src/riscv/Utility/Monads.v` and `FreeMonad.v`:

- `OState S A := S -> (option A) * S` (`Monads.v:72-95`, used by `Platform/Minimal.v`) for deterministic partial execution.
- `OStateND S A := S -> (option (A * S) -> Prop)` (`Monads.v:217-245`, used by `Platform/MinimalNoMul.v`) for angelic/demonic relational non-determinism.
- `Post S A := S -> (A -> S -> Prop) -> Prop` (`Monads.v:331-355`) for direct predicate-transformer semantics.
- `free riscv_primitive primitive_result` (`Utility/FreeMonad.v:10-45`, used by `Platform/MinimalMMIO.v:131-165`): represents each instruction as a finite free-monad interaction tree of primitive machine actions, interpreted via `interp_action` (`MinimalMMIO.v:150-165`). In `MinimalMMIO.v`, memory is partitioned into RAM (`mem : map.map word byte`) and MMIO addresses (`isMMIOAddr : word -> Prop` with `map.undef_on mach.(getMem) isMMIOAddr`), where loads/stores in `isMMIOAddr` append `MMInput`/`MMOutput` events to `getLog : list LogItem`.

To connect these monads to separation-logic proofs in `bedrock2`, `src/riscv/Spec/Primitives.v` (lines 27–184) defines:

```coq
Class PrimitivesParams (M: Type -> Type) (Machine: Type) := {
  Monad_M :: Monad M;
  RiscvProgram_M :: RiscvProgram M word;
  RiscvMachine_M :: RiscvMachine M word;
  mcomp_sat: forall {A: Type}, M A -> Machine -> (A -> Machine -> Prop) -> Prop;
  is_initial_register_value: word -> Prop;
  nonmem_load: HList.tuple byte 1 -> LogItem -> Prop;
  ...
}.
```

The `Primitives` class (`Primitives.v:44-184`) then axiomatizes the weakest-precondition contracts of each primitive (`spec_Bind`, `spec_Return`, `spec_getRegister`, `spec_loadWord`, `spec_storeWord`, `spec_step`) in terms of `mcomp_sat`, allowing `bedrock2` (`compiler/src/compiler/FlatToRiscvCommon.v:251-283` and `Pipeline.v:112-195`) to prove compiler correctness generically over any `PrimitivesParams` instance!

---

### 3. Comparative Synthesis Across the Five Hard ISA Formalization Problems

To evaluate how Anneal should model architectural corner cases in Lean 4, we audited how nine non-Lean frameworks solve the five hardest ISA formalization problems.

| Framework (Prover) | (1) Partial Registers & Sub-Word Aliasing | (2) Undefined / Underspecified Flags | (3) Memory Provenance vs. Flat Byte Map | (4) I-Cache Coherence & Self-Modifying Code | (5) System-Mode Virtual Memory & Page Tables |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **CompCert** (`Rocq`, `e26caf9f`) | Full registers only (`Pregmap.t val` in `x86/Asm.v:55`, `aarch64/Asm.v:72`, `riscV/Asm.v:83`); sub-word operations modeled as explicit `Val.zero_ext` / `Val.sign_ext` / `Val.loword` on full register values. | Each flag (`ZF`, `CF`, `PF`, `SF`, `OF`) is an independent `preg` in `Pregmap.t val` holding `Vint 0`, `Vint 1`, or `Vundef` (`x86/Asm.v:45-48`). `compare_ints` sets `PF <- Vundef` (`x86/Asm.v:440`); `nextinstr_nf` clobbers all 5 flags to `Vundef` (`x86/Asm.v:562-564`). | **Block+offset provenance (`Vptr b ofs`)** and 2-stage permissions (`Max`/`Cur`) preserved all the way to `Asm.v` (`common/Values.v:34-40`, `common/Memory.v:57-68`). Requires synthetic `Pallocframe` / `Pfreeframe` pseudo-instructions (`x86/Asm.v:949-976`, `riscV/Asm.v:380-403`). | Code lives in an immutable global `code` list inside `Genv.t` (`fn_code : code`), completely disjoint from data `Mem.mem`; self-modifying code is unrepresentable. | User-mode only; no page tables or TLB. |
| **Jasmin** (`Rocq`, `6c4994d5`) | Every instruction descriptor carries `id_msb_flag : msb_flag` (`MSB_CLEAR` vs `MSB_MERGE` in `proofs/arch/arch_decl.v:279-283`, `714-750`). On x86-64 (`x86_instr_decl.v:397-399`), `sz <= U16` uses `MSB_MERGE` (preserving upper bits via `wand old (wshl (-1) (wsize_bits sz))`), while `U32`/`U64` uses `MSB_CLEAR` (zeroing upper bits). | `rflagv := Def bool \| Undef` (`arch_decl.v:555`). Total semantics computes `undefined_flag : bool` (`x86_instr_decl.v:281`), and `arch_sem.v:378-389` filters outputs via `id_init : seq safety_cond` to `Undef`. Reading `Undef` in `st_get_rflag` (`arch_sem.v:244-245`) returns `Error ErrAddrUndef` (`undef_error`). | **Flat word pointers (`PointerW`)** over byte map `coreMem` (`proofs/lang/memory_model.v:78-90, 894-950`). Stack is a linear region `[stack_limit, stack_root)` with `frames : seq pointer` (`memory_model.v:896-930`), verified via `validw` and `stack_stable` (`stack_alloc.v`). | Code resides in structured program AST (`p_funcs`); memory `mem` holds only data and stack frames. | User-mode cryptographic routines only. |
| **Vale** (`F*`, `bbae0eb8`) | `reg_64 = int_between 0 16` (`fstar/specs/hardware/X64.Machine_s.fst:62`); sub-register slices modeled via `ins_MovBe64` / explicit bitmasks over `nat64`. | Uninterpreted `assume val havoc : state -> a -> nat64` (`fstar/specs/hardware/X64.Semantics_s.fst:52`); instructions update `s.flags` with `havoc s ins` before writing defined `cf` (bit 0) and `overflow` (bit 11) (`X64.Semantics_s.fst:121-156`). | Flat map `mem : Map.t int nat8` paired with taint map `memTaint : Map.t int taint` (`X64.Semantics_s.fst:45-48`) for constant-time leakage verification. | Structured `va_code` AST (`Block`, `IfElse`, `While`); instruction bytes are not fetched from `mem`. | User-mode only. |
| **ACL2 `x86isa`** (`ACL2`, `9df88e94`) | Full 64-bit signed integer array `rgfi` (`state.lisp:186-195`). `rr08`/`wr08` (`register-readers-and-writers.lisp:197-355`) decode legacy high bytes `AH`/`CH`/`DH`/`BH` when `rex = 0` and `reg >= 4` using `(part-select ... :low 8 :width 8)` and `(part-install ... :low 8 :width 8)`. `wr16` uses `part-install :low 0 :width 16`; `wr32` writes `(n32 val)` zeroing bits 32..63 (`lines 439-530`). | State carries `:undef` seed (`state.lisp:243-246`). `(undef-flg x86)` (`register-readers-and-writers.lisp:1649-1672`) calls `(undef-read x86)` (`other-non-det.lisp:71-75`), which increments `:undef` and passes the old seed + `rip` to uninterpreted `(undef-read-logic ...)`. `write-user-rflags` (`lines 1701-1787`) calls `!flgi-undefined` for every set bit in `undefined-mask`. | Flat byte-addressed linear/physical memory (`mem` in `state.lisp:215-235`, `top-level-memory.lisp:120-250`). | Fetches instruction bytes directly from `mem` via `rb` (`top-level-memory.lisp`) without a separate I-cache buffer; self-modifying stores take effect immediately. | **Dual-mode switch `(app-view x86)`** (`state.lisp:248-250`, `top-level-memory.lisp:224-250`, `paging.lisp:58-250`). In `app-view`, `rme*` is a pure read of `2^48` linear memory (`(equal (mv-nth 2 (rme* ...)) x86)`). In `sys-view` (`(not (app-view x86))`), `ia32e-la-to-pa` walks 4-level IA-32e page tables in physical memory and **writes accessed/dirty (`A`/`D`) bits into `:mem`**, so memory reads mutate `x86`! |
| **HOL4 `L3` (`l3-machine-code`)** (`HOL4`, `d73e6036`) | Generated from Fox's L3 DSL into `wordsTheory` bitvectors (`w2w`, bit-field extracts `(h >< l) w`). | Individual `bool option` flag fields (`SOME b` vs `NONE` for unpredictable/undefined flags). | Flat word-to-byte map split by `SELECT_STATE m y s` (`examples/l3-machine-code/common/stateScript.sml:45-120`) into domain `y` and frame. | `CODE_POOL instr c` (`stateScript.sml:148-154`) embeds instruction encodings into the read-only state projection so data writes outside `c` are frame-disjoint from code. | Architecture-dependent (modeled in `arm8` system specs, omitted in user-mode Hoare triples). |
| **CakeML `asmSem`** (`HOL4`, `665f9b21`) | Target-agnostic `reg : num -> word` of architecture word width (`'a word` in `compiler/encoders/asm/asmSemScript.sml:19-30`); sub-word operations restricted to memory `MemLoadByte` / `MemStoreByte`. | **Eliminates status flags at the IR boundary:** `asm` (`compiler/encoders/asm/asmScript.sml:21-96`) fuses compare-and-branch into `JumpCmp cmp r ri addr` and writes carry/overflow directly to general registers in `AddCarry r1 r2 r3 r4` and `AddOverflow` (`asmSemScript.sml:95-125`). | Flat byte map `mem : 'a word -> word8` with explicit valid address domain `mem_domain : 'a word set` (`asmSemScript.sml:22-24, 52-75`). | Code lives in target `bytes_in_memory` predicate checked by encoder target proofs; `mem_domain` excludes code addresses during data execution. | User-mode only (`mem_domain`). |
| **HolBA `BIR`** (`HOL4`, `ef22c1fd`) | Untyped/sized `bir_imm_t` (`Bit1`..`Bit128`) stored in `bir_var_environment_t` (`src/theory/bir/bir_programScript.sml:83-89`); sub-word updates lowered to bitfield expressions during lifting. | Underspecified flags lifted to explicit `BStmt_Assign` with symbolic/arbitrary expressions or `BStmt_Assert` / `BStmt_Assume` (`bir_programScript.sml:36-41, 264-278`). Note that BIR uses **standard** polarity: `BStmt_Assume false` transitions to `BST_AssumptionViolated`, whereas `BStmt_Assert false` transitions to `BST_AssertionViolated`. | Flat finite map `mmap : num \|-> num` (`src/theory/bir/bir_exp_memScript.sml:15-30`) with endian-aware splitting (`bir_number_of_mem_splits_def`, lines 62–71). | Lifts concrete binary basic blocks to `BirProgram` (`bir_block_t list` indexed by `BL_Address bir_imm_t`, `bir_programScript.sml:16-68`), checked by HOL4 lifting theorems (`bir_lifting_machinesTheory`). | User-mode binary analysis only. |
| **`riscv-coq` & `bedrock2`** (`Rocq`, `45dc8dfc` / `757f17c6`) | RISC-V has only full XLEN registers (`x1`..`x31`, `x0 = 0`); sub-word operations occur only at memory loads/stores (`loadByte`, `loadHalf`, `loadWord`, `ExecuteI.v:65-160`). | RISC-V has no condition-code flag register; branches compare two GPRs directly (`Beq`, `Bne`, `Blt`, `Bge`, `Bltu`, `Bgeu` in `ExecuteI.v:35-60`). | **Flat byte map `map.map word byte`** (`Platform/RiscvMachine.v:25`, `bedrock2/compiler/src/compiler/FlatToRiscvCommon.v:96-113`). Stack allocation simply decrements `sp` in flat memory (`FlatToRiscvCommon.v:146-197`) with no synthetic `Pallocframe` instruction. | **Explicit `xAddrs : list word`** (`RiscvMachine.v:23-50`, `Minimal.v:47-56`). `Fetch` checks `isXAddr4B pc xAddrs`; every `storeN` calls `invalidateWrittenXAddrs` removing written addresses from `xAddrs` until resynchronized! | `RiscvMachine.translate` hook (`Machine.v:84`) and `flushTLB` (`Machine.v:85`). |
| **`seL4 l4v` (AArch64)** (`Isabelle/HOL`, `7b8c0990`) | `user_regs = register => machine_word` (`spec/machine/AARCH64/MachineOps.thy:150-170`) plus `user_fpu_state` and banked `vcpu_regs` (`MachineOps.thy:361-371`). | Condition flags inside `SPSR_EL1` modeled as opaque `machine_word` in `user_context` (`MachineOps.thy:150-164`). | Flat word-aligned `underlying_memory : machine_word => word8` (`MachineOps.thy:36-48`), lifted to typed kernel objects (`kheap`) in `ArchVSpace_A.thy`. | Hardware cache/pipeline operations (`isb`, `dsb`, `cleanByVA_PoU`, `invalidateCacheRange_I`, `invalidate_I_PoU` in `MachineOps.thy:380-456`) wrapped via `machine_op_lift` over opaque `machine_state_rest`. | **Two-stage AArch64 ASID + VMID page tables** (`spec/abstract/AARCH64/ArchVSpace_A.thy:34-217`), with explicit TLB maintenance obligations (`invalidate_tlb_by_asid`, `invalidate_tlb_by_asid_va`, `setVSpaceRoot`). |

#### 3.1 Key Comparative Insights for Anneal

1. **Why CompCert Preserves `Vptr block ofs` to `Asm.v` While `bedrock2` and `Jasmin` Use Flat Words:**
   CompCert's compiler passes rely on non-aliasing between distinct allocations (`b1 <> b2`), including the current function's stack frame and caller/callee memory. Because `Mem.alloc` creates a fresh abstract `block`, CompCert's assembly semantics (`x86/Asm.v:949-976`, `aarch64/Asm.v:850-885`, `riscV/Asm.v:380-403`) cannot execute a real `sub rsp, #sz` instruction to allocate a stack frame; instead, it executes a synthetic `Pallocframe sz ofs_ra ofs_link` instruction that calls `Mem.alloc`. By contrast, **Jasmin** (`proofs/lang/memory_model.v:894-950` and `proofs/compiler/stack_alloc.v`) and **`bedrock2`** (`FlatToRiscvCommon.v:146-197`) execute real `sub rsp, #sz` / `addi sp, sp, -sz` instructions over a flat address space by maintaining an explicit linear stack region `[stack_limit, stack_root)` and proving non-aliasing from address arithmetic (`validw`, `stack_stable`, and separation-logic `ptsto_bytes` disjointness).
   - **Lesson for Anneal:** Anneal's MIR semantics (`Trusted/Memory.lean`) already uses `AllocId`-indexed allocations (`Allocation`), which matches `ProvMachine` in our Lean probe. At the inline-assembly boundary, Anneal should **not** introduce synthetic `Pallocframe` instructions; instead, inline assembly blocks should operate either in `ProvMachine` (when pointers are passed in registers without raw integer-to-pointer casts) or lower to `FlatMachine` via our `LoadRelated` / `prov_to_flat_load64_simulation` bridge once disjoint address ranges (`blk.baseAddr + blk.size <= nextBlk.baseAddr`) are established.

2. **Why Jasmin's `MSB_CLEAR` / `MSB_MERGE` + `RFlagVal` Design Is Ideal for Dependent Type Theory:**
   CompCert's `Pregmap.t val` stores both 64-bit registers and 1-bit flags in a untyped map returning `val`, requiring dynamic `Vint`/`Vlong` pattern-matching on every instruction, whereas Vale's `assume val havoc : state -> a -> nat64` introduces an axiom and ACL2's `(undef-flg x86)` threads a monotonically incrementing `:undef` counter through the state record (`(xr fld index (write-user-rflags ...))` in `register-readers-and-writers.lisp:1792-1797` requires `(not (equal fld :undef))` in every frame theorem!). Jasmin's design (`proofs/arch/arch_decl.v:279-283, 555` and `arch_sem.v:244-245, 405-425`) is completely axiom-free, keeps register values (`BitVec 64`) separate from flags (`FlagId → RFlagVal` where `RFlagVal := .def Bool | .undef`), and captures x86-64/AArch64 sub-register write aliasing in a 2-constructor `MsbFlag` (`clear` vs `merge`).

3. **Why ACL2 `x86isa`'s `app-view` vs. `sys-view` Split Matters for Memory-Read Purity:**
   In `acl2/books/projects/x86isa/machine/top-level-memory.lisp` (lines 224–250) and `paging.lisp` (lines 58–250), a memory read `(rme* size addr r-x x86)` returns a 3-tuple `(mv flg val x86)`. In `app-view` (user-space verification), ACL2 proves the critical frame theorem `(equal (mv-nth 2 (rme* size addr r-x x86)) x86)`: **reading memory does not modify the machine state**. In `sys-view` (hardware page-table walk mode), `ia32e-la-to-pa` sets the hardware Accessed (`A`) and Dirty (`D`) bits inside the page-table entries stored in physical memory `:mem`, so **even a memory read mutates `:mem` and `:tlb`**! Because Anneal targets user-space and kernel-module Rust where page tables are not walked inside inline assembly (`reports/machine-code-foundations-and-environment-selection-2026/`), Anneal's `IsaMachineM.loadWord64` should preserve read purity (`s` unchanged on `.ok (w, s)`), matching `app-view`.

---

### 4. Lean 4.34.1 Architectural Adaptation and Mechanized Probe (`support/islaris_trace_and_riscv_typeclass_lean_probe.lean`)

To validate these architectural conclusions directly against Anneal's `Trusted/StepResult.lean` and `Trusted/Refinement.lean` kernel, we authored and verified a 936-line standalone Lean 4.34.1 mechanization in `support/islaris_trace_and_riscv_typeclass_lean_probe.lean`. Every theorem in the file is checked with `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768` with **zero `sorry` / `sorryAx`** and **zero custom axioms** (verified via `#guard_msgs in #print axioms`).

#### 4.1 Typeclass-Parameterized `IsaMachineM` Over `FlatMachine` and `ProvMachine`

Lines 129–214 of `support/islaris_trace_and_riscv_typeclass_lean_probe.lean` define the `IsaMachineM (M : Type → Type) [Monad M]` typeclass and the generic instruction interpreter `executeInst {M} [Monad M] [IsaMachineM M] (inst : IsaInst) : M Unit`, instantiated over `MachineM S α := S → Except Error (α × S)` for both:

- **`FlatMachine` (lines 232–296):** Models registers as `Reg → BitVec 64`, flags as `FlagId → RFlagVal`, memory as `Nat → Option (BitVec 64)`, and instruction-cache coherence via `xAddrs : List Nat` (`riscv-coq` `Minimal.v:47-56`), where `storeWord64` invalidates the stored address from `xAddrs` (`s.xAddrs.filter (fun a => a != addr)`) and `syncICache` (`fence.i`) restores `s.codeAddrs`.
- **`ProvMachine` (lines 300–416):** Models registers as `Reg → IsaVal` where `IsaVal := .word (BitVec 64) | .ptr (allocId : Nat) (ofs : Nat)` and memory as `blocks : Nat → Option AllocBlock` (with `baseAddr`, `size`, `perm : Perm`, and `cells`). In `ProvMachine`, `loadWord64` and `storeWord64` require `.ptr id baseOfs` (rejecting raw `.word` integers as pointer forgery with `.error .ub`) and check `blk.perm.canRead` / `blk.perm.canWrite` and `baseOfs + ofs < blk.size`.

We prove five foundational theorems over `IsaMachineM`:

1. **`msb_clear_vs_merge_contrast` (lines 423–426):** Proves that a 32-bit sub-register write `0xDEADBEEF#32` into `0xCAFEBABE11223344#64` yields `0x00000000DEADBEEF#64` under `MsbFlag.clear` and `0xCAFEBABEDEADBEEF#64` under `MsbFlag.merge`.
2. **`reading_undef_flag_triggers_ub_refines_any` (lines 446–457):** Proves that after `.cmpSetFlags .r0 .r1` (which sets `.zf` to `.def true` and `.pf` to `.undef`, matching CompCert's `compare_ints` in `x86/Asm.v:433-446`), `.readFlagToReg .r2 .zf` steps deterministically to `s2.regs .r2 = 1#64`, whereas `.readFlagToReg .r2 .pf` returns `.failed .ub`, which refines any target `StepResult FlatMachine` under `StepResult.Refines`.
3. **`self_modifying_store_without_fenceI_fails_fetch` (lines 462–478):** Proves that storing into instruction address `0x104` removes `0x104` from `xAddrs`, causing the next instruction at `pc = 0x104` to fail with `.failed .unsupported` until `.fenceI` restores `0x104 ∈ xAddrs`.
4. **`forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat` (Negative Control 1, lines 531–548):** Constructs two adjacent 8-byte allocations (`Block 0` at `[0x1000, 0x1008)` holding `111#64` and `Block 1` at `[0x1008, 0x1010)` holding `222#64`). Proves:
   - An in-bounds load `.load64 .r2 .r0 0` from `.ptr 0 0` succeeds in both `ProvMachine` and `FlatMachine`, loading `111#64`.
   - A cross-allocation out-of-bounds load `.load64 .r2 .r0 8` (one byte/word past `Block 0`, landing on `Block 1` at `0x1008`) triggers `.failed .ub` in `ProvMachine` (`stepProv (.load64 .r2 .r0 8) sampleProvState = .failed .ub`), whereas `stepFlat` on `sampleMatchingFlatState` silently succeeds and reads `222#64` from `Block 1`!
   - A load from a raw integer register `.r1 = .word 0x1000#64` triggers `.failed .ub` in `ProvMachine`.
5. **`prov_to_flat_load64_simulation` (Universal Provenance-to-Flat Simulation, lines 595–640):** Proves that for **all** `ps : ProvMachine`, `fs : FlatMachine`, `dst addrReg : Reg`, and `ofs : Nat` satisfying `LoadRelated ps fs addrReg ofs`, the projected outcome of `stepProv (.load64 dst addrReg ofs) ps` refines `stepFlat (.load64 dst addrReg ofs) fs` under `StepResult.Refines`.

#### 4.2 `IslaTrace` Symbolic Trace Language, Adequacy Bridge, and `seq_nb_state` Negative Control

Lines 644–900 of `support/islaris_trace_and_riscv_typeclass_lean_probe.lean` mechanize the `IslaTrace` language (`.done`, `.readReg`, `.writeReg`, `.readMem`, `.writeMem`, `.setPC`, `.smtAssert`, `.sailAssume`, `.cases`) and its `IslaNBOutcome` evaluator (`evalSingleTracePath`, `evalTraceBranches`), capturing Islaris's `seq_nb_state` operational semantics (`islaris/theories/opsem.v:512-591`):

- `.smtAssert cond k` (`Smt (Assert e)` / `LAssert`): steps to `evalSingleTracePath k s` if `cond = true`, and transitions to `.nbHalted` (`seq_nb_state = true`) if `cond = false`.
- `.sailAssume cond k` (`Assume e` / `LAssume`): steps to `evalSingleTracePath k s` if `cond = true`, and transitions to `.stuckUB` if `cond = false`.

We prove four machine-checked theorems establishing both the positive adequacy bridge and the completeness soundness boundary:

1. **`smtAssert_vs_sailAssume_inverted_polarity` (lines 849–862):** Proves that for **all** machine states `s`, continuations `k`, and postconditions `post`, `naiveIslarisAdequacy (.smtAssert false k) s post` is `True` (vacuously satisfied via `.nbHalted`), whereas `naiveIslarisAdequacy (.sailAssume false k) s post` is `False` (violated via `.stuckUB`).
2. **`islaTrace_refines_stepResult` (Positive Adequacy Bridge, lines 745–753):** Proves that for any instruction `inst`, trace `t`, state `s`, and postcondition `post`, if `t` satisfies `ValidCompleteTraceAt inst t s` (the `sail-riscv`-style completeness invariant requiring that whenever `stepFlat inst s = .step s'`, `(.stepped s') ∈ evalTraceBranches t s`) and `naiveIslarisAdequacy t s post` holds, then `stepFlat inst s = .step s'` implies `post s'`.
3. **`incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator` (Negative Control 2, lines 796–833):** For `branchInst := .branchEqZero .r0 0x2000#64 0x1004#64` and `sampleFlatState` (where `r0 = 42 != 0`), proves that:
   - The incomplete trace `incompleteBranchTrace` (which includes only the `r0 == 0` branch and omits the `r0 != 0` branch) **satisfies** `naiveIslarisAdequacy incompleteBranchTrace sampleFlatState (fun s' => s'.pc = 0x2000#64)`—proving the false postcondition `s'.pc = 0x2000#64`—even though the real machine steps to `s'.pc = 0x1004#64 ≠ 0x2000#64`!
   - The completeness validator catches and rejects `incompleteBranchTrace` (`hasNonHaltedBranch incompleteBranchTrace sampleFlatState = false` and `¬ ValidCompleteTraceAt branchInst incompleteBranchTrace sampleFlatState`), while accepting the two-branch trace `completeBranchTrace`.
4. **`completeBranchTrace_valid_for_all_states` (lines 837–866):** Proves that `ValidCompleteTraceAt branchInst completeBranchTrace s` holds universally for **all** concrete `FlatMachine` states `s`.

## Boundaries

1. **Unverified OCaml/Rust Toolchain in Standard `Islaris` and `CN2Islaris`:**
   - Standard AArch64 Islaris proofs (`islaris/theories/aarch64/`, `CN2Islaris/proofs/`) trust: (a) the Sail-to-JIB lowering in `isla-sail/jib_ir.ml`, (b) the Z3-backed symbolic execution and tree simplification in `isla/src/footprint.rs`, and (c) the event-stripping filters in `islaris/frontend/decomp.ml:74-88` (`arch_ignored_regs`, concrete `ReadReg` deletion, and index `i > 0` `Smt (Assert _)` deletion).
   - If Anneal uses an external symbolic trace generator (such as `isla-footprint`), the generated traces **must not** be admitted as axioms. Instead, Anneal must either generate traces via Lean 4 definitional reduction/reflection over a Lean ground ISA semantics (`LNSym` / `sail-riscv-lean`) or require an automatically checked `ValidCompleteTraceAt` proof per instruction trace (`Theorem 3.1` / `Theorem 3.3`).
2. **Non-Recursive Call-Graph and Scalar/1D-Array Restrictions in `CN2Islaris`:**
   - `cerberus/backend/cn/dwarfData.ml:49-71` cannot bound stack depth for recursive functions or indirect function calls (`blr`), and `binaryVerification.ml:194-264` only translates initialized 64-bit `unsigned long` scalars and 1D arrays with step size 8.
3. **Single-Thread Sequential Execution Scope:**
   - Although `islaris` defines a concurrent trace semantics (`par_step` in `islaris/theories/opsem.v:595-660`), its verification rules assume sequential consistency (`SC`) rather than the relaxed Armv8-A/RISC-V concurrency models (`Flat`/`Promising`). Similarly, Anneal's current `StepResult` kernel (`Trusted/StepResult.lean`) is sequential and deterministic.
4. **User-Mode vs. System-Mode Memory:**
   - As shown by ACL2 `x86isa`'s `app-view` vs. `sys-view` split (`top-level-memory.lisp:224-250`, `paging.lisp:58-250`) and `seL4 l4v`'s `machine_rest_monad` (`MachineOps.thy:19-28, 374-456`), modeling hardware page-table walks or MMU TLB state destroys pure memory reads and requires carrying ghost ASID/VMID invariants. Anneal's inline assembly verification should remain explicitly scoped to user-mode / fixed-mapping virtual memory (`app-view`).

## Evidence

All primary-source files, exact 40-character git commit SHAs, git blob SHA-1 hashes, and SHA-256 digests are recorded in [`support/source-manifest.json`](support/source-manifest.json). Key evidence locations include:

- **Lean 4.34.1 Mechanized Probe (`support/islaris_trace_and_riscv_typeclass_lean_probe.lean`, 936 lines, SHA-256 `b1dc5ad4e99921e1913146a7c71d731a7a3dbac8269ae7c12720c8fc7df06acd`):**
  - `Section 1` (lines 45–102): `Error`, `StepResult`, `StepResult.Refines`, `Partial`, `Partial.undefined_refines_any`.
  - `Section 2` (lines 104–640): `IsaMachineM`, `executeInst`, `FlatMachine`, `ProvMachine`, `msb_clear_vs_merge_contrast`, `reading_undef_flag_triggers_ub_refines_any`, `self_modifying_store_without_fenceI_fails_fetch`, `forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat`, `prov_to_flat_load64_simulation`.
  - `Section 3` (lines 642–889): `IslaTrace`, `IslaNBOutcome`, `evalSingleTracePath`, `evalTraceBranches`, `naiveIslarisAdequacy`, `ValidCompleteTraceAt`, `islaTrace_refines_stepResult`, `incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator`, `completeBranchTrace_valid_for_all_states`, `smtAssert_vs_sailAssume_inverted_polarity`.
  - `Section 4` (lines 891–936): `#guard_msgs in #print axioms` confirming zero `sorryAx` and zero custom axioms across all 9 main theorems.
- **Isla / Islaris / CN2Islaris Primary Sources:**
  - `rems-project/isla` (`e9b5d945394277656593a0d429466d7fa0a2b4b3`): `isla-sail/jib_ir.ml:29-105`, `src/footprint.rs:577-718`.
  - `rems-project/isla-lang` (`db2ba552ba4b26fabbff27d5ad806d38ecce9bd6`): `coq/isla_lang.v:139-179`.
  - `rems-project/islaris` (`c978e10f50db5c40f0fdf113f5f76a779782c6f9`): `frontend/main.ml:83-163`, `frontend/decomp.ml:29-162`, `frontend/isla_lang_if.ml:32-119`, `frontend/arch.ml:54-116`, `theories/opsem.v:476-591`, `theories/lifting.v:87-93, 369-387, 793-832`, `theories/adequacy.v:85-97`, `sail-riscv/sail_opsem.v:589-650, 965-1120`, `sail-riscv/memcpy.v:65-85`.
  - `rems-project/cerberus` (`3bdd8cb8e2805d46c22725d7651a2ed90b012837`): `backend/cn/binaryVerification.ml:74-283, 694-755`, `backend/cn/dwarfData.ml:7-75`.
  - `rems-project/CN2Islaris` (`f34f9a2f0a9b75a6b342aa966d0d14daca58c466`): `examples/Makefile:1-90`, `proofs/array_read/O2/array_read.v:1-120`, `proofs/conditional/O2/conditional.v:1-120`.
- **`riscv-coq` & `bedrock2` Primary Sources:**
  - `mit-plv/riscv-coq` (`45dc8dfc17c77aabb433355b9d39edc6bfd429ae`): `src/riscv/Spec/Machine.v:35-86`, `src/riscv/Spec/Decode.v:1483-1529`, `src/riscv/Spec/Execute.v:1-60`, `src/riscv/Spec/ExecuteI.v:1-165`, `src/riscv/Spec/Primitives.v:27-184`, `src/riscv/Platform/RiscvMachine.v:23-70`, `src/riscv/Platform/Minimal.v:20-95`, `src/riscv/Platform/MinimalMMIO.v:131-165`, `src/riscv/Utility/Monads.v:72-355`, `src/riscv/Utility/FreeMonad.v:10-45`.
  - `mit-plv/bedrock2` (`757f17c6083bf8d43b5293a0db545c8d0aa32a13`): `compiler/src/compiler/FlatToRiscvCommon.v:96-197, 251-283`, `compiler/src/compiler/Pipeline.v:112-195`.
- **CompCert, Jasmin, Vale, ACL2 `x86isa`, HOL4 (`L3`, `CakeML`, `HolBA`), and `seL4 l4v` Primary Sources:**
  - `AbsInt/CompCert` (`e26caf9fa6cd91665c9e8ee2b5194f413c796821`): `common/Values.v:34-40, 369-385, 690-707`, `common/Memory.v:57-68`, `x86/Asm.v:25-55, 433-446, 562-564, 949-976`, `aarch64/Asm.v:28-80`, `riscV/Asm.v:39-83, 380-403`.
  - `jasmin-lang/jasmin` (`6c4994d56a9a030201e62275a7d343b101bd0a23`): `proofs/arch/arch_decl.v:157-158, 279-283, 529, 555-574, 714-750`, `proofs/arch/arch_sem.v:244-245, 378-389, 405-425`, `proofs/compiler/x86_instr_decl.v:281-318, 397-399`, `proofs/lang/memory_model.v:78-90, 894-950`.
  - `project-everest/vale` (`bbae0eb89143734363b14a77642dbf8dec36e288`): `fstar/specs/hardware/X64.Machine_s.fst:62-110`, `fstar/specs/hardware/X64.Semantics_s.fst:45-156`.
  - `acl2/acl2` (`9df88e946034e24212f3aedd8b71b02e4224783e`): `books/projects/x86isa/machine/state.lisp:186-250`, `register-readers-and-writers.lisp:197-530, 1600-1823`, `other-non-det.lisp:71-75`, `top-level-memory.lisp:120-250`, `paging.lisp:58-250`.
  - `HOL-Theorem-Prover/HOL` (`d73e603616d80726506326d83af8f0e74559623c`): `examples/l3-machine-code/common/stateScript.sml:45-154`.
  - `CakeML/cakeml` (`665f9b21712ad093e10a404ccc2f78e64a34aeef`): `compiler/encoders/asm/asmScript.sml:21-96`, `compiler/encoders/asm/asmSemScript.sml:19-125`.
  - `kth-step/HolBA` (`ef22c1fd8da612c57f2e7f273cb14594a7e529d3`): `src/theory/bir/bir_programScript.sml:16-95, 254-368`, `src/theory/bir/bir_exp_memScript.sml:15-100`.
  - `seL4/l4v` (`7b8c09901f25bd3ba5d05046bba14e226bd659d1`): `spec/machine/AARCH64/MachineOps.thy:19-57, 148-204, 374-456`, `spec/abstract/AARCH64/ArchVSpace_A.thy:34-217`.

## Revalidation

To revalidate this report and its Lean 4.34.1 mechanization:

1. **Verify the standalone Lean 4.34.1 probe (`zero sorry`, `zero custom axioms`):**
   ```bash
   /usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768 \
     reports/rocq-hol-acl2-isa-verification-frameworks-lean-adaptation-2026/support/islaris_trace_and_riscv_typeclass_lean_probe.lean
   ```
   The command must exit with status `0` and produce no output (confirming that every `#guard_msgs in #print axioms` check matches).
2. **Verify source manifest hashes against upstream repositories:**
   Check the commit SHAs and git blob hashes in `support/source-manifest.json` against the 16 repositories listed in `REPORT.json`.
3. **When to Revalidate:**
   Revalidate whenever Anneal's `Trusted/StepResult.lean`, `Trusted/Refinement.lean`, or `Trusted/Memory.lean` changes its `StepResult` or `Allocation` types, or when `rems-project/islaris` merges `sail-riscv-update` / `CN2Islaris` into `main`.

*Authored by an AI agent acting on joshlf's behalf.*
