# Lean 4 WebAssembly Formalizations and Virtual ISA Verification (2026)

## Summary

A primary-source inspection of all six public Lean 4 WebAssembly (`Wasm`) formalization repositories (`plum-umd/lean-wasm`, `cajal-technologies/talos`, `linobit-corp/wasm-lean`, `aionescu/lean-wasm`, `argumentcomputer/Wasm.lean`, and `T-Brick/lean-wasm`), cross-referenced against the Coq/Rocq and Isabelle/HOL WebAssembly ecosystems (`WasmCert-Coq`, `Iris-Wasm`, `WasmCert-Isabelle`) and the eBPF virtual-ISA verification stack (`CertrBPF`/`CertFC`, `Jitterbug`, and `Kops`/`KinsnLean4`), establishes five core technical findings for Anneal (`joshlf/anneal-private`):

1. **Two production-grade, zero-`sorry`, zero-custom-axiom Lean 4 Wasm formalizations exist as of October 2026 (`plum-umd/lean-wasm` and `cajal-technologies/talos`), serving complementary verification roles**:
   - `plum-umd/lean-wasm` (`d438fabdd6304bcbc72f211b9f532be76ebc7f29`, Lean `v4.27.0`, 96 `.lean` files, 19,394 LOC, 218 `theorem` declarations, 0 `sorry`s, 0 custom axioms) targets **WebAssembly 3.0** (`2026-10-09` specification), achieves **100% conformance across all 257 official Wasm testsuite scripts** (65,202 commands, 0 failures), and mechanizes executable module-validator soundness (`validate_sound : validate module = .ok () → module.Valid`), subtype-carrying stepper soundness (`step_sound`, `run_sound`, `stepConfiguration_sound`, `runConfiguration_sound`), and local redex determinism (`reduce_iff`, `reduces_deterministic`). It does not yet mechanize global syntactic type safety (`progress` and `preservation` of `ConfigStep` under `Configuration.Typed`).
   - `cajal-technologies/talos` (`80644390de3ad4db3055445259a034413ae41577`, Lean `v4.34.1`, 410 `.lean` files, 176,097 LOC, 3,718 `theorem` declarations, 0 active `sorry`s, 0 custom axioms) targets **end-to-end functional verification of Rust programs compiled to Wasm (`wasm32`)** using **`iris-lean` separation logic** over an authoritative small-step operational semantics (`Wasm.SmallStep`, 7,654 LOC) covering Wasm 2.0/3.0 control flow, multi-memory, tables, bulk-memory operations, and Wasm 3.0 exception handling (`try_table`, `throw`, `throw_ref`). It proves both partial and total outcome adequacy (`adequate_to_partiallyMeetsOutcome`, `stronglyNormalizing_adequate_outcome`) and verifies concrete `rustc`-compiled `.wasm` binaries (`SwapElements`, `SwapElementsOpt3`, `Mergesort`, `GcdStdio`, `HexEncodeStdio`, `HexDecodeStdio`, `RustVec`, `RustU64`, `RustArray`).

2. **A third zero-`sorry` repository (`linobit-corp/wasm-lean`) exhibits a critical relational vacuity bug in its headline interpreter soundness theorem**:
   - While `linobit-corp/wasm-lean` (`6d612a510d145950838ec193e9ae0b75a7c881ef`, Lean `v4.15.0`, 54 `.lean` files, 14,005 LOC, 250 `theorem` declarations, 0 active `sorry`s) passes 14,342/14,342 Wasm 1.0 spec test assertions and contains genuine local progress/preservation proofs for `ReduceSimple`, its headline block-execution soundness theorem (`execBlock_sound : execBlock fuel s f instrs = (.ok (), s', f') → ReduceStar (s, f, instrs) (s', f', [])` in `WasmLean/Correctness/Block.lean:825`) is **vacuous on every non-control-flow instruction**. Specifically, `WasmLean/Semantics/Reduce.lean:339-343` defines `Reduce.r_interp_flat` with **zero premises**, relating any consumed stack and any `BasicInstr` to any produced stack across any store/frame pair, and `misc_instr_reduces` (`WasmLean/Correctness/Lemmas.lean:73-91`) invokes `.single .r_interp_flat` while ignoring the interpreter execution hypothesis `_hbi`.

3. **The remaining three Lean 4 Wasm repositories (`aionescu/lean-wasm`, `argumentcomputer/Wasm.lean`, `T-Brick/lean-wasm`) are incomplete prototypes**:
   - `aionescu/lean-wasm` (`66f1166f84a763b23475b0eb660153c72ec54d29`, 9 files, 1,458 LOC, 0 theorems, 8 active `sorry`s) explores an intrinsically-typed AST (`Instr : InstrKind → List Ty → List (List Ty) → List Ty → List Ty → Type`) over a heterogeneous stack (`HList Ty.type`), but hits dependent-type unification failures when pattern-matching on `List.append`-indexed stack splits (`HList.take` / `HList.drop`).
   - `argumentcomputer/Wasm.lean` (`454172e1219ce648732211a7804829809dffd64d`, 23 files, 4,616 LOC, 0 theorems, 8 active `sorry`s) is an unverified Lean 4 nightly (`2023-01-10`) interpreter and binary/text codec that omits linear memory from `Store m` and contains arithmetic bugs in signed right shift (`shr_s`) and float equality.
   - `T-Brick/lean-wasm` (`43b051f30b920e4d1253d83ae08b3dc83b4d6d88`, 44 files, 7,005 LOC, 12 theorems, 39 active `sorry`s) is a Wasm 2.0 specification scaffold whose memory step relation is commented out (`Wasm/Dynamics.lean:482-572`), whose `Instr : Step` relation omits control flow, calls, and memory instructions, and whose operand type-matching rule `Typ.MatchSingle.refl` (`Wasm/Validation/Statics.lean:32`) leaves `t1 t2` unconstrained.

4. **Extrinsic vs. intrinsic typing in Lean 4 Wasm models**:
   - Every Lean 4 Wasm formalization that scales to full module validation, linear memory, and Wasm 2.0/3.0 control flow (`plum-umd/lean-wasm`, `cajal-technologies/talos`, `linobit-corp/wasm-lean`) uses an **extrinsically-typed** AST (`Instr : Type`, `Stack := List Value`) paired with a separate inductive typing relation or executable validator. Intrinsically-typed stacks (`HStack : List WasmTy → Type`) eliminate `.stuckTypeMismatch` by construction and admit a clean lockstep erasure theorem (`stepIntrinsic_erases_to_extrinsic`), but struggle with Wasm's stack-polymorphic instructions (`unreachable`, `br`, `return`) and `List.append` associative re-indexing in Lean 4's dependent pattern matcher.

5. **Virtual ISA semantics in Anneal (`Compiles MirLang WasmLang` and eBPF `VerifiedChecker`)**:
   - In Anneal's `Trusted/Refinement.lean` and `Trusted/StepResult.lean` algebra, a WebAssembly `trap` (`unreachable`, integer division by zero, out-of-bounds `LinearMem` access) is a **deterministic, well-defined abort outcome** (`.terminated .unwind`, with `PrefixOutcome.isSafe = True` and `defined = True`), **not** `Partial.ub` (`defined = False`).
   - This creates a fundamental directional asymmetry: compiling an `unsafe` Rust MIR raw-pointer dereference (which has `defined = False` / `Partial.ub` when out-of-bounds of its Rust allocation) to a Wasm `i32.load` **is a sound refinement** (`rustc_raw_load_to_wasm_compiles`), because source UB refines both a silent in-bounds Wasm linear-memory read and a deterministic Wasm trap. Conversely, proving a source contract that forbids traps (`EnsuresNoTrap`) from compiled Wasm requires proving that `.terminated .unwind` is unreachable (`wasm_trap_refutes_ensuresNoTrap`), whereas a panic/trap-permitting contract (`EnsuresValueOrTrap`) is satisfied even when Wasm traps (`wasm_trap_satisfies_valueOrTrap`).
   - Furthermore, Wasm linear memory enforces only a **coarse sandbox boundary** (`ea + width ≤ mem.size`) with no per-allocation provenance (`wasm_linear_memory_lack_of_provenance`), and lowering pointer offsets via 32-bit `i32.add` on `wasm32` wraps modulo $2^{32}$ into low memory whereas Wasm's static `memarg.offset` computes `ea = base.toNat + offset.toNat` in unbounded `Nat` and deterministically traps (`wasm32_u32_wrapping_vs_memarg_offset`).
   - For the eBPF virtual ISA, the in-kernel static verifier maps directly to an Anneal `VerifiedChecker EbpfLang (fun _ => EbpfWellFormed minPktLen)` (`ebpfVerifiedChecker`), and the Kops (`arXiv:2606.24213` / `KinsnLean4`) dual-sequence JIT extension architecture is a direct instance of composing `VerifiedChecker.check_sound` with `Compiles EbpfLang NativeJitLang π_jit seq_proof seq_native` (`kops_dual_sequence_jit_soundness`).

All three formal bridges—extrinsic/intrinsic Wasm erasure and vacuity analysis, `Compiles MirLang WasmLang` trap-vs-UB refinement, and the eBPF `VerifiedChecker` / Kops dual-sequence soundness theorem—are mechanized with **zero `sorry`s and zero custom axioms** in [`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean), checked under Lean `v4.34.1`.

## Applicability

This report applies to:

- The six Lean 4 WebAssembly repositories at the exact commits recorded in `REPORT.json` and [`support/source-manifest.json`](support/source-manifest.json):
  1. `plum-umd/lean-wasm` at `d438fabdd6304bcbc72f211b9f532be76ebc7f29` (Lean `v4.27.0`);
  2. `cajal-technologies/talos` at `80644390de3ad4db3055445259a034413ae41577` (Lean `v4.34.1`, with `mathlib4` at `0f4eab4be9cd2fd9bcd1ca9bbeadfa16b8ae0b82` and `cajal-technologies/iris-lean` at `b1152bd6e649f4ac376e7f778d02581d66b622cf`);
  3. `linobit-corp/wasm-lean` at `6d612a510d145950838ec193e9ae0b75a7c881ef` (Lean `v4.15.0`, with `linobit-corp/bfloat-lean` at `89b9d3f3fd842bc5a12854b07c92a493c9c9d2b5`);
  4. `aionescu/lean-wasm` at `66f1166f84a763b23475b0eb660153c72ec54d29` (Lean `v4.10.0-rc2`);
  5. `argumentcomputer/Wasm.lean` at `454172e1219ce648732211a7804829809dffd64d` (Lean `nightly-2023-01-10`);
  6. `T-Brick/lean-wasm` at `43b051f30b920e4d1253d83ae08b3dc83b4d6d88` (Lean `v4.25.0`).
- Comparative WebAssembly and eBPF verification repositories:
  - `WasmCert/WasmCert-Coq` at `58a3d3f8b7af4dc8aa9351f254a9e672643b21f8` (and its `iris-wasm-opam` branch at `57b05fb59a193078e5db4378cce164766e7b8a2c`, `logsem/iriswasm` at `e37f8387a1171d104d78a2f77f9e637e090cf3d4`);
  - `WasmCert/WasmCert-Isabelle` at `d9b4659c8b38879a5fc7e0213950751a61091908`;
  - `future-proof-iot/CertFC` (`CertrBPF`) at `75690097c946c555cc4ce1e69d13ef86dc738180`;
  - `uw-unsat/jitterbug` at `78d1e75ad506498b585fbac66985ff9d9d05952d`;
  - `eunomia-bpf/bpf-benchmark` (`kinsn/lean/`, `KinsnLean4` / Kops `arXiv:2606.24213`) at `d03e6742bd2a56b94448071b0439d67a6574e9a3` (Lean `v4.28.0`).
- Anneal (`joshlf/anneal-private` at `0c00b820d4571ba35a9c48dfe2cca50dfd1d3e0d`) and its trusted semantic core (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`) under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Primary-Source Census of the Six Lean 4 Wasm Repositories

Basis: source + execution

Direct inspection of every `.lean` file across the six repositories yields the following exact census (separating active `sorry` proof holes from string literals and comments):

| Repository | Commit (`HEAD`) | Lean Toolchain | `.lean` Files | Lean LOC | `theorem` Decls | Active `sorry`s (Comments/Strings) | Custom `axiom`s | Wasm Spec Target | Spec Testsuite Conformance | Primary Architecture & Proof Status |
| :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- | :--- | :--- |
| `plum-umd/lean-wasm` | `d438fabdd6304bcbc72f211b9f532be76ebc7f29` | `v4.27.0` | 96 | 19,394 | 218 | **0** (0) | **0** | Wasm 3.0 (`2026-10-09`) | **257/257 scripts** (65,202 commands, 0 failures) | Extrinsic AST + inductive `Module.Valid` + sound executable validator (`validate_sound`) + subtype-carrying stepper (`step_sound`, `runConfiguration_sound`) + local determinism (`reduce_iff`, `reduces_deterministic`). |
| `cajal-technologies/talos` | `80644390de3ad4db3055445259a034413ae41577` | `v4.34.1` | 410 | 176,097 | 3,718 | **0** (6 in `verifier/` codegen strings) | **0** | Wasm 2.0 + 3.0 exceptions (`try_table`) + multi-memory | 78+ conformance & small-step equivalence suites | Fuel-bounded big-step + authoritative small-step (`Wasm.SmallStep`) + `iris-lean` separation logic (`WasmHeap`, `WasmRules`) + partial/total adequacy + verified Rust-to-Wasm programs. |
| `linobit-corp/wasm-lean` | `6d612a510d145950838ec193e9ae0b75a7c881ef` | `v4.15.0` | 54 | 14,005 | 250 | **0** (2 in comments) | **0** | Wasm 1.0 MVP + partial 2.0 bulk ops | **14,342/14,342** Wasm 1.0 assertions | Fuel-bounded interpreter + `bfloat-lean` IEEE 754 floats. **Critical bug**: `Reduce.r_interp_flat` has zero premises, making `execBlock_sound` vacuous for all non-control-flow instructions. |
| `aionescu/lean-wasm` | `66f1166f84a763b23475b0eb660153c72ec54d29` | `v4.10.0-rc2` | 9 | 1,458 | 0 | **8** (11 commented) | **0** | Wasm 1.0 arithmetic + control-flow core | None | Intrinsically-typed GADT (`Instr : InstrKind → List Ty → List (List Ty) → List Ty → List Ty → Type`) over `HList Ty.type`; blocked by dependent unification in `Spec.lean` and `Fast.lean`. |
| `argumentcomputer/Wasm.lean` | `454172e1219ce648732211a7804829809dffd64d` | `nightly-2023-01-10` | 23 | 4,616 | 0 | **8** (1 commented) | **0** | Wasm 1.0 subset (no linear memory) | Selected `.wast` arithmetic scripts | Unverified monadic interpreter (`EngineM m`), `.wast` parser, binary serializer; omits linear memory from `Store m`; buggy `shr_s` and float `.eq`. |
| `T-Brick/lean-wasm` | `43b051f30b920e4d1253d83ae08b3dc83b4d6d88` | `v4.25.0` | 44 | 7,005 | 12 | **39** (3 commented) | **0** | Wasm 2.0 scaffold | None | Incomplete spec transcription; memory step rules commented out (`Dynamics.lean:482-572`); `Instr : Step` omits control flow/memory/calls; unsound `Typ.MatchSingle.refl`. |

---

#### 1.1 `plum-umd/lean-wasm`: Wasm 3.0 Reference Semantics, Verified Validator, and Subtype-Carrying Stepper

Basis: source (`plum-umd/lean-wasm@d438fabdd6304bcbc72f211b9f532be76ebc7f29`)

`plum-umd/lean-wasm` is the most complete specification-level mechanization of the **WebAssembly 3.0** standard (`2026-10-09` W3C draft) in Lean 4:

- **Syntax and Type System (`Wasm/Syntax/`, `Wasm/Validation.lean`)**:
  - Covers the full Wasm 3.0 type hierarchy (`Wasm/Syntax/Types.lean`): number types (`i32`, `i64`, `f32`, `f64`), vector type (`v128`), packed storage types (`i8`, `i16`), heap and reference types (`any`, `eq`, `i31`, `struct`, `array`, `func`, `noext`, `nofunc`, `none`, concrete type indices `DefType`), recursive type groups (`RecType`, `SubType`), and Iso-recursive type unrolling.
  - Defines the declarative specification typing judgments (`InstrsTyped`, `Module.Valid` in `Wasm/Validation.lean`) alongside a computable checker (`validate : Module → Except String Unit` in `Wasm/ExecutableValidation.lean`).
- **Executable Validator Soundness (`Wasm/ExecutableValidationSoundness.lean`)**:
  - Proves `validate_sound` (`Wasm/ExecutableValidationSoundness.lean:1000`):
    ```lean
    theorem validate_sound {m : Module} (h : validate m = .ok ()) : m.Valid
    ```
    Every individual validation check (`checkFuncType_sound`, `checkTableType_sound`, `checkMemType_sound`, `checkGlobal_sound`, `checkElem_sound`, `checkData_sound`, `checkExport_sound`, `checkInstrs_sound`) is proved sound against its inductive specification counterpart with zero `sorry`s.
- **Subtype-Carrying Stepper Architecture (`Wasm/Reduction.lean`, `Wasm/Stepper.lean`, `Wasm/Configuration.lean`)**:
  - Rather than writing an untyped interpreter and proving soundness post-hoc, `plum-umd/lean-wasm` defines its executable single-step functions to return **dependent subtypes** carrying the proof of the relational step:
    - `Wasm/Reduction.lean:23-68`: Defines relational local reduction `Reduces (s : Store) (f : Frame) (es : List AdminInstr) (s' : Store) (f' : Frame) (es' : List AdminInstr) : Prop`, an executable function `reduce?`, and proves both bidirectional equivalence and determinism:
      ```lean
      theorem reduce_iff : reduce? s f es = some (s', f', es') ↔ Reduces s f es s' f' es'
      theorem reduces_deterministic :
        Reduces s f es s₁ f₁ es₁ → Reduces s f es s₂ f₂ es₂ → (s₁, f₁, es₁) = (s₂, f₂, es₂)
      ```
    - `Wasm/Stepper.lean:107-305`: Defines `StepResult s f es` where the `.step` constructor carries a proof `h : Step s f es s' f' es'`, and proves `step_sound` (`Stepper.lean:212`) and `run_sound : run fuel s f es = (.normal s' f' vs, n) → Steps s f es s' f' (vs.map AdminInstr.val)` (`Stepper.lean:300`).
    - `Wasm/Configuration.lean:181, 223`: Lifts `Step` to whole-store configurations `ConfigStep`, proving `stepConfiguration_sound` and `runConfiguration_sound`.
    - `Wasm/Host.lean:133-345`: Decomposes host-function calls into resumable `HostCallFrame` continuations (`resumeHostCall`, `stepWithHost_sound`), enabling verified host/WASI embedding without axioms.
- **IEEE 754 Floats and SIMD (`Wasm/Float.lean`, `Wasm/Simd/`)**:
  - Implements pure bit-level IEEE 754-2019 `Float32` and `Float64` arithmetic (`Wasm/Float.lean`, including canonical/arithmetic NaN propagation required by the Wasm 3.0 spec) and all 256 `v128` SIMD opcodes (`Wasm/Simd/`), enabling 100% conformance across all 257 `.wast` files (65,202 commands) in `WebAssembly/testsuite@b464a4cd100d98175ae6e3890db89a2e6c8302f7`.
- **Current Proof Boundary**:
  - `plum-umd/lean-wasm` defines configuration typing (`Configuration.Typed` in `Wasm/Configuration.lean`), but has **not yet proved global syntactic type preservation and progress** (`ConfigStep c c' → c.Typed t → c'.Typed t`).

---

#### 1.2 `cajal-technologies/talos`: Authoritative Small-Step Wasm 2.0/3.0 Semantics, `iris-lean` Separation Logic, and Verified Rust-to-Wasm Programs

Basis: source (`cajal-technologies/talos@80644390de3ad4db3055445259a034413ae41577`)

`cajal-technologies/talos` is a 176,097-LOC industrial-scale Lean `v4.34.1` verification platform for proving functional correctness of WebAssembly programs—specifically targeting **Rust programs compiled to Wasm (`wasm32`)**:

- **Five-Component Repository Architecture**:
  1. `interpreter/` (78 `.lean` files, 24,524 LOC): Wasm binary decoder (`Binary.lean`), WAT parser (`Text/`), module validator (`Validation/`), fuel-bounded big-step evaluator (`Interpreter/Wasm/Semantics.lean`), and authoritative small-step machine (`Interpreter/Wasm/SmallStep.lean`, 7,654 LOC).
  2. `codelib/` (31 `.lean` files, 31,401 LOC): Instantiation of `cajal-technologies/iris-lean` separation logic for `Wasm.SmallStep` (`SmallStepLanguage.lean`, `SmallStepOutcomeAdequacy.lean`, `WasmHeap.lean`, `WasmRules.lean`, `SimpWasm.lean`) plus verified byte/slice/framing libraries.
  3. `programs/lean/` (260 `.lean` files, 114,507 LOC): End-to-end separation-logic correctness proofs of real `.wasm` modules compiled from Rust (`SwapElements.lean`, `SwapElementsOpt3.lean`, `Mergesort.lean`, `GcdStdio.lean`, `HexEncodeStdio.lean`, `HexDecodeStdio.lean`, `RustVec.lean`, `RustU64.lean`, `RustArray.lean`, `LinkedList.lean`).
  4. `verifier/` (22 `.lean` files, 4,941 LOC): Automated verification-condition and Lean proof-skeleton generator for Wasm functions (`Verifier/Emit.lean`, `Verifier/Symbolic.lean`, `Verifier/WPGen.lean`). The 6 occurrences of the substring `sorry` in the entire repository are string templates inside `Verifier/Emit.lean` and `Verifier/Main.lean` used when emitting user proof stubs; the compiled Lean codebase has **0 active `sorry`s and 0 custom axioms**.
  5. `float/` (19 `.lean` files, 724 LOC): IEEE 754 floating-point support.

- **Authoritative Small-Step Machine (`Interpreter/Wasm/SmallStep.lean`)**:
  - `Config α` (`SmallStep.lean:337-350`) explicitly separates:
    - `store : Store α` (linear memories `mems : Array Memory`, `tables`, `globals`, `funcs`, `tags`, `elems`, ` datas`, and parameterized host state `host : α`),
    - `frame : Frame` (local variables `locals : Array Value` and `module : ModuleInst`),
    - `stack : Array Value` (explicit operand stack),
    - `ctrl : Array CtrlFrame` (structured control frames `.block`, `.loop`, `.tryTable` with saved stack heights `stackHeight : Nat` and continuation instruction streams),
    - `callStack : Array CallFrame` (caller activation frames across nested `call` / `call_indirect`),
    - `code : InstrStream` (current instruction slice + `pc : Nat`), and
    - `status : ExecStatus` (`.running` | `.done` | `.trapped (reason : TrapReason)`).
  - Defines both an executable stepper `step : Config α → Option (StepKind × Config α)` (`SmallStep.lean:2548`) and an inductive relation `inductive Step : Config α → StepKind → Config α → Prop` (`SmallStep.lean:3255`), proved equivalent via `step_sound : step c = some (k, c') → Step c k c'` (`SmallStep.lean:3455`) and `step_complete : Step c k c' → step c = some (k, c')` (`SmallStep.lean:3496`), yielding determinism (`Step.deterministic` at `SmallStep.lean:3525`).
  - Covers **Wasm 3.0 exception handling** (`try_table` catch clauses `.catch_`, `.catch_ref`, `.catch_all`, `.catch_all_ref`, `throw`, `throw_ref`, and runtime `ExnInst` / `exnref` payloads) and **multi-memory** (`memIdx : UInt32` on all load/store/bulk-memory instructions).

- **`iris-lean` Separation Logic & Outcome Adequacy (`codelib/CodeLib/SepLogic/`)**:
  - `WasmHeap.lean:35-120`: Models multi-memory linear heaps via `GenHeap (Nat × UInt32) UInt8` (`MemoryKey := memId × addr`), defining byte points-to assertions `addr ↦[memId] b`, contiguous byte-slice points-to `addr ↦*[memId] bs`, and typed little-endian `u32`/`u64` points-to predicates, alongside ghost maps for globals (`GlobalKey ↦g v`), locals (`LocalKey ↦l v`), and host I/O streams.
  - `SmallStepOutcomeAdequacy.lean:45-310`: Defines `ObservableOutcome := .done (Array Value) | .trapped TrapReason` and proves both:
    - **Partial adequacy** (`adequate_to_partiallyMeetsOutcome`): if an Iris weakest precondition holds for initial configuration `c`, then every terminal configuration reachable from `c` satisfies the postcondition `Φ : ObservableOutcome → Prop`.
    - **Total termination adequacy** (`stronglyNormalizing_adequate_outcome` and the top-level closed-world theorem `wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome`): for deterministic, strongly-normalizing steps, the Iris WP proof guarantees that execution terminates in finitely many steps with an `ObservableOutcome` satisfying `Φ`.

---

#### 1.3 `linobit-corp/wasm-lean`: Vacuity Discovery in `Reduce.r_interp_flat` and `execBlock_sound`

Basis: source (`linobit-corp/wasm-lean@6d612a510d145950838ec193e9ae0b75a7c881ef`) + derived

`linobit-corp/wasm-lean` (54 `.lean` files, 14,005 LOC, 250 `theorem` declarations, 0 `sorry`s enforced by `scripts/check_no_sorry.lean`) implements a Wasm 1.0 interpreter (`WasmLean/Interpreter/Exec.lean`) backed by `linobit-corp/bfloat-lean` for IEEE 754 floating-point operations and passes 14,342/14,342 Wasm 1.0 spec assertions. Its README claims a complete formal soundness proof (`execBlock_sound`) relating the fuel-based interpreter `execBlock` to the small-step reduction relation `ReduceStar`.

**Primary-source audit reveals that `execBlock_sound` is relationally vacuous on every basic instruction routed through `execBasicInstr`**:

1. **Zero-premise catch-all constructor `Reduce.r_interp_flat` (`WasmLean/Semantics/Reduce.lean:339-343`)**:
   ```lean
   | r_interp_flat {s s' : Store} {f f' : Frame}
       {consumed produced : List ValNum} {bi : BasicInstr} {base : List AdminInstr} :
       Reduce (s, f, consumed.reverse.map vnConst ++ [.basic bi] ++ base)
              (s', f', produced.reverse.map vnConst ++ base)
   ```
   Notice that `r_interp_flat` has **zero hypotheses** constraining `s'`, `f'`, `consumed`, `produced`, or `bi`. It asserts that *any* `BasicInstr` can transition from *any* store `s`, frame `f`, and consumed numeric values `consumed` to *any* store `s'`, frame `f'`, and produced numeric values `produced`.
2. **Ten additional zero-premise constructors in `Reduce` (`WasmLean/Semantics/Reduce.lean:256-329`)**:
   `r_table_get`, `r_table_set`, `r_call_indirect`, `r_load`, `r_store`, `r_memory_size`, `r_memory_grow`, `r_memory_fill`, `r_memory_copy`, and `r_cvtop` are likewise defined with **zero premises** (e.g., `r_load` transitions `[i32.const addr, load] → [vnConst res]` for any unconstrained `res : ValNum`, and `r_store` transitions `(s, f, [i32.const addr, vnConst v, store]) → (s', f, [])` for any unconstrained store `s'`).
3. **Unused interpreter hypothesis `_hbi` in `WasmLean/Correctness/Lemmas.lean:73-112` and `WasmLean/Correctness/Block.lean:285`**:
   In `WasmLean/Correctness/Lemmas.lean:73-91`:
   ```lean
   theorem misc_instr_reduces (s s_mid : Store) (f f_mid : Frame)
       (ms : ModState) (bi : BasicInstr) (base : List AdminInstr) :
       ReduceStar (s, f, valsToAdmin ms.stack ++ [.basic bi] ++ base)
                  (s_mid, f_mid, valsToAdmin ms_mid.stack ++ base) := by
     ...
     exact .single .r_interp_flat
   ```
   And in `ax_misc_instr_reduces` (`Lemmas.lean:99`) and `block_case_reduces` (`Block.lean:285`), the interpreter execution hypothesis `_hbi : execBasicInstr s f ms bi = .ok (s_mid, f_mid, ms_mid)` is prefixed with an underscore (`_hbi`) and **never used in the proof**. We mechanize this exact vacuity pattern in Theorem `WasmExtrinsicIntrinsic.linobit_unconstrained_reduce_vacuity` ([`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L715-L719)).
4. **What IS genuinely proved in `linobit-corp/wasm-lean`**:
   - Pure stack-only `ReduceSimple` transitions (`r_nop`, `r_drop`, `r_select_true`, `r_select_false`, `r_unop`, `r_binop_ok`, `r_binop_trap`, `r_testop_i32`, `r_testop_i64`, `r_relop`, `r_br_if_false`, `r_br_if_true`, `r_if_true`, `r_if_false` in `WasmLean/Semantics/Reduce.lean:166-225`) have genuine side conditions (`evalUnop`, `evalBinop`, `evalTestop`, `evalRelop`), and their local progress and type-preservation lemmas in `WasmLean/Soundness/Progress.lean` and `WasmLean/Soundness/Preservation.lean` (`preservation_unop_constnum`, `preservation_binop_success`, `preservation_relop`, etc.) as well as the linear-memory byte lemmas in `WasmLean/Soundness/MemoryList.lean` are non-vacuous proofs.

---

#### 1.4 `aionescu/lean-wasm`, `argumentcomputer/Wasm.lean`, and `T-Brick/lean-wasm`

Basis: source

- **`aionescu/lean-wasm` (`66f1166f84a763b23475b0eb660153c72ec54d29`, 9 files, 1,458 LOC, 0 theorems, 8 active `sorry`s)**:
  - Defines an intrinsically-typed instruction GADT (`Wasm/IR.lean:38-80`):
    ```lean
    inductive Instr : InstrKind → List Ty → List (List Ty) → List Ty → List Ty → Type
    ```
    indexed by representation kind (`InstrKind := .src | .spec | .fast`), local variable context `locals : List Ty`, label stack context `labels : List (List Ty)`, input operand stack `stkIn : List Ty`, and output operand stack `stkOut : List Ty`.
  - Evaluates instructions over a heterogeneous operand stack `Stack (ts : List Ty) := HList Ty.type ts` (`Wasm/Eval/Common.lean:6`).
  - Compiles `.src` instructions to `.spec` (`Wasm/Eval/Spec.lean`) and `.fast` (`Wasm/Eval/Fast.lean`, which uses an explicit zipper continuation `LabelStack`), but leaves **8 active `sorry`s** (`Spec.lean:206, 240, 241` and `Fast.lean:204, 238, 239, 243, 244`) where Lean 4's dependent pattern matcher cannot unify stack-type indices containing `List.append` (`s' ++ s`) or `HList.take` / `HList.drop`.
- **`argumentcomputer/Wasm.lean` (`454172e1219ce648732211a7804829809dffd64d`, 23 files, 4,616 LOC, 0 theorems, 8 active `sorry`s)**:
  - Early Lean 4 (`nightly-2023-01-10`) executable prototype using a transformer stack `EngineM m := ExceptT Return $ ExceptT Continuation $ StateT (List StackEntry) $ StateT Frame $ StateT (Store m) $ Except EngineErrors` (`Wasm/Engine.lean:188`) with `partial def runOp` (`Engine.lean:778`).
  - `Store m` (`Engine.lean:180-182`) contains only `globals` and `func`—**linear memory is completely unimplemented**.
  - Contains 7 `sorry`s in binary decoding/encoding (`Wasm/Bytes.lean:333, 558, 560, 562, 577, 581, 583`) and 1 `sorry` in `Wasm/Engine.lean:143`, plus concrete arithmetic bugs: signed right shift `shr_s` (`Engine.lean:545-547`) computes `(x >>> k) ||| (x &&& (N / 2))` (preserving only the sign bit at its original position rather than sign-extending all shifted bits), and float equality (`Engine.lean:506`) compares raw bit patterns with the author comment `-- lmao even this isn't right because of +0 == -0`.
- **`T-Brick/lean-wasm` (`43b051f30b920e4d1253d83ae08b3dc83b4d6d88`, 44 files, 7,005 LOC, 12 theorems, 39 active `sorry`s)**:
  - Attempts a direct textbook transcription of the Wasm 2.0 specification (`Wasm/Syntax`, `Wasm/Validation`, `Wasm/Dynamics`, `Wasm/Binary`, `Wasm/Text`), but is unfinished and contains multiple soundness-breaking bugs:
    1. `Wasm/Dynamics.lean:43-49`: `Unop.ctz` and `Unop.popcnt` both invoke `Unsigned.clz c` (copy-paste error).
    2. `Wasm/Dynamics.lean:482-572`: The entire `Memory` step relation is commented out.
    3. `Wasm/Dynamics.lean:576-615`: `Instr : Step` only handles `numeric`, `reference`, `parametric`, `variable`, `table`, and `atomic`; it omits `memory`, `block`, `loop`, `wasm_if`, `br`, `br_if`, `br_table`, `wasm_return`, `call`, and `call_indirect`.
    4. `Wasm/Validation/Statics.lean:32`: `Typ.MatchSingle.refl` is written `{t1 t2 : Typ.{u}} → MatchSingle C t1 t2` with distinct unconstrained type variables `t1` and `t2`, allowing any value type to match any other value type.

---

### 2. Extrinsically-Typed vs. Intrinsically-Typed Wasm Semantics in Lean 4

Basis: source + execution ([`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L237-L721))

Across the six Lean 4 Wasm formalizations, two distinct representation paradigms appear:

| Architectural Dimension | Extrinsically-Typed Representation (`plum-umd/lean-wasm`, `cajal-technologies/talos`, `linobit-corp/wasm-lean`) | Intrinsically-Typed Representation (`aionescu/lean-wasm`) |
| :--- | :--- | :--- |
| **Instruction Syntax** | Simple inductive `Instr : Type`; binary/WAT decoders construct `Instr` directly without dependent type-checking during parsing. | Dependent GADT `IWasmInstr : List WasmTy → List WasmTy → Type`; binary decoding requires a dependent type-inference/elaboration pass. |
| **Operand Stack** | Homogeneous `List WasmVal` or `Array Value`. | Heterogeneous `HStack : List WasmTy → Type` (`HList WasmTy.denote`). |
| **Step Return Type** | `WasmStepOutcome` with 3 branches: `.next mem' stack'`, `.trap reason`, and `.stuckTypeMismatch`. | `Except TrapReason (LinearMem × HStack ts₂)` with 2 branches: `.ok (mem', stk')` and `.error reason`; `.stuckTypeMismatch` is unrepresentable. |
| **Frame & Stack Polymorphism** | Handled declaratively in `InstrTyped` (`InstrTyped .unreachable ts₁ ts₂`) or algorithmically via an abstract operand stack with unknown-bottom flag (`ellipses : Bool` in `plum-umd/lean-wasm`). | Requires explicit `List.append` indices (`IWasmInstr (s₁ ++ rest) (s₂ ++ rest)`) or universe-polymorphic quantifier wrappers, triggering dependent pattern-matching unification failures in Lean 4 (`aionescu/lean-wasm` `Spec.lean:206,240`). |
| **Separation Logic Integration** | Directly compatible with `iris-lean` (`Talos` `SmallStepLanguage.lean`), which expects a single uniform configuration type `Config α : Type`. | Incompatible with standard homogeneous `Language` signatures in Iris without sigma-type erasure `(Σ ts, HStack ts)`. |

In Part 1 of [`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L237-L721) (`namespace WasmExtrinsicIntrinsic`), we mechanize both representations over `i32`/`i64` arithmetic and byte-level `LinearMem` (with Wasm's exact unbounded-`Nat` effective address `effectiveAddr base offset := base.toNat + offset.toNat`) and prove their exact bridge:

1. **Single-step and multi-step lockstep erasure correspondence** (`stepIntrinsic_erases_to_extrinsic` at line 586, `execIntrinsicSeq_erases_to_extrinsic` at line 650):
   ```lean
   theorem stepIntrinsic_erases_to_extrinsic {ts₁ ts₂ : List WasmTy}
       (i : IWasmInstr ts₁ ts₂) (mem : LinearMem) (stk : HStack ts₁) :
       stepExtrinsic i.erase mem stk.toVals =
         eraseIntrinsicOutcome (stepIntrinsic i mem stk)
   ```
2. **Extrinsic syntactic progress and preservation via intrinsic reification** (`extrinsic_progress_and_preservation` at line 683):
   By lifting a well-typed extrinsic stack `StackTyped stk ts₁` into `HStack ts₁` via `HStack.ofTypedVals` (`toVals_ofTypedVals` at line 472) and lifting `InstrTyped i ts₁ ts₂` via `InstrTyped.exists_intrinsic` (line 665), extrinsic progress and preservation follow immediately from `stepIntrinsic_erases_to_extrinsic`: a well-typed instruction never reaches `.stuckTypeMismatch`, and either traps (`.trap r`) or transitions to `.next mem' stk'` with `StackTyped stk' ts₂`.

---

### 3. Cross-Prover Wasm Verification Ecosystem Comparison (`WasmCert-Coq`, `Iris-Wasm`, `WasmCert-Isabelle`, `SpecTec`)

Basis: source + documentation

Comparing the Lean 4 Wasm ecosystem against the established Coq/Rocq, Isabelle/HOL, and W3C `SpecTec` ecosystems clarifies what Lean 4 has already matched and what remains unique to Coq/Isabelle:

| System | Prover & Commit | Spec Version | Mechanized Metatheory & Program Logic | Key Architectural Comparison to Lean 4 (`plum-umd` & `talos`) |
| :--- | :--- | :--- | :--- | :--- |
| **`WasmCert-Coq` & `Iris-Wasm`** | Coq/Rocq (`58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`; `iris-wasm-opam` `57b05fb59a193078e5db4378cce164766e7b8a2c`, `iriswasm` `e37f8387a1171d104d78a2f77f9e637e090cf3d4`) | Wasm 2.0 (main); Wasm 1.0 + MSWasm / Wasm-GC in branches | Full syntactic type soundness (`t_preservation` in `theories/type_preservation.v:2082`, `t_progress_interp_ctx` in `theories/type_progress.v:23`); `stdpp` + `Iris` program logic (`iris-wasm`) with logical relations for robustness/encapsulation. | `WasmCert-Coq` has full syntactic `progress` + `preservation`, which `plum-umd/lean-wasm` has not yet completed. Conversely, `cajal-technologies/talos` in Lean 4.34.1 already ports the `Iris-Wasm` separation-logic paradigm to `iris-lean` (`WasmHeap.lean`, `WasmRules.lean`) and scales it to Wasm 3.0 `try_table` exceptions and `rustc`-compiled `.wasm` binaries. |
| **`WasmCert-Isabelle`** | Isabelle/HOL (`d9b4659c8b38879a5fc7e0213950751a61091908`) | Wasm 1.0 + Wasm 2.0 SIMD/bulk-memory extensions | Full `preservation` and `progress` (`WebAssembly/Wasm_Soundness.thy:5-34`), executable interpreter (`Wasm_Interpreter_Properties.thy`), and OCaml extraction. | Achieves full type soundness in ~12,500 LOC (vs. ~45,000 LOC in `WasmCert-Coq`) via Isabelle's `auto`/`blast` automation, but lacks a higher-order separation logic comparable to `Iris-Wasm` or `Talos` (`iris-lean`). |
| **W3C `SpecTec`** | Custom DSL (`WebAssembly/spec` Wasm 3.0) | Wasm 3.0 (`2026`) | Generates normative LaTeX/HTML prose, reference OCaml interpreter, and mechanized AST/typing definitions for **Coq, Isabelle, and Agda** (POPL 2024). | `SpecTec` does **not** currently have a Lean 4 backend; `plum-umd/lean-wasm` was authored directly against the Wasm 3.0 specification and validated against the 65,202-command Wasm 3.0 testsuite. |

---

### 4. Virtual & Sandboxed ISA Verification: Wasm vs. eBPF (`CertrBPF`, `Jitterbug`, `Kops`/`KinsnLean4`)

Basis: source + execution ([`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L988-L1196))

WebAssembly and Linux eBPF are the two dominant virtual/sandboxed ISAs in systems software, but their verification architectures partition safety obligations differently between **load-time static verification**, **runtime sandbox checks**, and **JIT refinement**:

| Verification Dimension | WebAssembly (`plum-umd/lean-wasm`, `cajal-technologies/talos`) | eBPF (`CertrBPF`/`CertFC`, `Jitterbug`, `Kops`/`KinsnLean4`) |
| :--- | :--- | :--- |
| **Machine Model** | Structured control-flow stack machine with separate activation call stack (cannot be overwritten by linear memory stores) and byte-addressed linear memories (`LinearMem`). | 11-register (`R0`–`R10`, where `R10` is read-only frame pointer) flat register machine with bounded loops, helper calls, and typed pointers (stack, packet, map, context). |
| **Load-Time Static Verifier** | Decidable syntactic/type validator (`validate : Module → Except String Unit` in `plum-umd/lean-wasm`): checks operand stack types, local initialization, label arities, and index bounds in $O(\text{code size})$. Does **not** prove absence of traps. | Path-sensitive abstract interpreter (`linux/kernel/bpf/verifier.c`; mechanized in Coq for rBPF by `CertrBPF` at `verifier/property/invariant.v:568` `verifier_inv_imply`): tracks 64-bit/32-bit value intervals (`smin`/`smax`, `umin`/`umax`, `var_off`), pointer tags, and packet bounds to **prove absence of runtime faults/UB before execution**. |
| **Out-of-Bounds Memory Access** | Checked at runtime (`ea + width ≤ mem.size` in unbounded `Nat`) or via virtual-memory guard pages; out-of-bounds access triggers a **deterministic `trap`** (`.terminated .unwind`). | Rejected statically at load time by the eBPF verifier (`CertrBPF` `isolation/Isolation2.v:28, 1968` `inv_avoid_step_undef`, `inv_avoid_bpf_interpreter_undef`). |
| **JIT Compilation Verification** | Typically verified via translation validation or compiler simulation (e.g., VeriWasm / Wasmtime Cranelift ISLE rules). | Verified per-instruction against target ISA semantics: `Jitterbug` (`uw-unsat/jitterbug` `racket/lib/spec/per-insn.rkt`) in Rosette/Serval for RV32/RV64/ARM32/ARM64/x86, and **`Kops` / `KinsnLean4`** (`eunomia-bpf/bpf-benchmark` `kinsn/lean/`) in **Lean 4.28.0**. |

#### Primary-Source Inspection of `Kops` / `KinsnLean4` (`eunomia-bpf/bpf-benchmark@d03e6742bd2a56b94448071b0439d67a6574e9a3`)

In `eunomia-bpf/bpf-benchmark/kinsn/lean/` (Lean `v4.28.0`, 3,519 declarations across `KinsnLean4/Kinsn/`, **0 `sorry`s, 0 custom axioms** verified in `KinsnLean4/AxiomCheck.lean`), Kops (`arXiv:2606.24213`) introduces a **dual-sequence virtual-ISA extension architecture**:
- Each custom kernel instruction (`kinsn`, such as `EXTR64`, `BFI64`, `MADD64`, `CSEL64`, `LDP64`, `STP64`, `PREFETCH`, `BARRIER`) carries:
  1. A **vanilla eBPF proof sequence** (`seq_proof`), which the unmodified Linux kernel eBPF verifier analyzes using its standard abstract-interpretation transfer functions; and
  2. A **target-specific native JIT sequence** (`seq_native` on ARM64 or x86-64).
- `KinsnLean4/Kinsn/Defs.lean` defines `KinsnEquiv` (`arm_refines` and `x86_refines`), and `KinsnLean4/Kinsn/ModuleCatalog.lean` proves `arm_jit_sound` and `x86_jit_sound` across 96 non-debug `kinsn` operations across 10 modules (`Barrier`, `Bitfield`, `Branch`, `Conditional`, `Endian`, `LoadStore`, `Multiply`, `Prefetch`, `Rotate`, `SIMD`).

In Part 3 of [`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L1006-L1196) (`namespace EbpfVerifierAndKopsBridge`), we prove that Kops's dual-sequence architecture is a direct instance of Anneal's `VerifiedChecker` and `Compiles` algebra:
- **`ebpfVerifiedChecker`** (line 1112): Formalizes a static eBPF divisor and packet-bounds checker (`ebpfVerifierCheck minPktLen`) as an Anneal `VerifiedChecker EbpfLang (fun _ => EbpfWellFormed minPktLen)`.
- **`kops_dual_sequence_jit_soundness`** (line 1182): Proves that if `(ebpfVerifiedChecker minPktLen).check seq_proof = true` and `Compiles EbpfLang NativeJitLang π_jit seq_proof seq_native` holds for a monotone `π_jit`, then `NativeJitLang.sem seq_native ≤ π_jit (EbpfWellFormed minPktLen)` follows directly by `Preorder.le_trans` without modifying the verifier.

---

### 5. Anneal Rust-to-Wasm (`wasm32-unknown-unknown` / `wasm32-wasip2`) Target Architecture and Semantic Pitfalls

Basis: source + execution ([`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L738-L985))

When Anneal targets WebAssembly (`wasm32-unknown-unknown` or `wasm32-wasip2`) as a compilation target (`Compiles MirLang WasmLang π p_mir p_wasm`) or lifts `.wasm` binaries into Lean 4 verification obligations, four subtle semantic boundaries arise between Rust MIR (`Trusted/MirSemantics.lean`) and WebAssembly (`WebAssembly 2.0/3.0 §4.4.7`). We mechanize all four in Part 2 of [`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean#L738-L985) (`namespace WasmTrapVsRustUb`):

#### 5.1 Wasm `trap` Is `.terminated .unwind` (`defined = True`), Not `Partial.ub` (`defined = False`)
- In Anneal's `SmallStepMachine` (`Trusted/StepResult.lean`), `.failed .ub` sets `PrefixOutcome.isSafe = False`, which makes `(BehaviorOf M p q).defined = False` (`Partial.ub`, the top element of the refinement preorder).
- In WebAssembly (`cajal-technologies/talos` `SmallStepOutcomeAdequacy.lean` and `plum-umd/lean-wasm` `Wasm/Reduction.lean`), a `trap` (`unreachable`, `divByZero`, `outOfBoundsMem`) is a **deterministic, memory-safe halting state** that preserves sandbox isolation. In Anneal's `StepResult`, a Wasm trap maps to `.terminated .unwind` (or a dedicated `.terminated (.trap reason)` constructor), which has `PrefixOutcome.isSafe = True` and therefore `(WasmLang.sem wprog q).defined = True` for **every** query `q` (proved in Theorem `wasm_trap_is_defined_not_ub` at line 828).

#### 5.2 The Directional Asymmetry Between Compiler Refinement (`Compiles`) and Contract Verification (`EnsuresNoTrap` vs. `EnsuresValueOrTrap`)
- **Compiler direction (`Compiles MirLang WasmLang`)**: Suppose a Rust MIR program `mprog` dereferences a raw pointer `*ptr` backed by an allocation of length `mprog.allocLen`. When `q.addr.toNat + 4 > mprog.allocLen`, `MirLoadMachine` steps to `.failed .ub`, so `¬ (MirLang.sem mprog q).defined` (`mir_oob_raw_load_is_ub` at line 844). Because `Partial.instPreorder` defines `x ≤ y` as `∀ hy : y.defined, ∃ hx : x.defined, x.val hx ≤ y.val hy`, source UB (`y.defined = False`) is refined by **any** target Wasm behavior—whether Wasm traps (`.terminated .unwind`) or silently reads unrelated bytes in linear memory! Consequently, `Compiles MirLang WasmLang π_mir_wasm mprog ⟨0⟩` holds unconditionally (`rustc_raw_load_to_wasm_compiles` at line 878).
- **Binary/Target verification direction (`WasmLang.sem wprog ≤ spec`)**: When Anneal verifies a compiled `.wasm` binary against a specification `spec` (as in `cajal-technologies/talos`), `WasmLang.sem wprog` is on the **left-hand side** of `≤` and has `defined = True`.
  - If the specification requires **total panic/trap freedom** (`EnsuresNoTrap`, where `val` requires `out ≠ .terminated .unwind`), any reachable Wasm trap **refutes** the specification (`wasm_trap_refutes_ensuresNoTrap` at line 958: `¬ (WasmLang.sem ⟨0⟩ q ≤ EnsuresNoTrap q)` when `¬ (q.addr.toNat + 4 ≤ q.mem.size)`).
  - If the specification permits panics/traps (`EnsuresValueOrTrap`, corresponding to Rust's safe partial correctness where unwinding/trapping does not violate memory safety), a Wasm trap **satisfies** the specification (`wasm_trap_satisfies_valueOrTrap` at line 968: `WasmLang.sem wprog ≤ EnsuresValueOrTrap`).

#### 5.3 Lack of Per-Allocation Provenance in Wasm Linear Memory
- Unlike Rust's abstract machine (Stacked Borrows / Tree Borrows in `MirSemantics.lean`), Wasm linear memory is a flat byte array `bytes : List UInt8` of size $N \times 65{,}536$ bytes.
- Theorem `wasm_linear_memory_lack_of_provenance` (line 915) proves that whenever a Rust raw pointer overflows its source allocation (`¬ (q.addr.toNat + 4 ≤ mprog.allocLen)`) but still falls within the allocated Wasm linear memory pages (`q.addr.toNat + 4 ≤ q.mem.size`), `MirLang` has Undefined Behavior (`¬ (MirLang.sem mprog q).defined`) while `WasmLoadMachine` **does not trap** and instead returns `∃ v, ReachesPrefix WasmLoadMachine ⟨0⟩ 1 (.start q) (.terminated (.normal v))` from the adjacent object in linear memory. Therefore, Wasm's linear-memory bounds check cannot be treated as a spatial memory-safety checker for individual Rust allocations.

#### 5.4 `wasm32` 32-Bit Pointer Wrapping (`i32.add`) vs. Unbounded `Nat` `memarg.offset`
- In WebAssembly (`WebAssembly 2.0/3.0 §4.4.7`, `plum-umd/lean-wasm` `Wasm/Stepper.lean`, and `cajal-technologies/talos` `SmallStep.lean`), the effective address of `i32.load offset` is defined in **unbounded natural numbers**:
  $$\mathrm{ea} = \mathrm{base.toNat} + \mathrm{offset.toNat}$$
  and traps if $\mathrm{ea} + \mathrm{width} > \mathrm{mem.size}$.
- However, on `wasm32`, Rust's `usize` is 32 bits (`BitVec 32`), and pointer arithmetic lowered to Wasm `i32.add` wraps modulo $2^{32}$ **before** the load instruction executes.
- Theorem `wasm32_u32_wrapping_vs_memarg_offset` (line 1002) proves on a 1-page memory (`mem.size = 65536`) with `base = 0xFFFF_FFF0#32` and `offset = 0x20`:
  1. Lowering the address calculation to `i32.add` (`base + 0x20#32 = 0x0000_0010#32`) followed by `i32.load offset=0` yields `effectiveAddr (base + off32) 0 + 4 = 20 ≤ 65536`, **silently reading address `0x10`** instead of trapping!
  2. Encoding `offset = 0x20` in Wasm's static `memarg.offset` immediate (`i32.load offset=0x20`) yields `effectiveAddr base 0x20 + 4 = 4294967316 > 65536`, **deterministically trapping**!
- Consequently, any Anneal verification pass over `rustc`-generated Wasm must model dynamic `i32.add` address calculations with modulo-$2^{32}$ bitvector arithmetic and reserve unbounded-`Nat` addition strictly for the instruction's static `memarg.offset` field.

#### 5.5 Recommended Lean 4 Wasm Foundation for Anneal
- Because Anneal is pinned to **Lean `v4.34.1`** and `cajal-technologies/talos` (`80644390de3ad4db3055445259a034413ae41577`) is **already built on Lean `v4.34.1`** with zero `sorry`s, zero custom axioms, an authoritative small-step semantics (`Wasm.SmallStep`) proved equivalent to its executable stepper (`step_sound`, `step_complete`), `iris-lean` separation logic (`WasmHeap.lean`, `WasmRules.lean`), and existing proofs of `rustc`-compiled `.wasm` programs, `cajal-technologies/talos` is the direct drop-in foundation for verifying Rust-compiled-to-Wasm artifacts in Anneal.
- If Anneal requires Wasm 3.0 module-validator soundness (`validate_sound`) or SIMD/GC reference-type semantics, `plum-umd/lean-wasm` (`d438fabdd6304bcbc72f211b9f532be76ebc7f29`, zero `sorry`s, zero custom axioms, mathlib-free) can be ported forward from Lean `v4.27.0` to `v4.34.1`.

## Boundaries

- **Global syntactic type soundness in `plum-umd/lean-wasm` (`not examined` / `unsupported` upstream)**: While `plum-umd/lean-wasm` proves executable validator soundness (`validate_sound : validate m = .ok () → m.Valid`), stepper soundness (`step_sound`, `runConfiguration_sound`), and local redex determinism (`reduces_deterministic`), it does not yet contain a mechanized proof of global syntactic type preservation (`ConfigStep c c' → c.Typed t → c'.Typed t`) or global progress (`c.Typed t → Terminal c ∨ ∃ c', ConfigStep c c'`).
- **Shared-memory concurrency (`Wasm threads` proposal) (`known not to apply`)**: Neither `plum-umd/lean-wasm` nor `cajal-technologies/talos` models concurrent multi-thread shared-memory execution (`memory.atomic.*` under the Wasm relaxed-memory model); `T-Brick/lean-wasm` defines syntax for `atomic` instructions (`Wasm/Syntax/Instr.lean`), but all atomic dynamic reduction rules in `T-Brick/lean-wasm` (`Wasm/Dynamics.lean:614`) are `sorry` stubs.
- **`linobit-corp/wasm-lean` `execBlock_sound` (`known not to apply` as a semantic correctness proof)**: As established in Finding 1.3 and mechanized in `WasmExtrinsicIntrinsic.linobit_unconstrained_reduce_vacuity`, `execBlock_sound` in `linobit-corp/wasm-lean` cannot be used as an authoritative interpreter correctness certificate for basic/memory/table instructions because `Reduce.r_interp_flat` has zero premises.

## Evidence

### Primary Repository Revisions and Files Examined
All repository metadata, line counts, theorem counts, and `sorry` audits were collected on `2026-10-29` and are preserved in [`support/source-manifest.json`](support/source-manifest.json):

1. **`plum-umd/lean-wasm`** (`d438fabdd6304bcbc72f211b9f532be76ebc7f29`):
   - `Wasm/Syntax/Types.lean`, `Wasm/Syntax/Instr.lean`: Wasm 3.0 AST and GC/exception/SIMD types.
   - `Wasm/Validation.lean` & `Wasm/ExecutableValidation.lean`: Declarative `Module.Valid` and computable `validate`.
   - `Wasm/ExecutableValidationSoundness.lean:1000`: `theorem validate_sound`.
   - `Wasm/Reduction.lean:23-68`: `Reduces`, `reduce?`, `reduce_iff`, `reduces_deterministic`.
   - `Wasm/Stepper.lean:107-305`: `StepResult`, `step_sound`, `run_sound`.
   - `Wasm/Configuration.lean:181-225`: `ConfigStep`, `stepConfiguration_sound`, `runConfiguration_sound`.
   - `Wasm/Host.lean:133-345`: `HostCallFrame`, `resumeHostCall`, `stepWithHost_sound`.
2. **`cajal-technologies/talos`** (`80644390de3ad4db3055445259a034413ae41577`):
   - `interpreter/Interpreter/Wasm/SmallStep.lean:337-350, 2548, 3255, 3455, 3496, 3525`: `Config α`, `step`, `inductive Step`, `step_sound`, `step_complete`, `Step.deterministic`.
   - `codelib/CodeLib/SepLogic/SmallStepLanguage.lean`, `SmallStepOutcomeAdequacy.lean`, `WasmHeap.lean`, `WasmRules.lean`: `iris-lean` instantiation, `MemoryKey := Nat × UInt32`, partial and total adequacy over `ObservableOutcome`.
   - `programs/lean/Project/`: Verified Rust-to-Wasm modules (`SwapElements.lean`, `SwapElementsOpt3.lean`, `Mergesort.lean`, `GcdStdio.lean`, `HexEncodeStdio.lean`, `HexDecodeStdio.lean`, `RustVec.lean`, `RustU64.lean`, `RustArray.lean`).
3. **`linobit-corp/wasm-lean`** (`6d612a510d145950838ec193e9ae0b75a7c881ef`):
   - `WasmLean/Semantics/Reduce.lean:256-343`: Zero-premise constructors `r_table_get`, `r_table_set`, `r_call_indirect`, `r_load`, `r_store`, `r_memory_size`, `r_memory_grow`, `r_memory_fill`, `r_memory_copy`, `r_cvtop`, and `r_interp_flat`.
   - `WasmLean/Correctness/Lemmas.lean:73-112` & `WasmLean/Correctness/Block.lean:285, 825`: `misc_instr_reduces`, `ax_misc_instr_reduces`, `block_case_reduces`, and `execBlock_sound`.
   - `WasmLean/Soundness/Progress.lean`, `WasmLean/Soundness/Preservation.lean`, `WasmLean/Soundness/MemoryList.lean`: Non-vacuous local `ReduceSimple` and `MemoryList` proofs.
4. **`aionescu/lean-wasm`** (`66f1166f84a763b23475b0eb660153c72ec54d29`):
   - `Wasm/IR.lean:38-80`, `Wasm/Eval/Common.lean:6`, `Wasm/Eval/Spec.lean:206, 240, 241`, `Wasm/Eval/Fast.lean:204, 238, 239, 243, 244`.
5. **`argumentcomputer/Wasm.lean`** (`454172e1219ce648732211a7804829809dffd64d`):
   - `Wasm/Engine.lean:143, 180-188, 506, 545-547, 778`, `Wasm/Bytes.lean:333, 558-583`.
6. **`T-Brick/lean-wasm`** (`43b051f30b920e4d1253d83ae08b3dc83b4d6d88`):
   - `Wasm/Validation/Statics.lean:32`, `Wasm/Dynamics.lean:43-49, 482-572, 576-615`.
7. **Comparison Wasm & eBPF Repositories**:
   - `WasmCert/WasmCert-Coq` (`58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`): `theories/type_preservation.v:2082`, `theories/type_progress.v:23`; `iris-wasm-opam` (`57b05fb59a193078e5db4378cce164766e7b8a2c`) / `logsem/iriswasm` (`e37f8387a1171d104d78a2f77f9e637e090cf3d4`).
   - `WasmCert/WasmCert-Isabelle` (`d9b4659c8b38879a5fc7e0213950751a61091908`): `WebAssembly/Wasm_Soundness.thy:5-34`.
   - `future-proof-iot/CertFC` (`75690097c946c555cc4ce1e69d13ef86dc738180`): `verifier/property/invariant.v:568`, `isolation/Isolation2.v:28, 1968`.
   - `uw-unsat/jitterbug` (`78d1e75ad506498b585fbac66985ff9d9d05952d`): `racket/lib/bpf-common.rkt`, `racket/lib/spec/per-insn.rkt`.
   - `eunomia-bpf/bpf-benchmark` (`d03e6742bd2a56b94448071b0439d67a6574e9a3`): `kinsn/lean/KinsnLean4/Kinsn/Defs.lean`, `ModuleCatalog.lean`, `AxiomCheck.lean`.

### Preserved Lean 4.34.1 Verification Probe
The standalone file [`support/lean_wasm_and_ebpf_bridge_probe.lean`](support/lean_wasm_and_ebpf_bridge_probe.lean) (1,250 lines, SHA-256 `62dfcee3ef3883a48da7abda9fed30bb8097460d65959f76af8c674bdf2298a4`) was verified under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with zero `sorry`s and zero custom axioms (`#guard_msgs` + `#print axioms` on all 12 headline definitions/theorems):
- `WasmExtrinsicIntrinsic.stepIntrinsic_erases_to_extrinsic` (`[propext]`)
- `WasmExtrinsicIntrinsic.execIntrinsicSeq_erases_to_extrinsic` (`[propext]`)
- `WasmExtrinsicIntrinsic.extrinsic_progress_and_preservation` (`[propext]`)
- `WasmExtrinsicIntrinsic.linobit_unconstrained_reduce_vacuity` (`[]`)
- `WasmTrapVsRustUb.wasm_trap_is_defined_not_ub` (`[propext]`)
- `WasmTrapVsRustUb.rustc_raw_load_to_wasm_compiles` (`[propext]`)
- `WasmTrapVsRustUb.wasm_linear_memory_lack_of_provenance` (`[propext, Quot.sound]`)
- `WasmTrapVsRustUb.wasm_trap_refutes_ensuresNoTrap` (`[propext]`)
- `WasmTrapVsRustUb.wasm_trap_satisfies_valueOrTrap` (`[propext]`)
- `WasmTrapVsRustUb.wasm32_u32_wrapping_vs_memarg_offset` (`[]`)
- `EbpfVerifierAndKopsBridge.ebpfVerifiedChecker` (`[propext, Quot.sound]`)
- `EbpfVerifierAndKopsBridge.kops_dual_sequence_jit_soundness` (`[propext, Quot.sound]`)

## Revalidation

1. **Re-verify the standalone Lean 4.34.1 probe**:
   ```console
   ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768 \
     reports/lean4-wasm-formalizations-and-virtual-isa-verification-2026/support/lean_wasm_and_ebpf_bridge_probe.lean
   ```
   A passing run exits with code `0` and produces no output, confirming all proofs and `#guard_msgs` axiom checks (`[propext]`, `[Quot.sound]`, or `[]`, with no `sorryAx`).

2. **Re-check whether `plum-umd/lean-wasm` has added global syntactic type preservation/progress**:
   Inspect `Wasm/Configuration.lean` and `Wasm/` in `plum-umd/lean-wasm` for any theorem relating `ConfigStep c c'` and `Configuration.Typed`.

3. **Re-check whether `linobit-corp/wasm-lean` has eliminated `Reduce.r_interp_flat`**:
   Inspect `WasmLean/Semantics/Reduce.lean` for `r_interp_flat` and `WasmLean/Correctness/Lemmas.lean` for `misc_instr_reduces` to see whether `execBasicInstr` has been connected to premises on `Reduce` constructors.

*Authored by an AI agent acting on joshlf's behalf.*
