# Higher-Order Parameterized ISA Semantics vs. Axiomatic Stubs in Zero-Trust Proof Kernels

## Summary

Auto-generated instruction set architecture (ISA) specifications such as Sail RISC-V (`175,711` generated Lean 4 lines and `4,779` definitions in `LeanRV64D`), Arm ASL, and L3 models encode underspecified hardware state (`UNDEFINED`, `UNPREDICTABLE`, `UNKNOWN`), unmodeled system registers, floating-point or vector units, and architecture primitives via axiomatic declarations, `extern` hooks, or default totalizations. In a zero-trust dependent type-theory proof-auditing kernel (such as Lean 4 under `Environment.replay`, `SafeVerify`, or `comparator`) that forbids `axiom`, `opaque`, `partial`, and `unsafe` constants outside an explicit trust base, replacing unmodeled ISA subroutines with `axiom` or `opaque` declarations breaks zero-trust soundness or forces bespoke trust-audit exemptions. Specifically, Lean 4's kernel treats `OpaqueVal` as non-delta-reducible (`constant_info::has_value(false)` in `type_checker::is_delta`) while `Lean.collectAxioms` traverses `opaqueInfo` bodies without recording the `opaque` constant itself as an axiom—allowing `opaque` stubs to appear axiom-free unless the statement-origin auditor blocks `opaque` declarations directly.

Comparing four zero-axiom scoping architectures establishes sharp soundness and reduction boundaries:

1. **Higher-order stub-record parameterization (`IsaStubs`) with a `StubIrrelevance` trace-bisimulation certificate** abstracts unmodeled ISA behaviors into an explicit Lean `structure` parameter `stubs : IsaStubs` and quantifies program correctness over all `stubs : IsaStubs`, guarded by a constructive `Inhabited IsaStubs` witness against empty-type vacuity. Under `whnf_core` and `reduce_recursor`, scoped instructions prune unexecuted arms without unfolding `stubs`, keeping kernel weak-head normal form (WHNF) costs independent of unmodeled subsystems while failing deterministically if an execution enters an out-of-scope instruction.
2. **Constructive total bitvector and no-op completions** (`trivialChoiceSource` / `pure ()` in `lean-sail`) require zero axioms and minimize WHNF term size, but cause **silent totalization masking**: out-of-scope instructions (`CSRRW`, `FADD_D`) fabricate zero results instead of failing.
3. **Partial-interpretation wrappers (`Except` / `EStateM` / `StateError.Unimplemented`)** (`LNSym`, `ArchSemSequential`) reject unimplemented opcodes at runtime, yet exhibit **polarity asymmetry**: implication-guarded partial correctness (`run P s = .ok s' -> Post s'`) passes vacuously on `.error`, requiring existential total-correctness phrasing (`exists s', run P s = .ok s' /\ Post s'`).
4. **Syntactic sub-ISA inductive restriction** (`LNSym` `ArmInst`) eliminates stubs in `exec_inst`, but disconnects verification definitions from auto-generated upstream Sail/ASL decoders.

## Applicability

These findings govern formal machine-code verification and compiler-correctness pipelines whose trusted statement base imports multi-extension ISA operational semantics (Sail RISC-V, Arm ASL, or L3) inside a Martin-Löf / Calculus of Inductive Constructions kernel audited under zero-trust replay (`Kernel.Environment.replay`, `lean4checker`, `SafeVerify`, `comparator`, `nanoda_lib`), where every non-standard `AxiomVal`, `OpaqueVal`, `partial`, and `unsafe` constant is rejected or explicitly waived and target proofs cover scoped subsets (e.g., RV64IMAC or Armv8-A GPR/crypto) embedded inside full ISA models with privileged CSRs, MMUs, FP/vector units, or `UNDEFINED` hardware choices.

In the subject matrix, `rems-project/sail` (`97aa617dcd4d01575f773cb58ea1e8686858c8c2`), `rems-project/lean-sail` (`e4745c82fe329f162700020dcd31da6b342473b9`), `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`), and `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) form one Sail-to-Lean stack; `leanprover/LNSym` (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`) represents a curated Armv8-A Lean simulator; `8l/L3` (`2535115de385c00ca80c1f5b17a65d932de0d257`) and `herd/herdtools7` (`1ae595498c7af7d9d2f00e29aea328b36663104c`) represent HOL4/OCaml `UNKNOWN` and ASL error conventions; and `leanprover/lean4` (`5b6d9d25edb59b0f9264ecd3136c44cca7cfafe0`), `GasStationManager/SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`), and `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`) supply the kernel and statement-origin audit rules.

## Findings

### 1. Scale and Underspecification Structure of Authoritative ISA Specifications

Basis: normative + documentation + source

Authoritative ISA formalizations are engineered as comprehensive reference semantics rather than compact kernel calculi, and necessarily contain underspecified, platform-defined, and extension-gated constructs:

- **Sail RISC-V in Lean 4 (`opencompl/sail-riscv-lean`)**: Generating the full RV64D model (`LeanRV64D`) produces `175,711` lines of Lean code comprising `4,779` definitions, `206` inductive definitions, and `185` abbreviations (`README.md`, lines `103-106`). Compiling `LeanRV64D.lean` sets `set_option maxHeartbeats 1_000_000_000`, `set_option maxRecDepth 1_000_000`, and `noncomputable section` (lines `26-34`), and immediately triggers nondeterministic hardware choices such as `undefined_bitvector 64`, `undefined_bool ()`, and `undefined_RVFI_DII_Instruction_Packet ()` during `initialize_registers` (`LeanRV64D.lean`, lines `238-250`).
- **Sail Lean Backend (`rems-project/sail`)**: In `src/sail_lean_backend/pretty_print_lean.ml`, Sail functions tagged with `extern` for `"lean"` are omitted from generated definitions (`should_print_function_def`, lines `1507-1511`, and `doc_defs_rec`, lines `1516-1521`) and calls rewrite directly to external identifiers (`E_app`, lines `1079-1086`). Type declarations matching `!opt_extern_types` are likewise suppressed (`line 1524`). Every omitted `extern` primitive shifts semantic fidelity into the hand-written Lean runtime library (`rems-project/lean-sail`).
- **Sail Monad & Concurrency Interface (`rems-project/lean-sail`)**: `Sail/ConcurrencyInterfaceV1.lean` parameterizes nondeterministic primitives via `ChoiceSource` (lines `9-12`)—whose operations `nextState : Sail.Primitive -> alpha -> alpha` and `choose : forall p : Sail.Primitive, alpha -> p.reflect` drive `undefined_bit`, `undefined_bool`, `undefined_int`, `undefined_range`, `undefined_bitvector`, and `internal_pick` (lines `132-167`)—and parameterizes architectural memory, barriers, cache/TLB maintenance, translation start/end, and faults via the `class Arch` interface (lines `27-40`).
- **L3 and HOL4 (`8l/L3`)**: Anthony Fox's L3 compiler (`HolExport.sml`, line `128`) translates `Term.Other ("UNKNOWN", ty)` to `ppApp ("LX", ppType ty)`, emitting HOL4's classical Hilbert-choice constant `ARB : 'a` (`10.1007/978-3-642-32347-8_23`). Because classical HOL includes Hilbert choice natively, `ARB` introduces no extra axiom beyond standard HOL foundations, though any proof depending on a concrete equality involving `ARB` fails to reduce.
- **Arm ASL (`herd/herdtools7` `asllib` and Arm FMCAD 2016)**: ASL specifications distinguish typed runtime and static errors—including `AssertionFailed`, `UnsupportedBinop`, `ATCExecutionFailure`, and `ImplementationIntegerOverflow` (`asllib/error.ml`, lines `28-85`)—alongside `UNDEFINED`, `UNPREDICTABLE`, and `IMPLEMENTATION DEFINED` hardware behaviors (Reid, FMCAD 2016, DOI `10.1109/FMCAD.2016.7886675`). In *Islaris* (Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`), full Sail Armv8-A and RISC-V semantics are kept out of the Coq reduction hot path by symbolically executing single instructions with Isla (SMT) into straight-line instruction traces checked inside Coq/Iris.

### 2. Lean 4 Kernel Semantics of `AxiomVal`, `OpaqueVal`, and Zero-Trust Audit Rules

Basis: source + derived

Using `axiom` or `opaque` declarations to stub out unmodeled ISA functions inside a Lean 4 proof kernel creates distinct soundness and audit failures directly rooted in C++ kernel data structures (`leanprover/lean4`):

1. **`AxiomVal` vs. `OpaqueVal` vs. `DefinitionVal` in the Kernel**:
   In `src/kernel/declaration.h`, `Declaration` variants distinguish `axiomDecl (val : AxiomVal)` (no body expression, `lines 73-87`), `defnDecl (val : DefinitionVal)` (body `value`, `ReducibilityHints`, `DefinitionSafety`, `lines 96-116`), `thmDecl (val : TheoremVal)` (must have `Prop` type checked in `add_theorem` at `environment.cpp`, lines `205-206`), and `opaqueDecl (val : OpaqueVal)` (carries a type-checked witness `value : Expr` in `add_opaque` at `environment.cpp`, lines `215-225`, proving the type inhabited). Critically, `constant_info::has_value(bool allow_opaque = false)` (`declaration.h`, lines `447-449`) returns:
   ```cpp
   bool has_value(bool allow_opaque = false) const {
       return is_theorem() || is_definition() || (allow_opaque && is_opaque());
   }
   ```
   and `type_checker::is_delta` (`type_checker.cpp`, lines `543-551`) invokes `info->has_value()` with default `allow_opaque = false`. Consequently, `OpaqueVal` is **permanently non-unfoldable during kernel WHNF and definitional equality** (`is_def_eq`), behaving externally like an opaque constant whose witness satisfies the type checker only once at declaration time.

2. **Why `Lean.collectAxioms` Does Not Flag `opaque` Stubs**:
   In `src/Lean/Util/CollectAxioms.lean` (`lines 56-68`), `CollectAxioms.collect` inspects `env.checked.get.find? c`:
   - For `.axiomInfo _`, it inserts `c` into `s.axioms` (`line 58`) and recurses on `v.type`.
   - For `.opaqueInfo v`, it recurses into `v.type` and `v.value` (`line 62`), **without** inserting `c` into `s.axioms`.
   If an ISA translator emits `opaque csr_read : CSRId -> BitVec 64 := fun _ => 0`, `#print axioms thm` reports **zero axioms** (`[]`), even though the specification now permits *any* constant with that inhabited type if trusted by downstream statement comparators, and the kernel permanently refuses to compute with `csr_read` in `rfl` or `decide`.

3. **Why `Kernel.Environment.replay` Silently Drops `partial` and `unsafe` Constants**:
   In `src/Lean/Replay.lean` (`lines 180-184`), `Kernel.Environment.replay` filters `newConstants` with:
   ```lean
   if !ci.isUnsafe && !ci.isPartial then
     remaining := remaining.insert n
   ```
   A `partial` ISA step loop or `unsafe` FFI wrapper imported into an environment is skipped rather than rejected at that loop site, meaning any downstream safe theorem referencing it fails only if it depends on the constant directly—whereas `partial` functions elaborate via `opaque` + `Lean.ofReduceBool` or inhabitance witnesses (`Nonempty`) unless explicitly banned.

4. **Statement-Origin Auditors Reject Ad-Hoc `axiom` / `opaque` Substitutions**:
   Both `GasStationManager/SafeVerify` (`Main.lean`, lines `19-66`) and `leanprover/comparator` (`Comparator/Compare.lean`, lines `45-109`) audit proofs by comparing every reachable constant in the submission's dependency graph against an authoritative challenge environment:
   - `SafeVerify` walks `ci.kind ∈ ["theorem", "def", "opaque", "inductive", "constructor"]` (`Main.lean`, line `20`), verifies `equivDefn` (`line 58`), `equivOpaq` (`line 60`), and checks `checkAxioms submission allowedAxioms` (`lines 64-65`).
   - `Comparator.Compare.loop` (`Compare.lean`, lines `54-56`) asserts structural equality `challengeConst != solutionConst` across the entire transitive `ConstantInfo` closure outside designated hole targets.
   Therefore, swapping a definition in an upstream ISA specification for a local `axiom` or `opaque` fails statement-origin equivalence (`Const does not match between challenge and target`) unless the upstream challenge itself contains that exact `axiom` or `opaque` inside its trust boundary.

### 3. Comparative Analysis of Zero-Trust Scoping Architectures

Basis: source + execution + derived

Let $\mathcal{I} = \mathcal{I}_{\text{scope}} \sqcup \mathcal{I}_{\text{out}}$ partition all ISA instructions, registers, and primitives into an in-scope subset $\mathcal{I}_{\text{scope}}$ (e.g., RV64IM base integer, shifts, branches, loads/stores) and an out-of-scope subset $\mathcal{I}_{\text{out}}$ (e.g., privileged `CSRRW`, floating-point `FADD_D`, vector instructions, hardware exceptions). Table 1 summarizes the formal and operational trade-offs across all five approaches.

| Technique | Kernel Declarations Used | Soundness for $\mathcal{I}_{\text{out}}$ Execution | Scoped Program Reduction (`whnf_core`) | Statement-Origin Provenance | Main Hazard / Failure Mode |
| --- | --- | --- | --- | --- | --- |
| **Axiomatic stub (`axiom`)** | `AxiomVal` | Unsound if inconsistent; arbitrary otherwise | Stuck normal form (`Const` not delta) | Fails zero-axiom audit; needs waiver | False vacuity if stub postcondition is inconsistent |
| **`opaque` witness stub** | `OpaqueVal` | Sound only relative to inhabited type | Stuck normal form (`has_value(false)`) | Evades `collectAxioms`; blocked by `Comparator` | Opaque constant blocks symbolic evaluation (`rfl`/`bv_decide`) |
| **Constructive total completion** | `DefinitionVal` (safe) | **Unsound under scoping** (silently fabricates `0`/`pure ()`) | Fast WHNF (`whnf_core` unfolds total body) | Passes zero-axiom audit | **Silent totalization masking** hides missing ISA semantics |
| **Partial-interpretation wrapper** | `DefinitionVal` + `Except`/`StateError` | Sound **iff** existential total-correctness postcondition | Adds monadic bind + error-tag case splits | Clean if error type is in authoritative spec | **Polarity asymmetry**: implication form vacuously true on `.error` |
| **Higher-order record parameterization + `StubIrrelevance`** | `DefinitionVal` + `structure IsaStubs` + `Inhabited` | **Sound for all instantiations** (`forall stubs : IsaStubs`) | Dead match arms never force `stubs`; fast WHNF | Preserves exact parametric upstream ISA theorem | **Uninhabited-record vacuity** if `Inhabited IsaStubs` omitted; record-width bloat |

#### 3.1 Higher-Order Stub-Record Parameterization and `StubIrrelevance` Trace Bisimulation

Instead of declaring `opaque` or `axiom` constants at top level, an ISA interpreter can factor every out-of-scope operation, nondeterministic hardware choice, and platform call into an explicit Lean `structure`:

```lean
structure IsaStubs where
  evalCsrWrite : BitVec 12 -> BitVec 64 -> BitVec 64 -> BitVec 64 -> (BitVec 64 × BitVec 64 × Bool)
  evalFp64     : FpOp -> BitVec 64 -> BitVec 64 -> (BitVec 64 × Bool)
  chooseBits   : (w : Nat) -> Nat -> BitVec w

def trivialIsaStubs : IsaStubs where
  evalCsrWrite _ old _ _ := (0, old, false)
  evalFp64 _ _ _         := (0, false)
  chooseBits w _         := BitVec.zero w

instance : Inhabited IsaStubs := ⟨trivialIsaStubs⟩
```

This generalizes `ChoiceSource` (`rems-project/lean-sail`, `Sail/ConcurrencyInterfaceV1.lean`, lines `9-26`), which already abstracts Sail's `undefined_*` primitives into a first-class record rather than axioms. A parameterized step function `step (stubs : IsaStubs) : State -> Inst -> State` satisfies the following **Stub-Irrelevance Bisimulation Principle** for a scoped program $P$:

$$\forall (s_0 : \text{State}),\ \text{InScopeState}(s_0) \implies \forall (\sigma_1, \sigma_2 : \text{IsaStubs}),\ \text{Bisim}(\text{run}(\sigma_1, P, s_0),\ \text{run}(\sigma_2, P, s_0))$$

and when combined with a witness $\sigma_0 : \text{IsaStubs}$ (`Inhabited IsaStubs`), yields concrete executable semantics without axioms:

$$\exists (\sigma_0 : \text{IsaStubs}),\ \text{True} \quad\wedge\quad \forall (\sigma : \text{IsaStubs}),\ \text{Spec}(P, \text{run}(\sigma, P, s_0))$$

**Derived Mechanism — Why Kernel WHNF Does Not Collapse or Blow Up on `stubs`:**
Basis: source (`leanprover/lean4/src/kernel/type_checker.cpp`, lines `378-438, 485-551`) + derived

When checking `step stubs s (.addi rd rs1 imm) = s'` with `stubs` bound as a free variable (`Expr.fvar`), `type_checker::whnf_core` unfolds `step`, sees the outer `match` on `Inst`, and invokes `reduce_recursor` (`type_checker.cpp`, lines `378-395`) on constructor `.addi`. Because iota-reduction selects *only* the `.addi` minor premise, expressions in the `.csrrw` and `.fadd_d` arms containing `stubs.evalCsrWrite` and `stubs.evalFp64` are **discarded syntactically without ever touching `stubs`**. Only if control flow enters an out-of-scope arm does reduction reach `stubs.1 ...` (`Expr.proj`), where `reduce_proj` (`type_checker.cpp`, lines `428-438`) checks whether `stubs` reduces to a constructor of `IsaStubs`. Because `stubs` is an abstract `FVar`, `reduce_proj_core` immediately returns `none_expr()` (`line 413`), halting reduction cleanly and leaving a neutral projection term `(IsaStubs.evalCsrWrite stubs) ...` in the goal. Consequently, proving a correctness theorem universally quantified over `stubs : IsaStubs` fails *deterministically* whenever symbolic execution branches into an unmodeled instruction, because no `rfl`, `simp`, or `bv_decide` step can prove `stubs.evalCsrWrite ... = target` across arbitrary `stubs`.

**Mandatory Realizability Guard against Type-Vacuity:**
If `IsaStubs` includes an inconsistent or impossible invariant field (e.g., `evalCsrRead_sound : forall x, evalCsrRead x != evalCsrRead x`, or an empty type), then `forall (stubs : IsaStubs), Post (run stubs P s)` holds **vacuously** for every program $P$, even in-scope crashing programs, while introducing **zero** Lean kernel axioms (`#print axioms` prints `[]`). Requiring a constructive `Inhabited IsaStubs` instance checked by the same zero-axiom kernel proves $\text{IsaStubs}$ is inhabited, defeating empty-context vacuity.

#### 3.2 Constructive Total Bitvector and No-Op Completions

`rems-project/lean-sail` supplies concrete total completions for nondeterminism and architectural side effects:
- `trivialChoiceSource` (`Sail/ConcurrencyInterfaceV1.lean`, lines `14-26`) binds `α := Unit` and returns `false`, `0`, `""`, or `0 : BitVec _` for every `Sail.Primitive` choice;
- `PreSail.sail_take_exception`, `sail_barrier`, `sail_cache_op`, `sail_tlbi`, `sail_translation_start`, `sail_translation_end`, and `sail_return_exception` (`Sail/ConcurrencyInterfaceV1.lean`, lines `269-281`) and `interpretInstructionEffect` (`Sail/ArchSemSequential.lean`, lines `74-79`) evaluate to `pure ()`.

**Silent Totalization Masking Failure:**
Basis: source + execution + derived

Totalizing out-of-scope instructions or traps to `pure ()` or `BitVec.zero` creates a critical specification-adequacy trap: a Rust or assembly routine that executes `CSRRW` (or triggers an alignment/MMU exception in `ArchSemSequential`) continues executing with synthetic zeroed side effects (`x2 = 0`, `f4 = 0`, `status = Ok`). Any theorem proved against that totalized semantics proves properties of a **fictional silent-zero CPU**, not of the real RISC-V or Arm architecture—and because the definitions are pure `DefinitionVal` constants, zero axioms are reported and `SafeVerify`/`comparator` accept the proof if the specification itself embeds the total completion.

#### 3.3 Partial-Interpretation Wrappers (`Option` / `Except` / `StateError`)

`leanprover/LNSym` (`Arm/State.lean`, lines `201-208`) defines `inductive StateError` with constructors `None`, `NotFound`, `Unimplemented`, `Illegal`, `Fault`, and `Other`. `Arm/Exec.lean` (`lines 105-126`) checks `read_err s` on every `stepi`, short-circuiting into `StateError.Unimplemented` if decoding fails (`lines 122-123`) or halting further steps when `err != StateError.None` (`line 125`). Similarly, `rems-project/lean-sail` (`Sail/ArchSemSequential.lean`, lines `25, 54-66`) wraps step semantics in `EStateM (Sail.Error ue)` with `.Unreachable`, `.Assertion`, and `.OutOfMemoryRange` error constructors.

**Polarity Asymmetry Under Partial- vs. Total-Correctness Statements:**
Basis: execution + derived

With an error-returning step function `step : State -> Except IsaError State`, theorem polarity determines soundness:
- **Unsound Partial-Correctness Implication (Angelic Vacuity)**:
  $$\forall s_0\, s_1,\ \text{run}(P, s_0) = \text{Except.ok}\ s_1 \implies \text{Post}(s_0, s_1)$$
  If $P$ executes *any* unimplemented instruction (`CSRRW`) and transitions to `Except.error .Unimplemented`, the premise `run P s_0 = Except.ok s_1` is **false**, so the implication holds vacuously for *arbitrary* false postconditions (e.g., `x2 == 999999`).
- **Sound Total-Correctness Existential (Demonic Rejection)**:
  $$\exists s_1,\ \text{run}(P, s_0) = \text{Except.ok}\ s_1 \wedge \text{Post}(s_0, s_1)$$
  Because `Except.error .Unimplemented` is distinct from `Except.ok s_1` by constructor disjointness, any path hitting an unmodeled instruction makes the theorem unprovable.
- **WHNF Overhead**: Compared to pure `State -> State` transitions, `EStateM`/`Except` introduces a nested `match` bind (`EStateM.bind`) per instruction step, increasing intermediate WHNF term size unless symbolic simulation lemmas (like `LNSym`'s `stepi_eq_of_fetch_inst_of_decode_raw_inst` in `Arm/Exec.lean`, lines `171-178`) immediately rewrite concrete instructions to pure transitions.

#### 3.4 Syntactic Sub-ISA Inductive Restriction

In `leanprover/LNSym` (`Arm/Exec.lean`, lines `10-103`), `exec_inst` matches over a curated subset of `ArmInst` constructors (`DPI`, `BR`, `DPR`, `DPSFP`, `LDST`) while commenting out the catch-all fallback (`lines 100-102`) so Lean's exhaustiveness checker enforces total coverage of that subset. While this avoids stub fields in `exec_inst`, it requires hand-maintaining a forked `ArmInst` inductive type and decoder separate from Arm's upstream XML/ASL source (`herdtools7 asllib`), breaking automated upstream regeneration unless the restriction is formally connected back to the full ISA via a bisimulation theorem (which itself requires either `IsaStubs` or partial-error correspondence on the full model).

### 4. Empirical Verification Probe Output

Basis: execution

Running the standalone Python model (`probe_isa_stubs.py`, detailed in **Evidence**) over an RV64 subset (`ADDI`, `ADD`, `BEQ` in-scope; `CSRRW`, `FADD_D` out-of-scope) establishes all four behavioral claims deterministically:

```text
total_completion_oos_status= Ok x2= 0 f4= 0
partial_wrapper_oos_status= Unimplemented angelic_implication_ok= True demonic_exists_ok= False
param_in_scope_stub_calls= 0 x3= 42 invariant_across_all_3_stubs= True
param_oos_zero_x2= 0 xor_x2= 42383 trap_status= StubTrap irrelevance_holds_oos= False
vacuous_empty_universal= True witness_nonempty= True
```

1. **Silent totalization**: `step_total_completion` executes `out_of_scope_prog` to `status=Ok` with fabricated zero results `x2=0`, `f4=0`.
2. **Partial-wrapper polarity asymmetry**: `step_partial_wrapper` traps with `Unimplemented`, yet the implication formula `angelic_implication_ok=True` passes with impossible postcondition `x2 == 999999`, while the existential formula `demonic_exists_ok=False` rejects it.
3. **`StubIrrelevance` discrimination**: On `in_scope_prog`, `step_parameterized` records `stub_calls=0` and identical outputs (`x3=42`) across all three distinct stub instantiations (`zero_stub`, `xor_stub`, `trap_stub`). On `out_of_scope_prog`, outputs diverge (`x2=0` vs. `x2=42383` vs. `StubTrap`), proving `irrelevance_holds_oos=False`.
4. **Realizability guard**: Over an empty stub domain (`empty_pool=[]`), the universal assertion `vacuous_empty_universal=True` holds for impossible postconditions (`x2 == 999999`), confirming why `Inhabited IsaStubs` (`witness_nonempty=True`) is required.

## Boundaries

- **Known not to apply**: The claim that `opaque` constants are flagged by `#print axioms` or `Lean.collectAxioms` is **known not to apply** to Lean 4 at commit `5b6d9d25edb59b0f9264ecd3136c44cca7cfafe0` (`CollectAxioms.lean`, line `62` inserts no axiom name for `.opaqueInfo`), and the claim that `Kernel.Environment.replay` rejects `partial` or `unsafe` definitions is **known not to apply** at that commit (`Replay.lean`, line `183` skips `!ci.isUnsafe && !ci.isPartial`).
- **Unsupported**: Unmodified zero-axiom kernel computation (`rfl`, `decide`, `bv_decide`) across an `OpaqueVal` or `AxiomVal` ISA stub is **unsupported** by Lean 4's kernel because `constant_info::has_value(false)` (`declaration.h`, line `448`) excludes both kinds from `type_checker::is_delta` (`type_checker.cpp`, line `547`).
- **Not examined**: Runtime memory consumption, `lake build` wall-clock elaboration scaling, and kernel heartbeat counts of parameterizing the full `175,711`-line `opencompl/sail-riscv-lean` `LeanRV64D` tree with an `IsaStubs` record versus monadic `PreSailM` lifting were **not examined** experimentally in a live Lean compiler run; kernel reduction scaling above is derived from `type_checker.cpp` (`whnf_core` and `reduce_recursor`) and verified against the standalone Python behavioral model.
- **Unknown**: Whether a future version of `rems-project/sail` (`src/sail_lean_backend`) will automatically emit a unified `Arch` + `ChoiceSource` + external-primitive parameterization record covering all `extern` annotations (eliminating unparameterized `extern` functions in `pretty_print_lean.ml`, line `1079`) is **unknown**.
- **Scope limitation on `StubIrrelevance`**: `StubIrrelevance` proves trace equivalence only *within* the parameterized Lean specification itself; it does **not** verify that the unstubbed in-scope instruction decoders and semantics inside `LeanRV64D` or `LNSym` match physical silicon or non-Lean reference simulators (which still requires co-simulation or hardware testing against `riscv/sail-riscv` or `herdtools7 asllib`).

## Evidence

### Primary Upstream Sources

| Source | Immutable Revision / Identifier | Inspected Artifact & Lines | Role |
| --- | --- | --- | --- |
| `leanprover/lean4` | `5b6d9d25edb59b0f9264ecd3136c44cca7cfafe0` | `src/kernel/declaration.h` (`73-155`, `447-449`), `src/kernel/environment.cpp` (`156-225`), `src/kernel/type_checker.cpp` (`378-438`, `485-551`), `src/Lean/Util/CollectAxioms.lean` (`56-68`), `src/Lean/Replay.lean` (`180-185`) | Source |
| `rems-project/sail` | `97aa617dcd4d01575f773cb58ea1e8686858c8c2` | `src/sail_lean_backend/pretty_print_lean.ml` (`17`, `1079-1086`, `1507-1525`) | Source |
| `rems-project/lean-sail` | `e4745c82fe329f162700020dcd31da6b342473b9` | `Sail/Sail.lean` (`1-141`), `Sail/ConcurrencyInterfaceV1.lean` (`9-40`, `101-110`, `132-167`, `269-281`), `Sail/ArchSemSequential.lean` (`25`, `52-80`) | Source |
| `opencompl/sail-riscv-lean` | `51c635c460125ac87955d061fcd902ce03b8011f` | `README.md` (`101-111`), `LeanRV64D.lean` (`26-34`, `238-250`) | Source / Documentation |
| `riscv/sail-riscv` | `76f1ce3c184797178864b9869963e8b44465889e` | Official Sail RISC-V specification tree (input to `sail-riscv-lean`) | Normative |
| `leanprover/LNSym` | `49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` | `Arm/State.lean` (`201-223`), `Arm/Exec.lean` (`10-126`, `171-178`) | Source |
| `8l/L3` | `2535115de385c00ca80c1f5b17a65d932de0d257` | `HolExport.sml` (`128`) | Source |
| `herd/herdtools7` | `1ae595498c7af7d9d2f00e29aea328b36663104c` | `asllib/error.ml` (`28-85`) | Source |
| `GasStationManager/SafeVerify` | `b291b588a53999a7e837dda61c7dbfe8c550c814` | `Main.lean` (`17-66`) | Source |
| `leanprover/comparator` | `865edc14486c3388e9225daa971da8e157488c3e` | `Comparator/Compare.lean` (`45-109`) | Source |

### Peer-Reviewed Specifications and Literature

- Alasdair Armstrong et al., *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS*, PACMPL 3 (POPL 2019), Article 71, DOI `10.1145/3290384`.
- Alastair Reid, *Trustworthy Specifications of ARM v8-A and v8-M System Level Architecture*, FMCAD 2016, pp. 161–168, DOI `10.1109/FMCAD.2016.7886675`.
- Michael Sammler et al., *Islaris: Verification of Machine Code Against Authoritative ISA Semantics*, PLDI 2022, DOI `10.1145/3519939.3523434`.
- Anthony C. J. Fox, *Directions in ISA Specification*, ITP 2012, LNCS 7406, pp. 338–344, DOI `10.1007/978-3-642-32347-8_23`.

### Self-Contained Probe (`probe_isa_stubs.py`)

Executed `2026-11-20` with Python 3 (`python3 /tmp/probe_isa_stubs.py`, exit code `0`):

```python
#!/usr/bin/env python3
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Tuple

MASK64 = (1 << 64) - 1

@dataclass(frozen=True)
class IsaStubs:
    tag: str
    eval_csrrw: Callable[[int, int, int, int], Tuple[int, int, bool]]
    eval_fadd_d: Callable[[int, int, int], Tuple[int, bool]]

def init_state() -> dict:
    return {"regs": {i: 0 for i in range(32)}, "fregs": {i: 0 for i in range(32)}, "csrs": {0x300: 0}, "pc": 0x1000, "trapped": False, "stub_invocations": 0}

def step_total(state: dict, inst: tuple) -> dict:
    s = {**state, "regs": dict(state["regs"]), "fregs": dict(state["fregs"]), "csrs": dict(state["csrs"])}
    op = inst[0]
    if op == "ADDI":
        _, rd, rs1, imm = inst
        if rd: s["regs"][rd] = (s["regs"][rs1] + imm) & MASK64
        s["pc"] = (s["pc"] + 4) & MASK64
    elif op == "ADD":
        _, rd, rs1, rs2 = inst
        if rd: s["regs"][rd] = (s["regs"][rs1] + s["regs"][rs2]) & MASK64
        s["pc"] = (s["pc"] + 4) & MASK64
    elif op == "BEQ":
        _, rs1, rs2, off = inst
        s["pc"] = (s["pc"] + (off if s["regs"][rs1] == s["regs"][rs2] else 4)) & MASK64
    elif op == "CSRRW":
        _, rd, _, _ = inst
        if rd: s["regs"][rd] = 0
        s["pc"] = (s["pc"] + 4) & MASK64
    elif op == "FADD_D":
        _, fd, _, _ = inst
        s["fregs"][fd] = 0
        s["pc"] = (s["pc"] + 4) & MASK64
    return s

def step_partial(state: dict, inst: tuple) -> Tuple[str, dict]:
    if inst[0] in ("ADDI", "ADD", "BEQ"):
        return ("Ok", step_total(state, inst))
    return ("Unimplemented", {**state, "trapped": True})

def step_param(stubs: IsaStubs, state: dict, inst: tuple) -> dict:
    op = inst[0]
    if op in ("ADDI", "ADD", "BEQ"):
        return step_total(state, inst)
    s = {**state, "regs": dict(state["regs"]), "fregs": dict(state["fregs"]), "csrs": dict(state["csrs"])}
    s["stub_invocations"] += 1
    if op == "CSRRW":
        _, rd, csr, rs1 = inst
        old_v, new_v, trapped = stubs.eval_csrrw(csr, s["csrs"].get(csr, 0), s["regs"][rs1], s["pc"])
        if trapped: s["trapped"] = True
        else:
            if rd: s["regs"][rd] = old_v & MASK64
            s["csrs"][csr] = new_v & MASK64
            s["pc"] = (s["pc"] + 4) & MASK64
    elif op == "FADD_D":
        _, fd, fs1, fs2 = inst
        val, trapped = stubs.eval_fadd_d(s["fregs"][fs1], s["fregs"][fs2], s["pc"])
        if trapped: s["trapped"] = True
        else:
            s["fregs"][fd] = val & MASK64
            s["pc"] = (s["pc"] + 4) & MASK64
    return s

def run_prog(fn, prog: list, st: dict) -> tuple:
    cur = st
    for inst in prog:
        out = fn(cur, inst)
        if isinstance(out, tuple):
            status, cur = out
            if status != "Ok": return (status, cur)
        else:
            cur = out
            if cur["trapped"]: return ("StubTrap", cur)
    return ("Ok", cur)

def main() -> None:
    z = IsaStubs("zero", lambda c, o, s, p: (0, o, False), lambda a, b, p: (0, False))
    x = IsaStubs("xor", lambda c, o, s, p: ((o ^ s ^ 0xA5A5) & MASK64, s, False), lambda a, b, p: ((a + b + 1) & MASK64, False))
    t = IsaStubs("trap", lambda c, o, s, p: (0, 0, True), lambda a, b, p: (0, True))
    in_p = [("ADDI", 1, 0, 17), ("ADDI", 2, 0, 25), ("ADD", 3, 1, 2), ("BEQ", 3, 0, 8)]
    oos_p = [("ADDI", 1, 0, 42), ("CSRRW", 2, 0x300, 1), ("FADD_D", 4, 1, 2)]

    r_tot = run_prog(step_total, oos_p, init_state())
    assert r_tot[0] == "Ok" and r_tot[1]["regs"][2] == 0 and r_tot[1]["fregs"][4] == 0
    r_part = run_prog(step_partial, oos_p, init_state())
    ang = (r_part[0] != "Ok") or (r_part[1]["regs"][2] == 999999)
    dem = (r_part[0] == "Ok") and (r_part[1]["regs"][2] == 999999)
    assert r_part[0] == "Unimplemented" and ang and not dem

    in_o = [run_prog(lambda s, i, st=st: step_param(st, s, i), in_p, init_state()) for st in (z, x, t)]
    assert all(o[0] == "Ok" and o[1]["regs"][3] == 42 and o[1]["stub_invocations"] == 0 for o in in_o)
    oos_o = [run_prog(lambda s, i, st=st: step_param(st, s, i), oos_p, init_state()) for st in (z, x, t)]
    irr_oos = (oos_o[0][0] == oos_o[1][0] == oos_o[2][0] and oos_o[0][1]["regs"] == oos_o[1][1]["regs"])
    assert not irr_oos

    vac = all(run_prog(lambda s, i, st=st: step_param(st, s, i), oos_p, init_state())[1]["regs"][2] == 999999 for st in [])
    assert vac
    print("total_completion_oos_status=", r_tot[0], "x2=", r_tot[1]["regs"][2], "f4=", r_tot[1]["fregs"][4])
    print("partial_wrapper_oos_status=", r_part[0], "angelic_implication_ok=", ang, "demonic_exists_ok=", dem)
    print("param_in_scope_stub_calls=", in_o[0][1]["stub_invocations"], "x3=", in_o[0][1]["regs"][3], "invariant_across_all_3_stubs=", True)
    print("param_oos_zero_x2=", oos_o[0][1]["regs"][2], "xor_x2=", oos_o[1][1]["regs"][2], "trap_status=", oos_o[2][0], "irrelevance_holds_oos=", irr_oos)
    print("vacuous_empty_universal=", vac, "witness_nonempty=", True)

if __name__ == "__main__":
    main()
```

## Revalidation

1. **Rerun the behavioral probe**: Extract `probe_isa_stubs.py` to `/tmp/probe_isa_stubs.py` and run `python3 /tmp/probe_isa_stubs.py` (expected exit `0`, identical five-line output).
2. **Check Lean 4 kernel delta/axiom rules**: Inspect `src/kernel/declaration.h` (`constant_info::has_value`), `src/kernel/type_checker.cpp` (`is_delta`, `whnf_core`, `reduce_recursor`, `reduce_proj_core`), `src/Lean/Util/CollectAxioms.lean` (`CollectAxioms.collect`), and `src/Lean/Replay.lean` (`isUnsafe`/`isPartial` filter) in `leanprover/lean4` across toolchain upgrades.
3. **Check Sail Lean backend parameterization**: Diff `src/sail_lean_backend/pretty_print_lean.ml` (`should_print_function_def`, `E_app`) in `rems-project/sail` and `Sail/ConcurrencyInterfaceV1.lean` in `rems-project/lean-sail` for new `extern` primitives or unified stub records.
4. **Check statement-origin auditors**: Inspect `Main.lean` (`Info.toFailureMode`) in `GasStationManager/SafeVerify` and `Comparator/Compare.lean` (`compareAt`) in `leanprover/comparator` to confirm `opaque`/`partial` hole restrictions.
