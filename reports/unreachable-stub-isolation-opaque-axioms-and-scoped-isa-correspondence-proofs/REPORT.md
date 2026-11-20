# Unreachable-Stub Isolation, Opaque Declarations, and Scoped ISA Correspondence Proofs in Zero-Axiom Trust Boundaries

## Summary

Whole-architecture instruction-set specifications extracted from Sail or Arm Architecture Specification Language (ASL) into Lean 4 couple integer and privileged execution to out-of-scope external primitives—including Berkeley SoftFloat floating-point routines (`riscv_f16Add` through `riscv_f64roundToInt`), load-reserved/store-conditional reservation hooks, entropy sources, and implementation-defined (`IMPDEF`) callbacks—inside one monolithic `fetch`-`decode`-`execute` transition function. How out-of-scope primitives are stubbed determines both machine-checkable zero-axiom compliance and Pollack-consistency (whether the proved theorem means what an auditor reads):

1. **`axiom` declarations break zero-axiom gates indiscriminately.** `Lean.collectAxioms` (`src/Lean/Util/CollectAxioms.lean`) walks `type` and `value` of every referenced constant. Declaring SoftFloat or platform externs as `axiom` (as `opencompl/sail-riscv-lean` does with 75 `axiom`s in `LeanRV64D/RiscvExtras.lean`) contaminates `#print axioms` for every theorem mentioning `try_step` or `execute`, even when floating-point execution is architecturally disabled (`mstatus.FS = 0b00`).
2. **`opaque` and `partial def` declarations evade `#print axioms` and kernel replay while leaving uninterpreted specification holes.** Bodyless `opaque f : A → B` elaborates via `default_or_ofNonempty%` (`mkInhabitantFor`) to `Declaration.opaqueDecl` backed by `Inhabited.default` (zero axioms when `B` is constructively inhabited) or `Classical.choice` (`Nonempty`), and `partial def` compiles to the same kernel `opaqueDecl`. `Lean.collectAxioms` omits `ConstantInfo.opaqueInfo` names, and replay checkers (`Environment.replay`, `lean4checker`, `Lean4Lean`) accept `opaqueDecl`, yet the kernel blocks delta-reduction (`hasValue = false` unless `allowOpaque := true`). In specifications, `opaque` permits congruence tautologies (`f x = f x` across models sharing a stub), premise vacuity or uninstantiability in guards/decoders, and native-versus-kernel divergence under `@[extern]`.
3. **Bare total dummy definitions (`def stub _ := default`) permit silent reliance on fabricated outputs.** If a scope predicate omits an entry path—such as gating RISC-V floating-point exclusion solely on `mstatus.FS = 0b00` without excluding `Ext_Zfinx`, which runs `riscv_f32*` ops on `X` registers while `mstatus.FS = 0b00`—a transparent dummy unfolds in the kernel to `0`, letting proofs that accidentally rely on `0` pass undetected.
4. **Parameterized stub records with constructive unreachable-stub observational irrelevance (`∀ stubA stubB, InScope s → scopedExec stubA k s = scopedExec stubB k s`) strictly dominate all three alternatives.** Bundling out-of-scope primitives into an inhabited `Stubs` record with `dummyStubs : Stubs := default` uses zero custom axioms and zero `opaqueInfo` constants, forces the kernel to reject any leaked path via an unprovable `stubA.op ... = stubB.op ...` goal over distinct free variables, runs ordinary verification on the concrete `scopedExec dummyStubs`, and transfers correspondence universally to any compliant `realImpl : Stubs`.

## Applicability

These findings apply to ISA specifications, binary lifters, compiler backends, and kernel/hypervisor models verified in Lean 4 under strict zero-custom-axiom trust boundaries (permitting at most Lean's foundational `propext`, `Quot.sound`, and optionally `Classical.choice`, alongside human and automated auditing of theorem statements).

The eight subjects in `REPORT.json` span two layers:

- **Kernel and proof-auditing substrate:** `leanprover/lean4` (`450d6b121a45a48ffc58a83c921c813dffb259cb`) defines kernel declaration checks (`src/kernel/environment.cpp`), delta-reduction (`src/kernel/type_checker.cpp`), `opaque` and `partial` elaboration (`src/Lean/Elab/DefView.lean`, `src/Lean/Elab/PreDefinition/Main.lean`, `src/Lean/Elab/PreDefinition/MkInhabitant.lean`), and axiom collection (`src/Lean/Util/CollectAxioms.lean`). `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`), `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`), and `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`) implement environment replay, challenge-solution statement auditing, and mechanized kernel typechecking.
- **Sail ISA extraction pipeline and RISC-V case study:** `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`) defines the authoritative Sail RV32/RV64 specification, compiled by `rems-project/sail` (`97aa617dcd4d01575f773cb58ea1e8686858c8c2`, `src/sail_lean_backend/`) against `rems-project/lean-sail` (`079463134b9c50450b8393e1566a09fc492a34d9`) to generate `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`).

Within the corpus, this report complements `lean4-kernel-soundness-criticisms-defeq-pathologies-and-lean4lean-checkers`, `minimal-tcb-verification-spines-and-statement-adequacy-architectures`, `proof-kernels-opaque-interfaces-and-adversarial-spec-hardening`, and `reference-model-bisimulation-executable-semantics-and-differential-oracles` by isolating `Declaration.opaqueDecl` mechanics, Sail `extern` lowering, RISC-V `mstatus.FS` versus `Ext_Zfinx` gating, and constructive stub-irrelevance proofs.

The constructive irrelevance pattern transfers directly to Armv8-A/v9-A ASL extractions (stubbing SVE/SME FPUs, cryptographic blocks, or `IMPLEMENTATION_DEFINED` callbacks) and conceptually to Coq/Rocq section variables and Isabelle/HOL locales, subject to the prover-specific kernel boundaries noted under **Boundaries**.

## Findings

### 1. Out-of-Scope Primitives in Monolithic Extracted ISA Specifications

Basis: source + documentation

Sail (`rems-project/sail`) and Arm ASL organize architectural semantics around an extensible decoded-instruction sum (`union clause instruction = ...`) and clause-distributed execution (`function clause execute ...`) invoked from a unified fetch-decode-execute step (`try_step` / `run_hart_active`). In `rems-project/sail` (`src/sail_lean_backend/sail_plugin_lean.ml:176-245`, `src/sail_lean_backend/pretty_print_lean.ml:1507-1546`), the `"merge_function_clauses"` pass folds all enabled extensions into one closed Lean inductive `instruction` and one monolithic `execute (merge_var : instruction) : SailM ExecutionResult` function (`LeanRV64D/InstsEnd.lean`, `LeanRV64D/Step.lean:332-490`).

When Sail binds primitive operations to foreign C symbols via `val name = extern "..." : typ` without an inline Lean operator mapping (`pretty_print_lean.ml:1079-1098`), `should_print_function_def` (`pretty_print_lean.ml:1507-1511`) suppresses body emission for `"lean"` externs and defers to handwritten support modules. In `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`), two support modules illustrate opposite compromises:

- **`LeanRV64D/RiscvExtras.lean` (lines 16–112)** defines 5 total I/O/formatting stubs (`print_bits`, `print_string`, `prerr_string`, `putchar`, `string_of_int`), **8 platform and reservation `axiom` declarations** (`plat_term_write`, `plat_term_read`, `load_reservation`, `match_reservation`, `cancel_reservation`, `valid_reservation`, `get_16_random_bits`, `sys_enable_experimental_extensions` at lines 31–41), and **67 Berkeley SoftFloat `axiom` declarations** (`riscv_f16Add` through `riscv_f64roundToInt` at lines 46–112, e.g., `axiom riscv_f64Add : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)` at line 54).
- **`LeanRV64D/FakeReal.lean` (lines 6–65)** aliases Sail's mathematical `real` to hardware `Float` (`abbrev real := Float`), delegates `sqrt_real := Float.sqrt` and `real_power := Float.pow` to Lean core `@[extern]` `opaque` C bindings, and defines unsound dummy operations `round_down (x : real) : Int := x.toUInt64.toNat` (mapping negative reals to `0`), `round_up (x : real) : Int := round_down (x + 0.5)` (misrounding integers and fractions below `0.5`), and `random_real (_ : Unit) : real := 34`.

Because `LeanRV64D.Functions.try_step` (`LeanRV64D/Step.lean:417-490`) references `run_hart_waiting` (`valid_reservation`) and `run_hart_active` (`execute`, which dispatches into `FextInsts`, `DextInsts`, `ZfhInsts`, and `VextFpInsts`), **every theorem whose statement mentions `try_step` transitively pulls all 75 custom axioms from `RiscvExtras.lean` and all `FakeReal` definitions into its axiom footprint**, even when proving properties restricted to `RV64IMAC` integer execution.

### 2. Lean 4 Kernel Declaration Taxonomy: `axiom`, `opaque`, `partial`, `extern`, and Total Definitions

Basis: source + derived

In `leanprover/lean4` (`450d6b121a45a48ffc58a83c921c813dffb259cb`), surface declarations elaborate to kernel `Declaration` values (`src/Lean/Declaration.lean:163-171`) stored as `ConstantInfo` (`src/Lean/Declaration.lean:406-415`):

| Surface construct | Kernel `ConstantInfo` | Kernel checks body? | Kernel $\delta$-reduces (`is_delta`)? | Reported by `#print axioms` (`collectAxioms`)? | Native compiler (`@[extern]` / `_unsafe_rec`) |
| --- | --- | --- | --- | --- | --- |
| `axiom f : T` | `.axiomInfo` | No (`T : Sort u` only; `environment.cpp:156-162`) | Never (`hasValue = false`) | **Yes**: inserts `f` into `s.axioms` (`CollectAxioms.lean:57-59`) | Uncompilable unless `@[extern]` (`Elab/Declaration.lean:136-137`) |
| `opaque f : T := e` | `.opaqueInfo` | **Yes**: checks `e : T` (`environment.cpp:215-227`) | **Never** (`has_value(false) = false`; `declaration.h:447-449`, `type_checker.cpp:543-551`) | **No** for `f`; walks `T` and `e` (`CollectAxioms.lean:62`) | Compiles `e` unless `@[extern]` or `@[implemented_by]` |
| `opaque f : T` (no `:=`) | `.opaqueInfo` | **Yes**: synthesizes `e` via `default_or_ofNonempty%` (`DefView.lean:187-199`, `MkInhabitant.lean:58-62`) | **Never** | **Zero axioms** if `Inhabited` succeeds; `Classical.choice` only on `Nonempty` fallback | Compiles `default` (or invokes linked `@[extern]` C function) |
| `partial def f x := body` | `.opaqueInfo` (+ `unsafe` `f._unsafe_rec`) | **Yes**, on dummy `mkInhabitantFor`, **not** `body` (`PreDefinition/Main.lean:20-36`, `Basic.lean:285-297`) | **Never** (`f` is `.opaqueInfo`) | **Zero axioms** if codomain constructively `Inhabited`; ignores `body`'s axioms | Executes `f._unsafe_rec` (`DefinitionSafety.partial`), which may diverge |
| `@[irreducible] def f : T := e` | `.defnInfo` (`ReducibilityHints.regular`) | **Yes** (`environment.cpp:184-193`) | **Yes**: kernel ignores `@[irreducible]` (`Declaration.lean:38-45`) | Walks `T` and `e` | Compiles `e` |
| `def f : T := e` (total) | `.defnInfo` | **Yes** (`environment.cpp:184-193`) | **Yes** (`has_value() = true`) | Walks `T` and `e` (zero axioms if constructive) | Compiles `e` (unless `@[extern]` / `@[implemented_by]`) |

Three kernel/elaborator mechanisms govern trust-boundary audits:

1. **Zero-axiom synthesis in bodyless `opaque` (`DefView.lean:187-199`, `MkInhabitant.lean:31-62`):** Omitting `:= val` triggers `mkDefViewOfOpaque`, inserting `default_or_ofNonempty%`. `mkInhabitantFor` introduces local `Inhabited` instances for parameters `xs` (`withInhabitedInstances xs`) and tries `mkInhabitantForAux?` with `useOfNonempty := false` (`Inhabited.default`) before `useOfNonempty := true` (`Classical.ofNonempty`). Because `BitVec w`, `Bool`, `Nat`, `Unit`, products, and `StateT σ (Except ε) α` (for inhabited `ε` or `α`) have constructive `Inhabited` instances, changing all 75 `axiom` stubs in `LeanRV64D/RiscvExtras.lean` to `opaque` causes `#print axioms` to report **zero axioms**—not even `Classical.choice`.
2. **`partial def` compiles to `Declaration.opaqueDecl` (`PreDefinition/Main.lean:20-36`):** `addAndCompilePartial` sends `Declaration.opaqueDecl` with `mkInhabitantFor` to the kernel (discarding the recursive body from the logical environment) while compiling `f._unsafe_rec` (`DefinitionSafety.partial`) for native execution. As documented in `Lean4Lean/Verify/Axioms.lean:38-40, 123-128, 255-257`, no nontrivial property of a `partial def` is provable in the kernel without adding an explicit `axiom` equating it to a total twin (`axiom normalize_eq : normalize = Total.normalize`).
3. **`ReducibilityHints.opaque` vs `Declaration.opaqueDecl` (`Declaration.lean:38-45` vs `declaration.h:447-449`):** `ReducibilityHints.opaque` on `.defnInfo` merely delays unfolding order during `is_def_eq`, whereas `ConstantInfo.opaqueInfo` sets `hasValue (allowOpaque := false) = false`, causing `type_checker::is_delta` (`type_checker.cpp:543-551`) to return `none_constant_info()` and block kernel unfolding unconditionally.

### 3. Audit-Boundary Transparency Risks of `opaque` and `partial` Declarations in Specifications

Basis: source + derived

Replacing `axiom` stubs with `opaque` or `partial def` declarations to pass a `#print axioms` check creates four specification-integrity hazards—concrete instances of Pollack-inconsistency (Wiedijk, DOI `10.1016/j.entcs.2012.06.008`), where a kernel-checked theorem validates a statement weaker than its surface reading:

1. **Invisibility to `#print axioms`, environment replay, and challenge comparators:**
   - `CollectAxioms.collect` (`CollectAxioms.lean:62`) recurses on `v.type` and `v.value` of `.opaqueInfo v` without recording `c` in `s.axioms`.
   - `Lean.Kernel.Environment.replay` (`src/Lean/Replay.lean:100-101, 183`, used by `lean4checker`) replays `.opaqueInfo` via `addDecl (.opaqueDecl info)`—confirming only that its hidden `default` witness inhabits `info.type`—and skips `ci.isUnsafe` and `ci.isPartial` declarations entirely.
   - `leanprover/comparator` (`Comparator/Axioms.lean:43-46`, `Comparator/Util.lean:13-15`, `tests/projects/opaque_value/`) inspects `info.value? (allowOpaque := true)` to stop an untrusted *solution* from smuggling axioms inside a fresh `opaque`, yet when an `opaque` stub sits in the trusted *challenge* (`Challenge.lean`), `Comparator/Compare.lean:54` matches `challengeConst == solutionConst` and reports success without flagging uninterpreted specification symbols.
2. **Reflexivity and congruence tautologies across shared stubs:**
   If a fast ISA model `fastStep` and an extracted Sail model `sailStep` share `opaque riscv_f64Add : BitVec 3 → BitVec 64 → BitVec 64 → BitVec 5 × BitVec 64`, a bisimulation theorem `∀ s, fastStep s = sailStep s` discharges the `FADD.D` branch by `rfl` (`congrArg`), because `riscv_f64Add rm a b = riscv_f64Add rm a b` holds for any uninterpreted constant. `#print axioms` reports zero axioms even though IEEE 754 addition is completely unverified.
3. **Premise vacuity and uninstantiability in guards, decoders, and predicates:**
   In conditional correspondence theorems of the form `∀ s s', InScope s → sailStep s = .ok s' → implStep s = .ok s'`, defining `InScope` over a `partial def` decoder (`decode bytes = some (.ADDI ...)`) or declaring a placeholder specification guard `opaque ValidFpRounding : BitVec 3 → Prop` blocks kernel reduction on concrete states $s_0$. Even though `ValidFpRounding rm` is internally backed by `default : Prop := True`, `is_delta` refuses to unfold it, rendering `InScope s₀` unprovable for every concrete binary image without introducing a new assumption.
4. **Native-versus-kernel semantic divergence under `@[extern]` (`ExternAttr.lean:61-73`, `Float/Float.lean:193-365`):**
   Tagging `opaque riscv_f64Add` with `@[extern "c_softfloat_f64_add"]` links Berkeley SoftFloat into compiled `lake exe` test binaries—allowing `riscv-arch-test` suites to pass 100% of floating-point vectors natively—while the Lean kernel still sees an uninterpreted `opaqueInfo` symbol.

### 4. Failure Modes of Bare Total Dummy Definitions Without Irrelevance Isolation

Basis: source + derived

Replacing `axiom` or `opaque` externs with unparameterized total dummy definitions—such as `def riscv_f32ToI32 (_ : BitVec 3) (_ : BitVec 32) : BitVec 5 × BitVec 32 := (0#5, 0#32)`—eliminates both custom axioms and `opaqueInfo` constants, leaving pure `.defnInfo` declarations. Without an observational irrelevance theorem, however, kernel transparency creates the dual failure mode: **silent proof reliance on fabricated return values**.

The `F` versus `Zfinx` extension rules in `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`) exhibit this hazard directly:

- In `model/extensions/FD/fext_insts.sail:479-532`, single-precision instructions (`FSQRT.S`, `FCVT.W.S`, `FADD.S`) are gated by `when haveSingleFPU()`, which holds whenever `currentlyEnabled(Ext_F)` **or** `currentlyEnabled(Ext_Zfinx)` is true.
- Setting `mstatus.FS = 0b00` (`Off`) disables `Ext_F`, trapping `F` instructions to `Illegal_Instruction` when `Ext_Zfinx` is absent.
- Under `Ext_Zfinx` ("Floating-Point in Integer Registers", `model/extensions/FD/fdext_regs.sail:282-288, 312-318`), however, `mstatus.FS` is hardwired to `0b00` while `F` instructions execute directly on `X` registers (`X(fregidx_to_regidx(i))[31..0]`).
- If an engineer scopes an "integer-only" RV64 theorem using only `s.mstatus.FS = 0b00` (omitting `hartSupports Ext_Zfinx = false`), a bare dummy `riscv_f32ToI32 _ _ := (0#5, 0#32)` unfolds during `FCVT.W.S` to write `0` to `X(rd)` and `0#5` to `fflags`. A false theorem claiming zero-register preservation or trap-freedom on `mstatus.FS = 0b00` then typechecks cleanly in the Lean kernel while failing on compliant `Zfinx` hardware.

### 5. Parameterized Stub Bundles and Constructive Unreachable-Stub Observational Irrelevance

Basis: derived + source

To achieve zero custom axioms, zero `opaqueInfo` constants in the specification cone, transparent concrete evaluation, and machine-checked immunity to dummy values simultaneously, out-of-scope primitives are isolated via a **Parameterized Stub Bundle + Constructive Observational Irrelevance** discipline:

1. **Bundle out-of-scope primitives into a plain `structure` with a total `default` witness:**
   ```lean
   structure SoftFloatStubs where
     f32Add   : BitVec 3 → BitVec 32 → BitVec 32 → BitVec 5 × BitVec 32
     f32ToI32 : BitVec 3 → BitVec 32 → BitVec 5 × BitVec 32
     f64Add   : BitVec 3 → BitVec 64 → BitVec 64 → BitVec 5 × BitVec 64
     deriving Inhabited

   def dummySoftFloat : SoftFloatStubs := default
   ```
   Parameterize the ISA step explicitly as `step (stubs : SoftFloatStubs) (s : HartState) : Except Trap HartState` (or via `ReaderT SoftFloatStubs` in `SailM`), and define `scopedStep := step dummySoftFloat`. Every constant is a transparent `.inductInfo` or `.defnInfo`.

2. **Prove single-step constructive observational irrelevance:**
   ```lean
   theorem step_stub_irrelevant
       (stubA stubB : SoftFloatStubs) (s : HartState)
       (h_scope : InScope s) :
       step stubA s = step stubB s
   ```
   Inside this proof, `stubA` and `stubB` are distinct universally quantified free variables (`Expr.fvar`). Neither delta-reduction nor reflexivity can equate `stubA.f32ToI32 rm x` with `stubB.f32ToI32 rm x`. The kernel accepts `step_stub_irrelevant` if and only if `h_scope : InScope s` refutes (`False.elim`) every branch touching a field of `stubs` while every reachable branch evaluates identically without `stubs`. Omitting `s.supports_zfinx = false` from `InScope` leaves the unprovable goal `stubA.f32ToI32 rm v = stubB.f32ToI32 rm v`, immediately catching the scope leak.

### 6. Lifting Single-Step Irrelevance to Multi-Step Scoped ISA Correspondence and Extension Plug-In

Basis: derived

Single-step irrelevance extends to $k$-step execution (`execN stubs k s`) only when `InScope` is closed under reachable transitions—otherwise an `M`-mode `CSRRW` at step 0 could set `mstatus.FS := 0b01` and execute floating-point instructions at step 1. Multi-step isolation requires an inductive **Scope-Closure Invariant** $\text{Inv} : \text{HartState} \to \text{Prop}$ satisfying:

1. **Scope inclusion:** $\forall s,\; \text{Inv}(s) \implies \text{InScope}(s)$.
2. **Concrete step preservation (proved once on `dummySoftFloat`):**
   $$\forall s\; s',\; \text{Inv}(s) \to \text{step}(\text{dummySoftFloat}, s) = \text{Except.ok}(s') \implies \text{Inv}(s').$$

Standard architectural realizations of $\text{Inv}$ include (a) static capability disablement (`supports_F = false ∧ supports_Zfinx = false`), (b) unprivileged User-mode envelopes (`cur_privilege = .User ∧ mstatus.FS = 0b00 ∧ supports_Zfinx = false`, halting at trap boundaries since User `CSRRW mstatus` traps), and (c) $W \oplus X$ verified code-image envelopes where all executable addresses decode to integer instructions that never write `mstatus.FS`.

Induction on $k : \mathbb{N}$ then yields multi-step irrelevance and universal extension plug-in:

```lean
def execN (stubs : SoftFloatStubs) : Nat → HartState → Except Trap HartState
  | 0,     s => .ok s
  | k + 1, s => do let s' ← step stubs s; execN stubs k s'

theorem execN_stub_irrelevant (stubA stubB : SoftFloatStubs) :
    ∀ (k : Nat) (s : HartState), Inv s → execN stubA k s = execN stubB k s
  | 0, _s, _h_inv => rfl
  | k + 1, s, h_inv => by
      have hA := step_stub_irrelevant stubA dummySoftFloat s (Inv.toInScope h_inv)
      have hB := step_stub_irrelevant stubB dummySoftFloat s (Inv.toInScope h_inv)
      rw [execN, execN, hA, hB]
      cases h_res : step dummySoftFloat s with
      | error _ => rfl
      | ok s' => exact execN_stub_irrelevant stubA stubB k s' (Inv.step_preserved h_inv h_res)

theorem correspondence_transfers_to_real_extension
    {implExec : Nat → HartState → Except Trap HartState}
    (h_dummy : ∀ k s, Inv s → implExec k s = execN dummySoftFloat k s)
    (realIEEE754SoftFloat : SoftFloatStubs) :
    ∀ k s, Inv s → implExec k s = execN realIEEE754SoftFloat k s := by
  intro k s h_inv
  exact (h_dummy k s h_inv).trans (execN_stub_irrelevant dummySoftFloat realIEEE754SoftFloat k s h_inv)
```

All instruction-level symbolic evaluation and invariant preservation proofs run against the closed concrete term `step dummySoftFloat` without universally quantified stub noise; later supplying a verified `realIEEE754SoftFloat : SoftFloatStubs` transfers every proved correspondence theorem in one `.trans` step without re-proving integer obligations. Pairing `#print axioms` with a specification-cone walk rejecting `.opaqueInfo` and `.axiomInfo` in the theorem's type completes the zero-axiom audit gate.

## Boundaries

- **Reachable platform nondeterminism vs unreachable stubs (`known not to apply`):** Constructive stub irrelevance (`step stubA s = step stubB s`) is **`known not to apply`** to hooks invoked along in-scope paths—such as `load_reservation` / `match_reservation` / `cancel_reservation` during `LR`/`SC` atomics, MMIO `plat_term_write`, or `sys_enable_experimental_extensions ()` if queried unconditionally during integer decode. Reachable environment interactions must be modeled via explicit state fields (e.g., `reservation : Option PhysAddr`) or relational nondeterminism.
- **Native execution under `@[extern]` or `@[implemented_by]` (`known not to apply`):** Kernel proofs of `execN_stub_irrelevant` are **`known not to apply`** to compiled native binaries (`lean --c` / `lake build`) if reachable definitions carry `@[extern]` or `@[implemented_by]`, which substitute unverified C or Lean IR (`src/Lean/Compiler/ExternAttr.lean:61-73`). Native runners require checking `Lean.isExtern` and `Compiler.getImplementedBy?` separately.
- **Kernel unfolding of `opaque` declarations (`unsupported`):** Delta-reducing `ConstantInfo.opaqueInfo` inside proofs or kernel `is_def_eq` is explicitly **`unsupported`** by the Lean 4 kernel (`src/kernel/declaration.h:447-449`, `src/kernel/type_checker.cpp:543-551`), even when `:= val` is written in the same module. Unlike Coq/Rocq's `Transparent`/`Opaque` toggle on `Defined` constants, Lean 4 `opaqueDecl` is permanent.
- **Automatic stub-bundle emission in Sail's Lean backend (`unsupported` / `unknown`):** At `rems-project/sail` commit `97aa617dcd4d01575f773cb58ea1e8686858c8c2`, `sail_plugin_lean.ml` does not automatically package unresolved `extern` declarations into a Lean `structure` or `ReaderT` bundle (`unsupported`); `opencompl/sail-riscv-lean` supplies top-level `axiom`s in `LeanRV64D/RiscvExtras.lean`. Whether upstream `rems-project/sail` will adopt record- or typeclass-parameterized externs is **`unknown`** from repository sources.
- **Non-Lean provers and full Sail-Armv9 SVE/SME extractions (`not examined`):** Source-level axiom/opacity auditing in Coq/Rocq (`Print Assumptions` over functor `Parameter`s) and Isabelle/HOL locales, as well as generated Lean code for Armv9-A SVE2/SME ASL specifications, was **`not examined`** directly here.

## Evidence

### Primary Repository Sources (Observed 2026-11-20)

1. **`leanprover/lean4` (`450d6b121a45a48ffc58a83c921c813dffb259cb`):**
   - `src/Lean/Declaration.lean:16-45, 138-149, 163-171, 406-491`: `ReducibilityHints` (documenting at lines 38–45 that hints and `@[irreducible]` never block kernel unfolding), `OpaqueVal`, `Declaration.opaqueDecl`, `ConstantInfo.opaqueInfo`, `ConstantInfo.isPartial` (lines 439–441), and `ConstantInfo.hasValue (allowOpaque := false)` (lines 471–476).
   - `src/kernel/declaration.h:214-230, 434-450`, `src/kernel/type_checker.cpp:543-590`, and `src/kernel/environment.cpp:156-227`: Kernel `has_value(false)` blocking `is_delta` on `is_opaque()`, and `add_axiom` vs `add_opaque` value checking.
   - `src/Lean/Elab/DefView.lean:187-199` and `src/Lean/Elab/PreDefinition/MkInhabitant.lean:31-76`: `mkDefViewOfOpaque` (`default_or_ofNonempty%`) and `mkInhabitantFor` (`Inhabited` before `Nonempty`).
   - `src/Lean/Elab/PreDefinition/Main.lean:20-36` and `src/Lean/Elab/PreDefinition/Basic.lean:201-205, 285-297`: `addAndCompilePartial` emitting kernel `Declaration.opaqueDecl` plus `unsafe` `_unsafe_rec`.
   - `src/Lean/Util/CollectAxioms.lean:56-67` and `src/Lean/Replay.lean:81-102, 177-198`: `CollectAxioms.collect` omitting `.opaqueInfo` names from `s.axioms`, and `Environment.replay` accepting `.opaqueInfo` while skipping `isUnsafe`/`isPartial`.
   - `src/Lean/Compiler/ExternAttr.lean:19-73, 119-135` and `src/Init/Data/Float/Float.lean:193, 288, 344-365`: `@[extern]` C bindings on `opaque` `Float` primitives.
2. **`leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`):**
   - `Comparator/Axioms.lean:39-71`, `Comparator/Compare.lean:50-58, 67-109`, `Comparator/Util.lean:10-27`, and `tests/projects/opaque_value/{Challenge.lean,Solution.lean,test.json}`: Solution-side `allowOpaque := true` checking vs silent acceptance of `Challenge.lean` `opaqueInfo` constants.
3. **`leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`) and `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`):**
   - `digama0/lean4lean` `Lean4Lean/Verify/Axioms.lean:38-41, 71-85, 121-129, 255-257, 362-364`: Practical consequences of standard-library `opaque`, `@[extern] opaque`, and `partial def` blockers (`Level.normalize`, `Expr.replace`, `PersistentHashMap.insertAux`) requiring total twins (`Total.normalize`).
4. **`rems-project/sail` (`97aa617dcd4d01575f773cb58ea1e8686858c8c2`), `rems-project/lean-sail` (`079463134b9c50450b8393e1566a09fc492a34d9`), `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`), and `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`):**
   - `rems-project/sail` `src/sail_lean_backend/sail_plugin_lean.ml:144-156, 225` and `src/sail_lean_backend/pretty_print_lean.ml:1079-1098, 1309-1314, 1507-1522`: `merge_function_clauses` and `extern` suppression.
   - `riscv/sail-riscv` `model/extensions/FD/fdext_regs.sail:274-339` and `model/extensions/FD/fext_insts.sail:479-620`: `haveSingleFPU()` and `Ext_Zfinx` executing SoftFloat externs over `X` registers with `mstatus.FS = 0b00`.
   - `opencompl/sail-riscv-lean` `LeanRV64D/RiscvExtras.lean:31-112`, `LeanRV64D/FakeReal.lean:6-65`, and `LeanRV64D/Step.lean:241-490`: The 75 `axiom` declarations and `FakeReal` definitions reachable from `try_step`.

### Peer-Reviewed Literature and Technical Reports

- Alasdair Armstrong et al. "ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS." *Proc. ACM Program. Lang.* 3, POPL, Article 71 (2019). DOI: `10.1145/3290384`.
- Alastair Reid. "Trustworthy Specifications of ARM v8-A and v8-M System Level Architecture." *FMCAD 2016*, pp. 161–168 (2016). DOI: `10.1109/FMCAD.2016.7886675`.
- Leonardo de Moura and Sebastian Ullrich. "The Lean 4 Theorem Prover and Programming Language." *CADE 28*, LNCS 12699, pp. 625–635 (2021). DOI: `10.1007/978-3-030-79876-5_37`.
- Mario Carneiro. "Lean4Lean: Towards a Verified Typechecker for Lean 4." `arXiv:2403.14064` (2024).
- Freek Wiedijk. "Pollack-inconsistency." *ENTCS* 285, pp. 85–100 (2012). DOI: `10.1016/j.entcs.2012.06.008`.
- Robert Pollack. "How to Believe a Machine-Checked Proof." In *Twenty-Five Years of Constructive Type Theory*, Oxford University Press (1998); BRICS `RS-97-18` (1997).

## Revalidation

To revalidate these invariants on a new Lean 4 toolchain release (using core `Lean` without external Lake dependencies), save `/tmp/revalidate_stub_isolation.lean` and run `lean /tmp/revalidate_stub_isolation.lean`:

```lean
import Lean

-- 1. Opaque stub: zero axioms in `collectAxioms`, yet congruence proves reflexivity tautology
opaque opaqueF32ToI32 : BitVec 3 → BitVec 32 → BitVec 5 × BitVec 32

theorem opaque_congruence_trap (rm : BitVec 3) (x : BitVec 32) :
    opaqueF32ToI32 rm x = opaqueF32ToI32 rm x := rfl

-- 2. Parameterized RV64 integer + F/Zfinx step with constructive stub irrelevance
inductive Instr where
  | addi (rd rs1 : Fin 32) (imm : BitVec 64)
  | fcvt_w_s (rd rs1 : Fin 32) (rm : BitVec 3)
  | csrrw_mstatus_fs (newFs : BitVec 2)

inductive Priv where | User | Machine deriving DecidableEq

structure HartState where
  pc            : Nat
  regs          : Fin 32 → BitVec 64
  mstatusFs     : BitVec 2
  priv          : Priv
  supportsF     : Bool
  supportsZfinx : Bool

structure SoftFloatStubs where
  f32ToI32 : BitVec 3 → BitVec 32 → BitVec 5 × BitVec 32
  deriving Inhabited

def dummySoftFloat : SoftFloatStubs := default

def haveSingleFPU (s : HartState) : Bool :=
  (s.supportsF && (s.mstatusFs != 0b00#2)) || s.supportsZfinx

def step (prog : Nat → Instr) (stubs : SoftFloatStubs) (s : HartState) :
    Except Unit HartState :=
  match prog s.pc with
  | .addi rd rs1 imm =>
      .ok { s with pc := s.pc + 4, regs := fun r => if r == rd then s.regs rs1 + imm else s.regs r }
  | .fcvt_w_s rd rs1 rm =>
      if haveSingleFPU s then
        let (_fflags, w32) := stubs.f32ToI32 rm ((s.regs rs1).truncate 32)
        .ok { s with pc := s.pc + 4, regs := fun r => if r == rd then w32.signExtend 64 else s.regs r }
      else .error ()
  | .csrrw_mstatus_fs newFs =>
      if s.priv == .Machine then .ok { s with pc := s.pc + 4, mstatusFs := newFs } else .error ()

def InScope (s : HartState) : Prop := s.mstatusFs = 0b00#2 ∧ s.supportsZfinx = false
def Inv (s : HartState) : Prop := s.priv = .User ∧ InScope s

theorem step_stub_irrelevant (prog : Nat → Instr) (stubA stubB : SoftFloatStubs)
    (s : HartState) (h : InScope s) :
    step prog stubA s = step prog stubB s := by
  obtain ⟨h_fs, h_zfinx⟩ := h
  unfold step; split
  · rfl
  · have h_no : haveSingleFPU s = false := by simp [haveSingleFPU, h_fs, h_zfinx]
    simp [h_no]
  · rfl

theorem inv_preserved (prog : Nat → Instr) {s s' : HartState}
    (h_inv : Inv s) (h_step : step prog dummySoftFloat s = .ok s') : Inv s' := by
  obtain ⟨h_priv, h_fs, h_zfinx⟩ := h_inv
  unfold step at h_step; split at h_step
  · injection h_step with h_eq; subst h_eq; exact ⟨h_priv, h_fs, h_zfinx⟩
  · have h_no : haveSingleFPU s = false := by simp [haveSingleFPU, h_fs, h_zfinx]
    simp [h_no] at h_step
  · simp [h_priv] at h_step

def execN (prog : Nat → Instr) (stubs : SoftFloatStubs) : Nat → HartState → Except Unit HartState
  | 0, s => .ok s
  | k + 1, s => do let s' ← step prog stubs s; execN prog stubs k s'

theorem execN_stub_irrelevant (prog : Nat → Instr) (stubA stubB : SoftFloatStubs) :
    ∀ (k : Nat) (s : HartState), Inv s → execN prog stubA k s = execN prog stubB k s
  | 0, _s, _h => rfl
  | k + 1, s, h_inv => by
      have hA := step_stub_irrelevant prog stubA dummySoftFloat s h_inv.2
      have hB := step_stub_irrelevant prog stubB dummySoftFloat s h_inv.2
      rw [execN, execN, hA, hB]
      cases h_res : step prog dummySoftFloat s with
      | error _ => rfl
      | ok s' => exact execN_stub_irrelevant prog stubA stubB k s' (inv_preserved prog h_inv h_res)

-- 3. Specification-cone walk detecting `.opaqueInfo` and `.axiomInfo` in theorem types
partial def hasOpaqueOrAxiomInSpecCone (env : Lean.Environment) (declName : Lean.Name) : Bool :=
  let rec loop (worklist : List Lean.Name) (visited : Lean.NameSet) : Bool :=
    match worklist with
    | [] => false
    | c :: rest =>
      if visited.contains c then loop rest visited
      else
        let visited := visited.insert c
        match env.find? c with
        | none | some (.opaqueInfo _) | some (.axiomInfo _) => true
        | some (.defnInfo v) =>
            loop (v.type.getUsedConstants.toList ++ v.value.getUsedConstants.toList ++ rest) visited
        | some (.inductInfo v) =>
            loop (v.type.getUsedConstants.toList ++ v.ctors ++ rest) visited
        | some (.ctorInfo v) | some (.recInfo v) =>
            loop (v.type.getUsedConstants.toList ++ rest) visited
        | some (.thmInfo _) | some (.quotInfo _) => loop rest visited
  match env.find? declName with
  | none => true
  | some root => loop root.type.getUsedConstants.toList {}

#eval do
  let env ← Lean.MonadEnv.getEnv
  let axs1 ← Lean.collectAxioms ``opaque_congruence_trap
  let bad1 := hasOpaqueOrAxiomInSpecCone env ``opaque_congruence_trap
  let axs2 ← Lean.collectAxioms ``execN_stub_irrelevant
  let bad2 := hasOpaqueOrAxiomInSpecCone env ``execN_stub_irrelevant
  unless axs1.isEmpty && bad1 == true && axs2.isEmpty && bad2 == false do
    throw <| IO.userError "Revalidation discriminator failed!"
```

For source-only revalidation on a newer `leanprover/lean4` commit, diff `src/Lean/Util/CollectAxioms.lean` (`.opaqueInfo` arm), `src/Lean/Elab/DefView.lean` (`mkDefViewOfOpaque`), `src/Lean/Elab/PreDefinition/Main.lean` (`addAndCompilePartial`), and `src/kernel/declaration.h` (`has_value`).
