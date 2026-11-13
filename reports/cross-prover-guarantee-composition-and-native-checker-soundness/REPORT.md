# Composing Guarantees Across Provers and Natively Compiled Checkers: Formal Handles, Translation Boundaries, and TCB Accounting

## Summary

An industrial verified compilation and verification stack frequently combines heterogeneous assurance links: a front-end theorem proved in Lean 4, a translation-validation or certificate check executed by a natively compiled checker binary, and a backend or ISA theorem proved in another theorem prover (such as CompCert or Bedrock2 in Rocq, CakeML or L3 in HOL4, `s2n-bignum` in HOL Light, or `seL4` in Isabelle/HOL). Investigating the exact formal handles in Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), Anneal's boundary auditor (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`), cross-prover translation pipelines (`lean4export`, `lean4less`, `lean2dk`, `rocq-lean-import`, `OpenTheory`, `Sail`, `Lem`, `Ott`, `L3`), and heterogeneous project chains (`seL4`, `CakeML`, `awslabs/s2n-bignum`, `leanprover/LNSym`) establishes four governing conclusions, mechanized in [`support/CrossProverAndNativeCheckerCompositionProbe.lean`](support/CrossProverAndNativeCheckerCompositionProbe.lean) (196 lines, zero `sorryAx`):

1. **Lean 4's Native Evaluation Handles (`Lean.ofReduceBool`, `Lean.trustCompiler`, and Lean 4.34.1 `Lean.Meta.nativeEqTrue`) and a Critical Auditor Finding:**
   - In `src/lean/Init/Core.lean:2338-2409` of `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), Lean declares `axiom trustCompiler : True`, `opaque reduceBool (b : Bool) : Bool := have := trustCompiler; b`, `axiom ofReduceBool (a b : Bool) (h : reduceBool a = b) : a = b`, `opaque reduceNat`, and `axiom ofReduceNat`, all marked `@[deprecated "in-kernel native reduction is deprecated; assert native evaluations with axioms instead" (since := "2026-02-01")]`.
   - Crucially, in Lean `v4.34.1`, the `native_decide` and `bv_decide` tactics (`src/lean/Lean/Elab/Tactic/Decide.lean:57-68` and `src/lean/Lean/Meta/Native.lean:37-87`) **no longer emit `Lean.ofReduceBool` or `Lean.trustCompiler`**. Instead, `Lean.Meta.nativeEqTrue` compiles a temporary `meta` definition `_native.<tacticName>.decl : Bool := e`, executes `unsafe evalConst Bool auxDeclName` in the elaborator, and—if `true`—injects a fresh **per-invocation `Declaration.axiomDecl`** named `<thm>._native.<tacticName>.ax_1_1 : e = true` (`Native.lean:75-82`).
   - **Auditor Consequence (`naive_blocklist_misses_v4341_native_decide_axiom`):** Any verification auditor that only blocklists the fixed axiom names `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and `Lean.trustCompiler` will **falsely accept** `by native_decide` and `by bv_decide` in Lean `v4.34.1`! Anneal's `TrustedBoundary.lean` (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`, lines 208–218 and 515–560) defeats both mechanisms because Phase 1 (`allowedTheorySyntaxKinds`) rejects `native_decide`/`bv_decide` syntactically and Phase 2 (`verifyAndCollectLocals`) enforces a **closed foundation axiom allowlist** (`{Classical.choice, Quot.sound, propext}`) while rejecting all non-foundation `.axiomInfo` declarations (`annealAllowlistAudit`).
2. **Three Composition Methods for Natively Compiled Checkers and Their Exact Trust Footprints:**
   - **Method A — Untrusted Native Witness Generation + In-Kernel `rfl` / `decide +kernel` Replay (`in_kernel_certificate_replay_zero_tcb_growth`):** An untrusted native binary computes a compact certificate $c$ (e.g., an SSA `regalloc2` `blockIn` map, an LRAT unsatisfiability proof, or a CFG cutpoint witness), and the Lean 4 kernel evaluates `check p₁ p₂ c = true` via `Eq.refl true` (accelerated by `type_checker.cpp`'s native GMP `reduce_nat` and cached per module by `decide +kernel`'s `mkAuxLemma` in `Decide.lean:104-118`). **Trust added to TCB: zero.**
   - **Method B — Unverified Native Execution (`leanc` / `evalConst` / `ofReduceBool`):** A checker proved sound in Lean (`∀ p₁ p₂ c, check p₁ p₂ c = true → Refines p₁ p₂`) is compiled via `leanc -O2` (or `nativeEqTrue`) and run natively outside the kernel. **Trust added to TCB:** Lean's LCNF compiler, lambda lifter, IR optimizer, C code generator, C compiler (`clang`/`gcc`), dynamic linker, JSON/byte parser, and every `@[implemented_by]`, `@[extern]`, and `@[csimp]` override (~30,000+ LOC).
   - **Method C — Verified Machine-Code Checker Extraction (`CakeML` `compile_correct` / Anneal Self-Hosted `Architecture B`):** The checker's source implementation is itself compiled through a verified compiler pipeline down to machine-code bytes (`cake_compiled_thm` / `checkerMirBody_two_step_sound`), eliminating the unverified compiler from the native checker's TCB and leaving only the target ISA operational model and OS I/O wrapper.
3. **Establishing Semantic Agreement Across Provers (`Sail`, `Lem`, `Ott`, `L3`, `Dedukti`, `OpenTheory`, and Differential Testing):**
   - **Single-source code generation (`Sail`, `Lem`, `Ott`, `L3`)** aligns AST structure across provers, but each backend printer (`sail -coq` vs. `sail -lean`) and target bitvector/monad library remains an unverified translation stage.
   - **Proof translation (`lean4export` + `lean4less` + `lean2dk`, `rocq-lean-import`, `OpenTheory`)** re-checks proof steps in a single target kernel, but requires extensionality axioms (`pIrrel`, `Singleton.elim`, `quot_sound`) and still requires statement-level bijection checking (`leanprover/comparator`) at the interface boundary (`bijection_gated_cross_prover_transfer_sound` vs. `canary_unverified_prover_translation_mismatch`).
   - **Differential testing and co-simulation** catch shallow encoding bugs (such as `LNSym`'s inverted `LDST.mayModifiedRegs` load/store bit or `cslib-community/bignum`'s missing shifted-register decode arm), but cannot replace a formal boundary bijection across unbounded inputs.

## Applicability

This report applies to:
1. **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: `src/lean/Init/Core.lean:2331-2415`, `src/lean/Lean/Meta/Native.lean:1-87`, `src/lean/Lean/Elab/Tactic/Decide.lean:1-193`, and `src/kernel/type_checker.cpp:101-372`.
2. **Anneal (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`)**: `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`, `trusted/lean/foundation-lock.json`, and `THREAT_MODEL.md`.
3. **Cross-Prover Translation & Specification Systems**: `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`, `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e`, `rish987/lean4less@5b66bbc4af5c2c11313fcfb5098630dadaf19281`, `rish987/lean2dk@29f985670008c29e852d61c562b8c10c84f7c5fb`, `rocq-community/rocq-lean-import@2d28bbe80e7361bf3ac54f5ef099207fc61ce837`, `rems-project/sail@7e0e53d183cad75b8f36bfbbecc0ef75614a8418`, and `coruus/L3@d6558e679a25ffaaf16a47a3189f8f8111e45e0c`.
4. **Heterogeneous Verification Projects**: `seL4` (`seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, `seL4/graph-refine@94c93d18830d680fc6732d21fb16ca58ebca9dc5`), `CakeML` (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`), `awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428`, and `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`.

## Findings

### 1. Formal Handles for Compiled Evaluation in Lean 4.34.1 and Native Checker Composition

Basis: source + execution (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `src/lean/Init/Core.lean:2331-2415`, `src/lean/Lean/Meta/Native.lean:1-87`, `src/lean/Lean/Elab/Tactic/Decide.lean:57-133`; `joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc` `trusted/audit/TrustedBoundary.lean`; [`support/CrossProverAndNativeCheckerCompositionProbe.lean`](support/CrossProverAndNativeCheckerCompositionProbe.lean)).

#### 1.1 Exact Signatures and Evolution of `trustCompiler`, `ofReduceBool`, and `nativeEqTrue` in Lean `v4.34.1`

In `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`src/lean/Init/Core.lean:2338-2409`), the built-in kernel reduction hints are defined as:

```lean
@[deprecated "in-kernel native reduction is deprecated; assert native evaluations with axioms instead" (since := "2026-02-01")]
axiom trustCompiler : True

opaque reduceBool (b : Bool) : Bool :=
  have := trustCompiler
  b

opaque reduceNat (n : Nat) : Nat :=
  have := trustCompiler
  n

axiom ofReduceBool (a b : Bool) (h : reduceBool a = b) : a = b
axiom ofReduceNat  (a b : Nat)  (h : reduceNat a = b)  : a = b
```

In `src/lean/Lean/Meta/Native.lean:37-87` and `src/lean/Lean/Elab/Tactic/Decide.lean:57-68`, Lean `v4.34.1` decouples `native_decide` and `bv_decide` from in-kernel `reduceBool`:
1. `elabNativeDecideCore` constructs `d ← mkDecide expectedType` and invokes `nativeEqTrue tacticName d`.
2. Inside `withoutModifyingEnv`, `nativeEqTrue` creates a temporary `meta` definition `auxDeclName := _native.<tacticName>.decl` with value `e`, compiles it synchronously via `addAndCompile decl`, and executes `unsafe evalConst Bool auxDeclName` in the elaborator (`Native.lean:44-71`).
3. If evaluation returns `true`, `nativeEqTrue` adds a fresh **per-invocation axiom** to the kernel environment (`Native.lean:75-82`):
   ```lean
   let auxAxiomName ← mkAuxDeclName <| `_native ++ tacticName ++ `ax
   let axDecl := Declaration.axiomDecl {
     name := auxAxiomName
     levelParams := levels
     type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
     isUnsafe := false
   }
   addDecl axDecl
   ```
   and returns `of_decide_eq_true expectedType s (mkConst auxAxiomName levelParams)`.

Executing Lean `v4.34.1` on a side-by-side probe (`def myCheck : Bool := (List.range 10).length == 10`) confirms the distinct `#print axioms` footprints:
- `theorem via_ofReduceBool : myCheck = true := Lean.ofReduceBool myCheck true rfl` reports:
  `'via_ofReduceBool' depends on axioms: [Lean.ofReduceBool, Lean.trustCompiler]`
- `theorem via_native_decide : myCheck = true := by native_decide` reports:
  `'via_native_decide' depends on axioms: [via_native_decide._native.native_decide.ax_1_1]`

As proved in `naive_blocklist_misses_v4341_native_decide_axiom` ([`support/CrossProverAndNativeCheckerCompositionProbe.lean`](support/CrossProverAndNativeCheckerCompositionProbe.lean), lines 168–186), an auditor must never rely on a name blocklist (`!= "Lean.ofReduceBool" && != "Lean.trustCompiler"`); it must enforce a closed allowlist of foundation axioms (`{"Classical.choice", "Quot.sound", "propext"}`) together with `origin == .foundation`, as implemented in Anneal's `TrustedBoundary.lean`.

#### 1.2 Comparing the Four Reflection and Native-Checker Architectures

| Architecture | How `check p₁ p₂ c = true` Is Discharged | Axiom Footprint in Lean `v4.34.1` | What Must Be Trusted Beyond the Lean 4 Kernel? | Admitted by `anneal-audit` (`TrustedBoundary.lean`)? |
| :--- | :--- | :--- | :--- | :---: |
| **1. In-Kernel `rfl` / `decide` / `decide +kernel`** | Kernel `whnf` / `is_def_eq` reduces `check p₁ p₂ c` to `Bool.true` using C++ GMP `reduce_nat` (`Decide.lean:88-133`; `decide +kernel` caches via `mkAuxLemma`) | `[]` (or `{propext, Quot.sound}`) | **Nothing** (0 bytes added to TCB; `in_kernel_certificate_replay_zero_tcb_growth`) | **Yes** (`rfl` and `decide` without `+native`) |
| **2. Elaborator Native Eval (`native_decide` / `bv_decide` via `nativeEqTrue`)** | Elaborator runs `addAndCompile` + `unsafe evalConst Bool` and emits `Declaration.axiomDecl` (`_native.<tac>.ax_1_1`) | `[<thm>._native.<tac>.ax_1_1]` | Lean elaborator, LCNF/C compiler pipeline, dynamic linker, and all `@[implemented_by]` / `@[extern]` / `@[csimp]` hooks | **No** (rejected in Phase 1 and Phase 2) |
| **3. Legacy Kernel Interpreter (`Lean.ofReduceBool` / `Lean.ofReduceNat`)** | Kernel invokes Lean VM interpreter on `Lean.reduceBool c` during `whnf` (`Init/Core.lean:2342-2409`) | `[Lean.ofReduceBool, Lean.trustCompiler]` | Lean compiler, VM interpreter, and all `@[implemented_by]` / `@[extern]` hooks (~30k+ LOC); breaks external kernel replay (`nanoda_lib`) | **No** (rejected in Phase 2) |
| **4. Verified Binary Extraction (`CakeML` / Self-Hosted `Architecture B`)** | Checker implementation `checkerMirBody` is compiled by a verified compiler to `checkerIsaProg`, proved via Two-Step Equivalence (`checkerMirBody_two_step_sound`) | `[]` (for the meta-theorem proving binary soundness) | Target hardware ISA semantics, OS loader, and I/O byte-stream wrapper binding the file bytes $(p_1, p_2, c)$ to the theorem statement | **Yes** (meta-theorem is axiom-free) |

---

### 2. Establishing Agreement Between Definitions in Different Provers

Basis: source + derived ([`support/heterogeneous_composition_matrix.json`](support/heterogeneous_composition_matrix.json), [`support/CrossProverAndNativeCheckerCompositionProbe.lean`](support/CrossProverAndNativeCheckerCompositionProbe.lean)).

When composing a theorem proved in Prover $A$ (e.g., Lean 4) with a theorem proved in Prover $B$ (e.g., Rocq, HOL4, HOL Light, or Isabelle/HOL), the combined argument is sound only if the intermediate language syntax and semantics $(Prog_A, sem_A)$ in Prover $A$ denote the exact same mathematical relation as $(Prog_B, sem_B)$ in Prover $B$ (`BoundaryBijection` in `CrossProverAndNativeCheckerCompositionProbe.lean:69-94`). Precedents establish this agreement through three mechanisms with distinct assurance profiles:

1. **Single-Source Specification Generation (`Sail`, `Lem`, `Ott`, `L3`):**
   - **Mechanism:** Author the ISA or language semantics once in a domain-specific specification language and generate definitions for multiple provers from the same AST:
     - **Sail (`rems-project/sail@7e0e53d183cad75b8f36bfbbecc0ef75614a8418`, `0.20.3`):** Compiles official `sail-riscv` (`a83603b6`) and `sail-arm` (`7d058164`) specifications to Coq/Rocq (`sail -coq`), Isabelle/HOL (`sail -isabelle`), HOL4 (`sail -hol4`), and Lean 4 (`sail -lean` over `PreSailM`).
     - **Lem (`rems-project/lem`) and Ott (ICFP 2007):** Emit HOL4, Isabelle/HOL, Coq, and OCaml definitions from a single specification (used across CakeML, `linksem` ELF linking semantics, and RustBelt/Cerberus precursors).
     - **L3 (`coruus/L3@d6558e679a25ffaaf16a47a3189f8f8111e45e0c`):** Compiles `arm8`, `x64`, `mips`, and `riscv` specifications to HOL4 (`HolExport.sml`) and flat functional models (`Monadify.deMonadifyDefn`).
   - **What Remains Trusted:** Each backend code generator (`sail -coq` vs. `sail -lean`) and its target support library (`PreSailM` in Lean 4 vs. `mword` in Coq) is an unverified translator. Furthermore, when an intermediate pipeline strips or transforms events (such as `islaris/frontend/decomp.ml:74-88` stripping concrete `ReadReg`s and inverting `Smt (Assert e)` vs. `Assume e` polarity), single-source ancestry does not prevent soundness bugs unless validated by a target-level simulation (`islaTrace_refines_stepResult`).
2. **Proof & Kernel-Environment Translation (`lean4export`, `lean4less`, `lean2dk`, `rocq-lean-import`, `OpenTheory`):**
   - **Mechanism:** Translate the theorem and its proof object from Prover $A$ into Prover $B$ (or a shared logical framework such as Dedukti) so a single kernel checks both links:
     - **HOL `OpenTheory` (`.art`, `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c` `candle/readerProofScript.sml`):** Transfers theorems between HOL Light, HOL4, and CakeML Candle over a compact stack-machine article format with verified semantics (`proves_sound`).
     - **Lean 4 $\to$ Dedukti / Rocq (`lean4export@df81913e`, `lean4less@5b66bbc4`, `lean2dk@29f98567`, `rocq-lean-import@2d28bbe8`):** Because Lean 4's kernel uses extensional definitional proof irrelevance (`isDefEqProofIrrel`), K-like singleton elimination (`toCtorWhenK`), and definitional `Quot.lift`, translating Lean 4 into Dedukti or Rocq requires `lean4less` to insert explicit `HEq` casts backed by 3 postulates (`Lean4Less.pIrrel`, `Singleton.elim`, `Quot.liftProp`), while `lean2dk` (`claude-stable`) requires lazy delta-unfolding (`DK_LAZY_DELTA=1`), WHNF/convertibility hash-table memoization, and stubbing 43 reflection-heavy `omega`/`Nat.Linear` lemmas as axioms, and `rocq-lean-import` incurs $2^n$ `SProp`/`Type` sort-splitting duplications and disables Rocq positivity/guard checks on nested inductives.
   - **What Remains Trusted:** Even when a translated proof checks in the target kernel, the consumer must still verify that the *translated theorem statement* matches the intended target specification (`leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e` `compareAt`).
3. **Differential Testing and Co-Simulation of Executable Definitions:**
   - **Mechanism:** Execute both provers' definitions (or hardware/QEMU vs. prover definitions) on shared test vectors or ELF binaries (`LNSym` + `ELFSage`, `K x86-64` hardware co-simulation, `s2n-bignum` + `cslib-community/bignum` byte-level decode comparison, MiniRust vs. Miri).
   - **What Remains Trusted:** Differential testing is a necessary falsification check—catching bugs like `LNSym`'s inverted `LDST.mayModifiedRegs` load/store bit (`Arm/Decode.lean:260-308`) and `cslib-community/bignum`'s missing shifted-register decode arm (`Bignum/Arm/Decode.lean:38`)—but as proved in `canary_unverified_prover_translation_mismatch` (where 8-bit wrapping addition `(x + 1) % 256` and unbounded `x + 1` agree on $0..254$ and diverge at $x = 255$), finite testing cannot substitute for a deductive `BoundaryBijection`.

---

### 3. How Precedent Projects Document and Account for Heterogeneous Chains

Basis: source + documentation (`seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, `seL4/graph-refine@94c93d18830d680fc6732d21fb16ca58ebca9dc5`, `seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b`, `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`, `awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428`, `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`; [`support/heterogeneous_composition_matrix.json`](support/heterogeneous_composition_matrix.json)).

| Project & Pinned Identity | Heterogeneous Links Composed | How Boundary Agreement Is Established | How the Trust Ledger Is Documented |
| :--- | :--- | :--- | :--- |
| **seL4** (`seL4/l4v@6b4076aeb` + `seL4/graph-refine@94c93d188` + `verification-manifest@f1f7a4289`) | (1) Isabelle/HOL proofs (`Abstract_A` $\to$ `ExecSpec` $\to$ `SIMPL` via `CParser`), (2) Python/SMT `graph-refine` validator, (3) Cambridge HOL4/L3 ARM/RISC-V ISA model | Both Isabelle `SIMPL` and the decompiled ELF binary are exported to a shared first-order `GraphLang` format; HOL4/L3 instruction semantics are exported to SMT-LIB bitvector formulas checked by Z3/CVC4 | `l4v/README.md`, `verification-manifest/default.xml` (pinning exact commit hashes and Isabelle release), and Sewell et al. (PLDI 2013) explicitly itemizing unverified boot code, assembly stubs, MMU/TLB/cache ops, and the `GraphLang` exporter/SMT solvers |
| **CakeML** (`CakeML/cakeml@f73189499` + `Candle` + `cake_lpr` + `Silver` PLDI 2019) | (1) HOL4 compiler proof (`compile_correct`), (2) L3 ISA models (`arm8`, `x64`, `riscv`), (3) OpenTheory `.art` kernel reader (`Candle`), (4) x64 machine-code bootstrap (`cake_compiled_thm`), (5) Silver Verilog CPU | Internalizes all links into **one HOL4 kernel**: L3 compiles ISA models directly into HOL4 theories (`HolExport.sml`), and `x64BootstrapProofScript.sml` proves in HOL4 that the x64 binary bytes implement the HOL4 compiler/checker function | Single top-level HOL4 theorem (`cake_compiled_thm` / `lpr_ok_thm` / `semantics_thm`) whose explicit hypotheses (`config_ok`, `installed`, `ffi_oracle`) state every remaining machine and environment assumption |
| **AWS `s2n-bignum`** (`awslabs/s2n-bignum@4d1356a74`) | (1) HOL Light x86-64 and AArch64 object-code proofs (`BIGNUM_ADD_SUBROUTINE_CORRECT`), (2) `define_assert_from_elf` `.o` byte loader, (3) Cryptol / SAW equivalence checks in CI | `define_assert_from_elf` reads the compiled ELF `.o` `.text` section directly into a HOL Light byte-list constant and checks byte-for-byte equality against the literal byte list inside the HOL Light proof (`object_binding.py`) | Dedicated [`SOUNDNESS.md`](https://github.com/awslabs/s2n-bignum/blob/4d1356a7470663c752660a59375dc3a9ef548428/SOUNDNESS.md) enumerating 6 trusted components: (1) HOL Light kernel + OCaml runtime, (2) x86/Arm ISA semantics, (3) ELF `.text` loader, (4) C header ABI match, (5) non-self-modifying code, and (6) `UArchEvent` constant-time trace model |
| **`leanprover/LNSym`** (`5c05220ff970e3bdd7813ad0c9ef3741522c8b92`) | (1) Lean 4 AArch64 operational semantics (`Arm/Exec.lean`), (2) Cryptol-transcribed algorithm specs (`Specs/SHA512.lean`), (3) `ELFSage` ELF parser (`Tests/ELFParser/`) | `ELFSage` extracts `.text` instruction words into a Lean `program : Map (BitVec 64) (BitVec 32)` table; `#genStepEqTheorems` reflects instruction fetch/decode by `Eq.refl` inside the Lean 4 kernel | Tracked via Lean `#print axioms` (`propext`, `Classical.choice`, `Quot.sound`) plus explicit repository separation between `Arm/` (semantics), `Specs/` (transcribed Cryptol specs), and `Proofs/` |

## Boundaries

1. **Unverified Native Checker Execution vs. Kernel Certificate Replay (`known not to apply` to zero-TCB claims):**
   - Running a Lean checker compiled via `leanc -O2` or `native_decide` is ~20x faster on cold single-process startup than full environment replay, but places the Lean compiler, C compiler, and `@[implemented_by]`/`@[extern]` annotations inside the TCB. In Anneal, native binaries may be used as **untrusted certificate generators** outside Lean, while the authoritative verification gate must remain in-kernel `rfl` / `decide +kernel` replay (`in_kernel_certificate_replay_zero_tcb_growth`).
2. **Incomplete Cross-Prover Translators (`known not to apply` to full Lean 4 `Std`/`Init` without axioms):**
   - At the inspected revisions, `lean2dk` (`29f98567`) stubs 43 `omega`/`Nat.Linear` reflection lemmas as axioms, and `rocq-lean-import` (`2d28bbe8`) disables Rocq's positivity and guard checkers on nested inductives and axiomatizes `quot_sound`. Therefore, Lean-to-Dedukti and Lean-to-Rocq translations do not replace native Lean 4 kernel replay (`TrustedBoundary.lean` `base.toKernelEnv.replay`).

## Evidence

1. **Primary Upstream Sources Inspected:**
   - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): `src/lean/Init/Core.lean:2331-2415`, `src/lean/Lean/Meta/Native.lean:1-87`, and `src/lean/Lean/Elab/Tactic/Decide.lean:1-193`.
   - `joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`: `trusted/audit/TrustedBoundary.lean:1-823`, `trusted/audit/src/lib.rs`, `trusted/lean/foundation-lock.json`.
   - Cross-prover and ISA frameworks: `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`, `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e`, `rish987/lean4less@5b66bbc4af5c2c11313fcfb5098630dadaf19281`, `rish987/lean2dk@29f985670008c29e852d61c562b8c10c84f7c5fb`, `rocq-community/rocq-lean-import@2d28bbe80e7361bf3ac54f5ef099207fc61ce837`, `rems-project/sail@7e0e53d183cad75b8f36bfbbecc0ef75614a8418`, `coruus/L3@d6558e679a25ffaaf16a47a3189f8f8111e45e0c`, `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, `seL4/graph-refine@94c93d18830d680fc6732d21fb16ca58ebca9dc5`, `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`, `awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428`, and `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`.
2. **Preserved Support Artifacts in This Package:**
   - [`support/CrossProverAndNativeCheckerCompositionProbe.lean`](support/CrossProverAndNativeCheckerCompositionProbe.lean) (196 lines, `sha256: dccb4a0a352704ffba89f61f087e1b052cd47ae2b6c1764edb078cdfced999ff`): Checked under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false`, proving `in_kernel_certificate_replay_zero_tcb_growth`, `bijection_gated_cross_prover_transfer_sound`, `canary_unverified_prover_translation_mismatch`, and `naive_blocklist_misses_v4341_native_decide_axiom` with zero `sorryAx` and zero `Lean.ofReduceBool`.
   - [`support/heterogeneous_composition_matrix.json`](support/heterogeneous_composition_matrix.json) (65 lines, `sha256: e5a028fe7422746dd332b2b0fb8d708ec01316cb66eb7baa4a2b7255c2ac54dc`): Structured matrix of Lean native evaluation handles, cross-prover agreement mechanisms, and heterogeneous project documentation chains.

## Revalidation

Run the following command to revalidate all four mechanized Lean 4.34.1 theorems and verify the JSON matrix:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/cross-prover-guarantee-composition-and-native-checker-soundness/support/CrossProverAndNativeCheckerCompositionProbe.lean

python3 -c 'import json; d = json.load(open("reports/cross-prover-guarantee-composition-and-native-checker-soundness/support/heterogeneous_composition_matrix.json")); assert len(d["lean_native_evaluation_handles"]) == 3 and len(d["cross_prover_agreement_mechanisms"]) == 3; print("OK")'
```

Expected output: three `#print axioms` checks report `does not depend on any axioms` and one reports `[propext, Quot.sound]`, and the Python check prints `OK` with exit code `0`.
