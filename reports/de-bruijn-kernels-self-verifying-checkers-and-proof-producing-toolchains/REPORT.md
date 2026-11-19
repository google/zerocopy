# De Bruijn Kernels, Self-Verifying Checkers, and Proof-Producing Toolchains

## Summary

Formal assurance scales only as far as its Trusted Computing Base (TCB) remains small, isolated, and independently checkable. Across modern proof assistants and verified compilers, minimizing the TCB rests on four reinforcing mechanisms:

1. **The De Bruijn split (statement vs. proof, generation vs. checking):** Decouple untrusted proof search and synthesis from a small proof checker, and physically isolate human-audited theorem statements from untrusted proof streams—exemplified by Metamath Zero's `.mm0`/`.mmb` split (`mm0-c` at 1,141 lines of C across `main.c`, `verifier.c`, and `verifier_types.c`) and bare-metal x86-64 ELF self-verification (`examples/verifier.mm0`, 29 lines).
2. **Machine-code and dual-kernel anchoring:** Eliminate unverified language runtimes, compilers, garbage collectors, and single-implementation kernel bugs by either compiling a verified kernel down to machine code with I/O-trace soundness (CakeML/Candle's `proves_sound` + `semantics_thm` proving every printed theorem on `stdout` is set-theoretically valid) or replaying flat exported declaration streams across an independent implementation (`lean4export` + `nanoda_lib` in safe Rust; MetaCoq + CertiCoq; Rocq's `rocqchk`).
3. **Hardening dependent-type kernel and runtime escape surfaces:** Auditing `#print axioms` alone is insufficient when untrusted synthesis agents author code or proofs. Concrete escapes include Lean 4's hardcoded symbol-name `reduce_nat` acceleration (`Nat.land` / `Nat.gcd` shadowing deriving `False` with zero axioms in standalone environments), unverified `@[implemented_by]` / `@[extern]` substitutions combined with `native_decide` (`Lean.ofReduceBool`), cached `.olean` axiom tables (`exportedAxiomsExt`), elaboration-time host I/O, and bidirectional import contamination of specification syntax.
4. **Definitional erasure and proof-producing / translation-validating compilation:** In intensional dependent type theory, algebraic verification scaffolding (refinement preorders, weakest preconditions, separation-logic triples) erases from the trusted specification via $\beta\delta\iota\zeta$-conversion (`rfl`), while CompCert (hybrid verified passes + verified validators for untrusted oracles such as `Allocation.regalloc`), Cogent (unverified compiler emitting C + Isabelle/HOL correspondence proofs), and Alive2 (SMT translation validation for LLVM IR) trade proof effort against TCB size along distinct architectural axes.

## Applicability

This reference synthesizes architectural invariants, source-level mechanisms, and threat models across thirteen pinned upstream verification systems and compilers examined on `2026-11-19`:

- **Minimal proof kernels and self-verifying checkers:** `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`), `jrh13/hol-light` (`6dbb775efdff7f75aa20006532bf6336bc645861`), and `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, specifically the `candle/` subtree).
- **Dependent type theory kernels, metatheory, and external replay:** `leanprover/lean4` (`8009d0a64d2860606c6a5ac5ff6702622b24921e`), `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`), `leanprover/lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`), `ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`), `MetaCoq/metacoq` (`51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`, branch `9.1`), `CertiCoq/certicoq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`), and `rocq-prover/rocq` (`25f5b18a320e4796f181f938d3b74bebe7db4dc4`).
- **Translation-validating and proof-producing compilers:** `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`), `AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`), and `au-ts/cogent` (`49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a`).

The report compares these subjects along a common axis—how each system draws, minimizes, and enforces the boundary between untrusted proof/code producers and the trusted checking core—and applies to engineers designing verification pipelines, audit harnesses for LLM- or tactic-generated proofs, dual-kernel CI gates, or verified compiler backends.

**Scope qualifications:**
- Specific Lean 4 C++ kernel line numbers, environment extension behaviors (`exportedAxiomsExt`), and attribute checks apply strictly to `leanprover/lean4` at `8009d0a64d2860606c6a5ac5ff6702622b24921e` (which includes Lean 4's module system and `LEAN_NAT_MAX_SIZE` numeral bounds). Earlier Lean 4 releases (e.g., `v4.0`–`v4.14`) lack `exportedAxiomsExt` and `LEAN_NAT_MAX_SIZE` while sharing the `reduce_nat` hardcoded-name mechanism.
- Self-contained Python 3.13.15 model probes (`Basis: execution`) validate the abstract state-machine invariants (primitive shadowing divergence, statement-vs-proof stack isolation, and register-allocation translation validation), whereas Lean 4 kernel escape mechanics are established by direct C++ and Lean source inspection (`Basis: source`) rather than live Lean binary execution (see **Boundaries**).

## Findings

### 1. The De Bruijn Criterion and LCF Micro-Kernel Baseline

`Basis: normative + source`

The **De Bruijn criterion** (named for N. G. de Bruijn's Automath architecture and formalized by Barendregt and Wiedijk, *Phil. Trans. R. Soc. A* 2005, DOI `10.1098/rsta.2005.1650`) requires a proof assistant to emit proof objects checkable by a small, independent, easily auditable verifier whose soundness does not depend on proof search, tactics, decision procedures, or IDE frontends. Two foundational designs implement this principle differently:

1. **LCF-style abstract-datatype kernels (`jrh13/hol-light@6dbb775e`):** Rather than storing explicit proof trees, the kernel exposes an opaque ML type `thm` whose constructors are sealed inside a module signature (`fusion.ml` L12–81, 680 total lines). Every theorem value must be fabricated through exactly **10 primitive inference rules** (`REFL`, `TRANS`, `MK_COMB`, `ABS`, `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST_TYPE`, `INST`) plus three conservative/axiomatic declaration primitives (`new_axiom`, `new_basic_definition`, `new_basic_type_definition`).
   - *Residual TCB hazard of LCF:* Because no external proof artifact is emitted, soundness depends completely on the host language's type soundness, module abstraction barrier, mutability discipline (e.g., `Obj.magic`, mutable strings in legacy OCaml, or C FFI calls), compiler, and garbage collector.
2. **Explicit-certificate De Bruijn checkers (`digama0/mm0`, `lean4export` + `nanoda_lib`, `rocqchk`):** Proof search serializes a self-contained proof artifact (`.mmb` bytecode, NDJSON declaration stream, `.vo` term) consumed by a standalone process with no access to the tactic engine's heap or mutability primitives.

---

### 2. Ultra-Small & Self-Verifying Proof Checkers

#### 2.1 Metamath Zero (`digama0/mm0@0d414c0b`): Statement-vs-Proof Split and Bare-Metal ELF Verification

`Basis: normative + source + execution`

Metamath Zero (Carneiro, *CICM 2020*, LNCS 12236, pp. 71–88, DOI `10.1007/978-3-030-53518-6_5`, arXiv:1910.10703) extends the De Bruijn criterion to **auditor-centric separation of specification from proof**. Per `mm0.md` L1–25, verification takes two physically separate inputs:

- **Specification file (`.mm0`):** Human-audited header containing sorts, term constructors, definitions, axioms, notation, and theorem statements. The auditor reads *only* this file to confirm that axiom system $A$ and theorem statements $T_1, \dots, T_n$ express the intended claims.
- **Proof file (`.mmb`, binary format in `mm0-c/mmb.md`):** An untrusted, compiler-generated bytecode hint stream that the auditor never inspects.

**Reference verifier footprint (`mm0-c/`):** Direct inspection of `digama0/mm0@0d414c0b` shows the entire C verifier comprises:

| File | Total Lines | Non-Empty Lines | Role in Verification |
| :--- | ---: | ---: | :--- |
| `mm0-c/main.c` | 79 | 71 | CLI entry, `mmap` of `.mmb`, stdin reading of `.mm0`, invoking `verify()` |
| `mm0-c/verifier.c` | 819 | 759 | `.mm0` parser + lockstep `.mmb` stack/heap proof & unification interpreter |
| `mm0-c/verifier_types.c` | 243 | 203 | Binary header structs, sort/term/theorem table layouts, opcode constants |
| `mm0-c/verifier_debug.c` | 322 | 290 | Optional diagnostic printing (excluded from minimal check path) |
| **Core total (excl. debug)** | **1,141** | **1,033** | Complete C reference verifier |

**Structural anti-shadowing invariant (`mm0-c/verifier.c`):** The `verify(u8* file, u64 len)` loop (L670–790) advances through `.mmb` statement opcodes (`CMD_STMT_SORT`, `CMD_STMT_DEF`, `CMD_STMT_LOCAL_DEF`, `CMD_STMT_AXIOM`, `CMD_STMT_THM`, `CMD_STMT_LOCAL_THM`) in **strict lockstep** with the `.mm0` specification parser via `parse_until(stmt_type)` (L712, L756, L789):
- Local helper definitions and lemmas (`IS_CMD_STMT_LOCAL`) stay invisible to the `.mm0` header and cannot alter public declarations.
- For every public `theorem` (`CMD_STMT_THM`), the proof stack machine executes only bounded proof opcodes (`CMD_PROOF_REF`, `CMD_PROOF_DUMMY`, `CMD_PROOF_TERM`/`_SAVE`, `CMD_PROOF_THM`/`_SAVE`, `CMD_PROOF_HYP`, `CMD_PROOF_CONV`, `CMD_PROOF_REFL`, `CMD_PROOF_SYMM`, `CMD_PROOF_CONG`, `CMD_PROOF_UNFOLD`, `CMD_PROOF_CONV_CUT`, `CMD_PROOF_CONV_SAVE`, `CMD_PROOF_SAVE`, plus `CMD_PROOF_SORRY` which is guarded/tracked), checks that the top stack element has type `STACK_TYPE_PROOF` (L780–781), runs `run_unify(UThmEnd, ...)` against the theorem's declared conclusion (L788), and synchronizes with the next parsed `.mm0` statement (`parse_until`, L789).
- Because the `.mmb` bytecode ISA has **no opcode** to rewrite, shadow, or omit a `.mm0` header declaration, a malicious proof generator cannot weaken a theorem statement without modifying the human-audited `.mm0` file. (Confirmed via abstract stack-machine model Probe 2 in **Evidence**.)

**Bare-metal x86-64 ELF self-verification (`examples/verifier.mm0`):** To remove the C compiler (`gcc`/`clang`) and C standard library from the TCB, MM0 specifies its own x86-64 ELF verifier directly against a formal x86-64 ISA and Linux syscall specification (`examples/x86.mm1`, 5,940 lines; `examples/mm0.mm0`, 1,367 lines; MMC proof-producing compiler in `examples/compiler.mm1`). The entire top-level security specification in `examples/verifier.mm0` (L1–29) consists of three theorems over the raw ELF byte string `Verifier : string`:

```mm0
def Verifier: string;
theorem Verifier_basicElf: $ isBasicElf Verifier $;
theorem Verifier_terminates {mm0_file output: nat} (k: nat):
  $ initialConfig Verifier k ->
    terminates_ensuring k (S\ mm0_file, {output | output = 0 /\ Valid mm0_file}) $;
theorem Verifier_Valid (k mm0_file: nat):
  $ initialConfig Verifier k /\ succeeds k mm0_file 0 -> Valid mm0_file $;
```

Under this specification, an auditor trusting only the x86-64 ISA + Linux `read`/`write`/`exit` kernel semantics (`x86.mm0`), MM0's logical rules (`mm0.mm0`), and the 29-line theorem statement (`verifier.mm0`) obtains machine-code assurance: if the concrete ELF binary `Verifier` consumes `mm0_file` on `stdin`, produces empty `stdout`, and exits with code `0`, then every theorem in `mm0_file` is derivable (`Valid mm0_file`).

#### 2.2 CakeML and Candle (`CakeML/cakeml@2874b664`): Machine-Code Verified HOL Light with I/O Soundness

`Basis: source + documentation`

**Candle** (Abrahamsson, Myreen, Kumar, and Sewell, *ITP 2022*, LIPIcs 237, DOI `10.4230/LIPIcs.ITP.2022.3`) eliminates the LCF host-runtime TCB gap of HOL Light by implementing a HOL Light-compatible kernel and interactive REPL in **CakeML**, verifying logical soundness in HOL4, and compiling the entire prover—including lexer/parser (`candle/parser/`), kernel (`candle/standard/ml_kernel/`, `candle/prover/candle_kernelProgScript.sml`), verified compute primitive (`candle/prover/compute/`), generational garbage collector, and bignum runtime—down to x86-64, ARMv8, MIPS, and RISC-V machine code via CakeML's verified compiler.

Direct inspection of `CakeML/cakeml@2874b664` confirms the two-stage end-to-end soundness chain:

1. **Logical soundness against set theory (`candle/standard/semantics/holSoundnessScript.sml` L313–327):**
   ```hol
   Theorem proves_sound:
     is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c
   ```
   Each primitive inference rule (`ABS_correct`, `ASSUME_correct`, `BETA_correct`, `DEDUCT_ANTISYM_correct`, `EQ_MP_correct`, `INST_correct`, `INST_TYPE_correct`, `MK_COMB_correct`, `REFL_correct`) is individually proved sound with respect to a Zermelo-style set-theoretic universe (`candle/set-theory/`).
2. **Observable FFI / I/O trace soundness (`candle/prover/candle_prover_semanticsScript.sml` L428–441 & `candle/prover/candle_prover_invScript.sml` L267–273):**
   ```hol
   Theorem semantics_thm:
     semantics_prog (init_state ffi with eval_state := es)
                    init_env (candle_code ++ prog) res ∧
     eval_state_ok es ∧ prog_syntax_ok candle_code ∧
     EVERY safe_dec prog ∧ ffi.io_events = [] ∧ res ≠ Fail ⇒
       (∀outcome io_list. res = Terminate outcome io_list ⇒ EVERY ok_event io_list) ∧
       (∀io_trace. res = Diverge io_trace ⇒ every ok_event io_trace)
   ```
   Crucially, `candle_prover_invScript.sml` L267–273 maintains an invariant `state_ok ctxt s` enforcing separation between kernel reference cells (`loc ∈ kernel_locs`) and untrusted user ML references (`loc ∉ kernel_locs`), preserving type-stamp isolation (`kernel_types`) and guaranteeing `EVERY ok_event s.ffi.io_events` on **both** terminating and diverging REPL sessions. Composing `semantics_thm` with CakeML's compiler correctness theorem yields an observable guarantee at the binary boundary: any theorem statement printed to `stdout` by the compiled Candle executable is logically valid in the current HOL context under set-theoretic consistency—even when arbitrary untrusted OCaml/ML tactic code runs inside the same REPL process.

---

### 3. Dependent Type Theory Metatheory and Dual-Kernel External Replay

Dependent type theories (Calculus of Inductive Constructions, PCUIC, Lean's dependent type theory with proof-irrelevant `Prop`, quotient types, and structure $\eta$) have dramatically larger kernels than HOL or MM0 (~5,000–15,000+ LOC vs. ~700–1,200 LOC). Managing kernel soundness in this regime relies on two complementary strategies: **formalized self-verification** and **independent multi-implementation replay**.

#### 3.1 Lean4Lean (`digama0/lean4lean@67f63b0c`) vs. `lean4export` + `nanoda_lib` (`ammkrn/nanoda_lib@0da9f98f`)

`Basis: source + documentation`

| Dimension | `leanprover/lean4` C++ Kernel | `digama0/lean4lean` | `lean4export` + `ammkrn/nanoda_lib` |
| :--- | :--- | :--- | :--- |
| **Implementation language** | C++ (`src/kernel/`) | Lean 4 (`Lean4Lean/TypeChecker.lean`, 979 lines) | Rust (`src/tc.rs` 1,400 L, `env.rs` 328 L, `parser.rs` 1,083 L) |
| **Design independence** | Reference implementation | Directly ported from C++ kernel (`README.md` L3–6: *"not really an independent implementation"*) | Clean-room Rust checker over flat NDJSON export (`Export.lean`, 438 L) |
| **Memory safety (`unsafe`)** | Manual C++ memory & pointer management | Lean 4 runtime / C++ FFI | **0 `unsafe` blocks** in inspected `lib.rs`, `tc.rs`, `env.rs`, `parser.rs` (all `unsafe` tokens are `is_unsafe` schema guards `assert!(!is_unsafe)`) |
| **Formal soundness proof** | None (informal) | Partial in Lean 4 (`Lean4Lean/Verify/Environment.lean` L235 still has `\| inductDecl _ _ _ _ => sorry`) | None (relies on implementation diversity + safe Rust) |
| **`Nat`/`String` accel. default** | Always enabled in `whnf` / `lazy_delta_reduction` | Mirrors C++ kernel | **Disabled by default** (`nat_extension: false`, `string_extension: false`, `tc.rs` L360, L409) |
| **Axiom enforcement** | Cached `exportedAxiomsExt` in `#print axioms` | Fresh environment checking (`lean4lean --fresh`) | Explicit `permitted_axioms` allowlist + `unpermitted_axiom_hard_error: true` (`README.md`) |

Key engineering findings from source inspection:

1. **Lean4Lean's metatheoretic value and current verification boundary:** As Mario Carneiro notes in arXiv:2403.14064 and `README.md`, Lean4Lean mirrors the C++ kernel's algorithmic heuristics (running within ~20–50% of C++ speed on Mathlib) to formally specify Lean's type theory (`Lean4Lean.Theory`) and prove the checker sound (`Lean4Lean.Verify`). Formalizing the checker uncovered real kernel bugs (including definitional-equality edge cases involving structure $\eta$, projections, and `Prop` universe normalization—cf. `leanprover/lean4@8009d0a6` `src/kernel/type_checker.cpp` L371–377, where `is_prop` must check `normalizes_to_zero(sort_level(s))` because `imax 1 0` denotes `Prop` without being syntactically `zero`, and comparing syntactically would let `infer_proj` extract computational data from a proof and break proof irrelevance). However, at commit `67f63b0c`, `Lean4Lean/Verify/Environment.lean` L224–235 explicitly retains `| inductDecl _ _ _ _ => sorry` in `theorem addDecl.WF`, so inductive positivity and recursor-generation soundness are not yet fully discharged in the mechanized proof.
2. **True implementation diversity via `lean4export` + `nanoda_lib`:** `lean4export` (`Export.lean`) serializes only transitive kernel declarations into flat NDJSON, stripping `Expr.mdata` by default and omitting `unsafe` declarations unless `--export-unsafe` is explicitly passed (`README.md`). `nanoda_lib` parses that stream (`parser.rs` L825–921 asserting `!is_unsafe` on every axiom, opaque, inductive, constructor, and recursor), rejects unauthorized axioms by hard error, and defaults `nat_extension` and `string_extension` to `false`—requiring any kernel arithmetic acceleration to be explicitly opted in. Running both Lean 4's C++ kernel and `nanoda_lib` as a **dual-kernel gate** eliminates single-implementation C++ memory-safety and algorithm bugs without waiting for full self-verification.

#### 3.2 MetaCoq (`MetaCoq/metacoq@51b14e4b`), CertiCoq (`CertiCoq/certicoq@ab66e016`), and Rocq (`rocq-prover/rocq@25f5b18a`)

`Basis: source + documentation`

- **MetaCoq (`POPL 2020`, DOI `10.1145/3371076`):** Mechanizes the Polymorphic Cumulative Calculus of Inductive Constructions (PCUIC)—including confluence, subject reduction, a verified safe typechecker (`safechecker/theories/PCUICSafeChecker.v`, 2,585 lines, exporting `check_wf_env`, `check_type_wf_env_fast`, and soundness/completeness specs), and verified erasure of types and `Prop` proofs to untyped $\lambda$-calculus. By Gödel's second incompleteness theorem, termination of conversion inside the verified checker requires an explicit strong-normalization hypothesis (`NormalizationIn Σ`, `PCUICSafeChecker.v` L2509–2538) assumed as an axiom rather than proved within the same logic.
- **CertiCoq (`ICFP 2021`, DOI `10.1145/3473591`):** Compiles MetaCoq-erased Gallina terms through verified ANF/closure-conversion/lambda-lifting passes to CompCert Clight C (with FFI/data-representation glue in `theories/Glue/glue.v`, 1,366 lines). Composing MetaCoq + CertiCoq + CompCert closes the extraction TCB gap that otherwise forces OCaml extraction and the OCaml compiler into the TCB of Rocq-verified programs.
- **Rocq's standalone `rocqchk`/`coqchk` (`checker/safe_checking.ml` & `kernel/safe_typing.mli`):** Rocq ships an independent kernel verifier (`rocqchk`) that checks compiled `.vo` libraries from scratch. Notably, `checker/safe_checking.ml` L55–61 explicitly notes that even when importing declarations, **VM bytecode is recompiled from scratch** (`vm_library_of env clib` / `recompile_vm_library`) rather than trusting precompiled bytecode embedded in `.vo` files, keeping the trusted surface bounded. By contrast, `native_compute` (`output_native_objects` in `kernel/safe_typing.mli` L264) delegates conversion to OCaml native compilation, expanding the TCB to the full OCaml compiler toolchain.

---

### 4. Kernel, Elaborator, and Runtime Escape Surfaces in Dependent Type Provers

When automated synthesis agents or untrusted contributors produce Lean 4 or Rocq artifacts, running `#print axioms` on the final theorem is **strictly insufficient** as a security gate. Direct inspection of `leanprover/lean4@8009d0a6` exposes five distinct escape surfaces:

#### 4.1 Accelerated-Primitive Name Hijacking (`reduce_nat` $\vdash \bot$ with Zero Axioms)

`Basis: source + execution (abstract model) + derived`

In `leanprover/lean4@8009d0a6`, `src/kernel/type_checker.cpp` hardcodes 14 constant names initialized at startup (`g_nat_succ`, `g_nat_add`, `g_nat_sub`, `g_nat_mul`, `g_nat_pow`, `g_nat_gcd`, `g_nat_mod`, `g_nat_div`, `g_nat_beq`, `g_nat_ble`, `g_nat_land`, `g_nat_lor`, `g_nat_xor`, `g_nat_shiftLeft`, `g_nat_shiftRight`; e.g., L1266 `g_nat_gcd = new_persistent_expr_const({"Nat", "gcd"})`, L1271 `g_nat_land = new_persistent_expr_const({"Nat", "land"})`).

Inside `type_checker::reduce_nat` (L660–691), the kernel checks **only** `is_constant(f)` and constant-name equality (`if (f == *g_nat_land) return reduce_bin_nat_op(nat_land, e);`, L684)—it **never** verifies that `Nat.land` came from `Init`, nor that its defining body agrees with GMP/C++ `nat_land`, nor even whether the declaration is a `def` vs. `theorem` or `opaque`.

Critically, compare the two reduction paths in `type_checker.cpp`:
1. **`whnf` (L720–724):** Calls `reduce_nat(t1)` **before** `unfold_definition(t1)`.
2. **`lazy_delta_reduction(t_n, s_n)` (L1061–1073):** Gates `reduce_nat` on `if ((!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce)` (L1061). When *either* side contains a free variable (`has_fvar` is true, e.g., inside a binder), `lazy_delta_reduction` **skips `reduce_nat`** and executes `lazy_delta_reduction_step` (L1068 $\to$ L990), which invokes `unfold_definition(t_n)` on the user's definition!

**Exploit mechanism (`Basis: derived from source`):** In a standalone `prelude`-only file (or any environment where `Init.Data.Nat.Bitwise` is not imported), declaring `def Nat.land (_ _ : Nat) : Nat := Nat.zero` yields:
- Closed conversion (`!has_fvar`): `Nat.land 1 1` reduces via `reduce_nat` $\to$ `1`, so `Nat.land 1 1 = 1` holds definitionally.
- Open conversion (`has_fvar`, e.g., `∀ x : Nat, Nat.land 1 1 = (fun _ => Nat.zero) x`): `lazy_delta_reduction` skips `reduce_nat` and delta-unfolds `Nat.land`, so `Nat.land 1 1 = 0` holds definitionally.
- Transitivity derives `0 = 1`, from which `Nat.rec` derives `False` with **zero axioms** (`#print axioms` prints nothing).

**Defense:**
1. Enforce a strict **reserved-namespace policy** blocking non-sysroot declarations under `Nat`, `String`, `Bool`, `Int`, `BitVec`, `Init`, `Std`, `Lean`, and `LeanIR` (and rejecting `prelude` files in untrusted proof inputs).
2. Replay exported environments in `nanoda_lib` with `nat_extension: false` and `string_extension: false` (or verify that all `Nat.*`/`String.*` constants match cryptographic hashes of the pinned standard library).

#### 4.2 Runtime Substitution (`@[implemented_by]`, `@[extern]`, `@[csimp]`) and Compiler Reflection (`native_decide`)

`Basis: source`

In `leanprover/lean4@8009d0a6`:
- **`@[implemented_by]` (`src/Lean/Compiler/ImplementedByAttr.lean` L41–44, L46–73):** Checks only that the replacement function has matching universe-parameter count and syntactically equal type (`declType == fnType`, L69). The docstring explicitly warns: *"The provided implementation is not checked to be equivalent to the original definition. This makes it possible to prove `False` with `native_decide` using incorrect implementations."* Crucially, **kernel typechecking ignores `@[implemented_by]`**: a theorem `f = true := rfl` audits with **zero axioms** even while the compiled binary executes `badImpl` returning `false`!
- **`@[extern]` (`src/Lean/Compiler/ExternAttr.lean` L19–59):** Binds a Lean declaration to arbitrary C/C++/LLVM symbols or inline code templates (`ExternEntry.inline`, `ExternEntry.standard`, `ExternEntry.adhoc`), completely opaque to the kernel.
- **`@[csimp]` (`src/Lean/Compiler/CSimpAttr.lean` L20–60):** Safer than `@[implemented_by]` because it requires a kernel-checked equality theorem (`fromDeclName = toDeclName`), though it only rewrites code compiled *after* the attribute is registered (`linter.csimpNoncomputable`, L31).
- **`native_decide` (`src/Lean/Elab/Tactic/Decide.lean` L70–81, L202–205):** Evaluates boolean decision procedures via `nativeEqTrue` (running the compiled LCNF/C runtime rather than kernel WHNF) and trusts the result via compiler-reflection axioms (`Lean.ofReduceBool` / `Lean.trustCompiler`). Any bug in the LCNF compiler, C backend, `@[implemented_by]`, or `@[extern]` immediately becomes logical unsoundness.

**Defense:**
- Enforce an **axiom allowlist ceiling**: `{propext, Quot.sound}` for constructive proofs (or `{propext, Classical.choice, Quot.sound}` when classical logic is permitted). Hard-reject `sorryAx`, `Lean.ofReduceBool`, and `Lean.trustCompiler`.
- For verified *executables* (where runtime behavior matters, not just logical truth), audit the entire transitive call graph for `@[implemented_by]`, `@[extern]`, `unsafe`, and `partial` annotations, or use a verified compiler pipeline (CakeML/Candle or MetaCoq+CertiCoq+CompCert).
- Replace `native_decide` with kernel-checked proof-by-reflection: run an untrusted solver (SAT/SMT/LP) externally to produce a certificate `c : Cert`, prove `∀ c, check c = true → Goal` inside the kernel, and discharge `check c = true` via kernel WHNF (`decide +kernel` / `Eq.refl true`, which uses `type_checker.cpp` L1149–1153 fast reflection without leaving the kernel).

#### 4.3 Cached Axiom Tables (`exportedAxiomsExt`) and Unchecked Declaration APIs

`Basis: source`

Inspection of `leanprover/lean4@8009d0a6` reveals a subtle audit trap in the module system:
- **`src/Lean/Util/CollectAxioms.lean` L114–155:** To avoid walking imported constant bodies across module boundaries, `exportedAxiomsExt` pre-computes each declaration's axiom array during `.olean` serialization (`exportEntriesFnEx`, L126–144) and stores it as persistent environment extension state (`ExportedAxiomsState`). Downstream invocations of `collectAxioms` / `#print axioms` perform binary search over `importedModuleEntries` (L102–111) rather than traversing imported `ConstantInfo` terms!
- **`src/kernel/environment.cpp` L303–305:** Exposes `extern "C" lean_add_decl_without_checking`, calling `environment(env).add(declaration(decl, true), false)` with `check = false`.
- **`src/Lean/Environment.lean` L2918–2929:** `importModules` defaults to `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, but interactive tooling and build pipelines often load `.olean` files with extensions and plugins enabled.

**Defense:** Never trust `#print axioms` run inside an untrusted elaboration session or over untrusted pre-built `.olean` artifacts. Audit by either (a) compiling from clean audited sources and replaying in a fresh environment with `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, or (b) exporting with `lean4export` and running an independent external kernel (`nanoda_lib` with `unpermitted_axiom_hard_error: true`, or `lean4lean --fresh`).

#### 4.4 Elaboration-Time Host I/O and One-Way Specification Import Isolation

`Basis: source`

- **Elaboration-time execution:** Lean commands such as `#eval`, `run_cmd`, `by_elab`, `elab`, `macro`, and `[init]` initializers execute arbitrary compiled code—including filesystem and network I/O—*during elaboration*, before the kernel ever runs.
  - *Defense:* Parse untrusted Lean source files with parser-only entrypoints (`Lean.Parser.parseHeader` in `src/Lean/Parser/Module.lean` L85–95 and `Lean.Parser.parseCommand` at L151–161) and validate every top-level command against a closed `SyntaxNodeKind` allowlist before invoking elaboration, combined with OS-level sandboxing (no network, read-only workspace outside scratch).
- **One-way specification import isolation:** If a human-reviewed specification module imports an untrusted theory or proof module, the untrusted module can inject scoped/global notation, coercions (`Coe`), typeclass instances (`@[instance]`), macros, or `@[simp]` lemmas that silently change the elaborated AST of the specification text while leaving the human-readable surface syntax plausible.
  - *Rule:* The module import graph MUST be strictly one-way: `UntrustedProofs → TrustedSpecs → PinnedPrelude`. Trusted specification files may never import untrusted proof or tactic modules, and external checkers should pretty-print the *kernel-level* fully elaborated theorem statement (`nanoda_lib`'s `pp_declars` with `explicit: true`, `notation: null`) for final audit comparison.

---

### 5. Definitional Unfolding (`rfl` Erasure of Algebraic Scaffolding)

`Basis: source + derived`

A major practical objection to minimal-TCB kernels is ergonomics: writing proofs directly in primitive quantifiers over small-step transition systems is tedious, whereas algebraic verification frameworks (refinement preorders, Galois connections, monadic weakest preconditions, separation-logic Hoare triples, Goguen–Burstall institutions) enable compositional automation.

In intensional dependent type theories supporting $\beta\delta\iota\zeta$-conversion (Lean 4, Rocq), **algebraic scaffolding requires zero lines inside the trusted specification** whenever two conditions hold:

1. **Primitive endpoint statement:** The trusted specification states the root correctness theorem purely in primitive logical connectives ($\forall, \to, \exists, \land, \lor, =$) over ground syntax/transition types (e.g., `∀ x, P x → Q (f x)`).
2. **Transparent definitional aliases in untrusted theory:** Untrusted proof libraries define higher-level combinators as transparent `def`s that unfold definitionally to the primitive connectives—for instance:
   ```lean
   def Refines (P Q : S → Prop) : Prop := ∀ s, P s → Q s
   def WP (f : S → S) (Q : S → Prop) : S → Prop := fun s => Q (f s)
   ```
   A proof `h : Refines P (WP f Q)` assembled via transitivity, monotonicity, and framing combinators directly inhabits the trusted type `∀ s, P s → Q (f s)` by definitional equality (`rfl`), without adding `Refines`, `WP`, or any algebra lemma to the specification's AST or TCB!

**Caveats and failure modes (`Basis: derived`):**
- **Opacity barriers:** Marking any scaffold combinator `opaque`, `irreducible` (without kernel-transparent unfolding), or axiomatizing algebraic laws breaks definitional erasure and forces either an explicit bridge lemma (fine, since it still stays inside the untrusted proof term) or leaks the constant into the trusted statement (a TCB violation).
- **Kernel WHNF blowup:** If the endpoint theorem requires the kernel's `is_def_eq` to reduce deeply nested symbolic interpreters or recursive structures during type comparison, kernel checking can time out; in practice, keep endpoint statements shallow and prove equality bridges via explicit propositional rewrites (`Eq.mp`) inside the untrusted proof term rather than giant `rfl` conversions.

---

### 6. Proof-Producing and Translation-Validating Compiler Architectures

When compiling high-level programs to machine code, verification architectures sit on a spectrum determined by whether the compiler itself is verified, validated per run, or forced to emit checkable proof scripts:

#### 6.1 CompCert (`AbsInt/CompCert@2685140b`): Hybrid Verified Passes + Verified Translation Validation

`Basis: source + documentation`

CompCert (Leroy, *CACM 2009*, DOI `10.1145/1538788.1538814`) proves whole-program behavioral preservation (`driver/Compiler.v` L353 `Theorem cstrategy_semantic_preservation`) across ~20 IR lowering and optimization passes (`transf_c_program` $\to$ `transf_clight_program` $\to$ `transf_cminor_program` $\to$ `transf_rtl_program`, L120–168). Rather than verifying complex heuristic algorithms directly in Rocq, CompCert applies **translation validation** (Pnueli–Siegel–Singerman) to its hardest optimization passes—most prominently graph-coloring register allocation (Rideau & Leroy, *CC 2010*, DOI `10.1007/978-3-642-11970-5_13`):

- In `backend/Allocation.v` L1355–1365:
  ```coq
  Definition check_function (rtl: RTL.function) (ltl: LTL.function) (env: regenv): res unit := ...
  Parameter regalloc: RTL.function -> res LTL.function.
  Definition transf_function (f: RTL.function) : res LTL.function :=
    ...
    | OK tf => do x <- check_function f tf env; OK tf
  ```
- The heuristic Iterated Register Coalescing allocator (`regalloc`) is an **unverified OCaml oracle** (`Parameter`). Its output `tf` is checked on every compilation by a Rocq-verified linear-time symbolic validator (`check_function`), which verifies that every live RTL virtual register holds an identical symbolic value in its assigned LTL machine register or stack slot across all CFG edges (modeled in Python Probe 3). If the oracle has a bug, `check_function` fails closed and compilation aborts cleanly; the unverified allocator is **completely out of the TCB**.
- Similar verified-validator patterns appear in `ValueAnalysis`, `CSE`, and `Deadcode` (`Compiler.v` L133–139, `partial_if` passes).
- **Residual CompCert TCB:** Rocq kernel, OCaml extraction + OCaml compiler, C preprocessor/parser, and the final assembly pretty-printer/assembler/linker (unless paired with a verified binary emitter).

#### 6.2 Alive2 (`AliveToolkit/alive2@3bdd4f5e`): Bounded SMT Translation Validation for Production LLVM

`Basis: source + documentation`

Alive2 (Lopes et al., *PLDI 2021*, DOI `10.1145/3453483.3454030`) targets an unmodified, unverified industrial compiler (LLVM) by symbolically executing source and target LLVM IR functions (`tools/transform.cpp` L1410–1419 `exec()`, `tv/tv.cpp` L248–335) and checking refinement via Z3 (`check_refinement`, `transform.cpp` L542–766):

1. **UB refinement:** Whenever the source executes without undefined behavior (`retdom_a && src_state.getGuardableUB()`, L682), the target must also avoid UB (`tgt_state.getGuardableUB()`, L685).
2. **Poison refinement:** Whenever the source returns a non-poison value (`a.non_poison`), the target must return a non-poison value (`poison_cnstr`, L739–746, *"Target is more poisonous than source"*).
3. **`undef` & value/memory refinement:** For every source non-deterministic `undef` choice, the target's value and final memory state must refine the source (`encode_undef_refinement`, L501–538, L752–766).

**Trade-off vs. De Bruijn kernels:** Alive2 requires zero proof maintenance from LLVM developers and catches dozens of real LLVM miscompilations, but it is **not** a De Bruijn checker: loops are bounded/unrolled, complex memory transformations can time out in Z3, and the entire C++ IR-to-SMT encoder plus Z3 solver sit inside the TCB with no independently checkable proof certificate.

#### 6.3 Cogent (`au-ts/cogent@49b6ceb0`): Proof-Producing Compilation Without Compiler Verification

`Basis: source + documentation`

Cogent (O'Connor et al., *ICFP 2016*, DOI `10.1145/2951913.2951940`) exemplifies **certifying / proof-producing compilation**: an unverified Haskell compiler (`cogent/`) takes a linearly-typed, terminating systems program (designed for OS filesystems and drivers without GC) and co-generates:
1. Low-level C code;
2. A shallow functional embedding in Isabelle/HOL (for high-level functional-correctness proofs);
3. A deep embedding in Isabelle/HOL; and
4. Machine-checkable Isabelle/HOL refinement proofs connecting the shallow embedding $\to$ deep embedding $\to$ C semantics (parsed via AutoCorres/C-Parser).

Because Isabelle/HOL's LCF kernel checks the generated refinement script for every compiled program, **the entire Cogent compiler is completely outside the TCB**. The cost is language restraint (uniqueness/linear types, no unbounded recursion, FFI glue to C data structures still requires manual proof) and per-build Isabelle proof-checking latency.

---

### 7. Cross-System TCB and Architecture Comparison Matrix

`Basis: source + documentation + derived`

| System (Pinned Rev.) | Primary Checking Core | Core Size / Language | Proof vs. Statement Split | Runtime / Machine-Code Grounding | Key Escape / Residual TCB Risks |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **MM0 (`mm0-c`)** (`0d414c0b`) | Stack/unify verifier | 1,141 L C (core) | Strict physical `.mm0` vs. `.mmb` | C compiler (`mm0-c`), or bare-metal x86-64 ELF (`verifier.mm0`) | Minimal: x86-64 ISA + Linux syscalls + `.mm0` statement audit |
| **HOL Light** (`6dbb775e`) | LCF abstract `thm` | 680 L OCaml (`fusion.ml`) | None (in-process ML) | None (OCaml compiler/runtime/GC in TCB) | `Obj.magic`, C FFI, OCaml compiler/runtime bugs |
| **CakeML / Candle** (`2874b664`) | Verified HOL kernel + CakeML | Verified in HOL4; compiled to machine code | REPL state invariant separates kernel refs | Full machine-code + FFI `ok_event` I/O trace refinement | HOL4 meta-checker + ISA model + bootstrap binary |
| **Lean 4 (C++)** (`8009d0a6`) | CIC+Prop+Quot kernel | ~6k+ L C++ (`src/kernel/`) | Single-file unless manually layered | Unverified LCNF/C runtime (`@[implemented_by]`/`@[extern]`) | `reduce_nat` name hijack, `native_decide`, cached `exportedAxiomsExt`, elab I/O |
| **Lean4Lean** (`67f63b0c`) | Lean 4 kernel in Lean 4 | 979 L (`TypeChecker.lean`) + theory | `--fresh` module replay | Shares Lean 4 runtime; mirrors C++ design | Incomplete `inductDecl` verification (`sorry` at `Verify/Environment.lean` L235) |
| **`lean4export` + `nanoda_lib`** (`df81913e` / `0da9f98f`) | Clean-room Rust checker | ~2.8k L safe Rust (`tc`/`env`/`parser`) | Flat NDJSON export vs. Rust checker | Rust compiler (`rustc`); `nat`/`string` accel OFF by default | Exporter fidelity (mismatch between exported and displayed theorem if unprinted) |
| **MetaCoq + CertiCoq** (`51b14e4b` / `ab66e016`) | Verified PCUIC checker + C compiler | 2,585 L (`PCUICSafeChecker.v`) + pipeline | Erasure + verified C codegen | CompCert C backend (eliminates OCaml extraction TCB) | `NormalizationIn Σ` axiom; C glue / GC runtime (`glue.v`) |
| **Rocq (`rocqchk`)** (`25f5b18a`) | Standalone OCaml checker | Independent `.vo` verifier (`checker/`) | `.vo` replay; recompiles VM bytecode | OCaml runtime; `native_compute` adds OCaml native compiler | `native_compute`, OCaml runtime, C primitives |
| **CompCert** (`2685140b`) | Verified passes + verified validators | Rocq proofs + OCaml oracles | Per-pass simulation (`Allocation.check_function`) | Emits verified `Asm` AST; unverified `.S` printer/assembler | Rocq kernel, OCaml extraction, C parser, assembler/linker |
| **Alive2** (`3bdd4f5e`) | Bounded SMT TV | C++ IR-to-SMT + Z3 | Validates unverified LLVM IR passes | None (LLVM IR level, not machine code) | Bounded loop unrolling, SMT timeouts, C++ encoder & Z3 in TCB |
| **Cogent** (`49b6ceb0`) | Proof-producing compiler | Unverified Haskell + Isabelle/HOL | Emits C + Isabelle refinement proofs | C semantics via AutoCorres + C compiler | Isabelle/HOL kernel, C compiler (unless CompCert), manual C FFI glue |

## Boundaries

- **Live Lean 4.34.1 binary execution (`not examined`):** Although `lean` (`v4.34.1`) was present on the observation host, an unrelated concurrent workload held the host's single cgroup build slot during this session (`LSP_DEFERRED_BUILD_ACTIVE`). Consequently, the Lean 4 `Nat.land` shadowing exploit and `@[implemented_by]` + `native_decide` proof of `False` are established from direct inspection of `leanprover/lean4@8009d0a6` C++ and Lean source (`Basis: source + derived`) and modeled in Python 3.13.15 (`Basis: execution`), rather than confirmed by live Lean 4.34.1 invocation. Exact standalone `.lean` reproducers are provided in **Revalidation** so a consumer with an idle Lean toolchain can confirm execution in <2 seconds.
- **Full `nanoda_lib` crate `unsafe` audit (`not examined`):** Zero `unsafe` Rust blocks were directly verified in `src/lib.rs`, `src/tc.rs`, `src/env.rs`, and `src/parser.rs` of `ammkrn/nanoda_lib@0da9f98f`; auxiliary modules (`expr.rs`, `inductive.rs`, `level.rs`, `quot.rs`, `union_find.rs`, `unique_hasher.rs`) and transitive Cargo dependencies (`serde`, `rayon`, etc.) were not audited line by line.
- **MM0 x86-64 ELF binary bootstrap completion (`not examined`):** `examples/verifier.mm0` (29 lines) defines the exact top-level machine-code specification and `examples/x86.mm1` / `examples/mm0.mm0` supply the ISA and logic specs, but compiling and verifying the full `verifier.mm1` ELF proof end-to-end with `mm0-rs` was not executed during this investigation.
- **CompCert binary-emitter extensions (`not examined`):** CompCert's upstream `driver/Compiler.v` stops at `Asm.program` (`Asmgen.transf_program`, L147) followed by unverified assembly printing; downstream verified-assembler extensions (e.g., CompCertELF) were not examined.
- **Soundness of `NormalizationIn Σ` inside the same logic (`known not to apply`):** Neither MetaCoq nor Lean4Lean can prove strong normalization (and hence consistency) of its own type theory without a stronger metatheory (e.g., an extra Grothendieck universe or set-theoretic cardinal), per Gödel's second incompleteness theorem.
- **Alive2 as a De Bruijn proof producer (`unsupported`):** Alive2 (`AliveToolkit/alive2@3bdd4f5e`) does not emit independently checkable proof certificates for a De Bruijn kernel; its assurance relies on Z3 and its C++ semantics encoder.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)

1. **`digama0/mm0` @ `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`**
   - `mm0.md` L1–25: normative `.mm0` specification vs. untrusted proof-stream architecture.
   - `mm0-c/main.c` (79 L), `mm0-c/verifier.c` (819 L, `verify` L670–790, `CMD_PROOF_*` L382–639, `CMD_STMT_*` L709–790, lockstep `parse_until` L712/L756/L789), `mm0-c/verifier_types.c` (243 L), `mm0-c/verifier_debug.c` (322 L).
   - `examples/verifier.mm0` L1–29: `Verifier`, `Verifier_basicElf`, `Verifier_terminates`, `Verifier_Valid`.
   - `examples/x86.mm1` (5,940 L), `examples/mm0.mm0` (1,367 L), `examples/compiler.mm1` (33 L).
2. **`CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`**
   - `candle/README.md` L1–28, `candle/prover/README.md` L1–35.
   - `candle/standard/semantics/holSoundnessScript.sml` L313–327: `Theorem proves_sound`.
   - `candle/prover/candle_prover_invScript.sml` L267–273: `state_ok` (`kernel_locs`, `kernel_types`, `EVERY ok_event s.ffi.io_events`).
   - `candle/prover/candle_prover_semanticsScript.sml` L428–441: `Theorem semantics_thm`.
   - `candle/prover/candle_kernelProgScript.sml` L1–165.
3. **`jrh13/hol-light` @ `6dbb775efdff7f75aa20006532bf6336bc645861`**
   - `fusion.ml` L12–81 (680 L total): `module type Hol_kernel`, abstract `type thm`, 10 inference rules.
4. **`leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`**
   - `src/kernel/type_checker.cpp`: `is_prop` `imax 1 0` normalization comment (L371–377); `reduce_bin_nat_op` & `reduce_nat` 14 hardcoded `Nat.*` names (L602–691, L1266–1271); `whnf` calling `reduce_nat` before `unfold_definition` (L718–729); `lazy_delta_reduction` gating `reduce_nat` on `(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce` before `lazy_delta_reduction_step` / `unfold_definition` (L990, L1057–1074); `is_def_eq_core` reflection fast-path (`g_bool_true`, L1149–1153).
   - `src/kernel/environment.cpp` L303–305: `lean_add_decl_without_checking`.
   - `src/Lean/Compiler/ImplementedByAttr.lean` L41–73: unchecked replacement warning and type-only check.
   - `src/Lean/Compiler/ExternAttr.lean` L19–59: `ExternEntry` (`adhoc`, `inline`, `standard`, `opaque`).
   - `src/Lean/Compiler/CSimpAttr.lean` L20–60: proof-backed compiler simplification and `linter.csimpNoncomputable`.
   - `src/Lean/Elab/Tactic/Decide.lean` L70–81, L202–205: `elabNativeDecideCore` via `nativeEqTrue`.
   - `src/Lean/Util/CollectAxioms.lean` L96–155: `ExportedAxiomsState` and `exportedAxiomsExt` cached `.olean` axiom lookup.
   - `src/Lean/Environment.lean` L2918–2929: `importModules` (`trustLevel := 0`, `plugins := #[]`, `loadExts := false`).
   - `src/Lean/Parser/Module.lean` L85–95 (`parseHeader`), L151–161 (`parseCommand`).
5. **`digama0/lean4lean` @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`**
   - `README.md` L1–45; `Lean4Lean/TypeChecker.lean` (979 L); `Lean4Lean/Verify/TypeChecker.lean` (252 L); `Lean4Lean/Verify/Environment.lean` L224–235 (`addDecl.WF` with `| inductDecl _ _ _ _ => sorry`).
6. **`leanprover/lean4export` @ `df81913eee5519d5a88ae5b0fd701b5298cc29ab`** & **`ammkrn/nanoda_lib` @ `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`**
   - `lean4export/README.md`, `lean4export/Export.lean` (438 L).
   - `nanoda_lib/README.md` (`permitted_axioms`, `unpermitted_axiom_hard_error`, `nat_extension`/`string_extension` defaults, `pp_declars`), `src/tc.rs` (1,400 L, L360/L409), `src/env.rs` (328 L), `src/parser.rs` (1,083 L, L825–921 `assert!(!is_unsafe)`).
7. **`MetaCoq/metacoq` @ `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`**, **`CertiCoq/certicoq` @ `ab66e0164e7ecb63e5af95c90c8e479068bf95c2`**, **`rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`**
   - `MetaCoq`: `safechecker/theories/PCUICSafeChecker.v` (2,585 L, `NormalizationIn Σ` at L2509–2538).
   - `CertiCoq`: `README.md`, `theories/Glue/glue.v` (1,366 L).
   - `Rocq`: `checker/safe_checking.ml` (62 L, VM bytecode recompilation), `kernel/safe_typing.mli` L247–266 (`recompile_vm_library`, `output_native_objects`).
8. **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`**, **`AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`**, **`au-ts/cogent` @ `49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a`**
   - `CompCert`: `driver/Compiler.v` L120–168 (`transf_rtl_program`, `transf_c_program`), L353–393 (`cstrategy_semantic_preservation`); `backend/Allocation.v` L1345–1365 (`check_function`, `Parameter regalloc`, `transf_function`).
   - `Alive2`: `tv/tv.cpp` L248–335; `tools/transform.cpp` L501–766 (`encode_undef_refinement`, `check_refinement`), L1410–1512 (`exec`, `TransformVerify::verify`).
   - `Cogent`: `README.md`.

### Peer-Reviewed Literature

- Henk Barendregt & Freek Wiedijk (2005), *"The Challenge of Computer Mathematics"*, Phil. Trans. R. Soc. A, DOI `10.1098/rsta.2005.1650`.
- Mario Carneiro (2020), *"Metamath Zero: Designing a Theorem Prover Prover"*, CICM 2020, LNCS 12236, pp. 71–88, DOI `10.1007/978-3-030-53518-6_5` (preprint `arXiv:1910.10703`).
- Oskar Abrahamsson, Magnus O. Myreen, Ramana Kumar, & Thomas Sewell (2022), *"Candle: A Verified Implementation of HOL Light"*, ITP 2022, LIPIcs, DOI `10.4230/LIPIcs.ITP.2022.3`.
- Mario Carneiro (2024), *"Lean4Lean: Towards a Verified Typechecker for Lean, in Lean"*, `arXiv:2403.14064`.
- Matthieu Sozeau et al. (2020), *"Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"*, POPL 2020, PACMPL, DOI `10.1145/3371076`.
- Zoe Paraskevopoulou, John M. Li, & Andrew W. Appel (2021), *"Compositional Optimizations for CertiCoq"*, ICFP 2021, PACMPL, DOI `10.1145/3473591`.
- Xavier Leroy (2009), *"Formal Verification of a Realistic Compiler"*, CACM 52(7), pp. 107–115, DOI `10.1145/1538788.1538814`.
- Silvain Rideau & Xavier Leroy (2010), *"Validating Register Allocation and Spilling"*, CC 2010, LNCS 6011, DOI `10.1007/978-3-642-11970-5_13`.
- Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, & John Regehr (2021), *"Alive2: Bounded Translation Validation for LLVM"*, PLDI 2021, DOI `10.1145/3453483.3454030`.
- Liam O'Connor et al. (2016), *"Refinement through Restraint: Bringing Down the Cost of Verification"*, ICFP 2016, DOI `10.1145/2951913.2951940`.

### Executable Model Micro-Probes (`Basis: execution`, Python 3.13.15, `2026-11-19`)

Command executed: `python3 /tmp/probe_kernels.py` (self-contained script preserved inline below):

```python
#!/usr/bin/env python3
"""Micro-probes: accelerated-primitive shadowing, MM0 split, and register-alloc TV."""

def run_primitive_shadowing_probe() -> None:
    env_defs = {"Nat.land": lambda a, b: 0}
    kernel_accel = {"Nat.land": lambda a, b: a & b}
    def eval_whnf(name: str, a: int, b: int, guard: bool) -> int:
        if guard and name.startswith("Nat."):
            raise ValueError(f"REJECTED: reserved kernel-accelerated symbol {name!r}")
        return kernel_accel[name](a, b) if name in kernel_accel else env_defs[name](a, b)
    v_delta = env_defs["Nat.land"](1, 1)
    v_accel = eval_whnf("Nat.land", 1, 1, guard=False)
    print(f"unguarded: delta={v_delta}, accel={v_accel}, contradiction={v_delta != v_accel}")
    try:
        eval_whnf("Nat.land", 1, 1, guard=True)
    except ValueError as e:
        print(f"guarded: {e}")

def run_mm0_split_probe() -> None:
    axioms = {"ax_id": ("->", "P", "P"), "ax_k": ("->", "P", ("->", "Q", "P"))}
    def verify_stream(target, ops):
        st = []
        for op in ops:
            if op[0] == "AXIOM": st.append(axioms[op[1]])
            elif op[0] == "TRY_MUTATE_HEADER":
                return False, "structural rejection: proof stream has no opcode to alter .mm0 header"
            else: return False, f"unknown {op[0]}"
        return (True, "VERIFIED") if st == [target] else (False, f"conclusion mismatch: {st}")
    target = ("->", "P", "P")
    print("valid:", verify_stream(target, [("AXIOM", "ax_id")]))
    print("wrong:", verify_stream(target, [("AXIOM", "ax_k")]))
    print("mutate:", verify_stream(target, [("TRY_MUTATE_HEADER", "True")]))

def run_translation_validation_probe() -> None:
    rtl = [("const", "v1", 10), ("const", "v2", 20), ("add", "v3", "v1", "v2"), ("ret", "v3")]
    def validate(rtl_ops, ltl_ops):
        ve, me = {}, {}
        for i, (r, l) in enumerate(zip(rtl_ops, ltl_ops)):
            if r[0] == "const":
                ve[r[1]] = ("C", r[2]); me[l[1]] = ("C", l[2])
            elif r[0] == "add":
                if me.get(l[2]) != ve.get(r[2]) or me.get(l[3]) != ve.get(r[3]):
                    return False, f"pc {i}: clobbered operand"
                sym = ("ADD", ve[r[2]], ve[r[3]])
                ve[r[1]] = sym; me[l[1]] = sym
            elif r[0] == "ret" and me.get(l[1]) != ve.get(r[1]):
                return False, f"pc {i}: return mismatch"
        return True, "VALIDATED"
    ltl_good = [("const", "r0", 10), ("const", "r1", 20), ("add", "r0", "r0", "r1"), ("ret", "r0")]
    ltl_bad  = [("const", "r0", 10), ("const", "r0", 20), ("add", "r0", "r0", "r0"), ("ret", "r0")]
    print("good:", validate(rtl, ltl_good))
    print("bad: ", validate(rtl, ltl_bad))

if __name__ == "__main__":
    run_primitive_shadowing_probe()
    run_mm0_split_probe()
    run_translation_validation_probe()
```

Observed output (`Python 3.13.15`, exit `0`):
```text
unguarded: delta=0, accel=1, contradiction=True
guarded: REJECTED: reserved kernel-accelerated symbol 'Nat.land'
valid: (True, 'VERIFIED')
wrong: (False, "conclusion mismatch: [('->', 'P', ('->', 'Q', 'P'))]")
mutate: (False, 'structural rejection: proof stream has no opcode to alter .mm0 header')
good: (True, 'VALIDATED')
bad:  (False, 'pc 2: clobbered operand')
```

## Revalidation

1. **Lean 4 `reduce_nat` shadowing check (standalone Lean reproducer, ~1s on any idle Lean 4 toolchain):**
   Diff `src/kernel/type_checker.cpp` around `reduce_nat` and `lazy_delta_reduction` on a newer `leanprover/lean4` revision to check whether `reduce_nat` verifies module origin or `ConstantInfo` identity, or run `lean /tmp/nat_hijack.lean`:
   ```lean
   prelude
   inductive False : Prop
   inductive True : Prop where | intro : True
   inductive Eq {α : Sort u} (a : α) : α → Prop where | refl : Eq a a
   inductive Nat where | zero : Nat | succ (n : Nat) : Nat
   class OfNat (α : Type u) (_ : Nat) where ofNat : α
   instance (n : Nat) : OfNat Nat n where ofNat := n
   def Nat.land (_ _ : Nat) : Nat := Nat.zero
   def isZero : Nat → Prop | Nat.zero => True | Nat.succ _ => False
   theorem open_zero : ∀ _x : Nat, Eq (Nat.land 1 1) Nat.zero := fun _ => Eq.refl _
   theorem closed_one : Eq (Nat.land 1 1) (Nat.succ Nat.zero) := Eq.refl _
   theorem zero_eq_one : Eq Nat.zero (Nat.succ Nat.zero) :=
     @Eq.rec Nat (Nat.land 1 1) (fun n _ => Eq n (Nat.succ Nat.zero)) closed_one Nat.zero (open_zero Nat.zero)
   theorem hijack_false : False :=
     @Eq.rec Nat Nat.zero (fun n _ => isZero n) True.intro (Nat.succ Nat.zero) zero_eq_one
   #print axioms hijack_false
   ```
   If `hijack_false` typechecks with zero printed axioms, hardcoded-name `reduce_nat` shadowing remains active.
2. **Lean 4 `@[implemented_by]` + `native_decide` and `rfl` erasure checks:**
   Run `lean` on a 10-line file declaring `@[implemented_by badImpl] def specFlag : Bool := true` (with `badImpl := false`): verify `specFlag = true := rfl` reports zero axioms while `specFlag = false := by native_decide` introduces `Lean.ofReduceBool`/`Lean.trustCompiler`.
3. **Lean4Lean inductive verification progress:**
   Check `Lean4Lean/Verify/Environment.lean` in newer `digama0/lean4lean` commits for `sorry` in `theorem addDecl.WF` (at `67f63b0c`, line 235 is `| inductDecl _ _ _ _ => sorry`).
4. **External dual-kernel check (`lean4export` + `nanoda_lib`):**
   Export a target module (`lake env lean4export MyMod > out.ndjson`) and run `nanoda_lib` with `"unpermitted_axiom_hard_error": true`, `"nat_extension": false`, `"string_extension": false`, and `"pp_declars": ["MyMod.main_theorem"]` to verify both kernel replay and pretty-printed statement fidelity.
5. **Python model probes:**
   Rerun the inline Python 3.13 script in **Evidence** (`python3 /tmp/probe_kernels.py`) to confirm deterministic outputs.
