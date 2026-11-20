# Lean 4 Kernel Evaluation, Symbolic Execution, and Native-Axiom-Free Proofs for RISC-V ISA Models (Lean v4.34.1, Trust Level 0)

## Summary

Under a trust-level-0 policy that admits only `propext`, `Classical.choice`, and `Quot.sound`
(no `native_decide`, no `Lean.ofReduceBool`, no `sorry`), Lean `v4.34.1` supports both concrete
kernel evaluation and symbolic execution of Sail-style monadic RISC-V semantics, but only with
specific data structures, recursion encodings, and tactics:

1. **`bv_decide` is never admissible once it reaches its SAT stage, and has no kernel-only mode.**
   Every such proof depends on a fresh per-invocation axiom `<theorem>._native.bv_decide.ax_*`
   created by `Lean.Meta.nativeEqTrue`; it does **not** reference `Lean.ofReduceBool`. `native_decide`
   uses the same mechanism (`<theorem>._native.native_decide.ax_*`). This holds identically on
   `v4.29.0`, `v4.34.1`, and `v4.35.0`. `-t0` does not reject these proofs; only an axiom
   allowlist does. A `bv_decide` call whose goal is closed by its `bv_normalize` front end emits no
   native axiom. Re-checking a `bv_decide` certificate in the kernel fails: the LRAT parser is a
   `partial def` and the AIG bitblaster caches with `Std.HashMap`.
2. **What the kernel can and cannot reduce.** `Std.HashMap`, `Std.ExtHashMap`, `Std.ExtDHashMap`, and
   anything using `USize` are kernel-irreducible (because `System.Platform.getNumBits` is `opaque`);
   `partial` definitions and well-founded recursion with a non-`Nat` measure (`Lean.opaqueId`) are
   kernel-irreducible. Structural recursion **and well-founded recursion with a `Nat`-valued
   measure** (compiled to `WellFounded.Nat.fix`) reduce in the kernel. `@[irreducible]` affects only
   the elaborator. Closures, association lists, `Array` (List-backed in the kernel), `UInt64`,
   `BitVec` (GMP-accelerated `Nat`), and `String` reduce.
3. **Concrete execution: use `decide +kernel`** (axiom-admissible; Anneal's surface-syntax preflight
   rejects its `+kernel` configuration item in `theory/`/`correspondence/` modules — see Applicability). A Sail-V1-style `EStateM` RV64 interpreter that
   decodes real 32-bit encodings every step evaluates 1,000 steps in 0.99 s and 10,000 steps in
   6.67 s / 1.44 GB with a closure register file (≈0.6 ms and ≈0.1 MB per step), with axioms
   `[propext, Quot.sound]`. Elaborator `decide` and `rfl` exhaust the default 200,000 heartbeats by
   100 steps. `Std.HashMap`/`ExtHashMap` register files never evaluate. Consequently the
   `ExtDHashMap`-backed state of lean-sail's sequential interpreters can only be reasoned about
   with `get?_insert`-style rewriting, never by kernel evaluation.
4. **Symbolic execution practice.** riscv-zkvm proves a forward, success-only simulation from its
   hand-written RV64IM model to the generated Sail model (51 instructions, executed in M-mode with bare
   translation and PMP off; ECALL/EBREAK/FENCE/CSR excluded; upstream calls these "equivalence
   theorems"; see package `riscv-privileged-isa-model-correspondence-prior-art`) with **zero** `bv_decide`/`native_decide` invocations (a `sail_step` simp set +
   `sail_reduce` macro, per-register `ExtDHashMap.get?_insert` lemmas, a `StateRel` abstraction,
   step lemmas, `dsimproc`s, a CPS block tactic), but its own axiom gate admits four extra Sail
   platform axioms. riscv-lean uses `bv_decide` in 7 theorems. A single plain `simp` call symbolically
   executes a Sail-style `EStateM` step on a symbolic register file from a concrete instruction
   word.
5. **Native-free 64-bit arithmetic.** Typical RV64IM identities (MUL↔SLLI, DIVU↔SRLI, DIVU/REMU
   reconstruction, REMU bound, MULHU as `Nat`, ADDW, SUB as NOT+1, disjoint-bit concatenation, ring
   identities) prove with Init `BitVec` lemmas plus `toNat`/`omega`, per-bit `simp`, or `grind`'s
   ring module, all inside the allowed axiom set (11 theorems, 0.48 s total).

## Applicability

- **Toolchain.** All execution evidence was observed with the official Lean `v4.34.1` Linux
  x86_64 release (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), with `-t0` and
  `-M2048` (2048 MiB Lean memory limit) unless stated, on 2026-11-20. Source claims cite the
  `v4.34.1` tag tree. The native-axiom mechanism (Finding 1.1–1.2) was additionally executed on
  `v4.29.0` (`98dc76e3c0a9b856c9b98726b713fb04fab16740`) and `v4.35.0`
  (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) binaries, and the `v4.29.0` source tree was
  inspected for frontend layout. Other Lean versions were not examined.
- **Policy model.** "Admissible" means: `#print axioms` lists only a subset of
  `{propext, Classical.choice, Quot.sound}`. This is the policy enforced by the Anneal
  `TrustedBoundary` auditor (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`,
  `trusted/audit/TrustedBoundary.lean`), but the findings are stated for that axiom set and do not
  depend on Anneal.
- **Axiom admissibility is not surface-syntax admissibility.** At the same Anneal revision, the
  preflight syntax allowlists are stricter (source, observed 2026-11-20): `allowedTheoryTacticKinds`
  (`trusted/audit/TrustedBoundary.lean:529-557`), which governs both `theory/` and `correspondence/`
  modules, admits `decide`, `simp`, `dsimp`, `rfl`, `exact`, `rw`, `induction`, `cases`, `unfold` and
  similar tactics but not tactic configuration items (`Parser.Tactic.configItem`, so `decide +kernel` and
  `decide +native` are rejected), and not `omega`, `bv_omega`, or `grind`; `trusted/` modules are
  tactic-free; `allowedCommandKinds` (`:445-453`) excludes `set_option`, and `allowedCommandSyntaxKinds`
  (`:464-485`) excludes `termination_by`/`decreasing_by` clauses and `partial`. The `decide +kernel`,
  `omega`, `bv_omega`, `grind`, `termination_by`, and `set_option` uses in this report are therefore
  admissible by axiom footprint but would be rejected by that preflight inside Anneal-audited source
  modules (package `dual-polar-mutation-refutation-spec-strength-auditing-and-anti-vacuity-harnesses`
  likewise records the Pass-1 `decide +kernel` ban). They apply as stated to contexts that only check
  axioms (e.g. kernel replay of vendored or generated code that is not syntax-audited) or to a policy
  that admits these forms.
- **Probes** are small standalone files importing only `Init`/`Std` (A4/A5/A3 additionally
  `import Lean` for meta-programming). They model Sail's monads; they are not the generated Sail
  RISC-V model. Statements about the generated models are source-based (riscv-zkvm
  `@6810fc14d9c40373101321cefaec59df8d82e3e7`, Lean `v4.33.1` pin; riscv-lean
  `@0e3365ac7b670d79d70e9b4a8b7fba782607c44f`, Lean `v4.32.2` pin; lean-sail
  `@e4745c82fe329f162700020dcd31da6b342473b9`, Lean `v4.34.1` pin). Neither riscv-zkvm nor
  riscv-lean was built.
- **Timings** are wall-clock for the whole `lean` process, including ≈0.25–0.35 s start-up and
  `Init`/`Std` import (≈500 MB RSS baseline), on a 96-core x86_64 Linux host. Treat them as
  relative magnitudes.

## Findings

### 1. Native evaluation tactics and their axiom footprint

#### 1.1 `bv_decide` and `native_decide` add a fresh per-invocation axiom, not `Lean.ofReduceBool`

Basis: source + execution.

`src/Lean/Meta/Native.lean:37-86` (`v4.34.1`) defines the shared helper:

```lean
public def nativeEqTrue (tacticName : Name) (e : Expr) (axiomDeclRange? : Option Syntax := none) :
    MetaM NativeEqTrueResult := do
  ...  -- addAndCompile an aux `def : Bool := e`, then `unsafe evalConst Bool auxDeclName`
  let auxAxiomName ← mkAuxDeclName <| `_native ++ tacticName ++ `ax
  let axDecl := Declaration.axiomDecl {
    name := auxAxiomName, levelParams := levels,
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true), isUnsafe := false }
  addDecl axDecl
```

Callers: `bv_decide` — `LratCert.toReflectionProof`, `src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26-44`
(line 39 `nativeEqTrue `bv_decide (verifyBVExpr expr cert)`, result fed to
`unsat_of_verifyBVExpr_eq_true`); the `bv_check` path `lratChecker` (same file, lines 111-116) uses
the same function. `native_decide` — `elabNativeDecideCore`, `src/Lean/Elab/Tactic/Decide.lean:57-59`.
In `v4.29.0` the same calls live at `src/Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean:277-299`
(`LratCert.toReflectionProof`, `nativeEqTrue` at line 290) and `src/Lean/Elab/Tactic/Decide.lean:55-57`;
the `Frontend/` directory no longer exists at the `v4.34.1` tag, where the frontend is
`src/Lean/Elab/Tactic/BVDecide.lean` plus `src/Lean/Meta/Tactic/BVDecide/**`.
`Lean.ofReduceBool` and `Lean.trustCompiler` still exist (`src/Init/Core.lean:2338, 2396`) but are not
referenced by either tactic; in `v4.34.1` they and the related `Lean.reduceBool`/`Lean.reduceNat`/`Lean.ofReduceNat`
declarations carry `@[deprecated "in-kernel native reduction is deprecated; assert native evaluations with axioms instead" (since := "2026-02-01")]`
(`src/Init/Core.lean:2337-2409`).

Execution (`support/A1_axioms.lean`, `support/A6_native_axiom_by_toolchain.lean`):

```text
'a1_bvdecide_xor' depends on axioms: [propext, Classical.choice, Quot.sound, a1_bvdecide_xor._native.bv_decide.ax_1_5]
'a1_bvdecide_mul' depends on axioms: [propext, Classical.choice, Quot.sound, a1_bvdecide_mul._native.bv_decide.ax_1_5]
'a1_native' depends on axioms: [a1_native._native.native_decide.ax_1_1]
```

The A6 output is identical on `v4.29.0`, `v4.34.1`, and `v4.35.0`. All runs used `-t0`, which does
not reject them: in Lean 4 the trust level only gates *skipping* type checking above
`LEAN_BELIEVER_TRUST_LEVEL = 1024` (`src/kernel/environment.h:20-23`). Rejection therefore has to
come from an axiom check. A check that only **denylists** `Lean.ofReduceBool`/`Lean.trustCompiler`
(such as `forbiddenVendorCompilerRefs`, `joshlf/anneal@c131b320…`
`trusted/audit/TrustedBoundary.lean:1615-1617`) would not by itself catch these proofs; an
**allowlist** of axioms (or rejection of every `axiom` declaration, as that file's doc comment at
lines 75-95 describes for vendor code) does.

#### 1.2 When `bv_decide` stays admissible, and the absence of a kernel mode

Basis: source + execution.

- `BVDecideConfig` (`src/Std/Tactic/BVDecide/Syntax.lean:40-97`) has exactly the fields
  `timeout, trimProofs, binaryProofs, acNf, andFlattening, embeddedConstraintSubst, structures,
  fixedInt, enums, graphviz, maxSteps, shortCircuit, solverMode`. None of them selects kernel
  checking or reflection without native evaluation.
- If `bv_normalize` closes the goal, no SAT call and no axiom are produced
  (`src/Lean/Meta/Tactic/BVDecide/Main.lean:42-55`, `bvDecide'` returns before `bvUnsat`).
  Execution (`support/A2_axioms_more.lean`): `a2_bvdecide_trivial : x + 0 = x := by bv_decide` →
  `[propext, Classical.choice, Quot.sound]`.

#### 1.3 Re-checking a `bv_decide` certificate in the kernel fails

Basis: execution + source.

- **Replace the axiom by `Eq.refl true`** (`support/A4_kernelize_bvdecide.lean`, a `#kernelize`
  command that rewrites the `bv_decide` proof term and re-adds it with `addDecl`). The kernel must
  then evaluate `verifyBVExpr expr cert` itself. Results: 8-, 16-, and 64-bit `xor`/`and`/`or` goals →
  `(kernel) deep recursion detected`; 8-bit `x * 3 = x + x + x` → `(kernel) application type mismatch
  … argument has type true = true but function has type verifyBVExpr … = true → …`. At `-M2048` the
  file aborts with `lean::memory_exception … at 'interpreter'`; with `-M5000` it runs 15.3 s / 2.9 GB.
- **Bypass the parser** (`support/A5_kernel_lrat_check.lean`): parse the certificate at meta level,
  embed the 95 parsed LRAT actions as a closed `Array IntAction`, then
  `decide +kernel` on `LRAT.check acts (AIG.toCNF expr.bitblast.relabelNat) = true` → reduction
  "got stuck".
- **Source reasons.** `verifyCert` (`src/Std/Tactic/BVDecide/Reflect.lean:174-191`) calls
  `LRAT.parseLRATProof cert.toUTF8`, which runs `partial def parseActions`
  (`src/Std/Tactic/BVDecide/LRAT/Parser.lean:132, 301`). `partial` definitions are opaque to the
  kernel (Finding 2.4). The AIG bitblaster's structural-sharing cache is
  `{ map : HashMap (Decl α) Nat // Cache.WF decls map }` (`src/Std/Sat/AIG/Basic.lean:115-140`), and
  `Std.HashMap` is kernel-irreducible (Finding 2.1). Which blocker stops the parser-free run
  (A5) first was not localized.

#### 1.4 Axiom footprints of the non-native tactics

Basis: execution (`support/A1_axioms.lean`, `A2_axioms_more.lean`, `E1_safe_bv_identities.lean`,
`D1_irreducible_opaque.lean`). All goals over `BitVec 64` unless noted.

| tactic | probe goal | `#print axioms` |
|---|---|---|
| `bv_normalize` | `x + 0 = x` | `[propext, Classical.choice, Quot.sound]` |
| `bv_omega` | `x < 10 → x + 1 ≤ 10` | `[propext, Quot.sound]` |
| `omega` | `a < b → a + 1 ≤ b` (`Nat`) | `[propext, Quot.sound]` |
| `simp` (BitVec literal simprocs) | `0xFFFFFFFFFFFFFFFF#64 + 1#64 = 0#64` | `[propext]` |
| `decide`, `decide +kernel` | closed 64-bit product | none |
| `decide +kernel` | `∀ x : BitVec 8, x ^^^ x = 0` (256 cases) | `[propext, Quot.sound]` |
| `rfl` | closed 64-bit `sdiv` | `[propext]` |
| `grind` | `Nat` order; `Int` ring; `BitVec 64` ring `(a+b)*(a+b) = a*a + 2*a*b + b*b`; `Int` linear | `[propext, Classical.choice, Quot.sound]` |
| `simp +arith` | `a + 2 + 3 = 5 + a` | `[propext, Quot.sound]` |

All are admissible. See package `lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching`
for proof-term size and kernel replay cost of `bv_omega` and per-bit proofs.

### 2. What the Lean `v4.34.1` kernel reduces

#### 2.1 `Std.HashMap` and `USize` are kernel-irreducible

Basis: source + execution.

- `src/Init/Prelude.lean:2305`:
  `@[extern "lean_system_platform_nbits"] opaque System.Platform.getNumBits : Unit → Subtype fun (n : Nat) => Or (Eq n 32) (Eq n 64)`.
  `System.Platform.numBits` and therefore every `USize` operation are stuck in the kernel.
- `src/Std/Data/DHashMap/Internal/Index.lean:51-53`:
  `@[irreducible, inline, expose] def mkIdx (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  ⟨(scrambleHash hash).toUSize &&& (USize.ofNat sz - 1), …⟩` is the bucket index used by
  `Std.HashMap`, `Std.DHashMap` and their `Ext*` quotients.
- Execution (`support/B3_kernel_primitives.lean`, each line one `decide +kernel` example). **Fail:**
  `System.Platform.numBits = 64`; `(5 : USize).toNat = 5`;
  `((∅ : Std.HashMap Nat Nat).insert 1 2).get? 1 = some 2`; the same with `Std.ExtHashMap`.
  **Pass:** `(0xFFFFFFFFFFFFFFFF : UInt64) + 1 = 0`; `hash (5 : Nat) = 5`;
  `((Array.replicate 32 0).set! 7 9)[7]! = 9`; 64-bit literal `*`, `/`, `sdiv`; `"abc" ++ "d" = "abcd"`.

#### 2.2 lean-sail's sequential state is built on these maps

Basis: source (`rems-project/lean-sail@e4745c82fe329f162700020dcd31da6b342473b9`, Lean `v4.34.1` pin).

- Concurrency interface V2: `Sail/ArchSem.lean:131-139`
  `inductive FreeM (Eff : Type v) [Effect Eff] (α : Type w) | pure (a : α) | impure (call : Eff) (cont : Effect.ret call → FreeM Eff α)`
  and `:198-202` `abbrev PreSailM (userError : Type) := FreeM ((Except (Sail.Error userError) InstructionEffect) ⊕ FinChoice)`.
  Its sequential interpreter (`Sail/ArchSemSequential.lean:17-25, 83-90`):
  `structure SequentialState (RegisterType : Register → Type) where regs : Std.ExtDHashMap Register RegisterType; mem : Std.ExtHashMap Nat (BitVec 8); tags : Unit; cycleCount : Nat; sailOutput : Array String`,
  `abbrev ArchSemSeqM ue ty := EStateM (Sail.Error ue) (SequentialState Arch.register_type) ty`,
  `def interpretSailEffects : PreSailM ue ty → ArchSemSeqM ue ty := FreeM.liftM (…)`.
- Concurrency interface V1: `Sail/ConcurrencyInterfaceV1.lean:101-113`
  `structure SequentialState … where regs : Std.ExtDHashMap Register RegisterType; choiceState : c.α; mem : Std.ExtHashMap Nat (BitVec 8); …`,
  `abbrev PreSailM RegisterType c ue := EStateM (Sail.Error ue) (SequentialState RegisterType c)`,
  `abbrev PreSailME c ue α := ExceptT (Sail.Error ue ⊕ α) (PreSailM RegisterType c ue)`.
- Derived: by 2.1, neither interpreter's state can be evaluated by the kernel. Proofs over it must
  carry hypotheses such as `s.regs.get? Register.x1 = some a` and rewrite with
  `Std.ExtDHashMap.get?_insert`/`get?_insert_self` (the pattern used by riscv-zkvm, Finding 3.1, and by
  the RV64D proofs in package `sail-isa-models-lean-backend-and-rv64d-decoding-framing`). The V2
  effect tree itself is an inductive value and closes by `rfl` (Finding 2.5).

#### 2.3 Concrete execution of a Sail-style monadic RV64 interpreter

Basis: execution (`support/gen_b1.py`, `support/gen_b1_param.py`, `support/b1/SUMMARY.tsv`,
`support/b1scale/SUMMARY.tsv`, sample `support/b1/B1_fun_1000_dk.lean`).

The model is `abbrev M := EStateM Err St` with `structure St where regs : Regs; pc : BitVec 64`. A
structural-fuel loop `run : Nat → M Unit` runs `step`, which fetches a 32-bit word from a
`List (BitVec 32)`, decodes it with `extractLsb`/`signExtend` (ADDI, ADD, MUL, BNE), and reads and
writes registers through `rdReg`/`wrReg` (`x0` hard-wired). The program is
`addi x5,x0,0; addi x6,x0,K; addi x7,x0,3; loop: add x5,x5,x6; mul x8,x5,x7; addi x6,x6,-1; bne x6,x0,loop`
in real RV64 encodings. Each file proves `result n = v`, with `v` precomputed by a Python reference
simulator in the generator; `result` reads `x5 + x8` after `n` steps.

| register file `Regs` | n=10 | n=100 | n=1,000 | n=3,000 | n=10,000 |
|---|---|---|---|---|---|
| `Nat → BitVec 64` (closure update) | 0.37 s / 505 MB | 0.43 s / 517 MB | 0.99 s / 599 MB | 2.39 s / 784 MB | 6.67 s / 1,444 MB |
| `List (Nat × BitVec 64)` (assoc list) | 0.34 s | 0.46 s | 1.25 s / 628 MB | 2.88 s / 867 MB | 8.37 s / 1,728 MB |
| `Array (BitVec 64)` | 0.44 s | 0.55 s | 2.23 s / 833 MB | 5.99 s / 1,493 MB | `(kernel) excessive memory consumption detected` (17.1 s) |
| `Std.HashMap Nat (BitVec 64)` | stuck | stuck | stuck | – | – |
| `Std.ExtHashMap Nat (BitVec 64)` | stuck | stuck | stuck | – | – |

All entries use `decide +kernel`. Every successful proof has axioms `[propext, Quot.sound]`. The
HashMap variants are stuck even at n = 1. With elaborator `decide` or `rfl`, every representation
fails at n = 100 and n = 1,000 with `(deterministic) timeout at whnf, maximum number of heartbeats
(200000)` (≈7–8 s, ≈2.79 GB); they succeed at n ≤ 10.

The difference is in `src/Lean/Elab/Tactic/Decide.lean:83-110`. Default `decide` (`doElab`) first
reduces the `Decidable` instance with heartbeat-limited `Meta.whnf` at default transparency;
`decide +kernel` (`doKernel`) passes `mkDecideProof` directly to the kernel via `mkAuxLemma`.

From n = 1,000 to n = 10,000 the closure register file costs ≈0.63 ms and ≈0.095 MB per decoded and
executed instruction. Kernel memory grows roughly linearly with trace length. Package
`lean-large-isa-and-compiler-semantics-scaling` reports 100,000 steps at 650 MB using a
continuation-passing forcing trick (`forceMach`) with `by rfl`; this report's naive monadic style
does not use that trick.

#### 2.4 Recursion encodings

Basis: execution (`support/B2_recursion_freem.lean`, `support/B4_k6_runWF10_kernel.lean`) + source.

| encoding | elaborator `decide` | kernel `decide +kernel` |
|---|---|---|
| structural fuel (`sumFuel 1000 0 = 500500`) | – | OK, no axioms |
| `termination_by n - i` (Nat measure): `sumWF 0 10/200/2000 0` | **fails** (stuck) | **OK** `[propext, Quot.sound]` |
| exact `runWF10` from package `lean-large-isa-and-compiler-semantics-scaling` (`termination_by limit - st.pc`, `pc : Nat`), 100 and 10,000 recursive calls | **fails** (`decide` and `rfl`) | **OK** `[propext, Quot.sound]`, file 0.96 s |
| `termination_by m n => (m, n)` (lexicographic): `ack 1 1 = 3` | – | **stuck** |
| `partial def sumPartial` | – | **stuck** |

Source: `src/Lean/Elab/PreDefinition/WF/Fix.lean:281-305`. `isNatLtWF` recognizes
`invImage _ Nat f Nat.lt_wfRel`, and then `mkFix` uses ``mkConst `WellFounded.Nat.fix``. Otherwise
it builds `WellFounded.fix` with the well-foundedness proof wrapped in `Lean.opaqueId`.
`src/Init/WF.lean:483-499` documents `WellFounded.Nat.fix` with: "In contrast to `WellFounded.fix`,
this fixpoint operator reduces on closed terms. (More precisely: when `h x` evaluates to a ground
value)". It is implemented by `Nat.rec` on fuel `Nat.eager (h x + 1)`.

`#print runWF10` in B4 shows:
`@[irreducible] def runWF10 : Nat → MachState → MachState := fun limit => WellFounded.Nat.fix (fun x => limit - x.pc) fun st a => if h : st.pc < limit then a (step10 st) ⋯ else st`.
The `@[irreducible]` attribute is why elaborator `decide`/`rfl` fail, and the kernel ignores it
(Finding 2.6).

#### 2.5 Free-monad (Sail V2-style) programs

Basis: execution (`support/B2_recursion_freem.lean`).

The probe models lean-sail's `FreeM` with two effects (`rd r`, `wr r v`) and interprets it into
`EStateM String (Nat → BitVec 64)`.

- `execAdd 3 1 2 = .impure (.rd 1) (fun a => .impure (.rd 2) (fun b => .impure (.wr 3 (a + b)) .pure))`
  closes by `rfl`.
- `resultFree 1000 = 3000` (1,000 interpreted ADDs) closes by `decide +kernel` with **no axioms**.
  The whole file takes 1.98 s / 628 MB.

#### 2.6 Reducibility attributes versus `opaque`

Basis: execution (`support/D1_irreducible_opaque.lean`).

- `@[irreducible] def fIrr (n : Nat) := n + 1`: `fIrr 3 = 4` passes by `decide +kernel` (no axioms)
  and fails by `decide`.
- `opaque gOpq : Nat → Nat := fun n => n + 1`: `gOpq 3 = 4` fails by `decide +kernel`.

Reducibility attributes steer the elaborator (`whnf`, `simp`, `decide`) only. `opaque`, `partial`,
and `Lean.opaqueId` block the kernel.

### 3. Symbolic execution of Sail-generated RISC-V code in existing developments

#### 3.1 riscv-zkvm

Basis: source (`Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7`; Lean `v4.33.1`;
lean-sail `079463134b9c50450b8393e1566a09fc492a34d9`, i.e. the V1 `EStateM` interface).

- **Sail monad plumbing.** `RiscvZkvm/Rv64/SailEquiv/SailStepAttr.lean:18` has
  `register_simp_attr sail_step`. In `RiscvZkvm/Rv64/SailEquiv/VmemReduction.lean:47-59`:

  ```lean
  attribute [sail_step]
    SailME.run PreSail.PreSailME.run PreSail.readReg
    EStateM.map EStateM.bind EStateM.pure EStateM.get
    bind pure get MonadState.get getThe MonadStateOf.get
    ExceptT.run ExceptT.mk ExceptT.bind ExceptT.bindCont ExceptT.lift ExceptT.pure
    MonadLift.monadLift monadLift liftM Functor.map
  syntax "sail_reduce" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
  macro_rules
    | `(tactic| sail_reduce) => `(tactic| simp +decide only [sail_step])
    | `(tactic| sail_reduce [$args,*]) => `(tactic| simp +decide only [sail_step, $args,*])
  ```

  Per-register read lemmas live in `MonadLemmas.lean:44-80`, e.g.
  `runSail_rX_bits_x1 (h : s.regs.get? Register.x1 = some v) : runSail (rX_bits (regidx.Regidx 1)) s = some (v, s)`,
  proved by `simp [runSail, rX_bits, rX, …, PreSail.readReg, h, …]`. `runSail_bind` (lines 25-33)
  turns `EStateM` binds into `Option` matches.
- **Register-map abstraction.** `StateRel.lean:264-266`:
  `structure StateRel (sRv : MachineState) (sSail : SailState) : Prop where reg_agree : ∀ (r : Reg), sailRegVal sSail r = some (sRv.getReg r) …`.
  Here `sailRegVal` (`:128-134`) is a 32-way match returning `some 0#64` for `x0` and
  `s.regs.get? Register.xN` otherwise. Proofs rewrite with `Std.ExtDHashMap.get?_insert[_self]`
  (e.g. `StateRel.lean:242-247, 287, 391-407`; `ALUProofs.lean:48-56`).
- **Bit-level facts without SAT.** `VmemReduction.lean` `append8_eq_or_shifts` proves 64-bit
  little-endian byte assembly with `BitVec.eq_of_getLsbD_eq`, `simp only [BitVec.getLsbD_*]`, and
  eight `rcases Nat.lt_or_ge i (8·k)` cases closed by `simp`/`omega`/`rfl`.
- **Computable-model side.**
  - `RiscvZkvm/Rv64/Execution.lean:528-532`:
    `@[simp] theorem step_non_ecall_non_mem (hfetch : s.code s.pc = some i) (hne : i ≠ .ECALL) (hnb : i ≠ .EBREAK) (hnm : i.isMemAccess = false) : step s = some (execInstrBr s i)`.
  - `Logic/Tactics/SymStep.lean:72-85`: `sym_step h` ≔ `first | (rw [step_non_ecall_non_mem $h (by intro hEq; cases hEq) (by intro hEq; cases hEq) (by simp [Instr.isMemAccess])]; simp only [execInstrBr]) | (simp only [step_non_ecall_non_mem …, execInstrBr])`.
  - `Logic/Tactics/RunBlock.lean:1364`: `elab "runBlock" specs:ident* : tactic` resolves
    `@[spec_gen_rv64]` per-instruction specs, frames them with `seqFrame`, normalizes addresses
    (fallback `simp only [signExtend12_…] <;> bv_omega`, line 159), and permutes the
    separation-logic postcondition of a `cpsTripleWithin` goal.
  - `Logic/SignExtendSimproc.lean:66-99`: `dsimproc_decl reduceSignExtend12/13/21`, plus a
    `signext` macro that runs `simp only [reduce…]` then `first | bv_omega | rfl | decide`.
- **Tactic census.** Counted with `grep -rwo` over hand-owned `RiscvZkvm/**`, excluding generated
  `RiscvZkvm/Sail/**`: `omega` 602, `decide` 445, `grind` 170, `bv_omega` 62. **`bv_decide` and
  `native_decide` have 0 invocations**; their 5 + 3 textual hits are prose or backticked
  mentions, and `scripts/check-forbidden-tactics.sh --report` prints "(none)". The generated tree
  has 0 hits.
- **Axiom gate.** `scripts/AxiomSweep.lean:47-53` sets
  `allowedAxioms := [propext, Classical.choice, Quot.sound, load_reservation, match_reservation, plat_term_write, sys_enable_experimental_extensions]`,
  and `docs/validation.md:150-171` documents "exactly seven axioms". Declarations that reach any of
  the four Sail platform axioms would fail a three-axiom policy; which ones do was not determined.
- **Documentation note.** The repository's comments in `scripts/check-forbidden-tactics.sh` and
  `scripts/AxiomSweep.lean` say these tactics seal results behind `Lean.ofReduceBool` /
  `Lean.trustCompiler`. Per Finding 1.1, on Lean ≥ `v4.29.0` they emit `_native.*.ax_*` axioms
  instead. The gates still catch them, because one is a source scan and the other an allowlist.

#### 3.2 riscv-lean

Basis: source (`opencompl/riscv-lean@0e3365ac7b670d79d70e9b4a8b7fba782607c44f`; Lean `v4.32.2`; requires
`opencompl/sail-riscv-lean@11d8fa212a60c05dcc9fe5db925dd4d06dad65b5` and lean-sail
`079463134b9c50450b8393e1566a09fc492a34d9` per `lake-manifest.json`).

- Monadic Sail is related to "skeletons". `RISCV/Skeleton.lean`:
  `def skeleton_binary (rs2 rs1 rd : regidx) (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do let rs1_val ← rX_bits rs1; let rs2_val ← rX_bits rs2; wX_bits rd (execute_func rs1_val rs2_val); pure RETIRE_SUCCESS`.
  Per-instruction lemmas follow in `RISCV/SailToRV64.lean`, e.g.
  `theorem itype_addi_eq : execute_ITYPE imm rs1 rd iop.ADDI = skeleton_unary rs1 rd (fun val1 => SailRV64.itype imm val1 iop.ADDI) := by simp [execute_ITYPE, SailRV64.itype, skeleton_unary]`,
  `addiw_eq … := by rfl`. `utype_eq` unfolds `Sail.ConcurrencyInterfaceV1.PreSail.readReg` and
  `EStateM.get/bind` under a `s.regs.get? Register.PC = some valt` hypothesis.
- No custom tactics, simprocs, or simp attributes. Counts with `grep -rwo` over `RISCV/`: `simp` 302,
  `omega` 93, `bv_decide` 7, `grind` 5, `native_decide` 0, `bv_omega` 0.
- The 7 `bv_decide` invocations are at `RISCV/SailToRV64.lean:106` (`shiftiop_srai_eq`) and
  `RISCV/SailPureToInstructions.lean:718` (`zbb_orcb_eq`), `:728` (`zbb_rev8_eq`), `:849`
  (`reverse_bits_eq`), `:859` (`zbkb_brev8_eq`), `:893` (`not_eq`), `:961` (`zextb_eq`). Derived (from
  Finding 1.1 and the `v4.29.0`/`v4.34.1`/`v4.35.0` observations): on these toolchains each would
  carry a `_native.bv_decide.ax_*` axiom and be rejected under the three-axiom policy, as would
  anything depending on them. The project's own `v4.32.2` pin was not executed.

#### 3.3 One `simp` call symbolically executes a Sail-style step

Basis: execution (`support/S1_symbolic_step.lean`, built on the B1 closure-register model).

```lean
theorem s1_add_step (r : Regs) :
    step.run { regs := r, pc := 12#64 } =
      .ok () { regs := Regs.set r 5 (Regs.get r 5 + Regs.get r 6), pc := 16#64 } := by
  simp [step, code, rdReg, wrReg, advance, EStateM.run, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure]
```

The register file `r` is fully symbolic; the instruction word is concrete and decoded by `simp`'s
BitVec literal simprocs. A three-instruction straight-line version (`add`, `mul`, `addi`) closes
with the same `simp` call. Both depend on `[propext, Quot.sound]`; the file takes 0.54 s / 512 MB.
`Regs.get`/`Regs.set` stay folded, so the register map remains abstract. Growth of this approach
with block length was not measured beyond three instructions.

### 4. Keeping kernel cost and memory per theorem small

Basis: execution (Findings 2.3–2.6) + derived.

1. **Per-theorem budget (derived from 2.3).** Naive monadic concrete evaluation grows kernel memory
   by ≈0.1 MB per step, so one `decide +kernel` theorem holds about 10⁴ concrete steps under 2048 MiB
   (≈5×10³ with `Array`). Longer traces need chained segment theorems, or the CPS forcing trick in
   package `lean-large-isa-and-compiler-semantics-scaling`. The chaining lemma
   `run (a + b) = run a >>= fun _ => run b` should follow for structural fuel by induction on `a`
   with the `EStateM` monad laws (derived; not mechanized here).
2. **Shielding (derived from 2.6).** `@[irreducible]`, `Hold`-style wrappers, and
   `simp only` discipline control elaborator blow-up but do not reduce kernel re-checking. Only
   splitting into separately checked theorems, referenced by constant, bounds kernel work per
   declaration.
3. **Data structures for any kernel-evaluated layer (derived from 2.1, 2.4).** Use closures,
   association lists, `Array`, `BitVec`, `UInt64`, and structural or `Nat`-measure recursion. Avoid
   `Std.HashMap`/`ExtHashMap`/`ExtDHashMap`, `USize`, `partial`, and non-`Nat` well-founded
   measures.
4. **Decode facts.** Packages `end-to-end-verified-mir-to-isa-refinement-chain-and-seams` (decoder
   decoupled from machine state) and `sail-isa-models-lean-backend-and-rv64d-decoding-framing`
   (effect tree by `rfl`, then interpretation by `simp`) describe complementary sharding of decode
   from execute.
5. **Reflection with a verified checker.** Lean's own LRAT checker cannot be run in the kernel as
   shipped (Finding 1.3). A kernel-runnable variant would need a non-`partial` parser (or a pre-parsed
   certificate term) and a HashMap-free AIG cache. This was not attempted.

### 5. Native-free proofs of 64-bit RV64IM arithmetic identities

Basis: execution (`support/E1_safe_bv_identities.lean`, whole file 0.48 s / 502 MB, `Init` only).

| theorem | statement | proof | axioms |
|---|---|---|---|
| `e1_mul8_shl` | `x * 8#64 = x <<< 3` | `rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl` | `[propext, Quot.sound]` |
| `e1_udiv8_shr` | `x / 8#64 = x >>> 3` | `eq_of_toNat_eq; simp [toNat_udiv, toNat_ushiftRight, Nat.shiftRight_eq_div_pow]` | `[propext]` |
| `e1_divu_remu` | `(x / y) * y + x % y = x` (all `y`, incl. 0) | `eq_of_toNat_eq`; `Nat.div_mul_le_self`, `Nat.div_add_mod'`, `Nat.mod_eq_of_lt`; `omega` | `[propext]` |
| `e1_remu_lt` | `y ≠ 0 → x % y < y` | `BitVec.umod_lt` + `omega` | `[propext, Quot.sound]` |
| `e1_mulhu_nat` | `(x.zeroExtend 128 * y.zeroExtend 128).toNat = x.toNat * y.toNat` | `toNat_mul`, `toNat_setWidth`, `Nat.mul_lt_mul_of_lt_of_lt`, `Nat.pow_add` | `[propext]` |
| `e1_grind_ring` | `(a + b) * c - a * c = b * c` | `grind` | `[propext, Classical.choice, Quot.sound]` |
| `e1_sub_not` | `x - y = x + ~~~y + 1` | `sub_eq_add_neg`, `neg_eq_not_add`, `add_assoc`; `rfl` | same |
| `e1_addw` | `(x.setWidth 32 + y.setWidth 32).signExtend 64 = ((x + y).setWidth 32).signExtend 64` | `congr 1; eq_of_toNat_eq; simp [toNat_add, toNat_setWidth]; omega` | `[propext, Quot.sound]` |
| `e1_udiv_zero` | `x / 0#64 = 0#64` | `BitVec.udiv_zero` | `[propext, Quot.sound]` |
| `e1_and_or` | `(x &&& y) ||| (x &&& ~~~y) = x` | `eq_of_getLsbD_eq`; `simp [getLsbD_*]`; case split | `[propext, Classical.choice, Quot.sound]` |
| `e1_concat` | `(hi.setWidth 64 <<< 32) + lo.setWidth 64 = (hi.setWidth 64 <<< 32) ||| lo.setWidth 64` | `BitVec.add_eq_or_of_and_eq_zero`; per-bit `simp`; `BitVec.getLsbD_of_ge` | same |

Also admissible: closed-literal 64-bit `*`, `/`, `%`, `sdiv` by `decide`/`decide +kernel`/`rfl`
(Finding 1.4 and B3); `bv_omega`/`omega` for linear goals; `grind` ring normalization over
`BitVec 64`.

`e1_udiv_zero` exposes a semantic seam. Lean's `BitVec` defines `x / 0 = 0` and `x % 0 = x`, whereas
RISC-V DIVU/DIVUW return all ones for a zero divisor. A model built on Lean `BitVec` division must
special-case the divisor-0 and signed-overflow inputs.

### 6. Derived design consequences for a small kernel-reducible trusted RV64 S-mode model

Basis: derived from Findings 1–5; not executed against any particular model. Tactic recommendations
below are about axiom footprint; under Anneal's syntax allowlists (Applicability) `decide +kernel`,
`omega`, `bv_omega`, `grind`, `termination_by`, and `set_option` are not available in audited
`theory/`/`correspondence/` source, so there they apply only where those forms are admitted.

1. **Representation.** A model meant to be checked by `decide +kernel` (concrete tests, decode
   tables, finite-domain lemmas) should keep registers and CSRs in closures, structures, or
   association lists and memory in a function or list, use `BitVec`/`UInt64` arithmetic, and
   recurse structurally or by a `Nat` measure. A HashMap-backed Sail sequential state cannot serve as
   a kernel-evaluated reference; correspondence with it must go through `get?_insert` rewriting.
2. **Correspondence interface.** Generated Sail `execute` clauses yield V2 effect trees that close
   by `rfl`. Stating correspondence as "Sail effect tree ⇒ trusted-model step", with one separate
   interpreter lemma, avoids evaluating the HashMap-backed interpreter at all.
3. **Tactic choice.** Use `decide +kernel` for concrete execution. Budget about 10⁴ concrete steps
   per theorem at 2048 MiB and shard beyond that. Use plain `simp` over the step definition (Finding
   3.3) or step lemmas (Finding 3.1) for symbolic execution.
4. **Arithmetic toolkit.** Never use `bv_decide`, in any form. Use Init `BitVec` lemmas with
   `toNat`/`omega`, `grind`, per-bit `eq_of_getLsbD_eq`, `decide +kernel` on closed terms, and
   `dsimproc`s for literal normalization. riscv-zkvm shows this suffices for a full RV64IM
   equivalence. riscv-lean's 7 `bv_decide` lemmas (orc.b, rev8, brev8, srai, not, zext.b) mark exactly
   where hand proofs are needed if its approach is reused.
5. **Audit hygiene.** Keep the axiom check an allowlist. A denylist naming `Lean.ofReduceBool`
   misses `native_decide` and `bv_decide` on every toolchain examined. `-t0` alone rejects nothing.

## Boundaries

- **Not examined:** Lean versions other than `v4.29.0`, `v4.34.1`, `v4.35.0` (the `since := "2026-02-01"`
  deprecation of in-kernel native reduction suggests older toolchains may route `native_decide` through
  `Lean.ofReduceBool`; not checked). Building or running
  the generated Sail RISC-V models (riscv-zkvm, riscv-lean, sail-riscv-lean); all statements about
  them are source-based. riscv-lean on its own `v4.32.2` pin. Signed `DIV`/`REM` universal identities
  (Init has `BitVec.toInt_sdiv`, `src/Init/Data/BitVec/Bitblast.lean:1657`, and `BitVec.sdiv_eq`,
  `Lemmas.lean:4735`, but they were not exercised). Memory/CSR/trap instructions in the probe
  interpreter (only ADDI/ADD/MUL/BNE). Growth of `simp`-based symbolic execution beyond three
  instructions. Kernel cost under `lean4checker`/external checkers.
- **Unknown:**
  - Whether any form admitted by Anneal's `theory/`/`correspondence/` syntax allowlist (plain `decide`,
    `rfl`, term-mode `of_decide_eq_true`) obtains kernel-only evaluation at the scale of Finding 2.3,
    given that elaborator-level `decide`/`rfl` time out by about 100 steps.
  - Which blocker (HashMap cache, conversion, or checker data structures) stops the parser-free
    kernel LRAT check (A5).
  - Whether the `(kernel) deep recursion detected` results in A4 would become "stuck" or succeed
    with a larger `maxRecDepth`/stack.
  - Which riscv-zkvm declarations depend on the four Sail platform axioms.
  - Whether Sail's mutual `termination_by` blocks (riscv-zkvm `RiscvZkvm/Sail/PlatformConfig.lean:1179-1652`,
    `Vmem.lean:350-352`) actually compile to `WellFounded.Nat.fix`. All 10 measures there are
    `Nat`-valued `(…).toNat` expressions discharged by `decreasing_trivial => decide`
    (`RiscvExtras.lean:117`), which suggests they do, but the packed mutual relation was not printed
    or kernel-evaluated.
- **Known not to apply:** the claim "`WellFounded.fix` blocks kernel evaluation" for `Nat`-measure
  `termination_by` on `v4.34.1` (Finding 2.4). The claim "`bv_decide`/`native_decide` depend on
  `Lean.ofReduceBool`" on `v4.29.0`–`v4.35.0` (Finding 1.1). Kernel evaluation of any `Std.HashMap`-family
  structure (Finding 2.1).
- **Unsupported:** a kernel-checked or reflection-only mode of `bv_decide` in `v4.34.1`
  (`BVDecideConfig` has none).
- **Not established (attractive stronger conclusions):**
  - That `decide +kernel` throughput or memory carries over to the real generated Sail model; its
    HashMap state rules kernel evaluation out entirely.
  - That ≈0.1 MB/step is a property of the kernel rather than of this naive monadic encoding.
  - That `grind` decides arbitrary non-linear `BitVec` goals; only ring-normal identities were shown.
  - That all riscv-zkvm proofs fail a three-axiom policy; only the gate's allowance is known.
  - That no Init lemma exists for carry-mixing identities such as `(x &&& y) + (x ||| y) = x + y`.
    A text search of `src/Init/Data/BitVec/{Lemmas,Bitblast}.lean` and
    `src/Init/Data/Nat/Bitwise/Lemmas.lean` found none, but this is not exhaustive.

## Evidence

All observations were made on 2026-11-20.

- **Lean source** (`leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`,
  obtained with `git clone --depth 1 --branch v4.34.1`):
  - `src/Lean/Meta/Native.lean:37-86`
  - `src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26-44, 111-116`
  - `src/Lean/Meta/Tactic/BVDecide/Main.lean:42-55`
  - `src/Lean/Elab/Tactic/Decide.lean:57-59, 78-110`
  - `src/Std/Tactic/BVDecide/Syntax.lean:40-97`
  - `src/Std/Tactic/BVDecide/Reflect.lean:174-200`
  - `src/Std/Tactic/BVDecide/LRAT/Parser.lean:132, 301`
  - `src/Std/Tactic/BVDecide/LRAT/Checker.lean`
  - `src/Std/Tactic/BVDecide/LRAT/Internal/CompactLRATChecker.lean:27-57`
  - `src/Std/Sat/AIG/Basic.lean:115-140`
  - `src/Init/Core.lean:2338, 2396`
  - `src/Init/Prelude.lean:2305`
  - `src/Std/Data/DHashMap/Internal/Index.lean:51-53`
  - `src/Init/WF.lean:470-517`
  - `src/Lean/Elab/PreDefinition/WF/Fix.lean:281-305`
  - `src/kernel/environment.h:20-23`
- **Lean `v4.29.0` source layout** (`98dc76e3c0a9b856c9b98726b713fb04fab16740`, `git clone --filter=blob:none --no-checkout`):
  - `src/Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean:277-299` (`LratCert.toReflectionProof`)
    and `:419-424` (`bvDecide'`)
  - `src/Lean/Elab/Tactic/Decide.lean:55-57`
  - `src/Lean/Meta/Native.lean:36-80`
- **lean-sail** `e4745c82fe329f162700020dcd31da6b342473b9`: `Sail/ArchSem.lean:131-145, 195-245`;
  `Sail/ArchSemSequential.lean:1-110`; `Sail/ConcurrencyInterfaceV1.lean:95-130`.
- **riscv-zkvm** `6810fc14d9c40373101321cefaec59df8d82e3e7`:
  - `AGENTS.md`, `scripts/check-forbidden-tactics.sh`, `scripts/AxiomSweep.lean:1-110`, `docs/validation.md:150-171`
  - `RiscvZkvm/Rv64/SailEquiv/{SailStepAttr,VmemReduction,MonadLemmas,StateRel,ALUProofs}.lean`
  - `RiscvZkvm/Rv64/Execution.lean:528-540`
  - `RiscvZkvm/Rv64/Logic/Tactics/{SymStep,RunBlock}.lean`, `RiscvZkvm/Rv64/Logic/SignExtendSimproc.lean`
  - `RiscvZkvm/Sail/{PlatformConfig,Vmem,RiscvExtras}.lean` (`termination_by` survey)
- **riscv-lean** `0e3365ac7b670d79d70e9b4a8b7fba782607c44f`: `README.md`, `lake-manifest.json`,
  `RISCV/{Skeleton,SailToRV64,SailPureToInstructions,ForLean}.lean`.
- **Anneal** `c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/audit/TrustedBoundary.lean:75-95, 1600-1680`
  (axiom policy) and `:440-557` (`allowedHeaderKinds`, `allowedCommandKinds`, `allowedDeclarationKinds`,
  `allowedCommandSyntaxKinds`, `allowedTheoryTacticKinds` surface-syntax allowlists).
- **Execution probes** (in `support/`; each `X.lean` has its recorded output `X.out`). Unless noted,
  each was run as `support/run.sh support/X.lean`, i.e.
  `[wrapper] /usr/bin/time -v lean -t0 -M2048 X.lean` with the official `v4.34.1` binary. The
  recorded runs used the `anneal-lean-run --mode file --memory-max-mb 6144 --timeout 600 --` cgroup
  wrapper; any equivalent resource limit, or none, reproduces them.

| file | establishes | key output | wall / peak RSS |
|---|---|---|---|
| `A1_axioms.lean` | 1.1, 1.4 | `…_native.bv_decide.ax_1_5`, `…_native.native_decide.ax_1_1`; others admissible | 0.81 s / 691 MB |
| `A2_axioms_more.lean` | 1.2, 1.4 | `a2_bvdecide_trivial` admissible; `grind` (incl. `BitVec 64` ring) admissible | 1.47 s / 704 MB |
| `A3_list_aux.lean` | 1.3 setup | aux names `…_native.bv_decide.ax_1_5`, `…_expr_def_1_1`, `…_cert_def_1_1` | 1.11 s / 1.62 GB |
| `A4_kernelize_bvdecide.lean` (`LEANMEM=5000`) | 1.3 | `(kernel) deep recursion detected` ×3; `(kernel) application type mismatch … verifyBVExpr` | 15.3 s / 2.91 GB |
| `A5_kernel_lrat_check.lean` (`LEANMEM=5000`) | 1.3 | `95 LRAT actions`; `decide` "Reduction got stuck" | 1.19 s / 1.64 GB |
| `A6_native_axiom_by_toolchain.lean` (run directly with the `v4.29.0`, `v4.34.1`, `v4.35.0` binaries) | 1.1 | identical `_native` axioms on all three | – |
| `gen_b1.py` → 60 files `b1/B1_<regfile>_<n>_<tactic>.lean`; `batch.sh b1` → `b1/SUMMARY.tsv` | 2.3 | table in 2.3 | – |
| `gen_b1_param.py` with `K=3000 NS=3000,10000 TACS="decide +kernel" RFS=fun,array,assoc` → `b1scale/`; `batch.sh b1scale` → `b1scale/SUMMARY.tsv` | 2.3 | `B1_array_10000_dk: (kernel) excessive memory consumption detected` | – |
| `b1/B1_fun_1000_dk.lean` (sample generated file) | 2.3 | `[propext, Quot.sound]` | 0.99 s / 599 MB |
| `B2_recursion_freem.lean` | 2.4, 2.5 | `sumWF` by `decide +kernel` OK; `ack` lexicographic and `partial` stuck; `b2_free_1000` no axioms | 1.98 s / 628 MB |
| `B3_kernel_primitives.lean` | 2.1 | errors exactly at `numBits`, `USize`, `HashMap`, `ExtHashMap` lines | 0.37 s / 627 MB |
| `B4_k6_runWF10_kernel.lean` | 2.4 | corpus `runWF10`: elaborator `decide`/`rfl` fail; `decide +kernel` OK at 100 and 10,000 calls; `#print` shows `WellFounded.Nat.fix` | 0.96 s / 597 MB |
| `D1_irreducible_opaque.lean` | 2.6 | `@[irreducible]` passes `decide +kernel`; `opaque` fails | 0.24 s / 490 MB |
| `E1_safe_bv_identities.lean` | 5 | 11 theorems, all admissible | 0.48 s / 502 MB |
| `S1_symbolic_step.lean` | 3.3 | `[propext, Quot.sound]` for 1- and 3-step symbolic theorems | 0.54 s / 512 MB |

Tactic counts in 3.1/3.2 were taken with `grep -rwo --include=*.lean -e <tactic>` (riscv-zkvm:
`RiscvZkvm` with `--exclude-dir=Sail`; riscv-lean: `RISCV`).

## Revalidation

- **Native axiom mechanism (cheapest, < 1 s):** run `support/A6_native_axiom_by_toolchain.lean` on
  the new toolchain. The findings hold while `#print axioms` shows `<thm>._native.bv_decide.ax_*` and
  `<thm>._native.native_decide.ax_*`. If `Lean.ofReduceBool` reappears, or a kernel mode appears in
  `BVDecideConfig` (`src/Std/Tactic/BVDecide/Syntax.lean`), revisit Finding 1. Also diff
  `src/Lean/Meta/Native.lean` and grep for `nativeEqTrue` callers.
- **Kernel reducibility facts:** rerun `support/B3_kernel_primitives.lean` (expect exactly 4 errors:
  `numBits`, `USize`, `HashMap`, `ExtHashMap`). Rerun `support/B2_recursion_freem.lean` and
  `support/B4_k6_runWF10_kernel.lean` (expect `decide +kernel` success for the `Nat`-measure WF cases
  and failure for `ack`/`partial`). Check that `isNatLtWF`/`WellFounded.Nat.fix` still exist in
  `src/Lean/Elab/PreDefinition/WF/Fix.lean` and that `getNumBits` is still `opaque`.
- **Throughput:** `python3 support/gen_b1.py /tmp/b1 && support/batch.sh /tmp/b1` (≈2 min) and compare
  with `support/b1/SUMMARY.tsv`. For lean-sail, re-read `Sail/ArchSemSequential.lean`
  `SequentialState`; any switch away from `Std.Ext*HashMap` changes Finding 2.2.
- **Third-party practice:** rerun `scripts/check-forbidden-tactics.sh --report` in riscv-zkvm, and
  `grep -rwo bv_decide RISCV` in riscv-lean, at the new revision.
- **Safe identities:** rerun `support/E1_safe_bv_identities.lean`; failures usually mean an Init lemma
  was renamed (e.g. `BitVec.shiftLeft_eq_mul_twoPow`, `BitVec.add_eq_or_of_and_eq_zero`).
