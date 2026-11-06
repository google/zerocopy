# Lean 4 Prelude String/UTF-8 Kernel Reduction, Recursor Traps, Core Tactics, Kernel-Reducible bv_decide, Std.Do, and Std.Data Containers

## Summary

Verifying systems code, compiler passes, and machine-code artifacts in Lean 4 across `v4.30.0-rc2` (`leanprover/lean4` commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`) under a strict kernel trust boundary (`joshlf/anneal` commits `beb778bb135474a67dc017c185d2753a60693d8c` and `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`) operates under two simultaneous constraints: (a) a minimal `prelude` + `Init.NotationExtra` import closure (`trusted/lean/foundation-lock.json`) and (b) post-elaboration environment and source auditing (`trusted/audit/TrustedBoundary.lean`) that admits only `{Classical.choice, Quot.sound, propext}`, rejects `set_option` overrides (freezing `maxRecDepth = 512` and `maxHeartbeats = 200000`), rejects `deriving` clauses and `native_decide` / `Lean.trustCompiler`, rejects declarations whose `ConstantInfo.isUnsafe` or `ConstantInfo.isPartial` flag is set (including compiler-synthesized `<decl>._unsafe_rec`), and replays compiled `.olean` declarations through `Kernel.Environment.replay`.

Synthesizing source and execution evidence across `v4.30.0-rc2` and `v4.34.1` establishes nine findings across `prelude`-only kernel reduction, LCNF recursor compilation, kernel-reducible bitvector reflection (`bv_decide_kernel`), `omega` and `grind` import closures, `Std.Do` (`mvcgen`), and `Std.Data` containers:

1. **`String.toUTF8` Opacity vs. `String.ofByteArray` 2-Field Unpacking (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean`):**
   In both `v4.30.0-rc2` and `v4.34.1`, `String` (`Init/Prelude.lean:3542-3550`) is a 2-field structure `String.ofByteArray (toByteArray : ByteArray) (isValidUTF8 : ByteArray.IsValidUTF8 toByteArray)`. `String.toUTF8` (`Init/Data/String/Defs.lean:75-77`) is absent from `prelude` + `Init.NotationExtra` and is declared under `module` without `@[expose]`, making `"Hi".toUTF8` opaque across module boundaries. Matching a 1-field pattern `⟨⟨bytes⟩⟩` fails because `String.ofByteArray` has 2 explicit fields, whereas 2-field constructor unpacking `match s with | ⟨bytes, _⟩ => bytes.data.toList` (`s.toByteArray.data.toList`) reduces string literals to `List UInt8` in the kernel via `string_lit_to_constructor` (`src/kernel/expr.cpp:427-446`).
2. **`String.ofList` `:= rfl` `maxRecDepth = 512` Explosion vs. `congrArg String.ofList rfl` (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/benchmark_results.json`):**
   Proving `String.ofList cs = "literal"` with a syntactic `:= rfl` proof fails at $N = 56$ characters for computed hexadecimal lists (`bytesToHexChars`) and at $N = 82$ characters for flat `List Char` literals under `maxRecDepth = 512`. Two mechanisms combine to cause this failure: (a) in `isExprDefEqExpensive` (`Lean/Meta/ExprDefEq.lean:2217-2230`), delta unfolding (`isDefEqDelta`) runs before string-literal structural shortcutting (`isDefEqStringLit`), expanding `String.ofList` into `List.toByteArray.loop`; and (b) `@[defeq]` attribute inference (`inferDefEqAttr` in `Lean/DefEqAttrib.lean:33-35, 121-188`) inspects every theorem whose proof is syntactically `rfl` (`isRflProofCore = true`) and re-runs `isDefEq` with `smartUnfolding = false`, which unfolds `List.toByteArray.loop` into raw nested `List.brecOn` / `List.rec` terms. Replacing `rfl` with `congrArg String.ofList rfl` causes `isRflProofCore` to return `false` (skipping `smartUnfolding = false`) and unifies the `List Char` arguments via `tryHeuristic` (`Lean/Meta/ExprDefEq.lean:1498-1524`), scaling raw string literals to $N = 125$ characters (covering 118-character Stage-0 ELF64 `.o` hex artifacts) and chunked `String.ofList` equalities to $N = 1,042$ and $N = 2,048+$ characters in `131 ms`.
3. **`Nat` `BEq` (`==`) Partial Unfolding in `dsimp` vs. Opaque `BEq` Rewriting (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean`):**
   In `prelude`-only modules, `(k == idx)` on `Nat` resolves to `instBEqOfDecidableEq` (`decide (k = idx)` in `Init/Prelude.lean:1069-1070`). Running `dsimp [(· == ·), BEq.beq]` on `if (k == idx) = true then ...` unfolds `(k == idx)` inside the visible `@ite` condition `(k == idx) = true` while leaving `instDecidableEqBool (k == idx) true` un-unfolded inside `@ite`'s hidden `[Decidable c]` argument, causing `rw` and `cases` to fail with motive type mismatches. Keeping `(· == ·)` opaque and rewriting with `nat_beq_self` and `nat_eq_of_beq_eq_true` preserves syntactic alignment across both arguments of `@ite`.
4. **LCNF `List.rec` Code-Generator Rejection vs. `@Nat.rec` `@[csimp]` Support & Silent `._unsafe_rec` Emission:**
   Lean 4's LCNF code generator (`Lean/Compiler/LCNF/ToImpure.lean:183`) rejects computational definitions that invoke `@List.rec` (`code generator does not support recursor 'List.rec' yet`), whereas `@Nat.rec` succeeds because `Init/Data/Nat/Basic.lean:28-29` exports `@[csimp] theorem Nat.rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled`—the only recursor `@[csimp]` rule in `Init`. Conversely, every recursive `def` (even structurally recursive or `Prop`-valued, because `shouldGenCodeFor` in `Lean/Elab/PreDefinition/Basic.lean:134-135` checks only `!preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable`) invokes `addAndCompilePartialRec` (`Lean/Elab/PreDefinition/Structural/Main.lean:198`), registering `<decl>._unsafe_rec` (`isPartial = true`) in `env.checked`, which `TrustedBoundary.lean:1357-1358` rejects as an `unsafe/partial declaration`. Expressing computational recursion through `List.foldr`, `List.foldl`, or `@Nat.rec`—and proving inductive properties as `theorem` rather than `def`—emits zero `._unsafe_rec` constants.
5. **Lazy `ite` `Option`-Accumulator $O(2^N)$ WHNF Duplication vs. Spine-Strict `Option.casesOn` & Compositional `List.foldr`:**
   When a pass validator or certificate checker threads an accumulator `acc : Option State` that contains a free variable (such as a symbolic initial environment `env0 : Nat → Nat`), `useWHNFCache` (`Lean/Meta/WHNF.lean:1055-1061`) returns `false` because `e.hasFVar` is `true`. If the step body writes `if cond acc = true then step acc else none` without pattern-matching `acc` first, reducing `@ite` evaluates `acc` once in the condition and returns a second unreduced copy of `acc` in the `then` branch, unfolding `Option.rec` $4(2^N - 1) + 2 = \Theta(2^N)$ times and exhausting `maxHeartbeats = 200000` at $N = 16$ (`16,501 ms`). Matching `match acc with | none => none | some s => ...` before the `ite` forces `Option.casesOn` once per step, binding `s` to the constructor payload with `@Nat.rec` already eliminated and reducing `Option.rec` unfoldings to $2N + 2 = O(N)$ (`112.7 ms` at $N = 16$). Combining spine-strict steps with compositional per-block `List.foldr` (`checkMultiBlockPipeline_cons`) scales multi-block verification to $N = 1,024+$ instructions (`93.4 ms`) under default `maxRecDepth = 512`.
6. **`anneal-audit` Preflight & `Init.Prelude` Syntax Rules (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean`):**
   Five recurring syntax and identifier traps in `prelude`-only modules—the reserved `section` command keyword in structure fields, rejected `deriving` clauses, reserved `eq_*` declaration suffixes in `validateUserDeclIdent`, `Prop`-based `ite` on `a <= b`, and the `Nat.lxor` $\to$ `Nat.xor` rename in `Init/Data/Nat/Bitwise/Basic.lean:38`—have deterministic `prelude`-compatible replacements.
7. **Upstream `bv_decide` vs. In-Kernel Bitvector Reflection (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean`, `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean`):**
   In Lean `v4.30.0-rc2` and `v4.34.1`, `Lean.ofReduceBool` and `Lean.trustCompiler` are deprecated (`src/lean/Init/Core.lean:2337–2409`). Instead, `bv_decide` calls `Lean.Meta.nativeEqTrue \`bv_decide` (`src/lean/Lean/Meta/Native.lean:37–87`) inside `LratCert.toReflectionProof` (`src/lean/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26–44`), which evaluates `verifyBVExpr` via `unsafe evalConst Bool` and injects a fresh per-theorem axiom `<thm>._native.bv_decide.ax_1_5` into the kernel environment. Simply replacing `nativeEqTrue` with `Eq.refl true` on upstream `Std.Tactic.BVDecide.Reflect.verifyBVExpr` fails to reduce in the kernel because of seven independent reduction blockers across `Std.Sat` and `Std.Tactic.BVDecide`. However, upstream `bv_decide`'s normalization (`Normalize.bvNormalize`) and reflection (`Reflect.reflectBV`) front-end constructs a 100% kernel-checked proof of `bvExpr.Unsat → False` using only `{propext, Classical.choice, Quot.sound}`. Replacing only the final `bvExpr.Unsat` step yields two complete, zero-`_native`-axiom kernel reflection procedures: `KernelLRAT.checkCert` (`6.21 ms`, `[propext, Quot.sound]`) and `KernelBVDecide.checkBVLogicalUnsat` / `bv_decide_kernel` (`456 ms – 3.02 s` on 64-bit `BitVec` and `UInt64`, `[propext, Classical.choice, Quot.sound]`).
8. **`omega` and `grind` Under `prelude` and `TrustedBoundary.lean` (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean`, `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean`):**
   Neither `omega` (`src/lean/Lean/Elab/Tactic/Omega/Core.lean:107, 111, 224`; `Omega/Frontend.lean:672`) nor `grind` (`src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean:240–300`; `Grind/Main.lean:396`) ever emits native axioms; all generated proof terms depend solely on subsets of `{Classical.choice, Quot.sound, propext}`. Under an explicit `prelude` header, `omega` requires **76** transitive `Init.*` modules (51 in `foundation-lock.json` plus 25 additional `Init.*` modules), minimal `grind` (`grind -lia -ring -linarith`) requires **172** `Init.*` modules, and full `grind` requires **247** `Init.*` modules via explicit imports of `Init.Omega`, `Init.Grind`, `Init.GrindInstances`, and `Init.Data.Int.OfNat` (mandatory because `Init/Grind/*.lean` uses `module` and imports `Init.Data.Int.OfNat` privately while Cutsat's `Nat` elaborator constructs proof terms referencing `Nat.ToInt.of_le`). Expanding `foundation-lock.json` also exposes five lazy on-demand equation theorems (`List.drop.eq_def`, `List.takeWhile.eq_def`, `List.take.eq_def`, `List.eraseIdx.eq_def`, and `List.find?.eq_def`) realized independently in multiple `Init.*` modules with identical `.type` but distinct proof terms (`stored.value? true != ci.value? true`).
9. **`Std.Do` (`SPred`, `WP`, `Triple`, `mvcgen`) and `Std.Data` Containers (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean`):**
   `Std.Do` provides a universe-polymorphic weakest-precondition calculus whose verification condition generator `mvcgen` discharges stateful and exception-raising monadic specifications (`StateM`, `EStateM`) via `omega` and `grind` using only `[propext, Classical.choice, Quot.sound]`, requiring `-Dmvcgen.warning=false` and adding `` `spec `` to `TrustedBoundary.allowedAttributeNames`. For `Std.Data` containers, bundled `Std.TreeMap`, `Std.HashMap`, `Std.ExtTreeMap`, and `Std.ExtHashMap` are rejected by the kernel inside recursive inductive types (`(kernel) application type mismatch: DTreeMap.Internal.Impl.WF inner`) because the value type family occurs in a negative position inside `Impl.WF.constModify`; unbundled `Std.TreeMap.Raw` and `Std.HashMap.Raw` succeed inside recursive inductives. Finally, `Std.TreeMap` and `Std.TreeMap.Raw` reduce in the kernel (`decide +kernel` / `rfl`) with zero axioms (`[]` on `Std.TreeMap.Raw`), whereas `Std.HashMap` and `Std.HashMap.Raw` cannot reduce in the kernel even on an empty map.

## Applicability

These findings apply to Lean 4 developments across `v4.30.0-rc2` and `v4.34.1` that restrict imports to `prelude` + `Init.NotationExtra` or enforce post-elaboration kernel environment audits modeled on `joshlf/anneal`:

| Subject | Repository / Path | Revision / Digest | Role in Investigation |
| :--- | :--- | :--- | :--- |
| Lean 4 toolchain, core libraries, and tactics (`v4.30.0-rc2` baseline) | `leanprover/lean4` | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) | Baseline reference for `Init.Prelude`, `Lean/Meta`, `Lean/Compiler/LCNF`, `Std.Sat`, `Std.Tactic.BVDecide`, `Init.Omega`, `Init.Grind`, `Std.Do`, and `Std.Data`. |
| Lean 4 toolchain, core libraries, and tactics (`v4.34.1` primary target) | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `Lake version 5.0.0-src+5045d00`) | Primary source and execution environment for `Init.*`, `Std.Sat`, `Std.Tactic.BVDecide`, `Init.Omega`, `Init.Grind`, `Std.Do`, and `Std.Data`. |
| Anneal trusted audit boundary and compiler verification modules | `joshlf/anneal` | `beb778bb135474a67dc017c185d2753a60693d8c` and `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` | Trust-boundary policy (`trusted/audit/TrustedBoundary.lean`), `.olean` replay checker (`trusted/audit/src/lib.rs`), 51-module `Init.*` lock (`trusted/lean/foundation-lock.json`), and compiler verification modules (`Trusted/MirSemantics.lean`, `Trusted/Rv64Ast.lean`, `Trusted/Rv64Semantics.lean`, `theory/Anneal/Compiler/*.lean`). |
| `support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean` | Package support file | `a692c4682372e307f80d90ab5dc374f545216a568c694ed4f548ef373d54ae54` | Self-contained `prelude` + `import Init.NotationExtra` module verified with Lean `v4.34.1` (`294.8 ms`, exit code `0`, zero `._unsafe_rec` constants). |
| `support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/run_benchmarks.py` & `benchmark_results.json` | Package support files | `4e70b4a6aff0eecd85ee304e6e07c078262a8661fd46de482aaed7f45519baad` & `6c5c9df5e3461fa3cfd34b6182f5719c15da1bf089e4c88df0753b9e358acac2` | Automated scaling benchmark driver and recorded JSON output for `String.ofList`, lazy vs. spine-strict `Option` WHNF, and LCNF recursor probes. |
| `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean` | Package support file | `3d2465d2cf40724556c1f14bc7f9a3375d277148d8de3f23822930341053a6f8` | Verified Lean `v4.34.1` implementation of `KernelLRAT`, `KernelBVDecide`, and `bv_decide_kernel` contrasted against standard `bv_decide`. |
| `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean` | Package support file | `abeb3548f70a9d683b791638c6b084c050e9e780ae99d4fcacf8ec0e72c4d114` | Verified `prelude`-mode Lean `v4.34.1` probe exercising `omega` and `grind` (`lia`, `ring`, `ToInt`) under `TrustedBoundary.lean` Phase 1 and Phase 2 rules. |
| `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean` | Package support file | `1cdc3c347bde6d4f2a091b7ed374085e60b4788324998cf33cc60782ffd5bf5d` | Verified Lean `v4.34.1` probe for `Std.Do` (`mvcgen`, `@[spec]`, `StateM`, `EStateM`) and `Std.Data` (`TreeMap`, `TreeMap.Raw`, `ExtTreeMap`, `HashMap.Raw`). |
| `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean` | Package support file | `ab8544539c4a5ed319edfbed888262376cbcb6445f01d8a1f2b9b54ae2f46c42` | Verified `#guard_msgs` diagnostic isolating all 7 `verifyBVExpr` / `Std.HashMap` kernel-reduction blockers and checking `omega`/`grind` axiom footprints. |

Scope qualifications and inline operational vocabulary:

- All compilation timings, `#print axioms` footprints, and `#guard_msgs` diagnostics were observed with `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) on `x86_64-unknown-linux-gnu` using single-threaded execution (`-j1`) and a 1,024 MB memory cap (`-M1024`), and cross-checked against `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`).
- Whenever this report refers to Anneal's small-step operational outcome, trace behavior, or nondeterministic choice vocabulary, those types have the following self-contained definitions:
  ```lean
  inductive StepResult (State : Type) where
    | step (next : State)
    | done
    | trapped
    | stuck

  inductive Behavior (Obs : Type) where
    | terminates (trace : List Obs)
    | traps      (trace : List Obs)
    | diverges   (trace : Nat → Obs)
    | goesWrong

  inductive ChoiceKind where
    | demonic
    | angelic
  ```

## Findings

### Finding 1: `String.toUTF8` Kernel Opacity vs. `String.ofByteArray` 2-Field Constructor Unpacking

`Basis: source + execution`

#### Mechanical Root Cause in Lean `v4.30.0-rc2` and `v4.34.1`

In Lean 4 versions prior to the UTF-8 byte-array refactor, `String` wrapped a `List Char` (`String.mk : List Char → String`), allowing pattern matches of the form `match s with | ⟨cs⟩ => ...`. In both `v4.30.0-rc2` (`3dc1a088b6d2`) and `v4.34.1` (`5045d0056413`), `Init/Prelude.lean:3525-3550` defines `String` instead as a 2-field structure backed by a `ByteArray` and a `Prop`-valued UTF-8 validity proof:

```lean
-- Init/Prelude.lean:3525-3550
inductive ByteArray.IsValidUTF8 (b : ByteArray) : Prop where
  | intro (cs : List Char) (h : b = List.utf8Encode cs) : ByteArray.IsValidUTF8 b

structure String where
  ofByteArray ::
  toByteArray : ByteArray
  isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
```

Attempting to extract the UTF-8 byte stream of a `String` in a `prelude`-only module encounters two distinct obstacles if written using legacy idioms:

1. **`String.toUTF8` is both outside `prelude` and unexposed across `module` boundaries:** `String.toUTF8` is defined in `Init/Data/String/Defs.lean:75-77`, which is not in the transitive import closure of `prelude` + `Init.NotationExtra` (`trusted/lean/foundation-lock.json`):
   ```text
   <probe>.lean:3:7: error(lean.unknownIdentifier): Unknown constant `String.toUTF8`
   ```
   Furthermore, `Init/Data/String/Defs.lean` begins with the `module` header (line `6`) and declares `String.toUTF8` as `@[extern "lean_string_to_utf8"] def String.toUTF8 (a : @& String) : ByteArray := a.toByteArray` **without `@[expose]`** (unlike `@[expose] def String.utf8ByteSize` at lines `68-70`). Consequently, in any Lean 4 `module` file, `String.toUTF8`'s body is hidden from the kernel and elaborator:
   ```text
   <probe>.lean:3:0: error: Not a definitional equality: the left-hand side
     "Hi".toUTF8.data.toList
   is not definitionally equal to the right-hand side
     [72, 105]
   ```
2. **Single-field anonymous constructor unpacking `⟨⟨bytes⟩⟩` fails with arity mismatch:** Because `String.ofByteArray` has two explicit fields (`toByteArray : ByteArray` and `isValidUTF8 : ByteArray.IsValidUTF8 toByteArray`), matching `| ⟨⟨bytes⟩⟩ => ...` is rejected during elaboration:
   ```text
   <probe>.lean:5:4: error: Insufficient number of fields for `⟨...⟩` constructor:
   Constructor `String.ofByteArray` has 2 explicit field, but only 1 was provided
   ```

#### Verified `prelude`-Only Pattern

Unpacking both fields of `String.ofByteArray` (`| ⟨bytes, _⟩ => bytes.data.toList` or `s.toByteArray.data.toList`, as used in `Trusted/Rv64Semantics.lean:947-949` when serializing `.strtab` symbol names into ELF64 object files) compiles to `String.casesOn` (`Expr.proj `String 0 s`). When applied to a string literal `.lit (.strVal "Hi\n")`, both `Meta.whnf` (`Expr.toCtorIfLit` in `Lean/Meta/WHNF.lean:23-29`) and the C++ kernel (`string_lit_to_constructor` in `src/kernel/expr.cpp:427-446`) convert the literal to `String.ofByteArray (List.toByteArray (List.utf8Encode ...)) ...` and reduce `stringToBytes "Hi\n" = [72, 105, 10]` by `rfl`:

```lean
-- support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean:45-58
def stringToBytes (s : String) : List UInt8 :=
  match s with
  | ⟨bytes, _⟩ => bytes.data.toList

theorem stringToBytes_hi :
    stringToBytes "Hi\n" = [72, 105, 10] := rfl
```

---

### Finding 2: `String.ofList` / `List.toByteArray.loop` `maxRecDepth = 512` Explosion vs. `congrArg String.ofList rfl`

`Basis: source + execution`

#### Three-Layer Root Cause in Lean `v4.34.1`

In `Trusted/MirSemantics.lean:878-899` and `Trusted/Rv64Semantics.lean:1028-1037`, an emitted object-file artifact `art : EmittedArtifact` carries a propositional obligation `art.holds : encodeRv64ElfHex body = art.hexContents`, where `encodeRv64ElfHex` constructs a `"elf64-riscv-o:"`-prefixed hexadecimal string via `String.ofList` (`Init/Prelude.lean:3560-3561`):

```lean
-- Init/Prelude.lean:3559-3561
@[extern "lean_string_mk", expose, implicit_reducible]
def String.ofList (cs : List Char) : String :=
  { toByteArray := List.utf8Encode cs, isValidUTF8 := .intro cs rfl }
```

When a theorem attempts to prove `String.ofList cs = "literal"` using a syntactic `:= rfl` proof under default `maxRecDepth = 512`, elaboration fails with `maximum recursion depth has been reached` at **$N = 56$ characters** (`28` encoded bytes) for `bytesToHexChars` and at **$N = 82$ characters** for a flat `List Char` literal. Tracing `Lean/Meta/ExprDefEq.lean`, `Lean/Meta/WHNF.lean`, and `Lean/DefEqAttrib.lean` reveals three interacting mechanisms:

1. **Ordering of `isDefEqDelta` before `isDefEqStringLit` in `isExprDefEqExpensive` (`Lean/Meta/ExprDefEq.lean:2217-2230`):**
   Lean's definitional-equality checker includes a fast path `isDefEqStringLit` (`Lean/Meta/ExprDefEq.lean:1685-1697`) intended to rewrite `String.ofList cs =?= "..."` into `String.ofList cs =?= String.ofList ("...".toList)` without unfolding `String.ofList`. However, in `isExprDefEqExpensive` (`Lean/Meta/ExprDefEq.lean:2205-2233`), step 5 (`isDefEqDelta` at line `2217`) and step 7 (`isDefEqEtaStruct` at line `2222`) execute **before** step 11 (`isDefEqStringLit` at line `2230`):
   ```lean
   -- Lean/Meta/ExprDefEq.lean:2217-2230
   -- Step 5: If either is a constant, unfold it
   if (← isDefEqDelta t s) then return true
   ...
   -- Step 7: Eta reduction for structures
   if (← isDefEqEtaStruct t s) then return true
   ...
   -- Step 11: String literal comparison
   if (← isDefEqStringLit t s) then return true
   ```
   Because `String.ofList` is marked `@[expose, implicit_reducible]`, `isDefEqDelta` unfolds `String.ofList cs` on the LHS to `String.ofByteArray (List.utf8Encode cs) (.intro cs rfl)` at line `2217` before line `2230` is ever reached. Then `isDefEqEtaStruct` (`lines 129-165`) projects `.toByteArray` on both sides and converts the RHS string literal via `Expr.toCtorIfLit` (`Lean/Meta/WHNF.lean:27-28`) into a second `List.utf8Encode ['9', ...]` chain. Both sides are then forced through `List.utf8Encode` $\to$ `List.flatMap String.utf8EncodeChar` $\to$ `List.toByteArray` $\to$ `List.toByteArray.loop` $\to$ `ByteArray.push` $\to$ `Array.push` $\to$ `List.concat`.
2. **`inferDefEqAttr` (`Lean/DefEqAttrib.lean:33-35, 121-188`) disables `smartUnfolding` on every syntactic `:= rfl` theorem:**
   Whenever a theorem declaration has a proof term `val` for which `isRflProofCore` (`Lean/DefEqAttrib.lean:129-141`) returns `true` (namely, when the proof term's head constant is `Eq.refl`, `rfl`, `Eq.symm`, or an existing `@[defeq]` theorem), Lean `v4.34.1` automatically runs `inferDefEqAttr` $\to$ `validateDefEqAttr` $\to$ `isDefEqCareful` (`Lean/DefEqAttrib.lean:33-35`):
   ```lean
   -- Lean/DefEqAttrib.lean:33-35
   private def isDefEqCareful (e1 e2 : Expr) : MetaM Bool := do
     withOptions (smartUnfolding.set · false) <| do
       withDefault (isDefEq e1 e2) <||> withTransparency .all (isDefEq e1 e2)
   ```
   With `smartUnfolding` set to `false`, `unfoldDefinitionCore?` (`Lean/Meta/WHNF.lean:853, 913`) ignores `_sunfold` matcher equations and unfolds `List.toByteArray.loop`, `List.flatMap`, `List.map`, `List.flatten`, `List.append`, and `List.concat` into raw nested `List.brecOn` and `List.rec` applications. At $N = 81$ characters (`List.rec ↦ 948`, `List.brecOn ↦ 328`), `isDefEqCareful` sits just below `maxRecDepth = 512`; at $N = 82$ characters (or $N = 56$ characters when `cs` is produced by `bytesToHexChars`), `isDefEqCareful` exceeds `maxRecDepth = 512`.
3. **Why `congrArg String.ofList rfl` bypasses both bottlenecks:**
   - First, the proof term `congrArg String.ofList rfl` has head constant `congrArg`. In `isRflProofCore` (`Lean/DefEqAttrib.lean:129-141`), `congrArg` matches none of `Eq.refl`, `rfl`, or `Eq.symm` and does not carry `@[defeq]`, so `isRflProofCore` returns **`false`** and `inferDefEqAttr` / `isDefEqCareful` (`smartUnfolding = false`) is completely skipped.
   - Second, during elaboration of `congrArg String.ofList rfl` against expected type `String.ofList cs = "..."`, Lean unifies `String.ofList ?m.a = String.ofList ?m.b` with `String.ofList cs = "..."`. While `?m.b` is an unassigned metavariable, `String.ofList ?m.b` unfolds only as far as `List.toByteArray.loop (List.flatMap String.utf8EncodeChar ?m.b) ByteArray.empty`, where `List.toByteArray.loop` is **stuck** on `?m.b`. Once the RHS string literal unfolds to `List.toByteArray.loop (List.flatMap String.utf8EncodeChar ['9', ...]) ByteArray.empty`, both sides share head constant `List.toByteArray.loop` with a metavariable argument on the left, triggering `tryHeuristic` (`Lean/Meta/ExprDefEq.lean:1498-1524`) to unify `?m.b := ['9', ...]` directly and check `cs = ['9', ...]` in `List Char` without running `List.toByteArray.loop` on `cs`.
   - Third, if the theorem's RHS is a raw string literal `"..."`, `ensureHasType` still checks `String.ofList ['9', ...] =?= "..."` with `smartUnfolding = true`, which succeeds up to **$N = 125$ characters** (covering the 118-character Stage-0 ELF64 `.o` string in `MirToRv64Stage0.lean:1203-1212`) and reaches `maxRecDepth = 512` at $N = 126$ characters inside `List.toByteArray.loop`. When both sides of the equality are structured as `String.ofList` over chunked character lists ($\le 64$ characters per chunk so each `List.foldr` / `List.append` spine stays well below `512`), neither the elaborator nor the kernel ever unfolds `String.ofList`, scaling to $N = 1,042$ and $N = 2,048+$ characters in `131 ms`.

#### Empirical Scaling Benchmark (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/benchmark_results.json`)

All measurements below were recorded with Lean `v4.34.1` under default `maxRecDepth = 512` (baseline process startup + `prelude` / `Init.NotationExtra` import overhead: `67.0 ms`):

| $N$ (chars) | Bytes | `:= rfl` (`bytesToHexChars` vs. `"..."`) | `:= rfl` (flat `List Char` vs. `"..."`) | `congrArg String.ofList rfl` (`bytesToHexChars` vs. `"..."`) | `congrArg String.ofList rfl` (chunked `String.ofList`) |
| ---: | ---: | :--- | :--- | :--- | :--- |
| 32 | 16 | `ok` (`118.6 ms`) | `ok` (`86.2 ms`) | `ok` (`106.3 ms`) | `ok` (`111.6 ms`) |
| 54 | 27 | `ok` (threshold max) | `ok` | `ok` | `ok` |
| 56 | 28 | **`maxRecDepth`** (`136.4 ms`) | `ok` | `ok` | `ok` |
| 64 | 32 | **`maxRecDepth`** (`141.0 ms`) | `ok` (`118.9 ms`) | `ok` (`131.1 ms`) | `ok` (`126.4 ms`) |
| 70 | 35 | **`maxRecDepth`** (`144.7 ms`) | `ok` (`124.7 ms`) | `ok` (`133.5 ms`) | `ok` (`129.8 ms`) |
| 74 | 37 | **`maxRecDepth`** (`151.0 ms`) | `ok` (`122.6 ms`) | `ok` (`134.0 ms`) | `ok` (`126.2 ms`) |
| 75 | 37.5 | **`maxRecDepth`** (`151.5 ms`) | `ok` (`123.1 ms`) | `ok` (`133.8 ms`) | `ok` (`128.4 ms`) |
| 80 | 40 | **`maxRecDepth`** (`151.5 ms`) | `ok` (`130.4 ms`) | `ok` (`141.6 ms`) | `ok` (`131.3 ms`) |
| 81 | 40.5 | **`maxRecDepth`** | `ok` (threshold max) | `ok` | `ok` |
| 82 | 41 | **`maxRecDepth`** (`157.3 ms`) | **`maxRecDepth`** (`131.5 ms`) | `ok` (`145.2 ms`) | `ok` (`130.4 ms`) |
| 118 | 59 | **`maxRecDepth`** (`133.5 ms`) | **`maxRecDepth`** (`129.2 ms`) | `ok` (`165.1 ms`) | `ok` (`130.8 ms`) |
| 125 | 62.5 | **`maxRecDepth`** | **`maxRecDepth`** | `ok` (`169.6 ms`, threshold max) | `ok` (`129.1 ms`) |
| 126 | 63 | **`maxRecDepth`** (`135.7 ms`) | **`maxRecDepth`** (`125.8 ms`) | **`maxRecDepth`** (`159.6 ms`) | `ok` (`127.2 ms`) |
| 256 | 128 | **`maxRecDepth`** (`149.0 ms`) | **`maxRecDepth`** (`154.0 ms`) | **`maxRecDepth`** (`143.9 ms`) | `ok` (`123.4 ms`) |
| 512 | 256 | **`maxRecDepth`** (`170.4 ms`) | **`maxRecDepth`** (`202.5 ms`) | **`maxRecDepth`** (`135.3 ms`) | `ok` (`127.6 ms`) |
| 1042 | 521 | **`maxRecDepth`** (`167.8 ms`) | **`maxRecDepth`** (`259.2 ms`) | **`maxRecDepth`** (`131.1 ms`) | `ok` (`131.5 ms`) |
| 2048 | 1024 | **`maxRecDepth`** (`167.0 ms`) | **`maxRecDepth`** (`380.8 ms`) | **`maxRecDepth`** (`133.4 ms`) | `ok` (`131.8 ms`) |

---

### Finding 3: `Nat` `BEq` (`==`) Partial Unfolding Hazard in `dsimp` vs. Opaque `BEq` Rewriting

`Basis: source + execution`

#### Mechanical Root Cause in `Init/Prelude.lean`

In standard Lean 4 files that import `Init.Data.Nat.Basic`, `Nat` has a dedicated `@[expose] instance : BEq Nat := ⟨Nat.beq⟩`. In `prelude` + `Init.NotationExtra` modules, however, `Init.Data.Nat.Basic` is not imported, so `(k == idx)` on `Nat` synthesizes the generic `DecidableEq`-backed instance from `Init/Prelude.lean:1069-1070`:

```lean
-- Init/Prelude.lean:1069-1070
@[expose, implicit_reducible]
instance instBEqOfDecidableEq [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)
```

When a function branches on `if (k == idx) = true then val else locals k` (such as `MirEnv.updateLocal` in `Trusted/MirSemantics.lean`), the elaborated `@ite` application contains `(k == idx)` in **two** places:

```lean
@ite (Option Nat)
  ((k == idx) = true)                      -- 1. explicit Prop condition `c`
  (instDecidableEqBool (k == idx) true)    -- 2. implicit `[Decidable c]` instance
  val
  (locals k)
```

Because `dsimp` simplifies only non-dependent subterms and skips implicit `Decidable` proof/instance arguments whose types depend on the condition, calling `dsimp [updateLocal, (· == ·), BEq.beq]` unfolds `(k == idx)` inside the first argument (`decide (k = idx) = true`) while leaving `(k == idx)` **un-unfolded** inside the second argument (`instDecidableEqBool (k == idx) true`). Any subsequent `rw` or `cases` on `decide (idx = idx) = true` then abstracts only the first argument and fails with an ill-typed `@ite` motive:

```text
<probe>.lean:13:6: error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => (if _a = true then val else locals idx) = val
Error: Application type mismatch: The argument
  instDecidableEqBool (idx == idx) true
has type
  Decidable ((idx == idx) = true)
but is expected to have type
  Decidable (_a = true)
in the application
  @ite (Option Nat) (_a = true) (instDecidableEqBool (idx == idx) true)
```

#### Verified `prelude`-Only Pattern

Keep `(· == ·)` and `BEq.beq` **opaque** during `dsimp`, and rewrite or split on `(k == idx)` directly using `nat_beq_self`, `nat_eq_of_beq_eq_true`, and `nat_beq_comm` (`theory/Anneal/Compiler/MirOptPasses.lean:122-146, 189-200`, reproduced in `support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean:142-215`):

```lean
-- support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean:142-171
theorem nat_beq_self (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

theorem nat_eq_of_beq_eq_true {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

theorem updateLocal_self (locals : LocalEnv) (idx : Nat) (val : Option Nat) :
    updateLocal locals idx val idx = val := by
  dsimp [updateLocal]
  rw [nat_beq_self idx]
  rfl
```

Because `rw [nat_beq_self idx]` and `cases h : (k == idx)` abstract the opaque subterm `(idx == idx)` or `(k == idx)` simultaneously in both the proposition `((k == idx) = true)` and the instance `(instDecidableEqBool (k == idx) true)`, the `@ite` motive remains well-typed.

---

### Finding 4: LCNF Code-Generator `List.rec` Rejection vs. `@Nat.rec` / `List.foldr` Acceptance & Silent `._unsafe_rec` Emission

`Basis: source + execution`

#### 4.1 Why LCNF Rejects `@List.rec` but Accepts `@Nat.rec`, `List.foldr`, and `List.foldl`

In Lean `v4.30.0-rc2` and `v4.34.1`, every non-`Prop`, non-`theorem`, computable `def` is compiled through the LCNF pipeline (`Lean/Compiler/LCNF/Main.lean`). Prior to LCNF lowering, `Compile.preprocess` (`Lean/Compiler/LCNF/ToLCNF.lean:447`) applies all registered `@[csimp]` replacement theorems (`LCNF.CSimp.replaceConstants`). Next, `ToImpure.lean:180-185` (and `Lean/CoreM.lean:682-696`) rejects any remaining inductive recursor application that has no special compiler lowering:

```lean
-- Lean/Compiler/LCNF/ToImpure.lean:180-185
| .recInfo _ =>
  throwError "code generator does not support recursor `{declName}` yet, \
    consider using 'match ... with' and/or structural recursion"
```

- **Why `@List.rec` fails in computational `def`s:** Neither `Init/Prelude.lean` nor `Init/Data/List/Basic.lean` defines a `@[csimp]` replacement for `List.rec`. Invoking `@List.rec` inside a computational `def` therefore reaches `ToImpure.lean:183` unchanged and fails:
  ```text
  <probe>.lean:4:4: error: code generator does not support recursor `List.rec` yet,
  consider using 'match ... with' and/or structural recursion
  ```
- **Why `@Nat.rec` succeeds:** `Init/Data/Nat/Basic.lean:22-29` (which is in the transitive import closure of `Init.NotationExtra`) defines `Nat.recCompiled` and registers the **only** recursor `@[csimp]` theorem in `Init`:
  ```lean
  -- Init/Data/Nat/Basic.lean:22-29
  @[specialize] def recCompiled
      {motive : Nat → Sort u} (zero : motive 0)
      (succ : (n : Nat) → motive n → motive (n + 1)) (t : Nat) : motive t :=
    match t with
    | 0 => zero
    | n + 1 => succ n (recCompiled zero succ n)

  @[csimp] theorem rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled := by
    funext motive zero succ n
    induction n with
    | zero => rfl
    | succ n ih => simp [recCompiled, ← ih]
  ```
  `Compile.preprocess` rewrites `@Nat.rec` to `@Nat.recCompiled` before `ToImpure` runs.
- **Why `List.foldr` and `List.foldl` succeed without emitting `._unsafe_rec` in user modules:** `List.foldr` (`Init/Data/List/Basic.lean:1058`) and `List.foldl` (`Init/Prelude.lean:2885`) are already compiled inside `Init` (whose declarations are allowlisted by `TrustedBoundary.lean`'s foundation lock). Calling `List.foldr` or `List.foldl` from a user `def` is a non-recursive function application.

#### 4.2 Why Structural Recursive `def`s Emit `<decl>._unsafe_rec` and Fail `anneal-audit`

A natural impulse when `@List.rec` is rejected by LCNF is to write a structural recursive function using pattern matching:

```lean
def recDefSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + recDefSum xs
```

Even though Lean 4's structural recursion compiler (`Lean/Elab/PreDefinition/Structural/Main.lean:183-218`) proves termination using `List.brecOn` without `Init.WF`, line `198` of `Structural/Main.lean` still passes the original recursive pre-definition to `addAndCompilePartialRec` (`Lean/Elab/PreDefinition/Basic.lean:280-295`) so the LCNF code generator can compile tail-recursive loops rather than `brecOn` closures:

```lean
-- Lean/Elab/PreDefinition/Basic.lean:280-295
def addAndCompilePartialRec (preDefs : Array PreDefinition) : TermElabM Unit := do
  if preDefs.any shouldGenCodeFor then
    let us := preDefs[0]!.levelParams
    let all := preDefs.toList.map (·.declName)
    let mkUnsafe ( preDef : PreDefinition ) : Declaration :=
      .defnDecl {
        name        := Compiler.mkUnsafeRecName preDef.declName
        levelParams := us
        type        := preDef.type
        value       := preDef.value.replace fun e => ...
        safety      := .partial
        hints       := .opaque
      }
    withEnableInfoTree false do
      add Decls (preDefs.map mkUnsafe)
    compileDecls (preDefs.map (Compiler.mkUnsafeRecName ·.declName))
```

Crucially, `Compiler.mkUnsafeRecName declName` (`Lean/Compiler/Old.lean:49`) creates `<declName>._unsafe_rec` with `safety := .partial` (`ConstantInfo.isPartial = true`) and inserts it into the kernel's checked environment (`env.checked`). Even more subtly, `shouldGenCodeFor` (`Lean/Elab/PreDefinition/Basic.lean:134-135`) checks **only** syntactic declaration modifiers, not whether the return type is `Prop`:

```lean
-- Lean/Elab/PreDefinition/Basic.lean:134-135
def shouldGenCodeFor (preDef : PreDefinition) : Bool :=
  !preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable
```

Thus **every** recursive `def` (computational or `Prop`-valued) that is not marked `noncomputable` emits `<decl>._unsafe_rec` into the `.olean` environment. When `anneal-audit` (`trusted/audit/TrustedBoundary.lean:1357-1358`) inspects every declaration in the target closure, it rejects `<decl>._unsafe_rec`:

```lean
-- trusted/audit/TrustedBoundary.lean:1357-1358
if ci.isUnsafe || ci.isPartial then
  errors := errors.push s!"{label}: unsafe/partial declaration '{name}'"
```

#### Verified Zero-`._unsafe_rec` Matrix (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/benchmark_results.json`)

| Declaration Form | Example | LCNF Codegen | Emits `<decl>._unsafe_rec`? | `anneal-audit` Status |
| :--- | :--- | :--- | :--- | :--- |
| Computational `def` calling `@List.rec` | `def sumViaListRec := @List.rec ...` | **Rejected** (`ToImpure.lean:183`) | No | Fails elaboration |
| Recursive `def` (structural or `match`) | `def recDefSum \| [] => 0 \| x :: xs => ...` | Accepted (`addAndCompilePartialRec`) | **Yes (`isPartial = true`)** | **Rejected** (`unsafe/partial declaration`) |
| Computational `def` calling `List.foldr` / `List.foldl` | `evalPlaceOffset`, `updateCodeAt`, `applyRelocsToCode` | Accepted | **No (`false`)** | **Accepted** |
| Computational `def` calling `@Nat.rec` | `stepBounded`, `checkSyntheticBlock` | Accepted (via `@[csimp] Nat.rec_eq_recCompiled`) | **No (`false`)** | **Accepted** |
| Recursive `theorem` (`Prop`-valued) | `theorem list_length_append` | Skipped (`shouldGenCodeFor = false`) | **No (`false`)** | **Accepted** |

---

### Finding 5: Lazy `ite` `Option`-Accumulator $O(2^N)$ WHNF Duplication vs. Spine-Strict Pattern Matching & Compositional `List.foldr`

`Basis: source + execution`

#### Mechanical Root Cause: `useWHNFCache = false` on Free Variables + Unforced `@ite` Branches

In translation-validation and pass-certificate theorems (such as `theory/Anneal/Compiler/KancVerticalSlice.lean:271-345` and `MirOptPasses.lean`), a bounded checker folds over $N$ instructions threading an accumulator `acc : Option State` initialized with a symbolic environment parameter `(env0 : Nat → Nat)` (a free variable inside the theorem body).

Two mechanisms in `Lean/Meta/WHNF.lean` interact when `acc` is threaded through an `@ite` step without pattern-matching `acc` first:

1. **`Meta.whnf` disables its WHNF cache whenever `e.hasFVar` is `true` (`Lean/Meta/WHNF.lean:1055-1061`):**
   ```lean
   -- Lean/Meta/WHNF.lean:1055-1061
   @[inline] private def useWHNFCache (e : Expr) : MetaM Bool := do
     -- We cache only closed terms without expr metavars.
     if e.hasFVar || e.hasExprMVar || (← read).customCanUnfoldPredicate?.isSome then
       return false
     else
       return true
   ```
   Because `acc` contains the theorem parameter `env0`, `e.hasFVar` is `true` at every step, so `Meta.whnf` never caches the WHNF of `acc`.
2. **Unforced `@ite` duplicates the unreduced `@Nat.rec` term `acc` at every step:**
   Consider the lazy step body:
   ```lean
   if (match acc with | some s => s.wm == idx | none => false) = true then
     match acc with | some s => some ⟨s.wm + 1, s.env⟩ | none => none
   else none
   ```
   Here the outer eliminator is `@ite`, whose major premise is the `Decidable` instance for `(match acc with ...) = true`. Reducing `@ite` to WHNF first reduces `acc` inside the condition to verify `s.wm == idx`, and then discards that work to return the unreduced `then`-branch `match acc with | some s => some ⟨s.wm + 1, s.env⟩ | none => none`, which still contains the **unreduced** `@Nat.rec ... idx` term `acc`. At step $k + 1$, reducing `acc_{k+1}` forces `acc_k` twice: once in the condition and once in the `then`-branch. Across $N$ steps, `Meta.whnf` unfolds `BEq.beq` exactly $2(2^N - 1)$ times and `Option.rec` $4(2^N - 1) + 2$ times.
3. **Why spine-strict `match acc with | none => none | some s => ...` restores $O(N)$ reduction:**
   When `match acc with` is placed **outside** the `ite`:
   ```lean
   match acc with
   | none => none
   | some s => if (s.wm == idx) = true then some ⟨s.wm + 1, s.env⟩ else none
   ```
   the outer eliminator is `Option.casesOn acc ...`, whose major premise is `acc` itself (`@Nat.rec ... idx`). Reducing `Option.casesOn` to WHNF reduces `acc` **once** to `Option.some ⟨w, env0⟩` and binds `s := ⟨w, env0⟩`—a constructor term from which `@Nat.rec` has already been eliminated. Both the `ite` condition (`s.wm == idx`) and the `then`-branch (`some ⟨s.wm + 1, s.env⟩`) now reference `s` rather than `acc`, reducing `BEq.beq` unfoldings from $2(2^N - 1)$ to **$2N$** and `Option.rec` unfoldings from $4(2^N - 1) + 2$ to **$2N + 2$**.

#### Empirical Benchmark 2A: Lazy `ite` ($O(2^N)$) vs. Spine-Strict `match` ($O(N)$) with Symbolic State `(env0 : Nat → Nat)`

| $N$ (steps) | Lazy `ite` Status | Lazy `ite` Time (`ms`) | Lazy `Option.rec` Unfoldings ($4(2^N-1)+2$) | Lazy `BEq.beq` Unfoldings ($2(2^N-1)$) | Lazy `Nat.rec` Unfoldings | Strict `match` Status | Strict `match` Time (`ms`) | Strict `Option.rec` Unfoldings ($2N+2$) | Strict `BEq.beq` Unfoldings ($2N$) | Strict `Nat.rec` Unfoldings |
| ---: | :--- | ---: | ---: | ---: | ---: | :--- | ---: | ---: | ---: | ---: |
| 6 | `ok` | 125.5 | 254 | 126 | 962 | `ok` | 90.0 | 14 | 12 | 158 |
| 8 | `ok` | 208.8 | 1,022 | 510 | 4,018 | `ok` | 94.5 | 18 | 16 | 274 |
| 10 | `ok` | 556.8 | 4,094 | 2,046 | 16,290 | `ok` | 97.0 | 22 | 20 | 422 |
| 12 | `ok` | 1,944.6 | 16,382 | 8,190 | 65,426 | `ok` | 99.9 | 26 | 24 | 602 |
| 14 | `ok` | 7,609.5 | 65,534 | 32,766 | 262,018 | `ok` | 107.5 | 30 | 28 | 814 |
| 15 | `ok` | 15,946.3 | 131,070 | 65,534 | 524,154 | `ok` | 110.1 | 32 | 30 | 932 |
| 16 | **`maxHeartbeats`** | **16,501.9** | **134,938+** | **67,471+** | **539,692+** | `ok` | **112.7** | **34** | **32** | **1,058** |

#### Empirical Benchmark 2B: Monolithic Spine-Strict `@Nat.rec` vs. Compositional Per-Block `List.foldr` (`checkMultiBlockPipeline_cons`)

Even with spine-strict `Option` matching, a single monolithic `@Nat.rec` fold pushes 3 recursive WHNF frames per step and reaches `maxRecDepth = 512` at $N = 172$ steps (`Nat.rec ↦ 249` at failure for $N = 256$). Decomposing a multi-block function into per-block `rfl` lemmas (64 instructions per block) combined via `checkMultiBlockPipeline_cons` (`List.foldr`) bounds the maximum WHNF recursion depth by the block size rather than total function length:

| Total Instructions ($N$) | Monolithic `@Nat.rec` Status | Monolithic Time (`ms`) | Compositional `List.foldr` Blocks ($B \times 64$) | Compositional `List.foldr` Status | Compositional Time (`ms`) |
| ---: | :--- | ---: | :--- | :--- | ---: |
| 64 | `ok` | 89.0 | $1 \times 64$ | `ok` | 91.8 |
| 128 | `ok` | 100.6 | $2 \times 64$ | `ok` | 90.2 |
| 171 | `ok` (threshold max) | 114.4 | — | — | — |
| 256 | **`maxRecDepth`** | 83.8 | $4 \times 64$ | `ok` | 90.7 |
| 512 | **`maxRecDepth`** | 83.5 | $8 \times 64$ | `ok` | 91.5 |
| 1024 | **`maxRecDepth`** | 82.9 | $16 \times 64$ | `ok` | 93.4 |

---

### Finding 6: `anneal-audit` Preflight & `Init.Prelude` Identifier/Syntax Traps

`Basis: source + execution`

Five additional preflight and library boundaries govern `prelude` + `Init.NotationExtra` modules audited by `trusted/audit/TrustedBoundary.lean`:

| Trap | Failure Diagnostic in Lean `v4.34.1` / `anneal-audit` | Root Cause | Verified `prelude`-Compatible Replacement |
| :--- | :--- | :--- | :--- |
| **`section` structure field name** | `<probe>.lean:8:10: error: unexpected token ':'; expected command` (and `policy:command parser error` in `TrustedBoundary.lean:1004-1019`) | `section` is a reserved command keyword in Lean 4's grammar (`Lean.Parser.Command.section`). | Rename the structure field to `secKind : Rv64SectionKind` (`Trusted/Rv64Ast.lean:395`). |
| **`deriving DecidableEq, BEq`** | `policy:deriving clauses are unsupported` (`TrustedBoundary.lean:644-649`) | `scanPolicyText` explicitly forbids `deriving` clauses in audited source files so all synthesized instances remain explicit. | Define an explicit `Type.beq` function and `instance : BEq Type` (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean:340-350`). |
| **`.eq_of_beq_eq_true` / `eq_of_decide` lemma names** | `declaration name '<name>' uses reserved suffix/prefix` (`TrustedBoundary.lean:511-535`) | `validateUserDeclIdent` reserves `eq_1`..`eq_N`, `eq_def`, `eq_unfold`, and any final name component starting with `eq_` (`last.startsWith "eq_"`) to prevent user theorems from shadowing kernel/equation-compiler projections. | Name equality reflection lemmas `.of_beq_eq_true` or `nat_eq_of_beq_eq_true` (`last` starts with `of_` or `nat_`, not `eq_`). |
| **`if a <= b` condition type** | `tactic 'rewrite' failed` when rewriting `Nat.ble a b = true` | In `Init/Prelude.lean:1770-1778`, `a <= b` is the `Prop` `LE.le a b` (`Nat.le`) decided by `Nat.decLe`, not `Bool` `Nat.ble`. | Split with `if h : a <= b then ... else ...` (`Decidable.byCases`) and simplify with `simp [h]` (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean:360-369`). |
| **`Nat.lxor` and `rcases` / `omega`** | `error(lean.unknownIdentifier): Unknown constant 'Nat.lxor'` | `Nat.lxor` was renamed to `Nat.xor` in `Init/Data/Nat/Bitwise/Basic.lean:38` (imported via `Init.NotationExtra`). `rcases` (`Init.RCases`) and `omega` (`Init.Omega`) are outside `prelude` + `Init.NotationExtra`. | Use `Nat.xor` (`Trusted/Rv64Semantics.lean`) and destruct inductive hypotheses with `cases` / `match` (`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean:371-375`). |

---

### Finding 7: Upstream `bv_decide` Native Axiom Injection, the Seven Kernel-Reduction Blockers in `verifyBVExpr`, and `bv_decide_kernel`

`Basis: source + execution + derived`

#### 7.1 How `bv_decide` Injects Per-Theorem `_native` Axioms in Lean `v4.30.0-rc2` and `v4.34.1`

In Lean `v4.30.0-rc2` and `v4.34.1`, the legacy `Lean.ofReduceBool` theorem and `Lean.trustCompiler` axiom (`src/lean/Init/Core.lean:2337–2409`) are marked `@[deprecated]`. Instead, `bv_decide` splits its proof pipeline into two stages:

1. **Kernel-Checked Preprocessing and Reification (`Normalize.bvNormalize` and `Reflect.reflectBV`):**
   - `Lean/Elab/Tactic/BVDecide.lean:51–63` (`bvNormalize`) applies `false_or_by_contra` and normalizes `BitVec`, `UInt8`..`UInt64`, `USize`, `Int8`..`Int64`, `ISize`, and `Bool` hypotheses using kernel-checked `bv_normalize` and `seval` `simp` theorems.
   - `Lean/Meta/Tactic/BVDecide/Reflect/SatAtBVLogical.lean:32–80` (`Reflect.reflectBV` and `SatAtBVLogical.proveFalse`) reifies the normalized hypotheses into a single syntactic expression `bvExpr : Std.Tactic.BVDecide.BVLogicalExpr` (`src/lean/Std/Tactic/BVDecide/Bitblast/BVExpr/Basic.lean:166–224`) paired with a kernel proof term `exprSat : bvExpr.SatAssignment atomsAssignment`. `SatAtBVLogical.proveFalse` constructs a closure `proveFalse (unsat : Expr) : MetaM Expr` that takes any proof term `unsat : bvExpr.Unsat` and applies it to `atomsAssignment` and `exprSat` to produce a kernel-checked proof of `False` using only `{propext, Classical.choice, Quot.sound}`.
2. **Native Evaluation and Axiom Injection (`LratCert.toReflectionProof`):**
   - `Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26–44` (`LratCert.toReflectionProof`) defines two auxiliary declarations—one for the reflected `BVLogicalExpr` and one for the raw LRAT certificate string (`LratCert`)—and invokes `Lean.Meta.nativeEqTrue \`bv_decide` (`src/lean/Lean/Meta/Native.lean:37–87`) on the proposition:
     ```lean
     Std.Tactic.BVDecide.Reflect.verifyBVExpr <exprDef> (loadLRATProof <certDef>) = true
     ```
   - `Lean.Meta.nativeEqTrue` (`src/lean/Lean/Meta/Native.lean:64–86`) compiles an auxiliary boolean thunk, evaluates it in native machine code via `unsafe evalConst Bool auxDeclName`, and calls `addDecl (.axiomDecl ...)` to inject a fresh per-theorem axiom named `<declName>._native.bv_decide.ax_1_5` into the kernel environment.
   - Applying `Std.Tactic.BVDecide.Reflect.verifyBVExpr_bv_unsat` (`src/lean/Std/Tactic/BVDecide/Reflect.lean:87–95`) to that native axiom yields `bvExpr.Unsat`.

As verified in Section 1 of [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean) (lines 31–62), every theorem proved by standard `bv_decide` depends on a theorem-specific `_native.bv_decide.ax_1_5` axiom (for example, `align_mask_bv64._native.bv_decide.ax_1_5`). In Anneal's audit pipeline (`trusted/audit/TrustedBoundary.lean`), any such theorem is rejected at Phase 1 if `native_decide` or `decide +native` syntax appears (lines 318–329) and at Phase 2 (`verifyAndCollectLocals`, lines 857–858, and `closure` axiom allowlist check against `{Classical.choice, Quot.sound, propext}`, lines 568–570) because the generated `.olean` contains an unauthorized axiom declaration and depends on it in its transitive constant closure.

#### 7.2 The Seven Kernel-Reduction Blockers in Upstream `verifyBVExpr`

If `Lean.Meta.nativeEqTrue` in `LratCert.toReflectionProof` is replaced by `mkEqRefl (toExpr true)` (or `eagerReduce (Eq.refl true)`), the Lean 4 kernel attempts to reduce `verifyBVExpr bv (loadLRATProof cert)` via weak-head normal form (`whnf`) and fails. Direct source inspection of `verifyBVExpr` (`src/lean/Std/Tactic/BVDecide/Reflect.lean:60–65`) and `#guard_msgs` execution in [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean) (lines 29–139) identify seven independent kernel-reduction blockers:

| # | Upstream Symbol and Source Coordinates (`leanprover/lean4` at `5045d00564`) | Reduction Blocker Mechanism | Diagnostic Witness in `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean` |
| :--- | :--- | :--- | :--- |
| 1 | `LRAT.parseLRATProof`, `LRAT.Parser.parseActions` (`src/lean/Std/Tactic/BVDecide/LRAT/Parser.lean:132, 201, 213, 279, 301`) & `String.toUTF8` (`src/lean/Init/Data/String/Bootstrap.lean:51`) | `Text.parseActions`, `Binary.parseLit`, `manyTillZero`, and `manyTillNegOrZero` are declared as `partial def`, which compile to `opaque` constants in the kernel with no equational reduction rules; `String.toUTF8` is `@[extern "lean_string_to_utf8"] opaque`. | `blocker1_lrat_parser_cannot_reduce_in_kernel` (lines 48–52) |
| 2 | `Std.DHashMap.Internal.mkIdx` (`src/lean/Std/Data/DHashMap/Internal/Index.lean:51–53`), `USize` (`src/lean/Init/Prelude.lean:2305`), & `mixHash` (`src/lean/Init/Prelude.lean:4680`) | `mkIdx` is marked `@[irreducible] def` and computes bucket indices via `USize.ofNat (hash a).toNat`, which depends on `opaque System.Platform.getNumBits : Unit → Nat` and `opaque mixHash : UInt64 → UInt64 → UInt64`. Even `(∅ : Std.HashMap Nat Nat)[0]?` cannot reduce in the kernel. | `blocker2_hashmap_empty_lookup_blocks_rfl` (lines 68–71) vs. `treeMap_empty_lookup_reduces_in_kernel` (lines 58–60) |
| 3 | `BVExpr.bitblast.go` (`src/lean/Std/Tactic/BVDecide/Bitblast/BVExpr/Circuit/Impl/Expr.lean:47–48, 87, 118`) | Threads a `BVExpr.Cache` backed by `Std.DHashMap` keyed by `BVExprWithHash` (whose hash invokes `opaque mixHash`), halting reduction on the first `BVExpr` cache lookup. | `blocker3_and_4_bitblast_aig_cache_blocks_rfl` (lines 85–88) |
| 4 | `Std.Sat.AIG.Cache` (`src/lean/Std/Sat/AIG/Basic.lean:139–159, 241–246`) | `Cache.empty`, `Cache.noUpdate`, `Cache.insert`, and `Cache.get?` are marked `@[irreducible]` and wrap `Std.HashMap (Decl α) (Nat × ...)`. Every smart gate constructor (`mkGateCached`, `mkAtomCached`, `mkConstCached`) probes `Cache.get?`. (Only `.const false` avoids probing the map because it returns index 0 immediately: `constFalse_aig_size_reduces`, lines 35–37.) | `blocker3_and_4_bitblast_aig_cache_blocks_rfl` (lines 85–88) |
| 5 | `Std.Sat.AIG.denote.go` (`src/lean/Std/Sat/AIG/Basic.lean:480–491`) | Defined by well-founded recursion with the explicit source comment `termination_by (x, 0) -- Don't allow reduction, we have large concrete gate entries`, blocking definitional unfolding of `⟦aig, assign⟧`. | `blocker5_aig_denote_wf_blocks_rfl` (lines 99–102) |
| 6 | `AIG.Entrypoint.relabelNat` (`src/lean/Std/Sat/AIG/RelabelNat.lean:162–179`) & `CNF.relabelFin` (`src/lean/Std/Sat/CNF/RelabelFin.lean:115`) | `relabelNat` inserts atoms into `Std.HashMap α Nat` (blocking reduction even on `constFalseExpr.bitblast.relabelNat`); `CNF.relabelFin` branches on an `@[no_expose] instance : Decidable (∃ v, VarMem v f)`. | `blocker6_relabelNat_blocks_rfl` (lines 114–117) |
| 7 | `LRAT.Internal.DefaultClause.ofArray.folder` (`src/lean/Std/Tactic/BVDecide/LRAT/Internal/Clause.lean:141–168`) | Marked `@[irreducible]` and folds over clause literals using `Std.HashMap (PosFin n) Bool` to deduplicate literals and detect tautologies during `LRAT.check`. | `blocker7_defaultClause_ofArray_blocks_rfl` (lines 129–134) |

#### 7.3 Verified Zero-`_native`-Axiom Replacements: `KernelLRAT` and `KernelBVDecide` (`bv_decide_kernel`)

Because `Normalize.bvNormalize` and `Reflect.reflectBV` already reduce goal obligations to proving `bvExpr.Unsat` (`∀ assign, bvExpr.eval assign = false`) purely within the kernel, eliminating `bv_decide`'s native axiom requires only a total, `Std.HashMap`-free, `@[irreducible]`-free boolean decision procedure that reduces in the kernel (`decide +kernel` or `eagerReduce (Eq.refl true)`) and has a mechanized soundness theorem concluding `.Unsat`:

1. **`KernelLRAT`: Total List-Based RUP Certificate Checker (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean:78–296`):**
   - `isFalsified`, `reduceClause`, `getClause`, `rupPropagate`, `negateClause`, `checkRupStep`, and `checkCert` (lines 105–235) are defined by structural recursion on `List` and `Nat` without `Std.HashMap`, `USize`, `partial def`, or `@[irreducible]` barriers.
   - `KernelLRAT.checkCert_sound` (lines 246–273) proves `checkCert F cert = true → F.Unsat` by induction on `cert`.
   - `KernelLRAT.sampleCNF_unsat` (lines 291–294) proves unsatisfiability of a 6-clause 2-bit adder carry-out formula via `checkCert_sound sampleUnsatCNF sampleLRATCert (by decide +kernel)` in **6.21 ms** with axiom footprint `[propext, Quot.sound]`.
2. **`KernelBVDecide`: Linear-Size Propagate-Generate ROBDD Bitblaster (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean:307–1006`):**
   Making 64-bit `BitVec` and `UInt64` arithmetic reduce quickly inside Lean 4's kernel `whnf` reducer without a `Std.HashMap` DAG cache uses three algorithmic choices:
   - **Nested structural recursion (`BDD.rec`) instead of well-founded recursion:** Binary BDD operations (`bddAnd`, `bddOr`, `bddXor` at lines 332–382) are factored into an outer structural recursion on `a : BDD` and a higher-order inner helper (`bddAndNode`, `bddOrNode`, `bddXorNode`) that recurses structurally on `b : BDD` while receiving curried recursive closures (`bddAnd la`, `bddAnd ha`), reducing directly via `BDD.rec` with zero `WellFounded.fix` overhead.
   - **Interleaved LSB-to-MSB variable ordering (`BVar.gt`, lines 311–318):** Decision variables `BVar := { bit : Nat, var : Nat }` are ordered first by bit position `bit` (0 up to $w - 1$) and then by variable index `var`.
   - **Propagate-generate basis `(x_i, x_i ^^ y_i)` for ripple-carry addition (`bddVar` and `assignToBDDEnv`, lines 388–394, 540–558):** Encoding variable 1's $i$-th bit in `bddVar` as `x_i ^^ p_i` (where `p_i` is `var_0[i] ^^ var_1[i]`) simplifies the ripple-carry sum bit to `p_i ^^ c_i` and the carry-out to $\text{carry}_{i+1} = \text{ite}(p_i,\, c_i,\, x_i)$. Because `c_i` appears in only the `high` branch of `p_i`, the uncached tree size of the carry ROBDD at bit $w$ is **strictly linear** ($2w + 1$, or **131 nodes** at bit 64) without any hash table.
3. **`module` + `public meta import` Memory Isolation Under `-M1024`:**
   In Lean `v4.34.1`, writing an unadorned `import Lean.Elab.Tactic.BVDecide` in a file without the `module` header loads the entire `Lean.*` compiler and elaborator `.olean` graph into the non-meta kernel environment (~950 MB of resident heap), causing `-M1024` to fail with `(kernel) excessive memory consumption detected` on the first theorem. Declaring `module` at the top of `ProbeBVDecide.lean` (lines 9–15) and using `public meta import Lean.Elab.Tactic.BVDecide` and `public meta import Lean.Meta.Tactic.Grind.Main` isolates the tactic elaborator to the `meta` phase, allowing all standard `bv_decide` and `bv_decide_kernel` 64-bit proofs to compile cleanly under `lean -j1 -M1024`.

#### 7.4 Empirical Comparison: Standard `bv_decide` vs. `bv_decide_kernel`

Measured on `leanprover/lean4:v4.34.1` (`-j1 -M1024 -Dprofiler=true`):

| Obligation in `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean` | Width | Standard `bv_decide` Axiom Footprint | `bv_decide_kernel` Axiom Footprint | `bv_decide_kernel` Kernel Time |
| :--- | :--- | :--- | :--- | :--- |
| `KernelLRAT.sampleCNF_unsat` | CNF (6 clauses) | N/A | `[propext, Quot.sound]` | **6.21 ms** |
| `checked_add_no_overflow_bv8_kernel` | 8-bit | `... + _native.bv_decide.ax_1_5` | `[propext, Classical.choice, Quot.sound]` | **114 ms** |
| `checked_add_no_overflow_bv16_kernel` | 16-bit | `... + _native.bv_decide.ax_1_5` | `[propext, Classical.choice, Quot.sound]` | **274 ms** |
| `checked_add_no_overflow_bv32_kernel` | 32-bit | `... + _native.bv_decide.ax_1_5` | `[propext, Classical.choice, Quot.sound]` | **616 ms** |
| `bitwise_and_le_mask_bv64_kernel` | 64-bit | `[propext, Classical.choice, Quot.sound, bitwise_and_le_mask_bv64._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **456 ms** |
| `align_mask_bv64_kernel` | 64-bit | `[propext, Classical.choice, Quot.sound, align_mask_bv64._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **642 ms** |
| `checked_add_no_overflow_bv64_kernel` | 64-bit | `[propext, Classical.choice, Quot.sound, checked_add_no_overflow_bv64._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **1.59 s** |
| `uint64_align_roundup_kernel` | 64-bit (`UInt64`) | `[propext, Classical.choice, Quot.sound, uint64_align_roundup._native.bv_decide.ax_1_5]` | `[propext, Classical.choice, Quot.sound]` | **3.02 s** |

---

### Finding 8: `omega` and `grind` Under `prelude` and `TrustedBoundary.lean`

`Basis: source + execution + derived`

#### 8.1 Proof-Term Construction and Axiom Footprints of `omega` and `grind`

1. **`omega` (`src/lean/Init/Omega.lean`, `src/lean/Lean/Elab/Tactic/Omega/Core.lean`, `Omega/Frontend.lean:672`):**
   `Init/Omega.lean:9–15` exports `Init.Omega.LinearCombo`, `Init.Omega.IntList`, `Init.Omega.Int`, `Init.Omega.Constraint`, and `Init.Omega.Logic`. During elaboration (`Lean/Elab/Tactic/Omega/Core.lean:107, 111, 224`), `omega` constructs explicit `Int`/`Nat` linear-combination witness terms and discharges bounded decidable side-conditions using `mkDecideProof` (kernel `decide`) and `mkEqReflWithExpectedType` (kernel `Eq.refl`). It never calls `Lean.Meta.nativeEqTrue` or `Lean.ofReduceBool`. Pure `Nat` linear bounds proofs (`mir_slice_subslice_bounds_omega` in `ProbeGrindOmega.lean:30–35` and `omega_bounds_check` in `DiagnoseReduce.lean:146–154`) depend only on `[propext, Quot.sound]`.
2. **`grind` (`src/lean/Init/Grind.lean`, `src/lean/Init/GrindInstances.lean`, `src/lean/Lean/Meta/Tactic/Grind/Main.lean:396`):**
   `Init/Grind.lean:9–31` exports 22 submodules (`Norm`, `Tactics`, `Lemmas`, `Cases`, `Propagator`, `Util`, `Offset`, `AC`, `ToInt`, `ToIntLemmas`, `Ring`, `Module`, `Ordered`, `Ext`, `Injective`, `Order`, `Config`, `Lint`, `Annotated`, `PP`, `Homo`, `FieldNormNum`), while `Init/GrindInstances.lean:9–12` exports the typeclass instances connecting `Int`, `Nat`, `Fin`, `BitVec`, `UInt8`..`UInt64`, `USize`, `SInt`, and `Rat` to `Grind.ToInt`, `Grind.CommRing`, and `Grind.NatModule`. `grind`'s arithmetic procedures (`cutsat` / `lia`, `ring`, `linarith`) construct explicit polynomial and Cooper/Cutsat certificate terms and discharge boolean reflection steps via `eagerReflBoolTrue` = `mkApp2 (mkConst ``eagerReduce [0]) (mkConst ``Bool) (mkConst ``Bool.true)` (`src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean:240–300`). Every theorem proved by `grind` in [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean) and [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean) depends only on `[propext, Classical.choice, Quot.sound]`.

#### 8.2 `prelude` Import Closures and the Private `Init.Data.Int.OfNat` Trap

Anneal's `trusted/lean/` and `theory/` modules compile with an explicit `prelude` header (`TrustedBoundary.lean:251–273`), and `trusted/lean/foundation-lock.json` locks **51** `Init.*` modules. Although `Init.Grind.Attr`, `Init.Grind.Interactive`, and `Init.Grind.Tactics` are present in that 51-module lock (transitively imported via `Init.Data.Nat.Div.Basic` → `Init.WFTactics` → `Init.WF` → `Init.Grind.Tactics`), they provide only syntax and attribute declarations.

In a `prelude` file, enabling `grind` over `Nat`, `Int`, and fixed-width machine integers (`UInt64`, `USize`, `BitVec`) requires four explicit imports (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean:9–13`):

```lean
prelude
import Init.Omega
import Init.Grind
import Init.GrindInstances
import Init.Data.Int.OfNat
```

- **Private Import of `Init.Data.Int.OfNat` Under Lean 4's `module` System:**
  The files in `src/lean/Init/Grind/*.lean` use Lean `v4.34.1`'s `module` header and import `Init.Data.Int.OfNat` as a private `import` rather than a `public import`. However, `grind`'s `Nat` Cutsat proof generator (`src/lean/Lean/Meta/Tactic/Grind/Arith/Cutsat/Nat.lean:9, 41`) constructs kernel proof terms that directly reference `Nat.ToInt.of_le` (defined in `src/lean/Init/Data/Int/OfNat.lean:388`). Without `import Init.Data.Int.OfNat` in a `prelude` file, `grind` fails on `Nat` linear arithmetic with `(kernel) unknown constant 'Nat.ToInt.of_le'`.
- **Separation of `Init.GrindInstances`:**
  `Init.Grind` defines the `Grind.ToInt` and `Grind.CommRing` classes, but the instances for `UInt64`, `USize`, `BitVec`, and `Int` live in `Init.GrindInstances` (`Init.GrindInstances.ToInt`, `Init.GrindInstances.Ring`, `Init.GrindInstances.Nat`).

| Tactic Capability in a `prelude` File | Minimal Explicit `import` Header | Transitive `Init.*` Closure | Modules Already in `foundation-lock.json` | Additional `Init.*` Modules Required |
| :--- | :--- | :--- | :--- | :--- |
| Current `foundation-lock.json` | (51 locked modules) | **51** | 51 | **0** |
| `omega` (`Nat` and `Int` linear integer arithmetic) | `import Init.Omega` | **76** | 51 | **25** (`Init.ByCases`, `Init.Classical`, `Init.Data.BEq`, `Init.Data.Bool`, `Init.Data.Int.DivMod.Basic`, `Init.Data.Int.DivMod.Bootstrap`, `Init.Data.Int.Lemmas`, `Init.Data.Int.Order`, `Init.Data.Nat.Dvd`, `Init.Data.Nat.Gcd`, `Init.Data.Nat.MinMax`, `Init.Data.Nat.Order`, `Init.Data.Order.Classes`, `Init.Data.Order.Factories`, `Init.Data.Order.Lemmas`, `Init.Data.ToString.Macro`, `Init.Omega`, `Init.Omega.Coeffs`, `Init.Omega.Constraint`, `Init.Omega.Int`, `Init.Omega.IntList`, `Init.Omega.LinearCombo`, `Init.Omega.Logic`, `Init.PropLemmas`, `Init.RCases`) |
| Minimal `grind` (`grind -lia -ring -linarith`: congruence closure + E-matching) | `import Init.Grind.Lemmas`<br>`import Init.Grind.Norm`<br>`import Init.Grind.Tactics` | **172** | 51 | **121** |
| Full `grind` + `omega` (`lia`, `ring`, `linarith`, `ToInt` over `Nat`, `Int`, `UInt64`, `USize`, `BitVec`) | `import Init.Omega`<br>`import Init.Grind`<br>`import Init.GrindInstances`<br>`import Init.Data.Int.OfNat` | **247** | 51 | **196** |

#### 8.3 Duplicate Realized `.eq_def` Constants Across `Init.*` vs. `TrustedBoundary.lean:851`

All six theorems in [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean) pass `TrustedBoundary.lean` Phase 1 (`preflight`) with `"ok": true` and pass `baseEnv.toKernelEnv.replay` across all 12 compiled declarations. However, when `foundation-lock.json` is expanded to either the 76-module `Init.Omega` closure or the 247-module `Init.Grind` closure, `TrustedBoundary.verifyAndCollectLocals` (`trusted/audit/TrustedBoundary.lean:850–852`) fails at Phase 2 (`audit`) with:

```json
{"ok": false, "message": "policy:stored declaration differs from inventory List.drop.eq_def", "category": "policy"}
```

Across the 247 `Init.*` modules in `Init.Grind`'s transitive closure, five equation theorems are realized independently on demand (`realizeConst`) in more than one `Init.*` module:
1. `List.drop.eq_def`: realized in both `Init.Data.Array.GetLit` (in the 51-module `foundation-lock.json`) and `Init.Data.List.TakeDrop` (imported by `Init.Omega` and `Init.Grind`).
2. `List.takeWhile.eq_def`: realized in `Init.Data.List.TakeDrop` and `Init.Data.List.Impl`.
3. `List.take.eq_def`: realized in `Init.Data.List.TakeDrop` and `Init.Data.List.Impl`.
4. `List.eraseIdx.eq_def`: realized in `Init.Data.List.Impl`, `Init.Data.List.Erase`, and `Init.Data.List.Nat.Basic`.
5. `List.find?.eq_def`: realized in `Init.Data.List.Impl` and `Init.Data.List.ToArray`.

For all six duplicate occurrences across those five constants, `stored.type == ci.type` holds (`true`), but `stored.value? true == ci.value? true` is `false` because `env.checked` retains only one module's realized proof term. Scoping the value-equality check at `TrustedBoundary.lean:851` to `(!foundation.contains m.module || orig == m.module)` while preserving `stored.type == ci.type` for every module resolves the collision.

---

### Finding 9: `Std.Do` (`SPred`, `WP`, `Triple`, `mvcgen`) and `Std.Data` Containers

`Basis: source + execution + derived`

#### 9.1 Architecture and Audit Integration of `Std.Do` and `mvcgen`

`Std.Do` (`src/lean/Std/Do.lean`) and `Std.Tactic.Do` (`src/lean/Std/Tactic/Do.lean`) implement a foundational weakest-precondition program logic for monadic Lean programs in four layers:
1. **State-Indexed Predicates (`SVal` and `SPred`):** `abbrev SVal (σs : List (Type u)) (α : Type u) : Type u` (`src/lean/Std/Do/SPred/SVal.lean:30–32`) and `abbrev SPred (σs : List (Type u)) : Type u := SVal σs (ULift Prop)` (`src/lean/Std/Do/SPred/SPred.lean:34`) with entailment `P ⊢ₛ Q` (`SPred.entails`, lines 67–69).
2. **Effect Shapes and Multi-Barrel Postconditions (`PostShape` and `PostCond`):** `inductive PostShape : Type (u + 1)` (`src/lean/Std/Do/PostCond.lean:54–66`), `abbrev Assertion (ps : PostShape.{u}) : Type u := SPred (PostShape.args ps)` (lines 93–94), and `def PostCond (α : Type u) (ps : PostShape.{u}) : Type u := (α → Assertion ps) × ExceptConds ps` (line 255).
3. **Conjunctive Predicate Transformers and `WP` Instances (`PredTrans`, `WP`, `WPMonad`):** `structure PredTrans (ps : PostShape) (α : Type u)` (`src/lean/Std/Do/PredTrans.lean:63–70`), `class WP (m : Type u → Type v) (ps : outParam PostShape.{u})` (`src/lean/Std/Do/WP/Basic.lean:54–56`), and `class WPMonad` (`src/lean/Std/Do/WP/Monad.lean:36–41`) for `Id`, `StateT` / `StateM`, `ReaderT` / `ReaderM`, `ExceptT` / `Except`, `OptionT` / `Option`, and `EStateM`.
4. **Hoare Triples and Verification Condition Generation (`Triple` and `mvcgen`):** `def Triple [WP m ps] (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop := P ⊢ₛ wp⟦x⟧ Q` (`src/lean/Std/Do/Triple/Basic.lean:37–38`), discharged by `mvcgen` (`src/lean/Lean/Elab/Tactic/Do/VCGen.lean:40–150, 453–489`) and `mleave` (`src/lean/Std/Tactic/Do/Syntax.lean:177–221`).

Section 1 of [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean) (lines 44–109) verifies `tryBumpAlloc_spec`, `allocPair_spec`, and `checkedStep_spec`; all three depend only on `[propext, Classical.choice, Quot.sound]`. Admitting `mvcgen` under Anneal's audit boundary requires: (1) passing `-Dmvcgen.warning=false` because `VCGen.lean:455–456` logs an unconditional experimental warning unless `mvcgen.warning` is `false`, (2) adding `` `spec `` to `TrustedBoundary.allowedAttributeNames` (`TrustedBoundary.lean:201`), and (3) importing `Std.Do.Triple.Basic` + `Std.Do.WP.Monad` directly (**92** modules: 18 `Std.*` + 74 `Init.*`) rather than top-level `Std.Do` (**460** modules).

#### 9.2 `Std.Data` Three-Tier Container Matrix, Recursive Inductives, and Kernel Reduction

Lean `v4.34.1`'s `Std.Data` provides three tiers for both hash maps (`HashMap` / `DHashMap`) and size-balanced binary search trees (`TreeMap` / `DTreeMap`, with balance parameters $\delta = 3, \text{ratio} = 2$ at `src/lean/Std/Data/DTreeMap/Internal/Def.lean:36–41`):

| Tier | Tree-Based (`Ord` / `cmp`) | Hash-Based (`BEq` + `Hashable`) | Internal Representation & Well-Formedness | Nestable in Recursive Inductives? | Reduces in Kernel (`rfl` / `decide +kernel`)? | Extensional Equality (`m₁ = m₂ ↔ ∀ k, m₁[k]? = m₂[k]?`)? | Transitive Module Closure |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Unbundled (`.Raw`)** | `Std.TreeMap.Raw α β cmp` (`Std/Data/TreeMap/Raw/Basic.lean:65`) | `Std.HashMap.Raw α β` (`Std/Data/HashMap/Raw.lean:61`) | Pure inductive/struct data (`Impl α β` or `size × Array AssocList`); separate `Raw.WF` predicate; lookup lemmas take `(h : m.WF)`. | **Yes** (`GoodRecValue`, `ProbeStdDoData.lean:146–149`) | **`TreeMap.Raw`: Yes (`[]` axioms)**<br>`HashMap.Raw`: **No** | No (structural equality on tree/buckets) | `TreeMap.Raw.Basic`: **169** (11 `Std.*`)<br>`TreeMap.Raw` + `Lemmas`: **259** (44 `Std.*`)<br>`HashMap.Raw`: **168** (8 `Std.*`) |
| **Bundled** | `Std.TreeMap α β cmp` (`Std/Data/TreeMap/Basic.lean:67`) | `Std.HashMap α β` (`Std/Data/HashMap/Basic.lean:64`) | `{ inner : Raw, wf : inner.WF }`; lookup lemmas require no `WF` hypothesis. | **No** (`BadRecValue`, `ProbeStdDoData.lean:135–138`) | **`TreeMap`: Yes**<br>`HashMap`: **No** | No (`Equiv` relation `~m` instead of `=`) | `TreeMap` + `Lemmas`: **262** (47 `Std.*`) |
| **Extensional (`Ext*`)** | `Std.ExtTreeMap α β cmp` (`Std/Data/ExtTreeMap/Basic.lean:71`) | `Std.ExtHashMap α β` (`Std/Data/ExtHashMap/Basic.lean:61`) | `Quotient` of bundled map by `Equiv` (`~m`); requires `[TransCmp cmp]` or `[EquivBEq α] [LawfulHashable α]`. | **No** (wraps `Quotient` over bundled map) | **No** (`Quot.lift` blocks concrete `Repr`, though `@[simp, grind =]` proves symbolic lookups) | **Yes** (`@[ext] theorem ext`, proved with `ext k; grind`, `ProbeStdDoData.lean:174–177`) | `ExtTreeMap` + `Lemmas`: **268** (53 `Std.*`) |

When a bundled container appears inside a recursive inductive type (`BadRecValue` in `ProbeStdDoData.lean:135–138`), Lean's nested-inductive elaborator specializes `Std.DTreeMap.Internal.Impl Nat (fun _ => BadRecValue)` into `_nested.Std.DTreeMap.Internal.Impl_3`, whereas `Impl.WF` (`src/lean/Std/Data/DTreeMap/Internal/WF/Defs.lean:47–53`) cannot be specialized because its constructor `Impl.WF.constModify` places the value type family `β` in a negative position (`f : α → Option γ → Option γ`), causing `(kernel) application type mismatch: DTreeMap.Internal.Impl.WF inner`. Unbundling via `Std.TreeMap.Raw` or `Std.HashMap.Raw` (`GoodRecValue`, lines 146–149) passes kernel inductive translation cleanly. Moreover, `Std.TreeMap.Raw` reduces in the kernel with **zero axioms** (`treemap_raw_kernel_reduce`, lines 157–160) and discharges symbolic `WF` lookup obligations via `grind [Std.TreeMap.Raw.WF.insert]` (`treemap_raw_lookup_insert`, lines 169–172).

## Boundaries

1. **String-Literal vs. `String.ofList` RHS Limit (`N = 125` vs. `N = 2,048+`):**
   When the RHS of an equality theorem is a raw string literal `"..."`, `congrArg String.ofList rfl` avoids `inferDefEqAttr` (`smartUnfolding = false`) and avoids unfolding `String.ofList` on the LHS, but `ensureHasType` still checks `String.ofList ['9', ...] =?= "..."` with `smartUnfolding = true`. Under `maxRecDepth = 512`, that terminal `List.toByteArray.loop` check succeeds up to **$N = 125$ ASCII characters** and hits `maxRecDepth = 512` at $N = 126$ characters. For artifacts exceeding 125 characters (such as 521-byte / 1,042-character or 1,024-byte / 2,048-character ELF64 hex payloads), expressing the expected literal as `String.ofList` over chunked character lists ($\le 64$ characters per chunk) keeps both sides in `String.ofList` form so `congrArg String.ofList rfl` never enters `List.toByteArray.loop`.
2. **Closed-Term vs. Free-Variable WHNF Caching in Finding 5:**
   When an `Option` accumulator `acc` is a **closed** ground term (`e.hasFVar == false` and `e.hasExprMVar == false`), `useWHNFCache` (`Lean/Meta/WHNF.lean:1058`) returns `true` and memoizes the WHNF of `acc` across both branches of an unforced `ite`. The $O(2^N)$ elaborator blowup in Finding 5 specifically manifests when `acc` contains at least one free variable (`e.hasFVar == true`, such as a universally quantified initial state or environment parameter `(env0 : Nat → Nat)`) or expression metavariable. Spine-strict pattern matching (`match acc with | none => none | some s => ...`) guarantees $O(N)$ WHNF reduction regardless of whether `acc` is closed or open.
3. **Un-chunked `List.foldr` Spine Limit (`L <= 505`):**
   Because `List.foldr` (`Init/Data/List/Basic.lean:1058`) is not tail-recursive, reducing a single flat `List.foldr` over a list of length $L \ge 506$ exceeds `maxRecDepth = 512`. Large lists reduced in the kernel must be structured as two-level chunked lists (e.g., $32 \times 32 = 1,024$ elements) or proved compositionally via `checkMultiBlockPipeline_cons`.
4. **Non-Linear Bitvector Operations in `KernelBVDecide` (`unsupported` in current ROBDD prototype):**
   `KernelBVDecide.blastExpr` (`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean:643–678`) implements `.var`, `.const`, `.extract`, `.append`, `.un .not`, `.bin .and`, `.bin .or`, `.bin .xor`, `.bin .add`, `.bin .eq`, and `.bin .ult`. General 64-bit multiplication (`mul`), unsigned division/remainder (`udiv`, `umod`), and variable shifts (`shl`, `ushr`, `sshr`) are `unsupported` in `blastExpr` because ROBDD representations of 64-bit multipliers grow exponentially in the bit width; supporting them without `_native` axioms requires pairing a `Std.HashMap`-free AIG-to-CNF bitblaster with `KernelLRAT.checkCert_sound` (`ProbeBVDecide.lean:246–273`).
5. **Propagate-Generate Basis Scope (`known not to apply` to $\ge 3$ independent addends):**
   The `bddVar` propagate-generate transformation (`ProbeBVDecide.lean:388–394`) applies specifically to variable 1 relative to variable 0 (`x_i ^^ p_i`), giving exact $2w + 1$ tree size for two-variable 64-bit additions (`x + y`) and one-variable constant additions (`x + c`). It is `known not to apply` to obligations summing three or more independent 64-bit variables without an intermediate DAG cache or LRAT certificate.
6. **`Std.*` Namespace Policy in `TrustedBoundary.lean` (`unsupported` without policy change; multi-thread `Std.Do` concurrency `not examined`):**
   `trusted/audit/TrustedBoundary.lean:34, 488` currently restricts `foundation-lock.json` modules to the `Init.` prefix; admitting `Std.Do` or `Std.Data.TreeMap` directly into `trusted/lean/` is `unsupported` without updating `TrustedBoundary.lean`. Multi-thread concurrent program verification in `Std.Do` was `not examined` (and whether future Lean releases move `isDefEqStringLit` ahead of `isDefEqDelta` in `Lean/Meta/ExprDefEq.lean` remains `unknown`).

## Evidence

### 1. Primary Upstream and Repository Sources

All primary source coordinates were inspected across `leanprover/lean4` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` for `v4.30.0-rc2` and `5045d0056413266e57c625dcd7c365b10e377c52` for `v4.34.1`) and hashed in [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/source-manifest.json`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/source-manifest.json):

1. **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
   - `src/lean/Init/Prelude.lean:1069-1070` (`instBEqOfDecidableEq`), `1770-1778` (`LE Nat` / `Nat.decLe`), `2305` (`USize`), `2885-2888` (`List.foldl`), `3525-3561` (`ByteArray.IsValidUTF8`, `String.ofByteArray`, `String.ofList`, `List.toByteArray.loop`), `4680` (`mixHash`).
   - `src/lean/Init/Core.lean:2337–2409` (deprecation of `Lean.ofReduceBool` and `Lean.trustCompiler`; definition of `eagerReduce`).
   - `src/lean/Init/Data/String/Defs.lean:6, 68-80` (`module` header and unexposed `@[extern "lean_string_to_utf8"] def String.toUTF8`).
   - `src/lean/Init/Data/Nat/Basic.lean:22-29` (`Nat.recCompiled` and `@[csimp] theorem Nat.rec_eq_recCompiled`).
   - `src/lean/Init/Data/Nat/Bitwise/Basic.lean:38` (`Nat.xor`).
   - `src/lean/Lean/Meta/ExprDefEq.lean:129-165` (`isDefEqEtaStruct`), `1498-1524` (`tryHeuristic`), `1685-1697` (`isDefEqStringLit`), `2205-2233` (`isExprDefEqExpensive` step ordering).
   - `src/lean/Lean/DefEqAttrib.lean:33-35` (`isDefEqCareful` setting `smartUnfolding := false`), `121-188` (`isRflProofCore` and `inferDefEqAttr`).
   - `src/lean/Lean/Meta/WHNF.lean:23-29` (`Expr.toCtorIfLit`), `853-918` (`unfoldDefinitionCore?`), `1055-1061` (`useWHNFCache`).
   - `src/lean/Lean/Compiler/LCNF/ToImpure.lean:180-185` (`List.rec` codegen rejection).
   - `src/lean/Lean/Elab/PreDefinition/Basic.lean:134-135` (`shouldGenCodeFor`), `280-295` (`addAndCompilePartialRec` emitting `._unsafe_rec`).
   - `src/lean/Lean/Elab/PreDefinition/Structural/Main.lean:183-218` (structural recursion compiler calling `addAndCompilePartialRec`).
   - `src/lean/Lean/Meta/Native.lean:37–87` (`Lean.Meta.nativeEqTrue` and per-theorem `_native.<tactic>.ax_*` axiom injection).
   - `src/lean/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:26–44` (`LratCert.toReflectionProof` calling `Lean.Meta.nativeEqTrue \`bv_decide`) and `Reflect/SatAtBVLogical.lean:32–80` (`Reflect.reflectBV` and `SatAtBVLogical.proveFalse`).
   - `src/lean/Std/Tactic/BVDecide/Reflect.lean:60–95`, `LRAT/Parser.lean:132, 201, 213, 279, 301`, `LRAT/Internal/Clause.lean:141–168`, `Bitblast/BVExpr/Circuit/Impl/Expr.lean:47–118`, `Std/Sat/AIG/Basic.lean:139–159, 241–246, 480–491`, `Std/Sat/AIG/RelabelNat.lean:162–179`, and `Std/Data/DHashMap/Internal/Index.lean:51–53`.
   - `src/lean/Lean/Elab/Tactic/Omega/Core.lean:107, 111, 224`, `Omega/Frontend.lean:672`, `Lean/Meta/Tactic/Grind/Main.lean:396`, `Grind/Arith/Cutsat/Proof.lean:240–300`, and `Grind/Arith/Cutsat/Nat.lean:9, 41`.
   - `src/lean/Std/Do/SPred/SVal.lean:30–32`, `SPred.lean:34, 67–69`, `PostCond.lean:54–110, 255`, `PredTrans.lean:63–89`, `WP/Basic.lean:54–112`, `WP/Monad.lean:36–106`, `Triple/Basic.lean:37–38`, and `Lean/Elab/Tactic/Do/VCGen.lean:40–150, 453–489`.
   - `src/lean/Std/Data/DTreeMap/Internal/WF/Defs.lean:47–53`, `TreeMap/Basic.lean:67`, `TreeMap/Raw/Basic.lean:65`, `ExtTreeMap/Basic.lean:71`, `HashMap/Basic.lean:64`, and `HashMap/Raw.lean:61`.
2. **`joshlf/anneal` (`beb778bb135474a67dc017c185d2753a60693d8c` and `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
   - `trusted/audit/TrustedBoundary.lean:201, 316, 318–329, 511-535, 568–570, 644-649, 845–858, 1004-1019, 1357-1358`.
   - `trusted/audit/src/lib.rs:1233` and `trusted/lean/foundation-lock.json:1–56`.
   - `trusted/lean/Trusted/Rv64Ast.lean:393-399`, `Trusted/Rv64Semantics.lean:947-949, 1012-1037`, `theory/Anneal/Compiler/MirToRv64Stage0.lean:1118-1212`, `theory/Anneal/Compiler/MirOptPasses.lean:122-146, 189-200`, and `theory/Anneal/Compiler/KancVerticalSlice.lean:271-345`.

### 2. Support Files and Preserved Mechanized Probes

- [`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean`](support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean) (`sha256: a692c4682372e307f80d90ab5dc374f545216a568c694ed4f548ef373d54ae54`): Self-contained `prelude` + `import Init.NotationExtra` module verified with Lean `v4.34.1` (`294.8 ms`, exit code `0`, zero `._unsafe_rec` constants).
- [`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/run_benchmarks.py`](support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/run_benchmarks.py) (`sha256: 4e70b4a6aff0eecd85ee304e6e07c078262a8661fd46de482aaed7f45519baad`) and [`support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/benchmark_results.json`](support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/benchmark_results.json) (`sha256: 6c5c9df5e3461fa3cfd34b6182f5719c15da1bf089e4c88df0753b9e358acac2`).

#### 2.1 [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean) (1,006 lines, SHA-256 `3d2465d2cf40724556c1f14bc7f9a3375d277148d8de3f23822930341053a6f8`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `StandardBVDecide.align_mask_bv64` | 34–36 | 64-bit alignment mask preservation via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, align_mask_bv64._native.bv_decide.ax_1_5]` |
| `StandardBVDecide.checked_add_no_overflow_bv64` | 41–43 | 64-bit unsigned addition overflow equivalence via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, checked_add_no_overflow_bv64._native.bv_decide.ax_1_5]` |
| `StandardBVDecide.bitwise_and_le_mask_bv64` | 48–50 | 64-bit bitwise AND upper bound via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, bitwise_and_le_mask_bv64._native.bv_decide.ax_1_5]` |
| `StandardBVDecide.uint64_align_roundup` | 55–59 | 64-bit `UInt64` alignment round-up via standard `bv_decide`. | `[propext, Classical.choice, Quot.sound, uint64_align_roundup._native.bv_decide.ax_1_5]` |
| `KernelLRAT.rupPropagate_sound` | 175–197 | Soundness of unit propagation over hint indices. | `[propext, Quot.sound]` |
| `KernelLRAT.checkCert_sound` | 246–273 | Soundness of total list-based LRAT/RUP certificate checker (`checkCert F cert = true → F.Unsat`). | `[propext, Quot.sound]` |
| `KernelLRAT.sampleCNF_unsat` | 291–292 | In-kernel LRAT certificate discharge via `decide +kernel` (6.21 ms). | `[propext, Quot.sound]` |
| `KernelBVDecide.eval_bddAnd`, `eval_bddOr`, `eval_bddXor` | 446–528 | Soundness of nested structurally recursive (`BDD.rec`) ROBDD gate operations. | `[propext, Quot.sound]` |
| `KernelBVDecide.eval_bddVar` | 547–562 | Soundness of the propagate-generate basis `(x_i, x_i ^^ y_i)` under `assignToBDDEnv`. | `[propext, Quot.sound]` |
| `KernelBVDecide.eval_carryLoop`, `eval_eqLoop` | 588–642 | Soundness of ripple-carry and bit-equality ROBDD loops against `BitVec.carry` and `==`. | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.eval_blastExpr`, `eval_blastPred`, `eval_blastLogical` | 680–901 | End-to-end soundness of `Std.HashMap`-free bitblasting over `BVExpr`, `BVPred`, and `BVLogicalExpr`. | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.unsat_of_checkBVLogicalUnsat` | 908–917 | Master reflection theorem: `checkBVLogicalUnsat expr = true → expr.Unsat`. | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.align_mask_bv64_kernel` | 964–966 | 64-bit alignment mask preservation proved in-kernel via `bv_decide_kernel` (642 ms). | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.checked_add_no_overflow_bv8/16/32/64_kernel` | 972–986 | 8-, 16-, 32-, and 64-bit unsigned addition overflow equivalence proved via `bv_decide_kernel` (1.59 s at 64-bit). | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.bitwise_and_le_mask_bv64_kernel` | 991–993 | 64-bit bitwise AND upper bound proved via `bv_decide_kernel` (456 ms). | `[propext, Classical.choice, Quot.sound]` |
| `KernelBVDecide.uint64_align_roundup_kernel` | 998–1002 | 64-bit `UInt64` alignment round-up proved via `bv_decide_kernel` (3.02 s). | `[propext, Classical.choice, Quot.sound]` |

#### 2.2 [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean) (69 lines, SHA-256 `abeb3548f70a9d683b791638c6b084c050e9e780ae99d4fcacf8ec0e72c4d114`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `test_grind_eq` | 26–27 | Congruence closure and E-matching under `prelude` via `grind`. | `[propext, Classical.choice, Quot.sound]` |
| `mir_slice_subslice_bounds_omega` | 30–35 | Subslice index bounds check under `prelude` via `omega`. | `[propext, Quot.sound]` |
| `mir_struct_field_layout_omega` | 39–47 | Struct field layout and padding offset check under `prelude` via `omega`. | `[propext, Classical.choice, Quot.sound]` |
| `mir_slice_subslice_bounds_grind` | 50–55 | Subslice index bounds check under `prelude` via `grind` (`lia`). | `[propext, Classical.choice, Quot.sound]` |
| `mir_uint64_checked_index_grind` | 59–64 | `UInt64` bounded offset addition under `prelude` via `grind` (`ToInt` + `lia`). | `[propext, Classical.choice, Quot.sound]` |
| `mir_stride_offset_ring_grind` | 67–69 | Stride offset distributivity over `Int` under `prelude` via `grind` (`ring`). | `[propext, Classical.choice, Quot.sound]` |

#### 2.3 [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean) (184 lines, SHA-256 `1cdc3c347bde6d4f2a091b7ed374085e60b4788324998cf33cc60782ffd5bf5d`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `ProbeStdDo.tryBumpAlloc_spec` | 66–72 | `@[spec]` Hoare triple for `StateM FrameState Bool` proved via `mvcgen [tryBumpAlloc] <;> grind`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdDo.allocPair_spec` | 85–89 | Compositional Hoare triple for sequential allocations proved via `mvcgen [allocPair] <;> omega`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdDo.checkedStep_spec` | 103–108 | Multi-barrel `EStateM String FrameState Nat` Hoare triple proved via `mvcgen [checkedStep] <;> omega`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdData.BadRecValue` | 135–138 | `#guard_msgs` proof that bundled `Std.TreeMap` fails kernel nested-inductive typechecking (`Impl.WF inner`). | N/A (`#guard_msgs` expected error) |
| `ProbeStdData.GoodRecValue` | 146–149 | Recursive inductive type nesting `Std.TreeMap.Raw` and `Std.HashMap.Raw`. | `[]` |
| `ProbeStdData.treemap_kernel_reduce` | 152–155 | In-kernel reduction (`decide +kernel`) on bundled `Std.TreeMap Nat Nat`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdData.treemap_raw_kernel_reduce` | 157–160 | Zero-axiom in-kernel reduction (`decide +kernel`) on `Std.TreeMap.Raw Nat Nat`. | `[]` (zero axioms) |
| `ProbeStdData.treemap_raw_lookup_insert` | 169–172 | Symbolic `Std.TreeMap.Raw` lookup proof discharging `WF` via `grind [Std.TreeMap.Raw.WF.insert]`. | `[propext, Classical.choice, Quot.sound]` |
| `ProbeStdData.exttreemap_ext_insert_comm` | 174–177 | Extensional equality (`m₁ = m₂`) on `Std.ExtTreeMap Nat Nat` proved via `ext k; grind`. | `[propext, Classical.choice, Quot.sound]` |

#### 2.4 [`support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean`](support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean) (178 lines, SHA-256 `ab8544539c4a5ed319edfbed888262376cbcb6445f01d8a1f2b9b54ae2f46c42`)

| Declaration | Lines | Role & Verified Property | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `DiagnoseReduce.constFalse_aig_size_reduces` | 35–37 | Baseline showing `BVLogicalExpr.const false` reduces in the kernel via `eagerReduce (Eq.refl 1)`. | `[]` (zero axioms) |
| `DiagnoseReduce.blocker1_lrat_parser_cannot_reduce_in_kernel` | 50–52 | `#guard_msgs` witness that `LRAT.parseLRATProof` / `String.toUTF8` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.treeMap_empty_lookup_reduces_in_kernel` | 58–60 | Baseline showing `(∅ : Std.TreeMap Nat Nat)[0]? = none` reduces via `decide +kernel`. | `[propext, Classical.choice, Quot.sound]` |
| `DiagnoseReduce.blocker2_hashmap_empty_lookup_blocks_rfl` | 68–71 | `#guard_msgs` witness that `(∅ : Std.HashMap Nat Nat)[0]?` blocks kernel `rfl` at `mkIdx`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker3_and_4_bitblast_aig_cache_blocks_rfl` | 85–88 | `#guard_msgs` witness that 1-bit `BVLogicalExpr.bitblast` blocks kernel `rfl` at `Std.DHashMap` / `AIG.Cache`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker5_aig_denote_wf_blocks_rfl` | 99–102 | `#guard_msgs` witness that well-founded `AIG.denote` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker6_relabelNat_blocks_rfl` | 114–117 | `#guard_msgs` witness that `AIG.Entrypoint.relabelNat` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.blocker7_defaultClause_ofArray_blocks_rfl` | 129–134 | `#guard_msgs` witness that `LRAT.Internal.DefaultClause.ofArray` blocks kernel `rfl`. | N/A (`#guard_msgs`) |
| `DiagnoseReduce.omega_bounds_check`, `grind_uint64_lia_check`, `grind_int_ring_check` | 140–176 | `#guard_msgs in #print axioms` verification of `omega` and `grind` axiom footprints. | `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]` |

## Revalidation

To revalidate all positive proofs, scaling tables, negative error reproductions, and core-tactic probes from the report package directory using Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):

```bash
# 1. Verify the self-contained prelude-only probe directly with Lean 4.34.1
lean support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/ProbePreludeTraps.lean

# 2. Re-run the full scaling benchmark and diagnostic suite
python3 support/lean-4-34-1-prelude-string-utf8-beq-and-recursor-traps/run_benchmarks.py

# 3. Verify the four standalone core-tactics, bv_decide_kernel, Std.Do, and Std.Data probes
lean -j1 -M1024 support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean
lean -j1 -M1024 support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean
lean -j1 -M1024 support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean
lean -j1 -M1024 support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean
```

What each probe discriminates on a newer Lean 4 toolchain:

1. Whether `Init/Data/String/Defs.lean` adds `@[expose]` to `String.toUTF8`, and whether `Lean/DefEqAttrib.lean` (`inferDefEqAttr`) continues to run `isDefEqCareful` with `smartUnfolding = false` on syntactic `:= rfl` theorems.
2. Whether `Lean/Compiler/LCNF/ToImpure.lean` adds `@[csimp]` or native support for `@List.rec`, and whether `shouldGenCodeFor` in `Lean/Elab/PreDefinition/Basic.lean` continues to emit `._unsafe_rec` for structural recursive `def`s.
3. `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/DiagnoseReduce.lean` fails if any of the seven upstream `verifyBVExpr` / `Std.HashMap` kernel-reduction blockers becomes reducible or if `omega` or `grind` changes its axiom footprint.
4. `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeBVDecide.lean` verifies that `KernelLRAT.checkCert_sound` and `KernelBVDecide.unsat_of_checkBVLogicalUnsat` (`bv_decide_kernel`) compile within `-M1024` and discharge 64-bit `BitVec` and `UInt64` obligations using only `[propext, Classical.choice, Quot.sound]`.
5. `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeGrindOmega.lean` and `support/lean4-core-tactics-kernel-bvdecide-stddo-and-containers/ProbeStdDoData.lean` verify `prelude` + `Init.Omega` + `Init.Grind` + `Init.GrindInstances` + `Init.Data.Int.OfNat`, `Std.Do` (`mvcgen` + `@[spec]`), `BadRecValue` nested-inductive rejection on bundled `Std.TreeMap`, and zero-axiom kernel reduction on `Std.TreeMap.Raw`.
