<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Lean 4.34.1 `prelude`-Only String/UTF-8 Kernel Reduction, `BEq` Partial Unfolding, and LCNF Recursor Compilation Traps

## Summary

Modules that verify compiler passes and machine-code artifacts in
`joshlf/anneal` (`beb778bb135474a67dc017c185d2753a60693d8c`) under Lean
`v4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`)
operate under two simultaneous constraints:

1. **Minimal `prelude` import closure:** Trusted semantic files
   (`Trusted/*.lean`) and `prelude`-only theory modules import only
   `Init.Prelude` and `Init.NotationExtra` (locked by
   `trusted/lean/foundation-lock.json`). Higher-level standard-library modules
   (`Init.Data.String.Basic`, `Init.WF`, `Init.Omega`, `Init.Classical`) are
   outside the import closure.
2. **Strict environment and source auditing (`anneal-audit`):**
   `trusted/audit/TrustedBoundary.lean` rejects `set_option` overrides (freezing
   `maxRecDepth = 512` and `maxHeartbeats = 200000`), rejects `deriving`
   clauses, rejects reserved theorem-name suffixes (`eq_*`), and rejects every
   declaration in the post-elaboration environment whose `ConstantInfo.isUnsafe`
   or `ConstantInfo.isPartial` flag is set—including compiler-synthesized
   auxiliary constants such as `<decl>._unsafe_rec`.

Within this boundary, six subtle interactions between Lean `v4.34.1`'s
elaborator, definitional-equality engine, LCNF code generator, and kernel
trigger failures that do not appear in unrestricted `import Init` code:

1. **`String.toUTF8` Opacity vs. `String.ofByteArray` 2-Field Unpacking:**
   In Lean `v4.34.1`, `String` (`Init/Prelude.lean:3542-3550`) is a 2-field
   structure `String.ofByteArray (toByteArray : ByteArray) (isValidUTF8 :
   ByteArray.IsValidUTF8 toByteArray)`. `String.toUTF8`
   (`Init/Data/String/Defs.lean:75-77`) is absent from `prelude` +
   `Init.NotationExtra` and is declared under `module` without `@[expose]`,
   making `"Hi".toUTF8` opaque across module boundaries. Matching a 1-field
   pattern `⟨⟨bytes⟩⟩` fails because `String.ofByteArray` has 2 explicit fields,
   whereas 2-field constructor unpacking `match s with | ⟨bytes, _⟩ =>
   bytes.data.toList` (`s.toByteArray.data.toList`) reduces string literals to
   `List UInt8` in the kernel via `string_lit_to_constructor`
   (`src/kernel/expr.cpp:427-446`).
2. **`String.ofList` `:= rfl` `maxRecDepth = 512` Explosion vs. `congrArg
   String.ofList rfl`:**
   Proving `String.ofList cs = "literal"` with a syntactic `:= rfl` proof fails
   at $N = 56$ characters for computed hexadecimal lists (`bytesToHexChars`) and
   at $N = 82$ characters for flat `List Char` literals under `maxRecDepth =
   512`. Two mechanisms combine to cause this failure: (a) in
   `isExprDefEqExpensive` (`Lean/Meta/ExprDefEq.lean:2217-2230`), delta
   unfolding (`isDefEqDelta`) runs before string-literal structural shortcutting
   (`isDefEqStringLit`), expanding `String.ofList` into `List.toByteArray.loop`;
   and (b) Lean `v4.34.1`'s `@[defeq]` attribute inference (`inferDefEqAttr` in
   `Lean/DefEqAttrib.lean:33-35, 121-188`) inspects every theorem whose proof is
   syntactically `rfl` (`isRflProofCore = true`) and re-runs `isDefEq` with
   `smartUnfolding = false`, which unfolds `List.toByteArray.loop` into raw
   nested `List.brecOn` / `List.rec` terms. Replacing `rfl` with `congrArg
   String.ofList rfl` causes `isRflProofCore` to return `false` (skipping
   `smartUnfolding = false`) and unifies the `List Char` arguments via
   `tryHeuristic` (`Lean/Meta/ExprDefEq.lean:1498-1524`), scaling raw string
   literals to $N = 125$ characters (covering 118-character Stage-0 ELF64 `.o`
   hex artifacts) and chunked `String.ofList` equalities to $N = 1,042$ and
   $N = 2,048+$ characters in `131 ms`.
3. **`Nat` `BEq` (`==`) Partial Unfolding in `dsimp` vs. Opaque `BEq`
   Rewriting:**
   In `prelude`-only modules, `(k == idx)` on `Nat` resolves to
   `instBEqOfDecidableEq` (`decide (k = idx)` in `Init/Prelude.lean:1069-1070`).
   Running `dsimp [(· == ·), BEq.beq]` on `if (k == idx) = true then ...`
   unfolds `(k == idx)` inside the visible `@ite` condition `(k == idx) = true`
   while leaving `instDecidableEqBool (k == idx) true` un-unfolded inside
   `@ite`'s hidden `[Decidable c]` argument, causing `rw` and `cases` to fail
   with motive type mismatches. Keeping `(· == ·)` opaque and rewriting with
   `nat_beq_self` and `nat_eq_of_beq_eq_true` preserves syntactic alignment
   across both arguments of `@ite`.
4. **LCNF `List.rec` Code-Generator Rejection vs. `@Nat.rec` `@[csimp]` Support
   & Silent `._unsafe_rec` Emission:**
   Lean `v4.34.1`'s LCNF code generator (`Lean/Compiler/LCNF/ToImpure.lean:183`)
   rejects computational definitions that invoke `@List.rec` (`code generator
   does not support recursor 'List.rec' yet`), whereas `@Nat.rec` succeeds
   because `Init/Data/Nat/Basic.lean:28-29` exports `@[csimp] theorem
   Nat.rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled`—the only recursor
   `@[csimp]` rule in `Init`. Conversely, every recursive `def` (even
   structurally recursive or `Prop`-valued, because `shouldGenCodeFor` in
   `Lean/Elab/PreDefinition/Basic.lean:134-135` checks only
   `!preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable`) invokes
   `addAndCompilePartialRec`
   (`Lean/Elab/PreDefinition/Structural/Main.lean:198`), registering
   `<decl>._unsafe_rec` (`isPartial = true`) in `env.checked`, which
   `TrustedBoundary.lean:1357-1358` rejects as an `unsafe/partial declaration`.
   Expressing computational recursion through `List.foldr`, `List.foldl`, or
   `@Nat.rec`—and proving inductive properties as `theorem` rather than
   `def`—emits zero `._unsafe_rec` constants.
5. **Lazy `ite` `Option`-Accumulator $O(2^N)$ WHNF Duplication vs. Spine-Strict
   `Option.casesOn` & Compositional `List.foldr`:**
   When a pass validator or certificate checker threads an accumulator `acc :
   Option State` that contains a free variable (such as a symbolic initial
   environment `env0 : Nat → Nat`), `useWHNFCache`
   (`Lean/Meta/WHNF.lean:1055-1061`) returns `false` because `e.hasFVar` is
   `true`. If the step body writes `if cond acc = true then step acc else none`
   without pattern-matching `acc` first, reducing `@ite` evaluates `acc` once in
   the condition and returns a second unreduced copy of `acc` in the `then`
   branch, unfolding `Option.rec` $4(2^N - 1) + 2 = \Theta(2^N)$ times and
   exhausting `maxHeartbeats = 200000` at $N = 16$ (`16,501 ms`). Matching
   `match acc with | none => none | some s => ...` before the `ite` forces
   `Option.casesOn` once per step, binding `s` to the constructor payload with
   `@Nat.rec` already eliminated and reducing `Option.rec` unfoldings to
   $2N + 2 = O(N)$ (`112.7 ms` at $N = 16$). Combining spine-strict steps with
   compositional per-block `List.foldr` (`checkMultiBlockPipeline_cons`) scales
   multi-block verification to $N = 1,024+$ instructions (`93.4 ms`) under
   default `maxRecDepth = 512`.
6. **`anneal-audit` Preflight & `Init.Prelude` Syntax Rules:**
   Five recurring syntax and identifier traps in `prelude`-only modules—the
   reserved `section` command keyword in structure fields, rejected `deriving`
   clauses, reserved `eq_*` declaration suffixes in `validateUserDeclIdent`,
   `Prop`-based `ite` on `a <= b`, and the `Nat.lxor` $\to$ `Nat.xor` rename in
   `Init/Data/Nat/Bitwise/Basic.lean:38`—have deterministic `prelude`-compatible
   replacements verified in `support/ProbePreludeTraps.lean`.

## Applicability

These findings apply to all Lean `v4.34.1` developments that restrict imports to
`prelude` + `Init.NotationExtra` or enforce post-elaboration environment audits
modeled on `joshlf/anneal`:

- **Compiler Toolchain:** `leanprover/lean4` version `v4.34.1` (commit
  `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`).
- **Verification Repository & Audit Policy:** `joshlf/anneal` commit
  `beb778bb135474a67dc017c185d2753a60693d8c`
  (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`,
  `trusted/lean/Trusted/MirSemantics.lean`, `trusted/lean/Trusted/Rv64Ast.lean`,
  `trusted/lean/Trusted/Rv64Semantics.lean`, and
  `theory/Anneal/Compiler/*.lean`).
- **Reproducible Support Package:** Self-contained positive proofs in
  `support/ProbePreludeTraps.lean`, automated scaling and error-reproduction
  driver in `support/run_benchmarks.py`, and recorded outputs in
  `support/benchmark_results.json`.

## Findings

### Finding 1: `String.toUTF8` Kernel Opacity vs. `String.ofByteArray` 2-Field Constructor Unpacking

#### Mechanical Root Cause in Lean `v4.34.1`

In Lean 4 versions prior to the UTF-8 byte-array refactor, `String` wrapped a
`List Char` (`String.mk : List Char → String`), allowing pattern matches of the
form `match s with | ⟨cs⟩ => ...`. In Lean `v4.34.1`,
`Init/Prelude.lean:3525-3550` defines `String` instead as a 2-field structure
backed by a `ByteArray` and a `Prop`-valued UTF-8 validity proof:

```lean
-- Init/Prelude.lean:3525-3550
inductive ByteArray.IsValidUTF8 (b : ByteArray) : Prop where
  | intro (cs : List Char) (h : b = List.utf8Encode cs) : ByteArray.IsValidUTF8 b

structure String where
  ofByteArray ::
  toByteArray : ByteArray
  isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
```

Attempting to extract the UTF-8 byte stream of a `String` in a `prelude`-only
module encounters two distinct obstacles if written using legacy idioms:

1. **`String.toUTF8` is both outside `prelude` and unexposed across `module`
   boundaries:** `String.toUTF8` is defined in
   `Init/Data/String/Defs.lean:75-77`, which is not in the transitive import
   closure of `prelude` + `Init.NotationExtra`
   (`trusted/lean/foundation-lock.json`):
   ```text
   <probe>.lean:3:7: error(lean.unknownIdentifier): Unknown constant `String.toUTF8`
   ```
   Furthermore, `Init/Data/String/Defs.lean` begins with the `module` header
   (line `6`) and declares `String.toUTF8` as `@[extern "lean_string_to_utf8"]
   def String.toUTF8 (a : @& String) : ByteArray := a.toByteArray` **without
   `@[expose]`** (unlike `@[expose] def String.utf8ByteSize` at lines `68-70`).
   Consequently, in any Lean 4 `module` file, `String.toUTF8`'s body is hidden
   from the kernel and elaborator:
   ```text
   <probe>.lean:3:0: error: Not a definitional equality: the left-hand side
     "Hi".toUTF8.data.toList
   is not definitionally equal to the right-hand side
     [72, 105]
   ```
2. **Single-field anonymous constructor unpacking `⟨⟨bytes⟩⟩` fails with arity
   mismatch:** Because `String.ofByteArray` has two explicit fields
   (`toByteArray : ByteArray` and `isValidUTF8 : ByteArray.IsValidUTF8
   toByteArray`), matching `| ⟨⟨bytes⟩⟩ => ...` is rejected during elaboration:
   ```text
   <probe>.lean:5:4: error: Insufficient number of fields for `⟨...⟩` constructor:
   Constructor `String.ofByteArray` has 2 explicit field, but only 1 was provided
   ```

#### Verified `prelude`-Only Pattern

Unpacking both fields of `String.ofByteArray` (`| ⟨bytes, _⟩ =>
bytes.data.toList` or `s.toByteArray.data.toList`, as used in
`Trusted/Rv64Semantics.lean:947-949` when serializing `.strtab` symbol names
into ELF64 object files) compiles to `String.casesOn` (`Expr.proj `String 0 s`).
When applied to a string literal `.lit (.strVal "Hi\n")`, both `Meta.whnf`
(`Expr.toCtorIfLit` in `Lean/Meta/WHNF.lean:23-29`) and the C++ kernel
(`string_lit_to_constructor` in `src/kernel/expr.cpp:427-446`) convert the
literal to `String.ofByteArray (List.toByteArray (List.utf8Encode ...)) ...` and
reduce `stringToBytes "Hi\n" = [72, 105, 10]` by `rfl`:

```lean
-- support/ProbePreludeTraps.lean:45-58
def stringToBytes (s : String) : List UInt8 :=
  match s with
  | ⟨bytes, _⟩ => bytes.data.toList

theorem stringToBytes_hi :
    stringToBytes "Hi\n" = [72, 105, 10] := rfl
```

---

### Finding 2: `String.ofList` / `List.toByteArray.loop` `maxRecDepth = 512` Explosion vs. `congrArg String.ofList rfl`

#### Three-Layer Root Cause in Lean `v4.34.1`

In `Trusted/MirSemantics.lean:878-899` and
`Trusted/Rv64Semantics.lean:1028-1037`, an emitted object-file artifact `art :
EmittedArtifact` carries a propositional obligation `art.holds :
encodeRv64ElfHex body = art.hexContents`, where `encodeRv64ElfHex` constructs a
`"elf64-riscv-o:"`-prefixed hexadecimal string via `String.ofList`
(`Init/Prelude.lean:3560-3561`):

```lean
-- Init/Prelude.lean:3559-3561
@[extern "lean_string_mk", expose, implicit_reducible]
def String.ofList (cs : List Char) : String :=
  { toByteArray := List.utf8Encode cs, isValidUTF8 := .intro cs rfl }
```

When a theorem attempts to prove `String.ofList cs = "literal"` using a
syntactic `:= rfl` proof under default `maxRecDepth = 512`, elaboration fails
with `maximum recursion depth has been reached` at **$N = 56$ characters** (`28`
encoded bytes) for `bytesToHexChars` and at **$N = 82$ characters** for a flat
`List Char` literal. Tracing `Lean/Meta/ExprDefEq.lean`, `Lean/Meta/WHNF.lean`,
and `Lean/DefEqAttrib.lean` reveals three interacting mechanisms:

1. **Ordering of `isDefEqDelta` before `isDefEqStringLit` in
   `isExprDefEqExpensive` (`Lean/Meta/ExprDefEq.lean:2217-2230`):**
   Lean's definitional-equality checker includes a fast path `isDefEqStringLit`
   (`Lean/Meta/ExprDefEq.lean:1685-1697`) intended to rewrite `String.ofList cs
   =?= "..."` into `String.ofList cs =?= String.ofList ("...".toList)` without
   unfolding `String.ofList`. However, in `isExprDefEqExpensive`
   (`Lean/Meta/ExprDefEq.lean:2205-2233`), step 5 (`isDefEqDelta` at line
   `2217`) and step 7 (`isDefEqEtaStruct` at line `2222`) execute **before**
   step 11 (`isDefEqStringLit` at line `2230`):
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
   Because `String.ofList` is marked `@[expose, implicit_reducible]`,
   `isDefEqDelta` unfolds `String.ofList cs` on the LHS to
   `String.ofByteArray (List.utf8Encode cs) (.intro cs rfl)` at line `2217`
   before line `2230` is ever reached. Then `isDefEqEtaStruct` (`lines 129-165`)
   projects `.toByteArray` on both sides and converts the RHS string literal via
   `Expr.toCtorIfLit` (`Lean/Meta/WHNF.lean:27-28`) into a second
   `List.utf8Encode ['9', ...]` chain. Both sides are then forced through
   `List.utf8Encode` $\to$ `List.flatMap String.utf8EncodeChar` $\to$
   `List.toByteArray` $\to$ `List.toByteArray.loop` $\to$ `ByteArray.push` $\to$
   `Array.push` $\to$ `List.concat`.
2. **`inferDefEqAttr` (`Lean/DefEqAttrib.lean:33-35, 121-188`) disables
   `smartUnfolding` on every syntactic `:= rfl` theorem:**
   Whenever a theorem declaration has a proof term `val` for which
   `isRflProofCore` (`Lean/DefEqAttrib.lean:129-141`) returns `true` (namely,
   when the proof term's head constant is `Eq.refl`, `rfl`, `Eq.symm`, or an
   existing `@[defeq]` theorem), Lean `v4.34.1` automatically runs
   `inferDefEqAttr` $\to$ `validateDefEqAttr` $\to$ `isDefEqCareful`
   (`Lean/DefEqAttrib.lean:33-35`):
   ```lean
   -- Lean/DefEqAttrib.lean:33-35
   private def isDefEqCareful (e1 e2 : Expr) : MetaM Bool := do
     withOptions (smartUnfolding.set · false) <| do
       withDefault (isDefEq e1 e2) <||> withTransparency .all (isDefEq e1 e2)
   ```
   With `smartUnfolding` set to `false`, `unfoldDefinitionCore?`
   (`Lean/Meta/WHNF.lean:853, 913`) ignores `_sunfold` matcher equations and
   unfolds `List.toByteArray.loop`, `List.flatMap`, `List.map`, `List.flatten`,
   `List.append`, and `List.concat` into raw nested `List.brecOn` and `List.rec`
   applications. At $N = 81$ characters (`List.rec ↦ 948`, `List.brecOn ↦ 328`),
   `isDefEqCareful` sits just below `maxRecDepth = 512`; at $N = 82$ characters
   (or $N = 56$ characters when `cs` is produced by `bytesToHexChars`),
   `isDefEqCareful` exceeds `maxRecDepth = 512`.
3. **Why `congrArg String.ofList rfl` bypasses both bottlenecks:**
   - First, the proof term `congrArg String.ofList rfl` has head constant
     `congrArg`. In `isRflProofCore` (`Lean/DefEqAttrib.lean:129-141`),
     `congrArg` matches none of `Eq.refl`, `rfl`, or `Eq.symm` and does not
     carry `@[defeq]`, so `isRflProofCore` returns **`false`** and
     `inferDefEqAttr` / `isDefEqCareful` (`smartUnfolding = false`) is
     completely skipped.
   - Second, during elaboration of `congrArg String.ofList rfl` against expected
     type `String.ofList cs = "..."`, Lean unifies `String.ofList ?m.a =
     String.ofList ?m.b` with `String.ofList cs = "..."`. While `?m.b` is an
     unassigned metavariable, `String.ofList ?m.b` unfolds only as far as
     `List.toByteArray.loop (List.flatMap String.utf8EncodeChar ?m.b)
     ByteArray.empty`, where `List.toByteArray.loop` is **stuck** on `?m.b`.
     Once the RHS string literal unfolds to `List.toByteArray.loop (List.flatMap
     String.utf8EncodeChar ['9', ...]) ByteArray.empty`, both sides share head
     constant `List.toByteArray.loop` with a metavariable argument on the left,
     triggering `tryHeuristic` (`Lean/Meta/ExprDefEq.lean:1498-1524`) to unify
     `?m.b := ['9', ...]` directly and check `cs = ['9', ...]` in `List Char`
     without running `List.toByteArray.loop` on `cs`.
   - Third, if the theorem's RHS is a raw string literal `"..."`,
     `ensureHasType` still checks `String.ofList ['9', ...] =?= "..."` with
     `smartUnfolding = true`, which succeeds up to **$N = 125$ characters**
     (covering the 118-character Stage-0 ELF64 `.o` string in
     `MirToRv64Stage0.lean:1203-1212`) and reaches `maxRecDepth = 512` at
     $N = 126$ characters inside `List.toByteArray.loop`. When both sides of the
     equality are structured as `String.ofList` over chunked character lists
     ($\le 64$ characters per chunk so each `List.foldr` / `List.append` spine
     stays well below `512`), neither the elaborator nor the kernel ever unfolds
     `String.ofList`, scaling to $N = 1,042$ and $N = 2,048+$ characters in
     `131 ms`.

#### Empirical Scaling Benchmark (`support/benchmark_results.json`)

All measurements below were recorded with Lean `v4.34.1` under default
`maxRecDepth = 512` (baseline process startup + `prelude` / `Init.NotationExtra`
import overhead: `67.0 ms`):

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

#### Mechanical Root Cause in `Init/Prelude.lean`

In standard Lean 4 files that import `Init.Data.Nat.Basic`, `Nat` has a
dedicated `@[expose] instance : BEq Nat := ⟨Nat.beq⟩`. In `prelude` +
`Init.NotationExtra` modules, however, `Init.Data.Nat.Basic` is not imported, so
`(k == idx)` on `Nat` synthesizes the generic `DecidableEq`-backed instance from
`Init/Prelude.lean:1069-1070`:

```lean
-- Init/Prelude.lean:1069-1070
@[expose, implicit_reducible]
instance instBEqOfDecidableEq [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)
```

When a function branches on `if (k == idx) = true then val else locals k` (such
as `MirEnv.updateLocal` in `Trusted/MirSemantics.lean`), the elaborated `@ite`
application contains `(k == idx)` in **two** places:

```lean
@ite (Option Nat)
  ((k == idx) = true)                      -- 1. explicit Prop condition `c`
  (instDecidableEqBool (k == idx) true)    -- 2. implicit `[Decidable c]` instance
  val
  (locals k)
```

Because `dsimp` simplifies only non-dependent subterms and skips implicit
`Decidable` proof/instance arguments whose types depend on the condition,
calling `dsimp [updateLocal, (· == ·), BEq.beq]` unfolds `(k == idx)` inside the
first argument (`decide (k = idx) = true`) while leaving `(k == idx)`
**un-unfolded** inside the second argument (`instDecidableEqBool (k == idx)
true`). Any subsequent `rw` or `cases` on `decide (idx = idx) = true` then
abstracts only the first argument and fails with an ill-typed `@ite` motive:

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

Keep `(· == ·)` and `BEq.beq` **opaque** during `dsimp`, and rewrite or split on
`(k == idx)` directly using `nat_beq_self`, `nat_eq_of_beq_eq_true`, and
`nat_beq_comm` (`theory/Anneal/Compiler/MirOptPasses.lean:122-146, 189-200`,
reproduced in `support/ProbePreludeTraps.lean:142-215`):

```lean
-- support/ProbePreludeTraps.lean:142-171
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

Because `rw [nat_beq_self idx]` and `cases h : (k == idx)` abstract the opaque
subterm `(idx == idx)` or `(k == idx)` simultaneously in both the proposition
`((k == idx) = true)` and the instance `(instDecidableEqBool (k == idx) true)`,
the `@ite` motive remains well-typed.

---

### Finding 4: LCNF Code-Generator `List.rec` Rejection vs. `@Nat.rec` / `List.foldr` Acceptance & Silent `._unsafe_rec` Emission

#### 1. Why LCNF Rejects `@List.rec` but Accepts `@Nat.rec`, `List.foldr`, and `List.foldl`

In Lean `v4.34.1`, every non-`Prop`, non-`theorem`, computable `def` is compiled
through the LCNF pipeline (`Lean/Compiler/LCNF/Main.lean`). Prior to LCNF
lowering, `Compile.preprocess` (`Lean/Compiler/LCNF/ToLCNF.lean:447`) applies
all registered `@[csimp]` replacement theorems (`LCNF.CSimp.replaceConstants`).
Next, `ToImpure.lean:180-185` (and `Lean/CoreM.lean:682-696`) rejects any
remaining inductive recursor application that has no special compiler lowering:

```lean
-- Lean/Compiler/LCNF/ToImpure.lean:180-185
| .recInfo _ =>
  throwError "code generator does not support recursor `{declName}` yet, \
    consider using 'match ... with' and/or structural recursion"
```

- **Why `@List.rec` fails in computational `def`s:** Neither `Init/Prelude.lean`
  nor `Init/Data/List/Basic.lean` defines a `@[csimp]` replacement for
  `List.rec`. Invoking `@List.rec` inside a computational `def` therefore
  reaches `ToImpure.lean:183` unchanged and fails:
  ```text
  <probe>.lean:4:4: error: code generator does not support recursor `List.rec` yet,
  consider using 'match ... with' and/or structural recursion
  ```
- **Why `@Nat.rec` succeeds:** `Init/Data/Nat/Basic.lean:22-29` (which is in the
  transitive import closure of `Init.NotationExtra`) defines `Nat.recCompiled`
  and registers the **only** recursor `@[csimp]` theorem in `Init`:
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
  `Compile.preprocess` rewrites `@Nat.rec` to `@Nat.recCompiled` before
  `ToImpure` runs.
- **Why `List.foldr` and `List.foldl` succeed without emitting `._unsafe_rec` in
  user modules:** `List.foldr` (`Init/Data/List/Basic.lean:1058`) and
  `List.foldl` (`Init/Prelude.lean:2885`) are already compiled inside `Init`
  (whose declarations are allowlisted by `TrustedBoundary.lean`'s foundation
  lock). Calling `List.foldr` or `List.foldl` from a user `def` is a
  non-recursive function application.

#### 2. Why Structural Recursive `def`s Emit `<decl>._unsafe_rec` and Fail `anneal-audit`

A natural impulse when `@List.rec` is rejected by LCNF is to write a structural
recursive function using pattern matching:

```lean
def recDefSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + recDefSum xs
```

Even though Lean `v4.34.1`'s structural recursion compiler
(`Lean/Elab/PreDefinition/Structural/Main.lean:183-218`) proves termination
using `List.brecOn` without `Init.WF`, line `198` of `Structural/Main.lean`
still passes the original recursive pre-definition to `addAndCompilePartialRec`
(`Lean/Elab/PreDefinition/Basic.lean:280-295`) so the LCNF code generator can
compile tail-recursive loops rather than `brecOn` closures:

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

Crucially, `Compiler.mkUnsafeRecName declName` (`Lean/Compiler/Old.lean:49`)
creates `<declName>._unsafe_rec` with `safety := .partial`
(`ConstantInfo.isPartial = true`) and inserts it into the kernel's checked
environment (`env.checked`). Even more subtly, `shouldGenCodeFor`
(`Lean/Elab/PreDefinition/Basic.lean:134-135`) checks **only** syntactic
declaration modifiers, not whether the return type is `Prop`:

```lean
-- Lean/Elab/PreDefinition/Basic.lean:134-135
def shouldGenCodeFor (preDef : PreDefinition) : Bool :=
  !preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable
```

Thus **every** recursive `def` (computational or `Prop`-valued) that is not
marked `noncomputable` emits `<decl>._unsafe_rec` into the `.olean` environment.
When `anneal-audit` (`trusted/audit/TrustedBoundary.lean:1357-1358`) inspects
every declaration in the target closure, it rejects `<decl>._unsafe_rec`:

```lean
-- trusted/audit/TrustedBoundary.lean:1357-1358
if ci.isUnsafe || ci.isPartial then
  errors := errors.push s!"{label}: unsafe/partial declaration '{name}'"
```

#### Verified Zero-`._unsafe_rec` Matrix (`support/benchmark_results.json`)

| Declaration Form | Example | LCNF Codegen | Emits `<decl>._unsafe_rec`? | `anneal-audit` Status |
| :--- | :--- | :--- | :--- | :--- |
| Computational `def` calling `@List.rec` | `def sumViaListRec := @List.rec ...` | **Rejected** (`ToImpure.lean:183`) | No | Fails elaboration |
| Recursive `def` (structural or `match`) | `def recDefSum \| [] => 0 \| x :: xs => ...` | Accepted (`addAndCompilePartialRec`) | **Yes (`isPartial = true`)** | **Rejected** (`unsafe/partial declaration`) |
| Computational `def` calling `List.foldr` / `List.foldl` | `evalPlaceOffset`, `updateCodeAt`, `applyRelocsToCode` | Accepted | **No (`false`)** | **Accepted** |
| Computational `def` calling `@Nat.rec` | `stepBounded`, `checkSyntheticBlock` | Accepted (via `@[csimp] Nat.rec_eq_recCompiled`) | **No (`false`)** | **Accepted** |
| Recursive `theorem` (`Prop`-valued) | `theorem list_length_append` | Skipped (`shouldGenCodeFor = false`) | **No (`false`)** | **Accepted** |

---

### Finding 5: Lazy `ite` `Option`-Accumulator $O(2^N)$ WHNF Duplication vs. Spine-Strict Pattern Matching & Compositional `List.foldr`

#### Mechanical Root Cause: `useWHNFCache = false` on Free Variables + Unforced `@ite` Branches

In translation-validation and pass-certificate theorems (such as
`theory/Anneal/Compiler/KancVerticalSlice.lean:271-345` and
`MirOptPasses.lean`), a bounded checker folds over $N$ instructions threading an
accumulator `acc : Option State` initialized with a symbolic environment
parameter `(env0 : Nat → Nat)` (a free variable inside the theorem body).

Two mechanisms in `Lean/Meta/WHNF.lean` interact when `acc` is threaded through
an `@ite` step without pattern-matching `acc` first:

1. **`Meta.whnf` disables its WHNF cache whenever `e.hasFVar` is `true`
   (`Lean/Meta/WHNF.lean:1055-1061`):**
   ```lean
   -- Lean/Meta/WHNF.lean:1055-1061
   @[inline] private def useWHNFCache (e : Expr) : MetaM Bool := do
     -- We cache only closed terms without expr metavars.
     if e.hasFVar || e.hasExprMVar || (← read).customCanUnfoldPredicate?.isSome then
       return false
     else
       return true
   ```
   Because `acc` contains the theorem parameter `env0`, `e.hasFVar` is `true` at
   every step, so `Meta.whnf` never caches the WHNF of `acc`.
2. **Unforced `@ite` duplicates the unreduced `@Nat.rec` term `acc` at every
   step:**
   Consider the lazy step body:
   ```lean
   if (match acc with | some s => s.wm == idx | none => false) = true then
     match acc with | some s => some ⟨s.wm + 1, s.env⟩ | none => none
   else none
   ```
   Here the outer eliminator is `@ite`, whose major premise is the `Decidable`
   instance for `(match acc with ...) = true`. Reducing `@ite` to WHNF first
   reduces `acc` inside the condition to verify `s.wm == idx`, and then discards
   that work to return the unreduced `then`-branch `match acc with | some s =>
   some ⟨s.wm + 1, s.env⟩ | none => none`, which still contains the
   **unreduced** `@Nat.rec ... idx` term `acc`! At step $k + 1$, reducing
   `acc_{k+1}` forces `acc_k` twice: once in the condition and once in the
   `then`-branch. Across $N$ steps, `Meta.whnf` unfolds `BEq.beq` exactly
   $2(2^N - 1)$ times and `Option.rec` $4(2^N - 1) + 2$ times.
3. **Why spine-strict `match acc with | none => none | some s => ...` restores
   $O(N)$ reduction:**
   When `match acc with` is placed **outside** the `ite`:
   ```lean
   match acc with
   | none => none
   | some s => if (s.wm == idx) = true then some ⟨s.wm + 1, s.env⟩ else none
   ```
   the outer eliminator is `Option.casesOn acc ...`, whose major premise is
   `acc` itself (`@Nat.rec ... idx`). Reducing `Option.casesOn` to WHNF reduces
   `acc` **once** to `Option.some ⟨w, env0⟩` and binds `s := ⟨w, env0⟩`—a
   constructor term from which `@Nat.rec` has already been eliminated. Both the
   `ite` condition (`s.wm == idx`) and the `then`-branch (`some ⟨s.wm + 1,
   s.env⟩`) now reference `s` rather than `acc`, reducing `BEq.beq` unfoldings
   from $2(2^N - 1)$ to **$2N$** and `Option.rec` unfoldings from $4(2^N - 1) +
   2$ to **$2N + 2$**.

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

Even with spine-strict `Option` matching, a single monolithic `@Nat.rec` fold
pushes 3 recursive WHNF frames per step and reaches `maxRecDepth = 512` at
$N = 172$ steps (`Nat.rec ↦ 249` at failure for $N = 256$). Decomposing a
multi-block function into per-block `rfl` lemmas (64 instructions per block)
combined via `checkMultiBlockPipeline_cons` (`List.foldr`) bounds the maximum
WHNF recursion depth by the block size rather than total function length:

| Total Instructions ($N$) | Monolithic `@Nat.rec` Status | Monolithic Time (`ms`) | Compositional `List.foldr` Blocks ($B \times 64$) | Compositional `List.foldr` Status | Compositional Time (`ms`) |
| ---: | :--- | ---: | ---: | :--- | ---: |
| 64 | `ok` | 89.0 | $1 \times 64$ | `ok` | 91.8 |
| 128 | `ok` | 100.6 | $2 \times 64$ | `ok` | 90.2 |
| 171 | `ok` (threshold max) | 114.4 | — | — | — |
| 256 | **`maxRecDepth`** | 83.8 | $4 \times 64$ | `ok` | 90.7 |
| 512 | **`maxRecDepth`** | 83.5 | $8 \times 64$ | `ok` | 91.5 |
| 1024 | **`maxRecDepth`** | 82.9 | $16 \times 64$ | `ok` | 93.4 |

---

### Finding 6: `anneal-audit` Preflight & `Init.Prelude` Identifier/Syntax Traps

Five additional preflight and library boundaries govern `prelude` +
`Init.NotationExtra` modules audited by `trusted/audit/TrustedBoundary.lean`:

| Trap | Failure Diagnostic in Lean `v4.34.1` / `anneal-audit` | Root Cause | Verified `prelude`-Compatible Replacement |
| :--- | :--- | :--- | :--- |
| **`section` structure field name** | `<probe>.lean:8:10: error: unexpected token ':'; expected command` (and `policy:command parser error` in `TrustedBoundary.lean:1004-1019`) | `section` is a reserved command keyword in Lean 4's grammar (`Lean.Parser.Command.section`). | Rename the structure field to `secKind : Rv64SectionKind` (`Trusted/Rv64Ast.lean:395`). |
| **`deriving DecidableEq, BEq`** | `policy:deriving clauses are unsupported` (`TrustedBoundary.lean:644-649`) | `scanPolicyText` explicitly forbids `deriving` clauses in audited source files so all synthesized instances remain explicit. | Define an explicit `Type.beq` function and `instance : BEq Type` (`support/ProbePreludeTraps.lean:340-350`). |
| **`.eq_of_beq_eq_true` / `eq_of_decide` lemma names** | `declaration name '<name>' uses reserved suffix/prefix` (`TrustedBoundary.lean:511-535`) | `validateUserDeclIdent` reserves `eq_1`..`eq_N`, `eq_def`, `eq_unfold`, and any final name component starting with `eq_` (`last.startsWith "eq_"`) to prevent user theorems from shadowing kernel/equation-compiler projections. | Name equality reflection lemmas `.of_beq_eq_true` or `nat_eq_of_beq_eq_true` (`last` starts with `of_` or `nat_`, not `eq_`). |
| **`if a <= b` condition type** | `tactic 'rewrite' failed` when rewriting `Nat.ble a b = true` | In `Init/Prelude.lean:1770-1778`, `a <= b` is the `Prop` `LE.le a b` (`Nat.le`) decided by `Nat.decLe`, not `Bool` `Nat.ble`. | Split with `if h : a <= b then ... else ...` (`Decidable.byCases`) and simplify with `simp [h]` (`support/ProbePreludeTraps.lean:360-369`). |
| **`Nat.lxor` and `rcases` / `omega`** | `error(lean.unknownIdentifier): Unknown constant 'Nat.lxor'` | `Nat.lxor` was renamed to `Nat.xor` in `Init/Data/Nat/Bitwise/Basic.lean:38` (imported via `Init.NotationExtra`). `rcases` (`Init.RCases`) and `omega` (`Init.Omega`) are outside `prelude` + `Init.NotationExtra`. | Use `Nat.xor` (`Trusted/Rv64Semantics.lean`) and destruct inductive hypotheses with `cases` / `match` (`support/ProbePreludeTraps.lean:371-375`). |

## Boundaries

1. **String-Literal vs. `String.ofList` RHS Limit (`N = 125` vs.
   `N = 2,048+`):**
   When the RHS of an equality theorem is a raw string literal `"..."`,
   `congrArg String.ofList rfl` avoids `inferDefEqAttr` (`smartUnfolding =
   false`) and avoids unfolding `String.ofList` on the LHS, but `ensureHasType`
   still checks `String.ofList ['9', ...] =?= "..."` with `smartUnfolding =
   true`. Under `maxRecDepth = 512`, that terminal `List.toByteArray.loop` check
   succeeds up to **$N = 125$ ASCII characters** and hits `maxRecDepth = 512` at
   $N = 126$ characters. For artifacts exceeding 125 characters (such as
   521-byte / 1,042-character or 1,024-byte / 2,048-character ELF64 hex
   payloads), expressing the expected literal as `String.ofList` over chunked
   character lists ($\le 64$ characters per chunk) keeps both sides in
   `String.ofList` form so `congrArg String.ofList rfl` never enters
   `List.toByteArray.loop`.
2. **Closed-Term vs. Free-Variable WHNF Caching in Finding 5:**
   When an `Option` accumulator `acc` is a **closed** ground term (`e.hasFVar ==
   false` and `e.hasExprMVar == false`), `useWHNFCache`
   (`Lean/Meta/WHNF.lean:1058`) returns `true` and memoizes the WHNF of `acc`
   across both branches of an unforced `ite`. The $O(2^N)$ elaborator blowup in
   Finding 5 specifically manifests when `acc` contains at least one free
   variable (`e.hasFVar == true`, such as a universally quantified initial state
   or environment parameter `(env0 : Nat → Nat)`) or expression metavariable.
   Spine-strict pattern matching (`match acc with | none => none | some s =>
   ...`) guarantees $O(N)$ WHNF reduction regardless of whether `acc` is closed
   or open.
3. **Un-chunked `List.foldr` Spine Limit (`L <= 505`):**
   Because `List.foldr` (`Init/Data/List/Basic.lean:1058`) is not
   tail-recursive, reducing a single flat `List.foldr` over a list of length
   $L \ge 506$ exceeds `maxRecDepth = 512`. Large lists reduced in the kernel
   must be structured as two-level chunked lists (e.g., $32 \times 32 = 1,024$
   elements) or proved compositionally via `checkMultiBlockPipeline_cons`.

## Evidence

### Repository Source Citations

- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`,
  `v4.34.1`):**
  - `src/lean/Init/Prelude.lean:1069-1070` (`instBEqOfDecidableEq`),
    `1770-1778` (`LE Nat` / `Nat.decLe`), `2885-2888` (`List.foldl`),
    `3525-3561` (`ByteArray.IsValidUTF8`, `String.ofByteArray`, `String.ofList`,
    `List.toByteArray.loop`).
  - `src/lean/Init/Data/String/Defs.lean:6, 68-80` (`module` header and
    unexposed `@[extern "lean_string_to_utf8"] def String.toUTF8`).
  - `src/lean/Init/Data/Nat/Basic.lean:22-29` (`Nat.recCompiled` and `@[csimp]
    theorem Nat.rec_eq_recCompiled`).
  - `src/lean/Init/Data/Nat/Bitwise/Basic.lean:38` (`Nat.xor`).
  - `src/lean/Lean/Meta/ExprDefEq.lean:129-165` (`isDefEqEtaStruct`),
    `1498-1524` (`tryHeuristic`), `1685-1697` (`isDefEqStringLit`), `2205-2233`
    (`isExprDefEqExpensive` step ordering).
  - `src/lean/Lean/DefEqAttrib.lean:33-35` (`isDefEqCareful` setting
    `smartUnfolding := false`), `121-188` (`isRflProofCore` and
    `inferDefEqAttr`).
  - `src/lean/Lean/Meta/WHNF.lean:23-29` (`Expr.toCtorIfLit`), `853-918`
    (`unfoldDefinitionCore?`), `1055-1061` (`useWHNFCache`).
  - `src/lean/Lean/Compiler/LCNF/ToImpure.lean:180-185` (`List.rec` codegen
    rejection).
  - `src/lean/Lean/Elab/PreDefinition/Basic.lean:134-135` (`shouldGenCodeFor`),
    `280-295` (`addAndCompilePartialRec` emitting `._unsafe_rec`).
  - `src/lean/Lean/Elab/PreDefinition/Structural/Main.lean:183-218` (structural
    recursion compiler calling `addAndCompilePartialRec`).
- **`joshlf/anneal` (`beb778bb135474a67dc017c185d2753a60693d8c`):**
  - `trusted/audit/TrustedBoundary.lean:511-535` (`validateUserDeclIdent`),
    `644-649` (`deriving` rejection), `1004-1019` (command parser check),
    `1357-1358` (`ci.isUnsafe || ci.isPartial` rejection).
  - `trusted/lean/foundation-lock.json` (`Init.Prelude` + `Init.NotationExtra`
    lock).
  - `trusted/lean/Trusted/Rv64Ast.lean:393-399` (`Rv64SymDef.secKind`).
  - `trusted/lean/Trusted/Rv64Semantics.lean:947-949` (`⟨bytes, _⟩` 2-field
    unpacking), `1012-1037` (`rv64HexDigit` and `encodeRv64ElfHex`).
  - `theory/Anneal/Compiler/MirToRv64Stage0.lean:1118-1212`
    (`congrArg String.ofList rfl` on Stage-0 ELF64 `.o` artifacts).
  - `theory/Anneal/Compiler/MirOptPasses.lean:122-146, 189-200` (`nat_beq_self`,
    `nat_eq_of_beq_eq_true`, `nat_beq_comm`, `updateLocal_comm`).
  - `theory/Anneal/Compiler/KancVerticalSlice.lean:271-345`
    (`checkSyntheticBlock`, `checkSyntheticPipeline`,
    `checkMultiBlockPipeline_cons`).

### Support Files and SHA-256 Digests

- `support/ProbePreludeTraps.lean`
  (`sha256: a692c4682372e307f80d90ab5dc374f545216a568c694ed4f548ef373d54ae54`):
  Self-contained `prelude` + `import Init.NotationExtra` module verified with
  Lean `v4.34.1` (`294.8 ms`, exit code `0`, zero `._unsafe_rec` constants).
- `support/run_benchmarks.py`
  (`sha256: 4e70b4a6aff0eecd85ee304e6e07c078262a8661fd46de482aaed7f45519baad`):
  Automated scaling benchmark and negative diagnostic reproduction runner.
- `support/benchmark_results.json`
  (`sha256: 6c5c9df5e3461fa3cfd34b6182f5719c15da1bf089e4c88df0753b9e358acac2`):
  Recorded JSON output of all benchmarks and compiler diagnostic probes.

## Revalidation

To revalidate all positive proofs, scaling tables, and negative error
reproductions from the report package directory using Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`):

```bash
# 1. Verify the self-contained prelude-only probe directly with Lean 4.34.1
lean support/ProbePreludeTraps.lean

# 2. Re-run the full scaling benchmark and diagnostic suite
python3 support/run_benchmarks.py
```

Revalidating on a newer Lean 4 toolchain should check:

1. Whether `Init/Data/String/Defs.lean` adds `@[expose]` to `String.toUTF8`.
2. Whether `Lean/DefEqAttrib.lean` (`inferDefEqAttr`) continues to run
   `isDefEqCareful` with `smartUnfolding = false` on syntactic `:= rfl`
   theorems, and whether `isDefEqStringLit` is moved ahead of `isDefEqDelta` in
   `Lean/Meta/ExprDefEq.lean`.
3. Whether `Lean/Compiler/LCNF/ToImpure.lean` adds `@[csimp]` or native support
   for `@List.rec`, and whether `shouldGenCodeFor` in
   `Lean/Elab/PreDefinition/Basic.lean` continues to emit `._unsafe_rec` for
   structural recursive `def`s.
