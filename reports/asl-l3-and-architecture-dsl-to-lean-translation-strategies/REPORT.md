# ASL, L3, and Architecture DSL-to-Lean 4 Translation Strategies for Anneal

## Summary

This report investigates the internal compiler architectures, type systems, and semantic lowering passes of the two primary non-Sail hardware architecture description ecosystems—Arm's **Architecture Specification Language (ASL)** (`rems-project/mra_tools`, `rems-project/asl-interpreter`, `rems-project/asl_to_sail`, and `herd/herdtools7/asllib`) and Anthony Fox's **L3** (`coruus/L3`)—and evaluates how they compare against Sail (`rems-project/sail`) as sources for Lean 4 ISA models in Anneal (`joshlf/anneal-private`).

1. **ASLv0 vs. ASLv1 Type-Checking and Getter/Setter Reference Semantics**:
   - Arm's Machine Readable Architecture (MRA) XML specifications are extracted by `mra_tools/bin/instrs2asl.py` and `bin/reg2asl.py` into ASLv0 (`rems-project/asl-interpreter`), where bitvector types `bits(E)` carry arbitrary AST expressions `E` checked by unification (`libASL/tcheck.ml:811-955`) and external Z3 queries (`check_constraints`, `libASL/tcheck.ml:761-790`, which contains an explicit unsoundness note on integer division at lines `725-727, 743-754`).
   - ASLv0 array-like setters (`Decl_ArraySetterDefn`) permit `Formal_InOut(ty, id)` reference parameters (`&vector`, e.g., `Elem[bits(N) &vector, integer e, integer size] = bits(size) value` in `asl-interpreter/prelude.asl:68-77`). While `libASL/tcheck.ml:1588-1676` elaborates nested slice assignments on getters/setters into `LExpr_ReadWrite`, `asl-interpreter`'s evaluator (`libASL/eval.ml:595-601, 972-981`) invokes `eval_proccall` by value on `LExpr_Write`, binding `Formal_InOut` parameters to local variables in the callee environment and discarding the callee frame on return without writing back to the caller's l-expression.
   - Arm's modern ASLv1 (`herd/herdtools7/asllib`) eliminates both problems at the language level: integer constraints are tracked statically in the type system (`constraint_kind = UnConstrained | WellConstrained of int_constraint list * precision_loss_flag | PendingConstrained | Parameterized`, `asllib/AST.mli:255-273`), bitvector widths must evaluate to static constants or constrained symbolic expressions (`asllib/Typing.ml:568-573`, `Interpreter.ml:696-700`), `&` reference setter parameters are removed in favor of paired `accessor_pair` definitions (`asllib/desugar.ml:212-248`), and partial setter assignments (`Setter(args).field[slice] = rhs`) are desugared by `desugar_setter` (`asllib/desugar.ml:126-162`) into a 3-statement read-modify-write sequence using a fresh `__setter_v1_temporary`.

2. **Why `asl_to_sail` Requires Iterative Z3 Constraint Repair and Manual Patching**:
   - `rems-project/asl_to_sail` translates ASLv0 into Sail by converting `Formal_InOut` setter parameters into pure return values (`Decl_ArraySetterDefn` in `lib/translate_asl.ml:3082-3117` and `sail_of_setter_assignment` in `lib/translate_asl.ml:1762-1784`), expanding slice assignments on getters/setters (`LExpr_Slices(LExpr_ReadWrite ...)` in `lib/translate_asl.ml:2038-2065`) into read-modify-write updates via `SetSlice` / `vector_update_subrange`, hoisting runtime SVE/SME vector lengths (`CurrentVL.read()`, `PL.read()`) into existential type variables via `vlExprsClass` (`lib/translate_asl.ml:257-342`) or `-mono_vl` case splits (`lib/translate_asl.ml:2900-2910`), and running a 3-pass fixed-point abstract interpreter (`intConstraintsClass` in `lib/translate_asl.ml:1038-1194, 3149-3179`) to infer finite set/range bounds (`IC_Set`, `IC_Range`) for decode-time bit-slice widths.
   - Because ASLv0 leaves many bit-width invariants implicit in procedural control flow, `asl_to_sail` wraps `Libsail.Type_check.check` in a 50-iteration feedback loop (`iterate_check` in `bin/main.ml:731-770`) that intercepts `Err_unresolved_quants` and `Err_failed_constraint` errors and invokes `Sail_to_sail.rewrite_add_constraint` (`lib/sail_to_sail.ml:844-925`) to inject missing type constraints or runtime `assert(...)` statements—still requiring manual `.sail` and `.val.sail` override patches (`bin/main.ml:780-829`) where automatic inference fails.

3. **L3's Closed Functional Compilation Pipeline (`coruus/L3`)**:
   - In contrast to ASL and Sail, L3 has a compact, non-dependent Hindley-Milner type system (`Type.bty` in `L3/Base.sml:329-429`) where bitwidths are either concrete positive integers (`BV of int`) or type variables restricted to finite integer sets (`BVV of string` with `Constrain.constraints` in `L3/Base.sml:263-318`, e.g., `with N in 8, 16, 32, 64` in `isa-models/arm-v8/v8-base.spec:104, 240`).
   - L3 compiles bit-string pattern matching (`case 'sf op S 100010 sh imm12 Rn Rd'` in `isa-models/arm-v8/v8-iset.spec:2408`) in two pure AST passes: `Matches.boolifyMatches` (`L3/Matches.sml:435-483`) explodes an $N$-bit scrutinee via `boolify'N` into an $N$-tuple of booleans and reconstructs sub-bitvector bindings via `[..]`, and `Convert.boolMatchConv` (`L3/Export.sml:1213-1323`) compiles the boolean matrix into a balanced `if-then-else` decision tree while `Term.checkMatch` (`L3/Base.sml:3198-3278`) statically verifies pattern exhaustiveness and irredundancy.
   - L3 lowers imperative state and exceptions without a free monad: `Exception.buildExceptionDatatype` (`L3/Export.sml:36-54`) synthesizes an `exception` datatype (`NoException | ...`) stored as a field `exception :: exception` in the single global `state` record (`Monad.defineStateType`, `L3/Export.sml:682-712`); `Monadify.monadifyDefn` (`L3/Export.sml:843-1013`) introduces state-passing combinators (`m'const`, `m'bind`, `m'read`, `m'write`, `m'extend` for local mutable variables via state-tuple extension `ty ** sty`), and `Monadify.deMonadifyDefn` (`L3/Export.sml:1026-1121`) beta-reduces those combinators away, emitting pure total functions `state -> val * state` (`HOLconv` in `L3/HolExport.sml:571-676`).

4. **Mapping `CONSTRAINED UNPREDICTABLE` vs. `UNDEFINED` into Anneal's `StepResult` and Mechanized Probe**:
   - In `support/asl_l3_to_lean_bridge_probe.lean` (1,161 lines, verified under Lean 4.34.1 with `-j1 -M768`, zero `sorryAx`, and zero custom axioms), we mechanize:
     - **(a)** Lawful indexed lenses (`AslIndexedLens`, `LawfulIndexedLens`) for `X`, `V`, and `Elem`, proving that `asl_to_sail`'s pure return-value lowering (`asl_to_sail_Elem_write`) and `asllib`'s `desugar_setter` temporary RMW lowering (`asllib_desugar_rmw`) are definitionally equal (`rfl`), satisfy full read-after-write roundtrip and lane/register framing, and avoid `asl-interpreter`'s by-value bug (`asl_interpreter_by_value_bug_loses_write`).
     - **(b)** The interaction of ASL's `ConstrainUnpredictable` and L3's `UNKNOWN ("...") :: bits(k)` with Anneal's `BehaviorOf`: when `ConstrainUnpredictable` is modeled as `StepResult.choice ChoiceKind.demonic`, any permitted `Constraint_UNDEF` / `Unallocated` branch (such as `case 2 => Unallocated` in L3's `LoadImmediate` overlap handler at `isa-models/arm-v8/v8-iset.spec:1178-1196`) causes `(BehaviorOf M p).defined ⟨s, 1⟩` to collapse to `False` (`constrained_unpred_with_undef_not_defined`, `l3_load_imm_unpred_not_defined`). Restricting `ConstrainUnpredictable` to non-faulting architectural outcomes (`Constraint_WBSUPPRESS`, `Constraint_UNKNOWN`, `Constraint_NOP`) preserves `BehaviorOf.defined` (`constrained_unpred_nonfaulting_is_defined`, `nonFaultingLoadImm_defined_and_reaches_all`).
     - **(c)** An L3-to-Lean 4 AArch64 prototype (`decodeA64`, `encodeA64`, `L3State`, `l3_Run`, `L3Machine`, `L3Bridge`) with a mechanized encode/decode roundtrip theorem (`decodeA64_encodeA64_roundtrip`), `TotalStep` and `InhabitedDemonic` proofs, kernel `rfl` execution of a 4-instruction AArch64 program (`ADD X0, X1, #42; STR X0, [SP, #0]; LDR X2, [SP, #0]; RET`), and an end-to-end `BehaviorOf L3Bridge.machine testProg ≤ testProgSpec` refinement theorem (`testProg_refines_spec`).

---

## Applicability

This report applies to the repositories, revisions, and toolchains pinned in `REPORT.json` and `support/source-manifest.json`:

| Subject | Repository / Package | Revision / Commit SHA | Tree SHA | Primary Inspected Paths |
| :--- | :--- | :--- | :--- | :--- |
| `anneal` | `https://github.com/joshlf/anneal-private` | `42f4571d761b46c7142815f38b69c3781b3555e3` | `219dfb9655e7b1a2754d3590cdbbec224ac790a0` | `trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`, `theory/Anneal/StepResult.lean`, `theory/Anneal/FunctionalTranslation.lean` |
| `asl-interpreter` | `https://github.com/rems-project/asl-interpreter` | `8cfc0b27002d282da55568e3462868e9dfd8c3bd` | `f2324bfbff6f660dffce481b230419c56a9ba22d` | `libASL/asl.ott`, `libASL/tcheck.ml`, `libASL/eval.ml`, `libASL/value.ml`, `prelude.asl` |
| `mra_tools` | `https://github.com/rems-project/mra_tools` | `941317606f36580f668498889abc6301ed8222d8` | `cbdffcb5376e0c2c9f6fa0bb95fdad79339109d7` | `bin/instrs2asl.py`, `bin/reg2asl.py`, `bin/asl_utils.py`, `support/fetchdecode.asl`, `support/memory.asl`, `prelude.asl` |
| `asl_to_sail` | `https://github.com/rems-project/asl_to_sail` | `78242b8d60a507fab18d9b4f225bfc7bd33e62b3` | `61d7bcc4c75f5da6b031b964b41c104652997dd7` | `lib/translate_asl.ml`, `lib/sail_to_sail.ml`, `bin/main.ml`, `prelude.sail` |
| `herdtools7` | `https://github.com/herd/herdtools7` | `6bea2e8131feaeb497a7bf86d52d94cdd8721a6c` | `8f63475252d3c49d08a2ab07fbca6f9186d8b88c` | `asllib/AST.mli`, `asllib/desugar.ml`, `asllib/Typing.ml`, `asllib/Interpreter.ml` |
| `L3` | `https://github.com/coruus/L3` | `d6558e679a25ffaaf16a47a3189f8f8111e45e0c` | `537e00c5d951c7f147c47365689d1392c93eba6f` | `L3/Base.sml`, `L3/Matches.sml`, `L3/Export.sml`, `L3/HolExport.sml`, `L3/SMLExport.sml`, `isa-models/arm-v8/v8-base.spec`, `isa-models/arm-v8/v8-iset.spec` |
| `sail` | `https://github.com/rems-project/sail` | `0f51056900af85d0b18928d6ea2d2271d18184e8` | `7d85a599692b9d1826ea881a040e4e1cccd50bc9` | `src/sail_lean_backend/pretty_print_lean.ml`, `src/sail_lean_backend/sail_plugin_lean.ml` |
| `lean4` | `leanprover/lean4` | `v4.34.1` | N/A | `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean` |

---

## Findings

### 1. Arm ASL Language Architecture & MRA Extraction (`mra_tools`, `asl-interpreter`, `herdtools7/asllib`)

Basis: `mixed` (`direct-inspection` of `mra_tools`, `asl-interpreter`, and `herdtools7/asllib` + `empirical-probe` in `support/asl_l3_to_lean_bridge_probe.lean`)

#### 1.1 MRA XML Extraction into ASLv0 (`rems-project/mra_tools`)

Arm's Machine Readable Architecture (MRA) release distributes the AArch64 and AArch32 instruction sets and system registers as XML files containing `<regdiagram>` bit-encoding tables, `<decode>` blocks, `<execute>` blocks, and shared pseudocode (`shared_pseudocode.xml`). `mra_tools` extracts these into ASLv0 via two Python scripts:

- **Register extraction (`bin/reg2asl.py`, blob `238501b36cd1bebb0e4bd462fc25d3eb20dea0d3`, lines `115-248`)**:
  Parses `<reg_fieldset>` and `<field>` tags to emit `__register bits(width) { hi:lo field_name, ... } reg_name;` declarations (`Decl_RegDefn` in `asl.ott:268`). Named bit-fields within architectural system registers (such as `PSTATE`, `SCTLR_EL1`, `FPCR`) are accessed using field syntax (`SCTLR_EL1.M`), which `asl-interpreter` elaborates into bit-slice reads and writes (`LExpr_BitTuple` / `LExpr_Slices`).
- **Instruction and decode-tree extraction (`bin/instrs2asl.py`, blob `e89baa62a8356d3ac8bbc604c43d8a2e873bcb5e`, lines `110-245`, `480-590`)**:
  - `read_regdiagram` (`instrs2asl.py:110-189`) inspects `<box>` elements in each `<regdiagram>`. Fixed `'0'`/`'1'` bits become opcode mask characters (`'0'`, `'1'`, `'x'`). Crucially, constrained "should-be-zero" `(0)` and "should-be-one" `(1)` bits in the XML diagram are Relaxed to `'x'` in the `__opcode` mask and emitted as explicit `__unpredictable_unless <bit_index> == '<0|1>';` guards (`instrs2asl.py:157-180`).
  - Each instruction XML page is emitted as an `__instruction` block (`Decl_InstructionDefn` in `asl.ott:295-307`) containing one or more `__encoding` blocks (`Encoding_Block(id, arch, fields, opcode, guard, unpreds, decode_stmts, loc)`), a `__postdecode` block, and an `__execute` (or `__conditional __execute`) block.
  - Decode hierarchy XML files (`encodingindex.xml`) are translated into a tree of `__decode` case blocks (`DecoderCase_Case(slices, alts, loc)` in `asl.ott:310-325`) that pattern-match on bit-slices (`DecoderSlice_Slice(lo, wd)` or concatenated named fields `DecoderSlice_FieldName`) and dispatch to `__encoding` identifiers or `__field` sub-decoders.

#### 1.2 ASLv0 Type System, Dependent Bitvectors, and Unification (`rems-project/asl-interpreter`)

In `asl-interpreter/libASL/asl.ott` (blob `844b6b210d97c3fae8bd8478d7778a8fdf6f5c61`, lines `82-119`), types include:
- `Type_Integer` (unbounded mathematical integer $\mathbb{Z}$),
- `Type_Bits(expr)` (bitvector `bits(E)` parameterized by an arbitrary AST expression `E`),
- `Type_Register(int, (slices * ident) list)` (`__register bits(N) { ... }`),
- `Type_Array(ixtype, ty)` (`array [0..N] of T` or enum-indexed arrays), and
- `Type_Tuple(ty list)`.

`libASL/tcheck.ml` (blob `fab728a7e8a1ceeb17a4a73a5b2648367a4d10bb`) type-checks ASLv0 as follows:
- **Polymorphic type-variable inference via syntactic unification (`tcheck.ml:811-955`)**:
  Functions and getters/setters that mention `bits(N)` in their parameter or return types have `N` implicitly bound as a polymorphic integer parameter (`tenv#addTypeVar`). At each call site (`instantiate_Rule`, `tcheck.ml:900-955`), `unifier` matches actual argument widths against formal parameter widths to synthesize explicit type arguments `tes : expr list` injected into `Expr_TApply(fn, tes, args)` and `Stmt_TCall(proc, tes, args, loc)`.
- **Algebraic normalization + external Z3 constraint checking (`tcheck.ml:715-790`)**:
  Before invoking Z3 (`check_constraints`, `tcheck.ml:761-790`), `simplify_ValidationExpr` (`tcheck.ml:715-755`) rewrites integer expressions into canonical linear forms. At lines `725-727` and `743-754`, the implementation includes an explicit warning:
  ```ocaml
  (* Warning: the following rule is unsound for arbitrary integers,
   * (e.g., (x DIV 8) * 8 == x is only true when x is a multiple of 8)
   * across Arm's ASL code, it is always valid.
   *)
  ```
  Specifically, `simplify_ValidationExpr` unconditionally rewrites `(a DIV b) * b` to `a` (`tcheck.ml:745-754`) so that bitvector width equalities such as `bits(( datasize DIV 8 ) * 8) == bits(datasize)` unify syntactically without requiring divisibility preconditions in Z3. In a theorem prover with dependent `BitVec n` types such as Lean 4, `(datasize / 8) * 8 = datasize` is *not* definitionally true and is provably false unless `8 ∣ datasize`, creating a major proof obligation at every byte-loop and element-lane boundary.

#### 1.3 Polymorphic Getters/Setters and the `Formal_InOut` By-Value Bug in `asl-interpreter`

ASLv0 supports overloaded array-like getters (`Decl_ArrayGetterDefn`, `asl.ott:285`) and setters (`Decl_ArraySetterDefn`, `asl.ott:286`). Setters can declare formal parameters as either by-value `Formal_In(ty, id)` or by-reference `Formal_InOut(ty, id)` (`&id` in surface syntax, `asl.ott:258-260`). For example, `asl-interpreter/prelude.asl:68-77` defines vector element access:
```asl
bits(size) Elem[bits(N) vector, integer e, integer size]
    assert e >= 0 && (e+1)*size <= N;
    return vector[e*size +: size];

Elem[bits(N) &vector, integer e, integer size] = bits(size) value
    assert e >= 0 && (e+1)*size <= N;
    vector[e*size +: size] = value;
    return;
```

During type-checking (`tc_lexpr2` in `libASL/tcheck.ml:1588-1676`), an assignment LHS `A[i]` is resolved in two different ways depending on context:
1. If `A[i]` is the top-level LHS of an assignment (`X[n] = v` or `Elem[V[n], e, 64] = v`), `tc_lexpr2` (`tcheck.ml:1653-1676`) emits `LExpr_Write(setter_fn, tes, args)` where `args` are type-checked as *r-expressions* (`expr list`) via `tc_exprs`.
2. If `A[i]` appears *inside* a nested bit-slice or field assignment (`X[n][31:0] = v`), `tc_slice_lexpr` (`tcheck.ml:1540-1565`) requires the inner l-expression to be checked in mode `"read-write"`, producing `LExpr_Slices(LExpr_ReadWrite(getter_fn, setter_fn, tes, args), slices)`.

In `asl-interpreter/libASL/eval.ml` (blob `7995d8fb07d115aacc87b6e1c77f645ae4500fb3`):
- For `LExpr_ReadWrite(getter, setter, tes, args)` (`eval.ml:603-631`), `eval_lexpr` reads the current value via `eval_funcall loc env getter tvargs vargs`, mutates the slice on that value, and then calls `eval_proccall loc env setter (tvargs @ vargs @ [v])`.
- However, for `LExpr_Write(setter, tes, args)` (`eval.ml:595-601`), `eval_lexpr` evaluates all `args` by value into `vargs : Value.value list` and calls `eval_proccall loc env setter (tvargs @ vargs @ [v])`. Inside `eval_proccall` (`eval.ml:972-981`), both `Formal_In(ty, x)` and `Formal_InOut(ty, x)` are bound via `Env.addLocalVar loc lenv x v` to a fresh local variable in the callee's local scope `lenv`. When `Elem.write` mutates `vector[e*size +: size] = value` and returns, `lenv` is discarded and the caller's argument (e.g., `V[n]` in `Elem[V[n], e, 64] = rhs`) is **never updated**. We mechanize this contrast in Section 2 of `support/asl_l3_to_lean_bridge_probe.lean` (`eval_Elem_write_by_value` vs. `asl_to_sail_Elem_write` and theorem `asl_interpreter_by_value_bug_loses_write`).

#### 1.4 ASLv1 Cleanup in `herd/herdtools7/asllib`

Arm's standardized ASLv1 implementation in `herd/herdtools7/asllib` fixes these ASLv0 design hazards directly in the language specification and AST:
- **Static integer constraint categories (`asllib/AST.mli`, blob `3056e85602506bb546f32103d94d8959fd8832ec`, lines `255-273`, and `asllib/Typing.ml`, blob `482dbe3e3f5e5249bd4530c55b5af206de661b6e`, lines `1-600`)**:
  Every integer type `T_Int(constraint_kind)` is classified as `UnConstrained`, `WellConstrained(int_constraint list, precision_loss_flag)` (where each `int_constraint` is `Constraint_Exact of expr` or `Constraint_Range of expr * expr`), `PendingConstrained`, or `Parameterized of identifier`. Bitvector widths `T_Bits(e, bitfields)` and array lengths `T_Array(ArrayLength_Expr e, ty)` are required by `Typing.ml:568-573` and `Interpreter.ml:696-700` to be statically constrained or evaluable via `StaticInterpreter`.
- **Elimination of `Formal_InOut` and RMW desugaring (`asllib/desugar.ml`, blob `4516f9c55d4ef7823b380d6634b03d7275d92510`, lines `126-162`, `212-248`)**:
  ASLv1 removes `&` reference setter parameters completely. Accessors are declared as paired `accessor_pair` blocks (`desugar.ml:212-248`) generating a getter `F_Getter` and a setter `F_Setter` whose signature takes `(setter_arg, ty) :: args`. When a setter appears on the LHS of a sub-slice or field write (`Setter(args)[slices] = rhs`), `desugar_setter` (`desugar.ml:126-162`) lowers it into an explicit 3-step `read_modify_write` block using a fresh temporary variable `__setter_v1_temporary`:
  ```ocaml
  (* asllib/desugar.ml:144-161 *)
  let read = S_Decl (LDK_Var, LDI_Var temp, Some rhs_ty, Some getter_call) |> add_pos in
  let modify = S_Assign (temp_lexpr, rhs) |> add_pos in
  let write = S_Call { name; args = E_Var temp :: args; params; call_type = ST_Setter } |> add_pos in
  S_Seq (S_Seq (read, modify) |> add_pos, write)
  ```
- **Explicit loop/recursion limits (`asllib/Interpreter.ml`, blob `2c51eeb8a9fc158e6fffc066f113067697840bc9`, lines `261-275`, `1171-1212`, `1280-1349`)**:
  ASLv1 adds optional `limit` expressions to `S_While(cond, limit, body)`, `S_Repeat(body, cond, limit)`, and `func.recurse_limit`. `Interpreter.ml` evaluates `limit` via `eval_limit` (`lines 1171-1186`) and decrements it on every iteration (`check_limit`, raising `LoopLimitReached` or `RecursionLimitReached` if exhausted), providing a built-in fuel bound for total functional translation.

---

### 2. The `asl_to_sail` Translation Pipeline (`rems-project/asl_to_sail`)

Basis: `direct-inspection` of `rems-project/asl_to_sail` (`lib/translate_asl.ml`, `lib/sail_to_sail.ml`, `bin/main.ml`, `prelude.sail`)

`rems-project/asl_to_sail` bridges ASLv0 (`libASL`) to Sail (`libsail`). Inspecting `lib/translate_asl.ml` (blob `aa7638f2406d164308d283b92a41a6bb33215af0`, 3,347 lines), `lib/sail_to_sail.ml` (blob `f19ffcf5745ad3514634d1abcbf51cf8a608864b`, 1,009 lines), and `bin/main.ml` (blob `df6b64a5229c38779f47206dbb141a2568c6e824`, 1,124 lines) reveals five core translation passes and why automatic translation requires Z3 constraint repair plus human patch overrides:

1. **`Formal_InOut` Setter Reference Elimination (`lib/translate_asl.ml:1762-1784, 3082-3117`)**:
   - When translating `Decl_ArraySetterDefn(id, args, vty, v, body, loc)` (`translate_asl.ml:3082-3117`), `asl_to_sail` partitions `args` into `Formal_In` and `Formal_InOut` parameters (`inout_arg_Highlight`).
   - If `Formal_InOut` parameters `[(ty₁, x₁); ...; (tyₖ, xₖ)]` are present (as in `Elem.write` where `&vector` is `Formal_InOut`), the generated Sail setter function is given return type `ty₁` (or `Type_Tuple [ty₁; ...; tyₖ]`) instead of `unit`, and `returnStmtClass` rewrites every `Stmt_ProcReturn` in `body` to `Stmt_FunReturn(ret_exp)` returning the mutated `xᵢ` variables (`translate_asl.ml:3092-3103`).
   - At setter call sites (`sail_of_setter_assignment` in `translate_asl.ml:1762-1784`), `asl_to_sail` queries `Ctx.SetterInOutArgs` to split the call arguments into input expressions `in_args` and in-out expressions `inout_args`, converts each `inout_arg` into a Sail l-expression via `lexpr_of_expr` (`translate_asl.ml:1770-1778`), and emits `LE_tuple(lexps) = setter(in_args, rhs)` (e.g., `V[n] = Elem_set(V[n], e, size, rhs)`).

2. **Slice Read-Modify-Write Lowering on Getters/Setters (`lib/translate_asl.ml:2038-2065`)**:
   - When an assignment LHS slices the result of a getter/setter pair (`LExpr_Slices(LExpr_ReadWrite(read, write, tes, args), [slice])`), `translate_asl.ml:2038-2065` synthesizes a read call `E_app(read, args)`, updates the slice via `sail_slice_update_exp` (`SetSlice(width, total_width, read(args), lo, rhs)` or `vector_update_subrange`), and feeds that updated expression as the new RHS into `sail_of_setter_assignment`.

3. **SVE/SME Runtime Vector Length (`VL`/`PL`) Hoisting and Monomorphization (`lib/translate_asl.ml:257-342, 2900-2910` and `prelude.sail:319-325`)**:
   - In ASLv0, SVE and SME instructions compute bitvector widths from runtime state reads `VL = CurrentVL.read()` (`VL IN {128, 256, 512, 1024, 2048}`) and `PL = VL DIV 8`. In Sail (and Lean 4), a mutable register read cannot appear directly inside a type `bits(CurrentVL)`.
   - `vlExprsClass` (`translate_asl.ml:257-342`) scans function and instruction bodies for reads of `CurrentVL`, `VL`, and `PL`, hoisting them to the top of the body as `let 'VL = CurrentVL` where `CurrentVL` is typed in `prelude.sail:319-325` with an existential refinement:
     ```sail
     type is_VL('vl : Int) -> Bool = ('vl in {128, 256, 512, 1024, 2048})
     val GetCurrentVL : unit -> {'vl, is_VL('vl). int('vl)}
     ```
   - Alternatively, when `-mono_vl` is enabled (`translate_asl.ml:2900-2910`), `sail_of_encoding` wraps the entire execute block in a `Stmt_Case` split over every concrete `VL` in `ctx.tc_env.vl_values` (`128`, `256`, `512`, `1024`, `2048`), duplicating and specializing the instruction body for each fixed width.

4. **3-Pass Fixed-Point Decode Constraint Inference (`lib/translate_asl.ml:482-513, 1038-1194, 3149-3179`)**:
   - `sliceVarsClass` (`translate_asl.ml:482-513`) identifies all local variables that appear in bit-slice widths `Slice_LoWd(lo, wd)` or `Type_Bits(n)`.
   - `intConstraintsClass` (`translate_asl.ml:1038-1194`) performs abstract interpretation over decode statements (`Stmt_VarDeclsNoInit`, `Stmt_Assign`, `Stmt_If`, `Stmt_Case`, `Stmt_Assert`), tracking integer domains `int_constraint = IC_Unknown | IC_Set of Big_int.num list | IC_Range of Big_int.num * Big_int.num | IC_Var of ident`. For example, `esize = 8 << UInt(size)` where `size : bits(2)` is inferred as `IC_Set [8; 16; 32; 64]`.
   - `infer_int_constraints` (`translate_asl.ml:3149-3179`) runs `intConstraintsClass` in a 3-iteration fixed-point loop (`for _ = 1 to 3 do ...`) and annotates constrained decode variables with existential Sail types `{'n, 'n in {8, 16, 32, 64}. int('n)}`.

5. **50-Iteration Z3 Type-Check Feedback Loop and Manual Patch Escape Hatch (`bin/main.ml:731-829`, `lib/sail_to_sail.ml:844-925`)**:
   - Even after `intConstraintsClass`, Sail's dependent type-checker fails on many translated ASL functions because interprocedural bitwidth preconditions are missing from function signatures.
   - `iterate_check` (`bin/main.ml:731-770`) runs up to `max_iters = 50` rounds of `Libsail.Type_check.check`. Whenever Sail raises `Err_unresolved_quants` or `Err_failed_constraint`, `Sail_to_sail.rewrite_add_constraint` (`sail_to_sail.ml:844-925`) parses the failed Z3 obligation and either strengthens the function's `val` type signature or injects an `assert(constraint)` into the function body.
   - Where `iterate_check` still fails (or where ASL idioms cannot be automatically typed in Sail), `bin/main.ml:780-829` loads human-written override files (`-patch` `.sail` and `.val.sail` files) that replace specific generated functions and type signatures outright.

---

### 3. L3 Language & Compiler Architecture (`coruus/L3`)

Basis: `mixed` (`direct-inspection` of `coruus/L3` + `empirical-probe` in `support/asl_l3_to_lean_bridge_probe.lean`)

Anthony Fox's L3 (`coruus/L3`, commit `d6558e679a25ffaaf16a47a3189f8f8111e45e0c`) is an architecture description language implemented in ~10,000 lines of Standard ML (`L3/Base.sml`, `L3/Matches.sml`, `L3/Eval.sml`, `L3/Export.sml`, `L3/HolExport.sml`, `L3/SMLExport.sml`) that powers the Cambridge/SRI Armv7, Armv8 (`isa-models/arm-v8/`), MIPS (`isa-models/mips/`), and x86-64 (`isa-models/x86-64/`) formal models.

#### 3.1 Closed Non-Dependent AST and Finite Bitwidth Polymorphism (`L3/Base.sml`)

In `L3/Base.sml` (blob `908963866de7a3a2b44dce28a4d36df6209ceba0`):
- **Types (`Type.bty`, lines `329-429`, paired with `Constrain.constraints`, lines `263-318`)**:
  ```sml
  datatype bty =
     VarType of string
   | ConstType of string
   | BV of int
   | BVV of string
   | ParamType of pty * bty
   | Prod of bty * bty
   | Arrow of bty * bty
  ```
  Unlike ASL and Sail, bitvector widths are **never** arbitrary value expressions. A bitvector type is either a concrete positive integer `BV(n)` (`bits(64)`) or a bit-width variable `BVV("N")` (`bits(N)`) constrained by a finite `PosIntSet.pintset` in `Constrain.constraints`. For example, in `isa-models/arm-v8/v8-base.spec:240-255`:
  ```l3
  bits(N) X (reg n) with N in 32, 64 = if n == 31 then 0 else REG(n)<N-1:0>
  ```
  During specialization and export (`Expand.expandDefns` in `L3/Export.sml:435-610`), functions with constrained `BVV` variables are monomorphized over the finite integer set (`X'32`, `X'64`), eliminating dependent bitwidth proofs entirely.
- **Terms (`Term.value` and `Term.term`, lines `1602-1620`)**:
  Every L3 expression after parsing and type-checking is represented by the 5-constructor algebraic datatype `Term.term`:
  ```sml
  datatype term =
     Lit of value
   | Var of string * Type.ty
   | BVar of int * Type.ty
   | Comb of string * Type.ty * term list
   | Abs of (string * Type.ty) list * Type.ty * term
  ```

#### 3.2 Bit-String Pattern Matching Compilation (`L3/Matches.sml` and `L3/Export.sml`)

L3 specifications write instruction decoders using bit-string concatenation patterns (`Comb(":", _, [p1, p2])`), such as `case 'sf op S 100010 sh imm12 Rn Rd'` in `isa-models/arm-v8/v8-iset.spec:2408` or `'Rw 1 imm`24'` in `L3/examples/tiny.spec:159`. L3 compiles these patterns in three verified stages:

1. **Static Exhaustiveness and Irredundancy Verification (`Term.checkMatch` in `L3/Base.sml:3198-3278`)**:
   Before code generation, `checkMatch` checks every `match` expression over bitvectors, booleans, enums, and tuples to verify that all bit combinations are covered and reports any unreachable/redundant pattern arms.
2. **Bit-Pattern Boolification (`Matches.boolifyMatches` in `L3/Matches.sml:435-483`, blob `c8fbf5e55e5e79b1a85195c655479606c397b529`)**:
   - `mkBoolify` (`Matches.sml:371-379`) applies `boolify'N` to convert an $N$-bit scrutinee `x :: bits(N)` into an $N$-tuple of `bool`s `(b_{N-1}, ..., b_0)`.
   - `boolify1` (`Matches.sml:392-423`) traverses each bit-concatenation pattern `p1 : p2`: fixed literal bits `'0'`/`'1'` become boolean patterns `false`/`true`, wildcard bits `'_` become fresh wildcard variables, and a $k$-bit pattern variable `imm` (`Var("imm", BV k)`) is expanded into $k$ boolean variables `imm'k-1, ..., imm'0` wrapped in a `let imm = [..] [imm'k-1, ..., imm'0] in body` binding that reconstructs the $k$-bit vector on the arm's RHS.
3. **Balanced Boolean Decision Tree Synthesis (`Convert.boolMatchConv` in `L3/Export.sml:1213-1323`, blob `bd762d5a0f3aa98eb8f85dfef592af7629953f35`)**:
   - Given a multi-arm match on an $N$-tuple of booleans, `bestSplit` (`Export.sml:1213-1249`) selects the tuple column $i$ with the fewest wildcards across remaining rows and partitions the pattern matrix into `true` and `false` sub-matrices, emitting a nested `i-t-e` (`if b_i then tree_true else tree_false`) decision tree.

#### 3.3 Exception Lowering and State-Monad Beta-Reduction (`L3/Export.sml:36-74, 682-1121`)

L3's imperative features (mutable global registers/memory declared in `declare { ... }`, local mutable variables `var v = e`, `for` / `foreach` loops, and architectural exceptions `exception UNDEFINED_FAULT`) are lowered into pure functional code by `L3/Export.sml` in four passes:

1. **Exception State-Field Synthesis (`Exception.buildExceptionDatatype` and `Exception.removeExceptionCalls`, `Export.sml:36-74`)**:
   - `buildExceptionDatatype` (`Export.sml:36-54`) collects all declared exceptions into a single inductive datatype `datatype exception = NoException | UNDEFINED_FAULT | ...`, adds a mutable global field `exception :: exception` to the architectural state, and synthesizes:
     ```l3
     unit raise'exception (e :: exception) = when exception == NoException do exception <- e
     ```
   - `removeExceptionCalls` (`Export.sml:59-74`) rewrites every `#Exn(arg)` expression of expected type `ty` into `(raise'exception (Exn(arg)); UNKNOWN :: ty)`.
2. **Global State Record Synthesis (`Monad.defineStateType`, `Export.sml:682-712`)**:
   - Collects all mutable globals in `Env.listVariables()` (including `PC`, `REG`, `SP_EL0`, `MEM`, `PSTATE`, and `exception`) into a single flat record type `state`.
3. **Monadic Combinator Lowering (`Monadify.monadifyDefn`, `Export.sml:843-1013`)**:
   - Imperative statements and expressions are rewritten into state-monad combinators (`Export.sml:198-334`):
     - `m'const : 'a -> ('state -> 'a * 'state)`
     - `m'bind : ('state -> 'a * 'state) -> ('a -> 'state -> 'b * 'state) -> ('state -> 'b * 'state)`
     - `m'read : ('state -> 'a) -> ('state -> 'a * 'state)`
     - `m'write : ('state -> 'state) -> ('state -> unit * 'state)`
     - `m'extend` and `m'unextend` (`Export.sml:308-324, 810-820`): for local mutable variables (`var v = init; body`), L3 temporarily extends the state type from `'state` to `'v * 'state`, runs `body` on the extended state tuple, and projects back to `'state` via `Snd` on exit.
4. **De-Monadification via Beta-Reduction (`Monadify.deMonadifyDefn`, `Export.sml:1026-1121`)**:
   - Rather than leaving monadic `bind` combinators in the exported theorem-prover definitions, `deMonadifyDefn` unfolds `m'const`, `m'bind`, `m'read`, `m'write`, `m'extend`, and `m'unextend` into explicit `let (v, state') = ... in ...` state-passing expressions (`state -> val * state`).
   - `HolExport.sml` (`HOLconv`, blob `3ffcae2d32c7152d242a73fe46af4e5a46fb7878`, lines `505-676`) then pretty-prints these pure definitions directly into HOL4 (`Define` / `tDefine` with explicit termination `measure` from `L3/examples/tiny.spec:219` or `isa-models/arm-v8/v8-base.spec:302`).

---

### 4. Trade-Off Matrix: Direct ASL-to-Lean 4 vs. ASL-to-Sail-to-Lean 4 vs. L3-to-Lean 4

Basis: `mixed` (`direct-inspection` of `asl-interpreter`, `herdtools7/asllib`, `asl_to_sail`, `sail`, and `L3` + `empirical-probe` in `support/asl_l3_to_lean_bridge_probe.lean`)

| Dimension | Direct ASL-to-Lean 4 (from `mra_tools` / `asllib`) | ASL-to-Sail-to-Lean 4 (`asl_to_sail` + `sail -lean`) | L3-to-Lean 4 (`coruus/L3` AST / `Export.sml`) |
| :--- | :--- | :--- | :--- |
| **Bitvector Type System & Width Proofs** | **High friction (ASLv0) / Moderate (ASLv1)**: ASLv0 `bits(E)` requires dependent `BitVec E` casts and proves `(a / b) * b = a` via Z3 (`tcheck.ml:745-754`). ASLv1 `WellConstrained` (`AST.mli:255-273`) bounds widths statically, but slice updates still require arithmetic cast obligations in Lean 4. | **Moderate friction**: `asl_to_sail` infers `IC_Set`/`IC_Range` (`translate_asl.ml:1038-1194`) and runs 50 Z3 repair rounds (`main.ml:731-770`), emitting existential Sail types translated by `sail -lean` into dependent `BitVec` terms with `sail_assert` calls. | **Zero dependent-width friction**: `Type.bty` (`Base.sml:329-429`) restricts bitwidths to concrete `BV(n)` or finite-set `BVV("N")` (`with N in 8, 16, 32, 64`) monomorphized by `Expand.expandDefns` (`Export.sml:435-610`). Every Lean type is a concrete `BitVec n`. |
| **Execution Monad & Kernel `rfl` Reduction** | **Moderate**: Requires either a fuel-bounded state+exception interpreter (`asllib/Interpreter.ml`) or a custom monadic lowering pass for `See` / `Undefined` / `Unpredictable` exceptions. | **High friction for `rfl`**: `sail -lean` (`pretty_print_lean.ml`) lowers effectful functions into `PreSailM RegisterType trivialChoiceSource exception` (`StateT σ (ExceptT ε Id)`), requiring monad-unfolding lemmas (`runSailPure`) before kernel `rfl` or `simp` can reduce a step. | **Ideal for `rfl`**: `Monadify.deMonadifyDefn` (`Export.sml:1026-1121`) beta-reduces all monad combinators away and folds exceptions into `state.exception`, emitting flat `L3State → α × L3State` functions that reduce by kernel `rfl` in Lean 4 without monad unfolding. |
| **Getter/Setter & Reference (`&`) Lowering** | **Must adopt ASLv1 `desugar_setter`**: Direct translation of ASLv0 `LExpr_Write` must not copy `asl-interpreter/libASL/eval.ml:595-601` (which loses `Formal_InOut` writes); it must implement `asllib/desugar.ml:126-162` (`read_modify_write` temporary) or indexed lenses. | **Handled by `asl_to_sail`**: `translate_asl.ml:1762-1784, 3082-3117` converts `Formal_InOut` parameters into tuple return values and expands slice writes via `SetSlice`. | **Native in L3**: L3 component references (`REG(n)<31:0> <- v` or `X(n) <- v`, `v8-base.spec:240-255`) are compiled directly by `Monadify` (`Export.sml:885-960`) into record functional updates. |
| **`CONSTRAINED UNPREDICTABLE` vs. `UNDEFINED`** | **Explicit `ConstrainUnpredictable(which)`**: Returns a `Constraint` enum (`Constraint_UNDEF`, `Constraint_NOP`, `Constraint_WBSUPPRESS`, `Constraint_UNKNOWN`). Easily parameterized by a verification profile to exclude `Constraint_UNDEF` when proving user-mode safety. | **Partially flattened**: `asl_to_sail` translates `ConstrainUnpredictable` via `prelude.sail` choice hooks; in `sail -lean`, `trivialChoiceSource` determinizes nondeterministic choices unless replaced by a relational/nondeterministic monad. | **Encoded via `UNKNOWN :: bits(k)` case splits**: In `v8-iset.spec:1178-1196`, `match UNKNOWN ("LoadImmediate unpredictable") :: bits(2)` hardcodes `case 2 => Unallocated` (`#UNDEFINED_FAULT`), which collapses Anneal's demonic `BehaviorOf.defined` to `False` unless filtered. |
| **Loops & Recursion Termination** | **Fuel / `limit` annotations**: ASLv1 includes explicit `limit` clauses (`Interpreter.ml:1171-1212`); ASLv0 `while`/`repeat` loops require fuel or manual termination measures. | **Monadic loop combinators**: `sail -lean` emits `foreachM` / `whileM` combinators (with `sorry` or fuel for general `whileM`). | **Bounded `for` + `measure` recursion**: L3 uses bounded `for i in a .. b` (`m'for`) and explicit `measure` annotations (`HolExport.sml:505-509`), mapping cleanly to structural recursion or `WellFounded.fix` in Lean 4. |
| **ISA Coverage & Maintenance** | **Full Armv8-A / Armv9-A coverage** (including SVE/SME, system registers, and page tables) directly from Arm's official MRA XML releases. | **Broad Armv8.5-A / Armv9-A coverage** via `sail-arm`, but depends on a 3-stage pipeline (`mra_tools` → `asl_to_sail` + 50 Z3 iterations + manual `.sail` patches → `sail -lean`). | **Clean user-mode AArch64 base coverage** (`isa-models/arm-v8/v8-base.spec` + `v8-iset.spec`, ~2,430 lines total for integer, branch, system, and CRC32 instructions; FP/SIMD stubbed at `v8-iset.spec:2329-2365`). |

---

### 5. Anneal Integration & Mechanized Lean 4.34.1 Bridge Probe (`support/asl_l3_to_lean_bridge_probe.lean`)

Basis: `empirical-probe` (`support/asl_l3_to_lean_bridge_probe.lean`, SHA-256 `a09e8257b28bb006c1f198d46e91860a2e127d009e64a7d57010cd79edce106e`, 1,161 lines, verified with Lean 4.34.1 `-j1 -M768`)

To validate these findings against Anneal's actual semantic types (`Preorder`, `Partial`, `StepResult`, `PrefixOutcome`, `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`, and `BridgeTransition` from `trusted/lean/Trusted/Refinement.lean` and `trusted/lean/Trusted/StepResult.lean`), we constructed `support/asl_l3_to_lean_bridge_probe.lean`.

#### 5.1 Mechanization (a): ASL Getter/Setter Lenses and `CONSTRAINED UNPREDICTABLE` in Anneal

1. **Lawful Indexed Lenses and `Formal_InOut` Lowering (`lines 198-406`)**:
   - We define `AslIndexedLens S ι α` and `LawfulIndexedLens` (`get_set_same` and `get_set_other`), and instantiate them on `AslState` for:
     - `X_get64` / `X_set64` (`lines 222-265`): proving `X_get64_set64_same_non_zr` (`n.val < 31 → X_get64 (X_set64 s n v) n = v`), `X_get64_zr` (`X_get64 s 31 = 0#64`), `X_set64_zr_noop` (`X_set64 s 31 v = s`), and `X_get64_set64_other` (`i ≠ j → X_get64 (X_set64 s i v) j = X_get64 s j`).
     - `V_lens : AslIndexedLens AslState (Fin 32) (BitVec 128)` (`lines 268-278`, theorem `V_lens_lawful`).
     - `Elem64_lens : AslIndexedLens (BitVec 128) (Fin 2) (BitVec 64)` (`lines 283-348`, theorem `Elem64_lens_lawful`), modeling `Elem[bits(N) &vector, integer e, integer size] = bits(size) value` (`asl-interpreter/prelude.asl:68-77`).
   - We then model all three implementations of `Elem[V[n], e, 64] = rhs`:
     - `eval_Elem_write_by_value` (`lines 352-355`, modeling `asl-interpreter/libASL/eval.ml:595-601, 972-981`),
     - `asl_to_sail_Elem_write` (`lines 358-359`, modeling `asl_to_sail/lib/translate_asl.ml:1762-1784, 3082-3117`), and
     - `asllib_desugar_rmw` (`lines 362-365`, modeling `herdtools7/asllib/desugar.ml:126-162`).
   - We prove:
     - `asl_to_sail_eq_asllib_rmw` (`lines 369-371`): `asl_to_sail_Elem_write s n e rhs = asllib_desugar_rmw s n e rhs := rfl`.
     - `asl_to_sail_Elem_roundtrip` (`lines 374-378`), `asl_to_sail_Elem_frame_lane` (`lines 381-387`), and `asl_to_sail_Elem_frame_reg` (`lines 390-394`).
     - `asl_interpreter_by_value_bug_loses_write` (`lines 398-408`): proves that for `rhs = Elem64_lens.get (V_lens.get s n) e + 1#64`, `eval_Elem_write_by_value` fails to update `V[n]` and disagrees with `asl_to_sail_Elem_write`.

2. **`CONSTRAINED UNPREDICTABLE` vs. `UNDEFINED` in Anneal's `BehaviorOf` (`lines 414-539`)**:
   - We model `AslConstraint` (`UNPREDICTABLE | UNDEF | NOP | WBSUPPRESS | UNKNOWN (val : BitVec 64)`) and `ConstrainedLdrMachine` (`lines 433-435`) for post-indexed `LDR Xt, [Xn], #imm` with overlapping registers (`n == t && n != 31`), mapping `ConstrainUnpredictable` to `StepResult.choice ChoiceKind.demonic`.
   - **Theorem `constrained_unpred_with_undef_not_defined` (`lines 449-461`) & Corollary `l3_load_imm_unpred_not_defined` (`lines 466-471`)**:
     Proves that whenever `AslConstraint.UNDEF ∈ allowed`—including L3's exact 4-way list `l3LoadImmUnpredAllowed unkVal = [.WBSUPPRESS, .UNKNOWN unkVal, .UNDEF, .NOP]` from `isa-models/arm-v8/v8-iset.spec:1178-1196`—the machine reaches `.failed .ub` in 1 step via `ReachesFromResult.demonic`, so `¬ (BehaviorOf (ConstrainedLdrMachine ...) ()).defined ⟨s, 1⟩`.
   - **Theorem `constrained_unpred_nonfaulting_is_defined` (`lines 483-501`) & Corollary `nonFaultingLoadImm_defined_and_reaches_all` (`lines 505-531`)**:
     Proves that when `allowed` is restricted to `IsNonFaultingConstraint` (`nonFaultingLoadImmAllowed unkVal = [.WBSUPPRESS, .UNKNOWN unkVal, .NOP]`), `(BehaviorOf M ()).defined ⟨s, 1⟩` holds and all three permitted architectural post-states are reachable in 1 step.

#### 5.2 Mechanization (b): L3-to-Lean 4 Prototype and `SmallStepMachine` / `BridgeTransition`

In Section 3 of `support/asl_l3_to_lean_bridge_probe.lean` (`lines 534-1120`), we translate a representative AArch64 fragment from `isa-models/arm-v8/v8-base.spec` and `v8-iset.spec` (`AddSubImmediate`, `LoadStoreImmediate64`, `BranchRegisterRet`, `Unallocated`) directly into Lean 4 following L3's `Matches.sml` and `Export.sml` pipeline:
- **Total Bit-Slice Decode/Encode and Roundtrip Theorem (`lines 539-725`)**:
  `decodeA64 : BitVec 32 → L3Instr` extracts instruction fields via `BitVec.extractLsb'`, `encodeA64 : L3Instr → Option (BitVec 32)` concatenates the bitfields, and `decodeA64_encodeA64_roundtrip` (`lines 708-725`) proves `∀ instr w, encodeA64 instr = some w → decodeA64 w = instr`.
- **Lowered State-Exception Record and `BridgeTransition` (`lines 731-983`)**:
  `L3State` (`lines 738-746`) embeds `exception : L3Exception` (`NoException | UNDEFINED_FAULT | ALIGNMENT_FAULT`) directly into the state record as synthesized by `Exception.buildExceptionDatatype` (`L3/Export.sml:36-54`). `L3Bridge : BridgeTransition CodeMem L3State` (`lines 979-982`) packages `L3Machine` with mechanized proofs of `TotalStep` (`l3Machine_total`, using the total fuel evaluator `runSteps_sound`) and `InhabitedDemonic` (`l3Machine_inhabited`).
- **Concrete 4-Instruction AArch64 Trace Execution by Kernel `rfl` and `BehaviorOf` Refinement (`lines 988-1120`)**:
  - `decode_insn_add_x0_x1_42`, `decode_insn_str_x0_sp_0`, `decode_insn_ldr_x2_sp_0`, and `decode_insn_ret_x30` (`lines 994-1004`) verify by `rfl` that the 32-bit machine words `0x9100A820`, `0xF90003E0`, `0xF94003E2`, and `0xD65F03C0` decode to `ADD X0, X1, #42`, `STR X0, [SP, #0]`, `LDR X2, [SP, #0]`, and `RET X30`.
  - `testProg_four_step_rfl` (`lines 1072-1081`) executes all 4 instructions from `testInitState` (`X1 = 100`, `SP = 0x8000`, `X30 = 0x2000`) by kernel `rfl`, confirming termination with `.returned`, `PC = 0x2000`, `X0 = 142`, `X2 = 142`, and `exception = .NoException`.
  - `testProg_refines_spec` (`lines 1098-1113`) proves `BehaviorOf L3Bridge.machine testProg ≤ testProgSpec` in Anneal's `Partial (ExecQuery L3State) (ExecOut L3State)` preorder.

---

## Boundaries

1. **Scope of the L3 Armv8 Specification (`coruus/L3/isa-models/arm-v8/`)**:
   The upstream L3 Armv8 model (`v8-base.spec` and `v8-iset.spec`) models user-space and basic system AArch64 instructions (integer arithmetic/logical, branches, loads/stores, system register moves, and CRC32), while floating-point and SIMD instructions are stubbed out as `NoOperation` in `v8-iset.spec:2329-2365`. Consequently, L3's Compilation Strategy (finite `BVV` monomorphization + boolified decision-tree decode + `deMonadifyDefn` state-exception record) is an ideal architectural blueprint for Anneal's Lean 4 ISA backend, whereas full Armv9-A / SVE / SME instruction coverage must still be sourced from Arm's MRA XML / ASLv1 definitions (`herdtools7/asllib` or `mra_tools`).
2. **User-Mode Exception-as-UB Modeling**:
   In `support/asl_l3_to_lean_bridge_probe.lean`, architectural faults (`Error_Undefined` / `UNDEFINED_FAULT` and `ALIGNMENT_FAULT`) are mapped to `StepResult.failed .ub` in `l3Step` (`lines 891-908`), matching Anneal's user-mode verification contract where taking an unexpected synchronous exception is treated as a specification failure. Modeling EL1 exception vector entry would instead transition `PC` to `VBAR_EL1 + offset` via `StepResult.next`.

---

## Evidence

All claims in this report are grounded in:

1. **Mechanized Lean 4.34.1 Artifact (`support/asl_l3_to_lean_bridge_probe.lean`)**:
   - Path: `reports/asl-l3-and-architecture-dsl-to-lean-translation-strategies/support/asl_l3_to_lean_bridge_probe.lean`
   - SHA-256: `a09e8257b28bb006c1f198d46e91860a2e127d009e64a7d57010cd79edce106e` (47,818 bytes, 1,161 lines)
   - Verified with `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768` (exit code 0, zero warnings, zero `sorryAx`, and `#guard_msgs in #print axioms` checks at lines `1126-1160` confirming dependencies are restricted to standard Lean axioms `[propext, Quot.sound]` and `Classical.choice`).
2. **Primary Source Manifest (`support/source-manifest.json`)**:
   - Records exact git commit SHAs, tree SHAs, git blob SHA-1s, and file SHA-256 digests for all 30 inspected source files across `anneal`, `asl-interpreter`, `mra_tools`, `asl_to_sail`, `herdtools7`, `L3`, and `sail`.

---

## Revalidation

To revalidate the mechanized Lean 4.34.1 bridge probe from a clean checkout of the `reference` branch:

```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M768 \
  reports/asl-l3-and-architecture-dsl-to-lean-translation-strategies/support/asl_l3_to_lean_bridge_probe.lean
```

The command must exit with status `0` and produce no output (all `#guard_msgs in #print axioms` assertions are checked during elaboration).

*Authored by an AI agent acting on joshlf's behalf.*
