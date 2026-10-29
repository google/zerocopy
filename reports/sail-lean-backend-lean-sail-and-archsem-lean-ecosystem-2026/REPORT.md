# Sail Lean Backend, `lean-sail`, and the ArchSem Lean Ecosystem (2026)

## Summary

This report analyzes the architecture, recent evolution, and soundness boundaries of the Sail-to-Lean 4 compilation and concurrency-modeling stack across `rems-project/sail` (`0f51056900af85d0b18928d6ea2d2271d18184e8`, 2026-10-29), `rems-project/lean-sail` (`1e5b216bf881ef08da160db63b44ecda430802d6`, tag `v8`, 2026-10-27), `rems-project/archsem-lean` (`318583a5f2052c039c25dfd69a3beec0b0a27090`, 2026-06-29), `rems-project/archsem` (`42204d87df2e7d20e5ec23deb8ba8220e65148ab`, 2026-10-29), and `rems-project/sail-tiny-arm-lean` (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`, 2026-10-25), and establishes how these components interface with Anneal's (`joshlf/anneal-private` at `42f4571d761b46c7142815f38b69c3781b3555e3`) Layer 1A (`Behavior`, `WellFormed`), Layer 1B (`StepResult`, `ChoiceKind`, `ReachesPrefix`, `BehaviorOf`), `Trusted.Memory`, and `TrustedBoundary` kernel audit.

Key conclusions:

1. **Critical October 2026 Sail Lean Backend Fixes & Features (`7e0e53d18` → `0f5105690`):**
   - Commit `f7a1fedbce8b762935e60e6b45c0f28b89656344` fixed a critical silent miscompilation in `Rewrites.rewrite_var_updates` (`src/lib/rewrites.ml:2888-2900`): because `lean_rewrites` (`src/sail_lean_backend/sail_plugin_lean.ml:176-244`) omits the `letbind_effects` pass used by the Coq/Lem backends, tuple assignments lowered into `E_let` expressions previously dropped variable updates inside `E_let` bodies (causing Arm's `ADD` instruction to write an undefined result).
   - Commit `e55d89e79e3e5dfa88a137c73be371fb3671c983` fixed eager lifting of effectful right-hand sides in `&&` and `||` (`src/sail_lean_backend/pretty_print_lean.ml:1036-1040`), emitting Lean's monadic short-circuit operators `<&&>` and `<||>` so untaken branches do not trigger assertions, exceptions, or register/memory effects.
   - Commit `2ae2199f8890180a8f9653f6ea08e54cd9790220` added dependent existential type support (`src/lib/deptype_targets.ml` and `src/sail_lean_backend/pretty_print_lean.ml:331-347, 528-540, 688-693, 903-928`), lowering Sail existential types `{'n, P('n). T('n)}` to Lean dependent Sigma types `(Σ n, T n)` when `'n` appears in `T`, synthesizing dependent pair witnesses `⟨c, d⟩` in patterns and function/constructor arguments, and bumping `lib_default_rev` from `"v7"` to `"v8"`.
   - Commit `0f51056900af85d0b18928d6ea2d2271d18184e8` added the `rewrite_if_eq` pass (`src/lib/rewrites.ml:562-655`, `src/sail_lean_backend/sail_plugin_lean.ml:182`), rewriting `if lhs == rhs then ...` into pattern matches when `--lean-non-beq-type` disables `deriving BEq` on large inductive types (such as ISA ASTs).

2. **Soundness Gaps in `lean-sail`'s `ArchSemSequential` (`Sail/ArchSemSequential.lean`):**
   - `Sail.ArchSem.Sequential.interpretSailEffects` (`Sail/ArchSemSequential.lean:83-90`) interprets the V2 freer monad `PreSailM ue ty` into a deterministic `EStateM (Sail.Error ue) (SequentialState Arch.register_type) ty` by hardcoding every bounded nondeterministic choice `.inr choice` (`FinChoice`) to index `⟨0, h⟩ : Fin choice` (`line 88`). Consequently, `undefined_bit`, `undefined_bool`, `undefined_bitvector`, `undefined_range`, and `internal_pick` always evaluate only branch `0`, masking any assertion failure or undefined behavior on branches `1 .. choice - 1`.
   - `Sail.ArchSem.Sequential.interpretEffect` (`Sail/ArchSemSequential.lean:51-81`) silently evaluates `.memWriteAnnounce`, `.barrier`, `.archException`, `.cacheOp`, `.tlbOp`, `.translationStart`, `.translationEnd`, and `.returnException` to `pure ()` (`lines 64, 70, 74-79`). If a Sail specification signals an architectural fault via `sail_take_exception` without manually aborting the surrounding computation via `SailME.throw`, `ArchSemSequential` treats the exception as a no-op and continues executing subsequent side effects.
   - Even in `Sail.ArchSem` (`Sail/ArchSem.lean:288-289, 344-349`), `undefined_vector n a` deterministically returns `Pure.pure <| Vector.replicate n a` without emitting a `FinChoice` effect, and `sail_sys_reg_read` / `sail_sys_reg_write` discard `_id : Arch.sys_reg_id` and delegate to `readRegRef` / `writeRegRef` with `accessType := Option.none`.

3. **Comparison of `archsem-lean` (Lean 4) vs. `archsem` (Rocq) and Bridge to Anneal:**
   - `rems-project/archsem-lean` (`318583a5f2052c039c25dfd69a3beec0b0a27090`) implements the V2 freer monad trace relation (`ArchSem/Trace.lean`), `ListSet`-backed nondeterministic state monad `NEStateM` (`ArchSem/NondeterministicMonad.lean`), `ComputationalTerminatingModel` with `weaker`/`wider`/`equivalent` refinement (`ArchSem/TerminatingModel.lean`), axiomatic candidate executions (`ArchSem/CandidateExecution.lean`), and TinyArm sequential, sequential-axiomatic, and user-mode promising (`runNaive` and `runPromiseFirst`) models with fuel-monotonicity proofs (`ArchSemTinyArm/PromisingFirstProof.lean`).
   - However, `archsem-lean` currently covers only 8-byte aligned user-mode TinyArm (plus 4-byte unmodified `ifetch`) and rejects atomic RMWs (`ArchSemTinyArm/Promising.lean:327, 387`). By contrast, `rems-project/archsem` in Rocq (`42204d87df2e7d20e5ec23deb8ba8220e65148ab`) supports mixed-size byte-accurate `GenPromising` and `UMPromising` (with atomic RMWs and store-exclusive `xcl_view` forwarding), full EL10 virtual-memory `VMPromising` (2,809 lines, with 4-level page-table walks, TLB entries, `relaxed_regs` TTBRs, break-before-make checks, thread enumeration caching `#306`, and epoch-based TLBI commutation filtering `#307`), a mechanized Phase 1 equivalence theorem `VMUM_phase1` (`ArchSemArm/VMUMEquivThm.v:400`), RISC-V RVWMO (`ArchSemRiscV/UMAxRiscV.v`), and x86-TSO (`ArchSemX86/OperationalX86TSO.v`).
   - Anneal must **not** use `ArchSemSequential` or `--lean-partial-function` in its trusted specification pipeline: `TrustedBoundary.lean` rejects `partial` definitions both syntactically (`Parser.Command.partial` at `line 149`) and in the kernel environment (`ci.isPartial` at `lines 595, 664, 747`). Instead, Anneal should consume the `CONCURRENCY_INTERFACE_V2` freer monad `PreSailM` (`FreeM ((Except (Sail.Error ue) InstructionEffect) ⊕ FinChoice)`) and interpret it directly into `StepResult` (`Trusted/StepResult.lean`) and `Trusted.Memory` (`Trusted/Memory.lean`), mapping `FinChoice` and `visibleAtomicMsgs` to `StepResult.choice .demonic` and mapping Sail errors/assertions/exceptions to `StepResult.failed .ub`. This bridge is mechanized and proven sound with zero `sorry` and zero custom axioms in [`support/sail_archsem_lean_bridge_probe.lean`](support/sail_archsem_lean_bridge_probe.lean).

---

## Applicability

This report applies to:

- **`joshlf/anneal-private`** (`42f4571d761b46c7142815f38b69c3781b3555e3`):
  - `trusted/lean/Trusted/Refinement.lean` (`Preorder`, `Partial`, `Behavior`, `Language`, `WellFormed`)
  - `trusted/lean/Trusted/StepResult.lean` (`ChoiceKind`, `FailureKind`, `StepResult`, `PrefixOutcome`, `ReachesPrefix`, `SmallStepMachine`, `BehaviorOf`)
  - `trusted/lean/Trusted/Memory.lean` (`Timestamp`, `View`, `AccessOrder`, `AtomicMsg`, `MemState`, `visibleAtomicMsgs`, `applyAtomicLoad`, `appendAtomicMsg`)
  - `trusted/audit/TrustedBoundary.lean` (`inspectSyntax`, `audit`, `downstreamAudit`, `verifyCrateAudit`)
- **`rems-project/sail`** (`0f51056900af85d0b18928d6ea2d2271d18184e8`, compared against `7e0e53d183cad75b8f36bfbbecc0ef75614a8418`):
  - `src/sail_lean_backend/sail_plugin_lean.ml`, `src/sail_lean_backend/pretty_print_lean.ml`
  - `src/sail_lean_backend/Sail/SpecializationArchSem.lean`, `src/sail_lean_backend/Sail/SpecializationV1.lean`, `src/sail_lean_backend/Sail/FakeReal.lean`, `src/sail_lean_backend/Sail/Real.lean`
  - `src/lib/deptype_targets.ml`, `src/lib/rewrites.ml`, `src/lib/type_check.ml`, `src/lib/externs.json`, `src/rocq/lib/Monad.v`, `test/suites/lean.py`
- **`rems-project/lean-sail`** (`main` at `1e5b216bf881ef08da160db63b44ecda430802d6` / tag `v8`, tag `v7` at `01bb54c7c8a69e52ba11863c67e7c403a6cd198a`, and `archsem-lean` branch at `be17410bd7969c130e7dcee237d56abef572feeb`):
  - `Sail/ArchSem.lean`, `Sail/ArchSemSequential.lean`, `Sail/ConcurrencyInterfaceV1.lean`, `Sail/Sail.lean`, `Sail/Common.lean`, `Sail/BitVec.lean`, `Sail/IntRange.lean`, `Sail/Attr.lean`
- **`rems-project/archsem-lean`** (`318583a5f2052c039c25dfd69a3beec0b0a27090`):
  - `ArchSem/Defs.lean`, `ArchSem/Trace.lean`, `ArchSem/NondeterministicMonad.lean`, `ArchSem/ListSet.lean`, `ArchSem/TerminatingModel.lean`, `ArchSem/CandidateExecution.lean`, `ArchSemTinyArm/Defs.lean`, `ArchSemTinyArm/Sequential.lean`, `ArchSemTinyArm/SequentialAxiomatic.lean`, `ArchSemTinyArm/Promising.lean`, `ArchSemTinyArm/PromisingFirstProof.lean`
- **`rems-project/archsem`** (`42204d87df2e7d20e5ec23deb8ba8220e65148ab`):
  - `ArchSem/Interface.v`, `ArchSem/FromSail.v`, `ArchSem/SeqModel.v`, `ArchSem/GenPromising.v`, `ArchSem/TermModels.v`, `ArchSem/CandidateExecutions.v`, `ArchSem/ISAManip.v`, `ArchSemArm/UMPromising.v`, `ArchSemArm/VMPromising.v`, `ArchSemArm/VMUMEquivThm.v`, `ArchSemRiscV/UMAxRiscV.v`, `ArchSemX86/OperationalX86TSO.v`
- **`rems-project/sail-tiny-arm-lean`** (`4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`)

---

## Findings

### 1. `rems-project/sail` Lean Backend Architecture & October 2026 Evolution (`7e0e53d18` → `0f5105690`)

#### 1.1 Commit-by-Commit Audit (`7e0e53d183cad75b8f36bfbbecc0ef75614a8418` to `0f51056900af85d0b18928d6ea2d2271d18184e8`)

| Commit SHA | Date | Files Modified | Technical Impact |
|---|---|---|---|
| `f7a1fedbce8b762935e60e6b45c0f28b89656344` | 2026-10-10 (merged 2026-10-16) | `src/lib/rewrites.ml` (`lines 2888-2900`), `test/lean/let_var.sail` | **Critical bugfix in `rewrite_var_updates`:** `rewrite_tuple_assignments` rewrites `(a, b) = e` into an `E_let` whose body updates `a` and `b`. Because `lean_rewrites` omits `("letbind_effects", [])`, variable updates inside `E_let` bodies were previously dropped by `rewrite_var_updates`, miscompiling Arm's `ADD` instruction to write an undefined value. Adds an explicit `E_let (lpat, bind, body) when updates_vars body && not (updates_vars bind)` clause that returns updated mutable variables from the `E_let` as a tuple. |
| `48c271e1ae812f0f7f6f8016cce52ef06fedbfd2` | 2026-10-14 | `src/lib/type_check.ml`, `src/lib/util.ml` | Stores integer bounds `[a, b]` in the typing environment (`Env.prove_by_bounds` at `type_check.ml:455`) and discharges linear inequality obligations before invoking external Z3 SMT queries. |
| `9a6b307658ce6fd77788937d192185746cac2d9e` | 2026-10-16 | `src/lib/type_check.ml` | Checks global constraint bounds for inconsistency during `prove_by_bounds` so dead branches under inconsistent global constraints discharge cleanly. |
| `e49821011450d2c26dad90e8806fc82d9698b627` | 2026-10-16 | `src/sail_lean_backend/pretty_print_lean.ml` (`line 425`) | Wraps negative/rational `L_real` literals in parentheses `(r : Real)` so method calls and binary operators do not misparse in Lean 4. |
| `9f4f5853d9063404652eb276a7ea2c6881096310` | 2026-10-16 | `test/c/for_shadow.sail`, `test/lean/loop.expected.lean` | Updates `for_shadow` regression test for Lean loop lowering. |
| `e55d89e79e3e5dfa88a137c73be371fb3671c983` | 2026-10-19 | `src/sail_lean_backend/pretty_print_lean.ml` (`lines 1036-1040`) | **Critical short-circuiting fix for `&&` / `||` with effectful `rhs`:** Previously, `and_bool` / `or_bool` treated `rhs` as a normal effectful argument, lifting `← rhs` prior to evaluating `lhs`. Now emits Lean's monadic short-circuit operators `lhs <&&> (do rhs)` and `lhs <||> (do rhs)` (lifting `pure lhs` if `lhs` is pure), preserving short-circuiting of assertions, memory accesses, and exceptions. |
| `9c10b069e1db217aa4d1e14664e9ccb76b6e6ad0` | 2026-10-20 | `src/sail_lean_backend/pretty_print_lean.ml` (`lines 1475-1479`) | Sets `in_sail_monad = has_effect exp` when pretty-printing top-level `Def_let (LB_aux (LB_val (pat, exp), _))` and wraps effectful top-level `let` bindings in `unwrapValue (do ...)`. |
| `ed68849777f5c1c5c9f0bf9f27480a0acca1e34a` | 2026-10-21 | `src/sail_lean_backend/pretty_print_lean.ml` (`lines 307, 953-956, 1169`), `src/lib/externs.json` | Maps `string_literal` to `String` (`line 307`); qualifies enum constructors as `EnumType.Ctor` when shadowed by a type of the same name (`lines 953-956`); fixes `E_try` catch block typing to use `mk_tannot env exc_typ` (`line 1169`). |
| `dea849055e636ac8cbf2a7bd3755313aafcdd3da` | 2026-10-22 | `src/lib/type_check.ml` (`lines 659-685`) | Improves `unify_nexp` for `Nexp_sum` and `Nexp_minus`: when unifying `n1a + n1b` with `n2a + n2b` (or `n1a - n1b` with `n2a - n2b`), if `prove env (nc_eq n1b n2b)` holds, directly unifies `n1a` with `n2a` instead of synthesizing nested subtraction terms. |
| `2ae2199f8890180a8f9653f6ea2d2271d18184e8` (`2ae2199f8`) | 2026-10-27 | `src/lib/deptype_targets.ml`, `src/sail_lean_backend/sail_plugin_lean.ml` (`line 119`), `src/sail_lean_backend/pretty_print_lean.ml` (`lines 331-347, 528-540, 579-586, 625-635, 688-693, 903-928`), `test/suites/lean.py` | **Dependent existential type support in Lean backend & `lean-sail` bump to `v8`:** Extracts `Deptype_targets` from the Coq backend; lowers `Typ_exist` with relevant type variables into Lean Sigma types `(Σ k_1 ... k_n, inner)`; lowers existential patterns to `⟨k_1, ..., k_n, inner⟩`; and synthesizes dependent pair witnesses in `d_of_arg_with_typ` via `Type_check.unify`. |
| `f8b40b198c25d9b73bb001ad8ae92ca85ebdf22d` | 2026-10-28 | `src/rocq/lib/Monad.v`, `src/lib/partial_eval.ml`, `src/sail_lean_backend/*.ml` | Introduces a shared Rocq `Monad.v` for partial evaluation (`ZAst.v`) and regular execution (`Semantics.v`), and normalizes AST constructors (`DEF_aux` → `Def_aux`, `DEC_aux` → `Reg_aux`). |
| `0f51056900af85d0b18928d6ea2d2271d18184e8` | 2026-10-29 | `src/lib/rewrites.ml` (`lines 562-655, 4933`), `src/sail_lean_backend/sail_plugin_lean.ml` (`line 182`) | **Adds `rewrite_if_eq` pass:** When `--lean-non-beq-type <Type>` omits `BEq` on a type, rewrites `if lhs == rhs then e1 else e2` (where `==` is `eq_anything` on a non-`BEq` type or a container thereof, and one side is pattern-convertible via `pat_of_exp`, including unfolding top-level `Def_let` constants) into `match lhs with | pat => e1 | _ => e2`. |

#### 1.2 The 41-Stage `lean_rewrites` Pipeline (`src/sail_lean_backend/sail_plugin_lean.ml:176-244`)

When `sail --lean` runs, it applies the following 41-stage rewrite sequence before invoking `Pretty_print_lean.pp_ast_lean`:

1. `move_termination_measures` (`line 177`): Attaches `termination_measure` declarations directly to recursive function clauses.
2. `instantiate_outcomes [String_arg "lean"]` (`line 178`): Instantiates generic outcome declarations (`CONCURRENCY_INTERFACE_V1` or `CONCURRENCY_INTERFACE_V2`) for the `"lean"` target.
3. `realize_mappings` (`line 179`): Expands bidirectional mappings into forward/backward functions.
4. `remove_vector_subrange_pats` (`line 180`), `remove_duplicate_valspecs` (`line 181`).
5. `if_eq` (`line 182`, added 2026-10-29): Converts equality comparisons on `--lean-non-beq-type` types into `match` expressions.
6. `toplevel_string_append` (`line 183`), `pat_string_append` (`line 184`), `mapping_patterns` (`line 185`), `add_unspecified_rec` (`line 186`).
7. `undefined [Bool_arg true]` (`line 187`): Synthesizes `undefined_<type>` functions for types when `--Instantiation_of_undefined` is active.
8. `vector_string_pats_to_bit_list` (`line 188`), `remove_not_pats` (`line 189`), `remove_impossible_int_cases` (`line 190`), `tuple_assignments` (`line 191`), `vector_concat_assignments` (`line 192`), `simple_assignments` (`line 193`).
9. `remove_vector_concat` (`line 194`), `remove_bitvector_pats` (`line 195`): Replaces bitvector concatenation patterns with boolean guards and slice extractions (`extractLsb` / `access`, as seen in `SailTinyArmUser/TinyArm.lean:57-538`).
10. `remove_numeral_pats` (`line 196`), `pattern_literals [Literal_arg "lem"]` (`line 197`), `guarded_pats` (`line 198`), `register_ref_writes` (`line 199`), `nexp_ids` (`line 200`).
11. `split` (`line 201`), `minimise_recursive_functions` (`line 202`).
12. `recheck_defs` (`line 203`).
13. `remove_assert` (`line 204`): Rewrites internal `E_assert` AST nodes into explicit calls to `sail_assert`.
14. `top_sort_defs` (`line 205`), `const_prop_mutrec [String_arg "coq"]` (`line 206`), `exp_lift_assign` (`line 207`).
15. `early_return` (`line 208`): Marks functions containing early `return` statements (`Early_return.has_early_return`) so the Lean printer wraps them in `ExceptM.run` (pure) or `SailME.run` (effectful).
16. `merge_function_clauses` (`line 209`), `recheck_defs` (`line 210`), `rewrite_explicit_measure` (`line 211`), `rewrite_loops_with_escape_effect` (`line 212`), `recheck_defs` (`line 213`).
17. `infer_effects [Bool_arg true]` (`line 214`), `attach_effects` (`line 215`), `remove_blocks` (`line 216`), `attach_effects` (`line 217`).
18. **`argument_effects`** (`line 233`) & **`rewrite_var_updates`** (`line 235`): Rather than running `letbind_effects` (which is commented out at `line 232`), the Lean backend lifts effectful subexpressions out of function/operator arguments into sequential `E_let` bindings (`argument_effects`) and then converts mutable local variable assignments inside `E_if` and `E_let` branches into functional tuple-threading (`rewrite_var_updates`).
19. `attach_effects` (`line 234, 236`), `remove_superfluous_letbinds` (`line 237`), `remove_superfluous_returns` (`line 238`), `bit_lists_to_lits` (`line 239`), `toplevel_let_patterns` (`line 240`), `recheck_defs` (`line 241`), `attach_effects` (`line 242`).

#### 1.3 Lowering of Types, Control Flow, Monads, and Termination (`src/sail_lean_backend/pretty_print_lean.ml`)

- **Types (`doc_sail_typ`, `lines 269-348`):**
  - `int` → `Int`, `nat` → `Nat`, `unit` → `Unit`, `bool` → `Bool`, `bit` → `(BitVec 1)`, `string` / `string_literal` → `String`, `real` → `Real`.
  - Bounded `range(lo, hi)` and `atom(n)` → `Int` (`lines 296-297`) — note that range constraints are erased to `Int` unless wrapped in a `Typ_exist` whose witness is relevant!
  - `bitvector(n)` / `bits(n)` → `(BitVec n)` (`line 299`); `vector(n, T)` → `(Vector T n)` (`line 301`); `list(T)` → `(List T)` (`line 303`); `register(T)` → `(RegisterRef T)` (`line 298`).
  - `Typ_exist (kids, _, typ)` (`lines 331-347`): Computes `relevant = Deptype_targets.relevant_existential_vars typ` and filters `kids` to `kids_to_print` that appear in `Type_check.tyvars_of_typ typ`. If non-empty, emits `(Σ k_1 ... k_m, inner)`; if empty (e.g., `{('n : Int), 'n >= 0. int('n)}` after `int('n)` erases to `Int`), erases the existential wrapper!
- **Control Flow & Loops (`lines 783-788, 868-895, 971-1040, 1265-1282`):**
  - Pure functions without loops or early return emit a direct expression body `: T := ...`.
  - Pure functions with `while`/`until`/`foreach` loops emit `: T := Id.run do ...` (`lines 784, 1268`).
  - Pure functions with early return emit `: T := ExceptM.run do ...` (`lines 783, 1267`).
  - Effectful functions without early return emit `: SailM T := do ...` (`lines 786, 1270`).
  - Effectful functions with early return emit `: SailM T := SailME.run do ...` (`lines 785, 1269`).
  - `while#` / `until#` without a fuel measure emit Lean `let mut loop_vars := ...; while ... do ...` (`lines 868-874, 888-895`), which Lean's elaborator compiles via `Lean.Loop.forIn` (an opaque `partial` combinator!).
  - `while#t` / `until#t` with a fuel expression emit `whileFuelM` / `untilFuelM` (`lines 875-887`, defined by structural recursion on `Nat` in `Sail/Sail.lean:45-61`).
  - `foreach#` emits `for i in [from:to:step]i do` (`lines 971-1031`), using `IntRange` (`Sail/IntRange.lean`), which reduces structurally on `Nat` size.
- **Termination & `partial def` (`lines 1283-1337`):**
  - `doc_termination` (`lines 1321-1337`) emits `termination_by (exp).toNat` **only** when a Sail `termination_measure` (`Rec_measure (pat, exp)`) is attached to the function. Simultaneously, `Sail/Sail.lean:133-136` extends `macro_rules | \`(tactic| decreasing_trivial) => \`(tactic| first | grind | decide)`.
  - If a recursive Sail function has no `termination_measure` (and Lean cannot infer structural recursion), compilation fails unless `--lean-partial-function <fn>` (or an unmeasured `while` loop) is used, which emits `partial def` (`line 1284`).
  - **Impact on Anneal:** Anneal's `TrustedBoundary.lean` rejects `partial` definitions both syntactically (`Parser.Command.partial` in `inspectSyntax`, `trusted/audit/TrustedBoundary.lean:149`) and in the kernel environment (`ci.isPartial` in `audit`/`downstreamAudit`/`verifyCrateAudit`, `trusted/audit/TrustedBoundary.lean:595, 664, 747`). Furthermore, in Lean 4's kernel, any `partial def` (or function using `while ... do` via `Lean.Loop.forIn`) is compiled as an opaque constant with no equation theorems, blocking kernel reduction and symbolic proof unfolding. Therefore, every Sail function imported into Anneal's trusted boundary must use structural recursion, bounded `foreach`, or `while#t`/`until#t` (`whileFuelM`/`untilFuelM`) with explicit `termination_measure`s, and `--lean-partial-function` must never be used on trusted specifications.

---

### 2. `rems-project/lean-sail`: Concurrency Interfaces V1 vs. V2 and `ArchSemSequential` Soundness

#### 2.1 Evolution from `be17410bd` (`archsem-lean` branch) and `v7` (`01bb54c7c`) to `v8` (`1e5b216bf`)

- **`archsem-lean` branch (`be17410bd7969c130e7dcee237d56abef572feeb`, 2026-06-19):** Introduced `Sail/ArchSem.lean` (`CONCURRENCY_INTERFACE_V2`) with the `Effect` typeclass, freer monad `FreeM`, `InstructionEffect`, and separated `FinChoice`. Contained a typo `.returnExecption` (`Sail/ArchSem.lean:188`), lacked `Sail/ArchSemSequential.lean` and `Sail/IntRange.lean`, and targeted `leanprover/lean4:v4.29.0-rc2`.
- **`v7` (`01bb54c7c8a69e52ba11863c67e7c403a6cd198a`, 2026-10-12):** Merged `ArchSem.lean` into `main`, added `Sail/ArchSemSequential.lean` and `Sail/IntRange.lean`, fixed `.returnException` (`Sail/ArchSem.lean:191`), added `Sail.Error.InfiniteNondeterminisim` (`Sail/Common.lean:20`) for `undefined_int`/`undefined_nat`/`undefined_string`, and upgraded to `leanprover/lean4:v4.29.0`.
- **`v8` (`1e5b216bf881ef08da160db63b44ecda430802d6`, 2026-10-27):** Added `Sail.BitVec.updateSubrange'` (`Sail/BitVec.lean:69-73`) with flexible `Nat`/`Int` width conversions via `ToNat` (`Sail/Sail.lean:63-91`) to support dependent existential bitvector widths emitted by `sail` commit `2ae2199f8890180a8f9653f6ea08e54cd9790220`.

#### 2.2 V1 (`Sail/ConcurrencyInterfaceV1.lean`) vs. V2 (`Sail/ArchSem.lean`)

When `sail --lean` runs, `sail_plugin_lean.ml:326` checks whether `CONCURRENCY_INTERFACE_V2` is present in the Sail environment:

| Aspect | V1 (`Sail.ConcurrencyInterfaceV1`) | V2 (`Sail.ArchSem`) |
|---|---|---|
| Activation in `sail` | Default when `CONCURRENCY_INTERFACE_V2` is absent (`interface_v = 1`) | Activated when Sail library `concurrency_interface/v2.sail` defines `CONCURRENCY_INTERFACE_V2` (`interface_v = 2`) |
| Specialization template | `src/sail_lean_backend/Sail/SpecializationV1.lean` | `src/sail_lean_backend/Sail/SpecializationArchSem.lean` |
| Underlying monad | Stateful `EStateM (Error ue) (SequentialState RegType ChoiceSource)` (`ConcurrencyInterfaceV1.lean:273-274`) | Purely syntactic freer monad `PreSailM ue := FreeM ((Except (Sail.Error ue) InstructionEffect) ⊕ FinChoice)` (`ArchSem.lean:212-213`) |
| Early-return monad | `PreSailME := ExceptT exception PreSailM` | `PreSailME ue exception := FreeM (Except exception ((Except (Sail.Error ue) InstructionEffect) ⊕ FinChoice))` (`ArchSem.lean:219-220`) |
| Nondeterminism | Deterministic PRNG `ChoiceSource` threaded in `SequentialState.choiceState` (`ConcurrencyInterfaceV1.lean:245-261`) | Explicit uninterpreted `FinChoice` (`Nat`, returning `Fin n`) in the right summand of `PreSailM` (`ArchSem.lean:69-72, 273-274`) |
| Trace / axiomatic / promising inspection | **Impossible** — register/memory operations directly mutate `SequentialState` inside `EStateM` | **Supported** — `FreeM` is an inductive syntax tree of `InstructionEffect` and `FinChoice` calls |

#### 2.3 Four Concrete Soundness Hazards in `Sail.ArchSem` and `Sail.ArchSemSequential`

1. **Deterministic `FinChoice := 0` in `ArchSemSequential` (`Sail/ArchSemSequential.lean:87-89`):**
   ```lean
   def interpretSailEffects : PreSailM ue ty → ArchSemSeqM ue ty :=
     FreeM.liftM (fun
       | .inl (.error err) => throw err
       | .inl (.ok eff) => interpretEffect eff
       | .inr choice =>
         if h : 0 < choice then
           pure (⟨0, h⟩ : Fin choice)
         else
           throw .Unreachable)
   ```
   Every call to `undefined_bit`, `undefined_bool`, `undefined_range`, `undefined_bitvector`, or `internal_pick` emits `.impure (.inr n) k`. Under `ArchSemSequential`, only branch `0` is ever executed! For example, `SailTinyArmUser.Functions.initialize_registers` (`SailTinyArmUser.lean:51-86`) initializes every register via `← undefined_bitvector 64`, which `ArchSemSequential` silently collapses to `0#64`. Worse, if an instruction specification uses `undefined_*` or `internal_pick` to model `CONSTRAINED UNPREDICTABLE` or `UNDEFINED` bits and asserts or faults on non-zero branches, `ArchSemSequential` reports unconditional success (`Theorem archSemSeq_unsound_for_demonic_undefined` in [`support/sail_archsem_lean_bridge_probe.lean`](support/sail_archsem_lean_bridge_probe.lean)).
2. **Eight Silently Ignored Effects in `ArchSemSequential` (`Sail/ArchSemSequential.lean:64, 70, 74-79`):**
   ```lean
   | .memWriteAnnounce _ => pure ()
   | .barrier _ => pure ()
   | .archException _
   | .cacheOp _
   | .tlbOp _
   | .translationStart _
   | .translationEnd _
   | .returnException => pure ()
   ```
   Because `.archException` and `.returnException` evaluate to `pure ()` with return type `Unit`, any Sail model that signals a fault via `sail_take_exception fault` without also throwing a monadic exception continues executing the remainder of the instruction in `ArchSemSequential` (`Theorem archSemSeq_unsound_for_silent_exception` in [`support/sail_archsem_lean_bridge_probe.lean`](support/sail_archsem_lean_bridge_probe.lean)). By contrast, both `archsem-lean` (`ArchSemTinyArm/Sequential.lean:73-80`) and `archsem` (`ArchSem/SeqModel.v:149`) reject `TakeException` as an error.
3. **`undefined_vector` Omits `FinChoice` (`Sail/ArchSem.lean:288-289`):**
   Even inside `Sail/ArchSem.lean`, `undefined_vector (n : Nat) (a : α) : PreSailM ue (Vector α n)` is defined as `Pure.pure <| Vector.replicate n a`, bypassing `FinChoice` entirely and hardcoding the default witness `a` passed by the Sail compiler.
4. **System Register Identifier Erasure (`Sail/ArchSem.lean:344-349`):**
   ```lean
   def sail_sys_reg_read [Arch] (_id : Arch.sys_reg_id) (r : RegisterRef α) : PreSailM ue α :=
     readRegRef r
   def sail_sys_reg_write [Arch] (_id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : PreSailM ue Unit :=
     writeRegRef r v
   ```
   `sail_sys_reg_read` and `sail_sys_reg_write` ignore `_id : Arch.sys_reg_id` and call `readRegRef` / `writeRegRef`, which emit `.regRead reg Option.none` and `.regWrite reg Option.none v` (`ArchSem.lean:294-301`). Thus, the `Option Arch.sys_reg_id` access-kind field on `.regRead` and `.regWrite` is always `none` when called through `sail_sys_reg_read` / `sail_sys_reg_write`.

---

### 3. `rems-project/archsem-lean` vs. `rems-project/archsem` (Rocq)

#### 3.1 Architecture of `archsem-lean` (`318583a5f2052c039c25dfd69a3beec0b0a27090`)

`archsem-lean` is structured into two libraries:

1. **Architecture-Generic Core (`ArchSem/`):**
   - `ArchSem/Defs.lean`: Extends `Sail.ArchSem.Arch` with `ArchExtra` (providing `Ord`/`TransCmp`/`LawfulEqCmp` for `Std.ExtTreeMap`/`Std.ExtDTreeMap` register and memory maps, `Hashable`, and `register_pc`) and defines `RegisterMap`, `MemoryMap` (byte-indexed `Std.ExtTreeMap (BitVec addr_size) (BitVec 8)`), `ArchState nThreads`, and `TerminationCondition nThreads`.
   - `ArchSem/NondeterministicMonad.lean`: Defines `NExcept ε α` (`oks : ListSet α`, `errors : ListSet ε`) and `NEStateM ε σ α := σ → NExcept ε (σ × α)`, with `choose`, `chooseFin`, `discard`, and monotonicity lemmas (`bind_mono`, `bind_app_congr`) used in fuel-stabilization proofs.
   - `ArchSem/TerminatingModel.lean`: Defines `ModelResult nThreads Flag termCond` (`.finalState`, `.flagged`, `.error`), `TerminatingModel` (set-valued in `Prop`), and `ComputationalTerminatingModel` (`ListSet`-valued), together with `weaker`, `wider`, and `equivalent` refinement relations (`lines 91-125`).
   - `ArchSem/Trace.lean`: Defines `Effect.Event Eff := Sigma Effect.ret`, `FreeM.Trace Eff α` (`List (Event Eff) × TraceEnd Eff α`), and the inductive trace-matching relation `FreeM.traces` (`lines 52-57`), plus `PreSailM.deterministicTraces` (`lines 90-99`), which resolves `FinChoice` nondeterminism while preserving `InstructionEffect` events.
   - `ArchSem/CandidateExecution.lean` (1,170 lines): Formalizes `Eid` (`tid`, `iid`, `ieid`), `PreCand nThreads`, `Cand nThreads` (`memReadsFrom`, `regReadsFrom`, `coherence`, `exclusives`), decidable well-formedness (`Cand.wf` at `lines 1102-1127`), and derived dependency/ordering relations (`programOrder`, `addr`, `data`, `ctrl`, `atomicUpdate`).
2. **TinyArm Instantiation (`ArchSemTinyArm/`):**
   - `ArchSemTinyArm/Sequential.lean`: Interprets `SailM Unit` into `NEStateM String SequentialState Unit`, branching over `FinChoice` via `NEStateM.chooseFin` (`line 87`).
   - `ArchSemTinyArm/SequentialAxiomatic.lean`: Defines a decidable sequential axiomatic model (`consistent` and `not_ub`, `lines 56-106`).
   - `ArchSemTinyArm/Promising.lean` (837 lines): Ports user-mode promising semantics (without mixed-size accesses; all explicit accesses must be 8-byte aligned `Loc := BitVec 61`, and `ifetch` must be 4-byte aligned from unmodified `InitialMem`). Implements both `runNaive` (`lines 744-755`, interleaving promise and instruction steps) and `runPromiseFirst` (`lines 761-796`, enumerating certified promises per thread first).
   - `ArchSemTinyArm/PromisingFirstProof.lean` (368 lines): Proves fuel monotonicity and eventual stabilization of `runToTermination` and `enumerateResults`, culminating in `naive_promising_monotonic_fuel_full` (`lines 340-352`) and `promise_first_monotonic_fuel_full` (`lines 354-366`), which prove `(createPromiseFirstModel isem fuel).weaker (createPromiseFirstModel isem fuel')` for all `fuel' ≥ fuel`.

#### 3.2 Feature & Verification Gap Matrix: `archsem` (Rocq) vs. `archsem-lean` (Lean 4)

| Capability | `rems-project/archsem` (Rocq, `42204d87d`) | `rems-project/archsem-lean` (Lean 4, `318583a5f`) |
|---|---|---|
| **Generic Promising Framework** | `ArchSem/GenPromising.v` (`Promising.Model` record supporting arbitrary `mEvent`, `mEvent_affects` thread-cache reuse `#306`, `filter_promises` `#307`, `tState_min_new_prom_view` early stopping, and `check_valid_end`) | Hardcoded for TinyArm in `ArchSemTinyArm/Promising.lean`; no generic `GenPromising` abstraction, no `enum_cache` reuse, and no `min_new_prom_view` early stopping |
| **Mixed-Size Memory Accesses** | Supported in `GenPromising.v:175-265` (`read_from_aux`, `read_all_aux` with per-byte timestamps and `Msg.overlap`) and `UMPromising.v:297-357` (per-byte `fwdb` and `coh`) | **Unsupported:** `ArchSemTinyArm/Promising.lean:34, 485-534` restricts explicit reads/writes to 8-byte aligned `Loc := BitVec 61` (and 4-byte `ifetch`) |
| **Atomic RMW & Exclusive Forwarding** | Supported in `UMPromising.v:98-103, 331-333, 383-418` (`IIS.rmw_read`, `FwdItem.xcl_view` implementing `[R];rmw;rfi;[A\|Q]` in `aob`) | Atomic RMW rejected with `"Atomic RMW unsupported"` (`Promising.lean:327, 387`); `readFwdView` (`line 318`) uses `f.time` instead of `xcl_view` |
| **`no_promises_until` Guards** | Enforced in `UMPromising.v:250, 318, 438, 469, 483, 487, 491, 503, 509` (prevents out-of-thin-air promise dependence on unfulfilled earlier promises) | Omitted in `ArchSemTinyArm/Promising.lean` (neither `readMem`, `regWrite ._PC`, `memWriteAnnounce`, nor `barrier` checks `no_promises_until`) |
| **Arm Virtual Memory (`VMPromising`)** | Full 2,809-line model in `ArchSemArm/VMPromising.v` (EL0/EL1 4KB 48-bit Stage-1 translation, `Ev.Msg` + `Ev.Tlbi`, TLB refill/invalidation, `relaxed_regs` TTBRs, BBM checks, epoch-based TLBI commutation filter `#307`) | **Absent** |
| **Axiomatic Models & Equivalence Proofs** | `UMArm.v`, `VMSA22Arm.v`, `VMUMEquivThm.v` (`Theorem VMUM_phase1` proving `UM.consistent_ok ↔ VMSA.consistent_ok` under EL0 hypotheses), `UMAxRiscV.v`, `AxiomaticX86TSO.v` | Only `SequentialAxiomatic.lean` (sequential consistency); Furthermore, `CandidateExecution.lean:1134-1152` defines `addr`, `data`, and `ctrl` with **identical** bodies (`memReads ; ... ; memWriteReqs`), lacking syntactic/semantic separation of address, data, and control dependencies |
| **Other Architectures (RISC-V, x86)** | `ArchSemRiscV/` (`UMAxRiscV.v`) and `ArchSemX86/` (`AxiomaticX86TSO.v`, `OperationalX86TSO.v` with store buffers and global lock) | **Absent** (only TinyArm) |
| **Version Skew with `lean-sail` & `sail-tiny-arm-lean`** | Coq build synchronized via `dune` and `coq-sail` | `archsem-lean` pins `lean-sail` at `be17410bd` (with `.returnExecption` typo) and `sail-tiny-arm-lean` at `e8fbacf0a` (`Out.*` namespace) on `nightly-2026-02-17`, whereas `sail-tiny-arm-lean` `main` (`4a474cfc4`) uses `SailTinyArmUser.*` and `lean-sail` `v7` on `v4.29.0` |

---

### 4. Integration Architecture for Anneal (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/Memory.lean`)

#### 4.1 Semantic Alignment Between `ArchSem` and Anneal Layer 1A / 1B

Anneal's trusted foundation (`trusted/lean/Trusted/`) and `archsem` / `archsem-lean` share an isomorphic refinement-and-UB lattice:

| Concept | `archsem` / `archsem-lean` | Anneal (`Trusted/Refinement.lean` & `Trusted/StepResult.lean`) |
|---|---|---|
| Behavior representation | `Set (ModelResult n Flag term)` (`.finalState`, `.flagged`, `.error`) | `Behavior Obs` (`wf : Prop`, `val : Obs → Prop`) |
| Safety / UB-freedom | `no_error` (`∀ s ∈ m, ¬ s.is_error`, `TerminatingModel.lean:94`) | `b.wf` (`¬ ReachesPrefix M.step fuel (M.init p) (.failed .ub)`, `StepResult.lean:96`) and `b ≤ WellFormed P` (`Refinement.lean:59`) |
| Refinement ordering | `m.weaker m'` (`m'.no_error → m.finalStates ⊆ m'.finalStates ∧ m.no_error`, `TerminatingModel.lean:99-103`) | `b1 ≤ b2` (`(b2.wf → b1.wf) ∧ (b1.wf → ∀ o, b1.val o → b2.val o)`, `Refinement.lean:45`) |
| Fuel exhaustion vs. UB | Confused in `ArchSemTinyArm/Sequential.lean:101` and `Promising.lean:747, 764, 772`, which throw `.error "out of fuel"` (conflating insufficient fuel with UB!) | Cleanly separated in `FailureKind` (`StepResult.lean:24-29`): `.fuelExhausted` (`ReachesPrefix.zero`) does **not** falsify `wf` (`wf` only forbids `.failed .ub`), so increasing fuel is monotone without false UB! |
| Bounded nondeterminism (`FinChoice`) | `NEStateM.chooseFin n` (`List.finRange n`) | `StepResult.choice .demonic (fun i : Fin n => ...)` (`StepResult.lean:39`) |
| Weak-memory load nondeterminism | `Promising.read loc vread init mem` (`ListSet (Value × Timestamp)`) | `MemState.visibleAtomicMsgs m curView a` (`Memory.lean:160-165`) paired with `StepResult.choice .demonic` and `applyAtomicLoad` (`Memory.lean:168-174`) |

#### 4.2 Mechanized Bridge & Soundness Proofs (`support/sail_archsem_lean_bridge_probe.lean`)

In [`support/sail_archsem_lean_bridge_probe.lean`](support/sail_archsem_lean_bridge_probe.lean), checked standalone under Lean 4.34.1 (`/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768`) with zero `sorry` and only standard axioms `[propext, Quot.sound]`, we mechanize `FreeM`, `PreSailM`, `archSemSeqInterpret` (`ArchSemSequential`), `archsemLeanInterpret` (`NEStateM`), and the Anneal `StepResult` + `Trusted.Memory` bridge (`sailBridgeMachine` / `stepSailConfig`), and prove:

1. **`FreeM.instLawfulMonad` (`lines 92-146`):** Proves `LawfulMonad (FreeM Eff)` for any `[Effect Eff]`.
2. **`archSemSeq_unsound_for_demonic_undefined` (`lines 691-701`):** For `undefHazardProg : PreSailM Unit Unit` (which binds `b ← undefined_bit ()` and executes `sail_assert (b == 0#1)`):
   - `archSemSeqInterpret undefHazardProg emptySeqState = .ok () emptySeqState` (succeeds unconditionally because `ArchSemSequential` hardcodes `FinChoice` to `0`).
   - `"SailError" ∈ (archsemLeanInterpret undefHazardProg emptySeqState).errors` (`archsem-lean`'s `NEStateM` catches the failure on branch `1`).
   - `¬ (BehaviorOf (sailBridgeMachine Unit Unit emptyBridgeState) 2 undefHazardProg ≤ WellFormed (Unit × BridgeMachineState))` (Anneal's `StepResult` bridge rejects the program as non-`WellFormed` because demonic branch `⟨1, _⟩ : Fin 2` reaches `PrefixOutcome.failed .ub`).
3. **`archSemSeq_unsound_for_silent_exception` (`lines 714-726`):** For `silentExnProg` (which calls `sail_take_exception ()` followed by `writeReg .R0 0xdead#64`), `archSemSeqInterpret` silently treats `.archException` as `pure ()` and commits `R0 = some 0xdead#64`, whereas both `archsemLeanInterpret` and Anneal's `stepSailConfig` immediately fail with exception/UB (`ReachesPrefix stepSailConfig 1 ... (.failed .ub)`).
4. **`unsync_can_read_new_and_stale` & `synced_cannot_read_stale` (`lines 769-875`):** Demonstrates how `stepSailConfig` bridges `.memRead` to `MemState.visibleAtomicMsgs`: before acquire/barrier synchronization (`curView = View.bot`), reading `0x1000` branches demonically (`StepResult.choice .demonic`) to observe both the new store `42#64` (`timestamp = 1`) and the initial value `0#64` (`timestamp = 0`); once `curView.ts 0x1000` advances to `1`, `synced_cannot_read_stale` proves that `¬ ReachesPrefix stepSailConfig 2 { term := readAddr1000Prog, state := syncedBridgeState } (.done (.ok 0#64, s'))` for any `s'`.
5. **`stepResult_wellFormed_excludes_neStateM_error` & `archSemSeq_ok_in_stepResult_behavior` (`lines 928-1091`):** Proves across all `IsChoiceRegOnly` `FreeM` trees that:
   - If the Anneal `StepResult` bridge satisfies `(BehaviorOf (sailBridgeMachine ue α sBridge) fuel m).wf` for all `fuel`, then `(archsemLeanInterpret m sSeq).errors = []` (no nondeterministic branch in `NEStateM` can fail).
   - Whenever `archSemSeqInterpret m sSeq = .ok val sSeq'`, there exists a finite `fuel` and register-agreeing `sBridge'` such that `(BehaviorOf (sailBridgeMachine ue α sBridge) fuel m).val (val, sBridge')` holds.

---

## Boundaries

1. **Where `lean-sail`'s `ArchSemSequential` Breaks:**
   - **Never sound for verification of specifications containing `undefined_*`, `internal_pick`, `choose_fin`, architectural exceptions (`sail_take_exception` / `sail_return_exception`), barriers (`sail_barrier`), cache/TLB maintenance (`sail_cache_op` / `sail_tlbi`), or concurrent memory accesses.** Its only valid use case is fast deterministic single-path smoke testing of purely sequential, exception-free, deterministically initialized instruction fragments.
2. **Where `sail` Dependent Existential Lowering (`2ae2199f8`) Breaks:**
   - As documented in `src/sail_lean_backend/pretty_print_lean.ml:897-899` and `test/suites/lean.py:28-29`, dependent Sigma pair synthesis `(Σ k, inner)` is currently implemented only for patterns (`doc_pat`) and direct function/constructor arguments (`d_of_arg_with_typ`), **not** for existential types returned by functions or nested inside tuples/unions (`exists_tuple_order` and `exists_union_order` remain skipped in `test/suites/lean.py`).
   - Furthermore, when an existential type variable `'n` is used only in a constraint and erased from the payload type (e.g., `{'n, 0 <= 'n <= 31. int('n)}` where `int('n)` lowers to `Int`), `relevant_existential_vars` is empty and the constraint `0 <= 'n <= 31` is erased from the Lean type (`pretty_print_lean.ml:333-336`).
3. **Where `archsem-lean` (`318583a5f`) Breaks Relative to `archsem` (Rocq):**
   - `archsem-lean`'s `Promising.lean` does not support mixed-size memory accesses (rejecting any explicit access size other than 8 bytes or unaligned addresses), rejects atomic RMW accesses (`mem_acc_is_atomic_rmw`), omits `no_promises_until` guards on `readMem` / `regWrite ._PC` / `memWriteAnnounce` / `barrier`, and conflates fuel exhaustion (`"out of fuel"`) with model `.error` (UB).
   - `archsem-lean`'s `CandidateExecution.lean:1134-1152` defines `addr`, `data`, and `ctrl` with identical relational expressions, because `FreeM` traces do not yet carry register/memory syntactic dependency annotations.
4. **Where Anneal's `TrustedBoundary.lean` Rejects Sail-Generated Lean Code:**
   - Any Sail function lowered with `--lean-partial-function` or containing an unmeasured `while`/`until` loop (which elaborates to `Lean.Loop.forIn`) produces `partial` constants in the Lean environment, which `TrustedBoundary.lean` rejects (`Parser.Command.partial` at `line 149` and `ci.isPartial` at `lines 595, 664, 747`).

---

## Evidence

- **Local Checked Mechanization:**
  - [`support/sail_archsem_lean_bridge_probe.lean`](support/sail_archsem_lean_bridge_probe.lean) — 1,105 lines of standalone Lean 4.34.1 code, verified with `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768` (exit code 0, zero warnings, zero `sorryAx`, and only standard `[propext, Quot.sound]` axioms verified by 7 `#guard_msgs in #print axioms` blocks).
- **Source Provenance Manifest:**
  - [`support/source-manifest.json`](support/source-manifest.json) — exact commit revisions, commit timestamps, file byte sizes, line counts, and SHA-256 digests for all 64 inspected source files across `rems-project/sail`, `rems-project/lean-sail`, `rems-project/archsem-lean`, `rems-project/archsem`, and `rems-project/sail-tiny-arm-lean`, plus `support/sail_archsem_lean_bridge_probe.lean`.
- **Key Upstream Source Locations:**
  - `rems-project/sail` (`0f51056900af85d0b18928d6ea2d2271d18184e8`):
    - `src/sail_lean_backend/sail_plugin_lean.ml:119` (`lib_default_rev = "v8"`), `lines 176-244` (`lean_rewrites`), `lines 326-447` (`lean_target`).
    - `src/sail_lean_backend/pretty_print_lean.ml:269-348` (`doc_sail_typ` & Sigma types), `lines 528-586` (`doc_pat` existential patterns), `lines 868-928` (loops & `d_of_arg_with_typ`), `lines 971-1040` (`foreach` & `<&&>`/`<||>` short-circuiting), `lines 1265-1337` (`doc_funcl_init`, `doc_termination`), `lines 1470-1495` (`Def_let` monadic lifting).
    - `src/lib/rewrites.ml:562-655` (`rewrite_if_eq`), `lines 2888-2900` (`rewrite_var_updates` `E_let` bugfix).
    - `src/lib/deptype_targets.ml:34-97` (`unfold_exists_typ`, `relevant_existential_vars`, `typ_of_constructor`).
  - `rems-project/lean-sail` (`1e5b216bf881ef08da160db63b44ecda430802d6`):
    - `Sail/ArchSem.lean:27-72` (`Effect`, `FreeM`, `FinChoice`), `lines 151-220` (`InstructionEffect`, `PreSailM`, `PreSailME`), `lines 273-364` (primitives, `undefined_vector`, `sail_sys_reg_read`/`write`).
    - `Sail/ArchSemSequential.lean:51-90` (`interpretEffect`, `interpretSailEffects`).
  - `rems-project/archsem-lean` (`318583a5f2052c039c25dfd69a3beec0b0a27090`):
    - `ArchSem/Trace.lean:36-99`, `ArchSem/NondeterministicMonad.lean:16-245`, `ArchSem/TerminatingModel.lean:60-145`, `ArchSem/CandidateExecution.lean:872-1169`.
    - `ArchSemTinyArm/Sequential.lean:51-124`, `ArchSemTinyArm/SequentialAxiomatic.lean:56-107`, `ArchSemTinyArm/Promising.lean:324-834`, `ArchSemTinyArm/PromisingFirstProof.lean:17-367`.
  - `rems-project/archsem` (`42204d87df2e7d20e5ec23deb8ba8220e65148ab`):
    - `ArchSem/Interface.v:332-445`, `ArchSem/FromSail.v:205-286`, `ArchSem/SeqModel.v:110-178`, `ArchSem/GenPromising.v:352-896`, `ArchSem/TermModels.v:205-459`, `ArchSemArm/UMPromising.v:314-561`, `ArchSemArm/VMPromising.v:158-216`, `ArchSemArm/VMUMEquivThm.v:400-406`.

---

## Revalidation

1. **Re-verify the standalone Lean 4.34.1 mechanization probe:**
   ```bash
   /usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     -j1 -M768 \
     reports/sail-lean-backend-lean-sail-and-archsem-lean-ecosystem-2026/support/sail_archsem_lean_bridge_probe.lean
   ```
   Expected result: exit code `0` with zero stdout/stderr output (all `#guard_msgs in #print axioms` assertions confirm only `[propext, Quot.sound]`).

2. **Triggers for revalidating upstream conclusions:**
   - When `rems-project/sail` updates `src/sail_lean_backend/pretty_print_lean.ml` or `src/lib/deptype_targets.ml` (particularly if existential Sigma pair synthesis is extended to function return values and tuples, or if `lib_default_rev` advances beyond `"v8"`).
   - When `rems-project/lean-sail` modifies `Sail/ArchSem.lean` or `Sail/ArchSemSequential.lean` (e.g., if `sail_sys_reg_read`/`write` begins passing `some id` to `.regRead`/`.regWrite`, or if `ArchSemSequential` is replaced by a nondeterministic interpreter).
   - When `rems-project/archsem-lean` upgrades its `lean-toolchain` and `lake-manifest.json` from `lean-sail` `be17410bd` to `v8` (`1e5b216bf`) and ports mixed-size `GenPromising` or `VMPromising` from `rems-project/archsem`.

*Authored by an AI agent acting on joshlf's behalf.*
