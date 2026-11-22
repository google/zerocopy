# Rust Native Contracts (`#![feature(contracts)]`): `requires`/`ensures` Lowering, Defining-Crate Check Scoping, CTFE Bypass, LLVM Range Deduction, and Static-Verification Erasure

## Summary

In 2026 nightly `rustc` (`1.98.0-nightly` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` through `1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, unchanged in core contract lowering through `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), Rust's unstable native contracts (`#![feature(contracts)]`, `core::contracts::{requires, ensures}`, `-Z contract-checks=yes|no`) exhibit seven load-bearing architectural properties established by primary-source inspection, live compiler/LLVM/Miri execution, and a kernel-checked Lean `v4.34.1` mechanization:

1. **HIR-baked boolean literals govern `#[requires]`/`#[ensures]`, not `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)`:** `compiler/rustc_ast_lowering/src/contract.rs` lowers contract guards directly into HIR `if true { ... }` / `if false { ... }` using the defining crate's `self.tcx.sess.contract_checks()` (`default: false`). Consequently, `inc_bounded`'s `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR contain zero `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)` operands. Although `RuntimeChecks::ContractChecks` and `sym::contract_checks` exist in `rustc_middle::mir::syntax` and `LowerIntrinsics`, `sym::contract_checks` is omitted from `check_intrinsic_type` (`rustc_hir_analysis/src/check/intrinsic.rs`) and undeclared in `library/core`, failing with `error[E0093]` if invoked directly.
2. **Cross-crate enforcement strictly tracks the defining crate's `-Z contract-checks` flag, even for `#[inline]`, `#[inline(always)]`, and generic functions:** Because the `bool` literal is baked during AST-to-HIR lowering in the defining crate, a `2 × 2` cross-crate matrix confirms `up=no, ds=yes -> rc = 0` (violated contract silently missed) and `up=yes, ds=no -> rc = -6` (`SIGABRT` via `core::panicking::panic_nounwind`) identically across `#[inline]`, `#[inline(always)]`, and generic functions.
3. **`build_check_ensures` imposes `Fn(&Ret) -> bool + Copy + 'static`, producing capture and inference traps:** `library/core/src/contracts.rs` defines `build_check_ensures<Ret, C>(cond: C) -> C where C: Fn(&Ret) -> bool + Copy + 'static`. Writing `#[ensures(|ret| *ret == x + 1)]` fails with `error[E0597]` (`x` captured by reference does not satisfy `'static`) unless `move |ret|` is written; capturing non-`Copy` values fails with `error[E0277]`; capturing non-`'static` references fails lifetime checking; method calls on `ret` without an explicit type annotation (`#[ensures(|ret| ret.is_ok())]`) fail with `error[E0282]`; and the parser grammar requires `#[requires]` before `#[ensures]` with at most one of each.
4. **`#[ensures]` intercepts implicit tail returns, explicit `return`, `?`, and `do yeet`, but is silently bypassed by explicit tail calls (`become`) and unwinding panics:** `LoweringContext::checked_return` wraps `ExprKind::Ret`, `ExprKind::Try` (`?`), and `ExprKind::Yeet` (`do yeet`), causing early-return postcondition violations to abort with `rc = -6` (`"failed ensures check"`). In contrast, `ExprKind::Become` (`#![feature(explicit_tail_calls)]`) lowers directly to `hir::ExprKind::Become` without calling `checked_return`, silently returning an invalid result (`rc = 0`, `TAIL=0`) even under `-Z contract-checks=yes`. Unwinding panics caught by `catch_unwind` likewise bypass `#[ensures]`.
5. **CTFE silently bypasses both `#[requires]` and `#[ensures]` even under `-Z contract-checks=yes`, while Miri rejects active contract checks on all calls (valid or invalid):** Although `CompileTimeMachine::runtime_checks` returns `interp_ok(true)`, both `contract_check_requires` and `contract_check_ensures` use `const_eval_select!` with an empty `if const { /* Do nothing */ }` arm. As a result, `pub const BAD: u32 = bad_const_fn(0)` (violating both `#[requires(x > 0)]` and `#[ensures(|ret| *ret > 100)]`) compiles with `rc = 0` and evaluates to `0` under `-Z contract-checks=yes`. Under Miri with `-Z contract-checks=yes`, even precondition- and postcondition-satisfying calls fail with `rc = 1` (`error: unsupported operation`) because neither intrinsic carries `#[miri::intrinsic_fallback_is_spec]`; under default / `-Z contract-checks=no`, Miri executes cleanly (`rc = 0`) and misses contract violations.
6. **LLVM 22 and LLVM 23 fold tautological `#[ensures]` and deduce `noundef range(i32 1, 101)` + `add nuw nsw` from `-Z contract-checks=yes`:** For `inc_bounded(x: u32) -> u32` (`#[requires(x < 100)]`, `#[ensures(move |ret| *ret == x + 1 && *ret > 0 && *ret <= 100)]`), default and `-Z contract-checks=no` emit 5-line bare `add i32 %x, 1; ret`. Enabling `-Z contract-checks=yes` emits 14 lines containing a single `icmp ult i32 %0, 100` guard, a single 21-byte `"failed requires check"` `core::panicking::panic_nounwind` + `unreachable` block, zero `"failed ensures check"` code, return attribute `noundef range(i32 1, 101)`, and `%__ret = add nuw nsw i32 %0, 1`. Non-tautological `#[ensures]` (`buggy_early_return`) retains the 20-byte `"failed ensures check"` `panic_nounwind` call.
7. **Static-verification erasure soundness and fail-closed Anneal boundary:** Unlike runtime contracts, `joshlf/anneal@c131b320e` checks static proof obligations (`BodyVerified`, `ProgramVerified`, `CrateTheorem`, `UnitTheorem`) over `Runtime(PostCleanup)` MIR and intentionally omits `Operand::RuntimeChecks` from `Trusted.MirAst.Operand` (failing closed with `"runtimeChecks unsupported"` in `Trusted.Correspondence`). The companion Lean `v4.34.1` development (`support/NativeContractsAndRuntimeChecksSoundness.lean`) proves `verified_contract_erasure_preserves_behavior`, its converse `static_verification_iff_erasure_preserves_behavior`, `ensures_checks_every_normal_exit`, `contract_check_determined_by_defining_crate_flag`, LLVM range/folding soundness, and four constructive counterexamples (`ce1`–`ce4`) with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, and `0` `partial def`.

## Applicability

This report characterizes five pinned subjects listed in `REPORT.json` and their relationships:

| Subject | Repository & Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| `rustc 1.102.0-nightly` + LLVM `23.1.5` | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11) | Primary upstream source audit across macro expansion, parser, AST-to-HIR lowering, MIR transforms, codegen, CTFE, and Miri; plus recorded LLVM 23.1.5 / runtime / cross-crate / CTFE / Miri execution baseline (`support/rustc_1_102_llvm23_baseline.json`). |
| `rustc 1.98.0-nightly` + LLVM `22.1.6` + Miri `0.1.0` | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31) | Live end-to-end execution of the full expanded probe suite (`support/probe_rustc_contracts.py` -> `support/probe_rustc_contracts_results_1_98_llvm22.json`), including MIR dumps, LLVM IR, 2×2×3 cross-crate matrix, 9 capture/syntax diagnostics, 6 exit-path tests (`return`, `?`, `do yeet`, `become`, `catch_unwind`), CTFE execution, and `no_std` Miri execution; plus line-by-line source diff against `3ef0c22cd`. |
| `rustc` source drift snapshot | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (2026-11-22) | Source-only drift check verifying whether contract macros, `core/src/contracts.rs`, `rustc_ast_lowering/src/contract.rs`, `lower_intrinsics.rs`, or `miri::intrinsic_fallback_is_spec` on contract intrinsics changed after `3ef0c22cd`. |
| Anneal trusted MIR boundary | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Direct source audit of `Trusted.MirAst`, `Trusted.MirSemantics`, `Trusted.Correspondence`, and vendored `lean-miri` (`Miri/MIR/Syntax.lean`), contrasting runtime contract checking with Anneal's static proof obligations and fail-closed `RuntimeChecks` rejection. (Note: `Trusted.MirAst` cites upstream `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `anneal-rustc-capture` pins `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.) |
| Lean 4 proof kernel | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, 2026-09-24) | Kernel-checked execution of `support/NativeContractsAndRuntimeChecksSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and `#print axioms` auditing. |

### Shared vs. Version-Specific Behavior Across Studied `rust-lang/rust` Revisions

Direct diffing across `14210df0e` (2026-05-31), `3ef0c22cd` (2026-11-11), and `342d74463` (2026-11-22) establishes the following exact version alignment:

- **Identical across all three revisions (`14210df0e`, `3ef0c22cd`, `342d74463`):**
  - `library/core/src/contracts.rs` is byte-for-byte identical (24 lines): `build_check_ensures<Ret, C>` requires `C: Fn(&Ret) -> bool + Copy + 'static`.
  - `compiler/rustc_ast_lowering/src/contract.rs` lowers all contract guards to `self.expr_bool_literal(span, self.tcx.sess.contract_checks())` (baked defining-crate literal), intercepts `return`, `?`, and `do yeet` via `checked_return`, and leaves `ExprKind::Become` unchecked.
  - `library/core/src/intrinsics/mod.rs` implements `contract_check_requires` and `contract_check_ensures` with `const_eval_select!` (`if const` is a no-op; `else` calls `crate::panicking::panic_nounwind(...)`), and omits `#[miri::intrinsic_fallback_is_spec]` on both intrinsics.
  - `compiler/rustc_hir_analysis/src/check/intrinsic.rs` lists `sym::contract_checks` in the known-intrinsic match (`line 92`) while omitting it from `check_intrinsic_type` (`line 697` in `14210df0e`, `line 635` in `3ef0c22cd`).
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs` maps `sym::contract_checks` to `RuntimeChecks::ContractChecks` (`lines 26-30`).
  - Empirical `inc_bounded` LLVM IR structure is functionally identical between LLVM `22.1.6` (`14210df0e`) and LLVM `23.1.5` (`3ef0c22cd`): 5 lines (`add i32 %x, 1; ret`) at default / `-Z contract-checks=no`, and 14 lines (`noundef range(i32 1, 101)`, `icmp ult i32 %0, 100`, single 21-byte `panic_nounwind` + `unreachable`, `%__ret = add nuw nsw i32 %0, 1; ret`) at `-Z contract-checks=yes`.
- **Minor differences between `14210df0e`, `3ef0c22cd`, and `342d74463`:**
  - `compiler/rustc_builtin_macros/src/contracts.rs`: `3ef0c22cd` (and `342d74463`) added an explicit empty-annotation check (`lines 140-153`, emitting `` `requires` attribute requires an argument ``) and switched `new_tts` from `TokenStream` to `Vec<TokenTree>`.
  - `compiler/rustc_ast_lowering/src/contract.rs`: `3ef0c22cd` removed a redundant `#[allow(unreachable_code)]` attribute attachment at lines 351-352 of `14210df0e` and migrated `LangItem` import paths and `sym::__ensures_checker` / `sym::__ret` symbols.
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs`: `342d74463` refactored `intrinsic.name` matching to `let Intrinsic::Rustc(name) = intrinsic.name` (preserving the exact `sym::ub_checks | sym::overflow_checks | sym::contract_checks` arm).
  - LLVM IR metadata: LLVM `23.1.5` (`3ef0c22cd`) attaches `!guid !188` / `!guid !194` metadata to `define` headers and `nofree` on the `panic_nounwind` pointer argument, whereas LLVM `22.1.6` (`14210df0e`) omits `!guid` and `nofree` while producing identical CFG, `range(i32 1, 101)`, `add nuw nsw`, and 21-byte `panic_nounwind` semantics.

### Configuration and Execution Scope

- **Target / Host:** `x86_64-unknown-linux-gnu`, Rust edition `2024`.
- **Required feature gates:** `#![feature(contracts)]` (tracking issue `rust-lang/rust#128044`, emits `#[warn(incomplete_features)]`); auxiliary exit-path probes additionally enable `#![feature(yeet_expr)]` and `#![feature(explicit_tail_calls)]`; the raw intrinsic negative probe enables `#![feature(intrinsics)]`.
- **Compiler flags:** `-C opt-level=2` (for MIR optimization and LLVM IR deduction probes), `-Z contract-checks=yes`, `-Z contract-checks=no`, and default (omitted, equivalent to `no` via `self.opts.unstable_opts.contract_checks.unwrap_or(false)`).
- **Miri execution scope:** The `14210df0e` Miri runs use `miri 0.1.0` directly on a `#![no_std]` harness with a locally compiled MIR-encoded `core` (`--cfg=miri -Zalways-encode-mir -Cpanic=abort`) and a minimal `compiler_builtins` stub; the `3ef0c22cd` baseline runs `cargo miri` on a `std` crate with `-Z contract-checks=yes`. Both confirm the same `rc = 1` rejection on `contract_check_requires`.

## Findings

### 1. End-to-End Compiler Pipeline: Builtin Macro Expansion, Parser Grammar, and HIR Lowering

`Basis: source + execution`

Rust's native contract mechanism spans four front-end/middle-end layers before reaching MIR optimization and codegen:

#### 1.1 Public Library Surface and Builtin Attribute Macro Expansion

`library/core/src/contracts.rs` (`lines 1-24`, identical at `14210df0e`, `3ef0c22cd`, and `342d74463`) re-exports two compiler builtin attribute macros and defines one helper lang item:

```rust
pub use crate::macros::builtin::{contracts_ensures as ensures, contracts_requires as requires};

#[unstable(feature = "contracts_internals", issue = "128044")]
#[rustc_const_unstable(feature = "contracts", issue = "128044")]
#[lang = "contract_build_check_ensures"]
pub const fn build_check_ensures<Ret, C>(cond: C) -> C
where
    C: Fn(&Ret) -> bool + Copy + 'static,
{
    cond
}
```

`library/core/src/macros/mod.rs` (`lines 1836-1853` at `14210df0e`) marks both `contracts_ensures` and `contracts_requires` with `#[unstable(feature = "contracts", issue = "128044")]`, `#[allow_internal_unstable(contracts_internals)]`, and `#[rustc_builtin_macro]`.

In `compiler/rustc_builtin_macros/src/contracts.rs` (`lines 8-169` at `3ef0c22cd`), `ExpandRequires` and `ExpandEnsures` perform token-tree rewriting rather than AST transformation:

1. They scan forward for `kw::Fn`. If absent, expansion fails with `"contract annotations can only be used on functions"` (`lines 61-72`).
2. If any token before `fn` is `kw::Async` or `kw::Gen`, expansion fails with `"contract annotations are not yet supported on async or gen functions"` (`lines 75-80`).
3. They scan forward to the first `kw::Where` token or the final `{ ... }` function body delimiter. If no body delimiter is present (for example, a bodyless trait method declaration), expansion fails with `"contract annotations is only supported in functions with bodies"` (`lines 83-106, 120-127`).
4. Immediately before `where` (or before `{ ... }`), expansion injects the internal keyword token `kw::ContractRequires` or `kw::ContractEnsures` followed by the annotation wrapped in `{ ... }` (`lines 155-168`).

#### 1.2 Parser Grammar (`FnContract`)

In `compiler/rustc_parse/src/parser/function.rs` (`lines 127-166` at `3ef0c22cd`), `parse_fn` parses a function signature in the fixed order: parameters/return type -> `self.parse_contract()?` -> `self.parse_where_clause()?` -> body. `parse_contract` in `compiler/rustc_parse/src/parser/generics.rs` (`lines 348-391` at `3ef0c22cd`) parses clauses strictly in `contract_requires` then `contract_ensures` order:

```rust
pub(super) fn parse_contract(&mut self) -> PResult<'a, Option<Box<ast::FnContract>>> {
    let (declarations, requires) = self.parse_contract_requires()?;
    let ensures = self.parse_contract_ensures()?;
    if requires.is_none() && ensures.is_none() {
        Ok(None)
    } else {
        Ok(Some(Box::new(ast::FnContract { declarations, requires, ensures })))
    }
}
```

Key syntactic consequences visible in `parse_contract_requires` (`lines 359-381`) and `parse_contract_ensures` (`lines 383-391`):

- `parse_contract_requires` parses `{ ... }` as a block, pops its final tail expression `precond`, wraps `precond` in a zero-argument non-`move` closure (`self.mk_closure_expr(precond.span, precond)` — equivalent to `|| <expr>`), and retains any preceding statements in `FnContract.declarations` (`compiler/rustc_ast/src/ast.rs:4068-4074`).
- `parse_contract_ensures` parses the braced token stream directly via `self.parse_expr()` without wrapping it in a closure — the user must supply a unary closure expression `|ret| ...` (or `move |ret| ...`).
- Both clauses gate on `sym::contracts_internals` (satisfied by the macro's def-site `ALLOW_CONTRACTS` hygiene context).

#### 1.3 AST-to-HIR Lowering: Baked Session Literals Instead of `RuntimeChecks`

In `compiler/rustc_ast_lowering/src/item.rs` (`lines 1260-1281` at `3ef0c22cd`), `lower_fn_body` dispatches to `this.lower_contract(body, contract)` whenever `contract.is_some()`. `compiler/rustc_ast_lowering/src/contract.rs` (`lines 19-355` at `3ef0c22cd`) performs the core desugaring:

- **Precondition-only `(Some(req), None)` (`lines 97-123, 174-194`):** Prepends:
  ```rust
  if <bool_lit(tcx.sess.contract_checks())> {
      <contract_decls>;
      core::intrinsics::contract_check_requires(|| <req>);
  }
  <body>
  ```
- **Postcondition-only `(None, Some(ens))` (`lines 67-96, 196-276`):** Lowers `let __ensures_checker = if <bool_lit> { <contract_decls>; Some(build_check_ensures(<ens>)) } else { None };` before `body`, then wraps the tail expression and every intercepted early return with `inject_ensures_check` (`lines 295-354`):
  ```rust
  {
      let __ret = <expr>;
      if <bool_lit(tcx.sess.contract_checks())> {
          core::intrinsics::contract_check_ensures(__ensures_checker, __ret)
      } else {
          __ret
      }
  }
  ```
  *(Note: the illustrative comment at `contract.rs:74-88` shows `CONTRACT_DECLARATIONS` inside the post-body `if`, whereas the actual code at `lines 90-91` and `196-232` places `contract_decls` inside the pre-body `lower_contract_check_with_postcond` block.)*
- **Both `(Some(req), Some(ens))` (`lines 29-66`):** Evaluates `contract_decls`, calls `contract_check_requires(|| <req>)`, and constructs `Some(build_check_ensures(<ens>))` inside the pre-body `if <bool_lit>`, then wraps every checked return with the post-body `if <bool_lit> { contract_check_ensures(__ensures_checker, __ret) } else { __ret }`.

Crucially, at all three guard emission sites (`contract.rs:187`, `:227`, and `:342`), `rustc` emits a **compile-time `bool` literal** evaluated immediately from the defining crate's compiler session:

```rust
self.expr_bool_literal(span, self.tcx.sess.contract_checks())
```

where `compiler/rustc_session/src/session.rs:1098-1099` defines:

```rust
pub fn contract_checks(&self) -> bool {
    self.opts.unstable_opts.contract_checks.unwrap_or(false)
}
```

and `compiler/rustc_session/src/options.rs:2479-2480` registers `-Z contract-checks` as an `Option<bool>` with `[TRACKED]` default `None` (false). The rationale documented in `contract.rs:9-18` is to keep contract expressions type-checked even when disabled while relying on constant-branch elimination to remove dead `if false { ... }` arms.

#### 1.4 Resulting MIR Structure (`Runtime(PostCleanup)` vs. `Runtime(Optimized)`)

Live MIR dumps of `inc_bounded` on `rustc 1.98.0-nightly (14210df0e)` confirm the exact HIR-to-MIR transition (`support/probe_rustc_contracts_results_1_98_llvm22.json`):

| Mode (`-C opt-level=2`) | `Runtime(PostCleanup)` Guard | `Runtime(PostCleanup)` Calls Present | `Runtime(Optimized)` Calls Present | `Operand::RuntimeChecks(ContractChecks)` |
| :--- | :--- | :--- | :--- | :--- |
| Default (omitted) | `_3 = const false;`, `_11 = const false;` | `contract_check_requires`, `build_check_ensures`, `contract_check_ensures` (in unreachable dead blocks `bb1`/`bb2`/`bb6`) | None in executable CFG (`bb0` is single block: `_2 = const Option::None; _0 = Add(copy _1, const 1_u32); return;`); `build_check_ensures` string survives only in debuginfo `scope 4 (inlined build_check_ensures::...)` comment | `false` (both MIR dumps) |
| `-Z contract-checks=no` | `_3 = const false;`, `_11 = const false;` | Identical to default | Identical to default | `false` (both MIR dumps) |
| `-Z contract-checks=yes` | `_3 = const true;`, `_11 = const true;` | `contract_check_requires`, `build_check_ensures`, `contract_check_ensures` (in live blocks) | `contract_check_requires` (`bb0`) and `contract_check_ensures` (`bb1`); `build_check_ensures` inlined into `Option::Some(copy _6)` | `false` (both MIR dumps) |

Two subtleties matter for downstream MIR consumers (including static verifiers):

1. Even under `-Z contract-checks=no`, **`Runtime(PostCleanup)` MIR still contains the dead `bb1`/`bb2`/`bb6` blocks** invoking `contract_check_requires`, `build_check_ensures`, and `contract_check_ensures` behind `switchInt(const false)`. Those blocks are eliminated only later during `run_optimization_passes` (`SimplifyConstCondition` + `SimplifyCfg` in `compiler/rustc_mir_transform/src/lib.rs:750-770`).
2. `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)` never appears in either MIR dump of any `#[requires]`/`#[ensures]` function.

---

### 2. `build_check_ensures` Type Bounds, Capture Hazards, and Attribute-Order Grammar Limits

`Basis: source + execution`

Because `#[ensures(closure)]` is lowered via `core::contracts::build_check_ensures<Ret, C>(cond: C) -> C` (`library/core/src/contracts.rs:19-24`), every postcondition closure must satisfy `C: Fn(&Ret) -> bool + Copy + 'static`. Moreover, `build_check_ensures` is invoked *before* the function body is lowered, so type inference for `Ret` is deferred until the post-body call `contract_check_ensures(__ensures_checker, __ret)`.

Live compilation probes on `rustc 1.98.0-nightly` (`support/probe_rustc_contracts_results_1_98_llvm22.json`, `probe_3_capture_and_syntax`) and `rustc 1.102.0-nightly` (`support/rustc_1_102_llvm23_baseline.json`, `probe_2b_ensures_borrow_capture_e0597`) establish nine distinct compile-time failure modes:

| Probe Case | Input Pattern | Exit Code | Observed Diagnostic | Root Cause in `rustc` Source |
| :--- | :--- | :---: | :--- | :--- |
| Non-`move` capture of `Copy` param | `#[ensures(\|ret\| *ret == x + 1)] fn f(x: u32) -> u32` | `1` | `error[E0597]: \`x\` does not live long enough` (both `1.98` and `1.102`) | Closure borrows `&x` with frame lifetime `'_`, violating `+ 'static` on `build_check_ensures` (`library/core/src/contracts.rs:21`). Fixed by `move \|ret\| ...`. |
| `move` capture of non-`Copy` param | `#[ensures(move \|ret\| *ret == v.len())] fn f(v: Vec<u8>) -> usize` | `1` | `error[E0277]: the trait bound \`Vec<u8>: Copy\` is not satisfied in \`{closure}\`` | Violates `+ Copy` on `build_check_ensures` (`contracts.rs:21`) and `contract_check_ensures` (`intrinsics/mod.rs:2794`), which need `Copy` because `__ensures_checker` is copied at each `checked_return` site (`contract.rs:327`). |
| `move` capture of borrowed param | `#[ensures(move \|ret\| *ret == *x + 1)] fn f(x: &u32) -> u32` | `1` | `error: lifetime may not live long enough` | Even with `move`, capturing `x: &'a u32` ties the closure type to `'a`, violating `+ 'static`. |
| Method call on unannotated `ret` | `#[ensures(\|ret\| ret.is_ok())] fn f(...) -> Result<u32, u32>` | `1` | `error[E0282]: type annotations needed for \`&_\`` | `build_check_ensures` is type-checked before `contract_check_ensures(__ensures_checker, __ret)` unifies `Ret`, so method lookup cannot resolve `ret.is_ok()` without `\|ret: &Result<u32, u32>\|`. (By contrast, `*ret > 0` succeeds via delayed integer/operator inference.) |
| Reversed attribute order | `#[ensures(...)]` placed above `#[requires(...)]` | `1` | `error: expected one of \`.\`, \`?\`, \`where\`, \`{\`, or an operator, found \`contract_requires\`` | Outer attributes expand top-to-bottom, injecting `contract_ensures` before `contract_requires`; `parse_contract` (`generics.rs:348-350`) parses `contract_requires` strictly before `contract_ensures`. |
| Stacked `#[requires]` | Two `#[requires(...)]` attributes on one `fn` | `1` | `error: expected one of \`where\` or \`{\`, found \`contract_requires\`` | `parse_contract_requires` (`generics.rs:362`) consumes at most one `kw::ContractRequires`. |
| `async fn` / `gen fn` | `#[requires(x > 0)] pub async fn f(x: u32) -> u32` | `1` | `error: contract annotations are not yet supported on async or gen functions` | Explicitly rejected in `rustc_builtin_macros/src/contracts.rs:75-80`. |
| Bodyless trait method | `trait T { #[requires(x > 0)] fn f(x: u32) -> u32; }` | `1` | `error: contract annotations is only supported in functions with bodies` | Explicitly rejected in `rustc_builtin_macros/src/contracts.rs:84-100`. |
| Direct `contract_checks` intrinsic | `#![feature(intrinsics)] #[rustc_intrinsic] pub const fn contract_checks() -> bool;` | `1` | `error[E0093]: unrecognized intrinsic function: \`contract_checks\`` | `sym::contract_checks` is absent from `check_intrinsic_type` (`rustc_hir_analysis/src/check/intrinsic.rs:635` at `3ef0c22cd`, `:697` at `14210df0e`). |

Note also an asymmetry between `#[requires]` and `#[ensures]` bounds: `contract_check_requires<C: Fn() -> bool + Copy>` (`library/core/src/intrinsics/mod.rs:2765`) does **not** require `'static`, which is why the parser-generated `|| x < 100` closure freely borrows `&x` from the stack frame (confirmed directly in the `Runtime(PostCleanup)` MIR dump: `_6 = &_1; _5 = {closure} { x: move _6 };`).

---

### 3. Multi-Exit `#[ensures]` Interception Completeness and Unchecked Control-Flow Bypasses

`Basis: source + execution`

When lowering a function with an `#[ensures]` clause, `wrap_body_with_contract_check` (`compiler/rustc_ast_lowering/src/contract.rs:234-276`) stores the `(postcond_span, __ensures_checker, check_hir_id)` tuple in `self.contract_ensures` before lowering the function body, and then wraps the body's implicit tail expression with `inject_ensures_check`. Nested item/closure scopes are protected by `with_new_scopes` (`compiler/rustc_ast_lowering/src/lib.rs:1122-1144`), which saves and clears `self.contract_ensures` (`let old_contract = self.contract_ensures.take(); ... self.contract_ensures = old_contract;`) so returns inside inner closures or nested functions are never misrouted through the outer function's postcondition.

Auditing all exit-producing `ExprKind` arms in `compiler/rustc_ast_lowering/src/expr.rs` (`3ef0c22cd`) and testing each exit construct live under `-Z contract-checks=yes` (`support/probe_rustc_contracts_results_1_98_llvm22.json`, `probe_1_modes` and `probe_4_exit_paths`) reveals the exact boundary between checked and unchecked exits:

| Exit Construct | `rustc_ast_lowering` Site (`3ef0c22cd`) | Calls `checked_return` / `inject_ensures_check`? | Live Empirical Result (`-Z contract-checks=yes`, violated `#[ensures]`) |
| :--- | :--- | :---: | :--- |
| Implicit tail return | `contract.rs:267` | Yes | Aborts with `rc = -6` (`failed ensures check`, `panic_nounwind`) |
| Explicit `return expr;` | `expr.rs:483-486` | Yes | `buggy_early_return(true)`: `rc = -6`, `failed ensures check` (both `1.98` and `1.102`); `buggy_early_return(false)`: `rc = 0`, `42` |
| `?` operator (`Try` residual exit) | `expr.rs:2018` (when outside `try { ... }`) | Yes | `try_exit(Err(1))`: `rc = -6`, `failed ensures check`; `try_exit(Ok(1))`: `rc = 0`, `Ok(2)` |
| `do yeet expr` (`#![feature(yeet_expr)]`) | `expr.rs:2070` (when `TryBlockScope::Function`) | Yes | `yeet_exit(true)`: `rc = -6`, `failed ensures check`; `yeet_exit(false)`: `rc = 0`, `Ok(1)` |
| Explicit tail call `become helper()` (`#![feature(explicit_tail_calls)]`) | `expr.rs:488-491` (`hir::ExprKind::Become(sub_expr)`) | **No** | **Silent bypass:** `tail_bypass()` (`#[ensures(\|ret\| *ret > 0)]`, `become helper()` returning `0`) compiles (`rc = 0`) and returns `TAIL=0` with `rc = 0`, `failed_ensures = false` |
| Unwinding `panic!` inside body | Unwind edge, bypasses return expressions | **No** | `panics_before_return()` (`#[ensures(\|_\| false)]`) caught via `std::panic::catch_unwind` exits with `rc = 0`, `CAUGHT=true`, `failed_ensures = false` |

The `become` bypass is structurally inherent to tail-call frame replacement: because `become helper()` destroys the caller's stack frame before transferring control to `helper`, there is no caller frame remaining to receive `helper`'s return value and execute `contract_check_ensures`. Until `rustc` either forbids `become` inside `#[ensures]` functions or lowers `become` to a non-tail call when contracts are present, `#[ensures]` is **unsound as a universal postcondition over functions using `explicit_tail_calls`**.

Conversely, note that when a contract check itself fails, both `contract_check_requires` (`core/src/intrinsics/mod.rs:2773`) and `contract_check_ensures` (`:2806`) invoke `crate::panicking::panic_nounwind(...)` (`library/core/src/panicking.rs:219-226`, annotated `#[rustc_nounwind]`). On Linux this terminates the process via `SIGABRT` (`rc = -6`, `"thread caused non-unwinding panic. aborting."`) so callers cannot catch and suppress a violated safety contract via `catch_unwind`.

---

### 4. Dual Check-Scoping Architecture: HIR-Baked Defining-Crate Dominance vs. Latent `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)`

`Basis: source + execution`

A central hazard when adopting Rust native contracts across crate boundaries is assuming `-Z contract-checks=yes` on a downstream binary crate activates contracts in upstream library dependencies (the way `-C overflow-checks=yes` or `-Z ub-checks=yes` activates `#[rustc_inherit_overflow_checks]` / `#[rustc_preserve_ub_checks]` checks in `core` for inlined/generic functions). **That assumption is false for 2026 `#[requires]`/`#[ensures]`.**

#### 4.1 Complete 2×2 Cross-Crate Empirical Matrix

Compiling an upstream crate `up` (`libup.rlib`, `-C opt-level=2`) against a downstream binary `ds` (`-C opt-level=2`) calling violated preconditions (`x = 50` against `x < 10`) yields identical defining-crate dominance across both `rustc 1.98.0-nightly` (`support/probe_rustc_contracts_results_1_98_llvm22.json`, `probe_2_cross_crate`) and `rustc 1.102.0-nightly` (`support/rustc_1_102_llvm23_baseline.json`, `probe_2_cross_crate_contract_checks`):

| Upstream `up` `-Z contract-checks` | Downstream `ds` `-Z contract-checks` | `#[inline] inline_inc(50)` (`1.98` / `1.102`) | `#[inline(always)] inline_always_inc(50)` (`1.98`) | Generic `generic_inc::<u32>(50)` (`1.98`) | Outcome |
| :---: | :---: | :---: | :---: | :---: | :--- |
| `no` | `no` | `rc = 0` (`51`) / `rc = 0` (`51`) | `rc = 0` (`51`) | `rc = 0` (`51`) | Violated contract unchecked |
| **`no`** | **`yes`** | **`rc = 0` (`51`) / `rc = 0` (`51`)** | **`rc = 0` (`51`)** | **`rc = 0` (`51`)** | **Downstream `yes` ignored; violated contract missed** |
| **`yes`** | **`no`** | **`rc = -6` / `rc = -6`** (`failed requires check`) | **`rc = -6`** (`failed requires check`) | **`rc = -6`** (`failed requires check`) | **Upstream `yes` enforced despite downstream `no`** |
| `yes` | `yes` | `rc = -6` / `rc = -6` (`failed requires check`) | `rc = -6` (`failed requires check`) | `rc = -6` (`failed requires check`) | Violated contract aborts |

Why do even `#[inline]`, `#[inline(always)]`, and generic functions track the defining crate? Because `.rlib` metadata exports MIR derived from the defining crate's HIR, and `rustc_ast_lowering/src/contract.rs:187, 227, 342` already evaluated `self.tcx.sess.contract_checks()` into a concrete `bool` literal (`const false` or `const true`) before MIR was even built. For `up=no`, the exported `Runtime(Optimized)` MIR of `inline_inc` has already constant-folded the `if false` branch away; even for unoptimized/generic MIR, the baked `const false` literal remains invariant to the downstream crate's `-Z contract-checks` flag.

#### 4.2 Audit of the Latent `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)` Pipeline

In parallel with HIR-baked contract macros, `rustc` already contains partial MIR/codegen/interpreter plumbing for deferred contract checks — modeled after `ub_checks()` and `overflow_checks()` — across eight compiler sites (`3ef0c22cd`):

1. **MIR Syntax (`compiler/rustc_middle/src/mir/syntax.rs:1338, 1588-1608`):** Defines `Operand::RuntimeChecks(RuntimeChecks)` with `RuntimeChecks::{UbChecks, ContractChecks, OverflowChecks}` and `RuntimeChecks::value(self, sess) -> bool` dispatching `Self::ContractChecks => sess.contract_checks()`.
2. **Intrinsic Lowering (`compiler/rustc_mir_transform/src/lower_intrinsics.rs:26-42`):** `LowerIntrinsics` (a `PassPolicy::Required` pass in `run_runtime_cleanup_passes`) lowers calls to `sym::ub_checks | sym::overflow_checks | sym::contract_checks` into `Rvalue::Use(Operand::RuntimeChecks(op), WithRetag::Yes)`.
3. **Preservation Through MIR Optimizations:**
   - `InstSimplify` (`compiler/rustc_mir_transform/src/instsimplify.rs:34-37, 471-492`) runs `SimplifyUbCheck` **only** on `RuntimeChecks::UbChecks` (when `#[rustc_preserve_ub_checks]` is absent); it leaves `RuntimeChecks::ContractChecks` and `RuntimeChecks::OverflowChecks` unreduced.
   - `SimplifyConstCondition` (`compiler/rustc_mir_transform/src/simplify_branches.rs:49`) returns `None` for `Operand::RuntimeChecks(_)`.
   - `GVN` (`compiler/rustc_mir_transform/src/gvn.rs:276, 585, 1048, 1056, 1982`) tracks `Value::RuntimeChecks(c)` symbolically without folding it to a boolean constant.
4. **Codegen Materialization (`compiler/rustc_codegen_ssa/src/mir/operand.rs:1164-1173`):** Materializes `Operand::RuntimeChecks(checks)` as `Scalar::from_bool(checks.value(bx.tcx().sess))` using the **codegen (monomorphizing/caller) crate's** `Session`.
5. **Interpreter Hooks (`compiler/rustc_const_eval/src/interpret/operand.rs:850-853`):** Delegates `Operand::RuntimeChecks(checks)` to `M::runtime_checks(self, checks)`.
   - **CTFE (`compiler/rustc_const_eval/src/const_eval/machine.rs:981-988`):** Returns `interp_ok(true)` unconditionally, with the comment: *"We can't look at `tcx.sess` here as that can differ across crates, which can lead to unsound differences in evaluating the same constant at different instantiation sites."*
   - **Miri (`src/tools/miri/src/machine.rs:1448-1453`):** Returns `interp_ok(r.value(ecx.tcx.sess))`.
6. **The Missing Frontend Link (`library/core` and `rustc_hir_analysis/src/check/intrinsic.rs`):** Despite `sym::contract_checks` appearing in `check/intrinsic.rs:92` and `lower_intrinsics.rs:29`, `library/core/src/intrinsics/mod.rs` declares only `ub_checks()` (`line 2675`) and `overflow_checks()` (`line 2699`) — **never** `contract_checks()` — and `check_intrinsic_type` (`check/intrinsic.rs:635`) matches only `sym::ub_checks | sym::overflow_checks`, rejecting user declarations of `contract_checks` with `error[E0093]`.

Thus, in 2026 `rustc`, `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)` is **wired-but-unreachable infrastructure** awaiting a future migration of `rustc_ast_lowering/src/contract.rs` from `expr_bool_literal(sess.contract_checks())` to a deferred `contract_checks()` intrinsic call. If that migration lands, cross-crate scoping for `#[inline]`/generic functions will flip from defining-crate determinism to caller-crate (monomorphization-crate) scoping — directly reversing the current 2×2 matrix.

---

### 5. CTFE Bypass via `const_eval_select!` and Miri Intrinsic-Fallback Rejection

`Basis: source + execution`

#### 5.1 Why CTFE Silently Skips `#[requires]` and `#[ensures]` Even Under `-Z contract-checks=yes`

Neither `compiler/rustc_const_eval/src/interpret/intrinsics.rs` nor `compiler/rustc_codegen_llvm/src/intrinsic.rs` contains special-case handlers for `contract_check_requires` or `contract_check_ensures`. Both are fallback-body `#[rustc_intrinsic]` functions in `library/core/src/intrinsics/mod.rs` (`lines 2763-2811` at `3ef0c22cd`; `lines 2686-2739` at `14210df0e`):

```rust
#[lang = "contract_check_requires"]
#[rustc_intrinsic]
pub const fn contract_check_requires<C: Fn() -> bool + Copy>(cond: C) {
    const_eval_select!(
        @capture[C: Fn() -> bool + Copy] { cond: C } :
        if const {
                // Do nothing
        } else {
            if !cond() {
                // Emit no unwind panic in case this was a safety requirement.
                crate::panicking::panic_nounwind("failed requires check");
            }
        }
    )
}

#[lang = "contract_check_ensures"]
#[rustc_intrinsic]
pub const fn contract_check_ensures<C: Fn(&Ret) -> bool + Copy, Ret>(
    cond: Option<C>,
    ret: Ret,
) -> Ret {
    const_eval_select!(
        @capture[C: Fn(&Ret) -> bool + Copy, Ret] { cond: Option<C>, ret: Ret } -> Ret :
        if const {
            // Do nothing
            ret
        } else {
            if let crate::option::Option::Some(cond) = cond && !cond(&ret) {
                // Emit no unwind panic in case this was a safety requirement.
                crate::panicking::panic_nounwind("failed ensures check");
            }
            ret
        }
    )
}
```

When `rustc` prepares MIR for CTFE (`inner_mir_for_ctfe` in `compiler/rustc_mir_transform/src/lib.rs:506-541`), line `526` runs `remap_mir_for_const_eval_select(tcx, body, hir::Constness::Const { always })` (`lines 244-318`), rewriting the `const_eval_select` call terminator to invoke `called_in_const` (the no-op `if const` arm). By contrast, `inner_optimized_mir` (`line 813`) passes `hir::Constness::NotConst`, selecting `called_at_rt`.

This produces a striking soundness asymmetry:

- Even though `CompileTimeMachine::runtime_checks` returns `interp_ok(true)` (`const_eval/machine.rs:987`) and even when the crate is compiled with `-Z contract-checks=yes` (baking `if true` around the intrinsic calls), CTFE executes the `if const { /* Do nothing */ }` arm of both `contract_check_requires` and `contract_check_ensures`.
- Empirically confirmed on both `rustc 1.98.0-nightly` (`probe_5_ctfe_bypass`) and `rustc 1.102.0-nightly` (`probe_3_ctfe_violation`):
  ```rust
  #[requires(x > 0)]
  #[ensures(|ret| *ret > 100)]
  pub const fn bad_const_fn(x: u32) -> u32 { x }
  pub const BAD: u32 = bad_const_fn(0);
  ```
  compiles with `compile_rc = 0` under both `-Z contract-checks=no` and `-Z contract-checks=yes`, and at runtime prints `BAD_CONST=0` (`runtime_rc = 0`) — delivering a value that violates both the function's precondition (`0 > 0`) and its postcondition (`0 > 100`).

#### 5.2 Why Miri Fails with `rc = 1` on Valid and Invalid Calls Under `-Z contract-checks=yes`

In `src/tools/miri/src/intrinsics/mod.rs` (`lines 57-79` at `3ef0c22cd`; `lines 70-85` at `14210df0e`), when Miri encounters an intrinsic without a Miri shim and without `must_be_overridden`, it refuses to execute the intrinsic's Rust fallback body unless the intrinsic carries the tool attribute `#[miri::intrinsic_fallback_is_spec]`:

```rust
let intrinsic_fallback_is_spec = ecx
    .tcx
    .tool_attrs(instance.def_id(), &[sym::miri, sym::intrinsic_fallback_is_spec])
    .next()
    .is_some();
if !intrinsic_fallback_is_spec {
    throw_unsup_format!(
        "Miri can only use intrinsic fallback bodies that exactly reflect the specification: \
         they fully check for UB and are as non-deterministic as possible. After verifying that \
         `{intrinsic_name}` does so, add the `#[miri::intrinsic_fallback_is_spec]` attribute \
         to it; also ping @rust-lang/miri when you do that"
    );
}
```

Whereas `const_allocate`, `const_deallocate`, and `const_make_global` immediately above in `library/core/src/intrinsics/mod.rs` (`lines 2714, 2734, 2745` at `3ef0c22cd`) carry `#[miri::intrinsic_fallback_is_spec]`, neither `contract_check_requires` (`line 2765`) nor `contract_check_ensures` (`line 2794`) carries that attribute (still absent at `rust-lang/rust@342d74463`).

Live Miri execution (`support/probe_rustc_contracts_results_1_98_llvm22.json`, `probe_6_miri`) confirms the complete behavioral matrix:

| Miri Run Configuration | Input Validity | Miri Exit Code | Observed Behavior |
| :--- | :--- | :---: | :--- |
| Default (no `-Z contract-checks`) | Valid (`inc_bounded(41)`, `BAD_CONST`) | `0` | Passes (`if false` skips contract intrinsics) |
| Default (no `-Z contract-checks`) | Invalid (`inc_bounded(200)`) | `0` | **Passes silently; contract violation unchecked** |
| `-Z contract-checks=no` | Invalid `requires` (`inc_bounded(200)`) or invalid `ensures` (`ensures_only(true)`) | `0` | **Passes silently; contract violation unchecked** |
| `-Z contract-checks=yes` | **Valid** (`inc_bounded(41)`) | **`1`** | `error: unsupported operation` citing missing `#[miri::intrinsic_fallback_is_spec]` on `contract_check_requires` |
| `-Z contract-checks=yes` | Invalid (`inc_bounded(200)`) | **`1`** | Same `unsupported operation` on `contract_check_requires` (aborts before evaluating condition) |
| `-Z contract-checks=yes` | **Valid** `#[ensures]`-only (`ensures_only(false)`) | **`1`** | `error: unsupported operation` citing missing `#[miri::intrinsic_fallback_is_spec]` on `contract_check_ensures` |

Consequently, the `rc = 1` result observed in the `rustc 1.102.0-nightly` Miri baseline (`support/rustc_1_102_llvm23_baseline.json`, `probe_4_miri_contract_yes`) is **not** Miri catching a contract failure — it is Miri rejecting the `contract_check_requires` / `contract_check_ensures` fallback bodies as unsupported operations whenever `-Z contract-checks=yes` reaches them.

---

### 6. LLVM 22/23 Contract-Driven Return-Range Narrowing, Overflow Deduction, and Tautological Postcondition Folding

`Basis: source + execution + derived`

Compiling `inc_bounded` at `-C opt-level=2` demonstrates how `-Z contract-checks=yes` interacts with LLVM's scalar optimization pipeline across both LLVM `22.1.6` (`rustc 1.98.0-nightly`) and LLVM `23.1.5` (`rustc 1.102.0-nightly`):

```rust
#[unsafe(no_mangle)]
#[requires(x < 100)]
#[ensures(move |ret| *ret == x + 1 && *ret > 0 && *ret <= 100)]
pub fn inc_bounded(x: u32) -> u32 {
    x + 1
}
```

#### 6.1 Default / `-Z contract-checks=no` (5 lines of LLVM IR on both LLVM 22.1.6 and LLVM 23.1.5)

Observed on LLVM `23.1.5` (`rustc 1.102.0-nightly`, `support/rustc_1_102_llvm23_baseline.json`):

```llvm
define dso_local noundef i32 @inc_bounded(i32 noundef %x) unnamed_addr #4 !guid !188 {
start:
  %0 = add i32 %x, 1
  ret i32 %0
}
```

Observed on LLVM `22.1.6` (`rustc 1.98.0-nightly`, `support/probe_rustc_contracts_results_1_98_llvm22.json`):

```llvm
define dso_local noundef i32 @inc_bounded(i32 noundef %x) unnamed_addr #4 {
start:
  %__ret = add i32 %x, 1
  ret i32 %__ret
}
```

With contract checks disabled, MIR constant-folds the HIR-baked `if false` guards before LLVM sees the body; LLVM receives an unguarded wrapping `add i32 %x, 1`, deduces no return range, and attaches neither `nuw` nor `nsw`. Runtime invocation with `x = 200` returns `REQ=201` (`rc = 0`).

#### 6.2 `-Z contract-checks=yes` (14 lines of LLVM IR on both LLVM 22.1.6 and LLVM 23.1.5)

Observed on LLVM `23.1.5` (`rustc 1.102.0-nightly`):

```llvm
define dso_local noundef range(i32 1, 101) i32 @inc_bounded(i32 noundef %0) unnamed_addr #4 personality ptr @rust_eh_personality !guid !194 {
start:
  %_0.i.i = icmp ult i32 %0, 100
  br i1 %_0.i.i, label %_RINvNtCs2F9dQBLtWXO_4core10intrinsics23contract_check_requiresNCNvCsgaVBRbqlPg9_15contracts_probe11inc_bounded0EB12_.exit, label %bb3.i, !prof !195

bb3.i:                                            ; preds = %start
; call core::panicking::panic_nounwind
  tail call void @_RNvNtCs2F9dQBLtWXO_4core9panicking14panic_nounwind(ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) @alloc_4ad7987833f2e907b8b0c3d7691d6e36, i64 noundef 21) #12, !noalias !196
  unreachable

_RINvNtCs2F9dQBLtWXO_4core10intrinsics23contract_check_requiresNCNvCsgaVBRbqlPg9_15contracts_probe11inc_bounded0EB12_.exit: ; preds = %start
  %__ret = add nuw nsw i32 %0, 1
  ret i32 %__ret
}
```

Observed on LLVM `22.1.6` (`rustc 1.98.0-nightly`):

```llvm
define dso_local noundef range(i32 1, 101) i32 @inc_bounded(i32 noundef %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %_0.i.i = icmp ult i32 %0, 100
  br i1 %_0.i.i, label %_RINvNtCs8b4M6GsfcPr_4core10intrinsics22contract_check_ensuresNCNvCs2djAezbpFDZ_15contracts_probe11inc_boundeds_0mEB11_.exit, label %bb3.i, !prof !176

bb3.i:                                            ; preds = %start
; call core::panicking::panic_nounwind
  tail call void @_RNvNtCs8b4M6GsfcPr_4core9panicking14panic_nounwind(ptr noalias noundef nonnull readonly captures(address, read_provenance) @alloc_4ad7987833f2e907b8b0c3d7691d6e36, i64 noundef 21) #13, !noalias !177
  unreachable

_RINvNtCs8b4M6GsfcPr_4core10intrinsics22contract_check_ensuresNCNvCs2djAezbpFDZ_15contracts_probe11inc_boundeds_0mEB11_.exit: ; preds = %start
  %__ret = add nuw nsw i32 %0, 1
  ret i32 %__ret
}
```

#### 6.3 Exact Optimization Chain and Contrast with Non-Tautological `#[ensures]`

1. **Dominating precondition check acts as a sound path-sensitive range guard:** On the fall-through edge of `br i1 %_0.i.i` (since the false arm terminates in `panic_nounwind` + `unreachable`), LLVM's LazyValueInfo / CorrelatedValuePropagation / IPSCCP / FunctionAttrs know `0 <=u %0 <u 100`.
2. **Overflow flags (`nuw nsw`):** Because `%0 <u 100`, `%0 + 1` satisfies both `%0 + 1 < 2^32` (no unsigned wrap, `nuw`) and `0 <=s %0 <s 100 => %0 + 1 <=s 100 <= 2^31 - 1` (no signed wrap, `nsw`), so LLVM strengthens `add i32 %0, 1` to `add nuw nsw i32 %0, 1`.
3. **Complete folding of tautological `#[ensures]`:** Under `0 <=u %0 <u 100`, `*ret == x + 1 && *ret > 0 && *ret <= 100` simplifies to `true`. Notice the length argument to `panic_nounwind`: `i64 noundef 21` matches `len("failed requires check") == 21`, whereas `len("failed ensures check") == 20` is completely absent from the emitted IR (`inc_bounded_has_panic_nounwind_len_20: false`).
4. **Return-value `range(i32 1, 101)` attribute:** Because the only non-diverging return emits `%__ret = add nuw nsw i32 %0, 1` with `%0 in [0, 100)`, LLVM attaches `noundef range(i32 1, 101)` (half-open `[1, 101)`) to the function's return value, exposing the postcondition's range invariant to downstream callers at zero postcondition-checking cost.
5. **Non-tautological `#[ensures]` control (`buggy_early_return`):** On `buggy_early_return(flag: bool) -> u32` (`if flag { return 0; } 42` with `#[requires(true)] #[ensures(|ret| *ret > 0)]`), LLVM `22.1.6` folds the trivial `#[requires(true)]` check away, retains the 20-byte `"failed ensures check"` `panic_nounwind(..., i64 noundef 20)` on the `flag == true` arm (12 lines of IR), and emits `ret i32 42` on the `flag == false` arm (`buggy_early_return_has_panic_nounwind_len_20: true`).

---

### 7. Contrast with Anneal's Static Proof Boundary (`Trusted.MirAst` and `Trusted.MirSemantics`)

`Basis: source + derived`

Inspecting `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` directly shows how a static MIR verifier's specification and trust boundary fundamentally differs from `rustc`'s runtime contract checking:

1. **Fail-closed rejection of `Operand::RuntimeChecks` (`trusted/lean/Trusted/MirAst.lean:33-39, 522-561`):**
   `Trusted.MirAst.Operand` defines only three constructors:
   ```lean
   inductive Operand where
     | copy (place : Place)
     | move (place : Place)
     | constant (c : ConstOperand)
   ```
   Lines `548-556` explicitly document the boundary against upstream `compiler/rustc_middle/src/mir/syntax.rs` (`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):
   > "`Operand::RuntimeChecks(RuntimeChecks)` is crate-dependent and evaluated via a runtime hook rather than a compile-time constant (`compiler/rustc_middle/src/mir/syntax.rs`: 'This is not quite a const since its value can differ across crates within a single crate graph'; `vendor/lean-miri/Miri/Interpreter/OperandMachine.lean` evaluates it via `h.runtimeChecks`). It is intentionally unmodeled in `MirAst.Operand` and must fail closed (be rejected by capture) rather than being folded into a `.constant` boolean."

   Matching this contract, `trusted/correspondence/Trusted/Correspondence.lean:1399-1400` binds `refLocalAccessHooks`'s `runtimeChecks` callback to fail closed:
   ```lean
   runtimeChecks := fun frame state _ =>
     ⟨frame, state, .error (.resolver "runtimeChecks unsupported")⟩
   ```
   Meanwhile, `vendor/lean-miri/Miri/MIR/Syntax.lean:127-131` models all three upstream variants (`UbChecks`, `ContractChecks`, `OverflowChecks`) via a runtime hook (`CompilerIntrinsicFacts.runtimeChecks`) precisely so Miri-correspondence audits can explicitly witness the rejection boundary.

2. **Static mathematical proof obligations vs. runtime guards (`trusted/lean/Trusted/MirSemantics.lean:1751-1808`):**
   Anneal states obligations mathematically over `Runtime(PostCleanup)` MIR without instrumenting the compiled binary:
   - `BodyVerified p defId body safetyPre` requires `getElem? p.bodies defId = some body`, `BodyStaticAdmitted p body = true`, and for every well-typed argument list `args` (assuming `safetyPre args` only when `body.isUnsafe = true`), `WellFormed (entryProgForBody p defId) { args := args }` (never stepping to `FaultKind.undefined` or `FaultKind.unsupported`).
   - `ProgramVerified p specs` lifts `BodyVerified` across all bodies in `p` plus `specs.property p` (functional postconditions or termination).
   - `CrateTheorem c` and `UnitTheorem c` bind whole-crate or proof-unit captures to `ProgramVerified c.program c.specs`.

| Dimension | 2026 `rustc` `#[requires]`/`#[ensures]` (HIR-baked) | Latent `Operand::RuntimeChecks(ContractChecks)` | Anneal Static Obligations (`joshlf/anneal@c131b320e`) |
| :--- | :--- | :--- | :--- |
| **Enforcement mechanism** | Runtime branches + `panic_nounwind` (`SIGABRT`, `rc = -6`) | Deferred runtime boolean materialized at codegen | Lean 4 kernel proof over `Runtime(PostCleanup)` MIR (`WellFormed`, `Specs.property`) |
| **Default behavior** | **Off** (`-Z contract-checks=no`); checks erased in optimized MIR/LLVM | **Unreachable** (`E0093`, unregistered in `check_intrinsic_type`) | Soundness proved statically before execution; zero runtime check overhead |
| **Cross-crate scoping** | Defining crate only (even `#[inline]` & generics) | Caller / monomorphizing crate at codegen | Crate-independent semantics; rejects `Operand::RuntimeChecks` fail-closed |
| **CTFE enforcement** | **Bypassed** (`const_eval_select!` `if const` is no-op) | `CompileTimeMachine::runtime_checks` returns `true`, but `contract_check_*` still no-ops in CTFE | Applies uniformly to modeled MIR bodies independent of runtime/CTFE split |
| **Miri compatibility** | Rejects **all** reached checks at `yes` (missing `#[miri::intrinsic_fallback_is_spec]`) | Supported by `MiriMachine::runtime_checks` (`r.value(sess)`) | `Trusted.Correspondence` bridges `M_anneal` to `vendor/lean-miri` with fail-closed `runtimeChecks` |
| **Exit-path coverage** | Tail, `return`, `?`, `do yeet` checked; `become` and unwind bypassed | Depends on lowering consumer | Covers every reachable MIR terminator (`FaultKind.unsupported` fails closed on unmodeled terminators) |
| **Impact on `Runtime(PostCleanup)` MIR capture** | Leaves dead `if false { contract_check_* }` closures in `PostCleanup` MIR even at `-Z contract-checks=no` | Emits `Operand::RuntimeChecks(ContractChecks)` directly in `PostCleanup` MIR | Unmodeled closure/intrinsic calls or `RuntimeChecks` fail closed during capture/execution |

**Operational capture hazard for Anneal:** If an upstream crate annotates a function with `#[requires]` or `#[ensures]` — even when compiled with default `-Z contract-checks=no` — its `Runtime(PostCleanup)` MIR contains unreachable `bb1`/`bb2`/`bb6` blocks constructing contract closures and calling `contract_check_requires` / `build_check_ensures` / `contract_check_ensures`. Because Anneal captures `Runtime(PostCleanup)` MIR before `SimplifyConstCondition`, either those dead blocks must be unreachable-pruned or explicitly recognized, or capture will reject the body fail-closed.

---

### 8. Kernel-Checked Lean `v4.34.1` Formalization (`support/NativeContractsAndRuntimeChecksSoundness.lean`)

`Basis: derived + execution`

`support/NativeContractsAndRuntimeChecksSoundness.lean` provides a standalone, zero-dependency Lean `v4.34.1` mechanization of the operational semantics, cross-crate scoping duality, multi-exit `ensures` interception, LLVM range/tautology deduction, and static-verification erasure equivalence.

#### 8.1 Semantic Model

- `EvalMode := runtime | ctfe` models `const_eval_select!` in `contract_check_{requires,ensures}`.
- `LoweringMode := hirBaked | deferredRuntimeCheck` and `CrateBuildFlags := { defContractChecks, callerContractChecks }` model the scoping duality between `rustc_ast_lowering/src/contract.rs` (`hirBaked` -> `defContractChecks`) and `Operand::RuntimeChecks(ContractChecks)` (`deferredRuntimeCheck` -> `callerContractChecks`).
- `BodyExpr Ret` inductively models six control-flow constructs: `tail`, `earlyReturn`, `tryResidual` (`?` / `do yeet`), `panicUnwind`, `tailCallBecome` (`become`), and `branch`. `ExitKind.isCheckedNormalExit` returns `true` iff the exit is `tail`, `earlyReturn`, or `tryResidual`, faithfully matching `rustc_ast_lowering/src/contract.rs` and `expr.rs:483-491, 2018, 2070`.
- `evalInstrumented mode lmode flags f x` dispatches to `evalBodyNoCheck` in `.ctfe` mode (modeling `const_eval_select!`) and, in `.runtime` mode with active checks, checks `f.req x` (returning `.abortRequires` on `false`) before executing `evalBodyWithEnsures (f.ens x) (f.body x)`.
- `StaticContractVerified f` states `∀ x, f.req x = true → ∃ r, evalUninstrumented f x = .ok r ∧ f.ens x r = true`.

#### 8.2 Verified Theorems, Constructive Counterexamples, and Kernel Axiom Audit

Verified cleanly with `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, zero warnings, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`):

| Theorem / Counterexample | Formal Statement Summary | `#print axioms` Output |
| :--- | :--- | :--- |
| `verified_contract_erasure_preserves_behavior` | `StaticContractVerified f → f.req x = true → evalInstrumented mode lmode flags f x = evalUninstrumented f x` (all `mode`, `lmode`, `flags`) | `[propext]` |
| `static_verification_iff_erasure_preserves_behavior` | For `become`-free normal-returning functions on valid inputs, `StaticContractVerified f ↔ (∀ x, f.req x = true → evalInstrumented .runtime .hirBaked ⟨true, c⟩ f x = evalUninstrumented f x)` | `[propext]` |
| `ensures_checks_every_normal_exit` | Under active runtime checks and `f.req x = true`, every checked normal exit (`tail`, `earlyReturn`, `tryResidual`) returning `r` yields `.ok r` iff `f.ens x r = true` and `.abortEnsures` iff `f.ens x r = false` | `[propext]` |
| `runtime_ok_implies_req_and_ens` | For any `NoBecomeBypass` body, observing `.ok r` under active runtime checks implies `f.req x = true ∧ f.ens x r = true` | `[propext]` |
| `contract_check_determined_by_defining_crate_flag` | `evalInstrumented mode .hirBaked ⟨defFlag, c₁⟩ f x = evalInstrumented mode .hirBaked ⟨defFlag, c₂⟩ f x` (caller-crate invariance) | `[]` (no axioms) |
| `deferred_runtime_check_tracks_caller_crate_flag` | `evalInstrumented mode .deferredRuntimeCheck ⟨d₁, callerFlag⟩ f x = evalInstrumented mode .deferredRuntimeCheck ⟨d₂, callerFlag⟩ f x` (defining-crate invariance) | `[]` (no axioms) |
| `incBounded_runtime_guarded_return_range` | `evalInstrumented .runtime .hirBaked ⟨true, c⟩ incBounded x = .ok r → 1 ≤ r ∧ r < 101` (soundness of LLVM `range(i32 1, 101)` and `nuw nsw`) | `[propext]` |
| `incBounded_tautological_ensures_folding_sound` | Replacing `incBounded.ens` with `fun _ _ => true` preserves runtime behavior for **all** `x : Nat` (soundness of LLVM's elimination of `"failed ensures check"`) | `[propext]` |
| `ce1_unverified_erasure_misses_precondition_violation` | `incBounded` on `x = 200`: `req 200 = false`, checked returns `.abortRequires`, erased returns `.ok 201`, `.ok 201 ≠ .abortRequires` | `[]` (no axioms) |
| `ce2_ctfe_skipping_requires_evaluates_invalid_const` | `posConstFn` on `x = 0` with `⟨true, true⟩`: `.ctfe` returns `.ok 0` (violating `req` and `ens`), `.runtime` returns `.abortRequires` | `[]` (no axioms) |
| `ce3_unchecked_downstream_caller_relying_on_uninstrumented_upstream_misses_contract` | `upstreamInlineInc` on `x = 50`: `.hirBaked` with `⟨false, true⟩` returns `.ok 51` (miss), `.hirBaked` with `⟨true, false⟩` returns `.abortRequires`, `.deferredRuntimeCheck` with `⟨false, true⟩` returns `.abortRequires` | `[]` (no axioms) |
| `ce4_early_return_caught_vs_become_and_unwind_bypass` | `buggyEarlyReturn true` yields `.abortEnsures`, whereas `tailBecomeBypass ()` yields `.ok 0` despite `ens () 0 = false`, and `panicsBeforeReturn ()` yields `.unwind 1` | `[]` (no axioms) |

## Boundaries

To prevent over-generalization, negative space is classified using the four `reference-corpus/1` boundary categories:

### Known Not to Apply

- **Caller-crate flag inheritance for `#[requires]`/`#[ensures]`:** Unlike `ub_checks()` / `overflow_checks()` in `core`, passing `-Z contract-checks=yes` on a downstream binary crate does **not** enable `#[requires]` or `#[ensures]` checks in upstream dependencies — even on `#[inline]`, `#[inline(always)]`, or generic functions — because AST-to-HIR lowering bakes `self.tcx.sess.contract_checks()` as a boolean literal in the defining crate.
- **CTFE contract enforcement:** `-Z contract-checks=yes` does **not** enforce `#[requires]` or `#[ensures]` during compile-time constant evaluation (`const` / `static` initializers or `const { ... }` blocks) because `const_eval_select!` routes CTFE to the no-op `if const` arm.
- **Miri contract validation under `-Z contract-checks=yes`:** Enabling `-Z contract-checks=yes` under Miri does **not** execute contract checks; it fails unconditionally (`rc = 1`, `unsupported operation`) on both valid and invalid inputs due to the missing `#[miri::intrinsic_fallback_is_spec]` attribute on `contract_check_requires` and `contract_check_ensures`.
- **Universal postcondition checking across `become` and unwinding:** `#[ensures]` does **not** check return values produced via explicit tail calls (`become`, `#![feature(explicit_tail_calls)]`) and does **not** run when a function exits via an unwinding panic.
- **Unverified erasure equivalence:** `verified_contract_erasure_preserves_behavior` applies strictly on precondition-admitted inputs (`f.req x = true`) of statically verified functions; erasing checks without verifying callers does **not** preserve behavior on invalid inputs (`ce1`).

### Unsupported

- **Direct use of `core::intrinsics::contract_checks`:** Unsupported in `rustc` (`error[E0093]`) because `sym::contract_checks` is absent from `library/core` and `check_intrinsic_type` (`rustc_hir_analysis/src/check/intrinsic.rs`).
- **Contracts on `async fn`, `gen fn`, and bodyless trait declarations:** Explicitly rejected by `compiler/rustc_builtin_macros/src/contracts.rs`.
- **Reversed or multiple `#[requires]`/`#[ensures]` attributes on a single function:** Rejected by `compiler/rustc_parse/src/parser/generics.rs`.
- **Non-`Copy` or non-`'static` captures in `#[ensures]`:** Rejected by the `C: Fn(&Ret) -> bool + Copy + 'static` bound on `core::contracts::build_check_ensures`.
- **`Operand::RuntimeChecks` in Anneal (`joshlf/anneal@c131b320e`):** Intentionally unmodeled in `Trusted.MirAst.Operand` and rejected fail-closed (`"runtimeChecks unsupported"`) in `Trusted.Correspondence`.

### Not Examined

- **Non-`x86_64-unknown-linux-gnu` codegen targets** (e.g., `aarch64`, `riscv64`, `wasm32`) and alternative codegen backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`): LLVM IR deduction was observed on `x86_64-unknown-linux-gnu` with `rustc_codegen_llvm` only.
- **LTO / ThinLTO cross-crate range propagation** from a `#[requires]`-guarded upstream function's `range(...)` return attribute into downstream callers: only intra-function LLVM range/overflow deduction and cross-crate check firing were executed.
- **Contract clauses with interior side effects or panics inside the predicate itself** (e.g., a `#[requires]` expression that panics with unwinding or mutates state through interior mutability), and `FnContract.declarations` referencing mutable parameters modified in the body (which in Lean is modeled cleanly via by-value argument capture `f.ens x r`, matching `move |ret| ...`).
- **Trait `impl` method contracts, `extern "C"` ABI functions with contracts, and `#[track_caller]` interaction** with `panic_nounwind`.
- **Direct live execution on `rust-lang/rust@342d74463`:** Audited by source diff against `3ef0c22cd` only; live execution was performed on `14210df0e` (`rustc 1.98.0-nightly`, LLVM `22.1.6`, Miri `0.1.0`) and compared against the recorded `3ef0c22cd` (`rustc 1.102.0-nightly`, LLVM `23.1.5`) execution baseline.

### Unknown

- **Upstream timeline for migrating `rustc_ast_lowering/src/contract.rs` to `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)` and adding `#[miri::intrinsic_fallback_is_spec]`:** Both pieces of partial infrastructure exist in-tree (`lower_intrinsics.rs:29`, `syntax.rs:1594`, `miri/src/intrinsics/mod.rs:62-74`), but whether and when upstream `rust-lang/rust` will switch HIR lowering to deferred runtime checks, enforce contracts in CTFE, or forbid `become` in `#[ensures]` functions is unresolved (`rust-lang/rust#128044`).

### Stronger Conclusions Not Established

- Passing `support/NativeContractsAndRuntimeChecksSoundness.lean` does **not** prove end-to-end equivalence of LLVM `22`/`23` passes or `rustc`'s full MIR/Rust memory model; it mechanizes the abstract operational semantics of `requires`/`ensures` instrumentation, cross-crate flag scoping, CTFE `const_eval_select!` bypass, multi-exit checking, and `inc_bounded`'s arithmetic range/folding properties.
- Observing `range(i32 1, 101)` and tautological `#[ensures]` elimination on `inc_bounded` does **not** guarantee LLVM will fold arbitrary complex `#[ensures]` predicates or narrow ranges across non-linear arithmetic or opaque function calls.

## Evidence

### 1. Primary-Source Citation Ledger

All Git commit SHAs below were resolved and inspected directly against upstream repositories:

- **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11T17:59:24Z; `rustc 1.102.0-nightly`, LLVM `23.1.5`):**
  - `library/core/src/contracts.rs:1-24` — `pub use ...::{contracts_ensures as ensures, contracts_requires as requires}` and `#[lang = "contract_build_check_ensures"] pub const fn build_check_ensures<Ret, C>(cond: C) -> C where C: Fn(&Ret) -> bool + Copy + 'static`.
  - `library/core/src/intrinsics/mod.rs:2654-2701` — `ub_checks()` and `overflow_checks()` (no `contract_checks()` declared).
  - `library/core/src/intrinsics/mod.rs:2711-2749` — `const_allocate`, `const_deallocate`, `const_make_global` carrying `#[miri::intrinsic_fallback_is_spec]`.
  - `library/core/src/intrinsics/mod.rs:2751-2811` — `contract_check_requires` and `contract_check_ensures` using `const_eval_select!` (`if const` no-op; `else` `panic_nounwind`), omitting `#[miri::intrinsic_fallback_is_spec]`.
  - `library/core/src/panicking.rs:219-226` — `#[rustc_nounwind] pub const fn panic_nounwind(expr: &'static str) -> !`.
  - `compiler/rustc_builtin_macros/src/contracts.rs:8-169` — `ExpandRequires`, `ExpandEnsures`, `expand_contract_clause`, `expand_contract_clause_tts` (`async`/`gen` rejection `:75-80`, bodyless rejection `:83-106`, empty-arg error `:140-153`).
  - `compiler/rustc_parse/src/parser/function.rs:127-166` and `compiler/rustc_parse/src/parser/generics.rs:348-391` — `parse_contract`, `parse_contract_requires` (wrapping `precond` in `mk_closure_expr`), `parse_contract_ensures`.
  - `compiler/rustc_ast/src/ast.rs:4068-4085` — `pub struct FnContract { declarations, requires, ensures }`.
  - `compiler/rustc_ast_lowering/src/item.rs:1260-1281` — `lower_fn_body` delegating to `lower_contract`.
  - `compiler/rustc_ast_lowering/src/contract.rs:19-355` — `lower_contract`, `lower_contract_check_just_precond` (`:187`), `lower_contract_check_with_postcond` (`:227`), `wrap_body_with_contract_check` (`:234-276`), `checked_return` (`:280-292`), `inject_ensures_check` (`:295-354`, guard at `:342`).
  - `compiler/rustc_ast_lowering/src/expr.rs:483-491, 2018, 2070` — `Ret`, `Try`, and `Yeet` invoking `self.checked_return(...)`; `Become` (`:488-491`) bypassing `checked_return`.
  - `compiler/rustc_ast_lowering/src/lib.rs:293, 339, 360, 1122-1144` — `ALLOW_CONTRACTS` and `with_new_scopes` saving/clearing `self.contract_ensures`.
  - `compiler/rustc_hir_analysis/src/check/intrinsic.rs:90-92, 635-641` — `sym::contract_checks` listed at `:92`, omitted from `check_intrinsic_type` at `:635`.
  - `compiler/rustc_session/src/options.rs:2479-2480` and `compiler/rustc_session/src/session.rs:1098-1099` — `-Z contract-checks: Option<bool>` defaulting to `false`.
  - `compiler/rustc_middle/src/mir/syntax.rs:1338, 1588-1608` — `Operand::RuntimeChecks(RuntimeChecks)` and `RuntimeChecks::ContractChecks => sess.contract_checks()`.
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs:26-42` — `sym::ub_checks | sym::overflow_checks | sym::contract_checks` lowered to `Operand::RuntimeChecks(op)`.
  - `compiler/rustc_mir_transform/src/lib.rs:244-318, 506-541, 682-696, 698-787, 802-836` — `remap_mir_for_const_eval_select`, `inner_mir_for_ctfe` (`:526`), `run_runtime_cleanup_passes` (`LowerIntrinsics`), `run_optimization_passes`, and `inner_optimized_mir` (`:813`).
  - `compiler/rustc_mir_transform/src/instsimplify.rs:34-37, 471-492`, `gvn.rs:276, 585, 1048, 1056, 1982`, and `simplify_branches.rs:49` — `RuntimeChecks::ContractChecks` preserved through MIR optimization.
  - `compiler/rustc_codegen_ssa/src/mir/operand.rs:1164-1173` — codegen materialization via `checks.value(bx.tcx().sess)`.
  - `compiler/rustc_const_eval/src/interpret/operand.rs:850-853` and `compiler/rustc_const_eval/src/const_eval/machine.rs:981-988` — `CompileTimeMachine::runtime_checks` returning `interp_ok(true)`.
  - `src/tools/miri/src/machine.rs:1448-1453` and `src/tools/miri/src/intrinsics/mod.rs:50-80` — `MiriMachine::runtime_checks` (`r.value(ecx.tcx.sess)`) and `#[miri::intrinsic_fallback_is_spec]` gate.
- **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31T20:13:59Z; `rustc 1.98.0-nightly`, LLVM `22.1.6`, Miri `0.1.0`):**
  - Diffed directly against `3ef0c22cd` for `library/core/src/contracts.rs`, `library/core/src/intrinsics/mod.rs:2686-2739`, `library/core/src/macros/mod.rs:1836-1853`, `compiler/rustc_builtin_macros/src/contracts.rs`, `compiler/rustc_ast_lowering/src/contract.rs`, `compiler/rustc_hir_analysis/src/check/intrinsic.rs:90-92, 697-703`, `compiler/rustc_mir_transform/src/lower_intrinsics.rs`, and `src/tools/miri/src/intrinsics/mod.rs:70-88`.
- **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (2026-11-22T00:04:39Z):**
  - Verified byte-for-byte identical to `3ef0c22cd` on `library/core/src/contracts.rs`, `compiler/rustc_builtin_macros/src/contracts.rs`, and `compiler/rustc_ast_lowering/src/contract.rs`; verified `lower_intrinsics.rs` preserves the `sym::contract_checks => RuntimeChecks::ContractChecks` lowering and `library/core/src/intrinsics/mod.rs:2761-2804` still omits `#[miri::intrinsic_fallback_is_spec]`.
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `trusted/lean/Trusted/MirAst.lean:33-49, 522-561` — `Operand` definition and fail-closed `RuntimeChecks` documentation citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (2026-10-20) and `anneal-rustc-capture` pinning `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (2026-05-30).
  - `trusted/correspondence/Trusted/Correspondence.lean:1391-1404` — `refLocalAccessHooks` rejecting `runtimeChecks` with `.error (.resolver "runtimeChecks unsupported")`.
  - `trusted/lean/Trusted/MirSemantics.lean:1751-1808` — `BodyVerified`, `Specs`, `Crate`, `ProgramVerified`, `CrateTheorem`, `UnitTheorem`.
  - `vendor/lean-miri/Miri/MIR/Syntax.lean:127-131` — `inductive RuntimeChecks | UbChecks | ContractChecks | OverflowChecks`.
- **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, 2026-09-24T17:27:27Z).**

### 2. Preserved Support Artifacts

All executable probes, recorded outputs, and kernel-checked Lean proofs are preserved inside `support/`:

- `support/probe_rustc_contracts.py` — Standalone Python 3.10+ probe harness executing all six empirical campaigns (`probe_1_modes`, `probe_2_cross_crate`, `probe_3_capture_and_syntax`, `probe_4_exit_paths`, `probe_5_ctfe_bypass`, `probe_6_miri`) in isolated `tempfile.TemporaryDirectory()` workspaces with deterministic path scrubbing.
- `support/probe_rustc_contracts_results_1_98_llvm22.json` — Complete live execution output acquired on `2026-11-22` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` / `miri 0.1.0 (14210df0e2 2026-05-31)`.
- `support/rustc_1_102_llvm23_baseline.json` — Scrubbed execution baseline acquired on `rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 2026-11-11)` / LLVM `23.1.5` (with `local_rust_src_commit` `49d734536222bf28bb6d07d885b3a81d145981da`, 2026-09-11), preserving the 5-line vs. 14-line LLVM `23.1.5` IR, runtime `rc = -6` / `rc = 0` matrix, 2×2 cross-crate matrix, `E0597` check, CTFE `rc = 0` check, and Miri `rc = 1` check.
- `support/NativeContractsAndRuntimeChecksSoundness.lean` — Standalone Lean `v4.34.1` formalization and `#print axioms` audit script (zero external imports, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`/`partial def`).

### 3. Recorded Execution Commands

```console
$ python3 support/probe_rustc_contracts.py --output support/probe_rustc_contracts_results_1_98_llvm22.json
# exit 0 (rustc 1.98.0-nightly 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65, LLVM 22.1.6, miri 0.1.0)

$ lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/NativeContractsAndRuntimeChecksSoundness.lean
# exit 0 (Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52)
# 6 theorems depend on no axioms; 6 theorems depend only on [propext]
```

## Revalidation

To cheaply test whether these findings still hold on a newer nightly `rustc`, LLVM release, Miri version, or `joshlf/anneal` revision, execute the following four narrow discriminating checks rather than repeating a full compiler crawl:

1. **Rerun the end-to-end empirical probe on the target nightly toolchain:**
   ```console
   python3 support/probe_rustc_contracts.py --output /tmp/contracts_reval.json
   ```
   Check six discriminator fields in `/tmp/contracts_reval.json`:
   - `probe_1_modes.contract_yes_O2.inc_bounded_mir_signals.has_runtime_checks_contract_checks_postcleanup`: if this flips from `false` to `true`, `rustc` has migrated `#[requires]`/`#[ensures]` from HIR-baked literals to `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)`.
   - `probe_2_cross_crate.up_no_ds_yes.inline.rc` and `up_yes_ds_no.inline.rc`: if these flip from `(0, -6)` to `(-6, 0)`, cross-crate scoping has switched from defining-crate to caller-crate semantics.
   - `probe_3_capture_and_syntax.borrow_capture_e0597.rc` and `raw_contract_checks_intrinsic_e0093.rc`: detects relaxation of `build_check_ensures`'s `+ 'static` bound or registration of `core::intrinsics::contract_checks`.
   - `probe_4_exit_paths.explicit_tail_call_become.runtime_rc`: if this flips from `0` (or compile fails), `rustc` has closed the `become` postcondition bypass.
   - `probe_5_ctfe_bypass.contract_yes.compile_rc`: if this flips from `0` to `1`, CTFE has begun enforcing contract intrinsics instead of taking a `const_eval_select!` no-op.
   - `probe_6_miri.runs.contract_yes_ok.has_fallback_is_spec_error`: if this flips from `true` to `false`, Miri has enabled `#[miri::intrinsic_fallback_is_spec]` (or added a shim) for `contract_check_{requires,ensures}`.

2. **Diff the five load-bearing `rust-lang/rust` source files against `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`:**
   - `library/core/src/contracts.rs`
   - `library/core/src/intrinsics/mod.rs` (`contract_check_requires`, `contract_check_ensures`, `contract_checks`)
   - `compiler/rustc_ast_lowering/src/contract.rs` (check `expr_bool_literal(..., contract_checks())` and `checked_return`)
   - `compiler/rustc_ast_lowering/src/expr.rs` (`ExprKind::Become`)
   - `compiler/rustc_hir_analysis/src/check/intrinsic.rs` (`check_intrinsic_type`)

3. **Re-check the Lean `v4.34.1` formalization and axiom boundary:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/NativeContractsAndRuntimeChecksSoundness.lean
   ```
   Confirm exit code `0` and that `#print axioms` lists no `Classical.choice`, `sorryAx`, or `Lean.ofReduceBool`.

4. **Check `joshlf/anneal` for `RuntimeChecks` or contract-closure admission:**
   Diff `trusted/lean/Trusted/MirAst.lean` (`inductive Operand`), `trusted/correspondence/Trusted/Correspondence.lean` (`refLocalAccessHooks`), and `trusted/rustc-capture/src/` against `c131b320eeeb26ef692e5afd5ec8db49ee518613` to determine whether `Operand::RuntimeChecks` or dead `const false` contract-check blocks remain fail-closed.
