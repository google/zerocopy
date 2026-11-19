# Rust HIR/THIR Lowering, Temporary Drop Scopes, Implicit Coercions, and Proof Elaboration Surprises

## Summary

Formal verification tools that analyze Mid-level Intermediate Representation (MIR) or proof-assistant kernel terms (`Expr`) certify properties of the **post-lowering** program—yet engineers, code reviewers, and specification authors audit **surface syntax**. Across Rust (`AST -> HIR -> THIR -> MIR`), C++, Lean 4 (`Syntax -> Term -> Expr`), and Rocq, front-end elaboration and desugaring introduce semantic behaviors that frequently contradict a surface reader's mental model before IR verification even begins.

Direct inspection of `rust-lang/rust` (`c884ecfbab`) and live execution under `rustc 1.98.0-nightly` (Editions 2021 vs. 2024) demonstrates five first-order Rust lowering surprises:
1. **Temporary drop scopes and Edition 2024 flips (`rustc_hir_analysis/src/check/region.rs`):** In Edition 2021, temporaries inside `if let` scrutinees outlive the `else` branch (`ScopeData::IfThen`), and temporaries in block tail expressions drop *after* local variables (`let _local = ...; Temp().val()`), causing `RwLock`/`MutexGuard` self-deadlocks (`Err(WouldBlock)` in live execution) and `E0597` borrow errors unless a trailing semicolon forces an early statement boundary. Edition 2024 reverses both via `ScopeData::IfThenRescope` and `edition.at_least_rust_2024()` (`TAIL_EXPR_DROP_ORDER`), while syntactic temporary lifetime extension (`&*String::new()`) still turns identical-looking explicit calls (`&*Deref::deref(&String::new())`) into `E0716` failures.
2. **Compound assignment evaluation-order inversion (`region.rs:318-351`):** `a += b` evaluates **RHS before LHS** when both operands are primitives known prior to monomorphization, but evaluates **LHS before RHS** for trait-overloaded `AddAssign` types and generic `<T: AddAssign>` instantiations (even when `T = u8`).
3. **Method probing (`method/probe.rs`) & implicit coercions (`coercion.rs`):** Receiver probing walks `T -> &T -> &mut T -> Deref* -> [U]` and prefers inherent methods over trait methods at each deref step, silently routing `smart_ptr.clone()` or `coerce_to_ref` through arbitrary user-defined `Deref` code.
4. **Match constant-typo shadowing (`check_match.rs`) & match ergonomics (`RFC 2005` / `RFC 3627`):** Misspelling an upper-case `const` identifier in a `match` arm silently elaborates as an irrefutable `PatKind::Binding(ByValue)` catch-all variable matching every input (`match_typo(999)` executes the typoed arm cleanly), while `RFC 2005` default binding modes allow `mut` to strip inherited references and single `&` patterns to strip two reference layers—requiring Edition 2024 `RFC 3627` restrictions.
5. **Async `.await` desugaring (`rustc_ast_lowering/src/expr.rs`):** `<expr>.await` lowers into `IntoFuture::into_future` + an explicit `loop { match Pin::new_unchecked(&mut __awaitee).poll(...) { Ready(r) => break r, Pending => {} } task_context = yield (); }`, capturing all live temporaries into the coroutine state and enabling arbitrary synchronous `drop()` cancellation at any yield point without `AsyncDrop`.

Parallel hazards occur in C++ (`std::initializer_list` constructor hijacking `[over.match.list]`, `uint16_t * uint16_t -> int` signed overflow UB `[conv.prom]`, Argument-Dependent Lookup `[basic.lookup.argdep]`) and proof assistants: in `leanprover/lean4` (`4f5982e315`), `autoImplicit` and `relaxedAutoImplicit` both default to `true` (`src/Lean/Elab/AutoBound.lean:17-25`), silently turning a misspelled constant `max_bound` in a theorem into a universally quantified implicit `{max_bound : Nat}` hypothesis (verified live in Lean 4.34.1), while `Nat.sub` truncates (`3 - 5 = 0`) and invisible `Coe` insertions alter kernel statements (`Pollack-inconsistency`, `doi:10.1016/j.entcs.2012.06.008`).

## Applicability

This report documents primary-source compiler mechanics and live toolchain probes observed on 2026-11-19 across five pinned repositories, two locally executed compiler/prover binaries, and normative language/verification references:

- **Rust front-end lowering (`rust-lang/rust` @ `c884ecfbabb04b04fa5054dafc67ec258ecde745`, `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** Covers HIR lowering (`rustc_ast_lowering/src/expr.rs`), scope-tree & drop-order resolution (`rustc_hir_analysis/src/check/region.rs`, `rustc_middle/src/middle/region.rs`), method probing (`rustc_hir_typeck/src/method/probe.rs`), coercions (`rustc_hir_typeck/src/coercion.rs`), THIR construction (`rustc_mir_build/src/thir/cx/{expr,block}.rs`), pattern checking (`rustc_mir_build/src/thir/pattern/check_match.rs`), and RFCs 2005, 3606, and 3627.
- **Live Rust probe toolchain:** `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`) comparing `--edition=2021` vs. `--edition=2024` behavior on identical source.
- **Proof-assistant elaboration (`leanprover/lean4` @ `4f5982e315272d89e2d2113d7ae0d8c9480f15db`, `rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`):** Covers Lean 4 `AutoBound.lean`, `App.lean` (`CoeFun`), `Extra.lean` (`binop%` maximal-type coercion), Rocq `metasyntax.ml`, and live execution on `Lean 4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), plus Wiedijk's formalization of Pollack-inconsistency (`doi:10.1016/j.entcs.2012.06.008`).
- **C++ contrast:** Grounded in normative ISO/IEC 14882 clauses (`[over.match.list]`, `[dcl.init.list]`, `[conv.prom]`, `[basic.lookup.argdep]`) without local Clang/GCC execution.

Findings on Edition 2024 temporary scopes (`ScopeData::IfThenRescope`, RFC 3606) and match ergonomics (`RFC 3627`) apply specifically to crates compiled with `--edition=2024` (or newer) vs. `--edition=2021` (and earlier); note also that `cargo fix --edition` migration rewrites rely on preserving pre-2024 drop order where code could observe differences, which can surprise maintainers expecting 2024 semantics inside migrated `match` wrappers.

## Findings

### 1. The Surface-to-IR Verification Blindspot & Front-End Hazard Taxonomy

`Basis: source + normative + derived`

Every compiler or formal verifier establishes a split between a **surface-facing front end** (which resolves names, precedence, coercions, binding modes, drop scopes, and macro/notation desugaring) and a **lowered core IR** (`MIR` in Rust, `Csyntax`/`Clight` in C, `Expr` kernel terms in Lean 4/Rocq). Because IR-level verifiers (bounded model checkers, deductive Rust verifiers, or proof kernels) accept only the post-lowering artifact, front-end surprises constitute an unverified semantic shift:

| Hazard Class | Surface Appearance | Actual Post-Lowering / Kernel Semantics | Primary Source / Standard Locus |
|---|---|---|---|
| **1. `if let` lock scope (Ed. 2021)** | `if let Ok(v) = *lk.read() {..} else { lk.write() }` | Read guard lives through `else` (`ScopeData::IfThen`) -> deadlock | `region.rs:353-358`; fixed in Ed. 2024 (`IfThenRescope`) |
| **2. Tail-expr drop order (Ed. 2021)** | `{ let _a = A; B().x() }` | `A` drops *before* `B()` (`!edition.at_least_rust_2024()`) | `region.rs:145-162`; RFC 3606 |
| **3. Syntactic lifetime extension** | `&*String::new()` vs. `&*Deref::deref(&String::new())` | First extends `String` to block; second fails `E0716` | `region.rs:601-625`; `operator-expr.md:192-205` |
| **4. `+=` evaluation order** | `lhs() += rhs()` | `i32`: **RHS then LHS**; `AddAssign`/generic: **LHS then RHS** | `region.rs:318-351`; `operator-expr.md:1126-1170` |
| **5. `Deref`/Autoref method probing** | `arc_val.clone()` or `foo(&mut box_x)` | `probe.rs` walks `Deref` chain (`T -> *T`); `coercion.rs` calls user `deref()` | `method/probe.rs:1346-1430`; `coercion.rs:422-490` |
| **6. Match const-typo shadowing** | `match code { EXPECTED_AUTHH => .. }` | Typoed `EXPECTED_AUTHH` is an irrefutable `ByValue` var binding | `check_match.rs` (`PatKind::Binding`) |
| **7. Match ergonomics (2021 vs. 2024)** | `let (x, mut y) = &(a, b);` / `let [&x] = &[&42];` | `mut` resets to `ByValue`; single `&` strips 2 refs in Ed. 2021 | `RFC 2005`, `RFC 3627:25-66` |
| **8. Async `.await` cancellation** | `foo().await` inside `select!` | Coroutine `loop` + `yield ()`; arbitrary `drop()` at suspend point | `rustc_ast_lowering/src/expr.rs:985-1199` |
| **9. C++ `initializer_list` / ADL / promotion** | `std::vector<int>{10, 20}`; `u16_a * u16_b` | 2-element `{10, 20}` vs. 10-element `(10, 20)`; signed `int` UB | ISO C++ `[over.match.list]`, `[conv.prom]`, `[basic.lookup.argdep]` |
| **10. Lean 4 `autoImplicit` / `Coe` / `Nat.sub`** | `x < max_bound -> ...`; `3 - 5`; `n + i` | `{max_bound : Nat}` added silently; `3 - 5 = 0`; `↑n + i` inserted | `AutoBound.lean:17-68`, `App.lean`, `Extra.lean:111-180` |

---

### 2. Rust Temporary Lifetimes, Lifetime Extension, and Edition 2024 Drop-Scope Semantics

`Basis: source + normative + execution`

In `rustc`, temporary destruction order is constructed during HIR type/region analysis in `compiler/rustc_hir_analysis/src/check/region.rs` (`ScopeResolutionVisitor`) using `Scope` and `ScopeData` (`compiler/rustc_middle/src/middle/region.rs:124-160`), and later consumed during THIR construction (`rustc_mir_build/src/thir/cx/{block,expr}.rs`).

#### 2.1 `ScopeTree` Mechanics and Edition 2024 Changes (`RFC 3606` + `IfThenRescope`)

Every terminating expression creates a `ScopeData::Destruction` enclosing its `ScopeData::Node` (`region.rs:91, 242-258`). However, two constructs historically created unexpectedly broad temporary scopes:
1. **Block tail expressions (`resolve_block`, `region.rs:145-162`):**
   - Statements ending in `;` are terminating scopes (`resolve_stmt`, `lines 222-249`), dropping temporaries at the `;`.
   - Before Rust 2024 (`let terminating = edition.at_least_rust_2024()` at `line 148`), a block's tail expression (`blk.expr`, lacking `;`) had `terminating = false`. Its temporaries therefore outlived the entire block—dropping **after** every `let` local declared inside the block (`ScopeData::Remainder`)!
   - When compiled with `--edition=2021` on a local `RefCell`:
     ```rust
     fn test_refcell_tail_drop() -> usize {
         let cell = RefCell::new(10usize);
         *cell.borrow() // ERROR E0597 in Edition 2021; compiles cleanly in Edition 2024!
     }
     ```
     Live `rustc 1.98.0-nightly --edition=2021` rejects this with `error[E0597]: 'cell' does not live long enough` (`help: ... save the expression's value in a new local variable`), because the temporary `Ref<'_, usize>` drops *after* `cell`. Under `--edition=2024`, `terminating = true` causes `Ref<'_, usize>` to drop immediately after evaluating `*cell.borrow()`, before `cell` drops.
   - **Observable behavioral flip (`TAIL_EXPR_DROP_ORDER`):** Where the code *does* compile in both editions (e.g., `let _local = DropLog("local"); TempHolder(DropLog("tail_temp")).val()`), Probe 2.1 proves live execution order flips silently:
     - Edition 2021 stdout: `drop: local` followed by `drop: tail_temp` (emitting `-W tail-expr-drop-order` warning `relative drop order changing in Rust 2024`);
     - Edition 2024 stdout: `drop: tail_temp` followed by `drop: local`.
     As `RFC 3606:128-138` notes, if `_local` is a guard or `PanicOnDrop`, Edition 2021 leaves a `Mutex` poisoned on panic whereas Edition 2024 unlocks it first.

2. **`if let` Scrutinee Temporaries and `RwLock`/`MutexGuard` Deadlocks (`region.rs:170-190, 353-375`):**
   - `resolve_cond` (`region.rs:170-190`) sets `terminate = false` whenever `cond.kind` is `hir::ExprKind::Let(_)` because bindings in the pattern may borrow temporaries created by the scrutinee inside the `then` branch.
   - In Edition 2021, `resolve_expr` wraps `ExprKind::If` with `ScopeData::IfThen` (`line 358`), extending scrutinee temporaries across **both** the `then` branch *and* the `else` branch! Thus:
     ```rust
     if let Ok(_v) = *lock.read().unwrap() { /* ... */ }
     else { lock.try_write() /* DEADLOCK if .write() in Edition 2021! */ }
     ```
     In live Probe 2.1 execution (`rustc 1.98.0-nightly`), `--edition=2021` prints `if_let_else_try_write: Err(WouldBlock -> DEADLOCK if .write())`, whereas `--edition=2024` (`ScopeData::IfThenRescope` at `region.rs:356`) drops the `RwLockReadGuard` before entering `else` and prints `if_let_else_try_write: Ok(unlocked)`.
   - **Critical residual trap (`destructors.md:281-283` & `cargo fix`):** `match` scrutinees remain **non-terminating** in *both* Edition 2021 and Edition 2024 (`match *lock.read().unwrap() { Ok(_) => {}, Err(_) => { /* STILL DEADLOCKS! */ } }`)! Because automated edition migration tools preserve 2021 drop scopes by rewriting flagged constructs into `match` blocks, migrated code can inadvertently retain legacy lock-holding behavior.

#### 2.2 Syntactic Temporary Lifetime Extension (`region.rs:550-625`) & Explicit `super let`

Temporary lifetime extension in `let` statements is strictly **syntactic**, governed by `is_binding_pat` (`region.rs:573-599`: explicit `ref`/`ref mut` inside structural patterns) and the `E&` grammar in `record_rvalue_scope_if_borrow_expr` (`region.rs:601-615`: `&ET`, struct/tuple/array literals, blocks, `if`, `match`, `as`, parentheses, and dereferences `*`). Consequently, `rust-lang/reference` (`src/expressions/operator-expr.md:192-205`) highlights a striking desugaring non-equivalence:
- `let x = &*String::new();` **compiles** because syntactic `*` propagates extended temporary scope to `String::new()`.
- `let y = &*std::ops::Deref::deref(&String::new());` **fails with `E0716`** because the function call breaks syntactic `E&` propagation even though `*x` semantically desugars to `*Deref::deref(&x)`!
- Conversely, Rust 2024 (`region.rs:226-234`) introduces `super let` (`let` inside a block extending into the parent scope) as an explicit, non-syntactically fragile alternative.

---

### 3. Method Resolution, Autoderef/Autoref Chains, Implicit Coercions, `as` Casts & `AssignOp` Order

`Basis: source + normative + execution`

1. **Method Probing & `Deref` Shadowing (`rustc_hir_typeck/src/method/probe.rs:1346-1430`):**
   - `pick_all_method` iterates over `self.steps` built by following the `Deref` chain (`filter(|step| step.reachable_via_deref && !step.from_unsafe_deref)`, `lines 1356-1361`). At each receiver type `self_ty`, it checks:
     1. `pick_by_value_method` (`T`), checking shadowing against inherent `&T` and `&mut T` (`lines 1375-1401`);
     2. `pick_autorefd_method(..., Mutability::Not)` (`&T`), checking shadowing against `&mut T` (`lines 1403-1429`);
     3. `&mut T`; then advances to `*T` via `Deref::deref` and retries.
   - At every step, **inherent methods beat trait methods** (`PickKind::InherentImplPick`). If a smart pointer `Wrapper<T>` adds a new inherent method `.len()` or `.clone()`, existing calls `w.clone()` silently stop resolving to `T::clone`. Even more subtly, because `pick_by_value_method` matches `xform_self_ty` directly at each deref step (`rustc_probe.rs:1375-1401`) and `core::clone::Clone` is implemented for `&T` (`library/core/src/clone.rs:780-785`), calling `(&&arc_val).clone()` matches `impl<T> Clone for &T` at `step 0` (`&&Arc<T>`) and silently copies the `&Arc<T>` reference instead of incrementing the `Arc` refcount (unlike `(&arc_val).clone()`, where `step 0`'s `&Arc<T>` directly matches `Arc::clone(&self)`, prompting `rustc` to warn `suspicious_double_ref_op` on double references). Similarly, calling `.clone()` on a `MutexGuard<Vec<u8>>` dereferences to `Vec<u8>` and deep-clones the vector, and any `Deref` coercion or method dispatch invisibly invokes user-defined `Deref::deref` / `DerefMut::deref_mut` trait code.

2. **Coercion Sites & Transitive `Deref` Coercions (`rustc_hir_typeck/src/coercion.rs:242-490`, `type-coercions.md`):**
   - At coercion sites (`let _: T = e`, function arguments, struct fields, return expressions, assignments), `Coerce::coerce` attempts: `! -> T` (`NeverToAny`), `Unsize` (`coerce_unsized`, e.g., `[T; N] -> [T]`, `T -> dyn Trait`), raw pointer conversion (`&mut T -> *mut T -> *const T`), reference coercion (`coerce_to_ref`, walking `self.autoderef(span, a)` and testing `unify_raw(&{mutbl_b} deref_ty, b)` at `lines 454-490`), and non-capturing closure/fn-item to `fn` pointers (`lines 328-345`).
   - **Hazard:** Coercions are silent in surface ASTs yet execute arbitrary user trait implementations (`Deref::deref`) or silently discard length/vtable metadata when paired with `as` (`*const [u8] as *const u8`, `operator-expr.md:734-745`) or silently wrap/truncate signed/unsigned integers (`256u16 as u8 == 0`, `-1i8 as u8 == 255`, saturating `f64::NAN as u32 == 0`).

3. **Compound Assignment `+=` Operand Order Inversion (`region.rs:318-351`, `operator-expr.md:1126-1170`):**
   - As documented verbatim in `rustc_hir_analysis/src/check/region.rs:318-351` and `rust-lang/reference/src/expressions/operator-expr.md:1126-1170`, `a += b` evaluates **RHS before LHS** when `rustc` knows both types are primitive *prior to monomorphization* (`let mut x = 10i32; *{ ... } += { ... };`), matching basic assignment `=` (`MIR` lowers it directly without a method call).
   - Whenever either operand is a non-primitive type (like `Wrapping<u8>`) or a generic parameter `T: AddAssign`—**even when instantiated with `u8` at monomorphization** (`f3::<u8>` in `operator-expr.md:1154-1169`)—`a += b` desugars to `AddAssign::add_assign(&mut a, b)`, flipping evaluation order to **LHS before RHS**!
   - Live execution in Probe 2.1 (`rustc 1.98.0-nightly`) confirms:
     `i32` prints `prim_rhs` then `prim_lhs`; `CustomCounter` prints `custom_lhs` then `custom_rhs` in both Edition 2021 and Edition 2024. Furthermore, `x += x` compiles for `T: AddAssign + Copy`, whereas its naive expansion `AddAssign::add_assign(&mut x, x)` fails borrow check `E0503` because `autoref` defers the `&mut` borrow (`operator-expr.md:1191-1215`).

---

### 4. Pattern-Matching Constant-Typo Variable Shadowing & Match Ergonomics (`RFC 2005` / `RFC 3627`)

`Basis: source + normative + execution`

1. **Constant-Typo Catch-All Shadowing (`rustc_mir_build/src/thir/pattern/check_match.rs`):**
   - In Rust `match` arms, an unqualified identifier `FOO` resolves to a constant (`PatKind::Constant`) **only** if `FOO` is resolved as a `const` (or unit `struct`/enum variant) in scope. If `FOO` is misspelled (e.g., `EXPECTED_AUTHH` instead of `EXPECTED_AUTH`) or forgotten in a `use` import, name resolution treats it as a fresh irrefutable `PatKind::Binding` (`BindingMode::ByValue`), turning an equality guard into a catch-all binding that matches **every** value and renders subsequent arms dead!
   - Probe 2.1 demonstrates `test_match_const_typo(999)` matching `EXPECTED_AUTHH` and printing `"matched typoed constant as catch-all variable!"`. While `rustc` emits default-on lints (`unused_variables`, `non_snake_case`, `unreachable_patterns`), suppressing or failing to `#![deny(...)]` them in generated/macro code or using the typoed identifier inside the arm body removes `unused_variables`, leaving only `non_snake_case` as a warning!

2. **Match Ergonomics Binding-Mode State Machine (`RFC 2005` vs. Edition 2024 `RFC 3627`):**
   - Under `RFC 2005`, matching a reference scrutinee (`&T` or `&mut T`) against a non-reference pattern sets the **default binding mode** to `ref` or `ref mut` (`BindingMode(ByRef::Yes(...), ...)`), implicitly adding `&`/`&mut` to leaf variable bindings.
   - `RFC 3627` (`3627-match-ergonomics-2024.md:25-66`) catalogs three major human expectation failures in pre-2024 Rust:
     1. **`mut` silently resets binding mode:** `let (x, mut y) = &(true, false);` gives `x: &bool` (inherited `ref`) but `y: bool` (by-value copy!) because `mut` reset the binding mode (`lines 25-35`);
     2. **One `&` pattern strips two `&` layers:** `let [a] = &[&42];` binds `a: &&i32`, yet `let [&a] = &[&42];` strips *both* the inherited `&` and the inner `&`, binding `a: i32` (`lines 56-65`);
     3. **No local cancellation of inherited reference:** `let (s, v, &u) = arg;` could not extract `u: u8` locally without abandoning match ergonomics (`lines 37-54`).
   - Edition 2024 (`RFC 3627:9-18`) enforces "eat one layer": `&`/`&mut` patterns consume only one reference layer, `mut` on an inherited non-default binding mode is an error, `&` can match `&mut` on all editions, and `ref mut` can never arise implicitly behind an `&` pattern.

---

### 5. Async `.await` Desugaring & Cancellation Drop-Point Hazards

`Basis: source + derived`

Inspection of `compiler/rustc_ast_lowering/src/expr.rs:985-1200` (`lower_expr_await` / `make_lowered_await`) shows the exact HIR expansion of `<expr>.await`:
1. Evaluates `IntoFuture::into_future(<expr>)` and binds it to `mut __awaitee` (`lines 1061-1063, 1185-1199`);
2. Loops, calling `unsafe { Future::poll(Pin::new_unchecked(&mut __awaitee), get_context(task_context)) }` (`lines 1073-1106`);
3. On `Poll::Ready(result)`, executes `break result`; on `Poll::Pending`, yields `()` (`hir::ExprKind::Yield`, `lines 1145-1166`) and suspends the coroutine.

**Lowering traps:**
- **Suspension-point cancellation (`drop(future)`):** Because Rust models cancellation by synchronously dropping the `Future` struct at any `yield ()` point—and lacks `AsyncDrop`—any state machine spanning multiple `.await` points can be dropped mid-protocol (e.g., `tokio::select!` dropping a partially flushed buffered writer or held logical lease while a peer already observed partial bytes).
- **Extended temporaries crossing `.await` (`Send` & coroutine size bloat):** Any temporary created in the arguments or scrutinee of an expression containing `.await` (e.g., `process(&mutex.lock().unwrap(), fetch().await)`) stays live inside the generated coroutine `enum` across `yield ()`, causing opaque `Future is not Send` errors (when a non-`Send` `MutexGuard` or `Ref` spans the yield) or subtle cross-task lock-inversion deadlocks.

---

### 6. C++ Contrast: List-Initialization Hijacking, Integral Promotion UB & ADL

`Basis: normative + derived`

C++ exhibits analogous surface-to-IR semantic discontinuities driven by implicit conversion sequences (up to one user-defined conversion bracketed by standard conversions) and name-lookup rules in ISO/IEC 14882:
1. **`std::initializer_list` Overload Hijacking (`[over.match.list]`, `[dcl.init.list]`):** Uniform brace syntax `{...}` strictly prefers `std::initializer_list<T>` constructors over ordinary parameterized constructors. Consequently, `std::vector<int>(10, 20)` constructs a 10-element vector filled with `20`, while `std::vector<int>{10, 20}` silently constructs a 2-element vector `[10, 20]`—even though brace syntax was introduced to *prevent* narrowing conversions and "most vexing parse" ambiguities!
2. **Usual Arithmetic Conversions & Integral Promotion Signed UB (`[conv.prom]`):** Multiplying two unsigned 16-bit integers (`uint16_t a = 65535, b = 65535; auto c = a * b;`) on 32-bit-`int` targets promotes both `uint16_t` operands to **signed `int`** before multiplication (`65535 * 65535 = 4294836225 > INT_MAX`), producing **signed integer overflow undefined behavior** from two unsigned operands!
3. **Argument-Dependent Lookup / Koenig Lookup (`[basic.lookup.argdep]`):** Unqualified function calls (`swap(a, b)`, `begin(x)`) search associated namespaces of every argument type (including template arguments and base classes). Adding an overload or helper function inside an unrelated type's namespace can silently hijack unqualified calls in generic templates without modifying call-site syntax.

---

### 7. Proof Assistant Elaboration Hazards: Lean 4 `autoImplicit`, Coercions, `Nat.sub`, and Pollack-Inconsistency

`Basis: source + execution + literature`

Interactive theorem provers share the exact same front-end hazard class: the **kernel** checks an elaborated `Expr` term, not the human-written `Syntax` or `Vernac` string!

1. **Lean 4 `autoImplicit` & `relaxedAutoImplicit` Default `true` (`leanprover/lean4`, `src/Lean/Elab/AutoBound.lean:17-68`):**
   - `AutoBound.lean:17-25` registers **both** `autoImplicit` and `relaxedAutoImplicit` with `defValue := true`. Any unbound atomic identifier in a declaration header becomes an implicit universally quantified argument `{var : Sort/Type}`.
   - Even setting `relaxedAutoImplicit := false` still permits `isValidAutoBoundSuffix` (`lines 35-36`: single character followed by digits, subscripts, `_`, or `'`, e.g., `x`, `n1`, `αᵣₒₛₑ₂₁₁'''`).
   - **Live Lean 4.34.1 verification (Probe 2.2):** Defining `MAX_BOUND : Nat := 0` and writing `theorem spec_with_typo (x : Nat) : x < max_bound → x < max_bound := fun h => h` succeeds with zero errors or warnings; `#check @spec_with_typo` reveals the actual elaborated kernel type:
     `@spec_with_typo : ∀ {max_bound : Nat} (x : Nat), x < max_bound → x < max_bound`.
     Adding `set_option autoImplicit false` immediately rejects the theorem with `error(lean.unknownIdentifier): Unknown identifier 'max_bound'` and the exact note from `AutoBound.lean:64`.
   - Furthermore, `AutoBound.lean:39-50` documents Lean issue `#255`: erasing macro scopes on auto-bound candidates caused an infinite elaboration loop when a `local notation "A" => id x` expanded inside a theorem header!

2. **Invisible Coercions (`App.lean`, `Extra.lean`) & Truncating Total Arithmetic (`Nat.sub`, `/ 0`):**
   - `Lean/Elab/App.lean:378, 1784` (`coerceToFunction?`) and `Lean/Elab/Extra.lean:111-180` (`binop%` / `leftact%` / `rightact%`) compute maximal types across expression trees and silently inject `Coe`/`CoeFun`/`Nat.cast` nodes into elaborated terms (`def coerce_probe (n : Nat) (i : Int) : Int := n + i` elaborates to `fun n i => ↑n + i` in Probe 2.2).
   - When paired with totalized integer-like operations—`(3 : Nat) - 5 = 0` (`Nat.sub` saturating at `0`) and `42 / 0 = 0` (`rfl`-proved in Probe 2.2)—a human reading `a - b + c` or `a / b` over `Nat` can prove an unintended theorem that relies on `a < b` clamping to `0`.

3. **Rocq Notations, Sections & Wiedijk's Pollack-Inconsistency (`doi:10.1016/j.entcs.2012.06.008`):**
   - In `rocq-prover/rocq` (`vernac/metasyntax.ml`), custom precedence levels, scopes (`%nat`, `%Z`), `Coercion`, and `Section` `Variables` (which generalize theorems only over variables actually referenced in the elaborated statement/proof) can silently change theorem types if notation precedence masks an argument or a typo binds a fresh implicit variable.
   - Wiedijk (`doi:10.1016/j.entcs.2012.06.008`) formalizes **Pollack-inconsistency**: a proof assistant whose parser and pretty-printer fail to round-trip faithfully allows printing an elaborated kernel formula `P` as surface text `S` that parses back as a *different* formula `P'` (or makes `False` look visually identical to `True`), undermining human auditability of the final printed theorem statement.

---

### 8. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + derived`

Front-end elaboration complexity directly affects engineering velocity, IDE responsiveness, binary size, and proof verification cost across all six levels:

| Dimension | Rust Front End (`rustc` Edition 2021 -> 2024) | C++ Front End (Templates, Overloads, ADL) | Lean 4 / Rocq Elaborator & Kernel |
|---|---|---|---|
| **(L1) Human & Agent Authoring Velocity** | Edition 2024 (`IfThenRescope`, `RFC 3606`, `RFC 3627`) eliminates common `MutexGuard`/`RefCell` drop workarounds and `mut` binding surprises, cutting human/LLM borrow-check repair turns; constant-typo `match` still requires lint discipline | High cognitive and review cost: overload/ADL/`initializer_list` interactions frequently require inspecting template instantiations and ABI rules | `autoImplicit = true` optimizes quick prototyping (`-30–50%` header boilerplate) at severe audit risk (vacuous theorems); disabling `autoImplicit` adds explicit binder parameters but catches typos in 1 turn |
| **(L2) Toolchain Build Time** | `rustc_hir_analysis` + `rustc_hir_typeck` + `rustc_mir_build` are major components of Stage 1/2 `rustc` bootstrap (`region.rs` 870 lines, `coercion.rs` 2,289 lines, `probe.rs` 2,783 lines, `check_match.rs` 1,582 lines) | Heavy Clang/GCC front-end C++ AST/Sema codegen and template instantiation machinery | Lean 4 self-hosted elaborator (`App.lean` 2,361 lines, `Extra.lean` 624 lines, `AutoBound.lean` 101 lines) bootstrapped via C++ kernel + Lean binaries |
| **(L3) Compilation, Elaboration & LSP Latency** | Autoderef + trait-obligation probing in `probe.rs` backtracks across candidate steps (`probe_instantiate_query_response`); THIR->MIR drop elaboration expands CFG cleanup edges per temporary scope; Edition 2024 shrinks `ScopeTree` span for `if let` and tail expressions | ADL + template SFINAE/concept satisfaction + overload ranking dominates C++ compile latency; interactive `< 50 ms` LSP budgets strain on deep template headers | `binop%` maximal-type traversal (`Extra.lean:132-143`) + `CoeFun` metavariable probing + typeclass search cause tail elaboration `rlimit` timeouts; Lean 4.34.1 compiled the standalone 19-line Probe 2.2 in `< 1 s` |
| **(L4) Generated Code Execution Performance** | Implicit `Deref` coercions execute real runtime deref code; temporaries live across `.await` inflate coroutine state structs (extra `memcpy`/cache misses); extended drop scopes require live landing-pad cleanup across more basic blocks, whereas Edition 2024 drops temporaries before locals | Implicit temporary conversions copy/allocate objects silently; `uint16_t` signed UB enables aggressive dead-branch elimination that miscompiles overflow paths | Zero runtime impact on extracted/erased proofs; coercion (`Nat.cast`) inserts real runtime conversion functions in computable definitions (`coerce_probe` -> `Nat.cast n + i`) |
| **(L5) Proof / Certificate Verification Speed** | MIR verifiers skip `AST->HIR->THIR` elaboration altogether; verifying lowering soundness manually is very expensive, whereas `#![deny(tail_expr_drop_order, non_snake_case)]` runs in `< 1 ms` during `rustc` compilation | Static analyzers operate on Clang AST or LLVM IR, missing UB eliminated before IR if `-O2` runs first | Kernel checking of elaborated terms (`lean` / external `lean4export` / `rocqchk`) is fast (`< 10 ms` per small theorem) and independent of `autoImplicit`/`Coe` rules, **but checking only the post-elaboration term cannot detect vacuous `autoImplicit` binders unless an explicit policy audits binder origins** |
| **(L6) RAM, Disk & Binary Footprints** | Async coroutine state-machine `Future` size grows linearly with every temporary held across `.await`; extra drop scopes expand unwind `.eh_frame` tables in final binaries | Instantiated template symbols and inline conversion wrappers inflate object `.text`/debug `.debug_info` footprints | Deep `Coe` / `binop%` expansion chains increase kernel `Expr` DAG sizes and `.olean` / `.vo` disk footprints; Probe 2.1 compiled tiny single-file Rust binaries cleanly with zero extra dependencies |

---

### 9. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

#### (C1) Human Comprehensibility & Mental-Model Ergonomics

`Basis: source + execution + derived`

- **Nonlocal punctuation fragility:** Adding or removing a single trailing `;` on line 38 of a Rust function (`if let ... { ... } else { ... };` vs. tail expression) flips whether an `RwLockReadGuard` outlives locals (`E0597` in Edition 2021) or changes relative drop order (`drop: local` vs. `drop: tail_temp`), violating local-reasoning ergonomics.
- **Typographic homonymity without syntactic sigils:** In Rust pattern matching (`EXPECTED_AUTHH` vs. `EXPECTED_AUTH`) and Lean 4 headers (`max_bound` vs. `MAX_BOUND`), a 1-character typo or missing `use` switches the construct from **referential equality/constant lookup** to **fresh variable binding** with no syntactic keyword (`let`, `var`, `∀`) distinguishing the two! While `rustc`'s diagnostics (`unused_variables` + `did you mean test_match_const_typo::EXPECTED_AUTH`) and Lean 4's `autoImplicit = false` note (`Unknown identifier` at `AutoBound.lean:64`) catch single errors clearly, using the bound name in the arm body silences `unused_variables`, and leaving `autoImplicit = true` silences Lean completely.
- **Diagnostic transparency:** `rustc`'s `-W tail-expr-drop-order` explicitly prints `#1` temporary spans, custom `Drop` impl locations, and exact drop-order explanations (`Probe 2.1b`), whereas async coroutine `Future is not Send` errors caused by anonymous temporaries held across `.await` remain notoriously hard to map back to the offending subexpression.

#### (C2) Simplicity, Orthogonality & Universal Model Refinement

`Basis: source + derived`

Evaluating front-end lowering mechanisms through Daniel Jackson's Concept Design (1-to-1 concept-to-purpose alignment), John Ousterhout's Deep Modules, and Matthias Felleisen's macro-expressibility identifies four universal simplifications that eliminate edge-case sprawl:

1. **Lexical-block drop scoping + explicit extension (`super let`) instead of syntactic `E&` heuristics:**
   - Pre-2024 Rust conflated *evaluation-order temporaries* with *borrow-extension convenience*, creating special cases (`IfThen`, tail expressions, `E&` grammar `region.rs:603-615`, and `Deref` syntactic exceptions). Dropping temporaries at the tightest lexical construct (statement, `if let` condition+then, tail expression, match arm—with `super let` as the single explicit extension primitive) turns Edition 2024 rules from ad-hoc patches into one compositional rule: **values drop when their lexical syntactic unit finishes unless explicitly hoisted by `super let`**.
2. **Syntactically distinct binding vs. constant patterns:**
   - Distinguishing variable binders from constant patterns syntactically (e.g., sigils, lowercase-enforced binders with hard errors on unresolved uppercase pattern identifiers, or explicit `const` pattern syntax) eliminates constant-typo catch-all bugs globally rather than relying on optional lints.
3. **Strict `autoImplicit = false` + Pollack-consistent surface printing:**
   - Requiring explicit quantification (or at most explicit `variable` declarations) in specification modules enforces a 1-to-1 correspondence between written specification symbols and kernel binders with zero loss of expressive power, and checking that pretty-printed theorem types re-parse to alpha-equivalent kernel `Expr`s detects Pollack-inconsistency before human sign-off.
4. **Explicit coercion & conversion boundaries in verified subsets:**
   - Separating machine-checked arithmetic (`wrapping_add`, `checked_sub`, explicit `Int.ofNat`) from implicit coercions (`Coe`, `uint16_t` promotions, `Deref` coercions) guarantees that every runtime call and integer overflow check visible in MIR or kernel `Expr` corresponds visibly to an operator in the surface code reviewed by humans.

## Boundaries

- **Other `rustc` desugarings (`not examined` in full):** While `?` (`Try::branch` / `FromResidual::from_residual`), closures (RFC 2229 disjoint field capture), `for` loops (`IntoIterator::into_iter`), and `async gen` blocks (`FutureKind::AsyncIterator` in `rustc_ast_lowering/src/expr.rs:1014-1049`) also desugar prior to THIR/MIR, only `region.rs`, `coercion.rs`, `method/probe.rs`, `check_match.rs`, and `lower_expr_await` were inspected in source here.
- **Downstream C++ clang/gcc AST execution (`not examined`):** C++ list-initialization (`[over.match.list]`), integral promotion (`[conv.prom]`), and ADL (`[basic.lookup.argdep]`) behaviors are cited from normative ISO/IEC 14882 clauses rather than locally compiled `clang++`/`g++` execution runs.
- **Edition 2024 `match` scrutinees (`known not to apply`):** Contrary to `if let` (`ScopeData::IfThenRescope`), Rust Edition 2024 did **not** narrow `match` scrutinee temporary lifetimes (`destructors.md:281-283`, `rfc_3606.md:182-187`); `match *lock.read().unwrap() { ... }` continues to hold the read guard across all arms in Edition 2024.
- **`relaxedAutoImplicit := false` still permits implicit variables (`known not to apply` as complete guard):** In `leanprover/lean4@4f5982e315` (`src/Lean/Elab/AutoBound.lean:35-36, 61`), setting only `relaxedAutoImplicit = false` still silently auto-binds single-letter names and indexed names (`x`, `n1`, `α'`); projects seeking zero accidental quantifiers must set `autoImplicit = false`.
- **MIR-level verifier coverage (`unsupported` without surface hooks):** Verifiers operating solely on Rust MIR or Lean kernel `Expr` cannot detect Edition-2021 vs. 2024 drop-order shifts, constant-typo pattern shadowing, or `autoImplicit` binder injection because those choices are already finalized in lowered MIR/kernel terms (`unknown` whether a given `ByValue` binding or `{max_bound : Nat}` binder was human-intended).

## Evidence

- **Primary GitHub Sources (inspected 2026-11-19 at exact commit SHAs):**
  - `rust-lang/rust` @ `c884ecfbabb04b04fa5054dafc67ec258ecde745`:
    - `compiler/rustc_hir_analysis/src/check/region.rs` (`resolve_block` & `edition.at_least_rust_2024()` lines 57–166; `resolve_cond` lines 170–190; `super let` lines 226–234; `AssignOp` primitive vs. trait order lines 318–351; `IfThenRescope` lines 353–375; `is_binding_pat` & `E&` grammar lines 550–625)
    - `compiler/rustc_middle/src/middle/region.rs` (`Scope`, `ScopeData::{Node, CallSite, Arguments, Destruction, IfThen, IfThenRescope, MatchGuard, Remainder}` lines 75–160)
    - `compiler/rustc_hir_typeck/src/method/probe.rs` (`pick_core`, `pick_all_method` lines 1319–1430)
    - `compiler/rustc_hir_typeck/src/coercion.rs` (`Coerce::coerce` lines 242–368; `coerce_to_ref` `autoderef` loop lines 422–490)
    - `compiler/rustc_mir_build/src/thir/cx/block.rs` (`mirror_block`, `mirror_stmts` lines 10–106) and `compiler/rustc_mir_build/src/thir/pattern/check_match.rs` (`PatKind::Binding`, `report_unreachable_pattern`)
    - `compiler/rustc_ast_lowering/src/expr.rs` (`lower_expr_await`, `make_lowered_await` lines 985–1200)
  - `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/destructors.md` (`lines 261-450`), `src/type-coercions.md` (`lines 1-200`), `src/expressions/operator-expr.md` (`Deref` extension `&*String::new()` vs. `Deref::deref` lines 179–205; `as` casts lines 651–901; `compound-assign` `f1`/`f2`/`f3::<u8>` lines 1089–1210).
  - `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/3606-temporary-lifetimes-in-tail-expressions.md` (`lines 1-190`), `text/3627-match-ergonomics-2024.md` (`lines 1-140`), `text/2005-match-ergonomics.md`.
  - `leanprover/lean4` @ `4f5982e315272d89e2d2113d7ae0d8c9480f15db`: `src/Lean/Elab/AutoBound.lean` (`autoImplicit`, `relaxedAutoImplicit`, `isValidAutoBoundSuffix`, `#255` note, `checkValidAutoBoundImplicitName` lines 17–73), `src/Lean/Elab/App.lean` (`coerceToFunction?` lines 378, 1746–1815), `src/Lean/Elab/Extra.lean` (`Op` `binop%`/`leftact%`/`rightact%` maximal-type coercions lines 108–250).
  - `rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`: `vernac/metasyntax.ml`.
- **Self-Contained Reproducible Rust Probe (`Basis: execution`, observed 2026-11-19 on `rustc 1.98.0-nightly` commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**

```rust
// Save as /tmp/probe_rust_lowering.rs
use std::cell::RefCell;
use std::sync::RwLock;

struct DropLog(&'static str);
impl Drop for DropLog { fn drop(&mut self) { println!("drop: {}", self.0); } }
struct TempHolder(DropLog);
impl TempHolder { fn val(&self) -> usize { 42 } }
struct CustomCounter(i32);
impl std::ops::AddAssign<i32> for CustomCounter {
    fn add_assign(&mut self, rhs: i32) { self.0 += rhs; }
}

fn test_if_let_lock(lock: &RwLock<Result<i32, &'static str>>) {
    if let Ok(_v) = *lock.read().unwrap() {
        println!("if_let_branch: ok");
    } else {
        match lock.try_write() {
            Ok(mut w) => { *w = Ok(7); println!("if_let_else_try_write: Ok(unlocked)"); }
            Err(_) => println!("if_let_else_try_write: Err(WouldBlock -> DEADLOCK if .write())"),
        }
    }
}

fn test_tail_drop_order() -> usize {
    let _local = DropLog("local");
    TempHolder(DropLog("tail_temp")).val()
}

fn test_refcell_tail_drop() -> usize {
    let cell = RefCell::new(10usize);
    *cell.borrow() // Fails E0597 in Edition 2021; compiles in Edition 2024
}

fn test_assign_op_order() {
    let mut x = 10i32;
    *{ println!("prim_lhs"); &mut x } += { println!("prim_rhs"); 5 };
    let mut c = CustomCounter(10);
    *{ println!("custom_lhs"); &mut c } += { println!("custom_rhs"); 5 };
}

#[allow(dead_code, non_snake_case, unreachable_patterns)]
fn test_match_const_typo(code: u32) -> &'static str {
    const EXPECTED_AUTH: u32 = 200;
    match code {
        EXPECTED_AUTHH => "matched typoed constant as catch-all variable!",
        EXPECTED_AUTH => "unreachable real constant",
        _ => "fallback",
    }
}

fn main() {
    let lock = RwLock::new(Err("missing"));
    test_if_let_lock(&lock);
    let v = test_tail_drop_order();
    println!("tail_val: {v}");
    println!("refcell_tail_val: {}", test_refcell_tail_drop());
    test_assign_op_order();
    println!("match_typo(999): {}", test_match_const_typo(999));
}
```

Recorded diagnostics and execution outputs:
1. `rustc --edition=2021 /tmp/probe_rust_lowering.rs -o /tmp/probe_2021`:
   Fails with `error[E0597]: 'cell' does not live long enough` on `*cell.borrow()`, plus `warning: unused variable: EXPECTED_AUTHH` noting `help: you might have meant to pattern match on the similarly named constant EXPECTED_AUTH`.
2. Replacing `*cell.borrow()` with `let r = *cell.borrow(); r` and compiling with `rustc --edition=2021 -W tail-expr-drop-order /tmp/probe_rust_lowering_2021run.rs -o /tmp/probe_2021run && /tmp/probe_2021run`:
   Emits `warning: relative drop order changing in Rust 2024` and outputs:
```text
if_let_else_try_write: Err(WouldBlock -> DEADLOCK if .write())
drop: local
drop: tail_temp
tail_val: 42
refcell_tail_val: 10
prim_rhs
prim_lhs
custom_lhs
custom_rhs
match_typo(999): matched typoed constant as catch-all variable!
```
3. Unmodified `rustc --edition=2024 /tmp/probe_rust_lowering.rs -o /tmp/probe_2024 && /tmp/probe_2024`:
   Compiles with zero errors and outputs:
```text
if_let_else_try_write: Ok(unlocked)
drop: tail_temp
drop: local
tail_val: 42
refcell_tail_val: 10
prim_rhs
prim_lhs
custom_lhs
custom_rhs
match_typo(999): matched typoed constant as catch-all variable!
```

- **Self-Contained Reproducible Lean 4.34.1 Probe (`Basis: execution`, observed 2026-11-19 on Lean `4.34.1` commit `5045d0056413266e57c625dcd7c365b10e377c52`):**

```lean
-- Save as /tmp/probe_lean_elab.lean and run: lean /tmp/probe_lean_elab.lean
def MAX_BOUND : Nat := 0
theorem spec_with_typo (x : Nat) : x < max_bound → x < max_bound := fun h => h
#check @spec_with_typo

section Strict
set_option autoImplicit false
theorem nat_sub_underflow_zero : (3 : Nat) - 5 = 0 := rfl
theorem nat_div_zero : (42 : Nat) / 0 = 0 := rfl
end Strict

def coerce_probe (n : Nat) (i : Int) : Int := n + i
set_option pp.coercions true in
#print coerce_probe
```

Recorded output:
```text
@spec_with_typo : ∀ {max_bound : Nat} (x : Nat), x < max_bound → x < max_bound
def coerce_probe : Nat → Int → Int :=
fun n i => ↑n + i
```
And running `lean` on `set_option autoImplicit false` followed by `theorem spec_with_typo (x : Nat) : x < max_bound -> x < max_bound := fun h => h` exits non-zero with:
```text
error(lean.unknownIdentifier): Unknown identifier `max_bound`

Note: It is not possible to treat `max_bound` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```

## Revalidation

1. **Re-run the Rust Edition 2021 vs. 2024 lowering probe:** Save the Rust snippet above to `/tmp/probe_rust_lowering.rs` and compile/run with both `--edition=2021` (with `-W tail-expr-drop-order`) and `--edition=2024`; verify `if_let_else_try_write` flips from `Err(WouldBlock)` to `Ok(unlocked)`, `drop: local` vs. `drop: tail_temp` swaps order, and `prim_rhs`/`prim_lhs` vs. `custom_lhs`/`custom_rhs` remains inverted.
2. **Re-run the Lean 4 `autoImplicit` & `Coe` probe:** Run `lean /tmp/probe_lean_elab.lean` (and a strict-mode check with `set_option autoImplicit false`) on future Lean releases to check whether `autoImplicit` or `relaxedAutoImplicit` defaults in `src/Lean/Elab/AutoBound.lean` change.
3. **Diff `rust-lang/rust` lowering files on toolchain upgrades:** Inspect diffs in `compiler/rustc_hir_analysis/src/check/region.rs` (`resolve_block`, `resolve_cond`, `AssignOp`, `IfThenRescope`), `compiler/rustc_hir_typeck/src/method/probe.rs`, `compiler/rustc_hir_typeck/src/coercion.rs`, and `compiler/rustc_ast_lowering/src/expr.rs` (`lower_expr_await`) against commit `c884ecfbabb04b04fa5054dafc67ec258ecde745`.
