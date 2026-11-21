# Rust 2021 versus 2024 temporary drop scopes in rustc, value-versus-place `match` scrutinees, and the discriminant-read precondition of `UnreachableEnumBranching`

## Summary

1. **The edition changes when a temporary is dropped through exactly two decisions, both made while the region scope tree is built.** In `compiler/rustc_hir_analysis/src/check/region.rs`, `resolve_block` resolves a block's tail expression with `terminating = edition.at_least_rust_2024()`, so in Edition 2024 the tail expression gets its own `ScopeData::Destruction` scope; and `resolve_expr` enters `ScopeData::IfThenRescope` instead of `ScopeData::IfThen` around an `if` condition and `then` block when `expr.span.at_least_rust_2024()`. There is **no `ScopeData::TailExpr` variant**: the string `TailExpr` does not occur in `compiler/rustc_middle/src/middle/region.rs` at either pinned revision. `ScopeTree::default_temporary_scope` then walks parent scopes, stopping *below* a `Destruction` scope and *at* an `IfThenRescope` (or `MatchGuard`) scope, while passing through the Edition 2021 `IfThen`. The MIR builder schedules each temporary's drop in the scope that walk returns and emits a scope's drops in reverse scheduling order.
2. **Executed result (rustc 1.98.0-nightly, native and Miri, identical):** Edition 2021 prints `TAIL=12 IF_LET=91 MATCH=91`, Edition 2024 prints `TAIL=21 IF_LET=19 MATCH=91`. A block local is dropped before a tail-expression temporary in 2021 and after it in 2024; an `if let` scrutinee temporary is dropped after the `else` block in 2021 and before it in 2024; a `match` scrutinee temporary outlives the arms in both. The `ElaborateDrops` MIR shows the same reversal of `drop`/`StorageDead` order, and a destructor log derived from that MIR equals the runtime log for all six probe functions in both editions.
3. **`match` is edition-invariant only when the scrutinee is not a block.** `match { e } { .. }` (and therefore `match unsafe { e } { .. }`) makes `e` a block tail expression: the probe prints `MATCH_BLOCK_SCRUTINEE=91` in 2021 and `19` in 2024.
4. **Value versus place scrutinee.** `unsafe { match *p { .. } }` lowers the scrutinee as the place `(*_1)` (`_2 = discriminant((*_1))`), while `match unsafe { *p } { .. }` lowers a block, which the MIR builder never treats as a place: it materializes a temporary and consumes `*p` by copy or move (`_2 = copy (*_1); _3 = discriminant(_2)`). For a type that is not `Copy` the second form is rejected with `E0507` in both editions. Under Miri the two forms report different undefined behavior for the same forged tag.
5. **`UnreachableEnumBranching` rewrites `switchInt(move _2) -> [0: bb2, otherwise: bb1]` into `[0: bb2, 2: bb1, otherwise: bb4]` with `bb4: unreachable`** for `unsafe { match *p { Tri::A(v) => v + 1, _ => 77 } }` over `#[repr(u8)] enum Tri { A(u32), B(Never), C }`. The pass runs whenever the MIR optimization level is at least 1, including `-C opt-level=0` builds. Its justification is stated in the interpreter: `InterpCx::read_discriminant` throws `UninhabitedEnumVariantRead` and comments "This is the basis for the `uninhabited_enum_branching` MIR pass". Miri reports `read discriminant of an uninhabited enum variant` (exit status 1) at both `-Zmir-opt-level=0` and `-Zmir-opt-level=2`. The documentation comment on `Rvalue::Discriminant` nevertheless says the validity requirements are "undecided", and the LLVM `!range` metadata on the tag load (`!{i8 0, i8 3}`) does not exclude the uninhabited variant's tag.
6. **Mechanization (Lean v4.34.1, 79 theorems, axioms ⊆ {`propext`}).** A transcription of the scope walk and the builder's scope stack proves the exact traces above for any number of block locals and temporaries; a model of the pass proves it behavior-preserving for every enum, switch and tag under the interpreter's rule, proves that rule *necessary* (for every enum, any discriminant semantics that can yield a value outside the inhabited variants' discriminants admits a miscompiled switch), and exhibits the `Tri` program as the counterexample under raw-tag and declared-tag-only semantics.
7. **Consequence for the Anneal trusted MIR semantics at the pinned revision:** it models only fieldless enums (every variant inhabited) and treats `Drop` terminators as unsupported. A body whose edition-dependent difference involves a destructor therefore cannot be executed by it at all, and the uninhabited-variant rule is never exercised by it; for all-inhabited enums the invalid-tag rule alone suffices for the rewrite (proved).

## Applicability

**Subjects and how they relate.**

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (rustc 1.98.0-nightly, 2026-05-31, LLVM 22.1.6, host `x86_64-unknown-linux-gnu`) is both the source revision whose files were read and the exact toolchain whose `rustc` and `miri` binaries were executed. Every line number in this report refers to this revision unless a second number is given in parentheses.
- `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (rustc 1.102.0-nightly, 2026-11-11) was examined in two weaker ways: the same source files were fetched and the same source lines located (numbers in parentheses), and an execution receipt recorded earlier with that toolchain is retained in `support/retained_receipt_rustc_1_102_0_nightly.json`. That toolchain was **not** executed for this report.
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` is examined only for what its `Trusted.MirAst` / `Trusted.MirSemantics` Lean modules model about enum discriminants, storage markers and drops. The Lean development in this package does not import it.
- The Rust Reference, RFC 3606 and the Edition Guide revisions are the documents against which the implementation is compared.
- Lean v4.34.1 is the kernel that checked `support/EditionDropScopesAndEnumBranching.lean`.

**Shared across the two rustc revisions** (source located at both; execution at the first, retained receipt at the second): the two edition tests in region resolution, `default_temporary_scope` (identical line positions), the `as_temp` → `schedule_drop` path, the `Block`-is-not-a-place categorization, the `UnreachableEnumBranching` algorithm, and the `read_discriminant` uninhabited-variant check. The retained receipt's first output line (native and Miri, both editions) and its MIR text for six bodies are identical to this report's probe output.

**Different between the two revisions** (source only): helper renames in the MIR builder (`break_for_else` → `break_from_if_then_scope`, `lower_let_expr` → `lower_fallible_let`, `then_else_break` → `lower_if_condition`, `scope_index` → `stack_index`, `schedule_drop(.., DropKind::Value)` → `schedule_drop_value(..)`), the pass-enabling hook (`is_enabled`: `sess.mir_opt_level() > 0` → `policy`: `PassPolicy::optional(ctx.mir_opt_level() >= 1)`), the uninhabited test (`op.layout().for_variant(self, index).is_uninhabited()` → `op.layout().is_variant_uninhabited(index)`), and the lint query name in `resolve_block`. Of the 22 audited `rust-lang/rust` files only `compiler/rustc_mir_build/src/thir/cx/block.rs` is byte-identical across the two revisions.

**Configuration.** Crate edition selected with `--edition 2021` / `--edition 2024`; single-file programs in which the blocks, `if let` and `match` expressions under test are written directly rather than produced by macros, so their spans carry the crate's edition. Native builds use rustc defaults unless a flag is named. MIR dumps use `-Zdump-mir=<pass>` with `--emit=mir`. Miri is invoked as the `miri` driver with an explicit `--sysroot` built by `cargo miri setup`. Miri runs without MIR optimizations by default; passing `-Zmir-opt-level=2` makes it print a warning that MIR optimizations were explicitly enabled (recorded by the probe), and passing `-Zmir-opt-level=0` does not.

**Extension beyond what was run.** Statements about other toolchains rest only on the source locations found at the second revision and on the retained receipt; they are not claims about releases in between or later. The Lean theorems are statements about the model defined in the Lean file, whose correspondence to rustc is by transcription of the cited functions and by agreement with the executed traces on the probed shapes.

## Findings

### 1. Where the edition enters: region scope resolution

`Basis: source (rust-lang/rust at both revisions) + documentation (Rust Reference) + normative design text (RFC 3606)`

`rustc_middle::middle::region::ScopeData` (`compiler/rustc_middle/src/middle/region.rs:112`) has exactly these variants: `Node`, `CallSite`, `Arguments`, `Destruction` (line 124), `IfThen` (128), `IfThenRescope` (133), `MatchGuard` (138), `Remainder(FirstStatementIndex)` (141). The Edition 2024 tail-expression rule has no scope kind of its own.

The scope tree is built by `ScopeResolutionVisitor` in `compiler/rustc_hir_analysis/src/check/region.rs`. The helper that makes a node "terminating" is (lines 740–749 (736–745); comment removed):

```rust
fn enter_node_scope_with_dtor(&mut self, id: hir::ItemLocalId, terminating: bool) {
    if terminating {
        self.enter_scope(Scope { local_id: id, data: ScopeData::Destruction });
    }
    self.enter_scope(Scope { local_id: id, data: ScopeData::Node });
}
```

Every statement other than a `super let` is terminating (`resolve_stmt`, line 245 (243)); an expression visited through the default `visit_expr` is not (line 830 (826): `resolve_expr(self, ex, false)`). The file consults the edition at three textual sites in two functions, and nowhere else:

- `resolve_block`, tail expression (lines 144–164, edition test at 146–147 (148)):

  ```rust
  if let Some(tail_expr) = blk.expr {
      let local_id = tail_expr.hir_id.local_id;
      let edition = blk.span.edition();
      let terminating = edition.at_least_rust_2024();
      if !terminating && /* the `tail_expr_drop_order` lint needs to run */ {
          visitor.scope_tree.backwards_incompatible_scope
              .insert(local_id, Scope { local_id, data: ScopeData::Node });
      }
      resolve_expr(visitor, tail_expr, terminating);
  }
  ```

  (abridged: the lint test is `!visitor.tcx.lints_that_dont_need_to_run(()).contains(&lint::LintId::of(lint::builtin::TAIL_EXPR_DROP_ORDER))` at the first revision and uses `skippable_lints` at the second.) Each `let` statement of the block enters a `Remainder(i)` scope nested in the previous one (lines 108 and 132 (109, 133)).

- `resolve_expr`, `hir::ExprKind::If` with and without `else` (lines 355–382, edition tests at 357 and 372, scope kind chosen at 358/373 (356/371)):

  ```rust
  let data = if expr.span.at_least_rust_2024() {
      ScopeData::IfThenRescope
  } else {
      ScopeData::IfThen
  };
  visitor.enter_scope(Scope { local_id: then.hir_id.local_id, data });
  visitor.cx.var_parent = visitor.cx.parent;
  resolve_cond(visitor, cond);
  resolve_expr(visitor, then, true);
  visitor.cx = expr_cx;
  resolve_expr(visitor, otherwise, true);
  ```

  `resolve_cond` (line 172 (170)) does not make a `let` condition terminating ("Temporaries for `let` expressions must live into the success branch", lines 174–175 (172–173)).

`resolve_expr` has no case for `hir::ExprKind::Match`: the only occurrence of `hir::ExprKind::Match` in the file is at line 661 (657), inside the lifetime-extension helper `record_rvalue_scope_if_borrow_expr`, after `resolve_expr` ends (the next item, `enum LetKind`, starts at line 401 (399)). A `match` therefore falls to `_ => intravisit::walk_expr(visitor, expr)` (line 394 (392)): its scrutinee is resolved as an ordinary non-terminating sub-expression and each arm through `resolve_arm` (line 194 (192)). No edition test is reachable from a `match` unless the scrutinee or an arm contains a block or an `if`.

Both the edition of a block and of an `if` are read from the **span** (`blk.span.edition()`, `expr.span.at_least_rust_2024()`), not from a crate-wide setting.

The walk that turns the tree into a temporary scope is `ScopeTree::default_temporary_scope` (`region.rs:308–341` in `rustc_middle`, same line positions at both revisions; abridged and reformatted: `debug!` calls and comments removed, match arms compacted):

```rust
pub fn default_temporary_scope(&self, inner: Scope) -> (Scope, Option<Scope>) {
    let mut id = inner;
    let mut backwards_incompatible = None;
    while let Some(&p) = self.parent_map.get(&id) {
        match p.data {
            ScopeData::Destruction => return (id, backwards_incompatible),
            ScopeData::IfThenRescope | ScopeData::MatchGuard => return (p, backwards_incompatible),
            ScopeData::Node | ScopeData::CallSite | ScopeData::Arguments
            | ScopeData::IfThen | ScopeData::Remainder(_) => {
                if backwards_incompatible.is_none() {
                    backwards_incompatible =
                        self.backwards_incompatible_scope.get(&p.local_id).copied();
                }
                id = p
            }
        }
    }
    span_bug!(/* span */, "no enclosing temporary scope")
}
```

`temporary_scope(expr_id)` (line 346) first honors a recorded extended scope and otherwise calls this walk starting from `Node(expr_id)`.

Derived consequences for the probed shapes (each row is checked in the Lean file by evaluating the transcribed walk):

| Shape | Edition 2021 temporary scope | Edition 2024 temporary scope |
| :--- | :--- | :--- |
| temporary in the tail of `let x = { let l = ..; tail };` | `Node(statement)`: the walk passes the tail, the `Remainder` scopes, the block and the block expression, and stops below `Destruction(statement)` | `Node(tail)`: the walk stops below `Destruction(tail)` |
| temporary in the scrutinee of `if let P = s { .. } else { .. }` (expression statement) | `Node(statement)`: `IfThen` is passed through | `IfThenRescope(then)`: the walk stops at it |
| temporary in the scrutinee of `match s { .. }`, `s` not a block | `Node(statement)` | `Node(statement)` |
| temporary inside `e` in `match { e } { .. }` | `Node(statement)` | `Node(e)`: `e` is a block tail |

Documents agree with this (quotations below have link markup removed). The Reference lists, among the places that bound a temporary scope, "The pattern-matching condition(s) and consequent body of `if`" and "The entirety of the tail expression of a block", both marked as Edition 2024 rules (`src/destructors.md:277–279`), states "The 2024 edition added two new temporary scope narrowing rules: `if let` temporaries are dropped before the `else` block, and temporaries of tail expressions of blocks are dropped immediately after the tail expression is evaluated" (line 289, rule `destructors.scope.temporary.edition2024` at 287), and notes "The scrutinee of a `match` expression is not a temporary scope, so temporaries in the scrutinee can be dropped after the `match` expression" (line 282). RFC 3606 covers only the tail-expression rule ("In the next edition, drop temporaries in tail expressions *before* dropping locals, rather than after", line 10) and lists "Dropping temporaries in a match scrutinee *before* the arms are evaluated, rather than after" as a future possibility whose "initial approaches didn't work out" (lines 182–186). The `if let` rule has no RFC text among the examined sources; it is described by the Edition Guide chapter `temporary-if-let-scope.md` (line 5) and implemented by the `IfThenRescope` scope. The two compatibility lints are `IF_LET_RESCOPE` (`compiler/rustc_lint/src/if_let_rescope.rs:83` (82)) and `TAIL_EXPR_DROP_ORDER` (`compiler/rustc_lint_defs/src/builtin.rs:5275` (5318)), both allow-by-default.

### 2. From scope tree to MIR: scheduling and emitting drops

`Basis: source`

THIR mirrors the scope choices without adding any: every expression is wrapped in `ExprKind::Scope { region_scope: Node(expr), .. }` (`compiler/rustc_mir_build/src/thir/cx/expr.rs:76` (143)), `ExprKind::If` carries `if_then_scope` with the same `IfThenRescope`/`IfThen` choice (lines 910–918 (1056–1064)), `let` statements carry `Remainder` scopes (`thir/cx/block.rs:67`). `Destruction` scopes exist only in the scope tree: the identifier `Destruction` does not occur anywhere under `compiler/rustc_mir_build/src/` at the first revision, and the MIR builder's scope stack is made of the `Node`, `Remainder`, `IfThen`/`IfThenRescope` and similar scopes that THIR carries.

In the MIR builder (`compiler/rustc_mir_build/src/builder/`):

- `as_temp` (`expr/as_temp.rs:16`) writes the value and calls `schedule_drop(expr_span, temp_lifetime, temp, DropKind::Value)` (line 131; `schedule_drop_value` at (120)) with the scope returned by `temporary_scope`; when the scope is an `IfThenRescope` it tags the local `LocalInfo::IfThenRescopeTemp` (line 83 (72)); when the scope tree recorded a `backwards_incompatible` scope it also schedules a lint-only hint (line 135 (124)).
- `schedule_drop` searches the scope stack from the innermost entry outward and pushes a `DropData` onto the entry with `scope.region_scope == region_scope` (`scope.rs:1488–1497` (1449–1458)); if none matches it is a compiler bug (`span_bug!`).
- Leaving a scope emits its drops in reverse scheduling order: `build_scope_drops` iterates `scope.drops.iter().rev()` (`scope.rs:1872` (1841)).
- `ast_block_stmts` (`block.rs:34`) pushes each `let`'s remainder scope and remembers it in `let_scope_stack` (lines 188, 246 (188, 257)), lowers the tail expression with `expr_into_dest` (line 324 (335)), and only then pops the remainder scopes in reverse (line 348 (359)). A tail temporary scheduled in `Node(tail)` is therefore dropped before the block's locals; one scheduled in `Node(statement)` is dropped after the block has been left.
- `ExprKind::If` (`expr/into.rs:68` (61)) records `condition_scope = this.local_scope()` (line 71 (64)), which is the innermost scope at that point, `Node(if)`; enters `if_then_scope`; and lowers the condition inside `in_if_then_scope(condition_scope, ..)` (line 89 (82); `scope.rs:654`). A `let` condition is lowered by `lower_let_expr` (`matches/mod.rs:2359`; `lower_fallible_let` at (2320)), which evaluates the scrutinee with `lower_scrutinee` and, for the failing-pattern edge, calls `break_for_else` (line 2380; `break_from_if_then_scope` at (2346)). `break_for_else` (`scope.rs:1062` (1057)) collects the drops of every scope stack entry *inside* the condition scope (`for scope in &self.scopes.scopes[scope_index + 1..]`, line 1077 (1072)) into the else-edge drop tree. Hence a scrutinee temporary scheduled in `IfThenRescope(then)` is dropped on the way into the `else` block, and one scheduled in `Node(statement)` is untouched by that edge.
- `match_expr` (`matches/mod.rs:351` (334)) evaluates the scrutinee with `lower_scrutinee` (line 393 (375)), which calls `as_place_builder` (line 399 (380)); nothing on this path consults the edition.

### 3. Executed drop orders and MIR

`Basis: execution (support/probe_results_rustc_1_98_0_nightly.json; rustc and Miri 1.98.0-nightly) + derived`

`support/rust/drop_order.rs` logs a digit when a `Guard(n)` is dropped and digits 8/9 when a `then`/`else` block or first/second match arm runs. Output, identical under native execution and Miri (exit status 0):

| Log | Source shape | Edition 2021 | Edition 2024 |
| :--- | :--- | :--- | :--- |
| `TAIL` | `let out = { let _local = Guard(1); id(Guard(2).val()) };` | `12` | `21` |
| `FN_TAIL` | the same block as a function body | `12` | `21` |
| `IF_LET` | `if let None = Guard(1).some() { push(8); } else { push(9); }` (pattern fails) | `91` | `19` |
| `IF_LET_THEN` | `if let Some(_) = Guard(1).some() { push(8); } else { push(9); }` (pattern matches) | `81` | `81` |
| `MATCH` | `match Guard(1).some() { None => push(8), _ => push(9) }` | `91` | `91` |
| `MATCH_BLOCK_SCRUTINEE` | `match { Guard(1).some() } { None => push(8), _ => push(9) }` | `91` | `19` |

MIR after `ElaborateDrops` for `run_tail_expr` (`_2` is the block local `Guard(1)`, `_5` the tail temporary `Guard(2)`); the normal-path blocks differ only as follows:

```text
Edition 2021                                   Edition 2024
bb2: StorageDead(_3);                          bb2: drop(_5) -> [return: bb3, unwind: bb7];
     drop(_2) -> [return: bb3, unwind: bb7];   bb3: StorageDead(_5);
bb3: StorageDead(_2);                               StorageDead(_3);
     drop(_5) -> [return: bb4, unwind: bb8];        drop(_2) -> [return: bb4, unwind: bb8];
bb4: StorageDead(_5); ...                      bb4: StorageDead(_2); ...
bb6 (cleanup): drop(_2) -> bb7                 bb6 (cleanup): drop(_5) -> bb7
bb7 (cleanup): drop(_5) -> bb8                 bb7 (cleanup): drop(_2) -> bb8
```

For `run_if_let_else` (`_4` is the scrutinee temporary): in Edition 2021 both branches join at `bb6: drop(_4)` after `push(8)` / `push(9)`; in Edition 2024 the else edge is `bb4: drop(_4)` → `bb5: StorageDead(_4); StorageDead(_2); _7 = push(const 9_u64)`, while the then edge keeps `push(const 8_u64)` before `bb3: .. drop(_4)`. For `run_match_block_scrutinee` in Edition 2024 the temporary is dropped in `bb1`, before `PlaceMention(_2); _5 = discriminant(_2); switchInt(move _5)`.

The probe script walks the normal path of each dumped body (taking the switch edge the program takes at runtime) and concatenates the digits of dropped `Guard` locals and `push` calls; this MIR-implied log equals the runtime log for all six functions in both editions (12 checks). The retained 1.102.0-nightly receipt records `TAIL=12 IF_LET=91 MATCH=91` / `TAIL=21 IF_LET=19 MATCH=91` for native and Miri, and its `run_tail_expr` and `run_if_let_else` MIR texts for both editions are line-for-line identical to the ones produced here (trailing whitespace ignored).

### 4. Compile-time and lock consequences of the two rules

`Basis: execution + documentation (Edition Guide)`

| Program (`support/rust/`) | Edition 2021 | Edition 2024 |
| :--- | :--- | :--- |
| `tail_temp_borrows_local.rs`: `let c = RefCell::new(vec![1u8, 2, 3]); c.borrow().len()` as a function body | ``error[E0597]: `c` does not live long enough`` | compiles; prints `LEN=3` (native and Miri) |
| `block_tail_temp_escapes.rs`: `let n = { &String::from("1234") }.len();` | compiles; prints `N=4` (native and Miri) | `error[E0716]: temporary value dropped while borrowed` |
| `if_let_mutex_guard.rs`: `if let Some(_v) = *m.lock().unwrap() { .. } else if m.try_lock().is_ok() { "released" } else { "held" }` on `Mutex::new(None)` | `IF_LET_ELSE_LOCK=held` | `IF_LET_ELSE_LOCK=released` |
| same file, `match *m.lock().unwrap() { Some(_v) => .., None => /* try_lock */ }` | `MATCH_ARM_LOCK=held` | `MATCH_ARM_LOCK=held` |

The first two rows are adaptations of the Edition Guide's two examples of the tail rule, one in each direction (`temporary-tail-expr-scope.md`); the guide also states that "there are no semantics-preserving rewrites to shorten the lifetime for temporary values in tail expressions" (line 90). The lock rows are the guide's `if let` example made observable with `try_lock` instead of a blocking second lock, and confirm its migration advice "It is always safe to rewrite `if let` with a `match`" (`temporary-if-let-scope.md:63`): the `match` form keeps the Edition 2021 behavior in Edition 2024. In Edition 2021 a blocking `lock()` in the `else` block would deadlock; the probe does not execute that.

### 5. Value versus place scrutinee

`Basis: source + execution`

`Category::of` (`builder/expr/category.rs`) classifies `ExprKind::Deref` as `Category::Place` (lines 39–46 (41–48)) and `ExprKind::Block` as `Category::Rvalue(RvalueFunc::Into)` (line 89 (91)). `expr_as_place` (`builder/expr/as_place.rs:416`) lowers `ExprKind::Deref { arg }` by lowering `arg` as a place and appending a deref projection (lines 446–449 (447–450)), but lists `ExprKind::Block { .. }` (line 565 (566)) among the expressions handled by:

```rust
// these are not places, so we need to make a temporary.
let temp_lifetime = this.region_scope_tree.temporary_scope(expr.temp_scope_id);
let temp = unpack!(block = this.as_temp(block, temp_lifetime, expr_id, mutability));
block.and(PlaceBuilder::from(temp))
```

(lines 591–595 (592–596); one `debug_assert!` line omitted). `as_temp` fills the temporary with `expr_into_dest`; for a block that reaches the tail expression (`block.rs:324`), and a place-category tail such as `*p` is written into the destination as `Rvalue::Use(this.consume_by_copy_or_move(place), ..)` (`expr/into.rs:845–858` (856–869)), where `consume_by_copy_or_move` returns `Operand::Copy(place)` for `Copy` types and `Operand::Move(place)` otherwise (`builder/misc.rs:61–69`).

So, for a raw pointer `p`:

- `unsafe { match *p { .. } }`: the scrutinee is the `Deref` expression itself; `lower_scrutinee` obtains the place `(*_1)`. Observed MIR: `_2 = discriminant((*_1));`. Nothing is moved, so the form is accepted for a type that is not `Copy` (`support/rust/scrutinee_value_vs_place.rs` prints `PLACE=41`).
- `match unsafe { *p } { .. }`: the scrutinee is a block; a temporary is created and `*p` is copied or moved into it. Observed MIR for a `Copy` enum: `_2 = copy (*_1); _3 = discriminant(_2);`. For a type that is not `Copy` the move out of `*p` is rejected by the borrow checker in both editions: ``error[E0507]: cannot move out of `*p` which is behind a raw pointer``, pointing at `*p` with "move occurs because `*p` has type `Msg`, which does not implement the `Copy` trait" (the diagnostic is created with code `E0507` at `compiler/rustc_borrowck/src/borrowck_errors.rs:275` (274)).

The two forms also differ in which undefined behavior Miri reports for a forged tag that selects the uninhabited variant (Finding 7), and the block form is subject to the Edition 2024 tail rule (Finding 3).

### 6. `UnreachableEnumBranching`: algorithm, enabling and observed rewrite

`Basis: source + execution`

`compiler/rustc_mir_transform/src/unreachable_enum_branching.rs` (176 (173) lines). The pass considers a block only if its terminator is `SwitchInt { discr: Operand::Move(p), .. }` on a local (`get_discriminant_local`, line 17 (18)), the block's last statement assigns that local from `Rvalue::Discriminant(place)` (line 39 (40)) and `place` has an enum type; cleanup blocks are skipped (line 93 (94)). `variant_discriminants` (line 51 (52)) returns the discriminants of the variants whose layout is not uninhabited (`(!layout.is_uninhabited())`, line 72 (73)); when the layout cannot be computed, all variants in `variant_range` are allowed. Then (lines 122–167 (123–168); comments and one `#[allow]` attribute removed):

```rust
for (index, (val, _)) in targets.iter().enumerate() {
    if !allowed_variants.remove(&val) {
        unreachable_targets.push(index);
    }
}
let replace_otherwise_to_unreachable = allowed_variants.len() <= 1
    && !body.basic_blocks[targets.otherwise()].is_empty_unreachable();
if unreachable_targets.is_empty() && !replace_otherwise_to_unreachable {
    continue;
}
let unreachable_block = patch.unreachable_no_cleanup_block();
let mut targets = targets.clone();
if replace_otherwise_to_unreachable {
    let otherwise_is_last_variant = allowed_variants.len() == 1;
    if otherwise_is_last_variant {
        let last_variant = *allowed_variants.iter().next().unwrap();
        targets.add_target(last_variant, targets.otherwise());
    }
    unreachable_targets.push(targets.iter().count());
}
for index in unreachable_targets.iter() {
    targets.all_targets_mut()[*index] = unreachable_block;
}
patch.patch_terminator(bb, TerminatorKind::SwitchInt { targets, discr: discr.clone() });
```

`SwitchTargets::add_target` appends the value and inserts the block just before the `otherwise` target (`compiler/rustc_middle/src/mir/terminator.rs:92–99` (94–101)); `target_for_value` takes the first matching value, else `otherwise` (line 86 (88)). The pass is enabled when `sess.mir_opt_level() > 0` (line 81; `ctx.mir_opt_level() >= 1` at (82)) and is registered in the optimization pipeline at `compiler/rustc_mir_transform/src/lib.rs:720` (734).

Observed on `support/rust/enum_branching.rs` (`#[repr(u8)] enum Tri { A(u32), B(Never), C }` with `enum Never {}`), dumped with `-C opt-level=3 -Zdump-mir=UnreachableEnumBranching`:

| Function | `switchInt` before | `switchInt` after |
| :--- | :--- | :--- |
| `classify_raw_wildcard`: `unsafe { match *p { Tri::A(v) => v + 1, _ => 77 } }` | `switchInt(move _2) -> [0: bb2, otherwise: bb1]` | `switchInt(move _2) -> [0: bb2, 2: bb1, otherwise: bb4]`, new `bb4: unreachable` |
| `classify_raw_value`: `match unsafe { *p } { Tri::A(v) => v + 1, _ => 77 }` | `switchInt(move _3) -> [0: bb2, otherwise: bb1]` | `switchInt(move _3) -> [0: bb2, 2: bb1, otherwise: bb4]` |
| `classify_ref`: every variant named, `Tri::B(n) => match n {}` | `switchInt(move _2) -> [0: bb4, 1: bb3, 2: bb2, otherwise: bb1]` (`bb1` already `unreachable`) | `switchInt(move _2) -> [0: bb4, 1: bb1, 2: bb2, otherwise: bb1]` |

In the first two rows the single unclaimed allowed discriminant (2, variant `C`) receives an explicit case that jumps to the old wildcard block and the wildcard edge becomes `unreachable`; in the third row the edge for the uninhabited variant is redirected to the existing empty unreachable block and `otherwise` is left alone. The `classify_raw_wildcard` before/after MIR texts are line-for-line identical to those in the retained 1.102.0-nightly receipt.

Whether the final MIR of `classify_raw_wildcard` contains the unreachable block, by build configuration: `-C opt-level=0`: yes (`[0: bb2, 2: bb1, otherwise: bb7]`); `-C opt-level=0 -Zmir-opt-level=0`: no; `-C opt-level=3`: yes; `-C opt-level=3 -Zmir-opt-level=0`: no. The pass therefore also runs in unoptimized builds unless MIR optimizations are disabled explicitly.

LLVM IR emitted by rustc before any LLVM optimization (`-C opt-level=3 -C no-prepopulate-passes --emit=llvm-ir`): with the pass, `switch i8 %_2, label %bb4 [ i8 0, label %bb2  i8 2, label %bb1 ]` with `bb4: unreachable`; with `-Zmir-opt-level=0`, `%2 = icmp eq i8 %_2, 0` / `br i1 %2, label %bb2, label %bb1`. In both, the tag load carries `!range !{i8 0, i8 3}`, a range that contains tag 1.

### 7. What reading a discriminant requires: interpreter, MIR documentation, Miri, native code

`Basis: source + execution; the disagreement between sources is preserved, not resolved`

The interpreter evaluates `Rvalue::Discriminant(place)` by `read_discriminant` followed by `discriminant_for_variant` (`compiler/rustc_const_eval/src/interpret/step.rs:275–280` (284–289)). `InterpCx::read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs:52` (53)), documented "Will never return an uninhabited variant" (line 50 (51)):

- throws `UninhabitedEnumVariantRead(None)` for `Variants::Empty` (line 69 (70)) and `UninhabitedEnumVariantRead(Some(index))` for an uninhabited `Variants::Single` layout;
- for a direct tag, throws `InvalidTag` if the tag is outside the tag's layout `valid_range` ("Codegen adds range metadata on the discriminant load so we really have to make this UB", lines 114–116 (115–117)) or matches no declared discriminant (line 137 (138));
- finally (lines 210–215 (211–216)):

  ```rust
  // Reading the discriminant of an uninhabited variant is UB. This is the basis for the
  // `uninhabited_enum_branching` MIR pass. It also ensures consistency with
  // `write_discriminant`.
  if op.layout().for_variant(self, index).is_uninhabited() {
      throw_ub!(UninhabitedEnumVariantRead(Some(index)))
  }
  ```

The message is "read discriminant of an uninhabited enum variant" (`compiler/rustc_middle/src/mir/interpret/error.rs:624` (623)).

The documentation of the MIR construct itself is weaker: the comment on `Rvalue::Discriminant` (`compiler/rustc_middle/src/mir/syntax.rs:1433–1443` (1437–1447)) says "The validity requirements for the underlying value are undecided for this rvalue, see #91095" (a `rust-lang/rust` issue). The Reference's list of undefined behavior includes "Producing an invalid value" (link markup removed), where "An `enum` must have a valid discriminant, and all fields of the variant indicated by that discriminant must be valid at their respective type" (`src/behavior-considered-undefined.md:59`, rule `undefined.validity.enum` at 139–140), and does not single out discriminant reads of a place. The implementation (interpreter rule plus a pass that depends on it) is thus stricter than the MIR documentation commits to.

Miri on forged tags (`support/rust/enum_branching.rs` writes the tag byte through a raw pointer into a `MaybeUninit<Tri>`), same results at `-Zmir-opt-level=0` and `-Zmir-opt-level=2`, exit status 1 in every case:

| Forged tag and form | Miri diagnostic |
| :--- | :--- |
| tag 1 (uninhabited `B`), place scrutinee | `error: Undefined Behavior: read discriminant of an uninhabited enum variant` at `match *p` |
| tag 1, block (value) scrutinee | `error: Undefined Behavior: constructing invalid value of type Tri: at .<enum-tag>, encountered an uninhabited enum variant` at `*p` in `match unsafe { *p }` |
| tag 3 (no such variant), place scrutinee | `error: Undefined Behavior: enum value has invalid tag: 0x03` |

Valid tags 0 and 2 run without diagnostics under both levels and print `VALID A=42 C=77 A_VALUE=42 C_VALUE=77 A_REF=42 C_REF=77`.

Native execution of the three forged-tag programs was also recorded for four build configurations (`-C opt-level=0`/`3`, each with and without `-Zmir-opt-level=0`). All twelve runs printed 77 for the forged tag. These executions have undefined behavior; that they happened to return the wildcard arm's value is not evidence that the rewrite is harmless, and the emitted LLVM IR above shows that the wildcard edge is `unreachable` whenever the pass ran.

### 8. Mechanized model and theorems

`Basis: execution (Lean v4.34.1 kernel) + derived (correspondence of the model to rustc is by transcription and by agreement with Finding 3 and Finding 6)`

`support/EditionDropScopesAndEnumBranching.lean` has no imports and contains 79 theorems, 57 definitions (all marked `noncomputable`, so no executable code and no compiler-only auxiliary constants are generated for them), 16 `abbrev`s, 6 inductive types and 5 structures. It compiles with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with exit status 0 and no diagnostics. `#print axioms` was run for all 79 theorems: 65 depend on `propext` only and 14 on no axiom; none depends on `Classical.choice`, `Quot.sound`, `sorryAx` or `Lean.ofReduceBool`. A census of every kernel constant the compiled module declares (669 including generated auxiliaries: 270 theorems, 353 definitions, 11 inductive types, 24 constructors, 11 recursors) finds 0 axiom declarations, 0 opaque constants, 0 `unsafe` constants, 0 `partial` constants, 0 constants whose name contains `_unsafe_rec`, 0 constants that mention `WellFounded.fix` (all recursion is structural), and `propext` as the only axiom any constant depends on. Outside comments the file contains no `sorry`, `admit`, `axiom`, `omega`, `decide`, `native_decide`, `bv_decide`, `partial`, `unsafe`, `opaque`, `@[extern]` or `@[implemented_by]`.

**Part A (drop scopes).** Definitions transcribe the mechanisms of Findings 1–2: `ScopeData`, `defaultTemporaryScope` (the walk, on an explicit parent chain), `enterNodeScopeWithDtor`, `resolveBlockTail` (terminating iff `Edition.atLeastRust2024`), `ifThenScope` (`ifThenRescope` iff `atLeastRust2024`), and a builder with `pushScope`, `scheduleIn` (search by region scope, innermost first; failure models the `span_bug!`), `popScope` (emit drops reversed), `breakForElse` (drops of all entries inside the condition scope), and `lowerBlockStmts` (nested remainder scopes). `compileBlockTail ed locals temps`, `compileIfLetElse ed scrutTemps matched thenTag elseTag` and `compileMatch ed scrutIsBlock scrutTemps armTag` run them and return the event list (`init l`, `drop l`, `body tag`) of the normal path. Proved:

- *Exact traces for arbitrary lists* (`compileBlockTail_ed2021`, `compileBlockTail_ed2024`): for all `locals temps : List Nat`, Edition 2021 yields `init locals ++ init temps ++ drops(reverse locals) ++ drops(reverse temps)` and Edition 2024 yields `init locals ++ init temps ++ drops(reverse temps) ++ drops(reverse locals)`. Hence the dropped-local sequences are `locals.reverse ++ temps.reverse` versus `temps.reverse ++ locals.reverse` (`blockTail_dropTrace_ed2021/ed2024`); they coincide if either list is empty (`blockTail_edition_invisible_of_nil`) and differ whenever both are non-empty and disjoint (`blockTail_edition_visible_of_cons`).
- *`if let`* (`compileIfLetElse_else_ed2021/ed2024`, `compileIfLetElse_then`): on the failing-pattern path Edition 2021 yields `init temps ++ [else body] ++ drops(reverse temps)` and Edition 2024 yields `init temps ++ drops(reverse temps) ++ [else body]`; on the matching path both editions yield `init temps ++ [then body] ++ drops(reverse temps)`.
- *`match`* (`compileMatch_plain`, `compileMatch_block_ed2021/ed2024`): with a non-block scrutinee both editions yield `init temps ++ [arm body] ++ drops(reverse temps)`; with a block scrutinee Edition 2024 yields `init temps ++ drops(reverse temps) ++ [arm body]`.
- **Theorem 1** (`dropTrace_reversal_and_match_invariance`): for one block local `l` and one tail temporary `t` the drop sequences are `[l, t]` (2021) and `[t, l]` (2024); for one scrutinee temporary `g` the observable sequences are `[else body, drop g]` (2021) and `[drop g, else body]` (2024); each Edition 2024 sequence is the reverse of the Edition 2021 one; and `compileMatch .ed2021 false temps arm = compileMatch .ed2024 false temps arm` for all `temps`. `match_block_scrutinee_is_edition_sensitive` shows the invariance fails for a block scrutinee. The `match` invariance holds because the modeled `match` path consults the edition only through a block in the scrutinee, mirroring the absence of an edition test on that path in rustc; it is a statement about the model, supported for rustc by Findings 1 and 3.
- *Agreement with execution* (`probe_tail_ed2021`, …, `probe_match_block_scrutinee_ed2024`, eight theorems): instantiated with the probe's identifiers the model yields `[1,2]`/`[2,1]`, `[9,1]`/`[1,9]`, `[8,1]`, `[9,1]`, and `[9,1]`/`[1,9]`, i.e. every digit string in the table of Finding 3 except `FN_TAIL`, whose shape (the block is the function body) is not modeled separately.
- **Counterexample 1** (`ce1_ed2021_tail_temp_borrow_of_local_dangling_vs_ed2024_safe`): for `l ≠ t`, if `t`'s destructor reads `l`, the Edition 2021 trace drops `t` after `l` is dead and the Edition 2024 trace does not. In real Rust the Edition 2021 program is rejected at compile time (`E0597`, Finding 4); the model shows the order the borrow checker is protecting against.
- **Counterexample 2** (`ce2_ed2021_if_let_mutex_guard_deadlocks_in_else_vs_ed2024_released`): interpreting `init g` as acquiring a non-reentrant mutex, `drop g` as releasing it and the `else` body as locking it again, the Edition 2021 trace deadlocks and the Edition 2024 trace completes; `match_arm_relock_deadlocks_in_both_editions` shows the `match` form deadlocks in both.

**Part B (discriminant reads and the pass).** An enum is a list of variants `(discr, inhabited)`; a place is represented by its tag value; `runSwitch sem e env sw tag` reads the discriminant under semantics `sem` (`none` = undefined behavior) and continues at `env (targetForValue d sw.cases sw.otherwise)`, where `env` maps a block to an outcome (`ub` or `ret v`). Three semantics: `evalDiscriminantStrict` (undeclared tag or uninhabited variant is UB, as in `read_discriminant`), `evalDiscriminantDeclaredTag` (only undeclared tags are UB), `evalDiscriminantRawTag` (returns the tag). `unreachableEnumBranching e otherwiseIsEmptyUnreachable ub sw` transcribes the code quoted in Finding 6 with the allowed set as a list. Proved:

- **Theorem 2** (`unreachableEnumBranching_preserves_strict`, `unreachableEnumBranching_refines_strict`): for every enum, switch, replacement block, block environment and tag, the rewritten switch has exactly the behavior of the original under `evalDiscriminantStrict` (so in particular it refines it). More generally (`unreachableEnumBranching_preserves_of_allowed_only`) this holds for any semantics that never yields a value outside the inhabited variants' discriminants.
- **Necessity and exact characterization** (`inhabited_only_rule_is_necessary`, `unreachableEnumBranching_sound_iff_allowed_only`): for a fixed enum, the rewrite refines every switch if and only if the discriminant semantics never yields a value outside the inhabited variants' discriminants. The witness for necessity is the switch that names every inhabited discriminant and sends all edges to one block.
- `unreachableEnumBranching_preserves_declaredTag_of_all_inhabited`: if every variant is inhabited, the declared-tag semantics already suffices.
- *Agreement with the dumped MIR* (`tri_rewrite_matches_observed_mir`, `tri_exhaustive_rewrite_matches_observed_mir`): on `Tri` the model computes `⟨[(0,2)], 1⟩ ↦ ⟨[(0,2),(2,1)], 4⟩` and `⟨[(0,4),(1,3),(2,2)], 1⟩ ↦ ⟨[(0,4),(1,1),(2,2)], 1⟩`, the two rewrites in the table of Finding 6.
- **Counterexample 3 and Theorem 3** (`ce3_raw_tag_discriminant_semantics_makes_unreachable_enum_branching_unsound`, `unreachableEnumBranching_unsound_rawTag`, `unreachableEnumBranching_unsound_declaredTag`): on `Tri` with tag 1, under the raw-tag and the declared-tag semantics the original switch returns 77 (the wildcard arm) and the rewritten switch reaches `unreachable`; the universally quantified refinement statement is therefore false for both semantics, even assuming the replacement block is `unreachable`. Under the strict semantics the original already has undefined behavior on tag 1 (`tri_tag1_is_ub_under_strict`), matching Miri.

### 9. Relation to the Anneal trusted MIR semantics

`Basis: source (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613) + derived`

`trusted/lean/Trusted/MirAst.lean` describes `EnumTy` (line 265) as a "Structural descriptor for a fieldless Rust enum" (line 226), lists `Drop` among the `TerminatorKind` variants represented by `.unsupported` (line 783) and `BackwardIncompatibleDropHint` among the unsupported statements (line 656). In `trusted/lean/Trusted/MirSemantics.lean`, `evalRvalue` (line 1240) evaluates `.discriminant place` (line 1269) only for an unprojected local of an admitted fieldless enum, returns `.error .undefined` for a dead local or an uninitialized scalar-tagged enum (line 1301), and otherwise returns the declared discriminant of the stored variant index. An enum value is stored as a variant index that is well-formed only if it is below the number of declared variants, and enum constants are decoded with `findDiscrVariant?` (line 544); a constant whose bit pattern matches no declared discriminant evaluates to `.error .undefined`. `.storageDead` (line 1391) and `.unreachable` (line 1551, `.fault .undefined`) are modeled.

Derived: (a) The edition is not an input of that semantics. It interprets the MIR rustc emitted, in which the edition has already been compiled into the positions of `drop` terminators and `StorageDead` statements (Finding 3). Because `Drop` is unsupported and fails closed, a body whose edition-dependent difference involves a destructor cannot be executed by that semantics at all; a body with only storage markers is interpreted with whichever `StorageDead` order rustc emitted for the crate's edition. (b) Because every modeled variant is inhabited and a stored enum value is a variant index checked against the declared variants, the uninhabited-variant branch of `read_discriminant` is never exercised; an invalid constant bit pattern is rejected when the constant is decoded, not at the discriminant read. By `unreachableEnumBranching_preserves_declaredTag_of_all_inhabited`, a pass with the algorithm of Finding 6 is behavior-preserving on such enums given only the invalid-tag rule. Extending that semantics to payload-carrying enums with uninhabited variants would require the stricter rule of Finding 7 for the rewrite to remain sound (`unreachableEnumBranching_sound_iff_allowed_only`). These are statements about the model in this package applied to the documented scope of those modules; no theorem here is stated over `Trusted.MirSemantics` itself.

## Boundaries

**Not examined.**

- Unwinding. Cleanup blocks appear in the dumped MIR (their drop order mirrors the normal path) but no panic was executed and the Lean model has no unwind edges.
- Other constructs that create or bound temporary scopes: `while let`, let chains, `let … else`, match guards (`MatchGuard` is transcribed in the walk but no modeled shape uses it), `super let`, temporary lifetime extension (`let x = &temp();`, `record_rvalue_scope_if_borrow_expr`), closures, coroutines and `async` blocks, constants and statics.
- Mixed-edition code. The edition is read from spans, so macro-generated blocks or `if` expressions can carry a different edition than the crate; no macro-generated block or `if` was probed.
- The two lints (`if_let_rescope`, `tail_expr_drop_order`) and the `BackwardIncompatibleDropHint` statement were located in source but not executed.
- Enum layouts other than a direct `u8` tag: niche-encoded enums, `Variants::Single`, `Variants::Empty`, generic enums whose layout cannot be computed (the `variant_range` fallback of the pass), and coroutine state discriminants. The Lean model covers direct tags only.
- Later MIR passes that consume the rewritten switch (for example CFG simplification) and LLVM's optimization of the resulting `unreachable` default.
- Targets other than `x86_64-unknown-linux-gnu`; code generation backends other than LLVM; rustc versions other than the two pinned revisions.

**Unknown.**

- Whether the language will specify discriminant reads the way the interpreter implements them. The MIR documentation calls the validity requirement "undecided"; this report records the implementation and the documentation and does not resolve the difference.
- Which Rust program produced the retained 1.102.0-nightly receipt. Its recorded MIR for six bodies and its first output line equal this report's, but the source is not preserved, and the receipt's remaining fields (for example the exit statuses it labels `miri_move_match_tag1_*`) are not relied upon.

**Known not to apply.**

- "`match` is edition-invariant" does not extend to a scrutinee wrapped in a block (`MATCH_BLOCK_SCRUTINEE` is `91` versus `19`), nor to blocks or `if let` inside arms.
- "Edition 2024 drops temporaries earlier, so it accepts more programs" is false in one direction: `block_tail_temp_escapes.rs` compiles in 2021 and fails with `E0716` in 2024.
- The native outputs for forged tags (all 77) do not show that the rewrite is unobservable; they are executions with undefined behavior.
- The unsoundness results of Part B are counterfactual. They do not show a miscompilation in rustc: under the rule the interpreter implements, the source program already has undefined behavior on the forged tag, and Theorem 2 shows the rewrite preserves behavior.
- `E0507` for `match unsafe { *p }` is a borrow-check error for types that are not `Copy`; for `Copy` types the form compiles and copies the value.

**Unsupported.**

- The Anneal trusted MIR semantics at the pinned revision does not support `Drop` terminators or payload-carrying enums; programs using them fail closed there.

**Stronger conclusions the evidence does not establish.** The Lean theorems do not verify rustc; they verify a model whose shapes were chosen to match three source forms. Agreement between model and compiler was checked only on the probed programs. Source identity between the two rustc revisions was checked at the located lines, not for whole files.

## Evidence

All paths below are inside this package's `support/` directory unless they name an upstream repository. Evidence was acquired on 2026-11-21, except the retained receipt, whose acquisition date was not recorded (its toolchain commit is dated 2026-11-11).

**Upstream sources (commit ids resolved through the GitHub commits API on 2026-11-21; `resolved_revisions.json`).**

| Repository | Revision | Committer date | Role |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | 2026-05-31 | source read; toolchain executed (`rustc -Vv`: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6) |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | 2026-11-11 | source lines located; toolchain of the retained receipt |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | 2026-11-19 | `trusted/lean/Trusted/MirAst.lean`, `MirSemantics.lean` |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | 2026-11-17 | `src/destructors.md`, `src/behavior-considered-undefined.md` |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | 2026-11-14 | `text/3606-temporary-lifetimes-in-tail-expressions.md` |
| `rust-lang/edition-guide` | `ab8544aeed7b792984366aa122ac19bd47ad9a2f` | 2026-08-25 | `src/rust-2024/temporary-if-let-scope.md`, `temporary-tail-expr-scope.md` |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`) | 2026-09-24 | kernel; `lean --version` reports the same commit |

- `audit_upstream_sources.py` and its output `upstream_source_anchor_manifest.json`: for each of 29 files, the git blob id, size and line count at every pinned revision, and the 1-based line numbers of 141 regular-expression anchors (0 expectation failures). Every line number quoted in this report is taken from that manifest or from direct reading of the same fetched file. The anchor `tail_expr_anywhere_in_file` records zero matches of `TailExpr` in `rustc_middle`'s `region.rs` at both revisions; `match_mentions_in_file` records the single `hir::ExprKind::Match` in the region-resolution file.

**Execution.**

- `probe_edition2024_drop_scopes_and_enum_branching.py` runs the given `rustc` and `miri` on the six programs in `rust/` inside a scratch directory and writes `probe_results_rustc_1_98_0_nightly.json`: commands (tool paths replaced by placeholders), exit statuses, outputs, error codes, MIR dumps (`ElaborateDrops` after-dumps for six functions per edition; `UnreachableEnumBranching` before/after dumps for three functions), final MIR per build configuration, unoptimized LLVM IR of `classify_raw_wildcard`, Miri diagnostics, native runs, the comparison with the retained receipt, and 78 expectation checks (78 passed). Expectations are literals compared against observed values; nothing in the results file is a literal copied from the script except the `expected` fields of the checks.
- `rust/drop_order.rs`, `rust/tail_temp_borrows_local.rs`, `rust/block_tail_temp_escapes.rs`, `rust/if_let_mutex_guard.rs`, `rust/scrutinee_value_vs_place.rs`, `rust/enum_branching.rs`: the probe programs.
- `retained_receipt_rustc_1_102_0_nightly.json`: receipt recorded with rustc 1.102.0-nightly (`3ef0c22cd`, LLVM 23.1.5); field values verbatim, two top-level keys renamed; not re-executed.

**Mechanization.**

- `EditionDropScopesAndEnumBranching.lean`: the Lean development (SHA-256 recorded in the receipt).
- `check_lean.py` and its output `lean_verification_receipt.json`: Lean version string, flags, exit status of the as-published run (0, no error or warning lines), `#print axioms` result for each of the 79 theorems, declaration counts, counts (all zero) of the constructs listed in Finding 8, and the kernel-constant census (obtained by compiling the module and importing it, together with the `Lean` library, into a small generated census file).

**Synthesis versus source facts.** The table of temporary scopes in Finding 1, the claims labelled "Derived" in Findings 2, 3 and 9, and the reading of the three anchors as "the only edition tests" (obtained by searching the two region files and the MIR-building crate for `at_least_rust_2024` and `.edition()`; other hits in the MIR-building crate are in unsafety checking and pattern lowering) are this report's synthesis.

## Revalidation

Cheapest discriminating checks first. Each establishes only what it checks.

1. **Have the edition tests or the walk moved?** Run `python3 support/audit_upstream_sources.py --out /tmp/manifest.json` after editing `PINS` to the revision of interest. A non-zero exit lists anchors whose match count changed. The anchors that carry the main findings are `tail_terminating_from_edition`, `if_then_rescope_choice`, `default_temporary_scope_destruction_arm`, `default_temporary_scope_rescope_arm`, `default_temporary_scope_passthrough_if_then`, `tail_expr_anywhere_in_file` (expects 0), `match_mentions_in_file` (expects 1), `non_places_need_temporary`, `remove_from_allowed`, `replace_otherwise_condition`, `basis_for_pass_comment` and `uninhabited_variant_check`. A new edition test elsewhere would not be caught by anchors; additionally search `compiler/rustc_hir_analysis/src/check/region.rs`, `compiler/rustc_middle/src/middle/region.rs` and `compiler/rustc_mir_build/src/` for `at_least_rust_20` and `.edition()`.
2. **Does a toolchain still produce the orders?** `rustc --edition 2021 support/rust/drop_order.rs -o /tmp/d21 && /tmp/d21` must print `TAIL=12 IF_LET=91 MATCH=91` then `FN_TAIL=12 IF_LET_THEN=81 MATCH_BLOCK_SCRUTINEE=91`; with `--edition 2024` it must print `TAIL=21 IF_LET=19 MATCH=91` then `FN_TAIL=21 IF_LET_THEN=81 MATCH_BLOCK_SCRUTINEE=19`. No unstable flag is involved, so a stable compiler that supports Edition 2024 can run this check; only nightly builds were run for this report.
3. **Full probe.** `python3 support/probe_edition2024_drop_scopes_and_enum_branching.py --rustc <nightly rustc> --miri <matching miri> --miri-sysroot <sysroot from cargo miri setup> --retained-receipt support/retained_receipt_rustc_1_102_0_nightly.json --out /tmp/probe.json` prints `78/78 checks passed` and exits 0 when everything in Findings 3–7 reproduces; failed check names identify what changed (for example `ueb/classify_raw_wildcard/switch_after`, `ueb/miri/2/tag1_place/ub_lines`, `scrutinee_value_vs_place/2024/value_error_codes`). Block numbers in the expected `switchInt` lines depend on MIR construction details and may change without a semantic change; inspect `pass_before_after` in the output before concluding anything from such a failure.
4. **Single-command checks of the pass and its precondition.** `mkdir -p /tmp/ueb && rustc --edition 2024 -C opt-level=3 -Zdump-mir=UnreachableEnumBranching -Zdump-mir-dir=/tmp/ueb --emit=mir -o /tmp/ueb/all.mir support/rust/enum_branching.rs` and compare the `classify_raw_wildcard` before/after `switchInt` lines; `miri --sysroot <sysroot> --edition 2024 -Zmir-opt-level=2 --cfg tag1_place support/rust/enum_branching.rs` must fail with `read discriminant of an uninhabited enum variant`. If Miri stops reporting this while the pass still performs the rewrite, then by the characterization in Finding 8 the rewrite is no longer justified by the interpreter's rule, and Finding 7 must be redone.
5. **Mechanization.** `python3 support/check_lean.py --out /tmp/receipt.json -- <path to lean v4.34.1>` prints `ok=True` and exits 0; it fails if Lean reports any error or warning, if any theorem or other constant depends on an axiom other than `propext`, if a forbidden construct appears in the source, or if the census finds an axiom declaration, an opaque, `unsafe` or `partial` constant, an `_unsafe_rec` auxiliary, or a use of `WellFounded.fix`. For another Lean version the proofs may need adjustment (they use `simp`); the statements do not depend on the version.
6. **If the scope tree or the pass is restructured** (for example a dedicated tail-expression scope kind, or the pass consulting something other than layout inhabitedness), the transcriptions in the Lean file must be re-derived from source; no cheap probe substitutes for rereading `resolve_block`, `resolve_expr`, `default_temporary_scope`, `as_temp`, `break_for_else` and `run_pass`.
