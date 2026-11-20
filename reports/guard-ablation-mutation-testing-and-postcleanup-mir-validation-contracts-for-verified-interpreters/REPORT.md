# Guard-Ablation Mutation Testing and `Runtime(PostCleanup)` MIR Validation Contracts for Verified Interpreters

## Summary

Verified Rust interpreters, static borrow checkers, and certified MIR-to-logic translators fail silently into unsoundness when structural preconditions or aliasing guards are omitted, bypassed, or evaluated in the wrong order. Positive test suites verify completeness (valid programs pass), yet cannot detect missing, dead, or caller-bypassed soundness checks. **Guard-ablation mutation testing** closes this gap by systematically suppressing individual soundness preconditions (`if !guard { return Err(...); }` $\to$ `{}` or helper checks forced to `Ok(())`) and asserting that targeted negative canaries fail through the **public verification entrypoint**, not solely through isolated helper unit tests. Measuring the gap between isolated helper kill rate ($K_{\text{unit}}$) and public-entrypoint kill rate ($K_{\text{entry}}$) exposes dropped check results, missing match-arm calls, vacuous downstream failures, and guards shadowed by earlier compiler passes.

For `MirPhase::Runtime(RuntimePhase::PostCleanup)` Rust MIR, upstream `rustc` validation (`compiler/rustc_mir_transform/src/validate.rs`), operational interpretation (`compiler/rustc_const_eval/src/interpret/`), Miri's Stacked/Tree Borrows trackers (`rust-lang/miri`), and MiniRust (`minirust/minirust`) enforce seven load-bearing structural and aliasing contracts:

1. **Entry-block (`START_BLOCK` / `bb0`) back-edge prohibition**: Every CFG edge targeting `bb0` is rejected statically so loop execution never conflates re-entry with `FnEntry` protector setup or initial local liveness.
2. **Typed, duplicate-free, bit-width-checked `SwitchInt` arms**: `SwitchInt` discriminants are restricted to `Uint`/`Int`/`Char`/`Bool`; branch keys must be unique and satisfy `ScalarInt::try_from_uint(value, size)` (storing signed negative integers zero-extended to `size` bits, e.g., `-1i8` as `0xff_u128`).
3. **Non-overlapping `StatementKind::Assign` / `Rvalue::Use` copies**: Memory-layout (`BackendRepr::Memory`) and padded copies execute `mem_copy(..., nonoverlapping: true)`, making partial or exact self-overlap UB even where naive value-snapshot semantics allow it.
4. **Deref-temporary retag suppression (`CopyForDeref` $\to$ `WithRetag::No`)**: `EraseDerefTemps` erases `LocalInfo::DerefTemp` to `LocalInfo::Boring` and turns `Rvalue::CopyForDeref(place)` into `Rvalue::Use(Operand::Copy(place), WithRetag::No)`; interpreters must honor `WithRetag::No` to avoid invalidating sibling pointers during address projection.
5. **Physical-holder isolation at `FnEntry`**: Protectors and fresh `BorTag`s must be minted per physical callee slot rather than deduplicated by target address, permitting `f(&r, &r)` while rejecting `unsafe { f(&mut *p, &mut *p) }`.
6. **Store-before-retag tuple and aggregate field ordering**: `write_aggregate` writes every field via `copy_op_no_validate` before running `validate_place` (`ValueVisitor::walk_value`) in `in_memory_order`, preventing premature inter-field invalidation.
7. **Out-of-band retired-tag preservation**: Pointers carry monotonic `BorTag(NonZero<u64>)` provenance out-of-band; invalidation pops stack items or sets Tree Borrows nodes `Disabled` in place while stale pointer copies keep their retired tags so subsequent accesses fault without ABA tag collision.

## Applicability

This report characterizes five concrete upstream subjects and their mutual relationships:

- **Primary Rust semantics and interpreter reference**: `rust-lang/rust` at commit `ac7bce92720268483c462f49fadb6cc3a01e73ce` (`rustc_mir_transform`, `rustc_middle::mir`, `rustc_const_eval::interpret`), paired with `rust-lang/miri` at `7e679961edcfe2c526f19153bb8b03de346efa5c` (which pins that `rust-lang/rust` SHA in `rust-version`) and `minirust/minirust` at `063d784186d3252bee242217f218223205c0b568`.
- **Mutation tooling baseline**: `sourcefrog/cargo-mutants` at `6c720ae82a1784b84cfa06066f7b0d59ed1798d0` and `mull-project/mull` at `8d55e80c0782256b4bae0e7793f4e25f35b6dff0`.
- **Subject relationships**: `rustc` MIR validation and `rustc_const_eval` define the exact IR invariants after `CleanupPostBorrowck` and `EraseDerefTemps`; `rust-lang/miri` implements the reference Stacked and Tree Borrows hooks; `minirust/minirust` supplies the normative operational spec (`spec/lang/well-formed.md`, `spec/lang/step/statements.md`), including documented divergences such as its explicit `TODO` on `Assign` overlap; `cargo-mutants` and `mull` show which AST/IR guard patterns existing mutators miss.
- **Boundary with sibling topics**: General `Runtime(PostCleanup)` constant placement, `RequiredConsts`, layout folding, and `UbChecks` are outside scope and covered separately; this report targets structural CFG/typing/overlap contracts, retagging invariants, and guard-ablation verification.

## Findings

### 1. Asymmetry of Soundness-Guard Ablation vs. Standard Mutation

Basis: normative + source + derived

Classical mutation testing (Jia & Harman, *IEEE TSE* 2011, DOI `10.1109/TSE.2010.62`; Petrović & Ivanković, *ICSE-SEIP* 2018, DOI `10.1145/3183519.3183521`) injects syntax edits (`+`/`-`, `==`/`!=`) assuming well-tested logic fails on valid inputs. For **proof engines, borrow checkers, and certified translators**, the public relation is an asymmetric admission gate: $\text{Verifier}(P) \in \{\text{Accept}(\pi), \text{Reject}(e)\}$. A soundness guard $g \in \mathcal{G}$ has the form `if !cond(x) { return Err(RejectReason); }`. Ablating $g$ replaces its rejection branch with `{}` (or forces the predicate to `Ok(())`/`true`):

1. **Zero kill rate on positive suites**: Under ablation $g \mapsto \top$, $\text{Accept}(\text{Verifier}_{\neg g}) \supseteq \text{Accept}(\text{Verifier})$. Every valid Rust program or verified theorem continues to pass (**0% positive-suite kill rate**).
2. **Relation to proof-assistant and extreme mutation**: Coq proof/spec mutation (`mCoq`, Jain, Celik & Gligoric, *ICSE-Companion* 2020, DOI `10.1145/3377812.3382156`) exhibits the same asymmetry when weakening preconditions, while extreme method-body mutation (`Descartes`, Vera-Pérez et al., *ASE* 2018 DOI `10.1145/3238147.3240474`; *Empir. Softw. Eng.* 2019 DOI `10.1007/s10664-018-9653-2`) detects *pseudo-tested methods* whose bodies can be stubbed without failing any test.
3. **Negative soundness canaries**: Killing $\text{Verifier}_{\neg g}$ requires a negative canary $P_{\neg g}$ satisfying every guard in $\mathcal{G} \setminus \{g\}$ while violating $g$, paired with an assertion checking `Err(ExpectedCategory)` so unrelated downstream rejections do not mask a missing check.

### 2. Operator Gaps in `cargo-mutants` and `mull` for Inline Guard Ablation

Basis: source + derived

Inspecting `sourcefrog/cargo-mutants` (`6c720ae82a1784b84cfa06066f7b0d59ed1798d0`, `src/mutant.rs:23-35`, `src/visit.rs:508-835`) confirms that its AST visitor emits exactly six mutant genres: `Genre::{FnValue, BinaryOperator, UnaryOperator, MatchArm, MatchArmGuard, StructField}`. `DiscoveryVisitor` mutates `ExprBinary`, `ExprUnary`, `Arm`, and `ItemFn` bodies, **not** standalone `Expr::If` conditions or early-return blocks:

- **Factored guard helpers (`fn check_*(...) -> Result<(), E>`)**: Receive `Genre::FnValue` mutation to `Ok(())`, cleanly modeling whole-guard ablation.
- **Inline `if` checks calling predicates (`if has_duplicates(t) { return Err(...); }`)**: Contain no `BinaryOperator`, `UnaryOperator`, or `MatchArmGuard`, so `cargo-mutants` generates **zero** mutants.
- **Regex and LLVM IR mutators**: Regex tools (Groce et al., *ICSE-Companion* 2018, DOI `10.1145/3183440.3183485`) rewrite `if (` $\to$ `if (false && `, and `mull-project/mull` (`8d55e80c0782256b4bae0e7793f4e25f35b6dff0`) flips LLVM `br i1` instructions, except when prior optimization folds branches or `cfg!(debug_assertions)` strips `debug_assert!` in release builds.

**Engineering rule**: Factor every load-bearing soundness guard into a `Result`/`bool` helper audited by `FnValue` ablation, or run a dedicated AST/macro guard-ablation pass over `if !G { return Err(..); }` / `ensure!`.

### 3. Helper-Only Kill Rate vs. Public-Entrypoint Kill Rate Matrix

Basis: derived

Measuring mutation score over unit tests alone conflates helper coverage with boundary enforcement. Partitioning the suite into **helper-only unit tests** ($K_{\text{unit}}(g) \in \{0,1\}$) and **public-entrypoint tests** ($K_{\text{entry}}(g) \in \{0,1\}$, invoking `verify_crate` / `interpret_mir_body`) exposes four distinct states:

| $(K_{\text{unit}}, K_{\text{entry}})$ | Classification | Root Causes | Remediation |
| :--- | :--- | :--- | :--- |
| `(1, 1)` | Enforced load-bearing guard | Reachable from public entrypoint with discriminating negative canary. | Keep canary; assert exact rejection variant. |
| `(1, 0)` | **Pseudo-enforced / decoupled** | (1) **Caller drop**: entrypoint ignores `Result` or omits call on an IR arm. (2) **Upstream shadowing**: HIR typeck/borrowck rejects all surface-Rust violators before the MIR pass runs. (3) **Downstream absorption**: a later step rejects the same canary when `g` is ablated. | Add a raw-MIR negative canary through the public entrypoint if `g` defends against optimizer/untrusted IR bugs; otherwise wire or remove dead branches. |
| `(0, 0)` | Dead, redundant, or untested | No negative canary exists, or `g` is implied by earlier validated invariants (equivalent mutant). | Add a negative canary, or discharge an implication proof and remove redundancy. |
| `(0, 1)` | Entrypoint-only catch | Public test kills `g`, but no isolated unit test pins corner cases. | Add boundary unit tests (e.g., `u8`/`i8`/`bool` bit limits). |

### 4. Contract 1 — Entry-Block (`START_BLOCK` / `bb0`) Back-Edge Prohibition

Basis: normative + source + derived

In `rust-lang/rust` (`ac7bce92720268483c462f49fadb6cc3a01e73ce`), `compiler/rustc_mir_transform/src/validate.rs:139-142` (`CfgChecker::check_edge`) checks every terminator target (`Goto`, `SwitchInt`, `Drop`, `Call`, `TailCall`, `Assert`, `FalseEdge`, `FalseUnwind`):

```rust
fn check_edge(&mut self, location: Location, bb: BasicBlock, edge_kind: EdgeKind) {
    if bb == START_BLOCK {
        self.fail(location, "start block must not have predecessors")
    }
    // ... cleanup-flag and Normal/Unwind consistency checks ...
}
```

At call entry (`compiler/rustc_const_eval/src/interpret/call.rs:613-695`; MiniRust `spec/lang/well-formed.md:808-833`), `_0` and `_1..=_n` start live and receive `RetagMode::FnEntry` strong protectors (`FrameState::protected_tags`), while body temporaries start dead until `StorageLive`. Accepting `goto -> bb0` either re-runs `FnEntry` initialization on loop iterations, violates `StorageLive` single-allocation invariants, or breaks SSA/fuel-loop pre-header assumptions (`bb0` in-degree `0`). Verified `PostCleanup` interpreters must reject any edge to `START_BLOCK` upfront.

### 5. Contract 2 — `TerminatorKind::SwitchInt` Type, Uniqueness, and Range Validation

Basis: normative + source + derived

`validate.rs` checks `TerminatorKind::SwitchInt { discr, targets }` across two passes:

1. **Duplicate branch keys** (`CfgChecker::visit_terminator`, `validate.rs:345-363`): Inserts every `(value: u128, _)` into `self.value_cache: FxHashSet<u128>` and fails with `"duplicated values in SwitchInt terminator"` if `targets.iter().len() != self.value_cache.len()`.
2. **Discriminant type and bit-width range** (`TypeChecker::visit_terminator`, `validate.rs:1600-1618`): Restricts `discr` to `Uint`, `Int` (normalized to `pointer_width`), `Char` (`32` bits), or `Bool` (`1` bit), and fails with `"the value {value:#x} is not a proper {switch_ty}"` whenever `ScalarInt::try_from_uint(value, size).is_none()`. Compare MiniRust `Discriminator::Branch` (`spec/lang/well-formed.md:267-284`), enforcing `can_represent` and non-overlapping branch ranges.

**Operational hazards**:
- **Zero-extended signed arm patterns**: `SwitchTargets` stores `-1i8` as `0xff_u128` (`255`), *not* `u128::MAX`. Sign-extending `discr` to `i128 as u128` causes `-1i8` to miss `0xff` and fall through to `otherwise` (often `TerminatorKind::Unreachable`, inducing false UB!).
- **Silent bit-masking**: Masking `value & ((1 << w) - 1)` without `ScalarInt::try_from_uint` accepts illegal `bool` arms like `2` or `u8` arms like `0x100`.
- **Duplicate-arm divergence**: Linear scan vs. hash-table dispatch disagree on duplicate keys; `char` validity (`<= 0x10FFFF`, non-surrogate) must still be checked at discriminant evaluation because `validate.rs:1606` checks `32` bits.

### 6. Contract 3 — Overlapping `StatementKind::Assign` / `Rvalue::Use` Undefined Behavior

Basis: normative + source

`compiler/rustc_middle/src/mir/syntax.rs:330-340` requires that the LHS place of `Assign` not overlap RHS places read, except for fully initialized `BackendRepr::Scalar | BackendRepr::ScalarPair` primitives (tracked in `rust-lang/rust#68364`). Inspecting `compiler/rustc_const_eval/src/interpret/step.rs:179-184` and `place.rs:950-1048`:

- `copy_op_no_validate` (`place.rs:970-1023`) checks `src_has_padding` (`false` for `Scalar` and contiguous/pointer `ScalarPair`; `true` for all `BackendRepr::Memory` and SIMD layouts).
- Unpadded immediates take the `read_immediate_raw` $\to$ `write_immediate_no_validate` fast path (permitting `x = copy x`).
- All `BackendRepr::Memory` aggregates and padded `ScalarPair`s (e.g., `(u8, u64)`) take `place.rs:1044`: `self.mem_copy(src.ptr(), dest.ptr(), dest_size, /*nonoverlapping*/ true)?`, raising **UB on both partial overlap and exact self-overlap** (`*p = Copy(*p)`), matching `llvm.memcpy` lowering.

**MiniRust gap**: In `minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`, `spec/lang/step/statements.md:17-38`), `eval_statement` reads `eval_value(source)` into a value snapshot before calling `place_store` and notes an explicit `TODO` referencing `#68364`. Interpreters targeting `rustc`/LLVM lowering must explicitly enforce non-overlap on `Assign` rather than adopting snapshot `memmove` semantics.

### 7. Contract 4 — Deref-Temporary Retag Suppression (`CopyForDeref` $\to$ `WithRetag::No`)

Basis: source + derived

At `rust-lang/rust` `ac7bce92720268483c462f49fadb6cc3a01e73ce`, standalone `StatementKind::Retag` is replaced by `WithRetag::{Yes, No}` on `Rvalue::Use(Operand<'tcx>, WithRetag)` (`syntax.rs:490-503, 1369`):

1. `Derefer` (`deref_separator.rs:23-80`) extracts chained dereferences (`place.projection[1..].contains(&ProjectionElem::Deref)`) into `LocalInfo::DerefTemp` locals via `Rvalue::CopyForDeref(deref_place)` (checked in `validate.rs:1498-1504`).
2. `EraseDerefTemps` (`erase_deref_temps.rs:19-33`, `PassPolicy::Required`) resets `LocalInfo::DerefTemp` to `LocalInfo::Boring` and rewrites `CopyForDeref(place)` $\to$ `Rvalue::Use(Operand::Copy(place), WithRetag::No)` with the comment: *"We do \*NOT\* want a retag here! This assignment might copy a mutable reference we can't actually copy, we just need it temporarily to create another pointer."*
3. `step.rs:179-186` dispatches `WithRetag::Yes` $\to$ `RetagMode::Default`, `WithRetag::No` $\to$ `RetagMode::None`, and panics on `CopyForDeref`.

Because `LocalInfo::DerefTemp` is already erased in `PostCleanup` MIR, interpreters must check `WithRetag::No` (never unconditionally retagging all `Rvalue::Use` copies of `&mut T`, nor unconditionally disabling retagging across all `Use` statements).

### 8. Contract 5 — Physical-Holder Deduplication Distinguishing `f(&r, &r)` from `f(&mut *p, &mut *p)`

Basis: normative + source + derived

At call entry (`call.rs:613-705`), `init_stack_frame` enters `RetagMode::FnEntry` and initializes each distinct formal argument local `_1..=_n` via `pass_argument` (`call.rs:444-466`, calling `protect_in_place_function_argument` for `FnArg::InPlace`). In `rust-lang/miri` (`7e679961edcfe2c526f19153bb8b03de346efa5c`):

- `next_ptr_tag` (`src/borrow_tracker/mod.rs:109`) assigns each argument slot a fresh `BorTag(NonZero<u64>)` registered in `FrameState::protected_tags` (`mod.rs:84`).
- Under Tree Borrows (Villani et al., *PLDI* 2025, DOI `10.1145/3735592`; `tree_borrows/mod.rs:129-149, 436-528`) and Stacked Borrows (Jung et al., *POPL* 2020, DOI `10.1145/3371109`):
  - **`f(&r, &r)` (`&T` without `UnsafeCell`)**: `_1` receives protected `Frozen` tag $t_1$; `_2` retags via a read from `r` receiving protected `Frozen` tag $t_2 \ne t_1$. Foreign reads leave `Frozen` intact (`tree.rs:203-212`), so both holders coexist cleanly.
  - **`unsafe { f(&mut *p, &mut *p) }`**: `_1` gets protected `Unique` (SB) / `Reserved` or `Unique` (TB with `-Zmiri-tree-borrows-implicit-writes` unless `#[rustc_no_writable]`). Retagging `_2` (under SB) or executing implicit/subsequent writes (under TB) triggers a conflicting foreign access against a `StrongProtector`, causing immediate UB.

**Deduplication trap**: Keying borrow trackers by target `(AllocId, offset)` instead of `(PhysicalHolderSlot, BorTag)` either merges `_1` and `_2` (unsoundly accepting `f(&mut *p, &mut *p)`) or rejects overlapping addresses unconditionally (falsely rejecting `f(&r, &r)`).

### 9. Contract 6 — Store-Before-Retag Tuple & Aggregate Field Ordering

Basis: source + derived

In `step.rs:303-345` (`write_aggregate`, non-`RawPtr` aggregates), `Rvalue::Aggregate(kind, operands)` executes in two strict phases:

1. **Unretagged store loop (`step.rs:328-333`)**: Stores every operand via `copy_op_no_validate(&op, &field_dest, false)` with zero retags.
2. **Post-store discriminant + `validate_place` (`step.rs:335-343`)**: Writes any enum discriminant and calls `validate_place(..., reset_provenance_and_padding: true)` (`validity.rs:624`), walking `FieldsShape::Arbitrary { in_memory_order, .. }` (`visitor.rs:148-153`) to invoke `M::retag_ptr_value` on reference/box fields.

Eagerly retagging inside the operand store loop breaks code where field `0`'s retag would disturb borrow state needed to evaluate field `1`. Moreover, `visitor.rs:148-153` traverses fields in **ascending `in_memory_order` byte offset**, whereas MiniRust `retag_val` (`spec/lang/step/statements.md:97-125`) traverses tuples in syntactic `FieldIdx` order—diverging whenever `repr(Rust)` reorders fields by alignment.

### 10. Contract 7 — Out-of-Band Retired-Tag Preservation

Basis: normative + source + derived

Pointers carry out-of-band provenance wrapping `BorTag(NonZero<u64>)` (`miri` `src/borrow_tracker/mod.rs:32-55`), drawn from monotonic `next_ptr_tag` (`mod.rs:109`). On retirement:
- **Stacked Borrows (`stacked_borrows/mod.rs:183-245`)**: Pops the invalidated `Item` from the memory stack while stale pointer copies in locals/memory retain their original `BorTag`, triggering `err_sb_ub` on dereference.
- **Tree Borrows (`tree_borrows/tree.rs:44-48, 191-202`)**: Marks the invalidated node `Permission::Disabled` in place (`new_access_noop = true` preserves causal error paths while blocking all child accesses); GC (`remove_unreachable_tags`) only compacts unexposed, unprotected tags unreachable from all `VisitProvenance` roots (`mod.rs:87-99`). Shadow-memory tools (`BorrowSanitizer`, McCormack et al., *RW2025*) face the identical requirement to keep retired shadow IDs distinct from live or wildcard tags.

Stripping retired tags to `None`/wildcard breaks dangling-int vs. retired-borrow distinction and permits permissive int-to-ptr bypasses, while recycling tag integers causes **ABA tag collision** (letting a stale `&mut` pointer hijack a newly minted tag).

## Boundaries

- **Equivalent vs. untested `(0, 0)` guards**: Distinguishing mathematically redundant guards from untested soundness holes is **unknown** from ablation scores alone without an implication proof or raw-MIR negative canary.
- **Weak-memory concurrency**: Atomic ordering interactions (`Acquire`/`Release`/`SeqCst`) with Tree Borrows retagging were **not examined**.
- **Misconception that `WithRetag::No` applies only to `&T`**: This assumption is **known not to apply**; `erase_deref_temps.rs:21-23` targets temporary `&mut T` copies in dereference chains.
- **Standalone `Expr::If` guard deletion in `cargo-mutants`**: Directly mutating inline `if cond(x) { return Err(..); }` checks is **unsupported** by `cargo-mutants` `Genre` (`src/mutant.rs:23-35`) at `6c720ae82a1784b84cfa06066f7b0d59ed1798d0` without helper extraction or `match` guards.
- **MiniRust `Assign` overlap enforcement**: Rejecting overlapping `Assign` strictly per MiniRust `spec/lang/step/statements.md:17-38` at `063d784186d3252bee242217f218223205c0b568` is **unsupported** without extending MiniRust past its documented `#68364` `TODO`.
- **Empirical `mull` throughput on Rust verifiers**: Equivalent-mutant ratios and runtime overhead of `mull` (`8d55e80c0782256b4bae0e7793f4e25f35b6dff0`) on `rustc_mir_transform` were **not examined**.

## Evidence

- **`rust-lang/rust`** (`ac7bce92720268483c462f49fadb6cc3a01e73ce`):
  - `compiler/rustc_mir_transform/src/validate.rs`: lines `139-142` (`check_edge` `START_BLOCK`), `345-363` (`SwitchInt` duplicates), `1498-1504` (`DerefTemp` requires `CopyForDeref`), `1600-1618` (`ScalarInt::try_from_uint`).
  - `compiler/rustc_mir_transform/src/deref_separator.rs`: lines `23-81` (`DerefChecker`); `erase_deref_temps.rs`: lines `19-33` (`EraseDerefTempsVisitor`).
  - `compiler/rustc_middle/src/mir/syntax.rs`: lines `330-340` (`Assign` overlap), `490-503` (`WithRetag`), `697-701` (`SwitchInt`), `1369` (`Rvalue::Use`).
  - `compiler/rustc_const_eval/src/interpret/step.rs`: lines `179-186`, `303-345` (`write_aggregate`); `place.rs`: lines `950-1048` (`copy_op_no_validate`, `mem_copy(..., nonoverlapping: true)` at `1044`); `call.rs`: lines `444-466`, `613-705`; `validity.rs`: lines `613-624`; `visitor.rs`: lines `148-153` (`in_memory_order`).
- **`rust-lang/miri`** (`7e679961edcfe2c526f19153bb8b03de346efa5c`): `rust-version`; `src/borrow_tracker/mod.rs:32-55, 72-99, 109`; `tree_borrows/mod.rs:129-149, 436-528`; `tree_borrows/tree.rs:44-48, 191-212`; `stacked_borrows/mod.rs:183-245`.
- **`minirust/minirust`** (`063d784186d3252bee242217f218223205c0b568`): `spec/lang/well-formed.md:267-284, 808-833`; `spec/lang/step/statements.md:17-38, 97-125`.
- **`sourcefrog/cargo-mutants`** (`6c720ae82a1784b84cfa06066f7b0d59ed1798d0`): `src/mutant.rs:23-35`; `src/visit.rs:508-835`.
- **`mull-project/mull`** (`8d55e80c0782256b4bae0e7793f4e25f35b6dff0`): LLVM IR mutation engine.
- **Papers**: Villani et al. *PLDI 2025* DOI `10.1145/3735592`; Jung et al. *POPL 2020* DOI `10.1145/3371109`; McCormack et al. *RW2025* (`BorrowSanitizer/bsan`); Jia & Harman *IEEE TSE 2011* DOI `10.1109/TSE.2010.62`; Petrović & Ivanković *ICSE-SEIP 2018* DOI `10.1145/3183519.3183521`; Groce et al. *ICSE-Companion 2018* DOI `10.1145/3183440.3183485`; Jain et al. *ICSE-Companion 2020* DOI `10.1145/3377812.3382156`; Vera-Pérez et al. *ASE 2018* DOI `10.1145/3238147.3240474`, *EMSE 2019* DOI `10.1007/s10664-018-9653-2`.

## Revalidation

1. **Upstream MIR validation drift probe**:
   ```bash
   RUST_SHA=$(curl -fsSL https://raw.githubusercontent.com/rust-lang/miri/master/rust-version | tr -d '[:space:]')
   curl -fsSL "https://raw.githubusercontent.com/rust-lang/rust/$RUST_SHA/compiler/rustc_mir_transform/src/validate.rs" | grep -n -C 3 "START_BLOCK\|try_from_uint\|duplicated values"
   curl -fsSL "https://raw.githubusercontent.com/rust-lang/rust/$RUST_SHA/compiler/rustc_mir_transform/src/erase_deref_temps.rs" | grep -n -C 3 "WithRetag"
   ```
2. **Miri differential litmus suite** (`cargo miri test` and `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test`):
   ```rust
   #![feature(custom_mir, core_intrinsics)]
   use core::intrinsics::mir::*;

   fn shared_pair(a: &i32, b: &i32) -> i32 { *a + *b }
   unsafe fn mut_pair(a: &mut i32, b: &mut i32) -> i32 { *a = 1; *b = 2; *a }

   #[test]
   fn contract5_physical_holders() {
       let mut x = 10;
       assert_eq!(shared_pair(&x, &x), 20); // MUST pass
       let p: *mut i32 = &mut x;
       let _ = unsafe { mut_pair(&mut *p, &mut *p) }; // MUST trigger UB
   }

   struct Holder<'a> { r: &'a mut [i32; 2] }
   #[test]
   fn contract4_deref_temp_no_retag() {
       let mut arr = [1, 2];
       let s = Holder { r: &mut arr };
       unsafe {
           let p0 = &raw mut (*s.r)[0];
           let p1 = &raw mut (*s.r)[1]; // CopyForDeref -> WithRetag::No
           *p0 += 10; *p1 += 20;
       }
       assert_eq!(arr, [11, 22]);
   }

   #[derive(Copy, Clone)]
   struct Big([u64; 4]);
   #[custom_mir(dialect = "runtime", phase = "post-cleanup")]
   fn self_assign_big(mut x: Big) -> Big {
       mir!({ x = Move(x); RET = Move(x); Return() }) // MUST trigger mem_copy nonoverlapping UB
   }
   ```
3. **Two-tier guard ablation verification**: Run `cargo mutants` separately against isolated unit helpers (`K_unit`) and public-entrypoint negative canaries (`K_entry`) covering both surface Rust and raw MIR, inspecting every guard with `(K_unit, K_entry) != (1, 1)`.
