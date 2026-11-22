# `rustc` MIR Runtime `UbChecks` Instrumentation, `Operand::RuntimeChecks` Evaluation Timing, and `CheckEnums` Soundness

## Summary

`rustc` implements runtime Undefined Behavior (UB) checking across two distinct MIR mechanisms that operate at different pipeline phases and obey different cross-crate and soundness invariants:

1. **Syntactic MIR UB-Check Insertion Passes (`CheckAlignment`, `CheckNull`, `CheckEnums`):** Run at the very start of `run_optimization_passes` (`MirPhase::Runtime(RuntimePhase::Optimized)`), gated by `Session::ub_checks()` (defaulting to `debug_assertions`, overridable via `-Z ub-checks={yes,no}`, and since `1.102.0-nightly` exposed as `PassPolicy::Optional` rather than `is_required() == true`). All three passes emit `TerminatorKind::Assert` with `unwind: UnwindAction::Unreachable` targeting `#[rustc_nounwind]` panic lang items (`panic_misaligned_pointer_dereference`, `panic_null_pointer_dereference`, `panic_null_reference_constructed`, `panic_invalid_enum_construction`), which set `PanicInfo { can_unwind: false }` and force immediate `SIGABRT` (`-6`) even inside `std::panic::catch_unwind` or `Drop` cleanup pads.
2. **Deferred Session-Flag Operands (`Operand::RuntimeChecks`):** `LowerIntrinsics` lowers `core::intrinsics::{ub_checks, overflow_checks, contract_checks}` to `Operand::RuntimeChecks(RuntimeChecks::{UbChecks, OverflowChecks, ContractChecks})` *before* `MirPhase::Runtime(RuntimePhase::PostCleanup)`. Contrary to the doc comment on `core::intrinsics::ub_checks()`, `InstSimplify::SimplifyUbCheck` folds `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` eagerly into `ConstValue::from_bool(tcx.sess.ub_checks())` inside `optimized_mir` **before `.rmeta` serialization** for every crate that lacks `#![rustc_preserve_ub_checks]` whenever `mir_opt_level >= 1` — which holds by default even at `-C opt-level=0` (`OptLevel::No.mir_opt_level() == 1`) and even when the upstream crate enables `-Z ub-checks=yes`. Only `core`, `alloc`, and `std` carry `#![rustc_preserve_ub_checks]`, which is why `core::slice::get_unchecked` evaluates according to the *downstream* crate's `-Z ub-checks` flag while an ordinary upstream crate's `#[inline(always)]` generic functions bake in the *upstream* crate's flag. By contrast, `SimplifyUbCheck` never folds `RuntimeChecks::OverflowChecks` or `RuntimeChecks::ContractChecks`, so `core::intrinsics::overflow_checks()` always survives to downstream codegen.
3. **Asymmetric Projection and ZST Semantics (`CheckAlignment` vs. `CheckNull`):** `CheckAlignment` invokes `check_pointers` with `BorrowedFieldProjectionMode::FollowProjections`, replacing the checked pointee type with the projected field type for `SharedBorrow | MutatingUseContext::Borrow` (avoiding false positives on `&(*p).byte_field` while still checking `(*p).byte_field` direct loads against the outer struct's alignment, and exploiting `field_align | field_offset` on non-packed structs so testing the base pointer address modulo `field_align` matches the projected field address). `CheckNull` invokes `check_pointers` with `NoFollowProjections` and splits `PlaceContext`: borrows (`&*p`, `&mut *p`) check nullness unconditionally even for zero-sized types (ZSTs), whereas non-borrow uses (`*p` copy/move) check `size_of::<T>() != 0`, permitting raw ZST dereferences from `null()`. Between `1.98.0-nightly` (`14210df0e27c`) and `1.102.0-nightly` (`3ef0c22cdb86`) / HEAD (`01afe534803b`), `CheckNull` split borrow failures from `AssertKind::NullPointerDereference` (`"null pointer dereference occurred"`) into `AssertKind::NullReferenceConstructed` (`"null reference produced"`). Both passes silently skip all unsized raw pointers (`!pointee_ty.is_sized`, e.g., `*const [u32]`).
4. **`CheckEnums` Coverage Gaps and Unmasked Signed-Niche Defect:** `EnumFinder::visit_rvalue` instruments *only* `Rvalue::Cast(CastKind::Transmute, ..)` — leaving raw-pointer dereferences (`*p`) and union field reads (`u.e`) completely unchecked under `-Z ub-checks=yes`. Worse, while `insert_direct_enum_check` explicitly masks sign-extended `u128` discriminants via `& discr.size.unsigned_int_max()`, **`insert_niche_check` omits this mask**. Whenever a niched enum inherits a signed tag scalar (`Primitive::Int(_, true)`, e.g., `Option<#[repr(i8)] enum>`), `insert_discr_cast_to_u128` sign-extends negative tag bytes to `u128`, violating the `discr < 2^w` precondition of `u128` wrapping-range subtraction and causing **both** false-positive `SIGABRT` aborts on 100% sound Rust (`Option<NegMid>` at valid byte `0xf6`, accepted by Miri) and false-negative UB bypasses (`Option<NegHigh>` at invalid byte `0x80`, rejected by Miri). Adding `& discr.size.unsigned_int_max()` before the wrapping subtraction restores exact equivalence with `WrappingRange::contains` across all widths $w \in \{8, 16, 32, 64, 128\}$.
5. **Anneal Trusted Boundary (`joshlf/anneal@c131b320eeeb`) and Mechanized Proof:** `Trusted.MirAst.Operand` intentionally excludes `RuntimeChecks` so MIR capture fails closed rather than folding crate-dependent flags into constants; `Trusted.MirAst.AssertKind` models `.misalignedPtrDeref` and `.nullPtrDeref` while routing `NullReferenceConstructed` and `InvalidEnumConstruction` to `.unsupported`; and `Trusted.MirSemantics.evalTerminator` currently fails closed on all `.assert` terminators. A standalone pure Lean 4 (`v4.34.1`) formalization (`support/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean`, `1,169` LOC, `47` user theorems, `122` total `.thmInfo` constants, `429` module constants, axioms `#[propext]`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`) mechanizes all four pillars and five constructive sharpness counterexamples (`ce1`–`ce5`).

## Applicability

This report characterizes six durable upstream subjects and their mutual relationships:

| Subject | Repository | Full Immutable Revision | Role in This Report |
| :--- | :--- | :--- | :--- |
| `rustc` compiler source (HEAD) | `rust-lang/rust` | `01afe534803b93889b85f6028117251cfbd431da` (`2026-11-22`) | Primary implementation source for all MIR passes, `Operand::RuntimeChecks`, `InstSimplify`, `WrappingRange`, `codegen_ssa`, `core::ub_checks`, and `core::panicking`. |
| `rustc 1.102.0-nightly` toolchain | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`, LLVM `23.1.5`, `x86_64-unknown-linux-gnu`) | Source-diffed against `1.98.0-nightly` and HEAD; recorded native execution + MIR dump baseline for the 8 core single-crate cases and 2 asymmetric cross-crate configs (`up_no__down_yes`, `up_yes__down_no`). |
| `rustc 1.98.0-nightly` toolchain and `Miri` | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`) | Live native execution (`-Z ub-checks={yes,no}` + MIR dumps) and live `Miri` differential oracle across all 12 single-crate cases and 9 cross-crate configurations; source-diffed against `1.102.0-nightly` and HEAD. |
| The Rust Reference | `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`2026-11-17`) | Normative UB definitions (`r[undefined.misaligned.*]`, `r[undefined.dangling.*]`, `r[undefined.validity.*]`). |
| Anneal Trusted MIR AST & Semantics | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | Direct source audit of `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `Trusted/Correspondence.lean` for fail-closed handling of `RuntimeChecks` and `AssertKind`. |
| Lean 4 theorem prover kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`) | Kernel checker (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and `env.constants.map₁` purity auditor for `support/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean`. |

### Version-Shared vs. Version-Specific Behavior

All three `rustc` revisions (`14210df0e27c` / `1.98.0-nightly`, `3ef0c22cdb86` / `1.102.0-nightly`, and `01afe534803b` / HEAD) share the following core semantics (verified by exact source inspection and diffing across all three commits):

- Pipeline placement of `LowerIntrinsics` in `run_runtime_cleanup_passes` (`Runtime(PostCleanup)`) and `CheckAlignment` -> `CheckNull` -> `CheckEnums` -> `InstSimplify::BeforeInline` -> `Inline` -> `InstSimplify::AfterSimplifyCfg` in `run_optimization_passes` (`Runtime(Optimized)`).
- `InstSimplify::SimplifyUbCheck` folding `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` whenever `mir_opt_level >= 1` and `#![rustc_preserve_ub_checks]` is absent, while leaving `OverflowChecks` and `ContractChecks` symbolic.
- `OptLevel::No.mir_opt_level() == 1` (so `-C opt-level=0` runs `InstSimplify` by default unless `-Z mir-opt-level=0` is explicitly passed).
- `CheckAlignment`'s `FollowProjections` mode, `[bool, i8, u8]` exclusion, `max_reliable_alignment()` mask cap, and `CheckNull`'s `NoFollowProjections` mode + ZST borrow-vs-copy split.
- `PointerFinder::visit_place`'s early return on `!pointee_ty.is_sized`.
- `CheckEnums`'s `CastKind::Transmute`-only visitor, `insert_direct_enum_check`'s `& unsigned_int_max()` mask, and `insert_niche_check`'s **omission** of `& unsigned_int_max()` after `insert_discr_cast_to_u128`.
- `UnwindAction::Unreachable` + `#[rustc_nounwind]` panic lang items forcing `SIGABRT` (`-6`) on Linux `x86_64-unknown-linux-gnu`.

Four material differences were observed across the three `rustc` commits:

1. **`CheckNull` `AssertKind` split (`1.98.0-nightly` vs. `1.102.0-nightly` & HEAD):** In `14210df0e27c` (`1.98.0-nightly`), `insert_null_check` unconditionally emitted `AssertKind::NullPointerDereference` (`"null pointer dereference occurred"`) for both raw dereferences and borrows (`&*null::<()>()`, confirmed in `ub_04`). By `3ef0c22cdb86` (`1.102.0-nightly`) and unchanged at `01afe534803b` (HEAD), `check_null.rs:55-88` splits `SharedBorrow | MutatingUseContext::Borrow` into `AssertKind::NullReferenceConstructed` (`"null reference produced"`, lang item `panic_null_reference_constructed`) while keeping `AssertKind::NullPointerDereference` for non-borrow place uses.
2. **MIR pass policy overrideability (`1.98.0-nightly` vs. `1.102.0-nightly` & HEAD):** In `14210df0e27c`, `CheckAlignment`, `CheckNull`, and `CheckEnums` implemented `is_enabled(&self, sess) -> sess.ub_checks()` plus `fn is_required(&self) -> bool { true }` (blocking `-Z mir-enable-passes` overrides). By `3ef0c22cdb86` and `01afe534803b`, all three implement `fn policy(&self, ctx: &PassCtx<'_>) -> PassPolicy { PassPolicy::optional(ctx.ub_checks()) }`, meaning `-Z mir-enable-passes=-CheckEnums` (or `+CheckEnums`) can selectively disable or enable each pass independently of `-Z ub-checks`.
3. **Basic-block splitting refactor (`1.102.0-nightly` vs. HEAD):** Between `3ef0c22cdb86` and `01afe534803b`, `check_pointers.rs:89-166` replaced `split_block` with `basic_blocks.push_with(...)`, and `check_enums.rs:350-377` hoisted `discr_masked` allocation before `BasicBlockData::new` to eliminate unterminated intermediate blocks. Both refactors are semantics-preserving.
4. **`core::ub_checks::check_language_ub` (`1.102.0-nightly` vs. HEAD):** In `3ef0c22cdb86`, `library/core/src/ub_checks.rs:96-108` evaluated `const_eval_select!(if const { false } else { !cfg!(miri) }) && intrinsics::ub_checks()` (keeping `intrinsics::ub_checks()` outside the `const_eval_select!`). By `01afe534803b` (HEAD), `&& intrinsics::ub_checks()` moved *inside* the runtime `else` arm (`!cfg!(miri) && intrinsics::ub_checks()`), avoiding any `RuntimeChecks::UbChecks` operand along the `const` evaluation path.

### Configuration and Scope Qualifications

- All native execution measurements were acquired on `x86_64-unknown-linux-gnu` with Rust Edition 2024 and default panic strategy (`panic=unwind`, where `#[rustc_nounwind]` panics abort via `SIGABRT`, exit status `-6` in Python `subprocess`, shell status `134`).
- The 4 newly added single-crate extension cases (`ub_09` through `ub_12`) and the 7 expanded cross-crate isolation configurations (`up_no__down_no`, `up_yes__down_yes`, `up_no_opt0_default__down_yes`, `up_no_miropt0__down_yes`, `up_no_preserve_attr__down_yes`, `up_ovf_no__down_ovf_yes`, `up_ovf_yes__down_ovf_no`) were executed live on `rustc 1.98.0-nightly` (`14210df0e27c`) + `Miri`; extension of `ub_09` and `ub_10` (the unmasked signed-niche defect) to `1.102.0-nightly` (`3ef0c22cdb86`) and HEAD (`01afe534803b`) is **derived** from verified source identity across `check_enums.rs:216-231, 318-336, 466-541`, `rustc_middle/src/ty/layout.rs:188-198`, and `rustc_abi/src/layout/enum_layout.rs:614-648`, rather than direct binary execution on `1.102.0-nightly` or HEAD.

## Findings

### 1. MIR Pass Pipeline Placement, `PassPolicy` Evolution, and Flag Semantics

Basis: source (`rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da`, `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)

#### 1.1 Session Check Predicates (`Session::{ub_checks, overflow_checks, contract_checks}`)

In `compiler/rustc_session/src/session.rs:1091-1101` (`01afe534803b`), the three runtime-check session flags have distinct defaults:

```rust
pub fn overflow_checks(&self) -> bool {
    self.opts.cg.overflow_checks.unwrap_or(self.opts.debug_assertions)
}

pub fn ub_checks(&self) -> bool {
    self.opts.unstable_opts.ub_checks.unwrap_or(self.opts.debug_assertions)
}

pub fn contract_checks(&self) -> bool {
    self.opts.unstable_opts.contract_checks.unwrap_or(false)
}
```

- Both `ub_checks()` and `overflow_checks()` inherit `self.opts.debug_assertions` unless explicitly overridden via `-Z ub-checks={yes,no}` or `-C overflow-checks={yes,no}`.
- `contract_checks()` defaults strictly to `false` even when `debug_assertions` is enabled, requiring explicit `-Z contract-checks=yes`.
- Independently, `Session::mir_opt_level()` (`session.rs:988-990`) delegates to `OptLevel::mir_opt_level()` (`compiler/rustc_session/src/config.rs:123-128`), which returns **`1` at `-C opt-level=0`** (`OptLevel::No => 1`) and **`2` at all higher optimization levels** (`_ => 2`). Only an explicit `-Z mir-opt-level=0` sets `mir_opt_level` to `0`.

#### 1.2 Exact MIR Pipeline Ordering Across Phases

In `compiler/rustc_mir_transform/src/lib.rs:684-789` (`01afe534803b`), the runtime MIR pipeline separates intrinsic lowering (`PostCleanup`) from UB-check instrumentation and constant folding (`Optimized`):

```text
MirPhase::Runtime(RuntimePhase::Initial)
  └─ run_runtime_cleanup_passes (lib.rs:684-698)
       1. LowerIntrinsics         ── lowers ub_checks / overflow_checks / contract_checks
                                     into Rvalue::Use(Operand::RuntimeChecks(..), WithRetag::Yes)
       2. RemovePlaceMention
       3. SimplifyCfg::PreOptimizations
     ═══> MirPhase::Runtime(RuntimePhase::PostCleanup)  [Miri & Anneal capture boundary]

  └─ run_optimization_passes (lib.rs:700-789)
       1. CheckAlignment          ── PassPolicy::optional(ctx.ub_checks())
       2. CheckNull               ── PassPolicy::optional(ctx.ub_checks())
       3. CheckEnums              ── PassPolicy::optional(ctx.ub_checks())
       4. LowerSliceLenCalls
       5. InstSimplify::BeforeInline     ── PassPolicy::optional(ctx.mir_opt_level() >= 1)
                                            runs SimplifyUbCheck if !#![rustc_preserve_ub_checks]
       6. ForceInline / Inline
       7. RemoveStorageMarkers / RemoveZsts / RemoveUnneededDrops
       8. UnreachableEnumBranching / UnreachablePropagation / SimplifyCfg
       9. InstSimplify::AfterSimplifyCfg ── second SimplifyUbCheck opportunity (post-inlining!)
      10. SimplifyConstCondition::AfterInstSimplify ── prunes dead precondition_check branches
      11. RefProp / SROA / DSE / GVN / SsaRangeProp / DataflowConstProp / JumpThreading / ...
     ═══> MirPhase::Runtime(RuntimePhase::Optimized)    [serialized into .rmeta for generic/#[inline] fns]
```

Three structural invariants follow directly from this ordering:

1. **Pre-optimization UB check placement:** `CheckAlignment`, `CheckNull`, and `CheckEnums` execute as passes 1–3 of `run_optimization_passes` ("Add some UB checks before any UB gets optimized away", `lib.rs:710`) so that `GVN`, `UnreachableEnumBranching`, and `ReferencePropagation` cannot assume UB absence and delete the check before it is inserted.
2. **`Runtime(PostCleanup)` never contains pass-inserted UB assertions, but DOES contain `Operand::RuntimeChecks`:** Because `LowerIntrinsics` runs in `run_runtime_cleanup_passes` (before `PostCleanup`) whereas `CheckAlignment`/`CheckNull`/`CheckEnums`/`InstSimplify` run in `run_optimization_passes` (after `PostCleanup`), Miri and any `Runtime(PostCleanup)` verifier see `Operand::RuntimeChecks` from `core::ub_checks::assert_unsafe_precondition!`, while never seeing `CheckAlignment`/`CheckNull`/`CheckEnums` assertions.
3. **Why `InstSimplify` runs twice (`BeforeInline` and `AfterSimplifyCfg`):** Running `InstSimplify::BeforeInline` folds `UbChecks` in the current crate *before* inlining (so ordinary crates collapse their own checks before `.rmeta` export), while `InstSimplify::AfterSimplifyCfg` runs *after* `Inline` pulls in cross-crate `core`/`alloc`/`std` bodies that retained symbolic `Operand::RuntimeChecks(UbChecks)` via `#![rustc_preserve_ub_checks]`, allowing `SimplifyConstCondition::AfterInstSimplify` (`lib.rs:744-752`) to prune dead `precondition_check` calls inside the downstream crate when `-Z ub-checks=no`!

---

### 2. Cross-Crate `Operand::RuntimeChecks` Evaluation Timing and the `InstSimplify` Folding Boundary

Basis: source (`rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) + execution (`rustc 1.98.0-nightly`, `rustc 1.102.0-nightly`) + derived (Lean 4 mechanization)

#### 2.1 Representation and Five Evaluators of `Operand::RuntimeChecks`

In `compiler/rustc_middle/src/mir/syntax.rs:1336-1339, 1588-1608` (`01afe534803b`):

```rust
pub enum Operand<'tcx> {
    Copy(Place<'tcx>),
    Move(Place<'tcx>),
    Constant(Box<ConstOperand<'tcx>>),
    /// Query the compilation session of the current crate for a particular flag. This is not quite
    /// a const since its value can differ across crates within a single crate graph.
    RuntimeChecks(RuntimeChecks),
}

pub enum RuntimeChecks {
    UbChecks,
    ContractChecks,
    OverflowChecks,
}

impl RuntimeChecks {
    pub fn value(self, sess: &rustc_session::Session) -> bool {
        match self {
            Self::UbChecks => sess.ub_checks(),
            Self::ContractChecks => sess.contract_checks(),
            Self::OverflowChecks => sess.overflow_checks(),
        }
    }
}
```

Five distinct consumers encounter `Operand::RuntimeChecks`:

| Consumer | Source Location (`01afe534803b`) | Behavior on `Operand::RuntimeChecks(r)` |
| :--- | :--- | :--- |
| `LowerIntrinsics` (producer) | `compiler/rustc_mir_transform/src/lower_intrinsics.rs:27-43` | Replaces `Call(ub_checks \| overflow_checks \| contract_checks)` with `*dst = Use(Operand::RuntimeChecks(op), WithRetag::Yes)` + `Goto(target)`. |
| MIR optimizers other than `InstSimplify` (`GVN`, `DataflowConstProp`, `SimplifyBranches`, `PromoteConsts`, `JumpThreading`, `KnownPanicsLint`) | `gvn.rs:281, 590, 1041-1050`; `dataflow_const_prop.rs:216`; `simplify_branches.rs:44`; `promote_consts.rs:363-365`; `jump_threading.rs:501`; `known_panics_lint.rs:288` | Treat `Operand::RuntimeChecks` as opaque/non-promotable (`Value::RuntimeChecks`, `ValueOrPlace::TOP`, `Err(Unpromotable)`); `DummyMachine::runtime_checks` (`dummy_machine.rs:117-121`) explicitly `panic!`s if a MIR pass tries to const-evaluate it. |
| `InstSimplify::SimplifyUbCheck` | `compiler/rustc_mir_transform/src/instsimplify.rs:29-37, 472-493` | Runs when `ctx.mir_opt_level() >= 1` AND `!find_attr!(tcx.hir_krate_attrs(), RustcPreserveUbChecks)`. Rewrites **only** `RuntimeChecks::UbChecks` to `ConstValue::from_bool(tcx.sess.ub_checks())`. Leaves `OverflowChecks` and `ContractChecks` untouched. |
| `codegen_ssa` (`codegen_operand`) | `compiler/rustc_codegen_ssa/src/mir/operand.rs:1164-1173` | Evaluates `checks.value(bx.tcx().sess)` using the **codegenning (downstream) crate's `Session`**, emitting a boolean `Immediate`. |
| CTFE (`CompileTimeMachine`) vs. `Miri` (`MiriMachine`) | `rustc_const_eval/src/const_eval/machine.rs:564-571` vs. `src/tools/miri/src/machine.rs:1448-1453` | CTFE unconditionally returns `interp_ok(true)` (to prevent unsound cross-crate const divergence); Miri evaluates `interp_ok(r.value(ecx.tcx.sess))`. |

#### 2.2 Why `core::slice::get_unchecked` Follows Downstream `-Z ub-checks` While User Crates Prematurely Fold

In `compiler/rustc_mir_transform/src/instsimplify.rs:29-37, 481-492` (`01afe534803b`):

```rust
fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
    PassPolicy::optional(ctx.mir_opt_level() >= 1)
}

fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let preserve_ub_checks = find_attr!(tcx.hir_krate_attrs(), RustcPreserveUbChecks);
    if !preserve_ub_checks {
        SimplifyUbCheck { tcx }.visit_body(body);
    }
    ...
}

impl<'tcx> MutVisitor<'tcx> for SimplifyUbCheck<'tcx> {
    fn visit_operand(&mut self, operand: &mut Operand<'tcx>, _: Location) {
        if let Operand::RuntimeChecks(RuntimeChecks::UbChecks) = operand {
            *operand = Operand::Constant(Box::new(ConstOperand {
                span: rustc_span::DUMMY_SP,
                user_ty: None,
                const_: Const::Val(
                    ConstValue::from_bool(self.tcx.sess.ub_checks()),
                    self.tcx.types.bool,
                ),
            }));
        }
    }
}
```

The distributed standard library crates carry the internal crate-level attribute `#![rustc_preserve_ub_checks]` at:
- `library/core/src/lib.rs:66`
- `library/alloc/src/lib.rs:223`
- `library/std/src/lib.rs:227`

Because `core` carries `#![rustc_preserve_ub_checks]`, even though the precompiled sysroot is built with optimizations and without debug assertions, `SimplifyUbCheck` is skipped during `core`'s `optimized_mir`. Thus `core::slice::index::<usize>::get_unchecked` (`library/core/src/slice/index.rs:203-221`), which invokes:

```rust
assert_unsafe_precondition!(
    check_library_ub,
    "slice::get_unchecked requires that the index is within the slice",
    (this: usize = self, len: usize = slice.len()) => this < len
);
```

retains `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` inside `core`'s serialized `.rmeta` MIR. When a downstream crate `down` monomorphizes `get_unchecked`, `down`'s `InstSimplify::AfterSimplifyCfg` (if `down` lacks `#![rustc_preserve_ub_checks]`) or `codegen_operand` evaluates `UbChecks` against **`down`'s** `Session::ub_checks()`. Notice also that `core::slice::index::get_unchecked` specifically picks `check_library_ub` (`pub use intrinsics::ub_checks as check_library_ub`, `library/core/src/ub_checks.rs:88`) rather than `check_language_ub` (`!cfg!(miri) && intrinsics::ub_checks()`, `ub_checks.rs:96-108`) so that Miri and const-eval still produce the richer precondition diagnostic rather than hitting the subsequent `intrinsics::assume(self < slice.len())`.

By contrast, an ordinary upstream library crate `up_lib` has `preserve_ub_checks == false`. When `up_lib` is compiled with `-C opt-level=2 -Z ub-checks=no` — **or even with `-C opt-level=0 -Z ub-checks=no`** (because `OptLevel::No.mir_opt_level() == 1` enables `InstSimplify`!) — `InstSimplify::BeforeInline` executes `SimplifyUbCheck`, replacing `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` with `const false` *inside `up_lib`'s `optimized_mir`* even for `#[inline(always)]` generic functions (`generic_ub_check<T>`). `SimplifyConstCondition::AfterInstSimplify` then deletes the entire check branch before `.rmeta` serialization. In the MIR dumps of `up_lib.generic_ub_check` (from `support/probe_ub_checks_results.json`), `has_ub_checks` drops from `true` (`InstSimplify-before-inline.before.mir`, 92 lines) to `false` (`InstSimplify-before-inline.after.mir`, 92 lines), and the final `runtime-optimized.after.mir` shrinks to 26 lines (`-O2`) or 17 lines (`-O0`) with the panic block completely gone. Downstream `down` compiled with `-Z ub-checks=yes` imports the already-pruned MIR and silently executes the out-of-bounds call with `rc = 0`.

#### 2.3 Docs-vs.-Implementation Discrepancy on `core::intrinsics::ub_checks()`

Basis: documentation (`library/core/src/intrinsics/mod.rs:2659-2662`) vs. source (`compiler/rustc_mir_transform/src/instsimplify.rs:34-37, 481-492`) + execution (`up_yes__down_no`)

The upstream docstring on `core::intrinsics::ub_checks` (`library/core/src/intrinsics/mod.rs:2659-2662`, `01afe534803b`) states:

> "if the crate has UB checks enabled **or** carries the `#[rustc_preserve_ub_checks]` attribute, evaluation is delayed until monomorphization (or until the call gets inlined into a crate that does not delay evaluation further); otherwise it can happen any time."

Direct source inspection and live cross-crate execution **refute** the first disjunct ("if the crate has UB checks enabled"):

- `InstSimplify::run_pass` (`instsimplify.rs:34-37`) checks **only** `find_attr!(tcx.hir_krate_attrs(), RustcPreserveUbChecks)` — it does **not** check `tcx.sess.ub_checks()`!
- Consequently, in configuration `up_yes__down_no` (`up_lib` compiled with `-C opt-level=2 -Z ub-checks=yes`, `down` compiled with `-C opt-level=0 -Z ub-checks=no`), `up_lib.generic_ub_check`'s `InstSimplify-before-inline` folds `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` from `has_ub_checks = true` to `has_ub_checks = false` (`const true`, final `runtime-optimized.after.mir` = 81 lines). When `down` monomorphizes `up_lib::generic_ub_check::<u8>` under `-Z ub-checks=no`, the upstream check is **still baked in as `const true` and panics** (`rc = 101`, `UP_LIB_GENERIC_UB_CHECK_FIRED`), identically on both `rustc 1.98.0-nightly` and `rustc 1.102.0-nightly`!
- Meanwhile, `RuntimeChecks::OverflowChecks` (`up_ovf_no__down_ovf_yes` and `up_ovf_yes__down_ovf_no`) is **not** matched by `SimplifyUbCheck` (`instsimplify.rs:482`), so `up_lib.generic_overflow_check` retains `has_overflow_checks = true` (`96` lines in `runtime-optimized.after.mir`) even at `-C opt-level=2` without `#![rustc_preserve_ub_checks]`, and evaluates purely according to `down`'s `-C overflow-checks` flag (`rc = 101` when `down` sets `overflow-checks=yes`, `rc = 0` when `down` sets `overflow-checks=no`).
- Adding `#![rustc_preserve_ub_checks]` (`up_no_preserve_attr__down_yes`) OR passing `-Z mir-opt-level=0` (`up_no_miropt0__down_yes`) to `up_lib` preserves `has_ub_checks = true` through `up_lib`'s `runtime-optimized.after.mir` (`96` lines and `90` lines respectively), restoring downstream evaluation for both `inlined_oob` and `generic_oob` (`rc = 101`) while `non_generic_oob` (already monomorphized and codegenned in `up_lib` without inlining) stays `rc = 0`.

---

### 3. `CheckAlignment`, `CheckNull`, and `check_pointers`: Projection Asymmetry, ZST Semantics, and Unsized Blind Spots

Basis: normative (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) + source (`rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) + execution (`rustc 1.98.0-nightly`, `Miri`, `rustc 1.102.0-nightly`) + derived (Lean 4 mechanization)

#### 3.1 Shared `check_pointers` Infrastructure (`check_pointers.rs`)

Both `CheckAlignment` and `CheckNull` delegate CFG traversal and block splitting to `check_pointers` (`compiler/rustc_mir_transform/src/check_pointers.rs:43-251`, `01afe534803b`):

1. **Panic-handler guard (`check_pointers.rs:62-64`):** Returns immediately if `tcx.lang_items().get(LangItem::PanicImpl).is_none()` (preventing `#![no_std]` libraries without a panic handler from failing to compile due to newly inserted panic lang-item calls).
2. **Reverse block and statement iteration (`check_pointers.rs:74-76`):** Walks `basic_blocks.indices().rev()` and `(0..statements.len()).rev()` so splitting a block at `location.statement_index` only invalidates statement indices already processed.
3. **Visited `PlaceContext` filter (`PointerFinder::should_visit_place`, `check_pointers.rs:182-198`):**
   - **Visited:** `MutatingUse(Store | Call | Yield | Drop | Borrow)` and `NonMutatingUse(Copy | Move | SharedBorrow)`.
   - **Skipped:** `RawBorrow` (`&raw const (*p).f` / `&raw mut (*p).f`, matching `r[undefined.misaligned.raw]`), `PlaceMention`, `Inspect`, `ShallowBorrow`, `SetDiscriminant`, `Deinit`, `Projection`, `Retag`, etc.
4. **Raw-pointer root extraction (`check_pointers.rs:203-215`):** Requires `place.is_indirect()` and extracts `let pointer = Place::from(place.local);` — rejecting places rooted at references (`&T` / `&mut T`) or `Box<T>` and inspecting **only** `ty::RawPtr(mut pointee_ty, _)`.
   - Note an important implementation nuance: `pointer` is always the *base raw pointer local* `Place::from(place.local)`, NOT an address-computed projection `&raw const (*p).field`!
5. **`BorrowedFieldProjectionMode` switch (`check_pointers.rs:219-228`):**
   ```rust
   if matches!(self.field_projection_mode, BorrowedFieldProjectionMode::FollowProjections)
       && matches!(
           context,
           PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow)
               | PlaceContext::MutatingUse(MutatingUseContext::Borrow)
       )
   {
       pointee_ty = place.ty(self.local_decls, self.tcx).ty;
   }
   ```
6. **Sizedness filter (`check_pointers.rs:231-234`):**
   ```rust
   if !pointee_ty.is_sized(self.tcx, self.typing_env) {
       trace!("Raw pointer, but pointee is not known to be sized: {:?}", pointer_ty);
       return;
   }
   ```
   Every raw pointer to a DST (`*const [T]`, `*const str`, `*const dyn Trait`, or a struct with an unsized tail) is **unconditionally skipped** by both `CheckAlignment` and `CheckNull`!
7. **Array element unwrapping and `excluded_pointees` (`check_pointers.rs:237-245`):** Unwraps a single outer `ty::Array(ty, _)` to its element type and skips if `excluded_pointees.contains(&element_ty)`.

#### 3.2 `CheckAlignment`: Why `FollowProjections` Is Sound for Borrows While Direct Loads Keep Outer Alignment

The Rust Reference (`src/behavior-considered-undefined.md:82-97`, `c9cc32825b03`) draws a crisp distinction between loading/storing a projected place vs. taking a reference to it:

- **`r[undefined.misaligned.ptr]` & `r[undefined.misaligned.load-store]`:** If `ptr: *const S` (`align_of::<S>() == 16`) is misaligned, `(*ptr).byte_field` is "based on a misaligned pointer" even though `byte_field: u8` has alignment 1; **loading from or storing to** `(*ptr).byte_field` is immediate UB!
- **`r[undefined.misaligned.reference]`:** Taking `&(*ptr).byte_field` or `&mut (*ptr).byte_field` requires only the alignment of the **field type** (`align_of::<u8>() == 1`), not `align_of::<S>()`, so `&(*ptr).byte_field` is valid even when `ptr` is only 1-byte aligned (and `&(*ptr).word_field` requires alignment 4, not 16).
- **`r[undefined.misaligned.raw]`:** `&raw const (*ptr).byte_field` has no alignment requirement at all.

`CheckAlignment` (`compiler/rustc_mir_transform/src/check_alignment.rs:20-148`, `01afe534803b`) matches this specification for all sized non-packed structs through three cooperating mechanisms:

1. **Borrow projection replacement (`FollowProjections`):** For `&(*p).byte_field` (`ub_02`), `context` is `SharedBorrow`, so `pointee_ty` becomes `u8`, which is in `excluded_pointees = [bool, i8, u8]` (`check_alignment.rs:22`), emitting **zero** alignment checks (`BYTE=0`, exit `0` under `ub-checks=yes`, `ub-checks=no`, and Miri). For `&(*p).word_field` (`ub_03`), `pointee_ty` becomes `u32`, emitting `addr & (align_of::<u32>() - 1) == 0` (checking multiple of `0x4`, NOT `0x10`; aborts with `SIGABRT` when `addr % 4 == 1`, confirmed by Miri `required 4 byte alignment but found 1`).
2. **Base-address divisibility theorem (`checkAlignment_followProjections_sound`):** Even though `check_pointers.rs:208` tests the *base* pointer address `addr` rather than `addr + field_offset`, for every non-packed struct Rust guarantees `field_align | field_offset`. Therefore `addr % field_align == 0 <-> (addr + field_offset) % field_align == 0` (`mod_add_eq_zero_iff_of_dvd`). (For `#[repr(packed)]` structs, taking `&(*p).field` on any field with `align > 1` is already rejected at compile time by `E0793`, as noted in `r[undefined.misaligned.packed]`.)
3. **Direct load (`Copy`) keeps base pointee type (`ub_12`):** For `let loaded: u8 = unsafe { (*p).byte_field };`, `context` is `NonMutatingUse(Copy)` (NOT `SharedBorrow`), so `FollowProjections` does **not** replace `pointee_ty`. `CheckAlignment` therefore tests `addr` against `align_of::<OverAligned>() == 0x10` (`16`), aborting with `misaligned pointer dereference: address must be a multiple of 0x10` — matching Miri (`accessing memory based on pointer with alignment 1, but alignment 16 is required`), while the preceding `&raw const (*p).byte_field` is skipped by `should_visit_place` and prints `RAW_BORROW_OK=true`!
4. **Target `max_reliable_alignment()` mask weakening (`check_alignment.rs:86-108`):** On targets whose `max_reliable_alignment() < Align::MAX`, `CheckAlignment` further masks `alignment_mask = (align - 1) & (max_align.bytes() - 1)`, weakening the check so it never produces false positives on targets whose allocator/stack cannot guarantee high alignments (proved monotone in `maxReliableAlign_weakening_never_false_aborts`).

#### 3.3 `CheckNull`: ZST Borrow vs. Copy Asymmetry and Cross-Version `AssertKind` Split

The Rust Reference (`r[undefined.dangling.def]` Note 2, `src/behavior-considered-undefined.md:109-110`) specifies that if `size_of::<T>() == 0`, a pointer is trivially never dangling *even if it is null*, so reading/writing (`*p`) a zero-sized value through `core::ptr::null::<()>()` is **not UB**. Conversely, `r[undefined.validity.reference-box]` (`src/behavior-considered-undefined.md:152`) mandates that *every* `&T` / `&mut T` must be non-null — even `&()`!

`CheckNull` (`compiler/rustc_mir_transform/src/check_null.rs:18-128`, `01afe534803b`) passes `excluded_pointees = &[]` and `BorrowedFieldProjectionMode::NoFollowProjections`, and branches directly on `context`:

```rust
let (pointee_should_be_checked, assert_kind) = match context {
    // Borrows pointing to "null" are UB even if the pointee is a ZST.
    PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow)
    | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
        (const_bool(true), AssertKind::NullReferenceConstructed)
    }
    // Other usages of null pointers only are UB if the pointee is not a ZST.
    _ => {
        // pointee_should_be_checked = (size_of::<pointee_ty>() != 0)
        (Operand::Copy(pointee_should_be_checked), AssertKind::NullPointerDereference)
    }
};
// is_ok = !((addr == 0) & pointee_should_be_checked)
```

Three subtleties are load-bearing:

1. **Exact ZST asymmetry (`ub_04`, proved in `checkNull_zst_borrow_vs_copy_iff`):** On `let p: *const () = null();`, `let v = *p;` has `context = Copy`, so `pointee_should_be_checked = (0 != 0) = false`, `is_ok = true`, printing `RAW_ZST_OK=()` under `ub-checks=yes`, `ub-checks=no`, and Miri. Immediately afterward, `let r = &*p;` has `context = SharedBorrow`, so `pointee_should_be_checked = true`, `is_ok = !(true & true) = false`, aborting with `SIGABRT` (`-6`) under `ub-checks=yes` and rejected as UB (`encountered a null reference`) by Miri.
2. **Why `CheckNull` uses `NoFollowProjections`:** For a non-ZST struct `S { z: (), x: u32 }` and a null pointer `p: *const S = null()`, a direct field read `(*p).z` or borrow `&(*p).z` accesses a place based on a null pointer to a non-ZST struct (`r[undefined.dangling.def]`); checking `size_of::<S>() != 0` via `NoFollowProjections` prevents a zero-sized field from masking nullness of the enclosing struct (and for borrows, `pointee_should_be_checked` is unconditionally `true` anyway).
3. **Cross-version `AssertKind` divergence (`1.98.0-nightly` vs. `1.102.0-nightly` / HEAD):** In `1.98.0-nightly` (`14210df0e27c`), `ub_04` aborts with `"null pointer dereference occurred"` (`AssertKind::NullPointerDereference`); in `1.102.0-nightly` (`3ef0c22cdb86`) and HEAD (`01afe534803b`), `ub_04` aborts with `"null reference produced"` (`AssertKind::NullReferenceConstructed`). Any tool matching `AssertKind` or runtime stderr strings across releases must handle both variants.

#### 3.4 Unsized Raw-Pointer Blind Spot (`ub_11`)

Because `check_pointers.rs:231` skips `!pointee_ty.is_sized(self.tcx, self.typing_env)`, `ub_11` (`&*slice_from_raw_parts(misaligned_u32_ptr, 2)`) emits **zero** `CheckAlignment` and **zero** `CheckNull` assertions (`CheckAlignment.before.mir == CheckAlignment.after.mir == 163 lines`, `CheckNull.after.mir == 163 lines`), silently exiting `0` (`UNSIZED_LEN=2`) under `-Z ub-checks=yes`, while Miri immediately rejects it with `Undefined Behavior: constructing invalid value of type &[u32]: encountered an unaligned reference (required 4 byte alignment but found 1)`.

---

### 4. `CheckEnums`: Direct Sign-Extended Masking, `WrappingRange` Modular Arithmetic, Transmute-Only Blind Spots, and the Unmasked Signed-Niche Defect

Basis: normative (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `r[undefined.validity.enum]`) + source (`rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) + execution (`rustc 1.98.0-nightly`, `Miri`, `rustc 1.102.0-nightly`) + derived (Lean 4 mechanization)

#### 4.1 `EnumFinder::visit_rvalue`: Transmute-Only Scope and Layout Dispatch

`CheckEnums` (`compiler/rustc_mir_transform/src/check_enums.rs:166-238`, `01afe534803b`) intentionally restricts instrumentation to `Rvalue::Cast(CastKind::Transmute, op, ty)` where `ty` is an enum ADT:

```rust
impl<'a, 'tcx> Visitor<'tcx> for EnumFinder<'a, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(CastKind::Transmute, op, ty) = rvalue {
            let ty::Adt(adt_def, _) = ty.kind() else { return; };
            if !adt_def.is_enum() { return; }
            ...
            match enum_layout.variants {
                Variants::Empty if op_layout.is_uninhabited() => return,
                Variants::Empty => self.enums.push(EnumCheckType::Uninhabited),
                Variants::Single { .. } => {}
                Variants::Multiple { tag_encoding: TagEncoding::Direct, tag: Scalar::Initialized { value, .. }, .. } => { ... }
                Variants::Multiple { tag_encoding: TagEncoding::Niche { .. }, tag: Scalar::Initialized { value, valid_range, .. }, tag_field, .. } => { ... }
                _ => return,
            }
            self.super_rvalue(rvalue, location);
        }
    }
}
```

Four architectural consequences follow:

1. **Non-`Transmute` blind spots (`ub_07`, mechanized in `ce1_ptr_read_and_union_bypass_checkEnums`):** Constructing an invalid `#[repr(u8)] enum BinaryTag { Zero = 0, One = 1 }` from byte `2u8` via raw-pointer dereference (`*(&raw const invalid_byte as *const BinaryTag)`) or via union field read (`RawOrEnum { raw: 2u8 }.en`) produces **no** `Rvalue::Cast(CastKind::Transmute, ..)` in MIR. `CheckEnums` inserts **zero** `InvalidEnumConstruction` assertions (`CheckEnums.before.mir == CheckEnums.after.mir == 206 lines` on `1.102.0-nightly` and `205 lines` on `1.98.0-nightly`), and both invalid enum constructions execute to completion with `rc = 0` (`BYPASSED_CHECK_ENUMS=1 1`) under `-Z ub-checks=yes`. Miri rejects the invalid enum tag immediately (`encountered 0x02, but expected a valid enum tag`).
2. **Compound/nested enum blind spot:** If `ty` is a struct, tuple, or array *containing* an enum field (e.g., `transmute::<(u8, u8), (BinaryTag, u8)>`), `ty.kind()` is not an enum ADT so `EnumFinder` returns immediately without checking the inner enum.
3. **Subslice tag extraction (`check_enums.rs:278-316`):** When `discr.size.bytes() < op_size.bytes()` (e.g., `Option<(u32, High)>` where the tag byte lies at byte `offset`), `insert_discr_cast_to_u128` transmutes `source_op` into `[MaybeUninit<u8>; op_size]`, takes `ProjectionElem::Subslice { from: offset, to: offset + discr.size, from_end: false }`, and transmutes that subslice into `discr.ty`. When `discr.size.bytes() == op_size.bytes()`, it transmutes `source_op` into unsigned `u8`/`u16`/`u32`/`u64`/`u128` and casts via `CastKind::IntToInt` into `discr.ty`.
4. **Sign/zero extension to `u128` (`check_enums.rs:318-336`):** `insert_discr_cast_to_u128` finally casts `discr_in_discr_ty : discr.ty` via `CastKind::IntToInt` to `u128`. Critically, `discr.ty` is computed from `value.to_int_ty(self.tcx)` (`compiler/rustc_middle/src/ty/layout.rs:188-198`):
   ```rust
   fn to_int_ty<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
       match *self {
           Primitive::Int(i, signed) => i.to_ty(tcx, signed),
           Primitive::Pointer(_) => tcx.data_layout().ptr_sized_integer().to_ty(tcx, false),
           Primitive::Float(_) => bug!("floats do not have an int type"),
       }
   }
   ```
   When `value` is `Primitive::Int(i, true)` (signed!), `discr.ty` is a **signed** integer type (`i8`, `i16`, `i32`, `i64`, `i128`), so `CastKind::IntToInt` to `u128` performs **two's-complement sign extension** (e.g., `-1isize` becomes `0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_u128` and `-10i8` becomes `0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fff6_u128`).

#### 4.2 `insert_direct_enum_check`: Exact Recovery via `& discr.size.unsigned_int_max()`

In `insert_direct_enum_check` (`check_enums.rs:389-418`, `01afe534803b`), `rustc` explicitly masks the `u128` discriminant before switching on the truncated discriminant list:

```rust
let mask = discr.size.unsigned_int_max();
let rvalue = Rvalue::BinaryOp(BinOp::BitAnd, Box::new((Operand::Copy(discr_place), Const(mask))));
// ...
TerminatorKind::SwitchInt {
    discr: Operand::Copy(discr_masked),
    targets: SwitchTargets::new(
        discriminants.into_iter().map(|discr_val| (discr.size.truncate(discr_val), new_block)),
        invalid_discr_block,
    ),
}
```

Because `maskW w (signExtendTo128 w raw) = raw % 2^w` for every width $w \in \{8, 16, 32, 64, 128\}$ (mechanized in `maskW_signExtendTo128` and `insertDirectEnumCheck_signed_mask_sound`), `NegFieldless { MinusOne = -1, PlusOne = 1 }` (`#[repr(isize)]`, `ub_05`) masks `0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_u128 & 0xffff_ffff_ffff_ffff_u128 = 0xffff_ffff_ffff_ffff_u128`, matching `Size(8).truncate((-1i128) as u128)` (`VALID_NEG_OK=-1`), while rejecting `0isize` with `SIGABRT` (`trying to construct an enum from an invalid value 0x0`).

#### 4.3 `insert_niche_check` and `WrappingRange`: Exact Modular Equivalence Under `discr < 2^w`

`rustc_abi::WrappingRange` (`compiler/rustc_abi/src/wrapping_range.rs:19-63`, `01afe534803b`) defines membership as:

```rust
pub struct WrappingRange { pub start: u128, pub end: u128 }

pub fn contains(&self, v: u128) -> bool {
    if self.start <= self.end {
        self.start <= v && v <= self.end
    } else {
        self.start <= v || v <= self.end
    }
}
```

`CheckEnums::insert_niche_check` (`check_enums.rs:478-526`, `01afe534803b`) implements this check in MIR using `u128` wrapping subtraction:

```rust
let discr = insert_discr_cast_to_u128(tcx, local_decls, block_data, source_op, discr, op_size, Some(offset), source_info);
let start_const = Const(valid_range.start : u128);
let end_start_diff_const = Const(u128::wrapping_sub(valid_range.end, valid_range.start) : u128);
// discr_diff = discr - start_const   (BinOp::Sub on u128, wrapping mod 2^128)
// is_ok      = discr_diff <= end_start_diff_const
```

A subtle algebraic property holds for **all** widths $w \in \{8, 16, 32, 64, 128\}$ even though `u128::wrapping_sub` wraps modulo $2^{128}$ rather than modulo $2^w$:

- **Theorem (`insertNicheCheck_u128_iff_wrappingRange_contains`):** Provided `r.start < 2^w`, `r.end_ < 2^w`, and **`discr < 2^w`**, the `u128` comparison `wrappingSub128 discr r.start ≤ wrappingSub128 r.end_ r.start` is **logically equivalent** to `WrappingRange::contains r discr`!
- Concrete trace on `Option<High>` (`#[repr(u8)] enum High { H254 = 254, H255 = 255 }`, `ub_06`), where `valid_range = WrappingRange { start: 254, end: 0 }` and `end_start_diff = 0u128.wrapping_sub(254) = 2^128 - 254`:
  - `discr = 254` (`Some(H254)`): `254 - 254 = 0 <= 2^128 - 254` -> `true` (valid).
  - `discr = 255` (`Some(H255)`): `255 - 254 = 1 <= 2^128 - 254` -> `true` (valid).
  - `discr = 0` (`None`): `0.wrapping_sub(254) = 2^128 - 254 <= 2^128 - 254` -> `true` (valid).
  - `discr = 100` (`0x64`, invalid): `100.wrapping_sub(254) = 2^128 - 154 > 2^128 - 254` -> `false` -> `SIGABRT` (`trying to construct an enum from an invalid value 0x64`).

#### 4.4 Upstream `rustc` Defect: Missing `& unsigned_int_max()` Mask in `insert_niche_check` Breaks Signed Niched Enums in Both Directions

Basis: source (`rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) + execution (`rustc 1.98.0-nightly` + `Miri`, `ub_09` & `ub_10`) + derived (Lean 4 mechanization `ce2_unmasked_high_bits_break_u128_wrapping_niche_check` & `insertNicheCheck_masked_signed_sound`)

Comparing `insert_direct_enum_check` (`check_enums.rs:389-404`) against `insert_niche_check` (`check_enums.rs:478-526`) exposes a genuine **soundness and completeness bug** present across `1.98.0-nightly`, `1.102.0-nightly`, and `rust-lang/rust` HEAD (`01afe534803b`):

1. When layout builds a niched enum around a signed `#[repr(i8)]` (or `i16`/`i32`/`i64`) inner enum (`compiler/rustc_abi/src/layout/enum_layout.rs:614-648`), `niche.reserve(dl, count)` preserves the signed primitive `niche.value = Primitive::Int(I8, true)` inside `Variants::Multiple { tag: niche_scalar, tag_encoding: TagEncoding::Niche { .. }, .. }`.
2. `EnumFinder::visit_rvalue` (`check_enums.rs:223`) passes `discr.ty = value.to_int_ty(self.tcx)` = **`i8`** (signed) to `insert_niche_check`.
3. `insert_niche_check` (`check_enums.rs:478`) calls `insert_discr_cast_to_u128`, which casts the raw byte through `i8` into `u128` via `CastKind::IntToInt`, **sign-extending** any byte with bit 7 set (`0x80..=0xff`) into `[2^128 - 128, 2^128 - 1]`.
4. **Unlike `insert_direct_enum_check`, `insert_niche_check` never applies `& discr.size.unsigned_int_max()`.** Meanwhile `valid_range.{start, end}` remain unextended unsigned `u8` values in `[0, 255]`. Thus the precondition `discr < 2^w` of `insertNicheCheck_u128_iff_wrappingRange_contains` is **violated**, producing **two opposite failures** empirically confirmed against Miri:
   - **False-positive `SIGABRT` on 100% sound, UB-free Rust (`ub_09`):**
     For `#[repr(i8)] enum NegMid { A = -10, B = -9 }`, `Option<NegMid>` has non-wrapping `valid_range = WrappingRange { start: 246, end: 248 }` (`0xf6..=0xf8`, `end_start_diff = 2`). Transmuting valid byte `(-10i8) as u8` (`0xf6`) into `Option<NegMid>` sign-extends to `2^128 - 10` (`0xfffffffffffffffffffffffffffffff6`), yielding `(2^128 - 10).wrapping_sub(246) = 2^128 - 256 > 2`. Under `-Z ub-checks=yes`, `rustc` **falsely aborts** (`rc = -6`, `trying to construct an enum from an invalid value 0xfffffffffffffffffffffffffffffff6`), while both `-Z ub-checks=no` (`rc = 0`) and **Miri** (`rc = 0`, `VALID_NEGMID=Some(A)`) confirm the program has **zero UB**!
   - **False-negative UB bypass on invalid negative bytes (`ub_10`):**
     For `#[repr(i8)] enum NegHigh { MinusTwo = -2, MinusOne = -1 }`, `Option<NegHigh>` has wrapping `valid_range = WrappingRange { start: 254, end: 0 }` (`0xfe..=0xff | 0x00`, `end_start_diff = 2^128 - 254`). Transmuting **invalid** byte `0x80u8` (`-128i8`) sign-extends to `2^128 - 128`, yielding `(2^128 - 128).wrapping_sub(254) = 2^128 - 382 <= 2^128 - 254`, which evaluates to **`true`**! Under `-Z ub-checks=yes`, `rustc` **silently accepts all 126 invalid negative bytes `0x80..=0xfd`** (`rc = 0`, `BYPASSED_SIGNED_NICHE_0x80=true`), while Miri rejects `0x80` as immediate UB (`encountered 0x80, but expected a valid enum tag`) and `rustc` still catches positive invalid bytes like `0x01` (`rc = -6`).
5. **Exact remediation (proved sound and complete in `insertNicheCheck_masked_signed_sound`):** Either mask `discr` with `discr.size.unsigned_int_max()` at the end of `insert_discr_cast_to_u128` (or inside `insert_niche_check` mirroring `check_enums.rs:390-404`), OR emit an unsigned integer type (`value.to_unsigned_int_ty`) for `discr.ty` so `CastKind::IntToInt` zero-extends instead of sign-extending.

---

### 5. Non-Unwinding `UnwindAction::Unreachable` and `#[rustc_nounwind]` Abort Semantics

Basis: source (`rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da`) + execution (`ub_01`, `ub_03`–`ub_06`, `ub_08`, `ub_09`, `ub_12`, `std_get_unchecked_oob`) + derived (Lean 4 mechanization)

All four MIR-pass UB checks (`CheckAlignment`, `CheckNull`, `CheckEnums` direct/uninhabited/niche) emit `TerminatorKind::Assert` with:

```rust
// This calls a panic function associated with the check, which is #[rustc_nounwind].
// We never want to insert an unwind into unsafe code, because unwinding could
// make a failing UB check turn into much worse UB when we start unwinding.
unwind: UnwindAction::Unreachable,
```
(`check_pointers.rs:113-117`, `check_enums.rs:367-370, 458-461, 535-538`).

The end-to-end abort enforcement spans four layers:

1. **MIR Assert-to-LangItem dispatch (`compiler/rustc_codegen_ssa/src/mir/block.rs:801-839`):** `codegen_assert_terminator` maps `MisalignedPointerDereference`, `NullPointerDereference`, `NullReferenceConstructed`, and `InvalidEnumConstruction` to their respective lang items in `library/core/src/panicking.rs:277-338`, each annotated with **`#[rustc_nounwind]`**.
2. **`do_call` unwind override (`compiler/rustc_codegen_ssa/src/mir/block.rs:220-233`):** Because `!fn_abi.can_unwind`, `do_call` forces `unwind = UnwindAction::Unreachable` and emits a plain LLVM `call` (never an `invoke` with a landing pad), so no unwinding edge enters the caller's cleanup pads or an enclosing `catch_unwind` frame.
3. **Runtime non-unwinding abort (`library/core/src/panicking.rs:95-120`):** Each of the four lang items calls `panic_nounwind_fmt`, which constructs `PanicInfo::new(&fmt, Location::caller(), /* can_unwind */ false, false)` (or `abort_immediate()` under `-C panic=immediate-abort`). The panic runtime prints `"thread caused non-unwinding panic. aborting."` and raises `SIGABRT` (`-6`).
4. **Empirical contrast (`ub_08` and cross-crate `std_get_unchecked_oob` vs. `up_lib`):**
   - In `ub_08`, wrapping `unsafe { *core::ptr::null::<u32>() }` inside `std::panic::catch_unwind` **cannot catch** the `CheckNull` panic under `-Z ub-checks=yes`: the process aborts with `SIGABRT` (`-6`) and never reaches `println!("CAUGHT=...")`. Under `-Z ub-checks=no`, the null dereference traps with `SIGSEGV` (`-11`).
   - Similarly, `core::ub_checks::assert_unsafe_precondition!` (`library/core/src/ub_checks.rs:66-75`) marks `precondition_check` `#[rustc_nounwind]` and invokes `panic_nounwind_fmt`, so `std_get_unchecked_oob` aborts with `rc = -6` (`SIGABRT`). By contrast, an ordinary user `panic!()` guarded by `if core::intrinsics::ub_checks()` (as in `up_lib`) is unwinding and exits with `rc = 101`.
   - As mechanized in `ce4_unwinding_ub_check_in_cleanup_causes_double_panic` and `nounwind_contract_violated_triggers_ub`, violating this contract has two hazards: making the panic function unwinding while keeping `UnwindAction::Unreachable` triggers immediate unwinding UB (`ubUnwindIntoUnreachable`), whereas attaching an unwinding `Cleanup`/`Continue` edge to UB checks causes double-panic aborts inside `Drop` cleanup pads and executes user destructors on UB-corrupted invariants.

---

### 6. Anneal Trusted Boundary Implications (`Trusted.MirAst` and `Trusted.MirSemantics`)

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) + derived

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three exact trusted-boundary facts:

1. **Fail-closed exclusion of `Operand::RuntimeChecks` (`trusted/lean/Trusted/MirAst.lean:522-561`):**
   ```lean
   inductive Operand where
     | copy (place : Place)
     | move (place : Place)
     | constant (c : ConstOperand)
   ```
   Lines 548–556 explicitly document that `Operand::RuntimeChecks(RuntimeChecks)` is crate-dependent and intentionally unmodeled in `MirAst.Operand`, so capture **must fail closed (reject the body)** rather than folding it into `.constant`. Our cross-crate findings confirm why this design is strictly necessary:
   - Capturing at `MirPhase::Runtime(RuntimePhase::PostCleanup)` encounters symbolic `Operand::RuntimeChecks(UbChecks)` inside any body calling `core::ub_checks::assert_unsafe_precondition!` (or `core::intrinsics::{ub_checks, overflow_checks, contract_checks}`), because `LowerIntrinsics` runs *before* `PostCleanup`.
   - Capturing at `MirPhase::Runtime(RuntimePhase::Optimized)` instead would silently bake in premature `InstSimplify::SimplifyUbCheck` folding for user crates, diverge from Miri on signed-niche enums (`ub_09`/`ub_10`), and mix crate-flag-dependent UB-check blocks into verified proof obligations!
   - If a future verified compiler or Anneal extension admits `Operand::RuntimeChecks`, it MUST be parameterized over an abstract crate-flag oracle `(r : RuntimeChecks) → Bool` (quantified universally over `{false, true}` for library proofs, or instantiated to the target crate's verified `Session` configuration for whole-program verification) rather than constant-folded.
2. **Partial `AssertKind` coverage (`trusted/lean/Trusted/MirAst.lean:699-741`):**
   ```lean
   inductive AssertKind where
     | overflow (op : BinOp) | overflowNeg | divByZero | remByZero
     | boundsCheck | misalignedPtrDeref | nullPtrDeref | unsupported
   ```
   Lines 727–731 explicitly map `NullReferenceConstructed` (added between `1.98.0-nightly` and `1.102.0-nightly`) and `InvalidEnumConstruction` to `.unsupported`. Any future capture extension handling post-`CheckNull` / post-`CheckEnums` MIR must add explicit constructors (or keep capture strictly at `Runtime(PostCleanup)` before those passes run).
3. **Fail-closed `TerminatorKind.assert` evaluation (`trusted/lean/Trusted/MirSemantics.lean:1568-1569` and `trusted/correspondence/Trusted/Correspondence.lean:2062-2063`):**
   ```lean
   | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
     .fault .unsupported
   ```
   Both `MirSemantics` and `Correspondence` currently fail closed on `.assert` terminators (preventing any unsound omission of `UnwindAction::Unreachable` / `#[rustc_nounwind]` semantics until `TerminatorKind.assert` is operationally modeled).

---

### 7. Differential Empirical Matrix (`rustc 1.98.0-nightly`, `Miri 1.98.0-nightly`, and `rustc 1.102.0-nightly`)

Basis: execution (`support/probe_ub_checks_runtime_checks_and_check_enums.py` -> `support/probe_ub_checks_results.json` on `rustc 1.98.0-nightly` + `Miri`; recorded baseline on `rustc 1.102.0-nightly`)

#### 7.1 Single-Crate 12-Case Differential Matrix

In `ub_01`, `ub_02`, `ub_03`, `ub_11`, and `ub_12`, the stack buffer uses `#[repr(align(16))] struct AlignedBuf([u8; N]);` so `buf.0.as_ptr().add(1)` is deterministically congruent to `1 (mod 16)` across both native execution and Miri's randomized allocator.

| Case | `1.98` `ub-checks=yes` | `1.98` `ub-checks=no` | `Miri 1.98` Oracle | `1.102` `ub-checks=yes` / `no` | Key Finding / Diagnostic |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `ub_01` Misaligned `*const u32` read | `rc=-6` (`SIGABRT`) | `rc=0` (`V=0`) | `rc=1` (UB: align 1 vs 4) | `rc=-6` / `rc=0` (`V=0`) | `CheckAlignment` emits `MisalignedPointerDereference` (`0x4`); matches across `1.98`/`1.102`/Miri. |
| `ub_02` `&(*p).byte_field` (`u8` of `align(16)`) | `rc=0` (`BYTE=0`) | `rc=0` (`BYTE=0`) | `rc=0` (`BYTE=0`, no UB) | `rc=0` / `rc=0` (`BYTE=0`) | `FollowProjections` switches to `u8` (excluded); 0 misaligned asserts emitted; matches `r[undefined.misaligned.reference]`. |
| `ub_03` `&(*p).word_field` (`u32` of `align(16)`) | `rc=-6` (`SIGABRT`, `0x4`) | `rc=0` (`WORD=0`) | `rc=1` (UB: align 4 vs 1) | `rc=-6` (`0x4`) / `rc=0` (`WORD=0`) | `FollowProjections` checks `u32` align `0x4` (not struct align `0x10`). |
| `ub_04` ZST `*null::<()>()` vs `&*null::<()>()` | `rc=-6`, `RAW_ZST_OK=()`, `"null pointer dereference occurred"` | `rc=0` (`RAW_ZST_OK=()\nREF_ZST=0x0`) | `rc=1`, `RAW_ZST_OK=()`, UB: null ref `&()` | `rc=-6`, `RAW_ZST_OK=()`, `"null reference produced"` / `rc=0` | Raw ZST copy permitted; ZST borrow rejected. **Version delta:** `1.98` emits `NullPointerDereference`, `1.102`/HEAD emits `NullReferenceConstructed`. |
| `ub_05` Direct negative `isize` enum (`-1` ok, `0` bad) | `rc=-6`, `VALID_NEG_OK=-1`, invalid `0x0` | `rc=0` (`VALID_NEG_OK=-1\nINVALID_ZERO=0`) | `rc=1`, `VALID_NEG_OK=-1`, UB: `0x0` | `rc=-6` / `rc=0` | `insert_direct_enum_check` masks sign-extended `-1isize` via `& unsigned_int_max()`, accepts `-1`, aborts on `0x0`. |
| `ub_06` Wrapping niche `Option<High>` (`254`, `0` ok; `100` bad) | `rc=-6`, `WRAP_OK=true true`, invalid `0x64` | `rc=0` (`WRAP_OK=true true\nWRAP_BAD=true`) | `rc=1`, `WRAP_OK=true true`, UB: `0x64` | `rc=-6` / `rc=0` | `insert_niche_check` handles unsigned `WrappingRange { 254, 0 }` accurately via `u128::wrapping_sub`. |
| `ub_07` `CheckEnums` blind spot (`*p` & `union` read of `2u8`) | `rc=0` (`BYPASSED_CHECK_ENUMS=1 1`) | `rc=0` (`BYPASSED_CHECK_ENUMS=1 1`) | `rc=1` (UB: invalid tag `0x02`) | `rc=0` / `rc=0` (`BYPASSED_CHECK_ENUMS=1 1`) | **Blind spot:** `EnumFinder` visits only `CastKind::Transmute`; 0 `InvalidEnumConstruction` asserts emitted. |
| `ub_08` Null deref inside `catch_unwind` | `rc=-6` (`SIGABRT`, uncaught) | `rc=-11` (`SIGSEGV`) | `rc=1` (UB: null 4B access) | `rc=-6` / `rc=-11` | `UnwindAction::Unreachable` + `#[rustc_nounwind]` forces `SIGABRT` even inside `catch_unwind`. |
| `ub_09` Signed niche **false positive** (`Option<NegMid>`, valid `0xf6`) | **`rc=-6` (`SIGABRT`, `0xfffffffffffffffffffffffffffffff6`)** | `rc=0` (`VALID_NEGMID=Some(A)`) | **`rc=0` (`VALID_NEGMID=Some(A)`, NO UB!)** | Not executed on `1.102`; **derived** same bug from identical `check_enums.rs` | **Real `rustc` bug:** Unmasked sign-extension in `insert_niche_check` falsely aborts a UB-free Rust program! |
| `ub_10` Signed niche **false negative** (`Option<NegHigh>`, invalid `0x80`) | **`rc=0` (`BYPASSED_SIGNED_NICHE_0x80=true`)** | `rc=0` (`BYPASSED_SIGNED_NICHE_0x80=true`) | **`rc=1` (UB: invalid tag `0x80`)** | Not executed on `1.102`; **derived** same bug from identical `check_enums.rs` | **Real `rustc` bug:** Sign-extended `2^128 - 128` falsely satisfies `wrapping_sub <= 2^128 - 254`, bypassing `CheckEnums`. |
| `ub_11` Unsized `*const [u32]` misaligned borrow | **`rc=0` (`UNSIZED_LEN=2`)** | `rc=0` (`UNSIZED_LEN=2`) | **`rc=1` (UB: align 4 vs 1)** | Not executed on `1.102`; **derived** from identical `check_pointers.rs:231` | **Blind spot:** `!pointee_ty.is_sized` skips all DST raw pointers; 0 assertions emitted. |
| `ub_12` `&raw const (*p).byte_field` vs direct load `(*p).byte_field` | `rc=-6`, `RAW_BORROW_OK=true`, `multiple of 0x10` | `rc=0` (`RAW_BORROW_OK=true\nDIRECT_FIELD_LOAD=0`) | `rc=1`, `RAW_BORROW_OK=true`, UB: align 1 vs 16 | Not executed on `1.102`; **derived** from identical `check_pointers.rs` | `&raw const` skipped (`r[undefined.misaligned.raw]`); direct `Copy` checks outer struct align `0x10` (`r[undefined.misaligned.ptr]`). |

#### 7.2 Cross-Crate `up_lib` -> `down` `RuntimeChecks` 9-Configuration Matrix

All 9 configurations ran live on `rustc 1.98.0-nightly` (`14210df0e27c`); configurations `up_no__down_yes` and `up_yes__down_no` also matched the recorded `rustc 1.102.0-nightly` (`3ef0c22cdb86`) baseline on every call (`inlined_oob`, `generic_oob`, `non_generic_oob`, `std_get_unchecked_oob`).

| Configuration | `up_lib` Flags & Attrs | `down` Flags | `up_lib` `generic` MIR `UbChecks`/`Ovf` (`before` -> `after InstSimplify` -> `optimized`) | `inlined_oob` | `generic_oob` | `non_generic_oob` | `std_get_unchecked_oob` | `generic_overflow_check_oob` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `up_no__down_no` | `-O2 -Z ub-checks=no` | `-O0 -Z ub-checks=no` | `ub: T -> F -> F` (26L) | `rc=0` | `rc=0` | `rc=0` | `rc=0` | — |
| `up_no__down_yes` | `-O2 -Z ub-checks=no` | `-O0 -Z ub-checks=yes` | `ub: T -> F -> F` (26L) | **`rc=0` (erased!)** | **`rc=0` (erased!)** | `rc=0` | **`rc=-6` (`SIGABRT`)** | — |
| `up_yes__down_no` | `-O2 -Z ub-checks=yes` | `-O0 -Z ub-checks=no` | `ub: T -> F -> F` (81L) | **`rc=101` (baked!)** | **`rc=101` (baked!)** | `rc=101` | `rc=0` | — |
| `up_yes__down_yes` | `-O2 -Z ub-checks=yes` | `-O0 -Z ub-checks=yes` | `ub: T -> F -> F` (81L) | `rc=101` | `rc=101` | `rc=101` | `rc=-6` (`SIGABRT`) | — |
| `up_no_opt0_default__down_yes` | `-O0 -Z ub-checks=no` | `-O0 -Z ub-checks=yes` | `ub: T -> F -> F` (17L) | **`rc=0` (still erased at `-O0`!)** | **`rc=0` (still erased at `-O0`!)** | `rc=0` | `rc=-6` (`SIGABRT`) | — |
| `up_no_miropt0__down_yes` | `-O0 -Z mir-opt-level=0 -Z ub-checks=no` | `-O0 -Z ub-checks=yes` | `ub: T` (90L, `InstSimplify` skipped) | **`rc=101` (restored)** | **`rc=101` (restored)** | `rc=0` | `rc=-6` (`SIGABRT`) | — |
| `up_no_preserve_attr__down_yes` | `-O2 -Z ub-checks=no` + `#![rustc_preserve_ub_checks]` | `-O0 -Z ub-checks=yes` | `ub: T -> T -> T` (96L) | **`rc=101` (restored)** | **`rc=101` (restored)** | `rc=0` | `rc=-6` (`SIGABRT`) | — |
| `up_ovf_no__down_ovf_yes` | `-O2 -C overflow-checks=no` | `-O0 -C overflow-checks=yes` | `ovf: T -> T -> T` (96L) | — | — | — | — | **`rc=101` (follows `down`!)** |
| `up_ovf_yes__down_ovf_no` | `-O2 -C overflow-checks=yes` | `-O0 -C overflow-checks=no` | `ovf: T -> T -> T` (96L) | — | — | — | — | **`rc=0` (follows `down`!)** |

---

### 8. Kernel-Checked Lean 4 Formalization (`MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean`)

Basis: derived (kernel-checked in Lean `v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)

`support/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean` (`1,169` lines, `54,861` bytes) mechanizes the full mathematical structure of the passes and counterexamples using only Lean 4 core `Init` (zero external dependencies, zero `import Lean`). Verified under strict flags (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and audited via `support/audit_lean_purity.lean` over `env.constants.map₁`:

- **Total module constants in `env.constants.map₁`:** `429`
- **Explicit user `theorem` declarations:** `47` (`122` total `.thmInfo` entries including compiler-generated equational lemmas)
- **Axioms used across all `122` theorem constants:** `#[propext]` only (**`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`**)
- **Purity violations:** `0` `._unsafe_rec`, `0` `unsafe` declarations, `0` `partial def`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `sorry`.

#### Core Mechanized Theorem Catalog

| Theorem / Witness | Line (`MirUbChecks...lean`) | Formalized Property | Upstream / Empirical Correspondence |
| :--- | :---: | :--- | :--- |
| `maskW_signExtendTo128` | L181 | `∀ w raw, maskW w (signExtendTo128 w raw) = raw % 2^w` for all `w ∈ {8,16,32,64,128}` | `check_enums.rs:389-404`, `ub_05` |
| `checkNullPasses_eq_false_iff_nullAccessIsUB` | L371 | Exact soundness & completeness of `CheckNull` for all sized pointees, contexts, and addresses | `check_null.rs:55-128`, `r[undefined.dangling.def]`, `r[undefined.validity.reference-box]` |
| `checkNull_zst_borrow_vs_copy_iff` | L394 | For any sized ZST at `addr = 0`, `CheckNull` aborts iff `isBorrowContext ctx = true` (`&*p`/`&mut *p` -> `false` with `NullReferenceConstructed`; `*p` copy/move -> `true` with `NullPointerDereference`) | `check_null.rs:55-88`, `ub_04` |
| `checkAlignment_followProjections_sound` | L441 | For any non-packed sized place (`fieldAlign ∣ fieldOffset`), `CheckAlignment` under `FollowProjections` passes iff `refAlignmentRequired` holds (covering borrows, direct loads, raw borrows, and `[bool,i8,u8]` exclusion) | `check_alignment.rs:20-148`, `check_pointers.rs:182-249`, `ub_01`, `ub_02`, `ub_03`, `ub_12` |
| `maxReliableAlign_weakening_never_false_aborts` | L485 | `cap ∣ reqAlign → addr % reqAlign = 0 → addr % cap = 0` | `check_alignment.rs:86-108` |
| `insertDirectEnumCheck_signed_mask_sound` | L528 | `insert_direct_enum_check` (sign-extend + `maskW`) agrees identically with unsigned width-`w` discriminant membership | `check_enums.rs:338-419`, `ub_05` |
| `insertNicheCheck_u128_iff_wrappingRange_contains` | L635 | `∀ w r discr, r.start < 2^w → r.end_ < 2^w → discr < 2^w → insertNicheCheckU128 r discr = r.contains discr` | `check_enums.rs:466-541`, `wrapping_range.rs:57-63`, `ub_06` |
| `insertNicheCheck_masked_signed_sound` | L680 | Adding `maskW w` after `signExtendTo128 w` restores exact equivalence with `WrappingRange::contains` for signed and unsigned tags at every width `w` | Remediation of `ub_09` & `ub_10` |
| `preserveUbChecks_evaluates_in_downstream` | L766 | `up.preserveUbChecks = true → crossCrateGenericCheck up down .ubChecks = down.ubChecks` | `instsimplify.rs:34-37`, `core/lib.rs:66`, `up_no_preserve_attr__down_yes`, `std_get_unchecked_oob` |
| `mirOptZero_evaluates_in_downstream` | L776 | `up.mirOptLevel = 0 → crossCrateGenericCheck up down .ubChecks = down.ubChecks` | `instsimplify.rs:29-31`, `up_no_miropt0__down_yes` |
| `overflowAndContractChecks_always_evaluate_in_downstream` | L788 | `OverflowChecks` and `ContractChecks` always survive `InstSimplify` and evaluate in `down` | `instsimplify.rs:482`, `up_ovf_no__down_ovf_yes`, `up_ovf_yes__down_ovf_no` |
| `runtimeChecks_crate_graph_monotonic` | L799 | Downstream check-flag monotonicity across all `RuntimeCheckKind`s | `syntax.rs:1588-1608`, `codegen_ssa/operand.rs:1164-1173` |
| `premature_fold_runtimeChecks_erases_downstream_ubCheck` | L827 | `up.preserveUbChecks = false ∧ up.mirOptLevel ≥ 1 ∧ up.ubChecks = false ∧ down.ubChecks = true → crossCrateGenericCheck = false ≠ down.ubChecks` | `instsimplify.rs:34-37, 481-492`, `up_no__down_yes`, `up_no_opt0_default__down_yes` |
| `premature_fold_refutes_ubChecks_docstring` | L847 | `up.preserveUbChecks = false ∧ up.mirOptLevel ≥ 1 ∧ up.ubChecks = true ∧ down.ubChecks = false → crossCrateGenericCheck = true ≠ down.ubChecks` | Refutes `core/intrinsics/mod.rs:2660-2662`, `up_yes__down_no` |
| `ctfe_runtimeChecks_crate_graph_invariant` & `anneal_capture_rejects_symbolic_runtimeChecks` | L864, L873 | CTFE always returns `true`; Anneal capture rejects every `.symbolic` `RuntimeChecks` operand fail-closed | `const_eval/machine.rs:564-571`, `Trusted/MirAst.lean:548-556` |
| `nounwind_ubCheck_aborts_even_inside_catchUnwind` & `nounwind_contract_violated_triggers_ub` | L929, L941 | `#[rustc_nounwind]` + `UnwindAction::Unreachable` yields `.abortNonUnwinding` in all frames; unwinding into `Unreachable` is UB | `check_pointers.rs:117`, `panicking.rs:95-120, 277-338`, `ub_08` |
| `ce1_ptr_read_and_union_bypass_checkEnums` | L967 | Constructive witness: invalid `BinaryTag` byte `2` bypasses `CheckEnums` under `.rawPtrRead` and `.unionFieldRead` | `check_enums.rs:168`, `ub_07` |
| `ce2_unmasked_high_bits_break_u128_wrapping_niche_check` | L1003 | Constructive witness: unmasked `256`, false negative on `Option<NegHigh>` `0x80`, false positive on `Option<NegMid>` `0xf6`, and exact repair via `maskW .w8` | `check_enums.rs:478-526`, `ub_09`, `ub_10` |
| `ce3_noFollowProjections_false_positive_on_byte_field_borrow` | L1077 | Constructive witness: `NoFollowProjections` falsely rejects valid `&(*p).byte_field`, while `FollowProjections` accepts it, rejects direct `Copy` load `(*p).byte_field`, and checks `&(*p).word_field` at align 4 | `check_alignment.rs:32`, `ub_02`, `ub_03`, `ub_12` |
| `ce4_unwinding_ub_check_in_cleanup_causes_double_panic` | L1094 | Constructive witness: unwinding UB check inside `Drop` cleanup causes `.doublePanicAbort` and inside `catch_unwind` is caught instead of aborting | `check_pointers.rs:113-117`, `ub_08` |
| `ce5_unsized_slice_raw_ptr_bypasses_checkPointers` | L1116 | Constructive witness: `isSized = false` causes `CheckAlignment` and `CheckNull` to skip misaligned and null `*const [u32]` borrows | `check_pointers.rs:231`, `ub_11` |
| `unified_ub_checks_soundness_under_repaired_invariants` | L1140 | Combined end-to-end soundness contract uniting all four repaired invariants | Whole-pipeline synthesis |

## Boundaries

The following negative-space boundaries and non-claims qualify every finding above:

- **Not examined:**
  - Non-`x86_64-unknown-linux-gnu` execution targets (such as `i686`, `aarch64`, `wasm32`, or targets with `target.max_reliable_alignment() < Align::MAX`, e.g., `m68k` / AVR / strict-alignment embedded targets). The `max_reliable_alignment` code path in `check_alignment.rs:86-108` was verified by source inspection and Lean proof (`maxReliableAlign_weakening_never_false_aborts`), not live target execution.
  - `-C panic=immediate-abort` codegen (verified by source inspection of `library/core/src/panicking.rs:283-331`, not native binary execution) and Cranelift / GCC (`rustc_codegen_cranelift`, `rustc_codegen_gcc`) codegen of `Operand::RuntimeChecks` and `TerminatorKind::Assert`.
  - Live execution of `ub_09`–`ub_12` and the 7 expanded cross-crate configurations on a compiled `rustc 1.102.0-nightly` (`3ef0c22cdb86`) or HEAD (`01afe534803b`) binary; those extensions were executed live on `rustc 1.98.0-nightly` (`14210df0e27c`) + `Miri` and extended to `1.102.0-nightly`/HEAD via exact source diffing.
  - Multi-field niche enums where `discr.size.bytes() < op_size.bytes()` (`[MaybeUninit<u8>; N]` + `Subslice` path in `check_enums.rs:278-304`), `#[feature(contracts)]` AST lowering of `contract_checks` (`compiler/rustc_ast_lowering/src/contract.rs:186-341`), and `-Z extra-const-ub-checks` CTFE checks.
  - Custom `#[rustc_layout_scalar_valid_range_start]` / `#[rustc_layout_scalar_valid_range_end]` non-enum types (such as `NonZero<T>`, `NonNull<T>`, `char`, `bool`): these are **not** enum ADTs, so `CheckEnums` does not inspect `transmute::<u8, bool>(2)` or `transmute::<u32, NonZero<u32>>(0)`.
- **Unknown:**
  - Whether any upstream `rust-lang/rust` issue or PR has already been filed for the signed-niche unmasked sign-extension defect (`ub_09`/`ub_10`) or the `core::intrinsics::ub_checks()` docstring mismatch (`library/core/src/intrinsics/mod.rs:2660-2662`) after `01afe534803b` (`2026-11-22`).
  - Whether future `rustc` releases will extend `CheckNull`/`CheckAlignment` to unsized pointers (`*const [T]`, `*const dyn Trait`) by computing dynamic alignment via `align_of_val_raw` and dynamic size via `size_of_val_raw`.
- **Known not to apply:**
  - **Runtime UB checks are NOT a complete UB detector and cannot be relied on for safety.** As proved by `ub_07`, `ub_10`, `ub_11` (and explicitly stated in `assert_unsafe_precondition!`'s panic message), `CheckAlignment`, `CheckNull`, and `CheckEnums` miss unsized raw pointers, non-`Transmute` invalid enum constructions (`*p`, `union` field reads, compound-type transmutes), signed-niche negative invalid tags (`ub_10`), dangling-but-non-null pointers (use-after-free, out-of-bounds), aliasing violations (Stacked/Tree Borrows), uninitialized memory reads, and data races.
  - **`CheckAlignment` base-pointer divisibility does NOT generalize to `#[repr(packed)]` field projections** if a raw-pointer borrow could somehow bypass `E0793`, because `field_align | field_offset` fails for packed structs.
  - **The Lean 4 formalization does NOT import `joshlf/anneal`'s `Trusted.MirSemantics` or `rustc`'s Rust compiler implementation directly.** It is a faithful standalone mathematical model of the exact MIR pass logic, wrapping arithmetic, crate-flag pipeline, and unwind semantics audited in `rust-lang/rust@01afe534803b` and cross-checked against live `rustc` + `Miri`; proving full compiler implementation refinement requires connecting these theorems to an executable Rust/MIR semantics.
- **Unsupported:**
  - `joshlf/anneal@c131b320eeeb` (`Trusted.MirAst` and `Trusted.MirSemantics`) explicitly does not support `Operand::RuntimeChecks`, `AssertKind::NullReferenceConstructed`, `AssertKind::InvalidEnumConstruction`, or operational execution of `TerminatorKind::Assert` (all fail closed via capture rejection or `.fault .unsupported`).
  - `rustc`'s `DummyMachine` (used by MIR optimizations) does not support evaluating `Operand::RuntimeChecks` (`dummy_machine.rs:120`: `panic!("compiletime machine evaluated {r:?}")`).

## Evidence

### Primary Upstream Sources

All Git commit SHAs below were resolved and verified directly against GitHub on `2026-11-22`:

1. **`rust-lang/rust` @ `01afe534803b93889b85f6028117251cfbd431da` (HEAD, `2026-11-22`):**
   - `compiler/rustc_mir_transform/src/check_alignment.rs:12-148` (`CheckAlignment`, `PassPolicy::optional(ctx.ub_checks())`, `excluded_pointees = [bool, i8, u8]`, `FollowProjections`, `max_reliable_alignment()` mask cap, `AssertKind::MisalignedPointerDereference`).
   - `compiler/rustc_mir_transform/src/check_null.rs:10-128` (`CheckNull`, `NoFollowProjections`, `SharedBorrow | Borrow` -> `(true, AssertKind::NullReferenceConstructed)` vs. `_` -> `(size_of != 0, AssertKind::NullPointerDereference)`).
   - `compiler/rustc_mir_transform/src/check_enums.rs:16-541` (`CheckEnums`, `EnumFinder::visit_rvalue` `CastKind::Transmute`-only visitor L167-237, `insert_discr_cast_to_u128` L257-336, `insert_direct_enum_check` `& unsigned_int_max()` L338-419, `insert_uninhabited_enum_check` L421-464, `insert_niche_check` unmasked `u128::wrapping_sub` L466-541).
   - `compiler/rustc_mir_transform/src/check_pointers.rs:10-251` (`BorrowedFieldProjectionMode`, `check_pointers` `push_with` block splitting and `UnwindAction::Unreachable` L105-165, `PointerFinder::should_visit_place` L182-198, `visit_place` base local + `FollowProjections` + `!is_sized` skip + array unwrap L202-250).
   - `compiler/rustc_mir_transform/src/lib.rs:684-789` (`run_runtime_cleanup_passes` -> `Runtime(PostCleanup)`, `run_optimization_passes` pass order).
   - `compiler/rustc_mir_transform/src/lower_intrinsics.rs:27-43` (`ub_checks | overflow_checks | contract_checks` -> `Operand::RuntimeChecks`).
   - `compiler/rustc_mir_transform/src/instsimplify.rs:16-38, 472-493` (`InstSimplify::{BeforeInline, AfterSimplifyCfg}`, `mir_opt_level >= 1`, `RustcPreserveUbChecks` gate, `SimplifyUbCheck` matching only `RuntimeChecks::UbChecks`).
   - `compiler/rustc_mir_transform/src/pass_manager.rs:88-165` (`PassPolicy::{Required, Optional}`).
   - `compiler/rustc_mir_transform/src/cost_checker.rs:64-81, 131-159` (`RuntimeChecks::UbChecks` inlining bonus).
   - `compiler/rustc_middle/src/mir/syntax.rs:1018-1056, 1336-1339, 1588-1608` (`UnwindAction`, `AssertKind`, `Operand::RuntimeChecks`, `RuntimeChecks::value`).
   - `compiler/rustc_middle/src/mir/terminator.rs:170-318` (`AssertKind::panic_function`, `fmt_assert_args`).
   - `compiler/rustc_middle/src/ty/layout.rs:188-198` (`PrimitiveExt::to_int_ty` preserving `signed` on `Primitive::Int(i, signed)`).
   - `compiler/rustc_abi/src/wrapping_range.rs:19-63` (`WrappingRange`, `WrappingRange::contains`).
   - `compiler/rustc_abi/src/layout/enum_layout.rs:614-648` (`niche.reserve(dl, count)` preserving signed `niche_scalar` inside `TagEncoding::Niche`).
   - `compiler/rustc_session/src/session.rs:988-990, 1091-1101` (`mir_opt_level`, `overflow_checks`, `ub_checks`, `contract_checks`).
   - `compiler/rustc_session/src/config.rs:123-128` (`OptLevel::mir_opt_level`: `No => 1`, `_ => 2`).
   - `compiler/rustc_codegen_ssa/src/mir/operand.rs:1164-1173` (`Operand::RuntimeChecks` codegen via `checks.value(bx.tcx().sess)`).
   - `compiler/rustc_codegen_ssa/src/mir/block.rs:220-233, 752-841` (`do_call` `!fn_abi.can_unwind` forcing `UnwindAction::Unreachable`; `codegen_assert_terminator` lang-item dispatch).
   - `compiler/rustc_const_eval/src/const_eval/machine.rs:564-571` (`CompileTimeMachine::runtime_checks` returning `interp_ok(true)`).
   - `src/tools/miri/src/machine.rs:1448-1453` (`MiriMachine::runtime_checks` returning `interp_ok(r.value(ecx.tcx.sess))`).
   - `library/core/src/lib.rs:66`, `library/alloc/src/lib.rs:223`, `library/std/src/lib.rs:227` (`#![rustc_preserve_ub_checks]`).
   - `library/core/src/ub_checks.rs:53-108` (`assert_unsafe_precondition!`, `check_library_ub`, `check_language_ub`).
   - `library/core/src/slice/index.rs:203-233` (`get_unchecked` / `get_unchecked_mut` using `check_library_ub`).
   - `library/core/src/intrinsics/mod.rs:2659-2705` (`ub_checks()` docstring discrepancy vs. `InstSimplify`).
   - `library/core/src/panicking.rs:95-120, 277-338` (`panic_nounwind_fmt`, `#[rustc_nounwind]` on all four UB-check panic lang items).
2. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`):**
   - Diffed verbatim against `01afe534803b` across `check_alignment.rs`, `check_null.rs`, `check_enums.rs`, `check_pointers.rs`, `lib.rs`, `instsimplify.rs`, `syntax.rs`, and `ub_checks.rs`.
   - Recorded native execution & MIR dumps for `ub_01`–`ub_08`, `up_no__down_yes`, and `up_yes__down_no` on `rustc 1.102.0-nightly` (LLVM `23.1.5`, `x86_64-unknown-linux-gnu`).
3. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`):**
   - Diffed verbatim against `3ef0c22cdb86` across `check_alignment.rs`, `check_null.rs`, `check_enums.rs`, and `check_pointers.rs`, isolating the `NullReferenceConstructed` split and `is_required() -> PassPolicy::optional` transition.
   - Live execution of all 12 single-crate probes (native `-Z ub-checks={yes,no}` + MIR dumps + `Miri`) and all 9 cross-crate configurations captured in `support/probe_ub_checks_results.json`.
4. **`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`2026-11-17`):**
   - `src/behavior-considered-undefined.md:19, 82-110, 139-153` (`r[undefined.pointer-access]`, `r[undefined.misaligned.*]`, `r[undefined.dangling.def]`, `r[undefined.validity.enum]`, `r[undefined.validity.reference-box]`).
5. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`):**
   - `trusted/lean/Trusted/MirAst.lean:522-561, 699-741, 785-796` (`Operand`, `AssertKind`, `TerminatorKind`).
   - `trusted/lean/Trusted/MirSemantics.lean:1568-1569` (`evalTerminator` `.assert` -> `.fault .unsupported`).
   - `trusted/correspondence/Trusted/Correspondence.lean:181, 406, 483, 2062-2063`.

### Preserved Package Support Artifacts

| Path | Description | Verification Status (`2026-11-22`) |
| :--- | :--- | :--- |
| `support/probe_ub_checks_runtime_checks_and_check_enums.py` | Standalone Python 3.10+ stdlib differential harness running all 12 single-crate probes (`rustc -Z ub-checks={yes,no}`, MIR pass dumps, `Miri`) and all 9 cross-crate `up_lib -> down` configurations. | Executed cleanly (`exit 0`) on `rustc 1.98.0-nightly` + `Miri`. |
| `support/probe_ub_checks_results.json` | Sanitized JSON execution trace and MIR dump summary produced by `probe_ub_checks_runtime_checks_and_check_enums.py`. | Zero volatile paths/PIDs; reproduces all 12 single-crate and 9 cross-crate results reported in Section 7. |
| `support/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean` | Standalone `1,169`-line Lean 4 (`v4.34.1`) formalization (`47` user theorems, `122` `.thmInfo` constants, `429` module constants). | Passes `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, `0` warnings). |
| `support/audit_lean_purity.lean` | Standalone Lean 4 metaprogramming auditor inspecting `env.constants.map₁` and `Lean.collectAxioms` across every declaration in `MirUbChecksRuntimeChecksAndCheckEnumsSoundness`. | Passes (`exit 0`): `AUDIT_TOTAL_CONSTS=429`, `AUDIT_THEOREMS=122`, `AUDIT_ALL_AXIOMS_USED=#[propext]`, `AUDIT_UNSAFE_RECS=0`, `AUDIT_UNSAFE_DECLS=0`, `AUDIT_FORBIDDEN_AXIOMS=0`. |

## Revalidation

To cheaply revalidate these findings against a newer `rustc`, `Miri`, `joshlf/anneal`, or `Lean 4` toolchain:

1. **Re-run the differential `rustc` + `Miri` probe (takes ~10s):**
   ```bash
   python3 support/probe_ub_checks_runtime_checks_and_check_enums.py --out /tmp/reval_ubchk.json
   ```
   Key discriminating assertions to check in `/tmp/reval_ubchk.json`:
   - **`ub_04`:** Confirms `RAW_ZST_OK=()` succeeds and `&*null::<()>()` aborts (`rc = -6`) with `"null reference produced"` (`AssertKind::NullReferenceConstructed` on `>= 1.102`).
   - **`ub_09` & `ub_10` (signed-niche regression detector):** If `ub_09` switches from `rc = -6` to `rc = 0` (`VALID_NEGMID=Some(A)`) AND `ub_10` switches from `rc = 0` to `rc = -6` (aborting on invalid `0x80`), upstream has fixed the missing `& discr.size.unsigned_int_max()` mask in `CheckEnums::insert_niche_check`!
   - **`ub_07` & `ub_11` (coverage expansion detectors):** If `ub_07` switches to `rc = -6`, `CheckEnums` has expanded beyond `CastKind::Transmute`; if `ub_11` switches to `rc = -6`, `check_pointers` has added unsized DST raw-pointer support.
   - **`up_yes__down_no` & `up_no_opt0_default__down_yes` (folding policy detectors):** If `up_yes__down_no`'s `generic_oob` switches from `rc = 101` to `rc = 0`, `InstSimplify::SimplifyUbCheck` has been updated to honor `core::intrinsics::ub_checks()`'s docstring (`sess.ub_checks()` delaying evaluation).

2. **Diff the 5 determining upstream `rustc` files against `01afe534803b93889b85f6028117251cfbd431da`:**
   ```bash
   git diff 01afe534803b93889b85f6028117251cfbd431da..HEAD -- \
     compiler/rustc_mir_transform/src/check_alignment.rs \
     compiler/rustc_mir_transform/src/check_null.rs \
     compiler/rustc_mir_transform/src/check_enums.rs \
     compiler/rustc_mir_transform/src/check_pointers.rs \
     compiler/rustc_mir_transform/src/instsimplify.rs \
     library/core/src/ub_checks.rs
   ```
   Zero behavioral diff in `SimplifyUbCheck`, `PointerFinder::visit_place`, `insert_null_check`, `insert_alignment_check`, and `insert_niche_check` confirms all source-derived findings remain invariant.

3. **Re-verify the Lean 4 formalization and `env.constants.map₁` purity audit (takes ~4s):**
   ```bash
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1"
   LEAN_BIN="$LEAN_SYSROOT/bin/lean"
   "$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean
   mkdir -p /tmp/reval_lean_audit
   "$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -R support -o /tmp/reval_lean_audit/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.olean \
     support/MirUbChecksRuntimeChecksAndCheckEnumsSoundness.lean
   LEAN_PATH="/tmp/reval_lean_audit:$LEAN_SYSROOT/lib/lean" \
     "$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/audit_lean_purity.lean
   ```
   Confirm `AUDIT_ALL_AXIOMS_USED=#[propext]`, `AUDIT_UNSAFE_RECS=0`, `AUDIT_UNSAFE_DECLS=0`, and `AUDIT_FORBIDDEN_AXIOMS=0`.

4. **Check `joshlf/anneal` trusted boundary drift:**
   Diff `trusted/lean/Trusted/MirAst.lean` (`Operand`, `AssertKind`) and `trusted/lean/Trusted/MirSemantics.lean` (`evalTerminator` `.assert`) against `c131b320eeeb26ef692e5afd5ec8db49ee518613`. If `Operand` gains a `runtimeChecks` constructor or `evalTerminator` stops returning `.fault .unsupported` on `.assert`, re-audit Anneal's handling of crate-graph check flags and `UnwindAction::Unreachable`.
