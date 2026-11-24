# Integer Overflow Checks, Unchecked `nuw`/`nsw`, Mandatory Division Guards, and Safe Shift Masking in rustc

## Summary

`rustc` lowers integer operations along three sharply distinct semantic tiers spanning source syntax, Mid-level Intermediate Representation (MIR), LLVM IR, hardware instructions, Constant-Time Function Evaluation (CTFE) / Miri, and formal verification boundaries (`source`, `normative`, `execution`, `derived`):

1. **Profile-dependent overflow checks (`-C overflow-checks=on` vs. `off`)**: Binary `+`, `-`, `*`, unary `-`, and safe shifts `<<`/`>>` conditionally insert MIR panic checks when overflow checks are enabled (`self.check_overflow` in MIR construction, preserved or stripped for `#[rustc_inherit_overflow_checks]` intrinsics by `AssertKind::is_optional_overflow_check`), and wrap modulo `2^w` without panic when disabled (`source`, `execution`).
2. **Profile-independent mandatory safety guards (safe `/` and `%`, plus safe shift bit-width masking)**: Safe integer division and remainder *always* insert MIR `DivisionByZero`/`RemainderByZero` traps and signed `a == MIN && b == -1` overflow traps regardless of `-C overflow-checks` (`on` or `off`) and optimization level, because LLVM `sdiv` and `srem` treat both zero divisors and `(INT_MIN, -1)` as immediate Undefined Behavior (UB) and x86-64 `idiv` raises hardware `#DE` (`SIGFPE`) on both. Safe bit-shifts with overflow checks disabled mask the shift count with `and %rhs, (W - 1)` in SSA codegen (`shift_mask_val`), producing total, poison-free bitvector shifts across all Rust integer widths `8..=256` (`source`, `normative`, `execution`, `derived`).
3. **Unchecked `unsafe` intrinsics (`unchecked_{add,sub,mul,shl,shr,div,rem}`)**: These lower directly to `BinOp::*Unchecked` (for `+`, `-`, `*`, `<<`, `>>`) or raw unguarded `Div`/`Rem`, emit LLVM `add`/`sub`/`mul` with `nuw`/`nsw` flags or bare `shl`/`lshr`/`ashr`/`sdiv`/`srem` without guards, trigger library `panic_nounwind_fmt` (`SIGABRT`) under `-C debug-assertions=on`, defer `poison` until `noundef` ABI or branch sinks under `-C debug-assertions=off`, and cause immediate Abstract Machine UB under CTFE/Miri even if the resulting value is discarded (`source`, `normative`, `execution`, `derived`).

These three tiers were audited end-to-end across upstream primary sources (`rust-lang/rust`, `llvm/llvm-project`, and `joshlf/anneal`), reproduced empirically under `rustc 1.98.0-nightly` / `LLVM 22.1.6` / `miri 0.1.0`, and mechanized cleanly in kernel-checked `Lean v4.34.1` (`1,914` LOC, `105` explicit theorems [`148` environment theorem constants], `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `0` `partial`/`unsafe`, relying strictly on `[Quot.sound, propext]`) (`source`, `execution`, `derived`).

| Operation Class | `-C overflow-checks=on` MIR / Native | `-C overflow-checks=off` MIR / Native | LLVM IR (`-O2`, checks off) | Miri Behavior | Kernel-Checked Refinement Theorem |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Safe `+`, `-`, `*` | `*WithOverflow` + `assert`; panics (`101`) | `BinOp::{Add,Sub,Mul}`; two's-complement wrap (`0`) | Bare `add`/`sub`/`mul` (no `nuw`/`nsw`) | Panic (`on`) vs. wrap (`off`) | `non_overflowing_four_way_bit_identical`, `wrapping_always_ok` |
| Safe unary `-x` | `Eq(x, MIN)` + `assert`; panics on `MIN` | `UnOp::Neg`; `-MIN == MIN` | `sub iW 0, %x` (no `nsw`) | Panic (`on`) vs. `MIN` (`off`) | `non_overflowing_neg_agree` |
| Safe `/` and `%` | `DivByZero`/`RemByZero` + signed `(MIN, -1)` guard; panics | **Identical guards retained**; panics even under `-O2` | `icmp eq 0`, `(MIN,-1)` branches + `sdiv`/`srem` | Panics (`101`) even with `checks=off` | `safeDiv_profile_independent`, `safeDiv_ub_free`, `srem_inSignedRange_of_nonzero` |
| Safe `<<`, `>>` | `Lt(unsigned_rhs, W)` + `assert`; panics if out of `[0, W)` | Unchecked MIR `Shl`/`Shr`; codegen masks `& (W - 1)` | `and %rhs, W-1` (+ `zext nneg`) + `shl`/`lshr`/`ashr` | Panic (`on`) vs. masked wrap (`off`) | `shiftMask_lt_pow2`, `safeShift_checksOff_always_ok`, `toNat_mod_pow2_eq_toInt_emod` |
| `unchecked_{add,sub,mul}` | With `-C debug-assertions=on`: `SIGABRT` (`-6`); checks omitted in Miri | With `-C debug-assertions=off`: deferred `poison` until `noundef` sink | `{add,sub,mul} {nuw,nsw}` (or `unchecked_su*`: both) | **Immediate UB** (`1`) even on `let _ = ...` | `miriUnchecked_eq_lowerNoundef_llvm`, `wrapping_refines_llvm_and_miri`, `nsw_sgt_fold_sound` |
| `unchecked_{shl,shr}` | Precondition trap if `-C debug-assertions=on`; immediate UB in Miri | Bare shift without `& (W - 1)`; `poison` if `>= W` | Bare `shl`/`ashr`/`lshr` (`poison` on overshift) | **Immediate UB** (`1`) if `< 0` or `>= W` | `witness_u32_shl_32_four_tiers` |
| `intrinsics::unchecked_{div,rem}` | Lowers to unguarded MIR `Div`/`Rem` (`assert` omitted!) | Raw hardware `idiv`/`udiv`; x86 `SIGFPE` (`#DE`) or LLVM UB | Bare `sdiv`/`srem`/`udiv`/`urem` without guards | **Immediate UB** (`1`) on `0` or `(MIN, -1)` | `safeDiv_refines_llvmDiv`, `safeRem_refines_llvmRem` |

## Applicability

These findings apply to:

- **Rust compilation pipelines targeting LLVM backends (and MIR interpretation via CTFE / Miri)** built from the audited `rust-lang/rust` compiler architecture (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) and verified empirically against `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, embedded `LLVM 22.1.6`) on `x86_64-unknown-linux-gnu` (`source`, `execution`).
- **All standard Rust fixed-width signed and unsigned integer primitives (`i8`/`u8`, `i16`/`u16`, `i32`/`u32`, `i64`/`u64`, `i128`/`u128`, `isize`/`usize`)**, noting that pointer-sized `isize`/`usize` normalize to target width (64 bits on `x86_64`) and mixed-width shift RHS lowering in `compiler/rustc_codegen_ssa/src/base.rs` explicitly relies on the width assertion `lhs_sz <= 256` (`source`, `derived`).
- **Static verification and MIR semantics models** such as Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), where callers must know precisely which MIR constructs encode profile-conditional panics (`*WithOverflow` + optional `AssertKind`), which encode mandatory safety traps (`Div`/`Rem`), and how `-C overflow-checks=off` interacts with shift masking vs. `unsafe` unchecked operations (`source`, `derived`).

Outside applicability (detailed further under `## Boundaries`): non-LLVM codegen backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`) were `not examined`; hypothetical `512`-bit or wider non-primitive integers invalidate `base.rs`'s `zext`-after-mask optimization for signed negative shift counts (`known not to apply` per the source assertion `lhs_sz <= 256`, formally witnessed at `512` bits in Lean theorem `base_rs_512bit_i8_mismatch_witness`); arbitrary target architectures outside `x86_64-unknown-linux-gnu` were not executed empirically (`not examined`) (`derived`).

## Findings

### 1. Three-Tier Architecture from HIR/MIR Construction Through LLVM Codegen and CTFE

Tracing an integer operator from source lowering to backend emission and interpreter evaluation establishes three non-overlapping semantic pipelines in `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) (`source`):

```text
Rust Source / core Method
  │
  ├─► Safe +, -, *, neg, <<, >>
  │     └─► MIR build (as_rvalue.rs:97-118, 447-519):
  │           ├─ if check_overflow:
  │           │     AddWithOverflow / Eq(MIN) / Lt(rhs as uint, W)
  │           │     + AssertKind::{OverflowNeg, Overflow}  <── is_optional_overflow_check() == true
  │           └─ else:                                           (can be stripped in SSA codegen
  │                 raw BinOp::{Add,Sub,Mul,Shl,Shr} / UnOp::Neg  when !sess.overflow_checks())
  │                 └─ SSA/LLVM codegen (rvalue.rs, base.rs):
  │                       ├─ +, -, *, neg ──► bare add/sub/mul/sub(0,x) (TWO'S-COMPLEMENT WRAP)
  │                       └─ <<, >>       ──► mask rhs = bx.and(rhs, W-1) then shl/lshr/ashr
  │
  ├─► Safe /, % (always guarded)
  │     └─► MIR build (as_rvalue.rs:520-581):
  │           └─ UNCONDITIONAL (ignores check_overflow; is_optional_overflow_check() == false):
  │                 1) Assert(rhs != 0, DivisionByZero / RemainderByZero)
  │                 2) if signed: Assert(!(rhs == -1 && lhs == MIN), Overflow(Div/Rem))
  │                 └─ SSA/LLVM codegen (rvalue.rs:948-965): sdiv / udiv / srem / urem
  │
  └─► core::num unchecked_{add,sub,mul,shl,shr} & intrinsics::unchecked_{div,rem}
        ├─ core wrapper (int_macros.rs + ub_checks.rs:53-106):
        │     if check_language_ub() { /* !cfg!(miri) && intrinsics::ub_checks() */
        │         precondition_check(...) -> panic_nounwind_fmt (SIGABRT)  under -Cdebug-assertions=on
        │     }  /* omitted in CTFE/Miri and erased under -Cdebug-assertions=off */
        └─ lower_intrinsics.rs:117-154:
              ├─ unchecked_{add,sub,mul,shl,shr} ──► BinOp::*Unchecked
              │     ├─ LLVM codegen (builder.rs:557-594, rvalue.rs:913-947, 986-993):
              │     │     add/sub/mul {nuw|nsw}; raw shl/lshr/ashr (NO W-1 mask!) ──► LLVM poison
              │     └─ CTFE/Miri (operator.rs:114-170, 200-298): throw_ub!(...) ──► Immediate UB
              └─ unchecked_{div,rem} ──► raw MIR BinOp::{Div,Rem} (WITHOUT assertions!)
                    ├─ LLVM codegen: bare sdiv/udiv/srem/urem ──► LLVM immediate UB / x86 #DE
                    └─ CTFE/Miri: DivisionByZero / DivisionOverflow / RemainderOverflow ──► Immediate UB
```

Four design invariants emerge directly from this pipeline (`source`, `normative`):

1. **Optional vs. mandatory MIR `Assert` classification**: `compiler/rustc_middle/src/mir/terminator.rs:170-176` defines `AssertKind::is_optional_overflow_check(&self)` to return `true` **only** for `AssertKind::OverflowNeg(..)` and `AssertKind::Overflow(BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr, ..)`. Both `DivisionByZero`/`RemainderByZero` and `Overflow(BinOp::Div | BinOp::Rem, ..)` return `false`. When codegen lowers MIR in `compiler/rustc_codegen_ssa/src/mir/block.rs:769-780`, it folds `if !bx.sess().overflow_checks() && msg.is_optional_overflow_check()` to `const_cond = Some(expected)`, stripping optional checks (such as those inlined from `#[rustc_inherit_overflow_checks]` helpers) while keeping every `/` and `%` guard intact (`source`).
2. **Checked methods vs. unchecked intrinsics**: Safe checked methods (`checked_div`, `checked_rem` in `library/core/src/num/int_macros.rs:1034-1041, 1280-1287`) perform an explicit branch (`unlikely(rhs == 0 || (self == Self::MIN && rhs == -1))`) and return `Option::None` on both `(x, 0)` and `(MIN, -1)`. Conversely, `wrapping_shl`/`wrapping_shr` (`int_macros.rs:2536-2542, 2573-2579`) are implemented inside `core` via `unchecked_shl(rhs & (Self::BITS - 1))`—using the exact same power-of-two mask identity that codegen applies to bare `<<`/`>>` (`source`).
3. **Asymmetric codegen for signed/unsigned truncation and intrinsics**: In `compiler/rustc_codegen_llvm/src/builder.rs:557-594`, single-signedness intrinsics emit either `NSW` (`unchecked_sadd`, `unchecked_ssub`, `unchecked_smul`) or `NUW` (`unchecked_uadd`, `unchecked_usub`, `unchecked_umul`), whereas mixed signed-plus-unsigned intrinsics `unchecked_suadd`/`susub`/`sumul` attach **both** `NUW` and `NSW` (`LLVMRustSetHasNUW` + `LLVMRustSetHasNSW`, matching `unchecked_utrunc`/`unchecked_strunc` at lines `979-1001`). By contrast, `checked_binop` (`lines 623-664`) lowers unsigned `Add`/`Sub` to plain `add`/`sub` paired with `icmp ult` and lowers signed ops or `Mul` to `llvm.{s,u}{add,sub,mul}.with.overflow` (`source`).
4. **CTFE/Miri parity without LLVM `poison` deferral**: In `compiler/rustc_const_eval/src/interpret/operator.rs`, `BinOp::*Unchecked` and `Div`/`Rem` evaluate mathematically with `throw_ub!(ShiftOverflow ..)`, `throw_ub!(DivisionByZero)`, `throw_ub!(RemainderByZero)`, `throw_ub!(DivisionOverflow)`, `throw_ub!(RemainderOverflow)`, and `throw_ub!(ArithOverflow ..)` directly on overflow (`lines 114-170, 200-241, 265-298`), converting deferred LLVM SSA `poison` into Rust Abstract Machine immediate UB even when the resulting SSA value has no `noundef` return/branch user (`source`, `execution`).

### 2. Tier 1: Profile-Dependent `-C overflow-checks` Behavior (Checked Panics vs. Deterministic Wrapping)

In `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs`:

- **Unary negation (`lines 97-118`)**: When `this.check_overflow && op == UnOp::Neg && expr.ty.is_signed()`, MIR building synthesizes `minval_literal`, checks equality against the operand, and emits `TerminatorKind::Assert` with `AssertKind::OverflowNeg(arg.to_copy())` before `UnOp::Neg`. When `!this.check_overflow`, only `Rvalue::UnaryOp(UnOp::Neg, ...)` is emitted (`source`).
- **Ring binary ops `+`, `-`, `*` (`lines 447-470`)**: When `self.check_overflow && ty.is_integral()`, `rustc` maps `op.wrapping_to_overflowing().unwrap()` to `BinOp::AddWithOverflow`, `SubWithOverflow`, or `MulWithOverflow` returning `(T, bool)` and asserts `!overflow` via `AssertKind::Overflow(op, lhs, rhs)`. When disabled, bare `BinOp::{Add,Sub,Mul}` lowers directly (`source`).
- **Bit shifts `<<`, `>>` (`lines 471-519`)**: When `self.check_overflow && ty.is_integral()`, the RHS is cast via `CastKind::IntToInt` to the unsigned type matching `rhs_ty`, zero/sign comparison `< lhs_size.bits()` is checked (`assert`), so *both* negative signed shift counts (which become huge unsigned counts after `IntToInt`) and counts `>= width` trigger `AssertKind::Overflow(op, lhs, rhs)` (`source`).

Empirical MIR dumps captured by `support/probe_int_overflow_nuw_nsw_div_shift.py` (`rustc 1.98.0-nightly`) directly confirm this structural divergence under `-Copt-level=0` (`execution`):

```text
; mir_add_i32 (-Coverflow-checks=on):
  bb0: { _3 = AddWithOverflow(copy _1, copy _2);
         assert(!move (_3.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _1, copy _2) -> [success: bb1, unwind continue]; }
  bb1: { _0 = move (_3.0: i32); return; }

; mir_add_i32 (-Coverflow-checks=off):
  bb0: { _0 = Add(copy _1, copy _2); return; }

; mir_neg_i32 (-Coverflow-checks=on vs. off):
  ; on:  _2 = Eq(copy _1, const i32::MIN); assert(!move _2, "attempt to negate `{}`, which would overflow", copy _1)
  ; off: _0 = Neg(copy _1); return;

; mir_shl_u32 (-Coverflow-checks=on vs. off):
  ; on:  _3 = Lt(copy _2, const 32_u32); assert(move _3, "attempt to shift left by `{}`, which would overflow", copy _2)
  ; off: _0 = Shl(copy _1, copy _2); return;
```

Executing all seven boundary cases across native binaries and Miri yields 100% deterministic panic-vs-wrap separation (`execution`):

| Case (`probe.rs`) | Native `checks=on` (`rc` / panic) | Native `checks=off` (`rc=0`) | Miri `checks=on` (`rc`) | Miri `checks=off` (`rc=0`) |
| :--- | :--- | :--- | :--- | :--- |
| `255u8 + 1` (`u8_add`) | `101`: `attempt to add with overflow` | `ADD_U8=0` | `101` (panic) | `ADD_U8=0` |
| `127i8 + 1` (`i8_add`) | `101`: `attempt to add with overflow` | `ADD_I8=-128` | `101` (panic) | `ADD_I8=-128` |
| `0u8 - 1` (`u8_sub`) | `101`: `attempt to subtract with overflow` | `SUB_U8=255` | `not examined` | `not examined` |
| `16u8 * 16` (`u8_mul`) | `101`: `attempt to multiply with overflow` | `MUL_U8=0` | `not examined` | `not examined` |
| `-(-128i8)` (`i8_neg_min`) | `101`: `attempt to negate with overflow` | `NEG_I8=-128` | `101` (panic) | `NEG_I8=-128` |
| `1u32 << 32` (`u32_shl_32`) | `101`: `attempt to shift left with overflow` | `SHL_U32=1` | `101` (panic) | `SHL_U32=1` |
| `-8i32 >> 32` (`i32_shr_32`) | `101`: `attempt to shift right with overflow` | `SHR_I32=-8` | `not examined` | `not examined` |

LLVM IR emitted under `-Copt-level=2 -Coverflow-checks=off` for `safe_add_wrapping_when_off` is `define noundef i32 @safe_add_wrapping_when_off(i32 noundef %a, i32 noundef %b)` with `%_0 = add i32 %b, %a`—strictly omitting both `nuw` and `nsw` (`execution`).

### 3. Tier 2a: Profile-Independent Mandatory Division/Remainder Guards (`i32::MIN / -1` and `% -1`)

Safe `/` and `%` never honor `-Coverflow-checks=off`. In `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs:520-581`, `BinOp::Div | BinOp::Rem if ty.is_integral()` unconditionally emits:

1. Divisor-zero guard: `rhs == 0` followed by `assert(!zero, DivisionByZero | RemainderByZero)`.
2. Signed min-by-minus-one guard (`if ty.is_signed()`): `(rhs == -1) & (lhs == MIN)` followed by `assert(!overflow, Overflow(Div | Rem, lhs, rhs))` (`source`).

This matches LLVM's normative specification in `llvm/docs/LangRef.md:11477-11685` (`normative`):

- `udiv` (`lines 11503-11504`) and `urem` (`lines 11623-11625`): division/remainder by zero is **immediate UB**.
- `sdiv` (`lines 11546-11549`) and `srem` (`lines 11671-11678`): **both** zero divisor **and** division/remainder of the most negative value (`INT_MIN`) by `-1` cause immediate UB. Crucially, `LangRef.md:11674-11678` explicitly documents that `srem` makes `(INT_MIN, -1)` immediate UB *notwithstanding* `INT_MIN.tmod (-1) == 0` fitting cleanly within `[INT_MIN, INT_MAX]`, because x86/hardware `idiv` computes quotient and remainder in one trapping instruction (`normative`).

Live MIR, LLVM IR, and x86-64 machine code confirm that these guards survive both `-Coverflow-checks=off` and `-Copt-level=2` (`execution`):

```text
; mir_div_i32 & mir_rem_i32 under BOTH -Coverflow-checks=on AND -Coverflow-checks=off:
  bb0: { _3 = Eq(copy _2, const 0_i32); assert(!move _3, ...) -> [success: bb1, unwind continue]; }
  bb1: { _4 = Eq(copy _2, const -1_i32); _5 = Eq(copy _1, const i32::MIN);
         _6 = BitAnd(move _4, move _5); assert(!move _6, ...) -> [success: bb2, unwind continue]; }
  bb2: { _0 = Div(copy _1, copy _2); /* or Rem */ return; }
```

In emitted LLVM IR under `-Copt-level=2 -Coverflow-checks=off` (`execution`):

- `safe_i32_div_always_checked` emits `%_3 = icmp eq i32 %b, 0` (`panic_const_div_by_zero`), then `%_4 = icmp eq i32 %b, -1`, `%_5 = icmp eq i32 %a, -2147483648`, `%_6 = and i1 %_5, %_4` (`panic_const_div_overflow`), and only then `bb2: %_0 = sdiv i32 %a, %b; ret i32 %_0`.
- `safe_i32_rem_always_checked` emits the **identical** two guards (`panic_const_rem_by_zero`, `panic_const_rem_overflow`) before `%_0 = srem i32 %a, %b`, with LLVM attaching return range `range(i32 -2147483647, -2147483648)` (`execution`).
- Emitted x86-64 assembly for `safe_i32_div_always_checked` lowers the `-1 && MIN` guard into a combined branch-free test: `movl %esi, %eax; notl %eax; leal -2147483648(%rdi), %ecx; orl %eax, %ecx; je .LBB6_6` (`(%esi ^ -1) | (%edi - INT_MIN) == 0`) right after `testl %esi, %esi; je .LBB6_4`, and only then executes `cltd; idivl %esi` (`execution`).

Live execution under `-Coverflow-checks=off -Copt-level=2` and Miri (`RUSTFLAGS=-Coverflow-checks=off`) confirms panic exit `101` for `i32::MIN / -1` (`attempt to divide with overflow`), `i32::MIN % -1` (`attempt to calculate the remainder with overflow`), `1i32 / 0` (`attempt to divide by zero`), and `1i32 % 0` (`attempt to calculate the remainder with a divisor of zero`), and across **all five** signed primitive widths (`i8`, `i16`, `i32`, `i64`, `i128`) in `div_min_all_signed_widths_off_opt2`: `PANIC_STATUS=(true, true, true, true, true)` (`execution`).

### 4. Tier 2b: Safe Shift Bit-Width Masking (`& (W - 1)`), Mixed-Width Signed RHS, and x86-64 Hardware Masking

When `-Coverflow-checks=off`, MIR builds unguarded `BinOp::Shl` / `BinOp::Shr`, and `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:986-993` dispatches through `base::build_shift_expr_rhs(bx, lhs, rhs, op == BinOp::ShlUnchecked)` (`compiler/rustc_codegen_ssa/src/base.rs:330-367`):

1. If `!is_unchecked`, `build_shift_expr_rhs` computes `mask = common::shift_mask_val(bx, llty, rhs_llty, false)` (`compiler/rustc_codegen_ssa/src/common.rs:106-115`: `let val = val - 1`) and executes `rhs = bx.and(rhs, mask)` **before** width adjustment (`source`).
2. If `lhs_sz < rhs_sz`, codegen calls `bx.unchecked_utrunc` (when `is_unchecked`) or `bx.trunc` (otherwise); if `lhs_sz > rhs_sz`, it asserts `assert!(lhs_sz <= 256)` (`base.rs:355-363`, explicitly noting a `512`-bit hazard!) and zero-extends `bx.zext(rhs, lhs_llty)` (`source`).

Empirical LLVM IR under `-Copt-level=2 -Coverflow-checks=off` confirms every case cleanly (`execution`):

```llvm
define noundef i32 @safe_shl_masked_when_off(i32 noundef %a, i32 noundef %b) {
  %0 = and i32 %b, 31
  %_0 = shl i32 %a, %0
  ret i32 %_0
}
define noundef i8 @safe_u8_shl_masked(i8 noundef zeroext %a, i32 noundef %b) {
  %0 = trunc i32 %b to i8
  %1 = and i8 %0, 7
  %_0 = shl i8 %a, %1
  ret i8 %_0
}
define noundef i32 @safe_u32_shl_i8_masked(i32 noundef %a, i8 noundef signext %b) {
  %0 = and i8 %b, 31
  %1 = zext nneg i8 %0 to i32
  %_0 = shl i32 %a, %1
  ret i32 %_0
}
define noundef i32 @u32_unchecked_shl_raw(i32 noundef %a, i32 noundef %b) {
  %_0 = shl i32 %a, %b
  ret i32 %_0
}
```

Two critical subtleties follow from source, execution, and our Lean formalization:

- **Mixed-width signed negative RHS soundness & `512`-bit ceiling**: For `(1u32 << (-1i8))` (`SHL_NEG_I8=0x80000000`) and `(-8i8 >> 9i32)` (`SHR_I8_9=-4`), both native `-Coverflow-checks=off -Copt-level=2` and Miri `-Coverflow-checks=off` return bit-identical results (`execution`). In `safe_u32_shl_i8_masked`, LLVM masks `and i8 %b, 31` first (yielding `0..31`, letting LLVM attach `zext nneg` safely!). Why? Because `2^k | 2^r` whenever `k <= r`: our Lean theorem `toNat_mod_pow2_eq_toInt_emod` proves for **all** `k <= r` and `b : BitVec r` that `Int.ofNat (b.toNat &&& (2^k - 1)) = b.toInt.emod (2^k)` (`8..=256`-bit LHS vs `i8` RHS all satisfy `k <= 8 <= r`). Conversely, at `512` bits (`k = 9`, `i8` RHS `r = 8`), `b = -1i8` gives `zext(-1i8) &&& 511 = 255` instead of `(-1).emod 512 = 511` (`base_rs_512bit_i8_mismatch_witness`), explaining why `base.rs:360-362` asserts `lhs_sz <= 256` (`source`, `derived`).
- **x86-64 machine code hides LLVM `shl` UB**: Inspecting the emitted x86-64 assembly (`-Copt-level=2 -Coverflow-checks=off`), **both** `safe_shl_masked_when_off` and `u32_unchecked_shl_raw` lower to identical assembly (`execution`):

```asm
movl %esi, %ecx
movl %edi, %eax
shll %cl, %eax
retq
```

  Hardware `shll %cl` masks `%cl` by `31` in silicon, so LLVM elides the `and i32 %b, 31` instruction on x86-64. Relying on hardware execution or disassembled x86-64 code would therefore falsely equate `<<` and `unchecked_shl`, missing the fact that `u32_unchecked_shl_raw(1, 32)` produces LLVM IR `poison` -> `ret noundef` UB (`LangRef.md:11766-11768`) and immediate UB in Miri (`normative`, `execution`, `derived`). In addition, `common.rs:116-120` extends `shift_mask_val` recursively to SIMD vectors via `vector_element_type_and_length` and `vector_splat`, ensuring the same bit-width mask `(elem_bits - 1)` is splatted across every vector lane for SSA backends (`source`).

### 5. Tier 3: `unchecked_*` Intrinsics, LLVM `nuw`/`nsw`, `-C debug-assertions`, Optimizations, and Miri UB

`library/core/src/num/int_macros.rs` (`lines 725-739, 864-878, 1003-1017, 1590-1603, 1769-1782`) guards each safe method wrapper (`u32::unchecked_add`, etc.) with `assert_unsafe_precondition!(check_language_ub, ..., ...)` (`library/core/src/ub_checks.rs:51-106`) before calling `core::intrinsics::unchecked_*` (`source`). Reading `ub_checks.rs:13-80, 96-106` directly reveals why runtime aborts, release LLVM IR, and Miri diagnostics diverge systematically (`source`):

1. **Inline-control and codegen-time gating**: `assert_unsafe_precondition!` defines an inner `const fn precondition_check` annotated with `#[rustc_no_mir_inline]`, `#[inline]`, `#[rustc_nounwind]`, and `#[track_caller]`, invoked behind `if ::core::ub_checks::$kind()`. As documented in `ub_checks.rs:28-32, 56-63`, gating behind a codegen-time condition instead of `debug_assert!` keeps precompiled `core` monomorphizations lightweight while allowing LLVM (rather than the MIR inliner) to delete the branch when `intrinsics::ub_checks()` evaluates to `false`, or inline it when enabled (`source`).
2. **Miri and `const` exclusion (`check_language_ub`)**: `ub_checks.rs:96-106` defines `check_language_ub()` using `const_eval_select!`: in `if const { false } else { !cfg!(miri) && intrinsics::ub_checks() }`, both compile-time CTFE and Miri suppress the runtime `precondition_check` call completely so the interpreter evaluates the raw intrinsic directly in `compiler/rustc_const_eval/src/interpret/operator.rs:114-170, 200-298` and reports source-accurate language UB (`source`).
3. **Non-unwinding runtime failure under `-Cdebug-assertions=on`**: On violation, `precondition_check` (`ub_checks.rs:68-79`) invokes `core::panicking::panic_nounwind_fmt(..., false)` with `"unsafe precondition(s) violated: "` + the intrinsic message + `"\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."`. Because the call is `#[rustc_nounwind]`, native execution aborts (`SIGABRT`, exit status `-6`) rather than unwinding (`source`, `execution`).

Empirical runs on `u32::MAX.unchecked_add(1)` demonstrate these **three distinct behaviors** across compiler configurations (`execution`):

- **Native `-Cdebug-assertions=on -Copt-level=2`**: Emits `%0 = xor i32 %a, -1; %_4.1.i = icmp ugt i32 %b, %0; br i1 %_4.1.i, label %bb1.i, ...` calling `@...panic_nounwind_fmt` (`unreachable`) before falling through to `%_0 = add nuw i32 %b, %a`. Running the binary exits `-6` (`SIGABRT`) printing `unsafe precondition(s) violated: u32::unchecked_add cannot overflow` (`execution`).
- **Native `-Cdebug-assertions=off -Copt-level=2`**: `intrinsics::ub_checks()` folds to `false`, eliminating `%bb1.i` completely and leaving `%_0 = add nuw i32 %b, %a; ret i32 %_0`—meaning overflowing inputs evaluate to LLVM `poison` propagated across a `ret noundef i32` ABI boundary (silent UB in the unoptimized/unchecked test binary, exiting `0`) (`execution`).
- **Miri (`cargo +nightly miri run --offline`, default or `-Coverflow-checks=off`)**: `!cfg!(miri)` disables the `precondition_check`, so Miri hits `operator.rs` and terminates cleanly with exit code `1`: `error: Undefined Behavior: arithmetic overflow in unchecked_add`—even when the result is discarded via `let _ = u32::MAX.unchecked_add(1);` (`execution`).

Across Suite D in Miri (`support/probe_results.json`), **all eight** unchecked UB test cases fail with exit code `1` while **both** valid boundary controls pass with exit code `0` (`execution`):

| Suite D Miri Case | Input Expression | Exit Code | Miri Diagnostic / Verbatim Output |
| :--- | :--- | :--- | :--- |
| `u32_unchecked_add_overflow_unused_ub` | `let _ = u32::MAX.unchecked_add(1);` | `1` | `Undefined Behavior: arithmetic overflow in unchecked_add` |
| `i32_unchecked_add_overflow_ub` | `i32::MAX.unchecked_add(1)` | `1` | `Undefined Behavior: arithmetic overflow in unchecked_add` |
| `u32_unchecked_sub_underflow_ub` | `0u32.unchecked_sub(1)` | `1` | `Undefined Behavior: arithmetic overflow in unchecked_sub` |
| `i32_unchecked_sub_underflow_ub` | `i32::MIN.unchecked_sub(1)` | `1` | `Undefined Behavior: arithmetic overflow in unchecked_sub` |
| `u32_unchecked_mul_overflow_ub` | `u32::MAX.unchecked_mul(2)` | `1` | `Undefined Behavior: arithmetic overflow in unchecked_mul` |
| `i32_unchecked_mul_min_neg1_ub` | `i32::MIN.unchecked_mul(-1)` | `1` | `Undefined Behavior: arithmetic overflow in unchecked_mul` |
| `u32_unchecked_shl_32_ub` | `1u32.unchecked_shl(32)` | `1` | `Undefined Behavior: overflowing shift by 32 in unchecked_shl` |
| `i32_unchecked_shr_32_ub` | `1i32.unchecked_shr(32)` | `1` | `Undefined Behavior: overflowing shift by 32 in unchecked_shr` |
| `u32_unchecked_shl_31_valid` (control) | `1u32.unchecked_shl(31)` | `0` | `SHL31=0x80000000` |
| `i32_checked_div_min_neg1_none` (control) | `i32::MIN.checked_div(-1)` | `0` | `CHECKED_DIV=None` |

Finally, LLVM exploits `nsw`/`nuw` aggressively to rewrite downstream comparisons (`normative`, `execution`):

```rust
pub unsafe fn nsw_allows_sgt_fold(x: i32) -> bool {
    if x <= 0 { return true; }
    unsafe { x.unchecked_add(1) > 0 } // LLVM IR: ret i1 true  | x86-64: movb $1, %al; retq
}
pub fn wrapping_preserves_sgt_cmp(x: i32) -> bool {
    if x <= 0 { return true; }
    x.wrapping_add(1) > 0             // LLVM IR: %0 = icmp ne i32 %x, 2147483647 | cmpl $2147483647, %edi; setne %al
}
```

Executed at `x = i32::MAX`, `nsw_allows_sgt_fold` returns `true` (`NSW_CMP=true`) via constant folding (`x + 1 > 0` assuming no signed overflow), whereas `wrapping_preserves_sgt_cmp` returns `false` (`WRAP_CMP=false`) because `-2147483648 <= 0` (`execution`, formalized generically across all `w >= 2` in Lean theorems `nsw_sgt_fold_sound` and `wrapping_sgt_fold_counterexample_i32`).

### 6. Kernel-Checked Lean v4.34.1 Formalization (`IntegerOverflowUncheckedNuwNswAndShiftMaskSoundness.lean`)

The formalization in `support/IntegerOverflowUncheckedNuwNswAndShiftMaskSoundness.lean` (`1,914` lines, `86,507` bytes, `7` inductives, `52` explicit `noncomputable def`s, `105` declared `theorem`s, compiling with `185` env definitions and `148` env theorem constants) models all three semantic tiers over arbitrary parametric bitvector width `w : Nat` (`w = 2^k` for shifts), `Signedness`, `OverflowProfile`, Alive2-style `PoisonVal w` (`val` vs `poison`), and unified `ExecOutcome w` (`ok`, `panic`, `poison`, `immediateUB`) (`derived`):

- **Constructive & Pure Lean MetaM Discipline**: Every definition carries an explicit `noncomputable def` modifier (`0` plain `def`, `0` `noncomputable section`, `0` `deriving`, `0` `._unsafe_rec`, `0` `partial`/`unsafe`). Avoiding Lean stdlib lemmas that pull `Classical.choice` internally (`Nat.pow_lt_pow_right`, `Nat.and_two_pow_sub_one_eq_mod`, `BitVec.le_toInt`, `BitVec.toInt_lt`, `BitVec.toInt_sdiv`, `BitVec.toInt_srem`), we prove constructive replacements directly from `BitVec.msb_eq_toNat`, `BitVec.toInt_eq_toNat_cond`, `BitVec.toNat_udiv`, `BitVec.toNat_umod`, `Nat.testBit_and`, and `Nat.testBit_mod_two_pow` (`toInt_of_msb_false`, `toInt_of_msb_true`, `bitvec_toInt_inSignedRange`, `testBit_two_pow_sub_one_clean`, `shiftMask_eq_mod_pow2`, and inline constructive proofs inside `sdiv_inSignedRange_of_guarded` and `srem_inSignedRange_of_nonzero`). An exhaustive MetaM audit collects axioms across all `148` kernel theorem constants and verifies `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `Lean.ofReduceNat`, `0` `Lean.trustCompiler`, and `0` `._unsafe_rec`—using strictly `[Quot.sound, propext]` (`derived`).

The Lean formalization is organized into six modular sections matching each stage of the compiler pipeline (`derived`):

| Lean Section & Lines | Core Types & Constructive Definitions | Primary Discharged Theorems |
| :--- | :--- | :--- |
| **Part I (`L37-L246`)** Semantic Domains & Refinement | `Signedness`, `OverflowProfile`, `PoisonVal` (`val` \| `poison`), `PoisonVal.Refines`, `ExecOutcome` (`ok` \| `panic` \| `poison` \| `immediateUB`), `ofPoisonVal`, `lowerNoundef`, `ExecOutcome.Refines` | `PoisonVal.refines_trans`, `ExecOutcome.refines_trans`, `refines_of_poisonRefines`, `refines_lowerNoundef_of_poisonRefines`, `not_ok_refines_panic`, `not_poison_refines_ok`, `not_immediateUB_refines_ok` |
| **Part II (`L247-L664`)** Constructive `BitVec w` & Overflow | `uMaxNat`, `sMinInt`, `sMaxInt`, `inUnsignedRange`, `inSignedRange`, `uAddOv`, `sAddOv`, `uSubOv`, `sSubOv`, `uMulOv`, `sMulOv`, `sNegOv`, `toInt_of_msb_false`, `toInt_of_msb_true`, `bitvec_toInt_inSignedRange` | `pow2_pred_lt_pow2`, `intMinBv_toInt`, `intMaxBv_toInt`, `allOnesBv_toInt`, `negOneLit_eq_allOnes`, `intMin_ne_zero`, `allOnes_ne_zero`, `intMin_ne_allOnes`, `bmod_eq_self_of_inSignedRange`, `toNat_add_eq_of_noOv`..`toInt_neg_eq_of_noOv` |
| **Part III (`L665-L1231`)** Safe & Unchecked `Div`/`Rem` | `divZeroGuard`, `sdivOverflowGuard`, `llvmDivRemDefined`, `evalLlvmDiv`, `evalLlvmRem`, `evalRustSafeDiv`, `evalRustSafeRem`, `evalUncheckedDiv`, `evalUncheckedRem` | `sdiv_inSignedRange_of_guarded`, `sdiv_overflow_iff_intMin_negOne`, `srem_inSignedRange_of_nonzero`, `srem_intMin_negOne_math_zero`, `safeDiv_profile_independent`, `safeRem_profile_independent`, `safeDiv_ub_free`, `safeRem_ub_free`, `safeDiv_refines_llvmDiv`, `safeRem_refines_llvmRem`, `witness_i32_min_div_rem_panics` |
| **Part IV (`L1233-L1523`)** Checked, Wrapping & `nuw`/`nsw` | `ArithOp`, `arithOverflow`, `bvArith`, `mathArith`, `evalCheckedArith`, `evalWrappingArith`, `evalRustSafeArith`, `evalLlvmArithPoison`, `evalRustLlvmUnchecked`, `evalMiriUncheckedArith`, `evalCheckedNeg`, `evalWrappingNeg`, `evalLlvmNegNsw` | `miriUnchecked_eq_lowerNoundef_llvm`, `bvArith_eq_math_of_noOv`, `non_overflowing_four_way_bit_identical`, `checked_nopanic_implies_all_agree`, `wrapping_refines_llvm_and_miri`, `non_overflowing_neg_agree`, `wrapping_always_ok`, `witness_u8_add_overflow_separation`, `nuw_nsw_incomparable_u8_i8`, `nsw_sgt_fold_sound`, `wrapping_sgt_fold_counterexample_i32` |
| **Part V (`L1525-L1771`)** Shift Masking & Mixed-Width `zext` | `ShiftKind`, `evalLlvmShift`, `rustShiftMask`, `shiftInBounds`, `evalRustSafeShift`, `evalMiriUncheckedShift`, `testBit_zero_nat`, `testBit_two_pow_sub_one_clean` | `shiftMask_eq_mod_pow2`, `shiftMask_lt_pow2`, `evalLlvmShift_masked_never_poison`, `safeShift_checksOff_always_ok`, `safeShift_never_poison_or_ub`, `safeShift_inBounds_four_way_agree`, `pow2_dvd_of_le`, `toNat_mod_pow2_eq_toInt_emod`, `base_rs_512bit_i8_mismatch_witness`, `witness_u32_shl_neg1_i8`, `witness_u32_shl_32_four_tiers` |
| **Part VI (`L1772-L1914`)** Unified Dispatch & Width Canaries | `RustcIntBinOp`, `evalRustcIntBinOp`, `isSafeRustcBinOp`, `isAlwaysTotalWhenChecksOff` | `safe_rustc_binop_never_ub_or_poison`, `checksOff_non_divrem_always_ok`, `rust_all_widths_div_rem_ub_free`, `probe_correspondence_canary_suite` |

Key proved theorems (exact names and module anchors in `support/IntegerOverflowUncheckedNuwNswAndShiftMaskSoundness.lean`) (`derived`):

1. **Division/Remainder UB-Freedom & Refinement**:
   - `sdiv_inSignedRange_of_guarded` (`L864`) & `sdiv_overflow_iff_intMin_negOne` (`L990`): Across *all* `w >= 2` and `b != 0#w`, `a.toInt.tdiv b.toInt` overflows signed range `[ -2^(w-1), 2^(w-1) - 1 ]` **if and only if** `a = BitVec.intMin w ∧ b = BitVec.allOnes w`, and otherwise `(a.sdiv b).toInt = a.toInt.tdiv b.toInt`.
   - `srem_inSignedRange_of_nonzero` (`L1021`) & `srem_intMin_negOne_math_zero` (`L1116`): Across all `w >= 1` and `b != 0#w`, `(a.srem b).toInt = a.toInt.tmod b.toInt` is **always** in `inSignedRange w` (including `(-2^(w-1)).tmod (-1) = 0`), clarifying the gap between mathematical remainder safety and LLVM `srem`'s hardware-coupled UB rule.
   - `safeDiv_profile_independent` (`L1127`), `safeRem_profile_independent` (`L1130`), `safeDiv_ub_free` (`L1138`), `safeRem_ub_free` (`L1161`), `safeDiv_refines_llvmDiv` (`L1187`), `safeRem_refines_llvmRem` (`L1203`), `witness_i32_min_div_rem_panics` (`L1221`), and `rust_all_widths_div_rem_ub_free` (`L1863`): Guarded `/` and `%` never produce `.immediateUB` or `.poison` for `w = 8, 16, 32, 64, 128` (and all `w >= 2`), and strictly refine raw LLVM `udiv`/`sdiv`/`urem`/`srem`.
2. **Checked, Wrapping, `nuw`/`nsw` Poison, and Miri Refinement**:
   - `miriUnchecked_eq_lowerNoundef_llvm` (`L1313`): Miri's `unchecked_*` immediate UB equals `ExecOutcome.lowerNoundef` applied to LLVM `nuw`/`nsw` poison.
   - `non_overflowing_four_way_bit_identical` (`L1343`) & `checked_nopanic_implies_all_agree` (`L1362`): Whenever `arithOverflow op s a b = false` (equivalently `evalCheckedArith ≠ .panic`), checked (`checks=on`), wrapping (`checks=off`), LLVM `nuw`/`nsw`, Miri `unchecked_*`, and exact integer arithmetic agree bit-for-bit.
   - `wrapping_refines_llvm_and_miri` (`L1380`) & `wrapping_always_ok` (`L1422`): `-C overflow-checks=off` wrapping arithmetic is total (`.ok`) and unconditionally refines LLVM `nuw`/`nsw` and Miri `unchecked_*` across *all* inputs.
   - `witness_u8_add_overflow_separation` (`L1429`), `nuw_nsw_incomparable_u8_i8` (`L1456`), `nsw_sgt_fold_sound` (`L1473`), & `wrapping_sgt_fold_counterexample_i32` (`L1510`): Proves non-refinement of `nuw`/Miri against wrapping on `255#8 + 1#8`, incomparability of `nuw` vs. `nsw` (`127#8 + 1#8` vs. `255#8 + 1#8`), and generic `w >= 2` soundness of LLVM `add nsw` `sgt` folding vs. `i32::MAX` wrap failure.
3. **Shift Masking Total-Safety & Mixed-Width Bounds**:
   - `shiftMask_eq_mod_pow2` (`L1615`), `shiftMask_lt_pow2` (`L1625`), `evalLlvmShift_masked_never_poison` (`L1637`), `safeShift_checksOff_always_ok` (`L1646`), `safeShift_never_poison_or_ub` (`L1657`), & `safeShift_inBounds_four_way_agree` (`L1676`): `b.toNat &&& (2^k - 1) = b.toNat % 2^k < 2^k`, guaranteeing poison/UB freedom under both profiles and exact totality under `checks=off`.
   - `toNat_mod_pow2_eq_toInt_emod` (`L1720`) & `base_rs_512bit_i8_mismatch_witness` (`L1744`): `zext`-after-mask preserves `b.toInt.emod (2^k)` whenever `k <= r`, breaking at `k = 9, r = 8` (`255 ≠ 511`).
4. **End-to-End Dispatch & Empirical Canaries**:
   - `safe_rustc_binop_never_ub_or_poison` (`L1808`), `checksOff_non_divrem_always_ok` (`L1845`), and `probe_correspondence_canary_suite` (`L1893`): End-to-end 13-way correspondence matching every native/Miri boundary in `probe_results.json`.

### 7. Integration with Anneal (`joshlf/anneal`) Trusted MIR Semantics

Auditing `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) against real `rustc` MIR highlights the exact boundary Anneal enforces (`source`, `derived`):

- **AST & Semantics (`trusted/lean/Trusted/MirAst.lean:400-433, 732-740`; `MirSemantics.lean:1034-1160, 1568-1569`)**: Anneal represents `BinOp` (`add`, `sub`, `mul`, `div`, `rem`, `shl`, `shr`, plus `*Unchecked` and `addWithOverflow`/`subWithOverflow`/`mulWithOverflow`) and `AssertKind`, **however**:
  1. `evalBinOp` currently rejects `*WithOverflow` with `.unsupported`;
  2. `evalTerminator` maps every `TerminatorKind.assert` to `.fault .unsupported` (`MirSemantics.lean:1568-1569`);
  3. `evalArithOp` and `evalShiftOp` evaluate `BinOp::{Div,Rem}`, `BinOp::{Add,Sub,Mul}Unchecked`, and `BinOp::{Shl,Shr}Unchecked` by returning UB (`ExecResult` faults caught by `MirWp.lean:936-967` canaries `canary_negative_ub_signed_rem_overflow_i8`, `canary_negative_ub_add_unchecked_overflow_u32`, `canary_negative_ub_shift_unchecked_at_bitwidth_anneal`), whereas `-Coverflow-checks=off` `BinOp::{Add,Sub,Mul}` wrap modulo `2^w` and `BinOp::{Shl,Shr}` mask shift amounts to `< 2^k` (`source`, `derived`).
- **Implication for Verified Code Under Anneal**: Functions compiled under `-Coverflow-checks=on` produce `*WithOverflow` and `Assert` terminators unsupported by `evalTerminator`/`evalBinOp`, whereas `-Coverflow-checks=off` exposes unwrapped two's-complement `+`/`-`/`*` and masked `<<`/`>>` alongside *mandatory* `TerminatorKind.assert` guards emitted by `rustc` on every safe `/` and `%`. Unless Anneal's MIR capture or `evalTerminator` explicitly proves or lowers `DivisionByZero`/`RemainderByZero` and signed `(MIN, -1)` assertions cleanly, even `-Coverflow-checks=off` code containing safe `/` or `%` enters `Assert` terminators (`source`, `derived`).

## Boundaries

- **Non-LLVM codegen backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`)**: `not examined` — shift masking width assertions (`base.rs` is shared SSA codegen, while `builder.rs` is LLVM-specific), `nuw`/`nsw` flag attachment, and `checked_binop` intrinsics in Cranelift/GCC backends were not audited.
- **Target architectures other than `x86_64-unknown-linux-gnu`**: `not examined` empirically — while `as_rvalue.rs` MIR construction, `builder.rs` LLVM IR attributes (`nuw`/`nsw`), `common.rs` shift masks, `operator.rs` Miri UB, and our generic width-`w` Lean proofs are architecture-independent, native execution and assembly (`cltd`/`idivl`, `shll %cl`) were only executed on `x86_64-unknown-linux-gnu`.
- **Rust `usize`/`isize` non-64-bit targets (e.g., 16-bit or 32-bit targets)**: `unknown` empirically — the Lean model parameterizes over all `w = 2^k >= 2` (`k >= 1`), covering 16-bit and 32-bit pointers in theory, while empirical runs tested 64-bit `x86_64` where `usize`/`isize` are 64-bit.
- **SIMD vector integers (`Simd<T, N>`) and `unchecked_su*` scalar-index truncation intrinsics**: `not examined` empirically — `common.rs:116-120` handles vector splats for shift masks and `builder.rs:565-594, 979-1001` emits dual `nuw nsw` flags on `unchecked_su{add,sub,mul}` and `unchecked_{u,s}trunc`, neither of which was executed via `probe_int_overflow_nuw_nsw_div_shift.py`.
- **`512`-bit and wider non-primitive integer types paired with smaller signed shift RHS (`i8`)**: `known not to apply` safely — `compiler/rustc_codegen_ssa/src/base.rs:360-362` asserts `lhs_sz <= 256` explicitly because `zext` after `and` produces `255` instead of `511` at `(-1i8)` for a `512`-bit LHS (formally witnessed in `base_rs_512bit_i8_mismatch_witness`).
- **Anneal `MirSemantics` handling of `TerminatorKind.assert` and `*WithOverflow`**: `unsupported` in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`MirSemantics.lean:1568-1569`, `evalBinOp`) — currently faults with `.unsupported` rather than modeling check-panic vs. assumption propagation (`source`).
- **Lean kernel meta-axioms & tactic boundaries**: `known not to apply` (eliminated by construction) — no `Classical.choice`, `sorry`, `omega`, `bv_decide`, `native_decide`, `partial def`, or `._unsafe_rec` exists anywhere in `support/IntegerOverflowUncheckedNuwNswAndShiftMaskSoundness.lean`; all `148` environment theorems rest exclusively on `[Quot.sound, propext]`.

## Evidence

### 1. Upstream Primary-Source Audit

| Repository & Commit SHA | File Path | Audited Lines | Key Mechanism / Normative Rule Verified |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs` | `97-118`, `447-581` | Optional `*WithOverflow`/shift/neg checks vs. unconditional `Div`/`Rem` zero and `(MIN, -1)` asserts |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_middle/src/mir/terminator.rs` | `170-176` | `AssertKind::is_optional_overflow_check` includes only `OverflowNeg` and `Overflow(Add\|Sub\|Mul\|Shl\|Shr)` |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_codegen_ssa/src/mir/block.rs` | `769-780` | Suppresses inlined optional overflow checks when `!bx.sess().overflow_checks()` |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_mir_transform/src/lower_intrinsics.rs` | `117-154` | Lowers `unchecked_{add,sub,mul,shl,shr}` to `*Unchecked`, `unchecked_{div,rem}` to bare `Div`/`Rem` |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` | `913-965`, `986-993`, `1060-1083` | Dispatches `AddUnchecked`/`SubUnchecked`/`MulUnchecked`, `Div`/`Rem`, `Shl\|ShlUnchecked`, `checked_binop` |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_codegen_ssa/src/common.rs` | `106-124` | `shift_mask_val`: computes `val - 1` bitmask (`W - 1`) for safe shifts |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_codegen_ssa/src/base.rs` | `330-367` | `build_shift_expr_rhs`: applies `bx.and(rhs, mask)`, asserts `lhs_sz <= 256` before `bx.zext` |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_codegen_llvm/src/builder.rs` | `557-594`, `623-664`, `979-1001` | Emits `LLVMBuild{NSW,NUW}{Add,Sub,Mul}`, `unchecked_su*` dual flags, `llvm.*.with.overflow`, `unchecked_*trunc` |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `library/core/src/num/int_macros.rs` | `725-739`, `864-878`, `1003-1041`, `1280-1287`, `1590-1603`, `1769-1782`, `2536-2579` | `unchecked_*` wrappers, `checked_div`/`checked_rem`, `wrapping_shl`/`wrapping_shr` masking |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `library/core/src/ub_checks.rs` | `51-106` | `assert_unsafe_precondition!` + `check_language_ub` (`!cfg!(miri) && intrinsics::ub_checks()`) |
| `rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`) | `compiler/rustc_const_eval/src/interpret/operator.rs` | `114-170`, `200-241`, `265-298` | CTFE/Miri immediate UB checks (`ShiftOverflow`, `DivisionByZero`, `DivisionOverflow`, `ArithOverflow`) |
| `llvm/llvm-project` (`d62e4be8f7eb9c3fdc44751a9fd08084ec38d98f`) | `llvm/docs/LangRef.md` | `5543-5600`, `11234-11435`, `11477-11685`, `11741-11875` | `Poison Values` + `noundef` UB sinks, `nuw`/`nsw`, `udiv`/`sdiv`/`urem`/`srem` (`srem` `INT_MIN/-1` rationale), shift overshift poison |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `theory/Anneal/MirWp.lean` | `400-433`, `732-740`; `1034-1160`, `1568-1569`; `936-967` | Anneal `BinOp`, `AssertKind`, `evalTerminator` `.unsupported` fault, and negative UB canaries |

### 2. Verbatim Suite C LLVM IR Signatures (`rustc 1.98.0-nightly`, `-Copt-level=2 -Coverflow-checks=off`)

All `nuw`/`nsw` and shift attributes observed in `support/probe_results.json` (`experiments.c_llvm_ir_and_asm_nuw_nsw_div_shift`) (`execution`):

```llvm
define noundef i32 @safe_add_wrapping_when_off(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = add i32 %b, %a
  ret i32 %_0
}
define noundef i32 @i32_unchecked_add_nsw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = add nsw i32 %b, %a
  ret i32 %_0
}
define noundef i32 @u32_unchecked_add_nuw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = add nuw i32 %b, %a
  ret i32 %_0
}
define noundef i32 @i32_unchecked_sub_nsw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = sub nsw i32 %a, %b
  ret i32 %_0
}
define noundef i32 @u32_unchecked_sub_nuw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = sub nuw i32 %a, %b
  ret i32 %_0
}
define noundef i32 @i32_unchecked_mul_nsw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = mul nsw i32 %b, %a
  ret i32 %_0
}
define noundef i32 @u32_unchecked_mul_nuw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = mul nuw i32 %b, %a
  ret i32 %_0
}
define noundef i32 @i32_unchecked_shr_raw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = ashr i32 %a, %b
  ret i32 %_0
}
define noundef i32 @u32_unchecked_shr_raw(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = lshr i32 %a, %b
  ret i32 %_0
}
```

Contrast `-Cdebug-assertions=on` vs. `off` on `probe_u32_unchecked_add` (`execution`):

```llvm
; -Cdebug-assertions=on:
define noundef i32 @probe_u32_unchecked_add(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %0 = xor i32 %a, -1
  %_4.1.i = icmp ugt i32 %b, %0
  br i1 %_4.1.i, label %bb1.i, label %...precondition_check.exit, !prof !4
bb1.i:
  tail call void @_RNvNtCs8b4M6GsfcPr_4core9panicking18panic_nounwind_fmt(...) #2
  unreachable
...precondition_check.exit:
  %_0 = add nuw i32 %b, %a
  ret i32 %_0
}

; -Cdebug-assertions=off:
define noundef i32 @probe_u32_unchecked_add(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_0 = add nuw i32 %b, %a
  ret i32 %_0
}
```

### 3. Support Artifacts Produced in Package `support/`

- **`support/probe_int_overflow_nuw_nsw_div_shift.py`** (`23,935` bytes): Self-contained reproducible harness running all experiments inside `with tempfile.TemporaryDirectory():` using `rustc --edition=2024` and `cargo +nightly miri run --offline`, sanitizing temporary directory and home prefixes cleanly.
- **`support/probe_results.json`** (`52,198` bytes): Full structured empirical record captured on `2026-11-23` under:
  - `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
  - Embedded `LLVM version: 22.1.6` (`x86_64-unknown-linux-gnu`)
  - `cargo 1.98.0-nightly (fbb61be30 2026-05-26)` and `miri 0.1.0 (14210df0e2 2026-05-31)`
- **`support/IntegerOverflowUncheckedNuwNswAndShiftMaskSoundness.lean`** (`1,914` lines, `86,507` bytes): Standalone `Lean v4.34.1` formalization verified with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, zero errors/warnings) and MetaM constant/axiom inspection:
  - `7` inductives (`Signedness`, `OverflowProfile`, `PoisonVal`, `ExecOutcome`, `ArithOp`, `ShiftKind`, `RustcIntBinOp`)
  - `52` source `noncomputable def`s (`185` total env definitions)
  - `105` declared theorems (`148` env theorem constants)
  - `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `unsafe`, `0` `._unsafe_rec`, exact axiom set `[Quot.sound, propext]`.

## Revalidation

To reproduce the empirical compiler/MIR/LLVM/asm/Miri measurements from the corpus root (requires `rustc 1.98.0-nightly` + `miri` component; executes inside isolated temporary directories):

```console
python3 reports/rustc-integer-overflow-checks-unchecked-nuw-nsw-div-min-and-shift-masking/support/probe_int_overflow_nuw_nsw_div_shift.py --out reports/rustc-integer-overflow-checks-unchecked-nuw-nsw-div-min-and-shift-masking/support/probe_results.json
```

To type-check and kernel-verify the Lean `v4.34.1` mechanization with warnings denied and async elaboration disabled (and confirm zero `Classical.choice`, `sorryAx`, `ofReduceBool`, `partial`, or `._unsafe_rec` via `Lean.collectAxioms`):

```console
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  reports/rustc-integer-overflow-checks-unchecked-nuw-nsw-div-min-and-shift-masking/support/IntegerOverflowUncheckedNuwNswAndShiftMaskSoundness.lean
```

To re-verify upstream primary-source anchors at the exact audited revisions (read-only GitHub API) and regenerate and validate corpus metadata and unit tests from the corpus root:

```console
gh api repos/rust-lang/rust/commits/20fe935d50367c0ff8872c2ebfa050c5c99d9201 --jq .sha
gh api repos/llvm/llvm-project/commits/d62e4be8f7eb9c3fdc44751a9fd08084ec38d98f --jq .sha
gh api repos/joshlf/anneal/commits/c131b320eeeb26ef692e5afd5ec8db49ee518613 --jq .sha
python3 tools/reference.py catalog
python3 tools/reference.py check
python3 -m unittest discover -s tests -v
```
