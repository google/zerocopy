# `rustc` Codegen & Miri Semantics for `simd_select`, `simd_select_bitmask`, `ctlz_nonzero` / `cttz_nonzero`, and `simd_as` Saturation

## Summary

Four closely related families of Rust intrinsics—scalar/vector bit-counting (`ctlz`, `cttz`, `ctlz_nonzero`, `cttz_nonzero`, `simd_ctlz`, `simd_cttz`), SIMD lane selection (`simd_select`, `simd_reduce_all`, `simd_reduce_any`), packed bitmask selection (`simd_select_bitmask`, `simd_bitmask`), and float-to-integer conversions (`simd_as`, `simd_cast`, `float_to_int_unchecked`)—sit directly on the boundary between `rustc_const_eval`/Miri abstract-machine Undefined Behavior (UB) and `rustc_codegen_llvm` / `rustc_codegen_ssa` LLVM lowering. Any sound MIR verifier (such as Anneal's `Trusted.MirSemantics`) or codegen soundness proof must model the exact preconditions, lowering invariants, and hardware divergences established across upstream source inspection, live differential execution (`rustc 1.98.0-nightly`, LLVM `22.1.6`, `miri 0.1.0`), and constructive Lean `v4.34.1` mechanization:

1. **`ctlz_nonzero` / `cttz_nonzero` vs. `ctlz` / `cttz` / `simd_ctlz` / `simd_cttz` (`is_zero_poison` Range Refinement):**
   Scalar `ctlz_nonzero` and `cttz_nonzero` lower in `rustc_codegen_llvm` to `@llvm.ctlz.*` and `@llvm.cttz.*` with `is_zero_poison = i1 true`, whereas scalar `ctlz`/`cttz` and vector `simd_ctlz`/`simd_cttz` unconditionally pass `i1 false`. At `x = 0`, LLVM `LangRef.md` specifies `poison` for `i1 true` and bit-width `W` for `i1 false`; LLVM's `ValueTracking::getRangeForIntrinsic` (`ConstantRange([0, W))`) and `KnownBits::ctlz(true)` (`MaxLZ = min(MaxLZ, W - 1)`) tighten the static range from `[0, W]` to `[0, W)` (clearing bit `p` when `W = 2^p`, e.g., bit `5` on `i32`). At `-O2`, LLVM attaches `noundef range(i32 0, 32)` and elides downstream `n < 32` guards; on `x = 0` under native x86-64 (`bsrl` + `xorl $31` + `addl $1000`), probe execution prints `CTLZ_ZERO=3301782111` (`FOLDED_LT32=3301783111`, outside `[1000, 1032)`), while Miri halts with immediate UB. Upstream `library/core/src/intrinsics/mod.rs` doccomments still state that `*_nonzero` returns `undef` on `0` (`L1808`, `L1871`), disagreeing with LLVM `LangRef.md` (`poison`) and CTFE/Miri (immediate UB).

2. **`simd_select` MSB Extraction vs. Miri `{0, !0}` Lane Validity (`vector_mask_to_bitmask`):**
   `rustc_const_eval`'s `simd_element_to_bool` validates every lane of `simd_select`, `simd_reduce_all`, `simd_reduce_any`, and `simd_bitmask` via signed `to_int(size)`, accepting **only** `0` (`false`) or `-1` (`!0 = 2^w - 1`, `true`) and throwing immediate UB on any other bit pattern (such as `1` or `-2`). Conversely, `rustc_codegen_llvm` lowers non-scalable `simd_select` and `simd_reduce_{all,any}` via `vector_mask_to_bitmask` (`lshr (w - 1)` followed by `trunc to <N x i1>`, folded at `-O2` to `icmp slt <N x iW> %mask, zeroinitializer`), which reads only each lane's sign bit (MSB). Thus native execution silently treats `[1, 0, 1, 0]` as all-false and `[-2, -2, 1, 0]` lane `0..1` as true while Miri aborts with UB. As formalized in Lean (`unique_fixed_point_of_bit_confluence`), `{0, 2^w - 1}` is the unique fixed-point domain where MSB extraction (`vector_mask_to_bitmask`), LSB checking (`& 1`), and bitwise mixing coincide.

3. **`simd_select_bitmask` Little-Endian Packing & LLVM `22.1.6` x86-64 `U8x10` Miscompilation:**
   In `rustc_codegen_llvm` and Miri, `simd_select_bitmask` accepts a scalar unsigned/signed integer of `len.max(8).next_power_of_two()` bits or an `Align::ONE` `[u8; len.div_ceil(8)]` byte array, truncates to `i{len}`, and bitcasts to `<len x i1>`, mapping bit `i = 8 * k + b` (`b < 8`) to lane `8 * k + b` on little-endian targets (`bit_i = i` on LE, `len - 1 - i` on BE in `simd_bitmask_index`) while ignoring excess upper bits `>= len`. This induces an exact Galois bijection between `[u8; K]` bitmasks and boolean vectors of arbitrary length `N <= 8 * K` (`simdSelectBitmask_after_simdBitmask`). Live differential probing against `rustc 1.98.0-nightly` / LLVM `22.1.6`, however, uncovered an **LLVM x86-64 backend miscompilation on non-power-of-two byte vectors longer than 8 lanes (`U8x10`)**: `rustc` emits valid LLVM IR (`load i16`, `trunc i16 to i10`, `bitcast i10 to <10 x i1>`, `select <10 x i1>`), and Miri selects lane `8` from mask bit `8` (`byte 1, bit 0`), whereas native x86-64 `-O0`/`-O2` (`+sse2` and `+avx2`) replicates byte `0` across all 16 vector bytes (`punpcklbw; pshuflw $0; pshufd $68` on SSE2; `vpbroadcastb` on AVX2), silently selecting lane `8` using bit `0` instead of bit `8` (`U8x16` with `pshuflw $80; pshufd $80` and `+avx512f,+avx512bw,+avx512vl` with `kmovd %esi, %k1` lower correctly).

4. **`simd_as` Total Saturation vs. `simd_cast` & `float_to_int_unchecked` Open-Interval UB:**
   On float-to-int casts, `simd_as` lowers to `@llvm.fptosi.sat` / `@llvm.fptoui.sat` (and Miri's saturating `apfloat` conversions `to_i128` / `to_u128`), defining a total clamped function (`NaN -> 0`, `±Inf` and out-of-range finite values `-> MIN/MAX`). By contrast, `simd_cast` and scalar `float_to_int_unchecked` lower to bare `fptosi` / `fptoui` (`poison` on out-of-range or NaN) and Miri's `float_to_int_checked(..., Round::TowardZero)` (immediate UB whenever `INVALID_OP | OVERFLOW | UNDERFLOW`). Because rounding is toward zero (`TruncTowardZero`), the exact UB-free finite domain is the open interval `(-2^(w-1) - 1, 2^(w-1))` for signed `iW` (e.g., `-128.9f32` and `127.9f32` succeed for `i8`, whereas `-129.0f32` is UB) and `(-1, 2^w)` for unsigned `uW` (e.g., `-0.999f32 -> 0` and `255.9f32 -> 255` succeed for `u8`, whereas `-1.0f32` is UB).

5. **Constructive Lean `v4.34.1` Mechanization & Anneal TCB Boundary:**
   All four semantic contracts, Galois bijections, range refinements, open-interval equivalences, and differential counterexamples are mechanized in a `2,276`-line Lean `v4.34.1` module (`support/SimdSelectBitmaskCtlzAndSimdAsSoundness.lean`) compiled with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` over locked `Init.*` imports (`433` declarations, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `0` `partial`/`unsafe`, axioms strictly within `{propext, Quot.sound}`). In upstream `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted.MirAst` currently maps floats, SIMD vector types, and `Rvalue::Cast` to `.unsupported` (`L308, L475, L613`), so incorporating these intrinsics cleanly requires extending `Trusted.MirAst` and `Trusted.MirSemantics` while respecting `TrustedBoundary.lean`'s syntax/axiom/noncomputable gates.

## Applicability

These findings govern the semantics, LLVM lowering, CTFE/Miri checks, and formal verification modeling across five pinned subjects recorded in `REPORT.json`:

1. **Upstream Rust & Miri Source Audit (`rust-lang/rust` @ `5debe6a1244452beced762385f88a51857a915fc`):**
   Covers `library/core/src/intrinsics/mod.rs`, `library/core/src/intrinsics/simd/mod.rs`, `compiler/rustc_codegen_llvm/src/intrinsic.rs`, `compiler/rustc_codegen_llvm/src/builder.rs`, `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs`, `compiler/rustc_codegen_ssa/src/traits/builder.rs`, `compiler/rustc_const_eval/src/interpret/intrinsics.rs`, `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs`, `compiler/rustc_const_eval/src/interpret/cast.rs`, and `src/tools/miri/src/intrinsics/{mod.rs, math.rs, simd.rs}`. Note that this repository revision corresponds to an upstream HEAD tree whose submodule `src/llvm-project` gitlink is `08ec928a5bd1866f4008c8ad216166ca685fd380`.

2. **Executed Nightly Toolchain (`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6`, `miri 0.1.0`):**
   Covers all live `--emit=llvm-ir`, `-Copt-level={0,2}` native x86-64 binaries, target-feature assembly comparisons (`+sse2`, `+avx2`, `+avx512f,+avx512bw,+avx512vl`), Miri Stacked Borrows (default), and Miri Tree Borrows (`-Zmiri-tree-borrows`) runs preserved in `support/probe_simd_select_bitmask_ctlz_and_simd_as.py` and `support/probe_results.json`. Its bundled LLVM submodule gitlink is `08c84e69a84d95936296dfcab0e38b34100725d5`. Where line numbers shifted slightly between `14210df0e` (`2026-05-31`) and upstream HEAD `5debe6a12444`, both source files are cited; codegen structure differs primarily in trivial helpers (`bx.const_int(bx.type_i1(), 0)` in `14210df0e` at `intrinsic.rs:3406` vs. `bx.const_bool(false)` at `5debe6a12444` `intrinsic.rs:3391`), while semantics match across all inspected functions except where noted.

3. **Upstream LLVM IR & Optimization / Legalization Audit (`llvm/llvm-project` @ `5426281720dcb4d2006140fce25cd6fcfd71d5dc`):**
   Covers normative IR semantics in `llvm/docs/LangRef.md` (`@llvm.ctlz.*`, `@llvm.cttz.*`, `fptoui`, `fptosi`), range and known-bits refinement in `llvm/lib/Analysis/ValueTracking.cpp` (`getRangeForIntrinsic`, `computeKnownBitsFromOperator`, `canCreateUndefOrPoison`) and `llvm/lib/Support/KnownBits.cpp` (`KnownBits::ctlz`), constant folding in `llvm/lib/Analysis/ConstantFolding.cpp`, and vector-bitcast type widening in `llvm/lib/CodeGen/SelectionDAG/LegalizeVectorTypes.cpp` (`WidenVecRes_BITCAST`).

4. **Anneal Verification TCB & MIR Semantics (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   Covers `trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, and `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ProjectionElem`, `Rvalue`, and the `noncomputable` requirement preventing `._unsafe_rec` helper synthesis).

5. **Lean `v4.34.1` Mechanization Toolchain (`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52`):**
   Covers kernel-checked compilation (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and `.olean` MetaM constant/axiom auditing (`trustLevel := 0`, `plugins := #[]`, `loadExts := false`) of `support/SimdSelectBitmaskCtlzAndSimdAsSoundness.lean`.

**Relationship Among Subjects & Prior Corpus Coverage:**
This report establishes the **codegen lowering vs. Miri UB semantic contract** between `rust-lang/rust` and `llvm/llvm-project`, verifies it differentially on `14210df0e` (`LLVM 22.1.6`), and formalizes the contract inside `joshlf/anneal`'s Pass-1 Lean `v4.34.1` (`5045d0056`) trust boundary. Earlier reports in this corpus separately catalog all `rustc` intrinsics (`rustc-intrinsics-simd-and-arch-semantic-sources`), examine `core::simd::Mask` alignment/tail-load contracts (`core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras`), and formalize IEEE float NaN sets and rounding (`rust-floating-point-semantics-llvm-lowering-and-isa-behavior`, `float-nan-set-semantics-refinement-tiers-truncating-cast-open-interval-and-saturation`). Those findings complement rather than duplicate the present intrinsic lowering, poison range refinement, multi-byte bitmask bijection, and LLVM `22.1.6` x86-64 `U8x10` codegen divergence results.

## Findings

### 1. Bit-Counting Intrinsics: `ctlz_nonzero` / `cttz_nonzero` vs. `ctlz` / `cttz` / `simd_ctlz` / `simd_cttz`

```text
Basis: normative + documentation + source + execution + derived
```

#### 1.1 LLVM Lowering and `is_zero_poison` Polarity

In `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`rust-lang/rust@5debe6a1244452beced762385f88a51857a915fc:388-403`; identical logic at `14210df0e27c:488-503`), scalar leading/trailing zero intrinsics lower uniformly via `self.const_bool(name == sym::ctlz_nonzero || name == sym::cttz_nonzero)`:

```rust
// compiler/rustc_codegen_llvm/src/intrinsic.rs:392-403 (5debe6a12444)
sym::ctlz | sym::ctlz_nonzero | sym::cttz | sym::cttz_nonzero => {
    let y = self.const_bool(name == sym::ctlz_nonzero || name == sym::cttz_nonzero);
    let llvm_name = if name == sym::ctlz || name == sym::ctlz_nonzero {
        "llvm.ctlz"
    } else {
        "llvm.cttz"
    };
    let ret = self.call_intrinsic(llvm_name, &[llty], &[args[0].immediate(), y]);
    self.intcast(ret, result_layout.llvm_type(self), false)
}
```

By contrast, in the SIMD branch of `generic_simd_intrinsic` (`intrinsic.rs:3389-3397` in `5debe6a12444`, using `bx.const_bool(false)`; `intrinsic.rs:3404-3412` in `14210df0e`, using `bx.const_int(bx.type_i1(), 0)`), `simd_ctlz` and `simd_cttz` hardcode the second operand to `false`:

```rust
// compiler/rustc_codegen_llvm/src/intrinsic.rs:3389-3397 (5debe6a12444)
sym::simd_ctlz | sym::simd_cttz => {
    // for the (int, i1 immediate) pair, the second arg adds `(0, true) => poison`
    let dont_poison_on_zero = bx.const_bool(false);
    Ok(bx.call_intrinsic(
        llvm_intrinsic,
        &[vec_ty],
        &[args[0].immediate(), dont_poison_on_zero],
    ))
}
```

Thus `ctlz`, `cttz`, `simd_ctlz`, and `simd_cttz` emit `is_zero_poison = i1 false` (`0`), while `ctlz_nonzero` and `cttz_nonzero` emit `is_zero_poison = i1 true` (`1`).

#### 1.2 Normative LLVM IR Semantics, Static Range Refinement, and Upstream Docstring Drift

LLVM's `llvm/docs/LangRef.md` (`llvm/llvm-project@5426281720dcb4d2006140fce25cd6fcfd71d5dc`, lines `18906-18919` for `llvm.ctlz.*` and `18947-18960` for `llvm.cttz.*`) defines the exact semantic split on zero inputs:

- When `is_zero_poison == 0` (`i1 false`), `src == 0` returns the bit-width `W` of the integer element type (`[0, W]`).
- When `is_zero_poison == 1` (`i1 true`), `src == 0` produces **`poison`** (not merely `undef`).

Crucially, `i1 true` feeds directly into LLVM's range and known-bits dataflow analyses (`5426281720dc`):

1. **`ValueTracking::getRangeForIntrinsic` (`llvm/lib/Analysis/ValueTracking.cpp:10813-10825`):**
   ```cpp
   case Intrinsic::ctlz:
   case Intrinsic::cttz: {
     APInt Upper(Width, Width);
     if (!UseInstrInfo || !match(II.getArgOperand(1), m_One()))
       Upper += 1;
     return ConstantRange::getNonEmpty(APInt::getZero(Width), Upper);
   }
   ```
   When `UseInstrInfo` holds and operand 1 is constant `1` (`is_zero_poison = true`), `ConstantRange` has exclusive upper bound `Width`, i.e., `[0, Width)`. Without `i1 true`, `Upper` increments by `1` to yield `[0, Width + 1)` (`[0, Width]` closed). Note that `ValueTracking::canCreateUndefOrPoison` (`ValueTracking.cpp:8322-8326`, inspecting no-flags cases without operand checks) still returns `false` on `Intrinsic::ctlz`/`cttz` in the fast switch checked there, because zero-input poisoning is gated by `UseInstrInfo` + operand `Arg1` (`m_One()`).

2. **`KnownBits::ctlz` (`llvm/lib/Support/KnownBits.cpp:803-812`) & `ValueTracking::computeKnownBits` (`ValueTracking.cpp:2279-2295`):**
   ```cpp
   KnownBits KnownBits::ctlz(bool ZeroIsPoison) const {
     unsigned BitWidth = getBitWidth();
     unsigned MaxLZ = countMaxLeadingZeros();
     if (ZeroIsPoison)
       MaxLZ = std::min(MaxLZ, BitWidth - 1);

     KnownBits Result(BitWidth);
     Result.Zero.setBitsFrom(llvm::bit_width(MaxLZ));
     return Result;
   }
   ```
   Symmetrically, `Intrinsic::cttz` (`ValueTracking.cpp:2285-2295`) checks `if (II->getArgOperand(1) == ConstantInt::getTrue(...)) PossibleTZ = std::min(PossibleTZ, BitWidth - 1)` and sets `Known.Zero.setBitsFrom(llvm::bit_width(PossibleTZ))`. For a `32`-bit word (`BitWidth = 32`), `bit_width(31) = 5` whereas `bit_width(32) = 6`: therefore `is_zero_poison = true` proves bit `5` (`32 = 2^5`) and all higher bits `5..31` are identically `0`, letting InstCombine/IPSCCP eliminate downstream bounds comparisons `n < 32` completely!

3. **CTFE / Miri (`compiler/rustc_const_eval/src/interpret/intrinsics.rs:907-911` at `5debe6a12444`; `L943-947` at `14210df0e`):**
   ```rust
   sym::ctlz_nonzero | sym::cttz_nonzero if bits == 0 => {
       throw_ub_format!("`{name}` called on 0");
   }
   sym::ctlz | sym::ctlz_nonzero => u128::from(bits.leading_zeros()) - extra,
   sym::cttz | sym::cttz_nonzero => u128::from((bits << extra).trailing_zeros()) - extra,
   ```
   Vector `simd_ctlz`/`simd_cttz` (`intrinsics/simd.rs:79-81, 104-106`) delegate lane-by-lane to `sym::ctlz`/`sym::cttz` (`dont_poison_on_zero` behavior), never throwing zero-input UB.

4. **Documentation Disagreement (`library/core/src/intrinsics/mod.rs:1808-1809, 1871-1872`):**
   Upstream Rust docstrings on `ctlz_nonzero` and `cttz_nonzero` state *"returns `undef` when given an `x` with value `0`"*. That phrasing is stale relative to both `rustc_const_eval`/Miri (which halt immediately with UB, not frozen/unspecified integer bits) and LLVM `LangRef.md` (which defines `poison` rather than `undef`, enabling `noundef range(i32 0, 32)` propagation across return sites).

#### 1.3 Live Differential Execution (`rustc 1.98.0-nightly`, LLVM `22.1.6`, `miri 0.1.0`)

Probe A (`support/probe_simd_select_bitmask_ctlz_and_simd_as.py`, recorded in `support/probe_results.json`) contrasts `ctlz`, `ctlz_nonzero`, `cttz`, `cttz_nonzero`, `simd_ctlz`, `simd_cttz`, and guarded functions `fold_ctlz_safe_lt32` vs. `fold_ctlz_nonzero_lt32` (`if n < 32 { n.wrapping_add(1000) } else { 9999 }`):

- **LLVM `-O2` IR Attributes & Guard Deletion:**
  - `call_ctlz`: `define internal fastcc noundef range(i32 0, 33) i32 @...call_ctlz(i32 noundef %x) { %_0 = tail call range(i32 0, 33) i32 @llvm.ctlz.i32(i32 %x, i1 false); ret i32 %_0 }`
  - `call_ctlz_nonzero`: `define internal fastcc noundef range(i32 0, 32) i32 @...call_ctlz_nonzero(i32 noundef %x) { %_0 = tail call range(i32 0, 33) i32 @llvm.ctlz.i32(i32 %x, i1 true); ret i32 %_0 }` (likewise `range(i32 0, 32)` on `call_cttz_nonzero`).
  - `call_simd_ctlz`: `tail call range(i32 0, 33) <4 x i32> @llvm.ctlz.v4i32(<4 x i32> %0, i1 false)`.
  - `fold_ctlz_safe_lt32`:
    ```llvm
    define internal fastcc noundef range(i32 1000, 10000) i32 @_RNvCscNtYg2vSlvG_4main19fold_ctlz_safe_lt32(i32 noundef %x) {
    start:
      %_3.not = icmp eq i32 %x, 0
      %n = tail call range(i32 0, 33) i32 @llvm.ctlz.i32(i32 %x, i1 true)
      %0 = add nuw nsw i32 %n, 1000
      %_0.sroa.0.0 = select i1 %_3.not, i32 9999, i32 %0
      ret i32 %_0.sroa.0.0
    }
    ```
    LLVM converts safe `ctlz(x, i1 false) < 32` into an explicit zero test `icmp eq i32 %x, 0` paired with a `ctlz(..., i1 true)` call, returning `9999` (`range(i32 1000, 10000)`) on `x = 0` (`SAFE_LT32_AT_0=9999` across `-O0`, `-O2`, Miri SB, and Miri TB).
  - `fold_ctlz_nonzero_lt32`:
    ```llvm
    define internal fastcc noundef range(i32 1000, 1032) i32 @_RNvCscNtYg2vSlvG_4main22fold_ctlz_nonzero_lt32(i32 noundef %x) {
    start:
      %n = tail call range(i32 0, 33) i32 @llvm.ctlz.i32(i32 %x, i1 true)
      %0 = add nuw nsw i32 %n, 1000
      ret i32 %0
    }
    ```
    Because `ctlz_nonzero` passes `i1 true`, LLVM deletes `if n < 32` and promises return range `range(i32 1000, 1032)` (`add nuw nsw`), lowering x86-64 machine code directly to `bsrl %edi, %eax; xorl $31, %eax; addl $1000, %eax`.

- **Empirical Runtime Divergence Table (Probe A):**

| Mode | Native `-O0` (`bsr` undef) | Native `-O2` (deleted `< 32` guard) | Miri Stacked Borrows | Miri `-Zmiri-tree-borrows` |
| :--- | :--- | :--- | :--- | :--- |
| `safe` (`0`, `0x1_ffff`, `0x1_0000`, SIMD `[0,1,0x8000_0000,0x1_0000]`) | `SAFE_CTLZ=32 SAFE_CTLZ_NZ=15 SAFE_CTTZ=32 SAFE_CTTZ_NZ=16` `SIMD_CTLZ=[32,31,0,15]` `SIMD_CTTZ=[32,0,31,16]` `SAFE_LT32_AT_0=9999` (`rc=0`) | Identical (`rc=0`) | Identical (`rc=0`) | Identical (`rc=0`) |
| `ctlz_zero` (`ctlz_nonzero(0)`, `fold_ctlz_nonzero_lt32(0)`) | `CTLZ_ZERO=31 FOLDED_LT32=1031` (`rc=0`, stale `%eax`) | **`CTLZ_ZERO=3301782111 FOLDED_LT32=3301783111`** (`rc=0`, out of `[1000, 1032)`, uninitialized register bits XOR 31) | **UB (`rc=1`)**: `` `ctlz_nonzero` called on 0 `` | **UB (`rc=1`)**: `` `ctlz_nonzero` called on 0 `` |
| `cttz_zero` (`cttz_nonzero(0)`) | `CTTZ_ZERO=32` (`rc=0`) | `CTTZ_ZERO=32` (`rc=0`, `tzcnt`/`rep bsf` produces 32 on host) | **UB (`rc=1`)**: `` `cttz_nonzero` called on 0 `` | **UB (`rc=1`)**: `` `cttz_nonzero` called on 0 `` |

Look closely at the `-O2` output `CTLZ_ZERO=3301782111` (`0xc4cc265f`) and `FOLDED_LT32=3301783111` (`CTLZ_ZERO + 1000`): x86 `bsrl %edi, %eax` leaves destination register `%eax` unspecified when `%edi == 0` on Intel/AMD CPUs (typically preserving the prior register contents, which in `-O2` held a stack/address/return residual `0xc4cc2640`), and `xorl $31, %eax` yields a large arbitrary value violating LLVM's promised `noundef range(i32 0, 32)` contract. Both `-O0` (`1031`) and `-O2` (`3301783111`) fail to execute the `else 9999` arm, demonstrating why any Rust caller relying on `if ctlz_nonzero(0) < 32` as a runtime zero guard is defeated by LLVM `-O2`.

---

### 2. `simd_select` MSB Extraction vs. Miri `{0, !0}` Lane Validity

```text
Basis: normative + source + execution + derived
```

#### 2.1 `rustc_codegen_llvm` MSB Extraction vs. Miri `simd_element_to_bool`

For integer-lane SIMD masks (`M`), `rustc_codegen_llvm` converts mask vectors via `vector_mask_to_bitmask` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:2118-2130` in `5debe6a12444`):

```rust
fn vector_mask_to_bitmask<'a, 'll, 'tcx>(
    bx: &mut Builder<'a, 'll, 'tcx>,
    i_xn: Value<'ll>,
    in_elem_bitwidth: u64,
    in_len: u64,
) -> Value<'ll> {
    // Shift the MSB to the right by "in_elem_bitwidth - 1" into the first bit position.
    let shift_idx = bx.cx.const_int(bx.type_ix(in_elem_bitwidth), (in_elem_bitwidth - 1) as _);
    let shift_indices = vec![shift_idx; in_len as _];
    let i_xn_msb = bx.lshr(i_xn, bx.const_vector(shift_indices.as_slice()));
    // Truncate vector to an <i1 x N>
    bx.trunc(i_xn_msb, bx.type_vector(bx.type_i1(), in_len))
}
```

Both `simd_select` (`intrinsic.rs:2401-2431`, for non-scalable vectors; scalable vectors instead require `ty::Bool` elements and call `bx.trunc(args[0].immediate(), i1xn)` directly at `2410-2422`), `simd_bitmask` (`2451`), and `simd_reduce_all` / `simd_reduce_any` (`bitwise_red!` at `3056, 3079-3080`) funnel through `vector_mask_to_bitmask`. At `-O0`, LLVM IR literally contains `lshr <4 x i32> %0, splat (i32 31)` + `trunc <4 x i32> %3 to <4 x i1>`. At `-O2`, LLVM InstCombine folds `(trunc (lshr x, W-1) to i1)` cleanly into `icmp slt <4 x i32> %0, zeroinitializer` (`probe_results.json` `do_simd_select` / `do_reduce_any`).

In stark contrast, `rustc_const_eval/src/interpret/intrinsics/simd.rs` (`L373-392` for `simd_select`, `L469-473` for `simd_bitmask`, `L873-885` for `simd_element_to_bool`) enforces strict all-0/all-1 validity on **every** lane (unsigned and signed integer mask types alike):

```rust
// compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs:879-885 (5debe6a12444)
let val = elem.to_scalar().to_int(elem.layout.size)?;
interp_ok(match val {
    0 => false,
    -1 => true,
    _ => throw_ub_format!("each element of a SIMD mask must be all-0-bits or all-1-bits"),
})
```

Notice why `core::intrinsics::simd::simd_select` (`library/core/src/intrinsics/simd/mod.rs:640`) requires `mask must only contain 0 and !0` even though LLVM only reads the MSB: elsewhere in `core::simd` and vector ISAs, scalar conversions read the LSB (`& 1`), bitwise blends (such as NEON `vbsl`) mix bit-for-bit across all `w` bits, and LLVM's MSB extraction ignores bits `0..w-2`.

#### 2.2 Differential Execution on `[1, 0, 1, 0]` and `[-2, -2, 1, 0]` (Probe B)

Running Probe B with `a = [10, 20, 30, 40]` and `b = [100, 200, 300, 400]` confirms exact disagreement whenever any lane has value outside `{0, -1}`:

| Probe Mode | Mask Vector | Native `-O0` & `-O2` Output | Miri (Stacked & Tree Borrows) |
| :--- | :--- | :--- | :--- |
| `safe` (`do_simd_select`) | `[0, -1, 0, -1]` | `SEL=[100, 20, 300, 40]` (`rc=0`) | `SEL=[100, 20, 300, 40]` (`rc=0`) |
| `bad_mask_one` (`do_simd_select`) | `[1, 0, 1, 0]` | **`BAD_MASK_ONE=[100, 200, 300, 400]`** (`rc=0`, treats `1` as `false`!) | **UB (`rc=1`)**: `each element of a SIMD mask must be all-0-bits or all-1-bits` |
| `bad_mask_neg2` (`do_simd_select`) | `[-2, -2, 1, 0]` | **`BAD_MASK_NEG2=[10, 20, 300, 400]`** (`rc=0`, treats `-2` as `true` and `1` as `false`!) | **UB (`rc=1`)**: `each element of a SIMD mask must be all-0-bits or all-1-bits` |
| `bad_reduce_any_one` (`do_reduce_any`) | `[1, 0, 0, 0]` | **`BAD_REDUCE_ANY_ONE=false`** (`rc=0`) | **UB (`rc=1`)**: `each element of a SIMD mask must be all-0-bits or all-1-bits` |

(Also note a minor source cleanup in `simd_shuffle`: upstream `library/core/src/intrinsics/simd/mod.rs:345-359` removed `simd_shuffle_const_generic` and now requires the 3rd index argument of `simd_shuffle` to be a `const` item or inline `const { ... }` block, verified locally when passing a non-const `U32x4` failed compilation and switching to `const IDX: U32x4 = U32x4([0, 5, 2, 7]);` lowered cleanly to `shufflevector <4 x i32> %0, <4 x i32> %1, <4 x i32> <i32 0, i32 5, i32 2, i32 7>`; `compiler/rustc_codegen_llvm/src/intrinsic.rs:2257` and `const_eval/intrinsics/simd.rs:560` still retain backward-handling arms for `sym::simd_shuffle_const_generic`.)

---

### 3. `simd_select_bitmask` / `simd_bitmask` Little-Endian Packing & LLVM `22.1.6` x86-64 `U8x10` Miscompilation

```text
Basis: normative + source + execution + derived
```

#### 3.1 Codegen and CTFE/Miri Bit-Packing Semantics

In `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`L2141-2178` for `simd_select_bitmask`; `L2433-2481` for `simd_bitmask`), a bitmask argument for an `len`-lane SIMD vector accepts either:
- a scalar integer type (`ty::Int` or `ty::Uint`) of exact bit width `len.max(8).next_power_of_two()`, or
- a byte array `[u8; len.div_ceil(8)]`, which `rustc_codegen_llvm` stores to an alloca and loads as an unaligned scalar integer `i{8 * expected_bytes}` with `Align::ONE` (`intrinsic.rs:2158-2162`).

Codegen then truncates that scalar integer to `i{len}` (`bx.trunc(mask, im)`), bitcasts to `<len x i1>` (`bx.bitcast(m_im, i1xn)`), and feeds `m_i1s` to `bx.select`. Symmetrically, `simd_bitmask` extracts `<len x i1>` via `vector_mask_to_bitmask`, bitcasts `<len x i1>` to `i{len}`, and zero-extends (`bx.zext`) to `u{next_power_of_two}` or `[u8; div_ceil(8)]` (`i{8 * expected_bytes}`).

On **little-endian** architectures, LLVM lays out the lowest bit of byte `0` in bit position `0` of `i{8 * K}`, the highest bit of byte `0` in bit `7`, bit `0` of byte `1` in bit `8`, and so forth—matching Miri's `simd_bitmask_index` (`const_eval/src/interpret/intrinsics/simd.rs:856-863`):
- `Endian::Little => idx` (bit `8 * byte + b` selects lane `8 * byte + b`, and unused bits `>= len` are ignored by `trunc`);
- `Endian::Big => vec_len - 1 - idx` (MSB-first lane indexing within the least-significant `vec_len` bits).

Miri explicitly enforces a `bitmask_len <= 64` ceiling (`simd.rs:399-404, 459-464`, throwing unsupported above 64 lanes). Under `bitmask_len <= 64`, both integer (`u8`, `u16`, ...) and byte-array (`[u8; 2]`) bitmasks agree completely on `U8x16` (`BM_ARR2=[3, 1]` and `BM_U16=0x0103` when lanes `0, 1, 8` are `-1`, and `SEL_ARR16_BIT8_LANE8=9` cleanly on `[0x00, 0x01]`).

#### 3.2 Discovered LLVM `22.1.6` x86-64 SSE2/AVX2 Miscompilation on `U8x10` (`[u8; 2]` Bitmask)

Running Probe B uncovered a severe silent backend miscompilation in `rustc 1.98.0-nightly` / **LLVM `22.1.6`** on `do_simd_select_bitmask_arr2_len10(mask: [u8; 2], a: U8x10, b: U8x10) -> U8x10` (`a10 = [1..=10]`, `b10 = [11..=20]`):

1. **`rustc` Mid-End LLVM IR Is Completely Valid (`probe_results.json` `-O0` and `-O2`):**
   ```llvm
   ; opt_2 IR from probe_results.json
   define internal fastcc void @_RNvCscNtYg2vSlvG_4main33do_simd_select_bitmask_arr2_len10(
       ptr ... %_0, i16 noundef %0, ptr ... %a, ptr ... %b) unnamed_addr #4 {
   start:
     %1 = load <10 x i8>, ptr %a, align 16
     %2 = load <10 x i8>, ptr %b, align 16
     %3 = trunc i16 %0 to i10
     %4 = bitcast i10 %3 to <10 x i1>
     %5 = select <10 x i1> %4, <10 x i8> %1, <10 x i8> %2
     store <10 x i8> %5, ptr %_0, align 16
     ret void
   }
   ```
   Under these exact IR instructions:
   - For `mask = [0b1100_1011, 0b1111_1110]` (`[203, 254]`): bit `8` (byte `1`, bit `0`) is `0`, so lane `8` must select `b10[8] = 19` (`SEL_ARR10 = [1, 2, 13, 4, 15, 16, 7, 8, 19, 10]`). Miri SB & TB both output **`19`** at lane `8`.
   - For `mask = [0x00, 0x01]`: bit `8` is `1` and bit `0` is `0`, so lane `8` must select `a10[8] = 9` and lanes `0..7` must select `b10[0..7]` (`SEL_ARR10_BIT8 = [11, 12, 13, 14, 15, 16, 17, 18, 9, 20]`). Miri SB & TB both output **`9`** at lane `8`.

2. **Native x86-64 Execution Silently Selects Wrong Lanes (`-O0` and `-O2`):**
   - `native opt_0` and `native opt_2` BOTH output `SEL_ARR10 = [1, 2, 13, 4, 15, 16, 7, 8, 9, 10]` (lane `8` is **`9`** instead of `19`) and `SEL_ARR10_BIT8 = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]` (lane `8` is **`19`** instead of `9`)!
   - By contrast, 16-lane `U8x16` (`SEL_ARR` and `SEL_ARR16_BIT8_LANE8 = 9`) executes identically on Miri and native `-O0`/`-O2`.

3. **x86-64 Disassembly Isolates the Exact Instruction Divergence (`+sse2`, `+avx2` vs. `+avx512bw`):**
   ```asm
   ; U8x16 (CORRECT on +sse2): pshuflw $80 (0,0,1,1) / pshufd $80 places byte 0 in low 8 lanes, byte 1 in high 8 lanes
   movd    %esi, %xmm0
   punpcklbw %xmm0, %xmm0          ; [b0, b0, b1, b1, ...]
   pshuflw $80, %xmm0, %xmm0       ; [b0, b0, b0, b0, b1, b1, b1, b1, ...]
   pshufd  $80, %xmm0, %xmm0       ; bytes 0..7 = b0, bytes 8..15 = b1

   ; U8x10 (BROKEN on +sse2): pshuflw $0 (0,0,0,0) / pshufd $68 destroys byte 1 and broadcasts byte 0!
   movd    %esi, %xmm0
   punpcklbw %xmm0, %xmm0          ; [b0, b0, b1, b1, ...]
   pshuflw $0, %xmm0, %xmm0        ; overwrites ALL low 4 words with word 0 = (b0, b0)!
   pshufd  $68, %xmm0, %xmm0       ; duplicates low qword -> ALL 16 lanes get byte 0!

   ; U8x10 (BROKEN on +avx2): explicitly broadcasts byte 0 across the entire xmm register!
   vmovd       %esi, %xmm1
   vpbroadcastb %xmm1, %xmm1       ; ignores bits 8..9 (byte 1) completely!

   ; U8x10 (OPMASK on +avx512f,+avx512bw,+avx512vl): uses native predicate mask register %k1
   kmovd   %esi, %k1
   vmovdqu8 (%rdx), %xmm0 {%k1}
   ```
   Under SSE2 and AVX2, LLVM SelectionDAG type legalization widens `<10 x i1>` / `trunc i16 to i10; bitcast i10 to <10 x i1>` into `<16 x i8>` vector operations (`WidenVecRes_BITCAST` at `llvm/lib/CodeGen/SelectionDAG/LegalizeVectorTypes.cpp:6598-6709`, plus downstream X86 target lowering/combining — exact internal pass blame beyond observed IR/asm is recorded as `unknown` in Boundaries). On both default SSE2 targets and `+avx2`, byte `1` (`bits 8..9`) is discarded and replaced with byte `0` (`bits 0..1`), causing bit `i` of `U8x10` for `i in {8, 9}` to observe bit `i - 8`. Because Miri interprets `rustc` MIR directly rather than executing LLVM SelectionDAG, Miri passes while compiled x86-64 binaries silently compute wrong bytes! (Notice also that the AVX-512 binary was inspected via `--emit=asm` rather than executed natively, so runtime behavior under `+avx512bw` is marked not examined natively in Boundaries.)

---

### 4. Float-to-Integer Casts: `simd_as` Total Saturation vs. `simd_cast` / `float_to_int_unchecked`

```text
Basis: normative + documentation + source + execution + derived
```

#### 4.1 Codegen and Miri Divergence Across Saturating vs. Unchecked Conversions

For `(Style::Float, Style::Int(sign))` vector casts (`compiler/rustc_codegen_llvm/src/intrinsic.rs:3271-3281`):
- **`simd_cast` (`name == sym::simd_as` is `false`):** Calls `bx.fptoui` or `bx.fptosi` (`cg_llvm/builder.rs:1015-1060`), emitting unguarded LLVM `fptoui <N x float> %0 to <N x iW>` / `fptosi` instructions (`poison` whenever `NaN`, `±Inf`, or the truncated-toward-zero value falls outside the target integer type per `llvm/docs/LangRef.md:13424-13473` and `ValueTracking.cpp:8313-8317`, where `Instruction::FPToSI | Instruction::FPToUI => return true` unconditionally marks them poison-generating). On `is_like_wasm` targets (`f32`/`f64 -> i32`/`i64`), `builder.rs:1030-1059` deliberately substitutes `@llvm.wasm.trunc.{unsigned,signed}` instead of IR `fptoui`/`fptosi` to exploit trapping semantics rather than letting LLVM insert guard branches around poison.
- **`simd_as` (`name == sym::simd_as` is `true`):** Calls `bx.cast_float_to_int` (`rustc_codegen_ssa/src/traits/builder.rs:400-418`), which dispatches to `self.fptosi_sat` / `self.fptoui_sat` (`cg_llvm/builder.rs:1007-1013`), emitting `@llvm.fptosi.sat.*` / `@llvm.fptoui.sat.*`.
- **Scalar `float_to_int_unchecked` (`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:373-396`):** Emits scalar `bx.fptosi` / `bx.fptoui`, identical in poison/UB contract per lane to `simd_cast`. (Its docstring at `core/src/intrinsics/mod.rs:1675` similarly says *"may return undef"* despite LLVM defining `poison` and Miri triggering UB.)

In CTFE/Miri (`const_eval/intrinsics/simd.rs:530-542`, `cast.rs:384-410`, `intrinsics.rs:1306-1363`, `miri/src/intrinsics/math.rs:168-182`):
- **`simd_as`:** Calls `float_to_float_or_int` -> `cast_from_float`, which invokes `rustc_apfloat::Float::to_i128` / `to_u128` (saturating casts returning `0` on `NaN`, `MIN` on underflow/`-Inf`, `MAX` on overflow/`+Inf`).
- **`simd_cast` and `float_to_int_unchecked`:** Call `float_to_int_checked(&op, dest.layout, Round::TowardZero)?`. Inside `float_to_int_checked`, `INEXACT` is ignored (fractional truncation is permitted), whereas `Status::INVALID_OP | Status::OVERFLOW | Status::UNDERFLOW` forces `None`, raising immediate Miri UB (`"`...` called on {val} which cannot be represented in target type"`).

#### 4.2 Exact Open-Interval Domain Proof & Differential Execution (Probe C)

Because conversion rounds **toward zero** (`Round::TowardZero`), a finite float `x` fails representation check `[MIN, MAX]` if and only if its integer truncation lies outside `[MIN, MAX]`:
- **Signed `iW` (`W >= 1`, `MIN = -2^(W-1)`, `MAX = 2^(W-1) - 1`):** `trunc_toward_zero(x) in [-2^(W-1), 2^(W-1) - 1]` holds iff `x` belongs to the strict open interval **`(-2^(W-1) - 1, 2^(W-1))`**! Thus for `i8`, `-128.9f32` truncates toward zero to `-128` (valid!) and `127.9f32` truncates to `127` (valid!), whereas `-129.0f32` truncates to `-129` (UB!).
- **Unsigned `uW` (`MIN = 0`, `MAX = 2^W - 1`):** `trunc_toward_zero(x) in [0, 2^W - 1]` holds iff `x` belongs to the strict open interval **`(-1, 2^W)`**! Thus for `u8`, `-0.999f32` truncates toward zero to `0` (valid!) and `255.9f32` truncates to `255` (valid!), whereas `-1.0f32` truncates to `-1` (UB!).

Probe C (`support/probe_results.json`) confirms every boundary across `-O0`, `-O2`, Miri SB, and Miri TB:

| Test Case / Input | Native `-O0` & `-O2` | Miri (Stacked & Tree Borrows) |
| :--- | :--- | :--- |
| `simd_as<f32x4 -> i32x4>([NaN, 1e20, -1e20, 42.9])` | `[0, 2147483647, -2147483648, 42]` (`rc=0`) | `[0, 2147483647, -2147483648, 42]` (`rc=0`) |
| `simd_as<f32x4 -> i32x4>([+Inf, -Inf, -0.999, 2^31])` | `[2147483647, -2147483648, 0, 2147483647]` (`rc=0`) | `[2147483647, -2147483648, 0, 2147483647]` (`rc=0`) |
| `simd_as<f32x4 -> u32x4>([-1.5, 1e20, NaN, 42.9])` | `[0, 4294967295, 0, 42]` (`rc=0`) | `[0, 4294967295, 0, 42]` (`rc=0`) |
| `simd_cast<f32x4 -> i8x4>([-128.9, 127.9, -0.999, 0.999])` & `float_to_int_unchecked(-128.9f32 -> i8)` | `[-128, 127, 0, 0]`, `SCALAR_I8_OPEN=-128` (`rc=0`) | `[-128, 127, 0, 0]`, `SCALAR_I8_OPEN=-128` (`rc=0`) |
| `simd_cast<f32x4 -> u8x4>([-0.999, 255.9, 0.0, 42.9])` & `float_to_int_unchecked(-0.999f32 -> u8)` | `[0, 255, 0, 42]`, `SCALAR_U8_OPEN=0` (`rc=0`) | `[0, 255, 0, 42]`, `SCALAR_U8_OPEN=0` (`rc=0`) |
| `simd_cast<f32x4 -> i32x4>([NaN, 1e30, -1e30, 42.9])` (`simd_cast_oob`) | `[-2147483648, -2147483648, -2147483648, 42]` (`rc=0`, x86 `cvttps2dq` indefinite sentinel) | **UB (`rc=1`)**: `` `simd_cast` intrinsic called on NaN_f32 which cannot be represented in target type `i32` `` |
| `simd_cast<f32x4 -> i8x4>([-129.0, 0, 0, 0])` (`simd_cast_i8_oob`) | `[-128, 0, 0, 0]` (`rc=0`) | **UB (`rc=1`)**: `` `simd_cast` intrinsic called on -129f32 which cannot be represented in target type `i8` `` |
| `simd_cast<f32x4 -> u8x4>([-1.0, 0, 0, 0])` (`simd_cast_u8_neg1`) | `[0, 0, 0, 0]` (`rc=0`) | **UB (`rc=1`)**: `` `simd_cast` intrinsic called on -1f32 which cannot be represented in target type `u8` `` |
| `float_to_int_unchecked(1e30f32 -> i32)` / `(NaN -> i32)` | `-2147483648` (`rc=0`) | **UB (`rc=1`)**: `` `float_to_int_unchecked` intrinsic called on ... `` |

---

### 5. Kernel-Checked Lean `v4.34.1` Formalization & Anneal Pass-1 Alignment

```text
Basis: source + execution + derived
```

#### 5.1 Formalization Architecture & Key Mechanized Theorems (`support/SimdSelectBitmaskCtlzAndSimdAsSoundness.lean`)

The formalization contains `2,276` lines (`433` declarations imported at `trustLevel := 0`) using exclusively `prelude` plus `14` locked `Init.*` modules from `joshlf/anneal`'s `trusted/lean/foundation-lock.json` (`Init.Core`, `Init.Notation`, `Init.NotationExtra`, `Init.Tactics`, `Init.SimpLemmas`, `Init.Data.Nat.Basic`, `Init.Data.Nat.Div.Basic`, `Init.Data.Int.Basic`, `Init.Data.List.Basic`, `Init.Data.List.Notation`, `Init.Data.Option.Basic`, `Init.WF`, `Init.WFTactics`), strict prefix `Nat.div` / `Nat.mod` helpers, and `noncomputable def` on every definition:

| Module | Core Definitions & Mechanized Theorems | Axiom Closure |
| :--- | :--- | :--- |
| **Module 0 (`Outcome`, `pow2`, `bitAt`)** | `Outcome α` (`ok`/`ub`), `Outcome.refines` preorder (`refines_refl`, `refines_trans`, `refines_ub`), `nat_div_div_eq_div_mul`, `nat_mod_mul_eq`, `bitAt_add_pow2_mul_low`, `bitAt_add_pow2_mul_high`, `bitAt_allOnes_lt` | `[]` / `[propext]` |
| **Module 1 (`simd_select`, `simd_reduce_{all,any}`)** | `msbLane`, `lsbLane`, `decodeSimdMaskLane?`, `validMaskVec`, `simdSelectMiri`, `simdSelectLlvmMsb`, `unique_fixed_point_of_bit_confluence` (unique `{0, 2^w - 1}` fixed point), `simdSelectMsb_refines_miri`, `simdSelectMsb_eq_miri_of_valid`, `simdReduceAll_refines_miri`, `simdReduceAny_refines_miri`, `simdSelect_counterexample_mask_one`, `simdSelect_counterexample_mask_neg2`, `simdReduceAny_counterexample_mask_one` | `[Quot.sound, propext]` / `[propext]` |
| **Module 2 (`simd_select_bitmask`, `simd_bitmask`)** | `bitsToNatLE`, `natToBitsLE`, `bytesToNatLE`, `natToBytesLE`, `bitmaskBytesToBools`, `boolsToBitmaskBytes`, `bitAt_bytesToNatLE` (bit `8*k+b` of byte array = bit `b` of byte `k`), `bitmaskBytesToBools_boolsToBitmaskBytes` (Galois left-inverse for all `N <= 8*K`), `boolsToBitmaskBytes_bitmaskBytesToBools`, `bitmaskBytesToBools_upper_bit_invariant`, `simdSelectBitmask_after_simdBitmask`, `llvm_x86_u8x10_bitmask_bug_witness` (`[203, 254]` & `[0, 1]` vs. `buggySse2ReplicateByte0`) | `[Quot.sound, propext]` / `[propext]` |
| **Module 3 (`ctlz`/`cttz` & `*_nonzero`)** | `ctlzStep`, `cttzStep`, bit-spec theorems (`ctlzStep_prefix_zero`, `ctlzStep_first_one`, `cttzStep_prefix_zero`, `cttzStep_first_one`), `ctlz_safe_total_range` (`<= W`), `ctlz_nonzero_strict_range` & `cttz_nonzero_strict_range` (`< W`), `ctlz_safe_refines_nonzero`, `cttz_safe_refines_nonzero`, `ctlz_nonzero_clears_high_bits` (clears bit `p+j` for `W = 2^p`), `ctlz_nonzero_lt_guard_elision_sound`, `ctlz_zero_divergence_witness` | `[]` / `[propext]` |
| **Module 4 (`simd_as` vs. `simd_cast`)** | `ExtFloat` (`nan`, `posInf`, `negInf`, `finite`), `truncTowardZero`, `inOpenFloatDomain`, `evalFloatToIntSat`, `evalFloatToIntUnchecked`, `truncInBounds_iff_inOpenFloatDomain`, `simdAs_total_and_in_bounds`, `simdAs_refines_simdCast`, `float_to_int_open_boundary_witnesses` | `[]` / `[propext]` |
| **Module 5 (Unified Contract)** | `all_four_intrinsic_contracts_sound`: single joint theorem bundling Modules 1–4 refinement, LE bijection, strict `< w` range + branch elision soundness, and total clamped float-to-int refinement | `[Quot.sound, propext]` |

#### 5.2 TCB Discipline and Upstream `joshlf/anneal` Support Boundary

An `.olean` MetaM environment audit (`MOD_IDX=51`, `TOTAL_DECLS=433`) verified:
- `UNSAFE_REC_COUNT = 0`: marking every `def` as `noncomputable def` prevents Lean 4 from synthesizing `partial` `._unsafe_rec` compiler auxiliaries (which `TrustedBoundary.validateRepoConstant` rejects at `trusted/audit/TrustedBoundary.lean:1136-1153`, matching `MirAst.lean:77-91`);
- `PARTIAL_OR_UNSAFE_DEFN_COUNT = 0`, `UNSAFE_CONST_COUNT = 0`, `DISALLOWED_AXIOMS_COUNT = 0`;
- Zero invocations of `sorryAx`, `Classical.choice`, `Lean.ofReduceBool` (`bv_decide` / `native_decide`), `omega`, or `deriving` clauses on data inductives.

In upstream `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` currently leaves `TyKind::Float`, SIMD vector `TyKind`, and `Rvalue::Cast` unmodeled and maps them to `.unsupported` (`trusted/lean/Trusted/MirAst.lean:308, 475, 613`), failing closed in `Trusted.MirSemantics`. Adding any of the four intrinsic families to Anneal's MIR semantics requires lifting those representations into `Trusted.MirAst` / `Trusted.MirSemantics` and enforcing the `{0, !0}` mask guard, `bits != 0` guard for `ctlz_nonzero`/`cttz_nonzero`, open-interval guard for `float_to_int_unchecked`/`simd_cast`, and little/big-endian `simd_bitmask` indexing as exact UB conditions.

## Boundaries

- **not examined (architectures & SIMD widths outside x86-64 LE and `U8x10`/`U8x16`):**
  - Big-endian targets (`simd_bitmask_index` reverses bit indices `vec_len - 1 - idx`), ARM AArch64 (`vbsl` / SVE predicate registers), scalable vectors (`scalable_vector` `ty::Bool` `simd_select` path at `cg_llvm/intrinsic.rs:2410-2422`), WebAssembly (`@llvm.wasm.trunc.{signed,unsigned}` emission in `cg_llvm/builder.rs:1030-1059`), and physical runtime execution of the `+avx512bw` binary (inspected via `--emit=asm` only; not executed on AVX-512 hardware).
  - Non-power-of-two `simd_select_bitmask` element/lane combinations beyond `U8x10` and `U8x16` (e.g., `u16x10`, `u8x12`, `u8x20`, `u8x33`) under `rustc 1.98.0-nightly` / LLVM `22.1.6` were not included in the automated JSON harness.
- **unknown (exact internal SelectionDAG pass vs. X86 backend lowering split for `U8x10`):**
  - While `--emit=llvm-ir` (`trunc i16 to i10; bitcast i10 to <10 x i1>; select`) proves `rustc_codegen_llvm` IR is sound and Miri computes the right byte, and x86-64 `--emit=asm` shows byte `0` replication (`pshuflw $0` on SSE2, `vpbroadcastb` on AVX2), we did not run LLVM `-print-after-all` / `-debug-only=legalize-types` to pinch whether the bug originates inside generic `DAGTypeLegalizer::WidenVecRes_BITCAST` (`LegalizeVectorTypes.cpp:6598-6709`) or X86 target lowering/DAGCombine of `<16 x i1>` bitcasts. Also unknown whether upstream `llvm/llvm-project@5426281720dc` or newer rustc builds with LLVM `23.x` already fixed this bug (`rustc 1.98.0-nightly` links LLVM `22.1.6`).
- **known not to apply:**
  - `simd_ctlz` / `simd_cttz` do **not** inherit scalar `ctlz_nonzero`'s `i1 true` poison contract (`intrinsic.rs:3389-3397`), and LLVM does not emit `[0, W)` assumptions for them.
  - `simd_select_bitmask` on a scalar `[u8; 2]` mask ignores excess upper bits `>= N` rather than requiring padding bits to be zero, unlike integer mask lanes in `simd_select` where every non-`{0, -1}` bit pattern is Miri UB.
  - `simd_as` never produces Miri UB or LLVM poison on `NaN`, `±Inf`, or out-of-range finite values; conclusions about `simd_cast` / `float_to_int_unchecked` UB do not apply to `simd_as`.
  - Miri Stacked Borrows vs. Tree Borrows aliasing models (`-Zmiri-tree-borrows`) do **not** alter outcomes for any of these intrinsic UB checks, because all four checks operate on immediate scalars/vectors before or independent of borrow retagging.
- **unsupported:**
  - `simd_bitmask` / `simd_select_bitmask` on vectors with `len.next_multiple_of(8) > 64` explicitly throw `FaultKind::Unsupported` in CTFE/Miri (`const_eval/intrinsics/simd.rs:399-404, 459-464`).
  - `joshlf/anneal@c131b320e` `Trusted.MirAst` does not currently support `Float`, SIMD vectors, or `Rvalue::Cast` (`MirAst.lean:308, 475, 613`).

## Evidence

- **Primary Rust & Miri Source (`rust-lang/rust` HEAD `5debe6a1244452beced762385f88a51857a915fc` & executed `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
  - `compiler/rustc_codegen_llvm/src/intrinsic.rs`: scalar `ctlz`/`ctlz_nonzero`/`cttz`/`cttz_nonzero` (`L391-403` at HEAD; `L491-503` at `14210df0e`), `vector_mask_to_bitmask` (`L2118-2130`), `simd_select_bitmask` (`L2141-2178`), `simd_shuffle_const_generic` / `simd_shuffle` (`L2257-2325`), `simd_select` (`L2401-2431`), `simd_bitmask` (`L2433-2481`), `simd_reduce_{and,or,xor,all,any}` (`L3045-3080`), `simd_cast` vs. `simd_as` (`L3271-3281`), `simd_ctlz` / `simd_cttz` (`L3389-3397` at HEAD; `L3404-3412` at `14210df0e`).
  - `compiler/rustc_codegen_llvm/src/builder.rs` (`fptoui_sat`/`fptosi_sat`/`fptoui`/`fptosi` wasm branch, `L1007-1060`), `compiler/rustc_codegen_ssa/src/traits/builder.rs` (`cast_float_to_int`, `L400-418`), `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs` (`float_to_int_unchecked`, `L373-396`).
  - `compiler/rustc_const_eval/src/interpret/intrinsics.rs` (`ctlz_nonzero`/`cttz_nonzero` UB at `L907-911` [`14210df0e:943-947`], `float_to_int_checked` at `L1306-1363`), `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`simd_ctlz`/`simd_cttz` `L79-106`, `simd_select` `L373-392`, `simd_select_bitmask` `L394-455`, `simd_bitmask` `L457-503`, `simd_cast`/`simd_as` `L504-542`, `simd_bitmask_index` `L856-863`, `simd_element_to_bool` `L873-885`), `compiler/rustc_const_eval/src/interpret/cast.rs` (`cast_from_float` `L384-410`).
  - `src/tools/miri/src/intrinsics/{mod.rs, math.rs:168-182, simd.rs:1-80}`, `library/core/src/intrinsics/mod.rs` (`float_to_int_unchecked` `L1675-1682`, `ctlz_nonzero` `L1808-1828`, `cttz_nonzero` `L1871-1885`), `library/core/src/intrinsics/simd/mod.rs` (`simd_shuffle` `L345-359`, `simd_bitmask` `L592-627`, `simd_select` `L629-643`, `simd_select_bitmask` `L645-659`).
- **Primary LLVM Source & Normative IR (`llvm/llvm-project` HEAD `5426281720dcb4d2006140fce25cd6fcfd71d5dc`):**
  - `llvm/docs/LangRef.md`: `fptoui` (`L13401-13436`), `fptosi` (`L13438-13473`), `llvm.ctlz.*` (`L18897-18919`), `llvm.cttz.*` (`L18923-18960`).
  - `llvm/lib/Analysis/ValueTracking.cpp` (`computeKnownBitsFromOperator` `Intrinsic::ctlz`/`cttz` `L2279-2295`, `canCreateUndefOrPoison` `L8313-8326`, `getRangeForIntrinsic` `L10813-10825`), `llvm/lib/Support/KnownBits.cpp` (`KnownBits::ctlz` `L803-812`), `llvm/lib/CodeGen/SelectionDAG/LegalizeVectorTypes.cpp` (`WidenVecRes_BITCAST` `L6598-6709`).
- **Executed Differential Suite (`support/probe_simd_select_bitmask_ctlz_and_simd_as.py`, `support/probe_results.json`, `2026-11-23`):**
  - Executed on `x86_64-unknown-linux-gnu` under `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` and `miri 0.1.0 (14210df0e2 2026-05-31)` across `--emit=llvm-ir -Copt-level={0,2}`, native execution `-Copt-level={0,2}`, `cargo +nightly miri run --offline`, and `MIRIFLAGS=-Zmiri-tree-borrows`, plus `--emit=asm -Ctarget-feature={+sse2,+avx2,+avx512f,+avx512bw,+avx512vl}` for Probe B `U8x10`.
- **Anneal TCB & Kernel-Checked Lean `v4.34.1` Proof (`joshlf/anneal@c131b320e`, `leanprover/lean4` `5045d0056`, `support/SimdSelectBitmaskCtlzAndSimdAsSoundness.lean`):**
  - `trusted/audit/TrustedBoundary.lean` (`allowedHeaderKinds`..`allowedTheorySyntaxKinds` `L442-575`, `validateRepoConstant` `L1136-1153`), `trusted/lean/foundation-lock.json` (`51` locked `Init.*` modules), `trusted/lean/Trusted/MirAst.lean` (`noncomputable` convention `L75-91`, `.unsupported` variants `L308, L475, L613`).
  - `support/SimdSelectBitmaskCtlzAndSimdAsSoundness.lean` (`2,276` LOC, `433` kernel declarations) verified via `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc=0`) and MetaM `.olean` inspection at `trustLevel := 0` confirming `0` `._unsafe_rec`, `0` `partial`/`unsafe`, `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`.

## Revalidation

To revalidate all empirical and mechanized findings on another `rustc`, LLVM, or `anneal` revision:

1. **Re-run the Complete Differential `rustc` / LLVM-IR / `Miri` Probe (`< 15s` with cached Miri sysroot):**
   ```bash
   python3 reports/rustc-simd-select-msb-bitmask-ctlz-poison-and-simd-as-saturation-soundness/support/probe_simd_select_bitmask_ctlz_and_simd_as.py
   ```
   Confirm `CTLZ_ZERO` vs. `SAFE_LT32_AT_0=9999` (`fold_ctlz_nonzero_lt32` vs. `fold_ctlz_safe_lt32` in `opt_2` IR), confirm `BAD_MASK_ONE` / `BAD_MASK_NEG2` native vs. Miri UB, verify whether LLVM has fixed `SEL_ARR10` / `SEL_ARR10_BIT8` (`U8x10` native lane `8` matching Miri `[..., 19, 10]` and `[..., 9, 20]`), and inspect `simd_cast_i8_oob` (`-129.0`) vs. `simd_cast_u8_neg1` (`-1.0`).

2. **Minimal x86-64 `U8x10` Bitmask Assembly Check:**
   Emit `--emit=asm -Copt-level=2` (and `-Ctarget-feature=+avx2` vs. `+avx512bw`) for `do_simd_select_bitmask_arr2_len10` and check whether LLVM still lowers `<10 x i1>` bitcast selection via `pshuflw $0` / `vpbroadcastb` instead of propagating mask byte `1` (`bits 8..9`) into bytes `8..9`.

3. **Re-verify Lean `v4.34.1` Proof & Zero-`_unsafe_rec` / Axiom Hygiene:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-simd-select-msb-bitmask-ctlz-poison-and-simd-as-saturation-soundness/support/SimdSelectBitmaskCtlzAndSimdAsSoundness.lean
   ```
   Follow with `.olean` MetaM constant inspection verifying `0` `._unsafe_rec` helpers, `0` `partial`/`unsafe` definitions, `0` `sorryAx`/`Classical.choice`/`ofReduceBool` axioms, and confirming `foundation-lock.json` still admits every imported `Init.*` module.

4. **Check Upstream Source Deltas:**
   Inspect `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`ctlz_nonzero`, `vector_mask_to_bitmask`, `simd_select_bitmask`, `simd_select`, `simd_cast`/`simd_as`, `simd_ctlz`/`simd_cttz`), `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`simd_element_to_bool`), and `joshlf/anneal`'s `Trusted/MirAst.lean` for any lifted float/SIMD/cast constructors.
