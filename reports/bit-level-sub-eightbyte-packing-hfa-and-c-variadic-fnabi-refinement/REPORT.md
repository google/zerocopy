# Bit-Level Sub-Eightbyte Packing, HFA Vector Lanes, C Bitfields, and C-Variadic (`va_list`) `FnAbi` Refinement Across All 8 Tier 1 Targets

## Summary

Mechanizes concrete `BitVec 64` and `BitVec 128` register/stack marshaling refinement (`ConcreteBitVecFnAbiRefinement`), C FFI bitfield storage-unit allocation (System V vs. Microsoft Visual C++), and all four Tier 1 C-variadic (`extern "C" fn(..., ...)` / `core::ffi::VaList`) state machines in `475` lines of self-contained Lean `v4.34.1` (`542` total lines, `0` `sorry`, `0` `native_decide`), cross-checked against `rustc 1.99.1` and `clang 19.1.7` across all `8` Tier 1 targets plus live C-to-Rust FFI execution on `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` (`qemu-aarch64`).

## Applicability

- **Subjects and pinned revisions:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`): `rustc_target::callconv` (`x86_64.rs`, `aarch64.rs`, `x86_win64.rs`, `x86.rs`), `rustc_abi::PassMode` (`Direct`, `Pair`, `Cast`, `Indirect`), `ArgExtension` (`None`, `Zext`, `Sext`), and `core::ffi::VaList` (`va_arg` MIR intrinsic lowering).
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) and `clang 19.1.7`: System V AMD64, AAPCS64 (Linux, Apple Darwin `DarwinPCS`, Windows ARM64), Windows x64, and i686 System V / MSVC bitfield and ABI lowering.
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): kernel-checked bit-level and `BitVec 64`/`BitVec 128` proofs in [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean) (`6,071.81 ms` verification time).
- **Target matrix (`8` Tier 1 targets):** `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-pc-windows-msvc`, and `aarch64-pc-windows-msvc`.
- **Upstream foundation:** Discharges the abstract `MirVal` scalar-field boundary and the non-variadic `FnAbi` restriction in `lean-fnabi-marshaling-refinement-sysv64-win64-aapcs64-i686`, and connects byte-level padding provenance (`AbstractByte.Uninit`) from `typed-place-memory-object-model-padding-provenance-and-cast-soundness` directly to hardware shift-and-mask register packing.

## Findings

### 1. Concrete `BitVec 64` Shift/Mask Sub-Eightbyte Packing and Bit-Level Algebra

In `lean-fnabi-marshaling-refinement-sysv64-win64-aapcs64-i686`, multi-field sub-eightbyte aggregates such as `#[repr(C)] struct Sub8Tuple { a: u8, b: u16, c: u32 }` (`size = 8 B`, `align = 4 B`, with a 1-byte padding hole at byte offset `1`) were represented as lists of abstract `MirVal` scalars. In compiled machine code (`rustc 1.99.1` `-C opt-level=3`), `PassMode::Cast` coerces `Sub8Tuple` into a single `i64` register (`%rdi` on System V AMD64, `x0` on AAPCS64/Darwin/WinARM64, `%rcx` on Windows x64, and `edx:eax` return on `i686-pc-windows-msvc`), packing and extracting fields via hardware bitwise shifts (`shl`, `lshr`, `ashr` / `ubfx`, `sbfx`, `bfi`) and masks (`and`, `or`).

#### 1.1 Universal Bit-Indexed and Concrete `BitVec 64` Formulations

In [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean), we mechanize both a concrete `BitVec 64` shift/mask algebra (`packFieldBV64` and `extractFieldBV64`) and a universal bit-indexed register model (`BitWord := Nat → Bool`, `packBits`, `extractBitsZext`, `extractBitsSext`) over arbitrary bit offsets `off` and widths `width`:

```lean
def packFieldBV64 (offsetBytes sizeBytes : Nat) (acc fieldVal : BitVec 64) : BitVec 64 :=
  let sh := offsetBytes * 8
  let m  := byteMaskBV64 sizeBytes
  let cleared := acc &&& ~~~(m <<< sh)
  cleared ||| ((fieldVal &&& m) <<< sh)

def extractFieldBV64 (offsetBytes sizeBytes : Nat) (ext : ArgExtension) (word : BitVec 64) : BitVec 64 :=
  let sh := offsetBytes * 8
  let m  := byteMaskBV64 sizeBytes
  let raw := (word >>> sh) &&& m
  match ext with
  | .None | .Zext => raw
  | .Sext =>
    if sizeBytes == 0 || sizeBytes >= 8 then raw
    else
      let signBit := (raw >>> (sizeBytes * 8 - 1)) &&& 1#64
      if signBit == 1#64 then raw ||| ~~~m else raw
```

We prove four machine-checked theorems in [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean) governing sub-eightbyte packing, caller `ArgExtension` (`None`, `Zext`, `Sext`), and uninitialized inter-field padding (`AbstractByte.Uninit`):

1. **`extractBitsZext_packBits_same`:** For all `off width : Nat` and `acc fieldVal : BitWord`, extracting `width` zero-extended bits at `off` immediately after `packBits off width acc fieldVal` yields `extractBitsZext 0 width fieldVal`, independent of any prior bit pattern in `acc`.
2. **`extractBitsSext_packBits_same`:** For all `off width : Nat` with `0 < width`, extracting `width` sign-extended bits (`Sext`) at `off` after `packBits off width acc fieldVal` yields `extractBitsSext 0 width fieldVal`.
3. **`extractBitsZext_packBits_disjoint`:** Whenever `off1 + w1 ≤ off2 ∨ off2 + w2 ≤ off1`, packing a second field at `(off2, w2)` leaves `extractBitsZext off1 w1` strictly invariant.
4. **`unpack_pack_eightbyte_three_fields_id` & `unpack_pack_eightbyte_bitvec_id`:** Packing three disjoint fields `(u8, u16, u32)` at byte offsets `(0, 2, 4)` into a dirty 64-bit register `0xDEAD_BEEF_CAFE_BABE#64` (preserving the uninitialized padding byte `0xBA` at offset `1`) and extracting via `Zext` or `Sext` recovers every field identically (`0x0000_0000_0000_00F7#64` under `Zext`, `0xFFFF_FFFF_FFFF_FFF7#64` under `Sext`, `0xFFFF_FFFF_FFFF_8001#64` for `0x8001` under `Sext`, and `0x0000_0000_1122_3344#64` for offset `4`).

#### 1.2 Sub-32-Bit Stack Slot Packing: Apple Darwin ARM64 (`DarwinPCS`) vs. Linux/Windows AAPCS64

Across our 8-target probe (`abi_stack_sub32_ext` in [support/verify_bitlane_and_valist_abi.py](support/verify_bitlane_and_valist_abi.py) and [support/bitlane_valist_oracle_results.json](support/bitlane_valist_oracle_results.json)), once `x0..x7` (`%rdi..%r9` on System V AMD64) are exhausted by 8 fixed integer parameters, stack parameters `(s_u8: u8, s_i16: i16, s_u32: u32, s_u64: u64)` exhibit a sharp target divergence:

| Target | LLVM IR Stack Parameter Attributes (`s_u8, s_i16, s_u32`) | Stack Slot Allocation & Byte Offsets from `sp` |
| :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `i8 noundef zeroext, i16 noundef signext, i32 noundef` | 8-byte slots: `sp+0` (`u8`), `sp+8` (`i16`), `sp+16` (`u32`), `sp+24` (`u64`) |
| `aarch64-unknown-linux-gnu` | `i8 noundef, i16 noundef, i32 noundef` | 8-byte slots: `sp+0` (`u8`), `sp+8` (`i16`), `sp+16` (`u32`), `sp+24` (`u64`) (callee extends) |
| `aarch64-pc-windows-msvc` | `i8 noundef, i16 noundef, i32 noundef` | 8-byte slots: `sp+0` (`u8`), `sp+8` (`i16`), `sp+16` (`u32`), `sp+24` (`u64`) |
| `aarch64-apple-darwin` | `i8 noundef zeroext, i16 noundef signext, i32 noundef` | **Tight natural-alignment packing:** `sp+0` (`u8`), `sp+2` (`i16`, 1B pad at `sp+1`), `sp+4` (`u32`), `sp+8` (`u64`) |
| `x86_64-pc-windows-msvc` / `gnu` | `i8 noundef zeroext, i16 noundef signext, i32 noundef` | 8-byte slots above 32-byte shadow space (`sp+32 + 8*k`) |
| `i686-unknown-linux-gnu` / `msvc` | `i8 noundef zeroext, i16 noundef signext, i32 noundef` | 4-byte cdecl stack slots (`esp+4 + 4*k`) |

Theorem `darwin_compact_stack_pack_unpack_id` in [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean) proves that `marshalDarwinCompactStack` packs `(u8, i16, u32)` into a single 8-byte stack doubleword `[sp .. sp+7]` while preserving the uninitialized padding byte at `sp + 1`.

### 2. Concrete `BitVec 128` HFA Vector-Lane Marshaling (`v0..v3` vs. Packed `xmm0..xmm1`)

For `#[repr(C)] struct HfaF32x4 { a: f32, b: f32, c: f32, d: f32 }` (`16 B`) and `#[repr(C)] struct SubF16F32 { a: f16, b: f16, c: f32 }` (`8 B`), `rustc 1.99.1` lowers `FnAbi` across the 8 Tier 1 targets into four distinct register/memory representations ([support/bitlane_valist_oracle_results.json](support/bitlane_valist_oracle_results.json)):

| Target | `SubF16F32` (`{f16, f16, f32}`) LLVM IR Signature | `HfaF32x4` (`{f32, f32, f32, f32}`) LLVM IR Signature | Physical Vector / GPR Lanes Used |
| :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `define noundef float @...(double %0)` | `define { <2 x float>, <2 x float> } @...(<2 x float> %0, <2 x float> %1)` | Packed 64-bit low halves of `xmm0[63:0]` (`{a,b}`) and `xmm1[63:0]` (`{c,d}`); bits `[127:64]` untouched |
| `aarch64-unknown-linux-gnu` | `define noundef float @...(i64 %0)` | `define [4 x float] @...([4 x float] %0)` | `SubF16F32` in GPR `x0` (`f16`+`f32` mixed is not an HFA); `HfaF32x4` in `s0, s1, s2, s3` (`v0.s[0]..v3.s[0]`) |
| `aarch64-apple-darwin` | `define noundef float @...(i64 %0)` | `define [4 x float] @...([4 x float] %0)` | `SubF16F32` in GPR `x0`; `HfaF32x4` in `v0.s[0]..v3.s[0]` (`[127:32]` untouched) |
| `aarch64-pc-windows-msvc` | `define noundef float @...(i64 %0)` | `define [4 x float] @...([4 x float] %0)` | `SubF16F32` in GPR `x0`; `HfaF32x4` in `v0.s[0]..v3.s[0]` |
| `x86_64-pc-windows-msvc` / `gnu` | `define noundef float @...(i64 %0)` | `define void @...(ptr sret([16 x i8]) %_0, ptr %h)` | `extern "C"` passes `8 B` in GPR `%rcx` and `16 B` by indirect pointer (`vectorcall` uses `xmm0..xmm3`) |
| `i686-unknown-linux-gnu` / `msvc` | `define noundef float @...(ptr byval([8 x i8]) %s)` | `define void @...(ptr sret([16 x i8]) %_0, ptr byval([16 x i8]) %h)` | Passed on stack via `byval`; `sret` pointer for `16 B` return |

Notice the subtle mixed-precision rule verified empirically in `abi_sub_f16_f32_lane`: on System V AMD64 (`x86_64-unknown-linux-gnu`), `{a: f16, b: f16, c: f32}` has three floating-point fields in one eightbyte and is classified as `SSE` (`double %0` in `xmm0[63:0]`), whereas on AAPCS64 (`aarch64-*`), an HFA requires all fundamental members to have the *identical* floating-point type (`f16` vs. `f32` fails homogeneity), so `SubF16F32` is passed as an integer eightbyte (`i64 %0` in `x0`)!

Theorem `decode_encode_hfa_lanes_id` in [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean) models `Vec128Reg` (`s0, s1, s2, s3 : BitVec 32`) and proves that both `decodeHfa4SysV64 ∘ encodeHfa4SysV64` (`2 × 64-bit` packed low halves in `xmm[base]..xmm[base+1]`) and `decodeHfa4Aapcs64 ∘ encodeHfa4Aapcs64` (`4 × 32-bit` separate `v[base].s[0]..v[base+3].s[0]` lanes) recover `v : HfaF32x4` identically regardless of arbitrary caller bits in `s2..s3` (`[127:64]`) or `s1..s3` (`[127:32]`).

### 3. C FFI Bitfield Storage-Unit Divergence (SysV vs. MSVC) and `#[repr(C, packed(1))]` Slicing

When `Verified Rust` interoperates with C headers containing bitfields or unaligned `#[repr(C, packed(N))]` structs, two distinct layout rules apply across the 8 Tier 1 targets:

1. **SysV vs. MSVC Bitfield Storage-Unit Allocation (`layoutCBitfields`):**
   We probed `clang 19.1.7 -O2 -emit-llvm` across all 8 targets on three C bitfield structs (`MixedBF { uint32_t a : 3; uint16_t b : 5; }`, `SameTypeBF { uint32_t a : 3; uint32_t b : 5; uint32_t c : 24; }`, and `StraddleBF { uint32_t a : 20; uint32_t b : 20; }`):
   - On all four non-Windows targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-apple-darwin`), `MixedBF` packs `a : 3` and `b : 5` into a **single 4-byte storage unit** (`sizeof(struct MixedBF) == 4`, `bitOffset(a) = 0`, `bitOffset(b) = 3`), and `bf_extract_mixed` takes `i32 %0` on `x86_64-unknown-linux-gnu`.
   - On all four Windows targets (`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc` — since MinGW defaults to `-mms-bitfields`), changing the declared underlying integer type from `uint32_t` (`4 B`) to `uint16_t` (`2 B`) **forces allocation of a new storage unit** at byte offset `4`, yielding `sizeof(struct MixedBF) == 8` (`bitOffset(a) = 0`, `byteOffset(b) = 4, bitOffset(b) = 0`)!
   - Theorem `sysv_vs_msvc_mixed_bitfield_divergence` in [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean) proves `layoutCBitfields false decls = ([(0, 0, 3), (0, 3, 5)], 4)` and `layoutCBitfields true decls = ([(0, 0, 3), (4, 0, 5)], 8)`.
2. **Unaligned `#[repr(C, packed(1))]` Cross-Eightbyte Structs (`Packed10 { tag: u8, word: u64, tail: u8 }`, `10 B`):**
   - On `x86_64-unknown-linux-gnu`, `word: u64` at byte offset `1` straddles the 8-byte boundary between eightbyte 0 (`[0..8)`) and eightbyte 1 (`[8..10)`). Under System V AMD64 §3.2.3 aggregate classification, an unaligned field that crosses an eightbyte boundary forces the entire aggregate to class `MEMORY`, so `rustc` lowers `abi_packed10_sum` to `ptr byval([10 x i8]) align 1`.
   - On `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and `aarch64-pc-windows-msvc`, AAPCS64 classifies any composite `≤ 16 B` that is not an HFA/HVA as a contiguous byte block copied into two 64-bit GPRs (`[2 x i64] %0` in `x0, x1`), where `word` is reconstructed inside the callee by shifting `x0 >> 8` and ORing `(x1 & 0xFF) << 56`! Both live harnesses (`X86_64_LIVE_OK` and `AARCH64_LIVE_OK`) execute `abi_packed10_sum` across the C-to-Rust boundary and verify `0x010203040506073b`.

### 4. Mechanized C-Variadic (`core::ffi::VaList`) State Machines Across All 4 Tier 1 Layouts

In [support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean) (§5), we formalize all four Tier 1 `va_list` (`core::ffi::VaListImpl`) state machines and prove their `va_arg` extraction soundness theorems:

| `va_list` Layout Family | Targets | Size / Alignment | State Fields & Stepping Invariant | Lean 4 Soundness Theorem |
| :--- | :--- | :--- | :--- | :--- |
| **System V AMD64 `__va_list_tag`** | `x86_64-unknown-linux-gnu` | `24 B` (`align 8`) | `gp_offset` (`0..48` in `8 B` steps for `%rdi..%r9`), `fp_offset` (`48..176` in `16 B` steps for `%xmm0..%xmm7`), `overflow_arg_area`, `reg_save_area`. **2-eightbyte all-or-nothing rule:** a `16 B` struct (`Pair64`) requires `gp_offset <= 32`; if `gp_offset == 40` (5 fixed GPRs used, `%r9` free), `Pair64` is read from `overflow_arg_area` and `gp_offset` stays `40` so a subsequent `u64` `va_arg` backfills from `%r9`! | `va_arg_extract_sound_sysv64` (verified live in `c_va_straddle_pair_then_scalar`) |
| **AAPCS64 Linux `__va_list`** | `aarch64-unknown-linux-gnu` | `32 B` (`align 8`) | `__stack`, `__gr_top`, `__vr_top`, negative `__gr_offs` (`-((8 - fixed_gprs)*8)`), negative `__vr_offs` (`-((8 - fixed_vrs)*16)`). **Even-register `u128` alignment:** `vaArgAapcs64U128` aligns `__gr_offs` up to a multiple of `16` (`-56` at `x1` $\to$ `-48` at `x2:x3`, skipping `x1`), and `vaArgAapcs64Hfa4` steps `__vr_offs` by `+64` (`v0.s[0]..v3.s[0]`). | `va_arg_extract_sound_aapcs64` (verified live in `aarch64_va_u128_and_hfa4`) |
| **Windows `char*` Home-Space `va_list`** | `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, `i686-*` | `8 B` / `4 B` pointer | Caller mirrors variadic floats into both `xmmN` and GPR (`rcx/rdx/r8/r9`), callee spills variadic GPRs into contiguous 32-byte shadow home space `[rsp+8 .. rsp+32]` immediately below stack slot 4; `vaArgWin64Slot` steps linearly by `+8 B` (`+4 B` on `i686`). | `va_arg_extract_sound_win64` |
| **Apple Darwin ARM64 `char*` `va_list`** | `aarch64-apple-darwin` | `8 B` pointer | Fixed arguments use `x0..x7` / `v0..v7` (or compact stack), whereas **all** variadic `...` arguments are placed on the stack at 8-byte aligned slots starting at `varargsStackBase`, never in `x0..x7` or `v0..v7`. | `va_arg_extract_sound_darwin64` |

## Boundaries

1. **x87 80-bit `long double` (`f80`) and 128-bit `fp128` (`_Float128` / `f128`) register classes:** This report mechanizes 8/16/32/64-bit integer sub-lanes, `f16`/`f32`/`f64` scalar and Homogeneous Floating-Point Aggregate (HFA) lanes in 128-bit XMM/NEON registers (`Vec128Reg`), and 128-bit integer pairs (`u128` / `i128`). Legacy x87 `ST(0)` stack returns (`PassMode::Direct` on `i686` for C `float`/`double` when SSE2 return is not used by `extern "C"`) and soft-float/XMM `f128` ABI transitions remain outside the `Vec128Reg` model.
2. **Dynamic `alloca` (`PassMode::Indirect { on_stack: true }` with non-constant size):** Unsized or dynamically sized stack arguments are rejected by `Verified Rust` compilation; all `byval([N x i8])` and indirect shadow-copy marshaling proofs operate on statically bounded `N : Nat` byte sizes.
3. **`aarch64-pc-windows-msvc` C++ non-trivial aggregate return (`x1` vs. `x8` sret):** All results in this report apply to `#[repr(C)]` plain-old-data (`Copy`) structs and C-variadic functions; C++ non-trivial destructor aggregate ABI conventions are out of scope.

## Evidence

- **Lean 4 mechanization ([support/ConcreteBitVecFnAbiRefinement.lean](support/ConcreteBitVecFnAbiRefinement.lean)):** `542` total lines (`475` non-comment code lines), `9` theorems (`extractBitsZext_packBits_same`, `extractBitsSext_packBits_same`, `extractBitsZext_packBits_disjoint`, `unpack_pack_eightbyte_three_fields_id`, `unpack_pack_eightbyte_bitvec_id`, `darwin_compact_stack_pack_unpack_id`, `decode_encode_hfa_lanes_id`, `sysv_vs_msvc_mixed_bitfield_divergence`, `va_arg_extract_sound_sysv64`, `va_arg_extract_sound_aapcs64`, `va_arg_extract_sound_win64`, `va_arg_extract_sound_darwin64`), `0` `sorry`, `0` `native_decide`, `#eval checkAllM5 = true`, verified in `6,071.81 ms` using `anneal-lean-run`.
- **8-target + live execution harness ([support/verify_bitlane_and_valist_abi.py](support/verify_bitlane_and_valist_abi.py) and [support/bitlane_valist_oracle_results.json](support/bitlane_valist_oracle_results.json)):** Verifies all `8` Tier 1 targets and executes live C-to-Rust tests on `x86_64-unknown-linux-gnu` (`X86_64_LIVE_OK`) and `aarch64-unknown-linux-gnu` (`AARCH64_LIVE_OK`).

## Revalidation

```bash
python3 support/verify_bitlane_and_valist_abi.py
```
