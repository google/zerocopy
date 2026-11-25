# By-Value `MaybeUninit<T>` ABI Boundaries, `Primitive::Bool`, MemorySanitizer `noundef` TLS, and LLVM Byte-Type Constraints

## Summary

Contrary to standard-library documentation claiming `core::mem::MaybeUninit<T>` universally shares the function-call ABI of `T`, live `#[rustc_abi(assert_eq)]` checks and `rustc_abi`/`rustc_target` source inspection show that by-value `T` vs. `MaybeUninit<T>` equivalence fails systematically along four independent axes:

1. **Boolean and `[0, 1]` scalar-extension divergence across ABIs and targets (`3ef0c22cd` vs. `2da92876c4`):**
   - At `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (and identical at `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`), testing 18 types across 8 target triples reveals **6 universal `extern "Rust"` incompatibilities** (`bool`, `#[repr(transparent)] struct BoolWrap(bool)`, `enum E2Rust { A, B }`, `#[repr(u8)] enum E2U8 { A = 0, B = 1 }`, `enum OptU8 { None, Some(u8) }`, and `(bool, u8)`) plus 2 target-specific failures (`#[repr(C)] enum E2C { A = 0, B = 1 }` on `thumbv8m.main-none-eabi` and `enum OptF32 { None, Some(f32) }` on `m68k-unknown-linux-gnu`). Under `extern "C"`, `Cast(i16)` masks `(bool, u8)` and `OptU8`, leaving 4 universal failures (`bool`, `BoolWrap`, `E2Rust`, `E2U8`), `E2C` on `thumbv8m`, and two float-struct failures on `mips64-unknown-linux-gnuabi64`.
   - `PR #165481` (`2da92876c4dec47182369f7702c4ebb70ab1a914`) introduces `Primitive::Bool` and separates explicit `#[repr($int)]` and `#[repr(C)]` enums (`E2U8`, `thumbv8m` `E2C`) from `i1 zeroext`, fixing their `MaybeUninit<T>` parity. However, `layout_of_union` still calls `Scalar::to_union()` (not `hide_niches`), which yields `Scalar::Union { value: Primitive::Bool }` where `is_bool() == false`. Consequently, `extern "Rust"`'s `extend_bool` keeps all non-`#[repr($int)]` `0..=1` scalars—`bool`, `BoolWrap`, `E2Rust`, `OptU8`, `(bool, u8)`, and `m68k` `OptF32`—ABI-incompatible with `MaybeUninit<T>`, while `x86_64` `extern "C"` returns (`backend_repr.is_bool()`) and LLVM IR `i1` vs. `i8` remain mismatched.
2. **Target-specific non-boolean divergences (`m68k` `OptF32` and `mips64` `F32x2`/`F64x3`):**
   - On `m68k-unknown-linux-gnu`, `i32:16:32` causes `Integer::for_align(dl, Align(4))` to return `None` (`f32` has 4-byte alignment while `I32` has 2-byte ABI alignment and `I64` has 8-byte size), forcing `OptF32`'s `0..=1` tag down to `min_ity = I8` (`is_bool() == true` / `Primitive::Bool`) and breaking `MaybeUninit<OptF32>` under `extern "Rust"`, while passing on `x86_64` where `OptF32` gets a `u32` tag.
   - On `mips64-unknown-linux-gnuabi64`, `#[repr(C)] struct F32x2(f32, f32)` fails in `classify_ret` (`FieldsShape::Arbitrary` $\mapsto$ floating-point `InReg` register pair vs. `FieldsShape::Union` $\mapsto$ integer `Uniform(i64)`), whereas `F64x3` returns indirectly on both sides and fails in `classify_arg` (`FieldsShape::Arbitrary` $\mapsto$ `prefix: [f64, f64, f64]` vs. `Union` $\mapsto$ `Uniform(i64)`).
3. **Padding preservation vs. ABI extension (`extern "Rust"`/`Miri`) and MSan `noundef` TLS:**
   - Passing `MaybeUninit<(u16, u8)>` with initialized padding (`0xaabbccdd` written via `*mut u32`) to an `#[inline(never)]` identity function under `rustc -O` drops the padding byte (`0x00bbccdd`), while `cargo miri run` rejects `transmute::<MaybeUninit<(u16, u8)>, u32>` as uninitialized-byte UB (with unpadded control `MaybeUninit<(u16, u16)>` returning `0xaabbccdd`). Preserving all 8 bits of `MaybeUninit<bool>` at machine boundaries conflicts with `zeroext i1` C ABI rules unless the by-value `T` $\equiv$ `MaybeUninit<T>` guarantee is narrowed away from `bool` and general aggregates.
   - Compiling with `-Zsanitizer=memory` (`rustc -Copt-level=1`) turns LLVM `noundef` into an observable ABI contract: `take_i32(x: i32)` skips `__msan_param_tls` and `__msan_retval_tls` completely (`movl %edi, %eax; retq`), whereas `take_mu_i32(x: MaybeUninit<i32>)` loads parameter shadow from `%fs:(__msan_param_tls)` and writes return shadow to `%fs:(__msan_retval_tls)`, causing caller/callee shadow mismatches across transmuted function pointers.
4. **LLVM byte-type (`bN`) ABI blocker:** Lowering `MaybeUninit<T>` to LLVM `bN` (under design for sound poison/provenance preservation) inherits integer ABI classification (`iN`), breaking parity with `f64`/HFA on float targets and with `ptr` on pointer-vs-integer register targets (`m68k`, `x32`/ARM64-ILP32, CHERI).

## Applicability

- **Examined compiler revisions (`REPORT.json`):** Primary source inspection and live multi-target execution (`#[rustc_abi(assert_eq)]`, `--emit=llvm-ir`, `--emit=asm`, native execution, and `Miri`) ran on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) on an `x86_64-unknown-linux-gnu` host, cross-checked identically on `rustc 1.102.0-nightly` (`6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`, LLVM `23.1.6`). Post-`3ef0c22cd` `Primitive::Bool` changes (`PR #165481`, `2da92876c4dec47182369f7702c4ebb70ab1a914`) were audited by direct source-diff inspection alongside `tests/ui/abi/compatibility.rs` and `miri/tests/pass/function_calls/abi_compat.rs`; `PR #165481` was not executed locally because both installed nightlies predate `2026-11-23`.
- **Target matrix:** Cross-compiled metadata checks cover 8 targets: `x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`, `aarch64-unknown-linux-gnu`, `thumbv8m.main-none-eabi`, `m68k-unknown-linux-gnu`, `mips64-unknown-linux-gnuabi64`, `bpfeb-unknown-none`, and `wasm32-unknown-unknown`, evaluating both `fn(T) -> T` (`extern "Rust"`) and `extern "C" fn(T) -> T`.
- **Relation to existing corpus packages:** Extends and does not duplicate [`rustc-union-layout-scalar-union-abi-inhabitedness-and-byte-semantics`](../rustc-union-layout-scalar-union-abi-inhabitedness-and-byte-semantics/REPORT.md) (`layout_of_union`, `Scalar::Union`, single-target `noundef`/`range` erasure, and `FieldsShape::Union` padding stripping), [`rustc-abi-repr-transparent-ffi-noundef-range-and-zerocopy-wrapper-inheritance`](../rustc-abi-repr-transparent-ffi-noundef-range-and-zerocopy-wrapper-inheritance/REPORT.md) (wrapper attribute inheritance vs. `MaybeUninit` erasure), and [`scalarpair-register-lowering-refinement-init-uniform-scalars-and-provenance-boundaries`](../scalarpair-register-lowering-refinement-init-uniform-scalars-and-provenance-boundaries/REPORT.md) (formal byte/register round-trip semantics).

## Findings

### 1. Eight-Target `T` vs. `MaybeUninit<T>` `#[rustc_abi(assert_eq)]` Matrix (`extern "Rust"` vs. `extern "C"`)

**Basis:** `source` (`3ef0c22cd`) + `execution` (`support/probe_maybeuninit_abi_matrix.py`)

Testing 18 representative `Copy` types (`i32`, `u8`, `*const ()`, `f64`, `bool`, `BoolWrap`, `E2Rust`, `E2U8`, `E3U8`, `E2C`, `OptU8`, `OptBool`, `(bool, u8)`, `OptF32`, `F32x2`, `F64x3`, `#[repr(C)] Padded(u16, u8)`, and `(u16, u8)`) with `#[rustc_abi(assert_eq)]` comparing `(fn(T) -> T, fn(MaybeUninit<T>) -> MaybeUninit<T>)` separately for `"Rust"` and `"C"` ABIs on `3ef0c22cd` yields:

| Target Triple | `extern "Rust"` Failures (out of 18) | `extern "C"` Failures (out of 18) |
| :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `bool`, `BoolWrap`, `E2Rust`, `E2U8`, `OptU8`, `(bool, u8)` (6) | `bool`, `BoolWrap`, `E2Rust`, `E2U8` (4) |
| `x86_64-pc-windows-msvc` | `bool`, `BoolWrap`, `E2Rust`, `E2U8`, `OptU8`, `(bool, u8)` (6) | `bool`, `BoolWrap`, `E2Rust`, `E2U8` (4) |
| `aarch64-unknown-linux-gnu` | `bool`, `BoolWrap`, `E2Rust`, `E2U8`, `OptU8`, `(bool, u8)` (6) | `bool`, `BoolWrap`, `E2Rust`, `E2U8` (4) |
| `bpfeb-unknown-none` | `bool`, `BoolWrap`, `E2Rust`, `E2U8`, `OptU8`, `(bool, u8)` (6) | `bool`, `BoolWrap`, `E2Rust`, `E2U8` (4) |
| `wasm32-unknown-unknown` | `bool`, `BoolWrap`, `E2Rust`, `E2U8`, `OptU8`, `(bool, u8)` (6) | `bool`, `BoolWrap`, `E2Rust`, `E2U8` (4) |
| `thumbv8m.main-none-eabi` | 6 baseline + `E2C` (7) | 4 baseline + `E2C` (5) |
| `m68k-unknown-linux-gnu` | 6 baseline + `OptF32` (7) | 4 baseline only (`OptF32` passes) (4) |
| `mips64-unknown-linux-gnuabi64` | 6 baseline (6) | 4 baseline + `F32x2`, `F64x3` (6) |

*(An identical matrix run on `6905905bb` matches `3ef0c22cd` cell for cell.)*

Two structural masking behaviors explain why `extern "C"` diverges from `extern "Rust"` on the same target:

1. **Aggregate `PassMode::Cast` erasure of `OptU8` and `(bool, u8)`:** Under `extern "Rust"`, `OptU8` and `(bool, u8)` stay `PassMode::Pair(a_attrs, b_attrs)` where field `a` is `u8 is 0..=1` (`is_bool() == true`), causing `adjust_for_rust_abi`'s `extend_bool` (`compiler/rustc_target/src/callconv/mod.rs:751-771` in `3ef0c22cd`) to attach `ArgExtension::Zext` to `a` for `T` while omitting it for `MaybeUninit<T>` (`Scalar::Union` has `is_bool() == false`). Under `extern "C"`, targets such as `x86_64-unknown-linux-gnu` lower both 2-byte pairs via `PassMode::Cast(i16)` (`define i16 @c_opt_u8(i16 returned %0)` == `define i16 @c_mu_opt_u8(i16 returned %0)`), stripping `ArgExtension::Zext` and passing `#[rustc_abi(assert_eq)]`.
2. **Same-mechanism failure on `OptBool` pass vs. `OptU8` fail:** Unlike `OptU8` (two-variant enum with 1-byte payload -> `ScalarPair`), `enum OptBool { None, Some(bool) }` reserves niche value `2` for `None`, packing into a single byte `u8 is 0..=2` (`is_bool() == false`), so `OptBool` passes `#[rustc_abi(assert_eq)]` everywhere.

### 2. Three Root Mechanisms Behind Target-Specific Failures

**Basis:** `source` (`3ef0c22cd`, `PR #165481`) + `execution`

#### 2.1 Short-Enum Targets (`thumbv8m` `E2C`) and `m68k` `OptF32` via `Integer::for_align`

In `compiler/rustc_abi/src/layout/enum_layout.rs`, tag integer selection chooses `min_ity` when `repr.c() || repr.int.is_some()` and `Integer::for_align(dl, start_align).unwrap_or(min_ity)` otherwise. Whenever an enum has 2 variants with discriminants `0..=1` and receives `I8` (`Scalar::Initialized { value: Primitive::Int(I8, false), valid_range: 0..=1 }`), `is_bool()` evaluates to `true`:

- **`thumbv8m.main-none-eabi` (`E2C`):** Bare Arm EABI enables short C enums (`c_enum_min_size = 1`), giving `#[repr(C)] enum E2C { A = 0, B = 1 }` tag `I8` (`valid_range: 0..=1`, `Direct`), triggering `Zext` / `i1` lowering on `E2C` while `MaybeUninit<E2C>` lowers to `Scalar::Union(I8)`.
- **`m68k-unknown-linux-gnu` (`OptF32`):** The `m68k` target (`compiler/rustc_target/src/spec/targets/m68k_unknown_linux_gnu.rs:19`) sets `i32:16:32` (`I32` ABI align = 2 bytes) while leaving default `f32:32:32` (`f32` align = 4 bytes) and `i64:32:64` (`I64` size = 8 bytes). When laying out `OptF32` (`align = 4`), `Integer::for_align(cx, Align(4))` (`compiler/rustc_abi/src/lib.rs:1344-1350`) checks:
  ```rust
  [I8, I16, I32, I64, I128].into_iter().find(|&candidate| {
      wanted == candidate.align(dl) && wanted.bytes() == candidate.size().bytes()
  })
  ```
  On `x86_64`, `I32` satisfies both conditions (`4 == 4`), selecting `u32 is 0..=1` (`is_bool() == false`), so `fn(OptF32)` passes `#[rustc_abi(assert_eq)]`. On `m68k`, neither `I32` (`align = 2 != 4`) nor `I64` (`size = 8 != 4`) matches, so `for_align` returns `None` and falls back to `min_ity = I8` (`u8 is 0..=1`, `is_bool() == true`). Thus `fn(OptF32)` fails `assert_eq` on `m68k` under `extern "Rust"`, while `extern "C"` passes because `m68k` (`compiler/rustc_target/src/callconv/m68k.rs`) passes `ScalarPair` aggregates indirectly via `PassMode::Indirect`.

#### 2.2 `mips64` Float Struct `FieldsShape::Arbitrary` vs. `FieldsShape::Union` (`F32x2` vs. `F64x3`)

On `mips64-unknown-linux-gnuabi64`, `rustc` (`compiler/rustc_target/src/callconv/mips64.rs`) inspects `layout.fields` separately in return and argument classification, causing `MaybeUninit<T>` (`FieldsShape::Union`) to lose floating-point register placement even though size and alignment match:

- **`F32x2` (`64` bits `<= 128`) diverges in `classify_ret` (`mips64.rs:82-101`):** `classify_ret` grants float-register returns (`CastTarget::pair(f32, f32)` with `ArgAttribute::InReg`) only inside `if let FieldsShape::Arbitrary { .. } = ret.layout.fields` when `count <= 2`. `MaybeUninit<F32x2>` has `FieldsShape::Union`, skipping that branch and falling through to `Uniform::new(Reg::i64(), size)` (integer register `$v0`). Meanwhile `classify_arg` (`mips64.rs:185-230`) only promotes aligned `Float::F64` fields, so `F32x2` arguments already use `Uniform(Reg::i64(), 8)` on both sides.
- **`F64x3` (`192` bits `> 128`) diverges in `classify_arg` (`mips64.rs:185-230`):** Because `bits > 128`, `classify_ret` (`mips64.rs:103`) returns both `F64x3` and `MaybeUninit<F64x3>` indirectly (`ret.make_indirect()`). On arguments, `classify_arg` matches `FieldsShape::Arbitrary` (`mips64.rs:194-223`) and pushes `prefix: [Reg::f64(), Reg::f64(), Reg::f64()]`, whereas `FieldsShape::Union` (`mips64.rs:191-193`) emits empty `prefix` and passes all 24 bytes in integer chunks (`Uniform(Reg::i64(), 24)`).

#### 2.3 What `PR #165481` (`2da92876c4`) Fixes vs. What Remains Broken

`PR #165481` (`2da92876c4dec47182369f7702c4ebb70ab1a914`) introduces an explicit `Primitive::Bool` variant (`Size::from_bits(1)`, `Align::ONE`) separate from `Primitive::Int(I8, false)`:

- **What `PR #165481` fixes:** In `enum_layout.rs:333-342`, `Primitive::Bool` is emitted *only* when `repr.int.is_none() && !repr.c() && matches!(tag_valid_range, WrappingRange { start: 0, end: 1 }) && ity == Integer::I8`. Therefore `#[repr(u8)] enum E2U8 { A = 0, B = 1 }` (`c_e2_u8`) and `thumbv8m` `#[repr(C)] enum E2C { A = 0, B = 1 }` (`c_e2_c`) get `Primitive::Int(I8, false)` instead of `Primitive::Bool`, aligning their ABI with `u8` and `MaybeUninit<T>`.
- **Why `bool`, `E2Rust`, `OptU8`, `(bool, u8)`, and `m68k` `OptF32` stay broken:**
  1. `hide_niches` (`compiler/rustc_abi/src/layout.rs:566-578` in `2da92876c4`) converts `Primitive::Bool` to `Primitive::Int(I8, false)` only for `NicheOptimizations::Disabled` (`UnsafeCell`/`UnsafePinned`). `MaybeUninit<T>` enters `layout_of_union` and calls `Scalar::to_union()` (`compiler/rustc_abi/src/lib.rs:1636-1638, 1975-1993`), producing `Scalar::Union { value: Primitive::Bool }`. Because `Scalar::is_bool()` (`matches!(self, Scalar::Initialized { value: Primitive::Bool, .. })`) is `false` for `Scalar::Union`, all 6 `extern "Rust"` cases (`bool`, `BoolWrap`, `E2Rust`, `OptU8`, `(bool, u8)`, and `m68k` `OptF32`, which still satisfies `repr.int.is_none() && !repr.c() && 0..=1 && ity == I8`) continue failing `extend_bool` (`callconv/mod.rs:805-820`).
  2. Under `extern "C"`, `PR #165481` removes `backend_repr.is_bool() == other.backend_repr.is_bool()` from `LayoutData::eq_abi` (`lib.rs:2502-2506`) and updates `extend_integer_width_to` (`callconv/mod.rs:627-629`) to attach `Zext` for `Primitive::Bool` regardless of `Initialized` vs. `Union`. That makes `#[rustc_abi(assert_eq)]` on `extern "C" fn(bool)` pass on targets calling `extend_integer_width_to(32/64)`, **except** `x86_64-unknown-linux-gnu` where return extension (`compiler/rustc_target/src/callconv/x86_64.rs:301`: `if !is_arg && arg.layout.backend_repr.is_bool() { arg.extend_integer_width_to(8); }`) still checks `is_bool()`. Moreover, `rustc_codegen_llvm` still lowers `immediate_llvm_type` via `scalar.is_bool()` (`i1` for `bool`, `i8` for `MaybeUninit<bool>`), so `src/tools/miri/tests/pass/function_calls/abi_compat.rs:748-749` explicitly comments out `bool` as unresolved (`rust-lang/rust#165800`).

### 3. Padding Byte Preservation, MSan `noundef` TLS Protocol, and LLVM `bN` Constraints

**Basis:** `source` (`3ef0c22cd`, `PR #159317`) + `execution` + `normative` (C ABI `i1` extension rules)

1. **Irreconcilable `zeroext` vs. padding-byte preservation on `bool` and `MaybeUninit<(u16, u8)>`:**
   - Executing `rustc +nightly -O` on passing `x = MaybeUninit::<(u16, u8)>::uninit()` initialized with `write_unaligned(0xaabbccdd)` through `#[inline(never)] unsafe fn id(x: MaybeUninit<(u16, u8)>) -> MaybeUninit<(u16, u8)> { x }` and transmuting the result to `u32` prints **`0x00bbccdd`**: LLVM's `ScalarPair` return `{ i16, i8 }` discards the byte at offset `2` (or upper bits depending on field ordering). Running the identical code under `cargo +nightly miri run` (`miri 0.1.0`) fails (`rc=1`: `Undefined Behavior: constructing invalid value of type u32: encountered uninitialized memory`), while the unpadded control `MaybeUninit<(u16, u16)>` exits `0` printing `0xaabbccdd`.
   - For `bool`, Rust semantics guarantee valid `bool` values are bytes `0x00` or `0x01`, while `MaybeUninit<bool>` can hold arbitrary bytes (`0x02..=0xff` or uninitialized). Zero-extending `bool` (`i1 zeroext` in SysV/Win64/RISC-V/etc., or `rust` ABI `Zext` at `callconv/mod.rs`) signals to LLVM that bits `1..=7` / `8..=31` are zero, whereas `MaybeUninit<bool>` must preserve all 8 byte bits across typed copies (`zeroext` on `MaybeUninit<bool>` would discard bits `1..=7` in `MaybeUninit`).
2. **MemorySanitizer `-Zsanitizer=memory` Makes `noundef` an Observable ABI Contract:**
   - Compiling `take_i32(x: i32) -> i32`, `take_mu_i32(x: MaybeUninit<i32>) -> MaybeUninit<i32>`, and `call_ext` under `rustc +nightly -Copt-level=1 -Zsanitizer=memory --emit=asm` demonstrates how MSan `-fsanitize-memory-param-retval` turns `noundef` into a cross-call TLS protocol:
     * `take_i32` (`define noundef i32 @take_i32(i32 noundef %x)`) emits only `movl %edi, %eax; retq`, reading zero shadow bytes because `noundef` asserts caller-validated initialization.
     * `take_mu_i32` (`define i32 @take_mu_i32(i32 %x)`) loads parameter shadow from `__msan_param_tls@GOTTPOFF(%rip)` (`movl %fs:(%rcx), %ecx`) and stores return shadow into `__msan_retval_tls@GOTTPOFF(%rip)` (`movl %ecx, %fs:(%rdx)`).
     * At call sites in `call_ext`, the call through `fn(i32) -> i32` neither populates `%fs:(__msan_param_tls)` nor reads `%fs:(__msan_retval_tls)` (clearing `%fs:(__msan_retval_tls)` with `movl $0` only for its own next return/use), whereas the call through `fn(MaybeUninit<i32>) -> MaybeUninit<i32>` saves/restores `__msan_param_tls` (`movl %fs:24(%r15), %r12d; ...; movl %r12d, %fs:(%r15)`) and reads `%fs:(__msan_retval_tls)`. Calling across a pointer transmuted between `fn(i32)` and `fn(MaybeUninit<i32>)` under MSan corrupts shadow tracking and induces false-positive uninitialized-memory traps (`rust-lang/rust#165040`).
3. **LLVM Byte Type (`bN`) ABI Blockers:** Using LLVM's proposed `bN` byte type (`b8`, `b64`, `b128`, `<M x bN>`) for `MaybeUninit<T>` preserves provenance and poison without premature bitcasts, but because LLVM lowers `bN` via integer register classes (`iN`), it cannot uphold universal `T` $\equiv$ `MaybeUninit<T>` ABI equivalence for: (a) floating-point scalars (`f32`/`f64`) and HFAs (`[f32; 4]`), which pass in FP/SIMD registers (`xmm`/`s`/`d`) rather than GPRs; and (b) pointers on ABIs distinguishing pointers from integers—specifically `m68k` (address registers `%a0..%a7` vs. data registers `%d0..%d7`), 32-bit-pointer-on-64-bit ABIs (`x86_64-gnux32` and `aarch64_be`/`aarch64-ilp32`, where `X86CallingConv.td`/`AArch64CallingConvention.td` zero-extend pointers separately from 64-bit integers), and capability targets such as CHERI (`b128` vs. integer `i128`).

## Boundaries

- **`PR #165481` execution (`not examined locally`):** Both installed nightlies (`3ef0c22cd` from `2026-11-11` and `6905905bb` from `2026-11-19`) precede `PR #165481` (`2026-11-23`), so post-`2da92876c4` `#[rustc_abi(assert_eq)]` behavior (`E2U8`, `E2C`, and `x86_64` `extern "C"` `bool`) is `derived` by inspecting `2da92876c4` alongside `3ef0c22cd` sources rather than directly executed.
- **Unexamined ABIs and non-`Copy` aggregates:** Only 8 targets (`x86_64` Linux/Windows, `aarch64`, `thumbv8m`, `m68k`, `mips64`, `bpfeb`, `wasm32`) and 18 `Copy` test types were probed; `x87_f80`, `ppcf128`, `loongarch`, `s390x`, and `#[rustc_scalable_vector]` types inside `MaybeUninit<T>` are `not examined` in the probe matrix.
- **Documentation vs. guarantee (`known not to apply` universally):** While `core::mem::MaybeUninit<T>` docs state `MaybeUninit<T>` has the same ABI as `T`, the Rust Reference (`rust-lang/reference@956d1bd0`) makes no global `T` $\equiv$ `MaybeUninit<T>` by-value ABI guarantee (`r[layout.repr.transparent]` applies to `struct` / single-variant `enum`, whereas `MaybeUninit<T>` is a `#[repr(transparent)] union`). Upstream opsem consensus (`rust-lang/unsafe-code-guidelines#518`, `rust-lang/rust#165800`) treats narrowing the ABI promise to integer types (`iN`/`uN`)—and possibly integer vectors, never `bool` or arbitrary aggregates—as necessary if `bN` and strict bit-preservation are retained.

## Evidence

- **Primary compiler sources (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `2da92876c4dec47182369f7702c4ebb70ab1a914`):**
  - `compiler/rustc_target/src/callconv/mod.rs:751-771` (`3ef0c22cd`; `805-820` in `2da92876c4`) — `extend_bool` attaching `Zext` under `is_rustic_abi`; `603-633` (`2da92876c4`) — `extend_integer_width_to` matching `Primitive::Bool`.
  - `compiler/rustc_target/src/callconv/x86_64.rs:301` — `if !is_arg && arg.layout.backend_repr.is_bool() { arg.extend_integer_width_to(8); }`.
  - `compiler/rustc_target/src/callconv/mips64.rs:82-105, 185-230` — `FieldsShape::Arbitrary` vs. `FieldsShape::Union` in `classify_ret` (`F32x2`) and `classify_arg` (`F64x3`).
  - `compiler/rustc_abi/src/lib.rs:1344-1350` (`Integer::for_align`), `1636-1638, 1975-1993` (`to_union`), `2502-2506` (`2da92876c4` `LayoutData::eq_abi`).
  - `compiler/rustc_abi/src/layout.rs:566-581` (`hide_niches`, `2da92876c4`) and `compiler/rustc_abi/src/layout/enum_layout.rs:290-342` (`Primitive::Bool` tag emission, `2da92876c4`).
  - `compiler/rustc_target/src/spec/targets/m68k_unknown_linux_gnu.rs:19` (`i32:16:32`).
  - `compiler/rustc_codegen_llvm/src/type_of.rs:277-302` (`immediate_llvm_type` vs. `scalar_llvm_type_at`).
  - `tests/ui/abi/compatibility.rs` and `src/tools/miri/tests/pass/function_calls/abi_compat.rs:748-749` (`2da92876c4`).
- **Observed execution receipts (`2026-11-25`, reproducible via `support/probe_maybeuninit_abi_matrix.py`):**
  - 8-target × 18-type matrix: identical pass/fail counts on `3ef0c22cd` and `6905905bb` (`extern "Rust"`: 12 pass / 6 fail on `x86_64`/`win64`/`aarch64`/`bpfeb`/`wasm32`, 11/7 on `thumbv8m` and `m68k`, 12/6 on `mips64`; `extern "C"`: 14 pass / 4 fail on 6 targets, 13/5 on `thumbv8m`, 12/6 on `mips64`).
  - MSan `-Zsanitizer=memory -Copt-level=1` assembly on `x86_64-unknown-linux-gnu`: `__msan_param_tls` / `__msan_retval_tls` emitted in `take_mu_i32` / `take_mu_bool` and skipped in `take_i32` / `take_bool`.
  - Padding test: `rustc +nightly -O` prints `0x00bbccdd`; `cargo +nightly miri run` fails with `rc=1` on `MaybeUninit<(u16, u8)>` (`encountered uninitialized memory`) and exits `0` printing `0xaabbccdd` on `MaybeUninit<(u16, u16)>`.

## Revalidation

Run the standalone self-contained probe directly from this report package directory using an installed nightly toolchain supporting `#![feature(no_core, rustc_attrs, lang_items, transparent_unions, auto_traits)]` and `cargo miri`:

```bash
python3 support/probe_maybeuninit_abi_matrix.py
```

When re-running on `rustc` commits containing `PR #165481` (`2da92876c4` or newer), check:
1. Whether `c_e2_u8` and `thumbv8m` `c_e2_c` move from `fail` to `pass`;
2. Whether `c_bool`, `c_bool_wrap`, `c_e2_rust`, `c_opt_u8`, `c_pair_bool_u8`, and `m68k` `c_opt_f32` still fail under `extern "Rust"`, and whether `extern "C"` narrows to `x86_64` `bool`/`BoolWrap`/`E2Rust`;
3. Whether MSan `-Zsanitizer=memory` assembly for `take_i32` vs. `take_mu_i32` still diverges on `__msan_param_tls`.
