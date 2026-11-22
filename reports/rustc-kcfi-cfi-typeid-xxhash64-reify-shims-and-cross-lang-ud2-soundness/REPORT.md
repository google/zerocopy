# rustc and Clang KCFI type identifiers on x86-64: XXH64 type-id hashing, the `ud2` guard, the reify trampoline, and what one tag per address costs

## Summary

- Under `-Zsanitizer=kcfi` (rustc) and `-fsanitize=kcfi` (Clang) every
  indirectly callable function carries one 32-bit identifier, and every
  indirect call site compares the identifier it expects with the one stored in
  front of the target. The identifier is the low 32 bits of XXH64 with seed 0
  of an Itanium-mangled type-id string `_ZTSF<return><parameters>E`, followed
  by `.normalized` and/or `.generalized` when those options are on. Example:
  `_ZTSFu3u64u3i32E.normalized` hashes to `0x39961622a0fe4f69`, so its
  identifier is `0xa0fe4f69 = 2701021033`.
- On x86-64 the identifier is the immediate of a `movl $id, %eax` placed in a
  16-byte prefix `__cfi_<symbol>` (eleven `0x90` bytes, then `b8 imm32`), so
  the word sits at `entry - 4`. The call site executes
  `movl $-id, %r10d; addl -4(%target), %r10d; je +2; ud2; call/jmp *%target`.
  The addition is zero exactly when the stored word equals the expected one
  (proved for all 32-bit values); a mismatch executes `ud2`, which a Linux
  user process sees as `SIGILL`.
- rustc and Clang build *different* strings for the same C-compatible integer
  signature unless both sides normalise integers: rustc writes fixed-width
  vendor names (`u3u64`, `u3i32`), Clang writes C builtin codes (`m`, `i`).
  A C caller of a Rust `extern "C" fn(i32) -> u64` therefore dies with
  `SIGILL` by default and returns normally with
  `-Zsanitizer-cfi-normalize-integers` plus
  `-fsanitize-cfi-icall-experimental-normalize-integers`. Signatures without
  integers or `char` (pointers to `void`, floats, `bool`) agree without
  normalisation.
- Normalisation does not make every ABI-compatible prototype agree. Clang
  keeps `long *` and `long long *` as distinct substitution candidates even
  though both pointees normalise to `u3i64`; rustc has one `*mut i64`. The C
  type `void (*)(long *, long long *)` and Rust
  `extern "C" fn(*mut i64, *mut i64)` get different normalised identifiers and
  the call dies with `SIGILL`.
- KCFI can store only one identifier per entry address. A trait method needs
  two: one with `Self` erased to `dyn Trait` (what a vtable call expects) and
  one with the concrete `Self` (what a `fn(&T, ..)` pointer call expects).
  rustc resolves this only under KCFI by making `<T as Trait>::method as fn`
  resolve to a separate function, the reify shim (v0 symbol suffix
  `11reify_fnptr`), which carries the concrete-`Self` identifier and jumps
  directly to the method. Non-K CFI instead attaches several type-id strings
  to the one method and creates no shim.
- The same one-identifier rule is violated by LLVM's MergeFunctions pass,
  which rustc runs at `-Copt-level=2` and above: two functions with identical
  LLVM IR but different KCFI identifiers are folded into one entry that keeps
  one identifier. On the executed toolchain a program with no `unsafe` that
  calls `fn(*mut i32, *const i32) -> u32` through a pointer of exactly that
  type dies with `SIGILL`; with `-Zmerge-functions=disabled` or at
  `-Copt-level=1` it returns.
- A passing check does not imply equal types: `fn(isize, bool, usize, f32, i64)`
  and `fn(u8, u64, f64, u16, i8)` have different 64-bit hashes and the same
  32-bit identifier `0xba801ccf`; rustc emits that identifier for both and a
  call of one through the other's type is not trapped.

## Applicability

The findings concern forward-edge checking of indirect calls on
**x86-64 Linux (SysV, LP64, signed `char`)** with these subjects:

| Subject | Role here |
| --- | --- |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | rustc 1.98.0-nightly (nightly-2026-06-01, LLVM 22.1.6). Source read **and** this exact toolchain executed. |
| `rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e` | Head of the default branch on 2026-11-21. **Source read only**; not built or executed. |
| `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` | The `src/llvm-project` submodule of the first rustc revision; source of the x86 lowering and MergeFunctions that produced the Rust-side machine code. |
| `llvm/llvm-project@cd708029e0b2869e80abe31ddb175f7c35361f90` (`llvmorg-19.1.7`) | Clang source; the executed compiler is the Debian build `clang version 19.1.7 (10.1+build1)`. |
| `shepmaster/twox-hash@79168f770e0e870a11c5bb69ec0382547ef04790` (`v1.6.3`) | The `XxHash64` implementation rustc links. |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | A Lean model of a MIR fragment; examined only to locate these mechanisms relative to it. |
| `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Checks the mechanization in `support/`. |

Relationship between the two rustc revisions. Every statement marked
*execution* was observed with `14210df0`. For `bdf712ee` the same files were
compared textually: `kcfi/typeid/mod.rs` differs only in the spelling of the
shim instance (`InstanceKind::ReifyShim(_, Some(ReifyReason::FnPtr))` became
`InstanceKind::Shim(ShimKind::Reify(_, Some(ReifyReason::FnPtr)))`);
`cfi/typeid/mod.rs` is byte-identical; in `encode.rs` the integer, pointer,
reference, `dyn`, ADT and substitution code is unchanged (the differences are
const-generic value encoding, an architecture-dependent `f128` code, and new
type kinds); in `transform.rs` the integer-normalisation and
`#[repr(transparent)]` arms are unchanged apart from comments and the instance transformation was
reorganised into one match per instance kind. Behaviour at `bdf712ee` is
therefore *derived* from source, not observed.

Configuration of the executed builds:

- rustc: `--edition 2021 -Copt-level=2 -Ccodegen-units=1 -Cpanic=abort
  -Csymbol-mangling-version=v0`, plus `-Zsanitizer=kcfi` and, where stated,
  `-Zsanitizer-cfi-normalize-integers`.
- Clang: `-O2 -fsanitize=kcfi`, plus
  `-fsanitize-cfi-icall-experimental-normalize-integers` where stated.
- The Rust standard library is the precompiled one shipped with the nightly.
  It is **not** built with KCFI; rustc accepts the mixture only with
  `-Cunsafe-allow-abi-mismatch=sanitizer[,sanitizer-cfi-normalize-integers]`.
  Every indirect call whose outcome is reported is made by code compiled with
  KCFI in the probe crates or the C harness.
- Machine code was read from the linked executables with `llvm-objdump`
  22.1.6 (the copy in the rustc toolchain). CPU: Intel Xeon, 2.20 GHz.

What extends beyond the observation and why. The hash function and the
`UInt32` guard arithmetic are target-independent facts about strings and
numbers. The prefix layout and guard instruction sequence are specific to
LLVM's x86 backend. The C-side strings depend on the C data model: on a target
where `long` is 32 bits the builtin codes and normalised widths differ.
`-Zsanitizer=cfi` was used only to make rustc print type-id *strings* in LLVM
IR; no CFI-instrumented program was linked or run.

## Findings

### 1. The identifier is XXH64(seed 0) truncated to 32 bits

rustc (`compiler/rustc_sanitizers/src/kcfi/typeid/mod.rs`, both revisions,
lines 23–25 and 54–56):

```rust
let mut hash: XxHash64 = Default::default();
hash.write(itanium_cxx_abi::typeid_for_instance(tcx, instance, options).as_bytes());
hash.finish() as u32
```

`XxHash64` is `twox_hash::XxHash64` (line 11); `Cargo.lock` pins `twox-hash`
1.6.3, whose `Default` is `XxHash64::with_seed(0)` (`src/sixty_four.rs:269-273`).
Clang (`clang/lib/CodeGen/CodeGenModule.cpp:2142-2158`) mangles the canonical
function type, appends `.normalized` when
`SanitizeCfiICallNormalizeIntegers` is set, and returns
`static_cast<uint32_t>(llvm::xxHash64(OutName))`; `llvm::xxHash64` fixes
`uint64_t Seed = 0` (`llvm/lib/Support/xxhash.cpp:103-105`).

Basis: source + execution + derived. The probe implements XXH64 in pure Python
from the algorithm description, checks four reference vectors (the empty
string, `a`, `abc`, and a 39-byte string that exercises the 32-byte stripe
loop), and then finds that for all 358 rustc-emitted and 93 Clang-emitted
functions per mode in its differential set the `!kcfi_type` value in LLVM IR
equals the low 32 bits of that hash of the predicted string.

| Type-id string | XXH64 (seed 0) | Identifier |
| --- | --- | --- |
| `_ZTSFu3u64u3i32E.normalized` | `0x39961622a0fe4f69` | `2701021033` = `0xa0fe4f69` |
| `_ZTSFu3u32S_E.normalized` | `0x56f8788b77d77d34` | `2010610996` = `0x77d77d34` |
| `_ZTSFu3u64u3i32E` | `0x05d9f2dfe4b6c9d7` | `3837184471` = `0xe4b6c9d7` |
| `_ZTSFu3u32S_E` | `0x7203348fa406b3fc` | `2751902716` = `0xa406b3fc` |
| `_ZTSFmiE` | `0xdb839590eb321a32` | `3945929266` = `0xeb321a32` |
| `_ZTSFyiE` | `0x2ceb4821ace0ed9e` | `2900422046` = `0xace0ed9e` |
| `_ZTSFjjE` | `0x1c2cbdbf673a7326` | `1731883814` = `0x673a7326` |

The Lean file defines the same function as a total structural recursion on a
byte list (`xxHash64Seed0`) and the kernel checks each identifier in the table
by reduction (`rfl`), e.g. `kcfi_u64_i32_normalized` and
`kcfi_u32_u32_normalized`.

### 2. How rustc builds the string

Entry point `typeid_for_fnabi`
(`cfi/typeid/itanium_cxx_abi/mod.rs`, lines at `14210df0`): `"_Z"` (32),
`"TS"` (37), `'F'` (40), the encoded return type, the encoded parameters,
`'E'` (94), then `.normalized` (98) if `NORMALIZE_INTEGERS` and `.generalized`
(102) if `GENERALIZE_POINTERS`. Option bits (`cfi/typeid/mod.rs:18-33`):
`GENERALIZE_POINTERS = 1`, `GENERALIZE_REPR_C = 2`, `NORMALIZE_INTEGERS = 4`,
`USE_CONCRETE_SELF = 8`.

Rules that matter for the fragment examined:

- **Skipped arguments.** Parameters whose pass mode is `PassMode::Ignore`
  (zero-sized values on this target) are filtered out (line 71); if nothing
  was pushed the parameter list is the single code `v` (line 79). Execution:
  `fn(Z0, Z0)` with a unit struct `Z0` gets `_ZTSFvvE`, the same string as
  `fn()`.
- **C ABI.** For `CanonAbi::C` the encoder option `GENERALIZE_REPR_C` is
  inserted, otherwise removed (lines 48–55). With it, a `#[repr(C)]` ADT is
  encoded by its bare name `<length><name>` instead of the Rust vendor name
  (`encode.rs:467-483`). Basis: source only; no `#[repr(C)]` ADT was compiled.
- **Type transformation before encoding** (`transform.rs`, `fold_ty`):
  `c_void` becomes `()` (134); a `#[repr(transparent)]` struct is replaced by
  its unique non-zero-sized field, recursively (137–176), or by `()` if it has
  none (179); and with `NORMALIZE_INTEGERS`, `bool` becomes `u8` (83), `char`
  becomes `u32` (93), `isize`/`usize` become the fixed-width integer of the
  target's pointer width (107–126; `i64`/`u64` here).
- **Leaf encodings** (`encode.rs`): `bool` is `b` (343); integers are vendor
  types `u2i8 u3i16 u3i32 u3i64 u4i128 u5isize u2u8 u3u16 u3u32 u3u64 u4u128
  u5usize` (349–360); `f32`/`f64` are `f`/`d`; `char` is `u4char` (383); `()`
  is `v`; `*const T` is `PK<T>`, `*mut T` is `P<T>` (568–580); `&T` is
  `u3refI<T>E` with prefix `U3mut` for `&mut` (554–566); `dyn Trait` is
  `u3dynI<predicates><region>E` (601–610); other ADTs are
  `u<length><path>` where the path contains `C` + a crate disambiguator +
  crate name + item names (634–732).
- **Substitution** (`compress`, lines 49–63): each completed component with a
  dictionary key is looked up; if present it is replaced by `S<seq-id>_`,
  otherwise the key is inserted with index `dict.len()`. `to_seq_id` (746–752)
  yields the empty string for index 0 and upper-case base 36 of `index - 1`
  otherwise: `S_`, `S0_`, `S1_`, … Integers, `char`, pointers, `const`
  pointees, references, ADTs, `dyn` types, predicates and regions are keyed;
  `bool`, floats and `()` are not.
- **Crate disambiguator.** The type-id path uses
  `s<base62(stable_crate_id - 1)>_` (`encode.rs:704,736-742`) while a v0
  symbol uses `s<base62(stable_crate_id - 2)>_` (`rustc_symbol_mangling/src/v0.rs:197-210,855-856,974-979`),
  so the two differ by one in the last base-62 digit. Execution: symbol prefix
  `CskdnFWz4JOn5_10reify_kcfi`, type-id component `CskdnFWz4JOn6_10reify_kcfi`.
  Identifiers of types that mention an ADT or trait therefore depend on the
  crate name and on whatever feeds the stable crate id, including the compiler
  version.

Examples, each equal to the value rustc emitted (execution) and to the value
the Lean model computes (`rust_substitutions`, `rust_pointers`,
`rust_zero_sized_arguments`, `rust_integer_normalisation`,
`rust_transparent_u32`):

| Rust signature | Default | With integer normalisation |
| --- | --- | --- |
| `fn(i32) -> u64` | `_ZTSFu3u64u3i32E` | `_ZTSFu3u64u3i32E.normalized` |
| `fn(TransU32) -> u32`, `#[repr(transparent)] struct TransU32(u32)` | `_ZTSFu3u32S_E` | `_ZTSFu3u32S_E.normalized` |
| `fn(u32, u32, u32) -> u32` | `_ZTSFu3u32S_S_S_E` | same + suffix |
| `fn(i8, u8, i8, u8)` | `_ZTSFvu2i8u2u8S_S0_E` | same + suffix |
| `fn(*const i32, *const i32, i32)` | `_ZTSFvPKu3i32S1_S_E` | same + suffix |
| `fn(*mut i32, *const i32)` | `_ZTSFvPu3i32PKS_E` | same + suffix |
| `fn(bool, char, usize, isize) -> bool` | `_ZTSFbbu4charu5usizeu5isizeE` | `_ZTSFu2u8S_u3u32u3u64u3i64E.normalized` |
| `fn(usize, u64) -> u64` | `_ZTSFu3u64u5usizeS_E` | `_ZTSFu3u64S_S_E.normalized` |
| `fn(*mut c_void, *const c_void)` | `_ZTSFvPvPKvE` | same + suffix |

In `_ZTSFvPKu3i32S1_S_E` the dictionary after the first parameter is
`[i32, const i32, *const i32]`; the second parameter is the whole pointer
(index 2, `S1_`) and the third is `i32` (index 0, `S_`).

### 3. How Clang builds the string for a C prototype

`mangleCanonicalTypeName` emits `_ZTS` and the mangled function type
(`clang/lib/AST/ItaniumMangle.cpp:7306-7317`). Without normalisation the
integer leaves are the Itanium builtin codes (`a c h s t i j l m x y`, `b` for
`_Bool`), and builtins are not substitution candidates. With
`NormalizeIntegers` every integer builtin, including `_Bool` and the `char`
types, is written `u<n>i<bits>` or `u<n>u<bits>` by signedness and size, and
one representative builtin per size and signedness is used as substitution
key (`ItaniumMangle.cpp:3075` onward; e.g. for 64-bit signed:
`mangleSubstitution(BuiltinType::Long)`, `Out << "u3i64"`,
`addSubstitution(BuiltinType::Long)` at 3099–3102). Compound types are
substituted by canonical type identity: `mangleSubstitution(QualType)` keys on
`T.getAsOpaquePtr()` (6758–6767).

| C function pointer type | Default | Normalised |
| --- | --- | --- |
| `uint64_t (*)(int32_t)` with `uint64_t = unsigned long` | `_ZTSFmiE` | `_ZTSFu3u64u3i32E.normalized` |
| same with `unsigned long long` | `_ZTSFyiE` | `_ZTSFu3u64u3i32E.normalized` |
| `uint32_t (*)(uint32_t)` | `_ZTSFjjE` | `_ZTSFu3u32S_E.normalized` |
| `void (*)(long, long long)` | `_ZTSFvlxE` | `_ZTSFvu3i64S_E.normalized` |
| `void (*)(long *, long *)` | `_ZTSFvPlS_E` | `_ZTSFvPu3i64S0_E.normalized` |
| `void (*)(long *, long long *)` | `_ZTSFvPlPxE` | `_ZTSFvPu3i64PS_E.normalized` |
| `void (*)(const char *, const signed char *)` | `_ZTSFvPKcPKaE` | `_ZTSFvPKu2i8PKS_E.normalized` |

Basis: source + execution. All rows are identifiers Clang 19.1.7 emitted for
function definitions or call sites, matched by the Python model; the Lean
model computes the same strings (`clang_u64_i32`, `clang_u32_u32`,
`clang_pointers`).

The last three rows show the limit of normalisation. In
`void (*)(long *, long long *)` the second pointee is a back-reference to the
`u3i64` representative (`S_`), but the pointer itself is a new candidate
(`PS_`), because `long *` and `long long *` are different canonical types.

### 4. Machine encoding on x86-64

Prefix (`llvm/lib/Target/X86/X86AsmPrinter.cpp`, `emitKCFITypeId`; lines
154–190 at `cd708029`, 163–228 at `08c84e69`): a function symbol
`__cfi_<name>` is emitted, then
`emitNops(offsetToAlignment(PrefixBytes, MF.getAlignment()))` with
`PrefixBytes = patchable-function-prefix + 5`, then `MOV32ri` into `EAX` with
immediate `MaskKCFIType(Type)`. `AsmPrinter::emitNops` emits `N` copies of the
target's one-byte no-op. With 16-byte function alignment and no patchable
prefix that is 11 no-ops and a 5-byte move, so the immediate occupies the four
bytes before the entry.

Call site (`llvm/lib/Target/X86/X86MCInstLower.cpp`, `LowerKCFI_CHECK`; lines
898–945 at `cd708029`, 896–943 at `08c84e69`; the function bodies are
identical): `MOV32ri TempReg, -MaskKCFIType(Type)` with `TempReg = R10D`, or
`R11D` when the target is in `R10`; `ADD32rm TempReg, [AddrReg - (PrefixNops + 4)]`;
`JCC_1 COND_E` over a `TRAP`. The source comment gives the reason for the
negation: the full constant is not encoded at the call site, so the call site
does not itself look like a valid prefix.

`MaskKCFIType` (`X86AsmPrinter.cpp:118-131` / `127-140`): if the value equals
`0xFA1E0FF3` (ENDBR64), `0xFB1E0FF3` (ENDBR32) or the negation of either, it
is replaced by `Value + 1`, at the prefix and at the call site alike.

With the `kcfi-arity` module flag the fork at `08c84e69` chooses the
destination register of the prefix move by argument count
(`X86AsmPrinter.cpp:192-228`); this flag was not set in any build here and the
register observed is always `%eax`.

Execution, normalised build, callback `rust_cb_u64_i32` and C caller
`call_u64_i32` (`uint64_t call_u64_i32(cb f, int32_t x) { return f(x); }`):

```text
<__cfi_rust_cb_u64_i32>:  90 90 90 90 90 90 90 90 90 90 90   11 x nop
                          b8 69 4f fe a0                      movl $0xA0FE4F69, %eax
<rust_cb_u64_i32>:        (entry = prefix symbol + 16)

<call_u64_i32>:  48 89 f8              movq %rdi, %rax
                 89 f7                 movl %esi, %edi
                 41 ba 97 b0 01 5f     movl $0x5F01B097, %r10d
                 44 03 50 fc           addl -4(%rax), %r10d
                 74 02                 je   +2
                 0f 0b                 ud2
                 ff e0                 jmpq *%rax
```

`0x5F01B097 + 0xA0FE4F69 = 2^32`. In the default build of the same pair the
prefix holds `0xE4B6C9D7` (rustc's `_ZTSFu3u64u3i32E`) and the call site loads
`0x14CDE5CE` (the negation of Clang's `_ZTSFmiE` = `0xEB321A32`); the sum is
`0xF984AFA5`, non-zero, and the process dies.

Basis: source + execution. The probe decodes these bytes from the linked
binaries rather than assuming them, and checks for every Rust callback that
the prefix is 16 bytes, starts with exactly eleven `0x90`, and that its
immediate equals the `!kcfi_type` value in the LLVM IR of the same build.

Exactness (mechanized, `kcfi_negated_add_zero_iff_hash_eq`): for all
`h m : UInt32`, `(0 - h) + m = 0 ↔ m = h`; the same on naturals,
`((2^32 - h) % 2^32 + m) % 2^32 = 0 ↔ m = h`
(`kcfi_negated_add_zero_iff_hash_eq_nat`). Because of masking the comparison
is between *masked* identifiers (`masked_guard_iff`), and masking is not
injective: `0xFA1E0FF3` and `0xFA1E0FF4` pass each other's check
(`maskKCFIType_not_injective`). None of the identifiers observed here is a
masked value.

### 5. Cross-language calls: what runs and what traps

One C harness and one Rust program, four build configurations, five calls.
Exit status `-4` means the process was killed by `SIGILL`.

| Call (C caller type → Rust callee) | no sanitizer | KCFI, default | KCFI, both normalised | KCFI, only Rust normalised |
| --- | --- | --- | --- | --- |
| `uint64_t (*)(int32_t)` → `extern "C" fn(i32) -> u64` | `U64_OK=1042` | `-4` | `U64_OK=1042` | `-4` |
| `uint32_t (*)(uint32_t)` → `extern "C" fn(TransU32) -> u32` | `TRANS_OK=100` | `-4` | `TRANS_OK=100` | `-4` |
| `uint64_t (*)(int32_t)` → `extern "C" fn(i64) -> u64` (transmuted, wrong type) | returns `2042` | `-4` | `-4` | `-4` |
| `void (*)(long *, long *)` → `extern "C" fn(*mut i64, *mut i64)` | `PTRS_SAME_OK=16` | `-4` | `PTRS_SAME_OK=16` | `-4` |
| `void (*)(long *, long long *)` → same callee | `PTRS_MIXED_OK=16` | `-4` | `-4` | `-4` |

Identifiers (rustc `!kcfi_type` of the callee | Clang `"kcfi"` operand bundle
at the call site):

| Pair | Default | Normalised |
| --- | --- | --- |
| `u64(i32)` | `3837184471` \| `3945929266` | `2701021033` \| `2701021033` |
| `u32(u32)` via transparent wrapper | `2751902716` \| `1731883814` | `2010610996` \| `2010610996` |
| two `i64` pointers, `long *, long *` | `436628713` \| `99822569` | `1309558340` \| `1309558340` |
| two `i64` pointers, `long *, long long *` | `436628713` \| `1246749912` | `1309558340` \| `293747588` |

Basis: execution; strings from sections 2 and 3.

Over the differential set (179 generated Rust signatures, 93 of them with an
ABI-compatible C prototype compiled by Clang) equality of the two compilers'
identifiers coincided with equality of the predicted strings in every case,
and:

- without normalisation, 20 pairs agree and 73 differ; the agreeing pairs are
  exactly those whose signature contains no integer type and no `char`
  (e.g. `void (*)(void *, const void *)` = `_ZTSFvPvPKvE`,
  `void (*)(float, double, _Bool, void *)` = `_ZTSFvfdbPvE`);
- with normalisation on both sides, 89 agree and 4 differ; the four are
  exactly the prototypes in which two *compound* C types differ only by the
  spelling of a same-width integer (`long *` with `long long *`,
  `const char *` with `const signed char *`, `const unsigned long *` with
  `const unsigned long long *`, `long **` with `long long *`).

Mechanized counterparts. `normalized_integer_signatures_agree`: for every
return type and every parameter list consisting of integer types, of any
length and with any repetitions, if each Rust integer has the signedness and
width of the C integer in the same position, the modelled rustc and Clang
encoders return the same normalised string; hence the guard passes
(`normalized_integer_signature_passes_guard`).
`unnormalized_integer_return_never_agrees`: for a function returning an
integer and taking no parameters, none of the 12 × 12 pairings of a Rust
integer type with a C integer type gives equal identifiers.
`ce1_unnormalized_lp64_uint64_c_rust_ffi_triggers_ud2_trap`: the first row of
the table. `ce5_normalized_pointers_to_long_and_long_long_still_trap`: the
last two rows.

### 6. One identifier per address: the reify shim

Why two identifiers are needed. When rustc declares a function under KCFI it
computes one identifier with `kcfi::typeid_for_instance` and attaches it with
`set_kcfi_type_metadata`, under the comment "LLVM KCFI does not support
multiple !kcfi_type attachments" (`rustc_codegen_llvm/src/declare.rs:226-240`
at `14210df0`; 231 onward at `bdf712ee`). For a method that implements a
dyn-compatible trait, `transform_instance` rewrites the instance to a virtual
call on `dyn Trait` unless `USE_CONCRETE_SELF` is set (`transform.rs:378-403`
at `14210df0`; `erase_self` and `transform_impl_method` at `bdf712ee`,
lines 522 and 451–473), so the attached identifier is the self-erased one,
matching what a `dyn` call site computes. A `fn(&Counter, u32) -> u32` call
site computes the identifier of that pointer type, with the concrete `Self`.

Under non-K CFI the same declaration attaches a set of type-id strings: one
per subset of `{GENERALIZE_POINTERS, NORMALIZE_INTEGERS, USE_CONCRETE_SELF}`
(`declare.rs:193-208`), and call sites test membership with `llvm.type.test`
(`builder.rs:1899`). Execution: for

```rust
pub trait Step { fn step(&self, x: u32) -> u32; }
pub struct Counter(pub u32);
impl Step for Counter { fn step(&self, x: u32) -> u32 { self.0.wrapping_add(x) } }
```

in a crate named `reify_kcfi`, `-Zsanitizer=cfi` attaches six distinct strings
to `<Counter as Step>::step`:

```text
_ZTSFu3u32u3refIu3dynIu33NtCskdnFWz4JOn6_10reify_kcfi4Stepu6regionEES_E
_ZTSFu3u32u3refIvES_E.generalized
_ZTSFu3u32u3refIu3dynIu33NtCskdnFWz4JOn6_10reify_kcfi4Stepu6regionEES_E.normalized
_ZTSFu3u32u3refIu36NtCskdnFWz4JOn6_10reify_kcfi7CounterES_E
_ZTSFu3u32u3refIvES_E.normalized.generalized
_ZTSFu3u32u3refIu36NtCskdnFWz4JOn6_10reify_kcfi7CounterES_E.normalized
```

and defines no shim. With `-Zsanitizer=kcfi` the method carries exactly one
identifier, `68117223`, which is the hash of the first string; and a second
function exists:

```text
_RNSNvXCskdnFWz4JOn5_10reify_kcfiNtB4_7CounterNtB4_4Step4step11reify_fnptr   !kcfi_type 1587319811
_RNvXCskdnFWz4JOn5_10reify_kcfiNtB2_7CounterNtB2_4Step4step                  !kcfi_type 68117223
```

`1587319811` is the hash of the fourth string (concrete `Self`). The `dyn`
call site carries `"kcfi"(i32 68117223)` and the function-pointer call site
`"kcfi"(i32 1587319811)`. Without a sanitizer no shim is defined and no
`!kcfi_type` is attached.

How the shim arises. `Instance::resolve_for_fn_ptr` sets
`reason = tcx.sess.is_sanitizer_kcfi_enabled().then_some(ReifyReason::FnPtr)`
and, when KCFI is enabled and the item is a method of a dyn-compatible trait
(or of an impl of one), replaces the resolved instance by a reify shim, with
the comment "If this function could also go in a vtable, we need to
`ReifyShim` it with KCFI because it can only attach one type per function"
(`rustc_middle/src/ty/instance.rs:593-619` at `14210df0`; 692–694 at
`bdf712ee`). `kcfi::typeid_for_instance` inserts `USE_CONCRETE_SELF` for
exactly that instance kind (`kcfi/typeid/mod.rs:49-50`). The shim's MIR is
`build_call_shim(tcx, instance, None, CallKind::Direct(def_id))`
(`rustc_mir_transform/src/shim.rs:96-97`; line 60 at `bdf712ee`): one direct
call to the method with all arguments moved, then return. The v0 mangler
names it `reify_fnptr` (`rustc_symbol_mangling/src/v0.rs:55`).

In the linked executable the shim is a single direct jump:

```text
<__cfi_..4step11reify_fnptr>:  11 x nop ; b8 03 94 9c 5e   movl $0x5E9C9403, %eax   (1587319811)
<..4step11reify_fnptr>:        e9 .. .. .. ..              jmp  <..7CounterNtB2_4Step4step>
<__cfi_..4Step4step>:          11 x nop ; b8 e7 62 0f 04   movl $0x040F62E7, %eax   (68117223)
<..4Step4step>:                89 f0 ; 03 07 ; c3          movl %esi,%eax ; addl (%rdi),%eax ; retq
```

Direct transfers carry no check, so the shim's own call into the method is
not subject to the method's identifier.

Execution of the four ways to pair the two entries with the two call sites:

| Path | no sanitizer | KCFI |
| --- | --- | --- |
| `dyn` call through the real vtable | `DYN_OK=42` | `DYN_OK=42` |
| `fn(&Counter,u32)->u32` call through `<Counter as Step>::step as fn` | `FNPTR_OK=42` | `FNPTR_OK=42` |
| is that fn pointer equal to the vtable slot? | `true` | `false` |
| vtable slot value called as `fn(&Counter,u32)->u32` | `42` | `-4` (SIGILL) |
| fn-pointer value placed in a forged vtable and called through `dyn` | `42` | `-4` (SIGILL) |

Basis: source + execution. The last two rows use `transmute` to cross-wire the
entries; the no-sanitizer column shows that the cross-wiring itself is
functional and that the trap is the KCFI check.

Mechanized counterpart. The model is a code image mapping an address to at
most one entry `(tag, body)`, where a body is either code or a direct jump;
`indirectCall` traps iff `guardPasses expected tag` is false
(`indirectCall_traps_iff`). `reifyFnPtr_trampoline_bridges_vtable_and_fnptr_kcfi`:
for any two distinct identifiers and two distinct addresses, with the method
at one address tagged with the self-erased identifier and a jump-to-method at
the other tagged with the concrete-`Self` identifier, (1) the `dyn` site
calling the method entry returns the method's result, (2) the fn-pointer site
calling the trampoline entry returns the same result, (3) the fn-pointer site
calling the method entry traps, (4) the `dyn` site calling the trampoline
entry traps. `step_trampoline` instantiates it at the two identifiers above,
computed by the kernel from the two strings.
`ce2_omitting_reify_fnptr_trampoline_breaks_either_vtable_or_fnptr_kcfi`: with
a single entry, whatever its one tag is, at least one of the two sites traps.

A side observation from the same build: the KCFI executable, which prints a
`u32` and a `bool` with `println!`, also contains `reify_fnptr` shims for
`<u32 as core::fmt::Display>::fmt` and `<bool as core::fmt::Display>::fmt`,
because `format_args!` takes those trait methods as function pointers.

For another crate disambiguator the two strings change and so do the
identifiers: with `kSCH9d8WqNd` in place of `kdnFWz4JOn6` they hash to
`1701147868` (self-erased) and `551552321` (concrete `Self`)
(`step_ids_other_disambiguator`). This is a computation on strings; which
compiler build assigns that disambiguator was not examined.

### 7. One identifier per address: MergeFunctions

rustc declares every Rust function `unnamed_addr` ("Function addresses in
Rust are never significant, allowing functions to be merged",
`declare.rs:181-187`), enables LLVM's MergeFunctions pass at optimisation
levels 2, 3, `s` and `z` unless the target or `-Zmerge-functions` disables it
(`rustc_codegen_ssa/src/back/write.rs:244-258` at `14210df0`), and the target
default is `MergeFunctions::Aliases` (`rustc_target/src/spec/mod.rs:2910`).
In `MergeFunctions::mergeTwoFunctions`
(`llvm/lib/Transforms/IPO/MergeFunctions.cpp:931-941` at `08c84e69`), when
function `G` duplicates `F` and `G->hasGlobalUnnamedAddr()`, every use of `G`,
including address-taken uses, is replaced by `F`
("If G's address is not significant, replace it entirely"); if `G` must stay
visible it becomes an alias of `F` (`writeAlias`, 827–847). `!kcfi_type` is
copied only when a thunk is written (`copyMetadataIfPresent(G, NewG, "kcfi_type")`,
line 805). The pass's function comparison file
(`llvm/lib/Transforms/Utils/FunctionComparator.cpp`) contains no reference to
`kcfi`. Two functions whose IR is equal and whose KCFI identifiers differ are
therefore merged, and the surviving entry carries one of the two identifiers.

Execution (`support/probe_results.json`, part G). Source, no `unsafe`:

```rust
#[inline(never)] pub fn f_i32(a: *mut i32, b: *const i32) -> u32 { let _ = (a, b); 7 }
#[inline(never)] pub fn f_u8(a: *mut u8, b: *const u8) -> u32 { let _ = (a, b); 7 }
#[inline(never)] fn call_i32(f: fn(*mut i32, *const i32) -> u32) -> u32 { f(std::ptr::null_mut(), std::ptr::null()) }
#[inline(never)] fn call_u8(f: fn(*mut u8, *const u8) -> u32) -> u32 { f(std::ptr::null_mut(), std::ptr::null()) }
// main: "i32" => call_i32(black_box(f_i32)),  "u8" => call_u8(black_box(f_u8))
```

Identifiers: `f_i32` is `_ZTSFu3u32Pu3i32PKS0_E` = `2077473701`; `f_u8` is
`_ZTSFu3u32Pu2u8PKS0_E` = `1133697259`.

| Build | `i32` call | `u8` call | definitions in IR |
| --- | --- | --- | --- |
| no sanitizer, `-Copt-level=2` | `I32_OK=7` | `U8_OK=7` | — |
| KCFI, `-Copt-level=1` | `I32_OK=7` | `U8_OK=7` | both, each with its own id |
| KCFI, `-Copt-level=2` | `-4` (SIGILL) | `U8_OK=7` | only `f_u8` (id `1133697259`); the `call_i32` site still expects `2077473701` |
| KCFI, `-Copt-level=2 -Zmerge-functions=trampolines` | `-4` (SIGILL) | `U8_OK=7` | only `f_u8` |
| KCFI, `-Copt-level=2 -Zmerge-functions=disabled` | `I32_OK=7` | `U8_OK=7` | both, each with its own id |

For exported symbols the fold shows up as aliases. Compiling the 358
generated functions of the differential set (identical bodies) with KCFI at
`-Copt-level=2`, 169 symbols are emitted as aliases and 52 of them share an
entry whose prefix identifier is not the identifier of their own signature;
for example `sig_c_8` (`_ZTSFvPvPKvE`, `574810481`) is an alias of an entry
prefixed with `436628713` (`_ZTSFvPu3i64S0_E`). A C caller using the correct
prototype for such a symbol expects an identifier that is not there.

Basis: source + execution on `14210df0`. For `bdf712ee`: its `write.rs` still
enables the pass from the same option and target default
(`Session::merge_functions`, `rustc_session/src/session.rs:428-430`;
`write.rs:247-252`) and the MergeFunctions code in its LLVM submodule
(`rust-lang/llvm-project@08ec928a5bd1866f4008c8ad216166ca685fd380`,
`MergeFunctions.cpp:812,960-966`) has the same structure, so the behaviour is
*derived* to persist; it was not executed.

Mechanized counterpart:
`ce4_folding_differently_typed_functions_traps_a_type_correct_call`.

### 8. Truncation to 32 bits

The search in the probe enumerates Rust-ABI signatures `fn(p1, …, pn)` with
`n ≤ 5` pairwise distinct parameter types drawn from 14 scalars, in a fixed
order, and stops at the first pair with equal low 32 bits. After 122,485
candidates:

| Signature | Type-id | XXH64 |
| --- | --- | --- |
| `fn(isize, bool, usize, f32, i64)` | `_ZTSFvu5isizebu5usizefu3i64E` | `0xa62274beba801ccf` |
| `fn(u8, u64, f64, u16, i8)` | `_ZTSFvu2u8u3u64du3u16u2i8E` | `0xc41a702dba801ccf` |

rustc emits `!kcfi_type 3128958159` (`0xba801ccf`) for functions of both
types. A function of the first type, transmuted to a pointer of the second
type and called through a site expecting the second type, runs
(`CALLEE_RAN=A`, exit 0); a function of a third, non-colliding type
(`fn(u64, u8)`, id `1601364660`) cast the same way dies with `SIGILL`.

Basis: derived (search) + execution. Mechanized:
`ce3_xxhash64_truncation_collision_boundary` (both strings are outputs of the
modelled encoder, the 64-bit hashes differ, the identifiers are equal) and
`ce3_wrong_signature_call_is_not_trapped`. The count of candidates is
consistent with a birthday bound for 32 bits; it is not a measurement of
collision frequency in real programs.

### 9. Crate-graph gating

`-Zsanitizer` and, under KCFI, `-Zsanitizer-cfi-normalize-integers` are target
modifiers (`rustc_session/src/options.rs:103-131,2600`): a crate compiled with
a value different from a dependency's is rejected. Execution, compiling
`fn main() {}` against the stock standard library:

| Flags | Result |
| --- | --- |
| `-Zsanitizer=kcfi` | error: `` `-Z sanitizer=kcfi` requires `-C panic=abort` `` |
| `-Cpanic=abort -Zsanitizer=kcfi` | error: ``mixing `-Zsanitizer` will cause an ABI mismatch in crate `m` `` (one error per dependency, 20 here) |
| … `-Cunsafe-allow-abi-mismatch=sanitizer` | accepted |
| … `-Zsanitizer-cfi-normalize-integers -Cunsafe-allow-abi-mismatch=sanitizer` | error: ``mixing `-Zsanitizer-cfi-normalize-integers` will cause an ABI mismatch`` |
| … `-Cunsafe-allow-abi-mismatch=sanitizer,sanitizer-cfi-normalize-integers` | accepted |
| … `-Cunsafe-allow-abi-mismatch=sanitizer -Cunsafe-allow-abi-mismatch=sanitizer-cfi-normalize-integers` | error about `-Zsanitizer` again: the second occurrence of the flag replaces the first |
| `-Cpanic=abort -Zsanitizer-cfi-normalize-integers` (no sanitizer) | error: requires `-Zsanitizer=cfi` or `-Zsanitizer=kcfi` |

Basis: source + execution. The gate compares flags between crates; it does not
detect the Rust/C mismatches of section 5, which involve no second Rust crate.

### 10. The mechanization

`support/KcfiXxHash64AndReifyTrampolineSoundness.lean` (Lean 4.34.1, no
imports) contains the definitions and 54 theorems. Checked with kernel type
checking on and warnings as errors, exit status 0. `#print axioms` for every
theorem and the main definitions reports only `propext` and `Quot.sound`, or
no axioms. The file uses neither `Classical.choice` nor compiled evaluation;
identifiers are obtained by reduction checked by the kernel (`rfl`, `decide`,
`decide +kernel`).

What the model is and is not. The encoders `rustTypeId` and `clangTypeId` are
hand-written Lean functions for the fragment of section 2 and 3 (integers,
`bool`, `char`, floats, unit/void, raw pointers, transparent wrappers,
zero-sized arguments). Their link to the compilers is: (a) a separate Python
implementation of the same rules agrees with every identifier rustc and Clang
emitted in the differential set; (b) the Lean functions return the same
strings as that implementation in the 39 encoder evaluations stated in the
file's theorems. The Lean and Python implementations were not compared beyond those
strings. The reference and `dyn` strings of section 6 are taken from rustc's
output and hashed; the model does not derive them.

### 11. Where this sits relative to the Anneal MIR model

At `joshlf/anneal@c131b320`, `trusted/lean/Trusted/MirAst.lean` defines the
MIR fragment that model gives semantics to. `MirTy.unsupported` stands for,
among others, `FnDef`, `FnPtr` and `Dynamic` types (lines 308–321);
`Rvalue.unsupported` stands for, among others, `Cast` (lines 612–628); and the
only call terminator is
`call (callee : DefId) (args : List Operand) (dst : Place) …`, documented as
"direct `FnDef` `TerminatorKind::Call`", with indirect `Call` mapped to
`.unsupported` (lines 780–795).

Derived consequence: a MIR body that creates a function pointer
(`ReifyFnPointer` cast), holds one, calls through one, or makes a `dyn` method
call is outside that fragment. Statements proved in that model therefore
neither rely on nor constrain KCFI identifiers, reify shims, MergeFunctions or
the guard; all of these arise after MIR, in instance resolution, shim
construction, LLVM codegen and machine code. Conversely nothing in this report
is a statement about that model's semantics.

## Boundaries

Not examined:

- Any architecture other than x86-64 (the prefix and guard are x86 lowering),
  any C data model other than LP64 with signed `char`, Windows, kernel
  targets, and FineIBT-style rewriting of the prefix.
- `-Zsanitizer-kcfi-arity`, `patchable-function-prefix`,
  `-Zsanitizer-cfi-generalize-pointers` (its strings appear only in the CFI
  listing of section 6), C variadic functions, C++.
- `#[repr(C)]` ADTs and extern types (`GENERALIZE_REPR_C`), by value or behind
  pointers: source read, nothing compiled.
- Reify shims other than the method-to-fn-pointer case: closures and `Fn`
  trait objects, caller-location shims, `ReifyReason::Vtable`, drop glue,
  `VTableShim`.
- A standard library built with KCFI. All builds link the stock library under
  `-Cunsafe-allow-abi-mismatch`; indirect calls made *inside* that library are
  unchecked and calls from instrumented code into library function pointers
  were not exercised.
- LTO, a linked and executed non-K CFI program, multiple codegen units.
- Whether the MergeFunctions interaction is known to or recorded by the
  upstream projects, and whether ThinLTO or linker identical-code folding
  produce the same effect.

Unknown:

- Behaviour of rustc at `bdf712ee`. The source reading predicts the same
  results, including the MergeFunctions trap; no build of that revision was
  available.
- Which compiler builds assign crate disambiguator `kSCH9d8WqNd` to a crate
  named `reify_kcfi`. The identifiers `1701147868` and `551552321` are what
  the strings with that disambiguator hash to, nothing more.

Known not to apply:

- "Integer normalisation makes every ABI-compatible C prototype match its Rust
  counterpart": false for prototypes that mix same-width integer spellings
  under pointers (section 5).
- "A passing KCFI check means caller and callee types are equal": false by the
  collision of section 8 and by masking (section 4).
- "A type-correct indirect call passes KCFI": false at `-Copt-level=2` on the
  executed toolchain (section 7), and false across languages without
  normalisation (section 5).

Stronger conclusions the evidence does not support:

- The Lean theorems are about the stated definitions. They do not verify
  rustc, Clang, LLVM or twox-hash; agreement with the compilers is empirical
  and limited to the fragment and the cases listed.
- The cross-language agreement theorem covers signatures made only of
  integers. For other types agreement was observed on the generated set, not
  proved.
- The trampoline theorem shows that the two-entry layout satisfies both call
  sites and separates them. It does not show that rustc creates the shim in
  every situation that needs one.
- The collision count is one run of one deterministic enumeration.

## Evidence

All observations were made on 2026-11-22. Line numbers were extracted
mechanically from the fetched files; `support/source_anchors.json` records the
quoted lines and `support/check_source_anchors.py` re-checks them.

Source, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (the 17 files fetched first, covering the sanitizer, codegen, instance, shim,
mangling and session code, are byte-identical to the copies in the toolchain's
`rustc-src` component):

- `compiler/rustc_sanitizers/src/kcfi/typeid/mod.rs`: 11, 16–26, 29–57
  (one-identifier comment at 39; shim test at 49–50).
- `compiler/rustc_sanitizers/src/cfi/typeid/mod.rs`: 11–35.
- `compiler/rustc_sanitizers/src/cfi/typeid/itanium_cxx_abi/mod.rs`: 25–106,
  111–128.
- `…/itanium_cxx_abi/encode.rs`: 49–63 (`compress`), 342–400 (leaves),
  450–493 (ADTs), 554–610 (pointers, `dyn`), 634–732 (names), 736–752.
- `…/itanium_cxx_abi/transform.rs`: 51–227 (`fold_ty`), 305–460
  (`transform_instance`), 486–517.
- `compiler/rustc_codegen_llvm/src/declare.rs`: 173–245;
  `…/builder.rs`: 1861–1955.
- `compiler/rustc_middle/src/ty/instance.rs`: 38–58, 102, 584–627, 629–705.
- `compiler/rustc_mir_transform/src/shim.rs`: 90–97, 811–1000.
- `compiler/rustc_symbol_mangling/src/v0.rs`: 55–56, 197–210, 855–856,
  974–979.
- `compiler/rustc_session/src/options.rs`: 100–160, 2600;
  `…/session.rs`: 1248–1265.
- `compiler/rustc_codegen_ssa/src/back/write.rs`: 235–258;
  `compiler/rustc_target/src/spec/mod.rs`: 2910;
  `…/spec/targets/x86_64_unknown_linux_gnu.rs`: 13–21 (KCFI is a supported
  sanitizer of the host target).
- `Cargo.lock`: `twox-hash` 1.6.3, checksum
  `97fee6b57c6a41524a810daee9286c02d7752c4253064d0b05472833a438f675`.

Source, `rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e`:
`kcfi/typeid/mod.rs` 49–50; `transform.rs` 84, 137–140, 451–473, 510–600;
`encode.rs` 58, 457; `declare.rs` 186, 204, 231–243; `builder.rs` 2144;
`instance.rs` 692–694; `shim.rs` 60; `v0.rs` 55–56; `session.rs` 428–430,
1720; `write.rs` 247–252; `spec/mod.rs` 2835.

Source, `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5`:
`llvm/lib/Target/X86/X86AsmPrinter.cpp` 127–140, 142–159, 163–228;
`llvm/lib/Target/X86/X86MCInstLower.cpp` 896–943;
`llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp` 4418–4422;
`llvm/lib/Support/xxhash.cpp` 103–105;
`llvm/lib/Transforms/IPO/MergeFunctions.cpp` 805, 816–847, 875–961.

Source, `llvm/llvm-project@cd708029e0b2869e80abe31ddb175f7c35361f90`:
`clang/lib/CodeGen/CodeGenModule.cpp` 2142–2158, 2784–2790;
`clang/lib/AST/ItaniumMangle.cpp` 3075–3140, 6758–6767, 7306–7317;
`llvm/lib/Support/xxhash.cpp` 103–105;
`llvm/lib/Target/X86/X86AsmPrinter.cpp` 118–131, 133–150, 154–190;
`llvm/lib/Target/X86/X86MCInstLower.cpp` 898–945.

Source, `shepmaster/twox-hash@79168f770e0e870a11c5bb69ec0382547ef04790`:
`src/sixty_four.rs` 9–13, 269–273.

Source, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
`trusted/lean/Trusted/MirAst.lean` 308–321, 612–628, 780–795.

Revisions were resolved through the GitHub commits API on the observation
date: the two rustc revisions (the second as the default branch head), the
submodule pointer of `src/llvm-project` through the contents API, the tags
`llvmorg-19.1.7`, `v1.6.3` (twox-hash) and `v4.34.1` (Lean).

Execution environment: Linux x86-64; `rustc 1.98.0-nightly (14210df0e
2026-05-31)`, LLVM 22.1.6; `Debian clang version 19.1.7 (10.1+build1)`,
unpacked from the distribution packages `clang-19`, `libclang-cpp19`,
`libllvm19`, `libclang-common-19-dev`, all version `1:19.1.7-10.1+build1`
(sha256 of the four `.deb` files, in that order:
`94d0031a183342903bb58359fc63852f33360d4fe1a837ae4932b692d0e48096`,
`f153300fd379bcc337e5022ec32335ee1f5fdc89f7c4ef5e2ac246eef1ac5f04`,
`90da5b2b48815691c3e04ee6e3295793073129f54e359f5f21f854f56c111b04`,
`f6dd380aa67242e21513c3731c8d19d6bb7fe425836cd7e336dad59fc2f9eab9`);
`llvm-objdump` 22.1.6 from the rustc toolchain; Lean 4.34.1.

Preserved material in `support/`:

- `probe_kcfi_xxhash64_reify_and_ffi.py` — the probe. It contains every
  source program as a string, builds in a temporary directory, and writes one
  JSON document. Parts: A hash vectors; B cross-language builds, executions,
  IR identifiers and decoded machine code; C the reify shim; D the
  differential test of the two encoder models and the alias count under
  MergeFunctions; E the collision; F flag gating; G the MergeFunctions
  executable. It evaluates 48 named checks and exits 0 only if all hold.
- `probe_results.json` — the output of that probe on the environment above
  (all 48 checks hold; two consecutive runs produced identical documents).
- `KcfiXxHash64AndReifyTrampolineSoundness.lean` — the mechanization.
- `lean_check_output.txt` — the `#print axioms` output and exit status of the
  check described under Revalidation.
- `source_anchors.json`, `check_source_anchors.py` — quoted source lines with
  line numbers per pinned revision, and a script that re-fetches and compares.

## Revalidation

Cheapest checks first.

1. **Hash and strings only (seconds, no compilers).** Compute XXH64 with seed
   0 of `_ZTSFu3u64u3i32E.normalized` with any implementation; the low 32 bits
   must be `0xa0fe4f69`. If not, the report's identifier model does not apply.

2. **Mechanization (about 20 s).**

   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/KcfiXxHash64AndReifyTrampolineSoundness.lean
   ```

   with Lean 4.34.1. Expect exit status 0 and axiom lines mentioning only
   `propext` and `Quot.sound`. This checks the theorems about the model; it
   says nothing about a newer compiler.

3. **Source drift (network only).**
   `python3 support/check_source_anchors.py` re-fetches each pinned file and
   reports quoted lines that moved. To assess a newer rustc, diff
   `compiler/rustc_sanitizers/src/` against `14210df0`, and look at four
   places: `kcfi/typeid/mod.rs` (hash, truncation, the shim test),
   `encode.rs::compress` and the integer arm of `encode_ty`,
   `transform.rs::fold_ty`, and `Instance::resolve_for_fn_ptr`.

4. **Full probe (about 20 s with the tools present).**

   ```bash
   RUSTC=rustc CLANG=clang-19 python3 support/probe_kcfi_xxhash64_reify_and_ffi.py --out /tmp/kcfi_probe.json
   ```

   Needs a nightly rustc (the `-Z` flags), Clang 19 or later with
   `-fsanitize=kcfi`, and `llvm-objdump` (taken from the rustc sysroot if the
   `llvm-tools` component is installed). Without root on a Debian-like host
   Clang can be unpacked from the distribution packages:

   ```bash
   mkdir -p /tmp/clang19 && cd /tmp/clang19
   apt-get download clang-19 libclang-cpp19 libllvm19 libclang-common-19-dev
   for d in *.deb; do dpkg-deb -x "$d" root; done
   export LD_LIBRARY_PATH=/tmp/clang19/root/usr/lib/llvm-19/lib:/tmp/clang19/root/usr/lib/x86_64-linux-gnu
   export CLANG=/tmp/clang19/root/usr/lib/llvm-19/bin/clang
   ```

   Reading the result for another toolchain: the checks named `A_*`, `B_*`,
   `D_*`, `E_*` and `F_*` are expected to be stable while the encoders and the
   x86 lowering are unchanged. The identifiers in part C change with the crate
   disambiguator, hence with the compiler version; the checks there compare
   relationships (which string hashes to which emitted identifier), not fixed
   numbers. The `G_*` checks and the alias count in part D record the
   MergeFunctions behaviour; if a newer toolchain makes
   `G_kcfi_O2_default_merging_makes_one_type_correct_call_die_with_SIGILL`
   fail while the other `G_*` checks hold, the interaction of section 7 has
   changed and that section no longer describes it.

5. **Single discriminating experiments**, if the probe cannot be run whole:
   compile the three-line trait example of section 6 with
   `--emit=llvm-ir -Zsanitizer=kcfi -Cpanic=abort
   -Cunsafe-allow-abi-mismatch=sanitizer` and look for a symbol ending in
   `11reify_fnptr` and two different `!kcfi_type` values; compile it with
   `-Zsanitizer=cfi -Clinker-plugin-lto` instead and look for several
   `!type` strings on the method and no such symbol.

A passing probe establishes only what its checks state for the toolchain it
ran with. Nothing here is a substitute for rereading the sources of a compiler
whose `rustc_sanitizers` crate or x86 KCFI lowering has changed.
