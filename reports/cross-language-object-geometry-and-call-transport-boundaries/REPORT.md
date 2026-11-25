# Cross-Language Object Geometry vs. Call-Transport Boundaries: Itanium `dsize`, Sub-Byte Storage Units, Runtime Parameters, and Non-Compositionality

## Summary

Formalizing object layout and call-ABI transport across Rust, C, C++, and LLVM (`geometry(T, σ)` vs. `call(S)`) requires separating properties of standalone objects from contextual subobject, storage-unit, runtime-scalable, and register-classification rules that `(size, align)` pairs cannot capture. Cross-checking normative specifications (`Itanium C++ ABI@2837827a`, `ARM AAPCS64@353c2f24`, `LLVM LangRef`, `rust-lang/reference@956d1bd0`) against `rustc 1.102.0-nightly` (`3ef0c22cd`), `g++ 15.2.0`, and `clang++-19` (`19.1.7`) establishes four boundary results:

1. **C++ `dsize` tail-padding reuse depends on C++03-POD status (`Itanium §2.2–2.4`) and `[[no_unique_address]]`:**
   - Executing `-std=c++23` probes on both `g++ 15.2.0` and `clang++-19` shows identical layout divergence: a C++03-non-POD class `NonPodSubobj { int a; char b; ~NonPodSubobj() {} }` (`sizeof = 8`, `dsize = 5`) permits both derived classes (`DerivedFromNonPod : NonPodSubobj { char c; }` -> `c_off = 5, sizeof = 8`) and `[[no_unique_address]]` members (`ComposedNonPodNoUniq` -> `c_off = 5, sizeof = 8`) to allocate subsequent fields inside its 3-byte tail padding. By contrast, a C++03-POD struct `PodSubobj { int a; char b; }` (`sizeof = 8`) prevents tail-padding reuse even with `[[no_unique_address]]` (`ComposedPodNoUniq` -> `c_off = 8, sizeof = 12`) because Itanium C++ ABI keeps `dsize == sizeof` for C++03 TC1 PODs; empty members still collapse under `[[no_unique_address]]` (`WithEmptyNoAttr b_off = 8, sizeof = 12` vs. `WithEmptyNoUniq b_off = 4, sizeof = 8`).
   - Meanwhile, hidden compiler metadata (`vptr`, multiple-inheritance base offsets such as `Multi` `Base2_ptr_off = 16`, Itanium VTTs, array `operator new` cookies, initialization guard variables, MSVC `/vd` `vtordisp`, and `/vmb`/`/vmg` representation-dependent member pointers) and non-trivial-for-calls rules (`pass_ntc(NonTrivialCopy)` lowered by `clang++-19` to indirect `ptr` despite `sizeof == 8`, defaulted move constructor, and defaulted trivial destructor) violate value-copyable standalone geometry assumptions.
2. **Sub-byte bitfield storage units vs. addressable byte boundaries:** In ISO C/C++ (executed identically on `g++ 15.2.0` and `clang++-19`), adjacent bitfields share addressable allocation units (`BfContig { unsigned a:8; unsigned b:8; }` -> `sizeof = 4`; `BfBool { bool a:1; bool b:1; }` -> `sizeof = 1`), overflow straddling units (`BfSplit { unsigned a:17; unsigned b:16; }` -> `sizeof = 8`), and force new allocation units at zero-width declarations (`BfZeroBreak { unsigned a:8; unsigned :0; unsigned b:8; }` -> `sizeof = 8`). Rust's type model has no bitfields (`RFC #3113` unmerged), treating every field offset as byte-granular.
3. **Runtime-parametric geometry (`σ`) and non-integral pointer barriers (`LLVM LangRef`, `AAPCS64`):**
   - Geometry is not always a static constant: dynamically sized types (`slice` element count `n` and `dyn Trait` vtable lookups) parameterize size/alignment by dynamic pointer metadata `σ`, while Arm AAPCS64 scalable SVE/SME types (`z0..z31`, `p0..p15`) depend on the dynamic hardware vector granule `VG` (`vscale`, lowering `#[rustc_scalable_vector(4)]` to `<vscale x 4 x i32>` in `rustc`).
   - LLVM `LangRef` non-integral pointer types (marked via target `datalayout` `ni:`) hold non-address metadata or external capability state and explicitly forbid `ptrtoint`/`inttoptr` instructions, blocking integer-byte round-tripping models.
4. **Four non-compositionality traps between `geometry(T, σ)` and `call(S)`:**
   - Equal `(size, align)` never suffices to equate either subobject geometry or call ABI: `UnsafeCell<T>` disables niches (`NicheOptimizations::Disabled`) and `readonly`/`noalias` call attributes; `MaybeUninit<T>` erases validity via `to_union()` yet retains `FieldsShape::Union` differences and boolean extension mismatches; `#[repr(C)]` sets `ABI_UNOPTIMIZABLE` to block single-field scalar unboxing even on 1-field wrappers; and function-pointer/trait compatibility requires full `FnAbi` equivalence (`PassMode` + `ArgAttributes` + `ArgExtension`), not bit-size identity.

## Applicability

- **Examined subjects (`REPORT.json`):** `itanium-cxx-abi/cxx-abi@2837827a025f43d1fcfc37ec053d1314cfd1bba3`, `ARM-software/abi-aa@353c2f249a16e6d42e9dae15e78ea148dc6e5349` (`aapcs64/aapcs64.rst`), `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rust-lang/reference@956d1bd03d2a8934fc5041ecb04b33e55159c655`, `LLVM LangRef` (observed `2026-11-25`, LLVM 23 documentation; no repository SHA published on the static HTML artifact), `g++` (`Debian 15.2.0-14`, `15.2.0`), and `clang++-19` (`19.1.7`).
- **Scope and relation to existing corpus packages:** This report synthesizes cross-language geometry-vs.-call boundary conditions for C++, C, LLVM, AAPCS64, and Rust without duplicating existing single-subsystem reports:
  - [`repr-c-layout-algebra-dst-tails-and-enum-tags`](../repr-c-layout-algebra-dst-tails-and-enum-tags/REPORT.md) (`#[repr(C, Int)]` vs. `#[repr(Int)]` layout algebra and flat slice-DST layout);
  - [`rust-cpp-ffi-abi-soundness-improper-ctypes-setjmp-errno-and-init-array`](../rust-cpp-ffi-abi-soundness-improper-ctypes-setjmp-errno-and-init-array/REPORT.md) (Itanium non-trivial copy/move C++ ABI, SSO moves, member pointers, exceptions, `.init_array`, and `improper_ctypes`);
  - [`rustc-track-caller-implicit-location-abi-and-reify-shim-semantics`](../rustc-track-caller-implicit-location-abi-and-reify-shim-semantics/REPORT.md) (`#[track_caller]` implicit `&Location` argument and `ReifyShim`);
  - [`rustc-scalable-vectors-sve-stack-smashing-next-solver-wf-bypass-and-riscv-ice`](../rustc-scalable-vectors-sve-stack-smashing-next-solver-wf-bypass-and-riscv-ice/REPORT.md) (`#[rustc_scalable_vector]` `vscale=1` layout bugs and SVE stack overflow);
  - [`rustc-abi-repr-rust-vs-repr-c-layout-zst-packed-align-and-e0588-retirement`](../rustc-abi-repr-rust-vs-repr-c-layout-zst-packed-align-and-e0588-retirement/REPORT.md) (`LayoutCalculator` struct reordering and ZST alignment).

## Findings

### 1. C++ Subobject Geometry (`dsize` vs. `sizeof`, `is_pod_for_layout`) and Hidden ABI State

**Basis:** `normative` (`itanium-cxx-abi/cxx-abi@2837827a`) + `documentation` (MSVC `/vd`, `/vmb`/`/vmg`) + `execution` (`support/probe_cross_lang_geometry_boundaries.py`)

Under Itanium C++ ABI §2.2 and §2.4 (`itanium-cxx-abi/cxx-abi@2837827a`), every class carries four layout quantities—`sizeof(C)` (full object footprint), `dsize(C)` (data size excluding tail padding), `nvsize(C)` / `nvalign(C)` (non-virtual base size/alignment)—and distinguishes potentially overlapping subobjects (base subobjects and `[[no_unique_address]]` members). Critically, Itanium §2.2 pins `POD for the purpose of layout` to **ISO C++ 2003 TC1**, freezing `dsize(P) = sizeof(P)` whenever `P` is C++03-POD (preventing tail-padding reuse so `memcpy` over a POD remains safe across C++ standard revisions), while allowing tail-padding reuse on non-POD classes:

| C++ Struct / Class (`-std=c++23`) | `g++ 15.2.0` (`x86_64`) | `clang++-19` (`x86_64`) | Geometry Rule Exercised |
| :--- | :--- | :--- | :--- |
| `Empty {}` | `sizeof=1, alignof=1` | `sizeof=1, alignof=1` | Standalone non-zero empty class addressability |
| `WithEmptyNoAttr { int a; Empty e; int b; }` | `sizeof=12, b_off=8` | `sizeof=12, b_off=8` | Empty member consumes 1 byte + 3 bytes padding |
| `WithEmptyNoUniq { int a; [[no_unique_address]] Empty e; int b; }` | `sizeof=8, b_off=4` | `sizeof=8, b_off=4` | Potentially-overlapping empty member elides byte storage |
| `ComposedPodNoUniq { [[no_unique_address]] PodSubobj p; char c; }` | `sizeof=12, c_off=8` | `sizeof=12, c_off=8` | `PodSubobj { int a; char b; }` is C++03-POD (`dsize=8`), blocking tail reuse |
| `DerivedFromNonPod : NonPodSubobj { char c; }` | `sizeof=8, c_off=5` | `sizeof=8, c_off=5` | `~NonPodSubobj() {}` makes `dsize=5 < sizeof=8`, packing `c` in tail pad |
| `ComposedNonPodNoUniq { [[no_unique_address]] NonPodSubobj p; char c; }` | `sizeof=8, c_off=5` | `sizeof=8, c_off=5` | `[[no_unique_address]]` reuses non-POD `dsize=5` tail padding |
| `DerivedNonPod` (`vptr` + POD `BaseWithTailPad`) | `sizeof=24, c_off=16` | `sizeof=24, c_off=16` | Virtual table adds hidden 8B `vptr`; POD base tail pad stays protected |
| `Multi : Base1, Base2 { int z; }` (two virtual bases) | `sizeof=32, Base2_ptr_off=16` | `sizeof=32, Base2_ptr_off=16` | `static_cast<Base2*>` requires `this`-pointer offset adjustment (`+16`) |
| `extern "C" long pass_ntc(NonTrivialCopy v)` | *(indirect via caller)* | `i64 @pass_ntc(ptr readonly %0)` | User-defined copy ctor + defaulted trivial move+dtor still forces indirect pass |

In addition to `dsize`/`nvsize` splits, C++ layouts carry invisible ABI artifacts absent from surface field declarations: Itanium VTT tables for virtual base construction, `operator new[]` element-count cookies, static local `__cxa_guard` initialization guards, and MSVC's `/vd0`/`/vd1`/`/vd2` hidden `vtordisp` adjustment fields (compensating `this` offsets during construction/destruction of classes with virtual bases) plus `/vmb` vs. `/vmg` compiler-flag-dependent member-pointer layouts.

### 2. Sub-Byte Addressable Bitfields vs. Byte-Granular Rust Geometry

**Basis:** `normative` (ISO C23 / C++ `[class.bit]`) + `execution` (`support/probe_cross_lang_geometry_boundaries.py`)

Both `g++ 15.2.0` and `clang++-19` `-std=c++23` confirm bit-level packing rules that violate byte-indexed `(offset, size)` struct models:
- Adjacent compatible bitfields share an addressable storage unit (`BfContig { unsigned a:8; unsigned b:8; }` -> `sizeof=4`; `BfBool { bool a:1; bool b:1; }` -> `sizeof=1`).
- Exceeding unit width advances to the next alignment unit (`BfSplit { unsigned a:17; unsigned b:16; }` -> `sizeof=8`).
- Unnamed zero-width bitfields (`: 0;`) forcibly terminate the current allocation unit (`BfZeroBreak { unsigned a:8; unsigned :0; unsigned b:8; }` -> `sizeof=8` despite only 16 value bits).

In Rust, bitfields do not exist (`RFC #3113` unmerged), and `rustc_abi` tracks field offsets strictly in bytes (`Size`); cross-language bitfield FFI relies on raw integer/array backing units matching the C/C++ compiler's allocation-unit width and endian bit numbering (`C2y` / `WG14` clarifications on signedness and exact-width bitfield alignment notwithstanding).

### 3. Parametric Runtime Geometry (`σ`), Non-Integral Pointers, and Contextual Signature Transforms

**Basis:** `normative` (`ARM AAPCS64@353c2f24`, `LLVM LangRef`) + `source` (`rustc 3ef0c22cd`)

Even within a single target triple, object geometry `geometry(T, σ)` and call transport `call(S)` cannot always be resolved to static constants:

1. **Dynamic metadata `σ` and hardware vector length `vscale`:**
   - Rust DSTs (`[T]`, `dyn Trait`) make `size_of_val` and `align_of_val` functions of the thin/vtable metadata `σ`, transmitted in `PassMode::Pair` as `(data_ptr, metadata)`.
   - Arm `AAPCS64` (`353c2f249a`) separates fixed-width NEON vectors from scalable SVE/SME vector types (`z0..z31`, predicates `p0..p15`), whose size in bytes scales with the runtime hardware vector granule `VG` (`vscale`). In `rustc 3ef0c22cd`, `#[rustc_scalable_vector(4)] struct SvI32(i32)` emits `<vscale x 4 x i32>` in AArch64 `+sve` IR while mistakenly advertising static `vscale = 1` size under `Sized` (analyzed in [`rustc-scalable-vectors-sve-stack-smashing-next-solver-wf-bypass-and-riscv-ice`](../rustc-scalable-vectors-sve-stack-smashing-next-solver-wf-bypass-and-riscv-ice/REPORT.md)).
2. **LLVM non-integral pointers:** `LLVM LangRef` (`Data Layout`, `ni:<addrspace>`) designates non-integral pointer address spaces whose bitwise representation carries non-address metadata, unstable encodings, or external hardware state (such as capabilities). LLVM treats `ptrtoint` and `inttoptr` on non-integral pointers as **ill-typed**, meaning abstract geometry/transport models must treat pointer provenance/state distinctly from integer byte sequences on such targets.
3. **Contextual ABI augmentation (`#[track_caller]`):** Contextual attributes outside the surface type `fn(u32) -> u32` alter ABI lowering: `#[track_caller]` appends an implicit `&'static core::panic::Location<'static>` trailing parameter (`dereferenceable(24)` on x86-64) to direct calls and generates a `{shim:reify#0}` wrapper on function-pointer coercion (analyzed in [`rustc-track-caller-implicit-location-abi-and-reify-shim-semantics`](../rustc-track-caller-implicit-location-abi-and-reify-shim-semantics/REPORT.md)).

### 4. Four Non-Compositionality Barriers for Unified Layout and ABI Models

**Basis:** `derived` from Findings §1–§3 + `source` (`rustc_abi`, `rustc_target`)

A compositional formalism separating object geometry `E ⊢ geometry(T, σ) = G` from call transport `E ⊢ call(S) = C` must reject naive `(size, align)` congruence across four seams:

1. **Subobject context sensitivity:** `geometry(T, σ)` as a standalone object (`sizeof`) differs from its embedded geometry as a C++ base/member (`dsize` when non-POD or `[[no_unique_address]]`) and from `UnsafeCell<T>` (`NicheOptimizations::Disabled`, removing outer enum niches and `readonly`/`noalias` call guarantees).
2. **Scalar-validity vs. register-ABI coupling:** `MaybeUninit<T>` preserves `(size, align)` and `FieldsShape::Union` lowers via `to_union()`, yet strips validity (`Scalar::Union`) while creating ABI incompatibilities on `bool`/`0..=1` tags and target float-struct (`mips64` `FieldsShape::Arbitrary`) rules.
3. **Wrapper-flag non-transparency (`#[repr(C)]` vs. `#[repr(transparent)]`):** A single-field `#[repr(C)] struct WrapC(u32)` matches `u32` in `(size, align)`, yet sets `ReprFlags::IS_C` inside `ABI_UNOPTIMIZABLE`—altering `FnAbi` (`sret`/`byval` on `i686`, `i64` container with `range(i64 0, 4294967296)` vs. `i32` on `aarch64`, indirect `repr(C)` ZST on `win64`, and distinct KCFI/CFI type hashes).
4. **Calling-convention soundness (`FnAbi` equivalence vs. memory layout):** Function compatibility depends on full `FnAbi` lowering (`PassMode::{Ignore, Direct, Pair, Cast, Indirect}` + `ArgAttributes` + `ArgExtension` + `#[track_caller]` hidden parameters + cross-language LLVM IR types under LTO), never on `(size, align)` equality of parameter and return types.

## Boundaries

- **Windows MSVC C++ compilation (`not examined locally`):** MSVC `/vd` (`vtordisp`) and `/vmb`/`/vmg` member-pointer layout rules come from Microsoft/LLVM ABI semantics rather than running proprietary MSVC `cl.exe` binaries locally.
- **Bitfield C2y `N3886` edge cases (`unknown` runtime divergence across vendor extensions):** Live execution tested `g++ 15.2.0` and `clang++-19` on `x86_64-unknown-linux-gnu`; packed/over-aligned bitfield storage-unit rules on AIX, Windows MSVC, and embedded ABI targets are `not examined` in this probe.
- **Non-integral pointers (`not executed`):** No CHERI or AMDGPU non-integral pointer target binary was executed; LLVM `LangRef` `ni:` restrictions are cited normatively.

## Evidence

- **Normative specifications and compiler sources:**
  - `itanium-cxx-abi/cxx-abi@2837827a025f43d1fcfc37ec053d1314cfd1bba3:abi.html` (§2.2 POD for layout, §2.4 Non-POD layout, §2.5–§2.8 virtual tables/VTT/cookies/guards, §3.1.1 non-trivial copy/move passing).
  - `ARM-software/abi-aa@353c2f249a16e6d42e9dae15e78ea148dc6e5349:aapcs64/aapcs64.rst` (SVE scalable vector/predicate ABI and `VG` dependency).
  - `https://llvm.org/docs/LangRef.html` (LLVM 23, observed `2026-11-25`: *Data Layout* `ni:` non-integral pointer rules and *Vector Type* scalable vectors).
  - `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `rust-lang/reference@956d1bd03d2a8934fc5041ecb04b33e55159c655`.
- **Observed execution receipts (`2026-11-25`, reproducible via `support/probe_cross_lang_geometry_boundaries.py`):**
  - `g++ 15.2.0` & `clang++-19` `-std=c++23`: `Empty=1/1`, `WithEmptyNoAttr=12/b_off=8`, `WithEmptyNoUniq=8/b_off=4`, `ComposedPodNoUniq=12/c_off=8`, `DerivedFromNonPod=8/c_off=5`, `ComposedNonPodNoUniq=8/c_off=5`, `DerivedNonPod=24/c_off=16`, `Multi=32/Base2_ptr_off=16`, `BfContig=4`, `BfSplit=8`, `BfZeroBreak=8`, `BfBool=1`; `clang++-19` IR `i64 @pass_ntc(ptr nocapture noundef readonly %0)`.
  - `rustc +nightly` (`3ef0c22cd`) SVE `--target=aarch64-unknown-linux-gnu -Ctarget-feature=+sve`: `define <vscale x 4 x i32> @id_sv(<vscale x 4 x i32> returned %x)`.

## Revalidation

Run the standalone revalidation script from this package directory using `g++`, `clang++-19`, and `rustc +nightly`:

```bash
python3 support/probe_cross_lang_geometry_boundaries.py
```

Verify that both C++ compilers print `c_off=5` (`sizeof=8`) for `DerivedFromNonPod` / `ComposedNonPodNoUniq` vs. `c_off=8` (`sizeof=12`) for `ComposedPodNoUniq`, `BfZeroBreak` prints `sizeof=8` vs. `BfContig` `sizeof=4`, `pass_ntc` lowers to a `ptr` parameter in LLVM IR, and SVE emits `<vscale x 4 x i32>`.
