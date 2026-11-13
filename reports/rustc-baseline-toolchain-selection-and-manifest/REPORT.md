# Rust Toolchain Baseline Selection and Component Identity Manifest

## Summary

Evaluating five `rust-lang/rust` toolchain candidates—`nightly-2026-05-31`
(`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `1.98.1`
(`48a229ceaefd4985c50990b14116b6d856af0985`), `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `1.100.0`
(`0ef1bc386059596dada8fb65b50425aab2ea637a`), and `nightly-2026-11-12`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`)—establishes **Rust 1.99.1** paired
with **Lean 4 v4.34.1** (`5045d0056413266e57c625dcd7c365b10e377c52`) as the
canonical verification and code-generation baseline:

1. **Specification and semantic alignment:** Rust `1.99.1` is the latest point
   release of the `1.99` train covered by the Ferrocene Language Specification
   (`rust-lang/fls` tag `1.99`, commit
   `946eacae5a4a33a89af7832178504692439e7478`) and matches the `Runtime(PostCleanup)`
   MIR semantics mechanized in `joshlf/anneal`
   (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`). It includes the point-release
   fix for the x86-64 FFI `bool` return-value miscompilation
   (`rust-lang/rust#163911`) while avoiding the unindexed `ProjectionElem::PhantomDeref`
   MIR variant (`rust-lang/rust#159103`) and the x86 `"Rust"` calling-convention
   SSE register-passing change (`rust-lang/rust#161583`) introduced in `1.100.0`.
2. **Stable releases do not shrink the backend contract:** A drop-in `rustc`
   targeting a stable release cannot omit nightly code-generation features used
   by the standard library. In Rust `1.99.1`, `src/bootstrap` sets
   `RUSTC_BOOTSTRAP=1` globally to compile `core` (265 `#![feature(...)]`
   gates), `alloc` (181), `std` (207), `stdarch` (41), `portable_simd` (12),
   `proc_macro` (12), `panic_unwind` (6), `panic_abort` (4), and
   `compiler_builtins` (18)—a union of **469 distinct feature gates** across the
   sysroot, including `core_intrinsics`, `repr_simd`, `simd_ffi`, `f16`, `f128`,
   `asm_experimental_arch`, `abi_unadjusted`, `abi_custom`, `linkage`,
   `thread_local`, and `naked_functions_target_feature`.
3. **Controlled subsystem evolution across candidates:** Between `1.98.1` and
   `1.99.1`, `rustc_middle::mir::syntax` adds `AssertKind::NullReferenceConstructed`
   and `CastKind::BoxDerefTransmute`, and `rustc_codegen_ssa::traits::asm`
   replaces stringified assembly constants (`Const { string: String }`) and
   `SymFn`/`SymStatic` variants with typed `Const { value: Scalar, ty: Ty<'tcx> }`
   and `SymThreadLocalStatic { def_id: DefId }`. Between `1.99.1` and `1.100.0`,
   `rustc_codegen_ssa::traits::type_` expands `BaseTypeCodegenMethods` with
   `type_f16b`, `type_ppcf128`, and `type_x87_f80` and changes `int_width` and
   `vector_length` to return `Option<u64>`.
4. **Proof-checker toolchain coupling:** Lean 4 `v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`) bundles Clang `22.1.4`, LLD
   `22.1.4`, `libclang-cpp.so.22.1`, and `libLLVM.so.22.1` built from
   `llvm/llvm-project` `35990504507d79e0b9deb809c8ee5e1b34ceef20`, upgrading
   from the LLVM `19.1.2` toolchain (`7ba7d8e2f7b6445b60679da826210cdde29eaf8b`)
   bundled in Lean `v4.27.0` through `v4.29.1`.

## Applicability

These findings govern toolchain pinning, component hash verification, and
cross-version semantic comparisons across the five `rust-lang/rust` revisions
and eight Tier 1 target triples (`x86_64-unknown-linux-gnu`,
`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-unknown-linux-gnu`,
`aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, and
`i686-pc-windows-msvc`, plus `x86_64-apple-darwin` where host archives are
published):

- **Exact observation:** Git commit identities, submodule/subtree revisions,
  `Cargo.lock` dependency versions, `#![feature(...)]` inventories, and source
  diffs are taken directly from the five `rust-lang/rust` commits listed in
  `REPORT.json`. Official distribution archive SHA-256 digests are extracted
  from the signed `static.rust-lang.org/dist` channel manifests for each
  candidate.
- **Host execution environment:** Runtime `--print cfg`, `--print target-list`,
  and `-vV` probes were executed on `x86_64-unknown-linux-gnu` (Linux
  `7.1.6-1rodete1-amd64`) across the installed `1.99.1`, `1.100.0`,
  `nightly-2026-05-31`, and `nightly-2026-11-12` toolchains and the `elan`
  Lean 4 installations (`v4.15.0` through `v4.34.1`).

## Findings

### 1. Candidate toolchain identity matrix

Basis: source + execution

Table 1 records the top-level repository, LLVM submodule, Cargo submodule, and
distribution manifest identities for the five candidate toolchains.

| Candidate | `rust-lang/rust` Commit | Commit Date | `src/llvm-project` Commit | LLVM Version | `src/tools/cargo` Commit (Version) | Channel Manifest SHA-256 (`channel-rust-*.toml`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `nightly-2026-05-31` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | 2026-05-30 | `08c84e69a84d95936296dfcab0e38b34100725d5` | `22.1.6` | `f57b05f80f5d42dc63a0e4ea48a2d5c4c79ec028` (`0.99.0-nightly`) | `d4101af9bbf8d0ee88fbf1f82794fa0269b185bcb4cbfe0ea8cacc542cb0abc4` |
| `1.98.1` | `48a229ceaefd4985c50990b14116b6d856af0985` | 2026-09-01 | `52ed14fcd56afc30f9cccd8ca8ce237c2eef7e04` | `22.1.7` | `797e8a9bca276c1c9f9f738d2a20f484fa4eea9d` (`0.99.0`) | `a7c8774a5fd8441c997d94c029776cbc5eb111e9d72ab5d256fa69866644347e` |
| **`1.99.1` (Baseline)** | **`58cf8f9c35b355199727627d07ae34a4e2846d67`** | **2026-10-13** | **`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`** | **`23.1.1`** | **`5f94df4789f005f9a352888e8355ffc645b7ed0e` (`0.100.0`)** | **`fb152be80975c194aa5fc684b2aec3a6e14e2b855efe2faa4e5f8ae6e590f463`** |
| `1.100.0` | `0ef1bc386059596dada8fb65b50425aab2ea637a` | 2026-11-09 | `0a5579eb649d3634a9c30ac873300cc2944fa070` | `23.1.5` | `3acc79c0c841844675bc53a605922dbfc441e750` (`0.101.0`) | `3051e859570f64a8c5acb9d09e87425db52c7d97287c67e8f6d57d7d34ef9258` |
| `nightly-2026-11-12` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | 2026-11-11 | `0a5579eb649d3634a9c30ac873300cc2944fa070` | `23.1.5` | `c07ac2c4d12237effc4b94f4543769b421790045` (`0.103.0-nightly`) | `0e29758e4495709044396db6992e8bc44cd0109e7dbb21e430216cf368ac6c9d` |

In all five candidates, `src/llvm-project`, `src/tools/cargo`, and
`library/backtrace` are Git submodules (`mode 160000`), whereas
`library/stdarch`, `library/compiler-builtins`, `src/tools/miri`,
`src/tools/rust-analyzer`, `compiler/rustc_codegen_cranelift`, and
`compiler/rustc_codegen_gcc` are tracked as in-tree subtrees (`mode 040000`).
Table 2 records the exact subtree Git tree OIDs, last-modifying commits, and
locked dependency versions (`library/Cargo.lock` and root `Cargo.lock`) across
the five candidates.

| Component / Dependency | `nightly-2026-05-31` | `1.98.1` | **`1.99.1` (Baseline)** | `1.100.0` | `nightly-2026-11-12` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `library/stdarch` (`core_arch` / `std_detect`) | `0.1.5` (tree `51f0b7f45f00`, commit `599f62467c46`) | `0.1.5` (tree `d06650ab63b4`, commit `eaa172c56530`) | **`0.1.5` (tree `a156bbe91754`, commit `5ca95c07e0be`)** | `0.1.5` (tree `5f790a4b17e3`, commit `4282aee7a71e`) | `0.1.5` (tree `c82e57035578`, commit `a79fce1e15f7`) |
| `library/compiler-builtins` (`libm`) | `0.1.160` (`libm 0.2.16`) | `0.1.160` (`libm 0.2.16`) | **`0.1.160` (`libm 0.2.16`)** | `0.1.160` (`libm 0.2.16`) | `0.1.160` (`libm 0.2.16`) |
| `libc` (`library/Cargo.lock` / root `Cargo.lock`) | `0.2.185` / `0.2.183` | `0.2.185` / `0.2.183` | **`0.2.189` / `0.2.183`** | `0.2.189` / `0.2.189` | `0.2.191` / `0.2.191` |
| `hashbrown` (`library/Cargo.lock` / root `Cargo.lock`) | `0.17.1` / `0.15.5, 0.16.1, 0.17.0` | `0.17.1` / `0.15.5, 0.16.1, 0.17.0` | **`0.17.1` / `0.15.5, 0.16.1, 0.17.0`** | `0.17.1` / `0.17.1` | `0.17.1` / `0.17.1` |
| `library/backtrace` submodule (`root Cargo.lock`) | `28ec93b503bf` (`0.3.75`) | `d902726a1dcd` (`0.3.75`) | **`d902726a1dcd` (`0.3.75`)** | `d902726a1dcd` (`0.3.75`) | `d902726a1dcd` (`0.3.77`) |
| `src/tools/miri` subtree (last commit) | tree `c6b53fd00d62` (`cf39dc63f489`) | tree `538a9749b457` (`9272c6d92a9b`) | **tree `a1a75784070b` (`6e08e3164ef4`)** | tree `3b3f4440d378` (`fcf74ea7379f`) | tree `245c2c165628` (`e982cc300b86`) |
| `src/tools/rust-analyzer` subtree (last commit) | tree `56623fd25929` (`3eb07737846c`) | tree `1eae41ef9740` (`5d0c6bad9418`) | **tree `48abafade3eb` (`5b3e2771b1fa`)** | tree `6f56fb759259` (`370012b288ab`) | tree `4087c9c22a82` (`180c1af4ec1e`) |
| `compiler/rustc_codegen_cranelift` subtree | tree `71095f98744b` (`cf39dc63f489`) | tree `0f52eda7bedc` (`9272c6d92a9b`) | **tree `d5caa35afe6d` (`196dd2a174f4`)** | tree `5a3306a2f490` (`f0f6653e3be1`) | tree `39472295e594` (`9b042a6ed04b`) |
| `compiler/rustc_codegen_gcc` subtree | tree `91e88b19f585` (`15b13982bfa6`) | tree `73ec44f17a1c` (`95adef7b5caf`) | **tree `7c739655f340` (`6a3b9acf1485`)** | tree `f3d9337b5a2f` (`c6dc51196d5d`) | tree `61e02f65fba0` (`1a97ea16c051`) |
| `compiler/rustc_codegen_gcc/libgccjit.version` | `6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3` | `6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3` | **`6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3`** | `badf78d09d16e66f4ca07971c51aa6a227558d4f` | `e1c6e07b095d091177376a163da44039475e05e3` |

### 2. Tier 1 release archive SHA-256 digests for Rust 1.99.1

Basis: normative + source

Table 3 lists the `.tar.xz` SHA-256 digests from `channel-rust-1.99.1.toml`
(manifest SHA-256 `fb152be80975c194aa5fc684b2aec3a6e14e2b855efe2faa4e5f8ae6e590f463`)
across the eight Tier 1 targets plus `x86_64-apple-darwin`. The target-independent
`rust-src-1.99.1.tar.xz` archive (`target = "*"`) has SHA-256
`e485a88c45db546b73571df7bebfcb4454ba4fb552c492e25fc5b00eeb5bf22d`. Full
archive hashes for all five candidate toolchains are preserved in
`support/baseline_manifest.json`.

| Target Triple | `rustc-1.99.1-<target>.tar.xz` | `rust-std-1.99.1-<target>.tar.xz` | `cargo-1.99.1-<target>.tar.xz` | `rustc-dev-1.99.1-<target>.tar.xz` | `llvm-tools-1.99.1-<target>.tar.xz` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `2ff05ff9c08a90861e7f6e4065b40a8b87463b4576186fd613871c3e37f2091f` | `109b074225bf5b9ea3820890876bfdf4ed161adbfaf94b2b4b5984c85ee5d958` | `4c9927101f44e701cf6312d4a506bd09cb10724ee042ae74be2c715064b743eb` | `e2b1c9ffe50910d5274339b52774eec05433682835219566449cd09c67c1d1d2` | `8429c5117debfb45c22cf2f97712ef00e0e94976c96cf92f661974a458ca7e84` |
| `x86_64-pc-windows-msvc` | `7da83c2af1f209606b0160f25174d2867c7c7b73667c32c9e5fbcef4f5f45348` | `4fe09430ded40b8b3092b49f0a651178eb1f8154ef4d1f1a73f2a3595b2d956f` | `83ca3c1d2e83c27bf12553ee87be617b546bd55d2069324bf96187c079434e15` | `be6f2cec671534b1d2f20da3f5670279c270de9ea6617e967030705ba1a539c6` | `61b0ce740983240f48ceab73b6a1306a6c25bd7c92dc8135e47e8401b16d9b32` |
| `x86_64-pc-windows-gnu` | `a48f186defb3d57538b34e14a24a94f6e29906f191630b627dcb091198bae438` | `b17e3bc962ff24b3bc47a750d838defed85b280746250e3a3ad029e6c1a29dd7` | `4a0623f4ec9e62f33666fb3289173e6200b90282ca96fc6f013e8a7160582461` | `e198825fec4f2ac40a15981240a359e2c880e8fc957293f460d7def6baa439a4` | `7cc7089d8e6e8031adc8c9a2251d32c7e70c34e2ed472834b0753fa63ebd91b2` |
| `aarch64-unknown-linux-gnu` | `acdcdfe09ae1f103aa9a2b7f88903a9588bc2e99288af10e6fbf5514e2e49f25` | `e25668477083d6a9ddb87b9beb9c00742225f38233ccb4bfba3afa7a07427f52` | `5156832e0c1254e9b49a79edabdc6d4c35f32f8fc1cf3ca700f268ff96087ab0` | `84f8470606b763856480ab0a22bb3f494b66cdbe3a0f77eb276bf8fb040e6087` | `cd1818058908c1c4e99bd2843fe103df255157454e16186ec9cc3b5b5823b39c` |
| `aarch64-apple-darwin` | `23948a0a9c162fd2952defb3fb0462c44e8fcfd1a4ab8a274a1e1bdb2cf810a3` | `fe79d6ab5a0321de26463999d8c112b8ad3eafbcbcf822d66a2300b45dde1031` | `685e563d94db1f003ffa5f5831439eec02569b9950b69867953c8213269c1eaf` | `eb39c1be4e4ae8957cd3e2c44f4ef6a0b6c5f5bc40a6e17477d19edcf56280d7` | `b348db9d79666aee4b5e2ff4269029fffd16815cbd47f47018cd0b06e4f815f5` |
| `aarch64-pc-windows-msvc` | `4d89c7f3f9d8637c667332adf77b55f43c322ae0ff038e75493bb28e16369af2` | `044748841f47007a222dd5b3f5e9dacec1dae7386d7d308c5172d07ea7112fa0` | `28ae5b9b72ae43aa01d2f6c1b285be59f8aef6eafc96f9e16b912c3c1363a638` | `e38d5809c6983952ab6ff8455068c74a2265c961500cb79e694f4700a2bf17cf` | `d1b503c317d5cee401a845b402cd65fdbdcce3272a007cb3b25ec4dcdfdd1b27` |
| `i686-unknown-linux-gnu` | `e45304801ebbc061653979c13b805519b3446a12099f3215944b0f6e69c0fca2` | `8abb74feac06cfb0d3de4e27301adb05f740661c7d6fb154528906202157ae15` | `df80890e57e5aee20660c784b26ff1b1f97ec04bde43ecf8801704a9c2f017fd` | `6edf3439ca73e7b17ad510d648cf827159bdffb57dcba6e6c8f38479790f14e8` | `7eefac3d697a3636405903a2674a5a6f9ec2e327a3d1bbb36b75ba4d29ab93e5` |
| `i686-pc-windows-msvc` | `aca41f7a209617a45ae0cc5679e4e94d49d63038ae1986f1ea5fceb2cfe4ddb1` | `3a086606ba2581d43e905f65466d122c257ef0329ae3fbc3ceb067286d0668b0` | `d2db94eab7d2a622c002889e19d394573af51cde003cc7c75ce8e741dd66fb58` | `d4ada8d670cf64109cb4b882697cd2cf08fcc81cb983ae6fbb3ae2603f4da764` | `e96fc866494af0d061166d59b5cad0efcea8c3e856010b01f3a61451d8aea4c1` |
| `x86_64-apple-darwin` | `203feef2c2165d7dda1f30ccf75590f72a6abc52ce259ed1c418de84a6887698` | `484d5b88b424ddd29df196e1eb9420c8335bb5fac90a3c37140253345a8c65c4` | `6636dabcec164909d1c6eb9e2c596148787c84f7d3a02ff68a141569077f80b5` | `fe39284e48a8ccd6bacd75008468dbc8350442183d740fdfa1e788340e9fe5fa` | `3112e92b03b1cca4264a30ca602948d31976cd45db7de2bc7900efa25a39a045` |

In stable channel manifests (`1.98.1`, `1.99.1`, `1.100.0`), the `miri-preview`
and `rustc-codegen-cranelift-preview` package entries set `available = false`
for all targets (`pkg.miri-preview.version = ""`), even though `src/tools/miri`
and `compiler/rustc_codegen_cranelift` are present in the release source tree
and buildable via `./x.py build src/tools/miri` or
`./x.py build compiler/rustc_codegen_cranelift`. Prebuilt `miri-preview` and
`rustc-codegen-cranelift-preview` tarballs are published only in the nightly
manifests (`nightly-2026-05-31` and `nightly-2026-11-12`; see
`support/baseline_manifest.json`).

### 3. Does pinning a stable release shrink the compiler surface? (`RUSTC_BOOTSTRAP` and sysroot `#![feature]` census)

Basis: source + derived

Pinning a stable release (`1.99.1`) restricts **external user crates** (when
invoked without `RUSTC_BOOTSTRAP`) from enabling unstable `#![feature(...)]`
gates or `-Z` flags, but it **does not shrink the internal language, MIR, or
code-generation surface required to build the Rust sysroot (`core`, `alloc`,
`std`, `compiler_builtins`, `proc_macro`, `panic_unwind`, `panic_abort`)**:

1. **How a stable toolchain compiles its own unstable sysroot:** In
   `src/bootstrap/bootstrap.py:1119-1138` and
   `src/bootstrap/src/core/builder/cargo.rs:845,1197`, `bootstrap` exports
   `RUSTC_BOOTSTRAP=1` into every Cargo and `rustc` invocation. Inside the
   compiler (`compiler/rustc_feature/` and `compiler/rustc_session/`),
   `RUSTC_BOOTSTRAP=1` forces a stage-1/stage-2 compiler built with
   `CFG_RELEASE_CHANNEL="stable"` to accept all `#![feature(...)]` attributes
   and `-Z` flags as if it were a nightly compiler. For crates that must *not*
   accidentally depend on unstable features during bootstrap, `bootstrap`
   explicitly passes `-Zallow-features=` to override `RUSTC_BOOTSTRAP=1`.
2. **Quantitative `#![feature(...)]` inventory across sysroot crates:** Table 4
   counts the distinct `#![feature(...)]` identifiers enabled across the
   standard-library workspace and `library/compiler-builtins`, alongside the
   total active unstable language/compiler features declared in
   `compiler/rustc_feature/src/unstable.rs`.

| Candidate | `core` | `alloc` | `std` | `stdarch` | `portable_simd` | `compiler_builtins` | `proc_macro` | `panic_unwind` / `panic_abort` | Union Across Sysroot | `rustc_feature` Active Unstable Gates |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `nightly-2026-05-31` | 253 | 157 | 198 | 40 | 10 | 17 | 11 | 7 / 4 | 454 | 182 |
| `1.98.1` | 252 | 167 | 203 | 41 | 10 | 17 | 12 | 6 / 4 | 456 | 187 |
| **`1.99.1` (Baseline)** | **265** | **181** | **207** | **41** | **12** | **18** | **12** | **6 / 4** | **469** | **188** |
| `1.100.0` | 267 | 180 | 208 | 41 | 12 | 18 | 11 | 6 / 4 | 475 | 187 |
| `nightly-2026-11-12` | 273 | 180 | 207 | 41 | 12 | 17 | 11 | 6 / 4 | 487 | 192 |

3. **Backend-critical unstable features required by `1.99.1` sysroot crates:**
   In `1.99.1`, `library/compiler-builtins` enables 18 unstable features:
   `abi_custom`, `abi_unadjusted`, `asm_experimental_arch`,
   `cfg_target_has_atomic`, `compiler_builtins`, `compiler_builtins_lib`,
   `core_intrinsics`, `decl_macro`, `f128`, `f16`, `lang_items`, `linkage`,
   `macro_metavar_expr_concat`, `optimize_attribute`, `repr_simd`,
   `rustc_attrs`, `rustc_private`, and `test`. Furthermore, `core`, `alloc`, and
   `std` enable codegen-affecting features including `simd_ffi`, `link_llvm_intrinsics`,
   `ffi_const`, `ffi_pure`, `c_variadic`, `naked_functions_target_feature`,
   `thread_local`, `cfg_Accessible`, `ub_checks`, `allow_internal_unstable`,
   and `staged_api`. Any backend that compiles the `1.99.1` sysroot from source
   or inlines cross-crate `#[inline]` / generic MIR from `core` and `std` must
   support these lowered constructs.

### 4. Subsystem diffs across the five candidates

Basis: source + execution

Comparing `nightly-2026-05-31`, `1.98.1`, `1.100.0`, and `nightly-2026-11-12`
against `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) isolates the
exact design surfaces that shift between versions (full diffs in
`support/candidate_diffs.json`):

1. **MIR syntax (`compiler/rustc_middle/src/mir/syntax.rs`):**
   - `nightly-2026-05-31` $\rightarrow$ `1.99.1` (`1 file changed, 50 insertions,
     61 deletions`) and `1.98.1` $\rightarrow$ `1.99.1` (`19 insertions, 5 deletions`):
     - `AssertKind` adds `NullReferenceConstructed` (alongside
       `NullPointerDereference` and `InvalidEnumConstruction(O)`).
     - `CastKind` adds `BoxDerefTransmute` (`syntax.rs:1498-1508`), generated by
       elaborated `Box<T>` dereferences to convert the inner `Unique`/`NonNull`
       pointer into a raw pointer while asserting `Box<T>` validity.
     - Between `nightly-2026-05-31` and `1.98.1`/`1.99.1`, `AggregateKind::Closure`,
       `Coroutine`, and `CoroutineClosure` change their second payload field
       from `GenericArgsRef<'tcx>` to `GenericArgs<'tcx>` (`nightly-2026-05-31`
       uses `GenericArgsRef<'tcx>`), and derived `Hash` impls on `StatementKind`,
       `Rvalue`, and `TerminatorKind` are removed in favor of `StableHash`.
   - `1.99.1` $\rightarrow$ `1.100.0` (`4 insertions, 25 deletions` in reverse):
     - `ProjectionElem<V, T>` adds `PhantomDeref` (`syntax.rs:1261-1280`, landed
       in `rust-lang/rust#159103` for experimental `Reborrow` traits). Because
       `PhantomDeref` is a borrow-checking placeholder that `1.100.0` carries in
       `PlaceElem`, pinning `1.99.1` avoids having to handle or reject
       `PhantomDeref` in post-cleanup MIR visitors.
     - `AnalysisPhase` replaces `CoverageKind::BlockMarker | SpanMarker` doc
       references with `CoverageKind::is_removed_after_analysis`.
   - `1.100.0` $\rightarrow$ `nightly-2026-11-12`: Only doc-comment updates in
     `syntax.rs`; no enum variant additions in `StatementKind`, `Rvalue`, or
     `TerminatorKind`.

2. **Codegen backend traits (`compiler/rustc_codegen_ssa/src/traits/`):**
   - `1.98.1` $\rightarrow$ `1.99.1` (`7 files changed, 37 insertions, 65 deletions`):
     - In `traits/asm.rs:28-53`, `InlineAsmOperandRef::Const { string: String }`
       and `GlobalAsmOperandRef::Const { string: String }` are replaced by
       `Const { value: Scalar, ty: Ty<'tcx> }`, and `SymFn`/`SymStatic` are
       replaced by `SymThreadLocalStatic { def_id: DefId }`.
   - `1.99.1` $\rightarrow$ `1.100.0` (`6 files changed, 30 insertions, 44 deletions`
     in reverse):
     - `AsmCodegenMethods::codegen_global_asm` (`traits/asm.rs:68-82`) gains an
       `extra_rust_target_features: &[String]` parameter to forward target
       features from `#[unsafe(naked)]` functions into module-level assembly.
     - `WriteBackendMethods` (`traits/write.rs:16-52`) relaxes `type Module: Send + Sync`
       to `type Module: Send`, simplifies `target_machine_factory(&self, sess: &Session)`,
       and passes `incr_comp_session: Option<&BorrowedIncrCompSession>` to
       `run_thin_lto`.
   - `1.99.1` $\rightarrow$ `nightly-2026-11-12` (`9 files changed, 94 insertions,
     116 deletions` in reverse):
     - `BaseTypeCodegenMethods` (`traits/type_.rs:19-88`) adds `type_f16b()`,
       `type_ppcf128()`, and `type_x87_f80()`, removes `type_array`, `type_kind`,
       and `element_type`, and changes `int_width`, `float_type`, and
       `vector_length` to return `Option<...>`.

3. **Tier 1 target specifications (`compiler/rustc_target/src/spec/targets/`) and `--print cfg`:**
   - Across `1.99.1`, `1.100.0`, `nightly-2026-05-31`, and `nightly-2026-11-12`,
     `rustc --print cfg --target <triple>` is byte-for-byte identical across
     `1.99.1` and `1.100.0` for all eight Tier 1 targets (full outputs in
     `support/tier1_cfgs.json`).
   - Between `nightly-2026-05-31` and `1.99.1`:
     - `aarch64_pc_windows_msvc.rs` changes `base.features` from
       `"+v8a,+neon,+outline-atomics"` to `"+v8a,+neon"`.
     - `aarch64_unknown_linux_gnu.rs` adds default GNU linker flags
       `-Wl,--fix-cortex-a53-843419` (`pre_link_args`).
   - Between `1.99.1` and `1.100.0`:
     - `i686_pc_windows_msvc.rs:28` changes `TargetMetadata.host_tools` from
       `Some(true)` to `Some(false)` (while keeping `tier: Some(1)` and
       `std: Some(true)`).
     - `x86` 32-bit `"Rust"` ABI (`rust-lang/rust#161583`) changes in `1.100.0`
       to pass floating-point and vector scalars in SSE registers when SSE2 is
       baseline-enabled (as on `i686-unknown-linux-gnu` and
       `i686-pc-windows-msvc`, where `target_feature="sse2"` is default).

4. **Intrinsics, `simd_*`, `target_features`, `core::arch`, and MIR passes:**
   Table 5 summarizes the quantitative size of each subsystem across the five
   candidates.

| Subsystem Metric | `nightly-2026-05-31` | `1.98.1` | **`1.99.1` (Baseline)** | `1.100.0` | `nightly-2026-11-12` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `#[rustc_intrinsic]` declarations in `library/core/src/intrinsics/` | 311 | 311 | **316** | 306 | 279 |
| `simd_*` intrinsic declarations in `library/core/src/intrinsics/simd.rs` | 12 (module split) | 12 (module split) | **12 (in `simd/` submodules: 81 total)** | 12 (81 total) | 12 (81 total) |
| Unique `#[link_name = "llvm.*"]` bindings in `library/stdarch/crates/core_arch` | 8,166 | 8,171 | **8,115** | 8,106 | 8,150 |
| `compiler/rustc_mir_transform/src/lib.rs` line count | 838 | 867 | **843** | 842 | 855 |
| Total targets in `rustc --print target-list` | 256 | 258 | **261** | 266 | 267 |

   Note that the drop in `#[rustc_intrinsic]` count from `316` in `1.99.1` to
   `306` in `1.100.0` and `279` in `nightly-2026-11-12` reflects ongoing
   upstream replacement of compiler intrinsics with MIR-built operations or
   default body implementations in `library/core/src/intrinsics/`, while the
   drop in `#[link_name = "llvm.*"]` bindings in `core_arch` (`8,171` in
   `1.98.1` to `8,115` in `1.99.1` and `8,106` in `1.100.0`) reflects replacing
   target-specific LLVM intrinsic externs with portable `simd_*` intrinsics.

5. **LLVM version progression (LLVM 22.1.x vs LLVM 23.1.x):**
   - `nightly-2026-05-31` (`22.1.6`) and `1.98.1` (`22.1.7`) use the LLVM 22
     release branch, whereas `1.99.1` (`23.1.1`), `1.100.0` (`23.1.5`), and
     `nightly-2026-11-12` (`23.1.5`) use LLVM 23 (`rust-lang/rust` commit
     `2ed3b6628395` upgraded `rustc` to LLVM 23, and `1ad842af36c0` updated
     `1.99.1` to LLVM `23.1.1`).
   - Selecting `1.99.1` places the baseline on LLVM 23 (`23.1.1`), matching the
     `1.100.0` and `nightly-2026-11-12` major LLVM IR version (opaque pointers,
     `nuw`/`nsw` on `getelementptr inbounds`, `captures(...)` attribute syntax
     replacing legacy `nocapture` bitmasks, and range metadata refinements).

### 5. Post-release fixes, miscompilations, and inherited bug ledger

Basis: documentation + source

To support deviation tracking under compiler qualification (Goal 4), Table 6
lists the point-release bug fixes and miscompilations recorded in `RELEASES.md`
across the `1.98.x`, `1.99.x`, and `1.100.0` boundaries:

| Release Boundary | Issue / PR | Affected Subsystem & Behavior | Impact on `1.99.1` Baseline |
| :--- | :--- | :--- | :--- |
| Fixed in `1.98.1` (after `1.98.0` / `nightly-2026-05-31`) | `rust-lang/rust#161441` | Miscompilation in vtable generation for trait objects with non-trivial subtyping/upcasting layouts. | **Resolved in `1.99.1`.** (`nightly-2026-05-31` lacks this fix.) |
| Fixed in `1.99.1` (after `1.99.0`) | `rust-lang/rust#163911` | Miscompilation of FFI `bool` return values on `x86_64` (missing `range(i8 0, 2)` / `zext` ABI attribute alignment with Clang). | **Resolved in `1.99.1`.** |
| Fixed in `1.99.1` (after `1.99.0`) | `rust-lang/rust#163614` | `library`: missing symbol `wcslen` on UEFI and embedded targets. | **Resolved in `1.99.1`.** |
| Fixed in `1.99.1` (after `1.99.0`) | `rust-lang/rust#163947` | `rust-lld`: missing `@loader_path` rpath for `libLLVM` on macOS. | **Resolved in `1.99.1`.** |
| Landed in `1.100.0` (after `1.99.1`) | `rust-lang/rust#160911` | From `1.94` up to `1.100`, ARMv7-A hardfloat targets erroneously included `+d32` (`VFPv3-D32`) in baseline target features. | **Inherited by `1.99.1`** on Tier 2 ARMv7-A hardfloat targets (does not affect the 8 Tier 1 targets). |
| Landed in `1.100.0` (after `1.99.1`) | `rust-lang/rust#161280` | On ARM targets, `-Ctarget-feature` / `-Ctarget-cpu` flags that alter the float/vector ABI are rejected as hard errors in `1.100.0` (warn-by-default in `1.99.1`). | **Inherited by `1.99.1`:** `1.99.1` emits an ABI warning rather than a hard error. |
| Landed in `1.100.0` (after `1.99.1`) | `rust-lang/rust#160302` | Hard error when enabling SSE/AVX on x86 32-bit/64-bit softfloat targets. | **Inherited by `1.99.1`:** relevant only to `-Ctarget-feature=-sse` / softfloat configurations. |
| Landed in `1.100.0` (after `1.99.1`) | `rust-lang/rust#161583` | Changes the unstable default `"Rust"` ABI on 32-bit x86 (`i686-*`) to pass floats in SSE registers when SSE is baseline-enabled. | **`1.99.1` uses the pre-1.100 x86 `"Rust"` ABI.** Must be accounted for if comparing `i686` codegen against `1.100.0`. |

### 6. External verification and testing tool compatibility

Basis: source + documentation

Table 7 summarizes how the six external verification, benchmarking, and
differential-testing tools align with the `1.99.1` (LLVM `23.1.1`) baseline.

| Tool | Pinned Repository & Revision | LLVM / Toolchain Compatibility with Rust `1.99.1` (LLVM `23.1.1`) |
| :--- | :--- | :--- |
| **Alive2** | `AliveToolkit/alive2` `adacbd5180ccf95075e9867c4f0c259f59c9fef2` | Requires C++20 (`CMakeLists.txt:29`) and builds against LLVM 22/23 `llvm-project` headers/libraries; standalone `alive-tv` validates textual `.ll` and `.bc` emitted by `rustc +1.99.1 --emit=llvm-ir,llvm-bc`. |
| **Vellvm** | `vellvm/vellvm` `1d651e7a391c6d0112f0b2ecb7c363c58c3a7d3c` (and `506f1eb0be542611521985719b971fbce8498dc9`) | Mechanized in Rocq `9.1.1` / OCaml `4.14.1` (`README.md:14-17`). Models opaque pointers (`ptr`), byte-level poison memory (`DTYPE_B`), and `freeze`. Parsing LLVM 23 `.ll` files emitted by `rustc 1.99.1` requires stripping LLVM 23-specific parameter attributes (`captures(none)`, `noundef`, `range(...)`) not in Vellvm's OCaml lexer. |
| **Lean-MLIR** | `opencompl/lean-mlir` `b8c4a771319a044854a4bbb49b8821381ef86ff8` | Pure Lean 4 formalization of SSA dialects, `BitVec`, and `PoisonOr` (`lean-toolchain`: `nightly-2025-12-01`, core `BitVec` theorems compatible with Lean `v4.34.1`). Does not link against host `libLLVM`, so it is unaffected by LLVM 22 vs 23 C++ API changes. |
| **`rustc-perf`** | `rust-lang/rustc-perf` `b9d680e5dda9b6d9ff98716e9eed705dad3c105d` | Workspace `rust-version = "1.97.0"` (`Cargo.toml:6`). Building `collector` (`cargo +1.99.1 build --release -p collector`) and running `bench_local` works directly with `rustc 1.99.1` as both host builder and benchmarked compiler. |
| **`abi-cafe`** | `Gankra/abi-cafe` `94d38030419eb00a1ba80e5e2b4d763dcee58db4` | Invokes `rustc` and C compilers as external subprocesses (`Cargo.toml:1-25`). Supports `rustc 1.99.1` directly and supports pairing `--codegen-backend` variants via `-Zcodegen-backend` when `RUSTC_BOOTSTRAP=1` is set. |
| **`rustlantis`** | `cbeuw/rustlantis` `2be7c5a6763831dc0f908f0e05723ebbbc2a62cc` | Emits `#![feature(custom_mir, core_intrinsics)]` programs (`README.md:3-18`, `--call-syntax v4`). Compiles and executes on `rustc 1.99.1` when invoked with `RUSTC_BOOTSTRAP=1` (or on `nightly-2026-05-31` / `nightly-2026-11-12` natively). |

### 7. Lean 4 baseline (`v4.34.1`) and bundled C/LLVM toolchain

Basis: execution + source

Inspecting the eight `leanprover/lean4` releases installed under `~/.elan/toolchains/`
shows three distinct bundled LLVM/Clang generations across Lean 4's history
(Table 8).

| Lean 4 Release | `leanprover/lean4` Commit | Bundled `clang` & `ld.lld` Version | Bundled `llvm/llvm-project` Commit | Bundled Shared Libraries (`lib/`) |
| :--- | :--- | :--- | :--- | :--- |
| `v4.15.0` | `11651562caae` | `15.0.1` | `b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf` | `libclang-cpp.so.15`, `libLLVM-15.0.1.so` |
| `v4.16.0` | `128a1e6b0a82` | `15.0.1` | `b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf` | `libclang-cpp.so.15`, `libLLVM-15.0.1.so` |
| `v4.27.0` | `db93fe1608548721853390a10cd40580fe7d22ae` | `19.1.2` | `7ba7d8e2f7b6445b60679da826210cdde29eaf8b` | `libclang-cpp.so.19.1`, `libLLVM.so.19.1` |
| `v4.28.0-rc1` | `3b0f2862196c6a8af9eb0025ee650252694013dd` | `19.1.2` | `7ba7d8e2f7b6445b60679da826210cdde29eaf8b` | `libclang-cpp.so.19.1`, `libLLVM.so.19.1` |
| `v4.28.0` | `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` | `19.1.2` | `7ba7d8e2f7b6445b60679da826210cdde29eaf8b` | `libclang-cpp.so.19.1`, `libLLVM.so.19.1` |
| `v4.29.0` | `98dc76e3c0a9b856c9b98726b713fb04fab16740` | `19.1.2` | `7ba7d8e2f7b6445b60679da826210cdde29eaf8b` | `libclang-cpp.so.19.1`, `libLLVM.so.19.1` |
| `v4.29.1` | `f72c35b3f637c8c6571d353742168ab66cc22c00` | `19.1.2` | `7ba7d8e2f7b6445b60679da826210cdde29eaf8b` | `libclang-cpp.so.19.1`, `libLLVM.so.19.1` |
| **`v4.34.1` (Baseline)** | **`5045d0056413266e57c625dcd7c365b10e377c52`** | **`22.1.4`** | **`35990504507d79e0b9deb809c8ee5e1b34ceef20`** | **`libclang-cpp.so.22.1` (65,075,176 B), `libLLVM.so.22.1` (77,258,216 B)** |

Pinning **Lean 4 `v4.34.1`** (`5045d0056413266e57c625dcd7c365b10e377c52`)
provides `bv_decide` / `bv_omega` and ` cadical` (`bin/cadical`, 1,111,624 B)
alongside `bin/leanchecker` (51,080 B), `bin/clang` (`22.1.4`), `bin/ld.lld`
(`22.1.4`), and `bin/llvm-ar` (76,888 B), plus bundled static/shared runtime
archives (`libc++.a`, `libc++abi.a`, `libgmp.a`, `libunwind.a`, `libatomic.so.1.2.0`,
and glibc CRT startup objects `crt1.o`, `crti.o`, `crtn.o`). Note that invoking
Lean's bundled `bin/clang` directly outside `leanc` requires passing
`-isystem <toolchain>/include/clang` (as `bin/leanc` does internally), because
its default resource header directory is scoped to Lean's internal sysroot.

## Boundaries

- **LLVM C++ repository history (`not examined` in full):** While the exact
  `src/llvm-project` submodule commit hashes (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`
  for `1.99.1`, `0a5579eb649d3634a9c30ac873300cc2944fa070` for `1.100.0` and
  `nightly-2026-11-12`, `52ed14fcd56afc30f9cccd8ca8ce237c2eef7e04` for
  `1.98.1`, and `08c84e69a84d95936296dfcab0e38b34100725d5` for
  `nightly-2026-05-31`) and their `LLVM version` strings were verified via
  `rustc -vV` and `rust-lang/rust` commit logs, line-by-line diffs of
  `llvm/docs/LangRef.rst` inside `rust-lang/llvm-project` belong to the
  dedicated LLVM IR semantics investigation (`W4`).
- **Prebuilt `miri-preview` and `rustc-codegen-cranelift-preview` archives on
  stable (`unsupported` by upstream `dist`):** Upstream `static.rust-lang.org/dist`
  does not ship prebuilt `miri-preview` or `rustc-codegen-cranelift-preview` tarballs
  for stable releases (`1.98.1`, `1.99.1`, `1.100.0`); consumers requiring Miri
  or `cg_clif` at the exact `1.99.1` commit must either build `src/tools/miri`
  / `compiler/rustc_codegen_cranelift` from commit
  `58cf8f9c35b355199727627d07ae34a4e2846d67` or use a pinned nightly companion.

## Evidence

- **Candidate `rust-lang/rust` commits and source trees:**
  - `1.99.1`: `58cf8f9c35b355199727627d07ae34a4e2846d67` (`src/version`,
    `Cargo.lock`, `library/Cargo.lock`, `src/bootstrap/bootstrap.py:1119-1138`,
    `compiler/rustc_middle/src/mir/syntax.rs:1-1720`,
    `compiler/rustc_codegen_ssa/src/traits/`,
    `compiler/rustc_target/src/spec/targets/`).
  - `1.100.0`: `0ef1bc386059596dada8fb65b50425aab2ea637a` (`RELEASES.md:1-180`,
    `compiler/rustc_middle/src/mir/syntax.rs:1258-1280`,
    `compiler/rustc_target/src/spec/targets/i686_pc_windows_msvc.rs:26-30`).
  - `1.98.1`: `48a229ceaefd4985c50990b14116b6d856af0985` (`RELEASES.md`).
  - `nightly-2026-05-31`: `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.
  - `nightly-2026-11-12`: `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`.
- **Preserved support artifacts:**
  - `support/baseline_manifest.json` — complete machine-readable manifest of the
    selected `1.99.1` + Lean `v4.34.1` baseline, all five candidates' submodule
    and subtree identities, `Cargo.lock` dependency versions, official
    `channel-rust-*.toml` SHA-256 digests and per-target `.tar.xz` SHA-256
    hashes, Lean 4 toolchain inventories, and external tool revisions.
  - `support/candidate_diffs.json` — per-crate `#![feature(...)]` lists and
    counts across `core`, `alloc`, `std`, and sysroot crates, subsystem metric
    counts, and unified diffs of `mir/syntax.rs`, `codegen_ssa/traits`, and
    Tier 1 target specs against `1.99.1`.
  - `support/tier1_cfgs.json` — `rustc -vV`, target counts, and
    `rustc --print cfg --target <triple>` outputs for all Tier 1 targets across
    `1.99.1`, `1.100.0`, `nightly-2026-05-31`, and `nightly-2026-11-12`.
  - `support/probe_baseline.py` — standalone revalidation script.

## Revalidation

Run `python3 reports/rustc-baseline-toolchain-selection-and-manifest/support/probe_baseline.py`
to verify the installed `1.99.1` toolchain identity against
`support/baseline_manifest.json`. When evaluating a future `rust-lang/rust`
release candidate against `1.99.1`:

1. Fetch `https://static.rust-lang.org/dist/channel-rust-<version>.toml` and
   compare its `rustc`, `rust-std`, `rustc-dev`, `llvm-tools-preview`, and
   `rust-src` target archive availability and hashes.
2. Diff `compiler/rustc_middle/src/mir/syntax.rs`,
   `compiler/rustc_codegen_ssa/src/traits/`, and
   `compiler/rustc_target/src/spec/targets/` against
   `58cf8f9c35b355199727627d07ae34a4e2846d67`.
3. Diff `rustc +<version> --print cfg --target <triple>` against
   `support/tier1_cfgs.json` for all eight Tier 1 targets.
