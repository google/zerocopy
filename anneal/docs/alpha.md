<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR verifier alpha

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) is an
> experimental verifier under active development and has **not** yet completed
> an independent audit of its Trusted Computing Base (TCB). Today it verifies
> only a small, pointer-free scalar subset of Rust without returning calls
> (`x86_64-unknown-linux-gnu` Profile v1) across selected functions or
> monomorphizations (`UnitTheorem`) or single library or binary crates with no
> required normal or build dependencies (`CrateTheorem`). Passing results depend
> on an intact build host (`rustc`—and any `build.rs` or proc-macro run to
> produce inputs—executes outside the Lean sandbox) as well as human review of
> stated specifications (the declared primary specification module, every
> `specification`-role module, and their transitive meaning dependencies),
> compilation and scope configuration (`request.json` or `verify rustc`
> flags), and TCB audit logs (complete review-surface reporting remains under
> active development). Do not rely on alpha runs as a production security or
> soundness guarantee, and expect frequent breaking changes. Track maturity
> across
> [Stage 0 (`#4095`)](https://github.com/google/zerocopy/issues/4095) ->
> [Stage 1 (`#4012`)](https://github.com/google/zerocopy/issues/4012) ->
> [Stage 2 (`#4096`)](https://github.com/google/zerocopy/issues/4096).

The developer alpha checks selected Rust functions or scalar crates on x86-64
Linux with glibc, such as Ubuntu 24.04. It compiles a library or single binary
target with no required normal or build dependencies (dev-dependencies and
inactive optional dependencies are ignored) using the pinned compiler and
checks the authored Lean proof against the captured MIR, the stated
specification, and Anneal's safety obligations. A successful receipt
(`"schema_version": 3`) identifies the verified scope, compilation
configuration, input digests, containment backend, and assumptions.

On Linux, `ExecSeal` isolates target Lean preflight, elaboration, and audit by
default inside Tier 1 `linux_bwrap` or Tier 2 `linux_landlock_seccomp`
(recorded in `elaboration_sandbox`, failing closed when unavailable unless
`--allow-unsandboxed-elaboration` is passed; see
[elaborator containment](elaborator-containment-design.md)). Rust compilation
(`rustc`) still runs as the caller, so supply a separate isolated execution
environment when processing untrusted Rust crates or build scripts, on
non-Linux hosts, or with `--allow-unsandboxed-elaboration`.

## Try a proof

From the Zerocopy checkout, build and install the pinned tools with Nix.
Keep the same installation cache for setup and verification.

```sh
cd anneal
mkdir -p target
nix build .#omnibus-archive --max-jobs 1 --cores 2 --out-link target/omnibus-link
export XDG_CACHE_HOME="$(mktemp -d)"
cargo run --locked -p cargo-anneal -- setup --local-archive target/omnibus-link
cargo run --locked -p cargo-anneal -- verify \
  --request trusted/cargo-anneal/assets/scalar/request.json
```

The example proves that `zero()` returns zero (`cargo anneal init
--standalone --proof-dir <new-directory>` scaffolds the same four starter
files outside the repository) and prints a human verification card
(`[SCOPED]` for a selected function, `[OK]` only for untainted whole-crate
verification). Inside a Cargo package, `cargo anneal init` scaffolds a
Profile v1 `Specs` starter, and `cargo anneal init --profile v2` scaffolds a
`SpecsV2` starter for crates whose capture emits MIR Profile v2; `--profile`
cannot be combined with `--standalone`. Pass `--receipt-out <path>` to write
the canonical Receipt Schema v3 JSON atomically to disk alongside human
output, or `--format json` to emit JSON directly on stdout
(`--color auto|always|never`, `-q`/`--quiet`, and `-v`/`--verbose` control
terminal styling and detail truncation). To experiment, make a copy of the
fixture directory and change its Rust function to return one. The same proof
then fails (`[FAIL]`, exit code `1`). `--artifacts <new-directory>` retains
the captured Lean program, bound claim, and diagnostic evidence for proof
development; `verify` rejects a path that already exists, or whose parent is
not an existing directory, before it starts any verification work.

To rerun into the same path, add `--overwrite-artifacts`. Every artifact
directory that `verify` writes carries a `.cargo-anneal-artifacts` marker
file. The flag replaces an existing destination only if it is a real directory
(not a symlink) that contains neither the working directory nor any
verification input (request, sources, proofs, shard plan, the selected tools,
or the running `cargo-anneal`), holds only entries that `verify` produces
(each with the expected file or directory type), and, unless empty, carries
that marker; anything else is refused before verification starts. Before
running, `verify` removes an earlier `result.json` and `lean-lib/` from the
destination, so a failing rerun never leaves earlier success evidence behind.
The new artifacts are written to a sibling directory first, and the old
directory is removed only after they are complete. With `--manifest-path`, a
destination inside the package or `--proof-dir` is left out of source
discovery, so a rerun does not pick up its own artifacts, but one holding the
root file of any package target is refused, as is any existing destination
when the package targets cannot be listed.

In `request.json`, each `source_root` resolves relative to the directory
containing the request file or to an existing out-of-tree directory, and
declared inputs must be clean relative regular-file paths inside their
canonicalized `source_root`. Set `scope` to
`{"kind": "selected_unit", "roots": ["module::function"]}` (with optional
`"instantiations": [{"path": "module::generic", "args": ["usize"]}]` for
explicit concrete monomorphizations, or `"roots": []` with a non-empty
`"instantiations"` list when targeting only generic items; `UnitTheorem`,
returning `selected_unit_verified`) or `{"kind": "crate"}` (`CrateTheorem`,
returning `crate_verified`), and list the `specification` and `proof` Lean
modules under `proof.sources`. For a Cargo crate with a single library or
binary target and no required normal or build dependencies (dev-dependencies
and inactive optional dependencies are ignored),
`--manifest-path <Cargo.toml>
--proof-dir <dir>` (with optional `--no-default-features`, `--features <list>`,
`--all-features`, `--panic unwind|abort`, `--overflow-checks`,
`--select <path>`, and `--instantiate <JSON>`) constructs the same request
automatically.

The `--manifest-path` shortcut fails closed on Cargo configuration that could
change how the crate is compiled. Inside the package and its workspace (from
the package directory up to the workspace root), a `.cargo/config` or
`.cargo/config.toml` may contain only the `[alias]`, `[term]`, `[doc]`,
`[cargo-new]`, and `[future-incompat-report]` tables. The shortcut also
inspects ancestor directories strictly above the workspace root and the active
`$CARGO_HOME/config{,.toml}` (failing closed on compilation, toolchain, and
download overrides while admitting `[net]`, `[registries]`, `[registry]`, and
`[source]` so offline and vendored host setups keep working), and pins child
`cargo metadata` processes to that exact inspected `$CARGO_HOME`. Any other
table (for example `[build]`, `[target]`, `[profile]`, `[env]`, `[patch]`,
`[http]`, or `[install]`), unparseable TOML, or a symlinked or non-regular
config file, `.cargo` directory, or `$CARGO_HOME` directory is refused as
`unsupported`. A `rust-toolchain` or `rust-toolchain.toml` file in the resolved
ancestry of `$TMPDIR` (the temporary working directory used to run
`cargo metadata`) is likewise refused; clear `$TMPDIR`, point it at a clean
directory, or write an explicit `request.json` instead.

Each `instantiations` entry, like each `--instantiate` value, names a generic
function of the crate being verified by its `rustc` path (`path`) and lists
its generic arguments in Rust syntax (`args`): primitive types, `str`, tuples,
arrays, slices, references, raw pointers, paths to structs, enums, unions, and
type aliases, `bool`, `char`, and integer constants, and lifetimes. `'static`
is the only lifetime a request can name, and `'_` means `'static`. A bare
primitive name (`u8`, `bool`, `str`, and so on) always means the primitive
type, even when the root of the crate being verified declares a type of that
name; `crate::u8` names the latter. Any other type path resolves as follows:

- `crate::a::B` starts at the root of the crate being verified, and
  `::krate::a::B` at the root of the crate named `krate`.
- A request has no enclosing module, so the first segment of any other path
  is read two ways: as a crate name (an external crate, or the crate being
  verified by its own name), continuing from that crate's root, and as a name
  at the root of the crate being verified. The path resolves only if the
  readings that resolve all name one definition; otherwise the request is
  refused as ambiguous. In `zerocopy`, `byteorder::BigEndian` names the
  `BigEndian` type of the `byteorder` module. In a crate whose root declares
  `mod core` with its own `num::Wrapping`, `core::num::Wrapping<u8>` is
  refused.
- Each segment before the last must name a module, and the last a struct,
  enum, union, or type alias. A segment that names anything else in the type
  namespace, such as a trait, a re-exported primitive type, or a struct or
  enum before the last segment, refuses the request.
- A reading that reaches a segment naming nothing in the type namespace may
  instead spell how `rustc` prints a local definition, such as `f::Local` for
  a type declared inside function `f`, or `_::Local` for one declared inside
  `const _: () = { ... };`. No path that also reads as an external crate's
  path resolves this way.
- A `_` segment never names an underscore import such as `use m as _;` or
  `extern crate k as _;`, which no Rust path can name.
- A name that glob imports make ambiguous in a module, whether of the crate
  being verified or of another crate, makes every path through it ambiguous.

A type alias in a request means what it would mean where Rust code uses it:
its expansion must be well-formed and must normalize, including any lifetime
and higher-ranked obligations that normalizing incurs. A lazy type alias
(`#![feature(lazy_type_alias)]`) must also satisfy its own bounds; as in Rust,
the bounds of an ordinary type alias are not enforced.

## Stage 0 / MIR Profile v1: supported vs. refused

The alpha runs on the x86-64 Linux scalar MIR profile (Profile v1) with
`-Zmir-preserve-ub` (`#4114`) and `-Zmir-opt-level=0` enforced during capture.
Any construct outside this profile returns an explicit fail-closed refusal
rather than approximating semantics, unless it belongs to the experimental
[Profile v2](#experimental-mir-profile-v2-borrowed-slices-and-raw-pointers).

| Category | Supported today (Profile v1) | Refused today (fail-closed) |
| :--- | :--- | :--- |
| **Types** | `bool`, `char`, 8- through 128-bit and pointer-sized integers (`i8`..`i128`, `isize`, `u8`..`u128`, `usize` on 64-bit targets), `()`, `!`, `core::cmp::Ordering`, `(T, bool)` overflowing-arithmetic pairs (via `core::intrinsics::*_with_overflow`), and non-generic inhabited crate-local fieldless enums (including pure scalar explicit discriminants). | References and raw pointers (`&T`, `&mut T`, `*const T`, `*mut T`), slices, arrays, structs, unions, enums with payloads, uninhabited zero-variant enums, enums whose size or alignment differs from their tag's (such as `#[repr(u8, align(4))]` or `#[repr(align(8))]`), floats, general tuples, and generic types. |
| **Statements & rvalues** | `Assign` (`Use` on retag-noop scalar types, unary `Not`/`Neg`, binary bitwise/shift/wrapping-arithmetic/unchecked-arithmetic/`*WithOverflow`/comparison/`Cmp`/unchecked `Div`/`Rem`, `CastKind::IntToInt`, `Discriminant`), `StorageLive`, `StorageDead`, bare unprojected `PlaceMention`, and `Nop`. | Place projections (fields, indexing, dereferencing, projected `PlaceMention`), `Aggregate` rvalues, `PtrMetadata`, pointer/float/`Transmute` casts, and inline assembly. |
| **Terminators & operands** | `Goto`, `SwitchInt`, `Return`, `Unreachable`, returning direct `Call` terminators to non-generic intra-crate functions (non-`Use` `CallSource`, non-cleanup unwind, and supported scalar/unit signature), diverging calls (`TerminatorKind::Call` with `target: None` and non-`Use` `CallSource`, lowered to fail-closed `unsupported` when reachable), primitive `Assert` terminators (`DivByZero`, `RemByZero`, `Overflow(Div | Rem)`, `BoundsCheck`, `MisalignedPtrDeref`, and `NullPtrDeref`) with Profile v1 conditions (modeled via `evalAssertFailure`: `MisalignedPtrDeref` and `NullPtrDeref` fault `.undefined`; the other safe assertions abort under `--panic abort` without a crate-local `#[panic_handler]` on non-cleanup unwinds and otherwise fault `.unsupported`), and closed `core::num` `sysrootCall` arithmetic (`unchecked_{add,sub,mul}` under `-Cdebug-assertions=no -Coverflow-checks=no` with UB checks off, and `wrapping_{add,sub,mul}`; `usize::unchecked_sub` instead takes the Profile v2 `core` call path below); `Copy`/`Move` on unprojected locals; scalar constants (including `Const::Unevaluated`, `Const::Ty(Value)`, and read-only provenance-free `.rodata` `ConstValue::Indirect` / `GlobalAlloc::Memory` scalars evaluated via CTFE alongside `required_consts`) and `ZeroSized` unit/single-variant-enum constants. | Indirect, closure, trait-object, generic, or unsupported external calls (including `overflowing_*` methods under `-Copt-level=0`), intra-crate calls to `#[track_caller]` functions or to `unsafe fn`s (refused at entry because callee safety contracts are not yet checked at call sites), calls with cleanup unwind edges, and `CallSource::Use`, optional arithmetic overflow `Assert` terminators (`Overflow(Add | Sub | Mul | Shl | Shr)` and `OverflowNeg`, which select Profile v2), `Drop`, unwind/abort terminators, and constants whose CTFE evaluation fails or refers to `static`, mutable, or provenance-bearing memory. |
| **Crate scope & items** | Single `lib` or `bin` crates (a `lib` crate may restate its type as `#![crate_type = "lib"]` or `"rlib"`) with no required normal or build dependencies, no `cfg(miri)`, and no active unstable `#![feature(...)]` attributes unless named by `--allow-unstable-feature` (which taints; inactive `#![cfg_attr(..., feature(...))]` lines other than `rustc_private` are permitted, and already-stabilized language features are admitted untainted and recorded in `configuration.stabilized_features_present`; dev-dependencies and inactive optional dependencies are ignored; `Scope::Crate` or `Scope::SelectedUnit`, Cargo `[features]` via `--features`/`--all-features`/`--no-default-features`, configurable `--panic unwind|abort`, and crate-local `#[panic_handler]` in `bin` selected-unit scope), plus opt-in `--stdlib-crate core` (requires `Scope::SelectedUnit`, a `lib` crate, `crate_name == "core"`, a compilation that loads no other crate, no `cfg(miri)`, only `core`'s version-pinned `#![feature(...)]` allowlist, and any crate-local `Ordering` language item to have the modeled shape; admits `core`'s own `#[lang]` items and skips object emission); non-generic free and associated functions (and, in `Scope::Crate`, safe `trait` declarations, safe `impl` blocks, bodyless safe Rust-ABI trait methods (including `#[inline]` hints, which rustc ignores there), non-generic pure-value `const`/`assoc const` items, and pure scalar `AnonConst` items), plus explicitly requested concrete monomorphizations (`instantiations` / `--instantiate`) in `Scope::SelectedUnit`. | Required normal or build external crate dependencies, multi-target crates, `cfg(miri)` on any crate, any active unstable `#![feature(...)]` attribute on normal crates that `--allow-unstable-feature` does not name (unstable lang and lib features, including library features `rustc` has since stabilized; compiler-internal features, `ergonomic_clones`, and `rustc_private` are refused even when named; `--stdlib-crate core` refuses any feature outside its version-pinned `core` allowlist), uninstantiated polymorphic generics, closures, crate-local `#[lang]` items without `--stdlib-crate` (except `#[panic_handler]` in `bin` selected-unit scope), `struct`/`union`/`static`/`InlineConst` owners, bodyless free functions, and `unsafe`/unmodeled `trait`/`impl`/`const`/`AnonConst` items in whole-crate scope, exported (`#[macro_export]`, `pub macro`, or publicly re-exported) macros, other `#![crate_type]` attributes, crate-root `#![cfg_attr]` or `#![feature]` attributes whose arguments capture cannot parse (such as non-literal values), `unsafe(..)`-wrapped `feature`/`crate_type` items under `#![cfg_attr]`, global assembly, and proc-macro crates. |

For a realistic scalar example, `ci/verify_starnix_e2e.py` checks Starnix's
`ebpf_core` endianness conversion using symbolic MIR helpers in `Anneal.MirWp`.

## Experimental MIR Profile v2: borrowed slices and raw pointers

Capture selects Profile v2 (`mirProfileVersion = 2`) for the whole captured
program when any captured body uses one of its additions; a program without
them stays on Profile v1. When capture refuses a Profile v1 call in a Profile
v2 program, its diagnostic names the refused call and the first body and
construct requiring Profile v2. Every body of a Profile v2 program, including
scalar-only ones, is checked against `UnitTheoremV2` or `CrateTheoremV2`. Its
receipt lists an "experimental Profile v2 MIR semantics" assumption and marks
`correspondence_provenance` inapplicable, because Pass 2 relates only Profile
v1 rules to `vendor/lean-miri/`.

| Category | Added by Profile v2 | Refused (fail-closed) |
| :--- | :--- | :--- |
| **Types** | General tuples and `Range<usize>`, `RangeTo<usize>`, and `RangeFrom<usize>` locals; supported `Option<T>` (`bool`, `()`, `&T`/`&mut T`/`&[T]`, integers, raw pointers); fixed arrays `[T; N]` whose element type is a Profile v1 scalar, `()`, an admitted enum, or a nested fixed array thereof; single-level `&T`, `&mut T`, `*const T`, and `*mut T` (whose pointee is a sized ref-free non-tuple/non-range type, including an admitted fixed array `[T; N]`, or a slice `[T]` of sized ref-free elements), plus shared `&str`; lifetime-only generic signatures. | Nested references or pointers (`&&T`, `*const &T`, `&[&T]`, `[&T; N]`, `&Option<&T>`), fixed arrays of tuples, overflow pairs, references, or raw pointers, tuples/overflow pairs/ranges behind `&`/`*const`/`[]`/`Option` (whose unspecified `#[repr(Rust)]` layout capture does not check, so they stay non-addressable), nested `Option<Option<T>>`, `Option<char>`, `Option<Ordering>`, `Option<Enum>` (including over-aligned enums whose layout differs from their tag), `&mut str`, `*const str`, `*mut str`, bare unsized `str`, structs, and the remaining Profile v1 refusals. |
| **Bodies** | Bodies whose locals include references or raw pointers, but not both (exempting compiler-synthesized `*const` temporaries written solely by `RawPtrKind::FakeForPtrMetadata` and read solely by `PtrMetadata`). | Bodies whose locals mix references and non-`FakeForPtrMetadata` raw pointers, because Profile v2 does not model Rust's pointer aliasing rules (Stacked or Tree Borrows). For example, `<&mut [u8] as SplitByteSlice>::split_at_unchecked`, which uses `as_mut_ptr` and `from_raw_parts_mut`, is refused. |
| **Statements & rvalues** | `Ref` of locals and of dereferenced references, `RawPtr` (address-of) of locals and of dereferenced raw pointers, `RawPtr(FakeForPtrMetadata)` of dereferenced references or raw pointers into metadata-only `PtrMetadata` temporaries, assignment through projected and dereferenced places (field and `ConstantIndex`), raw-to-raw `PtrToPtr` casts that do not add mutability, `IntToPtr` casts, array-to-slice `Unsize` casts (`&[T; N]`, `&mut [T; N]`, `*const [T; N]`, `*mut [T; N]` without adding mutability), `PtrMetadata`, `Offset`, `Range`/`RangeTo`/`RangeFrom`/`Option` aggregates, `Option` `Discriminant`/`Downcast`, array aggregates and `Repeat`, `ConstantIndex` projections, copy reads of tuple, overflow-pair, array, range, and option fields (including field and `ConstantIndex` projections after a dereference), moves of tuple and overflow-pair fields out of locals (which deinitialize only the moved field), projected `Discriminant` reads (including through references and nested projections), read-only provenance-free rodata array and reference constants (returning them fails closed), and `Use` with retags. | General reference-to-raw-pointer and raw-pointer-to-reference conversions (refused with the mixed-locals rule), non-`PtrMetadata` uses of `FakeForPtrMetadata` temporaries, `*const T` to `*mut T` casts and mutability-upgrading `Unsize` casts (Profile v2 cannot tell whether the pointee is an immutable binding, which the cast would let the body mutate), other unsupported casts, index projections, unsupported projections after a dereference, other projected moves (`move (*p)`, nested fields, `Option` downcast moves, `ConstantIndex` moves), piecemeal projected initialization of an uninitialized immediate local (fails closed with `.unsupported` at runtime), returning references or pointers to callee rodata allocations, and unsupported aggregates. |
| **Terminators** | `Assert` terminators and returning calls to the closed-set `CoreCallOp`s (`<[T]>::{len, is_empty, split_at, split_at_mut, get_unchecked, Index/IndexMut<Range<usize>>, Index/IndexMut<RangeFrom<usize>>}`, `<*const/*mut T>::add`, `usize::unchecked_sub`, integer `is_multiple_of`, `checked_{add,mul,sub}`, `saturating_add`, `wrapping_{shl,shr}`, `leading_zeros`, `overflowing_{add,sub}`, and `to_le_bytes`, `cmp::{min,max}`, `mem::replace`, `Option::{is_some,is_none,take,unwrap}`, and `<[T; N] as PartialEq>::eq` for integer, `bool`, `char`, `()`, `Ordering`, and nested-array elements; enums are refused), plus—only under `--panic abort` without a crate-local `#[panic_handler]`—diverging `core::panicking::{panic, panic_nounwind}` (evaluating their shared `&str` message operand). Lowering those `core::panicking` calls under `--panic abort` selects Profile v2 for the program (so Profile v1 intra-crate and `core::num` sysroot calls are refused in the same program); under `--panic unwind` or with a crate-local `#[panic_handler]`, those diverging calls stay `Terminator::Unsupported` (Profile v1-eligible). The captured `UnwindAction` (`Continue`, `Unreachable`, or `Terminate`) is recorded as is. Under opt-in `--panic abort` (when the crate defines no crate-local `#[panic_handler]`), failing non-optional safe `Assert`s and admitted `core::panicking::{panic, panic_nounwind}` calls terminate as `.aborted` carrying post-mutation `CallerMemory`; this satisfies `BodyVerifiedV2` without a termination claim and leaves panic hooks and handlers (including downstream `#![no_std]` binary `#[panic_handler]`s) unverified (recorded in receipt assumptions), so proving panic-freedom requires an explicit `EffectMaskV2.noAbort` `SafeContractV2` obligation in `SpecsV2.property`. Failing optional overflow checks abort the same way under `--overflow-checks`; under default `-Coverflow-checks=no`, where codegen elides them, they stay `.fault .unsupported`. Crates with a crate-local `#[panic_handler]`, cleanup unwinds, and `--panic unwind` keep failing safe `Assert`s and `core::panicking::{panic, panic_nounwind}` calls fail-closed as `.fault .unsupported`. | Every other call (including `<[T]>::{as_ptr, as_mut_ptr}` and `core::slice::from_raw_parts{,_mut}`, which convert between references and raw pointers, `core::panicking::panic_fmt` including formatted panics and custom `assert!(cond, "...")` messages, and Profile v1 intra-crate and `core::num` sysroot calls), calls in crates that shadow `core`, and cleanup unwinds. |

Notes on Profile v2 coverage and traps:

- **Local-only types:** General tuples, overflow pairs `(T, bool)`, and
  `Range<usize>` / `RangeTo<usize>` / `RangeFrom<usize>` are `#[repr(Rust)]`
  and subject to `rustc` field reordering, so Profile v2 restricts them to
  locals and refuses references, raw pointers, slices, or `Option` wrappers
  over them.
- **21 `core` contract ops (`CoreContracts`):** Beyond the 7 base pointer and
  slice ops, Profile v2 adds checked, overflowing, saturating, and wrapping
  scalar arithmetic, `is_multiple_of`, `leading_zeros`,
  `core::cmp::{min, max}`, `core::mem::replace`,
  `Option::{is_some, is_none, take, unwrap}`, and slice `is_empty`, `split_at`,
  `split_at_mut`, `Index<Range<usize>>`, and `Index<RangeFrom<usize>>` (where
  out-of-bounds slicing or `Option::unwrap` on `None` fail closed via
  `corePanicTrap`).
- Each query (`Query`) supplies caller memory (`callerMem`) alongside its
  arguments. `SpecsV2` pairs per-function safety preconditions (`safety`,
  required only of `unsafe` functions) with a whole-program `property`.
  `ValidEntryArgsV2` requires live, in-bounds, aligned, initialized reference
  arguments in caller allocations whose bytes decode to valid pointee values,
  and disjoint mutable references. This applies to `unsafe` functions too, so a
  receipt says nothing about callers that pass an `unsafe` function a reference
  to uninitialized or invalid memory; receipts state this assumption.
- Raw pointer arguments are unconstrained, so an `unsafe` function's `safety`
  precondition must state their liveness, bounds, alignment, initialization, and
  mutability. Mutability here means the allocation's mutability: Profile v2
  does not track pointer aliasing permissions, so callers must also pass raw
  pointers whose provenance permits the accesses the function makes (for
  example, not a pointer derived from a live `&T` that the function writes
  through). Profile v2 encodes memory little-endian and assumes natural ABI
  alignment (1, 2, 4, 8, and 16 bytes for `i8` through `i128`, 8 bytes for
  `isize` and pointers, and no added aggregate alignment). Capture admits only
  targets whose data layout matches.

Profile v2 also models `alloc::vec::Vec<T>` and `alloc::boxed::Box<P>` with the
`Global` allocator, for scalar or `()` elements and pointees
(`Trusted.MirSemantics.AllocContracts`):
`Vec::{new, with_capacity, len, push, reserve, resize, extend_from_slice}`,
`Vec` indexing by `usize` and dereferencing, `Box::new`,
`Box::<[T]>::from(Vec<T>)`, `Box::clone`, and `Box` dereferences. A capacity
overflow or an out-of-bounds index is a panic, which Profile v2 does not model,
so a proof must rule it out. The model assumes that allocation never fails: it
does not model the out-of-memory path (`handle_alloc_error`), and receipts
record this assumption. References to `Vec` and `Box` handles are admitted, but
raw pointers to them are refused, because Rust leaves the layout of `Vec`
unspecified. A `Box` counts as a reference for the rule against mixing
references and raw pointers, because the aliasing models retag it like a unique
reference: `Box` dereferences yield `&P`, and a body that derives a raw pointer
from a `Box` is refused. Entry arguments that own a heap buffer must point at
the start of an allocation with exactly the buffer's layout. An owned `Vec` or
`Box` buffer counts as a mutable span in the entry and return disjointness
checks. The buffer behind a reference to a `Vec` or `Box` handle is not checked
against other spans; receipts state its disjointness from that handle and from
every other argument as an assumption, so results say nothing about calls in
which such a buffer aliases its handle or another argument (for example, a
`&[u8]` into the buffer of a `&mut Vec<u8>` argument). Under `--panic abort`,
the caller memory that post-abort conditions see omits heap buffers that the
call allocated. Returning a reference into the buffer of a `&mut Vec<T>`
argument that reallocated during the call faults with `.undefined`, because
returned references must point into the caller's entry allocations; this is
conservative. On return, the caller memory that `post` sees also contains the
heap buffers the call allocated and did not free, such as the buffer of a
returned `Box` or of a `Vec` that grew through a `&mut Vec<T>` argument. Slices
`&[T]` and `*const [T]` of every scalar or `()` element type are admitted local
types, although `<[T]>::len` and the other slice functions above still require
integer elements.

`tests/cargo-anneal/tests/profile_v2_e2e.rs` verifies the unmodified
`zerocopy/src/byte_slice.rs` `<&[u8] as SplitByteSlice>::split_at_unchecked`
under `UnitTheoremV2`, raw-pointer load and store fixtures under
`CrateTheoremV2`, `core` range/slice/`Option`/`mem::replace`/scalar contract
fixtures in `tests/cargo-anneal/tests/fixtures/profile_v2_core_contracts/`,
and the runtime overflow check fixtures below.

### Runtime overflow checks

By default capture compiles with `-Coverflow-checks=no`, so `+`, `-`, `*`,
and unary `-` wrap and `<<` and `>>` mask their shift amount, as in a default
release build. `--overflow-checks` (request field
`compilation.overflow_checks: true`) captures with `-Coverflow-checks=yes`
instead, matching builds that enable overflow checks (such as default debug
builds). Rustc then guards each of those operations with an `Assert`
terminator, so such bodies use Profile v2. Under `--panic unwind` a failed
check faults, so a verified theorem proves that no overflow check fires on any
admitted input. Under `--panic abort` (without a crate-local
`#[panic_handler]`) a failed check aborts like the other safe panics, so a
panic-freedom proof needs a `SafeContractV2` with `EffectMaskV2.noAbort`.
Capture records the setting as `configuration.overflow_checks` in
`capture.json` and in the receipt, and as `Program.overflowChecks` in
`Captured.lean`, which specifications can pin. `--overflow-checks` is refused
together with `--stdlib-crate`. Verify the setting against the deployed
build: a proof without `--overflow-checks` says nothing about a build in which
overflow panics, and vice versa.

### Bundled proof libraries and specification boundaries

- **Proof modules:** May import any of the bundled 3-axiom `Anneal.*` proof
  libraries listed in
  [`theory/bundle-manifest.json`](../theory/bundle-manifest.json) (such as
  `Anneal.MirWp`, `Anneal.LoopInv`, `Anneal.BitVec`, and `Anneal.ClassicalEm`),
  which are compiled and audited on demand when imported. Other experimental
  modules under `theory/Anneal/` that are not in `theory/bundle-manifest.json`
  are not bundled into `cargo-anneal`.
- **Specification modules:** Stay restricted to `Trusted.*`, `Init.*`/`Std.*`,
  and declared `specification` helpers.

On Lean `v4.35.0+` toolchains bundling `leanexport`, `nanoda_bin`, and
`con-ron` (with `--allow-unpinned-lean`), `cargo-anneal` verifies proofs via
the out-of-process Universal NDJSON Comparator rather than in-process
`.olean` replay; pass `--paranoid-quorum` to also cross-check with `con-leche`
and `lean4lean`.

Verify the stated compilation configuration in the receipt when comparing a
result with a deployed binary. See the [threat model](../THREAT_MODEL.md) for
the verification assumptions.

## Build-system and toolchain options

Build systems such as Bazel or GN that already resolve crate inputs and Lean
module mappings can invoke `verify rustc` directly instead of writing a
`request.json` file:

```sh
cargo anneal verify rustc /path/to/src/lib.rs \
  --crate-name scalar --edition 2024 \
  --source-file /path/to/src/helper.rs \
  --spec-file Spec=/path/to/spec/Spec.lean \
  --proof-file Proof=/path/to/proof/Proof.lean \
  --spec-decl Spec:Spec.specs --theorem Proof:Proof.verify \
  --select module::function --artifacts /path/to/evidence
```

`verify rustc` dereferences symlinks when staging regular source files so
symlinked runfiles trees work directly, while still rejecting special files and
concurrent source edits. Additional flags support build-system and custom
toolchain integration:

- `--export-lean-lib` (requires `--artifacts <directory>`): atomically stages
  Door-1-verified target `.olean` files inside the private work directory and
  retains them under `<artifacts>/lean-lib/` after target audit passes; omits
  authored `proof` `.olean`s on `proof_failed` (exit `1`)—including authored
  `Proof`-module deterministic heartbeat or recursion-depth limit failures,
  which classify as `proof_failed` with structured `"reason"`
  (`"heartbeat_limit_exceeded"` or `"recursion_depth_exceeded"`) so non-proof
  `.olean`s remain exported for debugging while negative and mutation checks
  refuse to credit them as kills—and exports nothing on `tool_failed`
  (exit `2`).
- `--lean-memory-mb <MB>`: sets Lean's `-M<MB>` memory limit (`resolve-imports`
  enforces a `4096` MiB floor).
- `--max-inspector-output-bytes <BYTES>`: sets the maximum Lean inspector
  `result.json` output size in bytes (`67108864` / `64 MiB` by default, up to
  `1073741824` / `1 GiB`; also raises child `RLIMIT_FSIZE` when set above
  `256 MiB`).

Parallel Lean compilation uses a bounded number of workers. By default it uses
the smaller of the host's available parallelism and a built-in cap. Setting
`ANNEAL_COMPILE_WORKERS=<n>` (a positive integer) requests `n` workers, still
bounded by available parallelism (standalone NDJSON kernel verification with
`con-ron` and `con-leche` remains hard-capped at `2` jobs); invalid or
non-positive values are ignored. The worker count is then limited to one worker
per `4096` MiB of memory (never fewer than one worker), using the tighter of
`ANNEAL_LEAN_RUN_MEM_MB=<MB>` and, on Linux, the cgroup v2 `memory.max` of the
current cgroup and its ancestors, so concurrent Lean workers stay within a
container or job memory budget. An invalid or non-positive
`ANNEAL_LEAN_RUN_MEM_MB` is ignored.

When building `cargo-anneal` itself with Cargo's `--no-default-features` flag
(for example, `cargo install --locked --no-default-features cargo-anneal`), the
default `setup` feature and remote archive download support (`exocrate`) are
omitted, so pass explicit `--capture`, `--sysroot`, and `--lean` paths to
`verify`. On `cargo anneal verify --manifest-path`, `--no-default-features`
instead disables default features of the target crate being verified.

Each `--allow-*` relaxation flag follows Receipt Schema v3's Uniform
Flag-Driven Taint Law: passing the flag prints a `TAINTED` warning banner on
stderr, adds its sorted entry to `taint_reasons` even on clean runs, and
switches passing status to `tainted_crate_verified` or
`tainted_selected_unit_verified`:

- `--allow-unpinned-lean` (requires explicit `--lean <path>`): adds
  `"unpinned_lean"`, dynamically discovers and hashes the minimal `Init.*` and
  `Std.*` sysroot import closure (recorded in `unpinned_lean` and
  `audit.unpinnedLean`), and marks `correspondence_provenance.applicable` as
  `false`.
- `--allow-unsandboxed-elaboration`: adds `"unsandboxed_elaboration"`, disables
  `ExecSeal` (`"elaboration_sandbox": "none"`), and retains `"hostile Lean
  elaborator effects"` in `deferred`.
- `--allow-sorry-in-proof`: adds `"sorry_in_proof"`, permits `sorry` strictly
  in authored `proof` modules outside Phase 1 (never in `specification`,
  `Model`, `Capture`, or `Expected` modules; `"spec-preflight"` also enforces
  pure declarative syntax on `specification` modules), and records
  `sorry`-using proof declarations in `sorry_declarations`.
- `--allow-unstable-feature <NAME>` (repeat or comma-separate; no wildcards):
  adds `"unmodeled_unstable_features"`, admits exactly the named unstable
  `#![feature(...)]` gates on a normal crate (never with `--stdlib-crate`), and
  records a top-level `unstable_features` object (`allowed`, the enabled
  `observed` subset, and the `incomplete_observed` subset that `rustc` marks
  incomplete) plus a static assumption that their semantics are unmodeled.
  Compiler-internal features (as `rustc` classifies them), `ergonomic_clones`,
  and `rustc_private` stay refused. Gate CI on the exact feature set with
  `cargo anneal inspect --allowed-unstable-features <NAME,...>` (which admits
  that taint and no other) and optionally
  `--forbid-incomplete-unstable-features`.

## Inspect receipts offline

Run `cargo anneal inspect <receipt.json>` (including under
`--no-default-features`) to validate Receipt Schema v3 cross-checks, compute the
6-axis assurance profile, compare two receipts with `--diff <BASE> <HEAD>`
(`--no-regressions`), or verify local retained artifact hashes with
`--verify-artifacts <DIR>`. Bare single-receipt `inspect` fails closed on
failed, tainted, or warn-mode extension receipts (`exit 1`, or `exit 2` with
`--unknown-fields deny`). Under `--diff <BASE> <HEAD>`, invariant violations
and default warn-mode extension fields also fail closed (`exit 1`, or `exit 2`
with `--unknown-fields deny`), while `--no-regressions` gates on Tier A
assurance downgrades. Pass `--passive` to inspect receipts without status,
taint, or warn-mode extension gating (invariant, artifact, and
`--compare-ledger` failures still exit `1`). Pass
`--max-receipt-bytes <BYTES>` (`67108864` / `64 MiB` by default, up to
`1073741824` / `1 GiB`) to inspect or diff larger receipts. Note that `inspect`
checks internal consistency and local digests offline and does not
cryptographically authenticate external receipts.

## Install a published alpha

Replace `<version>` with the semver version from a published `anneal-v<version>`
prerelease tag on GitHub Releases (for example, `0.2.0-alpha.11`, without the
`anneal-v` prefix; `main` stays at `0.0.0-dev` with an all-zero archive digest
rather than tracking published release metadata, so when running from a source
checkout use `cargo anneal setup --local-archive target/omnibus-link` as shown
in [Try a proof](#try-a-proof) above):

```sh
cargo install --locked cargo-anneal@<version>
cargo anneal setup
cargo anneal verify --request /path/to/scalar/request.json
```

To install the alpha alongside an earlier version of `cargo-anneal`, use
`cargo install --root <directory>` and invoke
`<directory>/bin/cargo-anneal` directly.

## Cut the release

Before the first publication, create the GitHub environment `anneal-release`
with required reviewers and a deployment branch rule allowing only `main`.
In the crates.io settings for `cargo-anneal`, add a
trusted publisher for `google/zerocopy`, workflow `release.yml`, and
environment `anneal-release`.
Verify that the `zerocopy` and `zerocopy-derive` registrations for
`release.yml` explicitly require their `release` environment. These
environment bindings keep credentials scoped to each publication job.
See [crates.io Trusted Publishing](https://crates.io/docs/trusted-publishing).

1. Run **Release** (`workflow_dispatch`) on `main`. Select `anneal`, enter the
   desired `0.2.0-alpha.<N>` version (such as `0.2.0-alpha.13`), keep `branch`
   set to `main`, and optionally pass a 40-character first-parent `main`
   `commit` SHA (leave blank to release current `main` `HEAD`). On `main`,
   `trusted/cargo-anneal/Cargo.toml` and `Cargo.lock` remain at `0.0.0-dev`
   with an all-zero archive digest; cutting a release opens no pull request and
   pushes no commits to `main`.
2. Wait for `anneal-build-archive`, `anneal-host-archive`, and
   `anneal-qualify-package` to finish on Ubuntu 24.04. Running release
   scripts and composite actions from the dispatched `main` workflow revision,
   the workflow resolves and pins the target commit SHA, builds the
   `x86_64-unknown-linux-gnu` omnibus archive from an isolated detached
   checkout of that commit, publishes it to a commit-and-digest-addressed
   GitHub prerelease (`anneal-toolchain-<commit12>-<sha256_16>`) after
   verifying GitHub's asset SHA-256, checks `anneal-release` environment
   protections, stamps the isolated target checkout in place, installs the
   packaged `.crate`, runs remote `cargo anneal setup` twice, and runs
   `ci/probe_alpha.py`.
3. Verify the resolved commit SHA, hosted toolchain digest, and qualification
   log, then approve the `anneal-release` deployment. Because `main` remains
   unpinned (`anneal-v<version>` tags commit `C`), `anneal-release` approvers
   act as the human review gate for the stamped release metadata before
   crates.io upload. `anneal-publish-crate` re-verifies SemVer ordering, live
   hosted archive integrity, and exact packaged source parity, publishes
   `cargo-anneal` from a freshly stamped clean checkout via OIDC, and verifies
   the uploaded `.crate` and crates.io checksum; `anneal-publish-github` tags
   `C` as `anneal-v<version>` and publishes path-scoped GitHub Release notes.

Concurrent merges to `main` do not disturb an in-flight release, and failed
qualification or rejected deployment approvals leave the SemVer version
reusable on a subsequent commit. `resolve-and-validate` checks `anneal-v*` Git
tags on `origin/main` first-parent history against un-yanked `crates.io`
versions: it fails closed if the target `anneal-v<version>` tag already exists
without a matching `crates.io` release or if any un-yanked `crates.io` release
strictly above the highest existing `anneal-v*` tag (`0.2.0-alpha.11` and
subsequent tagged releases) lacks a first-parent `anneal-v*` tag on `main`,
while tolerating four older untagged historical releases below that
high-water mark (`0.1.0-alpha.10`, `0.1.0-alpha.11`, `0.1.0-alpha.24`, and
`0.2.0-alpha.1`).
Post-crate recovery re-dispatch applies to commit-bound releases
(`anneal-toolchain-<C12>-<D16>`): if a transient failure occurs during archive
hosting, qualification, or GitHub Release creation, rerun the failed jobs within
the 24-hour (`retention-days: 1`) `upload-file-artifact` window; once that
artifact expires (or after `cargo publish` succeeds), dispatch **Release** again
for the same commit and version to rebuild or complete `anneal-v<version>`
against the published crate's commit and toolchain digest. If any un-yanked
`crates.io` release strictly above the highest `anneal-v*` tag lacked its
`anneal-v<version>` tag, push that tag onto its first-parent release commit
manually before dispatching a newer version.
