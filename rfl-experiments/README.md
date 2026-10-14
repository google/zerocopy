<!-- Copyright 2026 The Fuchsia Authors -->
<!-- SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT -->

# Zerocopy experiments for Rust for Linux

Six host-side prototypes exercise opportunities identified in Linux at
[`0fcb05b72344`](https://github.com/torvalds/linux/tree/0fcb05b72344f40806cbe810de8872f1698bf053).
They use this branch's zerocopy projection machinery. Linux's existing
vendored zerocopy is not substituted for it.

## Run the demo

From the repository root:

```sh
./rfl-experiments/setup-linux.sh
./rfl-experiments/run.sh run --example demo
./rfl-experiments/run.sh
```

Setup fetches a pinned, shallow, sparse Linux checkout into `rfl-linux/`.
That checkout is ignored by Git. Setup refuses to overwrite an existing
checkout at another revision or with local changes.

The run script uses zerocopy's repository-controlled Cargo wrapper. It may
install a missing pinned Rust toolchain. After setup, experiment dependencies
are local and Cargo runs offline with the committed lockfile. The wrapper's
own tooling bootstrap may still require its normal Cargo cache/network access.

Useful individual demonstrations:

```sh
./rfl-experiments/run.sh test --lib address_projection
./rfl-experiments/run.sh test --lib binder
./rfl-experiments/run.sh test --lib conversions
./rfl-experiments/run.sh test --lib typed_init
./rfl-experiments/run.sh test --lib device_ids
./rfl-experiments/run.sh test --lib firmware
./rfl-experiments/run.sh test --doc
RFL_TOOLCHAIN=nightly ./rfl-experiments/run.sh miri test --lib
```

The Miri command first prepares its standard-library sysroot outside the
repository's vendored Cargo configuration. That one-time setup may download
standard-library dependencies; the experiment itself remains offline.

## The six prototypes

| Prototype | Existing RfL code | Demonstrated replacement |
|---|---|---|
| [`address_projection`](src/address_projection.rs) | `rust/kernel/ptr/projection.rs` | Field descriptors computed with `offset_of!`, raw-address projection, runtime slice indexing/ranges, and an adapter to zerocopy's `Project` |
| [`binder`](src/binder.rs) | `drivers/android/binder/{defs,allocation,thread}.rs` | Initialized byte storage with shared `ReadOnly` union projections and exclusive scalar writes |
| [`conversions`](src/conversions.rs) | `rust/kernel/transmute.rs`, `samples/rust/rust_dma.rs` | Safe facades retaining RfL method names, backed by zerocopy traits and conversion APIs |
| [`typed_init`](src/typed_init.rs) | `rust/pin-init/src/__internal.rs`, `internal/src/pin_data.rs` | Typed slots and drop guards, with a concrete disjoint-field split inside real RfL pin-init |
| [`device_ids`](src/device_ids.rs) | `rust/kernel/device_id.rs`, `rust/kernel/pci.rs` | A typed context-field descriptor, a provenance-preserving const table, and an exact runtime wrapper cast |
| [`firmware`](src/firmware.rs) | `drivers/gpu/drm/tyr/fw/parser.rs` | Borrowed little-endian wire headers with explicit semantic validation |

### Raw-address projection

`field_descriptor!` emits a layout offset and a field-type witness; it does not
allocate a dummy object. `AddressProject` never accesses memory and accepts
null, wrapping, and MMIO addresses. `InAllocation<P>` adapts the same descriptor
to the existing `Project<Src, Dst>` contract without weakening `PtrInner`.

Tests compare field/index results with the unchanged Linux projection source.
Its host shim substitutes panic for Kbuild's build-error mechanism; compile-time
Kbuild error behavior is not covered. Packed projections are supported without
claiming alignment. Compile-fail examples reject wrong field types and implicit
`Deref`. This descriptor macro covers sized fields; unsized field descriptors
and integration into RfL's I/O backends remain future work.

### Binder

The model follows the Binder ABI with `BINDER_IPC_32BIT` disabled. It supports
handle and buffer objects, not every Binder tag. Their layouts are represented
as C structs/unions; owned byte storage holds a fully initialized snapshot.
The handle setter changes only the four selected bytes, preserving the unused
union bytes, flags, and cookie. A separate `binder_pri_ptr_cookie` experiment
changes priority while preserving implicit padding.

No mutable reference to an entire padded aggregate is exposed. A compile-fail
example shows why the standard mutable byte conversion rejects such a type.
The tests do not exercise live userspace copies, IPC32 compatibility, Binder's
full protocol, or concurrent access.

### Conversion migration

`LegacyFromBytes` requires zerocopy's `FromBytes + Immutable`; reference
conversions additionally require `KnownLayout`. `LegacyAsBytes` requires
`IntoBytes + Immutable`. Mutable conversions retain both byte-validity bounds.
The facade implements all eight original conversion methods without handwritten
unsafe code. Differential tests compile the original Linux conversion source.
A DMA-shaped record uses derives instead of duplicate legacy unsafe impls.

This is a migration facade, not an in-tree compatibility patch: existing manual
legacy impls would need removal, and padded Binder wrappers require their own
storage design. Kernel-pointer disclosure policy is not enforced by zerocopy.

### Pinned initialization

The Cargo shims compile Linux's unchanged pin-init and proc-macro sources.
`Slot` stores an exclusive, aligned, uninitialized `Ptr`; `Guard` stores a safe
one. A separate marker carries structural pinning. Two disjoint field guards
can coexist. Tests cover successful ownership transfer, second-field errors,
unwinding, exactly-once destruction, and a self-address-sensitive pinned field.

The concrete split uses derived `Projection` operations, then a small unsafe
bridge through `MaybeUninit` field references. Today `Ptr::from_inner` is not
available to external crates, and `Ptr::project` does not split a whole-object
exclusive capability into several fields. A reusable upstream split API would
need generated disjointness and pin metadata. This prototype does not replace
pin-init's general rollback, field-completeness, or pinned-destructor machinery.

### Device-ID tables

The PCI-shaped table retains context-reference provenance in `MaybeUninit`
storage during CTFE. A descriptor selects the actual `driver_data` field and
checks pointer size/alignment before storing the reference. The table exposes
no safe mutable access. Tests recover both original static references, check
the zero sentinel, and cover an empty table.

The const constructor is concrete to this bus-shaped type and extracts its
known wrapper field, avoiding `transmute_copy`. This does not add const trait
methods to zerocopy or solve generic const conversion for every RfL bus. Runtime
wrapper conversion separately exercises `CastSizedExact` and `Ptr` validity
transitions. No integer-to-pointer reconstruction is used.

### Firmware

The 20-byte firmware header and section header use zerocopy's little-endian
integers and checked borrowed prefix conversion. Parsing works on unaligned
byte slices. Magic, version, reserved fields, header bounds, section ranges,
and page alignment are checked separately. Tests include truncated and malformed
inputs. Entry dispatch, section flag interpretation, GPU mapping, and loading
remain outside this fixed-header prototype.

## Validation and integration scope

The root crate's unit tests and compile-fail doctests are the demo's acceptance
checks. Miri exercises the allocation-backed unsafe bridges. These prototypes
are tested on the host, not built as Linux drivers or modules. They do not
provide MMIO accessors, DMA synchronization, reverse `container_of` projections,
or a replacement for structural pinning. See [SAFETY.md](SAFETY.md) for the trust
boundaries and remaining audit scope.

The host validation covers 17 unit tests, five compile-fail doctests, and the
six-part executable demo. The unit tests also pass under Miri. This is evidence
for those cases on the tested host, not kernel-wide validation.

The shims read sources from the pinned Linux checkout without editing them.
They are host build manifests, not proposed Linux build-system changes. New
experiment code uses the repository's license; the Linux source files retain
their own licenses, including GPL-2.0 for the projection/conversion baselines.
