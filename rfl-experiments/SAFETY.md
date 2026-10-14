<!-- Copyright 2026 The Fuchsia Authors -->
<!-- SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT -->

# Prototype safety boundaries

The experiment scope is the host-side Rust crate and its six source modules,
using this worktree's zerocopy and Linux source pinned in `setup-linux.sh`.
Host tests are behavioral evidence, not a universal soundness certificate.
Kernel configurations, LKMM, device access, interrupts, and userspace races
are not modeled. The Binder model uses the native 64-bit ABI tested on the
host with IPC32 disabled; its mirrored layouts require comparison with bindgen
output before kernel integration.

## Trusted dependencies and semantics

- Zerocopy's allocation, pointer-invariant, projection, cast, and transmute
  contracts are dependencies. This prototype does not re-audit their unsafe
  implementations. The exact revision is inherited from the containing Git
  commit and its PR #3870 ancestry.
- Linux's pinned pin-init code is trusted to supply aligned, exclusively
  writable initialization slots, retain pinning, and apply its documented
  initialization/error contracts. Its host `std` allocation implementation is
  used rather than the kernel allocator.
- Compiler, standard-library, and macro dependencies are trusted. The stable
  toolchain is selected by zerocopy's metadata; Miri uses its pinned nightly.
  The proc-macro shims use Linux's vendored sources, matching its stable
  `wrap_proc_macro` selection, not the full Kbuild probe pipeline.

Relevant standard-library contracts are documented at
[`offset_of!`](https://doc.rust-lang.org/1.99.0/std/mem/macro.offset_of.html),
[`wrapping_add`](https://doc.rust-lang.org/1.99.0/std/primitive.pointer.html#method.wrapping_add),
[`MaybeUninit`](https://doc.rust-lang.org/1.99.0/std/mem/union.MaybeUninit.html),
and [`Pin`](https://doc.rust-lang.org/1.99.0/std/pin/index.html).
These establish respectively actual-field offsets, arithmetic without memory
access, the uninitialized-storage representation, and the independent pinning
obligations. Ordinary pointer reads/writes/drops additionally require the
documented allocation, alignment, initialization, and access permissions.

## Local obligations

| Boundary | Producer and preservation | Consumer |
|---|---|---|
| Raw address descriptor | `offset_of!` selects an actual field; the witness checks its type; wrapping arithmetic does not dereference it | `AddressProject` promises provenance and containment for allocation-backed input; `InAllocation` supplies `Project` |
| Binder snapshot | Zeroed byte storage plus bounded byte copies; private storage; only projected scalar mutation | `Initialized` supports `ReadOnly` union reads; scalar validity conversion supports aligned writes without aggregate-padding mutation |
| Typed slots | An exclusive whole-record slot is consumed; generated projections select its two disjoint, aligned fields | `MaybeUninit` bridge creates field capabilities; pin metadata restricts the address-sensitive field to `PinInit` |
| Initialization guards | Successful writes/initializers establish safe fields; guards own their destruction | Error/unwind drops completed fields; success forgets guards only after both fields initialize, transferring ownership to the pinned record |
| Const device-ID contexts | Concrete integer ID layout plus a checked, actual context field; construction writes static references; storage is private | Reads interpret the same stored reference representation; no pointer is reconstructed from an integer |
| Firmware and migration facade | Public safe zerocopy conversions and explicit protocol checks | Typed references are used only after conversion; malformed inputs return errors |

The initialization split is deliberately concrete. Generalizing it requires a
proof that arbitrary selected fields are distinct/disjoint, alignment is
preserved or checked, the parent capability is consumed, and structural pinning
is respected. Passing an unchecked list of field descriptors is insufficient.

The device-ID raw pointer retains provenance for the whole table, including
the sentinel. External C code must not mutate its supposedly immutable contents
while Rust accesses them. The host demo does not invoke C or expose a safe
mutation API.

Before production integration, audit these contracts on the selected kernel
targets, compare mirrored ABI layouts with generated bindings, verify the macro
and build selections, and review all C/hardware interference paths. The tests
and adjacent safety comments do not certify that larger claim.
