# Rust atomic operations and memory orderings at nightly-2026-05-31

## Summary

At the Rust revision behind nightly-2026-05-31, the atomic library explicitly adopts the C++20 atomic memory model, omitting `memory_order_consume` and translating C++'s object-based wording into Rust's access-based model. The critical safety boundary is not “all shared writes must be atomic.” It is that a **data race**—conflicting, unsynchronized accesses where at least one access is non-atomic—is undefined behavior. Conflicting atomic accesses can race without becoming a data race, but non-synchronized atomics have an additional mixed-size restriction: partially overlapping atomic accesses are not allowed unless they are both reads.

Ordering controls synchronization, not atomicity. `Relaxed` still performs an atomic access but does not by itself order unrelated memory. Release/acquire synchronization can carry earlier writes to later reads when the acquire observes the relevant release. Read-modify-write operations split their load and store components: `Acquire` weakens the store half to `Relaxed`, while `Release` weakens the load half to `Relaxed`. Compare-exchange also has a separate failure ordering because failure is only a load.

For Anneal, the reusable model should therefore keep at least four dimensions separate: access atomicity, overlap/access size, memory ordering, and the happens-before relation. Treating `Ordering` as a scalar “strength” attached to an otherwise ordinary load/store loses operation-specific semantics.

## Applicability

This report covers `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, with the bundled Rust Reference at `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

The report focuses on the semantics exposed by `core::sync::atomic`: the module memory model, `Ordering`, atomic load/store/read-modify-write operations, compare-exchange success and failure, and fences. It is intended as the baseline for future Anneal work if concurrency enters the verification surface.

This is not a hardware memory-model report. It does not derive x86, ARM, RISC-V, LLVM, or target-specific lowering behavior. It also does not claim a complete formal Rust memory model beyond the contracts the pinned library and Reference state.

## Findings

### Rust adopts C++20 atomic rules with an access-based translation

The pinned `core::sync::atomic` module says Rust atomics follow the C++20 atomic rules from `intro.races`, except there is no consume ordering. Because C++ partitions memory into atomic and non-atomic objects while Rust's model is access-based, the library documentation translates references to “atomic objects” into atomic loads and stores on memory accesses.

One visible consequence is that Rust permits concurrent atomic and non-atomic **reads** of the same memory when no write is involved. The module explicitly contrasts this with C++ `atomic_ref`, whose object model forbids the analogous overlap even though the accesses do not create a race in the C++ memory model.

Basis: **documentation/source** in the pinned atomic module.

### A data race requires a conflicting non-atomic access

The Rust Reference lists data races as undefined behavior. The atomic module gives the operational shape used here: two accesses conflict when they overlap and at least one writes; they are non-synchronized when neither happens-before the other. A data race is a conflicting non-synchronized pair where at least one access is non-atomic.

A failed `compare_exchange` or `compare_exchange_weak` is not a write for this classification. Therefore a failed CAS participates as a load, even though the instruction implementing it may be a read-modify-write primitive on a given machine.

Atomicity alone is not a synchronization proof. `Relaxed` loads and stores avoid data races with other same-size atomic accesses, but without a synchronizing relation they do not make unrelated non-atomic data safe to communicate across threads.

Basis: **normative** for “data races are UB”; **documentation/source** for the pinned atomic-model elaboration.

### Overlapping atomics have a separate mixed-size rule

The atomic module records a second undefined-behavior boundary inherited from C++: non-synchronized conflicting atomic accesses may not partially overlap at different access sizes. Every such pair must be disjoint, cover exactly the same memory with the same size, or consist only of reads.

This matters because “both accesses are atomic” is not sufficient. Reinterpreting one atomic storage location through a differently sized atomic type and concurrently writing through both can still be undefined behavior.

A verifier that models atomics only as indivisible reads/writes on abstract variables needs an explicit correspondence rule from each atomic operation to its concrete byte range and size.

Basis: **documentation/source**.

### `Relaxed` supplies atomicity without cross-location synchronization

`Ordering::Relaxed` imposes no additional ordering constraints beyond the atomic operation itself. The module's examples use a relaxed global counter precisely to show the distinction: the counter update is atomic, but it does not synchronize unrelated memory.

This is the minimum useful ordering distinction for proofs. A successful relaxed read-modify-write can establish a linearized modification of the atomic location without establishing that preceding writes in one thread become visible after a later relaxed read in another.

Basis: **documentation/source**; the proof-model phrasing is **derived**.

### Release and acquire carry synchronization in opposite directions

A release store orders prior operations before an acquire-or-stronger load that observes the released value according to the memory model. In the common publication pattern, writes before the release become visible to code after the matching acquire.

The direction is important. `Release` is only applicable where an operation can store; `Acquire` is only applicable where an operation can load. The atomic APIs enforce this distinction for pure operations: `load` accepts only `Relaxed`, `Acquire`, or `SeqCst` and panics for `Release` or `AcqRel`; `store` accepts only `Relaxed`, `Release`, or `SeqCst` and panics for `Acquire` or `AcqRel`.

Basis: **documentation/source**.

### Read-modify-write ordering decomposes into load and store components

Operations such as `swap`, fetch operations, and successful compare-exchange both read and write. Their ordering is not applied symmetrically to both halves.

The pinned documentation states:

- `Acquire` makes the store component `Relaxed`;
- `Release` makes the load component `Relaxed`;
- `AcqRel` gives acquire semantics to the load and release semantics to the store; and
- `SeqCst` additionally participates in the single order required for sequentially consistent operations.

This prevents a common modeling error: treating `Acquire` on an RMW as if the write were also a release, or treating `Release` as if the read were also an acquire.

Basis: **documentation/source**.

### Compare-exchange has distinct success and failure orderings

`compare_exchange` takes separate orderings because its two outcomes perform different classes of access. On success it performs a read-modify-write. On failure it performs only a load, so the failure ordering may be only `Relaxed`, `Acquire`, or `SeqCst`; release semantics have no store to apply to.

The weak form may fail spuriously even when the compared value matches. Code using `compare_exchange_weak` must therefore tolerate retry without interpreting every failure as evidence that another thread changed the value.

CAS also has the ordinary ABA limitation: seeing the same value again does not establish that the value was unchanged in the interval. A proof that needs identity-over-time must encode more than equality of the compared bits.

Basis: **documentation/source**.

### `SeqCst` adds a global order among sequentially consistent operations

`Ordering::SeqCst` carries the applicable acquire/release behavior for the operation and additionally requires all threads to observe sequentially consistent operations in one consistent total order.

This does not mean an entire concurrent program becomes sequentially consistent merely because one operation is `SeqCst`. The guarantee is tied to the memory-model relations and the set of sequentially consistent operations.

Basis: **documentation/source**; the final boundary sentence is **derived**.

### Fences still require atomic operations to establish synchronization

`fence` accepts `Acquire`, `Release`, `AcqRel`, or `SeqCst`; `Relaxed` is rejected because there is no relaxed fence. The synchronization effect is not a free-standing replacement for atomic communication. The module documentation explicitly says synchronization with fences still requires atomic operations in the participating threads.

`compiler_fence` has a narrower domain. It emits no machine code and constrains compiler reordering only for operations that execute on the same hardware thread/CPU, such as a thread and its signal or interrupt handler. It can establish synchronization in those same-thread-concurrent situations, but it is not a cross-CPU hardware fence.

Basis: **documentation/source**.

### Atomic access does not license mutation of target-level read-only memory

The module has an implementation-sensitive but explicit read-only-memory rule. In general, atomic accesses to memory that the underlying target maps read-only are undefined behavior; even a CAS expected to fail may use an instruction that attempts a write, and some atomic loads may be implemented with compare-exchange.

The pinned version preserves a narrow stable exception for sufficiently small `Relaxed` loads on listed target architectures. The size threshold is target-dependent. Other loads might happen to work, but the documentation says that is not a stable guarantee.

This rule concerns target-level read-only pages, not ordinary Rust shared references to writable memory. The report keeps that distinction explicit because conflating them would incorrectly forbid normal atomic loads through shared references.

Basis: **documentation/source**.

### Atomic availability and lock-freedom are target properties

When an atomic type in this module is available, the documentation guarantees that it is lock-free in the sense that it does not internally acquire a global mutex. It does **not** guarantee wait-freedom; an operation may use a retry loop.

Availability itself is conditional on target support. `target_has_atomic`/related configuration controls widths and operation classes, and some targets offer loads/stores without compare-and-swap operations.

A portable proof or generated program therefore cannot assume that every integer width supports every atomic operation merely because the source type exists on the current host.

Basis: **documentation/source**.

## Boundaries

**No complete hardware lowering model.** The report does not map Rust orderings to exact machine instructions or prove the correctness of LLVM/backend lowering.

**No consume ordering.** Rust's documented model intentionally omits C++ `memory_order_consume`; this report does not invent an analogue.

**No complete aliasing/provenance model.** Atomics solve particular concurrency races. They do not erase pointer validity, provenance, lifetime, or aliasing obligations for locating the memory being accessed.

**No promise that `Relaxed` means “cheap.”** Ordering is semantic. Instruction selection and cost are target/compiler properties not established here.

**No fairness or wait-freedom.** Lock-free availability does not imply a particular thread completes in bounded steps.

**Read-only-memory guarantees are target-qualified.** The “sufficiently small relaxed load” exception has an architecture table in this pinned source. Do not carry its thresholds to another target or revision without revalidation.

**No fresh litmus execution.** The report did not run Loom, Miri, hardware litmus tests, or compiler codegen probes. It preserves the exact pinned library/Reference contract.

## Evidence

Evidence was acquired on 2026-09-27.

- **Documentation/source:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `library/core/src/sync/atomic.rs`, blob `4f2faa7e5fbd6bd7aa7377118b2e2dc1849243c5`. Relevant regions include the module-level memory-model documentation, read-only-memory and portability sections, `Ordering`, `AtomicBool::load`/`store`/RMW/compare-exchange documentation, `fence`, and `compiler_fence`. The integer and pointer atomic families are generated from the same ordering model, though availability depends on target configuration.
- **Normative:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`, section `undefined.race`: data races are undefined behavior, within the Reference's explicit broader caveat that Rust's complete unsafe semantics is not yet formally specified.

The report also relies on the atomic module's pinned links to C++20 for the adopted memory-model semantics. Those links identify the external model; the Rust source is the evidence that this exact Rust revision adopts it with the stated Rust-specific translation and exceptions.

## Revalidation

For another Rust revision, first diff the module-level documentation in `library/core/src/sync/atomic.rs`. Changes there can alter the memory model even if individual method signatures remain unchanged. Recheck, in order:

1. the stated C++ memory-model version and Rust-specific deviations;
2. the data-race and mixed-size-access definitions;
3. `Ordering` documentation;
4. load/store accepted ordering sets;
5. RMW load/store decomposition;
6. compare-exchange success/failure restrictions and weak-CAS spurious failure;
7. `fence` and `compiler_fence`; and
8. target availability plus read-only-memory guarantees.

Then compare the bundled Rust Reference's data-race UB statement. If implementation behavior matters, add a small set of litmus tests with exact compiler/Miri/Loom/tool versions rather than treating one observed architecture as the language model. A useful discriminating set includes release/acquire publication, relaxed counter update, weak-CAS retry, a mixed-size overlapping atomic access, and fence-mediated publication.