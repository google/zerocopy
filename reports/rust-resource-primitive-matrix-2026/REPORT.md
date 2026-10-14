# Rust resource primitives and their accepted source boundary

## Summary

VeriFast, Verus and Creusot expose different resource interfaces for unsafe Rust. Their permission objects, accepted Rust operations and concurrency contracts must be compared separately. The examined VeriFast frontend checks shared immutability but does not claim full Rust pointer aliasing. Verus requires permissioned wrappers for raw dereferences; its raw allocation token records an address domain and provenance rather than byte values. Creusot has typed pointer permissions and explicit ordering interfaces, while arbitrary MIR pointer offsets are rejected in the inspected translation branch. These are source results at exact revisions, not acceptance or performance measurements.

## Applicability

This report compares VeriFast `0a83dba42db7ce0b445034ece5298afe980e57dc` (commit dated 2026-10-09), Verus `0141ebc6f14410dfc87fef1da57408578002eb7c`, and Creusot `c4e9770ac1371ac4274bfe02145266d315c2fb86`. Their source APIs are separate alternatives, not a jointly tested configuration. No full build or verified Rust example was executed in this wave.

The VeriFast foundational pilot is inspected as a separate route. Its [January 2026 preprint, arXiv:2601.13727v1](https://arxiv.org/abs/2601.13727v1), was available before the 2026-10-14 cutoff. Its historical feature list does not define the October source's accepted fragment. The October artifact's theorem and axioms are the stronger evidence for that artifact.

## Findings

### F1. Common primitive matrix

Basis: **source** and pinned upstream **documentation**. Entries describe the inspected interface; an unexamined row is not a tool-wide absence.

| Obligation | VeriFast Rust | Verus | Creusot |
|---|---|---|---|
| Ownership interpretation | Per-type `own(thread,value)` and `share(lifetime,thread,address)`, with automatic safe-function semantic contracts | Tracked, noncopy permission objects; executable and ghost modes are distinct | Ghost permission objects and logical pointer models; borrow-aware contracts |
| Lifetime access | Fractional lifetime tokens, inclusion, full borrows, shared borrows | Permissioned API lifetime/borrow obligations; no equivalence to VeriFast's Iris lifetime algebra established here | Borrowed permissions and mutable-reference final-value machinery; not a full provenance theorem |
| Raw pointer operation | Separation predicates plus inspected shared-immutability discipline | Direct raw dereference rejected; explicit `vstd::raw_ptr` wrappers required | Trusted pointer intrinsics; backend rejects the inspected MIR `Offset` operation |
| Byte state | Points-to resource interfaces; full byte-validity/initialization semantics not compared exhaustively | Typed `PointsTo` carries `MemContents`; `PointsToRaw` lacks a byte-value map | Typed and slice permissions; precise untyped padding/byte map parity not established |
| Concurrency boundary | Masks, atomic protocols, Send/Sync lemmas in specifications | Atomic wrappers inspected here use SeqCst; concurrent invariants need their own contracts | Ordering-parameterized atomic interface and SC-DRF feature choice; commit/synchronization resources |
| Primitive trust | `.rsspec` declarations and supplied library contracts; foundational route separately bounded | `external_body` operations and axiomatic tracked-token contracts, translation and SMT backend | `trusted` contracts/intrinsics, rustc-to-Coma/Why3 translation and solver result |

The matrix distinguishes whether native Rust is accepted, whether its resource behavior is expressible, and what justifies the wrapper's meaning. A resource token cannot justify an accepted pointer operation unless the operation's contract is tied to native execution. Rejecting a native operation does not imply the logic cannot express a manually wrapped equivalent. That equivalence remains an explicit proof obligation.

### F2. VeriFast safe-function and alias contracts

The current [alias reference](https://github.com/verifast/verifast/blob/0a83dba42db7ce0b445034ece5298afe980e57dc/docs/rust-reference/src/rusts-aliasing-rules.md) says its present verification covers shared immutability rather than the full Rust pointer alias rules. Creating a shared reference transfers a fraction strictly between zero and one of points-to access to a new provenance; ending the borrow permits transfer back. UnsafeCell contents are exempted from the shared-reference transfer. This is a concrete resource discipline, not a proof of compatibility with all Stacked Borrows or Tree Borrows behaviors.

`non-unsafe-funcs.md` describes generated semantic contracts. A safe function receives a thread token, required lifetime fractions/inclusions and ownership of arguments; it returns ownership of the result and the retained lifetime/thread resources. Unwind clauses retain specified resources. For a user-supplied contract, verification checks that the generated semantic precondition supplies the custom precondition and that the custom postcondition supplies the generated semantic postcondition.

Custom struct interpretations require share construction and monotonicity laws. Send and Sync require appropriate independence from the current thread identifier; generic laws retain the `type_interp` premises and conditional Send/Sync requirements. The `FnOnce`, `FnMut` and `Fn` specifications in `bin/rust/std/lib.rsspec` also carry ownership, mutable closure state, lifetime and unwind obligations. Those specifications are an assumption boundary until their native implementations are justified.

### F3. VeriFast foundational endpoint and admitted premises

In `bin/rust/rocq/SymexSoundness.v:1573–1607`, `bodies_are_correct_sound` proves persistent specification soundness relative to `wp_Program`, using guarded recursion over callees. `verified_program_has_no_ub:1615–1623` assumes `bodies_are_correct` and an exact empty-argument, unit-output, true-pre/true-post main contract. Its conclusion is `program_has_no_ub`.

That name does not supply a concrete operational adequacy theorem. In [AxSem.v:321–339](https://github.com/verifast/verifast/blob/0a83dba42db7ce0b445034ece5298afe980e57dc/bin/rust/rocq/AxSem.v), `wp_Program` itself is admitted, `wp_Program_intro` is admitted and ignores missing bodies, and `program_has_no_ub` is defined as Iris provability of that WP for main. StorageLive/StorageDead introduction rules at lines 115–121 are explicitly named UNSOUND and end in `Admitted`; the source identifies a soundness bug. The symbolic proof uses those rules. The January preprint also acknowledges its incomplete axiomatic semantics. Therefore the inspected route yields a foundational proof relative to an unvalidated axiomatic layer; it does not remove that layer from the trust boundary.

The October Rocq translator explicitly prints unsupported types/generic arguments outside its selected representation cases. This limit belongs to the foundational export route and must not be generalized to ordinary VeriFast. The inspected mutex example also contains `assume(false)` in `init_ref_Mutex` and a Deref proof branch. It demonstrates a specification shape, not an assumption-free verified mutex result.

### F4. Verus pointer rewriting and tracked memory meaning

The inspected `rust_to_vir_expr.rs:4536–4542` rejects raw pointer dereference and directs users to the permissioned raw-pointer API. Implicit raw borrowing and some implicit pointer casts are likewise rejected in their explicit branches; supported thin/slice pointer conversions and pointer-to-integer operations are mapped to specified functions. Any reuse of ordinary zerocopy pointer code therefore needs a concrete rewriting map and an execution relation for the wrappers.

In [raw_ptr.rs](https://github.com/verus-lang/verus/blob/0141ebc6f14410dfc87fef1da57408578002eb7c/source/vstd/raw_ptr.rs), typed `PointsTo` is tracked and noncopy, with address/provenance/metadata and `MemContents`. `Uninit` represents lack of logical contents knowledge; it need not assert that physical bytes were deinitialized. `PointsToRaw:758–855` records an arbitrary address domain and provenance. Split/join and typed conversion are axiomatic contracts. Conversion into a typed token requires the exact range, alignment and a nonnull/nonzero-size condition and produces uninitialized logical contents. The reverse conversion requires logically uninitialized contents. The source has a TODO for a byte-value map: this raw-domain interface does not itself carry per-byte values.

The global-allocator interface at `raw_ptr.rs:859–968` also separates a noncopy Dealloc token recording address, size, alignment and provenance from the raw-domain token. Allocation requires a valid nonzero layout and aborts on native allocation failure. Deallocation consumes both whole-range raw permission and matching Dealloc permission, with exact pointer/layout/provenance checks. These external-body contracts make deallocation obligations expressible; they do not supply a foundational native allocator/alias theorem.

Erasing ghost tokens is appropriate for verified callers that meet the required preconditions. It does not protect an unchecked native caller or prove that every safe Rust entry can acquire those tokens. An open safe wrapper needs ordinary Rust ownership, visibility and abstraction invariants to establish its permission precondition.

### F5. Creusot permissions and the ordering contrast

Creusot's pointer deep model contains an address plus hidden runtime metadata, allowing provenance/wide-pointer distinctions to affect equality. It should not be summarized as pure integer-address erasure. `PermPointer` provides typed allocation/access/borrow transformations; the inspected `from_ref`, `from_mut`, `as_ref`, `as_mut`, `to_box` and destruction paths have trusted contracts. Slice permissions expose split/access interfaces. A logical offset operation exists in the library, but `backend/program.rs:688` rejects MIR `BinOp::Offset`: library specification availability and frontend acceptance are different facts.

In Verus's inspected integer atomic implementation, load and store external bodies use SeqCst. This supports that wrapper interface; it does not establish absence of every weaker-ordering API. Creusot's [atomic.rs](https://github.com/creusot-rs/creusot/blob/c4e9770ac1371ac4274bfe02145266d315c2fb86/creusot-std/src/std/sync/atomic.rs) defines Relaxed/Acquire/Release/AcqRel marker interfaces and selects SeqCst under its SC-DRF configuration or the marker's ordering otherwise. Committers and synchronization views belong to its logical protocol. These interfaces cannot be identified without comparing state, allowed transitions and environmental interference. This inspection answers the API/trust comparison, while a real weak-memory compatibility proof remains future work.

### F6. Interior mutability requires its own resource interface

Verus's current preferred `cell/pcell.rs` is distinct from the deprecated `cell.rs` API. A PCell stores a ManuallyDrop-wrapped UnsafeCell, so dropping the cell alone does not drop its contents. Its external Send/Sync implementations apply regardless of T; the tracked noncopy PointsTo token inherits T's marker traits. The trusted core creates the cell/token together, ties their logical IDs, and requires shared or mutable borrowing of the matching token for native shared or mutable access. `into_inner` consumes the matching token. The ID is a logical cell identity, not a fixed native address, because cells can move. `pcell_maybe_uninit.rs` layers initialized/uninitialized logical contents and put/take/replace over that core. These are precise wrapper/resource contracts, not unconditional access to arbitrary UnsafeCell values.

Creusot's inspected `std/cell.rs` exposes UnsafeCell construction/get as `check(ghost)` external specifications. This small source interface does not establish ordinary executable UnsafeCell verification or full parity with PCell. Its typed pointer permissions and atomic protocols are separate evidence. Comparing a complete executable interior-mutability wrapper requires identifying its actual resource implementation and trust premises. Basis: **source**; the added cell files are identified in `source-evidence.json`.

## Boundaries

Known limits: VeriFast's documented alias coverage; admitted VeriFast foundational semantics/storage rules; Verus rejected raw dereference; Creusot rejected inspected MIR offset. These are consequential exclusions to verify when changing revisions.

Not examined: a complete frontend feature census; accepted zero-copy Rust programs under each tool; arbitrary union/SIMD/padding byte reasoning; every atomic variant or ordering; compiler correspondence; performance. The mutex assumption is not a newly executed failure. No installed tool was invoked, and installation/build failure is not classified as unsupported language support.

Research answered with constraints: the concrete primitive, acceptance and trust contrasts in F1–F5. Remaining research: exhaustive byte-memory parity and order-model compatibility. Future engineering: a source-to-wrapper transformation with simulation, verified open safe wrappers, and pinned tool runs on selected zerocopy cases.

## Evidence

Observed 2026-10-14. `source-evidence.json` records all inspected files with repository, full revision, Git blob and immutable URL. Narrow locations include the VeriFast alias/non-unsafe-function reference, lifetime/alias `.rsspec` declarations, AxSem and SymexSoundness endpoints, Rocq translator, closure specifications and mutex assumption sites; Verus pointer/atomic APIs and rejecting translation branches; Creusot pointer/atomic APIs and offset rejection.

The January preprint is version-pinned context for its own artifact claims, not normative Rust authority. Source was inspected directly through primary GitHub files. No source mirrors are required by this package.

## Revalidation

Diff the named pointer translation branches and resource APIs at a new pin. For VeriFast, inspect every admitted definition/rule reachable from the theorem and compare `program_has_no_ub` with an actual execution adequacy target. For concurrency, compare the concrete operation's native ordering with its logical transition contract and feature configuration. Then run a minimal accepted/rejected Rust case and preserve tool flags and any trusted contract. A successful wrapper test alone does not establish open-client or byte-model closure.

*Authored by an AI agent acting on joshlf's behalf.*
