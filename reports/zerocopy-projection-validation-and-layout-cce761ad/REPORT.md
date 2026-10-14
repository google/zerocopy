# Pointer projections, stable validation and layout boundaries in zerocopy

## Summary

The PR's `Ptr` carries aliasing, alignment and validity dimensions over a live allocation-derived range. Projection shrinks a footprint while transferring the appropriate invariants; it does not derive permission from geometry alone. Runtime validation must preserve checked facts until their consumer, and reference reinterpretation must remain valid under every permitted mutation.

Slice geometry, packed-field alignment, DST metadata and union validity introduce different obligations. The inspected model explicitly leaves physical layout and permission correspondence to its consumer. A small packed-field probe confirms one compiler boundary; it supplies no generic layout theorem.

## Applicability

Source case `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87` was byte-verified against the local commit. Rust contract snapshots are `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec` and Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. Native probes separately used rustc 1.99.0, commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, aarch64-apple-darwin, LLVM 23.1.1, edition 2021, default debug compilation. No promise is generalized between these identities or across supported targets.

## Findings

### Ptr supplies a resource invariant beyond its numerical range

`Ptr`'s field is private to a leaf module. Non-ZST referents must derive from a valid allocation, fit inside it and retain lifetime; the invariant tuple additionally specifies aliasing, alignment and validity. `Ptr::from_inner` is unsafe and requires these dimensions separately. `Shared` follows shared-reference constraints and permitted library interior mutation; `Exclusive` follows mutable-reference constraints. `Initialized` describes all bytes as initialized, while `Safe` additionally covers T's bit validity and library safety invariants. Basis: **source**, [Ptr](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/pointer/ptr.rs#L33), [invariants](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/pointer/invariant.rs#L113).

`Rust.Memory` defines unbounded-Nat allocation/referent footprints and `FitsInAllocation`. It explicitly does not establish existence, liveness, initialization, target address bounds or permission. Inclusion alone also fails to constrain an empty referent's start, so `FitsInAllocation` retains endpoint constraints separately. `IsContiguous` adds the reverse footprint inclusion; the base structures only bound members. Basis: **source**, `anneal/lean/Rust/Memory.lean:12–95`. Thus importing these records cannot justify a dereference by itself. Basis: **derived**.

### Projection consumes access and transfers selected invariants

`HasField` promises a non-strict byte subset with unchanged provenance; it does not promise alignment. `ProjectField` maps the input invariant tuple to a projected tuple retaining the aliasing dimension. Its conditional law requires `is_projectable` to succeed for the projected tag. `Ptr::project` reborrows the tag, matches the projectability result, then obtains the inner projection and constructs the resulting Ptr under that law. Basis: **source**, `lib.rs:1376–1458`, `pointer/ptr.rs:906–934`.

`project_transmute_unchecked` consumes its parent and returns an unaligned result. Its safety contract separately requires validity/mutation compatibility and shared coexistence soundness. Shrinking the region proves useful range/lifetime implications, but a child may have an invariant relating it to bytes outside the child. Parent recovery must therefore restore the full parent's library invariant, not merely reuse its old base/length. Basis: **source** + **derived**, `pointer/ptr.rs:495–562`, `invariant.rs:90–99`.

The lifetime/resource interpretation of these moves must model suspended ancestor access, child escapes and restoration at reference reconstruction. The inspected source comments argue consumption and lifetime restrictions; this report does not prove every public construction or escape path closed. Basis: **derived** obligation, not an execution finding.

### Validity conversion is directional and mutation-sensitive

`TryTransmuteFromPtr` distinguishes source/destination validity and aliases. Its contract requires source validity to survive any destination mutation and destination validity to survive any still-accessible source mutation. `MutationCompatible` supplies either suitable read restrictions or mutual validity implications plus `SharedCompatible`. Equal size/address is consequently insufficient. Basis: **source**, [transmute resource contracts](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/pointer/transmute.rs#L85).

For exclusive access, suspending the source can prevent competing mutations; for shared immutable source/destination, no interior mutation is permitted; for shared mutable representations, the coexistence law must cover both types' safe methods. One-way initial bit validity does not establish either preservation implication. Basis: **derived** from the contract's two directions. Rust's UnsafeCell contract supplies no escape from mutable-reference exclusivity or races.

### Validation needs stable observations until every consumer

`TryFromBytes::is_safe` has a conditional implementer law: true permits relying on valid Self. It may panic, and its shared use for a non-Immutable Self may panic or fail compilation. `Ptr::try_into_safe` validates a reborrowed shared read-only candidate before assuming Safe; its bounds retain both read capability and a validity-transition contract. The false branch returns the original Ptr. Basis: **source**, `lib.rs:1965–1997`, `pointer/ptr.rs:787–825`.

The derive validates fields through projection. With field invariants it retains each validated shared pointer, validates fields sequentially and wraps user invariant expressions in closures so a user `return` cannot bypass later fields. The enum path checks discriminants and validates selected-variant fields; it rejects representations lacking C or primitive layout. Basis: **source**, `zerocopy-derive/src/derive/try_from_bytes.rs:32–126,154–195`.

This source mechanism addresses local validation order and early-return escape. A type-wide invariant still requires closure under every ingress and mutation path: constructors, safe public fields/methods, callbacks, drops and downstream unsafe implementers. A constructor's precondition cannot be reversed into a fact about all values. A shared cached check also needs immutability or a protocol stabilizing every subsequent consumer. Basis: **derived** from conditional validation plus Rust access restrictions. Full closure is unexamined.

### Slice separation includes padding and ZST cases

`PtrInner::split_at_unchecked` changes left metadata and produces the right trailing slice. Its own contract says nonoverlap holds when the left has no trailing padding; a padded left DST may overlap the right through its final padding. This is not an unconditional separation primitive. `Ptr<[T]>::iter` consumes the whole slice and argues that nonzero-sized elements occupy disjoint byte ranges, while ZST elements occupy no bytes. Basis: **source**, `inner.rs:278–325`, `ptr.rs:1300–1336`.

Rust's array rule supplies element stride and slices share the sliced array's layout. For zero stride, byte disjointness is vacuous; API-specific non-null/alignment and lifetime obligations remain. Empty footprints therefore cannot be used to invent pointer provenance or discharge reference-formation requirements. Basis: **normative** contracts + **derived**, Reference `type-layout.md:74–85`; pointer API safety contracts.

### Packed DST layout and dictionary identity remain explicit

`KnownLayout::MaybeUninit` must retain the same layout/metadata and admit uninitialized bytes at all positions. The C-struct derive retains field order/repr alignment/packing in layout computation, creates per-field MaybeUninit analogs and uses ManuallyDrop for the trailing possibly unsized field. Its comments explicitly account for packed generic trivial-drop constraints. Basis: **source**, `lib.rs:748–770`; `zerocopy-derive/src/derive/known_layout.rs:99–120,188–228`.

`Rust.Layout` proves final-padding arithmetic using unbounded naturals and an explicit positive power-of-two alignment. It does not prove that the supplied numbers describe a Rust type, fit usize/isize, match recursive default representation, or encode valid DST metadata. `reprCSliceDstSize_aligned` only concludes divisibility of the complete rounded size. Basis: **source**, `anneal/lean/Rust/Layout.lean:12–25,34–41,89–108`.

The proof must retain the actual `KnownLayout`, field-projection, IntoBytes and validator dictionaries, including associated types and trait bounds. Matching the mathematical carrier alone does not equate providers or their laws. Generated impl tokens, source cfg and downstream blanket/manual impls require a selected-source/obligation closure. This is a **derived** dictionary requirement; specialization/coinductive law checking across all implementations is not investigated here.

### Union and SIMD support cannot be inferred from field syntax

The union validator generates a disjunction of field validators, with each field's early returns local to its own closure. Its safety comment relies on a sufficient bit-valid field criterion and acknowledges incomplete Rust union validity. The pinned Reference independently states exact union validity remains undecided, gives safe construction and a zero-sized-field case, and does not settle every arbitrary byte interpretation. Basis: **source** and **normative** qualification, `try_from_bytes.rs:280–310`; Reference `behavior-considered-undefined.md:144–145`. The sufficient-condition bridge needed for every generated union is **unknown** here; an unresolved general rule is not a proved counterexample.

The Reference treats executing unavailable target features as UB unless the platform explicitly permits it. Thus SIMD/intrinsic contracts need the actual instruction, lane representation, alignment, CPU-feature/runtime detection and target configuration. No portable SIMD or intrinsic implementation is audited in this wave; a union derive's syntax is not evidence of their support. Basis: **normative** plus **derived** scope boundary.

### The Safe documentation has an unresolved local contract tension

`Validity`'s safety contract requires its admitted set to depend only on T's bit validity (`invariant.rs:56–69`). `Safe`'s documentation includes library safety invariants (`231–237`), while its impl comment again asserts dependence only on bit validity. If library admission is stricter than language bit validity, these statements need reconciliation before using the bit-only substitution law for Safe. This is a directly observed **source** tension and an **unknown** interpretation; no valid-use UB witness or soundness verdict is established here.

### The packed probe discriminates reference formation from raw unaligned access

`packed_bad.rs` attempts `&packet.value` for a `repr(C, packed)` u32 field and compilation returns E0793. `packed_good.rs` uses a raw field address plus `read_unaligned` of an initialized u32 and prints `value=12345678`. Both inputs, commands, compiler identity and outputs are retained in this package. Basis: **execution**.

This observation separates a reference-formation obligation from a raw unaligned-read route on one target. It does not establish every packed offset, DST layout, generic destructor behavior, reference validity or provenance rule. The operation contract must still justify each real read. Basis: **derived** limitation.

## Boundaries

- **Not examined:** full PR soundness/configuration audit, exhaustive generated trait dictionaries and all invariant-producing/preserving APIs, callback reentrancy or escaping-child cases.
- **Unknown:** complete normative union-validity bridge, source-to-model aliasing/provenance correspondence and every packed-DST metadata relation.
- **Not examined:** portable SIMD/target-feature implementations, arbitrary union fields, default-Rust recursive layouts/niches and specialization/coinductive law machinery.
- **Known not to apply:** pure geometry establishes neither allocation existence nor access authority; padded DST splitting does not promise unconditional byte separation.

## Evidence

`source-evidence.json` records immutable PR/Rust/Reference files. `probe-results.json`, `packed_good.rs` and `packed_bad.rs` preserve the bounded native test. All evidence was acquired 2026-10-14. Source and comment claims are distinguished from **normative** contracts, the two **execution** observations and explicit **derived** implications. No Lean checking was performed; source theorem declarations are inspected endpoints.

## Revalidation

Diff projection contracts and their actual derive consumers together. Check parent suspension/restoration and validation-to-use dataflow at each access, then enumerate all invariant ingress/mutation paths. Recompute complete object footprints including final padding before claiming separation. Retain the exact trait providers/associated types. Repeat the packed probe only as a narrow diagnostic check; audit layout/target metadata and operation contracts independently for a new configuration.

*Authored by an AI agent acting on joshlf's behalf.*
