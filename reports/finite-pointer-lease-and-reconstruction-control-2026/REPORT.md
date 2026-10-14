# A finite pointer lease and reconstruction control

## Summary

The original finite model checks construction, disjoint splitting, projection, casting gates, and reference-like reconstruction while rejecting stale, duplicated, overlapping, expired, and lifetime-extended authority. Removing the allocation-death condition makes the bad lifetime extension pass. These are actual theorem/control observations about a four-cell lease protocol, compared with actual zerocopy pointer contracts and safe Rust controls; they are not a proof of zerocopy or a complete Rust provenance model.

## Applicability

`PointerLease.lean` imports installed `Std` only. The identical source was checked by installed Lean 4.31.0 at `68218e876d2a38b1985b8590fff244a83c321783` and Lean 4.34.1 at `5045d0056413266e57c625dcd7c365b10e377c52`, with both final exits 0. Exact library/module identities accompany the version identities. The Lean 4.31 source has the known nested-inductive kernel defect discussed in F6; its acceptance is conditional evidence. The second replay and source comparison are recorded separately, not as a general theorem of kernel soundness.

Rust controls use the pinned 1.101.0-nightly compiler, edition 2024, optimization level 1, `aarch64-apple-darwin`. Source comparison uses zerocopy at `cce761ad53785973ec2f4a6b13715b770b340c87` and the separately pinned Reference. The Rust controls are original small programs and do not execute zerocopy's `Ptr` implementation.

## Findings

### F1. A registered lease adds obligations absent from geometry

Basis: source + execution + derived.

The model has four cells, arbitrary byte values `Fin 256`, one allocation identity, an allocation-death time, an owner ticket per cell, and a registry of live capability records. A capability records ticket, allocation, half-open range, expiry, alignment, initialization, and validity. `Owned` checks exact registry equality, allocation identity, bounded range, expiry no later than allocation death, and owner equality on every covered cell. `reconstructByte` adds unexpired use and initialization/validity/alignment gates. `reconstructWord` additionally requires four-byte alignment, aligned offset, and a four-cell extent.

These are explicit assumptions in a small interpretation, not a trusted read primitive with hidden permissions. `construction` quantifies over arbitrary four-byte contents. Conversely, `geometry_misses_lifetime` proves that the bad extended lease still has valid allocation/range geometry. `weakened_gate_accepts_extension` retains registry, geometry, ownership, and local expiry but omits the allocation-death bound: it accepts expiry 20 at time 11 although the allocation dies at time 10. The full gate rejects that same registered lease. This is a discriminating control for a missing semantic premise.

### F2. Splitting, projection, and consumption change authority while framing bytes

Basis: source + execution.

For each `k : Fin 5`, splitting replaces parent ticket 1 with tickets 2 and 3 for `[0,k)` and `[k,4)`. `split_left`, `split_right`, `split_disjoint`, and `split_covers` establish the authority/range properties, including empty children at endpoints. `stale_parent_rejected` shows the parent cannot still be used in the new registry. `consume` deletes a ticket, and `duplicate_reconstruction_rejected` forbids reconstructing from it afterward.

Projection registers a ticket for one cell. `projection` checks its authority; `projection_preserves_bytes` quantifies over every cell and leaves all bytes unchanged. `restoration` registers a whole-range ticket 4 and rejects the retired child. These fixed constructors exhibit the required authority transitions. They do not prove a general update grammar, nor derive restoration from arbitrary outstanding subleases. In a future general protocol, restoration would need the child-return/loan-closing evidence; the current model constructs a separately defined restored state.

### F3. Negative controls identify lifetime, alias, and alignment gates

Basis: source + execution.

`lifetime_extension_rejected` rejects the registered lease whose expiry exceeds allocation death; `expired_rejected` rejects use at the lease's expiry. `alias_overlap_rejected` builds overlapping ranges and fails the second owner's claim at cell 2. `cast_without_alignment_rejected` rejects word reconstruction from a byte-aligned capability. `reconstructed_byte` succeeds for the initial lease; `reconstructed_word_after_alignment_evidence` succeeds when the separately supplied alignment flag is 4.

That last flag is deliberately an interpretation premise. The model does not compute an address or prove that an allocator actually supplies four-byte alignment. Likewise its `valid=true` and initialized flags are premises, not byte validators. A source certificate must justify them from representation and allocation facts. The rejection controls show why they cannot be silently inferred from bounds.

### F4. Actual zerocopy Ptr preserves more than numerical ranges

Basis: source + derived.

At the pinned PR stack, `Ptr<'a,T,I>` records aliasing, alignment, and validity invariants over `PtrInner`, with lifetime covariance and type invariance. `from_ref` and `from_mut` establish distinct shared/exclusive safe aligned cases. `as_ref` and `as_mut` form references only at appropriate invariant states; `reborrow` narrows the exclusive borrow lifetime. Casting requires trait laws such as mutation compatibility and castability, and yields an unaligned destination state until alignment is justified. Projection uses selected field/projectability evidence rather than merely adding an offset.

`as_inner(&self)` returns a copy of the underlying raw capability representation, and `PtrInner` is copyable. Consequently consuming the outer object is not itself proof that every derived raw access path disappears. The actual interpretation must track which escaped raw values retain usable rights and which references/tags/lifetimes constrain them. The model's registry provides one finite mechanism but is not claimed to match all Rust alias models.

`PtrInner::split_at_unchecked` explicitly requires a valid split bound. Its disjointness guarantee additionally requires the left part to have no trailing padding, which holds for ordinary slices. For a more general trailing-slice DST, that padding can overlap the right part. A general byte-range separation rule cannot be imported solely from the metadata split. The four-byte model and native slice control satisfy the padding-free case; general DST metadata and zero-sized address behavior remain outside the executed model.

### F5. Safe native and compiler controls separate raw addresses from references

Basis: normative + execution + derived.

The native control exercises all five split positions of a four-byte array with `split_at_mut`, updates the two disjoint slices, ends their borrows, and reads the restored parent. All results match the expected per-cell updates. A raw `u8 → () → u8` cast preserves pointer equality in those five live allocations but is never dereferenced through the erased pointer. It therefore tests a representation roundtrip, not provenance or reconstruction permission.

For a packed struct, `addr_of!` obtains the raw field address and `read_unaligned` reads its live initialized `u32`; output is `12345678`. The separate attempt to form `&u32` to that packed field is rejected with E0793. Two further controls reject extending a borrowed mutable slice to `'static`, and duplicating it into two mutable references (E0499). These are expected compile errors, not panics or unsupported research results. No invalid Rust program was executed.

The Reference distinguishes raw address formation, aligned reference creation, typed validity, and access obligations, while stating that exact aliasing rules are not fully determined. The finite model makes its own authority policy explicit within that unresolved normative boundary. Successful borrow checking/native output does not prove unsafe raw-pointer manipulation in every client.

### F6. The proof observation includes checker status and kernel trust

Basis: execution + documentation + source.

Both final Lean runs check all 19 named endpoints. Their printed dependencies are only `propext` and/or `Quot.sound`, with no axioms for the definitional byte-frame theorem. Final logs contain no `sorryAx`; both processes exit 0. Earlier ordinary development failures are preserved separately and are not accepted proof evidence: one temporary source had unsolved goals and printed `sorryAx` while exiting 1; other attempts had redundant tactics after goals were already solved. Reading only those printed theorem names would have misclassified failure as acceptance.

Official Lean 4.32.2 release notes and fix PR 14577 describe a kernel soundness bug involving ill-typed nested-inductive parametric arguments. Direct source comparison finds the final nested-argument `tc.check` absent at the 4.31 commit and present at the 4.34.1 commit, along with restoration rechecks. This establishes source affectedness and the inspected fix region, not execution of an exploit or exhaustive kernel validation. Printed axiom closure alone cannot make acceptance of an arbitrary producer reliable on the affected checker. No exploit or toolchain upgrade was performed.

## Boundaries

The requested bounded capability case now has an actual checked finite interpretation, wrong variants, and safe compiler/native controls. Not examined: an actual Rust-to-Lean pointer correspondence proof, general allocators, integer-pointer roundtrips, strict/exposed provenance, full Stacked/Tree Borrows, shared aliases/interior mutability, arbitrary `Ptr` escapes, general DST/ZST splitting, byte-to-type validation, or panic/drop behavior. These exclusions do not invalidate the finite mechanism. Future engineering must bind its lease transitions to source access paths and prove the alignment/validity/restoration premises. The four-cell bound is semantic scope, not a claim of all allocations. The model complements a separate partial-heap derivation checker; it does not implement one.

## Evidence

Package-owned material: `PointerLease.lean` (SHA-256 in metadata), `lean-execution.json` with both final runs and clearly separated earlier failures, the four Rust controls, and `native-execution.json`. Toolchain full commits, shared libraries, `Init.olean`, and Rust compiler hashes are recorded. Evidence date: 2026-10-14.

- [Pinned zerocopy source](https://github.com/google/zerocopy/tree/cce761ad53785973ec2f4a6b13715b770b340c87): `zerocopy/src/pointer/ptr.rs:Ptr,as_inner,from_ref,from_mut,as_ref,as_mut,reborrow,cast,project`; `pointer/inner.rs:PtrInner,split_at_unchecked` lines 283–324; `pointer/mod.rs`, projection and cast unsafe laws. Source identities are in `source-identities.json`.
- [Pinned Reference](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md): reference liveness/aliasing, typed validity, and misaligned access/formation. The Reference's unresolved exact-alias rules remain a qualification, not permission to ignore its stated obligations.
- [Lean release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) and [fix PR 14577](https://github.com/leanprover/lean4/pull/14577), merged `a39eab69e1eee9ad38f4efe507907b1026a77808`. Direct comparison of `src/kernel/inductive.cpp`: 4.31 Git blob `7a09077a769a0a21a6a8820bc6277b20cc753d65`; 4.34.1 Git blob `438f92d3f6df654dbd6bb1a131fd5a15997620e6`, final nested checks lines 1316–1323. `kernel-fix-identity.json` records the immutable endpoint.

## Revalidation

Run `lean PointerLease.lean` with explicitly selected installed toolchains, record each full version/library identity, exit code, complete diagnostics, and all 19 printed dependency sets. Reject any failed run or admission. Read the predicates and bad variants: removing the death bound must still make the extension control pass, and the full gate must reject it. Compile/run `pointer_safe.rs` with the recorded compiler flags and compile the three negative controls expecting the intended errors. For another source implementation, inspect every construction, projection, split, cast, raw escape, and reconstruction path and bind its actual premises to the model; matching numerical outputs alone cannot provide that certificate.

*Authored by an AI agent acting on joshlf's behalf.*
