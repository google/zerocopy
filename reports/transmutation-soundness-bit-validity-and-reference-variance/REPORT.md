# Transmutation soundness for bit validity: value, shared, mutable and interior-mutable casts (Lean 4 toy model)

## Summary

This package states and proves, in Lean 4 without Mathlib, exact soundness conditions for reinterpreting one memory region at a second type, in a toy model in which a type is nothing but its *bit validity*: a predicate on byte sequences of one fixed size `n`. Four cast disciplines are modelled (value transmute, shared-reference cast, mutable-reference cast, shared-reference cast with interior mutability), each both *unchecked* (every source-valid value is accepted without inspection, `Sound`) and *checked once at cast time* (the bytes are validated at the destination type when the cast is made, `CheckedSound`). All 29 main theorems, and the 80 further theorems that the result cards name (the five counterexample cards and every counterexample, non-vacuity witness and positive control), are kernel-checked; no declaration of the package uses an axiom other than `propext` and `Quot.sound`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Notation: `T ⊆ U` means every `T`-valid byte sequence is `U`-valid; `T ≡ U` means both inclusions; `T ⊓ U` and `T ⊔ U` are intersection and union of validities; "satisfiable" means some byte sequence is valid. Every result relates two types of the same size whose views cover one and the same region.

One sentence per result (the plain-language claim of its card; the Lean statements are under Findings):

- **R1** (`valueSound_iff_includes`): A value transmute from T to U, two types of the same size, is sound (no permitted, well-typed use of the destination value ever reads bytes that are invalid at U) if and only if every T-valid byte sequence is U-valid.
- **R2** (`sharedSound_iff_includes`): A shared-reference cast from T to U, two types of the same size whose views cover the same region, where the original and the cast reference may both read in any interleaving and nobody writes, never reads invalid bytes if and only if every T-valid byte sequence is U-valid.
- **R3** (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`): An unchecked mutable-reference cast from T to U, two types of the same size whose views cover the same region (the cast reference is used exclusively, then the owner resumes at T), is sound if and only if every T-valid byte sequence is U-valid and, provided T has at least one valid byte sequence, every U-valid byte sequence is T-valid.
- **R3-eq** (`mutSound_iff_validityEq_of_satisfiable`): If the source type T has at least one valid byte sequence, an unchecked mutable-reference cast from T to a type U of the same size (both views covering the same region) is sound if and only if T and U have exactly the same valid byte sequences.
- **R3-imp** (`not_mutSound_of_satisfiable_of_not_validityEq`): No unchecked mutable-reference cast from a type T with at least one valid byte sequence to a type U of the same size (both views covering the same region) whose validity differs from T's is sound.
- **R4** (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`): An unchecked shared-reference cast from T to U (one that accepts every T-valid value without inspecting it), two types of the same size whose views cover the same region, in which both references stay live, the source side may write T-valid values iff srcWrites and the destination side may write U-valid values iff dstWrites, is sound for bit validity in this model (aliasing rules are not modelled) if and only if every T-valid byte sequence is U-valid and, when the destination side may write and T has a valid byte sequence, every U-valid byte sequence is T-valid; srcWrites does not matter.
- **R4-eq** (`sharedIMSound_dstWrites_iff_validityEq_of_satisfiable`): If the destination side of an unchecked shared cast with interior mutability between two types T and U of the same size (both views covering the same region) may write and T has a valid byte sequence, the cast is sound for bit validity in this model if and only if T and U accept exactly the same byte sequences, regardless of whether the source side may write.
- **R4-src** (`sharedIMSound_noDstWrites_iff_includes`): If the destination side of an unchecked shared cast between two types T and U of the same size (both views covering the same region) may not write, the cast is sound for bit validity in this model (aliasing rules are not modelled) if and only if every T-valid byte sequence is U-valid, even when the source side writes T-valid values.
- **R4-mut** (`mutSound_iff_sharedIMSound_dstWrites`): For two types T and U of the same size whose views cover the same region, an unchecked mutable-reference cast from T to U is sound exactly when the unchecked shared cast with interior mutability from T to U in which the destination side may write is sound for bit validity (whether or not the source side may also write).
- **R5-trans** (`valueSound_trans`, `sharedSound_trans`, `mutSound_trans`, `sharedIMSound_trans`): For each cast kind (value, shared, unchecked mutable, and shared with interior mutability for fixed write permissions) and types T, U, V of the same size, if the casts T -> U and U -> V are sound then the cast T -> V is sound.
- **R5-hier** (`valueSound_of_sharedSound`, `sharedSound_of_valueSound`, `sharedSound_of_mutSound`): For two types T and U of the same size, a sound unchecked mutable-reference cast from T to U implies a sound shared-reference cast, and in this model shared-reference soundness and value-transmute soundness coincide.
- **R5-symm** (`mutSound_symm_of_satisfiable`): If the source type T has a valid byte sequence and the unchecked mutable-reference cast from T to a type U of the same size is sound, then the reverse mutable-reference cast from U to T is sound.
- **R6-bool-byte** (`boolV_to_byteV_value_and_shared_sound`, `boolV_to_byteV_mut_violating_run`, `mutSound_needs_includes_rev`): For a bool-like type (valid bytes 0 and 1) and a raw byte (all bytes valid): the value transmute and the shared cast bool -> byte are sound, but the mutable cast is unsound, witnessed by writing 2 through the byte view and then reading the bool.
- **R6-byte-bool** (`byteV_to_boolV_unsound_even_by_value`): The reverse direction byte -> bool is unsound for unchecked value transmutes, unchecked shared-reference casts and unchecked mutable-reference casts, already because transmuting the byte 2 produces an invalid bool (this card does not cover the shared cast with interior mutability, for which see R4, nor checked casts, which are sound for byte -> bool by R8-value-shared and R8-mut).
- **R6-im** (`boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes`): The shared cast bool -> byte is sound without writes but becomes unsound once the destination side may write (with or without source-side writes).
- **R6-src-writes** (`sharedIMSound_eq_needs_dstWrites`): Source-side writes alone do not force validity equality: the shared cast bool -> byte where only the source side may write is sound for bit validity in this model (aliasing rules are not modelled) although the validities differ.
- **R6-never** (`mutSound_eq_needs_satisfiable`, `sharedIMSound_eq_needs_satisfiable`): For the uninhabited type never and the raw byte type, the unchecked mutable cast never -> byte and the unchecked shared cast with interior mutability never -> byte in which both sides may write are (vacuously) sound although the two validities differ, so 'mutable (or destination-writable) casts are sound iff the validities are equal' fails without assuming the source is inhabited (in general every cast from an uninhabited type is vacuously sound in this model: the proof tool sound_of_not_satisfiable).
- **R7-shared-lattice** (`sharedSound_to_join_left`, `sharedSound_to_join_right`, `sharedSound_from_meet_left`, `sharedSound_from_meet_right`, `sharedSound_join_iff`, `sharedSound_meet_iff`): For types T, U, V of the same size, ordered by inclusion of their validities, shared casts from T or from U into the join T ⊔ U, and from the meet T ⊓ U into T or into U, are always sound; a shared cast out of T ⊔ U into V is sound iff both T -> V and U -> V are; a shared cast from V into T ⊓ U is sound iff both V -> T and V -> U are.
- **R7-mut-join** (`mutSound_to_join_left_iff_includes_rev_of_satisfiable`): For a source type T with a valid byte sequence and a type U of the same size, the unchecked mutable cast from T into the join T ⊔ U is sound if and only if the join adds nothing, that is every U-valid byte sequence is already T-valid (the reverse inclusion U ⊆ T).
- **R7-mut-meet** (`mutSound_from_meet_left_iff_includes_of_satisfiable_meet`): For types T and U of the same size such that some byte sequence is valid at both (satisfiability of T and of U separately is not enough), the unchecked mutable cast from the meet T ⊓ U into T is sound if and only if the meet removes nothing from T, that is every T-valid byte sequence is U-valid.
- **R8-value-shared** (`checkedSound_valueProtocol`, `checkedSound_sharedProtocol`): A value transmute, or a shared-reference cast without interior mutability, between two types T and U of the same size that is checked once at cast time (it goes ahead only if the bytes are valid at U) is sound for bit validity in this model, for every T and U.
- **R8-mut** (`checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev`): A mutable-reference cast between two types T and U of the same size (both views covering the same region) that is checked once at cast time (it goes ahead only if the bytes are valid at U) and then used without further checks, after which the owner resumes at T, is sound if and only if, provided some byte sequence is valid at both T and U, every U-valid byte sequence is T-valid; the read-side condition T ⊆ U of the unchecked cast (R3) is not needed.
- **R8-im** (`checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev`): A shared-reference cast with interior mutability between two types T and U of the same size (both views covering the same region), checked once at cast time, in which both references stay live, the source side may write T-valid values iff srcWrites and the destination side may write U-valid values iff dstWrites, is sound for bit validity in this model (aliasing rules are not modelled) if and only if, provided some byte sequence is valid at both T and U, source-side writes require every T-valid byte sequence to be U-valid and destination-side writes require every U-valid byte sequence to be T-valid; unlike the unchecked case (R4), source-side writes matter because they happen after the check.

Corrections to commonly stated forms, all kernel-checked:

1. "A mutable-reference cast is sound iff the two validities are equal" is false as stated: from an uninhabited source every cast is vacuously sound (`mutSound_eq_needs_satisfiable`). The exact form is R3; the equality form R3-eq assumes `T` satisfiable.
2. "Shared casts where either side can write need the same equality as mutable casts" is false for bit validity: for unchecked casts, source-side writes add no requirement (`sharedIMSound_eq_needs_dstWrites`); equality is needed exactly when the destination side writes (R4, R4-eq, R4-src).
3. Value-transmute and shared-cast soundness coincide in this model (R5-hier), so the hierarchy is mutable ⇒ shared ⇔ value, strict only at the first step.
4. The equality requirement for mutable casts concerns unchecked casts. A mutable cast checked once at cast time needs only `(T ⊓ U satisfiable) → U ⊆ T` (R8-mut); a checked shared cast with interior mutability needs `T ⊆ U` for source-side writes and `U ⊆ T` for destination-side writes (R8-im), so source-side writes matter again once the cast is checked.

**Non-claims.** Model–system relation: none proved. Every result is about the toy model; the kernel-checked theorems neither establish nor refute the corresponding claims about Rust's `core::mem::transmute`, reference casts, rustc's transmutability checker or zerocopy's transmute macros. Nothing is said about alignment, size-changing (prefix, sub-slice or unsized) casts, provenance, uninitialised or padding bytes, pointer metadata or the memory a pointer refers to, aliasing models, concurrency, destructors or auto traits, or library-level safety invariants. Statements about Rust, rustc and zerocopy are separate `derived (modeling bridge)` claims, not kernel-checked. The full non-claims of every result are listed first under Boundaries.

## Applicability

### Model fidelity

This is a **toy model**, not a mirror of any production definition. It is meant to capture the *validity invariant* of a language with typed memory reinterpretation (Rust is the running example: `core::mem::transmute`, reference casts, and the transmute macros of the zerocopy crate), and the read/write argument that decides which validity relationship each kind of cast needs. Its definitions are in the Lean namespace `Toy.Transmute` (library `ToyTransmute`, module `ToyTransmute.Basic`):

- a type of size `n` over a byte alphabet `B` is a predicate `Validity B n := (Fin n → B) → Prop`; sizes are a type index, so every cast relates types of equal size and both views cover the same `n` bytes;
- a program run is a finite list of whole-region operations: a read through the source view (typed at `T`) or the destination view (typed at `U`), or a write of a whole byte sequence through one of the views; a write is well typed when the written bytes are valid at the writer's type;
- `NoInvalidRead T U m tr` says that running `tr` from contents `m` never reads bytes invalid at the reading view's type; a read of invalid bytes models the undefined behaviour of producing an invalid value;
- a cast discipline (`Protocol`) is the set of runs permitted while the cast is in effect; `Sound P T U` says that from every `T`-valid initial contents every permitted, well-typed run reads only valid bytes; `CheckedSound P T U` is the same with initial contents restricted to those valid at both `T` and `U` (the check succeeded).

Known gaps (each is a non-claim of every result): alignment; size-changing, prefix, sub-slice and unsized casts; provenance; uninitialised and padding bytes; pointer metadata and the memory a pointer refers to (values are flat byte sequences); aliasing models (Stacked Borrows, Tree Borrows) and lifetimes; per-byte placement of `UnsafeCell`; synchronization protocols of interior-mutable types; concurrency; destructors and auto traits; library-level safety invariants; re-checking disciplines (checks on every read or store); composition of checked casts.

Toolchain: Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib, no Lake dependencies (`lean/lakefile.toml` declares one `[[lean_lib]]`, `ToyTransmute`, and no `[[require]]`).

### Modeling bridge

Every kernel-checked statement in this package is about the toy model. The following explains what each modelling choice is meant to capture in a real language with typed memory reinterpretation (Rust is the running example), what is omitted, and how each omission affects how far a result reaches. Basis for every item: derived (modeling bridge); none of it is kernel-checked.

1. **Types are bit-validity predicates on equal-size byte sequences.** `Validity B n` captures the *validity invariant* (UCG glossary): the byte sequences a value may consist of without immediate undefined behaviour. Bytes are always initialised and carry no provenance. **Omitted:** uninitialised and padding bytes, and pointer provenance (MiniRust's abstract bytes model both; the Aeneas prototype models uninitialised bytes); library-level *safety* invariants; alignment; size changes (the size `n` is a type index, so prefix casts, sub-slice casts and unsized types are not expressible); pointer metadata. *Effect:* the characterizations are exact only for casts between same-size types whose validity is a property of initialised bytes alone. A type with padding, or a destination that is under-aligned, needs conditions this package does not state. Because bytes are always initialised, the all-bytes validity includes every type; with uninitialised bytes a source must additionally consist of initialised bytes (zerocopy's `Src: IntoBytes`).
2. **Values are flat.** A value is its bytes and nothing else. For a type whose bytes encode a reference, box or other pointer, the model sees only the pointer's own bytes, never the memory it refers to. *Effect:* R1 does not cover value transmutes of pointer-containing types: `&mut bool` and `&mut u8` have the same pointer bit patterns, but reinterpreting one as the other is a reference cast whose referents fall under R3 (rustc's checker accordingly combines a byte-level check with recursive referent checks).
3. **Reads and writes act on the whole region and are typed.** A read through a view is defined only if the region is valid at that view's type; a write through a view stores any byte sequence valid at that view's type. Writing *any* valid value is the most permissive thing safe code holding a writable reference can do. A field-wise update by well-typed code leaves the region valid, and so is covered by a whole-region write. *Effect:* the sufficiency directions stay correct when writes are restricted. The necessity directions use writes of arbitrary valid values: if an API restricts which values can be written through the cast reference (for example because the destination type has a stronger safety invariant or private fields), the write-side requirement can weaken.
4. **Two views of one region, and a protocol instead of an aliasing model.** Which view may act when is fixed by the discipline (`valueProtocol`, `sharedProtocol`, `mutProtocol`, `sharedIMProtocol`). A run starts at the cast; what happened before is summarised by the initial contents. **Omitted:** the language's aliasing model (for Rust, the Stacked Borrows and Tree Borrows proposals, and the rule that bytes may not be mutated while a shared reference without interior mutability to them is in use), lifetimes, reborrowing chains with more than two views, and two-phase borrows. *Effect:* R4's source-only-writes case is sound for bit validity, but Rust's aliasing rules govern it independently. zerocopy's `transmute_ref!` excludes it by requiring `Immutable` on both source and destination; rustc's transmutability checker (at the cited commit) requires only the destination referent of a shared-reference cast to be free of interior mutability and places no such condition on the source referent.
5. **Interior mutability is a per-side write permission.** The flags `srcWrites` and `dstWrites` mean "this side may write the region while both references are live". **Omitted:** `UnsafeCell` applies to particular byte ranges, and those ranges may sit at different offsets in T and U (`&(UnsafeCell<u8>, u8) → &(u8, UnsafeCell<u8>)` has equal validities and interior mutability on both sides, yet is not covered); interior-mutable types also carry synchronization or borrow-tracking protocols (atomics, `Cell`, `RefCell`) that validity equality does not reconcile, which is why rustc rejects even `&UnsafeCell<u8> → &UnsafeCell<u8>`.
6. **Unchecked and checked casts.** `Sound` describes unchecked casts, which must accept every T-valid value without inspecting it. `CheckedSound` describes casts that validate the bytes at U once, at cast time, and then proceed unchecked (zerocopy's `try_transmute!`, `try_transmute_ref!`, `try_transmute_mut!`). **Omitted:** designs that re-check on every read or every store (as Java arrays do on stores), failure handling, and races between the check and later use.
7. **Runs are finite sequential interleavings.** No concurrency or data races.
8. **The initial contents are valid at the source type.** This models "the source reference points to a valid value when the cast happens". In particular every cast from an uninhabited type is vacuously sound. The Rust Reference requires a reference to point to a valid value (a point it notes is still debated), under which a reference to an uninhabited type is never valid; the vacuous case therefore does not license creating such a reference.
9. **Value transmute.** The value is moved into the destination, which may then read and write it at U. A copied source keeps an independent region, which is not modelled. **Omitted:** destructors and auto traits (`Send`, `Sync`): a transmute skips the source's destructor and may later run the destination's, and reinterpretation between types differing in `Send`/`Sync` can break thread-safety guarantees; none of this is captured by validity.
10. **Language-level unions and enums.** `Validity.join` is the validity of a hypothetical "either T or U" type of the same size. It is not the validity of a Rust `union`, whose validity requirements may be weaker, nor of a tagged enum.

### Real-system qualifiers (derived)

Basis: derived (modeling bridge) + normative specification + source + documentation. These three qualifiers are the points where the model meets real systems most directly; each is restated in the cards it affects.

1. **References to valid values are a debated rule.** The Rust Reference, page "Behavior considered undefined", rule [undefined.validity.reference-box]: "A reference or Box<T> must be aligned and non-null, it cannot be dangling, and it must point to a valid value", followed by the note that "the last point (about pointing to a valid value) remains a subject of some debate." The model's assumption that the initial contents are valid at `T` corresponds to this rule; the vacuous soundness of every cast from an uninhabited type (R3, R3-eq, R6-never) therefore does not license creating a reference to an uninhabited type.
2. **rustc constrains only the destination referent of a shared-reference cast.** In `rust-lang/rust` at commit `5b216e01a117532b30f061f3dff8a61408113c77`, file `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`, lines 276-282: the referents must be transmutable from source to destination and, if the destination reference is mutable, also from destination to source; otherwise (shared destination reference) the condition `Condition::Immutable { ty: dst_ref.referent }` is added. No interior-mutability (`Freeze`) condition is placed on the source referent. Lines 92-93 state that "mutable destination references also generate a reverse transmutability obligation for their referents"; lines 112-119 answer Yes for an uninhabited source. In the model, the destination-immutable shared case is `dstWrites = false`, for which R4/R4-src require only `T ⊆ U`; the source-writes case is decided in Rust by the aliasing model, which the model omits.
3. **zerocopy's checked mutable cast is the real instance of the checked mutable case.** zerocopy 0.8.63's `try_transmute_mut!` (`Src: FromBytes + IntoBytes + ?Sized`, `Dst: TryFromBytes + IntoBytes + ?Sized`, plus alignment and size bounds; "while the value of the referent is checked for validity at runtime, the size and alignment are checked at compile time") is an instance of `CheckedSound mutProtocol` (R8-mut): `Dst: IntoBytes` and `Src: FromBytes` give `U ⊆ T` over initialised bytes, and the run-time check supplies validity at `U` for the initial contents. Its remaining bound `Src: IntoBytes` has no counterpart in the model, whose bytes are always initialised: it guarantees that the source referent's bytes are initialised, so that the run-time check can read them, which `Src: FromBytes` alone does not (a `FromBytes` type may contain padding bytes). Its documented examples convert `&mut 0u8` to `Ok(&mut false)` and reject `&mut 2u8`.

### How the subjects relate

The Lean toolchain is the checker of every theorem. The other subjects in `REPORT.json` are the real systems and specifications the model is interpreted against, each identified by an immutable revision or release where one exists: rustc's transmutability checker and its `UnsafeCell` reference UI test (`rust-lang/rust` commit `5b216e01a117532b30f061f3dff8a61408113c77`), zerocopy 0.8.63 (a crates.io release, identified by its crate checksum; its documentation was read on docs.rs), two pages of the Rust Reference, the nightly `TransmuteFrom`/`Assume` documentation and the Unsafe Code Guidelines glossary (each read on its live site and pinned to the upstream source commit at which the quoted text was verified), MiniRust, the RustHornBelt Coq development, and the Java Language Specification, Java SE 21 edition (no repository revision exists; the edition identifies the text). The text quoted from each was checked at the cited revision or version; none of them was executed, and every statement connecting them to the theorems is a derived claim.

Everything else the cards cite is recorded only under Evidence (Primary sources), as prior art or design history, and is not a subject: the Safer Transmute RFC text is an unmerged pull request, compiler-team proposal 411 is an issue-tracker entry, and the Aeneas layouts work is an open draft pull request, so none of the three is a durable revision; the blog posts by Wrenn and by Jung have no immutable revision; RFC 2835 is cited as context only; and the published papers are cited as prior art, checked against their publisher, Crossref or DataCite records and, where a passage is quoted, against that passage; no claim of this report rests on a full reading of them (the primary texts of [REYNOLDS] and [PIERCE_SANGIORGI] were not accessible; see the source-verification limits under Evidence).

## Findings

### Conventions

- Lean names are in namespace `Toy.Transmute` (omitted below). Every main theorem is in `lean/ToyTransmute/Results.lean`; counterexamples, non-vacuity witnesses and positive controls are in `lean/ToyTransmute/Counterexamples.lean`; definition examples in `lean/ToyTransmute/Examples.lean`; proof tools in `lean/ToyTransmute/Tools.lean`.
- Blocks headed *Lean* are Lean's own `#check` output for the compiled project (`set_option pp.fieldNotation.generalized false`, namespace opened). In Lean's printing `↔` binds more weakly than `→`, so `A ↔ B → C` means `A ↔ (B → C)`.
- Blocks headed *Unfolded* are hand-written and follow one convention: `ValueSound`, `SharedSound`, `MutSound` and `SharedIMSound s d` are replaced by `Sound valueProtocol`, `Sound sharedProtocol`, `Sound mutProtocol` and `Sound (sharedIMProtocol s d)`; `Includes`, `ValidityEq`, `Satisfiable`, `Validity.meet` and `Validity.join` are replaced by their one-line bodies; in the characterizations (R1-R4, R8) `Sound` / `CheckedSound` and the protocol are unfolded as well; corollaries keep `Sound <protocol>` folded. For reference:

```lean
Sound P T U        := ∀ m, T m → ∀ tr, P tr → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr
CheckedSound P T U := ∀ m, T m → U m → ∀ tr, P tr → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr
```

- Fixtures (one-byte types over `Fin 256`): `bool` = `boolV` (bytes 0, 1), `bool'` = `boolV'` (byte value below 2; extensionally equal to `boolV`), `byte` = `byteV` (all bytes), `never` = `neverV` (no bytes), `zero-only` = `zeroV`, `two-only` = `twoV`.
- Every theorem below has `Basis: execution (Lean kernel check)`: it was elaborated and kernel-checked by Lean v4.34.1, with the axioms listed under Evidence. A separate `Basis: derived (modeling bridge)` line, where present, gives the card's claim about real systems and its reasoning; that line is not kernel-checked.

### Results at a glance

| id | kind | Lean name(s) | tier | depth |
| --- | --- | --- | --- | --- |
| R1 | characterization | `valueSound_iff_includes` | T1 | shallow |
| R2 | characterization | `sharedSound_iff_includes` | T1 | shallow |
| R3 | characterization | `mutSound_iff_includes_and_satisfiable_imp_includes_rev` | T1 | shallow |
| R3-eq | characterization | `mutSound_iff_validityEq_of_satisfiable` | T1 | definitional |
| R3-imp | impossibility | `not_mutSound_of_satisfiable_of_not_validityEq` | T1 | definitional |
| R4 | characterization | `sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev` | T1 | shallow |
| R4-eq | characterization | `sharedIMSound_dstWrites_iff_validityEq_of_satisfiable` | T1 | definitional |
| R4-src | characterization | `sharedIMSound_noDstWrites_iff_includes` | T1 | definitional |
| R4-mut | characterization | `mutSound_iff_sharedIMSound_dstWrites` | T1 | definitional |
| R5-trans | theorem | `valueSound_trans`, `sharedSound_trans`, `mutSound_trans`, `sharedIMSound_trans` | T1 | shallow |
| R5-hier | theorem | `valueSound_of_sharedSound`, `sharedSound_of_valueSound`, `sharedSound_of_mutSound` | T1 | definitional |
| R5-symm | theorem | `mutSound_symm_of_satisfiable` | T0 | definitional |
| R6-bool-byte | counterexample | `boolV_to_byteV_value_and_shared_sound`, `boolV_to_byteV_mut_violating_run`, `mutSound_needs_includes_rev` | T1 | definitional |
| R6-byte-bool | counterexample | `byteV_to_boolV_unsound_even_by_value` | T1 | definitional |
| R6-im | counterexample | `boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes` | T1 | definitional |
| R6-src-writes | counterexample | `sharedIMSound_eq_needs_dstWrites` | T1 | definitional |
| R6-never | counterexample | `mutSound_eq_needs_satisfiable`, `sharedIMSound_eq_needs_satisfiable` | T1 | definitional |
| R7-shared-lattice | theorem | `sharedSound_to_join_left`, `sharedSound_to_join_right`, `sharedSound_from_meet_left`, `sharedSound_from_meet_right`, `sharedSound_join_iff`, `sharedSound_meet_iff` | T0 | definitional |
| R7-mut-join | characterization | `mutSound_to_join_left_iff_includes_rev_of_satisfiable` | T0 | definitional |
| R7-mut-meet | characterization | `mutSound_from_meet_left_iff_includes_of_satisfiable_meet` | T0 | definitional |
| R8-value-shared | theorem | `checkedSound_valueProtocol`, `checkedSound_sharedProtocol` | T1 | shallow |
| R8-mut | characterization | `checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev` | T1 | shallow |
| R8-im | characterization | `checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev` | T1 | shallow |

### Definitions

Each core definition with what it is meant to capture and its proved positive and negative examples (all in `lean/ToyTransmute/Examples.lean`). Definitions are shown as Lean prints them. Where an example's name does not say what it tests, its statement follows in parentheses; these statements are at `B = Fin 256` and `n = 1`, use the fixtures defined at the end of this section (`byteSeq x` is the one-byte sequence `x`), and write constructors with Lean's leading dot (`.dst` for `Side.dst`, `.read` for `Op.read`).

All in `ToyTransmute/Basic.lean` (the proof-tool vocabulary at the end is in `ToyTransmute/Tools.lean`); examples in `ToyTransmute/Examples.lean`.

#### `Bytes`

The contents of one memory region: `n` bytes over an arbitrary byte alphabet `B` (examples use `Fin 256`, `n = 1`).

Lean (pretty-printed):
```lean
@[reducible] def Bytes : Type → Nat → Type :=
fun B n => Fin n → B
```

#### `Validity`

A type's bit validity: the set of `n`-byte sequences that are valid representations of a value of the type. Captures the *validity invariant* of a language (not the library-level safety invariant). Size is a type index, so every cast in the package is between equal-size types.

Lean (pretty-printed):
```lean
@[reducible] def Validity : Type → Nat → Type :=
fun B n => Bytes B n → Prop
```

#### `Includes`

`Includes T U` (written T ⊆ U): every T-valid byte sequence is U-valid.

Lean (pretty-printed):
```lean
def Includes : {B : Type} → {n : Nat} → Validity B n → Validity B n → Prop :=
fun {B} {n} T U => ∀ (m : Bytes B n), T m → U m
```
Positive example(s): `includes_boolV_byteV`. Negative example(s): `not_includes_byteV_boolV`.

#### `ValidityEq`

`ValidityEq T U` (written T ≡ U): T and U accept exactly the same byte sequences. Extensional.

Lean (pretty-printed):
```lean
def ValidityEq : {B : Type} → {n : Nat} → Validity B n → Validity B n → Prop :=
fun {B} {n} T U => ∀ (m : Bytes B n), T m ↔ U m
```
Positive example(s): `validityEq_boolV_boolV'`. Negative example(s): `not_validityEq_boolV_byteV`.

#### `Satisfiable`

Some byte sequence is valid for the type (the type is inhabited at the byte level).

Lean (pretty-printed):
```lean
def Satisfiable : {B : Type} → {n : Nat} → Validity B n → Prop :=
fun {B} {n} T => ∃ m, T m
```
Positive example(s): `satisfiable_boolV`. Negative example(s): `not_satisfiable_neverV`.

#### `Side`

The two views of the region: `src` (the original reference/owner, typed at the source type T) and `dst` (the reinterpreted reference or value, typed at the destination type U).

Lean (pretty-printed):
```lean
inductive Side : Type
number of parameters: 0
constructors:
Side.src : Side
Side.dst : Side
```

#### `Side.ty`

The type a view is typed at.

Lean (pretty-printed):
```lean
def Side.ty : {B : Type} → {n : Nat} → Validity B n → Validity B n → Side → Validity B n :=
fun {B} {n} T U x =>
  match x with
  | Side.src => T
  | Side.dst => U
```
Positive example(s): `side_ty_dst_example` (`Side.ty boolV byteV .dst = byteV`: the destination view is typed at the destination type). Negative example(s): `side_ty_src_ne_example` (`Side.ty boolV byteV .src ≠ byteV`: the source view is not typed at the destination type).

#### `Op`

One operation on the region: a typed read through a view, or a write of a whole byte sequence through a view.

Lean (pretty-printed):
```lean
inductive Op : Type → Nat → Type
number of parameters: 2
constructors:
Op.read : {B : Type} → {n : Nat} → Side → Op B n
Op.write : {B : Type} → {n : Nat} → Side → Bytes B n → Op B n
```

#### `Op.side`

The view an operation goes through.

Lean (pretty-printed):
```lean
def Op.side : {B : Type} → {n : Nat} → Op B n → Side :=
fun {B} {n} x =>
  match x with
  | Op.read s => s
  | Op.write s v => s
```
Positive example(s): `op_side_read_dst_example` (`Op.side (.read .dst) = .dst`). Negative example(s): `op_side_write_src_ne_dst_example` (`Op.side (.write .src (byteSeq 0)) ≠ .dst`: a write through the original view does not go through the destination view).

#### `Op.IsRead`

The operation is a read.

Lean (pretty-printed):
```lean
def Op.IsRead : {B : Type} → {n : Nat} → Op B n → Prop :=
fun {B} {n} x =>
  match x with
  | Op.read s => True
  | Op.write s v => False
```
Positive example(s): `op_isRead_read_example` (`Op.IsRead (.read .src)`). Negative example(s): `not_op_isRead_write_example` (`¬ Op.IsRead (.write .src (byteSeq 0))`).

#### `Op.WellTyped`

A write stores bytes valid at the writer's type (reads are always well typed). This is all that code using only well-typed references can do.

Lean (pretty-printed):
```lean
def Op.WellTyped : {B : Type} → {n : Nat} → Validity B n → Validity B n → Op B n → Prop :=
fun {B} {n} T U x =>
  match x with
  | Op.read s => True
  | Op.write s v => Side.ty T U s v
```
Positive example(s): `wellTyped_write_dst_two`. Negative example(s): `not_wellTyped_write_src_two`.

#### `NoInvalidRead`

Running the operations from the given contents, every read observes bytes valid at the type of the view it reads through. A read of invalid bytes models the undefined behaviour of producing an invalid value. Validity is checked only at reads: a run that never reads, or overwrites before reading, is unaffected by invalid initial contents (`noInvalidRead_unchecked_until_read`). Cast-time validity is enforced by `Sound`, which quantifies over every permitted run, including the run `readDst` that reads through the cast view immediately.

Lean (pretty-printed):
```lean
def NoInvalidRead : {B : Type} →
  {n : Nat} → Validity B n → Validity B n → Bytes B n → List (Op B n) → Prop :=
fun {B} {n} T U x x_1 => List.brecOn (motive := fun x => Bytes B n → Prop) x_1 (NoInvalidRead._f T U) x
```
Source (the recursion above is compiled; this is the definition as written):
```lean
def NoInvalidRead {B : Type} {n : Nat} (T U : Validity B n) :
    Bytes B n → List (Op B n) → Prop
  | _, [] => True
  | m, .read s :: rest => s.ty T U m ∧ NoInvalidRead T U m rest
  | _, .write _ v :: rest => NoInvalidRead T U v rest
```
Positive example(s): `noInvalidRead_example` (`NoInvalidRead boolV byteV (byteSeq 1) [.read .src, .read .dst]`: from the valid `bool` 1, reads through both views observe valid bytes). Negative example(s): `not_noInvalidRead_example` (`¬ NoInvalidRead boolV byteV (byteSeq 1) [.write .dst (byteSeq 2), .read .src]`: writing 2 through the byte view and then reading through the `bool` view observes an invalid `bool`).

#### `Protocol`

A cast discipline: which operation sequences may occur while the cast is in effect. It constrains which views perform which kinds of operation; well-typedness is imposed by `Sound`.

Lean (pretty-printed):
```lean
@[reducible] def Protocol : Type → Nat → Type :=
fun B n => List (Op B n) → Prop
```

#### `Sound`

The safety contract for a discipline P from T to U: from every T-valid initial contents, every permitted run whose writes are well typed never reads invalid bytes.

Lean (pretty-printed):
```lean
def Sound : {B : Type} → {n : Nat} → Protocol B n → Validity B n → Validity B n → Prop :=
fun {B} {n} P T U =>
  ∀ (m : Bytes B n),
    T m → ∀ (tr : List (Op B n)), P tr → (∀ (op : Op B n), op ∈ tr → Op.WellTyped T U op) → NoInvalidRead T U m tr
```
Positive example(s): `sound_positive_example` (`Sound sharedProtocol boolV byteV`: the shared cast bool → byte). Negative example(s): `sound_negative_example` (`¬ Sound mutProtocol boolV byteV`: the mutable cast bool → byte).

#### `valueProtocol`

Value transmute: the value is moved into the destination, which then reads and writes it at U; the source view does nothing more with these bytes. The empty run is permitted; validity of the transmuted value at once is recovered because `Sound` also quantifies over `readDst`.

Lean (pretty-printed):
```lean
def valueProtocol : {B : Type} → {n : Nat} → Protocol B n :=
fun {B} {n} tr => ∀ (op : Op B n), op ∈ tr → Op.side op = Side.dst
```
Positive example(s): `valueProtocol_example` (`valueProtocol [.read .dst, .write .dst (byteSeq 2), .read .dst]`: the destination reads and writes). Negative example(s): `not_valueProtocol_example` (`¬ valueProtocol [.read .src]`: the moved-from source may not act).

#### `sharedProtocol`

Shared-reference cast without interior mutability: both references read, in any interleaving; nobody writes.

Lean (pretty-printed):
```lean
def sharedProtocol : {B : Type} → {n : Nat} → Protocol B n :=
fun {B} {n} tr => ∀ (op : Op B n), op ∈ tr → Op.IsRead op
```
Positive example(s): `sharedProtocol_example` (`sharedProtocol [.read .src, .read .dst, .read .src]`: interleaved reads through both views). Negative example(s): `not_sharedProtocol_example` (`¬ sharedProtocol [.write .src (byteSeq 0)]`: no write is permitted).

#### `mutProtocol`

Mutable-reference cast: an exclusive period in which only the cast reference acts (reads and writes at U), then the owner's period (reads and writes at T). No interleaving. A run starts when the cast reference is created; whatever the owner did before is summarised by the initial contents.

Lean (pretty-printed):
```lean
def mutProtocol : {B : Type} → {n : Nat} → Protocol B n :=
fun {B} {n} tr =>
  ∃ during after,
    tr = during ++ after ∧
      (∀ (op : Op B n), op ∈ during → Op.side op = Side.dst) ∧ ∀ (op : Op B n), op ∈ after → Op.side op = Side.src
```
Positive example(s): `mutProtocol_example` (`mutProtocol [.read .dst, .write .dst (byteSeq 2), .read .src, .write .src (byteSeq 0)]`: the cast reference's exclusive period, then the owner's). Negative example(s): `not_mutProtocol_example` (the owner reads while the cast reference is still to be used), `not_mutProtocol_interleaved_example` (the owner reads between two uses of the cast reference).

#### `Op.PermittedIM`

Under interior mutability: reads always permitted; a source write iff `srcWrites`, a destination write iff `dstWrites`.

Lean (pretty-printed):
```lean
def Op.PermittedIM : {B : Type} → {n : Nat} → Bool → Bool → Op B n → Prop :=
fun {B} {n} srcWrites dstWrites x =>
  match x with
  | Op.read s => True
  | Op.write Side.src v => srcWrites = true
  | Op.write Side.dst v => dstWrites = true
```
Positive example(s): `permittedIM_example` (`Op.PermittedIM true false (.write .src (byteSeq 0))`: a source write with the source flag set). Negative example(s): `not_permittedIM_example` (`¬ Op.PermittedIM false true (.write .src (byteSeq 0))`: a source write with the source flag unset).

#### `sharedIMProtocol`

Shared-reference cast with interior mutability: both references stay live, any interleaving; each side may also write when its flag is set. With both flags false it equals `sharedProtocol` (`sharedIMProtocol_false_false : sharedIMProtocol false false = sharedProtocol`, in `ToyTransmute/Tools.lean`).

Lean (pretty-printed):
```lean
def sharedIMProtocol : {B : Type} → {n : Nat} → Bool → Bool → Protocol B n :=
fun {B} {n} srcWrites dstWrites tr => ∀ (op : Op B n), op ∈ tr → Op.PermittedIM srcWrites dstWrites op
```
Positive example(s): `sharedIMProtocol_example` (`sharedIMProtocol true true [.write .src (byteSeq 1), .write .dst (byteSeq 2), .read .src]`: with both flags set, both views write, interleaved with reads). Negative example(s): `not_sharedIMProtocol_example` (`¬ sharedIMProtocol true false [.write .dst (byteSeq 2)]`: with only the source side writable, a write through the cast view is not permitted).

#### `ValueSound`

`Sound valueProtocol`.

Lean (pretty-printed):
```lean
def ValueSound : {B : Type} → {n : Nat} → Validity B n → Validity B n → Prop :=
fun {B} {n} T U => Sound valueProtocol T U
```
Positive example(s): `valueSound_boolV_byteV`. Negative example(s): `not_valueSound_byteV_boolV`.

#### `SharedSound`

`Sound sharedProtocol`.

Lean (pretty-printed):
```lean
def SharedSound : {B : Type} → {n : Nat} → Validity B n → Validity B n → Prop :=
fun {B} {n} T U => Sound sharedProtocol T U
```
Positive example(s): `sharedSound_boolV_byteV`. Negative example(s): `not_sharedSound_byteV_boolV`.

#### `MutSound`

`Sound mutProtocol`.

Lean (pretty-printed):
```lean
def MutSound : {B : Type} → {n : Nat} → Validity B n → Validity B n → Prop :=
fun {B} {n} T U => Sound mutProtocol T U
```
Positive example(s): `mutSound_boolV_boolV'`. Negative example(s): `not_mutSound_boolV_byteV`, `not_mutSound_byteV_boolV`.

#### `SharedIMSound`

`Sound (sharedIMProtocol srcWrites dstWrites)`.

Lean (pretty-printed):
```lean
def SharedIMSound : {B : Type} → {n : Nat} → Bool → Bool → Validity B n → Validity B n → Prop :=
fun {B} {n} srcWrites dstWrites T U => Sound (sharedIMProtocol srcWrites dstWrites) T U
```
Positive example(s): `sharedIMSound_boolV_boolV'`, `sharedIMSound_true_false_boolV_byteV`. Negative example(s): `not_sharedIMSound_dst_boolV_byteV`.

#### `CheckedSound`

The safety contract for a cast checked once at cast time: only initial contents valid at both T and U are considered (the check rejected the rest); the run after the check is unchecked, exactly as in `Sound`. Models fallible conversions that validate once and then return an ordinary value or reference.

Lean (pretty-printed):
```lean
def CheckedSound : {B : Type} → {n : Nat} → Protocol B n → Validity B n → Validity B n → Prop :=
fun {B} {n} P T U =>
  ∀ (m : Bytes B n),
    T m → U m → ∀ (tr : List (Op B n)), P tr → (∀ (op : Op B n), op ∈ tr → Op.WellTyped T U op) → NoInvalidRead T U m tr
```
Positive example(s): `checkedSound_mut_byteV_boolV` (checked `&mut byte → &mut bool`). Negative example(s): `not_checkedSound_mut_boolV_byteV` (checked `&mut bool → &mut byte`: write 2 through the byte view, read the bool).

#### `Validity.meet`

Intersection of validities (valid for both).

Lean (pretty-printed):
```lean
def Validity.meet : {B : Type} → {n : Nat} → Validity B n → Validity B n → Validity B n :=
fun {B} {n} T U m => T m ∧ U m
```
Positive example(s): `meet_boolV_zeroV_zero`. Negative example(s): `not_meet_boolV_zeroV_one`.

#### `Validity.join`

Union of validities (valid for either). The validity of a hypothetical 'either T or U' type of the same size, not of a Rust union.

Lean (pretty-printed):
```lean
def Validity.join : {B : Type} → {n : Nat} → Validity B n → Validity B n → Validity B n :=
fun {B} {n} T U m => T m ∨ U m
```
Positive example(s): `join_boolV_twoV_two`. Negative example(s): `not_join_boolV_twoV_three`.

#### Fixtures (one-byte types over `Fin 256`)

#### `byteSeq`

The one-byte sequence `x`.

Lean (pretty-printed):
```lean
def byteSeq : Fin 256 → Bytes (Fin 256) 1 :=
fun x x_1 => x
```

#### `boolV`

bool-like: valid bytes 0 and 1.

Lean (pretty-printed):
```lean
def boolV : Validity (Fin 256) 1 :=
fun m => m 0 = 0 ∨ m 0 = 1
```
Positive example(s): `boolV_byteSeq_zero`, `boolV_byteSeq_one`. Negative example(s): `not_boolV_byteSeq_two`.

#### `boolV'`

Same validity as `boolV`, written as `val < 2` (tests extensionality).

Lean (pretty-printed):
```lean
def boolV' : Validity (Fin 256) 1 :=
fun m => ↑(m 0) < 2
```
Positive example(s): `boolV'_byteSeq_one`. Negative example(s): `not_boolV'_byteSeq_two`.

#### `byteV`

Raw initialised byte: every byte valid. Intended total; no negative example by design (`byteV_total`).

Lean (pretty-printed):
```lean
def byteV : Validity (Fin 256) 1 :=
fun x => True
```
Positive example(s): `byteV_total`. Negative example(s): — (by design; see intent).

#### `neverV`

Uninhabited one-byte type. Intended empty; no positive example by design (`neverV_empty`).

Lean (pretty-printed):
```lean
def neverV : Validity (Fin 256) 1 :=
fun x => False
```
Positive example(s): — (by design; see intent). Negative example(s): `neverV_empty`.

#### `zeroV`

Only byte 0 valid (unit-like enumeration).

Lean (pretty-printed):
```lean
def zeroV : Validity (Fin 256) 1 :=
fun m => m 0 = 0
```
Positive example(s): `zeroV_byteSeq_zero`. Negative example(s): `not_zeroV_byteSeq_one`.

#### `twoV`

Only byte 2 valid.

Lean (pretty-printed):
```lean
def twoV : Validity (Fin 256) 1 :=
fun m => m 0 = 2
```
Positive example(s): `twoV_byteSeq_two`. Negative example(s): `not_twoV_byteSeq_zero`.

#### Proof-tool vocabulary (`ToyTransmute/Tools.lean`)

#### `readDst`

The run 'read once through the cast view'.

Lean (pretty-printed):
```lean
def readDst : {B : Type} → {n : Nat} → List (Op B n) :=
fun {B} {n} => [Op.read Side.dst]
```

#### `writeDstReadSrc`

The run 'write `u` through the cast view, then read through the original view'.

Lean (pretty-printed):
```lean
def writeDstReadSrc : {B : Type} → {n : Nat} → Bytes B n → List (Op B n) :=
fun {B} {n} u => [Op.write Side.dst u, Op.read Side.src]
```

#### `Op.Preserves`

Compatibility of a region invariant `I` with one operation (used by `sound_of_invariant`).

Lean (pretty-printed):
```lean
def Op.Preserves : {B : Type} →
  {n : Nat} → Validity B n → Validity B n → (Bytes B n → Prop) → Op B n → Prop :=
fun {B} {n} T U I x =>
  match x with
  | Op.read s => ∀ (m : Bytes B n), I m → Side.ty T U s m
  | Op.write s v => Side.ty T U s v → I v
```
Positive example(s): `op_preserves_read_dst_example` (`Op.Preserves boolV byteV boolV (.read .dst)`: the region invariant `bool` implies validity for a read through the byte view). Negative example(s): `not_op_preserves_write_dst_example` (`¬ Op.Preserves boolV byteV boolV (.write .dst (byteSeq 2))`: writing 2 through the byte view does not re-establish the invariant `bool`).

#### `writeSrcReadDst`

The run 'write `v` through the original view, then read through the cast view' (used for checked casts with source-side writes).

Lean (pretty-printed):
```lean
def writeSrcReadDst : {B : Type} → {n : Nat} → Bytes B n → List (Op B n) :=
fun {B} {n} v => [Op.write Side.src v, Op.read Side.dst]
```

### Result cards

All cards share one design question, repeated in each card.

#### R1: `valueSound_iff_includes`

- **Kind:** characterization.
- **Tier:** T1. The value-transmute condition is stated informally in the Rust safe-transmute design documents (MCP 411) and elsewhere; this is a mechanized statement of it in a small operational model.
- **Plain claim:** A value transmute from T to U, two types of the same size, is sound (no permitted, well-typed use of the destination value ever reads bytes that are invalid at U) if and only if every T-valid byte sequence is U-valid.

Lean (`valueSound_iff_includes`):
```lean
valueSound_iff_includes : ∀ {B : Type} {n : Nat} (T U : Validity B n), ValueSound T U ↔ Includes T U
```
Unfolded:
```lean
(∀ m, T m → ∀ tr, (∀ op ∈ tr, op.side = .dst) → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr)
  ↔ (∀ m, T m → U m)
```

- **Hypothesis ledger:**
  - `(none: an equivalence with no hypotheses)`: The statement is universally quantified over all byte alphabets, sizes and validity predicates (source and destination share the size index n). Tightness: **harmless**.
  - `right-hand side: Includes T U`: Needed by the very first read of the transmuted value at U. Tightness: **tight**; counterexample `byteV_to_boolV_unsound_even_by_value`. byte -> bool: Includes fails and ValueSound fails (transmuting the byte 2).
- **Depth:** shallow. Necessity: the one-step run readDst (not_sound_of_read_dst). Sufficiency: induction over the run with invariant U.
- **Non-vacuity witness:** Both sides true for bool -> byte, both false for byte -> bool. Lean: `valueSound_iff_includes_nonvacuous`.
- **Related witnesses:** `noInvalidRead_unchecked_until_read`. Validity is checked at reads: an unused or overwritten transmuted value is not checked by an individual run; Sound recovers cast-time validity by quantifying over the run that reads immediately.
- **Prior art** (full records under Evidence, Primary sources): [MCP411] rustc MCP 411, Lang Item for Transmutability; [WRENN] Wrenn 2024, Safety Goggles for Alchemists; [REF_UB] Rust Reference, Behavior considered undefined; [MINIRUST] MiniRust representation relation; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [TRANSMUTEFROM] core::mem::TransmuteFrom and core::mem::Assume (nightly docs); [UCG] Unsafe Code Guidelines glossary, validity vs safety invariant; [JUNG_BLOG] Jung 2018, Two Kinds of Invariants; [RUSTBELT] Jung et al., RustBelt, POPL 2018; [RUSTC] rustc_transmute source and UI test at a pinned commit; [AENEAS] Aeneas PR #1447 (layouts and abstract bytes, work in progress); [RFC2835] RFC 2835, project-safe-transmute; [KREBBERS] Krebbers, C memory model / C11 aliasing restrictions in Coq; [TUCH] Tuch, Klein, Norrish, Types, Bytes, and Separation Logic, POPL 2007; [REFINEDC] Sammler et al., RefinedC, PLDI 2021; [REFINEDRUST] Gäher et al., RefinedRust, PLDI 2024.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R1.
- Basis: execution (Lean kernel check): `valueSound_iff_includes` and the witnesses named above.
- Basis: derived (modeling bridge): Read through modeling-bridge items 1, 2 and 9, R1 is the familiar condition for a value transmute between two same-size types without padding or uninitialised bytes and without pointer-valued fields: every bit pattern valid for the source must be valid for the destination ([MCP411], [WRENN]). The model represents Rust's 'producing an invalid value' ([REF_UB] rule [undefined.invalid]) as a read of invalid bytes, and the value transmute as the discipline in which only the destination acts. zerocopy 0.8.63's `transmute!` (`Src: IntoBytes, Dst: FromBytes`, equal sizes) enforces a sufficient form of the condition: every `Src`-valid sequence is initialised and every initialised sequence is `Dst`-valid, so `T ⊆ U` by transitivity ([ZEROCOPY]).

#### R2: `sharedSound_iff_includes`

- **Kind:** characterization.
- **Tier:** T1. Folklore (a read-only reinterpretation needs exactly the value-transmute condition); the sufficiency direction has a mechanized analogue for semantic subtyping (shr_subtype in the RustHornBelt Coq development). Stated here as an exact characterization for an operational model with interleaved reads through both views.
- **Plain claim:** A shared-reference cast from T to U, two types of the same size whose views cover the same region, where the original and the cast reference may both read in any interleaving and nobody writes, never reads invalid bytes if and only if every T-valid byte sequence is U-valid.

Lean (`sharedSound_iff_includes`):
```lean
sharedSound_iff_includes : ∀ {B : Type} {n : Nat} (T U : Validity B n), SharedSound T U ↔ Includes T U
```
Unfolded:
```lean
(∀ m, T m → ∀ tr, (∀ op ∈ tr, op.IsRead) → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr)
  ↔ (∀ m, T m → U m)
-- (op.WellTyped T U holds trivially for reads, so the third premise is vacuous here)
```

- **Hypothesis ledger:**
  - `(none: an equivalence with no hypotheses)`: The statement is universally quantified over all byte alphabets, sizes and validity predicates (source and destination share the size index n). Tightness: **harmless**.
  - `right-hand side: Includes T U`: Needed by a read through the cast reference. Tightness: **tight**; counterexample `byteV_to_boolV_unsound_even_by_value`. byte -> bool: Includes fails and SharedSound fails.
- **Depth:** shallow. Necessity: readDst. Sufficiency: invariant T (no writes, so the contents never change).
- **Non-vacuity witness:** Both sides true for bool -> byte, both false for byte -> bool. Lean: `sharedSound_iff_includes_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [MCP411] rustc MCP 411, Lang Item for Transmutability; [RUSTC] rustc_transmute source and UI test at a pinned commit; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [REF_VAR] Rust Reference, Subtyping and variance; [RUSTHORNBELT] Matsushita et al., RustHornBelt, PLDI 2022, and its Coq development; [RUSTBELT] Jung et al., RustBelt, POPL 2018; [REYNOLDS] Reynolds, Design of the Programming Language Forsythe, 1997; [PIERCE_SANGIORGI] Pierce and Sangiorgi, Typing and Subtyping for Mobile Processes, MSCS 1996; [TRANSMUTEFROM] core::mem::TransmuteFrom and core::mem::Assume (nightly docs).
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R2.
- Basis: execution (Lean kernel check): `sharedSound_iff_includes` and the witnesses named above.
- Basis: derived (modeling bridge): For a Rust `&T → &U` cast in which neither referent contains `UnsafeCell`, the referents have the same size and the address is suitably aligned, R2 says the bit-validity requirement is exactly `T ⊆ U`. rustc's checker requires forward referent transmutability for every reference cast ([RUSTC], `mod.rs` lines 276-282), and zerocopy's `transmute_ref!` (`Src: IntoBytes + Immutable`, `Dst: FromBytes + Immutable`) implies `T ⊆ U` by the argument given for R1 ([ZEROCOPY]). Reasoning: with no writes the region never changes, which is what `Immutable` on both referents guarantees in Rust.

#### R3: `mutSound_iff_includes_and_satisfiable_imp_includes_rev`

- **Kind:** characterization.
- **Tier:** T1. The two-direction requirement for mutable references is stated informally in the Safer Transmute RFC text and implemented in rustc's transmutability checker; its sufficiency direction has a mechanized analogue for semantic subtyping (uniq_subtype in the RustHornBelt Coq development), and the read/write capability decomposition is classic (Reynolds; Pierce and Sangiorgi). The exact characterization with the satisfiability side condition is folklore made precise.
- **Plain claim:** An unchecked mutable-reference cast from T to U, two types of the same size whose views cover the same region (the cast reference is used exclusively, then the owner resumes at T), is sound if and only if every T-valid byte sequence is U-valid and, provided T has at least one valid byte sequence, every U-valid byte sequence is T-valid.

Lean (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`):
```lean
mutSound_iff_includes_and_satisfiable_imp_includes_rev : ∀ {B : Type} {n : Nat} (T U : Validity B n),
  MutSound T U ↔ Includes T U ∧ (Satisfiable T → Includes U T)
```
Unfolded:
```lean
(∀ m, T m → ∀ tr, (∃ during after, tr = during ++ after ∧ (∀ op ∈ during, op.side = .dst) ∧ (∀ op ∈ after, op.side = .src)) →
     (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr)
  ↔ (∀ m, T m → U m) ∧ ((∃ m, T m) → ∀ m, U m → T m)
```

- **Hypothesis ledger:**
  - `(none: an equivalence with no hypotheses)`: The statement is universally quantified over all byte alphabets, sizes and validity predicates (source and destination share the size index n). Tightness: **harmless**.
  - `right-hand side: Includes T U (read side)`: Needed by a read through the cast reference before any write. Tightness: **tight**; counterexample `byteV_to_boolV_unsound_even_by_value`. byte -> bool: the write-side condition holds (bool ⊆ byte), the read-side condition fails, and MutSound fails.
  - `right-hand side: Satisfiable T -> Includes U T (write side)`: Needed because a U-valid value written through the cast reference is later read at T by the owner. Tightness: **tight**; counterexample `mutSound_needs_includes_rev`. bool -> byte: the read-side condition holds, bool is satisfiable, byte ⊈ bool, and MutSound fails (explicit run: boolV_to_byteV_mut_violating_run).
  - `right-hand side: the guard 'Satisfiable T ->' on the write side`: Exactness: without the guard the right-hand side would read T ⊆ U ∧ U ⊆ T, which is false for an uninhabited T whose casts are vacuously sound. Tightness: **tight**; counterexample `mutSound_rhs_needs_satisfiable_guard`, `mutSound_eq_needs_satisfiable`. never -> byte: MutSound holds and never ⊆ byte holds, but byte ⊈ never, so the unguarded equivalence fails.
- **Depth:** shallow. Necessity: runs readDst and writeDstReadSrc u. Sufficiency: if T is satisfiable both inclusions give T ≡ U and the invariant T works across both periods; otherwise vacuous.
- **Non-vacuity witness:** Both sides true for bool -> bool' (same validity, different definitions); both false for bool -> byte. Lean: `mutSound_exact_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [RUSTC] rustc_transmute source and UI test at a pinned commit; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [REF_VAR] Rust Reference, Subtyping and variance; [RUSTHORNBELT] Matsushita et al., RustHornBelt, PLDI 2022, and its Coq development; [RUSTBELT] Jung et al., RustBelt, POPL 2018; [JUNG_THESIS] Jung 2020, PhD thesis; [REYNOLDS] Reynolds, Design of the Programming Language Forsythe, 1997; [PIERCE_SANGIORGI] Pierce and Sangiorgi, Typing and Subtyping for Mobile Processes, MSCS 1996; [JLS] JLS SE 21, array covariance and ArrayStoreException; [REF_UB] Rust Reference, Behavior considered undefined.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R3.
- Basis: execution (Lean kernel check): `mutSound_iff_includes_and_satisfiable_imp_includes_rev` and the witnesses named above.
- Basis: derived (modeling bridge): For a Rust `&mut T → &mut U` cast between same-size referents, R3 corresponds to the rule implemented by rustc's transmutability checker at commit `5b216e01a117532b30f061f3dff8a61408113c77`: the referents must be transmutable forwards and, for a mutable destination reference, backwards (`compiler/rustc_transmute/src/maybe_transmutable/mod.rs` lines 92-93 and 276-282), and to the Safer Transmute RFC text's rule that a mutate-able reference 'may also not expand the bit-validity of the referenced type' ([RFC2981]). rustc answers Yes for an uninhabited source (lines 112-119), matching the vacuous case. The Rust Reference, rule [undefined.validity.reference-box], requires a reference to 'point to a valid value' and notes that this point 'remains a subject of some debate'; under that requirement a reference to an uninhabited type is never valid, so the vacuous case does not license creating one. zerocopy's `transmute_mut!` requires `FromBytes + IntoBytes` on both sides, which makes both validities equal to the set of initialised byte sequences, a special case of `T ≡ U` ([ZEROCOPY]).

#### R3-eq: `mutSound_iff_validityEq_of_satisfiable`

- **Kind:** characterization.
- **Tier:** T1. Same status as R3; this is the commonly quoted 'mutable casts need equal validity' form, with its hidden satisfiability hypothesis made explicit.
- **Plain claim:** If the source type T has at least one valid byte sequence, an unchecked mutable-reference cast from T to a type U of the same size (both views covering the same region) is sound if and only if T and U have exactly the same valid byte sequences.

Lean (`mutSound_iff_validityEq_of_satisfiable`):
```lean
mutSound_iff_validityEq_of_satisfiable : ∀ {B : Type} {n : Nat} {T U : Validity B n},
  Satisfiable T → (MutSound T U ↔ ValidityEq T U)
```
Unfolded:
```lean
(∃ m, T m) → (Sound mutProtocol T U ↔ ∀ m, T m ↔ U m)
```

- **Hypothesis ledger:**
  - `hT : Satisfiable T`: Excludes the uninhabited source, for which every mutable cast is vacuously sound. Tightness: **tight**; counterexample `mutSound_eq_needs_satisfiable`. never -> byte: not satisfiable; MutSound holds; validities differ; so the equivalence fails.
- **Depth:** definitional. Propositional corollary of R3 (one or two lines given R3).
- **Non-vacuity witness:** bool -> bool' (satisfiable, sound, equal validity). Lean: `mutSound_eq_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [RUSTC] rustc_transmute source and UI test at a pinned commit; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [RUSTHORNBELT] Matsushita et al., RustHornBelt, PLDI 2022, and its Coq development; [RUSTBELT] Jung et al., RustBelt, POPL 2018.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R3-eq.
- Basis: execution (Lean kernel check): `mutSound_iff_validityEq_of_satisfiable` and the witnesses named above.
- Basis: derived (modeling bridge): Same reading as R3: for an inhabited referent type `T`, the rustc rule (forward and reverse referent transmutability for `&mut` destinations; [RUSTC] `mod.rs` lines 276-282) amounts to equal bit validity in this model. The reverse obligation is stated as a comment at `mod.rs` lines 92-93.

#### R3-imp: `not_mutSound_of_satisfiable_of_not_validityEq`

- **Kind:** impossibility.
- **Tier:** T1. Impossibility reading of R3-eq.
- **Plain claim:** No unchecked mutable-reference cast from a type T with at least one valid byte sequence to a type U of the same size (both views covering the same region) whose validity differs from T's is sound.

Lean (`not_mutSound_of_satisfiable_of_not_validityEq`):
```lean
not_mutSound_of_satisfiable_of_not_validityEq : ∀ {B : Type} {n : Nat} {T U : Validity B n},
  Satisfiable T → ¬ValidityEq T U → ¬MutSound T U
```
Unfolded:
```lean
(∃ m, T m) → ¬ (∀ m, T m ↔ U m) → ¬ Sound mutProtocol T U
```

- **Hypothesis ledger:**
  - `hT : Satisfiable T`: Excludes the vacuously sound uninhabited source. Tightness: **tight**; counterexample `not_mutSound_needs_satisfiable`. never -> byte: validities differ and the mutable cast is sound.
  - `hne : ¬ ValidityEq T U`: The validities must differ. Tightness: **tight**; counterexample `not_mutSound_needs_not_validityEq`. bool -> bool': equal validity, sound.
- **Depth:** definitional. Contrapositive of R3-eq.
- **Non-vacuity witness:** bool -> byte satisfies both hypotheses (and is confirmed unsound directly). Lean: `not_mutSound_nonvacuous`.
- **Positive control:** `not_mutSound_positive_control_weaker_casts`, `not_mutSound_needs_satisfiable`, `checkedSound_mut_escapes_impossibility`. Weakening the cast kind: for the same bool -> byte pair the value transmute, the shared cast, and the shared cast with source-only writes are sound. Dropping satisfiability: never -> byte is a sound mutable cast with different validity. Checking at cast time: byte -> bool checked once at cast time is sound although the validities differ.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [RUSTC] rustc_transmute source and UI test at a pinned commit; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [JLS] JLS SE 21, array covariance and ArrayStoreException.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R3-imp.
- Basis: execution (Lean kernel check): `not_mutSound_of_satisfiable_of_not_validityEq` and the witnesses named above.
- Basis: derived (modeling bridge): In Rust terms: no unchecked `&mut T → &mut U` cast between same-size referents, with `T` inhabited and with different bit validities, is sound for bit validity. zerocopy 0.8.63's `try_transmute_mut!` escapes the impossibility by checking validity at `U` once at cast time, which is the checked discipline of R8-mut ([ZEROCOPY]); Java arrays escape the analogous covariance problem with a run-time check on every store ([JLS]), a discipline not modelled here.

#### R4: `sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`

- **Kind:** characterization.
- **Tier:** T1. The interior-mutability rule is stated informally in the Safer Transmute RFC text (shared references to UnsafeCell bytes are 'mutate-able'); capability-indexed read/write subtyping is classic (Pierce and Sangiorgi). Folklore made precise, parametrically in which side may write, which exposes that source-side writes add no validity requirement.
- **Plain claim:** An unchecked shared-reference cast from T to U (one that accepts every T-valid value without inspecting it), two types of the same size whose views cover the same region, in which both references stay live, the source side may write T-valid values iff srcWrites and the destination side may write U-valid values iff dstWrites, is sound for bit validity in this model (aliasing rules are not modelled) if and only if every T-valid byte sequence is U-valid and, when the destination side may write and T has a valid byte sequence, every U-valid byte sequence is T-valid; srcWrites does not matter.

Lean (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`):
```lean
sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev : ∀ {B : Type} {n : Nat}
  (srcWrites dstWrites : Bool) (T U : Validity B n),
  SharedIMSound srcWrites dstWrites T U ↔ Includes T U ∧ (dstWrites = true → Satisfiable T → Includes U T)
```
Unfolded:
```lean
(∀ m, T m → ∀ tr, (∀ op ∈ tr, op.PermittedIM srcWrites dstWrites) → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr)
  ↔ (∀ m, T m → U m) ∧ (dstWrites = true → (∃ m, T m) → ∀ m, U m → T m)
-- op.PermittedIM s d: reads always; a source write iff s = true; a destination write iff d = true
```

- **Hypothesis ledger:**
  - `(none: an equivalence with no hypotheses)`: The statement is universally quantified over all byte alphabets, sizes and validity predicates (source and destination share the size index n). Tightness: **harmless**.
  - `right-hand side: Includes T U`: Needed by reads through the cast reference (of the initial value, or of values written by the source side). Tightness: **tight**; counterexample `sharedIMSound_needs_includes_canonical`. byte -> bool, every pair of flags: the other conjunct holds, Includes fails, the cast is unsound.
  - `right-hand side: dstWrites = true -> Satisfiable T -> Includes U T`: Needed because a value written through the cast reference is read back at T through the original reference. Tightness: **tight**; counterexample `sharedIMSound_needs_includes_rev_canonical`. bool -> byte with the destination flag set: Includes T U holds, bool is satisfiable, byte ⊈ bool, the cast is unsound.
  - `right-hand side: the guard 'dstWrites = true ->'`: Exactness: with only source-side writes, inclusion suffices. Tightness: **tight**; counterexample `sharedIMSound_rhs_needs_dstWrites_guard`. bool -> byte without destination writes, either source flag: sound, but the unguarded right-hand side is false.
  - `right-hand side: the guard 'Satisfiable T ->'`: Exactness for uninhabited sources. Tightness: **tight**; counterexample `sharedIMSound_rhs_needs_satisfiable_guard`. never -> byte with the destination flag set, either source flag: sound, but the unguarded right-hand side is false.
- **Depth:** shallow. Necessity: readDst and writeDstReadSrc u (the latter is permitted exactly when dstWrites). Sufficiency: invariant T.
- **Non-vacuity witness:** Both sides true for bool -> bool' (both flags) and bool -> byte (source flag only); both false for bool -> byte (destination flag set). Lean: `sharedIMSound_exact_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [RUSTC] rustc_transmute source and UI test at a pinned commit; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [REF_VAR] Rust Reference, Subtyping and variance; [RUSTHORNBELT] Matsushita et al., RustHornBelt, PLDI 2022, and its Coq development; [STACKED_BORROWS] Jung et al., Stacked Borrows, POPL 2020; [TREE_BORROWS] Villani et al., Tree Borrows, PLDI 2025; [JUNG_THESIS] Jung 2020, PhD thesis; [PIERCE_SANGIORGI] Pierce and Sangiorgi, Typing and Subtyping for Mobile Processes, MSCS 1996.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R4.
- Basis: execution (Lean kernel check): `sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev` and the witnesses named above.
- Basis: derived (modeling bridge): The Safer Transmute RFC text classifies shared references whose referents contain `UnsafeCell` bytes as 'mutate-able' and requires that such casts not expand bit validity ([RFC2981]); R4 refines this by the side that may write. rustc's checker at the pinned commit requires only the destination referent of a shared-reference cast to be free of interior mutability (`Condition::Immutable { ty: dst_ref.referent }`, `mod.rs` lines 276-282) and places no such condition on the source referent; in the model the destination-immutable case is `dstWrites = false`, for which R4 requires only `T ⊆ U` (R4-src). The source-writes case is sound for bit validity in the model, but in Rust it is governed by the aliasing model ([STACKED_BORROWS], [TREE_BORROWS]), which is not modelled; zerocopy's `transmute_ref!` excludes it by requiring `Immutable` on both sides ([ZEROCOPY]).

#### R4-eq: `sharedIMSound_dstWrites_iff_validityEq_of_satisfiable`

- **Kind:** characterization.
- **Tier:** T1. The interior-mutability rule of the Safer Transmute RFC text, made precise, with its two hidden hypotheses (destination-side writes, satisfiable source) explicit.
- **Plain claim:** If the destination side of an unchecked shared cast with interior mutability between two types T and U of the same size (both views covering the same region) may write and T has a valid byte sequence, the cast is sound for bit validity in this model if and only if T and U accept exactly the same byte sequences, regardless of whether the source side may write.

Lean (`sharedIMSound_dstWrites_iff_validityEq_of_satisfiable`):
```lean
sharedIMSound_dstWrites_iff_validityEq_of_satisfiable : ∀ {B : Type} {n : Nat} (srcWrites : Bool) {T U : Validity B n},
  Satisfiable T → (SharedIMSound srcWrites true T U ↔ ValidityEq T U)
```
Unfolded:
```lean
(∃ m, T m) → (Sound (sharedIMProtocol srcWrites true) T U ↔ ∀ m, T m ↔ U m)
```

- **Hypothesis ledger:**
  - `dstWrites = true (instantiated in the statement)`: Destination-side writes are what force the reverse inclusion. Tightness: **tight**; counterexample `sharedIMSound_eq_needs_dstWrites`. With only source-side writes, bool -> byte is sound but the validities differ. This refutes the reading 'shared casts where either side can write need equality'.
  - `hT : Satisfiable T`: Excludes the vacuously sound uninhabited source. Tightness: **tight**; counterexample `sharedIMSound_eq_needs_satisfiable`. never -> byte, both flags set: sound, validities differ.
- **Depth:** definitional. Specialization of R4 at dstWrites = true.
- **Non-vacuity witness:** bool -> bool' with both flags set. Lean: `sharedIMSound_eq_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [RUSTC] rustc_transmute source and UI test at a pinned commit; [RUSTHORNBELT] Matsushita et al., RustHornBelt, PLDI 2022, and its Coq development.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R4-eq.
- Basis: execution (Lean kernel check): `sharedIMSound_dstWrites_iff_validityEq_of_satisfiable` and the witnesses named above.
- Basis: derived (modeling bridge): Reading as for R4: when the destination referent may be mutated through the shared reference (it contains `UnsafeCell` over the region) and the source type is inhabited, bit-validity soundness requires equal validities, matching the RFC's mutate-able-reference rule ([RFC2981]). This does not say rustc accepts such casts: it rejects `&UnsafeCell<u8> → &UnsafeCell<u8>` because the two types may use incompatible synchronization strategies ([RUSTC], `tests/ui/transmutability/references/unsafecell.rs` lines 25-29).

#### R4-src: `sharedIMSound_noDstWrites_iff_includes`

- **Kind:** characterization.
- **Tier:** T1. Direct consequence of the read/write argument; not found stated explicitly in the sources consulted, but too elementary to claim as novel.
- **Plain claim:** If the destination side of an unchecked shared cast between two types T and U of the same size (both views covering the same region) may not write, the cast is sound for bit validity in this model (aliasing rules are not modelled) if and only if every T-valid byte sequence is U-valid, even when the source side writes T-valid values.

Lean (`sharedIMSound_noDstWrites_iff_includes`):
```lean
sharedIMSound_noDstWrites_iff_includes : ∀ {B : Type} {n : Nat} (srcWrites : Bool) (T U : Validity B n),
  SharedIMSound srcWrites false T U ↔ Includes T U
```
Unfolded:
```lean
Sound (sharedIMProtocol srcWrites false) T U ↔ ∀ m, T m → U m
```

- **Hypothesis ledger:**
  - `dstWrites = false (instantiated in the statement)`: With destination-side writes the reverse inclusion is also needed. Tightness: **tight**; counterexample `sharedIMSound_noDst_needs_noDstWrites`. bool -> byte with the destination flag set: Includes holds, the cast is unsound.
  - `right-hand side: Includes T U`: Reads through the cast reference. Tightness: **tight**; counterexample `sharedIMSound_needs_includes`.
- **Depth:** definitional. Specialization of R4 at dstWrites = false.
- **Non-vacuity witness:** bool -> byte with only the source flag set. Lean: `sharedIMSound_noDst_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RUSTC] rustc_transmute source and UI test at a pinned commit; [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [STACKED_BORROWS] Jung et al., Stacked Borrows, POPL 2020; [TREE_BORROWS] Villani et al., Tree Borrows, PLDI 2025.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R4-src.
- Basis: execution (Lean kernel check): `sharedIMSound_noDstWrites_iff_includes` and the witnesses named above.
- Basis: derived (modeling bridge): Reading as for R4: a shared cast whose destination referent is free of interior mutability needs only `T ⊆ U` for bit validity, even if the source side writes; this is the case rustc's checker leaves unconstrained on the source side ([RUSTC], `mod.rs` lines 276-282), and whose legality in Rust is decided by the aliasing model, not by validity.

#### R4-mut: `mutSound_iff_sharedIMSound_dstWrites`

- **Kind:** characterization.
- **Tier:** T1. Makes precise the informal grouping of &mut T with interior-mutable &T as 'mutate-able references'.
- **Plain claim:** For two types T and U of the same size whose views cover the same region, an unchecked mutable-reference cast from T to U is sound exactly when the unchecked shared cast with interior mutability from T to U in which the destination side may write is sound for bit validity (whether or not the source side may also write).

Lean (`mutSound_iff_sharedIMSound_dstWrites`):
```lean
mutSound_iff_sharedIMSound_dstWrites : ∀ {B : Type} {n : Nat} (srcWrites : Bool) (T U : Validity B n),
  MutSound T U ↔ SharedIMSound srcWrites true T U
```
Unfolded:
```lean
Sound mutProtocol T U ↔ Sound (sharedIMProtocol srcWrites true) T U
```

- **Hypothesis ledger:**
  - `dstWrites = true (instantiated in the statement)`: Mutable soundness coincides with the destination-writable shared discipline only. Tightness: **tight**; counterexample `mutSound_iff_sharedIM_needs_dstWrites`. bool -> byte: MutSound fails but the source-only-writes shared cast is sound.
- **Depth:** definitional. Both sides have the same characterization (R3, R4); the two disciplines are different sets of runs (phased vs interleaved).
- **Non-vacuity witness:** bool -> bool' is sound under all three disciplines. Lean: `mutSound_iff_sharedIM_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [REF_VAR] Rust Reference, Subtyping and variance.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R4-mut.
- Basis: execution (Lean kernel check): `mutSound_iff_sharedIMSound_dstWrites` and the witnesses named above.
- Basis: derived (modeling bridge): The RFC text groups `&mut T` with interior-mutable `&T` as 'mutate-able references' ([RFC2981]); R4-mut confirms that the two have the same bit-validity condition in the model. Their aliasing rules in Rust differ and are not modelled.

#### R5-trans: `valueSound_trans`, `sharedSound_trans`, `mutSound_trans`, `sharedIMSound_trans`

- **Kind:** theorem.
- **Tier:** T1. Composability of transmutability is folklore; the mutable case is checked here including chains that start at an unsatisfiable type.
- **Plain claim:** For each cast kind (value, shared, unchecked mutable, and shared with interior mutability for fixed write permissions) and types T, U, V of the same size, if the casts T -> U and U -> V are sound then the cast T -> V is sound.

Lean (`valueSound_trans`):
```lean
valueSound_trans : ∀ {B : Type} {n : Nat} {T U V : Validity B n}, ValueSound T U → ValueSound U V → ValueSound T V
```
Unfolded:
```lean
Sound valueProtocol T U → Sound valueProtocol U V → Sound valueProtocol T V
```

Lean (`sharedSound_trans`):
```lean
sharedSound_trans : ∀ {B : Type} {n : Nat} {T U V : Validity B n}, SharedSound T U → SharedSound U V → SharedSound T V
```
Unfolded:
```lean
Sound sharedProtocol T U → Sound sharedProtocol U V → Sound sharedProtocol T V
```

Lean (`mutSound_trans`):
```lean
mutSound_trans : ∀ {B : Type} {n : Nat} {T U V : Validity B n}, MutSound T U → MutSound U V → MutSound T V
```
Unfolded:
```lean
Sound mutProtocol T U → Sound mutProtocol U V → Sound mutProtocol T V
```

Lean (`sharedIMSound_trans`):
```lean
sharedIMSound_trans : ∀ {B : Type} {n : Nat} (srcWrites dstWrites : Bool) {T U V : Validity B n},
  SharedIMSound srcWrites dstWrites T U → SharedIMSound srcWrites dstWrites U V → SharedIMSound srcWrites dstWrites T V
```
Unfolded:
```lean
Sound (sharedIMProtocol srcWrites dstWrites) T U → Sound (sharedIMProtocol srcWrites dstWrites) U V
  → Sound (sharedIMProtocol srcWrites dstWrites) T V
```

- **Hypothesis ledger:**
  - `h₁ : Sound(T -> U)`: First leg. Tightness: **tight**; counterexample `valueSound_trans_needs_first`, `sharedSound_trans_needs_first`, `mutSound_trans_needs_first`, `sharedIMSound_trans_needs_first`. (T, U, V) = (byte, bool, bool): the second leg bool -> bool is sound, the composite byte -> bool is not.
  - `h₂ : Sound(U -> V)`: Second leg. Tightness: **tight**; counterexample `valueSound_trans_needs_second`, `sharedSound_trans_needs_second`, `mutSound_trans_needs_second`, `sharedIMSound_trans_needs_second`. (T, U, V) = (byte, byte, bool): the first leg is sound, the composite is not.
- **Depth:** shallow. From the characterizations R1-R4 (transitivity of inclusion; for the guarded reverse inclusion, satisfiability of T transfers to U through T ⊆ U).
- **Non-vacuity witness:** value/shared: the strict chain zero-only -> bool -> byte; mutable: the satisfiable chain bool' -> bool -> bool ⊔ zero-only (for a satisfiable source every sound mutable chain has extensionally equal validities) and the chain never -> bool -> bool' whose end points differ; interior mutability: the same two chains for every pair of flags, and the strict chain zero-only -> bool -> byte without destination writes. Lean: `valueSound_trans_nonvacuous`, `sharedSound_trans_nonvacuous`, `mutSound_trans_nonvacuous`, `mutSound_trans_uninhabited_nonvacuous`, `sharedIMSound_trans_nonvacuous`, `sharedIMSound_trans_uninhabited_nonvacuous`, `sharedIMSound_noDst_trans_strict_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [MCP411] rustc MCP 411, Lang Item for Transmutability; [WRENN] Wrenn 2024, Safety Goggles for Alchemists.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R5-trans.
- Basis: execution (Lean kernel check): `valueSound_trans`, `sharedSound_trans`, `mutSound_trans`, `sharedIMSound_trans` and the witnesses named above.
- Basis: derived (modeling bridge): For Rust casts this composes only the bit-validity component of soundness; alignment, size relations and aliasing conditions are separate and are not addressed. Composability of transmutability is assumed informally in the safe-transmute design documents ([MCP411], [WRENN]).

#### R5-hier: `valueSound_of_sharedSound`, `sharedSound_of_valueSound`, `sharedSound_of_mutSound`

- **Kind:** theorem.
- **Tier:** T1. Folklore ordering of cast kinds by strength, made precise; the value/shared coincidence is a property of this model.
- **Plain claim:** For two types T and U of the same size, a sound unchecked mutable-reference cast from T to U implies a sound shared-reference cast, and in this model shared-reference soundness and value-transmute soundness coincide.

Lean (`valueSound_of_sharedSound`):
```lean
valueSound_of_sharedSound : ∀ {B : Type} {n : Nat} {T U : Validity B n}, SharedSound T U → ValueSound T U
```
Unfolded:
```lean
Sound sharedProtocol T U → Sound valueProtocol T U
```

Lean (`sharedSound_of_valueSound`):
```lean
sharedSound_of_valueSound : ∀ {B : Type} {n : Nat} {T U : Validity B n}, ValueSound T U → SharedSound T U
```
Unfolded:
```lean
Sound valueProtocol T U → Sound sharedProtocol T U
```

Lean (`sharedSound_of_mutSound`):
```lean
sharedSound_of_mutSound : ∀ {B : Type} {n : Nat} {T U : Validity B n}, MutSound T U → SharedSound T U
```
Unfolded:
```lean
Sound mutProtocol T U → Sound sharedProtocol T U
```

- **Hypothesis ledger:**
  - `h (the stronger soundness)`: Each implication needs its premise. Tightness: **tight**; counterexample `not_valueSound_byteV_boolV`, `not_sharedSound_byteV_boolV`. Without the premise the conclusion fails for byte -> bool.
- **Depth:** definitional. Transports across R1, R2 and the first conjunct of R3.
- **Non-vacuity witness:** bool -> byte (shared and value); bool -> bool' (mutable). Lean: `sharedSound_boolV_byteV`, `valueSound_boolV_byteV`, `mutSound_boolV_boolV'`.
- **Related witnesses:** `sharedSound_not_imp_mutSound`. Strictness: bool -> byte is shared-sound but not mutable-sound, so the converse of sharedSound_of_mutSound fails.
- **Prior art** (full records under Evidence, Primary sources): [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [RUSTC] rustc_transmute source and UI test at a pinned commit.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R5-hier.
- Basis: execution (Lean kernel check): `valueSound_of_sharedSound`, `sharedSound_of_valueSound`, `sharedSound_of_mutSound` and the witnesses named above.
- Basis: derived (modeling bridge): Only the implication from mutable to shared soundness is expected to transfer to Rust's bit-validity conditions; the coincidence of value and shared soundness is an artefact of omitting alignment, unsized size relations and aliasing from the model.

#### R5-symm: `mutSound_symm_of_satisfiable`

- **Kind:** theorem.
- **Tier:** T0. Symmetry of validity equality transported across R3-eq: a re-derivation of a known fact in this vocabulary.
- **Plain claim:** If the source type T has a valid byte sequence and the unchecked mutable-reference cast from T to a type U of the same size is sound, then the reverse mutable-reference cast from U to T is sound.

Lean (`mutSound_symm_of_satisfiable`):
```lean
mutSound_symm_of_satisfiable : ∀ {B : Type} {n : Nat} {T U : Validity B n}, Satisfiable T → MutSound T U → MutSound U T
```
Unfolded:
```lean
(∃ m, T m) → Sound mutProtocol T U → Sound mutProtocol U T
```

- **Hypothesis ledger:**
  - `hT : Satisfiable T`: Excludes the uninhabited source. Tightness: **tight**; counterexample `mutSound_symm_needs_satisfiable`. never -> byte is sound, byte -> never is not.
  - `h : MutSound T U`: The forward cast must be sound. Tightness: **tight**; counterexample `mutSound_symm_needs_mutSound`. (T, U) = (bool, byte): bool is satisfiable, the conclusion byte -> bool fails.
- **Depth:** definitional. From R3-eq and R3.
- **Non-vacuity witness:** bool -> bool'. Lean: `mutSound_symm_nonvacuous`.
- **Related witnesses:** `mutSound_not_iff_symm_of_satisfiable_left`. The implication is one-way under Satisfiable T: byte -> never is unsound while never -> byte is sound.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [RUSTC] rustc_transmute source and UI test at a pinned commit.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R5-symm.
- Basis: execution (Lean kernel check): `mutSound_symm_of_satisfiable` and the witnesses named above.
- Basis: derived (modeling bridge): For Rust `&mut` casts between inhabited, same-size referents, the bit-validity condition is symmetric; real mutable-reference casts additionally require the destination to be no more strictly aligned than the source, which is not symmetric.

#### R6-bool-byte: `boolV_to_byteV_value_and_shared_sound`, `boolV_to_byteV_mut_violating_run`, `mutSound_needs_includes_rev`

- **Kind:** counterexample.
- **Tier:** T1. The bool/byte example is the standard illustration (bool validity is normative in the Rust Reference); here it is fully mechanized.
- **Plain claim:** For a bool-like type (valid bytes 0 and 1) and a raw byte (all bytes valid): the value transmute and the shared cast bool -> byte are sound, but the mutable cast is unsound, witnessed by writing 2 through the byte view and then reading the bool.

Lean (`boolV_to_byteV_value_and_shared_sound`):
```lean
boolV_to_byteV_value_and_shared_sound : Includes boolV byteV ∧ ValueSound boolV byteV ∧ SharedSound boolV byteV
```

Lean (`boolV_to_byteV_mut_violating_run`):
```lean
boolV_to_byteV_mut_violating_run : mutProtocol (writeDstReadSrc (byteSeq 2)) ∧
  (∀ (op : Op (Fin 256) 1), op ∈ writeDstReadSrc (byteSeq 2) → Op.WellTyped boolV byteV op) ∧
    boolV (byteSeq 0) ∧ ¬NoInvalidRead boolV byteV (byteSeq 0) (writeDstReadSrc (byteSeq 2))
```

Lean (`mutSound_needs_includes_rev`):
```lean
mutSound_needs_includes_rev : Includes boolV byteV ∧ Satisfiable boolV ∧ ¬Includes byteV boolV ∧ ¬MutSound boolV byteV
```

- **Hypothesis ledger:**
  - none (a concrete counterexample statement).
- **Depth:** definitional. Concrete computation plus the invariant tool.
- **Non-vacuity witness:** (a counterexample; the instance itself is the witness)
- **Prior art** (full records under Evidence, Primary sources): [REF_UB] Rust Reference, Behavior considered undefined; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*).
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R6-bool-byte.
- Basis: execution (Lean kernel check): `boolV_to_byteV_value_and_shared_sound`, `boolV_to_byteV_mut_violating_run`, `mutSound_needs_includes_rev` and the witnesses named above.
- Basis: derived (modeling bridge): With `boolV` read as Rust's `bool` (valid bytes 0 and 1, [REF_UB] rule [undefined.validity.bool]) and `byteV` as `u8`: transmuting `bool → u8` by value and `&bool → &u8` are fine for bit validity, while `&mut bool → &mut u8` is not (write 2 through the `u8` view, then read the `bool`). zerocopy's `transmute_mut!` rejects this pair because `bool` is not `FromBytes` ([ZEROCOPY]).

#### R6-byte-bool: `byteV_to_boolV_unsound_even_by_value`

- **Kind:** counterexample.
- **Tier:** T1. Standard example.
- **Plain claim:** The reverse direction byte -> bool is unsound for unchecked value transmutes, unchecked shared-reference casts and unchecked mutable-reference casts, already because transmuting the byte 2 produces an invalid bool (this card does not cover the shared cast with interior mutability, for which see R4, nor checked casts, which are sound for byte -> bool by R8-value-shared and R8-mut).

Lean (`byteV_to_boolV_unsound_even_by_value`):
```lean
byteV_to_boolV_unsound_even_by_value : (Satisfiable byteV → Includes boolV byteV) ∧
  ¬Includes byteV boolV ∧ ¬ValueSound byteV boolV ∧ ¬SharedSound byteV boolV ∧ ¬MutSound byteV boolV
```

- **Hypothesis ledger:**
  - none (a concrete counterexample statement).
- **Depth:** definitional.
- **Non-vacuity witness:** (a counterexample)
- **Prior art** (full records under Evidence, Primary sources): [REF_UB] Rust Reference, Behavior considered undefined; [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*).
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R6-byte-bool.
- Basis: execution (Lean kernel check): `byteV_to_boolV_unsound_even_by_value` and the witnesses named above.
- Basis: derived (modeling bridge): With the same reading, `u8 → bool` is unsound for every unchecked cast kind (value, shared and mutable by this card, shared with interior mutability by R4); zerocopy's `try_transmute_mut!` documentation shows the checked conversion accepting `&mut 0u8` and rejecting `&mut 2u8` ([ZEROCOPY]).

#### R6-im: `boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes`

- **Kind:** counterexample.
- **Tier:** T1. Standard argument, mechanized.
- **Plain claim:** The shared cast bool -> byte is sound without writes but becomes unsound once the destination side may write (with or without source-side writes).

Lean (`boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes`):
```lean
boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes : SharedSound boolV byteV ∧
  SharedIMSound false false boolV byteV ∧ ¬SharedIMSound false true boolV byteV ∧ ¬SharedIMSound true true boolV byteV
```

- **Hypothesis ledger:**
  - none (a concrete counterexample statement).
- **Depth:** definitional.
- **Non-vacuity witness:** (a counterexample)
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged).
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R6-im.
- Basis: execution (Lean kernel check): `boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes` and the witnesses named above.
- Basis: derived (modeling bridge): With the same reading, a shared cast from `bool` to a `u8`-like type is fine while nobody writes and breaks once the destination side may write, as for interior-mutable destinations in the RFC text ([RFC2981]).

#### R6-src-writes: `sharedIMSound_eq_needs_dstWrites`

- **Kind:** counterexample.
- **Tier:** T1. Elementary; recorded because it corrects a tempting over-statement.
- **Plain claim:** Source-side writes alone do not force validity equality: the shared cast bool -> byte where only the source side may write is sound for bit validity in this model (aliasing rules are not modelled) although the validities differ.

Lean (`sharedIMSound_eq_needs_dstWrites`):
```lean
sharedIMSound_eq_needs_dstWrites : Satisfiable boolV ∧
  SharedIMSound true false boolV byteV ∧
    ¬ValidityEq boolV byteV ∧ ¬(SharedIMSound true false boolV byteV ↔ ValidityEq boolV byteV)
```

- **Hypothesis ledger:**
  - none (a concrete counterexample statement).
- **Depth:** definitional.
- **Non-vacuity witness:** (a counterexample)
- **Prior art** (full records under Evidence, Primary sources): [RUSTC] rustc_transmute source and UI test at a pinned commit; [STACKED_BORROWS] Jung et al., Stacked Borrows, POPL 2020; [TREE_BORROWS] Villani et al., Tree Borrows, PLDI 2025.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R6-src-writes.
- Basis: execution (Lean kernel check): `sharedIMSound_eq_needs_dstWrites` and the witnesses named above.
- Basis: derived (modeling bridge): With the same reading, an interior-mutable `bool`-like source viewed through a read-only `u8` destination is sound for bit validity in the model; in Rust such a cast is decided by the aliasing model ([STACKED_BORROWS], [TREE_BORROWS]), and rustc's checker places no interior-mutability condition on the source referent ([RUSTC], `mod.rs` lines 276-282).

#### R6-never: `mutSound_eq_needs_satisfiable`, `sharedIMSound_eq_needs_satisfiable`

- **Kind:** counterexample.
- **Tier:** T1. Edge case made explicit.
- **Plain claim:** For the uninhabited type never and the raw byte type, the unchecked mutable cast never -> byte and the unchecked shared cast with interior mutability never -> byte in which both sides may write are (vacuously) sound although the two validities differ, so 'mutable (or destination-writable) casts are sound iff the validities are equal' fails without assuming the source is inhabited (in general every cast from an uninhabited type is vacuously sound in this model: the proof tool sound_of_not_satisfiable).

Lean (`mutSound_eq_needs_satisfiable`):
```lean
mutSound_eq_needs_satisfiable : ¬Satisfiable neverV ∧
  MutSound neverV byteV ∧ ¬ValidityEq neverV byteV ∧ ¬(MutSound neverV byteV ↔ ValidityEq neverV byteV)
```

Lean (`sharedIMSound_eq_needs_satisfiable`):
```lean
sharedIMSound_eq_needs_satisfiable : ¬Satisfiable neverV ∧
  SharedIMSound true true neverV byteV ∧ ¬(SharedIMSound true true neverV byteV ↔ ValidityEq neverV byteV)
```

- **Hypothesis ledger:**
  - none (a concrete counterexample statement).
- **Depth:** definitional.
- **Non-vacuity witness:** (a counterexample)
- **Prior art** (full records under Evidence, Primary sources): [UCG] Unsafe Code Guidelines glossary, validity vs safety invariant; [MINIRUST] MiniRust representation relation; [RUSTC] rustc_transmute source and UI test at a pinned commit; [REF_UB] Rust Reference, Behavior considered undefined.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R6-never.
- Basis: execution (Lean kernel check): `mutSound_eq_needs_satisfiable`, `sharedIMSound_eq_needs_satisfiable` and the witnesses named above.
- Basis: derived (modeling bridge): rustc's checker answers Yes for an uninhabited source type ([RUSTC], `mod.rs` lines 112-119), which matches the vacuous case of the model; the Rust Reference's rule [undefined.validity.reference-box] (a reference must point to a valid value, a point it notes is still debated) means a reference to an uninhabited type is never valid, so the case is not a usable cast in Rust ([REF_UB]).

#### R7-shared-lattice: `sharedSound_to_join_left`, `sharedSound_to_join_right`, `sharedSound_from_meet_left`, `sharedSound_from_meet_right`, `sharedSound_join_iff`, `sharedSound_meet_iff`

- **Kind:** theorem.
- **Tier:** T0. Standard facts about the inclusion lattice of predicates, transported to shared-cast soundness via R2.
- **Plain claim:** For types T, U, V of the same size, ordered by inclusion of their validities, shared casts from T or from U into the join T ⊔ U, and from the meet T ⊓ U into T or into U, are always sound; a shared cast out of T ⊔ U into V is sound iff both T -> V and U -> V are; a shared cast from V into T ⊓ U is sound iff both V -> T and V -> U are.

Lean (`sharedSound_to_join_left`):
```lean
sharedSound_to_join_left : ∀ {B : Type} {n : Nat} (T U : Validity B n), SharedSound T (Validity.join T U)
```
Unfolded:
```lean
Sound sharedProtocol T (fun m => T m ∨ U m)
```

Lean (`sharedSound_to_join_right`):
```lean
sharedSound_to_join_right : ∀ {B : Type} {n : Nat} (T U : Validity B n), SharedSound U (Validity.join T U)
```
Unfolded:
```lean
Sound sharedProtocol U (fun m => T m ∨ U m)
```

Lean (`sharedSound_from_meet_left`):
```lean
sharedSound_from_meet_left : ∀ {B : Type} {n : Nat} (T U : Validity B n), SharedSound (Validity.meet T U) T
```
Unfolded:
```lean
Sound sharedProtocol (fun m => T m ∧ U m) T
```

Lean (`sharedSound_from_meet_right`):
```lean
sharedSound_from_meet_right : ∀ {B : Type} {n : Nat} (T U : Validity B n), SharedSound (Validity.meet T U) U
```
Unfolded:
```lean
Sound sharedProtocol (fun m => T m ∧ U m) U
```

Lean (`sharedSound_join_iff`):
```lean
sharedSound_join_iff : ∀ {B : Type} {n : Nat} (T U V : Validity B n),
  SharedSound (Validity.join T U) V ↔ SharedSound T V ∧ SharedSound U V
```
Unfolded:
```lean
Sound sharedProtocol (fun m => T m ∨ U m) V ↔ Sound sharedProtocol T V ∧ Sound sharedProtocol U V
```

Lean (`sharedSound_meet_iff`):
```lean
sharedSound_meet_iff : ∀ {B : Type} {n : Nat} (T U V : Validity B n),
  SharedSound V (Validity.meet T U) ↔ SharedSound V T ∧ SharedSound V U
```
Unfolded:
```lean
Sound sharedProtocol V (fun m => T m ∧ U m) ↔ Sound sharedProtocol V T ∧ Sound sharedProtocol V U
```

- **Hypothesis ledger:**
  - `(none: unconditional statements and equivalences without hypotheses)`: All six statements are universally quantified over byte alphabets, sizes and validity predicates. Tightness: **harmless**.
  - `sharedSound_join_iff, right-hand conjunct SharedSound T V`: The join contains T. Tightness: **tight**; counterexample `sharedSound_join_iff_needs_left`. (T, U, V) = (two-only, bool, bool): the other conjunct holds, T -> V fails, the join cast fails.
  - `sharedSound_join_iff, right-hand conjunct SharedSound U V`: The join contains U. Tightness: **tight**; counterexample `sharedSound_join_iff_needs_right`. (T, U, V) = (bool, two-only, bool).
  - `sharedSound_meet_iff, right-hand conjunct SharedSound V T`: The meet is contained in T. Tightness: **tight**; counterexample `sharedSound_meet_iff_needs_left`. (T, U, V) = (zero-only, byte, bool).
  - `sharedSound_meet_iff, right-hand conjunct SharedSound V U`: The meet is contained in U. Tightness: **tight**; counterexample `sharedSound_meet_iff_needs_right`. (T, U, V) = (byte, zero-only, bool).
- **Depth:** definitional. From R2 and elementary predicate logic.
- **Non-vacuity witness:** bool -> bool ⊔ two-only and two-only -> bool ⊔ two-only (strictly larger targets); bool ⊓ zero-only -> bool and zero-only ⊓ bool -> bool (strictly smaller sources); the join characterization with both sides true and both false; the meet characterization with both sides true for three pairwise different types and both sides false. Lean: `sharedSound_to_join_left_nonvacuous`, `sharedSound_to_join_right_nonvacuous`, `sharedSound_from_meet_left_nonvacuous`, `sharedSound_from_meet_right_nonvacuous`, `sharedSound_join_iff_nonvacuous`, `sharedSound_meet_iff_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [UCG] Unsafe Code Guidelines glossary, validity vs safety invariant; [FRISCH] Frisch, Castagna, Benzaken, Semantic Subtyping, JACM 2008.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R7-shared-lattice.
- Basis: execution (Lean kernel check): `sharedSound_to_join_left`, `sharedSound_to_join_right`, `sharedSound_from_meet_left`, `sharedSound_from_meet_right`, `sharedSound_join_iff`, `sharedSound_meet_iff` and the witnesses named above.
- Basis: derived (modeling bridge): No direct real-system claim. The join is the validity of a hypothetical 'either T or U' type of the same size, not of a Rust `union` (whose validity requirements may be weaker) or of a tagged enum; the lattice reading is the standard set-theoretic one ([FRISCH]).

#### R7-mut-join: `mutSound_to_join_left_iff_includes_rev_of_satisfiable`

- **Kind:** characterization.
- **Tier:** T0. Beyond R3-eq the only content is the lattice identity (T ⊔ U ≡ T) ↔ U ⊆ T: a re-derivation in this vocabulary of the familiar problem with covariant mutable containers.
- **Plain claim:** For a source type T with a valid byte sequence and a type U of the same size, the unchecked mutable cast from T into the join T ⊔ U is sound if and only if the join adds nothing, that is every U-valid byte sequence is already T-valid (the reverse inclusion U ⊆ T).

Lean (`mutSound_to_join_left_iff_includes_rev_of_satisfiable`):
```lean
mutSound_to_join_left_iff_includes_rev_of_satisfiable : ∀ {B : Type} {n : Nat} {T U : Validity B n},
  Satisfiable T → (MutSound T (Validity.join T U) ↔ Includes U T)
```
Unfolded:
```lean
(∃ m, T m) → (Sound mutProtocol T (fun m => T m ∨ U m) ↔ ∀ m, U m → T m)
```

- **Hypothesis ledger:**
  - `hT : Satisfiable T`: Excludes the vacuous uninhabited source. Tightness: **tight**; counterexample `mutSound_to_join_needs_satisfiable`. never -> never ⊔ byte is sound but byte ⊄ never.
  - `right-hand side: Includes U T`: A value valid only at U, written through the join view, is read back at T. Tightness: **tight**; counterexample `mutSound_to_join_needs_includes_rev`. bool -> bool ⊔ two-only: bool is satisfiable, two-only ⊈ bool, the mutable cast is unsound.
- **Depth:** definitional. From R3-eq and the lattice identity.
- **Non-vacuity witness:** bool -> bool ⊔ zero-only: bool is satisfiable, the join adds nothing, the cast is sound; the forward inclusion bool ⊆ zero-only fails there, so the right-hand side is the reverse inclusion. Lean: `mutSound_to_join_nonvacuous`.
- **Related witnesses:** `mutSound_to_join_fails_example`. bool -> bool ⊔ two-only is shared-sound but not mutable-sound.
- **Prior art** (full records under Evidence, Primary sources): [JLS] JLS SE 21, array covariance and ArrayStoreException; [REF_VAR] Rust Reference, Subtyping and variance; [REYNOLDS] Reynolds, Design of the Programming Language Forsythe, 1997.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R7-mut-join.
- Basis: execution (Lean kernel check): `mutSound_to_join_left_iff_includes_rev_of_satisfiable` and the witnesses named above.
- Basis: derived (modeling bridge): The model reproduces the familiar problem with covariant mutable containers: Java arrays are covariant and discharge the write-side obligation by a run-time check on stores ([JLS] sections 4.10.3 and 10.5), while Rust makes `&'a mut T` invariant in `T` ([REF_VAR], rule [subtyping.variance.builtin-types]); variance in Rust concerns lifetimes, so this is an analogy, not a claim about Rust's subtyping.

#### R7-mut-meet: `mutSound_from_meet_left_iff_includes_of_satisfiable_meet`

- **Kind:** characterization.
- **Tier:** T0. Beyond R3-eq the only content is the lattice identity (T ⊓ U ≡ T) ↔ T ⊆ U: a re-derivation in this vocabulary.
- **Plain claim:** For types T and U of the same size such that some byte sequence is valid at both (satisfiability of T and of U separately is not enough), the unchecked mutable cast from the meet T ⊓ U into T is sound if and only if the meet removes nothing from T, that is every T-valid byte sequence is U-valid.

Lean (`mutSound_from_meet_left_iff_includes_of_satisfiable_meet`):
```lean
mutSound_from_meet_left_iff_includes_of_satisfiable_meet : ∀ {B : Type} {n : Nat} {T U : Validity B n},
  Satisfiable (Validity.meet T U) → (MutSound (Validity.meet T U) T ↔ Includes T U)
```
Unfolded:
```lean
(∃ m, T m ∧ U m) → (Sound mutProtocol (fun m => T m ∧ U m) T ↔ ∀ m, T m → U m)
```

- **Hypothesis ledger:**
  - `h : Satisfiable (T ⊓ U)`: Excludes the vacuous case of an empty meet; it cannot be weakened to satisfiability of T, nor of T and U separately. Tightness: **tight**; counterexample `mutSound_from_meet_needs_joint_satisfiable`, `mutSound_from_meet_needs_satisfiable`. zero-only and two-only are both satisfiable but disjoint: the cast out of the empty meet is sound while zero-only ⊈ two-only; also byte ⊓ never -> byte.
  - `right-hand side: Includes T U`: A T-valid value written through the T view is read back at the meet. Tightness: **tight**; counterexample `mutSound_from_meet_fails_example`. bool ⊓ zero-only -> bool: the meet is satisfiable, bool ⊈ zero-only, the cast is unsound.
- **Depth:** definitional. From R3-eq and the lattice identity.
- **Non-vacuity witness:** zero-only ⊓ bool -> zero-only: the meet is satisfiable, bool is strictly larger than zero-only, the meet removes nothing, the cast is sound. Lean: `mutSound_from_meet_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged).
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R7-mut-meet.
- Basis: execution (Lean kernel check): `mutSound_from_meet_left_iff_includes_of_satisfiable_meet` and the witnesses named above.
- Basis: derived (modeling bridge): No direct real-system claim beyond R3: narrowing a mutable reference from a type with fewer valid values to one with more is unsound unless nothing is removed.

#### R8-value-shared: `checkedSound_valueProtocol`, `checkedSound_sharedProtocol`

- **Kind:** theorem.
- **Tier:** T1. Checked conversions are an established design (zerocopy's try_transmute! and try_transmute_ref!); that a successful check makes value and read-only casts safe for bit validity is folklore, made precise here.
- **Plain claim:** A value transmute, or a shared-reference cast without interior mutability, between two types T and U of the same size that is checked once at cast time (it goes ahead only if the bytes are valid at U) is sound for bit validity in this model, for every T and U.

Lean (`checkedSound_valueProtocol`):
```lean
checkedSound_valueProtocol : ∀ {B : Type} {n : Nat} (T U : Validity B n), CheckedSound valueProtocol T U
```
Unfolded:
```lean
∀ m, T m → U m → ∀ tr, (∀ op ∈ tr, op.side = .dst) → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr
```

Lean (`checkedSound_sharedProtocol`):
```lean
checkedSound_sharedProtocol : ∀ {B : Type} {n : Nat} (T U : Validity B n), CheckedSound sharedProtocol T U
```
Unfolded:
```lean
∀ m, T m → U m → ∀ tr, (∀ op ∈ tr, op.IsRead) → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr
```

- **Hypothesis ledger:**
  - `(none: unconditional statements)`: Universally quantified over byte alphabets, sizes and validity predicates. Tightness: **harmless**.
- **Depth:** shallow. Invariant U (value) or T ⊓ U (shared) with the checked invariant tool.
- **Non-vacuity witness:** For byte -> bool some contents pass the check, the checked casts are sound, and the unchecked ones are not. Lean: `checkedSound_valueProtocol_nonvacuous`, `checkedSound_sharedProtocol_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [MCP411] rustc MCP 411, Lang Item for Transmutability.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R8-value-shared.
- Basis: execution (Lean kernel check): `checkedSound_valueProtocol`, `checkedSound_sharedProtocol` and the witnesses named above.
- Basis: derived (modeling bridge): zerocopy 0.8.63's `try_transmute!` (`Src: IntoBytes, Dst: TryFromBytes`, equal sizes) and `try_transmute_ref!` (`Src: IntoBytes + Immutable`, `Dst: TryFromBytes + Immutable`, alignment and size bounds) are real checked casts of this kind ([ZEROCOPY]). The model needs no condition on `T` only because its bytes are always initialised: reading the source bytes to run the check requires them to be initialised, which is what `Src: IntoBytes` provides; and on success `try_transmute!` forgets the source without running its destructor.

#### R8-mut: `checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev`

- **Kind:** characterization.
- **Tier:** T1. Checked mutable reinterpretation exists in practice (zerocopy's try_transmute_mut!); the exact condition, including the empty-meet edge case, is folklore made precise.
- **Plain claim:** A mutable-reference cast between two types T and U of the same size (both views covering the same region) that is checked once at cast time (it goes ahead only if the bytes are valid at U) and then used without further checks, after which the owner resumes at T, is sound if and only if, provided some byte sequence is valid at both T and U, every U-valid byte sequence is T-valid; the read-side condition T ⊆ U of the unchecked cast (R3) is not needed.

Lean (`checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev`):
```lean
checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev : ∀ {B : Type} {n : Nat} (T U : Validity B n),
  CheckedSound mutProtocol T U ↔ Satisfiable (Validity.meet T U) → Includes U T
```
Unfolded:
```lean
(∀ m, T m → U m → ∀ tr, (∃ during after, tr = during ++ after ∧ (∀ op ∈ during, op.side = .dst) ∧ (∀ op ∈ after, op.side = .src)) →
     (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr)
  ↔ ((∃ m, T m ∧ U m) → ∀ m, U m → T m)
```

- **Hypothesis ledger:**
  - `(none: an equivalence with no hypotheses)`: The statement is universally quantified over all byte alphabets, sizes and validity predicates (source and destination share the size index n). Tightness: **harmless**.
  - `right-hand side: Includes U T`: A U-valid value written through the cast reference is later read at T by the owner; the check does not cover later writes. Tightness: **tight**; counterexample `checkedSound_mut_needs_includes_rev`. bool -> byte: the meet is satisfiable, byte ⊈ bool, the checked cast is unsound.
  - `right-hand side: the guard 'Satisfiable (T ⊓ U) ->'`: If no byte sequence is valid at both types the check never succeeds and the cast is vacuously sound; the guard cannot be weakened to satisfiability of T or of U. Tightness: **tight**; counterexample `checkedSound_mut_rhs_needs_satisfiable_meet_guard`. zero-only -> two-only: both satisfiable, the meet is empty, the checked cast is sound, two-only ⊈ zero-only.
- **Depth:** shallow. Necessity: the run writeDstReadSrc u from contents that pass the check. Sufficiency: a two-phase invariant (U while the cast reference is used, T afterwards).
- **Non-vacuity witness:** Both sides true for byte -> bool; both false for bool -> byte. Lean: `checkedSound_mut_nonvacuous`.
- **Related witnesses:** `checkedSound_mut_escapes_impossibility`, `checkedSound_mut_byteV_boolV`. byte -> bool: the unchecked mutable cast is unsound (R3-imp), the checked one is sound.
- **Prior art** (full records under Evidence, Primary sources): [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [JLS] JLS SE 21, array covariance and ArrayStoreException; [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged).
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R8-mut.
- Basis: execution (Lean kernel check): `checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev` and the witnesses named above.
- Basis: derived (modeling bridge): zerocopy 0.8.63's `try_transmute_mut!` (`Src: FromBytes + IntoBytes`, `Dst: TryFromBytes + IntoBytes`, alignment and size checked at compile time, 'the value of the referent is checked for validity at runtime') is the real-world instance of the checked mutable case ([ZEROCOPY]). Reasoning: over possibly uninitialised bytes, `Dst: IntoBytes` says every `U`-valid sequence is initialised and `Src: FromBytes` says every initialised sequence is `T`-valid, so `U ⊆ T`, the right-hand side of R8-mut; the run-time check supplies validity at `U` of the initial contents; `T ⊆ U` is not required, matching the macro's acceptance of `&mut 0u8 → &mut bool`. The remaining bound `Src: IntoBytes` is outside the model (bytes here are always initialised): the run-time check reads the source referent's bytes, which must therefore be initialised, and `Src: FromBytes` alone does not exclude padding bytes.

#### R8-im: `checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev`

- **Kind:** characterization.
- **Tier:** T1. Elementary consequence of the read/write argument for casts checked once; recorded because it shows that a check at cast time does not make source-side interior mutability harmless. Not found stated in the sources consulted, but too elementary to claim as novel.
- **Plain claim:** A shared-reference cast with interior mutability between two types T and U of the same size (both views covering the same region), checked once at cast time, in which both references stay live, the source side may write T-valid values iff srcWrites and the destination side may write U-valid values iff dstWrites, is sound for bit validity in this model (aliasing rules are not modelled) if and only if, provided some byte sequence is valid at both T and U, source-side writes require every T-valid byte sequence to be U-valid and destination-side writes require every U-valid byte sequence to be T-valid; unlike the unchecked case (R4), source-side writes matter because they happen after the check.

Lean (`checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev`):
```lean
checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev : ∀ {B : Type} {n : Nat}
  (srcWrites dstWrites : Bool) (T U : Validity B n),
  CheckedSound (sharedIMProtocol srcWrites dstWrites) T U ↔
    Satisfiable (Validity.meet T U) → (srcWrites = true → Includes T U) ∧ (dstWrites = true → Includes U T)
```
Unfolded:
```lean
(∀ m, T m → U m → ∀ tr, (∀ op ∈ tr, op.PermittedIM srcWrites dstWrites) → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr)
  ↔ ((∃ m, T m ∧ U m) → (srcWrites = true → ∀ m, T m → U m) ∧ (dstWrites = true → ∀ m, U m → T m))
-- op.PermittedIM s d: reads always; a source write iff s = true; a destination write iff d = true
```

- **Hypothesis ledger:**
  - `(none: an equivalence with no hypotheses)`: The statement is universally quantified over all byte alphabets, sizes and validity predicates (source and destination share the size index n). Tightness: **harmless**.
  - `right-hand side: srcWrites = true -> Includes T U`: A T-valid value written through the source after the check is read at U through the cast reference. Tightness: **tight**; counterexample `checkedSound_sharedIM_needs_srcWrites_includes`. byte -> bool with both flags: the meet is satisfiable, the other conjunct (bool ⊆ byte) holds, byte ⊈ bool, the checked cast is unsound.
  - `right-hand side: dstWrites = true -> Includes U T`: A U-valid value written through the cast reference is read at T through the original reference. Tightness: **tight**; counterexample `checkedSound_sharedIM_needs_dstWrites_includes_rev`. bool -> byte with both flags: the meet is satisfiable, the other conjunct holds, byte ⊈ bool, the checked cast is unsound.
  - `right-hand side: the guard 'srcWrites = true ->'`: Exactness: without source-side writes after the check, T ⊆ U is not needed: the check establishes validity at U for the initial contents, and every later value is written at U. Tightness: **tight**; counterexample `checkedSound_sharedIM_rhs_needs_srcWrites_guard`. byte -> bool with only destination-side writes: the meet is satisfiable, bool ⊆ byte, the checked cast is sound, but the right-hand side without this guard demands byte ⊆ bool, which fails.
  - `right-hand side: the guard 'dstWrites = true ->'`: Exactness: without destination-side writes, U ⊆ T is not needed: the contents are then the checked initial value (valid at T and at U) or T-valid values written through the source. Tightness: **tight**; counterexample `checkedSound_sharedIM_rhs_needs_dstWrites_guard`. bool -> byte with only source-side writes: the meet is satisfiable, bool ⊆ byte, the checked cast is sound, but the right-hand side without this guard demands byte ⊆ bool, which fails.
  - `right-hand side: the guard 'Satisfiable (T ⊓ U) ->'`: If the check never succeeds the cast is vacuously sound. Tightness: **tight**; counterexample `checkedSound_sharedIM_rhs_needs_satisfiable_meet_guard`. zero-only -> two-only with both flags: both satisfiable, the meet is empty, the checked cast is sound, the unguarded right-hand side is false.
- **Depth:** shallow. Necessity: the runs writeSrcReadDst v and writeDstReadSrc u from contents that pass the check. Sufficiency: the single invariant T ⊓ U for every pair of flags, with the checked invariant tool: the check establishes it, a permitted source write stays in it because T ⊆ U, and a permitted destination write because U ⊆ T.
- **Non-vacuity witness:** Both sides true: both flags with bool -> bool'; destination-only writes with byte -> bool; source-only writes with bool -> byte. Both sides false: source-only writes with byte -> bool. Lean: `checkedSound_sharedIM_nonvacuous`.
- **Prior art** (full records under Evidence, Primary sources): [ZEROCOPY] zerocopy 0.8.63 docs (transmute!, transmute_ref!, transmute_mut!, try_transmute*); [RUSTC] rustc_transmute source and UI test at a pinned commit; [RFC2981] Safer Transmute RFC text (rust-lang/rfcs#2981, unmerged); [STACKED_BORROWS] Jung et al., Stacked Borrows, POPL 2020; [TREE_BORROWS] Villani et al., Tree Borrows, PLDI 2025.
- **Design question:** A library offering safe reinterpretation of memory (value transmutes, shared-reference casts, mutable-reference casts) must decide which validity relationship between source and destination type each cast kind requires; too permissive is unsound, too restrictive rejects useful casts. Which conditions are exactly necessary and sufficient, and how does interior mutability change them?
- **Non-claims:** the global non-claim and the card-specific non-claims under Boundaries, R8-im.
- Basis: execution (Lean kernel check): `checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev` and the witnesses named above.
- Basis: derived (modeling bridge): No real system examined implements checked interior-mutable shared casts: zerocopy's `try_transmute_ref!` requires `Immutable` on both sides and so never relies on this case ([ZEROCOPY]). The card is a design reference: a check at cast time does not make source-side interior mutability harmless.

### Supporting statements

Every counterexample, non-vacuity witness, positive control and related witness named by a card, as Lean prints it (one, marked below, is quoted from the source instead), with the cards that use it. All are fully proved in `lean/ToyTransmute/Counterexamples.lean` or `lean/ToyTransmute/Examples.lean`; none depends on a main result.

#### `valueSound_iff_includes_nonvacuous`

Used by: R1: non-vacuity witness.
```lean
valueSound_iff_includes_nonvacuous : (ValueSound boolV byteV ∧ Includes boolV byteV) ∧
  ¬ValueSound byteV boolV ∧ ¬Includes byteV boolV
```

#### `noInvalidRead_unchecked_until_read`

Used by: R1: related witness. Quoted from the source, because Lean's printed form `valueProtocol []` omits the byte alphabet and size (`Protocol (Fin 256) 1`) of its first conjunct:
```lean
-- lean/ToyTransmute/Examples.lean:332-336
theorem noInvalidRead_unchecked_until_read :
    (valueProtocol : Protocol (Fin 256) 1) [] ∧ ¬ boolV (byteSeq 2) ∧
      NoInvalidRead byteV boolV (byteSeq 2) [] ∧
      NoInvalidRead byteV boolV (byteSeq 2) [.write .dst (byteSeq 0), .read .dst] ∧
      ¬ NoInvalidRead byteV boolV (byteSeq 2) readDst
```

#### `byteV_to_boolV_unsound_even_by_value`

Used by: R1: counterexample (right-hand side: Includes T U); R2: counterexample (right-hand side: Includes T U); R3: counterexample (right-hand side: Includes T U (read side)); R6-byte-bool: result.
```lean
byteV_to_boolV_unsound_even_by_value : (Satisfiable byteV → Includes boolV byteV) ∧
  ¬Includes byteV boolV ∧ ¬ValueSound byteV boolV ∧ ¬SharedSound byteV boolV ∧ ¬MutSound byteV boolV
```

#### `sharedSound_iff_includes_nonvacuous`

Used by: R2: non-vacuity witness.
```lean
sharedSound_iff_includes_nonvacuous : (SharedSound boolV byteV ∧ Includes boolV byteV) ∧
  ¬SharedSound byteV boolV ∧ ¬Includes byteV boolV
```

#### `mutSound_exact_nonvacuous`

Used by: R3: non-vacuity witness.
```lean
mutSound_exact_nonvacuous : (MutSound boolV boolV' ∧
    Includes boolV boolV' ∧ (Satisfiable boolV → Includes boolV' boolV)) ∧
  ¬MutSound boolV byteV ∧ ¬(Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV))
```

#### `mutSound_needs_includes_rev`

Used by: R3: counterexample (right-hand side: Satisfiable T -> Includes U T (write side)); R6-bool-byte: result.
```lean
mutSound_needs_includes_rev : Includes boolV byteV ∧ Satisfiable boolV ∧ ¬Includes byteV boolV ∧ ¬MutSound boolV byteV
```

#### `mutSound_rhs_needs_satisfiable_guard`

Used by: R3: counterexample (right-hand side: the guard 'Satisfiable T ->' on the write side).
```lean
mutSound_rhs_needs_satisfiable_guard : ¬Satisfiable neverV ∧
  MutSound neverV byteV ∧
    Includes neverV byteV ∧
      ¬Includes byteV neverV ∧ ¬(MutSound neverV byteV ↔ Includes neverV byteV ∧ Includes byteV neverV)
```

#### `mutSound_eq_needs_satisfiable`

Used by: R3: counterexample (right-hand side: the guard 'Satisfiable T ->' on the write side); R3-eq: counterexample (hT : Satisfiable T); R6-never: result.
```lean
mutSound_eq_needs_satisfiable : ¬Satisfiable neverV ∧
  MutSound neverV byteV ∧ ¬ValidityEq neverV byteV ∧ ¬(MutSound neverV byteV ↔ ValidityEq neverV byteV)
```

#### `mutSound_eq_nonvacuous`

Used by: R3-eq: non-vacuity witness.
```lean
mutSound_eq_nonvacuous : Satisfiable boolV ∧ MutSound boolV boolV' ∧ ValidityEq boolV boolV'
```

#### `not_mutSound_nonvacuous`

Used by: R3-imp: non-vacuity witness.
```lean
not_mutSound_nonvacuous : Satisfiable boolV ∧ ¬ValidityEq boolV byteV ∧ ¬MutSound boolV byteV
```

#### `not_mutSound_positive_control_weaker_casts`

Used by: R3-imp: positive control.
```lean
not_mutSound_positive_control_weaker_casts : Satisfiable boolV ∧
  ¬ValidityEq boolV byteV ∧ ValueSound boolV byteV ∧ SharedSound boolV byteV ∧ SharedIMSound true false boolV byteV
```

#### `not_mutSound_needs_satisfiable`

Used by: R3-imp: positive control; R3-imp: counterexample (hT : Satisfiable T).
```lean
not_mutSound_needs_satisfiable : ¬Satisfiable neverV ∧ ¬ValidityEq neverV byteV ∧ MutSound neverV byteV
```

#### `checkedSound_mut_escapes_impossibility`

Used by: R3-imp: positive control; R8-mut: related witness.
```lean
checkedSound_mut_escapes_impossibility : Satisfiable byteV ∧
  ¬ValidityEq byteV boolV ∧ ¬MutSound byteV boolV ∧ CheckedSound mutProtocol byteV boolV
```

#### `not_mutSound_needs_not_validityEq`

Used by: R3-imp: counterexample (hne : ¬ ValidityEq T U).
```lean
not_mutSound_needs_not_validityEq : Satisfiable boolV ∧ ValidityEq boolV boolV' ∧ MutSound boolV boolV'
```

#### `sharedIMSound_exact_nonvacuous`

Used by: R4: non-vacuity witness.
```lean
sharedIMSound_exact_nonvacuous : (SharedIMSound true true boolV boolV' ∧
    Includes boolV boolV' ∧ (true = true → Satisfiable boolV → Includes boolV' boolV)) ∧
  (SharedIMSound true false boolV byteV ∧ Includes boolV byteV) ∧
    ¬SharedIMSound true true boolV byteV ∧
      ¬(Includes boolV byteV ∧ (true = true → Satisfiable boolV → Includes byteV boolV))
```

#### `sharedIMSound_needs_includes_canonical`

Used by: R4: counterexample (right-hand side: Includes T U).
```lean
sharedIMSound_needs_includes_canonical : ∀ (srcWrites dstWrites : Bool),
  (dstWrites = true → Satisfiable byteV → Includes boolV byteV) ∧
    ¬Includes byteV boolV ∧
      ¬SharedIMSound srcWrites dstWrites byteV boolV ∧
        ¬(SharedIMSound srcWrites dstWrites byteV boolV ↔ dstWrites = true → Satisfiable byteV → Includes boolV byteV)
```

#### `sharedIMSound_needs_includes_rev_canonical`

Used by: R4: counterexample (right-hand side: dstWrites = true -> Satisfiable T -> Includes U T).
```lean
sharedIMSound_needs_includes_rev_canonical : ∀ (srcWrites : Bool),
  Includes boolV byteV ∧
    Satisfiable boolV ∧
      ¬Includes byteV boolV ∧
        ¬SharedIMSound srcWrites true boolV byteV ∧ ¬(SharedIMSound srcWrites true boolV byteV ↔ Includes boolV byteV)
```

#### `sharedIMSound_rhs_needs_dstWrites_guard`

Used by: R4: counterexample (right-hand side: the guard 'dstWrites = true ->').
```lean
sharedIMSound_rhs_needs_dstWrites_guard : ∀ (srcWrites : Bool),
  SharedIMSound srcWrites false boolV byteV ∧
    ¬(Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV)) ∧
      ¬(SharedIMSound srcWrites false boolV byteV ↔ Includes boolV byteV ∧ (Satisfiable boolV → Includes byteV boolV))
```

#### `sharedIMSound_rhs_needs_satisfiable_guard`

Used by: R4: counterexample (right-hand side: the guard 'Satisfiable T ->').
```lean
sharedIMSound_rhs_needs_satisfiable_guard : ∀ (srcWrites : Bool),
  ¬Satisfiable neverV ∧
    SharedIMSound srcWrites true neverV byteV ∧
      ¬(Includes neverV byteV ∧ (true = true → Includes byteV neverV)) ∧
        ¬(SharedIMSound srcWrites true neverV byteV ↔ Includes neverV byteV ∧ (true = true → Includes byteV neverV))
```

#### `sharedIMSound_eq_nonvacuous`

Used by: R4-eq: non-vacuity witness.
```lean
sharedIMSound_eq_nonvacuous : Satisfiable boolV ∧ SharedIMSound true true boolV boolV' ∧ ValidityEq boolV boolV'
```

#### `sharedIMSound_eq_needs_dstWrites`

Used by: R4-eq: counterexample (dstWrites = true (instantiated in the statement)); R6-src-writes: result.
```lean
sharedIMSound_eq_needs_dstWrites : Satisfiable boolV ∧
  SharedIMSound true false boolV byteV ∧
    ¬ValidityEq boolV byteV ∧ ¬(SharedIMSound true false boolV byteV ↔ ValidityEq boolV byteV)
```

#### `sharedIMSound_eq_needs_satisfiable`

Used by: R4-eq: counterexample (hT : Satisfiable T); R6-never: result.
```lean
sharedIMSound_eq_needs_satisfiable : ¬Satisfiable neverV ∧
  SharedIMSound true true neverV byteV ∧ ¬(SharedIMSound true true neverV byteV ↔ ValidityEq neverV byteV)
```

#### `sharedIMSound_noDst_nonvacuous`

Used by: R4-src: non-vacuity witness.
```lean
sharedIMSound_noDst_nonvacuous : SharedIMSound true false boolV byteV ∧ Includes boolV byteV
```

#### `sharedIMSound_noDst_needs_noDstWrites`

Used by: R4-src: counterexample (dstWrites = false (instantiated in the statement)).
```lean
sharedIMSound_noDst_needs_noDstWrites : Includes boolV byteV ∧ ¬SharedIMSound true true boolV byteV
```

#### `sharedIMSound_needs_includes`

Used by: R4-src: counterexample (right-hand side: Includes T U).
```lean
sharedIMSound_needs_includes : ∀ (srcWrites dstWrites : Bool),
  ¬Includes byteV boolV ∧ ¬SharedIMSound srcWrites dstWrites byteV boolV
```

#### `mutSound_iff_sharedIM_nonvacuous`

Used by: R4-mut: non-vacuity witness.
```lean
mutSound_iff_sharedIM_nonvacuous : MutSound boolV boolV' ∧
  SharedIMSound false true boolV boolV' ∧ SharedIMSound true true boolV boolV'
```

#### `mutSound_iff_sharedIM_needs_dstWrites`

Used by: R4-mut: counterexample (dstWrites = true (instantiated in the statement)).
```lean
mutSound_iff_sharedIM_needs_dstWrites : ¬MutSound boolV byteV ∧
  SharedIMSound true false boolV byteV ∧ ¬(MutSound boolV byteV ↔ SharedIMSound true false boolV byteV)
```

#### `valueSound_trans_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
valueSound_trans_nonvacuous : ValueSound zeroV boolV ∧ ValueSound boolV byteV
```

#### `sharedSound_trans_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
sharedSound_trans_nonvacuous : SharedSound zeroV boolV ∧ SharedSound boolV byteV
```

#### `mutSound_trans_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
mutSound_trans_nonvacuous : MutSound boolV' boolV ∧ MutSound boolV (Validity.join boolV zeroV)
```

#### `mutSound_trans_uninhabited_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
mutSound_trans_uninhabited_nonvacuous : ¬Satisfiable neverV ∧
  Satisfiable boolV ∧ ¬ValidityEq neverV boolV' ∧ MutSound neverV boolV ∧ MutSound boolV boolV'
```

#### `sharedIMSound_trans_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
sharedIMSound_trans_nonvacuous : ∀ (srcWrites dstWrites : Bool),
  SharedIMSound srcWrites dstWrites boolV' boolV ∧ SharedIMSound srcWrites dstWrites boolV (Validity.join boolV zeroV)
```

#### `sharedIMSound_trans_uninhabited_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
sharedIMSound_trans_uninhabited_nonvacuous : ∀ (srcWrites dstWrites : Bool),
  ¬Satisfiable neverV ∧
    ¬ValidityEq neverV boolV' ∧
      SharedIMSound srcWrites dstWrites neverV boolV ∧ SharedIMSound srcWrites dstWrites boolV boolV'
```

#### `sharedIMSound_noDst_trans_strict_nonvacuous`

Used by: R5-trans: non-vacuity witness.
```lean
sharedIMSound_noDst_trans_strict_nonvacuous : ∀ (srcWrites : Bool),
  ¬ValidityEq zeroV boolV ∧
    ¬ValidityEq boolV byteV ∧
      ¬ValidityEq zeroV byteV ∧ SharedIMSound srcWrites false zeroV boolV ∧ SharedIMSound srcWrites false boolV byteV
```

#### `valueSound_trans_needs_first`

Used by: R5-trans: counterexample (h₁ : Sound(T -> U)).
```lean
valueSound_trans_needs_first : ValueSound boolV boolV ∧ ¬ValueSound byteV boolV
```

#### `sharedSound_trans_needs_first`

Used by: R5-trans: counterexample (h₁ : Sound(T -> U)).
```lean
sharedSound_trans_needs_first : SharedSound boolV boolV ∧ ¬SharedSound byteV boolV
```

#### `mutSound_trans_needs_first`

Used by: R5-trans: counterexample (h₁ : Sound(T -> U)).
```lean
mutSound_trans_needs_first : MutSound boolV boolV ∧ ¬MutSound byteV boolV
```

#### `sharedIMSound_trans_needs_first`

Used by: R5-trans: counterexample (h₁ : Sound(T -> U)).
```lean
sharedIMSound_trans_needs_first : ∀ (srcWrites dstWrites : Bool),
  SharedIMSound srcWrites dstWrites boolV boolV ∧ ¬SharedIMSound srcWrites dstWrites byteV boolV
```

#### `valueSound_trans_needs_second`

Used by: R5-trans: counterexample (h₂ : Sound(U -> V)).
```lean
valueSound_trans_needs_second : ValueSound byteV byteV ∧ ¬ValueSound byteV boolV
```

#### `sharedSound_trans_needs_second`

Used by: R5-trans: counterexample (h₂ : Sound(U -> V)).
```lean
sharedSound_trans_needs_second : SharedSound byteV byteV ∧ ¬SharedSound byteV boolV
```

#### `mutSound_trans_needs_second`

Used by: R5-trans: counterexample (h₂ : Sound(U -> V)).
```lean
mutSound_trans_needs_second : MutSound byteV byteV ∧ ¬MutSound byteV boolV
```

#### `sharedIMSound_trans_needs_second`

Used by: R5-trans: counterexample (h₂ : Sound(U -> V)).
```lean
sharedIMSound_trans_needs_second : ∀ (srcWrites dstWrites : Bool),
  SharedIMSound srcWrites dstWrites byteV byteV ∧ ¬SharedIMSound srcWrites dstWrites byteV boolV
```

#### `sharedSound_boolV_byteV`

Used by: R5-hier: non-vacuity witness.
```lean
sharedSound_boolV_byteV : SharedSound boolV byteV
```

#### `valueSound_boolV_byteV`

Used by: R5-hier: non-vacuity witness.
```lean
valueSound_boolV_byteV : ValueSound boolV byteV
```

#### `mutSound_boolV_boolV'`

Used by: R5-hier: non-vacuity witness.
```lean
mutSound_boolV_boolV' : MutSound boolV boolV'
```

#### `sharedSound_not_imp_mutSound`

Used by: R5-hier: related witness.
```lean
sharedSound_not_imp_mutSound : SharedSound boolV byteV ∧ ¬MutSound boolV byteV
```

#### `not_valueSound_byteV_boolV`

Used by: R5-hier: counterexample (h (the stronger soundness)).
```lean
not_valueSound_byteV_boolV : ¬ValueSound byteV boolV
```

#### `not_sharedSound_byteV_boolV`

Used by: R5-hier: counterexample (h (the stronger soundness)).
```lean
not_sharedSound_byteV_boolV : ¬SharedSound byteV boolV
```

#### `mutSound_symm_nonvacuous`

Used by: R5-symm: non-vacuity witness.
```lean
mutSound_symm_nonvacuous : Satisfiable boolV ∧ MutSound boolV boolV'
```

#### `mutSound_not_iff_symm_of_satisfiable_left`

Used by: R5-symm: related witness.
```lean
mutSound_not_iff_symm_of_satisfiable_left : Satisfiable byteV ∧
  ¬MutSound byteV neverV ∧ MutSound neverV byteV ∧ ¬(MutSound byteV neverV ↔ MutSound neverV byteV)
```

#### `mutSound_symm_needs_satisfiable`

Used by: R5-symm: counterexample (hT : Satisfiable T).
```lean
mutSound_symm_needs_satisfiable : ¬Satisfiable neverV ∧ MutSound neverV byteV ∧ ¬MutSound byteV neverV
```

#### `mutSound_symm_needs_mutSound`

Used by: R5-symm: counterexample (h : MutSound T U).
```lean
mutSound_symm_needs_mutSound : Satisfiable boolV ∧ ¬MutSound boolV byteV ∧ ¬MutSound byteV boolV
```

#### `boolV_to_byteV_value_and_shared_sound`

Used by: R6-bool-byte: result.
```lean
boolV_to_byteV_value_and_shared_sound : Includes boolV byteV ∧ ValueSound boolV byteV ∧ SharedSound boolV byteV
```

#### `boolV_to_byteV_mut_violating_run`

Used by: R6-bool-byte: result.
```lean
boolV_to_byteV_mut_violating_run : mutProtocol (writeDstReadSrc (byteSeq 2)) ∧
  (∀ (op : Op (Fin 256) 1), op ∈ writeDstReadSrc (byteSeq 2) → Op.WellTyped boolV byteV op) ∧
    boolV (byteSeq 0) ∧ ¬NoInvalidRead boolV byteV (byteSeq 0) (writeDstReadSrc (byteSeq 2))
```

#### `boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes`

Used by: R6-im: result.
```lean
boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes : SharedSound boolV byteV ∧
  SharedIMSound false false boolV byteV ∧ ¬SharedIMSound false true boolV byteV ∧ ¬SharedIMSound true true boolV byteV
```

#### `sharedSound_to_join_left_nonvacuous`

Used by: R7-shared-lattice: non-vacuity witness.
```lean
sharedSound_to_join_left_nonvacuous : SharedSound boolV (Validity.join boolV twoV) ∧
  ¬Includes (Validity.join boolV twoV) boolV
```

#### `sharedSound_to_join_right_nonvacuous`

Used by: R7-shared-lattice: non-vacuity witness.
```lean
sharedSound_to_join_right_nonvacuous : SharedSound twoV (Validity.join boolV twoV) ∧
  ¬Includes (Validity.join boolV twoV) twoV
```

#### `sharedSound_from_meet_left_nonvacuous`

Used by: R7-shared-lattice: non-vacuity witness.
```lean
sharedSound_from_meet_left_nonvacuous : SharedSound (Validity.meet boolV zeroV) boolV ∧
  ¬Includes boolV (Validity.meet boolV zeroV)
```

#### `sharedSound_from_meet_right_nonvacuous`

Used by: R7-shared-lattice: non-vacuity witness.
```lean
sharedSound_from_meet_right_nonvacuous : SharedSound (Validity.meet zeroV boolV) boolV ∧
  ¬Includes boolV (Validity.meet zeroV boolV)
```

#### `sharedSound_join_iff_nonvacuous`

Used by: R7-shared-lattice: non-vacuity witness.
```lean
sharedSound_join_iff_nonvacuous : (SharedSound (Validity.join boolV twoV) byteV ∧
    SharedSound boolV byteV ∧ SharedSound twoV byteV) ∧
  ¬SharedSound (Validity.join boolV twoV) boolV ∧ ¬SharedSound twoV boolV
```

#### `sharedSound_meet_iff_nonvacuous`

Used by: R7-shared-lattice: non-vacuity witness.
```lean
sharedSound_meet_iff_nonvacuous : (¬ValidityEq zeroV boolV ∧
    ¬ValidityEq zeroV (Validity.join zeroV twoV) ∧
      SharedSound zeroV (Validity.meet boolV (Validity.join zeroV twoV)) ∧
        SharedSound zeroV boolV ∧ SharedSound zeroV (Validity.join zeroV twoV)) ∧
  ¬SharedSound boolV (Validity.meet byteV zeroV) ∧ SharedSound boolV byteV ∧ ¬SharedSound boolV zeroV
```

#### `sharedSound_join_iff_needs_left`

Used by: R7-shared-lattice: counterexample (sharedSound_join_iff, right-hand conjunct SharedSound T V).
```lean
sharedSound_join_iff_needs_left : SharedSound boolV boolV ∧
  ¬SharedSound twoV boolV ∧
    ¬SharedSound (Validity.join twoV boolV) boolV ∧
      ¬(SharedSound (Validity.join twoV boolV) boolV ↔ SharedSound boolV boolV)
```

#### `sharedSound_join_iff_needs_right`

Used by: R7-shared-lattice: counterexample (sharedSound_join_iff, right-hand conjunct SharedSound U V).
```lean
sharedSound_join_iff_needs_right : SharedSound boolV boolV ∧
  ¬SharedSound twoV boolV ∧
    ¬SharedSound (Validity.join boolV twoV) boolV ∧
      ¬(SharedSound (Validity.join boolV twoV) boolV ↔ SharedSound boolV boolV)
```

#### `sharedSound_meet_iff_needs_left`

Used by: R7-shared-lattice: counterexample (sharedSound_meet_iff, right-hand conjunct SharedSound V T).
```lean
sharedSound_meet_iff_needs_left : SharedSound boolV byteV ∧
  ¬SharedSound boolV zeroV ∧
    ¬SharedSound boolV (Validity.meet zeroV byteV) ∧
      ¬(SharedSound boolV (Validity.meet zeroV byteV) ↔ SharedSound boolV byteV)
```

#### `sharedSound_meet_iff_needs_right`

Used by: R7-shared-lattice: counterexample (sharedSound_meet_iff, right-hand conjunct SharedSound V U).
```lean
sharedSound_meet_iff_needs_right : SharedSound boolV byteV ∧
  ¬SharedSound boolV zeroV ∧
    ¬SharedSound boolV (Validity.meet byteV zeroV) ∧
      ¬(SharedSound boolV (Validity.meet byteV zeroV) ↔ SharedSound boolV byteV)
```

#### `mutSound_to_join_nonvacuous`

Used by: R7-mut-join: non-vacuity witness.
```lean
mutSound_to_join_nonvacuous : Satisfiable boolV ∧
  MutSound boolV (Validity.join boolV zeroV) ∧ Includes zeroV boolV ∧ ¬Includes boolV zeroV
```

#### `mutSound_to_join_fails_example`

Used by: R7-mut-join: related witness.
```lean
mutSound_to_join_fails_example : SharedSound boolV (Validity.join boolV twoV) ∧
  ¬MutSound boolV (Validity.join boolV twoV)
```

#### `mutSound_to_join_needs_satisfiable`

Used by: R7-mut-join: counterexample (hT : Satisfiable T).
```lean
mutSound_to_join_needs_satisfiable : ¬Satisfiable neverV ∧
  MutSound neverV (Validity.join neverV byteV) ∧
    ¬Includes byteV neverV ∧ ¬(MutSound neverV (Validity.join neverV byteV) ↔ Includes byteV neverV)
```

#### `mutSound_to_join_needs_includes_rev`

Used by: R7-mut-join: counterexample (right-hand side: Includes U T).
```lean
mutSound_to_join_needs_includes_rev : Satisfiable boolV ∧
  ¬Includes twoV boolV ∧ ¬MutSound boolV (Validity.join boolV twoV)
```

#### `mutSound_from_meet_nonvacuous`

Used by: R7-mut-meet: non-vacuity witness.
```lean
mutSound_from_meet_nonvacuous : Satisfiable (Validity.meet zeroV boolV) ∧
  ¬ValidityEq zeroV boolV ∧ MutSound (Validity.meet zeroV boolV) zeroV ∧ Includes zeroV boolV
```

#### `mutSound_from_meet_needs_joint_satisfiable`

Used by: R7-mut-meet: counterexample (h : Satisfiable (T ⊓ U)).
```lean
mutSound_from_meet_needs_joint_satisfiable : Satisfiable zeroV ∧
  Satisfiable twoV ∧
    ¬Satisfiable (Validity.meet zeroV twoV) ∧
      MutSound (Validity.meet zeroV twoV) zeroV ∧
        ¬Includes zeroV twoV ∧ ¬(MutSound (Validity.meet zeroV twoV) zeroV ↔ Includes zeroV twoV)
```

#### `mutSound_from_meet_needs_satisfiable`

Used by: R7-mut-meet: counterexample (h : Satisfiable (T ⊓ U)).
```lean
mutSound_from_meet_needs_satisfiable : ¬Satisfiable (Validity.meet byteV neverV) ∧
  MutSound (Validity.meet byteV neverV) byteV ∧
    ¬Includes byteV neverV ∧ ¬(MutSound (Validity.meet byteV neverV) byteV ↔ Includes byteV neverV)
```

#### `mutSound_from_meet_fails_example`

Used by: R7-mut-meet: counterexample (right-hand side: Includes T U).
```lean
mutSound_from_meet_fails_example : Satisfiable (Validity.meet boolV zeroV) ∧
  ¬Includes boolV zeroV ∧ ¬MutSound (Validity.meet boolV zeroV) boolV
```

#### `checkedSound_valueProtocol_nonvacuous`

Used by: R8-value-shared: non-vacuity witness.
```lean
checkedSound_valueProtocol_nonvacuous : Satisfiable (Validity.meet byteV boolV) ∧
  CheckedSound valueProtocol byteV boolV ∧ ¬ValueSound byteV boolV
```

#### `checkedSound_sharedProtocol_nonvacuous`

Used by: R8-value-shared: non-vacuity witness.
```lean
checkedSound_sharedProtocol_nonvacuous : Satisfiable (Validity.meet byteV boolV) ∧
  CheckedSound sharedProtocol byteV boolV ∧ ¬SharedSound byteV boolV
```

#### `checkedSound_mut_nonvacuous`

Used by: R8-mut: non-vacuity witness.
```lean
checkedSound_mut_nonvacuous : (Satisfiable (Validity.meet byteV boolV) ∧
    CheckedSound mutProtocol byteV boolV ∧ Includes boolV byteV) ∧
  Satisfiable (Validity.meet boolV byteV) ∧ ¬CheckedSound mutProtocol boolV byteV ∧ ¬Includes byteV boolV
```

#### `checkedSound_mut_byteV_boolV`

Used by: R8-mut: related witness.
```lean
checkedSound_mut_byteV_boolV : CheckedSound mutProtocol byteV boolV
```

#### `checkedSound_mut_needs_includes_rev`

Used by: R8-mut: counterexample (right-hand side: Includes U T).
```lean
checkedSound_mut_needs_includes_rev : Satisfiable (Validity.meet boolV byteV) ∧
  ¬Includes byteV boolV ∧ ¬CheckedSound mutProtocol boolV byteV
```

#### `checkedSound_mut_rhs_needs_satisfiable_meet_guard`

Used by: R8-mut: counterexample (right-hand side: the guard 'Satisfiable (T ⊓ U) ->').
```lean
checkedSound_mut_rhs_needs_satisfiable_meet_guard : Satisfiable zeroV ∧
  Satisfiable twoV ∧
    ¬Satisfiable (Validity.meet zeroV twoV) ∧
      CheckedSound mutProtocol zeroV twoV ∧
        ¬Includes twoV zeroV ∧ ¬(CheckedSound mutProtocol zeroV twoV ↔ Includes twoV zeroV)
```

#### `checkedSound_sharedIM_nonvacuous`

Used by: R8-im: non-vacuity witness.
```lean
checkedSound_sharedIM_nonvacuous : (CheckedSound (sharedIMProtocol true true) boolV boolV' ∧
    Includes boolV boolV' ∧ Includes boolV' boolV) ∧
  (CheckedSound (sharedIMProtocol false true) byteV boolV ∧ Includes boolV byteV) ∧
    (CheckedSound (sharedIMProtocol true false) boolV byteV ∧ Includes boolV byteV) ∧
      Satisfiable (Validity.meet byteV boolV) ∧
        ¬CheckedSound (sharedIMProtocol true false) byteV boolV ∧ ¬Includes byteV boolV
```

#### `checkedSound_sharedIM_needs_srcWrites_includes`

Used by: R8-im: counterexample (right-hand side: srcWrites = true -> Includes T U).
```lean
checkedSound_sharedIM_needs_srcWrites_includes : Satisfiable (Validity.meet byteV boolV) ∧
  Includes boolV byteV ∧ ¬Includes byteV boolV ∧ ¬CheckedSound (sharedIMProtocol true true) byteV boolV
```

#### `checkedSound_sharedIM_needs_dstWrites_includes_rev`

Used by: R8-im: counterexample (right-hand side: dstWrites = true -> Includes U T).
```lean
checkedSound_sharedIM_needs_dstWrites_includes_rev : Satisfiable (Validity.meet boolV byteV) ∧
  Includes boolV byteV ∧ ¬Includes byteV boolV ∧ ¬CheckedSound (sharedIMProtocol true true) boolV byteV
```

#### `checkedSound_sharedIM_rhs_needs_satisfiable_meet_guard`

Used by: R8-im: counterexample (right-hand side: the guard 'Satisfiable (T ⊓ U) ->').
```lean
checkedSound_sharedIM_rhs_needs_satisfiable_meet_guard : Satisfiable zeroV ∧
  Satisfiable twoV ∧
    ¬Satisfiable (Validity.meet zeroV twoV) ∧
      CheckedSound (sharedIMProtocol true true) zeroV twoV ∧
        ¬((true = true → Includes zeroV twoV) ∧ (true = true → Includes twoV zeroV))
```

#### `checkedSound_sharedIM_rhs_needs_srcWrites_guard`

Used by: R8-im: counterexample (right-hand side: the guard 'srcWrites = true ->').
```lean
checkedSound_sharedIM_rhs_needs_srcWrites_guard : CheckedSound (sharedIMProtocol false true) byteV boolV ∧
  Satisfiable (Validity.meet byteV boolV) ∧
    Includes boolV byteV ∧
      ¬Includes byteV boolV ∧
        ¬(Satisfiable (Validity.meet byteV boolV) → Includes byteV boolV ∧ (true = true → Includes boolV byteV)) ∧
          ¬(CheckedSound (sharedIMProtocol false true) byteV boolV ↔
              Satisfiable (Validity.meet byteV boolV) → Includes byteV boolV ∧ (true = true → Includes boolV byteV))
```

#### `checkedSound_sharedIM_rhs_needs_dstWrites_guard`

Used by: R8-im: counterexample (right-hand side: the guard 'dstWrites = true ->').
```lean
checkedSound_sharedIM_rhs_needs_dstWrites_guard : CheckedSound (sharedIMProtocol true false) boolV byteV ∧
  Satisfiable (Validity.meet boolV byteV) ∧
    Includes boolV byteV ∧
      ¬Includes byteV boolV ∧
        ¬(Satisfiable (Validity.meet boolV byteV) → (true = true → Includes boolV byteV) ∧ Includes byteV boolV) ∧
          ¬(CheckedSound (sharedIMProtocol true false) boolV byteV ↔
              Satisfiable (Validity.meet boolV byteV) → (true = true → Includes boolV byteV) ∧ Includes byteV boolV)
```

### Proof tools

The proofs rest on two explicit violating runs and on invariant reasoning (`lean/ToyTransmute/Tools.lean`; the first two lemmas below are in `lean/ToyTransmute/Results.lean`). Necessity: soundness of a discipline that permits the run `readDst = [read dst]` forces `T ⊆ U`; soundness of a discipline that permits every run `writeDstReadSrc u = [write dst u, read src]` forces `T satisfiable → U ⊆ T`; for checked interior-mutable casts the run `writeSrcReadDst v = [write src v, read dst]` forces `T ⊆ U` when source writes are permitted. Sufficiency: an invariant on the region contents that holds initially, is re-established by every permitted well-typed write and implies the validity demanded by every permitted read (two invariants switched at the hand-over point for checked mutable casts).

```lean
includes_of_sound_readDst : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n},
  P readDst → Sound P T U → Includes T U
```
```lean
includes_rev_of_sound_writeDstReadSrc : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n},
  (∀ (u : Bytes B n), P (writeDstReadSrc u)) → Sound P T U → Satisfiable T → Includes U T
```
```lean
not_sound_of_read_dst : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n},
  P readDst → ∀ {m : Bytes B n}, T m → ¬U m → ¬Sound P T U
```
```lean
not_sound_of_write_dst_read_src : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n} {u : Bytes B n},
  P (writeDstReadSrc u) → ∀ {m : Bytes B n}, T m → U u → ¬T u → ¬Sound P T U
```
```lean
sound_of_invariant : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n} (I : Bytes B n → Prop),
  (∀ (m : Bytes B n), T m → I m) →
    (∀ (tr : List (Op B n)), P tr → ∀ (op : Op B n), op ∈ tr → Op.Preserves T U I op) → Sound P T U
```
```lean
noInvalidRead_of_invariant : ∀ {B : Type} {n : Nat} {T U : Validity B n} (I : Bytes B n → Prop) (tr : List (Op B n))
  (m : Bytes B n),
  I m →
    (∀ (op : Op B n), op ∈ tr → Op.WellTyped T U op) →
      (∀ (op : Op B n), op ∈ tr → Op.Preserves T U I op) → NoInvalidRead T U m tr
```
```lean
sound_of_validityEq : ∀ {B : Type} {n : Nat} (P : Protocol B n) {T U : Validity B n}, ValidityEq T U → Sound P T U
```
```lean
sound_of_not_satisfiable : ∀ {B : Type} {n : Nat} (P : Protocol B n) {T : Validity B n},
  ¬Satisfiable T → ∀ (U : Validity B n), Sound P T U
```
```lean
noInvalidRead_append_of_invariants : ∀ {B : Type} {n : Nat} {T U : Validity B n} (I J : Bytes B n → Prop),
  (∀ (m : Bytes B n), I m → J m) →
    ∀ (l₁ l₂ : List (Op B n)) (m : Bytes B n),
      I m →
        (∀ (op : Op B n), op ∈ l₁ → Op.WellTyped T U op) →
          (∀ (op : Op B n), op ∈ l₂ → Op.WellTyped T U op) →
            (∀ (op : Op B n), op ∈ l₁ → Op.Preserves T U I op) →
              (∀ (op : Op B n), op ∈ l₂ → Op.Preserves T U J op) → NoInvalidRead T U m (l₁ ++ l₂)
```
```lean
checkedSound_of_sound : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n},
  Sound P T U → CheckedSound P T U
```
```lean
checkedSound_of_invariant : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n} (I : Bytes B n → Prop),
  (∀ (m : Bytes B n), T m → U m → I m) →
    (∀ (tr : List (Op B n)), P tr → ∀ (op : Op B n), op ∈ tr → Op.Preserves T U I op) → CheckedSound P T U
```
```lean
checkedSound_mut_of_invariants : ∀ {B : Type} {n : Nat} {T U : Validity B n} (I J : Bytes B n → Prop),
  (∀ (m : Bytes B n), T m → U m → I m) →
    (∀ (m : Bytes B n), I m → J m) →
      (∀ (m : Bytes B n), I m → U m) →
        (∀ (v : Bytes B n), U v → I v) →
          (∀ (m : Bytes B n), J m → T m) → (∀ (v : Bytes B n), T v → J v) → CheckedSound mutProtocol T U
```
```lean
checkedSound_of_not_satisfiable_meet : ∀ {B : Type} {n : Nat} (P : Protocol B n) {T U : Validity B n},
  ¬Satisfiable (Validity.meet T U) → CheckedSound P T U
```
```lean
not_checkedSound_of_write_dst_read_src : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n}
  {u : Bytes B n}, P (writeDstReadSrc u) → ∀ {m : Bytes B n}, T m → U m → U u → ¬T u → ¬CheckedSound P T U
```
```lean
not_checkedSound_of_write_src_read_dst : ∀ {B : Type} {n : Nat} {P : Protocol B n} {T U : Validity B n}
  {v : Bytes B n}, P (writeSrcReadDst v) → ∀ {m : Bytes B n}, T m → U m → T v → ¬U v → ¬CheckedSound P T U
```

## Boundaries

### Non-claims

**Global non-claim (applies to every result).** All statements are about the toy model of this package: a type is a bit-validity predicate on byte sequences of one fixed size n, both views cover the same n-byte region, reads and writes act on the whole region, and values are flat byte sequences. Nothing is said about alignment, size-changing (prefix, sub-slice or unsized) casts, provenance, uninitialised or padding bytes, pointer metadata or the memory a pointer refers to, aliasing models, concurrency, destructors or auto traits, or library-level safety invariants; see the modeling bridge in the Applicability section of the package report.

Per result, in addition to the global non-claim:

#### R1

- Does not cover transmutes between types of different sizes: such casts cannot be expressed (sizes are a type index).
- Values are flat byte sequences. For a type whose bytes contain a reference, box or other pointer, Includes on the pointer's own bytes says nothing about the memory it points to: `&mut bool` and `&mut u8` have the same pointer bit patterns, yet reinterpreting one as the other is a mutable-reference cast whose referents are governed by R3. Value transmutes of pointer-containing types are not covered.
- Characterizes unchecked casts, which accept every T-valid value without inspecting it. A conversion that checks validity at U once, at cast time (zerocopy's try_transmute! and try_transmute_ref!), is sound in this model for every pair of equal-size types (R8-value-shared), even when T ⊆ U fails.
- Bytes here are always initialised, so the all-bytes validity (byteV) includes every T. Do not read this as 'a destination that accepts every initialised byte sequence can receive any source': with uninitialised or padding bytes the source must also consist of initialised bytes only, which is what zerocopy's Src: IntoBytes requires in addition to Dst: FromBytes.
- Only bit validity is modelled; destructors and auto traits are not. Even when T ≡ U, a value transmute does not run T's destructor (zerocopy's transmute! documents that the source 'will not be dropped') and U's destructor may later run on the bytes; through a mutable-reference cast a value written at U may later be dropped at T and vice versa; and reinterpreting between types that differ in Send or Sync can break thread-safety guarantees. None of this is captured here.
- Does not claim that value transmutes and shared-reference casts have the same requirements in a real language: in this model they coincide (R5-hier), but real reference casts additionally involve alignment, size relations for unsized types, and interior-mutability/aliasing rules.
- Says nothing about the source after the transmute: a copied source is an independent region and is not modelled.
- Soundness quantifies over all permitted runs; an individual run that never reads the value observes nothing (noInvalidRead_unchecked_until_read). This matches eager cast-time validity only at the level of Sound, not run by run.

#### R2

- Assumes no writes through either reference while the cast is in effect; with interior mutability see R4.
- Both views cover exactly the same n bytes. Reference casts to a smaller referent (prefix casts, sub-slices, `&mut [u8; 4] → &mut [u8; 2]`), which rustc's checker accepts when the destination referent is no larger than the source referent, are outside the model: whole-type validity equality would wrongly reject `&mut [u8; 4] → &mut [u8; 2]`, and equality of the prefix's own validity would wrongly accept a write that breaks an invariant coupling the viewed bytes with the unviewed ones (for example two bytes required to sum to zero).
- Characterizes unchecked casts, which accept every T-valid value without inspecting it. A conversion that checks validity at U once, at cast time (zerocopy's try_transmute! and try_transmute_ref!), is sound in this model for every pair of equal-size types (R8-value-shared), even when T ⊆ U fails.
- Bytes here are always initialised, so the all-bytes validity (byteV) includes every T. Do not read this as 'a destination that accepts every initialised byte sequence can receive any source': with uninitialised or padding bytes the source must also consist of initialised bytes only, which is what zerocopy's Src: IntoBytes requires in addition to Dst: FromBytes.
- Does not address alignment: a real &T -> &U cast also needs the address to be suitably aligned for U.
- The original reference's reads always succeed here only because nobody writes; this is not a claim about aliasing-model legality of keeping both references.

#### R3

- Characterizes unchecked mutable-reference casts, which must accept every T-valid initial value without inspecting it. A cast that checks validity at U once, at cast time, and then hands out an ordinary unchecked `&mut U` (as zerocopy's try_transmute_mut! does) is a different discipline: by R8-mut it is sound iff (some byte sequence is valid at both T and U) → U ⊆ T; neither T ⊆ U nor T ≡ U is required (checkedSound_mut_escapes_impossibility: byte → bool).
- Both views cover exactly the same n bytes. Reference casts to a smaller referent (prefix casts, sub-slices, `&mut [u8; 4] → &mut [u8; 2]`), which rustc's checker accepts when the destination referent is no larger than the source referent, are outside the model: whole-type validity equality would wrongly reject `&mut [u8; 4] → &mut [u8; 2]`, and equality of the prefix's own validity would wrongly accept a write that breaks an invariant coupling the viewed bytes with the unviewed ones (for example two bytes required to sum to zero).
- Writes are whole-region writes of arbitrary U-valid values. If an API only lets the holder write a restricted set of values (for example because U has a stronger safety invariant or private fields), the write-side requirement weakens accordingly; this is not modelled.
- Vacuous soundness from an unsatisfiable source holds here only because Sound assumes the region already holds a T-valid value. The Rust Reference ([undefined.validity.reference-box]) requires a reference to point to a valid value, noting that this point 'remains a subject of some debate'; under that requirement a reference to an uninhabited type is never valid, so this edge case does not license creating, say, a `&mut` to an empty enum and casting it to `&mut u8`. rustc's checker likewise answers Yes for uninhabited source types (mod.rs lines 112-119).
- Only bit validity is modelled; destructors and auto traits are not. Even when T ≡ U, a value transmute does not run T's destructor (zerocopy's transmute! documents that the source 'will not be dropped') and U's destructor may later run on the bytes; through a mutable-reference cast a value written at U may later be dropped at T and vice versa; and reinterpreting between types that differ in Send or Sync can break thread-safety guarantees. None of this is captured here.
- Does not model reborrowing chains with more than two live views, nor two-phase borrows.

#### R3-eq

- Equality is extensional (same accepted byte sequences), not equality of type names or definitions.
- Does not say a sound mutable cast is the identity on values; only that both views accept the same bytes.
- Characterizes unchecked mutable-reference casts, which must accept every T-valid initial value without inspecting it. A cast that checks validity at U once, at cast time, and then hands out an ordinary unchecked `&mut U` (as zerocopy's try_transmute_mut! does) is a different discipline: by R8-mut it is sound iff (some byte sequence is valid at both T and U) → U ⊆ T; neither T ⊆ U nor T ≡ U is required (checkedSound_mut_escapes_impossibility: byte → bool).
- Both views cover exactly the same n bytes. Reference casts to a smaller referent (prefix casts, sub-slices, `&mut [u8; 4] → &mut [u8; 2]`), which rustc's checker accepts when the destination referent is no larger than the source referent, are outside the model: whole-type validity equality would wrongly reject `&mut [u8; 4] → &mut [u8; 2]`, and equality of the prefix's own validity would wrongly accept a write that breaks an invariant coupling the viewed bytes with the unviewed ones (for example two bytes required to sum to zero).
- Only bit validity is modelled; destructors and auto traits are not. Even when T ≡ U, a value transmute does not run T's destructor (zerocopy's transmute! documents that the source 'will not be dropped') and U's destructor may later run on the bytes; through a mutable-reference cast a value written at U may later be dropped at T and vice versa; and reinterpreting between types that differ in Send or Sync can break thread-safety guarantees. None of this is captured here.
- Vacuous soundness from an unsatisfiable source holds here only because Sound assumes the region already holds a T-valid value. The Rust Reference ([undefined.validity.reference-box]) requires a reference to point to a valid value, noting that this point 'remains a subject of some debate'; under that requirement a reference to an uninhabited type is never valid, so this edge case does not license creating, say, a `&mut` to an empty enum and casting it to `&mut u8`. rustc's checker likewise answers Yes for uninhabited source types (mod.rs lines 112-119).

#### R3-imp

- Escape hatches, each defeating the impossibility: the cast checks validity at U once at cast time (R8-mut; the condition then becomes (some byte sequence is valid at both T and U) → U ⊆ T, as for zerocopy's try_transmute_mut!); the cast reference cannot write arbitrary U-valid values (not modelled); the owner never reads again (not a property of a reference cast); or the source type is uninhabited.
- Does not forbid other checked designs either, such as re-validating on every read or a run-time check on every store (as for Java arrays); those are outside the model.
- Both views cover exactly the same n bytes. Reference casts to a smaller referent (prefix casts, sub-slices, `&mut [u8; 4] → &mut [u8; 2]`), which rustc's checker accepts when the destination referent is no larger than the source referent, are outside the model: whole-type validity equality would wrongly reject `&mut [u8; 4] → &mut [u8; 2]`, and equality of the prefix's own validity would wrongly accept a write that breaks an invariant coupling the viewed bytes with the unviewed ones (for example two bytes required to sum to zero).

#### R4

- Bit validity only. The source-only-writes case (an interior-mutable source viewed through a read-only destination) is validity-sound here, but in Rust writing through one reference while a shared reference without interior mutability to the same bytes is in use is governed by the aliasing model (Stacked Borrows, Tree Borrows), independently of validity. zerocopy's transmute_ref! excludes the case by requiring Immutable on both Src and Dst. rustc's transmutability checker (at the cited commit) requires only the destination referent of a shared-reference cast to be free of interior mutability and places no such condition on the source referent.
- The write flags are per side and cover the whole region; they do not track which bytes lie inside an `UnsafeCell`. In Rust, `&(UnsafeCell<u8>, u8) → &(u8, UnsafeCell<u8>)` has equal validities and interior mutability on both sides, yet the destination may mutate a byte that the source type does not mark as interior-mutable; nothing here says such a cast is sound.
- Validity equality says nothing about whether two interior-mutable types use compatible synchronization or borrow-tracking protocols (for example an atomic integer versus `Cell<u8>`, or the borrow flag of a `RefCell`). rustc's transmutability checker rejects even `&UnsafeCell<u8> → &UnsafeCell<u8>` (its UI test comment: 'the two types may use different, incompatible synchronization strategies'), and zerocopy's transmute_ref! requires both sides to be free of interior mutability.
- Both views cover exactly the same n bytes. Reference casts to a smaller referent (prefix casts, sub-slices, `&mut [u8; 4] → &mut [u8; 2]`), which rustc's checker accepts when the destination referent is no larger than the source referent, are outside the model: whole-type validity equality would wrongly reject `&mut [u8; 4] → &mut [u8; 2]`, and equality of the prefix's own validity would wrongly accept a write that breaks an invariant coupling the viewed bytes with the unviewed ones (for example two bytes required to sum to zero).
- Does not model concurrent (racing) writes; runs are sequential interleavings.
- Unchecked casts only. For a cast checked once at cast time, source-side writes do matter (R8-im).

#### R4-eq

- Does not say that interior mutability on the source side alone forces equality; it does not (sharedIMSound_eq_needs_dstWrites).
- The write flags are per side and cover the whole region; they do not track which bytes lie inside an `UnsafeCell`. In Rust, `&(UnsafeCell<u8>, u8) → &(u8, UnsafeCell<u8>)` has equal validities and interior mutability on both sides, yet the destination may mutate a byte that the source type does not mark as interior-mutable; nothing here says such a cast is sound.
- Validity equality says nothing about whether two interior-mutable types use compatible synchronization or borrow-tracking protocols (for example an atomic integer versus `Cell<u8>`, or the borrow flag of a `RefCell`). rustc's transmutability checker rejects even `&UnsafeCell<u8> → &UnsafeCell<u8>` (its UI test comment: 'the two types may use different, incompatible synchronization strategies'), and zerocopy's transmute_ref! requires both sides to be free of interior mutability.
- Bit validity only; aliasing rules are not modelled (see R4).
- Unchecked casts only. For a cast checked once at cast time, equality is not required: with only destination-side writes, R8-im requires just (some byte sequence is valid at both T and U) → U ⊆ T. For example byte is satisfiable and the validities of byte and bool differ (checkedSound_mut_escapes_impossibility), yet byte → bool checked once at cast time with only destination-side writes is sound (checkedSound_sharedIM_nonvacuous). With source-side writes as well, the checked cast needs both inclusions whenever the meet is satisfiable (R8-im).

#### R4-src

- Bit validity only. The source-only-writes case (an interior-mutable source viewed through a read-only destination) is validity-sound here, but in Rust writing through one reference while a shared reference without interior mutability to the same bytes is in use is governed by the aliasing model (Stacked Borrows, Tree Borrows), independently of validity. zerocopy's transmute_ref! excludes the case by requiring Immutable on both Src and Dst. rustc's transmutability checker (at the cited commit) requires only the destination referent of a shared-reference cast to be free of interior mutability and places no such condition on the source referent.
- In particular this does not license `&Cell<T> → &U` casts in Rust: mutating bytes through the cell while a shared reference without interior mutability to them is in use is governed by the aliasing model regardless of validity.
- Unchecked casts only. A cast checked once at cast time with source-side writes needs T ⊆ U as well (R8-im).

#### R4-mut

- Equal soundness conditions do not mean the disciplines permit the same programs: the mutable discipline forbids the owner from acting while the cast reference is live, the shared one does not.
- Says nothing about aliasing-model legality, which differs between the two in real languages.
- The write flags are per side and cover the whole region; they do not track which bytes lie inside an `UnsafeCell`. In Rust, `&(UnsafeCell<u8>, u8) → &(u8, UnsafeCell<u8>)` has equal validities and interior mutability on both sides, yet the destination may mutate a byte that the source type does not mark as interior-mutable; nothing here says such a cast is sound.
- Validity equality says nothing about whether two interior-mutable types use compatible synchronization or borrow-tracking protocols (for example an atomic integer versus `Cell<u8>`, or the borrow flag of a `RefCell`). rustc's transmutability checker rejects even `&UnsafeCell<u8> → &UnsafeCell<u8>` (its UI test comment: 'the two types may use different, incompatible synchronization strategies'), and zerocopy's transmute_ref! requires both sides to be free of interior mutability.
- Unchecked casts only. For casts checked once at cast time, the mutable cast does not correspond to the destination-writable shared cast with interior mutability when the source side may also write: checked once at cast time, byte → bool is sound as a mutable cast (checkedSound_mut_byteV_boolV) but unsound as a shared cast with interior mutability in which both sides may write (checkedSound_sharedIM_needs_srcWrites_includes), because the source-side writes happen after the check. (Without source-side writes the right-hand sides of R8-mut and R8-im coincide; that is a derived consequence of those two results, not a separate theorem.)

#### R5-trans

- Transitivity of the pairwise soundness predicates. Not proved: that a chain of casts with three simultaneously live views (T-, U- and V-typed) is sound as a single operational scenario; the model only has two views.
- Does not mix kinds: e.g. a shared cast followed by a mutable cast is not covered.
- Transitivity of unchecked soundness. Composing casts checked at cast time (R8) needs the intermediate check and is not stated here.

#### R5-hier

- The coincidence of value and shared soundness is an artefact of omitting alignment, size changes for unsized types and aliasing; in a real language a value transmute can be fine while the corresponding reference cast is not (e.g. under-aligned destination).
- Values are flat byte sequences. For a type whose bytes contain a reference, box or other pointer, Includes on the pointer's own bytes says nothing about the memory it points to: `&mut bool` and `&mut u8` have the same pointer bit patterns, yet reinterpreting one as the other is a mutable-reference cast whose referents are governed by R3. Value transmutes of pointer-containing types are not covered.

#### R5-symm

- Satisfiable T yields the one-way implication MutSound T U → MutSound U T, not MutSound T U ↔ MutSound U T: for (T, U) = (byte, never), never → byte is (vacuously) sound and byte → never is not (mutSound_not_iff_symm_of_satisfiable_left). The biconditional needs both T and U satisfiable.
- Symmetry concerns bit validity only. Real mutable-reference casts also require the destination to be no more strictly aligned than the source, which is not symmetric unless the alignments are equal.
- Only bit validity is modelled; destructors and auto traits are not. Even when T ≡ U, a value transmute does not run T's destructor (zerocopy's transmute! documents that the source 'will not be dropped') and U's destructor may later run on the bytes; through a mutable-reference cast a value written at U may later be dropped at T and vice versa; and reinterpreting between types that differ in Send or Sync can break thread-safety guarantees. None of this is captured here.

#### R6-bool-byte

- Says nothing about other pairs of types beyond what R1-R3 state.

#### R6-byte-bool

- Does not say that byte -> bool is unusable: a conversion checked at cast time is sound (R8-value-shared, R8-mut).
- Covers the value, shared and mutable disciplines only. The shared cast with interior mutability is not part of this theorem; for byte → bool it is unsound under every pair of write flags by R4 (sharedIMSound_needs_includes_canonical).

#### R6-im

- Bit validity only. Even the version without destination writes is subject to aliasing rules in a real language (see R4-src).

#### R6-src-writes

- Bit validity only; in Rust a write through the source while a shared reference without interior mutability to the same bytes is in use is governed by the aliasing model (see R4-src).
- Unchecked casts only; checked at cast time, source-side writes do require T ⊆ U (R8-im).

#### R6-never

- Vacuous soundness from an unsatisfiable source holds here only because Sound assumes the region already holds a T-valid value. The Rust Reference ([undefined.validity.reference-box]) requires a reference to point to a valid value, noting that this point 'remains a subject of some debate'; under that requirement a reference to an uninhabited type is never valid, so this edge case does not license creating, say, a `&mut` to an empty enum and casting it to `&mut u8`. rustc's checker likewise answers Yes for uninhabited source types (mod.rs lines 112-119).

#### R7-shared-lattice

- The join is the validity of a hypothetical 'either T or U' type of the same size. It is not the validity of a Rust union, whose validity requirements may be weaker, nor of a tagged enum (which has a different layout).

#### R7-mut-join

- Not a statement about Rust unions or enums (see R7-shared-lattice).
- Characterizes unchecked mutable-reference casts, which must accept every T-valid initial value without inspecting it. A cast that checks validity at U once, at cast time, and then hands out an ordinary unchecked `&mut U` (as zerocopy's try_transmute_mut! does) is a different discipline: by R8-mut it is sound iff (some byte sequence is valid at both T and U) → U ⊆ T; neither T ⊆ U nor T ≡ U is required (checkedSound_mut_escapes_impossibility: byte → bool).

#### R7-mut-meet

- Not a statement about Rust unions or enums (see R7-shared-lattice).
- Characterizes unchecked mutable-reference casts, which must accept every T-valid initial value without inspecting it. A cast that checks validity at U once, at cast time, and then hands out an ordinary unchecked `&mut U` (as zerocopy's try_transmute_mut! does) is a different discipline: by R8-mut it is sound iff (some byte sequence is valid at both T and U) → U ⊆ T; neither T ⊆ U nor T ≡ U is required (checkedSound_mut_escapes_impossibility: byte → bool).

#### R8-value-shared

- Soundness of the successful path only: the check costs run time and can fail; what happens on failure is not modelled.
- The check is on bit validity only; library safety invariants of U (for example a private field that must be even) need their own checks.
- Shared casts with interior mutability are not covered: with source-side writes after the check, T ⊆ U is needed again (R8-im).
- Values are flat byte sequences. For a type whose bytes contain a reference, box or other pointer, validating or comparing the pointer's own bytes says nothing about the memory it points to: `&mut bool` and `&mut u8` have the same pointer bit patterns, yet reinterpreting one as the other is a mutable-reference cast whose referents are governed by R3. Value transmutes of pointer-containing types are not covered.
- Bytes here are always initialised, so the check can always read the source bytes. With uninitialised or padding bytes, performing the run-time check at U means reading the source value's bytes, so the source must consist of initialised bytes only; zerocopy's try_transmute! and try_transmute_ref! require Src: IntoBytes for this. The unconditional 'for every T and U' of this result does not remove that requirement.
- Only bit validity is modelled; destructors are not. On success, zerocopy's try_transmute! does not run the source's destructor (its documentation: 'the Src produced by the expression $e will not be dropped. Semantically, its bits will be copied into a new value of type Dst, the original Src will be forgotten'), and the destination's destructor may later run on the bytes. None of this is captured here.

#### R8-mut

- The check happens exactly once, when the cast is made; later contents are not re-checked. Designs that re-check on every read or on every store (as Java arrays do on stores) are different disciplines, not modelled.
- The check is on bit validity only; library safety invariants of U are not checked, and an API that restricts what may be written through the cast reference weakens the write-side requirement (not modelled).
- Concurrent modification of the bytes between the check and the use is not modelled.
- Soundness of the successful path only: the check costs run time and can fail; what happens on failure is not modelled.
- Bytes here are always initialised, so the check can always read the source bytes. With uninitialised or padding bytes, performing the run-time check at U means reading the source referent's bytes, so the source must consist of initialised bytes only; zerocopy's try_transmute_mut! requires Src: IntoBytes for this, in addition to the Src: FromBytes and Dst: IntoBytes bounds that give U ⊆ T (Src: FromBytes alone does not exclude padding bytes in the source). The 'if and only if' of this result does not remove that requirement.
- Both views cover exactly the same n bytes. Reference casts to a smaller referent (prefix casts, sub-slices, `&mut [u8; 4] → &mut [u8; 2]`), which rustc's checker accepts when the destination referent is no larger than the source referent, are outside the model: whole-type validity equality would wrongly reject `&mut [u8; 4] → &mut [u8; 2]`, and equality of the prefix's own validity would wrongly accept a write that breaks an invariant coupling the viewed bytes with the unviewed ones (for example two bytes required to sum to zero).
- Only bit validity is modelled; destructors and auto traits are not. Even when T ≡ U, a value transmute does not run T's destructor (zerocopy's transmute! documents that the source 'will not be dropped') and U's destructor may later run on the bytes; through a mutable-reference cast a value written at U may later be dropped at T and vice versa; and reinterpreting between types that differ in Send or Sync can break thread-safety guarantees. None of this is captured here.

#### R8-im

- Bit validity only; aliasing rules are not modelled. zerocopy's try_transmute_ref! requires both sides to be free of interior mutability, so it never relies on this case.
- The write flags are per side and cover the whole region; they do not track which bytes lie inside an `UnsafeCell`. In Rust, `&(UnsafeCell<u8>, u8) → &(u8, UnsafeCell<u8>)` has equal validities and interior mutability on both sides, yet the destination may mutate a byte that the source type does not mark as interior-mutable; nothing here says such a cast is sound.
- Validity equality says nothing about whether two interior-mutable types use compatible synchronization or borrow-tracking protocols (for example an atomic integer versus `Cell<u8>`, or the borrow flag of a `RefCell`). rustc's transmutability checker rejects even `&UnsafeCell<u8> → &UnsafeCell<u8>` (its UI test comment: 'the two types may use different, incompatible synchronization strategies'), and zerocopy's transmute_ref! requires both sides to be free of interior mutability.
- The check happens exactly once, when the cast is made; later contents are not re-checked. Designs that re-check on every read or on every store are different disciplines, not modelled.
- Concurrent modification of the bytes between the check and later use is not modelled: runs are sequential interleavings and the check is atomic with the cast. Because both references stay live under interior mutability, a real implementation must also exclude source-side writes that race with the check itself (a time-of-check-to-time-of-use hazard); nothing here addresses that.
- Soundness of the successful path only: the check costs run time and can fail; what happens on failure is not modelled.
- Bytes here are always initialised, so the check can always read the source bytes. With uninitialised or padding bytes, performing the run-time check at U means reading the source referent's bytes, so the source must consist of initialised bytes only (zerocopy's checked casts require Src: IntoBytes for this). The characterization does not remove that requirement.
- The check is on bit validity only; library safety invariants of U need their own checks.

### Attractive stronger conclusions that are not established

- That a cast satisfying the condition of R1-R4 or R8 is sound in Rust: alignment, size relations, provenance, uninitialised and padding bytes, aliasing rules, destructors, auto traits and safety invariants all add conditions not stated here.
- That value and shared casts have the same requirements in Rust (they coincide in the model, R5-hier; this neither establishes nor refutes that they coincide in Rust).
- That `MutSound T U ↔ MutSound U T` under `Satisfiable T` alone (false: `mutSound_not_iff_symm_of_satisfiable_left`).
- That source-side interior mutability is harmless in Rust (R4-src is about bit validity only), or harmless for checked casts (false: R8-im).
- That checked casts compose (not stated); that three simultaneously live views behave like a chain of two-view casts (not modelled).
- That a cast from an uninhabited type is usable because it is vacuously sound (the Rust Reference requires references to point to valid values; see the real-system qualifiers).

### Escape hatches

The one impossibility result, R3-imp (no unchecked mutable cast from a satisfiable `T` to a `U` with different validity is sound), is defeated by each of: checking validity at `U` once at cast time (R8-mut; `checkedSound_mut_escapes_impossibility`: byte → bool); weakening the cast kind to a value, shared, or source-only-writes shared cast (`not_mutSound_positive_control_weaker_casts`); an uninhabited source (`not_mutSound_needs_satisfiable`). Outside the model, restricting which values the cast reference may write, never reading through the original owner again, or re-checking on every read or store (as Java arrays do on stores) would also defeat it; none of these is modelled.

### Tightness `unknown`

None. Every hypothesis and every right-hand-side component listed as `tight` has a proved counterexample in canonical form (all other components hold and the conclusion fails); the only `harmless` entries are the "no hypotheses" placeholders of unconditional statements and equivalences.

### Disproved and dropped statements

No statement of this package was found false or left unproved: all 29 main theorems are proved, with unchanged statements. The following tempting forms are false and are disproved in Lean (they are recorded so they are not re-derived):

- "Mutable-reference cast sound iff `T ≡ U`" without a satisfiability hypothesis: refuted by never → byte (`mutSound_eq_needs_satisfiable`, `mutSound_rhs_needs_satisfiable_guard`).
- "Shared casts in which either side may write need `T ≡ U`": refuted by bool → byte with only source-side writes (`sharedIMSound_eq_needs_dstWrites`).
- "A checked mutable cast is sound iff `U ⊆ T`", or with the guard weakened to satisfiability of `T` and `U` separately: refuted by zero-only → two-only (`checkedSound_mut_rhs_needs_satisfiable_meet_guard`).
- "Source-side writes do not matter for checked interior-mutable casts": refuted by byte → bool with both flags (`checkedSound_sharedIM_needs_srcWrites_includes`).
- "A checked interior-mutable cast whose meet is satisfiable needs `T ⊆ U` (respectively `U ⊆ T`) whichever side writes": refuted by byte → bool with only destination-side writes (`checkedSound_sharedIM_rhs_needs_srcWrites_guard`) and by bool → byte with only source-side writes (`checkedSound_sharedIM_rhs_needs_dstWrites_guard`).
- "Mutable soundness is symmetric under `Satisfiable T`" as a biconditional: refuted by `(byte, never)` (`mutSound_not_iff_symm_of_satisfiable_left`).
- "A mutable cast out of a meet is characterized under satisfiability of `T` and of `U` separately": refuted by zero-only and two-only (`mutSound_from_meet_needs_joint_satisfiable`).

### Not examined

Size-changing reference casts (prefix casts, sub-slices) with coupled cross-byte invariants; per-byte interior mutability; re-checking disciplines; composition of checked casts; mixed-kind chains; reborrowing chains with more than two views and two-phase borrows; partial writes; unions as joins; uninitialised bytes, padding and provenance; concurrency.

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (the commit the `v4.34.1` tag points to on GitHub, and the commit reported by `lean --version` of the toolchain used). Observed 2026-11-20.

Axiom audit (`lean/support/Audit.lean`; the per-declaration axiom lists are in `audit/axioms.json`): 316 declarations in the `ToyTransmute` modules; every one depends only on axioms in {`propext`, `Classical.choice`, `Quot.sound`}; in fact none uses `Classical.choice` and none uses `sorryAx`. The sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`.

Statement hashes (copied from `audit/statements.json`): `statement sha256` is the SHA-256 of `toString (repr ci.type)` of the theorem's type; `closure sha256` is the SHA-256 of the newline-joined, sorted lines `name : repr type [:= repr value]` for every package constant reachable from that type (definition values included, theorem proofs excluded); `size` is the number of such constants. Changing a statement or any definition it depends on changes these hashes. The package program `lean/support/RevalidationAudit.lean` prints exactly these inputs (see Revalidation).

Main theorems:

| theorem | card | axioms | statement sha256 | closure sha256 (size) |
| --- | --- | --- | --- | --- |
| `valueSound_iff_includes` | R1 | `propext` | `0ecc3e02f7c2b865b6f65f3554f0fec7cfe128c59eeae22e19a0768ca02d7fd5` | `39ed16ba270a9d8f9a869ed787f63e04dd1020be211976e6788a60f90a32acbe` (25) |
| `sharedSound_iff_includes` | R2 | `propext` | `9f3bb8a97b105d5622bdbe2c48979a30d8a7bceee2e7ed4f69dd149140d64afa` | `89d30311606cfa939e11203824972b06e062d2b053041883bf814e9519b79378` (25) |
| `mutSound_iff_includes_and_satisfiable_imp_includes_rev` | R3 | `Quot.sound`, `propext` | `b558dac72952e46c2d0bea7ac353e4d3819e29d5d589c33d81bf4c9ebd5f759e` | `acaf543265400fb2c446a3b33890cd5a6d239a4c69cc29dbf669fdf95f70e9f0` (26) |
| `mutSound_iff_validityEq_of_satisfiable` | R3-eq | `Quot.sound`, `propext` | `e9386db9b7bcd2987878038c505cedadd2534ea47f5c2a5cdbe2ed9b7bd1bf4c` | `450e5496d6dcc27afb2a8ffc2ffa6e8a5ce4462ae6ace7b3bac89c3bc5e9705f` (26) |
| `not_mutSound_of_satisfiable_of_not_validityEq` | R3-imp | `Quot.sound`, `propext` | `5514a9dcf338223264ad1ba8275d1e4ec34130413d89e02c66fb469d5349647a` | `450e5496d6dcc27afb2a8ffc2ffa6e8a5ce4462ae6ace7b3bac89c3bc5e9705f` (26) |
| `sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev` | R4 | `propext` | `2578bd25e372ae87935843fccf4abec28936a2a519d67fa08ce3ac89e14dc2d1` | `8bccd5aaec08e798be74f53daf8589b09aa7767c1e97819731c2f06fe4874720` (27) |
| `sharedIMSound_dstWrites_iff_validityEq_of_satisfiable` | R4-eq | `propext` | `9dae542c39555ed31abc7dda445d14dee143374b33d022004fed37f6210bcb0b` | `c9c2a973cf149afd7feb43ed296f8c2e535942a68421ee87f4c9b998b9717924` (27) |
| `sharedIMSound_noDstWrites_iff_includes` | R4-src | `propext` | `cd8042f85726c4c741843667e7ec16ada67a89307375839a9ca23f57480c1054` | `ca1de2d46f33afa6ba5c13766345634d3ff9f6da8f5a611ff596482310cb3557` (26) |
| `mutSound_iff_sharedIMSound_dstWrites` | R4-mut | `Quot.sound`, `propext` | `69875a46be367c0eb905b974b98ab396c753a0547471af47025481453b5f6413` | `855a26592433dd84a86d8b7b13da58bcd9baa7afad308562f86bfa4bc7a5b9cb` (28) |
| `valueSound_trans` | R5-trans | `propext` | `5892f9df14abdc01aff0f7c7f448bf20965f6649894ad52ea8b32b5c7f47e5ba` | `aa9872928055eac42cbfa19f73214a23308e30e2cd78cd0f12473e547a4ddbe1` (24) |
| `sharedSound_trans` | R5-trans | `propext` | `1368169a212f0ae38afc020106ef8a43fc0ce5afaaf3dc55bfde51908f1db636` | `7b3816b4e9b458db30e98cab47ffa34df6e84a57b8508914c4e3970f878feaa2` (24) |
| `mutSound_trans` | R5-trans | `Quot.sound`, `propext` | `6d32d1106be9dbf7109a99992269f57047b2114be0cbfa3108835d018c2372bf` | `4bd61699a2cbebc6c7a5f771f6c51e833fe698234c6061f04af9d6c4e573d620` (24) |
| `sharedIMSound_trans` | R5-trans | `propext` | `b5a9f6efb08c463d15a02a1ce57f91754db86decbcb63d3bd2726b796a053d7e` | `c66f27a0f53353cdc441bcb2def413947076ccc2aede0e2dcc03ffc57b118f4d` (25) |
| `valueSound_of_sharedSound` | R5-hier | `propext` | `9e87258410355ca618628c989c9f6e50c05e8a4f6a8ed362d53b6338a65e4a0c` | `003104975ddddd288b41482b7666a60ef35d4c7d71408cee027361212e2c8c8b` (27) |
| `sharedSound_of_valueSound` | R5-hier | `propext` | `e4986812747e978f620df715343b375de315478551421bfc6d07b37239bd5160` | `003104975ddddd288b41482b7666a60ef35d4c7d71408cee027361212e2c8c8b` (27) |
| `sharedSound_of_mutSound` | R5-hier | `Quot.sound`, `propext` | `c42bc904566724c5a4ba31fd38704ad4116d5f365b98c953179203409b214613` | `b5edd5f1b2a2d56ba2161cac2dc48de03a6fc6bdb812c140ab746f5856a8f24b` (27) |
| `mutSound_symm_of_satisfiable` | R5-symm | `Quot.sound`, `propext` | `230f324af41c09a9b446b32a1435ea9f319749ec90ea4d925371c467fc954480` | `c6307d934d54744641068a5bea467143830e9efb88f4a8dac53ff7e28a6c4d7c` (25) |
| `sharedSound_to_join_left` | R7-shared-lattice | `propext` | `aecb0623a4cc709710004467286faf62236d4867037b7318e4e1ba256156c889` | `35bd9632212475d298a1610be7444915210a29273f05d6de2d2bb07ef15ac7d1` (25) |
| `sharedSound_to_join_right` | R7-shared-lattice | `propext` | `ad87a4cfcffe56b9331416396cf7cc38bdc02a2392a7b8994f63c3d83f03fa25` | `35bd9632212475d298a1610be7444915210a29273f05d6de2d2bb07ef15ac7d1` (25) |
| `sharedSound_from_meet_left` | R7-shared-lattice | `propext` | `bcbca9ad95efac059cc7e10e1dfcf6e270fb25d7ade3d9060f532780c0ec74be` | `70a9d88646c436793b539fb4196f2f087fd02851ada9c8c46aa112f33609fca0` (25) |
| `sharedSound_from_meet_right` | R7-shared-lattice | `propext` | `c48dc4086007c94ce7c3e8afabb9cb408d31d1afe3ff543f6bba048a1c59f515` | `70a9d88646c436793b539fb4196f2f087fd02851ada9c8c46aa112f33609fca0` (25) |
| `sharedSound_join_iff` | R7-shared-lattice | `propext` | `fdcbeb915423ebbe39a9959ae9e1684e4e145e643dd5621baf50b00f8c50840f` | `35bd9632212475d298a1610be7444915210a29273f05d6de2d2bb07ef15ac7d1` (25) |
| `sharedSound_meet_iff` | R7-shared-lattice | `propext` | `f396d1487f32c9941183e4198de1b66306f14f30d05bb445b31ecf3d6da771d8` | `70a9d88646c436793b539fb4196f2f087fd02851ada9c8c46aa112f33609fca0` (25) |
| `mutSound_to_join_left_iff_includes_rev_of_satisfiable` | R7-mut-join | `Quot.sound`, `propext` | `bed7c8ed5d9b37484fce05a333ebd6eff39ce3da8ab78936e5fe94b31a25b64c` | `1e9c409ad5059e3a0987110eab8fa444202b57b4ab1e3670a269e0a3297ff15d` (27) |
| `mutSound_from_meet_left_iff_includes_of_satisfiable_meet` | R7-mut-meet | `Quot.sound`, `propext` | `dd487e1f5b8e0b8d7adf761452a76f12e13b27292afcdc2ea81481c279a9386d` | `db5aba04ae434324a78caccfdc80ebeaaa73f72685980327169065ab2ab7171d` (27) |
| `checkedSound_valueProtocol` | R8-value-shared | `propext` | `cd121ad2973c63dbd217c42e2445c4057c47c7ca9590a89ffceb3475a7104c3a` | `701dfa795d1a0e43549a70391f336b6cbc96cb24d27d6dcee53784bcbcc77160` (23) |
| `checkedSound_sharedProtocol` | R8-value-shared | `propext` | `51b534ddebb96570146b7d52218b24b1a88d3aef5bdcfec0e0f37b5fa9cca947` | `7aac799046a8e6b18bddbffd7a1c158024b08930dc5f06d09b037dff6251a3d6` (23) |
| `checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev` | R8-mut | `propext` | `f3a70810bf5ec631380079b325d5343c1755bfd19ac0c3519fac516c896426bd` | `d29276313e75ec3dc99535c2378ea537f31531890fe214a3f085c1ceca299633` (26) |
| `checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev` | R8-im | `propext` | `400adbd776d2a7b052ca254988eb87fa886b5decb855f70191b4e3cd9c23a340` | `a00df1e3ea31b8847bad294166a7bfc970fca26c82c5f67acb759f8e93785f0a` (27) |

Counterexamples, witnesses and controls named by the cards (each also carries `Basis: execution (Lean kernel check)`):

| theorem | axioms | statement sha256 | closure sha256 (size) |
| --- | --- | --- | --- |
| `boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes` | `propext` | `cdc9bac7c8fcf5da12b5e710212a038d198ace2765a69a12f150da7f0c47148d` | `69f2a35eb42c213d6efd8a7361d03cff7c0d1c167cbdb4c8be36955435f20bfc` (32) |
| `boolV_to_byteV_mut_violating_run` | `propext` | `636baafd746a0c098d90a68679591de1743f794f9087b16a635311db8a783c65` | `4b726078e7ace860ae1d4dbccdba5f598a1ade5c690d9a4a0b5a855a9911f6b8` (28) |
| `boolV_to_byteV_value_and_shared_sound` | `propext` | `7f475a1dde2cba45bea2618ff3d257bf9232798c771d0247f5c95cf4319db52b` | `a8351b4620851ad5aafd6b4b6f91a39c14570046995ee1fb8a955da82820b3bd` (32) |
| `byteV_to_boolV_unsound_even_by_value` | `Quot.sound`, `propext` | `29d0503a9858f2d8a861d25656b2f818e8cefd14193fb19bab46f3d3536139f5` | `ac9a6d6cb1b8fc6fa6ebe1964d1488332cf95e989f34d5162aa7d25bc2e5b473` (35) |
| `checkedSound_mut_escapes_impossibility` | `Quot.sound`, `propext` | `666b0c2fbc9813dd407ed27dd4d2d37a7375d2c1996f6540e113b19878b92271` | `fa1f78bcaf457747e897a9e3df1467dc7bab3b2561a8af0821ff60bced0ceebd` (31) |
| `checkedSound_mut_needs_includes_rev` | `propext` | `67f3643746b445df65f4bedcefb52d890a0009fa9ec1f318e1afe6b0328f07b6` | `048004635b0b689743cf426d13022959d264cafc38bb3eddf89e28acfad23616` (30) |
| `checkedSound_mut_nonvacuous` | `propext` | `be9d4126d4fc613fa1447cc1dc7b550dfc98827b6c6177041b574f5ceb9c17bc` | `048004635b0b689743cf426d13022959d264cafc38bb3eddf89e28acfad23616` (30) |
| `checkedSound_mut_rhs_needs_satisfiable_meet_guard` | `propext` | `f73880c0eefe9dfd0884f5208528dd0266e7883f30e37c13269eb8bc05b5223a` | `73c83c62457c18346d837246902dc054881de47b7a73ffef6d4ba958b72c2caf` (30) |
| `checkedSound_sharedIM_needs_dstWrites_includes_rev` | `propext` | `22ec66ccb30d29da285fdcf1f49507c4d0b88173636614df54be923ec05df4e1` | `b8a0d0d81f950419f56d86e5494e63e99da06bf7ac3e261acc597b2ce8a0af9b` (31) |
| `checkedSound_sharedIM_needs_srcWrites_includes` | `propext` | `de22e5e734786990e8b2a7d397c18ef795a3699a4d2a0c5190c62581f2eca1b3` | `b8a0d0d81f950419f56d86e5494e63e99da06bf7ac3e261acc597b2ce8a0af9b` (31) |
| `checkedSound_sharedIM_nonvacuous` | `Quot.sound`, `propext` | `3df9b39155857677e257c9bc925586c1882dfb8c125bc8df30c44898e261d904` | `56597aa6b73ae335167598e538bef7c803cd246ec8bcb79b4cedba4563b7ef5d` (32) |
| `checkedSound_sharedIM_rhs_needs_dstWrites_guard` | `propext` | `782249652b9297e93a864be1dc957b797248e73fe3205d9a6076b7ed0178d728` | `b8a0d0d81f950419f56d86e5494e63e99da06bf7ac3e261acc597b2ce8a0af9b` (31) |
| `checkedSound_sharedIM_rhs_needs_satisfiable_meet_guard` | `propext` | `71662e6d192cb333d56ecf6c77148a7477cf4c3a6669a326996eb125e788ba49` | `2740667fae57de7db235e391c679dd678664d0de782b449789ab40a5e139f34d` (31) |
| `checkedSound_sharedIM_rhs_needs_srcWrites_guard` | `propext` | `665ae7d3520a88b8f37e8346147e93c34e6f9da7f3a2146583fe93982ff8f76b` | `b8a0d0d81f950419f56d86e5494e63e99da06bf7ac3e261acc597b2ce8a0af9b` (31) |
| `checkedSound_sharedProtocol_nonvacuous` | `propext` | `36c2e224f6d932d5e43c08fe7a42bdcf9e110f26d7096e4e513e168d3a79bd82` | `f392a3b7fc746753d3c2a1129fac271b2c2d0a2773e6cb05266bd9e19e7443fe` (31) |
| `checkedSound_valueProtocol_nonvacuous` | `propext` | `f16c728fbb646b32e18c823baac2c96ad1b48cb3b3ea032f5ecc17be130f0a81` | `f6e07be2fe46cfdea6403cdb6d0d1f2857cbf4ffa6baccd297a3bc24a6c3a235` (31) |
| `mutSound_boolV_boolV'` | `Quot.sound`, `propext` | `aaf8a25579530670c8e7c6e47657ecf1c8588b54fb1395c4a37fa2e38faf2375` | `a68c72599fb77d172f47dd7f9cf2444f2090d0641b5b17c8ab525f091154f01d` (28) |
| `mutSound_eq_needs_satisfiable` | `propext` | `b9e50517db3ead1de29518e23c01be8964e4f7e33ac068cedadce83beb2995df` | `2ba9bdec6bb38e2531971d7e431aefd189bf28774829058ecc65048be66107c3` (28) |
| `mutSound_eq_nonvacuous` | `Quot.sound`, `propext` | `31a2ae375c149e3ffed504986fe1ccc01bee1bd1a998c497dab5d090523c904f` | `d7b0dc773bcc6119feed576219f0f2b464bd427ca5b94809868a9faa6a64ef63` (30) |
| `mutSound_exact_nonvacuous` | `Quot.sound`, `propext` | `6941b99fb59dedfe4773ed17fa9a421c8258970f5947e1be3a8efb001abc163b` | `a30fada57e40734a69ee8d368bc324cb09f3b59207633ed601a87da5468c6fed` (31) |
| `mutSound_from_meet_fails_example` | `propext` | `4c4d7ab56a393de9563f5f939c4166f017bd3978a022da933f1aa54d5ae7d857` | `3318ac68ea207c41d6f975cd002385d9d0fb22a73b98fd06aeffbe0252531f41` (31) |
| `mutSound_from_meet_needs_joint_satisfiable` | `propext` | `1545c2a7a2f5b7bf46db5c3fb5277c5dca0d7e6359cff676a1ea2d47a09ea1a8` | `8aea55bb82af920f42393abe36ff83b0d40874a84be3ca337ce3bd7418ca369f` (31) |
| `mutSound_from_meet_needs_satisfiable` | `propext` | `bf039dad6dbd338640cfa36275129171cc8820dfaf5a1f0bb828478f1012ae76` | `9ecc87200315755fca06332b05c11684e772937560d021197968de3151e9c718` (29) |
| `mutSound_from_meet_nonvacuous` | `propext` | `c3b8ae421539067c4625cc74dca04dc72f6f19db1b4b130758b84ca4636398d0` | `fd5c456ee21752d40d949ddb65b545b17b5f11a2d0f6913fdfbc50f572f6cdb6` (32) |
| `mutSound_iff_sharedIM_needs_dstWrites` | `propext` | `6b0ae6da4618cbdf7cf4b1aadbc44f5b54915e00c35cf37ea0c93d49b3a87f06` | `8b57bc39f097f59594fef227a4b5f3216e9ab0440221847107f8fb57adb29a05` (32) |
| `mutSound_iff_sharedIM_nonvacuous` | `Quot.sound`, `propext` | `a711269315835b1908ef237347b77ca49adb55110a1b485f6b49be72eafbcfc3` | `49afbf4f10768e6b73d595fa66dbc7c3cf02c8bd52d19088d7c67ae6de36007a` (32) |
| `mutSound_needs_includes_rev` | `propext` | `7f4a59d335cd9b836b1603ac29362f092fc0a5ee49e555a2cc019e5d4246f249` | `b6bdc8ddb563be8c0cd415a5ada3e257635f2173b47e6d25b7f1d2affaf2878c` (30) |
| `mutSound_rhs_needs_satisfiable_guard` | `propext` | `0a1ac8511d23ac9bf76c9a4b0c75e39438d428776985089dbe3934e838289724` | `5f935770e0c51ab5a42cde8f1353fe80b5c9be5df7fbacea9f69aee0f0ca51a4` (28) |
| `mutSound_symm_needs_mutSound` | `Quot.sound`, `propext` | `623f85b1c1d9f694249c107f6ed70831fc1a5cccf034e7ea35bd887310dccea4` | `884975d0d856bdd3c47ad3916819971f0470f3d8e418f826f06eea8c6e732e6f` (29) |
| `mutSound_symm_needs_satisfiable` | `Quot.sound`, `propext` | `ec62ecaf81f62fe9856c8caaffb5a88037676bf16d9d27f0d4f4c1de8ce41100` | `00b38f700f8b3dab7b1b05f662a8aa5c35c675fe00d4b7eca1d16e4fdfcc7abb` (27) |
| `mutSound_symm_nonvacuous` | `Quot.sound`, `propext` | `f5cfa609a0639a59d65827981c09799f99847729ab80d061e8c6829e0785caec` | `36ac454a7b5eec88663718afcedb01807ab1fbb3d017034b1c44544c70d99c9c` (29) |
| `mutSound_to_join_needs_includes_rev` | `propext` | `022bb9ddca14b7614162ed0f5ab02087fc50b631cdb663947e9af4f792cac6f3` | `7800909411d9ff3d6ee0820cc1d4072daacc3a158f70be7393b3402fc97ec5fe` (31) |
| `mutSound_to_join_needs_satisfiable` | `propext` | `ceb71fe9350f9e6553e0571667404027888daba3e464a0ffa67bea18a539d8f8` | `361bb7d73d091ce3a69a4e09db811979c97b3245e7c83e408ba349f698ad197d` (29) |
| `mutSound_to_join_nonvacuous` | `propext` | `c518851441936a0bc3841b5c3231f89e00bc48d8cfd2943e6b942941b238f304` | `3274e818883fcb0d0bfa69375513c3e91c2237d7c368933c78ef15ef51a50972` (31) |
| `mutSound_trans_needs_first` | `Quot.sound`, `propext` | `90eabebadd1aa4405c92b8adf24606e396169a7d6b536d32e4863dd56a0525bd` | `dda29a32c6fe1365e8cffe8451986425719103796a4bd4ea10b5dcacc1587b6a` (28) |
| `mutSound_trans_needs_second` | `Quot.sound`, `propext` | `110be2b23f182a96c3de37d6a118ea19ca0b921583e1a85f63fb18539d48c0c8` | `dda29a32c6fe1365e8cffe8451986425719103796a4bd4ea10b5dcacc1587b6a` (28) |
| `mutSound_trans_nonvacuous` | `Quot.sound`, `propext` | `fcddf1330b056261e4ba71a092fb1fd711e554ca8d53455221d4e95ae3151321` | `566c9c224ebdff7cb5a2ee2ecd860d0266800df8cd8caca591c63f7277fa26f4` (30) |
| `mutSound_trans_uninhabited_nonvacuous` | `Quot.sound`, `propext` | `297e411bba6ad6eeb1ff3ae2663b3c64f91234eed63136ef8af1b24c940fb5ae` | `be772b41d6e00d0c8ae33e07159e6f77f77d2b3c97dd962e71cf31035e087970` (31) |
| `not_mutSound_needs_not_validityEq` | `Quot.sound`, `propext` | `8a602da29f0af7fffc990527ccb1d082dd2182919e4b3f02b59b1c6c1eb531fc` | `d7b0dc773bcc6119feed576219f0f2b464bd427ca5b94809868a9faa6a64ef63` (30) |
| `not_mutSound_needs_satisfiable` | `propext` | `884eee943b0994b708e7062b752149ff4f05bdd1ea2dd3e66391f4791f0b3cd0` | `2ba9bdec6bb38e2531971d7e431aefd189bf28774829058ecc65048be66107c3` (28) |
| `not_mutSound_nonvacuous` | `propext` | `3530b274224e35858ceb80f35c83389242a1748b0980af962f5b9492c43b1302` | `7e1a556571b45bd5e187db6e1e25ddca8aec048ec9ba492cdfb3df930c612ff1` (30) |
| `not_mutSound_positive_control_weaker_casts` | `propext` | `65b67c5a4ac5cf94f4a8ffb8492ff193c139280cee9c58f4260be7ed8b4d7f1c` | `8e4226ffa15df1800fc8db8003c7b3f364594d41b16a31eb8373ce1f9b9a535d` (37) |
| `not_sharedSound_byteV_boolV` | `propext` | `020009b66ba8f185100dc1fa357f851db8b15919d82271a8b3b8a4648d7b9478` | `7b9db16168d24a34dcba0d3c3c924ff161ac08ac5d2522ad80dfd780edc1ca48` (28) |
| `not_valueSound_byteV_boolV` | `propext` | `c82f443c19f87c0c4f82e3d4d6e154a0e4da3d7bbb6752ba6c77e70825a45a7b` | `af4e36fcd35a65e0e00b0a7d478024e405fe6212057604d653005d655d60cbff` (28) |
| `sharedIMSound_eq_needs_dstWrites` | `propext` | `09af8c8dc1bd73e43eaf5cfb808b0ee2cf7585852e10b547b5cdc676dbb99554` | `155827f8e0d94547bba5a64185e77f434363bc96bb2a1a8d784025222f70243f` (31) |
| `sharedIMSound_eq_needs_satisfiable` | `propext` | `98f22932aa83f40c71c15e5207f86a911ffbc0a9cbcad95ea2e617a648c0f405` | `2262424bae698b232556feb7120739cb5b379e0e651a12a9583087bd6a9e4188` (29) |
| `sharedIMSound_eq_nonvacuous` | `Quot.sound`, `propext` | `f9a2f1d5cf2692a73ffab66b508e54c51925ef29bdcfdfb874b976dc35552172` | `aa0533907222466e19aeebea164707dfe37c90b23afa8beb7e52b1a59f164de4` (31) |
| `sharedIMSound_exact_nonvacuous` | `Quot.sound`, `propext` | `2f6d49be2d6eaf7cb60a2cf82e05a5c9d91cdc2019c21acf081ffc6c08d712c6` | `28b2cb04fcb3f32d82ea55f2a564f7b56193dd4c053b00a52ea25d648ecd77ab` (32) |
| `sharedIMSound_needs_includes` | `propext` | `594066fd35fea343baddd4a4df78d5cee7c8904d9fabc9f97da4c138ba5cbb27` | `aa0a2fd1a263803503674ad61f3795433d14175b4e3aab4e6a6cd0803c45de3a` (30) |
| `sharedIMSound_needs_includes_canonical` | `propext` | `6f7be7df2d5a10eb104cdbc3774fc4ca11a8f7da3069d9eed129a49dd76264d8` | `a6394e84c2205f03ac67751bb974238e81facb7328ec8e0af05d78f10c577f3e` (31) |
| `sharedIMSound_needs_includes_rev_canonical` | `propext` | `d5757d0b7c258ce0ff88f801a730ac1875ff3a3e6c19c82c00d278658271a0be` | `a6394e84c2205f03ac67751bb974238e81facb7328ec8e0af05d78f10c577f3e` (31) |
| `sharedIMSound_noDst_needs_noDstWrites` | `propext` | `39be4f38490545db0882a2c5295e892dde20fee4cbb5911371dcdb8e7b782784` | `aa0a2fd1a263803503674ad61f3795433d14175b4e3aab4e6a6cd0803c45de3a` (30) |
| `sharedIMSound_noDst_nonvacuous` | `propext` | `a548435588ea24e9ecdc8edd1d734c9dc2786da08fb8ddecb02e66776fd9b871` | `aa0a2fd1a263803503674ad61f3795433d14175b4e3aab4e6a6cd0803c45de3a` (30) |
| `sharedIMSound_noDst_trans_strict_nonvacuous` | `propext` | `17b1f5f80c1c97c05e15194a10132e57673e249d48bf255c82dc13d41aebfdd2` | `1ae3229ea60293b05ad0ff522d25ab70f3ebbcbc1a6278e68f459c70c86f0ab3` (31) |
| `sharedIMSound_rhs_needs_dstWrites_guard` | `propext` | `dfed9dcdfef59614550078d2cb95e916c7e2424a0273d68fcc23628bf5a0d34e` | `a6394e84c2205f03ac67751bb974238e81facb7328ec8e0af05d78f10c577f3e` (31) |
| `sharedIMSound_rhs_needs_satisfiable_guard` | `propext` | `0f826238dd758473d69d68a2b1ae6356bec6f8c78ffcd1bdf57d4415174a2bcb` | `2beb48e4ae9ecdfb96aa14b39922b0c7bec6fdc098f1783ef94849ca37f5b7f2` (29) |
| `sharedIMSound_trans_needs_first` | `propext` | `46b114e8ef636afb42c6c6925ea3c8c1adaaf31cba67abb1773985c7e992cd96` | `5281af42ca66467dc4e8806672fdc9b2440087eda38ef3b1c12bd74e06555649` (29) |
| `sharedIMSound_trans_needs_second` | `propext` | `c565107d36fe3d8f9111fafbca5e6e4529234e12ed499762ad74d53f9ef053a7` | `5281af42ca66467dc4e8806672fdc9b2440087eda38ef3b1c12bd74e06555649` (29) |
| `sharedIMSound_trans_nonvacuous` | `Quot.sound`, `propext` | `b7206af6e8888e81fee005ac931618fcd5b24a33d2ecd059b17d8d85c2ac0d9f` | `cc9dd18370e76f8f56d3509c870621253be8ee7c4fad6a34c5cc8d862f9ddcf4` (31) |
| `sharedIMSound_trans_uninhabited_nonvacuous` | `Quot.sound`, `propext` | `1875024a182534725c5dd1104850937b030fc53471d608efdd21b0a5952178db` | `86af1c71652b4a8bdb71c3d32da3aa87497fd426f1ba6061d7516fa396f7d9c6` (32) |
| `sharedSound_boolV_byteV` | `propext` | `7f55e9d96f7ee3c849133c92ff6d6fb1425516db8c6de977c22bbf8366b1fa64` | `7b9db16168d24a34dcba0d3c3c924ff161ac08ac5d2522ad80dfd780edc1ca48` (28) |
| `sharedSound_from_meet_left_nonvacuous` | `propext` | `4f8b2ad9f62186f5e096e9bcd85a30f16c6ac2c84a345c9fe8b397e38e46d547` | `958467c618fcf69be59fb4e118d750b45570c077947513ad0a4f263ebb2038b9` (30) |
| `sharedSound_from_meet_right_nonvacuous` | `propext` | `2ccdca8fa6d674a9d4a3eda70bf96217635bbfc06ae2257025f34906368416e9` | `958467c618fcf69be59fb4e118d750b45570c077947513ad0a4f263ebb2038b9` (30) |
| `sharedSound_iff_includes_nonvacuous` | `propext` | `37d2232747bb5ba47b4f0916cc2a6e0efff110a78a794e1baa9411903b65105d` | `7a233629a0ce5a1c7fe4e36fd0c035d796a54f4c01fb9653508d7a063c1cf7c4` (29) |
| `sharedSound_join_iff_needs_left` | `propext` | `2008dfdcb5f160856d906c3ca5a4451553908d7b93fba74304bf75a272e32d6a` | `60659b31dd57732a7bb2e622ee2ffc85238ec9885ba0a63c2a071a911068ba50` (29) |
| `sharedSound_join_iff_needs_right` | `propext` | `cd41ae30200e89aa3d29f8f74d8e393f7d261b3de66142d89204236e01d65f02` | `60659b31dd57732a7bb2e622ee2ffc85238ec9885ba0a63c2a071a911068ba50` (29) |
| `sharedSound_join_iff_nonvacuous` | `propext` | `64d42281ae816d11913bff01d00169e7cd85d02b361b4aebf83b92055b53b315` | `56bc6c5e634bc2940b33551566c94118d4942e6176c6195a653d29fbe3325d6c` (30) |
| `sharedSound_meet_iff_needs_left` | `propext` | `d849fdbb704f2d4cdeb35638c970df417588c89353d28cc8df2c5e74594608b1` | `8237c3c77f0a3820019bc7f62b7e939f744e18d91b34de6d6d9f97f857da0244` (30) |
| `sharedSound_meet_iff_needs_right` | `propext` | `eae1554db054485bcfd76904c43727a74b94aae730d42ca2d44b1943070820c1` | `8237c3c77f0a3820019bc7f62b7e939f744e18d91b34de6d6d9f97f857da0244` (30) |
| `sharedSound_meet_iff_nonvacuous` | `propext` | `d8ada44c9f685e2c8c87be3eaa64f9c4e8bacaeac6fb396db90c160b6de62b3a` | `023c5dd555b43b7afdd87b249810734d4a83d5d45cc928a8fd40f48077e8c044` (33) |
| `sharedSound_to_join_left_nonvacuous` | `propext` | `df67ec05834da898d42b60ce5d1a4fb80490a46e3f7cdf9584f0ddf63e760e0e` | `0a8f56cdf357cd01766f01bc6830fbb450527bec4e1c2649fa51f81b97b7ad45` (30) |
| `sharedSound_to_join_right_nonvacuous` | `propext` | `afca034559254da335ec789b1492e60b78af886656e5a548a9626f2f0a3b6d2d` | `0a8f56cdf357cd01766f01bc6830fbb450527bec4e1c2649fa51f81b97b7ad45` (30) |
| `sharedSound_trans_needs_first` | `propext` | `90f55c1d6d890833f6290415440d953554649e4a00d3e88bd1311070b5ff5225` | `7b9db16168d24a34dcba0d3c3c924ff161ac08ac5d2522ad80dfd780edc1ca48` (28) |
| `sharedSound_trans_needs_second` | `propext` | `b5449bc3895240cc824407178191f3f0966091a4231558b489ccbd43daf9e7b4` | `7b9db16168d24a34dcba0d3c3c924ff161ac08ac5d2522ad80dfd780edc1ca48` (28) |
| `sharedSound_trans_nonvacuous` | `propext` | `46810c4830c10c103ee26f45f159c3643b193c9d04b7a7c26c3199e62aa97f14` | `75115e51a0b5c8d1dbc7aabbf4d98399519f28417b58b723eb78d9ead9aa7ffa` (29) |
| `valueSound_boolV_byteV` | `propext` | `6bda92740ddaddacb052b7c79e6ccc5953225c8d48572daea6663aca01134033` | `af4e36fcd35a65e0e00b0a7d478024e405fe6212057604d653005d655d60cbff` (28) |
| `valueSound_iff_includes_nonvacuous` | `propext` | `725b3e6f9e49ea647d9b34078d869a7389f8633d968c253b14c6c99c7c1a53b8` | `e594456521961c853842e5b7423375c63f5391bdf18482e35f0e253e3292f49a` (29) |
| `valueSound_trans_needs_first` | `propext` | `00b42c5d607bc01348baa569246d92766c6a9249f72c799dfc806bd9ac008a00` | `af4e36fcd35a65e0e00b0a7d478024e405fe6212057604d653005d655d60cbff` (28) |
| `valueSound_trans_needs_second` | `propext` | `13ee731648f38fc5368ab5ab202a3ffe373dd425eadf451ce2d2b021c311e9df` | `af4e36fcd35a65e0e00b0a7d478024e405fe6212057604d653005d655d60cbff` (28) |
| `valueSound_trans_nonvacuous` | `propext` | `6d36c120f8b4154bedf6246ae8ee78cff1984d4adb34ae28341d28a39f1fb732` | `5b5cd6a71c84bd697be68f9c0dca1edd760776ab723a044aa8988f08e12661e0` (29) |

Related witnesses not hashed above (fully proved; axioms): `checkedSound_mut_byteV_boolV` (`propext`); `mutSound_not_iff_symm_of_satisfiable_left` (`Quot.sound`, `propext`); `mutSound_to_join_fails_example` (`propext`); `noInvalidRead_unchecked_until_read` (`propext`); `sharedSound_not_imp_mutSound` (`propext`).

### Primary sources

Checked at the source on 2026-11-20 (repository commits, specification pages, publisher or Crossref records). Keys are those used in the cards.

- **[MCP411]** Rust compiler-team major change proposal 411, 'Lang Item for Transmutability', https://github.com/rust-lang/compiler-team/issues/411 (opened 2021-03-04, accepted), section 'When is a bit-reinterpretation cast sound?': 'A transmutation is well-defined if any possible values of type Src are a valid instance of Dst.' Informal statement of the value-transmute condition.
- **[WRENN]** J. Wrenn. 'Safety Goggles for Alchemists: The Path Towards Safer Transmute', blog post, 2024-09-30, https://jack.wrenn.fyi/blog/safety-goggles-for-alchemists/, section 'Theory of Alchemy': 'A type, Src, is transmutable into a type, Dst, if every possible value of Src is a valid value of Dst.'
- **[REF_UB]** The Rust Reference, 'Behavior considered undefined', https://doc.rust-lang.org/reference/behavior-considered-undefined.html (read 2026-11-20; the quoted rules were verified verbatim in the source file src/behavior-considered-undefined.md of rust-lang/reference at commit e24eecf97b0c9a6dbac67191098204dc8a190aaa, the Reference revision of the Rust 1.100.0 release, the latest stable release on that date): rule [undefined.invalid] 'Producing an invalid value.'; rule [undefined.validity.def] 'The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB.'; rule [undefined.validity.bool] 'A bool value must be false (0) or true (1).'; rule [undefined.validity.reference-box] 'A reference or Box<T> must be aligned and non-null, it cannot be dangling, and it must point to a valid value', followed by the note that 'the last point (about pointing to a valid value) remains a subject of some debate.' Normative basis for modelling a read of invalid bytes as undefined behaviour and for the bool fixture.
- **[MINIRUST]** MiniRust (github.com/minirust/minirust, branch master at commit 063d784186d3252bee242217f218223205c0b568), file spec/lang/representation.md, section 'MiniRust representation relation': '`decode` converts a list of bytes into a (potentially not well-formed) value; this operation can fail if the byte list is not a valid representation for the given type.' Section 'Transmutation': a transmute whose bytes do not decode raises UB ('transmuted value is not valid at new type'). Abstract bytes (spec/mem/interface.md, 'Abstract Bytes') are Uninit or Init(u8, optional provenance fragment). In this package, `Validity T` plays the role of 'decode at T succeeds' restricted to initialised, provenance-free bytes; MiniRust's richer bytes are not modelled. MiniRust was announced by R. Jung, 'Announcing: MiniRust', 2022-08-08, https://www.ralfj.de/blog/2022/08/08/minirust.html.
- **[ZEROCOPY]** zerocopy 0.8.63 documentation (crates.io release published 2026-10-13, crate checksum SHA-256 e5fe1f8f1b06191a00962174c61aa5005e0bb391a6d80d07e24d115c01a92ed8), https://docs.rs/zerocopy/0.8.63/zerocopy/ (read 2026-11-20). Macro transmute! behaves like `const fn transmute<Src, Dst>(src: Src) -> Dst where Src: IntoBytes, Dst: FromBytes, size_of::<Src>() == size_of::<Dst>()` (an `#![allow(shrink)]` form also permits shrinking), and 'the Src produced by the expression $e will not be dropped'. Macro transmute_ref! behaves like `fn transmute_ref<'src, 'dst, Src, Dst>(src: &'src Src) -> &'dst Dst where 'src: 'dst, Src: IntoBytes + Immutable + ?Sized, Dst: FromBytes + Immutable + ?Sized, align_of::<Src>() >= align_of::<Dst>(), size_compatible::<Src, Dst>()`. Macro transmute_mut! behaves like `const fn transmute_mut<'src, 'dst, Src, Dst>(src: &'src mut Src) -> &'dst mut Dst where 'src: 'dst, Src: FromBytes + IntoBytes + ?Sized, Dst: FromBytes + IntoBytes + ?Sized, align_of::<Src>() >= align_of::<Dst>(), size_compatible::<Src, Dst>()`. Checked forms: try_transmute! (`Src: IntoBytes, Dst: TryFromBytes, size_of::<Src>() == size_of::<Dst>()`), try_transmute_ref! (`Src: IntoBytes + Immutable + ?Sized, Dst: TryFromBytes + Immutable + ?Sized`, plus the alignment and size-compatibility bounds) and try_transmute_mut! (`Src: FromBytes + IntoBytes + ?Sized, Dst: TryFromBytes + IntoBytes + ?Sized`, plus the alignment and size-compatibility bounds; 'while the value of the referent is checked for validity at runtime, the size and alignment are checked at compile time'; its examples convert `&mut 0u8` to `Ok(&mut false)` and reject `&mut 2u8`). Trait summaries: FromBytes 'Types for which any bit pattern is valid.'; TryFromBytes 'Types for which some bit patterns are valid.'; IntoBytes 'Types that can be converted to an immutable slice of initialized bytes.'; Immutable 'Types which are free from interior mutability.' Relation to this package (derived): over bytes that may be uninitialised, Src: IntoBytes says every Src-valid byte sequence is initialised and Dst: FromBytes says every initialised byte sequence is Dst-valid, so together they give T ⊆ U by transitivity through the set of initialised byte sequences; requiring both traits on both sides (transmute_mut!) makes both validities equal to that set, a special case of T ≡ U. In this package bytes are always initialised, so that intermediate set is the all-bytes validity and Src: IntoBytes has no counterpart. try_transmute_mut! is an instance of a checked mutable cast (R8-mut): Src: FromBytes and Dst: IntoBytes give U ⊆ T, and the run-time check supplies validity at U for the initial contents. For try_transmute_mut!, the bound Src: IntoBytes makes the source referent's bytes initialised, so that the run-time check can read them; Src: FromBytes alone does not exclude padding bytes.
- **[TRANSMUTEFROM]** Unstable trait core::mem::TransmuteFrom, nightly documentation https://doc.rust-lang.org/nightly/core/mem/trait.TransmuteFrom.html (core 1.102.0-nightly, built from rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2 of 2026-11-19; read 2026-11-20; the quoted documentation comments were verified verbatim in library/core/src/mem/transmutability.rs at that commit; tracking issue rust-lang/rust#99571), declared as `pub unsafe trait TransmuteFrom<Src, const ASSUME: Assume = { Assume::NOTHING }> where Src: ?Sized`; it is implemented when 'the compiler has proved that the bits of a value of type Src can be soundly reinterpreted as a Self'. The companion struct core::mem::Assume (https://doc.rust-lang.org/nightly/core/mem/struct.Assume.html) has fields alignment, lifetimes, safety and validity; its documentation states two reference rules: with alignment false, 'TransmuteFrom is not implemented for transmutations that might violate the alignment requirements of references', and with lifetimes false, it 'is not implemented for transmutations that extend the lifetimes of references'. These pages do not state the mutable-reference (reverse validity) or interior-mutability rules. The trait was renamed from BikeshedIntrinsicFrom in rust-lang/rust pull request #129657 (merged 2024-08-28).
- **[UCG]** Rust Unsafe Code Guidelines, glossary entry 'Validity and safety invariant', https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#validity-and-safety-invariant (read 2026-11-20; verified in reference/src/glossary.md of rust-lang/unsafe-code-guidelines at commit d809f91e62968913d808e53397fbcf7cea762cce, the head of its master branch on that date): 'The validity invariant is an invariant that all data must uphold any time it is accessed or copied in a typed manner.' and 'The safety invariant is an invariant that safe code may assume all data to uphold.' The predicate `Validity` of this package models the former only.
- **[JUNG_BLOG]** R. Jung, 'Two Kinds of Invariants: Safety and Validity', blog post, 2018-08-22, https://www.ralfj.de/blog/2018/08/22/two-kinds-of-invariants.html. Distinguishes the validity invariant (modelled here) from the safety invariant (not modelled).
- **[RUSTBELT]** R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer. RustBelt: Securing the Foundations of the Rust Programming Language. Proc. ACM Program. Lang. 2(POPL), Article 66, pp. 1-34, January 2018. doi:10.1145/3158154. Its semantic model works by 'interpreting λRust types as predicates on values expressed in a rich program logic'; `Validity` here is a drastically simplified, logic-free analogue (types as predicates on byte sequences).
- **[RUSTC]** rustc source, rust-lang/rust commit 5b216e01a117532b30f061f3dff8a61408113c77, file compiler/rustc_transmute/src/maybe_transmutable/mod.rs: lines 92-93, comment 'mutable destination references also generate a reverse transmutability obligation for their referents'; lines 112-119: if the source layout is uninhabited the answer is Yes ('because instances of the `src` type do not exist'); lines 244-259: a reference transition is rejected if the destination reference is mutable and the source reference is not, if the destination referent is more strictly aligned (unless alignment is assumed), or if the destination referent is larger than the source referent; lines 276-282: the referents must be transmutable from source to destination, and if the destination reference is mutable also from destination to source; otherwise (shared destination reference) the condition `Condition::Immutable { ty: dst_ref.referent }` is added. No interior-mutability condition is placed on the source referent. The UI test tests/ui/transmutability/references/unsafecell.rs at the same commit rejects `&'static UnsafeCell<u8> -> &'static UnsafeCell<u8>` (line 29; comment at lines 25-26: 'We forbid `UnsafeCell`-containing ref-to-ref transmutations, because the two types may use different, incompatible synchronization strategies.') and accepts `&'static mut UnsafeCell<bool> -> &'static u8` (line 42). Implementation counterpart of the mutable-reference rule; for shared references it requires the destination referent to be free of interior mutability instead of characterising the interior-mutable case.
- **[AENEAS]** AeneasVerif/aeneas pull request #1447, '[WIP] Layouts, machine types, low-level representations.' (open draft, created 2026-10-15; head JoJoDeveloping:layouts at commit 2a1dd75567517e078f90b1df746af7373fe24cbc), files under backends/lean/Aeneas/Data/Layout/: a Lean model of MiniRust-style abstract bytes `uninit | init b` without provenance (Bytes.lean), per-layout `encode`/`decode` (EncodeDecode.lean, 'Following MiniRust's spec/lang/representation.md ("Generic properties")'), and proofs of the monotonicity and round-trip laws for valid layouts (GaloisConnection.lean). Its description states the work is in progress. Related Lean prototype of the byte-representation layer that this package abstracts away; it does not state cast-soundness conditions for references.
- **[RFC2835]** RFC 2835 'project-safe-transmute', https://rust-lang.github.io/rfcs/2835-project-safe-transmute.html: forms a project group 'with the purpose of designing subsequent RFCs around the topic of safe transmute between types.' Context only; it states no soundness conditions.
- **[KREBBERS]** R. Krebbers. A Formal C Memory Model for Separation Logic. Journal of Automated Reasoning 57(4):319-387, 2016. doi:10.1007/s10817-016-9369-1; R. Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. doi:10.1007/978-3-319-03545-1_4. Mechanizations of C's effective types (type-based restrictions on which types may access an object), a different axis from bit validity.
- **[TUCH]** H. Tuch, G. Klein, M. Norrish. Types, Bytes, and Separation Logic. POPL 2007, pp. 97-108. doi:10.1145/1190216.1190234. Typed views of byte-addressed C memory with separation logic, mechanized in Isabelle/HOL; it does not address reference-cast variance.
- **[REFINEDC]** M. Sammler, R. Lepigre, R. Krebbers, K. Memarian, D. Dreyer, D. Garg. RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types. PLDI 2021, pp. 158-174. doi:10.1145/3453483.3454036. A refinement and ownership type system for C whose soundness is proved in Coq, following the semantic approach of RustBelt.
- **[REFINEDRUST]** L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer. RefinedRust: A Type System for High-Assurance Verification of Rust Programs. Proc. ACM Program. Lang. 8(PLDI), pp. 1115-1139, 2024. doi:10.1145/3656422. A refinement type system for safe and unsafe Rust proven sound in Coq; it does not state cast-soundness characterizations of the kind given here.
- **[REF_VAR]** The Rust Reference, 'Subtyping and variance', https://doc.rust-lang.org/reference/subtyping.html (read 2026-11-20; verified in src/subtyping.md of rust-lang/reference at commit e24eecf97b0c9a6dbac67191098204dc8a190aaa, the Reference revision of the Rust 1.100.0 release), rule [subtyping.variance.builtin-types]: the table lists &'a T as covariant in T, &'a mut T as invariant in T, and std::cell::UnsafeCell<T> as invariant in T. The same read/write argument applied to lifetime subtyping rather than to bit validity; Cell<T> is invariant by the composite-type rule [subtyping.variance.user-composite-types], not by the table.
- **[RUSTHORNBELT]** Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856. doi:10.1145/3519939.3523704. Its Coq development (GitHub repository dewert99/rust-horn-belt, commit af47b28f38dd0cbeb620c2cb9ade29f0aad24c27, whose README reads 'This is the Coq development for "RustHornBelt: ..."') defines semantic subtyping `subtype E L ty ty' f` (theories/typing/type.v lines 933-934) and `eqtype` as subtyping in both directions (type.v lines 937-938), and proves `shr_subtype` (theories/typing/shr_bor.v lines 77-79: subtyping of referents gives subtyping of shared references), `uniq_subtype` (theories/typing/uniq_bor.v lines 153-155: eqtype of referents gives subtyping of unique borrows) and `cell_subtype` (theories/typing/lib/cell.v lines 104-105: eqtype gives subtyping of cells). These are mechanized sufficiency results of the same shape as the sufficiency directions of R2, R3 and R4 with destination writes, for a semantic subtyping relation rather than byte-level bit validity; they do not state the converse (necessity) direction or the satisfiability edge case.
- **[REYNOLDS]** J. C. Reynolds. Design of the Programming Language Forsythe. In P. W. O'Hearn and R. D. Tennent (eds.), Algol-like Languages, pp. 173-233, Birkhäuser, 1997. doi:10.1007/978-1-4612-4118-8_9. Forsythe's phrase types separate expressions (which can be read), acceptors (which can be assigned to) and variables (both), the classic decomposition of a read-write location into read and write capabilities.
- **[PIERCE_SANGIORGI]** B. Pierce, D. Sangiorgi. Typing and Subtyping for Mobile Processes. Mathematical Structures in Computer Science 6(5):409-453, 1996. doi:10.1017/S096012950007002X. Refines channel types of the pi-calculus by distinguishing the capabilities to read, to write, and to both read and write, which gives rise to a subtype relation on channels.
- **[RFC2981]** 'Safer Transmute' RFC, rust-lang/rfcs pull request #2981 (closed without merging on 2021-03-31; text as of the pull request's head commit ee1204c23320c33437107ff222e09afd9d5fef1d, file text/0000-safer-transmute.md), section 'Requirements on References' / 'Mutate-able References Must Preserve Validity': mutate-able references are all &mut T plus 'all shared (i.e., &T) references whose referent type contain any bytes produced by the contents of UnsafeCell', and 'the transmutation of a mutate-able reference may also not expand the bit-validity of the referenced type.' Closest informal prior statement of the mutable-reference and interior-mutability rules.
- **[JUNG_THESIS]** R. Jung. Understanding and Evolving the Rust Programming Language. PhD thesis, Universität des Saarlandes, 2020. doi:10.22028/D291-31946. Presents RustBelt and Stacked Borrows together.
- **[JLS]** The Java Language Specification, Java SE 21 edition: section 4.10.3 'Subtyping among Array Types' ('If S and T are both reference types, then S[] >1 T[] iff S >1 T.') and section 10.5 'Array Store Exception' ('If the type of the value being assigned is not assignment-compatible (§5.2) with the component type, an ArrayStoreException is thrown.'), https://docs.oracle.com/javase/specs/jls/se21/html/. The classic covariant mutable container: the write-side obligation is discharged by a run-time check instead of being required statically.
- **[STACKED_BORROWS]** R. Jung, H.-H. Dang, J. Kang, D. Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4(POPL), pp. 1-32, 2020. doi:10.1145/3371109. An operational aliasing model for Rust; aliasing is outside this package's model.
- **[TREE_BORROWS]** N. Villani, J. Hostert, D. Dreyer, R. Jung. Tree Borrows. Proc. ACM Program. Lang. 9(PLDI), pp. 1019-1042, 2025. doi:10.1145/3735592. A later operational aliasing model for Rust; aliasing is outside this package's model.
- **[FRISCH]** A. Frisch, G. Castagna, V. Benzaken. Semantic Subtyping: Dealing Set-Theoretically with Function, Union, Intersection, and Negation Types. Journal of the ACM 55(4), Article 19, pp. 1-64, 2008. doi:10.1145/1391289.1391293. Types as sets ordered by inclusion, with union and intersection; the lattice reading of R7 is this standard set-theoretic one.

Mechanized prior work: RustBelt and RustHornBelt prove in Coq sufficiency results of the same shape as the sufficiency directions of R2, R3 and R4 (destination writes) for their semantic subtyping relation (`shr_subtype`, `uniq_subtype`, `cell_subtype`). No mechanization of the converse (necessity) directions, of the satisfiability edge case, or of the checked-cast conditions of R8 was found. No result here is claimed novel (no T3).

Source-verification limits: the bibliographic records of [REYNOLDS] and [PIERCE_SANGIORGI] were verified on Crossref, but their primary texts were not accessible, so the cards give only one-line descriptions consistent with secondary summaries. The original RustBelt Coq repository could not be fetched; the Coq lemma names `shr_subtype`, `uniq_subtype` and `cell_subtype` are attributed to the RustHornBelt development at the pinned commit only. The zerocopy `try_transmute!` documentation quoted under R8-value-shared ("Note that the Src produced by the expression $e will not be dropped. Semantically, its bits will be copied into a new value of type Dst, the original Src will be forgotten, and the value of type Dst will be returned.") was read at https://docs.rs/zerocopy/0.8.63/zerocopy/macro.try_transmute.html on 2026-11-20.

## Revalidation

Build the library and re-run both audits (Lean `v4.34.1` via `elan`, which reads `lean/lean-toolchain`; no Lake dependencies), then recompute the statement hashes with the Python program below, from the package root:

```sh
cd lean
lake build                                    # builds ToyTransmute; expect no errors and no warnings about sorry
lake env lean support/Audit.lean              # expect: axiom audit passed: 316 declarations ...
lake env lean support/RevalidationAudit.lean > /tmp/revalidation.out
cd ..
python3 - <<'EOF'
import hashlib, json, re
out = json.loads(re.search(r"REVALIDATION_JSON (\{.*\})", open("/tmp/revalidation.out", encoding="utf-8").read()).group(1))
rec = json.load(open("audit/statements.json"))["statements"]
rec_ax = json.load(open("audit/axioms.json"))["declarations"]
got = {s["name"]: {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
                   "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
                   "closure_size": len(s["closure"])} for s in out["stmts"] if not s.get("missing")}
got_ax = {d["name"]: sorted(d["axioms"]) for d in out["decls"]}
named = set()
for card in json.load(open("results.json", encoding="utf-8")):
    refs = [card.get("lean"), card.get("nonvacuity_witness_lean"), card.get("positive_control_lean")]
    refs += [h.get("counterexample") for h in card["hypotheses"]]
    for v in refs:
        named |= {v} if isinstance(v, str) else set(v or [])
bad_ax = sorted(n for n, a in got_ax.items() if set(a) - {"propext", "Classical.choice", "Quot.sound"})
print("declarations audited:", len(got_ax), "| non-standard axioms:", bad_ax or "none")
print("axiom lists differ from audit/axioms.json:", sorted(n for n in set(got_ax) | set(rec_ax) if got_ax.get(n) != rec_ax.get(n)) or "none")
print("statements hashed:", len(got), "| hash drift vs audit/statements.json:", sorted(n for n in set(got) | set(rec) if got.get(n) != rec.get(n)) or "none")
print("card-referenced names not hashed:", sorted(named - set(got)) or "none")
EOF
```

Expected output of the Python program:

```text
declarations audited: 316 | non-standard axioms: none
axiom lists differ from audit/axioms.json: none
statements hashed: 109 | hash drift vs audit/statements.json: none
card-referenced names not hashed: none
```

`support/Audit.lean` fails if any declaration of any `ToyTransmute` module depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` (in particular on `sorryAx`), and prints the axioms of every declaration in `ToyTransmute.Results`. `support/RevalidationAudit.lean` (like `support/Audit.lean`, outside the `ToyTransmute` library target) prints, for every declaration of the `ToyTransmute` modules, its axioms, and for every Lean name referenced by a card in `results.json`, the `repr` of its type and its definition closure; the Python program hashes these by the recipe under Evidence and compares them with `audit/statements.json` and `audit/axioms.json`. Any hash drift means that a statement, or a definition it depends on, changed. For a single theorem, `#print axioms Toy.Transmute.<name>` in a file importing `ToyTransmute` gives its axioms.

Modeling-bridge claims (derived) are revalidated by re-reading the pinned sources, not by Lean: for a newer rustc, diff `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` around the reference-transition code (the `dst_ref.is_mut` branch that adds `Condition::Immutable { ty: dst_ref.referent }`) and `tests/ui/transmutability/references/unsafecell.rs` against commit `5b216e01a117532b30f061f3dff8a61408113c77`; for a newer zerocopy, re-read the trait bounds of `transmute!`, `transmute_ref!`, `transmute_mut!`, `try_transmute!`, `try_transmute_ref!` and `try_transmute_mut!`; for the Rust Reference, diff `src/behavior-considered-undefined.md` and `src/subtyping.md` against rust-lang/reference commit `e24eecf97b0c9a6dbac67191098204dc8a190aaa` (in particular rule [undefined.validity.reference-box] and its note on pointing to a valid value); for the nightly `TransmuteFrom` documentation, diff `library/core/src/mem/transmutability.rs` against rust-lang/rust commit `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`; for the Unsafe Code Guidelines glossary, diff `reference/src/glossary.md` against rust-lang/unsafe-code-guidelines commit `d809f91e62968913d808e53397fbcf7cea762cce`.
