# MiniRust representation relation

The main purpose of [types](types.md) is to define how [values](values.md) are (de)serialized into/from memory.
This is the *[representation relation]*, which is defined in the following.
We also use this file to define the *language invariant* (or "validity invariant"): a predicate on byte ranges that must always hold when a range of bytes is "used at a given type".
For most types, the language invariant is defined by "these bytes represent some value", but for pointers, the language invariant imposes extra requirements.

The representation relation is defined by two functions, which are inverses to each other: `decode` and `encode`.
`decode` converts a list of bytes into a (potentially not well-formed) value; this operation can fail if the byte list is not a valid representation for the given type.
The decoded values must still be checked to be [well-formed][well-formed-value] by `check_value`, since some types also have additional runtime constraints.
`encode` inverts `decode`; it will always succeed for [well-formed][well-formed-value] inputs.

`encode`, `decode` and `check_value` satisfy some [properties](#generic-properties), which the specification must ensure, i.e. violating these properties is a spec bug.
However, they can also make some assumptions which the specification ensures:
The types these are called with/on are all [well-formed](well-formed.md#well-formed-layouts-and-types) and sized, as unsized types cannot be represented as values.
`encode` can also assume the value is [well-formed][well-formed-value] for the type,
and `decode` can assume the length of the byte list matches the size of the type.

[representation relation]: https://github.com/rust-lang/unsafe-code-guidelines/blob/master/reference/src/glossary.md#representation-relation
[well-formed-value]: #well-formed-values

## Type-directed Encode/Decode of values

We start with the definition of `encode` and `decode`.
Generally, whether a sequence of bytes represents a "well-formed value" is already defined by `decode`: if decoding succeeds, the representation is well-formed.
However, pointer types have further runtime constraints, which are only checked in `check_value`.

Since this definition is huge, we split it by type.
(We basically pretend we can have fallible patterns for the `self` parameter and declare the function multiple times with non-overlapping patterns.
If any pattern is not covered, that is a bug in the spec.)

```rust
impl Type {
    /// Decode a list of bytes into a value.
    /// 
    /// This can fail if `bytes` is not a valid encoding for the type,
    /// which typically means Undefined Behavior.
    /// Assumes `self` is well formed and `bytes.len()` matches the types size (violating this is a spec bug).
    #[specr::argmatch(self)]
    fn decode<M: Memory>(self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> { .. }

    /// Encode `v` into a list of bytes according to the type `self`.
    /// 
    /// Assumes `self` is well formed and `val` is well-formed for this type (violating this is a spec bug)..
    #[specr::argmatch(self)]
    fn encode<M: Memory>(self, val: Value<M>) -> List<AbstractByte<M::Provenance>> { .. }
}
```

### `bool`

```rust
impl Type {
    fn decode<M: Memory>(Type::Bool: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        if bytes.len() != 1 { panic!("decode of Type::Bool with invalid length"); }
        ret(match bytes[0] {
            AbstractByte::Init(0, _) => Value::Bool(false),
            AbstractByte::Init(1, _) => Value::Bool(true),
            _ => throw!(),
        })
    }
    fn encode<M: Memory>(Type::Bool: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        let Value::Bool(b) = val else { panic!() };
        list![AbstractByte::Init(if b { 1 } else { 0 }, None)]
    }
}
```

Note, in particular, that `bool` just entirely ignored provenance; we discuss this a bit more when we come to integer types.

### Integers

```rust
impl Type {
    fn decode<M: Memory>(Type::Int(IntType { signed, size }): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        if bytes.len() != size.bytes() { panic!("decode of Type::Int with invalid length"); }
        // Fails if any byte is `Uninit`.
        let bytes_data: List<u8> = bytes.try_map(|b| b.data())?;
        ret(Value::Int(M::T::ENDIANNESS.decode(signed, bytes_data)))
    }
    fn encode<M: Memory>(Type::Int(IntType { signed, size }): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        let Value::Int(i) = val else { panic!() };
        // `Endianness::encode` will do the integer's bound check.
        let bytes_data = M::T::ENDIANNESS.encode(signed, size, i).unwrap();
        bytes_data.map(|b| AbstractByte::Init(b, None))
    }
}
```

This entirely ignores provenance during decoding, and generates `None` provenance during encoding.
This corresponds to having ptr-to-int transmutation implicitly strip provenance (i.e., it behaves like [`addr`](https://doc.rust-lang.org/nightly/std/primitive.pointer.html#method.addr)),
and having int-to-ptr transmutation generate "invalid" pointers (like [`ptr::invalid`](https://doc.rust-lang.org/nightly/std/ptr/fn.invalid.html)).
This is required to achieve a "monotonicity" with respect to provenance (as discussed [below](#generic-properties)).

- TODO: Is that the right semantics for ptr-to-int transmutation? See [this discussion](https://github.com/rust-lang/unsafe-code-guidelines/issues/286).
- TODO: This does not allow uninitialized integers. I think that is fairly clearly what we want, also considering LLVM is moving towards using `noundef` heavily to avoid many of the current issues in their `undef` handling. But this is also still [being discussed](https://github.com/rust-lang/unsafe-code-guidelines/issues/71).

### Pointers

Pointers are significantly more complex to represent than just the integer address.
For one, they need to encode the provenance.
When decoding, we have to deal with the possibility of the pointer bytes not all having the same provenance;
this is defined to yield a pointer without provenance.
Some well-formedness properties, such as dereferenceablity of safe pointers, are not checked during `decode` itself.
This is done instead in [check_value][well-formed-value], since it needs access to the current `Machine` state.

On the other hand, some pointers are wide pointers which also need to encode their metadata.
The helpers `decode_ptr` and `encode_ptr` deal with thin pointers.
For wide pointers, `PtrType::as_wide_pair` defines the pointer as a pair of a thin pointer and some metadata type.

```rust
fn decode_ptr<M: Memory>(bytes: List<AbstractByte<M::Provenance>>) -> Option<ThinPointer<M::Provenance>> {
    if bytes.len() != M::T::PTR_SIZE.bytes() { panic!("decode of thin pointer with invalid length"); }
    // Convert into list of bytes; fail if any byte is uninitialized.
    let bytes_data = bytes.try_map(|b| b.data())?;
    let addr = M::T::ENDIANNESS.decode(Unsigned, bytes_data);
    // Get the provenance. Must be the same for all bytes, else we use `None`.
    // As start value we use the first byte's provenance (to avoid having to add a "top" element).
    let provenance = bytes.fold_with_idx(
        bytes[0].provenance_frag().map(|frag| frag.provenance),
        |acc, idx, byte| {
            // Crucially, if `acc` is ever `None`, it remains `None`.
            if let Some(frag) = byte.provenance_frag() &&
                frag.position == idx && Some(frag.provenance) == acc
            {
                acc
            } else {
                None
            }
        }
    );
    ret(ThinPointer { addr, provenance })
}

fn encode_ptr<M: Memory>(ptr: ThinPointer<M::Provenance>) -> List<AbstractByte<M::Provenance>> {
    let bytes_data = M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap();
    bytes_data.map_with_idx(|i, b|
        AbstractByte::Init(b, ptr.provenance.map(|provenance|
            ProvenanceFrag { provenance, position: i }
        ))
    )
}

impl PointerMetaKind {
    /// Returns the type of the metadata when used as a value.
    pub fn ty<T: Target>(self) -> Type {
        match self {
            PointerMetaKind::None => unit_type(),
            PointerMetaKind::ElementCount => Type::Int(IntType::usize_ty::<T>()),
            PointerMetaKind::VTablePointer(trait_name) => Type::Ptr(PtrType::VTablePtr(trait_name)),
        }
    }
}

impl PtrType {
    /// Returns a pair type representing this wide pointer or `None` if it is thin.
    pub fn as_wide_pair<T: Target>(self) -> Option<Type> {
        if self.meta_kind() == PointerMetaKind::None {
            return None;
        }
        let meta_ty = self.meta_kind().ty::<T>();
        assert_eq!(meta_ty.layout::<T>().expect_size("metadata is always sized"), T::PTR_SIZE, "metadata is assumed to be pointer-sized");
        assert_eq!(meta_ty.layout::<T>().expect_align("metadata is always sized"), T::PTR_ALIGN, "metadata is assumed to be pointer-aligned");
        let thin_pointer_field = (Offset::ZERO, Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None }));
        let metadata_field = (T::PTR_SIZE, meta_ty);
        ret(Type::Tuple {
            sized_fields: list![thin_pointer_field, metadata_field],
            sized_head_layout: TupleHeadLayout {
                end: Int::from(2) * T::PTR_SIZE,
                align: T::PTR_ALIGN,
                packed_align: None,
            },
            unsized_field: None,
        })
    }
}

impl PointerMetaKind {
    /// Decodes a value to metadata.
    /// The spec will only call this with values which are well formed for `self.ty()`,
    /// but this may return ill-formed metadata (as defined by `Machine::check_ptr_metadata`), thus needs to be checked.
    fn decode_value<M: Memory>(self, value: Value<M>) -> Option<PointerMeta<M::Provenance>> {
        match (self, value) {
            (PointerMetaKind::None, Value::Tuple(fields)) if fields.is_empty() => None,
            (PointerMetaKind::ElementCount, Value::Int(count)) => Some(PointerMeta::ElementCount(count)),
            (PointerMetaKind::VTablePointer(_), Value::Ptr(ptr)) if ptr.metadata.is_none() => Some(PointerMeta::VTablePointer(ptr.thin_pointer)),
            _ => panic!("PointerMeta::decode_value called with invalid value"),
        }
    }

    /// Encodes metadata as a value.
    /// The spec ensures this is only called with well-formed metadata (as defined by `Machine::check_ptr_metadata`).
    fn encode_as_value<M: Memory>(self, meta: Option<PointerMeta<M::Provenance>>) -> Value<M> {
        match (self, meta) {
            (PointerMetaKind::None, None) => unit_value(),
            (PointerMetaKind::ElementCount, Some(PointerMeta::ElementCount(count))) => Value::Int(count),
            (PointerMetaKind::VTablePointer(_), Some(PointerMeta::VTablePointer(ptr))) => Value::Ptr(ptr.widen(None)),
            _ => panic!("PointerMeta::encode_as_value called with invalid value"),
        }
    }
}

impl Type {
    fn decode<M: Memory>(Type::Ptr(ptr_type): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
            // This will recursively call this decode function again, but with a thin pointer type.
            let Value::Tuple(parts) = pair_ty.decode::<M>(bytes)? else {
                panic!("as_wide_pair always returns a tuple type");
            };
            let Value::Ptr(ptr) = parts[0] else {
                panic!("as_wide_pair always returns tuple with the first field being a thin pointer");
            };
            // This metadata might not be well-formed, but we are allowed to return ill-formed pointers here.
            let meta = ptr_type.meta_kind().decode_value(parts[1]);
            assert!(meta.is_some(), "as_wide_pair always returns a suitable metadata type");
            ret(Value::Ptr(ptr.thin_pointer.widen(meta)))
        } else {
            // Handle thin pointers.
            let ptr = decode_ptr::<M>(bytes)?;
            ret(Value::Ptr(ptr.widen(None)))
        }
    }
    fn encode<M: Memory>(Type::Ptr(ptr_type): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        let Value::Ptr(ptr) = val else { panic!("val is WF for a pointer") };

        if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
            let thin_ptr_value = Value::Ptr(ptr.thin_pointer.widen(None));
            let meta_data_value = ptr_type.meta_kind().encode_as_value::<M>(ptr.metadata);
            let tuple = Value::Tuple(list![thin_ptr_value, meta_data_value]);

            // This will recursively call this encode function again, but with a thin pointer type.
            pair_ty.encode::<M>(tuple)
        } else {
            // Handle thin pointers.
            assert!(ptr.metadata.is_none(), "ptr_type and value have mismatching metadata");
            encode_ptr::<M>(ptr.thin_pointer)
        }
    }
}
```

- TODO: This definition says that when multiple provenances are mixed, the pointer has `None` provenance, i.e., it is "invalid".
  Is that the semantics we want? Also see [this discussion](https://github.com/rust-lang/unsafe-code-guidelines/issues/286#issuecomment-1136948796).

### Tuples (and structs, ...)

```rust
impl Type {
    fn decode<M: Memory>(Type::Tuple { sized_fields, sized_head_layout, unsized_field }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        assert!(unsized_field.is_none(), "decode of Type::Tuple with unsized field");

        let (size, _) = sized_head_layout.head_size_and_align();
        if bytes.len() != size.bytes() { panic!("decode of Type::Tuple with invalid length"); }
        ret(Value::Tuple(
            sized_fields.try_map(|(offset, ty)| {
                let subslice = bytes.subslice_with_length(
                    offset.bytes(),
                    ty.layout::<M::T>().expect_size("WF ensures all sized tuple fields are sized").bytes()
                );
                ty.decode::<M>(subslice)
            })?
        ))
    }
    fn encode<M: Memory>(Type::Tuple { sized_fields, sized_head_layout, unsized_field }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        assert!(unsized_field.is_none(), "encode of Type::Tuple with unsized field");

        let (size, _) = sized_head_layout.head_size_and_align();
        let Value::Tuple(values) = val else { panic!() };
        assert_eq!(values.len(), sized_fields.len());
        let mut bytes = list![AbstractByte::Uninit; size.bytes()];
        for ((offset, ty), value) in sized_fields.zip(values) {
            bytes.write_subslice_at_index(offset.bytes(), ty.encode::<M>(value));
        }
        bytes
    }
}
```

Note in particular that `decode` ignores the bytes which are before, between, or after the fields (usually called "padding").
`encode` in turn always and deterministically makes those bytes `Uninit`.
(The [generic properties](#generic-properties) defined below make this the only possible choice for `encode`.)

### Arrays

```rust
impl Type {
    fn decode<M: Memory>(Type::Array { elem, count }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        let elem_size = elem.layout::<M::T>().expect_size("WF ensures array element is sized");
        let full_size = elem_size * count;

        if bytes.len() != full_size.bytes() { panic!("decode of Type::Array with invalid length"); }

        let chunks: List<_> = (Int::ZERO..count).map(|i|
            bytes.subslice_with_length(i*elem_size.bytes(), elem_size.bytes())
        ).collect();

        ret(Value::Tuple(
            chunks.try_map(|elem_bytes| elem.decode::<M>(elem_bytes))?
        ))
    }
    fn encode<M: Memory>(Type::Array { elem, count }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        let Value::Tuple(values) = val else { panic!() };
        assert_eq!(values.len(), count);
        values.flat_map(|value| {
            let bytes = elem.encode::<M>(value);
            assert_eq!(bytes.len(), elem.layout::<M::T>().expect_size("WF ensures array element is sized").bytes());
            bytes
        })
    }
}
```

### Unions

A union simply stores the bytes directly, no high-level interpretation of data happens.

- TODO: Some real unions actually do not preserve all bytes, they [can have padding](https://github.com/rust-lang/unsafe-code-guidelines/issues/156).
  So we have to model that there can be "gaps" between the parts of the byte list that are preserved perfectly.
- TODO: Should we require *some* kind of validity? See [this discussion](https://github.com/rust-lang/unsafe-code-guidelines/issues/73).

```rust
impl Type {
    fn decode<M: Memory>(Type::Union { size, chunks, .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        if bytes.len() != size.bytes() { panic!("decode of Type::Union with invalid length"); }
        let mut chunk_data = list![];
        // Store the data from each chunk.
        for (offset, size) in chunks {
            chunk_data.push(bytes.subslice_with_length(offset.bytes(), size.bytes()));
        }
        ret(Value::Union(chunk_data))
    }
    fn encode<M: Memory>(Type::Union { size, chunks, .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        let Value::Union(chunk_data) = val else { panic!() };
        assert_eq!(chunk_data.len(), chunks.len());
        let mut bytes = list![AbstractByte::Uninit; size.bytes()];
        // Restore the data from each chunk.
        for ((offset, size), data) in chunks.zip(chunk_data) {
            assert_eq!(size.bytes(), data.len());
            bytes.write_subslice_at_index(offset.bytes(), data);
        }
        bytes
    }
}
```

### Enums

Enum encoding and decoding.
Note that the discriminant may not be written into bytes that contain encoded data.
This is to ensure that pointers to the data always contain valid values.

```rust
/// Uses the `Discriminator` to decode the discriminant from the tag read out of the value's bytes using the accessor.
/// Returns `Ok(None)` when reaching `Discriminator::Invalid` and when any of the reads
/// for `Discriminator::Branch` encounters uninitialized memory.
/// Returns `Err` only if `accessor` returns `Err`.
///
/// The accessor is given an offset relative to the beginning of the encoded enum value,
/// and it should return the abstract byte at that offset.
/// FIXME: we have multiple quite different fail sources, it would be nice to return more error information.
fn decode_discriminant<M: Memory>(mut accessor: impl FnMut(Offset, Size) -> Result<List<AbstractByte<M::Provenance>>>, discriminator: Discriminator) -> Result<Option<Int>> {
    match discriminator {
        Discriminator::Known(val) => ret(Some(val)),
        Discriminator::Invalid => ret(None),
        Discriminator::Branch { offset, value_type, children, fallback } => {
            let bytes = accessor(offset, value_type.size)?;
            let Some(Value::Int(val)) = Type::Int(value_type).decode::<M>(bytes)
                else { return ret(None); };
            let next_discriminator = children.iter()
                .find_map(|((start, end), child)| if start <= val && val < end { Some(child) } else { None })
                .unwrap_or(fallback);
            decode_discriminant::<M>(accessor, next_discriminator)
        }
    }
}

/// Writes the tag described by the tagger into the bytes accessed using the accessor.
/// Returns `Err` only if `accessor` returns `Err`.
///
/// The accessor is given an offset relative to the beginning of the encoded enum value
/// and the integer value and type to store at that offset.
fn encode_discriminant<M: Memory>(
    mut accessor: impl FnMut(Offset, List<AbstractByte<M::Provenance>>) -> Result,
    tagger: Map<Offset, (IntType, Int)>
) -> Result<()> {
    for (offset, (value_type, value)) in tagger.iter() {
        let bytes = Type::Int(value_type).encode::<M>(Value::Int(value));
        accessor(offset, bytes)?;
    }
    ret(())
}

impl Type {
    fn decode<M: Memory>(Type::Enum { variants, discriminator, size, .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        if bytes.len() != size.bytes() { panic!("decode of Type::Enum with invalid length"); }
        // We can unwrap the decoded discriminant as our accessor never fails, and
        // decode_discriminant only fails if the accessor fails.
        let discriminant = decode_discriminant::<M>(
            |offset, size| ret(bytes.subslice_with_length(offset.bytes(), size.bytes())),
            discriminator
        ).unwrap()?;

        // Decode into the variant.
        // Because the variant is the same size as the enum we don't need to pass a subslice.
        let Some(value) = variants[discriminant].ty.decode(bytes)
            else { return None };

        Some(Value::Variant { discriminant, data: value })
    }

    fn encode<M: Memory>(Type::Enum { variants, .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        // FIXME: can't use `let ... else` as specr-transpile does not recognize that as a
        // match so it does not do GcGow handling.
        let (discriminant, data) = match val {
            Value::Variant { discriminant, data } => (discriminant, data),
            _ => panic!(),
        };

        // `idx` is guaranteed to be in bounds by the well-formed check in the type.
        let Variant { ty: variant, tagger } = variants[discriminant];
        let mut bytes = variant.encode(data);

        // Write tag into the bytes around the data.
        // This is fine as we don't allow encoded data and the tag to overlap.
        // We can unwrap the `Result` as our accessor never fails, and
        // encode_discriminant only fails if the accessor fails.
        encode_discriminant::<M>(|offset, value_bytes| {
            bytes.write_subslice_at_index(offset.bytes(), value_bytes);
            ret(())
        }, tagger).unwrap();
        bytes
    }
}
```

### Unsized types

Unsized types do not have values and thus there is no representation relation.

```rust
impl Type {
    fn decode<M: Memory>(Type::Slice { .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        panic!("decode of Type::Slice")
    }
    fn encode<M: Memory>(Type::Slice { .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        panic!("encode of Type::Slice")
    }
}

impl Type {
    fn decode<M: Memory>(Type::TraitObject(..): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
        panic!("decode of Type::TraitObject")
    }
    fn encode<M: Memory>(Type::TraitObject(..): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
        panic!("encode of Type::TraitObject")
    }
}
```

## Well-formed values

We call a value `val` *well-formed* for a type `ty` if `machine.check_value(val, ty).is_ok()`.
The specification ensures (statically or dynamically) that all values in MiniRust are always well-formed,
the only exception being values returned from `decode`, which must be passed to `check_value` before being passed to any other part of the specification.
Violating this when running a well-formed program is a spec bug.
Therefore, `encode` and other expressions can assume well-formed inputs as well.
This is MiniRust's way of ensuring the language invariant.

In particular, a load instruction causes UB when the sequence of bytes does not correspond to a representation of a well-formed value.
Generally, this is already dealt with by `decode`: if decoding succeeds, the representation is well-formed.
However, pointer types have further runtime constraints: specifically, [safe pointers][ptr_type] require the address to be aligned, dereferenceable and non-null, and they require the pointee type to be inhabited.
This is separated from `decode`, because checking alignment or the well-formedness of a trait object pointer needs vtable information, and dereferenceablity need information about the current state of memory.
Dropping dereferenceablity as a requirement to unify these steps was discussed, see [this discussion](https://github.com/rust-lang/unsafe-code-guidelines/issues/77), but for trait objects this separation is desireable.
Therefore usages for `decode` will either follow up by calling `check_value` to raise UB or reason about why this is statically ensured already. 

So types like `&!`, have many byte lists which decode without problems, but none are *well-formed*:
when the pointee type is uninhabited, there exists no valid reference to that type.

[ptr_type]: ../mem/pointer.md#Pointee

```rust
/// Ensures the given boolean is true or else raises UB.
fn ensure_else_ub(b: bool, msg: &str) -> Result<()> {
    if !b { throw_ub!("{}", msg); }
    ret(())
}

impl<M: Memory> Machine<M> {
    /// Defines well-formedness for pointer metadata for a given kind.
    fn check_ptr_metadata(&self, meta: Option<PointerMeta<M::Provenance>>, kind: PointerMetaKind) -> Result {
        match (meta, kind) {
            (None, PointerMetaKind::None) => {}
            (Some(PointerMeta::ElementCount(num)), PointerMetaKind::ElementCount) =>
                self.check_value(Value::Int(num), Type::Int(IntType::usize_ty::<M::T>()))?,
            (Some(PointerMeta::VTablePointer(ptr)), PointerMetaKind::VTablePointer(trait_name)) => {
                self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))?;
            }
            _ => throw_ub!("Value::Ptr: invalid metadata"),
        };

        Ok(())
    }

    /// Checks that a pointer is well-formed.
    fn check_ptr(&self, ptr: Pointer<M::Provenance>, ptr_ty: PtrType) -> Result {
        ensure_else_ub(ptr.thin_pointer.addr.in_bounds(Unsigned, M::T::PTR_SIZE), "Value::Ptr: pointer out-of-bounds")?;

        // This has to be checked first, to ensure we can e.g. compute size/align below.
        self.check_ptr_metadata(ptr.metadata, ptr_ty.meta_kind())?;

        // Safe pointer, i.e. references, boxes
        if let Some(pointee) = ptr_ty.safe_pointee() {
            let size = self.compute_size(pointee.layout, ptr.metadata);
            let align = self.compute_align(pointee.layout, ptr.metadata);
            // The total size must be at most `isize::MAX`.
            ensure_else_ub(size.bytes().in_bounds(Signed, M::T::PTR_SIZE), "Value::Ptr: total size exeeds isize::MAX")?;

            // Safe pointers need to be non-null, aligned, dereferenceable, and not point to an uninhabited type.
            // (Think: uninhabited types have impossible alignment.)
            ensure_else_ub(ptr.thin_pointer.addr != 0, "Value::Ptr: null safe pointer")?;
            ensure_else_ub(align.is_aligned(ptr.thin_pointer.addr), "Value::Ptr: unaligned safe pointer")?;
            ensure_else_ub(pointee.inhabited, "Value::Ptr: safe pointer to uninhabited type")?;
            ensure_else_ub(
                self.mem.dereferenceable(ptr.thin_pointer, size).is_ok(),
                "Value::Ptr: non-dereferenceable safe pointer"
            )?;

            // However, we do not care about the data stored wherever this pointer points to.
        } else if let PtrType::VTablePtr(trait_name) = ptr_ty {
            // This is a "stand-alone" vtable pointer, something that does not exist
            // in surface Rust. Ensure that it points to an allocated vtable for the correct trait.
            let vtable = self.vtable_from_ptr(ptr.thin_pointer)?;
            ensure_else_ub(vtable.trait_name == trait_name, "Value::Ptr: invalid vtable in metadata")?;
        }

        Ok(())
    }

    /// We assume `ty` is itself well-formed and sized and the variant of `value` matches the `ty` variant.
    /// The specification must not call this function otherwise.
    fn check_value(&self, value: Value<M>, ty: Type) -> Result {
        match (value, ty) {
            (Value::Int(i), Type::Int(int_ty)) => {
                ensure_else_ub(int_ty.can_represent(i), "Value::Int: invalid integer value")?;
            }
            (Value::Bool(_), Type::Bool) => {},
            (Value::Ptr(ptr), Type::Ptr(ptr_ty)) => self.check_ptr(ptr, ptr_ty)?,
            (Value::Tuple(vals), Type::Tuple { sized_fields, unsized_field, .. }) => {
                assert!(unsized_field.is_none(), "Value: unsized structs cannot be represented as values");
                ensure_else_ub(vals.len() == sized_fields.len(), "Value::Tuple: invalid number of fields")?;
                for (val, (_, ty)) in vals.zip(sized_fields) {
                    self.check_value(val, ty)?;
                }
            }
            (Value::Tuple(vals), Type::Array { elem, count }) => {
                ensure_else_ub(vals.len() == count, "Value::Tuple: invalid number of elements")?;
                for val in vals {
                    self.check_value(val, elem)?;
                }
            }
            (Value::Union(chunk_data), Type::Union { chunks, .. }) => {
                ensure_else_ub(chunk_data.len() == chunks.len(), "Value::Union: invalid chunk size")?;
                for (data, (_, size)) in chunk_data.zip(chunks) {
                    ensure_else_ub(data.len() == size.bytes(), "Value::Union: invalid chunk data")?;
                }
            }
            (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) => {
                let Some(variant) = variants.get(discriminant) else {
                    throw_ub!("Value::Variant: invalid discrimant");
                };
                self.check_value(data, variant.ty)?;
            }
            (_, Type::Slice { .. }) => panic!("Value: slices cannot be represented as values"),
            (_, Type::TraitObject { .. }) => panic!("Value: trait objects cannot be represented as values"),
            _ => panic!("Value: value does not match type")
        }

        ret(())
    }
}
```

- TODO: Do we really want to check `dereferenceable` here? That makes "being a valid value" a non-persistent property.
  We might want to consider treating dereferenceability separately.
- TODO: Do we really want to special case references to uninhabited types? Do we somehow want to require more, like pointing to a valid instance of the pointee type?
  (The latter would not even be possible with the current pointee information in MiniRust.)
  Also see [this discussion](https://github.com/rust-lang/unsafe-code-guidelines/issues/77).
- TODO: Inhabitedness and non-nullness could be checked in `decode` itself. Should we?

## Typed memory accesses

One key use of the value representation is to define a "typed" interface to memory.
Loading bytes at a type which does not correspond to any representation of a [well-formed value][well-formed-value] will raise UB, ensuring that all values in MiniRust are well-formed.
Since all values are well-formed, (thus a store with a ill-formed value is a spec bug) it can simply encode the value and store the byte list.

This interface is inspired by [Cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/).

```rust
impl<M: Memory> Machine<M> {
    fn typed_store(&mut self, ptr: ThinPointer<M::Provenance>, val: Value<M>, ty: Type, align: Align, atomicity: Atomicity) -> Result {
        // All values floating around in MiniRust must be well-formed.
        assert!(self.check_value(val, ty).is_ok(), "trying to store {val:?} which is ill-formed for {:#?}", ty);
        let bytes = ty.encode::<M>(val);
        self.mem.store(ptr, bytes, align, atomicity)?;

        ret(())
    }

    fn typed_load(&mut self, ptr: ThinPointer<M::Provenance>, ty: Type, align: Align, atomicity: Atomicity) -> Result<Value<M>> {
        let bytes = self.mem.load(ptr, ty.layout::<M::T>().expect_size("the callers ensure `ty` is sized"), align, atomicity)?;
        ret(match ty.decode::<M>(bytes) {
            Some(val) => {
                // Ensures we only produce well-formed values.
                self.check_value(val, ty)?;
                val
            }
            None => throw_ub!("load at type {ty:?} but the data in memory violates the language invariant"), // FIXME use Display instead of Debug for `ty`
        })
    }
}
```

## Generic properties

There are some generic properties that `encode` and `decode` must satisfy.
The most obvious part is consistency of size:
- `ty.encode(value).len() == ty.layout().expect_size("")`
- `ty.decode(bytes)` may assume this property: `bytes.len() == ty.layout().expect_size("")`

More interestingly, we have some round-trip properties.
For instance, starting with a valid value, encoding it, and then decoding it, must produce the same result.

To make this precise, we first have to define an order in values and byte lists that captures when one value (byte list) is "more defined" than another.
"More defined" here can either mean initializing some previously uninitialized data, or adding provenance to data that didn't have it.
(Adding provenance means adding the permission to access some memory, so this can make previously undefined programs defined, but it can never make previously defined programs undefined.)

Note that none of the definitions in this section are needed to define the semantics of a Rust program, or to make MiniRust into a runnable interpreter.
They only serve as internal consistency requirements of the semantics.
It would be a specification bug if the representation relations defined above violated these properties.

```rust
#[allow(unused)]
trait DefinedRelation {
    /// returns whether `self` is less or as defined as `other`
    fn le_defined(self, other: Self) -> bool;
}
```

Starting with `AbstractByte`, we define `b1 <= b2` ("`b1` is less-or-equally-defined as `b2`") as follows:

```rust
impl<Provenance> DefinedRelation for AbstractByte<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        use AbstractByte::*;
        match (self, other) {
            // `Uninit <= _`: initializing something makes it "more defined".
            (Uninit, _) =>
                true,
            // Among initialized bytes, adding provenance makes it "more defined".
            (Init(data1, None), Init(data2, _)) =>
                data1 == data2,
            // If both bytes have provenance, everything must be equal.
            (Init(data1, Some(provenance1)), Init(data2, Some(provenance2))) =>
                data1 == data2 && provenance1 == provenance2,
            // Nothing else is related.
            _ => false,
        }
    }
}
```

Similarly, on `Pointer` we say that adding provenance in the thin pointer or metadata makes it more defined:
```rust
impl<Provenance> DefinedRelation for ThinPointer<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        self.addr == other.addr &&
            match (self.provenance, other.provenance) {
                (None, _) => true,
                (Some(prov1), Some(prov2)) => prov1 == prov2,
                _ => false,
            }
    }
}

impl<Provenance> DefinedRelation for PointerMeta<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        match (self, other) {
            (PointerMeta::VTablePointer(ptr1), PointerMeta::VTablePointer(ptr2)) => ptr1.le_defined(ptr2),
            _ => self == other
        }
    }
}

impl<Provenance> DefinedRelation for Pointer<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        self.thin_pointer.le_defined(other.thin_pointer) &&
            self.metadata.le_defined(other.metadata)
    }
}
```

The order on `List<AbstractByte>` is assumed to be such that `bytes1 <= bytes2` if and only if they have the same length and are bytewise related by `<=`.
In fact, we define this to be in general how lists are partially ordered (based on the order of their element type):
```rust
impl<T: DefinedRelation> DefinedRelation for List<T> {
    fn le_defined(self, other: Self) -> bool {
        self.len() == other.len() &&
            self.zip(other).all(|(l, r)| l.le_defined(r))
    }
}
```

For `Value`, we lift the order on byte lists to relate `Bytes`s, and otherwise require equality:
```rust
impl<M: Memory> DefinedRelation for Value<M> {
    fn le_defined(self, other: Self) -> bool {
        use Value::*;
        match (self, other) {
            (Int(i1), Int(i2)) =>
                i1 == i2,
            (Bool(b1), Bool(b2)) =>
                b1 == b2,
            (Ptr(p1), Ptr(p2)) =>
                p1.le_defined(p2),
            (Tuple(vals1), Tuple(vals2)) =>
                vals1.le_defined(vals2),
            (Variant { discriminant: discriminant1, data: data1 }, Variant { discriminant: discriminant2, data: data2 }) =>
                discriminant1 == discriminant2 && data1.le_defined(data2),
            (Union(chunks1), Union(chunks2)) => chunks1.le_defined(chunks2),
            _ => false
        }
    }
}
```

Finally, on `Option<Value>` we assume that `None <= _`, and `Some(v1) <= Some(v2)` if and only if `v1 <= v2`:
```rust
impl<T: DefinedRelation> DefinedRelation for Option<T> {
    fn le_defined(self, other: Self) -> bool {
        match (self, other) {
            (None, _) => true,
            (Some(l), Some(r)) => l.le_defined(r),
            _ => false
        }
    }
}
```

In the following, let `ty` be an arbitrary well-formed type.
We say that a `v: Value` is ["well-formed"][well-formed-value] for a type if `machine.check_value(v, ty)` is `Ok(())`.
This ensures that the basic structure of the value and the type match up.

Now we can state the laws that we require.
First of all, `encode` and `decode` must both be "monotone":
- If `val1 <= val2` (and if both values are well-formed for `ty`), then `ty.encode(val1) <= ty.encode(val2)`.
- If `bytes1 <= bytes2`, then `ty.decode(bytes1) <= ty.decode(bytes2)`.

More interesting are the round-trip properties:
- If `val` is well-formed for `ty`, then `ty.decode(ty.encode(val)) == Some(val)`.
  In other words, encoding a value and then decoding it again is lossless.
- If `ty.decode(bytes) == Some(val)` (and `bytes` has the right length for `ty`), then `ty.encode(val) <= bytes`.
  In other words, if a byte list is successfully decoded, then encoding it again will lead to a byte list that is "less defined"
  (some bytes might have become `Uninit`, but otherwise it is the same).

(For the category theory experts: this is called an "adjoint" relationship, or a "Galois connection" in abstract interpretation speak.
Monotonicity ensures that `encode` and `decode` are functors.)

The last property might sound surprising, but consider what happens for padding: `encode` will always make it `Uninit`,
so a bytes-value-bytes roundtrip of some data with padding will reset some bytes to `Uninit`.

Together, these properties ensure that it is okay to optimize away a self-assignment like `tmp = x; x = tmp`.
The effect of this assignment (as defined [later](step/statements.md)) is to decode the `bytes1` stored at `x`, and then encode the resulting value again into `bytes2` and store that back.
(We ignore the intermediate storage in `tmp`.)
The second round-trip property ensures that `bytes2 <= bytes1`.
If we remove the assignment, `x` ends up with `bytes1` rather than `bytes2`; we thus "increase memory" (as in, the memory in the transformed program is "more defined" than the one in the source program).
According to monotonicity, "increasing" memory can only ever lead to "increased" decoded values.
For example, if the original program later did a successful decode at an integer to some `v: Value`, then the transformed program will return *the same* value (since `<=` on `Value::Int` is equality).

## Transmutation

The representation relation also says everything there is to say about "transmutation".
By this I mean not just the `std::mem::transmute` function, but any operation that "re-interprets data from one type at another type"
(essentially a `reinterpret_cast` in C++ terms).
Transmutation means taking a value at some type, encoding it, and then decoding it *at a different type*, and checking it is a well-formed value for this different type.
More precisely:

```rust
impl<M: Memory> Machine<M> {
    /// Transmutes `val` from `type1` to `type2`.
    fn transmute(&self, val: Value<M>, type1: Type, type2: Type) -> Result<Value<M>> {
        assert!(
            type1.layout::<M::T>().expect_size("WF ensures sized operands")
                == type2.layout::<M::T>().expect_size("WF ensures sized operands")
        );        
        let bytes = type1.encode::<M>(val);
        if let Some(raw_value) = type2.decode::<M>(bytes) {
            self.check_value(raw_value, type2)?;
            ret(raw_value)
        } else {
            throw_ub!("transmuted value is not valid at new type")
        }
    }
}
```

This operation can, of course, fail, which means that the encoding of `val` is not valid at `type2`.
