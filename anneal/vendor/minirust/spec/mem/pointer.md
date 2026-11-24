# MiniRust pointers

One key question a memory model has to answer is *what is a pointer*.
It might seem like the answer is just "an integer of appropriate size", but [that is not the case][pointers-complicated] (as [more][pointers-complicated-2] and [more][pointers-complicated-3] discussion shows).
This becomes even more prominent with aliasing models such as [Stacked Borrows].
The memory model hence takes the stance that a pointer consists of the *address* (which truly is just an integer of appropriate size) and a *provenance*.
What exactly [provenance] *is* is up to the memory model.
As far as the interface is concerned, this is some opaque extra data that we carry around with our pointers and that places restrictions on which pointers may be used to do what when.

On top of this basic concept of a pointer, Rust also knows pointers with metadata (such as `*const [i32]`).
We therefore use the term *thin pointer* for what has been described above, and *pointer* for a pointer that optionally carries some metadata.

[pointers-complicated]: https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html
[pointers-complicated-2]: https://www.ralfj.de/blog/2020/12/14/provenance.html
[pointers-complicated-3]: https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html
[provenance]: https://github.com/rust-lang/unsafe-code-guidelines/blob/master/reference/src/glossary.md#pointer-provenance
[Stacked Borrows]: https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md

## Pointer Types

```rust
/// An "address" is a location in memory. This corresponds to the actual
/// location in the real program.
/// We make it a mathematical integer, but of course it is bounded by the size
/// of the address space.
pub type Address = Int;

/// A "thin pointer" is an address together with its Provenance.
/// Provenance can be absent; those pointers are
/// invalid for all non-zero-sized accesses.
pub struct ThinPointer<Provenance> {
    pub addr: Address,
    pub provenance: Option<Provenance>,
}

/// The runtime metadata that can be stored in a wide pointer.
pub enum PointerMeta<Provenance> {
    /// The metadata counts the number of elements in the slice.
    ElementCount(Int),
    /// The metadata points to a vtable referred at this location.
    /// This must point to a valid vtable and it is a spec bug if it doesn't.
    VTablePointer(ThinPointer<Provenance>),
}

/// A "pointer" is the thin pointer with optionally some metadata, making it a wide pointer.
/// This corresponds to the Rust raw pointer types, as well as references and boxes.
pub struct Pointer<Provenance> {
    pub thin_pointer: ThinPointer<Provenance>,
    pub metadata: Option<PointerMeta<Provenance>>,
}

impl<Provenance> ThinPointer<Provenance> {
    /// Offsets a pointer in bytes using wrapping arithmetic.
    /// This does not check whether the pointer is still in-bounds of its allocation.
    pub fn wrapping_offset<T: Target>(self, offset: Int) -> Self {
        let addr = self.addr + offset;
        let addr = addr.bring_in_bounds(Unsigned, T::PTR_SIZE);
        ThinPointer { addr, ..self }
    }

    pub fn widen(self, metadata: Option<PointerMeta<Provenance>>) -> Pointer<Provenance> {
        Pointer {
            thin_pointer: self,
            metadata,
        }
    }
}

```

## Pointee

We sometimes need information what it is that a pointer points to, this is captured in a "pointer type".
However, for unsized types the size and align might depend on the pointer metadata, which gives rise to the "layout strategy".

```rust
/// Describes what is needed to define the layout of the sized head of a tuple `(head.., tail)`.
pub struct TupleHeadLayout {
    /// The offset where the head ends and tail starts.
    /// This is the end of the last sized field; it is *not* necessarily aligned to `align`.
    pub end: Offset,

    /// The alignment of the head. This is the maximal alignment of any sized field and capped to the packed alignment.
    pub align: Align,

    /// If this is `Some(a)` the alignment of the tail will be capped at this value.
    /// Must be `None` for sized tuples.
    pub packed_align: Option<Align>,
}

/// Describes how the size and align of the value can be determined.
pub enum LayoutStrategy {
    /// The type is statically `Sized` with the given size and align.
    Sized(Size, Align),
    /// The type contains zero or more elements of the inner layout.
    /// The total size is a multiple of the element size and the align is exactly the element align.
    Slice(Size, Align),
    /// The size of the type must be looked up in the VTable of a wide pointer.
    /// Additionally, the vtable must be for the given trait.
    TraitObject(TraitName),
    /// The type consists of a sized head an unsized tail.
    Tuple {
        head: TupleHeadLayout,
        #[specr::indirection]
        tail: LayoutStrategy,
    },
}

/// Describes where in a potentially unsized type the UnsafeCell are.
/// Separate from `LayoutStrategy` since we must be able to compute `LayoutStrategy` from a
/// MiniRust `Type`, but that does not have enough information for an `UnsafeCellStrategy`.
/// FIXME: maybe it should?
pub enum UnsafeCellStrategy {
    /// List of offsets and sizes of `UnsafeCell`s.
    Sized { cells: List<(Offset, Size)> },
    /// Since the elements of a slice have the same type, we only keep track of the
    /// UnsafeCell's of one element, we can then "repeat" this for the rest of the slice.
    Slice { element_cells: List<(Offset, Size)> },
    /// The bytes for UnsafeCell's must be looked up in the VTable.
    TraitObject,
    /// A Tuple consists of a sized head an unsized tail.
    Tuple {
        head_cells: List<(Offset, Size)>,
        #[specr::indirection]
        tail_cells: UnsafeCellStrategy,
    },
}

/// Describes what we know about data behind a pointer.
pub struct PointeeInfo {
    pub layout: LayoutStrategy,
    pub inhabited: bool,
    /// Indicates where the `UnsafeCell` in this type are, which permit interior mutability.
    pub unsafe_cells: UnsafeCellStrategy,
    /// Whether the pointee implements the `Freeze` trait. This is used to determine
    /// whether the bytes "outside" the pointee have interior mutability.
    pub freeze: bool,
    pub unpin: bool,
}

/// A "trait name" is an identifier for the trait a vtable is for.
/// This depends on the defined methods and the marker traits.
pub struct TraitName(pub libspecr::Name);

/// The statically known kind of metadata stored in a pointer.
/// This determines the type of the metadata, while `Option<PointerMeta>` determines its value.
pub enum PointerMetaKind {
    None,
    ElementCount,
    VTablePointer(TraitName),
}

/// Stores all the information that we need to know about a pointer.
pub enum PtrType {
    Ref {
        /// Indicates a shared vs mutable reference.
        mutbl: Mutability,
        /// Describes what we know about the pointee.
        pointee: PointeeInfo,
    },
    Box {
        pointee: PointeeInfo,
    },
    Raw {
        /// Indicates what kind of metadata this pointer carries.
        meta_kind: PointerMetaKind,
    },
    FnPtr,
    /// This is a "stand-alone" vtable pointer, something that does not exist in surface Rust.
    VTablePtr(TraitName),
}
```

We also define two helper functions to get information about the pointer independent of the `PtrType` variant.
```rust
impl PtrType {
    /// If this is a safe pointer, return the pointee information.
    pub fn safe_pointee(self) -> Option<PointeeInfo> {
        match self {
            PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => Some(pointee),
            PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => None,
        }
    }

    pub fn meta_kind(self) -> PointerMetaKind {
        match self {
            PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => pointee.layout.meta_kind(),
            PtrType::Raw { meta_kind, .. } => meta_kind,
            PtrType::FnPtr | PtrType::VTablePtr(_) => PointerMetaKind::None,
        }
    }
}
```
