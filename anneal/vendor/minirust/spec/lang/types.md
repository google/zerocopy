# MiniRust types

This file defines the types of MiniRust.
Note that MiniRust types play a somewhat different role than Rust types:
every Rust type corresponds to a MiniRust type, but MiniRust types mostly just serve to define how valid [values](values.md) are represented in memory.
Basically, they define a (de)serialization format -- the [**representation relation**](representation.md), defined by an "encode" function to turn values into byte lists, and a "decode" function for the opposite operation.
In particular, MiniRust is by design *not type-safe*.
However, the representation relation is a key part of the language, since it forms the interface between the low-level and high-level view of data, between lists of (abstract) bytes and values.

That said, types do have a little more information than required for the representation relation.
For pointer types (references and boxes), types also contain a "mutability", which does not affect the representation relation but can be relevant for the aliasing rules.
(We might want to organize this differently in the future, and remove mutability from types.)
Union types know the types of their fields solely to support union field place projections.

Note that for now, we make the exact offsets of each field part of the type.
As always, this definition is incomplete.
In the future, we might want to separate a type from its layout, and consider these separate components -- we will have to see what works best.

```rust
/// The types of MiniRust.
pub enum Type {
    Int(IntType),
    Bool,
    /// `Ptr` represents all pointer types: references, raw pointers, boxes, function and vtable pointers.
    /// A pointer type does *not* need the full pointee type, since (de)serializing a pointer does not
    /// require knowledge about the pointee. We only track the metadata kind and basic pointee information
    /// like size and alignment that is required to check reference validity. This also means types have a finite
    /// representation even when the Rust type is recursive.
    Ptr(PtrType),
    /// "Tuple" is used for all heterogeneous types, i.e., both Rust tuples and structs.
    Tuple {
        /// Fields must not overlap.
        sized_fields: Fields,
        /// The layout of the sized fiels, i.e., the head.
        sized_head_layout: TupleHeadLayout,
        /// A last field (in terms of offset), i.e., the tail, may contain an unsized type,
        /// then its offset is given by rounding the `end` of `sized_head_layout` up to the alignment of this type.
        #[specr::indirection]
        // FIXME: Due to `specr::indirection` we cannot match on this field.
        unsized_field: Option<Type>,
    },
    Array {
        #[specr::indirection]
        elem: Type,
        count: Int,
        // TODO: store whether this is a (SIMD) vector, and something about alignment?
    },
    /// Slices, i.e. `[T]` are unsized types which therefore cannot be represented as values.
    /// This type is also used for strings: `str` are treated as `[u8]`.
    Slice {
        #[specr::indirection]
        elem: Type,
    },
    Union {
        /// Fields *may* overlap. Fields only exist for field access place projections,
        /// they are irrelevant for the representation relation.
        fields: Fields,
        /// A union can be split into multiple "chunks", where only the data inside those chunks is
        /// preserved, and data between chunks is lost (like padding in a struct).
        /// This is necessary to model the behavior of some `repr(C)` unions, see
        /// <https://github.com/rust-lang/unsafe-code-guidelines/issues/156> for details.
        chunks: List<(Offset, Size)>,
        /// The total size of the union, can indicate padding after the last chunk.
        size: Size,
        /// Total alignment of the union. Due to `repr(packed)` and `repr(align)`,
        /// this is independent of the fields' alignment.
        align: Align,
    },
    Enum {
        /// The map variants, each identified by a discriminant. Each variant is given by a type and its
        /// tag description. All variants are thought to "start at offset 0"; if the
        /// discriminant is encoded as an explicit tag, then that will be put into the
        /// padding of the active variant. (This means it is *not* safe to hand out mutable
        /// references to a variant at that type, as then the tag might be overwritten!)
        /// The Rust type `!` is encoded as an `Enum` with an empty list of variants.
        variants: Map<Int, Variant>,
        /// The `IntType` for the discriminant. This is used for the type of
        /// `GetDiscriminant` and `SetDiscriminant`. It is entirely independent of how
        /// the discriminant is represented in memory (the "tag").
        discriminant_ty: IntType,
        /// The decision tree to decode the discriminant from the tag at runtime.
        discriminator: Discriminator,
        /// The total size of the enum can indicate trailing padding.
        /// Must be large enough to contain all variants.
        size: Size,
        /// Total alignment of the enum. Due to `repr(packed)` and `repr(align)`,
        /// this is independent of the fields' alignment.
        align: Align,
    },
    /// A `dyn TraitName`. Commonly only used behind a pointer.
    TraitObject(TraitName),
}

pub struct IntType {
    pub signed: Signedness,
    pub size: Size,
}

pub type Fields = List<(Offset, Type)>;

pub struct Variant {
    /// The actual type of the variant.
    pub ty: Type,
    /// The information on where to store which values to write the tag.
    /// MUST NOT touch any bytes written by the actual type of the variant and vice
    /// versa. This is because we allow references/pointers to (enum) fields which
    /// should be able to dereference without having to deal with the tag.
    pub tagger: Map<Offset, (IntType, Int)>,
}

/// The decision tree that computes the discriminant out of the tag for a specific
/// enum type.
pub enum Discriminator {
    /// We know the discriminant.
    Known(Int),
    /// Tag decoding failed, there is no valid discriminant.
    Invalid,
    /// We don't know the discriminant, so we branch on the value of a specific value.
    Branch {
        offset: Offset,
        value_type: IntType,
        #[specr::indirection]
        fallback: Discriminator,
        /// An left-inclusive right-exclusive range of values that map to some Discriminator.
        children: Map<(Int, Int), Discriminator>,
    },
}
```

Note that references have no lifetime, since the lifetime is irrelevant for their representation in memory!
They *do* have a mutability since that is (or will be) relevant for the memory model.

## Layout of a type

Here we define the size and other layout properties of a type.

```rust
impl IntType {
    pub fn align<T: Target>(self) -> Align {
        let size = self.size.bytes();
        // The size is a power of two, so we can use it as alignment.
        let natural_align = Align::from_bytes(size).unwrap();
        // Integer alignment is capped by the target.
        natural_align.min(T::INT_MAX_ALIGN)
    }
}

impl Type {
    /// The layout, i.e. the size and align of the type. For `?Sized` types, this needs to be computed.
    pub fn layout<T: Target>(self) -> LayoutStrategy {
        use Type::*;
        use LayoutStrategy::Sized;
        match self {
            Int(int_type) => Sized(int_type.size, int_type.align::<T>()),
            Bool => Sized(Size::from_bytes_const(1), Align::ONE),
            Ptr(p) if p.meta_kind() == PointerMetaKind::None => Sized(T::PTR_SIZE, T::PTR_ALIGN),
            Ptr(_) => Sized(libspecr::Int::from(2) * T::PTR_SIZE, T::PTR_ALIGN),
            Union { size, align, .. } | Enum { size, align, .. } => Sized(size, align),
            Tuple { sized_head_layout, unsized_field, .. } => match unsized_field {
                None => {
                    let (size, align) = sized_head_layout.head_size_and_align();
                    Sized(size, align)
                }
                Some(tail_ty) => LayoutStrategy::Tuple {
                    head: sized_head_layout,
                    tail: tail_ty.layout::<T>(),
                },
            },
            Array { elem, count } => Sized(
                elem.layout::<T>().expect_size("WF ensures array element is sized") * count,
                elem.layout::<T>().expect_align("WF ensures array element is sized"),
            ),
            Slice { elem } => LayoutStrategy::Slice(
                elem.layout::<T>().expect_size("WF ensures slice element is sized"),
                elem.layout::<T>().expect_align("WF ensures array element is sized"),
            ),
            TraitObject(trait_name) => LayoutStrategy::TraitObject(trait_name),
        }
    }

    /// Returns the metadata kind when this type is used as a pointee.
    /// This matches the meta kind of the layout, but without needing to specify a target.
    pub fn meta_kind(self) -> PointerMetaKind {
        match self {
            Type::Slice { .. } => PointerMetaKind::ElementCount,
            Type::TraitObject(trait_name) => PointerMetaKind::VTablePointer(trait_name),
            Type::Tuple { unsized_field, .. } => match unsized_field {
                None => PointerMetaKind::None,
                Some(ty) => ty.meta_kind(),
            },
            _ => PointerMetaKind::None,
        }
    }
}
```

And we also define how to compute the actual size and alignment.

```rust
impl TupleHeadLayout {
    /// The actual alignment of the tail, considering the packed attribute.
    fn capped_tail_align(self, tail_align: Align) -> Align {
        match self.packed_align {
            Some(packed_align) => tail_align.min(packed_align),
            None => tail_align,
        }
    }

    /// Where the tail starts, given the aligment of the tail type.
    pub fn tail_offset(self, tail_align: Align) -> Offset {
        let capped_tail_align = self.capped_tail_align(tail_align);
        let tail_offset = self.end.align_to(capped_tail_align);
        tail_offset
    }

    /// The size and alignment of the full tuple, including the tail.
    /// Given the size and alignment of the tail type.
    pub fn full_size_and_align(self, tail_size: Size, tail_align: Align) -> (Size, Align) {
        let capped_tail_align = self.capped_tail_align(tail_align);
        let align = capped_tail_align.max(self.align);
        let tail_offset = self.tail_offset(tail_align);
        let end = tail_offset + tail_size;
        let size = end.align_to(align);
        (size, align)
    }

    /// Returns the size and alignment of the tuple when there is no tail.
    pub fn head_size_and_align(self) -> (Size, Align) {
        // This is equivalent to `full_size_and_align(ZERO, ONE)`.
        (self.end.align_to(self.align), self.align)
    }
}

impl LayoutStrategy {
    pub fn is_sized(self) -> bool {
        matches!(self, LayoutStrategy::Sized(..))
    }

    /// Returns the size when the type must be statically sized.
    pub fn expect_size(self, msg: &str) -> Size {
        match self {
            LayoutStrategy::Sized(size, _) => size,
            _ => panic!("expect_size called on unsized type: {msg}"),
        }
    }

    /// Returns the alignment when the type must be statically sized.
    pub fn expect_align(self, msg: &str) -> Align {
        match self {
            LayoutStrategy::Sized(_, align) => align,
            _ => panic!("expect_align called on unsized type: {msg}"),
        }
    }

    /// Computes the dynamic size and alignment, but the caller must provide compatible metadata.
    /// 
    /// The size and align of unsized structs depend on each other,
    /// thus we must recursively compute them at the same time.
    pub fn compute_size_and_align<Provenance>(
        self,
        meta: Option<PointerMeta<Provenance>>, 
        vtables: impl FnOnce(ThinPointer<Provenance>) -> VTable,
    ) -> (Size, Align) {
        match (self, meta) {
            (LayoutStrategy::Sized(size, align), None) => (size, align),
            (LayoutStrategy::Slice(elem_size, align), Some(PointerMeta::ElementCount(count))) => (count * elem_size, align),
            (LayoutStrategy::TraitObject(..), Some(PointerMeta::VTablePointer(vtable_ptr))) => {
                let vtable = vtables(vtable_ptr);
                (vtable.size, vtable.align)
            }
            (LayoutStrategy::Tuple { head, tail }, Some(meta)) => {
                let (tail_size, tail_align) = tail.compute_size_and_align(Some(meta), vtables);
                head.full_size_and_align(tail_size, tail_align)
            }
            _ => panic!("pointer meta data does not match type"),
        }
    }

    /// Returns the metadata kind which is needed to compute this strategy,
    /// i.e `machine.check_pointer_metadata(meta, self.meta_kind()).is_ok()` implies `machine.compute_*(meta)` is well-defined.
    pub fn meta_kind(self) -> PointerMetaKind {
        match self {
            LayoutStrategy::Sized(..) => PointerMetaKind::None,
            LayoutStrategy::Slice(..) => PointerMetaKind::ElementCount,
            LayoutStrategy::TraitObject(trait_name) => PointerMetaKind::VTablePointer(trait_name),
            LayoutStrategy::Tuple { tail, .. } => tail.meta_kind(),
        }
    }
}
```

## Integer type convenience functions

```rust
impl IntType {
    pub const I8: IntType = IntType { signed: Signedness::Signed, size: Size::from_bytes_const(1) };
    pub const I32: IntType = IntType { signed: Signedness::Signed, size: Size::from_bytes_const(4) };

    pub fn usize_ty<T: Target>() -> Self {
        IntType { signed: Signedness::Unsigned, size: T::PTR_SIZE }
    }

    pub fn can_represent(&self, i: Int) -> bool {
        i.in_bounds(self.signed, self.size)
    }

    pub fn bring_in_bounds(&self, i: Int) -> Int {
        i.bring_in_bounds(self.signed, self.size)
    }

    /// Generate the return type for IntWithOverflow
    pub fn with_overflow<T: Target>(&self) -> Type {
        // Define a tuple type with two fields: An integer followed directly by a boolean.
        let fields = list![(Size::ZERO, Type::Int(*self)), (self.size, Type::Bool)];
        // Alignment is always the one of the integer as boolean has align requirement 1.
        let align = self.align::<T>();
        // The total size is `self.size + 1` rounded up to the next multiple of `align`.
        // Since `self.size` is already a multiple of `align`, we can compute this as follows:
        let size = self.size + Size::from_bytes(align.bytes()).unwrap();
        Type::Tuple {
            sized_fields: fields,
            sized_head_layout: TupleHeadLayout {
                end: size,
                align,
                packed_align: None,
            },
            unsized_field: None,
        }
    }
}
```

## Unit type

```rust
/// Returns the type of a zero-sized, one aligned-tuple.
pub fn unit_ty() -> Type {
    let size = Size::from_bytes(<i32 as Into<Int>>::into(0)).unwrap();
    let align = Align::from_bytes(<i32 as Into<Int>>::into(1)).unwrap();
    Type::Tuple {
        sized_fields: List::new(),
        sized_head_layout: TupleHeadLayout { end: size, align, packed_align: None },
        unsized_field: None,
    }
}
```
