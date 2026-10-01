use crate::ast::*;
use crate::common::serialize_map_to_array::SeqHashMapToArray;
use crate::ids::IndexVec;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

mod vars;
pub use vars::*;

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    Hash,
    PartialOrd,
    Ord,
    EnumIsA,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
pub enum Region {
    /// Region variable. See `DeBruijnVar` for details.
    Var(RegionDbVar),
    /// Static region
    Static,
    /// Body-local region, considered existentially-bound at the level of a body.
    Body(RegionId),
    /// Erased region
    Erased,
}

/// Identifier of a trait instance.
/// This is derived from the trait resolution.
///
/// Should be read as a path inside the trait clauses which apply to the current
/// definition. Note that every path designated by `TraitInstanceId` refers
/// to a *trait instance*, which is why the [`TraitRefKind::Clause`] variant may seem redundant
/// with some of the other variants.
#[derive(
    Debug, Clone, SerializeState, DeserializeState, PartialEq, Eq, Hash, EnumIsA, Drive, DriveMut,
)]
pub enum TraitRefKind {
    /// A specific top-level implementation item.
    TraitImpl(TraitImplRef),

    /// One of the local clauses.
    ///
    /// Example:
    /// ```text
    /// fn f<T>(...) where T : Foo
    ///                    ^^^^^^^
    ///                    Clause(0)
    /// ```
    Clause(ClauseDbVar),

    /// A parent clause
    ///
    /// Example:
    /// ```text
    /// trait Foo1 {}
    /// trait Foo2 { fn f(); }
    ///
    /// trait Bar : Foo1 + Foo2 {}
    ///             ^^^^   ^^^^
    ///                    parent clause 1
    ///     parent clause 0
    ///
    /// fn g<T : Bar>(x : T) {
    ///   x.f()
    ///   ^^^^^
    ///   Parent(Clause(0), 1)::f(x)
    ///                     ^
    ///                     parent clause 1 of clause 0
    /// }
    /// ```
    ParentClause(Box<TraitRef>, TraitClauseId),

    /// A clause defined on an associated type. This variant is only used during translation; after
    /// the `lift_associated_item_clauses` pass, clauses on items become `ParentClause`s.
    ///
    /// Example:
    /// ```text
    /// trait Foo {
    ///   type W: Bar0 + Bar1 // Bar1 contains a method bar1
    ///                  ^^^^
    ///               this is the clause 1 applying to W
    /// }
    ///
    /// fn f<T : Foo>(x : T::W) {
    ///   x.bar1();
    ///   ^^^^^^^
    ///   ItemClause(Clause(0), W, 1)
    ///                         ^^^^
    ///                         clause 1 from item W (from local clause 0)
    /// }
    /// ```
    ItemClause(Box<TraitRef>, AssocTypeId, TraitClauseId),

    /// The implicit `Self: Trait` clause. Present inside trait declarations, including trait
    /// method declarations. Not present in trait implementations as we can use `TraitImpl` intead.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("Self"))]
    SelfId,

    /// A trait implementation that is computed by the compiler, such as for built-in trait
    /// `Sized`. This morally points to an invisible `impl` block; as such it contains
    /// the information we may need from one.
    ///
    /// Also used as a placeholder for trait clauses that were stripped by the
    /// `--remove-adt-clauses` pass: the original `Clause` reference is replaced with a
    /// `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }`. See
    /// [`BuiltinImplData::RemovedAdtClause`].
    BuiltinOrAuto {
        #[drive(skip)]
        builtin_data: BuiltinImplData,
        /// Exactly like the same field on `TraitImpl`: the `TraitRef`s required to satisfy the
        /// implied predicates on the trait declaration. E.g. since `FnMut: FnOnce`, a built-in `T:
        /// FnMut` impl would have a `TraitRef` for `T: FnOnce`.
        parent_trait_refs: IndexVec<TraitClauseId, TraitRef>,
        /// The values of the associated types for this trait.
        types: IndexMap<AssocTypeId, TraitAssocTyImpl>,
    },

    /// The automatically-generated implementation for `dyn Trait`.
    Dyn,

    /// For error reporting.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("UnknownTrait"))]
    #[drive(skip)]
    Unknown(String),
}

/// Describes a built-in impl. Mostly lists the implemented trait, sometimes with more details
/// about the contents of the implementation.
#[derive(Debug, Clone, SerializeState, DeserializeState, PartialEq, Eq, Hash, Drive, DriveMut)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Builtin"))]
pub enum BuiltinImplData {
    /// Auto traits (defined with `auto trait ...`, also `Unpin`).
    Auto,

    Sized,
    MetaSized,
    PointeeSized,

    Copy,
    Clone,

    Tuple,
    Transmute,
    Unsize,

    Pointee,
    DiscriminantKind,

    Fn,
    FnMut,
    FnOnce,
    FnPtr,
    AsyncFn,
    AsyncFnMut,
    AsyncFnOnce,
    Coroutine,
    Future,

    /// An impl of `Destruct` for a type with no drop glue.
    NoopDestruct,
    /// An impl of `Destruct` for a type parameter, which we could not resolve because
    /// `--add-drop-bounds` was not set.
    UntrackedDestruct,

    /// Placeholder used by the `--remove-adt-clauses` pass when it strips a trait clause from a
    /// type declaration. References to the removed clause are rewritten as
    /// `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }`.
    RemovedAdtClause,
}

/// A reference to a trait.
///
/// This type is hash-consed, `TraitRefContents` contains the actual data.
#[derive(Debug, Clone, SerializeState, DeserializeState, PartialEq, Eq, Hash, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct TraitRef(pub HashConsed<TraitRefContents>);

#[derive(Debug, Clone, SerializeState, DeserializeState, PartialEq, Eq, Hash, Drive, DriveMut)]
pub struct TraitRefContents {
    pub kind: TraitRefKind,
    /// Not necessary, but useful
    pub trait_decl_ref: PolyTraitDeclRef,
}

/// A predicate of the form `Type: Trait<Args>`.
///
/// About the generics, if we write:
/// ```text
/// impl Foo<bool> for String { ... }
/// ```
///
/// The substitution is: `[String, bool]`.
#[derive(Debug, Clone, SerializeState, DeserializeState, PartialEq, Eq, Hash, Drive, DriveMut)]
pub struct TraitDeclRef {
    pub id: TraitDeclId,
    pub generics: BoxedArgs,
}

/// A quantified trait predicate, e.g. `for<'a> Type<'a>: Trait<'a, Args>`.
pub type PolyTraitDeclRef = RegionBinder<TraitDeclRef>;

/// A reference to a tait impl, using the provided arguments.
#[derive(Debug, Clone, SerializeState, DeserializeState, PartialEq, Eq, Hash, Drive, DriveMut)]
pub struct TraitImplRef {
    pub id: TraitImplId,
    pub generics: BoxedArgs,
}

/// .0 outlives .1
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct OutlivesPred<T, U>(pub T, pub U);

pub type RegionOutlives = OutlivesPred<Region, Region>;
pub type TypeOutlives = OutlivesPred<Ty, Region>;

/// A constraint over a trait associated type.
///
/// Example:
/// ```text
/// T : Foo<S = String>
///         ^^^^^^^^^^
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct TraitTypeConstraint {
    pub trait_ref: TraitRef,
    pub type_id: AssocTypeId,
    pub ty: Ty,
}

/// A set of generic arguments.
#[derive(Clone, Eq, PartialEq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct GenericArgs {
    pub regions: IndexVec<RegionId, Region>,
    pub types: IndexVec<TypeVarId, Ty>,
    pub const_generics: IndexVec<ConstGenericVarId, ConstantExpr>,
    pub trait_refs: IndexVec<TraitClauseId, TraitRef>,
}

pub type BoxedArgs = Box<GenericArgs>;

/// A value of type `T` bound by regions. We should use `binder` instead but this causes name clash
/// issues in the derived ocaml visitors.
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct RegionBinder<T> {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_regions"))]
    #[serde_state(stateless)]
    pub regions: IndexVec<RegionId, RegionParam>,
    /// Named this way to highlight accesses to the inner value that might be handling parameters
    /// incorrectly. Prefer using helper methods.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_value"))]
    pub skip_binder: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("BK"))]
pub enum BinderKind {
    /// The parameters of a generic associated type.
    TraitType(TraitDeclId, AssocTypeId),
    /// The parameters of a trait method. Used in the `methods` lists in trait decls and trait
    /// impls.
    TraitMethod(TraitDeclId, TraitMethodId),
    /// The parameters bound in a non-trait `impl` block. Used in the `Name`s of inherent methods.
    InherentImplBlock,
    /// Binder used for `dyn Trait` existential predicates.
    Dyn,
    /// Some other use of a binder outside the main Charon ast.
    Other,
}

/// A value of type `T` bound by generic parameters. Used in any context where we're adding generic
/// parameters that aren't on the top-level item, e.g. `for<'a>` clauses (uses `RegionBinder` for
/// now), trait methods, GATs (TODO).
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct Binder<T> {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_params"))]
    pub params: GenericParams,
    /// Named this way to highlight accesses to the inner value that might be handling parameters
    /// incorrectly. Prefer using helper methods.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_value"))]
    pub skip_binder: T,
    /// The kind of binder this is.
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)]
    pub kind: BinderKind,
}

/// Generic parameters for a declaration, including predicates.
#[derive(
    Default, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut,
)]
pub struct GenericParams {
    #[serde_state(stateless)]
    pub regions: IndexVec<RegionId, RegionParam>,
    #[serde_state(stateless)]
    pub types: IndexVec<TypeVarId, TypeParam>,
    pub const_generics: IndexVec<ConstGenericVarId, ConstGenericParam>,
    // TODO: rename to match [GenericArgs]?
    pub trait_clauses: IndexVec<TraitClauseId, TraitParam>,
    /// The first region in the pair outlives the second region
    pub regions_outlive: Vec<RegionBinder<RegionOutlives>>,
    /// The type outlives the region
    pub types_outlive: Vec<RegionBinder<TypeOutlives>>,
    /// Constraints over trait associated types
    pub trait_type_constraints: IndexVec<TraitTypeConstraintId, RegionBinder<TraitTypeConstraint>>,
}

/// Where a given predicate came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub enum PredicateOrigin {
    // Note: we use this for globals too, but that's only available with an unstable feature.
    // ```
    // fn function<T: Clone>() {}
    // fn function<T>() where T: Clone {}
    // const NONE<T: Copy>: Option<T> = None;
    // ```
    WhereClauseOnFn,
    // ```
    // struct Struct<T: Clone> {}
    // struct Struct<T> where T: Clone {}
    // type TypeAlias<T: Clone> = ...;
    // ```
    WhereClauseOnType,
    // Note: this is both trait impls and inherent impl blocks.
    // ```
    // impl<T: Clone> Type<T> {}
    // impl<T> Type<T> where T: Clone {}
    // impl<T> Trait for Type<T> where T: Clone {}
    // ```
    WhereClauseOnImpl,
    // The special `Self: Trait` clause which is in scope inside the definition of `Foo` or an
    // implementation of it.
    // ```
    // trait Trait {}
    // ```
    TraitSelf,
    // Note: this also includes supertrait constraints.
    // ```
    // trait Trait<T: Clone> {}
    // trait Trait<T> where T: Clone {}
    // trait Trait: Clone {}
    // ```
    WhereClauseOnTrait,
    // ```
    // trait Trait {
    //     type AssocType: Clone;
    // }
    // ```
    TraitItem(AssocTypeId),
    /// Clauses that are part of a `dyn Trait` type.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("OriginDyn"))]
    Dyn,
}

// rustc counts bytes in layouts as u64
pub type ByteCount = u64;

/// Simplified layout of a single variant.
///
/// Maps fields to their offset within the layout.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub struct VariantLayout {
    /// The offset of each field.
    #[drive(skip)]
    pub field_offsets: IndexVec<FieldId, ByteCount>,
    /// Whether the variant is uninhabited, i.e. has any valid possible value.
    /// Note that uninhabited types can have arbitrary layouts.
    #[drive(skip)]
    pub uninhabited: bool,
    /// How to write the tag when constructing this variant. Each entry means: write `value` at
    /// byte `offset`. Mirrors MiniRust's `Variant::tagger`.
    #[drive(skip)]
    pub tagger: Vec<(ByteCount, ScalarValue)>,
}

/// Decision tree used to determine the active variant by reading memory. Mirrors MiniRust's
/// `Discriminator`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Discriminator {
    /// The variant is known.
    Known(VariantId),
    /// No valid variant (e.g., invalid tag value).
    Invalid,
    /// Branch on an integer value read from memory at `offset`.
    Branch {
        /// Byte offset to read from.
        offset: ByteCount,
        /// Integer type to read.
        int_ty: IntegerTy,
        /// If the integer is in one of these ranges, continue with the given `Discriminator`. The
        /// ranges are sorted.
        children: Vec<(std::ops::RangeInclusive<ScalarValue>, Discriminator)>,
        /// Fallback if no range in `children` matches.
        fallback: Box<Discriminator>,
    },
}

/// Simplified type layout information.
///
/// Does not include information about niches.
/// If the type does not have a fully known layout (e.g. it is ?Sized)
/// some of the layout parts are not available.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
)]
#[serde_state(stateless)]
pub struct Layout {
    /// The size of the type in bytes.
    #[drive(skip)]
    pub size: Option<ByteCount>,
    /// The alignment, in bytes.
    #[drive(skip)]
    pub align: Option<ByteCount>,
    /// Decision tree that determines the active variant by reading memory. Only `Some` for enums.
    #[drive(skip)]
    pub discriminator: Option<Discriminator>,
    /// Whether the type is uninhabited, i.e. has any valid value at all.
    /// Note that uninhabited types can have arbitrary layouts: `(u32, !)` has space for the `u32`
    /// and `enum E2 { A, B(!), C(i32, !) }` may have space for a discriminant.
    #[drive(skip)]
    pub uninhabited: bool,
    /// Map from `VariantId` to the corresponding field layouts. Some variants don't have a
    /// meaningful layout due to being uninhabited (though an uninhabited variant may have a
    /// layout). Structs and unions are modeled as having exactly one variant.
    pub variant_layouts: IndexVec<VariantId, Option<VariantLayout>>,
    /// The representation options of this type declaration as annotated by the user.
    #[drive(skip)]
    #[serde_state(stateless)]
    pub repr: ReprOptions,
}

/// The metadata stored in a pointer. That's the information stored in pointers alongside
/// their address. It's empty for `Sized` types, and interesting for unsized
/// aka dynamically-sized types.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut, Hash)]
#[serde_state(default_state = ())]
pub enum PtrMetadata {
    /// Types that need no metadata, namely `T: Sized` types.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("NoMetadata"))]
    None,
    /// Metadata for `[T]` and `str`, and user-defined types
    /// that directly or indirectly contain one of the two.
    /// Of type `usize`.
    /// Notably, length for `[T]` denotes the number of elements in the slice.
    /// While for `str` it denotes the number of bytes in the string.
    Length,
    /// Metadata for `dyn Trait`, referring to the vtable struct. Has type `&'static vtable`
    VTable(TypeDeclRef),
    /// Unknown due to generics, but will inherit from the given type.
    /// This is consistent with `<Ty as Pointee>::Metadata`.
    /// Of type `TyKind::Metadata(Ty)`.
    InheritFrom(Ty),
}

/// Describes which layout algorithm is used for representing the corresponding type.
/// Depends on the `#[repr(...)]` used.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReprAlgorithm {
    /// The default layout algorithm. Used without an explicit `ŗepr` or for `repr(Rust)`.
    #[default]
    Rust,
    /// The C layout algorithm as enforced by `repr(C)`.
    C,
}

/// Describes modifiers to the alignment and packing of the corresponding type.
/// Represents `repr(align(n))` and `repr(packed(n))`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum AlignmentModifier {
    Align(ByteCount),
    Pack(ByteCount),
}

/// The representation options as annotated by the user.
///
/// NOTE: This does not include less common/unstable representations such as `#[repr(simd)]`
/// or the compiler internal `#[repr(linear)]`. Similarly, enum discriminant representations
/// are encoded in [`Variant::discriminant`] and [`Discriminator`] instead.
/// This only stores whether the discriminant type was derived from an explicit annotation.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReprOptions {
    pub repr_algo: ReprAlgorithm,
    pub align_modif: Option<AlignmentModifier>,
    pub transparent: bool,
    pub explicit_discr_type: bool,
}

/// A type declaration.
///
/// Types can be opaque or transparent.
///
/// Transparent types are local types not marked as opaque.
/// Opaque types are the others: local types marked as opaque, and non-local
/// types (coming from external dependencies).
///
/// In case the type is transparent, the declaration also contains the
/// type definition (see [TypeDeclKind]).
///
/// A type can only be an ADT (structure or enumeration), as type aliases are
/// inlined in MIR.
#[derive(Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub struct TypeDecl {
    pub def_id: TypeDeclId,
    /// Meta information associated with the item.
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    /// The context of the type: distinguishes top-level items from closure-related items.
    pub src: ItemSource,
    /// The type kind: enum, struct, or opaque.
    pub kind: TypeDeclKind,
    /// The layout of the type for each target. Information may be partial because of generics or
    /// dynamically-sized types. If we cannot compute a layout, the target has no entry.
    #[serde(with = "SeqHashMapToArray::<TargetTriple, Layout>")]
    pub layout: SeqHashMap<TargetTriple, Layout>,
    /// The metadata associated with a pointer to the type.
    pub ptr_metadata: PtrMetadata,
}

generate_index_type!(VariantId, "Variant");
generate_index_type!(FieldId, "Field");

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    EnumIsA,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
)]
pub enum TypeDeclKind {
    Struct(IndexVec<FieldId, Field>),
    Enum(IndexVec<VariantId, Variant>),
    Union(IndexVec<FieldId, Field>),
    /// An opaque type.
    ///
    /// Either a local type marked as opaque, or an external type.
    Opaque,
    /// An alias to another type. This only shows up in the top-level list of items, as rustc
    /// inlines uses of type aliases everywhere else.
    Alias(Ty),
    /// Used if an error happened during the extraction, and we don't panic
    /// on error.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TDeclError"))]
    #[drive(skip)]
    Error(String),
}

#[derive(Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(stateless)]
pub struct Variant {
    pub id: VariantId,
    pub span: Span,
    #[drive(skip)]
    pub attr_info: AttrInfo,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("variant_name"))]
    #[drive(skip)]
    pub name: String,
    #[serde_state(stateful)]
    pub fields: IndexVec<FieldId, Field>,
    /// The discriminant value outputted by `std::mem::discriminant` for this variant. This can be
    /// different than the value stored in memory (called `tag`); that one is described by
    /// [`Discriminator`] and [`VariantLayout::tagger`].
    pub discriminant: Literal,
}

#[derive(Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(stateless)]
pub struct Field {
    pub span: Span,
    #[drive(skip)]
    pub attr_info: AttrInfo,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("field_name"))]
    #[drive(skip)]
    pub name: Option<String>,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("field_ty"))]
    #[serde_state(stateful)]
    pub ty: Ty,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
pub enum UIntTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("IntegerType"))]
pub enum IntegerTy {
    Signed(IntTy),
    Unsigned(UIntTy),
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("FloatType"))]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    Hash,
    VariantName,
    EnumIsA,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
#[serde_state(stateless)]
pub enum RefKind {
    Mut,
    Shared,
}

/// The nature of locations where a given lifetime parameter is used. If this lifetime ever flows
/// to be used as the lifetime of a mutable reference `&'a mut` then we consider it mutable.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, EnumIsA,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Lt"))]
pub enum LifetimeMutability {
    /// A lifetime that is used for a mutable reference.
    Mutable,
    /// A lifetime used only in shared references.
    Shared,
    /// A lifetime for which we couldn't/didn't compute mutability.
    Unknown,
}

/// Type identifier.
///
/// Allows us to factorize the code for built-in types, adts and tuples
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    VariantName,
    EnumAsGetters,
    EnumIsA,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum TypeId {
    /// A "regular" ADT type.
    ///
    /// Includes transparent ADTs and opaque ADTs (local ADTs marked as opaque,
    /// and external ADTs).
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TAdtId"))]
    Adt(TypeDeclId),
    Tuple,
    /// Built-in type. Either a primitive type like array or slice, or a
    /// non-primitive type coming from a standard library
    /// and that we handle like a primitive type. Types falling into this
    /// category include: Box, Vec, Cell...
    /// The Array and Slice types were initially modelled as primitive in
    /// the [Ty] type. We decided to move them to built-in types as it allows
    /// for more uniform treatment throughout the codebase.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TBuiltin"))]
    #[serde_state(stateless)]
    Builtin(BuiltinTy),
}

/// Reference to a type declaration or builtin type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct TypeDeclRef {
    pub id: TypeId,
    pub generics: BoxedArgs,
}

/// Types of primitive values. Either an integer, bool, char
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    VariantIndexArity,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("LiteralType"))]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
#[serde_state(stateless)]
pub enum LiteralTy {
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    Bool,
    Char,
}

/// A type.
///
/// Warning: the `DriveMut` impls of `Ty` needs to clone and re-hash the modified type to maintain
/// the hash-consing invariant. This is expensive, avoid visiting types mutably when not needed.
#[derive(Debug, Clone, Hash, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct Ty(pub HashConsed<TyKind>);

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    Hash,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    VariantIndexArity,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum TyKind {
    /// An ADT.
    /// Note that here ADTs are very general. They can be:
    /// - user-defined ADTs
    /// - tuples (including `unit`, which is a 0-tuple)
    /// - built-in types (includes some primitive types, e.g., arrays or slices)
    ///
    /// The information on the nature of the ADT is stored in (`TypeId`)[TypeId].
    /// The last list is used encode const generics, e.g., the size of an array
    ///
    /// Note: this is incorrectly named: this can refer to any valid `TypeDecl` including extern
    /// types.
    Adt(TypeDeclRef),
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TVar"))]
    TypeVar(TypeDbVar),
    Literal(LiteralTy),
    /// The never type, for computations which don't return. It is sometimes
    /// necessary for intermediate variables. For instance, if we do (coming
    /// from the rust documentation):
    /// ```text
    /// let num: u32 = match get_a_number() {
    ///     Some(num) => num,
    ///     None => break,
    /// };
    /// ```
    /// the second branch will have type `Never`. Also note that `Never`
    /// can be coerced to any type.
    ///
    /// Note that we eliminate the variables which have this type in a micro-pass.
    /// As statements don't have types, this type disappears eventually disappears
    /// from the AST.
    Never,
    // We don't support floating point numbers on purpose (for now)
    /// A borrow
    Ref(Region, Ty, RefKind),
    /// A raw pointer.
    RawPtr(Ty, RefKind),
    /// A trait associated type
    ///
    /// Ex.:
    /// ```text
    /// trait Foo {
    ///   type Bar; // type associated to the trait Foo
    /// }
    /// ```
    TraitType(TraitRef, AssocTypeId, GenericArgs),
    /// `dyn Trait`
    DynTrait(DynPredicate),
    /// Function pointer type. This is a literal pointer to a region of memory that
    /// contains a callable function.
    /// This is a function signature with limited generics: it only supports lifetime generics, not
    /// other kinds of generics.
    FnPtr(RegionBinder<FunSig>),
    /// The unique type associated with each function item. Each function item is given
    /// a unique generic type that takes as input the function's early-bound generics. This type
    /// is not generally nameable in Rust; it's a ZST (there's a unique value), and a value of that type
    /// can be cast to a function pointer or passed to functions that expect `FnOnce`/`FnMut`/`Fn` parameters.
    /// There's a binder here because charon function items take both early and late-bound
    /// lifetimes as arguments; given that the type here is polymorpohic in the late-bound
    /// variables (those that could appear in a function pointer type like `for<'a> fn(&'a u32)`),
    /// we need to bind them here.
    FnDef(RegionBinder<FnPtr>),
    /// As a marker of taking out metadata from a given type
    /// The internal type is assumed to be a type variable
    PtrMetadata(Ty),
    /// An array type `[T; N]`
    Array(Ty, Box<ConstantExpr>),
    /// A slice type `[T]`
    Slice(Ty),
    /// A pattern type. This is a newtype over the first type whose valid values are restricted by
    /// the pattern.
    Pattern(Ty, TypePattern),
    /// A type that could not be computed or was incorrect.
    #[drive(skip)]
    Error(String),
}

/// Builtin types identifiers.
///
/// WARNING: for now, all the built-in types are covariant in the generic
/// parameters (if there are). Adding types which don't satisfy this
/// will require to update the code abstracting the signatures (to properly
/// take into account the lifetime constraints).
///
/// TODO: update to not hardcode the types (except `Box` maybe) and be more
/// modular.
/// TODO: move to builtins.rs?
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum BuiltinTy {
    /// Boxes are de facto a primitive type.
    Box,
    /// Primitive type
    Str,
}

#[derive(
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

impl ClosureKind {
    // pub fn trait_name(self) -> &'static str {}
    pub fn method_name(self) -> &'static str {
        match self {
            ClosureKind::FnOnce => "call_once",
            ClosureKind::FnMut => "call_mut",
            ClosureKind::Fn => "call",
        }
    }
}

/// Additional information for closures.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct ClosureInfo {
    #[serde_state(stateless)]
    pub kind: ClosureKind,
    /// The `FnOnce` implementation of this closure -- always exists.
    pub fn_once_impl: RegionBinder<TraitImplRef>,
    /// The `FnMut` implementation of this closure, if any.
    pub fn_mut_impl: Option<RegionBinder<TraitImplRef>>,
    /// The `Fn` implementation of this closure, if any.
    pub fn_impl: Option<RegionBinder<TraitImplRef>>,
    /// The signature of the function that this closure represents.
    pub signature: RegionBinder<FunSig>,
}

/// A function signature.
#[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct FunSig {
    /// Is the function unsafe or not
    #[drive(skip)]
    pub is_unsafe: bool,
    /// The calling convention of this function.
    #[drive(skip)]
    pub abi: Abi,
    pub inputs: Vec<Ty>,
    pub output: Ty,
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    Hash,
    VariantName,
    EnumIsA,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
)]
#[serde_state(stateless)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Abi"))]
pub enum Abi {
    Rust,
    C,
    /// Rust's spelling for the ABI, e.g. "C-unwind" or "system".
    Other(#[drive(skip)] ustr::Ustr),
}

impl Abi {
    pub fn rust() -> Self {
        Self::Rust
    }

    pub fn rust_name(&self) -> &str {
        match self {
            Self::Rust => "Rust",
            Self::C => "C",
            Self::Other(name) => name.as_str(),
        }
    }
}

/// The contents of a `dyn Trait` type.
#[derive(Debug, Clone, Hash, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
pub struct DynPredicate {
    /// This binder binds a single type `T`, which is considered existentially quantified. The
    /// predicates in the binder apply to `T` and represent the `dyn Trait` constraints.
    /// E.g. `dyn Iterator<Item=u32> + Send` is represented as `exists<T: Iterator<Item=u32> + Send> T`.
    ///
    /// Only the first trait clause may have methods. We use the vtable of this trait in the `dyn
    /// Trait` pointer metadata.
    pub binder: Binder<Ty>,
}

/// A type-level pattern used by [`TyKind::Pattern`].
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    Hash,
    VariantName,
    EnumIsA,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
)]
#[serde_state(state_implements = HashConsSerializerState)] // Avoid corecursive impls due to perfect derive
pub enum TypePattern {
    Range(Box<ConstantExpr>, Box<ConstantExpr>),
    OrPattern(Vec<TypePattern>),
    NotNull,
}
