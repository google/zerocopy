use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

/// A type.
///
/// This is an interned value; see `TyKind` for the actual contents.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(state_implements = DedupSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct Ty(pub HashConsed<WithCachedTypeInfo<TyKind>>);

/// A type.
///
/// This is interned as `Ty`, making it cheap to clone and compare.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantName, EnumIsA, EnumAsGetters, EnumToGetters, VariantIndexArity)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum TyKind {
    /// A scalar (integers, floats, `char`, or `bool`).
    Scalar(ScalarTy),
    /// An array `[T; N]`. The third field is the proof that `T: Sized`; it is absent with
    /// `--hide-marker-traits`.
    Array(Ty, ConstantExpr, Option<TraitRef>),
    /// A slice `[T]`. The second field is the proof that `T: Sized`; it is absent with
    /// `--hide-marker-traits`.
    Slice(Ty, Option<TraitRef>),
    /// An ADT: structs, enums, unions, as well as tuples and `str`.
    Adt(TypeDeclRef),
    /// A reference: `&T` or `&mut T`.
    Ref(Region, Ty, RefKind),
    /// A raw pointer.
    RawPtr(Ty, RefKind),
    /// The unique type associated with each function item. Each function item is given a unique
    /// type that has the function's early-bound generics. This type is not generally nameable in
    /// Rust; it's a ZST (there's a unique value), and a value of that type can be cast to a
    /// function pointer or passed to functions that expect `FnOnce`/`FnMut`/`Fn` parameters.
    ///
    /// There's a binder here because charon function items take both early and late-bound
    /// lifetimes as arguments; given that the type we're pointing to is polymorphic in the
    /// late-bound variables, we need to bind them here.
    ///
    /// ```rust
    /// // `'a` is early-bound, 'b is late-bound.
    /// fn foo<'a, 'b>(x: &'a u32, y: &'b u32)
    /// where u32: 'b
    /// {}
    /// ```
    /// For rustc, there's a ZST `foo<'a>`, that can be cast to a `for<'b> fn(&'a u32, &'b u32)`
    /// function pointer.
    /// For charon, there's an item `foo<'a, 'b>`, and the `FnDef` item that corresponds to rustc's
    /// `foo<'a>` is represented as `FnDef(for<'b> foo<'a, 'b>)`.
    FnDef(RegionBinder<FnPtr>),
    /// Function pointer type. This is a literal pointer to a region of memory that contains a
    /// callable function.
    ///
    /// A function pointer can have lifetime generics, e.g. `for<'a> fn(&'a mut u32) -> &'a u32`,
    /// hence the binder.
    FnPtr(RegionBinder<FunSig>),
    /// `dyn Trait`: erased value known to implement `Trait`. A pointer to it will carry a vtable
    /// pointer that stores the methods that can be called on this value.
    DynTrait(DynPredicate),
    /// A pattern type: a type that is representationally identical to its base type, except the
    /// only valid values are the ones that match the pattern.
    Pattern(Ty, TypePattern),
    /// The never type, the canonical uninhabited type.
    Never,

    /// A type variable.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TVar"))]
    TypeVar(TypeDbVar),
    /// A trait associated type: `<T as Trait>::AssocType<Args>`.
    TraitType(TraitRef, AssocTypeId, GenericArgs),
    /// The type of pointer metadata for the given type; e.g. for `[T]`, this type is `usize`. The
    /// way to write this type in Rust is `<X as core::ptr::Pointee>::Metadata`.
    PtrMetadata(Ty),

    /// A type that could not be computed or was incorrect.
    Error(String),
}

/// Types of primitive scalar values.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantName, EnumIsA, EnumAsGetters, VariantIndexArity)]
#[derive(
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("ScalarType"))]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
#[serde_state(stateless)]
pub enum ScalarTy {
    Integer(IntegerTy),
    Float(FloatTy),
    Bool,
    Char,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumIsA, VariantName)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("IntegerType"))]
pub enum IntegerTy {
    Signed(IntTy),
    Unsigned(UIntTy),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumIsA, VariantName)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumIsA, VariantName)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub enum UIntTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumIsA, VariantName)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("FloatType"))]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

/// Builtin ADT identifiers.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumIsA, EnumAsGetters, VariantName)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum BuiltinAdt {
    /// A tuple `(A, B, ...)`, including `unit`.
    Tuple,
    /// Boxes; always detected, though they are only treated as primitives with `--treat-box-as-builtin`
    Box,
    /// The `str` type, which corresponds to a `[u8]` that encodes a string with UTF-8.
    Str,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantName, EnumIsA)]
#[derive(
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
#[serde_state(stateless)]
pub enum RefKind {
    Mut,
    Shared,
}

/// The contents of a `dyn Trait` type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantName, EnumIsA)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(state_implements = DedupSerializerState)] // Avoid corecursive impls due to perfect derive
pub enum TypePattern {
    Range(ConstantExpr, ConstantExpr),
    OrPattern(Vec<TypePattern>),
    NotNull,
}

macro_rules! static_type {
    ($e:expr) => {{
        use std::sync::LazyLock;
        static TY: LazyLock<Ty> = LazyLock::new(|| $e.into_ty());
        TY.clone()
    }};
}

impl Ty {
    pub fn new(kind: TyKind) -> Self {
        Ty(HashConsed::new(WithCachedTypeInfo::new(kind)))
    }

    pub fn kind(&self) -> &TyKind {
        self.0.inner()
    }

    pub fn with_kind_mut<R>(&mut self, f: impl FnOnce(&mut TyKind) -> R) -> R {
        self.0.with_inner_mut(|kind| kind.with_value_mut(f))
    }

    /// Return the unit type
    pub fn mk_unit() -> Ty {
        static_type!(TyKind::Adt(TypeDeclRef {
            id: TypeDeclId::UNIT,
            generics: Box::new(GenericArgs::empty()),
            builtin: Some(BuiltinAdt::Tuple),
        }))
    }

    pub fn mk_bool() -> Ty {
        static_type!(TyKind::Scalar(ScalarTy::Bool))
    }

    pub fn mk_usize() -> Ty {
        static_type!(TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(
            UIntTy::Usize
        ))))
    }

    pub fn mk_array(ty: Ty, len: ConstantExpr, ty_is_sized: Option<TraitRef>) -> Ty {
        TyKind::Array(ty, len, ty_is_sized).into_ty()
    }

    pub fn mk_slice(ty: Ty, ty_is_sized: Option<TraitRef>) -> Ty {
        TyKind::Slice(ty, ty_is_sized).into_ty()
    }

    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        *self == Ty::mk_unit()
    }

    pub fn get_ptr_metadata(&self, translated: &TranslatedCrate) -> PtrMetadata {
        let ty_decls = &translated.type_decls;
        match self.kind() {
            TyKind::Pattern(ty, _) => ty.get_ptr_metadata(translated),
            TyKind::Adt(ty_ref) => {
                // there are two cases:
                // 1. if the declared type has a fixed metadata, just returns it
                // 2. if it depends on some other types or the generic itself
                let Some(decl) = ty_decls.get(ty_ref.id) else {
                    return PtrMetadata::InheritFrom(self.clone());
                };
                match decl.ptr_metadata.clone().substitute(&ty_ref.generics) {
                    // if it depends on some type, recursion with the binding env
                    PtrMetadata::InheritFrom(ty) => ty.get_ptr_metadata(translated),
                    // otherwise, simply return it
                    meta => meta,
                }
            }
            TyKind::DynTrait(pred) => match pred.vtable_ref(translated) {
                Some(vtable) => PtrMetadata::VTable(vtable),
                None => PtrMetadata::InheritFrom(self.clone()),
            },
            // `[T]` has metadata length
            TyKind::Slice(..) => PtrMetadata::Length,
            TyKind::TraitType(..) | TyKind::TypeVar(_) => PtrMetadata::InheritFrom(self.clone()),
            TyKind::Scalar(_)
            | TyKind::Never
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::FnPtr(..)
            | TyKind::FnDef(..)
            | TyKind::Array(..)
            | TyKind::Error(_) => PtrMetadata::None,
            // The metadata itself must be Sized, hence must with `PtrMetadata::None`
            TyKind::PtrMetadata(_) => PtrMetadata::None,
        }
    }

    /// The field types of a tuple, in order. Panics if the type is not a tuple,
    /// or if the type declaration is not found in the crate.
    pub fn as_tuple_fields(&self, translated: &TranslatedCrate) -> Vec<Ty> {
        let Some(tref) = self.as_adt().filter(|tref| tref.is_tuple()) else {
            unreachable!("as_tuple_fields called on non-tuple type {:?}", self);
        };

        // Avoid doing a substitution if the tuple is polymorphic and we can just
        // retrieve the fields from the generics, since substitutions won't work
        // in case `--unbind-item-vars` is set.
        let is_instantiated = translated
            .item_names
            .get(&ItemId::Type(tref.id))
            .map(|name| name.name.iter().any(|elem| elem.is_instantiated()))
            .unwrap_or(false);
        if !is_instantiated {
            return tref.generics.types.as_vec().clone();
        }

        translated
            .type_decls
            .get(tref.id)
            .and_then(|decl| decl.kind.as_struct())
            .expect("the declaration of specialized tuple {tref:?} is missing")
            .iter()
            .map(|f| f.ty.clone().substitute(&tref.generics))
            .collect()
    }

    pub fn as_adt(&self) -> Option<&TypeDeclRef> {
        self.kind().as_adt()
    }
}

impl TyKind {
    pub fn into_ty(self) -> Ty {
        Ty::new(self)
    }

    pub fn is_usize(&self) -> bool {
        matches!(
            self,
            TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::Usize)))
        )
    }

    pub fn is_unsigned_scalar(&self) -> bool {
        match self {
            TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(_))) => true,
            TyKind::Pattern(ty, _) => ty.is_unsigned_scalar(),
            _ => false,
        }
    }

    pub fn is_signed_scalar(&self) -> bool {
        match self {
            TyKind::Scalar(ScalarTy::Integer(IntegerTy::Signed(_))) => true,
            TyKind::Pattern(ty, _) => ty.is_signed_scalar(),
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, TyKind::Scalar(ScalarTy::Bool))
    }

    pub fn is_str(&self) -> bool {
        match self {
            TyKind::Adt(ty_ref) => ty_ref.is_str(),
            _ => false,
        }
    }

    /// Return true if the type is Box
    pub fn is_box(&self) -> bool {
        match self {
            TyKind::Adt(ty_ref) => ty_ref.is_box(),
            _ => false,
        }
    }

    pub fn is_tuple(&self) -> bool {
        match self {
            TyKind::Adt(ty_ref) => ty_ref.is_tuple(),
            _ => false,
        }
    }

    pub fn as_adt_id(&self) -> Option<TypeDeclId> {
        self.as_adt().map(|a| a.id)
    }

    pub fn as_box(&self) -> Option<&Ty> {
        match self {
            TyKind::Adt(ty_ref) if ty_ref.is_box() => Some(&ty_ref.generics.types[0]),
            _ => None,
        }
    }

    pub fn as_box_mut(&mut self) -> Option<&mut Ty> {
        match self {
            TyKind::Adt(ty_ref) if ty_ref.is_box() => Some(&mut ty_ref.generics.types[0]),
            _ => None,
        }
    }

    pub fn builtin_deref(&self) -> Option<&Ty> {
        match self {
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(ty),
            TyKind::Adt(ty_ref) if ty_ref.is_box() => Some(&ty_ref.generics.types[0]),
            _ => None,
        }
    }

    pub fn builtin_deref_mut(&mut self) -> Option<&mut Ty> {
        match self {
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(ty),
            TyKind::Adt(ty_ref) if ty_ref.is_box() => Some(&mut ty_ref.generics.types[0]),
            _ => None,
        }
    }

    pub fn as_array_or_slice(&self) -> Option<&Ty> {
        match self {
            TyKind::Slice(ty, _) | TyKind::Array(ty, ..) => Some(ty),
            _ => None,
        }
    }

    pub fn as_array_or_slice_mut(&mut self) -> Option<&mut Ty> {
        match self {
            TyKind::Slice(ty, _) | TyKind::Array(ty, ..) => Some(ty),
            _ => None,
        }
    }
}

impl IntegerTy {
    pub fn to_unsigned(&self) -> Self {
        match self {
            IntegerTy::Signed(IntTy::Isize) => IntegerTy::Unsigned(UIntTy::Usize),
            IntegerTy::Signed(IntTy::I8) => IntegerTy::Unsigned(UIntTy::U8),
            IntegerTy::Signed(IntTy::I16) => IntegerTy::Unsigned(UIntTy::U16),
            IntegerTy::Signed(IntTy::I32) => IntegerTy::Unsigned(UIntTy::U32),
            IntegerTy::Signed(IntTy::I64) => IntegerTy::Unsigned(UIntTy::U64),
            IntegerTy::Signed(IntTy::I128) => IntegerTy::Unsigned(UIntTy::U128),
            _ => *self,
        }
    }

    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self, ptr_size: ByteCount) -> usize {
        match self {
            IntegerTy::Signed(ty) => ty.target_size(ptr_size),
            IntegerTy::Unsigned(ty) => ty.target_size(ptr_size),
        }
    }
}

impl ScalarTy {
    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self, ptr_size: ByteCount) -> usize {
        match self {
            ScalarTy::Integer(int_ty) => int_ty.target_size(ptr_size),
            ScalarTy::Float(float_ty) => float_ty.target_size(),
            ScalarTy::Char => 4,
            ScalarTy::Bool => 1,
        }
    }
}

impl RefKind {
    pub fn mutable(x: bool) -> Self {
        if x { Self::Mut } else { Self::Shared }
    }
}

impl DynPredicate {
    /// Get a reference to the vtable type that corresponds to this predicate.
    pub fn vtable_ref(&self, translated: &TranslatedCrate) -> Option<TypeDeclRef> {
        let dyn_ty = TyKind::DynTrait(self.clone()).into_ty();
        // The first clause is the one relevant for the vtable. We're extracting it from our binder
        // so must give a value for the `Self` type.
        let relevant_tref = self.binder.params.trait_clauses[0]
            .trait_
            .clone()
            .erase()
            .substitute(&GenericArgs::new_types([dyn_ty].into()));

        // Get the vtable ref from the trait decl
        let trait_decl = translated.trait_decls.get(relevant_tref.id)?;
        let vtable_ref = trait_decl
            .vtable
            .clone()?
            .substitute_with_self(&relevant_tref.generics, &TraitRefKind::Dyn);
        Some(vtable_ref)
    }
}

impl From<ScalarTy> for Ty {
    fn from(value: ScalarTy) -> Self {
        TyKind::Scalar(value).into_ty()
    }
}

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Ty {
        kind.into_ty()
    }
}

/// Convenience impl.
impl std::ops::Deref for Ty {
    type Target = WithCachedTypeInfo<TyKind>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Dummy impl, only there to avoid overflow computing whether our types are `Send` given the giant
/// recursive knot of types we have.
unsafe impl Send for Ty {}
