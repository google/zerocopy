use std::fmt::Debug;

use quote::ToTokens;

/// The generic marker trait for our system.
/// This uses GATs to define how primitives behave in this mode.

/// Types that can be mirrored into a thread-safe representation.
pub trait Mirror {
    type Image: Debug + Clone + Send + 'static;
    fn mirror(&self) -> Self::Image;
}

pub trait ThreadSafety: 'static + Sized + Copy + Debug {
    /// How this mode handles underlying non-thread-safe AST node representation.
    type Node<T: Mirror + Clone + Debug>: Debug + Clone;

    /// A generic transform trait to move data from the current representation
    /// to the canonical "ThreadSafe" representation.
    ///
    /// If we are already Safe, this is identity.
    /// If we are Local, this erases the contents into `()`.
    fn lift_node<T: Mirror + Clone + Debug>(node: Self::Node<T>) -> <Safe as ThreadSafety>::Node<T>
    where
        T: Debug;
}

// --- Mode 1: Non-Thread-Safe (Fast, Local) ---
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Local;

impl ThreadSafety for Local {
    // Retains full node payload natively
    type Node<T: Mirror + Clone + Debug> = T;

    fn lift_node<T: Mirror + Clone + Debug>(node: Self::Node<T>) -> <Safe as ThreadSafety>::Node<T>
    where
        T: Debug,
    {
        node.mirror()
    }
}

// --- Mode 2: Thread-Safe (Send + Sync) ---
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Safe;

impl ThreadSafety for Safe {
    // Erases nodes completely
    type Node<T: Mirror + Clone + Debug> = T::Image;

    fn lift_node<T: Mirror + Clone + Debug>(node: Self::Node<T>) -> <Safe as ThreadSafety>::Node<T>
    where
        T: Debug,
    {
        // Already safe; just return ()
        node
    }
}

/// Types implement this to describe how they turn into their Send-able version.
pub trait LiftToSafe {
    /// The thread-safe equivalent of Self.
    /// Crucially, this type must be Send.
    type Target: Send + Debug;

    /// Consumes the current version and produces the thread-safe version.
    fn lift(self) -> Self::Target;
}

/// A "Leaf" type that adapts its internal storage based on M.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstNode<T: Mirror + Clone + std::fmt::Debug, M: ThreadSafety = Local> {
    pub inner: M::Node<T>,
}

impl<T: Mirror + Clone + std::fmt::Debug> AstNode<T, Local> {
    pub fn new(val: T) -> Self {
        Self { inner: val }
    }
}

impl<T: Mirror + Clone + std::fmt::Debug, M> LiftToSafe for AstNode<T, M>
where
    T: Debug + 'static,
    M: ThreadSafety,
{
    // The target is ALWAYS the Safe version
    type Target = AstNode<T, Safe>;

    fn lift(self) -> Self::Target {
        AstNode { inner: M::lift_node(self.inner) }
    }
}

// =========================================================================
//  Safe AST Mirrors
//  These structs replace `syn` types in the Safe mode.
// =========================================================================

// --- Span ---
// We don't need the raw Span for generation, only for error reporting which happens earlier.
impl Mirror for proc_macro2::Span {
    type Image = ();
    fn mirror(&self) -> Self::Image {
        ()
    }
}

// --- Identifiers & Paths ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeIdent(pub String);

impl Mirror for syn::Ident {
    type Image = SafeIdent;
    fn mirror(&self) -> Self::Image {
        SafeIdent(self.to_string())
    }
}

// --- Types ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeType {
    Path { segments: Vec<SafePathSegment> },
    Reference { mutability: bool, elem: Box<SafeType> },
    Tuple { elems: Vec<SafeType> },
    Slice { elem: Box<SafeType> },
    Array { elem: Box<SafeType>, len: String },
    Ptr { mutability: bool, elem: Box<SafeType> },
    Other, // For types we don't strictly support/need (mapped to MatchError)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafePathSegment {
    pub ident: String,
    pub args: Vec<SafeType>,
}

impl Mirror for syn::Type {
    type Image = SafeType;
    fn mirror(&self) -> Self::Image {
        match self {
            syn::Type::Path(tp) => SafeType::Path {
                segments: tp
                    .path
                    .segments
                    .iter()
                    .map(|s| {
                        let args = match &s.arguments {
                            syn::PathArguments::AngleBracketed(a) => a
                                .args
                                .iter()
                                .filter_map(|arg| {
                                    if let syn::GenericArgument::Type(t) = arg {
                                        Some(t.mirror())
                                    } else {
                                        None
                                    }
                                })
                                .collect(),
                            _ => vec![],
                        };
                        SafePathSegment { ident: s.ident.to_string(), args }
                    })
                    .collect(),
            },
            syn::Type::Reference(tr) => SafeType::Reference {
                mutability: tr.mutability.is_some(),
                elem: Box::new(tr.elem.mirror()),
            },
            syn::Type::Tuple(tt) => {
                SafeType::Tuple { elems: tt.elems.iter().map(|t| t.mirror()).collect() }
            }
            syn::Type::Slice(ts) => SafeType::Slice { elem: Box::new(ts.elem.mirror()) },
            syn::Type::Array(ta) => SafeType::Array {
                elem: Box::new(ta.elem.mirror()),
                len: ta.len.to_token_stream().to_string(), // len is String
            },
            syn::Type::Ptr(tp) => SafeType::Ptr {
                mutability: tp.mutability.is_some(),
                elem: Box::new(tp.elem.mirror()),
            },
            _ => SafeType::Other,
        }
    }
}

// --- Functions ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeSignature {
    pub ident: String,
    pub inputs: Vec<SafeFnArg>,
    pub output: SafeReturnType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeFnArg {
    Typed { name: String, ty: SafeType },
    Receiver { mutability: bool, reference: bool },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeReturnType {
    Default,
    Type(SafeType),
}

impl Mirror for syn::Signature {
    type Image = SafeSignature;
    fn mirror(&self) -> Self::Image {
        SafeSignature {
            ident: self.ident.to_string(),
            inputs: self
                .inputs
                .iter()
                .map(|arg| match arg {
                    syn::FnArg::Receiver(r) => SafeFnArg::Receiver {
                        mutability: r.mutability.is_some(),
                        reference: r.reference.is_some(),
                    },
                    syn::FnArg::Typed(t) => {
                        let name = if let syn::Pat::Ident(i) = &*t.pat {
                            i.ident.to_string()
                        } else {
                            "_".to_string() // Wildcards or complex patterns
                        };
                        SafeFnArg::Typed { name, ty: t.ty.mirror() }
                    }
                })
                .collect(),
            output: match &self.output {
                syn::ReturnType::Default => SafeReturnType::Default,
                syn::ReturnType::Type(_, t) => SafeReturnType::Type(t.mirror()),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeItemFn {
    pub sig: SafeSignature,
}
impl Mirror for syn::ItemFn {
    type Image = SafeItemFn;
    fn mirror(&self) -> Self::Image {
        SafeItemFn { sig: self.sig.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeImplItemFn {
    pub sig: SafeSignature,
}
impl Mirror for syn::ImplItemFn {
    type Image = SafeImplItemFn;
    fn mirror(&self) -> Self::Image {
        SafeImplItemFn { sig: self.sig.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeTraitItemFn {
    pub sig: SafeSignature,
}
impl Mirror for syn::TraitItemFn {
    type Image = SafeTraitItemFn;
    fn mirror(&self) -> Self::Image {
        SafeTraitItemFn { sig: self.sig.mirror() }
    }
}

// --- Generics (Structs/Enums/Traits) ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeGenerics {
    pub params: Vec<SafeGenericParam>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeGenericParam {
    Type(String),
    Const(String),
    Lifetime,
}

impl Mirror for syn::Generics {
    type Image = SafeGenerics;
    fn mirror(&self) -> Self::Image {
        SafeGenerics {
            params: self
                .params
                .iter()
                .map(|p| match p {
                    syn::GenericParam::Type(t) => SafeGenericParam::Type(t.ident.to_string()),
                    syn::GenericParam::Const(c) => SafeGenericParam::Const(c.ident.to_string()),
                    syn::GenericParam::Lifetime(_) => SafeGenericParam::Lifetime,
                })
                .collect(),
        }
    }
}

// --- Items (Struct/Enum/Trait/Impl) ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeItemStruct {
    pub ident: String,
    pub generics: SafeGenerics,
}
impl Mirror for syn::ItemStruct {
    type Image = SafeItemStruct;
    fn mirror(&self) -> Self::Image {
        SafeItemStruct { ident: self.ident.to_string(), generics: self.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeItemEnum {
    pub ident: String,
    pub generics: SafeGenerics,
}
impl Mirror for syn::ItemEnum {
    type Image = SafeItemEnum;
    fn mirror(&self) -> Self::Image {
        SafeItemEnum { ident: self.ident.to_string(), generics: self.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeItemUnion {
    pub ident: String,
    pub generics: SafeGenerics,
}
impl Mirror for syn::ItemUnion {
    type Image = SafeItemUnion;
    fn mirror(&self) -> Self::Image {
        SafeItemUnion { ident: self.ident.to_string(), generics: self.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeItemTrait {
    pub ident: String,
    pub generics: SafeGenerics,
}
impl Mirror for syn::ItemTrait {
    type Image = SafeItemTrait;
    fn mirror(&self) -> Self::Image {
        SafeItemTrait { ident: self.ident.to_string(), generics: self.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeItemImpl; // Empty for now, we don't generate logic for Impl header yet
impl Mirror for syn::ItemImpl {
    type Image = SafeItemImpl;
    fn mirror(&self) -> Self::Image {
        SafeItemImpl
    }
}
