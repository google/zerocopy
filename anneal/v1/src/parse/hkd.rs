use std::fmt::Debug;

use quote::ToTokens;

/// Generic support for bridging non-thread-safe AST nodes across threads.
///
/// Anneal concurrently parses many Rust files using `rayon` worker threads.
/// Because `syn` AST nodes are not guaranteed to be `Send + Sync` (and are
/// often heavy to clone), we cannot send the raw `syn` types back to
/// the main thread over a channel.
///
/// To solve this without sacrificing the convenience of standard `syn` types
/// during the initial parse, we use Generic Associated Types (GATs) to define
/// how primitives behave in two separate operating modes:
///
/// 1. `Local`: Holds raw `syn` AST nodes. This is fast and precise, but it is
///    not consistently `Send` safe. It is used exclusively on the worker
///    parsing threads.
/// 2. `Safe`: Holds specific, explicitly-owned `Send` representations (usually
///    `String`s or simplified structs like `SafeType` or `SafeSignature`).
///
/// This architecture allows us to parse deeply using `syn` on worker threads,
/// then immediately "lift" the extensive AST into a lightweight, thread-safe
/// representation before sending it back to the main orchestrating thread.
///
/// A trait defining how a non-thread-safe type transforms into a thread-safe
/// representation.
///
/// This is primarily implemented on `syn` types, enabling them to construct
/// their matching `Safe` equivalent (e.g., `syn::Type` -> `SafeType`).
pub trait Mirror {
    type Image: Debug + Clone + Send + 'static;
    fn mirror(&self) -> Self::Image;
}

/// A trait defining a "mode" for AST storage.
///
/// This allows generic structs (like `AstNode`) to transparently switch their
/// internal storage between non-thread-safe (`Local`) and thread-safe (`Safe`)
/// configurations without requiring duplicated structs.
pub trait ThreadSafety: 'static + Sized + Copy + Debug {
    /// How this mode handles underlying non-thread-safe AST node
    /// representation.
    type Node<T: Mirror + Clone + Debug>: Debug + Clone;

    /// A generic transform trait to move data from the current representation
    /// to the canonical "ThreadSafe" representation.
    ///
    /// If we are already Safe, this is identity.
    /// If we are Local, this erases the contents into `()`.
    fn lift_node<T: Mirror + Clone + Debug>(node: Self::Node<T>)
    -> <Safe as ThreadSafety>::Node<T>;
}

// --- Mode 1: Non-Thread-Safe (Fast, Local) ---

/// The local parsing mode.
///
/// In this mode, AST nodes are typically `syn` types directly. This is used
/// during the immediate parsing phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Local;

impl ThreadSafety for Local {
    // Retains full node payload natively
    type Node<T: Mirror + Clone + Debug> = T;

    fn lift_node<T: Mirror + Clone + Debug>(
        node: Self::Node<T>,
    ) -> <Safe as ThreadSafety>::Node<T> {
        node.mirror()
    }
}

// --- Mode 2: Thread-Safe (Send + Sync) ---

/// The thread-safe mode.
///
/// In this mode, AST nodes are strictly `Send + Sync` (often `String`s or
/// simplified structs). This is used when passing parsed items between threads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Safe;

impl ThreadSafety for Safe {
    // Erases nodes completely
    type Node<T: Mirror + Clone + Debug> = T::Image;

    fn lift_node<T: Mirror + Clone + Debug>(
        node: Self::Node<T>,
    ) -> <Safe as ThreadSafety>::Node<T> {
        // Already safe; just return ()
        node
    }
}

/// A trait defining how an `AstNode` (or similar structural container) carrying
/// local, unsafe data transforms into its thread-safe configuration.
///
/// Unlike `Mirror` (which acts on the underlying `syn` types directly), this
/// trait handles the conversion of the generic AST wrappers.
pub trait LiftToSafe {
    /// The thread-safe equivalent of Self.
    type Target: Send + Debug;

    /// Consumes the current version and produces the thread-safe version.
    fn lift(self) -> Self::Target;
}

/// A container for AST elements that adapts its internal storage based on the
/// generic mode parameter `M`.
///
/// When `M` is `Local`, `inner` holds the fast, native `syn` structural type.
/// When `M` is `Safe`, `inner` holds the mirrored, stringified, `Send`-safe
/// equivalent.
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
// We don't need the raw Span for generation, only for error reporting which
// happens earlier.
impl Mirror for proc_macro2::Span {
    type Image = miette::SourceSpan;
    fn mirror(&self) -> Self::Image {
        crate::parse::span_to_miette(*self)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeQSelf {
    pub ty: Box<SafeType>,
    pub position: usize,
}

impl Mirror for syn::QSelf {
    type Image = SafeQSelf;
    fn mirror(&self) -> Self::Image {
        SafeQSelf { ty: Box::new(self.ty.mirror()), position: self.position }
    }
}

// --- Types ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeType {
    Path {
        qself: Option<Box<SafeQSelf>>,
        segments: Vec<SafePathSegment>,
    },
    Reference {
        mutability: bool,
        elem: Box<SafeType>,
    },
    Tuple {
        elems: Vec<SafeType>,
    },
    Slice {
        elem: Box<SafeType>,
    },
    Array {
        elem: Box<SafeType>,
        len: String,
    },
    Ptr {
        mutability: bool,
        elem: Box<SafeType>,
    },
    /// The `!` type in Rust, which represents a value that can never be
    /// constructed.
    Never,
    /// A catch-all for types that are not explicitly supported or needed by
    /// the functional model. These are typically mapped to `MatchError` in Lean.
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeTypeParamBound {
    Trait {
        ty: SafeType,
        /// Represents whether the bound is relaxed with a question mark (e.g.,
        /// `?Sized`).
        is_maybe: bool,
    },
    Lifetime,
}

impl Mirror for syn::TypeParamBound {
    type Image = SafeTypeParamBound;
    fn mirror(&self) -> Self::Image {
        match self {
            syn::TypeParamBound::Trait(t) => SafeTypeParamBound::Trait {
                ty: syn::Type::Path(syn::TypePath { qself: None, path: t.path.clone() }).mirror(),
                is_maybe: matches!(t.modifier, syn::TraitBoundModifier::Maybe(_)),
            },
            syn::TypeParamBound::Lifetime(_) => SafeTypeParamBound::Lifetime,
            _ => SafeTypeParamBound::Lifetime, // Fallback
        }
    }
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
                qself: tp.qself.as_ref().map(|q| Box::new(q.mirror())),
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
            syn::Type::Never(_) => SafeType::Never,
            _ => SafeType::Other,
        }
    }
}

// --- Functions ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeSignature {
    pub ident: String,
    pub name_span: miette::SourceSpan,
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
            name_span: crate::parse::span_to_miette(self.ident.span()),
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
    pub generics: SafeGenerics,
}
impl Mirror for syn::ItemFn {
    type Image = SafeItemFn;
    fn mirror(&self) -> Self::Image {
        SafeItemFn { sig: self.sig.mirror(), generics: self.sig.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeImplItemFn {
    pub sig: SafeSignature,
    pub generics: SafeGenerics,
}
impl Mirror for syn::ImplItemFn {
    type Image = SafeImplItemFn;
    fn mirror(&self) -> Self::Image {
        SafeImplItemFn { sig: self.sig.mirror(), generics: self.sig.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeTraitItemFn {
    pub sig: SafeSignature,
    pub generics: SafeGenerics,
}
impl Mirror for syn::TraitItemFn {
    type Image = SafeTraitItemFn;
    fn mirror(&self) -> Self::Image {
        SafeTraitItemFn { sig: self.sig.mirror(), generics: self.sig.generics.mirror() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeForeignItemFn {
    pub sig: SafeSignature,
    pub generics: SafeGenerics,
}

impl Mirror for syn::ForeignItemFn {
    type Image = SafeForeignItemFn;
    fn mirror(&self) -> Self::Image {
        SafeForeignItemFn { sig: self.sig.mirror(), generics: self.sig.generics.mirror() }
    }
}

// --- Generics (Structs/Enums/Traits) ---
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafeGenerics {
    pub params: Vec<SafeGenericParam>,
    pub where_clause: Vec<SafeWherePredicate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeGenericParam {
    /// A type parameter (e.g., `T: Trait`).
    Type { name: String, bounds: Vec<SafeTypeParamBound> },
    /// A const parameter (e.g., `const N: usize`).
    ///
    /// We capture the type of the const parameter (`ty`) to ensure that
    /// the generated Lean code correctly types the corresponding
    /// constant in the functional model.
    Const { name: String, ty: SafeType },
    /// A lifetime parameter (e.g., `'a`).
    Lifetime,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeWherePredicate {
    Type { bounded_ty: SafeType, bounds: Vec<SafeTypeParamBound> },
    Lifetime,
}

impl Mirror for syn::WherePredicate {
    type Image = SafeWherePredicate;
    fn mirror(&self) -> Self::Image {
        match self {
            syn::WherePredicate::Type(t) => SafeWherePredicate::Type {
                bounded_ty: t.bounded_ty.mirror(),
                bounds: t.bounds.iter().map(|b| b.mirror()).collect(),
            },
            _ => SafeWherePredicate::Lifetime,
        }
    }
}

impl Mirror for syn::Generics {
    type Image = SafeGenerics;
    fn mirror(&self) -> Self::Image {
        SafeGenerics {
            params: self
                .params
                .iter()
                .map(|p| match p {
                    syn::GenericParam::Type(t) => SafeGenericParam::Type {
                        name: t.ident.to_string(),
                        bounds: t.bounds.iter().map(|b| b.mirror()).collect(),
                    },
                    syn::GenericParam::Const(c) => {
                        SafeGenericParam::Const { name: c.ident.to_string(), ty: c.ty.mirror() }
                    }
                    syn::GenericParam::Lifetime(_) => SafeGenericParam::Lifetime,
                })
                .collect(),
            where_clause: self
                .where_clause
                .as_ref()
                .map(|w| w.predicates.iter().map(|p| p.mirror()).collect())
                .unwrap_or_default(),
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

#[cfg(test)]
mod tests {
    use syn::parse_quote;

    use super::*;

    #[test]
    fn test_mirror_array_len() {
        let ty: syn::Type = parse_quote!([u8; 1 + 2]);
        let safe = ty.mirror();
        if let SafeType::Array { len, .. } = safe {
            assert_eq!(len, "1 + 2");
        } else {
            panic!("Expected Array, got {:?}", safe);
        }
    }

    #[test]
    fn test_mirror_qself() {
        let ty: syn::Type = parse_quote!(<T as Trait>::Assoc);
        let safe = ty.mirror();
        if let SafeType::Path { qself, .. } = safe {
            assert!(qself.is_some());
            let q = qself.unwrap();
            // Position logic: <A as B>::C
            // Path: B::C
            // Split: <A as B> :: C
            // position = length of B = 1.
            assert_eq!(q.position, 1);
        } else {
            panic!("Expected Path, got {:?}", safe);
        }
    }

    #[test]
    fn test_mirror_never() {
        let ty: syn::Type = parse_quote!(!);
        let safe = ty.mirror();
        assert_eq!(safe, SafeType::Never);
    }

    #[test]
    fn test_mirror_complex_never() {
        // Result<!, u32>
        let ty: syn::Type = parse_quote!(Result<!, u32>);
        let safe = ty.mirror();
        if let SafeType::Path { segments, .. } = safe {
            let res = segments.last().unwrap();
            assert_eq!(res.ident, "Result");
            assert_eq!(res.args[0], SafeType::Never);
        } else {
            panic!("Expected Path, got {:?}", safe);
        }

        // (u32, !)
        let ty: syn::Type = parse_quote!((u32, !));
        let safe = ty.mirror();
        if let SafeType::Tuple { elems } = safe {
            assert_eq!(elems[1], SafeType::Never);
        } else {
            panic!("Expected Tuple, got {:?}", safe);
        }
    }

    #[test]
    fn test_mirror_const_generics() {
        let generics: syn::Generics = parse_quote!(<const N: usize, const M: u32>);
        let safe = generics.mirror();

        let mk_path = |ident: &str| SafeType::Path {
            qself: None,
            segments: vec![SafePathSegment { ident: ident.to_string(), args: Vec::new() }],
        };

        match &safe.params[0] {
            SafeGenericParam::Const { name, ty } => {
                assert_eq!(name, "N");
                assert_eq!(*ty, mk_path("usize"));
            }
            _ => panic!("Expected Const, got {:?}", safe.params[0]),
        }
        match &safe.params[1] {
            SafeGenericParam::Const { name, ty } => {
                assert_eq!(name, "M");
                assert_eq!(*ty, mk_path("u32"));
            }
            _ => panic!("Expected Const, got {:?}", safe.params[1]),
        }
    }
}
