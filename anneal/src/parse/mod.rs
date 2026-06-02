// Parsing logic for extracting Anneal annotations from Rust source code.
//
// This module provides the core infrastructure for traversing Rust source
// files, identifying items annotated with `/// ````anneal` blocks, and
// extracting them for verification.

pub mod attr;
pub mod hkd;

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use log::{debug, trace};
use miette::{NamedSource, SourceSpan};
use syn::{
    Attribute, Error, Expr, ForeignItemFn, ImplItemFn, ItemEnum, ItemFn, ItemImpl, ItemMod,
    ItemStruct, ItemTrait, ItemUnion, Lit, Meta, TraitItemFn, spanned::Spanned, visit::Visit,
};

use self::{
    attr::{FunctionAnnealBlock, ImplAnnealBlock, TraitAnnealBlock, TypeAnnealBlock},
    hkd::{AstNode, LiftToSafe, Local, Safe, ThreadSafety},
};
use crate::errors::AnnealError;

#[derive(Clone, Debug)]
pub enum FunctionItem<M: ThreadSafety = Local> {
    /// A standard free-standing function.
    Free(AstNode<ItemFn, M>),
    /// A function defined within an `impl` block.
    Impl(
        AstNode<ImplItemFn, M>,
        /// The type that the `impl` block is for (the `Self` type).
        Option<AstNode<syn::Type, M>>,
        /// The generics of the `impl` block itself.
        Option<AstNode<syn::Generics, M>>,
    ),
    /// A function defined within a trait.
    Trait(AstNode<TraitItemFn, M>),
    /// A function defined within an `extern` block.
    Foreign(AstNode<ForeignItemFn, M>),
}

impl FunctionItem<Local> {
    /// Returns the name of the function.
    pub fn name(&self) -> String {
        match self {
            Self::Free(x) => x.inner.sig.ident.to_string(),
            Self::Impl(x, _, _) => x.inner.sig.ident.to_string(),
            Self::Trait(x) => x.inner.sig.ident.to_string(),
            Self::Foreign(x) => x.inner.sig.ident.to_string(),
        }
    }
}

impl FunctionItem<Safe> {
    pub fn name(&self) -> &str {
        match self {
            Self::Free(x) => &x.inner.sig.ident,
            Self::Impl(x, _, _) => &x.inner.sig.ident,
            Self::Trait(x) => &x.inner.sig.ident,
            Self::Foreign(x) => &x.inner.sig.ident,
        }
    }

    pub fn sig(&self) -> &crate::parse::hkd::SafeSignature {
        match self {
            Self::Free(x) => &x.inner.sig,
            Self::Impl(x, _, _) => &x.inner.sig,
            Self::Trait(x) => &x.inner.sig,
            Self::Foreign(x) => &x.inner.sig,
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionItem<M> {
    type Target = FunctionItem<Safe>;

    fn lift(self) -> Self::Target {
        match self {
            Self::Free(x) => FunctionItem::Free(x.lift()),
            Self::Impl(x, p, g) => {
                FunctionItem::Impl(x.lift(), p.map(|p| p.lift()), g.map(|g| g.lift()))
            }
            Self::Trait(x) => FunctionItem::Trait(x.lift()),
            Self::Foreign(x) => FunctionItem::Foreign(x.lift()),
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeItem<M: ThreadSafety = Local> {
    Struct(AstNode<ItemStruct, M>),
    Enum(AstNode<ItemEnum, M>),
    Union(AstNode<ItemUnion, M>),
}

impl TypeItem<Local> {
    pub fn name(&self) -> String {
        match self {
            Self::Struct(x) => x.inner.ident.to_string(),
            Self::Enum(x) => x.inner.ident.to_string(),
            Self::Union(x) => x.inner.ident.to_string(),
        }
    }
}

impl TypeItem<Safe> {
    pub fn name(&self) -> &str {
        match self {
            Self::Struct(x) => &x.inner.ident,
            Self::Enum(x) => &x.inner.ident,
            Self::Union(x) => &x.inner.ident,
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TypeItem<M> {
    type Target = TypeItem<Safe>;

    fn lift(self) -> Self::Target {
        match self {
            Self::Struct(x) => TypeItem::Struct(x.lift()),
            Self::Enum(x) => TypeItem::Enum(x.lift()),
            Self::Union(x) => TypeItem::Union(x.lift()),
        }
    }
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct AnnealDecorated<T, B> {
    pub item: T,
    pub anneal: B,
}

impl<T: LiftToSafe, B: LiftToSafe> LiftToSafe for AnnealDecorated<T, B> {
    type Target = AnnealDecorated<T::Target, B::Target>;

    fn lift(self) -> Self::Target {
        AnnealDecorated { item: self.item.lift(), anneal: self.anneal.lift() }
    }
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum ParsedItem<M: ThreadSafety = Local> {
    Function(AnnealDecorated<FunctionItem<M>, FunctionAnnealBlock<M>>),
    Type(AnnealDecorated<TypeItem<M>, TypeAnnealBlock<M>>),
    Trait(AnnealDecorated<AstNode<ItemTrait, M>, TraitAnnealBlock<M>>),
    Impl(AnnealDecorated<AstNode<ItemImpl, M>, ImplAnnealBlock<M>>),
}

impl ParsedItem<Local> {
    pub fn name(&self) -> Option<String> {
        match self {
            Self::Function(x) => Some(x.item.name()),
            Self::Type(x) => Some(x.item.name()),
            Self::Trait(x) => Some(x.item.inner.ident.to_string()),
            Self::Impl(_) => None,
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for ParsedItem<M> {
    type Target = ParsedItem<Safe>;

    fn lift(self) -> Self::Target {
        match self {
            Self::Function(x) => ParsedItem::Function(x.lift()),
            Self::Type(x) => ParsedItem::Type(x.lift()),
            Self::Trait(x) => ParsedItem::Trait(x.lift()),
            Self::Impl(x) => ParsedItem::Impl(x.lift()),
        }
    }
}

/// A complete parsed item including its module path and source file.
///
/// This struct pairs the parsed item (e.g., function, struct) with context
/// about where it was found, including the logical module path (e.g., `["foo",
/// "bar"]` for `mod foo { mod bar { ... } }`) and the physical source file
/// path.
#[derive(Debug)]
pub struct ParsedLeanItem<M: ThreadSafety = Local> {
    pub item: ParsedItem<M>,
    /// The module path to the module containing this item, relative to the
    /// outermost module at `source_file`, which may not be the crate root.
    pub module_path: Vec<String>,
    /// The absolute path to the source file containing this item.
    pub source_file: PathBuf,
}

impl<M: ThreadSafety> LiftToSafe for ParsedLeanItem<M> {
    type Target = ParsedLeanItem<Safe>;

    fn lift(self) -> Self::Target {
        ParsedLeanItem {
            item: self.item.lift(),
            module_path: self.module_path,
            source_file: self.source_file,
        }
    }
}

/// Represents a `mod foo;` declaration found in the source.
///
/// This is used by the scanner to discover additional files that need to be
/// processed.
#[derive(Debug, Clone)]
pub struct UnloadedModule {
    pub name: String,
    /// The value of `#[path = "..."]` if present.
    pub path_attr: Option<String>,
    /// True if this module was declared inside a block (e.g., a function body).
    pub inside_block: bool,
}

/// Parses the given Rust source file and invokes the callback `f` for each item
/// annotated with a `/// ```lean` block.
///
/// While parsing, collects every `mod foo;` declaration and returns them all.
///
/// If parsing fails, or if any item has multiple Lean blocks, the callback is
/// invoked with an `Err`.
///
/// Parsing errors and generated items will be associated with this file path.
///
/// Set `inside_block = true` if this file was discovered via a `mod foo;` item
/// inside of a block.
pub fn read_file_and_scan_compilation_unit<F>(
    path: &Path,
    inside_block: bool,
    f: F,
) -> Result<(String, Vec<UnloadedModule>), io::Error>
where
    F: FnMut(&str, Result<ParsedLeanItem, AnnealError>),
{
    log::trace!("read_file_and_scan_compilation_unit({:?}, inside_block={})", path, inside_block);
    let source = fs::read_to_string(path)?;
    let mut unloaded_modules = Vec::new();
    scan_compilation_unit_internal(&source, Some(path.to_path_buf()), inside_block, f, |m| {
        unloaded_modules.push(m)
    });
    Ok((source, unloaded_modules))
}

pub(crate) fn scan_compilation_unit_internal<I, M>(
    source: &str,
    source_file: Option<PathBuf>,
    inside_block: bool,
    mut item_cb: I,
    mod_cb: M,
) where
    I: FnMut(&str, Result<ParsedLeanItem, AnnealError>),
    M: FnMut(UnloadedModule),
{
    trace!("Parsing source code into syn::File");
    let file_name = source_file
        .as_ref()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|| "<input>".to_string());
    let named_source = miette::NamedSource::new(file_name, source.to_string());
    let file = match syn::parse_file(source) {
        Ok(file) => {
            debug!("Successfully parsed source code into syn::File");
            file
        }
        Err(e) => {
            debug!("Failed to parse source code: {}", e);
            item_cb(
                source,
                Err(AnnealError::Syn {
                    src: named_source.clone(),
                    span: span_to_miette(e.span()),
                    msg: e.to_string(),
                }),
            );
            return;
        }
    };

    trace!("Initializing AnnealVisitor to traverse AST");
    let mut visitor = AnnealVisitor {
        current_path: Vec::new(),
        current_impl_type: None,
        current_impl_generics: None,
        inside_block,
        item_cb,
        mod_cb,
        source_code: source.to_string(),
        named_source,
    };

    syn::visit::visit_file(&mut visitor, &file);
    trace!("Finished traversing AST");
}

struct AnnealVisitor<I, M> {
    current_path: Vec<String>,
    /// The parsed type of the current `impl` block being visited, if any.
    ///
    /// This is maintained in the visitor state to be passed down into the
    /// parsed representation of the methods (`FunctionItem::Impl`). This allows
    /// the code generator to explicitly resolve receiver bounds using the
    /// concrete structure type rather than a generic `Self` alias, which is
    /// necessary because Lean scope resolution for Aeneas-generated theorems
    /// requires exact target types.
    current_impl_type: Option<AstNode<syn::Type, Local>>,
    /// The generics of the current `impl` block being visited, if any.
    current_impl_generics: Option<AstNode<syn::Generics, Local>>,
    inside_block: bool,
    item_cb: I,
    mod_cb: M,
    source_code: String,
    named_source: NamedSource<String>,
}

impl<I, M> AnnealVisitor<I, M>
where
    I: FnMut(&str, Result<ParsedLeanItem, AnnealError>),
    M: FnMut(UnloadedModule),
{
    /// Processes an `item` (function, struct, etc.) that may have a Anneal
    /// annotation.
    ///
    /// This generic helper abstracts the common logic for:
    /// 1. Extracting the Anneal block from the item's attributes using `parse`.
    /// 2. Validating that the item is not inside a block (where verification is
    ///    unsupported).
    /// 3. Wrapping the item and its Anneal block into a `ParsedItem` using
    ///    `wrap`.
    /// 4. Invoking the `item_cb` with the result.
    fn process_item<
        T: Spanned,
        B,
        P: FnOnce(&[Attribute], &str) -> Result<Option<B>, Error>,
        W: FnOnce(&T, B) -> ParsedItem,
    >(
        &mut self,
        item: &T,
        attrs: &[Attribute],
        parse: P,
        wrap: W,
    ) {
        let block_res = parse(attrs, &self.source_code);
        let item_res = match block_res {
            // This item doesn't have a Anneal annotation; skip it.
            Ok(None) => return,
            Ok(Some(_block)) if self.inside_block => Err(AnnealError::NestedItem {
                src: self.named_source.clone(),
                span: span_to_miette(item.span()),
                msg: "Anneal cannot verify items defined inside function bodies or other blocks. \
                      Move this item to the module level if you wish to verify it."
                    .to_string(),
            }),
            Ok(Some(block)) => {
                let parsed_item = wrap(item, block);
                Ok(ParsedLeanItem {
                    item: parsed_item,
                    module_path: self.current_path.clone(),
                    source_file: PathBuf::from(self.named_source.name()),
                })
            }
            Err(e) => {
                log::trace!("Error extracting ```lean block: {}", e);
                Err(AnnealError::DocBlock {
                    src: self.named_source.clone(),
                    span: span_to_miette(e.span()),
                    msg: e.to_string(),
                })
            }
        };

        let source = &self.source_code.as_str()[item.span().byte_range()];
        (self.item_cb)(source, item_res);
    }
}

impl<'ast, I, M> Visit<'ast> for AnnealVisitor<I, M>
where
    I: FnMut(&str, Result<ParsedLeanItem, AnnealError>),
    M: FnMut(UnloadedModule),
{
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        let mod_name = node.ident.to_string();

        // Unloaded module (i.e., `mod foo;`).
        if node.content.is_none() {
            (self.mod_cb)(UnloadedModule {
                name: mod_name.clone(),
                path_attr: extract_path_attr(&node.attrs),
                inside_block: self.inside_block,
            });
        }

        if let Some(path_attr) = extract_cfg_attr_path(&node.attrs) {
            log::warn!(
                "Module '{}' uses a #[cfg_attr(..., path = \"{}\")] directive. \
                 Anneal does not currently evaluate conditional paths; \
                 Anneal annotations in this file may be ignored.",
                mod_name,
                path_attr
            );
        }

        trace!("Entering module: {}", mod_name);
        self.current_path.push(mod_name);
        syn::visit::visit_item_mod(self, node);
        let popped = self.current_path.pop();
        trace!("Exiting module: {}", popped.unwrap_or_default());
    }

    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        trace!("Visiting Fn {}", i.sig.ident);
        self.process_item(
            i,
            &i.attrs,
            |attrs, source| {
                FunctionAnnealBlock::parse_from_attrs(attrs, i.sig.unsafety.is_some(), source)
            },
            |item, anneal| {
                ParsedItem::Function(AnnealDecorated {
                    item: FunctionItem::Free(AstNode::new(item.clone())),
                    anneal,
                })
            },
        );
        syn::visit::visit_item_fn(self, i);
    }

    fn visit_item_struct(&mut self, i: &'ast ItemStruct) {
        trace!("Visiting Struct {}", i.ident);
        self.process_item(i, &i.attrs, TypeAnnealBlock::parse_from_attrs, |item, anneal| {
            ParsedItem::Type(AnnealDecorated {
                item: TypeItem::Struct(AstNode::new(item.clone())),
                anneal,
            })
        });
        syn::visit::visit_item_struct(self, i);
    }

    fn visit_item_enum(&mut self, i: &'ast ItemEnum) {
        trace!("Visiting Enum {}", i.ident);
        self.process_item(i, &i.attrs, TypeAnnealBlock::parse_from_attrs, |item, anneal| {
            ParsedItem::Type(AnnealDecorated {
                item: TypeItem::Enum(AstNode::new(item.clone())),
                anneal,
            })
        });
        syn::visit::visit_item_enum(self, i);
    }

    fn visit_item_union(&mut self, i: &'ast ItemUnion) {
        trace!("Visiting Union {}", i.ident);
        self.process_item(i, &i.attrs, TypeAnnealBlock::parse_from_attrs, |item, anneal| {
            ParsedItem::Type(AnnealDecorated {
                item: TypeItem::Union(AstNode::new(item.clone())),
                anneal,
            })
        });
        syn::visit::visit_item_union(self, i);
    }

    fn visit_item_trait(&mut self, i: &'ast ItemTrait) {
        let name = i.ident.to_string();
        trace!("Visiting Trait {}", name);
        self.process_item(
            i,
            &i.attrs,
            |attrs, source| TraitAnnealBlock::parse_from_attrs(attrs, i.unsafety.is_some(), source),
            |item, anneal| {
                ParsedItem::Trait(AnnealDecorated { item: AstNode::new(item.clone()), anneal })
            },
        );

        self.current_path.push(name);
        syn::visit::visit_item_trait(self, i);
        self.current_path.pop();
    }

    fn visit_block(&mut self, node: &'ast syn::Block) {
        let old_inside = self.inside_block;
        self.inside_block = true;
        syn::visit::visit_block(self, node);
        self.inside_block = old_inside;
    }

    fn visit_item_impl(&mut self, i: &'ast ItemImpl) {
        trace!("Visiting Impl");
        self.process_item(i, &i.attrs, ImplAnnealBlock::parse_from_attrs, |item, anneal| {
            ParsedItem::Impl(AnnealDecorated { item: AstNode::new(item.clone()), anneal })
        });

        let mut impl_ty_node = None;
        if let syn::Type::Path(_) = &*i.self_ty {
            impl_ty_node = Some(AstNode::new(*i.self_ty.clone()));
        }

        let old_impl_type = self.current_impl_type.take();
        let old_impl_generics = self.current_impl_generics.take();
        self.current_impl_type = impl_ty_node;
        self.current_impl_generics = Some(AstNode::new(i.generics.clone()));

        syn::visit::visit_item_impl(self, i);

        self.current_impl_type = old_impl_type;
        self.current_impl_generics = old_impl_generics;
    }

    /// Visits a foreign function (one defined in an `extern` block).
    ///
    /// This allows Anneal to extract specifications for functions written
    /// in other languages (or other Rust crates) that are declared in
    /// the current crate.
    fn visit_foreign_item_fn(&mut self, i: &'ast ForeignItemFn) {
        trace!("Visiting Foreign Fn {}", i.sig.ident);
        self.process_item(
            i,
            &i.attrs,
            |attrs, source| {
                FunctionAnnealBlock::parse_from_attrs(attrs, i.sig.unsafety.is_some(), source)
            },
            |item, anneal| {
                ParsedItem::Function(AnnealDecorated {
                    item: FunctionItem::Foreign(AstNode::new(item.clone())),
                    anneal,
                })
            },
        );
        syn::visit::visit_foreign_item_fn(self, i);
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        trace!("Visiting ImplItemFn {}", i.sig.ident);
        let current_impl_type = self.current_impl_type.clone();
        let current_impl_generics = self.current_impl_generics.clone();
        self.process_item(
            i,
            &i.attrs,
            |attrs, source| {
                FunctionAnnealBlock::parse_from_attrs(attrs, i.sig.unsafety.is_some(), source)
            },
            move |item, anneal| {
                ParsedItem::Function(AnnealDecorated {
                    item: FunctionItem::Impl(
                        AstNode::new(item.clone()),
                        current_impl_type.clone(),
                        current_impl_generics.clone(),
                    ),
                    anneal,
                })
            },
        );
        syn::visit::visit_impl_item_fn(self, i);
    }

    fn visit_trait_item_fn(&mut self, i: &'ast TraitItemFn) {
        trace!("Visiting TraitItemFn {}", i.sig.ident);
        self.process_item(
            i,
            &i.attrs,
            |attrs, source| {
                FunctionAnnealBlock::parse_from_attrs(attrs, i.sig.unsafety.is_some(), source)
            },
            |item, anneal| {
                ParsedItem::Function(AnnealDecorated {
                    item: FunctionItem::Trait(AstNode::new(item.clone())),
                    anneal,
                })
            },
        );
        syn::visit::visit_trait_item_fn(self, i);
    }
}

/// Extracts the `...` from the first `#[path = "..."]` attribute found, if any.
fn extract_path_attr(attrs: &[Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        if attr.path().is_ident("path")
            && let Meta::NameValue(nv) = &attr.meta
            && let Expr::Lit(expr_lit) = &nv.value
            && let Lit::Str(lit_str) = &expr_lit.lit
        {
            return Some(lit_str.value());
        }
        None
    })
}

/// Extracts the `...` from `#[cfg_attr(..., path = "...")]` if present.
fn extract_cfg_attr_path(attrs: &[Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        if attr.path().is_ident("cfg_attr") {
            let mut found_path = None;
            // The syntax is `#[cfg_attr(condition, attr1, attr2, ...)]`; we
            // parse the nested meta items.
            let _ = attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("path")
                    && let Ok(value) = meta.value()
                    && let Ok(Lit::Str(lit_str)) = value.parse::<Lit>()
                {
                    found_path = Some(lit_str.value());
                }
                Ok(())
            });
            found_path
        } else {
            None
        }
    })
}

pub(crate) fn span_to_miette(span: proc_macro2::Span) -> SourceSpan {
    let range = span.byte_range();
    SourceSpan::new(range.start.into(), range.end - range.start)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_to_vec(code: &str) -> Vec<(String, Result<ParsedLeanItem, AnnealError>)> {
        let mut items = Vec::new();
        scan_compilation_unit_internal(
            code,
            None,
            false,
            |src, res| items.push((src.to_string(), res)),
            |_| {},
        );
        items
    }

    impl ParsedItem {
        /// Returns the context of the Anneal block.
        fn anneal_context(&self) -> &[attr::SpannedLine] {
            match self {
                Self::Function(f) => &f.anneal.content,
                Self::Type(t) => &t.anneal.content,
                Self::Trait(t) => &t.anneal.content,
                Self::Impl(i) => &i.anneal.content,
            }
        }
    }

    #[test]
    fn test_parse_lean_block() {
        let code = r#"
            /// ```lean, anneal
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        let (src, res) = items.into_iter().next().unwrap();
        let item = res.unwrap();
        assert_eq!(
            src,
            "/// ```lean, anneal
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}"
        );
        assert!(matches!(item.item, ParsedItem::Function(_)));
        assert_eq!(
            item.item.anneal_context()[0].content.trim(),
            "theorem foo : True := by trivial"
        );
    }

    #[test]
    fn test_multiple_lean_blocks_error() {
        let code = r#"
            /// ```lean, anneal
            /// context:
            /// a
            /// ```
            /// ```lean, anneal
            /// context:
            /// b
            /// ```
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        for (_, res) in items {
            assert!(res.is_err());
        }
    }

    #[test]
    fn test_unclosed_lean_block() {
        let code = r#"
            /// ```lean, anneal
            /// context:
            /// theorem foo : True := by trivial
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        let (_, res) = items.into_iter().next().unwrap();
        assert!(res.is_err());
    }

    #[test]
    fn test_module_paths() {
        let code = r#"
            mod foo {
                mod bar {
                    /// ```lean, anneal
                    /// context:
                    /// ```
                    fn baz() {}
                }
            }
        "#;
        let items = parse_to_vec(code);
        let (_, res) = items.into_iter().next().unwrap();
        let item = res.unwrap();
        assert_eq!(item.module_path, vec!["foo", "bar"]);
    }

    #[test]
    fn test_visit_in_file() {
        let code = r#"
            mod foo {
                /// ```lean, anneal
                /// context:
                /// theorem foo : True := by trivial
                /// ```
                fn bar() {}
            }
        "#;
        let items = parse_to_vec(code);
        let (_, res) = items.into_iter().next().unwrap();
        // Since we are parsing a string, `inside_block` is false initially.
        // `visit_item_mod` does not change `inside_block` for inline modules.
        // `AnnealVisitor` only sets `inside_block = true` when visiting a
        // `Block` (function body). Inline modules are not "blocks" in the `syn`
        // sense (they have braces, but the `ItemMod` structure handles them).
        // Thus, this should succeed.

        // The `anneal` tag ensures the block is correctly identified and
        // processed.
        let item = res.unwrap();
        assert!(matches!(item.item, ParsedItem::Function(_)));
    }

    #[test]
    fn test_span_multiple_modules_precision() {
        let code = r#"
            mod a {
                /// ```lean, anneal
                /// theorem a : True := trivial
                /// ```
                fn foo() {}
            }
            mod b {
                /// ```lean, anneal
                /// theorem b : False := sorry
                /// ```
                fn foo() {}
            }
        "#;
        let items = parse_to_vec(code);
        assert_eq!(items.len(), 2);

        let (src1, item1) = &items[0];
        let (src2, item2) = &items[1];

        let i1 = item1.as_ref().unwrap();
        let i2 = item2.as_ref().unwrap();

        // Verify we got the right blocks for the right items
        assert!(i1.item.anneal_context()[0].content.contains("theorem a"));
        assert!(i2.item.anneal_context()[0].content.contains("theorem b"));

        // Verify source snippets match the function definition + doc comment
        assert!(src1.contains("theorem a"));
        assert!(src1.contains("fn foo"));
        assert!(src2.contains("theorem b"));
        assert!(src2.contains("fn foo"));
    }

    #[test]
    fn test_multiple_parsing_failures_output() {
        let code1 = r#"
            /// ```lean, anneal
            /// context:
            /// unclosed block 1
            fn bad_doc_1() {}

            /// ```lean, anneal
            /// context:
            /// unclosed block 2
            fn bad_doc_2() {}
        "#;

        let code2 = r#"
            fn bad_syntax_1() {
                let x = 
            }

            fn bad_syntax_2() {
                let y = 
            }
        "#;

        let path = std::path::Path::new("src/foo.rs");
        let mut items = Vec::new();

        scan_compilation_unit_internal(
            code1,
            Some(path.to_path_buf()),
            false,
            |_src, res| items.push(res),
            |_| {},
        );
        scan_compilation_unit_internal(
            code2,
            Some(path.to_path_buf()),
            false,
            |_src, res| items.push(res),
            |_| {},
        );

        let mut report_string = String::new();
        for err in items.into_iter().filter_map(|r| r.err()) {
            let mut buf = String::new();
            miette::GraphicalReportHandler::new()
                .with_width(80)
                .with_links(false)
                .with_theme(miette::GraphicalTheme::unicode_nocolor())
                .render_report(&mut buf, &err)
                .unwrap();
            report_string.push_str(&buf);
            report_string.push('\n');
        }

        let expected = r#"anneal::doc_block

  × Documentation block error: Unclosed Anneal block in documentation.
   ╭─[src/foo.rs:2:13]
 1 │ 
 2 │             /// ```lean, anneal
   ·             ─────────┬─────────
   ·                      ╰── problematic block
 3 │             /// context:
   ╰────

anneal::doc_block

  × Documentation block error: Unclosed Anneal block in documentation.
   ╭─[src/foo.rs:7:13]
 6 │ 
 7 │             /// ```lean, anneal
   ·             ─────────┬─────────
   ·                      ╰── problematic block
 8 │             /// context:
   ╰────

anneal::syn_error

  × Syntax error in Rust source: unexpected end of input, expected an
  │ expression
   ╭─[src/foo.rs:4:13]
 3 │                 let x = 
 4 │             }
   ·             ┬
   ·             ╰── here
 5 │ 
   ╰────
"#;
        assert_eq!(report_string.trim(), expected.trim());
    }

    #[test]
    fn test_foreign_function_scanning() {
        let code = r#"
            extern "C" {
                /// ```lean, anneal
                /// theorem ext_foo_ok : True := trivial
                /// ```
                fn ext_foo();
            }
        "#;
        let items = parse_to_vec(code);
        assert_eq!(items.len(), 1);
        let (src, res) = items.into_iter().next().unwrap();
        let item = res.unwrap();
        assert!(src.contains("fn ext_foo"));
        assert!(matches!(
            item.item,
            ParsedItem::Function(AnnealDecorated { item: FunctionItem::Foreign(_), .. })
        ));
        assert!(item.item.anneal_context()[0].content.contains("ext_foo_ok"));
    }
}
