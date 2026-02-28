// Parsing logic for extracting Hermes annotations from Rust source code.
//
// This module provides the core infrastructure for traversing Rust source files,
// identifying items annotated with `/// ````hermes` blocks, and extracting them
// for verification.

pub mod attr;
pub mod hkd;

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use log::{debug, trace};
use miette::{NamedSource, SourceSpan};
use syn::{
    spanned::Spanned, visit::Visit, Attribute, Error, Expr, ImplItemFn, ItemEnum, ItemFn, ItemImpl,
    ItemMod, ItemStruct, ItemTrait, ItemUnion, Lit, Meta, TraitItemFn,
};

use self::{
    attr::{FunctionHermesBlock, ImplHermesBlock, TraitHermesBlock, TypeHermesBlock},
    hkd::{AstNode, LiftToSafe, Local, Safe, ThreadSafety},
};
use crate::errors::HermesError;

#[derive(Clone, Debug)]
pub enum FunctionItem<M: ThreadSafety = Local> {
    Free(AstNode<ItemFn, M>),
    Impl(AstNode<ImplItemFn, M>, Option<String>),
    Trait(AstNode<TraitItemFn, M>),
}

impl FunctionItem<Local> {
    pub fn name(&self) -> String {
        match self {
            Self::Free(x) => x.inner.sig.ident.to_string(),
            Self::Impl(x, _) => x.inner.sig.ident.to_string(),
            Self::Trait(x) => x.inner.sig.ident.to_string(),
        }
    }
}

impl FunctionItem<Safe> {
    pub fn name(&self) -> &str {
        match self {
            Self::Free(x) => &x.inner.sig.ident,
            Self::Impl(x, _) => &x.inner.sig.ident,
            Self::Trait(x) => &x.inner.sig.ident,
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionItem<M> {
    type Target = FunctionItem<Safe>;

    fn lift(self) -> Self::Target {
        match self {
            Self::Free(x) => FunctionItem::Free(x.lift()),
            Self::Impl(x, p) => FunctionItem::Impl(x.lift(), p),
            Self::Trait(x) => FunctionItem::Trait(x.lift()),
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
pub struct HermesDecorated<T, B> {
    pub item: T,
    pub hermes: B,
}

impl<T: LiftToSafe, B: LiftToSafe> LiftToSafe for HermesDecorated<T, B> {
    type Target = HermesDecorated<T::Target, B::Target>;

    fn lift(self) -> Self::Target {
        HermesDecorated { item: self.item.lift(), hermes: self.hermes.lift() }
    }
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum ParsedItem<M: ThreadSafety = Local> {
    Function(HermesDecorated<FunctionItem<M>, FunctionHermesBlock<M>>),
    Type(HermesDecorated<TypeItem<M>, TypeHermesBlock<M>>),
    Trait(HermesDecorated<AstNode<ItemTrait, M>, TraitHermesBlock<M>>),
    Impl(HermesDecorated<AstNode<ItemImpl, M>, ImplHermesBlock<M>>),
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
    F: FnMut(&str, Result<ParsedLeanItem, HermesError>),
{
    log::trace!("read_file_and_scan_compilation_unit({:?}, inside_block={})", path, inside_block);
    let source = fs::read_to_string(path)?;
    let mut unloaded_modules = Vec::new();
    scan_compilation_unit_internal(&source, Some(path.to_path_buf()), inside_block, f, |m| {
        unloaded_modules.push(m)
    });
    Ok((source, unloaded_modules))
}

fn scan_compilation_unit_internal<I, M>(
    source: &str,
    source_file: Option<PathBuf>,
    inside_block: bool,
    mut item_cb: I,
    mod_cb: M,
) where
    I: FnMut(&str, Result<ParsedLeanItem, HermesError>),
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
                Err(HermesError::Syn {
                    src: named_source.clone(),
                    span: span_to_miette(e.span()),
                    msg: e.to_string(),
                }),
            );
            return;
        }
    };

    trace!("Initializing HermesVisitor to traverse AST");
    let mut visitor = HermesVisitor {
        current_path: Vec::new(),
        current_impl_type: None,
        inside_block,
        item_cb,
        mod_cb,
        source_code: source.to_string(),
        named_source,
    };

    syn::visit::visit_file(&mut visitor, &file);
    trace!("Finished traversing AST");
}

struct HermesVisitor<I, M> {
    current_path: Vec<String>,
    current_impl_type: Option<String>,
    inside_block: bool,
    item_cb: I,
    mod_cb: M,
    source_code: String,
    named_source: NamedSource<String>,
}

impl<I, M> HermesVisitor<I, M>
where
    I: FnMut(&str, Result<ParsedLeanItem, HermesError>),
    M: FnMut(UnloadedModule),
{
    /// Processes an `item` (function, struct, etc.) that may have a Hermes
    /// annotation.
    ///
    /// This generic helper abstracts the common logic for:
    /// 1. Extracting the Hermes block from the item's attributes using `parse`.
    /// 2. Validating that the item is not inside a block (where verification is
    ///    unsupported).
    /// 3. Wrapping the item and its Hermes block into a `ParsedItem` using
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
            // This item doesn't have a Hermes annotation; skip it.
            Ok(None) => return,
            Ok(Some(_block)) if self.inside_block => Err(HermesError::NestedItem {
                src: self.named_source.clone(),
                span: span_to_miette(item.span()),
                msg: "Hermes cannot verify items defined inside function bodies or other blocks. \
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
                Err(HermesError::DocBlock {
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

impl<'ast, I, M> Visit<'ast> for HermesVisitor<I, M>
where
    I: FnMut(&str, Result<ParsedLeanItem, HermesError>),
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
                 Hermes does not currently evaluate conditional paths; \
                 Hermes annotations in this file may be ignored.",
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
        self.process_item(i, &i.attrs, FunctionHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Function(HermesDecorated {
                item: FunctionItem::Free(AstNode::new(item.clone())),
                hermes,
            })
        });
        syn::visit::visit_item_fn(self, i);
    }

    fn visit_item_struct(&mut self, i: &'ast ItemStruct) {
        trace!("Visiting Struct {}", i.ident);
        self.process_item(i, &i.attrs, TypeHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Type(HermesDecorated {
                item: TypeItem::Struct(AstNode::new(item.clone())),
                hermes,
            })
        });
        syn::visit::visit_item_struct(self, i);
    }

    fn visit_item_enum(&mut self, i: &'ast ItemEnum) {
        trace!("Visiting Enum {}", i.ident);
        self.process_item(i, &i.attrs, TypeHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Type(HermesDecorated {
                item: TypeItem::Enum(AstNode::new(item.clone())),
                hermes,
            })
        });
        syn::visit::visit_item_enum(self, i);
    }

    fn visit_item_union(&mut self, i: &'ast ItemUnion) {
        trace!("Visiting Union {}", i.ident);
        self.process_item(i, &i.attrs, TypeHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Type(HermesDecorated {
                item: TypeItem::Union(AstNode::new(item.clone())),
                hermes,
            })
        });
        syn::visit::visit_item_union(self, i);
    }

    fn visit_item_trait(&mut self, i: &'ast ItemTrait) {
        let name = i.ident.to_string();
        trace!("Visiting Trait {}", name);
        self.process_item(i, &i.attrs, TraitHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Trait(HermesDecorated { item: AstNode::new(item.clone()), hermes })
        });

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
        self.process_item(i, &i.attrs, ImplHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Impl(HermesDecorated { item: AstNode::new(item.clone()), hermes })
        });

        let mut impl_name = None;
        if let syn::Type::Path(type_path) = &*i.self_ty {
            if let Some(segment) = type_path.path.segments.last() {
                impl_name = Some(segment.ident.to_string());
            }
        }

        let old_impl_type = self.current_impl_type.take();
        self.current_impl_type = impl_name;

        syn::visit::visit_item_impl(self, i);

        self.current_impl_type = old_impl_type;
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        trace!("Visiting ImplItemFn {}", i.sig.ident);
        let current_impl_type = self.current_impl_type.clone();
        self.process_item(
            i,
            &i.attrs,
            FunctionHermesBlock::parse_from_attrs,
            move |item, hermes| {
                ParsedItem::Function(HermesDecorated {
                    item: FunctionItem::Impl(AstNode::new(item.clone()), current_impl_type.clone()),
                    hermes,
                })
            },
        );
        syn::visit::visit_impl_item_fn(self, i);
    }

    fn visit_trait_item_fn(&mut self, i: &'ast TraitItemFn) {
        trace!("Visiting TraitItemFn {}", i.sig.ident);
        self.process_item(i, &i.attrs, FunctionHermesBlock::parse_from_attrs, |item, hermes| {
            ParsedItem::Function(HermesDecorated {
                item: FunctionItem::Trait(AstNode::new(item.clone())),
                hermes,
            })
        });
        syn::visit::visit_trait_item_fn(self, i);
    }
}

/// Extracts the `...` from the first `#[path = "..."]` attribute found, if any.
fn extract_path_attr(attrs: &[Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        if attr.path().is_ident("path") {
            if let Meta::NameValue(nv) = &attr.meta {
                if let Expr::Lit(expr_lit) = &nv.value {
                    if let Lit::Str(lit_str) = &expr_lit.lit {
                        return Some(lit_str.value());
                    }
                }
            }
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
                if meta.path.is_ident("path") {
                    if let Ok(value) = meta.value() {
                        if let Ok(Lit::Str(lit_str)) = value.parse::<Lit>() {
                            found_path = Some(lit_str.value());
                        }
                    }
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

    fn parse_to_vec(code: &str) -> Vec<(String, Result<ParsedLeanItem, HermesError>)> {
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
        /// Returns the context of the Hermes block.
        fn hermes_context(&self) -> &[attr::SpannedLine] {
            match self {
                Self::Function(f) => &f.hermes.common.context,
                Self::Type(t) => &t.hermes.common.context,
                Self::Trait(t) => &t.hermes.common.context,
                Self::Impl(i) => &i.hermes.common.context,
            }
        }
    }

    #[test]
    fn test_parse_lean_block() {
        let code = r#"
            /// ```lean, hermes
            /// context
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        let (src, res) = items.into_iter().next().unwrap();
        let item = res.unwrap();
        assert_eq!(
            src,
            "/// ```lean, hermes
            /// context
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}"
        );
        assert!(matches!(item.item, ParsedItem::Function(_)));
        assert_eq!(
            item.item.hermes_context()[0].content.trim(),
            "theorem foo : True := by trivial"
        );
    }

    #[test]
    fn test_multiple_lean_blocks_error() {
        let code = r#"
            /// ```lean, hermes
            /// context
            /// a
            /// ```
            /// ```lean, hermes
            /// context
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
            /// ```lean, hermes
            /// context
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
                    /// ```lean, hermes
                    /// context
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
                /// ```lean, hermes
                /// context
                /// theorem foo : True := by trivial
                /// ```
                fn bar() {}
            }
        "#;
        let items = parse_to_vec(code);
        let (_, res) = items.into_iter().next().unwrap();
        // Since we are parsing a string, `inside_block` is false initially,
        // but `visit_item_mod` doesn't change `inside_block` for inline modules?
        // Wait, `visit_item_mod` calls `syn::visit::visit_item_mod`.
        // `syn` traverses the content.
        // `HermesVisitor::visit_item_mod`:
        // checks `node.content.is_none()` for unloaded modules.
        // calls `visit_item_mod`.
        //
        // NOTE: The `HermesVisitor` does NOT set `inside_block = true` when entering a module.
        // It sets `inside_block = true` when visiting a `Block` (function body).
        // Inline modules are not "blocks" in `syn` sense (they have braces but `ItemMod` structure handles it).
        // So this should SUCCEED unless I misunderstood `inside_block`.

        // Actually `test_visit_in_file` was failing with `unwrap` on `None` meaning it didn't find the block.
        // With `hermes` tag it should find it.
        let item = res.unwrap();
        assert!(matches!(item.item, ParsedItem::Function(_)));
    }

    #[test]
    fn test_span_multiple_modules_precision() {
        let code = r#"
            mod a {
                /// ```lean, hermes
                /// context
                /// theorem a : True := trivial
                /// ```
                fn foo() {}
            }
            mod b {
                /// ```lean, hermes
                /// context
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
        assert!(i1.item.hermes_context()[0].content.contains("theorem a"));
        assert!(i2.item.hermes_context()[0].content.contains("theorem b"));

        // Verify source snippets match the function definition + doc comment
        assert!(src1.contains("theorem a"));
        assert!(src1.contains("fn foo"));
        assert!(src2.contains("theorem b"));
        assert!(src2.contains("fn foo"));
    }

    #[test]
    fn test_multiple_parsing_failures_output() {
        let code1 = r#"
            /// ```lean, hermes
            /// context
            /// unclosed block 1
            fn bad_doc_1() {}

            /// ```lean, hermes
            /// context
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

        let expected = r#"hermes::doc_block

  × Documentation block error: Unclosed Hermes block in documentation.
   ╭─[src/foo.rs:2:13]
 1 │ 
 2 │             /// ```lean, hermes
   ·             ─────────┬─────────
   ·                      ╰── problematic block
 3 │             /// context
   ╰────

hermes::doc_block

  × Documentation block error: Unclosed Hermes block in documentation.
   ╭─[src/foo.rs:7:13]
 6 │ 
 7 │             /// ```lean, hermes
   ·             ─────────┬─────────
   ·                      ╰── problematic block
 8 │             /// context
   ╰────

hermes::syn_error

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
}
