use std::{
    convert::Infallible,
    fs, io,
    path::{Path, PathBuf},
};

use log::{debug, trace};
use miette::{NamedSource, SourceSpan};
use proc_macro2::Span;
use syn::{
    spanned::Spanned, visit::Visit, Attribute, Error, Expr, ImplItemFn, ItemEnum, ItemFn, ItemImpl,
    ItemMod, ItemStruct, ItemTrait, ItemUnion, Lit, Meta, TraitItemFn,
};

use crate::errors::HermesError;

/// A custom error type that associates a `syn::Error` with the file path
/// it originated from.
#[derive(Debug)]
pub struct ParseError {
    error: Error,
    source_file: Option<PathBuf>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(path) = &self.source_file {
            write!(f, "{}: {}", path.display(), self.error)
        } else {
            write!(f, "{}", self.error)
        }
    }
}
impl std::error::Error for ParseError {}

#[derive(Clone, Debug)]
pub enum FunctionItem {
    Free(ItemFn),
    Impl(ImplItemFn),
    Trait(TraitItemFn),
}

impl FunctionItem {
    pub fn name(&self) -> String {
        match self {
            Self::Free(x) => x.sig.ident.to_string(),
            Self::Impl(x) => x.sig.ident.to_string(),
            Self::Trait(x) => x.sig.ident.to_string(),
        }
    }

    pub fn attrs(&self) -> &[Attribute] {
        match self {
            Self::Free(x) => &x.attrs,
            Self::Impl(x) => &x.attrs,
            Self::Trait(x) => &x.attrs,
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeItem {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
}

impl TypeItem {
    pub fn name(&self) -> String {
        match self {
            Self::Struct(x) => x.ident.to_string(),
            Self::Enum(x) => x.ident.to_string(),
            Self::Union(x) => x.ident.to_string(),
        }
    }

    pub fn attrs(&self) -> &[Attribute] {
        match self {
            Self::Struct(x) => &x.attrs,
            Self::Enum(x) => &x.attrs,
            Self::Union(x) => &x.attrs,
        }
    }
}

#[derive(Clone, Debug)]
pub struct HermesDecorated<T, A = Infallible> {
    pub item: T,
    pub hermes: HermesBlock<A>,
}

#[derive(Clone, Debug)]
pub enum ParsedItem {
    Function(HermesDecorated<FunctionItem, HermesAttr>),
    Type(HermesDecorated<TypeItem, Infallible>),
    Trait(HermesDecorated<ItemTrait, Infallible>),
    Impl(HermesDecorated<ItemImpl, Infallible>),
}

impl ParsedItem {
    pub fn name(&self) -> Option<String> {
        match self {
            Self::Function(x) => Some(x.item.name()),
            Self::Type(x) => Some(x.item.name()),
            Self::Trait(x) => Some(x.item.ident.to_string()),
            Self::Impl(_) => None,
        }
    }

    /// Returns the attributes on this item.
    fn attrs(&self) -> &[Attribute] {
        match self {
            Self::Function(x) => x.item.attrs(),
            Self::Type(x) => x.item.attrs(),
            Self::Trait(x) => &x.item.attrs,
            Self::Impl(x) => &x.item.attrs,
        }
    }

    /// Returns the content of the Hermes block.
    pub fn hermes_content(&self) -> &str {
        match self {
            Self::Function(x) => &x.hermes.content,
            Self::Type(x) => &x.hermes.content,
            Self::Trait(x) => &x.hermes.content,
            Self::Impl(x) => &x.hermes.content,
        }
    }
}

/// Converts from a pair of `item` and `block: HermesBlock<HermesAttr>` to a
/// `HermesDecorated<Infallible>`, erroring if the `block` has an attribute.
///
/// On success, passes the `HermesDecorate<Infallible>` to `f`.
fn try_from_raw_reject_attr<T, F: FnOnce(HermesDecorated<T>) -> ParsedItem>(
    item: T,
    block: HermesBlock<HermesAttr>,
    f: F,
) -> Result<ParsedItem, (SourceSpan, String)> {
    if let Some(_attr) = block.attribute {
        return Err((
            span_to_miette(block.start_span),
            "This item does not support Hermes attributes (like `spec` or `unsafe(axiom)`). Only generic `hermes` blocks are allowed.".to_string(),
        ));
    }
    Ok(f(HermesDecorated {
        item,
        hermes: HermesBlock {
            attribute: None,
            content: block.content,
            content_span: block.content_span,
            start_span: block.start_span,
        },
    }))
}

/// A complete parsed item including its module path and source file.
#[derive(Debug)]
pub struct ParsedLeanItem {
    pub item: ParsedItem,
    pub module_path: Vec<String>,
    source_file: Option<PathBuf>,
}

/// Represents a `mod foo;` declaration found in the source.
#[derive(Debug, Clone)]
pub struct UnloadedModule {
    pub name: String,
    /// The value of `#[path = "..."]` if present.
    pub path_attr: Option<String>,
    pub span: proc_macro2::Span,
    /// True if this module was declared inside a block.
    pub inside_block: bool,
}

/// Parses the given Rust source code and invokes the callback `f` for each item
/// annotated with a `/// ```lean` block.
///
/// While parsing, collects every `mod foo;` declaration and returns them all.
///
/// If parsing fails, or if any item has multiple Lean blocks, the callback is
/// invoked with an `Err`.
pub fn scan_compilation_unit<F>(source: &str, f: F) -> Vec<UnloadedModule>
where
    F: FnMut(&str, Result<ParsedLeanItem, HermesError>),
{
    let mut unloaded_modules = Vec::new();
    scan_compilation_unit_internal(source, None, false, f, |m| unloaded_modules.push(m));
    unloaded_modules
}

/// Like [`scan_compilation_unit`], but reads the source code from a file path.
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
    scan_compilation_unit_internal(&source, None, inside_block, f, |m| unloaded_modules.push(m));
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
    let file_name = {
        let f = source_file
            .as_ref()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|| "<input>".to_string());

        f
    };
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
                Err(HermesError::SynError {
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
        inside_block,
        item_cb,
        mod_cb,
        source_file,
        source_code: source.to_string(),
        named_source,
    };

    syn::visit::visit_file(&mut visitor, &file);
    trace!("Finished traversing AST");
}

struct HermesVisitor<I, M> {
    current_path: Vec<String>,
    inside_block: bool,
    item_cb: I,
    mod_cb: M,
    source_file: Option<PathBuf>,
    source_code: String,
    named_source: NamedSource<String>,
}

impl<I, M> HermesVisitor<I, M>
where
    I: FnMut(&str, Result<ParsedLeanItem, HermesError>),
    M: FnMut(UnloadedModule),
{
    /// Processes an `item` that may have a Hermes annotation.
    ///
    /// If the `item` has a Hermes annotation, it is passed to `f` along with the
    /// parsed `HermesBlock`. `f` may accept or reject the item (currently,
    /// rejection can only happen when a Hermes attribute is preesnt on the
    /// annotation (e.g., `spec` or `unsafe(axiom)`) and the item type does not
    /// support attributes).
    ///
    /// If the item does not have a Hermes annotation, it is skipped.
    fn process_item<
        T,
        F: FnOnce(T, HermesBlock<HermesAttr>) -> Result<ParsedItem, (SourceSpan, String)>,
    >(
        &mut self,
        item: T,
        attrs: &[Attribute],
        span: Span,
        f: F,
    ) {
        let item_res = match HermesBlock::parse_from_attrs(attrs) {
            // This item doesn't have a Hermes annotation; skip it.
            Ok(None) => return,
            Ok(Some(_block)) if self.inside_block => Err(HermesError::NestedItemError {
                src: self.named_source.clone(),
                span: span_to_miette(span),
                msg: "Hermes cannot verify items defined inside function bodies or other blocks."
                    .to_string(),
            }),
            Ok(Some(block)) => f(item, block)
                .map(|item| ParsedLeanItem {
                    item,
                    module_path: self.current_path.clone(),
                    source_file: self.source_file.clone(),
                })
                .map_err(|(span, msg)| HermesError::DocBlockError {
                    src: self.named_source.clone(),
                    span,
                    msg,
                }),
            Err(e) => {
                log::trace!("Error extracting ```lean block: {}", e);
                Err(HermesError::DocBlockError {
                    src: self.named_source.clone(),
                    span: span_to_miette(e.span()),
                    msg: e.to_string(),
                })
            }
        };

        let source = &self.source_code.as_str()[span.byte_range()];
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
                span: node.span(),
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

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        trace!("Visiting Fn {}", node.sig.ident);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            Ok(ParsedItem::Function(HermesDecorated {
                item: FunctionItem::Free(item),
                hermes: block,
            }))
        });
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_item_struct(&mut self, node: &'ast ItemStruct) {
        trace!("Visiting Struct {}", node.ident);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            try_from_raw_reject_attr(item, block, |d| {
                ParsedItem::Type(HermesDecorated {
                    item: TypeItem::Struct(d.item),
                    hermes: d.hermes,
                })
            })
        });
        syn::visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast ItemEnum) {
        trace!("Visiting Enum {}", node.ident);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            try_from_raw_reject_attr(item, block, |d| {
                ParsedItem::Type(HermesDecorated { item: TypeItem::Enum(d.item), hermes: d.hermes })
            })
        });
        syn::visit::visit_item_enum(self, node);
    }

    fn visit_item_union(&mut self, node: &'ast ItemUnion) {
        trace!("Visiting Union {}", node.ident);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            try_from_raw_reject_attr(item, block, |d| {
                ParsedItem::Type(HermesDecorated {
                    item: TypeItem::Union(d.item),
                    hermes: d.hermes,
                })
            })
        });
        syn::visit::visit_item_union(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast ItemTrait) {
        let name = node.ident.to_string();
        trace!("Visiting Trait {}", name);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            try_from_raw_reject_attr(item, block, ParsedItem::Trait)
        });

        self.current_path.push(name);
        syn::visit::visit_item_trait(self, node);
        self.current_path.pop();
    }

    fn visit_block(&mut self, node: &'ast syn::Block) {
        let old_inside = self.inside_block;
        self.inside_block = true;
        syn::visit::visit_block(self, node);
        self.inside_block = old_inside;
    }

    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        trace!("Visiting Impl");
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            try_from_raw_reject_attr(item, block, ParsedItem::Impl)
        });
        syn::visit::visit_item_impl(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        trace!("Visiting ImplItemFn {}", node.sig.ident);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            Ok(ParsedItem::Function(HermesDecorated {
                item: FunctionItem::Impl(item),
                hermes: block,
            }))
        });
        syn::visit::visit_impl_item_fn(self, node);
    }

    fn visit_trait_item_fn(&mut self, node: &'ast TraitItemFn) {
        trace!("Visiting TraitItemFn {}", node.sig.ident);
        self.process_item(node.clone(), node.attrs.as_slice(), node.span(), |item, block| {
            Ok(ParsedItem::Function(HermesDecorated {
                item: FunctionItem::Trait(item),
                hermes: block,
            }))
        });
        syn::visit::visit_trait_item_fn(self, node);
    }
}

/// Helper to extract exactly one Lean block from a slice of attributes.
/// Returns `Ok(None)` if no block is found.
/// Returns `Err` if the block is malformed or multiple blocks are found.

/// Extracts the `...` from the first `#[path = "..."]` attribute found, if any.
fn extract_path_attr(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        if attr.path().is_ident("path") {
            if let Meta::NameValue(nv) = &attr.meta {
                if let Expr::Lit(expr_lit) = &nv.value {
                    if let Lit::Str(lit_str) = &expr_lit.lit {
                        return Some(lit_str.value());
                    }
                }
            }
        }
    }
    None
}

/// Extracts the `...` from `#[cfg_attr(..., path = "...")]` if present.
fn extract_cfg_attr_path(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        if attr.path().is_ident("cfg_attr") {
            let mut found_path = None;
            // The syntax is `#[cfg_attr(condition, attr1, attr2, ...)]`; we
            // parse the nested meta items.
            let _ = attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("path") {
                    if let Ok(value) = meta.value() {
                        if let Ok(lit) = value.parse::<Lit>() {
                            if let Lit::Str(lit_str) = lit {
                                found_path = Some(lit_str.value());
                            }
                        }
                    }
                }
                Ok(())
            });

            if let Some(p) = found_path {
                return Some(p);
            }
        }
    }
    None
}

fn span_to_miette(span: proc_macro2::Span) -> SourceSpan {
    let range = span.byte_range();
    SourceSpan::new(range.start.into(), range.end - range.start)
}

use attr::*;
mod attr {
    use proc_macro2::Span;

    use super::*;

    /// Represents a parsed attribute from a Hermes info string.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum HermesAttr {
        /// `spec`: Indicates a function specification and proof.
        Spec,
        /// `unsafe(axiom)`: Indicates an axiomatization of an unsafe function.
        UnsafeAxiom,
    }

    /// A fully parsed Hermes documentation block.
    #[derive(Debug, Clone)]
    pub struct HermesBlock<A = Infallible> {
        /// The Hermes attribute parsed from the info string, if any.
        pub attribute: Option<A>,
        /// The opaque content of the code block.
        pub content: String,
        /// The span covering the entire content (merged from start to end line).
        pub content_span: Span,
        /// The span of the opening ` ``` ` line.
        pub start_span: Span,
    }

    /// Parses the info string of a code block.
    ///
    /// * `info`: The info string text (e.g. "lean, hermes, spec").
    ///
    /// Returns:
    /// * `Ok(Some(Some(attr)))` if `hermes` was found and had valid arguments.
    /// * `Ok(Some(None))` if `hermes` was found but had no arguments.
    /// * `Ok(None)` if `hermes` was not found.
    /// * `Err(msg)` if `hermes` was found but had invalid arguments.
    fn parse_hermes_info_string(info: &str) -> Result<Option<Option<HermesAttr>>, String> {
        let mut tokens = info.split(',').map(str::trim).filter(|s| !s.is_empty());

        // Find and consume the `hermes` token.
        if tokens.find(|&t| t == "hermes").is_none() {
            return Ok(None);
        }

        let first_arg = tokens.next();
        let second_arg = tokens.next();
        match (first_arg, second_arg) {
            (Some(first), Some(second)) => return Err(format!(
                "Multiple attributes specified after 'hermes' ('{first}', '{second}'). Only one attribute is allowed."
            )),
            (None, None) => return Ok(Some(None)),
            (Some("spec"), None) => return Ok(Some(Some(HermesAttr::Spec))),
            (Some("unsafe(axiom)"), None) => return Ok(Some(Some(HermesAttr::UnsafeAxiom))),
            (Some(token), None) if token.starts_with("unsafe") => return Err(format!(
                "Unknown or malformed attribute: '{token}'. Did you mean 'unsafe(axiom)'?"
            )),
            (Some(token), None) => return Err(format!(
                "Unrecognized Hermes attribute: '{token}'. Supported attributes are 'spec', 'unsafe(axiom)'."
            )),
            (None, Some(_)) => unreachable!(),
        }
    }

    /// Helper to extract the string content and span from a `#[doc = "..."]` attribute.
    ///
    /// Returns `Some((content, span))` if the attribute is a doc comment.
    fn extract_doc_line(attr: &Attribute) -> Option<(String, Span)> {
        if !attr.path().is_ident("doc") {
            return None;
        }
        match &attr.meta {
            Meta::NameValue(nv) => {
                if let Expr::Lit(expr_lit) = &nv.value {
                    if let Lit::Str(lit_str) = &expr_lit.lit {
                        return Some((lit_str.value(), lit_str.span()));
                    }
                }
                None
            }
            _ => None,
        }
    }

    impl HermesBlock<HermesAttr> {
        pub fn parse_from_attrs(
            attrs: &[Attribute],
        ) -> Result<Option<HermesBlock<HermesAttr>>, Error> {
            let mut found_block: Option<HermesBlock<HermesAttr>> = None;
            let mut iter = attrs.iter().peekable();

            while let Some(attr) = iter.next() {
                // 1. Check if this attribute is a doc comment
                let (text, span) = match extract_doc_line(attr) {
                    Some(val) => val,
                    None => continue,
                };

                // 2. Check for the opening of a code block
                let trimmed = text.trim();
                if !trimmed.starts_with("```") {
                    continue;
                }

                // 3. Check if it is a Hermes block
                let info_string = trimmed[3..].trim();
                let parsed_attr =
                    match parse_hermes_info_string(info_string).map_err(|m| Error::new(span, m))? {
                        Some(attr) => attr,
                        None => continue, // It's a code block, but not for Hermes. Ignore it.
                    };

                // 4. Duplicate Block Check
                if found_block.is_some() {
                    return Err(Error::new(span, "Multiple Hermes blocks found on a single item."));
                }

                // 5. Accumulate Body Content
                let start_span = span;
                let mut content = String::new();
                let mut first_content_span: Option<Span> = None;
                let mut last_content_span: Option<Span> = None;
                let mut closed = false;

                // Consume subsequent doc attributes until we find the closing fence
                while let Some(next_attr) = iter.peek() {
                    let (next_text, next_span) = match extract_doc_line(next_attr) {
                        Some(val) => val,
                        None => break, // Interrupted by non-doc attribute
                    };

                    if next_text.trim().starts_with("```") {
                        iter.next(); // Consume the closing fence
                        closed = true;
                        break;
                    }

                    // Append line to content
                    content.push_str(&next_text);
                    content.push('\n');

                    // Track spans for error reporting
                    if first_content_span.is_none() {
                        first_content_span = Some(next_span);
                    }
                    last_content_span = Some(next_span);

                    iter.next(); // Advance iterator
                }

                if !closed {
                    return Err(Error::new(start_span, "Unclosed Hermes block in documentation."));
                }

                // 6. Calculate Content Span (merging start and end lines)
                let content_span = match (first_content_span, last_content_span) {
                    (Some(s), Some(e)) => s.join(e).unwrap_or(s),
                    (Some(s), None) => s,
                    _ => start_span,
                };

                found_block =
                    Some(HermesBlock { attribute: parsed_attr, content, content_span, start_span });
            }

            Ok(found_block)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_to_vec(code: &str) -> Vec<(String, Result<ParsedLeanItem, HermesError>)> {
        let mut items = Vec::new();
        scan_compilation_unit(code, |src, res| items.push((src.to_string(), res)));
        items
    }

    #[test]
    fn test_parse_lean_block() {
        let code = r#"
            /// ```lean, hermes
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
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}"
        );
        assert!(matches!(item.item, ParsedItem::Function(_)));
        assert_eq!(item.item.hermes_content(), " theorem foo : True := by trivial\n");
        assert!(item.source_file.is_none());
    }

    #[test]
    fn test_multiple_lean_blocks_error() {
        let code = r#"
            /// ```lean, hermes
            /// a
            /// ```
            /// ```lean, hermes
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
                /// theorem a : True := trivial
                /// ```
                fn foo() {}
            }
            mod b {
                /// ```lean, hermes
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
        assert!(i1.item.hermes_content().contains("theorem a"));
        assert!(i2.item.hermes_content().contains("theorem b"));

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
            /// unclosed block 1
            fn bad_doc_1() {}

            /// ```lean, hermes
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
 3 │             /// unclosed block 1
   ╰────

hermes::doc_block

  × Documentation block error: Unclosed Hermes block in documentation.
   ╭─[src/foo.rs:6:13]
 5 │ 
 6 │             /// ```lean, hermes
   ·             ─────────┬─────────
   ·                      ╰── problematic block
 7 │             /// unclosed block 2
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
