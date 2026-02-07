use std::{
    fs, io,
    ops::Range,
    path::{Path, PathBuf},
};

use log::{debug, trace};
use miette::{NamedSource, SourceSpan};
use proc_macro2::Span;
use syn::{
    spanned::Spanned as _, visit::Visit, Attribute, Error, Expr, ItemEnum, ItemFn, ItemImpl,
    ItemMod, ItemStruct, ItemTrait, ItemUnion, Lit, Meta,
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

/// The item from the original source code.
#[derive(Clone, Debug)]
pub enum ParsedItem {
    Fn(ItemFn),
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
    Trait(ItemTrait),
    Impl(ItemImpl),
}

impl ParsedItem {
    /// Returns the attributes on this item.
    fn attrs(&self) -> &[Attribute] {
        match self {
            Self::Fn(item) => &item.attrs,
            Self::Struct(item) => &item.attrs,
            Self::Enum(item) => &item.attrs,
            Self::Union(item) => &item.attrs,
            Self::Trait(item) => &item.attrs,
            Self::Impl(item) => &item.attrs,
        }
    }
}

/// A complete parsed item including its module path and the extracted Lean block.
#[derive(Debug)]
pub struct ParsedLeanItem {
    pub item: ParsedItem,
    module_path: Vec<String>,
    lean_block: String,
    source_file: Option<PathBuf>,
}

/// Represents a `mod foo;` declaration found in the source.
#[derive(Debug, Clone)]
pub struct UnloadedModule {
    pub name: String,
    /// The value of `#[path = "..."]` if present.
    pub path_attr: Option<String>,
    pub span: proc_macro2::Span,
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
    scan_compilation_unit_internal(source, None, f, |m| unloaded_modules.push(m));
    unloaded_modules
}

/// Like [`scan_compilation_unit`], but reads the source code from a file path.
///
/// Parsing errors and generated items will be associated with this file path.
pub fn read_file_and_scan_compilation_unit<F>(
    path: &Path,
    f: F,
) -> Result<(String, Vec<UnloadedModule>), io::Error>
where
    F: FnMut(&str, Result<ParsedLeanItem, HermesError>),
{
    log::trace!("read_file_and_scan_compilation_unit({:?})", path);
    let source = fs::read_to_string(path).expect("Failed to read file");
    let unloaded_modules = scan_compilation_unit(&source, f);
    Ok((source, unloaded_modules))
}

fn scan_compilation_unit_internal<I, M>(
    source: &str,
    source_file: Option<PathBuf>,
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
    let _x = source_file
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
    fn check_and_add(&mut self, item: ParsedItem, span: Span) {
        let Range { start, end } = span.byte_range();
        let source = &self.source_code.as_str()[start..end];

        let attrs = item.attrs();
        trace!("Checking item in module path `{:?}` for ```lean block", self.current_path);
        match extract_lean_block(attrs) {
            Ok(Some(lean_block)) => {
                debug!("Found valid ```lean block for item in `{:?}`", self.current_path);
                (self.item_cb)(
                    source,
                    Ok(ParsedLeanItem {
                        item,
                        module_path: self.current_path.clone(),
                        lean_block,
                        source_file: self.source_file.clone(),
                    }),
                );
            }
            Ok(None) => {
                trace!("No ```lean block found for item");
            } // Skip item
            Err(e) => {
                debug!("Error extracting ```lean block: {}", e);
                (self.item_cb)(
                    source,
                    Err(HermesError::DocBlockError {
                        src: self.named_source.clone(),
                        span: span_to_miette(e.span()),
                        msg: e.to_string(),
                    }),
                );
            }
        }
    }
}

impl<'ast, I, M> Visit<'ast> for HermesVisitor<I, M>
where
    I: FnMut(&str, Result<ParsedLeanItem, HermesError>),
    M: FnMut(UnloadedModule),
{
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        let mod_name = node.ident.to_string();

        // Check for unloaded modules (mod foo;)
        if node.content.is_none() {
            (self.mod_cb)(UnloadedModule {
                name: mod_name.clone(),
                path_attr: extract_path_attr(&node.attrs),
                span: node.span(),
            });
        }

        trace!("Entering module: {}", mod_name);
        self.current_path.push(mod_name);
        syn::visit::visit_item_mod(self, node);
        let popped = self.current_path.pop();
        trace!("Exiting module: {}", popped.unwrap_or_default());
    }

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        trace!("Visiting Fn {}", node.sig.ident);
        self.check_and_add(ParsedItem::Fn(node.clone()), node.span());
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_item_struct(&mut self, node: &'ast ItemStruct) {
        trace!("Visiting Struct {}", node.ident);
        self.check_and_add(ParsedItem::Struct(node.clone()), node.span());
        syn::visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast ItemEnum) {
        trace!("Visiting Enum {}", node.ident);
        self.check_and_add(ParsedItem::Enum(node.clone()), node.span());
        syn::visit::visit_item_enum(self, node);
    }

    fn visit_item_union(&mut self, node: &'ast ItemUnion) {
        trace!("Visiting Union {}", node.ident);
        self.check_and_add(ParsedItem::Union(node.clone()), node.span());
        syn::visit::visit_item_union(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast ItemTrait) {
        trace!("Visiting Trait {}", node.ident);
        self.check_and_add(ParsedItem::Trait(node.clone()), node.span());
        syn::visit::visit_item_trait(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        trace!("Visiting Impl");
        self.check_and_add(ParsedItem::Impl(node.clone()), node.span());
        syn::visit::visit_item_impl(self, node);
    }
}

/// Helper to extract exactly one Lean block from a slice of attributes.
/// Returns `Ok(None)` if no block is found.
/// Returns `Err` if the block is malformed or multiple blocks are found.
fn extract_lean_block(attrs: &[Attribute]) -> Result<Option<String>, Error> {
    let mut lean_blocks = Vec::new();
    let mut in_block = false;
    let mut current_block = String::new();
    let mut block_start_span = None;

    trace!("Searching {} attributes for ```lean blocks", attrs.len());
    for attr in attrs {
        if attr.path().is_ident("doc") {
            if let Meta::NameValue(nv) = &attr.meta {
                if let Expr::Lit(expr_lit) = &nv.value {
                    if let Lit::Str(lit_str) = &expr_lit.lit {
                        let text = lit_str.value();
                        let span = lit_str.span();

                        // Split by newlines in case it's a multiline `/** ... */` block
                        // or multi-line string literal in a `#[doc = "..."]` attribute.
                        for line in text.lines() {
                            // Trim leading whitespace but leave rest intact so we can identify "```lean"
                            let mut trimmed = line.trim_start();

                            // Let's strip any trailing whitespace for comparison purposes
                            let trimmed_end = trimmed.trim_end();

                            // Handle block comment `*` prefix heuristics
                            if trimmed_end.starts_with('*')
                                && trimmed_end != "*"
                                && !trimmed_end.starts_with("**")
                            {
                                trimmed = trimmed[1..].trim_start();
                            }

                            let check_val = trimmed.trim_end();

                            if !in_block {
                                if check_val == "```lean" {
                                    trace!("Found opening ```lean tag");
                                    in_block = true;
                                    block_start_span = Some(span);
                                    current_block.push_str(line);
                                    current_block.push('\n');
                                }
                            } else {
                                current_block.push_str(line);
                                current_block.push('\n');
                                if check_val == "```" {
                                    trace!("Found closing ``` tag");
                                    in_block = false;
                                    lean_blocks
                                        .push((current_block.clone(), block_start_span.unwrap()));
                                    current_block.clear();
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if in_block {
        debug!("Unclosed ```lean block detected");
        return Err(Error::new(
            block_start_span.unwrap(),
            "Unclosed ```lean block in documentation",
        ));
    }

    if lean_blocks.is_empty() {
        trace!("Finished attribute scan: no lean blocks found");
        Ok(None)
    } else if lean_blocks.len() > 1 {
        debug!("Multiple ```lean blocks found");
        let mut err = Error::new(lean_blocks[1].1, "Multiple lean blocks found on a single item");
        for block in &lean_blocks[2..] {
            err.combine(Error::new(block.1, "Additional lean block found here"));
        }
        Err(err)
    } else {
        debug!("Successfully extracted exactly one ```lean block");
        Ok(Some(lean_blocks.into_iter().next().unwrap().0))
    }
}

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

fn span_to_miette(span: proc_macro2::Span) -> SourceSpan {
    let range = span.byte_range();
    SourceSpan::new(range.start.into(), range.end - range.start)
}

#[cfg(test)]
mod tests {
    use syn::spanned::Spanned as _;

    use super::*;

    fn parse_to_vec(code: &str) -> Vec<(String, Result<ParsedLeanItem, HermesError>)> {
        let mut items = Vec::new();
        scan_compilation_unit(code, |src, res| items.push((src.to_string(), res)));
        items
    }

    #[test]
    fn test_parse_lean_block() {
        let code = r#"
            /// ```lean
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        let (src, res) = items.into_iter().next().unwrap();
        let item = res.unwrap();
        assert_eq!(
            src,
            "/// ```lean
            /// theorem foo : True := by trivial
            /// ```
            fn foo() {}"
        );
        assert!(matches!(item.item, ParsedItem::Fn(_)));
        assert_eq!(item.lean_block, " ```lean\n theorem foo : True := by trivial\n ```\n");
        assert!(item.source_file.is_none());
    }

    #[test]
    fn test_multiple_lean_blocks_error() {
        let code = r#"
            /// ```lean
            /// a
            /// ```
            /// ```lean
            /// b
            /// ```
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        let (src, res) = items.into_iter().next().unwrap();
        let err = res.unwrap_err();
        assert_eq!(
            src,
            "/// ```lean
            /// a
            /// ```
            /// ```lean
            /// b
            /// ```
            fn foo() {}"
        );
        assert!(err.to_string().contains("Multiple lean blocks"));
    }

    #[test]
    fn test_unclosed_lean_block() {
        let code = r#"
            /// ```lean
            /// a
            fn foo() {}
        "#;
        let items = parse_to_vec(code);
        let (src, res) = items.into_iter().next().unwrap();
        let err = res.unwrap_err();
        assert_eq!(
            src,
            "/// ```lean
            /// a
            fn foo() {}"
        );
        assert!(err.to_string().contains("Unclosed"));
    }

    #[test]
    fn test_module_paths() {
        let code = r#"
            mod a {
                mod b {
                    /// ```lean
                    /// ```
                    fn foo() {}
                }
            }
        "#;
        let items = parse_to_vec(code);
        let (src, res) = items.into_iter().next().unwrap();
        let item = res.unwrap();
        assert_eq!(
            src,
            "/// ```lean
                    /// ```
                    fn foo() {}"
        );
        assert_eq!(item.module_path, vec!["a", "b"]);
    }

    #[test]
    fn test_visit_in_file() {
        let code = r#"
            /// ```lean
            /// a
            fn foo() {}
        "#;
        let mut items = Vec::new();
        scan_compilation_unit_internal(
            code,
            Some(Path::new("src/foo.rs").to_path_buf()),
            |source: &str, res| items.push((source.to_string(), res)),
            |_| {},
        );
        let (src, res) = items.into_iter().next().unwrap();
        assert_eq!(
            src,
            "/// ```lean
            /// a
            fn foo() {}"
        );

        let rep = format!("{:?}", miette::Report::new(res.unwrap_err()));
        assert!(rep.contains("src/foo.rs"));
        assert!(rep.contains("Unclosed"));
    }

    #[test]
    fn test_span_multiple_modules_precision() {
        let source = "mod a {
    mod b {
        /// ```lean
        /// theorem a : True := trivial
        /// ```
        fn bar() {}
    }
}
mod c {
    /// ```lean
    /// theorem b : False := sorry
    /// ```
    fn baz() {}
}
";
        let mut items = Vec::new();
        scan_compilation_unit(source, |_src, res| items.push(res));
        let i1 = items[0].as_ref().unwrap();
        let i2 = items[1].as_ref().unwrap();

        // Note that the span of `attrs()[0]` is only the very first line of the doc comment:
        // `/// ```lean`.
        // The rest of the comment lines are actually separate attributes `attrs()[1]`, `attrs()[2]`, etc.
        // because `///` style doc comments generate one `#[doc="..."]` attribute per line.

        let span1_start = i1.item.attrs().first().unwrap().span().byte_range().start;
        let span1_end = i1.item.attrs().last().unwrap().span().byte_range().end;

        let span2_start = i2.item.attrs().first().unwrap().span().byte_range().start;
        let span2_end = i2.item.attrs().last().unwrap().span().byte_range().end;

        let text1 = &source[span1_start..span1_end];
        let text2 = &source[span2_start..span2_end];

        assert_eq!(text1, "/// ```lean\n        /// theorem a : True := trivial\n        /// ```");
        assert_eq!(text2, "/// ```lean\n    /// theorem b : False := sorry\n    /// ```");
    }

    #[test]
    fn test_multiple_parsing_failures_output() {
        let code1 = r#"
            /// ```lean
            /// unclosed block 1
            fn bad_doc_1() {}

            /// ```lean
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
            |_src, res| items.push(res),
            |_| {},
        );
        scan_compilation_unit_internal(
            code2,
            Some(path.to_path_buf()),
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

  × Documentation block error: Unclosed ```lean block in documentation
   ╭─[src/foo.rs:2:13]
 1 │ 
 2 │             /// ```lean
   ·             ─────┬─────
   ·                  ╰── problematic block
 3 │             /// unclosed block 1
   ╰────

hermes::doc_block

  × Documentation block error: Unclosed ```lean block in documentation
   ╭─[src/foo.rs:6:13]
 5 │ 
 6 │             /// ```lean
   ·             ─────┬─────
   ·                  ╰── problematic block
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
