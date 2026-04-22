use proc_macro2::Span;
use syn::{ExprLit, MetaNameValue};

use super::*;

/// Parsing logic for Anneal attributes and documentation blocks.
///
/// This module handles the extraction and parsing of `/// ````anneal` blocks
/// from Rust source code. It supports various block types (Function, Type,
/// Trait, Impl) and their respective sections (requires, ensures, proof,
/// etc.).
///
/// ### Indentation-Sensitive Parsing (Off-Side Rule)
/// Anneal relies strictly on indentation to determine block structure within
/// the parsed comments.
/// - Top-level block keywords (`context`, `requires`, `ensures`, `proof`,
///   `axiom`) establish a baseline indentation.
/// - Content lines *must* be indented deeper than their associated
///   structural keyword to be treated as children of that block.
///
/// This design enforces a Python-like semantic meaning without
/// requiring braces in standard Rust comments.
///
/// The parsing process involves:
/// 1. Extracting raw documentation lines using `extract_doc_line` (handling
///    `/// `, `/** ... */`, `#[doc = ...]`).
/// 2. Identifying Anneal blocks denoted by ` ```lean, anneal...` fences.
/// 3. Parsing the indented content into structured `RawAnnealSpecBody`
///    blocks.
/// 4. Validating and converting the raw body into context-specific types
///    (e.g., `FunctionAnnealBlock`).
///
/// Represents a parsed attribute from a Anneal info string on a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionAttribute {
    /// `spec`: Indicates a function specification and proof.
    Spec,
    /// `unsafe(axiom)`: Indicates an axiomatization of an unsafe function.
    UnsafeAxiom,
}

/// A single logical clause in a Anneal specification (e.g. one `requires`
/// entry).
///
/// A clause consists of a starting keyword line and any subsequent indented
/// lines.
#[derive(Debug, Clone)]
pub struct Clause<M: ThreadSafety = Local> {
    pub keyword_span: AstNode<Span, M>,
    pub name: Option<SpannedLine<M>>,
    pub lines: Vec<SpannedLine<M>>,
}

/// A collection of logical clauses (e.g., `requires`, `ensures`, `proof`),
/// uniquely segmented into an optional unnamed singleton and a named map.
#[derive(Debug, Clone)]
pub struct Propositions<M: ThreadSafety = Local> {
    pub unnamed: Option<Clause<M>>,
    pub named: std::collections::BTreeMap<String, Clause<M>>,
}

impl<M: ThreadSafety> Default for Propositions<M> {
    fn default() -> Self {
        Self { unnamed: None, named: std::collections::BTreeMap::new() }
    }
}

impl<M: ThreadSafety> Propositions<M> {
    pub fn is_empty(&self) -> bool {
        self.unnamed.is_none() && self.named.is_empty()
    }

    pub fn push(&mut self, clause: Clause<M>) -> Result<(), String> {
        if let Some(name) = &clause.name {
            if self.named.contains_key(&name.content) {
                return Err(format!("Duplicate bound name `{}`.", name.content));
            }
            self.named.insert(name.content.clone(), clause);
        } else {
            if self.unnamed.is_some() {
                return Err("Multiple unnamed bounds are not allowed. If you have multiple bounds, they must all be named (e.g., `requires (my_name):`).".to_string());
            }
            self.unnamed = Some(clause);
        }
        Ok(())
    }
}

/// A parsed Anneal documentation block attached to a function.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct FunctionAnnealBlock<M: ThreadSafety = Local> {
    pub content: Vec<SpannedLine<M>>,
    pub content_span: AstNode<Span, M>,
    pub start_span: AstNode<Span, M>,
    pub mode: FunctionAttribute,
}


/// A parsed Anneal documentation block attached to a struct, enum, or union.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypeAnnealBlock<M: ThreadSafety = Local> {
    pub content: Vec<SpannedLine<M>>,
    pub content_span: AstNode<Span, M>,
    pub start_span: AstNode<Span, M>,
}

/// A parsed Anneal documentation block attached to a trait.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TraitAnnealBlock<M: ThreadSafety = Local> {
    pub content: Vec<SpannedLine<M>>,
    pub content_span: AstNode<Span, M>,
    pub start_span: AstNode<Span, M>,
}

/// A parsed Anneal documentation block attached to an impl.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ImplAnnealBlock<M: ThreadSafety = Local> {
    pub content: Vec<SpannedLine<M>>,
    pub content_span: AstNode<Span, M>,
    pub start_span: AstNode<Span, M>,
}



#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedInfoString {
    FunctionMode(FunctionAttribute),
    GenericMode,
}

/// Parses the info string of a code block.
///
/// * `info`: The info string text (e.g. "lean, anneal, spec").
///
/// Returns:
/// * `Ok(Some(Some(attr)))` if `anneal` was found and had valid arguments.
/// * `Ok(Some(None))` if `anneal` was found but had no arguments.
/// * `Ok(None)` if `anneal` was not found.
/// * `Err(msg)` if `anneal` was found but had invalid arguments.
fn parse_anneal_info_string(info: &str) -> Result<Option<ParsedInfoString>, String> {
    let mut tokens = info.split(',').map(str::trim).filter(|s| !s.is_empty());

    // Find and consume the `anneal` token.
    if tokens.find(|&t| t == "anneal").is_none() {
        return Ok(None);
    }

    let first_arg = tokens.next();
    if let Some(second) = tokens.next() {
        let first = first_arg.unwrap_or("");
        return Err(format!(
            "Multiple attributes specified after 'anneal' ('{first}', '{second}'). Only one attribute is allowed."
        ));
    }

    use FunctionAttribute::*;
    use ParsedInfoString::*;
    match first_arg {
        None => Ok(Some(GenericMode)),
        Some("spec") => Ok(Some(FunctionMode(Spec))),
        Some("unsafe(axiom)") => Ok(Some(FunctionMode(UnsafeAxiom))),
        Some(token) if token.starts_with("unsafe") => {
            Err(format!("Unknown or malformed attribute: '{token}'. Did you mean 'unsafe(axiom)'?"))
        }
        Some(token) => Err(format!(
            "Unrecognized Anneal attribute: '{token}'. Supported attributes are 'spec', 'unsafe(axiom)'."
        )),
    }
}

/// Extracts the offset of the content within a standard slash comment
/// (e.g., `/// `, `//!`, `/**`, etc.).
fn extract_slash_comment_offset(trimmed: &str, leading_ws: usize) -> Option<usize> {
    if trimmed.starts_with("///")
        || trimmed.starts_with("//!")
        || trimmed.starts_with("/**")
        || trimmed.starts_with("/*!")
    {
        Some(leading_ws + 3)
    } else {
        None
    }
}

/// Extracts the offset of the content within a `#[doc = "..."]` attribute.
fn extract_bracket_doc_offset(trimmed: &str, leading_ws: usize) -> Option<usize> {
    let after_bracket = trimmed.strip_prefix("#[")?;

    // We need to find the opening quote of the string literal after `doc`
    // and `=`.
    // A robust way is to find the first `=` and then the first quote.
    let eq_idx = after_bracket.find('=')?;
    let after_eq = &after_bracket[eq_idx + 1..];

    let quote_intra_idx = after_eq.find(|c: char| ['"', 'r'].contains(&c))?;
    let quote_total_idx = eq_idx + 1 + quote_intra_idx;
    let literal_part = &after_bracket[quote_total_idx..];

    let quote_width = if literal_part.starts_with('r') {
        // Raw string: r"...", r#"..."#, etc.
        literal_part.find('"').map(|i| i + 1).unwrap_or(1)
    } else {
        1 // Standard "
    };

    // +2 for "#["
    Some(leading_ws + 2 + quote_total_idx + quote_width)
}

/// Extracts the string content and spans for each line from a documentation
/// attribute.
///
/// This handles `/// `, `//!`, `/** ... */`, and `#[doc = "..."]` attributes
/// uniformly. It attempts to calculate the precise source span for each line
/// of content, which is critical for accurate error reporting.
///
/// If the source code cannot be read or the content doesn't match the
/// expected locations, it falls back to using the attribute's full span.
pub(crate) fn extract_doc_line(attr: &Attribute, source: &str) -> Vec<(String, SourceSpan, Span)> {
    if !attr.path().is_ident("doc") {
        return Vec::new();
    }

    match &attr.meta {
        Meta::NameValue(MetaNameValue {
            value: Expr::Lit(ExprLit { lit: Lit::Str(s), .. }),
            ..
        }) => {
            let content = s.value();
            let original_span = s.span();
            let span = crate::parse::span_to_miette(original_span);

            // Calculate the start of the span in the source code.
            let start = span.offset();
            let len = span.len();

            // If we can't read the source (e.g., during testing with dummy
            // sources), fallback to the original span.
            let raw_slice = match source.get(start..start + len) {
                Some(slice) => slice,
                None => return vec![(content, span, original_span)],
            };

            // Determine the offset of the content within the raw slice.
            //
            // We need to skip over the comment markers (`/// `, `//!`,
            // `/**`) or the attribute syntax (`#[doc = ...]`) to find the
            // actual text content.
            let trimmed = raw_slice.trim_start();
            let leading_ws = raw_slice.len() - trimmed.len();

            let offset = extract_slash_comment_offset(trimmed, leading_ws)
                .or_else(|| extract_bracket_doc_offset(trimmed, leading_ws))
                .unwrap_or_else(|| {
                    // Fallback: search for content if we can't recognize the structure
                    raw_slice.find(&content).unwrap_or(0)
                });

            let real_start = start + offset;

            // Verify that the content we found matches exactly what `syn` gave
            // us. This is a safety check: strict span calculation relies on
            // this match. If they don't match (e.g., due to macro expansion or
            // escaped characters we didn't account for completely), we still
            // return the content but with a less precise span (falling back to
            // the attribute span).
            let expected_source_slice = source.get(real_start..real_start + content.len());
            let exact_match = expected_source_slice == Some(content.as_str());

            let mut results = Vec::new();
            let mut current_offset = real_start;

            // Split multiline content (common in `/** ... */` blocks) into
            // individual lines. Each line gets its own calculated span.
            for part in content.split('\n') {
                let part_len = part.len();
                let mut part_span = if exact_match {
                    SourceSpan::new(current_offset.into(), part_len)
                } else {
                    SourceSpan::new(real_start.into(), content.len())
                };

                if exact_match {
                    current_offset += part_len + 1;
                }

                let final_content = if let Some(stripped) = part.strip_suffix('\r') {
                    if exact_match {
                        part_span = SourceSpan::new(part_span.offset().into(), part_len - 1);
                    }
                    stripped
                } else {
                    part
                };

                results.push((final_content.to_string(), part_span, original_span));
            }
            results
        }
        _ => Vec::new(),
    }
}

/// Consumes lines from the iterator until a closing fence (```) is found.
///
/// Returns the collected lines and the span of the closing fence (or the last
/// line).
fn parse_block_lines<I>(
    iter: &mut I,
    start: Span,
    fence: &str,
) -> Result<(Vec<SpannedLine>, Span), Error>
where
    I: Iterator<Item = (String, SourceSpan, Span)>,
{
    let mut lines = Vec::new();
    let mut end = start;
    let mut closed = false;

    for (line, span, original_span) in iter {
        if line.trim().starts_with(fence) {
            closed = true;
            break;
        }

        lines.push(SpannedLine { content: line, span, raw_span: AstNode::new(original_span) });
        end = original_span;
    }

    if !closed {
        return Err(Error::new(start, "Unclosed Anneal block in documentation."));
    }

    Ok((lines, end))
}

/// Parses a "Anneal block" from a sequence of attributes.
///
/// This function flat-maps all documentation attributes into a single stream
/// of lines, allowing it to handle both single-line `/// ` comments and
/// multi-line `/** ... */` blocks transparently. It looks for a start fence
/// ` ```... ` and parses the content until the end fence.
fn parse_anneal_block_common(
    attrs: &[Attribute],
    source: &str,
) -> Result<Option<(ParsedAnnealBody, ParsedInfoString)>, Error> {
    let mut all_lines = attrs.iter().flat_map(|attr| extract_doc_line(attr, source));

    let mut block = None;

    while let Some((text, _, start_original)) = all_lines.next() {
        // Check for start fence
        let trimmed = text.trim();
        if !trimmed.starts_with("```") {
            // Not a start fence, skip this line logic
            continue;
        }

        let mut fence_len = 0;
        for c in trimmed.chars() {
            if c == '`' {
                fence_len += 1;
            } else {
                break;
            }
        }
        let fence = &trimmed[..fence_len];
        let info = &trimmed[fence_len..];

        let parsed_info = match parse_anneal_info_string(info.trim()) {
            Ok(Some(a)) => a,
            Ok(Option::None) => continue,
            Err(msg) => return Err(Error::new(start_original, msg)),
        };

        if block.is_some() {
            return Err(Error::new(
                start_original,
                "Multiple Anneal blocks found on a single item.",
            ));
        }

        let (lines, end) = parse_block_lines(&mut all_lines, start_original, fence)?;

        block = Some((
            ParsedAnnealBody {
                content: lines,
                content_span: start_original.join(end).unwrap_or(start_original),
                start_span: start_original,
            },
            parsed_info,
        ));
    }
    Ok(block)
}

/// Returns an error containing `msg` if `section` is non-empty.
fn reject_section(section: &RawSection, msg: &str) -> Result<(), Error> {
    if let Some(span) = &section.keyword_span { Err(Error::new(span.inner, msg)) } else { Ok(()) }
}

/// Returns an error containing `msg` if `clauses` is non-empty.
fn reject_clauses(clauses: &[Clause<Local>], msg: &str) -> Result<(), Error> {
    if let Some(clause) = clauses.first() {
        Err(Error::new(clause.keyword_span.inner, msg))
    } else {
        Ok(())
    }
}

/// Returns an error containing `msg` if `clauses` is non-empty.
fn reject_propositions(clauses: &Propositions<Local>, msg: &str) -> Result<(), Error> {
    if let Some(clause) = clauses.iter().next() {
        Err(Error::new(clause.keyword_span.inner, msg))
    } else {
        Ok(())
    }
}

fn parse_item_block_common(
    attrs: &[Attribute],
    context_name: &str,
    source: &str,
) -> Result<Option<ParsedAnnealBody>, Error> {
    parse_anneal_block_common(attrs, source)?
        .map(|(item, info)| {
            if !matches!(info, ParsedInfoString::GenericMode) {
                return Err(Error::new(
                    item.start_span,
                    format!(
                        "Function attributes (like `spec`) are not permitted on {context_name}."
                    ),
                ));
            }
            Ok(item)
        })
        .transpose()
}

impl FunctionAnnealBlock<Local> {
    pub fn parse_from_attrs(
        attrs: &[Attribute],
        _is_unsafe: bool,
        source: &str,
    ) -> Result<Option<Self>, Error> {
        let Some((item, parsed_info)) = parse_anneal_block_common(attrs, source)? else {
            return Ok(None);
        };

        let attribute = match parsed_info {
            ParsedInfoString::FunctionMode(attr) => attr,
            ParsedInfoString::GenericMode => FunctionAttribute::Spec, // Implicit `spec` for functions
        };

        Ok(Some(Self {
            content: item.content,
            content_span: AstNode::new(item.content_span),
            start_span: AstNode::new(item.start_span),
            mode: attribute,
        }))
    }
}

impl TypeAnnealBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute], source: &str) -> Result<Option<Self>, Error> {
        let Some(item) = parse_item_block_common(attrs, "types", source)? else {
            return Ok(None);
        };

        Ok(Some(Self {
            content: item.content,
            content_span: AstNode::new(item.content_span),
            start_span: AstNode::new(item.start_span),
        }))
    }
}

impl TraitAnnealBlock<Local> {
    pub fn parse_from_attrs(
        attrs: &[Attribute],
        _is_unsafe: bool,
        source: &str,
    ) -> Result<Option<Self>, Error> {
        let Some(item) = parse_item_block_common(attrs, "traits", source)? else {
            return Ok(None);
        };

        Ok(Some(Self {
            content: item.content,
            content_span: AstNode::new(item.content_span),
            start_span: AstNode::new(item.start_span),
        }))
    }
}

impl ImplAnnealBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute], source: &str) -> Result<Option<Self>, Error> {
        let Some(item) = parse_item_block_common(attrs, "impl items", source)? else {
            return Ok(None);
        };

        Ok(Some(Self {
            content: item.content,
            content_span: AstNode::new(item.content_span),
            start_span: AstNode::new(item.start_span),
        }))
    }
}

/// A single parsed line from a documentation block, retaining structural layout info.
#[derive(Debug, Clone)]
pub struct SpannedLine<M: ThreadSafety = Local> {
    pub content: String,
    pub span: SourceSpan,
    pub raw_span: AstNode<Span, M>,
}

#[derive(Debug, Default, Clone)]
pub(super) struct RawSection {
    /// The exact span of the line where the keyword (e.g., `proof`)
    /// appeared.
    pub(super) keyword_span: Option<AstNode<Span, Local>>,
    pub(super) lines: Vec<SpannedLine<Local>>,
}

impl RawSection {
    /// Returns true if the keyword was encountered, even if no arguments were
    /// provided.
    #[allow(dead_code)]
    pub(super) fn is_present(&self) -> bool {
        self.keyword_span.is_some()
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Section {
    Init,
    Context,
    Requires,
    Ensures,
    ProofContext,
    ProofCase,
    IsValid,
    IsSafe,
}

pub(super) struct ParsedAnnealBody {
    pub(super) content: Vec<SpannedLine<Local>>,
    pub(super) content_span: Span,
    pub(super) start_span: Span,
}

impl<M: ThreadSafety> LiftToSafe for SpannedLine<M> {
    type Target = SpannedLine<Safe>;
    fn lift(self) -> Self::Target {
        SpannedLine { content: self.content, span: self.span, raw_span: self.raw_span.lift() }
    }
}



impl<M: ThreadSafety> LiftToSafe for FunctionAnnealBlock<M> {
    type Target = FunctionAnnealBlock<Safe>;
    fn lift(self) -> Self::Target {
        FunctionAnnealBlock {
            content: self.content.into_iter().map(|l| l.lift()).collect(),
            content_span: self.content_span.lift(),
            start_span: self.start_span.lift(),
            mode: self.mode,
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TypeAnnealBlock<M> {
    type Target = TypeAnnealBlock<Safe>;
    fn lift(self) -> Self::Target {
        TypeAnnealBlock {
            content: self.content.into_iter().map(|l| l.lift()).collect(),
            content_span: self.content_span.lift(),
            start_span: self.start_span.lift(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TraitAnnealBlock<M> {
    type Target = TraitAnnealBlock<Safe>;
    fn lift(self) -> Self::Target {
        TraitAnnealBlock {
            content: self.content.into_iter().map(|l| l.lift()).collect(),
            content_span: self.content_span.lift(),
            start_span: self.start_span.lift(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for ImplAnnealBlock<M> {
    type Target = ImplAnnealBlock<Safe>;
    fn lift(self) -> Self::Target {
        ImplAnnealBlock {
            content: self.content.into_iter().map(|l| l.lift()).collect(),
            content_span: self.content_span.lift(),
            start_span: self.start_span.lift(),
        }
    }
}

impl<M: ThreadSafety> Propositions<M> {
    pub fn iter(&self) -> impl Iterator<Item = &Clause<M>> {
        self.unnamed.iter().chain(self.named.values())
    }
}

impl<M: ThreadSafety> std::iter::FromIterator<Clause<M>> for Propositions<M> {
    fn from_iter<T: IntoIterator<Item = Clause<M>>>(iter: T) -> Self {
        let mut props = Propositions { unnamed: None, named: std::collections::BTreeMap::new() };
        for clause in iter {
            props.push(clause).unwrap();
        }
        props
    }
}

impl<M: ThreadSafety> std::ops::Index<usize> for Propositions<M> {
    type Output = Clause<M>;

    fn index(&self, index: usize) -> &Self::Output {
        self.iter().nth(index).expect("Index out of bounds")
    }
}

#[cfg(test)]
mod tests {
    use syn::parse_quote;

    use super::*;

    impl<M: ThreadSafety> Propositions<M> {
        pub fn len(&self) -> usize {
            self.named.len() + if self.unnamed.is_some() { 1 } else { 0 }
        }
    }

    #[test]
    fn test_parse_anneal_info_string() {
        // Not anneal
        assert_eq!(parse_anneal_info_string(""), Ok(None));
        assert_eq!(parse_anneal_info_string("rust"), Ok(None));
        assert_eq!(parse_anneal_info_string("lean"), Ok(None));

        // Just anneal
        assert_eq!(
            parse_anneal_info_string("lean, anneal"),
            Ok(Some(ParsedInfoString::GenericMode))
        );
        assert_eq!(parse_anneal_info_string(" anneal "), Ok(Some(ParsedInfoString::GenericMode)));
        assert_eq!(
            parse_anneal_info_string("lean , anneal "),
            Ok(Some(ParsedInfoString::GenericMode))
        );

        // Valid attributes
        assert!(matches!(
            parse_anneal_info_string("anneal, spec"),
            Ok(Some(ParsedInfoString::FunctionMode(FunctionAttribute::Spec)))
        ));
        assert!(matches!(
            parse_anneal_info_string("lean,anneal,unsafe(axiom)"),
            Ok(Some(ParsedInfoString::FunctionMode(FunctionAttribute::UnsafeAxiom)))
        ));

        // Invalid attributes
        assert!(parse_anneal_info_string("anneal, unknown").is_err());
        assert!(parse_anneal_info_string("anneal, unsafe").is_err());
        assert!(parse_anneal_info_string("anneal, spec, other").is_err());
    }

    #[test]
    fn test_extract_doc_line() {
        // Valid doc attribute
        let attr: syn::Attribute = parse_quote!(#[doc = " test line"]);
        let result = extract_doc_line(&attr, "");
        assert_eq!(result.len(), 1);
        let (content, _, _) = &result[0];
        assert_eq!(content, " test line");

        // Non-doc attribute
        let attr: syn::Attribute = parse_quote!(#[derive(Clone)]);
        assert!(extract_doc_line(&attr, "").is_empty());

        // Alternate doc syntax (e.g., hidden)
        let attr: syn::Attribute = parse_quote!(#[doc(hidden)]);
        assert!(extract_doc_line(&attr, "").is_empty());
    }

    #[test]
    fn test_parse_from_attrs_valid_spec() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```lean, anneal, spec"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionAnnealBlock::parse_from_attrs(&attrs, false, "").unwrap().unwrap();
        assert_eq!(block.content.len(), 3);
        assert_eq!(block.content[0].content, " context:");
        assert_eq!(block.content[1].content, " body 1");
        assert_eq!(block.content[2].content, " body 2");
        assert_eq!(block.mode, FunctionAttribute::Spec);
    }

    #[test]
    fn test_parse_from_attrs_valid_axiom() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```lean, anneal, unsafe(axiom)"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionAnnealBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
        assert_eq!(block.content.len(), 3);
        assert_eq!(block.content[0].content, " context:");
        assert_eq!(block.content[1].content, " body 1");
        assert_eq!(block.content[2].content, " body 2");
        assert_eq!(block.mode, FunctionAttribute::UnsafeAxiom);
    }

    #[test]
    fn test_parse_from_attrs_unclosed() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```anneal"]), parse_quote!(#[doc = " no end fence"])];
        let err = FunctionAnnealBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "Unclosed Anneal block in documentation.");
    }

    #[test]
    fn test_parse_from_attrs_interrupted() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```anneal"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " line 1"]),
            parse_quote!(#[derive(Clone)]), // Interrupts contiguous doc lines
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionAnnealBlock::parse_from_attrs(&attrs, false, "").unwrap().unwrap();
        assert_eq!(block.content.len(), 2);
        assert_eq!(block.content[0].content, " context:");
        assert_eq!(block.content[1].content, " line 1");
    }

    #[test]
    fn test_parse_from_attrs_multiple_blocks() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```anneal"]),
            parse_quote!(#[doc = " ```"]),
            parse_quote!(#[doc = " ```anneal"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = FunctionAnnealBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "Multiple Anneal blocks found on a single item.");
    }

    fn mk_lines(lines: &[&str]) -> Vec<SpannedLine> {
        lines
            .iter()
            .map(|l| SpannedLine {
                content: (*l).to_string(),
                span: miette::SourceSpan::new(0.into(), 0),
                raw_span: AstNode::new(proc_macro2::Span::call_site()),
            })
            .collect()
    }
















    #[test]



























































    #[test]
    fn test_extract_doc_line_offsets() {
        let source = "///     sorry\nfn foo() {}";
        let file = syn::parse_file(source).unwrap();
        let item = &file.items[0];
        let attr = match item {
            syn::Item::Fn(f) => &f.attrs[0],
            _ => panic!("Expected function"),
        };

        let lines = extract_doc_line(attr, source);
        assert!(!lines.is_empty());
        let (content, span, _) = &lines[0];

        // Verify content matches what is in the source at that span
        let start = span.offset();
        let len = span.len();
        let source_slice = &source[start..start + len];
        assert_eq!(content, source_slice, "Content should match source slice at returned span");
        assert!(start >= 3, "Span should start after '/// '");
    }

    #[test]
    fn test_extract_doc_line_edge_cases() {
        let cases = vec![
            // 1. Sugared Comments
            ("/// content", " content", 3),
            ("///   content", "   content", 3),
            ("/// content", "content", 3),
            ("//! content", " content", 3),
            // 2. Block Comments
            ("/** content */", " content ", 3),
            ("/*! content */", " content ", 3),
            // 3. Attribute Form
            (r#"#[doc = " content"]"#, " content", 9),
            (r#"#[doc="content"]"#, "content", 7),
            (r#"#[doc   =   "content"]"#, "content", 13),
            // 4. Raw Strings
            (r##"#[doc = r" content"]"##, " content", 10),
            (r##"#[doc = r#" content"#]"##, " content", 11),
            (r###"#[doc = r##" content"##]"###, " content", 12),
            // 5. UTF-8
            ("/// 🦀 content", " 🦀 content", 3),
            // 6. No trailing space
            ("///content", "content", 3),
            ("//!content", "content", 3),
            ("/**content*/", "content*/", 3),
            ("/*!content*/", "content*/", 3),
        ];

        let mut failures = Vec::new();

        for (source, _expected_content_value, expected_offset) in cases {
            let full_source = format!("{}\nfn foo() {{}}", source);
            let file = syn::parse_file(&full_source).expect("Failed to parse dummy source");

            // Try to find the attribute on the function first, then on the
            // file (for inner attrs).
            let item = &file.items[0];
            let attr = match item {
                syn::Item::Fn(f) => {
                    if !f.attrs.is_empty() {
                        &f.attrs[0]
                    } else if !file.attrs.is_empty() {
                        &file.attrs[0]
                    } else {
                        panic!("No attributes found for case: {}", source);
                    }
                }
                _ => panic!("Expected function"),
            };

            let lines = extract_doc_line(attr, &full_source);
            if lines.is_empty() {
                panic!("Failed to extract doc line for case: {}", source);
            }
            let (content, span, _) = &lines[0];

            let start = span.offset();

            // Check offset matches expected
            if start != expected_offset {
                failures.push(format!(
                    "Offset mismatch for '{}': expected {}, got {}",
                    source, expected_offset, start
                ));
            }

            // Check content matches source slice
            let source_slice = &full_source[start..start + span.len()];
            if content != source_slice && !source.contains("escaped") {
                failures.push(format!(
                    "Content-Source mismatch for '{}': content {:?}, source slice {:?}",
                    source, content, source_slice
                ));
            }
        }

        if !failures.is_empty() {
            panic!("Failures:\n{}", failures.join("\n"));
        }
    }

    #[test]
    fn test_multiline_block_comment() {
        let source = "/**
  line 1
  line 2
```
*/
fn foo() {}";
        let file = syn::parse_file(source).unwrap();
        let item = &file.items[0];
        let attrs = match item {
            syn::Item::Fn(f) => &f.attrs,
            _ => panic!("Expected function"),
        };

        let mut iter = attrs.iter().flat_map(|a| extract_doc_line(a, source));
        let (lines, _) =
            parse_block_lines(&mut iter, proc_macro2::Span::call_site(), "```").unwrap();

        println!("Parsed {} lines", lines.len());
        for (i, line) in lines.iter().enumerate() {
            println!("Line {}: {:?}", i, line.content);
        }

        assert!(lines.len() >= 3, "Expected split lines, got {}", lines.len());
        assert!(lines.iter().any(|l| l.content.contains("line 1")));
        assert!(lines.iter().any(|l| l.content.contains("line 2")));
    }
}
