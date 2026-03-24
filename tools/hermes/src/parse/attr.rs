use proc_macro2::Span;
use syn::{ExprLit, MetaNameValue};

use super::*;

/// Parsing logic for Hermes attributes and documentation blocks.
///
/// This module handles the extraction and parsing of `/// ````hermes` blocks
/// from Rust source code. It supports various block types (Function, Type,
/// Trait, Impl) and their respective sections (requires, ensures, proof,
/// etc.).
///
/// ### Indentation-Sensitive Parsing (Off-Side Rule)
/// Hermes relies strictly on indentation to determine block structure within
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
/// 2. Identifying Hermes blocks denoted by ` ```lean, hermes...` fences.
/// 3. Parsing the indented content into structured `RawHermesSpecBody`
///    blocks.
/// 4. Validating and converting the raw body into context-specific types
///    (e.g., `FunctionHermesBlock`).
///
/// Represents a parsed attribute from a Hermes info string on a function.
#[derive(Debug, Clone, PartialEq, Eq)]
enum FunctionAttribute {
    /// `spec`: Indicates a function specification and proof.
    Spec,
    /// `unsafe(axiom)`: Indicates an axiomatization of an unsafe function.
    UnsafeAxiom,
}

/// A single logical clause in a Hermes specification (e.g. one `requires`
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

/// A parsed Hermes documentation block attached to a function.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct FunctionHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub requires: Propositions<M>,
    pub ensures: Propositions<M>,
    pub inner: FunctionBlockInner<M>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum FunctionBlockInner<M: ThreadSafety = Local> {
    Proof { context: Vec<SpannedLine<M>>, cases: Propositions<M> },
    /// An axiom block (using `unsafe(axiom)`).
    Axiom,
}

/// A parsed Hermes documentation block attached to a struct, enum, or union.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypeHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub is_valid: Vec<Clause<M>>,
}

/// A parsed Hermes documentation block attached to a trait.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TraitHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub is_safe: Vec<Clause<M>>,
}

/// A parsed Hermes documentation block attached to an impl.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ImplHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
}

/// Common fields shared by all Hermes documentation blocks.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct HermesBlockCommon<M: ThreadSafety = Local> {
    pub context: Vec<SpannedLine<M>>,
    /// The span of the entire block, including the opening and closing ` ``` `
    /// lines.
    pub content_span: AstNode<Span, M>,
    /// The span of the opening ` ``` ` line.
    pub start_span: AstNode<Span, M>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedInfoString {
    FunctionMode(FunctionAttribute),
    GenericMode,
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
fn parse_hermes_info_string(info: &str) -> Result<Option<ParsedInfoString>, String> {
    let mut tokens = info.split(',').map(str::trim).filter(|s| !s.is_empty());

    // Find and consume the `hermes` token.
    if tokens.find(|&t| t == "hermes").is_none() {
        return Ok(None);
    }

    let first_arg = tokens.next();
    if let Some(second) = tokens.next() {
        let first = first_arg.unwrap_or("");
        return Err(format!(
            "Multiple attributes specified after 'hermes' ('{first}', '{second}'). Only one attribute is allowed."
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
            "Unrecognized Hermes attribute: '{token}'. Supported attributes are 'spec', 'unsafe(axiom)'."
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
        return Err(Error::new(start, "Unclosed Hermes block in documentation."));
    }

    Ok((lines, end))
}

/// Parses a "Hermes block" from a sequence of attributes.
///
/// This function flat-maps all documentation attributes into a single stream
/// of lines, allowing it to handle both single-line `/// ` comments and
/// multi-line `/** ... */` blocks transparently. It looks for a start fence
/// ` ```... ` and parses the content until the end fence.
fn parse_hermes_block_common(
    attrs: &[Attribute],
    source: &str,
) -> Result<Option<(ParsedHermesBody, ParsedInfoString)>, Error> {
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

        let parsed_info = match parse_hermes_info_string(info.trim()) {
            Ok(Some(a)) => a,
            Ok(Option::None) => continue,
            Err(msg) => return Err(Error::new(start_original, msg)),
        };

        if block.is_some() {
            return Err(Error::new(
                start_original,
                "Multiple Hermes blocks found on a single item.",
            ));
        }

        let (lines, end) = parse_block_lines(&mut all_lines, start_original, fence)?;

        let body = match RawHermesSpecBody::parse(&lines) {
            Ok(body) => body,
            Err((err_span, msg)) => {
                // Map the error span back to the raw source span if possible.
                let raw_span = lines
                    .iter()
                    .find(|l| l.span == err_span)
                    .map(|l| l.raw_span.inner)
                    .unwrap_or(start_original);
                return Err(Error::new(raw_span, msg));
            }
        };
        block = Some((
            ParsedHermesBody {
                body,
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
) -> Result<Option<(HermesBlockCommon, RawHermesSpecBody)>, Error> {
    parse_hermes_block_common(attrs, source)?
        .map(|(item, info)| {
            if !matches!(info, ParsedInfoString::GenericMode) {
                return Err(Error::new(
                    item.start_span,
                    format!(
                        "Function attributes (like `spec`) are not permitted on {context_name}."
                    ),
                ));
            }

            let mut body = item.body;
            reject_propositions(
                &body.requires,
                "`requires` sections are only permitted on functions.",
            )?;
            reject_propositions(
                &body.ensures,
                "`ensures` sections are only permitted on functions.",
            )?;
            reject_section(
                &body.proof_context,
                "`proof context` sections are only permitted on `spec` functions.",
            )?;
            reject_propositions(
                &body.proof_cases,
                "`proof` sections are only permitted on `spec` functions.",
            )?;

            let common = HermesBlockCommon {
                context: std::mem::take(&mut body.context.lines),
                content_span: AstNode::new(item.content_span),
                start_span: AstNode::new(item.start_span),
            };

            Ok((common, body))
        })
        .transpose()
}

impl FunctionHermesBlock<Local> {
    pub fn parse_from_attrs(
        attrs: &[Attribute],
        is_unsafe: bool,
        source: &str,
    ) -> Result<Option<Self>, Error> {
        let Some((item, parsed_info)) = parse_hermes_block_common(attrs, source)? else {
            return Ok(None);
        };

        let attribute = match parsed_info {
            ParsedInfoString::FunctionMode(attr) => attr,
            ParsedInfoString::GenericMode => FunctionAttribute::Spec, // Implicit `spec` for functions
        };

        let body = item.body;
        reject_clauses(&body.is_valid, "`isValid` sections are only permitted on types.")?;
        reject_clauses(&body.is_safe, "`isSafe` sections are only permitted on traits.")?;

        if !is_unsafe {
            reject_propositions(
                &body.requires,
                "`requires` sections are only permitted on `unsafe` functions.",
            )?;
        }

        let inner = match attribute {
            FunctionAttribute::Spec => {
                FunctionBlockInner::Proof {
                    context: body.proof_context.lines,
                    cases: body.proof_cases,
                }
            }
            FunctionAttribute::UnsafeAxiom => {
                reject_section(
                    &body.proof_context,
                    "`proof context` sections are only permitted on `spec` functions.",
                )?;
                reject_propositions(
                    &body.proof_cases,
                    "`proof` sections are only permitted on `spec` functions.",
                )?;
                FunctionBlockInner::Axiom
            }
        };

        // Naming rules are inherently enforced by the `Propositions` struct
        // itself during parsing. E.g., it ensures a maximum of one unnamed
        // bound, and handles parsing duplicated names.

        let mut all_names = std::collections::BTreeMap::new();
        let check_duplicates = |clauses: &Propositions<Local>,
                                kind: &'static str,
                                map: &mut std::collections::BTreeMap<String, &'static str>|
         -> Result<(), Error> {
            for clause in clauses.iter() {
                if let Some(name) = &clause.name
                    && let Some(prev_kind) = map.insert(name.content.clone(), kind)
                {
                    if prev_kind == kind {
                        return Err(Error::new(
                            name.raw_span.inner,
                            format!("Duplicate {} name `{}`.", kind, name.content),
                        ));
                    } else {
                        return Err(Error::new(
                            name.raw_span.inner,
                            format!(
                                "Bound name `{}` conflicts with an existing {} bound.",
                                name.content, prev_kind
                            ),
                        ));
                    }
                }
            }
            Ok(())
        };

        check_duplicates(&body.requires, "requires", &mut all_names)?;
        check_duplicates(&body.ensures, "ensures", &mut all_names)?;

        let mut proof_names = std::collections::BTreeMap::new();
        if let FunctionBlockInner::Proof { cases, .. } = &inner {
            check_duplicates(cases, "proof case", &mut proof_names)?;
        }

        Ok(Some(Self {
            common: HermesBlockCommon {
                context: body.context.lines,
                content_span: AstNode::new(item.content_span),
                start_span: AstNode::new(item.start_span),
            },
            requires: body.requires,
            ensures: body.ensures,
            inner,
        }))
    }
}

impl TypeHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute], source: &str) -> Result<Option<Self>, Error> {
        let Some((common, body)) = parse_item_block_common(attrs, "types", source)? else {
            return Ok(None);
        };

        reject_clauses(&body.is_safe, "`isSafe` sections are only permitted on traits.")?;

        if body.is_valid.is_empty() {
            return Err(Error::new(
                common.start_span.inner,
                "Hermes blocks on types must define an `isValid` type invariant. Did you misspell it?",
            ));
        }

        for clause in &body.is_valid {
            let first_line = clause.lines.first().map(|l| l.content.as_str()).unwrap_or("");
            if !first_line.contains(":=") {
                return Err(Error::new(
                    clause.keyword_span.inner,
                    "Type invariant `isValid` must be declared with an assignment operator (e.g., `isValid self := <Proposition>`).",
                ));
            }
        }

        Ok(Some(Self { common, is_valid: body.is_valid }))
    }
}

impl TraitHermesBlock<Local> {
    pub fn parse_from_attrs(
        attrs: &[Attribute],
        is_unsafe: bool,
        source: &str,
    ) -> Result<Option<Self>, Error> {
        let Some((common, body)) = parse_item_block_common(attrs, "traits", source)? else {
            return Ok(None);
        };

        reject_clauses(&body.is_valid, "`isValid` sections are only permitted on types.")?;

        if body.is_safe.is_empty() {
            return Err(Error::new(
                common.start_span.inner,
                "Hermes blocks on traits must define an `isSafe` trait invariant. Did you misspell it?",
            ));
        }

        if !is_unsafe {
            reject_clauses(
                &body.is_safe,
                "`isSafe` sections are only permitted on `unsafe` traits.",
            )?;
        }

        for clause in &body.is_safe {
            let first_line = clause.lines.first().map(|l| l.content.as_str()).unwrap_or("");
            if first_line.is_empty() {
                // Just keeping a dummy check if needed, or we can just remove the loop entirely.
            }
        }

        Ok(Some(Self { common, is_safe: body.is_safe }))
    }
}

impl ImplHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute], source: &str) -> Result<Option<Self>, Error> {
        let Some((common, body)) = parse_item_block_common(attrs, "impl items", source)? else {
            return Ok(None);
        };

        reject_clauses(&body.is_valid, "`isValid` sections are only permitted on types.")?;
        reject_clauses(&body.is_safe, "`isSafe` sections are only permitted on traits.")?;

        Ok(Some(Self { common }))
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

/// The structured content of a completely unvalidated Hermes specification block.
#[derive(Debug, Default, Clone)]
pub(super) struct RawHermesSpecBody {
    /// Content before any keyword (e.g., Lean imports, let bindings, type invariants)
    pub(super) context: RawSection,
    pub(super) requires: Propositions<Local>,
    pub(super) ensures: Propositions<Local>,
    pub(super) proof_context: RawSection,
    pub(super) proof_cases: Propositions<Local>,
    pub(super) is_valid: Vec<Clause<Local>>,
    pub(super) is_safe: Vec<Clause<Local>>,
}

#[derive(Debug, Clone)]
pub(super) enum ActiveClause {
    Unnamed,
    Named(String),
}

pub(super) struct ParsedHermesBody {
    pub(super) body: RawHermesSpecBody,
    pub(super) content_span: Span,
    pub(super) start_span: Span,
}

impl RawHermesSpecBody {
    // Helper to push a line to the current active destination
    fn add_line(
        &mut self,
        section: Section,
        active_clause: &Option<ActiveClause>,
        line: SpannedLine<Local>,
    ) {
        match section {
            Section::Init | Section::Context => self.context.lines.push(line),
            Section::ProofContext => self.proof_context.lines.push(line),
            Section::Requires => match active_clause {
                Some(ActiveClause::Unnamed) => {
                    if let Some(clause) = self.requires.unnamed.as_mut() {
                        clause.lines.push(line);
                    }
                }
                Some(ActiveClause::Named(name)) => {
                    if let Some(clause) = self.requires.named.get_mut(name) {
                        clause.lines.push(line);
                    }
                }
                None => {}
            },
            Section::Ensures => match active_clause {
                Some(ActiveClause::Unnamed) => {
                    if let Some(clause) = self.ensures.unnamed.as_mut() {
                        clause.lines.push(line);
                    }
                }
                Some(ActiveClause::Named(name)) => {
                    if let Some(clause) = self.ensures.named.get_mut(name) {
                        clause.lines.push(line);
                    }
                }
                None => {}
            },
            Section::ProofCase => match active_clause {
                Some(ActiveClause::Unnamed) => {
                    if let Some(clause) = self.proof_cases.unnamed.as_mut() {
                        clause.lines.push(line);
                    }
                }
                Some(ActiveClause::Named(name)) => {
                    if let Some(clause) = self.proof_cases.named.get_mut(name) {
                        clause.lines.push(line);
                    }
                }
                None => {}
            },
            Section::IsValid => {
                if let Some(clause) = self.is_valid.last_mut() {
                    clause.lines.push(line);
                }
            }
            Section::IsSafe => {
                if let Some(clause) = self.is_safe.last_mut() {
                    clause.lines.push(line);
                }
            }
        }
    }

    // Helper to start a new clause or section.
    //
    // This function initializes a new section or pushes a new clause to an
    // existing list of clauses (e.g., requires/ensures). It handles the
    // parsing of optional inline arguments.
    fn start_section(
        &mut self,
        section: Section,
        keyword_span: AstNode<Span, Local>,
        name: Option<SpannedLine<Local>>,
        arg: Option<SpannedLine<Local>>,
    ) -> Result<Option<ActiveClause>, String> {
        match section {
            Section::Init | Section::Context => {
                // explicit 'context' keyword?
                self.context.keyword_span = Some(keyword_span);
                if let Some(l) = arg {
                    self.context.lines.push(l);
                }
                Ok(None)
            }
            Section::ProofContext => {
                self.proof_context.keyword_span = Some(keyword_span);
                if let Some(l) = arg {
                    self.proof_context.lines.push(l);
                }
                Ok(None)
            }
            Section::Requires => {
                let lines = arg.into_iter().collect();
                let clause_name = name.clone();
                let clause = Clause { keyword_span, name, lines };
                self.requires.push(clause)?;
                Ok(Some(
                    clause_name.map_or(ActiveClause::Unnamed, |n| ActiveClause::Named(n.content)),
                ))
            }
            Section::Ensures => {
                let lines = arg.into_iter().collect();
                let clause_name = name.clone();
                let clause = Clause { keyword_span, name, lines };
                self.ensures.push(clause)?;
                Ok(Some(
                    clause_name.map_or(ActiveClause::Unnamed, |n| ActiveClause::Named(n.content)),
                ))
            }
            Section::ProofCase => {
                let lines = arg.into_iter().collect();
                let clause_name = name.clone();
                let clause = Clause { keyword_span, name, lines };
                self.proof_cases.push(clause)?;
                Ok(Some(
                    clause_name.map_or(ActiveClause::Unnamed, |n| ActiveClause::Named(n.content)),
                ))
            }
            Section::IsValid => {
                let lines = arg.into_iter().collect();
                self.is_valid.push(Clause { keyword_span, name, lines });
                Ok(None)
            }
            Section::IsSafe => {
                let lines = arg.into_iter().collect();
                self.is_safe.push(Clause { keyword_span, name, lines });
                Ok(None)
            }
        }
    }

    /// Parses a sequence of raw documentation lines into structured sections.
    ///
    /// This function implements the core state machine for parsing Hermes
    /// blocks. It iterates through lines, recognizing keywords (e.g.,
    /// `requires`, `ensures`) to switch sections, and collecting content lines
    /// into the current section.
    ///
    /// # Indentation Rules
    /// - Keywords must be at the same indentation level as the baseline
    ///   (the first keyword found).
    /// - Content lines must be indented *more* than the current section's
    ///   keyword.
    ///
    /// # Errors
    /// Returns a tuple `(SourceSpan, String)` on failure, pointing to the
    /// problematic line.
    fn parse<'a, I>(lines: I) -> Result<Self, (SourceSpan, String)>
    where
        I: IntoIterator<Item = &'a SpannedLine<Local>>,
    {
        // Matches exact keywords or keywords followed by any whitespace,
        // returning the trimmed remainder.
        fn strip_keyword<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
            let mut current = line;
            let mut first = true;
            for part in keyword.split_whitespace() {
                if !first {
                    // Must have consumed at least some whitespace between parts
                    let trimmed = current.trim_start();
                    if trimmed.len() == current.len() {
                        return None;
                    }
                    current = trimmed;
                } else {
                    current = current.trim_start();
                    first = false;
                }

                if current.starts_with(part) {
                    current = &current[part.len()..];
                } else {
                    return None;
                }
            }

            // To be a valid keyword match, it must be either the entire line,
            // or followed by a space, a colon, or a parenthesis (for named
            // bounds).
            if current.is_empty()
                || current.starts_with(char::is_whitespace)
                || current.starts_with('(')
                || current.starts_with(':')
            {
                Some(current)
            } else {
                None
            }
        }

        let keywords = [
            ("context", Section::Context),
            ("requires", Section::Requires),
            ("ensures", Section::Ensures),
            ("proof context", Section::ProofContext),
            ("proof", Section::ProofCase),
            ("isValid", Section::IsValid),
            ("isSafe", Section::IsSafe),
        ];

        lines
            .into_iter()
            .try_fold(
                (RawHermesSpecBody::default(), Section::Init, None::<usize>, None::<ActiveClause>),
                |(mut spec, current_section, baseline_indent, active_clause), line| {
                    let trimmed = line.content.trim();
                    let span = line.span;
                    let raw_span = line.raw_span.clone();

                    let item = SpannedLine {
                        content: line.content.clone(),
                        span,
                        raw_span: raw_span.clone(),
                    };

                    if trimmed.is_empty() {
                         // Pass empty lines to the current section/clause
                         // handler to preserve vertical spacing if needed, or
                         // ignore. For now, let's push them.
                         if current_section != Section::Init {
                              spec.add_line(current_section, &active_clause, item);
                         }
                        return Ok((spec, current_section, baseline_indent, active_clause));
                    }

                    let indent = line.content.len() - line.content.trim_start().len();

                    // Enforce the off-side rule for keyword detection.
                    //
                    // A keyword is only considered a section header if it is
                    // indented to the exact baseline of the current spec
                    // block. Otherwise, it is parsed as continuation text
                    // within the active section.
                    let is_keyword_candidate = baseline_indent.is_none_or(|base| indent == base);

                    if is_keyword_candidate
                        && let Some((&section, arg_str)) = keywords
                            .iter()
                            .find_map(|(k, s)| strip_keyword(trimmed, k).map(|arg| (s, arg)))
                    {
                        let section_is_clause = matches!(section, Section::Requires | Section::Ensures | Section::ProofCase);

                            let mut name: Option<SpannedLine<Local>> = None;
                            let mut remaining_arg = arg_str.trim_start();

                            if remaining_arg.starts_with('(')
                                && let Some(close_idx) = remaining_arg.find(')')
                            {
                                let name_str = remaining_arg[1..close_idx].trim();
                                    let after_name = remaining_arg[close_idx + 1..].trim_start();

                                    let mut apply_name = false;

                                    if section_is_clause {
                                        let keyword_name = keywords.iter().find(|(_, s)| *s == section).unwrap().0.trim_end_matches(':');
                                        apply_name = true;
                                        if let Some(remaining) = after_name.strip_prefix(':') {
                                            remaining_arg = remaining.trim_start();
                                        } else {
                                            return Err((span, format!("`{}` clauses with a name must be followed by a colon (e.g., `{} (name):`).", keyword_name, keyword_name)));
                                        }
                                    } else {
                                        // Not a clause, check if it looks like they tried to name it
                                        if after_name.starts_with(':') {
                                            let keyword_name = keywords.iter().find(|(_, s)| *s == section).unwrap().0;
                                            return Err((span, format!("`{}` sections cannot be named.", keyword_name)));
                                        }
                                    }

                                    if apply_name {
                                        if name_str.is_empty() {
                                            return Err((span, "Invalid bound name ``. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore).".to_string()));
                                        }
                                        let is_valid_ident = name_str.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
                                            && name_str.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_');

                                        // Block Lean keywords
                                        let lean_keywords = ["if", "then", "else", "match", "with", "do", "let", "mut", "for", "in", "by", "have", "show", "from", "syntax", "macro", "rules", "where", "theorem", "def", "abbrev", "lemma", "axiom", "inductive", "structure", "class", "instance", "variable", "universe", "namespace", "section", "end", "open", "export", "import", "set_option", "local", "scoped", "macro_rules", "notation", "prefix", "infix", "infixl", "infixr", "postfix", "deriving", "noncomputable", "partial", "protected", "private", "public", "mutual", "unsafe", "mutual"];
                                        let is_lean_keyword = lean_keywords.contains(&name_str);

                                        if !is_valid_ident {
                                            return Err((span, format!("Invalid bound name `{name_str}`. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore).")));
                                        } else if is_lean_keyword {
                                            return Err((span, format!("Invalid bound name `{}`. Names cannot be Lean keywords.", name_str)));
                                        }
                                        name = Some(SpannedLine {
                                            content: name_str.to_string(),
                                            span,
                                            raw_span: raw_span.clone(),
                                        });
                                    }
                                }

                            // Lean 4 definitions for `isValid` and `isSafe`
                            // require the keyword to literally appear in the
                            // generated syntax. We flag these sections here
                            // to ensure the keyword itself is preserved as
                            // part of the parsed content.
                            let keep_keyword = matches!(section, Section::IsValid | Section::IsSafe);

                            if name.is_none() {
                                let rest = remaining_arg.trim_start();
                                if !keep_keyword {
                                    if let Some(remaining) = rest.strip_prefix(':') {
                                        remaining_arg = remaining.trim_start();
                                    } else {
                                        let keyword_name = keywords.iter().find(|(_, s)| *s == section).unwrap().0.trim_end_matches(':');
                                        return Err((span, format!("Hermes keyword `{}` must be followed by a colon (e.g., `{}:`).", keyword_name, keyword_name)));
                                    }
                                }
                            }
                            let first_line_content = if keep_keyword {
                                trimmed.to_string()
                            } else {
                                remaining_arg.to_string()
                            };

                            let arg = if !first_line_content.trim().is_empty() {
                                Some(SpannedLine {
                                    content: first_line_content,
                                    span,
                                    raw_span: raw_span.clone(),
                                })
                            } else {
                                if keep_keyword {
                                    Some(SpannedLine {
                                        content: first_line_content,
                                        span,
                                        raw_span: raw_span.clone(),
                                    })
                                } else {
                                    None
                                }
                            };

                            let next_active = spec.start_section(section, raw_span, name, arg)
                                .map_err(|msg| (span, msg))?;
                            let new_baseline = baseline_indent.unwrap_or(indent);
                            return Ok((spec, section, Some(new_baseline), next_active));
                        }

                    if current_section == Section::Init {
                         return Err((
                            span,
                            "Expected a Hermes keyword to start the block (e.g. `context`, `requires`, ...).".to_string(),
                        ));
                    }

                    if current_section != Section::Context && indent <= baseline_indent.unwrap() {
                        return Err((
                            span,
                            "Invalid indentation: expected an indented continuation or a valid \
                             Hermes keyword (context, requires, ensures, proof, isValid, isSafe). \
                             Did you misspell a keyword?"
                                .to_string(),
                        ));
                    }
                    // Not a new keyword; continuation of the current section.
                    spec.add_line(current_section, &active_clause, item);

                    Ok((spec, current_section, baseline_indent, active_clause))
                },
            )
            .map(|(spec, _, _, _)| spec)
    }
}

impl<M: ThreadSafety> LiftToSafe for SpannedLine<M> {
    type Target = SpannedLine<Safe>;
    fn lift(self) -> Self::Target {
        SpannedLine { content: self.content, span: self.span, raw_span: self.raw_span.lift() }
    }
}

impl<M: ThreadSafety> LiftToSafe for Clause<M> {
    type Target = Clause<Safe>;
    fn lift(self) -> Self::Target {
        Clause {
            keyword_span: self.keyword_span.lift(),
            name: self.name.map(|n| n.lift()),
            lines: self.lines.into_iter().map(|l| l.lift()).collect(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for Propositions<M> {
    type Target = Propositions<Safe>;
    fn lift(self) -> Self::Target {
        Propositions {
            unnamed: self.unnamed.map(|c| c.lift()),
            named: self.named.into_iter().map(|(k, v)| (k, v.lift())).collect(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for HermesBlockCommon<M> {
    type Target = HermesBlockCommon<Safe>;
    fn lift(self) -> Self::Target {
        HermesBlockCommon {
            context: self.context.into_iter().map(|l| l.lift()).collect(),
            content_span: self.content_span.lift(),
            start_span: self.start_span.lift(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionBlockInner<M> {
    type Target = FunctionBlockInner<Safe>;
    fn lift(self) -> Self::Target {
        match self {
            Self::Proof { context, cases } => FunctionBlockInner::Proof {
                context: context.into_iter().map(|l| l.lift()).collect(),
                cases: cases.lift(),
            },
            Self::Axiom => FunctionBlockInner::Axiom,
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionHermesBlock<M> {
    type Target = FunctionHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        FunctionHermesBlock {
            common: self.common.lift(),
            requires: self.requires.lift(),
            ensures: self.ensures.lift(),
            inner: self.inner.lift(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TypeHermesBlock<M> {
    type Target = TypeHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        TypeHermesBlock {
            common: self.common.lift(),
            is_valid: self.is_valid.into_iter().map(|c| c.lift()).collect(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TraitHermesBlock<M> {
    type Target = TraitHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        TraitHermesBlock {
            common: self.common.lift(),
            is_safe: self.is_safe.into_iter().map(|c| c.lift()).collect(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for ImplHermesBlock<M> {
    type Target = ImplHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        ImplHermesBlock { common: self.common.lift() }
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
    fn test_parse_hermes_info_string() {
        // Not hermes
        assert_eq!(parse_hermes_info_string(""), Ok(None));
        assert_eq!(parse_hermes_info_string("rust"), Ok(None));
        assert_eq!(parse_hermes_info_string("lean"), Ok(None));

        // Just hermes
        assert_eq!(
            parse_hermes_info_string("lean, hermes"),
            Ok(Some(ParsedInfoString::GenericMode))
        );
        assert_eq!(parse_hermes_info_string(" hermes "), Ok(Some(ParsedInfoString::GenericMode)));
        assert_eq!(
            parse_hermes_info_string("lean , hermes "),
            Ok(Some(ParsedInfoString::GenericMode))
        );

        // Valid attributes
        assert!(matches!(
            parse_hermes_info_string("hermes, spec"),
            Ok(Some(ParsedInfoString::FunctionMode(FunctionAttribute::Spec)))
        ));
        assert!(matches!(
            parse_hermes_info_string("lean,hermes,unsafe(axiom)"),
            Ok(Some(ParsedInfoString::FunctionMode(FunctionAttribute::UnsafeAxiom)))
        ));

        // Invalid attributes
        assert!(parse_hermes_info_string("hermes, unknown").is_err());
        assert!(parse_hermes_info_string("hermes, unsafe").is_err());
        assert!(parse_hermes_info_string("hermes, spec, other").is_err());
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
            parse_quote!(#[doc = " ```lean, hermes, spec"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap().unwrap();
        match block {
            FunctionHermesBlock {
                common: HermesBlockCommon { context, .. },
                inner: FunctionBlockInner::Proof { .. },
                ..
            } => {
                assert_eq!(context[0].content, " body 1");
                assert_eq!(context[1].content, " body 2");
            }
            _ => panic!("Expected block with Proof inner"),
        }
    }

    #[test]
    fn test_parse_from_attrs_valid_axiom() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```lean, hermes, unsafe(axiom)"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
        match block {
            FunctionHermesBlock {
                common: HermesBlockCommon { context, .. },
                inner: FunctionBlockInner::Axiom,
                ..
            } => {
                assert_eq!(context[0].content, " body 1");
                assert_eq!(context[1].content, " body 2");
            }
            _ => panic!("Expected block with Axiom inner"),
        }
    }

    #[test]
    fn test_parse_from_attrs_unclosed() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```hermes"]), parse_quote!(#[doc = " no end fence"])];
        let err = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "Unclosed Hermes block in documentation.");
    }

    #[test]
    fn test_parse_from_attrs_interrupted() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " line 1"]),
            parse_quote!(#[derive(Clone)]), // Interrupts contiguous doc lines
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap().unwrap();
        assert_eq!(block.common.context.len(), 1);
        assert_eq!(block.common.context[0].content, " line 1");
    }

    #[test]
    fn test_parse_from_attrs_multiple_blocks() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " ```"]),
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "Multiple Hermes blocks found on a single item.");
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
    fn test_hermes_spec_body_parse_empty() {
        let lines = mk_lines(&[]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(!spec.context.is_present());
        assert!(spec.requires.is_empty());
        assert!(spec.ensures.is_empty());
        assert!(spec.proof_cases.is_empty() && spec.proof_context.lines.is_empty());
    }

    #[test]
    fn test_hermes_spec_body_parse_context_only() {
        let lines = mk_lines(&["context:", "import Foo", "def bar := 1"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(spec.context.is_present());
        assert_eq!(spec.context.lines.len(), 2);
        assert_eq!(spec.context.lines[0].content, "import Foo");
    }

    #[test]
    fn test_hermes_spec_body_parse_requires() {
        let lines = mk_lines(&["requires:", "  x > 0", "  y > 0"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        let clause = &spec.requires[0];
        assert_eq!(clause.lines.len(), 2);
        assert_eq!(clause.lines[0].content, "  x > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_clauses() {
        let lines = mk_lines(&["requires:", "  x > 0", "requires (foo):", "  y > 0"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
        assert_eq!(spec.requires[1].lines[0].content, "  y > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_sections() {
        let lines = mk_lines(&["requires:", "  x > 0", "ensures:", "  result = x"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
        assert_eq!(spec.ensures[0].lines[0].content, "  result = x");
    }

    #[test]
    fn test_hermes_spec_body_parse_interleaved_sections() {
        let lines = mk_lines(&[
            "requires:",
            "  x > 0",
            "ensures:",
            "  result = x",
            "requires (req_y):",
            "  y > 0",
            "ensures (ens_res):",
            "  result > 0",
        ]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.ensures.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
        assert_eq!(spec.ensures[0].lines[0].content, "  result = x");
        assert_eq!(spec.requires[1].lines[0].content, "  y > 0");
        assert_eq!(spec.ensures[1].lines[0].content, "  result > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_inline_arg() {
        let lines = mk_lines(&["requires: x > 0", "  y > 0"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].lines.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, "x > 0");
        assert_eq!(spec.requires[0].lines[1].content, "  y > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_invalid_indent() {
        let lines = mk_lines(&["requires:", "x > 0", "y > 0"]); // "y > 0" has same indent/no indent as requires?
        // mk_lines creates lines with 0 indent unless spaces are in string? Use specific strings.
        // Actually mk_lines takes &str, so if I pass "requires", it has 0 indent.
        // "x > 0" has 0 indent. This should fail if `parse` logic checks indent <= baseline.
        // Baseline is 0. 0 <= 0 is true.
        // "Invalid indentation: expected an indented continuation..."
        // Because for continuation, we usually expect INDENT > BASELINE.
        // The code says: `indent <= baseline_indent.unwrap()` error.
        // So yes, 0 <= 0 error.
        let spec = RawHermesSpecBody::parse(&lines);
        assert!(spec.is_err());
    }

    #[test]
    fn test_hermes_spec_body_parse_implicit_context_fails() {
        let lines = mk_lines(&["import Foo"]);
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(
            err.1.contains("Expected a Hermes keyword")
                || err.1.contains("must be followed by a colon")
        );
    }

    #[test]
    fn test_hermes_spec_body_parse_strict_keywords() {
        let lines = mk_lines(&[
            "context:",
            "requires_foo a",
            "ensuresbar",
            "proof_of_concept",
            "axiomatic",
            "  requires   ", // valid keyword
            "   genuine requirements ",
        ]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        // The first four are context lines because they don't match keywords strictly.
        assert_eq!(spec.context.lines.len(), 6);
        assert_eq!(spec.context.lines[0].content, "requires_foo a");
        assert_eq!(spec.context.lines[1].content, "ensuresbar");
        assert_eq!(spec.context.lines[2].content, "proof_of_concept");
        assert_eq!(spec.context.lines[3].content, "axiomatic");

        // The line "  requires   " does not match the baseline indent (which is
        // 0), so it is parsed as continuation text within the context section.
        assert_eq!(spec.context.lines[4].content, "  requires   ");
        assert_eq!(spec.context.lines[5].content, "   genuine requirements ");

        assert!(spec.requires.is_empty());
        assert!(spec.ensures.is_empty());
    }

    #[test]
    fn test_hermes_spec_body_parse_arguments_vs_continuation() {
        let lines = mk_lines(&[
            "requires: a > 0",
            "  and b < 0", // Continuation: keeps original whitespace
            "ensures: c == 1",
            "proof:", // standalone keyword
            "  trivial",
        ]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(!spec.context.is_present());

        assert_eq!(spec.requires.len(), 1);
        // Prefix argument keeps its exact text post-"requires" (which is now trimmed).
        assert_eq!(spec.requires[0].lines[0].content, "a > 0");
        // Continuation line keeps full exact original text.
        assert_eq!(spec.requires[0].lines[1].content, "  and b < 0");

        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, "c == 1");

        assert_eq!(spec.proof_cases.len(), 1);
        assert_eq!(spec.proof_cases[0].lines.len(), 1);
        assert_eq!(spec.proof_cases[0].lines[0].content, "  trivial");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_same_section() {
        // Check that it can interleave sections or repeat them
        let lines = mk_lines(&["requires: a", "ensures: b", "requires (foo): c"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, "a");
        assert_eq!(spec.requires[1].lines[0].content, "c");

        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, "b");
    }

    fn dummy_line(content: &str) -> SpannedLine {
        SpannedLine {
            content: content.to_string(),
            span: (0, 0).into(),
            raw_span: AstNode::new(Span::call_site()),
        }
    }

    #[test]
    fn test_parse_spec_valid_indentation() {
        let lines =
            mk_lines(&["context:", "context_line", "requires:", "  req1", "ensures:", "  ens1"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.context.lines[0].content, "context_line");
        assert_eq!(spec.requires[0].lines[0].content, "  req1");
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, "  ens1");
    }

    #[test]
    fn test_parse_spec_inline_args_valid() {
        let lines = vec![
            dummy_line("requires: a > 0"),
            dummy_line("ensures:\tb > 0"), // Tests tab whitespace
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].lines[0].content, "a > 0");
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, "b > 0");
    }

    #[test]
    fn test_parse_spec_blank_lines() {
        let lines = vec![
            dummy_line("requires:"),
            dummy_line("  a > 0"),
            dummy_line(""),
            dummy_line("  b > 0"),
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires[0].lines.len(), 3); // 2 content lines + 1 blank line
    }

    #[test]
    fn test_parse_spec_header_no_indent_rules() {
        let lines = mk_lines(&["context:", "context_line", "  indented context", "more context"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.context.lines.len(), 3);
    }

    #[test]
    fn test_parse_spec_err_typo_keyword() {
        let lines = vec![
            dummy_line("requires:"),
            dummy_line("  a > 0"),
            dummy_line("ensure"), // Typo, missing 's'. Indentation is 0.
            dummy_line("  b > 0"),
        ];
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(
            err.1.contains("Invalid indentation") || err.1.contains("must be followed by a colon")
        );
    }

    #[test]
    fn test_parse_spec_err_missing_colon_named_bound() {
        let lines = vec![dummy_line("requires (h_req)"), dummy_line("  a > 0")];
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(err.1.contains("must be followed by a colon"));
    }

    #[test]
    fn test_parse_spec_valid_apostrophe_name() {
        let lines = vec![dummy_line("requires (h_x'_is_valid):"), dummy_line("  true")];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "h_x'_is_valid");
    }

    #[test]
    fn test_parse_spec_err_under_indented_continuation() {
        let lines = mk_lines(&[
            "context:",
            "header",
            "requires:",
            "  req1",
            "req2_oops", // This looks like a new keyword but isn't one, and isn't indented
        ]);
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(
            err.1.contains("Invalid indentation") || err.1.contains("must be followed by a colon")
        );
    }

    #[test]
    fn test_parse_from_attrs_not_hermes() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```lean"]), parse_quote!(#[doc = " ```"])];
        let block_func = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap();
        assert!(block_func.is_none());
        let block_item = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap();
        assert!(block_item.is_none());
    }

    #[test]
    fn test_type_block_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " context:"]), // Types shouldn't really have context/header usually, but parser allows it?
            // Actually TypeHermesBlock only takes `is_valid`.
            // Let's check `parse_from_attrs` implementation for TypeHermesBlock.
            // It calls `parse_item_block_common`.
            // `parse_item_block_common` allows header in `HermesBlockCommon`.
            // But `TypeHermesBlock` struct doesn't have `context` field? It has `common: HermesBlockCommon`.
            // `HermesBlockCommon` has `header`.
            // So yes, types can have context.
            parse_quote!(#[doc = " foo"]),
            parse_quote!(#[doc = " isValid self :="]),
            parse_quote!(#[doc = "  bar"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
        assert_eq!(block.is_valid[0].lines[0].content, "isValid self :=");
        assert_eq!(block.is_valid[0].lines[1].content, "  bar");
        assert_eq!(block.common.context[0].content, " foo");
    }

    #[test]
    fn test_type_block_missing_is_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " context:"]),
            parse_quote!(#[doc = " foo"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
        assert_eq!(
            err.to_string(),
            "Hermes blocks on types must define an `isValid` type invariant. Did you misspell it?"
        );
    }

    #[test]
    fn test_trait_block_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
        assert_eq!(block.is_safe.len(), 1);
        assert_eq!(block.is_safe[0].lines[0].content, "isSafe");
        assert_eq!(block.is_safe[0].lines[1].content, "  val == true");
    }

    #[test]
    fn test_trait_block_missing_is_safe() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```hermes"]), parse_quote!(#[doc = " ```"])];
        let err = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap_err();
        assert_eq!(
            err.to_string(),
            "Hermes blocks on traits must define an `isSafe` trait invariant. Did you misspell it?"
        );
    }

    #[test]
    fn test_function_rejects_invariants() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes, spec"]),
            parse_quote!(#[doc = " isValid"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "`isValid` sections are only permitted on types.");
    }

    #[test]
    fn test_type_rejects_function_clauses() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " requires:"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " isValid"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
        assert_eq!(err.to_string(), "`requires` sections are only permitted on functions.");
    }

    #[test]
    fn test_type_rejects_is_safe() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isValid self :="]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " isSafe"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
        assert_eq!(err.to_string(), "`isSafe` sections are only permitted on traits.");
    }
    #[test]
    fn test_empty_section_is_present() {
        let lines = mk_lines(&["requires:", "  x > 0", "ensures:"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(!spec.requires.is_empty());
        assert!(!spec.ensures.is_empty());
        assert!(spec.ensures[0].lines.is_empty());
    }

    #[test]
    fn test_trait_rejects_is_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe my_trait :"]),
            parse_quote!(#[doc = " isValid foo :="]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap_err();
        assert_eq!(err.to_string(), "`isValid` sections are only permitted on types.");
    }

    #[test]
    fn test_is_valid_newline_after_keyword() {
        // Here, the keyword `isValid` is followed by a newline, but we include
        // `:=` to bypass validation. It should still preserve the keyword in
        // the generated parsed body.
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isValid :="]),
            parse_quote!(#[doc = "  self.val > 0"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
        // Since `isValid` has no inline arguments beyond `:=`, the first line is exactly "isValid :=".
        assert_eq!(block.is_valid[0].lines[0].content, "isValid :=");
        assert_eq!(block.is_valid[0].lines[1].content, "  self.val > 0");
    }

    #[test]
    fn test_is_safe_extra_whitespace() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe     self    :="]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
        // keep_keyword should preserve the exact string from the comment line
        assert_eq!(block.is_safe[0].lines[0].content, "isSafe     self    :=");
    }

    #[test]
    fn test_reject_section_points_to_keyword() {
        // Create dummy lines manually so we can distinguish raw_span
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];

        let requires_attr: syn::Attribute = parse_quote!(#[doc = " requires:"]);
        let cont_attr: syn::Attribute = parse_quote!(#[doc = "  x > 0"]);

        attrs.push(requires_attr.clone());
        attrs.push(cont_attr);
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();

        let lines = extract_doc_line(&requires_attr, "");
        assert_eq!(lines.len(), 1);
        let (_, _, requires_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", requires_raw_span));
    }

    #[test]
    fn test_parse_requires_on_safe_fn_errors() {
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];
        let requires_attr: syn::Attribute = parse_quote!(#[doc = " requires: true"]);
        attrs.push(requires_attr.clone());
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(
            err.to_string(),
            "`requires` sections are only permitted on `unsafe` functions."
        );
        let lines = extract_doc_line(&requires_attr, "");
        let (_, _, requires_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", requires_raw_span));
    }

    #[test]
    fn test_parse_requires_on_unsafe_fn_succeeds() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " requires: true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
        assert!(!block.requires.is_empty());
    }

    #[test]
    fn test_parse_ensures_only_on_safe_fn_succeeds() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " ensures: result > 0"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap().unwrap();
        assert!(block.requires.is_empty());
        assert!(!block.ensures.is_empty());
    }

    #[test]
    fn test_parse_multiple_requires_on_safe_fn_errors() {
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];
        let first_requires: syn::Attribute = parse_quote!(#[doc = " requires: x > 0"]);
        let second_requires: syn::Attribute = parse_quote!(#[doc = " requires (foo): y > 0"]);

        attrs.push(first_requires.clone());
        attrs.push(second_requires);
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(
            err.to_string(),
            "`requires` sections are only permitted on `unsafe` functions."
        );

        let lines = extract_doc_line(&first_requires, "");
        let (_, _, requires_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", requires_raw_span));
    }

    #[test]
    fn test_parse_empty_requires_on_safe_fn_errors() {
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];
        let requires_attr: syn::Attribute = parse_quote!(#[doc = " requires:"]);
        attrs.push(requires_attr.clone());
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(
            err.to_string(),
            "`requires` sections are only permitted on `unsafe` functions."
        );
        let lines = extract_doc_line(&requires_attr, "");
        let (_, _, requires_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", requires_raw_span));
    }

    #[test]
    fn test_parse_is_safe_on_safe_trait_errors() {
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];
        let is_safe_attr: syn::Attribute = parse_quote!(#[doc = " isSafe true"]);
        attrs.push(is_safe_attr.clone());
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = TraitHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "`isSafe` sections are only permitted on `unsafe` traits.");
        let lines = extract_doc_line(&is_safe_attr, "");
        let (_, _, is_safe_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", is_safe_raw_span));
    }

    #[test]
    fn test_parse_is_safe_on_unsafe_trait_succeeds() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
        assert!(!block.is_safe.is_empty());
    }

    #[test]
    fn test_parse_multiple_is_safe_on_safe_trait_errors() {
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];
        let first_is_safe: syn::Attribute = parse_quote!(#[doc = " isSafe x > 0"]);
        let second_is_safe: syn::Attribute = parse_quote!(#[doc = " isSafe y > 0"]);

        attrs.push(first_is_safe.clone());
        attrs.push(second_is_safe);
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = TraitHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "`isSafe` sections are only permitted on `unsafe` traits.");

        let lines = extract_doc_line(&first_is_safe, "");
        let (_, _, is_safe_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", is_safe_raw_span));
    }

    #[test]
    fn test_parse_empty_is_safe_on_safe_trait_errors() {
        // Here we test just the keyword without content. Notice that `TraitHermesBlock`
        // also checks for a colon (`:`). However, the `is_unsafe` check comes first!
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];
        let is_safe_attr: syn::Attribute = parse_quote!(#[doc = " isSafe"]);
        attrs.push(is_safe_attr.clone());
        attrs.push(parse_quote!(#[doc = " ```"]));

        let err = TraitHermesBlock::parse_from_attrs(&attrs, false, "").unwrap_err();
        assert_eq!(err.to_string(), "`isSafe` sections are only permitted on `unsafe` traits.");
        let lines = extract_doc_line(&is_safe_attr, "");
        let (_, _, is_safe_raw_span) = lines[0];
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", is_safe_raw_span));
    }

    mod edge_cases {
        use super::*;

        #[test]
        fn test_keyword_prefix_safety() {
            // Verify that 'proof_helper' is parsed as content, not a 'proof' section.
            let lines = mk_lines(&[
                "requires:",
                "  proof_helper", // Should be content of requires
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(!spec.requires.is_empty());
            assert_eq!(spec.requires[0].lines.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  proof_helper");
            assert!(spec.proof_cases.is_empty() && spec.proof_context.lines.is_empty());
        }

        #[test]
        fn test_keyword_collision_error() {
            // Verify that keywords inside a section are treated as continuation
            // text if their indentation differs from the baseline.
            let lines = mk_lines(&[
                "requires:",
                "  proof", // Indented 'proof' - parser must treat as continuation content
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(!spec.requires.is_empty());
            assert_eq!(spec.requires[0].lines.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  proof"); // 'proof' is now a continuation
            assert!(spec.proof_cases.is_empty() && spec.proof_context.lines.is_empty());
        }

        #[test]
        fn test_multiple_sections_concatenation() {
            let lines = mk_lines(&["requires: a", "requires (foo): b"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 2);
            assert_eq!(spec.requires[0].lines[0].content, "a");
            assert_eq!(spec.requires[1].lines[0].content, "b");
        }

        #[test]
        fn test_typo_safety() {
            let lines = mk_lines(&[
                "requires:",
                "  is_safe", // Typo for isSafe, should be content
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires[0].lines[0].content, "  is_safe");
        }

        #[test]
        fn test_trait_rejects_function_keywords() {
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ```hermes"]),
                parse_quote!(#[doc = " isSafe"]),
                parse_quote!(#[doc = "  val"]),
                parse_quote!(#[doc = " requires: true"]), // Should error
                parse_quote!(#[doc = " ```"]),
            ];
            let err = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap_err();
            assert_eq!(err.to_string(), "`requires` sections are only permitted on functions.");
        }

        #[test]
        fn test_nested_fences_failure() {
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ```hermes"]),
                parse_quote!(#[doc = " isSafe"]),
                parse_quote!(#[doc = " ```"]), // Nested fence? No this is just premature close.
                parse_quote!(#[doc = "  nested"]),
                parse_quote!(#[doc = " ```"]),
            ];
            // The parser sees the first ``` and stops.
            // The "nested" part matches nothing and is ignored by parse_from_attrs loop?
            // Actually `parse_from_attrs` iterates until it finds the block.
            // It parses until `is_end_fence`.
            // So if we have ` ``` ` inside, it closes the block.
            // Then `nested` is outside.
            // The result is valid block with just `isSafe`.
            // But if the INTENTION was nested, it fails silently or just closes early.
            // Let's verify it closes early.
            let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
            assert!(block.is_safe.len() == 1);
            assert!(!block.is_safe[0].lines.is_empty());
            assert_eq!(block.is_safe[0].lines[0].content, "isSafe");
        }

        #[test]
        fn test_nested_code_blocks() {
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ````hermes"]),
                parse_quote!(#[doc = " requires: true"]),
                parse_quote!(#[doc = "  ```rust"]),
                parse_quote!(#[doc = "  let x = 1;"]),
                parse_quote!(#[doc = "  ```"]),
                parse_quote!(#[doc = " ensures: true"]),
                parse_quote!(#[doc = " ````"]),
            ];
            // This test will fail currently because the parser stops at the first ` ``` `
            // instead of matching the length of the opening fence (````).
            let block = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();

            assert_eq!(block.requires.len(), 1);
            // The parser should ideally skip the inner ```rust block and parse the ensures clause.
            assert_eq!(block.ensures.len(), 1);
        }

        #[test]
        fn test_nested_code_blocks_in_comments() {
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ```hermes"]),
                parse_quote!(#[doc = " context:"]),
                parse_quote!(#[doc = "   -- ```"]),
                parse_quote!(#[doc = "   -- Some code"]),
                parse_quote!(#[doc = "   -- ```"]),
                parse_quote!(#[doc = " ensures: true"]),
                parse_quote!(#[doc = " ```"]),
            ];

            let block = FunctionHermesBlock::parse_from_attrs(&attrs, false, "").unwrap().unwrap();

            assert_eq!(block.common.context.len(), 3);
            assert_eq!(block.ensures.len(), 1);
        }

        #[test]
        fn test_mixed_tabs_spaces_indentation() {
            // Indentation logic uses `len() - trim_start().len()`.
            // '\t' is 1 char. ' ' is 1 char.
            let lines = mk_lines(&[
                "requires:",
                "\t\ta > 0", // 2 chars indent
                "  b > 0",   // 2 chars indent
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires[0].lines.len(), 2);
            assert_eq!(spec.requires[0].lines[0].content, "\t\ta > 0");
            assert_eq!(spec.requires[0].lines[1].content, "  b > 0");
        }

        #[test]
        fn test_missing_definition_syntax() {
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ```hermes"]),
                parse_quote!(#[doc = " isSafe"]), // Missing body
                parse_quote!(#[doc = " ```"]),
            ];
            // Should succeed with empty body or fail?
            // Currently parser allows empty sections.
            let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
            assert!(block.is_safe.len() == 1);
            assert_eq!(block.is_safe[0].lines[0].content, "isSafe");
        }

        #[test]
        fn test_complex_lean_expressions() {
            // Verify parsing of multiline, commented, and unicode Lean content.
            // The parser doesn't validate Lean lexical rules, just extracts lines.
            // But we want to ensure it doesn't choke on tokens.
            let _lines = mk_lines(&[
                "isSafe Self :=",
                "  -- This is a comment",
                "  x ≥ 0 ∧ y ≤ 10",  // Unicode
                "  let result := 1", // 'result' keyword in Lean
            ]);
            // For Trait, we look for isSafe.
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ```hermes"]),
                parse_quote!(#[doc = " isSafe Self :="]),
                parse_quote!(#[doc = "  -- This is a comment"]),
                parse_quote!(#[doc = "  x ≥ 0 ∧ y ≤ 10"]),
                parse_quote!(#[doc = "  let result := 1"]),
                parse_quote!(#[doc = " ```"]),
            ];
            let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
            // isSafe Self := (1)
            // -- This is a comment (2)
            // x ≥ 0 ∧ y ≤ 10 (3)
            // let result := 1 (4)
            // Total 4 lines.
            assert_eq!(block.is_safe.len(), 1);
            assert_eq!(block.is_safe[0].lines.len(), 4);
            assert_eq!(block.is_safe[0].lines[2].content, "  x ≥ 0 ∧ y ≤ 10");
        }

        #[test]
        fn test_argument_name_collisions() {
            // Verify that arguments named 'result', 'old_x' are parsed as content and don't trigger keywords.
            // 'result' is not a keyword in Hermes parser, only a binder in generation.
            let lines = mk_lines(&["requires:", "  result > 0", "  old_x < new_x"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires[0].lines.len(), 2);
            assert_eq!(spec.requires[0].lines[0].content, "  result > 0");
            assert_eq!(spec.requires[0].lines[1].content, "  old_x < new_x");
        }

        #[test]
        fn test_interleaved_attributes() {
            // Verify that non-doc attributes are skipped and doc attributes are concatenated.
            let attrs: Vec<syn::Attribute> = vec![
                parse_quote!(#[doc = " ```hermes"]),
                parse_quote!(#[allow(dead_code)]), // Interleaved attribute
                parse_quote!(#[doc = " isSafe"]),
                parse_quote!(#[cfg(all())]), // Another Interleaved
                parse_quote!(#[doc = "  val"]),
                parse_quote!(#[doc = " ```"]),
            ];
            let block = TraitHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
            assert_eq!(block.is_safe.len(), 1);
            assert_eq!(block.is_safe[0].lines[0].content, "isSafe");
            assert_eq!(block.is_safe[0].lines[1].content, "  val");
        }

        #[test]
        fn test_comment_before_keyword_fails() {
            let lines = mk_lines(&["// comment", "context"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(
                err.1.contains("Expected a Hermes keyword")
                    || err.1.contains("must be followed by a colon")
            );
        }

        #[test]
        fn test_context_inline_args() {
            let lines = mk_lines(&["context: inline_context", "more_context"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.context.lines[0].content, "inline_context");
            assert_eq!(spec.context.lines[1].content, "more_context");
        }

        #[test]
        fn test_multiple_context_sections() {
            let lines = mk_lines(&["context: part1", "context: part2"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.context.lines.len(), 2);
            assert_eq!(spec.context.lines[0].content, "part1");
            assert_eq!(spec.context.lines[1].content, "part2");
        }

        #[test]
        fn test_delayed_context() {
            let lines = mk_lines(&["requires: x > 0", "context:", "added_to_context"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(!spec.requires.is_empty());
            assert_eq!(spec.context.lines.len(), 1);
            assert_eq!(spec.context.lines[0].content, "added_to_context");
        }

        #[test]
        fn test_case_sensitive_context() {
            let lines = mk_lines(&["Context"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(
                err.1.contains("Expected a Hermes keyword")
                    || err.1.contains("must be followed by a colon")
            );
        }

        #[test]
        fn test_leading_whitespace_ignored() {
            let lines = mk_lines(&["   ", "", "context:", "stuff"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.context.lines[0].content, "stuff");
        }

        #[test]
        fn test_edge_indentation_drift() {
            // Verify that keywords at drifting indentation levels compared to
            // the baseline are treated as continuation lines.
            let lines = mk_lines(&[
                "requires:",
                "  x > 0",
                "  ensures:", // Indented keyword -> Continuation line
                "    y > 0",  // Indented content -> Continuation line
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].lines.len(), 3);
            assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
            assert_eq!(spec.requires[0].lines[1].content, "  ensures:");
            assert_eq!(spec.requires[0].lines[2].content, "    y > 0");

            assert!(spec.ensures.is_empty());
        }

        #[test]
        fn test_edge_keywords_as_content_wrapped() {
            let lines = mk_lines(&[
                "requires:",
                "  (requires x)", // Safe
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  (requires x)");
        }

        #[test]
        fn test_edge_empty_clauses() {
            let lines = mk_lines(&["requires:", "ensures:"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert!(spec.requires[0].lines.is_empty());
            assert_eq!(spec.ensures.len(), 1);
            assert!(spec.ensures[0].lines.is_empty());
        }

        #[test]
        fn test_edge_unicode_indentation() {
            // \u{2003} is em-space.
            // Rust string trim handles unicode whitespace.
            let lines = mk_lines(&["requires:", "\u{2003}x > 0"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            // Indentation calculation:
            // "\u{2003}x > 0".len() (unicode text len in bytes) - "x > 0".len()
            // em-space is 3 bytes usually.
            // So indent is 3. 3 > 0. Should be valid.
            assert_eq!(spec.requires[0].lines[0].content, "\u{2003}x > 0");
        }

        #[test]
        fn test_edge_crlf_lines() {
            use proc_macro2::Span;
            // Let's make lines with \r manually.
            let lines = vec![
                SpannedLine {
                    content: "requires:\r".to_string(),
                    span: (0, 0).into(),
                    raw_span: AstNode::new(Span::call_site()),
                },
                SpannedLine {
                    content: "  x > 0\r".to_string(),
                    span: (0, 0).into(),
                    raw_span: AstNode::new(Span::call_site()),
                },
            ];
            // Parser calls `line.content.trim()`.
            // "requires\r".trim() -> "requires". Matches keyword.
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  x > 0\r");
        }

        #[test]
        fn test_edge_proof_context_vs_cases() {
            let lines = mk_lines(&[
                "proof context:",
                "  let helper = 1",
                "proof:", // unnamed
                "  simp_all",
                "proof (named_case) :", // named
                "  trivial",
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();

            // Context lines
            assert_eq!(spec.proof_context.lines.len(), 1);
            assert_eq!(spec.proof_context.lines[0].content, "  let helper = 1");

            // Proof cases
            assert_eq!(spec.proof_cases.len(), 2);

            // unnamed
            assert!(spec.proof_cases[0].name.is_none());
            assert_eq!(spec.proof_cases[0].lines.len(), 1);
            assert_eq!(spec.proof_cases[0].lines[0].content, "  simp_all");

            // named
            assert_eq!(spec.proof_cases[1].name.as_ref().unwrap().content, "named_case");
            assert_eq!(spec.proof_cases[1].lines.len(), 1);
            assert_eq!(spec.proof_cases[1].lines[0].content, "  trivial");
        }

        #[test]
        fn test_edge_named_requires_ensures() {
            let lines = mk_lines(&[
                "requires (req_a): a > 0",
                "requires (req_b) :",
                "  b > 0",
                "ensures (ens_result):",
                "  result > 0",
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();

            assert_eq!(spec.requires.len(), 2);

            // req_a inline
            assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "req_a");
            assert_eq!(spec.requires[0].lines.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "a > 0");

            // req_b next line
            assert_eq!(spec.requires[1].name.as_ref().unwrap().content, "req_b");
            assert_eq!(spec.requires[1].lines.len(), 1);
            assert_eq!(spec.requires[1].lines[0].content, "  b > 0");

            assert_eq!(spec.ensures.len(), 1);
            assert_eq!(spec.ensures[0].name.as_ref().unwrap().content, "ens_result");
            assert_eq!(spec.ensures[0].lines.len(), 1);
            assert_eq!(spec.ensures[0].lines[0].content, "  result > 0");
        }

        #[test]
        fn test_edge_named_requires_malformed() {
            let lines = mk_lines(&[
                "requires (missing_colon) a > 0",     // No colon
                "ensures (missing_paren: result > 0", // Unclosed paren
            ]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_edge_proof_context_whitespace() {
            let lines = mk_lines(&[
                "proof    context:", // spaces
                "  let x = 1",
                "proof\tcontext:", // tabs
                "  let y = 2",
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.proof_context.lines.len(), 2);
            assert_eq!(spec.proof_context.lines[0].content, "  let x = 1");
            assert_eq!(spec.proof_context.lines[1].content, "  let y = 2");
        }
    }

    mod named_bounds_edge_cases {
        use super::*;

        fn dummy_line(content: &str) -> SpannedLine {
            SpannedLine {
                content: content.to_string(),
                span: (0, 0).into(),
                raw_span: AstNode::new(proc_macro2::Span::call_site()),
            }
        }

        #[test]
        fn test_parse_name_extraction() {
            let lines = vec![dummy_line("requires (h_name) : x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "h_name");
            assert_eq!(spec.requires[0].lines[0].content, "x > 0");
        }

        #[test]
        fn test_parse_name_extraction_spacing() {
            let lines = vec![dummy_line("requires  (  h_name  )  :  x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "h_name");
            assert_eq!(spec.requires[0].lines[0].content, "x > 0");
        }

        #[test]
        fn test_parse_colon_without_name() {
            let lines = vec![dummy_line("requires : x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert!(spec.requires[0].name.is_none());
            assert_eq!(spec.requires[0].lines[0].content, "x > 0");
        }

        #[test]
        fn test_parse_name_without_colon() {
            let lines = vec![dummy_line("requires (h_name) x > 0")];
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_parse_unmatched_parens() {
            let lines = vec![dummy_line("requires (h_name : x > 0")];
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_parse_nested_parens() {
            let lines = vec![dummy_line("requires (h_name(1)): x > 0")];
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_bizarre_proof_no_colon() {
            let lines = vec![dummy_line("proof (h_my_proof): trivial")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.proof_cases.len(), 1);
            assert_eq!(spec.proof_cases[0].name.as_ref().unwrap().content, "h_my_proof");
            assert_eq!(spec.proof_cases[0].lines[0].content, "trivial");
        }

        #[test]
        fn test_bizarre_requires_no_space_before_paren() {
            let lines = vec![dummy_line("requires (h_no_space): x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "h_no_space");
            assert_eq!(spec.requires[0].lines[0].content, "x > 0");
        }

        #[test]
        fn test_bizarre_requires_only_colon() {
            let lines = vec![dummy_line("requires: x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert!(spec.requires[0].name.is_none());
            assert_eq!(spec.requires[0].lines[0].content, "x > 0");
        }

        #[test]
        fn test_bizarre_proof_with_unusual_unicode() {
            let lines = vec![dummy_line("proof (h_ßåç):")];
            // Rust's char::is_alphanumeric allows extended Unicode alphabetic chars.
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.proof_cases.len(), 1);
            assert_eq!(spec.proof_cases[0].name.as_ref().unwrap().content, "h_ßåç");
        }

        #[test]
        fn test_bizarre_multiple_colons() {
            let lines = vec![dummy_line("ensures (h_colons): : : x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.ensures.len(), 1);
            assert_eq!(spec.ensures[0].name.as_ref().unwrap().content, "h_colons");
            assert_eq!(spec.ensures[0].lines[0].content, ": : x > 0");
        }

        #[test]
        fn test_bizarre_keep_keyword_interaction() {
            let lines = mk_lines(&["isValid (name):=", "  x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(err.1, "`isValid` sections cannot be named.");
        }

        #[test]
        fn test_dusty_proof_context_with_colon() {
            let lines = vec![dummy_line("proof context: let x = 5")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(spec.proof_context.keyword_span.is_some());
            assert_eq!(spec.proof_context.lines[0].content, "let x = 5");
        }

        #[test]
        fn test_dusty_inner_colons() {
            let lines = mk_lines(&["requires (:h_name:):", "  x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(
                err.1,
                "Invalid bound name `:h_name:`. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore)."
            );
        }

        #[test]
        fn test_dusty_spaced_name() {
            let lines = mk_lines(&["requires (my name):", "  x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(
                err.1,
                "Invalid bound name `my name`. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore)."
            );
        }

        #[test]
        fn test_invalid_lean_identifier_symbols() {
            let lines = mk_lines(&["requires (h-foo!):", "  x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(
                err.1,
                "Invalid bound name `h-foo!`. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore)."
            );
        }

        #[test]
        fn test_invalid_lean_identifier_starts_with_number() {
            let lines = mk_lines(&["requires (1h_foo):", "  x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(
                err.1,
                "Invalid bound name `1h_foo`. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore)."
            );
        }

        #[test]
        fn test_unsupported_named_is_valid() {
            let lines = mk_lines(&["isValid (my_inv):="]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(err.1, "`isValid` sections cannot be named.");
        }

        #[test]
        fn test_unsupported_named_proof_context() {
            let lines = mk_lines(&["proof context (ctx_name):", "  have h : x = 0 := rfl"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(err.1, "`proof context` sections cannot be named.");
        }

        #[test]
        fn test_dusty_proof_extra_closing_parens() {
            let lines = vec![dummy_line("proof (h_name)):")];
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_empty_name() {
            let lines = mk_lines(&["requires (): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(
                err.1,
                "Invalid bound name ``. Names must be valid identifiers (alphanumeric and underscores, starting with a letter or underscore)."
            );
        }

        #[test]
        fn test_underscore_name() {
            let lines = vec![dummy_line("requires (_): x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "_");
        }

        #[test]
        fn test_proof_colon_stripping() {
            let lines = vec![dummy_line("proof:"), dummy_line("proof (foo):")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.proof_cases.len(), 2);
            assert!(spec.proof_cases[0].name.is_none());
            assert!(spec.proof_cases[0].lines.is_empty());
            assert_eq!(spec.proof_cases[1].name.as_ref().unwrap().content, "foo");
            assert!(spec.proof_cases[1].lines.is_empty());
        }

        #[test]
        fn test_double_colon_requires() {
            let lines = vec![dummy_line("requires (name):: x > 0")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].name.as_ref().unwrap().content, "name");
            assert_eq!(spec.requires[0].lines[0].content, ": x > 0");
        }

        #[test]
        fn test_unnamed_missing_parens_colon() {
            let lines = vec![dummy_line("requires name: x > 0")];
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_adversarial_keyword_smashing() {
            // "proofcontext" should not parse as "proof context"
            // Since it's the first line, it fails initialization.
            let lines = mk_lines(&["proofcontext:"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("Expected a Hermes keyword to start the block"));
        }

        #[test]
        fn test_adversarial_parens_in_name() {
            let lines = mk_lines(&["requires (foo()): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_adversarial_double_parens() {
            let lines = mk_lines(&["requires ((name)): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_adversarial_offside_spoofing() {
            let lines = mk_lines(&["requires (name):", "  requires (spoof): x > 0"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].lines.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  requires (spoof): x > 0");
        }

        #[test]
        fn test_adversarial_newline_in_signature() {
            let lines = vec![
                dummy_line("requires ("),
                dummy_line("  h_name"),
                dummy_line("): x > 0"), // This violates the off-side rule
                                        // because it is at baseline indent but
                                        // is not a keyword.
            ];
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(
                err.1.contains("Invalid indentation")
                    || err.1.contains("must be followed by a colon")
            );
        }

        #[test]
        fn test_adversarial_valid_keyword_with_trailing_colon() {
            let lines = vec![dummy_line("isValid:"), dummy_line("  true")];
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.is_valid[0].lines.len(), 2);
            assert_eq!(spec.is_valid[0].lines[0].content, "isValid:");
            assert_eq!(spec.is_valid[0].lines[1].content, "  true");
        }

        #[test]
        fn test_adversarial_emoji_name() {
            let lines = mk_lines(&["requires (h_🦀): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("Invalid bound name `h_🦀`"));
        }

        #[test]
        fn test_adversarial_context_named() {
            let lines = mk_lines(&["context (foo):"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(err.1, "`context` sections cannot be named.");
        }


        #[test]
        fn test_adversarial_is_safe_named() {
            let lines = mk_lines(&["isSafe (foo):"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert_eq!(err.1, "`isSafe` sections cannot be named.");
        }

        #[test]
        fn test_adversarial_lean_keyword_requires() {
            let lines = mk_lines(&["requires (if): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("Names cannot be Lean keywords"));
        }

        #[test]
        fn test_adversarial_lean_keyword_ensures() {
            let lines = mk_lines(&["ensures (then): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("Names cannot be Lean keywords"));
        }

        #[test]
        fn test_adversarial_lean_keyword_proof() {
            let lines = mk_lines(&["requires: x > 0", "proof (theorem):", "  simp_all"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(
                err.1.contains("Names cannot be Lean keywords")
                    || err.1.contains("must be followed by a colon")
            );
        }

        #[test]
        fn test_adversarial_requires_multiline_colon() {
            // A requires block that has a name but the colon is on the next line.
            // This is malformed and fails to parse.
            let lines = mk_lines(&["requires (name)", "  : x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }

        #[test]
        fn test_adversarial_proof_context_named_no_colon() {
            // Trying to name a proof context without a colon. It falls back to unnamed content.
            let lines = mk_lines(&["proof context (foo) x = 1"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(
                err.1.contains("must be followed by a colon") || err.1.contains("proof context")
            );
        }

        #[test]
        fn test_adversarial_multiple_parens() {
            // Testing multiple independent parens. The name should only be targeted on the first enclosed token
            // followed immediately by `:`. This one is NOT followed by `:`, so it fails!
            let lines = mk_lines(&["requires (name) (other): x > 0"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("must be followed by a colon"));
        }
    }

    mod static_validation {
        use super::*;

        fn dummy_attr(doc: &str) -> syn::Attribute {
            let doc_str = format!(" ```hermes\n{}\n```", doc);
            syn::parse_quote!(#[doc = #doc_str])
        }

        #[test]
        fn test_multiple_unnamed_requires_allowed() {
            let attrs = vec![dummy_attr("requires: a > 0\nrequires: b > 0")];
            let err = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap_err();
            assert!(
                err.to_string().contains("Cannot mix named and unnamed `requires` clauses")
                    || err.to_string().contains("must all be named"),
                "Actual error: {}",
                err
            );
        }

        #[test]
        fn test_mix_named_unnamed_ensures_allowed() {
            let attrs = vec![dummy_attr("ensures (foo): a > 0\nensures: b > 0")];
            let spec = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
            assert_eq!(spec.ensures.len(), 2);
        }

        #[test]
        fn test_duplicate_requires_name() {
            let attrs = vec![dummy_attr("requires (foo): a > 0\nrequires (foo): b > 0")];
            let err = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap_err();
            assert!(err.to_string().contains("Duplicate bound name `foo`"));
        }

        #[test]
        fn test_conflict_between_requires_and_ensures() {
            let attrs = vec![dummy_attr("requires (foo): a > 0\nensures (foo): b > 0")];
            let err = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap_err();
            assert!(
                err.to_string()
                    .contains("Bound name `foo` conflicts with an existing requires bound")
            );
        }

        #[test]
        fn test_multiple_proofs_mixed_allowed() {
            let attrs =
                vec![dummy_attr("ensures (a): x\nensures (b): y\nproof (a): p1\nproof: p2")];
            let spec = FunctionHermesBlock::parse_from_attrs(&attrs, true, "").unwrap().unwrap();
            if let crate::parse::attr::FunctionBlockInner::Proof { cases, .. } = spec.inner {
                assert_eq!(cases.len(), 2);
            } else {
                panic!();
            }
        }

        #[test]
        fn test_missing_colon_rejections_exhaustive() {
            let cases = vec![
                // Base keywords without colons
                "requires x > 0",
                "ensures x > 0",
                "proof context x > 0",
                "context x > 0",
                "proof trivial",
                // Named keywords without colons
                "requires (name) x > 0",
                "ensures (name) x > 0",
                "proof (name) x > 0",
                // Malformed colons or trickery
                "requires (name x > 0",
                "requires name) x > 0",
                "proof context (name) x > 0",
            ];

            for case in cases {
                let attrs = vec![dummy_attr(case)];
                match FunctionHermesBlock::parse_from_attrs(&attrs, true, "") {
                    Ok(Some(parsed)) => {
                        // If it parsed successfully, it MUST mean that the
                        // keyword was completely ignored (e.g., `requires x >
                        // 0` didn't match `requires:` or `requires (name):`)
                        // and thus was treated as initialization garbage text.
                        // We verify that NO clauses were actually parsed from
                        // it.
                        let has_any_parsed_data = !parsed.requires.is_empty()
                            || !parsed.ensures.is_empty()
                            || !parsed.common.context.is_empty();

                        let has_proof_data = match parsed.inner {
                            super::FunctionBlockInner::Proof { context, cases } => {
                                !context.is_empty() || !cases.is_empty()
                            }
                            _ => false,
                        };

                        assert!(
                            !has_any_parsed_data && !has_proof_data,
                            "Case `{}` parsed as valid clauses despite missing/malformed colon!",
                            case
                        );
                    }
                    Ok(None) => {} // Block was not present, meaning hermes couldn't
                    // parse it as hermes at all. This is fine.
                    Err(err) => {
                        let err_msg = err.to_string();
                        // Every explicitly rejected error must be one of these
                        assert!(
                            err_msg.contains("must be followed by a colon")
                                || err_msg.contains("Names must be valid identifiers")
                                || err_msg.contains("Expected a Hermes keyword to start the block"),
                            "Failed to correctly reject missing colon for case: `{}`. Instead got: {}",
                            case,
                            err_msg
                        );
                    }
                }
            }
        }
    }

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
