use proc_macro2::Span;
use syn::{ExprLit, MetaNameValue};

use super::*;

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
    pub lines: Vec<SpannedLine<M>>,
}

/// A parsed Hermes documentation block attached to a function.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct FunctionHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub requires: Vec<Clause<M>>,
    pub ensures: Vec<Clause<M>>,
    pub inner: FunctionBlockInner<M>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum FunctionBlockInner<M: ThreadSafety = Local> {
    Proof { lines: Vec<SpannedLine<M>>, keyword: Option<AstNode<Span, M>> },
    Axiom { lines: Vec<SpannedLine<M>>, keyword: Option<AstNode<Span, M>> },
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

/// Extracts the string content and spans for each line from a documentation attribute.
///
/// This handles `///`, `//!`, `/** ... */`, and `#[doc = "..."]` attributes uniformly.
/// It attempts to calculate the precise source span for each line of content, which
/// is critical for accurate error reporting.
///
/// If the source code cannot be read or the content doesn't match the expected
/// locations, it falls back to using the attribute's full span.
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

            // If we can't read the source (e.g. during testing with dummy sources),
            // fallback to the original span.
            let raw_slice = match source.get(start..start + len) {
                Some(slice) => slice,
                None => return vec![(content, span, original_span)],
            };

            // Determine the offset of the content within the raw slice.
            //
            // We need to skip over the comment markers (`///`, `//!`, `/**`) or
            // the attribute syntax (`#[doc = ...]`) to find the actual text
            // content.
            let trimmed = raw_slice.trim_start();
            let leading_ws = raw_slice.len() - trimmed.len();

            let offset = if trimmed.starts_with("///")
                || trimmed.starts_with("//!")
                || trimmed.starts_with("/**")
                || trimmed.starts_with("/*!")
            {
                leading_ws + 3
            } else if let Some(after_bracket) = trimmed.strip_prefix("#[") {
                // Handle #[doc = "..."]
                // We need to find the opening quote of the string literal after `doc` and `=`.
                // A robust way is to find the first `=` and then the first quote.
                after_bracket
                    .find('=')
                    .and_then(|eq_idx| {
                        let after_eq = &after_bracket[eq_idx + 1..];
                        after_eq.find(|c: char| c == '"' || c == 'r').map(|quote_intra_idx| {
                            let quote_total_idx = eq_idx + 1 + quote_intra_idx;
                            let literal_part = &after_bracket[quote_total_idx..];
                            let quote_width = if literal_part.starts_with('r') {
                                // Raw string: r"...", r#"..."#, etc.
                                literal_part.find('"').map(|i| i + 1).unwrap_or(1)
                            } else {
                                1 // Standard "
                            };
                            leading_ws + 2 + quote_total_idx + quote_width // +2 for "#["
                        })
                    })
                    .unwrap_or_else(|| {
                        // Fallback: search for content if we can't recognize the structure
                        raw_slice.find(&content).unwrap_or(0)
                    })
            } else {
                // Fallback: search for content if we can't recognize the structure
                raw_slice.find(&content).unwrap_or(0)
            };

            let real_start = start + offset;

            // Verify that the content we found matches exactly what `syn` gave us.
            // This is a safety check: strict span calculation relies on this match.
            // If they don't match (e.g., due to macro expansion or escaped characters
            // we didn't account for perfectly), we still return the content but
            // with a less precise span (falling back to the attribute span).
            let expected_source_slice = source.get(real_start..real_start + content.len());
            let exact_match = expected_source_slice == Some(content.as_str());

            let mut results = Vec::new();
            let mut current_offset = real_start;

            // Split multiline content (common in `/** ... */` blocks) into individual lines.
            // Each line gets its own calculated span.
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

                let final_content = if part.ends_with('\r') {
                    if exact_match {
                        part_span = SourceSpan::new(part_span.offset().into(), part_len - 1);
                    }
                    &part[..part.len() - 1]
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
fn parse_block_lines<'a, I>(iter: &mut I, start: Span) -> Result<(Vec<SpannedLine>, Span), Error>
where
    I: Iterator<Item = (String, SourceSpan, Span)>,
{
    let mut lines = Vec::new();
    let mut end = start;
    let mut closed = false;

    for (line, span, original_span) in iter {
        if line.trim().starts_with("```") {
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
/// This function flat-maps all documentation attributes into a single stream of lines,
/// allowing it to handle both single-line `///` comments and multi-line `/** ... */`
/// blocks transparently. It looks for a start fence ` ```... ` and parses the content
/// until the end fence.
fn parse_hermes_block_common(
    attrs: &[Attribute],
    source: &str,
) -> Result<Option<(ParsedHermesBody, ParsedInfoString)>, Error> {
    let mut all_lines = attrs.iter().flat_map(|attr| extract_doc_line(attr, source));

    let mut block = None;

    while let Some((text, _, start_original)) = all_lines.next() {
        // Check for start fence
        let info_opt = text.trim().strip_prefix("```");
        if info_opt.is_none() {
            // Not a start fence, skip this line logic
            continue;
        }
        let info = info_opt.unwrap();

        let parsed_info = match parse_hermes_info_string(info.trim()) {
            Ok(Some(a)) => a,
            Ok(None) => continue,
            Err(msg) => return Err(Error::new(start_original, msg)),
        };

        if block.is_some() {
            return Err(Error::new(
                start_original,
                "Multiple Hermes blocks found on a single item.",
            ));
        }

        let (lines, end) = parse_block_lines(&mut all_lines, start_original)?;

        let body = match RawHermesSpecBody::parse(&lines) {
            Ok(body) => body,
            Err((err_span, msg)) => {
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
    if let Some(span) = &section.keyword_span {
        Err(Error::new(span.inner, msg))
    } else {
        Ok(())
    }
}

/// Returns an error containing `msg` if `clauses` is non-empty.
fn reject_clauses(clauses: &[Clause<Local>], msg: &str) -> Result<(), Error> {
    if let Some(clause) = clauses.first() {
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
            reject_clauses(&body.requires, "`requires` sections are only permitted on functions.")?;
            reject_clauses(&body.ensures, "`ensures` sections are only permitted on functions.")?;
            reject_section(
                &body.proof,
                "`proof` sections are only permitted on `spec` functions.",
            )?;
            reject_section(
                &body.axiom,
                "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
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
    pub fn parse_from_attrs(attrs: &[Attribute], source: &str) -> Result<Option<Self>, Error> {
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

        let inner = match attribute {
            FunctionAttribute::Spec => {
                reject_section(
                    &body.axiom,
                    "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
                )?;
                FunctionBlockInner::Proof {
                    lines: body.proof.lines,
                    keyword: body.proof.keyword_span,
                }
            }
            FunctionAttribute::UnsafeAxiom => {
                reject_section(
                    &body.proof,
                    "`proof` sections are only permitted on `spec` functions.",
                )?;
                FunctionBlockInner::Axiom {
                    lines: body.axiom.lines,
                    keyword: body.axiom.keyword_span,
                }
            }
        };

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

        Ok(Some(Self { common, is_valid: body.is_valid }))
    }
}

impl TraitHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute], source: &str) -> Result<Option<Self>, Error> {
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
    Proof,
    Axiom,
    IsValid,
    IsSafe,
}

/// The structured content of a completely unvalidated Hermes specification block.
#[derive(Debug, Default, Clone)]
pub(super) struct RawHermesSpecBody {
    /// Content before any keyword (e.g., Lean imports, let bindings, type invariants)
    pub(super) context: RawSection,
    pub(super) requires: Vec<Clause<Local>>,
    pub(super) ensures: Vec<Clause<Local>>,
    pub(super) proof: RawSection,
    pub(super) axiom: RawSection,
    pub(super) is_valid: Vec<Clause<Local>>,
    pub(super) is_safe: Vec<Clause<Local>>,
}

pub(super) struct ParsedHermesBody {
    pub(super) body: RawHermesSpecBody,
    pub(super) content_span: Span,
    pub(super) start_span: Span,
}

impl RawHermesSpecBody {
    // Helper to push a line to the current active destination
    fn add_line(&mut self, section: Section, line: SpannedLine<Local>) {
        match section {
            Section::Init | Section::Context => self.context.lines.push(line),
            Section::Proof => self.proof.lines.push(line),
            Section::Axiom => self.axiom.lines.push(line),
            Section::Requires => {
                if let Some(clause) = self.requires.last_mut() {
                    clause.lines.push(line);
                }
            }
            Section::Ensures => {
                if let Some(clause) = self.ensures.last_mut() {
                    clause.lines.push(line);
                }
            }
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

    // Helper to start a new clause or section
    fn start_section(
        &mut self,
        section: Section,
        keyword_span: AstNode<Span, Local>,
        arg: Option<SpannedLine<Local>>,
    ) {
        match section {
            Section::Init | Section::Context => {
                // explicit 'context' keyword?
                self.context.keyword_span = Some(keyword_span);
                if let Some(l) = arg {
                    self.context.lines.push(l);
                }
            }
            Section::Proof => {
                self.proof.keyword_span = Some(keyword_span);
                if let Some(l) = arg {
                    self.proof.lines.push(l);
                }
            }
            Section::Axiom => {
                self.axiom.keyword_span = Some(keyword_span);
                if let Some(l) = arg {
                    self.axiom.lines.push(l);
                }
            }
            Section::Requires => {
                let lines = arg.into_iter().collect();
                self.requires.push(Clause { keyword_span, lines });
            }
            Section::Ensures => {
                let lines = arg.into_iter().collect();
                self.ensures.push(Clause { keyword_span, lines });
            }
            Section::IsValid => {
                let lines = arg.into_iter().collect();
                self.is_valid.push(Clause { keyword_span, lines });
            }
            Section::IsSafe => {
                let lines = arg.into_iter().collect();
                self.is_safe.push(Clause { keyword_span, lines });
            }
        }
    }

    /// Parses a sequence of raw documentation lines into structured sections.
    fn parse<'a, I>(lines: I) -> Result<Self, (SourceSpan, String)>
    where
        I: IntoIterator<Item = &'a SpannedLine<Local>>,
    {
        // Matches exact keywords or keywords followed by any whitespace,
        // returning the trimmed remainder.
        fn strip_keyword<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
            line.strip_prefix(keyword)
                .filter(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace))
        }

        let keywords = [
            ("context", Section::Context),
            ("requires", Section::Requires),
            ("ensures", Section::Ensures),
            ("proof", Section::Proof),
            ("axiom", Section::Axiom),
            ("isValid", Section::IsValid),
            ("isSafe", Section::IsSafe),
        ];

        lines
            .into_iter()
            .try_fold(
                (RawHermesSpecBody::default(), Section::Init, None::<usize>),
                |(mut spec, current_section, baseline_indent), line| {
                    let trimmed = line.content.trim();
                    let span = line.span;
                    let raw_span = line.raw_span.clone();

                    let item = SpannedLine {
                        content: line.content.clone(),
                        span,
                        raw_span: raw_span.clone(),
                    };

                    if trimmed.is_empty() {
                         // Pass empty lines to the current section/clause handler
                         // to preserve vertical spacing if needed, or ignore.
                         // For now, let's push them.
                         if current_section != Section::Init {
                              spec.add_line(current_section, item);
                         }
                        return Ok((spec, current_section, baseline_indent));
                    }

                    let indent = line.content.len() - line.content.trim_start().len();

                    if let Some((&section, arg_str)) = keywords
                        .iter()
                        .find_map(|(k, s)| strip_keyword(trimmed, k).map(|arg| (s, arg)))
                    {
                        let arg = if !arg_str.trim().is_empty() {
                            Some(SpannedLine {
                                content: arg_str.to_string(),
                                span, // Note: This span covers the whole line including keyword
                                raw_span: raw_span.clone(),
                            })
                            // ideally we'd slice the span for the arg, but `extract_doc_line` gives us line granularity.
                            // We can keep using the full line span for the content line, that's fine.
                            // The keyword span however... line.raw_span is the whole line.
                        } else {
                            None
                        };

                        spec.start_section(section, raw_span, arg);
                        return Ok((spec, section, Some(indent)));
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
                             Hermes keyword (context, requires, ensures, proof, axiom, isValid, isSafe). \
                             Did you misspell a keyword?"
                                .to_string(),
                        ));
                    }
                    // Not a new keyword; continuation of the current section.
                    spec.add_line(current_section, item);

                    Ok((spec, current_section, baseline_indent))
                },
            )
            .map(|(spec, _, _)| spec)
    }
}

#[cfg(test)]
mod tests {
    use syn::parse_quote;

    use super::*;

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
            parse_quote!(#[doc = " context"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
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
            parse_quote!(#[doc = " context"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
        match block {
            FunctionHermesBlock {
                common: HermesBlockCommon { context, .. },
                inner: FunctionBlockInner::Axiom { .. },
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
        let err = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
        assert_eq!(err.to_string(), "Unclosed Hermes block in documentation.");
    }

    #[test]
    fn test_parse_from_attrs_interrupted() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " context"]),
            parse_quote!(#[doc = " line 1"]),
            parse_quote!(#[derive(Clone)]), // Interrupts contiguous doc lines
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
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
        let err = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
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
        assert!(!spec.proof.is_present());
        assert!(!spec.axiom.is_present());
    }

    #[test]
    fn test_hermes_spec_body_parse_context_only() {
        let lines = mk_lines(&["context", "import Foo", "def bar := 1"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(spec.context.is_present());
        assert_eq!(spec.context.lines.len(), 2);
        assert_eq!(spec.context.lines[0].content, "import Foo");
    }

    #[test]
    fn test_hermes_spec_body_parse_requires() {
        let lines = mk_lines(&["requires", "  x > 0", "  y > 0"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        let clause = &spec.requires[0];
        assert_eq!(clause.lines.len(), 2);
        assert_eq!(clause.lines[0].content, "  x > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_clauses() {
        let lines = mk_lines(&["requires", "  x > 0", "requires", "  y > 0"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
        assert_eq!(spec.requires[1].lines[0].content, "  y > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_sections() {
        let lines = mk_lines(&["requires", "  x > 0", "ensures", "  result = x"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
        assert_eq!(spec.ensures[0].lines[0].content, "  result = x");
    }

    #[test]
    fn test_hermes_spec_body_parse_inline_arg() {
        let lines = mk_lines(&["requires x > 0", "  y > 0"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].lines.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, " x > 0");
        assert_eq!(spec.requires[0].lines[1].content, "  y > 0");
    }

    #[test]
    fn test_hermes_spec_body_parse_invalid_indent() {
        let lines = mk_lines(&["requires", "x > 0", "y > 0"]); // "y > 0" has same indent/no indent as requires?
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
        assert!(err.1.contains("Expected a Hermes keyword"));
    }

    #[test]
    fn test_hermes_spec_body_parse_strict_keywords() {
        let lines = mk_lines(&[
            "context",
            "requires_foo a",
            "ensuresbar",
            "proof_of_concept",
            "axiomatic",
            "  requires   ", // valid keyword
            "   genuine requirements ",
        ]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        // The first four are context lines because they don't match keywords strictly.
        assert_eq!(spec.context.lines.len(), 4);
        assert_eq!(spec.context.lines[0].content, "requires_foo a");
        assert_eq!(spec.context.lines[1].content, "ensuresbar");
        assert_eq!(spec.context.lines[2].content, "proof_of_concept");
        assert_eq!(spec.context.lines[3].content, "axiomatic");

        // "  requires   " switches section but adds no lines because its arg is empty.
        // Following line is added verbatim to requires section.
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].lines[0].content, "   genuine requirements ");
        assert!(spec.ensures.is_empty());
    }

    #[test]
    fn test_hermes_spec_body_parse_arguments_vs_continuation() {
        let lines = mk_lines(&[
            "requires a > 0",
            "  and b < 0", // Continuation: keeps original whitespace
            "ensures c == 1",
            "proof", // standalone keyword
            "  trivial",
        ]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(!spec.context.is_present());

        assert_eq!(spec.requires.len(), 1);
        // Prefix argument keeps its exact text post-"requires" (which is " a > 0").
        assert_eq!(spec.requires[0].lines[0].content, " a > 0");
        // Continuation line keeps full exact original text.
        assert_eq!(spec.requires[0].lines[1].content, "  and b < 0");

        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, " c == 1");

        assert_eq!(spec.proof.lines.len(), 1);
        assert_eq!(spec.proof.lines[0].content, "  trivial");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_same_section() {
        // Check that it can interleave sections or repeat them
        let lines = mk_lines(&["requires a", "ensures b", "requires c", "axiom d"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.requires[0].lines[0].content, " a");
        assert_eq!(spec.requires[1].lines[0].content, " c");

        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, " b");

        assert_eq!(spec.axiom.lines.len(), 1);
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
            mk_lines(&["context", "context_line", "requires", "  req1", "ensures", "  ens1"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.context.lines[0].content, "context_line");
        assert_eq!(spec.requires[0].lines[0].content, "  req1");
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, "  ens1");
    }

    #[test]
    fn test_parse_spec_inline_args_valid() {
        let lines = vec![
            dummy_line("requires a > 0"),
            dummy_line("ensures\tb > 0"), // Tests tab whitespace
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].lines[0].content, " a > 0");
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].lines[0].content, "\tb > 0");
    }

    #[test]
    fn test_parse_spec_blank_lines() {
        let lines = vec![
            dummy_line("requires"),
            dummy_line("  a > 0"),
            dummy_line(""),
            dummy_line("  b > 0"),
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires[0].lines.len(), 3); // 2 content lines + 1 blank line
    }

    #[test]
    fn test_parse_spec_header_no_indent_rules() {
        let lines = mk_lines(&["context", "context_line", "  indented context", "context again"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.context.lines.len(), 3);
    }

    #[test]
    fn test_parse_spec_err_typo_keyword() {
        let lines = vec![
            dummy_line("requires"),
            dummy_line("  a > 0"),
            dummy_line("ensure"), // Typo, missing 's'. Indentation is 0.
            dummy_line("  b > 0"),
        ];
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(err.1.contains("Invalid indentation"));
    }

    #[test]
    fn test_parse_spec_err_under_indented_continuation() {
        let lines = mk_lines(&[
            "context",
            "header",
            "requires",
            "  req1",
            "req2_oops", // This looks like a new keyword but isn't one, and isn't indented
        ]);
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(err.1.contains("Invalid indentation"));
    }

    #[test]
    fn test_parse_from_attrs_not_hermes() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```lean"]), parse_quote!(#[doc = " ```"])];
        let block_func = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap();
        assert!(block_func.is_none());
        let block_item = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap();
        assert!(block_item.is_none());
    }

    #[test]
    fn test_type_block_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " context"]), // Types shouldn't really have context/header usually, but parser allows it?
            // Actually TypeHermesBlock only takes `is_valid`.
            // Let's check `parse_from_attrs` implementation for TypeHermesBlock.
            // It calls `parse_item_block_common`.
            // `parse_item_block_common` allows header in `HermesBlockCommon`.
            // But `TypeHermesBlock` struct doesn't have `context` field? It has `common: HermesBlockCommon`.
            // `HermesBlockCommon` has `header`.
            // So yes, types can have context.
            parse_quote!(#[doc = " foo"]),
            parse_quote!(#[doc = " isValid"]),
            parse_quote!(#[doc = "  bar"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TypeHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
        assert_eq!(block.is_valid[0].lines[0].content, "  bar");
        assert_eq!(block.common.context[0].content, " foo");
    }

    #[test]
    fn test_type_block_missing_is_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " context"]),
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
        let block = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
        assert_eq!(block.is_safe.len(), 1);
        assert_eq!(block.is_safe[0].lines[0].content, "  val == true");
    }

    #[test]
    fn test_trait_block_missing_is_safe() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```hermes"]), parse_quote!(#[doc = " ```"])];
        let err = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
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
        let err = FunctionHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
        assert_eq!(err.to_string(), "`isValid` sections are only permitted on types.");
    }

    #[test]
    fn test_type_rejects_function_clauses() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " requires"]),
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
            parse_quote!(#[doc = " isValid"]),
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
        let lines = mk_lines(&["requires", "  x > 0", "ensures"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(!spec.requires.is_empty());
        assert!(!spec.ensures.is_empty());
        assert!(spec.ensures[0].lines.is_empty());
    }

    #[test]
    fn test_trait_rejects_is_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe my_trait"]),
            parse_quote!(#[doc = " isValid foo"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
        assert_eq!(err.to_string(), "`isValid` sections are only permitted on types.");
    }

    #[test]
    fn test_reject_section_points_to_keyword() {
        // Create dummy lines manually so we can distinguish raw_span
        let mut attrs: Vec<syn::Attribute> = vec![parse_quote!(#[doc = " ```hermes"])];

        let requires_attr: syn::Attribute = parse_quote!(#[doc = " requires"]);
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
    mod edge_cases {
        use super::*;

        #[test]
        fn test_keyword_prefix_safety() {
            // Verify that 'proof_helper' is parsed as content, not a 'proof' section.
            let lines = mk_lines(&[
                "requires",
                "  proof_helper", // Should be content of requires
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(!spec.requires.is_empty());
            assert_eq!(spec.requires[0].lines.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  proof_helper");
            assert!(!spec.proof.is_present());
        }

        #[test]
        fn test_keyword_collision_error() {
            // Verify that 'proof' inside 'requires' triggers a new section or error if indentation is wrong.
            // If it's indented, it MIGHT be parsed as content if it doesn't match the strict keyword rule?
            // "The parser currently greedily matches keywords".
            // Let's see if it switches section even if indented.
            let lines = mk_lines(&[
                "requires",
                "  proof", // Indented 'proof' - parser might treat as section start if greedy
            ]);
            // If it is treated as section start, 'proof' arg is empty.
            // But 'proof' is valid in Spec.
            // Fails if 'proof' cannot be inside 'requires' block? No, it just switches section.
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(!spec.requires.is_empty());
            assert!(spec.requires[0].lines.is_empty()); // 'proof' switched section
            assert!(spec.proof.is_present());
        }

        #[test]
        fn test_multiple_sections_concatenation() {
            let lines = mk_lines(&["requires a", "requires b"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 2);
            assert_eq!(spec.requires[0].lines[0].content, " a");
            assert_eq!(spec.requires[1].lines[0].content, " b");
        }

        #[test]
        fn test_typo_safety() {
            let lines = mk_lines(&[
                "requires",
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
                parse_quote!(#[doc = " requires true"]), // Should error
                parse_quote!(#[doc = " ```"]),
            ];
            let err = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap_err();
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
            let block = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
            assert!(block.is_safe.len() == 1);
            // The isSafe clause is present, but lines might be empty if "  nested" was outside.
            // Wait, "  nested" was NOT outside, it was AFTER ` ``` `?
            // "The parser sees the first ``` and stops."
            // So `isSafe` line had empty content.
            // Next line was ```.
            // So `isSafe` clause has 0 lines.
            assert!(block.is_safe[0].lines.is_empty());
        }

        #[test]
        fn test_mixed_tabs_spaces_indentation() {
            // Indentation logic uses `len() - trim_start().len()`.
            // '\t' is 1 char. ' ' is 1 char.
            let lines = mk_lines(&[
                "requires",
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
            let block = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
            assert!(block.is_safe.len() == 1);
            assert!(block.is_safe[0].lines.is_empty());
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
            let block = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
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
            let lines = mk_lines(&["requires", "  result > 0", "  old_x < new_x"]);
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
            let block = TraitHermesBlock::parse_from_attrs(&attrs, "").unwrap().unwrap();
            assert_eq!(block.is_safe.len(), 1);
            assert_eq!(block.is_safe[0].lines[0].content, "  val");
        }

        #[test]
        fn test_comment_before_keyword_fails() {
            let lines = mk_lines(&["// comment", "context"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("Expected a Hermes keyword"));
        }

        #[test]
        fn test_context_inline_args() {
            let lines = mk_lines(&["context inline_context", "more_context"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.context.lines[0].content, " inline_context");
            assert_eq!(spec.context.lines[1].content, "more_context");
        }

        #[test]
        fn test_multiple_context_sections() {
            let lines = mk_lines(&["context part1", "context part2"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.context.lines.len(), 2);
            assert_eq!(spec.context.lines[0].content, " part1");
            assert_eq!(spec.context.lines[1].content, " part2");
        }

        #[test]
        fn test_delayed_context() {
            let lines = mk_lines(&["requires x > 0", "context", "added_to_context"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert!(!spec.requires.is_empty());
            assert_eq!(spec.context.lines.len(), 1);
            assert_eq!(spec.context.lines[0].content, "added_to_context");
        }

        #[test]
        fn test_case_sensitive_context() {
            let lines = mk_lines(&["Context"]);
            let err = RawHermesSpecBody::parse(&lines).unwrap_err();
            assert!(err.1.contains("Expected a Hermes keyword"));
        }

        #[test]
        fn test_leading_whitespace_ignored() {
            let lines = mk_lines(&["   ", "", "context", "stuff"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.context.lines[0].content, "stuff");
        }

        #[test]
        fn test_edge_indentation_drift() {
            // Keywords at different indentation levels should be accepted
            // provided content is indented relative to its own keyword.
            let lines = mk_lines(&[
                "requires",
                "  x > 0",
                "  ensures", // Indented keyword
                "    y > 0", // Indented content
                "axiom",     // Back to 0
                "  z > 0",
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  x > 0");
            assert_eq!(spec.ensures.len(), 1);
            assert_eq!(spec.ensures[0].lines[0].content, "    y > 0");
            assert_eq!(spec.axiom.lines.len(), 1);
            assert_eq!(spec.axiom.lines[0].content, "  z > 0");
        }

        #[test]
        fn test_edge_keywords_as_content_wrapped() {
            let lines = mk_lines(&[
                "requires",
                "  (requires x)", // Safe
            ]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert_eq!(spec.requires[0].lines[0].content, "  (requires x)");
        }

        #[test]
        fn test_edge_empty_clauses() {
            let lines = mk_lines(&["requires", "ensures", "axiom"]);
            let spec = RawHermesSpecBody::parse(&lines).unwrap();
            assert_eq!(spec.requires.len(), 1);
            assert!(spec.requires[0].lines.is_empty());
            assert_eq!(spec.ensures.len(), 1);
            assert!(spec.ensures[0].lines.is_empty());
            assert_eq!(spec.axiom.lines.len(), 0); // Axiom is RawSection, has lines.
            assert!(spec.axiom.keyword_span.is_some());
        }

        #[test]
        fn test_edge_unicode_indentation() {
            // \u{2003} is em-space.
            // Rust string trim handles unicode whitespace.
            let lines = mk_lines(&["requires", "\u{2003}x > 0"]);
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
                    content: "requires\r".to_string(),
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
        assert!(start >= 3, "Span should start after '///'");
    }

    #[test]
    fn test_extract_doc_line_edge_cases() {
        let cases = vec![
            // 1. Sugared Comments
            ("/// content", " content", 3),
            ("///   content", "   content", 3),
            ("///content", "content", 3),
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
        ];

        let mut failures = Vec::new();

        for (source, _expected_content_value, expected_offset) in cases {
            let full_source = format!("{}\nfn foo() {{}}", source);
            let file = syn::parse_file(&full_source).expect("Failed to parse dummy source");

            // Try to find the attribute on the function first, then on the file (for inner attrs)
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
            if content != source_slice {
                if !source.contains("escaped") {
                    if content != source_slice {
                        failures.push(format!(
                            "Content-Source mismatch for '{}': content {:?}, source slice {:?}",
                            source, content, source_slice
                        ));
                    }
                }
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
        let (lines, _) = parse_block_lines(&mut iter, proc_macro2::Span::call_site()).unwrap();

        println!("Parsed {} lines", lines.len());
        for (i, line) in lines.iter().enumerate() {
            println!("Line {}: {:?}", i, line.content);
        }

        assert!(lines.len() >= 3, "Expected split lines, got {}", lines.len());
        assert!(lines.iter().any(|l| l.content.contains("line 1")));
        assert!(lines.iter().any(|l| l.content.contains("line 2")));
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
            lines: self.lines.into_iter().map(|l| l.lift()).collect(),
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
            Self::Proof { lines, keyword } => FunctionBlockInner::Proof {
                lines: lines.into_iter().map(|l| l.lift()).collect(),
                keyword: keyword.map(|k| k.lift()),
            },
            Self::Axiom { lines, keyword } => FunctionBlockInner::Axiom {
                lines: lines.into_iter().map(|l| l.lift()).collect(),
                keyword: keyword.map(|k| k.lift()),
            },
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionHermesBlock<M> {
    type Target = FunctionHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        FunctionHermesBlock {
            common: self.common.lift(),
            requires: self.requires.into_iter().map(|c| c.lift()).collect(),
            ensures: self.ensures.into_iter().map(|c| c.lift()).collect(),
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
