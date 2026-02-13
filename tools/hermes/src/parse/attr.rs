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

/// A parsed Hermes documentation block attached to a function.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct FunctionHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub requires: Vec<SpannedLine<M>>,
    pub ensures: Vec<SpannedLine<M>>,
    pub inner: FunctionBlockInner<M>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum FunctionBlockInner<M: ThreadSafety = Local> {
    Proof(Vec<SpannedLine<M>>),
    Axiom(Vec<SpannedLine<M>>),
}

/// A parsed Hermes documentation block attached to a struct, enum, or union.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypeHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub is_valid: Vec<SpannedLine<M>>,
}

/// A parsed Hermes documentation block attached to a trait.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TraitHermesBlock<M: ThreadSafety = Local> {
    pub common: HermesBlockCommon<M>,
    pub is_safe: Vec<SpannedLine<M>>,
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
    pub header: Vec<SpannedLine<M>>,
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

/// Helper to extract the string content and span from a `#[doc = "..."]` attribute.
///
/// Returns `Some((content, span))` if the attribute is a doc comment.
fn extract_doc_line(attr: &Attribute) -> Option<(String, Span)> {
    if !attr.path().is_ident("doc") {
        return None;
    }

    match &attr.meta {
        Meta::NameValue(MetaNameValue {
            value: Expr::Lit(ExprLit { lit: Lit::Str(s), .. }),
            ..
        }) => Some((s.value(), s.span())),
        _ => None,
    }
}

// Common parsing logic extracted
fn parse_block_lines<'a, I>(iter: &mut I, start: Span) -> Result<(Vec<SpannedLine>, Span), Error>
where
    I: Iterator<Item = &'a Attribute>,
{
    let mut lines = Vec::new();
    let mut end = start;
    let mut closed = false;

    for next in iter {
        let Some((line, span)) = extract_doc_line(next) else { break };

        if line.trim().starts_with("```") {
            closed = true;
            break;
        }

        lines.push(SpannedLine {
            content: line,
            span: span_to_miette(span),
            raw_span: AstNode::new(span),
        });
        end = span;
    }

    if !closed {
        return Err(Error::new(start, "Unclosed Hermes block in documentation."));
    }

    Ok((lines, end))
}

fn parse_hermes_block_common(
    attrs: &[Attribute],
) -> Result<Option<(ParsedHermesBody, ParsedInfoString)>, Error> {
    let mut iter = attrs.iter();
    let mut block = None;

    while let Some(attr) = iter.next() {
        let Some((text, start)) = extract_doc_line(attr) else { continue };
        let Some(info) = text.trim().strip_prefix("```") else { continue };

        let parsed_info = match parse_hermes_info_string(info.trim()) {
            Ok(Some(a)) => a,
            Ok(None) => continue,
            Err(msg) => return Err(Error::new(start, msg)),
        };

        if block.is_some() {
            return Err(Error::new(start, "Multiple Hermes blocks found on a single item."));
        }

        let (lines, end) = parse_block_lines(&mut iter, start)?;

        let body = match RawHermesSpecBody::parse(&lines) {
            Ok(body) => body,
            Err((err_span, msg)) => {
                let raw_span = lines
                    .iter()
                    .find(|l| l.span == err_span)
                    .map(|l| l.raw_span.inner)
                    .unwrap_or(start);
                return Err(Error::new(raw_span, msg));
            }
        };
        block = Some((
            ParsedHermesBody {
                body,
                content_span: start.join(end).unwrap_or(start),
                start_span: start,
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

fn parse_item_block_common(
    attrs: &[Attribute],
    context_name: &str,
) -> Result<Option<(HermesBlockCommon, RawHermesSpecBody)>, Error> {
    parse_hermes_block_common(attrs)?
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
            reject_section(&body.requires, "`requires` sections are only permitted on functions.")?;
            reject_section(&body.ensures, "`ensures` sections are only permitted on functions.")?;
            reject_section(
                &body.proof,
                "`proof` sections are only permitted on `spec` functions.",
            )?;
            reject_section(
                &body.axiom,
                "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
            )?;

            let common = HermesBlockCommon {
                header: std::mem::take(&mut body.header),
                content_span: AstNode::new(item.content_span),
                start_span: AstNode::new(item.start_span),
            };

            Ok((common, body))
        })
        .transpose()
}

impl FunctionHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute]) -> Result<Option<Self>, Error> {
        let Some((item, parsed_info)) = parse_hermes_block_common(attrs)? else {
            return Ok(None);
        };

        let attribute = match parsed_info {
            ParsedInfoString::FunctionMode(attr) => attr,
            ParsedInfoString::GenericMode => FunctionAttribute::Spec, // Implicit `spec` for functions
        };

        let body = item.body;
        reject_section(&body.is_valid, "`isValid` sections are only permitted on types.")?;
        reject_section(&body.is_safe, "`isSafe` sections are only permitted on traits.")?;

        let inner = match attribute {
            FunctionAttribute::Spec => {
                reject_section(
                    &body.axiom,
                    "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
                )?;
                FunctionBlockInner::Proof(body.proof.lines)
            }
            FunctionAttribute::UnsafeAxiom => {
                reject_section(
                    &body.proof,
                    "`proof` sections are only permitted on `spec` functions.",
                )?;
                FunctionBlockInner::Axiom(body.axiom.lines)
            }
        };

        Ok(Some(Self {
            common: HermesBlockCommon {
                header: body.header,
                content_span: AstNode::new(item.content_span),
                start_span: AstNode::new(item.start_span),
            },
            requires: body.requires.lines,
            ensures: body.ensures.lines,
            inner,
        }))
    }
}

impl TypeHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute]) -> Result<Option<Self>, Error> {
        let Some((common, body)) = parse_item_block_common(attrs, "types")? else {
            return Ok(None);
        };

        reject_section(&body.is_safe, "`isSafe` sections are only permitted on traits.")?;

        if !body.is_valid.is_present() {
            return Err(Error::new(
                common.start_span.inner,
                "Hermes blocks on types must define an `isValid` type invariant. Did you misspell it?",
            ));
        }

        Ok(Some(Self { common, is_valid: body.is_valid.lines }))
    }
}

impl TraitHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute]) -> Result<Option<Self>, Error> {
        let Some((common, body)) = parse_item_block_common(attrs, "traits")? else {
            return Ok(None);
        };

        reject_section(&body.is_valid, "`isValid` sections are only permitted on types.")?;

        if !body.is_safe.is_present() {
            return Err(Error::new(
                common.start_span.inner,
                "Hermes blocks on traits must define an `isSafe` trait invariant. Did you misspell it?",
            ));
        }

        Ok(Some(Self { common, is_safe: body.is_safe.lines }))
    }
}

impl ImplHermesBlock<Local> {
    pub fn parse_from_attrs(attrs: &[Attribute]) -> Result<Option<Self>, Error> {
        let Some((common, body)) = parse_item_block_common(attrs, "impl items")? else {
            return Ok(None);
        };

        reject_section(&body.is_valid, "`isValid` sections are only permitted on types.")?;
        reject_section(&body.is_safe, "`isSafe` sections are only permitted on traits.")?;

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
    /// The exact span of the line where the keyword (e.g., `requires`)
    /// appeared.
    pub(super) keyword_span: Option<AstNode<Span, Local>>,
    pub(super) lines: Vec<SpannedLine<Local>>,
}

impl RawSection {
    /// Returns true if the keyword was encountered, even if no arguments were
    /// provided.
    pub(super) fn is_present(&self) -> bool {
        self.keyword_span.is_some()
    }
}

/// The structured content of a completely unvalidated Hermes specification block.
#[derive(Debug, Default, Clone)]
pub(super) struct RawHermesSpecBody {
    /// Content before any keyword (e.g., Lean imports, let bindings, type invariants)
    pub(super) header: Vec<SpannedLine<Local>>,
    pub(super) requires: RawSection,
    pub(super) ensures: RawSection,
    pub(super) proof: RawSection,
    pub(super) axiom: RawSection,
    pub(super) is_valid: RawSection,
    pub(super) is_safe: RawSection,
}

pub(super) struct ParsedHermesBody {
    pub(super) body: RawHermesSpecBody,
    pub(super) content_span: Span,
    pub(super) start_span: Span,
}

impl RawHermesSpecBody {
    /// Parses a sequence of raw documentation lines into structured sections.
    fn parse<'a, I>(lines: I) -> Result<Self, (SourceSpan, String)>
    where
        I: IntoIterator<Item = &'a SpannedLine<Local>>,
    {
        #[derive(Debug, Clone, Copy, PartialEq)]
        enum Section {
            Header,
            Requires,
            Ensures,
            Proof,
            Axiom,
            IsValid,
            IsSafe,
        }

        fn get_section(section: Section, spec: &mut RawHermesSpecBody) -> &mut RawSection {
            match section {
                Section::Requires => &mut spec.requires,
                Section::Ensures => &mut spec.ensures,
                Section::Proof => &mut spec.proof,
                Section::Axiom => &mut spec.axiom,
                Section::IsValid => &mut spec.is_valid,
                Section::IsSafe => &mut spec.is_safe,
                Section::Header => unreachable!(),
            }
        }

        // Matches exact keywords or keywords followed by any whitespace,
        // returning the trimmed remainder.
        fn strip_keyword<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
            line.strip_prefix(keyword)
                .filter(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace))
        }

        let keywords = [
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
                (RawHermesSpecBody::default(), Section::Header, None::<usize>),
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
                        if current_section == Section::Header {
                            spec.header.push(item);
                        } else {
                            get_section(current_section, &mut spec).lines.push(item);
                        }
                        return Ok((spec, current_section, baseline_indent));
                    }

                    let indent = line.content.len() - line.content.trim_start().len();

                    if let Some((&section, arg)) = keywords
                        .iter()
                        .find_map(|(k, s)| strip_keyword(trimmed, k).map(|arg| (s, arg)))
                    {
                        let sec = get_section(section, &mut spec);
                        sec.keyword_span.get_or_insert_with(|| raw_span.clone());

                        if !arg.trim().is_empty() {
                            sec.lines.push(SpannedLine {
                                content: arg.to_string(),
                                span,
                                raw_span,
                            });
                        }
                        return Ok((spec, section, Some(indent)));
                    }

                    if current_section != Section::Header && indent <= baseline_indent.unwrap() {
                        return Err((
                            span,
                            "Invalid indentation: expected an indented continuation or a valid \
                             Hermes keyword (requires, ensures, proof, axiom, isValid, isSafe). \
                             Did you misspell a keyword?"
                                .to_string(),
                        ));
                    }
                    // Not a new keyword; continuation of the current section.
                    if current_section == Section::Header {
                        spec.header.push(item);
                    } else {
                        get_section(current_section, &mut spec).lines.push(item);
                    }

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
        let result = extract_doc_line(&attr).unwrap();
        assert_eq!(result.0, " test line");

        // Non-doc attribute
        let attr: syn::Attribute = parse_quote!(#[derive(Clone)]);
        assert!(extract_doc_line(&attr).is_none());

        // Alternate doc syntax (e.g., hidden)
        let attr: syn::Attribute = parse_quote!(#[doc(hidden)]);
        assert!(extract_doc_line(&attr).is_none());
    }

    #[test]
    fn test_parse_from_attrs_valid_spec() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```lean, hermes, spec"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap().unwrap();
        match block {
            FunctionHermesBlock {
                common: HermesBlockCommon { header, .. },
                inner: FunctionBlockInner::Proof(_),
                ..
            } => {
                assert_eq!(header[0].content, " body 1");
                assert_eq!(header[1].content, " body 2");
            }
            _ => panic!("Expected block with Proof inner"),
        }
    }

    #[test]
    fn test_parse_from_attrs_valid_axiom() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```lean, hermes, unsafe(axiom)"]),
            parse_quote!(#[doc = " body 1"]),
            parse_quote!(#[doc = " body 2"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap().unwrap();
        match block {
            FunctionHermesBlock {
                common: HermesBlockCommon { header, .. },
                inner: FunctionBlockInner::Axiom(_),
                ..
            } => {
                assert_eq!(header[0].content, " body 1");
                assert_eq!(header[1].content, " body 2");
            }
            _ => panic!("Expected block with Axiom inner"),
        }
    }

    #[test]
    fn test_parse_from_attrs_unclosed() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```hermes"]), parse_quote!(#[doc = " no end fence"])];
        let err = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap_err();
        assert_eq!(err.to_string(), "Unclosed Hermes block in documentation.");
    }

    #[test]
    fn test_parse_from_attrs_interrupted() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " line 1"]),
            parse_quote!(#[derive(Clone)]), // Interrupts contiguous doc lines
            parse_quote!(#[doc = " ```"]),
        ];
        let err = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap_err();
        assert_eq!(err.to_string(), "Unclosed Hermes block in documentation.");
    }

    #[test]
    fn test_parse_from_attrs_multiple_blocks() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " ```"]),
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap_err();
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
        assert!(spec.header.is_empty());
        assert!(!spec.requires.is_present());
        assert!(!spec.ensures.is_present());
        assert!(!spec.proof.is_present());
        assert!(!spec.axiom.is_present());
    }

    #[test]
    fn test_hermes_spec_body_parse_header_only() {
        let lines = mk_lines(&["import Foo", "def bar := 1"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.header.len(), 2);
        assert_eq!(spec.header[0].content, "import Foo");
        assert_eq!(spec.header[1].content, "def bar := 1");
        assert!(!spec.requires.is_present());
    }

    #[test]
    fn test_hermes_spec_body_parse_strict_keywords() {
        let lines = mk_lines(&[
            "requires_foo a",
            "ensuresbar",
            "proof_of_concept",
            "axiomatic",
            "  requires   ", // valid keyword
            "   genuine requirements ",
        ]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        // The first four are headers because they don't match keywords strictly.
        assert_eq!(spec.header.len(), 4);
        assert_eq!(spec.header[0].content, "requires_foo a");
        assert_eq!(spec.header[1].content, "ensuresbar");
        assert_eq!(spec.header[2].content, "proof_of_concept");
        assert_eq!(spec.header[3].content, "axiomatic");

        // "  requires   " switches section but adds no lines because its arg is empty.
        // Following line is added verbatim to requires section.
        assert_eq!(spec.requires.lines.len(), 1);
        assert_eq!(spec.requires.lines[0].content, "   genuine requirements ");
        assert!(!spec.ensures.is_present());
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
        assert!(spec.header.is_empty());

        assert_eq!(spec.requires.lines.len(), 2);
        // Prefix argument keeps its exact text post-"requires" (which is " a > 0").
        assert_eq!(spec.requires.lines[0].content, " a > 0");
        // Continuation line keeps full exact original text.
        assert_eq!(spec.requires.lines[1].content, "  and b < 0");

        assert_eq!(spec.ensures.lines.len(), 1);
        assert_eq!(spec.ensures.lines[0].content, " c == 1");

        assert_eq!(spec.proof.lines.len(), 1);
        assert_eq!(spec.proof.lines[0].content, "  trivial");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_same_section() {
        // Check that it can interleave sections or repeat them
        let lines = mk_lines(&["requires a", "ensures b", "requires c", "axiom d"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.lines.len(), 2);
        assert_eq!(spec.requires.lines[0].content, " a");
        assert_eq!(spec.requires.lines[1].content, " c");

        assert_eq!(spec.ensures.lines.len(), 1);
        assert_eq!(spec.ensures.lines[0].content, " b");

        assert_eq!(spec.axiom.lines.len(), 1);
        assert_eq!(spec.axiom.lines[0].content, " d");
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
        let lines = vec![
            dummy_line("open Aeneas"),
            dummy_line("requires"),
            dummy_line("  x > 0"),
            dummy_line("    && y > 0"),
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.header.len(), 1);
        assert_eq!(spec.requires.lines.len(), 2);
        assert_eq!(spec.requires.lines[0].content, "  x > 0");
    }

    #[test]
    fn test_parse_spec_inline_args_valid() {
        let lines = vec![
            dummy_line("requires a > 0"),
            dummy_line("ensures\tb > 0"), // Tests tab whitespace
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.lines.len(), 1);
        assert_eq!(spec.requires.lines[0].content, " a > 0");
        assert_eq!(spec.ensures.lines.len(), 1);
        assert_eq!(spec.ensures.lines[0].content, "\tb > 0");
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
        assert_eq!(spec.requires.lines.len(), 3); // 2 content lines + 1 blank line
    }

    #[test]
    fn test_parse_spec_header_no_indent_rules() {
        let lines = vec![
            dummy_line("no indent"),
            dummy_line("    four spaces"),
            dummy_line("back to zero"),
            dummy_line("requires x"),
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.header.len(), 3);
        assert_eq!(spec.requires.lines.len(), 1);
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
        let lines = vec![
            dummy_line("  requires"), // baseline is 2
            dummy_line(" a > 0"),     // indent is 1 (1 <= 2)
        ];
        let err = RawHermesSpecBody::parse(&lines).unwrap_err();
        assert!(err.1.contains("Invalid indentation"));
    }

    #[test]
    fn test_parse_from_attrs_not_hermes() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```lean"]), parse_quote!(#[doc = " ```"])];
        let block_func = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap();
        assert!(block_func.is_none());
        let block_item = TypeHermesBlock::parse_from_attrs(&attrs).unwrap();
        assert!(block_item.is_none());
    }

    #[test]
    fn test_type_block_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isValid"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TypeHermesBlock::parse_from_attrs(&attrs).unwrap().unwrap();
        assert_eq!(block.is_valid.len(), 1);
        assert_eq!(block.is_valid[0].content, "  val == true");
    }

    #[test]
    fn test_trait_block_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let block = TraitHermesBlock::parse_from_attrs(&attrs).unwrap().unwrap();
        assert_eq!(block.is_safe.len(), 1);
        assert_eq!(block.is_safe[0].content, "  val == true");
    }

    #[test]
    fn test_type_block_missing_is_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isVaild"]),
            parse_quote!(#[doc = "  val == true"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TypeHermesBlock::parse_from_attrs(&attrs).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Hermes blocks on types must define an `isValid` type invariant. Did you misspell it?"
        );
    }

    #[test]
    fn test_trait_block_missing_is_safe() {
        let attrs: Vec<syn::Attribute> =
            vec![parse_quote!(#[doc = " ```hermes"]), parse_quote!(#[doc = " ```"])];
        let err = TraitHermesBlock::parse_from_attrs(&attrs).unwrap_err();
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
        let err = FunctionHermesBlock::parse_from_attrs(&attrs).unwrap_err();
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
        let err = TypeHermesBlock::parse_from_attrs(&attrs).unwrap_err();
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
        let err = TypeHermesBlock::parse_from_attrs(&attrs).unwrap_err();
        assert_eq!(err.to_string(), "`isSafe` sections are only permitted on traits.");
    }
    #[test]
    fn test_empty_section_is_present() {
        let lines = mk_lines(&["requires", "  x > 0", "ensures"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(spec.requires.is_present());
        assert!(spec.ensures.is_present());
        assert!(spec.ensures.lines.is_empty());
    }

    #[test]
    fn test_trait_rejects_is_valid() {
        let attrs: Vec<syn::Attribute> = vec![
            parse_quote!(#[doc = " ```hermes"]),
            parse_quote!(#[doc = " isSafe my_trait"]),
            parse_quote!(#[doc = " isValid foo"]),
            parse_quote!(#[doc = " ```"]),
        ];
        let err = TraitHermesBlock::parse_from_attrs(&attrs).unwrap_err();
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

        let err = TypeHermesBlock::parse_from_attrs(&attrs).unwrap_err();

        let (_, requires_span) = extract_doc_line(&requires_attr).unwrap();
        assert_eq!(format!("{:?}", err.span()), format!("{:?}", requires_span));
    }
}

impl<M: ThreadSafety> LiftToSafe for SpannedLine<M> {
    type Target = SpannedLine<Safe>;
    fn lift(self) -> Self::Target {
        SpannedLine { content: self.content, span: self.span, raw_span: self.raw_span.lift() }
    }
}

impl<M: ThreadSafety> LiftToSafe for HermesBlockCommon<M> {
    type Target = HermesBlockCommon<Safe>;
    fn lift(self) -> Self::Target {
        HermesBlockCommon {
            header: self.header.into_iter().map(|l| l.lift()).collect(),
            content_span: self.content_span.lift(),
            start_span: self.start_span.lift(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionBlockInner<M> {
    type Target = FunctionBlockInner<Safe>;
    fn lift(self) -> Self::Target {
        match self {
            Self::Proof(v) => FunctionBlockInner::Proof(v.into_iter().map(|l| l.lift()).collect()),
            Self::Axiom(v) => FunctionBlockInner::Axiom(v.into_iter().map(|l| l.lift()).collect()),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for FunctionHermesBlock<M> {
    type Target = FunctionHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        FunctionHermesBlock {
            common: self.common.lift(),
            requires: self.requires.into_iter().map(|l| l.lift()).collect(),
            ensures: self.ensures.into_iter().map(|l| l.lift()).collect(),
            inner: self.inner.lift(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TypeHermesBlock<M> {
    type Target = TypeHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        TypeHermesBlock {
            common: self.common.lift(),
            is_valid: self.is_valid.into_iter().map(|l| l.lift()).collect(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for TraitHermesBlock<M> {
    type Target = TraitHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        TraitHermesBlock {
            common: self.common.lift(),
            is_safe: self.is_safe.into_iter().map(|l| l.lift()).collect(),
        }
    }
}

impl<M: ThreadSafety> LiftToSafe for ImplHermesBlock<M> {
    type Target = ImplHermesBlock<Safe>;
    fn lift(self) -> Self::Target {
        ImplHermesBlock { common: self.common.lift() }
    }
}
