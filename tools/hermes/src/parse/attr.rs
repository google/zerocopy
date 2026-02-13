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
pub struct FunctionHermesBlock {
    pub common: HermesBlockCommon,
    pub requires: Vec<SpannedLine>,
    pub ensures: Vec<SpannedLine>,
    pub inner: FunctionBlockInner,
}

#[derive(Debug, Clone)]
pub enum FunctionBlockInner {
    Proof(Vec<SpannedLine>),
    Axiom(Vec<SpannedLine>),
}

/// A parsed Hermes documentation block attached to a type or trait.
#[derive(Debug, Clone)]
pub struct ItemHermesBlock {
    pub common: HermesBlockCommon,
}

#[derive(Debug, Clone)]
pub struct HermesBlockCommon {
    pub header: Vec<SpannedLine>,
    /// The span of the entire block, including the opening and closing ` ``` `
    /// lines.
    pub content_span: Span,
    /// The span of the opening ` ``` ` line.
    pub start_span: Span,
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
    let second_arg = tokens.next();
    match (first_arg, second_arg) {
        (Some(first), Some(second)) => {
            return Err(format!(
                "Multiple attributes specified after 'hermes' ('{first}', '{second}'). Only one attribute is allowed."
            ));
        }
        (None, None) => return Ok(Some(ParsedInfoString::GenericMode)),
        (Some("spec"), None) => {
            return Ok(Some(ParsedInfoString::FunctionMode(FunctionAttribute::Spec)));
        }
        (Some("unsafe(axiom)"), None) => {
            return Ok(Some(ParsedInfoString::FunctionMode(FunctionAttribute::UnsafeAxiom)));
        }
        (Some(token), None) if token.starts_with("unsafe") => {
            return Err(format!(
                "Unknown or malformed attribute: '{token}'. Did you mean 'unsafe(axiom)'?"
            ));
        }
        (Some(token), None) => {
            return Err(format!(
                "Unrecognized Hermes attribute: '{token}'. Supported attributes are 'spec', 'unsafe(axiom)'."
            ));
        }
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
        Meta::NameValue(MetaNameValue {
            value: Expr::Lit(ExprLit { lit: Lit::Str(s), .. }),
            ..
        }) => Some((s.value(), s.span())),
        _ => None,
    }
}

// Common parsing logic extracted
fn parse_block_lines<'a, I>(
    iter: &mut I,
    start: Span,
) -> Result<(String, Vec<SpannedLine>, Span), Error>
where
    I: Iterator<Item = &'a Attribute>,
{
    let mut content = String::new();
    let mut lines = Vec::new();
    let mut end = start;
    let mut closed = false;

    for next in iter {
        let Some((line, span)) = extract_doc_line(next) else { break };

        if line.trim().starts_with("```") {
            closed = true;
            break;
        }

        content.push_str(&line);
        content.push('\n');
        lines.push(SpannedLine { content: line, span: span_to_miette(span), raw_span: span });
        end = span;
    }

    if !closed {
        return Err(Error::new(start, "Unclosed Hermes block in documentation."));
    }

    Ok((content, lines, end))
}

fn parse_hermes_block_common(
    attrs: &[Attribute],
    check_info: impl Fn(&ParsedInfoString, Span) -> Result<(), Error>,
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

        check_info(&parsed_info, start)?;

        if block.is_some() {
            return Err(Error::new(start, "Multiple Hermes blocks found on a single item."));
        }

        let (_, lines, end) = parse_block_lines(&mut iter, start)?;

        let body = match RawHermesSpecBody::parse(&lines) {
            Ok(body) => body,
            Err((err_span, msg)) => {
                let raw_span =
                    lines.iter().find(|l| l.span == err_span).map(|l| l.raw_span).unwrap_or(start);
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

impl FunctionHermesBlock {
    pub fn parse_from_attrs(attrs: &[Attribute]) -> Result<Option<Self>, Error> {
        let Some((item, parsed_info)) = parse_hermes_block_common(attrs, |_, _| Ok(()))? else {
            return Ok(None);
        };

        let attribute = match parsed_info {
            ParsedInfoString::FunctionMode(attr) => attr,
            ParsedInfoString::GenericMode => FunctionAttribute::Spec, // Implicit `spec` for functions
        };

        let body = item.body;
        if !body.axiom.is_empty() && attribute != FunctionAttribute::UnsafeAxiom {
            return Err(Error::new(
                body.axiom[0].raw_span,
                "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
            ));
        } else if !body.proof.is_empty() && attribute != FunctionAttribute::Spec {
            return Err(Error::new(
                body.proof[0].raw_span,
                "`proof` sections are only permitted on `spec` functions.",
            ));
        }

        let content_span = item.content_span;
        let start_span = item.start_span;
        let block = match attribute {
            FunctionAttribute::Spec => {
                if !body.axiom.is_empty() {
                    return Err(Error::new(
                        body.axiom[0].raw_span,
                        "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
                    ));
                }
                Self {
                    common: HermesBlockCommon { header: body.header, content_span, start_span },
                    requires: body.requires,
                    ensures: body.ensures,
                    inner: FunctionBlockInner::Proof(body.proof),
                }
            }
            FunctionAttribute::UnsafeAxiom => {
                if !body.proof.is_empty() {
                    return Err(Error::new(
                        body.proof[0].raw_span,
                        "`proof` sections are only permitted on `spec` functions.",
                    ));
                }
                Self {
                    common: HermesBlockCommon { header: body.header, content_span, start_span },
                    requires: body.requires,
                    ensures: body.ensures,
                    inner: FunctionBlockInner::Axiom(body.axiom),
                }
            }
        };

        Ok(Some(block))
    }
}

impl ItemHermesBlock {
    pub fn parse_from_attrs(attrs: &[Attribute]) -> Result<Option<Self>, Error> {
        let Some((item, _)) = parse_hermes_block_common(attrs, |parsed_info, start| {
            match parsed_info {
                ParsedInfoString::FunctionMode(_) => Err(Error::new(
                    start,
                    "This item does not support Hermes attributes (like `spec` or `unsafe(axiom)`). Only generic `hermes` blocks are allowed.",
                )),
                ParsedInfoString::GenericMode => Ok(()),
            }
        })?
        else {
            return Ok(None);
        };

        let body = item.body;
        if !body.requires.is_empty() {
            return Err(Error::new(
                body.requires[0].raw_span,
                "`requires` sections are only permitted on functions.",
            ));
        }
        if !body.ensures.is_empty() {
            return Err(Error::new(
                body.ensures[0].raw_span,
                "`ensures` sections are only permitted on functions.",
            ));
        }
        if !body.proof.is_empty() {
            return Err(Error::new(
                body.proof[0].raw_span,
                "`proof` sections are only permitted on `spec` functions.",
            ));
        }
        if !body.axiom.is_empty() {
            return Err(Error::new(
                body.axiom[0].raw_span,
                "`axiom` sections are only permitted on `unsafe(axiom)` functions.",
            ));
        }

        Ok(Some(Self {
            common: HermesBlockCommon {
                header: body.header,
                content_span: item.content_span,
                start_span: item.start_span,
            },
        }))
    }
}

/// A single parsed line from a documentation block, retaining structural layout info.
#[derive(Debug, Clone)]
pub struct SpannedLine {
    pub content: String,
    pub span: SourceSpan,
    pub raw_span: Span,
}

/// The structured content of a completely unvalidated Hermes specification block.
#[derive(Debug, Default, Clone)]
pub(super) struct RawHermesSpecBody {
    /// Content before any keyword (e.g., Lean imports, let bindings, type invariants)
    pub(super) header: Vec<SpannedLine>,
    pub(super) requires: Vec<SpannedLine>,
    pub(super) ensures: Vec<SpannedLine>,
    pub(super) proof: Vec<SpannedLine>,
    pub(super) axiom: Vec<SpannedLine>,
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
        I: IntoIterator<Item = &'a SpannedLine>,
    {
        let mut spec = RawHermesSpecBody::default();

        #[derive(Debug, Clone, Copy, PartialEq)]
        enum Section {
            Header,
            Requires,
            Ensures,
            Proof,
            Axiom,
        }
        let mut current_section = Section::Header;
        let mut baseline_indent: Option<usize> = None;

        fn get_vec(section: Section, spec: &mut RawHermesSpecBody) -> &mut Vec<SpannedLine> {
            match section {
                Section::Header => &mut spec.header,
                Section::Requires => &mut spec.requires,
                Section::Ensures => &mut spec.ensures,
                Section::Proof => &mut spec.proof,
                Section::Axiom => &mut spec.axiom,
            }
        }

        // Matches exact keywords or keywords followed by any whitespace.
        fn starts_with_keyword(line: &str, keyword: &str) -> bool {
            if let Some(rest) = line.strip_prefix(keyword) {
                rest.is_empty() || rest.starts_with(char::is_whitespace)
            } else {
                false
            }
        }

        let keywords = [
            ("requires", Section::Requires),
            ("ensures", Section::Ensures),
            ("proof", Section::Proof),
            ("axiom", Section::Axiom),
        ];

        for line in lines {
            let trimmed = line.content.trim();
            let span = line.span;
            let raw_span = line.raw_span;

            if trimmed.is_empty() {
                get_vec(current_section, &mut spec).push(SpannedLine {
                    content: line.content.clone(),
                    span,
                    raw_span,
                });
                continue;
            }

            let indent = line.content.len() - line.content.trim_start().len();

            if let Some(&(keyword, section)) =
                keywords.iter().find(|(k, _)| starts_with_keyword(trimmed, k))
            {
                current_section = section;
                baseline_indent = Some(indent);
                if let Some(arg) = trimmed.strip_prefix(keyword) {
                    if !arg.trim().is_empty() {
                        get_vec(current_section, &mut spec).push(SpannedLine {
                            content: arg.to_string(),
                            span,
                            raw_span,
                        });
                    }
                }
                continue;
            }

            if current_section != Section::Header {
                if indent <= baseline_indent.unwrap() {
                    return Err((
                        span,
                        "Invalid indentation: expected an indented continuation or a valid Hermes keyword (requires, ensures, proof, axiom). Did you misspell a keyword?".to_string()
                    ));
                }
            }
            // Not a new keyword; continuation of the current section.
            get_vec(current_section, &mut spec).push(SpannedLine {
                content: line.content.clone(),
                span,
                raw_span,
            });
        }

        Ok(spec)
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
                raw_span: proc_macro2::Span::call_site(),
            })
            .collect()
    }

    #[test]
    fn test_hermes_spec_body_parse_empty() {
        let lines = mk_lines(&[]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert!(spec.header.is_empty());
        assert!(spec.requires.is_empty());
        assert!(spec.ensures.is_empty());
        assert!(spec.proof.is_empty());
        assert!(spec.axiom.is_empty());
    }

    #[test]
    fn test_hermes_spec_body_parse_header_only() {
        let lines = mk_lines(&["import Foo", "def bar := 1"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.header.len(), 2);
        assert_eq!(spec.header[0].content, "import Foo");
        assert_eq!(spec.header[1].content, "def bar := 1");
        assert!(spec.requires.is_empty());
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
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].content, "   genuine requirements ");
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
        assert!(spec.header.is_empty());

        assert_eq!(spec.requires.len(), 2);
        // Prefix argument keeps its exact text post-"requires" (which is " a > 0").
        assert_eq!(spec.requires[0].content, " a > 0");
        // Continuation line keeps full exact original text.
        assert_eq!(spec.requires[1].content, "  and b < 0");

        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].content, " c == 1");

        assert_eq!(spec.proof.len(), 1);
        assert_eq!(spec.proof[0].content, "  trivial");
    }

    #[test]
    fn test_hermes_spec_body_parse_multiple_same_section() {
        // Check that it can interleave sections or repeat them
        let lines = mk_lines(&["requires a", "ensures b", "requires c", "axiom d"]);
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.requires[0].content, " a");
        assert_eq!(spec.requires[1].content, " c");

        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].content, " b");

        assert_eq!(spec.axiom.len(), 1);
        assert_eq!(spec.axiom[0].content, " d");
    }

    fn dummy_line(content: &str) -> SpannedLine {
        SpannedLine {
            content: content.to_string(),
            span: (0, 0).into(),
            raw_span: Span::call_site(),
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
        assert_eq!(spec.requires.len(), 2);
        assert_eq!(spec.requires[0].content, "  x > 0");
    }

    #[test]
    fn test_parse_spec_inline_args_valid() {
        let lines = vec![
            dummy_line("requires a > 0"),
            dummy_line("ensures\tb > 0"), // Tests tab whitespace
        ];
        let spec = RawHermesSpecBody::parse(&lines).unwrap();
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.requires[0].content, " a > 0");
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.ensures[0].content, "\tb > 0");
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
        assert_eq!(spec.requires.len(), 3); // 2 content lines + 1 blank line
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
        assert_eq!(spec.requires.len(), 1);
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
        let block_item = ItemHermesBlock::parse_from_attrs(&attrs).unwrap();
        assert!(block_item.is_none());
    }
}
