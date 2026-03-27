use chumsky::{inspector::SimpleState, prelude::*};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum SectionType {
    Context,
    Requires,
    Ensures,
    ProofContext,
    Proof,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum SectionHeader<'a> {
    Section { typ: SectionType, name: Option<&'a str> },
    IsValid { arg: &'a str },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Section<'a> {
    header: SectionHeader<'a>,
    content: &'a str,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum AttrArg {
    Axiom,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Attr<'a> {
    arg: Option<AttrArg>,
    sections: Vec<Section<'a>>,
}

type ParserError<'a> = extra::Full<Rich<'a, char>, extra::SimpleState<usize>, ()>;

fn inline_ws<'a>() -> impl Parser<'a, &'a str, (), ParserError<'a>> {
    just(' ').repeated().ignored()
}

fn ident<'a>() -> impl Parser<'a, &'a str, &'a str, ParserError<'a>> {
    let first_char = any().filter(|c: &char| c.is_alphabetic() || *c == '_');
    let rest_chars =
        any().filter(|c: &char| c.is_alphanumeric() || *c == '_' || *c == '\'').repeated();

    first_char.then(rest_chars).to_slice()
}

/// A helper that wraps any content parser in balanced backticks.
fn code_block<'a, P, O>(content_parser: P) -> impl Parser<'a, &'a str, O, ParserError<'a>>
where
    P: Parser<'a, &'a str, O, ParserError<'a>>,
    O: 'a,
{
    let open_backticks = just('`').repeated().at_least(3).count();

    let close_backticks = just('`').repeated().count().try_map_with(|count, e| {
        let (expected, _): &(usize, O) = e.ctx();
        let expected = *expected;
        if count == expected {
            Ok(())
        } else {
            Err(Rich::custom(
                e.span(),
                format!("Expected {} backticks to close the block, found {}", expected, count),
            ))
        }
    });

    open_backticks
        .then(content_parser)
        .then_with_ctx(close_backticks)
        .map(|((_open_count, content), _)| content)
}

impl SectionType {
    fn parser<'a>() -> impl Parser<'a, &'a str, SectionType, ParserError<'a>> {
        let proof_context = just("proof")
            .then_ignore(inline_ws())
            .ignore_then(just("context"))
            .to(SectionType::ProofContext);

        let single_keyword = any()
            .filter(|c: &char| c.is_ascii_alphabetic())
            .repeated()
            .at_least(1)
            .to_slice()
            .try_map(|s: &str, span| match s {
                "context" => Ok(SectionType::Context),
                "requires" => Ok(SectionType::Requires),
                "ensures" => Ok(SectionType::Ensures),
                "proof" => Ok(SectionType::Proof),
                _ => Err(Rich::custom(span, format!("Unknown section type: '{}'", s))),
            });

        choice((proof_context, single_keyword))
    }
}

impl<'a> SectionHeader<'a> {
    fn parser() -> impl Parser<'a, &'a str, SectionHeader<'a>, ParserError<'a>> {
        let is_valid = just("isValid")
            .then_ignore(inline_ws())
            .ignore_then(ident())
            .then_ignore(inline_ws())
            .then_ignore(just(':'))
            .map(|arg| SectionHeader::IsValid { arg });

        let kw_with_id = SectionType::parser()
            .then_ignore(inline_ws())
            .then_ignore(just('('))
            .then_ignore(inline_ws())
            .then(ident())
            .then_ignore(inline_ws())
            .then_ignore(just(')'))
            .then_ignore(inline_ws())
            .then_ignore(just(':'))
            .map(|(typ, name)| SectionHeader::Section { typ, name: Some(name) });

        let kw_only = SectionType::parser()
            .then_ignore(inline_ws())
            .then_ignore(just(':'))
            .map(|typ| SectionHeader::Section { typ, name: None });

        just(' ').ignore_then(choice((is_valid, kw_with_id, kw_only)))
    }
}

impl<'a> Section<'a> {
    fn parser() -> impl Parser<'a, &'a str, Section<'a>, ParserError<'a>> {
        fn content_line<'a>() -> impl Parser<'a, &'a str, (), ParserError<'a>> {
            let indented = just("  ")
                .ignore_then(none_of("\r\n").repeated().ignored())
                .then_ignore(just('\r').or_not().then(just('\n')))
                .ignored();

            let empty =
                just(' ').or_not().then_ignore(just('\r').or_not().then(just('\n'))).ignored();

            choice((indented, empty))
        }

        SectionHeader::parser()
            .then_ignore(inline_ws())
            .then(
                // To be zero-copy, we capture the inline content AND the
                // subsequent indented lines as a single contiguous slice.
                none_of("\r\n")
                    .repeated()
                    .ignored()
                    .then_ignore(just('\r').or_not().then(just('\n')))
                    .then_ignore(content_line().repeated())
                    .to_slice(),
            )
            .map(|(hdr, content)| Section { header: hdr, content })
    }
}

impl<'a> Attr<'a> {
    fn parser() -> impl Parser<'a, &'a str, Attr<'a>, ParserError<'a>> {
        let doc_strings = none_of("\r\n")
            .repeated()
            .to_slice()
            .try_map(|s: &str, span| {
                let mut parts = s.split(',').map(str::trim);

                // Scan for the `hermes` token.
                let mut found_hermes = false;
                for part in parts.by_ref() {
                    if part == "hermes" {
                        found_hermes = true;
                        break;
                    }
                }

                if !found_hermes {
                    return Err(Rich::custom(span, "Not a hermes code block"));
                }

                // Once we've found the `hermes` token, all subsequent tokens
                // are parsed as arguments.
                let mut parsed_arg = None;

                for part in parts {
                    if part.is_empty() {
                        continue;
                    }

                    // Reject if we already found an argument.
                    if parsed_arg.is_some() {
                        return Err(Rich::custom(
                            span,
                            "Multiple hermes attribute arguments are not allowed; expected only one (e.g., `unsafe(axiom)`)",
                        ));
                    }

                    match part {
                        "unsafe(axiom)" => parsed_arg = Some(AttrArg::Axiom),
                        "axiom" => {
                            return Err(Rich::custom(
                                span,
                                "Use `unsafe(axiom)` instead of `axiom`",
                            ))
                        }
                        _ => {
                            return Err(Rich::custom(
                                span,
                                format!("Invalid hermes attribute argument: '{}'", part),
                            ))
                        }
                    }
                }

                // Default to `Spec` if nothing was provided after `hermes`.
                Ok(parsed_arg)
            })
            .then_ignore(just('\r').or_not().then(just('\n')));

        let content_parser = doc_strings
            .then(Section::parser().repeated().collect::<Vec<Section<'a>>>())
            .map(|(arg, sections)| Attr { arg, sections });

        code_block(content_parser)
    }

    pub fn multi_parser() -> impl Parser<'a, &'a str, Vec<Attr<'a>>, ParserError<'a>> {
        let attr_block = Attr::parser().map(Some);

        let non_attr_block = {
            let non_hermes_doc_strings = none_of("\r\n")
                .repeated()
                .to_slice()
                .try_map(|s: &str, span| {
                    let is_hermes = s.split(',').map(str::trim).any(|part| part == "hermes");
                    if is_hermes {
                        // If it *is* a hermes block, forcefully fail this path.
                        // This guarantees the sliding window falls through and
                        // Chumsky bubbles up the actual syntax error from
                        // `Attr::parser()`.
                        Err(Rich::custom(span, "Expected non-hermes block"))
                    } else {
                        Ok(())
                    }
                })
                .then_ignore(just('\r').or_not().then(just('\n')));

            // Consume characters until we hit 3 or more backticks.
            let block_content =
                any().and_is(just('`').repeated().at_least(3).not()).repeated().ignored();

            let content_parser = non_hermes_doc_strings.ignore_then(block_content).to(None);

            code_block(content_parser)
        };

        let non_block = {
            let open_backticks_lookahead = just('`').repeated().at_least(3);
            open_backticks_lookahead
                .not()
                .ignore_then(any()) // Only consume the char if it's not the start of a code block.
                .to(None)
        };

        choice((attr_block, non_attr_block, non_block))
            .repeated()
            .collect::<Vec<Option<Attr<'a>>>>()
            .map(|blocks: Vec<Option<Attr<'a>>>| blocks.into_iter().flatten().collect())
            .then_ignore(end())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_parse {
        ([$parser:expr] $src:expr => Ok($expected:expr)) => {{ assert_eq!($parser.parse($src).into_result(), Ok($expected)) }};
        ([$parser:expr] $src:expr => Err($expected:expr)) => {{
            let err = $parser.parse($src).into_result().unwrap_err();
            let expected = $expected;
            let expected: &dyn std::any::Any = &expected;
            let expected = if let Some(expected) = expected.downcast_ref::<&'static str>() {
                expected.to_string()
            } else {
                format!("{:?}", expected)
            };
            assert_eq!(format!("{:?}", err), expected)
        }};
        ([$parser:expr] $src:expr => $expected:expr, $expected_rest:expr) => {{
            let test_parser = (&$parser).then(any().repeated().to_slice());
            assert_eq!(test_parser.parse($src).into_result(), Ok(($expected, $expected_rest)))
        }};
    }

    #[test]
    fn test_ident() {
        let parser = ident();

        // Single-character.
        assert_parse!([parser] "x" => Ok("x"));
        assert_parse!([parser] "_" => Ok("_"));

        // Multi-character.
        assert_parse!([parser] "x_'0" => Ok("x_'0"));
        assert_parse!([parser] "_x_'0" => Ok("_x_'0"));
        assert_parse!([parser] "_'0" => Ok("_'0"));

        // Invalid.
        assert_parse!([parser] "" => Err("[found end of input at 0..0 expected any]"));
        assert_parse!([parser] "0" => Err("[found ''0'' at 0..1 expected something else]"));
        assert_parse!([parser] "0x" => Err("[found ''0'' at 0..1 expected something else]"));
        assert_parse!([parser] "'" => Err("[found ''\\''' at 0..1 expected something else]"));
        assert_parse!([parser] "'x" => Err("[found ''\\''' at 0..1 expected something else]"));
    }

    #[test]
    fn test_section_type() {
        let parser = SectionType::parser();

        assert_parse!([parser] "context" => Ok(SectionType::Context));
        assert_parse!([parser] "requires" => Ok(SectionType::Requires));
        assert_parse!([parser] "ensures" => Ok(SectionType::Ensures));
        assert_parse!([parser] "proof" => Ok(SectionType::Proof));
        assert_parse!([parser] "proof context" => Ok(SectionType::ProofContext));
        assert_parse!([parser] "foo" => Err("[Unknown section type: 'foo' at 0..1]"));
        assert_parse!([parser] "" => Err("[found end of input at 0..0 expected ''p'', or any]"));

        assert_parse!([parser] "context:" => SectionType::Context, ":");
        assert_parse!([parser] "requires:" => SectionType::Requires, ":");
        assert_parse!([parser] "ensures:" => SectionType::Ensures, ":");
        assert_parse!([parser] "proof:" => SectionType::Proof, ":");
        assert_parse!([parser] "proof context:" => SectionType::ProofContext, ":");

        assert_parse!([parser] "context (foo):" => SectionType::Context, " (foo):");
        assert_parse!([parser] "requires (foo):" => SectionType::Requires, " (foo):");
        assert_parse!([parser] "ensures (foo):" => SectionType::Ensures, " (foo):");
        assert_parse!([parser] "proof (foo):" => SectionType::Proof, " (foo):");
        assert_parse!([parser] "proof context (foo):" => SectionType::ProofContext, " (foo):");
    }

    #[test]
    fn test_section_header() {
        use SectionHeader::*;
        use SectionType::*;

        let parser = SectionHeader::<'static>::parser();

        assert_parse!([parser] " context:" => Ok(Section { typ: Context, name: None }));
        assert_parse!([parser] " requires:" => Ok(Section { typ: Requires, name: None }));
        assert_parse!([parser] " requires (foo):" => Ok(Section { typ: Requires, name: Some("foo") }));
        assert_parse!([parser] " isValid foo :" => Ok(SectionHeader::IsValid { arg: "foo" }));

        // No leading space.
        assert_parse!([parser] "context:" => Err("[found ''c'' at 0..1 expected '' '']"));

        // Argument not in parens.
        assert_parse!([parser] " requires foo:" => Err("[found ''f'' at 10..11 expected '' '', ''('', or '':'']"));

        // While `proof context` is a valid section type, `proof ctx` is not.
        //
        // TODO: This error is confusing. We should probably say something
        // closer to "expected literal `context`".
        assert_parse!([parser] " proof context:" => Ok(Section { typ: SectionType::ProofContext, name: None }));
        assert_parse!([parser] " proof ctx:" => Err("[found ''t'' at 8..9 expected ''o'']"));

        // A named argument to `context` or `proof context` is always
        // syntactically valid, although semantically invalid (we reject it
        // later, after initial parsing).
        assert_parse!([parser] " context (foo):" => Ok(Section { typ: SectionType::Context, name: Some("foo") }));
        assert_parse!([parser] " proof context (foo):" => Ok(Section { typ: SectionType::ProofContext, name: Some("foo") }));

        // No argument to `isValid`.
        assert_parse!([parser] " isValid:" => Err("[found '':'' at 8..9 expected '' '', or something else]"));
        assert_parse!([parser] " isValid :" => Err("[found '':'' at 9..10 expected '' '', or something else]"));

        // Argument to `isValid` in parens.
        assert_parse!([parser] " isValid (foo):" => Err("[found ''('' at 9..10 expected '' '', or something else]"));
    }

    #[test]
    fn test_section() {
        use SectionType::*;

        let parser = Section::<'static>::parser();

        assert_parse!([parser] " context:\n  x = 1\n  y = 2\n" => Ok(Section { header: SectionHeader::Section { typ: Context, name: None }, content: "\n  x = 1\n  y = 2\n" }));
        // When the subsequent `requires:` is single-indented, it is considered
        // to be a separate section.
        assert_parse!([parser] " context:\n requires:" => Section { header: SectionHeader::Section { typ: Context, name: None }, content: "\n" }, " requires:");
        // When the subsequent `requires:` is double-indented, it is considered
        // to be part of the `context:` section.
        assert_parse!([parser] " context:\n  requires:\n" => Section { header: SectionHeader::Section { typ: Context, name: None }, content: "\n  requires:\n" }, "");
    }

    #[test]
    fn test_attr_parser() {
        let parser = Attr::parser();

        assert_parse!([parser] "```hermes\n```" => Ok(Attr { arg: None, sections: vec![] }));
        assert_parse!([parser] "```hermes, unsafe(axiom)\n```" => Ok(Attr { arg: Some(AttrArg::Axiom), sections: vec![] }));

        // Irregular whitespace and trailing commas.
        assert_parse!([parser] "```  hermes ,  unsafe(axiom),,  \n```" => Ok(Attr { arg: Some(AttrArg::Axiom), sections: vec![] }));

        // Higher backtick counts (balanced).
        assert_parse!([parser] "````hermes\n````" => Ok(Attr { arg: None, sections: vec![] }));

        // With nested sections.
        let with_sections = "```hermes\n context:\n  x = 1\n```";
        assert_parse!([parser] with_sections => Ok(Attr {
            arg: None,
            sections: vec![Section {
                header: SectionHeader::Section { typ: SectionType::Context, name: None },
                content: "\n  x = 1\n"
            }]
        }));

        assert_parse!([parser] "```rust\n```" => Err("[Not a hermes code block at 3..4]"));
        assert_parse!([parser] "```hermes, foo\n```" => Err("[Invalid hermes attribute argument: 'foo' at 3..4]"));
        assert_parse!([parser] "```hermes, axiom\n```" => Err("[Use `unsafe(axiom)` instead of `axiom` at 3..4]"));
        assert_parse!([parser] "```hermes, unsafe(axiom), unsafe(axiom)\n```" => Err("[Multiple hermes attribute arguments are not allowed; expected only one (e.g., `unsafe(axiom)`) at 3..4]"));
        // Mismatched backticks (open 3, close 4).
        assert_parse!([parser] "```hermes\n````" => Err("[Expected 3 backticks to close the block, found 4 at 10..11]"));
        // Mismatched backticks (open 4, close 3).
        assert_parse!([parser] "````hermes\n```" => Err("[Expected 4 backticks to close the block, found 3 at 11..12]"));
    }

    #[test]
    fn test_attr_multi_parser() {
        let parser = Attr::multi_parser();

        assert_parse!([parser] "" => Ok(vec![]));
        assert_parse!([parser] "Some normal documentation text." => Ok(vec![]));
        assert_parse!([parser] "```rust\nfn main() {}\n```" => Ok(vec![]));

        // Interleaved valid content.
        let interleaved = "
        This is a file.
        ```rust
        code
        ```
        ```hermes, unsafe(axiom)
         context:
        ```
        More text.
        ";
        assert_parse!([parser] interleaved => Ok(vec![Attr {
            arg: Some(AttrArg::Axiom),
            sections: vec![Section {
                header: SectionHeader::Section { typ: SectionType::Context, name: None },
                content: "\n"
            }]
        }]));

        // A malformed hermes block should not be swallowed as text/ignored.
        let broken_hermes = "
        Some text.
        ```hermes, bad_arg
        ```
        ";
        assert_parse!([parser] broken_hermes => Err("[Invalid hermes attribute argument: 'bad_arg' at 39..46]"));

        // A syntax error inside a section of a hermes block.
        let broken_section = "
        ```hermes
         invalid_section_header:
        ```
        ";
        assert_parse!([parser] broken_section => Err("[Unknown section type: 'invalid_section_header' at 19..41]"));
    }
}
