use chumsky::{
    prelude::*,
    text::{inline_whitespace, newline, whitespace},
};

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

#[derive(Clone, Debug, PartialEq, Eq)]
enum Chunk<'a> {
    Text(&'a str),
    CodeBlock { doc_string: &'a str, content: &'a str },
}

type ParserError<'a> = extra::Full<Rich<'a, char>, extra::SimpleState<usize>, ()>;

fn ident<'a>() -> impl Parser<'a, &'a str, &'a str, ParserError<'a>> {
    let first_char = any().filter(|c: &char| c.is_alphabetic() || *c == '_');
    let rest_chars =
        any().filter(|c: &char| c.is_alphanumeric() || *c == '_' || *c == '\'').repeated();

    first_char.then(rest_chars).to_slice()
}

fn keyword<'a>() -> impl Parser<'a, &'a str, &'a str, ParserError<'a>> {
    any().filter(|c: &char| c.is_ascii_alphabetic()).repeated().at_least(1).to_slice()
}

fn specific_keyword<'a>(k: &str) -> impl Parser<'a, &'a str, (), ParserError<'a>> {
    keyword().try_map(move |s: &str, span| {
        if s == k {
            Ok(())
        } else {
            Err(Rich::custom(span, format!("Expected '{}', found '{}'", k, s)))
        }
    })
}

/// Extracts the `(doc_string, content)` of a single code block.
fn code_block<'a>() -> impl Parser<'a, &'a str, (&'a str, &'a str), ParserError<'a>> {
    let backticks = just('`').repeated().at_least(3).count();

    let close_backticks = just('`').repeated().count().try_map_with(|count, e| {
        let expected: &usize = e.ctx();
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

    backticks
        .then_with_ctx({
            let doc_string = none_of("\r\n").repeated().to_slice().then_ignore(newline());

            let content =
                any().and_is(just('`').repeated().at_least(3).not()).repeated().to_slice();

            doc_string.then(content).then_ignore(close_backticks)
        })
        .map(|(_count, (doc_string, content))| (doc_string, content))
}

// impl SectionType {
//     fn parser<'a>() -> impl Parser<'a, &'a str, SectionType, ParserError<'a>> {
//         let leading_keywords = keyword().separated_by(inline_whitespace()).at_least(1).collect::<Vec<_>>();

//         let optional_parens = inline_whitespace()
//             .ignore_then(just('('))
//             .ignore_then(inline_whitespace())
//             .ignore_then(ident())
//             .then_ignore(inline_whitespace())
//             .then_ignore(just(')'))
//             .or_not();

//         // let proof_context = specific_keyword("proof")
//         //     .then_ignore(inline_whitespace())
//         //     .ignore_then(specific_keyword("context"))
//         //     .to(SectionType::ProofContext);

//         // let single_keyword = keyword().try_map(|s: &str, span| match s {
//         //     "context" => Ok(SectionType::Context),
//         //     "requires" => Ok(SectionType::Requires),
//         //     "ensures" => Ok(SectionType::Ensures),
//         //     "proof" => Ok(SectionType::Proof),
//         //     _ => Err(Rich::custom(span, format!("Unknown section type: '{}'", s))),
//         // });

//         // choice((single_keyword, proof_context))
//     }
// }

impl<'a> SectionHeader<'a> {
    fn parser() -> impl Parser<'a, &'a str, SectionHeader<'a>, ParserError<'a>> {
        let leading_keywords =
            keyword().separated_by(inline_whitespace()).at_least(1).collect::<Vec<_>>();

        let optional_parens = inline_whitespace()
            .ignore_then(just('('))
            .ignore_then(inline_whitespace())
            .ignore_then(ident())
            .then_ignore(inline_whitespace())
            .then_ignore(just(')'))
            .or_not();

        just(' ')
            .ignore_then(leading_keywords)
            .then(optional_parens)
            .then_ignore(inline_whitespace())
            .then_ignore(just(':'))
            .try_map(|(words, parens_arg), span| {
                match (words.as_slice(), parens_arg) {
                    (["isValid", arg], None) => Ok(SectionHeader::IsValid { arg }),
                    (["isValid"], None) => Err(Rich::custom(
                        span,
                        "isValid requires an argument (e.g., 'isValid foo:')",
                    )),
                    (["isValid", ..], Some(_)) => {
                        Err(Rich::custom(span, "isValid does not take parentheses"))
                    }
                    (["isValid", ..], _) => {
                        Err(Rich::custom(span, "isValid takes exactly one argument"))
                    }

                    (["proof", "context"], arg) => {
                        Ok(SectionHeader::Section { typ: SectionType::ProofContext, name: arg })
                    }
                    (["proof", other], _) => Err(Rich::custom(
                        span,
                        format!("Expected 'context' after 'proof', found '{}'", other),
                    )),

                    (["context"], arg) => {
                        Ok(SectionHeader::Section { typ: SectionType::Context, name: arg })
                    }
                    (["requires"], arg) => {
                        Ok(SectionHeader::Section { typ: SectionType::Requires, name: arg })
                    }
                    (["ensures"], arg) => {
                        Ok(SectionHeader::Section { typ: SectionType::Ensures, name: arg })
                    }
                    (["proof"], arg) => {
                        Ok(SectionHeader::Section { typ: SectionType::Proof, name: arg })
                    }

                    // Catch likely typos and provide helpful error messages.
                    ([kw, arg], None)
                        if matches!(*kw, "context" | "requires" | "ensures" | "proof") =>
                    {
                        Err(Rich::custom(
                            span,
                            format!("Argument '{}' to '{}' must be in parentheses", arg, kw),
                        ))
                    }

                    ([other], _) => {
                        Err(Rich::custom(span, format!("Unknown section type: '{}'", other)))
                    }
                    _ => Err(Rich::custom(span, "Invalid section header format")),
                }
            })

        // let is_valid = specific_keyword("isValid")
        //     .then_ignore(inline_whitespace())
        //     .ignore_then(ident())
        //     .then_ignore(inline_whitespace())
        //     .then_ignore(just(':'))
        //     .map(|arg| SectionHeader::IsValid { arg });

        // let kw_with_id = SectionType::parser()
        //     .then_ignore(inline_whitespace())
        //     .then_ignore(just('('))
        //     .then_ignore(inline_whitespace())
        //     .then(ident())
        //     .then_ignore(inline_whitespace())
        //     .then_ignore(just(')'))
        //     .then_ignore(inline_whitespace())
        //     .then_ignore(just(':'))
        //     .map(|(typ, name)| SectionHeader::Section { typ, name: Some(name) });

        // let kw_only = SectionType::parser()
        //     .then_ignore(inline_whitespace())
        //     .then_ignore(just(':'))
        //     .map(|typ| SectionHeader::Section { typ, name: None });

        // just(' ').ignore_then(choice((is_valid, kw_with_id, kw_only)))
    }
}

impl<'a> Section<'a> {
    fn parser() -> impl Parser<'a, &'a str, Section<'a>, ParserError<'a>> {
        fn content_line<'a>() -> impl Parser<'a, &'a str, (), ParserError<'a>> {
            let indented = just("  ")
                .ignore_then(none_of("\r\n").repeated().ignored())
                .then_ignore(newline())
                .ignored();

            let empty = just(' ').or_not().then_ignore(newline()).ignored();

            choice((indented, empty))
        }

        SectionHeader::parser()
            .then_ignore(inline_whitespace())
            .then(
                // To be zero-copy, we capture the inline content AND the
                // subsequent indented lines as a single contiguous slice.
                none_of("\r\n")
                    .repeated()
                    .ignored()
                    .then_ignore(newline())
                    .then_ignore(content_line().repeated())
                    .to_slice(),
            )
            .map(|(hdr, content)| Section { header: hdr, content })
    }
}

impl<'a> Attr<'a> {
    fn doc_string_parser() -> impl Parser<'a, &'a str, Option<AttrArg>, ParserError<'a>> {
        none_of(",\r\n")
            .repeated()
            .to_slice()
            .map_with(|s: &str, e| (s.trim(), e.span()))
            .separated_by(just(','))
            .allow_trailing()
            .collect::<Vec<_>>()
            .try_map(|tokens: Vec<(&str, _)>, span| {
                // Find the position of the first `hermes` token.
                let hermes_pos = tokens.iter().position(|&(s, _)| s == "hermes").ok_or(Rich::custom(span, "Not a hermes code block"))?;
                // Only validate tokens after `hermes`.
                tokens.iter()
                    .skip(hermes_pos + 1)
                    .filter(|(part, _)| !part.is_empty())
                    .try_fold(None, |parsed_arg, &(part, ref tok_span)| {
                        if parsed_arg.is_some() {
                            return Err(Rich::custom(
                                *tok_span,
                                "Multiple hermes attribute arguments are not allowed; expected only one (e.g., `unsafe(axiom)`)",
                            ));
                        }

                        match part {
                            "unsafe(axiom)" => Ok(Some(AttrArg::Axiom)),
                            "axiom" => Err(Rich::custom(
                                *tok_span,
                                "Use `unsafe(axiom)` instead of `axiom`",
                            )),
                            _ => Err(Rich::custom(
                                *tok_span,
                                format!("Invalid hermes attribute argument: '{}'", part),
                            )),
                        }
                    })
            })
    }

    fn parse_inner(doc_string: &'a str, content: &'a str) -> Result<Self, Rich<'a, char>> {
        let arg = Self::doc_string_parser()
            .parse(doc_string)
            .into_result()
            .map_err(|errs| errs.into_iter().next().unwrap())?;

        let sections = Section::parser()
            .repeated()
            .collect::<Vec<_>>()
            .parse(content)
            .into_result()
            .map_err(|errs| errs.into_iter().next().unwrap())?;

        Ok(Attr { arg, sections })
    }

    /// Parses a single `hermes` code block. Fails if the block is not a
    /// `hermes` block.
    fn parser() -> impl Parser<'a, &'a str, Attr<'a>, ParserError<'a>> {
        code_block().try_map(|(doc_string, content), span| {
            let is_hermes = doc_string.split(',').map(str::trim).any(|part| part == "hermes");

            if !is_hermes {
                return Err(Rich::custom(span, "Not a hermes code block"));
            }

            Self::parse_inner(doc_string, content)
        })
    }

    /// Parses an entire document, extracting all `hermes` blocks and ignoring
    /// everything else.
    fn multi_parser() -> impl Parser<'a, &'a str, Vec<Attr<'a>>, ParserError<'a>> {
        Chunk::parser().then_ignore(whitespace()).repeated().collect::<Vec<_>>().try_map(
            |chunks, _span| {
                let mut attrs = Vec::new();

                for chunk in chunks {
                    if let Chunk::CodeBlock { doc_string, content } = chunk {
                        let is_hermes =
                            doc_string.split(',').map(str::trim).any(|part| part == "hermes");

                        // Only attempt to parse if it is explicitly a hermes block
                        if is_hermes {
                            attrs.push(Self::parse_inner(doc_string, content)?);
                        }
                    }
                }

                Ok(attrs)
            },
        )
    }
}

impl<'a> Chunk<'a> {
    fn parser() -> impl Parser<'a, &'a str, Chunk<'a>, ParserError<'a>> {
        let open_backticks = just('`').repeated().at_least(3).count();
        let close_backticks = just('`').repeated().count().try_map_with(|count, e| {
            let expected: &usize = e.ctx();
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

        let code_block = open_backticks
            .then_with_ctx({
                // Capture the doc string line.
                let doc_string = none_of("\r\n").repeated().to_slice().then_ignore(newline());

                // Capture all contents until the closing backticks.
                let content =
                    any().and_is(just('`').repeated().at_least(3).not()).repeated().to_slice();

                doc_string.then(content).then_ignore(close_backticks)
            })
            .map(|(_count, (doc_string, content))| Chunk::CodeBlock { doc_string, content });

        let text = any()
            .and_is(just('`').repeated().at_least(3).not())
            .repeated()
            .at_least(1)
            .ignored()
            .to_slice()
            .map(Chunk::Text);

        choice((code_block, text))
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
        use SectionHeader::*;
        use SectionType::*;

        let parser = SectionHeader::<'static>::parser();

        assert_parse!([parser] " context:" => Ok(Section { typ: Context, name: None }));
        assert_parse!([parser] " requires:" => Ok(Section { typ: Requires, name: None }));
        assert_parse!([parser] " ensures:" => Ok(Section { typ: Ensures, name: None }));
        assert_parse!([parser] " proof:" => Ok(Section { typ: Proof, name: None }));
        assert_parse!([parser] " proof context:" => Ok(Section { typ: ProofContext, name: None }));
        assert_parse!([parser] " foo:" => Err("[Unknown section type: 'foo' at 0..5]"));
        assert_parse!([parser] "" => Err("[found end of input at 0..0 expected '' '']"));
        assert_parse!([parser] " " => Err("[found end of input at 1..1 expected any]"));

        assert_parse!([parser] " context (foo):" => Ok(Section { typ: Context, name: Some("foo") }));
        assert_parse!([parser] " requires (foo):" => Ok(Section { typ: Requires, name: Some("foo") }));
        assert_parse!([parser] " ensures (foo):" => Ok(Section { typ: Ensures, name: Some("foo") }));
        assert_parse!([parser] " proof (foo):" => Ok(Section { typ: Proof, name: Some("foo") }));
        assert_parse!([parser] " proof context (foo):" => Ok(Section { typ: ProofContext, name: Some("foo") }));
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
        assert_parse!([parser] " requires foo:" => Err("[Argument 'foo' to 'requires' must be in parentheses at 0..14]"));

        // While `proof context` is a valid section type, `proof ctx` is not.
        //
        // TODO: This error is confusing. We should probably say something
        // closer to "expected literal `context`".
        assert_parse!([parser] " proof context:" => Ok(Section { typ: SectionType::ProofContext, name: None }));
        assert_parse!([parser] " proof ctx:" => Err("[Expected 'context' after 'proof', found 'ctx' at 0..11]"));

        // A named argument to `context` or `proof context` is always
        // syntactically valid, although semantically invalid (we reject it
        // later, after initial parsing).
        assert_parse!([parser] " context (foo):" => Ok(Section { typ: SectionType::Context, name: Some("foo") }));
        assert_parse!([parser] " proof context (foo):" => Ok(Section { typ: SectionType::ProofContext, name: Some("foo") }));

        // No argument to `isValid`.
        assert_parse!([parser] " isValid:" => Err("[isValid requires an argument (e.g., 'isValid foo:') at 0..9]"));
        assert_parse!([parser] " isValid :" => Err("[isValid requires an argument (e.g., 'isValid foo:') at 0..10]"));

        // Argument to `isValid` in parens.
        assert_parse!([parser] " isValid (foo):" => Err("[isValid does not take parentheses at 0..15]"));
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

        assert_parse!([parser] "```rust\n```" => Err("[Not a hermes code block at 0..11]"));
        assert_parse!([parser] "```hermes, foo\n```" => Err("[Invalid hermes attribute argument: 'foo' at 7..11]"));
        assert_parse!([parser] "```hermes, axiom\n```" => Err("[Use `unsafe(axiom)` instead of `axiom` at 7..13]"));
        assert_parse!([parser] "```hermes, unsafe(axiom), unsafe(axiom)\n```" => Err("[Multiple hermes attribute arguments are not allowed; expected only one (e.g., `unsafe(axiom)`) at 22..36]"));
        // Mismatched backticks (open 3, close 4).
        assert_parse!([parser] "```hermes\n````" => Err("[Expected 3 backticks to close the block, found 4 at 10..14]"));
        // Mismatched backticks (open 4, close 3).
        assert_parse!([parser] "````hermes\n```" => Err("[Expected 4 backticks to close the block, found 3 at 11..14]"));
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
 More text.";
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
        assert_parse!([parser] broken_hermes => Err("[Invalid hermes attribute argument: 'bad_arg' at 7..15]"));

        // A syntax error inside a section of a hermes block.
        let broken_section = "
        ```hermes
            invalid_section_header:
        ```
        ";
        assert_parse!([parser] broken_section => Err("[found '' '' at 1..2 expected something else]"));
    }
}
