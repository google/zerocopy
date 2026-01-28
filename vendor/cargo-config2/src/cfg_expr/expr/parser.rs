// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::cfg_expr::{
    error::{ParseError, Reason},
    expr::{
        ExprNode, Expression, Func, InnerPredicate,
        lexer::{Lexer, Token},
    },
};

impl Expression {
    /// Given a cfg() expression (the cfg( and ) are optional), attempts to
    /// parse it into a form where it can be evaluated
    pub(crate) fn parse(original: &str) -> Result<Self, ParseError> {
        #[derive(Debug)]
        struct FuncAndSpan {
            func: Func,
            parens_index: usize,
            span: core::ops::Range<usize>,
            predicates: Vec<InnerPredicate>,
            nest_level: u8,
        }

        let lexer = Lexer::new(original);

        // The lexer automatically trims any cfg( ), so reacquire
        // the string before we start walking tokens
        let original = lexer.inner;

        let mut func_stack: Vec<FuncAndSpan> = Vec::with_capacity(5);
        let mut expr_queue = Vec::with_capacity(5);

        // Keep track of the last token to simplify validation of the token stream
        let mut last_token: Option<Token<'_>> = None;

        let parse_predicate = |key: (&str, core::ops::Range<usize>),
                               val: Option<(&str, core::ops::Range<usize>)>|
         -> Result<InnerPredicate, ParseError> {
            let span = key.1;
            Ok(InnerPredicate { identifier: span, value: val.map(|(_, span)| span) })
        };

        macro_rules! token_err {
            ($span:expr) => {{
                let expected: &[&str] = match last_token {
                    None => &["<key>", "all", "any", "not"],
                    Some(Token::All | Token::Any | Token::Not) => &["("],
                    Some(Token::CloseParen) => &[")", ","],
                    Some(Token::Comma) => &[")", "<key>"],
                    Some(Token::Equals) => &["\""],
                    Some(Token::Key(_)) => &["=", ",", ")"],
                    Some(Token::Value(_)) => &[",", ")"],
                    Some(Token::OpenParen) => &["<key>", ")", "all", "any", "not"],
                };

                return Err(ParseError {
                    original: original.to_owned(),
                    span: $span,
                    reason: Reason::Unexpected(&expected),
                });
            }};
        }

        let mut pred_key: Option<(&str, _)> = None;
        let mut pred_val: Option<(&str, _)> = None;

        let mut root_predicate_count = 0;

        // Basic implementation of the https://en.wikipedia.org/wiki/Shunting-yard_algorithm
        'outer: for lt in lexer {
            let lt = lt?;
            match &lt.token {
                Token::Key(k) => {
                    if matches!(last_token, None | Some(Token::OpenParen | Token::Comma)) {
                        pred_key = Some((k, lt.span.clone()));
                    } else {
                        token_err!(lt.span)
                    }
                }
                Token::Value(v) => {
                    if matches!(last_token, Some(Token::Equals)) {
                        // We only record the span for keys and values
                        // so that the expression doesn't need a lifetime
                        // but in the value case we need to strip off
                        // the quotes so that the proper raw string is
                        // provided to callers when evaluating the expression
                        pred_val = Some((v, lt.span.start + 1..lt.span.end - 1));
                    } else {
                        token_err!(lt.span)
                    }
                }
                Token::Equals => {
                    if !matches!(last_token, Some(Token::Key(_))) {
                        token_err!(lt.span)
                    }
                }
                Token::All | Token::Any | Token::Not => {
                    if matches!(last_token, None | Some(Token::OpenParen | Token::Comma)) {
                        let new_fn = match lt.token {
                            // the 0 is a dummy value -- it will be substituted for the real
                            // number of predicates in the `CloseParen` branch below.
                            Token::All => Func::All(0),
                            Token::Any => Func::Any(0),
                            Token::Not => Func::Not,
                            _ => unreachable!(),
                        };

                        if let Some(fs) = func_stack.last_mut() {
                            fs.nest_level += 1;
                        }

                        func_stack.push(FuncAndSpan {
                            func: new_fn,
                            span: lt.span,
                            parens_index: 0,
                            predicates: vec![],
                            nest_level: 0,
                        });
                    } else {
                        token_err!(lt.span)
                    }
                }
                Token::OpenParen => {
                    if matches!(last_token, Some(Token::All | Token::Any | Token::Not)) {
                        if let Some(ref mut fs) = func_stack.last_mut() {
                            fs.parens_index = lt.span.start;
                        }
                    } else {
                        token_err!(lt.span)
                    }
                }
                Token::CloseParen => {
                    if matches!(
                        last_token,
                        None | Some(Token::All | Token::Any | Token::Not | Token::Equals)
                    ) {
                        token_err!(lt.span)
                    }
                    if let Some(top) = func_stack.pop() {
                        let key = pred_key.take();
                        let val = pred_val.take();

                        let num_predicates =
                            top.predicates.len() + key.is_some() as usize + top.nest_level as usize;

                        let func = match top.func {
                            Func::All(_) => Func::All(num_predicates),
                            Func::Any(_) => Func::Any(num_predicates),
                            Func::Not => {
                                // not() doesn't take a predicate list, but only a single predicate,
                                // so ensure we have exactly 1
                                if num_predicates != 1 {
                                    return Err(ParseError {
                                        original: original.to_owned(),
                                        span: top.span.start..lt.span.end,
                                        reason: Reason::InvalidNot(num_predicates),
                                    });
                                }

                                Func::Not
                            }
                        };

                        for pred in top.predicates {
                            expr_queue.push(ExprNode::Predicate(pred));
                        }

                        if let Some(key) = key {
                            let inner_pred = parse_predicate(key, val)?;
                            expr_queue.push(ExprNode::Predicate(inner_pred));
                        }

                        expr_queue.push(ExprNode::Fn(func));

                        // This is the only place we go back to the top of the outer loop,
                        // so make sure we correctly record this token
                        last_token = Some(Token::CloseParen);
                        continue 'outer;
                    }

                    // We didn't have an opening parentheses if we get here
                    return Err(ParseError {
                        original: original.to_owned(),
                        span: lt.span,
                        reason: Reason::UnopenedParens,
                    });
                }
                Token::Comma => {
                    if matches!(
                        last_token,
                        None | Some(
                            Token::OpenParen | Token::All | Token::Any | Token::Not | Token::Equals
                        )
                    ) {
                        token_err!(lt.span)
                    }
                    let key = pred_key.take();
                    let val = pred_val.take();

                    let inner_pred = key.map(|key| parse_predicate(key, val)).transpose()?;

                    match (inner_pred, func_stack.last_mut()) {
                        (Some(pred), Some(func)) => {
                            func.predicates.push(pred);
                        }
                        (Some(pred), None) => {
                            root_predicate_count += 1;

                            expr_queue.push(ExprNode::Predicate(pred));
                        }
                        _ => {}
                    }
                }
            }

            last_token = Some(lt.token);
        }

        if let Some(Token::Equals) = last_token {
            return Err(ParseError {
                original: original.to_owned(),
                span: original.len()..original.len(),
                reason: Reason::Unexpected(&["\"<value>\""]),
            });
        }

        // If we still have functions on the stack, it means we have an unclosed parens
        if let Some(top) = func_stack.pop() {
            if top.parens_index == 0 {
                Err(ParseError {
                    original: original.to_owned(),
                    span: top.span,
                    reason: Reason::Unexpected(&["("]),
                })
            } else {
                Err(ParseError {
                    original: original.to_owned(),
                    span: top.parens_index..original.len(),
                    reason: Reason::UnclosedParens,
                })
            }
        } else {
            let key = pred_key.take();
            let val = pred_val.take();

            if let Some(key) = key {
                root_predicate_count += 1;
                expr_queue.push(ExprNode::Predicate(parse_predicate(key, val)?));
            }

            if expr_queue.is_empty() {
                Err(ParseError {
                    original: original.to_owned(),
                    span: 0..original.len(),
                    reason: Reason::Empty,
                })
            } else if root_predicate_count > 1 {
                Err(ParseError {
                    original: original.to_owned(),
                    span: 0..original.len(),
                    reason: Reason::MultipleRootPredicates,
                })
            } else {
                Ok(Expression { original: original.to_owned(), expr: expr_queue })
            }
        }
    }
}
