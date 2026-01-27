// SPDX-License-Identifier: Apache-2.0 OR MIT

pub(crate) mod lexer;
mod parser;

use core::ops::Range;

/// A predicate function, used to combine 1 or more predicates
/// into a single value
#[derive(Debug, Clone, Copy)]
enum Func {
    /// `not()` with a configuration predicate. It is true if its predicate
    /// is false and false if its predicate is true.
    Not,
    /// `all()` with a comma separated list of configuration predicates. It
    /// is false if at least one predicate is false. If there are no predicates,
    /// it is true.
    ///
    /// The associated `usize` is the number of predicates inside the `all()`.
    All(usize),
    /// `any()` with a comma separated list of configuration predicates. It
    /// is true if at least one predicate is true. If there are no predicates,
    /// it is false.
    ///
    /// The associated `usize` is the number of predicates inside the `any()`.
    Any(usize),
}

/// A single predicate in a `cfg()` expression
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Predicate<'a> {
    /// A generic bare predicate key that doesn't match one of the known options, eg `cfg(bare)`
    Flag(&'a str),
    /// A generic key = "value" predicate that doesn't match one of the known options, eg `cfg(foo = "bar")`
    KeyValue { key: &'a str, val: &'a str },
}

#[derive(Clone, Debug)]
struct InnerPredicate {
    identifier: Range<usize>,
    value: Option<Range<usize>>,
}

impl InnerPredicate {
    fn to_pred<'a>(&self, s: &'a str) -> Predicate<'a> {
        match &self.value {
            Some(vs) => {
                Predicate::KeyValue { key: &s[self.identifier.clone()], val: &s[vs.clone()] }
            }
            None => Predicate::Flag(&s[self.identifier.clone()]),
        }
    }
}

#[derive(Clone, Debug)]
enum ExprNode {
    Fn(Func),
    Predicate(InnerPredicate),
}

/// A parsed `cfg()` expression that can evaluated
#[derive(Clone, Debug)]
pub(crate) struct Expression {
    expr: Vec<ExprNode>,
    // We keep the original string around for providing the arbitrary
    // strings that can make up an expression
    original: String,
}

impl Expression {
    #[cfg(test)]
    /// An iterator over each predicate in the expression
    pub(crate) fn predicates(&self) -> impl Iterator<Item = Predicate<'_>> {
        self.expr.iter().filter_map(move |item| match item {
            ExprNode::Predicate(pred) => {
                let pred = pred.clone().to_pred(&self.original);
                Some(pred)
            }
            ExprNode::Fn(_) => None,
        })
    }

    /// Evaluates the expression, using the provided closure to determine the value of
    /// each predicate, which are then combined into a final result depending on the
    /// functions not(), all(), or any() in the expression.
    ///
    /// `eval_predicate` typically returns `bool`, but may return any type that implements
    /// the `Logic` trait.
    pub(crate) fn eval<EP, T>(&self, mut eval_predicate: EP) -> T
    where
        EP: FnMut(&Predicate<'_>) -> T,
        T: Logic + core::fmt::Debug,
    {
        let mut result_stack = Vec::with_capacity(8);

        // We store the expression as postfix, so just evaluate each license
        // requirement in the order it comes, and then combining the previous
        // results according to each operator as it comes
        for node in &self.expr {
            match node {
                ExprNode::Predicate(pred) => {
                    let pred = pred.to_pred(&self.original);

                    result_stack.push(eval_predicate(&pred));
                }
                ExprNode::Fn(Func::All(count)) => {
                    // all() with a comma separated list of configuration predicates.
                    let mut result = T::top();

                    for _ in 0..*count {
                        let r = result_stack.pop().unwrap();
                        result = result.and(r);
                    }

                    result_stack.push(result);
                }
                ExprNode::Fn(Func::Any(count)) => {
                    // any() with a comma separated list of configuration predicates.
                    let mut result = T::bottom();

                    for _ in 0..*count {
                        let r = result_stack.pop().unwrap();
                        result = result.or(r);
                    }

                    result_stack.push(result);
                }
                ExprNode::Fn(Func::Not) => {
                    // not() with a configuration predicate.
                    // It is true if its predicate is false
                    // and false if its predicate is true.
                    let r = result_stack.pop().unwrap();
                    result_stack.push(r.not());
                }
            }
        }

        result_stack.pop().unwrap()
    }
}

/// A propositional logic used to evaluate `Expression` instances.
///
/// An `Expression` consists of some predicates and the `any`, `all` and `not` operators. An
/// implementation of `Logic` defines how the `any`, `all` and `not` operators should be evaluated.
pub(crate) trait Logic {
    /// The result of an `all` operation with no operands, akin to Boolean `true`.
    fn top() -> Self;

    /// The result of an `any` operation with no operands, akin to Boolean `false`.
    fn bottom() -> Self;

    /// `AND`, which corresponds to the `all` operator.
    fn and(self, other: Self) -> Self;

    /// `OR`, which corresponds to the `any` operator.
    fn or(self, other: Self) -> Self;

    /// `NOT`, which corresponds to the `not` operator.
    fn not(self) -> Self;
}

/// A boolean logic.
impl Logic for bool {
    #[inline]
    fn top() -> Self {
        true
    }

    #[inline]
    fn bottom() -> Self {
        false
    }

    #[inline]
    fn and(self, other: Self) -> Self {
        self && other
    }

    #[inline]
    fn or(self, other: Self) -> Self {
        self || other
    }

    #[inline]
    fn not(self) -> Self {
        !self
    }
}

/// A three-valued logic -- `None` stands for the value being unknown.
///
/// The truth tables for this logic are described on
/// [Wikipedia](https://en.wikipedia.org/wiki/Three-valued_logic#Kleene_and_Priest_logics).
impl Logic for Option<bool> {
    #[inline]
    fn top() -> Self {
        Some(true)
    }

    #[inline]
    fn bottom() -> Self {
        Some(false)
    }

    #[inline]
    fn and(self, other: Self) -> Self {
        match (self, other) {
            // If either is false, the expression is false.
            (Some(false), _) | (_, Some(false)) => Some(false),
            // If both are true, the expression is true.
            (Some(true), Some(true)) => Some(true),
            // One or both are unknown -- the result is unknown.
            _ => None,
        }
    }

    #[inline]
    fn or(self, other: Self) -> Self {
        match (self, other) {
            // If either is true, the expression is true.
            (Some(true), _) | (_, Some(true)) => Some(true),
            // If both are false, the expression is false.
            (Some(false), Some(false)) => Some(false),
            // One or both are unknown -- the result is unknown.
            _ => None,
        }
    }

    #[inline]
    fn not(self) -> Self {
        self.map(|v| !v)
    }
}
