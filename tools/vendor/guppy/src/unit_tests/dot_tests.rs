// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::petgraph_support::dot::{DisplayVisitor, DotFmt, DotVisitor, DotWrite};
use petgraph::{
    prelude::*,
    visit::{EdgeRef, NodeRef},
};
use std::fmt;

#[test]
fn dot_fmt() {
    let mut graph = Graph::new();
    let a = graph.add_node("A");
    // " is escaped.
    let b = graph.add_node(r#"B1"B2"#);
    // \ is escaped by DisplayVisitor but not by NoEscapeDisplayVisitor.
    let c = graph.add_node(r"C1\C2\\C3\lC4\nC5");
    // Newlines are converted into \l.
    let d = graph.add_node("D1\nD2");
    graph.add_edge(a, b, 100);
    graph.add_edge(a, c, 200);
    graph.add_edge(b, d, 300);
    graph.add_edge(c, d, 400);

    let dot_fmt = DotFmt::new(&graph, DisplayVisitor);
    let output = format!("{dot_fmt}");
    static EXPECTED_DOT: &str = r#"digraph {
    0 [label="A"]
    1 [label="B1\"B2"]
    2 [label="C1\\C2\\\\C3\\lC4\\nC5"]
    3 [label="D1\lD2"]
    0 -> 1 [label="100"]
    0 -> 2 [label="200"]
    1 -> 3 [label="300"]
    2 -> 3 [label="400"]
}
"#;
    assert_eq!(&output, EXPECTED_DOT, "dot output matches");

    let no_escape_dot_fmt = DotFmt::new(&graph, NoEscapeDisplayVisitor);
    let output = format!("{no_escape_dot_fmt}");
    static EXPECTED_DOT_NO_ESCAPE: &str = r#"digraph {
    0 [label="A"]
    1 [label="B1\"B2"]
    2 [label="C1\C2\\C3\lC4\nC5"]
    3 [label="D1\lD2"]
    0 -> 1 [label="100"]
    0 -> 2 [label="200"]
    1 -> 3 [label="300"]
    2 -> 3 [label="400"]
}
"#;
    assert_eq!(
        &output, EXPECTED_DOT_NO_ESCAPE,
        "dot output matches (backslashes not escaped)"
    );
}

/// A visitor for formatting graph labels that outputs `fmt::Display` impls for node and edge
/// weights.
///
/// This visitor does not escape backslashes.
#[derive(Copy, Clone, Debug)]
pub struct NoEscapeDisplayVisitor;

impl<NR, ER> DotVisitor<NR, ER> for NoEscapeDisplayVisitor
where
    NR: NodeRef,
    ER: EdgeRef,
    NR::Weight: fmt::Display,
    ER::Weight: fmt::Display,
{
    fn visit_node(&self, node: NR, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        f.set_escape_backslashes(false);
        write!(f, "{}", node.weight())
    }

    fn visit_edge(&self, edge: ER, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        f.set_escape_backslashes(false);
        write!(f, "{}", edge.weight())
    }
}
