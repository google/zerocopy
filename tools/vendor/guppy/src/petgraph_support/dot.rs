// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use petgraph::{
    prelude::*,
    visit::{GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable, NodeRef},
};
use std::fmt::{self, Write};

static INDENT: &str = "    ";

/// A visitor interface for formatting graph labels.
pub trait DotVisitor<NR, ER> {
    /// Visits this node. The implementation may output a label for this node to the given
    /// `DotWrite`.
    fn visit_node(&self, node: NR, f: &mut DotWrite<'_, '_>) -> fmt::Result;

    /// Visits this edge. The implementation may output a label for this edge to the given
    /// `DotWrite`.
    fn visit_edge(&self, edge: ER, f: &mut DotWrite<'_, '_>) -> fmt::Result;

    // TODO: allow more customizations? more labels, colors etc to be set?
}

/// A visitor for formatting graph labels that outputs `fmt::Display` impls for node and edge
/// weights.
///
/// This visitor will escape backslashes.
#[derive(Copy, Clone, Debug)]
#[allow(dead_code)]
pub struct DisplayVisitor;

impl<NR, ER> DotVisitor<NR, ER> for DisplayVisitor
where
    NR: NodeRef,
    ER: EdgeRef,
    NR::Weight: fmt::Display,
    ER::Weight: fmt::Display,
{
    fn visit_node(&self, node: NR, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        write!(f, "{}", node.weight())
    }

    fn visit_edge(&self, edge: ER, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        write!(f, "{}", edge.weight())
    }
}

impl<NR, ER, T> DotVisitor<NR, ER> for &T
where
    T: DotVisitor<NR, ER>,
{
    fn visit_node(&self, node: NR, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        (*self).visit_node(node, f)
    }

    fn visit_edge(&self, edge: ER, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        (*self).visit_edge(edge, f)
    }
}

#[derive(Clone, Debug)]
pub struct DotFmt<G, V> {
    graph: G,
    visitor: V,
}

impl<G, V> DotFmt<G, V>
where
    for<'a> &'a G: IntoEdgeReferences + IntoNodeReferences + GraphProp + NodeIndexable,
    for<'a> V:
        DotVisitor<<&'a G as IntoNodeReferences>::NodeRef, <&'a G as IntoEdgeReferences>::EdgeRef>,
{
    /// Creates a new formatter for this graph.
    #[allow(dead_code)]
    pub fn new(graph: G, visitor: V) -> Self {
        Self { graph, visitor }
    }

    /// Outputs a graphviz-compatible representation of this graph to the given formatter.
    pub fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{} {{", graph_type(&self.graph))?;

        for node in self.graph.node_references() {
            write!(
                f,
                "{}{} [label=\"",
                INDENT,
                (&self.graph).to_index(node.id())
            )?;
            self.visitor.visit_node(node, &mut DotWrite::new(f))?;
            writeln!(f, "\"]")?;
        }

        let edge_str = edge_str(&self.graph);
        for edge in self.graph.edge_references() {
            write!(
                f,
                "{}{} {} {} [label=\"",
                INDENT,
                (&self.graph).to_index(edge.source()),
                edge_str,
                (&self.graph).to_index(edge.target())
            )?;
            self.visitor.visit_edge(edge, &mut DotWrite::new(f))?;
            writeln!(f, "\"]")?;
        }

        writeln!(f, "}}")
    }
}

impl<G, V> fmt::Display for DotFmt<G, V>
where
    for<'a> &'a G: IntoEdgeReferences + IntoNodeReferences + GraphProp + NodeIndexable,
    for<'a> V:
        DotVisitor<<&'a G as IntoNodeReferences>::NodeRef, <&'a G as IntoEdgeReferences>::EdgeRef>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt(f)
    }
}

/// A write target for `Dot` graphs. Use with the `write!` macro.
pub struct DotWrite<'a, 'b> {
    f: &'a mut fmt::Formatter<'b>,
    escape_backslashes: bool,
}

impl<'a, 'b> DotWrite<'a, 'b> {
    fn new(f: &'a mut fmt::Formatter<'b>) -> Self {
        Self {
            f,
            escape_backslashes: true,
        }
    }

    /// Sets a config option for whether backslashes should be escaped. Defaults to `true`.
    ///
    /// This can be set to `false` if the visitor knows to output graphviz control characters.
    #[allow(dead_code)]
    pub fn set_escape_backslashes(&mut self, escape_backslashes: bool) {
        self.escape_backslashes = escape_backslashes;
    }

    /// Glue for usage of the `write!` macro.
    ///
    /// This method should generally not be invoked manually, but rather through `write!` or similar
    /// macros (`println!`, `format!` etc).
    ///
    /// Defining this inherent method allows `write!` to work without callers needing to import the
    /// `std::fmt::Write` trait.
    pub fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        // Forward to the fmt::Write impl.
        Write::write_fmt(self, args)
    }
}

impl Write for DotWrite<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for c in s.chars() {
            self.write_char(c)?;
        }
        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        match c {
            '"' => self.f.write_str(r#"\""#),
            // \l is for left-justified newlines (\n means center-justified newlines)
            '\n' => self.f.write_str(r"\l"),
            // Backslashes are only escaped if the config is set.
            '\\' if self.escape_backslashes => self.f.write_str(r"\\"),
            // Other escapes like backslashes are passed through.
            c => self.f.write_char(c),
        }
    }
}

fn graph_type<G: GraphProp>(graph: G) -> &'static str {
    if graph.is_directed() {
        "digraph"
    } else {
        "graph"
    }
}

fn edge_str<G: GraphProp>(graph: G) -> &'static str {
    if graph.is_directed() { "->" } else { "--" }
}
