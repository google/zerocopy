// This file serves as the core test case for various module resolution
// strategies supported by Rust and the Hermes parser.
//
// We include a variety of module structures to ensure that Charon correctly
// spans the file tree during extraction.

// `mod foo;` -> `foo.rs`
pub mod foo;

// `mod bar;` -> `bar/mod.rs`
pub mod bar;

// Test inline modules, which define their contents directly within the syntax
// tree rather than reading from an external file, to verify that lexical
// scope boundaries are correctly processed natively.
pub mod baz {
    /// ```lean, hermes
    /// ```
    pub fn inline() {}
}

// The `#[path]` attribute allows codebases to override standard layouts and map
// modules to arbitrary files.
//
// We verify this behavior because complex builds often redirect module
// resolution to generated files or non-standard directories.
#[path = "sys/unix.rs"]
pub mod sys;

// Nested modules inherently push the directory context deeper.
//
// We verify nested resolution to confirm that path discovery stacks correctly
// navigate deep filesystem layers.
pub mod a;

// It is possible for identical files to be loaded through multiple logical
// module identifiers.
//
// We test loading the same physical file twice to verify that the compiler
// deduplicates or properly isolates identical source definitions mapped from
// multiple points.
pub mod c;
#[path = "c.rs"]
pub mod d;

// Modules can explicitly map to completely disparate paths outside the crate
// root.
//
// We verify external path dependencies to ensure the analyzer's sandbox
// boundaries safely permit and resolve upward traversals beyond the immediate
// project root.
#[path = "../extra.rs"]
pub mod extra;

/// ```lean, hermes
/// ```
pub fn root_dummy() {}
