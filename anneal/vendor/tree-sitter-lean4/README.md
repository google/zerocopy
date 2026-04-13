# Tree-Sitter-Lean4

Lean4 is a programming language, commonly used for mathematical theorem proving as a [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant).

This project contains a Lean parser definition:

- Tree-Sitter grammar for parsing [Lean 4](github.com/leanprover/lean4) source code.
- Tree-Sitter queries for usage in the modal text editor [Helix](https://helix-editor.vercel.app/).
- Rust library pushed to Crates.io for parsing Lean in a Rust program

**Important**: Lean is a very extensible language. Therefore, the Tree-Sitter grammar is of limited use. For parsing advanced Lean programs you will need to use the Lean kernel. See also [Metaprogramming in Lean](https://github.com/leanprover-community/lean4-metaprogramming-book).

## Usage

### Rust

Add this crate as a normal dependency in your `Cargo.toml` file.

```bash
cargo add tree-sitter-lean4
```

During the first build, you need these binaries in your path:

- C code generator `tree-sitter` (only if the `src/parser.c` is missing)
- C compiler `cc`

Then instantiate the parser:

```rust
use tree_sitter::{InputEdit, Language, Parser, Point};

let mut parser = Parser::new();
parser.set_language(&tree_sitter_lean4::LANGUAGE.into()).expect("Error loading Rust grammar");
```

See [Tree-Sitter-Rust](https://github.com/tree-sitter/tree-sitter/tree/master/lib/binding_rust).

### Nix Flake

This is the recommended approach for reproducible builds.

```nix
{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    tree-sitter-lean.url = "github:wvhulle/tree-sitter-lean";
  };

  outputs = { nixpkgs, tree-sitter-lean, ... }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      devShells.${system}.default = pkgs.mkShell {
        # If you want to use ast-grep (see next section)
        packages = [ pkgs.ast-grep ];
        shellHook = ''
          # Create a symlink in the working directory for easy access (add to .gitignore)
          ln -sf ${tree-sitter-lean.packages.${system}.grammar}/parser tree-sitter-lean.so
        '';
      };
    };
}
```

See [`nixpkgs` tree-sitter documentation](https://nixos.org/manual/nixpkgs/stable/#tree-sitter) for more Tree-Sitter with Nix examples.

Push build cache to public cache server:

```bash
nix build . --print-out-paths | cachix push wvhulle
```

## Development

Read [writing the grammar](https://tree-sitter.github.io/tree-sitter/creating-parsers/3-writing-the-grammar.html). Be careful of adding conflicts in the grammar as they cause exponential growth of the state space.

Use the `tree-sitter` CLI:

```bash
tree-sitter generate # Re-run this after every grammar rule change
tree-sitter parse Test.lean # A long Lean file that needs to be parsed correctly
```

## Tests

Add tests for the Tree-Sitter grammar to [./test/corpus](./test/corpus).

Tests are run with

```bash
tree-sitter test
```

Check the amount of failures with:

```bash
tree-sitter test --overview-only | grep ✗ | lines | length
```

Tests can be updated automatically when you change the grammar:

```bash
tree-sitter test --update
```

See [writing tests](https://tree-sitter.github.io/tree-sitter/creating-parsers/5-writing-tests.html)

You should also test the queries from `./queries`:

```bash
tree-sitter query higlights.scm Test.lean
```

This will report any errors such as incorrect node names in the query file.

## License

Based on <https://github.com/Julian/lean.nvim>. Grammar was completely rewritten to be simpler.

MIT
