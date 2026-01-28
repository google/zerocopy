[![Crates.io](https://img.shields.io/crates/v/cargo-readme.svg)](https://crates.io/crates/cargo-readme)
[![Workflow Status](https://github.com/webern/cargo-readme/workflows/main/badge.svg)](https://github.com/webern/cargo-readme/actions?query=workflow%3A%22main%22)

# cargo-readme

Generate README.md from doc comments.

Cargo subcommand that extract documentation from your crate's doc comments that you can use to
populate your README.md.

#### Attribution

This library was authored by Livio Ribeiro ([@livioribeiro](https://github.com/livioribeiro))
and originally located at `https://github.com/livioribeiro/cargo-readme`, which now redirects
here (as of August 2023). Thank you, Livio, for this lib!

## Installation

```sh
cargo install cargo-readme
```

## Motivation

As you write documentation, you often have to show examples of how to use your software. But
how do you make sure your examples are all working properly? That we didn't forget to update
them after a breaking change and left our (possibly new) users with errors they will have to
figure out by themselves?

With `cargo-readme`, you just write the rustdoc, run the tests, and then run:

```sh
cargo readme > README.md
```

And that's it! Your `README.md` is populated with the contents of the doc comments from your
`lib.rs` (or `main.rs`).

## Usage

Let's take the following rust doc:

```rust
//! This is my awesome crate
//!
//! Here goes some other description of what it is and what is does
//!
//! # Examples
//! ```
//! fn sum2(n1: i32, n2: i32) -> i32 {
//!   n1 + n2
//! }
//! # assert_eq!(4, sum2(2, 2));
//! ```
```

Running `cargo readme` will output the following:

~~~markdown
[![Build Status](__badge_image__)](__badge_url__)

# my_crate

This is my awesome crate

Here goes some other description of what it is and what is does

## Examples
```rust
fn sum2(n1: i32, n2: i32) -> i32 {
  n1 + n2
}
```

License: MY_LICENSE
~~~

Let's see what's happened:

- a badge was created from the one defined in the `[badges]` section of `Cargo.toml`
- the crate name ("my-crate") was added
- "# Examples" heading became "## Examples"
- code block became "```rust"
- hidden line `# assert_eq!(4, sum2(2, 2));` was removed

`cargo-readme` also supports multiline doc comments `/*! */` (but you cannot mix styles):

~~~rust
/*!
This is my awesome crate

Here goes some other description of what it is and what is does

```
fn sum2(n1: i32, n2: i32) -> i32 {
  n1 + n2
}
```
*/
~~~

If you have additional information that does not fit in doc comments, you can use a template.
Just create a file called `README.tpl` in the same directory as `Cargo.toml` with the following
content:

```tpl
{{badges}}

# {{crate}}

{{readme}}

Current version: {{version}}

Some additional info here

License: {{license}}
```

The output will look like this

~~~markdown
[![Build Status](__badge_image__)](__badge_url__)

# my_crate

Current version: 3.0.0

This is my awesome crate

Here goes some other description of what it is and what is does

## Examples
```rust
fn sum2(n1: i32, n2: i32) -> i32 {
  n1 + n2
}
```

Some additional info here

License: MY_LICENSE
~~~

By default, `README.tpl` will be used as the template, but you can override it using the
`--template` to choose a different template or `--no-template` to disable it.

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or https://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
