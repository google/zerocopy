rust-uritemplate
================

[![Build Status](https://img.shields.io/travis/chowdhurya/rust-uritemplate/master.svg?style=flat-square)](https://travis-ci.org/chowdhurya/rust-uritemplate)
[![Cargo version](https://img.shields.io/crates/v/uritemplate.svg?style=flat-square)](https://crates.io/crates/uritemplate)
[![License](https://img.shields.io/crates/l/uritemplate.svg?style=flat-square)](https://github.com/chowdhurya/rust-uritemplate/blob/master/LICENSE)

[Documentation](https://chowdhurya.github.io/rust-uritemplate/uritemplate/)


`rust-uritemplate` is a Rust implementation of
[RFC6570  - URI Template](http://tools.ietf.org/html/rfc6570) that can process
URI Templates up to and including ones designated as Level 4 by the
specification. It passes all of the tests in the
[uritemplate-test](https://github.com/uri-templates/uritemplate-test) test
suite.

Basic Usage
-----------
Variable setting can be chained for nice, clean code.

```rust
let uri = UriTemplate::new("/view/{object:1}/{/object,names}{?query*}")
    .set("object", "lakes")
    .set("names", &["Erie", "Superior", "Ontario"])
    .set("query", &[("size", "15"), ("lang", "en")])
    .build();

assert_eq!(uri, "/view/l/lakes/Erie,Superior,Ontario?size=15&lang=en");
```

It is not possible to set a variable to the value "undefined". Instead, simply
delete the variable if you have already set it.

```rust
let mut t = UriTemplate::new("{hello}");
t.set("hello", "Hello World!");
assert_eq!(t.build(), "Hello%20World%21");

t.delete("hello");
assert_eq!(t.build(), "");
```

The `delete` function returns `true` if the variable existed and `false`
otherwise.

Supported Types
---------------
Any type that implements `IntoTemplateVar` can be set as the value of a
`UriTemplate` variable. The following implementations are provided by default
for each type of variable:

- Scalar Values: `String`, `&str`
- Lists: `Vec<String>`, `&[String]`, `&[str]`
- Associative Arrays: `Vec<(String, String)>`, `&[(String, String)]`,
  `&[(&str, &str)]`, `&HashMap<String, String>`

In addition, you can implement `IntoTemplateVar` for your own types. View the
documentation for `IntoTemplateVar` for information on how that works.
