# comma

[![Crates.io](https://img.shields.io/crates/v/comma?style=flat-square)](https://crates.io/crates/comma)
[![docs.rs](https://docs.rs/comma/badge.svg)](https://docs.rs/comma)
[![Build Status](https://travis-ci.org/emctague/comma.svg?branch=master)](https://travis-ci.org/emctague/comma)

`comma` splits shell-style commands, e.g. `sendmsg joe "I say \"hi\" to you!"`, into a list of individual tokens.
It correctly handles unicode characters, escape sequences, and single- or double-quoted strings.

## Cargo

```toml
[dependencies]
comma = "1.0.0"
```

## Usage

```rust
use comma::parse_command;

fn main () {
    let parsed = parse_command("sendmsg joe \"I say \\\"hi\\\" to you!\" 'but only\\ntoday'").unwrap();
    println!("Result: {:#?}", parsed); // Result: [ "sendmsg", "joe", "I say \"hi\" to you!", "but only\ntoday" ]
}
```