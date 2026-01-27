# `serde_tokenstream`

This Rust crate is intended for use with macros that need bespoke configuration.
It's implemented as a `serde::Deserializer` that operates on a
`proc_macro2::TokenSteam` (easily converted from the standard
`proc_macro::TokenStream`).

## Usage

Say we're building an attribute proc macro that you want consumers to use like
this:

```rust
#[MyMacro {
    name = "SNPP",
    owner = "Canary M Burns",
    details = {
        kind = Fission,
        year_of_opening = 1968,
    }
}]
fn some_func() {
    ...
}
```

It's also useful for function-like macros:

```rust
my_macro!(
    name = "SNPP",
    owner = "Hans",
    layoffs_in_alphabetical_order = [
        "Simpson, Homer"
    ]
);
```

The function that implements the proc macro must have two parameters (both of
type `proc_macro::TokenStream`): attributes (the tokens with the braces that
follow the name of the macro), and the item (the function, type, etc. to
which the macro is applied):

```rust
#[proc_macro_attribute]
pub fn MyMacro(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    ...
}
```

We'll first define the `struct` type that represents the configuration and
`derive` a `serde::Deserialize`:

```rust
#[derive(Deserialize)]
struct Config {
    name: String,
    owner: String,
    details: ConfigDetails,
}

#[derive(Deserialize)]
struct ConfigDetails {
    kind: ConfigDetailsType,
    year_of_opening: usize,
}

#[derive(Deserialize)]
enum ConfigDetailsType {
    Coal,
    Fission,
    Hydroelectric,
}
```

Now we can parse `attr` into the `Config` struct with
`serde_tokenstream::from_tokenstream`:

```rust
use proc_macro2::TokenStream;
use serde_tokenstream::from_tokenstream;

#[allow(non_snake_case)]
#[proc_macro_attribute]
pub fn MyMacro(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let config = match from_tokenstream::<Config>(&TokenStream::from(attr)) {
        Ok(c) => c,
        Err(err) => return err.to_compile_error().into(),
    };

    ...
}
```

See the `serde` documentation for the full range of controls that can be
applied to types and their members.

## Error Handling

Errors indicate the problematic portion of consuming code to assist the macro
consumer:

```rust
#[MyMacro{
    name = "Rocinante",
    owner = "Rocicorp",
    details = {
        kind = Fusion,
        year_of_opening = 2347
    }
}]
fn deploy() {
    ...
}
```

```
error: unknown variant `Fusion`, expected one of `Coal`, `Fission`, `Hydroelectric`
 --> tests/test_err1.rs:7:16
  |
7 |         kind = Fusion,
  |                ^^^^^^
```

## Nested attributes

For parsing attributes nested inside an outer macro, use
`from_tokenstream_spanned`. This function provides better span attribution for
errors at the top level.

The most common use is with `syn::MetaList`. For example, if your macro is a
derive macro:

```rust
#[derive(MyRobot)]
#[robot {
    name = "Mawhrin-Skel",
    kind = Drone,
    planet = "Eä",
}]
fn monitor() {
    ...
}
```

Then `robot` can be interpreted as a `syn::MetaList` instance. With that:

```rust
use serde_tokenstream::from_tokenstream;

#[derive(Deserialize)]
struct Robot {
    ...
}

#[proc_macro_derive(MyRobot, attributes(robot))]
pub fn my_robot(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let list = /* obtain the `syn::MetaList` from the input */;

    let config = match from_tokenstream_spanned::<Robot>(
        list.delimiter.span(),
        &list.tokens
    ) {
        Ok(c) => c,
        Err(err) => return err.to_compile_error().into(),
    };
}
```

## TokenStream and syn::\* values

In some cases, it's useful to pass TokenStream values as parameters to a macro.
In this case we can use the `TokenStreamWrapper` which is a wrapper around
`TokenStream` that implements `Deserialize` or `ParseWrapper` which is a
wrapper around `syn::Parse` that implements `Deserialize`. The latter is useful
for passing in, for example, a `syn::Path`, or other specific entities from the
`syn` crate.

## OrderedMap

You may want to use the map syntax with keys that cannot be used by types such
as `HashMap` or `BTreeMap` because they don't implement `Hash` or `Ord`. In
those cases, you can use an `OrderedMap` and extract the pairs as an iterator
of tuples.

Let's say we we want our "keys" to be `serde_json::Value`s and our value to
be... whatever... `String`s! You can't use `serde_json::Value` as the key in a
`HashMap` or `BTreeMap`, but we can for an `OrderedMap`:

```rust
let config = from_tokenstream::<OrderedMap<serde_json::Value, String>>(tokens)?;
```

The macro can then be invoked like this:

```rust
my_macro!(
    {
        "type" = "string",
        "format" = "uuid",
    } = "uuid::Uuid",
    {
        "type" = "string",
        "format" = "ip",
    } = "std::net::IpAddr",
);
```
