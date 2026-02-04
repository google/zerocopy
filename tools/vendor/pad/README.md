# rust-pad [![pad on crates.io](http://meritbadge.herokuapp.com/pad)](https://crates.io/crates/pad) [![Build status](https://travis-ci.org/ogham/rust-pad.svg?branch=master)](https://travis-ci.org/ogham/rust-pad)


This is a library for padding strings at runtime.

It provides four helper functions for the most common use cases, and one
main function to cover the other cases.

### [View the Rustdoc](https://docs.rs/pad)


# Installation

This crate works with [Cargo](http://crates.io). Add the following to your `Cargo.toml` dependencies section:

```toml
[dependencies]
pad = "0.1"
```


# Padding in the stdlib

**You do not need this crate for simple padding!**
It’s possible to pad strings using the Rust standard library.

For example, to pad a number with zeroes:

```rust
// Padding using std::fmt
assert_eq!("0000012345", format!("{:0>10}", 12345));
```

You can even use a variable for the padding width:

```rust
// Padding using std::fmt
assert_eq!("hello       ", format!("{:width$}", "hello", width=12));
```

The [Rust documentation for `std::fmt`](https://doc.rust-lang.org/std/fmt/)
contains more examples. The rest of the examples will use the `pad` crate.


# Usage

You can pad a string to have a minimum width with the `pad_to_width`
method:

```rust
use pad::PadStr;
println!("{}", "Hi there!".pad_to_width(16));
```

This will print out “Hi there!” followed by seven spaces, which is the
number of spaces necessary to bring it up to a total of sixteen characters
wide.

String length is determined with the
[unicode_width](https://unicode-rs.github.io/unicode-width/unicode_width/index.html)
crate, without assuming CJK.


## Alignment

By default, strings are left-aligned: any extra characters are added on
the right. To change this, pass in an `Alignment` value:

```rust
use pad::{PadStr, Alignment};
let s = "I'm over here".pad_to_width_with_alignment(20, Alignment::Right);
```

There are four of these in total:

- **Left**, which puts the text on the left and spaces on the right;
- **Right**, which puts the text on the right and spaces on the left;
- **Middle**, which centres the text evenly, putting it slightly to the left if it can’t be exactly centered;
- **MiddleRight**, as above, but to the right.


## Characters

Another thing that’s set by default is the character that’s used to pad
the strings — by default, it’s space, but you can change it:

```rust
use pad::PadStr;
let s = "Example".pad_to_width_with_char(10, '_');
```


## Truncation

Finally, you can override what happens when a value exceeds the width you
give. By default, the width parameter indicates a *minimum width*: any
string less will be padded, but any string greater will still be returned
in its entirety.

You can instead tell it to pad with a maximum value, which will truncate
the input when a string longer than the width is passed in.

```rust
use pad::PadStr;
let short = "short".with_exact_width(10);  // "short     "
let long = "this string is long".with_exact_width(10);  // "this strin"
```


# A Full Example

All of the above functions delegate to the `pad` function, which you can
use in special cases. Here, in order to **right**-pad a number with
**zeroes**, pass in all the arguments:

```rust
use pad::{PadStr, Alignment};
let s = "12345".pad(10, '0', Alignment::Right, true);
```

(The `true` at the end could just as easily be `false`. It’s whether to
truncate or not.)


# A Note on Debugging

One very last point: the width function takes a `usize`, rather than a
signed number type. This means that if you try to pass in a negative size,
it’ll wrap around to a positive size, and produce a massive string and
possibly crash your program. So if your padding calls are failing for some
reason, this is probably why.
