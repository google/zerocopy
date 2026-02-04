# prettydiff

[![Crate](https://img.shields.io/crates/v/prettydiff.svg)](https://crates.io/crates/prettydiff)
[![docs.rs](https://docs.rs/prettydiff/badge.svg)](https://docs.rs/prettydiff)

Side-by-side diff for two files in Rust. App && Library.

## Examples

### Slice diff

```rust
use prettydiff::diff_slice;

println!("Diff: {}", diff_slice(&[1, 2, 3, 4, 5, 6], &[2, 3, 5, 7]));
println!(
    "Diff: {}",
    diff_slice(&["q", "a", "b", "x", "c", "d"], &["a", "b", "y", "c", "d", "f"])
);
println!(
    "Diff: {}",
    diff_slice(&["a", "c", "d", "b"], &["a", "e", "b"])
);
 ```

 ![diff_slice](https://raw.githubusercontent.com/romankoblov/prettydiff/master/screens/diff_slice.png)

Get vector of changes:

```rust
use prettydiff::diff_slice;

assert_eq!(
    diff_slice(&["q", "a", "b", "x", "c", "d"], &["a", "b", "y", "c", "d", "f"]).diff,
    vec![
        DiffOp::Remove(&["q"]),
        DiffOp::Equal(&["a", "b"]),
        DiffOp::Replace(&["x"], &["y"]),
        DiffOp::Equal(&["c", "d"]),
        DiffOp::Insert(&["f"]),
    ]
);
```

### Diff line by chars or words

![diff_chars](https://raw.githubusercontent.com/romankoblov/prettydiff/master/screens/diff_chars.png)

```rust
use prettydiff::{diff_chars, diff_words};

println!("diff_chars: {}", diff_chars("abefcd", "zadqwc"));
println!(
    "diff_chars: {}",
    diff_chars(
        "The quick brown fox jumps over the lazy dog",
        "The quick brown dog leaps over the lazy cat"
    )
);
println!(
    "diff_chars: {}",
    diff_chars(
        "The red brown fox jumped over the rolling log",
        "The brown spotted fox leaped over the rolling log"
    )
);
println!(
    "diff_chars: {}",
    diff_chars(
        "The red    brown fox jumped over the rolling log",
        "The brown spotted fox leaped over the rolling log"
    )
    .set_highlight_whitespace(true)
);
println!(
    "diff_words: {}",
    diff_words(
        "The red brown fox jumped over the rolling log",
        "The brown spotted fox leaped over the rolling log"
    )
);
println!(
    "diff_words: {}",
    diff_words(
        "The quick brown fox jumps over the lazy dog",
        "The quick, brown dog leaps over the lazy cat"
    )
);
```

### Diff lines

![diff_lines](https://raw.githubusercontent.com/romankoblov/prettydiff/master/screens/diff_lines.png)

```rust
use prettydiff::diff_lines;

let code1_a = r#"
void func1() {
    x += 1
}

void func2() {
    x += 2
}
    "#;
let code1_b = r#"
void func1(a: u32) {
    x += 1
}

void functhreehalves() {
    x += 1.5
}

void func2() {
    x += 2
}

void func3(){}
"#;
println!("diff_lines:");
println!("{}", diff_lines(code1_a, code1_b));
```

## App

This crate also provides app for side-by-side diff:

```sh
cargo install prettydiff
prettydiff left_file.txt right_file.txt
```

![App](https://raw.githubusercontent.com/romankoblov/prettydiff/master/screens/app.png)