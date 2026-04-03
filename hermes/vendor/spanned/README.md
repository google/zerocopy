# Simple span handling for `str` and `&[u8]`

This crate exposes some of the methods that exist on `str` or `bstr`.
If you are missing any you need, please open issues or PRs.

The basic usage is to read from a file and then use the methods to modify it:

```rust
let file = Spanned::<String>::read_from_file(path)?;
for line in file.lines() {
    if let Some(rest) = line.strip_prefix("cake:") {
        println!("found a cake at {}: {}", rest.span.line_start, *rest);
    }
}
```

any `Spanned` object will always know its file, line and column information and
correctly preserve it across operations that take subslices. The column information
is counted in the number of utf8 characters, which is not entirely correct.
Please open an issue if you encounter this to be a problem.
