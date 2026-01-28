## 0.3.1 (2025-03-31)

New:

- Support the `wasm32-wasip2` target.

Changes:

- Tweaked sanitization of invalid UTF-8 in options.
- Removed special handling for WASI since WASI is de facto Unicode-only.

## 0.3.0 (2023-01-16)

This release adds a new preferred way to cast `OsString` into `String` (`.string()?`) and makes raw argument processing more flexible.

Almost no programs should need changes to keep working, but `.string()?` makes it easier to use lexopt with other error types like [anyhow](https://docs.rs/anyhow)'s and using it is therefore recommended.

New:

- Add `ValueExt::string()` as the preferred method for converting from `OsString` into `String`. Unlike [`OsString::into_string()`](https://doc.rust-lang.org/std/ffi/struct.OsString.html#method.into_string) it has a normal error type so it's compatible with catch-all error types like [`anyhow::Error`](https://docs.rs/anyhow/latest/anyhow/struct.Error.html).
  - `into_string()?` will stay supported for the time being.
- Add `RawArgs::as_slice()` for unlimited lookahead.
- Add `Parser::try_raw_args()` to get raw arguments without consuming any arguments in case of failure.
- `Parser` now implements `Clone`, `Send`, and `Sync`. Its `Debug` output now shows the remaining arguments.

Changes:

- The input iterator is now consumed when you create a `Parser`, instead of during parsing. This breaks certain clever code that inspects the state of the iterator, but `RawArgs::as_slice()` may provide an alternative. (If you don't know what this means then you aren't affected.)
- Calling `Parser::values()` no longer consumes any arguments if you don't use the iterator.
- `RawArgs::peek()` now takes `&self` instead of `&mut self`.

## 0.2.1 (2022-07-10)

New:

- Add `Parser::raw_args()` for collecting raw unparsed arguments. ([#12](https://github.com/blyxxyz/lexopt/issues/12))
- Implement `Debug` for `ValuesIter`.

Bug fixes:

- Change "missing argument at end of command" error message. ([#11](https://github.com/blyxxyz/lexopt/issues/11))

## 0.2.0 (2021-10-23)

While this release is not strictly backward-compatible it should break very few programs.

New:

- Add `Parser::values()` for options with multiple arguments.
- Add `Parser::optional_value()` for options with optional arguments.
- Add `Parser::from_iter()` to construct from an iterator that includes the binary name. ([#5](https://github.com/blyxxyz/lexopt/issues/5))
- Document how to use `Parser::value()` to collect all remaining arguments.

Changes:

- Support `=` as a separator for short options (as in `-o=value`). ([#18](https://github.com/blyxxyz/lexopt/issues/18))
- Sanitize the binary name if it's invalid unicode instead of ignoring it.
- Make `Error::UnexpectedValue.option` a `String` instead of an `Option<String>`.

Bug fixes:

- Include `bin_name` in `Parser`'s `Debug` output.

## 0.1.0 (2021-07-16)
Initial release.
