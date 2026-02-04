# Unreleased

- Updated top-level docs to include a note about `ColoredString`\'s role in the `Colorize` pipeline as well as link to it to suggest learning more about how to manipulate existing `ColoredString`\'s.
- Changes to `ColoredString`:
  - Expose fields.
  - **[DEPRECATION]:** Deprecated methods `fgcolor`, `bgcolor`, and `style` due to their obsolescence in the face of the exposing of their represented fields.
  - Add methods for clearing specific elements of `fgcolor`, `bgcolor`, and `style`.
  - Change Default implementation to be via derive as Style now implements Default (see changes to Style below).
  - Add implementation of `DerefMut`.
  - Updated docs to reflect the above changes as well as generally greatly expand them.
- Changes to `Style`:
  - Implemented `Default` for `Style` (returns `CLEAR`). This exposes a method by which users can create plain `Style`\'s from scratch.
  - Implemented `From<Styles>` for `Style`. This lets users easily create `Style`\'s from specific styles.
  - Exposed previously private method `add`.
  - Created method `remove` which essentially does the opposite.
  - Added builder-style methods in the vein of `Colorize` to add stylings (e.g. `bold`, `underline`, `italic`, `strikethrough`).
  - Implemented bitwise operators `BitAnd`, `BitOr`, `BitXor`, and `Not` as well as their representative assignment operators. You can also use a `Styles` as an operand for these.
  - Implemented `FromIterator<Styles>` for Style.
- Changes to `Styles`:
  - Implemented bitwise operators `BitAnd`, `BitOr`, `BitXor`, and `Not` which all combine `Styles`\'s and output `Style`\'s. These can also take a `Style` as an operand.
- Added additional testing for all of the above changes.
- Added methods `with_style` and `with_color_and_style` to `Colorize`.

# 2.1.0
* Impl From<String> for ColoredString by @mahor1221 in https://github.com/colored-rs/colored/pull/126
* Allow conversion from ColoredString to Error by @spenserblack in https://github.com/colored-rs/colored/pull/86
* Suggestion for minor documentation clarification by @jonasbn in https://github.com/colored-rs/colored/pull/98
* Remove unnecessary is_terminal dependency by @Oakchris1955 in https://github.com/colored-rs/colored/pull/149
  - Document crate MSRV of `1.70`.

# 2.0.4
- Switch from `winapi` to `windows-sys`.

# 2.0.3
- Document crate MSRV of `1.63`.

# 2.0.2
- Fix typo in `src/control.rs`.
- Replace `atty` dependency with `is-terminal`.

# 2.0.1 (July 3, 2023)
- Add edition for future compatibility.
- Implement custom colors that can be stored in a variable.

# 2.0.0 (July 14, 2020)
- Add support for true colours.
- Alter `Color` interface to return `Cow<'static, str>`

# 1.9.3 (February 24, 2020)
- Fix compilation regression for 1.34.0. Thanks @jlevon for reporting.

# 1.9.2 (January 11, 2020)
- Exposed `ColoredString` data through methods for purposes of interrogating the applied colours.
- Increased documentation.

# 1.9.1 (December 31, 2019)

- Remove deprecated `try!` macro in codebase
- Reduce allocations in `ColoredString` impl (PR#65)
- Added `"purple"` as match in `impl FromStr for Color` (PR#71)

# 1.9.0 (November 11, 2019)

- **[POSSIBLE_BREAKING CHANGE]:** Replace `winconsole` with `winapi`:
  - Changes `set_virtual_terminal` function signature.
- Update dependencies
- Add Dockerfile
- Respect tty discovery for CLICOLOR

# 1.8.0 (April 30, 2019)

- FEAT: support Windows 10 colors

# 1.7.0 (January, 2019)
- TECH: update lazy\_static
- FEAT: introduce respect for the `NO_COLOR` environment variable

# 1.6.1 (July 9, 2018)
- TECH: update lazy\_static
- CHORE: fix typos in README and documentation

# 1.6.0 (October 31, 2017)
- FEAT: introduced bright colors. `"hello".bright_blue().on_bright_red();`
- FEAT: introduced strikethrough styling. `"hello".strikethrough();`

# 1.5.3 (September 28, 2017)

- FEAT: derive Copy and Clone for `Color`
- FEAT: derive Clone for `ColoredString`

# 1.5.2 (July 6, 2017)

- FIX: method `Colorize::reversed` has been added. `Colorize::reverse` was a typo, that we will keep
    for compatibility

# 1.5.1 (May 9, 2017)

- Update lazy\_static to 0.2.

# 1.5.0 (May 1, 2017)

- FEAT: support for `"hello".color("blue")` (dynamic colors)

# 1.3.2 (Nov 26, 2016)

- FIX: usage of nested ColoredString again, no more style broken mid-line

# 1.3.1 (Oct 14, 2016)

- FIX: usage of ColoredString in a nested way broke the styling mid-line

# 1.3.0 (Jul 31, 2016)

- Provide various options for disabling the coloring in an API-compatible way

# 1.2.0 (Mar 30, 2016)

- Support the different formatting options, like padding and alignment

# 1.1.0 (Mar 15, 2016)

- Respect the CLICOLOR/CLICOLOR\_FORCE behavior. See [this specs](http://bixense.com/clicolors/)

# 1.0.1 (Mar 14, 2016)

- Add a CHANGLOG
- Fix crate dependencies: move `ansi_term` in dev\_dependencies

# 1.0.0 (Mar 13, 2016)

- Initial release
