// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure Unicode control, bidirectional override, terminal-escape, and Markdown
//! injection sanitization primitives.
//!
//! These helpers sanitize untrusted strings (receipt fields, diagnostic text,
//! module paths, and error messages) via [`SanitizedInline`],
//! [`SanitizedBlock`], and the GFM escaping formatters for terminal and
//! report surfaces. Designed as a pure, I/O-free formatting substrate.

use std::fmt::{self, Display};

/// Return `true` when `ch` must be escaped before emitting untrusted text to a
/// terminal or report surface.
///
/// Rejects C0 control characters (`U+0000..=U+001F`), `DEL` (`U+007F`), C1
/// control characters (`U+0080..=U+009F`), Unicode bidirectional controls
/// (`U+061C`, `U+070F`, `U+200E..=U+200F`, `U+202A..=U+202E`,
/// `U+2066..=U+206F`), zero-width and invisible formatting characters
/// (`U+00AD`, `U+034F`, `U+115F..=U+1160`, `U+180E`, `U+200B..=U+200D`,
/// `U+2060..=U+2064`, `U+3164`, `U+FEFF`, `U+FFA0`, `U+FFF9..=U+FFFB`),
/// line/paragraph separators (`U+2028..=U+2029`), Unicode Tag characters
/// (`U+E0000..=U+E007F`), and variation selectors (`U+FE00..=U+FE0F`,
/// `U+E0100..=U+E01EF`).
pub const fn is_dangerous_unicode(ch: char) -> bool {
    matches!(
        ch as u32,
        0x0000..=0x001F
            | 0x007F..=0x009F
            | 0x00AD
            | 0x034F
            | 0x061C
            | 0x070F
            | 0x115F..=0x1160
            | 0x180E
            | 0x200B..=0x200F
            | 0x2028..=0x202E
            | 0x2060..=0x2064
            | 0x2066..=0x206F
            | 0x3164
            | 0xFE00..=0xFE0F
            | 0xFEFF
            | 0xFFA0
            | 0xFFF9..=0xFFFB
            | 0xE0000..=0xE007F
            | 0xE0100..=0xE01EF
    )
}

fn write_escaped_char(f: &mut fmt::Formatter<'_>, ch: char) -> fmt::Result {
    match ch {
        '\n' => f.write_str("\\n"),
        '\r' => f.write_str("\\r"),
        '\t' => f.write_str("\\t"),
        other => write!(f, "\\u{{{:04X}}}", other as u32),
    }
}

/// Renders an untrusted string on a single line with every dangerous code point
/// (including `\n`, `\r`, `\t`, ANSI CSI/OSC bytes, C1, Bidi, and Tag code
/// points) escaped visibly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SanitizedInline<'a>(pub &'a str);

impl Display for SanitizedInline<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for ch in self.0.chars() {
            if is_dangerous_unicode(ch) {
                write_escaped_char(f, ch)?;
            } else {
                write!(f, "{ch}")?;
            }
        }
        Ok(())
    }
}

/// Materialize [`SanitizedInline`] into an owned `String`.
pub fn sanitize_inline_string(input: &str) -> String {
    SanitizedInline(input).to_string()
}

/// Renders a multi-line untrusted text block prefixed on every physical line
/// with `"  | "` starting at column 0, normalizing `\r\n` and lone `\r` line
/// boundaries while escaping all other dangerous code points inline.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SanitizedBlock<'a>(pub &'a str);

impl Display for SanitizedBlock<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut chars = self.0.chars().peekable();
        f.write_str("  | ")?;
        while let Some(ch) = chars.next() {
            if ch == '\r' {
                if chars.peek() == Some(&'\n') {
                    let _ = chars.next();
                }
                f.write_str("\n  | ")?;
            } else if ch == '\n' {
                f.write_str("\n  | ")?;
            } else if is_dangerous_unicode(ch) {
                write_escaped_char(f, ch)?;
            } else {
                write!(f, "{ch}")?;
            }
        }
        Ok(())
    }
}

/// Escape an untrusted string for safe inclusion inside a GitHub-Flavored
/// Markdown table cell (inline control-escaped plus GFM syntax delimiters).
pub fn escape_gfm_cell(input: &str) -> String {
    use std::fmt::Write as _;

    let mut out = String::with_capacity(input.len());
    for ch in input.chars() {
        if is_dangerous_unicode(ch) {
            match ch {
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                other => {
                    let _ = write!(out, "\\u{{{:04X}}}", other as u32);
                }
            }
        } else {
            if matches!(ch, '\\' | '|' | '`' | '*' | '_' | '~' | '<' | '>' | '[' | ']' | '&') {
                out.push('\\');
            }
            out.push(ch);
        }
    }
    out
}

fn has_odd_backslash_pipe(s: &str) -> bool {
    let mut backslash_run = 0usize;
    for ch in s.chars() {
        if ch == '\\' {
            backslash_run += 1;
        } else if ch == '|' {
            if !backslash_run.is_multiple_of(2) {
                return true;
            }
            backslash_run = 0;
        } else {
            backslash_run = 0;
        }
    }
    false
}

fn format_html_code_span(inline: &str) -> String {
    use std::fmt::Write as _;

    let mut out = String::with_capacity(inline.len() + 16);
    out.push_str("<code>");
    for ch in inline.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '\\' => out.push_str("&#92;"),
            '|' => out.push_str("&#124;"),
            '`' => out.push_str("&#96;"),
            '*' => out.push_str("&#42;"),
            '_' => out.push_str("&#95;"),
            '~' => out.push_str("&#126;"),
            '[' => out.push_str("&#91;"),
            ']' => out.push_str("&#93;"),
            other => {
                let _ = write!(out, "{other}");
            }
        }
    }
    out.push_str("</code>");
    out
}

/// Format an untrusted value as a GitHub-Flavored Markdown inline code span
/// safe for inclusion inside a Markdown table cell.
///
/// Escapes dangerous Unicode/control code points, escapes `|` so GFM table
/// column splitting cannot trigger inside backticks, pads outer spaces or
/// backticks per CommonMark §6.1, and uses entity-escaped `<code>...</code>`
/// when an empty string or `\|` sequence cannot be represented losslessly as a
/// backtick span in a GFM table cell.
pub fn format_gfm_code_cell(input: &str) -> String {
    let inline = sanitize_inline_string(input);
    if inline.is_empty() || has_odd_backslash_pipe(&inline) {
        return format_html_code_span(&inline);
    }
    let mut escaped_pipe = String::with_capacity(inline.len());
    let mut backslash_run = 0usize;
    for ch in inline.chars() {
        if ch == '\\' {
            backslash_run += 1;
            escaped_pipe.push(ch);
        } else if ch == '|' {
            if backslash_run.is_multiple_of(2) {
                escaped_pipe.push('\\');
            }
            backslash_run = 0;
            escaped_pipe.push('|');
        } else {
            backslash_run = 0;
            escaped_pipe.push(ch);
        }
    }
    let fence_len = longest_backtick_run(&escaped_pipe) + 1;
    let fence = "`".repeat(fence_len);
    let has_outer_space = escaped_pipe.starts_with(' ')
        && escaped_pipe.ends_with(' ')
        && escaped_pipe.bytes().any(|b| b != b' ');
    let needs_pad = escaped_pipe.starts_with('`') || escaped_pipe.ends_with('`') || has_outer_space;
    if needs_pad {
        format!("{fence} {escaped_pipe} {fence}")
    } else {
        format!("{fence}{escaped_pipe}{fence}")
    }
}

/// Wrap `body` in a CommonMark/GFM fenced code block whose backtick delimiter
/// strictly exceeds the longest contiguous backtick run inside `body`,
/// neutralizing control characters and stripping backticks from the info
/// string per CommonMark §4.5.
pub fn format_fenced_code_block(lang: &str, body: &str) -> String {
    let max_run = longest_backtick_run(body);
    let fence_len = (max_run + 1).max(3);
    let fence = "`".repeat(fence_len);
    let mut out = String::new();
    out.push_str(&fence);
    for ch in sanitize_inline_string(lang).chars() {
        if ch != '`' {
            out.push(ch);
        }
    }
    out.push('\n');

    for chunk in body.split_inclusive('\n') {
        let (line, had_newline) = match chunk.strip_suffix('\n') {
            Some(rest) => (rest.strip_suffix('\r').unwrap_or(rest), true),
            None => (chunk, false),
        };
        for ch in line.chars() {
            if is_dangerous_unicode(ch) && ch != '\t' {
                let escaped = format!("\\u{{{:04X}}}", ch as u32);
                out.push_str(&escaped);
            } else {
                out.push(ch);
            }
        }
        if had_newline {
            out.push('\n');
        }
    }
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out.push_str(&fence);
    out
}

fn longest_backtick_run(s: &str) -> usize {
    let mut best = 0usize;
    let mut cur = 0usize;
    for b in s.bytes() {
        if b == b'`' {
            cur += 1;
            best = best.max(cur);
        } else {
            cur = 0;
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitize_inline_neutralizes_ansi_bidi_c1_and_tags() {
        let evil = "ok\x1b[31mred\x1b[0m\x07\u{0085}\u{202E}txt\u{E0001}\r\nnext";
        let rendered = sanitize_inline_string(evil);
        assert!(!rendered.contains('\x1b'));
        assert!(!rendered.contains('\n'));
        assert!(!rendered.contains('\r'));
        assert!(!rendered.contains('\u{202E}'));
        assert!(!rendered.contains('\u{0085}'));
        assert!(!rendered.contains('\u{E0001}'));
        assert!(rendered.contains("\\u{001B}[31mred"));
        assert!(rendered.contains("\\u{202E}"));
        assert!(rendered.contains("\\u{E0001}"));
        assert!(rendered.contains("\\r\\n"));
    }

    #[test]
    fn sanitize_block_keeps_column_zero_gutter_on_every_line() {
        let block = SanitizedBlock("line1\x1b[2J\r\nline2\rline3\nStatus: verified").to_string();
        let lines: Vec<&str> = block.lines().collect();
        assert_eq!(lines.len(), 4);
        for line in &lines {
            assert!(line.starts_with("  | "), "missing gutter: {line:?}");
        }
        assert!(!block.contains('\x1b'));
    }

    #[test]
    fn gfm_escaping_and_backtick_fence_sizing() {
        assert_eq!(escape_gfm_cell("a|b`<x>*_~&#\n"), "a\\|b\\`\\<x\\>\\*\\_\\~\\&#\\n");
        assert_eq!(escape_gfm_cell("~~strike~~"), "\\~\\~strike\\~\\~");
        let code_cell = format_gfm_code_cell("`x|``y`\u{206A}\u{3164}");
        assert!(code_cell.starts_with("``` "));
        assert!(code_cell.ends_with(" ```"));
        assert!(code_cell.contains("\\|"));
        assert!(code_cell.contains("\\u{206A}\\u{3164}"));
        assert_eq!(format_gfm_code_cell(""), "<code></code>");
        assert_eq!(format_gfm_code_cell(" foo "), "`  foo  `");
        assert_eq!(format_gfm_code_cell("   "), "`   `");
        assert_eq!(format_gfm_code_cell(r"a\|b"), "<code>a&#92;&#124;b</code>");
        assert_eq!(format_gfm_code_cell(r"a\\|b"), r"`a\\\|b`");
        let fenced_cr = format_fenced_code_block("txt", "a\r\nb\r");
        assert_eq!(fenced_cr, "```txt\na\nb\\u{000D}\n```");
        let fenced = format_fenced_code_block("json", "```\n````\n\"ok\"");
        assert!(fenced.starts_with("`````json\n"));
        assert!(fenced.ends_with("\n`````"));
        let bad_lang = format_fenced_code_block("rust`", "fn main() {}");
        assert!(bad_lang.starts_with("```rust\n"));
        assert!(!bad_lang.lines().next().unwrap().trim_start_matches('`').contains('`'));
    }
}
