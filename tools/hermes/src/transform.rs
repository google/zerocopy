use proc_macro2::Span;
use syn::spanned::Spanned;

use crate::parse::{ParsedItem, ParsedLeanItem};

/// Appends the spans of text that should be blanked out in the shadow crate.
///
/// For `unsafe` functions with Hermes annotations, this targets:
/// 1. The `unsafe` keyword (to make the function signature "safe" for Aeneas).
/// 2. The entire function block (to remove the unverified implementation).
pub fn append_edits(item: &ParsedLeanItem, edits: &mut Vec<Span>) {
    if let ParsedItem::Fn(func) = &item.item {
        if let Some(unsafety) = &func.sig.unsafety {
            // 1. Mark the `unsafe` keyword for blanking.
            // Result: `unsafe fn` -> `       fn`
            edits.push(unsafety.span());

            // TODO:
            // - Only blank bodies for functions which are modeled.
            // - Figure out what to replace these bodies with.
            edits.push(func.block.span());
        }
    }
}

/// Applies a set of redaction edits to the source buffer in-place.
///
/// For each span in `edits`, this function replaces all characters with spaces
/// (`0x20`), except for newline characters (`0x0A` and `0x0D`), which are
/// preserved to maintain line numbering and Windows compatibility. This allows
/// the shadow crate to report errors on spans that align with the user's
/// original file.
///
/// # Panics
///
/// Panics if any span in `edits` is not in-bounds of `buffer`.
pub fn apply_edits(buffer: &mut [u8], edits: &[Span]) {
    for span in edits {
        for byte in &mut buffer[span.byte_range()] {
            if !matches!(*byte, b'\n' | b'\r') {
                *byte = b' ';
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_edits_preserves_newlines() {
        let source = b"unsafe fn test() {\r\n    let a = 1;\n    let b = 2;\r\n}";
        let mut buffer = source.to_vec();

        let file = syn::parse_file(std::str::from_utf8(source).unwrap()).unwrap();
        let func = match &file.items[0] {
            syn::Item::Fn(f) => f,
            _ => panic!("Expected function"),
        };

        let edits = vec![func.sig.unsafety.unwrap().span(), func.block.span()];

        apply_edits(&mut buffer, &edits);

        let expected = b"       fn test()  \r\n              \n              \r\n ".to_vec();
        assert_eq!(std::str::from_utf8(&buffer).unwrap(), std::str::from_utf8(&expected).unwrap());
    }

    #[test]
    fn test_apply_edits_with_parsed_item() {
        let source = "
            /// ```lean
            /// theorem foo : True := by trivial
            /// ```
            unsafe fn foo() {
                let x = 1;
            }
        ";
        let mut items = Vec::new();
        crate::parse::scan_compilation_unit(source, |_src, res| items.push(res));

        let item = items.into_iter().next().unwrap().unwrap();
        let mut edits = Vec::new();
        append_edits(&item, &mut edits);

        let mut buffer = source.as_bytes().to_vec();
        apply_edits(&mut buffer, &edits);

        let expected = "
            /// ```lean
            /// theorem foo : True := by trivial
            /// ```
                   fn foo()  
                          
             
        ";
        assert_eq!(std::str::from_utf8(&buffer).unwrap(), expected);
    }

    #[test]
    fn test_apply_edits_multibyte_utf8() {
        // Source contains multi-byte characters:
        // - Immediately preceding `unsafe`: `/*前*/`
        // - Immediately following `{`: `/*后*/`
        // - Immediately before `}`: `/*前*/`
        let source = "
            fn safe() {}
            /// ```lean
            /// ```
            /*前*/unsafe fn foo() {/*后*/
                let x = '中';
            /*前*/}
        ";
        let mut items = Vec::new();
        crate::parse::scan_compilation_unit(source, |_src, res| items.push(res));

        // Find the unsafe function (should be the first item, as safe() is skipped)
        let item = items.into_iter().find(|i| {
            if let Ok(ParsedLeanItem { item: ParsedItem::Fn(f), .. }) = i {
                f.sig.ident == "foo"
            } else {
                false
            }
        }).unwrap().unwrap();

        let mut edits = Vec::new();
        append_edits(&item, &mut edits);

        let mut buffer = source.as_bytes().to_vec();
        apply_edits(&mut buffer, &edits);

        // Expected whitespace lengths:
        // Line 1: `            /*前*/unsafe fn foo() {/*后*/`
        // - Indent: 12 spaces
        // - `/*前*/`: 7 bytes (preserved)
        // - `unsafe`: 6 bytes -> 6 spaces
        // - ` fn foo() {`: 9 bytes (preserved)
        // - `/*后*/`: 7 bytes -> 7 spaces
        //
        // Line 2: `                let x = '中';`
        // - Indent: 16 spaces -> 16 spaces
        // - `let x = '中';`: 14 bytes -> 14 spaces
        //   `let` (3) + ` ` (1) + `x` (1) + ` ` (1) + `=` (1) + ` ` (1) + `'` (1) + `中` (3) + `'` (1) + `;` (1) = 14
        //   Total: 30 spaces
        //
        // Line 3: `            /*前*/}`
        // - Indent 12 spaces -> 12 spaces
        // - `/*前*/`: 7 bytes -> 7 spaces
        // - `}`: 1 byte (preserved)
        //   Total: 19 spaces + `}`

        let line_with_unsafe = "            /*前*/       fn foo() {       ";
        let line_body = " ".repeat(30);
        let line_end = format!("{}}}", " ".repeat(19)); 

        let expected = format!(
            "\n            fn safe() {{}}\n            /// ```lean\n            /// ```\n{}\n{}\n{}\n        ",
            line_with_unsafe,
            line_body,
            line_end
        );

        assert_eq!(std::str::from_utf8(&buffer).unwrap(), expected);
    }
}
