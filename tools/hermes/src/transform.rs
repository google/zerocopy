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
            if *byte != b'\n' && *byte != b'\r' {
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
}
