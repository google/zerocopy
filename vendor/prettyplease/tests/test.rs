use indoc::indoc;
use proc_macro2::{Delimiter, Group, TokenStream};
use quote::quote;

#[track_caller]
fn test(tokens: TokenStream, expected: &str) {
    let syntax_tree: syn::File = syn::parse2(tokens).unwrap();
    let pretty = prettyplease::unparse(&syntax_tree);
    assert_eq!(pretty, expected);
}

#[test]
fn test_parenthesize_cond() {
    let s = Group::new(Delimiter::None, quote!(Struct {}));
    test(
        quote! {
            fn main() {
                if #s == #s {}
            }
        },
        indoc! {"
            fn main() {
                if (Struct {} == Struct {}) {}
            }
        "},
    );
}

#[test]
fn test_parenthesize_match_guard() {
    let expr_struct = Group::new(Delimiter::None, quote!(Struct {}));
    let expr_binary = Group::new(Delimiter::None, quote!(true && false));
    test(
        quote! {
            fn main() {
                match () {
                    () if let _ = #expr_struct => {}
                    () if let _ = #expr_binary => {}
                }
            }
        },
        // FIXME: no parens around `Struct {}` because anything until the `=>`
        // is considered part of the match guard expression. Parsing of the
        // expression is not terminated by `{` in that position.
        //
        // FIXME: the `true && false` needs parens. Otherwise the precedence is
        // `(let _ = true) && false` which means something different.
        indoc! {"
            fn main() {
                match () {
                    () if let _ = (Struct {}) => {}
                    () if let _ = true && false => {}
                }
            }
        "},
    );
}
