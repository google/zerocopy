macro_rules! quote {
    () => (::proc_macro::TokenStream::new());
    ($($x:tt)*) => (quote_internal!([] $($x)*));
}

macro_rules! quote_internal {
    // Base case
    ([]) => (::proc_macro::TokenStream::new());
    ([$($expanded:tt)*]) => {
        [$($expanded)*].iter().cloned().collect::<::proc_macro::TokenStream>()
    };

    // Symbols and symbol pairs
    ([$($expanded:tt)*] :: $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new(':', ::proc_macro::Spacing::Joint)
        )),
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new(':', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] .. $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('.', ::proc_macro::Spacing::Joint)
        )),
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('.', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] : $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new(':', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] = $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('=', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] ; $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new(';', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] , $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new(',', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] . $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('.', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] & $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('&', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] '_ $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('\'', ::proc_macro::Spacing::Joint)
        )),
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Ident::new("_", ::proc_macro::Span::mixed_site())
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] < $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('<', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] > $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Punct::new('>', ::proc_macro::Spacing::Alone)
        )),
    ] $($tail)*));

    // Identifier
    ([$($expanded:tt)*] $i:ident $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(
            ::proc_macro::Ident::new(stringify!($i), ::proc_macro::Span::mixed_site())
        )),
    ] $($tail)*));

    // Groups
    ([$($expanded:tt)*] ($($inner:tt)*) $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(::proc_macro::Group::new(
            ::proc_macro::Delimiter::Parenthesis,
            quote_internal!([] $($inner)*))
        )),
    ] $($tail)*));
    ([$($expanded:tt)*] {$($inner:tt)*} $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(::proc_macro::Group::new(
            ::proc_macro::Delimiter::Brace,
            quote_internal!([] $($inner)*)
        ))),
    ] $($tail)*));
    ([$($expanded:tt)*] [$($inner:tt)*] $($tail:tt)*) => (quote_internal!([$($expanded)*
        ::proc_macro::TokenStream::from(::proc_macro::TokenTree::from(::proc_macro::Group::new(
            ::proc_macro::Delimiter::Bracket,
            quote_internal!([] $($inner)*)
        ))),
    ] $($tail)*));

    // Interpolated values
    ([$($expanded:tt)*] #($e:expr) $($tail:tt)*) => (quote_internal!([$($expanded)*
        $crate::to_tokens::ToTokens::into_token_stream($e),
    ] $($tail)*));
}
