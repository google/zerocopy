use proc_macro::{Group, Ident, Literal, Punct, TokenStream, TokenTree};

pub(crate) trait ToTokens: Sized {
    fn into_token_stream(self) -> TokenStream;
}

impl ToTokens for bool {
    fn into_token_stream(self) -> TokenStream {
        if self { quote!(true) } else { quote!(false) }
    }
}

impl ToTokens for TokenStream {
    fn into_token_stream(self) -> TokenStream {
        self
    }
}

macro_rules! impl_for_tree_types {
    ($($type:ty)*) => {$(
        impl ToTokens for $type {
            fn into_token_stream(self) -> TokenStream {
                TokenStream::from(TokenTree::from(self))
            }
        }
    )*};
}
impl_for_tree_types![Ident Literal Group Punct];

macro_rules! impl_for_int {
    ($($type:ty => $method:ident)*) => {$(
        impl ToTokens for $type {
            fn into_token_stream(self) -> TokenStream {
                TokenStream::from(TokenTree::from(Literal::$method(self)))
            }
        }
    )*};
}
impl_for_int! {
    i8 => i8_unsuffixed
    u8 => u8_unsuffixed
    u16 => u16_unsuffixed
    i32 => i32_unsuffixed
    u32 => u32_unsuffixed
}
