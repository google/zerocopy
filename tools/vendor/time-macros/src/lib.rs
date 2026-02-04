#![deny(
    anonymous_parameters,
    clippy::all,
    const_err,
    illegal_floating_point_literal_pattern,
    late_bound_lifetime_arguments,
    path_statements,
    patterns_in_fns_without_body,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_code,
    unused_extern_crates
)]
#![warn(
    clippy::dbg_macro,
    clippy::decimal_literal_representation,
    clippy::get_unwrap,
    clippy::nursery,
    clippy::pedantic,
    clippy::print_stdout,
    clippy::todo,
    clippy::unimplemented,
    clippy::unwrap_used,
    clippy::use_debug,
    single_use_lifetimes,
    unused_qualifications,
    variant_size_differences
)]
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::missing_const_for_fn,
    clippy::redundant_pub_crate,
    unstable_name_collisions
)]

#[macro_use]
mod quote;

mod date;
mod datetime;
mod error;
mod format_description;
mod helpers;
mod offset;
mod time;
mod to_tokens;

use proc_macro::TokenStream;

use self::date::Date;
use self::datetime::DateTime;
use self::error::Error;
use self::offset::Offset;
use self::time::Time;

macro_rules! impl_macros {
    ($($name:ident : $type:ty)*) => {$(
        #[proc_macro]
        pub fn $name(input: TokenStream) -> TokenStream {
            use crate::to_tokens::ToTokens;

            let mut iter = input.into_iter().peekable();
            match <$type>::parse(&mut iter) {
                Ok(value) => match iter.peek() {
                    Some(tree) => Error::UnexpectedToken { tree: tree.clone() }.to_compile_error(),
                    None => value.into_token_stream(),
                },
                Err(err) => err.to_compile_error(),
            }
        }
    )*};
}

impl_macros! {
    date: Date
    datetime: DateTime
    offset: Offset
    time: Time
}

// TODO Gate this behind the the `formatting` or `parsing` feature flag when weak dependency
// features land.
#[proc_macro]
pub fn format_description(input: TokenStream) -> TokenStream {
    let (span, string) = match helpers::get_string_literal(input) {
        Ok(val) => val,
        Err(err) => return err.to_compile_error(),
    };

    let items = match format_description::parse(&string, span) {
        Ok(items) => items,
        Err(err) => return err.to_compile_error(),
    };

    quote! {{
        const DESCRIPTION: &[::time::format_description::FormatItem<'_>] = &[#(
            items
                .into_iter()
                .map(|item| quote! { #(item), })
                .collect::<TokenStream>()
        )];
        DESCRIPTION
    }}
}
