// Copyright 2022 Oxide Computer Company

use std::cell::RefCell;

use proc_macro2::{TokenStream, TokenTree};
use serde::{de::Error, de::Visitor, Deserialize};

/// A Wrapper around proc_macro2::TokenStream that is Deserializable, albeit
/// only in the context of from_tokenstream(). You can use this if, say, your
/// macro allows users to pass in Rust tokens as a configuration option. This
/// can be useful, for example, in a macro that generates code where the caller
/// of that macro might want to augment the generated code.
#[derive(Debug)]
pub struct TokenStreamWrapper(TokenStream);

impl TokenStreamWrapper {
    pub fn into_inner(self) -> TokenStream {
        self.0
    }
}

impl<'de> Deserialize<'de> for TokenStreamWrapper {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self(deserializer.deserialize_bytes(WrapperVisitor)?))
    }
}

impl std::ops::Deref for TokenStreamWrapper {
    type Target = TokenStream;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A wrapper around the syn::parse::Parse trait that is Deserializable, albeit
/// only in the context of from_tokenstream(). This extends
/// [TokenStreamWrapper] by further interpreting the TokenStream and guiding
/// the user in the case of parse errors.
#[derive(Debug, Hash, Eq, PartialEq)]
pub struct ParseWrapper<P: syn::parse::Parse>(P);

impl<P: syn::parse::Parse> ParseWrapper<P> {
    pub fn into_inner(self) -> P {
        self.0
    }
}

impl<'de, P: syn::parse::Parse> Deserialize<'de> for ParseWrapper<P> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let token_stream = deserializer.deserialize_bytes(WrapperVisitor)?;

        Ok(Self(syn::parse2::<P>(token_stream).map_err(D::Error::custom)?))
    }
}

impl<P: syn::parse::Parse> std::ops::Deref for ParseWrapper<P> {
    type Target = P;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// We would like to be able to pass `TokenStream`s through unperturbed, but
/// that isn't directly possible with serde's model, because
/// serde--wisely--does not permit this kind of unholy communion between
/// Deserialize and Deserializer.
///
/// However, we can skirt around this with the otherwise-unused
/// deserialize_bytes/visit_bytes interfaces. Since there is no `TokenStream`
/// that could reasonably be interpreted as bytes, we use this interface to
/// signal to the `serde_tokenstream` deserializer that we should be
/// interpreting the TokenStream directly.
///
/// The mechanism works via a thread-local storage (TLS) side channel. When we
/// want to interpret a TokenStream directly:
///
/// 1. First, `TokenStreamWrapper` or `ParseWrapper` calls
///    `deserializer.deserialize_bytes(WrapperVisitor)`, assuming that
///    `deserializer` is always the `serde_tokenstream` deserializer.
/// 2. The `serde_tokenstream` deserializer calls `set_wrapper_tokens` with the
///    `TokenStream`.
/// 3. The `serde_tokenstream` deserializer calls `visitor.visit_bytes`, which
///    is always the `WrapperVisitor`.
/// 4. The `WrapperVisitor` deserializer immediately calls
///    `take_wrapper_tokens` to retrieve the `TokenStream`.
///
/// So, yes: this is ick. However, unlike some alternatives like serializing
/// TokenStreams to bytes, this approach allows us to retain Span information.
/// In turn, that allows us to craft very good, targeted errors to guide users
/// in the case of bad input.
struct WrapperVisitor;

impl<'de> Visitor<'de> for WrapperVisitor {
    type Value = TokenStream;

    fn expecting(
        &self,
        formatter: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        formatter.write_str("TokenStream")
    }

    fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        assert!(
            bytes.is_empty(),
            "visit_bytes should always be called with an empty slice \
             (a side channel is used to pass the actual TokenStream;
             was TokenStreamWrapper or ParseWrapper used outside of a
             serde_tokenstream context?)"
        );
        Ok(take_wrapper_tokens())
    }
}

thread_local! {
    // This acts as a side channel to pass information around between
    // visit_bytes and deserialize_bytes. It's fine...
    //
    // Instead of a `Vec<TokenStream>` representing a stack, it's okay to use a
    // single Option here because we read data back from it immediately after
    // writing to it. The order of operations is as follows:
    //
    // 1. `deserialize_bytes` in `serde_tokenstream.rs` calls
    //    `set_wrapper_tokens`.
    // 2. `deserialize_bytes` calls `WrapperVisitor::visit_bytes` immediately
    //    afterwards.
    // 3. `visit_bytes` calls `take_wrapper_tokens` to retrieve the tokens.
    // 4. Only after that does any potential syn parsing of the token stream
    //    occur.
    //
    // Because this set/take sequence is immediate without anything in between,
    // there's no nesting to be worried about.
    static WRAPPER_TOKENS: RefCell<Option<TokenStream>> = Default::default();
}

pub(crate) fn set_wrapper_tokens(tokens: Vec<TokenTree>) {
    WRAPPER_TOKENS.with(|cell| {
        let mut cell = cell.borrow_mut();
        assert!(cell.is_none(), "set_wrapper_tokens requires TLS to be unset");
        *cell = Some(tokens.into_iter().collect());
    });
}

fn take_wrapper_tokens() -> TokenStream {
    WRAPPER_TOKENS.with(|cell| {
        cell.borrow_mut().take().expect(
            "take_wrapper_tokens requires TLS to be set \
             (was TokenStreamWrapper or ParseWrapper used
             outside of a serde_tokenstream context?)",
        )
    })
}
