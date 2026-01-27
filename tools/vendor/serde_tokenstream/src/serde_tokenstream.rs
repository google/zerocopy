// Copyright 2022 Oxide Computer Company

use core::iter::Peekable;
use std::{
    any::type_name,
    fmt::{self, Display},
};

use proc_macro2::{extra::DelimSpan, Delimiter, Group, TokenStream, TokenTree};
use quote::ToTokens;
use serde::de::{
    DeserializeSeed, EnumAccess, MapAccess, SeqAccess, VariantAccess, Visitor,
};
use serde::{Deserialize, Deserializer};
use syn::{ExprLit, Lit};

use crate::ibidem::set_wrapper_tokens;

/// Alias for `syn::Error`.
///
/// `syn::Error` already does the heavy lifting of massaging errors for
/// consumption by the compiler so we lean on that report deserialization
/// errors so that the compiler reports and renders them appropriately.
pub type Error = syn::Error;

/// Alias for a Result with the error type serde_tokenstream::Error.
pub type Result<T> = std::result::Result<T, Error>;

/// Deserialize an instance of type T from a TokenStream.
///
/// # Example
/// ```
/// use quote::quote;
/// use serde::Deserialize;
/// use serde_tokenstream::from_tokenstream;
/// use serde_tokenstream::Result;
///
/// fn main() -> Result<()> {
///     #[derive(Deserialize)]
///     struct Record {
///         worker: String,
///         floor: u32,
///         region: String,
///     }
///     let tokenstream = quote! {
///         worker = "Homer J. Simpson",
///         floor = 7,
///         region = "G",
///     };
///
///     let rec = from_tokenstream::<Record>(&tokenstream)?;
///     println!("{} {}{}", rec.worker, rec.floor, rec.region);
///     Ok(())
/// }
/// ```
pub fn from_tokenstream<'a, T>(tokens: &'a TokenStream) -> Result<T>
where
    T: Deserialize<'a>,
{
    let deserializer = TokenDe::from_tokenstream(None, tokens);
    from_tokenstream_impl(deserializer)
}

/// Deserialize an instance of type T from a TokenStream with data inside,
/// along with a [`DelimSpan`] for the surrounding braces.
///
/// This is useful when parsing an attribute nested inside an outer macro. In
/// that case, better span information (not just `Span::call_site`) can be
/// produced.
///
/// # Example
///
/// The most common use is with [`syn::MetaList`] instances. For example, if
/// your macro is `#[derive(Record)]` and you're invoked like this:
///
/// ```rust,ignore
/// #[derive(Record)]
/// #[record { worker = "Homer J. Simpson", floor = 7, region = "G" }]
/// fn test() {}
/// ```
///
/// Then, the `record` attribute inside can be interpreted as a
/// `syn::MetaList`. With it in hand:
///
/// ```
/// use syn::parse_quote;
/// use serde::Deserialize;
/// use serde_tokenstream::from_tokenstream_spanned;
/// use serde_tokenstream::Result;
///
/// fn main() -> Result<()> {
///     #[derive(Deserialize)]
///     struct Record {
///         worker: String,
///         floor: u32,
///         region: String,
///     }
///
///     // This is the `syn::MetaList` instance above.
///     let list: syn::MetaList = parse_quote! {
///         record {
///             worker = "Homer J. Simpson",
///             floor = 7,
///             region = "G",
///         }
///     };
///
///     let rec = from_tokenstream_spanned::<Record>(list.delimiter.span(), &list.tokens)?;
///     println!("{} {}{}", rec.worker, rec.floor, rec.region);
///     Ok(())
/// }
/// ```
///
/// If there's an error like a missing field, it will now be reported with the
/// span of the braces inside the `record` attribute (whereas
/// [`from_tokenstream`] lacks the necessary [`Span`] information).
///
/// [`Span`]: proc_macro2::Span
pub fn from_tokenstream_spanned<'a, T>(
    span: &DelimSpan,
    tokens: &'a TokenStream,
) -> Result<T>
where
    T: Deserialize<'a>,
{
    let deserializer = TokenDe::from_tokenstream(Some(span), tokens);
    from_tokenstream_impl(deserializer)
}

fn from_tokenstream_impl<'a, T>(mut deserializer: TokenDe) -> Result<T>
where
    T: Deserialize<'a>,
{
    match T::deserialize(&mut deserializer) {
        // On success, check that there aren't additional, unparsed tokens.
        Ok(result) => match deserializer.next() {
            None => Ok(result),
            Some(token) => Err(Error::new(
                token.span(),
                format!("expected EOF but found `{}`", token),
            )),
        },
        // Pass through expected errors.
        Err(InternalError::Normal(err)) => Err(err),

        // Other errors should not be able to reach this point.
        Err(InternalError::NoData(msg)) => panic!(
            "Error::NoData should never propagate to the caller: {}",
            msg
        ),
        Err(InternalError::Unknown) => {
            panic!("Error::Unknown should never propagate to the caller")
        }
    }
}

#[derive(Clone, Debug)]
enum InternalError {
    Normal(Error),
    NoData(String),
    Unknown,
}

type InternalResult<T> = std::result::Result<T, InternalError>;

struct TokenDe {
    input: Peekable<Box<dyn Iterator<Item = TokenTree>>>,
    current: Option<TokenTree>,
    last: Option<TokenTree>,
    pending_member: bool,
}

impl<'de> TokenDe {
    fn from_tokenstream(
        span: Option<&DelimSpan>,
        input: &'de TokenStream,
    ) -> Self {
        // We implicitly start inside a brace-surrounded struct.
        // Constructing a Group allows for more generic handling.
        // If there is an error at the top level (such as a missing field) it
        // will be attributed to the span of the group, which is why we let
        // users optionally include the span for attribution.
        let mut group = Group::new(Delimiter::Brace, input.clone());
        if let Some(span) = span {
            group.set_span(span.join());
        }
        TokenDe::new(&TokenStream::from(TokenTree::from(group)))
    }

    fn new(input: &'de TokenStream) -> Self {
        let t: Box<dyn Iterator<Item = TokenTree>> =
            Box::new(input.clone().into_iter());
        TokenDe {
            input: t.peekable(),
            current: None,
            last: None,
            pending_member: false,
        }
    }

    fn gobble_optional_comma(&mut self) -> InternalResult<()> {
        match self.next() {
            None => Ok(()),
            Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => Ok(()),
            Some(token) => Err(InternalError::Normal(Error::new(
                token.span(),
                format!("expected `,` or nothing, but found `{}`", token),
            ))),
        }
    }

    fn next(&mut self) -> Option<TokenTree> {
        let next = self.input.next();

        self.last =
            std::mem::replace(&mut self.current, next.as_ref().cloned());
        next
    }

    fn previous(&self) -> Option<TokenTree> {
        self.current.clone().or_else(|| self.last.clone())
    }

    fn last_err<T>(&self, what: &str) -> InternalResult<T> {
        match &self.last {
            Some(token) => Err(InternalError::Normal(Error::new(
                token.span(),
                format!("expected {} following `{}`", what, token),
            ))),
            // It should not be possible to reach this point. Although
            // `self.last` starts as `None`, the first thing we'll try to do
            // is deserialize a structure type based on the `Group` we create
            // in `::from_tokenstream`.
            None => Err(InternalError::Unknown),
        }
    }

    fn deserialize_error<VV>(
        &self,
        next: Option<TokenTree>,
        what: &str,
    ) -> InternalResult<VV> {
        match next {
            Some(token) => Err(InternalError::Normal(Error::new(
                token.span(),
                format!("expected {}, but found `{}`", what, token),
            ))),
            None => self.last_err(what),
        }
    }

    fn deserialize_int<T, VV, F>(&mut self, visit: F) -> InternalResult<VV>
    where
        F: FnOnce(T) -> InternalResult<VV>,
        T: std::str::FromStr,
        T::Err: Display,
    {
        let next = self.next();

        let mut stream = Vec::new();

        let next_next = match &next {
            Some(tt @ TokenTree::Punct(p)) if p.as_char() == '-' => {
                stream.push(tt.clone());
                self.next()
            }
            any => any.clone(),
        };

        if let Some(tt) = next_next {
            stream.push(tt);

            if let Ok(i) =
                syn::parse2::<syn::LitInt>(stream.into_iter().collect())
            {
                if let Ok(value) = i.base10_parse::<T>() {
                    return visit(value);
                }
            }
        }

        self.deserialize_error(next, type_name::<T>())
    }

    fn deserialize_float<T, VV, F>(&mut self, visit: F) -> InternalResult<VV>
    where
        F: FnOnce(T) -> InternalResult<VV>,
        T: std::str::FromStr,
        T::Err: Display,
    {
        let next = self.next();

        let mut stream = Vec::new();

        let next_next = match &next {
            Some(tt @ TokenTree::Punct(p)) if p.as_char() == '-' => {
                stream.push(tt.clone());
                self.next()
            }
            any => any.clone(),
        };

        if let Some(tt) = next_next {
            stream.push(tt);

            let parsed =
                match syn::parse2::<ExprLit>(stream.into_iter().collect()) {
                    Ok(ExprLit { lit: Lit::Int(i), .. }) => {
                        i.base10_parse::<T>().ok()
                    }
                    Ok(ExprLit { lit: Lit::Float(f), .. }) => {
                        f.base10_parse::<T>().ok()
                    }
                    _ => None,
                };

            if let Some(value) = parsed {
                return visit(value);
            }
        }

        self.deserialize_error(next, type_name::<T>())
    }
}

impl serde::de::Error for InternalError {
    fn custom<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        InternalError::NoData(format!("{}", msg))
    }
}
impl std::error::Error for InternalError {}

impl Display for InternalError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(format!("{:?}", self).as_str())
    }
}

impl<'de> MapAccess<'de> for TokenDe {
    type Error = InternalError;

    fn next_key_seed<K>(&mut self, seed: K) -> InternalResult<Option<K::Value>>
    where
        K: serde::de::DeserializeSeed<'de>,
    {
        let keytok = match self.input.peek() {
            None => return Ok(None),
            Some(token) => token.clone(),
        };

        let key = seed.deserialize(&mut *self).map(Some);

        // Verify we have an '=' delimiter.
        if key.is_ok() {
            let _eq = match self.next() {
                Some(TokenTree::Punct(punct)) if punct.as_char() == '=' => {
                    punct
                }

                Some(token) => {
                    return Err(InternalError::Normal(Error::new(
                        token.span(),
                        format!("expected `=`, but found `{}`", token),
                    )))
                }
                None => {
                    return Err(InternalError::Normal(Error::new(
                        keytok.span(),
                        format!("expected `=` following `{}`", keytok),
                    )))
                }
            };
        }

        // We expect to have an object member.
        self.pending_member = true;

        key
    }

    fn next_value_seed<V>(&mut self, seed: V) -> InternalResult<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        let valtok = self.input.peek().map(|tok| tok.span());
        let value = seed.deserialize(&mut *self);

        // We've processed the expected member via seed.deserialize.
        self.pending_member = false;

        match &value {
            Ok(_) => {
                self.gobble_optional_comma()?;
            }
            Err(InternalError::NoData(msg)) => {
                if let Some(span) = valtok {
                    return Err(InternalError::Normal(Error::new(span, msg)));
                }
            }
            Err(_) => (),
        }

        value
    }
}

impl<'de> SeqAccess<'de> for TokenDe {
    type Error = InternalError;

    fn next_element_seed<T>(
        &mut self,
        seed: T,
    ) -> InternalResult<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        if self.input.peek().is_none() {
            return Ok(None);
        }
        let value = seed.deserialize(&mut *self).map(Some);
        if value.is_ok() {
            self.gobble_optional_comma()?;
        }
        value
    }
}

impl<'de> EnumAccess<'de> for &mut TokenDe {
    type Error = InternalError;
    type Variant = Self;

    fn variant_seed<V>(
        self,
        seed: V,
    ) -> InternalResult<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        let val = seed.deserialize(&mut *self);

        match val {
            Ok(v) => Ok((v, self)),
            // If there wan an error from serde, tag it with the current token.
            Err(InternalError::NoData(msg)) => match &self.current {
                Some(token) => {
                    Err(InternalError::Normal(Error::new(token.span(), msg)))
                }
                // This can't happen; we will need to have read a token at
                // this point.
                None => Err(InternalError::Unknown),
            },
            Err(err) => Err(err),
        }
    }
}

impl<'de> VariantAccess<'de> for &mut TokenDe {
    type Error = InternalError;

    fn unit_variant(self) -> InternalResult<()> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> InternalResult<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        let next = self.next();

        if let Some(TokenTree::Group(group)) = &next {
            if let Delimiter::Parenthesis = group.delimiter() {
                return seed.deserialize(&mut TokenDe::new(&group.stream()));
            }
        }
        self.deserialize_error(next, "(")
    }

    fn tuple_variant<V>(
        self,
        _len: usize,
        visitor: V,
    ) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(token) = &next {
            if let TokenTree::Group(group) = token {
                if let Delimiter::Parenthesis = group.delimiter() {
                    return match visitor
                        .visit_seq(TokenDe::new(&group.stream()))
                    {
                        Err(InternalError::NoData(msg)) => {
                            Err(InternalError::Normal(Error::new(
                                token.span(),
                                msg,
                            )))
                        }
                        other => other,
                    };
                }
            }
        }

        self.deserialize_error(next, "(")
    }

    fn struct_variant<V>(
        self,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(token) = &next {
            if let TokenTree::Group(group) = token {
                if let Delimiter::Brace = group.delimiter() {
                    // TODO we should pass fields through to the new TokenDe and
                    // then use that rather than the call to
                    // deserialize_ignored_any to determine if the
                    // given field is valid.
                    match visitor.visit_map(TokenDe::new(&group.stream())) {
                        Err(InternalError::NoData(msg)) => {
                            return Err(InternalError::Normal(Error::new(
                                token.span(),
                                msg,
                            )))
                        }
                        other => return other,
                    }
                }
            }
        };

        self.deserialize_error(next, "{")
    }
}

/// Stub out Deserializer trait functions we don't want to deal with right now.
macro_rules! de_unimp {
    ($i:ident $(, $p:ident : $t:ty )*) => {
        fn $i<V>(self $(, $p: $t)*, _visitor: V) -> InternalResult<V::Value>
        where
            V: Visitor<'de>,
        {
            unimplemented!(stringify!($i));
        }
    };
    ($i:ident $(, $p:ident : $t:ty )* ,) => {
        de_unimp!($i $(, $p: $t)*);
    };
}

impl<'de, 'a> Deserializer<'de> for &'a mut TokenDe {
    type Error = InternalError;

    fn deserialize_bool<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.next() {
            Some(TokenTree::Ident(ident)) if ident == "true" => {
                visitor.visit_bool(true)
            }
            Some(TokenTree::Ident(ident)) if ident == "false" => {
                visitor.visit_bool(false)
            }
            other => self.deserialize_error(other, "bool"),
        }
    }

    fn deserialize_option<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        // None is a missing field, so this must be Some.
        visitor.visit_some(self)
    }

    fn deserialize_string<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let token = self.next();
        let value = match &token {
            Some(TokenTree::Ident(ident)) => Some(ident.to_string()),
            Some(tt) => {
                match syn::parse2::<syn::LitStr>(TokenStream::from(tt.clone()))
                {
                    Ok(s) => Some(s.value()),
                    _ => None,
                }
            }
            _ => None,
        };

        value.map_or_else(
            || self.deserialize_error(token, "a string"),
            |v| visitor.visit_string(v),
        )
    }
    fn deserialize_str<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_seq<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(token) = &next {
            if let TokenTree::Group(group) = token {
                if let Delimiter::Bracket = group.delimiter() {
                    return match visitor
                        .visit_seq(TokenDe::new(&group.stream()))
                    {
                        Err(InternalError::NoData(msg)) => {
                            Err(InternalError::Normal(Error::new(
                                token.span(),
                                msg,
                            )))
                        }
                        other => other,
                    };
                }
            }
        }

        self.deserialize_error(next, "an array")
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(token) = &next {
            if let TokenTree::Group(group) = token {
                if let Delimiter::Brace = group.delimiter() {
                    // TODO we should pass fields through to the new TokenDe and
                    // then use that rather than the call to
                    // deserialize_ignored_any to determine if the
                    // given field is valid.
                    match visitor.visit_map(TokenDe::new(&group.stream())) {
                        Err(InternalError::NoData(msg)) => {
                            return Err(InternalError::Normal(Error::new(
                                token.span(),
                                msg,
                            )))
                        }
                        other => return other,
                    }
                }
            }
        };

        self.deserialize_error(next, "a struct")
    }

    fn deserialize_map<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(TokenTree::Group(group)) = &next {
            if let Delimiter::Brace = group.delimiter() {
                return visitor.visit_map(TokenDe::new(&group.stream()));
            }
        }

        self.deserialize_error(next, "a map")
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_enum(self)
    }

    fn deserialize_identifier<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(ident @ TokenTree::Ident(_)) = next {
            return visitor.visit_string(ident.to_string());
        }

        self.deserialize_error(next, "an identifier")
    }

    fn deserialize_char<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(tt) = &next {
            if let Ok(ch) =
                syn::parse2::<syn::LitChar>(TokenStream::from(tt.clone()))
            {
                return visitor.visit_char(ch.value());
            }
        }

        self.deserialize_error(next, "a char")
    }

    fn deserialize_unit<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(TokenTree::Group(group)) = &next {
            if let Delimiter::Parenthesis = group.delimiter() {
                if group.stream().is_empty() {
                    return visitor.visit_unit();
                }
            }
        }

        self.deserialize_error(next, "a unit")
    }

    fn deserialize_tuple<V>(
        self,
        _len: usize,
        visitor: V,
    ) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        if let Some(token) = &next {
            if let TokenTree::Group(group) = token {
                if let Delimiter::Parenthesis = group.delimiter() {
                    return match visitor
                        .visit_seq(TokenDe::new(&group.stream()))
                    {
                        Err(InternalError::NoData(msg)) => {
                            Err(InternalError::Normal(Error::new(
                                token.span(),
                                msg,
                            )))
                        }
                        other => other,
                    };
                }
            }
        }

        self.deserialize_error(next, "a tuple")
    }

    fn deserialize_any<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let token = self.next();

        match &token {
            None => self.last_err("a value"),
            Some(TokenTree::Group(group)) => match group.delimiter() {
                Delimiter::Brace => {
                    visitor.visit_map(TokenDe::new(&group.stream()))
                }
                Delimiter::Bracket => {
                    visitor.visit_seq(TokenDe::new(&group.stream()))
                }
                Delimiter::Parenthesis => {
                    let stream = &group.stream();
                    if stream.is_empty() {
                        visitor.visit_unit()
                    } else {
                        visitor.visit_seq(TokenDe::new(stream))
                    }
                }
                // A None delimiter occurs for a macro_rules! substitution. We
                // can simply descend into those tokens.
                Delimiter::None => {
                    TokenDe::new(&group.stream()).deserialize_any(visitor)
                }
            },
            Some(TokenTree::Ident(ident)) if *ident == "true" => {
                visitor.visit_bool(true)
            }
            Some(TokenTree::Ident(ident)) if *ident == "false" => {
                visitor.visit_bool(false)
            }
            Some(TokenTree::Ident(ident)) => {
                visitor.visit_string(ident.to_string())
            }
            Some(tt @ TokenTree::Literal(_)) => {
                match syn::parse2::<ExprLit>(TokenStream::from(tt.clone())) {
                    Ok(ExprLit { lit: Lit::Str(s), .. }) => {
                        visitor.visit_string(s.value())
                    }
                    Ok(ExprLit { lit: Lit::Byte(_), .. }) => todo!("byte"),
                    Ok(ExprLit { lit: Lit::Char(ch), .. }) => {
                        visitor.visit_char(ch.value())
                    }
                    Ok(ExprLit { lit: Lit::Int(i), .. }) => {
                        visitor.visit_u64(i.base10_parse::<u64>().or_else(
                            |_| self.deserialize_error(token, "an integer"),
                        )?)
                    }
                    Ok(ExprLit { lit: Lit::Float(f), .. }) => visitor
                        .visit_f64(f.base10_parse::<f64>().or_else(|_| {
                            self.deserialize_error(token, "a float")
                        })?),
                    Ok(ExprLit { lit: Lit::Bool(_), .. }) => {
                        unreachable!("bool is handled elsewhere");
                    }
                    Ok(expr @ ExprLit { .. }) => {
                        todo!(
                            "unhandled expr {}",
                            expr.to_token_stream().to_string(),
                        );
                    }
                    Err(err) => {
                        unreachable!("must be parseable: {} {}", tt, err)
                    }
                }
            }

            Some(neg @ TokenTree::Punct(p)) if p.as_char() == '-' => {
                if let Some(next) = self.next() {
                    let stream = [neg, &next]
                        .into_iter()
                        .cloned()
                        .collect::<TokenStream>();
                    match syn::parse2::<ExprLit>(stream) {
                        Ok(ExprLit { lit: Lit::Int(i), .. }) => {
                            return visitor.visit_i64(
                                i.base10_parse::<i64>().or_else(|_| {
                                    self.deserialize_error(token, "an integer")
                                })?,
                            )
                        }
                        Ok(ExprLit { lit: Lit::Float(f), .. }) => {
                            return visitor.visit_f64(
                                f.base10_parse::<f64>().or_else(|_| {
                                    self.deserialize_error(token, "a float")
                                })?,
                            )
                        }
                        _ => (),
                    }
                }

                self.deserialize_error(token, "a value")
            }
            Some(TokenTree::Punct(_)) => {
                self.deserialize_error(token, "a value")
            }
        }
    }

    fn deserialize_i8<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_i8(value))
    }
    fn deserialize_i16<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_i16(value))
    }
    fn deserialize_i32<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_i32(value))
    }
    fn deserialize_i64<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_i64(value))
    }
    fn deserialize_i128<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_i128(value))
    }
    fn deserialize_u8<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_u8(value))
    }
    fn deserialize_u16<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_u16(value))
    }
    fn deserialize_u32<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_u32(value))
    }
    fn deserialize_u64<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_u64(value))
    }
    fn deserialize_u128<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_int(|value| visitor.visit_u128(value))
    }

    fn deserialize_f32<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_float(|value| visitor.visit_f32(value))
    }
    fn deserialize_f64<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_float(|value| visitor.visit_f64(value))
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        if !self.pending_member {
            // If this isn't the direct value of an unexpected key, then just
            // process the value.
            self.deserialize_any(visitor)
        } else {
            // If we're expecting a member, this is going to be an error that we
            // want to highlight. We'll identify this error and any error we may
            // encounter while processing the value.

            // Save the token corresponding to the member name.
            let keytok = match self.last.clone() {
                Some(token) => token,
                // This can't happen -- we need to have read a token in order
                // for serde to determine that this value will
                // be ignored.
                None => return Err(InternalError::Unknown),
            };

            // We know this is going to be an error, but we parse the value
            // anyways to see if that *also* produces an error we can report to
            // the user.
            let value = self.deserialize_any(visitor);

            let msg = format!("extraneous member `{}`", &keytok);

            // Create a dummy token stream that contains the token corresponding
            // to the key and the last token we read. Error::new_spanned() just
            // looks at the first and last tokens in the stream.
            let mut ts = TokenStream::new();
            ts.extend(vec![keytok, self.previous().unwrap()]);

            // Create an error that underlines key, =, and value.
            let mut err = Error::new_spanned(ts, msg);

            // Add in the value error if there was one.
            if let Err(InternalError::Normal(e2)) = value {
                err.combine(e2);
            }

            Err(InternalError::Normal(err))
        }
    }

    // This isn't really attempting to deserialize bytes -- it merely acts as a
    // signal to pass through a TokenStream unperturbed. See the comment on
    // `WrapperVisitor` in `ibidem.rs` for more information.
    fn deserialize_bytes<V>(self, visitor: V) -> InternalResult<V::Value>
    where
        V: Visitor<'de>,
    {
        let next = self.next();

        // TODO format a spanned error of some sort
        let mut token = match &next {
            None => {
                return self
                    .deserialize_error(next, "anything but a ',', '=', or EOF")
            }
            Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => {
                return self
                    .deserialize_error(next, "anything but a ',', '=', or EOF")
            }
            Some(TokenTree::Punct(punct)) if punct.as_char() == '=' => {
                return self
                    .deserialize_error(next, "anything but a ',', '=', or EOF")
            }
            Some(token) => token.clone(),
        };

        // Gather the tokens up to the next ',', '=', or EOF.
        let mut tokens = Vec::new();
        loop {
            tokens.push(token);

            token = match self.input.peek() {
                None => break,
                Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => {
                    break
                }
                Some(TokenTree::Punct(punct)) if punct.as_char() == '=' => {
                    break
                }
                Some(_) => self.next().unwrap(),
            };
        }

        set_wrapper_tokens(tokens);
        visitor.visit_bytes(&[])
    }

    de_unimp!(deserialize_byte_buf);
    de_unimp!(deserialize_unit_struct, _name: &'static str);
    de_unimp!(deserialize_newtype_struct, _name: &'static str);
    de_unimp!(deserialize_tuple_struct, _name: &'static str, _len: usize);
}

#[cfg(test)]
mod tests {
    use crate::{ibidem::TokenStreamWrapper, ParseWrapper};

    use super::*;
    use quote::{quote, ToTokens};
    use std::collections::HashMap;

    #[derive(Clone, Debug, Deserialize)]
    #[serde(untagged)]
    #[allow(dead_code)]
    enum MapEntry {
        Value(String),
        Struct(MapData),
        Array(Vec<MapEntry>),
    }

    type MapData = HashMap<String, MapEntry>;

    fn compare_kv(k: Option<&MapEntry>, v: &str) {
        match k {
            Some(MapEntry::Value(s)) => assert_eq!(s, v),
            _ => panic!("incorrect value"),
        }
    }

    #[test]
    fn simple_map1() -> Result<()> {
        let data = from_tokenstream::<MapData>(&quote! {
            "potato" = potato
        })?;

        compare_kv(data.get("potato"), "potato");

        Ok(())
    }

    #[test]
    fn simple_map2() -> Result<()> {
        let data = from_tokenstream::<MapData>(&quote! {
            "potato" = potato,
            lizzie = "lizzie",
            brickley = brickley,
            "bug" = "bug"
        })?;

        compare_kv(data.get("potato"), "potato");
        compare_kv(data.get("lizzie"), "lizzie");
        compare_kv(data.get("brickley"), "brickley");
        compare_kv(data.get("bug"), "bug");

        Ok(())
    }

    #[test]
    fn bad_ident() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            potato: String,
        }
        match from_tokenstream::<Test>(&quote! {
            "potato" = potato
        }) {
            Err(err) => {
                assert_eq!(
                    err.to_string(),
                    "expected an identifier, but found `\"potato\"`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn just_ident() {
        match from_tokenstream::<MapData>(&quote! {
            howdy
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected `=` following `howdy`")
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn no_equals() {
        match from_tokenstream::<MapData>(&quote! {
            hi there
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected `=`, but found `there`")
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn paren_grouping() {
        match from_tokenstream::<MapData>(&quote! {
            hi = ()
        }) {
            Err(msg) => assert_eq!(
                msg.to_string(),
                "data did not match any variant of untagged enum MapEntry"
            ),
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn no_value() {
        match from_tokenstream::<MapData>(&quote! {
            x =
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected a value following `=`")
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn no_value2() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            x: String,
        }
        match from_tokenstream::<Test>(&quote! {
            x =
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected a string following `=`")
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn simple() {
        #[derive(Deserialize)]
        struct Test {
            hi: String,
        }
        let m = from_tokenstream::<Test>(&quote! {
            hi = there
        })
        .unwrap();

        assert_eq!(m.hi, "there");
    }

    #[test]
    fn simple2() {
        #[derive(Deserialize)]
        struct Test {
            message: String,
        }
        let m = from_tokenstream::<Test>(&quote! {
            message = "hi there"
        })
        .unwrap();
        assert_eq!(m.message, "hi there");
    }
    #[test]
    fn trailing_comma() {
        #[derive(Deserialize)]
        struct Test {
            hi: String,
        }
        let m = from_tokenstream::<Test>(&quote! {
            hi = there,
        })
        .unwrap();
        assert_eq!(m.hi, "there");
    }

    #[test]
    fn double_comma() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            hi: String,
        }
        match from_tokenstream::<Test>(&quote! {
            hi = there,,
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "expected an identifier, but found `,`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_value() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            wat: String,
        }
        match from_tokenstream::<Test>(&quote! {
            wat = ?
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected a string, but found `?`");
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_value2() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            the_meaning_of_life_the_universe_and_everything: String,
        }
        match from_tokenstream::<Test>(&quote! {
            the_meaning_of_life_the_universe_and_everything = 42
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "expected a string, but found `42`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_value3() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            a: (),
        }
        match from_tokenstream::<Test>(&quote! {
            a = 7,
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected a unit, but found `7`");
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_map_value() {
        match from_tokenstream::<MapData>(&quote! {
            wtf = [ ?! ]
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected a value, but found `?`")
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn extra_member1() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            a: String,
        }
        match from_tokenstream::<Test>(&quote! {
            b = 42,
            a = "howdy",
        }) {
            Err(msg) => assert_eq!(msg.to_string(), "extraneous member `b`"),
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn extra_member2() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            a: String,
        }
        match from_tokenstream::<Test>(&quote! {
            b = ?,
            a = "howdy",
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "extraneous member `b`");
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn simple_array1() {
        #[derive(Deserialize)]
        struct Test {
            array: Vec<u32>,
        }
        let t = from_tokenstream::<Test>(&quote! {
            array = []
        })
        .unwrap();
        assert!(t.array.is_empty());
    }

    #[test]
    fn simple_array2() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            array: Vec<u32>,
        }
        match from_tokenstream::<Test>(&quote! {
            array = [1, 2, 3]
        }) {
            Ok(t) => assert_eq!(t.array[0], 1),
            Err(err) => panic!("unexpected failure: {:?}", err),
        }
    }

    #[test]
    fn simple_array3() {
        #[derive(Deserialize)]
        struct Test {
            array: Vec<Test2>,
        }
        #[derive(Deserialize)]
        struct Test2 {}
        let t = from_tokenstream::<Test>(&quote! {
            array = [{}]
        })
        .unwrap();
        assert_eq!(t.array.len(), 1);
    }

    #[test]
    fn simple_array4() {
        #[derive(Deserialize)]
        struct Test {
            array: Vec<Test2>,
        }
        #[derive(Deserialize)]
        struct Test2 {}
        let t = from_tokenstream::<Test>(&quote! {
            array = [{}, {},]
        })
        .unwrap();
        assert_eq!(t.array.len(), 2);
    }

    #[test]
    fn bad_array1() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            array: Vec<Test2>,
        }
        #[derive(Deserialize)]
        struct Test2 {}
        match from_tokenstream::<Test>(&quote! {
            array = [{}<-]
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "expected `,` or nothing, but found `<`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_array2() {
        match from_tokenstream::<MapData>(&quote! {
            array = [{}<-]
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "expected `,` or nothing, but found `<`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_array3() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            array: Vec<Test2>,
        }
        #[derive(Deserialize)]
        struct Test2 {}
        match from_tokenstream::<Test>(&quote! {
            array = {}
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "expected an array, but found `{ }`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_array4() {
        match from_tokenstream::<MapData>(&quote! {
            array = [,]
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected a value, but found `,`");
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_enum() {
        #[derive(Deserialize)]
        enum Foo {
            Foo,
        }
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            foo: Foo,
        }
        match from_tokenstream::<Test>(&quote! {
            foo = Foop
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "unknown variant `Foop`, expected `Foo`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_enum2() {
        #[derive(Deserialize)]
        enum Foo {
            Foo,
        }
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            foo: Foo,
        }
        match from_tokenstream::<Test>(&quote! {
            foo =
        }) {
            Err(msg) => {
                assert_eq!(
                    msg.to_string(),
                    "expected an identifier following `=`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_enum3() {
        #[derive(Deserialize)]
        #[allow(dead_code)]
        enum Foo {
            Foo(u32),
        }
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            foo: Foo,
        }
        match from_tokenstream::<Test>(&quote! {
            foo = Foo
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected ( following `Foo`");
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn bad_enum4() {
        #[derive(Deserialize)]
        enum Foo {
            #[allow(dead_code)]
            Foo { foo: u32 },
        }
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            foo: Foo,
        }
        match from_tokenstream::<Test>(&quote! {
            foo = Foo
        }) {
            Err(msg) => {
                assert_eq!(msg.to_string(), "expected { following `Foo`");
            }
            Ok(_) => panic!("unexpected success"),
        }
    }

    #[test]
    fn tuple() {
        #[derive(Deserialize)]
        struct Test {
            #[allow(dead_code)]
            tup: (u32, u32),
        }
        match from_tokenstream::<Test>(&quote! {
            tup = (1, 2)
        }) {
            Ok(t) => assert_eq!(t.tup.1, 2),
            Err(err) => panic!("unexpected failure: {:?}", err),
        }
    }

    fn make_null_group() -> TokenStream {
        // If a consumer uses macro_rules! to specify an expression it will be
        // enclosed in a group with the None delimiter -- effectively an
        // invisible grouping. The constructs that case.
        let group = proc_macro2::Group::new(
            proc_macro2::Delimiter::None,
            quote! {
                "some string"
            },
        );

        quote! {
            s = #group
        }
    }

    #[test]
    fn null_group() {
        #[derive(Deserialize)]
        struct Test {
            s: String,
        }
        match from_tokenstream::<Test>(&make_null_group()) {
            Ok(t) => assert_eq!(t.s, "some string"),
            Err(err) => panic!("unexpected failure: {:?}", err),
        }
    }

    #[test]
    fn null_group_map() -> Result<()> {
        let data = from_tokenstream::<MapData>(&make_null_group())?;

        compare_kv(data.get("s"), "some string");

        Ok(())
    }

    #[test]
    fn int_as_float() {
        #[derive(Deserialize)]
        struct Test {
            x: f64,
        }
        match from_tokenstream::<Test>(&quote! {
            x = 100
        }) {
            Ok(t) => assert_eq!(t.x, 100.0),
            Err(err) => panic!("unexpected failure: {:?}", err),
        };
    }

    #[test]
    fn extra_member_and_bad_value1() {
        #[derive(Deserialize)]
        struct Test {}
        match from_tokenstream::<Test>(&quote! {
            family = ["homer", "marge", "bart", "lisa", "maggie",,]
        }) {
            Err(err) => {
                let errs = err.into_iter().collect::<Vec<_>>();
                assert_eq!(errs[0].to_string(), "extraneous member `family`");
                assert_eq!(
                    errs[1].to_string(),
                    "expected a value, but found `,`"
                );
            }
            Ok(_) => panic!("unexpected success"),
        };
    }

    #[test]
    fn test_numbers() {
        #[derive(Deserialize)]
        #[allow(unused)]
        struct Test {
            pos_i: u64,
            neg_i: i32,
            pos_f: f32,
            neg_f: f64,
        }
        let v = from_tokenstream::<Test>(&quote! {
            pos_i = 0x42,
            neg_i = -2147483648,
            pos_f = 1_000,
            neg_f = -10.0,
        })
        .unwrap();
        assert_eq!(v.pos_i, 0x42);
        assert_eq!(v.neg_i, -2147483648);
        assert_eq!(v.pos_f, 1000.0);
        assert_eq!(v.neg_f, -10.0);

        #[derive(Deserialize)]
        #[allow(unused)]
        struct FlatTest {
            #[serde(flatten)]
            test: Test,
        }
        let v = from_tokenstream::<FlatTest>(&quote! {
            pos_i = 42,
            neg_i = -2147483648,
            pos_f = 1e11,
            neg_f = -1e101,
        })
        .unwrap();
        assert_eq!(v.test.pos_i, 42);
        assert_eq!(v.test.neg_i, -2147483648);
        assert_eq!(v.test.pos_f, 1e11);
        assert_eq!(v.test.neg_f, -1e101);
    }

    enum ClosureOrPath {
        Closure(syn::ExprClosure),
        Path(syn::Path),
    }

    impl syn::parse::Parse for ClosureOrPath {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let lookahead = input.lookahead1();

            if lookahead.peek(syn::token::Paren) {
                let group: proc_macro2::Group = input.parse()?;
                return syn::parse2::<Self>(group.stream());
            }

            if let Ok(closure) = input.parse::<syn::ExprClosure>() {
                return Ok(Self::Closure(closure));
            }

            input.parse::<syn::Path>().map(Self::Path)
        }
    }

    impl ClosureOrPath {
        fn to_token_stream(&self) -> proc_macro2::TokenStream {
            match self {
                ClosureOrPath::Closure(c) => c.to_token_stream(),
                ClosureOrPath::Path(p) => p.to_token_stream(),
            }
        }
    }

    #[test]
    fn test_token_stream_wrapper() {
        #[derive(Deserialize)]
        struct Stuff {
            pre_tokens: ParseWrapper<ClosureOrPath>,
            text: String,
            post_tokens: Option<ParseWrapper<ClosureOrPath>>,
            no_tokens: Option<TokenStreamWrapper>,
            things: Vec<ParseWrapper<syn::Path>>,
        }

        let Stuff { pre_tokens, text, post_tokens, no_tokens, things } =
            from_tokenstream::<Stuff>(&quote! {
                text = "howdy",
                pre_tokens = (|a, b, c, d| { let _ = todo!(); }),
                post_tokens = word,
                things = [ serde::Serialize, JsonSchema ],
            })
            .unwrap();

        assert_eq!(
            pre_tokens.to_token_stream().to_string(),
            quote! { |a, b, c, d| { let _ = todo!(); } }.to_string()
        );
        assert_eq!(text, "howdy");
        assert_eq!(
            post_tokens.unwrap().to_token_stream().to_string(),
            quote! { word }.to_string()
        );
        assert!(no_tokens.is_none());
        assert_eq!(
            things[0].to_token_stream().to_string(),
            quote! { serde::Serialize }.to_string()
        );
        assert_eq!(
            things[1].to_token_stream().to_string(),
            quote! { JsonSchema }.to_string()
        );
    }

    #[test]
    fn test_enum() {
        #![allow(dead_code)]

        #[derive(Debug, Deserialize, PartialEq, Eq)]
        enum Thing {
            A,
            B(String),
            C(String, String),
            D { d: String },
        }

        #[derive(Debug, Deserialize)]
        struct Things {
            thing: Thing,
        }

        let a = from_tokenstream::<Things>(&quote! {
            thing = A,
        })
        .unwrap();
        assert_eq!(a.thing, Thing::A);

        let b = from_tokenstream::<Things>(&quote! {
            thing = B("b"),
        })
        .unwrap();
        assert_eq!(b.thing, Thing::B("b".to_string()));

        let c = from_tokenstream::<Things>(&quote! {
            thing = C("cc", "ccc"),
        })
        .unwrap();
        assert_eq!(c.thing, Thing::C("cc".to_string(), "ccc".to_string()));

        let d = from_tokenstream::<Things>(&quote! {
            thing = D { d = "d" },
        })
        .unwrap();
        assert_eq!(d.thing, Thing::D { d: "d".to_string() });
    }

    // Make sure ParseWrapper<syn::Type> is Hash
    #[test]
    fn test_parse_wrapper_hash() {
        #[derive(Deserialize)]
        struct Input {
            #[allow(dead_code)]
            patch: HashMap<ParseWrapper<syn::Ident>, Value>,
        }
        #[derive(Deserialize)]
        struct Value {
            #[allow(dead_code)]
            value: String,
        }

        let _ = from_tokenstream::<Input>(&quote! {
            patch = {
                A = { value = "a" },
                B = { value = "b" },
            }
        })
        .unwrap();
    }

    #[test]
    fn parse_u128() {
        #[derive(Deserialize)]
        struct Test {
            a: u128,
            b: u128,
            c: u128,
        }

        let t = from_tokenstream::<Test>(&quote! {
            a = 0,
            b = 18446744073709551616,
            c = 340282366920938463463374607431768211455,
        })
        .unwrap();
        assert_eq!(t.a, 0);
        assert_eq!(t.b, 18446744073709551616);
        assert_eq!(t.c, 340282366920938463463374607431768211455);
    }

    #[test]
    fn parse_i128() {
        #[derive(Deserialize)]
        struct Test {
            a: i128,
            b: i128,
            c: i128,
            d: i128,
        }

        let t = from_tokenstream::<Test>(&quote! {
            a = -170141183460469231731687303715884105728,
            b = -9223372036854775809,
            c = 9223372036854775808,
            d = 170141183460469231731687303715884105727,
        })
        .unwrap();
        assert_eq!(t.a, -170141183460469231731687303715884105728);
        assert_eq!(t.b, -9223372036854775809);
        assert_eq!(t.c, 9223372036854775808);
        assert_eq!(t.d, 170141183460469231731687303715884105727);
    }
}
