// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use core::fmt::{self, Display, Formatter};

use {
    proc_macro2::Span,
    syn::punctuated::Punctuated,
    syn::spanned::Spanned,
    syn::token::Comma,
    syn::{Attribute, DeriveInput, Error, LitInt, Meta},
};

pub struct Config<Repr: KindRepr> {
    // A human-readable message describing what combinations of representations
    // are allowed. This will be printed to the user if they use an invalid
    // combination.
    pub allowed_combinations_message: &'static str,
    // Whether we're checking as part of `derive(Unaligned)`. If not, we can
    // ignore `repr(align)`, which makes the code (and the list of valid repr
    // combinations we have to enumerate) somewhat simpler. If we're checking
    // for `Unaligned`, then in addition to checking against illegal
    // combinations, we also check to see if there exists a `repr(align(N > 1))`
    // attribute.
    pub derive_unaligned: bool,
    // Combinations which are valid for the trait.
    pub allowed_combinations: &'static [&'static [Repr]],
    // Combinations which are not valid for the trait, but are legal according
    // to Rust. Any combination not in this or `allowed_combinations` is either
    // illegal according to Rust or the behavior is unspecified. If the behavior
    // is unspecified, it might become specified in the future, and that
    // specification might not play nicely with our requirements. Thus, we
    // reject combinations with unspecified behavior in addition to illegal
    // combinations.
    pub disallowed_but_legal_combinations: &'static [&'static [Repr]],
}

impl<R: KindRepr> Config<R> {
    /// Validate that `input`'s representation attributes conform to the
    /// requirements specified by this `Config`.
    ///
    /// `validate_reprs` extracts the `repr` attributes, validates that they
    /// conform to the requirements of `self`, and returns them. Regardless of
    /// whether `align` attributes are considered during validation, they are
    /// stripped out of the returned value since no callers care about them.
    pub fn validate_reprs(&self, input: &DeriveInput) -> Result<Vec<R>, Vec<Error>> {
        let mut metas_reprs = reprs(&input.attrs)?;
        metas_reprs.sort_by(|a: &(_, R), b| a.1.partial_cmp(&b.1).unwrap());

        if self.derive_unaligned {
            if let Some((meta, _)) =
                metas_reprs.iter().find(|&repr: &&(_, R)| repr.1.is_align_gt_one())
            {
                return Err(vec![Error::new_spanned(
                    meta,
                    "cannot derive Unaligned with repr(align(N > 1))",
                )]);
            }
        }

        let mut metas = Vec::new();
        let mut reprs = Vec::new();
        metas_reprs.into_iter().filter(|(_, repr)| !repr.is_align()).for_each(|(meta, repr)| {
            metas.push(meta);
            reprs.push(repr)
        });

        if reprs.is_empty() {
            // Use `Span::call_site` to report this error on the
            // `#[derive(...)]` itself.
            return Err(vec![Error::new(Span::call_site(), "must have a non-align #[repr(...)] attribute in order to guarantee this type's memory layout")]);
        }

        let initial_sp = metas[0].span();
        let err_span = metas.iter().skip(1).fold(Some(initial_sp), |sp_option, meta| {
            sp_option.and_then(|sp| sp.join(meta.span()))
        });

        if self.allowed_combinations.contains(&reprs.as_slice()) {
            Ok(reprs)
        } else if self.disallowed_but_legal_combinations.contains(&reprs.as_slice()) {
            Err(vec![Error::new(
                err_span.unwrap_or_else(|| input.span()),
                self.allowed_combinations_message,
            )])
        } else {
            Err(vec![Error::new(
                err_span.unwrap_or_else(|| input.span()),
                "conflicting representation hints",
            )])
        }
    }
}

// The type of valid reprs for a particular kind (enum, struct, union).
pub trait KindRepr: 'static + Sized + Ord {
    fn is_align(&self) -> bool;
    fn is_align_gt_one(&self) -> bool;
    fn parse(meta: &Meta) -> syn::Result<Self>;
}

// Defines an enum for reprs which are valid for a given kind (structs, enums,
// etc), and provide implementations of `KindRepr`, `Ord`, and `Display`, and
// those traits' super-traits.
macro_rules! define_kind_specific_repr {
    ($type_name:expr, $repr_name:ident, $($repr_variant:ident),*) => {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub enum $repr_name {
            $($repr_variant,)*
            Align(u64),
        }

        impl KindRepr for $repr_name {
            fn is_align(&self) -> bool {
                match self {
                    $repr_name::Align(_) => true,
                    _ => false,
                }
            }

            fn is_align_gt_one(&self) -> bool {
                match self {
                    $repr_name::Align(n) => n > &1,
                    _ => false,
                }
            }

            fn parse(meta: &Meta) -> syn::Result<$repr_name> {
                match Repr::from_meta(meta)? {
                    $(Repr::$repr_variant => Ok($repr_name::$repr_variant),)*
                    Repr::Align(u) => Ok($repr_name::Align(u)),
                    _ => Err(Error::new_spanned(meta, concat!("unsupported representation for deriving FromBytes, AsBytes, or Unaligned on ", $type_name)))
                }
            }
        }

        // Define a stable ordering so we can canonicalize lists of reprs. The
        // ordering itself doesn't matter so long as it's stable.
        impl PartialOrd for $repr_name {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $repr_name {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                format!("{:?}", self).cmp(&format!("{:?}", other))
            }
        }

        impl core::fmt::Display for $repr_name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                match self {
                    $($repr_name::$repr_variant => Repr::$repr_variant,)*
                    $repr_name::Align(u) => Repr::Align(*u),
                }.fmt(f)
            }
        }
    }
}

define_kind_specific_repr!("a struct", StructRepr, C, Transparent, Packed);
define_kind_specific_repr!(
    "an enum", EnumRepr, C, U8, U16, U32, U64, Usize, I8, I16, I32, I64, Isize
);

// All representations known to Rust.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Repr {
    U8,
    U16,
    U32,
    U64,
    Usize,
    I8,
    I16,
    I32,
    I64,
    Isize,
    C,
    Transparent,
    Packed,
    Align(u64),
}

impl Repr {
    fn from_meta(meta: &Meta) -> Result<Repr, Error> {
        match meta {
            Meta::Path(path) => {
                let ident = path
                    .get_ident()
                    .ok_or_else(|| Error::new_spanned(meta, "unrecognized representation hint"))?;
                match format!("{}", ident).as_str() {
                    "u8" => return Ok(Repr::U8),
                    "u16" => return Ok(Repr::U16),
                    "u32" => return Ok(Repr::U32),
                    "u64" => return Ok(Repr::U64),
                    "usize" => return Ok(Repr::Usize),
                    "i8" => return Ok(Repr::I8),
                    "i16" => return Ok(Repr::I16),
                    "i32" => return Ok(Repr::I32),
                    "i64" => return Ok(Repr::I64),
                    "isize" => return Ok(Repr::Isize),
                    "C" => return Ok(Repr::C),
                    "transparent" => return Ok(Repr::Transparent),
                    "packed" => return Ok(Repr::Packed),
                    _ => {}
                }
            }
            Meta::List(list) => {
                return Ok(Repr::Align(list.parse_args::<LitInt>()?.base10_parse::<u64>()?))
            }
            _ => {}
        }

        Err(Error::new_spanned(meta, "unrecognized representation hint"))
    }
}

impl Display for Repr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        if let Repr::Align(n) = self {
            return write!(f, "repr(align({}))", n);
        }
        write!(
            f,
            "repr({})",
            match self {
                Repr::U8 => "u8",
                Repr::U16 => "u16",
                Repr::U32 => "u32",
                Repr::U64 => "u64",
                Repr::Usize => "usize",
                Repr::I8 => "i8",
                Repr::I16 => "i16",
                Repr::I32 => "i32",
                Repr::I64 => "i64",
                Repr::Isize => "isize",
                Repr::C => "C",
                Repr::Transparent => "transparent",
                Repr::Packed => "packed",
                _ => unreachable!(),
            }
        )
    }
}

fn reprs<R: KindRepr>(attrs: &[Attribute]) -> Result<Vec<(Meta, R)>, Vec<Error>> {
    let mut reprs = Vec::new();
    let mut errors = Vec::new();
    for attr in attrs {
        // Ignore documentation attributes.
        if attr.path().is_ident("doc") {
            continue;
        }
        if let Meta::List(ref meta_list) = attr.meta {
            if meta_list.path.is_ident("repr") {
                let parsed: Punctuated<Meta, Comma> =
                    match meta_list.parse_args_with(Punctuated::parse_terminated) {
                        Ok(parsed) => parsed,
                        Err(_) => {
                            errors.push(Error::new_spanned(
                                &meta_list.tokens,
                                "unrecognized representation hint",
                            ));
                            continue;
                        }
                    };
                for meta in parsed {
                    match R::parse(&meta) {
                        Ok(repr) => reprs.push((meta, repr)),
                        Err(err) => errors.push(err),
                    }
                }
            }
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(reprs)
}
