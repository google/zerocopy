// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Byte order-aware numeric primitives.
//!
//! This module contains equivalents of the native multi-byte integer types with
//! no alignment requirement and supporting byte order conversions.
//!
//! For each native multi-byte integer type - `u16`, `i16`, `u32`, etc - an
//! equivalent type is defined by this module - [`U16`], [`I16`], [`U32`], etc.
//! Unlike their native counterparts, these types have alignment 1, and take a
//! type parameter specifying the byte order in which the bytes are stored in
//! memory. Each type implements the [`FromBytes`], [`AsBytes`], and
//! [`Unaligned`] traits.
//!
//! These two properties, taken together, make these types very useful for
//! defining data structures whose memory layout matches a wire format such as
//! that of a network protocol or a file format. Such formats often have
//! multi-byte values at offsets that do not respect the alignment requirements
//! of the equivalent native types, and stored in a byte order not necessarily
//! the same as that of the target platform.
//!
//! # Example
//!
//! One use of these types is for representing network packet formats, such as
//! UDP:
//!
//! ```edition2018
//! # use zerocopy::*;
//! use ::byteorder::NetworkEndian;
//!
//! #[derive(FromBytes, AsBytes, Unaligned)]
//! #[repr(C)]
//! struct UdpHeader {
//!     src_port: U16<NetworkEndian>,
//!     dst_port: U16<NetworkEndian>,
//!     length: U16<NetworkEndian>,
//!     checksum: U16<NetworkEndian>,
//! }
//!
//! struct UdpPacket<B: ByteSlice> {
//!     header: LayoutVerified<B, UdpHeader>,
//!     body: B,
//! }
//!
//! impl<B: ByteSlice> UdpPacket<B> {
//!     fn parse(bytes: B) -> Option<UdpPacket<B>> {
//!         let (header, body) = LayoutVerified::new_from_prefix(bytes)?;
//!         Some(UdpPacket { header, body })
//!     }
//!
//!     fn src_port(&self) -> u16 {
//!         self.header.src_port.get()
//!     }
//!
//!     // more getters...
//! }
//! ```

use core::convert::{TryFrom, TryInto};
use core::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex};
use core::marker::PhantomData;
use core::num::TryFromIntError;

use zerocopy_derive::*;

use crate::AsBytes;
// This allows the custom derives to work. See the comment on this module for an
// explanation.
use crate::zerocopy;

// NOTE: We don't reexport `WriteBytesExt` or `ReadBytesExt` because those are
// only available with the `std` feature enabled, and zerocopy is `no_std` by
// default.
pub use byteorder::{BigEndian, ByteOrder, LittleEndian, NativeEndian, NetworkEndian, BE, LE};

macro_rules! impl_fmt_trait {
    ($name:ident, $native:ident, $trait:ident) => {
        impl<O: ByteOrder> $trait for $name<O> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                $trait::fmt(&self.get(), f)
            }
        }
    };
}

macro_rules! doc_comment {
    ($x:expr, $($tt:tt)*) => {
        #[doc = $x]
        $($tt)*
    };
}

macro_rules! define_max_value_constant {
    ($name:ident, $bytes:expr, unsigned) => {
        /// The maximum value.
        ///
        /// This constant should be preferred to constructing a new value using
        /// `new`, as `new` may perform an endianness swap depending on the
        /// endianness `O` and the endianness of the platform.
        pub const MAX_VALUE: $name<O> = $name([0xFFu8; $bytes], PhantomData);
    };
    ($name:ident, $bytes:expr, signed) => {
        // We don't provide maximum and minimum value constants for signed
        // values because there's no way to do it generically - it would require
        // a different value depending on the value of the ByteOrder type
        // parameter. Currently, one workaround would be to provide
        // implementations for concrete implementations of that trait. In the
        // long term, if we are ever able to make the `new` constructor a const
        // fn, we could use that instead.
    };
}

macro_rules! define_type {
    ($article:ident,
        $name:ident,
        $native:ident,
        $bits:expr,
        $bytes:expr,
        $read_method:ident,
        $write_method:ident,
        $sign:ident,
        [$($larger_native:ty),*],
        [$($larger_byteorder:ident),*]) => {
        doc_comment! {
            concat!("A ", stringify!($bits), "-bit ", stringify!($sign), " integer
stored in `O` byte order.

`", stringify!($name), "` is like the native `", stringify!($native), "` type with
two major differences: First, it has no alignment requirement (its alignment is 1).
Second, the endianness of its memory layout is given by the type parameter `O`.

", stringify!($article), " `", stringify!($name), "` can be constructed using
the [`new`] method, and its contained value can be obtained as a native
`",stringify!($native), "` using the [`get`] method, or updated in place with
the [`set`] method. In all cases, if the endianness `O` is not the same as the
endianness of the current platform, an endianness swap will be performed in
order to uphold the invariants that a) the layout of `", stringify!($name), "`
has endianness `O` and that, b) the layout of `", stringify!($native), "` has
the platform's native endianness.

`", stringify!($name), "` implements [`FromBytes`], [`AsBytes`], and [`Unaligned`],
making it useful for parsing and serialization. See the module documentation for an
example of how it can be used for parsing UDP packets.

[`new`]: crate::byteorder::", stringify!($name), "::new
[`get`]: crate::byteorder::", stringify!($name), "::get
[`set`]: crate::byteorder::", stringify!($name), "::set
[`FromBytes`]: crate::FromBytes
[`AsBytes`]: crate::AsBytes
[`Unaligned`]: crate::Unaligned"),
            #[derive(FromBytes, Unaligned, Copy, Clone, Eq, PartialEq, Hash)]
            #[repr(transparent)]
            pub struct $name<O>([u8; $bytes], PhantomData<O>);
        }

        impl<O> Default for $name<O> {
            fn default() -> $name<O> {
                $name::ZERO
            }
        }

        // TODO(joshlf): Replace this with #[derive(AsBytes)] once that derive
        // supports type parameters.
        unsafe impl<O: ByteOrder> AsBytes for $name<O> {
            fn only_derive_is_allowed_to_implement_this_trait()
            where
                Self: Sized,
            {
            }
        }

        impl<O> $name<O> {
            /// The value zero.
            ///
            /// This constant should be preferred to constructing a new value
            /// using `new`, as `new` may perform an endianness swap depending
            /// on the endianness and platform.
            pub const ZERO: $name<O> = $name([0u8; $bytes], PhantomData);

            define_max_value_constant!($name, $bytes, $sign);

            /// Constructs a new value from bytes which are already in the
            /// endianness `O`.
            pub const fn from_bytes(bytes: [u8; $bytes]) -> $name<O> {
                $name(bytes, PhantomData)
            }
        }

        impl<O: ByteOrder> $name<O> {
            // TODO(joshlf): Make these const fns if the ByteOrder methods ever
            // become const fns.

            /// Constructs a new value, possibly performing an endianness swap
            /// to guarantee that the returned value has endianness `O`.
            pub fn new(n: $native) -> $name<O> {
                let mut out = $name::default();
                O::$write_method(&mut out.0[..], n);
                out
            }

            /// Returns the value as a primitive type, possibly performing an
            /// endianness swap to guarantee that the return value has the
            /// endianness of the native platform.
            pub fn get(self) -> $native {
                O::$read_method(&self.0[..])
            }

            /// Updates the value in place as a primitive type, possibly
            /// performing an endianness swap to guarantee that the stored value
            /// has the endianness `O`.
            pub fn set(&mut self, n: $native) {
                O::$write_method(&mut self.0[..], n);
            }
        }

        // NOTE: The reasoning behind which traits to implement here is to only
        // implement traits which won't cause inference issues. Notably,
        // comparison traits like PartialEq and PartialOrd tend to cause
        // inference issues.

        impl<O: ByteOrder> From<$name<O>> for [u8; $bytes] {
            fn from(x: $name<O>) -> [u8; $bytes] {
                x.0
            }
        }

        impl<O: ByteOrder> From<[u8; $bytes]> for $name<O> {
            fn from(bytes: [u8; $bytes]) -> $name<O> {
                $name(bytes, PhantomData)
            }
        }

        impl<O: ByteOrder> From<$name<O>> for $native {
            fn from(x: $name<O>) -> $native {
                x.get()
            }
        }

        impl<O: ByteOrder> From<$native> for $name<O> {
            fn from(x: $native) -> $name<O> {
                $name::new(x)
            }
        }

        $(
            impl<O: ByteOrder> From<$name<O>> for $larger_native {
                fn from(x: $name<O>) -> $larger_native {
                    x.get().into()
                }
            }

            impl<O: ByteOrder> TryFrom<$larger_native> for $name<O> {
                type Error = TryFromIntError;
                fn try_from(x: $larger_native) -> Result<$name<O>, TryFromIntError> {
                    $native::try_from(x).map($name::new)
                }
            }
        )*

        $(
            impl<O: ByteOrder, P: ByteOrder> From<$name<O>> for $larger_byteorder<P> {
                fn from(x: $name<O>) -> $larger_byteorder<P> {
                    $larger_byteorder::new(x.get().into())
                }
            }

            impl<O: ByteOrder, P: ByteOrder> TryFrom<$larger_byteorder<P>> for $name<O> {
                type Error = TryFromIntError;
                fn try_from(x: $larger_byteorder<P>) -> Result<$name<O>, TryFromIntError> {
                    x.get().try_into().map($name::new)
                }
            }
        )*

        impl<O: ByteOrder> AsRef<[u8; $bytes]> for $name<O> {
            fn as_ref(&self) -> &[u8; $bytes] {
                &self.0
            }
        }

        impl<O: ByteOrder> AsMut<[u8; $bytes]> for $name<O> {
            fn as_mut(&mut self) -> &mut [u8; $bytes] {
                &mut self.0
            }
        }

        impl<O: ByteOrder> PartialEq<$name<O>> for [u8; $bytes] {
            fn eq(&self, other: &$name<O>) -> bool {
                self.eq(&other.0)
            }
        }

        impl<O: ByteOrder> PartialEq<[u8; $bytes]> for $name<O> {
            fn eq(&self, other: &[u8; $bytes]) -> bool {
                self.0.eq(other)
            }
        }

        impl_fmt_trait!($name, $native, Display);
        impl_fmt_trait!($name, $native, Octal);
        impl_fmt_trait!($name, $native, LowerHex);
        impl_fmt_trait!($name, $native, UpperHex);
        impl_fmt_trait!($name, $native, Binary);

        impl<O: ByteOrder> Debug for $name<O> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                // This results in a format like "U16(42)"
                write!(f, concat!(stringify!($name), "({})"), self.get())
            }
        }
    };
}

define_type!(
    A,
    U16,
    u16,
    16,
    2,
    read_u16,
    write_u16,
    unsigned,
    [u32, u64, u128, usize],
    [U32, U64, U128]
);
define_type!(A, U32, u32, 32, 4, read_u32, write_u32, unsigned, [u64, u128], [U64, U128]);
define_type!(A, U64, u64, 64, 8, read_u64, write_u64, unsigned, [u128], [U128]);
define_type!(A, U128, u128, 128, 16, read_u128, write_u128, unsigned, [], []);
define_type!(
    An,
    I16,
    i16,
    16,
    2,
    read_i16,
    write_i16,
    signed,
    [i32, i64, i128, isize],
    [I32, I64, I128]
);
define_type!(An, I32, i32, 32, 4, read_i32, write_i32, signed, [i64, i128], [I64, I128]);
define_type!(An, I64, i64, 64, 8, read_i64, write_i64, signed, [i128], [I128]);
define_type!(An, I128, i128, 128, 16, read_i128, write_i128, signed, [], []);

#[cfg(test)]
mod tests {
    use byteorder::NativeEndian;

    use super::*;
    use crate::{AsBytes, FromBytes, Unaligned};

    // A native integer type (u16, i32, etc)
    trait Native: FromBytes + AsBytes + Copy + Eq + Debug {
        const ZERO: Self;
        const MAX_VALUE: Self;

        fn rand() -> Self;
    }

    trait ByteArray:
        FromBytes + AsBytes + Copy + AsRef<[u8]> + AsMut<[u8]> + Debug + Default + Eq
    {
        /// Invert the order of the bytes in the array.
        fn invert(self) -> Self;
    }

    trait ByteOrderType: FromBytes + AsBytes + Unaligned + Copy + Eq + Debug {
        type Native: Native;
        type ByteArray: ByteArray;

        const ZERO: Self;

        fn new(native: Self::Native) -> Self;
        fn get(self) -> Self::Native;
        fn set(&mut self, native: Self::Native);
        fn from_bytes(bytes: Self::ByteArray) -> Self;
        fn into_bytes(self) -> Self::ByteArray;
    }

    trait ByteOrderTypeUnsigned: ByteOrderType {
        const MAX_VALUE: Self;
    }

    macro_rules! impl_byte_array {
        ($bytes:expr) => {
            impl ByteArray for [u8; $bytes] {
                fn invert(mut self) -> [u8; $bytes] {
                    self.reverse();
                    self
                }
            }
        };
    }

    impl_byte_array!(2);
    impl_byte_array!(4);
    impl_byte_array!(8);
    impl_byte_array!(16);

    macro_rules! impl_byte_order_type_unsigned {
        ($name:ident, unsigned) => {
            impl<O: ByteOrder> ByteOrderTypeUnsigned for $name<O> {
                const MAX_VALUE: $name<O> = $name::MAX_VALUE;
            }
        };
        ($name:ident, signed) => {};
    }

    macro_rules! impl_traits {
        ($name:ident, $native:ident, $bytes:expr, $sign:ident) => {
            impl Native for $native {
                const ZERO: $native = 0;
                const MAX_VALUE: $native = ::core::$native::MAX;

                fn rand() -> $native {
                    rand::random()
                }
            }

            impl<O: ByteOrder> ByteOrderType for $name<O> {
                type Native = $native;
                type ByteArray = [u8; $bytes];

                const ZERO: $name<O> = $name::ZERO;

                fn new(native: $native) -> $name<O> {
                    $name::new(native)
                }

                fn get(self) -> $native {
                    $name::get(self)
                }

                fn set(&mut self, native: $native) {
                    $name::set(self, native)
                }

                fn from_bytes(bytes: [u8; $bytes]) -> $name<O> {
                    $name::from(bytes)
                }

                fn into_bytes(self) -> [u8; $bytes] {
                    <[u8; $bytes]>::from(self)
                }
            }

            impl_byte_order_type_unsigned!($name, $sign);
        };
    }

    impl_traits!(U16, u16, 2, unsigned);
    impl_traits!(U32, u32, 4, unsigned);
    impl_traits!(U64, u64, 8, unsigned);
    impl_traits!(U128, u128, 16, unsigned);
    impl_traits!(I16, i16, 2, signed);
    impl_traits!(I32, i32, 4, signed);
    impl_traits!(I64, i64, 8, signed);
    impl_traits!(I128, i128, 16, signed);

    macro_rules! call_for_all_types {
        ($fn:ident, $byteorder:ident) => {
            $fn::<U16<$byteorder>>();
            $fn::<U32<$byteorder>>();
            $fn::<U64<$byteorder>>();
            $fn::<U128<$byteorder>>();
            $fn::<I16<$byteorder>>();
            $fn::<I32<$byteorder>>();
            $fn::<I64<$byteorder>>();
            $fn::<I128<$byteorder>>();
        };
    }

    macro_rules! call_for_unsigned_types {
        ($fn:ident, $byteorder:ident) => {
            $fn::<U16<$byteorder>>();
            $fn::<U32<$byteorder>>();
            $fn::<U64<$byteorder>>();
            $fn::<U128<$byteorder>>();
        };
    }

    #[cfg(target_endian = "big")]
    type NonNativeEndian = byteorder::LittleEndian;
    #[cfg(target_endian = "little")]
    type NonNativeEndian = byteorder::BigEndian;

    #[test]
    fn test_zero() {
        fn test_zero<T: ByteOrderType>() {
            assert_eq!(T::ZERO.get(), T::Native::ZERO);
        }

        call_for_all_types!(test_zero, NativeEndian);
        call_for_all_types!(test_zero, NonNativeEndian);
    }

    #[test]
    fn test_max_value() {
        fn test_max_value<T: ByteOrderTypeUnsigned>() {
            assert_eq!(T::MAX_VALUE.get(), T::Native::MAX_VALUE);
        }

        call_for_unsigned_types!(test_max_value, NativeEndian);
        call_for_unsigned_types!(test_max_value, NonNativeEndian);
    }

    #[test]
    fn test_native_endian() {
        fn test_native_endian<T: ByteOrderType>() {
            for _ in 0..1024 {
                let native = T::Native::rand();
                let mut bytes = T::ByteArray::default();
                bytes.as_bytes_mut().copy_from_slice(native.as_bytes());
                let mut from_native = T::new(native);
                let from_bytes = T::from_bytes(bytes);
                assert_eq!(from_native, from_bytes);
                assert_eq!(from_native.get(), native);
                assert_eq!(from_bytes.get(), native);
                assert_eq!(from_native.into_bytes(), bytes);
                assert_eq!(from_bytes.into_bytes(), bytes);

                let updated = T::Native::rand();
                from_native.set(updated);
                assert_eq!(from_native.get(), updated);
            }
        }

        call_for_all_types!(test_native_endian, NativeEndian);
    }

    #[test]
    fn test_non_native_endian() {
        fn test_non_native_endian<T: ByteOrderType>() {
            for _ in 0..1024 {
                let native = T::Native::rand();
                let mut bytes = T::ByteArray::default();
                bytes.as_bytes_mut().copy_from_slice(native.as_bytes());
                bytes = bytes.invert();
                let mut from_native = T::new(native);
                let from_bytes = T::from_bytes(bytes);
                assert_eq!(from_native, from_bytes);
                assert_eq!(from_native.get(), native);
                assert_eq!(from_bytes.get(), native);
                assert_eq!(from_native.into_bytes(), bytes);
                assert_eq!(from_bytes.into_bytes(), bytes);

                let updated = T::Native::rand();
                from_native.set(updated);
                assert_eq!(from_native.get(), updated);
            }
        }

        call_for_all_types!(test_non_native_endian, NonNativeEndian);
    }
}
