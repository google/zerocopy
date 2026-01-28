use quote::quote;
use syn::Result;

use super::test_derive;

#[test]
fn struct_() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone)]
			struct Test<T> {
				field: std::marker::PhantomData<T>,
			}
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T> {
				#[inline]
				fn clone(&self) -> Self {
					match self {
						Test { field: ref __field_field } => Test { field: ::core::clone::Clone::clone(__field_field) },
					}
				}
			}
		},
	)
}

#[test]
fn skip_inner() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone)]
			#[derive_where(skip_inner(Clone))]
			struct Test<T> {
				field: std::marker::PhantomData<T>,
			}
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T> {
				#[inline]
				fn clone(&self) -> Self {
					match self {
						Test { field: ref __field_field } => Test { field: ::core::default::Default::default() },
					}
				}
			}
		},
	)
}

#[test]
fn skip_field() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone)]
			struct Test<T> {
				#[derive_where(skip(Clone))]
				field: std::marker::PhantomData<T>,
			}
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T> {
				#[inline]
				fn clone(&self) -> Self {
					match self {
						Test { field: ref __field_field } => Test { field: ::core::default::Default::default() },
					}
				}
			}
		},
	)
}

#[test]
fn tuple() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T> {
				#[inline]
				fn clone(&self) -> Self {
					match self {
						Test(ref __field_0) => Test { 0: ::core::clone::Clone::clone(__field_0) },
					}
				}
			}
		},
	)
}

#[test]
fn enum_() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone)]
			enum Test<T> {
				A { field: std::marker::PhantomData<T>},
				B { },
				C(std::marker::PhantomData<T>),
				D(),
				E,
			}
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T> {
				#[inline]
				fn clone(&self) -> Self {
					match self {
						Test::A { field: ref __field_field } => Test::A { field: ::core::clone::Clone::clone(__field_field) },
						Test::B { } => Test::B { },
						Test::C(ref __field_0) => Test::C { 0: ::core::clone::Clone::clone(__field_0) },
						Test::D() => Test::D { },
						Test::E => Test::E,
					}
				}
			}
		},
	)
}

#[test]
fn union_() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone)]
			union Test<T> {
				a: std::marker::PhantomData<T>,
				b: u8,
			}
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T> {
				#[inline]
				fn clone(&self) -> Self {
					struct __AssertCopy<__T: ::core::marker::Copy + ?::core::marker::Sized>(::core::marker::PhantomData<__T>);
					let _: __AssertCopy<Self>;
					*self
				}
			}
		},
	)
}

#[test]
fn no_bound() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone, Copy)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T>
			{
				#[inline]
				fn clone(&self) -> Self {
					*self
				}
			}

			#[automatically_derived]
			impl<T> ::core::marker::Copy for Test<T>
			{ }
		},
	)
}

#[test]
fn custom_bound() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Clone, Copy; T: Trait)]
			struct Test<T>(T);
		},
		quote! {
			#[automatically_derived]
			impl<T> ::core::clone::Clone for Test<T>
			where T: Trait
			{
				#[inline]
				fn clone(&self) -> Self {
					*self
				}
			}

			#[automatically_derived]
			impl<T> ::core::marker::Copy for Test<T>
			where T: Trait
			{ }
		},
	)
}
