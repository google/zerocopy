use quote::quote;
use syn::Result;

use super::test_derive;

#[test]
fn basic() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Zeroize)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
		quote! {
			#[automatically_derived]
			impl<T> ::zeroize::Zeroize for Test<T> {
				fn zeroize(&mut self) {
					use ::zeroize::Zeroize;

					match self {
						Test(ref mut __field_0) => {
							__field_0.zeroize();
						}
					}
				}
			}
		},
	)
}

#[test]
fn drop() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(ZeroizeOnDrop; T)]
			struct Test<T, U>(T, std::marker::PhantomData<U>);
		},
		#[cfg(not(feature = "zeroize-on-drop"))]
		quote! {
			#[automatically_derived]
			impl<T, U> ::core::ops::Drop for Test<T, U>
			where T: ::zeroize::ZeroizeOnDrop
			{
				fn drop(&mut self) {
					::zeroize::Zeroize::zeroize(self);
				}
			}
		},
		#[cfg(feature = "zeroize-on-drop")]
		quote! {
			#[automatically_derived]
			impl<T, U> ::core::ops::Drop for Test<T, U>
			where T: ::zeroize::ZeroizeOnDrop
			{
				fn drop(&mut self) {
					trait AssertZeroizeOnDrop {
						fn __derive_where_zeroize_or_on_drop(self);
					}

					impl<T: ::zeroize::ZeroizeOnDrop + ?::core::marker::Sized> AssertZeroizeOnDrop for &&mut T {
						fn __derive_where_zeroize_or_on_drop(self) {}
					}

					trait AssertZeroize {
						fn __derive_where_zeroize_or_on_drop(&mut self);
					}

					impl<T: ::zeroize::Zeroize + ?::core::marker::Sized> AssertZeroize for T {
						fn __derive_where_zeroize_or_on_drop(&mut self) {
							::zeroize::Zeroize::zeroize(self);
						}
					}

					match self {
						Test(ref mut __field_0, ref mut __field_1) => {
							__field_0.__derive_where_zeroize_or_on_drop();
							__field_1.__derive_where_zeroize_or_on_drop();
						}
					}
				}
			}

			#[automatically_derived]
			impl<T, U> ::zeroize::ZeroizeOnDrop for Test<T, U>
			where T: ::zeroize::ZeroizeOnDrop
			{ }
		},
	)
}

#[test]
fn both() -> Result<()> {
	#[cfg(not(feature = "zeroize-on-drop"))]
	let drop = quote! {
		#[automatically_derived]
		impl<T, U> ::core::ops::Drop for Test<T, U>
		where T: ::zeroize::ZeroizeOnDrop
		{
			fn drop(&mut self) {
				::zeroize::Zeroize::zeroize(self);
			}
		}
	};
	#[cfg(feature = "zeroize-on-drop")]
	let drop = quote! {
		#[automatically_derived]
		impl<T, U> ::core::ops::Drop for Test<T, U>
		where T: ::zeroize::ZeroizeOnDrop
		{
			fn drop(&mut self) {
				trait AssertZeroizeOnDrop {
					fn __derive_where_zeroize_or_on_drop(self);
				}

				impl<T: ::zeroize::ZeroizeOnDrop + ?::core::marker::Sized> AssertZeroizeOnDrop for &&mut T {
					fn __derive_where_zeroize_or_on_drop(self) {}
				}

				trait AssertZeroize {
					fn __derive_where_zeroize_or_on_drop(&mut self);
				}

				impl<T: ::zeroize::Zeroize + ?::core::marker::Sized> AssertZeroize for T {
					fn __derive_where_zeroize_or_on_drop(&mut self) {
						::zeroize::Zeroize::zeroize(self);
					}
				}

				match self {
					Test(ref mut __field_0, ref mut __field_1) => {
						__field_0.__derive_where_zeroize_or_on_drop();
						__field_1.__derive_where_zeroize_or_on_drop();
					}
				}
			}
		}

		#[automatically_derived]
		impl<T, U> ::zeroize::ZeroizeOnDrop for Test<T, U>
		where T: ::zeroize::ZeroizeOnDrop
		{ }
	};

	test_derive(
		quote! {
			#[derive_where(Zeroize, ZeroizeOnDrop; T)]
			struct Test<T, U>(T, std::marker::PhantomData<U>);
		},
		quote! {
			#[automatically_derived]
			impl<T, U> ::zeroize::Zeroize for Test<T, U>
			where T: ::zeroize::Zeroize
			{
				fn zeroize(&mut self) {
					use ::zeroize::Zeroize;

					match self {
						Test(ref mut __field_0, ref mut __field_1) => {
							__field_0.zeroize();
							__field_1.zeroize();
						}
					}
				}
			}

			#drop
		},
	)
}

#[test]
fn crate_() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Zeroize(crate = zeroize_); T)]
			struct Test<T>(T);
		},
		quote! {
			#[automatically_derived]
			impl<T> zeroize_::Zeroize for Test<T>
			where T: zeroize_::Zeroize
			{
				fn zeroize(&mut self) {
					use zeroize_::Zeroize;

					match self {
						Test(ref mut __field_0) => {
							__field_0.zeroize();
						}
					}
				}
			}
		},
	)
}

#[test]
fn crate_drop() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(ZeroizeOnDrop(crate = zeroize_); T)]
			struct Test<T>(T);
		},
		#[cfg(not(feature = "zeroize-on-drop"))]
		quote! {
			#[automatically_derived]
			impl<T> ::core::ops::Drop for Test<T>
			where T: zeroize_::ZeroizeOnDrop
			{
				fn drop(&mut self) {
					zeroize_::Zeroize::zeroize(self);
				}
			}
		},
		#[cfg(feature = "zeroize-on-drop")]
		quote! {
			#[automatically_derived]
			impl<T> ::core::ops::Drop for Test<T>
			where T: zeroize_::ZeroizeOnDrop
			{
				fn drop(&mut self) {
					trait AssertZeroizeOnDrop {
						fn __derive_where_zeroize_or_on_drop(self);
					}

					impl<T: zeroize_::ZeroizeOnDrop + ?::core::marker::Sized> AssertZeroizeOnDrop for &&mut T {
						fn __derive_where_zeroize_or_on_drop(self) {}
					}

					trait AssertZeroize {
						fn __derive_where_zeroize_or_on_drop(&mut self);
					}

					impl<T: zeroize_::Zeroize + ?::core::marker::Sized> AssertZeroize for T {
						fn __derive_where_zeroize_or_on_drop(&mut self) {
							zeroize_::Zeroize::zeroize(self);
						}
					}

					match self {
						Test(ref mut __field_0) => {
							__field_0.__derive_where_zeroize_or_on_drop();
						}
					}
				}
			}

			#[automatically_derived]
			impl<T> zeroize_::ZeroizeOnDrop for Test<T>
			where T: zeroize_::ZeroizeOnDrop
			{ }
		},
	)
}

#[test]
fn fqs() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Zeroize)]
			struct Test<T>(#[derive_where(Zeroize(fqs))] std::marker::PhantomData<T>);
		},
		quote! {
			#[automatically_derived]
			impl<T> ::zeroize::Zeroize for Test<T> {
				fn zeroize(&mut self) {
					use ::zeroize::Zeroize;

					match self {
						Test(ref mut __field_0) => {
							::zeroize::Zeroize::zeroize(__field_0);
						}
					}
				}
			}
		},
	)
}

#[test]
fn enum_skip() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Zeroize)]
			enum Test<T> {
				A(std::marker::PhantomData<T>),
				#[derive_where(skip_inner(Zeroize))]
				B(std::marker::PhantomData<T>),
			}
		},
		quote! {
			#[automatically_derived]
			impl <T> ::zeroize::Zeroize for Test<T> {
				fn zeroize(&mut self) {
					use ::zeroize::Zeroize;

					match self {
						Test::A(ref mut __field_0) => {
							__field_0.zeroize();
						}
						Test::B(ref mut __field_0) => { }
					}
				}
			}
		},
	)
}

#[test]
fn enum_skip_drop() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(ZeroizeOnDrop)]
			enum Test<T> {
				A(std::marker::PhantomData<T>),
				#[derive_where(skip_inner)]
				B(std::marker::PhantomData<T>),
			}
		},
		#[cfg(not(feature = "zeroize-on-drop"))]
		quote! {
			#[automatically_derived]
			impl<T> ::core::ops::Drop for Test<T> {
				fn drop(&mut self) {
					::zeroize::Zeroize::zeroize(self);
				}
			}
		},
		#[cfg(feature = "zeroize-on-drop")]
		quote! {
			#[automatically_derived]
			impl <T> ::core::ops::Drop for Test<T> {
				fn drop(&mut self) {
					trait AssertZeroizeOnDrop {
						fn __derive_where_zeroize_or_on_drop(self);
					}

					impl<T: ::zeroize::ZeroizeOnDrop + ?::core::marker::Sized> AssertZeroizeOnDrop for &&mut T {
						fn __derive_where_zeroize_or_on_drop(self) {}
					}

					trait AssertZeroize {
						fn __derive_where_zeroize_or_on_drop(&mut self);
					}

					impl<T: ::zeroize::Zeroize + ?::core::marker::Sized> AssertZeroize for T {
						fn __derive_where_zeroize_or_on_drop(&mut self) {
							::zeroize::Zeroize::zeroize(self);
						}
					}

					match self {
						Test::A(ref mut __field_0) => {
							__field_0.__derive_where_zeroize_or_on_drop();
						}
						Test::B(ref mut __field_0) => { }
					}
				}
			}

			#[automatically_derived]
			impl<T> ::zeroize::ZeroizeOnDrop for Test<T> { }
		},
	)
}

#[test]
#[cfg(feature = "zeroize-on-drop")]
fn no_drop() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(ZeroizeOnDrop(no_drop); T)]
			struct Test<T, U>(T, std::marker::PhantomData<U>);
		},
		quote! {
			const _: () = {
				trait DeriveWhereAssertZeroizeOnDrop {
					fn assert(&mut self);
				}

				impl<T, U> DeriveWhereAssertZeroizeOnDrop for Test <T, U>
				where T: ::zeroize::ZeroizeOnDrop
				{
					fn assert(&mut self) {
						trait AssertZeroizeOnDrop {
							fn __derive_where_zeroize_on_drop(&mut self);
						}

						impl<T: ::zeroize::ZeroizeOnDrop + ?::core::marker::Sized> AssertZeroizeOnDrop for T {
							fn __derive_where_zeroize_on_drop(&mut self) {}
						}

						match self {
							Test (ref mut __field_0, ref mut __field_1) => {
								__field_0.__derive_where_zeroize_on_drop();
								__field_1.__derive_where_zeroize_on_drop();
							}
						}
					}
				}
			};

			#[automatically_derived]
			impl<T, U> ::zeroize::ZeroizeOnDrop for Test<T, U>
			where T: ::zeroize::ZeroizeOnDrop
			{ }
		},
	)
}
