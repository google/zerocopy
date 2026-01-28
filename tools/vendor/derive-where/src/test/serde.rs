use quote::quote;
use syn::Result;

use super::test_derive;

#[test]
fn basic() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Deserialize, Serialize)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
		quote! {
			#[::core::prelude::v1::derive(::serde::Deserialize)]
			#[serde(bound(deserialize = ""))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize)]
			struct Test<T>(std::marker::PhantomData<T>);

			#[::core::prelude::v1::derive(::serde::Serialize)]
			#[serde(bound(serialize = ""))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
	)
}

#[test]
fn bound() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Deserialize, Serialize; T)]
			struct Test<T, U>(T, std::marker::PhantomData<U>);
		},
		quote! {
			#[::core::prelude::v1::derive(::serde::Deserialize)]
			#[serde(bound(deserialize = "T : :: serde :: Deserialize < 'de >"))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize; T)]
			struct Test<T, U>(T, std::marker::PhantomData<U>);

			#[::core::prelude::v1::derive(::serde::Serialize)]
			#[serde(bound(serialize = "T : :: serde :: Serialize"))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize; T)]
			struct Test<T, U>(T, std::marker::PhantomData<U>);
		},
	)
}

#[test]
fn bound_two() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Deserialize, Serialize; T, U)]
			struct Test<T, U, V>(T, U, std::marker::PhantomData<V>);
		},
		quote! {
			#[::core::prelude::v1::derive(::serde::Deserialize)]
			#[serde(bound(deserialize = "T : :: serde :: Deserialize < 'de > , U : :: serde :: Deserialize < 'de >"))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize; T, U)]
			struct Test<T, U, V>(T, U, std::marker::PhantomData<V>);

			#[::core::prelude::v1::derive(::serde::Serialize)]
			#[serde(bound(serialize = "T : :: serde :: Serialize , U : :: serde :: Serialize"))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize; T, U)]
			struct Test<T, U, V>(T, U, std::marker::PhantomData<V>);
		},
	)
}

#[test]
fn attribute() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Deserialize, Serialize)]
			#[serde(test_attribute)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
		quote! {
			#[::core::prelude::v1::derive(::serde::Deserialize)]
			#[serde(bound(deserialize = ""))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize)]
			#[serde(test_attribute)]
			struct Test<T>(std::marker::PhantomData<T>);

			#[::core::prelude::v1::derive(::serde::Serialize)]
			#[serde(bound(serialize = ""))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize)]
			#[serde(test_attribute)]
			struct Test<T>(std::marker::PhantomData<T>);
		},
	)
}

#[test]
fn crate_() -> Result<()> {
	test_derive(
		quote! {
			#[derive_where(Deserialize, Serialize)]
			#[serde(crate = "serde_")]
			struct Test<T>(std::marker::PhantomData<T>);
		},
		quote! {
			#[::core::prelude::v1::derive(serde_::Deserialize)]
			#[serde(bound(deserialize = ""))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize)]
			#[serde(crate = "serde_")]
			struct Test<T>(std::marker::PhantomData<T>);

			#[::core::prelude::v1::derive(serde_::Serialize)]
			#[serde(bound(serialize = ""))]
			#[::derive_where::derive_where_serde]
			#[derive_where(Deserialize, Serialize)]
			#[serde(crate = "serde_")]
			struct Test<T>(std::marker::PhantomData<T>);
		},
	)
}
