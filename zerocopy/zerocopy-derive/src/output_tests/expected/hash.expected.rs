impl<T: Clone> ::zerocopy::util::macro_util::core_reexport::hash::Hash for Foo<T>
where
    Self: ::zerocopy::IntoBytes + ::zerocopy::Immutable,
    Self: Sized,
{
    fn hash<
        ___ZerocopyHasher: ::zerocopy::util::macro_util::core_reexport::hash::Hasher,
    >(&self, state: &mut ___ZerocopyHasher) {
        ::zerocopy::util::macro_util::core_reexport::hash::Hasher::write(
            state,
            ::zerocopy::IntoBytes::as_bytes(self),
        )
    }
    fn hash_slice<
        ___ZerocopyHasher: ::zerocopy::util::macro_util::core_reexport::hash::Hasher,
    >(data: &[Self], state: &mut ___ZerocopyHasher) {
        ::zerocopy::util::macro_util::core_reexport::hash::Hasher::write(
            state,
            ::zerocopy::IntoBytes::as_bytes(data),
        )
    }
}
