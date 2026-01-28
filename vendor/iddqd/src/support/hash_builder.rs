/// Default hasher for hash map types.
///
/// To disable this hasher, disable the `default-hasher` feature.
#[cfg(feature = "default-hasher")]
pub type DefaultHashBuilder = foldhash::fast::RandomState;

#[cfg(not(feature = "default-hasher"))]
mod dummy {
    use core::hash::{BuildHasher, Hasher};

    /// Dummy default hasher for hash map types.
    ///
    /// The `default-hasher` feature is currently disabled.
    #[derive(Clone, Copy, Debug)]
    pub enum DefaultHashBuilder {}

    impl BuildHasher for DefaultHashBuilder {
        type Hasher = Self;

        fn build_hasher(&self) -> Self::Hasher {
            unreachable!("this is an empty enum so self cannot exist")
        }
    }

    impl Hasher for DefaultHashBuilder {
        fn write(&mut self, _bytes: &[u8]) {
            unreachable!("this is an empty enum so self cannot exist")
        }

        fn finish(&self) -> u64 {
            unreachable!("this is an empty enum so self cannot exist")
        }
    }
}

#[cfg(not(feature = "default-hasher"))]
pub use dummy::DefaultHashBuilder;
