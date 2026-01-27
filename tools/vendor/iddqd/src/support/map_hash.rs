use core::{
    fmt,
    hash::{BuildHasher, Hash},
};

/// Packages up a hash for later validation.
#[derive(Clone)]
pub(crate) struct MapHash {
    pub(super) hash: u64,
}

impl MapHash {
    pub(crate) fn new(hash: u64) -> Self {
        Self { hash }
    }

    pub(crate) fn hash(&self) -> u64 {
        self.hash
    }

    pub(crate) fn is_same_hash<S: BuildHasher, K: Hash>(
        &self,
        state: &S,
        key: K,
    ) -> bool {
        self.hash == state.hash_one(key)
    }
}

impl fmt::Debug for MapHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MapHash")
            .field("hash", &self.hash)
            .finish_non_exhaustive()
    }
}
