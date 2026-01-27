use std::hash::Hash;
use std::marker::PhantomData;

use enum_dispatch::enum_dispatch;

/// In this module, the attribute with the argument appears over the enum.
mod attribute_argument_on_enum {
    use super::*;

    #[enum_dispatch]
    trait StoresKV<K: Hash, V> {
        fn store(&mut self, key: K, value: V);
        fn get(&self, key: &K) -> Option<&V>;
        fn update_value<F: Fn(V) -> V>(&mut self, key: &K, update_by: F);
    }

    #[enum_dispatch(StoresKV<K, V>)]
    enum KVStore<K: Hash, V, C: Credentials> {
        FileStorage(FileStorage<K, V>),
        RemoteStorage(RemoteStorage<K, V, C>),
        DevNull,
    }

    impl<K: Hash, V> StoresKV<K, V> for FileStorage<K, V> {
        #[allow(unused_variables)]
        fn store(&mut self, key: K, value: V) {
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn get(&self, key: &K) -> Option<&V> {
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn update_value<F: Fn(V) -> V>(&mut self, key: &K, update_by: F) {
            unimplemented!();
        }
    }

    impl<K: Hash, V, C: Credentials> StoresKV<K, V> for RemoteStorage<K, V, C> {
        #[allow(unused_variables)]
        fn store(&mut self, key: K, value: V) {
            let identity = self.credentials.identity();
            let api_key = self.credentials.api_key();
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn get(&self, key: &K) -> Option<&V> {
            let identity = self.credentials.identity();
            let api_key = self.credentials.api_key();
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn update_value<F: Fn(V) -> V>(&mut self, key: &K, update_by: F) {
            let identity = self.credentials.identity();
            let api_key = self.credentials.api_key();
            unimplemented!();
        }
    }

    impl<K: Hash, V> StoresKV<K, V> for DevNull {
        fn store(&mut self, _key: K, _value: V) {}
        fn get(&self, _key: &K) -> Option<&V> {
            None
        }
        fn update_value<F: Fn(V) -> V>(&mut self, _key: &K, _update_by: F) {}
    }

    #[test]
    fn attribute_argument_on_enum() {
        let mut storages: Vec<KVStore<String, String, SimpleCreds>> = vec![
            DevNull.into(),
            FileStorage::default().into(),
            RemoteStorage::new(SimpleCreds).into(),
        ];

        storages[0].store(String::from("key1"), String::from("value"));
        assert_eq!(storages[0].get(&String::from("key2")), None);
        storages[0].update_value(&String::from("key1"), |value| format!("{} + 1", value));
    }
}

/// Same as above, but the attributes are reversed such that the one with an argument is on the
/// trait rather than the enum.
mod attribute_argument_on_trait {
    use super::*;

    #[enum_dispatch(KVStoreReversed<K, V, _C>)]
    trait StoresKVReversed<K: Hash, V> {
        fn store(&mut self, key: K, value: V);
        fn get(&self, key: &K) -> Option<&V>;
        fn update_value<F: Fn(V) -> V>(&mut self, key: &K, update_by: F);
    }

    #[enum_dispatch]
    enum KVStoreReversed<K: Hash, V, C: Credentials> {
        FileStorage(FileStorage<K, V>),
        RemoteStorage(RemoteStorage<K, V, C>),
        DevNull,
    }

    impl<K: Hash, V> StoresKVReversed<K, V> for FileStorage<K, V> {
        #[allow(unused_variables)]
        fn store(&mut self, key: K, value: V) {
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn get(&self, key: &K) -> Option<&V> {
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn update_value<F: Fn(V) -> V>(&mut self, key: &K, update_by: F) {
            unimplemented!();
        }
    }

    impl<K: Hash, V, C: Credentials> StoresKVReversed<K, V> for RemoteStorage<K, V, C> {
        #[allow(unused_variables)]
        fn store(&mut self, key: K, value: V) {
            let identity = self.credentials.identity();
            let api_key = self.credentials.api_key();
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn get(&self, key: &K) -> Option<&V> {
            let identity = self.credentials.identity();
            let api_key = self.credentials.api_key();
            unimplemented!();
        }
        #[allow(unused_variables)]
        fn update_value<F: Fn(V) -> V>(&mut self, key: &K, update_by: F) {
            let identity = self.credentials.identity();
            let api_key = self.credentials.api_key();
            unimplemented!();
        }
    }

    impl<K: Hash, V> StoresKVReversed<K, V> for DevNull {
        fn store(&mut self, _key: K, _value: V) {}
        fn get(&self, _key: &K) -> Option<&V> {
            None
        }
        fn update_value<F: Fn(V) -> V>(&mut self, _key: &K, _update_by: F) {}
    }

    #[test]
    fn attribute_argument_on_enum() {
        let mut storages: Vec<KVStoreReversed<String, String, SimpleCreds>> = vec![
            DevNull.into(),
            FileStorage::default().into(),
            RemoteStorage::new(SimpleCreds).into(),
        ];

        storages[0].store(String::from("key1"), String::from("value"));
        assert_eq!(storages[0].get(&String::from("key2")), None);
        storages[0].update_value(&String::from("key1"), |value| format!("{} + 1", value));
    }
}

#[derive(Default)]
struct FileStorage<K: Hash, V> {
    key_value_type: PhantomData<(K, V)>,
}

trait Credentials {
    fn identity(&self) -> String;
    fn api_key(&self) -> String;
}

struct RemoteStorage<K: Hash, V, C: Credentials> {
    key_value_type: PhantomData<(K, V)>,
    credentials: C,
}

impl<K: Hash, V, C: Credentials> RemoteStorage<K, V, C> {
    fn new(credentials: C) -> Self {
        Self {
            key_value_type: Default::default(),
            credentials,
        }
    }
}

struct DevNull;

struct SimpleCreds;

impl Credentials for SimpleCreds {
    fn identity(&self) -> String {
        String::from("root")
    }
    fn api_key(&self) -> String {
        String::from("D0nTb3f0ol3D-Thi51Sn0tAR34al4P1kEY")
    }
}
