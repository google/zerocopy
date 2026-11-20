// RFC 2094 problem case #3. Expect: rejected by NLL (E0499); accepted by the Polonius analysis.
use std::collections::HashMap;
use std::hash::Hash;
pub fn get_default<'r, K: Hash + Eq + Copy, V: Default>(map: &'r mut HashMap<K, V>, key: K) -> &'r mut V {
    match map.get_mut(&key) {
        Some(value) => value,
        None => {
            map.insert(key, V::default());
            map.get_mut(&key).unwrap()
        }
    }
}
