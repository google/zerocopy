// RFC 2094 problem case #3: conditional control flow across functions.
use std::collections::HashMap;
pub fn get_default<'r>(map: &'r mut HashMap<u32, String>, key: u32) -> &'r mut String {
    match map.get_mut(&key) {
        Some(value) => value,
        None => {
            map.insert(key, String::new());
            map.get_mut(&key).unwrap()
        }
    }
}
