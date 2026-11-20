// RFC 2094 problem case #2: reference used in only one match arm.
use std::collections::HashMap;
fn process(_v: &mut String) {}
pub fn process_or_default(map: &mut HashMap<u32, String>, key: u32) {
    match map.get_mut(&key) {
        Some(value) => process(value),
        None => {
            map.insert(key, String::new());
        }
    }
}
