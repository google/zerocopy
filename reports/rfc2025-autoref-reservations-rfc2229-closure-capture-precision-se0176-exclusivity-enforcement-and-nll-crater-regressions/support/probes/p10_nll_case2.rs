// RFC 2094 problem case #2. Expect: accepted under NLL.
use std::collections::HashMap;
fn process(_v: &mut u32) {}
pub fn process_or_default(map: &mut HashMap<u32, u32>, key: u32) {
    match map.get_mut(&key) {
        Some(value) => process(value),
        None => {
            map.insert(key, u32::default());
        }
    }
}
