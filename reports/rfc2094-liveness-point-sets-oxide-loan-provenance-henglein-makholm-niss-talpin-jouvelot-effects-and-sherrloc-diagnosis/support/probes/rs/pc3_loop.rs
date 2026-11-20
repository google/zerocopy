// Problem case #3 inside a loop: a conditionally returned borrow plus a loop back edge.
use std::collections::HashMap;
pub fn get_or_insert_loop<'r>(map: &'r mut HashMap<u32, String>, key: u32) -> &'r String {
    loop {
        if let Some(v) = map.get(&key) {
            return v;
        }
        map.insert(key, String::new());
    }
}
