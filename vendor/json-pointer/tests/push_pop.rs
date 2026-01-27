use json_pointer::JsonPointer;
use quickcheck::{TestResult, quickcheck};

quickcheck! {

/// Pushing then popping should not affect the pointer or the pushed/popped
/// value.
fn push_then_pop_is_identity(s: String, t: String) -> TestResult {
    match s.parse::<JsonPointer<_, _>>() {
        Ok(mut ptr) => {
            let str1 = ptr.to_string();
            ptr.push(t.clone());
            let t2 = ptr.pop();
            let str2 = ptr.to_string();
            if Some(t) == t2 && str1 == str2 {
                TestResult::passed()
            } else {
                TestResult::failed()
            }
        },
        Err(_) => TestResult::discard(),
    }
}

}
