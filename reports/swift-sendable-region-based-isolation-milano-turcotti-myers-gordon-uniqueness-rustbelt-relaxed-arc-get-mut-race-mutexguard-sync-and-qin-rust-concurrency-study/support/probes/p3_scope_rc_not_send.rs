// Expect rejection: Rc<T> is !Send, so a scoped thread cannot capture a clone of it.
use std::rc::Rc;
fn main() {
    let r = Rc::new(5u32);
    std::thread::scope(|s| {
        let r2 = Rc::clone(&r);
        s.spawn(move || println!("{}", r2));
    });
}
