use std::{cell::Cell, future::{pending, Future}, rc::Rc, task::{Context, Poll, Waker}};

struct Counted(Rc<Cell<u32>>);
impl Drop for Counted {
    fn drop(&mut self) { self.0.set(self.0.get() + 1); }
}

fn main() {
    let drops = Rc::new(Cell::new(0));
    let owned = Counted(drops.clone());
    let unpolled = async move { let _owned = owned; pending::<()>().await; };
    drop(unpolled);
    assert_eq!(drops.get(), 1);
    let owned = Counted(drops.clone());
    let mut suspended = Box::pin(async move { let _owned = owned; pending::<()>().await; });
    let mut context = Context::from_waker(Waker::noop());
    assert!(matches!(suspended.as_mut().poll(&mut context), Poll::Pending));
    assert_eq!(drops.get(), 1);
    drop(suspended);
    assert_eq!(drops.get(), 2);
    println!("unpolled=1; suspended_before_drop=1; suspended_after_drop=2");
}
