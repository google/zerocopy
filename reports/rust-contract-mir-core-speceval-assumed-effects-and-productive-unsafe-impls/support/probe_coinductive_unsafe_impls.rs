#![allow(unused)]

use std::marker::PhantomData;
use std::rc::Rc;

// Case 1: direct coinductive unsafe impl on auto trait
pub struct NotSend(Rc<()>);
unsafe impl Send for NotSend where NotSend: Send {}

// Case 2: mutual cycle between auto-synthesized Send and unsafe impl Send
pub struct MutA(MutB);
pub struct MutB(Rc<()>, Option<Box<MutA>>);
unsafe impl Send for MutB where MutA: Send {}

// Case 4: legitimate recursive struct going through alloc's `unsafe impl<T: Send> Send for Box<T>`
pub struct BoxNode {
    pub val: u32,
    pub next: Option<Box<BoxNode>>,
}

// Case 5: custom pointer wrapper with strictly subterm-decreasing unsafe impl
pub struct MyBox<T>(*mut T);
unsafe impl<T: Send> Send for MyBox<T> {}
pub struct MyNode {
    pub val: u32,
    pub next: Option<MyBox<MyNode>>,
}

pub fn assert_send<T: Send>() {}

pub fn check_all() {
    assert_send::<NotSend>();
    assert_send::<MutA>();
    assert_send::<MutB>();
    assert_send::<BoxNode>();
    assert_send::<MyNode>();
}
