#![allow(unused)]

use std::marker::PhantomData;
use std::rc::Rc;

pub struct Wrap<T>(Rc<()>, PhantomData<T>);
unsafe impl<T> Send for Wrap<T> where Wrap<Wrap<T>>: Send {}

pub fn check_wrap() {
    fn assert_send<T: Send>() {}
    assert_send::<Wrap<u32>>();
}
