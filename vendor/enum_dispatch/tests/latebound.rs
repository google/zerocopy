#![deny(late_bound_lifetime_arguments)]

use enum_dispatch::enum_dispatch;

pub struct S<'a, T>(std::marker::PhantomData<&'a T>);
pub trait Trait<'a> {}

#[enum_dispatch]
pub trait FooAPI {
    fn foo_warn<'a>(&mut self) -> &'a u32 {
        unimplemented!()
    }

    fn foo_err<'a, 'b>(&'a self, x: &'b u32) -> &'b u32 {
        x
    }

    // have late bound parameters
    fn e1<'a>(&self) {}
    fn e2(&self, _e: &()) {}
    fn e3(&self, _e: &()) -> &() {
        unimplemented!()
    }
    fn e4<'a>(&self, _e: &'a ()) -> &'a () {
        unimplemented!()
    }
    fn e5(&self) {}
    fn e6(&mut self) {}
    fn e7<'a, 'b>(&self) {}
    fn e8<'a>(&self, _t: &'a ()) {}
    fn e9<'a>(&self, _t: &()) -> &'a () {
        unimplemented!()
    }
    fn e10<'a>(&self, _t: &mut ()) -> &'a () {
        unimplemented!()
    }
    fn e11<'a>(&self, _t: &mut ()) -> &'a mut () {
        unimplemented!()
    }
    fn e12<'a>(&self, _t: ()) -> &'static mut () {
        unimplemented!()
    }
    fn e13<'a>(&self, _t: &'a S<'static, ()>) -> &'static () {
        unimplemented!()
    }
    fn e14<'a>(&self, _t: &'static S<'a, ()>) -> &'static () {
        unimplemented!()
    }
    fn e15<'a>(&self, _t: &'a S<'static, ()>) -> &'a () {
        unimplemented!()
    }
    fn e16<'a>(&self, _t: &'a S<'a, ()>) -> &'static () {
        unimplemented!()
    }
    fn e17<'a, 'b, 'c, T: Trait<'b>>(&self) {}
    fn e18<'a, 'b, T: Trait<'b>>(&self) {}
    fn e19<'a, 'b, T: Trait<'b>, F>(&self, _e: F)
    where
        F: for<'d, 'c> FnOnce(),
    {
    }

    // have no late bound parameters
    fn e20(&self) {}
    fn e21<'a>(&self) -> &'a () {
        unimplemented!()
    }
    fn e22<'a>(&self, _t: ()) -> &'a () {
        unimplemented!()
    }
    fn e23<'a>(&self, _e: &'static ()) -> &'a () {
        unimplemented!()
    }
    fn e24(&self, _t: ()) -> &'static () {
        unimplemented!()
    }
    fn e25(&self, _t: &'static ()) -> &'static () {
        unimplemented!()
    }
    fn e26(&self, _t: &'static S<()>) -> &'static () {
        unimplemented!()
    }
    fn e27(&self, _t: &'static S<'static, ()>) -> &'static () {
        unimplemented!()
    }
    fn e28<'a>(&self, _t: &'static S<'static, ()>) -> &'a () {
        unimplemented!()
    }
    fn e29<'b, T: Trait<'b>>(&self) {}
    fn e30<'b, T: Trait<'b>, F>(&self, _e: F)
    where
        F: for<'d, 'c> FnOnce(),
    {
    }
    fn e31<'b, T: Trait<'b>, F>(&self, _e: F)
    where
        F: for<'d, 'c> FnOnce(&'b ()),
    {
    }
    fn e32<'b, F>(&self, _e: F)
    where
        F: for<'d, 'c> FnOnce(&'b ()),
    {
    }
}

#[enum_dispatch(FooAPI)]
pub enum Foo {
    Something,
}

pub struct Something(u32);

impl FooAPI for Something {}

#[test]
fn main() {
    assert_eq!(*Something(2).foo_err(&8), 8);
}
