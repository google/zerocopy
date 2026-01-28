use enum_dispatch::enum_dispatch;

pub struct SuperFoo<T: Bar> {
    _bar: T,
}

impl<T: Bar> Foo<T> for SuperFoo<T> {
    fn do_something(&mut self, _val: T) {
        println!("SuperFoo");
    }
}

pub struct UltraFoo<T: Bar> {
    _bar: T,
}

impl<T: Bar> Foo<T> for UltraFoo<T> {
    fn do_something(&mut self, _val: T) {
        println!("UltraFoo");
    }
}

pub trait Bar {}

#[enum_dispatch]
pub trait Foo<T: Bar> {
    fn do_something(&mut self, val: T);
}

#[enum_dispatch(Foo)]
pub enum AnyFoo<T: Bar> {
    SuperFoo(SuperFoo<T>),
    UltraFoo(UltraFoo<T>),
}

#[enum_dispatch]
pub trait Faz {}

use std::marker::PhantomData;
pub struct SuperFaz<'a>(PhantomData<&'a u8>);
pub struct UltraFaz();

impl<'a> Faz for SuperFaz<'a> {}
impl Faz for UltraFaz {}

#[enum_dispatch(Faz)]
pub enum AnyFaz<'a> {
    SuperFaz(SuperFaz<'a>),
    UltraFaz(UltraFaz),
}

#[test]
fn main() {
    use core::convert::TryInto;

    let anyfaz: AnyFaz = SuperFaz(PhantomData::<&u8>::default()).into();

    let superfaz: Result<SuperFaz, _> = anyfaz.try_into();

    assert!(superfaz.is_ok());
}
