use enum_dispatch::enum_dispatch;
use std::marker::PhantomData;

trait Constants {
    const EXAMPLE: u32;
}

struct Zero;

impl Constants for Zero {
    const EXAMPLE: u32 = 0;
}

struct Five;

impl Constants for Five {
    const EXAMPLE: u32 = 5;
}

#[enum_dispatch(AnyMath)]
trait Math {
    fn get_number<C: ?Sized>(&self) -> u32
    where
        C: Constants;
}

struct Adder(pub u32);

impl Math for Adder {
    fn get_number<C: ?Sized>(&self) -> u32
    where
        C: Constants,
    {
        self.0 + C::EXAMPLE
    }
}

struct MultiplierWith<C2: Constants + ?Sized> {
    _phantom: PhantomData<*const C2>,
}

impl<C2: Constants + ?Sized> Math for MultiplierWith<C2> {
    fn get_number<C: ?Sized>(&self) -> u32
    where
        C: Constants,
    {
        C2::EXAMPLE * C::EXAMPLE
    }
}

#[enum_dispatch]
enum AnyMath {
    Adder,
    FiveMultiplier(MultiplierWith<Five>),
}

#[test]
fn main() {
    let two_adder: AnyMath = Adder(2).into();
    let five_multiplier: AnyMath = MultiplierWith::<Five> {
        _phantom: PhantomData,
    }
    .into();
    assert_eq!(two_adder.get_number::<Zero>(), 2);
    assert_eq!(two_adder.get_number::<Five>(), 7);
    assert_eq!(five_multiplier.get_number::<Zero>(), 0);
    assert_eq!(five_multiplier.get_number::<Five>(), 25);
}
