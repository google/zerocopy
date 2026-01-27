use core::convert::TryInto;
use enum_dispatch::enum_dispatch;

#[enum_dispatch(Traited1)]
#[enum_dispatch(Traited2)]
trait Trait {
    fn describe(&self) -> char;
}

impl Trait for A {
    fn describe(&self) -> char {
        'A'
    }
}

impl Trait for B {
    fn describe(&self) -> char {
        'B'
    }
}

impl Trait for C {
    fn describe(&self) -> char {
        'C'
    }
}

#[enum_dispatch(Traited1, Traited2)]
trait TraitSingleLine {
    fn as_string(&self) -> String;
}

impl TraitSingleLine for A {
    fn as_string(&self) -> String {
        "A".to_string()
    }
}

impl TraitSingleLine for B {
    fn as_string(&self) -> String {
        " B ".to_string()
    }
}

impl TraitSingleLine for C {
    fn as_string(&self) -> String {
        self.describe().to_string()
    }
}

pub struct A;
pub struct B;
pub struct C;

#[enum_dispatch]
pub enum Traited1 {
    A,
    B,
    C,
}

#[enum_dispatch]
pub enum Traited2 {
    A,
    B,
    C,
}

#[test]
fn main() {
    let a = Traited1::from(A);
    let b = Traited1::from(B);
    let c = Traited1::from(C);

    assert_eq!(a.describe(), 'A');
    assert_eq!(b.describe(), 'B');
    assert_eq!(c.describe(), 'C');

    assert_eq!(a.as_string(), "A".to_string());
    assert_eq!(b.as_string(), " B ".to_string());
    assert_eq!(c.as_string(), "C".to_string());

    let b_from_c: Result<B, _> = c.try_into();
    assert!(b_from_c.is_err());
    assert_eq!(b_from_c.err().unwrap(), "Tried to convert variant C to B");

    let a_from_a: Result<A, _> = a.try_into();
    assert!(a_from_a.is_ok());

    let a_sl = Traited2::from(A);
    let b_sl = Traited2::from(B);
    let c_sl = Traited2::from(C);

    assert_eq!(a_sl.describe(), 'A');
    assert_eq!(b_sl.describe(), 'B');
    assert_eq!(c_sl.describe(), 'C');

    assert_eq!(a_sl.as_string(), "A".to_string());
    assert_eq!(b_sl.as_string(), " B ".to_string());
    assert_eq!(c_sl.as_string(), "C".to_string());

    let b_from_c_sl: Result<B, _> = c_sl.try_into();
    assert!(b_from_c_sl.is_err());
    assert_eq!(
        b_from_c_sl.err().unwrap(),
        "Tried to convert variant C to B"
    );

    let a_from_a_sl: Result<A, _> = a_sl.try_into();
    assert!(a_from_a_sl.is_ok());
}
