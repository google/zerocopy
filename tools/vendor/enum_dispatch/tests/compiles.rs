use core::convert::TryInto;
use enum_dispatch::enum_dispatch;

#[enum_dispatch(Traited)]
trait TestTrait {
    fn describe(&self) -> char;
    fn default_impl(&self) -> Vec<i8> {
        vec![0, 1, 2, 3]
    }
    fn has_args(&self, arg1: usize, arg2: &str) -> String;
    fn mutable(&mut self, argument: f32);
    fn self_by_value(self, argument: f32) -> f32;
}

impl TestTrait for A {
    fn describe(&self) -> char {
        'A'
    }

    fn has_args(&self, arg1: usize, arg2: &str) -> String {
        format!("A{},{}", arg1, arg2)
    }

    fn mutable(&mut self, _argument: f32) {}

    fn self_by_value(self, argument: f32) -> f32 {
        argument + 1.
    }
}

impl TestTrait for B {
    fn describe(&self) -> char {
        'B'
    }

    fn default_impl(&self) -> Vec<i8> {
        vec![0, 1, 2, 3, 4]
    }

    fn has_args(&self, arg1: usize, arg2: &str) -> String {
        format!("B{},{}", arg1, arg2)
    }

    fn mutable(&mut self, _argument: f32) {}

    fn self_by_value(self, argument: f32) -> f32 {
        argument + 2.
    }
}

impl TestTrait for C {
    fn describe(&self) -> char {
        'C'
    }

    fn default_impl(&self) -> Vec<i8> {
        vec![self.custom_number as i8; 10]
    }

    fn has_args(&self, arg1: usize, arg2: &str) -> String {
        format!(
            "C{},{}+{}",
            self.custom_number * arg1 as f64,
            arg2,
            self.custom_string
        )
    }

    fn mutable(&mut self, argument: f32) {
        self.custom_number = argument.into();
    }

    fn self_by_value(self, argument: f32) -> f32 {
        argument + self.custom_number as f32
    }
}

pub struct A;
pub struct B;
pub struct C {
    custom_string: String,
    custom_number: f64,
}
pub struct D {
    a_string: String,
}

impl TestTrait for D {
    fn describe(&self) -> char {
        'D'
    }

    fn default_impl(&self) -> Vec<i8> {
        vec![self.a_string.len() as i8; 15]
    }

    fn has_args(&self, arg1: usize, arg2: &str) -> String {
        format!("D{},{} ==> {}", arg1, arg2, self.a_string)
    }

    fn mutable(&mut self, argument: f32) {
        self.a_string = format!("updated as {}", argument);
    }

    fn self_by_value(self, argument: f32) -> f32 {
        argument * 9. + self.a_string.len() as f32
    }
}

#[enum_dispatch]
pub enum Traited {
    A,
    B,
    C,
    LetterD(D),
}

#[test]
fn main() {
    let mut a = Traited::from(A);
    let mut b = Traited::from(B);
    let mut c = Traited::from(C {
        custom_string: "the letter C".to_string(),
        custom_number: 4.2,
    });
    let mut d: Traited = D {
        a_string: "contained D".to_string(),
    }
    .into();

    match d {
        Traited::A(_) => assert!(false),
        Traited::B(_) => assert!(false),
        Traited::C(_) => assert!(false),
        Traited::LetterD(_) => assert!(true),
    }

    assert_eq!(a.describe(), 'A');
    assert_eq!(b.describe(), 'B');
    assert_eq!(c.describe(), 'C');
    assert_eq!(d.describe(), 'D');
    assert_eq!(a.default_impl().len(), 4);
    assert_eq!(b.default_impl().len(), 5);
    assert_eq!(c.default_impl().len(), 10);
    assert_eq!(c.default_impl()[2], 4);
    assert_eq!(d.default_impl().len(), 15);
    assert_eq!(a.has_args(10, "Argument of A"), "A10,Argument of A");
    assert_eq!(b.has_args(29, "B's argument"), "B29,B's argument");
    assert_eq!(
        c.has_args(42, "a C parameter"),
        "C176.4,a C parameter+the letter C"
    );
    assert_eq!(
        d.has_args(800, "provided to D"),
        "D800,provided to D ==> contained D"
    );
    a.mutable(9.0);
    b.mutable(10.0);
    c.mutable(11.0);
    d.mutable(90.0);
    assert_eq!(a.self_by_value(8.2), 9.2);
    assert_eq!(b.self_by_value(123.45), 125.45);
    assert_eq!(c.self_by_value(2.4), 13.4);
    assert_eq!(d.self_by_value(3.), 40.);

    let d: Traited = D {
        a_string: "contained D".to_string(),
    }
    .into();
    let d_from_d: Result<D, _> = d.try_into();
    assert!(d_from_d.is_ok());

    let c = Traited::from(C {
        custom_string: "the letter C".to_string(),
        custom_number: 4.2,
    });
    let d_from_c: Result<D, _> = c.try_into();
    assert!(d_from_c.is_err());
    assert_eq!(
        d_from_c.err().unwrap(),
        "Tried to convert variant C to LetterD"
    );
}
