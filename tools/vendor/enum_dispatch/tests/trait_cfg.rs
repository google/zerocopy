use enum_dispatch::enum_dispatch;

#[enum_dispatch(Traited)]
trait TestTrait {
    #[cfg(test)]
    fn test_method(&self) -> char;
    #[cfg(not(test))]
    fn release_method(&self) -> char;
}

impl TestTrait for A {
    #[cfg(test)]
    fn test_method(&self) -> char {
        'a'
    }
    #[cfg(not(test))]
    fn release_method(&self) -> char {
        'A'
    }
}

impl TestTrait for B {
    #[cfg(test)]
    fn test_method(&self) -> char {
        'b'
    }
    #[cfg(not(test))]
    fn release_method(&self) -> char {
        'B'
    }
}

pub struct A;
pub struct B;

#[enum_dispatch]
pub enum Traited {
    A,
    B,
}

#[test]
fn main() {
    let a = Traited::from(A);
    let b = Traited::from(B);

    #[cfg(test)]
    {
        assert_eq!(a.test_method(), 'a');
        assert_eq!(b.test_method(), 'b');
    }

    #[cfg(not(test))]
    {
        assert_eq!(a.release_method(), 'A');
        assert_eq!(b.release_method(), 'B');
    }
}
