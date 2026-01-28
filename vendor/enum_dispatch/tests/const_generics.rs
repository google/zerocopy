use enum_dispatch::enum_dispatch;

struct Nothing;
struct One(u8);
struct Array<const N: usize>([u8; N]);

impl<L, const N: usize, const M: u8, const O: bool> Trait<L, N, M, O> for Nothing {
    fn get_array(&self) -> [u8; N] {
        [0; N]
    }
}

impl<L, const N: usize, const M: u8, const O: bool> Trait<L, N, M, O> for One {
    fn get_array(&self) -> [u8; N] {
        [self.0; N]
    }
}

impl<L, const N: usize, const M: u8, const O: bool> Trait<L, N, M, O> for Array<N> {
    fn get_array(&self) -> [u8; N] {
        self.0
    }
}

impl<L, const N: usize, const M: u8, const O: bool> Trait<L, N, M, O> for Vec<L> {
    fn get_array(&self) -> [u8; N] {
        [self.len() as u8; N]
    }
}

#[enum_dispatch(Enum<L, N, M, O>)]
trait Trait<L, const N: usize, const M: u8, const O: bool> {
    fn get_array(&self) -> [u8; N];
}

#[enum_dispatch]
enum Enum<L, const N: usize, const M: u8, const O: bool> {
    Nothing,
    One,
    Array(Array<N>),
    L(Vec<L>),
}

#[test]
fn main() {
    let three: Enum<(), 3, b'0', true> = One(2).into();
    let eight: Enum<usize, 8, b'!', false> = One(3).into();
    assert_eq!(three.get_array(), [2, 2, 2]);
    assert_eq!(eight.get_array(), [3, 3, 3, 3, 3, 3, 3, 3]);
}
