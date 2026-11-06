#![feature(min_specialization)]
#![allow(dead_code)]

trait Family {
    type Borrow<'a> where Self: 'a;
    fn borrow<'a>(&'a self) -> Self::Borrow<'a>;
}
struct Buffer([u8; 4]);
impl Family for Buffer {
    type Borrow<'a> = &'a [u8] where Self: 'a;
    fn borrow<'a>(&'a self) -> Self::Borrow<'a> { &self.0 }
}
fn lend<'a, F: Family>(x: &'a F) -> F::Borrow<'a> { x.borrow() }

struct Link { next: Option<Box<Link>> }
fn require_send<T: Send>() {}

trait Tag { fn tag() -> u8 { 1 } }
impl<T> Tag for T { default fn tag() -> u8 { 2 } }
impl Tag for u8 { fn tag() -> u8 { 3 } }
fn selected<T: Tag>() -> u8 { T::tag() }

fn main() {
    let b = Buffer([1, 2, 3, 4]);
    assert_eq!(lend(&b), &[1, 2, 3, 4]);
    require_send::<Link>();
    assert_eq!(selected::<u8>(), 3);
    assert_eq!(selected::<u16>(), 2);
    println!("GAT_lend=4 recursive_Send=accepted selected_u8=3 selected_u16=2");
}
