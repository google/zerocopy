use std::cell::Cell;
#[inline(never)] fn update(x: &mut [u32]) {
 let (left,right)=x.split_at_mut(2); left[0]+=10; right[0]+=20;
}
fn main() {
 let mut data=[1u32,2,3,4]; update(&mut data); assert!(data == [11,2,23,4]);
 let cell=Cell::new(7u32); let shared=&cell; shared.set(shared.get()+5); assert!(cell.get() == 12);
}
