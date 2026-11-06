use zerocopy::{FromZeros, Unalign};
use std::{cell::Cell, rc::Rc, panic::{catch_unwind, AssertUnwindSafe}};
struct Tracked { value: u64, drops: Rc<Cell<usize>> }
impl Drop for Tracked { fn drop(&mut self) { self.drops.set(self.drops.get()+1); } }
#[repr(C, packed)] struct Packet { prefix: u8, value: Unalign<Tracked> }
#[repr(align(8))] struct Aligned(Packet);
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let drops=Rc::new(Cell::new(0));
    let mut backing=Aligned(Packet { prefix: 19, value: Unalign::new(Tracked {value: 7,drops:drops.clone()}) });
    let address=std::ptr::addr_of!(backing.0.value) as usize;
    assert_ne!(address % std::mem::align_of::<Tracked>(),0);
    let result=backing.0.value.update(|v| { assert_eq!(v.value,7);assert_eq!(drops.get(),0);v.value=11;23 });
    assert_eq!(result,23);assert_eq!(drops.get(),0);
    let expected_panic=catch_unwind(AssertUnwindSafe(||backing.0.value.update(|v| {assert_eq!(v.value,11);v.value=29;panic!("intentional callback unwind") })));
    assert!(expected_panic.is_err());assert_eq!(drops.get(),0);
    backing.0.value.update(|v|assert_eq!(v.value,29));
    assert_eq!(backing.0.prefix,19);drop(backing);assert_eq!(drops.get(),1);
    let mut direct=Unalign::new(1u8);
    assert!(catch_unwind(AssertUnwindSafe(||direct.update(|v|{*v=9;panic!("intentional byte unwind")}))).is_err());
    assert_eq!(direct.get(),9);
    let mut restores=0;
    for byte in 0..=255u8 {
        let result:Result<bool,_>=zerocopy::try_transmute!(byte);
        match result { Ok(v)=>assert_eq!(u8::from(v),byte), Err(e)=>{assert_eq!(e.into_src(),byte);restores+=1;} }
    }
    assert_eq!(restores,254);
    let mut growth=vec![5u16,7,9];let old_capacity=growth.capacity();
    u16::insert_vec_zeroed(&mut growth,1,4).unwrap();assert_eq!(growth,[5,0,0,0,0,7,9]);assert!(growth.capacity()>old_capacity);
    u16::extend_vec_zeroed(&mut growth,2).unwrap();assert_eq!(growth,[5,0,0,0,0,7,9,0,0]);
    let snapshot=growth.clone();
    assert!(u16::insert_vec_zeroed(&mut growth,1,usize::MAX).is_err());assert_eq!(growth,snapshot);
    assert!(catch_unwind(AssertUnwindSafe(||u16::insert_vec_zeroed(&mut growth,100,1))).is_err());assert_eq!(growth,snapshot);
    assert_eq!(u16::new_vec_zeroed(16).unwrap(),[0;16]);
    let mut zst=vec![(),()];<()>::insert_vec_zeroed(&mut zst,1,3).unwrap();assert_eq!(zst.len(),5);
    println!("unaligned_normal=1;unaligned_unwind=1;direct_unwind=1;drop_exactly_once=1;conditional_inputs=256;restores=254;growth_controls=6;all_match=true");
}
