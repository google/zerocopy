//! Specimen 1: Single-inheritance, diamond multi-supertrait, empty-marker
//! supertrait, principal-erasing auto-trait upcasting, drop-glue slot[0]
//! null vs non-null dispatch, and VtblEntry::Vacant emission.

use std::sync::atomic::{AtomicU64, Ordering};

static DROP_LOG: AtomicU64 = AtomicU64::new(0);

pub trait SBase {
    fn s_base(&self) -> u64;
}
pub trait SMid: SBase {
    fn s_mid(&self) -> u64;
}
pub trait SSub: SMid {
    fn s_sub(&self) -> u64;
}

pub trait Base {
    fn base_id(&self) -> u64;
}
pub trait SuperA: Base {
    fn a_val(&self) -> u64;
}
pub trait SuperB: Base {
    fn b_val(&self) -> u64;
}
pub trait Diamond: SuperA + SuperB {
    fn d_val(&self) -> u64;
}

pub trait EmptyMarker {}
pub trait SecondSuper {
    fn sec_val(&self) -> u64;
}
pub trait SubAfterEmpty: EmptyMarker + SecondSuper {
    fn sub_e(&self) -> u64;
}

pub trait CondVacant<T> {
    fn always(&self) -> u64;
    #[allow(dead_code)]
    fn only_if_copy(&self) -> u64
    where
        T: Copy;
}

pub struct CopyLeaf(pub u64);

impl SBase for CopyLeaf {
    #[inline(never)]
    fn s_base(&self) -> u64 { self.0 + 101 }
}
impl SMid for CopyLeaf {
    #[inline(never)]
    fn s_mid(&self) -> u64 { self.0 + 102 }
}
impl SSub for CopyLeaf {
    #[inline(never)]
    fn s_sub(&self) -> u64 { self.0 + 103 }
}
impl Base for CopyLeaf {
    #[inline(never)]
    fn base_id(&self) -> u64 { self.0 + 1 }
}
impl SuperA for CopyLeaf {
    #[inline(never)]
    fn a_val(&self) -> u64 { self.0 + 2 }
}
impl SuperB for CopyLeaf {
    #[inline(never)]
    fn b_val(&self) -> u64 { self.0 + 3 }
}
impl Diamond for CopyLeaf {
    #[inline(never)]
    fn d_val(&self) -> u64 { self.0 + 4 }
}
impl EmptyMarker for CopyLeaf {}
impl SecondSuper for CopyLeaf {
    #[inline(never)]
    fn sec_val(&self) -> u64 { self.0 + 5 }
}
impl SubAfterEmpty for CopyLeaf {
    #[inline(never)]
    fn sub_e(&self) -> u64 { self.0 + 6 }
}
impl<T> CondVacant<T> for CopyLeaf {
    #[inline(never)]
    fn always(&self) -> u64 { self.0 + 7 }
    #[inline(never)]
    fn only_if_copy(&self) -> u64
    where
        T: Copy,
    {
        self.0 + 8
    }
}

pub struct DropLeaf {
    pub id: u64,
    pub tag: u64,
}
impl Drop for DropLeaf {
    #[inline(never)]
    fn drop(&mut self) {
        DROP_LOG.fetch_add(self.id * 1000 + self.tag, Ordering::SeqCst);
    }
}
impl Base for DropLeaf {
    #[inline(never)]
    fn base_id(&self) -> u64 { self.id + 10 }
}
impl SuperA for DropLeaf {
    #[inline(never)]
    fn a_val(&self) -> u64 { self.id + 20 }
}
impl SuperB for DropLeaf {
    #[inline(never)]
    fn b_val(&self) -> u64 { self.id + 30 }
}
impl Diamond for DropLeaf {
    #[inline(never)]
    fn d_val(&self) -> u64 { self.id + 40 }
}

fn vtable_addr<T: ?Sized>(p: &T) -> usize {
    let raw: [usize; 2] = unsafe { std::mem::transmute_copy(&p) };
    raw[1]
}

#[no_mangle]
#[inline(never)]
pub fn upcast_single_mid(s: &dyn SSub) -> &dyn SMid { s }

#[no_mangle]
#[inline(never)]
pub fn upcast_single_base(s: &dyn SSub) -> &dyn SBase { s }

#[no_mangle]
#[inline(never)]
pub fn upcast_d_to_a(d: &dyn Diamond) -> &dyn SuperA { d }

#[no_mangle]
#[inline(never)]
pub fn upcast_d_to_b(d: &dyn Diamond) -> &dyn SuperB { d }

#[no_mangle]
#[inline(never)]
pub fn upcast_d_to_base(d: &dyn Diamond) -> &dyn Base { d }

#[no_mangle]
#[inline(never)]
pub fn upcast_b_to_base(b: &dyn SuperB) -> &dyn Base { b }

#[no_mangle]
#[inline(never)]
pub fn upcast_empty_to_sec(e: &dyn SubAfterEmpty) -> &dyn SecondSuper { e }

#[no_mangle]
#[inline(never)]
pub fn upcast_erase_principal(d: &(dyn Diamond + Send)) -> &dyn Send { d }

#[no_mangle]
#[inline(never)]
pub fn make_copy_diamond(x: &CopyLeaf) -> &dyn Diamond { x }

#[no_mangle]
#[inline(never)]
pub fn make_drop_diamond(x: &DropLeaf) -> &dyn Diamond { x }

#[no_mangle]
#[inline(never)]
pub fn make_vacant(x: &CopyLeaf) -> &dyn CondVacant<String> { x }

#[no_mangle]
#[inline(never)]
pub fn drop_box_super_b(b: Box<dyn SuperB>) {
    drop(b);
}

#[no_mangle]
#[inline(never)]
pub fn drop_box_send(s: Box<dyn Send>) {
    drop(s);
}

fn main() {
    let c = CopyLeaf(100);

    // 1. Single inheritance chain: prefix reuse throughout
    let ss: &dyn SSub = &c;
    let sm = upcast_single_mid(ss);
    let sb = upcast_single_base(ss);
    let single_same_mid = vtable_addr(ss) == vtable_addr(sm);
    let single_same_base = vtable_addr(ss) == vtable_addr(sb);
    let single_dispatch_ok =
        ss.s_sub() == c.s_sub() && sm.s_mid() == c.s_mid() && sb.s_base() == c.s_base();

    // 2. Diamond hierarchy on CopyLeaf (!needs_drop)
    let d_c = make_copy_diamond(&c);
    let a_c = upcast_d_to_a(d_c);
    let b_c = upcast_d_to_b(d_c);
    let base_direct_c = upcast_d_to_base(d_c);
    let base_via_b_c = upcast_b_to_base(b_c);
    let diamond_a_reuses_vptr = vtable_addr(d_c) == vtable_addr(a_c);
    let diamond_base_reuses_vptr = vtable_addr(d_c) == vtable_addr(base_direct_c);
    let diamond_b_uses_secondary_vptr = vtable_addr(d_c) != vtable_addr(b_c);
    let diamond_b_to_base_reuses_vptr = vtable_addr(b_c) == vtable_addr(base_via_b_c);
    let diamond_copy_dispatch_ok = d_c.d_val() == c.d_val()
        && a_c.a_val() == c.a_val()
        && a_c.base_id() == c.base_id()
        && b_c.b_val() == c.b_val()
        && b_c.base_id() == c.base_id()
        && base_direct_c.base_id() == c.base_id()
        && base_via_b_c.base_id() == c.base_id();

    // 3. Empty marker supertrait prefix optimization
    let e_c: &dyn SubAfterEmpty = &c;
    let sec_c = upcast_empty_to_sec(e_c);
    let empty_marker_reuses_vptr = vtable_addr(e_c) == vtable_addr(sec_c);
    let empty_marker_dispatch_ok =
        e_c.sub_e() == c.sub_e() && sec_c.sec_val() == c.sec_val();

    // 4. Principal-erasing auto-trait upcast
    let ds: &(dyn Diamond + Send) = &c;
    let erased = upcast_erase_principal(ds);
    let auto_erase_reuses_vptr = vtable_addr(ds) == vtable_addr(erased);

    // 5. Vacant slot trait object
    let vc = make_vacant(&c);
    let vacant_always = vc.always();

    // 6. Box<dyn Diamond> upcasting + drop glue (both CopyLeaf null-drop and DropLeaf non-null drop)
    let box_copy_d: Box<dyn Diamond> = Box::new(CopyLeaf(200));
    let box_copy_b: Box<dyn SuperB> = box_copy_d;
    let box_copy_b_val = box_copy_b.b_val();
    drop_box_super_b(box_copy_b);

    let dl_ref = DropLeaf { id: 3, tag: 9 };
    let d_dl = make_drop_diamond(&dl_ref);
    let b_dl = upcast_d_to_b(d_dl);
    let drop_leaf_dispatch_ok = d_dl.d_val() == dl_ref.d_val()
        && b_dl.b_val() == dl_ref.b_val()
        && b_dl.base_id() == dl_ref.base_id();
    drop(dl_ref);
    let drop_after_concrete = DROP_LOG.load(Ordering::SeqCst);

    let box_dl_d: Box<dyn Diamond> = Box::new(DropLeaf { id: 5, tag: 1 });
    let box_dl_b: Box<dyn SuperB> = box_dl_d;
    let box_dl_b_val = box_dl_b.b_val();
    drop_box_super_b(box_dl_b);
    let drop_after_upcast_b = DROP_LOG.load(Ordering::SeqCst);

    let box_dl_send: Box<dyn Diamond + Send> = Box::new(DropLeaf { id: 7, tag: 2 });
    let box_erased: Box<dyn Send> = box_dl_send;
    drop_box_send(box_erased);
    let drop_after_upcast_send = DROP_LOG.load(Ordering::SeqCst);

    println!("single_same_mid={single_same_mid}");
    println!("single_same_base={single_same_base}");
    println!("single_dispatch_ok={single_dispatch_ok}");
    println!("diamond_a_reuses_vptr={diamond_a_reuses_vptr}");
    println!("diamond_base_reuses_vptr={diamond_base_reuses_vptr}");
    println!("diamond_b_uses_secondary_vptr={diamond_b_uses_secondary_vptr}");
    println!("diamond_b_to_base_reuses_vptr={diamond_b_to_base_reuses_vptr}");
    println!("diamond_copy_dispatch_ok={diamond_copy_dispatch_ok}");
    println!("empty_marker_reuses_vptr={empty_marker_reuses_vptr}");
    println!("empty_marker_dispatch_ok={empty_marker_dispatch_ok}");
    println!("auto_erase_reuses_vptr={auto_erase_reuses_vptr}");
    println!("vacant_always={vacant_always}");
    println!("box_copy_b_val={box_copy_b_val}");
    println!("drop_leaf_dispatch_ok={drop_leaf_dispatch_ok}");
    println!("drop_after_concrete={drop_after_concrete}");
    println!("box_dl_b_val={box_dl_b_val}");
    println!("drop_after_upcast_b={drop_after_upcast_b}");
    println!("drop_after_upcast_send={drop_after_upcast_send}");
}
