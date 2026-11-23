#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::mem::{align_of, align_of_val, size_of, size_of_val};
use std::sync::Mutex;

static LOG: Mutex<Vec<String>> = Mutex::new(Vec::new());
static RECORD_DEALLOC: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());

struct SpyAlloc;

unsafe impl GlobalAlloc for SpyAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if (layout.size() == 32 || layout.size() == 64) && layout.align() == 32 {
            if let Ok(mut guard) = RECORD_DEALLOC.try_lock() {
                guard.push((layout.size(), layout.align()));
            }
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOC: SpyAlloc = SpyAlloc;

trait SuperA {
    fn id_a(&self) -> u64;
}

trait SuperB {
    fn id_b(&self) -> u64;
}

trait Sub: SuperA + SuperB {
    fn id_sub(&self) -> u64;
}

// 3-hop secondary upcast chain: Tier3 -> Tier2 -> Tier1 -> Tier0
trait Prim0 {
    fn p0(&self) -> u64;
}
trait Prim1 {
    fn p1(&self) -> u64;
}
trait Prim2 {
    fn p2(&self) -> u64;
}
trait Tier0 {
    fn t0(&self) -> u64;
}
trait Tier1: Prim1 + Tier0 {
    fn t1(&self) -> u64;
}
trait Tier2: Prim2 + Tier1 {
    fn t2(&self) -> u64;
}
trait Tier3: Prim0 + Tier2 {
    fn t3(&self) -> u64;
}

struct InnerDrop {
    tag: &'static str,
}

impl Drop for InnerDrop {
    fn drop(&mut self) {
        LOG.lock().unwrap().push(format!("drop_{}", self.tag));
    }
}

#[repr(C, align(32))]
struct DropTracker {
    a: u64,
    b: u64,
    inner: InnerDrop,
}

impl Drop for DropTracker {
    fn drop(&mut self) {
        LOG.lock().unwrap().push("drop_outer".to_string());
    }
}

impl SuperA for DropTracker {
    fn id_a(&self) -> u64 {
        self.a
    }
}
impl SuperB for DropTracker {
    fn id_b(&self) -> u64 {
        self.b
    }
}
impl Sub for DropTracker {
    fn id_sub(&self) -> u64 {
        self.a + self.b
    }
}
impl Prim0 for DropTracker {
    fn p0(&self) -> u64 {
        10
    }
}
impl Prim1 for DropTracker {
    fn p1(&self) -> u64 {
        11
    }
}
impl Prim2 for DropTracker {
    fn p2(&self) -> u64 {
        12
    }
}
impl Tier0 for DropTracker {
    fn t0(&self) -> u64 {
        self.a + 100
    }
}
impl Tier1 for DropTracker {
    fn t1(&self) -> u64 {
        self.a + 101
    }
}
impl Tier2 for DropTracker {
    fn t2(&self) -> u64 {
        self.a + 102
    }
}
impl Tier3 for DropTracker {
    fn t3(&self) -> u64 {
        self.a + 103
    }
}

#[repr(C, align(32))]
struct NoDropBig {
    words: [u64; 8],
}

impl SuperA for NoDropBig {
    fn id_a(&self) -> u64 {
        self.words[0]
    }
}
impl SuperB for NoDropBig {
    fn id_b(&self) -> u64 {
        self.words[1]
    }
}
impl Sub for NoDropBig {
    fn id_sub(&self) -> u64 {
        self.words[0] + self.words[1]
    }
}

#[inline(never)]
fn upcast_box_to_b(b: Box<dyn Sub>) -> Box<dyn SuperB> {
    b
}

#[inline(never)]
fn upcast_chain_3hop(b: Box<dyn Tier3>) -> Box<dyn Tier0> {
    let b2: Box<dyn Tier2> = b;
    let b1: Box<dyn Tier1> = b2;
    let b0: Box<dyn Tier0> = b1;
    b0
}

fn main() {
    let concrete_size = size_of::<DropTracker>();
    let concrete_align = align_of::<DropTracker>();

    let boxed_sub: Box<dyn Sub> = Box::new(DropTracker {
        a: 1,
        b: 2,
        inner: InnerDrop { tag: "inner" },
    });
    let sz_sub = size_of_val(&*boxed_sub);
    let al_sub = align_of_val(&*boxed_sub);

    let boxed_b: Box<dyn SuperB> = upcast_box_to_b(boxed_sub);
    let sz_b = size_of_val(&*boxed_b);
    let al_b = align_of_val(&*boxed_b);
    let val_b = boxed_b.id_b();

    drop(boxed_b);
    LOG.lock().unwrap().push("after_drop".to_string());

    // 3-hop secondary upcast chain
    let boxed_t3: Box<dyn Tier3> = Box::new(DropTracker {
        a: 5,
        b: 6,
        inner: InnerDrop { tag: "inner_3hop" },
    });
    let boxed_t0: Box<dyn Tier0> = upcast_chain_3hop(boxed_t3);
    let sz_t0 = size_of_val(&*boxed_t0);
    let al_t0 = align_of_val(&*boxed_t0);
    let val_t0 = boxed_t0.t0();
    drop(boxed_t0);

    // !needs_drop Box<dyn Sub> -> Box<dyn SuperB>
    let boxed_nodrop: Box<dyn Sub> = Box::new(NoDropBig { words: [11, 22, 0, 0, 0, 0, 0, 0] });
    let boxed_nodrop_b: Box<dyn SuperB> = upcast_box_to_b(boxed_nodrop);
    let sz_nd = size_of_val(&*boxed_nodrop_b);
    let al_nd = align_of_val(&*boxed_nodrop_b);
    let val_nd = boxed_nodrop_b.id_b();
    drop(boxed_nodrop_b);

    let log = LOG.lock().unwrap().clone();
    let deallocs = RECORD_DEALLOC.lock().unwrap().clone();

    println!(
        "CONCRETE=({concrete_size},{concrete_align}) SUB=({sz_sub},{al_sub}) B=({sz_b},{al_b}) T0=({sz_t0},{al_t0}) ND=({sz_nd},{al_nd})"
    );
    println!("VALS={val_b},{val_t0},{val_nd}");
    println!("DROP_ORDER={log:?}");
    println!("DEALLOC_LAYOUTS={deallocs:?}");
}
