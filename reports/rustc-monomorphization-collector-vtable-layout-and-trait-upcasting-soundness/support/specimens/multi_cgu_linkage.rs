//! Specimen 3: Multi-CGU partitioning, Internal vs External linkage,
//! LocalCopy vs GloballyShared instantiation modes, absence of LinkOnceODR,
//! and intra-crate duplicate private vtable addresses across CGUs.

pub trait Ping {
    fn ping(&self) -> u64;
}
pub struct Token(pub u64);
impl Ping for Token {
    #[inline(never)]
    fn ping(&self) -> u64 {
        self.0 + 1
    }
}

pub mod mod_a {
    use super::*;

    #[inline(never)]
    pub fn make_dyn_a(t: &Token) -> &dyn Ping {
        t
    }

    #[inline(never)]
    pub fn shared_generic<T: Copy>(x: T) -> T {
        x
    }

    #[inline(always)]
    pub fn always_inline_helper(x: u64) -> u64 {
        x.wrapping_mul(3)
    }

    #[inline(never)]
    pub fn only_in_a(x: u64) -> u64 {
        private_only_a(x) + always_inline_helper(x)
    }

    #[inline(never)]
    fn private_only_a(x: u64) -> u64 {
        x + 10
    }
}

pub mod mod_b {
    use super::*;

    #[inline(never)]
    pub fn make_dyn_b(t: &Token) -> &dyn Ping {
        t
    }

    #[inline(never)]
    pub fn call_cross_cgu(x: u64) -> u64 {
        mod_a::shared_generic(x) + mod_a::always_inline_helper(x) + mod_a::only_in_a(x)
    }
}

fn vtable_addr<T: ?Sized>(p: &T) -> usize {
    let raw: [usize; 2] = unsafe { std::mem::transmute_copy(&p) };
    raw[1]
}

fn main() {
    let t = Token(42);
    let da = mod_a::make_dyn_a(&t);
    let db = mod_b::make_dyn_b(&t);
    let va = vtable_addr(da);
    let vb = vtable_addr(db);
    let res = da.ping() + db.ping() + mod_b::call_cross_cgu(5);
    println!("same_vtable={}", va == vb);
    println!("res={res}");
}
