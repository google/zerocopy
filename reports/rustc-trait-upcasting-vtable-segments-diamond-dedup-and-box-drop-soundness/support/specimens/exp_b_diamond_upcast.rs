#![allow(dead_code)]

trait Root {
    fn root(&self) -> u64;
}

trait Sibling {
    fn sib(&self) -> u64;
}

trait Left: Root {
    fn left(&self) -> u64;
}

trait Right: Root {
    fn right(&self) -> u64;
}

trait Diamond: Left + Right {
    fn dia(&self) -> u64;
}

// Non-primary Right path: Sibling first, Root second.
trait RightSecond: Sibling + Root {
    fn rsec(&self) -> u64;
}

trait DiamondAsym: Left + RightSecond {
    fn dia2(&self) -> u64;
}

trait GenRoot<T> {
    fn tag(&self) -> u64;
}

trait AmbigDia: GenRoot<u8> + GenRoot<u16> {
    fn ambig(&self) -> u64;
}

struct Node(u64);

impl Root for Node {
    #[inline(never)]
    fn root(&self) -> u64 {
        self.0 + 1
    }
}

impl Sibling for Node {
    #[inline(never)]
    fn sib(&self) -> u64 {
        self.0 + 5
    }
}

impl Left for Node {
    #[inline(never)]
    fn left(&self) -> u64 {
        self.0 + 2
    }
}

impl Right for Node {
    #[inline(never)]
    fn right(&self) -> u64 {
        self.0 + 3
    }
}

impl Diamond for Node {
    #[inline(never)]
    fn dia(&self) -> u64 {
        self.0 + 4
    }
}

impl RightSecond for Node {
    #[inline(never)]
    fn rsec(&self) -> u64 {
        self.0 + 6
    }
}

impl DiamondAsym for Node {
    #[inline(never)]
    fn dia2(&self) -> u64 {
        self.0 + 7
    }
}

impl GenRoot<u8> for Node {
    #[inline(never)]
    fn tag(&self) -> u64 {
        8
    }
}

impl GenRoot<u16> for Node {
    #[inline(never)]
    fn tag(&self) -> u64 {
        16
    }
}

impl AmbigDia for Node {
    #[inline(never)]
    fn ambig(&self) -> u64 {
        self.0 + 9
    }
}

#[inline(never)]
fn dia_to_left(d: &dyn Diamond) -> &dyn Left {
    d
}

#[inline(never)]
fn dia_to_right(d: &dyn Diamond) -> &dyn Right {
    d
}

#[inline(never)]
fn dia_to_root(d: &dyn Diamond) -> &dyn Root {
    d
}

#[inline(never)]
fn left_to_root(l: &dyn Left) -> &dyn Root {
    l
}

#[inline(never)]
fn right_to_root(r: &dyn Right) -> &dyn Root {
    r
}

#[inline(never)]
fn asym_to_right_second(d: &dyn DiamondAsym) -> &dyn RightSecond {
    d
}

#[inline(never)]
fn asym_to_root(d: &dyn DiamondAsym) -> &dyn Root {
    d
}

#[inline(never)]
fn right_second_to_root(r: &dyn RightSecond) -> &dyn Root {
    r
}

#[inline(never)]
fn ambig_to_u8(d: &dyn AmbigDia) -> &dyn GenRoot<u8> {
    d
}

#[inline(never)]
fn ambig_to_u16(d: &dyn AmbigDia) -> &dyn GenRoot<u16> {
    d
}

#[inline(never)]
unsafe fn vptr_addr<T: ?Sized>(r: &T) -> usize {
    assert_eq!(std::mem::size_of::<&T>(), std::mem::size_of::<(usize, usize)>());
    unsafe { std::mem::transmute_copy::<&T, (usize, usize)>(&r).1 }
}

fn main() {
    let n = std::hint::black_box(Node(100));
    let d: &dyn Diamond = std::hint::black_box(&n);
    let l = dia_to_left(d);
    let r = dia_to_right(d);
    let root_from_d = dia_to_root(d);
    let root_from_l = left_to_root(l);
    let root_from_r = right_to_root(r);
    let r_direct: &dyn Right = std::hint::black_box(&n);
    let root_direct: &dyn Root = std::hint::black_box(&n);

    let vd = unsafe { vptr_addr(d) };
    let vl = unsafe { vptr_addr(l) };
    let vr = unsafe { vptr_addr(r) };
    let vr_dir = unsafe { vptr_addr(r_direct) };
    let vroot_d = unsafe { vptr_addr(root_from_d) };
    let vroot_l = unsafe { vptr_addr(root_from_l) };
    let vroot_r = unsafe { vptr_addr(root_from_r) };
    let vroot_dir = unsafe { vptr_addr(root_direct) };

    println!(
        "D_EQ_L={} L_EQ_ROOT={} D_EQ_ROOT_FROM_D={} R_EQ_RDIR={} ROOT_FROM_R_EQ_DIR={}",
        vd == vl,
        vl == vroot_l,
        vd == vroot_d,
        vr == vr_dir,
        vroot_r == vroot_dir
    );
    println!(
        "D_EQ_R={} ROOT_FROM_D_EQ_ROOT_FROM_R={}",
        vd == vr,
        vroot_d == vroot_r
    );

    let d2: &dyn DiamondAsym = std::hint::black_box(&n);
    let r2 = asym_to_right_second(d2);
    let root_asym_direct = asym_to_root(d2);
    let root_asym_via_r2 = right_second_to_root(r2);
    let vd2 = unsafe { vptr_addr(d2) };
    let vr2 = unsafe { vptr_addr(r2) };
    let vr2_root = unsafe { vptr_addr(root_asym_via_r2) };
    println!(
        "ASYM_D_EQ_ROOT={} ASYM_D_EQ_R2={} ASYM_R2_EQ_ROOT={} ASYM_ROOT_CALLS={},{}",
        vd2 == unsafe { vptr_addr(root_asym_direct) },
        vd2 == vr2,
        vr2 == vr2_root,
        root_asym_direct.root(),
        root_asym_via_r2.root()
    );

    let amb: &dyn AmbigDia = std::hint::black_box(&n);
    let g8 = ambig_to_u8(amb);
    let g16 = ambig_to_u16(amb);

    println!(
        "CALLS={},{},{},{},{},{} GEN_TAGS={},{}",
        d.dia(),
        l.left(),
        r.right(),
        root_from_d.root(),
        root_from_l.root(),
        root_from_r.root(),
        g8.tag(),
        g16.tag()
    );
}
