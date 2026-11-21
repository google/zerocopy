//! Specimen 4b: Downstream binary crate importing `sep_dep`.

extern crate sep_dep;

fn vtable_addr<T: ?Sized>(p: &T) -> usize {
    let raw: [usize; 2] = unsafe { std::mem::transmute_copy(&p) };
    raw[1]
}

fn main() {
    let g = sep_dep::Gauge(9);
    let d_dep = sep_dep::make_dep_vtable(&g);
    let d_app: &dyn sep_dep::Metric = &g;
    let same_vtable = vtable_addr(d_dep) == vtable_addr(d_app);
    let a = sep_dep::poly_default::<u64>(10, 20);
    let b = sep_dep::poly_inline_never::<u64>(30, 40);
    let c = sep_dep::poly_default::<i32>(3, 4);
    let dep_sum = sep_dep::instantiate_in_dep();
    println!("same_vtable={same_vtable}");
    println!("a={a}");
    println!("b={b}");
    println!("c={c}");
    println!("dep_sum={dep_sum}");
}
