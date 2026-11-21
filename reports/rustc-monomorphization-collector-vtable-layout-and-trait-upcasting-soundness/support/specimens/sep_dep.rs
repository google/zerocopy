//! Specimen 4a: Upstream rlib crate for separate-compilation generic sharing
//! (`-Z share-generics=yes|no` and `#[inline(never)]` unconditional reuse)
//! and cross-crate private vtable duplication.

pub trait Metric {
    fn score(&self) -> u64;
}

pub struct Gauge(pub u64);

impl Metric for Gauge {
    #[inline(never)]
    fn score(&self) -> u64 {
        self.0 * 2
    }
}

/// Unannotated generic: shared upstream only when `-Z share-generics=yes`.
pub fn poly_default<T: Copy>(x: T, _y: T) -> T {
    std::hint::black_box(x)
}

/// `#[inline(never)]` generic: upstream monomorphization reused even under `-Z share-generics=no`.
#[inline(never)]
pub fn poly_inline_never<T: Copy>(x: T, _y: T) -> T {
    std::hint::black_box(x)
}

#[inline(never)]
pub fn instantiate_in_dep() -> u64 {
    let g = Gauge(5);
    let d: &dyn Metric = &g;
    poly_default::<u64>(d.score(), 1) + poly_inline_never::<u64>(d.score(), 2)
}

#[inline(never)]
pub fn make_dep_vtable(g: &Gauge) -> &dyn Metric {
    g
}
