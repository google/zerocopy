\
#![allow(dead_code)]

macro_rules! local_generated {
    () => {
        fn generated_local() -> u32 { 10 }
    };
}

fn outer_a<T>() {
    fn inner<U>() -> u32 { 1 }
    struct Local(u32);
    impl Local { fn method(&self) -> u32 { self.0 } }

    let c1 = || inner::<u8>();
    let c2 = move || 2u32;
    let _: [u8; { 1 + 1 }] = [0; 2];
    let x = const { 3usize };

    local_generated!();
    let _ = (c1(), c2(), x, generated_local(), Local(4).method());
}

fn outer_b() {
    fn inner() -> u32 { 5 }
    let _ = inner();
}

fn main() { outer_a::<u16>(); outer_b(); }
