#![allow(dead_code)]

trait GenRoot<T> {
    fn tag(&self) -> u64;
}

trait AmbigDia: GenRoot<u8> + GenRoot<u16> {}

fn upcast(d: &dyn AmbigDia) {
    let _x: &dyn GenRoot<_> = d;
}

fn main() {}
