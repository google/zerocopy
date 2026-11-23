#![allow(dead_code)]

trait GenRoot<T> {
    fn tag(&self) -> u64;
}

trait LeftU8: GenRoot<u8> {}
trait RightU8: GenRoot<u8> {}
trait SameGenDia: LeftU8 + RightU8 {}

fn upcast(d: &dyn SameGenDia) -> u64 {
    let x: &dyn GenRoot<_> = d;
    x.tag()
}

fn main() {}
