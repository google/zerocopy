// A Result alias should not affect the enum_dispatch macro
#[allow(dead_code)]
#[allow(unused_imports)]
use std::io::Result;

use enum_dispatch::enum_dispatch;

struct Foo;
struct Bar;
impl TaggedTrait for Foo {}
impl TaggedTrait for Bar {}

#[enum_dispatch(TaggedTrait)]
enum TaggedEnum {
    Foo,
    Bar,
}

#[enum_dispatch]
trait TaggedTrait {
    fn baz(&self) -> u8 {
        0
    }
}

#[test]
fn main() {
    let foo = TaggedEnum::from(Foo);
    let bar = TaggedEnum::from(Bar);
    assert_eq!(foo.baz(), 0);
    assert_eq!(bar.baz(), 0);
}
