use enum_dispatch::enum_dispatch;

struct Foo;
struct Bar;
impl TaggedTrait for Foo {}
impl TaggedTrait for Bar {}

#[enum_dispatch(TaggedTrait)]
enum TaggedEnumBeforeTrait {
    Foo,
    Bar,
}

#[enum_dispatch]
enum UntaggedEnumBeforeTrait {
    Foo,
    Bar,
}

// It's unnecessary to add an #[enum_dispatch] attribute here, since the trait will be registered by
// the tagged versions.
#[enum_dispatch(UntaggedEnumBeforeTrait)]
#[enum_dispatch(UntaggedEnumAfterTrait)]
trait TaggedTrait {
    fn baz(&self) -> u8 {
        0
    }
}

#[enum_dispatch(TaggedTrait)]
enum TaggedEnumAfterTrait {
    Foo,
    Bar,
}

#[enum_dispatch]
enum UntaggedEnumAfterTrait {
    Foo,
    Bar,
}

#[test]
fn main() {
    let foo_a = UntaggedEnumAfterTrait::from(Foo);
    let bar_a = TaggedEnumAfterTrait::from(Bar);
    let foo_b = UntaggedEnumBeforeTrait::from(Foo);
    let bar_b = TaggedEnumBeforeTrait::from(Bar);
    assert_eq!(foo_a.baz(), 0);
    assert_eq!(bar_a.baz(), 0);
    assert_eq!(foo_b.baz(), 0);
    assert_eq!(bar_b.baz(), 0);
}
