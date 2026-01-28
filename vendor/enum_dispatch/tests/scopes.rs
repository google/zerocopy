mod scope1 {
    use crate::scope2::{Itemized, Subitem2};
    use enum_dispatch::enum_dispatch;

    pub struct Subitem1;
    impl Itemized for Subitem1 {
        fn do_it(&self) -> u8 {
            1
        }
    }

    #[enum_dispatch]
    pub enum Item {
        Subitem1,
        Subitem2,
    }
}

mod scope2 {
    use crate::scope1::{Item, Subitem1};
    use enum_dispatch::enum_dispatch;

    pub struct Subitem2;
    impl Itemized for Subitem2 {
        fn do_it(&self) -> u8 {
            2
        }
    }

    #[enum_dispatch(Item)]
    pub trait Itemized {
        fn do_it(&self) -> u8;
    }
}

use crate::scope2::Itemized;

#[test]
fn main() {
    let s1: scope1::Item = scope1::Subitem1.into();
    let s2 = scope1::Item::from(scope2::Subitem2);
    assert_eq!(s1.do_it(), 1);
    assert_eq!(s2.do_it(), 2);
}
