use zerocopy::pointer::{
    invariant::{Aligned, Exclusive, Shared, Valid},
    Ptr,
};

fn _when_exclusive<'big: 'small, 'small>(
    big: Ptr<'small, Valid<&'big u32>, (Exclusive, Aligned)>,
    mut _small: Ptr<'small, Valid<&'small u32>, (Exclusive, Aligned)>,
) {
    _small = big;
}

fn _when_shared<'big: 'small, 'small>(
    big: Ptr<'small, Valid<&'big u32>, (Shared, Aligned)>,
    mut _small: Ptr<'small, Valid<&'small u32>, (Shared, Aligned)>,
) {
    _small = big;
}

fn main() {}
