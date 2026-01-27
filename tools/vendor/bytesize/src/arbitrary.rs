use arbitrary::{Arbitrary, Unstructured};

use crate::ByteSize;

impl Arbitrary<'_> for ByteSize {
    fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        Ok(ByteSize(u64::arbitrary(u)?))
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        u64::size_hint(depth)
    }
}
