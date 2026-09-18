#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reviewed source adjustments after the content-checked initial patch."""
from pathlib import Path
import os

assert os.environ['GITHUB_REPOSITORY'] == 'google/zerocopy'
assert os.environ['GITHUB_REF'] == 'refs/heads/fix-transmute-reverse-before'
p = Path('zerocopy/src/pointer/transmute/reverse_tests.rs')
s = p.read_text()
old = '''    static_assertions::assert_impl_all!(u16:
        TransmuteFrom<u8, Initialized, Safe, cast::CastSized, Reverse<Initialized>>);
    static_assertions::assert_not_impl_any!(u16:
        TransmuteFrom<u8, Initialized, Safe, cast::CastSized, Reverse<Uninit>>);
    static_assertions::assert_not_impl_any!(core::num::NonZeroU16:
        TransmuteFrom<u8, Safe, Safe, cast::CastSized, Reverse<Safe>>);
'''
new = '''    // These helper traits keep `CastSized`'s Sized premise explicit. The
    // assertion macros introduce `T: ?Sized`, which cannot directly name a
    // relation whose reverse projection is implemented only for sized T.
    trait InitializedFrame {}
    impl<T> InitializedFrame for T where
        T: TransmuteFrom<u8, Initialized, Safe, cast::CastSized, Reverse<Initialized>>
    {}
    trait ArbitraryFrame {}
    impl<T> ArbitraryFrame for T where
        T: TransmuteFrom<u8, Initialized, Safe, cast::CastSized, Reverse<Uninit>>
    {}
    trait SafeByteReplacement {}
    impl<T> SafeByteReplacement for T where
        T: TransmuteFrom<u8, Safe, Safe, cast::CastSized, Reverse<Safe>>
    {}
    static_assertions::assert_impl_all!(u16: InitializedFrame);
    static_assertions::assert_not_impl_any!(u16: ArbitraryFrame);
    static_assertions::assert_not_impl_any!(core::num::NonZeroU16: SafeByteReplacement);
'''
assert s.count(old) == 1
p.write_text(s.replace(old, new))
p = Path('zerocopy/src/pointer/transmute.rs')
s = p.read_text().replace('    use crate::pointer::cast::Project as _;\n', '')
s = s.replace('let mut ptr = unsafe { ptr.assume_alignment::<Aligned>() };',
              'let ptr = unsafe { ptr.assume_alignment::<Aligned>() };')
old = '''// SAFETY: `MaybeUninit<T>` has no validity requirements. Currently this is not
// explicitly guaranteed, but it's obvious from `MaybeUninit`'s documentation
// that this is the intention:
// https://doc.rust-lang.org/1.85.0/core/mem/union.MaybeUninit.html
'''
new = '''// SAFETY: `MaybeUninit<T>` admits any bit value [1] and allows payloads
// which are uninitialized or invalid for T [2]. The projected bytes therefore
// satisfy `Safe` for MaybeUninit<T> without requiring T validity. `Project`
// only selects a region; it does not read a T or transfer ownership.
//
// [1] https://doc.rust-lang.org/1.56.0/std/mem/union.MaybeUninit.html#layout
//     "any bit value is valid for a `MaybeUninit<T>`"
// [2] https://doc.rust-lang.org/1.56.0/std/mem/union.MaybeUninit.html#examples
//     "the data here might *not* be initialized"
'''
assert s.count(old) == 1
s = s.replace(old, new)
anchor = '\nimpl<T> SizeEq<T> for MaybeUninit<T> {'
addition = '''
// SAFETY: MaybeUninit<T> permits uninitialized and invalid T payloads [1].
// Every replacement admitted by Uninit is therefore admissible after it is
// spliced into the selected region, independently of B and the retained bytes.
// No T value is read, dropped, or exposed by this representation theorem.
//
// [1] https://doc.rust-lang.org/1.56.0/std/mem/union.MaybeUninit.html#examples
unsafe impl<T, B: Validity, C> TransmuteFrom<T, Uninit, Safe, C, Reverse<B>>
    for MaybeUninit<T>
where
    C: Project<MaybeUninit<T>, T>,
{
}

// SAFETY: AsInitialized restricts the Uninit representation candidates.
// MaybeUninit<T> admits all of them, including uninitialized bytes [1], so
// any such replacement leaves an admissible MaybeUninit<T> representation.
//
// [1] https://doc.rust-lang.org/1.56.0/std/mem/union.MaybeUninit.html#examples
unsafe impl<T, B: Validity, C> TransmuteFrom<T, AsInitialized, Safe, C, Reverse<B>>
    for MaybeUninit<T>
where
    C: Project<MaybeUninit<T>, T>,
{
}
'''
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, addition + anchor))
p = Path('zerocopy/src/pointer/ptr.rs')
s = p.read_text()
anchor = '    use crate::pointer::cast::{CastSized, IdCast};'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, '    #[cfg(doc)]\n    use crate::pointer::cast::CastExact;\n' + anchor))
