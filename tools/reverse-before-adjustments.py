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
p.write_text(s)
