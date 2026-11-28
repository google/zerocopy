// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

template <typename T>
concept Small = sizeof(T) <= 8;

template <typename T>
  requires Small<T>
struct SliceRef {
  const T* ptr;
  unsigned long len;
};

template <typename T>
  requires Small<T>
unsigned long slice_len(SliceRef<T> s) { return s.len; }

template unsigned long slice_len<int>(SliceRef<int>);
