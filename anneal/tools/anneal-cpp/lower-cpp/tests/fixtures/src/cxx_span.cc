// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

using uint8_t = unsigned char;
using size_t = unsigned long;

template <typename T>
class Span {
 public:
  constexpr Span(T* p, size_t n) : ptr_(p), len_(n) {}
  constexpr size_t size() const { return len_; }
  constexpr T* data() const { return ptr_; }
  constexpr T& operator[](size_t i) const { return ptr_[i]; }

 private:
  T* ptr_;
  size_t len_;
};

uint8_t span_sum(const uint8_t* p, size_t n) {
  Span<const uint8_t> s(p, n);
  uint8_t acc = 0;
  for (size_t i = 0; i < s.size(); ++i) acc = acc + s[i];
  return acc;
}

const uint8_t* span_data(const uint8_t* p, size_t n) {
  Span<const uint8_t> s(p, n);
  return s.data();
}
