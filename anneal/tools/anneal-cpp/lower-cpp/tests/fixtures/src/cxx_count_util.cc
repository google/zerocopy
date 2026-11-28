// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

using uint64_t = unsigned long;

template <typename T>
constexpr T HowMany(T x, T m) { return (x + m - 1) / m; }

template <typename T>
constexpr T RoundUp(T x, T m) { return HowMany(x, m) * m; }

template <typename T>
constexpr T Bitmask(unsigned bits) {
  return bits >= sizeof(T) * 8 ? ~T(0) : (T(1) << bits) - 1;
}

template uint64_t HowMany<uint64_t>(uint64_t, uint64_t);
template uint64_t RoundUp<uint64_t>(uint64_t, uint64_t);
template uint64_t Bitmask<uint64_t>(unsigned);
