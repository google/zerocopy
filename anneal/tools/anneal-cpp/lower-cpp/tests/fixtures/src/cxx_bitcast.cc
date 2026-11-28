// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

using uint16_t = unsigned short;
using uint32_t = unsigned int;
using uint64_t = unsigned long;

template <typename To, typename From>
constexpr To bit_cast(const From& from) { return __builtin_bit_cast(To, from); }

struct Pod {
  uint32_t lo;
  uint32_t hi;
};

uint64_t pod_to_u64(Pod p) { return bit_cast<uint64_t>(p); }

struct PacketDesc {
  uint16_t buf_id : 11;
  uint16_t rsvd : 5;
  uint16_t len : 14;
  uint16_t gen : 1;
  uint16_t eop : 1;
  uint32_t hash;
};

uint64_t pack_desc(uint16_t id, uint16_t len, uint16_t gen) {
  PacketDesc d{};
  d.buf_id = id;
  d.len = len;
  d.gen = gen;
  return __builtin_bit_cast(uint64_t, d);
}

uint16_t desc_len(uint64_t raw) {
  PacketDesc d = __builtin_bit_cast(PacketDesc, raw);
  return d.len;
}
