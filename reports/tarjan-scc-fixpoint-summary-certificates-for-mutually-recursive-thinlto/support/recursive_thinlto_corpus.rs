// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! 30-Function Recursive and Mutually Recursive ThinLTO Benchmark Corpus.
//! Compiled with `rustc +1.99.1-x86_64-unknown-linux-gnu -C opt-level=3 --emit=llvm-ir`.

#![crate_name = "recursive_thinlto_corpus"]
#![crate_type = "rlib"]

// ============================================================================
// SCC 1 (|S| = 3): Mutually Recursive JSON Token Parser
// Ranking measure: (slice.len(), node_rank) where slice strictly shrinks on each step.
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn parse_json_value(buf: &[u8]) -> (u64, usize) {
    if buf.is_empty() {
        return (0, 0);
    }
    match buf[0] {
        b'[' => parse_json_array(&buf[1..]),
        b'{' => parse_json_object(&buf[1..]),
        b => ((b as u64).wrapping_add(1), 1),
    }
}

#[no_mangle]
#[inline(never)]
pub fn parse_json_array(buf: &[u8]) -> (u64, usize) {
    if buf.is_empty() {
        return (1, 0);
    }
    if buf[0] == b']' {
        return (2, 1);
    }
    let (v, consumed) = parse_json_value(&buf[1..]);
    let step = if consumed == 0 { 1 } else { consumed };
    if step >= buf.len() {
        (v.wrapping_add(3), buf.len())
    } else {
        let (rest_v, rest_c) = parse_json_array(&buf[step..]);
        (v.wrapping_add(rest_v), step.wrapping_add(rest_c))
    }
}

#[no_mangle]
#[inline(never)]
pub fn parse_json_object(buf: &[u8]) -> (u64, usize) {
    if buf.is_empty() {
        return (4, 0);
    }
    if buf[0] == b'}' {
        return (5, 1);
    }
    let (v, consumed) = parse_json_value(&buf[1..]);
    let step = if consumed == 0 { 1 } else { consumed };
    if step >= buf.len() {
        (v.wrapping_add(7), buf.len())
    } else {
        let (rest_v, rest_c) = parse_json_object(&buf[step..]);
        (v.wrapping_sub(rest_v), step.wrapping_add(rest_c))
    }
}

// ============================================================================
// SCC 2 (|S| = 3): Mutually Recursive Expression Evaluator with Zero-Decrease Hops
// Notice: eval_expr(depth, x) -> eval_term(depth, x) -> eval_factor(depth, x)
// keeps `depth` constant on forward dispatch (broken by node_rank: 2 > 1 > 0),
// while the backedge eval_factor(depth, x) -> eval_expr(depth - 1, x) strictly
// decreases `depth`!
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn eval_expr(depth: u32, x: u64) -> u64 {
    if depth == 0 {
        return x.wrapping_add(1);
    }
    let t = eval_term(depth, x.wrapping_mul(3));
    t.wrapping_add(eval_term(depth - 1, x.wrapping_add(5)))
}

#[no_mangle]
#[inline(never)]
pub fn eval_term(depth: u32, x: u64) -> u64 {
    if depth == 0 {
        return x.wrapping_mul(2);
    }
    let f = eval_factor(depth, x.wrapping_add(7));
    f.wrapping_sub(depth as u64)
}

#[no_mangle]
#[inline(never)]
pub fn eval_factor(depth: u32, x: u64) -> u64 {
    if depth <= 1 {
        return x.wrapping_add(11);
    }
    eval_expr(depth - 1, x.rotate_left(3))
}

// ============================================================================
// SCC 3 (|S| = 4): Mutually Recursive Frame State-Machine Dispatcher
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn fsm_state_header(rem: u32, acc: u64) -> u64 {
    if rem == 0 {
        return acc;
    }
    fsm_state_length(rem, acc.wrapping_add(0x10))
}

#[no_mangle]
#[inline(never)]
pub fn fsm_state_length(rem: u32, acc: u64) -> u64 {
    if rem == 0 {
        return acc;
    }
    fsm_state_payload(rem, acc.wrapping_mul(5))
}

#[no_mangle]
#[inline(never)]
pub fn fsm_state_payload(rem: u32, acc: u64) -> u64 {
    if rem == 0 {
        return acc;
    }
    fsm_state_trailer(rem, acc.wrapping_sub(0x55))
}

#[no_mangle]
#[inline(never)]
pub fn fsm_state_trailer(rem: u32, acc: u64) -> u64 {
    if rem <= 1 {
        return acc.wrapping_add(1);
    }
    fsm_state_header(rem - 1, acc.wrapping_add(rem as u64))
}

// ============================================================================
// SCC 4 (|S| = 2): Mutually Recursive DOM Element / Children Sanitizer
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn dom_visit_element(nodes: &[u64]) -> u64 {
    if nodes.is_empty() {
        return 0;
    }
    nodes[0].wrapping_add(dom_visit_children(&nodes[1..]))
}

#[no_mangle]
#[inline(never)]
pub fn dom_visit_children(nodes: &[u64]) -> u64 {
    if nodes.is_empty() {
        return 0;
    }
    let first = dom_visit_element(&nodes[..nodes.len() / 2]);
    let second = dom_visit_element(&nodes[nodes.len() / 2 + 1..]);
    first.wrapping_add(second)
}

// ============================================================================
// SCC 5 (|S| = 2): Mutually Recursive Regex Alternation / Sequence Matcher
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn regex_match_seq(pat_fuel: u32, text: &[u8]) -> bool {
    if pat_fuel == 0 || text.is_empty() {
        return true;
    }
    regex_match_alt(pat_fuel, &text[1..])
}

#[no_mangle]
#[inline(never)]
pub fn regex_match_alt(pat_fuel: u32, text: &[u8]) -> bool {
    if pat_fuel == 0 {
        return text.is_empty();
    }
    regex_match_seq(pat_fuel - 1, text)
}

// ============================================================================
// SCC 6 (|S| = 2): Mutually Recursive Type Unification Check
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn unify_type_term(fuel: u32, a: u64, b: u64) -> bool {
    if a == b {
        return true;
    }
    if fuel == 0 {
        return false;
    }
    unify_type_args(fuel, a >> 1, b >> 1)
}

#[no_mangle]
#[inline(never)]
pub fn unify_type_args(fuel: u32, a: u64, b: u64) -> bool {
    if fuel == 0 {
        return a == b;
    }
    unify_type_term(fuel - 1, a ^ 1, b ^ 1)
}

// ============================================================================
// SCCs 7..16 (|S| = 1 with self-loop): 10 Bounded Self-Recursive Functions
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn gcd_bounded_steps(fuel: u32, a: u64, b: u64) -> u64 {
    if fuel == 0 || b == 0 {
        a
    } else {
        gcd_bounded_steps(fuel - 1, b, a % b)
    }
}

#[no_mangle]
#[inline(never)]
pub fn binary_search_rec(slice: &[u64], target: u64) -> bool {
    if slice.is_empty() {
        return false;
    }
    let mid = slice.len() / 2;
    if slice[mid] == target {
        true
    } else if target < slice[mid] {
        binary_search_rec(&slice[..mid], target)
    } else {
        binary_search_rec(&slice[mid + 1..], target)
    }
}

#[no_mangle]
#[inline(never)]
pub fn trie_prefix_lookup(nodes: &[u8], key: &[u8]) -> u64 {
    if key.is_empty() || nodes.is_empty() {
        return nodes.first().copied().unwrap_or(0) as u64;
    }
    let step = ((nodes[0] ^ key[0]) as usize % 3) + 1;
    if step >= nodes.len() {
        nodes[0] as u64
    } else {
        trie_prefix_lookup(&nodes[step..], &key[1..])
    }
}

#[no_mangle]
#[inline(never)]
pub fn bst_checksum_rec(tree: &[u64]) -> u64 {
    if tree.is_empty() {
        return 0;
    }
    let mid = tree.len() / 2;
    let left = bst_checksum_rec(&tree[..mid]);
    let right = bst_checksum_rec(&tree[mid + 1..]);
    tree[mid].wrapping_add(left.rotate_left(5)).wrapping_add(right.rotate_right(3))
}

#[no_mangle]
#[inline(never)]
pub fn varint_decode_rec(buf: &[u8], shift: u32, acc: u64) -> u64 {
    if buf.is_empty() || shift >= 63 {
        return acc;
    }
    let byte = buf[0];
    let next_acc = acc | (((byte & 0x7f) as u64) << shift);
    if (byte & 0x80) == 0 {
        next_acc
    } else {
        varint_decode_rec(&buf[1..], shift + 7, next_acc)
    }
}

#[no_mangle]
#[inline(never)]
pub fn fast_pow_mod_rec(base: u64, exp: u64, m: u64) -> u64 {
    if m <= 1 {
        return 0;
    }
    if exp == 0 {
        return 1;
    }
    let half = fast_pow_mod_rec(base, exp >> 1, m);
    let sq = ((half as u128 * half as u128) % m as u128) as u64;
    if (exp & 1) == 0 {
        sq
    } else {
        ((sq as u128 * (base % m) as u128) % m as u128) as u64
    }
}

#[no_mangle]
#[inline(never)]
pub fn utf8_validate_ascii_chunks_rec(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return true;
    }
    if bytes[0] >= 0x80 {
        return false;
    }
    utf8_validate_ascii_chunks_rec(&bytes[1..])
}

#[no_mangle]
#[inline(never)]
pub fn leb128_byte_len_rec(val: u64) -> u32 {
    if val < 0x80 {
        1
    } else {
        1 + leb128_byte_len_rec(val >> 7)
    }
}

#[no_mangle]
#[inline(never)]
pub fn adler32_window_rec(data: &[u8], a: u32, b: u32) -> u32 {
    if data.is_empty() {
        return (b << 16) | a;
    }
    let a_next = (a + data[0] as u32) % 65521;
    let b_next = (b + a_next) % 65521;
    adler32_window_rec(&data[1..], a_next, b_next)
}

#[no_mangle]
#[inline(never)]
pub fn argmem_mutating_fill_rec(dst: &mut [u64], seed: u64) {
    if dst.is_empty() {
        return;
    }
    dst[0] = seed;
    argmem_mutating_fill_rec(&mut dst[1..], seed.wrapping_add(1));
}

// ============================================================================
// Negative Canaries (4 functions: unbounded cycles and unwinding recursion)
// ============================================================================

#[no_mangle]
#[inline(never)]
pub fn canary_unbounded_collatz_rec(n: u64) -> u64 {
    if n <= 1 {
        1
    } else if (n & 1) == 0 {
        canary_unbounded_collatz_rec(n / 2)
    } else {
        canary_unbounded_collatz_rec(n.wrapping_mul(3).wrapping_add(1))
    }
}

#[no_mangle]
#[inline(never)]
pub fn canary_zero_decrease_cycle_a(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        canary_zero_decrease_cycle_b(n)
    }
}

#[no_mangle]
#[inline(never)]
pub fn canary_zero_decrease_cycle_b(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        canary_zero_decrease_cycle_a(n)
    }
}

#[no_mangle]
#[inline(never)]
pub fn canary_panicking_recursive_walk(depth: u32, x: u64) -> u64 {
    if x == 0xDEAD_BEEF {
        panic!("explicit panic inside recursive walk");
    }
    if depth == 0 {
        x
    } else {
        canary_panicking_recursive_walk(depth - 1, x.wrapping_add(1))
    }
}
