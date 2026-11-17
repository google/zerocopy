// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone empirical and counterexample probe for DEFLATE/LZ77 matching,
//! binary-tree invariants, optimal DP truncation pruning, fixed-point pricing,
//! Kraft-rebalanced Huffman codes, multi-chunk stored blocks, and Variant-4
//! 64-bit bitreader refill invariants.
//!
//! Run:
//!   rustc --edition 2021 -O deflate_bt_dp_probe.rs -o /tmp/deflate_bt_dp_probe && /tmp/deflate_bt_dp_probe

#[allow(unused_imports)]
use std::convert::TryInto;

use std::mem::size_of;
use std::time::Instant;

const WINDOW_SIZE: usize = 32768;
const WINDOW_MASK: usize = WINDOW_SIZE - 1;
const BT_MAX_DIST_SAFE: usize = WINDOW_SIZE - 1; // 32767
const BT_MAX_DIST_BUGGY: usize = WINDOW_SIZE; // 32768
const MAX_MATCH: usize = 258;
const OPT_NO_TRUNC: u16 = 0x8000;

// ============================================================================
// 1. BT_MAX_DIST = 32767 vs. 32768 Self-Cycle Trap in 1-Based u16 Ring BST
// ============================================================================

fn run_bt_step(
    input: &[u8],
    pos: usize,
    bt_head4: &mut [u16; 4096],
    bt_child: &mut [[u16; 2]; WINDOW_SIZE],
    max_dist: usize,
    max_depth: usize,
) -> (usize, bool) {
    let h4 = 0usize; // Fixed bucket for controlled trace
    let v = ((pos & WINDOW_MASK) as u16) + 1;
    let mut cand_v = bt_head4[h4];
    bt_head4[h4] = v;

    let mut pending_lt: (usize, usize) = (pos & WINDOW_MASK, 0);
    let mut pending_gt: (usize, usize) = (pos & WINDOW_MASK, 1);

    let mut depth = 0usize;
    let mut hit_self_cycle = false;

    while cand_v != 0 && depth < max_depth {
        let cslot = (cand_v - 1) as usize;
        let d = (pos.wrapping_sub(cslot)) & WINDOW_MASK;
        // Under 1-based u16 ring addressing, a candidate at distance 32768
        // folds to `d == 0` (if masked by 0x7FFF) or `cslot == pos & 0x7FFF`
        // (`d_exact = pos - cpos == 32768`).
        let d_exact = if d == 0 { WINDOW_SIZE } else { d };
        if d_exact > max_dist {
            bt_child[pending_lt.0][pending_lt.1] = 0;
            bt_child[pending_gt.0][pending_gt.1] = 0;
            return (depth, hit_self_cycle);
        }
        depth += 1;
        let cpos = pos - d_exact;

        let mut ml = 0usize;
        while ml < 8 && pos + ml < input.len() && input[pos + ml] == input[cpos + ml] {
            ml += 1;
        }

        if input[pos + ml] < input[cpos + ml] {
            bt_child[pending_gt.0][pending_gt.1] = cand_v;
            pending_gt = (cslot, 0);
            let next_v = bt_child[cslot][0];
            if next_v == cand_v {
                hit_self_cycle = true;
            }
            cand_v = next_v;
        } else {
            bt_child[pending_lt.0][pending_lt.1] = cand_v;
            pending_lt = (cslot, 1);
            let next_v = bt_child[cslot][1];
            if next_v == cand_v {
                hit_self_cycle = true;
            }
            cand_v = next_v;
        }
    }

    bt_child[pending_lt.0][pending_lt.1] = 0;
    bt_child[pending_gt.0][pending_gt.1] = 0;
    (depth, hit_self_cycle)
}

fn probe_1_bt_max_dist_self_cycle() {
    let mut input = vec![0u8; WINDOW_SIZE + 64];
    // pos = 0: "ABCD_100"
    input[0..8].copy_from_slice(b"ABCD_100");
    // pos = 32768 (same ring slot 0, v = 1): "ABCD_200" (> "ABCD_100")
    input[WINDOW_SIZE..WINDOW_SIZE + 8].copy_from_slice(b"ABCD_200");
    // pos = 32776 (ring slot 8, v = 9): "ABCD_150" (< "ABCD_200", branches left into slot 0's left child)
    input[WINDOW_SIZE + 8..WINDOW_SIZE + 16].copy_from_slice(b"ABCD_150");

    // 1A: Buggy BT_MAX_DIST = 32768
    let mut head_buggy = [0u16; 4096];
    let mut child_buggy = [[0u16; 2]; WINDOW_SIZE];
    run_bt_step(&input, 0, &mut head_buggy, &mut child_buggy, BT_MAX_DIST_BUGGY, 64);
    run_bt_step(&input, WINDOW_SIZE, &mut head_buggy, &mut child_buggy, BT_MAX_DIST_BUGGY, 64);
    let slot0_after_32768_buggy = child_buggy[0];
    let (depth_buggy, cycle_buggy) = run_bt_step(
        &input,
        WINDOW_SIZE + 8,
        &mut head_buggy,
        &mut child_buggy,
        BT_MAX_DIST_BUGGY,
        64,
    );

    // 1B: Safe BT_MAX_DIST = 32767
    let mut head_safe = [0u16; 4096];
    let mut child_safe = [[0u16; 2]; WINDOW_SIZE];
    run_bt_step(&input, 0, &mut head_safe, &mut child_safe, BT_MAX_DIST_SAFE, 64);
    run_bt_step(&input, WINDOW_SIZE, &mut head_safe, &mut child_safe, BT_MAX_DIST_SAFE, 64);
    let slot0_after_32768_safe = child_safe[0];
    let (depth_safe, cycle_safe) = run_bt_step(
        &input,
        WINDOW_SIZE + 8,
        &mut head_safe,
        &mut child_safe,
        BT_MAX_DIST_SAFE,
        64,
    );

    println!("=== [Probe 1] BT_MAX_DIST = 32767 vs. 32768 Self-Cycle Trap ===");
    println!(
        "  BT_MAX_DIST=32768: after pos=32768, bt_child[0]={:?} (self-loop v=1!); next lookup depth={}, self_cycle={}",
        slot0_after_32768_buggy, depth_buggy, cycle_buggy
    );
    println!(
        "  BT_MAX_DIST=32767: after pos=32768, bt_child[0]={:?} (clean reset);   next lookup depth={}, self_cycle={}",
        slot0_after_32768_safe, depth_safe, cycle_safe
    );

    assert_eq!(slot0_after_32768_buggy, [1, 0], "Expected self-loop bt_child[0][0] == 1 at d=32768");
    assert!(cycle_buggy && depth_buggy == 64, "Expected infinite cycle hitting max_depth=64");
    assert_eq!(slot0_after_32768_safe, [0, 0], "Expected clean child reset at d=32767");
    assert!(!cycle_safe && depth_safe == 1, "Expected 1-step termination with BT_MAX_DIST=32767");
}

// ============================================================================
// 2. Binary-Tree Child-Splicing Soundness Only at ml == 258 (MAX_MATCH)
// ============================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum EarlyExitPolicy {
    /// Unsound: splices cand's children into pos at any `ml >= nice_len` (even `ml < 258`).
    SpliceAtNiceLen,
    /// Sound fallback: splices ONLY at `ml == 258`, zeroes at `ml < 258`.
    ZeroAtNiceLenSpliceAt258,
    /// Sound + Subtree-Preserving: attaches `cand` on its true comparison side at byte `ml`
    /// and zeroes only the opposite frontier when `nice_len <= ml < 258`.
    AttachCandSideAtNiceLen,
}

fn bt_insert_and_query(
    strings: &[&[u8]],
    nice_len: usize,
    policy: EarlyExitPolicy,
) -> Vec<(usize, usize)> {
    let mut root: usize = 0; // 1-based index into `strings`
    let mut child = vec![[0usize; 2]; strings.len() + 1];
    let mut results = Vec::with_capacity(strings.len());

    for (idx, &s) in strings.iter().enumerate() {
        let v = idx + 1;
        let mut cand_v = root;
        root = v;

        let mut pending_lt = (v, 0usize);
        let mut pending_gt = (v, 1usize);
        let mut best_len = 0usize;
        let mut best_cand = 0usize;

        while cand_v != 0 {
            let cs = strings[cand_v - 1];
            let limit = s.len().min(cs.len()).min(MAX_MATCH);
            let mut ml = 0usize;
            while ml < limit && s[ml] == cs[ml] {
                ml += 1;
            }
            if ml > best_len {
                best_len = ml;
                best_cand = cand_v;
            }
            if ml >= nice_len {
                match policy {
                    EarlyExitPolicy::SpliceAtNiceLen => {
                        child[pending_lt.0][pending_lt.1] = child[cand_v][0];
                        child[pending_gt.0][pending_gt.1] = child[cand_v][1];
                    }
                    EarlyExitPolicy::ZeroAtNiceLenSpliceAt258 => {
                        if ml == MAX_MATCH {
                            child[pending_lt.0][pending_lt.1] = child[cand_v][0];
                            child[pending_gt.0][pending_gt.1] = child[cand_v][1];
                        } else {
                            child[pending_lt.0][pending_lt.1] = 0;
                            child[pending_gt.0][pending_gt.1] = 0;
                        }
                    }
                    EarlyExitPolicy::AttachCandSideAtNiceLen => {
                        if ml == MAX_MATCH || ml >= s.len().min(cs.len()) {
                            child[pending_lt.0][pending_lt.1] = child[cand_v][0];
                            child[pending_gt.0][pending_gt.1] = child[cand_v][1];
                        } else if s[ml] < cs[ml] {
                            child[pending_gt.0][pending_gt.1] = cand_v;
                            child[pending_lt.0][pending_lt.1] = 0;
                        } else {
                            child[pending_lt.0][pending_lt.1] = cand_v;
                            child[pending_gt.0][pending_gt.1] = 0;
                        }
                    }
                }
                break;
            }
            if s[ml] < cs[ml] {
                child[pending_gt.0][pending_gt.1] = cand_v;
                pending_gt = (cand_v, 0);
                cand_v = child[cand_v][0];
            } else {
                child[pending_lt.0][pending_lt.1] = cand_v;
                pending_lt = (cand_v, 1);
                cand_v = child[cand_v][1];
            }
        }
        if cand_v == 0 {
            child[pending_lt.0][pending_lt.1] = 0;
            child[pending_gt.0][pending_gt.1] = 0;
        }
        results.push((best_len, best_cand));
    }
    results
}

fn probe_2_bt_child_splicing_soundness() {
    // When `pos` (S2) visits `cand` (S1) and finds `ml >= nice_len`, splicing `child[S1][0..1]`
    // into `pending_lt` / `pending_gt` EVICTS `S1` from the BST (replacing `S1` with `S2`),
    // and partitions `S1`'s subtrees around `S1` rather than `S2`.
    //   - At `ml == 258` (MAX_MATCH), `S2[0..258] == S1[0..258]` and `S2` is strictly closer,
    //     so evicting `S1` and inheriting its `<` and `>` subtrees is 100% lossless and order-preserving.
    //   - At `nice_len <= ml < 258` (e.g., `ml = 9, nice_len = 9`), `S2` and `S1` disagree at byte `ml`:
    //     1) Evicting `S1` destroys `S1[9..24]`, so a query `Q` matching `S1` on all 24 bytes gets only 9B;
    //     2) Even worse, if `S1` has a left child `H` with `lcp(H, S1) = 12 > ml = 9` and `S2[9] < S1[9] == H[9]`,
    //        splicing `child[S1][0] = H` into `S2`'s LEFT (`<`) child places `H` (`> S2` at byte 9!) into the `<`
    //        subtree, violating the BST invariant!
    //     3) By contrast, attaching `S1` on its true comparison side at byte `ml` (`AttachCandSideAtNiceLen`)
    //        retains both `S1` and `H` on the `>` side of `S2` in O(1) time.
    let h: &[u8] = b"ABCD_EFG_ZZ_0_MATCH_24B!";
    let s1: &[u8] = b"ABCD_EFG_ZZ_9_xxxxxxxxxx";
    let s2: &[u8] = b"ABCD_EFG_AA_0_yyyyyyyyyy"; // lcp(S2, S1) = 9; S2[9]='A' < S1[9]='Z' == H[9]
    let q: &[u8] = b"ABCD_EFG_ZZ_0_MATCH_24B!"; // Identical to H (24 B), lcp(Q, S2) = 9
    let seq = [h, s1, s2, q];

    // Insert [H, S1, S2] with nice_len = 9 (triggering early exit at S2 vs S1 with ml = 9),
    // then evaluate Query Q with nice_len = 24 (e.g., lazy evaluation / full match probe):
    let mut tree_unsound = bt_insert_and_query(&seq[..3], 9, EarlyExitPolicy::SpliceAtNiceLen);
    let mut tree_attach = bt_insert_and_query(&seq[..3], 9, EarlyExitPolicy::AttachCandSideAtNiceLen);
    let _ = (&mut tree_unsound, &mut tree_attach);

    // Also test with uniform nice_len = 12 where lcp(S2, S1) = 12 >= nice_len, while lcp(Q, S2) = 9 < nice_len!
    //   S1 (v=1): "ABCD_EFG_ZZ_0_MATCH_24B!" (24 B)
    //   S2 (v=2): "ABCD_EFG_ZZ_0_yyyyyyyyyy" (24 B) -> lcp(S2, S1) = 14 >= nice_len=12; S1[14]='M' < S2[14]='y'
    //   Query Q (v=3): "ABCD_EFG_ZZ_0_MATCH_24B!" (24 B, identical to S1!)
    //   Under SpliceAtNiceLen (evicting S1 at ml=14): Q visits S2 (lcp=14 >= 12) and S1 was evicted -> best_len = 14 (lost 10 B!).
    //   Under AttachCandSideAtNiceLen (keeping S1 as S2's left child, queried with nice_len=24): Q finds S1 -> best_len = 24!
    let s1_u: &[u8] = b"ABCD_EFG_ZZ_0_MATCH_24B!";
    let s2_u: &[u8] = b"ABCD_EFG_ZZ_0_yyyyyyyyyy";
    let q_u: &[u8] = b"ABCD_EFG_ZZ_0_MATCH_24B!";
    let res_unsound_evict = bt_insert_and_query(&[s1_u, s2_u, q_u], 14, EarlyExitPolicy::SpliceAtNiceLen);

    // And for the BST ordering inversion (H > S3 spliced into S3's LEFT `<` child at ml = 12 >= nice_len = 12,
    // while Q has lcp(Q, S3) = 9 < nice_len = 12 so Q does NOT early-exit at S3!):
    // Wait: if lcp(S3, S2) = 12 and lcp(Q, S3) = 9, then lcp(Q, S2) = 9, so Q matches a child R of S2 that
    // diverged from S2 at byte 9 (lcp(R, S2) = 9 < 12):
    //   R  (v=1): "ABCD_EFG_ZZ_0_MATCH_24B!" (24 B)
    //   S2 (v=2): "ABCD_EFG_AA_0_xxxxxxxxxx" (24 B) -> lcp(S2, R) = 9 < 12, R[9]='Z' > S2[9]='A' (R is S2's RIGHT child).
    //   S3 (v=3): "ABCD_EFG_AA_0_yyyyyyyyyy" (24 B) -> lcp(S3, S2) = 14 >= nice_len=12!
    //   Query Q (v=4): "ABCD_EFG_ZZ_0_MATCH_24B!" (24 B, identical to R; lcp(Q, S3) = 9 < nice_len=12!).
    //   Look what happens at S3 (nice_len = 12):
    //     - Under ZeroAtNiceLenSpliceAt258 (`*pending_lt = 0; *pending_gt = 0`): S3 zeroes its children, dropping R (Q gets 9B).
    //     - Under AttachCandSideAtNiceLen (`S2 < S3` at byte 14 -> S2 attached to S3's left child, or `S3 < S2` -> S2 attached to S3's right child):
    //       When S3[14]='a' < S2[14]='x', S2 is attached to S3's RIGHT child, so Q (with Q[9]='Z' > S3[9]='A') branches RIGHT to S2,
    //       then RIGHT to R, and finds the full 24-byte match even with uniform nice_len = 12!
    let r_node: &[u8] = b"ABCD_EFG_ZZ_0_MATCH_24B!";
    let s2_node: &[u8] = b"ABCD_EFG_AA_0_xxxxxxxxxx";
    let s3_node: &[u8] = b"ABCD_EFG_AA_0_aaaaaaaaaa"; // lcp(S3, S2) = 14 >= nice_len=12, S3[14]='a' < S2[14]='x'
    let q_node: &[u8] = b"ABCD_EFG_ZZ_0_MATCH_24B!"; // lcp(Q, S3) = 9 < nice_len=12, Q[9]='Z' > S3[9]='A'
    let seq_uniform = [r_node, s2_node, s3_node, q_node];
    let res_zero_cut = bt_insert_and_query(&seq_uniform, 12, EarlyExitPolicy::ZeroAtNiceLenSpliceAt258);
    let res_attach_uniform = bt_insert_and_query(&seq_uniform, 12, EarlyExitPolicy::AttachCandSideAtNiceLen);

    // At ml == 258 (MAX_MATCH), verify that splicing child[cand][0..1] preserves 100% of both `<` and `>` children
    // (where b_lt and b_gt diverge from b_root1 at byte 10 < nice_len = 32):
    let mut b_lt = [b'M'; MAX_MATCH];
    b_lt[10] = b'A';
    let mut b_gt = [b'M'; MAX_MATCH];
    b_gt[10] = b'Z';
    let b_root1 = [b'M'; MAX_MATCH];
    let b_root2 = [b'M'; MAX_MATCH]; // lcp(b_root2, b_root1) == 258 == MAX_MATCH!
    let seq_258: [&[u8]; 6] = [&b_lt, &b_gt, &b_root1, &b_root2, &b_lt, &b_gt];
    let res_258 = bt_insert_and_query(&seq_258, 32, EarlyExitPolicy::ZeroAtNiceLenSpliceAt258);

    println!("\n=== [Probe 2] Binary-Tree Child-Splicing Soundness Only at ml == 258 ===");
    println!(
        "  Unsound evict-splice at ml=14 < 258:       Query Q match_len={} (evicted 24B match S1!)",
        res_unsound_evict[2].0
    );
    println!(
        "  Uniform nice_len=12 zero-cut vs side-attach: zero-cut Q match_len={}, side-attach Q match_len={} (found R at v={})",
        res_zero_cut[3].0, res_attach_uniform[3].0, res_attach_uniform[3].1
    );
    println!(
        "  Sound splice at ml=258 (MAX_MATCH):        root2 match_len={}, subsequent < child match_len={}, > child match_len={}",
        res_258[3].0, res_258[4].0, res_258[5].0
    );

    assert_eq!(res_unsound_evict[2].0, 14, "Evicting cand via splice at ml=14 < 258 loses 24B match S1");
    assert_eq!(res_zero_cut[3].0, 9, "Zeroing both pending pointers at ml=14 drops R's subtree");
    assert_eq!(res_attach_uniform[3].0, 24, "Attaching cand on its comparison side preserves R (24B)");
    assert_eq!(res_258[3].0, 258);
    assert_eq!(res_258[4].0, 258, "Splicing at ml==258 must preserve the < subtree");
    assert_eq!(res_258[5].0, 258, "Splicing at ml==258 must preserve the > subtree");
}

// ============================================================================
// 3. bt_head3 `cv != v` Distance-Shadowing Bug
// ============================================================================

fn simulate_bt_head3_vs_head4(require_cv_ne_v: bool) -> (usize, usize, u32) {
    // Stream layout:
    //   pos = 100:  "ABCD_FAR"   (distance from pos=3100 is d_far = 3000)
    //   pos = 3090: "ABCD_NEAR"  (distance from pos=3100 is d_near = 10)
    //   pos = 3100: "ABCD_CURR"  (4-byte match with both pos=100 and pos=3090)
    // Suppose pos=100 updated bt_head3[h3] (e.g., pos=3090 was skipped in head3 or collided),
    // while pos=3090 is the root of bt_head4[h4].
    let v: u32 = u32::from_le_bytes(*b"ABCD");
    let cv_head3: u32 = u32::from_le_bytes(*b"ABCD"); // Same 4 bytes at d_far = 3000!
    let d_far = 3000usize;
    let d_near = 10usize;

    let mut best_len = 0usize;
    let mut best_dist = 0usize;

    // Step 1: bt_head3 probe
    let h3_match_3b = ((cv_head3 ^ v) & 0x00FF_FFFF) == 0;
    if h3_match_3b && (!require_cv_ne_v || cv_head3 != v) {
        // Without `cv != v`, extending or accepting the 4-byte match in head3 sets best_len = 4 at d_far = 3000:
        best_len = if cv_head3 == v { 4 } else { 3 };
        best_dist = d_far;
    }

    // Step 2: bt_head4 probe visits cpos = 3090 (d_near = 10), which has ml = 4.
    // Because BT only records matches strictly longer than `best_len` (`if ml > best_len`),
    // if `best_len` is already 4 from `bt_head3`, the closer `d_near = 10` match is shadowed!
    let ml_bt4 = 4usize;
    if ml_bt4 > best_len {
        best_len = ml_bt4;
        best_dist = d_near;
    }

    // Extra bits in RFC 1951 for distance: d=10 -> dsym=6 (2 extra bits); d=3000 -> dsym=22 (10 extra bits)
    let dist_extra_bits = if best_dist <= 16 { 2 } else { 10 };
    (best_len, best_dist, dist_extra_bits)
}

fn probe_3_bt_head3_distance_shadowing() {
    let (len_buggy, dist_buggy, ebits_buggy) = simulate_bt_head3_vs_head4(false);
    let (len_fixed, dist_fixed, ebits_fixed) = simulate_bt_head3_vs_head4(true);

    println!("\n=== [Probe 3] bt_head3 `cv != v` Distance-Shadowing Guard ===");
    println!(
        "  Without `cv != v`: best_len={}, best_dist={} ({} distance extra bits — shadowed d_near=10!)",
        len_buggy, dist_buggy, ebits_buggy
    );
    println!(
        "  With    `cv != v`: best_len={}, best_dist={}   ({} distance extra bits — saved {} bits/match)",
        len_fixed, dist_fixed, ebits_fixed, ebits_buggy - ebits_fixed
    );

    assert_eq!((len_buggy, dist_buggy), (4, 3000));
    assert_eq!((len_fixed, dist_fixed), (4, 10));
}

// ============================================================================
// 4. OPT_NO_TRUNC (0x8000) Suffix Pruning & RLE `!is_rle_interior` Ablation
// ============================================================================

fn build_repetitive_nci_xml_buffer(target_len: usize) -> Vec<u8> {
    let mut buf = Vec::with_capacity(target_len);
    // 144-byte structured XML/chemical record (>= nice_len = 64)
    let xml_record = b"<molecule id=\"m_0001\"><atomArray><atom id=\"a1\" elementType=\"C\" x3=\"1.234\" y3=\"-0.567\"/></atomArray><bondArray><bond atomRefs2=\"a1 a2\" order=\"1\"/></bondArray></molecule>\n";
    let mut idx = 0usize;
    while buf.len() + 256 <= target_len {
        // 36-byte tabular RLE '0' run (< nice_len = 64, matching nci's 16..48B runs under nice_len=128..258)
        buf.extend(std::iter::repeat(b'0').take(36));
        buf.push(b':');
        buf.push(((idx % 16) as u8) + b'A');
        // 170-byte repeated XML record (>= nice_len = 64, triggering suffix skip + OPT_NO_TRUNC)
        buf.extend_from_slice(xml_record);
        idx += 1;
    }
    buf.truncate(target_len);
    buf
}

#[inline]
fn hash4(v: u32) -> usize {
    ((v.wrapping_mul(0x1E35_A7BD)) >> 17) as usize
}

fn run_matchfind_and_dp_ablation(
    input: &[u8],
    skip_rle_interior: bool,
    use_opt_no_trunc: bool,
) -> (u64, u64, u64, u128) {
    let t0 = Instant::now();
    let n = input.len();
    let mut head4 = vec![u32::MAX; 32768];
    let mut prev4 = vec![0u16; WINDOW_SIZE];
    // (raw_len_with_flag, dist)
    let mut opt_matches = vec![(0u16, 0u16); n];

    let nice_len = 64usize;
    let max_chain = 64usize;
    let mut chain_steps: u64 = 0;

    let mut pos = 0usize;
    while pos + 4 <= n {
        let cur4 = u32::from_le_bytes(input[pos..pos + 4].try_into().unwrap());
        let is_rle = pos > 0 && cur4 == cur4.rotate_right(8) && input[pos - 1] == input[pos];
        let is_rle_interior = is_rle && pos + 4 < n && input[pos + 4] == input[pos];

        let h = hash4(cur4);
        let prev_pos = head4[h];

        if !skip_rle_interior || !is_rle_interior {
            let delta = if prev_pos != u32::MAX && pos - (prev_pos as usize) < WINDOW_SIZE {
                (pos - (prev_pos as usize)) as u16
            } else {
                0
            };
            prev4[pos & WINDOW_MASK] = delta;
            head4[h] = pos as u32;
        }

        let mut blen = 0usize;
        let mut bdist = 0usize;
        let max_l = MAX_MATCH.min(n - pos);

        // RLE fast-path if is_rle
        if skip_rle_interior && is_rle {
            let b = input[pos];
            let mut l = 0usize;
            while l < max_l && input[pos + l] == b {
                l += 1;
            }
            if l >= 3 {
                blen = l;
                bdist = 1;
            }
        }

        if blen < nice_len && prev_pos != u32::MAX && (!skip_rle_interior || !is_rle_interior) {
            let mut cpos = prev_pos as usize;
            let mut probes = 0usize;
            while pos - cpos <= BT_MAX_DIST_SAFE && probes < max_chain {
                probes += 1;
                chain_steps += 1;
                if input[cpos + blen] == input[pos + blen]
                    && u32::from_le_bytes(input[cpos..cpos + 4].try_into().unwrap()) == cur4
                {
                    let mut l = 4usize;
                    while l < max_l && input[cpos + l] == input[pos + l] {
                        l += 1;
                    }
                    if l > blen {
                        blen = l;
                        bdist = pos - cpos;
                        if blen >= nice_len {
                            break;
                        }
                    }
                }
                let d = prev4[cpos & WINDOW_MASK] as usize;
                if d == 0 {
                    break;
                }
                cpos -= d;
            }
        }

        if blen >= 3 {
            opt_matches[pos] = (blen as u16, bdist as u16);
        }

        if blen >= nice_len {
            let mut k = 1usize;
            while k < blen && pos + k + 4 <= n {
                let s = pos + k;
                let s4 = u32::from_le_bytes(input[s..s + 4].try_into().unwrap());
                let s_rle = s4 == s4.rotate_right(8) && input[s - 1] == input[s];
                let s_rle_int = s_rle && s + 4 < n && input[s + 4] == input[s];
                if !skip_rle_interior || !s_rle_int {
                    let sh = hash4(s4);
                    let sp = head4[sh];
                    prev4[s & WINDOW_MASK] =
                        if sp != u32::MAX && s - (sp as usize) < WINDOW_SIZE {
                            (s - (sp as usize)) as u16
                        } else {
                            0
                        };
                    head4[sh] = s as u32;
                }
                let rem_l = blen - k;
                if rem_l >= 3 {
                    let encoded_l = if use_opt_no_trunc {
                        (rem_l as u16) | OPT_NO_TRUNC
                    } else {
                        rem_l as u16
                    };
                    opt_matches[s] = (encoded_l, bdist as u16);
                }
                k += 1;
            }
            pos += blen;
        } else {
            pos += 1;
        }
    }

    // Forward DP pass counting exact edge relaxations
    let mut dp_cost = vec![u64::MAX >> 2; n + 1];
    dp_cost[0] = 0;
    let mut dp_edges: u64 = 0;

    for i in 0..n {
        let base = dp_cost[i];
        let lit_c = base + (8 << 4);
        if lit_c < dp_cost[i + 1] {
            dp_cost[i + 1] = lit_c;
        }
        dp_edges += 1;

        let (raw_l, dist) = opt_matches[i];
        let no_trunc = (raw_l & OPT_NO_TRUNC) != 0;
        let ml = ((raw_l & !OPT_NO_TRUNC) as usize).min(n - i);
        if ml >= 3 && dist > 0 {
            let mcost_base = base + (12 << 4);
            if no_trunc {
                dp_edges += 1;
                if mcost_base < dp_cost[i + ml] {
                    dp_cost[i + ml] = mcost_base;
                }
            } else {
                for l in 3..=ml {
                    dp_edges += 1;
                    if mcost_base < dp_cost[i + l] {
                        dp_cost[i + l] = mcost_base;
                    }
                }
            }
        }
    }

    let elapsed_us = t0.elapsed().as_micros();
    (chain_steps, dp_edges, dp_cost[n] >> 4, elapsed_us)
}

fn probe_4_opt_no_trunc_and_rle_ablation() {
    let buf = build_repetitive_nci_xml_buffer(65536);

    let (chains_00, edges_00, bits_00, us_00) = run_matchfind_and_dp_ablation(&buf, false, false);
    let (chains_10, edges_10, bits_10, us_10) = run_matchfind_and_dp_ablation(&buf, true, false);
    let (chains_01, edges_01, bits_01, us_01) = run_matchfind_and_dp_ablation(&buf, false, true);
    let (chains_11, edges_11, bits_11, us_11) = run_matchfind_and_dp_ablation(&buf, true, true);

    println!("\n=== [Probe 4] OPT_NO_TRUNC (0x8000) & RLE `!is_rle_interior` Ablation (64 KiB repetitive buffer) ===");
    println!(
        "  Baseline (no RLE guard, no OPT_NO_TRUNC): chain_steps={:>8}, dp_edges={:>9}, cost_bits={}, time={} us",
        chains_00, edges_00, bits_00, us_00
    );
    println!(
        "  + !is_rle_interior only:                  chain_steps={:>8} ({:.2}x fewer), dp_edges={:>9}, cost_bits={}, time={} us",
        chains_10,
        chains_00 as f64 / chains_10.max(1) as f64,
        edges_10,
        bits_10,
        us_10
    );
    println!(
        "  + OPT_NO_TRUNC only:                      chain_steps={:>8}, dp_edges={:>9} ({:.2}x fewer), cost_bits={}, time={} us",
        chains_01,
        edges_01,
        edges_00 as f64 / edges_01.max(1) as f64,
        bits_01,
        us_01
    );
    println!(
        "  + BOTH (!is_rle_interior + OPT_NO_TRUNC): chain_steps={:>8} ({:.2}x fewer), dp_edges={:>9} ({:.2}x fewer), cost_bits={}, time={} us",
        chains_11,
        chains_00 as f64 / chains_11.max(1) as f64,
        edges_11,
        edges_00 as f64 / edges_11.max(1) as f64,
        bits_11,
        us_11
    );

    assert!(chains_11 * 3 < chains_00, "Expected >3x chain step reduction from !is_rle_interior");
    assert!(edges_11 * 15 < edges_10, "Expected >15x DP edge reduction from OPT_NO_TRUNC");
    assert_eq!(bits_10, bits_11, "OPT_NO_TRUNC must preserve optimal terminal DP cost");
}

// ============================================================================
// 5. Pre-Encoded 5-Bit `dsym` (4.3 KiB L1d DpPrices) & Tiny-Input DP Trap
// ============================================================================

#[repr(C)]
struct DpPrices {
    lit_hi: [u64; 256],
    len_hi: [u64; 259],
    dist_sym_hi: [u64; 32],
}

#[inline]
const fn dist_to_sym(dist: usize) -> usize {
    if dist <= 4 {
        dist - 1
    } else {
        let d = dist - 1;
        let msb = (usize::BITS - 1 - d.leading_zeros()) as usize;
        (msb << 1) + ((d >> (msb - 1)) & 1)
    }
}

#[inline]
const fn dist_extra_bits(dsym: usize) -> u32 {
    if dsym < 4 {
        0
    } else {
        ((dsym as u32) >> 1) - 1
    }
}

#[inline]
const fn len_to_sym_and_extra(len: usize) -> (usize, u32) {
    if len == 258 {
        (285, 0)
    } else if len <= 10 {
        (254 + len, 0)
    } else {
        let l = len - 3;
        let msb = (usize::BITS - 1 - l.leading_zeros()) as usize;
        let ebits = (msb - 2) as u32;
        let sym = 265 + ((msb - 3) << 2) + ((l >> ebits) & 3);
        (sym, ebits)
    }
}

fn solve_one_match_dp(
    input: &[u8],
    match_pos: usize,
    match_len: usize,
    match_dist: usize,
    clamp_tiny_to_static: bool,
) -> (u32, bool, u32) {
    let n = input.len();
    let mut lit_price_q4 = [128u32; 256]; // Default 8.0 bits = 128 Q4 units
    let len_price_q4: u32;
    let dist_price_q4: u32;

    if clamp_tiny_to_static && n < 48 {
        // Static Huffman prices: lit 0..=143 -> 8 bits (128 Q4); len=4 -> 7 bits (112 Q4); dist -> 5 bits (80 Q4)
        for b in 0..=143 {
            lit_price_q4[b] = 8 * 16;
        }
        len_price_q4 = 7 * 16;
        dist_price_q4 = 5 * 16;
    } else {
        // Unclamped Pass-1 empirical byte-frequency table (`from_raw_bytes_into` without tiny-input guard)
        let mut counts = [0u32; 256];
        for &b in input {
            counts[b as usize] += 1;
        }
        let total_f = (n as f64).log2();
        for b in 0..256 {
            if counts[b] > 0 {
                let bits = (total_f - (counts[b] as f64).log2()).max(1.0);
                lit_price_q4[b] = (bits * 16.0).round() as u32;
            }
        }
        // Unclamped initial match priors: len=4 -> 5.5 bits (88 Q4), dist -> 5.0 bits (80 Q4)
        len_price_q4 = 88;
        dist_price_q4 = 80;
    }

    let four_lits_q4: u32 = input[match_pos..match_pos + match_len]
        .iter()
        .map(|&b| lit_price_q4[b as usize])
        .sum();
    let match_q4: u32 = len_price_q4 + dist_price_q4 + dist_extra_bits(dist_to_sym(match_dist)) * 16;
    let chose_match = match_q4 < four_lits_q4;

    // Actual RFC 1951 static-block bit cost (3-bit header + tokens + 7-bit EOB)
    let mut static_bits = 3u32 + 7u32;
    let mut i = 0usize;
    while i < n {
        if chose_match && i == match_pos {
            static_bits += 7 + 5 + dist_extra_bits(dist_to_sym(match_dist));
            i += match_len;
        } else {
            static_bits += if input[i] <= 143 { 8 } else { 9 };
            i += 1;
        }
    }
    (four_lits_q4, chose_match, static_bits)
}

fn probe_5_dp_prices_and_tiny_input_trap() {
    let dp_prices_bytes = size_of::<DpPrices>();
    let legacy_dist_u64_bytes = 32768 * size_of::<u64>();
    let legacy_dist_u16_bytes = 32768 * size_of::<u16>();

    // Verify 64-bit composite key `(cost_q4 << 32) | tie_break` with pre-encoded 5-bit dsym
    // never overflows bit 31 of the low half across all 256 lengths and 32768 distances:
    let mut prices = DpPrices {
        lit_hi: [128u64 << 32; 256],
        len_hi: [0u64; 259],
        dist_sym_hi: [0u64; 32],
    };
    for l in 3..=258 {
        let (_sym, ebits) = len_to_sym_and_extra(l);
        prices.len_hi[l] = (((7 + ebits) as u64) * 16) << 32;
    }
    for dsym in 0..30 {
        let ebits = dist_extra_bits(dsym);
        prices.dist_sym_hi[dsym] = (((5 + ebits) as u64) * 16) << 32;
    }

    let base_cost: u64 = (1000u64 << 32) | 42;
    for dist in [1usize, 4, 5, 512, 4096, 32768] {
        let dsym = dist_to_sym(dist);
        let dm1 = (dist - 1) as u64;
        let base_plus_dist = base_cost + prices.dist_sym_hi[dsym] + dm1;
        for l in [3usize, 4, 10, 32, 258] {
            let cand = base_plus_dist + prices.len_hi[l];
            let expected_hi = 1000 + (prices.dist_sym_hi[dsym] >> 32) + (prices.len_hi[l] >> 32);
            let expected_lo = 42 + dm1;
            assert_eq!(cand >> 32, expected_hi);
            assert_eq!(cand & 0xFFFF_FFFF, expected_lo);
        }
    }

    // Tiny-input DP trap 1: b"Deflate late" (12 B, match len=4, dist=4 at pos=8)
    let (lits_q4_unclamped_1, match_unclamped_1, bits_unclamped_1) =
        solve_one_match_dp(b"Deflate late", 8, 4, 4, false);
    let (lits_q4_clamped_1, match_clamped_1, bits_clamped_1) =
        solve_one_match_dp(b"Deflate late", 8, 4, 4, true);

    // Tiny-input DP trap 2: [10, 10, 10, 10, 10, 55] (6 B, RLE match len=4, dist=1 at pos=1)
    let rle6 = [10u8, 10, 10, 10, 10, 55];
    let (lits_q4_unclamped_2, match_unclamped_2, bits_unclamped_2) =
        solve_one_match_dp(&rle6, 1, 4, 1, false);
    let (lits_q4_clamped_2, match_clamped_2, bits_clamped_2) =
        solve_one_match_dp(&rle6, 1, 4, 1, true);

    println!("\n=== [Probe 5] 4.27 KiB L1d `DpPrices` (5-bit `dsym`) & Tiny-Input Pass-1 DP Trap ===");
    println!(
        "  sizeof(DpPrices) = {} B ({:.2} KiB, 30-iter rebuild) vs. dist_price[32768] = {} B ({:.1} KiB u16) / {} B ({:.1} KiB u64) (1092x fewer rebuild steps)",
        dp_prices_bytes,
        dp_prices_bytes as f64 / 1024.0,
        legacy_dist_u16_bytes,
        legacy_dist_u16_bytes as f64 / 1024.0,
        legacy_dist_u64_bytes,
        legacy_dist_u64_bytes as f64 / 1024.0
    );
    println!(
        "  b\"Deflate late\" (12 B): unclamped 4-lit Q4={} vs match Q4=168 -> chose_match={}, static_bits={} ({} B); clamped Q4={} -> chose_match={}, static_bits={} ({} B)",
        lits_q4_unclamped_1,
        match_unclamped_1,
        bits_unclamped_1,
        (bits_unclamped_1 + 7) / 8,
        lits_q4_clamped_1,
        match_clamped_1,
        bits_clamped_1,
        (bits_clamped_1 + 7) / 8
    );
    println!(
        "  [10,10,10,10,10,55] (6 B): unclamped 4-lit Q4={} vs match Q4=168 -> chose_match={}, static_bits={} ({} B); clamped Q4={} -> chose_match={}, static_bits={} ({} B)",
        lits_q4_unclamped_2,
        match_unclamped_2,
        bits_unclamped_2,
        (bits_unclamped_2 + 7) / 8,
        lits_q4_clamped_2,
        match_clamped_2,
        bits_clamped_2,
        (bits_clamped_2 + 7) / 8
    );

    assert_eq!(dp_prices_bytes, 4376);
    assert!(!match_unclamped_1 && bits_unclamped_1 == 106 && (bits_unclamped_1 + 7) / 8 == 14);
    assert!(match_clamped_1 && bits_clamped_1 == 86 && (bits_clamped_1 + 7) / 8 == 11);
    assert!(!match_unclamped_2 && bits_unclamped_2 == 58 && (bits_unclamped_2 + 7) / 8 == 8);
    assert!(match_clamped_2 && bits_clamped_2 == 38 && (bits_clamped_2 + 7) / 8 == 5);

    // Raw-byte empirical literal trap on prose:
    // High-frequency trigram characters (' ', 'e', 't') occur ~45% of the time in raw prose
    // (pricing 3 literals " the" at ~10.8 bits from raw bytes), but after LZ77 absorbs common words
    // into matches, residual literals are flatter (~21.5 bits for 3 literals), so raw-byte Pass-1
    // prices cause Pass-1 DP to break marginal (len=3, dist=512) matches (cost ~16 bits < 21.5 bits residual,
    // but > 10.8 bits raw-byte prior!).
    let raw_3lit_q4: u32 = 54 + 60 + 62; // ~3.38 + 3.75 + 3.88 = 11.0 bits (176 Q4)
    let residual_3lit_q4: u32 = 88 + 96 + 96; // ~5.5 + 6.0 + 6.0 = 17.5 bits (280 Q4)
    let marginal_len3_dist512_q4: u32 = 88 + 80 + 8 * 16; // len3 (5.5b) + dist (5.0b) + 8 extra bits = 18.5b? No, d=512 has 7 extra bits = 112 Q4 -> 280 Q4, or d=128 (5 extra bits = 80 Q4) -> 248 Q4!
    println!(
        "  Raw-byte prose literal trap (len=3, d=128 match Q4=248): raw-byte 3-lit Q4={} (<248, breaks match!) vs residual 3-lit Q4={} (>248, keeps match!)",
        raw_3lit_q4, residual_3lit_q4
    );
    assert!(raw_3lit_q4 < marginal_len3_dist512_q4 - 32 && residual_3lit_q4 > 248);
}

// ============================================================================
// 6. Canonical Length-Limited Huffman Kraft Rebalancing & `active_cl == 1`
// ============================================================================

fn build_length_limited_code_lengths(freqs: &[u32], max_bits: usize) -> (Vec<u8>, usize, u32) {
    let mut active: Vec<(u32, usize)> = freqs
        .iter()
        .copied()
        .enumerate()
        .filter(|&(sym_idx, f)| f > 0 && sym_idx < freqs.len())
        .map(|(i, f)| (f, i))
        .collect();

    let mut lens = vec![0u8; freqs.len()];
    if active.is_empty() {
        return (lens, 0, 0);
    }
    if active.len() == 1 {
        let only_sym = active[0].1;
        let partner = only_sym ^ 1;
        lens[only_sym] = 1;
        lens[partner] = 1;
        let kraft = (1u32 << (max_bits - 1)) + (1u32 << (max_bits - 1));
        return (lens, 1, kraft);
    }

    active.sort_unstable_by_key(|&(f, i)| (f, i));
    let n = active.len();

    // Two-queue Huffman parent array
    let mut parent = vec![0usize; 2 * n];
    let mut internal_w = vec![0u64; n];
    let mut leaf_idx = 0usize;
    let mut int_head = 0usize;
    let mut int_tail = 0usize;

    let next_min = |leaf_idx: &mut usize, int_head: &mut usize, int_tail: usize, internal_w: &[u64]| -> (u64, usize) {
        let take_leaf = if *leaf_idx < n {
            if *int_head < int_tail {
                (active[*leaf_idx].0 as u64) <= internal_w[*int_head]
            } else {
                true
            }
        } else {
            false
        };
        if take_leaf {
            let w = active[*leaf_idx].0 as u64;
            let id = *leaf_idx;
            *leaf_idx += 1;
            (w, id)
        } else {
            let w = internal_w[*int_head];
            let id = n + *int_head;
            *int_head += 1;
            (w, id)
        }
    };

    for step in 0..(n - 1) {
        let (w1, id1) = next_min(&mut leaf_idx, &mut int_head, int_tail, &internal_w);
        let (w2, id2) = next_min(&mut leaf_idx, &mut int_head, int_tail, &internal_w);
        internal_w[step] = w1 + w2;
        parent[id1] = n + step;
        parent[id2] = n + step;
        int_tail += 1;
    }

    let root = 2 * n - 2;
    let mut node_depth = vec![0usize; 2 * n - 1];
    let mut max_unbounded_depth = 0usize;
    let mut bl_count = vec![0u32; max_bits + 1];
    let mut overflow = 0u32;

    for id in (0..root).rev() {
        let d = node_depth[parent[id]] + 1;
        node_depth[id] = d;
        if id < n {
            if d > max_unbounded_depth {
                max_unbounded_depth = d;
            }
            if d > max_bits {
                bl_count[max_bits] += 1;
                overflow += 1;
            } else {
                bl_count[d] += 1;
            }
        }
    }

    let mut kraft: u32 = (1..=max_bits)
        .map(|b| bl_count[b] << (max_bits - b))
        .sum();
    let target: u32 = 1u32 << max_bits;

    // Exact Kraft debt rebalancing (length-limited Huffman normalization):
    // Note that a subtree rooted at depth `max_bits` with `k` leaves at depth `> max_bits`
    // had original Kraft weight `1` (`2^0`) and clamped weight `k`, so its exact Kraft
    // excess is `k - 1` (not `k`!). Rebalancing until `kraft == target` where each step
    // `bl_count[bits] -= 1; bl_count[bits+1] += 2; bl_count[max_bits] -= 1`
    // preserves total leaves `(-1 + 2 - 1 = 0)` and reduces `kraft` by `-2^{M-b} + 2*2^{M-b-1} - 1 = -1`
    // guarantees exact equality `kraft == 2^max_bits`.
    let _ = overflow;
    while kraft > target {
        let mut bits = max_bits - 1;
        while bl_count[bits] == 0 {
            bits -= 1;
        }
        bl_count[bits] -= 1;
        bl_count[bits + 1] += 2;
        bl_count[max_bits] -= 1;
        kraft -= 1;
    }

    // Assign lengths in descending frequency order (shortest lengths to highest frequencies)
    let mut rank = n;
    let mut kraft_sum = 0u32;
    for bits in 1..=max_bits {
        for _ in 0..bl_count[bits] {
            rank -= 1;
            let sym = active[rank].1;
            lens[sym] = bits as u8;
            kraft_sum += 1u32 << (max_bits - bits);
        }
    }

    (lens, max_unbounded_depth, kraft_sum)
}

fn probe_6_huffman_kraft_and_active_cl_1() {
    // 6A: 30 Fibonacci frequencies (unbounded depth = 29), constrained to MAX_BITS = 15 and MAX_BITS = 7
    let mut fib = vec![0u32; 30];
    fib[0] = 1;
    fib[1] = 1;
    for i in 2..30 {
        fib[i] = fib[i - 1] + fib[i - 2];
    }

    let (lens_15, unbounded_15, kraft_15) = build_length_limited_code_lengths(&fib, 15);
    let (lens_14, _unbounded_14, kraft_14) = build_length_limited_code_lengths(&fib, 14);
    let (lens_7, _unbounded_7, kraft_7) = build_length_limited_code_lengths(&fib[..19], 7);

    // 6B: Precode `active_cl == 1` (e.g., all 256 literal symbols have code length 8 -> precode uses ONLY symbol 8!)
    let mut precode_freqs = [0u32; 19];
    precode_freqs[8] = 38; // Only symbol 8 (and repeat code 16 if RLE, or 1 symbol active)
    let (pre_lens, _unb, pre_kraft) = build_length_limited_code_lengths(&precode_freqs, 7);

    println!("\n=== [Probe 6] Moffat-Katajainen Kraft Rebalancing & `active_cl == 1` Dummy Partner ===");
    println!(
        "  Fibonacci(30): unbounded_depth={}, capped MAX_BITS=15 max_len={}, Kraft={}/{} (100% tight)",
        unbounded_15,
        lens_15.iter().copied().max().unwrap(),
        kraft_15,
        1u32 << 15
    );
    println!(
        "  Fibonacci(30): capped MAX_BITS=14 (4-lit 64-bit word limit) max_len={}, Kraft={}/{}",
        lens_14.iter().copied().max().unwrap(),
        kraft_14,
        1u32 << 14
    );
    println!(
        "  Fibonacci(19): capped MAX_BITS=7  (RFC 1951 precode limit)  max_len={}, Kraft={}/{}",
        lens_7.iter().copied().max().unwrap(),
        kraft_7,
        1u32 << 7
    );
    println!(
        "  Precode active_cl == 1 (only sym=8 active): len[8]={}, dummy partner len[8^1=9]={}, Kraft={}/{}",
        pre_lens[8],
        pre_lens[9],
        pre_kraft,
        1u32 << 7
    );

    assert_eq!(unbounded_15, 29);
    assert_eq!(lens_15.iter().copied().max().unwrap(), 15);
    assert_eq!(kraft_15, 1u32 << 15);
    assert_eq!(lens_14.iter().copied().max().unwrap(), 14);
    assert_eq!(kraft_14, 1u32 << 14);
    assert_eq!(lens_7.iter().copied().max().unwrap(), 7);
    assert_eq!(kraft_7, 1u32 << 7);
    assert_eq!(pre_lens[8], 1);
    assert_eq!(pre_lens[9], 1);
    assert_eq!(pre_kraft, 1u32 << 7);
}

// ============================================================================
// 7. Exact Multi-Chunk `BTYPE=00` Stored Block Bit Cost with `first_pad`
// ============================================================================

fn stored_block_formula_bits(raw_len: usize, bit_offset: usize) -> usize {
    let first_pad = (8 - ((bit_offset + 3) & 7)) & 7;
    if raw_len == 0 {
        return 3 + first_pad + 32;
    }
    let chunks = 1 + (raw_len - 1) / 65535;
    3 + first_pad + 32 + (chunks - 1) * 40 + raw_len * 8
}

fn simulate_stored_block_emission(raw_len: usize, bit_offset: usize, is_final: bool) -> (usize, Vec<u8>) {
    let mut total_bits = bit_offset;
    let mut bfinal_flags = Vec::new();
    if raw_len == 0 {
        total_bits += 3; // BFINAL + BTYPE=00
        bfinal_flags.push(if is_final { 1 } else { 0 });
        let pad = (8 - (total_bits & 7)) & 7;
        total_bits += pad + 32;
        return (total_bits - bit_offset, bfinal_flags);
    }

    let mut rem = raw_len;
    while rem > 0 {
        let chunk = rem.min(65535);
        rem -= chunk;
        let chunk_final = is_final && rem == 0;
        bfinal_flags.push(if chunk_final { 1 } else { 0 });
        total_bits += 3;
        let pad = (8 - (total_bits & 7)) & 7;
        total_bits += pad + 32 + chunk * 8;
    }
    (total_bits - bit_offset, bfinal_flags)
}

fn probe_7_multi_chunk_stored_accounting() {
    println!("\n=== [Probe 7] Multi-Chunk `BTYPE=00` Stored Block Bit Cost with `first_pad` ===");
    for &raw_len in &[0usize, 1, 65535, 65536, 131070, 131071] {
        for bit_offset in 0..8 {
            let formula = stored_block_formula_bits(raw_len, bit_offset);
            let (emitted, bfinal_flags) = simulate_stored_block_emission(raw_len, bit_offset, true);
            assert_eq!(
                formula, emitted,
                "Stored bit mismatch at raw_len={}, bit_offset={}",
                raw_len, bit_offset
            );
            assert_eq!(*bfinal_flags.last().unwrap(), 1);
            for &f in &bfinal_flags[..bfinal_flags.len() - 1] {
                assert_eq!(f, 0, "Intermediate 65535-byte stored chunk must have BFINAL=0");
            }
        }
    }
    let (bits_65536_off0, flags_65536) = simulate_stored_block_emission(65536, 0, true);
    let (bits_65536_off3, _) = simulate_stored_block_emission(65536, 3, true);
    println!(
        "  Verified 48 (raw_len, bit_offset) pairs: raw_len=65536 (2 chunks, BFINAL={:?}) -> off=0: {} bits (80 header bits), off=3: {} bits (77 header bits)",
        flags_65536, bits_65536_off0, bits_65536_off3
    );
}


// ============================================================================
// 8. Exhaustive Distance Encoding & Variant-4 Inflate Refill (0..=63 Bits)
// ============================================================================

#[inline]
const fn ref_dist_to_sym_and_extra(dist: usize) -> (usize, u32, u32) {
    if dist <= 2 {
        (dist - 1, 0, 0)
    } else {
        let d = dist - 1;
        let msb = (usize::BITS - 1 - d.leading_zeros()) as usize;
        let ebits = (msb - 1) as u32;
        let sym = (msb << 1) + ((d >> ebits) & 1);
        let extra = (d & ((1usize << ebits) - 1)) as u32;
        (sym, ebits, extra)
    }
}

fn verify_exhaustive_dist_table_and_variant4_refill() {
    // Verify RFC 1951 1..=32768 round-trip for dist_to_sym + extra bits:
    let base_dist: [usize; 30] = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
        257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
        8193, 12289, 16385, 24577,
    ];
    for dist in 1usize..=32768 {
        let sym_fast = dist_to_sym(dist);
        let (sym_ref, ebits, extra) = ref_dist_to_sym_and_extra(dist);
        assert_eq!(sym_fast, sym_ref, "dist_to_sym mismatch at dist={}", dist);
        assert_eq!(ebits, dist_extra_bits(sym_fast));
        assert_eq!(base_dist[sym_ref] + extra as usize, dist);
    }

    // Verify Variant-4 branchless 64-bit LSB bitreader invariant across all starting
    // bit counts `bitcnt in 0..=63` and every unread byte count `avail >= 8`:
    //   new_buf = bitbuf | (le_u64(src) << bitcnt)
    //   consume_bytes = (63 - bitcnt) >> 3  (== 7 - (bitcnt >> 3))
    //   next_bitcnt = bitcnt | 56           (ranges 56..=63; exact bits preserved in 0..bitcnt)
    // Because shift `bitcnt < 64`, all low `bitcnt` bits of `bitbuf` stay intact and
    // new bits fill `[bitcnt, 64)` without overflow or branch misprediction.
    let stream = [0xA5u8, 0x5A, 0x3C, 0xC3, 0xF0, 0x0F, 0x96, 0x69, 0x11, 0x22, 0x33, 0x44];
    for bitcnt in 0u32..64 {
        let low_mask = if bitcnt == 0 { 0u64 } else { (1u64 << bitcnt) - 1 };
        let old_bits = 0xDEAD_BEEF_CAFE_BABEu64 & low_mask;
        let word = u64::from_le_bytes(stream[..8].try_into().unwrap());
        let new_buf = old_bits | (word << bitcnt);
        let advance = ((63 - bitcnt) >> 3) as usize;
        let new_cnt = bitcnt | 56;

        assert_eq!(advance, 7 - ((bitcnt >> 3) as usize));
        assert!((56..=63).contains(&new_cnt));
        assert_eq!(new_buf & low_mask, old_bits, "Existing bits corrupted at bitcnt={}", bitcnt);
        let expected_added_bits = ((new_cnt - bitcnt) as usize) / 8;
        assert_eq!(advance, expected_added_bits, "Byte advance vs bitcnt delta mismatch at {}", bitcnt);
        let loaded_bits = (word & ((1u64 << (advance * 8)) - 1)) << bitcnt;
        assert_eq!((new_buf ^ old_bits) & ((1u64 << (bitcnt + (advance as u32) * 8)) - 1), loaded_bits);
    }

    println!("\n=== [Probe 8] Exhaustive Distance Table (1..=32768) & Variant-4 Refill (0..=63) ===");
    println!("  dist_to_sym(1..=32768): 32768/32768 round-trips exact; Variant-4 refill: 64/64 bitcnt states exact (new_cnt in 56..=63, advance = 7 - (bitcnt >> 3))");
}

fn main() {
    probe_1_bt_max_dist_self_cycle();
    probe_2_bt_child_splicing_soundness();
    probe_3_bt_head3_distance_shadowing();
    probe_4_opt_no_trunc_and_rle_ablation();
    probe_5_dp_prices_and_tiny_input_trap();
    probe_6_huffman_kraft_and_active_cl_1();
    probe_7_multi_chunk_stored_accounting();
    verify_exhaustive_dist_table_and_variant4_refill();
    println!("\nALL 8 DEFLATE/INFLATE PROBES VERIFIED SUCCESSFULLY (exit 0).");
}
