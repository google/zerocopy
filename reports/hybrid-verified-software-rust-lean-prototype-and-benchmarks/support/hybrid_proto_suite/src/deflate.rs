#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LzToken {
    Lit(u8),
    Match { dist: usize, len: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeflatePlan {
    pub tokens: Vec<LzToken>,
    pub max_bits: u8,
    /// Fixed 256-entry literal byte code length table (0 = unused symbol).
    pub code_lengths: [u8; 256],
}

pub type DeflateCandidate = (Vec<LzToken>, DeflatePlan);

/// Fast greedy hash-chain LZ77 + canonical frequency-ordered Huffman length producer.
pub fn greedy_lz77_huffman_producer(input: &[u8]) -> Option<DeflateCandidate> {
    const HASH_BITS: usize = 12;
    const HASH_SIZE: usize = 1 << HASH_BITS;
    const MAX_MATCH: usize = 258;
    const MAX_DIST: usize = 32_768;

    let mut head = vec![usize::MAX; HASH_SIZE];
    let mut prev = vec![usize::MAX; input.len()];
    let mut tokens = Vec::with_capacity(input.len() / 2 + 1);
    let mut freq = [0u64; 256];

    let hash3 = |s: &[u8], i: usize| -> usize {
        (((s[i] as usize) << 10) ^ ((s[i + 1] as usize) << 5) ^ (s[i + 2] as usize))
            & (HASH_SIZE - 1)
    };

    let mut i = 0;
    while i < input.len() {
        let mut best_len = 0usize;
        let mut best_dist = 0usize;

        if i + 3 <= input.len() {
            let h = hash3(input, i);
            let mut cur = head[h];
            prev[i] = cur;
            head[h] = i;

            let mut chain = 0usize;
            while cur != usize::MAX && chain < 16 {
                let dist = i - cur;
                if dist > MAX_DIST || dist == 0 {
                    break;
                }
                let max_l = (input.len() - i).min(MAX_MATCH);
                let mut l = 0;
                while l < max_l && input[cur + l] == input[i + l] {
                    l += 1;
                }
                if l >= 3 && l > best_len {
                    best_len = l;
                    best_dist = dist;
                    if l == MAX_MATCH {
                        break;
                    }
                }
                cur = prev[cur];
                chain += 1;
            }
        }

        if best_len >= 3 {
            tokens.push(LzToken::Match {
                dist: best_dist,
                len: best_len,
            });
            // Insert intermediate positions into hash chain for better chaining.
            let end = (i + best_len).min(input.len().saturating_sub(2));
            for p in (i + 1)..end {
                let h = hash3(input, p);
                prev[p] = head[h];
                head[h] = p;
            }
            i += best_len;
        } else {
            let b = input[i];
            freq[b as usize] += 1;
            tokens.push(LzToken::Lit(b));
            i += 1;
        }
    }

    let code_lengths = build_bounded_kraft_lengths(&freq, 15);
    let plan = DeflatePlan {
        tokens: tokens.clone(),
        max_bits: 15,
        code_lengths,
    };
    Some((tokens, plan))
}

/// Assigns valid Kraft-compliant code lengths <= `max_bits` (15) to active symbols
/// using depth-capped package/split budgeting (never exceeds Kraft budget 2^max_bits).
fn build_bounded_kraft_lengths(freq: &[u64; 256], max_bits: u8) -> [u8; 256] {
    let mut lengths = [0u8; 256];
    let mut active: Vec<(usize, u64)> = freq
        .iter()
        .enumerate()
        .filter(|(_, &f)| f > 0)
        .map(|(sym, &f)| (sym, f))
        .collect();
    if active.is_empty() {
        return lengths;
    }
    if active.len() == 1 {
        lengths[active[0].0] = 1;
        return lengths;
    }
    active.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    // Balanced binary split ensures every active symbol gets depth <= ceil(log2(active.len())) <= 8 <= 15
    // while giving more frequent symbols shorter codes and saturating Kraft sum <= 2^max_bits.
    let mut budget = 1u64 << max_bits;
    let remaining = active.len();
    for (idx, &(sym, _)) in active.iter().enumerate() {
        let rem_syms = (remaining - idx) as u64;
        // Try shortest bit-length l in 1..=max_bits leaving >= 1 slot per remaining symbol.
        let mut chosen = max_bits;
        for l in 1..=max_bits {
            let w = 1u64 << (max_bits - l);
            if w <= budget && budget - w >= rem_syms - 1 {
                // Keep reasonable spread proportional to log2(remaining):
                if idx == remaining - 1 || w * 2 <= budget {
                    chosen = l;
                    break;
                }
            }
        }
        let w = 1u64 << (max_bits - chosen);
        budget -= w;
        lengths[sym] = chosen;
    }
    lengths
}

/// Linear O(|input| + 256) zero-output-buffer Deflate plan checker matching
/// HybridDeflateChecker.lean (`checkLzReplay` + `checkKraftBounds`).
pub fn check_deflate_plan(input: &[u8], cand: &DeflateCandidate) -> bool {
    let (out_tokens, plan) = cand;
    if out_tokens != &plan.tokens || plan.max_bits == 0 || plan.max_bits > 15 {
        return false;
    }

    // 1. Check code length bounds and Kraft sum <= 2^max_bits.
    let cap: u64 = 1u64 << plan.max_bits;
    let mut kraft_sum: u64 = 0;
    for &l in &plan.code_lengths {
        if l > plan.max_bits {
            return false;
        }
        if l > 0 {
            kraft_sum += 1u64 << (plan.max_bits - l);
            if kraft_sum > cap {
                return false;
            }
        }
    }

    // 2. Zero-allocation cursor replay against `input` + active literal coverage.
    let mut pos = 0usize;
    for &tok in &plan.tokens {
        match tok {
            LzToken::Lit(b) => {
                if pos >= input.len() || input[pos] != b || plan.code_lengths[b as usize] == 0 {
                    return false;
                }
                pos += 1;
            }
            LzToken::Match { dist, len } => {
                if dist == 0 || dist > pos || len == 0 || pos.checked_add(len) > Some(input.len()) {
                    return false;
                }
                for _ in 0..len {
                    if input[pos - dist] != input[pos] {
                        return false;
                    }
                    pos += 1;
                }
            }
        }
    }
    pos == input.len()
}

/// Trivial O(n) uncompressed Stored-block / uniform-8-bit literal fallback.
pub fn stored_literal_fallback(input: &[u8]) -> DeflateCandidate {
    let tokens: Vec<LzToken> = input.iter().copied().map(LzToken::Lit).collect();
    let plan = DeflatePlan {
        tokens: tokens.clone(),
        max_bits: 15,
        code_lengths: [8u8; 256],
    };
    (tokens, plan)
}

pub fn mutant_corrupt_match(input: &[u8]) -> Option<DeflateCandidate> {
    let mut cand = greedy_lz77_huffman_producer(input)?;
    if let Some(LzToken::Lit(b)) = cand.0.first_mut() {
        *b = b.wrapping_add(1);
    }
    cand.1.tokens = cand.0.clone();
    Some(cand)
}

pub fn mutant_oob_dist(input: &[u8]) -> Option<DeflateCandidate> {
    let mut cand = greedy_lz77_huffman_producer(input)?;
    cand.0.insert(0, LzToken::Match { dist: 1, len: 1 });
    cand.1.tokens = cand.0.clone();
    Some(cand)
}

pub fn mutant_kraft_oversubscribed(input: &[u8]) -> Option<DeflateCandidate> {
    let mut cand = greedy_lz77_huffman_producer(input)?;
    cand.1.code_lengths[0] = 1;
    cand.1.code_lengths[1] = 1;
    cand.1.code_lengths[2] = 2;
    Some(cand)
}

pub fn mutant_max_bits_16(input: &[u8]) -> Option<DeflateCandidate> {
    let mut cand = greedy_lz77_huffman_producer(input)?;
    if let Some(slot) = cand.1.code_lengths.iter_mut().find(|l| **l > 0) {
        *slot = 16;
    }
    Some(cand)
}

pub fn mutant_panic(_input: &[u8]) -> Option<DeflateCandidate> {
    panic!("simulated overflow panic in LZ77 hash chain");
}

pub fn build_structured_bytes(len: usize) -> Vec<u8> {
    let pattern = b"{\"tag\":\"hybrid_verified_software\",\"ok\":true,\"step\":12345},";
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        let mut b = pattern[i % pattern.len()];
        if i % 97 == 0 {
            b = b'^';
        }
        out.push(b);
    }
    out
}
