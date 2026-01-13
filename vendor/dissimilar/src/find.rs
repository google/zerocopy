// The strstr implementation in this file is extracted from the Rust standard
// library's str::find. The algorithm works for arbitrary &[T] haystack and
// needle but is only exposed by the standard library on UTF-8 strings.
//
// https://github.com/rust-lang/rust/blob/1.40.0/src/libcore/str/pattern.rs
//
// ---
//
// This is the Two-Way search algorithm, which was introduced in the paper:
// Crochemore, M., Perrin, D., 1991, Two-way string-matching, Journal of the ACM 38(3):651-675.
//
// Here's some background information.
//
// A *word* is a string of symbols. The *length* of a word should be a familiar
// notion, and here we denote it for any word x by |x|. (We also allow for the
// possibility of the *empty word*, a word of length zero.)
//
// If x is any non-empty word, then an integer p with 0 < p <= |x| is said to be
// a *period* for x iff for all i with 0 <= i <= |x| - p - 1, we have x[i] ==
// x[i+p]. For example, both 1 and 2 are periods for the string "aa". As another
// example, the only period of the string "abcd" is 4.
//
// We denote by period(x) the *smallest* period of x (provided that x is
// non-empty). This is always well-defined since every non-empty word x has at
// least one period, |x|. We sometimes call this *the period* of x.
//
// If u, v and x are words such that x = uv, where uv is the concatenation of u
// and v, then we say that (u, v) is a *factorization* of x.
//
// Let (u, v) be a factorization for a word x. Then if w is a non-empty word
// such that both of the following hold
//
//   - either w is a suffix of u or u is a suffix of w
//   - either w is a prefix of v or v is a prefix of w
//
// then w is said to be a *repetition* for the factorization (u, v).
//
// Just to unpack this, there are four possibilities here. Let w = "abc". Then
// we might have:
//
//   - w is a suffix of u and w is a prefix of v. ex: ("lolabc", "abcde")
//   - w is a suffix of u and v is a prefix of w. ex: ("lolabc", "ab")
//   - u is a suffix of w and w is a prefix of v. ex: ("bc", "abchi")
//   - u is a suffix of w and v is a prefix of w. ex: ("bc", "a")
//
// Note that the word vu is a repetition for any factorization (u,v) of x = uv,
// so every factorization has at least one repetition.
//
// If x is a string and (u, v) is a factorization for x, then a *local period*
// for (u, v) is an integer r such that there is some word w such that |w| = r
// and w is a repetition for (u, v).
//
// We denote by local_period(u, v) the smallest local period of (u, v). We
// sometimes call this *the local period* of (u, v). Provided that x = uv is
// non-empty, this is well-defined (because each non-empty word has at least one
// factorization, as noted above).
//
// It can be proven that the following is an equivalent definition of a local
// period for a factorization (u, v): any positive integer r such that x[i] ==
// x[i+r] for all i such that |u| - r <= i <= |u| - 1 and such that both x[i]
// and x[i+r] are defined. (i.e., i > 0 and i + r < |x|).
//
// Using the above reformulation, it is easy to prove that
//
//     1 <= local_period(u, v) <= period(uv)
//
// A factorization (u, v) of x such that local_period(u,v) = period(x) is called
// a *critical factorization*.
//
// The algorithm hinges on the following theorem, which is stated without proof:
//
// **Critical Factorization Theorem** Any word x has at least one critical
// factorization (u, v) such that |u| < period(x).
//
// The purpose of maximal_suffix is to find such a critical factorization.
//
// If the period is short, compute another factorization x = u' v' to use for
// reverse search, chosen instead so that |v'| < period(x).

use std::cmp;
use std::usize;

pub fn find(haystack: &[char], needle: &[char]) -> Option<usize> {
    assert!(!needle.is_empty());

    // crit_pos: critical factorization index
    let (crit_pos_false, period_false) = maximal_suffix(needle, false);
    let (crit_pos_true, period_true) = maximal_suffix(needle, true);
    let (crit_pos, mut period) = if crit_pos_false > crit_pos_true {
        (crit_pos_false, period_false)
    } else {
        (crit_pos_true, period_true)
    };

    // Byteset is an extension (not part of the two way algorithm); it is a
    // 64-bit "fingerprint" where each set bit j corresponds to a (byte & 63) ==
    // j present in the needle.
    let byteset;
    // Index into needle before which we have already matched.
    let mut memory;

    // A particularly readable explanation of what's going on here can be found
    // in Crochemore and Rytter's book "Text Algorithms", ch 13. Specifically
    // see the code for "Algorithm CP" on p. 323.
    //
    // What's going on is we have some critical factorization (u, v) of the
    // needle, and we want to determine whether u is a suffix of &v[..period].
    // If it is, we use "Algorithm CP1". Otherwise we use "Algorithm CP2", which
    // is optimized for when the period of the needle is large.
    let long_period = needle[..crit_pos] != needle[period..period + crit_pos];
    if long_period {
        // Long period case -- we have an approximation to the actual period,
        // and don't use memorization.
        //
        // Approximate the period by lower bound max(|u|, |v|) + 1.
        period = cmp::max(crit_pos, needle.len() - crit_pos) + 1;
        byteset = byteset_create(needle);
        // Dummy value to signify that the period is long.
        memory = usize::MAX;
    } else {
        // Short period case -- the period is exact.
        byteset = byteset_create(&needle[..period]);
        memory = 0;
    }

    // One of the main ideas of Two-Way is that we factorize the needle into two
    // halves, (u, v), and begin trying to find v in the haystack by scanning
    // left to right. If v matches, we try to match u by scanning right to left.
    // How far we can jump when we encounter a mismatch is all based on the fact
    // that (u, v) is a critical factorization for the needle.
    let mut position = 0;
    let needle_last = needle.len() - 1;
    'search: loop {
        // Check that we have room to search in. position + needle_last cannot
        // overflow if we assume slices are bounded by isize's range.
        let tail_byte = *haystack.get(position + needle_last)?;

        // Quickly skip by large portions unrelated to our substring.
        if !byteset_contains(byteset, tail_byte) {
            position += needle.len();
            if !long_period {
                memory = 0;
            }
            continue 'search;
        }

        // See if the right part of the needle matches.
        let start = if long_period {
            crit_pos
        } else {
            cmp::max(crit_pos, memory)
        };
        for i in start..needle.len() {
            if needle[i] != haystack[position + i] {
                position += i - crit_pos + 1;
                if !long_period {
                    memory = 0;
                }
                continue 'search;
            }
        }

        // See if the left part of the needle matches.
        let start = if long_period { 0 } else { memory };
        for i in (start..crit_pos).rev() {
            if needle[i] != haystack[position + i] {
                position += period;
                if !long_period {
                    memory = needle.len() - period;
                }
                continue 'search;
            }
        }

        // We have found a match!
        return Some(position);
    }
}

fn byteset_create(chars: &[char]) -> u64 {
    chars.iter().fold(0, |a, &ch| (1 << (ch as u8 & 0x3f)) | a)
}

fn byteset_contains(byteset: u64, ch: char) -> bool {
    (byteset >> ((ch as u8 & 0x3f) as usize)) & 1 != 0
}

// Compute the maximal suffix of `arr`.
//
// The maximal suffix is a possible critical factorization (u, v) of `arr`.
//
// Returns (`i`, `p`) where `i` is the starting index of v and `p` is the
// period of v.
//
// `order_greater` determines if lexical order is `<` or `>`. Both
// orders must be computed -- the ordering with the largest `i` gives
// a critical factorization.
//
// For long period cases, the resulting period is not exact (it is too short).
fn maximal_suffix(arr: &[char], order_greater: bool) -> (usize, usize) {
    let mut left = 0; // Corresponds to i in the paper
    let mut right = 1; // Corresponds to j in the paper
    let mut offset = 0; // Corresponds to k in the paper, but starting at 0
                        // to match 0-based indexing.
    let mut period = 1; // Corresponds to p in the paper

    while let Some(&a) = arr.get(right + offset) {
        // `left` will be inbounds when `right` is.
        let b = arr[left + offset];
        if (a < b && !order_greater) || (a > b && order_greater) {
            // Suffix is smaller, period is entire prefix so far.
            right += offset + 1;
            offset = 0;
            period = right - left;
        } else if a == b {
            // Advance through repetition of the current period.
            if offset + 1 == period {
                right += offset + 1;
                offset = 0;
            } else {
                offset += 1;
            }
        } else {
            // Suffix is larger, start over from current location.
            left = right;
            right += 1;
            offset = 0;
            period = 1;
        }
    }
    (left, period)
}
