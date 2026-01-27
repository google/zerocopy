//! Contains `compute_frequency`, a function
//! that uses a rolling Karp-Rabin hash to
//! efficiently count the number of occurences
//! of a given k-mer within a set.

/// Computes a best effort guess as to how many times `pattern` occurs within
/// `body`. While not 100% accurate, it will be accurate the vast majority of time
pub fn estimate_frequency(pattern: &[u8], body: &[u8]) -> usize {
    assert!(body.len() >= pattern.len());
    // A prime number for modulo operations to reduce collisions (q)
    const PRIME: isize = 2654435761;
    // Number of characters in the input alphabet (d)
    const ALPHABET_SIZE: isize = 256;
    // Hash of input pattern (p)
    let mut pattern_hash: isize = 0;
    // Hash of the current window of text (t)
    let mut window_hash: isize = 0;
    // High-order digit multiplier (h)
    let mut h: isize = 1;

    // Precompute h (?)
    h = (h * ALPHABET_SIZE) % PRIME;

    // Compute initial hash values
    for i in 0..pattern.len() {
        pattern_hash = (ALPHABET_SIZE * pattern_hash + pattern[i] as isize) % PRIME;
        window_hash = (ALPHABET_SIZE * window_hash + body[i] as isize) % PRIME;
    }

    let mut num_occurances = 0;
    for i in 0..=body.len() - pattern.len() {
        // There's *probably* a match if these two match
        if pattern_hash == window_hash {
            num_occurances += 1;
        }

        // Compute hash values for next window
        if i < body.len() - pattern.len() {
            window_hash = (ALPHABET_SIZE * (window_hash - body[i] as isize * h)
                + body[i + pattern.len()] as isize)
                % PRIME;
        }
    }

    num_occurances
}

#[cfg(test)]
mod tests {
    use super::estimate_frequency;
    #[test]
    fn dead_beef() {
        assert_eq!(
            estimate_frequency(&[0xde, 0xad], &[0xde, 0xad, 0xbe, 0xef, 0xde, 0xad]),
            2
        );
    }

    #[test]
    fn smallest_body() {
        assert_eq!(estimate_frequency(&[0x00, 0xff], &[0x00, 0xff]), 1);
    }

    #[test]
    fn no_match() {
        assert_eq!(
            estimate_frequency(&[0xff, 0xff], &[0xde, 0xad, 0xbe, 0xef, 0xde, 0xad]),
            0
        );
    }
}
