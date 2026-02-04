/**
 * `levenshtein-rs` - levenshtein
 *
 * MIT licensed.
 *
 * Copyright (c) 2016 Titus Wormer <tituswormer@gmail.com>
 */
#[must_use]
pub fn levenshtein(a: &str, b: &str) -> usize {
    let mut result = 0;

    /* Shortcut optimizations / degenerate cases. */
    if a == b {
        return result;
    }

    let length_a = a.chars().count();
    let length_b = b.chars().count();

    if length_a == 0 {
        return length_b;
    }

    if length_b == 0 {
        return length_a;
    }

    /* Initialize the vector.
     *
     * This is why it’s fast, normally a matrix is used,
     * here we use a single vector. */
    let mut cache: Vec<usize> = (1..).take(length_a).collect();
    let mut distance_a;
    let mut distance_b;

    /* Loop. */
    for (index_b, code_b) in b.chars().enumerate() {
        result = index_b;
        distance_a = index_b;

        for (index_a, code_a) in a.chars().enumerate() {
            distance_b = if code_a == code_b {
                distance_a
            } else {
                distance_a + 1
            };

            distance_a = cache[index_a];

            result = if distance_a > result {
                if distance_b > result {
                    result + 1
                } else {
                    distance_b
                }
            } else if distance_b > distance_a {
                distance_a + 1
            } else {
                distance_b
            };

            cache[index_a] = result;
        }
    }

    result
}
