#![allow(unused)]

#[no_mangle]
#[inline(never)]
pub fn ackermann(m: u64, n: u64) -> u64 {
    if m == 0 {
        n + 1
    } else if n == 0 {
        ackermann(m - 1, 1)
    } else {
        ackermann(m - 1, ackermann(m, n - 1))
    }
}

#[no_mangle]
#[inline(never)]
pub fn fib_tree_with_locals(n: u64, acc: [u64; 4]) -> u64 {
    if n <= 1 {
        return n + acc[0] + acc[3];
    }
    let next = [acc[0].wrapping_add(n), acc[1] ^ n, acc[2].wrapping_mul(3), acc[3].wrapping_sub(1)];
    std::hint::black_box(&next);
    fib_tree_with_locals(n - 1, next).wrapping_add(fib_tree_with_locals(n - 2, next))
}

#[no_mangle]
#[inline(never)]
pub fn crc32c_step(acc: u32, data: *const u8, len: usize) -> u32 {
    if data.is_null() { return acc; }
    let mut crc = !acc;
    let mut i = 0usize;
    while i < len {
        let byte = unsafe { *data.add(i) };
        crc ^= byte as u32;
        let mut bit = 0;
        while bit < 8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0x82F63B78u32 & mask);
            bit += 1;
        }
        i += 1;
    }
    !crc
}

#[no_mangle]
#[inline(never)]
pub fn recursive_parser_step(depth: usize, input: &[u8]) -> Result<u64, u32> {
    if depth == 0 || input.is_empty() {
        return Ok(input.len() as u64);
    }
    let mut scratch = [0u64; 16];
    for (i, &b) in input.iter().take(16).enumerate() {
        scratch[i] = (b as u64).wrapping_mul(depth as u64);
    }
    std::hint::black_box(&mut scratch);
    let sub = recursive_parser_step(depth - 1, &input[1..])?;
    Ok(sub.wrapping_add(scratch[depth & 15]))
}

#[no_mangle]
#[inline(never)]
pub fn format_and_drop_frame(x: u64, y: u64) -> usize {
    let s = format!("val={x}:{y}");
    std::hint::black_box(s.len())
}
