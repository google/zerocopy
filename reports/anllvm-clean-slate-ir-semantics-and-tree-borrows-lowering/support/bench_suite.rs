
#![no_std]
#![allow(dead_code)]

// 1. Slice iteration and summation with predicate clamping
#[inline]
fn scale_and_clamp(x: u64, factor: u64, cap: u64) -> u64 {
    let prod = x.wrapping_mul(factor);
    if prod > cap { cap } else { prod }
}

#[no_mangle]
pub fn bench_slice_sum(slice: &[u64], factor: u64, cap: u64) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < slice.len() {
        let v = slice[i];
        let scaled = scale_and_clamp(v, factor, cap);
        acc = acc.wrapping_add(scaled);
        i += 1;
    }
    acc
}

// 2. Struct / Enum protocol state-machine transitions
#[derive(Copy, Clone)]
pub enum ProtoState {
    Idle,
    Header { magic: u32, remaining: u32 },
    Payload { checksum: u32, count: u32 },
    Done { final_crc: u32 },
    Error(u32),
}

#[derive(Copy, Clone)]
pub struct PacketCtx {
    pub state: ProtoState,
    pub total_bytes: u32,
    pub flags: u32,
}

#[inline]
fn step_machine(mut ctx: PacketCtx, word: u32) -> PacketCtx {
    ctx.total_bytes = ctx.total_bytes.wrapping_add(4);
    ctx.state = match ctx.state {
        ProtoState::Idle => {
            if word == 0x5255_5354 {
                ProtoState::Header { magic: word, remaining: 2 }
            } else {
                ProtoState::Error(1)
            }
        }
        ProtoState::Header { magic, remaining } => {
            if remaining <= 1 {
                ProtoState::Payload { checksum: magic ^ word, count: (word & 0x3) + 1 }
            } else {
                ProtoState::Header { magic: magic.wrapping_add(word), remaining: remaining - 1 }
            }
        }
        ProtoState::Payload { checksum, count } => {
            let next_csum = checksum.rotate_left(5) ^ word;
            if count <= 1 {
                ProtoState::Done { final_crc: next_csum }
            } else {
                ProtoState::Payload { checksum: next_csum, count: count - 1 }
            }
        }
        ProtoState::Done { final_crc } => ProtoState::Done { final_crc },
        ProtoState::Error(code) => ProtoState::Error(code),
    };
    ctx
}

#[no_mangle]
pub fn bench_state_machine(w0: u32, w1: u32, w2: u32, w3: u32) -> u32 {
    let mut ctx = PacketCtx {
        state: ProtoState::Idle,
        total_bytes: 0,
        flags: 0x01,
    };
    ctx = step_machine(ctx, w0);
    ctx = step_machine(ctx, w1);
    ctx = step_machine(ctx, w2);
    ctx = step_machine(ctx, w3);
    match ctx.state {
        ProtoState::Done { final_crc } => final_crc ^ ctx.total_bytes,
        ProtoState::Payload { checksum, count } => checksum ^ count ^ ctx.total_bytes,
        ProtoState::Header { magic, remaining } => magic ^ remaining,
        ProtoState::Idle => 0,
        ProtoState::Error(e) => e | 0x8000_0000,
    }
}

// 3. Binary search and bounds-checked array indexing
#[no_mangle]
pub fn bench_binary_search(arr: &[u64], target: u64) -> usize {
    if arr.is_empty() {
        return usize::MAX;
    }
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    while low < high {
        let mid = low + ((high - low) >> 1);
        if mid >= arr.len() {
            break;
        }
        let mid_val = arr[mid];
        if mid_val < target {
            low = mid + 1;
        } else if mid_val > target {
            high = mid;
        } else {
            return mid;
        }
    }
    usize::MAX
}

// 4. Bit-manipulation, demanded-bits masking, and rolling checksum
#[inline]
fn mix_lanes(a: u64, b: u64) -> u64 {
    let x = a.wrapping_add(0).wrapping_mul(1);
    let hi_noise = (b | 0xffff_0000_0000_0000) & 0x0000_ffff_ffff_ffff;
    let rotated = (x ^ hi_noise).rotate_left(13);
    (rotated | 0xffff_ffff_0000_0000) & 0x0000_0000_ffff_ffff
}

#[no_mangle]
pub fn bench_checksum_bits(data: &[u64], seed: u64) -> u32 {
    let mut s1: u64 = seed & 0xffff;
    let mut s2: u64 = (seed >> 16) & 0xffff;
    let mut idx: usize = 0;
    while idx < data.len() {
        let word = data[idx];
        let mixed = mix_lanes(word, s1);
        s1 = (s1.wrapping_add(mixed)) & 0xffff;
        s2 = (s2.wrapping_add(s1)) & 0xffff;
        idx += 1;
    }
    ((s2 << 16) | s1) as u32
}

// 5. Option / Result combinator chains
#[inline]
fn parse_header_byte(b: u8) -> Option<u32> {
    if b >= b'0' && b <= b'9' {
        Some((b - b'0') as u32)
    } else if b >= b'a' && b <= b'f' {
        Some(10 + (b - b'a') as u32)
    } else {
        None
    }
}

#[inline]
fn validate_non_zero(v: u32) -> Result<u32, u32> {
    if v == 0 {
        Err(0xff)
    } else {
        Ok(v.wrapping_mul(16))
    }
}

#[no_mangle]
pub fn bench_option_result_chain(b0: u8, b1: u8, b2: u8, fallback: u32) -> u32 {
    let r0 = parse_header_byte(b0)
        .map(|x| x.wrapping_add(1))
        .ok_or(10u32)
        .and_then(validate_non_zero);
    let r1 = parse_header_byte(b1)
        .and_then(|y| parse_header_byte(b2).map(|z| y.wrapping_mul(16).wrapping_add(z)))
        .ok_or(20u32);
    match (r0, r1) {
        (Ok(v0), Ok(v1)) => v0.wrapping_add(v1),
        (Ok(v0), Err(e1)) => v0 ^ e1,
        (Err(e0), Ok(v1)) => v1 ^ e0,
        (Err(_), Err(_)) => fallback,
    }
}

// 6. Matrix/vector loop with loop-invariant load/compute, SCEV affine recurrence,
// dead scratch store (DSE), and dead diagnostic loop (LoopDeletion)
#[no_mangle]
pub fn bench_matrix_vec_loop(
    mat: &[u64],
    vec: &[u64],
    cfg_scale: &u64,
    out: &mut [u64],
    rows: usize,
    cols: usize,
) -> u64 {
    // Dead diagnostic loop (purely local counter, unused after loop -> LoopDeletion target)
    let mut diag: usize = 0;
    let mut k: usize = 0;
    while k < rows {
        diag = diag.wrapping_add(k ^ 0x5a5a);
        k += 1;
    }

    let mut total_checksum: u64 = 0;
    let mut r: usize = 0;
    while r < rows {
        let mut dot: u64 = 0;
        let mut c: usize = 0;
        let out_ptr = unsafe { out.as_mut_ptr().add(r) };
        let hdr_scale = *cfg_scale;
        while c < cols {
            // Redundant load (*cfg_scale) + loop-invariant compute + SCEV affine index (r * cols + c)
            let scale = (*cfg_scale).wrapping_add(hdr_scale).wrapping_add(1);
            let mat_idx = r.wrapping_mul(cols).wrapping_add(c);
            let m_val = unsafe { *mat.as_ptr().add(mat_idx) };
            let v_val = unsafe { *vec.as_ptr().add(c) };
            dot = dot.wrapping_add(m_val.wrapping_mul(v_val).wrapping_mul(scale));
            c += 1;
        }
        // Overwritten store to *out_ptr (DSE target)
        unsafe {
            *out_ptr = dot.wrapping_add(1);
            *out_ptr = dot;
        }
        total_checksum = total_checksum.wrapping_add(dot);
        r += 1;
    }
    total_checksum
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
