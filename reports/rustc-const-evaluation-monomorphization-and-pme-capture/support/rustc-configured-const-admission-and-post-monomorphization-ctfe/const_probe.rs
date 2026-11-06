pub struct RequireNonZero<const N: usize>;
impl<const N: usize> RequireNonZero<N> {
    pub const VALID: usize = 1 / N;
}

pub fn checked_kernel<const N: usize>(x: u32) -> u32 {
    let _ = RequireNonZero::<N>::VALID;
    x.wrapping_add(N as u32)
}

pub fn unused_zero_mention(x: u32) -> u32 {
    if false {
        let _ = core::mem::size_of::<RequireNonZero<0>>();
    }
    x
}

#[cfg(case_ok)]
pub fn entry_point(x: u32) -> u32 {
    checked_kernel::<4>(x)
}

#[cfg(case_fail_reachable)]
pub fn entry_point(x: u32) -> u32 {
    checked_kernel::<0>(x)
}
