#[repr(C)]
pub struct InputWords {
    pub payload: u32,
    pub spare: u32,
}

#[repr(C)]
pub struct MaskWords {
    pub bits: u32,
    pub fallback: u32,
}

mod internal {
    #[inline(never)]
    pub fn select(input: super::InputWords, mask: super::MaskWords, flag: bool) -> u32 {
        if flag { input.payload & mask.bits } else { input.spare }
    }
}

#[inline(never)]
pub fn evaluate(x: u32, flag: bool) -> u32 {
    let input = InputWords { payload: x, spare: 9 };
    let mask = MaskWords { bits: 31, fallback: 15 };
    internal::select(input, mask, flag)
}
