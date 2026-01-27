use crate::alphabet::{Alphabet, DecodeStep, EncodeStep};

/// PBKDF2 Base64: variant of unpadded standard Base64 with `.` instead of `+`.
///
/// ```text
/// [A-Z]      [a-z]      [0-9]      .     /
/// 0x41-0x5a, 0x61-0x7a, 0x30-0x39, 0x2e, 0x2f
/// ```
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Base64Pbkdf2;

impl Alphabet for Base64Pbkdf2 {
    const BASE: u8 = b'A';
    const DECODER: &'static [DecodeStep] = DECODER;
    const ENCODER: &'static [EncodeStep] = ENCODER;
    const PADDED: bool = false;
    type Unpadded = Self;
}

const DECODER: &[DecodeStep] = &[
    DecodeStep::Range(b'A'..=b'Z', -64),
    DecodeStep::Range(b'a'..=b'z', -70),
    DecodeStep::Range(b'0'..=b'9', 5),
    DecodeStep::Eq(b'.', 63),
    DecodeStep::Eq(b'/', 64),
];

const ENCODER: &[EncodeStep] = &[
    EncodeStep::Diff(25, 6),
    EncodeStep::Diff(51, -75),
    EncodeStep::Diff(61, -(b'.' as i16 - 0x22)),
    EncodeStep::Diff(62, b'/' as i16 - b'.' as i16 - 1),
];
