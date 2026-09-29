#![allow(dead_code)]
/// source marker: alpha
pub fn alpha(x: u32) -> u32 { x.wrapping_add(1) }
/// source marker: beta
pub fn beta(x: u32) -> u32 { x.wrapping_mul(2) }
#[cfg(feature = "selected")]
pub fn feature_only(x: u32) -> u32 { x.wrapping_add(17) }
#[cfg(not(feature = "selected"))]
pub fn default_only(x: u32) -> u32 { x.wrapping_add(13) }
