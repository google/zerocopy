#[cfg(not(feature = "selected"))]
pub fn model_value() -> u32 { 7 }

#[cfg(feature = "selected")]
pub fn model_value() -> u32 { 11 }
