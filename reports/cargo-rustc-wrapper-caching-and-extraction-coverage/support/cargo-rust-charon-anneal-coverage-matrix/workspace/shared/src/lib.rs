#[cfg(feature = "target-api")]
pub fn target_value() -> u32 { 11 }

#[cfg(feature = "build-api")]
pub fn build_value() -> u32 { 17 }

#[cfg(feature = "dev-api")]
pub fn dev_value() -> u32 { 23 }

#[cfg(feature = "macro-api")]
pub fn macro_value() -> u32 { 29 }
