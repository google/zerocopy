#![allow(dead_code)]

/// proof-id: movable
pub fn movable() -> u32 { 51 }

#[cfg_attr(feature = "selected", doc = "proof-id: conditional")]
#[cfg(feature = "selected")]
pub fn selected_only() -> u32 { 11 }

#[cfg(not(feature = "selected"))]
pub fn default_only() -> u32 { 12 }

pub mod left {
    /// proof-id: left-duplicate
    pub fn duplicate() -> u32 { 21 }
}

pub mod right {
    /// proof-id: right-duplicate
    pub fn duplicate() -> u32 { 22 }
}

pub trait Rule {
    /// proof-id: trait-default
    fn defaulted(&self) -> u32 { 31 }
    fn required(&self) -> u32;
}

pub struct Thing;
impl Rule for Thing {
    /// proof-id: trait-impl
    fn required(&self) -> u32 { 32 }
}

macro_rules! emit_generated {
    () => {
        /// proof-id: macro-generated
        pub fn generated() -> u32 { 41 }
    };
}
emit_generated!();

pub fn neighbor() -> u32 { 52 }

pub mod copy {
    /// proof-id: movable
    pub fn movable() -> u32 { 51 }
}

#[cfg(test)]
mod tests {
    /// proof-id: test-only
    pub fn test_subject() -> u32 { 61 }
    #[test]
    fn smoke() { assert_eq!(test_subject(), 61); }
}
