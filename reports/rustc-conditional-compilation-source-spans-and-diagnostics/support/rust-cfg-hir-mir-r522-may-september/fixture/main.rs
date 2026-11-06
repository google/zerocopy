#![allow(dead_code)]

#[cfg(feature = "a")]
pub fn feature_a_only() -> u32 { 10 }

#[cfg(not(feature = "a"))]
pub fn feature_off_only() -> u32 { 20 }

#[cfg(custom_from_build)]
pub fn custom_cfg_only() -> u32 { 30 }

#[cfg(not(custom_from_build))]
pub fn no_custom_cfg_only() -> u32 { 40 }

#[cfg_attr(feature = "a", path = "selected_a.rs")]
#[cfg_attr(not(feature = "a"), path = "selected_b.rs")]
pub mod selected;

macro_rules! emit_cfg_item {
    () => {
        #[cfg(feature = "a")]
        pub fn macro_a_only() -> u32 { 50 }
        #[cfg(not(feature = "a"))]
        pub fn macro_off_only() -> u32 { 60 }
    };
}
emit_cfg_item!();

pub fn cfg_control() -> u32 {
    if cfg!(feature = "a") { 70 } else { 80 }
}

pub fn selected_value() -> u32 {
    selected::value()
}
