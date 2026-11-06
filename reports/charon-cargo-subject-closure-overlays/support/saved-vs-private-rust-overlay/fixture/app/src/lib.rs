#![allow(dead_code)]
use proc_local::emit_generated;
include!(concat!(env!("OUT_DIR"), "/generated.rs"));
emit_generated!();

pub fn root(x: u32) -> u32 {
    dep_path::dep(x)
        .wrapping_add(BUILD_SUBJECT)
        .wrapping_add(include_str!("payload.txt").len() as u32)
        .wrapping_add(env!("PROBE_ENV").len() as u32)
        .wrapping_add(macro_generated(x))
}
