#![allow(dead_code)]
include!(concat!(env!("OUT_DIR"), "/generated.rs"));
/// proof-id: A
pub fn step(x: u32) -> u32 { x.wrapping_add(1) }
pub fn use_step(x: u32) -> u32 { step(x).wrapping_add(dep_path::delta(x)) }
pub fn payload_len() -> usize { include_str!("payload.txt").len() }
pub fn generated_value() -> u32 { SNAPSHOT_VALUE }
