#[cfg_attr(feature = "alternate", path = "alternate.rs")]
#[cfg_attr(not(feature = "alternate"), path = "default.rs")]
mod selected;

pub fn read() -> u32 { selected::marker() }
