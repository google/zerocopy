#![allow(unexpected_cfgs)]

#[cfg(debug_assertions)]
pub fn profile_value() -> u32 { 7 }

#[cfg(not(debug_assertions))]
pub fn profile_value() -> u32 { 11 }

#[cfg(probe_alt)]
pub fn config_value() -> u32 { 29 }

#[cfg(not(probe_alt))]
pub fn config_value() -> u32 { 23 }
