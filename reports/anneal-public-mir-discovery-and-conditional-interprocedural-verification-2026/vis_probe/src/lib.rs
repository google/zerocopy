// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]

// =============================================================================
// Category 1: Top-level `pub fn` vs. private `fn` vs. `pub(crate) fn`
// =============================================================================

pub fn cat1_top_pub(x: u32) -> u32 {
    x
}

fn cat1_top_priv(x: u32) -> u32 {
    x
}

pub(crate) fn cat1_top_pub_crate(x: u32) -> u32 {
    x
}

// =============================================================================
// Category 2: `pub fn` inside a private module (unexported vs. re-exported)
// =============================================================================

mod priv_mod {
    pub fn cat2_priv_mod_unexported(x: u32) -> u32 {
        x
    }

    pub fn cat2_priv_mod_reexported(x: u32) -> u32 {
        x
    }
}

pub use priv_mod::cat2_priv_mod_reexported;

// =============================================================================
// Category 3: Inherent impl methods on `pub struct` vs. private `struct`
// =============================================================================

pub struct PubStruct(pub u32);

impl PubStruct {
    pub fn cat3_pub_struct_inh_pub(&self) -> u32 {
        self.0
    }

    pub(crate) fn cat3_pub_struct_inh_pub_crate(&self) -> u32 {
        self.0
    }

    fn cat3_pub_struct_inh_priv(&self) -> u32 {
        self.0
    }
}

struct PrivStruct(pub u32);

impl PrivStruct {
    pub fn cat3_priv_struct_inh_pub(&self) -> u32 {
        self.0
    }

    fn cat3_priv_struct_inh_priv(&self) -> u32 {
        self.0
    }
}

// Private struct that is reachable through a public type alias (`pub type`)
// (triggers `private_interfaces` warning, `Level::Reachable` for type)
struct ReachablePrivStruct(pub u32);

impl ReachablePrivStruct {
    pub fn cat3_reachable_priv_struct_inh_pub(&self) -> u32 {
        self.0
    }

    fn cat3_reachable_priv_struct_inh_priv(&self) -> u32 {
        self.0
    }
}

pub type PublicAliasToPrivStruct = ReachablePrivStruct;

// `pub struct` inside a private module, leaked through a `pub fn` return type
// ("nameable-in-interface, unnameable-by-path" type, `Level::Reachable = Pub`)
mod priv_mod_type {
    pub struct PubInPrivMod(pub u32);

    impl PubInPrivMod {
        pub fn cat3_pub_in_priv_mod_inh_pub(&self) -> u32 {
            self.0
        }

        fn cat3_pub_in_priv_mod_inh_priv(&self) -> u32 {
            self.0
        }
    }
}

pub fn cat3_leak_pub_in_priv_mod(x: u32) -> priv_mod_type::PubInPrivMod {
    priv_mod_type::PubInPrivMod(x)
}

// =============================================================================
// Category 4: Trait implementation methods and default trait methods
// =============================================================================

pub trait PubTrait {
    fn cat4_trait_req(&self) -> u32;

    fn cat4_trait_default(&self) -> u32 {
        42
    }
}

// 4a: `impl PublicTrait for PublicStruct`
impl PubTrait for PubStruct {
    fn cat4_trait_req(&self) -> u32 {
        self.0
    }
}

// 4b: `impl PublicTrait for PrivateStruct` when returned via RPIT (`impl PubTrait`)
struct RpitPrivStruct(u32);

impl PubTrait for RpitPrivStruct {
    fn cat4_trait_req(&self) -> u32 {
        self.0
    }
}

impl RpitPrivStruct {
    pub fn cat4_rpit_priv_struct_inh_pub(&self) -> u32 {
        self.0
    }
}

pub fn cat4_return_rpit(x: u32) -> impl PubTrait {
    RpitPrivStruct(x)
}

// Private function returning `impl PubTrait` (tests `rustc_privacy` RPIT over-approximation)
struct PrivFnRpitStruct(u32);

impl PubTrait for PrivFnRpitStruct {
    fn cat4_trait_req(&self) -> u32 {
        self.0
    }
}

fn cat4_priv_return_rpit(x: u32) -> impl PubTrait {
    PrivFnRpitStruct(x)
}

// 4c: `impl PublicTrait for PrivateStruct` when returned via `&'static dyn PubTrait`
struct DynPrivStruct(u32);

impl PubTrait for DynPrivStruct {
    fn cat4_trait_req(&self) -> u32 {
        self.0
    }
}

static DYN_PRIV: DynPrivStruct = DynPrivStruct(7);

pub fn cat4_return_dyn() -> &'static dyn PubTrait {
    &DYN_PRIV
}

// 4d: `impl PublicTrait for UnexportedPrivStruct` (never leaked via RPIT or dyn)
struct UnexportedPrivStruct(u32);

impl PubTrait for UnexportedPrivStruct {
    fn cat4_trait_req(&self) -> u32 {
        self.0
    }
}

// 4e: `impl PrivateTrait for PublicStruct`
trait PrivTrait {
    fn cat4_priv_trait_req(&self) -> u32;
    fn cat4_priv_trait_default(&self) -> u32 {
        99
    }
}

impl PrivTrait for PubStruct {
    fn cat4_priv_trait_req(&self) -> u32 {
        self.0
    }
}

// =============================================================================
// Category 5: Generic functions (uninstantiated vs. locally instantiated)
// =============================================================================

pub fn cat5_generic_pub_uninstantiated<T>(x: T) -> T {
    x
}

pub fn cat5_generic_pub_instantiated<T>(x: T) -> T {
    x
}

fn cat5_generic_priv_uninstantiated<T>(x: T) -> T {
    x
}

pub fn cat5_caller_of_generic(x: u32) -> u32 {
    cat5_generic_pub_instantiated(x)
}

fn cat5_priv_helper_called_by_generic(x: u32) -> u32 {
    x
}

pub fn cat5_generic_calling_priv_helper<T>(x: u32, _t: T) -> u32 {
    cat5_priv_helper_called_by_generic(x)
}

// =============================================================================
// Category 6: FFI / binary roots (`#[no_mangle]`, `#[export_name]`, `fn main`)
// =============================================================================

#[no_mangle]
fn cat6_ffi_no_mangle(x: u32) -> u32 {
    x
}

#[export_name = "cat6_custom_export_symbol"]
fn cat6_ffi_export_name(x: u32) -> u32 {
    x
}

pub fn main() {
    let _ = cat1_top_priv(1);
}

// =============================================================================
// Category 7: Closures (returned by `pub fn`, returned by private `fn`, local)
// =============================================================================

pub fn cat7_make_adder_pub(x: usize) -> impl Fn(usize) -> usize {
    move |y| x + y
}

fn cat7_make_adder_priv(x: usize) -> impl Fn(usize) -> usize {
    move |y| x + y
}

pub fn cat7_internal_closure_only(x: usize) -> usize {
    let f = |y: usize| x + y;
    f(1)
}
