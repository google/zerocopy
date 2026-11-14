#![crate_name = "plugin_dylib"]
#![crate_type = "cdylib"]

extern crate shared_api;
use shared_api::{SharedStruct, SharedTrait};

#[repr(C)]
pub struct PluginPrivateStruct {
    pub bias: u64,
}

impl SharedTrait for PluginPrivateStruct {
    #[inline(never)]
    fn compute(&self, x: u64) -> u64 {
        x.wrapping_add(self.bias).wrapping_mul(3)
    }

    #[inline(never)]
    fn tag_id(&self) -> u64 {
        202
    }
}

static PLUGIN_SHARED_INSTANCE: SharedStruct = SharedStruct { factor: 10 };
static PLUGIN_PRIVATE_INSTANCE: PluginPrivateStruct = PluginPrivateStruct { bias: 100 };

#[repr(C)]
pub struct RawTraitObject {
    pub data_ptr: *const (),
    pub vtable_ptr: *const usize,
}

#[no_mangle]
pub extern "C" fn plugin_get_shared_struct_trait_obj() -> RawTraitObject {
    let fat: &dyn SharedTrait = &PLUGIN_SHARED_INSTANCE;
    unsafe { std::mem::transmute(fat) }
}

#[no_mangle]
pub extern "C" fn plugin_get_private_struct_trait_obj() -> RawTraitObject {
    let fat: &dyn SharedTrait = &PLUGIN_PRIVATE_INSTANCE;
    unsafe { std::mem::transmute(fat) }
}
