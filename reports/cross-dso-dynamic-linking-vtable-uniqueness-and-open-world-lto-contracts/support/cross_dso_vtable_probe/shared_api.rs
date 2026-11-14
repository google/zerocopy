#![crate_name = "shared_api"]
#![crate_type = "rlib"]

pub trait SharedTrait {
    fn compute(&self, x: u64) -> u64;
    fn unused_vfe_slot(&self) -> u64 {
        0xDEAD_BEEF
    }
    fn tag_id(&self) -> u64;
}

#[repr(C)]
pub struct SharedStruct {
    pub factor: u64,
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn shared_struct_compute_canonical(factor: u64, x: u64) -> u64 {
    x.wrapping_mul(factor).wrapping_add(7)
}

impl SharedTrait for SharedStruct {
    #[inline(never)]
    fn compute(&self, x: u64) -> u64 {
        shared_struct_compute_canonical(self.factor, x)
    }

    #[inline(never)]
    fn tag_id(&self) -> u64 {
        101
    }
}

#[inline(never)]
pub fn instantiate_shared_vtable(s: &SharedStruct) -> &dyn SharedTrait {
    s as &dyn SharedTrait
}
