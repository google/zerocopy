// Rust cdylib specimen inspecting STV_DEFAULT vs. STV_HIDDEN symbol visibility,
// #[unsafe(no_mangle)], SymbolExportLevel::{C, Rust}, --version-script demotion
// of linked C/C++ objects, and cross-language ThinLTO internalization.

unsafe extern "C" {
    fn cpp_vis_default_fn(x: u64) -> u64;
    fn cpp_vis_hidden_fn(x: u64) -> u64;
    fn cpp_thinlto_leaf_mul_add128(a: u128, b: u128) -> u128;
}

fn rust_private_helper(x: u64) -> u64 {
    x.wrapping_mul(13).wrapping_add(3)
}

#[inline(never)]
pub fn rust_mangled_pub_api(x: u64) -> u64 {
    rust_private_helper(x) + unsafe { cpp_vis_default_fn(x) + cpp_vis_hidden_fn(x) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn rust_exported_c_unwind_api(x: u64) -> u64 {
    rust_mangled_pub_api(x)
}

#[unsafe(export_name = "rust_custom_export_api")]
#[inline(never)]
pub extern "C" fn rust_custom_export_impl(a: u64, b: u64) -> u64 {
    let v = unsafe { cpp_thinlto_leaf_mul_add128(a as u128, b as u128) };
    (v & 0xffff_ffff_ffff_ffffu128) as u64
}
