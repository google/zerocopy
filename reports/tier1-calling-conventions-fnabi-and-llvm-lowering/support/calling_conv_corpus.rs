#![no_std]
#![allow(improper_ctypes_definitions, internal_features)]
#![feature(abi_vectorcall, f16, f128, repr_simd, rust_cold_cc, rustc_attrs, unboxed_closures)]

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ReprCZst;

#[derive(Copy, Clone)]
pub struct RustZst;

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct TransU32(RustZst, pub u32);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct SmallInt8 { pub a: u32, pub b: u32 }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Pair16 { pub a: u64, pub b: u64 }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct MixedIntFloat16 { pub a: u64, pub b: f64 }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Triple24 { pub a: u64, pub b: u64, pub c: u64 }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Hfa2F32 { pub x: f32, pub y: f32 }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Hfa4F32 { pub x: f32, pub y: f32, pub z: f32, pub w: f32 }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Hfa5F32 { pub a: f32, pub b: f32, pub c: f32, pub d: f32, pub e: f32 }

#[repr(C, align(16))]
#[derive(Copy, Clone)]
pub struct Overaligned16 { pub a: u64, pub b: u64 }

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct Vec4F32([f32; 4]);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Hva2V128 { pub v0: Vec4F32, pub v1: Vec4F32 }

// 1. Narrow integer extension (DarwinPCS vs SysV/Win64/AAPCS64)
#[no_mangle] pub extern "C" fn cc_narrow_int(a: i8, b: u8, c: i16, d: u16) -> i8 { a.wrapping_add(b as i8).wrapping_add(c as i8).wrapping_add(d as i8) }

// 2. ZST (repr(C) ZST on Win64 vs SysV/AAPCS64) and repr(transparent)
#[no_mangle] pub extern "C" fn cc_zst_and_transparent(z1: ReprCZst, t: TransU32, z2: ReprCZst) -> TransU32 { let _ = (z1, z2); TransU32(RustZst, t.1 + 1) }

// 3. 8-byte struct
#[no_mangle] pub extern "C" fn cc_struct_8b(s: SmallInt8) -> SmallInt8 { SmallInt8 { a: s.b, b: s.a } }

// 4. 16-byte integer struct (Pair16)
#[no_mangle] pub extern "C" fn cc_struct_16b(s: Pair16) -> Pair16 { Pair16 { a: s.b, b: s.a } }

// 5. 16-byte mixed int+float struct (SysV RDI+XMM0 vs AAPCS64 X0+X1 vs Win64 indirect)
#[no_mangle] pub extern "C" fn cc_mixed_16b(s: MixedIntFloat16) -> MixedIntFloat16 { MixedIntFloat16 { a: s.a + 1, b: s.b } }

// 6. 24-byte struct (sret + indirect/byval)
#[no_mangle] pub extern "C" fn cc_struct_24b(s: Triple24) -> Triple24 { Triple24 { a: s.c, b: s.b, c: s.a } }

// 7. Homogeneous Floating-Point Aggregates (HFA2, HFA4, HFA5)
#[no_mangle] pub extern "C" fn cc_hfa2_f32(h: Hfa2F32) -> Hfa2F32 { Hfa2F32 { x: h.y, y: h.x } }
#[no_mangle] pub extern "C" fn cc_hfa4_f32(h: Hfa4F32) -> Hfa4F32 { Hfa4F32 { x: h.w, y: h.z, z: h.y, w: h.x } }
#[no_mangle] pub extern "C" fn cc_hfa5_f32(h: Hfa5F32) -> Hfa5F32 { Hfa5F32 { a: h.e, b: h.b, c: h.c, d: h.d, e: h.a } }

// 8. Overaligned 16-byte struct (even-odd X2/X3 alignment on DarwinPCS vs unadjusted on AAPCS64; indirect on i686 MSVC)
#[no_mangle] pub extern "C" fn cc_overaligned_16b(dummy: u32, s: Overaligned16) -> u64 { (dummy as u64).wrapping_add(s.a).wrapping_add(s.b) }

// 9. 128-bit integer (i128/u128)
#[no_mangle] pub extern "C" fn cc_u128(dummy: u32, x: u128) -> u128 { x.wrapping_add(dummy as u128) }

// 10. f16 and f128
#[cfg(not(all(target_arch = "x86_64", target_os = "windows", target_env = "gnu")))]
#[no_mangle] pub extern "C" fn cc_f16_f128(a: f16, b: f128) -> f128 { let _ = a; b }

// 11. 128-bit SIMD vector and HVA on C ABI vs Rust ABI
#[no_mangle] pub extern "C" fn cc_vec128_c(v: Vec4F32) -> Vec4F32 { v }
#[no_mangle] pub extern "C" fn cc_hva2_c(h: Hva2V128) -> Hva2V128 { Hva2V128 { v0: h.v1, v1: h.v0 } }
#[no_mangle] pub fn cc_vec128_rust(v: Vec4F32) -> Vec4F32 { v }

// 12. Rust ABI: ScalarPair, &[u8], Triple24, f32 return
#[no_mangle] pub fn cc_rust_pair(p: (u64, u64)) -> (u64, u64) { (p.1, p.0) }
#[no_mangle] pub fn cc_rust_slice(s: &[u8]) -> usize { s.len() }
#[no_mangle] pub fn cc_rust_triple(t: Triple24) -> Triple24 { Triple24 { a: t.c, b: t.b, c: t.a } }
#[no_mangle] pub fn cc_rust_f32(x: f32, y: f32) -> f32 { x + y }

// 13. #[track_caller], rust-call, rust-cold, C-unwind
#[no_mangle] #[track_caller] pub fn cc_track_caller(x: u32) -> &'static core::panic::Location<'static> { let _ = x; core::panic::Location::caller() }
#[no_mangle] pub extern "rust-call" fn cc_rust_call(args: (usize, u32, u64)) -> u64 { (args.0 as u64).wrapping_add(args.1 as u64).wrapping_add(args.2) }
#[cfg(not(target_arch = "x86"))]
#[no_mangle] pub extern "rust-cold" fn cc_rust_cold_void(p: *mut u32, x: u32) { unsafe { *p = x; } }
#[cfg(not(target_arch = "x86"))]
#[no_mangle] pub extern "rust-cold" fn cc_rust_cold_ret(a: u64, b: u64) -> u64 { a.wrapping_add(b) }
#[no_mangle] #[rustc_nounwind] pub extern "C" fn cc_c_nounwind(x: u32) -> u32 { x + 1 }
#[no_mangle] pub extern "C-unwind" fn cc_c_unwind(f: extern "C-unwind" fn(u32) -> u32, x: u32) -> u32 { f(x) + 1 }

// 14. Register exhaustion & stack spill (9 integer + 9 float args)
#[no_mangle] pub extern "C" fn cc_many_args(
    i0: u64, _i1: u64, _i2: u64, _i3: u64, _i4: u64, _i5: u64, _i6: u64, i7: u64, i8: u64,
    f0: f64, f1: f64, f2: f64, f3: f64, f4: f64, f5: f64, f6: f64, f7: f64, f8: f64,
) -> u64 {
    i0.wrapping_add(i7).wrapping_add(i8).wrapping_add(f8 as u64).wrapping_add((f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7) as u64)
}

// 15. C-variadic caller
#[no_mangle] pub unsafe extern "C" fn cc_variadic_caller(
    sink: unsafe extern "C" fn(u32, i8, i8, i8, ...) -> u32,
    a: u32, b: f64, c: i8,
) -> u32 {
    sink(a, 1, 2, 3, b, c as i32)
}

// 16. Target-specific ABIs (sysv64, win64, vectorcall on x86_64; fastcall, stdcall, thiscall, vectorcall on x86)
#[cfg(target_arch = "x86_64")]
#[no_mangle] pub extern "sysv64" fn cc_explicit_sysv64(a: u64, b: u64, s: Pair16) -> Pair16 { Pair16 { a: a.wrapping_add(s.a), b: b.wrapping_add(s.b) } }

#[cfg(target_arch = "x86_64")]
#[no_mangle] pub extern "win64" fn cc_explicit_win64(a: u64, b: u64, s: Pair16) -> Pair16 { Pair16 { a: a.wrapping_add(s.a), b: b.wrapping_add(s.b) } }

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
#[no_mangle] pub extern "vectorcall" fn cc_vectorcall(a: u32, b: u32, v0: Vec4F32, h: Hfa4F32) -> Hfa4F32 { let _ = (a, b, v0); h }

#[cfg(target_arch = "x86")]
#[no_mangle] pub extern "fastcall" fn cc_x86_fastcall(a: u32, b: u32, c: u32) -> u32 { a.wrapping_add(b).wrapping_add(c) }

#[cfg(target_arch = "x86")]
#[no_mangle] pub extern "stdcall" fn cc_x86_stdcall(a: u32, b: u32, c: u32) -> u32 { a.wrapping_add(b).wrapping_add(c) }

#[cfg(target_arch = "x86")]
#[no_mangle] pub extern "thiscall" fn cc_x86_thiscall(this: *const u32, a: u32, b: u32) -> u32 { (this as u32).wrapping_add(a).wrapping_add(b) }

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
