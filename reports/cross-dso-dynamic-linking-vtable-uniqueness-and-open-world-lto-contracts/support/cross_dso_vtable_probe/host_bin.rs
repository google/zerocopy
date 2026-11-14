#![crate_name = "host_bin"]

extern crate shared_api;
use shared_api::{SharedStruct, SharedTrait};
use std::ffi::CString;
use std::hint::black_box;
use std::time::Instant;

#[repr(C)]
#[derive(Copy, Clone)]
pub struct RawTraitObject {
    pub data_ptr: *const (),
    pub vtable_ptr: *const usize,
}

// Crate-private trait: never exported in ExportList or FFI signatures.
trait HostPrivateTrait {
    fn eval_private(&self, x: u64) -> u64;
}

struct HostInternalWorker {
    pub k: u64,
}

impl HostPrivateTrait for HostInternalWorker {
    #[inline(always)]
    fn eval_private(&self, x: u64) -> u64 {
        x.wrapping_mul(self.k).wrapping_add(13)
    }
}

extern "C" {
    fn dlopen(filename: *const i8, flags: i32) -> *mut ();
    fn dlsym(handle: *mut (), symbol: *const i8) -> *mut ();
}

const RTLD_NOW: i32 = 2;

static HOST_SHARED_INSTANCE: SharedStruct = SharedStruct { factor: 10 };

// In Rust 1.99.1 vtable layout for `SharedTrait`:
// slot 0: drop_in_place
// slot 1: size
// slot 2: align
// slot 3: compute(&self, u64) -> u64
// slot 4: unused_vfe_slot(&self) -> u64
// slot 5: tag_id(&self) -> u64
const SLOT_COMPUTE: usize = 3;

#[inline(never)]
fn dispatch_indirect(fat: &dyn SharedTrait, x: u64) -> u64 {
    fat.compute(x)
}

// Mode A: Unguarded WPO-DevirtSingleImpl (UNSOUND on OpenExportedTrait!)
// Assumes every `&dyn SharedTrait` is `SharedStruct` without checking `vtable_ptr`.
#[inline(never)]
unsafe fn dispatch_unguarded_wpo_single_impl(raw: RawTraitObject, x: u64) -> u64 {
    let s = &*(raw.data_ptr as *const SharedStruct);
    x.wrapping_mul(s.factor).wrapping_add(7)
}

// Mode B: VP-2 / VP-3 VTable-Pointer Guard (`vptr == host_vtable_ptr`)
// 100% sound in open world; hits fast path on host vtable, takes indirect fallback on plugin duplicate vtable.
#[inline(never)]
unsafe fn dispatch_vp3_vtable_guard(
    raw: RawTraitObject,
    host_vtable_ptr: *const usize,
    x: u64,
) -> (u64, bool) {
    if raw.vtable_ptr == host_vtable_ptr {
        let s = &*(raw.data_ptr as *const SharedStruct);
        (x.wrapping_mul(s.factor).wrapping_add(7), true)
    } else {
        let fat: &dyn SharedTrait = std::mem::transmute(raw);
        (fat.compute(x), false)
    }
}

// Mode C: Two-Level DSO-Resilient Guard (`vptr == host_vtable_ptr || (*vptr).slot == target_fn_ptr`)
// 100% sound in open world AND hits direct fast path even on plugin's duplicate vtable for SharedStruct!
#[inline(never)]
unsafe fn dispatch_vp_two_level_dso_guard(
    raw: RawTraitObject,
    host_vtable_ptr: *const usize,
    host_slot_fn_ptr: usize,
    plugin_shared_slot_fn_ptr: usize,
    x: u64,
) -> (u64, bool) {
    if raw.vtable_ptr == host_vtable_ptr {
        let s = &*(raw.data_ptr as *const SharedStruct);
        (x.wrapping_mul(s.factor).wrapping_add(7), true)
    } else {
        let slot_fn = *raw.vtable_ptr.add(SLOT_COMPUTE);
        if slot_fn == host_slot_fn_ptr || slot_fn == plugin_shared_slot_fn_ptr {
            let s = &*(raw.data_ptr as *const SharedStruct);
            (x.wrapping_mul(s.factor).wrapping_add(7), true)
        } else {
            let fat: &dyn SharedTrait = std::mem::transmute(raw);
            (fat.compute(x), false)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let so_path = CString::new(args[1].as_str()).unwrap();
    unsafe {
        let handle = dlopen(so_path.as_ptr(), RTLD_NOW);
        assert!(!handle.is_null(), "dlopen failed");

        let sym_shared = CString::new("plugin_get_shared_struct_trait_obj").unwrap();
        let get_plugin_shared: extern "C" fn() -> RawTraitObject =
            std::mem::transmute(dlsym(handle, sym_shared.as_ptr()));

        let sym_priv = CString::new("plugin_get_private_struct_trait_obj").unwrap();
        let get_plugin_priv: extern "C" fn() -> RawTraitObject =
            std::mem::transmute(dlsym(handle, sym_priv.as_ptr()));

        let host_fat: &dyn SharedTrait = &HOST_SHARED_INSTANCE;
        let host_raw: RawTraitObject = std::mem::transmute(host_fat);
        let plugin_shared_raw = get_plugin_shared();
        let plugin_priv_raw = get_plugin_priv();

        let host_vtable_addr = host_raw.vtable_ptr as usize;
        let plugin_shared_vtable_addr = plugin_shared_raw.vtable_ptr as usize;
        let plugin_priv_vtable_addr = plugin_priv_raw.vtable_ptr as usize;

        let host_slot_fn = *host_raw.vtable_ptr.add(SLOT_COMPUTE);
        let plugin_shared_slot_fn = *plugin_shared_raw.vtable_ptr.add(SLOT_COMPUTE);
        let plugin_priv_slot_fn = *plugin_priv_raw.vtable_ptr.add(SLOT_COMPUTE);

        // Ground truth indirect calls
        let gt_host = dispatch_indirect(std::mem::transmute(host_raw), 10);
        let gt_plugin_shared = dispatch_indirect(std::mem::transmute(plugin_shared_raw), 10);
        let gt_plugin_priv = dispatch_indirect(std::mem::transmute(plugin_priv_raw), 10);

        // 1. Check unguarded WPO-DevirtSingleImpl miscompilation on PluginPrivateStruct
        let unguarded_on_priv = dispatch_unguarded_wpo_single_impl(plugin_priv_raw, 10);

        // 2. Check VP-3 vtable guard
        let (vp3_host_val, vp3_host_hit) =
            dispatch_vp3_vtable_guard(host_raw, host_raw.vtable_ptr, 10);
        let (vp3_plug_shared_val, vp3_plug_shared_hit) =
            dispatch_vp3_vtable_guard(plugin_shared_raw, host_raw.vtable_ptr, 10);
        let (vp3_plug_priv_val, vp3_plug_priv_hit) =
            dispatch_vp3_vtable_guard(plugin_priv_raw, host_raw.vtable_ptr, 10);

        // 3. Check Two-Level DSO guard
        let (vp2l_host_val, vp2l_host_hit) = dispatch_vp_two_level_dso_guard(
            host_raw,
            host_raw.vtable_ptr,
            host_slot_fn,
            plugin_shared_slot_fn,
            10,
        );
        let (vp2l_plug_shared_val, vp2l_plug_shared_hit) = dispatch_vp_two_level_dso_guard(
            plugin_shared_raw,
            host_raw.vtable_ptr,
            host_slot_fn,
            plugin_shared_slot_fn,
            10,
        );
        let (vp2l_plug_priv_val, vp2l_plug_priv_hit) = dispatch_vp_two_level_dso_guard(
            plugin_priv_raw,
            host_raw.vtable_ptr,
            host_slot_fn,
            plugin_shared_slot_fn,
            10,
        );

        // Benchmark mixed cross-DSO stream (50% host SharedStruct, 45% plugin SharedStruct, 5% plugin PrivateStruct)
        let n_iters = 200_000usize;
        let mut stream = Vec::with_capacity(n_iters);
        for i in 0..n_iters {
            let r = i % 20;
            if r < 10 {
                stream.push(host_raw);
            } else if r < 19 {
                stream.push(plugin_shared_raw);
            } else {
                stream.push(plugin_priv_raw);
            }
        }

        let bench = |mode: u32| -> (f64, usize) {
            let mut times = Vec::with_capacity(21);
            let mut hits = 0usize;
            for _ in 0..21 {
                hits = 0;
                let t0 = Instant::now();
                let mut acc = 0u64;
                for (idx, &item) in stream.iter().enumerate() {
                    let x = (idx as u64) & 63;
                    match mode {
                        0 => {
                            let fat: &dyn SharedTrait = std::mem::transmute(item);
                            acc = acc.wrapping_add(dispatch_indirect(black_box(fat), x));
                        }
                        1 => {
                            let (v, h) = dispatch_vp3_vtable_guard(
                                black_box(item),
                                host_raw.vtable_ptr,
                                x,
                            );
                            if h {
                                hits += 1;
                            }
                            acc = acc.wrapping_add(v);
                        }
                        _ => {
                            let (v, h) = dispatch_vp_two_level_dso_guard(
                                black_box(item),
                                host_raw.vtable_ptr,
                                host_slot_fn,
                                plugin_shared_slot_fn,
                                x,
                            );
                            if h {
                                hits += 1;
                            }
                            acc = acc.wrapping_add(v);
                        }
                    }
                }
                black_box(acc);
                times.push(t0.elapsed().as_nanos() as f64 / 1000.0);
            }
            times.sort_by(|a, b| a.partial_cmp(b).unwrap());
            (times[times.len() / 2], hits)
        };

        let (indirect_us, _) = bench(0);
        let (vp3_us, vp3_hits) = bench(1);
        let (vp2l_us, vp2l_hits) = bench(2);

        // Benchmark CratePrivateTraitInOpenBinary (`HostPrivateTrait`)
        let priv_worker = HostInternalWorker { k: 10 };
        let priv_dyn: &dyn HostPrivateTrait = black_box(&priv_worker);
        let mut priv_ind_times = Vec::with_capacity(21);
        let mut priv_devirt_times = Vec::with_capacity(21);
        for _ in 0..21 {
            let t0 = Instant::now();
            let mut acc = 0u64;
            for i in 0..n_iters {
                acc = acc.wrapping_add(black_box(priv_dyn).eval_private((i as u64) & 63));
            }
            black_box(acc);
            priv_ind_times.push(t0.elapsed().as_nanos() as f64 / 1000.0);

            let t1 = Instant::now();
            let mut acc2 = 0u64;
            for i in 0..n_iters {
                acc2 = acc2.wrapping_add(black_box(&priv_worker).eval_private((i as u64) & 63));
            }
            black_box(acc2);
            priv_devirt_times.push(t1.elapsed().as_nanos() as f64 / 1000.0);
        }
        priv_ind_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        priv_devirt_times.sort_by(|a, b| a.partial_cmp(b).unwrap());

        println!(
            "JSON_RESULT:{{\"host_vtable_addr\":\"0x{:x}\",\"plugin_shared_vtable_addr\":\"0x{:x}\",\"plugin_priv_vtable_addr\":\"0x{:x}\",\"duplicate_vtable_addresses_distinct\":{},\"host_slot_fn\":\"0x{:x}\",\"plugin_shared_slot_fn\":\"0x{:x}\",\"plugin_priv_slot_fn\":\"0x{:x}\",\"gt_host\":{},\"gt_plugin_shared\":{},\"gt_plugin_priv\":{},\"unguarded_wpo_on_priv\":{},\"unguarded_wpo_miscompiled\":{},\"vp3_sound_all_3\":{},\"vp3_host_hit\":{},\"vp3_plugin_shared_hit\":{},\"vp2l_sound_all_3\":{},\"vp2l_host_hit\":{},\"vp2l_plugin_shared_hit\":{},\"vp2l_plugin_priv_hit\":{},\"stream_indirect_us\":{:.2},\"stream_vp3_us\":{:.2},\"stream_vp3_hit_rate_pct\":{:.2},\"stream_vp2l_us\":{:.2},\"stream_vp2l_hit_rate_pct\":{:.2},\"private_trait_indirect_us\":{:.2},\"private_trait_wpo_devirt_us\":{:.2}}}",
            host_vtable_addr,
            plugin_shared_vtable_addr,
            plugin_priv_vtable_addr,
            host_vtable_addr != plugin_shared_vtable_addr,
            host_slot_fn,
            plugin_shared_slot_fn,
            plugin_priv_slot_fn,
            gt_host,
            gt_plugin_shared,
            gt_plugin_priv,
            unguarded_on_priv,
            unguarded_on_priv != gt_plugin_priv,
            vp3_host_val == gt_host && vp3_plug_shared_val == gt_plugin_shared && vp3_plug_priv_val == gt_plugin_priv,
            vp3_host_hit,
            vp3_plug_shared_hit,
            vp2l_host_val == gt_host && vp2l_plug_shared_val == gt_plugin_shared && vp2l_plug_priv_val == gt_plugin_priv,
            vp2l_host_hit,
            vp2l_plug_shared_hit,
            vp2l_plug_priv_hit,
            indirect_us,
            vp3_us,
            (vp3_hits as f64 / n_iters as f64) * 100.0,
            vp2l_us,
            (vp2l_hits as f64 / n_iters as f64) * 100.0,
            priv_ind_times[priv_ind_times.len() / 2],
            priv_devirt_times[priv_devirt_times.len() / 2]
        );
    }
}
