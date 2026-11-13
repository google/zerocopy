import os, subprocess, json, glob, re

tmp = "/tmp/rustc-1.99.1-probes"
staged = "./reports"
s1991 = "<rust-1.99.1-checkout>"
rustc = ["rustc", "+1.99.1-x86_64-unknown-linux-gnu", "--edition=2024"]
llvm_bin = "<rustup-1.99.1-sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin"
llvm_nm = f"{llvm_bin}/llvm-nm"

# 1. V2: Extract complete AttributeKind, string attributes, MetadataKindId, instruction flags, global properties, module flags from s1991
with open(f"{s1991}/compiler/rustc_codegen_llvm/src/llvm/ffi.rs") as f:
    ffi_rs = f.read()
attr_kinds = re.findall(r"^\s+([A-Z][A-Za-z0-9_]+)\s*=\s*(\d+),", ffi_rs[ffi_rs.find("pub(crate) enum AttributeKind"):ffi_rs.find("pub(crate) enum IntPredicate")], re.M)

with open(f"{s1991}/compiler/rustc_codegen_llvm/src/llvm/metadata_kind.rs") as f:
    md_rs = f.read()
md_kinds = re.findall(r"FIXED_MD_KIND\((MD_[A-Za-z0-9_]+),\s*(\d+)\)", md_rs)

str_attrs = set()
module_flags = set()
for root, _, files in os.walk(f"{s1991}/compiler/rustc_codegen_llvm/src"):
    for fn in files:
        if fn.endswith(".rs"):
            with open(os.path.join(root, fn)) as fp:
                txt = fp.read()
            for m in re.finditer(r'CreateAttrString(?:Value)?\([^,]+,\s*"([^"]+)"', txt):
                str_attrs.add(m.group(1))
            for m in re.finditer(r'add_module_flag_(?:u32|str)\([^,]+,\s*[^,]+,\s*"([^"]+)"', txt):
                module_flags.add(m.group(1))

# Also emit real LLVM IR from 1.99.1 on a probe exercising references, niches, nonnull, Box, allocator, atomics, checked math, unchecked math, GEP
v2_probe_rs = f"{tmp}/v2_ir_probe.rs"
with open(v2_probe_rs, "w") as f:
    f.write("""#![crate_type = "lib"]
use std::num::NonZeroU64;

#[repr(C)]
pub struct BigPair(pub [u64; 8], pub u64);

pub fn ref_and_niche(r: &mut u64, shared: &BigPair, nz: NonZeroU64, b: bool) -> Option<NonZeroU64> {
    if b {
        *r = r.wrapping_add(shared.1).wrapping_add(nz.get());
        Some(nz)
    } else {
        None
    }
}

pub unsafe fn unchecked_ops(a: u32, b: u32, p: *const u32, idx: usize) -> u32 {
    unsafe {
        let sum = a.unchecked_add(b);
        let elem = *p.add(idx);
        sum.unchecked_mul(elem)
    }
}
""")
subprocess.run(rustc + ["-Copt-level=2", "--emit=llvm-ir", v2_probe_rs, "-o", f"{tmp}/v2_ir_probe.ll"], cwd=tmp, check=True)
with open(f"{tmp}/v2_ir_probe.ll") as f:
    v2_ir_sample = f.read()

v2_catalog = {
    "baseline": {
        "rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "attribute_kind_count": len(attr_kinds),
        "metadata_kind_count": len(md_kinds),
        "string_attribute_count": len(str_attrs),
        "module_flag_count": len(module_flags),
    },
    "enum_attribute_kinds": [{"variant": k, "discriminant": int(v)} for k, v in attr_kinds],
    "fixed_metadata_kinds": [{"name": k, "id": int(v)} for k, v in md_kinds],
    "string_attributes": sorted(str_attrs),
    "module_flags": sorted(module_flags),
    "sample_emitted_llvm_ir_lines": v2_ir_sample.splitlines()[:120],
}
v2_supp = os.path.join(staged, "rustc-llvm-ir-attributes-metadata-and-cross-path-obligations", "support")
os.makedirs(v2_supp, exist_ok=True)
with open(f"{v2_supp}/llvm_ir_catalog.json", "w") as f:
    json.dump(v2_catalog, f, indent=2)

# 2. V3: Binary origin attribution across hello_world, cli_tool, async_server, cdylib, staticlib and configs (dev, release, lto, panic=abort, gc-sections, icf=all)
v3_supp = os.path.join(staged, "rustc-binary-origin-attribution-gc-sections-and-icf-soundness", "support")
os.makedirs(v3_supp, exist_ok=True)

v3_sources = {
    "hello_world": 'fn main() { println!("Hello, world!"); }\n',
    "cli_tool": """
use std::env;
use std::fs;
use std::collections::HashMap;
fn main() {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for arg in env::args().skip(1) {
        if let Ok(data) = fs::read_to_string(&arg) {
            for word in data.split_whitespace() {
                *counts.entry(word.to_owned()).or_insert(0) += 1;
            }
        }
    }
    println!("unique={}", counts.len());
}
""",
    "async_server": """
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::net::TcpListener;
use std::sync::Arc;

async fn handle_conn(id: u64) -> u64 {
    id.wrapping_mul(6364136223846793005).wrapping_add(1)
}

fn dummy_waker() -> Waker {
    fn no_op(_: *const ()) {}
    fn clone(p: *const ()) -> RawWaker { RawWaker::new(p, &VTABLE) }
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn main() {
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    let mut fut = Box::pin(handle_conn(42));
    if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) {
        let _ = TcpListener::bind("127.0.0.1:0").map(|l| Arc::new(l));
        println!("ready={v}");
    }
}
""",
    "cdylib_sample": """
#[unsafe(no_mangle)]
pub extern "C" fn rust_cdylib_entry(x: u64, y: u64) -> u64 {
    let s = format!("{x}:{y}");
    s.len() as u64
}
""",
}

for name, src in v3_sources.items():
    with open(f"{tmp}/v3_{name}.rs", "w") as f:
        f.write(src)

def classify_symbol(sym):
    if "compiler_builtins" in sym or sym.startswith("__rust_probestack") or sym.startswith("__muloti4") or sym.startswith("__udivti3") or sym.startswith("__divti3"):
        return "compiler_builtins"
    if any(k in sym for k in ["std::", "core::", "alloc::", "rustc_demangle", "gimli::", "addr2line::", "miniz_oxide::", "object::", "hashbrown::", "__rust_alloc", "rust_eh_personality"]):
        if "gimli" in sym or "addr2line" in sym or "miniz_oxide" in sym or "object::" in sym:
            return "sysroot_backtrace_dwarf"
        return "sysroot_std_core_alloc"
    if any(k in sym for k in ["_start", "__libc_csu", "_init", "_fini", "deregister_tm_clones", "register_tm_clones", "__do_global_dtors_aux", "frame_dummy", "_dl_relocate_static_pie"]):
        return "crt_startup"
    if any(k in sym for k in ["_Unwind_", "__frame_dummy", "fde_", "read_encoded_value"]):
        return "unwinder"
    if any(k in sym for k in ["v3_hello_world", "v3_cli_tool", "v3_async_server", "rust_cdylib_entry", "handle_conn", "dummy_waker", "::main"]):
        return "local_crate_rust"
    return "other_or_linker"

def analyze_elf(path):
    total_file_bytes = os.path.getsize(path)
    sec_out = subprocess.check_output(["readelf", "-SW", path], text=True)
    sections = {}
    for line in sec_out.splitlines():
        m = re.match(r"^\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)", line)
        if m:
            sname, stype, addr, off, size = m.groups()
            sections[sname] = {"type": stype, "size": int(size, 16)}
    nm_out = subprocess.run([llvm_nm, "--demangle", "--print-size", "--size-sort", path], capture_output=True, text=True).stdout
    origin_bytes = {}
    for line in nm_out.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4:
            addr, size_hex, stype, sym = parts
            try:
                sz = int(size_hex, 16)
            except ValueError:
                continue
            cat = classify_symbol(sym)
            origin_bytes[cat] = origin_bytes.get(cat, 0) + sz
    return {
        "file_size_bytes": total_file_bytes,
        "text_bytes": sections.get(".text", {}).get("size", 0),
        "rodata_bytes": sections.get(".rodata", {}).get("size", 0),
        "data_rel_ro_bytes": sections.get(".data.rel.ro", {}).get("size", 0),
        "eh_frame_bytes": sections.get(".eh_frame", {}).get("size", 0) + sections.get(".eh_frame_hdr", {}).get("size", 0),
        "gcc_except_table_bytes": sections.get(".gcc_except_table", {}).get("size", 0),
        "rela_dyn_bytes": sections.get(".rela.dyn", {}).get("size", 0) + sections.get(".rela.plt", {}).get("size", 0),
        "tdata_tbss_bytes": sections.get(".tdata", {}).get("size", 0) + sections.get(".tbss", {}).get("size", 0),
        "symbol_origin_bytes": origin_bytes,
    }

v3_results = {"x86_64_linux_matrix": {}, "gc_and_icf_ablation": {}, "cross_target_rlib_staticlib": {}}
configs = [
    ("dev", []),
    ("release", ["-Copt-level=3"]),
    ("lto_fat", ["-Copt-level=3", "-Clto=fat", "-Ccodegen-units=1"]),
    ("panic_abort", ["-Copt-level=3", "-Cpanic=abort"]),
]

for bname in ["hello_world", "cli_tool", "async_server"]:
    v3_results["x86_64_linux_matrix"][bname] = {}
    for cname, flags in configs:
        out_p = f"{tmp}/v3_{bname}_{cname}"
        subprocess.run(rustc + flags + [f"{tmp}/v3_{bname}.rs", "-o", out_p], cwd=tmp, check=True)
        v3_results["x86_64_linux_matrix"][bname][cname] = analyze_elf(out_p)

for cname, flags in configs:
    out_cdylib = f"{tmp}/v3_cdylib_{cname}.so"
    subprocess.run(rustc + ["--crate-type=cdylib"] + flags + [f"{tmp}/v3_cdylib_sample.rs", "-o", out_cdylib], cwd=tmp, check=True)
    out_staticlib = f"{tmp}/v3_staticlib_{cname}.a"
    subprocess.run(rustc + ["--crate-type=staticlib"] + flags + [f"{tmp}/v3_cdylib_sample.rs", "-o", out_staticlib], cwd=tmp, check=True)
    v3_results["x86_64_linux_matrix"].setdefault("cdylib", {})[cname] = analyze_elf(out_cdylib)
    v3_results["x86_64_linux_matrix"].setdefault("staticlib", {})[cname] = {"file_size_bytes": os.path.getsize(out_staticlib)}

# Measure --gc-sections vs --no-gc-sections and --icf=all vs --icf=safe vs --icf=none on cli_tool (release) using rust-lld
for mode, lflags in [
    ("default_gc_sections", ["-Zunstable-options", "-Clink-self-contained=+linker", "-Clinker-flavor=gnu-lld-cc"]),
    ("no_gc_sections", ["-Zunstable-options", "-Clink-self-contained=+linker", "-Clinker-flavor=gnu-lld-cc", "-Clink-arg=-Wl,--no-gc-sections"]),
    ("icf_safe", ["-Zunstable-options", "-Clink-self-contained=+linker", "-Clinker-flavor=gnu-lld-cc", "-Clink-arg=-Wl,--icf=safe"]),
    ("icf_all", ["-Zunstable-options", "-Clink-self-contained=+linker", "-Clinker-flavor=gnu-lld-cc", "-Clink-arg=-Wl,--icf=all"]),
]:
    out_p = f"{tmp}/v3_cli_{mode}"
    subprocess.run(rustc + ["-Copt-level=3"] + lflags + [f"{tmp}/v3_cli_tool.rs", "-o", out_p], cwd=tmp, check=True)
    v3_results["gc_and_icf_ablation"][mode] = analyze_elf(out_p)

# Also prove ICF function pointer equality hazard with --icf=all vs --icf=safe!
icf_probe_rs = f"{tmp}/v3_icf_probe.rs"
with open(icf_probe_rs, "w") as f:
    f.write("""#[inline(never)]
pub fn fn_one(x: u64) -> u64 { x.wrapping_add(1234567) }
#[inline(never)]
pub fn fn_two(x: u64) -> u64 { x.wrapping_add(1234567) }
fn main() {
    let p1 = fn_one as usize;
    let p2 = fn_two as usize;
    println!("p1=0x{p1:x} p2=0x{p2:x} eq={} sum={}", p1 == p2, fn_one(1) + fn_two(2));
}
""")
for icf_mode in ["none", "safe", "all"]:
    out_p = f"{tmp}/v3_icf_{icf_mode}"
    subprocess.run(rustc + ["-Copt-level=2", "-Zunstable-options", "-Clink-self-contained=+linker", "-Clinker-flavor=gnu-lld-cc", f"-Clink-arg=-Wl,--icf={icf_mode}", icf_probe_rs, "-o", out_p], cwd=tmp, check=True)
    run_out = subprocess.check_output([out_p], text=True).strip()
    v3_results["gc_and_icf_ablation"][f"fn_ptr_probe_icf_{icf_mode}"] = {
        "stdout": run_out,
        "text_bytes": analyze_elf(out_p)["text_bytes"],
    }

# Cross-target staticlib sizes across all 8 Tier 1 targets
tier1 = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
]
for t in tier1:
    out_a = f"{tmp}/v3_staticlib_{t}.a"
    subprocess.run(rustc + ["--target", t, "--crate-type=staticlib", "-Copt-level=3", f"{tmp}/v3_cdylib_sample.rs", "-o", out_a], cwd=tmp, check=True)
    out_o = f"{tmp}/v3_obj_{t}.o"
    subprocess.run(rustc + ["--target", t, "--crate-type=lib", "--emit=obj", "-Copt-level=3", f"{tmp}/v3_cdylib_sample.rs", "-o", out_o], cwd=tmp, check=True)
    v3_results["cross_target_rlib_staticlib"][t] = {
        "staticlib_bytes": os.path.getsize(out_a),
        "single_cgu_object_bytes": os.path.getsize(out_o),
    }

with open(f"{v3_supp}/v3_attribution_tables.json", "w") as f:
    json.dump(v3_results, f, indent=2)

print("Generated V2 and V3 support artifacts successfully")
