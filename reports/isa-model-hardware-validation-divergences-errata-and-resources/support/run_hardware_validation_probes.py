#!/usr/bin/env python3
import json
import os
import re
import subprocess
from pathlib import Path

RUN_DIR = Path(os.environ.get("OUT_DIR", "/tmp/isa_val"))
TMP_DIR = RUN_DIR / "tmp"
TMP_DIR.mkdir(parents=True, exist_ok=True)

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = TC_ROOT / "bin" / "rustc"

def get_host_info():
    cpuinfo = Path("/proc/cpuinfo").read_text()
    info = {}
    for k in ["vendor_id", "cpu family", "model", "model name", "stepping", "microcode", "flags"]:
        m = re.search(rf"^{k}\s*:\s*(.+)$", cpuinfo, re.M)
        if m:
            info[k.replace(" ", "_")] = m.group(1).strip()
    if "flags" in info:
        info["flags_list"] = sorted(info["flags"].split())
        del info["flags"]
    qemu_i386_ver = subprocess.check_output(["qemu-i386", "--version"], text=True).splitlines()[0]
    qemu_aarch64_ver = subprocess.check_output(["qemu-aarch64", "--version"], text=True).splitlines()[0]
    info["qemu_i386_version"] = qemu_i386_ver
    info["qemu_aarch64_version"] = qemu_aarch64_ver
    return info

X86_64_PROBE_RS = r"""
use std::arch::asm;

fn main() {
    // 1. Base GPR: 128-bit MUL, SHLD, BSWAP
    let a: u64 = 0xFEDC_BA98_7654_3210;
    let b: u64 = 0x0123_4567_89AB_CDEF;
    let lo: u64;
    let hi: u64;
    let flags_mul: u64;
    unsafe {
        asm!(
            "mul {b}",
            "pushfq",
            "pop {fl}",
            inout("rax") a => lo,
            out("rdx") hi,
            b = in(reg) b,
            fl = out(reg) flags_mul,
        );
    }

    // 2. BMI1 & BMI2: TZCNT(0), LZCNT(0), PDEP, PEXT, BZHI, RORX, MULX
    let tz_zero_in: u64 = 0;
    let tz_zero_out: u64;
    let tz_flags: u64;
    unsafe {
        asm!(
            "tzcnt {out}, {inp}",
            "pushfq",
            "pop {fl}",
            inp = in(reg) tz_zero_in,
            out = out(reg) tz_zero_out,
            fl = out(reg) tz_flags,
        );
    }
    let lz_zero_out: u64;
    let lz_flags: u64;
    unsafe {
        asm!(
            "lzcnt {out}, {inp}",
            "pushfq",
            "pop {fl}",
            inp = in(reg) tz_zero_in,
            out = out(reg) lz_zero_out,
            fl = out(reg) lz_flags,
        );
    }
    let pdep_out: u64;
    let pext_out: u64;
    let bzhi_out: u64;
    let src_val: u64 = 0xABCD_EF01_2345_6789;
    let mask_val: u64 = 0x0F0F_0F0F_0F0F_0F0F;
    let idx_val: u64 = 20;
    unsafe {
        asm!(
            "pdep {pdep}, {src}, {mask}",
            "pext {pext}, {src}, {mask}",
            "bzhi {bzhi}, {src}, {idx}",
            src = in(reg) src_val,
            mask = in(reg) mask_val,
            idx = in(reg) idx_val,
            pdep = out(reg) pdep_out,
            pext = out(reg) pext_out,
            bzhi = out(reg) bzhi_out,
        );
    }

    // 3. Divergence probe: BSF and BSR on zero input with pre-seeded destination
    let mut bsf_dst: u64 = 0xDEAD_BEEF_CAFE_BABE;
    let bsf_flags: u64;
    let zero_reg: u64 = 0;
    unsafe {
        asm!(
            "bsf {dst}, {src}",
            "pushfq",
            "pop {fl}",
            dst = inout(reg) bsf_dst,
            src = in(reg) zero_reg,
            fl = out(reg) bsf_flags,
        );
    }
    let mut bsr_dst: u64 = 0x1337_C0DE_4242_9999;
    let bsr_flags: u64;
    unsafe {
        asm!(
            "bsr {dst}, {src}",
            "pushfq",
            "pop {fl}",
            dst = inout(reg) bsr_dst,
            src = in(reg) zero_reg,
            fl = out(reg) bsr_flags,
        );
    }

    // 4. ADX dual carry chains: ADCX (CF) and ADOX (OF) simultaneously
    let mut c_chain: u64 = 1;
    let mut o_chain: u64 = 2;
    let max_u64: u64 = u64::MAX;
    let one_u64: u64 = 1;
    let adx_flags: u64;
    unsafe {
        asm!(
            "xor eax, eax",
            "stc",
            "adcx {c}, {m}",
            "adox {o}, {m}",
            "pushfq",
            "pop {fl}",
            c = inout(reg) c_chain,
            o = inout(reg) o_chain,
            m = in(reg) max_u64,
            out("rax") _,
            fl = out(reg) adx_flags,
        );
    }
    let _ = one_u64;

    // 5. SSE4.2 CRC32Q & POPCNT
    let crc_in: u64 = 0x0123_4567_89AB_CDEF;
    let mut crc_acc: u64 = 0xFFFF_FFFF;
    let pop_out: u64;
    unsafe {
        asm!(
            "crc32 {crc}, {inp}",
            "popcnt {pop}, {inp}",
            crc = inout(reg) crc_acc,
            inp = in(reg) crc_in,
            pop = out(reg) pop_out,
        );
    }

    // 6. Approximation divergence probes: RCPSS, RSQRTSS (SSE) and VRCP14SS, VRSQRT14SS (AVX-512)
    let inputs_f32: [f32; 4] = [1.0, 2.0, 3.0, 0.25];
    let mut approx_rows = Vec::new();
    for &x in &inputs_f32 {
        let xb: u32 = x.to_bits();
        let rcpss_b: u32;
        let rsqrtss_b: u32;
        let vrcp14_b: u32;
        let vrsqrt14_b: u32;
        unsafe {
            asm!(
                "movd xmm0, {xb:e}",
                "rcpss xmm1, xmm0",
                "rsqrtss xmm2, xmm0",
                "vrcp14ss xmm3, xmm0, xmm0",
                "vrsqrt14ss xmm4, xmm0, xmm0",
                "movd {rcp:e}, xmm1",
                "movd {rsqrt:e}, xmm2",
                "vmovd {vrcp:e}, xmm3",
                "vmovd {vrsqrt:e}, xmm4",
                xb = in(reg) xb,
                rcp = out(reg) rcpss_b,
                rsqrt = out(reg) rsqrtss_b,
                vrcp = out(reg) vrcp14_b,
                vrsqrt = out(reg) vrsqrt14_b,
                out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _, out("xmm4") _,
            );
        }
        approx_rows.push(format!(
            "{{\"input\": {}, \"input_bits\": \"0x{:08x}\", \"rcpss_bits\": \"0x{:08x}\", \"rcpss_val\": {}, \"rsqrtss_bits\": \"0x{:08x}\", \"rsqrtss_val\": {}, \"vrcp14ss_bits\": \"0x{:08x}\", \"vrcp14ss_val\": {}, \"vrsqrt14ss_bits\": \"0x{:08x}\", \"vrsqrt14ss_val\": {}}}",
            x, xb,
            rcpss_b, f32::from_bits(rcpss_b),
            rsqrtss_b, f32::from_bits(rsqrtss_b),
            vrcp14_b, f32::from_bits(vrcp14_b),
            vrsqrt14_b, f32::from_bits(vrsqrt14_b)
        ));
    }

    // 7. FMA3 vs unfused MUL+ADD single-rounding discriminator
    let fma_a: f64 = 1.0 + f64::EPSILON;
    let fma_b: f64 = 1.0 - f64::EPSILON;
    let fma_c: f64 = -1.0;
    let fused_bits: u64;
    let unfused_bits: u64;
    unsafe {
        asm!(
            "vmovq xmm0, {a}",
            "vmovq xmm1, {b}",
            "vmovq xmm2, {c}",
            "vmovapd xmm3, xmm0",
            "vfmadd213sd xmm0, xmm1, xmm2",
            "vmulsd xmm3, xmm3, xmm1",
            "vaddsd xmm3, xmm3, xmm2",
            "vmovq {fused}, xmm0",
            "vmovq {unfused}, xmm3",
            a = in(reg) fma_a.to_bits(),
            b = in(reg) fma_b.to_bits(),
            c = in(reg) fma_c.to_bits(),
            fused = out(reg) fused_bits,
            unfused = out(reg) unfused_bits,
            out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
        );
    }

    // 8. AVX-512 predicate masking (k1 zero-masking vs merge-masking) & VPOPCNTQ
    let avx512_zmask_lo: u64;
    let avx512_zmask_hi: u64;
    let avx512_popcnt_lo: u64;
    unsafe {
        asm!(
            "mov eax, 0x05",
            "kmovw k1, eax",
            "vpternlogd zmm0, zmm0, zmm0, 0xff",
            "vpxorq zmm1, zmm1, zmm1",
            "vpaddq zmm1 {{k1}}{{z}}, zmm0, zmm0",
            "vpopcntq zmm2, zmm0",
            "vmovq {zlo}, xmm1",
            "vpextrq {zhi}, xmm1, 1",
            "vmovq {plo}, xmm2",
            "vzeroupper",
            out("eax") _,
            out("k1") _,
            out("zmm0") _, out("zmm1") _, out("zmm2") _,
            zlo = out(reg) avx512_zmask_lo,
            zhi = out(reg) avx512_zmask_hi,
            plo = out(reg) avx512_popcnt_lo,
        );
    }

    println!(
        "{{\"mul128_lo\": \"0x{:016x}\", \"mul128_hi\": \"0x{:016x}\", \"mul128_cf_of\": {}, \"tzcnt_0\": {}, \"tzcnt_0_cf\": {}, \"tzcnt_0_zf\": {}, \"lzcnt_0\": {}, \"lzcnt_0_cf\": {}, \"pdep\": \"0x{:016x}\", \"pext\": \"0x{:016x}\", \"bzhi\": \"0x{:016x}\", \"bsf_0_dst_preserved\": \"0x{:016x}\", \"bsf_0_zf\": {}, \"bsr_0_dst_preserved\": \"0x{:016x}\", \"bsr_0_zf\": {}, \"adx_c_chain\": {}, \"adx_o_chain\": {}, \"adx_cf\": {}, \"adx_of\": {}, \"crc32q\": \"0x{:016x}\", \"popcnt\": {}, \"fma_fused_bits\": \"0x{:016x}\", \"fma_unfused_bits\": \"0x{:016x}\", \"avx512_zmask_lane0\": \"0x{:016x}\", \"avx512_zmask_lane1\": \"0x{:016x}\", \"avx512_vpopcntq_allones\": {}, \"approximations\": [{}]}}",
        lo, hi, (flags_mul & 0x801) != 0,
        tz_zero_out, tz_flags & 1, (tz_flags >> 6) & 1,
        lz_zero_out, lz_flags & 1,
        pdep_out, pext_out, bzhi_out,
        bsf_dst, (bsf_flags >> 6) & 1,
        bsr_dst, (bsr_flags >> 6) & 1,
        c_chain, o_chain, adx_flags & 1, (adx_flags >> 11) & 1,
        crc_acc, pop_out,
        fused_bits, unfused_bits,
        avx512_zmask_lo, avx512_zmask_hi, avx512_popcnt_lo,
        approx_rows.join(", ")
    );
}
"""

I686_PROBE_RS = r"""
use std::arch::asm;

fn main() {
    let mut bsf_dst: u32 = 0xDEAD_BEEF;
    let bsf_flags: u32;
    let zero_reg: u32 = 0;
    unsafe {
        asm!(
            "bsf {dst}, {src}",
            "pushfd",
            "pop {fl}",
            dst = inout(reg) bsf_dst,
            src = in(reg) zero_reg,
            fl = out(reg) bsf_flags,
        );
    }
    let tz_out: u32;
    let tz_flags: u32;
    unsafe {
        asm!(
            "tzcnt {out}, {src}",
            "pushfd",
            "pop {fl}",
            out = out(reg) tz_out,
            src = in(reg) zero_reg,
            fl = out(reg) tz_flags,
        );
    }
    let shld_out: u32;
    let a: u32 = 0x1234_5678;
    let b: u32 = 0x9ABC_DEF0;
    unsafe {
        asm!(
            "shld {a}, {b}, 8",
            a = inout(reg) a => shld_out,
            b = in(reg) b,
        );
    }
    let x_bits: u32 = 3.0f32.to_bits();
    let rcp_bits: u32;
    let rsqrt_bits: u32;
    unsafe {
        asm!(
            "movd xmm0, {x}",
            "rcpss xmm1, xmm0",
            "rsqrtss xmm2, xmm0",
            "movd {rcp}, xmm1",
            "movd {rsqrt}, xmm2",
            x = in(reg) x_bits,
            rcp = out(reg) rcp_bits,
            rsqrt = out(reg) rsqrt_bits,
            out("xmm0") _, out("xmm1") _, out("xmm2") _,
        );
    }
    println!(
        "{{\"bsf_0_dst\": \"0x{:08x}\", \"bsf_0_zf\": {}, \"tzcnt_0\": {}, \"tzcnt_0_cf\": {}, \"shld_8\": \"0x{:08x}\", \"rcpss_3_0_bits\": \"0x{:08x}\", \"rsqrtss_3_0_bits\": \"0x{:08x}\"}}",
        bsf_dst, (bsf_flags >> 6) & 1, tz_out, tz_flags & 1, shld_out, rcp_bits, rsqrt_bits
    );
}
"""

AARCH64_PROBE_RS = r"""#![no_std]
#![no_main]

use core::arch::asm;

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    // 1. Base A64: UDIV/SDIV by 0 and INT64_MIN / -1, ADDS NZCV, CLZ, RBIT, REV
    let dividend: u64 = 0x1234_5678_9ABC_DEF0;
    let zero: u64 = 0;
    let udiv_zero: u64;
    let sdiv_zero: u64;
    let sdiv_min_neg1: i64;
    let min_i64: i64 = i64::MIN;
    let neg1_i64: i64 = -1;
    unsafe {
        asm!(
            "udiv {u}, {d}, {z}",
            "sdiv {s}, {d}, {z}",
            "sdiv {m}, {mn}, {n1}",
            d = in(reg) dividend,
            z = in(reg) zero,
            mn = in(reg) min_i64,
            n1 = in(reg) neg1_i64,
            u = out(reg) udiv_zero,
            s = out(reg) sdiv_zero,
            m = out(reg) sdiv_min_neg1,
        );
    }

    let adds_out: u64;
    let nzcv_adds: u64;
    let max_u64: u64 = u64::MAX;
    let one: u64 = 1;
    unsafe {
        asm!(
            "adds {out}, {a}, {b}",
            "mrs {nzcv}, nzcv",
            a = in(reg) max_u64,
            b = in(reg) one,
            out = out(reg) adds_out,
            nzcv = out(reg) nzcv_adds,
        );
    }

    let clz_out: u64;
    let rbit_out: u64;
    let rev_out: u64;
    let bit_in: u64 = 0x00F0_1234_5678_9ABC;
    unsafe {
        asm!(
            "clz {clz}, {inp}",
            "rbit {rbit}, {inp}",
            "rev {rev}, {inp}",
            inp = in(reg) bit_in,
            clz = out(reg) clz_out,
            rbit = out(reg) rbit_out,
            rev = out(reg) rev_out,
        );
    }

    // 2. LSE Atomics: CAS and LDADD
    let mut mem_cell: u64 = 100;
    let cas_prev: u64;
    let ldadd_prev: u64;
    unsafe {
        asm!(
            "mov {prev}, 100",
            "casal {prev}, {newv}, [{ptr}]",
            "ldaddal {addv}, {lprev}, [{ptr}]",
            ptr = in(reg) &mut mem_cell,
            newv = in(reg) 250u64,
            addv = in(reg) 50u64,
            prev = out(reg) cas_prev,
            lprev = out(reg) ldadd_prev,
        );
    }

    // 3. NEON / FP approximations: FRECPE and FRSQRTE on 3.0f32
    let x_bits: u32 = 0x4040_0000; // 3.0f32
    let frecpe_bits: u32;
    let frsqrte_bits: u32;
    unsafe {
        asm!(
            "fmov s0, {x:w}",
            "frecpe s1, s0",
            "frsqrte s2, s0",
            "fmov {rcp:w}, s1",
            "fmov {rsqrt:w}, s2",
            x = in(reg) x_bits,
            rcp = out(reg) frecpe_bits,
            rsqrt = out(reg) frsqrte_bits,
            out("v0") _, out("v1") _, out("v2") _,
        );
    }

    // 4. Crypto: AESE + AESMC, PMULL
    let aes_state_lo: u64;
    let pmull_lo: u64;
    unsafe {
        asm!(
            "movi v0.16b, #0x42",
            "movi v1.16b, #0x13",
            "aese v0.16b, v1.16b",
            "aesmc v0.16b, v0.16b",
            "umov {aes}, v0.d[0]",
            "pmull v2.1q, v0.1d, v1.1d",
            "umov {pmull}, v2.d[0]",
            aes = out(reg) aes_state_lo,
            pmull = out(reg) pmull_lo,
            out("v0") _, out("v1") _, out("v2") _,
        );
    }

    // 5. SVE: RDVL and INDEX + UADDV reduction
    let sve_vl_bytes: u64;
    let sve_index_sum: u64;
    unsafe {
        asm!(
            "rdvl {vl}, #1",
            "ptrue p0.d",
            "index z0.d, #1, #1",
            "uaddv d0, p0, z0.d",
            "fmov {sum}, d0",
            vl = out(reg) sve_vl_bytes,
            sum = out(reg) sve_index_sum,
            out("z0") _, out("p0") _,
        );
    }

    // 6. PAC & BTI: PACDA + AUTDA and BTI c
    let raw_ptr: u64 = 0x0000_1234_5678_9AB0;
    let pac_mod: u64 = 0xCAFE_BABE_1337_0001;
    let mut signed_ptr: u64 = raw_ptr;
    let aut_ptr: u64;
    unsafe {
        asm!(
            "bti c",
            "pacda {p}, {m}",
            "mov {aut}, {p}",
            "autda {aut}, {m}",
            p = inout(reg) signed_ptr,
            m = in(reg) pac_mod,
            aut = out(reg) aut_ptr,
        );
    }

    let out_words: [u64; 19] = [
        udiv_zero,
        sdiv_zero,
        sdiv_min_neg1 as u64,
        adds_out,
        nzcv_adds,
        clz_out,
        rbit_out,
        rev_out,
        cas_prev,
        ldadd_prev,
        mem_cell,
        frecpe_bits as u64,
        frsqrte_bits as u64,
        aes_state_lo,
        pmull_lo,
        sve_vl_bytes,
        sve_index_sum,
        signed_ptr,
        aut_ptr,
    ];

    unsafe {
        asm!(
            "mov x8, #64",
            "mov x0, #1",
            "mov x2, #152",
            "svc #0",
            "mov x8, #93",
            "mov x0, #0",
            "svc #0",
            in("x1") out_words.as_ptr(),
            options(noreturn)
        );
    }
}
"""

def main():
    import struct
    host = get_host_info()
    # 1. Build and run x86_64
    x64_src = TMP_DIR / "x64_val.rs"
    x64_bin = TMP_DIR / "x64_val"
    x64_src.write_text(X86_64_PROBE_RS)
    subprocess.run([str(RUSTC), "-Ctarget-cpu=native", "-O", str(x64_src), "-o", str(x64_bin)], check=True)
    x64_out = json.loads(subprocess.check_output([str(x64_bin)], text=True).strip())
    print("x86_64 native result:", json.dumps(x64_out, indent=2)[:600])

    # 2. Build and run i686 (native IA-32 vs qemu-i386)
    i686_src = TMP_DIR / "i686_val.rs"
    i686_bin = TMP_DIR / "i686_val"
    i686_src.write_text(I686_PROBE_RS)
    subprocess.run([str(RUSTC), "--target", "i686-unknown-linux-gnu", "-Ctarget-feature=+bmi1,+lzcnt,+popcnt,+sse4.2", "-O", str(i686_src), "-o", str(i686_bin)], check=True)
    i686_native = json.loads(subprocess.check_output([str(i686_bin)], text=True).strip())
    i686_qemu = json.loads(subprocess.check_output(["qemu-i386", "-cpu", "max", str(i686_bin)], text=True).strip())
    print("i686 native:", i686_native)
    print("i686 qemu:  ", i686_qemu)

    # 3. Build and run aarch64 under qemu-aarch64 -cpu max
    a64_src = TMP_DIR / "a64_val.rs"
    a64_obj = TMP_DIR / "a64_val.o"
    a64_bin = TMP_DIR / "a64_val"
    a64_src.write_text(AARCH64_PROBE_RS)
    rust_lld = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / "rust-lld"
    subprocess.run([
        str(RUSTC), "--target", "aarch64-unknown-linux-gnu",
        "-Ctarget-feature=+lse,+aes,+sha2,+sve,+paca,+pacg,+bti",
        "-Cpanic=abort", "-O", "--emit=obj", str(a64_src), "-o", str(a64_obj)
    ], check=True)
    subprocess.run([
        str(rust_lld), "-flavor", "gnu", "-static", "-e", "_start",
        str(a64_obj), "-o", str(a64_bin)
    ], check=True)
    raw_a64 = subprocess.check_output(["qemu-aarch64", "-cpu", "max", str(a64_bin)])
    w = struct.unpack("<19Q", raw_a64)
    raw_ptr = 0x0000_1234_5678_9AB0
    a64_qemu = {
        "udiv_by_0": w[0],
        "sdiv_by_0": w[1],
        "sdiv_min_neg1": f"0x{w[2]:016x}",
        "adds_u64_max_1": w[3],
        "adds_nzcv": f"0x{w[4]:08x}",
        "clz": w[5],
        "rbit": f"0x{w[6]:016x}",
        "rev": f"0x{w[7]:016x}",
        "lse_cas_prev": w[8],
        "lse_ldadd_prev": w[9],
        "lse_final_mem": w[10],
        "frecpe_3_0_bits": f"0x{w[11]:08x}",
        "frsqrte_3_0_bits": f"0x{w[12]:08x}",
        "aese_aesmc_lo": f"0x{w[13]:016x}",
        "pmull_lo": f"0x{w[14]:016x}",
        "sve_vl_bytes": w[15],
        "sve_uaddv_index": w[16],
        "pacda_signed": f"0x{w[17]:016x}",
        "autda_restored": f"0x{w[18]:016x}",
        "pac_tag_nonzero": (w[17] != raw_ptr and w[18] == raw_ptr),
    }
    print("aarch64 qemu result:", json.dumps(a64_qemu, indent=2))

    res = {
        "host_and_emulator_environment": host,
        "x86_64_native_icelake_server": x64_out,
        "i686_native_vs_qemu_i386": {
            "native_ia32_compat": i686_native,
            "qemu_i386_cpu_max": i686_qemu,
            "divergences_observed": {
                k: {"native": i686_native[k], "qemu_i386": i686_qemu[k]}
                for k in i686_native if i686_native[k] != i686_qemu[k]
            },
        },
        "aarch64_qemu_cpu_max": a64_qemu,
    }
    (RUN_DIR / "m9_hardware_validation_results.json").write_text(json.dumps(res, indent=2))
    print("Wrote m9_hardware_validation_results.json successfully.")

if __name__ == "__main__":
    main()
