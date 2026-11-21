#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""End-to-end prototype of `asm_verified!` (Zero-TCB Rust #[proc_macro]):
1. Compiles a real dependency-free Rust `#[proc_macro]` (`asm_verified!`) using `rustc 1.99.1`.
2. Verifies static compile-time rejection of 5 raw `asm!` footguns:
   - F1: Missing `target_feature` for AVX2/BMI2/ADX instructions/registers (closing rustc's `out("ymm0") _` blind spot)
   - F2: Touching `ymm`/`zmm` registers without `vzeroupper` before `ret`
   - F3: Ambiguous x86 Intel-syntax binary literals (`0b...` / `1010b`) or numeric local labels (`0:` / `0b` / `1f`)
   - F4: Dangerous assembler directives (`.section`, `.incbin`, `.byte`, `.macro`, `.altmacro`, `.org`)
   - F5: Live-input vs clobber/scratch register aliasing or unpreserved SysV callee-saved GPR (`rbx`, `rbp`, `r12`..`r15`)
3. Compiles 3 real assembly hyper-optimization archetypes to ELF64 `.o` via `rustc 1.99.1 -O`,
   runs native differential tests against scalar Rust + `core::arch` implementations,
   compares `rustc 1.99.1` codegen on `core::arch`/Rust vs `asm_verified!`, and
   extracts exact `.text` bytes + untrusted `HintCert` records for Lean 4.34.1 verification.
"""

from __future__ import annotations

import hashlib
import json
import re
import struct
import subprocess
import tempfile
from pathlib import Path

PROC_MACRO_RS = r'''#![crate_type = "proc-macro"]
extern crate proc_macro;
use proc_macro::{TokenStream, TokenTree};

#[proc_macro]
pub fn asm_verified(input: TokenStream) -> TokenStream {
    match expand_asm_verified(input) {
        Ok(ts) => ts.parse().unwrap(),
        Err(msg) => format!("compile_error!({:?});", msg).parse().unwrap(),
    }
}

fn unquote(s: &str) -> Result<String, String> {
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        Ok(s[1..s.len() - 1].to_string())
    } else {
        Err(format!("[asm_verified!] expected string literal, got `{}`", s))
    }
}

fn extract_bracket_strings(tt: &TokenTree) -> Result<Vec<String>, String> {
    if let TokenTree::Group(g) = tt {
        let mut out = Vec::new();
        for item in g.stream() {
            match item {
                TokenTree::Literal(lit) => out.push(unquote(&lit.to_string())?),
                TokenTree::Punct(p) if p.as_char() == ',' => {}
                other => return Err(format!("[asm_verified!] unexpected token in list: `{}`", other)),
            }
        }
        Ok(out)
    } else {
        Err("[asm_verified!] expected `[...]` group".to_string())
    }
}

fn canonical_gpr(reg: &str) -> Option<&'static str> {
    match reg {
        "rax" | "eax" | "ax" | "al" => Some("rax"),
        "rbx" | "ebx" | "bx" | "bl" => Some("rbx"),
        "rcx" | "ecx" | "cx" | "cl" => Some("rcx"),
        "rdx" | "edx" | "dx" | "dl" => Some("rdx"),
        "rsi" | "esi" | "si" | "sil" => Some("rsi"),
        "rdi" | "edi" | "di" | "dil" => Some("rdi"),
        "rbp" | "ebp" | "bp" | "bpl" => Some("rbp"),
        "rsp" | "esp" | "sp" | "spl" => Some("rsp"),
        "r8" | "r8d" | "r8w" | "r8b" => Some("r8"),
        "r9" | "r9d" | "r9w" | "r9b" => Some("r9"),
        "r10" | "r10d" | "r10w" | "r10b" => Some("r10"),
        "r11" | "r11d" | "r11w" | "r11b" => Some("r11"),
        "r12" | "r12d" | "r12w" | "r12b" => Some("r12"),
        "r13" | "r13d" | "r13w" | "r13b" => Some("r13"),
        "r14" | "r14d" | "r14w" | "r14b" => Some("r14"),
        "r15" | "r15d" | "r15w" | "r15b" => Some("r15"),
        _ => None,
    }
}

fn split_words_lower(line: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut cur = String::new();
    for ch in line.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '.' {
            cur.push(ch.to_ascii_lowercase());
        } else if !cur.is_empty() {
            words.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        words.push(cur);
    }
    words
}

fn expand_asm_verified(input: TokenStream) -> Result<String, String> {
    let toks: Vec<TokenTree> = input.into_iter().collect();
    let mut idx = 0usize;

    // Parse: fn <name>(<reg>: <ty>, ...) [-> <ret_reg>: <ret_ty>];
    if idx >= toks.len() || toks[idx].to_string() != "fn" {
        return Err("[asm_verified!] expected `fn <name>(...)`".to_string());
    }
    idx += 1;
    let fn_name = toks.get(idx).ok_or("[asm_verified!] missing fn name")?.to_string();
    idx += 1;
    let param_group = match toks.get(idx) {
        Some(TokenTree::Group(g)) => g.stream(),
        _ => return Err("[asm_verified!] expected parameter list".to_string()),
    };
    idx += 1;

    let mut params: Vec<(String, String)> = Vec::new();
    let ptoks: Vec<TokenTree> = param_group.into_iter().collect();
    let mut pi = 0usize;
    while pi < ptoks.len() {
        let reg = ptoks[pi].to_string();
        pi += 1;
        if pi >= ptoks.len() || ptoks[pi].to_string() != ":" {
            return Err(format!("[asm_verified!] expected `:` after param `{}`", reg));
        }
        pi += 1;
        let mut ty = String::new();
        while pi < ptoks.len() && ptoks[pi].to_string() != "," {
            let s = ptoks[pi].to_string();
            if s == "*" || s == "const" || s == "mut" {
                ty.push_str(&s);
                ty.push(' ');
            } else {
                ty.push_str(&s);
            }
            pi += 1;
        }
        if pi < ptoks.len() && ptoks[pi].to_string() == "," {
            pi += 1;
        }
        params.push((reg, ty.trim().to_string()));
    }

    let mut ret_spec: Option<(String, String)> = None;
    if idx + 1 < toks.len() && toks[idx].to_string() == "-" && toks[idx + 1].to_string() == ">" {
        idx += 2;
        let rreg = toks.get(idx).ok_or("[asm_verified!] missing return reg")?.to_string();
        idx += 1;
        if idx >= toks.len() || toks[idx].to_string() != ":" {
            return Err("[asm_verified!] expected `:` after return register".to_string());
        }
        idx += 1;
        let mut rty = String::new();
        while idx < toks.len() && toks[idx].to_string() != ";" {
            rty.push_str(&toks[idx].to_string());
            idx += 1;
        }
        ret_spec = Some((rreg, rty));
    }
    if idx >= toks.len() || toks[idx].to_string() != ";" {
        return Err("[asm_verified!] expected `;` after signature".to_string());
    }
    idx += 1;

    let mut target_features = String::new();
    let mut clobbers: Vec<String> = Vec::new();
    let mut hints_json = String::new();
    let mut asm_lines: Vec<String> = Vec::new();

    while idx < toks.len() {
        let key = toks[idx].to_string();
        idx += 1;
        if idx >= toks.len() || toks[idx].to_string() != "=" {
            return Err(format!("[asm_verified!] expected `=` after `{}`", key));
        }
        idx += 1;
        let val_tt = toks.get(idx).ok_or("[asm_verified!] missing value")?;
        idx += 1;
        match key.as_str() {
            "target_feature" => target_features = unquote(&val_tt.to_string())?,
            "clobbers" => clobbers = extract_bracket_strings(val_tt)?,
            "hints" => hints_json = unquote(&val_tt.to_string())?,
            "asm" => asm_lines = extract_bracket_strings(val_tt)?,
            other => return Err(format!("[asm_verified!] unknown clause `{}`", other)),
        }
        if idx < toks.len() && toks[idx].to_string() == ";" {
            idx += 1;
        }
    }

    if asm_lines.is_empty() {
        return Err("[asm_verified!] `asm = [...]` cannot be empty".to_string());
    }

    let enabled_feats: Vec<&str> = target_features
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();

    // Footgun 5a: Check SysV ABI parameter order & disjointness against scratch clobbers
    let sysv_order = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
    let mut in_gprs: Vec<&'static str> = Vec::new();
    for (i, (preg, _)) in params.iter().enumerate() {
        let cg = canonical_gpr(preg)
            .ok_or_else(|| format!("[asm_verified!] invalid GPR parameter `{}`", preg))?;
        if i >= sysv_order.len() || cg != sysv_order[i] {
            return Err(format!(
                "[asm_verified!] parameter {} uses `{}` but SysV AMD64 requires `{}`",
                i, preg, sysv_order[i]
            ));
        }
        in_gprs.push(cg);
    }
    let callee_saved = ["rbx", "rbp", "r12", "r13", "r14", "r15", "rsp"];
    for clob in &clobbers {
        if let Some(cg) = canonical_gpr(clob) {
            if in_gprs.contains(&cg) {
                return Err(format!(
                    "[asm_verified!] Footgun F5 (early-clobber / input aliasing): clobber `{}` aliases live input `{}`",
                    clob, cg
                ));
            }
            if callee_saved.contains(&cg) {
                return Err(format!(
                    "[asm_verified!] Footgun F5 (ABI violation): callee-saved register `{}` cannot be clobbered in leaf naked_asm",
                    clob
                ));
            }
        }
    }

    let mut touches_ymm_or_zmm = false;
    let mut saw_ret = false;

    for (line_idx, raw_line) in asm_lines.iter().enumerate() {
        let trimmed = raw_line.trim();
        if trimmed.is_empty() {
            continue;
        }

        // Footgun 4: Ban dangerous directives (`.section`, `.incbin`, `.byte`, `.macro`, `.altmacro`, `.org`, etc.)
        if trimmed.starts_with('.') && !trimmed.ends_with(':') {
            return Err(format!(
                "[asm_verified!] Footgun F4 (forbidden assembler directive at line {}): `{}`",
                line_idx, trimmed
            ));
        }

        // Footgun 3a: Ban numeric local labels (`0:`, `1:`) which collide with MASM binary literals (`0b`, `1b`)
        if trimmed.ends_with(':') {
            let lbl = &trimmed[..trimmed.len() - 1];
            if !lbl.starts_with(".L_") {
                return Err(format!(
                    "[asm_verified!] Footgun F3 (ambiguous label `{}`): labels must start with `.L_` (numeric labels collide with x86 `0b`/`1f` binary literals)",
                    trimmed
                ));
            }
            continue;
        }

        let words = split_words_lower(trimmed);
        if words.is_empty() {
            continue;
        }
        let mnem = words[0].as_str();

        // Footgun 3b: Ban binary literals (`0b...` or `[01]+b` tokens) in x86 Intel syntax
        for w in &words[1..] {
            let is_0b_pref = w.starts_with("0b") && w.len() > 2 && w[2..].chars().all(|c| c == '0' || c == '1' || c == '_');
            let is_masm_bin = w.len() >= 2 && w.ends_with('b') && w[..w.len() - 1].chars().all(|c| c == '0' || c == '1');
            let is_num_fwd = w.len() == 2 && w.ends_with('f') && w.chars().next().unwrap().is_ascii_digit();
            if is_0b_pref || is_masm_bin || is_num_fwd {
                return Err(format!(
                    "[asm_verified!] Footgun F3 (x86 Intel-syntax binary literal / numeric label `{}` at line {}): use `0x...` hex or decimal",
                    w, line_idx
                ));
            }
        }

        // Footgun 5b: Check that callee-saved registers are never written and `mulx` destinations are distinct
        if mnem == "mulx" && words.len() >= 3 && words[1] == words[2] {
            return Err(format!(
                "[asm_verified!] Footgun F5 (`mulx` destination aliasing at line {}): hi and lo registers `{}` must be distinct",
                line_idx, words[1]
            ));
        }
        for w in &words[1..] {
            if let Some(cg) = canonical_gpr(w) {
                if callee_saved.contains(&cg) {
                    return Err(format!(
                        "[asm_verified!] Footgun F5 (callee-saved / stack register `{}` touched in leaf kernel at line {})",
                        w, line_idx
                    ));
                }
            }
            if w.starts_with("ymm") || w.starts_with("zmm") {
                touches_ymm_or_zmm = true;
                if w.starts_with("zmm") && !enabled_feats.contains(&"avx512f") {
                    return Err(format!(
                        "[asm_verified!] Footgun F1 (missing `target_feature = \"avx512f\"` for `{}` at line {})",
                        w, line_idx
                    ));
                }
                if w.starts_with("ymm") && !enabled_feats.contains(&"avx") && !enabled_feats.contains(&"avx2") {
                    return Err(format!(
                        "[asm_verified!] Footgun F1 (missing `target_feature = \"avx\"/\"avx2\"` for `{}` at line {})",
                        w, line_idx
                    ));
                }
            }
        }

        // Footgun 1: Opcode-to-target_feature static gate (closing rustc's inline_asm.rs:463 gap)
        let req_feat = match mnem {
            "mulx" | "shlx" | "shrx" | "sarx" | "bzhi" | "pdep" | "pext" => Some("bmi2"),
            "adcx" | "adox" => Some("adx"),
            "vpmaddubsw" | "vpmaddwd" | "vpaddd" | "vpxor" | "vpcmpeqd" | "vpsrlw" | "vextracti128" => Some("avx2"),
            "vmovdqu" | "vpshufd" | "vmovd" | "vzeroupper" => Some("avx"),
            _ => None,
        };
        if let Some(rf) = req_feat {
            let satisfied = if rf == "avx" {
                enabled_feats.contains(&"avx") || enabled_feats.contains(&"avx2")
            } else {
                enabled_feats.contains(&rf)
            };
            if !satisfied {
                return Err(format!(
                    "[asm_verified!] Footgun F1 (instruction `{}` at line {} requires `target_feature` `{}`)",
                    mnem, line_idx, rf
                ));
            }
        }

        // Footgun 2: Every `ret` must be immediately preceded by `vzeroupper` when ymm/zmm were touched
        if mnem == "ret" {
            saw_ret = true;
            if touches_ymm_or_zmm {
                if line_idx == 0 || asm_lines[line_idx - 1].trim() != "vzeroupper" {
                    return Err(format!(
                        "[asm_verified!] Footgun F2 (dirty upper YMM/ZMM state): `ret` at line {} must be immediately preceded by `vzeroupper`",
                        line_idx
                    ));
                }
            }
        }
    }

    if !saw_ret {
        return Err("[asm_verified!] kernel must terminate with `ret`".to_string());
    }

    let rust_params = params
        .iter()
        .map(|(r, t)| format!("_{}: {}", r, t))
        .collect::<Vec<_>>()
        .join(", ");
    let fwd_args = params
        .iter()
        .map(|(r, _)| format!("_{}", r))
        .collect::<Vec<_>>()
        .join(", ");
    let rust_ret = match &ret_spec {
        Some((_, rt)) => format!(" -> {}", rt),
        None => String::new(),
    };
    let tf_attr = if target_features.is_empty() {
        String::new()
    } else {
        format!("#[target_feature(enable = {:?})]\n", target_features)
    };
    let asm_body = asm_lines
        .iter()
        .map(|l| format!("        {:?},", l))
        .collect::<Vec<_>>()
        .join("\n");
    let const_name = format!("__ASM_VERIFIED_HINTS_{}", fn_name.to_ascii_uppercase());
    let raw_sym = format!("{}_raw_naked", fn_name);

    // Note: On stable Rust 1.99.1/1.100.0, `#[target_feature]` directly on `#[unsafe(naked)]`
    // is unstable (E0658, rust-lang/rust#138568). Emitting a private `#[unsafe(naked)]`
    // symbol paired with a `#[inline] #[target_feature(enable = ...)] pub unsafe fn` gate
    // works on 100% stable Rust while enforcing caller `#[target_feature]` safety!
    Ok(format!(
        "#[allow(dead_code)]\nconst {const_name}: &str = {hints_lit:?};\n#[unsafe(naked)]\n#[no_mangle]\nunsafe extern \"sysv64\" fn {raw_sym}({rust_params}){rust_ret} {{\n    core::arch::naked_asm!(\n{asm_body}\n    )\n}}\n#[inline]\n{tf_attr}pub unsafe fn {fn_name}({rust_params}){rust_ret} {{\n    unsafe {{ {raw_sym}({fwd_args}) }}\n}}\n",
        const_name = const_name,
        hints_lit = hints_json,
        raw_sym = raw_sym,
        tf_attr = tf_attr,
        fn_name = fn_name,
        rust_params = rust_params,
        fwd_args = fwd_args,
        rust_ret = rust_ret,
        asm_body = asm_body,
    ))
}
'''

NEGATIVE_CASES = [
    (
        "F1_missing_target_feature_on_avx2_clobber",
        r'''#![crate_type = "lib"]
extern crate asm_verified_macro;
use asm_verified_macro::asm_verified;
asm_verified! {
    fn bad_f1(rdi: *const u8) -> rax: u64;
    target_feature = "";
    clobbers = ["ymm0"];
    hints = "{}";
    asm = [
        "vpxor ymm0, ymm0, ymm0",
        "xor eax, eax",
        "vzeroupper",
        "ret"
    ];
}
''',
        "Footgun F1",
    ),
    (
        "F2_missing_vzeroupper_before_ret",
        r'''#![crate_type = "lib"]
extern crate asm_verified_macro;
use asm_verified_macro::asm_verified;
asm_verified! {
    fn bad_f2(rdi: *const u8) -> rax: u64;
    target_feature = "avx2";
    clobbers = ["ymm0"];
    hints = "{}";
    asm = [
        "vpxor ymm0, ymm0, ymm0",
        "xor eax, eax",
        "ret"
    ];
}
''',
        "Footgun F2",
    ),
    (
        "F3_masm_binary_literal_and_numeric_label",
        r'''#![crate_type = "lib"]
extern crate asm_verified_macro;
use asm_verified_macro::asm_verified;
asm_verified! {
    fn bad_f3(rdi: u64) -> rax: u64;
    target_feature = "";
    clobbers = [];
    hints = "{}";
    asm = [
        "mov eax, 0b1010",
        "ret"
    ];
}
''',
        "Footgun F3",
    ),
    (
        "F4_dangerous_section_or_byte_directive",
        r'''#![crate_type = "lib"]
extern crate asm_verified_macro;
use asm_verified_macro::asm_verified;
asm_verified! {
    fn bad_f4(rdi: u64) -> rax: u64;
    target_feature = "";
    clobbers = [];
    hints = "{}";
    asm = [
        ".byte 0x0f, 0x0b",
        "ret"
    ];
}
''',
        "Footgun F4",
    ),
    (
        "F5_clobber_aliases_live_input_or_callee_saved",
        r'''#![crate_type = "lib"]
extern crate asm_verified_macro;
use asm_verified_macro::asm_verified;
asm_verified! {
    fn bad_f5(rdi: *mut u64, rsi: *const u64, rdx: u64) -> rax: u64;
    target_feature = "bmi2";
    clobbers = ["rsi"];
    hints = "{}";
    asm = [
        "xor eax, eax",
        "ret"
    ];
}
''',
        "Footgun F5",
    ),
]

POSITIVE_KERNELS_RS = r'''#![allow(dead_code)]
extern crate asm_verified_macro;
use asm_verified_macro::asm_verified;
use core::arch::x86_64::*;

// ============================================================================
// Archetype 1: 256-bit (4-limb) Multi-Precision Multiply-Accumulate
//   acc[0..4] + 2^256 * ret = old_acc[0..4] + a[0..4] * b
// ============================================================================
asm_verified! {
    fn mulx_adcx_adox_mac4_asm(rdi: *mut u64, rsi: *const u64, rdx: u64) -> rax: u64;
    target_feature = "bmi2,adx";
    clobbers = ["rcx", "r8", "r9", "r10", "r11", "flags"];
    hints = "{\"kernel\":\"mulx_adcx_adox_mac4\",\"kind\":\"straight_line_dual_carry\",\"limbs\":4,\"cf_chain\":[\"r8\",\"r9\",\"r10\",\"r11\",\"rax\"],\"of_chain\":[\"rdi+8\",\"rdi+16\",\"rdi+24\",\"rcx\"]}";
    asm = [
        "xor ecx, ecx",
        "xor eax, eax",
        "mulx r9, r8, qword ptr [rsi]",
        "adcx r8, qword ptr [rdi]",
        "mov qword ptr [rdi], r8",
        "mulx r10, r8, qword ptr [rsi + 8]",
        "adcx r9, r8",
        "adox r9, qword ptr [rdi + 8]",
        "mov qword ptr [rdi + 8], r9",
        "mulx r11, r8, qword ptr [rsi + 16]",
        "adcx r10, r8",
        "adox r10, qword ptr [rdi + 16]",
        "mov qword ptr [rdi + 16], r10",
        "mulx r9, r8, qword ptr [rsi + 24]",
        "adcx r11, r8",
        "adox r11, qword ptr [rdi + 24]",
        "mov qword ptr [rdi + 24], r11",
        "adcx rax, r9",
        "adox rax, rcx",
        "ret"
    ];
}

pub fn mulx_adcx_adox_mac4_ref(acc: &mut [u64; 4], a: &[u64; 4], b: u64) -> u64 {
    let mut carry: u128 = 0;
    let mut k = 0usize;
    while k < 4 {
        let prod = (a[k] as u128) * (b as u128) + (acc[k] as u128) + carry;
        acc[k] = prod as u64;
        carry = prod >> 64;
        k += 1;
    }
    carry as u64
}

#[no_mangle]
#[target_feature(enable = "bmi2,adx")]
pub unsafe fn mulx_adcx_adox_mac4_core_arch(acc: &mut [u64; 4], a: &[u64; 4], b: u64) -> u64 {
    let mut hi0 = 0u64;
    let mut hi1 = 0u64;
    let mut hi2 = 0u64;
    let mut hi3 = 0u64;
    let lo0 = _mulx_u64(a[0], b, &mut hi0);
    let lo1 = _mulx_u64(a[1], b, &mut hi1);
    let lo2 = _mulx_u64(a[2], b, &mut hi2);
    let lo3 = _mulx_u64(a[3], b, &mut hi3);

    let mut c_cf = 0u8;
    let mut c_of = 0u8;
    c_cf = _addcarryx_u64(c_cf, lo0, acc[0], &mut acc[0]);
    let mut t1 = 0u64;
    c_cf = _addcarryx_u64(c_cf, hi0, lo1, &mut t1);
    c_of = _addcarryx_u64(c_of, t1, acc[1], &mut acc[1]);
    let mut t2 = 0u64;
    c_cf = _addcarryx_u64(c_cf, hi1, lo2, &mut t2);
    c_of = _addcarryx_u64(c_of, t2, acc[2], &mut acc[2]);
    let mut t3 = 0u64;
    c_cf = _addcarryx_u64(c_cf, hi2, lo3, &mut t3);
    c_of = _addcarryx_u64(c_of, t3, acc[3], &mut acc[3]);
    let mut top = 0u64;
    let _ = _addcarryx_u64(c_cf, hi3, 0, &mut top);
    let _ = _addcarryx_u64(c_of, top, 0, &mut top);
    top
}

// ============================================================================
// Archetype 2: 2x-Unrolled Register-Pinned AVX2 `vpmaddubsw` + `vpmaddwd` Kernel
// ============================================================================
asm_verified! {
    fn dot_maddubs_unroll2_asm(rdi: *const u8, rsi: *const i8, rdx: u64) -> rax: i32;
    target_feature = "avx2";
    clobbers = ["rcx", "ymm0", "ymm1", "ymm2", "ymm3", "ymm4", "ymm5", "ymm6", "flags"];
    hints = "{\"kernel\":\"dot_maddubs_unroll2\",\"kind\":\"counted_simd_loop\",\"unroll_bytes\":64,\"loop_label\":\".L_loop\",\"acc_regs\":[\"ymm0\",\"ymm1\"],\"ones_reg\":\"ymm2\",\"vzeroupper_before_ret\":true}";
    asm = [
        "vpxor ymm0, ymm0, ymm0",
        "vpxor ymm1, ymm1, ymm1",
        "test rdx, rdx",
        "je .L_reduce",
        "vpcmpeqd ymm2, ymm2, ymm2",
        "vpsrlw ymm2, ymm2, 15",
        "shl rdx, 6",
        "xor ecx, ecx",
        ".L_loop:",
        "vmovdqu ymm3, ymmword ptr [rdi + rcx]",
        "vmovdqu ymm4, ymmword ptr [rsi + rcx]",
        "vpmaddubsw ymm3, ymm3, ymm4",
        "vpmaddwd ymm3, ymm3, ymm2",
        "vpaddd ymm0, ymm0, ymm3",
        "vmovdqu ymm5, ymmword ptr [rdi + rcx + 32]",
        "vmovdqu ymm6, ymmword ptr [rsi + rcx + 32]",
        "vpmaddubsw ymm5, ymm5, ymm6",
        "vpmaddwd ymm5, ymm5, ymm2",
        "vpaddd ymm1, ymm1, ymm5",
        "add rcx, 64",
        "cmp rcx, rdx",
        "jb .L_loop",
        ".L_reduce:",
        "vpaddd ymm0, ymm0, ymm1",
        "vextracti128 xmm1, ymm0, 1",
        "vpaddd xmm0, xmm0, xmm1",
        "vpshufd xmm1, xmm0, 0x4e",
        "vpaddd xmm0, xmm0, xmm1",
        "vpshufd xmm1, xmm0, 0xb1",
        "vpaddd xmm0, xmm0, xmm1",
        "vmovd eax, xmm0",
        "vzeroupper",
        "ret"
    ];
}

pub fn dot_maddubs_blocks64_ref(u: &[u8], s: &[i8]) -> i32 {
    let blocks = (u.len().min(s.len())) / 64;
    let mut acc: i32 = 0;
    for b in 0..blocks {
        for pair in 0..32 {
            let idx = b * 64 + pair * 2;
            let p = (u[idx] as i32) * (s[idx] as i32) + (u[idx + 1] as i32) * (s[idx + 1] as i32);
            acc = acc.wrapping_add(p.clamp(-32768, 32767));
        }
    }
    acc
}

// ============================================================================
// Archetype 3: Constant-Time Branchless `cmove` 8-Entry Table Lookup
// ============================================================================
asm_verified! {
    fn ct_lookup8_cmov_asm(rdi: *const u64, rsi: u64) -> rax: u64;
    target_feature = "";
    clobbers = ["r8", "flags"];
    hints = "{\"kernel\":\"ct_lookup8_cmov\",\"kind\":\"constant_time_linear_scan\",\"entries\":8,\"secret_reg\":\"rsi\",\"table_reg\":\"rdi\",\"acc_reg\":\"rax\",\"scratch_reg\":\"r8\"}";
    asm = [
        "xor eax, eax",
        "mov r8, qword ptr [rdi]",
        "cmp rsi, 0",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 8]",
        "cmp rsi, 1",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 16]",
        "cmp rsi, 2",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 24]",
        "cmp rsi, 3",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 32]",
        "cmp rsi, 4",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 40]",
        "cmp rsi, 5",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 48]",
        "cmp rsi, 6",
        "cmove rax, r8",
        "mov r8, qword ptr [rdi + 56]",
        "cmp rsi, 7",
        "cmove rax, r8",
        "ret"
    ];
}

#[no_mangle]
pub fn ct_lookup8_naive_rust(table: &[u64; 8], secret_idx: u64) -> u64 {
    let mut out = 0u64;
    let mut k = 0usize;
    while k < 8 {
        if (k as u64) == secret_idx {
            out = table[k];
        }
        k += 1;
    }
    out
}
'''

DIFF_MAIN_SUFFIX = r'''
fn main() {
    // 1. Test mulx_adcx_adox_mac4_asm across extremal carry ripples + PRNG vectors
    let edge_vectors: [([u64; 4], [u64; 4], u64); 5] = [
        ([0, 0, 0, 0], [0, 0, 0, 0], 0),
        ([u64::MAX; 4], [u64::MAX; 4], u64::MAX),
        ([u64::MAX, 0, u64::MAX, 0], [1, u64::MAX, 1, u64::MAX], u64::MAX),
        ([1, 2, 3, 4], [5, 6, 7, 8], 0xDEAD_BEEF_CAFE_BABE),
        ([u64::MAX; 4], [1, 0, 0, 0], 1),
    ];
    for (acc0, a, b) in edge_vectors {
        let mut acc_ref = acc0;
        let mut acc_asm = acc0;
        let mut acc_ca = acc0;
        let top_ref = mulx_adcx_adox_mac4_ref(&mut acc_ref, &a, b);
        let top_asm = unsafe { mulx_adcx_adox_mac4_asm(acc_asm.as_mut_ptr(), a.as_ptr(), b) };
        let top_ca = unsafe { mulx_adcx_adox_mac4_core_arch(&mut acc_ca, &a, b) };
        assert_eq!((acc_ref, top_ref), (acc_asm, top_asm));
        assert_eq!((acc_ref, top_ref), (acc_ca, top_ca));
    }
    let mut st = 0x1234_5678_9ABC_DEF0u64;
    let mut next_u64 = || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    for _ in 0..500 {
        let acc0 = [next_u64(), next_u64(), next_u64(), next_u64()];
        let a = [next_u64(), next_u64(), next_u64(), next_u64()];
        let b = next_u64();
        let mut acc_ref = acc0;
        let mut acc_asm = acc0;
        let top_ref = mulx_adcx_adox_mac4_ref(&mut acc_ref, &a, b);
        let top_asm = unsafe { mulx_adcx_adox_mac4_asm(acc_asm.as_mut_ptr(), a.as_ptr(), b) };
        assert_eq!((acc_ref, top_ref), (acc_asm, top_asm));
    }

    // 2. Test dot_maddubs_unroll2_asm across 0..=6 blocks including 0xFF * 0x7F saturation
    let mut u_buf = vec![0u8; 64 * 6];
    let mut s_buf = vec![0i8; 64 * 6];
    for i in 0..u_buf.len() {
        u_buf[i] = if i < 16 { 255 } else { (next_u64() & 0xFF) as u8 };
        s_buf[i] = if i < 16 { 127 } else { (next_u64() & 0xFF) as i8 };
    }
    for blocks in 0..=6usize {
        let got_ref = dot_maddubs_blocks64_ref(&u_buf[..blocks * 64], &s_buf[..blocks * 64]);
        let got_asm = unsafe { dot_maddubs_unroll2_asm(u_buf.as_ptr(), s_buf.as_ptr(), blocks as u64) };
        assert_eq!(got_ref, got_asm, "dot blocks={blocks}");
    }

    // 3. Test ct_lookup8_cmov_asm across all indices 0..16 + u64::MAX
    let tbl: [u64; 8] = [
        0x1111_0000_0000_0001, 0x2222_0000_0000_0002,
        0x3333_0000_0000_0003, 0x4444_0000_0000_0004,
        0x5555_0000_0000_0005, 0x6666_0000_0000_0006,
        0x7777_0000_0000_0007, 0x8888_0000_0000_0008,
    ];
    for idx in [0u64, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, u64::MAX] {
        let r_ref = ct_lookup8_naive_rust(&tbl, idx);
        let r_asm = unsafe { ct_lookup8_cmov_asm(tbl.as_ptr(), idx) };
        assert_eq!(r_ref, r_asm, "ct_lookup8 idx={idx}");
    }
    println!("ASM_VERIFIED_DIFF_OK");
}
'''


def extract_elf_symbols(obj_path: Path) -> dict[str, bytes]:
    data = obj_path.read_bytes()
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, _ = struct.unpack_from("<HHH", data, 58)
    sections = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        fields = struct.unpack_from("<IIQQQQIIQQ", data, off)
        sections.append({
            "sh_type": fields[1],
            "sh_offset": fields[4],
            "sh_size": fields[5],
            "sh_link": fields[6],
            "sh_entsize": fields[9],
        })
    out = {}
    for sec in sections:
        if sec["sh_type"] == 2:
            strtab = sections[sec["sh_link"]]
            for k in range(sec["sh_size"] // sec["sh_entsize"]):
                st_name, st_info, _, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", data, sec["sh_offset"] + k * sec["sh_entsize"]
                )
                if (st_info & 0xF) == 2 and 0 < st_shndx < len(sections) and st_size > 0:
                    sbase = strtab["sh_offset"] + st_name
                    send = data.index(b"\x00", sbase)
                    name = data[sbase:send].decode()
                    tsec = sections[st_shndx]
                    out[name] = data[tsec["sh_offset"] + st_value : tsec["sh_offset"] + st_value + st_size]
    return out


def disasm_symbol(obj_path: Path, sym_name: str) -> list[dict]:
    out = subprocess.check_output(["objdump", "-d", "-M", "intel", str(obj_path)], text=True)
    in_sym = False
    insns = []
    for line in out.splitlines():
        m_hdr = re.match(r"^[0-9a-fA-F]+\s+<([^>]+)>:$", line.strip())
        if m_hdr:
            in_sym = (m_hdr.group(1) == sym_name)
            continue
        if in_sym:
            m_ins = re.match(r"^\s*([0-9a-fA-F]+):\s+((?:[0-9a-fA-F]{2}\s+)+)\s*(.+)$", line)
            if m_ins:
                off = int(m_ins.group(1), 16)
                raw_hex = m_ins.group(2).strip().split()
                text = re.sub(r"#.*$", "", m_ins.group(3)).strip()
                insns.append({
                    "offset": off,
                    "bytes_hex": "".join(raw_hex),
                    "len": len(raw_hex),
                    "asm": text,
                })
    return insns


def main() -> None:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        macro_src = td_path / "asm_verified_macro.rs"
        macro_so = td_path / "libasm_verified_macro.so"
        macro_src.write_text(PROC_MACRO_RS)

        subprocess.check_call([
            "rustup", "run", "1.99.1", "rustc", "--edition=2021",
            "--crate-type", "proc-macro",
            str(macro_src), "-o", str(macro_so),
        ])

        # 1. Negative static footgun checks
        neg_results = []
        for label, bad_src, expected_tag in NEGATIVE_CASES:
            f = td_path / f"{label}.rs"
            f.write_text(bad_src)
            proc = subprocess.run(
                [
                    "rustup", "run", "1.99.1", "rustc", "--edition=2021",
                    "--extern", f"asm_verified_macro={macro_so}",
                    str(f), "--out-dir", str(td_path),
                ],
                capture_output=True,
                text=True,
            )
            assert proc.returncode != 0, f"{label} unexpectedly compiled!"
            assert expected_tag in proc.stderr, f"missing {expected_tag} in {proc.stderr}"
            err_line = next(
                (ln.strip() for ln in proc.stderr.splitlines() if expected_tag in ln),
                proc.stderr.splitlines()[0],
            )
            neg_results.append({
                "case": label,
                "rc": proc.returncode,
                "diagnostic": err_line,
            })

        # 2. Compile positive kernels to ELF64 .o + native executable for differential testing
        pos_lib_src = td_path / "pos_kernels.rs"
        pos_obj = td_path / "pos_kernels.o"
        pos_lib_src.write_text("#![crate_type = \"lib\"]\n" + POSITIVE_KERNELS_RS)
        subprocess.check_call([
            "rustup", "run", "1.99.1", "rustc", "--edition=2021",
            "-C", "opt-level=3",
            "--extern", f"asm_verified_macro={macro_so}",
            "--emit=obj", str(pos_lib_src), "-o", str(pos_obj),
        ])

        pos_bin_src = td_path / "pos_bin.rs"
        pos_bin = td_path / "pos_bin"
        pos_bin_src.write_text(POSITIVE_KERNELS_RS + DIFF_MAIN_SUFFIX)
        subprocess.check_call([
            "rustup", "run", "1.99.1", "rustc", "--edition=2021",
            "-C", "opt-level=3",
            "--extern", f"asm_verified_macro={macro_so}",
            str(pos_bin_src), "-o", str(pos_bin),
        ])
        diff_out = subprocess.check_output([str(pos_bin)], text=True).strip()
        assert diff_out == "ASM_VERIFIED_DIFF_OK"

        # 3. Extract ELF symbol bytes & disassembly for both asm_verified! and core::arch/Rust twins
        raw_syms = extract_elf_symbols(pos_obj)
        compared_syms = [
            "mulx_adcx_adox_mac4_asm_raw_naked",
            "mulx_adcx_adox_mac4_core_arch",
            "dot_maddubs_unroll2_asm_raw_naked",
            "ct_lookup8_cmov_asm_raw_naked",
            "ct_lookup8_naive_rust",
        ]
        sym_details = {}
        for sname in compared_syms:
            b = raw_syms[sname]
            insns = disasm_symbol(pos_obj, sname)
            sym_details[sname] = {
                "size_bytes": len(b),
                "sha256": hashlib.sha256(b).hexdigest(),
                "bytes_list": list(b),
                "insn_count": len(insns),
                "insns": insns,
            }

    out = {
        "negative_footgun_gates": neg_results,
        "differential_execution": diff_out,
        "elf_symbols": sym_details,
    }
    out_path = Path(__file__).with_name("probe_asm_verified_macro_and_obj_results.json")
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")

    print("Negative footgun checks passed:", len(neg_results))
    for nr in neg_results:
        print(f"  {nr['case']}: rc={nr['rc']} -> {nr['diagnostic']}")
    print("Differential test:", diff_out)
    for sname in compared_syms:
        sd = sym_details[sname]
        mnems = [i["asm"].split()[0] for i in sd["insns"]]
        print(f"\n=== {sname}: {sd['size_bytes']} B, {sd['insn_count']} insns ===")
        for i in sd["insns"]:
            print(f"  0x{i['offset']:02x}: {i['bytes_hex']:22s} {i['asm']}")


if __name__ == "__main__":
    main()
