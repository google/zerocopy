// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone `rustc_driver` v2 implementing:
//!
//! 1. Dual-query (`providers.queries.optimized_mir` and
//!    `providers.extern_queries.optimized_mir`) post-expansion `InlineAsm`
//!    attestation rewriting, emitting DWARF-tombstoned `.debug_anneal_sites`
//!    and `.debug_anneal_descs` sections via zero-drift `cr_zero_drift` (`\r` +
//!    `.space 0 <cmt>`) framing while capturing prebuilt sysroot `libcore`
//!    `stdarch` inline assembly without double-wrapping upstream crates.
//!
//! 2. Complete `TyCtxt` transitive type-graph and pointee-validity closure in
//!    `SpecConeCollector` (`ty.walk()`, `ty::Ref`, `ty::RawPtr`, `ty::Adt`,
//!    `ty::Slice`, `ty::Array`, `ty::Tuple`, `ty::FnPtr` + `fn_abi_of_fn_ptr`,
//!    stepwise `Place::iter_projections()` `PlaceRef::ty`, and foreign/local
//!    `GlobalAlloc::Static` `type_of` + mutability + `codegen_fn_attrs`).

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::process::ExitCode;
use std::sync::Mutex;

use rustc_abi::{FieldsShape, Variants};
use rustc_ast::ast::{InlineAsmOptions, InlineAsmTemplatePiece};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_interface::interface;
use rustc_middle::mir::interpret::{ConstAllocation, GlobalAlloc};
use rustc_middle::mir::{
    Body, Const, ConstOperand, ConstValue, InlineAsmMacro, InlineAsmOperand,
    Operand, Place, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{
    self, Instance, InstanceKind, Ty, TyCtxt, TypeVisitableExt,
};
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_span::DUMMY_SP;
use rustc_target::spec::Arch;

#[derive(Clone)]
struct RewrittenSiteMeta {
    site_id: u64,
    crate_name: String,
    def_path: String,
    is_local: bool,
    bb_idx: usize,
    session_nonce: String,
}

thread_local! {
    // Arena-allocated `&'tcx Body<'tcx>` snapshots of `Runtime(PostCleanup)`
    // MIR captured right before `optimized_mir` steals them during `rlib`
    // `cross_crate_inlinable` reachability checks.
    static SAVED_POSTCLEANUP_MIR: RefCell<BTreeMap<u32, usize>> =
        const { RefCell::new(BTreeMap::new()) };

    // Arena-allocated `&'tcx Body<'tcx>` snapshots of un-rewritten foreign
    // `extern_queries.optimized_mir` bodies so `SpecConeCollector` remains
    // invariant to `session_nonce` injection when both features run together.
    static SAVED_EXTERN_MIR: RefCell<BTreeMap<(u32, u32), usize>> =
        const { RefCell::new(BTreeMap::new()) };
}

// Process-wide mutex so `run_compiler`'s dedicated `rustc` worker thread and
// parallel query threads share the rewritten-site manifest with `main()`.
static REWRITTEN_SITES: Mutex<BTreeMap<(u64, usize), RewrittenSiteMeta>> =
    Mutex::new(BTreeMap::new());

// --- Minimal FIPS 180-4 SHA-256 (zero external crate dependencies) ---

fn scrub_raw_def_indices(raw: &str) -> String {
    // Strip HIR-order-sensitive `<krate>:<def_idx> ~ ` inside `DefId(...)`
    // so inserting unrelated items earlier in a file never perturbs keys.
    let mut out = String::with_capacity(raw.len());
    let mut rest = raw;
    while let Some(pos) = rest.find("DefId(") {
        out.push_str(&rest[..pos + 6]);
        let after = &rest[pos + 6..];
        if let Some(tilde) = after.find(" ~ ") {
            let prefix = &after[..tilde];
            if prefix.chars().all(|c| c.is_ascii_digit() || c == ':') {
                rest = &after[tilde + 3..];
                continue;
            }
        }
        rest = after;
    }
    out.push_str(rest);
    out
}

struct Sha256 {
    state: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
    total_bits: u64,
    scrub_def_idx: bool,
}

impl Sha256 {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
        0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];

    fn new() -> Self {
        Self::new_for_cone(false)
    }

    fn new_for_cone(scrub_def_idx: bool) -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
            ],
            buf: [0u8; 64],
            buf_len: 0,
            total_bits: 0,
            scrub_def_idx,
        }
    }

    fn compress(state: &mut [u32; 8], block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[4 * i],
                block[4 * i + 1],
                block[4 * i + 2],
                block[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7)
                ^ w[i - 15].rotate_right(18)
                ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17)
                ^ w[i - 2].rotate_right(19)
                ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(Self::K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }

    fn update(&mut self, mut data: &[u8]) {
        self.total_bits = self.total_bits.wrapping_add((data.len() as u64) * 8);
        if self.buf_len > 0 {
            let take = (64 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take]
                .copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == 64 {
                Self::compress(&mut self.state, &self.buf);
                self.buf_len = 0;
            }
        }
        while data.len() >= 64 {
            let block: &[u8; 64] = data[..64].try_into().unwrap();
            Self::compress(&mut self.state, block);
            data = &data[64..];
        }
        if !data.is_empty() {
            self.buf[..data.len()].copy_from_slice(data);
            self.buf_len = data.len();
        }
    }

    fn update_tag(&mut self, tag: &str, val: &str) {
        let scrubbed: Cow<'_, str> = if self.scrub_def_idx && val.contains("DefId(") {
            Cow::Owned(scrub_raw_def_indices(val))
        } else {
            Cow::Borrowed(val)
        };
        self.update(tag.as_bytes());
        self.update(b":");
        self.update(&(scrubbed.len() as u64).to_le_bytes());
        self.update(scrubbed.as_bytes());
        self.update(b"\n");
    }

    fn finalize(mut self) -> [u8; 32] {
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > 56 {
            self.buf[self.buf_len..64].fill(0);
            Self::compress(&mut self.state, &self.buf);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..56].fill(0);
        self.buf[56..64].copy_from_slice(&self.total_bits.to_be_bytes());
        Self::compress(&mut self.state, &self.buf);
        let mut out = [0u8; 32];
        for (i, word) in self.state.iter().enumerate() {
            out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
        }
        out
    }

    fn hex(data: &[u8]) -> String {
        let mut s = String::with_capacity(data.len() * 2);
        for b in data {
            use std::fmt::Write;
            let _ = write!(&mut s, "{b:02x}");
        }
        s
    }
}

fn session_nonce() -> String {
    if let Ok(v) = std::env::var("ANNEAL_SESSION_NONCE") {
        if !v.is_empty() {
            return v;
        }
    }
    let mut raw = [0u8; 16];
    if let Ok(mut f) = fs::File::open("/dev/urandom") {
        use std::io::Read;
        let _ = f.read_exact(&mut raw);
    }
    Sha256::hex(&raw)
}

fn target_comment_prefix(arch: &Arch) -> &'static str {
    match arch {
        Arch::AArch64 | Arch::Arm64EC => "//",
        Arch::Arm => "@",
        _ => "#",
    }
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

// --- Part 1: Dual-Query Post-Expansion MIR InlineAsm Rewriter ---

fn derive_disjoint_labels(nonce: &str, site_id: u64, user_text: &str) -> [u64; 4] {
    let mut salt: u64 = 0;
    loop {
        let mut h = Sha256::new();
        h.update(nonce.as_bytes());
        h.update(&site_id.to_le_bytes());
        h.update(&salt.to_le_bytes());
        let digest = h.finalize();
        let mut labels = [0u64; 4];
        for i in 0..4 {
            let raw = u32::from_le_bytes([
                digest[4 * i],
                digest[4 * i + 1],
                digest[4 * i + 2],
                digest[4 * i + 3],
            ]) as u64;
            // Leading digit 2..8 avoids Intel-syntax binary literal lexing on
            // `<id>b` directional references.
            labels[i] = 200_000_000 + (raw % 700_000_000) + (i as u64);
        }
        let distinct = labels[0] != labels[1]
            && labels[0] != labels[2]
            && labels[0] != labels[3]
            && labels[1] != labels[2]
            && labels[1] != labels[3]
            && labels[2] != labels[3];
        let collides = labels.iter().any(|l| user_text.contains(&l.to_string()));
        if distinct && !collides {
            return labels;
        }
        salt += 1;
    }
}

fn section_pair_for_mode(mode: &str) -> (&'static str, &'static str, &'static str) {
    match mode {
        // Unified v2 mode: `.debug_*` prefix guarantees `SEC_DEBUGGING` GC root
        // retention in GNU `ld.bfd` AND DWARF dead-section `(0, 0)` /
        // `UINT64_MAX` tombstoning across `ld.bfd`, `rust-lld`, and `ld.mold`,
        // with zero `PT_LOAD` footprint.
        "debug_tombstone_cr" | "cr_zero_drift_debug" => {
            (".debug_anneal_sites", ".debug_anneal_descs", "")
        }
        // Non-`SHF_EXCLUDE`, non-`.debug_*` mode for reproducing `--gc-sections`
        // `ld.bfd` 0-byte stripping and `lld`/`mold` `STT_SECTION + r_addend`
        // phantom non-zero-length spans.
        "non_exclude_cr" => (".anneal.asm_sites", ".anneal.asm_descs", ""),
        // Legacy v1 `SHF_EXCLUDE` mode (discarded by linkers before relaxation).
        _ => (".anneal.asm_sites", ".anneal.asm_descs", "e"),
    }
}

fn rewrite_body_inline_asm<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &mut Body<'tcx>,
    mode: &str,
) {
    let nonce = session_nonce();
    let cmt = target_comment_prefix(&tcx.sess.target.arch);
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    let def_path_hash = tcx.def_path_hash(def_id);
    let def_path = format!("{crate_name}::{}", tcx.def_path_str(def_id));
    let (sites_sec, descs_sec, sec_flags) = section_pair_for_mode(mode);

    for (bb_idx, bb_data) in
        body.basic_blocks.as_mut_preserves_cfg().iter_enumerated_mut()
    {
        let Some(term) = bb_data.terminator.as_mut() else {
            continue;
        };
        let TerminatorKind::InlineAsm {
            asm_macro,
            ref mut template,
            ref operands,
            options,
            ref mut line_spans,
            ..
        } = term.kind
        else {
            continue;
        };

        let mut user_concat = String::new();
        for p in template.iter() {
            if let InlineAsmTemplatePiece::String(s) = p {
                user_concat.push_str(s);
            }
        }

        // Idempotence guard: when an upstream `.rmeta` crate was already
        // instrumented by `anneal_driver_v2`, preserve its original attestation
        // wrapper and upstream `session_nonce` without double-wrapping.
        if user_concat.contains(".debug_anneal_sites")
            || user_concat.contains(".anneal.asm_sites")
        {
            continue;
        }

        let lower_check = user_concat.to_ascii_lowercase();
        for forbidden in [".macro", ".altmacro", ".rept", ".irp", ".irpc"] {
            if lower_check.contains(forbidden) {
                tcx.dcx().span_err(
                    term.source_info.span,
                    format!(
                        "anneal-driver: assembler directive `{forbidden}` \
                         forbidden in verified asm"
                    ),
                );
                return;
            }
        }

        let mut sh = Sha256::new();
        sh.update_tag("crate", &crate_name);
        sh.update_tag("def_path_hash", &format!("{def_path_hash:?}"));
        sh.update(&(bb_idx.index() as u64).to_le_bytes());
        let site_digest = sh.finalize();
        let site_id =
            u64::from_le_bytes(site_digest[0..8].try_into().unwrap())
                & 0x7fff_ffff_ffff_ffff;

        if let Ok(mut map) = REWRITTEN_SITES.lock() {
            map.insert(
                (site_id, bb_idx.index()),
                RewrittenSiteMeta {
                    site_id,
                    crate_name: crate_name.clone(),
                    def_path: def_path.clone(),
                    is_local: def_id.is_local(),
                    bb_idx: bb_idx.index(),
                    session_nonce: nonce.clone(),
                },
            );
        }

        let [l_s, l_e, l_d, l_de] =
            derive_disjoint_labels(&nonce, site_id, &user_concat);

        let is_naked = matches!(asm_macro, InlineAsmMacro::NakedAsm);
        let mut desc_pieces: Vec<InlineAsmTemplatePiece> = Vec::new();
        let mut reloc_indices: Vec<usize> = Vec::new();
        let use_cr = mode != "multiline_pushsection";
        let sep = if use_cr { "\r" } else { "\n" };

        desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
            "{nonce}|site={site_id}|crate={crate_name}"
        ))));

        for (op_idx, op) in operands.iter().enumerate() {
            match op {
                InlineAsmOperand::In { .. } if !is_naked => {
                    desc_pieces.push(InlineAsmTemplatePiece::String(
                        Cow::Owned(format!("|in{op_idx}=")),
                    ));
                    desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                        operand_idx: op_idx,
                        modifier: None,
                        span: DUMMY_SP,
                    });
                }
                InlineAsmOperand::Out { reg, place, .. } if !is_naked => {
                    match place {
                        Some(_) => {
                            desc_pieces.push(InlineAsmTemplatePiece::String(
                                Cow::Owned(format!("|out{op_idx}=")),
                            ));
                            desc_pieces.push(
                                InlineAsmTemplatePiece::Placeholder {
                                    operand_idx: op_idx,
                                    modifier: None,
                                    span: DUMMY_SP,
                                },
                            );
                        }
                        None => {
                            // `Display` on `InlineAsmRegOrRegClass::Reg` wraps
                            // the register name in `"..."` (e.g. `"x1"`), which
                            // would terminate `.asciz "..."` prematurely unless
                            // stripped.
                            let clean_reg = reg.to_string().replace('"', "");
                            desc_pieces.push(InlineAsmTemplatePiece::String(
                                Cow::Owned(format!("|clob{op_idx}={clean_reg}")),
                            ));
                        }
                    }
                }
                InlineAsmOperand::InOut { out_place, .. } if !is_naked => {
                    let kind_tag = if out_place.is_some() {
                        "inout"
                    } else {
                        "inout_clob"
                    };
                    desc_pieces.push(InlineAsmTemplatePiece::String(
                        Cow::Owned(format!("|{kind_tag}{op_idx}=")),
                    ));
                    desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                        operand_idx: op_idx,
                        modifier: None,
                        span: DUMMY_SP,
                    });
                }
                InlineAsmOperand::Const { .. } => {
                    desc_pieces.push(InlineAsmTemplatePiece::String(
                        Cow::Owned(format!("|const{op_idx}=")),
                    ));
                    desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                        operand_idx: op_idx,
                        modifier: None,
                        span: DUMMY_SP,
                    });
                }
                InlineAsmOperand::SymFn { .. }
                | InlineAsmOperand::SymStatic { .. } => {
                    reloc_indices.push(op_idx);
                }
                InlineAsmOperand::Label { .. } if !is_naked => {
                    reloc_indices.push(op_idx);
                }
                _ => {}
            }
        }

        // Under ATT_SYNTAX (`x86/eflags.rs` uses `options(nomem, att_syntax)`!),
        // bare register placeholders expand with a leading `%` (`%rax`), which is
        // completely safe inside `.asciz "..."`. However, in `.quad <sym>`, AT&T
        // syntax prints `$sym` unless `:c` is passed (`asm.rs` handles `Sym*`),
        // and `.space 0 #` works identically under both AT&T and Intel syntax.
        let _ = options.contains(InlineAsmOptions::ATT_SYNTAX);

        let mut new_pieces: Vec<InlineAsmTemplatePiece> = Vec::new();
        if use_cr {
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                ".space 0 {cmt}\r{l_s}:\n"
            ))));
        } else {
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "{l_s}:\n"
            ))));
        }
        new_pieces.extend(template.iter().cloned());
        if use_cr {
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "\r.space 0 {cmt}\r{l_e}:\r\
                 .pushsection {descs_sec},\"{sec_flags}\",@progbits\r\
                 {l_d}: .asciz \""
            ))));
        } else {
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "\n{l_e}:\n\
                 .pushsection {descs_sec},\"{sec_flags}\",@progbits\n\
                 {l_d}: .asciz \""
            ))));
        }
        new_pieces.extend(desc_pieces);
        let n_rel = reloc_indices.len();
        // 7-word (56-byte) fixed record header:
        //   [0] start_va  (`.quad {l_s}b` -> tombstoned to 0 / UINT64_MAX on GC/ICF)
        //   [1] end_va    (`.quad {l_e}b` -> tombstoned to 0 / UINT64_MAX on GC/ICF)
        //   [2] span_len  (`.quad {l_e}b - {l_s}b` -> ADD64/SUB64 under R_RISCV_RELAX)
        //   [3] site_id   (63-bit deterministic `(crate, DefPathHash, bb)` digest)
        //   [4] desc_off  (`.quad {l_d}b` -> merged byte offset in `.debug_anneal_descs`)
        //   [5] desc_len  (`.quad {l_de}b - {l_d}b` -> byte length including NUL)
        //   [6] n_rel     (count of trailing `.quad <sym_or_lbl>` relocations)
        new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
            "\"{sep}{l_de}: .popsection{sep}\
             .pushsection {sites_sec},\"{sec_flags}\",@progbits{sep}\
             .quad {l_s}b, {l_e}b, {l_e}b - {l_s}b, {site_id}, \
             {l_d}b, {l_de}b - {l_d}b, {n_rel}"
        ))));
        for r_idx in reloc_indices {
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "{sep}.quad "
            ))));
            new_pieces.push(InlineAsmTemplatePiece::Placeholder {
                operand_idx: r_idx,
                modifier: None,
                span: DUMMY_SP,
            });
        }
        new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
            "{sep}.popsection"
        ))));

        let new_line_count = new_pieces
            .iter()
            .map(|p| match p {
                InlineAsmTemplatePiece::String(s) => s.matches('\n').count(),
                InlineAsmTemplatePiece::Placeholder { .. } => 0,
            })
            .sum::<usize>()
            + 1;
        let span_fill =
            line_spans.first().copied().unwrap_or(term.source_info.span);
        let new_spans: Vec<_> = (0..new_line_count).map(|_| span_fill).collect();

        *template = tcx.arena.alloc_from_iter(new_pieces);
        *line_spans = tcx.arena.alloc_from_iter(new_spans);
    }
}

fn custom_local_optimized_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> &'tcx Body<'tcx> {
    if std::env::var("ANNEAL_SPECCONE_FN").is_ok() {
        let steal = tcx.mir_drops_elaborated_and_const_checked(def_id);
        if !steal.is_stolen() {
            let saved: &'tcx Body<'tcx> = tcx.arena.alloc(steal.borrow().clone());
            SAVED_POSTCLEANUP_MIR.with(|m| {
                m.borrow_mut().insert(
                    def_id.local_def_index.as_u32(),
                    saved as *const Body<'tcx> as usize,
                );
            });
        }
    }
    let orig = (rustc_interface::DEFAULT_QUERY_PROVIDERS
        .queries
        .optimized_mir)(tcx, def_id);
    let mode = std::env::var("ANNEAL_ASM_WRAP_MODE")
        .unwrap_or_else(|_| "off".to_string());
    if mode == "off" {
        return orig;
    }
    let mut cloned = orig.clone();
    rewrite_body_inline_asm(tcx, def_id.to_def_id(), &mut cloned, &mode);
    tcx.arena.alloc(cloned)
}

fn custom_extern_optimized_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> &'tcx Body<'tcx> {
    let orig = (rustc_interface::DEFAULT_QUERY_PROVIDERS
        .extern_queries
        .optimized_mir)(tcx, def_id);
    if std::env::var("ANNEAL_SPECCONE_FN").is_ok() {
        SAVED_EXTERN_MIR.with(|m| {
            m.borrow_mut().insert(
                (def_id.krate.as_u32(), def_id.index.as_u32()),
                orig as *const Body<'tcx> as usize,
            );
        });
    }
    let mode = std::env::var("ANNEAL_ASM_WRAP_MODE")
        .unwrap_or_else(|_| "off".to_string());
    let intercept_extern = std::env::var("ANNEAL_INTERCEPT_EXTERN_MIR")
        .map(|v| v != "0")
        .unwrap_or(true);
    if mode == "off" || !intercept_extern {
        return orig;
    }
    // Fast-path skip when the foreign MIR body contains no `InlineAsm`.
    let has_asm = orig.basic_blocks.iter().any(|bb| {
        matches!(
            bb.terminator.as_ref().map(|t| &t.kind),
            Some(TerminatorKind::InlineAsm { .. })
        )
    });
    if !has_asm {
        return orig;
    }
    let mut cloned = orig.clone();
    rewrite_body_inline_asm(tcx, def_id, &mut cloned, &mode);
    tcx.arena.alloc(cloned)
}

fn override_queries(_sess: &Session, providers: &mut Providers) {
    let mode = std::env::var("ANNEAL_ASM_WRAP_MODE")
        .unwrap_or_else(|_| "off".to_string());
    let need_cone = std::env::var("ANNEAL_SPECCONE_FN").is_ok();
    if mode != "off" || need_cone {
        providers.queries.optimized_mir = custom_local_optimized_mir;
        providers.extern_queries.optimized_mir = custom_extern_optimized_mir;
    }
}

// --- Part 2: Complete `TyCtxt` Type-Graph & Pointee-Validity `SpecConeCollector` ---

fn early_bind<'tcx, T: ty::TypeFoldable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    val: T,
) -> ty::EarlyBinder<'tcx, T> {
    #[cfg(anneal_rustc_1_98)]
    {
        let _ = tcx;
        ty::EarlyBinder::bind(val)
    }
    #[cfg(not(anneal_rustc_1_98))]
    {
        ty::EarlyBinder::bind(tcx, val)
    }
}

struct SpecConeCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    full_closure: bool,
    queue: VecDeque<Instance<'tcx>>,
    visited_instances: BTreeSet<String>,
    instance_digests: BTreeMap<String, String>,
    type_digests: BTreeMap<String, String>,
    alloc_digests: BTreeMap<String, String>,
}

impl<'tcx> SpecConeCollector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, full_closure: bool) -> Self {
        Self {
            tcx,
            full_closure,
            queue: VecDeque::new(),
            visited_instances: BTreeSet::new(),
            instance_digests: BTreeMap::new(),
            type_digests: BTreeMap::new(),
            alloc_digests: BTreeMap::new(),
        }
    }

    fn canonical_def_id(&self, def_id: DefId) -> String {
        format!(
            "{}::{}",
            self.tcx.crate_name(def_id.krate),
            self.tcx.def_path_str(def_id)
        )
    }

    fn fmt_dbg<D: std::fmt::Debug>(&self, val: &D) -> String {
        let raw = format!("{val:?}");
        if self.full_closure {
            scrub_raw_def_indices(&raw)
        } else {
            raw
        }
    }

    fn canonical_instance_key(&self, inst: Instance<'tcx>) -> String {
        let inst_str = self.fmt_dbg(&inst);
        format!("{inst_str}|{}", self.canonical_def_id(inst.def_id()))
    }

    fn enqueue_instance(&mut self, inst: Instance<'tcx>) {
        let key = self.canonical_instance_key(inst);
        if self.visited_instances.insert(key) {
            self.queue.push_back(inst);
        }
    }

    fn compute_init_byte_mask(
        &self,
        typing_env: ty::TypingEnv<'tcx>,
        ty: Ty<'tcx>,
        depth: usize,
    ) -> Vec<bool> {
        let Ok(layout) = self.tcx.layout_of(typing_env.as_query_input(ty)) else {
            return Vec::new();
        };
        if layout.is_unsized() {
            return Vec::new();
        }
        let sz = layout.size.bytes_usize();
        if sz == 0 || sz > 4096 || depth > 16 {
            return Vec::new();
        }
        let cx = LayoutCx::new(self.tcx, typing_env);
        match &layout.fields {
            FieldsShape::Primitive => vec![true; sz],
            FieldsShape::Union(count) => {
                let mut mask = vec![true; sz];
                for idx in 0..count.get() {
                    let f_layout = layout.field(&cx, idx);
                    let f_mask = self.compute_init_byte_mask(
                        typing_env,
                        f_layout.ty,
                        depth + 1,
                    );
                    for b in 0..sz {
                        let init_here = b < f_mask.len() && f_mask[b];
                        mask[b] &= init_here;
                    }
                }
                mask
            }
            FieldsShape::Array { stride, count } => {
                let mut mask = vec![false; sz];
                if *count > 0 {
                    let elem_ty = layout.field(&cx, 0).ty;
                    let elem_mask = self.compute_init_byte_mask(
                        typing_env,
                        elem_ty,
                        depth + 1,
                    );
                    let st = stride.bytes_usize();
                    for c in 0..(*count as usize) {
                        let base = c * st;
                        for (i, &bit) in elem_mask.iter().enumerate() {
                            if base + i < sz {
                                mask[base + i] = bit;
                            }
                        }
                    }
                }
                mask
            }
            FieldsShape::Arbitrary { offsets, .. } => match &layout.variants {
                Variants::Empty => vec![false; sz],
                Variants::Single { .. } => {
                    let mut mask = vec![false; sz];
                    for (f_idx, off) in offsets.iter_enumerated() {
                        let f_ty = layout.field(&cx, f_idx.index()).ty;
                        let f_mask = self.compute_init_byte_mask(
                            typing_env,
                            f_ty,
                            depth + 1,
                        );
                        let base = off.bytes_usize();
                        for (i, &bit) in f_mask.iter().enumerate() {
                            if base + i < sz {
                                mask[base + i] |= bit;
                            }
                        }
                    }
                    mask
                }
                Variants::Multiple {
                    tag,
                    tag_field,
                    variants,
                    ..
                } => {
                    let mut mask = vec![true; sz];
                    if variants.is_empty() {
                        return vec![false; sz];
                    }
                    for v_idx in variants.indices() {
                        let v_layout = layout.for_variant(&cx, v_idx);
                        let mut v_mask = vec![false; sz];
                        if let FieldsShape::Arbitrary { offsets: v_offs, .. } =
                            &v_layout.fields
                        {
                            for (f_idx, off) in v_offs.iter_enumerated() {
                                let f_ty = v_layout.field(&cx, f_idx.index()).ty;
                                let f_m = self.compute_init_byte_mask(
                                    typing_env,
                                    f_ty,
                                    depth + 1,
                                );
                                let base = off.bytes_usize();
                                for (i, &bit) in f_m.iter().enumerate() {
                                    if base + i < sz {
                                        v_mask[base + i] |= bit;
                                    }
                                }
                            }
                        }
                        for b in 0..sz {
                            mask[b] &= v_mask[b];
                        }
                    }
                    let tag_off = offsets[*tag_field].bytes_usize();
                    let tag_sz = tag.size(&self.tcx).bytes_usize();
                    for b in tag_off..(tag_off + tag_sz).min(sz) {
                        mask[b] = true;
                    }
                    mask
                }
            },
        }
    }

    fn normalize_ty(
        &self,
        typing_env: ty::TypingEnv<'tcx>,
        raw_ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        if raw_ty.has_escaping_bound_vars() {
            return self.tcx.erase_and_anonymize_regions(raw_ty);
        }
        let norm = self
            .tcx
            .try_normalize_erasing_regions(
                typing_env,
                ty::Unnormalized::new_wip(raw_ty),
            )
            .unwrap_or(raw_ty);
        self.tcx.erase_and_anonymize_regions(norm)
    }

    fn record_type_and_layout(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        raw_ty: Ty<'tcx>,
    ) {
        let ty = if self.full_closure {
            self.normalize_ty(typing_env, raw_ty)
        } else {
            self.tcx.erase_and_anonymize_regions(raw_ty)
        };
        let key = self.fmt_dbg(&ty);
        if self.type_digests.contains_key(&key) {
            return;
        }
        // Insert sentinel first to break recursive pointer cycles (`&Node`).
        self.type_digests.insert(key.clone(), String::new());

        let mut h = Sha256::new_for_cone(self.full_closure);
        h.update_tag("ty", &key);

        match *ty.kind() {
            ty::Adt(adt_def, args) => {
                h.update_tag("adt_def", &self.canonical_def_id(adt_def.did()));
                h.update_tag("adt_repr", &format!("{:?}", adt_def.repr()));
                if self.full_closure && adt_def.is_enum() {
                    for (v_idx, discr) in adt_def.discriminants(self.tcx) {
                        let v_name = adt_def.variant(v_idx).name;
                        h.update_tag(
                            "enum_discr",
                            &format!("{v_name}:{discr:?}"),
                        );
                    }
                }
                for f in adt_def.all_fields() {
                    let f_ty = self
                        .tcx
                        .normalize_erasing_regions(typing_env, f.ty(self.tcx, args));
                    h.update_tag("field", &format!("{}:{f_ty:?}", f.name));
                    self.record_type_and_layout(typing_env, f_ty);
                }
                if self.full_closure
                    && !ty.has_non_region_param()
                    && ty.needs_drop(self.tcx, typing_env)
                {
                    let dg = Instance::resolve_drop_glue(self.tcx, ty);
                    h.update_tag("adt_drop_glue", &self.canonical_instance_key(dg));
                    self.enqueue_instance(dg);
                }
            }
            ty::Ref(_, pointee, mutbl) if self.full_closure => {
                h.update_tag("ref_mutbl", &format!("{mutbl:?}"));
                self.record_type_and_layout(typing_env, pointee);
            }
            ty::RawPtr(pointee, mutbl) if self.full_closure => {
                h.update_tag("rawptr_mutbl", &format!("{mutbl:?}"));
                self.record_type_and_layout(typing_env, pointee);
            }
            ty::Slice(elem) if self.full_closure => {
                h.update_tag("slice_elem", &format!("{elem:?}"));
                self.record_type_and_layout(typing_env, elem);
            }
            ty::Array(elem, len) if self.full_closure => {
                h.update_tag("array_len", &format!("{len:?}"));
                self.record_type_and_layout(typing_env, elem);
            }
            ty::Tuple(elems) if self.full_closure => {
                h.update_tag("tuple_arity", &elems.len().to_string());
                for (i, elem) in elems.iter().enumerate() {
                    h.update_tag("tuple_elem", &format!("{i}:{elem:?}"));
                    self.record_type_and_layout(typing_env, elem);
                }
            }
            ty::FnPtr(..) if self.full_closure => {
                let poly_sig = ty.fn_sig(self.tcx);
                let sig =
                    self.tcx.instantiate_bound_regions_with_erased(poly_sig);
                h.update_tag("fnptr_abi", &format!("{:?}", sig.abi()));
                h.update_tag("fnptr_safety", &format!("{:?}", sig.safety()));
                h.update_tag("fnptr_variadic", &sig.c_variadic().to_string());
                for (i, inp_ty) in sig.inputs().iter().enumerate() {
                    h.update_tag("fnptr_in", &format!("{i}:{inp_ty:?}"));
                    self.record_type_and_layout(typing_env, *inp_ty);
                }
                let out_ty = sig.output();
                h.update_tag("fnptr_out", &format!("{out_ty:?}"));
                self.record_type_and_layout(typing_env, out_ty);
                if !ty.has_non_region_param() {
                    if let Ok(f_abi) = self.tcx.fn_abi_of_fn_ptr(
                        typing_env.as_query_input((poly_sig, ty::List::empty())),
                    ) {
                        h.update_tag("fnptr_conv", &format!("{:?}", f_abi.conv));
                        h.update_tag(
                            "fnptr_can_unwind",
                            &f_abi.can_unwind.to_string(),
                        );
                        h.update_tag(
                            "fnptr_ret_mode",
                            &format!("{:?}", f_abi.ret.mode),
                        );
                        for (i, a) in f_abi.args.iter().enumerate() {
                            h.update_tag(
                                "fnptr_arg_mode",
                                &format!("{i}:{:?}", a.mode),
                            );
                        }
                    }
                }
            }
            ty::FnDef(fn_def_id, fn_args) if self.full_closure => {
                #[cfg(not(anneal_rustc_1_98))]
                let fn_args = fn_args.skip_binder();
                if let Ok(Some(callee)) =
                    Instance::try_resolve(self.tcx, typing_env, fn_def_id, fn_args)
                {
                    h.update_tag(
                        "fndef_resolved",
                        &self.canonical_instance_key(callee),
                    );
                    self.enqueue_instance(callee);
                }
            }
            ty::Dynamic(preds, ..) if self.full_closure => {
                h.update_tag("dyn_preds", &format!("{preds:?}"));
            }
            _ => {}
        }

        // Universal `ty.walk()` transitive type-graph closure safety net:
        // visits every nested `Ty<'tcx>` across `Pat`, `Closure`, `Coroutine`,
        // `Alias`, generic type arguments, and future `TyKind` constructors.
        if self.full_closure {
            let sub_tys: Vec<Ty<'tcx>> = ty
                .walk()
                .filter_map(|arg| arg.as_type())
                .filter(|sub| *sub != ty && !sub.has_escaping_bound_vars())
                .collect();
            for sub in sub_tys {
                let norm_sub = self.normalize_ty(typing_env, sub);
                h.update_tag("walk_sub_ty", &format!("{norm_sub:?}"));
                self.record_type_and_layout(typing_env, norm_sub);
            }
        }

        if let Ok(layout) = self.tcx.layout_of(typing_env.as_query_input(ty)) {
            #[cfg(anneal_rustc_1_102)]
            let align_bytes = layout.align.bytes();
            #[cfg(not(anneal_rustc_1_102))]
            let align_bytes = layout.align.abi.bytes();
            h.update_tag("size", &layout.size.bytes().to_string());
            h.update_tag("align", &align_bytes.to_string());
            h.update_tag("backend_repr", &format!("{:?}", layout.backend_repr));
            h.update_tag("fields_shape", &format!("{:?}", layout.fields));
            h.update_tag("variants", &format!("{:?}", layout.variants));
            let init_mask = self.compute_init_byte_mask(typing_env, ty, 0);
            let mask_str: String = init_mask
                .iter()
                .map(|&b| if b { 'I' } else { 'U' })
                .collect();
            h.update_tag("init_byte_mask", &mask_str);
            if self.full_closure && !layout.is_unsized() {
                let cx = LayoutCx::new(self.tcx, typing_env);
                for f_idx in 0..layout.fields.count() {
                    let f_ty = layout.field(&cx, f_idx).ty;
                    self.record_type_and_layout(typing_env, f_ty);
                }
            }
        }
        self.type_digests.insert(key, Sha256::hex(&h.finalize()));
    }

    fn hash_const_alloc(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        alloc: ConstAllocation<'tcx>,
    ) -> String {
        let inner = alloc.inner();
        let len = inner.len();
        let bytes =
            inner.inspect_with_uninit_and_ptr_outside_interpreter(0..len);
        let mut h = Sha256::new_for_cone(self.full_closure);
        h.update_tag("len", &len.to_string());
        h.update_tag("align", &inner.align.bytes().to_string());
        let mut mask_str = String::with_capacity(len);
        let mut init_bytes = Vec::with_capacity(len);
        for i in 0..len {
            let is_init = inner
                .init_mask()
                .get(rustc_abi::Size::from_bytes(i as u64));
            if is_init {
                mask_str.push('1');
                init_bytes.push(bytes[i]);
            } else {
                mask_str.push('0');
                init_bytes.push(0);
            }
        }
        h.update_tag("init_mask", &mask_str);
        h.update(&init_bytes);
        for (offset, prov) in inner.provenance().ptrs().iter() {
            let target_id = prov.alloc_id();
            let target_hash = self.record_global_alloc(typing_env, target_id);
            h.update_tag("prov", &format!("{}->{}", offset.bytes(), target_hash));
        }
        Sha256::hex(&h.finalize())
    }

    fn record_global_alloc(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        alloc_id: rustc_middle::mir::interpret::AllocId,
    ) -> String {
        let key = format!("{alloc_id:?}");
        if let Some(existing) = self.alloc_digests.get(&key) {
            if !existing.is_empty() {
                return existing.clone();
            }
            return "cycle".to_string();
        }
        self.alloc_digests.insert(key.clone(), String::new());
        let digest = match self.tcx.global_alloc(alloc_id) {
            GlobalAlloc::Memory(mem) => {
                format!("mem:{}", self.hash_const_alloc(typing_env, mem))
            }
            GlobalAlloc::Function { instance } => {
                self.enqueue_instance(instance);
                format!("fn:{}", self.canonical_instance_key(instance))
            }
            GlobalAlloc::Static(def_id) => {
                let mut sh = Sha256::new_for_cone(self.full_closure);
                sh.update_tag("static_def", &self.canonical_def_id(def_id));
                if self.full_closure {
                    // Close foreign (`extern "C" { static ... }`) and mutable
                    // statics: record `DefKind::Static { safety, mutability }`,
                    // `is_foreign_item`, `is_mutable_static`, `codegen_fn_attrs`
                    // (`link_name`, `export_name`, `link_section`, `THREAD_LOCAL`
                    // flags), and full `type_of(def_id)` layout/pointee closure.
                    sh.update_tag(
                        "static_def_kind",
                        &format!("{:?}", self.tcx.def_kind(def_id)),
                    );
                    let is_foreign = self.tcx.is_foreign_item(def_id);
                    sh.update_tag("is_foreign", &is_foreign.to_string());
                    sh.update_tag(
                        "is_mutable",
                        &self.tcx.is_mutable_static(def_id).to_string(),
                    );
                    let static_ty = self.tcx.normalize_erasing_regions(
                        typing_env,
                        self.tcx.type_of(def_id).instantiate_identity(),
                    );
                    sh.update_tag("static_ty", &format!("{static_ty:?}"));
                    self.record_type_and_layout(typing_env, static_ty);
                    let cg = self.tcx.codegen_fn_attrs(def_id);
                    sh.update_tag("static_flags", &format!("{:?}", cg.flags));
                    sh.update_tag(
                        "static_symbol_attrs",
                        &format!(
                            "sym={:?}|linkage={:?}|sec={:?}",
                            cg.symbol_name, cg.linkage, cg.link_section
                        ),
                    );
                    if !is_foreign {
                        if let Ok(val) = self.tcx.eval_static_initializer(def_id) {
                            sh.update_tag(
                                "static_val",
                                &self.hash_const_alloc(typing_env, val),
                            );
                        }
                    }
                } else if !self.tcx.is_foreign_item(def_id) {
                    if let Ok(val) = self.tcx.eval_static_initializer(def_id) {
                        sh.update_tag(
                            "static_val",
                            &self.hash_const_alloc(typing_env, val),
                        );
                    }
                }
                format!("static:{}", Sha256::hex(&sh.finalize()))
            }
            GlobalAlloc::VTable(ty, dyn_ty) => {
                self.record_type_and_layout(typing_env, ty);
                format!("vtable:{ty:?}:{dyn_ty:?}")
            }
            other => format!("other:{other:?}"),
        };
        self.alloc_digests.insert(key, digest.clone());
        digest
    }

    fn hash_const_value(
        &mut self,
        typing_env: ty::TypingEnv<'tcx>,
        val: ConstValue,
        ty: Ty<'tcx>,
    ) -> String {
        self.record_type_and_layout(typing_env, ty);
        match val {
            ConstValue::ZeroSized => "zst".to_string(),
            ConstValue::Scalar(scalar) => match scalar {
                rustc_middle::mir::interpret::Scalar::Int(i) => {
                    format!("int:{i:?}")
                }
                rustc_middle::mir::interpret::Scalar::Ptr(ptr, size) => {
                    let (prov, offset) = ptr.prov_and_relative_offset();
                    let target =
                        self.record_global_alloc(typing_env, prov.alloc_id());
                    format!("ptr:{target}+{}({size:?})", offset.bytes())
                }
            },
            ConstValue::Slice { alloc_id, meta } => {
                let target = self.record_global_alloc(typing_env, alloc_id);
                format!("slice:{target}:len={meta}")
            }
            ConstValue::Indirect { alloc_id, offset } => {
                let target = self.record_global_alloc(typing_env, alloc_id);
                format!("indirect:{target}+{}", offset.bytes())
            }
        }
    }

    fn hash_const_operand(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        c_op: &ConstOperand<'tcx>,
    ) -> String {
        let mono_const = inst.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            typing_env,
            early_bind(self.tcx, c_op.const_),
        );
        let mono_ty = inst.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            typing_env,
            early_bind(self.tcx, c_op.ty()),
        );
        self.record_type_and_layout(typing_env, mono_ty);

        if let Const::Unevaluated(uv, _) = mono_const {
            if uv.promoted.is_none() {
                if let Ok(Some(resolved)) =
                    Instance::try_resolve(self.tcx, typing_env, uv.def, uv.args)
                {
                    let _ = self.canonical_instance_key(resolved);
                }
            }
        }

        if let ty::FnDef(fn_def_id, fn_args) = *mono_ty.kind() {
            #[cfg(not(anneal_rustc_1_98))]
            let fn_args = fn_args.skip_binder();
            if let Ok(Some(callee)) =
                Instance::try_resolve(self.tcx, typing_env, fn_def_id, fn_args)
            {
                self.enqueue_instance(callee);
                return format!("fndef:{}", self.canonical_instance_key(callee));
            }
        }

        match mono_const.eval(self.tcx, typing_env, DUMMY_SP) {
            Ok(cv) => self.hash_const_value(typing_env, cv, mono_ty),
            Err(err) => format!("const_err:{mono_const:?}:{err:?}"),
        }
    }

    fn hash_operand(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        body: &Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> String {
        match op {
            Operand::Copy(p) => {
                format!("copy({})", self.hash_place(inst, typing_env, body, p))
            }
            Operand::Move(p) => {
                format!("move({})", self.hash_place(inst, typing_env, body, p))
            }
            Operand::Constant(c) => {
                format!("const({})", self.hash_const_operand(inst, typing_env, c))
            }
            other => format!("op_other({other:?})"),
        }
    }

    fn hash_place(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        body: &Body<'tcx>,
        place: &Place<'tcx>,
    ) -> String {
        let mut s = format!("_{}", place.local.as_usize());
        if self.full_closure {
            // Walk every intermediate `PlaceRef` (`Deref`, `Field`, `Index`,
            // `ConstantIndex`, `Subslice`, `Downcast`, `OpaqueCast`, `Subtype`)
            // and record its monomorphized, normalized `Ty` + layout!
            for (step_idx, elem) in place.projection.iter().enumerate() {
                let next_ref = rustc_middle::mir::PlaceRef {
                    local: place.local,
                    projection: &place.projection[..=step_idx],
                };
                let step_raw_ty = next_ref.ty(&body.local_decls, self.tcx).ty;
                let step_ty = inst.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    early_bind(self.tcx, step_raw_ty),
                );
                self.record_type_and_layout(typing_env, step_ty);
                match elem {
                    rustc_middle::mir::ProjectionElem::Field(f, _) => {
                        s.push_str(&format!(".f{}({step_ty:?})", f.index()));
                    }
                    other => {
                        s.push_str(&format!(".{other:?}({step_ty:?})"));
                    }
                }
            }
        } else {
            for elem in place.projection.iter() {
                match elem {
                    rustc_middle::mir::ProjectionElem::Field(f, ty) => {
                        let m_ty =
                            inst.instantiate_mir_and_normalize_erasing_regions(
                                self.tcx,
                                typing_env,
                                early_bind(self.tcx, ty),
                            );
                        self.record_type_and_layout(typing_env, m_ty);
                        s.push_str(&format!(".f{}({m_ty:?})", f.index()));
                    }
                    other => s.push_str(&format!(".{other:?}")),
                }
            }
        }
        s
    }

    fn hash_mir_body(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        body: &Body<'tcx>,
        h: &mut Sha256,
    ) {
        h.update_tag("arg_count", &body.arg_count.to_string());
        for (local_idx, decl) in body.local_decls.iter_enumerated() {
            let m_ty = inst.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                typing_env,
                early_bind(self.tcx, decl.ty),
            );
            self.record_type_and_layout(typing_env, m_ty);
            h.update_tag(
                "local",
                &format!(
                    "_{}:{:?}:{m_ty:?}",
                    local_idx.as_usize(),
                    decl.mutability
                ),
            );
        }

        if let Some(req_consts) = body.required_consts.as_ref() {
            for rc in req_consts {
                let c_str = self.hash_const_operand(inst, typing_env, rc);
                h.update_tag("required_const", &c_str);
            }
        }

        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            h.update_tag(
                "bb",
                &format!("bb{}:cleanup={}", bb.index(), bb_data.is_cleanup),
            );
            for stmt in &bb_data.statements {
                match &stmt.kind {
                    StatementKind::Assign(box_pair) => {
                        let (lhs, rhs) = &**box_pair;
                        let lhs_s =
                            self.hash_place(inst, typing_env, body, lhs);
                        let rhs_s =
                            self.hash_rvalue(inst, typing_env, body, rhs);
                        h.update_tag("assign", &format!("{lhs_s} = {rhs_s}"));
                    }
                    StatementKind::SetDiscriminant {
                        place,
                        variant_index,
                    } => {
                        let p_s =
                            self.hash_place(inst, typing_env, body, place);
                        h.update_tag(
                            "set_disc",
                            &format!("{p_s} := {}", variant_index.as_usize()),
                        );
                    }
                    StatementKind::StorageLive(l) => {
                        h.update_tag(
                            "storage_live",
                            &format!("_{}", l.as_usize()),
                        );
                    }
                    StatementKind::StorageDead(l) => {
                        h.update_tag(
                            "storage_dead",
                            &format!("_{}", l.as_usize()),
                        );
                    }
                    StatementKind::PlaceMention(p) => {
                        let p_s = self.hash_place(inst, typing_env, body, p);
                        h.update_tag("place_mention", &p_s);
                    }
                    StatementKind::Intrinsic(intr) => {
                        h.update_tag("stmt_intrinsic", &format!("{intr:?}"));
                    }
                    StatementKind::Nop => {}
                    other => {
                        h.update_tag("stmt_other", &format!("{other:?}"));
                    }
                }
            }
            if let Some(term) = &bb_data.terminator {
                match &term.kind {
                    TerminatorKind::Goto { target, .. } => {
                        h.update_tag(
                            "term",
                            &format!("goto->bb{}", target.index()),
                        );
                    }
                    TerminatorKind::SwitchInt { discr, targets, .. } => {
                        let d_s =
                            self.hash_operand(inst, typing_env, body, discr);
                        let arms: Vec<String> = targets
                            .iter()
                            .map(|(val, tgt)| format!("{val}->bb{}", tgt.index()))
                            .collect();
                        h.update_tag(
                            "term",
                            &format!(
                                "switch({d_s}):[{}],else->bb{}",
                                arms.join(","),
                                targets.otherwise().index()
                            ),
                        );
                    }
                    TerminatorKind::Return => h.update_tag("term", "return"),
                    TerminatorKind::Unreachable => {
                        h.update_tag("term", "unreachable")
                    }
                    TerminatorKind::UnwindResume => {
                        h.update_tag("term", "unwind_resume")
                    }
                    TerminatorKind::UnwindTerminate(reason) => {
                        h.update_tag(
                            "term",
                            &format!("unwind_terminate({reason:?})"),
                        );
                    }
                    TerminatorKind::Drop {
                        place,
                        target,
                        unwind,
                        replace,
                        ..
                    } => {
                        let p_s =
                            self.hash_place(inst, typing_env, body, place);
                        let raw_ty = place.ty(&body.local_decls, self.tcx).ty;
                        let drop_ty = inst
                            .instantiate_mir_and_normalize_erasing_regions(
                                self.tcx,
                                typing_env,
                                early_bind(self.tcx, raw_ty),
                            );
                        self.record_type_and_layout(typing_env, drop_ty);
                        let drop_glue =
                            Instance::resolve_drop_glue(self.tcx, drop_ty);
                        let has_nontrivial_drop =
                            drop_ty.needs_drop(self.tcx, typing_env);
                        if has_nontrivial_drop {
                            self.enqueue_instance(drop_glue);
                        }
                        h.update_tag(
                            "term_drop",
                            &format!(
                                "{p_s}:ty={drop_ty:?}:glue={}:nontrivial={has_nontrivial_drop}:tgt=bb{}:unw={unwind:?}:rep={replace}",
                                self.canonical_instance_key(drop_glue),
                                target.index()
                            ),
                        );
                    }
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target,
                        unwind,
                        ..
                    } => {
                        let f_s =
                            self.hash_operand(inst, typing_env, body, func);
                        let a_s: Vec<String> = args
                            .iter()
                            .map(|a| {
                                self.hash_operand(
                                    inst, typing_env, body, &a.node,
                                )
                            })
                            .collect();
                        let dst_s = self
                            .hash_place(inst, typing_env, body, destination);
                        let tgt_s = target
                            .map(|b| format!("bb{}", b.index()))
                            .unwrap_or_else(|| "!".into());
                        h.update_tag(
                            "term_call",
                            &format!(
                                "{dst_s} = {f_s}({}) -> {tgt_s} unw={unwind:?}",
                                a_s.join(",")
                            ),
                        );
                    }
                    TerminatorKind::Assert {
                        cond,
                        expected,
                        target,
                        unwind,
                        ..
                    } => {
                        let c_s =
                            self.hash_operand(inst, typing_env, body, cond);
                        h.update_tag(
                            "term_assert",
                            &format!(
                                "assert({c_s} == {expected}) -> bb{} unw={unwind:?}",
                                target.index()
                            ),
                        );
                    }
                    TerminatorKind::InlineAsm {
                        asm_macro,
                        template,
                        operands,
                        options,
                        targets,
                        unwind,
                        ..
                    } => {
                        let t_s = InlineAsmTemplatePiece::to_string(template);
                        h.update_tag(
                            "term_asm",
                            &format!(
                                "{asm_macro:?}:{t_s}:opts={options:?}:ops={}:tgts={targets:?}:unw={unwind:?}",
                                operands.len()
                            ),
                        );
                    }
                    other => {
                        h.update_tag("term_other", &format!("{other:?}"));
                    }
                }
            }
        }
    }

    fn hash_rvalue(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        body: &Body<'tcx>,
        rv: &Rvalue<'tcx>,
    ) -> String {
        match rv {
            Rvalue::Use(op, _) => {
                format!("use({})", self.hash_operand(inst, typing_env, body, op))
            }
            Rvalue::Repeat(op, c) => {
                let m_c = inst.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    early_bind(self.tcx, *c),
                );
                format!(
                    "repeat({};{m_c:?})",
                    self.hash_operand(inst, typing_env, body, op)
                )
            }
            Rvalue::Ref(_, bk, p) => {
                format!(
                    "ref({bk:?},{})",
                    self.hash_place(inst, typing_env, body, p)
                )
            }
            Rvalue::RawPtr(kind, p) => {
                format!(
                    "rawptr({kind:?},{})",
                    self.hash_place(inst, typing_env, body, p)
                )
            }
            Rvalue::BinaryOp(op, box_ops) => format!(
                "binop({op:?},{},{})",
                self.hash_operand(inst, typing_env, body, &box_ops.0),
                self.hash_operand(inst, typing_env, body, &box_ops.1)
            ),
            Rvalue::UnaryOp(op, x) => format!(
                "unop({op:?},{})",
                self.hash_operand(inst, typing_env, body, x)
            ),
            Rvalue::Cast(kind, op, ty) => {
                let m_ty = inst.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    early_bind(self.tcx, *ty),
                );
                self.record_type_and_layout(typing_env, m_ty);
                format!(
                    "cast({kind:?},{},{m_ty:?})",
                    self.hash_operand(inst, typing_env, body, op)
                )
            }
            Rvalue::Aggregate(box_kind, fields) => {
                let f_s: Vec<String> = fields
                    .iter()
                    .map(|f| self.hash_operand(inst, typing_env, body, f))
                    .collect();
                let kind_s = self.fmt_dbg(box_kind);
                format!("agg({kind_s},[{}])", f_s.join(","))
            }
            Rvalue::Discriminant(p) => {
                format!("disc({})", self.hash_place(inst, typing_env, body, p))
            }
            Rvalue::CopyForDeref(p) => format!(
                "deref_copy({})",
                self.hash_place(inst, typing_env, body, p)
            ),
            other => format!("rv_other({other:?})"),
        }
    }

    fn process_instance(&mut self, inst: Instance<'tcx>) {
        let key = self.canonical_instance_key(inst);
        let def_id = inst.def_id();
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let mut h = Sha256::new_for_cone(self.full_closure);
        h.update_tag("instance", &key);
        h.update_tag("def_kind", &format!("{:?}", self.tcx.def_kind(def_id)));

        if !inst.args.has_non_region_param() {
            if let Ok(fn_abi) = self.tcx.fn_abi_of_instance(
                typing_env.as_query_input((inst, ty::List::empty())),
            ) {
                h.update_tag("conv", &format!("{:?}", fn_abi.conv));
                h.update_tag("can_unwind", &fn_abi.can_unwind.to_string());
                h.update_tag("ret_abi", &format!("{:?}", fn_abi.ret.mode));
                self.record_type_and_layout(typing_env, fn_abi.ret.layout.ty);
                for (i, arg) in fn_abi.args.iter().enumerate() {
                    h.update_tag("arg_abi", &format!("{i}:{:?}", arg.mode));
                    self.record_type_and_layout(typing_env, arg.layout.ty);
                }
            }
        }
        let cg_attrs = self.tcx.codegen_instance_attrs(inst.def);
        h.update_tag(
            "target_features",
            &format!("{:?}", cg_attrs.target_features),
        );
        h.update_tag("codegen_flags", &format!("{:?}", cg_attrs.flags));
        h.update_tag("inline_attr", &format!("{:?}", cg_attrs.inline));

        match inst.def {
            InstanceKind::Item(d) if d.is_local() => {
                let local_d = d.expect_local();
                if matches!(
                    self.tcx.def_kind(d),
                    DefKind::Fn | DefKind::AssocFn | DefKind::Closure
                ) {
                    let steal =
                        self.tcx.mir_drops_elaborated_and_const_checked(local_d);
                    if !steal.is_stolen() {
                        let body = steal.borrow();
                        self.hash_mir_body(inst, typing_env, &body, &mut h);
                    } else if let Some(ptr) = SAVED_POSTCLEANUP_MIR.with(|m| {
                        m.borrow()
                            .get(&local_d.local_def_index.as_u32())
                            .copied()
                    }) {
                        // SAFETY: `ptr` was allocated in `self.tcx.arena`
                        // during this exact compiler session before `.steal()`.
                        let body: &'tcx Body<'tcx> =
                            unsafe { &*(ptr as *const Body<'tcx>) };
                        self.hash_mir_body(inst, typing_env, body, &mut h);
                    } else {
                        let body = self.tcx.optimized_mir(d);
                        self.hash_mir_body(inst, typing_env, body, &mut h);
                    }
                    let promos = self.tcx.promoted_mir(local_d);
                    for (p_idx, p_body) in promos.iter_enumerated() {
                        h.update_tag(
                            "promoted_idx",
                            &format!("{}", p_idx.as_usize()),
                        );
                        self.hash_mir_body(inst, typing_env, p_body, &mut h);
                    }
                }
            }
            InstanceKind::Intrinsic(_) | InstanceKind::Virtual(_, _) => {
                h.update_tag("shim_or_intrinsic", &self.fmt_dbg(&inst.def));
            }
            InstanceKind::Item(d) => {
                if self.tcx.is_mir_available(d) {
                    // Trigger `optimized_mir` first so `SAVED_EXTERN_MIR` holds
                    // the un-rewritten foreign MIR body if `ASM_WRAP` is active.
                    let _ = self.tcx.optimized_mir(d);
                    if let Some(ptr) = SAVED_EXTERN_MIR.with(|m| {
                        m.borrow()
                            .get(&(d.krate.as_u32(), d.index.as_u32()))
                            .copied()
                    }) {
                        // SAFETY: `ptr` comes from `DEFAULT_QUERY_PROVIDERS`
                        // in `self.tcx.arena` for this session.
                        let body: &'tcx Body<'tcx> =
                            unsafe { &*(ptr as *const Body<'tcx>) };
                        self.hash_mir_body(inst, typing_env, body, &mut h);
                    } else {
                        let body = self.tcx.instance_mir(inst.def);
                        self.hash_mir_body(inst, typing_env, body, &mut h);
                    }
                }
            }
            _ => {
                let body = self.tcx.instance_mir(inst.def);
                self.hash_mir_body(inst, typing_env, body, &mut h);
            }
        }

        self.instance_digests
            .insert(key, Sha256::hex(&h.finalize()));
    }

    fn run_from_root(&mut self, root_local: LocalDefId) -> String {
        let root_inst = Instance::mono(self.tcx, root_local.to_def_id());
        self.enqueue_instance(root_inst);
        while let Some(inst) = self.queue.pop_front() {
            self.process_instance(inst);
        }

        let mut master = Sha256::new_for_cone(self.full_closure);
        for (k, v) in &self.instance_digests {
            master.update_tag("inst_entry", &format!("{k}={v}"));
        }
        for (k, v) in &self.type_digests {
            master.update_tag("type_entry", &format!("{k}={v}"));
        }
        let mut sorted_alloc_vals: Vec<&str> =
            self.alloc_digests.values().map(|s| s.as_str()).collect();
        sorted_alloc_vals.sort_unstable();
        for v in sorted_alloc_vals {
            master.update_tag("alloc_entry", v);
        }
        let cone_hash = Sha256::hex(&master.finalize());

        let inst_keys: Vec<String> = self
            .instance_digests
            .keys()
            .map(|k| format!("\"{}\"", json_escape(k)))
            .collect();
        let type_keys: Vec<String> = self
            .type_digests
            .keys()
            .map(|k| format!("\"{}\"", json_escape(k)))
            .collect();
        format!(
            "{{\n  \"spec_cone_hash\": \"{cone_hash}\",\n  \
             \"closure_mode\": \"{}\",\n  \
             \"num_instances\": {},\n  \
             \"num_types\": {},\n  \
             \"num_allocs\": {},\n  \
             \"instances\": [{}],\n  \
             \"types\": [{}]\n}}\n",
            if self.full_closure { "v2" } else { "v1" },
            self.instance_digests.len(),
            self.type_digests.len(),
            self.alloc_digests.len(),
            inst_keys.join(", "),
            type_keys.join(", ")
        )
    }
}

struct DriverCallbacks;

impl Callbacks for DriverCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        if tcx.dcx().has_errors().is_some() {
            return Compilation::Continue;
        }
        if let Ok(target_fn) = std::env::var("ANNEAL_SPECCONE_FN") {
            if !target_fn.is_empty() {
                let mut found: Option<LocalDefId> = None;
                for local_def_id in tcx.hir_body_owners() {
                    let path_s = tcx.def_path_str(local_def_id.to_def_id());
                    if path_s.ends_with(&target_fn)
                        && matches!(
                            tcx.def_kind(local_def_id.to_def_id()),
                            DefKind::Fn | DefKind::AssocFn
                        )
                        && (path_s == target_fn || found.is_none())
                    {
                        found = Some(local_def_id);
                    }
                }
                if let Some(root) = found {
                    let full_closure =
                        std::env::var("ANNEAL_SPECCONE_CLOSURE")
                            .map(|v| v != "v1")
                            .unwrap_or(true);
                    let mut collector =
                        SpecConeCollector::new(tcx, full_closure);
                    let json = collector.run_from_root(root);
                    if let Ok(out_path) = std::env::var("ANNEAL_SPECCONE_OUT") {
                        let _ = fs::write(out_path, json);
                    }
                }
            }
        }
        Compilation::Continue
    }
}

fn flush_manifest_if_requested() {
    let Ok(manifest_path) = std::env::var("ANNEAL_ATTEST_MANIFEST_OUT") else {
        return;
    };
    if manifest_path.is_empty() {
        return;
    }
    if let Ok(map) = REWRITTEN_SITES.lock() {
        let entries: Vec<String> = map
            .values()
            .map(|e| {
                format!(
                    "    {{\"site_id\": {}, \"crate_name\": \"{}\", \
                     \"def_path\": \"{}\", \"is_local\": {}, \
                     \"bb_idx\": {}, \"session_nonce\": \"{}\"}}",
                    e.site_id,
                    json_escape(&e.crate_name),
                    json_escape(&e.def_path),
                    e.is_local,
                    e.bb_idx,
                    json_escape(&e.session_nonce),
                )
            })
            .collect();
        let doc = format!(
            "{{\n  \"rewritten_sites\": [\n{}\n  ]\n}}\n",
            entries.join(",\n")
        );
        let _ = fs::write(&manifest_path, doc);
    }
}

fn main() -> ExitCode {
    rustc_driver::catch_with_exit_code(|| {
        let mut args: Vec<String> = std::env::args().collect();
        if args.len() >= 2
            && (args[1].ends_with("rustc") || args[1].contains("/rustc"))
        {
            args.remove(1);
        }
        SAVED_POSTCLEANUP_MIR.with(|m| m.borrow_mut().clear());
        SAVED_EXTERN_MIR.with(|m| m.borrow_mut().clear());
        if let Ok(mut map) = REWRITTEN_SITES.lock() {
            map.clear();
        }
        if let Ok(sr) = std::env::var("ANNEAL_SYSROOT") {
            if !args.iter().any(|a| a == "--sysroot") {
                args.push("--sysroot".to_string());
                args.push(sr);
            }
        }
        let mut callbacks = DriverCallbacks;
        #[cfg(anneal_rustc_1_102)]
        rustc_driver::compiler_entrypoint(&args, &mut callbacks);
        #[cfg(not(anneal_rustc_1_102))]
        rustc_driver::run_compiler(&args, &mut callbacks);
        flush_manifest_if_requested();
    })
}
